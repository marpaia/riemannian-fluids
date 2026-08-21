"""Mixed FEniCSx reference solves on embedded curved surface meshes."""

from __future__ import annotations

from dataclasses import asdict, dataclass

import basix.ufl
import numpy as np
import ufl
from dolfinx import fem
from dolfinx.fem.petsc import LinearProblem
from mpi4py import MPI

from riemannian_fluids.discretization.fenicsx_meshes import create_octahedral_sphere


@dataclass(frozen=True)
class SurfaceStokesDiagnostics:
    refinement: int
    degree: int
    geometry_degree: int
    cells: int
    velocity_dofs: int
    pressure_dofs: int
    relative_velocity_l2_error: float
    divergence_l2: float
    tangency_l2: float
    pressure_mean: float
    spectral_reference_error: float
    viscosity: float
    reaction: float
    tangency_penalty: float

    def as_dict(self) -> dict[str, float | int]:
        return asdict(self)


def _global_scalar(comm: MPI.Comm, value: float) -> float:
    return float(comm.allreduce(value, op=MPI.SUM))


def solve_sphere_surface_stokes(
    *,
    refinement: int,
    degree: int = 2,
    geometry_degree: int = 2,
    viscosity: float = 1.0,
    reaction: float = 1.0,
    tangency_penalty: float = 100.0,
) -> SurfaceStokesDiagnostics:
    """Solve a mixed manufactured resolvent-Stokes problem on a sphere mesh.

    The exact target is the degree-one rotational Killing field.  The positive
    reaction removes its deformation-viscosity kernel; the corresponding
    spherical spectral resolvent response is exactly the target coefficient.
    The mesh carries degree-``geometry_degree`` coordinates with nodes snapped
    to the unit sphere, and the tangent projector uses the exact sphere normal
    ``x/|x|`` so the tangency constraint targets the true surface rather than
    the faceted approximation.
    """

    if refinement < 0:
        raise ValueError("refinement must be nonnegative")
    if degree < 2:
        raise ValueError("Taylor--Hood velocity degree must be at least two")
    if viscosity <= 0.0 or reaction <= 0.0 or tangency_penalty <= 0.0:
        raise ValueError("viscosity, reaction, and tangency penalty must be positive")

    domain = create_octahedral_sphere(MPI.COMM_WORLD, refinement, geometry_degree=geometry_degree)
    cell = domain.basix_cell()
    velocity_element = basix.ufl.element("Lagrange", cell, degree, shape=(3,))
    pressure_element = basix.ufl.element("Lagrange", cell, degree - 1)
    mixed_element = basix.ufl.mixed_element([velocity_element, pressure_element])
    space = fem.functionspace(domain, mixed_element)
    velocity, pressure = ufl.TrialFunctions(space)
    velocity_test, pressure_test = ufl.TestFunctions(space)

    coordinate = ufl.SpatialCoordinate(domain)
    cell_normal = coordinate / ufl.sqrt(ufl.inner(coordinate, coordinate))
    identity = ufl.Identity(3)
    tangent_projector = identity - ufl.outer(cell_normal, cell_normal)

    def tangent_gradient(field):
        return ufl.dot(tangent_projector, ufl.dot(ufl.grad(field), tangent_projector))

    def surface_divergence(field):
        return ufl.tr(tangent_gradient(field))

    def deformation(field):
        gradient = tangent_gradient(field)
        return 0.5 * (gradient + ufl.transpose(gradient))

    exact_velocity = ufl.as_vector((-coordinate[1], coordinate[0], 0.0))
    projected_velocity = ufl.dot(tangent_projector, velocity)
    projected_test = ufl.dot(tangent_projector, velocity_test)
    bilinear = (
        2.0 * viscosity * ufl.inner(deformation(velocity), deformation(velocity_test)) * ufl.dx
        + reaction * ufl.inner(projected_velocity, projected_test) * ufl.dx
        + tangency_penalty * ufl.inner(velocity, cell_normal) * ufl.inner(velocity_test, cell_normal) * ufl.dx
        - pressure * surface_divergence(velocity_test) * ufl.dx
        + pressure_test * surface_divergence(velocity) * ufl.dx
    )
    linear = (
        2.0 * viscosity * ufl.inner(deformation(exact_velocity), deformation(velocity_test)) * ufl.dx
        + reaction * ufl.inner(ufl.dot(tangent_projector, exact_velocity), projected_test) * ufl.dx
    )

    pressure_space, _ = space.sub(1).collapse()
    zero_pressure = fem.Function(pressure_space)
    pressure_dofs = fem.locate_dofs_geometrical(
        (space.sub(1), pressure_space),
        lambda x: np.isclose(x[2], 1.0),
    )
    pressure_gauge = fem.dirichletbc(zero_pressure, pressure_dofs, space.sub(1))
    problem = LinearProblem(
        bilinear,
        linear,
        bcs=[pressure_gauge],
        petsc_options_prefix=f"sphere_surface_stokes_r{refinement}_",
        petsc_options={
            "ksp_type": "preonly",
            "pc_type": "lu",
            "pc_factor_mat_solver_type": "mumps",
        },
    )
    solution = problem.solve()
    velocity_solution = solution.sub(0).collapse()
    pressure_solution = solution.sub(1).collapse()

    velocity_error = velocity_solution - exact_velocity
    velocity_error_squared = fem.assemble_scalar(fem.form(ufl.inner(velocity_error, velocity_error) * ufl.dx))
    velocity_norm_squared = fem.assemble_scalar(fem.form(ufl.inner(exact_velocity, exact_velocity) * ufl.dx))
    divergence_squared = fem.assemble_scalar(fem.form(surface_divergence(velocity_solution) ** 2 * ufl.dx))
    tangency_squared = fem.assemble_scalar(fem.form(ufl.inner(velocity_solution, cell_normal) ** 2 * ufl.dx))
    pressure_integral = fem.assemble_scalar(fem.form(pressure_solution * ufl.dx))
    area = fem.assemble_scalar(fem.form(1.0 * ufl.dx(domain=domain)))
    comm = domain.comm
    relative_error = np.sqrt(_global_scalar(comm, velocity_error_squared) / _global_scalar(comm, velocity_norm_squared))
    divergence_l2 = np.sqrt(_global_scalar(comm, divergence_squared))
    tangency_l2 = np.sqrt(_global_scalar(comm, tangency_squared))
    pressure_mean = _global_scalar(comm, pressure_integral) / _global_scalar(comm, area)
    topology_map = domain.topology.index_map(domain.topology.dim)
    return SurfaceStokesDiagnostics(
        refinement=refinement,
        degree=degree,
        geometry_degree=geometry_degree,
        cells=topology_map.size_global,
        velocity_dofs=velocity_solution.function_space.dofmap.index_map.size_global * velocity_solution.function_space.dofmap.index_map_bs,
        pressure_dofs=pressure_solution.function_space.dofmap.index_map.size_global,
        relative_velocity_l2_error=float(relative_error),
        divergence_l2=float(divergence_l2),
        tangency_l2=float(tangency_l2),
        pressure_mean=float(pressure_mean),
        spectral_reference_error=float(relative_error),
        viscosity=viscosity,
        reaction=reaction,
        tangency_penalty=tangency_penalty,
    )
