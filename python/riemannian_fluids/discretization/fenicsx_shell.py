"""Resolved three-dimensional mixed finite elements in a spherical shell."""

from __future__ import annotations

from dataclasses import asdict

import basix.ufl
import numpy as np
import ufl
from dolfinx import fem
from dolfinx.fem.petsc import LinearProblem
from mpi4py import MPI

from riemannian_fluids.discretization.fenicsx_meshes import (
    INNER_WALL,
    OUTER_WALL,
    create_octahedral_shell,
)
from riemannian_fluids.discretization.sphere_spectral import SphereStokesBasis
from riemannian_fluids.shells import (
    ShellSolveDiagnostics,
    WallLaw,
    WallSelectionDiagnostics,
    wall_parameter,
)


def _global_scalar(comm: MPI.Comm, value: float) -> float:
    return float(comm.allreduce(value, op=MPI.SUM))


def solve_resolved_spherical_shell(
    *,
    refinement: int,
    normal_layers: int,
    thickness: float,
    degree: int = 2,
    viscosity: float = 1.0,
    reaction: float = 1.0,
) -> ShellSolveDiagnostics:
    """Solve a manufactured mixed Stokes problem on a tetrahedral volume shell.

    The exact velocity is a radially modulated rotation that is divergence
    free and vanishes on the two true spherical walls.  On the polyhedral
    walls it leaves a geometric trace error, so refinement tests the volume
    discretization and boundary approximation together.
    """

    if refinement < 0:
        raise ValueError("refinement must be nonnegative")
    if degree < 2:
        raise ValueError("Taylor--Hood velocity degree must be at least two")
    if viscosity <= 0.0 or reaction <= 0.0:
        raise ValueError("viscosity and reaction must be positive")
    shell = create_octahedral_shell(MPI.COMM_WORLD, refinement, normal_layers, thickness)
    domain = shell.domain
    cell = domain.basix_cell()
    velocity_element = basix.ufl.element("Lagrange", cell, degree, shape=(3,))
    pressure_element = basix.ufl.element("Lagrange", cell, degree - 1)
    mixed_element = basix.ufl.mixed_element([velocity_element, pressure_element])
    space = fem.functionspace(domain, mixed_element)
    velocity, pressure = ufl.TrialFunctions(space)
    velocity_test, pressure_test = ufl.TestFunctions(space)

    coordinate = ufl.SpatialCoordinate(domain)
    radius = ufl.sqrt(ufl.dot(coordinate, coordinate))
    rotation = ufl.as_vector((-coordinate[1], coordinate[0], 0.0))
    profile = (radius - shell.inner_radius) * (shell.outer_radius - radius)
    exact_velocity = profile * rotation
    exact_pressure = coordinate[2]

    def strain(field):
        gradient = ufl.grad(field)
        return 0.5 * (gradient + ufl.transpose(gradient))

    bilinear = (
        2.0 * viscosity * ufl.inner(strain(velocity), strain(velocity_test)) * ufl.dx
        + reaction * ufl.inner(velocity, velocity_test) * ufl.dx
        - pressure * ufl.div(velocity_test) * ufl.dx
        + pressure_test * ufl.div(velocity) * ufl.dx
    )
    linear = (
        2.0 * viscosity * ufl.inner(strain(exact_velocity), strain(velocity_test)) * ufl.dx
        + reaction * ufl.inner(exact_velocity, velocity_test) * ufl.dx
        - exact_pressure * ufl.div(velocity_test) * ufl.dx
        + pressure_test * ufl.div(exact_velocity) * ufl.dx
    )

    facet_dimension = domain.topology.dim - 1
    wall_facets = np.concatenate(
        (
            shell.facet_tags.find(INNER_WALL),
            shell.facet_tags.find(OUTER_WALL),
        )
    )
    velocity_space, _ = space.sub(0).collapse()
    zero_velocity = fem.Function(velocity_space)
    velocity_dofs = fem.locate_dofs_topological(
        (space.sub(0), velocity_space),
        facet_dimension,
        wall_facets,
    )
    velocity_bc = fem.dirichletbc(zero_velocity, velocity_dofs, space.sub(0))

    pressure_space, _ = space.sub(1).collapse()
    pressure_gauge_value = fem.Function(pressure_space)
    pressure_gauge_value.interpolate(lambda x: x[2])
    pressure_dofs = fem.locate_dofs_geometrical(
        (space.sub(1), pressure_space),
        lambda x: np.isclose(x[0], 0.0) & np.isclose(x[1], 0.0) & np.isclose(x[2], shell.outer_radius),
    )
    pressure_bc = fem.dirichletbc(pressure_gauge_value, pressure_dofs, space.sub(1))
    problem = LinearProblem(
        bilinear,
        linear,
        bcs=[velocity_bc, pressure_bc],
        petsc_options_prefix=f"resolved_shell_r{refinement}_n{normal_layers}_",
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
    pressure_error = pressure_solution - exact_pressure
    dx = ufl.Measure("dx", domain=domain)
    ds = ufl.Measure("ds", domain=domain, subdomain_data=shell.facet_tags)
    velocity_error_squared = fem.assemble_scalar(fem.form(ufl.inner(velocity_error, velocity_error) * dx))
    velocity_norm_squared = fem.assemble_scalar(fem.form(ufl.inner(exact_velocity, exact_velocity) * dx))
    pressure_error_squared = fem.assemble_scalar(fem.form(pressure_error**2 * dx))
    pressure_norm_squared = fem.assemble_scalar(fem.form(exact_pressure**2 * dx))
    divergence_squared = fem.assemble_scalar(fem.form(ufl.div(velocity_solution) ** 2 * dx))
    wall_residual_squared = fem.assemble_scalar(
        fem.form(
            ufl.inner(velocity_error, velocity_error) * ds(INNER_WALL)
            + ufl.inner(velocity_error, velocity_error) * ds(OUTER_WALL)
        )
    )
    pressure_integral = fem.assemble_scalar(fem.form(pressure_solution * dx))
    volume = fem.assemble_scalar(fem.form(1.0 * dx))
    rotation_norm_squared = fem.assemble_scalar(fem.form(ufl.inner(rotation, rotation) * dx))
    exact_average_numerator = fem.assemble_scalar(fem.form(ufl.inner(exact_velocity, rotation) * dx))
    discrete_average_numerator = fem.assemble_scalar(fem.form(ufl.inner(velocity_solution, rotation) * dx))

    comm = domain.comm
    velocity_error_squared = _global_scalar(comm, velocity_error_squared)
    velocity_norm_squared = _global_scalar(comm, velocity_norm_squared)
    pressure_error_squared = _global_scalar(comm, pressure_error_squared)
    pressure_norm_squared = _global_scalar(comm, pressure_norm_squared)
    divergence_squared = _global_scalar(comm, divergence_squared)
    wall_residual_squared = _global_scalar(comm, wall_residual_squared)
    pressure_integral = _global_scalar(comm, pressure_integral)
    volume = _global_scalar(comm, volume)
    rotation_norm_squared = _global_scalar(comm, rotation_norm_squared)
    exact_average = _global_scalar(comm, exact_average_numerator) / rotation_norm_squared
    discrete_average = _global_scalar(comm, discrete_average_numerator) / rotation_norm_squared
    topology_map = domain.topology.index_map(domain.topology.dim)
    return ShellSolveDiagnostics(
        refinement=refinement,
        cells=topology_map.size_global,
        velocity_dofs=velocity_solution.function_space.dofmap.index_map.size_global * velocity_solution.function_space.dofmap.index_map_bs,
        pressure_dofs=pressure_solution.function_space.dofmap.index_map.size_global,
        thickness=thickness,
        tangential_size=shell.tangential_size,
        normal_layers=normal_layers,
        wall_law=WallLaw.NO_SLIP,
        viscosity=viscosity,
        reaction=reaction,
        divergence_l2=float(np.sqrt(max(divergence_squared, 0.0))),
        wall_residual_l2=float(np.sqrt(max(wall_residual_squared, 0.0))),
        pressure_mean=pressure_integral / volume,
        averaged_surface_error_l2=abs(discrete_average - exact_average) / abs(exact_average),
        relative_velocity_l2_error=float(np.sqrt(velocity_error_squared / velocity_norm_squared)),
        relative_pressure_l2_error=float(np.sqrt(pressure_error_squared / pressure_norm_squared)),
    )


def diagnostics_dict(diagnostics: ShellSolveDiagnostics) -> dict[str, float | int | str]:
    """Serialize resolved-shell diagnostics with the resolution ratio."""

    return {**asdict(diagnostics), "h_over_thickness": diagnostics.h_over_thickness}


def solve_wall_selected_spherical_shell(
    *,
    refinement: int,
    normal_layers: int,
    thickness: float,
    wall_law: WallLaw,
    alpha: float = 0.0,
    degree: int = 2,
    viscosity: float = 1.0,
    reaction: float = 1.0,
    normal_penalty: float = 100.0,
) -> WallSelectionDiagnostics:
    """Solve the Navier--Hodge wall family and compare its transverse limit.

    Impermeability is imposed by a mesh-dependent normal penalty.  The
    tangential wall condition is the natural condition of the deformation
    form plus the signed curvature boundary form.  At alpha zero and one this
    is respectively the stress-free and vorticity-free endpoint form.
    """

    selected_alpha = wall_parameter(wall_law, alpha)
    if refinement < 0:
        raise ValueError("refinement must be nonnegative")
    if degree < 2:
        raise ValueError("Taylor--Hood velocity degree must be at least two")
    if viscosity <= 0.0 or reaction <= 0.0 or normal_penalty <= 0.0:
        raise ValueError("viscosity, reaction, and normal penalty must be positive")

    shell = create_octahedral_shell(MPI.COMM_WORLD, refinement, normal_layers, thickness)
    domain = shell.domain
    cell = domain.basix_cell()
    velocity_element = basix.ufl.element("Lagrange", cell, degree, shape=(3,))
    pressure_element = basix.ufl.element("Lagrange", cell, degree - 1)
    space = fem.functionspace(domain, basix.ufl.mixed_element([velocity_element, pressure_element]))
    velocity, pressure = ufl.TrialFunctions(space)
    velocity_test, pressure_test = ufl.TestFunctions(space)

    coordinate = ufl.SpatialCoordinate(domain)
    radius = ufl.sqrt(ufl.dot(coordinate, coordinate))
    radial_normal = coordinate / radius
    tangent_projector = ufl.Identity(3) - ufl.outer(radial_normal, radial_normal)
    rotation = ufl.as_vector((-coordinate[1], coordinate[0], 0.0))
    dx = ufl.Measure("dx", domain=domain)
    ds = ufl.Measure("ds", domain=domain, subdomain_data=shell.facet_tags)

    def strain(field):
        gradient = ufl.grad(field)
        return 0.5 * (gradient + ufl.transpose(gradient))

    projected_velocity = ufl.dot(tangent_projector, velocity)
    projected_test = ufl.dot(tangent_projector, velocity_test)
    penalty_scale = normal_penalty / shell.tangential_size
    curvature_pairing = ufl.inner(projected_velocity, projected_test) / radius
    if wall_law is WallLaw.HODGE:
        viscous_form = viscosity * (
            ufl.inner(ufl.curl(velocity), ufl.curl(velocity_test))
            + ufl.div(velocity) * ufl.div(velocity_test)
        ) * dx
        curvature_form = 0
    else:
        viscous_form = 2.0 * viscosity * ufl.inner(strain(velocity), strain(velocity_test)) * dx
        curvature_form = (
            -2.0 * viscosity * selected_alpha * curvature_pairing * ds(INNER_WALL)
            + 2.0 * viscosity * selected_alpha * curvature_pairing * ds(OUTER_WALL)
        )
    bilinear = (
        viscous_form
        + reaction * ufl.inner(velocity, velocity_test) * dx
        - pressure * ufl.div(velocity_test) * dx
        + pressure_test * ufl.div(velocity) * dx
        + penalty_scale
        * ufl.inner(velocity, radial_normal)
        * ufl.inner(velocity_test, radial_normal)
        * (ds(INNER_WALL) + ds(OUTER_WALL))
        + curvature_form
    )
    linear = ufl.inner(rotation, velocity_test) * dx

    pressure_space, _ = space.sub(1).collapse()
    zero_pressure = fem.Function(pressure_space)
    pressure_dofs = fem.locate_dofs_geometrical(
        (space.sub(1), pressure_space),
        lambda x: np.isclose(x[0], 0.0) & np.isclose(x[1], 0.0) & np.isclose(x[2], shell.outer_radius),
    )
    pressure_bc = fem.dirichletbc(zero_pressure, pressure_dofs, space.sub(1))
    problem = LinearProblem(
        bilinear,
        linear,
        bcs=[pressure_bc],
        petsc_options_prefix=f"wall_selected_{wall_law.value}_{selected_alpha:.3f}_r{refinement}_n{normal_layers}_",
        petsc_options={
            "ksp_type": "preonly",
            "pc_type": "lu",
            "pc_factor_mat_solver_type": "mumps",
        },
    )
    solution = problem.solve()
    velocity_solution = solution.sub(0).collapse()
    pressure_solution = solution.sub(1).collapse()

    rotation_norm_squared = fem.assemble_scalar(fem.form(ufl.inner(rotation, rotation) * dx))
    average_numerator = fem.assemble_scalar(fem.form(ufl.inner(velocity_solution, rotation) * dx))
    divergence_squared = fem.assemble_scalar(fem.form(ufl.div(velocity_solution) ** 2 * dx))
    normal_trace_squared = fem.assemble_scalar(
        fem.form(
            ufl.inner(velocity_solution, radial_normal) ** 2
            * (ds(INNER_WALL) + ds(OUTER_WALL))
        )
    )
    stress_residual = ufl.dot(
        tangent_projector,
        ufl.dot(ufl.grad(velocity_solution) + ufl.transpose(ufl.grad(velocity_solution)), radial_normal),
    )
    hodge_residual = ufl.cross(ufl.curl(velocity_solution), radial_normal)
    selected_residual = (1.0 - selected_alpha) * stress_residual + selected_alpha * hodge_residual
    wall_law_residual_squared = fem.assemble_scalar(
        fem.form(
            ufl.inner(selected_residual, selected_residual)
            * (ds(INNER_WALL) + ds(OUTER_WALL))
        )
    )
    pressure_integral = fem.assemble_scalar(fem.form(pressure_solution * dx))
    volume = fem.assemble_scalar(fem.form(1.0 * dx))

    comm = domain.comm
    rotation_norm_squared = _global_scalar(comm, rotation_norm_squared)
    averaged_coefficient = _global_scalar(comm, average_numerator) / rotation_norm_squared
    divergence_l2 = np.sqrt(max(_global_scalar(comm, divergence_squared), 0.0))
    normal_trace_l2 = np.sqrt(max(_global_scalar(comm, normal_trace_squared), 0.0))
    wall_law_residual_l2 = np.sqrt(max(_global_scalar(comm, wall_law_residual_squared), 0.0))
    pressure_mean = _global_scalar(comm, pressure_integral) / _global_scalar(comm, volume)
    basis = SphereStokesBasis(1)
    killing_index = basis.killing_mode_indices()[0]
    surface_eigenvalue = float(basis.interpolating_viscosity_eigenvalues(selected_alpha)[killing_index])
    expected_coefficient = 1.0 / (reaction + viscosity * surface_eigenvalue)
    topology_map = domain.topology.index_map(domain.topology.dim)
    return WallSelectionDiagnostics(
        refinement=refinement,
        degree=degree,
        cells=topology_map.size_global,
        velocity_dofs=velocity_solution.function_space.dofmap.index_map.size_global * velocity_solution.function_space.dofmap.index_map_bs,
        pressure_dofs=pressure_solution.function_space.dofmap.index_map.size_global,
        thickness=thickness,
        tangential_size=shell.tangential_size,
        normal_layers=normal_layers,
        wall_law=wall_law,
        alpha=selected_alpha,
        viscosity=viscosity,
        reaction=reaction,
        normal_penalty=normal_penalty,
        form="hodge-div-curl" if wall_law is WallLaw.HODGE else "deformation-with-signed-curvature-boundary",
        surface_eigenvalue=surface_eigenvalue,
        expected_surface_coefficient=expected_coefficient,
        averaged_shell_coefficient=averaged_coefficient,
        relative_surface_coefficient_error=abs(averaged_coefficient - expected_coefficient) / abs(expected_coefficient),
        divergence_l2=float(divergence_l2),
        normal_wall_trace_l2=float(normal_trace_l2),
        wall_law_residual_l2=float(wall_law_residual_l2),
        pressure_mean=float(pressure_mean),
    )


def wall_selection_diagnostics_dict(
    diagnostics: WallSelectionDiagnostics,
) -> dict[str, float | int | str]:
    """Serialize wall-selection diagnostics with the resolution ratio."""

    return {**asdict(diagnostics), "h_over_thickness": diagnostics.h_over_thickness}
