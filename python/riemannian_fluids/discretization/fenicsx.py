"""Optional DOLFINx realizations of Riemannian-fluid model problems."""

from __future__ import annotations

import numpy as np

from riemannian_fluids.shells import (
    parallel_shape,
    solve_two_wall_tangential_field,
    wall_residual,
)


def solve_normal_fibre(
    *,
    shape: np.ndarray,
    u0: np.ndarray,
    thickness: float,
    alpha: float,
    cells: int,
    degree: int,
) -> dict[str, float | int | str]:
    """Solve a manufactured vector PDE across one shell normal fibre."""

    import dolfinx
    import ufl
    from dolfinx import fem, mesh
    from dolfinx.fem.petsc import LinearProblem
    from mpi4py import MPI

    wall_field = solve_two_wall_tangential_field(shape, u0, thickness, alpha)
    u1 = np.asarray(wall_field.u1, dtype=np.float64)
    u2 = np.asarray(wall_field.u2, dtype=np.float64)
    half_width = 0.5 * thickness
    domain = mesh.create_interval(MPI.COMM_WORLD, cells, [-half_width, half_width])
    space = fem.functionspace(domain, ("Lagrange", degree, (2,)))

    facet_dimension = domain.topology.dim - 1
    lower_facets = mesh.locate_entities_boundary(
        domain, facet_dimension, lambda x: np.isclose(x[0], -half_width)
    )
    upper_facets = mesh.locate_entities_boundary(
        domain, facet_dimension, lambda x: np.isclose(x[0], half_width)
    )
    facets = np.concatenate((lower_facets, upper_facets))
    markers = np.concatenate(
        (
            np.full(lower_facets.shape, 1, dtype=np.int32),
            np.full(upper_facets.shape, 2, dtype=np.int32),
        )
    )
    ordering = np.argsort(facets)
    facet_tags = mesh.meshtags(domain, facet_dimension, facets[ordering], markers[ordering])

    trial = ufl.TrialFunction(space)
    test = ufl.TestFunction(space)
    coordinate = ufl.SpatialCoordinate(domain)[0]
    exact = ufl.as_vector(
        tuple(
            float(u0[i]) + coordinate * float(u1[i]) + coordinate**2 * float(u2[i])
            for i in range(2)
        )
    )
    forcing = exact - ufl.as_vector(tuple(2.0 * float(value) for value in u2))
    lower_law = ufl.as_matrix(2.0 * alpha * np.asarray(parallel_shape(shape, -half_width)))
    upper_law = ufl.as_matrix(2.0 * alpha * np.asarray(parallel_shape(shape, half_width)))
    normal_axis = ufl.as_vector((1.0,))
    ds = ufl.Measure("ds", domain=domain, subdomain_data=facet_tags)
    bilinear = (
        ufl.inner(ufl.grad(trial), ufl.grad(test)) * ufl.dx
        + ufl.inner(trial, test) * ufl.dx
        + ufl.inner(ufl.dot(lower_law, trial), test) * ds(1)
        - ufl.inner(ufl.dot(upper_law, trial), test) * ds(2)
    )
    problem = LinearProblem(
        bilinear,
        ufl.inner(forcing, test) * ufl.dx,
        petsc_options_prefix=f"normal_fibre_p{degree}_{cells}_",
        petsc_options={"ksp_type": "preonly", "pc_type": "lu"},
    )
    solution = problem.solve()

    error = solution - exact
    exact_l2_squared = fem.assemble_scalar(fem.form(ufl.inner(exact, exact) * ufl.dx))
    error_l2_squared = fem.assemble_scalar(fem.form(ufl.inner(error, error) * ufl.dx))
    exact_h1_squared = fem.assemble_scalar(
        fem.form(ufl.inner(ufl.grad(exact), ufl.grad(exact)) * ufl.dx)
    )
    error_h1_squared = fem.assemble_scalar(
        fem.form(ufl.inner(ufl.grad(error), ufl.grad(error)) * ufl.dx)
    )
    derivative = ufl.dot(ufl.grad(solution), normal_axis)
    lower_residual = derivative - ufl.dot(lower_law, solution)
    upper_residual = derivative - ufl.dot(upper_law, solution)
    wall_residual_squared = fem.assemble_scalar(
        fem.form(
            ufl.inner(lower_residual, lower_residual) * ds(1)
            + ufl.inner(upper_residual, upper_residual) * ds(2)
        )
    )

    comm = domain.comm
    exact_l2_squared = comm.allreduce(exact_l2_squared, op=MPI.SUM)
    error_l2_squared = comm.allreduce(error_l2_squared, op=MPI.SUM)
    exact_h1_squared = comm.allreduce(exact_h1_squared, op=MPI.SUM)
    error_h1_squared = comm.allreduce(error_h1_squared, op=MPI.SUM)
    wall_residual_squared = comm.allreduce(wall_residual_squared, op=MPI.SUM)
    analytic_wall_residual = max(
        np.linalg.norm(np.asarray(wall_residual(shape, wall_field, thickness, alpha, -1))),
        np.linalg.norm(np.asarray(wall_residual(shape, wall_field, thickness, alpha, 1))),
    )
    return {
        "dolfinx_version": dolfinx.__version__,
        "thickness": thickness,
        "alpha": alpha,
        "cells": cells,
        "degree": degree,
        "relative_l2_error": float(np.sqrt(error_l2_squared / exact_l2_squared)),
        "relative_h1_seminorm_error": float(np.sqrt(error_h1_squared / exact_h1_squared)),
        "two_wall_residual_l2": float(np.sqrt(max(wall_residual_squared, 0.0))),
        "analytic_two_wall_residual": float(analytic_wall_residual),
    }
