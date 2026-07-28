from __future__ import annotations

import numpy as np
from dolfinx import mesh
from mpi4py import MPI

from riemannian_fluids.discretization.fenicsx_meshes import INNER_WALL, OUTER_WALL, create_octahedral_shell
from riemannian_fluids.discretization.fenicsx_shell import (
    solve_resolved_spherical_shell,
    solve_wall_selected_spherical_shell,
)
from riemannian_fluids.shells import WallLaw, wall_parameter


def test_resolved_shell_mesh_has_only_the_two_tagged_walls() -> None:
    shell = create_octahedral_shell(MPI.COMM_WORLD, refinement=1, normal_layers=2, thickness=0.4)
    boundary_facets = mesh.locate_entities_boundary(
        shell.domain,
        shell.domain.topology.dim - 1,
        lambda x: np.full(x.shape[1], True),
    )
    tagged_count = len(shell.facet_tags.find(INNER_WALL)) + len(shell.facet_tags.find(OUTER_WALL))
    assert tagged_count == len(boundary_facets)


def test_resolved_shell_mixed_solve_is_finite_and_gauged() -> None:
    result = solve_resolved_spherical_shell(refinement=0, normal_layers=2, thickness=0.4)
    assert np.isfinite(result.relative_velocity_l2_error)
    assert np.isfinite(result.divergence_l2)
    assert abs(result.pressure_mean) < 1.0e-2


def test_wall_parameters_distinguish_endpoints_and_partial_slip() -> None:
    assert wall_parameter(WallLaw.NAVIER) == 0.0
    assert wall_parameter(WallLaw.PARTIAL_SLIP, 0.25) == 0.25
    assert wall_parameter(WallLaw.HODGE) == 1.0


def test_hodge_shell_response_is_distinct_from_navier_killing_response() -> None:
    hodge = solve_wall_selected_spherical_shell(
        refinement=0,
        normal_layers=2,
        thickness=0.4,
        wall_law=WallLaw.HODGE,
    )
    assert np.isfinite(hodge.averaged_shell_coefficient)
    assert 0.0 < hodge.averaged_shell_coefficient < 1.0
    assert hodge.expected_surface_coefficient == 1.0 / 3.0
