"""Deterministic simplicial meshes used by the FEniCSx reference studies."""

from __future__ import annotations

from dataclasses import dataclass
from functools import cache

import basix.ufl
import numpy as np
import ufl
from dolfinx import mesh
from mpi4py import MPI

INNER_WALL = 1
OUTER_WALL = 2


@dataclass(frozen=True)
class SphericalShellMesh:
    """A tetrahedral spherical shell with independently tagged walls."""

    domain: mesh.Mesh
    facet_tags: mesh.MeshTags
    inner_radius: float
    outer_radius: float
    tangential_size: float
    normal_layers: int


def _unit_midpoint(
    vertices: list[np.ndarray],
    midpoints: dict[tuple[int, int], int],
    first: int,
    second: int,
) -> int:
    edge = tuple(sorted((first, second)))
    if edge not in midpoints:
        value = vertices[first] + vertices[second]
        value /= np.linalg.norm(value)
        midpoints[edge] = len(vertices)
        vertices.append(value)
    return midpoints[edge]


@cache
def octahedral_sphere_arrays(refinement: int, radius: float = 1.0) -> tuple[np.ndarray, np.ndarray]:
    """Return an outward-oriented triangular approximation of a sphere."""

    if refinement < 0:
        raise ValueError("refinement must be nonnegative")
    if radius <= 0.0:
        raise ValueError("radius must be positive")
    vertices = [
        np.asarray((0.0, 0.0, 1.0)),
        np.asarray((1.0, 0.0, 0.0)),
        np.asarray((0.0, 1.0, 0.0)),
        np.asarray((-1.0, 0.0, 0.0)),
        np.asarray((0.0, -1.0, 0.0)),
        np.asarray((0.0, 0.0, -1.0)),
    ]
    faces = [
        (0, 1, 2),
        (0, 2, 3),
        (0, 3, 4),
        (0, 4, 1),
        (5, 2, 1),
        (5, 3, 2),
        (5, 4, 3),
        (5, 1, 4),
    ]
    for _ in range(refinement):
        midpoints: dict[tuple[int, int], int] = {}
        refined = []
        for first, second, third in faces:
            first_second = _unit_midpoint(vertices, midpoints, first, second)
            second_third = _unit_midpoint(vertices, midpoints, second, third)
            third_first = _unit_midpoint(vertices, midpoints, third, first)
            refined.extend(
                (
                    (first, first_second, third_first),
                    (first_second, second, second_third),
                    (third_first, second_third, third),
                    (first_second, second_third, third_first),
                )
            )
        faces = refined
    points = radius * np.asarray(vertices, dtype=np.float64)
    cells = np.asarray(faces, dtype=np.int64)
    points.setflags(write=False)
    cells.setflags(write=False)
    return points, cells


def create_octahedral_sphere(
    comm: MPI.Comm,
    refinement: int,
    *,
    radius: float = 1.0,
) -> mesh.Mesh:
    """Create a distributed piecewise-linear sphere surface."""

    points, cells = octahedral_sphere_arrays(refinement, radius)
    if comm.rank != 0:
        points = np.empty((0, 3), dtype=np.float64)
        cells = np.empty((0, 3), dtype=np.int64)
    coordinate_element = basix.ufl.element("Lagrange", "triangle", 1, shape=(3,))
    coordinate_domain = ufl.Mesh(coordinate_element)
    return mesh.create_mesh(comm, cells, coordinate_domain, points)


@cache
def octahedral_shell_arrays(
    refinement: int,
    normal_layers: int,
    thickness: float,
) -> tuple[np.ndarray, np.ndarray, float, float, float]:
    """Extrude an octahedral sphere triangulation into conforming tetrahedra."""

    if normal_layers < 2:
        raise ValueError("normal_layers must be at least two")
    if not 0.0 < thickness < 2.0:
        raise ValueError("thickness must lie between zero and two")
    unit_points, surface_cells = octahedral_sphere_arrays(refinement)
    inner_radius = 1.0 - 0.5 * thickness
    outer_radius = 1.0 + 0.5 * thickness
    radii = np.linspace(inner_radius, outer_radius, normal_layers + 1)
    points = np.concatenate(tuple(radius * unit_points for radius in radii), axis=0)
    vertex_count = unit_points.shape[0]
    tetrahedra = []
    for layer in range(normal_layers):
        lower_offset = layer * vertex_count
        upper_offset = (layer + 1) * vertex_count
        for face in surface_cells:
            first, second, third = sorted(int(index) for index in face)
            first_lower = lower_offset + first
            second_lower = lower_offset + second
            third_lower = lower_offset + third
            first_upper = upper_offset + first
            second_upper = upper_offset + second
            third_upper = upper_offset + third
            tetrahedra.extend(
                (
                    (first_lower, second_lower, third_lower, first_upper),
                    (second_lower, third_lower, first_upper, second_upper),
                    (third_lower, first_upper, second_upper, third_upper),
                )
            )
    edge_lengths = []
    for face in surface_cells:
        for first, second in ((face[0], face[1]), (face[1], face[2]), (face[2], face[0])):
            edge_lengths.append(np.linalg.norm(unit_points[int(first)] - unit_points[int(second)]))
    cells = np.asarray(tetrahedra, dtype=np.int64)
    points.setflags(write=False)
    cells.setflags(write=False)
    return points, cells, inner_radius, outer_radius, outer_radius * float(max(edge_lengths))


def create_octahedral_shell(
    comm: MPI.Comm,
    refinement: int,
    normal_layers: int,
    thickness: float,
) -> SphericalShellMesh:
    """Create a distributed tetrahedral shell with inner and outer wall tags."""

    points, cells, inner_radius, outer_radius, tangential_size = octahedral_shell_arrays(
        refinement,
        normal_layers,
        thickness,
    )
    if comm.rank != 0:
        points = np.empty((0, 3), dtype=np.float64)
        cells = np.empty((0, 4), dtype=np.int64)
    coordinate_element = basix.ufl.element("Lagrange", "tetrahedron", 1, shape=(3,))
    coordinate_domain = ufl.Mesh(coordinate_element)
    domain = mesh.create_mesh(comm, cells, coordinate_domain, points)
    facet_dimension = domain.topology.dim - 1
    inner_facets = mesh.locate_entities_boundary(
        domain,
        facet_dimension,
        lambda x: np.isclose(np.linalg.norm(x, axis=0), inner_radius),
    )
    outer_facets = mesh.locate_entities_boundary(
        domain,
        facet_dimension,
        lambda x: np.isclose(np.linalg.norm(x, axis=0), outer_radius),
    )
    facets = np.concatenate((inner_facets, outer_facets))
    markers = np.concatenate(
        (
            np.full(inner_facets.shape, INNER_WALL, dtype=np.int32),
            np.full(outer_facets.shape, OUTER_WALL, dtype=np.int32),
        )
    )
    ordering = np.argsort(facets)
    tags = mesh.meshtags(domain, facet_dimension, facets[ordering], markers[ordering])
    return SphericalShellMesh(
        domain=domain,
        facet_tags=tags,
        inner_radius=inner_radius,
        outer_radius=outer_radius,
        tangential_size=tangential_size,
        normal_layers=normal_layers,
    )
