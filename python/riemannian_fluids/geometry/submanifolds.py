"""Embedded submanifolds and their extrinsic geometry."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

import jax
import jax.numpy as jnp

from riemannian_fluids.geometry.manifolds import RiemannianManifold, euclidean_space
from riemannian_fluids.types import Array, Embedding

NormalFrame = Callable[[Array], Array]


@dataclass(frozen=True)
class EmbeddedSubmanifold:
    """A coordinate patch embedded in an intrinsic ambient manifold.

    ``normal_frame(q)`` stores ambient-coordinate normal vectors as columns.
    It is optional for Euclidean embeddings, where an orthonormal frame can be
    obtained numerically. Explicit frames are preferable when differentiating
    normal-bundle quantities.
    """

    name: str
    dimension: int
    ambient: RiemannianManifold
    embedding: Embedding
    normal_frame_field: NormalFrame | None = None
    coordinate_bounds: tuple[tuple[float | None, float | None], ...] = ()

    @property
    def ambient_dimension(self) -> int:
        return self.ambient.dimension

    @property
    def codimension(self) -> int:
        return self.ambient_dimension - self.dimension

    def metric(self, q: Array) -> Array:
        tangent = embedding_jacobian(self, q)
        ambient_metric = self.ambient.metric(self.embedding(q))
        return tangent.T @ ambient_metric @ tangent


def euclidean_submanifold(
    name: str,
    dimension: int,
    ambient_dimension: int,
    embedding: Embedding,
    *,
    normal_frame: NormalFrame | None = None,
    coordinate_bounds: tuple[tuple[float | None, float | None], ...] = (),
) -> EmbeddedSubmanifold:
    if ambient_dimension <= dimension:
        raise ValueError("ambient dimension must exceed intrinsic dimension")
    return EmbeddedSubmanifold(
        name,
        dimension,
        euclidean_space(ambient_dimension),
        embedding,
        normal_frame,
        coordinate_bounds,
    )


def _embedding(value: Embedding | EmbeddedSubmanifold) -> Embedding:
    return value.embedding if isinstance(value, EmbeddedSubmanifold) else value


def embedding_jacobian(value: Embedding | EmbeddedSubmanifold, q: Array) -> Array:
    """Return ambient-coordinate tangent vectors as columns."""

    return jax.jacfwd(_embedding(value))(q)


def normal_frame(value: Embedding | EmbeddedSubmanifold, q: Array) -> Array:
    """Return an ambient-metric orthonormal normal frame as columns."""

    if isinstance(value, EmbeddedSubmanifold) and value.normal_frame_field is not None:
        return value.normal_frame_field(q)

    tangent = embedding_jacobian(value, q)
    intrinsic_dimension = tangent.shape[1]
    ambient_dimension = tangent.shape[0]
    if isinstance(value, EmbeddedSubmanifold):
        ambient_metric = value.ambient.metric(value.embedding(q))
        is_euclidean = jnp.allclose(ambient_metric, jnp.eye(ambient_dimension))
        if not bool(is_euclidean):
            raise ValueError("non-Euclidean submanifolds require an explicit normal frame")

    if intrinsic_dimension == 2 and ambient_dimension == 3:
        raw = jnp.cross(tangent[:, 0], tangent[:, 1])
        return (raw / jnp.linalg.norm(raw))[:, None]

    _, _, vh = jnp.linalg.svd(tangent.T, full_matrices=True)
    return vh[intrinsic_dimension:, :].T


def unit_normal(value: Embedding | EmbeddedSubmanifold, q: Array) -> Array:
    """Return the normal of a hypersurface.

    For higher codimension, use :func:`normal_frame` explicitly.
    """

    frame = normal_frame(value, q)
    if frame.shape[1] != 1:
        raise ValueError("unit_normal is defined only for codimension-one embeddings")
    return frame[:, 0]
