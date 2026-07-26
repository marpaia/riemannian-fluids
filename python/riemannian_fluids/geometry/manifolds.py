"""Intrinsic coordinate descriptions of Riemannian manifolds."""

from __future__ import annotations

from dataclasses import dataclass

import jax.numpy as jnp

from riemannian_fluids.types import Array, MetricField


@dataclass(frozen=True)
class RiemannianManifold:
    """A coordinate patch with an explicit positive-definite metric."""

    name: str
    dimension: int
    metric_field: MetricField
    coordinate_bounds: tuple[tuple[float | None, float | None], ...] = ()

    def metric(self, q: Array) -> Array:
        value = jnp.asarray(self.metric_field(q))
        expected = (self.dimension, self.dimension)
        if value.shape != expected:
            raise ValueError(f"{self.name} metric has shape {value.shape}; expected {expected}")
        return value


def euclidean_space(dimension: int) -> RiemannianManifold:
    """Return Euclidean space in Cartesian coordinates."""

    if dimension < 1:
        raise ValueError("dimension must be positive")

    def euclidean_metric(q: Array) -> Array:
        return jnp.eye(dimension, dtype=q.dtype)

    return RiemannianManifold(f"R^{dimension}", dimension, euclidean_metric)
