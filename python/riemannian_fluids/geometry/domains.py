"""Coordinate-domain descriptions used by noncompact computations."""

from __future__ import annotations

from dataclasses import dataclass

from riemannian_fluids.geometry.manifolds import RiemannianManifold


@dataclass(frozen=True)
class CoordinateDomain:
    name: str
    manifold: RiemannianManifold
    bounds: tuple[tuple[float, float], ...]
    boundary_kind: str = "artificial-truncation"

    def __post_init__(self) -> None:
        if len(self.bounds) != self.manifold.dimension:
            raise ValueError("domain bounds must match the manifold dimension")
        if any(right <= left for left, right in self.bounds):
            raise ValueError("each coordinate interval must have positive length")

    def expanded(self, factor: float) -> CoordinateDomain:
        if factor <= 1.0:
            raise ValueError("expansion factor must exceed one")
        expanded_bounds = tuple(
            (
                0.5 * (left + right) - 0.5 * factor * (right - left),
                0.5 * (left + right) + 0.5 * factor * (right - left),
            )
            for left, right in self.bounds
        )
        return CoordinateDomain(f"{self.name}@{factor:g}", self.manifold, expanded_bounds)
