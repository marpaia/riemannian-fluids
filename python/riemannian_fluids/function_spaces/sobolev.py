"""Coordinate-quadrature Sobolev diagnostics for smooth reference fields."""

from __future__ import annotations

from collections.abc import Callable
from itertools import product

import jax
import jax.numpy as jnp
import numpy as np

from riemannian_fluids.geometry import CoordinateDomain, metric
from riemannian_fluids.tensors import covariant_derivative_vector
from riemannian_fluids.types import Array, ScalarField, VectorField


def tensor_product_quadrature(domain: CoordinateDomain, order: int) -> tuple[Array, Array]:
    """Return Gauss--Legendre points and coordinate-volume weights."""

    if order < 1:
        raise ValueError("quadrature order must be positive")
    reference_points, reference_weights = np.polynomial.legendre.leggauss(order)
    axes = []
    axis_weights = []
    for left, right in domain.bounds:
        axes.append(0.5 * (right - left) * reference_points + 0.5 * (right + left))
        axis_weights.append(0.5 * (right - left) * reference_weights)
    indices = tuple(product(range(order), repeat=domain.manifold.dimension))
    points = jnp.asarray([[axes[axis][index[axis]] for axis in range(len(axes))] for index in indices])
    weights = jnp.asarray([np.prod([axis_weights[axis][index[axis]] for axis in range(len(axes))]) for index in indices])
    return points, weights


def integrate(
    domain: CoordinateDomain,
    integrand: Callable[[Array], Array],
    *,
    order: int = 8,
) -> Array:
    points, coordinate_weights = tensor_product_quadrature(domain, order)
    values = jax.vmap(integrand)(points)
    densities = jax.vmap(lambda q: jnp.sqrt(jnp.linalg.det(metric(domain.manifold, q))))(points)
    return jnp.einsum("q,q,q...->...", coordinate_weights, densities, values)


def scalar_l2_norm(
    domain: CoordinateDomain,
    field: ScalarField,
    *,
    weight: ScalarField | None = None,
    order: int = 8,
) -> Array:
    density = (lambda q: jnp.asarray(1.0, dtype=q.dtype)) if weight is None else weight
    return jnp.sqrt(integrate(domain, lambda q: density(q) * field(q) ** 2, order=order))


def vector_l2_norm(
    domain: CoordinateDomain,
    field: VectorField,
    *,
    weight: ScalarField | None = None,
    order: int = 8,
) -> Array:
    density = (lambda q: jnp.asarray(1.0, dtype=q.dtype)) if weight is None else weight

    def squared(q: Array) -> Array:
        value = field(q)
        return density(q) * value @ metric(domain.manifold, q) @ value

    return jnp.sqrt(integrate(domain, squared, order=order))


def vector_h1_seminorm(
    domain: CoordinateDomain,
    field: VectorField,
    *,
    weight: ScalarField | None = None,
    order: int = 8,
) -> Array:
    density = (lambda q: jnp.asarray(1.0, dtype=q.dtype)) if weight is None else weight

    def squared(q: Array) -> Array:
        derivative = covariant_derivative_vector(domain.manifold, field, q)
        g = metric(domain.manifold, q)
        inverse = jnp.linalg.inv(g)
        return density(q) * jnp.einsum("kl,ij,ki,lj->", g, inverse, derivative, derivative)

    return jnp.sqrt(integrate(domain, squared, order=order))
