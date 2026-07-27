"""Differential forms in a coordinate patch."""

from __future__ import annotations

import math
from collections.abc import Callable
from dataclasses import dataclass
from itertools import permutations, product

import jax
import jax.numpy as jnp
import numpy as np

from riemannian_fluids.geometry import Geometry, dimension, metric
from riemannian_fluids.types import Array


def _permutation_sign(indices: tuple[int, ...]) -> int:
    inversions = sum(indices[left] > indices[right] for left in range(len(indices)) for right in range(left + 1, len(indices)))
    return -1 if inversions % 2 else 1


def levi_civita_symbol(n: int) -> Array:
    values = np.zeros((n,) * n, dtype=np.float64)
    for indices in permutations(range(n)):
        values[indices] = _permutation_sign(indices)
    return jnp.asarray(values)


@dataclass(frozen=True)
class DifferentialFormField:
    """A differential form represented by covariant coordinate coefficients."""

    geometry: Geometry
    degree: int
    coefficients: Callable[[Array], Array]

    def __post_init__(self) -> None:
        if self.degree < 0:
            raise ValueError("form degree must be nonnegative")

    def __call__(self, q: Array) -> Array:
        return self.coefficients(q)


def exterior_derivative(form: DifferentialFormField) -> DifferentialFormField:
    """Return the coordinate exterior derivative ``d form``."""

    degree = form.degree

    def coefficients(q: Array) -> Array:
        n = dimension(form.geometry, q)
        if degree >= n:
            return jnp.zeros((n,) * (degree + 1), dtype=q.dtype)
        derivative = jax.jacfwd(form.coefficients)(q)
        output = jnp.zeros((n,) * (degree + 1), dtype=q.dtype)
        for indices in product(range(n), repeat=degree + 1):
            value = jnp.asarray(0.0, dtype=q.dtype)
            for slot in range(degree + 1):
                remaining = indices[:slot] + indices[slot + 1 :]
                value += (-1) ** slot * derivative[remaining + (indices[slot],)]
            output = output.at[indices].set(value)
        return output

    return DifferentialFormField(form.geometry, degree + 1, coefficients)


def hodge_star(form: DifferentialFormField) -> DifferentialFormField:
    """Return the Riemannian Hodge star in the chart orientation."""

    degree = form.degree

    def coefficients(q: Array) -> Array:
        n = dimension(form.geometry, q)
        if degree > n:
            raise ValueError("form degree exceeds the manifold dimension")
        g = metric(form.geometry, q)
        inverse = jnp.linalg.inv(g)
        value = form(q)
        if degree:
            letters = "abcdefghijklmnopqrstuvwxyz"
            lower = letters[:degree]
            raised_indices = letters[degree : 2 * degree]
            factors = [value, *(inverse for _ in range(degree))]
            expression = lower
            for old, new in zip(lower, raised_indices, strict=True):
                expression += f",{new}{old}"
            expression += f"->{raised_indices}"
            value = jnp.einsum(expression, *factors)
        epsilon = levi_civita_symbol(n)
        remaining = n - degree
        if degree == 0:
            contraction = value * epsilon
        elif remaining == 0:
            contraction = jnp.einsum(f"{raised_indices},{raised_indices}->", value, epsilon)
        else:
            output_indices = "abcdefghijklmnopqrstuvwxyz"[2 * degree : degree + n]
            contraction = jnp.einsum(
                f"{raised_indices},{raised_indices}{output_indices}->{output_indices}",
                value,
                epsilon,
            )
        return jnp.sqrt(jnp.linalg.det(g)) * contraction / math.factorial(degree)

    return DifferentialFormField(form.geometry, complementary_degree(form), coefficients)


def complementary_degree(form: DifferentialFormField) -> int:
    """Return the complementary degree without requiring a sample point."""

    if hasattr(form.geometry, "dimension"):
        return int(form.geometry.dimension) - form.degree
    raise ValueError("Hodge star on a bare embedding needs explicit manifold metadata")


def codifferential(form: DifferentialFormField) -> DifferentialFormField:
    """Return ``delta=(-1)^(n(k+1)+1) * d *``."""

    if form.degree == 0:
        return DifferentialFormField(
            form.geometry,
            0,
            lambda q: jnp.asarray(0.0, dtype=q.dtype),
        )
    if not hasattr(form.geometry, "dimension"):
        raise ValueError("codifferential on a bare embedding needs explicit manifold metadata")
    n = int(form.geometry.dimension)
    sign = (-1) ** (n * (form.degree + 1) + 1)
    result = hodge_star(exterior_derivative(hodge_star(form)))
    return DifferentialFormField(form.geometry, form.degree - 1, lambda q: sign * result(q))


def hodge_laplacian(form: DifferentialFormField) -> DifferentialFormField:
    """Return ``Delta=d delta + delta d`` with the nonnegative convention."""

    if form.degree == 0:
        return codifferential(exterior_derivative(form))
    first = exterior_derivative(codifferential(form))
    second = codifferential(exterior_derivative(form))
    return DifferentialFormField(form.geometry, form.degree, lambda q: first(q) + second(q))
