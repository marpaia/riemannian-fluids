"""Fermi geometry and two-wall fields in a thin shell around a surface."""

from __future__ import annotations

from dataclasses import dataclass

import jax
import jax.numpy as jnp

from riemannian_fluids.geometry import (
    EmbeddedSubmanifold,
    mean_curvature,
    metric,
    shape_operator,
    tangent_coordinates,
    unit_normal,
)
from riemannian_fluids.operators import ricci_action, rough_laplacian
from riemannian_fluids.tensors import deformation_tensor, gradient
from riemannian_fluids.types import Array, Embedding, ScalarField, VectorField

type SurfaceEmbedding = Embedding | EmbeddedSubmanifold


def _embedding(surface: SurfaceEmbedding) -> Embedding:
    return surface.embedding if isinstance(surface, EmbeddedSubmanifold) else surface


@dataclass(frozen=True)
class AmbientJets:
    """Six Taylor coefficients of a vector field in Fermi coordinates."""

    u0: VectorField
    u1: VectorField
    u2: VectorField
    w0: ScalarField
    w1: ScalarField
    w2: ScalarField


@dataclass(frozen=True)
class TwoWallTangentialField:
    """Quadratic tangential field satisfying conditions at both shell walls."""

    u0: Array
    u1: Array
    u2: Array

    def tangent(self, r: Array | float) -> Array:
        return self.u0 + r * self.u1 + r**2 * self.u2

    def derivative(self, r: Array | float) -> Array:
        return self.u1 + 2.0 * r * self.u2


def fermi_map(embedding: SurfaceEmbedding, y: Array) -> Array:
    """Return ``Phi(q,r)=X(q)+rN(q)``."""

    q = y[:2]
    r = y[2]
    return _embedding(embedding)(q) + r * unit_normal(embedding, q)


def fermi_metric(embedding: Embedding, y: Array) -> Array:
    jacobian = jax.jacfwd(lambda point: fermi_map(embedding, point))(y)
    return jacobian.T @ jacobian


def ambient_cartesian_field(
    embedding: Embedding,
    jets: AmbientJets,
    weights: Array,
    y: Array,
) -> Array:
    """Build an ambient Cartesian field from all six Fermi-coordinate jets."""

    q = y[:2]
    r = y[2]
    tangent = weights[0] * jets.u0(q) + r * weights[1] * jets.u1(q) + r**2 * weights[2] * jets.u2(q)
    normal = weights[3] * jets.w0(q) + r * weights[4] * jets.w1(q) + r**2 * weights[5] * jets.w2(q)
    coordinate_components = jnp.concatenate((tangent, jnp.asarray((normal,))))
    coordinate_basis = jax.jacfwd(lambda point: fermi_map(embedding, point))(y)
    return coordinate_basis @ coordinate_components


def ambient_positive_laplacian_cartesian(
    embedding: Embedding,
    jets: AmbientJets,
    weights: Array,
    q: Array,
) -> Array:
    """Apply the positive Euclidean vector Laplacian in Fermi coordinates."""

    y = jnp.concatenate((q, jnp.zeros((1,), dtype=q.dtype)))

    def flux(point: Array) -> Array:
        ambient_metric = fermi_metric(embedding, point)
        inverse = jnp.linalg.inv(ambient_metric)
        volume_density = jnp.sqrt(jnp.linalg.det(ambient_metric))
        derivative = jax.jacfwd(lambda z: ambient_cartesian_field(embedding, jets, weights, z))(point)
        return volume_density * derivative @ inverse

    flux_derivative = jax.jacfwd(flux)(y)
    coordinate_laplacian = jnp.einsum("caa->c", flux_derivative)
    return -coordinate_laplacian / jnp.sqrt(jnp.linalg.det(fermi_metric(embedding, y)))


def ambient_positive_laplacian_tangent(
    embedding: Embedding,
    jets: AmbientJets,
    weights: Array,
    q: Array,
) -> Array:
    return tangent_coordinates(
        embedding,
        ambient_positive_laplacian_cartesian(embedding, jets, weights, q),
        q,
    )


def ambient_restriction_formula(embedding: Embedding, jets: AmbientJets, q: Array) -> Array:
    """Return the positive tangential ambient Laplacian from explicit jets."""

    shape = shape_operator(embedding, q)
    trace_shape = jnp.trace(shape)
    intrinsic = rough_laplacian(embedding, jets.u0, q) - ricci_action(embedding, jets.u0, q)
    tangent_jets = (trace_shape * jnp.eye(2, dtype=q.dtype) + 2.0 * shape) @ jets.u1(q)
    tangent_jets -= 2.0 * jets.u2(q)
    normal_value = 2.0 * shape @ gradient(embedding, jets.w0, q)
    normal_value += jets.w0(q) * gradient(
        embedding,
        lambda point: jnp.trace(shape_operator(embedding, point)),
        q,
    )
    return intrinsic + tangent_jets + normal_value


def matched_wall_jets(
    embedding: Embedding,
    field: VectorField,
    normal_first: ScalarField,
    normal_second: ScalarField,
    alpha: float,
) -> AmbientJets:
    """Return the two-wall matched jets for the invariant slip parameter."""

    def first(point: Array) -> Array:
        return 2.0 * alpha * shape_operator(embedding, point) @ field(point)

    def second(point: Array) -> Array:
        shape = shape_operator(embedding, point)
        return alpha * (1.0 + 2.0 * alpha) * shape @ shape @ field(point)

    return AmbientJets(
        u0=field,
        u1=first,
        u2=second,
        w0=lambda point: jnp.asarray(0.0, dtype=point.dtype),
        w1=normal_first,
        w2=normal_second,
    )


def parallel_shape(shape: Array, r: Array | float) -> Array:
    """Return ``S(r)=S(I-rS)^-1`` on a parallel surface."""

    identity = jnp.eye(shape.shape[0], dtype=shape.dtype)
    return shape @ jnp.linalg.inv(identity - r * shape)


def solve_two_wall_tangential_field(
    shape: Array,
    u0: Array,
    thickness: Array | float,
    alpha: Array | float,
) -> TwoWallTangentialField:
    """Solve the exact finite-thickness wall equations for a quadratic field."""

    identity = jnp.eye(shape.shape[0], dtype=shape.dtype)
    half_width = 0.5 * thickness
    blocks = []
    right_hand_sides = []
    for wall in (-half_width, half_width):
        wall_law = 2.0 * alpha * parallel_shape(shape, wall)
        blocks.append(
            jnp.concatenate(
                (
                    identity - wall * wall_law,
                    2.0 * wall * identity - wall**2 * wall_law,
                ),
                axis=1,
            )
        )
        right_hand_sides.append(wall_law @ u0)
    coefficients = jnp.linalg.solve(
        jnp.concatenate(blocks, axis=0),
        jnp.concatenate(right_hand_sides),
    )
    dimension = shape.shape[0]
    return TwoWallTangentialField(u0, coefficients[:dimension], coefficients[dimension:])


def asymptotic_wall_jets(shape: Array, u0: Array, alpha: Array | float) -> tuple[Array, Array]:
    return (
        2.0 * alpha * shape @ u0,
        alpha * (1.0 + 2.0 * alpha) * shape @ shape @ u0,
    )


def wall_residual(
    shape: Array,
    field: TwoWallTangentialField,
    thickness: Array | float,
    alpha: Array | float,
    wall_sign: int,
) -> Array:
    wall = wall_sign * 0.5 * thickness
    return field.derivative(wall) - 2.0 * alpha * parallel_shape(shape, wall) @ field.tangent(wall)


def solenoidal_corrector_amplitude(
    embedding: Embedding,
    field: VectorField,
    q: Array,
    alpha: Array | float,
) -> Array:
    """Return the scalar amplitude in ``(r^2-epsilon^2/4)q``."""

    g = metric(embedding, q)
    inverse = jnp.linalg.inv(g)
    shape = shape_operator(embedding, q)
    mean = mean_curvature(embedding, q)
    traceless_second_form = g @ (shape - mean * jnp.eye(2, dtype=q.dtype))
    deformation = deformation_tensor(embedding, field, q)
    shape_strain = jnp.einsum(
        "ia,jb,ij,ab->",
        inverse,
        inverse,
        traceless_second_form,
        deformation,
    )
    mean_derivative_along_field = jax.jacfwd(lambda point: mean_curvature(embedding, point))(q) @ field(q)
    return -(2.0 * alpha - 1.0) * mean_derivative_along_field - alpha * shape_strain


def finite_thickness_jets(
    embedding: Embedding,
    field: VectorField,
    thickness: float,
    alpha: float,
    *,
    corrected: bool,
) -> AmbientJets:
    """Return all six jets of a finite-thickness two-wall field."""

    def coefficients(point: Array) -> TwoWallTangentialField:
        return solve_two_wall_tangential_field(shape_operator(embedding, point), field(point), thickness, alpha)

    def normal_amplitude(point: Array) -> Array:
        if not corrected:
            return jnp.asarray(0.0, dtype=point.dtype)
        return solenoidal_corrector_amplitude(embedding, field, point, alpha)

    half_width = 0.5 * thickness
    return AmbientJets(
        u0=field,
        u1=lambda point: coefficients(point).u1,
        u2=lambda point: coefficients(point).u2,
        w0=lambda point: -(half_width**2) * normal_amplitude(point),
        w1=lambda point: jnp.asarray(0.0, dtype=point.dtype),
        w2=normal_amplitude,
    )


def fermi_divergence(
    embedding: Embedding,
    jets: AmbientJets,
    q: Array,
    r: Array | float,
) -> Array:
    """Differentiate the shell divergence exactly in Fermi coordinates."""

    def density(point: Array, normal_coordinate: Array | float) -> Array:
        shape = shape_operator(embedding, point)
        identity = jnp.eye(shape.shape[0], dtype=point.dtype)
        return jnp.sqrt(jnp.linalg.det(metric(embedding, point))) * jnp.linalg.det(identity - normal_coordinate * shape)

    def tangent_flux(point: Array) -> Array:
        tangent = jets.u0(point) + r * jets.u1(point) + r**2 * jets.u2(point)
        return density(point, r) * tangent

    def normal_flux(normal_coordinate: Array) -> Array:
        normal = jets.w0(q) + normal_coordinate * jets.w1(q) + normal_coordinate**2 * jets.w2(q)
        return density(q, normal_coordinate) * normal

    tangential_derivative = jax.jacfwd(tangent_flux)(q)
    normal_derivative = jax.grad(normal_flux)(jnp.asarray(r, dtype=q.dtype))
    return (jnp.trace(tangential_derivative) + normal_derivative) / density(q, r)
