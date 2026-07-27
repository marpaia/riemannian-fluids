"""Small dense reference solvers for mixed incompressible systems."""

from __future__ import annotations

from dataclasses import dataclass

import jax.numpy as jnp

from riemannian_fluids.operators import MixedStokesSystem
from riemannian_fluids.types import Array


@dataclass(frozen=True)
class MixedSolution:
    velocity: Array
    pressure: Array
    residual_norm: float
    pressure_mean: float


def solve_mixed_stokes(system: MixedStokesSystem) -> MixedSolution:
    """Solve a saddle system with an explicit zero-mean pressure gauge."""

    block = system.block_matrix()
    rhs = system.right_hand_side()
    velocity_count = system.velocity_operator.shape[0]
    pressure_count = system.divergence.shape[0]
    weights = jnp.ones((pressure_count,), dtype=block.dtype) if system.pressure_weights is None else system.pressure_weights
    gauge = jnp.concatenate((jnp.zeros((velocity_count,), dtype=block.dtype), weights))
    augmented = jnp.block(
        [
            [block, gauge[:, None]],
            [gauge[None, :], jnp.zeros((1, 1), dtype=block.dtype)],
        ]
    )
    augmented_rhs = jnp.concatenate((rhs, jnp.zeros((1,), dtype=rhs.dtype)))
    solution = jnp.linalg.lstsq(augmented, augmented_rhs, rcond=None)[0][:-1]
    residual = block @ solution - rhs
    pressure = solution[velocity_count:]
    return MixedSolution(
        solution[:velocity_count],
        pressure,
        float(jnp.linalg.norm(residual)),
        float(weights @ pressure / jnp.sum(weights)),
    )
