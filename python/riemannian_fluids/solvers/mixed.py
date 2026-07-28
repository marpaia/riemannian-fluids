"""Small dense reference solvers for mixed incompressible systems."""

from __future__ import annotations

from dataclasses import dataclass

import jax.numpy as jnp

from riemannian_fluids.discrete import FlowSolveResult, FlowState, SemiDiscreteFlowSystem


@dataclass(frozen=True)
class MixedSolution:
    result: FlowSolveResult

    @property
    def velocity(self):
        return self.result.state.velocity

    @property
    def pressure(self):
        return self.result.state.pressure

    @property
    def residual_norm(self) -> float:
        diagnostics = self.result.diagnostics
        return float(jnp.hypot(diagnostics.momentum_residual_norm, diagnostics.incompressibility_norm))

    @property
    def pressure_mean(self) -> float:
        return self.result.diagnostics.pressure_mean


def solve_mixed_stokes(
    system: SemiDiscreteFlowSystem,
    *,
    tolerance: float = 1.0e-10,
) -> MixedSolution:
    """Solve a saddle system with an explicit zero-mean pressure gauge."""

    if tolerance <= 0.0:
        raise ValueError("tolerance must be positive")

    block = system.block_matrix()
    rhs = system.right_hand_side()
    velocity_count = system.velocity_count
    weights = system.gauge_weights
    gauge = jnp.concatenate((jnp.zeros((velocity_count,), dtype=block.dtype), weights))
    augmented = jnp.block(
        [
            [block, gauge[:, None]],
            [gauge[None, :], jnp.zeros((1, 1), dtype=block.dtype)],
        ]
    )
    augmented_rhs = jnp.concatenate((rhs, jnp.zeros((1,), dtype=rhs.dtype)))
    solution = jnp.linalg.lstsq(augmented, augmented_rhs, rcond=None)[0][:-1]
    state = FlowState(solution[:velocity_count], solution[velocity_count:])
    diagnostics = system.diagnostics(state)
    residual_norm = float(jnp.hypot(diagnostics.momentum_residual_norm, diagnostics.incompressibility_norm))
    return MixedSolution(
        FlowSolveResult(
            state=state,
            diagnostics=diagnostics,
            converged=residual_norm <= tolerance,
            iterations=1,
            backend="jax-dense",
            metadata={"system": system.name, "residual_tolerance": tolerance},
        )
    )
