"""Two-implementation checks: symbolic expressions against the JAX backend.

Every symbolic quantity with a numeric twin is evaluated at deterministic
random points inside the chart's sample window and compared in float64.  A
failure means the two backends disagree about the mathematics, so callers
treat it as an error, not a warning.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass

import jax
import jax.numpy as jnp
import numpy as np
import sympy

from riemannian_fluids.symbolic.charts import SymbolicManifold
from riemannian_fluids.symbolic.kernel import Components

enable_x64 = jax.enable_x64

type ParamValues = Mapping[sympy.Symbol, float]
type NumericVectorFn = Callable[[jnp.ndarray], jnp.ndarray]

DEFAULT_POINTS = 8
DEFAULT_RTOL = 1e-8


class CrossCheckError(AssertionError):
    """The symbolic and numeric backends disagree beyond tolerance."""


@dataclass(frozen=True)
class CrossCheck:
    quantity: str
    max_error: float
    rtol: float
    points: int

    @property
    def passed(self) -> bool:
        return self.max_error <= self.rtol


def sample_points(chart: SymbolicManifold, count: int = DEFAULT_POINTS, seed: int = 0) -> np.ndarray:
    rng = np.random.default_rng(seed)
    lows = np.asarray([window[0] for window in chart.sample_window])
    highs = np.asarray([window[1] for window in chart.sample_window])
    return rng.uniform(lows, highs, size=(count, chart.dimension))


def lambdify_components(chart: SymbolicManifold, components: Components, params: ParamValues) -> Callable[[np.ndarray], np.ndarray]:
    substituted = [sympy.sympify(component).subs(params) for component in components]
    remaining = set().union(*(component.free_symbols for component in substituted)) - set(chart.coords)
    if remaining:
        raise ValueError(f"unbound parameters {sorted(remaining, key=str)}; supply values for every chart parameter")
    functions = [sympy.lambdify(chart.coords, component, modules="numpy") for component in substituted]

    def evaluate(q: np.ndarray) -> np.ndarray:
        return np.asarray([function(*q) for function in functions], dtype=np.float64)

    return evaluate


def crosscheck_components(
    chart: SymbolicManifold,
    components: Components,
    numeric_fn: NumericVectorFn,
    params: ParamValues,
    *,
    quantity: str,
    count: int = DEFAULT_POINTS,
    seed: int = 0,
    rtol: float = DEFAULT_RTOL,
) -> CrossCheck:
    """Compare symbolic components against a numeric backend function pointwise."""

    symbolic_fn = lambdify_components(chart, components, params)
    points = sample_points(chart, count, seed)
    max_error = 0.0
    with enable_x64(True):
        for q in points:
            expected = symbolic_fn(q)
            actual = np.asarray(numeric_fn(jnp.asarray(q, dtype=jnp.float64)), dtype=np.float64)
            scale = 1.0 + np.abs(expected).max()
            max_error = max(max_error, float(np.abs(expected - actual).max() / scale))
    return CrossCheck(quantity=quantity, max_error=max_error, rtol=rtol, points=count)


def require_agreement(check: CrossCheck) -> CrossCheck:
    if not check.passed:
        raise CrossCheckError(f"{check.quantity}: max scaled error {check.max_error:.3e} exceeds rtol {check.rtol:.1e}")
    return check


def crosscheck_scalar(
    chart: SymbolicManifold,
    expr: sympy.Expr,
    numeric_fn: Callable[[jnp.ndarray], jnp.ndarray],
    params: ParamValues,
    *,
    quantity: str,
    count: int = DEFAULT_POINTS,
    seed: int = 0,
    rtol: float = DEFAULT_RTOL,
) -> CrossCheck:
    check = crosscheck_components(
        chart,
        (expr,),
        lambda q: jnp.asarray([numeric_fn(q)]),
        params,
        quantity=quantity,
        count=count,
        seed=seed,
        rtol=rtol,
    )
    return check
