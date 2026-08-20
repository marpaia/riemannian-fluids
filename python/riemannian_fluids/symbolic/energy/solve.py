"""Certified evaluation of reduced energy integrals.

The solver assumes its integrand is a nonnegative energy density that is
continuous on the open radial interval (true for the densities constructed
here, whose only chart singularities sit at radial endpoints).  Under that
standing assumption the endpoint comparison tests used by the finiteness tier
are rigorous implications, not heuristics.
"""

from __future__ import annotations

from dataclasses import dataclass

import mpmath
import sympy

from riemannian_fluids.symbolic import kernel
from riemannian_fluids.symbolic.certificates import (
    Certificate,
    DerivationLedger,
    DivergentCertificate,
    ExactCertificate,
    FiniteCertificate,
    UnresolvedCertificate,
)
from riemannian_fluids.symbolic.charts import SymbolicManifold
from riemannian_fluids.symbolic.crosscheck import CrossCheck
from riemannian_fluids.symbolic.energy.domains import DomainSpec
from riemannian_fluids.symbolic.energy.reduce import RadialIntegral, reduce_to_radial
from riemannian_fluids.symbolic.fields import StructuredField
from riemannian_fluids.symbolic.simplify import expression_size, simp


def deformation_energy_density(field: StructuredField) -> sympy.Expr:
    """Return the viscous dissipation density ``2 |Def u|^2``."""

    manifold = field.manifold
    tensor = kernel.deformation_tensor(manifold, field.components())
    return simp(2 * kernel.covariant_tensor_squared_norm(manifold, tensor))


def dirichlet_energy_density(field: StructuredField) -> sympy.Expr:
    """Return the full covariant-derivative density ``|nabla u|^2``."""

    manifold = field.manifold
    derivative = kernel.covariant_derivative_vector(manifold, field.components())
    g = manifold.metric
    inverse = manifold.inverse_metric
    n = manifold.dimension
    total = sympy.Integer(0)
    for k in range(n):
        for ell in range(n):
            for i in range(n):
                for j in range(n):
                    total += g[k, ell] * inverse[i, j] * derivative[k, i] * derivative[ell, j]
    return simp(total)


@dataclass(frozen=True)
class EnergyIntegralResult:
    chart: SymbolicManifold
    domain: DomainSpec
    radial: RadialIntegral
    closed_form: sympy.Expr | None
    certificate: Certificate
    ledger: DerivationLedger


def _decided_limit(expr: sympy.Expr, variable: sympy.Symbol, point: sympy.Expr, direction: str) -> sympy.Expr | None:
    try:
        value = sympy.limit(expr, variable, point, direction)
    except (NotImplementedError, ValueError, RecursionError):
        return None
    if value.has(sympy.Limit, sympy.AccumBounds) or (value.free_symbols and not value.is_number):
        return None
    return value


def _finite_at_endpoint(integrand: sympy.Expr, variable: sympy.Symbol, point: sympy.Expr, direction: str) -> bool | None:
    """Comparison test at one endpoint for a nonnegative integrand: True, False, or undecided."""

    if point == sympy.oo:
        quadratic = _decided_limit(integrand * variable**2, variable, point, direction)
        if quadratic == 0:
            return True
        linear = _decided_limit(integrand * variable, variable, point, direction)
        if linear is not None and (linear == sympy.oo or linear.is_positive):
            return False
        return None
    value = _decided_limit(integrand, variable, point, direction)
    if value is not None and value.is_finite:
        return True
    root = _decided_limit(integrand * sympy.sqrt(sympy.Abs(variable - point)), variable, point, direction)
    if root == 0:
        return True
    linear = _decided_limit(integrand * (variable - point), variable, point, direction)
    if linear is not None and (linear == sympy.oo or linear.is_positive):
        return False
    return None


def _realify_logs(expr: sympy.Expr) -> sympy.Expr:
    """Normalize log branches: ``log(x) -> log(-x) + i*pi`` for provably negative ``x``.

    Antiderivatives on positive-parameter domains often pair a negative-argument
    logarithm with an explicit ``i*pi`` term; after this rewrite the imaginary
    parts cancel and the closed form displays as the real quantity it is.
    """

    replacements = {}
    for logarithm in expr.atoms(sympy.log):
        argument = logarithm.args[0]
        if argument.is_negative:
            replacements[logarithm] = sympy.log(-argument) + sympy.I * sympy.pi
    if not replacements:
        return expr
    candidate = sympy.expand(expr.subs(replacements))
    return candidate if not candidate.has(sympy.I) else expr


def _positivity_assumptions(radial: RadialIntegral) -> tuple[str, ...]:
    symbols = (radial.integrand.free_symbols | radial.interval[0].free_symbols | radial.interval[1].free_symbols) - {radial.variable}
    return tuple(f"{symbol} > 0" for symbol in sorted(symbols, key=str))


def energy_integral(
    density: sympy.Expr,
    chart: SymbolicManifold,
    domain: DomainSpec,
) -> EnergyIntegralResult:
    """Solve ``integral density dV`` over the domain with a tiered certificate.

    Tier one attempts an exact closed form; tier two proves finiteness or
    divergence by endpoint comparison; anything undecided is returned as an
    ``UnresolvedCertificate`` rather than a guess.
    """

    radial, ledger = reduce_to_radial(chart, density, domain)
    variable = radial.variable
    lower, upper = radial.interval
    assumptions = _positivity_assumptions(radial)

    normal_form = sympy.expand(radial.integrand.rewrite(sympy.exp))
    ledger = ledger.record(
        "normal-form", "rewrote hyperbolic/trigonometric factors as exponentials", expression_size(radial.integrand), expression_size(normal_form)
    )

    candidate: sympy.Expr | None
    try:
        candidate = sympy.integrate(normal_form, (variable, lower, upper))
    except (NotImplementedError, ValueError, RecursionError):
        candidate = None

    if candidate is not None and not candidate.has(sympy.Integral, sympy.Limit):
        closed = simp(_realify_logs(simp(candidate)))
        ledger = ledger.record("radial-integral", f"closed form over ({lower}, {upper})", expression_size(candidate), expression_size(closed))
        if closed.has(sympy.oo, sympy.zoo, sympy.nan):
            divergent = DivergentCertificate(assumptions, "the antiderivative evaluates to infinity")
            return EnergyIntegralResult(chart, domain, radial, None, divergent, ledger)
        return EnergyIntegralResult(chart, domain, radial, closed, ExactCertificate(assumptions), ledger)

    ledger = ledger.record("radial-integral", "no closed form; falling back to endpoint comparison", expression_size(normal_form), expression_size(normal_form))
    at_lower = _finite_at_endpoint(radial.integrand, variable, lower, "+")
    at_upper = _finite_at_endpoint(radial.integrand, variable, upper, "-")
    if at_lower is False or at_upper is False:
        which = f"radial endpoint {lower if at_lower is False else upper}"
        return EnergyIntegralResult(chart, domain, radial, None, DivergentCertificate(assumptions, f"comparison test diverges at {which}"), ledger)
    if at_lower is True and at_upper is True:
        return EnergyIntegralResult(chart, domain, radial, None, FiniteCertificate(assumptions), ledger)
    unresolved = UnresolvedCertificate("endpoint comparison tests were inconclusive; the answer may depend on parameter relations")
    return EnergyIntegralResult(chart, domain, radial, None, unresolved, ledger)


def verify_numerically(result: EnergyIntegralResult, params: dict[sympy.Symbol, float], *, rtol: float = 1e-8) -> CrossCheck:
    """Compare an exact closed form against high-precision quadrature of the radial integrand."""

    if result.closed_form is None:
        raise ValueError("numeric verification requires an exact closed form")
    variable = result.radial.variable
    integrand = result.radial.integrand.subs(params)
    unbound = integrand.free_symbols - {variable}
    if unbound:
        raise ValueError(f"unbound parameters {sorted(unbound, key=str)}")
    function = sympy.lambdify(variable, integrand, modules="mpmath")
    lower = mpmath.mpf(float(result.radial.interval[0].subs(params))) if result.radial.interval[0] != sympy.oo else mpmath.inf
    upper = mpmath.inf if result.radial.interval[1] == sympy.oo else mpmath.mpf(float(result.radial.interval[1].subs(params)))
    quadrature = mpmath.quad(function, [lower, upper])
    expected = float(result.closed_form.subs(params))
    error = abs(float(quadrature) - expected) / (1.0 + abs(expected))
    return CrossCheck(quantity="energy integral vs quadrature", max_error=error, rtol=rtol, points=1)
