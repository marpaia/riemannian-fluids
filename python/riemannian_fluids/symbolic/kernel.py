"""Symbolic covariant calculus: the SymPy twin of ``tensors/calculus.py`` and ``operators/viscosity.py``.

All functions take contravariant component tuples in a chart's coordinates and
return SymPy expressions or matrices.  Index conventions and signs follow
``symbolic/conventions.py`` and are enforced against the JAX backend by the
cross-check tests.
"""

from __future__ import annotations

import sympy

from riemannian_fluids.symbolic.charts import SymbolicManifold
from riemannian_fluids.symbolic.simplify import simp

type Components = tuple[sympy.Expr, ...]


def _diff(expr: sympy.Expr, coord: sympy.Symbol) -> sympy.Expr:
    return sympy.diff(expr, coord)


def christoffel_symbols(manifold: SymbolicManifold) -> list[list[list[sympy.Expr]]]:
    """Return ``Gamma[k][i][j] = Gamma^k_ij``."""

    coords = manifold.coords
    g = manifold.metric
    inverse = manifold.inverse_metric
    n = manifold.dimension
    gamma = [[[sympy.Integer(0) for _ in range(n)] for _ in range(n)] for _ in range(n)]
    for k in range(n):
        for i in range(n):
            for j in range(n):
                total = sympy.Integer(0)
                for ell in range(n):
                    total += inverse[k, ell] * (_diff(g[j, ell], coords[i]) + _diff(g[i, ell], coords[j]) - _diff(g[i, j], coords[ell])) / 2
                gamma[k][i][j] = simp(total)
    return gamma


def lower_index(manifold: SymbolicManifold, vector: Components) -> Components:
    g = manifold.metric
    return tuple(sum(g[i, j] * vector[j] for j in range(manifold.dimension)) for i in range(manifold.dimension))


def raise_index(manifold: SymbolicManifold, covector: Components) -> Components:
    inverse = manifold.inverse_metric
    return tuple(sum(inverse[i, j] * covector[j] for j in range(manifold.dimension)) for i in range(manifold.dimension))


def gradient(manifold: SymbolicManifold, scalar: sympy.Expr) -> Components:
    return raise_index(manifold, tuple(_diff(scalar, coord) for coord in manifold.coords))


def covariant_derivative_vector(manifold: SymbolicManifold, vector: Components) -> sympy.Matrix:
    """Return the matrix ``[k, i] = nabla_i u^k``."""

    n = manifold.dimension
    gamma = christoffel_symbols(manifold)
    result = sympy.zeros(n, n)
    for k in range(n):
        for i in range(n):
            result[k, i] = _diff(vector[k], manifold.coords[i]) + sum(gamma[k][i][ell] * vector[ell] for ell in range(n))
    return result


def divergence(manifold: SymbolicManifold, vector: Components) -> sympy.Expr:
    return simp(sum(covariant_derivative_vector(manifold, vector)[i, i] for i in range(manifold.dimension)))


def covariant_derivative_covector(manifold: SymbolicManifold, covector: Components) -> sympy.Matrix:
    """Return the matrix ``[j, i] = nabla_i alpha_j``."""

    n = manifold.dimension
    gamma = christoffel_symbols(manifold)
    result = sympy.zeros(n, n)
    for j in range(n):
        for i in range(n):
            result[j, i] = _diff(covector[j], manifold.coords[i]) - sum(gamma[k][i][j] * covector[k] for k in range(n))
    return result


def deformation_tensor(manifold: SymbolicManifold, vector: Components) -> sympy.Matrix:
    """Return the covariant symmetric tensor ``Def_ij``."""

    derivative = covariant_derivative_covector(manifold, lower_index(manifold, vector))
    return (derivative + derivative.T) / 2


def exterior_derivative_one_form(manifold: SymbolicManifold, vector: Components) -> sympy.Matrix:
    """Return ``F[i, j] = d_i alpha_j - d_j alpha_i`` for ``alpha = u-flat``, matching the numeric layer."""

    lowered = lower_index(manifold, vector)
    n = manifold.dimension
    result = sympy.zeros(n, n)
    for i in range(n):
        for j in range(n):
            result[i, j] = _diff(lowered[j], manifold.coords[i]) - _diff(lowered[i], manifold.coords[j])
    return result


def ricci_tensor(manifold: SymbolicManifold) -> sympy.Matrix:
    """Return the covariant Ricci tensor ``Ric_ij``."""

    n = manifold.dimension
    coords = manifold.coords
    gamma = christoffel_symbols(manifold)
    result = sympy.zeros(n, n)
    for i in range(n):
        for j in range(n):
            total = sympy.Integer(0)
            for k in range(n):
                total += _diff(gamma[k][i][j], coords[k]) - _diff(gamma[k][i][k], coords[j])
                for ell in range(n):
                    total += gamma[k][i][j] * gamma[ell][k][ell] - gamma[k][i][ell] * gamma[ell][j][k]
            result[i, j] = simp(total)
    return result


def scalar_curvature(manifold: SymbolicManifold) -> sympy.Expr:
    inverse = manifold.inverse_metric
    ricci = ricci_tensor(manifold)
    return simp(sum(inverse[i, j] * ricci[i, j] for i in range(manifold.dimension) for j in range(manifold.dimension)))


def ricci_action(manifold: SymbolicManifold, vector: Components) -> Components:
    """Return the contravariant components of ``sharp(Ric(u, .))``."""

    ricci = ricci_tensor(manifold)
    lowered = tuple(sum(ricci[i, j] * vector[j] for j in range(manifold.dimension)) for i in range(manifold.dimension))
    return raise_index(manifold, lowered)


def vector_squared_norm(manifold: SymbolicManifold, vector: Components) -> sympy.Expr:
    lowered = lower_index(manifold, vector)
    return sum(lowered[i] * vector[i] for i in range(manifold.dimension))


def covariant_tensor_squared_norm(manifold: SymbolicManifold, tensor: sympy.Matrix) -> sympy.Expr:
    inverse = manifold.inverse_metric
    n = manifold.dimension
    total = sympy.Integer(0)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for ell in range(n):
                    total += inverse[i, k] * inverse[j, ell] * tensor[i, j] * tensor[k, ell]
    return total


def _covariant_derivative_two_tensor(manifold: SymbolicManifold, tensor: sympy.Matrix) -> list[list[list[sympy.Expr]]]:
    """Return ``[i][j][k] = nabla_k T_ij`` for a covariant two-tensor."""

    n = manifold.dimension
    gamma = christoffel_symbols(manifold)
    coords = manifold.coords
    result = [[[sympy.Integer(0) for _ in range(n)] for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            for k in range(n):
                value = _diff(tensor[i, j], coords[k])
                value -= sum(gamma[ell][k][i] * tensor[ell, j] for ell in range(n))
                value -= sum(gamma[ell][k][j] * tensor[i, ell] for ell in range(n))
                result[i][j][k] = value
    return result


def rough_laplacian(manifold: SymbolicManifold, vector: Components) -> Components:
    """Return the positive connection Laplacian ``-tr_g(nabla^2 u)``."""

    n = manifold.dimension
    coords = manifold.coords
    inverse = manifold.inverse_metric
    gamma = christoffel_symbols(manifold)
    first = covariant_derivative_vector(manifold, vector)
    components: list[sympy.Expr] = []
    for k in range(n):
        total = sympy.Integer(0)
        for i in range(n):
            for j in range(n):
                second = _diff(first[k, j], coords[i])
                second += sum(gamma[k][i][ell] * first[ell, j] for ell in range(n))
                second -= sum(gamma[ell][i][j] * first[k, ell] for ell in range(n))
                total += inverse[i, j] * second
        components.append(simp(-total))
    return tuple(components)


def deformation_laplacian(manifold: SymbolicManifold, vector: Components) -> Components:
    """Return the positive operator ``2 Def* Def`` applied to ``u``."""

    n = manifold.dimension
    inverse = manifold.inverse_metric
    tensor = deformation_tensor(manifold, vector)
    covariant = _covariant_derivative_two_tensor(manifold, tensor)
    divergence_covector = tuple(sum(inverse[i, k] * covariant[i][j][k] for i in range(n) for k in range(n)) for j in range(n))
    return tuple(simp(-2 * component) for component in raise_index(manifold, divergence_covector))


def hodge_laplacian(manifold: SymbolicManifold, vector: Components) -> Components:
    """Return ``sharp((d delta + delta d)(u-flat))``."""

    n = manifold.dimension
    coords = manifold.coords
    inverse = manifold.inverse_metric
    negative_divergence = -divergence(manifold, vector)
    d_delta = tuple(_diff(negative_divergence, coords[i]) for i in range(n))
    two_form = exterior_derivative_one_form(manifold, vector)
    covariant = _covariant_derivative_two_tensor(manifold, two_form)
    delta_two_form = tuple(-sum(inverse[j, k] * covariant[j][i][k] for j in range(n) for k in range(n)) for i in range(n))
    combined = tuple(d_delta[i] + delta_two_form[i] for i in range(n))
    return tuple(simp(component) for component in raise_index(manifold, combined))
