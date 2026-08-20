"""Sign and orientation conventions shared with the numeric backend.

The symbolic backend implements ``analysis-positive-v1``:

- Christoffel symbols are indexed ``Gamma[k][i][j] = Gamma^k_ij``.
- The rough Laplacian is the positive connection Laplacian ``-tr_g(nabla^2 u)``.
- The deformation Laplacian is the positive operator ``2 Def* Def``.
- The Hodge Laplacian is ``sharp((d delta + delta d)(u-flat))``.
- A stream function on an oriented two-manifold generates the coexact field
  ``u = sharp(*d psi) = (d psi/dq^1, -d psi/dq^0) / sqrt(det g)``.

Every symbolic operator mirrors its JAX twin in ``tensors/`` and ``operators/``
function for function; the cross-backend tests in ``tests/test_symbolic_kernel.py``
enforce the agreement at sampled points.
"""

from __future__ import annotations

CONVENTION = "analysis-positive-v1"
