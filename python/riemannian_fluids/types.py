"""Small callable contracts shared by the mathematical modules."""

from collections.abc import Callable

import jax

Array = jax.Array
MetricField = Callable[[Array], Array]
Embedding = Callable[[Array], Array]
ScalarField = Callable[[Array], Array]
VectorField = Callable[[Array], Array]
CovectorField = Callable[[Array], Array]
TensorField = Callable[[Array], Array]
DifferentialForm = Callable[[Array], Array]
