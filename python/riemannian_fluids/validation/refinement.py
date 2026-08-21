"""Convergence diagnostics shared by paper reproductions."""

from __future__ import annotations

import math
from collections.abc import Sequence


def observed_orders(scales: Sequence[float], errors: Sequence[float]) -> tuple[float, ...]:
    if len(scales) != len(errors) or len(scales) < 2:
        raise ValueError("scales and errors need the same length of at least two")
    if any(value <= 0.0 for value in (*scales, *errors)):
        raise ValueError("scales and errors must be positive")
    return tuple(math.log(errors[index] / errors[index - 1]) / math.log(scales[index] / scales[index - 1]) for index in range(1, len(scales)))


def fitted_order(scales: Sequence[float], errors: Sequence[float]) -> float:
    """Return the least-squares slope of ``log(error)`` against ``log(scale)``."""

    if len(scales) != len(errors) or len(scales) < 2:
        raise ValueError("scales and errors need the same length of at least two")
    if any(value <= 0.0 for value in (*scales, *errors)):
        raise ValueError("scales and errors must be positive")
    log_scales = [math.log(value) for value in scales]
    log_errors = [math.log(value) for value in errors]
    mean_scale = sum(log_scales) / len(log_scales)
    mean_error = sum(log_errors) / len(log_errors)
    numerator = sum((s - mean_scale) * (e - mean_error) for s, e in zip(log_scales, log_errors, strict=True))
    denominator = sum((s - mean_scale) ** 2 for s in log_scales)
    return numerator / denominator


def monotone_refinement(errors: Sequence[float], *, slack: float = 0.0) -> bool:
    return all(right <= left + slack for left, right in zip(errors, errors[1:], strict=False))
