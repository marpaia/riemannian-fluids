"""Run the DOLFINx normal-fibre refinement study on a chosen surface."""

from __future__ import annotations

import argparse
import json
from collections.abc import Sequence

import numpy as np

from experiments.surfaces import surface_cases
from riemannian_fluids.discretization import solve_normal_fibre
from riemannian_fluids.geometry import shape_operator
from riemannian_fluids.tensors import stream_vector_field


def parse_cells(raw: str) -> tuple[int, ...]:
    values = tuple(int(item) for item in raw.split(","))
    if not values or any(value < 2 for value in values):
        raise argparse.ArgumentTypeError("cells must be integers at least two")
    if any(right <= left for left, right in zip(values, values[1:], strict=False)):
        raise argparse.ArgumentTypeError("cells must be strictly increasing")
    return values


def validate_results(results: Sequence[dict[str, float | int | str]]) -> None:
    failures = []
    linear = [row for row in results if row["degree"] == 1]
    if len(linear) > 1 and float(linear[-1]["relative_l2_error"]) > float(
        linear[0]["relative_l2_error"]
    ):
        failures.append("P1 L2 error did not decrease")
    quadratic = [row for row in results if row["degree"] == 2]
    if any(float(row["relative_l2_error"]) > 1.0e-9 for row in quadratic):
        failures.append("P2 did not reproduce the quadratic")
    if any(float(row["analytic_two_wall_residual"]) > 1.0e-10 for row in results):
        failures.append("analytic field failed a wall condition")
    if failures:
        raise AssertionError("Finite-element validation failed:\n  " + "\n  ".join(failures))


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--surface", choices=tuple(case.name for case in surface_cases()), default="ellipsoid"
    )
    parser.add_argument("--q", type=float, nargs=2, default=(1.1, 0.7))
    parser.add_argument("--thickness", type=float, default=0.1)
    parser.add_argument("--alpha", type=float, default=0.5)
    parser.add_argument("--cells", type=parse_cells, default=parse_cells("8,16,32"))
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)
    case = next(case for case in surface_cases() if case.name == args.surface)
    q = np.asarray(args.q, dtype=np.float64)
    field = stream_vector_field(case.embedding, case.stream_function)
    shape = np.asarray(shape_operator(case.embedding, q), dtype=np.float64)
    u0 = np.asarray(field(q), dtype=np.float64)
    results = [
        {
            "surface": args.surface,
            **solve_normal_fibre(
                shape=shape,
                u0=u0,
                thickness=args.thickness,
                alpha=args.alpha,
                cells=cells,
                degree=degree,
            ),
        }
        for degree in (1, 2)
        for cells in args.cells
    ]
    validate_results(results)
    if args.as_json:
        print(json.dumps(results, indent=2, sort_keys=True))
        return
    print("DOLFINx normal-fibre manufactured PDE")
    print("degree cells     relative L2  relative H1  wall residual")
    for row in results:
        print(
            f"P{int(row['degree']):<6d} {int(row['cells']):<8d} "
            f"{float(row['relative_l2_error']):.3e}    "
            f"{float(row['relative_h1_seminorm_error']):.3e}    "
            f"{float(row['two_wall_residual_l2']):.3e}"
        )


if __name__ == "__main__":
    main()
