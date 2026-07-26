"""Command-line entry points for the numerical studies."""

from __future__ import annotations

import argparse
from collections.abc import Callable, Sequence


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(prog="python -m experiments")
    parser.add_argument(
        "study",
        choices=("surface-viscosity", "thin-shell", "finite-elements"),
    )
    args, remainder = parser.parse_known_args(argv)
    entrypoint: Callable[[Sequence[str] | None], None]
    if args.study == "surface-viscosity":
        from experiments.surface_viscosity import main as entrypoint
    elif args.study == "thin-shell":
        from experiments.thin_shell import main as entrypoint
    else:
        from experiments.finite_elements import main as entrypoint
    entrypoint(remainder)


if __name__ == "__main__":
    main()
