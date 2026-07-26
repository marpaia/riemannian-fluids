"""One lean executable adapter per paper in the Riemannian-fluid corpus."""

from riemannian_fluids.validation import PaperModule, paper_module, validate_registry

from . import (
    chan_czubak_2013_hyperbolic,
    chan_czubak_2015_liouville,
    chan_czubak_2021_stokes,
    chan_czubak_2025_gauss,
    chan_czubak_disconzi_2017,
    chan_czubak_fuster_aguilera_2025,
    chan_czubak_pinilla_suarez_2025,
    chan_czubak_yoneda_2023,
    czubak_2024_survey,
    wang_braunstein_2026_kinematic,
    wang_braunstein_2026_shell,
)

MODULES: tuple[PaperModule, ...] = tuple(
    paper_module(module)
    for module in (
        czubak_2024_survey,
        chan_czubak_disconzi_2017,
        chan_czubak_yoneda_2023,
        chan_czubak_2025_gauss,
        chan_czubak_fuster_aguilera_2025,
        wang_braunstein_2026_kinematic,
        wang_braunstein_2026_shell,
        chan_czubak_2013_hyperbolic,
        chan_czubak_2015_liouville,
        chan_czubak_2021_stokes,
        chan_czubak_pinilla_suarez_2025,
    )
)
validate_registry(MODULES)


def find_paper(paper_id: str) -> PaperModule:
    try:
        return next(module for module in MODULES if module.paper.id == paper_id)
    except StopIteration as error:
        choices = ", ".join(module.paper.id for module in MODULES)
        raise KeyError(f"unknown paper {paper_id!r}; choose from {choices}") from error


__all__ = ("MODULES", "find_paper")
