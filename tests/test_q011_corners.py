"""Regression checks for the two formerly open 2003 corners."""

from research.ladder import Ladder, audit
from research.p17_vrc_boundary import DA_2003, NE_THESIS
from research.p21_least_preorder import integer_potential
from research.p26_q011_unrestricted import CornerWitness, certificate
from research.p27_ranged_ne_integer import (
    WITNESS,
    _psi,
    bounded_audit,
    invariant_obligations,
    path_closure,
)
from research.schema import Instance


def test_not_worse_da_contradicts_pair_and_carrier_dependent_witness() -> None:
    witness = CornerWitness(
        "dependent-regression",
        {(4, 1): 1, (5, 1): 2, (6, 1): 1},
        {-1: (5, 3, 2), 0: (6, 3, 1)},
        {"x": -1, "u": 4, "v": 6, "y": 3, "n": 1, "m": 1},
    )
    result = certificate(witness)

    assert result["legal"]
    assert result["target"] == [1] * 48 + [6]
    assert result["edges"]["all_replayed_and_audited"]
    assert result["instances"]["dominance_addition_audited"]
    assert result["instances"]["egalitarian_dominance_audited"]
    assert result["instances"]["decision_without_completeness"] == "unsat"


def test_ranged_ne_negative_step_preserves_post_vrc_barrier_on_full_chain() -> None:
    ladder = Ladder(negative=3, positive=6)
    source, target = (-1, -1), (-2, 0)
    assert audit(Instance(NE_THESIS, (source, target)), ladder, WITNESS)
    assert _psi(source) == 2 and _psi(target) == 1
    assert audit(Instance(DA_2003, ((-2, 1), (-3,))), ladder, WITNESS)

    # The finite quadratic potential cannot replace the increasing full-chain F.
    assert integer_potential(21) > integer_potential(20)
    assert invariant_obligations()["all_discharged"]
    assert path_closure()["post_vrc_invariant_decision"] == "unsat"
    diagnostic = bounded_audit(ladder, cap=3, include_empty=True)
    assert diagnostic["cyclic_scc_count"] == 0
    assert diagnostic["ed_reversals"] == 0
    assert diagnostic["vrc_images_reaching_a_negative_free_state"] == 0
