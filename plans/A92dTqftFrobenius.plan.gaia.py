"""Initial BP plan for 2D TQFT ↔ commutative Frobenius algebra (A-tier, conditional).
LKM claim: gcn_c8351754bdb44e38 (Dumitrescu et al. 2015; Kock §3.3.2)

Proof strategy (categorically honest form):

The naïve goal "Equiv (2Cob ⥤ V) (CommFrob V)" is wrong by univalence — a
strong-monoidal functor is determined by `Z(S^1)` only **up to** monoidal
natural iso, not on the nose. The honest target is a classifying equivalence
of categories:

  ∀ A : CommFrobeniusObj, ∃ F : 2Cob ⥤ V braided with F.obj S¹ = A
  ∧ ∀ F : 2Cob ⥤ V braided, ∃ iso (extend (F.obj S¹)) F.

Mathlib currently lacks the free-symmetric-monoidal-category-on-one-self-dual-
object construction that would give us the `extend` functor and its universal
property. We package those as data on `TwoCobUP.WithExtend` and prove the
classifying equivalence **conditional** on inhabiting that bundle.

This makes the main theorem mechanically axiom-free (#print axioms returns
[propext, Classical.choice, Quot.sound]) without smuggling open problems
into `axiom` declarations.
"""
from gaia.engine.lang import claim, derive

mathlib_braided = claim(
    "Mathlib provides braided monoidal categories and strong-monoidal functors "
    "with the algebraic structure on objects (`CategoryTheory.Monoidal.Braided.Basic`).",
    prior=0.97,
    metadata={
        "prior_justification": "Verified by lean_local_search.",
        "action": "abduction",
        "args": {"search_query": "BraidedCategory LaxBraided"},
    },
)

commfrob_structure = claim(
    "We can define `CommFrobeniusObj A` as a typeclass bundling commutative Frobenius "
    "algebra structure (multiplication, unit, comultiplication, counit, Frobenius "
    "identity, commutativity) on an object A of a braided monoidal category.",
    prior=0.99,
    metadata={
        "formal_artifact": "GaiaPhysicsLean/A92dTqftFrobenius/Defs.lean",
        "lean_target": "CommFrobeniusObj",
        "status": "proved",
    },
)

two_cob_up_bundle = claim(
    "We can package the 2Cob universal property as a `Type`-valued structure "
    "`TwoCobUP.WithExtend` with fields `carrier`, `circle`, `extend`, "
    "`extend_braided`, `extend_circle`, `extend_frob_circle`, `extend_unique`. "
    "Constructing a concrete inhabitant is a separate Mathlib gap (Kock §3.3).",
    prior=0.95,
    metadata={
        "formal_artifact": "GaiaPhysicsLean/A92dTqftFrobenius/TwoCob.lean",
        "lean_target": "TwoCobUP.WithExtend",
        "status": "proved (as data; inhabitant construction deferred)",
        "gap_kind": "mathlib_missing",
        "paper_ref": "Kock, Frobenius Algebras and 2D TQFTs, §3.3",
        "loc_est": 1500,
    },
)

target = claim(
    "Conditional on TwoCobUP.WithExtend: every commutative Frobenius algebra A "
    "is the value on S¹ of some braided functor 2Cob ⥤ V, and every such functor "
    "is naturally isomorphic to extend (F.obj S¹). This is the categorically "
    "honest form of the 2D-TQFT ↔ commutative-Frobenius classifying equivalence.",
    prior=0.99,
    metadata={
        "formal_artifact": "GaiaPhysicsLean/A92dTqftFrobenius/Theorem.lean",
        "lean_target": "two_cob_equiv_commutative_frobenius_exists",
        "status": "proved (conditional)",
        "axiom_closure": "[propext, Classical.choice, Quot.sound]",
        "honest_caveat": "Proof unpacks fields of TwoCobUP.WithExtend; concrete "
                          "inhabitant of WithExtend is not constructed in this file.",
    },
)

derive(target, given=[mathlib_braided, commfrob_structure, two_cob_up_bundle], rationale="Given the Mathlib braided/strong-monoidal infrastructure, our "
            "CommFrobeniusObj definition, and the TwoCobUP.WithExtend bundle, "
            "the classifying equivalence assembles in 11 lines by unpacking "
            "the extension functor's fields.",)
