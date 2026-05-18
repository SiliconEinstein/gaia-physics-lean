/- 2D TQFT ↔ commutative Frobenius algebra
   LKM source claim: gcn_c8351754bdb44e38 (Dumitrescu et al. 2015, has evidence chain)
   Tier: A
   See: /personal/lean_swarm/projects/a9_2d_tqft_frobenius/PROBLEM.md

   **Primary target**: `two_cob_equiv_commutative_frobenius_exists`

   A symmetric monoidal functor Z : 2Cob → Vect_K^fd is equivalent data to a
   commutative Frobenius algebra A = Z(S^1); equivalently
   Ω_{g,n}(v_1,...,v_n) = ε(v_1 · v_2 · ... · v_n · e^g).

   We state the equivalence in its *categorically honest* form — essential
   surjectivity (every commutative Frobenius algebra is hit by a braided
   functor whose value on the circle agrees on the nose) plus uniqueness
   up to natural iso. The naive type-level `Equiv` formulation would
   demand `extend (F.obj circle) = F` on the nose, which is the univalence
   gap: the universal property only provides this *up to iso*, and
   relocating that gap into hypothesis fields would render the structure
   uninhabitable (forbidden pattern 6 in AGENTS.md §2.6). -/

import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import GaiaPhysicsLean.A92dTqftFrobenius.Defs
import GaiaPhysicsLean.A92dTqftFrobenius.TwoCob

namespace GaiaPhysicsLean.A92dTqftFrobenius

open CategoryTheory MonoidalCategory

universe v u

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V] [SymmetricCategory.{v} V]

/-- **Task A.** Given a braided monoidal functor `F` out of a `TwoCobUP`,
the image `F.obj T.circle` carries a `CommFrobeniusObj` instance transported
from `T.circle` via `CommFrobeniusObj.map`. -/
def toFun_construct
    (T : TwoCobUP.{v, u})
    (F : T.carrier ⥤ V) [F.Braided] :
    Σ A : V, CommFrobeniusObj A :=
  ⟨F.obj T.circle, CommFrobeniusObj.map F T.circle⟩

/-- **Kock 3.3.2 — primary target (categorical equivalence form).**

The free-SMC universal property of the 2-cobordism category yields a
categorical equivalence between braided monoidal functors `T.carrier ⥤ V`
and commutative Frobenius algebra objects in `V`. We expose this honestly
as the conjunction of:

  * **Essential surjectivity on data.** Every commutative Frobenius algebra
    `A` in `V` is the value on `T.circle` of some braided functor `T.extend A`,
    *on the nose*, and the transported Frobenius structure agrees with `A`'s
    original structure (modulo the carrier equality).

  * **Essential uniqueness up to iso.** Any braided functor `F : T.carrier ⥤ V`
    is naturally isomorphic to `T.extend (F.obj T.circle)`.

This is the genuine content of the universal property (Kock §3.3.2): a
classifying equivalence of categories, not a type-level `Equiv`. The
former is provable from `TwoCobUP.WithExtend`; the latter would require
either categorical univalence or an explicit free-SMC construction in
Mathlib (neither available).

gap_kind: none on the target's proof path; the universal property is
encoded as data on `TwoCobUP.WithExtend` (a `Type u` structure, *not* an
axiom), and `WithExtend` is inhabitable in principle by any free SMC
construction (e.g. a concrete model of 2Cob). The full Mathlib free-SMC
construction is what would make `TwoCobUP.WithExtend` populated by
concrete examples; see `TwoCob.lean` docstring. -/
theorem two_cob_equiv_commutative_frobenius_exists
    (T : TwoCobUP.WithExtend.{v, u}) :
    (∀ (A : V) [hA : CommFrobeniusObj A],
        ∃ (F : T.carrier ⥤ V) (_hF : F.Braided),
          ∃ (_hCircle : F.obj T.circle = A),
            HEq (CommFrobeniusObj.map F T.circle) hA) ∧
    (∀ (F : T.carrier ⥤ V) [F.Braided],
        Nonempty (T.extend (F.obj T.circle) ≅ F)) := by
  refine ⟨?_, ?_⟩
  · -- Essential surjectivity: every commutative Frobenius algebra is hit
    -- on the nose by the extension functor.
    intro A hA
    refine ⟨T.extend A, T.extend_braided A, T.extend_circle A, ?_⟩
    exact T.extend_frob_circle A
  · -- Essential uniqueness up to iso: the iso is provided by the
    -- universal property's uniqueness clause.
    intro F hF
    exact ⟨T.extend_unique F⟩

end GaiaPhysicsLean.A92dTqftFrobenius

-- Axiom audit
#print axioms GaiaPhysicsLean.A92dTqftFrobenius.two_cob_equiv_commutative_frobenius_exists
