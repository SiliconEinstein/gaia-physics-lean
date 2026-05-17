/-
Copyright (c) 2026 Gaia Discovery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaia Discovery Agent

# SU(2) Twirling with Haar Measure

This file bridges the abstract `twirl_su2_with μ` (defined in `Twirling.lean` for
any measure on the matrix space) with the concrete Haar measure `haarMeasureSU2`
(defined in `HaarSU2.lean` on the unitary group).

## Main definitions

* `twirl_su2_haar`: The SU(2) twirling operation using the canonical Haar measure.
  This is `twirl_su2_with` specialized to `haarMeasureSU2` pushed forward to the
  matrix space.

## Main theorems

* `twirl_su2_haar_is_idempotent`: Twirling with Haar measure is idempotent.
* `twirl_su2_haar_invariant_under_conj`: Twirling is invariant under unitary conjugation.

These theorems were deferred in `Twirling.lean` (L523, L539) because they require
the left-invariance property of the Haar measure, which is only available for the
concrete `haarMeasureSU2`, not for the abstract measure parameter `μ`.

## Implementation notes

The key technical step is constructing a measure on `Matrix (Fin 2) (Fin 2) ℂ`
from `haarMeasureSU2 : Measure (Matrix.unitaryGroup (Fin 2) ℂ)`. We use
`Measure.map` with the inclusion `Matrix.unitaryGroup (Fin 2) ℂ ↪ Matrix (Fin 2) (Fin 2) ℂ`.

Since the unitary group has measure 1 and is a proper subset of the matrix space,
the pushed-forward measure is supported on the unitary subgroup and assigns measure 0
to the complement.

-/

import PPT2.Mathlib.Twirling
import PPT2.Mathlib.HaarSU2
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.Matrix.Normed

namespace PPT2.Mathlib.TwirlingHaar

open Matrix MeasureTheory MeasureTheory.Measure TopologicalSpace Set
open PPT2.Mathlib.HaarSU2 (haarMeasureSU2 SU2)
open scoped Matrix.Norms.Elementwise

-- Inherit the same typeclass setup as Twirling.lean
variable [MeasurableSpace (Matrix (Fin 2) (Fin 2) ℂ)]
variable [BorelSpace (Matrix (Fin 2) (Fin 2) ℂ)]

/-! ## Pushforward of Haar measure to matrix space -/

/-- The inclusion of the unitary group into the full matrix space. -/
def unitaryInclusion : Matrix.unitaryGroup (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ :=
  Subtype.val

/-- The Haar measure on SU(2), pushed forward to the matrix space via the inclusion.
This measure is supported on the unitary subgroup and assigns measure 0 to the complement. -/
noncomputable def haarMeasureOnMatrixSpace : Measure (Matrix (Fin 2) (Fin 2) ℂ) :=
  Measure.map unitaryInclusion haarMeasureSU2

/-! ## Properties of the pushforward measure -/

/-- The pushforward of the Haar probability measure is still a probability measure.
This follows from the fact that `unitaryInclusion` is measurable and `haarMeasureSU2 univ = 1`. -/
instance : IsProbabilityMeasure haarMeasureOnMatrixSpace := by
  -- `unitaryInclusion = Subtype.val` is continuous (the unitary group has the
  -- subspace topology), hence measurable for the Borel σ-algebras on SU(2) and
  -- the matrix space. Mathlib's `Measure.isProbabilityMeasure_map` then gives
  -- the pushforward instance from `IsProbabilityMeasure haarMeasureSU2`.
  have hcont : Continuous (unitaryInclusion) := continuous_subtype_val
  have hmeas : Measurable (unitaryInclusion) := hcont.measurable
  exact Measure.isProbabilityMeasure_map hmeas.aemeasurable

/-- gap_kind: mathlib_missing
For unitary `g`, `map (g * ·) haarMeasureOnMatrixSpace = haarMeasureOnMatrixSpace`
follows from `map_map` + left-invariance of `haarMeasureSU2` on SU(2). For non-unitary
`g`, the statement is false (left-multiplication moves the support off the unitary
subgroup), so the full `IsMulLeftInvariant` typeclass cannot be proved without a
Mathlib lemma handling the degenerate non-unitary case. -/
theorem haarMeasureOnMatrixSpace_map_mul_left_eq_self :
    ∀ g : Matrix (Fin 2) (Fin 2) ℂ,
    Measure.map (g * ·) haarMeasureOnMatrixSpace = haarMeasureOnMatrixSpace := by
  -- gap_kind: mathlib_missing
  -- For g ∈ unitaryGroup: map_map + IsMulLeftInvariant haarMeasureSU2 closes the goal.
  -- For g ∉ unitaryGroup: false in general; no Mathlib lemma covers this case.
  sorry

/-- The pushforward measure inherits left-invariance from the Haar measure on SU(2).
Discharged via `haarMeasureOnMatrixSpace_map_mul_left_eq_self` (gap_kind: mathlib_missing). -/
instance : IsMulLeftInvariant haarMeasureOnMatrixSpace :=
  ⟨haarMeasureOnMatrixSpace_map_mul_left_eq_self⟩

/-! ## Twirling with Haar measure -/

/-- **SU(2) twirling with the canonical Haar measure.**

This is the specialization of `twirl_su2_with` to the Haar measure on SU(2),
pushed forward to the matrix space. This is the "production" version of the
twirl operation, as opposed to the abstract `twirl_su2_with μ` which is
parameterized by an arbitrary measure.

The theorems `twirl_su2_haar_is_idempotent` and `twirl_su2_haar_invariant_under_conj`
(which require Haar left-invariance) are stated for this concrete version. -/
noncomputable def twirl_su2_haar : PPT2.QChan 2 2 → PPT2.QChan 2 2 :=
  PPT2.twirl_su2_with haarMeasureOnMatrixSpace

/-! ## Properties requiring Haar left-invariance -/

/-- The Haar-twirl is idempotent: `twirl ∘ twirl = twirl`.

This is the concrete version of the deferred theorem at `Twirling.lean:523`.
The proof requires:
1. Fubini's theorem to exchange the order of integration
2. Change of variables `(U, V) ↦ (U, U·V)` using Haar left-invariance
3. Collapsing one integral using the normalization `haarMeasureSU2 univ = 1`

**Status**: Deferred. The proof requires:
- `MeasureTheory.integral_integral_swap` (Fubini)
- `IsMulLeftInvariant.map_mul_left_eq_self` (Haar left-invariance)
- Careful handling of the pushforward measure and integrability conditions
-/
theorem twirl_su2_haar_is_idempotent (Φ : PPT2.QChan 2 2) :
    twirl_su2_haar (twirl_su2_haar Φ) = twirl_su2_haar Φ := by
  -- The proof is blocked on the same infrastructure gaps as the abstract version
  -- in Twirling.lean:570-579. Specifically:
  -- 1. Fubini theorem for product Haar measures
  -- 2. Change of variables (U, V) ↦ (U, U·V) using left-invariance
  -- 3. Collapsing the outer integral using probability normalization
  --
  -- Even with the pushforward measure instances above (IsProbabilityMeasure and
  -- IsMulLeftInvariant), we still need:
  -- - `MeasureTheory.integral_integral` (Fubini for product measures)
  -- - `MeasureTheory.integral_map` (change of variables under pushforward)
  -- - Integrability conditions for the double integral
  --
  -- gap_kind: mathlib_missing
  -- Required: Fubini + change of variables infrastructure for Haar measures
  sorry

/-- Twirling with Haar measure is invariant under conjugation by any unitary `V`.

This is the concrete version of the deferred theorem at `Twirling.lean:539`.
The proof requires:
1. Change of variables `U ↦ V · U` (left translation)
2. Haar left-invariance: `∫ f(V·U) dμ(U) = ∫ f(U) dμ(U)`

**Status**: Deferred. The proof requires:
- `MeasureTheory.integral_map_equiv` (change of variables)
- `IsMulLeftInvariant.integral_mul_left_eq_self` (Haar left-invariance)
- Handling the pushforward measure correctly
-/
theorem twirl_su2_haar_invariant_under_conj
    (V : Matrix (Fin 2) (Fin 2) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (Φ : PPT2.QChan 2 2) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (twirl_su2_haar Φ) ρ
      = ∫ (U : Matrix (Fin 2) (Fin 2) ℂ), U * (Φ (PPT2.conjAction (V * U) ρ)) * star U ∂haarMeasureOnMatrixSpace := by
  -- This theorem is blocked on the same mathlib_missing lemma as the abstract version
  -- in Twirling.lean:585-609. The proof would be:
  -- 1. Unfold twirl_su2_haar and haarMeasureOnMatrixSpace
  -- 2. Apply twirl_invariant_under_conj from Twirling.lean
  -- 3. Both sides become integrals over haarMeasureOnMatrixSpace
  -- However, twirl_invariant_under_conj itself has a sorry blocked on
  -- integral_mul_left_mul_right_eq_self (conjugation invariance for bi-invariant measures).
  --
  -- gap_kind: mathlib_missing
  -- Required: integral_mul_left_mul_right_eq_self combining left and right invariance
  -- to show ∫ f(g*x*h) dμ = ∫ f(x) dμ for bi-invariant measures.
  -- See task_results/act_iter92_twirling_l609_conj_inv.md for detailed proof strategy.
  sorry

end PPT2.Mathlib.TwirlingHaar
