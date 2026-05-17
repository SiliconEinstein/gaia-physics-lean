/-
PPT2.CP — completely-positive (CP) predicate via Choi-Jamiolkowski.

A quantum channel `Φ : QChan d₁ d₂` is CP iff its Choi matrix is positive
semidefinite.  This is the minimal CP foundational layer: it fixes the
definition, exposes the Choi unfolding, and records that every
entanglement-breaking channel is CP (a direct corollary of
`separable_implies_psd`).

Composition-closure of CP (`IsCP.comp`) is deferred to a later iteration.
-/
import PPT2.Choi
import PPT2.EntanglementBreaking
import PPT2.Separable
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order

namespace PPT2

open Matrix
open scoped ComplexOrder

/-- A quantum channel `Φ : QChan d d` is **completely positive** (CP) iff
    its Choi matrix is positive semidefinite.  This encodes the standard
    Choi-Jamiolkowski characterisation of CP maps. -/
def IsCP {d : Nat} (Φ : QChan d d) : Prop := (Choi Φ).PosSemidef

/-- Unfolding: CP channels have PSD Choi. -/
theorem IsCP.choi_psd {d : Nat} {Φ : QChan d d} (hCP : IsCP Φ) :
    (Choi Φ).PosSemidef := hCP

/-- Every entanglement-breaking channel is completely positive, because every
    separable matrix is positive semidefinite. -/
theorem IsEB.isCP {d : Nat} {Φ : QChan d d} (hEB : IsEB Φ) : IsCP Φ := by
  unfold IsCP IsEB at *
  exact separable_implies_psd hEB

/-- **Choi-Jamiolkowski operational bridge**: a CP channel (Choi-PSD) preserves
    positive semidefiniteness operationally.

    This is the forward direction of the standard Choi-Jamiolkowski theorem:
      `(Choi Φ).PosSemidef ↔ ∀ ρ, ρ.PosSemidef → (Φ ρ).PosSemidef`

    The proof strategy contracts the Choi matrix against a test vector, projects
    back into the input space, and uses `posSemidef_iff_dotProduct_mulVec`.

    gap_kind: mathlib_missing — the full Choi-Jamiolkowski characterization
    (including the reverse direction and the explicit vector-space isomorphism)
    belongs in Mathlib's quantum information theory library. -/
lemma isCP_preserves_posSemidef {d : Nat} (Φ : QChan d d) (hΦ : IsCP Φ) :
    ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → (Φ ρ).PosSemidef := by
  -- gap_kind: mathlib_missing
  -- The standard proof expresses ⟨x, Φ(ρ) x⟩ as a quadratic form in the Choi
  -- matrix by vectorizing: vec(Φ(ρ)) = (I ⊗ Φ) vec(ρ), then
  --   ⟨x, Φ(ρ) x⟩ = ⟨x ⊗ vec(ρ), Choi(Φ) (x ⊗ vec(ρ))⟩
  -- Since Choi(Φ) is PSD (by hΦ) and ρ is PSD, the result is nonnegative.
  --
  -- This requires:
  -- 1. Vectorization lemmas (vec : Matrix d d ℂ → (Fin d × Fin d → ℂ))
  -- 2. Choi matrix as (I ⊗ Φ) applied to the maximally entangled state
  -- 3. Tensor product structure on the vector space
  --
  -- All of these are standard quantum information theory infrastructure that
  -- should live in Mathlib. For now, we axiomatize this bridge.
  sorry

end PPT2
