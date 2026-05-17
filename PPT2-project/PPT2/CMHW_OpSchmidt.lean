/-
OpSchmidt.lean — Operator-Schmidt rank ≤ 2 machinery for PPT² conjecture.

Formalizes the key structural result from:
  Christandl, Müller-Hermes, Wolf (2019), arXiv:1807.01266
  "When Do Composed Maps Become Entanglement Breaking?"

Main results:
  1. `OperatorSchmidtRank` — definition via Choi matrix Schmidt decomposition
  2. `opSchmidtRank_le2_cp_ppt_isEB` — CP + PPT + opSchmidtRank ≤ 2 → EB
  3. `ppt2_via_opSchmidt` — Φ∘Ψ is EB when both are CP+PPT with rank ≤ 2

Sorry-map:
  S1. Operator-Schmidt decomposition existence (Mathlib: TensorProduct SVD)
  S2. Rank-1 Choi ↔ product channel (Mathlib: missing quantum info)
  S3. PPT + rank-1 Choi → PSD partial transpose (entrywise argument)
  S4. Convex combination of EB channels is EB (Separable.convex_combo exists)
  S5. CP + PPT + opSchmidtRank ≤ 2 → Choi separable (main CMHW argument)
  S6. Composition of EB with CP is EB (EB_comp_left/right exist in PPT2)
-/

-- NEEDS: Mathlib.LinearAlgebra.Matrix.PosDef
-- NEEDS: Mathlib.LinearAlgebra.Matrix.Kronecker
-- NEEDS: Mathlib.LinearAlgebra.TensorProduct.Basic
-- NEEDS: Mathlib.Analysis.Matrix.Order
-- NEEDS: PPT2.CP
-- NEEDS: PPT2.EntanglementBreaking
-- NEEDS: PPT2.PartialTranspose
-- NEEDS: PPT2.Separable

import PPT2.CP
import PPT2.EntanglementBreaking
import PPT2.PartialTranspose
import PPT2.Separable
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Order

namespace PPT2.CMHW

open Matrix BigOperators
open scoped ComplexOrder

/-!
## Operator-Schmidt Rank

The operator-Schmidt rank of Φ : QChan d d is the minimum number of terms
in a decomposition  Choi(Φ) = Σ_k A_k ⊗ B_k  (not necessarily PSD terms).
This is the Schmidt rank of the Choi matrix viewed as a vector in
(M_d ⊗ M_d) ⊗ (M_d ⊗ M_d) ≅ M_{d²} ⊗ M_{d²}.

For the CMHW result we only need the predicate "rank ≤ 2".
-/

/-- The operator-Schmidt rank of a bipartite matrix X is the minimum number
    of product terms A_k ⊗ B_k (no sign/PSD constraint) needed to write X. -/
noncomputable def OperatorSchmidtRank {d : ℕ}
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℕ :=
  -- NEEDS: Mathlib.LinearAlgebra.TensorProduct.rank (or SVD on vectorized form)
  -- Definition: min { n | ∃ A B : Fin n → M_d(ℂ), X = Σ_k A_k ⊗ B_k }
  -- For now: axiomatized via the existence predicate below.
  sorry

/-- Predicate: X has operator-Schmidt rank ≤ r. -/
def HasOpSchmidtRank {d : ℕ}
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (r : ℕ) : Prop :=
  ∃ (A B : Fin r → Matrix (Fin d) (Fin d) ℂ),
    X = ∑ k, Matrix.kronecker (A k) (B k)

/-- The Choi matrix of Φ has operator-Schmidt rank ≤ r. -/
def hasOpSchmidtRank {d : ℕ} (Φ : QChan d d) (r : ℕ) : Prop :=
  HasOpSchmidtRank (Choi Φ) r

/-!
## Rank-1 channels are EB when CP+PPT

A channel with opSchmidtRank = 1 has Choi(Φ) = A ⊗ B.
CP forces A ⊗ B ≥ 0, PPT forces (A ⊗ B)^{T_B} = A ⊗ Bᵀ ≥ 0.
Together these force A, B ≥ 0, so Choi(Φ) is already separable (rank-1 term).
-/

/-- A rank-1 product matrix A ⊗ B with A, B PSD is separable. -/
lemma kron_psd_separable {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Separable (Matrix.kronecker A B) := by
  -- S4: one-term convex combination with weight 1
  -- NEEDS: Separable definition allows k=1, p 0 = 1
  refine ⟨1, fun _ => 1, fun _ => A, fun _ => B, ?_, ?_, ?_, ?_⟩
  · intro i; norm_num
  · intro i; exact hA
  · intro i; exact hB
  · simp

/-- CP + PPT + opSchmidtRank ≤ 1 → EB.
    Proof: Choi = A ⊗ B; CP → A⊗B PSD; PPT → A⊗Bᵀ PSD.
    Standard argument: A⊗B PSD + A⊗Bᵀ PSD → A PSD ∧ B PSD → Separable. -/
lemma opSchmidtRank_le1_cp_ppt_isEB {d : ℕ} (Φ : QChan d d)
    (hCP  : IsCP Φ)
    (hPPT : IsPPT Φ)
    (hRk  : hasOpSchmidtRank Φ 1) : IsEB Φ := by
  obtain ⟨A, B, hChoi⟩ := hRk
  -- S1: extract the unique A 0, B 0
  -- S2: CP → A 0 ⊗ B 0 PSD; PPT → A 0 ⊗ (B 0)ᵀ PSD
  -- S3: from A⊗B PSD and A⊗Bᵀ PSD deduce A PSD and B PSD
  -- Then kron_psd_separable closes the goal.
  unfold IsEB
  rw [hChoi]
  simp [Fin.sum_univ_one]
  -- S3 gap: need A 0 PSD and B 0 PSD from CP+PPT
  apply kron_psd_separable
  · -- A 0 PSD: follows from CP (Choi PSD) + rank-1 structure
    -- NEEDS: lemma kron_left_psd_of_kron_psd (no Mathlib equivalent yet)
    sorry -- S3a
  · -- B 0 PSD: follows from PPT (partial-transpose Choi PSD) + rank-1
    -- NEEDS: lemma kron_right_psd_of_kron_ppt (no Mathlib equivalent yet)
    sorry -- S3b

/-!
## Main CMHW Theorem: opSchmidtRank ≤ 2 + CP + PPT → EB

Key idea (CMHW §3): write Choi(Φ) = A₁⊗B₁ + A₂⊗B₂.
CP + PPT constrain the 2×2 block Gram matrix of {A_k, B_k} to be PSD.
A spectral argument on this 2×2 system forces each term to be PSD,
reducing to the rank-1 case applied twice.
-/

/-- **CMHW Main Lemma** (arXiv:1807.01266, Theorem 1):
    If Φ : QChan d d is CP, PPT, and has operator-Schmidt rank ≤ 2,
    then Φ is entanglement-breaking. -/
theorem opSchmidtRank_le2_cp_ppt_isEB {d : ℕ} (Φ : QChan d d)
    (hCP  : IsCP Φ)
    (hPPT : IsPPT Φ)
    (hRk  : hasOpSchmidtRank Φ 2) : IsEB Φ := by
  obtain ⟨A, B, hChoi⟩ := hRk
  -- S5: The CMHW argument.
  -- Write Choi(Φ) = A 0 ⊗ B 0 + A 1 ⊗ B 1.
  -- CP: (A 0 ⊗ B 0 + A 1 ⊗ B 1) PSD.
  -- PPT: (A 0 ⊗ B 0ᵀ + A 1 ⊗ B 1ᵀ) PSD.
  -- CMHW Lemma 3.1: these two PSD conditions force the 2×2 Gram matrix
  --   G = [[⟨A0,A0⟩ ⟨A0,A1⟩],[⟨A1,A0⟩ ⟨A1,A1⟩]] (Hilbert-Schmidt inner product)
  -- to satisfy a joint positivity condition that implies each A_k ⊗ B_k ≥ 0.
  -- NEEDS: Matrix.PosSemidef.sum_kron_decomp (not in Mathlib)
  -- NEEDS: HilbertSchmidt inner product on M_d(ℂ) (Mathlib.Analysis.HilbertSpace.Basic)
  unfold IsEB
  rw [hChoi]
  -- Reduce to showing each summand is separable, then use Separable.convex_combo
  -- S5 gap: the full CMHW spectral argument
  sorry -- S5: main CMHW rank-2 → separable argument

/-!
## Corollary: PPT² via operator-Schmidt rank

If both Φ and Ψ are CP+PPT with opSchmidtRank ≤ 2, then Φ∘Ψ is EB,
hence PPT² ⊆ EB for this subclass.
-/

/-- **CMHW Corollary** (arXiv:1807.01266, Corollary 2):
    If Φ, Ψ : QChan d d are both CP, PPT, and have operator-Schmidt rank ≤ 2,
    then their composition Φ∘Ψ is entanglement-breaking. -/
theorem ppt2_via_opSchmidt {d : ℕ} (Φ Ψ : QChan d d)
    (hΦCP  : IsCP Φ) (hΦPPT : IsPPT Φ) (hΦRk : hasOpSchmidtRank Φ 2)
    (hΨCP  : IsCP Ψ) (hΨPPT : IsPPT Ψ) (hΨRk : hasOpSchmidtRank Ψ 2) :
    IsEB (Φ.comp Ψ) := by
  -- Ψ is EB by the main theorem
  have hΨEB : IsEB Ψ := opSchmidtRank_le2_cp_ppt_isEB Ψ hΨCP hΨPPT hΨRk
  -- Φ is CP, hence PSD-preserving
  have hΦPSD : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Φ M).PosSemidef :=
    isCP_preserves_posSemidef Φ hΦCP
  -- S6: EB_comp_left: Φ∘Ψ is EB because Ψ is EB and Φ is PSD-preserving
  exact EB_comp_left Φ Ψ hΨEB hΦPSD

/-!
## Sorry map summary

| ID  | Statement                                          | Mathlib gap                              |
|-----|----------------------------------------------------|------------------------------------------|
| S1  | OperatorSchmidtRank noncomputable def              | TensorProduct.rank / SVD on M_d⊗M_d     |
| S3a | kron_left_psd_of_kron_psd                          | No Mathlib lemma for partial PSD         |
| S3b | kron_right_psd_of_kron_ppt                         | No Mathlib lemma for PPT → factor PSD    |
| S5  | CMHW rank-2 → Choi separable                       | Full spectral/Gram argument (paper §3)   |

S6 is NOT a sorry: EB_comp_left is already proven in PPT2.EntanglementBreaking.
-/

end PPT2.CMHW
