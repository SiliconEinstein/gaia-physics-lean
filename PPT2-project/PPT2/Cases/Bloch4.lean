/-
PPT2.Cases.Bloch4 — 16-element Pauli/Bloch basis on M_2(ℂ) ⊗ M_2(ℂ)
                    (i.e. on `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ`).

This is the 4×4 analogue of `PPT2.Cases.Bloch` (which handles d = 2).
It is the next-step infrastructure required for the P3 axiom
(`ppt_implies_eb_dim2`) elimination path: the Choi matrix of a `QChan 2 2`
lives in `M_2(ℂ) ⊗ M_2(ℂ)` and so admits a 16-term Pauli HS expansion in the
orthogonal basis `{σ_k ⊗ σ_l : k, l ∈ Fin 4}`.

Definitions (1:1 mirror of `Bloch.lean`):
* `pauliPair k l := PPT2.kron (PPT2.Bloch.pauliBasis k) (PPT2.Bloch.pauliBasis l)`
* `blochCoord4 M k l := Matrix.trace ((pauliPair k l) * M) / 4`

Lemmas:
* `blochCoord4_add`  — additivity in `M`
* `blochCoord4_smul` — scalar-linearity in `M`
* `bloch4_hs_expansion` — completeness:
    `M = ∑_{k,l} blochCoord4 M k l • pauliPair k l`.

The HS-orthogonality factor `1/4` comes from the standard normalization
`tr(σ_k σ_k') = 2 δ_{k,k'}`, so `tr((σ_k ⊗ σ_l)(σ_k' ⊗ σ_l')) = 4 δ_{k,k'} δ_{l,l'}`.
-/
import PPT2.Basic
import PPT2.MatrixTensor
import PPT2.PartialTranspose
import PPT2.Cases.Pauli
import PPT2.Cases.Bloch
import Mathlib.LinearAlgebra.Matrix.Trace

namespace PPT2.Bloch4

open Matrix BigOperators
open scoped ComplexOrder Kronecker

/-- The 16-element bipartite Pauli basis on `M_2(ℂ) ⊗ M_2(ℂ)`. -/
noncomputable def pauliPair (k l : Fin 4) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  PPT2.kron (PPT2.Bloch.pauliBasis k) (PPT2.Bloch.pauliBasis l)

/-- Bloch coefficient of `M` against `σ_k ⊗ σ_l`.  The normalization is `1/4`
    so that the basis is HS-orthonormal in the resulting expansion. -/
noncomputable def blochCoord4
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (k l : Fin 4) : ℂ :=
  Matrix.trace ((pauliPair k l) * M) / 4

/-- `blochCoord4` is additive in `M`. -/
lemma blochCoord4_add
    (M N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (k l : Fin 4) :
    blochCoord4 (M + N) k l = blochCoord4 M k l + blochCoord4 N k l := by
  simp [blochCoord4, Matrix.mul_add, Matrix.trace_add, add_div]

/-- `blochCoord4` commutes with scalar multiplication in `M`. -/
lemma blochCoord4_smul
    (c : ℂ) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (k l : Fin 4) :
    blochCoord4 (c • M) k l = c * blochCoord4 M k l := by
  simp [blochCoord4, Matrix.trace_smul, mul_div_assoc]

/-! ### Entry-wise reduction of the Pauli-pair trace -/

private lemma pauliPair_apply (k l : Fin 4) (a b c d : Fin 2) :
    pauliPair k l (a, b) (c, d)
      = PPT2.Bloch.pauliBasis k a c * PPT2.Bloch.pauliBasis l b d := by
  simp [pauliPair, PPT2.kron, Matrix.kronecker_apply]

private lemma trace_pauliPair_mul_apply
    (k l : Fin 4) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix.trace ((pauliPair k l) * M)
      = ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
          PPT2.Bloch.pauliBasis k a c
          * PPT2.Bloch.pauliBasis l b d
          * M (c, d) (a, b) := by
  rw [Matrix.trace, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply, ← Finset.univ_product_univ,
      Finset.sum_product]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [pauliPair_apply]

/-! ### Pauli HS-orthogonality / completeness relation.

The key identity `∑_k σ_k(a,c) σ_k(x,z) = 2 · [a=z ∧ c=x]` is the completeness
relation for the d=2 Pauli basis.  Combined with the analogous relation on the
second tensor factor it collapses the 16-term bipartite expansion. -/

/-- Pauli completeness relation on a single tensor factor:
    `∑_k σ_k(a,c) * σ_k(x,z) = 2 * 1_{a = z ∧ c = x}`.
    This is the orthogonality of `{σ_I, σ_X, σ_Y, σ_Z}` against itself in
    the trace / Hilbert-Schmidt inner product, read off entry-wise. -/
private lemma pauli_completeness (a c x z : Fin 2) :
    (∑ k : Fin 4, PPT2.Bloch.pauliBasis k a c * PPT2.Bloch.pauliBasis k x z)
      = if a = z ∧ c = x then (2 : ℂ) else 0 := by
  fin_cases a <;> fin_cases c <;> fin_cases x <;> fin_cases z <;>
    simp [Fin.sum_univ_four, PPT2.Bloch.pauliBasis,
          PPT2.Bloch.σ_I, PPT2.Bloch.σ_X, PPT2.Bloch.σ_Y, PPT2.Bloch.σ_Z,
          PPT2.pauliMatrix, Matrix.one_apply,
          Complex.ext_iff, Complex.I_re, Complex.I_im] <;>
    norm_num

/-- Helper: the 16-term entry sum collapses via Pauli completeness to `4 * M (ra,rb) (ce,cf)`. -/
private lemma pauli_double_sum (ra rb ce cf : Fin 2)
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
      (∑ k : Fin 4, PPT2.Bloch.pauliBasis k a c * PPT2.Bloch.pauliBasis k ra ce) *
      (∑ l : Fin 4, PPT2.Bloch.pauliBasis l b d * PPT2.Bloch.pauliBasis l rb cf) *
      M (c, d) (a, b) = 4 * M (ra, rb) (ce, cf) := by
  simp_rw [pauli_completeness]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Fin.sum_univ_two]
  fin_cases ra <;> fin_cases rb <;> fin_cases ce <;> fin_cases cf <;> norm_num

/-- Helper: re-associate the 4-level sum `∑ k ∑ l ∑ a ∑ b ∑ c ∑ d (...)` so that the
    `k,l` sums bind to the corresponding Pauli factors over `(a,c)` and `(b,d)`. -/
private lemma sum_rearrange (ra rb ce cf : Fin 2)
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ∑ k : Fin 4, ∑ l : Fin 4,
      (∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
        PPT2.Bloch.pauliBasis k a c * PPT2.Bloch.pauliBasis l b d * M (c, d) (a, b)) *
      PPT2.Bloch.pauliBasis k ra ce * PPT2.Bloch.pauliBasis l rb cf =
    ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
      (∑ k : Fin 4, PPT2.Bloch.pauliBasis k a c * PPT2.Bloch.pauliBasis k ra ce) *
      (∑ l : Fin 4, PPT2.Bloch.pauliBasis l b d * PPT2.Bloch.pauliBasis l rb cf) *
      M (c, d) (a, b) := by
  simp only [Fin.sum_univ_four, Fin.sum_univ_two]
  ring

/-- Entry-level reconstruction: for every index `(ra,rb), (ce,cf)` the RHS of the
    expansion reproduces `M (ra,rb) (ce,cf)`.  The division by 4 is moved outside
    the double sum via `← Finset.sum_mul`, then `pauli_double_sum` kills it. -/
private lemma bloch4_entry (ra rb ce cf : Fin 2) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    M (ra, rb) (ce, cf) =
    ∑ k : Fin 4, ∑ l : Fin 4,
      (∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
        PPT2.Bloch.pauliBasis k a c * PPT2.Bloch.pauliBasis l b d * M (c, d) (a, b)) / 4 *
      (PPT2.Bloch.pauliBasis k ra ce * PPT2.Bloch.pauliBasis l rb cf) := by
  simp_rw [show ∀ (S Pk Pl : ℂ), S / 4 * (Pk * Pl) = S * Pk * Pl * (4⁻¹ : ℂ) from
    fun S Pk Pl => by ring]
  simp_rw [← Finset.sum_mul]
  rw [sum_rearrange, pauli_double_sum]
  ring

/-- **Pauli HS-basis completeness on `M_2(ℂ) ⊗ M_2(ℂ)`** (16-term form):
    every `4×4` complex matrix indexed by `Fin 2 × Fin 2` expands in the
    bipartite Pauli basis `{σ_k ⊗ σ_l : k, l ∈ Fin 4}` with coefficients
    `blochCoord4 M k l`. -/
theorem bloch4_hs_expansion
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    M = ∑ k : Fin 4, ∑ l : Fin 4,
          blochCoord4 M k l • pauliPair k l := by
  ext ⟨a, b⟩ ⟨e, f⟩
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
             blochCoord4, pauliPair_apply, trace_pauliPair_mul_apply]
  exact bloch4_entry a b e f M

/-- Partial transpose of a `pauliPair`: unfolds via the d=2 lemma
    `PPT2.Bloch.partialTranspose_kron_pauli`, since
    `pauliPair k l = kron (pauliBasis k) (pauliBasis l)`. -/
private lemma partialTranspose_pauliPair (k l : Fin 4) :
    PPT2.partialTranspose (pauliPair k l)
      = (if l = 2 then (-1 : ℂ) else 1) • pauliPair k l := by
  unfold pauliPair
  exact PPT2.Bloch.partialTranspose_kron_pauli k l

/-- **Partial transpose of the 16-term Pauli HS expansion.**
    Combining `bloch4_hs_expansion` with the entrywise action of the partial
    transpose on each `σ_k ⊗ σ_l` (which contributes a `-1` factor exactly when
    `l = 2`, since `σ_Y` is the only antisymmetric Pauli), the partial transpose
    of any bipartite matrix is again a 16-term Pauli expansion with the same
    Bloch coefficients but each `(k, l=2)` coefficient negated. -/
theorem partialTranspose_bloch4_hs_expansion
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    PPT2.partialTranspose M
      = ∑ k : Fin 4, ∑ l : Fin 4,
          ((if l = 2 then (-1 : ℂ) else 1) * blochCoord4 M k l)
            • pauliPair k l := by
  conv_lhs => rw [bloch4_hs_expansion M]
  rw [PPT2.partialTranspose_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [PPT2.partialTranspose_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [PPT2.partialTranspose_smul, partialTranspose_pauliPair, smul_smul,
      mul_comm (blochCoord4 M k l)]

theorem ppt_bloch4_psd_constraint
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hM : M.PosSemidef)
    (hPPT : (PPT2.partialTranspose M).PosSemidef) :
    (∑ k : Fin 4, ∑ l : Fin 4,
      ((if l = 2 then (-1 : ℂ) else 1) * blochCoord4 M k l)
        • pauliPair k l).PosSemidef := by
  rw [← partialTranspose_bloch4_hs_expansion]
  exact hPPT

/-- Helper: for every `k : Fin 4`, the HS-inner-product of `pauliPair k 2 = σ_k ⊗ σ_Y`
    against the partial transpose of `M` equals the negative of the HS-inner-product
    against `M`.  The proof swaps the `b ↔ d` summation variables in the entry
    expansion of the trace and uses `σ_Y(d,b) = -σ_Y(b,d)` (antisymmetry of σ_Y). -/
private lemma trace_pauliPair_two_partialTranspose
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (k : Fin 4) :
    Matrix.trace ((pauliPair k 2) * PPT2.partialTranspose M)
      = - Matrix.trace ((pauliPair k 2) * M) := by
  rw [trace_pauliPair_mul_apply, trace_pauliPair_mul_apply]
  -- Unfold the PT action: (PT M) (c,d) (a,b) = M (c,b) (a,d).
  simp only [show ∀ a b c d : Fin 2,
              (PPT2.partialTranspose M) (c, d) (a, b) = M (c, b) (a, d)
             from fun _ _ _ _ => rfl]
  -- Expand every Fin 2 sum into a 2-term sum, fin_cases k, and compute the
  -- concrete entries of σ_Y (which is non-zero only on the off-diagonal).
  simp only [Fin.sum_univ_two]
  fin_cases k <;>
    simp [PPT2.Bloch.pauliBasis, PPT2.Bloch.σ_I, PPT2.Bloch.σ_X,
          PPT2.Bloch.σ_Y, PPT2.Bloch.σ_Z, PPT2.pauliMatrix,
          Matrix.one_apply] <;>
    ring

theorem bloch4_coord_ppt_negation (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hM : M.PosSemidef) (hPPT : (PPT2.partialTranspose M).PosSemidef)
    (k : Fin 4) :
    blochCoord4 (PPT2.partialTranspose M) k 2 = -blochCoord4 M k 2 := by
  unfold blochCoord4
  rw [trace_pauliPair_two_partialTranspose M k, neg_div]

end PPT2.Bloch4
