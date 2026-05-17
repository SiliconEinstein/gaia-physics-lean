/-
PPT2.Cases.Bloch — Pauli/Bloch basis on M_2(ℂ) for Peres-Horodecki d=2.
Step (a) of the P3 (ppt_implies_eb_dim2) replacement roadmap.
-/
import PPT2.Basic
import PPT2.MatrixTensor
import PPT2.PartialTranspose
import PPT2.Cases.Pauli
import Mathlib.LinearAlgebra.Matrix.Trace

namespace PPT2.Bloch

open Matrix
open scoped ComplexOrder Kronecker

-- σ_I/X/Y/Z: alias from pauliMatrix where available, else define directly.
noncomputable def σ_I : Matrix (Fin 2) (Fin 2) ℂ := 1
noncomputable def σ_X : Matrix (Fin 2) (Fin 2) ℂ := PPT2.pauliMatrix 0
noncomputable def σ_Y : Matrix (Fin 2) (Fin 2) ℂ := PPT2.pauliMatrix 1
noncomputable def σ_Z : Matrix (Fin 2) (Fin 2) ℂ := PPT2.pauliMatrix 2

noncomputable def pauliBasis : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => σ_I
  | 1 => σ_X
  | 2 => σ_Y
  | 3 => σ_Z

noncomputable def blochCoord (M : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 4) : ℂ :=
  Matrix.trace (pauliBasis k * M) / 2

lemma blochCoord_add (M N : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 4) :
    blochCoord (M + N) k = blochCoord M k + blochCoord N k := by
  simp [blochCoord, Matrix.mul_add, Matrix.trace_add, add_div]

lemma blochCoord_smul (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 4) :
    blochCoord (c • M) k = c * blochCoord M k := by
  simp [blochCoord, Matrix.mul_smul, Matrix.trace_smul, mul_div_assoc]

/-- σ_Yᵀ = -σ_Y entrywise, so partialTranspose (kron σ_Y σ_Y) = -kron σ_Y σ_Y. -/
lemma partialTranspose_kron_pauli_y :
    PPT2.partialTranspose (PPT2.kron σ_Y σ_Y) = -(PPT2.kron σ_Y σ_Y) := by
  funext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [PPT2.partialTranspose, PPT2.kron, Matrix.kronecker_apply,
          σ_Y, PPT2.pauliMatrix, Matrix.neg_apply,
          Complex.ext_iff, Complex.I_re, Complex.I_im] <;>
    norm_num

/-! ### Pauli HS-basis completeness (P3 step b) -/

/-- `blochCoord` formula at index 0 (identity component). -/
lemma blochCoord_zero_eq (M : Matrix (Fin 2) (Fin 2) ℂ) :
    blochCoord M 0 = (M 0 0 + M 1 1) / 2 := by
  simp [blochCoord, pauliBasis, σ_I, Matrix.trace_fin_two,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- `blochCoord` formula at index 1 (X component). -/
lemma blochCoord_one_eq (M : Matrix (Fin 2) (Fin 2) ℂ) :
    blochCoord M 1 = (M 0 1 + M 1 0) / 2 := by
  unfold blochCoord pauliBasis σ_X
  rw [show Matrix.trace (PPT2.pauliMatrix 0 * M)
        = (PPT2.pauliMatrix 0 * M) 0 0 + (PPT2.pauliMatrix 0 * M) 1 1
      from Matrix.trace_fin_two _]
  simp [PPT2.pauliMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- `blochCoord` formula at index 2 (Y component). -/
lemma blochCoord_two_eq (M : Matrix (Fin 2) (Fin 2) ℂ) :
    blochCoord M 2 = Complex.I * (M 0 1 - M 1 0) / 2 := by
  unfold blochCoord pauliBasis σ_Y
  rw [show Matrix.trace (PPT2.pauliMatrix 1 * M)
        = (PPT2.pauliMatrix 1 * M) 0 0 + (PPT2.pauliMatrix 1 * M) 1 1
      from Matrix.trace_fin_two _]
  simp [PPT2.pauliMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- `blochCoord` formula at index 3 (Z component). -/
lemma blochCoord_three_eq (M : Matrix (Fin 2) (Fin 2) ℂ) :
    blochCoord M 3 = (M 0 0 - M 1 1) / 2 := by
  unfold blochCoord pauliBasis σ_Z
  rw [show Matrix.trace (PPT2.pauliMatrix 2 * M)
        = (PPT2.pauliMatrix 2 * M) 0 0 + (PPT2.pauliMatrix 2 * M) 1 1
      from Matrix.trace_fin_two _]
  simp [PPT2.pauliMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Pauli HS-basis completeness on M_2(ℂ):
    every 2×2 complex matrix expands in the orthogonal Pauli basis
    `{σ_I, σ_X, σ_Y, σ_Z}` with coefficients `blochCoord M k`. -/
theorem bloch_hs_expansion (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = ∑ k : Fin 4, blochCoord M k • pauliBasis k := by
  ext i j
  rw [Fin.sum_univ_four]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
             blochCoord_zero_eq, blochCoord_one_eq,
             blochCoord_two_eq, blochCoord_three_eq]
  fin_cases i <;> fin_cases j <;>
    simp [pauliBasis, σ_I, σ_X, σ_Y, σ_Z, PPT2.pauliMatrix, Matrix.one_apply]
  all_goals (try ring)
  all_goals (rw [show (Complex.I : ℂ) ^ 2 = -1 from Complex.I_sq])
  all_goals ring

/-! ### Partial transpose on Pauli tensor products -/

/-- σ_I, σ_X, σ_Z are real symmetric matrices, so transpose = identity. -/
private lemma pauli_transpose_real (k : Fin 4) (hk : k ≠ 2) :
    (pauliBasis k)ᵀ = pauliBasis k := by
  fin_cases k <;> try contradiction
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliBasis, σ_I, σ_X, σ_Z, PPT2.pauliMatrix,
            Matrix.transpose_apply, Matrix.one_apply]

/-- σ_Y is antisymmetric: σ_Yᵀ = -σ_Y. -/
private lemma pauli_y_transpose :
    (pauliBasis 2)ᵀ = -(pauliBasis 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliBasis, σ_Y, PPT2.pauliMatrix,
          Matrix.transpose_apply, Matrix.neg_apply,
          Complex.ext_iff, Complex.I_re, Complex.I_im]

/-- Main theorem: partial transpose of Pauli tensor products.
    Since partialTranspose acts on the second factor, only the second
    Pauli matrix gets transposed. σ_Y is the only antisymmetric Pauli,
    so we get a sign flip iff l = 2. -/
theorem partialTranspose_kron_pauli (k l : Fin 4) :
    PPT2.partialTranspose (PPT2.kron (pauliBasis k) (pauliBasis l))
      = (if l = 2 then (-1 : ℂ) else 1) •
          PPT2.kron (pauliBasis k) (pauliBasis l) := by
  by_cases hl : l = 2
  · -- Case l = 2: σ_Y gets transposed to -σ_Y
    subst hl
    funext ⟨a, b⟩ ⟨c, d⟩
    simp only [PPT2.partialTranspose, PPT2.kron, ite_true,
               Matrix.smul_apply, smul_eq_mul]
    -- Expand kronecker: kron A B ⟨i,j⟩ ⟨k,l⟩ = A i k * B j l
    -- partialTranspose swaps the second indices: ⟨a,b⟩ ⟨c,d⟩ → ⟨a,d⟩ ⟨c,b⟩
    -- So LHS = (pauliBasis k) a c * (pauliBasis 2) d b
    -- RHS = -1 * (pauliBasis k) a c * (pauliBasis 2) b d
    -- Need to show: (pauliBasis 2) d b = -(pauliBasis 2) b d
    have h1 : (pauliBasis k).kronecker (pauliBasis 2) (a, d) (c, b)
              = (pauliBasis k) a c * (pauliBasis 2) d b := rfl
    have h2 : (pauliBasis k).kronecker (pauliBasis 2) (a, b) (c, d)
              = (pauliBasis k) a c * (pauliBasis 2) b d := rfl
    rw [h1, h2]
    rw [show (pauliBasis 2) d b = ((pauliBasis 2)ᵀ) b d
        from (Matrix.transpose_apply _ _ _).symm]
    rw [pauli_y_transpose]
    simp [Matrix.neg_apply]
  · -- Case l ≠ 2: σ_I/σ_X/σ_Z are symmetric
    funext ⟨a, b⟩ ⟨c, d⟩
    simp only [PPT2.partialTranspose, PPT2.kron, ite_false, hl,
               Matrix.smul_apply, smul_eq_mul, one_mul]
    have h1 : (pauliBasis k).kronecker (pauliBasis l) (a, d) (c, b)
              = (pauliBasis k) a c * (pauliBasis l) d b := rfl
    have h2 : (pauliBasis k).kronecker (pauliBasis l) (a, b) (c, d)
              = (pauliBasis k) a c * (pauliBasis l) b d := rfl
    rw [h1, h2]
    rw [show (pauliBasis l) d b = ((pauliBasis l)ᵀ) b d
        from (Matrix.transpose_apply _ _ _).symm]
    rw [pauli_transpose_real l hl]

end PPT2.Bloch
