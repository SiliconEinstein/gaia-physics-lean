/-
PPT2.Cases.Pauli — d=2 Pauli / Werner-isotropic toolkit.

Definitions:
* `pauliEigenproj a s` for `a : Fin 3` (0=x, 1=y, 2=z) and `s : Bool`
  (true=+, false=-) is the rank-1 eigenprojector `(I ± σ_a)/2` written
  as a concrete 2×2 ℂ-matrix.
* `bellPhiPlus` is the rank-1 Bell projector `|Φ⁺⟩⟨Φ⁺|` for
  `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` on `Fin 2 × Fin 2`.

Lemmas:
* (a) `pauliEigenproj_psd` — every Pauli eigenprojector is PSD.
* (b) `bellPhiPlus_psd` — `|Φ⁺⟩⟨Φ⁺|` is PSD.
* (c) `dim2_isotropic_kron_identity` — Werner-isotropic algebraic identity
  `2•|Φ⁺⟩⟨Φ⁺| + I = ∑_{a,s} kron (P_a^s) (P_a^s)ᵀ`.

  *Normalisation note vs. spec*: the canonical identity holds with
  `kron(P_a^s, (P_a^s)ᵀ)` — the second factor is transposed (which equals
  the complex conjugate `P̄_a^s` since `P_a^s` is Hermitian).  Without the
  transpose the identity fails on the `(01,10)/(10,01)` entries because of
  the σ_y term sign.  The `1/2` prefactor on the RHS in the original spec
  is also dropped: with the transpose, the six `kron(P,Pᵀ)` terms already
  sum to `2•|Φ⁺⟩⟨Φ⁺| + I` directly.
* (d) `dim2_id_kron_decomp` — `(1/4)•I_4 = (1/4)•∑_{i,j} kron(|i⟩⟨i|,|j⟩⟨j|)`.

PSD proofs use the route “Hermitian + idempotent ⇒ PSD”
(`P = Pᴴ * P` and `posSemidef_conjTranspose_mul_self`).
-/
import PPT2.MatrixTensor
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace PPT2

open Matrix BigOperators
open scoped Kronecker ComplexOrder

/-- The three Pauli matrices, indexed by `Fin 3` (0 = X, 1 = Y, 2 = Z). -/
noncomputable def pauliMatrix : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -Complex.I; Complex.I, 0]
  | 2 => !![1, 0; 0, -1]

/-- Pauli eigenprojector `P_a^s = (I ± σ_a)/2`.  Encoded as an explicit
    concrete 2×2 ℂ-matrix for each of the six (a, s) combinations. -/
noncomputable def pauliEigenproj : Fin 3 → Bool → Matrix (Fin 2) (Fin 2) ℂ
  | 0, true  => !![(1/2 : ℂ),  (1/2 : ℂ);  (1/2 : ℂ),  (1/2 : ℂ)]
  | 0, false => !![(1/2 : ℂ), -(1/2 : ℂ); -(1/2 : ℂ), (1/2 : ℂ)]
  | 1, true  => !![(1/2 : ℂ), -(Complex.I/2); (Complex.I/2), (1/2 : ℂ)]
  | 1, false => !![(1/2 : ℂ),  (Complex.I/2); -(Complex.I/2), (1/2 : ℂ)]
  | 2, true  => !![(1 : ℂ), 0; 0, 0]
  | 2, false => !![(0 : ℂ), 0; 0, 1]

/-- Bell projector `|Φ⁺⟩⟨Φ⁺|` for `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`. -/
noncomputable def bellPhiPlus : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun ij kl => if ij.1 = ij.2 ∧ kl.1 = kl.2 then (1/2 : ℂ) else 0

/-- A Hermitian idempotent matrix is PSD: write `P = Pᴴ * P` then apply
    `posSemidef_conjTranspose_mul_self`. -/
private lemma posSemidef_of_hermitian_idempotent
    {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (hH : Pᴴ = P) (hI : P * P = P) : P.PosSemidef := by
  have heq : P = Pᴴ * P := by
    have := hI.symm
    rw [show P * P = Pᴴ * P from by rw [hH]] at this
    exact this
  rw [heq]
  exact Matrix.posSemidef_conjTranspose_mul_self P

/-- Hermitian property for each Pauli eigenprojector. -/
private lemma pauliEigenproj_herm (a : Fin 3) (s : Bool) :
    (pauliEigenproj a s)ᴴ = pauliEigenproj a s := by
  fin_cases a <;> cases s
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliEigenproj, Matrix.conjTranspose_apply,
            Complex.ext_iff, Complex.I_re, Complex.I_im] <;>
      norm_num

/-- Idempotent property for each Pauli eigenprojector. -/
private lemma pauliEigenproj_idem (a : Fin 3) (s : Bool) :
    pauliEigenproj a s * pauliEigenproj a s = pauliEigenproj a s := by
  fin_cases a <;> cases s
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliEigenproj, Matrix.mul_apply, Fin.sum_univ_two,
            Complex.ext_iff, Complex.I_re, Complex.I_im] <;>
      ring

/-- (a) Every Pauli eigenprojector is PSD. -/
theorem pauliEigenproj_psd (a : Fin 3) (s : Bool) :
    (pauliEigenproj a s).PosSemidef :=
  posSemidef_of_hermitian_idempotent _
    (pauliEigenproj_herm a s) (pauliEigenproj_idem a s)

/-- Hermitian property for `bellPhiPlus`. -/
private lemma bellPhiPlus_herm : bellPhiPlusᴴ = bellPhiPlus := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.conjTranspose_apply, bellPhiPlus]
  by_cases h1 : a = b
  · by_cases h2 : c = d
    · simp [h1, h2]
    · simp [h1, h2]
  · by_cases h2 : c = d
    · simp [h1, h2]
    · simp [h1, h2]

/-- Idempotent property for `bellPhiPlus`. -/
private lemma bellPhiPlus_idem : bellPhiPlus * bellPhiPlus = bellPhiPlus := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.mul_apply, bellPhiPlus, ← Finset.univ_product_univ,
    Finset.sum_product]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Fin.sum_univ_two]

/-- (b) The Bell projector is PSD. -/
theorem bellPhiPlus_psd : bellPhiPlus.PosSemidef :=
  posSemidef_of_hermitian_idempotent _ bellPhiPlus_herm bellPhiPlus_idem

/-- (c) d=2 Werner-isotropic algebraic identity (transposed second factor). -/
theorem dim2_isotropic_kron_identity :
    (2 : ℂ) • bellPhiPlus
      + (1 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    = ∑ a : Fin 3, ∑ s : Bool,
        kron (pauliEigenproj a s) (pauliEigenproj a s)ᵀ := by
  ext ⟨b, d⟩ ⟨b', d'⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    bellPhiPlus, Matrix.one_apply, Prod.mk.injEq,
    Matrix.sum_apply, Fintype.sum_bool, Fin.sum_univ_three,
    pauliEigenproj, Matrix.transpose_apply,
    kron, Matrix.kronecker_apply]
  fin_cases b <;> fin_cases d <;> fin_cases b' <;> fin_cases d' <;>
    simp [Complex.ext_iff, Complex.I_re, Complex.I_im] <;> ring

/-- (d) Identity decomposition: `(1/4)•I_4 = (1/4)•∑_{i,j} |i⟩⟨i| ⊗ |j⟩⟨j|`. -/
theorem dim2_id_kron_decomp :
    (1/4 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    = (1/4 : ℂ) • ∑ i : Fin 2, ∑ j : Fin 2,
        kron (Matrix.single i i (1 : ℂ)) (Matrix.single j j (1 : ℂ)) := by
  congr 1
  ext ⟨a, b⟩ ⟨c, e⟩
  simp only [Matrix.one_apply, Prod.mk.injEq,
    Matrix.sum_apply, kron, Matrix.kronecker_apply,
    Matrix.single_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [Fin.sum_univ_two]

end PPT2
