/-
GaiaPhysicsLean.A2ChoiTheorem.Defs

Core definitions for Choi's theorem (CP ⇔ Choi-matrix PSD):
  * `QChan dK dH`        — finite-dim quantum channel as bare ℂ-linear map.
  * `Choi Φ`             — Choi matrix `C_Φ = ∑_{i,j} |i⟩⟨j| ⊗ Φ(|i⟩⟨j|)`.
  * `Choi_apply`         — pointwise unfolding of `Choi`.
  * `IsCP Φ`             — CP via PSD-preservation under arbitrary ampliation.
  * `mul_single_mul_apply` — `(M * single i j 1 * N) r c = M r i * N j c`.

Used by sibling files `Forward.lean` and `Reverse.lean` in this directory.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.Complex.Order

namespace GaiaPhysicsLean.A2ChoiTheorem

open Matrix Kronecker
open scoped ComplexOrder

/-- A (bare) finite-dim quantum channel as a ℂ-linear map between matrix
    algebras. CPTP / TP bundling is intentionally deferred so that downstream
    `Choi`/CP work can manipulate the bare linear map.
    `@[reducible]` so `FunLike` application resolves through `LinearMap`. -/
@[reducible]
noncomputable def QChan (dK dH : ℕ) : Type :=
  Matrix (Fin dK) (Fin dK) ℂ →ₗ[ℂ] Matrix (Fin dH) (Fin dH) ℂ

/-- Choi matrix `C_Φ = ∑_{i,j} |i⟩⟨j| ⊗ Φ(|i⟩⟨j|)` (Kronecker product form). -/
noncomputable def Choi {dK dH : ℕ} (Φ : QChan dK dH) :
    Matrix (Fin dK × Fin dH) (Fin dK × Fin dH) ℂ :=
  ∑ i : Fin dK, ∑ j : Fin dK,
    Matrix.kroneckerMap (· * ·)
      (Matrix.single i j (1 : ℂ))
      (Φ (Matrix.single i j (1 : ℂ)))

/-- Pointwise unfolding of the Choi matrix:
    `(Choi Φ) (i,a) (j,b) = (Φ (single i j 1)) a b`. -/
lemma Choi_apply {dK dH : ℕ} (Φ : QChan dK dH)
    (i j : Fin dK) (a b : Fin dH) :
    Choi Φ (i, a) (j, b) = Φ (Matrix.single i j (1 : ℂ)) a b := by
  classical
  unfold Choi
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
  -- Outer sum over `i'`: only `i' = i` survives (row index of `single`).
  rw [Finset.sum_eq_single i]
  · -- Inner sum over `j'`: only `j' = j` survives (col index of `single`).
    rw [Finset.sum_eq_single j]
    · simp [Matrix.single_apply]
    · intro j' _ hj'
      simp [Matrix.single_apply, hj']
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro i' _ hi'
    apply Finset.sum_eq_zero
    intro j' _
    have hand : ¬ (i' = i ∧ j' = j) := by
      intro h; exact hi' h.1
    simp [Matrix.single_apply, hand]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Complete positivity of `Φ : QChan dK dH`: the ampliation `id_n ⊗ Φ`
    sends PSD inputs of size `n·dK` to PSD outputs of size `n·dH`, for every
    ancilla dimension `n`. -/
def IsCP {dK dH : ℕ} (Φ : QChan dK dH) : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n × Fin dK) (Fin n × Fin dK) ℂ),
    M.PosSemidef →
    (Matrix.of fun (p : Fin n × Fin dH) (q : Fin n × Fin dH) =>
      Φ (Matrix.of fun (i : Fin dK) (j : Fin dK) =>
        M (p.1, i) (q.1, j)) p.2 q.2).PosSemidef

/-- Sandwich a `Matrix.single i j 1` between `M` and `N`:
    `(M * single i j 1 * N) r c = M r i * N j c`.
    Finite-dim version of `|i⟩⟨j|` acting on the left and right. -/
private lemma mul_single_mul_apply
    {d₁ d₂ d : ℕ}
    (M : Matrix (Fin d₁) (Fin d) ℂ) (N : Matrix (Fin d) (Fin d₂) ℂ)
    (i j : Fin d) (r : Fin d₁) (c : Fin d₂) :
    (M * Matrix.single i j (1 : ℂ) * N) r c = M r i * N j c := by
  classical
  have hMS : ∀ y : Fin d,
      (M * Matrix.single i j (1 : ℂ)) r y = if y = j then M r i else 0 := by
    intro y
    by_cases hy : y = j
    · rw [if_pos hy, Matrix.mul_apply]
      rw [Finset.sum_eq_single i]
      · simp [Matrix.single_apply, hy]
      · intro x _ hx
        have hand : ¬ (i = x ∧ j = y) := fun h => hx h.1.symm
        simp [Matrix.single_apply, hand]
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [if_neg hy, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro x _
      have hand : ¬ (i = x ∧ j = y) := fun h => hy h.2.symm
      simp [Matrix.single_apply, hand]
  rw [Matrix.mul_apply]
  simp only [hMS, ite_mul, zero_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro y _ hy; simp [hy]
  · intro h; exact absurd (Finset.mem_univ j) h

end GaiaPhysicsLean.A2ChoiTheorem
