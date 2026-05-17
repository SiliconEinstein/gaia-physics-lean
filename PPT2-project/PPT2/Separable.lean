/-
PPT2.Separable — separable cone on bipartite finite-dimensional Hilbert spaces.
Standard convex-combination definition (Werner 1989; HHHH RMP 2009 §IV).
-/
import PPT2.Basic
import PPT2.MatrixTensor
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order

namespace PPT2

open Matrix BigOperators
open scoped ComplexOrder Kronecker

/-- A bipartite operator `X : (d × d) ⊗ (d × d) → (d × d) ⊗ (d × d)` (here
    represented as a square matrix on `Fin d × Fin d`) is **separable** iff it
    is a finite convex sum of tensor products of PSD matrices. -/
def Separable {d : Nat}
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  ∃ (k : ℕ) (p : Fin k → ℝ) (A B : Fin k → Matrix (Fin d) (Fin d) ℂ),
    (∀ i, 0 ≤ p i) ∧ (∀ i, (A i).PosSemidef) ∧ (∀ i, (B i).PosSemidef) ∧
    X = ∑ i, (p i : ℂ) • Matrix.kronecker (A i) (B i)

/-- The separable cone is closed under nonneg-real convex combinations. -/
theorem Separable.convex_combo {d : Nat}
    {X Y : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hX : Separable X) (hY : Separable Y)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Separable ((a : ℂ) • X + (b : ℂ) • Y) := by
  obtain ⟨k₁, p₁, A₁, B₁, hp₁, hA₁, hB₁, heq₁⟩ := hX
  obtain ⟨k₂, p₂, A₂, B₂, hp₂, hA₂, hB₂, heq₂⟩ := hY
  refine ⟨k₁ + k₂,
    fun i => Fin.addCases (fun j => a * p₁ j) (fun j => b * p₂ j) i,
    fun i => Fin.addCases (fun j => A₁ j) (fun j => A₂ j) i,
    fun i => Fin.addCases (fun j => B₁ j) (fun j => B₂ j) i,
    ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Fin.addCases_left]; exact mul_nonneg ha (hp₁ j)
    · simp [Fin.addCases_right]; exact mul_nonneg hb (hp₂ j)
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Fin.addCases_left]; exact hA₁ j
    · simp [Fin.addCases_right]; exact hA₂ j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Fin.addCases_left]; exact hB₁ j
    · simp [Fin.addCases_right]; exact hB₂ j
  · rw [heq₁, heq₂, Finset.smul_sum, Finset.smul_sum, Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [Fin.addCases_left, smul_smul, ← Complex.ofReal_mul]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [Fin.addCases_right, smul_smul, ← Complex.ofReal_mul]

/-- The separable cone is closed under addition.  Direct corollary of
    `Separable.convex_combo` with `a = b = 1`. -/
theorem Separable.add {d : Nat}
    {X Y : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hX : Separable X) (hY : Separable Y) :
    Separable (X + Y) := by
  have h := Separable.convex_combo hX hY (zero_le_one) (zero_le_one)
  simpa using h

/-- The separable cone is closed under multiplication by nonneg reals. -/
theorem Separable.smul {d : Nat}
    {X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hX : Separable X) {c : ℝ} (hc : 0 ≤ c) :
    Separable ((c : ℂ) • X) := by
  obtain ⟨k, p, A, B, hp, hA, hB, heq⟩ := hX
  refine ⟨k, fun i => c * p i, A, B,
    fun i => mul_nonneg hc (hp i), hA, hB, ?_⟩
  rw [heq, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_smul, ← Complex.ofReal_mul]

/-- The separable cone contains the zero element. -/
theorem Separable.zero {d : Nat} :
    Separable (0 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0,
    fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
  simp

/-- The separable cone is closed under finite sums (Finset version). -/
theorem Separable.sum {d : Nat} {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hf : ∀ i ∈ s, Separable (f i)) :
    Separable (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Separable.zero (d := d))
  | @insert a t hni ih =>
    rw [Finset.sum_insert hni]
    refine Separable.add (hf a (Finset.mem_insert_self a t)) ?_
    exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Separable matrices are PSD. The proof is the cone-positivity
    half of `separable_implies_ppt`: each summand `p i • (A i ⊗ₖ B i)`
    is PSD by `Matrix.PosSemidef.kronecker` + `Matrix.PosSemidef.smul`
    with `0 ≤ ((p i : ℝ) : ℂ)`, and the convex sum is PSD by
    `posSemidef_sum`. -/
theorem separable_implies_psd {d : Nat}
    {X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hX : Separable X) : X.PosSemidef := by
  obtain ⟨k, p, A, B, hp, hA, hB, hXeq⟩ := hX
  rw [hXeq]
  apply posSemidef_sum
  intro i _
  have hKron : ((A i) ⊗ₖ (B i)).PosSemidef := (hA i).kronecker (hB i)
  have hnonneg : (0 : ℂ) ≤ (p i : ℂ) := Complex.zero_le_real.mpr (hp i)
  exact hKron.smul hnonneg

end PPT2
