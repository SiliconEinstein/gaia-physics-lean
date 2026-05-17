/-
PPT2.PartialTranspose — partial transpose on the second tensor factor and the
PPT predicate for quantum channels via Choi.

本步把 partial_transpose 与 IsPPT 都留作 axiom 占位，待 P0 后期下沉。
-/
import PPT2.Basic
import PPT2.MatrixTensor
import PPT2.Choi
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

namespace PPT2

open Matrix
open scoped ComplexOrder

/-- Partial transpose on the second tensor factor: swap the B-side
    (column) indices of each matrix entry.  For a matrix element indexed by
    ((a,b),(c,d)) — where (a,b) is the row index and (c,d) is the column index
    in the bipartite space — the partial transpose sends it to ((a,d),(c,b)). -/
def partialTranspose {d : Nat}
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  λ ⟨a, b⟩ ⟨c, d⟩ => X ⟨a, d⟩ ⟨c, b⟩

/-- Partial transpose distributes over addition (entrywise reindexing). -/
theorem partialTranspose_add {d : Nat}
    (X Y : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    partialTranspose (X + Y) =
      partialTranspose X + partialTranspose Y := by
  funext ⟨a, b⟩ ⟨c, d⟩
  simp [partialTranspose]

/-- Partial transpose commutes with scalar multiplication. -/
theorem partialTranspose_smul {d : Nat} (c : ℂ)
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    partialTranspose (c • X) = c • partialTranspose X := by
  funext ⟨a, b⟩ ⟨e, f⟩
  simp [partialTranspose]

/-- Partial transpose of zero is zero. -/
theorem partialTranspose_zero {d : Nat} :
    partialTranspose
      (0 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) = 0 := by
  funext ⟨a, b⟩ ⟨c, d⟩
  simp [partialTranspose]

/-- Partial transpose distributes over a finite sum. -/
theorem partialTranspose_sum {d : Nat} {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    partialTranspose (∑ i ∈ s, f i) =
      ∑ i ∈ s, partialTranspose (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using partialTranspose_zero
  | @insert a t hni ih =>
    rw [Finset.sum_insert hni, partialTranspose_add,
        ih, Finset.sum_insert hni]

/-- Partial transpose is an involution: applying it twice yields the
    original matrix. Follows directly from the index swap definition. -/
theorem partialTranspose_involution {d : Nat}
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    partialTranspose (partialTranspose X) = X := by
  funext ⟨a, b⟩ ⟨c, e⟩
  simp [partialTranspose]

/-- Partial transpose commutes with negation (entrywise). -/
theorem partialTranspose_neg {d : Nat}
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    partialTranspose (-X) = - partialTranspose X := by
  funext ⟨a, b⟩ ⟨c, e⟩
  simp [partialTranspose]

/-- Partial transpose distributes over subtraction (entrywise). -/
theorem partialTranspose_sub {d : Nat}
    (X Y : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    partialTranspose (X - Y) =
      partialTranspose X - partialTranspose Y := by
  simp only [sub_eq_add_neg, partialTranspose_add, partialTranspose_neg]

/-- Partial transpose of the identity matrix is the identity. -/
theorem partialTranspose_one {d : Nat} :
    partialTranspose (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
      = 1 := by
  funext ⟨a, b⟩ ⟨c, e⟩
  by_cases h1 : a = c
  · subst h1
    by_cases h2 : b = e
    · subst h2; simp [partialTranspose, Matrix.one_apply]
    · simp [partialTranspose, Matrix.one_apply, h2, Ne.symm h2]
  · simp [partialTranspose, Matrix.one_apply, h1]

/-- A quantum channel is **PPT** iff the partial transpose of its Choi matrix
    is positive semidefinite. -/
def IsPPT {d : Nat} (Φ : QChan d d) : Prop :=
  (partialTranspose (Choi Φ)).PosSemidef

end PPT2
