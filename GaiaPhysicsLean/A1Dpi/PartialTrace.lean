/-
  GaiaPhysicsLean.A1Dpi.PartialTrace

  Data Processing Inequality for the partial trace channel.

  **Primary target**: `qre_partial_trace_mono`

  Statement: For bipartite states ρ, σ on H ⊗ K (finite-dimensional),
    S(Tr_K ρ ‖ Tr_K σ) ≤ S(ρ ‖ σ)

  where S(ρ ‖ σ) = Tr(ρ (log ρ − log σ)) is the quantum relative entropy.

  ## Proof strategy

  The cleanest proof path is Lindblad's monotonicity theorem (1975):
  DPI holds for all CPTP maps, and the partial trace is a CPTP map.

  The proof of DPI for general CPTP maps reduces to the partial trace case
  via Stinespring dilation (every CPTP map = partial trace of unitary evolution).
  So proving DPI for partial trace IS the hard core of the general DPI.

  ### Three proof paths considered

  **(a) Lieb's joint convexity** (Lieb 1973):
    The map (A, B) ↦ Tr(K† A^t K B^{1-t}) is jointly concave for t ∈ [0,1].
    From this one derives the DPI via a variational formula for relative entropy.
    **Status**: Lieb concavity is NOT in Mathlib as of 2026-05.
    See `lieb_joint_convexity_missing` axiom below.

  **(b) Klein's inequality + operator concavity of log**:
    Klein's inequality: Tr(f(A) - f(B) - f'(B)(A-B)) ≥ 0 for operator convex f.
    Applied to f = -log gives: Tr(ρ log ρ - ρ log σ) ≥ Tr(ρ - σ) ≥ 0.
    The DPI then follows from the operator concavity of log and the
    Peierls–Bogoliubov inequality.
    **Status**: Klein's inequality is NOT in Mathlib as of 2026-05.
    See `klein_inequality_missing` axiom below.

  **(c) Lindblad's direct approach** (Lindblad 1975):
    Use the integral representation of relative entropy and monotonicity
    of the Petz recovery map.
    **Status**: Petz recovery map is NOT in Mathlib as of 2026-05.

  ### Conclusion

  All three proof paths require Mathlib lemmas that do not yet exist.
  We state the theorem with `sorry` and document the gaps as axioms.

  References:
  - Lindblad, G. (1975). "Completely positive maps and entropy inequalities."
    Commun. Math. Phys. 40, 147–151.
  - Lieb, E.H. (1973). "Convex trace functions and the Wigner-Yanase-Dyson conjecture."
    Adv. Math. 11, 267–288.
  - Petz, D. (1986). "Sufficient subalgebras and the relative entropy of states of a
    von Neumann algebra." Commun. Math. Phys. 105, 123–131.
  - Ohya, M., Petz, D. (1993). "Quantum Entropy and Its Use." Springer.
-/

import Mathlib
import GaiaPhysicsLean.A1Dpi.Defs
import GaiaPhysicsLean.A1Dpi.UnitaryInv

open scoped MatrixOrder ComplexOrder

namespace GaiaPhysicsLean.A1Dpi

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-!
## Partial trace (general type-indexed version)

The partial trace Tr_n : Matrix (m × n) (m × n) ℂ → Matrix m m ℂ
traces out the second factor of a bipartite system.

For a matrix M indexed by (m × n), the partial trace over n is:
  (Tr_n M)(i, j) = ∑_{k : n} M (i, k) (j, k)
-/

/-- Partial trace over the second subsystem for general index types.
    For M : Matrix (m × n) (m × n) ℂ, the partial trace over n gives
    a matrix in Matrix m m ℂ by summing over the second index. -/
noncomputable def Matrix.partialTrace (n : Type*) [Fintype n]
    (M : Matrix (m × n) (m × n) ℂ) : Matrix m m ℂ :=
  fun i j => ∑ k : n, M (i, k) (j, k)

/-- The partial trace is linear in its argument. -/
lemma partialTrace_add (M N : Matrix (m × n) (m × n) ℂ) :
    Matrix.partialTrace n (M + N) = Matrix.partialTrace n M + Matrix.partialTrace n N := by
  ext i j
  simp [Matrix.partialTrace, Finset.sum_add_distrib]

/-- The partial trace commutes with scalar multiplication. -/
lemma partialTrace_smul (c : ℂ) (M : Matrix (m × n) (m × n) ℂ) :
    Matrix.partialTrace n (c • M) = c • Matrix.partialTrace n M := by
  ext i j
  simp [Matrix.partialTrace, Finset.mul_sum]

/-- The total trace factors through the partial trace:
    Tr(Tr_n M) = Tr(M). -/
lemma trace_partialTrace (M : Matrix (m × n) (m × n) ℂ) :
    Matrix.trace (Matrix.partialTrace n M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag, Matrix.partialTrace]
  exact (Fintype.sum_prod_type (fun p => M p p)).symm

/-- The partial trace of a positive semidefinite matrix is positive semidefinite.
    This follows because for any vector v : m → ℂ,
    v† (Tr_n M) v = ∑_k (v ⊗ e_k)† M (v ⊗ e_k) ≥ 0. -/
lemma partialTrace_posSemidef (M : Matrix (m × n) (m × n) ℂ) (hM : M.PosSemidef) :
    (Matrix.partialTrace n M).PosSemidef := by
  let B : n → Matrix (m × n) m ℂ := fun k p j => if p = (j, k) then 1 else 0
  suffices h : Matrix.partialTrace n M = ∑ k : n, (B k)ᴴ * M * (B k) by
    rw [h]
    exact Matrix.posSemidef_sum Finset.univ (fun k _ => hM.conjTranspose_mul_mul_same (B k))
  ext i j
  simp only [Matrix.partialTrace]
  simp only [Matrix.sum_apply]
  congr 1; ext k
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, B]

/-- **DPI for unitary channels** (trivial case).

    Unitary conjugation preserves the quantum relative entropy:
      S(U ρ U† ‖ U σ U†) = S(ρ ‖ σ)

    This is the easy case of DPI (equality holds). -/
lemma qre_unitary_mono
    {p : Type*} [Fintype p] [DecidableEq p]
    (ρ σ : Matrix p p ℂ) (U : Matrix p p ℂ)
    (hU_left : U.conjTranspose * U = 1) (hU_right : U * U.conjTranspose = 1)
    (hρ : IsSelfAdjoint ρ) (hσ : IsSelfAdjoint σ) :
    quantumRelativeEntropy (U * ρ * U.conjTranspose) (U * σ * U.conjTranspose) =
    quantumRelativeEntropy ρ σ := by
  have hU : U ∈ unitary (Matrix p p ℂ) :=
    Unitary.mem_iff.mpr ⟨hU_left, hU_right⟩
  rw [show U.conjTranspose = star U from rfl]
  exact qre_unitary_invariant ρ σ U hU hρ hσ

end GaiaPhysicsLean.A1Dpi
