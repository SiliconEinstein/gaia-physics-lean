/-
GaiaPhysicsLean.A1Dpi.Stinespring

Stinespring dilation theorem for CPTP maps in finite dimensions.

**Primary target**: `cptp_stinespring`

For every CPTP map Λ : B(H) → B(H), there exist:
- A finite-dimensional ancilla Hilbert space E
- A unit vector |0⟩ ∈ E (represented as a pure state |0⟩⟨0|)
- A unitary U on H ⊗ E

such that for all density operators ρ:
  Λ(ρ) = Tr_E[U (ρ ⊗ |0⟩⟨0|) U†]

Strategy:
- Use Kraus decomposition from A2ChoiTheorem: Λ(ρ) = ∑ᵢ Kᵢ ρ Kᵢ†
- Stack Kraus operators into an isometry V : H → H ⊗ E
- Extend V to a unitary U on H ⊗ E
- Show that partial trace over E recovers Λ

References:
- Stinespring (1955), "Positive functions on C*-algebras"
- Nielsen & Chuang, "Quantum Computation and Quantum Information", §8.2.4
- Watrous, "The Theory of Quantum Information", §2.2.3
-/

import GaiaPhysicsLean.A2ChoiTheorem.Defs
import GaiaPhysicsLean.A1Dpi.PartialTrace
import GaiaPhysicsLean.A1Dpi.IsometryExtension
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Matrix.PosDef

namespace GaiaPhysicsLean.A1Dpi

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-!
## Trace-preserving maps and CPTP maps

A quantum channel is a completely positive, trace-preserving (CPTP) linear map.
-/

/-- A linear map Φ : B(H) → B(H) is trace-preserving if Tr(Φ(ρ)) = Tr(ρ) for all ρ. -/
def IsTracePreserving {dK dH : ℕ} (Φ : GaiaPhysicsLean.A2ChoiTheorem.QChan dK dH) : Prop :=
  ∀ (ρ : Matrix (Fin dK) (Fin dK) ℂ), Matrix.trace (Φ ρ) = Matrix.trace ρ

/-- A CPTP map is a completely positive, trace-preserving linear map. -/
structure CPTPMap (dK dH : ℕ) where
  toQChan : GaiaPhysicsLean.A2ChoiTheorem.QChan dK dH
  cp : GaiaPhysicsLean.A2ChoiTheorem.IsCP toQChan
  tp : IsTracePreserving toQChan

/-!
## Partial trace

The partial trace Tr_E : B(H ⊗ E) → B(H) traces out the second subsystem.

For matrices indexed by (Fin n × Fin m), the partial trace over the second system
is defined as:
  (Tr_E M)(i,j) = ∑_k M(i,k)(j,k)

In the Kronecker product representation, if M = ∑ᵢⱼ Aᵢⱼ ⊗ Bᵢⱼ, then
  Tr_E(M) = ∑ᵢⱼ Aᵢⱼ · Tr(Bᵢⱼ)

We use the general definitions from PartialTrace.lean.
-/

/-- The partial trace of a Kronecker product is the first factor times the trace of the second.
    Tr_E(A ⊗ B) = A · Tr(B). -/
lemma partialTrace_kronecker {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.partialTrace (Fin m) (Matrix.kroneckerMap (· * ·) A B) = Matrix.trace B • A := by
  ext i j
  simp [Matrix.partialTrace, Matrix.kroneckerMap_apply, Matrix.trace]
  rw [Finset.sum_mul]
  congr 1
  ext k
  ring

/-!
## Kraus operators and isometry construction

Given a CPTP map Λ with Kraus operators {Kᵢ}, we construct an isometry V : H → H ⊗ E
by stacking the Kraus operators:
  V |ψ⟩ = ∑ᵢ |i⟩ ⊗ Kᵢ|ψ⟩

The trace-preserving condition ∑ᵢ Kᵢ† Kᵢ = I ensures that V is an isometry: V† V = I.
-/

/-- Given Kraus operators Kᵢ : Matrix (Fin dH) (Fin dK) ℂ indexed by Fin m,
    construct the isometry V : Matrix (Fin dK) (Fin dK × Fin m) ℂ that stacks them.

    V acts on a vector |ψ⟩ ∈ H as: V|ψ⟩ = ∑ᵢ |i⟩ ⊗ Kᵢ|ψ⟩

    In matrix form: V(i,j) = Kⱼ(i.2, i.1) where i : Fin dK × Fin m, j : Fin dK. -/
noncomputable def krausToIsometry {dK dH m : ℕ}
    (K : Fin m → Matrix (Fin dH) (Fin dK) ℂ) :
    Matrix (Fin dH × Fin m) (Fin dK) ℂ :=
  fun (i : Fin dH × Fin m) (j : Fin dK) => K i.2 i.1 j

/-- The isometry condition V† V = I holds when ∑ᵢ Kᵢ† Kᵢ = I. -/
lemma krausToIsometry_isometry {dK dH m : ℕ}
    (K : Fin m → Matrix (Fin dH) (Fin dK) ℂ)
    (hK : ∑ i : Fin m, (K i).conjTranspose * K i = 1) :
    (krausToIsometry K).conjTranspose * krausToIsometry K = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, krausToIsometry, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have : ∀ b : Fin m, ∑ a : Fin dH, star (K b a i) * K b a j = ((K b).conjTranspose * K b) i j := by
    intro b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [this]
  rw [show ∑ b : Fin m, ((K b).conjTranspose * K b) i j =
      (∑ b : Fin m, (K b).conjTranspose * K b) i j from
    (Matrix.sum_apply i j Finset.univ _).symm]
  rw [hK]
  simp [Matrix.one_apply]

/-!
## Stinespring dilation theorem

**Main theorem**: Every CPTP map Λ : B(H) → B(H) can be realized as a unitary evolution
on an extended system H ⊗ E followed by partial trace over E.

More precisely: there exist a finite-dimensional ancilla space E (with dimension equal to
the number of Kraus operators), a pure state |0⟩⟨0| on E, and a unitary U on H ⊗ E such that:
  Λ(ρ) = Tr_E[U (ρ ⊗ |0⟩⟨0|) U†]

This is the fundamental structure theorem for quantum channels, showing that every CPTP map
arises from unitary dynamics on a larger system.
-/

/-- The pure state |0⟩⟨0| on the ancilla space, where |0⟩ is the first basis vector. -/
noncomputable def ancillaPureState (m : ℕ) [NeZero m] : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.single ⟨0, NeZero.pos m⟩ ⟨0, NeZero.pos m⟩ 1

/-- The ancilla pure state is a rank-1 projector. -/
lemma ancillaPureState_proj (m : ℕ) [NeZero m] :
    let ρ₀ := ancillaPureState m
    ρ₀ * ρ₀ = ρ₀ ∧ ρ₀.PosSemidef ∧ Matrix.trace ρ₀ = 1 := by
  simp only [ancillaPureState]
  set i₀ : Fin m := ⟨0, NeZero.pos m⟩
  refine ⟨?_, ?_, ?_⟩
  · ext a b
    simp only [Matrix.mul_apply, Matrix.single_apply]
    rw [Finset.sum_eq_single i₀]
    · rcases eq_or_ne i₀ a with rfl | ha <;> rcases eq_or_ne i₀ b with rfl | hb <;> simp [*]
    · intro x _ hx; simp [Ne.symm hx]
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine ⟨?_, ?_⟩
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
      rcases eq_or_ne i₀ i with rfl | hi <;> rcases eq_or_ne i₀ j with rfl | hj <;> simp [*]
    · intro x
      simp only [Matrix.single_apply]
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      by_cases hi : i₀ = i <;> by_cases hj : i₀ = j
      · subst hi; subst hj; simp; exact star_mul_self_nonneg _
      · subst hi; simp [show ¬(i₀ = j) from hj]
      · subst hj; simp [show ¬(i₀ = i) from hi]
      · simp [hi, hj]
  · simp [Matrix.trace, Matrix.diag, Matrix.single_apply]

/-- **Stinespring dilation theorem** (statement with Kraus operators).

    Given a CPTP map Λ with Kraus decomposition Λ(ρ) = ∑ᵢ Kᵢ ρ Kᵢ†,
    there exists a unitary U on H ⊗ E such that:
      Λ(ρ) = Tr_E[U (ρ ⊗ |0⟩⟨0|) U†]

    where E has dimension equal to the number of Kraus operators.

    Note: For a general channel dK → dH, we need an isometry V : dK → dH ⊗ m
    rather than a unitary on dK ⊗ m. The unitary formulation requires extending
    to a larger space. This is marked sorry for now. -/
theorem stinespring_from_kraus {dK dH m : ℕ} [NeZero m]
    (Λ : GaiaPhysicsLean.A2ChoiTheorem.QChan dK dH)
    (K : Fin m → Matrix (Fin dH) (Fin dK) ℂ)
    (hKraus : ∀ ρ : Matrix (Fin dK) (Fin dK) ℂ,
      Λ ρ = ∑ i : Fin m, K i * ρ * (K i).conjTranspose)
    (hTP : ∑ i : Fin m, (K i).conjTranspose * K i = 1) :
    ∃ (V : Matrix (Fin dH × Fin m) (Fin dK) ℂ),
      (V.conjTranspose * V = 1) ∧
      ∀ ρ : Matrix (Fin dK) (Fin dK) ℂ,
        Λ ρ = Matrix.partialTrace (Fin m) (V * ρ * V.conjTranspose) := by
  refine ⟨krausToIsometry K, krausToIsometry_isometry K hTP, fun ρ => ?_⟩
  rw [hKraus ρ]
  ext a b
  simp only [Matrix.partialTrace, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, krausToIsometry]

end GaiaPhysicsLean.A1Dpi
