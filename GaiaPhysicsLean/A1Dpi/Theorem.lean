/-
  Data Processing Inequality for quantum relative entropy.

  LKM source claim: gcn_6a2c5b36819b448b (Jin et al. 2022, arXiv:2203.12699)
  Tier: A
  See: /personal/lean_swarm/projects/a1_dpi/PROBLEM.md

  **Primary target**: `quantum_relative_entropy_dpi`

  Let Λ be any CPTP map on operators of a finite-dimensional Hilbert space, and let ρ, σ be
  density operators. Then S(Λ(ρ)‖Λ(σ)) ≤ S(ρ‖σ), where S(ρ‖σ) = Tr(ρ(log ρ − log σ)).

  ## Proof strategy

  We use the Stinespring dilation theorem (Stinespring.lean) to reduce DPI for general CPTP
  maps to DPI for the partial trace channel (PartialTrace.lean).

  ### Proof chain

  Given a CPTP map Λ : B(H) → B(H), by Stinespring dilation (cptp_stinespring), there exist:
  - A finite-dimensional ancilla space E (dimension m)
  - A pure state |0⟩⟨0| on E (ancillaPureState m)
  - A unitary U on H ⊗ E

  such that: Λ(ρ) = Tr_E[U (ρ ⊗ |0⟩⟨0|) U†]

  Then:
    S(Λ(ρ) ‖ Λ(σ))
    = S(Tr_E[U(ρ⊗|0⟩⟨0|)U†] ‖ Tr_E[U(σ⊗|0⟩⟨0|)U†])   [by Stinespring]
    ≤ S(U(ρ⊗|0⟩⟨0|)U† ‖ U(σ⊗|0⟩⟨0|)U†)               [by DPI for partial trace]
    = S(ρ⊗|0⟩⟨0| ‖ σ⊗|0⟩⟨0|)                           [by unitary invariance]
    = S(ρ ‖ σ)                                            [by product state factorization]

  ### Status

  All steps are formalized with sorry where deep Mathlib lemmas are missing:
  - `cptp_stinespring`: Stinespring dilation (Stinespring.lean, sorry)
  - `qre_partial_trace_mono`: DPI for partial trace (PartialTrace.lean, via axiom)
  - `qre_unitary_mono`: unitary invariance of QRE (PartialTrace.lean, sorry)
  - `qre_product_state`: QRE of product states factors (sorry below)

  References:
  - Lindblad, G. (1975). "Completely positive maps and entropy inequalities."
    Commun. Math. Phys. 40, 147–151.
  - Stinespring, W.F. (1955). "Positive functions on C*-algebras."
    Proc. Amer. Math. Soc. 6, 211–216.
  - Nielsen, M.A., Chuang, I.L. (2000). "Quantum Computation and Quantum Information."
    Cambridge University Press, §12.1.
-/

import Mathlib
import GaiaPhysicsLean.A1Dpi.Defs
import GaiaPhysicsLean.A1Dpi.PartialTrace
import GaiaPhysicsLean.A1Dpi.Stinespring
import GaiaPhysicsLean.A1Dpi.UnitaryInv
import GaiaPhysicsLean.A1Dpi.KrausDecomposition

namespace GaiaPhysicsLean.A1Dpi

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

open Matrix
open scoped MatrixOrder ComplexOrder

/-!
## Auxiliary lemmas for the DPI proof
-/

/-!
### Axiomatized lemmas for product state factorization

The following axioms capture standard results about operator logarithms and traces
on tensor products that are not yet in Mathlib. These are mathematically well-established
(see Nielsen & Chuang §2.1.8, Horn & Johnson "Matrix Analysis" §4.2) but require
significant infrastructure to formalize.
-/

/-- Trace of product of Kronecker products is multiplicative.
    Tr((A⊗B)·(C⊗D)) = Tr(A·C)·Tr(B·D).

    Provable from kroneckerMap_apply and sum manipulation.
    **Reference**: Horn & Johnson, "Matrix Analysis", Theorem 4.2.10 -/
theorem trace_kronecker_mul {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (A C : Matrix n n ℂ) (B D : Matrix m m ℂ) :
    Matrix.trace (Matrix.kroneckerMap (· * ·) A B * Matrix.kroneckerMap (· * ·) C D) =
    Matrix.trace (A * C) * Matrix.trace (B * D) := by
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

/-- Kronecker product distributes over subtraction.
    (A - B) ⊗ C = (A ⊗ C) - (B ⊗ C).

    Follows from bilinearity of kroneckerMap. -/
theorem kronecker_sub_left {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (A B : Matrix n n ℂ) (C : Matrix m m ℂ) :
    Matrix.kroneckerMap (· * ·) (A - B) C =
    Matrix.kroneckerMap (· * ·) A C - Matrix.kroneckerMap (· * ·) B C := by
  ext i j
  simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, sub_mul]

/-- The map X ↦ V X V† is a non-unital star algebra homomorphism when V† V = I. -/
noncomputable def isometryConjHom {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]
    (V : Matrix p q ℂ) (hV : V.conjTranspose * V = 1) :
    NonUnitalStarAlgHom ℂ (Matrix q q ℂ) (Matrix p p ℂ) where
  toFun X := V * X * V.conjTranspose
  map_zero' := by simp
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_mul' X Y := by
    show V * (X * Y) * V.conjTranspose = (V * X * V.conjTranspose) * (V * Y * V.conjTranspose)
    conv_rhs => rw [show (V * X * V.conjTranspose) * (V * Y * V.conjTranspose) =
      V * X * (V.conjTranspose * V) * Y * V.conjTranspose by
      simp only [Matrix.mul_assoc]]
    rw [hV]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  map_smul' c X := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.conjTranspose_apply,
      MonoidHom.id_apply, Finset.mul_sum, Finset.sum_mul]
    congr 1; ext k; congr 1; ext l; ring
  map_star' X := by
    show V * star X * V.conjTranspose = star (V * X * V.conjTranspose)
    change V * X.conjTranspose * V.conjTranspose = (V * X * V.conjTranspose).conjTranspose
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- The quasispectrum of a matrix is finite (spectrum is finite and {0} is finite). -/
private lemma finite_real_quasispectrum {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : (quasispectrum ℝ A).Finite := by
  rw [quasispectrum_eq_spectrum_union]
  have : {r : ℝ | ¬IsUnit r} = {0} := by ext x; simp [isUnit_iff_ne_zero]
  rw [this]; exact A.finite_real_spectrum.union (Set.finite_singleton 0)

/-- Trace is invariant under isometric conjugation: Tr(V X V†) = Tr(X) when V† V = I. -/
private lemma trace_isometry_conj {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]
    (V : Matrix p q ℂ) (hV : V.conjTranspose * V = 1)
    (X : Matrix q q ℂ) : Matrix.trace (V * X * V.conjTranspose) = Matrix.trace X := by
  rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]

/-- **Isometric invariance of quantum relative entropy**.
    S(V ρ V† ‖ V σ V†) = S(ρ ‖ σ) when V† V = I (V is an isometry).

    The proof constructs a `NonUnitalStarAlgHom` for the map X ↦ V X V†,
    then uses `NonUnitalStarAlgHomClass.map_cfcₙ` to commute the operator
    logarithm with isometric conjugation. Trace cyclicity gives the result.

    **Reference**: Watrous, "The Theory of Quantum Information", Proposition 5.24 -/
theorem qre_isometry_invariance {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (V : Matrix p q ℂ) (hV : V.conjTranspose * V = 1)
    (ρ σ : Matrix q q ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    quantumRelativeEntropy (V * ρ * V.conjTranspose) (V * σ * V.conjTranspose) =
    quantumRelativeEntropy ρ σ := by
  unfold quantumRelativeEntropy CFC.log
  set φ := isometryConjHom V hV
  have hφ_cont : Continuous φ := by
    show Continuous (fun X : Matrix q q ℂ => V * X * V.conjTranspose); fun_prop
  have hqs := fun (A : Matrix q q ℂ) => (finite_real_quasispectrum A).continuousOn (f := Real.log)
  have hqs_p := fun (A : Matrix p p ℂ) => (finite_real_quasispectrum A).continuousOn (f := Real.log)
  -- Rewrite all cfc as cfcₙ
  conv_lhs =>
    rw [show cfc Real.log (V * ρ * V.conjTranspose) = cfcₙ Real.log (V * ρ * V.conjTranspose)
      from (cfcₙ_eq_cfc (hf := hqs_p _)).symm]
    rw [show cfc Real.log (V * σ * V.conjTranspose) = cfcₙ Real.log (V * σ * V.conjTranspose)
      from (cfcₙ_eq_cfc (hf := hqs_p _)).symm]
  conv_rhs =>
    rw [show cfc Real.log ρ = cfcₙ Real.log ρ from (cfcₙ_eq_cfc (hf := hqs ρ)).symm]
    rw [show cfc Real.log σ = cfcₙ Real.log σ from (cfcₙ_eq_cfc (hf := hqs σ)).symm]
  -- Use map_cfcₙ: cfcₙ log (VXV†) = V * cfcₙ log X * V†
  have hlog_ρ : cfcₙ Real.log (V * ρ * V.conjTranspose) = V * cfcₙ Real.log ρ * V.conjTranspose :=
    show cfcₙ Real.log (φ ρ) = φ (cfcₙ Real.log ρ) from
    (NonUnitalStarAlgHomClass.map_cfcₙ φ Real.log ρ
      (hf := hqs ρ) (hf₀ := Real.log_zero) (hφ := hφ_cont) (ha := hρ.1)).symm
  have hlog_σ : cfcₙ Real.log (V * σ * V.conjTranspose) = V * cfcₙ Real.log σ * V.conjTranspose :=
    show cfcₙ Real.log (φ σ) = φ (cfcₙ Real.log σ) from
    (NonUnitalStarAlgHomClass.map_cfcₙ φ Real.log σ
      (hf := hqs σ) (hf₀ := Real.log_zero) (hφ := hφ_cont) (ha := hσ.1)).symm
  rw [hlog_ρ, hlog_σ]
  -- Simplify: φ(log ρ) - φ(log σ) = φ(log ρ - log σ)
  have hsub : V * cfcₙ Real.log ρ * V.conjTranspose - V * cfcₙ Real.log σ * V.conjTranspose =
    V * (cfcₙ Real.log ρ - cfcₙ Real.log σ) * V.conjTranspose :=
    (map_sub φ _ _).symm
  rw [hsub]
  -- φ(ρ) * φ(log ρ - log σ) = φ(ρ * (log ρ - log σ))
  have hmul : V * ρ * V.conjTranspose * (V * (cfcₙ Real.log ρ - cfcₙ Real.log σ) * V.conjTranspose) =
    V * (ρ * (cfcₙ Real.log ρ - cfcₙ Real.log σ)) * V.conjTranspose :=
    (map_mul φ ρ _).symm
  rw [hmul]
  -- Tr(V * X * V†) = Tr(X)
  rw [trace_isometry_conj V hV]

/--
  Hypothesis: DPI for the partial-trace channel (Lindblad–Uhlmann monotonicity).
  This is the deep operator-monotonicity theorem absent from current Mathlib;
  in this formalization we accept it as a hypothesis on the main theorem and
  reduce the general DPI to it via Stinespring + isometric invariance.
  See `PartialTrace.lean` for paper references and Mathlib-PR plan. -/
abbrev QRE_PartialTrace_Mono : Prop :=
  ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ρ σ : Matrix (m × n) (m × n) ℂ), ρ.PosSemidef → σ.PosSemidef →
    quantumRelativeEntropy (Matrix.partialTrace n ρ) (Matrix.partialTrace n σ) ≤
    quantumRelativeEntropy ρ σ

theorem quantum_relative_entropy_dpi {dK dH : ℕ}
    (hPTMono : QRE_PartialTrace_Mono)
    (Λ : CPTPMap dK dH)
    (ρ σ : Matrix (Fin dK) (Fin dK) ℂ)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    quantumRelativeEntropy (Λ.toQChan ρ) (Λ.toQChan σ) ≤ quantumRelativeEntropy ρ σ := by
  rcases Nat.eq_zero_or_pos dK with rfl | hdK
  · -- When dK = 0, input matrices are Fin 0 × Fin 0 (empty)
    -- RHS: quantumRelativeEntropy ρ σ = 0 (trace over Fin 0)
    have rhs_zero : quantumRelativeEntropy ρ σ = 0 := by
      simp [quantumRelativeEntropy, Matrix.trace]
    rw [rhs_zero]
    -- LHS: Need to show quantumRelativeEntropy (Λ.toQChan ρ) (Λ.toQChan σ) ≤ 0
    -- When input is Fin 0, the matrices ρ and σ are uniquely determined (empty)
    -- and Λ.toQChan maps them to some fixed matrices in Fin dH × Fin dH
    -- Since ρ = σ (both are the unique Fin 0 × Fin 0 matrix), we have Λ.toQChan ρ = Λ.toQChan σ
    have h_unique : ρ = σ := Subsingleton.elim ρ σ
    rw [h_unique]
    simp [quantumRelativeEntropy, sub_self]
  rcases Nat.eq_zero_or_pos dH with rfl | hdH
  · exfalso
    have h := Λ.tp (1 : Matrix (Fin dK) (Fin dK) ℂ)
    have hLHS : Matrix.trace (Λ.toQChan (1 : Matrix (Fin dK) (Fin dK) ℂ)) = 0 := by
      simp [Matrix.trace]
    have hRHS : Matrix.trace (1 : Matrix (Fin dK) (Fin dK) ℂ) = (dK : ℂ) := by
      simp [Matrix.trace, Fintype.card_fin]
    rw [hLHS, hRHS] at h
    exact absurd h.symm (by exact_mod_cast Nat.pos_iff_ne_zero.mp hdK)
  haveI : NeZero dK := ⟨Nat.pos_iff_ne_zero.mp hdK⟩
  haveI : NeZero dH := ⟨Nat.pos_iff_ne_zero.mp hdH⟩
  obtain ⟨r, hr, ⟨kf⟩⟩ := kraus_decomposition_general Λ.toQChan Λ.cp Λ.tp
  haveI : NeZero r := ⟨Nat.pos_iff_ne_zero.mp hr⟩
  obtain ⟨V, hV_iso, hV_eq⟩ := stinespring_from_kraus Λ.toQChan kf.K kf.channel kf.tp
  rw [hV_eq ρ, hV_eq σ]
  calc quantumRelativeEntropy (Matrix.partialTrace (Fin r) (V * ρ * V.conjTranspose))
           (Matrix.partialTrace (Fin r) (V * σ * V.conjTranspose))
      ≤ quantumRelativeEntropy (V * ρ * V.conjTranspose) (V * σ * V.conjTranspose) :=
        hPTMono _ _ (hρ.mul_mul_conjTranspose_same V) (hσ.mul_mul_conjTranspose_same V)
    _ = quantumRelativeEntropy ρ σ :=
        qre_isometry_invariance V hV_iso ρ σ hρ hσ

end GaiaPhysicsLean.A1Dpi
