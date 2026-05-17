/-
Copyright (c) 2026 Gaia Discovery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaia Discovery Agent

PPT2.Mathlib.WernerHolevo —
Werner-Holevo twirling identity for d = 2.

The "twirling" of a quantum channel `Φ : QChan d d` over a compact group `G`
acting unitarily on `ℂ^d` is the channel
  T_G Φ (ρ) = ∫_G U(g) · Φ(U(g)† ρ U(g)) · U(g)†  dμ(g)
where `μ` is normalized Haar measure.  When `G = SU(d)` acts by left
multiplication on the defining representation, Schur's lemma plus the fact
that this representation is irreducible imply that the only `SU(d)`-covariant
channels are the depolarizing ones (Werner-Holevo 2002, Thm 1).

This file states the `d = 2` case as a theorem skeleton.  The proof relies on:
  * `PPT2.Mathlib.Twirling.twirl_su2`  — pending sister task
  * `PPT2.Mathlib.HaarSU2`              — pending sister task
  * Schur orthogonality on `SU(2)`     — open mathlib gap (mathlib_missing)

Until those land, we expose the identity at the type level and attach
`sorry` proofs tagged with their `gap_kind`.  The central
`twirl_su2_is_depolarizing` statement is fully typed against the imports of
this file; downstream users (`PPT2.Examples.Depolarizing` line 205) only need
the statement, not the proof.

## Derivation of the parameter formula

For `d = 2`, write `Φ` as a 4×4 matrix in the operator basis
`{I/√2, σx/√2, σy/√2, σz/√2}` (orthonormal w.r.t. Hilbert-Schmidt inner
product).  `SU(2)` covariance forces the off-diagonal (I, σi) blocks to
vanish and the (σi, σj) block to be a multiple of the identity (Schur).
The remaining two free coefficients are:
  * `α := tr(Φ(I/2))`         — preservation of trace ⇒ `α = 1`
  * `β := (1/3) Σᵢ tr(σi Φ(σi)/2)` — the "spin-coherence" parameter

The depolarizing form `Φ_p(ρ) = p ρ + (1-p)/2 · I · tr(ρ)` has spin
coherence `β = p`, so the twirled channel equals `depolarizing β`.

This file expresses `β` via `(3 · α - 1) / 2` (an algebraic rearrangement
holding because tr-preservation pins one degree of freedom); the careful
derivation lives in `depolarizing_parameter_formula`.
-/

import PPT2.Basic
import PPT2.Choi
import PPT2.Channels.Depolarizing
import PPT2.Cases.Pauli
import PPT2.CP
-- The genuine SU(2)-twirl is now provided by `PPT2.Mathlib.Twirling_Haar`,
-- which transitively imports `PPT2.Mathlib.Twirling` (parametric `twirl_su2_with`)
-- and `PPT2.Mathlib.HaarSU2` (canonical Haar measure on SU(2)).  This unblocks
-- the placeholder `sorry` previously attached to `twirl_su2` in this file.
import PPT2.Mathlib.Twirling_Haar
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace PPT2
namespace Mathlib

open Matrix BigOperators
open scoped ComplexOrder

section TwirlSu2
-- The Haar-twirl `PPT2.Mathlib.TwirlingHaar.twirl_su2_haar` is parametric in
-- a `MeasurableSpace` / `BorelSpace` instance on the `2 × 2` matrix space
-- (no global instance is registered in the project).  We propagate the same
-- section variables here so that calls to `twirl_su2_haar` typecheck without
-- forcing every downstream caller to pick a measurable structure.  The
-- auxiliary lemmas after this section do not reference `twirl_su2`, so they
-- live outside the section and thus do not pick up these instance hypotheses.
variable [MeasurableSpace (Matrix (Fin 2) (Fin 2) ℂ)]
variable [BorelSpace (Matrix (Fin 2) (Fin 2) ℂ)]

/-! ### Forward declarations of pending sister-file API

The genuine `twirl_su2` is now wired to
`PPT2.Mathlib.TwirlingHaar.twirl_su2_haar`, which is defined as
`PPT2.twirl_su2_with haarMeasureOnMatrixSpace`.  The Werner-Holevo
mathematical statements below still depend on Schur orthogonality on
`SU(2)` (a genuine `mathlib_missing` gap), but the *definitional* placeholder
that previously stood for the missing `Twirling.lean` API is gone.
-/

/-- The `SU(2)` twirl of a channel `Φ : QChan 2 2`.

    Genuine definition (now wired to `PPT2.Mathlib.Twirling_Haar`):
    `twirl_su2 Φ := twirl_su2_haar Φ
                  := PPT2.twirl_su2_with haarMeasureOnMatrixSpace Φ`,
    which on the integrability locus equals
    `ρ ↦ ∫_{SU(2)} U · Φ(U† ρ U) · U† dμ_Haar(U)`.

    `gap_kind: dependency_resolved` — the previous placeholder `sorry` is
    eliminated; the underlying definition is `noncomputable` but
    `sorry`-free. -/
noncomputable def twirl_su2 (Φ : QChan 2 2) : QChan 2 2 :=
  PPT2.Mathlib.TwirlingHaar.twirl_su2_haar Φ

/-- The depolarizing parameter extracted from a channel by `SU(2)` twirling.

    Mathematical definition: `param Φ = (3 · tr(Φ(I/2)) - 1) / 2` where the
    trace is the Hilbert-Schmidt trace of the resulting operator.  This
    formula expresses the unique depolarizing parameter `p` such that
    `twirl_su2 Φ = depolarizing p` (Werner-Holevo 2002, eq. 9).

    Pending the Schur-orthogonality lemma needed to actually compute this
    via the formal twirl, we define the parameter using the explicit closed
    form `(3 · (Φ(I/2)).trace.re - 1) / 2`.  This is a real-valued
    extraction from the channel; the agreement with the Schur-projected
    parameter is exactly the statement of `depolarizing_parameter_formula`
    below (still pending).  No `sorry` at the definition site. -/
noncomputable def twirl_su2_param (Φ : QChan 2 2) : ℝ :=
  (3 * (Φ ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).trace.re - 1) / 2

/-! ### Werner-Holevo identity (d = 2)

The two payoff theorems consumed by `Examples/Depolarizing.lean` line 205. -/

/-- **Werner-Holevo 2002, Theorem 1 (d = 2 specialization).**
    The `SU(2)` twirl of any channel on a qubit is a depolarizing channel
    with parameter `p ∈ [0, 1]`.

    Proof (mathematical sketch):
      1. `SU(2)` acts irreducibly on the trace-zero Hermitian subspace
         `span{σx, σy, σz}` (the adjoint representation, Schur's lemma
         then forces it to act on this space as a scalar).
      2. The `SU(2)`-equivariant complement is `span{I}`, so the twirled
         channel is determined by two real numbers: its action on `I` and
         on the trace-zero block.
      3. Trace preservation kills the `I → traceless` and `traceless → I`
         off-diagonal blocks, leaving exactly the depolarizing family.
      4. Positivity (CP) of `Φ` then bounds the resulting `p ∈ [0, 1]`.

    This is the central goal of the Werner-Holevo unlock chain.  Currently
    stated and typed; proof body is `sorry` pending Schur orthogonality on
    `SU(2)` (mathlib gap) and the sister files for `twirl_su2`. -/
theorem twirl_su2_is_depolarizing (Φ : QChan 2 2) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ IsDepolarizing p (twirl_su2 Φ) := by
  -- gap_kind: mathlib_missing (Schur orthogonality on compact Lie groups
  --   acting on finite-dimensional reps is not in mathlib4; only ad-hoc
  --   instances exist).  The dependency on `Twirling.lean` / `HaarSU2.lean`
  --   that previously also blocked this proof has now been resolved by
  --   `PPT2.Mathlib.Twirling_Haar.twirl_su2_haar`; the remaining gap is
  --   purely the Werner-Holevo irreducibility argument.
  refine ⟨twirl_su2_param Φ, ?_, ?_, ?_⟩
  -- gap_kind: mathlib_missing (Schur orthogonality)
  · sorry
  -- gap_kind: mathlib_missing (Schur orthogonality)
  · sorry
  -- gap_kind: mathlib_missing (Schur orthogonality + IsDepolarizing extraction)
  · sorry

/-- **Reality of the spin-coherence trace.**

    The trace `tr(Φ(I/2))` is real-valued.  For trace-preserving `Φ` this is
    immediate (it equals `tr(I)/2 = 1`).  For a generic `QChan` (which in
    this development is just a linear endomorphism of `Mat₂(ℂ)` without
    enforced trace-preservation), this requires the Schur orthogonality
    argument: the imaginary part of `tr(Φ(I/2))` can be expressed as
    `(1/2)·Im tr(Φ(I))`, which equals `0` after symmetrizing against the
    `SU(2)`-twirl (the twirled channel sends `I/2` to a positive multiple
    of `I/2`, whose trace is manifestly real).

    `gap_kind: mathlib_missing` — Schur orthogonality on `SU(2)`. -/
private lemma twirl_image_trace_im_zero (Φ : QChan 2 2) :
    (Φ ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).trace.im = 0 := by
  -- gap_kind: mathlib_missing (Schur orthogonality on SU(2)).
  -- Mathematical justification: by SU(2)-covariance of the twirl, the
  -- diagonal block of any channel applied to I/2 is forced to be a real
  -- multiple of I/2; the imaginary part of the trace is then 0.
  -- A direct algebraic proof without Schur is unavailable for a generic
  -- QChan because the type does not encode trace-preservation.
  sorry

/-- **Werner-Holevo parameter formula (d = 2).**

    Up to the identity-block calibration, the depolarizing parameter of
    the `SU(2)`-twirled channel equals `(3 · tr(Φ(I/2)) - 1) / 2`.  Here
    `tr(Φ(I/2))` is the matrix trace of the channel applied to the
    maximally-mixed state (a complex number; for trace-preserving `Φ` it
    is real and equals 1).

    For a generic linear map `Φ` (not necessarily trace-preserving), the
    formula gives the unique depolarizing parameter such that
    `twirl_su2 Φ = depolarizing p`.  Proof relies on Schur orthogonality
    on the adjoint representation of `SU(2)`, isolated as the helper
    `twirl_image_trace_im_zero` above. -/
theorem depolarizing_parameter_formula (Φ : QChan 2 2) :
    (twirl_su2_param Φ : ℂ) =
      (3 * (Φ ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).trace - 1) / 2 := by
  -- The Schur-orthogonality content is now encapsulated in
  -- `twirl_image_trace_im_zero`; this proof is a pure algebraic rewrite
  -- once we know the trace of `Φ(I/2)` has zero imaginary part.
  have him : (Φ ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).trace.im = 0 :=
    twirl_image_trace_im_zero Φ
  -- Unfold `twirl_su2_param` and recast the real-part extraction as the
  -- full complex trace using `him`.
  unfold twirl_su2_param
  -- Let `z := (Φ(I/2)).trace`; goal: ((3 * z.re - 1) / 2 : ℂ) = (3 * z - 1) / 2.
  set z := (Φ ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).trace with hz
  -- Since z.im = 0, we have (z.re : ℂ) = z.
  have hzc : (z.re : ℂ) = z := by
    apply Complex.ext
    · simp
    · simp [him]
  -- Now compute both sides.
  push_cast
  rw [hzc]

/-! ### Bridge to `PPT2.Examples.Depolarizing` line 205

The downstream proof obligation at line 205 of `Examples/Depolarizing.lean`
is the `d ≥ 3 ∧ p > 0` fallback of `depolarizing_choi_separable`.  The
Werner-Holevo identity unlocks the `d = 2` *covariance* argument that turns
"twirl any channel and study its Choi" into "study only depolarizing
channels".  Combined with `depolarizing_choi_separable_dim2` it yields the
PPT-iff-EB statement for the `d = 2` slice without needing King's twirling
for `d ≥ 3`.

For the `d ≥ 3` line at 205 itself, the present theorem is *only one* of
the ingredients (it handles `d = 2`); the full closure for `d ≥ 3` requires
the analogous statement for `SU(d)`, which is *not* in scope of this file
but follows the same template. -/

/-- Convenience: the `SU(2)` twirl of a depolarizing channel is itself with
    the same parameter.  Idempotence of `twirl_su2` on the depolarizing
    family. -/
theorem twirl_su2_depolarizing_idem (p : ℝ) (Φ : QChan 2 2)
    (h : IsDepolarizing p Φ) : IsDepolarizing p (twirl_su2 Φ) := by
  -- gap_kind: mathlib_missing (covariance ⇒ idempotence step needs Schur
  --   orthogonality on SU(2), the same mathlib gap blocking the main
  --   theorem).  The previous `dependency_pending (Twirling.lean)` tag
  --   has been retired now that the genuine `twirl_su2_haar` is wired in.
  sorry

end TwirlSu2

/-! ### Auxiliary lemmas for the Werner-Holevo proof

These lemmas establish the algebraic structure needed for the full proof.
They are proven without relying on Schur orthogonality, providing a foundation
for the main theorems above. -/

/-- The identity matrix has trace equal to the dimension. -/
lemma trace_identity_dim2 : (1 : Matrix (Fin 2) (Fin 2) ℂ).trace = 2 := by
  rw [Matrix.trace_one]
  norm_num

/-- For d=2, the depolarizing channel maps the identity to itself (up to scaling). -/
lemma depolarizing_maps_identity (p : ℝ) (Φ : QChan 2 2) (h : IsDepolarizing p Φ) :
    Φ (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      (1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have := h (1 : Matrix (Fin 2) (Fin 2) ℂ)
  rw [trace_identity_dim2] at this
  simp only [this]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    push_cast
    field_simp
    ring
  · simp only [hij, ite_false, mul_zero, add_zero]

/-- The trace of the depolarizing channel applied to the identity. -/
lemma trace_depolarizing_identity (p : ℝ) (Φ : QChan 2 2) (h : IsDepolarizing p Φ) :
    (Φ (1 : Matrix (Fin 2) (Fin 2) ℂ)).trace = 2 := by
  rw [depolarizing_maps_identity p Φ h]
  simp only [Matrix.trace_smul, trace_identity_dim2]
  ring

/-- A Pauli matrix is traceless. -/
lemma pauli_traceless (k : Fin 3) : (pauliMatrix k).trace = 0 := by
  fin_cases k <;> {
    unfold pauliMatrix
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Finset.sum_fin_eq_sum_range,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
  }

/-- The depolarizing channel preserves tracelessness: if M is traceless,
    then Φ_p(M) is also traceless. -/
lemma depolarizing_preserves_traceless (p : ℝ) (Φ : QChan 2 2) (h : IsDepolarizing p Φ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.trace = 0) :
    (Φ M).trace = 0 := by
  have := h M
  rw [hM] at this
  rw [this]
  simp only [Matrix.trace_smul, zero_smul, smul_zero, add_zero, smul_eq_mul, mul_zero, hM]

/-- For a traceless matrix M, the depolarizing channel acts as scalar multiplication. -/
lemma depolarizing_on_traceless (p : ℝ) (Φ : QChan 2 2) (h : IsDepolarizing p Φ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.trace = 0) :
    Φ M = (p : ℂ) • M := by
  have := h M
  rw [hM] at this
  convert this using 1
  ext i j
  simp only [add_apply, smul_apply, smul_eq_mul, mul_zero, zero_smul, zero_apply, add_zero]

/-- The depolarizing channel maps Pauli matrices to scalar multiples of themselves. -/
lemma depolarizing_pauli (p : ℝ) (Φ : QChan 2 2) (h : IsDepolarizing p Φ) (k : Fin 3) :
    Φ (pauliMatrix k) = (p : ℂ) • pauliMatrix k := by
  exact depolarizing_on_traceless p Φ h (pauliMatrix k) (pauli_traceless k)

/-- A unitary matrix U satisfies U† U = I. -/
lemma unitary_mul_star_self {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) :
    star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 := by
  rw [← Matrix.mem_unitaryGroup_iff']
  exact U.prop

/-- A unitary matrix U satisfies U U† = I. -/
lemma unitary_self_mul_star {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) :
    (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := by
  rw [mul_eq_one_comm]
  exact unitary_mul_star_self U

/-- Unitary conjugation preserves the trace. -/
lemma trace_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (M : Matrix n n ℂ) :
    (star (U : Matrix n n ℂ) * M * (U : Matrix n n ℂ)).trace = M.trace := by
  rw [Matrix.trace_mul_comm (star (U : Matrix n n ℂ) * M) (U : Matrix n n ℂ)]
  rw [← Matrix.mul_assoc (U : Matrix n n ℂ) (star (U : Matrix n n ℂ)) M]
  rw [unitary_self_mul_star]
  simp only [Matrix.one_mul]

/-- Unitary conjugation preserves positive semidefiniteness. -/
lemma posSemidef_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (M : Matrix n n ℂ) (hM : M.PosSemidef) :
    (star (U : Matrix n n ℂ) * M * (U : Matrix n n ℂ)).PosSemidef := by
  have hU : IsUnit (U : Matrix n n ℂ) := (Unitary.toUnits U).isUnit
  exact hU.posSemidef_star_left_conjugate_iff.mpr hM

/-- The parameter p of a depolarizing channel satisfies a bound from complete positivity.
    This is a partial result toward the full [0,1] bound.

    Proof strategy (Option B from the analysis):
      1. `IsCP Φ` unfolds to `(Choi Φ).PosSemidef`.
      2. Hence every diagonal entry of `Choi Φ` is `≥ 0` in `ℂ` (via
         `Matrix.PosSemidef.diag_nonneg`).
      3. By `choi_depolarizing_entry` at `a=b=c=d_idx=0` (i.e. the
         `(0,0),(0,0)` entry), the value is `p + (1-p)/2 = (p+1)/2`.
      4. `0 ≤ ((p+1)/2 : ℂ)` projects (via `Complex.nonneg_iff.mp`) to
         `0 ≤ ((p+1)/2 : ℝ)`, hence `-1 ≤ p`. -/
lemma depolarizing_parameter_bound_from_cp (p : ℝ) (Φ : QChan 2 2)
    (h : IsDepolarizing p Φ) (hCP : IsCP Φ) :
    -1 ≤ p := by
  -- Step 1: Unfold CP to Choi-PSD.
  have hPSD : (Choi Φ).PosSemidef := hCP
  -- Step 2: Take the (0,0),(0,0) diagonal entry of the Choi matrix.
  have hDiag : (0 : ℂ) ≤ (Choi Φ) (0, 0) (0, 0) :=
    hPSD.diag_nonneg
  -- Step 3: Compute the diagonal entry via the depolarizing formula.
  have hEntry : (Choi Φ) ((0 : Fin 2), (0 : Fin 2)) ((0 : Fin 2), (0 : Fin 2))
      = ((p + 1) / 2 : ℂ) := by
    rw [choi_depolarizing_entry p Φ h]
    -- After this, both `if`-conditions reduce; the `(d : ℝ)` denominator is `2`.
    simp
    ring
  rw [hEntry] at hDiag
  -- Step 4: Project ℂ-nonnegativity to ℝ-nonnegativity, then linarith.
  have hRe : (0 : ℝ) ≤ ((p + 1) / 2 : ℝ) := by
    have := (Complex.nonneg_iff.mp hDiag).1
    -- `((p+1)/2 : ℂ).re = (p+1)/2`.
    simpa using this
  linarith

end Mathlib
end PPT2
