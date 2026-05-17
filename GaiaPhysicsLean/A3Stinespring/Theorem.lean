/- Stinespring dilation theorem (finite-dim)
   LKM source claim: gcn_85c00af123214e3e
   Tier: A
   See: /personal/lean_swarm/projects/a3_stinespring/PROBLEM.md

   **Primary target**: `stinespring_dilation`

   For any trace-preserving CP map E : B(H_Q) → B(H_Q) there exists a Hilbert space H_E, a vector |0⟩_E, and a unitary U on H_Q ⊗ H_E such that E(ρ) = Tr_E[U(ρ ⊗ |0⟩⟨0|)U†].
-/

import GaiaPhysicsLean.A3Stinespring.Lemmas

namespace GaiaPhysicsLean.A3Stinespring

open Matrix GaiaPhysicsLean.A2ChoiTheorem

/-- **Stinespring dilation theorem (finite-dimensional version).**

    For any trace-preserving completely positive (CPTP) map Φ : QChan d d,
    there exists:
      * An environment dimension r (at most d²)
      * A Stinespring dilation structure containing:
        - A canonical environment state |0⟩_E (index e0 : Fin r)
        - A unitary U on the composite space H_Q ⊗ H_E

    such that the channel can be realized as:
      Φ(ρ) = Tr_E[U(ρ ⊗ |0⟩⟨0|)U†]

    This theorem bridges the operator-sum (Kraus) representation and the
    unitary dilation picture, showing that every CPTP map arises from
    unitary evolution on a larger Hilbert space followed by partial trace. -/
theorem stinespring_dilation {d : ℕ} [NeZero d] (Φ : QChan d d)
    (hCP : IsCP Φ) (hTP : IsTP Φ) :
    ∃ (r : ℕ) (data : StinespringData d r),
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
        Φ ρ = partialTraceR (data.U * (Matrix.kroneckerMap (· * ·) ρ (vecMulVec (Pi.single data.e0 1) (star (Pi.single data.e0 1)))) * data.U.conjTranspose) := by
  -- Step 1: Obtain Kraus decomposition from CP+TP
  obtain ⟨r, hr_pos, ⟨kraus⟩⟩ := kraus_decomposition Φ hCP hTP
  haveI : NeZero r := ⟨Nat.pos_iff_ne_zero.mp hr_pos⟩
  use r

  -- Step 2: Extend the Kraus isometry to a unitary
  obtain ⟨U, hU_unitary, hU_col⟩ := isometry_extends_to_unitary kraus.K kraus.tp

  -- Step 3: Package into StinespringData
  use {
    e0 := 0
    U := U
    unitary := hU_unitary
  }

  -- Step 4: Verify the dilation identity using partial_trace_dilation
  intro ρ
  rw [kraus.channel ρ]
  exact (partial_trace_dilation kraus.K kraus.tp U hU_unitary hU_col ρ).symm

end GaiaPhysicsLean.A3Stinespring
