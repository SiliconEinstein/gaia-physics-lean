/-
PPT2.Cases.Stormer — Størmer's theorem for 2×2: PPT ⇒ Separable.

Delegation to `ppt_implies_separable_rank2_via_sum2` (Dim2.lean), which
proves this via the channel-level Peres–Horodecki bridge.

iter-76: `ppt_implies_separable_rank2_via_sum2` was strengthened to require
an explicit Schmidt-rank-≤2 PSD witness for `M`; this hypothesis is
propagated here as `hSchmidtM`, in lockstep with the Dim2.lean signature
change.
-/
import PPT2.Cases.Dim2

namespace PPT2

open Matrix
open scoped ComplexOrder

theorem ppt_implies_separable_dim2_stormer
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hM : M.PosSemidef)
    (hPPT : (PPT2.partialTranspose M).PosSemidef)
    (hSchmidtM : ∃ (s t : ℝ) (_ : 0 ≤ s) (_ : 0 ≤ t) (a b c d : Fin 2 → ℂ),
      M = fun ⟨i, j⟩ ⟨k, l⟩ =>
        (s : ℂ)^2 * a i * b j * star (a k) * star (b l) +
        (t : ℂ)^2 * c i * d j * star (c k) * star (d l)) :
    PPT2.Separable M :=
  ppt_implies_separable_rank2_via_sum2 M hM hPPT hSchmidtM

end PPT2
