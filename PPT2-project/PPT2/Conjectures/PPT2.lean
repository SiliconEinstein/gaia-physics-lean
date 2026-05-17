/-
PPT2.Conjectures.PPT2 — top-level PPT² conjecture statement and the d=2 closed instance.

`PPT2Conjecture d` is the statement; closed dimensions (currently d=2) instantiate
it as theorems via the cases hierarchy.
-/
import PPT2.Basic
import PPT2.Choi
import PPT2.CP
import PPT2.EntanglementBreaking
import PPT2.PartialTranspose
import PPT2.Cases.Dim2

namespace PPT2

open Matrix
open scoped ComplexOrder

/-- The PPT² conjecture in dimension d: composition of any two PPT channels on
    `QChan d d` is entanglement-breaking, given the channel-validity hypotheses
    that the right factor `Ψ` is PSD-preserving and star-preserving.

    The two extra hypotheses encode the CP/channel structure that a `QChan`
    (currently a bare `LinearMap`) does not carry definitionally; both are
    consequences of complete positivity for any genuine quantum channel and
    they are exactly the hypotheses consumed by `EB_comp_right`
    (cf. `PPT2.EntanglementBreaking.choi_comp_right_formula`).  Open in
    general `d ≥ 4`. -/
def PPT2Conjecture (d : Nat) : Prop :=
  ∀ Φ Ψ : QChan d d, IsPPT Φ → IsPPT Ψ →
    (∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Ψ M).PosSemidef) →
    (∀ M : Matrix (Fin d) (Fin d) ℂ, Ψ Mᴴ = (Ψ M)ᴴ) →
    IsEB (Φ.comp Ψ)

/-- d = 2 closed instance: PPT² holds.

    iter-61: Promoted the `(Choi Φ).PosSemidef` assumption to an explicit
    hypothesis. The caller must provide this CP-validity condition alongside
    `IsPPT Φ`, since the bare `QChan` type does not encode it.

    iter-76: `ppt2_dim2` was strengthened to require an explicit Schmidt-rank-≤2
    PSD witness for `Choi Φ` (route 3 of the Peres-Horodecki sorry-discharge
    plan: see `PPT2.Cases.Dim2.ppt_implies_eb_dim2`).  This hypothesis is
    propagated here as `hSchmidtΦ`, matching the helper-layer convention. -/
theorem ppt2_conjecture_dim2
    (Φ Ψ : QChan 2 2)
    (hPSDΦ : (Choi Φ).PosSemidef)
    (hΦ : IsPPT Φ) (hΨ : IsPPT Ψ)
    (hPSDΨ : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, M.PosSemidef → (Ψ M).PosSemidef)
    (hStarΨ : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, Ψ Mᴴ = (Ψ M)ᴴ)
    (hSchmidtΦ : ∃ (s t : ℝ) (_ : 0 ≤ s) (_ : 0 ≤ t) (a b c d : Fin 2 → ℂ),
      Choi Φ = fun ⟨i, j⟩ ⟨k, l⟩ =>
        (s : ℂ)^2 * a i * b j * star (a k) * star (b l) +
        (t : ℂ)^2 * c i * d j * star (c k) * star (d l)) :
    IsEB (Φ.comp Ψ) :=
  ppt2_dim2 Φ Ψ hPSDΦ hΦ hΨ hPSDΨ hStarΨ hSchmidtΦ

end PPT2
