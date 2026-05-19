/- Choi's theorem: CP ⇔ Choi-matrix positive (finite-dim)
   LKM: gcn_81765219a10f496c (premise) + gcn_e167099bb6614b7c (Frembs 2022 Jordan reformulation)
   Tier: A
-/
import GaiaPhysicsLean.A2ChoiTheorem.Defs
import GaiaPhysicsLean.A2ChoiTheorem.Forward
import GaiaPhysicsLean.A2ChoiTheorem.Reverse

namespace GaiaPhysicsLean.A2ChoiTheorem

open scoped ComplexOrder

/-- **Choi's theorem.** A finite-dim linear map Φ : B(K) → B(H) is completely
positive iff its Choi matrix is positive semidefinite. -/
theorem choi_theorem_cp_iff_psd {dK dH : ℕ} (Φ : QChan dK dH) :
    IsCP Φ ↔ (Choi Φ).PosSemidef :=
  ⟨choi_psd_of_cp Φ, cp_of_choi_psd Φ⟩

end GaiaPhysicsLean.A2ChoiTheorem
