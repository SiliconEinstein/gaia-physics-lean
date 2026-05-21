"""Initial BP plan for Choi's theorem (A-tier).
LKM claims: gcn_81765219a10f496c (Choi 1975) + gcn_e167099bb6614b7c (Frembs 2022).

Proof strategy: bidirectional equivalence
- Forward (CP ⇒ Choi PSD): apply CP at ancilla dim = dK to the maximally
  entangled state |Ω⟩⟨Ω|, encoded as rank-1 PSD via vecMulVec.
- Reverse (Choi PSD ⇒ CP): spectral decompose C_Φ into rank-1 PSD summands,
  each is the Choi matrix of an explicit Kraus operator; sum gives Φ as
  a sum of CP maps.
"""
from gaia.engine.lang import claim, derive

mathlib_psd_spectral = claim(
    "Mathlib provides Matrix.PosSemidef.spectralTheorem and "
    "Matrix.PosSemidef.eigenvalues_nonneg for finite-dim Hermitian matrices "
    "over ℂ.",
    prior=0.97,
    metadata={
        "prior_justification": "Verified by lean_local_search / lean_loogle.",
        "action": "abduction",
        "args": {"search_query": "PosSemidef spectralTheorem eigenvalues_nonneg"},
    },
)

choi_construction = claim(
    "We can define Choi : QChan dK dH → Matrix (Fin dK × Fin dH) (Fin dK × Fin dH) ℂ "
    "explicitly as (id ⊗ Φ)(|Ω⟩⟨Ω|) where |Ω⟩ = Σₐ |a,a⟩.",
    prior=0.99,
    metadata={
        "formal_artifact": "GaiaPhysicsLean/A2ChoiTheorem/Defs.lean",
        "lean_target": "Choi",
        "status": "proved",
    },
)

forward_direction = claim(
    "CP Φ ⇒ Choi Φ is PSD: apply CP at ancilla dimension n=dK to "
    "|Ω⟩⟨Ω| = vecMulVec ω (star ω) where ω : Fin(dK²) → ℂ is the diagonal "
    "indicator. The CP image is exactly Choi Φ.",
    prior=0.97,
    metadata={
        "formal_artifact": "GaiaPhysicsLean/A2ChoiTheorem/Forward.lean",
        "lean_target": "choi_psd_of_cp",
        "status": "proved",
    },
)

reverse_direction = claim(
    "Choi Φ PSD ⇒ CP Φ: spectral decompose Choi Φ = Σᵢ λᵢ |vᵢ⟩⟨vᵢ| with "
    "λᵢ ≥ 0; each rank-1 summand is the Choi matrix of Kraus operator "
    "Kᵢ = √λᵢ · reshape(vᵢ); Φ = Σᵢ Kᵢ • Kᵢ† is a sum of CP maps.",
    prior=0.95,
    metadata={
        "formal_artifact": "GaiaPhysicsLean/A2ChoiTheorem/Reverse.lean",
        "lean_target": "cp_of_choi_psd",
        "status": "proved",
    },
)

target = claim(
    "Choi's theorem: for any QChan Φ between finite-dim matrix spaces, "
    "IsCP Φ ↔ (Choi Φ).PosSemidef.",
    prior=0.99,
    metadata={
        "formal_artifact": "GaiaPhysicsLean/A2ChoiTheorem/Theorem.lean",
        "lean_target": "choi_theorem_cp_iff_psd",
        "status": "proved",
        "axiom_closure": "[propext, Classical.choice, Quot.sound]",
    },
)

derive(target, given=[mathlib_psd_spectral, choi_construction, forward_direction, reverse_direction], rationale="Forward and reverse directions assemble into the bidirectional "
            "equivalence via simple iff-introduction.",)
