"""Initial BP plan for Data Processing Inequality (A-tier, conditional).
LKM claim: gcn_6a2c5b36819b448b (Lindblad 1975 + Jin et al. 2022).

Proof strategy (Lindblad-Stinespring reduction):

  S(Λ(ρ) ‖ Λ(σ))
  = S(Tr_E[V ρ V†] ‖ Tr_E[V σ V†])   [Stinespring]
  ≤ S(V ρ V† ‖ V σ V†)                 [DPI for partial trace]   ← HYPOTHESIS
  = S(ρ ‖ σ)                             [isometric invariance via cfcₙ]

The middle step (DPI for partial trace, i.e. Lindblad-Uhlmann monotonicity)
is the deep operator-monotonicity result; current Mathlib lacks the
operator-concavity infrastructure needed to prove it. We expose it as the
explicit hypothesis `QRE_PartialTrace_Mono` on the main theorem,
analogous to A9's `TwoCobUP.WithExtend` data bundle.
"""
from gaia.engine.lang import claim, derive

kraus_decomposition = claim(
    "Every CPTP map Λ : QChan dK dH admits a Kraus decomposition: there exist "
    "r ∈ ℕ and Kraus operators K_i : Fin r → Matrix (Fin dH) (Fin dK) ℂ such "
    "that Λ(ρ) = Σ_i K_i ρ K_i† and Σ_i K_i† K_i = 1.",
    prior=0.97,
    metadata={
        "formal_artifact": "GaiaPhysicsLean/A1Dpi/KrausDecomposition.lean",
        "lean_target": "kraus_decomposition_general",
        "status": "proved (0 sorry, 0 axiom)",
        "method": "Choi spectral decomposition + sibling A2.choi_theorem_cp_iff_psd",
    },
)

stinespring_isometric = claim(
    "Stinespring isometric dilation: given Kraus form, there exist m ∈ ℕ and "
    "an isometry V : Matrix (Fin dH × Fin m) (Fin dK) ℂ (V†V = 1) such that "
    "Λ(ρ) = Tr_E[V ρ V†] for all ρ.",
    prior=0.95,
    metadata={
        "formal_artifact": "GaiaPhysicsLean/A1Dpi/Stinespring.lean",
        "lean_target": "stinespring_from_kraus",
        "status": "proved (0 sorry, 0 axiom)",
        "note": "Isometric formulation only; unitary lift not needed for DPI.",
    },
)

isometric_invariance = claim(
    "QRE is invariant under isometric conjugation: for V with V†V = 1, "
    "S(V ρ V† ‖ V σ V†) = S(ρ ‖ σ).",
    prior=0.97,
    metadata={
        "formal_artifact": "GaiaPhysicsLean/A1Dpi/Theorem.lean",
        "lean_target": "qre_isometry_invariance",
        "status": "proved (0 sorry, 0 axiom)",
        "method": "uses Mathlib.NonUnitalStarAlgHomClass.map_cfcₙ on isometryConjHom",
    },
)

qre_partial_trace_mono_hypothesis = claim(
    "DPI for partial trace (Lindblad-Uhlmann monotonicity): for bipartite "
    "ρ, σ ∈ Matrix (m × n) (m × n) ℂ both PSD, "
    "S(Tr_n ρ ‖ Tr_n σ) ≤ S(ρ ‖ σ). "
    "Exposed as the hypothesis bundle QRE_PartialTrace_Mono on the main theorem.",
    prior=0.9,
    metadata={
        "formal_artifact": "GaiaPhysicsLean/A1Dpi/Theorem.lean (abbrev QRE_PartialTrace_Mono)",
        "status": "hypothesis (conditional)",
        "gap_kind": "mathlib_missing",
        "paper_ref": "Lindblad 1975 Commun. Math. Phys. 40, 147–151; "
                       "Uhlmann 1977 Commun. Math. Phys. 54, 21–32; "
                       "Lieb 1973 Adv. Math. 11, 267–288 (joint convexity)",
        "mathlib_pr_plan": "Add Mathlib.Analysis.Matrix.OperatorConcavity "
                              "(Lieb concavity, Klein inequality, Petz variational formula)",
        "loc_estimate": "300-500",
    },
)

target = claim(
    "Conditional on QRE_PartialTrace_Mono: for every CPTPMap Λ : dK → dH and "
    "PSD ρ, σ : Matrix (Fin dK) (Fin dK) ℂ, "
    "S(Λ.toQChan ρ ‖ Λ.toQChan σ) ≤ S(ρ ‖ σ).",
    prior=0.99,
    metadata={
        "formal_artifact": "GaiaPhysicsLean/A1Dpi/Theorem.lean",
        "lean_target": "quantum_relative_entropy_dpi",
        "status": "proved (conditional)",
        "axiom_closure": "[propext, Classical.choice, Quot.sound]",
        "conditional_on": "QRE_PartialTrace_Mono hypothesis",
    },
)

derive(target, given=[kraus_decomposition, stinespring_isometric, isometric_invariance,
                qre_partial_trace_mono_hypothesis], rationale="Stinespring reduces CPTP to isometric-conjugation + partial-trace. "
            "Isometric invariance handles the V-conjugation step (proved). "
            "Partial-trace monotonicity handles the Tr_E step (hypothesis).",
)
