"""Initial BP plan for Reeh–Schlieder (C-tier, axiomatic statement-only).
LKM claim: gcn_687a62424c964753 (Reeh-Schlieder 1961; Haag, Local Quantum Physics §II.5.3).

C-tier formalization protocol: state the theorem precisely against
axiomatized Haag-Kastler infrastructure + document the proof gap with
paper-ref + Mathlib-PR-plan + LOC-estimate.
"""
from gaia.engine.lang import claim, support, deduction

haag_kastler_axioms = claim(
    "We axiomatize the Haag-Kastler framework: opaque types MinkowskiSpace, "
    "HilbertSpace, BoundedOp; operator algebra ops opNorm/opSub/opMul/opApply; "
    "LocalNet structure with isotony, locality (Einstein causality), and "
    "weak_additivity fields; VacuumRep with vacuum vector + irreducibility.",
    prior=0.97,
    metadata={
        "formal_artifact": "GaiaPhysicsLean/C1ReehSchliederAxiomatic/Defs.lean",
        "status": "axiomatized",
        "gap_kind": "framework_substrate",
        "note": "These are C-tier framework axioms, not target-statement weakenings. "
                 "Once Mathlib has von-Neumann-algebra modular theory, these can be "
                 "instantiated against ContinuousLinearMap and friends.",
    },
)

target = claim(
    "For every irreducible vacuum representation rep of a Haag-Kastler net, and "
    "every region O with non-empty causal complement, the vacuum vector "
    "rep.vacuum is simultaneously cyclic AND separating for the local algebra "
    "rep.net.alg O.",
    prior=0.99,
    metadata={
        "formal_artifact": "GaiaPhysicsLean/C1ReehSchliederAxiomatic/Theorem.lean",
        "lean_target": "reeh_schlieder_cyclic_and_separating",
        "status": "stated (C-tier sorry, documented)",
        "gap_kind": "open_modular_theory",
        "paper_ref": "Reeh-Schlieder 1961 Nuovo Cimento 22:1051; "
                       "Haag, Local Quantum Physics (1996) §II.5.3",
        "mathlib_pr_plan": "Tomita-Takesaki modular operator Δ + modular "
                              "conjugation J for von Neumann algebras in standard form",
        "loc_estimate": "2000+",
    },
)

deduction(
    premises=[haag_kastler_axioms],
    conclusion=target,
    reason="Given the axiomatized Haag-Kastler substrate, the theorem statement "
            "type-checks. The proof itself uses weak additivity + irreducibility "
            "+ analytic continuation (the Reeh-Schlieder argument), which depends "
            "on Tomita-Takesaki modular theory not yet in Mathlib.",
    prior=0.95,
)
