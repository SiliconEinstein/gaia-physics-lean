"""Initial BP plan for Tsirelson bound for CHSH (≤ 2√2) (A-tier).
LKM claim: gcn_9f07543c6ff944b0 (premise) + gcn_aea213dfec744535 (SDP conclusion)
"""
from gaia.engine.lang import claim, support, deduction, abduction

# Premise 1: Simplified CHSH bound without tensor products
# For single-system formulation: CHSH = A_0(B_0+B_1) + A_1(B_0-B_1)
chsh_operator_norm = claim(
    "For dichotomic observables A_0, A_1, B_0, B_1 with ||A_i||,||B_j||≤1 and A_i^2=B_j^2=I, the CHSH operator S = A_0(B_0+B_1) + A_1(B_0-B_1) satisfies ||S|| ≤ 2√2.",
    prior=0.99,
    metadata={
        "prior_justification": "Verified via Lean proof with 0 sorries.",
        "action": "deduction",
        "args": {"target_file": "PhysicsLean/A10Tsirelson/Theorem.lean", "target_label": "chsh_operator_norm_bound"},"action_status": "done"
    },
action_id="act_559fdbb2be6b", action_status="done", verify_history=[{"source": "verify:main_agent", "action_id": "act_559fdbb2be6b", "verdict": "verified", "confidence": "0.95", "evidence": "Lemma chsh_operator_norm_bound fully proved with 0 sorries. Uses parallelogram law and AM-QM inequality to bound ||S|| ≤ 2√2 pointwise."}])

# Premise 2: Commutator norm bound
commutator_bound = claim(
    "For bounded operators A, B with ||A||,||B||≤1, the norm ||[A,B]|| ≤ 4.",
    prior=0.99,
    metadata={
        "prior_justification": "Verified via Lean proof with 0 sorries.",
        "action": "deduction",
        "args": {"target_file": "PhysicsLean/A10Tsirelson/Theorem.lean", "target_label": "commutator_norm_bound"},"action_status": "done"
    },
action_id="act_ffdecb098263", action_status="done", verify_history=[{"source": "verify:inquiry_review", "action_id": "act_ffdecb098263", "verdict": "verified", "confidence": "0.950", "evidence": "The sub-agent correctly applies the triangle inequality and sub-multiplicativity to derive ||[A,B]|| ≤ 2||A|| ||B|| ≤ 2, which is stricter than the claim's bound of 4. The premises are standard and pl"}])

# Premise 3: Norm extraction from squared bound
norm_from_squared = claim(
    "If ||X^2|| ≤ 8 for a self-adjoint operator X, then ||X|| ≤ 2√2.",
    prior=0.99,
    metadata={
        "prior_justification": "Verified via Lean proof with 0 sorries.",
        "action": "deduction",
        "args": {"target_file": "PhysicsLean/A10Tsirelson/Theorem.lean", "target_label": "norm_from_squared_selfadjoint"},"action_status": "done"
    },
action_id="act_8624b0a9c134", action_status="done", verify_history=[{"source": "verify:inquiry_review", "action_id": "act_8624b0a9c134", "verdict": "verified", "confidence": "0.950", "evidence": "The core premise that ||X²|| = ||X||² for self-adjoint operators is a standard consequence of the spectral theorem, directly implying the claim. The counter-evidence merely notes a missing Mathlib lem"}])

# Target: Tsirelson bound
target = claim(
    "For dichotomic observables A_0, A_1, B_0, B_1 with ||A_i||,||B_j||≤1 on any Hilbert space and any state |ψ⟩, |⟨A_0 B_0 + A_0 B_1 + A_1 B_0 − A_1 B_1⟩| ≤ 2√2.",
    prior=0.99,
    metadata={
        "prior_justification": "Verified via Lean proof with 0 sorries, standard axioms only.",
        "action": "deduction",
        "args": {"target_file": "PhysicsLean/A10Tsirelson/Theorem.lean", "target_label": "tsirelson_chsh_bound"},
        "action_status": "done"
    },
    action_id="act_target_verification",
    action_status="done",
    verify_history=[{
        "source": "verify:main_agent",
        "action_id": "act_target_verification",
        "verdict": "verified",
        "confidence": "0.95",
        "evidence": "Theorem tsirelson_chsh_bound fully proved with 0 sorries. Proof complete via chsh_operator_norm_bound and algebraic rewriting."
    }, {
        "source": "verify:main_agent_final",
        "action_id": "act_final_verification",
        "verdict": "verified",
        "confidence": "0.99",
        "evidence": "lake build PhysicsLean.A10Tsirelson.Theorem succeeds with rc=0. Theorem tsirelson_chsh_bound at line 147 has 0 sorries. Axioms: propext, Classical.choice, Quot.sound (standard only). All hallucinated Mathlib lemmas fixed via MCP search (opNorm_comp_le, le_opNorm, opNorm_le_bound', sq_le_sq₀)."
    }]
)

# Strategy: deduce target from premises
deduction(
    premises=[chsh_operator_norm, commutator_bound, norm_from_squared],
    conclusion=target,
    reason="Tsirelson's algebraic proof: (1) show CHSH operator has bounded norm via algebraic expansion, (2) use commutator bounds and dichotomic property, (3) apply spectral theorem for self-adjoint operators to get ||CHSH|| ≤ 2√2.",
    prior=0.8,
)
