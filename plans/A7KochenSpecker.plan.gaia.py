"""Initial BP plan for Kochen–Specker theorem (combinatorial, 18-vector set) (A-tier).
LKM claim: gcn_0b8cd733edc4459d

Iter 1 finding: native_decide introduces non-standard axiom. Switching to structural parity proof.
"""
from gaia.engine.lang import claim, support, deduction, abduction, contradiction

# Premise: Mathlib has finite-dim inner product spaces and decidability
mathlib_foundations = claim(
    "Mathlib4 provides Finset, Fintype, decidability, and finite-dimensional inner product spaces over ℂ",
    prior=0.95,
    metadata={
        "prior_justification": "Standard Mathlib4 content; verified by grep/Loogle",
        "status": "background_knowledge"
    }
)

# Premise: 18-vector encoding is computable
vector_encoding = claim(
    "The Cabello-Estebaranz-García-Alcaine 18 vectors in C^4 can be encoded as Fin 18 → Fin 4 → ℂ table",
    prior=0.95,
    metadata={
        "prior_justification": "Already implemented in Theorem.lean",
        "status": "completed"
    }
)

# Premise: Each vector appears in exactly 2 bases
vector_appearance_count = claim(
    "Each of the 18 vectors appears in exactly 2 of the 9 bases",
    prior=0.95,
    metadata={
        "prior_justification": "Already proved by decide in Theorem.lean:80-81",
        "status": "completed"
    }
)

# Premise: Sum of basis counts equals twice the true count
sum_basis_count_lemma = claim(
    "For any valuation a, the sum of basisCount over all 9 bases equals 2 times the number of vectors assigned true",
    prior=0.5,
    metadata={
        "prior_justification": "Theorem statement correct, builds with sorry. Gap: needs explicit computation proof. New iter3 strategy: convert trueCount to sum of indicators, expand both sides fully, use generalize to abstract each (if a i then 1 else 0) as Nat var, close with omega/ring.",
        "status": "pending",
        "action": "deduction",
        "args": {
            "domain": "lean",
            "target_file": "PhysicsLean/A7KochenSpecker/Theorem.lean",
            "target_label": "sum_basisCount_eq_twice_trueCount",
            "lake_project_dir": "/personal/lean_swarm/lean",
            "guidance": "Iter3 strategy: (1) Rewrite trueCount a = (filter (a · = true) univ).card to ∑ i:Fin 18, (if a i then 1 else 0) using Finset.card_eq_sum_ones / Finset.sum_filter / Finset.sum_boole. (2) Distribute 2 * ∑ = ∑ 2*. (3) Fully expand LHS to 36 terms (9 bases × 4 vectors each), unfold basisCount and bases. (4) Use `generalize ha_i : (if a i then 1 else 0 : Nat) = x_i` for each i ∈ Fin 18. (5) Both sides become linear Nat expressions in 18 variables; close with `ring` or `omega`. Avoid Finset.sum_bij. Avoid split_ifs (would create 2^18 cases)."
        }, "action_status": "failed"
    },
    action_id="act_6d29eee7cdcb",
    action_status="failed",
verify_history=[{"source": "verify:unavailable", "action_id": "act_6d29eee7cdcb", "verdict": "inconclusive", "confidence": "0.000", "evidence": "lean 路径越权"}])

# Premise: KS valuation implies sum equals 9
ks_valuation_sum_nine = claim(
    "If isKSValuation a holds, then the sum of basisCount over all 9 bases equals 9",
    prior=0.95,
    metadata={
        "prior_justification": "Proof completed in Theorem.lean:93-111, builds successfully",
        "status": "completed"
    }
)

# Contradiction: 9 is odd but 2*k is even
parity_contradiction = claim(
    "9 is odd but any number of the form 2*k is even, yielding a contradiction",
    prior=0.99,
    metadata={
        "prior_justification": "Already proved by omega in Theorem.lean:110-111",
        "status": "completed"
    }
)

# Target: Main theorem (structural proof)
target_structural = claim(
    "The Cabello-Estebaranz-García-Alcaine 18-vector set in C^4 admits no 0/1 assignment giving exactly one '1' per orthonormal basis (proved via parity argument)",
    prior=0.7,
    metadata={
        "prior_justification": "Proof complete modulo dependency. Parity argument correct: sum=9 (odd) but sum=2*trueCount (even). Only blocker: sum_basisCount_eq_twice_trueCount has sorry.",
        "status": "complete_modulo_dependency",
        "action": "deduction",
        "args": {
            "domain": "lean",
            "target_file": "PhysicsLean/A7KochenSpecker/Theorem.lean",
            "target_label": "kochen_specker_18vec_no_valuation_structural",
            "lake_project_dir": "/personal/lean_swarm/lean",
            "guidance": "Main proof at lines 121-129 is complete. Only blocker is sum_basisCount_eq_twice_trueCount lemma."
        }, "action_status": "failed"
    },
action_id="act_372342e9733a", action_status="failed", verify_history=[{"source": "verify:unavailable", "action_id": "act_372342e9733a", "verdict": "inconclusive", "confidence": "0.000", "evidence": "lean 路径越权"}])

# Strategy: structural proof via parity
lcs_f7123d44b575e01d = deduction(
    premises=[vector_appearance_count, sum_basis_count_lemma, ks_valuation_sum_nine, parity_contradiction],
    conclusion=target_structural,
    reason="Parity argument: if isKSValuation a holds, then sum = 9 (odd) but also sum = 2*trueCount (even), contradiction.",
    prior=0.8
)

# Connect mathlib_foundations as background support
support(premises=[mathlib_foundations], conclusion=vector_encoding)
support(premises=[mathlib_foundations], conclusion=vector_appearance_count)

# Old target with native_decide (kept for reference but not connected)
target_native = claim(
    "The Cabello-Estebaranz-García-Alcaine 18-vector set in C^4 admits no 0/1 assignment giving exactly one '1' per orthonormal basis (proved via native_decide)",
    prior=0.9,
    metadata={
        "prior_justification": "Proof exists but uses non-standard axiom",
        "status": "completed_but_invalid_axioms"
    }
)
