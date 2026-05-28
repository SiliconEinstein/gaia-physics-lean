"""Initial BP plan for the FKG inequality for ferromagnetic Ising measures (B-tier).
LKM claim: gcn_46b3420ea41e4842
"""
from gaia.engine.lang import claim, derive

config_defs = claim(
    "Define the finite Ising configuration space ConfigSpace Λ := Λ → Fin 2, increasing observables, ferromagnetic couplings, and the Ising Gibbs-measure predicate.",
    prior=0.8,
    metadata={
        "prior_justification": "Finite product configuration spaces and PMFs are directly supported by Mathlib.",
        "action": "derive",
        "args": {"target_file": "PhysicsLean/B6FkgInequality/Defs.lean", "target_label": "ConfigSpace/IsingMeasure/Increasing"},
        "action_status": "done",
    },
)

submodularity = claim(
    "For non-negative couplings, the finite Ising Hamiltonian is submodular: H(σ ⊔ τ) + H(σ ⊓ τ) ≤ H(σ) + H(τ).",
    prior=0.7,
    metadata={
        "prior_justification": "This is a finite algebraic inequality over Fin 2 spins; case analysis and nlinarith suffice.",
        "action": "derive",
        "args": {"target_file": "PhysicsLean/B6FkgInequality/Defs.lean", "target_label": "isingHamiltonian_submodular"},
        "action_status": "done",
    },
)

holley_condition = claim(
    "Hamiltonian submodularity implies the Holley lattice condition μ σ μ τ ≤ μ (σ ⊔ τ) μ (σ ⊓ τ) for the ferromagnetic Ising Gibbs measure.",
    prior=0.7,
    metadata={
        "prior_justification": "This follows by substituting the Gibbs formula and using monotonicity of exp.",
        "action": "derive",
        "args": {"target_file": "PhysicsLean/B6FkgInequality/Lemmas_v2.lean", "target_label": "ising_lattice_condition"},
        "action_status": "done",
    },
)

fkg_from_lattice = claim(
    "The Holley lattice condition implies positive correlation for increasing real-valued observables via Mathlib's four-functions/FKG lemma.",
    prior=0.7,
    metadata={
        "prior_justification": "Mathlib contains the Ahlswede-Daykin/FKG lemma; arbitrary real-valued observables are shifted to non-negative ones.",
        "action": "derive",
        "args": {"target_file": "PhysicsLean/B6FkgInequality/Lemmas_v2.lean", "target_label": "fkg_from_lattice_condition"},
        "action_status": "done",
    },
)

target = claim(
    "For a finite ferromagnetic Ising Gibbs measure μ and increasing observables f,g, Eμ[f g] ≥ Eμ[f] Eμ[g].",
    prior=0.5,
    metadata={
        "prior_justification": "Classical FKG theorem; proof depends on finite Ising submodularity and the four-functions theorem.",
        "action": "derive",
        "args": {"target_file": "PhysicsLean/B6FkgInequality/Theorem.lean", "target_label": "fkg_inequality"},
        "action_status": "done",
    },
)

derive(
    target,
    given=[config_defs, submodularity, holley_condition, fkg_from_lattice],
    rationale="The Ising Hamiltonian submodularity gives Holley's lattice condition, which instantiates Mathlib's FKG lemma for increasing observables.",
)
