"""Initial BP plan for Stinespring dilation theorem (finite-dim) (A-tier).
LKM claim: gcn_85c00af123214e3e

Strategy: from CP+TP we extract Kraus operators K_k : H_Q → H_Q satisfying
Σ_k K_k† K_k = I_{H_Q}. The isometry V|ψ⟩ := Σ_k K_k|ψ⟩⊗|k⟩ has V†V = I.
Extend V on H_Q⊗span(|0⟩) to a unitary U on H_Q⊗H_E (Gram-Schmidt on the
orthogonal complement). Stinespring identity E(ρ) = Tr_E[U(ρ⊗|0⟩⟨0|)U†]
follows from V having that ‖|ψ⟩’s tensored slot fixed at |0⟩'’s row in U,
giving Tr_E[U(ρ⊗|0⟩⟨0|)U†] = Tr_E(V ρ V†) = Σ_k K_k ρ K_k† = E(ρ).
"""
from gaia.engine.lang import claim, support, deduction

# --- Sub-claims (each with metadata.action so dispatcher schedules a runner) ---

claim_defs = claim(
    "Defs.lean: define the finite-dim quantum channel type, TP predicate, "
    "Kraus-form data, Stinespring dilation structure (Hilbert space H_E, vector |0⟩, "
    "unitary U on H_Q ⊗ H_E), and partial-trace specialised to matrix algebras.",
    prior=0.6,
    metadata={
        "prior_justification": "Definitions reuse A2 Choi (QChan, IsCP). TP predicate and StinespringData record are routine.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Defs.lean",
            "lean_target": "PhysicsLean.A3Stinespring",
            "subgoal": "types and definitions",
        },"action_status": "failed"
    },
action_id="act_951525cef886", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_951525cef886", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

claim_kraus = claim(
    "Lemmas.lean: from a CP+TP map Φ : QChan d d obtain Kraus operators K_k : Matrix (Fin d) (Fin d) ℂ "
    "such that Φ(X) = Σ_k K_k * X * K_k† and Σ_k K_k† * K_k = 1 (TP condition).",
    prior=0.4,
    metadata={
        "prior_justification": "Kraus existence is ~30-line packaging of A2.Reverse spectral decomposition; TP gives the resolution-of-identity.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.kraus_decomposition",
            "subgoal": "Kraus form for CPTP",
        },"action_status": "failed"
    },
action_id="act_8ddc3fa43e25", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_8ddc3fa43e25", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

claim_isometry = claim(
    "Lemmas.lean: define V : Matrix(Fin d, Fin 1, ℂ) → Matrix(Fin d × Fin r, Fin 1, ℂ) by "
    "V|ψ⟩ = Σ_k K_k|ψ⟩⊗|k⟩ and prove V† V = I from Σ K_k† K_k = I.",
    prior=0.4,
    metadata={
        "prior_justification": "Standard isometry calculation; pure algebra given the Kraus identity.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.kraus_isometry",
            "subgoal": "V isometry",
        },"action_status": "failed"
    },
action_id="act_70e79ae0b2ea", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_70e79ae0b2ea", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

claim_unitary_extend = claim(
    "Lemmas.lean: extend the isometry V to a unitary U on Fin d × Fin r so that "
    "U.submatrix (·, (·, 0)) = V (i.e. U restricted to the |0⟩ column equals V). "
    "Construction: complete the columns of V to an orthonormal basis (Gram-Schmidt).",
    prior=0.3,
    metadata={
        "prior_justification": "Mathlib has GramSchmidt; finite-dim isometry extension is standard linear algebra.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.isometry_extends_to_unitary",
            "subgoal": "unitary extension",
        },"action_status": "failed"
    },
action_id="act_0df525664afe", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_0df525664afe", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

claim_partial_trace = claim(
    "Lemmas.lean: for the constructed U and |0⟩ = e₀ ∈ Fin r, "
    "Tr_E [U (ρ ⊗ |0⟩⟨0|) U†] = Σ_k K_k ρ K_k† = Φ(ρ).",
    prior=0.4,
    metadata={
        "prior_justification": "Direct unfolding using that U|ψ⟩⊗|0⟩ = V|ψ⟩ = Σ K_k|ψ⟩⊗|k⟩; partial-trace acts on right factor.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.partial_trace_dilation",
            "subgoal": "partial trace identity",
        },"action_status": "failed"
    },
action_id="act_af5420fe8b2e", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_af5420fe8b2e", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

target = claim(
    "For any trace-preserving CP map E : B(H_Q) → B(H_Q) there exists a Hilbert space H_E, a vector |0⟩_E, and a unitary U on H_Q ⊗ H_E such that E(ρ) = Tr_E[U(ρ ⊗ |0⟩⟨0|)U†].",
    prior=0.5,
    metadata={
        "prior_justification": "Theorem is classical (Stinespring 1955); only the Lean formalization is uncertain.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Theorem.lean",
            "lean_target": "PhysicsLean.A3Stinespring.stinespring_dilation",
            "subgoal": "main theorem",
        },"action_status": "failed"
    },
action_id="act_f0a8c87c66ce", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_f0a8c87c66ce", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

# --- Sub-claims for filling sorries in Lemmas.lean ---

claim_kraus_tp_helper = claim(
    "Lemmas.lean: prove kraus_tp_from_choi_trace - that ∑_k K_k† K_k = I follows from "
    "the trace-preservation condition on the Choi matrix and the spectral decomposition.",
    prior=0.35,
    metadata={
        "prior_justification": "Requires connecting Choi matrix trace properties to Kraus operator sum; involves reshaping and partial trace algebra.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.kraus_tp_from_choi_trace",
            "subgoal": "TP condition from Choi trace",
        },"action_status": "failed"
    },
action_id="act_77cfd34f6391", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_77cfd34f6391", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

claim_kraus_channel_helper = claim(
    "Lemmas.lean: prove kraus_channel_from_choi - that Φ(X) = ∑_k K_k X K_k† follows from "
    "the Choi matrix spectral decomposition and the definition of the Choi matrix.",
    prior=0.35,
    metadata={
        "prior_justification": "Requires unfolding Choi matrix definition and connecting spectral decomposition to channel action; involves vectorization algebra.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.kraus_channel_from_choi",
            "subgoal": "channel identity from Choi",
        },"action_status": "failed"
    },
action_id="act_bcbadb300f62", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_bcbadb300f62", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

claim_unitary_extend_proof = claim(
    "Lemmas.lean: prove isometry_extends_to_unitary - construct unitary U from isometry V "
    "by completing columns to orthonormal basis (Gram-Schmidt or direct construction).",
    prior=0.3,
    metadata={
        "prior_justification": "Standard finite-dimensional linear algebra; Mathlib has orthonormal basis tools but may need manual construction.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.isometry_extends_to_unitary",
            "subgoal": "isometry to unitary extension",
        },"action_status": "failed"
    },
action_id="act_91d6e0d726da", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_91d6e0d726da", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

claim_partial_trace_proof = claim(
    "Lemmas.lean: prove partial_trace_dilation - that Tr_E[U(ρ⊗|0⟩⟨0|)U†] = ∑_k K_k ρ K_k† "
    "using the property that U restricted to |0⟩ column equals the Kraus isometry V.",
    prior=0.35,
    metadata={
        "prior_justification": "Requires unfolding partial trace definition and using U's column structure; involves tensor product and trace algebra.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.partial_trace_dilation",
            "subgoal": "partial trace dilation identity",
        },"action_status": "failed"
    },
action_id="act_505222d2c94b", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_505222d2c94b", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

# --- Fresh pending claims (iter 2 resume) targeting remaining sorries ---

claim_isometry_extend_v2 = claim(
    "Lemmas.lean: fill the sorry at line 191 in isometry_extends_to_unitary by completing "
    "the orthonormal columns of V to a full unitary on H_Q⊗H_E. Use Mathlib's Orthonormal.extend "
    "/ Basis.ofOrthonormalEquivUnit / gramSchmidt machinery. The constructed U must satisfy "
    "U.submatrix (·, (·,0)) = V, i.e. its |0⟩ column block equals the Kraus isometry V.",
    prior=0.45,
    metadata={
        "prior_justification": "Standard finite-dim isometry extension; Mathlib has orthonormal-basis extension. MCP search will locate the canonical lemma.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.isometry_extends_to_unitary",
            "subgoal": "fill sorry at line 191 via Gram-Schmidt / Orthonormal.extend",
            "sorry_line": 191,
            "mcp_search_hints": ["Orthonormal.extend", "gramSchmidt", "Basis.ofOrthonormalEquivUnit", "Matrix.unitaryGroup"],
        },"action_status": "failed"
    },
action_id="act_6f06a3506e48", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_6f06a3506e48", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

claim_partial_trace_v2 = claim(
    "Lemmas.lean: fill the sorry at line 209 in partial_trace_dilation by expanding "
    "U(ρ⊗|0⟩⟨0|)U† using U's column structure (hU_col : U restricted to |0⟩ column = V) "
    "and applying partialTraceR. Show the right-hand factor traces out to give Σ_k K_k ρ K_k†.",
    prior=0.4,
    metadata={
        "prior_justification": "Direct algebraic identity once hU_col is unfolded. Uses partialTraceR definition + linearity + tensor algebra.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.partial_trace_dilation",
            "subgoal": "fill sorry at line 209 by expanding via hU_col + partialTraceR",
            "sorry_line": 209,
            "mcp_search_hints": ["Matrix.kroneckerMap", "Matrix.trace_kronecker", "Finset.sum_mul"],
        },"action_status": "failed"
    },
action_id="act_46d3e8168dbc", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_46d3e8168dbc", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

claim_kraus_tp_v2 = claim(
    "Lemmas.lean: fill the sorry at line 73 in kraus_tp_from_choi_trace by deriving "
    "Σ_k K_k† K_k = I from the Choi trace-preservation condition Tr_E[Choi(Φ)] = I_Q and "
    "the spectral decomposition Choi(Φ) = Σ_k |vec K_k⟩⟨vec K_k|. Uses vecToKraus reshaping "
    "and finProdFinEquiv index bijection.",
    prior=0.3,
    metadata={
        "prior_justification": "Choi-Kraus algebra; requires reshaping + partial trace bookkeeping. Less direct than the unitary extension but mechanical once helpers are in place.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.kraus_tp_from_choi_trace",
            "subgoal": "fill sorry at line 73 via Choi trace identity",
            "sorry_line": 73,
            "mcp_search_hints": ["Matrix.trace_kronecker", "Matrix.PosSemidef.spectralTheorem", "finProdFinEquiv"],
        },"action_status": "failed"
    },
action_id="act_ec95a13e8fca", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_ec95a13e8fca", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

claim_kraus_channel_v2 = claim(
    "Lemmas.lean: fill the sorry at line 84 in kraus_channel_from_choi by deriving "
    "Φ(X) = Σ_k K_k X K_k† from the Choi spectral decomposition. Unfold Choi matrix definition, "
    "use spectral form Choi(Φ) = Σ_k |vec K_k⟩⟨vec K_k|, and derive Kraus action via vectorization.",
    prior=0.3,
    metadata={
        "prior_justification": "Core Choi-Kraus correspondence; uses vec/unvec identity vec(AXB) = (B^T ⊗ A) vec(X).",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.kraus_channel_from_choi",
            "subgoal": "fill sorry at line 84 via vec/unvec + Choi spectral form",
            "sorry_line": 84,
            "mcp_search_hints": ["Matrix.kroneckerMap", "Matrix.vecMulVec", "Matrix.PosSemidef.spectralTheorem"],
        },"action_status": "failed"
    },
action_id="act_1f08be1e89ba", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_1f08be1e89ba", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

claim_fix_isometry_signature = claim(
    "Lemmas.lean: fix the ill-typed signature of isometry_extends_to_unitary (line 455-461). "
    "The current hU_col has type mismatch: j : Fin 1 but kraus_isometry_map returns Matrix (Fin d × Fin r) (Fin 1). "
    "Repair to: ∀ (i : Fin d), U (i, 0) = column vector from kraus_isometry_map K (Pi.single i 1), "
    "and add [NeZero r] instance to allow (i, 0) construction.",
    prior=0.7,
    metadata={
        "prior_justification": "Signature fix is mechanical type repair; blocker is well-documented in code comments.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.isometry_extends_to_unitary",
            "subgoal": "fix signature type error at line 455-461",
            "blocker": "hU_col type mismatch: j : Fin 1 vs Matrix row index Fin d × Fin r",
            "mcp_search_hints": ["Orthonormal.exists_orthonormalBasis_extension", "OrthonormalBasis", "EuclideanSpace"],
        },"action_status": "failed"
    },
action_id="act_e5d095ae5aa5", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_e5d095ae5aa5", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

claim_complete_isometry_proof = claim(
    "Lemmas.lean: complete the proof of isometry_extends_to_unitary (line 543 sorry) after signature fix. "
    "Follow the commented scaffold: (1) define V as column-stacking matrix from K, "
    "(2) prove V†V = I from hTP, (3) reinterpret as orthonormal family, "
    "(4) apply Orthonormal.exists_orthonormalBasis_extension, (5) assemble U from basis.",
    prior=0.6,
    metadata={
        "prior_justification": "Proof scaffold is fully documented; Mathlib has all needed lemmas (Orthonormal.exists_orthonormalBasis_extension).",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.isometry_extends_to_unitary",
            "subgoal": "fill sorry at line 543 using Gram-Schmidt extension",
            "sorry_line": 543,
            "mcp_search_hints": ["Orthonormal.exists_orthonormalBasis_extension", "orthonormal_iff_ite", "OrthonormalBasis.toMatrix"],
        },"action_status": "failed"
    },
action_id="act_b348db79b5f8", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_b348db79b5f8", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

claim_complete_partial_trace = claim(
    "Lemmas.lean: complete the proof of partial_trace_dilation (line 607 sorry). "
    "Unfold partialTraceR, expand U M U† entry-wise, collapse kronecker |0⟩⟨0| to p=q=0, "
    "apply hU_col to rewrite U entries as Kraus operators, match RHS Σ_k K_k ρ K_k†.",
    prior=0.5,
    metadata={
        "prior_justification": "Proof strategy is documented; depends on fixed hU_col signature from isometry_extends_to_unitary.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.partial_trace_dilation",
            "subgoal": "fill sorry at line 607 via partial trace expansion",
            "sorry_line": 607,
            "depends_on": "act_e5d095ae5aa5",
            "mcp_search_hints": ["partialTraceR", "Matrix.kroneckerMap", "vecMulVec"],
        },"action_status": "failed"
    },
action_id="act_ac4fd742790b", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_ac4fd742790b", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

# iter-4: sever the A3→A2.Forward cut at Lemmas.lean:370.
# Root blocker (per TERMINAL.stuck.iter3.md): kraus_decomposition currently calls
# `choi_psd_of_cp Φ hCP` from forbidden sibling A2.Forward, which has 2 compile
# errors. We cannot fix A2 (USER_HINTS hard prohibition). Option 2 from iter-3:
# inline a direct proof of (Choi Φ).PosSemidef from IsCP Φ, then drop the
# imports of A2.Forward / A2.Reverse from Lemmas.lean.
claim_choi_psd_from_iscp_inline = claim(
    "Lemmas.lean:370: replace `choi_psd_of_cp Φ hCP` (which lives in forbidden "
    "sibling A2.Forward and currently fails to compile) with an inline proof of "
    "`(Choi Φ).PosSemidef` from `IsCP Φ`. Strategy: apply hCP with ancilla n=dK "
    "to the maximally-entangled rank-1 PSD matrix Ω(p,q) := ⟨p|q⟩ on Fin dK × Fin dK "
    "(i.e. the vec state ∑_i |i⟩|i⟩ as a density up to normalization); show Ω is "
    "PSD (rank-1, equals v vᴴ for v = ∑_i e_i ⊗ e_i); then the image matrix is "
    "definitionally Choi Φ up to index pairing. After this, delete the imports "
    "`import PhysicsLean.A2ChoiTheorem.Forward` (line 12) and "
    "`import PhysicsLean.A2ChoiTheorem.Reverse` (line 13) from Lemmas.lean and "
    "verify `lake build PhysicsLean.A3Stinespring.Theorem` returns rc=0.",
    prior=0.5,
    metadata={
        "prior_justification": "Standard Choi-PSD argument; well-known textbook construction (Nielsen-Chuang §8.2.4). Estimated ~50-100 LOC of Lean. This is the single cut that unblocks the entire A3 build.",
        "action": "deduction",
        "args": {
            "target_file": "PhysicsLean/A3Stinespring/Lemmas.lean",
            "lean_target": "PhysicsLean.A3Stinespring.Lemmas",
            "subgoal": "Inline proof of (Choi Φ).PosSemidef from IsCP Φ at line 370, then drop A2.Forward/A2.Reverse imports at lines 12-13. Witness: Ω = vecMulVec v (star v) where v : Fin dK × Fin dK → ℂ is v (i,j) = if i = j then 1 else 0 (or equivalent maximally-entangled vec). Apply hCP with n := dK, M := Ω. The Choi matrix is Φ-image of M after the obvious index pairing.",
            "cut_line": 370,
            "imports_to_drop": [12, 13],
            "termination_criterion": "lake build PhysicsLean.A3Stinespring.Theorem returns rc=0; no new axioms; no new sorries in A3 dep tree.",
            "mcp_search_hints": [
                "Matrix.PosSemidef.vecMulVec",
                "Matrix.PosSemidef of rank-one outer product",
                "maximally entangled state Mathlib",
                "Matrix.kroneckerMap PosSemidef",
            ],
        },"action_status": "failed"
    },
action_id="act_0b3efff9f35b", action_status="failed", verify_history=[{"source": "verify:lean_lake", "action_id": "act_0b3efff9f35b", "verdict": "inconclusive", "confidence": "0.400", "evidence": "lake build 失败（returncode=1），证明未完成"}])

# --- Strategy graph ---

# definitions support every downstream artifact
support(premises=[claim_defs], conclusion=claim_kraus,
        reason="Kraus extraction needs QChan, IsCP, IsTP definitions.", prior=0.9)
support(premises=[claim_defs], conclusion=claim_isometry,
        reason="Isometry construction needs StinespringData record fields.", prior=0.9)
support(premises=[claim_defs, claim_kraus], conclusion=claim_isometry,
        reason="V is built directly from the Kraus operators.", prior=0.85)
support(premises=[claim_isometry], conclusion=claim_unitary_extend,
        reason="Extension only needs that V has orthonormal columns.", prior=0.85)
support(premises=[claim_kraus, claim_unitary_extend], conclusion=claim_partial_trace,
        reason="Partial-trace identity uses both Kraus expansion and the unitary structure.", prior=0.85)

# New helper claims support the main lemmas
support(premises=[claim_kraus_tp_helper, claim_kraus_channel_helper], conclusion=claim_kraus,
        reason="kraus_decomposition theorem needs both TP condition and channel identity helpers.", prior=0.9)
support(premises=[claim_unitary_extend_proof], conclusion=claim_unitary_extend,
        reason="Filling the sorry in isometry_extends_to_unitary completes the claim.", prior=0.95)
support(premises=[claim_partial_trace_proof], conclusion=claim_partial_trace,
        reason="Filling the sorry in partial_trace_dilation completes the claim.", prior=0.95)

# v2 claims (iter-2 resume) wire into existing parents
support(premises=[claim_isometry_extend_v2], conclusion=claim_unitary_extend,
        reason="Filling sorry at L191 in isometry_extends_to_unitary directly discharges the parent claim.",
        prior=0.95)
support(premises=[claim_partial_trace_v2], conclusion=claim_partial_trace,
        reason="Filling sorry at L209 in partial_trace_dilation directly discharges the parent claim.",
        prior=0.95)
support(premises=[claim_kraus_tp_v2, claim_kraus_channel_v2], conclusion=claim_kraus,
        reason="Filling both Choi-Kraus sorries (L73, L84) closes kraus_decomposition.",
        prior=0.9)

# iter-2 signature fix and final proofs
support(premises=[claim_fix_isometry_signature], conclusion=claim_complete_isometry_proof,
        reason="Signature fix is prerequisite for completing the isometry extension proof.",
        prior=0.95)
support(premises=[claim_complete_isometry_proof], conclusion=claim_unitary_extend,
        reason="Completing the proof at line 543 closes isometry_extends_to_unitary.",
        prior=0.95)
support(premises=[claim_fix_isometry_signature, claim_complete_isometry_proof], conclusion=claim_complete_partial_trace,
        reason="partial_trace_dilation depends on well-typed hU_col from fixed isometry_extends_to_unitary.",
        prior=0.9)
support(premises=[claim_complete_partial_trace], conclusion=claim_partial_trace,
        reason="Completing the proof at line 607 closes partial_trace_dilation.",
        prior=0.95)

# iter-4 cut-sever: the inline Choi-PSD proof is a strict prerequisite for
# kraus_decomposition under the no-A2-edits constraint.
support(premises=[claim_choi_psd_from_iscp_inline], conclusion=claim_kraus,
        reason="Severing the A3→A2.Forward dependency at Lemmas.lean:370 is the "
               "one missing piece blocking lake build. Without this, "
               "kraus_decomposition cannot elaborate.",
        prior=0.95)

deduction(
    premises=[claim_defs, claim_kraus, claim_isometry, claim_unitary_extend, claim_partial_trace],
    conclusion=target,
    reason="Defs + Kraus + isometry + unitary extension + partial-trace identity assemble into the main theorem.",
    prior=0.9,
)
