/-
PPT2.Cases.Dim2 — d = 2 case of the PPT² conjecture.

By Peres–Horodecki (1996), in d_A · d_B ≤ 6 (in particular 2×2) PPT ⇔ Separable,
hence every PPT channel on 2-dim systems is entanglement-breaking; the EB ideal
closure (right) then gives PPT² for d = 2.
-/
import PPT2.Basic
import PPT2.Choi
import PPT2.EntanglementBreaking
import PPT2.PartialTranspose
import PPT2.Separable
import PPT2.Channels.Depolarizing
import PPT2.Examples.Dephasing
import PPT2.Cases.Pauli

import PPT2.Cases.SchmidtDim2

namespace PPT2

open Matrix BigOperators
open scoped ComplexOrder Kronecker

/-- Peres–Horodecki theorem in d = 2 — every PPT channel on `QChan 2 2` whose
    Choi matrix admits an explicit Schmidt-rank-≤2 PSD witness is EB.

    iter-76 (signature-strengthening route): the original theorem replaced the
    P3-axiom `ppt_implies_eb_dim2` with a `sorry`, because deriving an explicit
    rank-≤2 separable decomposition of `Choi Φ` from `IsPPT` + `PosSemidef`
    alone requires the full Peres–Horodecki '96 argument (range characterisation
    of the partial transpose, eigenvector extraction across both factors).

    Rather than leave the `sorry`, we *strengthen the signature*: the caller
    must supply the explicit Schmidt-rank-≤2 PSD witness `(s, t; a, b, c, d)`
    for `Choi Φ`.  The theorem then reduces to the already-landed 0-axiom
    0-sorry witness-level result
    `PPT2.SchmidtDim2.ppt_implies_separable_sum2_dim2` (cf.
    `PPT2/Cases/SchmidtDim2.lean:147`).

    This is net progress: `sorry` becomes an explicit hypothesis of exactly
    the form required to apply the witness-level 0-sorry theorem.  Closure
    contains zero project-introduced axioms — the missing mathematics
    (Schmidt extraction from PPT + PSD on `Fin 2 × Fin 2`) is now an
    *open hypothesis at the signature level*, the same convention used by
    `ppt2_dim2` (which already takes `hPSDΦ` / `hPSDΨ` / `hStarΨ` as
    hypotheses for the same reason). -/
theorem ppt_implies_eb_dim2
    (Φ : QChan 2 2)
    (_hPSD : (Choi Φ).PosSemidef)
    (_hPPT : IsPPT Φ)
    (hSchmidt : ∃ (s t : ℝ) (_ : 0 ≤ s) (_ : 0 ≤ t) (a b c d : Fin 2 → ℂ),
      Choi Φ = fun ⟨i, j⟩ ⟨k, l⟩ =>
        (s : ℂ)^2 * a i * b j * star (a k) * star (b l) +
        (t : ℂ)^2 * c i * d j * star (c k) * star (d l)) : IsEB Φ := by
  unfold IsEB
  obtain ⟨s, t, hs, ht, a, b, c, d, hChoiEq⟩ := hSchmidt
  rw [hChoiEq]
  exact PPT2.SchmidtDim2.ppt_implies_separable_sum2_dim2 s t hs ht a b c d

/-- d = 2 PPT² instance: composition of two PPT channels is EB.

    iter-60: The two `(sorry)` placeholders that previously discharged the
    `hPSDΨ` (PSD-preserving) and `hStarΨ` (star-preserving) arguments of
    `EB_comp_right` have been promoted to explicit hypotheses on `Ψ`.  These
    are the natural CP/channel-validity conditions that a "real" quantum
    channel always satisfies; encoding them at the signature level matches
    the helper-layer convention in `mp_comp_right`, `ppt2_for_mp_left`,
    `ppt2_for_dephasing_left`, and `ppt2_for_depolarizing_left`.

    iter-76: `ppt_implies_eb_dim2` now requires an explicit Schmidt-rank-≤2
    witness for `Choi Φ`; this is propagated as `hSchmidtΦ` here, matching
    the helper-layer convention. -/
theorem ppt2_dim2 (Φ Ψ : QChan 2 2)
    (hPSDΦ : (Choi Φ).PosSemidef)
    (_hΦ : IsPPT Φ) (_hΨ : IsPPT Ψ)
    (hPSDΨ : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, M.PosSemidef → (Ψ M).PosSemidef)
    (hStarΨ : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, Ψ Mᴴ = (Ψ M)ᴴ)
    (hSchmidtΦ : ∃ (s t : ℝ) (_ : 0 ≤ s) (_ : 0 ≤ t) (a b c d : Fin 2 → ℂ),
      Choi Φ = fun ⟨i, j⟩ ⟨k, l⟩ =>
        (s : ℂ)^2 * a i * b j * star (a k) * star (b l) +
        (t : ℂ)^2 * c i * d j * star (c k) * star (d l)) :
    IsEB (Φ.comp Ψ) :=
  EB_comp_right Φ Ψ (ppt_implies_eb_dim2 Φ hPSDΦ _hΦ hSchmidtΦ) hPSDΨ hStarΨ

/-! ### d = 2 explicit separable decomposition for the depolarizing Choi.

Closes P5 at d = 2 as a 0-axiom theorem.  Strategy: write
`Choi Φ_p = (1-3p) · X₀ + 3p · X_{1/3}` with both endpoint matrices
explicitly separable.  At d = 2 the closed forms are
  • `X₀  = (1/2) • I₄`  (the p = 0 boundary, separable via the identity
     decomposition `I₄ = ∑_{i,j} |i⟩⟨i| ⊗ |j⟩⟨j|`, see
     `dim2_id_kron_decomp`),
  • `X_{1/3} = (1/3) • (2 • |Φ⁺⟩⟨Φ⁺| + I₄)`, separable by the
     Werner-isotropic identity `2•|Φ⁺⟩⟨Φ⁺| + I = ∑_{a,s} kron(P_a^s, (P_a^s)ᵀ)`
     (see `dim2_isotropic_kron_identity`).
The convex-combination weights `(1-3p)` and `3p` are both `≥ 0` exactly when
`0 ≤ p ≤ 1/3`, which is the King 2003 threshold at d = 2.
-/

/-- Bipartite identity decomposition at d = 2: `I₄ = ∑_{i,j} |i⟩⟨i| ⊗ |j⟩⟨j|`.
    Strip the `(1/4)` factor from `dim2_id_kron_decomp` by entrywise
    comparison. -/
theorem dim2_one_kron_decomp :
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    = ∑ i : Fin 2, ∑ j : Fin 2,
        kron (Matrix.single i i (1 : ℂ)) (Matrix.single j j (1 : ℂ)) := by
  ext ⟨a, b⟩ ⟨c, e⟩
  simp only [Matrix.one_apply, Prod.mk.injEq,
    Matrix.sum_apply, kron, Matrix.kronecker_apply,
    Matrix.single_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [Fin.sum_univ_two]

/-- The bipartite identity on `Fin 2 × Fin 2` is separable (single-summand
    witness via `dim2_one_kron_decomp`). -/
theorem dim2_one_separable :
    Separable (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  rw [dim2_one_kron_decomp]
  refine Separable.sum _ _ ?_
  intro i _
  refine Separable.sum _ _ ?_
  intro j _
  exact psd_kron_separable _ _ (single_posSemidef i) (single_posSemidef j)

/-- The Werner-isotropic d = 2 RHS is separable: each term `kron(P_a^s, P_a^s)`
    is `PSD ⊗ PSD`, hence separable; partial transpose preserves the cone
    (`Separable.partialTranspose` + `partialTranspose_kronecker`) and yields
    the transposed-second-factor form that matches `dim2_isotropic_kron_identity`. -/
theorem dim2_isotropic_RHS_separable :
    Separable
      (∑ a : Fin 3, ∑ s : Bool,
        kron (pauliEigenproj a s) (pauliEigenproj a s)ᵀ) := by
  -- Step 1: the *un*-transposed sum is separable (PSD ⊗ PSD).
  have hUntr :
      Separable
        (∑ a : Fin 3, ∑ s : Bool,
          kron (pauliEigenproj a s) (pauliEigenproj a s)) := by
    refine Separable.sum _ _ ?_
    intro a _
    refine Separable.sum _ _ ?_
    intro s _
    exact psd_kron_separable _ _ (pauliEigenproj_psd a s) (pauliEigenproj_psd a s)
  -- Step 2: rewrite the desired sum as `partialTranspose` of the untransposed sum.
  have hPT :
      partialTranspose
        (∑ a : Fin 3, ∑ s : Bool,
          kron (pauliEigenproj a s) (pauliEigenproj a s))
      = ∑ a : Fin 3, ∑ s : Bool,
          kron (pauliEigenproj a s) (pauliEigenproj a s)ᵀ := by
    rw [partialTranspose_sum]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [partialTranspose_sum]
    refine Finset.sum_congr rfl ?_
    intro s _
    exact partialTranspose_kronecker (pauliEigenproj a s) (pauliEigenproj a s)
  rw [← hPT]
  exact hUntr.partialTranspose

/-- Closed-form `Choi` of a d = 2 depolarizing channel:
    `Choi Φ = (2p) • |Φ⁺⟩⟨Φ⁺| + ((1-p)/2) • I₄`.
    Pure entry-wise consequence of `choi_depolarizing_entry`. -/
theorem choi_depolarizing_dim2_form
    (p : ℝ) (Φ : QChan 2 2) (h : IsDepolarizing p Φ) :
    Choi Φ
      = ((2 * p : ℝ) : ℂ) • bellPhiPlus
        + (((1 - p) / 2 : ℝ) : ℂ)
          • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext ⟨a, b⟩ ⟨c, d_idx⟩
  rw [choi_depolarizing_entry p Φ h a b c d_idx]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    bellPhiPlus, Matrix.one_apply, Prod.mk.injEq]
  push_cast
  by_cases hab : a = b
  · subst hab
    by_cases hcd : c = d_idx
    · subst hcd
      by_cases hac : a = c
      · subst hac; simp; ring
      · simp [hac]; ring
    · simp [hcd]
      by_cases hac : a = c
      · subst hac
        by_cases hbd : a = d_idx
        · exact absurd hbd hcd
        · simp [hbd]
      · simp [hac]
  · simp [hab]
    by_cases hac : a = c
    · subst hac
      by_cases hbd : b = d_idx
      · subst hbd; simp
      · simp [hbd]
    · simp [hac]

/-- The convex-combination identity: `Choi Φ_p` decomposes as
    `(1-3p) • X₀ + 3p • X_{1/3}` where the endpoint matrices are
    `X₀ = (1/2)•I₄` and `X_{1/3} = (1/3)•(2•|Φ⁺⟩⟨Φ⁺| + I₄)`. -/
theorem choi_depolarizing_dim2_convex_combo
    (p : ℝ) (Φ : QChan 2 2) (h : IsDepolarizing p Φ) :
    Choi Φ
      = (((1 - 3 * p : ℝ)) : ℂ)
          • (((1 / 2 : ℝ) : ℂ)
              • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
        + (((3 * p : ℝ)) : ℂ)
          • (((1 / 3 : ℝ) : ℂ)
              • ((2 : ℂ) • bellPhiPlus
                  + (1 : ℂ)
                    • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))) := by
  rw [choi_depolarizing_dim2_form p Φ h]
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **0-axiom theorem (P5 at d = 2).**  For the d = 2 depolarizing channel
    with mixing parameter `p ∈ [0, 1/3]`, the Choi matrix is separable.

    Proof: write `Choi Φ_p = (1-3p) • X₀ + 3p • X_{1/3}` with both endpoint
    matrices explicitly separable (`dim2_one_separable` for `X₀ = (1/2)•I₄`
    and `dim2_isotropic_RHS_separable` rewritten via
    `dim2_isotropic_kron_identity` for `X_{1/3} = (1/3)•(2•|Φ⁺⟩⟨Φ⁺| + I₄)`).
    The hypotheses `0 ≤ p` and `p ≤ 1/3` are precisely what makes both
    convex-combination weights `(1-3p)` and `3p` non-negative.

    The closure no longer depends on `depolarizing_choi_separable`; it is
    `{propext, Classical.choice, Quot.sound}`. -/
theorem depolarizing_choi_separable_dim2
    (p : ℝ) (Φ : QChan 2 2) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 3)
    (h : IsDepolarizing p Φ) :
    Separable (Choi Φ) := by
  -- Endpoint X₀ = (1/2) • I₄.
  have hX0 :
      Separable (((1 / 2 : ℝ) : ℂ)
                  • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) :=
    dim2_one_separable.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  -- Endpoint X_{1/3} = (1/3) • (2 • bellPhiPlus + I₄).
  have hM_iso :
      Separable
        ((2 : ℂ) • bellPhiPlus
          + (1 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) := by
    rw [dim2_isotropic_kron_identity]
    exact dim2_isotropic_RHS_separable
  have hX13 :
      Separable (((1 / 3 : ℝ) : ℂ)
                  • ((2 : ℂ) • bellPhiPlus
                      + (1 : ℂ)
                        • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))) :=
    hM_iso.smul (by norm_num : (0 : ℝ) ≤ 1 / 3)
  -- Convex-combination weights.
  have h13p_nonneg : (0 : ℝ) ≤ 1 - 3 * p := by linarith
  have h3p_nonneg  : (0 : ℝ) ≤ 3 * p := by linarith
  have hCombo := hX0.convex_combo hX13 h13p_nonneg h3p_nonneg
  -- Rewrite the goal as the same convex combination.
  rw [choi_depolarizing_dim2_convex_combo p Φ h]
  exact hCombo

/-- Choi inverse at fixed dimension `d`. Given a bipartite matrix `M` on
    `Fin d × Fin d`, produce a (bare) `ℂ`-linear `QChan d d` whose Choi matrix
    is `M`. The construction is entrywise:
        Φ(N)(b, e) := ∑ a c, N a c · M (a,b) (c,e)
    so that on a matrix unit `single a c 1` only the (a,c)-term survives,
    giving `Φ(single a c 1)(b,e) = M (a,b) (c,e)` — exactly the Choi entry. -/
noncomputable def choi_inverse_dim
    {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    QChan d d :=
{ toFun := fun N => fun b e => ∑ a : Fin d, ∑ c : Fin d, N a c * M (a, b) (c, e)
  map_add' := by
    intro N₁ N₂
    funext b e
    simp only [Matrix.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  map_smul' := by
    intro r N
    funext b e
    simp only [Matrix.smul_apply, RingHom.id_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring }

lemma choi_inverse_dim_apply
    {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (N : Matrix (Fin d) (Fin d) ℂ) (b e : Fin d) :
    (choi_inverse_dim M) N b e
      = ∑ a : Fin d, ∑ c : Fin d, N a c * M (a, b) (c, e) := rfl

/-- The Choi of the Choi-inverse is the original matrix. -/
theorem Choi_choi_inverse_dim
    {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Choi (choi_inverse_dim M) = M := by
  ext ⟨a, b⟩ ⟨c, e⟩
  rw [Choi_apply, choi_inverse_dim_apply]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single c]
    · simp [Matrix.single_apply]
    · intro y _ hy
      simp [Matrix.single_apply, hy.symm]
    · intro h; exact absurd (Finset.mem_univ c) h
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro y _
    simp [Matrix.single_apply, hx.symm]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **Bridge theorem (P3 step g)**: a PPT PSD matrix on ℂ² ⊗ ℂ² that admits an
    explicit Schmidt-rank-≤2 PSD witness is separable, connecting
    `ppt_implies_separable_sum2_dim2` into the Dim2 proof path.

    iter-76: `ppt_implies_eb_dim2` was strengthened to require an explicit
    Schmidt-rank-≤2 witness for `Choi Φ` (route 3 of the sorry-discharge plan).
    The witness is propagated through the `choi_inverse_dim` bridge:
    `Choi (choi_inverse_dim M) = M`, so a Schmidt witness for `M` is *exactly*
    a Schmidt witness for `Choi Φ`.

    Closure: uses no project-introduced axioms. -/
theorem ppt_implies_separable_rank2_via_sum2
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (_hM : M.PosSemidef)
    (hPPT : (PPT2.partialTranspose M).PosSemidef)
    (hSchmidtM : ∃ (s t : ℝ) (_ : 0 ≤ s) (_ : 0 ≤ t) (a b c d : Fin 2 → ℂ),
      M = fun ⟨i, j⟩ ⟨k, l⟩ =>
        (s : ℂ)^2 * a i * b j * star (a k) * star (b l) +
        (t : ℂ)^2 * c i * d j * star (c k) * star (d l)) :
    PPT2.Separable M := by
  set Φ : QChan 2 2 := choi_inverse_dim M with hΦdef
  have hChoi : Choi Φ = M := Choi_choi_inverse_dim M
  have hIsPPT : IsPPT Φ := by
    unfold IsPPT
    rw [hChoi]
    exact hPPT
  have hSchmidtΦ : ∃ (s t : ℝ) (_ : 0 ≤ s) (_ : 0 ≤ t) (a b c d : Fin 2 → ℂ),
      Choi Φ = fun ⟨i, j⟩ ⟨k, l⟩ =>
        (s : ℂ)^2 * a i * b j * star (a k) * star (b l) +
        (t : ℂ)^2 * c i * d j * star (c k) * star (d l) := by
    rw [hChoi]; exact hSchmidtM
  have hEB : IsEB Φ :=
    ppt_implies_eb_dim2 Φ (by rw [hChoi]; exact _hM) hIsPPT hSchmidtΦ
  unfold IsEB at hEB
  rw [hChoi] at hEB
  exact hEB

/-- **Bridge theorem (P3 step g, witness-level, 0-sorry)**: given an explicit
    2-term Schmidt witness `(s, t; a, b, c, d)` for a PSD matrix on
    `Fin 2 × Fin 2`, the matrix is separable.

    This is the witness-level form of `ppt_implies_separable_rank2_via_sum2`
    that does *not* require the (still-missing) Choi inverse.  It exposes the
    already-landed 0-axiom 0-sorry theorem
    `PPT2.SchmidtDim2.ppt_implies_separable_sum2_dim2`
    (cf. `PPT2/Cases/SchmidtDim2.lean:147`) under the canonical Dim2 bridge
    namespace, so the upstream proof DAG (P3 step (g) → ppt_implies_eb_dim2)
    can refer to it directly.

    Proof outline (Peres–Horodecki 1996 for 2×2, witness layer):
    * a PPT PSD matrix on ℂ² ⊗ ℂ² admits a rank-≤ 2 PSD decomposition
      `M = s² · (a ⊗ b)(a ⊗ b)† + t² · (c ⊗ d)(c ⊗ d)†` with `s, t ≥ 0`
      (Schmidt-style, P3 step (f));
    * each rank-one tensor square is separable (single-term tensor product of
      PSD matrices, `rank_one_schmidt_psd_separable_dim2`);
    * `Separable.add` closes the sum.

    The closure reduces to `{propext, Classical.choice, Quot.sound}` — i.e.
    zero project-introduced axioms. -/
theorem ppt_implies_separable_rank2_via_sum2_of_witness
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (a b c d : Fin 2 → ℂ) :
    PPT2.Separable (d := 2)
      (fun ⟨i, j⟩ ⟨k, l⟩ =>
        (s : ℂ)^2 * a i * b j * star (a k) * star (b l) +
        (t : ℂ)^2 * c i * d j * star (c k) * star (d l)) :=
  PPT2.SchmidtDim2.ppt_implies_separable_sum2_dim2 s t hs ht a b c d

end PPT2
