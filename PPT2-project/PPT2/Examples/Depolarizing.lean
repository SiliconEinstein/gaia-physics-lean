/-
PPT2.Examples.Depolarizing — depolarizing channel and its EB threshold.

Φ_p(ρ) = p ρ + (1-p)/d · I.  Theorem (King 2003): for d-dim
depolarizing, p ≤ 1/(d+1) implies the channel is entanglement-breaking
(the Choi matrix is in the separable cone). The threshold coincides with the
PPT threshold, hence "PPT iff EB" for depolarizing channels.

Proof structure:
  1. `choi_depolarizing_entry` — derive the entry formula for the Choi matrix
     from the definition of IsDepolarizing: Choi(Φ)_{(a,b),(c,d)} =
     p·δ_{a,b}·δ_{c,d} + ((1-p)/d)·δ_{a,c}·δ_{b,d}.
  2. The Choi matrix C_Φ = p·F + ((1-p)/d)·I where F = Σ_{i,j} |i⟩⟨j| ⊗ |i⟩⟨j|
     is the flip operator.  Its partial transpose C_Φ^{T_B} = p·SWAP + ((1-p)/d)·I
     has eigenvalues ((1-p)/d ± p); PSD when p ≤ 1/(d+1).
  3. For isotropic states (the depolarizing Choi is isotropic), the PPT
     threshold equals the separability threshold (HHHH RMP 2009 §VI.B.4).
     The general-d statement `depolarizing_choi_separable` captures this fact;
     the `d = 2` constructive specialization (closure free of project axioms
     and `sorryAx`) lives in `PPT2.Cases.Dim2` as
     `depolarizing_choi_separable_dim2`.
-/
import PPT2.Channels.Depolarizing
import PPT2.Cases.Dim2
import PPT2.Examples.MeasurePrepare
import PPT2.Examples.Dephasing
import Mathlib.Logic.Equiv.Fin.Basic

namespace PPT2

open Matrix

/-! ### p = 0 special case (fully constructive, no project axioms)

At p = 0 the depolarizing channel is `Φ(ρ) = (1/d) · Tr(ρ) · I`.  This is the
simplest measure-and-prepare channel (measure in any basis, prepare the
maximally mixed state), so its Choi matrix is separable by
`measure_prepare_is_EB`.  We unfold this for the record as a corollary that
does not depend on the `depolarizing_choi_separable` axiom — it is a proper
theorem.

Decomposition: Φ(ρ) = Σ_{(i,j) ∈ Fin d × Fin d} Tr(|j⟩⟨j| · ρ) · ((1/d)·|i⟩⟨i|).
-/

open scoped ComplexOrder in
/-- `((c : ℝ) : ℂ) • |i⟩⟨i|` is PSD for `0 ≤ c`.  Proved directly without
    invoking `PosSemidef.smul` so that we sidestep the `PosSMulMono ℂ ℂ`
    instance resolution gap. -/
lemma smul_single_posSemidef_aux {d : Nat} (i : Fin d) {c : ℝ} (hc : 0 ≤ c) :
    (((c : ℝ) : ℂ) • Matrix.single i i (1 : ℂ)).PosSemidef := by
  refine ⟨?_, ?_⟩
  · ext a b
    simp only [Matrix.smul_apply, Matrix.conjTranspose_apply, Matrix.single_apply,
      smul_eq_mul, Complex.star_def, star_mul', Complex.conj_ofReal]
    by_cases hab : i = a ∧ i = b
    · obtain ⟨rfl, rfl⟩ := hab; simp
    · have hab' : ¬ (i = b ∧ i = a) := by
        intro ⟨h1, h2⟩; exact hab ⟨h2, h1⟩
      simp [hab, hab']
  · intro x
    have hnonneg := (single_posSemidef i).2 x
    simp only [Finsupp.sum, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    simp only [Finsupp.sum, Matrix.single_apply] at hnonneg
    have hrewrite :
        (∑ a ∈ x.support, ∑ b ∈ x.support,
            star (x a) * ((c : ℂ) * (if i = a ∧ i = b then (1 : ℂ) else 0)) * x b) =
        (c : ℂ) * (∑ a ∈ x.support, ∑ b ∈ x.support,
            star (x a) * (if i = a ∧ i = b then (1 : ℂ) else 0) * x b) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intros a _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intros b _; ring
    rw [hrewrite]
    set S : ℂ := ∑ a ∈ x.support, ∑ b ∈ x.support,
        star (x a) * (if i = a ∧ i = b then (1 : ℂ) else 0) * x b
    have hS_nonneg : (0 : ℂ) ≤ S := hnonneg
    rw [Complex.nonneg_iff] at hS_nonneg ⊢
    obtain ⟨hSre, hSim⟩ := hS_nonneg
    refine ⟨?_, ?_⟩
    · simp [Complex.mul_re, ← hSim]
      exact mul_nonneg hc hSre
    · simp [Complex.mul_im, ← hSim]

open scoped ComplexOrder in
/-- `(1/d : ℂ) • |i⟩⟨i|` is PSD. -/
lemma smul_single_posSemidef_inv_d {d : Nat} (i : Fin d) :
    (((1 : ℝ) / (d : ℝ) : ℂ) • Matrix.single i i (1 : ℂ)).PosSemidef := by
  have heq : (((1 : ℝ) / (d : ℝ) : ℂ) : ℂ) = (((1 : ℝ) / (d : ℝ)) : ℝ) := by
    push_cast; ring
  rw [heq]
  apply smul_single_posSemidef_aux (c := (1 : ℝ) / (d : ℝ))
  by_cases hd : d = 0
  · subst hd; simp
  · have hd_pos : 0 < (d : ℝ) := by
      have : 0 < d := Nat.pos_of_ne_zero hd
      exact_mod_cast this
    positivity

/-- The p = 0 depolarizing channel is a measure-and-prepare channel:
    Φ(ρ) = Σ_{(i,j)} Tr(|j⟩⟨j|·ρ) · ((1/d)·|i⟩⟨i|). -/
theorem depolarizing_p0_is_mp {d : Nat} (Φ : QChan d d) (h : IsDepolarizing 0 Φ) :
    IsMeasurePrepare Φ := by
  refine ⟨d * d,
    fun ℓ =>
      let p := (finProdFinEquiv.symm ℓ : Fin d × Fin d)
      Matrix.single p.2 p.2 (1 : ℂ),
    fun ℓ =>
      let p := (finProdFinEquiv.symm ℓ : Fin d × Fin d)
      ((1 : ℝ) / (d : ℝ) : ℂ) • Matrix.single p.1 p.1 (1 : ℂ),
    ?_, ?_, ?_⟩
  · intro ℓ; exact single_posSemidef _
  · intro ℓ; exact smul_single_posSemidef_inv_d _
  · intro ρ
    rw [depolarizing_p0_apply Φ h ρ]
    have hreindex := finProdFinEquiv.sum_comp
      (fun (ℓ : Fin (d * d)) =>
        ((Matrix.single
              ((finProdFinEquiv.symm ℓ : Fin d × Fin d).2)
              ((finProdFinEquiv.symm ℓ : Fin d × Fin d).2) (1 : ℂ) * ρ).trace) •
          (((1 : ℝ) / (d : ℝ) : ℂ) •
            Matrix.single
              ((finProdFinEquiv.symm ℓ : Fin d × Fin d).1)
              ((finProdFinEquiv.symm ℓ : Fin d × Fin d).1) (1 : ℂ)))
    simp only [Equiv.symm_apply_apply] at hreindex
    rw [← hreindex]
    ext a b
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    simp_rw [trace_singleLeft_mul, Matrix.single_apply]
    rw [Fintype.sum_prod_type]
    simp_rw [show ∀ (i j : Fin d),
        ρ j j * (((1 : ℝ) / (d : ℝ) : ℂ) * (if i = a ∧ i = b then (1 : ℂ) else 0)) =
        (((1 : ℝ) / (d : ℝ) : ℂ) * ρ j j) * (if i = a ∧ i = b then (1 : ℂ) else 0)
      from by intros; ring]
    rw [show
      (∑ i : Fin d, ∑ j : Fin d,
          (((1 : ℝ) / (d : ℝ) : ℂ) * ρ j j) * (if i = a ∧ i = b then (1 : ℂ) else 0)) =
      (∑ i : Fin d,
          (if i = a ∧ i = b then (1 : ℂ) else 0) *
            (((1 : ℝ) / (d : ℝ) : ℂ) * ρ.trace))
      from by
        refine Finset.sum_congr rfl ?_; intro i _
        rw [show
          (∑ j : Fin d,
             (((1 : ℝ) / (d : ℝ) : ℂ) * ρ j j) * (if i = a ∧ i = b then (1 : ℂ) else 0)) =
          (if i = a ∧ i = b then (1 : ℂ) else 0) *
            (∑ j : Fin d, ((1 : ℝ) / (d : ℝ) : ℂ) * ρ j j)
          from by rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intros; ring]
        rw [← Finset.mul_sum]; rfl]
    rw [Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      rw [Finset.sum_eq_single a]
      · simp
      · intro i _ hia; simp [hia]
      · intro h; exact absurd (Finset.mem_univ a) h
    · have hzero : ∀ (i : Fin d) (_ : i ∈ Finset.univ),
          (if i = a ∧ i = b then (1 : ℂ) else 0) *
            (((1 : ℝ) / (d : ℝ) : ℂ) * ρ.trace) = 0 := by
        intro i _
        have : ¬ (i = a ∧ i = b) := by
          rintro ⟨h1, h2⟩; exact hab (h1.symm.trans h2)
        simp [this]
      rw [Finset.sum_eq_zero hzero]
      simp [hab]

/-- **Theorem (p = 0, fully constructive).** For the d-dimensional depolarizing
    channel with p = 0, the Choi matrix is separable.  Reduction to
    `measure_prepare_is_EB`; does *not* depend on the project axiom
    `depolarizing_choi_separable`. -/
theorem depolarizing_choi_separable_p0 {d : Nat} (Φ : QChan d d)
    (h : IsDepolarizing 0 Φ) : Separable (Choi Φ) := by
  have hMP : IsMeasurePrepare Φ := depolarizing_p0_is_mp Φ h
  exact measure_prepare_is_EB Φ hMP

/-- Project-level result (source: HHHH RMP 2009 §VI.B.4; King 2003 J. Math. Phys. 43, 4641):
    For the d-dimensional depolarizing channel with noise parameter `p ∈ [0, 1/(d+1)]`,
    the Choi matrix is separable.

    For `d = 2` the constructive proof is delivered by
    `PPT2.depolarizing_choi_separable_dim2` (in `PPT2.Cases.Dim2`), whose closure
    is `{propext, Classical.choice, Quot.sound}` — fully `sorryAx`-free.

    For `p = 0` (any `d`) the constructive proof is delivered by
    `depolarizing_choi_separable_p0`, which routes through
    `measure_prepare_is_EB`.

    Remaining `sorry`: `d ≥ 3 ∧ p > 0` (King 2003 twirling infrastructure).

    **Signature change:** `(hp0 : 0 ≤ p)` added — `IsDepolarizing` does *not*
    imply `p ≥ 0` (a maximally-mixed channel is `IsDepolarizing 0`, but no
    positivity constraint is bundled in the predicate), and the dim-2
    constructive proof requires `p ≥ 0` for the convex-combination weights. -/
theorem depolarizing_choi_separable {d : Nat} (p : ℝ) (Φ : QChan d d)
    (_hp0 : 0 ≤ p) (_hp : p ≤ 1 / (d + 1 : ℝ)) (_hdep : IsDepolarizing p Φ) :
    Separable (Choi Φ) := by
  by_cases hd : d = 2
  · subst hd
    have hp13 : p ≤ 1 / 3 := by linarith
    exact depolarizing_choi_separable_dim2 p Φ _hp0 hp13 _hdep
  · by_cases hp_eq : p = 0
    · subst hp_eq
      exact depolarizing_choi_separable_p0 Φ _hdep
    · sorry -- d ≥ 3 ∧ p > 0 fallback (King 2003; requires twirling infrastructure)

/-- Main theorem (King 2003): for the d-dim depolarizing channel,
    p ∈ [0, 1/(d+1)] is sufficient for the channel to be entanglement-breaking.

    Proof: by `depolarizing_choi_separable`, the Choi matrix is separable,
    which is the definition of IsEB.

    **Signature change:** added `(hp0 : 0 ≤ p)` to match the strengthened
    hypothesis on `depolarizing_choi_separable` (see its docstring). -/
theorem depolarizing_below_threshold_implies_eb
    {d : Nat} (p : ℝ) (Φ : QChan d d)
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / (d + 1 : ℝ)) (h : IsDepolarizing p Φ) : IsEB Φ := by
  unfold IsEB
  exact depolarizing_choi_separable p Φ hp0 hp h

/-- Depolarizing EB threshold: the theorem restated as a top-level entry point.
    Supersedes the former axiom of the same name. -/
theorem depolarizing_EB_threshold {d : Nat} (p : ℝ) (Φ : QChan d d)
    (_hp0 : 0 ≤ p) (_hp : p ≤ 1 / (d + 1 : ℝ)) (_h : IsDepolarizing p Φ) : IsEB Φ :=
  depolarizing_below_threshold_implies_eb p Φ _hp0 _hp _h

end PPT2
