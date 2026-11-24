module

public import FormalResearch.ModularBootstrap.Upper.Positivity.VacuumCore

/-!
# Proposition V: the two inputs for the designs (`ut:Vac`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, proof of Proposition V (`ut:Vac`).  For the designs
`D(N, η_*, d)` (`f = 1`, `Q = (1-q)²`), `h₀ = combProfile c' (designComb …)`, `V = cardyV (c'/12)`:

* `sig_window_pointwise`, `sig_lobe_nonpos`, `sig_integrand_props`: the same for arbitrary offsets `σs` (displaced
  sites); `design_window_pointwise`, `design_lobe_nonpos`, `design_integrand_props` are the case
  `σs = designSigma1 d`.
* `design_window_pointwise`: Lemma `W` (`lemma_W_measure`) with `ID` (`tildeW_designMod`): for large `c'`
  and `σ ∈ [-S, Φ_{N₁+1}]`, `h₀ V (dt/dσ) ≤ FK_c (C_* κ Re W(-κσ) + ε')`;
* `design_lobe_nonpos`: `h₀ V ≤ 0` for `0 < t ≤ t_S = c'(ξ_* - λ S)²/3` (`S > |σ_1|`): the negative lobe
  `x < χ'_1`, where the only real zero of `B_D` is the simple zero `χ'_1` and `V ≥ 0`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Holes
  FormalResearch.ModularBootstrap.Upper.Membership

lemma lambda_mul_le (S : ℝ) {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ c' in atTop, lambdaComb c' * S ≤ δ := by
  have h := tendsto_lambdaComb_atTop.mul_const S
  rw [zero_mul] at h
  exact h.eventually_le_const hδ

/-- `h₀(c' x²/3)` is the real part of `designProfile` at `x` (offsets `σs`). -/
lemma combProfile_sig_ofReal {c' x : ℝ} (hx : 0 ≤ x) (hc' : 0 < c') (N : ℕ) (η : ℝ) (σs : ℕ → ℝ) :
    combProfile c' (designComb c' 1 N (1 / 4) (σs) (designWidth1 c' η)) (c' * x ^ 2 / 3) =
      (designProfile c' 1 N (1 / 4) (σs) (designWidth1 c' η) (x : ℂ)).re := by
  unfold combProfile
  rw [xOf_comp hc' hx]
  rfl

lemma combProfile_design_ofReal {c' x : ℝ} (hx : 0 ≤ x) (hc' : 0 < c') (N : ℕ) (η : ℝ) (d : ℝ) :
    combProfile c' (designComb c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' η)) (c' * x ^ 2 / 3) =
      (designProfile c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' η) (x : ℂ)).re :=
  combProfile_sig_ofReal hx hc' N η (designSigma1 d)

/-- Lemma `W` with Lemma `ID` for the modifications `sigMod N η σs` (arbitrary offsets): see
`design_window_pointwise`, the case `σs = designSigma1 d`. -/
theorem sig_window_pointwise (prob : Crossing.FixedWeightProblem) (hw : prob.w = 1) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ)
    {S : ℝ} (hS : 0 ≤ S) (n1 : ℕ) {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ c' in atTop, ∀ σ ∈ Icc (-S) (phiWKB (n1 + 1)),
      combProfile c' (designComb c' 1 N (1 / 4) (σs) (designWidth1 c' η))
          (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
        prob.cardyV (c' / 12) (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
        ((2 * c' * (xiStar + lambdaComb c' * σ) / 3) * lambdaComb c') ≤
      FKc (qProb prob) 1 c' * (CStar * kappaAiry * (sigWindowW N η σs ((-kappaAiry * σ : ℝ) : ℂ)).re + ε') := by
  obtain ⟨C₀, hC₀, hW⟩ := lemma_W_measure prob
    (sigModFamily N hN hη0 hη1 σs) hS n1 ε' hε'
  filter_upwards [eventually_ge_atTop C₀, sigProfile_re_eq_modifiedH0 N hη0 hη1 σs,
    eventually_gt_atTop (0 : ℝ), lambda_mul_le S xiStar_pos] with c' hc hE2 hcpos hlam σ hσ
  have hx : 0 ≤ xiStar + lambdaComb c' * σ := by
    have h1 := hσ.1
    have := mul_le_mul_of_nonneg_left h1 (lambdaComb_pos' hcpos).le
    nlinarith
  have h := hW hc (sigMod N η σs) (sigModFamily_mem N hN hη0 hη1 σs) σ hσ
  simp only [] at h
  rw [windowMeasureNormK_eq prob hcpos, tildeW_sigMod N hN η σs σ] at h
  have hFK := FKc_pos (qProb_pos prob) 1 hcpos
  rw [combProfile_sig_ofReal hx hcpos, hE2]
  have h4 := (div_le_iff₀ hFK).mp (sub_le_iff_le_add.mp (abs_le.mp h).2)
  linarith

theorem design_window_pointwise (prob : Crossing.FixedWeightProblem) (hw : prob.w = 1) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d : ℝ)
    {S : ℝ} (hS : 0 ≤ S) (n1 : ℕ) {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ c' in atTop, ∀ σ ∈ Icc (-S) (phiWKB (n1 + 1)),
      combProfile c' (designComb c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' η))
          (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
        prob.cardyV (c' / 12) (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
        ((2 * c' * (xiStar + lambdaComb c' * σ) / 3) * lambdaComb c') ≤
      FKc (qProb prob) 1 c' * (CStar * kappaAiry * (designWindowW N η d ((-kappaAiry * σ : ℝ) : ℂ)).re + ε') :=
  by
  simp only [designWindowW_eq_sig]
  exact sig_window_pointwise prob hw N hN hη0 hη1 (designSigma1 d) hS n1 hε'

lemma xOf_le_of_le {c' t y : ℝ} (hc' : 0 < c') (hy : 0 ≤ y) (ht : t ≤ c' * y ^ 2 / 3) :
    xOf c' t ≤ y := by
  unfold xOf
  calc √(3 * t / c') ≤ √(y ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [div_le_iff₀ hc']
        nlinarith
    _ = y := Real.sqrt_sq hy

/-- `h₀ V ≤ 0` on the negative lobe `x < χ'_1` for arbitrary offsets `σs` (the pairs `2..N` are positive
whatever their position): see `design_lobe_nonpos`, the case `σs = designSigma1 d`. -/
theorem sig_lobe_nonpos (prob : Crossing.FixedWeightProblem) (N : ℕ) {η : ℝ} (σs : ℕ → ℝ) {S : ℝ}
    (hS : |σs 1| < S) :
    ∀ᶠ c' in atTop, ∀ t ∈ Ioc 0 (c' * (xiStar + lambdaComb c' * (-S)) ^ 2 / 3),
      combProfile c' (designComb c' 1 N (1 / 4) (σs) (designWidth1 c' η)) t *
        prob.cardyV (c' / 12) t ≤ 0 := by
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  have hS0 : 0 ≤ S := (abs_nonneg _).trans hS.le
  filter_upwards [h_ev, lambda_mul_le S xiStar_pos, eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (12 * prob.totalShift)] with c' ⟨_, _, _, hgap⟩ hlam hcpos hcS t ht
  have hlpos := lambdaComb_pos' hcpos
  have hy0 : 0 ≤ xiStar + lambdaComb c' * (-S) := by linarith
  have hx := xOf_le_of_le hcpos hy0 ht.2
  have hσ1 : -S < σs 1 := by
    have := neg_abs_le (σs 1)
    linarith
  have hx1 : xOf c' t < designSite c' (σs) 1 := by
    have h1 : lambdaComb c' * (-S) < lambdaComb c' * σs 1 :=
      mul_lt_mul_of_pos_left hσ1 hlpos
    unfold designSite
    linarith
  have hV : 0 ≤ prob.cardyV (c' / 12) t :=
    prob.cardyV_nonneg (by linarith) ht.1.le
  refine mul_nonpos_of_nonpos_of_nonneg ?_ hV
  have hre := designComb_re_nonpos_of_lt hcpos (by norm_num : (0 : ℝ) ≤ 1 / 4) le_rfl hgap N
    (σs) (designWidth1 c' η) (xOf_nonneg c' t) hx1
  unfold combProfile combH0
  rw [sechSqProfile_ofReal, Complex.re_ofReal_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hre

theorem design_lobe_nonpos (prob : Crossing.FixedWeightProblem) (N : ℕ) {η : ℝ} (d : ℝ) {S : ℝ}
    (hS : |designSigma1 d 1| < S) :
    ∀ᶠ c' in atTop, ∀ t ∈ Ioc 0 (c' * (xiStar + lambdaComb c' * (-S)) ^ 2 / 3),
      combProfile c' (designComb c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' η)) t *
        prob.cardyV (c' / 12) t ≤ 0 :=
  sig_lobe_nonpos prob N (designSigma1 d) hS

/-- `h₀ V` is continuous on `[0, ∞)` and integrable on `(0, ∞)` for arbitrary offsets `σs`: see
`design_integrand_props`, the case `σs = designSigma1 d`. -/
theorem sig_integrand_props (prob : Crossing.FixedWeightProblem) (hw : prob.w = 1) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, 1 ≤ k → k ≤ N → |σs k| ≤ M) :
    ∀ᶠ c' in atTop,
      ContinuousOn (fun t => combProfile c' (designComb c' 1 N (1 / 4) (σs) (designWidth1 c' η)) t *
        prob.cardyV (c' / 12) t) (Ici 0) ∧
      IntegrableOn
      (fun t => combProfile c' (designComb c' 1 N (1 / 4) (σs) (designWidth1 c' η)) t *
        prob.cardyV (c' / 12) t) (Ioi 0) := by
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  filter_upwards [sig1_k7_membership_vacuum hw N hN hη0 hη1 σs M hM,
    designComb_innerCombHyp 1 N le_rfl hN M Cg (by norm_num : (0 : ℝ) ≤ 1 / 4) le_rfl, h_ev,
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (12 * prob.totalShift)]
    with c' hK7 hInner ⟨hgap_k, hgap_1_bd, hcd1_bd, _⟩ hpos hcS
  have hI := hInner (σs) (designWidth1 c' η) (fun k hk hkN => hM k hk hkN)
    (fun k hk hkN => ⟨mul_nonneg hη0 (siteGap_nonneg hpos (by omega)), by
      have hgk := (hgap_k k (by omega)).trans (hgap_1_bd.trans hcd1_bd)
      unfold designWidth1
      calc η * siteGap c' k ≤ 1 * (Cg * lambdaComb c') :=
            mul_le_mul (hη1.trans (by norm_num)) hgk (siteGap_nonneg hpos (by omega)) (by norm_num)
        _ = Cg * lambdaComb c' := one_mul _⟩)
  obtain ⟨C, hC0, hdec, -⟩ := hK7
  have hcont := hI.continuousOn_combProfile hpos
  have hk := kernelIntegrable_of_decay (w := prob.w) prob.hw hpos hcont hdec
  exact ⟨hcont.mul (Crossing.continuous_cardyV prob (c' / 12)).continuousOn,
    integrableOn_mul_cardyV (prob := prob)
      (by linarith) hcont hk⟩

/-- `h₀ V` is continuous on `[0, ∞)` and integrable on `(0, ∞)` for the designs (decay of `h₀` and
Lemma `K7`). -/
theorem design_integrand_props (prob : Crossing.FixedWeightProblem) (hw : prob.w = 1) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d M : ℝ)
    (hM : ∀ k, 1 ≤ k → k ≤ N → |designSigma1 d k| ≤ M) :
    ∀ᶠ c' in atTop,
      ContinuousOn (fun t => combProfile c' (designComb c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' η)) t *
        prob.cardyV (c' / 12) t) (Ici 0) ∧
      IntegrableOn
      (fun t => combProfile c' (designComb c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' η)) t *
        prob.cardyV (c' / 12) t) (Ioi 0) :=
  sig_integrand_props prob hw N hN hη0 hη1 (designSigma1 d) M hM

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.sig_integrand_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sig_integrand_props

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.sig_window_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sig_window_pointwise

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.sig_lobe_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sig_lobe_nonpos

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.design_integrand_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms design_integrand_props


/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.design_window_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms design_window_pointwise

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.design_lobe_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms design_lobe_nonpos

end FormalResearch.ModularBootstrap.Upper.Positivity
