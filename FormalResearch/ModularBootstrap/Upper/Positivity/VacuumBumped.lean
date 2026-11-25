module

public import FormalResearch.ModularBootstrap.Upper.Positivity.VacuumMain
public import FormalResearch.ModularBootstrap.Upper.Positivity.PropositionIII

/-!
# Proposition V and Lemma T for the bumped fixed designs at every weight (`ut:Vac`, `ut:T`, `fw:e3.3`, `fw:e3.6`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Lemma `T` (`ut:T`) and Proposition V (`ut:Vac`), with the
macroscopic bump of Section `fw:s1` (`R_bump`, display `fw:e3.3`; integrability and vacuum cost `fw:e3.6`).

For the `f = 1` finite modification `B_D = designComb c' 1 N (1/4) σs (designWidth1 c' η)` (the designs `D(N, η_*, d)` for
`σs = designSigma1 d`, displaced designs for other `σs`) the bumped comb `bumpSigComb d c' N N' η σs` (`Bump.bumpedComb`,
base cut `N`, cut `N' ≥ N`) is `h₀^{(p)} = R_bump · h₀` pointwise on the real axis (`Bump.bumped_value`), with
`1 ≤ R_bump ≤ C_p` and `R_bump ≤ 1 + C/c'` on `x ≤ ξ_* + r_p` (`Bump.bump_lemma`).  Everything below is stated for an
arbitrary `FixedWeightProblem` (`FK_c = FKc (qProb prob) 1 c'`, `qProb` carrying `(2 ξ_*)^{w-1}`, the test
`g_w = ½(h₀^{(p)} - 𝓗_w h₀^{(p)})` with `𝓗_w = hankelTransform prob.w`), hence at every weight, and **uniformly in the cut
`N' ≥ N`**: the thresholds in `c'` do not depend on `N'`.  The bump data `d : BumpData` is arbitrary here; for
Proposition III (positivity) it is `(rpParams (prob.w - 1)).bumpData`.

* `lemma_T_sig1_prob_mul`: Lemma `T` (`ut:T`) for the `f = 1` finite modifications at every weight with the
  multiplier hook `0 ≤ R ≤ K_b` for `R_bump` (`lemma_T_prob_mul` of `Window/Tail.lean` specialised to `f = 1`,
  `η₀ = 1/4`, `ε = designWidth1`; the far band is `fw:e3.6`, with `(1+x)^{w-1}` in place of the Peano bound);
* `sig_window_pointwise_w`: Lemma `W` + `ID` at every weight (`sig_window_pointwise` without its unused hypothesis);
* `vacuum_core_mul`: the vacuum estimate `∫_0^∞ R_i h₀ V dt ≤ FK_c (C_* V_D + ε)` for an arbitrary multiplier family
  `R_i(c', t)` with `1 ≤ R_i ≤ K_b`, `R_i ≤ 1 + C'/c'` for `x ≤ ξ_* + r`; with `R ≡ 1` it is `vacuum_core_sig`
  (whose hypothesis `prob.w = 1` is used only for integrability);
* `bumpSig_phaseHyp`, `bumpSig_k7W` (`fw:e3.4`, Lemma `K7` at every weight for the bumped combs, uniform in `N'`),
  `combProfile_bumped_eq` (value identity on the profile), `bumpSig_integrand_props`;
* `vacuum_core_bumped`: `V_c^{(p)} ≤ FK_c (C_* V_D + ε)` for the bumped designs;
* **`proposition_V_i_bumped`, `proposition_V_ii_bumped`** (and `_design`: `σs = designSigma1 d`, `V_D = windowIntegralVD`):
  Proposition V (i) `limsup (2/FK_c) ∫ Ψ_g du ≤ C_* V_D` and (ii) `V_D < 0 ⟹ g_vac ≥ π C_* |V_D| FK_c/4 > 0`, at every weight,
  with `∫ Ψ_g du := -g_vac/(2π)` (the crossing identity `integral_psiAiry_eq_neg_gVac`), as in `Positivity/Vacuum.lean`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Holes
  FormalResearch.ModularBootstrap.Upper.Membership FormalResearch.ModularBootstrap.Upper.Window.Tail

/-- **Lemma `T` for the `f = 1` finite modifications at fixed sites, every problem, every weight, with the
multiplier hook** `0 ≤ R ≤ K_b` (`R_bump ≤ C_p`, `fw:e3.3`; the Peano-type bound `fw:e3.6` is the far-band clause).
The integrand is `R(t) |h₀(t)| V(t)`, the constants absorb `K_b` and do not depend on `R`. -/
theorem lemma_T_sig1_prob_mul (prob : Crossing.FixedWeightProblem) {r₀ : ℝ} (hr₀ : 0 < r₀) (N : ℕ)
    (hN : 1 ≤ N) {etaStar : ℝ} (hη0 : 0 ≤ etaStar) (hη1 : etaStar ≤ 1 / 4) (σ : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, 1 ≤ k → k ≤ N → |σ k| ≤ M) (Kb : ℝ) (hKb : 0 ≤ Kb) :
    ∃ N₂ : ℕ, ∃ C_T C_far : ℝ, 0 ≤ C_T ∧ 0 ≤ C_far ∧ ∀ N₁ : ℕ, max 4 N₂ ≤ N₁ →
      ∀ᶠ c' in atTop, ∀ R : ℝ → ℝ, (∀ t, 0 ≤ R t ∧ R t ≤ Kb) →
        (∫ t in Icc (c' * chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3) (c' * (xiStar + r₀) ^ 2 / 3),
            R t * (|combProfile c' (designComb c' 1 N (1 / 4) σ (designWidth1 c' etaStar)) t| *
              prob.cardyV (c' / 12) t)) ≤
          FKc (qProb prob) 1 c' * C_T * (N₁ : ℝ) ^ (-(1 / 3 : ℝ)) ∧
        (∫ t in Ici (c' * (xiStar + r₀) ^ 2 / 3),
            R t * (|combProfile c' (designComb c' 1 N (1 / 4) σ (designWidth1 c' etaStar)) t| *
              prob.cardyV (c' / 12) t)) ≤ C_far * √c' := by
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  obtain ⟨N₂, C_T, C_far, hCT, hCf, h⟩ := lemma_T_prob_mul prob hr₀ 1 N le_rfl hN M Cg
    (by norm_num : (0 : ℝ) ≤ 1 / 4) le_rfl Kb hKb
  refine ⟨N₂, C_T, C_far, hCT, hCf, fun N₁ hN₁ => ?_⟩
  have hexp : -((2 / 3 : ℝ) * (2 * ((1 : ℕ) : ℝ) - 3 / 2)) = -(1 / 3 : ℝ) := by norm_num
  filter_upwards [h N₁ (by simpa using hN₁), h_ev, eventually_gt_atTop (0 : ℝ)]
    with c' hc' ⟨hgap_k, hgap_1_bd, hcd1_bd, _⟩ hpos R hR
  have key := hc' σ (designWidth1 c' etaStar) (fun k hk hkN => hM k hk hkN)
    (fun k hk hkN => ⟨mul_nonneg hη0 (siteGap_nonneg hpos (by omega)), by
      have hgk := (hgap_k k (by omega)).trans (hgap_1_bd.trans hcd1_bd)
      unfold designWidth1
      calc etaStar * siteGap c' k ≤ 1 * (Cg * lambdaComb c') :=
            mul_le_mul (hη1.trans (by norm_num)) hgk (siteGap_nonneg hpos (by omega)) (by norm_num)
        _ = Cg * lambdaComb c' := one_mul _⟩) R hR
  rw [hexp] at key
  exact key

/-- The one-sided multiplier estimate used for the window: `1 ≤ R ≤ 1 + δ`, `a ≤ b ≤ M`, `0 ≤ M` give
`R a ≤ b + δ M` (for `a ≥ 0` use `R ≤ 1 + δ`; for `a < 0` use `R ≥ 1`). -/
lemma mul_le_of_one_le_of_le {R a b δ M : ℝ} (hR1 : 1 ≤ R) (hRδ : R ≤ 1 + δ) (hδ : 0 ≤ δ)
    (hM : 0 ≤ M) (hab : a ≤ b) (hbM : b ≤ M) : R * a ≤ b + δ * M := by
  rcases le_or_gt 0 a with ha | ha
  · nlinarith only [mul_le_mul_of_nonneg_right hRδ ha, mul_le_mul_of_nonneg_left (hab.trans hbM) hδ, hab]
  · nlinarith only [mul_le_mul_of_nonneg_right hR1 (neg_nonneg.mpr ha.le), hab, mul_nonneg hδ hM]

/-- Lemma `W` with Lemma `ID` for the modifications `sigMod N η σs` at every weight (`sig_window_pointwise` with its
unused hypothesis `prob.w = 1` removed: the window limit is normalised by `FK_c`, which carries `qProb prob`). -/
theorem sig_window_pointwise_w (prob : Crossing.FixedWeightProblem) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {S : ℝ} (hS : 0 ≤ S) (n1 : ℕ) {ε' : ℝ} (hε' : 0 < ε') :
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

/-- **Vacuum core with a bounded multiplier family, every weight** (`ut:Vac` with `fw:e3.3`).  Let `R_i(c', t)`,
`i : ι`, be a family of multipliers with `1 ≤ R_i ≤ K_b` (`fw:e3.3`, first display), `R_i ≤ 1 + C'/c'` on
`x = √(3t/c') ≤ ξ_* + r` (second display), such that `R_i h₀ V` is continuous on `[0, ∞)` and integrable on
`(0, ∞)`, where `h₀ = combProfile` of the `f = 1` finite modification with offsets `σs`.  Then for every
`ε > 0` and `c'` large, uniformly in `i`, `∫_0^∞ R_i h₀ V dt ≤ FK_c (C_* V_D + ε)`, `V_D = windowIntegralSig`.
For `prob.w = 1` and `R ≡ 1` this is `vacuum_core_sig`. -/
theorem vacuum_core_mul (prob : Crossing.FixedWeightProblem) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {ι : Type*} (Rm : ι → ℝ → ℝ → ℝ)
    {Kb C' r : ℝ} (hKb : 0 ≤ Kb) (hC' : 0 ≤ C') (hr : 0 < r)
    (hR : ∀ᶠ c' in atTop, ∀ i t, 1 ≤ Rm i c' t ∧ Rm i c' t ≤ Kb)
    (hnear : ∀ᶠ c' in atTop, ∀ i t, xOf c' t ≤ xiStar + r → Rm i c' t ≤ 1 + C' / c')
    (hint : ∀ᶠ c' in atTop, ∀ i,
      ContinuousOn (fun t => Rm i c' t *
        (combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t *
          prob.cardyV (c' / 12) t)) (Ici 0) ∧
      IntegrableOn (fun t => Rm i c' t *
        (combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t *
          prob.cardyV (c' / 12) t)) (Ioi 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c' in atTop, ∀ i,
      ∫ t in Ioi 0, Rm i c' t *
          (combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t *
            prob.cardyV (c' / 12) t) ≤
        FKc (qProb prob) 1 c' * (CStar * windowIntegralSig N η σs + ε) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k, 1 ≤ k → k ≤ N → |σs k| ≤ M :=
    ⟨∑ k ∈ Finset.Icc 1 N, |σs k|, fun k hk hkN =>
      Finset.single_le_sum (f := fun j => |σs j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_Icc.mpr ⟨hk, hkN⟩)⟩
  obtain ⟨N₂, C_T, C_far, hCT, hCf, hT⟩ := lemma_T_sig1_prob_mul prob (r₀ := 3 / 10) (by norm_num) N hN
    hη0 hη1 σs M hM Kb hKb
  obtain ⟨n, hn1, hn2, hn3, hn4⟩ := (eventually_n_choice_sig N₂ (C_T := C_T) hε N hN η σs).exists
  have hn1' : 1 ≤ n := by have := (le_max_left 4 N₂).trans hn1; omega
  have hΦ0 : 0 ≤ phiWKB (n + 1) := phiWKB_nonneg (by omega)
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hwc := continuous_windowLimit_sig N hN η σs
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := -(n : ℝ)) (b := phiWKB (n + 1))).exists_bound_of_continuousOn
    hwc.continuousOn
  obtain ⟨e1, he1⟩ : ∃ e1 : ℝ, e1 = ε / 4 / (phiWKB (n + 1) + n + 1) := ⟨_, rfl⟩
  have he1pos : 0 < e1 := by rw [he1]; positivity
  have he1le : e1 * (phiWKB (n + 1) + n) ≤ ε / 4 := by
    rw [he1, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [show 0 < ε by exact hε]
  have hMb : 0 ≤ max M₀ 0 + e1 / 2 := by positivity
  filter_upwards [sig_window_pointwise_w prob N hN hη0 hη1 σs (S := n) hnR n (half_pos he1pos),
    sig_lobe_nonpos prob N σs hn2, hT n hn1, hR, hnear, hint,
    FKc_ge_mul_sqrt_of_pos (qProb_pos prob) (C_far / (ε / 4)), lambda_mul_le (n : ℝ) (half_pos xiStar_pos),
    lambda_mul_le (phiWKB (n + 1)) (by norm_num : (0 : ℝ) < 3 / 10),
    lambda_mul_le (phiWKB (n + 1)) hr, eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (12 * prob.totalShift),
    eventually_ge_atTop (2 * C' * (max M₀ 0 + e1 / 2) / e1 + 1)]
    with c' hpw hneg hTc hRc hnc hnc' hFKbig hln hlΦ hlr hcpos hcS hcbig i
  have hxi := xiStar_pos
  have hlpos := lambdaComb_pos' hcpos
  have hFK := FKc_pos (qProb_pos prob) 1 hcpos
  obtain ⟨hcont, hint'⟩ := hnc' i
  obtain ⟨hband0, hfar0⟩ := hTc (fun t => Rm i c' t) (fun t => ⟨by linarith [(hRc i t).1], (hRc i t).2⟩)
  have ha : (1 / 4 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
    linarith
  have hχ1 : xiStar ≤ chiQuantile c' ((n + 1 : ℕ) : ℝ) := (chiQuantile_spec hcpos ha).1
  have hχ2 : chiQuantile c' ((n + 1 : ℕ) : ℝ) ≤ xiStar + lambdaComb c' * phiWKB (n + 1) := by
    have h := (siteRadius_bounds hcpos ha).2
    unfold siteRadius at h
    rw [phiWKB_eq_phiQuantile (n + 1)]
    linarith
  have hy0 : 0 ≤ xiStar + lambdaComb c' * (-(n : ℝ)) := by linarith
  have hy1 : 0 ≤ xiStar + lambdaComb c' * phiWKB (n + 1) := by
    have := mul_nonneg hlpos.le hΦ0
    linarith
  have hSΦ : c' * (xiStar + lambdaComb c' * (-(n : ℝ))) ^ 2 / 3 ≤
      c' * (xiStar + lambdaComb c' * phiWKB (n + 1)) ^ 2 / 3 := by
    have h1 : xiStar + lambdaComb c' * (-(n : ℝ)) ≤ xiStar + lambdaComb c' * phiWKB (n + 1) := by
      have := mul_le_mul_of_nonneg_left (show -(n : ℝ) ≤ phiWKB (n + 1) by linarith) hlpos.le
      linarith
    have := pow_le_pow_left₀ hy0 h1 2
    nlinarith only [mul_le_mul_of_nonneg_left this hcpos.le]
  have hNΦ : c' * chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2 / 3 ≤
      c' * (xiStar + lambdaComb c' * phiWKB (n + 1)) ^ 2 / 3 := by
    have := pow_le_pow_left₀ (by linarith) hχ2 2
    nlinarith only [mul_le_mul_of_nonneg_left this hcpos.le]
  have hΦR : c' * (xiStar + lambdaComb c' * phiWKB (n + 1)) ^ 2 / 3 ≤ c' * (xiStar + 3 / 10) ^ 2 / 3 := by
    have := pow_le_pow_left₀ hy1 (show xiStar + lambdaComb c' * phiWKB (n + 1) ≤ xiStar + 3 / 10 by linarith) 2
    nlinarith only [mul_le_mul_of_nonneg_left this hcpos.le]
  set F : ℝ → ℝ := fun t => Rm i c' t *
    (combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t * prob.cardyV (c' / 12) t) with hF
  have hneg' : ∀ t ∈ Ioc 0 (c' * (xiStar + lambdaComb c' * (-(n : ℝ))) ^ 2 / 3), F t ≤ 0 := by
    intro t ht
    have h1 := (hRc i t).1
    have h2 := hneg t ht
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) h2
  have hN0 : 0 < c' * chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2 / 3 := by
    have := lt_of_lt_of_le hxi hχ1
    positivity
  have hS0 : 0 ≤ c' * (xiStar + lambdaComb c' * (-(n : ℝ))) ^ 2 / 3 := by positivity
  have hsplit := split_integral_le (F := F) hS0 hN0 hSΦ hNΦ hΦR hint' hneg'
  have hδ : C' / c' * (max M₀ 0 + e1 / 2) ≤ e1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hcpos]
    have h1 : 2 * C' * (max M₀ 0 + e1 / 2) / e1 ≤ c' := by linarith
    have h2 := (div_le_iff₀ he1pos).mp h1
    nlinarith only [h2]
  have hwin := window_part_le (c' := c') (FK := FKc (qProb prob) 1 c') (ε' := e1) (S := (n : ℝ))
    (Φ := phiWKB (n + 1)) hcpos.le hcont hwc (by linarith) (fun σ hσ => by
      have hx : 0 ≤ xiStar + lambdaComb c' * σ := by
        have h1 := mul_le_mul_of_nonneg_left hσ.1 hlpos.le
        have h2 : lambdaComb c' * (-(n : ℝ)) = -(lambdaComb c' * n) := mul_neg _ _
        linarith
      have hxr : xiStar + lambdaComb c' * σ ≤ xiStar + r := by
        have h1 := mul_le_mul_of_nonneg_left hσ.2 hlpos.le
        linarith
      have hRn := hnc i (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3)
        (by rw [xOf_comp hcpos hx]; exact hxr)
      have hRb := hRc i (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3)
      have hb := hpw σ hσ
      have hwσ : tildeW 1 (sigMod N η σs).sigmaFLim (sigMod N η σs).allSigmaLim
          (sigMod N η σs).allEpsLim σ ≤ max M₀ 0 := by
        have := hM₀ σ hσ
        exact (le_abs_self _).trans (this.trans (le_max_left _ _))
      rw [tildeW_sigMod N hN η σs σ] at hwσ ⊢
      have hbM : FKc (qProb prob) 1 c' * (CStar * kappaAiry * (sigWindowW N η σs ((-kappaAiry * σ : ℝ) : ℂ)).re + e1 / 2) ≤
          FKc (qProb prob) 1 c' * (max M₀ 0 + e1 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hFK.le
      have key := mul_le_of_one_le_of_le hRb.1 hRn (div_nonneg hC' hcpos.le)
        (mul_nonneg hFK.le hMb) hb hbM
      have e : Rm i c' (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
          (combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η))
            (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
            prob.cardyV (c' / 12) (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3)) *
          ((2 * c' * (xiStar + lambdaComb c' * σ) / 3) * lambdaComb c') =
          Rm i c' (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
          (combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η))
            (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
            prob.cardyV (c' / 12) (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
            ((2 * c' * (xiStar + lambdaComb c' * σ) / 3) * lambdaComb c')) := by ring
      rw [e]
      refine key.trans ?_
      have h3 : C' / c' * (FKc (qProb prob) 1 c' * (max M₀ 0 + e1 / 2)) =
          FKc (qProb prob) 1 c' * (C' / c' * (max M₀ 0 + e1 / 2)) := by ring
      nlinarith only [h3, mul_le_mul_of_nonneg_left hδ hFK.le])
  have hband : (∫ t in Icc (c' * chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2 / 3) (c' * (xiStar + 3 / 10) ^ 2 / 3),
      |Rm i c' t * (combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t *
        prob.cardyV (c' / 12) t)|) ≤ FKc (qProb prob) 1 c' * C_T * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    refine le_of_eq_of_le (setIntegral_congr_fun measurableSet_Icc fun t ht => ?_) hband0
    have h0 : 0 ≤ t := le_trans (by have := lt_of_lt_of_le hxi hχ1; positivity) ht.1
    rw [abs_mul, abs_of_nonneg (by linarith [(hRc i t).1] : 0 ≤ Rm i c' t), abs_profile_mul prob hcS _ h0]
  have hfar : (∫ t in Ici (c' * (xiStar + 3 / 10) ^ 2 / 3),
      |Rm i c' t * (combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t *
        prob.cardyV (c' / 12) t)|) ≤ C_far * √c' := by
    refine le_of_eq_of_le (setIntegral_congr_fun measurableSet_Ici fun t ht => ?_) hfar0
    have h0 : 0 ≤ t := le_trans (by positivity) ht
    rw [abs_mul, abs_of_nonneg (by linarith [(hRc i t).1] : 0 ≤ Rm i c' t), abs_profile_mul prob hcS _ h0]
  have hsc : 0 < √c' := Real.sqrt_pos.mpr hcpos
  have hfk4 : C_far * √c' ≤ ε / 4 * FKc (qProb prob) 1 c' := by
    have h := mul_le_mul_of_nonneg_left hFKbig (show 0 ≤ ε / 4 by positivity)
    have e : ε / 4 * (C_far / (ε / 4) * √c') = C_far * √c' := by field_simp
    linarith
  exact final_arith hFK hsplit hwin hn4 he1le
    (by rw [← mul_assoc]; exact hband) hn3 (hfar.trans hfk4)

/-! ### 2. The bumped `f = 1` designs at every weight -/

open FormalResearch.ModularBootstrap.Upper.Bump FormalResearch.ModularBootstrap.Upper.Ramped
  FormalResearch.ModularBootstrap.Crossing

/-- The bumped comb `B_D^{(p)}` of the `f = 1` finite modification with offsets `σs` and widths
`designWidth1 c' η` (base cut `N`): the `designComb` of cut `N'` with the data of `Bump.bumpedComb`
(heights `η_big ℓ_k` on the block `[ξ_* + 2 r_p, X_p]`, reference sites beyond `N`). -/
noncomputable def bumpSigComb (d : BumpData) (c' : ℝ) (N N' : ℕ) (η : ℝ) (σs : ℕ → ℝ) : ℂ → ℂ :=
  bumpedComb d c' 1 N N' (1 / 4) σs (designWidth1 c' η)

/-- The bumped finite modification satisfies `PhaseHyp` with total pair change `2`, for `c'` large and
every cut `N' ≥ N` (`fw:e3.4` and `phaseHyp_compact`; the threshold does not depend on `N'`). -/
theorem bumpSig_phaseHyp (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      PhaseHyp c' 1 N' (1 / 4) (bumpSigma c' N σs) (bumpEps d c' N (1 / 4) (designWidth1 c' η)) 2 := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k, 1 ≤ k → k ≤ N → |σs k| ≤ M :=
    ⟨∑ k ∈ Finset.Icc 1 N, |σs k|, fun k hk hkN =>
      Finset.single_le_sum (f := fun j => |σs j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_Icc.mpr ⟨hk, hkN⟩)⟩
  obtain ⟨Cg, hCg, hfam⟩ := designWidth1_family N hη0 hη1
  filter_upwards [phaseHyp_compact 1 N le_rfl hN M Cg (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumped_phaseHyp d 1 le_rfl (η₀ := 1 / 4) (by norm_num) le_rfl, hfam] with c' hc hb hf N' hNN'
  have h := hb N N' σs (designWidth1 c' η) 1
    (hc σs (designWidth1 c' η) (fun k hk hkN => hM k hk hkN) (fun k hk hkN => hf k hk hkN)) hNN'
  norm_num at h
  exact h

/-- **Lemma `K7` for the bumped designs at every weight**, uniform in the cut `N' ≥ N`: `h₀^{(p)}` and its
order-`(w-1)` transform decay, `g_w = ½(h₀^{(p)} - ĥ₀^{(p)})` is in the test class, `g_vac = ½ h_{0,vac} - π ∫ h₀^{(p)} V`,
`|½ h_{0,vac}| ≤ 2^m` (`fw:e3.4`, `fw:FWM`). -/
theorem bumpSig_k7W (prob : FixedWeightProblem) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' → K7ConclusionW prob c' (bumpSigComb d c' N N' η σs) := by
  obtain ⟨K, hK, hk7⟩ := phase_k7W (prob := prob) 1 le_rfl (η₀ := 1 / 4) (by norm_num) le_rfl
    (P := 2) (by norm_num)
  filter_upwards [hk7, bumpSig_phaseHyp d N hN hη0 hη1 σs] with c' h1 h2 N' hNN'
  exact h1 N' _ _ (h2 N' hNN')

/-- **The value identity on the profile**: `h₀^{(p)}(t) = R_bump(√(3t/c')) h₀(t)` for every `t` (`bumped_value`). -/
theorem combProfile_bumped_eq (d : BumpData) :
    ∀ᶠ c' in atTop, ∀ (N N' : ℕ) (σs ε : ℕ → ℝ), 1 ≤ N → N ≤ N' → ∀ t : ℝ,
      combProfile c' (bumpedComb d c' 1 N N' (1 / 4) σs ε) t =
        bumpFactor d c' (1 / 4) N N' (xOf c' t) *
          combProfile c' (designComb c' 1 N (1 / 4) σs ε) t := by
  filter_upwards [bumped_value d (η₀ := 1 / 4) (by norm_num) le_rfl] with c' hv N N' σs ε hN hNN' t
  obtain ⟨hb, hbump⟩ := hv 1 N N' σs ε (xOf c' t) hN hNN'
  unfold combProfile combH0
  rw [hbump, hb, sechSqProfile_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.ofReal_re]
  ring

lemma bumpC_pos (d : BumpData) (η₀ : ℝ) : 0 < bumpC d η₀ := Real.exp_pos _

lemma bumpC'_nonneg (d : BumpData) (η₀ : ℝ) : 0 ≤ bumpC' d η₀ := by
  have h1 : 0 < d.X - d.lo := sub_pos.mpr d.lo_lt_X
  have h2 := d.rhoHi_pos
  have h3 := d.rhoLo_pos
  have h4 := d.r_pos
  have h5 := pairK_nonneg η₀ d.H
  unfold bumpC'
  positivity

/-- **The integrand of the bumped vacuum functional**: continuity on `[0, ∞)` and integrability on `(0, ∞)`
of `h₀^{(p)} V` (uniformly in the cut, from `PhaseHyp`, `K7`-decay and `kernelIntegrable_of_decay`). -/
theorem bumpSig_integrand_props (prob : FixedWeightProblem) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      ContinuousOn (fun t => combProfile c' (bumpSigComb d c' N N' η σs) t * prob.cardyV (c' / 12) t)
        (Ici 0) ∧
      IntegrableOn (fun t => combProfile c' (bumpSigComb d c' N N' η σs) t * prob.cardyV (c' / 12) t)
        (Ioi 0) := by
  filter_upwards [bumpSig_phaseHyp d N hN hη0 hη1 σs, bumpSig_k7W prob d N hN hη0 hη1 σs,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    eventually_ge_atTop (12 * prob.totalShift), eventually_gt_atTop (0 : ℝ)]
    with c' hph hk7 hin hcS hpos N' hNN'
  obtain ⟨hfN, hA, -⟩ := hph N' hNN'
  have hI : InnerCombHyp c' (bumpSigComb d c' N N' η σs) := hin N' _ _ hfN hA
  obtain ⟨C, hC0, hdec, -⟩ := hk7 N' hNN'
  have hcont := hI.continuousOn_combProfile hpos
  have hk := kernelIntegrable_of_decay (w := prob.w) prob.hw hpos hcont hdec
  exact ⟨hcont.mul (Crossing.continuous_cardyV prob (c' / 12)).continuousOn,
    integrableOn_mul_cardyV (prob := prob) (by linarith) hcont hk⟩

/-- **Vacuum core for the bumped designs at every weight** (`ut:Vac`, `fw:e3.6`): for every `ε > 0`, `c'` large and every
cut `N' ≥ N`, `V_c^{(p)} = ∫_0^∞ h₀^{(p)} V dt ≤ FK_c (C_* V_D + ε)`, `FK_c = FKc (qProb prob) 1 c'`. -/
theorem vacuum_core_bumped (prob : FixedWeightProblem) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      ∫ t in Ioi 0, combProfile c' (bumpSigComb d c' N N' η σs) t * prob.cardyV (c' / 12) t ≤
        FKc (qProb prob) 1 c' * (CStar * windowIntegralSig N η σs + ε) := by
  have hR : ∀ᶠ c' in atTop, ∀ (i : {N' : ℕ // N ≤ N'}) (t : ℝ),
      1 ≤ bumpFactor d c' (1 / 4) N i.1 (xOf c' t) ∧ bumpFactor d c' (1 / 4) N i.1 (xOf c' t) ≤ bumpC d (1 / 4) := by
    filter_upwards [bumpFactor_one_le d (η₀ := 1 / 4) (by norm_num) le_rfl,
      bumpFactor_le d (η₀ := 1 / 4) (by norm_num) le_rfl] with c' h1 h2 i t
    exact ⟨h1 N i.1 _, h2 N i.1 _ (xOf_nonneg c' t)⟩
  have hnear : ∀ᶠ c' in atTop, ∀ (i : {N' : ℕ // N ≤ N'}) (t : ℝ), xOf c' t ≤ xiStar + d.r →
      bumpFactor d c' (1 / 4) N i.1 (xOf c' t) ≤ 1 + bumpC' d (1 / 4) / c' := by
    filter_upwards [bumpFactor_le_one_add d (η₀ := 1 / 4) (by norm_num) le_rfl] with c' h i t ht
    exact h N i.1 _ (xOf_nonneg c' t) ht
  have hint : ∀ᶠ c' in atTop, ∀ i : {N' : ℕ // N ≤ N'},
      ContinuousOn (fun t => bumpFactor d c' (1 / 4) N i.1 (xOf c' t) *
        (combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t *
          prob.cardyV (c' / 12) t)) (Ici 0) ∧
      IntegrableOn (fun t => bumpFactor d c' (1 / 4) N i.1 (xOf c' t) *
        (combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t *
          prob.cardyV (c' / 12) t)) (Ioi 0) := by
    filter_upwards [bumpSig_integrand_props prob d N hN hη0 hη1 σs, combProfile_bumped_eq d]
      with c' hp hval i
    have hfun : (fun t => bumpFactor d c' (1 / 4) N i.1 (xOf c' t) *
        (combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t *
          prob.cardyV (c' / 12) t)) =
        fun t => combProfile c' (bumpSigComb d c' N i.1 η σs) t * prob.cardyV (c' / 12) t := by
      funext t
      unfold bumpSigComb
      rw [hval N i.1 σs (designWidth1 c' η) hN i.2 t]
      ring
    rw [hfun]
    exact hp i.1 i.2
  have key := vacuum_core_mul prob N hN hη0 hη1 σs (ι := {N' : ℕ // N ≤ N'})
    (fun i c' t => bumpFactor d c' (1 / 4) N i.1 (xOf c' t)) (Kb := bumpC d (1 / 4))
    (C' := bumpC' d (1 / 4)) (r := d.r) (bumpC_pos d _).le (bumpC'_nonneg d _) d.r_pos hR hnear hint hε
  filter_upwards [key, combProfile_bumped_eq d] with c' hk hval N' hNN'
  have e : (fun t => combProfile c' (bumpSigComb d c' N N' η σs) t * prob.cardyV (c' / 12) t) =
      fun t => bumpFactor d c' (1 / 4) N N' (xOf c' t) *
        (combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t *
          prob.cardyV (c' / 12) t) := by
    funext t
    unfold bumpSigComb
    rw [hval N N' σs (designWidth1 c' η) hN hNN' t]
    ring
  rw [e]
  exact hk ⟨N', hNN'⟩


/-! ### 3. Proposition V (i), (ii) for the bumped designs at every weight -/

/-- `g_vac` of the bumped `f = 1` finite modification, `g_w = ½ (h₀^{(p)} - ĥ₀^{(p)})` (`pairOdd`),
`ĥ₀ = hankelTransform prob.w h₀`. -/
noncomputable def bumpSigGVac (prob : FixedWeightProblem) (d : BumpData) (N N' : ℕ) (η : ℝ) (σs : ℕ → ℝ)
    (c' : ℝ) : ℝ :=
  prob.gVac (c' / 12)
    (pairOdd (combProfile c' (bumpSigComb d c' N N' η σs))
      (hankelTransform prob.w (combProfile c' (bumpSigComb d c' N N' η σs))))

/-- `∫ Ψ_g du = -g_vac / (2π)` (`ut:s4`, the crossing identity `integral_psiAiry_eq_neg_gVac`) for the bumped design. -/
noncomputable def bumpSigPsiIntegral (prob : FixedWeightProblem) (d : BumpData) (N N' : ℕ) (η : ℝ)
    (σs : ℕ → ℝ) (c' : ℝ) : ℝ :=
  -bumpSigGVac prob d N N' η σs c' / (2 * π)

/-- `g_vac ≥ -2^m - π V_c^{(p)}` for the bumped designs (vacuum identity, `|½ h_{0,vac}| ≤ 2^m`), every weight. -/
theorem bumpSigGVac_ge (prob : FixedWeightProblem) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      -(2 : ℝ) ^ prob.m - π * (∫ t in Ioi 0,
          combProfile c' (bumpSigComb d c' N N' η σs) t * prob.cardyV (c' / 12) t) ≤
        bumpSigGVac prob d N N' η σs c' := by
  filter_upwards [bumpSig_k7W prob d N hN hη0 hη1 σs] with c' hK7 N' hNN'
  obtain ⟨C, hC0, -, -, -, hvac, hn⟩ := hK7 N' hNN'
  have hre := congrArg Complex.re hvac
  rw [Complex.ofReal_re, Complex.sub_re] at hre
  have h2 : ((π : ℂ) * ((∫ t in Ioi (0 : ℝ),
      combProfile c' (bumpSigComb d c' N N' η σs) t * prob.cardyV (c' / 12) t : ℝ) : ℂ)).re =
      π * (∫ t in Ioi (0 : ℝ),
        combProfile c' (bumpSigComb d c' N N' η σs) t * prob.cardyV (c' / 12) t) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [h2] at hre
  have h3 := (Complex.abs_re_le_norm _).trans hn
  have := (abs_le.mp h3).1
  unfold bumpSigGVac
  linarith

/-- **Proposition V (i)** (`ut:Vac`) for the bumped `f = 1` designs, at every weight `w = prob.w`, uniform in the cut
`N' ≥ N`: for every `ε > 0` and large `c'`, `(2/FK_c) ∫ Ψ_g du - C_* V_D ≤ ε` (`limsup ≤ 0`; no sign assumption on `V_D`),
`FK_c = FKc (qProb prob) 1 c'` and `V_D = windowIntegralSig N η σs`. -/
theorem proposition_V_i_bumped (prob : FixedWeightProblem) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      2 * bumpSigPsiIntegral prob d N N' η σs c' / FKc (qProb prob) 1 c' -
        CStar * windowIntegralSig N η σs ≤ ε := by
  have hπ := Real.pi_pos
  filter_upwards [bumpSigGVac_ge prob d N hN hη0 hη1 σs,
    vacuum_core_bumped prob d N hN hη0 hη1 σs (half_pos hε),
    FKc_ge_mul_sqrt_of_pos (qProb_pos prob) (2 * 2 ^ prob.m / (π * ε)),
    eventually_gt_atTop (1 : ℝ)] with c' hg hc hFKbig hc1 N' hNN'
  have hcpos : 0 < c' := by linarith
  have hFK := FKc_pos (qProb_pos prob) 1 hcpos
  have hsc : 1 ≤ √c' := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hc1.le
  have h8 : 2 * 2 ^ prob.m / (π * ε) ≤ FKc (qProb prob) 1 c' :=
    le_trans (le_mul_of_one_le_right (by positivity) hsc) hFKbig
  have h9 : 2 * 2 ^ prob.m ≤ π * ε * FKc (qProb prob) 1 c' := by
    have := (div_le_iff₀ (by positivity)).mp h8
    linarith
  have hg' := hg N' hNN'
  have hc' := hc N' hNN'
  unfold bumpSigPsiIntegral
  rw [sub_le_iff_le_add, div_le_iff₀ hFK]
  have e : 2 * (-bumpSigGVac prob d N N' η σs c' / (2 * π)) = -bumpSigGVac prob d N N' η σs c' / π := by
    field_simp
  rw [e, div_le_iff₀ hπ]
  nlinarith only [mul_le_mul_of_nonneg_left hc' hπ.le, hg', h9]

/-- **Proposition V (ii)** (`ut:Vac`) for the bumped `f = 1` designs, at every weight, uniform in the cut `N' ≥ N`: if
`V_D < 0` then for large `c'`, `g_vac > 0` and `g_vac ≥ π C_* |V_D| FK_c / 4`. -/
theorem proposition_V_ii_bumped (prob : FixedWeightProblem) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) (hV : windowIntegralSig N η σs < 0) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      0 < bumpSigGVac prob d N N' η σs c' ∧
        π * CStar * |windowIntegralSig N η σs| * FKc (qProb prob) 1 c' / 4 ≤
          bumpSigGVac prob d N N' η σs c' := by
  have hπ := Real.pi_pos
  have hC := CStar_pos
  have hVa : 0 < |windowIntegralSig N η σs| := abs_pos.mpr hV.ne
  have hε : 0 < CStar * |windowIntegralSig N η σs| / 2 := by positivity
  filter_upwards [bumpSigGVac_ge prob d N hN hη0 hη1 σs,
    vacuum_core_bumped prob d N hN hη0 hη1 σs hε,
    FKc_ge_mul_sqrt_of_pos (qProb_pos prob)
      (4 * 2 ^ prob.m / (π * CStar * |windowIntegralSig N η σs|)),
    eventually_gt_atTop (1 : ℝ)] with c' hg hc hFKbig hc1 N' hNN'
  have hcpos : 0 < c' := by linarith
  have hFK := FKc_pos (qProb_pos prob) 1 hcpos
  have hsc : 1 ≤ √c' := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hc1.le
  have hpos : 0 < π * CStar * |windowIntegralSig N η σs| := by positivity
  have h8 : 4 * 2 ^ prob.m / (π * CStar * |windowIntegralSig N η σs|) ≤ FKc (qProb prob) 1 c' :=
    le_trans (le_mul_of_one_le_right (by positivity) hsc) hFKbig
  have h9 : 4 * 2 ^ prob.m ≤ π * CStar * |windowIntegralSig N η σs| * FKc (qProb prob) 1 c' := by
    have := (div_le_iff₀ hpos).mp h8
    linarith
  have habs : |windowIntegralSig N η σs| = -windowIntegralSig N η σs := abs_of_neg hV
  have hVc : π * (∫ t in Ioi 0,
        combProfile c' (bumpSigComb d c' N N' η σs) t * prob.cardyV (c' / 12) t) ≤
      -(π * CStar * |windowIntegralSig N η σs| * FKc (qProb prob) 1 c' / 2) := by
    have := mul_le_mul_of_nonneg_left (hc N' hNN') hπ.le
    rw [habs] at this ⊢
    nlinarith only [this]
  have hlow : π * CStar * |windowIntegralSig N η σs| * FKc (qProb prob) 1 c' / 4 ≤
      bumpSigGVac prob d N N' η σs c' := by
    linarith only [hg N' hNN', hVc, h9]
  exact ⟨lt_of_lt_of_le (by positivity) hlow, hlow⟩

/-- Proposition V (i) for the designs `D(N, η_*, d)` (`σs = designSigma1 d`, `V_D = windowIntegralVD`). -/
theorem proposition_V_i_bumped_design (prob : FixedWeightProblem) (d' : BumpData) (N : ℕ) (hN : 1 ≤ N)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      2 * bumpSigPsiIntegral prob d' N N' η (designSigma1 d) c' / FKc (qProb prob) 1 c' -
        CStar * windowIntegralVD N η d ≤ ε := by
  simpa only [windowIntegralVD_eq_sig] using
    proposition_V_i_bumped prob d' N hN hη0 hη1 (designSigma1 d) hε

/-- Proposition V (ii) for the designs `D(N, η_*, d)`. -/
theorem proposition_V_ii_bumped_design (prob : FixedWeightProblem) (d' : BumpData) (N : ℕ) (hN : 1 ≤ N)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d : ℝ) (hV : windowIntegralVD N η d < 0) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      0 < bumpSigGVac prob d' N N' η (designSigma1 d) c' ∧
        π * CStar * |windowIntegralVD N η d| * FKc (qProb prob) 1 c' / 4 ≤
          bumpSigGVac prob d' N N' η (designSigma1 d) c' := by
  rw [windowIntegralVD_eq_sig] at hV ⊢
  exact proposition_V_ii_bumped prob d' N hN hη0 hη1 (designSigma1 d) hV

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.vacuum_core_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vacuum_core_mul

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.lemma_T_sig1_prob_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T_sig1_prob_mul

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.sig_window_pointwise_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sig_window_pointwise_w

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.bumpSig_phaseHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpSig_phaseHyp

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.bumpSig_k7W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpSig_k7W

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.combProfile_bumped_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combProfile_bumped_eq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.bumpSig_integrand_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpSig_integrand_props

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.vacuum_core_bumped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vacuum_core_bumped

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.bumpSigGVac_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpSigGVac_ge

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_V_i_bumped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_V_i_bumped

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_V_ii_bumped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_V_ii_bumped

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_V_i_bumped_design' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_V_i_bumped_design

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_V_ii_bumped_design' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_V_ii_bumped_design

end FormalResearch.ModularBootstrap.Upper.Positivity
