module

public import FormalResearch.ModularBootstrap.Upper.Bump.Factor

/-!
# The floor gain of the bump at the nearest raised site (`fw:e3.2`, `fw:e3.5`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, "The improved lower floor for a boosted nearest pair":
"the nearest quantile site `χ_{k₀}` lies inside the boosted block `[ξ_* + 2 r_p, X_p]` with
`|x - χ_{k₀}| ≤ ½ ℓ_{k₀}(1 + O_p(c'^{-1}))` for large `c'`, contributing `≥ (16/5)(η_big² + 1/4)(1 - o(1))`
by `fw:e3.2`, and every other boosted pair has ratio `≥ 1` by `fw:e3.1`".

* `gap_ratio_le`: on the block `ℓ_k ≤ (1 + C/c') ℓ_{k+1}` (from `chiDeriv_le_siteGap_prev`, `siteGap_le_chiDeriv`
  and the Lipschitz bound of `ρ_U`), the `1 + O(1/c')` in the paper;
* `exists_nearest_block_site`: for `ξ_* + 3 r_p ≤ x ≤ X_p - 1` there is a block index `k` with
  `|x - χ_k| ≤ (1/2 + C/(2c')) ℓ_k`;
* `bumpFactor_floor` (`fw:e3.5`, the gain): for every `τ > 0`, `R_bump(x) ≥ (1 - τ)(H² + 1/4)/(η₀² + 1/4)` on
  `ξ_* + 3 r_p ≤ x ≤ X_p - 1`; for `η₀ = 1/4` this is `(1 - τ)(16/5)(η_big² + 1/4)`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Bump

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Holes
open scoped Classical

/-- Lipschitz bound of `ρ_U` to the right of `l > ξ_*`. -/
lemma rhoU_sub_le {l a b : ℝ} (hl : xiStar < l) (hla : l ≤ a) (hab : a ≤ b) :
    rhoU b - rhoU a ≤ rhoUDeriv l * (b - a) := by
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := rhoU) (f' := rhoUDeriv)
    (C := rhoUDeriv l) (s := Set.Icc a b) (x := a) (y := b)
    (fun t ht => (hasDerivAt_rhoU (lt_of_lt_of_le hl (hla.trans ht.1))).hasDerivWithinAt)
    (fun t ht => by
      have h1 : 4 / 3 < rhoUDeriv t := rhoUDeriv_ge (lt_of_lt_of_le hl (hla.trans ht.1))
      rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
      exact rhoUDeriv_strictAntiOn.antitoneOn (Set.mem_Ioi.mpr hl)
        (Set.mem_Ioi.mpr (lt_of_lt_of_le hl (hla.trans ht.1))) (hla.trans ht.1))
    (convex_Icc a b) (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at key
  exact (le_abs_self _).trans key

/-- The constant of `gap_ratio_le`. -/
noncomputable def BumpData.gapC (d : BumpData) : ℝ := 4 * rhoUDeriv d.lo / d.rhoLo ^ 2

lemma BumpData.gapC_nonneg (d : BumpData) : 0 ≤ d.gapC := by
  have h := rhoUDeriv_ge d.xiStar_lt_lo
  unfold gapC
  have := d.rhoLo_pos
  positivity

/-- On the block the quantile gaps vary by a factor `1 + O(1/c')` from one cell to the next. -/
theorem gap_ratio_le (d : BumpData) :
    ∀ᶠ c' in atTop, ∀ k : ℕ, 1 ≤ k → d.InBlock c' k →
      siteGap c' k ≤ (1 + d.gapC / c') * siteGap c' (k + 1) := by
  filter_upwards [block_gap_bounds d, eventually_gt_atTop 0] with c' hbg hc' k hk hb
  have hρlo := d.rhoLo_pos
  have hD := rhoUDeriv_ge d.xiStar_lt_lo
  have hξ : xiStar < chiQuantile c' (k : ℝ) := lt_of_lt_of_le d.xiStar_lt_lo hb.1
  have hρk : d.rhoLo ≤ rhoU (chiQuantile c' (k : ℝ)) :=
    rhoU_strictMonoOn.monotoneOn (Set.mem_Ici.mpr d.xiStar_lt_lo.le) (Set.mem_Ici.mpr hξ.le) hb.1
  have hρkpos : 0 < rhoU (chiQuantile c' (k : ℝ)) := lt_of_lt_of_le hρlo hρk
  have hup := siteGap_le_chiDeriv hc' hk
  have hprev := chiDeriv_le_siteGap_prev hc' (k := k + 2) (by omega)
  have e1 : k + 2 - 1 = k + 1 := by omega
  rw [e1] at hprev
  have hmono2 : chiQuantile c' (k : ℝ) ≤ chiQuantile c' ((k + 2 : ℕ) : ℝ) :=
    chi_mono_nat hc' hk (by omega)
  have hξ2 : xiStar < chiQuantile c' ((k + 2 : ℕ) : ℝ) := lt_of_lt_of_le hξ hmono2
  have hρ2pos : 0 < rhoU (chiQuantile c' ((k + 2 : ℕ) : ℝ)) := rhoU_pos hξ2
  set ρk := rhoU (chiQuantile c' (k : ℝ)) with hρk_def
  set ρ2 := rhoU (chiQuantile c' ((k + 2 : ℕ) : ℝ)) with hρ2_def
  have hgap_k := (hbg k hk hb).2
  have hℓ1le : siteGap c' (k + 1) ≤ siteGap c' k := siteGap_antitone hc' hk (Nat.le_succ k)
  have hdist : chiQuantile c' ((k + 2 : ℕ) : ℝ) - chiQuantile c' (k : ℝ) ≤ 4 / (c' * d.rhoLo) := by
    have h1 := siteGap_eq c' k
    have h2 := siteGap_eq c' (k + 1)
    have h3 : chiQuantile c' ((k + 1 + 1 : ℕ) : ℝ) = chiQuantile c' ((k + 2 : ℕ) : ℝ) := rfl
    rw [h3] at h2
    have : (4 : ℝ) / (c' * d.rhoLo) = 2 * (2 / (c' * d.rhoLo)) := by ring
    rw [this]
    linarith
  have hρdiff : ρ2 - ρk ≤ rhoUDeriv d.lo * (4 / (c' * d.rhoLo)) := by
    have := rhoU_sub_le d.xiStar_lt_lo hb.1 hmono2
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_left hdist (by linarith)
  have hratio : ρ2 / ρk ≤ 1 + d.gapC / c' := by
    rw [div_le_iff₀ hρkpos]
    have h1 : ρ2 ≤ ρk + rhoUDeriv d.lo * (4 / (c' * d.rhoLo)) := by linarith
    have h2 : (1 + d.gapC / c') * ρk = ρk + d.gapC / c' * ρk := by ring
    have h3 : rhoUDeriv d.lo * (4 / (c' * d.rhoLo)) ≤ d.gapC / c' * ρk := by
      unfold BumpData.gapC
      rw [show 4 * rhoUDeriv d.lo / d.rhoLo ^ 2 / c' * ρk = rhoUDeriv d.lo * (4 * ρk / (c' * d.rhoLo ^ 2))
        by field_simp]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hρlo hc', mul_le_mul_of_nonneg_left hρk (by positivity : (0 : ℝ) ≤ 4 * (c' * d.rhoLo))]
    linarith
  have hℓk : siteGap c' k ≤ 2 / (c' * ρk) := hup
  have hℓk1 : 2 / (c' * ρ2) ≤ siteGap c' (k + 1) := hprev
  calc siteGap c' k ≤ 2 / (c' * ρk) := hℓk
    _ = (ρ2 / ρk) * (2 / (c' * ρ2)) := by field_simp
    _ ≤ (ρ2 / ρk) * siteGap c' (k + 1) := mul_le_mul_of_nonneg_left hℓk1 (by positivity)
    _ ≤ (1 + d.gapC / c') * siteGap c' (k + 1) :=
        mul_le_mul_of_nonneg_right hratio (le_trans (by positivity) hℓk1)

/-- For `ξ_* + 3 r_p ≤ x ≤ X_p - 1` there is a block index whose site is within `(1/2 + C/(2c')) ℓ_k` of `x`. -/
theorem exists_nearest_block_site (d : BumpData) :
    ∀ᶠ c' in atTop, ∀ x : ℝ, xiStar + 3 * d.r ≤ x → x ≤ d.X - 1 →
      ∃ k : ℕ, 1 ≤ k ∧ d.InBlock c' k ∧
        |x - chiQuantile c' (k : ℝ)| ≤ (1 / 2 + d.gapC / (2 * c')) * siteGap c' k := by
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  have hlam1 : ∀ᶠ c' in atTop, Cg * lambdaComb c' ≤ d.r / 2 := by
    have := tendsto_lambdaComb_atTop.const_mul Cg
    simp only [mul_zero] at this
    exact this.eventually_le_const (by have := d.r_pos; positivity)
  have hlam2 : ∀ᶠ c' in atTop, lambdaComb c' * phiQuantile (((1 : ℕ) : ℝ) + 2) ≤ d.r := by
    have := tendsto_lambdaComb_atTop.mul_const (phiQuantile (((1 : ℕ) : ℝ) + 2))
    simp only [zero_mul] at this
    exact this.eventually_le_const d.r_pos
  filter_upwards [h_ev, hlam1, hlam2, gap_ratio_le d, eventually_gt_atTop 0]
    with c' ⟨hmono, hg1, hg2, hgap⟩ hl1 hl2 hratio hc' x hx1 hx2
  have hgapk : ∀ k : ℕ, 1 ≤ k → siteGap c' k ≤ d.r / 2 := fun k hk => by
    have := (hmono k hk).trans (hg1.trans hg2)
    linarith
  have hgapk1 : ∀ k : ℕ, 1 ≤ k → siteGap c' k ≤ 1 / 2 := fun k hk => (hmono k hk).trans hgap
  have hχ1 : chiQuantile c' ((1 : ℕ) : ℝ) ≤ x := by
    have := d.r_pos
    have h := (refSite_bounds hc' (k := 1) (N := 1) le_rfl le_rfl).2
    linarith
  obtain ⟨n, hn1, hcell⟩ := exists_inCell hc' (M := 1) le_rfl (x := x) (by exact_mod_cast hχ1)
  obtain ⟨hcn1, hcn2⟩ := hcell
  have hrpos := d.r_pos
  have hgn := siteGap_eq c' n
  have hlo : d.lo ≤ chiQuantile c' (n : ℝ) := by
    by_contra hlt
    push Not at hlt
    have := hgapk n hn1
    unfold BumpData.lo at hlt
    linarith
  have hbn : d.InBlock c' n := ⟨hlo, by linarith [d.X_gt]⟩
  have hbn1 : d.InBlock c' (n + 1) := by
    refine ⟨hlo.trans (chi_mono_nat hc' hn1 (Nat.le_succ n)), ?_⟩
    have := hgapk1 n hn1
    linarith
  by_cases hnear : x - chiQuantile c' (n : ℝ) ≤ siteGap c' n / 2
  · refine ⟨n, hn1, hbn, ?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hcn1)]
    have h0 : 0 ≤ siteGap c' n := siteGap_nonneg hc' hn1
    have := d.gapC_nonneg
    have : 0 ≤ d.gapC / (2 * c') * siteGap c' n := by positivity
    nlinarith
  · push Not at hnear
    refine ⟨n + 1, by omega, hbn1, ?_⟩
    have hle : x - chiQuantile c' ((n + 1 : ℕ) : ℝ) ≤ 0 := by linarith
    rw [abs_of_nonpos hle]
    have hr := hratio n hn1 hbn
    have h1 : chiQuantile c' ((n + 1 : ℕ) : ℝ) - x < siteGap c' n / 2 := by linarith
    calc -(x - chiQuantile c' ((n + 1 : ℕ) : ℝ)) ≤ siteGap c' n / 2 := by linarith
      _ ≤ (1 + d.gapC / c') * siteGap c' (n + 1) / 2 := by linarith
      _ = (1 / 2 + d.gapC / (2 * c')) * siteGap c' (n + 1) := by field_simp

/-- Every pair ratio is `≥ 1`, uniformly. -/
theorem bumpRatio_one_le (d : BumpData) {η₀ : ℝ} (hη₀ : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ k : ℕ, 1 ≤ k → ∀ x : ℝ, 1 ≤ bumpRatio d c' η₀ x k := by
  filter_upwards [bumpRatio_facts d hη₀ hη₀1] with c' h k hk x
  by_cases hb : d.InBlock c' k
  · exact ((h k hk x).2.2 hb).1
  · exact ((h k hk x).2.1 hb).ge

/-- **The gain of the bump** (`fw:e3.5`, comb level).  For `0 < η₀ ≤ 1/4` and `τ > 0`, for `c'` large, every cut
`N₀ < (block) ≤ N` (`BlockAbove`, and `N` above every index with `χ_k ≤ X_p`) and every `x` with
`ξ_* + 3 r_p ≤ x ≤ X_p - 1`:
`(1 - τ)(η_big² + 1/4)/(η₀² + 1/4) ≤ R_bump(x)`; for `η₀ = 1/4` the constant is `(1 - τ)(16/5)(η_big² + 1/4)`. -/
theorem bumpFactor_floor (d : BumpData) {η₀ : ℝ} (hη₀ : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4) {τ : ℝ}
    (hτ : 0 < τ) :
    ∀ᶠ c' in atTop, ∀ (N₀ N : ℕ) (x : ℝ), d.BlockAbove c' N₀ →
      (∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ d.X → k ≤ N) →
      xiStar + 3 * d.r ≤ x → x ≤ d.X - 1 →
      (1 - τ) * ((d.H ^ 2 + 1 / 4) / (η₀ ^ 2 + 1 / 4)) ≤ bumpFactor d c' η₀ N₀ N x := by
  obtain ⟨δ, hδ, hratio⟩ := blaschkePairQ_ratio_ge hη₀ (hη₀1.trans d.H_ge) hτ
  have hρ := d.rhoLo_pos
  filter_upwards [block_gap_bounds d, exists_nearest_block_site d, bumpRatio_facts d hη₀ hη₀1,
    bumpRatio_one_le d hη₀ hη₀1, eventually_ge_atTop (2 / (d.rhoLo * δ)),
    eventually_ge_atTop (d.gapC / (2 * δ)), eventually_ge_atTop (4 * d.H / d.rhoLo),
    eventually_gt_atTop 0]
    with c' hbg hnear hfacts hone hc1 hc2 hc3 hc' N₀ N x hab hcut hx1 hx2
  have hρhi := d.rhoHi_pos
  obtain ⟨k, hk1, hkb, hkx⟩ := hnear x hx1 hx2
  have hℓpos : 0 < siteGap c' k := lt_of_lt_of_le (by positivity) (hbg k hk1 hkb).1
  have hℓL : siteGap c' k ≤ 2 / (c' * d.rhoLo) := (hbg k hk1 hkb).2
  have hℓδ : siteGap c' k ≤ δ := by
    refine hℓL.trans ?_
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hc1
    nlinarith
  have hθ2 : 1 / 2 + d.gapC / (2 * c') ≤ 1 / 2 + δ := by
    have : d.gapC / (2 * c') ≤ δ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hc2
      nlinarith
    linarith
  have hθ1 : 1 / 2 ≤ 1 / 2 + d.gapC / (2 * c') := by
    have := d.gapC_nonneg
    have : 0 ≤ d.gapC / (2 * c') := by positivity
    linarith
  have hHℓ : d.H * siteGap c' k ≤ 1 / 2 := by
    have h1 : d.H * siteGap c' k ≤ d.H * (2 / (c' * d.rhoLo)) :=
      mul_le_mul_of_nonneg_left hℓL d.H_pos.le
    have h2 : d.H * (2 / (c' * d.rhoLo)) ≤ 1 / 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hρ] at hc3
      nlinarith
    linarith
  have hxpos : 0 ≤ x := by have := xiStar_pos; have := d.r_pos; linarith
  have hQ := hratio (1 / 2 + d.gapC / (2 * c')) (siteGap c' k) (chiQuantile c' (k : ℝ)) x hθ1 hθ2 hℓpos
    hℓδ hkx (chi_nonneg hc' hk1) hxpos hHℓ
  have hQ0 := (hfacts k hk1 x).1
  have hkratio : (1 - τ) * ((d.H ^ 2 + 1 / 4) / (η₀ ^ 2 + 1 / 4)) ≤ bumpRatio d c' η₀ x k := by
    unfold bumpRatio
    have hheight : bumpHeight d c' η₀ k = d.H * siteGap c' k := by
      unfold bumpHeight; simp [hkb]
    rw [hheight, le_div_iff₀ hQ0]
    exact hQ
  have hkmem : k ∈ Finset.Ioc N₀ N := by
    rw [Finset.mem_Ioc]
    refine ⟨?_, hcut k hk1 hkb.2⟩
    by_contra hle
    exact hab k (not_lt.mp hle) hkb
  rw [bumpFactor_eq_prod, ← Finset.mul_prod_erase _ _ hkmem]
  have hrest : 1 ≤ ∏ j ∈ (Finset.Ioc N₀ N).erase k, bumpRatio d c' η₀ x j := by
    calc (1 : ℝ) = ∏ _j ∈ (Finset.Ioc N₀ N).erase k, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun j hj => by
          have hj' := Finset.mem_Ioc.mp (Finset.mem_of_mem_erase hj)
          exact hone j (by omega) x
  have hk0 : 0 ≤ bumpRatio d c' η₀ x k := zero_le_one.trans (hone k hk1 x)
  nlinarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.gap_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gap_ratio_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.exists_nearest_block_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_nearest_block_site

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.bumpFactor_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpFactor_floor

end FormalResearch.ModularBootstrap.Upper.Bump
