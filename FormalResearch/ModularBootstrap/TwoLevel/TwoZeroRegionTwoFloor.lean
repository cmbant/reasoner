module

public import FormalResearch.ModularBootstrap.Upper.Positivity.RegionII

/-!
# Proposition II, the floor of `h₀^D`

Temporary home of `proposition_II_floor` (the `h₀^D` half of the proof of `Upper.Positivity.proposition_II`), to be
moved into `Upper/Positivity/RegionII.lean` by the in-place patch.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Holes

/-- **Proposition II, floor half** (`ut:II` steps (2)--(3)): for `c'` large, every family member and every
`x ≥ ξ_* + c'^{-2/5}`, `x` lies right of the node `χ_{f+1/2}`, `B_D^{(f)}(x) = r > 0` is real, and with
`R = ‖B_ref^{(f)}(x)‖`: `0.7 · 0.998² · Lev^{(f)} ≤ sech²(πx/2) R` and `|log (r/R)| ≤ 1/1000`. -/
theorem proposition_II_floor (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) :
    ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x →
        chiQuantile c' ((f : ℝ) + 1 / 2) < x ∧
        ∃ R r : ℝ, 0 < R ∧ 0 < r ∧ designComb c' f N (1 / 4) σ ε (x : ℂ) = (r : ℂ) ∧
          (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * levComb c' f x ≤
            1 / Real.cosh (π * x / 2) ^ 2 * R ∧
          |Real.log (r / R)| ≤ 1 / 1000 := by
  obtain ⟨CP, hCP, hP⟩ := lemma_P_b f N hf hfN M E
  obtain ⟨CL, hCL, hL⟩ := eLeftComb_bounds
  obtain ⟨N₄, C₄, hN₄, hC₄, hfloor⟩ :=
    hole_floor_K5 (j := 4) (η₀ := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cg, hCg, hgapev⟩ := siteGap_eventually_le
  set s : ℝ := max (phiQuantile ((N : ℝ) + 2)) M with hs
  set n₀ : ℕ := ⌈1000 * C₄⌉₊ + 1 with hn₀
  set M0 : ℕ := max (max N₄ (f + 4)) n₀ with hM0
  have hM0pos : 1 ≤ M0 := by
    have : f + 4 ≤ M0 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) le_rfl
    omega
  have hmuc := muHole_four_quarter_gt
  have e1 := eventually_mul_lambda_le (4 * s) 1 one_pos
  have e2 := eventually_mul_lambda_le (phiQuantile ((M0 : ℝ) + 2)) 1 one_pos
  have e3 := eventually_mul_lambda_le CL (1 / 1000) (by norm_num)
  have e4 := eventually_mul_lambda_le CP (1 / 1000) (by norm_num)
  have e5 := eventually_mul_lambda_le (C₄ * Cg) (1 / 1000) (by norm_num)
  have e6 := eventually_mul_lambda_le M xiStar xiStar_pos
  have e7 := eventually_mul_lambda_le E (1 / 2) (by norm_num)
  filter_upwards [hP (η₀ := 1 / 4) (by norm_num) (by norm_num), hL, hfloor, hgapev,
    tail_ne_zero_of_refComb_ne_zero f N hfN (η₀ := 1 / 4) (by norm_num) (by norm_num),
    e1, e2, e3, e4, e5, e6, e7, eventually_ge_atTop (1 : ℝ)]
    with c' hPc hLc hflc hgc htailc he1 he2 he3 he4 he5 he6 he7 hc1 σ ε hσ hε x hx
  obtain ⟨hgap_k, hgap_1, hcd, hgap_half⟩ := hgc
  have hc' : 0 < c' := lt_of_lt_of_le one_pos hc1
  set u : ℝ := c' ^ (-(2 / 5 : ℝ)) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hc' _
  have hu1 : u ≤ 1 := rpow_neg_two_fifths_le_one hc1
  have hlam0 : 0 ≤ lambdaComb c' := (Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _).le
  have hxu : u ≤ x - xiStar := by linarith only [hx]
  have hxi : xiStar < x := by linarith only [hx, hu0]
  have hχM0 : chiQuantile c' (M0 : ℝ) ≤ x := by
    have h := (refSite_bounds hc' hM0pos (le_refl M0)).2
    linarith only [h, he2, hx]
  obtain ⟨n, hnmax, hn_n0, hcell, hχf, hχf2⟩ := cell_facts hc' hf hχM0
  have hn1 : 1 ≤ n := by
    have : f + 4 ≤ max N₄ (f + 4) := le_max_right _ _
    omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hMl : lambdaComb c' * M ≤ xiStar := by
    have h : M * lambdaComb c' ≤ xiStar * u := he6
    have h' : xiStar * u ≤ xiStar := by nlinarith only [hu1, xiStar_pos]
    linarith only [h, h']
  have hsite := design_site_facts (s := s) (x := x) hlam0 hMl (by rw [hs]; exact le_max_right _ M) he1 hu0
    (by linarith only [hx]) hσ
  have hεw : ∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ 1 / 2 := by
    intro k hk hkN
    have h := hε k hk hkN
    have h7 : E * lambdaComb c' ≤ 1 / 2 * u := he7
    exact ⟨h.1, by linarith only [h.2, h7, hu1]⟩
  obtain ⟨-, -, -, -, h0_norm⟩ :=
    refComb_re_nonneg_of_gt hc' (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) hgap_half hf hχf
  have hlev := levComb_pos c' f x
  have hfl := hflc f n x hf hnmax hcell
  have hsg : siteGap c' n ≤ Cg * lambdaComb c' := (hgap_k n hn1).trans (hgap_1.trans hcd)
  have hnC : C₄ / (n : ℝ) ≤ 1 / 1000 := by
    have h1 : 1000 * C₄ ≤ (n₀ : ℝ) := by
      have := Nat.le_ceil (1000 * C₄)
      have h2 : (⌈1000 * C₄⌉₊ : ℝ) + 1 = (n₀ : ℝ) := by rw [hn₀]; push_cast; ring
      linarith only [this, h2]
    have h2 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn_n0
    rw [div_le_iff₀ hnR]
    linarith only [h1, h2]
  have hδ1 : C₄ * (1 / (n : ℝ) + siteGap c' n) ≤ 2 / 1000 := by
    have h1 : C₄ * siteGap c' n ≤ C₄ * (Cg * lambdaComb c') :=
      mul_le_mul_of_nonneg_left hsg hC₄.le
    have h2 : C₄ * Cg * lambdaComb c' ≤ 1 / 1000 * u := he5
    have h3 : C₄ * (1 / (n : ℝ) + siteGap c' n) = C₄ / n + C₄ * siteGap c' n := by ring
    have h4 : C₄ * (Cg * lambdaComb c') = C₄ * Cg * lambdaComb c' := by ring
    rw [h3]
    linarith only [h1, h2, h4, hnC, hu1]
  have hLbd := (hLc f n 4 x hf hxi).2
  have hδ2 : eLeftComb c' f n 4 x ≤ 1 / 1000 :=
    hLbd.trans (div_le_of_mul_le hu0 (by norm_num) he3 hxu)
  have hq1 := floor_lower hmuc hδ1 hδ2 hfl
  have hq1pos : 0 < h0Comb c' f (1 / 4) x := by
    have h := lt_of_lt_of_le (by norm_num : (0 : ℝ) < (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000)) hq1
    rwa [lt_div_iff₀ hlev, zero_mul] at h
  have hsech : 0 < 1 / Real.cosh (π * x / 2) ^ 2 := by positivity
  have href_pos : 0 < ‖refComb c' f (1 / 4) (x : ℂ)‖ := by
    rw [h0_norm] at hq1pos
    exact pos_of_mul_pos_right hq1pos hsech.le
  obtain ⟨r, hr, hr0, hrpos⟩ := designComb_ofReal hc' (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num) hgap_half f N σ ε hsite hεw hfN
  have hrp : 0 < r := hrpos (htailc x (norm_pos_iff.mp href_pos))
  have hnormD : ‖designComb c' f N (1 / 4) σ ε (x : ℂ)‖ = r := by
    rw [hr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hPbd := hPc σ ε hσ hε x (by linarith only [he1, hx])
  rw [hnormD] at hPbd
  have hlogbd : |Real.log (r / ‖refComb c' f (1 / 4) (x : ℂ)‖)| ≤ 1 / 1000 := by
    have h := div_le_of_mul_le hu0 (by norm_num) he4 hxu
    rw [mul_div_assoc] at h
    exact hPbd.trans h
  have hfloor' : (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * levComb c' f x ≤
      1 / Real.cosh (π * x / 2) ^ 2 * ‖refComb c' f (1 / 4) (x : ℂ)‖ := by
    rw [← h0_norm]; exact (le_div_iff₀ hlev).mp hq1
  exact ⟨hχf2, ‖refComb c' f (1 / 4) (x : ℂ)‖, r, href_pos, hrp, hr, hfloor', hlogbd⟩

end FormalResearch.ModularBootstrap.Upper.Positivity
