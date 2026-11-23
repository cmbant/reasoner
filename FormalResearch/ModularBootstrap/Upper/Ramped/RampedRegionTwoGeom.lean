module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedDesignNearTip
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedDesignPhase

/-!
# Geometry of Region II for the ramped comb (`rem:thmU` Steps (3), (4))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Steps (3) and (4).  Tip geometry used to place a point
`x ≥ ξ_I = ξ_* + c'^{-3/5}` in a reference cell `n` and to bound the distance of `x` from the displaced sites
(`k ≤ N_Ai`) in the macroscopic range:

* `eventually_chi_le_xiI`: every fixed quantile index `a` has `χ_a ≤ ξ_I` for `c'` large;
* `exists_cell_of_xiI`: for fixed `M ≥ 1`, every `x ≥ ξ_I` lies in a cell `χ_n ≤ x < χ_{n+1}` with `n ≥ M`;
* `siteRadius_ge_const`: `χ_a - ξ_* ≥ r(s)` for `a ≥ s c'` (the lower tip bound of `r_1'` in the TeX, with the
  Langer chart replaced by `K0`);
* `eventually_siteRadius_nAi_le`: the displaced sites `k ≤ N_Ai` satisfy `χ_k - ξ_* ≤ r` for `c'` large.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design Upper.Holes Upper.Positivity

lemma lambda_mul_phi_le {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a) :
    lambdaComb c' * phiQuantile a ≤ (a / (kTip * c')) ^ (2 / 3 : ℝ) := by
  have hk := kTip_pos
  have hkc : 0 < kTip * c' := by positivity
  have h0 : 0 ≤ a - 1 / 4 := by linarith
  unfold lambdaComb phiQuantile
  rw [Real.rpow_neg hkc.le, ← div_eq_inv_mul, ← Real.div_rpow h0 hkc.le]
  exact Real.rpow_le_rpow (div_nonneg h0 hkc.le) (div_le_div_of_nonneg_right (by linarith) hkc.le)
    (by norm_num)

/-- Each fixed quantile `χ_a` lies below `ξ_I = ξ_* + c'^{-3/5}` for `c'` large. -/
theorem eventually_chi_le_xiI {a : ℝ} (ha : 1 / 4 ≤ a) :
    ∀ᶠ c' : ℝ in atTop, chiQuantile c' a ≤ xiStar + c' ^ (-(3 / 5 : ℝ)) := by
  have hΦ : 0 ≤ phiQuantile a := by unfold phiQuantile; exact Real.rpow_nonneg (by linarith) _
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_lam_pow_le (q := 3 / 5) (by norm_num) (show 0 < 1 / (phiQuantile a + 1) by positivity)]
    with c' hc' hlam
  have hb := (siteRadius_bounds hc' ha).2
  have hT : 0 < c' ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos hc' _
  have hinv : c' ^ (-(3 / 5 : ℝ)) * c' ^ (3 / 5 : ℝ) = 1 := by
    rw [← Real.rpow_add hc']; norm_num
  have hl : lambdaComb c' * c' ^ (3 / 5 : ℝ) * (phiQuantile a + 1) ≤ 1 := by
    have := (le_div_iff₀ (by positivity : 0 < phiQuantile a + 1)).1 hlam
    linarith
  have hrp : 0 < c' ^ (-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos hc' _
  have : lambdaComb c' * phiQuantile a ≤ c' ^ (-(3 / 5 : ℝ)) := by
    have h1 : lambdaComb c' * phiQuantile a ≤ lambdaComb c' * (phiQuantile a + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (lambdaComb_pos' hc').le
    have h2 : lambdaComb c' * (phiQuantile a + 1) =
        c' ^ (-(3 / 5 : ℝ)) * (lambdaComb c' * c' ^ (3 / 5 : ℝ) * (phiQuantile a + 1)) := by
      calc lambdaComb c' * (phiQuantile a + 1)
          = (c' ^ (-(3 / 5 : ℝ)) * c' ^ (3 / 5 : ℝ)) * (lambdaComb c' * (phiQuantile a + 1)) := by
            rw [hinv, one_mul]
        _ = _ := by ring
    have h3 : c' ^ (-(3 / 5 : ℝ)) * (lambdaComb c' * c' ^ (3 / 5 : ℝ) * (phiQuantile a + 1)) ≤
        c' ^ (-(3 / 5 : ℝ)) * 1 := mul_le_mul_of_nonneg_left hl hrp.le
    linarith
  unfold siteRadius at hb
  linarith

/-- For `M ≥ 1` and `c'` large, every `x ≥ ξ_I` lies in a reference cell `n ≥ M`. -/
theorem exists_cell_of_xiI (M : ℕ) (hM : 1 ≤ M) :
    ∀ᶠ c' : ℝ in atTop, ∀ x : ℝ, xiStar + c' ^ (-(3 / 5 : ℝ)) ≤ x →
      ∃ n : ℕ, M ≤ n ∧ inCell c' n x := by
  have hM' : (1 / 4 : ℝ) ≤ (M : ℝ) := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  filter_upwards [eventually_chi_le_xiI hM', eventually_gt_atTop (0 : ℝ)] with c' h hc' x hx
  exact exists_inCell hc' hM (h.trans hx)

/-- **Lower tip bound**: for every `s > 0` there is `r > 0` with `χ_a - ξ_* ≥ r` for all `a ≥ s c'`, `c'` large. -/
theorem siteRadius_ge_const {s : ℝ} (hs : 0 < s) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ c' : ℝ in atTop, ∀ a : ℝ, s * c' ≤ a → r ≤ siteRadius c' a := by
  have hk := kTip_pos
  have hc1 := c1K0_pos
  set s0 : ℝ := kTip * (3 / (4 * c1K0)) ^ (3 / 2 : ℝ) with hs0
  set s' : ℝ := min s s0 with hs'
  have hs'0 : 0 < s' := lt_min hs (by positivity)
  refine ⟨(1 / 2) * (s' / (2 * kTip)) ^ (2 / 3 : ℝ), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 / s'), eventually_gt_atTop (0 : ℝ)] with c' hc'1 hc'0 a ha
  set a' : ℝ := s' * c' with ha'
  have ha'1 : 1 ≤ a' := by
    have := (div_le_iff₀ hs'0).1 hc'1
    rw [ha']; linarith
  have ha'a : a' ≤ a := (mul_le_mul_of_nonneg_right (min_le_left _ _) hc'0.le).trans ha
  have ha'4 : (1 / 4 : ℝ) ≤ a' := by linarith
  have hmono : siteRadius c' a' ≤ siteRadius c' a := by
    unfold siteRadius
    have := chiQuantile_mono_le hc'0 ha'4 ha'a
    linarith
  refine le_trans ?_ hmono
  obtain ⟨hlow, -⟩ := siteRadius_bounds hc'0 ha'4
  set y : ℝ := lambdaComb c' * phiQuantile a' with hy
  have hkc : 0 < kTip * c' := by positivity
  have hy0 : 0 ≤ y := by
    have := lambdaComb_pos' hc'0
    have h2 : 0 ≤ phiQuantile a' := by
      unfold phiQuantile; exact Real.rpow_nonneg (by linarith) _
    rw [hy]; positivity
  have hyup : y ≤ 3 / (4 * c1K0) := by
    refine (lambda_mul_phi_le hc'0 ha'4).trans ?_
    have e : a' / (kTip * c') = s' / kTip := by rw [ha']; field_simp
    rw [e]
    have h1 : s' / kTip ≤ (3 / (4 * c1K0)) ^ (3 / 2 : ℝ) := by
      rw [div_le_iff₀ hk]
      calc s' ≤ s0 := min_le_right _ _
        _ = (3 / (4 * c1K0)) ^ (3 / 2 : ℝ) * kTip := by rw [hs0]; ring
    calc (s' / kTip) ^ (2 / 3 : ℝ) ≤ ((3 / (4 * c1K0)) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) :=
          Real.rpow_le_rpow (by positivity) h1 (by norm_num)
      _ = 3 / (4 * c1K0) := by
          rw [← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one]
  have hylow : (s' / (2 * kTip)) ^ (2 / 3 : ℝ) ≤ y := by
    have h1 : (a' / 2) ^ (2 / 3 : ℝ) ≤ phiQuantile a' := by
      unfold phiQuantile
      exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have e : lambdaComb c' * (a' / 2) ^ (2 / 3 : ℝ) = (s' / (2 * kTip)) ^ (2 / 3 : ℝ) := by
      unfold lambdaComb
      rw [Real.rpow_neg hkc.le, ← div_eq_inv_mul, ← Real.div_rpow (by linarith) hkc.le]
      congr 1
      rw [ha']; field_simp
    rw [← e, hy]
    exact mul_le_mul_of_nonneg_left h1 (lambdaComb_pos' hc'0).le
  have hq : 2 * c1K0 / 3 * y ≤ 1 / 2 := by
    have : y * (4 * c1K0) ≤ 3 := by
      have := (le_div_iff₀ (by positivity : 0 < 4 * c1K0)).1 hyup
      linarith
    nlinarith
  have hfinal : y / 2 ≤ y * (1 - 2 * c1K0 / 3 * y) := by nlinarith
  have : y * (1 - 2 * c1K0 / 3 * y) ≤ siteRadius c' a' := hlow
  linarith

/-- The displaced sites `k ≤ N_Ai` (`k ≥ 1`) satisfy `χ_k - ξ_* ≤ r` for `c'` large. -/
theorem eventually_siteRadius_nAi_le {r : ℝ} (hr : 0 < r) :
    ∀ᶠ c' : ℝ in atTop, ∀ k : ℕ, 1 ≤ k → k ≤ nAi c' → siteRadius c' k ≤ r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_lam_pow_le (q := 1 / 9) (by norm_num) (show 0 < r / 2 by positivity)] with c' hc'1 hlam k hk hkn
  have hc'0 : 0 < c' := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb := (siteRadius_bounds hc'0 (by linarith : (1 / 4 : ℝ) ≤ k)).2
  have hnA := nAi_le hc'1
  have hkA : (k : ℝ) ≤ 2 * c' ^ (1 / 6 : ℝ) := (by exact_mod_cast hkn : (k : ℝ) ≤ nAi c').trans hnA
  have hΦ : phiQuantile (k : ℝ) ≤ 2 * c' ^ (1 / 9 : ℝ) := by
    unfold phiQuantile
    have h1 : ((k : ℝ) - 1 / 4) ^ (2 / 3 : ℝ) ≤ (2 * c' ^ (1 / 6 : ℝ)) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have h2 : (2 * c' ^ (1 / 6 : ℝ)) ^ (2 / 3 : ℝ) = (2 : ℝ) ^ (2 / 3 : ℝ) * c' ^ (1 / 9 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hc'0.le _), ← Real.rpow_mul hc'0.le]
      norm_num
    have h3 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (2 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have h4 : 0 ≤ c' ^ (1 / 9 : ℝ) := Real.rpow_nonneg hc'0.le _
    nlinarith
  have hl := lambdaComb_pos' hc'0
  calc siteRadius c' k ≤ lambdaComb c' * phiQuantile k := hb
    _ ≤ lambdaComb c' * (2 * c' ^ (1 / 9 : ℝ)) := mul_le_mul_of_nonneg_left hΦ hl.le
    _ = 2 * (lambdaComb c' * c' ^ (1 / 9 : ℝ)) := by ring
    _ ≤ r := by linarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.eventually_chi_le_xiI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eventually_chi_le_xiI

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.exists_cell_of_xiI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_cell_of_xiI

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.siteRadius_ge_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms siteRadius_ge_const

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.eventually_siteRadius_nAi_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eventually_siteRadius_nAi_le

end FormalResearch.ModularBootstrap.Upper.Ramped
