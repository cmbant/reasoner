module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedDesignShift
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionII

/-!
# Near-tip Region II for `D_*` with no hypothesis (`rem:thmU` Step (3))

`rampedD_nearTip_twoG` is `ramped_nearTip_twoG` (`RampedRegionII.lean`) for the ramped comb with all its inputs
discharged: `RampedHoleHyp` (`rampedHoleHyp_D`), the shift cost `S` (`rampedShift_package`, which discharges
`ShiftSumEstimate`), the left curvature error `e_L ≤ C_L λ c'^{3/5}` (`eLeftComb_bounds`) and the relative loss
`E ≤ ε` for `n ≥ N₀(ε)` (`rampedHoleLoss_le`).  For every `0 < ε ≤ 1`:
`c_fl · min(1, 16 η_n²)(1 - ε) - amp ≤ 2g/Lev` on the near-tip range `ξ_I ≤ x`, `N₀ ≤ n ≤ n_cap + 6`, for every
amplitude bound `‖ĥ₀‖ ≤ amp · Lev`.  R6 supplies the amplitude (`nearTip_amp_le`, `ramped_phase_package`) and chooses
`C_mid` through `nearTip_gap_pos`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design FormalResearch.ModularBootstrap.Upper.Window
  Upper.Holes Upper.Hankel Upper.Positivity

lemma log_div_le {n : ℕ} (hn : 1 ≤ n) : Real.log n / n ≤ 3 * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.log_le_rpow_div hn0.le (show (0 : ℝ) < 1 / 3 by norm_num)
  have e : (n : ℝ) ^ (1 / 3 : ℝ) / n = (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    rw [show (-(2 / 3 : ℝ)) = (1 / 3 : ℝ) - 1 by norm_num, Real.rpow_sub hn0, Real.rpow_one]
  calc Real.log n / n ≤ ((n : ℝ) ^ (1 / 3 : ℝ) / (1 / 3)) / n := div_le_div_of_nonneg_right h hn0.le
    _ = 3 * ((n : ℝ) ^ (1 / 3 : ℝ) / n) := by field_simp
    _ = _ := by rw [e]

lemma inv_le_rpow {n : ℕ} (hn : 1 ≤ n) : (n : ℝ)⁻¹ ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)

/-- The relative loss of the near-tip floor is `O(n^{-2/3}) + O(μ)`, `μ = λ c'^{3/5}`. -/
lemma rampedHoleLoss_le {C Cg Cκ C_S C_L : ℝ} (hC : 0 < C) (hCg : 0 < Cg) (hCκ : 0 < Cκ) (hCS : 0 < C_S)
    (hCL : 0 < C_L) {n : ℕ} (hn : 8 ≤ n) {ℓ eL S κ μ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ Cg * μ) (hμ1 : Cg * μ ≤ 1)
    (hμ0 : 0 ≤ μ) (heL : eL ≤ C_L * μ) (hS : S ≤ C_S * ((n : ℝ) ^ (-(2 / 3 : ℝ)) + Real.log n / n) + C_S * μ)
    (hκ : κ = Cκ / n) :
    rampedHoleLoss C ℓ eL S κ n ≤
      (C + 3500 + 4 * C_S + 128 * Cκ ^ 2 + 70 * Cκ) * (n : ℝ) ^ (-(2 / 3 : ℝ)) +
        (C * Cg + 2 * C_L + C_S + 23 * Cg) * μ := by
  have hn1 : 1 ≤ n := by omega
  have hnr : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 := inv_le_rpow hn1
  have h2 := log_div_le hn1
  have hq : 0 ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hκ1 : κ ≤ Cκ * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    rw [hκ, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left h1 hCκ.le
  have hκ2 : κ ^ 2 ≤ Cκ ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    have h3 : κ ^ 2 = Cκ ^ 2 * ((n : ℝ)⁻¹) ^ 2 := by rw [hκ]; field_simp
    rw [h3]
    have : ((n : ℝ)⁻¹) ^ 2 ≤ (n : ℝ)⁻¹ := by
      have : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      nlinarith [inv_nonneg.2 hn0.le]
    exact mul_le_mul_of_nonneg_left (this.trans h1) (by positivity)
  have hℓ2 : ℓ ^ 2 ≤ Cg * μ := by nlinarith
  have hμ' : 0 ≤ Cg * μ := by positivity
  unfold rampedHoleLoss
  have e : (1 : ℝ) / n = (n : ℝ)⁻¹ := one_div _
  have e2 : 3500 / (n : ℝ) = 3500 * (n : ℝ)⁻¹ := div_eq_mul_inv _ _
  rw [e, e2]
  nlinarith [mul_le_mul_of_nonneg_left h1 hC.le, mul_le_mul_of_nonneg_left hℓ hC.le, mul_nonneg hq hCS.le]


/-- **Near-tip Region II for `D_*`, no hypothesis** (`rem:thmU` Step (3); this is `ramped_nearTip_twoG` with its
inputs `RampedHoleHyp`, `S`, `e_L` and the loss discharged): for fixed `C_I, C_mid` and every `0 < ε ≤ 1` there are
`N₀` and `c₀` such that for `c' ≥ c₀`, `d ∈ [0, 1]`, `N₀ ≤ n ≤ n_cap + 6`, `x` in the reference cell `n` with
`x ≥ ξ_* + c'^{-3/5}` and every amplitude bound `‖ĥ₀(c'x²/3)‖ ≤ amp · Lev`:
`c_fl · min(1, 16η_n²)(1 - ε) - amp ≤ 2g/Lev`. -/
theorem rampedD_nearTip_twoG (P : RampedParams) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N0 : ℕ, ∀ᶠ c' : ℝ in atTop, ∀ (d : ℝ), 0 ≤ d → d ≤ 1 → ∀ (n : ℕ) (x amp : ℝ), N0 ≤ n →
      n ≤ nCap P c' + 6 → inCell c' n x → xiStar + c' ^ (-(3 / 5 : ℝ)) ≤ x →
      ‖edgeHankel c' (designProfile c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c'))
          (c' * x ^ 2 / 3)‖ ≤ amp * levComb c' 1 x →
      cFl * min 1 (16 * rampedEta P c' n ^ 2) * (1 - ε) - amp ≤
        twoG c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') x / levComb c' 1 x := by
  obtain ⟨N₀', C, hC, hfl⟩ := ramped_nearTip_twoG
  obtain ⟨Cκ, hCκ, hHole⟩ := rampedHoleHyp_D
  obtain ⟨C_S, hCS, N0s, hN0s, hshift⟩ := rampedShift_package
  obtain ⟨C_L, hCL, hLev⟩ := eLeftComb_bounds
  obtain ⟨cg, Cg, c0g, hcg, hCg, hc0g, hgap⟩ := rampedGap_two_sided
  set Mn := C + 3500 + 4 * C_S + 128 * Cκ ^ 2 + 70 * Cκ with hMn
  set Mc := C * Cg + 2 * C_L + C_S + 23 * Cg with hMc
  have hMn0 : 0 < Mn := by positivity
  have hMc0 : 0 < Mc := by positivity
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, ∀ n : ℕ, N1 ≤ n → 2 * Mn / ε ≤ (n : ℝ) ^ (2 / 3 : ℝ) := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp tendsto_natCast_atTop_atTop
    obtain ⟨N1, hN1⟩ := eventually_atTop.1 (h.eventually_ge_atTop (2 * Mn / ε))
    exact ⟨N1, fun n hn => hN1 n hn⟩
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, ∀ n : ℕ, N2 ≤ n → 98 * Cκ ≤ (n : ℝ) := by
    obtain ⟨N2, hN2⟩ := exists_nat_ge (98 * Cκ)
    exact ⟨N2, fun n hn => hN2.trans (by exact_mod_cast hn)⟩
  refine ⟨max (max (max N₀' N0s) (max N1 N2)) 8, ?_⟩
  filter_upwards [hLev, hfl, hHole P, hshift,
    eventually_ge_atTop (max (max c0g 10000) 1),
    eventually_lam_pow_le (q := 3 / 5) (by norm_num) (show 0 < min (ε / (2 * Mc)) (1 / Cg) by positivity),
    eventually_gt_atTop (0 : ℝ)]
    with c' hLev' hfl' hHole' hshift' hc' hlam hc'0 d hd hd1 n x amp hn hnc hcell hxξ hamp
  have hc'1 : 1 ≤ c' := (le_max_right _ _).trans hc'
  have hc'4 : 10000 ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc')
  have hcg' : c0g ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hn8 : 8 ≤ n := (le_max_right _ _).trans hn
  have hnA : max N₀' N0s ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnB : max N1 N2 ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnN₀ : N₀' ≤ n := (le_max_left _ _).trans hnA
  have hnN0s : N0s ≤ n := (le_max_right _ _).trans hnA
  have hnN1 : N1 ≤ n := (le_max_left _ _).trans hnB
  have hnN2 : N2 ≤ n := (le_max_right _ _).trans hnB
  have hl := lambdaComb_pos' hc'0
  have hnr : (8 : ℝ) ≤ n := by exact_mod_cast hn8
  have hn0 : (0 : ℝ) < n := by linarith
  have hT : 1 ≤ c' ^ (3 / 5 : ℝ) := Real.one_le_rpow hc'1 (by norm_num)
  set μ := lambdaComb c' * c' ^ (3 / 5 : ℝ) with hμ
  have hμ0 : 0 ≤ μ := by positivity
  have hμa : μ ≤ ε / (2 * Mc) := hlam.trans (min_le_left _ _)
  have hμb : μ ≤ 1 / Cg := hlam.trans (min_le_right _ _)
  have hCgμ : Cg * μ ≤ 1 := by
    have := (le_div_iff₀ hCg).1 hμb
    linarith
  have hlmu : lambdaComb c' ≤ μ := by
    have : lambdaComb c' * 1 ≤ lambdaComb c' * c' ^ (3 / 5 : ℝ) := mul_le_mul_of_nonneg_left hT hl.le
    linarith
  obtain ⟨hdx1, hdxk, hS⟩ := hshift' P d hd hd1 n x hnN0s hnc hcell hxξ
  have hH := hHole' d hd hd1 n hn8 (by omega)
  have hxs : xiStar < x := by
    have : 0 < c' ^ (-(3 / 5 : ℝ)) := by positivity
    linarith
  -- e_L
  have heL : eLeftComb c' 1 n 4 x ≤ C_L * μ := by
    obtain ⟨-, hb⟩ := hLev' 1 n 4 x le_rfl hxs
    refine hb.trans ?_
    have hx' : c' ^ (-(3 / 5 : ℝ)) ≤ x - xiStar := by linarith
    have hT0 : 0 < c' ^ (-(3 / 5 : ℝ)) := by positivity
    rw [div_le_iff₀ (by linarith)]
    have hinv : c' ^ (3 / 5 : ℝ) * c' ^ (-(3 / 5 : ℝ)) = 1 := by
      rw [← Real.rpow_add hc'0]; norm_num
    calc C_L * lambdaComb c' = C_L * lambdaComb c' * (c' ^ (3 / 5 : ℝ) * c' ^ (-(3 / 5 : ℝ))) := by
          rw [hinv, mul_one]
      _ = C_L * μ * c' ^ (-(3 / 5 : ℝ)) := by rw [hμ]; ring
      _ ≤ C_L * μ * (x - xiStar) := mul_le_mul_of_nonneg_left hx' (by positivity)
  -- ℓ_n
  have hℓ : siteGap c' n ≤ Cg * μ := by
    obtain ⟨-, hu⟩ := hgap P c' hcg' n (by omega) (by omega)
    refine hu.trans ?_
    have h1 : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    calc Cg * lambdaComb c' * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ Cg * lambdaComb c' * 1 := by gcongr
      _ ≤ Cg * μ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hlmu hCg.le
  have hℓ0 : 0 ≤ siteGap c' n := siteGap_nonneg hc'0 (by omega)
  have hlossle : rampedHoleLoss C (siteGap c' n) (C_L * μ) (C_S * ((n : ℝ) ^ (-(2 / 3 : ℝ)) + Real.log n / n) +
      C_S * μ) (Cκ / n) (n : ℝ) ≤ Mn * (n : ℝ) ^ (-(2 / 3 : ℝ)) + Mc * μ :=
    rampedHoleLoss_le hC hCg hCκ hCS hCL hn8 hℓ0 hℓ hCgμ hμ0 le_rfl le_rfl rfl
  have hn23 : 2 * Mn / ε ≤ (n : ℝ) ^ (2 / 3 : ℝ) := hN1 n hnN1
  have hq : (n : ℝ) ^ (-(2 / 3 : ℝ)) * (n : ℝ) ^ (2 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hn0]; norm_num
  have hqpos : 0 < (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hA : Mn * (n : ℝ) ^ (-(2 / 3 : ℝ)) ≤ ε / 2 := by
    have h := (div_le_iff₀ hε).1 hn23
    have h1 : (n : ℝ) ^ (-(2 / 3 : ℝ)) * (2 * Mn) ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) * ((n : ℝ) ^ (2 / 3 : ℝ) * ε) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h2 : (n : ℝ) ^ (-(2 / 3 : ℝ)) * ((n : ℝ) ^ (2 / 3 : ℝ) * ε) = ε := by
      rw [← mul_assoc, hq, one_mul]
    linarith
  have hB : Mc * μ ≤ ε / 2 := by
    have := (le_div_iff₀ (by positivity)).1 hμa
    linarith
  have hE : rampedHoleLoss C (siteGap c' n) (C_L * μ) (C_S * ((n : ℝ) ^ (-(2 / 3 : ℝ)) + Real.log n / n) +
      C_S * μ) (Cκ / n) (n : ℝ) ≤ ε := by
    refine hlossle.trans ?_
    linarith
  have hκ0 : 0 ≤ Cκ / (n : ℝ) := by positivity
  have hκ98 : Cκ / (n : ℝ) ≤ 1 / 98 := by
    have := hN2 n hnN2
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    linarith
  have hcore := hfl' 1 (nCap P c' + 6) n x (rampedSigma d c') (rampedEta P c') (Cκ / n) (C_L * μ)
    (C_S * ((n : ℝ) ^ (-(2 / 3 : ℝ)) + Real.log n / n) + C_S * μ) amp le_rfl (by omega) hnN₀ (by omega) hcell
    hH hκ0 hκ98 (by positivity) hdx1 hdxk
    (fun k hk1 hkN hk => Or.inr (rampedEta_pos P hc'0 (by omega))) heL hS (hE.trans hε1) hamp
  have hmin : 0 ≤ cFl * min 1 (16 * rampedEta P c' n ^ 2) := by
    have := cFl_gt
    refine mul_nonneg (by linarith) (le_min zero_le_one (by positivity))
  have hlo : cFl * min 1 (16 * rampedEta P c' n ^ 2) * (1 - ε) ≤
      cFl * min 1 (16 * rampedEta P c' n ^ 2) *
        (1 - rampedHoleLoss C (siteGap c' n) (C_L * μ) (C_S * ((n : ℝ) ^ (-(2 / 3 : ℝ)) + Real.log n / n) +
          C_S * μ) (Cκ / n) (n : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hmin
  refine le_trans ?_ hcore
  linarith [hlo]


/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedD_nearTip_twoG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedD_nearTip_twoG

end FormalResearch.ModularBootstrap.Upper.Ramped
