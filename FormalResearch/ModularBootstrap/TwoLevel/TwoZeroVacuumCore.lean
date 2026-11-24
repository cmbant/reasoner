module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroVacuumBand
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroVacuumLobe
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroVacuumWindow

/-!
# The upper bound for `V_c = ∫_0^∞ h₂ V dt` (`upper_transfer.tex`, `ut:T2`, "Far band and assembly")

For the two-zero comb (`h₂ = combProfile c (twoZeroComb d c)`, `V = prob.cardyV (c/12)`, `prob.w = 1`), every compact
family `𝒦` of admissible designs and `ε > 0`: for `c` large and all `d ∈ 𝒦`,
`V_c := ∫_0^∞ h₂ V dt ≤ F_{2,c} (C_* κ ∫_ℝ W_2 du + ε)` (`twoZero_vacuum_core`).

Proof (as in the paper): `split_integral_le_gen` splits at `t_S = c(ξ_* - λS)²/3`, `t_Φ = c(ξ_* + λΦ_{N₁+1})²/3`,
`t_N = c χ_{N₁+1}²/3`, `t_R = c(ξ_* + 3/10)²/3`.  The deep lobe `t ≤ t_S` is positive at `f = 2` and bounded absolutely
(`twoZero_lobe_bound`, `≤ F (C_L S^{-3/2} + ε)`), the window `[t_S, t_Φ]` is compared with the window limit
(`twoZero_window_comb`, `window_part_le`; `∫_{-κΦ}^{κS} W_2 ≤ ∫ W_2` because `W_2 ≥ 0` outside `[q, p]`), the intermediate band
by `twoZero_band_bound` (`≤ F C_T N₁^{-1}`) and the far band by `twoZero_far_bound` (`≤ C_far √c = o(F)`); `S = N₁ = n` is taken
large.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Window.Cardy
open TwoZeroDesign

/-- `∫_a^b f ≤ ∫ f` when `f ≥ 0` outside `[a, b]`. -/
lemma intervalIntegral_le_integral_of_nonneg_outside {f : ℝ → ℝ} (hf : Integrable f) {a b : ℝ} (hab : a ≤ b)
    (hout : ∀ u : ℝ, u ∉ Icc a b → 0 ≤ f u) : ∫ u in a..b, f u ≤ ∫ u, f u := by
  have h1 := integral_add_compl (measurableSet_Icc (a := a) (b := b)) hf
  have h2 : 0 ≤ ∫ u in (Icc a b)ᶜ, f u := setIntegral_nonneg (measurableSet_Icc.compl) fun u hu => hout u hu
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  linarith

/-- The window integral of `W_2` over `[-κΦ, κS]` is at most the full integral. -/
lemma Wr_intervalIntegral_le {n : ℕ} (d : TwoZeroDesign n) (hd : d.Adm) {a b : ℝ} (hab : a ≤ b)
    (ha : a ≤ d.q) (hb : d.p ≤ b) : ∫ u in a..b, d.Wr u ≤ ∫ u, d.Wr u := by
  refine intervalIntegral_le_integral_of_nonneg_outside d.integrable_Wr hab fun u hu => ?_
  rw [mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with h | h
  · exact (d.Wr_pos_of_lt hd (lt_of_lt_of_le h ha)).le
  · exact (d.Wr_pos_of_gt hd (lt_of_le_of_lt hb h)).le

/-- The window integral in the variable `σ`: `∫_{-S}^{Φ} C_*κ² W_2(-κσ) dσ ≤ C_* κ ∫ W_2`
if `-κΦ ≤ q` and `p ≤ κ S`. -/
lemma window_integral_le {n : ℕ} (d : TwoZeroDesign n) (hd : d.Adm) {S Φ : ℝ} (hSΦ : -S ≤ Φ)
    (hq : -(kappaAiry * Φ) ≤ d.q) (hp : d.p ≤ kappaAiry * S) :
    ∫ σ in (-S)..Φ, CStar * kappaAiry ^ 2 * d.Wr (-kappaAiry * σ) ≤ CStar * kappaAiry * ∫ u, d.Wr u := by
  have hκ := kappaAiry_pos
  have hC := CStar_pos
  rw [intervalIntegral.integral_const_mul]
  have h1 : ∫ σ in (-S)..Φ, d.Wr (-kappaAiry * σ) = kappaAiry⁻¹ * ∫ u in (-(kappaAiry * Φ))..(kappaAiry * S), d.Wr u := by
    rw [intervalIntegral.integral_comp_mul_left (fun u => d.Wr u) (by linarith : -kappaAiry ≠ 0)]
    rw [smul_eq_mul]
    have e1 : -kappaAiry * Φ = -(kappaAiry * Φ) := by ring
    have e2 : -kappaAiry * (-S) = kappaAiry * S := by ring
    rw [e1, e2, intervalIntegral.integral_symm, inv_neg]
    ring
  rw [h1]
  have h2 := Wr_intervalIntegral_le d hd (a := -(kappaAiry * Φ)) (b := kappaAiry * S)
    (by nlinarith) hq hp
  have e : CStar * kappaAiry ^ 2 * (kappaAiry⁻¹ * ∫ u in (-(kappaAiry * Φ))..(kappaAiry * S), d.Wr u) =
      CStar * kappaAiry * ∫ u in (-(kappaAiry * Φ))..(kappaAiry * S), d.Wr u := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- Arithmetic of the assembly: the four pieces of the split integral add up to `F (K + ε)`. -/
lemma core_assemble {g : ℝ → ℝ} {tS tΦ tN tR F Wint K m e1 Φ ε CLm : ℝ} (h0 : 0 ≤ tS) (hN : 0 < tN)
    (hSΦ : tS ≤ tΦ) (hNΦ : tN ≤ tΦ) (hΦR : tΦ ≤ tR) (hint : IntegrableOn g (Ioi 0)) (hF : 0 < F)
    (hε : 0 < ε) (hlobe : ∫ t in Ioc 0 tS, |g t| ≤ F * (CLm + ε / 8)) (hCLm : CLm ≤ ε / 8)
    (hwin : ∫ t in tS..tΦ, g t ≤ F * (Wint + e1 * (Φ + m))) (hW : Wint ≤ K) (he1 : e1 * (Φ + m) ≤ ε / 8)
    (hband : ∫ t in Icc tN tR, |g t| ≤ F * (ε / 8)) (hfar : ∫ t in Ici tR, |g t| ≤ ε / 8 * F) :
    ∫ t in Ioi 0, g t ≤ F * (K + ε) := by
  have hs := split_integral_le_gen h0 hN hSΦ hNΦ hΦR hint
  have s1 : F * (CLm + ε / 8) ≤ F * (ε / 4) :=
    mul_le_mul_of_nonneg_left (by linarith) hF.le
  have s2 : F * (Wint + e1 * (Φ + m)) ≤ F * (K + ε / 8) :=
    mul_le_mul_of_nonneg_left (by linarith) hF.le
  nlinarith [mul_pos hF hε]

/-- The window piece of the split integral, from the pointwise window comparison. -/
lemma window_piece {c F e1 m Φ : ℝ} (hc : 0 ≤ c) (hF : 0 < F) {g w : ℝ → ℝ} (hg : ContinuousOn g (Ici 0))
    (hw : Continuous w) (hSΦ : -m ≤ Φ)
    (h : ∀ σ ∈ Icc (-m) Φ, |F⁻¹ * (g (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
      ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c)) - w σ| ≤ e1) :
    ∫ t in (c * (xiStar + lambdaComb c * (-m)) ^ 2 / 3)..(c * (xiStar + lambdaComb c * Φ) ^ 2 / 3), g t ≤
      F * ((∫ σ in (-m)..Φ, w σ) + e1 * (Φ + m)) := by
  refine window_part_le hc hg hw hSΦ fun σ hσ => ?_
  have h2 := (abs_le.mp (h σ hσ)).2
  have h3 : F⁻¹ * (g (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
      ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c)) ≤ w σ + e1 := by linarith
  rw [← div_eq_inv_mul, div_le_iff₀ hF] at h3
  linarith

/-- `|h V| = |h| V` on `t ≥ 0` inside a set integral. -/
lemma setIntegral_abs_profile (prob : FixedWeightProblem) {c : ℝ} (hcS : 12 * prob.totalShift ≤ c)
    (cp : ℝ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) (hs0 : ∀ t ∈ s, 0 ≤ t) :
    ∫ t in s, |cp t * prob.cardyV (c / 12) t| = ∫ t in s, |cp t| * prob.cardyV (c / 12) t :=
  setIntegral_congr_fun hs fun t ht => abs_profile_mul prob hcS cp (hs0 t ht)

/-- The natural number `n` used in the assembly: all smallness conditions hold. -/
lemma exists_core_index {C_L C_T S₀ R ε : ℝ} {N₂ : ℕ} (hε : 0 < ε) :
    ∃ m : ℕ, N₂ ≤ m ∧ S₀ ≤ (m : ℝ) ∧ 1 ≤ m ∧ C_L * (m : ℝ) ^ (-(3 / 2 : ℝ)) ≤ ε / 8 ∧
      C_T * (m : ℝ)⁻¹ ≤ ε / 8 ∧ R / kappaAiry ≤ (m : ℝ) ∧ R / kappaAiry ≤ phiWKB (m + 1) := by
  have h1 := eventually_ge_atTop N₂
  have h2 : ∀ᶠ m : ℕ in atTop, S₀ ≤ (m : ℝ) := tendsto_natCast_atTop_atTop.eventually_ge_atTop S₀
  have h3 := eventually_ge_atTop 1
  have h4 : ∀ᶠ m : ℕ in atTop, C_L * (m : ℝ) ^ (-(3 / 2 : ℝ)) ≤ ε / 8 := by
    have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp
      tendsto_natCast_atTop_atTop).const_mul C_L
    rw [mul_zero] at this
    exact this.eventually_le_const (by positivity)
  have h5 : ∀ᶠ m : ℕ in atTop, C_T * (m : ℝ)⁻¹ ≤ ε / 8 := by
    have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul C_T
    rw [mul_zero] at this
    exact this.eventually_le_const (by positivity)
  have h6 : ∀ᶠ m : ℕ in atTop, R / kappaAiry ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have h7 := phiWKB_succ_tendsto.eventually_ge_atTop (R / kappaAiry)
  obtain ⟨m, a, b, c', d, e, f, g⟩ := (h1.and (h2.and (h3.and (h4.and (h5.and (h6.and h7)))))).exists
  exact ⟨m, a, b, c', d, e, f, g⟩

/-- The ordering of the split points `t_S ≤ t_Φ`, `t_N ≤ t_Φ ≤ t_R`. -/
lemma core_geom {c lam ξ chi Φ m : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hξ : 0 < ξ) (hχ1 : ξ ≤ chi)
    (hχ2 : chi ≤ ξ + lam * Φ) (hlm : lam * m ≤ ξ / 2) (hlΦ : lam * Φ ≤ 3 / 10) (hΦ0 : 0 ≤ Φ)
    (hm0 : 0 ≤ m) :
    c * (ξ + lam * (-m)) ^ 2 / 3 ≤ c * (ξ + lam * Φ) ^ 2 / 3 ∧
      c * chi ^ 2 / 3 ≤ c * (ξ + lam * Φ) ^ 2 / 3 ∧
      c * (ξ + lam * Φ) ^ 2 / 3 ≤ c * (ξ + 3 / 10) ^ 2 / 3 := by
  have hy0 : 0 ≤ ξ + lam * (-m) := by linarith
  have hy1 : 0 ≤ ξ + lam * Φ := by
    have := mul_nonneg hlam.le hΦ0
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ξ + lam * (-m) ≤ ξ + lam * Φ := by
      have := mul_le_mul_of_nonneg_left (show -m ≤ Φ by linarith) hlam.le
      linarith
    have := pow_le_pow_left₀ hy0 h1 2
    have := mul_le_mul_of_nonneg_left this hc.le
    linarith
  · have := pow_le_pow_left₀ (by linarith) hχ2 2
    have := mul_le_mul_of_nonneg_left this hc.le
    linarith
  · have := pow_le_pow_left₀ hy1 (show ξ + lam * Φ ≤ ξ + 3 / 10 by linarith) 2
    have := mul_le_mul_of_nonneg_left this hc.le
    linarith

/-- The far band is `o(F)`. -/
lemma far_small (prob : FixedWeightProblem) {c C_far ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hcbig : C_far / (ε / 8 * twoZeroFConst prob) ≤ c) : C_far * √c ≤ ε / 8 * twoZeroF prob c := by
  rw [twoZeroF_eq_const_mul prob hc]
  have hc32 : c ^ (3 / 2 : ℝ) = c * √c := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hc, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hc32]
  have hFc := twoZeroFConst_pos prob
  have h1 : C_far ≤ ε / 8 * twoZeroFConst prob * c := by
    have := (div_le_iff₀ (by positivity : 0 < ε / 8 * twoZeroFConst prob)).mp hcbig
    linarith
  have h2 := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg c)
  linarith

/-- **`V_c ≤ F_{2,c} (C_* κ V_𝒟 + ε)`** (`ut:T2`, "Far band and assembly"), uniformly on a compact family of admissible designs:
for every `ε > 0`, `c` large and all `d ∈ 𝒦`,
`∫_0^∞ h₂ V dt ≤ F_{2,c} (C_* κ ∫_ℝ W_2 du + ε)`; no sign assumption on `∫ W_2`. -/
theorem twoZero_vacuum_core (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦,
      ∫ t in Ioi 0, combProfile c (d.twoZeroComb c) t * prob.cardyV (c / 12) t ≤
        twoZeroF prob c * (CStar * kappaAiry * (∫ u, d.Wr u) + ε) := by
  have hξ := xiStar_pos
  have hκ := kappaAiry_pos
  obtain ⟨C_L, S₀, hCL, hS₀, hlobe⟩ := twoZero_lobe_bound prob hw hK hA
  obtain ⟨N₂, C_T, hCT, hband⟩ := twoZero_band_bound prob hw (r₀ := 3 / 10) (by norm_num) hK hA
  obtain ⟨C_far, hCfar, hfar⟩ := twoZero_far_bound prob hw (r₀ := 3 / 10) (by norm_num) hK hA
  obtain ⟨R, hR0, hRb⟩ := hK.exists_bound
  obtain ⟨m, hmN, hmS, hm1, hmL, hmT, hmR, hmΦR⟩ :=
    exists_core_index (C_L := C_L) (C_T := C_T) (S₀ := S₀) (R := R) (N₂ := N₂) hε
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ, Φ = phiWKB (m + 1) := ⟨_, rfl⟩
  rw [← hΦdef] at hmΦR
  have hΦ0 : 0 ≤ Φ := by rw [hΦdef]; exact phiWKB_nonneg (by omega)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  obtain ⟨e1, he1⟩ : ∃ e1 : ℝ, e1 = ε / 8 / (Φ + m + 1) := ⟨_, rfl⟩
  have he1pos : 0 < e1 := by rw [he1]; positivity
  have he1le : e1 * (Φ + m) ≤ ε / 8 := by
    rw [he1, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [show 0 < ε by exact hε]
  have hev_c : ∀ᶠ c in atTop, C_far / (ε / 8 * twoZeroFConst prob) ≤ c := eventually_ge_atTop _
  filter_upwards [hlobe (m : ℝ) hmS (ε / 8) (by positivity), hband m hmN, hfar,
    twoZero_window_comb prob hw hK hA hm0 m he1pos, twoZero_integrand_props prob hw hK hA,
    lambda_mul_le (m : ℝ) (half_pos hξ), lambda_mul_le Φ (by norm_num : (0 : ℝ) < 3 / 10),
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (12 * prob.totalShift), hev_c]
    with c hLb hBb hFr hWc hprops hlm hlΦ hc hcS hcbig d hd
  obtain ⟨hcont, hint⟩ := hprops d hd
  have hlam := lambdaComb_pos' hc
  have hFpos := twoZeroF_pos prob hc
  have ha : (1 / 4 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
    linarith
  have hχ1 : xiStar ≤ chiQuantile c ((m + 1 : ℕ) : ℝ) := (chiQuantile_spec hc ha).1
  have hχ2 : chiQuantile c ((m + 1 : ℕ) : ℝ) ≤ xiStar + lambdaComb c * Φ := by
    have h := (siteRadius_bounds hc ha).2
    unfold siteRadius at h
    rw [hΦdef, phiWKB_eq_phiQuantile (m + 1)]
    linarith
  have hχpos : 0 < chiQuantile c ((m + 1 : ℕ) : ℝ) := lt_of_lt_of_le hξ hχ1
  obtain ⟨hSΦ, hNΦ, hΦR⟩ := core_geom hc hlam hξ hχ1 hχ2 hlm hlΦ hΦ0 hm0
  have hwcont : Continuous fun σ : ℝ => CStar * kappaAiry ^ 2 * d.Wr (-kappaAiry * σ) :=
    continuous_const.mul (d.continuous_Wr.comp (by fun_prop))
  have hwin := window_piece (c := c) (F := twoZeroF prob c) (e1 := e1) (m := (m : ℝ)) (Φ := Φ)
    (g := fun t => combProfile c (d.twoZeroComb c) t * prob.cardyV (c / 12) t) hc.le hFpos hcont hwcont
    (by linarith) (fun σ hσ => hWc d hd σ ⟨hσ.1, hσ.2.trans hΦdef.le⟩)
  have hq : -(kappaAiry * Φ) ≤ d.q := by
    have := (abs_le.mp (hRb d hd).2.1).1
    have h1 : R ≤ kappaAiry * Φ := by
      have := (div_le_iff₀ hκ).mp hmΦR
      linarith
    linarith
  have hp : d.p ≤ kappaAiry * (m : ℝ) := by
    have := (abs_le.mp (hRb d hd).1).2
    have h1 : R ≤ kappaAiry * (m : ℝ) := by
      have := (div_le_iff₀ hκ).mp hmR
      linarith
    linarith
  have hWint := window_integral_le d (hA d hd) (S := (m : ℝ)) (Φ := Φ) (by linarith) hq hp
  have hlobe' : ∫ t in Ioc 0 (c * (xiStar + lambdaComb c * (-(m : ℝ))) ^ 2 / 3),
      |combProfile c (d.twoZeroComb c) t * prob.cardyV (c / 12) t| ≤
      twoZeroF prob c * (C_L * (m : ℝ) ^ (-(3 / 2 : ℝ)) + ε / 8) := by
    rw [setIntegral_abs_profile prob hcS _ measurableSet_Ioc (fun t ht => ht.1.le)]
    exact hLb d hd
  have hband' : ∫ t in Icc (c * chiQuantile c ((m + 1 : ℕ) : ℝ) ^ 2 / 3) (c * (xiStar + 3 / 10) ^ 2 / 3),
      |combProfile c (d.twoZeroComb c) t * prob.cardyV (c / 12) t| ≤
      twoZeroF prob c * C_T * (m : ℝ)⁻¹ := by
    have h0 : 0 ≤ c * chiQuantile c ((m + 1 : ℕ) : ℝ) ^ 2 / 3 := by positivity
    rw [setIntegral_abs_profile prob hcS _ measurableSet_Icc (fun t ht => h0.trans ht.1)]
    exact hBb d hd
  have hfar' : ∫ t in Ici (c * (xiStar + 3 / 10) ^ 2 / 3),
      |combProfile c (d.twoZeroComb c) t * prob.cardyV (c / 12) t| ≤ C_far * √c := by
    have h0 : 0 ≤ c * (xiStar + 3 / 10) ^ 2 / 3 := by positivity
    rw [setIntegral_abs_profile prob hcS _ measurableSet_Ici (fun t ht => h0.trans ht)]
    exact hFr d hd
  have hfar'' := far_small prob hc hε hcbig (C_far := C_far)
  refine core_assemble (g := fun t => combProfile c (d.twoZeroComb c) t * prob.cardyV (c / 12) t)
    (CLm := C_L * (m : ℝ) ^ (-(3 / 2 : ℝ))) (K := CStar * kappaAiry * ∫ u, d.Wr u) (m := (m : ℝ)) (e1 := e1)
    (Φ := Φ) (by positivity) (by positivity) hSΦ hNΦ hΦR hint hFpos hε hlobe' hmL hwin hWint he1le ?_ ?_
  · refine hband'.trans ?_
    have : twoZeroF prob c * C_T * (m : ℝ)⁻¹ = twoZeroF prob c * (C_T * (m : ℝ)⁻¹) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hmT hFpos.le
  · exact hfar'.trans hfar''

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_vacuum_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_vacuum_core

end FormalResearch.ModularBootstrap.TwoLevel
