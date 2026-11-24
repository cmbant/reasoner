module

public import FormalResearch.ModularBootstrap.Upper.Positivity.RegionII
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroCombK7
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroTransfer

/-!
# Region II for the two-zero comb: Lemma II-F at `f = 2`, `r = 1` (`upper_transfer.tex`, `ut:IIF`, `ut:T2`)

Source: `upper_transfer.tex`, Lemma II-F (`ut:IIF`) and the "Region II" paragraph of the proof of Theorem `ut:T2`.
The test is `h₂ = sech²(πb/2) B₂`, `B₂ = T_{χ(p)} B₁` (`twoZeroComb`), `g = ½(h₂ - ĥ₂)`, and the level is
`Lev₂ = T_{χ(p)}(x) · Lev^{(2)}(x)` (`levComb c' 2`).  For every compact family `𝒦` of admissible designs, `c'` large,
`d ∈ 𝒦` and every real `x ≥ ξ_* + c'^{-2/5}` (no upper limit on `x`):

* `twoZeroT_ratio_le`: `T_{χ(p)}(x) > 0` and `T_{ξ_*}(x) ≤ (1 + 1/1000) T_{χ(p)}(x)` (the `T_{χ(p)}/T_{ξ_*} = 1 + o(1)` of
  `eq:ut:T2-IIa`, one-sided and for all `x`, not only `x ≤ ξ_* + 1`);
* `vRhoInfty_add_half`: `vρ∞(x; n + 1/2) = vρ∞(x; n) T_{ξ_*}(x)`, the shift `n_eff = n₁ - r/2` of the exponent;
* `twoZero_hat_bound`: `‖ĥ₂(c'x²/3)‖ ≤ 0.55 · 1.02 · Lev₂(x)` (from `twoZeroComb_phi_transform`, `|T| = 1` on the
  saddle line, `combAmplitude_le_vRhoInfty_mul_levComb` and `vRhoInfty_le` at `n_eff = 5/4 ≥ 3/4`);
* `twoZero_regionII`: `2 g(c'x²/3) / Lev₂(x) ≥ 13/100`, via the floor `proposition_II_floor` of `h₀^D/Lev^{(2)}`
  (the floor of `ut:II`, unchanged by the real factor `T_{χ(p)} > 0`);
* `twoZero_regionII_pos`: `g > 0` on `x ≥ ξ_* + c'^{-2/5}`, uniformly on `𝒦` (`twoZero_regionII_nonvacuous`: for an
  admissible design).

All results are proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Positivity
  FormalResearch.ModularBootstrap.Upper.Holes FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle FormalResearch.ModularBootstrap.Upper.Window.Tail

/-! ### 1. The real factor: monotonicity and Lipschitz dependence on the site -/

lemma tFac_mono {χ x y : ℝ} (hχ : 0 ≤ χ) (hχx : χ ≤ x) (hxy : x ≤ y) : tFac χ x ≤ tFac χ y := by
  have hpi := Real.pi_pos
  unfold tFac
  have h1 : 0 ≤ Real.tanh (π * (x - χ) / 2) := tanh_nonneg_of_nonneg (by nlinarith)
  have h2 : 0 ≤ Real.tanh (π * (x + χ) / 2) := tanh_nonneg_of_nonneg (by nlinarith)
  have h3 : 0 ≤ Real.tanh (π * (y - χ) / 2) := tanh_nonneg_of_nonneg (by nlinarith)
  exact mul_le_mul (tanh_mono_real (by nlinarith)) (tanh_mono_real (by nlinarith)) h2 h3

/-- `|T_χ(x) - T_ξ(x)| ≤ π |χ - ξ|` for `0 ≤ χ, ξ ≤ x`. -/
lemma tFac_sub_le {χ ξ x : ℝ} (hχ : 0 ≤ χ) (hξ : 0 ≤ ξ) (hχx : χ ≤ x) (hξx : ξ ≤ x) :
    |tFac χ x - tFac ξ x| ≤ π * |χ - ξ| := by
  have hpi := Real.pi_pos
  have ha : 0 ≤ π * (x - χ) / 2 := by have : 0 ≤ x - χ := by linarith
                                      positivity
  have hb : 0 ≤ π * (x + χ) / 2 := by have : 0 ≤ x + χ := by linarith
                                      positivity
  have ha0 : 0 ≤ π * (x - ξ) / 2 := by have : 0 ≤ x - ξ := by linarith
                                       positivity
  have hb0 : 0 ≤ π * (x + ξ) / 2 := by have : 0 ≤ x + ξ := by linarith
                                       positivity
  have h1 := abs_tanh_sub_le ha ha0
  have h2 := abs_tanh_sub_le hb hb0
  have e1 : π * (x - χ) / 2 - π * (x - ξ) / 2 = π * (ξ - χ) / 2 := by ring
  have e2 : π * (x + χ) / 2 - π * (x + ξ) / 2 = π * (χ - ξ) / 2 := by ring
  rw [e1, abs_div, abs_mul, abs_of_pos hpi, abs_two, abs_sub_comm ξ χ] at h1
  rw [e2, abs_div, abs_mul, abs_of_pos hpi, abs_two] at h2
  unfold tFac
  set u := Real.tanh (π * (x - χ) / 2)
  set v := Real.tanh (π * (x + χ) / 2)
  set u0 := Real.tanh (π * (x - ξ) / 2)
  set v0 := Real.tanh (π * (x + ξ) / 2)
  have hv : |v| ≤ 1 := (Real.abs_tanh_lt_one _).le
  have hu0 : |u0| ≤ 1 := (Real.abs_tanh_lt_one _).le
  have hid : u * v - u0 * v0 = (u - u0) * v + u0 * (v - v0) := by ring
  rw [hid]
  calc |(u - u0) * v + u0 * (v - v0)| ≤ |(u - u0) * v| + |u0 * (v - v0)| := abs_add_le _ _
    _ = |u - u0| * |v| + |u0| * |v - v0| := by rw [abs_mul, abs_mul]
    _ ≤ π * |χ - ξ| / 2 * 1 + 1 * (π * |χ - ξ| / 2) :=
        add_le_add (mul_le_mul h1 hv (abs_nonneg _) (by positivity))
          (mul_le_mul hu0 h2 (abs_nonneg _) zero_le_one)
    _ = π * |χ - ξ| := by ring

/-- The shift of the exponent in the Region-II saddle ratio: `vρ∞(x; n + 1/2) = vρ∞(x; n) T_{ξ_*}(x)`. -/
lemma vRhoInfty_add_half {x : ℝ} (hx : xiStar < x) (n : ℝ) :
    vRhoInfty x (n + 1 / 2) = vRhoInfty x n * tFac xiStar x := by
  have hT : 0 < tFac xiStar x := tFac_pos xiStar_pos.le hx
  have hT' : tanhTipK8 x = tFac xiStar x := rfl
  unfold vRhoInfty
  rw [hT', show 2 * (n + 1 / 2) = 2 * n + 1 by ring, Real.rpow_add hT, Real.rpow_one]
  ring

/-! ### 2. The factor `T_{χ(p)}` against `T_{ξ_*}` on Region II, uniformly on a compact family -/

namespace TwoZeroDesign

variable {n : ℕ}

/-- **`T_{χ(p)}/T_{ξ_*} = 1 + o(1)` on Region II** (`eq:ut:T2-IIa`): for `c'` large, `d ∈ 𝒦` and every
`x ≥ ξ_* + c'^{-2/5}`, `T_{χ(p)}(x) > 0` and `T_{ξ_*}(x) ≤ (1001/1000) T_{χ(p)}(x)`. -/
theorem twoZeroT_ratio_le {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) :
    ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x →
      0 < tFac (d.chiP c') x ∧ tFac xiStar x ≤ (1001 / 1000 : ℝ) * tFac (d.chiP c') x := by
  obtain ⟨c₁, Sg0, hc₁, hSg0, hbeyond⟩ := twoZeroT_ge_beyond hK
  obtain ⟨S, hS0, hS⟩ := hK.exists_sigmaP_bound
  have e1 := eventually_mul_lambda_le Sg0 1 one_pos
  have e2 := eventually_mul_lambda_le S 1 one_pos
  have e3 := eventually_mul_lambda_le (π * S) (c₁ / 1000) (by positivity)
  filter_upwards [hbeyond, eventually_lambda_small S, e1, e2, e3, eventually_ge_atTop (1 : ℝ)]
    with c' hb ⟨hl, hlS⟩ he1 he2 he3 hc1 d hd x hx
  set u : ℝ := c' ^ (-(2 / 5 : ℝ)) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hc1) _
  have hu1 : u ≤ 1 := rpow_neg_two_fifths_le_one hc1
  have hχge : xiStar / 2 ≤ d.chiP c' := chiP_ge (hS d hd) hl hlS
  have hσle : |d.sigmaP| ≤ S := hS d hd
  have hdiff : |d.chiP c' - xiStar| ≤ lambdaComb c' * S := by
    have : d.chiP c' - xiStar = lambdaComb c' * d.sigmaP := by unfold chiP; ring
    rw [this, abs_mul, abs_of_pos hl]
    exact mul_le_mul_of_nonneg_left hσle hl.le
  have hlSu : lambdaComb c' * S ≤ u := by nlinarith only [he2, hu0]
  have hχu : d.chiP c' ≤ xiStar + u := by
    have := (abs_le.mp hdiff).2
    linarith
  have hχx : d.chiP c' ≤ x := by linarith
  have hlow : c₁ * u ≤ tFac (d.chiP c') x := by
    set x₁ : ℝ := min x (xiStar + 1) with hx₁
    have hx₁u : xiStar + u ≤ x₁ := le_min hx (by linarith)
    have hx₁le : x₁ ≤ x := min_le_left _ _
    have hS0' : lambdaComb c' * Sg0 ≤ u := by nlinarith only [he1, hu0]
    have h1 := hb d hd x₁ (by linarith) (min_le_right _ _)
    have h2 : tFac (d.chiP c') x₁ ≤ tFac (d.chiP c') x :=
      tFac_mono (by linarith [xiStar_pos]) (by linarith) hx₁le
    have h3 : c₁ * u ≤ c₁ * (x₁ - xiStar) := mul_le_mul_of_nonneg_left (by linarith) hc₁.le
    linarith
  have hTpos : 0 < tFac (d.chiP c') x := lt_of_lt_of_le (by positivity) hlow
  refine ⟨hTpos, ?_⟩
  have hLip := tFac_sub_le (χ := d.chiP c') (ξ := xiStar) (x := x) (by linarith [xiStar_pos])
    xiStar_pos.le hχx (by linarith)
  have hsmall : π * |d.chiP c' - xiStar| ≤ c₁ / 1000 * u :=
    le_trans (mul_le_mul_of_nonneg_left hdiff Real.pi_pos.le) (by nlinarith only [he3])
  have := (abs_le.mp hLip).1
  have h4 : c₁ / 1000 * u ≤ tFac (d.chiP c') x / 1000 := by nlinarith only [hlow]
  nlinarith only [this, hsmall, h4]

end TwoZeroDesign

open TwoZeroDesign

/-! ### 3. The test `h₂`, its transform bound and Region II -/

/-- `2 g(c'x²/3) = h₂(x) - ĥ₂(c'x²/3)` (real part) for the two-zero test `h₂ = sech² · T_{χ(p)} B₁`. -/
noncomputable def TwoZeroDesign.twoZeroG {n : ℕ} (d : TwoZeroDesign n) (c' x : ℝ) : ℝ :=
  (sechSqProfile (x : ℂ) * d.twoZeroComb c' (x : ℂ) -
    edgeHankel c' (fun b => sechSqProfile b * d.twoZeroComb c' b) (c' * x ^ 2 / 3)).re

/-- **Region II, transform bound** (`ut:IIF`, second display, `f = 2`, `r = 1`, `n_eff = 5/4`): on `x ≥ ξ_* + c'^{-2/5}`
right of the node `χ_{5/2}`, `‖ĥ₂(c'x²/3)‖ ≤ 0.55 · 1.02 · T_{χ(p)}(x) Lev^{(2)}(x)`. -/
theorem twoZero_hat_bound {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x →
      chiQuantile c' (((2 : ℕ) : ℝ) + 1 / 2) < x →
      ‖edgeHankel c' (fun b => sechSqProfile b * d.twoZeroComb c' b) (c' * x ^ 2 / 3)‖ ≤
        (55 / 100 : ℝ) * (102 / 100) * (tFac (d.chiP c') x * levComb c' 2 x) := by
  obtain ⟨C, hC, hΦ⟩ := twoZeroComb_phi_transform hK hA (θ := 2 / 5) (by norm_num) (by norm_num)
  have hexp : (-1 + 3 * (2 / 5 : ℝ) / 2) = -(2 / 5 : ℝ) := by norm_num
  have e8 : ∀ᶠ c' in atTop, C * c' ^ (-(2 / 5 : ℝ)) ≤ 1 / 50 :=
    (tendsto_rpow_neg_two_fifths.const_mul C).eventually_le_const (by norm_num)
  filter_upwards [hΦ, e8, twoZeroT_ratio_le hK, eventually_ge_atTop (1 : ℝ)]
    with c' hΦc he8 hrat hc1 d hd x hx hnode
  have hc' : 0 < c' := lt_of_lt_of_le one_pos hc1
  have hu0 : 0 < c' ^ (-(2 / 5 : ℝ)) := Real.rpow_pos_of_pos hc' _
  have hxi : xiStar < x := by linarith only [hx, hu0]
  obtain ⟨hTpos, hTle⟩ := hrat d hd x hx
  have hΦx := hΦc d hd x hx
  rw [hexp] at hΦx
  have hA1 := combAmplitude_le_vRhoInfty_mul_levComb hc' (f := 2) (by norm_num) hnode
  have hn1 : n1Comb 2 = 5 / 4 + 1 / 2 := by unfold n1Comb; norm_num
  rw [hn1, vRhoInfty_add_half hxi] at hA1
  obtain ⟨hv1, hv2, hv3, -⟩ := vRhoInfty_le (n₁ := 5 / 4) (by norm_num) hxi
  have hv : vRhoInfty x (5 / 4) ≤ 542 / 1000 := by linarith only [hv1, hv2, hv3]
  have hlev := levComb_pos c' 2 x
  have hTξ : 0 ≤ tFac xiStar x := (tFac_pos xiStar_pos.le hxi).le
  have hA0 : 0 ≤ combAmplitude c' x := by
    unfold combAmplitude sdvPrefactor; positivity
  have hA2 : combAmplitude c' x ≤ (542 / 1000 : ℝ) * (tFac xiStar x * levComb c' 2 x) := by
    calc combAmplitude c' x ≤ vRhoInfty x (5 / 4) * tFac xiStar x * levComb c' 2 x := hA1
      _ = vRhoInfty x (5 / 4) * (tFac xiStar x * levComb c' 2 x) := by ring
      _ ≤ (542 / 1000 : ℝ) * (tFac xiStar x * levComb c' 2 x) :=
          mul_le_mul_of_nonneg_right hv (mul_nonneg hTξ hlev.le)
  have hTL : tFac xiStar x * levComb c' 2 x ≤ (1001 / 1000 : ℝ) * (tFac (d.chiP c') x * levComb c' 2 x) := by
    nlinarith only [hTle, hlev]
  have hw : 1 + C * c' ^ (-(2 / 5 : ℝ)) ≤ 102 / 100 := by linarith only [he8]
  calc _ ≤ combAmplitude c' x * (1 + C * c' ^ (-(2 / 5 : ℝ))) := hΦx
    _ ≤ combAmplitude c' x * (102 / 100) := mul_le_mul_of_nonneg_left hw hA0
    _ ≤ (542 / 1000 : ℝ) * (tFac xiStar x * levComb c' 2 x) * (102 / 100) :=
        mul_le_mul_of_nonneg_right hA2 (by norm_num)
    _ ≤ (542 / 1000 : ℝ) * ((1001 / 1000 : ℝ) * (tFac (d.chiP c') x * levComb c' 2 x)) * (102 / 100) := by
        gcongr
    _ ≤ _ := by
        have : 0 ≤ tFac (d.chiP c') x * levComb c' 2 x := (mul_pos hTpos hlev).le
        nlinarith only [this]

/-- **Lemma II-F in Region II for the two-zero comb** (`ut:IIF` with `f = 2`, `r = 1`, `n_eff = 5/4`; `ut:T2`,
"Region II"): for every compact family `𝒦` of admissible designs, `c'` large, `d ∈ 𝒦` and every real
`x ≥ ξ_* + c'^{-2/5}`, `2 g(c'x²/3) / Lev₂(x) ≥ 13/100`, `Lev₂ = T_{χ(p)}(x) Lev^{(2)}(x) > 0`
(`twoZeroG = 2 g`). -/
theorem twoZero_regionII {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x →
      13 / 100 ≤ d.twoZeroG c' x / (tFac (d.chiP c') x * levComb c' 2 x) := by
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  filter_upwards [proposition_II_floor 2 (n + 2) (by norm_num) (by omega) M E,
    twoZero_hat_bound hK hA, twoZeroT_ratio_le hK, eventually_gt_atTop (0 : ℝ)]
    with c' hfl hhat hrat hc' d hd x hx
  have hl : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _
  obtain ⟨hσ, hε⟩ := comb_family_bounds hl (hb d hd)
  obtain ⟨hnode, R, r, hR, hr, hcomb, hf1, hlog⟩ := hfl d.sigmaSeq (fun k => lambdaComb c' * d.epsHatSite k) hσ hε x hx
  obtain ⟨hTpos, -⟩ := hrat d hd x hx
  set T : ℝ := tFac (d.chiP c') x with hT
  have hlev := levComb_pos c' 2 x
  have hsech : 0 < 1 / Real.cosh (π * x / 2) ^ 2 := by positivity
  have hcomb2 : d.twoZeroComb c' (x : ℂ) = ((T * r : ℝ) : ℂ) := by
    unfold twoZeroComb
    rw [tFac_eq]
    have : d.comb c' (x : ℂ) = (r : ℂ) := hcomb
    rw [this]; push_cast; rfl
  have hre : (sechSqProfile (x : ℂ) * d.twoZeroComb c' (x : ℂ)).re =
      1 / Real.cosh (π * x / 2) ^ 2 * (T * r) := by
    rw [sechSqProfile_ofReal, hcomb2, ← Complex.ofReal_mul, Complex.ofReal_re]
  unfold twoZeroG
  rw [Complex.sub_re, hre]
  refine regionII_assemble (mul_pos hTpos hlev) hsech.le (mul_pos hTpos hR) (mul_pos hTpos hr) ?_ rfl ?_ rfl
    (Complex.re_le_norm _) (hhat d hd x hx hnode)
  · have : 1 / Real.cosh (π * x / 2) ^ 2 * (T * R) / (T * levComb c' 2 x) =
        1 / Real.cosh (π * x / 2) ^ 2 * R / levComb c' 2 x := by field_simp
    rw [this]
    exact (le_div_iff₀ hlev).mpr hf1
  · rw [mul_div_mul_left r R hTpos.ne']; exact hlog

/-- **Positivity of `g` in Region II**: `g > 0` on `x ≥ ξ_* + c'^{-2/5}`, uniformly on a compact family. -/
theorem twoZero_regionII_pos {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x → 0 < d.twoZeroG c' x := by
  filter_upwards [twoZero_regionII hK hA, twoZeroT_ratio_le hK] with c' h hr d hd x hx
  have hpos := mul_pos (hr d hd x hx).1 (levComb_pos c' 2 x)
  have := h d hd x hx
  rw [le_div_iff₀ hpos] at this
  linarith only [this, hpos]

/-- Non-vacuity: admissible designs exist, and for one of them (the singleton compact family) `twoZero_regionII_pos`
is a statement about an actual positive function on Region II. -/
theorem twoZero_regionII_nonvacuous :
    ∃ d : TwoZeroDesign 1, d.Adm ∧ ∀ᶠ c' : ℝ in atTop, ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x →
      0 < d.twoZeroG c' x := by
  obtain ⟨d, hd⟩ := twoZeroDesign_adm_nonempty
  refine ⟨d, hd, ?_⟩
  filter_upwards [twoZero_regionII_pos (isCompactFamily_singleton d)
    (fun e he => by rw [Set.mem_singleton_iff.mp he]; exact hd)] with c' h
  exact fun x hx => h d rfl x hx

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDesign.twoZeroT_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoZeroDesign.twoZeroT_ratio_le

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_hat_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_hat_bound

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_regionII' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_regionII

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_regionII_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_regionII_pos

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.vRhoInfty_add_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vRhoInfty_add_half

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_regionII_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_regionII_nonvacuous

end FormalResearch.ModularBootstrap.TwoLevel
