/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerVJets

/-!
# Inner Jacobian factor `H(y)` and `J₁ - J₀` bound (`fct:inner-symbols` (b3))

Paper I (`constant_terms_five.tex`), Proof of `(fct:inner-symbols)` (b3):
* `fctH y := √(kfun y / (2 * nfun y))`: smooth on `(-δ_H, δ_H)`, `fctH 0 = 1`,
  `HasDerivAt fctH (-(7 * π^2 / 240)) 0`, and `√(uctMderiv τ / (2 * uctM τ)) = τ^{-1/2} * fctH (τ^2)`;
* `concreteMt_zero`: `concreteMt 0 = 7 * π^4 / 7200`;
* `fctInner_J1_sub_J0_sym`: `Jfun S.V fctH (τ₁^2) (q₁, Y(u)) - Jfun S.V fctH (τ₁^2) (q₀, Y(u)) ∈ 𝒮⁸(C c^{-17/12})`
  via `ChartSetup.dJ_jets` and `ZeroPath`/`A_comp`.

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real ContDiff BigOperators
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment

namespace FormalResearch.SignUncertainty

local notation "τs" => (12 / π ^ 2) ^ (1 / 3 : ℝ)

/-! ### 1. The smooth factor `H(y) = √(kfun y / (2 * nfun y))` -/

/-- `H(y) = √(kfun y / (2 * nfun y))` appearing in `√(m'(τ)/(2 m(τ))) = τ^{-1/2} H(τ²)`. -/
noncomputable def fctH (y : ℝ) : ℝ :=
  Real.sqrt (CtCfu.kfun y / (2 * CtCfu.nfun y))

lemma fctH_zero : fctH 0 = 1 := by
  unfold fctH
  rw [CtCfu.kfun_zero, CtCfu.nfun_zero]
  have hpi : π ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  have : π ^ 2 / 6 / (2 * (π ^ 2 / 12)) = 1 := by field_simp [hpi]; ring
  rw [this, Real.sqrt_one]

lemma hasDerivAt_fctH_zero : HasDerivAt fctH (-(7 * π ^ 2 / 240)) 0 := by
  have hpi : π ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  have hk := CtCfu.hasDerivAt_kfun_zero
  have hn := CtCfu.hasDerivAt_nfun_zero
  have hn2 : HasDerivAt (fun y => 2 * CtCfu.nfun y) (-(7 * π ^ 4 / 720)) 0 := by
    have := hn.const_mul (2 : ℝ)
    convert this using 1
    ring
  have hne : (2 * CtCfu.nfun 0) ≠ 0 := by rw [CtCfu.nfun_zero]; positivity
  have hdiv : HasDerivAt (fun y => CtCfu.kfun y / (2 * CtCfu.nfun y)) (-(7 * π ^ 2 / 120)) 0 := by
    have hq := hk.div hn2 hne
    convert hq using 1
    rw [CtCfu.kfun_zero, CtCfu.nfun_zero]
    field_simp [hpi]
    ring
  have hpos : CtCfu.kfun 0 / (2 * CtCfu.nfun 0) ≠ 0 := by
    rw [CtCfu.kfun_zero, CtCfu.nfun_zero]
    positivity
  have hsq := hdiv.sqrt hpos
  have hval : (-(7 * π ^ 2 / 120)) / (2 * Real.sqrt (CtCfu.kfun 0 / (2 * CtCfu.nfun 0))) = -(7 * π ^ 2 / 240) := by
    have h1 : Real.sqrt (CtCfu.kfun 0 / (2 * CtCfu.nfun 0)) = 1 := fctH_zero
    rw [h1]
    ring
  exact hval ▸ hsq

lemma fctH_spec :
    ∃ (δH C_H : ℝ), 0 < δH ∧ δH ≤ 1 / 30 ∧ 4 ≤ C_H ∧
      JC 16 (Ioo (-δH) δH) fctH C_H ∧
      (∀ y ∈ Ioo (-δH) δH, 1 / 2 < CtCfu.kfun y / (2 * CtCfu.nfun y) ∧
        CtCfu.kfun y / (2 * CtCfu.nfun y) < 2 ∧ 0 < CtCfu.nfun y) := by
  have hratio_cont : ContinuousAt (fun y => CtCfu.kfun y / (2 * CtCfu.nfun y)) 0 := by
    have hk : ContinuousAt CtCfu.kfun 0 :=
      (CtCfu.contDiffOn_kfun.continuousOn).continuousAt
        (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr CtCfu.rr_pos, CtCfu.rr_pos⟩)
    have hn : ContinuousAt (fun y => 2 * CtCfu.nfun y) 0 :=
      continuous_const.continuousAt.mul
        ((CtCfu.contDiffOn_nfun.continuousOn).continuousAt
          (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr CtCfu.rr_pos, CtCfu.rr_pos⟩))
    have hn0 : 2 * CtCfu.nfun 0 ≠ 0 := by rw [CtCfu.nfun_zero]; positivity
    exact hk.div hn hn0
  have hn_cont : ContinuousAt CtCfu.nfun 0 :=
    (CtCfu.contDiffOn_nfun.continuousOn).continuousAt
      (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr CtCfu.rr_pos, CtCfu.rr_pos⟩)
  have hpi : π ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  have hr0 : CtCfu.kfun 0 / (2 * CtCfu.nfun 0) = 1 := by
    rw [CtCfu.kfun_zero, CtCfu.nfun_zero]; field_simp [hpi]; ring
  have hn0 : 0 < CtCfu.nfun 0 := by rw [CtCfu.nfun_zero]; positivity
  have hmem1 : {y : ℝ | 1 / 2 < CtCfu.kfun y / (2 * CtCfu.nfun y) ∧
      CtCfu.kfun y / (2 * CtCfu.nfun y) < 2} ∈ 𝓝 (0 : ℝ) := by
    refine hratio_cont.preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
    rw [hr0]; constructor <;> norm_num
  have hmem2 : {y : ℝ | 0 < CtCfu.nfun y} ∈ 𝓝 (0 : ℝ) :=
    hn_cont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hn0)
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hmem1 hmem2)
  set R : ℝ := min r (1 / 30) with hR
  have hR_pos : 0 < R := lt_min hr_pos (by norm_num)
  have hR_30 : R ≤ 1 / 30 := min_le_right _ _
  have hR_rr : R < CtCfu.rr := hR_30.trans_lt (by linarith only [tenth_lt_rr])
  have hsub_R : Ioo (-R) R ⊆ Ioo (-CtCfu.rr) CtCfu.rr := fun y hy =>
    ⟨by linarith [hy.1, hR_rr], by linarith [hy.2, hR_rr]⟩
  have hgood : ∀ y ∈ Ioo (-R) R, 1 / 2 < CtCfu.kfun y / (2 * CtCfu.nfun y) ∧
      CtCfu.kfun y / (2 * CtCfu.nfun y) < 2 ∧ 0 < CtCfu.nfun y := by
    intro y hy
    have hball : y ∈ Metric.ball (0 : ℝ) r := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
      have : R ≤ r := min_le_left _ _
      constructor <;> linarith [hy.1, hy.2]
    have hi := hr_sub hball
    exact ⟨hi.1.1, hi.1.2, hi.2⟩
  have hratio_cd : ContDiffOn ℝ 16 (fun y => CtCfu.kfun y / (2 * CtCfu.nfun y)) (Ioo (-R) R) :=
    ((CtCfu.contDiffOn_kfun.of_le (WithTop.coe_le_coe.mpr le_top)).mono hsub_R).div
      (contDiffOn_const.mul ((CtCfu.contDiffOn_nfun.of_le (WithTop.coe_le_coe.mpr le_top)).mono hsub_R))
      fun y hy => by linarith [(hgood y hy).2.2]
  have hH_cd : ContDiffOn ℝ 16 fctH (Ioo (-R) R) := by
    refine ContDiffOn.sqrt hratio_cd fun y hy => ?_
    linarith [(hgood y hy).1]
  set δH : ℝ := R / 2 with hδH
  have hδH_pos : 0 < δH := by positivity
  have hδH_30 : δH ≤ 1 / 30 := by linarith
  have hsub_comp : Icc (-δH) δH ⊆ Ioo (-R) R := fun y hy =>
    ⟨by linarith [hy.1, hδH_pos], by linarith [hy.2, hδH_pos]⟩
  obtain ⟨B, hB0, hB⟩ := exists_JC_Ioo (isOpen_Ioo (a := -R) (b := R)) hH_cd hsub_comp
  have hsub_oo : Ioo (-δH) δH ⊆ Ioo (-R) R := fun y hy =>
    ⟨by linarith [hy.1, hδH_pos], by linarith [hy.2, hδH_pos]⟩
  exact ⟨δH, max 4 B, hδH_pos, hδH_30, le_max_left _ _, hB.mono (le_max_right _ _),
    fun y hy => hgood y (hsub_oo hy)⟩

lemma sqrt_uctMderiv_div_two_uctM {τ : ℝ} (hτ0 : 0 < τ) (hτ14 : τ < 1 / 4) :
    Real.sqrt (uctMderiv τ / (2 * uctM τ)) = τ ^ (-(1 / 2 : ℝ)) * fctH (τ ^ 2) := by
  have hτ2 : τ ^ 2 < 1 / 16 := by nlinarith only [hτ0, hτ14]
  have hτ2_rr : τ ^ 2 < CtCfu.rr := hτ2.trans (by linarith only [tenth_lt_rr])
  have hm_eq : uctM τ = τ ^ 2 * CtCfu.nfun (τ ^ 2) := CtCfu.hankelEdgeM_eq hτ0.le hτ2_rr
  have hmp_eq : uctMderiv τ = τ * CtCfu.kfun (τ ^ 2) := by
    have h1 : mPrime τ = uctMderiv τ := by
      unfold uctMderiv uctEllDeriv mPrime
      rw [show 2 * (π * τ / 2) = π * τ by ring]
      have := Real.pi_pos
      field_simp
    rw [← h1, CtMDeriv.mPrime_eq_g0 ⟨hτ0, hτ14⟩]; rfl
  have hn_pos : 0 < CtCfu.nfun (τ ^ 2) := by
    have hm : 0 < uctM τ := uctM_pos hτ0
    rw [hm_eq] at hm
    exact pos_of_mul_pos_right hm (sq_nonneg τ)
  rw [hmp_eq, hm_eq]
  have hdiv : (τ * CtCfu.kfun (τ ^ 2)) / (2 * (τ ^ 2 * CtCfu.nfun (τ ^ 2))) =
      τ⁻¹ * (CtCfu.kfun (τ ^ 2) / (2 * CtCfu.nfun (τ ^ 2))) := by
    field_simp [hτ0.ne', hn_pos.ne']
  rw [hdiv, Real.sqrt_mul (inv_nonneg.mpr hτ0.le), Real.sqrt_eq_rpow, ← Real.rpow_neg_one τ,
    ← Real.rpow_mul hτ0.le]
  norm_num [fctH]

lemma concreteMt_zero : concreteMt 0 = 7 * π ^ 4 / 7200 := by
  obtain ⟨_, _, _, _, _, _, _, _, τ_lim, _, _, _, _, _, _, _, _, hτlim_pos, _, hcfu⟩ :=
    concrete_cfu_exist
  set c : ℝ := max 1 (τ_lim ^ (-(4 : ℝ)))
  have hc0 : 0 < c := by positivity
  have hτ1 : c ^ (-(1 / 4 : ℝ)) ≤ τ_lim := by
    have h1 : τ_lim ^ (-(4 : ℝ)) ≤ c := le_max_right _ _
    have := Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num : -(1 / 4 : ℝ) ≤ 0)
    refine this.trans_eq ?_
    rw [← Real.rpow_mul hτlim_pos.le]
    norm_num
  have hc1 : 1 ≤ c := le_max_left _ _
  have hK4t : (1 : ℝ) * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 := by
    rw [one_mul, ← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le]
    norm_num
    exact Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  obtain ⟨T, _, hTmt, _, _⟩ := hcfu (le_rfl) (Or.inl rfl) hc0 hτ1 hK4t
  have hmt_cont : ContinuousAt concreteMt 0 := by
    rw [← hTmt]
    exact (T.jc_mt.1.continuousOn).continuousAt (isOpen_Ioo.mem_nhds (by constructor <;> norm_num))
  have hslope : ∀ᶠ y in 𝓝[≠] (0 : ℝ),
      (CtCfu.ntil y - CtCfu.ntil 0) / y = -concreteMt y := by
    filter_upwards [inter_mem (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : -(1 / 30 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1 / 30))) self_mem_nhdsWithin] with y ⟨hy, hy0⟩
    have hy30 : |y| ≤ 1 / 30 := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
    have hy0' : y ≠ 0 := hy0
    rw [concreteMt_eq hy30, CtCfu.ntil_zero]
    field_simp [hy0']
    ring
  have hlim1 : Tendsto (fun y => (CtCfu.ntil y - CtCfu.ntil 0) / y) (𝓝[≠] (0 : ℝ))
      (𝓝 (-(7 * π ^ 4 / 7200))) := by
    have := (hasDerivAt_iff_tendsto_slope.mp CtCfu.hasDerivAt_ntil_zero)
    convert this using 1
    ext y; simp [slope_def_field, div_eq_mul_inv]
  have hlim2 : Tendsto (fun y => -concreteMt y) (𝓝[≠] (0 : ℝ)) (𝓝 (-concreteMt 0)) :=
    (hmt_cont.neg).tendsto.mono_left nhdsWithin_le_nhds
  have heq := tendsto_nhds_unique (hlim1.congr' hslope) hlim2
  linarith

/-! ### 2. `J₁ - J₀ ∈ 𝒮⁸(C c^{-17/12})` via `ChartSetup.dJ_jets` -/

/-- Rescaled quadratic composition: if `g` has `C^8` derivatives on `Yint` satisfying
`|g^{(k)}(y)| ≤ B * max y (8 * c^{-1/6}) ^ (4 - k)` for `y ≥ 0`, then
`u ↦ g (fctInnerY c u)` lies in `𝒮⁸(K_mult * B * c^{-2/3})` on `[0, U_c]`. -/
lemma dJ_comp_Y_sym {c B : ℝ} (hc : 100 ≤ c) (hB : 0 ≤ B) {g : ℝ → ℝ}
    (hg_cd : ContDiffOn ℝ 8 g Yint)
    (hg_bd : ∀ k : ℕ, k ≤ 8 → ∀ y ∈ Yint, 0 ≤ y →
      |iteratedDeriv k g y| ≤ B * max y (8 * c ^ (-(1 / 6 : ℝ))) ^ (4 - k)) :
    FctSymClsOn (Icc 0 (fctUc c)) 8 8
      ((Nat.factorial 8 : ℝ) * 16 ^ 4 * 8 ^ 4 * 100 ^ 8 * B * c ^ (-(2 / 3 : ℝ)))
      (fun u => ((g (fctInnerY c u) : ℝ) : ℂ)) := by
  have hc0 : 0 < c := by linarith
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hY_cd : ContDiff ℝ 8 (fctInnerY c) := by
    unfold fctInnerY; fun_prop
  have hcd_real : ContDiffOn ℝ 8 (fun u => g (fctInnerY c u)) (Icc 0 (fctUc c)) := by
    refine hg_cd.comp hY_cd.contDiffOn fun u hu => ?_
    have h35 := fctInnerY_mem_35 (by linarith) hu
    exact ⟨by linarith [h35.1], by linarith [h35.2]⟩
  have hgY_cd : ContDiffOn ℝ 8 (fun u => ((g (fctInnerY c u) : ℝ) : ℂ)) (Icc 0 (fctUc c)) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hcd_real
  refine ⟨hgY_cd, fun r hr u₀ hu₀ => ?_⟩
  rw [iteratedDerivWithin_ofReal_cast hDu hcd_real hr u₀ hu₀, Complex.norm_real, Real.norm_eq_abs]
  let r₀ : ℝ := (1 + u₀) / 100
  have hr₀_pos : 0 < r₀ := by dsimp only [r₀]; linarith [hu₀.1]
  let L₀ : ℝ := c ^ (-(1 / 6 : ℝ)) * (1 + u₀) ^ 2
  have h1u_pos : 0 < 1 + u₀ := by linarith [hu₀.1]
  have hL₀_pos : 0 < L₀ := by dsimp only [L₀]; positivity
  have hL₀_16 : L₀ ≤ 16 := by
    have hc12 : 1 ≤ c ^ ((1 : ℝ) / 12) := Real.one_le_rpow (by linarith) (by norm_num)
    have hUc_bd : 1 + u₀ ≤ 4 * c ^ ((1 : ℝ) / 12) := by
      have : u₀ ≤ 2.96 * c ^ ((1 : ℝ) / 12) := hu₀.2
      linarith
    have hsq : (1 + u₀) ^ 2 ≤ 16 * c ^ ((1 : ℝ) / 6) := by
      calc (1 + u₀) ^ 2 ≤ (4 * c ^ ((1 : ℝ) / 12)) ^ 2 :=
            pow_le_pow_left₀ (by linarith [hu₀.1]) hUc_bd 2
        _ = 16 * (c ^ ((1 : ℝ) / 12)) ^ 2 := by ring
        _ = 16 * c ^ ((1 : ℝ) / 6) := by
            rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
    have hprod : c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6) = 1 := by
      rw [← Real.rpow_add hc0]; norm_num
    calc L₀ = c ^ (-(1 / 6 : ℝ)) * (1 + u₀) ^ 2 := rfl
      _ ≤ c ^ (-(1 / 6 : ℝ)) * (16 * c ^ ((1 : ℝ) / 6)) := by gcongr
      _ = 16 * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6)) := by ring
      _ = 16 := by rw [hprod, mul_one]
  have hY35 := fctInnerY_mem_35 (by linarith) hu₀
  have hY_le_L0 : fctInnerY c u₀ ≤ L₀ := by
    have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have hsq : u₀ ^ 2 ≤ (1 + u₀) ^ 2 := pow_le_pow_left₀ hu₀.1 (by linarith) 2
    have h2c_nn : 0 ≤ (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) := by positivity
    unfold fctInnerY
    calc 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u₀ ^ 2
        ≤ 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * (1 + u₀) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq h2c_nn
      _ ≤ 1 * c ^ (-(1 / 6 : ℝ)) * (1 + u₀) ^ 2 := by
          have hc_nn : 0 ≤ c ^ (-(1 / 6 : ℝ)) * (1 + u₀) ^ 2 := by positivity
          calc 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * (1 + u₀) ^ 2
              = 2 ^ (-(4 / 3 : ℝ)) * (c ^ (-(1 / 6 : ℝ)) * (1 + u₀) ^ 2) := by ring
            _ ≤ 1 * (c ^ (-(1 / 6 : ℝ)) * (1 + u₀) ^ 2) := mul_le_mul_of_nonneg_right h243 hc_nn
            _ = 1 * c ^ (-(1 / 6 : ℝ)) * (1 + u₀) ^ 2 := by ring
      _ = L₀ := by dsimp only [L₀]; ring
  have hY_map : ∀ t ∈ Ioo (-1 : ℝ) 1,
      fctInnerY c (u₀ + r₀ * t) ∈ Yint ∧ 0 ≤ fctInnerY c (u₀ + r₀ * t) := by
    intro t ht
    have hm : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 0.3969 := fctB2_two_rpow_neg43_le
    have hy0 : 0 ≤ fctInnerY c (u₀ + r₀ * t) := by unfold fctInnerY; positivity
    have hc12 : 1 ≤ c ^ ((1 : ℝ) / 12) := Real.one_le_rpow (by linarith) (by norm_num)
    have h1 : |u₀ + r₀ * t| ≤ 3 * c ^ ((1 : ℝ) / 12) := by
      have hu296 : u₀ ≤ 2.96 * c ^ ((1 : ℝ) / 12) := hu₀.2
      calc |u₀ + r₀ * t| ≤ u₀ + r₀ := by
            rw [abs_le]; constructor <;> nlinarith [hu₀.1, ht.1, ht.2, hr₀_pos]
        _ = 1.01 * u₀ + 0.01 := by dsimp only [r₀]; ring
        _ ≤ 1.01 * (2.96 * c ^ ((1 : ℝ) / 12)) + 0.01 * c ^ ((1 : ℝ) / 12) := by nlinarith
        _ = 2.9996 * c ^ ((1 : ℝ) / 12) := by ring
        _ ≤ 3 * c ^ ((1 : ℝ) / 12) := by nlinarith [hc12]
    have hu_sq : (u₀ + r₀ * t) ^ 2 ≤ 3 ^ 2 * c ^ ((1 : ℝ) / 6) := by
      calc (u₀ + r₀ * t) ^ 2 = |u₀ + r₀ * t| ^ 2 := (sq_abs _).symm
        _ ≤ (3 * c ^ ((1 : ℝ) / 12)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = 3 ^ 2 * (c ^ ((1 : ℝ) / 12)) ^ 2 := by ring
        _ = 3 ^ 2 * c ^ ((1 : ℝ) / 6) := by
            rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
    have hprod : c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6) = 1 := by
      rw [← Real.rpow_add hc0]; norm_num
    have hy36 : fctInnerY c (u₀ + r₀ * t) < 3.6 := by
      calc fctInnerY c (u₀ + r₀ * t)
          ≤ 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * (3 ^ 2 * c ^ ((1 : ℝ) / 6)) := by
            unfold fctInnerY; gcongr
        _ = 2 ^ (-(4 / 3 : ℝ)) * 9 * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6)) := by ring
        _ = 2 ^ (-(4 / 3 : ℝ)) * 9 := by rw [hprod, mul_one]
        _ ≤ 0.3969 * 9 := by gcongr
        _ < 3.6 := by norm_num
    exact ⟨⟨by linarith, by linarith⟩, hy0⟩
  let htilde : ℝ → ℝ := fun t => (fctInnerY c (u₀ + r₀ * t) - fctInnerY c u₀) / L₀
  let gtilde : ℝ → ℝ := fun s => g (fctInnerY c u₀ + L₀ * s)
  have hht_cd : ContDiff ℝ ⊤ htilde := by
    dsimp only [htilde, fctInnerY]; fun_prop
  have hht_1 : |htilde 0| ≤ 1 := by simp [htilde]
  have hht_range : ∀ t ∈ Ioo (-1 : ℝ) 1, |htilde t| ≤ 1 := by
    intro t ht
    have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have hdiff : htilde t = 2 ^ (-(4 / 3 : ℝ)) * (2 * u₀ * r₀ * t + r₀ ^ 2 * t ^ 2) / (1 + u₀) ^ 2 := by
      dsimp only [htilde, fctInnerY, L₀]
      have hne : c ^ (-(1 / 6 : ℝ)) ≠ 0 := by positivity
      field_simp [hne, hL₀_pos.ne']; ring
    rw [hdiff, abs_div, abs_of_pos (sq_pos_of_pos (by linarith [hu₀.1] : 0 < 1 + u₀)),
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ (-(4 / 3 : ℝ)))]
    have hnum : |2 * u₀ * r₀ * t + r₀ ^ 2 * t ^ 2| ≤ (1 + u₀) ^ 2 := by
      have h2ur0 : 0 ≤ 2 * u₀ * r₀ := mul_nonneg (mul_nonneg zero_le_two hu₀.1) hr₀_pos.le
      have ha1 : |2 * u₀ * r₀ * t| ≤ 2 * u₀ * r₀ := by
        rw [abs_mul, abs_of_nonneg h2ur0]
        have : |t| ≤ 1 := (abs_lt.mpr ht).le
        exact mul_le_of_le_one_right h2ur0 this
      have ha2 : |r₀ ^ 2 * t ^ 2| ≤ r₀ ^ 2 := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg r₀), abs_sq]
        have : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
        exact mul_le_of_le_one_right (sq_nonneg r₀) this
      have htri : |2 * u₀ * r₀ * t + r₀ ^ 2 * t ^ 2| ≤ 2 * u₀ * r₀ + r₀ ^ 2 :=
        (abs_add_le _ _).trans (add_le_add ha1 ha2)
      exact htri.trans (by dsimp only [r₀]; nlinarith [hu₀.1])
    rw [div_le_one (sq_pos_of_pos (by linarith [hu₀.1] : 0 < 1 + u₀))]
    calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * |2 * u₀ * r₀ * t + r₀ ^ 2 * t ^ 2|
        ≤ 1 * (1 + u₀) ^ 2 := mul_le_mul h243 hnum (abs_nonneg _) zero_le_one
      _ = (1 + u₀) ^ 2 := one_mul _
  have hht_jb : JB 8 (Ioo (-1 : ℝ) 1) htilde 1 := by
    have hr₀_nn : 0 ≤ r₀ := hr₀_pos.le
    have hu₀_nn : 0 ≤ u₀ := hu₀.1
    have ha_coeff : ∀ t : ℝ, htilde t = (2 ^ (-(4 / 3 : ℝ)) / (1 + u₀) ^ 2) *
        (2 * u₀ * r₀ * t + r₀ ^ 2 * t ^ 2) := fun t => by
      dsimp only [htilde, fctInnerY, L₀]
      have hne : c ^ (-(1 / 6 : ℝ)) ≠ 0 := by positivity
      have hLne : c ^ (-(1 / 6 : ℝ)) * (1 + u₀) ^ 2 ≠ 0 := by positivity
      field_simp [hne, hLne]; ring
    have hd1fn : iteratedDeriv 1 htilde = fun s =>
        (2 ^ (-(4 / 3 : ℝ)) / (1 + u₀) ^ 2) * (2 * u₀ * r₀ + 2 * r₀ ^ 2 * s) := funext fun s => by
      have hfun : htilde = fun w => (2 ^ (-(4 / 3 : ℝ)) / (1 + u₀) ^ 2) * (2 * u₀ * r₀ * w + r₀ ^ 2 * w ^ 2) :=
        funext ha_coeff
      rw [hfun, iteratedDeriv_one, deriv_const_mul _ (by fun_prop)]
      have hd : HasDerivAt (fun w => 2 * u₀ * r₀ * w + r₀ ^ 2 * w ^ 2) (2 * u₀ * r₀ + 2 * r₀ ^ 2 * s) s :=
        (((hasDerivAt_id s).const_mul (2 * u₀ * r₀)).add ((hasDerivAt_pow 2 s).const_mul (r₀ ^ 2))).congr_deriv
          (by ring)
      rw [hd.deriv]
    have hd2fn : iteratedDeriv 2 htilde = fun _ => (2 ^ (-(4 / 3 : ℝ)) / (1 + u₀) ^ 2) * (2 * r₀ ^ 2) := funext fun z => by
      rw [iteratedDeriv_succ, hd1fn, deriv_const_mul _ (by fun_prop)]
      have hd : HasDerivAt (fun s => 2 * u₀ * r₀ + 2 * r₀ ^ 2 * s) (2 * r₀ ^ 2) z :=
        ((hasDerivAt_const z (2 * u₀ * r₀)).add ((hasDerivAt_id z).const_mul (2 * r₀ ^ 2))).congr_deriv (by ring)
      rw [hd.deriv]
    have h0_ge3 : ∀ m : ℕ, iteratedDeriv (m + 3) htilde = 0 := by
      intro m
      induction m with
      | zero => rw [iteratedDeriv_succ, hd2fn]; ext; simp
      | succ m ih => rw [show m + 1 + 3 = (m + 3) + 1 by omega, iteratedDeriv_succ, ih]; simp
    intro k hk t ht
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_of_isOpen isOpen_Ioo ht, Real.norm_eq_abs]
    have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    rcases Nat.lt_trichotomy k 1 with hk0 | hk1 | hk_ge2
    · have : k = 0 := by omega
      subst this; simpa only [iteratedDeriv_zero] using hht_range t ht
    · subst hk1; rw [hd1fn, abs_mul, abs_div, abs_of_nonneg (by positivity),
        abs_of_pos (sq_pos_of_pos h1u_pos)]
      have hnum : |2 * u₀ * r₀ + 2 * r₀ ^ 2 * t| ≤ (1 + u₀) ^ 2 := by
        have ha1 : |2 * u₀ * r₀| ≤ 2 * u₀ * r₀ := (abs_of_nonneg (by positivity)).le
        have ha2 : |2 * r₀ ^ 2 * t| ≤ 2 * r₀ ^ 2 := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_of_le_one_right (by positivity) (abs_lt.mpr ht).le
        have htri : |2 * u₀ * r₀ + 2 * r₀ ^ 2 * t| ≤ 2 * u₀ * r₀ + 2 * r₀ ^ 2 :=
          (abs_add_le _ _).trans (add_le_add ha1 ha2)
        exact htri.trans (by dsimp only [r₀]; nlinarith [hu₀.1])
      rw [div_mul_eq_mul_div, div_le_one (sq_pos_of_pos h1u_pos)]
      calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * |2 * u₀ * r₀ + 2 * r₀ ^ 2 * t|
          ≤ 1 * (1 + u₀) ^ 2 := mul_le_mul h243 hnum (abs_nonneg _) zero_le_one
        _ = (1 + u₀) ^ 2 := one_mul _
    · rcases Nat.lt_trichotomy k 2 with hk_lt | hk2 | hk_gt
      · omega
      · subst hk2; rw [hd2fn, abs_mul, abs_div, abs_of_nonneg (by positivity),
          abs_of_pos (sq_pos_of_pos h1u_pos)]
        have hnum : |2 * r₀ ^ 2| ≤ (1 + u₀) ^ 2 := by
          rw [abs_of_nonneg (by positivity)]; dsimp only [r₀]; nlinarith [hu₀.1]
        rw [div_mul_eq_mul_div, div_le_one (sq_pos_of_pos h1u_pos)]
        calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * |2 * r₀ ^ 2|
            ≤ 1 * (1 + u₀) ^ 2 := mul_le_mul h243 hnum (abs_nonneg _) zero_le_one
          _ = (1 + u₀) ^ 2 := one_mul _
      · have hk3 : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
        obtain ⟨m, rfl⟩ := hk3
        rw [h0_ge3 m, Pi.zero_apply, abs_zero]; exact zero_le_one
  -- Compact-bounded domain `T_s = Ico (max (-1.5) (-Y(u₀)/L₀)) (min 1.5 ((3.6 - Y(u₀))/L₀))`
  let a_lo : ℝ := max (-1.5 : ℝ) (-fctInnerY c u₀ / L₀)
  let b_hi : ℝ := min (1.5 : ℝ) ((3.6 - fctInnerY c u₀) / L₀)
  have ha_nonpos : a_lo ≤ 0 := max_le (by norm_num) (div_nonpos_of_nonpos_of_nonneg (by linarith [hY35.1]) hL₀_pos.le)
  have hb_pos : 0 < b_hi := lt_min (by norm_num) (div_pos (by linarith [hY35.2]) hL₀_pos)
  let T_s : Set ℝ := Ico a_lo b_hi
  have hT_u : UniqueDiffOn ℝ T_s := uniqueDiffOn_Ico a_lo b_hi
  have hT_map : ∀ s ∈ T_s, fctInnerY c u₀ + L₀ * s ∈ Yint ∧ 0 ≤ fctInnerY c u₀ + L₀ * s := by
    intro s hs
    have hs_lo : -fctInnerY c u₀ / L₀ ≤ s := (le_max_right _ _).trans hs.1
    have hs_hi : s < (3.6 - fctInnerY c u₀) / L₀ := lt_of_lt_of_le hs.2 (min_le_right _ _)
    have hy0 : 0 ≤ fctInnerY c u₀ + L₀ * s := by
      have := (div_le_iff₀ hL₀_pos).mp hs_lo; linarith
    have hy36 : fctInnerY c u₀ + L₀ * s < 3.6 := by
      have := (lt_div_iff₀ hL₀_pos).mp hs_hi; linarith
    exact ⟨⟨by linarith, by linarith⟩, hy0⟩
  have hht_maps : MapsTo htilde (Ioo (-1 : ℝ) 1) T_s := by
    intro t ht
    obtain ⟨hyY, hy0⟩ := hY_map t ht
    have hbd := abs_le.mp (hht_range t ht)
    refine ⟨max_le (by linarith [hbd.1]) ?_, lt_min (by linarith [hbd.2]) ?_⟩
    · rw [div_le_iff₀ hL₀_pos]; dsimp only [htilde]; rw [div_mul_cancel₀ _ hL₀_pos.ne']; linarith
    · rw [lt_div_iff₀ hL₀_pos]; dsimp only [htilde]; rw [div_mul_cancel₀ _ hL₀_pos.ne']; linarith [hyY.2]
  have hg_cd_m : ∀ (m : ℕ), m ≤ 8 →
      ContDiffOn ℝ ((8 - m : ℕ) : WithTop ℕ∞) (iteratedDeriv m g) Yint := by
    intro m
    induction m with
    | zero => intro _; simpa using hg_cd
    | succ m ih =>
      intro hm
      have hprev := ih (Nat.le_of_succ_le hm)
      have hsplit : ((8 - m : ℕ) : WithTop ℕ∞) = (((8 - (m + 1) : ℕ) : ℕ∞) + 1 : ℕ∞) := by
        have hn : 8 - m = (8 - (m + 1)) + 1 := by omega
        rw [hn]; push_cast; rfl
      rw [hsplit] at hprev
      have hd := hprev.derivWithin (m := ((8 - (m + 1) : ℕ) : ℕ∞)) isOpen_Ioo.uniqueDiffOn
        (by rw [← WithTop.coe_one, ← WithTop.coe_add])
      have hcongr : EqOn (derivWithin (iteratedDeriv m g) Yint) (iteratedDeriv (m + 1) g) Yint := by
        intro z hz
        rw [iteratedDeriv_succ, derivWithin_of_isOpen isOpen_Ioo hz]
      exact (hd.congr fun z hz => (hcongr hz).symm).of_le (by norm_cast)
  have hgt_jc : JC 8 T_s gtilde (B * (16 ^ 4 * 8 ^ 4) * L₀ ^ 4) := by
    have haff : ContDiffOn ℝ 8 (fun s : ℝ => fctInnerY c u₀ + L₀ * s) T_s := by fun_prop
    have hgt_cd : ContDiffOn ℝ 8 gtilde T_s :=
      hg_cd.comp haff fun s hs => (hT_map s hs).1
    refine ⟨hgt_cd, fun k hk s hs => ?_⟩
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, Real.norm_eq_abs]
    have haff_eq : gtilde = fun w => g (L₀ * w + fctInnerY c u₀) := by ext w; dsimp only [gtilde]; rw [add_comm]
    have hd_lin : ∀ (m : ℕ), m ≤ 8 → ∀ z ∈ T_s,
        iteratedDerivWithin m (fun w => g (L₀ * w + fctInnerY c u₀)) T_s z =
          L₀ ^ m * iteratedDeriv m g (L₀ * z + fctInnerY c u₀) := by
      intro m
      induction m with
      | zero => intro _ z _; simp
      | succ m ih =>
        intro hm z hz
        have hcongr : EqOn (iteratedDerivWithin m (fun w => g (L₀ * w + fctInnerY c u₀)) T_s)
            (fun w => L₀ ^ m * iteratedDeriv m g (L₀ * w + fctInnerY c u₀)) T_s :=
          fun w hw => ih (Nat.le_of_succ_le hm) w hw
        rw [iteratedDerivWithin_succ, derivWithin_congr hcongr (hcongr hz)]
        have hdg : ContDiffAt ℝ 1 (iteratedDeriv m g) (L₀ * z + fctInnerY c u₀) := by
          have hz_in : L₀ * z + fctInnerY c u₀ ∈ Yint := by simpa [add_comm] using (hT_map z hz).1
          have h1 := (hg_cd_m m (Nat.le_of_succ_le hm)).contDiffAt (isOpen_Ioo.mem_nhds hz_in)
          exact h1.of_le (by exact_mod_cast (by omega : 1 ≤ 8 - m))
        have hda : HasDerivAt (fun w => L₀ ^ m * iteratedDeriv m g (L₀ * w + fctInnerY c u₀))
            (L₀ ^ m * (iteratedDeriv (m + 1) g (L₀ * z + fctInnerY c u₀) * L₀)) z := by
          have h1 : HasDerivAt (iteratedDeriv m g) (iteratedDeriv (m + 1) g (L₀ * z + fctInnerY c u₀))
              (L₀ * z + fctInnerY c u₀) := by
            rw [iteratedDeriv_succ]
            exact (hdg.differentiableAt (by norm_num)).hasDerivAt
          have h2 : HasDerivAt (fun w => L₀ * w + fctInnerY c u₀) L₀ z := by
            simpa using ((hasDerivAt_id z).const_mul L₀).add_const (fctInnerY c u₀)
          exact (h1.comp z h2).const_mul (L₀ ^ m)
        rw [hda.hasDerivWithinAt.derivWithin (hT_u z hz)]
        ring
    rw [haff_eq, hd_lin k hk s hs, abs_mul, abs_pow, abs_of_pos hL₀_pos]
    obtain ⟨hy_int, hy_0⟩ := hT_map s hs
    have hgb := hg_bd k hk (L₀ * s + fctInnerY c u₀) (by simpa [add_comm] using hy_int) (by linarith)
    have hs_15 : s ≤ 1.5 := (lt_of_lt_of_le hs.2 (min_le_left _ _)).le
    have hy_le : L₀ * s + fctInnerY c u₀ ≤ 8 * L₀ := by
      have : L₀ * s ≤ 1.5 * L₀ := (mul_le_mul_of_nonneg_left hs_15 hL₀_pos.le).trans_eq (mul_comm _ _)
      linarith [hY_le_L0, hL₀_pos]
    have h8c : 8 * c ^ (-(1 / 6 : ℝ)) ≤ 8 * L₀ := by
      have h1u : 1 ≤ (1 + u₀) ^ 2 := by nlinarith [hu₀.1]
      dsimp only [L₀]; nlinarith [show (0 : ℝ) < c ^ (-(1 / 6 : ℝ)) by positivity]
    have hmax_le : max (L₀ * s + fctInnerY c u₀) (8 * c ^ (-(1 / 6 : ℝ))) ≤ 8 * L₀ :=
      max_le hy_le h8c
    by_cases hk4 : k ≤ 4
    · have hpow : max (L₀ * s + fctInnerY c u₀) (8 * c ^ (-(1 / 6 : ℝ))) ^ (4 - k) ≤ (8 * L₀) ^ (4 - k) :=
        pow_le_pow_left₀ (le_max_of_le_left (by linarith)) hmax_le (4 - k)
      calc L₀ ^ k * |iteratedDeriv k g (L₀ * s + fctInnerY c u₀)|
          ≤ L₀ ^ k * (B * max (L₀ * s + fctInnerY c u₀) (8 * c ^ (-(1 / 6 : ℝ))) ^ (4 - k)) := by gcongr
        _ ≤ L₀ ^ k * (B * (8 * L₀) ^ (4 - k)) := by gcongr
        _ = B * 8 ^ (4 - k) * (L₀ ^ k * L₀ ^ (4 - k)) := by rw [mul_pow]; ring
        _ = B * 8 ^ (4 - k) * L₀ ^ 4 := by rw [← pow_add, Nat.add_sub_of_le hk4]
        _ ≤ B * 8 ^ 4 * L₀ ^ 4 := by
            have h8p : (8 : ℝ) ^ (4 - k) ≤ 8 ^ 4 := pow_le_pow_right₀ (by norm_num) (Nat.sub_le 4 k)
            gcongr
        _ ≤ B * (16 ^ 4 * 8 ^ 4) * L₀ ^ 4 := by
            have h16 : (1 : ℝ) ≤ 16 ^ 4 := by norm_num
            nlinarith [mul_nonneg hB (pow_nonneg hL₀_pos.le 4)]
    · have hk4' : 4 ≤ k := by omega
      have hsub0 : 4 - k = 0 := Nat.sub_eq_zero_of_le hk4'
      have hpow_le : L₀ ^ k ≤ 16 ^ 4 * L₀ ^ 4 := by
        have hsplit : L₀ ^ k = L₀ ^ 4 * L₀ ^ (k - 4) := by
          rw [← pow_add, Nat.add_sub_of_le hk4']
        rw [hsplit, mul_comm (16 ^ 4)]
        gcongr
        exact (pow_le_pow_left₀ hL₀_pos.le hL₀_16 (k - 4)).trans
          (pow_le_pow_right₀ (by norm_num) (by omega))
      calc L₀ ^ k * |iteratedDeriv k g (L₀ * s + fctInnerY c u₀)|
          ≤ L₀ ^ k * (B * 1) := by simpa [hsub0] using mul_le_mul_of_nonneg_left hgb (pow_nonneg hL₀_pos.le k)
        _ ≤ (16 ^ 4 * L₀ ^ 4) * B := by rw [mul_one]; exact mul_le_mul_of_nonneg_right hpow_le hB
        _ ≤ B * (16 ^ 4 * 8 ^ 4) * L₀ ^ 4 := by
            have h84 : (1 : ℝ) ≤ 8 ^ 4 := by norm_num
            nlinarith [mul_nonneg hB (pow_nonneg hL₀_pos.le 4)]
  -- Apply `JB.comp` on `Ioo (-1) 1`
  have hjb := JB.comp (k := 8) isOpen_Ioo.uniqueDiffOn hT_u hgt_jc.1
    ((hht_cd.of_le le_top).contDiffOn) hht_maps (by positivity)
    (fun s hs i hi => hgt_jc.2 i hi (htilde s) (hht_maps hs))
    (fun i _ hi8 t ht => hht_jb i hi8 t ht)
  have h0_mem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hcomp_val : gtilde ∘ htilde = fun t => g (fctInnerY c (u₀ + r₀ * t)) := by
    ext t; dsimp only [Function.comp_apply, gtilde, htilde]
    rw [mul_div_cancel₀ _ hL₀_pos.ne']; ring_nf
  have hle := hjb r hr 0 h0_mem
  rw [hcomp_val, norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, Real.norm_eq_abs, max_self,
    iteratedDerivWithin_of_isOpen isOpen_Ioo h0_mem] at hle
  -- Relate `iteratedDeriv r (g ∘ Y (u₀ + r₀ ·)) 0` to `iteratedDerivWithin r (g ∘ Y) (Icc 0 U_c) u₀`
  have haff_rel : iteratedDeriv r (fun t => g (fctInnerY c (u₀ + r₀ * t))) 0 =
      r₀ ^ r * iteratedDerivWithin r (fun u => g (fctInnerY c u)) (Icc 0 (fctUc c)) u₀ := by
    let U_big : Set ℝ := (fctInnerY c) ⁻¹' Yint
    have hU_open : IsOpen U_big := isOpen_Ioo.preimage hY_cd.continuous
    have hU_sub : Icc 0 (fctUc c) ⊆ U_big := fun u hu => by
      have h35 := fctInnerY_mem_35 (by linarith) hu; exact ⟨by linarith [h35.1], by linarith [h35.2]⟩
    have hcd_big : ContDiffOn ℝ 8 (fun u => g (fctInnerY c u)) U_big :=
      hg_cd.comp hY_cd.contDiffOn fun u hu => hu
    have h0_in_big : u₀ ∈ U_big := hU_sub hu₀
    let Pre_U : Set ℝ := (fun w : ℝ => u₀ + r₀ * w) ⁻¹' U_big
    have hPre_open : IsOpen Pre_U := hU_open.preimage (by fun_prop)
    have h0_in_pre : (0 : ℝ) ∈ Pre_U := by simpa [Pre_U] using h0_in_big
    have hcomp_big := iteratedDerivWithin_comp_affine hU_open.uniqueDiffOn hPre_open.uniqueDiffOn
      hcd_big hr (v := 0) (by simpa using h0_in_big)
    change iteratedDerivWithin r (fun t => g (fctInnerY c (u₀ + r₀ * t))) Pre_U 0 =
      r₀ ^ r • iteratedDerivWithin r (fun u => g (fctInnerY c u)) U_big (u₀ + r₀ * 0) at hcomp_big
    rw [iteratedDerivWithin_of_isOpen hPre_open h0_in_pre, mul_zero, add_zero, smul_eq_mul,
      iteratedDerivWithin_of_isOpen hU_open h0_in_big] at hcomp_big
    rw [hcomp_big, iteratedDerivWithin_eq_iteratedDeriv hDu
      ((hcd_big.contDiffAt (hU_open.mem_nhds h0_in_big)).of_le (by exact_mod_cast hr)) hu₀]
  rw [haff_rel, abs_mul, abs_pow, abs_of_pos hr₀_pos] at hle
  have h1r : ((1 + u₀) ^ 8 : ℝ) / r₀ ^ r = 100 ^ r * (1 + u₀) ^ ((8 : ℝ) - r) := by
    have h1p : 0 < 1 + u₀ := by linarith [hu₀.1]
    dsimp only [r₀]
    rw [div_pow, div_div_eq_mul_div, ← Real.rpow_natCast (1 + u₀) 8, ← Real.rpow_natCast (1 + u₀) r]
    calc (1 + u₀) ^ (8 : ℝ) * 100 ^ r / (1 + u₀) ^ (r : ℝ)
        = 100 ^ r * ((1 + u₀) ^ (8 : ℝ) / (1 + u₀) ^ (r : ℝ)) := by ring
      _ = 100 ^ r * (1 + u₀) ^ ((8 : ℝ) - r) := by rw [← Real.rpow_sub h1p]
  have hL4 : L₀ ^ 4 = c ^ (-(2 / 3 : ℝ)) * (1 + u₀) ^ 8 := by
    dsimp only [L₀]; rw [mul_pow, ← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le, ← pow_mul]
    congr 1; norm_num
  have hle_div : |iteratedDerivWithin r (fun u => g (fctInnerY c u)) (Icc 0 (fctUc c)) u₀| ≤
      (Nat.factorial 8 : ℝ) * (B * (16 ^ 4 * 8 ^ 4) * L₀ ^ 4) / r₀ ^ r := by
    rw [le_div_iff₀ (pow_pos hr₀_pos r), mul_comm _ (r₀ ^ r)]
    simpa [one_pow, mul_one] using hle
  calc |iteratedDerivWithin r (fun u => g (fctInnerY c u)) (Icc 0 (fctUc c)) u₀|
      ≤ (Nat.factorial 8 : ℝ) * (B * (16 ^ 4 * 8 ^ 4) * (c ^ (-(2 / 3 : ℝ)) * (1 + u₀) ^ 8)) / r₀ ^ r := by
        rw [← hL4]; exact hle_div
    _ = (Nat.factorial 8 : ℝ) * (16 ^ 4 * 8 ^ 4) * B * c ^ (-(2 / 3 : ℝ)) * ((1 + u₀) ^ 8 / r₀ ^ r) := by ring
    _ = (Nat.factorial 8 : ℝ) * (16 ^ 4 * 8 ^ 4) * B * c ^ (-(2 / 3 : ℝ)) * (100 ^ r * (1 + u₀) ^ ((8 : ℝ) - r)) := by
        rw [h1r]
    _ ≤ (Nat.factorial 8 : ℝ) * (16 ^ 4 * 8 ^ 4) * B * c ^ (-(2 / 3 : ℝ)) * (100 ^ 8 * (1 + u₀) ^ ((8 : ℝ) - r)) := by
        have h100r : (100 : ℝ) ^ r ≤ 100 ^ 8 := pow_le_pow_right₀ (by norm_num) hr
        gcongr
    _ = (Nat.factorial 8 : ℝ) * 16 ^ 4 * 8 ^ 4 * 100 ^ 8 * B * c ^ (-(2 / 3 : ℝ)) * (1 + u₀) ^ ((8 : ℝ) - r) := by
        ring

/-- **`(fct:inner-symbols)` (b3), `J₁ - J₀` part**:
for `c` large enough, `K₄ τ₁² ≤ 1`, `(L₁, α) ∈ concretePhaseDom ellMin ε c`, and `S.A (ℓ₁, 1, α) ≤ 4 c^{-1/6}`,
we have `Jfun S.V fctH (τ₁^2) ((ℓ₁, 1, α), Y(u)) - Jfun S.V fctH (τ₁^2) ((ℓ₁, 0, α), Y(u)) ∈ 𝒮⁸(C c^{-17/12})`
on `[0, U_c]`. -/
theorem fctInner_J1_sub_J0_sym {M_box C0_box : ℝ} (hM0 : 0 ≤ M_box) (hC0_pos : 0 ≤ C0_box) :
    ∃ (δH C c₀ : ℝ), 0 < δH ∧ 0 ≤ C ∧ 100 ≤ c₀ ∧
      ∀ {K4 ε c : ℝ}, 1 ≤ K4 → (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        let τ₁ := c ^ (-(1 / 4 : ℝ))
        τ₁ ^ 2 < δH / 6 →
        K4 * τ₁ ^ 2 ≤ 1 →
        ∀ {T : CfuTheta} {S : ChartSetup (ℝ × ℝ × ℝ)},
          T.M = M_box →
          S.Ω = OmT τ₁ → S.ℓ = (fun p : ℝ × ℝ × ℝ => p.1) → S.r = T.r τ₁ K4 →
          S.ε = C0_box * τ₁ ^ 2 →
          ∀ {L1 α : ℝ},
            let ell1 := concreteEll1 ε c L1
            ell1 ∈ Ioo (0 : ℝ) 2.55 →
            |α| ≤ c ^ (-(1 / 2 : ℝ)) →
            S.A (ell1, 1, α) ≤ 4 * c ^ (-(1 / 6 : ℝ)) →
            FctSymClsOn (Icc 0 (fctUc c)) 8 8 (C * c ^ (-(17 / 12 : ℝ)))
              (fun u => ((Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), fctInnerY c u) -
                Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), fctInnerY c u) : ℝ) : ℂ)) := by
  obtain ⟨δH, C_H, hδH_pos, hδH_30, hCH4, hH_jc, _⟩ := fctH_spec
  let B_Th : ℝ := (4 + 2 ^ 16) * ((Nat.factorial 16 : ℝ) * M_box)
  have hBTh_nn : 0 ≤ B_Th := by positivity
  let β : ℝ := max 4 (max B_Th C_H)
  have hβ4 : 4 ≤ β := le_max_left _ _
  let CJmax : ℝ := ∑ n ∈ Finset.range 9, CJ n (Φb^[3] β)
  have hCJ_nn : ∀ n, 0 ≤ CJ n (Φb^[3] β) := fun n =>
    CJ_nonneg n (Φb_iter_nonneg (by linarith : 0 ≤ β) 3)
  have hCJmax_nn : 0 ≤ CJmax := Finset.sum_nonneg fun n _ => hCJ_nn n
  let C_mult : ℝ := (Nat.factorial 8 : ℝ) * 16 ^ 4 * 8 ^ 4 * 100 ^ 8 * CJmax
  set c₀ : ℝ := max (160000 : ℝ) ((30 * C0_box + 1) ^ 2) with hc₀_def
  have hc0_100 : 100 ≤ c₀ := by
    have hmax := le_max_left (160000 : ℝ) ((30 * C0_box + 1) ^ 2)
    linarith [hc₀_def]
  refine ⟨δH, C_mult, c₀, hδH_pos, by positivity, hc0_100, ?_⟩
  intro K4 ε c hK4 hε hc τ₁ hτ1_δH hK4t T S hTM hSΩ hSℓ hSr hSε L1 α ell1 hell1 hα hSA
  have hc160000 : (160000 : ℝ) ≤ c := by
    have hmax := le_max_left (160000 : ℝ) ((30 * C0_box + 1) ^ 2)
    linarith [hc₀_def]
  have hc100 : 100 ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_20 : τ₁ ≤ 1 / 20 := by
    have h1 : (20 : ℝ) ^ 4 ≤ c := by linarith
    have h2 : c ^ (-(1 / 4 : ℝ)) ≤ (160000 : ℝ) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hc160000 (by norm_num)
    have h3 : (160000 : ℝ) ^ (-(1 / 4 : ℝ)) = 1 / 20 := by
      rw [show (160000 : ℝ) = (20 : ℝ) ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]
      norm_num [Real.rpow_neg_one]
    exact h2.trans_eq h3
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_sq_eq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hτ₁_3_eq : τ₁ ^ 3 = c ^ (-(3 / 4 : ℝ)) := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hτ₁_1 : τ₁ ≤ 1 := by
    have : 1 ≤ c := by linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos this (by norm_num)
  have hτ₁_sq_le1 : τ₁ ^ 2 ≤ 1 := pow_le_one₀ hτ₁_pos.le hτ₁_1
  have hα_om : |α| < 2 * τ₁ ^ 2 := by
    rw [hτ₁_sq_eq]
    have : 0 < c ^ (-(1 / 2 : ℝ)) := by positivity
    linarith
  have hp0_mem : (ell1, 0, α) ∈ S.Ω := by
    rw [hSΩ]
    refine ⟨⟨by linarith [hell1.1], by linarith [hell1.2]⟩, ⟨by norm_num, by norm_num⟩, ?_⟩
    simpa [abs_lt] using hα_om
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, (ell1, 0, α) + t • (0, 1, 0) ∈ S.Ω := by
    intro t ht
    rw [hSΩ]
    have hpt : (ell1, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = (ell1, t, α) := by ext <;> simp
    rw [hpt]
    refine ⟨⟨by linarith [hell1.1], by linarith [hell1.2]⟩,
      ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    simpa [abs_lt] using hα_om
  -- Prove `|rhoF S.r (p, z)| ≤ 1/2 * |z|` on `S.Ω ×ˢ Ioo (-1) 6` to apply `A_comp`
  have hSε_bd : 15 * S.ε ≤ 1 / 2 := by
    have h1 : (30 * C0_box + 1) ≤ c ^ (1 / 2 : ℝ) := by
      have : (30 * C0_box + 1) ^ 2 ≤ c := by
        have hmax := le_max_right (160000 : ℝ) ((30 * C0_box + 1) ^ 2)
        linarith [hc₀_def]
      exact (Real.le_sqrt_of_sq_le this).trans (by rw [Real.sqrt_eq_rpow])
    have h2 : C0_box * τ₁ ^ 2 ≤ 1 / 30 := by
      rw [hτ₁_sq_eq, Real.rpow_neg hc0.le]
      have hpos : (0 : ℝ) < 30 * C0_box + 1 := by positivity
      calc C0_box * (c ^ ((1 : ℝ) / 2))⁻¹
          ≤ C0_box * (30 * C0_box + 1)⁻¹ := mul_le_mul_of_nonneg_left
            (inv_anti₀ hpos h1) hC0_pos
        _ ≤ 1 / 30 := by rw [← div_eq_mul_inv, div_le_div_iff₀ hpos (by norm_num)]; linarith
    rw [hSε]; linarith
  have hρ_bd : ∀ p ∈ S.Ω, ∀ z ∈ Ioo (-1 : ℝ) 6, |rhoF S.r (p, z)| ≤ 1 / 2 * |z| := by
    intro p hp z hz
    -- First `rhoF S.r (p, 0) = 0` since `S.r (p, 0) = 0`
    have hr0 : rhoF S.r (p, 0) = 0 := by
      have hrs0 : S.r (p, 0) = 0 := by rw [hSr]; simp [CfuTheta.r]
      simp [rhoF, hrs0]
    -- Bound `(d/dz) (rhoF S.r (p, z))` on `Ioo (-1) 6` using `S.hr` (`JC 18 _ S.r S.ε`)
    have hcd_r : ContDiffOn ℝ 18 S.r (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hr.1
    have hO : IsOpen (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hΩ.prod isOpen_Ioo
    have h0_mem : (p, (0 : ℝ)) ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hp, by norm_num, by norm_num⟩
    have hrho_cd : ContDiffOn ℝ 1 (fun w => rhoF S.r (p, w)) (Ioo (-1 : ℝ) 6) := by
      have hp_emb : ContDiffOn ℝ 18 (fun w : ℝ => (p, w)) (Ioo (-1 : ℝ) 6) := by fun_prop
      have hr_w : ContDiffOn ℝ 18 (fun w => S.r (p, w)) (Ioo (-1 : ℝ) 6) :=
        hcd_r.comp hp_emb fun w hw => ⟨hp, hw⟩
      have hfd_w : ContDiffOn ℝ 17 (fun w => fderiv ℝ S.r (p, w) (0, 1)) (Ioo (-1 : ℝ) 6) := by
        have h17 := (S.hr.succ_fderiv hO).clm_apply_const hO.uniqueDiffOn ((0 : ℝ × ℝ × ℝ), (1 : ℝ))
        exact h17.1.comp (hp_emb.of_le (by norm_num : (17 : WithTop ℕ∞) ≤ 18)) fun w hw => ⟨hp, hw⟩
      have h_eq : EqOn (fun w => rhoF S.r (p, w)) (fun w => S.r (p, w) + 2 * (w * fderiv ℝ S.r (p, w) (0, 1)))
          (Ioo (-1 : ℝ) 6) := fun _ _ => rfl
      refine ((hr_w.of_le (by norm_num)).add (contDiffOn_const.mul (contDiffOn_id.mul (hfd_w.of_le (by norm_num))))).congr h_eq
    have hderiv_bd : ∀ w ∈ Ioo (-1 : ℝ) 6, |deriv (fun t => rhoF S.r (p, t)) w| ≤ 1 / 2 := by
      intro w hw
      have hq : (p, w) ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hp, hw⟩
      have hdr : HasDerivAt (fun t => S.r (p, t)) (fderiv ℝ S.r (p, w) (0, 1)) w := by
        have h1 : HasFDerivAt S.r (fderiv ℝ S.r (p, w)) (p, w) :=
          ((S.hr.1.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt
        have h2 : HasDerivAt (fun t : ℝ => (p, t)) (0, 1) w := by
          simpa using (hasDerivAt_const w p).prodMk (hasDerivAt_id w)
        exact h1.comp_hasDerivAt w h2
      have hd2 : HasDerivAt (fun t => fderiv ℝ S.r (p, t) (0, 1))
          (fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)) w := by
        have h17 := (S.hr.succ_fderiv hO).clm_apply_const hO.uniqueDiffOn ((0 : ℝ × ℝ × ℝ), (1 : ℝ))
        have h1 : HasFDerivAt (fun x => fderiv ℝ S.r x (0, 1))
            (fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w)) (p, w) :=
          ((h17.1.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt
        have h2 : HasDerivAt (fun t : ℝ => (p, t)) (0, 1) w := by
          simpa using (hasDerivAt_const w p).prodMk (hasDerivAt_id w)
        exact h1.comp_hasDerivAt w h2
      have htot : HasDerivAt (fun t => rhoF S.r (p, t))
          (fderiv ℝ S.r (p, w) (0, 1) + 2 * (1 * fderiv ℝ S.r (p, w) (0, 1) +
            w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1))) w :=
        hdr.add (((hasDerivAt_id w).mul hd2).const_mul 2)
      rw [htot.deriv]
      have hb1 : |fderiv ℝ S.r (p, w) (0, 1)| ≤ S.ε := by
        have := (S.hr.2 1 (by norm_num) (p, w) hq)
        rw [norm_iteratedFDerivWithin_one _ (hO.uniqueDiffOn _ hq), fderivWithin_of_isOpen hO hq] at this
        calc |fderiv ℝ S.r (p, w) (0, 1)| = ‖fderiv ℝ S.r (p, w) (0, 1)‖ := Real.norm_eq_abs _
          _ ≤ ‖fderiv ℝ S.r (p, w)‖ * ‖((0 : ℝ × ℝ × ℝ), (1 : ℝ))‖ := (fderiv ℝ S.r _).le_opNorm _
          _ ≤ S.ε * 1 := mul_le_mul this (by simp [Prod.norm_def]) (norm_nonneg _) S.hε
          _ = S.ε := mul_one _
      have hb2 : |fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)| ≤ S.ε := by
        have h17 := (S.hr.succ_fderiv hO).clm_apply_const hO.uniqueDiffOn ((0 : ℝ × ℝ × ℝ), (1 : ℝ))
        have hbd := h17.2 1 (by norm_num) (p, w) hq
        rw [norm_iteratedFDerivWithin_one _ (hO.uniqueDiffOn _ hq), fderivWithin_of_isOpen hO hq] at hbd
        have hn1 : ‖((0 : ℝ × ℝ × ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
        rw [hn1, one_mul] at hbd
        calc |fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)|
            = ‖fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w)‖ * ‖((0 : ℝ × ℝ × ℝ), (1 : ℝ))‖ :=
              (fderiv ℝ _ _).le_opNorm _
          _ ≤ S.ε * 1 := mul_le_mul hbd (le_of_eq hn1) (norm_nonneg _) S.hε
          _ = S.ε := mul_one _
      have hw6 : |w| ≤ 6 := by rw [abs_le]; constructor <;> linarith [hw.1, hw.2]
      calc |fderiv ℝ S.r (p, w) (0, 1) + 2 * (1 * fderiv ℝ S.r (p, w) (0, 1) +
              w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1))|
          = |3 * fderiv ℝ S.r (p, w) (0, 1) +
              2 * w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)| := by
            congr 1; ring
        _ ≤ |3 * fderiv ℝ S.r (p, w) (0, 1)| +
              |2 * w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)| :=
            abs_add_le _ _
        _ = 3 * |fderiv ℝ S.r (p, w) (0, 1)| + 2 * |w| *
              |fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)| := by
            rw [abs_mul, abs_mul, abs_mul, show |(3 : ℝ)| = 3 by norm_num, show |(2 : ℝ)| = 2 by norm_num]
        _ ≤ 3 * S.ε + 2 * 6 * S.ε := by gcongr
        _ = 15 * S.ε := by ring
        _ ≤ 1 / 2 := hSε_bd
    have hmv := convex_Ioo (-1 : ℝ) 6 |>.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun w hw => ((hrho_cd.differentiableOn (by norm_num) w hw).hasDerivWithinAt).congr_deriv
        (by rw [derivWithin_of_isOpen isOpen_Ioo hw]))
      (fun w hw => by rw [Real.norm_eq_abs]; exact hderiv_bd w hw)
      (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 6 from ⟨by norm_num, by norm_num⟩) hz
    simpa [hr0, Real.norm_eq_abs, sub_zero] using hmv
  -- Now establish `ZeroPath` on `(ell1, 0, α) + t • (0, 1, 0)` so `0 ≤ S.A` and `S.A ≤ 8 * c^{-1/6}`
  have hzp : ∀ t ∈ Icc (0 : ℝ) 1, S.ZeroPath ((ell1, 0, α) + t • (0, 1, 0)) := by
    intro t ht
    have hpt : (ell1, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = (ell1, t, α) := by ext <;> simp
    refine ⟨hseg t ht, ?_, (1, 0, 0), by simp [Prod.norm_def], fun s hs => ?_⟩
    · rw [hSℓ, hpt]; linarith [hell1.1]
    · rw [hpt] at hs ⊢
      have hsub : (ell1, t, α) - s • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) = (ell1 - s, t, α) := by ext <;> simp
      rw [hsub, hSℓ]
      rw [hSℓ] at hs; simp only at hs
      refine ⟨?_, rfl⟩
      rw [hSΩ]
      exact ⟨⟨by linarith [hs.1, hs.2, hell1.1], by linarith [hs.1, hell1.2]⟩,
        ⟨by linarith [ht.1], by linarith [ht.2]⟩, by simpa [abs_lt] using hα_om⟩
  have hSA_bounds : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ S.A ((ell1, 0, α) + t • (0, 1, 0)) ∧
      S.A ((ell1, 0, α) + t • (0, 1, 0)) ≤ 8 * c ^ (-(1 / 6 : ℝ)) := by
    intro t ht
    have h1 := hzp (1 : ℝ) (right_mem_Icc.mpr zero_le_one)
    have h0 := hzp t ht
    have hpt1 : (ell1, 0, α) + (1 : ℝ) • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = (ell1, 1, α) := by ext <;> simp
    have hpt : (ell1, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = (ell1, t, α) := by ext <;> simp
    have hac := S.A_comp hρ_bd h1 h0 (by rw [hSℓ]; simp)
    have hA_t := S.A_comp hρ_bd h0 h1 (by rw [hSℓ]; simp)
    rw [hpt1] at hac
    refine ⟨hA_t.1, hac.2.trans (by linarith [hSA])⟩
  -- Check `hψ`, `hθ`, `hH`, `hHT` for `ChartSetup.dJ_jets`
  let θ : (ℝ × ℝ × ℝ) × ℝ → ℝ := fun q => T.Th τ₁ K4 q.1.2.2 q.2
  have hψ : ∀ q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6,
      fderiv ℝ (fun q : (ℝ × ℝ × ℝ) × ℝ => S.ℓ q.1 - π ^ 2 / 36 * q.2 + S.r q) q ((0, 1, 0), 0) =
        τ₁ ^ 3 * q.2 ^ 5 * θ q := by
    intro q hq
    have hO : IsOpen (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hΩ.prod isOpen_Ioo
    have hℓc : ContDiffAt ℝ 1 (fun x : (ℝ × ℝ × ℝ) × ℝ => S.ℓ x.1) q :=
      (S.hℓj.1.comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ × ℝ) ℝ).contDiff.contDiffOn
        (fun (x : (ℝ × ℝ × ℝ) × ℝ) (hx : x ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6) => hx.1)).contDiffAt
        (hO.mem_nhds hq) |>.of_le (by norm_num)
    have hrc : ContDiffAt ℝ 1 S.r q := (S.hr.1.contDiffAt (hO.mem_nhds hq)).of_le (by norm_num)
    have hline : HasDerivAt (fun s : ℝ =>
        S.ℓ (q.1 + s • (0, 1, 0)) - π ^ 2 / 36 * q.2 + S.r (q.1 + s • (0, 1, 0), q.2))
        (τ₁ ^ 3 * q.2 ^ 5 * θ q) 0 := by
      have heq : ∀ s : ℝ, S.ℓ (q.1 + s • (0, 1, 0)) - π ^ 2 / 36 * q.2 + S.r (q.1 + s • (0, 1, 0), q.2) =
          (q.1.1 - π ^ 2 / 36 * q.2 + τ₁ ^ 2 * (q.2 ^ 2 * T.mt (τ₁ ^ 2 * q.2)) -
            τ₁ ^ 4 * (q.2 * T.θt (τ₁ ^ 2 * q.2)) + q.1.2.1 * (τ₁ ^ 3 * (q.2 ^ 5 * θ q))) +
            s * (τ₁ ^ 3 * q.2 ^ 5 * θ q) := fun s => by
        rw [hSℓ, hSr]
        simp only [CfuTheta.r, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul,
          mul_zero, mul_one, add_zero, θ]
        ring
      let c_val : ℝ := q.1.1 - π ^ 2 / 36 * q.2 + τ₁ ^ 2 * (q.2 ^ 2 * T.mt (τ₁ ^ 2 * q.2)) -
        τ₁ ^ 4 * (q.2 * T.θt (τ₁ ^ 2 * q.2)) + q.1.2.1 * (τ₁ ^ 3 * (q.2 ^ 5 * θ q))
      have hd : HasDerivAt (fun s : ℝ => c_val + s * (τ₁ ^ 3 * q.2 ^ 5 * θ q))
          (0 + 1 * (τ₁ ^ 3 * q.2 ^ 5 * θ q)) 0 :=
        (hasDerivAt_const (0 : ℝ) c_val).add ((hasDerivAt_id (0 : ℝ)).mul_const (τ₁ ^ 3 * q.2 ^ 5 * θ q))
      exact (hd.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun s => heq s)
    have hpt0 : (q.1 + (0 : ℝ) • ((0 : ℝ), (1 : ℝ), (0 : ℝ)), q.2) = q := by simp
    have hf1 : HasFDerivAt (fun x : (ℝ × ℝ × ℝ) × ℝ => S.ℓ x.1 - π ^ 2 / 36 * x.2 + S.r x)
        (fderiv ℝ (fun x => S.ℓ x.1 - π ^ 2 / 36 * x.2 + S.r x) q)
        (q.1 + (0 : ℝ) • ((0 : ℝ), (1 : ℝ), (0 : ℝ)), q.2) :=
      hpt0.symm ▸ ((hℓc.sub (by fun_prop)).add hrc |>.differentiableAt (by norm_num)).hasFDerivAt
    have hcurve : HasDerivAt (fun s : ℝ => (q.1 + s • ((0 : ℝ), (1 : ℝ), (0 : ℝ)), q.2)) ((0, 1, 0), 0) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => q.1 + s • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) ((0 : ℝ), (1 : ℝ), (0 : ℝ)) 0 :=
        ((hasDerivAt_const (0 : ℝ) q.1).add ((hasDerivAt_id (0 : ℝ)).smul_const ((0 : ℝ), (1 : ℝ), (0 : ℝ)))).congr_deriv
          (by simp)
      exact h1.prodMk (hasDerivAt_const (0 : ℝ) q.2)
    have hf2 : HasDerivAt (fun s : ℝ => S.ℓ (q.1 + s • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) - π ^ 2 / 36 * q.2 +
        S.r (q.1 + s • ((0 : ℝ), (1 : ℝ), (0 : ℝ)), q.2))
        (fderiv ℝ (fun x => S.ℓ x.1 - π ^ 2 / 36 * x.2 + S.r x) q ((0, 1, 0), 0)) 0 := by
      simpa [Function.comp_def] using hf1.comp_hasDerivAt 0 hcurve
    exact hf2.unique hline
  have hθ_jc : JCΦ 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) θ (Φb^[3] β) 0 := by
    have hO : IsOpen (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hΩ.prod isOpen_Ioo
    have hUd : UniqueDiffOn ℝ (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := hO.uniqueDiffOn
    have hTM0 : 0 ≤ T.M := hTM ▸ hM0
    let L_snd : ((ℝ × ℝ × ℝ) × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ (ℝ × ℝ × ℝ) ℝ
    have hLsnd_norm : ‖L_snd‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
      simpa [L_snd] using norm_snd_le p
    have hcomp : ∀ f : ℝ → ℝ, JC 18 (Ioo (-1 : ℝ) 6) f T.M →
        JC 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => f q.2) ((Nat.factorial 16 : ℝ) * M_box) := fun f hf => by
      have h16 : JC 16 (Ioo (-1 : ℝ) 6) f M_box := (hf.mono_order (by norm_num)).mono (le_of_eq hTM)
      exact JC.comp_clm hUd isOpen_Ioo.uniqueDiffOn L_snd hLsnd_norm hM0 h16 fun q hq => hq.2
    have h0b := hcomp T.Θ0b T.jc_Θ0b
    have h0m : JC 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => (K4 * τ₁ ^ 2) * T.Θ0m q.2)
        ((Nat.factorial 16 : ℝ) * M_box) := by
      have h1 := (hcomp T.Θ0m T.jc_Θ0m).const_smul hUd (K4 * τ₁ ^ 2)
      refine (h1.mono ?_).congr fun _ _ => rfl
      rw [abs_of_nonneg (mul_nonneg (by linarith) (sq_nonneg τ₁))]
      exact mul_le_of_le_one_left (by positivity) hK4t
    have h1b : JC 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => τ₁ * T.Θ1b q.2)
        ((Nat.factorial 16 : ℝ) * M_box) := by
      have h1 := (hcomp T.Θ1b T.jc_Θ1b).const_smul hUd τ₁
      refine (h1.mono ?_).congr fun _ _ => rfl
      rw [abs_of_pos hτ₁_pos]; exact mul_le_of_le_one_left (by positivity) hτ₁_1
    have h1m : JC 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => (K4 * τ₁ ^ 3) * T.Θ1m q.2)
        ((Nat.factorial 16 : ℝ) * M_box) := by
      have h1 := (hcomp T.Θ1m T.jc_Θ1m).const_smul hUd (K4 * τ₁ ^ 3)
      refine (h1.mono ?_).congr fun _ _ => rfl
      rw [abs_of_nonneg (mul_nonneg (by linarith) (pow_nonneg hτ₁_pos.le 3))]
      have hK3 : K4 * τ₁ ^ 3 ≤ 1 := by
        calc K4 * τ₁ ^ 3 = (K4 * τ₁ ^ 2) * τ₁ := by ring
          _ ≤ 1 * 1 := mul_le_mul hK4t hτ₁_1 hτ₁_pos.le zero_le_one
          _ = 1 := one_mul 1
      exact mul_le_of_le_one_left (by positivity) hK3
    let L_α : ((ℝ × ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ × ℝ) ℝ))
    have hLα_norm : ‖L_α‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
      have h1 : ‖p.1.2.2‖ ≤ ‖p.1.2‖ := norm_snd_le p.1.2
      have h2 : ‖p.1.2‖ ≤ ‖p.1‖ := norm_snd_le p.1
      have h3 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
      simpa [L_α, one_mul] using (h1.trans h2).trans h3
    have hα_jc : JC 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => q.1.2.2) 1 :=
      JC.clm hUd L_α hLα_norm fun q hq => by
        rw [hSΩ] at hq
        have hqα := hq.1.2.2
        have h2τ : 2 * τ₁ ^ 2 ≤ 1 := by nlinarith only [hτ₁_20, hτ₁_pos]
        simpa [L_α, Real.norm_eq_abs, abs_le] using ⟨by linarith only [hqα.1, h2τ], by linarith only [hqα.2, h2τ]⟩
    have hα_term := JC.mul hUd zero_le_one (by positivity) hα_jc (hcomp T.Θα T.jc_Θα)
    have hsum := (((h0b.add hUd h0m).add hUd h1b).add hUd h1m).add hUd hα_term
    have hB_eq : ((Nat.factorial 16 : ℝ) * M_box + (Nat.factorial 16 : ℝ) * M_box +
        (Nat.factorial 16 : ℝ) * M_box + (Nat.factorial 16 : ℝ) * M_box +
        2 ^ 16 * 1 * ((Nat.factorial 16 : ℝ) * M_box)) = B_Th := by
      dsimp only [B_Th]; ring
    have hθ_B : JC 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) θ B_Th :=
      (hsum.mono (le_of_eq hB_eq)).congr fun q _ => by
        simp only [θ, CfuTheta.Th]
    exact hθ_B.mono ((le_max_left B_Th C_H |>.trans (le_max_right 4 _)).trans (Φb_iter_ge 3 β))
  have hH_jcΦ : JCΦ 16 (Ioo (-δH) δH) fctH (Φb^[3] β) 0 :=
    hH_jc.mono ((le_max_right _ _ |>.trans (le_max_right _ _)).trans (Φb_iter_ge 3 β))
  have hHT : ∀ q ∈ S.Ω ×ˢ Yint, τ₁ ^ 2 * (q.2 * S.V q ^ 2) ∈ Ioo (-δH) δH := by
    intro q hq
    have hVb := S.V_bounds hq
    have hV2 : S.V q ^ 2 ≤ 36 / 25 := by nlinarith only [hVb.1, hVb.2]
    have hq2 : |q.2| < 3.6 := by rw [abs_lt]; constructor <;> linarith only [hq.2.1, hq.2.2]
    have hprod : |τ₁ ^ 2 * (q.2 * S.V q ^ 2)| < 6 * τ₁ ^ 2 := by
      have hqV : |q.2| * S.V q ^ 2 < 6 := by nlinarith only [abs_nonneg q.2, hq2, hV2, hVb.1]
      rw [abs_mul, abs_of_nonneg (sq_nonneg τ₁), abs_mul, abs_of_nonneg (sq_nonneg (S.V q))]
      exact (mul_lt_mul_of_pos_left hqV (pow_pos hτ₁_pos 2)).trans_eq (mul_comm _ 6)
    exact abs_lt.mp (hprod.trans (by linarith only [hτ1_δH]))
  have hβ8 : 8 ≤ Φb^[3] β := by
    have h1 := Φb_ge2 β
    have h2 : Φb^[1] β ≤ Φb^[3] β := Φb_iter_mono (by norm_num) β
    have h3 : max 1 β = β := max_eq_right (by linarith only [hβ4])
    simp only [Function.iterate_one] at h2
    linarith only [h1, h2, h3, hβ4]
  have hV_jc3 : JCΦ 16 (S.Ω ×ˢ Yint) S.V (Φb^[3] β) 0 :=
    (S.V_jc hβ4).mono_m (by norm_num : 1 ≤ 3)
  have hJ_jc := J_coef_jc S.hΩ hβ8 hV_jc3 (fun _ hq => S.V_bounds hq)
    isOpen_Ioo hH_jcΦ (by rw [abs_of_nonneg (sq_nonneg τ₁)]; exact hτ₁_sq_le1) hHT
  have hJcd : ∀ p ∈ S.Ω, ContDiffOn ℝ 15 (fun s => Jfun S.V fctH (τ₁ ^ 2) (p, s)) Yint := fun p hp =>
    hJ_jc.2.2.2.1.comp (contDiffOn_const.prodMk contDiffOn_id) fun s hs => ⟨hp, hs⟩
  have hp1_mem : (ell1, 1, α) ∈ S.Ω := by
    have := hseg 1 (right_mem_Icc.mpr zero_le_one); simpa using this
  -- Apply `ChartSetup.dJ_jets` for `n ≤ 8` and feed into `dJ_comp_Y_sym`
  have hJdiff_bd : ∀ k : ℕ, k ≤ 8 → ∀ y ∈ Yint, 0 ≤ y →
      |iteratedDeriv k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), s) -
        Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), s)) y| ≤
        (τ₁ ^ 3 * CJmax) * max y (8 * c ^ (-(1 / 6 : ℝ))) ^ (4 - k) := by
    intro k hk y hy hy0
    have hdJ := S.dJ_jets hβ4 (0, 1, 0) θ (τ₁ ^ 3) hψ hθ_jc isOpen_Ioo hH_jcΦ
      (by rw [abs_of_nonneg (sq_nonneg τ₁)]; exact hτ₁_sq_le1) hHT hseg
      (fun t ht => (hSA_bounds t ht).1) (fun t ht => (hSA_bounds t ht).2) hy hy0 (by omega : k ≤ 13)
    have hsum : (ell1, 0, α) + ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = (ell1, 1, α) := by ext <;> simp
    rw [hsum] at hdJ
    have hk15 : ((k : ℕ∞) : WithTop ℕ∞) ≤ 15 := by
      rw [show (15 : WithTop ℕ∞) = (((15 : ℕ) : ℕ∞) : WithTop ℕ∞) by rfl]
      exact_mod_cast (by omega : k ≤ 15)
    have hcd1 : ContDiffAt ℝ k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), s)) y :=
      ((hJcd (ell1, 1, α) hp1_mem).contDiffAt (isOpen_Ioo.mem_nhds hy)).of_le (m := (k : ℕ∞)) hk15
    have hcd0 : ContDiffAt ℝ k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), s)) y :=
      ((hJcd (ell1, 0, α) hp0_mem).contDiffAt (isOpen_Ioo.mem_nhds hy)).of_le (m := (k : ℕ∞)) hk15
    rw [show (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), s) -
          Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), s)) =
        (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), s)) -
          (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), s)) from rfl,
      iteratedDeriv_sub hcd1 hcd0]
    have hCJ_le : CJ k (Φb^[3] β) ≤ CJmax :=
      Finset.single_le_sum (fun m _ => hCJ_nn m) (Finset.mem_range.mpr (by omega))
    calc |iteratedDeriv k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), s)) y -
            iteratedDeriv k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), s)) y|
        ≤ |τ₁ ^ 3| * CJ k (Φb^[3] β) * max y (8 * c ^ (-(1 / 6 : ℝ))) ^ (4 - k) := hdJ
      _ = τ₁ ^ 3 * CJ k (Φb^[3] β) * max y (8 * c ^ (-(1 / 6 : ℝ))) ^ (4 - k) := by
          rw [abs_of_pos (pow_pos hτ₁_pos 3)]
      _ ≤ (τ₁ ^ 3 * CJmax) * max y (8 * c ^ (-(1 / 6 : ℝ))) ^ (4 - k) := by gcongr
  have hJdiff_cd : ContDiffOn ℝ 8 (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), s) -
      Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), s)) Yint :=
    ((hJcd (ell1, 1, α) hp1_mem).of_le (by norm_num)).sub ((hJcd (ell1, 0, α) hp0_mem).of_le (by norm_num))
  have hcomp := dJ_comp_Y_sym hc100 (mul_nonneg (pow_nonneg hτ₁_pos.le 3) hCJmax_nn) hJdiff_cd hJdiff_bd
  have hB_eq : (Nat.factorial 8 : ℝ) * 16 ^ 4 * 8 ^ 4 * 100 ^ 8 * (τ₁ ^ 3 * CJmax) * c ^ (-(2 / 3 : ℝ)) =
      C_mult * c ^ (-(17 / 12 : ℝ)) := by
    dsimp only [C_mult]
    rw [hτ₁_3_eq]
    have hc_pow : c ^ (-(3 / 4 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(17 / 12 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    calc (Nat.factorial 8 : ℝ) * 16 ^ 4 * 8 ^ 4 * 100 ^ 8 * (c ^ (-(3 / 4 : ℝ)) * CJmax) * c ^ (-(2 / 3 : ℝ))
        = (Nat.factorial 8 : ℝ) * 16 ^ 4 * 8 ^ 4 * 100 ^ 8 * CJmax * (c ^ (-(3 / 4 : ℝ)) * c ^ (-(2 / 3 : ℝ))) := by
          ring
      _ = (Nat.factorial 8 : ℝ) * 16 ^ 4 * 8 ^ 4 * 100 ^ 8 * CJmax * c ^ (-(17 / 12 : ℝ)) := by
          rw [hc_pow]
  exact hcomp.mono_B Icc_subset_Ici_self hB_eq.le

/-- info: 'FormalResearch.SignUncertainty.fctInner_J1_sub_J0_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInner_J1_sub_J0_sym

end FormalResearch.SignUncertainty
