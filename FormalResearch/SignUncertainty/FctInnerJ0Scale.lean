/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerJ0

/-!
# Fixed-scale chart uniqueness and `J₀ - 1 ∈ 𝒮^{10}(C c^{-4/3})` (`fct:inner-symbols` (b3))

Paper I (`constant_terms_five.tex`), Proof of `(fct:inner-symbols)` (b3):
* `r_rs_chart_exist`: constructs the fixed-scale chart `S_rs` on `Ω_rs = (-1/20, 1/20) × (-1, 1)`
  for `r_rs(p, z) = r_*^2 (z^2 mt(r_*^2 z) - p.2 z θt(r_*^2 z))`, proves `J_rs(p, 0) = 1`,
  `∂_w J_rs((0, 0), 0) = 0`, and `JC 15 (Ω_rs × Yint) J_rs B_Jrs`;
* `Jfun_scale_eq`: uniqueness of `(B, d, R, D, Z, V)` on `(-1, 6)` identifies
  `Jfun S.V fctH (τ₁^2) ((ell1, 0, α), Y) = J_rs ((λ * ell1, τ₁^4 / r_*^2), λ * Y)` (`λ = τ₁^2 / r_*^2`);
* `fctInner_J0_sub_one_sym`: `Jfun S.V fctH (τ₁^2) ((ell1, 0, α), fctInnerY c u) - 1 ∈ 𝒮^{10}(C c^{-4/3})`
  on `[0, U_c]`.

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

/-- Fixed-scale parameter box `Ω_rs = (-1/20, 1/20) × (-1, 1)`. -/
noncomputable def fctOmegaRs : Set (ℝ × ℝ) := Ioo (-(1 / 20 : ℝ)) (1 / 20) ×ˢ Ioo (-1 : ℝ) 1

lemma isOpen_fctOmegaRs : IsOpen fctOmegaRs := isOpen_Ioo.prod isOpen_Ioo

/-- Rescaled remainder `r_rs((ℓ_rs, μ_θ), z) = r_*^2 (z^2 concreteMt(r_*^2 z) - μ_θ z θt(r_*^2 z))`. -/
noncomputable def fctRrs (r_star : ℝ) (θt : ℝ → ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ :=
  r_star ^ 2 * (q.2 ^ 2 * concreteMt (r_star ^ 2 * q.2) - q.1.2 * q.2 * θt (r_star ^ 2 * q.2))

private lemma hasDerivAt_mul_zero {g : ℝ → ℝ} (hg : ContinuousAt g 0) :
    HasDerivAt (fun x => x * g x) (g 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h1 : (fun t : ℝ => t⁻¹ • ((0 + t) * g (0 + t) - 0 * g 0)) =ᶠ[𝓝[≠] (0 : ℝ)] g := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [zero_add, zero_mul, sub_zero, smul_eq_mul]
    rw [inv_mul_cancel_left₀ ht]
  exact hg.tendsto.mono_left nhdsWithin_le_nhds |>.congr' h1.symm

/-- Fixed-scale chart data: given `M_box cR_box C0_box ≥ 0`, there is a fixed `r_star > 0` and
a uniform `B_Jrs ≥ 0` (independent of `θt`) such that for any `mt, θt` with `JC 18 (-1/30, 1/30) _ M_box`
and `mt 0 = 7 π^4 / 7200`, the chart `S_rs` exists on `fctOmegaRs`, `J_rs(p, 0) = 1`,
`deriv (J_rs (0, 0)) 0 = 0`, and `JC 15 (fctOmegaRs ×ˢ Yint) J_rs B_Jrs`. -/
lemma r_rs_chart_exist {M_box cR_box C0_box : ℝ}
    (hM0 : 0 ≤ M_box) (hcR0 : 0 ≤ cR_box) (hC0_pos : 0 ≤ C0_box) :
    ∃ (r_star B_Jrs δH : ℝ), 0 < r_star ∧ r_star ^ 2 ≤ 1 / 200 ∧ 0 < δH ∧ δH ≤ 1 / 30 ∧
      6 * r_star ^ 2 < δH ∧ cR_box * C0_box * r_star ^ 2 < 1 / 50 ∧ 0 ≤ B_Jrs ∧
      ∀ {θt : ℝ → ℝ},
        JC 18 (Ioo (-(1 / 30 : ℝ)) (1 / 30)) concreteMt M_box →
        JC 18 (Ioo (-(1 / 30 : ℝ)) (1 / 30)) θt M_box →
        ∃ S_rs : ChartSetup (ℝ × ℝ),
          S_rs.Ω = fctOmegaRs ∧ S_rs.ℓ = Prod.fst ∧
          S_rs.r = fctRrs r_star θt ∧
          15 * S_rs.ε ≤ 1 / 2 ∧
          JC 15 (fctOmegaRs ×ˢ Yint) (Jfun S_rs.V fctH (r_star ^ 2)) B_Jrs ∧
          (∀ p ∈ fctOmegaRs, Jfun S_rs.V fctH (r_star ^ 2) (p, 0) = 1) ∧
          deriv (fun w : ℝ => Jfun S_rs.V fctH (r_star ^ 2) ((0, 0), w)) 0 = 0 := by
  obtain ⟨cB, cd, cR, cD, cZ, cV, hcB, hcd, hcR, hcD, hcZ, hcV, ε0, hε0_pos, hcore⟩ :=
    cfu_chart_core (P := ℝ × ℝ)
  obtain ⟨δH, C_H, hδH_pos, hδH_30, hCH4, hH_jc, _⟩ := fctH_spec
  let U_rs : Set ((ℝ × ℝ) × ℝ) := fctOmegaRs ×ˢ Ioo (-1 : ℝ) 6
  have hU_open : IsOpen U_rs := isOpen_fctOmegaRs.prod isOpen_Ioo
  have hUd : UniqueDiffOn ℝ U_rs := hU_open.uniqueDiffOn
  -- Raw `JC 18` bound on `(z^2 mt(...) - μ_θ z θt(...))` valid whenever `r_star^2 ≤ 1/200`
  let M1 : ℝ := max 6 M_box
  have hM1 : 1 ≤ M1 := le_trans (by norm_num) (le_max_left 6 M_box)
  have hM1_0 : 0 ≤ M1 := by linarith
  let C_comp : ℝ := (Nat.factorial 18 : ℝ) * M_box * (max 1 6) ^ 18
  have hCcomp_0 : 0 ≤ C_comp := by positivity
  let C_raw : ℝ := 2 ^ 18 * (2 ^ 18 * 6 * 6) * C_comp + 2 ^ 18 * (2 ^ 18 * 1 * 6) * C_comp
  have hCraw_pos : 0 < C_raw + 1 := by positivity
  let cm : ℝ := max 1 (max cB (max cd (max cD (max cV 15))))
  have hcm_pos : 0 < cm := by positivity
  let thresh : ℝ := min (1 / 200 : ℝ) (min (δH / 12) (min (1 / (50 * (cR_box * C0_box + 1)))
    (min (ε0 / (C_raw + 1)) (1 / (100 * cm * (C_raw + 1))))))
  have hthresh_pos : 0 < thresh := by positivity
  let r_star : ℝ := Real.sqrt thresh
  have hr_pos : 0 < r_star := Real.sqrt_pos.mpr hthresh_pos
  have hr_sq : r_star ^ 2 = thresh := Real.sq_sqrt hthresh_pos.le
  have hr_200 : r_star ^ 2 ≤ 1 / 200 := hr_sq ▸ min_le_left _ _
  have hr_δH : 6 * r_star ^ 2 < δH := by
    have h1 : r_star ^ 2 ≤ δH / 12 := hr_sq ▸ (min_le_right _ _ |>.trans (min_le_left _ _))
    linarith
  have hr_cR : cR_box * C0_box * r_star ^ 2 < 1 / 50 := by
    have h1 : r_star ^ 2 ≤ 1 / (50 * (cR_box * C0_box + 1)) :=
      hr_sq ▸ (min_le_right _ _ |>.trans (min_le_right _ _ |>.trans (min_le_left _ _)))
    have hpos : (0 : ℝ) < 50 * (cR_box * C0_box + 1) := by positivity
    calc cR_box * C0_box * r_star ^ 2
        ≤ cR_box * C0_box * (1 / (50 * (cR_box * C0_box + 1))) := by gcongr
      _ = (cR_box * C0_box) / (50 * (cR_box * C0_box + 1)) := by ring
      _ < (cR_box * C0_box + 1) / (50 * (cR_box * C0_box + 1)) := by
          gcongr; linarith
      _ = 1 / 50 := by field_simp [show cR_box * C0_box + 1 ≠ 0 by positivity]
  let ε_rs : ℝ := r_star ^ 2 * (C_raw + 1)
  have hεrs_nn : 0 ≤ ε_rs := by positivity
  have hεrs_le : ε_rs ≤ ε0 := by
    have h1 : r_star ^ 2 ≤ ε0 / (C_raw + 1) :=
      hr_sq ▸ (min_le_right _ _ |>.trans (min_le_right _ _ |>.trans (min_le_right _ _ |>.trans (min_le_left _ _))))
    calc ε_rs = r_star ^ 2 * (C_raw + 1) := rfl
      _ ≤ (ε0 / (C_raw + 1)) * (C_raw + 1) := mul_le_mul_of_nonneg_right h1 hCraw_pos.le
      _ = ε0 := div_mul_cancel₀ _ hCraw_pos.ne'
  have hcm_bd : cm * ε_rs ≤ 1 / 100 := by
    have h1 : r_star ^ 2 ≤ 1 / (100 * cm * (C_raw + 1)) :=
      hr_sq ▸ (min_le_right _ _ |>.trans (min_le_right _ _ |>.trans (min_le_right _ _ |>.trans (min_le_right _ _))))
    have hne : 100 * cm * (C_raw + 1) ≠ 0 := by positivity
    calc cm * ε_rs = cm * (C_raw + 1) * r_star ^ 2 := by dsimp only [ε_rs]; ring
      _ ≤ cm * (C_raw + 1) * (1 / (100 * cm * (C_raw + 1))) := by gcongr
      _ = 1 / 100 := by field_simp [hne]
  let β_rs : ℝ := max 4 C_H
  have hβrs4 : 4 ≤ β_rs := le_max_left 4 C_H
  have hβrs8 : 8 ≤ Φb^[3] β_rs := by
    have h1 := Φb_ge2 β_rs
    have h2 : Φb^[1] β_rs ≤ Φb^[3] β_rs := Φb_iter_mono (by norm_num) β_rs
    have h3 : max 1 β_rs = β_rs := max_eq_right (by linarith only [hβrs4])
    simp only [Function.iterate_one] at h2
    linarith only [h1, h2, h3, hβrs4]
  let B_Jrs : ℝ := Φb^[9] (Φb^[3] β_rs)
  have hBJrs_nn : 0 ≤ B_Jrs := Φb_iter_nonneg (Φb_iter_nonneg (by linarith only [hβrs4]) 3) 9
  refine ⟨r_star, B_Jrs, δH, hr_pos, hr_200, hδH_pos, hδH_30, hr_δH, hr_cR, hBJrs_nn, ?_⟩
  intro θt hmt hθt
  -- Construct `JC 18 U_rs (fctRrs r_star θt) ε_rs`
  have hz_jc : JC 18 U_rs (fun q : (ℝ × ℝ) × ℝ => q.2) 6 :=
    JC.snd hUd (by norm_num) fun q hq => by
      rw [abs_le]; constructor <;> linarith [hq.2.1, hq.2.2]
  have hz2_jc : JC 18 U_rs (fun q : (ℝ × ℝ) × ℝ => q.2 ^ 2) (2 ^ 18 * 6 * 6) :=
    (JC.mul hUd (by norm_num) (by norm_num) hz_jc hz_jc).congr fun q _ => by ring
  let L_μ : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
  have hLμ_norm : ‖L_μ‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => ?_
    simpa [L_μ, one_mul] using (norm_snd_le q.1).trans (norm_fst_le q)
  have hμ_jc : JC 18 U_rs (fun q : (ℝ × ℝ) × ℝ => q.1.2) 1 :=
    JC.clm hUd L_μ hLμ_norm fun q hq => by
      have h1 := hq.1.2
      simpa [L_μ, Real.norm_eq_abs, abs_le] using ⟨h1.1.le, h1.2.le⟩
  have hμz_jc : JC 18 U_rs (fun q : (ℝ × ℝ) × ℝ => q.1.2 * q.2) (2 ^ 18 * 1 * 6) :=
    JC.mul hUd zero_le_one (by norm_num) hμ_jc hz_jc
  have hr2z_jc : JC 18 U_rs (fun q : (ℝ × ℝ) × ℝ => r_star ^ 2 * q.2) 6 := by
    refine (hz_jc.const_smul hUd (r_star ^ 2)).mono ?_
    rw [abs_of_pos (sq_pos_of_pos hr_pos)]
    exact mul_le_of_le_one_left (by norm_num) (by linarith only [hr_200])
  have hmaps_30 : MapsTo (fun q : (ℝ × ℝ) × ℝ => r_star ^ 2 * q.2) U_rs (Ioo (-(1 / 30 : ℝ)) (1 / 30)) := by
    intro q hq
    have hq2 : |q.2| < 6 := by rw [abs_lt]; constructor <;> linarith [hq.2.1, hq.2.2]
    have hprod : |r_star ^ 2 * q.2| < 6 / 200 := by
      rw [abs_mul, abs_of_pos (sq_pos_of_pos hr_pos)]
      nlinarith only [hr_200, hq2, sq_pos_of_pos hr_pos]
    exact abs_lt.mp (hprod.trans (by norm_num))
  have hmt_c : JC 18 U_rs (fun q => concreteMt (r_star ^ 2 * q.2)) C_comp :=
    JC.comp hUd isOpen_Ioo.uniqueDiffOn hM0 hmt hr2z_jc hmaps_30
  have hθt_c : JC 18 U_rs (fun q => θt (r_star ^ 2 * q.2)) C_comp :=
    JC.comp hUd isOpen_Ioo.uniqueDiffOn hM0 hθt hr2z_jc hmaps_30
  have hraw_jc : JC 18 U_rs
      (fun q : (ℝ × ℝ) × ℝ => q.2 ^ 2 * concreteMt (r_star ^ 2 * q.2) - q.1.2 * q.2 * θt (r_star ^ 2 * q.2))
      C_raw :=
    (JC.mul hUd (by positivity) hCcomp_0 hz2_jc hmt_c).sub hUd
      (JC.mul hUd (by positivity) hCcomp_0 hμz_jc hθt_c)
  have hr_jc : JC 18 U_rs (fctRrs r_star θt) ε_rs := by
    have hle : |r_star ^ 2| * C_raw ≤ ε_rs := by
      rw [abs_of_pos (sq_pos_of_pos hr_pos)]
      dsimp only [ε_rs]; nlinarith only [sq_nonneg r_star]
    have h1 := (hraw_jc.const_smul hUd (r_star ^ 2)).congr fun q _ => by
      dsimp only [fctRrs]; rw [smul_eq_mul]
    exact h1.mono hle
  -- Apply `cfu_chart_core`
  let L_ℓ : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  have hLℓ_norm : ‖L_ℓ‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
    simpa [L_ℓ, one_mul] using norm_fst_le p
  have hℓ_jc : JC 16 fctOmegaRs Prod.fst 3 :=
    (JC.clm isOpen_fctOmegaRs.uniqueDiffOn L_ℓ hLℓ_norm fun p hp => by
      have h1 := hp.1
      simpa [L_ℓ, Real.norm_eq_abs, abs_le] using ⟨by linarith [h1.1], by linarith [h1.2]⟩).mono
      (by norm_num : (1 : ℝ) ≤ 3)
  have hℓ_rng : ∀ p ∈ fctOmegaRs, (-1 / 10 : ℝ) < p.1 ∧ p.1 < 27 / 10 := fun p hp =>
    ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
  obtain ⟨B, d, R, Z, hB_jc, hB_eq, hd_jc, hd_eq, hR_jc, hR_eq, hD_jc, hZ_jc, hZ_eq, hV_jc, hcalg⟩ :=
    hcore isOpen_fctOmegaRs hεrs_nn hεrs_le hr_jc hℓ_jc hℓ_rng
  have hout : ChartOut cB cd cR cD cZ cV fctOmegaRs (fctRrs r_star θt) Prod.fst ε_rs B d R Z :=
    ⟨hB_jc, hB_eq, hd_jc, hd_eq, hR_jc, hR_eq, hD_jc, hZ_jc, hZ_eq, hV_jc, hcalg⟩
  have hle_cm : ∀ {x : ℝ}, x ≤ cm → x * ε_rs ≤ 1 / 100 := fun {x} hx =>
    (mul_le_mul_of_nonneg_right hx hεrs_nn).trans hcm_bd
  have hcB_cm : cB ≤ cm := le_trans (le_max_left _ _) (le_max_right _ _)
  have hcd_cm : cd ≤ cm := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hcD_cm : cD ≤ cm :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hcV_cm : cV ≤ cm :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have h15_cm : (15 : ℝ) ≤ cm :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  let S_rs : ChartSetup (ℝ × ℝ) :=
    { Ω := fctOmegaRs
      hΩ := isOpen_fctOmegaRs
      r := fctRrs r_star θt
      ℓ := Prod.fst
      cB := cB
      cd := cd
      cR := cR
      cD := cD
      cZ := cZ
      cV := cV
      ε := ε_rs
      B := B
      d := d
      R := R
      Z := Z
      out := hout
      hr := hr_jc
      hℓ := fun p hp => ⟨by linarith [(hℓ_rng p hp).1], by linarith [(hℓ_rng p hp).2]⟩
      hℓd := (ContinuousLinearMap.fst ℝ ℝ ℝ).differentiable.differentiableOn
      hℓj := hℓ_jc
      hcV := hle_cm hcV_cm
      hcV0 := hcV
      hε := hεrs_nn
      hcB := hle_cm hcB_cm
      hcd := hle_cm hcd_cm
      hcD := hle_cm hcD_cm
      hcB0 := hcB
      hcd0 := hcd
      hcD0 := hcD }
  have h15ε : 15 * S_rs.ε ≤ 1 / 2 := by
    have h1 : 15 * ε_rs ≤ 1 / 100 := hle_cm h15_cm
    change 15 * ε_rs ≤ 1 / 2; linarith only [h1]
  -- `JC 15 (fctOmegaRs ×ˢ Yint) (Jfun S_rs.V fctH (r_star^2)) B_Jrs`
  have hH_jcΦ : JCΦ 16 (Ioo (-δH) δH) fctH (Φb^[3] β_rs) 0 :=
    hH_jc.mono ((le_max_right 4 C_H).trans (Φb_iter_ge 3 β_rs))
  have hV_jc3 : JCΦ 16 (fctOmegaRs ×ˢ Yint) S_rs.V (Φb^[3] β_rs) 0 :=
    (S_rs.V_jc hβrs4).mono_m (by norm_num : 1 ≤ 3)
  have hHT_rs : ∀ q ∈ fctOmegaRs ×ˢ Yint, r_star ^ 2 * (q.2 * S_rs.V q ^ 2) ∈ Ioo (-δH) δH := by
    intro q hq
    have hVb := S_rs.V_bounds hq
    have hV2 : S_rs.V q ^ 2 ≤ 36 / 25 := by nlinarith only [hVb.1, hVb.2]
    have hq2 : |q.2| < 3.6 := by rw [abs_lt]; constructor <;> linarith only [hq.2.1, hq.2.2]
    have hqV : |q.2| * S_rs.V q ^ 2 < 6 := by nlinarith only [abs_nonneg q.2, hq2, hV2, hVb.1]
    have hprod : |r_star ^ 2 * (q.2 * S_rs.V q ^ 2)| < 6 * r_star ^ 2 := by
      rw [abs_mul, abs_of_pos (sq_pos_of_pos hr_pos), abs_mul, abs_of_nonneg (sq_nonneg (S_rs.V q))]
      exact (mul_lt_mul_of_pos_left hqV (sq_pos_of_pos hr_pos)).trans_eq (mul_comm _ 6)
    exact abs_lt.mp (hprod.trans hr_δH)
  have hr2_le1 : |r_star ^ 2| ≤ 1 := by
    rw [abs_of_pos (sq_pos_of_pos hr_pos)]; linarith only [hr_200]
  have hJ_jc := J_coef_jc isOpen_fctOmegaRs hβrs8 hV_jc3 (fun _ hq => S_rs.V_bounds hq)
    isOpen_Ioo hH_jcΦ hr2_le1 hHT_rs
  -- `Jfun S_rs.V fctH (r_star^2) (p, 0) = 1`
  have hJ0_val : ∀ p ∈ fctOmegaRs, Jfun S_rs.V fctH (r_star ^ 2) (p, 0) = 1 := by
    intro p hp
    have hVp := (S_rs.V_bounds (show (p, (0 : ℝ)) ∈ fctOmegaRs ×ˢ Yint from ⟨hp, zero_mem_Yint⟩)).1
    have hVne : S_rs.V (p, 0) ≠ 0 := by linarith
    simp [Jfun, fctH_zero, mul_inv_cancel₀ hVne]
  -- `deriv (fun w => Jfun S_rs.V fctH (r_star^2) ((0, 0), w)) 0 = 0`
  have hp00 : ((0 : ℝ), (0 : ℝ)) ∈ fctOmegaRs := ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  have hderiv0 : deriv (fun w : ℝ => Jfun S_rs.V fctH (r_star ^ 2) ((0, 0), w)) 0 = 0 := by
    -- Compute `S_rs.B (0, 0) = 0`, `S_rs.d (0, 0) = dStar`, `S_rs.R ((0,0), 0)`, `S_rs.Z ((0,0), 0) = 0`, etc.
    have hρ_rs : ∀ p ∈ S_rs.Ω, ∀ z ∈ Ioo (-1 : ℝ) 6, |rhoF S_rs.r (p, z)| ≤ 1 / 2 * |z| := by
      intro p hp z hz
      have hOrs : IsOpen (S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6) := S_rs.hΩ.prod isOpen_Ioo
      have hr0 : rhoF S_rs.r (p, 0) = 0 := by
        have hrs0 : S_rs.r (p, 0) = 0 := by change fctRrs r_star θt (p, 0) = 0; simp [fctRrs]
        simp [rhoF, hrs0]
      have hp_emb : ContDiffOn ℝ 18 (fun w : ℝ => (p, w)) (Ioo (-1 : ℝ) 6) := by fun_prop
      have hrho_cd : ContDiffOn ℝ 1 (fun w => rhoF S_rs.r (p, w)) (Ioo (-1 : ℝ) 6) := by
        have hr_w : ContDiffOn ℝ 18 (fun w => S_rs.r (p, w)) (Ioo (-1 : ℝ) 6) :=
          S_rs.hr.1.comp hp_emb fun w hw => ⟨hp, hw⟩
        have h17 := (S_rs.hr.succ_fderiv hOrs).clm_apply_const hOrs.uniqueDiffOn ((0 : ℝ × ℝ), (1 : ℝ))
        have hfd_w : ContDiffOn ℝ 17 (fun w => fderiv ℝ S_rs.r (p, w) (0, 1)) (Ioo (-1 : ℝ) 6) :=
          h17.1.comp (hp_emb.of_le (by norm_num : (17 : WithTop ℕ∞) ≤ 18)) fun w hw => ⟨hp, hw⟩
        refine ((hr_w.of_le (by norm_num)).add (contDiffOn_const.mul (contDiffOn_id.mul (hfd_w.of_le (by norm_num))))).congr
          fun _ _ => rfl
      have hderiv_bd : ∀ w ∈ Ioo (-1 : ℝ) 6, |deriv (fun t => rhoF S_rs.r (p, t)) w| ≤ 1 / 2 := by
        intro w hw
        have hq : (p, w) ∈ S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hp, hw⟩
        have h17 := (S_rs.hr.succ_fderiv hOrs).clm_apply_const hOrs.uniqueDiffOn ((0 : ℝ × ℝ), (1 : ℝ))
        have hdr : HasDerivAt (fun t => S_rs.r (p, t)) (fderiv ℝ S_rs.r (p, w) (0, 1)) w := by
          have h1 := ((S_rs.hr.1.contDiffAt (hOrs.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt
          have h2 : HasDerivAt (fun t : ℝ => (p, t)) ((0 : ℝ × ℝ), (1 : ℝ)) w :=
            (hasDerivAt_const w p).prodMk (hasDerivAt_id w)
          exact h1.comp_hasDerivAt w h2
        have hd2 : HasDerivAt (fun t => fderiv ℝ S_rs.r (p, t) (0, 1))
            (fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p, w) (0, 1)) w := by
          have h1 := ((h17.1.contDiffAt (hOrs.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt
          have h2 : HasDerivAt (fun t : ℝ => (p, t)) ((0 : ℝ × ℝ), (1 : ℝ)) w :=
            (hasDerivAt_const w p).prodMk (hasDerivAt_id w)
          exact h1.comp_hasDerivAt w h2
        have htot : HasDerivAt (fun t => rhoF S_rs.r (p, t))
            (fderiv ℝ S_rs.r (p, w) (0, 1) + 2 * (1 * fderiv ℝ S_rs.r (p, w) (0, 1) +
              w * fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p, w) (0, 1))) w :=
          (hdr.add (((hasDerivAt_id w).mul hd2).const_mul 2)).congr_of_eventuallyEq
            (Eventually.of_forall fun t => by simp [rhoF])
        rw [htot.deriv]
        have hb1 : |fderiv ℝ S_rs.r (p, w) (0, 1)| ≤ S_rs.ε := by
          have hbd := S_rs.hr.2 1 (by norm_num) (p, w) hq
          rw [norm_iteratedFDerivWithin_one _ (hOrs.uniqueDiffOn _ hq), fderivWithin_of_isOpen hOrs hq] at hbd
          calc |fderiv ℝ S_rs.r (p, w) (0, 1)| = ‖fderiv ℝ S_rs.r (p, w) (0, 1)‖ := Real.norm_eq_abs _
            _ ≤ ‖fderiv ℝ S_rs.r (p, w)‖ * ‖((0 : ℝ × ℝ), (1 : ℝ))‖ := (fderiv ℝ _ _).le_opNorm _
            _ ≤ S_rs.ε * 1 := mul_le_mul hbd (by simp [Prod.norm_def]) (norm_nonneg _) S_rs.hε
            _ = S_rs.ε := mul_one _
        have hb2 : |fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p, w) (0, 1)| ≤ S_rs.ε := by
          have hbd := h17.2 1 (by norm_num) (p, w) hq
          rw [norm_iteratedFDerivWithin_one _ (hOrs.uniqueDiffOn _ hq), fderivWithin_of_isOpen hOrs hq] at hbd
          have hn1 : ‖((0 : ℝ × ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
          rw [hn1, one_mul] at hbd
          calc |fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p, w) (0, 1)|
              = ‖fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p, w) (0, 1)‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p, w)‖ * ‖((0 : ℝ × ℝ), (1 : ℝ))‖ :=
                (fderiv ℝ _ _).le_opNorm _
            _ ≤ S_rs.ε * 1 := mul_le_mul hbd (le_of_eq hn1) (norm_nonneg _) S_rs.hε
            _ = S_rs.ε := mul_one _
        have hw6 : |w| ≤ 6 := by rw [abs_le]; constructor <;> linarith only [hw.1, hw.2]
        calc |fderiv ℝ S_rs.r (p, w) (0, 1) + 2 * (1 * fderiv ℝ S_rs.r (p, w) (0, 1) +
                w * fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p, w) (0, 1))|
            = |3 * fderiv ℝ S_rs.r (p, w) (0, 1) +
                2 * w * fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p, w) (0, 1)| := by congr 1; ring
          _ ≤ |3 * fderiv ℝ S_rs.r (p, w) (0, 1)| +
                |2 * w * fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p, w) (0, 1)| := abs_add_le _ _
          _ = 3 * |fderiv ℝ S_rs.r (p, w) (0, 1)| + 2 * |w| *
                |fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p, w) (0, 1)| := by
              rw [abs_mul, abs_mul, abs_mul, show |(3 : ℝ)| = 3 by norm_num, show |(2 : ℝ)| = 2 by norm_num]
          _ ≤ 3 * S_rs.ε + 2 * 6 * S_rs.ε := by gcongr
          _ = 15 * S_rs.ε := by ring
          _ ≤ 1 / 2 := h15ε
      have hmv := (convex_Ioo (-1 : ℝ) 6).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun w hw => ((hrho_cd.differentiableOn (by norm_num) w hw).hasDerivWithinAt).congr_deriv
          (by rw [derivWithin_of_isOpen isOpen_Ioo hw]))
        (fun w hw => by rw [Real.norm_eq_abs]; exact hderiv_bd w hw)
        (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 6 from ⟨by norm_num, by norm_num⟩) hz
      simpa [hr0, Real.norm_eq_abs, sub_zero] using hmv
    have hB00 : S_rs.B (0, 0) = 0 := S_rs.B_zero hρ_rs hp00 rfl
    have h000_Ioo : (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) ∈ S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hp00, by norm_num, by norm_num⟩
    have h000_Yint : (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) ∈ S_rs.Ω ×ˢ Yint := ⟨hp00, zero_mem_Yint⟩
    have hrz0 : fderiv ℝ S_rs.r ((0, 0), 0) (0, 1) = 0 := by
      have h1 : HasDerivAt (fun z : ℝ => S_rs.r ((0, 0), z)) 0 0 := by
        have hfn : ∀ z : ℝ, S_rs.r ((0, 0), z) = z * (z * (r_star ^ 2 * concreteMt (r_star ^ 2 * z))) :=
          fun z => by change fctRrs r_star θt ((0, 0), z) = _; simp [fctRrs]; ring
        have hm_c : ContinuousAt (fun z : ℝ => r_star ^ 2 * concreteMt (r_star ^ 2 * z)) 0 := by
          have h0_30 : (0 : ℝ) ∈ Ioo (-(1 / 30 : ℝ)) (1 / 30) := ⟨by norm_num, by norm_num⟩
          have hmul_c : ContinuousAt (fun z : ℝ => r_star ^ 2 * z) 0 :=
            continuousAt_const.mul continuousAt_id
          exact continuousAt_const.mul
            ((hmt.1.continuousOn.continuousAt (isOpen_Ioo.mem_nhds h0_30)).comp_of_eq hmul_c (mul_zero _))
        have hd_z2 : HasDerivAt (fun z : ℝ => z * (z * (r_star ^ 2 * concreteMt (r_star ^ 2 * z)))) 0 0 := by
          have h := hasDerivAt_mul_zero (continuousAt_id.mul hm_c)
          simpa using h
        exact hd_z2.congr_of_eventuallyEq (Eventually.of_forall fun z => hfn z)
      have hO : IsOpen (S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6) := S_rs.hΩ.prod isOpen_Ioo
      have hf := ((S_rs.hr.1.contDiffAt (hO.mem_nhds h000_Ioo)).differentiableAt (by norm_num)).hasFDerivAt
      have h2 : HasDerivAt (fun z : ℝ => (((0 : ℝ), (0 : ℝ)), z)) ((0 : ℝ × ℝ), (1 : ℝ)) 0 :=
        (hasDerivAt_const (0 : ℝ) ((0 : ℝ), (0 : ℝ))).prodMk (hasDerivAt_id (0 : ℝ))
      exact (hf.comp_hasDerivAt 0 h2).unique h1
    have hd00 : S_rs.d (0, 0) = dStar := by
      obtain ⟨hdpos, hdcube⟩ := S_rs.out.2.2.2.1 (0, 0) hp00
      rw [hB00, hrz0, mul_zero, sub_zero] at hdcube
      have hd3 : dStar ^ 3 = π ^ 2 / 12 := by
        unfold dStar; rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      have hd_pos : 0 < dStar := by unfold dStar; positivity
      exact pow_left_inj₀ hdpos.le hd_pos.le (by norm_num : 3 ≠ 0) |>.mp (hdcube.trans hd3.symm)
    have hrzz0 : fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) ((0, 0), 0) (0, 1) =
        2 * r_star ^ 2 * concreteMt 0 := by
      have hO : IsOpen (S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6) := S_rs.hΩ.prod isOpen_Ioo
      have h_eq : ∀ᶠ w in 𝓝 (0 : ℝ),
          fderiv ℝ S_rs.r ((0, 0), w) (0, 1) =
            2 * r_star ^ 2 * w * concreteMt (r_star ^ 2 * w) +
              r_star ^ 4 * w ^ 2 * deriv concreteMt (r_star ^ 2 * w) := by
        filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 6)] with w hw
        have hqw : ((0, 0), w) ∈ S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hp00, hw⟩
        have h1 := ((S_rs.hr.1.contDiffAt (hO.mem_nhds hqw)).differentiableAt (by norm_num)).hasFDerivAt
        have h2 : HasDerivAt (fun t : ℝ => (((0 : ℝ), (0 : ℝ)), t)) ((0 : ℝ × ℝ), (1 : ℝ)) w :=
          (hasDerivAt_const w ((0 : ℝ), (0 : ℝ))).prodMk (hasDerivAt_id w)
        have hd_lhs := h1.comp_hasDerivAt w h2
        have hw30 : r_star ^ 2 * w ∈ Ioo (-(1 / 30 : ℝ)) (1 / 30) := hmaps_30 hqw
        have hmt_at : DifferentiableAt ℝ concreteMt (r_star ^ 2 * w) :=
          (hmt.1.contDiffAt (isOpen_Ioo.mem_nhds hw30)).differentiableAt (by norm_num)
        have hd_mt : HasDerivAt (fun t => concreteMt (r_star ^ 2 * t))
            (deriv concreteMt (r_star ^ 2 * w) * r_star ^ 2) w := by
          have harg : HasDerivAt (fun t : ℝ => r_star ^ 2 * t) (r_star ^ 2) w :=
            ((hasDerivAt_id w).const_mul (r_star ^ 2)).congr_deriv (mul_one _)
          exact hmt_at.hasDerivAt.comp w harg
        have hd_rhs : HasDerivAt (fun t => S_rs.r ((0, 0), t))
            (2 * r_star ^ 2 * w * concreteMt (r_star ^ 2 * w) +
              r_star ^ 4 * w ^ 2 * deriv concreteMt (r_star ^ 2 * w)) w := by
          have hprod := ((hasDerivAt_pow 2 w).const_mul (r_star ^ 2)).mul hd_mt
          refine (hprod.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
          change fctRrs r_star θt ((0, 0), t) = _
          simp [fctRrs]; ring
        exact hd_lhs.unique hd_rhs
      have hd_g : HasDerivAt (fun w : ℝ =>
          2 * r_star ^ 2 * w * concreteMt (r_star ^ 2 * w) +
            r_star ^ 4 * w ^ 2 * deriv concreteMt (r_star ^ 2 * w))
          (2 * r_star ^ 2 * concreteMt 0) 0 := by
        have h0_30 : (0 : ℝ) ∈ Ioo (-(1 / 30 : ℝ)) (1 / 30) := ⟨by norm_num, by norm_num⟩
        have hmul_c : ContinuousAt (fun w : ℝ => r_star ^ 2 * w) 0 :=
          continuousAt_const.mul continuousAt_id
        have hm_c : ContinuousAt (fun w => concreteMt (r_star ^ 2 * w)) 0 :=
          (hmt.1.continuousOn.continuousAt (isOpen_Ioo.mem_nhds h0_30)).comp_of_eq hmul_c (mul_zero _)
        have hd1 : HasDerivAt (fun w => w * (2 * r_star ^ 2 * concreteMt (r_star ^ 2 * w)))
            (2 * r_star ^ 2 * concreteMt (r_star ^ 2 * 0)) 0 :=
          hasDerivAt_mul_zero (continuousAt_const.mul hm_c)
        have hdm_c : ContinuousAt (fun w => r_star ^ 4 * deriv concreteMt (r_star ^ 2 * w)) 0 := by
          have h17 := (hmt.succ_fderiv isOpen_Ioo).clm_apply_const isOpen_Ioo.uniqueDiffOn (1 : ℝ)
          have hcont : ContinuousAt (fun y => deriv concreteMt y) 0 := by
            refine (h17.1.continuousOn.continuousAt (isOpen_Ioo.mem_nhds h0_30)).congr ?_
            exact Eventually.of_forall fun y => by simp
          exact continuousAt_const.mul (hcont.comp_of_eq hmul_c (mul_zero _))
        have hd2 : HasDerivAt (fun w => w * (w * (r_star ^ 4 * deriv concreteMt (r_star ^ 2 * w)))) 0 0 :=
          (hasDerivAt_mul_zero (continuousAt_id.mul hdm_c)).congr_deriv (by simp)
        have htot := (hd1.add hd2).congr_deriv (by simp)
        refine htot.congr_of_eventuallyEq (Eventually.of_forall fun w => by ring)
      have h17 := (S_rs.hr.succ_fderiv hO).clm_apply_const hO.uniqueDiffOn ((0 : ℝ × ℝ), (1 : ℝ))
      have hf := ((h17.1.contDiffAt (hO.mem_nhds h000_Ioo)).differentiableAt (by norm_num)).hasFDerivAt
      have h2 : HasDerivAt (fun w : ℝ => (((0 : ℝ), (0 : ℝ)), w)) ((0 : ℝ × ℝ), (1 : ℝ)) 0 :=
        (hasDerivAt_const (0 : ℝ) ((0 : ℝ), (0 : ℝ))).prodMk (hasDerivAt_id (0 : ℝ))
      exact (hf.comp_hasDerivAt 0 h2).unique (hd_g.congr_of_eventuallyEq h_eq)
    have hhad0 : hadH S_rs.r S_rs.B ((0, 0), 0) = r_star ^ 2 * concreteMt 0 := by
      unfold hadH
      have heq : ∀ σ ∈ Icc (0 : ℝ) 1, (1 - σ) * fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1))
          ((0, 0), S_rs.B (0, 0) + σ * (0 - S_rs.B (0, 0))) (0, 1) =
          (1 - σ) * (2 * r_star ^ 2 * concreteMt 0) := fun σ _ => by
        rw [hB00]; simp [hrzz0]
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc heq,
        MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
      have hint : ∫ σ in (0 : ℝ)..1, (1 - σ) = 1 / 2 := by
        have hder : ∀ σ ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x - x ^ 2 / 2) (1 - σ) σ := fun σ _ => by
          have := (hasDerivAt_id σ).sub (((hasDerivAt_pow 2 σ).div_const 2))
          exact this.congr_deriv (by ring)
        have hint' := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
          ((continuousOn_const.sub continuousOn_id).intervalIntegrable)
        linarith only [hint']
      rw [intervalIntegral.integral_mul_const, hint]; ring
    have hR00 : S_rs.R ((0, 0), 0) = -(r_star ^ 2 * concreteMt 0) / dStar ^ 2 := by
      have hreq := (S_rs.out.2.2.2.2.2.1 ((0, 0), 0) h000_Ioo).2
      rw [hhad0, hd00] at hreq
      have hd2_ne : dStar ^ 2 ≠ 0 := by unfold dStar; positivity
      linarith [eq_div_of_mul_eq hd2_ne (by linarith : S_rs.R ((0, 0), 0) * dStar ^ 2 = -(r_star ^ 2 * concreteMt 0))]
    have hD00 : S_rs.D ((0, 0), 0) = dStar := by
      simp [ChartSetup.D, Dfun, hB00, hd00]
    have hDz00 : fderiv ℝ S_rs.D ((0, 0), 0) (0, 1) = S_rs.R ((0, 0), 0) := by
      have h1 : HasDerivAt (fun z : ℝ => S_rs.D ((0, 0), z)) (S_rs.R ((0, 0), 0)) 0 := by
        have hfn : ∀ z : ℝ, S_rs.D ((0, 0), z) = dStar + z * S_rs.R ((0, 0), z) := fun z => by
          simp [ChartSetup.D, Dfun, hB00, hd00]
        have hRc : ContinuousAt (fun z : ℝ => S_rs.R ((0, 0), z)) 0 := by
          have hO : IsOpen (S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6) := S_rs.hΩ.prod isOpen_Ioo
          exact (S_rs.out.2.2.2.2.1.1.continuousOn.continuousAt (hO.mem_nhds h000_Ioo)).comp
            ((continuous_const.prodMk continuous_id).continuousAt)
        have hd_z := (hasDerivAt_const (0 : ℝ) dStar).add (hasDerivAt_mul_zero hRc)
        exact (hd_z.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun z => by dsimp; rw [← hfn z])
      have hO : IsOpen (S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6) := S_rs.hΩ.prod isOpen_Ioo
      have hf := ((S_rs.out.2.2.2.2.2.2.1.1.add (contDiffOn_const (c := dStar))).contDiffAt
        (hO.mem_nhds h000_Ioo)).differentiableAt (by norm_num) |>.hasFDerivAt
      have h2 : HasDerivAt (fun z : ℝ => (((0 : ℝ), (0 : ℝ)), z)) ((0 : ℝ × ℝ), (1 : ℝ)) 0 :=
        (hasDerivAt_const (0 : ℝ) ((0 : ℝ), (0 : ℝ))).prodMk (hasDerivAt_id (0 : ℝ))
      have hdf_eq : fderiv ℝ (fun q => Dfun S_rs.B S_rs.d S_rs.R q - dStar + dStar) ((0, 0), 0) =
          fderiv ℝ S_rs.D ((0, 0), 0) := by congr 1; ext q; simp [ChartSetup.D]
      rw [hdf_eq] at hf
      exact (hf.comp_hasDerivAt 0 h2).unique (h1.congr_of_eventuallyEq (Eventually.of_forall fun z => by simp [ChartSetup.D]))
    have hZ00 : S_rs.Z ((0, 0), 0) = 0 := by
      have h := S_rs.V_eq h000_Yint
      simpa using h.symm
    have hZ_deriv : HasDerivAt (fun w : ℝ => S_rs.Z ((0, 0), w)) (dStar ^ 2)⁻¹ 0 := by
      have hO : IsOpen (S_rs.Ω ×ˢ Yint) := S_rs.hΩ.prod isOpen_Ioo
      have hZdiff : DifferentiableAt ℝ (fun w => S_rs.Z ((0, 0), w)) 0 :=
        (S_rs.Z_diff.differentiableAt (hO.mem_nhds h000_Yint)).comp (0 : ℝ)
          ((differentiableAt_const _).prodMk differentiableAt_id)
      have hDZ : HasDerivAt (fun w => S_rs.D ((0, 0), S_rs.Z ((0, 0), w)))
          (fderiv ℝ S_rs.D ((0, 0), 0) (0, 1) * deriv (fun w => S_rs.Z ((0, 0), w)) 0) 0 := by
        have hOd : IsOpen (S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6) := S_rs.hΩ.prod isOpen_Ioo
        have hf := ((S_rs.out.2.2.2.2.2.2.1.1.add (contDiffOn_const (c := dStar))).contDiffAt
          (hOd.mem_nhds h000_Ioo)).differentiableAt (by norm_num) |>.hasFDerivAt
        have hcurve : HasDerivAt (fun w => (((0 : ℝ), (0 : ℝ)), S_rs.Z ((0, 0), w)))
            ((0 : ℝ × ℝ), deriv (fun w => S_rs.Z ((0, 0), w)) 0) 0 :=
          (hasDerivAt_const (0 : ℝ) ((0 : ℝ), (0 : ℝ))).prodMk hZdiff.hasDerivAt
        have hc := hf.comp_hasDerivAt_of_eq 0 hcurve (by simp [hZ00])
        rw [hZ00] at hc
        convert hc using 1
        simp only [ChartSetup.D]
        have heq : fderiv ℝ (fun q => S_rs.D q - dStar + dStar) ((0, 0), 0) = fderiv ℝ S_rs.D ((0, 0), 0) := by
          congr 1; ext q; ring
        rw [heq]
        have hsm : ((0 : ℝ × ℝ), deriv (fun w => S_rs.Z ((0, 0), w)) 0) =
            deriv (fun w => S_rs.Z ((0, 0), w)) 0 • ((0 : ℝ × ℝ), (1 : ℝ)) := by simp
        rw [hsm, map_smul, smul_eq_mul, mul_comm]
      have hprod := (hZdiff.hasDerivAt.mul (hDZ.pow 2)).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
      have heq_id : ∀ᶠ w in 𝓝 (0 : ℝ), S_rs.Z ((0, 0), w) * S_rs.D ((0, 0), S_rs.Z ((0, 0), w)) ^ 2 = w := by
        filter_upwards [Ioo_mem_nhds (by norm_num : -(1 / 5 : ℝ) < 0) (by norm_num : (0 : ℝ) < 36 / 10)] with w hw
        exact S_rs.Z_D (show ((0, 0), w) ∈ S_rs.Ω ×ˢ Yint from ⟨hp00, hw⟩)
      have h1 := (hasDerivAt_id (0 : ℝ)).congr_of_eventuallyEq (heq_id.mono fun w hw => hw)
      have hval := h1.unique hprod
      rw [hZ00, hD00, zero_mul, add_zero] at hval
      have hd2_ne : dStar ^ 2 ≠ 0 := by unfold dStar; positivity
      have hder_val : deriv (fun w => S_rs.Z ((0, 0), w)) 0 = (dStar ^ 2)⁻¹ :=
        eq_inv_of_mul_eq_one_left (by linarith)
      exact hder_val ▸ hZdiff.hasDerivAt
    have hV00 : S_rs.V ((0, 0), 0) = τs := by
      simp only [ChartSetup.V, hZ00, hD00]; exact tauStar_eq_dStar_inv.symm
    have hV_deriv : HasDerivAt (fun w : ℝ => S_rs.V ((0, 0), w)) (r_star ^ 2 * (7 / 50)) 0 := by
      have hOd : IsOpen (S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6) := S_rs.hΩ.prod isOpen_Ioo
      have hf := ((S_rs.out.2.2.2.2.2.2.1.1.add (contDiffOn_const (c := dStar))).contDiffAt
        (hOd.mem_nhds h000_Ioo)).differentiableAt (by norm_num) |>.hasFDerivAt
      have hcurve : HasDerivAt (fun w => (((0 : ℝ), (0 : ℝ)), S_rs.Z ((0, 0), w))) ((0 : ℝ × ℝ), (dStar ^ 2)⁻¹) 0 :=
        (hasDerivAt_const (0 : ℝ) ((0 : ℝ), (0 : ℝ))).prodMk hZ_deriv
      have hDZ : HasDerivAt (fun w => S_rs.D ((0, 0), S_rs.Z ((0, 0), w)))
          (S_rs.R ((0, 0), 0) * (dStar ^ 2)⁻¹) 0 := by
        have hc := hf.comp_hasDerivAt_of_eq 0 hcurve (by simp [hZ00])
        rw [hZ00] at hc
        have heq : fderiv ℝ (fun q => S_rs.D q - dStar + dStar) ((0, 0), 0) = fderiv ℝ S_rs.D ((0, 0), 0) := by
          congr 1; ext q; ring
        rw [heq] at hc
        have hsm : ((0 : ℝ × ℝ), (dStar ^ 2)⁻¹) = (dStar ^ 2)⁻¹ • ((0 : ℝ × ℝ), (1 : ℝ)) := by simp
        rw [hsm, map_smul, smul_eq_mul, hDz00, mul_comm] at hc
        exact hc
      have hD_ne : S_rs.D ((0, 0), S_rs.Z ((0, 0), 0)) ≠ 0 := by
        rw [hZ00, hD00]; unfold dStar; positivity
      have hinv := hDZ.inv hD_ne
      refine hinv.congr_deriv ?_
      rw [hZ00, hD00, hR00, concreteMt_zero]
      have hd6 : dStar ^ 6 = π ^ 4 / 144 := by
        have hd3 : dStar ^ 3 = π ^ 2 / 12 := by
          unfold dStar; rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        calc dStar ^ 6 = (dStar ^ 3) ^ 2 := by ring
          _ = (π ^ 2 / 12) ^ 2 := by rw [hd3]
          _ = π ^ 4 / 144 := by ring
      have hd_ne : dStar ≠ 0 := by unfold dStar; positivity
      have hpi_ne : π ≠ 0 := Real.pi_ne_zero
      calc -(-(r_star ^ 2 * (7 * π ^ 4 / 7200)) / dStar ^ 2 * (dStar ^ 2)⁻¹) / dStar ^ 2
          = r_star ^ 2 * (7 * π ^ 4 / 7200) / dStar ^ 6 := by field_simp [hd_ne]
        _ = r_star ^ 2 * (7 * π ^ 4 / 7200) / (π ^ 4 / 144) := by rw [hd6]
        _ = r_star ^ 2 * (7 / 50) := by field_simp [hpi_ne]; ring
    -- Differentiate the 3 factors of `Jfun S_rs.V fctH (r_star^2) ((0, 0), w)` at `w = 0`
    have hVcont : ContinuousAt (fun w => fderiv ℝ S_rs.V ((0, 0), w) (0, 1) * (S_rs.V ((0, 0), w))⁻¹) 0 := by
      have hO : IsOpen (S_rs.Ω ×ˢ Yint) := S_rs.hΩ.prod isOpen_Ioo
      have hVcont_w : ContinuousAt (fun w => S_rs.V ((0, 0), w)) 0 :=
        ((S_rs.V_jc hβrs4).1.continuousOn.continuousAt (hO.mem_nhds h000_Yint)).comp
          ((continuous_const.prodMk continuous_id).continuousAt)
      have hVd_cont : ContinuousAt (fun w => fderiv ℝ S_rs.V ((0, 0), w) (0, 1)) 0 := by
        have h15 := (S_rs.V_jc hβrs4).succ_fderiv hO |>.clm_apply_const hO.uniqueDiffOn ((0 : ℝ × ℝ), (1 : ℝ))
        exact (h15.1.continuousOn.continuousAt (hO.mem_nhds h000_Yint)).comp
          ((continuous_const.prodMk continuous_id).continuousAt)
      have hV0_ne : S_rs.V ((0, 0), 0) ≠ 0 := by rw [hV00]; positivity
      exact hVd_cont.mul (hVcont_w.inv₀ hV0_ne)
    have hf1 : HasDerivAt (fun w => 1 + 2 * (w * fderiv ℝ S_rs.V ((0, 0), w) (0, 1)) * (S_rs.V ((0, 0), w))⁻¹)
        (2 * (r_star ^ 2 * (7 / 50) / τs)) 0 := by
      have hVd0 : fderiv ℝ S_rs.V ((0, 0), 0) (0, 1) = r_star ^ 2 * (7 / 50) := by
        have hO : IsOpen (S_rs.Ω ×ˢ Yint) := S_rs.hΩ.prod isOpen_Ioo
        have hf := ((S_rs.V_jc hβrs4).1.contDiffAt (hO.mem_nhds h000_Yint)).differentiableAt
          (by norm_num) |>.hasFDerivAt
        have h2 : HasDerivAt (fun w => (((0 : ℝ), (0 : ℝ)), w)) ((0 : ℝ × ℝ), (1 : ℝ)) 0 :=
          (hasDerivAt_const (0 : ℝ) ((0 : ℝ), (0 : ℝ))).prodMk (hasDerivAt_id (0 : ℝ))
        exact (hf.comp_hasDerivAt 0 h2).unique hV_deriv
      have hd := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add ((hasDerivAt_mul_zero hVcont).const_mul 2)
      refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun w => by dsimp; ring)
      rw [hVd0, hV00]; ring
    have hf2 : HasDerivAt (fun w => (S_rs.V ((0, 0), w) * (S_rs.V ((0, 0), 0))⁻¹) ^ (1 / 2 : ℝ))
        ((1 / 2 : ℝ) * (r_star ^ 2 * (7 / 50) / τs)) 0 := by
      have hV_pos0 : 0 < S_rs.V ((0, 0), 0) := by rw [hV00]; positivity
      have hratio : HasDerivAt (fun w => S_rs.V ((0, 0), w) * (S_rs.V ((0, 0), 0))⁻¹)
          (r_star ^ 2 * (7 / 50) * (S_rs.V ((0, 0), 0))⁻¹) 0 :=
        hV_deriv.mul_const _
      have hr1 : S_rs.V ((0, 0), 0) * (S_rs.V ((0, 0), 0))⁻¹ = 1 := mul_inv_cancel₀ hV_pos0.ne'
      have hpow := hratio.rpow_const (p := (1 / 2 : ℝ)) (Or.inl (by rw [hr1]; norm_num))
      refine hpow.congr_deriv ?_
      rw [hr1, hV00, Real.one_rpow]; ring
    have hf3 : HasDerivAt (fun w => fctH (r_star ^ 2 * (w * S_rs.V ((0, 0), w) ^ 2)))
        (-(7 * π ^ 2 / 240) * (r_star ^ 2 * τs ^ 2)) 0 := by
      have hO : IsOpen (S_rs.Ω ×ˢ Yint) := S_rs.hΩ.prod isOpen_Ioo
      have hVcont_w : ContinuousAt (fun w => r_star ^ 2 * S_rs.V ((0, 0), w) ^ 2) 0 :=
        continuousAt_const.mul
          (((S_rs.V_jc hβrs4).1.continuousOn.continuousAt (hO.mem_nhds h000_Yint)).comp
            ((continuous_const.prodMk continuous_id).continuousAt) |>.pow 2)
      have harg : HasDerivAt (fun w => w * (r_star ^ 2 * S_rs.V ((0, 0), w) ^ 2)) (r_star ^ 2 * τs ^ 2) 0 := by
        have := hasDerivAt_mul_zero hVcont_w
        rw [hV00] at this; exact this
      have h0_eq : (0 : ℝ) = 0 * (r_star ^ 2 * S_rs.V ((0, 0), 0) ^ 2) := by ring
      have hc := ((hasDerivAt_fctH_zero.comp_of_eq 0 harg h0_eq).congr_deriv (by ring)).congr_of_eventuallyEq
        (Eventually.of_forall fun w => by dsimp; ring)
      exact hc
    have htot := (hf1.mul hf2).mul hf3
    have hf1_0 : 1 + 2 * ((0 : ℝ) * fderiv ℝ S_rs.V ((0, 0), 0) (0, 1)) * (S_rs.V ((0, 0), 0))⁻¹ = 1 := by ring
    have hf2_0 : (S_rs.V ((0, 0), 0) * (S_rs.V ((0, 0), 0))⁻¹) ^ (1 / 2 : ℝ) = 1 := by
      have hne : S_rs.V ((0, 0), 0) ≠ 0 := by rw [hV00]; positivity
      rw [mul_inv_cancel₀ hne, Real.one_rpow]
    have hf3_0 : fctH (r_star ^ 2 * ((0 : ℝ) * S_rs.V ((0, 0), 0) ^ 2)) = 1 := by
      rw [zero_mul, mul_zero, fctH_zero]
    have hJ_der : HasDerivAt (fun w : ℝ => Jfun S_rs.V fctH (r_star ^ 2) ((0, 0), w))
        ((2 * (r_star ^ 2 * (7 / 50) / τs) *
            (S_rs.V ((0, 0), 0) * (S_rs.V ((0, 0), 0))⁻¹) ^ (1 / 2 : ℝ) +
          (1 + 2 * (0 * fderiv ℝ S_rs.V ((0, 0), 0) (0, 1)) * (S_rs.V ((0, 0), 0))⁻¹) *
            ((1 / 2 : ℝ) * (r_star ^ 2 * (7 / 50) / τs))) *
          fctH (r_star ^ 2 * (0 * S_rs.V ((0, 0), 0) ^ 2)) +
          (1 + 2 * (0 * fderiv ℝ S_rs.V ((0, 0), 0) (0, 1)) * (S_rs.V ((0, 0), 0))⁻¹) *
            (S_rs.V ((0, 0), 0) * (S_rs.V ((0, 0), 0))⁻¹) ^ (1 / 2 : ℝ) *
            (-(7 * π ^ 2 / 240) * (r_star ^ 2 * τs ^ 2))) 0 :=
      htot.congr_of_eventuallyEq (Eventually.of_forall fun w => by simp [Jfun])
    rw [hJ_der.deriv, hf1_0, hf2_0, hf3_0]
    have hτs3 : τs ^ 3 = 12 / π ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    have hτs_ne : τs ≠ 0 := by positivity
    have hpi_ne : π ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
    calc ((2 * (r_star ^ 2 * (7 / 50) / τs) * 1 + 1 * ((1 / 2 : ℝ) * (r_star ^ 2 * (7 / 50) / τs))) * 1 +
            1 * 1 * (-(7 * π ^ 2 / 240) * (r_star ^ 2 * τs ^ 2)))
        = r_star ^ 2 * τs ^ 2 * (7 / 20 / τs ^ 3 - 7 * π ^ 2 / 240) := by field_simp [hτs_ne]; ring
      _ = r_star ^ 2 * τs ^ 2 * (7 / 20 / (12 / π ^ 2) - 7 * π ^ 2 / 240) := by rw [hτs3]
      _ = 0 := by
          have : 7 / 20 / (12 / π ^ 2) - 7 * π ^ 2 / 240 = 0 := by field_simp [hpi_ne]; ring
          rw [this, mul_zero]
  exact ⟨S_rs, rfl, rfl, rfl, h15ε, hJ_jc.2.2.2, hJ0_val, hderiv0⟩

/-! ### 2. Rescaling uniqueness `S.V(q₀, Y) = S_rs.V(p_rs, λ Y)` -/

/-- Uniqueness of `(B, d, R, D, Z, V)` under `(ℓ, z) ↦ (λ ℓ, λ z)` for `λ = τ₁^2 / r_star^2`. -/
lemma Jfun_scale_eq {r_star : ℝ} (hr_pos : 0 < r_star)
    {θt : ℝ → ℝ} {S_rs : ChartSetup (ℝ × ℝ)}
    (hSrs_Ω : S_rs.Ω = fctOmegaRs) (hSrs_ℓ : S_rs.ℓ = Prod.fst)
    (hSrs_r : S_rs.r = fctRrs r_star θt) (h15rs : 15 * S_rs.ε ≤ 1 / 2)
    {K4 c τ₁ : ℝ} (hτ₁_pos : 0 < τ₁)
    {T : CfuTheta} {S : ChartSetup (ℝ × ℝ × ℝ)}
    (hTmt : T.mt = concreteMt) (hTθt : T.θt = θt)
    (hSΩ : S.Ω = OmT τ₁) (hSℓ : S.ℓ = fun p => p.1) (hSr : S.r = T.r τ₁ K4)
    {ell1 α : ℝ} (hq0 : (ell1, 0, α) ∈ S.Ω)
    (hlam_pos : 0 < τ₁ ^ 2 / r_star ^ 2) (hlam_16 : τ₁ ^ 2 / r_star ^ 2 ≤ 1 / 6)
    (hprs : (τ₁ ^ 2 / r_star ^ 2 * ell1, τ₁ ^ 4 / r_star ^ 2) ∈ fctOmegaRs)
    (hR_small : ∀ z ∈ Ioo (-1 : ℝ) 6, |(τ₁ ^ 2 / r_star ^ 2)⁻¹ * S.R ((ell1, 0, α), z)| < 1 / 50) :
    ∀ Y ∈ Icc (0 : ℝ) 3.5,
      Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), Y) =
        Jfun S_rs.V fctH (r_star ^ 2) ((τ₁ ^ 2 / r_star ^ 2 * ell1, τ₁ ^ 4 / r_star ^ 2),
          (τ₁ ^ 2 / r_star ^ 2) * Y) := by
  let lam : ℝ := τ₁ ^ 2 / r_star ^ 2
  let q0 : ℝ × ℝ × ℝ := (ell1, 0, α)
  let p_rs : ℝ × ℝ := (lam * ell1, τ₁ ^ 4 / r_star ^ 2)
  have hp_rs : p_rs ∈ S_rs.Ω := hSrs_Ω ▸ hprs
  have hz_map : ∀ z ∈ Ioo (-1 : ℝ) 6, lam * z ∈ Ioo (-1 : ℝ) 6 := fun z hz =>
    ⟨by nlinarith only [hlam_pos, hlam_16, hz.1], by nlinarith only [hlam_pos, hlam_16, hz.2]⟩
  have hr_scale : ∀ z : ℝ, S_rs.r (p_rs, lam * z) = lam * S.r (q0, z) := fun z => by
    simp only [hSrs_r, hSr, fctRrs, CfuTheta.r, hTmt, hTθt, q0, p_rs, lam]
    field_simp [hr_pos.ne']
    ring
  have hrz_scale : ∀ z ∈ Ioo (-1 : ℝ) 6,
      fderiv ℝ S_rs.r (p_rs, lam * z) (0, 1) = fderiv ℝ S.r (q0, z) (0, 1) := by
    intro z hz
    have hO : IsOpen (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hΩ.prod isOpen_Ioo
    have hOrs : IsOpen (S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6) := S_rs.hΩ.prod isOpen_Ioo
    have hqz : (q0, z) ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hq0, hz⟩
    have hf1 := ((S.hr.1.contDiffAt (hO.mem_nhds hqz)).differentiableAt (by norm_num)).hasFDerivAt
    have hd1 : HasDerivAt (fun w => S.r (q0, w)) (fderiv ℝ S.r (q0, z) (0, 1)) z :=
      hf1.comp_hasDerivAt z (by simpa using (hasDerivAt_const z q0).prodMk (hasDerivAt_id z))
    have hprsz : (p_rs, lam * z) ∈ S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hp_rs, hz_map z hz⟩
    have hf2 := ((S_rs.hr.1.contDiffAt (hOrs.mem_nhds hprsz)).differentiableAt (by norm_num)).hasFDerivAt
    have h2 : HasDerivAt (fun w => (p_rs, lam * w)) ((0 : ℝ × ℝ), lam) z :=
      (hasDerivAt_const z p_rs).prodMk (((hasDerivAt_id z).const_mul lam).congr_deriv (mul_one _))
    have hd2 : HasDerivAt (fun w => S_rs.r (p_rs, lam * w))
        (lam * fderiv ℝ S_rs.r (p_rs, lam * z) (0, 1)) z := by
      have hc := hf2.comp_hasDerivAt z h2
      have hsm : ((0 : ℝ × ℝ), lam) = lam • ((0 : ℝ × ℝ), (1 : ℝ)) := by simp
      rw [hsm, map_smul, smul_eq_mul] at hc
      exact hc
    have h_eq : (fun w => S_rs.r (p_rs, lam * w)) = fun w => lam * S.r (q0, w) := funext hr_scale
    have hval := hd2.unique ((hd1.const_mul lam).congr_of_eventuallyEq (Eventually.of_forall fun w => hr_scale w))
    exact mul_left_cancel₀ hlam_pos.ne' hval
  -- 1. `S_rs.B p_rs = lam * S.B q0`
  have hB_scale : S_rs.B p_rs = lam * S.B q0 := by
    obtain ⟨hB0_mem, hB0_eq⟩ := S.out.2.1 q0 hq0
    obtain ⟨hBrs_mem, hBrs_eq⟩ := S_rs.out.2.1 p_rs hp_rs
    let f : ℝ → ℝ := fun b => π ^ 2 / 12 * b - p_rs.1 - rhoF S_rs.r (p_rs, b)
    have hf_rs : f (S_rs.B p_rs) = 0 := by dsimp only [f]; rw [← hSrs_ℓ]; exact hBrs_eq
    have hf_0 : f (lam * S.B q0) = 0 := by
      dsimp only [f, rhoF]
      rw [hr_scale (S.B q0), hrz_scale (S.B q0) hB0_mem]
      rw [hSℓ] at hB0_eq
      dsimp only [p_rs, q0] at hB0_eq ⊢
      have heq : π ^ 2 / 12 * (lam * S.B q0) - lam * ell1 - (lam * S.r (q0, S.B q0) + 2 * (lam * S.B q0 * fderiv ℝ S.r (q0, S.B q0) (0, 1))) =
          lam * (π ^ 2 / 12 * S.B q0 - ell1 - rhoF S.r (q0, S.B q0)) := by
        dsimp only [rhoF, q0]; ring
      rw [heq, hB0_eq, mul_zero]
    -- Strictly positive derivative of `f` on `Ioo (-1) 6`
    have hOrs : IsOpen (S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6) := S_rs.hΩ.prod isOpen_Ioo
    have hp_emb : ContDiffOn ℝ 18 (fun w : ℝ => (p_rs, w)) (Ioo (-1 : ℝ) 6) := by fun_prop
    have h17 := (S_rs.hr.succ_fderiv hOrs).clm_apply_const hOrs.uniqueDiffOn ((0 : ℝ × ℝ), (1 : ℝ))
    have hrho_cd : ContDiffOn ℝ 1 (fun w => rhoF S_rs.r (p_rs, w)) (Ioo (-1 : ℝ) 6) := by
      have hr_w := S_rs.hr.1.comp hp_emb fun w hw => ⟨hp_rs, hw⟩
      have hfd_w := h17.1.comp (hp_emb.of_le (by norm_num : (17 : WithTop ℕ∞) ≤ 18)) fun w hw => ⟨hp_rs, hw⟩
      refine ((hr_w.of_le (by norm_num)).add (contDiffOn_const.mul (contDiffOn_id.mul (hfd_w.of_le (by norm_num))))).congr
        fun _ _ => rfl
    have hf_mono : StrictMonoOn f (Ioo (-1 : ℝ) 6) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioo (-1 : ℝ) 6)
      · exact ((continuousOn_const.mul continuousOn_id).sub continuousOn_const).sub hrho_cd.continuousOn
      · intro w hw
        rw [interior_Ioo] at hw
        have hq : (p_rs, w) ∈ S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hp_rs, hw⟩
        have hdr : HasDerivAt (fun t => S_rs.r (p_rs, t)) (fderiv ℝ S_rs.r (p_rs, w) (0, 1)) w :=
          (((S_rs.hr.1.contDiffAt (hOrs.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt
            w (by simpa using (hasDerivAt_const w p_rs).prodMk (hasDerivAt_id w))
        have hd2 : HasDerivAt (fun t => fderiv ℝ S_rs.r (p_rs, t) (0, 1))
            (fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p_rs, w) (0, 1)) w :=
          (((h17.1.contDiffAt (hOrs.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt
            w (by simpa using (hasDerivAt_const w p_rs).prodMk (hasDerivAt_id w))
        have htot : HasDerivAt f
            (π ^ 2 / 12 - (fderiv ℝ S_rs.r (p_rs, w) (0, 1) +
              2 * (1 * fderiv ℝ S_rs.r (p_rs, w) (0, 1) +
                w * fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p_rs, w) (0, 1)))) w := by
          have hd0 := (((hasDerivAt_id w).const_mul (π ^ 2 / 12)).sub_const p_rs.1).sub
            (hdr.add (((hasDerivAt_id w).mul hd2).const_mul 2))
          refine (hd0.congr_deriv (by dsimp; ring)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
          dsimp only [f, rhoF]; rfl
        rw [htot.deriv]
        have hb1 : |fderiv ℝ S_rs.r (p_rs, w) (0, 1)| ≤ S_rs.ε := by
          have hbd := S_rs.hr.2 1 (by norm_num) (p_rs, w) hq
          rw [norm_iteratedFDerivWithin_one _ (hOrs.uniqueDiffOn _ hq), fderivWithin_of_isOpen hOrs hq] at hbd
          calc |fderiv ℝ S_rs.r (p_rs, w) (0, 1)| = ‖fderiv ℝ S_rs.r (p_rs, w) (0, 1)‖ := Real.norm_eq_abs _
            _ ≤ ‖fderiv ℝ S_rs.r (p_rs, w)‖ * ‖((0 : ℝ × ℝ), (1 : ℝ))‖ := (fderiv ℝ _ _).le_opNorm _
            _ ≤ S_rs.ε * 1 := mul_le_mul hbd (by simp [Prod.norm_def]) (norm_nonneg _) S_rs.hε
            _ = S_rs.ε := mul_one _
        have hb2 : |fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p_rs, w) (0, 1)| ≤ S_rs.ε := by
          have hbd := h17.2 1 (by norm_num) (p_rs, w) hq
          rw [norm_iteratedFDerivWithin_one _ (hOrs.uniqueDiffOn _ hq), fderivWithin_of_isOpen hOrs hq] at hbd
          have hn1 : ‖((0 : ℝ × ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
          rw [hn1, one_mul] at hbd
          calc |fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p_rs, w) (0, 1)|
              = ‖fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p_rs, w) (0, 1)‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p_rs, w)‖ * ‖((0 : ℝ × ℝ), (1 : ℝ))‖ :=
                (fderiv ℝ _ _).le_opNorm _
            _ ≤ S_rs.ε * 1 := mul_le_mul hbd (le_of_eq hn1) (norm_nonneg _) S_rs.hε
            _ = S_rs.ε := mul_one _
        have hw6 : |w| ≤ 6 := by rw [abs_le]; constructor <;> linarith only [hw.1, hw.2]
        have hrho_le : |fderiv ℝ S_rs.r (p_rs, w) (0, 1) + 2 * (1 * fderiv ℝ S_rs.r (p_rs, w) (0, 1) +
              w * fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p_rs, w) (0, 1))| ≤ 1 / 2 := by
          calc |fderiv ℝ S_rs.r (p_rs, w) (0, 1) + 2 * (1 * fderiv ℝ S_rs.r (p_rs, w) (0, 1) +
                  w * fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p_rs, w) (0, 1))|
              = |3 * fderiv ℝ S_rs.r (p_rs, w) (0, 1) +
                  2 * w * fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p_rs, w) (0, 1)| := by congr 1; ring
            _ ≤ |3 * fderiv ℝ S_rs.r (p_rs, w) (0, 1)| +
                  |2 * w * fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p_rs, w) (0, 1)| := abs_add_le _ _
            _ = 3 * |fderiv ℝ S_rs.r (p_rs, w) (0, 1)| + 2 * |w| *
                  |fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p_rs, w) (0, 1)| := by
                rw [abs_mul, abs_mul, abs_mul, show |(3 : ℝ)| = 3 by norm_num, show |(2 : ℝ)| = 2 by norm_num]
            _ ≤ 3 * S_rs.ε + 2 * 6 * S_rs.ε := by gcongr
            _ = 15 * S_rs.ε := by ring
            _ ≤ 1 / 2 := h15rs
        have hpi2 : (9.8 : ℝ) < π ^ 2 := by nlinarith only [Real.pi_gt_d2]
        linarith only [(abs_le.mp hrho_le).2, hpi2]
    exact hf_mono.injOn hBrs_mem (hz_map (S.B q0) hB0_mem) (hf_rs.trans hf_0.symm)
  -- 2. `S_rs.d p_rs = S.d q0`
  have hd_scale : S_rs.d p_rs = S.d q0 := by
    obtain ⟨hd0_pos, hd0_cube⟩ := S.out.2.2.2.1 q0 hq0
    obtain ⟨hdrs_pos, hdrs_cube⟩ := S_rs.out.2.2.2.1 p_rs hp_rs
    have hB0_mem := (S.out.2.1 q0 hq0).1
    rw [hB_scale, hrz_scale (S.B q0) hB0_mem] at hdrs_cube
    exact pow_left_inj₀ hdrs_pos.le hd0_pos.le (by norm_num : 3 ≠ 0) |>.mp (hdrs_cube.trans hd0_cube.symm)
  -- 3. `S_rs.R (p_rs, lam * z) = lam⁻¹ * S.R (q0, z)` and `S_rs.D (p_rs, lam * z) = S.D (q0, z)`
  have hrzz_scale : ∀ z ∈ Ioo (-1 : ℝ) 6,
      fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p_rs, lam * z) (0, 1) =
        lam⁻¹ * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (q0, z) (0, 1) := by
    intro z hz
    have hO : IsOpen (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hΩ.prod isOpen_Ioo
    have hOrs : IsOpen (S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6) := S_rs.hΩ.prod isOpen_Ioo
    have h17 := (S.hr.succ_fderiv hO).clm_apply_const hO.uniqueDiffOn ((0 : ℝ × ℝ × ℝ), (1 : ℝ))
    have h17rs := (S_rs.hr.succ_fderiv hOrs).clm_apply_const hOrs.uniqueDiffOn ((0 : ℝ × ℝ), (1 : ℝ))
    have hqz : (q0, z) ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hq0, hz⟩
    have hd1 : HasDerivAt (fun w => fderiv ℝ S.r (q0, w) (0, 1))
        (fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (q0, z) (0, 1)) z :=
      (((h17.1.contDiffAt (hO.mem_nhds hqz)).differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt
        z ((hasDerivAt_const z q0).prodMk (hasDerivAt_id z))
    have hd2 : HasDerivAt (fun w => fderiv ℝ S_rs.r (p_rs, lam * w) (0, 1))
        (lam * fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p_rs, lam * z) (0, 1)) z := by
      have hprsz : (p_rs, lam * z) ∈ S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hp_rs, hz_map z hz⟩
      have hf2 := ((h17rs.1.contDiffAt (hOrs.mem_nhds hprsz)).differentiableAt (by norm_num)).hasFDerivAt
      have h2 : HasDerivAt (fun w => (p_rs, lam * w)) ((0 : ℝ × ℝ), lam) z :=
        (hasDerivAt_const z p_rs).prodMk (((hasDerivAt_id z).const_mul lam).congr_deriv (mul_one _))
      have hc := hf2.comp_hasDerivAt z h2
      have hsm : ((0 : ℝ × ℝ), lam) = lam • ((0 : ℝ × ℝ), (1 : ℝ)) := by simp
      rw [hsm, map_smul, smul_eq_mul] at hc
      exact hc
    have hev : (fun w => fderiv ℝ S_rs.r (p_rs, lam * w) (0, 1)) =ᶠ[𝓝 z]
        fun w => fderiv ℝ S.r (q0, w) (0, 1) := by
      filter_upwards [isOpen_Ioo.mem_nhds hz] with w hw
      exact hrz_scale w hw
    have hval := hd2.unique (hd1.congr_of_eventuallyEq hev)
    exact ((inv_mul_eq_iff_eq_mul₀ hlam_pos.ne').mpr hval.symm).symm
  have hhad_scale : ∀ z ∈ Ioo (-1 : ℝ) 6,
      hadH S_rs.r S_rs.B (p_rs, lam * z) = lam⁻¹ * hadH S.r S.B (q0, z) := by
    intro z hz
    have hB0_mem := (S.out.2.1 q0 hq0).1
    have hconv : Convex ℝ (Ioo (-1 : ℝ) 6) := convex_Ioo (-1) 6
    have heq : ∀ σ ∈ Icc (0 : ℝ) 1,
        (1 - σ) * fderiv ℝ (fun x => fderiv ℝ S_rs.r x (0, 1)) (p_rs, S_rs.B p_rs + σ * (lam * z - S_rs.B p_rs)) (0, 1) =
          lam⁻¹ * ((1 - σ) * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (q0, S.B q0 + σ * (z - S.B q0)) (0, 1)) := by
      intro σ hσ
      have hmid : S.B q0 + σ * (z - S.B q0) ∈ Ioo (-1 : ℝ) 6 :=
        hconv.add_smul_sub_mem hB0_mem hz hσ
      rw [hB_scale, show lam * S.B q0 + σ * (lam * z - lam * S.B q0) = lam * (S.B q0 + σ * (z - S.B q0)) by ring,
        hrzz_scale _ hmid]
      ring
    unfold hadH
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc heq, MeasureTheory.integral_const_mul]
  have hR_scale : ∀ z ∈ Ioo (-1 : ℝ) 6, S_rs.R (p_rs, lam * z) = lam⁻¹ * S.R (q0, z) := by
    intro z hz
    have hzd := hz_map z hz
    have hBrs_mem := (S_rs.out.2.1 p_rs hp_rs).1
    have h1 := (S_rs.out.2.2.2.2.2.1 (p_rs, lam * z) ⟨hp_rs, hzd⟩)
    have h0 := (S.out.2.2.2.2.2.1 (q0, z) ⟨hq0, hz⟩)
    let H0 := hadH S_rs.r S_rs.B (p_rs, lam * z)
    let d0 := S_rs.d p_rs
    let z0 := lam * z
    let B0 := S_rs.B p_rs
    let G : ℝ → ℝ := fun t => H0 + t * (d0 ^ 2 + d0 * z0 * t + 1 / 3 * z0 * (z0 - B0) * t ^ 2)
    have hG1 : G (S_rs.R (p_rs, lam * z)) = 0 := h1.2
    have hG2 : G (lam⁻¹ * S.R (q0, z)) = 0 := by
      dsimp only [G, H0, d0, z0, B0]
      rw [hhad_scale z hz, hd_scale, hB_scale]
      have halg : lam⁻¹ * hadH S.r S.B (q0, z) + lam⁻¹ * S.R (q0, z) *
          (S.d q0 ^ 2 + S.d q0 * (lam * z) * (lam⁻¹ * S.R (q0, z)) +
            1 / 3 * (lam * z) * (lam * z - lam * S.B q0) * (lam⁻¹ * S.R (q0, z)) ^ 2) =
          lam⁻¹ * (hadH S.r S.B (q0, z) + S.R (q0, z) *
            (S.d q0 ^ 2 + S.d q0 * z * S.R (q0, z) + 1 / 3 * z * (z - S.B q0) * S.R (q0, z) ^ 2)) := by
        dsimp only [lam]; field_simp [hτ₁_pos.ne', hr_pos.ne']
      rw [halg, h0.2, mul_zero]
    have hG_mono : StrictMonoOn G (Ioo (-(1 / 50 : ℝ)) (1 / 50)) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
      · exact Continuous.continuousOn (by fun_prop)
      · intro t ht
        rw [interior_Ioo] at ht
        have hd_dev : |d0 - dStar| ≤ 1 / 100 := S_rs.d_dev hp_rs
        have hz_6 : |z0| < 6 := by rw [abs_lt]; constructor <;> linarith only [hzd.1, hzd.2]
        have hzB : |z0 - B0| < 7 := by rw [abs_lt]; constructor <;> linarith only [hzd.1, hzd.2, hBrs_mem.1, hBrs_mem.2]
        have ht_50 : |t| < 1 / 50 := abs_lt.mpr ht
        have hpos := Rcoef_pos hd_dev hz_6 hzB ht_50
        have hder : HasDerivAt G (d0 ^ 2 + 2 * d0 * z0 * t + z0 * (z0 - B0) * t ^ 2) t := by
          have : G = fun s => H0 + d0 ^ 2 * s + d0 * z0 * s ^ 2 + 1 / 3 * z0 * (z0 - B0) * s ^ 3 := by
            ext s; dsimp only [G]; ring
          rw [this]
          have hd1 := ((hasDerivAt_const t H0).add ((hasDerivAt_id t).const_mul (d0 ^ 2))).add
            ((hasDerivAt_pow 2 t).const_mul (d0 * z0))
          have hd2 := hd1.add ((hasDerivAt_pow 3 t).const_mul (1 / 3 * z0 * (z0 - B0)))
          exact hd2.congr_deriv (by ring)
        rw [hder.deriv]; linarith only [hpos]
    exact hG_mono.injOn (abs_lt.mp h1.1) (abs_lt.mp (hR_small z hz)) (hG1.trans hG2.symm)
  have hD_scale : ∀ z ∈ Ioo (-1 : ℝ) 6, S_rs.D (p_rs, lam * z) = S.D (q0, z) := by
    intro z hz
    simp only [ChartSetup.D, Dfun, hB_scale, hd_scale, hR_scale z hz]
    dsimp only [lam]; field_simp [hτ₁_pos.ne', hr_pos.ne']
  -- 4. `S_rs.Z (p_rs, lam * Y) = lam * S.Z (q0, Y)` and `S_rs.V (p_rs, lam * Y) = S.V (q0, Y)` on `Y ∈ Yint`
  have hZ_scale : ∀ Y ∈ Yint, lam * Y ∈ Yint → S_rs.Z (p_rs, lam * Y) = lam * S.Z (q0, Y) := by
    intro Y hY hYlam
    have hZ0_mem : S.Z (q0, Y) ∈ Ioo (-1 : ℝ) 6 := S.Z_mem ⟨hq0, hY⟩
    have hZrs_mem : S_rs.Z (p_rs, lam * Y) ∈ Ioo (-1 : ℝ) 6 := S_rs.Z_mem ⟨hp_rs, hYlam⟩
    let g : ℝ → ℝ := fun z => z * S_rs.D (p_rs, z) ^ 2
    have hg_rs : g (S_rs.Z (p_rs, lam * Y)) = lam * Y := S_rs.Z_D ⟨hp_rs, hYlam⟩
    have hg_0 : g (lam * S.Z (q0, Y)) = lam * Y := by
      dsimp only [g]
      rw [hD_scale (S.Z (q0, Y)) hZ0_mem, mul_assoc, S.Z_D ⟨hq0, hY⟩]
    have hg_mono : StrictMonoOn g (Ioo (-1 : ℝ) 6) := by
      have hOrs : IsOpen (S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6) := S_rs.hΩ.prod isOpen_Ioo
      have hp_emb : ContDiffOn ℝ 1 (fun z : ℝ => (p_rs, z)) (Ioo (-1 : ℝ) 6) := by fun_prop
      have hD_cd : ContDiffOn ℝ 1 (fun z => S_rs.D (p_rs, z)) (Ioo (-1 : ℝ) 6) :=
        (((S_rs.out.2.2.2.2.2.2.1.1.add (contDiffOn_const (c := dStar))).of_le (by norm_num)).congr
          fun x _ => by simp [ChartSetup.D]).comp hp_emb fun z hz => ⟨hp_rs, hz⟩
      apply strictMonoOn_of_deriv_pos (convex_Ioo (-1 : ℝ) 6)
      · exact ContinuousOn.mul continuousOn_id (hD_cd.continuousOn.pow 2)
      · intro z hz
        rw [interior_Ioo] at hz
        have hq : (p_rs, z) ∈ S_rs.Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hp_rs, hz⟩
        have hDf := ((S_rs.out.2.2.2.2.2.2.1.1.add (contDiffOn_const (c := dStar))).contDiffAt
          (hOrs.mem_nhds hq)).differentiableAt (by norm_num) |>.hasFDerivAt
        have hDz : HasDerivAt (fun w => S_rs.D (p_rs, w)) (fderiv ℝ S_rs.D (p_rs, z) (0, 1)) z := by
          have hc := hDf.comp_hasDerivAt z (by simpa using (hasDerivAt_const z p_rs).prodMk (hasDerivAt_id z))
          have hdf_eq : fderiv ℝ (fun q => Dfun S_rs.B S_rs.d S_rs.R q - dStar + dStar) (p_rs, z) =
              fderiv ℝ S_rs.D (p_rs, z) := by
            congr 1; ext q; simp [ChartSetup.D]
          rw [hdf_eq] at hc
          exact hc.congr_of_eventuallyEq (Eventually.of_forall fun w => by simp [ChartSetup.D])
        have hprod : HasDerivAt g (1 * S_rs.D (p_rs, z) ^ 2 +
            z * (2 * S_rs.D (p_rs, z) * fderiv ℝ S_rs.D (p_rs, z) (0, 1))) z := by
          have hp0 := (hasDerivAt_id z).mul (hDz.pow 2)
          exact (hp0.congr_deriv (by simp)).congr_of_eventuallyEq
            (Eventually.of_forall fun w => by dsimp only [g]; simp)
        rw [hprod.deriv]
        have hyz := S_rs.Yz_pos hq
        linarith only [hyz]
    exact hg_mono.injOn hZrs_mem (hz_map (S.Z (q0, Y)) hZ0_mem) (hg_rs.trans hg_0.symm)
  have hV_scale : ∀ Y ∈ Yint, lam * Y ∈ Yint → S_rs.V (p_rs, lam * Y) = S.V (q0, Y) := by
    intro Y hY hYlam
    have hqY : (q0, Y) ∈ S.Ω ×ˢ Yint := ⟨hq0, hY⟩
    have hZ0_mem := S.Z_mem hqY
    simp only [ChartSetup.V, hZ_scale Y hY hYlam, hD_scale (S.Z (q0, Y)) hZ0_mem]
  -- 5. Put everything together on `Y ∈ Icc 0 3.5` (noting `Yint` is open and `lam * Y ∈ Yint`)
  intro Y hY
  have hY_int : Y ∈ Yint := ⟨by linarith [hY.1], by linarith [hY.2]⟩
  have hYlam_int : lam * Y ∈ Yint := by
    have h1 : lam * Y < 1 := by nlinarith only [hlam_pos, hlam_16, hY.1, hY.2]
    exact ⟨by nlinarith only [hlam_pos, hY.1], by linarith only [h1]⟩
  have hV_eq_Y : S.V (q0, Y) = S_rs.V (p_rs, lam * Y) := (hV_scale Y hY_int hYlam_int).symm
  have hV0_eq : S.V (q0, 0) = S_rs.V (p_rs, 0) := by
    have hz0 := (hV_scale 0 zero_mem_Yint (by simp [mul_zero]; exact zero_mem_Yint)).symm
    rw [mul_zero] at hz0; exact hz0
  have hVd_eq : fderiv ℝ S.V (q0, Y) (0, 1) = lam * fderiv ℝ S_rs.V (p_rs, lam * Y) (0, 1) := by
    have hO : IsOpen (S.Ω ×ˢ Yint) := S.hΩ.prod isOpen_Ioo
    have hOrs : IsOpen (S_rs.Ω ×ˢ Yint) := S_rs.hΩ.prod isOpen_Ioo
    have hqY : (q0, Y) ∈ S.Ω ×ˢ Yint := ⟨hq0, hY_int⟩
    have h1 := ((S.V_jc (by norm_num : (4 : ℝ) ≤ 4)).1.contDiffAt (hO.mem_nhds hqY)).differentiableAt
      (by norm_num) |>.hasFDerivAt
    have hd1 : HasDerivAt (fun y => S.V (q0, y)) (fderiv ℝ S.V (q0, Y) (0, 1)) Y :=
      h1.comp_hasDerivAt Y (by simpa using (hasDerivAt_const Y q0).prodMk (hasDerivAt_id Y))
    have hprsY : (p_rs, lam * Y) ∈ S_rs.Ω ×ˢ Yint := ⟨hp_rs, hYlam_int⟩
    have h2 := ((S_rs.V_jc (by norm_num : (4 : ℝ) ≤ 4)).1.contDiffAt (hOrs.mem_nhds hprsY)).differentiableAt
      (by norm_num) |>.hasFDerivAt
    have hcurve : HasDerivAt (fun y => (p_rs, lam * y)) ((0 : ℝ × ℝ), lam) Y :=
      (hasDerivAt_const Y p_rs).prodMk (((hasDerivAt_id Y).const_mul lam).congr_deriv (mul_one _))
    have hd2 : HasDerivAt (fun y => S_rs.V (p_rs, lam * y)) (lam * fderiv ℝ S_rs.V (p_rs, lam * Y) (0, 1)) Y := by
      have hc := h2.comp_hasDerivAt Y hcurve
      have hsm : ((0 : ℝ × ℝ), lam) = lam • ((0 : ℝ × ℝ), (1 : ℝ)) := by simp
      rw [hsm, map_smul, smul_eq_mul] at hc
      exact hc
    have hev : (fun y => S.V (q0, y)) =ᶠ[𝓝 Y] fun y => S_rs.V (p_rs, lam * y) := by
      filter_upwards [inter_mem (isOpen_Ioo.mem_nhds hY_int)
        ((continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hYlam_int))] with y hy
      exact (hV_scale y hy.1 hy.2).symm
    exact (hd2.congr_of_eventuallyEq hev).unique hd1 |>.symm
  simp only [Jfun]
  rw [hV_eq_Y, hV0_eq, hVd_eq]
  have h_tau : τ₁ ^ 2 * (Y * S_rs.V (p_rs, lam * Y) ^ 2) =
      r_star ^ 2 * (lam * Y * S_rs.V (p_rs, lam * Y) ^ 2) := by
    dsimp only [lam]; field_simp [hr_pos.ne']
  have h_prod : Y * (lam * fderiv ℝ S_rs.V (p_rs, lam * Y) (0, 1)) =
      lam * Y * fderiv ℝ S_rs.V (p_rs, lam * Y) (0, 1) := by ring
  rw [h_tau, h_prod]

/-! ### 3. `J₀(Y(u)) - 1 ∈ 𝒮^{10}(C c^{-4/3})` on `[0, U_c]` -/

/-- Hadamard / second-order integral representation on `Yint` around `0`. -/
private lemma hadamard_second_order {f : ℝ → ℝ} (hf : ContDiffOn ℝ 3 f Yint) (hf0 : f 0 = 0)
    {w : ℝ} (hw : w ∈ Yint) :
    f w - deriv f 0 * w =
      w ^ 2 * ∫ σ in Icc (0 : ℝ) 1, (1 - σ) * iteratedDeriv 2 f (σ * w) := by
  have hconv : Convex ℝ Yint := convex_Ioo _ _
  have h0_Y : (0 : ℝ) ∈ Yint := zero_mem_Yint
  have hmap : ∀ σ ∈ Set.uIcc (0 : ℝ) 1, σ * w ∈ Yint := fun σ hσ => by
    rw [uIcc_of_le zero_le_one] at hσ
    simpa [smul_eq_mul] using hconv.smul_mem_of_zero_mem h0_Y hw hσ
  let φ : ℝ → ℝ := fun σ => f (σ * w) + (1 - σ) * w * deriv f (σ * w)
  have hφ_deriv : ∀ σ ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt φ ((1 - σ) * w ^ 2 * iteratedDeriv 2 f (σ * w)) σ := by
    intro σ hσ
    have hmem : σ * w ∈ Yint := hmap σ hσ
    have hca : ContDiffAt ℝ 3 f (σ * w) := hf.contDiffAt (isOpen_Ioo.mem_nhds hmem)
    have hf1 : HasDerivAt f (deriv f (σ * w)) (σ * w) :=
      ((hca.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).differentiableAt (by norm_num)).hasDerivAt
    have hf2 : HasDerivAt (deriv f) (iteratedDeriv 2 f (σ * w)) (σ * w) := by
      have hcd1 : ContDiffOn ℝ 2 (deriv f) Yint := by
        have h2 := (hf.fderiv_of_isOpen isOpen_Ioo (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)).clm_apply
          (contDiffOn_const (c := (1 : ℝ)))
        exact h2.congr fun y _ => by simp
      have h1 := (hcd1.contDiffAt (isOpen_Ioo.mem_nhds hmem)).differentiableAt (by norm_num) |>.hasDerivAt
      rw [iteratedDeriv_succ, iteratedDeriv_one]; exact h1
    have harg : HasDerivAt (fun s => s * w) w σ := ((hasDerivAt_id σ).mul_const w).congr_deriv (by ring)
    have hA := hf1.comp σ harg
    have hB := (((hasDerivAt_const σ 1).sub (hasDerivAt_id σ)).mul_const w).mul (hf2.comp σ harg)
    exact (hA.add hB).congr_deriv (by simp; ring)
  have hφ_cont : ContinuousOn (fun σ => (1 - σ) * w ^ 2 * iteratedDeriv 2 f (σ * w)) (Set.uIcc (0 : ℝ) 1) := by
    have hcd2 : ContDiffOn ℝ 1 (iteratedDeriv 2 f) Yint := by
      have hcd1 : ContDiffOn ℝ 2 (deriv f) Yint :=
        ((hf.fderiv_of_isOpen isOpen_Ioo (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)).clm_apply
          (contDiffOn_const (c := (1 : ℝ)))).congr fun y _ => by simp
      have h2 := (hcd1.fderiv_of_isOpen isOpen_Ioo (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
        (contDiffOn_const (c := (1 : ℝ)))
      exact h2.congr fun y _ => by simp [iteratedDeriv_succ, iteratedDeriv_one]
    have hcomp := hcd2.continuousOn.comp (continuousOn_id.mul continuousOn_const) fun σ hσ => hmap σ hσ
    exact ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).mul hcomp
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hφ_deriv hφ_cont.intervalIntegrable
  have hφ1 : φ 1 = f w := by simp [φ]
  have hφ0 : φ 0 = deriv f 0 * w := by simp [φ, hf0]; ring
  rw [hφ1, hφ0] at hFTC
  rw [← hFTC]
  rw [intervalIntegral.integral_of_le zero_le_one, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have heq : ∀ σ : ℝ, (1 - σ) * w ^ 2 * iteratedDeriv 2 f (σ * w) =
      w ^ 2 * ((1 - σ) * iteratedDeriv 2 f (σ * w)) := fun σ => by ring
  simp_rw [heq]
  rw [MeasureTheory.integral_const_mul]

private lemma fctInner_u_sq_sym {c : ℝ} (hc0 : 0 < c) :
    FctSymClsOn (Icc 0 (fctUc c)) 8 2 2 (fun u => ((u ^ 2 : ℝ) : ℂ)) := by
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  refine FctSymClsOn.ofReal_cast (uniqueDiffOn_Icc hUc0) (contDiffOn_id.pow 2) fun r hr u hu => ?_
  have hu0 : 0 ≤ u := hu.1
  have h1u : 1 ≤ 1 + u := by linarith only [hu0]
  have hcd_sq : ContDiffAt ℝ r (fun x : ℝ => x ^ 2) u := by fun_prop
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hUc0) hcd_sq hu]
  rcases Nat.lt_trichotomy r 1 with hr0 | rfl | hr1
  · obtain rfl : r = 0 := by omega
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, Real.rpow_two]
    rw [abs_of_nonneg (sq_nonneg u)]
    nlinarith only [hu0]
  · rw [iteratedDeriv_one]
    have hd : deriv (fun x : ℝ => x ^ 2) u = 2 * u := by
      simpa using (hasDerivAt_pow 2 u).deriv
    rw [hd, Nat.cast_one, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
      abs_of_nonneg (by linarith only [hu0])]
    linarith only [hu0]
  · rcases eq_or_lt_of_le (by omega : 2 ≤ r) with rfl | hr2
    · rw [iteratedDeriv_succ, iteratedDeriv_one]
      have hd1 : deriv (fun x : ℝ => x ^ 2) = fun x : ℝ => 2 * x := by
        ext x; simpa using (hasDerivAt_pow 2 x).deriv
      have hd2 : deriv (fun x : ℝ => 2 * x) u = 2 := by
        simpa using ((hasDerivAt_id u).const_mul (2 : ℝ)).deriv
      rw [hd1, hd2, Nat.cast_ofNat, sub_self, Real.rpow_zero, mul_one, abs_of_pos (by norm_num)]
    · have hzero : iteratedDeriv r (fun x : ℝ => x ^ 2) u = 0 := by
        obtain ⟨k, rfl⟩ : ∃ k, r = k + 3 := ⟨r - 3, by omega⟩
        have h2 : iteratedDeriv 2 (fun x : ℝ => x ^ 2) = fun _ => (2 : ℝ) := by
          ext x
          rw [iteratedDeriv_succ, iteratedDeriv_one]
          have hd1 : deriv (fun y : ℝ => y ^ 2) = fun y => 2 * y := by
            ext y; simpa using (hasDerivAt_pow 2 y).deriv
          rw [hd1]; simpa using ((hasDerivAt_id x).const_mul (2 : ℝ)).deriv
        have h3 : ∀ m : ℕ, ∀ x : ℝ, iteratedDeriv (m + 3) (fun y : ℝ => y ^ 2) x = 0 := by
          intro m
          induction m with
          | zero => intro x; rw [zero_add, iteratedDeriv_succ, h2]; simp
          | succ m ih =>
            intro x
            rw [show m + 1 + 3 = (m + 3) + 1 by omega, iteratedDeriv_succ]
            have hfn : iteratedDeriv (m + 3) (fun y : ℝ => y ^ 2) = fun _ => (0 : ℝ) := funext ih
            rw [hfn]; simp
        exact h3 k u
      rw [hzero, abs_zero]
      positivity

/-- **`(fct:inner-symbols)` (b3), `J₀ - 1` part**:
under `c ≥ c₀`, `K₄ τ₁² ≤ 1`, `(ell1, 0, α) ∈ S.Ω`, and `S.A (ell1, 1, α) ≤ 4 c^{-1/6}`,
we have `Jfun S.V fctH (τ₁^2) ((ell1, 0, α), fctInnerY c u) - 1 ∈ 𝒮^{10}(C c^{-4/3})` on `[0, U_c]`. -/
theorem fctInner_J0_sub_one_sym {M_box C0_box : ℝ}
    (hM0 : 0 ≤ M_box) (hC0_pos : 0 ≤ C0_box) :
    ∃ (δH C c₀ : ℝ), 0 < δH ∧ 0 ≤ C ∧ 100 ≤ c₀ ∧
      ∀ {K4 ε c : ℝ}, 1 ≤ K4 → (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        let τ₁ := c ^ (-(1 / 4 : ℝ))
        τ₁ ^ 2 < δH / 6 →
        K4 * τ₁ ^ 2 ≤ 1 →
        ∀ {T : CfuTheta} {S : ChartSetup (ℝ × ℝ × ℝ)},
          T.M = M_box → T.mt = concreteMt →
          S.Ω = OmT τ₁ → S.ℓ = (fun p : ℝ × ℝ × ℝ => p.1) → S.r = T.r τ₁ K4 →
          S.ε = C0_box * τ₁ ^ 2 →
          ∀ {L1 α : ℝ},
            let ell1 := concreteEll1 ε c L1
            ell1 ∈ Ioo (0 : ℝ) 2.55 →
            |α| ≤ c ^ (-(1 / 2 : ℝ)) →
            S.A (ell1, 1, α) ≤ 4 * c ^ (-(1 / 6 : ℝ)) →
            FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C * c ^ (-(4 / 3 : ℝ)))
              (fun u => ((Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), fctInnerY c u) - 1 : ℝ) : ℂ)) := by
  obtain ⟨r_star, B_Jrs, δH, hr_pos, hr_200, hδH_pos, hδH_30, hr_δH, hr_cR, hBJrs_nn, hSrs_all⟩ :=
    r_rs_chart_exist hM0 (by norm_num : (0 : ℝ) ≤ 2) hC0_pos
  have hr2_pos : 0 < r_star ^ 2 := sq_pos_of_pos hr_pos
  -- Uniform constants independent of `(T, K4, ε, c, L1, α)`
  let Y_Q : Set ℝ := Ioo (-(1 / 10 : ℝ)) 1
  let bw_Q : ℝ := 2 ^ 13 * 1 * ((Nat.factorial 13 : ℝ) * 1)
  let C_comp_Q : ℝ := (Nat.factorial 13 : ℝ) * (max 1 (max 1 bw_Q)) ^ 13
  let B_Q : ℝ := (Nat.factorial 8 : ℝ) * (2 ^ 13 * C_comp_Q * B_Jrs)
  let C_Q_sym : ℝ := 100 ^ 8 * ((Nat.factorial 8 : ℝ) * B_Q)
  let C_d : ℝ := 8 * B_Jrs / r_star ^ 2
  let C_w : ℝ := 2 / r_star ^ 2
  let C_lin : ℝ := C_d * C_w
  let C_quad : ℝ := 2 ^ 8 * (2 ^ 8 * C_w * C_w) * C_Q_sym
  let C_tot : ℝ := C_lin + C_quad
  let thresh_c : ℝ := max (160000 : ℝ) (max ((30 * C0_box + 1) ^ 2)
    (max ((161 / r_star ^ 2) ^ 2) (2 / r_star ^ 2)))
  refine ⟨δH, C_tot, thresh_c, hδH_pos, by positivity,
    (by linarith only [le_max_left (160000 : ℝ) (max ((30 * C0_box + 1) ^ 2)
      (max ((161 / r_star ^ 2) ^ 2) (2 / r_star ^ 2)))] : 100 ≤ thresh_c), ?_⟩
  intro K4 ε c hK4 hε hc τ₁ hτ1_δH hK4t T S hTM hTmt hSΩ hSℓ hSr hSε L1 α ell1 hell1 hα hSA
  have hc160000 : (160000 : ℝ) ≤ c := le_trans (le_max_left _ _) hc
  have hc100 : (100 : ℝ) ≤ c := by linarith only [hc160000]
  have hc0 : 0 < c := by linarith only [hc100]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_sq_eq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hτ₁_4_eq : τ₁ ^ 4 = c⁻¹ := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num [Real.rpow_neg_one]
  have hτ₁_1 : τ₁ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [hc100]) (by norm_num)
  have hτ₁_sq_le1 : τ₁ ^ 2 ≤ 1 := pow_le_one₀ hτ₁_pos.le hτ₁_1
  have hc_C0 : (30 * C0_box + 1) ^ 2 ≤ c :=
    (le_max_left _ _ |>.trans (le_max_right _ _)).trans hc
  have hc_r1 : (161 / r_star ^ 2) ^ 2 ≤ c :=
    (le_max_left _ _ |>.trans (le_max_right _ _) |>.trans (le_max_right _ _)).trans hc
  have hc_r2 : 2 / r_star ^ 2 ≤ c :=
    (le_max_right _ _ |>.trans (le_max_right _ _) |>.trans (le_max_right _ _)).trans hc
  have hc_half : 161 / r_star ^ 2 ≤ c ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_r1
  have hc_neg_half : c ^ (-(1 / 2 : ℝ)) ≤ r_star ^ 2 / 161 := by
    rw [Real.rpow_neg hc0.le]
    have hpos : (0 : ℝ) < 161 / r_star ^ 2 := by positivity
    calc (c ^ (1 / 2 : ℝ))⁻¹ ≤ (161 / r_star ^ 2)⁻¹ := inv_anti₀ hpos hc_half
      _ = r_star ^ 2 / 161 := by rw [inv_div]
  have hc_neg_23_le : c ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hc100]) (by norm_num)
  -- Fixed-scale chart `S_rs` for `θt = T.θt`
  have hsub30 : Ioo (-(1 / 30 : ℝ)) (1 / 30) ⊆ Ioo (-1 : ℝ) 6 := fun x hx =>
    ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  have jc_30 : ∀ {g : ℝ → ℝ}, JC 18 (Ioo (-1 : ℝ) 6) g M_box → JC 18 (Ioo (-(1 / 30 : ℝ)) (1 / 30)) g M_box := by
    intro g hg
    refine ⟨hg.1.mono hsub30, fun i hi x hx => ?_⟩
    rw [iteratedFDerivWithin_of_isOpen (n := i) isOpen_Ioo hx,
      ← iteratedFDerivWithin_of_isOpen (n := i) isOpen_Ioo (hsub30 hx)]
    exact hg.2 i hi x (hsub30 hx)
  have hmt_jc : JC 18 (Ioo (-(1 / 30 : ℝ)) (1 / 30)) concreteMt M_box :=
    jc_30 (by rw [← hTM, ← hTmt]; exact T.jc_mt)
  have hθt_jc : JC 18 (Ioo (-(1 / 30 : ℝ)) (1 / 30)) T.θt M_box :=
    jc_30 (by rw [← hTM]; exact T.jc_θt)
  obtain ⟨S_rs, hSrs_Ω, hSrs_ℓ, hSrs_r, h15rs, hJrs_jc, hJrs_0, hJrs_d0⟩ :=
    hSrs_all hmt_jc hθt_jc
  -- Bounding `ell1 ≤ 8 c^{-1/6}` via `ZeroPath` / `A_comp` and `15 * S.ε ≤ 1/2`
  have hα_om : |α| < 2 * τ₁ ^ 2 := by
    rw [hτ₁_sq_eq]
    have : 0 < c ^ (-(1 / 2 : ℝ)) := by positivity
    linarith only [hα, this]
  have hp0_mem : (ell1, 0, α) ∈ S.Ω := by
    rw [hSΩ]
    refine ⟨⟨by linarith only [hell1.1], by linarith only [hell1.2]⟩, ⟨by norm_num, by norm_num⟩, ?_⟩
    simpa [abs_lt] using hα_om
  have hp1_mem : (ell1, 1, α) ∈ S.Ω := by
    rw [hSΩ]
    refine ⟨⟨by linarith only [hell1.1], by linarith only [hell1.2]⟩, ⟨by norm_num, by norm_num⟩, ?_⟩
    simpa [abs_lt] using hα_om
  have hSε_bd : 15 * S.ε ≤ 1 / 2 := by
    have h1 : 30 * C0_box + 1 ≤ c ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_C0
    have hpos : (0 : ℝ) < 30 * C0_box + 1 := by positivity
    have h2 : C0_box * τ₁ ^ 2 ≤ 1 / 30 := by
      rw [hτ₁_sq_eq, Real.rpow_neg hc0.le]
      calc C0_box * (c ^ (1 / 2 : ℝ))⁻¹ ≤ C0_box * (30 * C0_box + 1)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ hpos h1) hC0_pos
        _ ≤ 1 / 30 := by rw [← div_eq_mul_inv, div_le_div_iff₀ hpos (by norm_num)]; linarith only
    rw [hSε]; linarith only [h2]
  have hρ_bd : ∀ p ∈ S.Ω, ∀ z ∈ Ioo (-1 : ℝ) 6, |rhoF S.r (p, z)| ≤ 1 / 2 * |z| := by
    intro p hp z hz
    have hr0 : rhoF S.r (p, 0) = 0 := by
      have hrs0 : S.r (p, 0) = 0 := by rw [hSr]; simp [CfuTheta.r]
      simp [rhoF, hrs0]
    have hO : IsOpen (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hΩ.prod isOpen_Ioo
    have hp_emb : ContDiffOn ℝ 18 (fun w : ℝ => (p, w)) (Ioo (-1 : ℝ) 6) := by fun_prop
    have hr_w : ContDiffOn ℝ 18 (fun w => S.r (p, w)) (Ioo (-1 : ℝ) 6) :=
      S.hr.1.comp hp_emb fun w hw => ⟨hp, hw⟩
    have h17 := (S.hr.succ_fderiv hO).clm_apply_const hO.uniqueDiffOn ((0 : ℝ × ℝ × ℝ), (1 : ℝ))
    have hfd_w : ContDiffOn ℝ 17 (fun w => fderiv ℝ S.r (p, w) (0, 1)) (Ioo (-1 : ℝ) 6) :=
      h17.1.comp (hp_emb.of_le (by norm_num : (17 : WithTop ℕ∞) ≤ 18)) fun w hw => ⟨hp, hw⟩
    have hrho_cd : ContDiffOn ℝ 1 (fun w => rhoF S.r (p, w)) (Ioo (-1 : ℝ) 6) :=
      ((hr_w.of_le (by norm_num)).add
        (contDiffOn_const.mul (contDiffOn_id.mul (hfd_w.of_le (by norm_num))))).congr
        fun _ _ => rfl
    have hderiv_bd : ∀ w ∈ Ioo (-1 : ℝ) 6, |deriv (fun t => rhoF S.r (p, t)) w| ≤ 1 / 2 := by
      intro w hw
      have hq : (p, w) ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hp, hw⟩
      have hdr : HasDerivAt (fun t => S.r (p, t)) (fderiv ℝ S.r (p, w) (0, 1)) w := by
        have h1 := ((S.hr.1.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt
        exact h1.comp_hasDerivAt w (by simpa using (hasDerivAt_const w p).prodMk (hasDerivAt_id w))
      have hd2 : HasDerivAt (fun t => fderiv ℝ S.r (p, t) (0, 1))
          (fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)) w := by
        have h1 := ((h17.1.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt
        exact h1.comp_hasDerivAt w (by simpa using (hasDerivAt_const w p).prodMk (hasDerivAt_id w))
      have htot : HasDerivAt (fun t => rhoF S.r (p, t))
          (fderiv ℝ S.r (p, w) (0, 1) + 2 * (1 * fderiv ℝ S.r (p, w) (0, 1) +
            w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1))) w :=
        (hdr.add (((hasDerivAt_id w).mul hd2).const_mul 2)).congr_of_eventuallyEq
          (Eventually.of_forall fun t => by simp [rhoF])
      rw [htot.deriv]
      have hb1 : |fderiv ℝ S.r (p, w) (0, 1)| ≤ S.ε := by
        have hbd := S.hr.2 1 (by norm_num) (p, w) hq
        rw [norm_iteratedFDerivWithin_one _ (hO.uniqueDiffOn _ hq), fderivWithin_of_isOpen hO hq] at hbd
        calc |fderiv ℝ S.r (p, w) (0, 1)| = ‖fderiv ℝ S.r (p, w) (0, 1)‖ := Real.norm_eq_abs _
          _ ≤ ‖fderiv ℝ S.r (p, w)‖ * ‖((0 : ℝ × ℝ × ℝ), (1 : ℝ))‖ := (fderiv ℝ S.r _).le_opNorm _
          _ ≤ S.ε * 1 := mul_le_mul hbd (by simp [Prod.norm_def]) (norm_nonneg _) S.hε
          _ = S.ε := mul_one _
      have hb2 : |fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)| ≤ S.ε := by
        have hbd := h17.2 1 (by norm_num) (p, w) hq
        rw [norm_iteratedFDerivWithin_one _ (hO.uniqueDiffOn _ hq), fderivWithin_of_isOpen hO hq] at hbd
        have hbd' : ‖fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w)‖ ≤ S.ε :=
          hbd.trans (by simp [Prod.norm_def])
        calc |fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)|
            = ‖fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)‖ := Real.norm_eq_abs _
          _ ≤ ‖fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w)‖ * ‖((0 : ℝ × ℝ × ℝ), (1 : ℝ))‖ :=
              (fderiv ℝ _ _).le_opNorm _
          _ ≤ S.ε * 1 := mul_le_mul hbd' (by simp [Prod.norm_def]) (norm_nonneg _) S.hε
          _ = S.ε := mul_one _
      have hw6 : |w| ≤ 6 := by rw [abs_le]; constructor <;> linarith only [hw.1, hw.2]
      calc |fderiv ℝ S.r (p, w) (0, 1) + 2 * (1 * fderiv ℝ S.r (p, w) (0, 1) +
              w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1))|
          = |3 * fderiv ℝ S.r (p, w) (0, 1) +
              2 * w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)| := by congr 1; ring
        _ ≤ |3 * fderiv ℝ S.r (p, w) (0, 1)| +
              |2 * w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)| := abs_add_le _ _
        _ = 3 * |fderiv ℝ S.r (p, w) (0, 1)| +
              2 * |w| * |fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
              abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        _ ≤ 3 * S.ε + 2 * 6 * S.ε := by gcongr
        _ = 15 * S.ε := by ring
        _ ≤ 1 / 2 := hSε_bd
    have hmv := (convex_Ioo (-1 : ℝ) 6).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun w hw => ((hrho_cd.differentiableOn (by norm_num) w hw).hasDerivWithinAt).congr_deriv
        (by rw [derivWithin_of_isOpen isOpen_Ioo hw]))
      (fun w hw => by rw [Real.norm_eq_abs]; exact hderiv_bd w hw)
      (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 6 from ⟨by norm_num, by norm_num⟩) hz
    simpa [hr0, Real.norm_eq_abs, sub_zero] using hmv
  have hzp1 : S.ZeroPath (ell1, 1, α) := by
    refine ⟨hp1_mem, by rw [hSℓ]; linarith only [hell1.1], (1, 0, 0), by simp [Prod.norm_def], fun s hs => ?_⟩
    have hsub : (ell1, 1, α) - s • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) = (ell1 - s, 1, α) := by ext <;> simp
    rw [hSℓ] at hs ⊢; simp only at hs
    rw [hsub]
    refine ⟨?_, rfl⟩
    rw [hSΩ]
    exact ⟨⟨by linarith only [hs.1, hs.2, hell1.1], by linarith only [hs.1, hell1.2]⟩,
      ⟨by norm_num, by norm_num⟩, by simpa [abs_lt] using hα_om⟩
  have hSA1_nn : 0 ≤ S.A (ell1, 1, α) := (S.A_comp hρ_bd hzp1 hzp1 rfl).1
  have hSB1_nn : 0 ≤ S.B (ell1, 1, α) := by
    have hd_pos : 0 < S.d (ell1, 1, α) ^ 2 := sq_pos_of_pos (S.out.2.2.2.1 _ hp1_mem).1
    have hA_eq : S.A (ell1, 1, α) = S.d (ell1, 1, α) ^ 2 * S.B (ell1, 1, α) := rfl
    nlinarith only [hSA1_nn, hd_pos, hA_eq]
  have hell1_bd : ell1 ≤ 8 * c ^ (-(1 / 6 : ℝ)) := by
    have hB_eq := (S.out.2.1 (ell1, 1, α) hp1_mem)
    have hρB := hρ_bd (ell1, 1, α) hp1_mem (S.B (ell1, 1, α)) hB_eq.1
    rw [abs_of_nonneg hSB1_nn] at hρB
    have hℓ_le : ell1 ≤ (π ^ 2 / 12 + 1 / 2) * S.B (ell1, 1, α) := by
      have heq : S.ℓ (ell1, 1, α) = π ^ 2 / 12 * S.B (ell1, 1, α) - rhoF S.r ((ell1, 1, α), S.B (ell1, 1, α)) := by
        linarith only [hB_eq.2]
      rw [hSℓ] at heq
      have hrho_lo : -(1 / 2 * S.B (ell1, 1, α)) ≤ rhoF S.r ((ell1, 1, α), S.B (ell1, 1, α)) :=
        (abs_le.mp hρB).1
      linarith only [heq, hrho_lo]
    have hd_lo : (92 / 100 : ℝ) ≤ S.d (ell1, 1, α) := by
      have hd1 := abs_le.mp (S.d_dev hp1_mem)
      linarith only [hd1.1, dStar_bounds.1]
    have hA_ge : (0.8464 : ℝ) * S.B (ell1, 1, α) ≤ S.A (ell1, 1, α) := by
      have hdsq : (0.8464 : ℝ) ≤ S.d (ell1, 1, α) ^ 2 := by nlinarith only [hd_lo]
      have hA_eq : S.A (ell1, 1, α) = S.d (ell1, 1, α) ^ 2 * S.B (ell1, 1, α) := rfl
      nlinarith only [hdsq, hSB1_nn, hA_eq]
    have hpi_ub : π ^ 2 / 12 + 1 / 2 < 2 * 0.8464 := by
      have hpi := Real.pi_lt_d2
      nlinarith only [hpi, Real.pi_pos]
    have hle1 : ell1 ≤ (2 * 0.8464) * S.B (ell1, 1, α) :=
      hℓ_le.trans (mul_le_mul_of_nonneg_right hpi_ub.le hSB1_nn)
    linarith only [hle1, hA_ge, hSA]
  -- Rescaling parameters and hypotheses for `Jfun_scale_eq`
  let lam : ℝ := τ₁ ^ 2 / r_star ^ 2
  have hlam_pos : 0 < lam := div_pos (sq_pos_of_pos hτ₁_pos) hr2_pos
  have hlam_16 : lam ≤ 1 / 6 := by
    have h1 : τ₁ ^ 2 ≤ r_star ^ 2 / 161 := hτ₁_sq_eq ▸ hc_neg_half
    dsimp only [lam]
    rw [div_le_iff₀ hr2_pos]
    nlinarith only [h1, hr2_pos]
  let p_rs : ℝ × ℝ := (lam * ell1, τ₁ ^ 4 / r_star ^ 2)
  have hprs_mem : p_rs ∈ fctOmegaRs := by
    have hell_nn : 0 ≤ ell1 := hell1.1.le
    have hprod1 : 0 ≤ lam * ell1 := mul_nonneg hlam_pos.le hell_nn
    have hprod2 : lam * ell1 < 1 / 20 := by
      have hc16_1 : c ^ (-(1 / 6 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [hc100]) (by norm_num)
      have h1 : lam * ell1 ≤ (r_star ^ 2 / 161) / r_star ^ 2 * 8 * 1 := by
        have hlam_le : lam ≤ (r_star ^ 2 / 161) / r_star ^ 2 :=
          div_le_div_of_nonneg_right (hτ₁_sq_eq ▸ hc_neg_half) hr2_pos.le
        have h8 : ell1 ≤ 8 * 1 := hell1_bd.trans (mul_le_mul_of_nonneg_left hc16_1 (by norm_num))
        nlinarith only [hlam_le, h8, hell_nn, hlam_pos]
      have h2 : (r_star ^ 2 / 161) / r_star ^ 2 * 8 * 1 = 8 / 161 := by
        field_simp [hr2_pos.ne']
      linarith only [h1, h2]
    have hp2_pos : 0 < τ₁ ^ 4 / r_star ^ 2 := div_pos (pow_pos hτ₁_pos 4) hr2_pos
    have hp2_1 : τ₁ ^ 4 / r_star ^ 2 < 1 := by
      rw [hτ₁_4_eq, ← one_div, div_div, mul_comm c _]
      have hpos : (0 : ℝ) < r_star ^ 2 * c := by positivity
      rw [div_lt_one hpos]
      have : 2 ≤ r_star ^ 2 * c := (le_div_iff₀ hr2_pos).mp hc_r2 |>.trans_eq (mul_comm _ _)
      linarith only [this]
    exact ⟨⟨by linarith only [hprod1], hprod2⟩, ⟨by linarith only [hp2_pos], hp2_1⟩⟩
  have hR_small : ∀ z ∈ Ioo (-1 : ℝ) 6, |lam⁻¹ * S.R ((ell1, 0, α), z)| < 1 / 50 := by
    intro z hz
    have hq : ((ell1, 0, α), z) ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hp0_mem, hz⟩
    have hReq := S.out.2.2.2.2.2.1 _ hq
    have hBmem := (S.out.2.1 _ hp0_mem).1
    have hd_abs := abs_le.mp (S.d_dev hp0_mem)
    have hd_lo : (92 / 100 : ℝ) ≤ S.d (ell1, 0, α) := by linarith only [hd_abs.1, dStar_bounds.1]
    have hd_hi : S.d (ell1, 0, α) ≤ 95 / 100 := by linarith only [hd_abs.2, dStar_bounds.2]
    have hz6 : |z| ≤ 6 := by rw [abs_le]; constructor <;> linarith only [hz.1, hz.2]
    have hzB7 : |z - S.B (ell1, 0, α)| ≤ 7 := by
      rw [abs_le]; constructor <;> linarith only [hz.1, hz.2, hBmem.1, hBmem.2]
    have hR50 : |S.R ((ell1, 0, α), z)| ≤ 1 / 50 := hReq.1.le
    let coef := S.d (ell1, 0, α) ^ 2 + S.d (ell1, 0, α) * z * S.R ((ell1, 0, α), z) +
      1 / 3 * z * (z - S.B (ell1, 0, α)) * S.R ((ell1, 0, α), z) ^ 2
    have h1 : |S.d (ell1, 0, α) * z * S.R ((ell1, 0, α), z)| ≤ (95 / 100) * 6 * (1 / 50) := by
      rw [abs_mul, abs_mul, abs_of_pos (by linarith only [hd_lo])]
      exact mul_le_mul (mul_le_mul hd_hi hz6 (abs_nonneg z) (by positivity)) hR50 (abs_nonneg _) (by positivity)
    have h2 : |1 / 3 * z * (z - S.B (ell1, 0, α)) * S.R ((ell1, 0, α), z) ^ 2| ≤
        (1 / 3 : ℝ) * 6 * 7 * (1 / 50) ^ 2 := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)]
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left hz6 (by norm_num)) hzB7 (abs_nonneg _) (by positivity)
      exact mul_le_mul hh (pow_le_pow_left₀ (abs_nonneg _) hR50 2) (sq_nonneg _) (by positivity)
    have hcoef_ge : (1 / 2 : ℝ) ≤ coef := by
      have h1' := abs_le.mp h1
      have h2' := abs_le.mp h2
      have hdsq : (92 / 100 : ℝ) ^ 2 ≤ S.d (ell1, 0, α) ^ 2 := by nlinarith only [hd_lo]
      dsimp only [coef]; linarith only [hdsq, h1'.1, h2'.1]
    have hhad_bd : |hadH S.r S.B ((ell1, 0, α), z)| ≤ S.ε := by
      unfold hadH
      have hO : IsOpen (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hΩ.prod isOpen_Ioo
      have h17 := (S.hr.succ_fderiv hO).clm_apply_const hO.uniqueDiffOn ((0 : ℝ × ℝ × ℝ), (1 : ℝ))
      have hσ_mem : ∀ σ ∈ Icc (0 : ℝ) 1,
          ((ell1, 0, α), S.B (ell1, 0, α) + σ * (z - S.B (ell1, 0, α))) ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6 := by
        intro σ hσ
        have := (convex_Ioo (-1 : ℝ) 6).add_smul_sub_mem hBmem hz hσ
        exact ⟨hp0_mem, by simpa [smul_eq_mul] using this⟩
      have h_int_bd : ∀ σ ∈ Icc (0 : ℝ) 1,
          ‖(1 - σ) * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1))
            ((ell1, 0, α), S.B (ell1, 0, α) + σ * (z - S.B (ell1, 0, α))) (0, 1)‖ ≤ S.ε := by
        intro σ hσ
        have hqσ := hσ_mem σ hσ
        have hbd := h17.2 1 (by norm_num) _ hqσ
        rw [norm_iteratedFDerivWithin_one _ (hO.uniqueDiffOn _ hqσ), fderivWithin_of_isOpen hO hqσ] at hbd
        have hfd : ‖fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) _ ((0 : ℝ × ℝ × ℝ), (1 : ℝ))‖ ≤ S.ε :=
          ((fderiv ℝ _ _).le_opNorm _).trans (by
            have hn1 : ‖((0 : ℝ × ℝ × ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
            rw [hn1, mul_one] at *
            exact (mul_le_mul_of_nonneg_right hbd zero_le_one).trans_eq (mul_one _))
        have h1σ : ‖(1 - σ : ℝ)‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (by linarith only [hσ.2])]; linarith only [hσ.1]
        calc ‖(1 - σ) * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) _ (0, 1)‖
            = ‖1 - σ‖ * ‖fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) _ (0, 1)‖ := norm_mul _ _
          _ ≤ 1 * S.ε := mul_le_mul h1σ hfd (norm_nonneg _) zero_le_one
          _ = S.ε := one_mul _
      have hint_le := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume)
        (show volume (Icc (0 : ℝ) 1) < ⊤ by simp) h_int_bd
      simpa [Real.norm_eq_abs, Real.volume_Icc] using hint_le
    have hR_le : |S.R ((ell1, 0, α), z)| ≤ 2 * S.ε := by
      have heq : S.R ((ell1, 0, α), z) * coef = -hadH S.r S.B ((ell1, 0, α), z) := by
        dsimp only [coef]; linarith only [hReq.2]
      have hab : |S.R ((ell1, 0, α), z)| * |coef| = |hadH S.r S.B ((ell1, 0, α), z)| := by
        rw [← abs_mul, heq, abs_neg]
      rw [abs_of_pos (by linarith only [hcoef_ge])] at hab
      nlinarith only [hab, hcoef_ge, hhad_bd, abs_nonneg (S.R ((ell1, 0, α), z))]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hlam_pos)]
    calc lam⁻¹ * |S.R ((ell1, 0, α), z)|
        ≤ (r_star ^ 2 / τ₁ ^ 2) * (2 * (C0_box * τ₁ ^ 2)) := by
          rw [← hSε]
          exact mul_le_mul_of_nonneg_left hR_le (inv_pos.mpr hlam_pos).le
      _ = 2 * C0_box * r_star ^ 2 := by
          have htne : τ₁ ^ 2 ≠ 0 := (sq_pos_of_pos hτ₁_pos).ne'
          field_simp [htne]
      _ < 1 / 50 := hr_cR
  -- Setup `J_rs` and its 1st/2nd derivatives on `fctOmegaRs ×ˢ Yint`
  let J_rs : (ℝ × ℝ) × ℝ → ℝ := Jfun S_rs.V fctH (r_star ^ 2)
  have hO_rs : IsOpen (fctOmegaRs ×ˢ Yint) := isOpen_fctOmegaRs.prod isOpen_Ioo
  have hUd_rs : UniqueDiffOn ℝ (fctOmegaRs ×ˢ Yint) := hO_rs.uniqueDiffOn
  have hJrs_w_cd : ContDiffOn ℝ 15 (fun w => J_rs (p_rs, w)) Yint :=
    hJrs_jc.1.comp (contDiffOn_const.prodMk contDiffOn_id) fun w hw => ⟨hprs_mem, hw⟩
  -- 1. Linear term bound `|deriv (J_rs (p_rs, ·)) 0| ≤ C_d * c^{-2/3}`
  let F_der : ℝ × ℝ → ℝ := fun p => fderiv ℝ J_rs (p, 0) (0, 1)
  have hJrs_d14 : JC 14 (fctOmegaRs ×ˢ Yint) (fun q => fderiv ℝ J_rs q (0, 1)) B_Jrs :=
    JC.deriv_snd hO_rs hJrs_jc
  have hF_diff : ∀ p ∈ fctOmegaRs, HasFDerivWithinAt F_der
      ((fderiv ℝ (fun q => fderiv ℝ J_rs q (0, 1)) (p, 0)).comp (ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ))
      fctOmegaRs p := by
    intro p hp
    have h1 : HasFDerivAt (fun q => fderiv ℝ J_rs q (0, 1))
        (fderiv ℝ (fun q => fderiv ℝ J_rs q (0, 1)) (p, 0)) (p, 0) :=
      ((hJrs_d14.1.contDiffAt (hO_rs.mem_nhds ⟨hp, zero_mem_Yint⟩)).differentiableAt (by norm_num)).hasFDerivAt
    have h2 : HasFDerivAt (fun x : ℝ × ℝ => (x, (0 : ℝ))) (ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ) p :=
      (hasFDerivAt_id p).prodMk (hasFDerivAt_const 0 p)
    exact (h1.comp p h2).hasFDerivWithinAt
  have hF_bd : ∀ p ∈ fctOmegaRs,
      ‖(fderiv ℝ (fun q => fderiv ℝ J_rs q (0, 1)) (p, 0)).comp (ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ)‖ ≤ B_Jrs := by
    intro p hp
    have hq0 : (p, (0 : ℝ)) ∈ fctOmegaRs ×ˢ Yint := ⟨hp, zero_mem_Yint⟩
    have hb := hJrs_d14.2 1 (by norm_num) _ hq0
    rw [norm_iteratedFDerivWithin_one _ (hUd_rs _ hq0), fderivWithin_of_isOpen hO_rs hq0] at hb
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖fderiv ℝ (fun q => fderiv ℝ J_rs q (0, 1)) (p, 0)‖ * ‖ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ‖
        ≤ B_Jrs * 1 := mul_le_mul hb (ContinuousLinearMap.norm_inl_le_one ℝ (ℝ × ℝ) ℝ)
          (norm_nonneg _) hBJrs_nn
      _ = B_Jrs := mul_one _
  have hp00_mem : ((0 : ℝ), (0 : ℝ)) ∈ fctOmegaRs := ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  have hF_der_eq : ∀ p ∈ fctOmegaRs, deriv (fun w => J_rs (p, w)) 0 = F_der p := by
    intro p hp
    have hp0 : (p, (0 : ℝ)) ∈ fctOmegaRs ×ˢ Yint := ⟨hp, zero_mem_Yint⟩
    have h1 := ((hJrs_jc.1.contDiffAt (hO_rs.mem_nhds hp0)).differentiableAt (by norm_num)).hasFDerivAt
    have h2 : HasDerivAt (fun w : ℝ => (p, w)) (0, 1) 0 := by
      simpa using (hasDerivAt_const (0 : ℝ) p).prodMk (hasDerivAt_id (0 : ℝ))
    exact (h1.comp_hasDerivAt 0 h2).deriv
  have hF00 : F_der (0, 0) = 0 := by rw [← hF_der_eq (0, 0) hp00_mem]; exact hJrs_d0
  have hmv_der := (convex_Ioo (-(1 / 20 : ℝ)) (1 / 20)).prod (convex_Ioo (-1 : ℝ) 1) |>.norm_image_sub_le_of_norm_hasFDerivWithin_le
    hF_diff hF_bd hp00_mem hprs_mem
  have hprs_norm : ‖p_rs - (0, 0)‖ ≤ 8 / r_star ^ 2 * c ^ (-(2 / 3 : ℝ)) := by
    rw [show p_rs - ((0 : ℝ), (0 : ℝ)) = p_rs from sub_zero p_rs, Prod.norm_def]
    refine max_le ?_ ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos hlam_pos, abs_of_nonneg hell1.1.le]
      dsimp only [lam]
      rw [hτ₁_sq_eq]
      have hc_eq : c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ)) = c ^ (-(2 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      calc c ^ (-(1 / 2 : ℝ)) / r_star ^ 2 * ell1
          ≤ c ^ (-(1 / 2 : ℝ)) / r_star ^ 2 * (8 * c ^ (-(1 / 6 : ℝ))) :=
            mul_le_mul_of_nonneg_left hell1_bd (by positivity)
        _ = 8 / r_star ^ 2 * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ))) := by ring
        _ = 8 / r_star ^ 2 * c ^ (-(2 / 3 : ℝ)) := by rw [hc_eq]
    · rw [Real.norm_eq_abs, abs_of_pos (div_pos (pow_pos hτ₁_pos 4) hr2_pos), hτ₁_4_eq]
      have hcinv : c⁻¹ ≤ 8 * c ^ (-(2 / 3 : ℝ)) := by
        have h1 : c⁻¹ = c ^ (-1 : ℝ) := (Real.rpow_neg_one c).symm
        have h2 : c ^ (-1 : ℝ) ≤ c ^ (-(2 / 3 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith only [hc100]) (by norm_num)
        have hpos : 0 ≤ c ^ (-(2 / 3 : ℝ)) := by positivity
        linarith only [h1, h2, hpos]
      calc c⁻¹ / r_star ^ 2 ≤ (8 * c ^ (-(2 / 3 : ℝ))) / r_star ^ 2 :=
            div_le_div_of_nonneg_right hcinv hr2_pos.le
        _ = 8 / r_star ^ 2 * c ^ (-(2 / 3 : ℝ)) := by ring
  have hder_prs_bd : |deriv (fun w => J_rs (p_rs, w)) 0| ≤ C_d * c ^ (-(2 / 3 : ℝ)) := by
    rw [hF_der_eq p_rs hprs_mem]
    have h1 : ‖F_der p_rs‖ ≤ B_Jrs * ‖p_rs - (0, 0)‖ := by simpa [hF00, sub_zero] using hmv_der
    rw [Real.norm_eq_abs] at h1
    calc |F_der p_rs| ≤ B_Jrs * (8 / r_star ^ 2 * c ^ (-(2 / 3 : ℝ))) :=
          h1.trans (mul_le_mul_of_nonneg_left hprs_norm hBJrs_nn)
      _ = C_d * c ^ (-(2 / 3 : ℝ)) := by dsimp only [C_d]; ring
  -- 2. `Q_rs` uniform `JC 8` bound on `Y_Q = (-1/10, 1)`
  let Jrs_dd : (ℝ × ℝ) × ℝ → ℝ := fun q => fderiv ℝ (fun x => fderiv ℝ J_rs x (0, 1)) q (0, 1)
  have hJrs_dd_jc : JC 13 (fctOmegaRs ×ˢ Yint) Jrs_dd B_Jrs := JC.deriv_snd hO_rs hJrs_d14
  have hO_Q : IsOpen (fctOmegaRs ×ˢ Y_Q) := isOpen_fctOmegaRs.prod isOpen_Ioo
  have hUd_Q : UniqueDiffOn ℝ (fctOmegaRs ×ˢ Y_Q) := hO_Q.uniqueDiffOn
  have hUd_Q3 : UniqueDiffOn ℝ ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1) :=
    hUd_Q.prod (uniqueDiffOn_Icc zero_lt_one)
  have hσ_jc : JC 13 ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1) (fun x : ((ℝ × ℝ) × ℝ) × ℝ => x.2) 1 :=
    JC.snd hUd_Q3 le_rfl fun x hx => by
      rw [abs_le]; constructor <;> linarith only [hx.2.1, hx.2.2]
  have hw0_jc : JC 13 (fctOmegaRs ×ˢ Y_Q) (fun q : (ℝ × ℝ) × ℝ => q.2) 1 :=
    JC.snd hUd_Q le_rfl fun q hq => by
      rw [abs_le]; constructor <;> linarith only [hq.2.1, hq.2.2]
  have hw_jc : JC 13 ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1)
      (fun x : ((ℝ × ℝ) × ℝ) × ℝ => x.1.2) ((Nat.factorial 13 : ℝ) * 1) :=
    JC.comp_clm hUd_Q3 hUd_Q (ContinuousLinearMap.fst ℝ ((ℝ × ℝ) × ℝ) ℝ) (norm_fst_le_one _ _)
      (by norm_num : (0 : ℝ) ≤ 1) hw0_jc fun x hx => hx.1
  let L_p : (((ℝ × ℝ) × ℝ) × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).comp (ContinuousLinearMap.fst ℝ ((ℝ × ℝ) × ℝ) ℝ)
  have hLp_n : ‖L_p‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    have h1 := norm_fst_le_one (ℝ × ℝ) ℝ
    have h2 := norm_fst_le_one ((ℝ × ℝ) × ℝ) ℝ
    nlinarith only [h1, h2, norm_nonneg (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ),
      norm_nonneg (ContinuousLinearMap.fst ℝ ((ℝ × ℝ) × ℝ) ℝ)])
  have hmul_σw : JC 13 ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1)
      (fun x : ((ℝ × ℝ) × ℝ) × ℝ => x.2 * x.1.2) bw_Q := by
    have h1 := JC.mul hUd_Q3 zero_le_one (by positivity) hσ_jc hw_jc
    exact h1.mono (le_of_eq (by dsimp only [bw_Q]; ring))
  have hLp_u : ∀ i, 1 ≤ i → i ≤ 13 → ∀ y ∈ ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1),
      ‖iteratedFDerivWithin ℝ i (fun x : ((ℝ × ℝ) × ℝ) × ℝ => L_p x)
        ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1) y‖ ≤ 1 :=
    fun i hi _ y hy => (norm_iteratedFDerivWithin_clm_le hUd_Q3 L_p hi hy).trans hLp_n
  have hQ_comp := JC.comp_pair hUd_Q3 hUd_rs (g := Jrs_dd)
    (u := fun x => L_p x) (w := fun x => x.2 * x.1.2) (b1 := 1) (b2 := bw_Q)
    hBJrs_nn hJrs_dd_jc L_p.contDiff.contDiffOn hmul_σw.1 hLp_u
    (fun i _ hi y hy => hmul_σw.2 i hi y hy)
    (by
      intro x hx
      refine ⟨hx.1.1, ?_⟩
      have hσ := hx.2
      have hw := hx.1.2
      have hlo : -(1 / 5 : ℝ) < x.2 * x.1.2 := by nlinarith only [hσ.1, hσ.2, hw.1, hw.2]
      have hhi : x.2 * x.1.2 < 36 / 10 := by nlinarith only [hσ.1, hσ.2, hw.1, hw.2]
      exact ⟨hlo, hhi⟩)
  have h1mσ : JC 13 ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1)
      (fun x : ((ℝ × ℝ) × ℝ) × ℝ => 1 - x.2) 1 :=
    ((JC.const hUd_Q3 (1 : ℝ)).sub hUd_Q3 hσ_jc).mono (by norm_num)
  have hQ_integrand : JC 13 ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1)
      (fun x : ((ℝ × ℝ) × ℝ) × ℝ => (1 - x.2) * Jrs_dd (x.1.1, x.2 * x.1.2))
      (2 ^ 13 * 1 * (C_comp_Q * B_Jrs)) := by
    refine (JC.mul hUd_Q3 zero_le_one (by positivity) h1mσ hQ_comp).mono ?_
    dsimp only [C_comp_Q]
    exact le_of_eq (by ring)
  let Q_rs : (ℝ × ℝ) × ℝ → ℝ := fun q => ∫ σ in Icc (0 : ℝ) 1, (1 - σ) * Jrs_dd (q.1, σ * q.2)
  have hQ_rs_jc : JC 13 (fctOmegaRs ×ˢ Y_Q) Q_rs (2 ^ 13 * 1 * (C_comp_Q * B_Jrs)) :=
    JC.integral01 hO_Q (f := fun q σ => (1 - σ) * Jrs_dd (q.1, σ * q.2)) hQ_integrand
  have hUd_YQ : UniqueDiffOn ℝ Y_Q := isOpen_Ioo.uniqueDiffOn
  have hQ_p_jc : JC 8 Y_Q (fun w => Q_rs (p_rs, w)) B_Q := by
    have hcomp8 := JC.comp_pair (k := 8) hUd_YQ hUd_Q (g := Q_rs)
      (u := fun _ : ℝ => p_rs) (w := fun t : ℝ => t) (b1 := 1) (b2 := 1)
      (by positivity) (hQ_rs_jc.mono_n (by norm_num)) contDiffOn_const contDiffOn_id
      (fun j hj1 _ t ht => by
        rw [iteratedFDerivWithin_eq_iteratedFDeriv hUd_YQ contDiffAt_const ht,
          iteratedFDeriv_const_of_ne (by omega) p_rs, norm_zero]
        exact zero_le_one)
      (fun j hj1 _ t ht => by
        rw [iteratedFDerivWithin_eq_iteratedFDeriv hUd_YQ contDiffAt_id ht]
        rcases eq_or_lt_of_le hj1 with rfl | hj2
        · simp [norm_one]
        · have hz := iteratedFDeriv_id (𝕜 := ℝ) (F := ℝ) (n := j) t
          simp only [show j ≠ 1 by omega, ↓reduceIte] at hz
          rw [hz, norm_zero]; exact zero_le_one)
      (fun _ ht => ⟨hprs_mem, ht⟩)
    refine hcomp8.mono (le_of_eq ?_)
    have hmax1 : max (1 : ℝ) (max 1 1) = 1 := by norm_num
    rw [hmax1, one_pow, mul_one]
    dsimp only [B_Q]
    ring
  -- 3. `Jrs_dd (p_rs, y) = iteratedDeriv 2 (J_rs (p_rs, ·)) y` on `Yint`, giving Hadamard identity
  have hJrs_dd_eq : ∀ y ∈ Yint, iteratedDeriv 2 (fun t => J_rs (p_rs, t)) y = Jrs_dd (p_rs, y) := by
    intro y hy
    have hder1 : EqOn (deriv (fun t => J_rs (p_rs, t)))
        (fun t => fderiv ℝ J_rs (p_rs, t) (0, 1)) Yint := by
      intro t ht
      have h1 := ((hJrs_jc.1.contDiffAt (hO_rs.mem_nhds ⟨hprs_mem, ht⟩)).differentiableAt
        (by norm_num)).hasFDerivAt
      have h2 : HasDerivAt (fun s : ℝ => (p_rs, s)) (0, 1) t := by
        simpa using (hasDerivAt_const t p_rs).prodMk (hasDerivAt_id t)
      exact (h1.comp_hasDerivAt t h2).deriv
    have hhd : HasDerivAt (fun t => fderiv ℝ J_rs (p_rs, t) (0, 1)) (Jrs_dd (p_rs, y)) y := by
      have h1 := ((hJrs_d14.1.contDiffAt (hO_rs.mem_nhds ⟨hprs_mem, hy⟩)).differentiableAt
        (by norm_num)).hasFDerivAt
      have h2 : HasDerivAt (fun s : ℝ => (p_rs, s)) (0, 1) y := by
        simpa using (hasDerivAt_const y p_rs).prodMk (hasDerivAt_id y)
      exact h1.comp_hasDerivAt y h2
    have hderiv_eq : HasDerivAt (deriv (fun t => J_rs (p_rs, t))) (Jrs_dd (p_rs, y)) y :=
      hhd.congr_of_eventuallyEq ((Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hy) fun t ht => hder1 ht))
    rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv_eq.deriv]
  -- 4. `Q_rs (p_rs, lam * Y(u)) ∈ 𝒮^8_0(C_Q_sym)` on `[0, U_c]`
  let w_fn : ℝ → ℝ := fun u => lam * fctInnerY c u
  have hw_fn_eq : ∀ u : ℝ, w_fn u = lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2 := fun u => by
    dsimp only [w_fn, fctInnerY]; ring
  have hcoef_w_nn : 0 ≤ lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) := by positivity
  have hcoef_w_le : lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) ≤ C_w * c ^ (-(2 / 3 : ℝ)) := by
    have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have hc_eq : c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ)) = c ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    calc lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ))
        ≤ (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) * 1 * c ^ (-(1 / 6 : ℝ)) := by
          dsimp only [lam]; rw [hτ₁_sq_eq]; gcongr
      _ = 1 / r_star ^ 2 * c ^ (-(2 / 3 : ℝ)) := by rw [← hc_eq]; ring
      _ ≤ 2 / r_star ^ 2 * c ^ (-(2 / 3 : ℝ)) := by gcongr; norm_num
  have hw_maps_YQ : ∀ u₀ ∈ Icc 0 (fctUc c), ∀ t ∈ Ioo (-1 : ℝ) 1,
      w_fn (u₀ + (1 + u₀) / 100 * t) ∈ Y_Q := by
    intro u₀ hu₀ t ht
    have hu_nn : 0 ≤ u₀ := hu₀.1
    have hu_le : u₀ ≤ 2.96 * c ^ ((1 : ℝ) / 12) := hu₀.2
    have hc12_1 : 1 ≤ c ^ ((1 : ℝ) / 12) := Real.one_le_rpow (by linarith only [hc100]) (by norm_num)
    have harg_abs : |u₀ + (1 + u₀) / 100 * t| ≤ 4 * c ^ ((1 : ℝ) / 12) := by
      have h1 : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith only [ht.1, ht.2]
      have h2 : |u₀ + (1 + u₀) / 100 * t| ≤ u₀ + (1 + u₀) / 100 := by
        calc |u₀ + (1 + u₀) / 100 * t| ≤ |u₀| + |(1 + u₀) / 100 * t| := abs_add_le _ _
          _ = u₀ + (1 + u₀) / 100 * |t| := by
              rw [abs_of_nonneg hu_nn, abs_mul, abs_of_nonneg (by positivity)]
          _ ≤ u₀ + (1 + u₀) / 100 * 1 := by gcongr
          _ = u₀ + (1 + u₀) / 100 := by ring
      nlinarith only [h2, hu_le, hc12_1]
    have hc16 : (c ^ ((1 : ℝ) / 12)) ^ 2 = c ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
    have hsq : (u₀ + (1 + u₀) / 100 * t) ^ 2 ≤ 16 * c ^ ((1 : ℝ) / 6) := by
      rw [← sq_abs]
      calc |u₀ + (1 + u₀) / 100 * t| ^ 2 ≤ (4 * c ^ ((1 : ℝ) / 12)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) harg_abs 2
        _ = 16 * (c ^ ((1 : ℝ) / 12)) ^ 2 := by ring
        _ = 16 * c ^ ((1 : ℝ) / 6) := by rw [hc16]
    have hlam_w : w_fn (u₀ + (1 + u₀) / 100 * t) ≤ 1 / 10 := by
      rw [hw_fn_eq]
      have hinv : (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) * c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6) =
          c ^ (-(1 / 2 : ℝ)) / r_star ^ 2 := by
        have hc160 : c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6) = 1 := by
          rw [← Real.rpow_add hc0]; norm_num
        calc (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) * c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6)
            = c ^ (-(1 / 2 : ℝ)) / r_star ^ 2 * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6)) := by ring
          _ = c ^ (-(1 / 2 : ℝ)) / r_star ^ 2 := by rw [hc160, mul_one]
      calc lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * (u₀ + (1 + u₀) / 100 * t) ^ 2
          ≤ (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) * 1 * c ^ (-(1 / 6 : ℝ)) * (16 * c ^ ((1 : ℝ) / 6)) := by
            have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
            have hlam_eq : lam = c ^ (-(1 / 2 : ℝ)) / r_star ^ 2 := by dsimp only [lam]; rw [hτ₁_sq_eq]
            rw [hlam_eq]
            gcongr
        _ = 16 * (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) := by
            have hc160 : c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6) = 1 := by
              rw [← Real.rpow_add hc0]; norm_num
            calc (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) * 1 * c ^ (-(1 / 6 : ℝ)) * (16 * c ^ ((1 : ℝ) / 6))
                = 16 * ((c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6))) := by ring
              _ = 16 * (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) := by rw [hc160, mul_one]
        _ ≤ 16 * ((r_star ^ 2 / 161) / r_star ^ 2) := by gcongr
        _ = 16 / 161 := by field_simp [hr2_pos.ne']
        _ ≤ 1 / 10 := by norm_num
    have hw_nn : 0 ≤ w_fn (u₀ + (1 + u₀) / 100 * t) := by
      rw [hw_fn_eq]; exact mul_nonneg hcoef_w_nn (sq_nonneg _)
    exact ⟨by linarith only [hw_nn], by linarith only [hlam_w]⟩
  have hQ_w_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_Q_sym (fun u => ((Q_rs (p_rs, w_fn u) : ℝ) : ℂ)) := by
    have hU_big_open : IsOpen (w_fn ⁻¹' Y_Q) := isOpen_Ioo.preimage (by
      have heq : w_fn = fun u => lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2 := funext hw_fn_eq
      rw [heq]; fun_prop)
    have hsub_big : Icc 0 (fctUc c) ⊆ w_fn ⁻¹' Y_Q := fun u hu => by
      have h0 := hw_maps_YQ u hu 0 ⟨by norm_num, by norm_num⟩
      simpa using h0
    have hcd_real : ContDiffOn ℝ 8 (fun u => Q_rs (p_rs, w_fn u)) (Icc 0 (fctUc c)) := by
      have hw_cd : ContDiffOn ℝ 8 w_fn (Icc 0 (fctUc c)) := by
        have heq : w_fn = fun u => lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2 := funext hw_fn_eq
        rw [heq]; fun_prop
      exact hQ_p_jc.1.comp hw_cd hsub_big
    refine FctSymClsOn.ofReal_cast hDu hcd_real fun r hr u₀ hu₀ => ?_
    let r₀ : ℝ := (1 + u₀) / 100
    have hr₀_pos : 0 < r₀ := by dsimp only [r₀]; linarith only [hu₀.1]
    let w_aff : ℝ → ℝ := fun t => w_fn (u₀ + r₀ * t)
    have hw_aff_cd : ContDiffOn ℝ 8 w_aff (Ioo (-1 : ℝ) 1) := by
      have heq : w_aff = fun t => lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * (u₀ + r₀ * t) ^ 2 := by
        ext t; exact hw_fn_eq _
      rw [heq]; fun_prop
    have hw_aff_jb : ∀ i, 1 ≤ i → i ≤ 8 → ∀ t ∈ Ioo (-1 : ℝ) 1,
        ‖iteratedFDerivWithin ℝ i w_aff (Ioo (-1 : ℝ) 1) t‖ ≤ 1 := by
      intro i hi1 hi8 t ht
      have hcd_all : ContDiff ℝ 8 w_aff := by
        have heq : w_aff = fun s => lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * (u₀ + r₀ * s) ^ 2 := by
          ext s; exact hw_fn_eq _
        rw [heq]; fun_prop
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
        iteratedDerivWithin_of_isOpen isOpen_Ioo ht, Real.norm_eq_abs]
      let k_w : ℝ := lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ))
      have hkw_eq : w_aff = fun s => k_w * (u₀ + r₀ * s) ^ 2 := by ext s; exact hw_fn_eq _
      have h1u : 1 + u₀ ≤ 4 * c ^ ((1 : ℝ) / 12) := by
        have hc12_1 : 1 ≤ c ^ ((1 : ℝ) / 12) := Real.one_le_rpow (by linarith only [hc100]) (by norm_num)
        linarith only [hu₀.2, hc12_1]
      have hkw_c16 : k_w * (1 + u₀) ^ 2 ≤ 16 / 161 := by
        have hc16 : (c ^ ((1 : ℝ) / 12)) ^ 2 = c ^ ((1 : ℝ) / 6) := by
          rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
        have h1u2 : (1 + u₀) ^ 2 ≤ 16 * c ^ ((1 : ℝ) / 6) := by
          calc (1 + u₀) ^ 2 ≤ (4 * c ^ ((1 : ℝ) / 12)) ^ 2 :=
                pow_le_pow_left₀ (by linarith only [hu₀.1]) h1u 2
            _ = 16 * c ^ ((1 : ℝ) / 6) := by rw [mul_pow, hc16]
        have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
        have hlam_eq : lam = c ^ (-(1 / 2 : ℝ)) / r_star ^ 2 := by dsimp only [lam]; rw [hτ₁_sq_eq]
        have hc160 : c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6) = 1 := by
          rw [← Real.rpow_add hc0]; norm_num
        calc k_w * (1 + u₀) ^ 2
            ≤ (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2 * 1 * c ^ (-(1 / 6 : ℝ))) * (16 * c ^ ((1 : ℝ) / 6)) := by
              dsimp only [k_w]; rw [hlam_eq]; gcongr
          _ = 16 * (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) := by
              calc (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2 * 1 * c ^ (-(1 / 6 : ℝ))) * (16 * c ^ ((1 : ℝ) / 6))
                  = 16 * ((c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6))) := by ring
                _ = 16 * (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) := by rw [hc160, mul_one]
          _ ≤ 16 * ((r_star ^ 2 / 161) / r_star ^ 2) := by gcongr
          _ = 16 / 161 := by field_simp [hr2_pos.ne']
      rcases eq_or_lt_of_le hi1 with rfl | hi2
      · rw [iteratedDeriv_one, hkw_eq]
        have hd : deriv (fun s => k_w * (u₀ + r₀ * s) ^ 2) t = 2 * k_w * r₀ * (u₀ + r₀ * t) := by
          have harg : HasDerivAt (fun s => u₀ + r₀ * s) r₀ t := by
            simpa using (hasDerivAt_const t u₀).add ((hasDerivAt_id t).const_mul r₀)
          exact (((harg.pow 2).const_mul k_w).congr_deriv (by ring)).deriv
        rw [hd]
        have harg : |u₀ + r₀ * t| ≤ 1.01 * (1 + u₀) := by
          have ht1 : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith only [ht.1, ht.2]
          calc |u₀ + r₀ * t| ≤ |u₀| + |r₀ * t| := abs_add_le _ _
            _ = u₀ + r₀ * |t| := by rw [abs_of_nonneg hu₀.1, abs_mul, abs_of_pos hr₀_pos]
            _ ≤ u₀ + r₀ * 1 := by gcongr
            _ ≤ 1.01 * (1 + u₀) := by dsimp only [r₀]; linarith only [hu₀.1]
        have hmul : |2 * k_w * r₀ * (u₀ + r₀ * t)| ≤ 2 * k_w * ((1 + u₀) / 100) * (1.01 * (1 + u₀)) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_nonneg (by positivity : 0 ≤ k_w), abs_of_pos hr₀_pos]
          dsimp only [r₀]
          have : 0 ≤ 2 * k_w * ((1 + u₀) / 100) := by positivity
          gcongr
        have halg : 2 * k_w * ((1 + u₀) / 100) * (1.01 * (1 + u₀)) = (2.02 / 100) * (k_w * (1 + u₀) ^ 2) := by
          ring
        linarith only [hmul, halg, hkw_c16]
      · rcases eq_or_lt_of_le (by omega : 2 ≤ i) with rfl | hi3
        · rw [iteratedDeriv_succ, iteratedDeriv_one, hkw_eq]
          have hd1 : deriv (fun s => k_w * (u₀ + r₀ * s) ^ 2) = fun s => 2 * k_w * r₀ * (u₀ + r₀ * s) := by
            ext s
            have harg : HasDerivAt (fun x => u₀ + r₀ * x) r₀ s := by
              simpa using (hasDerivAt_const s u₀).add ((hasDerivAt_id s).const_mul r₀)
            exact (((harg.pow 2).const_mul k_w).congr_deriv (by ring)).deriv
          have hd2 : deriv (fun s => 2 * k_w * r₀ * (u₀ + r₀ * s)) t = 2 * k_w * r₀ ^ 2 := by
            have harg : HasDerivAt (fun x => u₀ + r₀ * x) r₀ t := by
              simpa using (hasDerivAt_const t u₀).add ((hasDerivAt_id t).const_mul r₀)
            exact ((harg.const_mul (2 * k_w * r₀)).congr_deriv (by ring)).deriv
          rw [hd1, hd2, abs_of_nonneg (by positivity)]
          have halg : 2 * k_w * r₀ ^ 2 = (2 / 10000) * (k_w * (1 + u₀) ^ 2) := by dsimp only [r₀]; ring
          linarith only [halg, hkw_c16]
        · have hzero : iteratedDeriv i w_aff t = 0 := by
            rw [hkw_eq]
            let P : Polynomial ℝ := Polynomial.C k_w * (Polynomial.C u₀ + Polynomial.C r₀ * Polynomial.X) ^ 2
            have heval : (fun s => k_w * (u₀ + r₀ * s) ^ 2) = fun s => P.eval s := by
              ext s; simp [P]
            rw [heval]
            have hdeg : P.natDegree < i := by
              have hle2 : P.natDegree ≤ 2 := by
                calc P.natDegree ≤ (Polynomial.C k_w).natDegree +
                      ((Polynomial.C u₀ + Polynomial.C r₀ * Polynomial.X) ^ 2).natDegree :=
                        Polynomial.natDegree_mul_le
                  _ = ((Polynomial.C u₀ + Polynomial.C r₀ * Polynomial.X) ^ 2).natDegree := by simp
                  _ ≤ 2 * (Polynomial.C u₀ + Polynomial.C r₀ * Polynomial.X).natDegree :=
                        Polynomial.natDegree_pow_le
                  _ ≤ 2 * 1 := by
                        gcongr
                        exact (Polynomial.natDegree_add_le _ _).trans (by
                          simp only [Polynomial.natDegree_C, zero_max]
                          exact (Polynomial.natDegree_mul_le).trans (by simp))
                  _ = 2 := by ring
              omega
            simp [Polynomial.iteratedDeriv_eval_eq_zero_of_natDegree_lt hdeg]
          rw [hzero, abs_zero]; exact zero_le_one
    have hQ_jb := JB.comp (k := 8) isOpen_Ioo.uniqueDiffOn hUd_YQ hQ_p_jc.1 hw_aff_cd
      (fun t ht => hw_maps_YQ u₀ hu₀ t ht) (by positivity)
      (fun w hw j hj => hQ_p_jc.2 j hj w hw) hw_aff_jb
    have h0_mem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hle := hQ_jb r hr 0 h0_mem
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, Real.norm_eq_abs, max_self, one_pow, mul_one,
      iteratedDerivWithin_of_isOpen isOpen_Ioo h0_mem] at hle
    have haff_rel : iteratedDeriv r (fun t => Q_rs (p_rs, w_aff t)) 0 =
        r₀ ^ r * iteratedDerivWithin r (fun u => Q_rs (p_rs, w_fn u)) (Icc 0 (fctUc c)) u₀ := by
      have hcd_big : ContDiffOn ℝ 8 (fun u => Q_rs (p_rs, w_fn u)) (w_fn ⁻¹' Y_Q) := by
        have hw_big : ContDiffOn ℝ 8 w_fn (w_fn ⁻¹' Y_Q) := by
          have heq : w_fn = fun u => lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2 := funext hw_fn_eq
          rw [heq]; fun_prop
        exact hQ_p_jc.1.comp hw_big fun u hu => hu
      have h0_big : u₀ ∈ w_fn ⁻¹' Y_Q := hsub_big hu₀
      let Pre_U : Set ℝ := (fun s : ℝ => u₀ + r₀ * s) ⁻¹' (w_fn ⁻¹' Y_Q)
      have hPre_open : IsOpen Pre_U := hU_big_open.preimage (by fun_prop)
      have h0_pre : (0 : ℝ) ∈ Pre_U := by simpa [Pre_U] using h0_big
      have hcomp_big := iteratedDerivWithin_comp_affine hU_big_open.uniqueDiffOn hPre_open.uniqueDiffOn
        hcd_big hr (v := 0) (by simpa using h0_big)
      change iteratedDerivWithin r (fun t => Q_rs (p_rs, w_aff t)) Pre_U 0 =
        r₀ ^ r • iteratedDerivWithin r (fun u => Q_rs (p_rs, w_fn u)) (w_fn ⁻¹' Y_Q) (u₀ + r₀ * 0) at hcomp_big
      rw [iteratedDerivWithin_of_isOpen hPre_open h0_pre, mul_zero, add_zero, smul_eq_mul,
        iteratedDerivWithin_of_isOpen hU_big_open h0_big] at hcomp_big
      rw [hcomp_big, iteratedDerivWithin_eq_iteratedDeriv hDu
        ((hcd_big.contDiffAt (hU_big_open.mem_nhds h0_big)).of_le (by exact_mod_cast hr)) hu₀]
    rw [haff_rel, abs_mul, abs_pow, abs_of_pos hr₀_pos] at hle
    have hr0_inv : (r₀ ^ r)⁻¹ = 100 ^ r * (1 + u₀) ^ ((0 : ℝ) - r) := by
      have h1p : 0 < 1 + u₀ := by linarith only [hu₀.1]
      dsimp only [r₀]
      rw [div_pow, inv_div, ← Real.rpow_natCast (1 + u₀) r, Real.rpow_sub h1p, Real.rpow_zero, one_div]
      ring
    calc |iteratedDerivWithin r (fun u => Q_rs (p_rs, w_fn u)) (Icc 0 (fctUc c)) u₀|
        ≤ ((Nat.factorial 8 : ℝ) * B_Q) / r₀ ^ r := (le_div_iff₀ (pow_pos hr₀_pos r)).mpr (by linarith only [hle])
      _ = ((Nat.factorial 8 : ℝ) * B_Q) * (100 ^ r * (1 + u₀) ^ ((0 : ℝ) - r)) := by
          rw [div_eq_mul_inv, hr0_inv]
      _ ≤ 100 ^ 8 * ((Nat.factorial 8 : ℝ) * B_Q) * (1 + u₀) ^ ((0 : ℝ) - r) := by
          have h100r : (100 : ℝ) ^ r ≤ 100 ^ 8 := pow_le_pow_right₀ (by norm_num) hr
          have hB_pos : 0 ≤ (Nat.factorial 8 : ℝ) * B_Q := by positivity
          have hpow_pos : 0 ≤ (1 + u₀) ^ ((0 : ℝ) - r) := by positivity
          calc ((Nat.factorial 8 : ℝ) * B_Q) * (100 ^ r * (1 + u₀) ^ ((0 : ℝ) - r))
              = 100 ^ r * ((Nat.factorial 8 : ℝ) * B_Q) * (1 + u₀) ^ ((0 : ℝ) - r) := by ring
            _ ≤ 100 ^ 8 * ((Nat.factorial 8 : ℝ) * B_Q) * (1 + u₀) ^ ((0 : ℝ) - r) := by gcongr
  -- 5. Combine linear + quadratic pieces via `FctSymClsOn`
  have hw_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 2 (C_w * c ^ (-(2 / 3 : ℝ)))
      (fun u => ((w_fn u : ℝ) : ℂ)) := by
    let k_w : ℝ := lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ))
    have hsc := (fctInner_u_sq_sym hc0).const_mul hDu (k_w : ℂ)
    have hnorm_kw : ‖(k_w : ℂ)‖ * 2 = 2 * k_w := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef_w_nn]; ring
    have hle : ‖(k_w : ℂ)‖ * 2 ≤ C_w * c ^ (-(2 / 3 : ℝ)) := by
      rw [hnorm_kw]
      have hc_eq : c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ)) = c ^ (-(2 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
      have hlam_eq : lam = c ^ (-(1 / 2 : ℝ)) / r_star ^ 2 := by dsimp only [lam]; rw [hτ₁_sq_eq]
      calc 2 * k_w = 2 * (lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ))) := rfl
        _ ≤ 2 * (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2 * 1 * c ^ (-(1 / 6 : ℝ))) := by rw [hlam_eq]; gcongr
        _ = C_w * c ^ (-(2 / 3 : ℝ)) := by dsimp only [C_w]; rw [← hc_eq]; ring
    refine (hsc.mono_B Icc_subset_Ici_self hle).congr hDu fun u _ => ?_
    rw [hw_fn_eq]; push_cast; ring
  have hlin_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C_lin * c ^ (-(4 / 3 : ℝ)))
      (fun u => ((deriv (fun w => J_rs (p_rs, w)) 0 * w_fn u : ℝ) : ℂ)) := by
    let d_lin : ℝ := deriv (fun w => J_rs (p_rs, w)) 0
    have hsc := hw_sym.const_mul hDu (d_lin : ℂ)
    have hle : ‖(d_lin : ℂ)‖ * (C_w * c ^ (-(2 / 3 : ℝ))) ≤ C_lin * c ^ (-(4 / 3 : ℝ)) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hcexp : c ^ (-(2 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      calc |d_lin| * (C_w * c ^ (-(2 / 3 : ℝ)))
          ≤ (C_d * c ^ (-(2 / 3 : ℝ))) * (C_w * c ^ (-(2 / 3 : ℝ))) := by gcongr; exact hder_prs_bd
        _ = C_lin * c ^ (-(4 / 3 : ℝ)) := by dsimp only [C_lin]; rw [← hcexp]; ring
    refine ((hsc.mono_B Icc_subset_Ici_self hle).mono_p Icc_subset_Ici_self (by positivity)
      (by norm_num)).congr hDu fun u _ => ?_
    push_cast; rfl
  have hquad_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C_quad * c ^ (-(4 / 3 : ℝ)))
      (fun u => ((w_fn u ^ 2 * Q_rs (p_rs, w_fn u) : ℝ) : ℂ)) := by
    have hw2 := hw_sym.mul Icc_subset_Ici_self hDu hw_sym
    have hcexp : c ^ (-(2 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    have hw2_bd : 2 ^ 8 * (C_w * c ^ (-(2 / 3 : ℝ))) * (C_w * c ^ (-(2 / 3 : ℝ))) =
        2 ^ 8 * C_w * C_w * c ^ (-(4 / 3 : ℝ)) := by
      rw [← hcexp]; ring
    have hw2' := hw2.mono_B Icc_subset_Ici_self hw2_bd.le
    have hmul := hw2'.mul Icc_subset_Ici_self hDu hQ_w_sym
    have hmul_eq : 2 ^ 8 * (2 ^ 8 * C_w * C_w * c ^ (-(4 / 3 : ℝ))) * C_Q_sym =
        C_quad * c ^ (-(4 / 3 : ℝ)) := by
      dsimp only [C_quad]; ring
    refine ((hmul.mono_B Icc_subset_Ici_self hmul_eq.le).mono_p Icc_subset_Ici_self (by positivity)
      (by norm_num)).congr hDu fun u _ => ?_
    push_cast; ring
  have hsum := hlin_sym.add hDu hquad_sym
  have hsum_eq : C_lin * c ^ (-(4 / 3 : ℝ)) + C_quad * c ^ (-(4 / 3 : ℝ)) = C_tot * c ^ (-(4 / 3 : ℝ)) := by
    dsimp only [C_tot]; ring
  refine (hsum.mono_B Icc_subset_Ici_self hsum_eq.le).congr hDu fun u hu => ?_
  have hY_mem : fctInnerY c u ∈ Icc (0 : ℝ) 3.5 := fctInnerY_mem_35 (by linarith only [hc100]) hu
  have hscale := Jfun_scale_eq hr_pos hSrs_Ω hSrs_ℓ hSrs_r h15rs hτ₁_pos hTmt rfl
    hSΩ hSℓ hSr hp0_mem hlam_pos hlam_16 hprs_mem hR_small (fctInnerY c u) hY_mem
  have hw_YQ : w_fn u ∈ Y_Q := by
    have h0 := hw_maps_YQ u hu 0 ⟨by norm_num, by norm_num⟩
    simpa using h0
  have hw_Yint : w_fn u ∈ Yint := ⟨by linarith only [hw_YQ.1], by linarith only [hw_YQ.2]⟩
  have hhad := hadamard_second_order (hJrs_w_cd.of_le (by norm_num)) (hJrs_0 p_rs hprs_mem) hw_Yint
  have hint_eq : ∫ σ in Icc (0 : ℝ) 1, (1 - σ) * iteratedDeriv 2 (fun t => J_rs (p_rs, t)) (σ * w_fn u) =
      Q_rs (p_rs, w_fn u) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    have hσw_Yint : σ * w_fn u ∈ Yint := by
      have h1 : -(1 / 10 : ℝ) < σ * w_fn u := by nlinarith only [hσ.1, hσ.2, hw_YQ.1, hw_YQ.2]
      have h2 : σ * w_fn u < 1 := by nlinarith only [hσ.1, hσ.2, hw_YQ.1, hw_YQ.2]
      exact ⟨by linarith only [h1], by linarith only [h2]⟩
    rw [hJrs_dd_eq (σ * w_fn u) hσw_Yint]
  have hval : Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), fctInnerY c u) - 1 =
      deriv (fun w => J_rs (p_rs, w)) 0 * w_fn u + w_fn u ^ 2 * Q_rs (p_rs, w_fn u) := by
    rw [hscale]
    change J_rs (p_rs, w_fn u) - 1 = _
    rw [← hint_eq]
    linarith only [hhad]
  rw [hval]
  push_cast
  ring

/-- info: 'FormalResearch.SignUncertainty.fctInner_J0_sub_one_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInner_J0_sub_one_sym

end FormalResearch.SignUncertainty
