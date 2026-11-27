module

public import Mathlib
public import FormalResearch.SignUncertainty.CtRoscBookProof
public import FormalResearch.SignUncertainty.CtDyadicCombined

/-!
# `ct:dyadic` (4), `window` Step W2 and positive half-moment

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:dyadic` (4) (sub-chart truncation `ξ ≤ ξ(φ_c(R))`)
and Step 1c (positive-side half-moment on `[0, φ_c(R)]`).

* `integral_Iic_abs_hankelHL_eq`: for `ξ₀ > 0`, `∫_{L ≤ log(π²ξ₀)} |h(L)| dL = ∫_{0 < u ≤ cξ₀} |f(u)| ρ₀(u) du`.
* `hankel_subchart_tail_le`: `L_pos < ctTaperLam ε c R` and `|∫_{L ≤ L_pos} K_ε h| ≤ c^{-4/3}` for large `c`.
* `psiR_pos_half_moment_le`: `∫_0^{φ_c(R)} (1+x)^{1/2} |Re Ψ̃(x)| dx ≤ 3 log c` for large `c`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

lemma integral_Iic_abs_hankelHL_eq {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (_hf : IsHankelEigenfn c ε f)
    {ξ₀ : ℝ} (hξ : 0 < ξ₀) :
    ∫ L in Iic (Real.log (π ^ 2 * ξ₀)), |hankelHL c f L| =
      ∫ u in Ioc 0 (c * ξ₀), |f u| * hankelRho0 c u := by
  have hpi : (0 : ℝ) < π ^ 2 := by positivity
  set φ : ℝ → ℝ := fun L => Real.exp L / π ^ 2 with hφ
  have himg : φ '' univ = Ioi 0 := by
    ext ξ
    simp only [mem_image, mem_univ, true_and, mem_Ioi, hφ]
    constructor
    · rintro ⟨L, rfl⟩; positivity
    · intro hξ'
      refine ⟨Real.log (π ^ 2 * ξ), ?_⟩
      rw [Real.exp_log (by positivity)]; field_simp
  have hd : ∀ L ∈ (univ : Set ℝ), HasDerivWithinAt φ (Real.exp L / π ^ 2) univ L :=
    fun L _ => ((Real.hasDerivAt_exp L).div_const _).hasDerivWithinAt
  have hinj : InjOn φ univ := by
    intro a _ b _ hab
    simp only [hφ] at hab
    exact Real.exp_injective ((div_left_inj₀ hpi.ne').1 hab)
  set G : ℝ → ℝ := fun ξ => (Iic ξ₀).indicator (fun _ => (1 : ℝ)) ξ * |hankelDmDens c f ξ| with hG
  have key := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hinj G
  rw [himg, setIntegral_univ] at key
  have hL_eq : (fun L : ℝ => |Real.exp L / π ^ 2| • G (φ L)) =
      (Iic (Real.log (π ^ 2 * ξ₀))).indicator (fun L => |hankelHL c f L|) := by
    funext L
    have hp : 0 < Real.exp L / π ^ 2 := by positivity
    have hiff : Real.exp L / π ^ 2 ≤ ξ₀ ↔ L ≤ Real.log (π ^ 2 * ξ₀) := by
      rw [div_le_iff₀ hpi, Real.le_log_iff_exp_le (by positivity)]
      constructor <;> intro h <;> linarith
    have hrho := hankelRho0_nonneg hc (by positivity : 0 ≤ c * (Real.exp L / π ^ 2))
    simp only [smul_eq_mul, G, hφ, hankelHL, hankelDmDens, abs_of_pos hp, Set.indicator]
    split_ifs with h1 h2 h2
    · simp only [one_mul, abs_mul, abs_of_pos hp, abs_of_pos hc, abs_of_nonneg hrho]
      ring
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · simp
  rw [hL_eq, integral_indicator measurableSet_Iic] at key
  have hξ_eq : ∫ ξ in Ioi (0 : ℝ), G ξ = ∫ ξ in Ioc 0 ξ₀, |hankelDmDens c f ξ| := by
    have hsub : Ioi (0 : ℝ) ∩ Ioc 0 ξ₀ = Ioc 0 ξ₀ := Set.inter_eq_right.2 fun _ hx => hx.1
    calc ∫ ξ in Ioi (0 : ℝ), G ξ
        = ∫ ξ in Ioi (0 : ℝ), (Ioc 0 ξ₀).indicator (fun ξ => |hankelDmDens c f ξ|) ξ := by
          refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ' => ?_
          have hmem : ξ ∈ Iic ξ₀ ↔ ξ ∈ Ioc 0 ξ₀ := by simp [mem_Iic, mem_Ioc, mem_Ioi.1 hξ']
          simp only [G, Set.indicator]
          split_ifs with h1 h2 h2
          · rw [one_mul]
          · exact absurd (hmem.1 h1) h2
          · exact absurd (hmem.2 h2) h1
          · exact zero_mul _
      _ = ∫ ξ in Ioc 0 ξ₀, |hankelDmDens c f ξ| := by
          rw [setIntegral_indicator measurableSet_Ioc, hsub]
  rw [← key, hξ_eq, ← intervalIntegral.integral_of_le hξ.le]
  have hsub := intervalIntegral.integral_comp_mul_left (fun u => |f u| * hankelRho0 c u) (a := (0 : ℝ)) (b := ξ₀) (c := c)
  simp only [mul_zero, smul_eq_mul] at hsub
  have hcongr : ∫ x in (0 : ℝ)..ξ₀, |hankelDmDens c f x| =
      c * ∫ x in (0 : ℝ)..ξ₀, |f (c * x)| * hankelRho0 c (c * x) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun ξ hξ' => ?_
    rw [uIcc_of_le hξ.le] at hξ'
    have hrho := hankelRho0_nonneg hc (mul_nonneg hc.le hξ'.1)
    unfold hankelDmDens
    rw [abs_mul, abs_mul, abs_of_pos hc, abs_of_nonneg hrho]
  rw [hcongr, hsub hc.ne', ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul, intervalIntegral.integral_of_le (by positivity)]

/-- **W2 (Sub-chart truncation)** (`ct:dyadic` (4)): for `0 < c₁ ≤ ctChartC1` and `c` large, at any `R ∈ [c₁² c^{2/3}, 4 c₁² c^{2/3}]`:
1. `L_pos := log(π² ξ(φ_c(R))) < ctTaperLam ε c R`, and
2. `|∫_{L ≤ L_pos} K_ε(e^L/π²) h(L) dL| ≤ c^{-4/3}`. -/
theorem hankel_subchart_tail_le {c₁ : ℝ} (hc₁ : 0 < c₁) (hle : c₁ ≤ ctChartC1) :
    ∃ c₀ : ℝ, ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ c : ℝ, c₀ ≤ c →
      ∀ f : ℝ → ℝ, IsHankelEigenfn c ε f → hankelMass c f = 1 →
        ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) →
          Real.log (π ^ 2 * hankelXi c (ctPhiR ε c R)) < ctTaperLam ε c R ∧
            |∫ L in Iic (Real.log (π ^ 2 * hankelXi c (ctPhiR ε c R))),
              CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L| ≤ c ^ (-(4 / 3 : ℝ)) := by
  obtain ⟨C₂, c₀₂, hC₂, hbody₂, hwin₂⟩ := ct_rosc_setup
  obtain ⟨ρ₁, M₁, hW₁, hν₁⟩ := hwin₂ 1 (Or.inl rfl)
  obtain ⟨ρ₂, M₂, hW₂, hν₂⟩ := hwin₂ (-1) (Or.inr rfl)
  obtain ⟨Kb₁, hKb₁, hdual₁⟩ := CtDual.ct_dual_id_part2 (Or.inl rfl)
  obtain ⟨Kb₂, hKb₂, hdual₂⟩ := CtDual.ct_dual_id_part2 (Or.inr rfl)
  set Kb := max Kb₁ Kb₂ with hKb
  have hKb_nn : 0 ≤ Kb := le_max_of_le_left hKb₁
  set bexp := 5 * (langerLobeK * c₁ ^ 2 / 2) ^ (3 / 2 : ℝ) with hbexp
  have hb : 0 < langerLobeK * c₁ ^ 2 / 2 := by have := langerLobeK_pos; positivity
  have hbexp_pos : 0 < bexp := by positivity
  have hev : ∀ᶠ c : ℝ in atTop,
      c₀₂ ≤ c ∧ 3e6 ≤ c ∧ 2 * M₁ ≤ c ∧ (2 * M₁) ^ 3 ≤ c ∧ 2 * M₂ ≤ c ∧ (2 * M₂) ^ 3 ≤ c ∧
      C₂ * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 ∧ 2 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) ∧
      2 * C₂ * c ^ (-(1 / 3 : ℝ)) ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) / 2 ∧
      1 ≤ (langerLobeK * c₁ ^ 2 / 2) * c ^ (2 / 3 : ℝ) ∧
      16 * (Kb + 1) * Real.exp (-bexp * c ^ (5 / 6 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) ∧
      16 * (Kb + 1) * Real.exp (-(1 / 25) * c) ≤ c ^ (-(4 / 3 : ℝ)) ∧
      1 ≤ c ^ (1 / 6 : ℝ) := by
    have hr1 : ∀ᶠ c : ℝ in atTop, 16 * (Kb + 1) * Real.exp (-bexp * c ^ (5 / 6 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) := by
      have := (tendsto_rpow_exp_rpow hbexp_pos).const_mul (16 * (Kb + 1))
      rw [mul_zero] at this
      filter_upwards [this.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_gt_atTop 0] with c hc hc0
      have hpos : 0 < c ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
      rw [Real.rpow_neg hc0.le, ← one_div, le_div_iff₀ hpos]
      linarith
    have hr2 : ∀ᶠ c : ℝ in atTop, 16 * (Kb + 1) * Real.exp (-(1 / 25) * c) ≤ c ^ (-(4 / 3 : ℝ)) := by
      have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 / 3 : ℝ) (1 / 25) (by norm_num)).const_mul (16 * (Kb + 1))
      rw [mul_zero] at this
      filter_upwards [this.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_gt_atTop 0] with c hc hc0
      have hpos : 0 < c ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
      rw [Real.rpow_neg hc0.le, ← one_div, le_div_iff₀ hpos]
      linarith
    filter_upwards [eventually_ge_atTop c₀₂, eventually_ge_atTop (3e6 : ℝ),
      eventually_ge_atTop (2 * M₁), eventually_ge_atTop ((2 * M₁) ^ 3),
      eventually_ge_atTop (2 * M₂), eventually_ge_atTop ((2 * M₂) ^ 3),
      eventually_rpow_neg_le (by norm_num : (0 : ℝ) < 1 / 3) C₂ (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_rpow_ge (by norm_num : (0 : ℝ) < 2 / 3) (by positivity : 0 < c₁ ^ 2) 2,
      eventually_rpow_neg_le (by norm_num : (0 : ℝ) < 1 / 3) (4 * C₂ + 1) (by positivity : 0 < c₁ ^ 2 / 2),
      eventually_rpow_ge (by norm_num : (0 : ℝ) < 2 / 3) (by positivity : 0 < c₁ ^ 2 / 2) 1,
      eventually_rpow_ge (by norm_num : (0 : ℝ) < 2 / 3) hb 1, hr1, hr2, eventually_ge_atTop (1 : ℝ)]
      with c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, h11, h12, h13, ?_⟩
    · have hc0 : 0 < c := by linarith
      have hc23 : 1 ≤ c ^ (2 / 3 : ℝ) := Real.one_le_rpow h14 (by norm_num)
      have hnn : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
      have ha : 2 * C₂ * c ^ (-(1 / 3 : ℝ)) ≤ (c₁ ^ 2 / 2) * 1 := by nlinarith
      nlinarith [show (0 : ℝ) ≤ c₁ ^ 2 / 2 by positivity]
    · exact Real.one_le_rpow h14 (by norm_num)
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.1 hev
  refine ⟨max c₀ 2, fun ε hε c hc f hf hM R hR => ?_⟩
  obtain ⟨hc₀₂, hc3, h2M1, h2M1_3, h2M2, h2M2_3, hsm, hR2, hC2R, hk_lb, hexp1, hexp2, hc16⟩ :=
    hc₀ c ((le_max_left _ _).trans hc)
  have hc2 : 2 ≤ c := le_max_right c₀ 2 |>.trans hc
  have hc0 : 0 < c := by linarith
  have hbody' := hbody₂ ε hε c hc₀₂
  have hH : CtRealChartHyp ε c C₂ := ⟨hbody', hC₂, hc3, hsm⟩
  have hWin : ∃ ρ M, CtWinHyp ε c ρ M := by
    have hlam : ∀ M, 0 ≤ M → (2 * M) ^ 3 ≤ c → ctLam c * M ≤ 1 / 2 := fun M hM0 hM3 => by
      have hl := ctLam_le hc0
      have h13 : 2 * M ≤ c ^ (1 / 3 : ℝ) := by
        have := Real.rpow_le_rpow (by positivity) hM3 (by norm_num : (0 : ℝ) ≤ 1 / 3)
        rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num,
          Real.rpow_one] at this
      have hp : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
      calc ctLam c * M ≤ (c ^ (1 / 3 : ℝ))⁻¹ * M := mul_le_mul_of_nonneg_right hl hM0
        _ ≤ 1 / 2 := by rw [inv_mul_le_iff₀ hp]; linarith
    rcases hε with rfl | rfl
    · exact ⟨ρ₁, M₁, hW₁, h2M1, hlam M₁ hW₁.2.1 h2M1_3, by rw [ctMu_mul_ctRmax hc0]; exact hν₁⟩
    · exact ⟨ρ₂, M₂, hW₂, h2M2, hlam M₂ hW₂.2.1 h2M2_3, by rw [ctMu_mul_ctRmax hc0]; exact hν₂⟩
  obtain ⟨ρ, M, hW⟩ := hWin
  have hRm : R ≤ ctRmax ctChartC1 c := hR.2.trans (ctRmax_mono hc0.le hc₁.le hle)
  have hR1 : 1 < R := lt_of_lt_of_le (by linarith) hR.1
  have hRp := ctRprime_bounds hH hW hR1 hRm
  have ha_abs : |ctPhiR ε c R| < langerRadius c :=
    hH.abs_ctPhiR_lt (u := R) (by rw [abs_of_pos (by linarith only [hR1])]; exact hRm)
  have ha_lb : R / 2 ≤ ctPhiR ε c R := by
    have h := (abs_le.1 (hH.abs_ctPhiR_sub_le (u := R) (by rw [abs_of_pos (by linarith only [hR1])]; exact hRm))).1
    have hC_half : C₂ * c ^ (-(1 / 3 : ℝ)) ≤ R / 2 := by linarith only [hC2R, hR.1, hR2]
    linarith only [h, hC_half]
  have ha0 : 0 < ctPhiR ε c R := by linarith only [ha_lb, hR1]
  have hk : 1 ≤ langerLobeK * ctPhiR ε c R := by
    have h1 : c₁ ^ 2 * c ^ (2 / 3 : ℝ) / 2 ≤ ctPhiR ε c R := by linarith only [ha_lb, hR.1]
    calc (1 : ℝ) ≤ (langerLobeK * c₁ ^ 2 / 2) * c ^ (2 / 3 : ℝ) := hk_lb
      _ = langerLobeK * (c₁ ^ 2 * c ^ (2 / 3 : ℝ) / 2) := by ring
      _ ≤ langerLobeK * ctPhiR ε c R := mul_le_mul_of_nonneg_left h1 langerLobeK_pos.le
  have hAlt : ctRmax ctChartC1 c < langerRadius c := by
    have := hH.Rm_add_lt
    have hpos_c : 0 ≤ C₂ * c ^ (-(1 / 3 : ℝ)) := mul_nonneg hC₂ (Real.rpow_nonneg hc0.le _)
    linarith only [this, hpos_c]
  have hrA : |-ctRprime ε c R| ≤ langerRadius c := by
    rw [abs_neg, abs_of_nonneg (by linarith only [hRp.1])]
    exact (hRp.2.1.trans hRm).trans hAlt.le
  have hL_lt : Real.log (π ^ 2 * hankelXi c (ctPhiR ε c R)) < ctTaperLam ε c R := by
    have hxi1 : 0 < hankelXi c (ctPhiR ε c R) := hankelXi_pos hc0 ha_abs.le
    have hxi_lt : hankelXi c (ctPhiR ε c R) < hankelXi c (-ctRprime ε c R) := by
      have hanti : StrictAntiOn (hankelXi c) (Icc (-ctRprime ε c R) (ctPhiR ε c R)) :=
        strictAntiOn_of_deriv_neg (convex_Icc _ _)
          (fun x hx => (hasDerivAt_hankelXi hc0 (abs_le.2 ⟨by linarith only [hx.1, (abs_le.1 hrA).1],
            by linarith only [hx.2, (abs_le.1 ha_abs.le).2]⟩)).continuousAt.continuousWithinAt)
          (fun x hx => by
            rw [interior_Icc] at hx
            have hx_abs : |x| ≤ langerRadius c := abs_le.2 ⟨by linarith only [hx.1, (abs_le.1 hrA).1],
              by linarith only [hx.2, (abs_le.1 ha_abs.le).2]⟩
            rw [(hasDerivAt_hankelXi hc0 hx_abs).deriv]
            exact hankelXiD_neg hc0 hx_abs)
      exact hanti ⟨le_rfl, by linarith only [hRp.1, ha0]⟩ ⟨by linarith only [hRp.1, ha0], le_rfl⟩
        (by linarith only [hRp.1, ha0])
    unfold ctTaperLam
    refine Real.log_lt_log (by positivity) ?_
    exact mul_lt_mul_of_pos_left hxi_lt (by positivity)
  refine ⟨hL_lt, ?_⟩
  set L_pos := Real.log (π ^ 2 * hankelXi c (ctPhiR ε c R)) with hLpos
  have hint_full : Integrable (fun L => CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L) :=
    integrable_dualK_hankelHL hc2 hε hf
  have hint_L : IntegrableOn (fun L => CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L) (Iic L_pos) :=
    hint_full.integrableOn
  have hKbd : ∀ ξ : ℝ, 0 < ξ → |CtDual.dualK ε c ξ| ≤ Kb := fun ξ hξ => by
    rcases hε with rfl | rfl
    · exact ((hdual₁ hc2).1 ξ hξ).2.trans (le_max_left _ _)
    · exact ((hdual₂ hc2).1 ξ hξ).2.trans (le_max_right _ _)
  have hint_abs : IntegrableOn (fun L => Kb * |hankelHL c f L|) (Iic L_pos) :=
    (((integrable_hankelHL hc0 hf).abs).integrableOn).const_mul Kb
  have hpt : ∀ L : ℝ, |CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L| ≤ Kb * |hankelHL c f L| := fun L => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hKbd _ (by positivity)) (abs_nonneg _)
  have hbd1 : |∫ L in Iic L_pos, CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L| ≤
      Kb * ∫ L in Iic L_pos, |hankelHL c f L| := by
    calc _ ≤ ∫ L in Iic L_pos, |CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ L in Iic L_pos, Kb * |hankelHL c f L| :=
          integral_mono hint_L.abs hint_abs hpt
      _ = Kb * ∫ L in Iic L_pos, |hankelHL c f L| := integral_const_mul _ _
  have hxi_pos : 0 < hankelXi c (ctPhiR ε c R) := hankelXi_pos hc0 ha_abs.le
  rw [hLpos, integral_Iic_abs_hankelHL_eq hc0 hf hxi_pos] at hbd1
  have hlobe := deep_lobe_at hc3 hf hε hM ha0.le (abs_le.1 ha_abs.le).2 hk
  have hcexp : (c₁ ^ 2 / 2) ^ (3 / 2 : ℝ) * c ^ (5 / 6 : ℝ) ≤ ctPhiR ε c R ^ (3 / 2 : ℝ) := by
    have h1 : (c₁ ^ 2 / 2) * c ^ (2 / 3 : ℝ) ≤ ctPhiR ε c R := by linarith only [ha_lb, hR.1]
    have h2 : ((c₁ ^ 2 / 2) * c ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) ≤ ctPhiR ε c R ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : ((c₁ ^ 2 / 2) * c ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = (c₁ ^ 2 / 2) ^ (3 / 2 : ℝ) * c := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hc0.le _), ← Real.rpow_mul hc0.le]; norm_num
    have h4 : c ^ (5 / 6 : ℝ) ≤ c := by
      calc c ^ (5 / 6 : ℝ) ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith only [hc3]) (by norm_num)
        _ = c := Real.rpow_one c
    rw [h3] at h2
    have h5 : (c₁ ^ 2 / 2) ^ (3 / 2 : ℝ) * c ^ (5 / 6 : ℝ) ≤ (c₁ ^ 2 / 2) ^ (3 / 2 : ℝ) * c :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    exact h5.trans h2
  have hexp_mon : Real.exp (-5 * (langerLobeK * ctPhiR ε c R) ^ (3 / 2 : ℝ)) ≤
      Real.exp (-bexp * c ^ (5 / 6 : ℝ)) := by
    refine Real.exp_le_exp.2 ?_
    have hm : (langerLobeK * ctPhiR ε c R) ^ (3 / 2 : ℝ) =
        langerLobeK ^ (3 / 2 : ℝ) * ctPhiR ε c R ^ (3 / 2 : ℝ) :=
      Real.mul_rpow langerLobeK_pos.le ha0.le
    have h1 : (langerLobeK * c₁ ^ 2 / 2) ^ (3 / 2 : ℝ) =
        langerLobeK ^ (3 / 2 : ℝ) * (c₁ ^ 2 / 2) ^ (3 / 2 : ℝ) := by
      rw [show langerLobeK * c₁ ^ 2 / 2 = langerLobeK * (c₁ ^ 2 / 2) by ring]
      exact Real.mul_rpow langerLobeK_pos.le (by positivity)
    rw [hm, hbexp, h1]
    have hpos_lk : 0 ≤ 5 * langerLobeK ^ (3 / 2 : ℝ) := by have := langerLobeK_pos; positivity
    have hmul := mul_le_mul_of_nonneg_left hcexp hpos_lk
    linarith only [hmul]
  calc _ ≤ Kb * (8 * (Real.exp (-5 * (langerLobeK * ctPhiR ε c R) ^ (3 / 2 : ℝ)) + Real.exp (-(1 / 25) * c))) :=
        hbd1.trans (mul_le_mul_of_nonneg_left hlobe hKb_nn)
    _ ≤ (Kb + 1) * (8 * (Real.exp (-bexp * c ^ (5 / 6 : ℝ)) + Real.exp (-(1 / 25) * c))) := by
        gcongr; linarith only
    _ = 1 / 2 * (16 * (Kb + 1) * Real.exp (-bexp * c ^ (5 / 6 : ℝ))) +
        1 / 2 * (16 * (Kb + 1) * Real.exp (-(1 / 25) * c)) := by ring
    _ ≤ 1 / 2 * c ^ (-(4 / 3 : ℝ)) + 1 / 2 * c ^ (-(4 / 3 : ℝ)) := by gcongr
    _ = c ^ (-(4 / 3 : ℝ)) := by ring

/-- **Positive-side half-moment** (part of `window` Step W4): on `[0, φ_c(R)]`,
`∫_0^{φ_c(R)} (1 + x)^{1/2} |Re Ψ̃(x)| dx ≤ 3 log c` for small `c₁` and large `c`. -/
theorem psiR_pos_half_moment_le {c₁ : ℝ} (hc₁ : 0 < c₁) (hle : c₁ ≤ ctChartC1) :
    ∃ c₀ : ℝ, ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ c : ℝ, c₀ ≤ c →
      ∀ f : ℝ → ℝ, IsHankelEigenfn c ε f → hankelMass c f = 1 →
        ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) →
          ∫ x in (0 : ℝ)..(ctPhiR ε c R), (1 + x) ^ (1 / 2 : ℝ) * |hankelPsiR c f x| ≤ 3 * Real.log c := by
  obtain ⟨C₂, c₀₂, hC₂, hbody₂, hwin₂⟩ := ct_rosc_setup
  set Lc := max 2 (max (langerLobeK⁻¹) ((5 * langerLobeK ^ (3 / 2 : ℝ))⁻¹ ^ 2)) with hLc
  have hL_log : ∀ᶠ c : ℝ in atTop, Real.log c ≤ (c₁ ^ 2 / 2) * c ^ (2 / 3 : ℝ) := by
    have hlo := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 2 / 3 by norm_num)).bound
      (show (0 : ℝ) < c₁ ^ 2 / 2 by positivity)
    filter_upwards [hlo, eventually_ge_atTop (1 : ℝ)] with c hc h1
    have hlog0 : 0 ≤ Real.log c := Real.log_nonneg h1
    have hc0 : 0 ≤ c ^ (2 / 3 : ℝ) := Real.rpow_nonneg (by linarith only [h1]) _
    rwa [Real.norm_eq_abs, abs_of_nonneg hlog0, Real.norm_eq_abs, abs_of_nonneg hc0] at hc
  have hlog_ge : ∀ᶠ c : ℝ in atTop, Lc ≤ Real.log c :=
    Real.tendsto_log_atTop.eventually_ge_atTop Lc
  have hr_le : ∀ᶠ c : ℝ in atTop,
      (1 + langerRadius c) ^ (1 / 2 : ℝ) * (8 * (c⁻¹ + c ^ (-(4 / 3) : ℝ)) + c ^ (-(4 / 3) : ℝ)) ≤ 1 := by
    have ht1 : Tendsto (fun c : ℝ => (1 + langerRadius c) ^ (1 / 2 : ℝ) * (c ^ (-(1 : ℝ)) + c ^ (-(4 / 3 : ℝ))))
        atTop (𝓝 0) := by
      have hbd : ∀ᶠ c : ℝ in atTop, ‖(1 + langerRadius c) ^ (1 / 2 : ℝ) * (c ^ (-(1 : ℝ)) + c ^ (-(4 / 3 : ℝ)))‖ ≤
          4 * ((langerKappa * 4.94e-4 + 1) ^ (1 / 2 : ℝ) * c ^ (-(2 / 3 : ℝ))) := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with c h1
        have hc0 : 0 < c := by linarith only [h1]
        have hA := langerRadius_pos hc0
        have hκ := langerKappa_pos
        have hc23p : 0 ≤ c ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
        have h1A : 1 + langerRadius c ≤ (langerKappa * 4.94e-4 + 1) * c ^ (2 / 3 : ℝ) := by
          have hc23 : 1 ≤ c ^ (2 / 3 : ℝ) := Real.one_le_rpow h1 (by norm_num)
          have hl : langerRadius c = (langerKappa * 4.94e-4) * c ^ (2 / 3 : ℝ) := by
            show c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 = _; ring
          rw [hl]; nlinarith only [hc23]
        have hp1 : (1 + langerRadius c) ^ (1 / 2 : ℝ) ≤ (langerKappa * 4.94e-4 + 1) ^ (1 / 2 : ℝ) * c ^ (1 / 3 : ℝ) := by
          calc _ ≤ ((langerKappa * 4.94e-4 + 1) * c ^ (2 / 3 : ℝ)) ^ (1 / 2 : ℝ) :=
                Real.rpow_le_rpow (by linarith only [hA]) h1A (by norm_num)
            _ = _ := by
                rw [Real.mul_rpow (by positivity) hc23p, ← Real.rpow_mul hc0.le]; norm_num
        have hc_neg : c ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        have hsum : c ^ (-(1 : ℝ)) + c ^ (-(4 / 3 : ℝ)) ≤ 2 * c ^ (-(1 : ℝ)) := by linarith only [hc_neg]
        have hmul : c ^ (1 / 3 : ℝ) * c ^ (-(1 : ℝ)) = c ^ (-(2 / 3 : ℝ)) := by
          rw [← Real.rpow_add hc0]; norm_num
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith only [hA]) _)
          (add_nonneg (Real.rpow_nonneg hc0.le _) (Real.rpow_nonneg hc0.le _)))]
        have hterm : 0 ≤ (langerKappa * 4.94e-4 + 1) ^ (1 / 2 : ℝ) * c ^ (-(2 / 3 : ℝ)) := by positivity
        calc (1 + langerRadius c) ^ (1 / 2 : ℝ) * (c ^ (-(1 : ℝ)) + c ^ (-(4 / 3 : ℝ)))
            ≤ ((langerKappa * 4.94e-4 + 1) ^ (1 / 2 : ℝ) * c ^ (1 / 3 : ℝ)) * (2 * c ^ (-(1 : ℝ))) :=
              mul_le_mul hp1 hsum (by positivity) (by positivity)
          _ = 2 * ((langerKappa * 4.94e-4 + 1) ^ (1 / 2 : ℝ) * (c ^ (1 / 3 : ℝ) * c ^ (-(1 : ℝ)))) := by ring
          _ ≤ 4 * ((langerKappa * 4.94e-4 + 1) ^ (1 / 2 : ℝ) * c ^ (-(2 / 3 : ℝ))) := by
              rw [hmul]; linarith only [hterm]
      have ht0 : Tendsto (fun c : ℝ => 4 * ((langerKappa * 4.94e-4 + 1) ^ (1 / 2 : ℝ) * c ^ (-(2 / 3 : ℝ))))
          atTop (𝓝 0) := by
        simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul _).const_mul 4
      exact squeeze_zero_norm' hbd ht0
    have ht3 : Tendsto (fun c : ℝ => (1 + langerRadius c) ^ (1 / 2 : ℝ) *
        (8 * (c ^ (-(1 : ℝ)) + c ^ (-(4 / 3 : ℝ))) + c ^ (-(4 / 3 : ℝ)))) atTop (𝓝 0) := by
      have hbd2 : ∀ᶠ c : ℝ in atTop,
          ‖(1 + langerRadius c) ^ (1 / 2 : ℝ) * (8 * (c ^ (-(1 : ℝ)) + c ^ (-(4 / 3 : ℝ))) + c ^ (-(4 / 3 : ℝ)))‖ ≤
            9 * ((1 + langerRadius c) ^ (1 / 2 : ℝ) * (c ^ (-(1 : ℝ)) + c ^ (-(4 / 3 : ℝ)))) := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with c h1
        have hc0 : 0 < c := by linarith only [h1]
        have hA := langerRadius_pos hc0
        have hp : 0 ≤ (1 + langerRadius c) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith only [hA]) _
        have hc4 : 0 ≤ c ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
        have hc1 : 0 ≤ c ^ (-(1 : ℝ)) := Real.rpow_nonneg hc0.le _
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (add_nonneg (mul_nonneg (by norm_num) (add_nonneg hc1 hc4)) hc4))]
        calc (1 + langerRadius c) ^ (1 / 2 : ℝ) * (8 * (c ^ (-(1 : ℝ)) + c ^ (-(4 / 3 : ℝ))) + c ^ (-(4 / 3 : ℝ)))
            ≤ (1 + langerRadius c) ^ (1 / 2 : ℝ) * (9 * (c ^ (-(1 : ℝ)) + c ^ (-(4 / 3 : ℝ)))) :=
              mul_le_mul_of_nonneg_left (by linarith only [hc4, hc1]) hp
          _ = 9 * ((1 + langerRadius c) ^ (1 / 2 : ℝ) * (c ^ (-(1 : ℝ)) + c ^ (-(4 / 3 : ℝ)))) := by ring
      exact squeeze_zero_norm' hbd2 (by simpa using ht1.const_mul 9)
    filter_upwards [ht3.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_gt_atTop 0] with c hc hc0
    rwa [Real.rpow_neg_one] at hc
  have hev : ∀ᶠ c : ℝ in atTop,
      c₀₂ ≤ c ∧ 3e6 ≤ c ∧ C₂ * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 ∧
      1 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) ∧
      Real.log c ≤ (c₁ ^ 2 / 2) * c ^ (2 / 3 : ℝ) ∧ Lc ≤ Real.log c ∧
      2 * langerRadius c * hankelRinf c ≤ 1 ∧
      3 * (langerRadius c * hankelRinf c) ≤ c ^ (-(4 / 3) : ℝ) ∧
      16 * Real.exp (-(1 / 25) * c) ≤ c ^ (-(4 / 3) : ℝ) ∧
      (1 + langerRadius c) ^ (1 / 2 : ℝ) * (8 * (c⁻¹ + c ^ (-(4 / 3) : ℝ)) + c ^ (-(4 / 3) : ℝ)) ≤ 1 := by
    filter_upwards [eventually_ge_atTop c₀₂, eventually_ge_atTop (3e6 : ℝ),
      eventually_rpow_neg_le (by norm_num : (0 : ℝ) < 1 / 3) C₂ (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_rpow_ge (by norm_num : (0 : ℝ) < 2 / 3) (by positivity : 0 < c₁ ^ 2) 1,
      hL_log, hlog_ge, rate_Ar, rate_exp_lin, hr_le]
      with c h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨h1, h2, h3, h4, h5, h6, h7.2, h7.1, h8, h9⟩
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.1 hev
  refine ⟨max c₀ 2, fun ε hε c hc f hf hM R hR => ?_⟩
  obtain ⟨hc₀₂, hc3, hsm, hR1_lb, hlog_ub, hlog_lc, hAr1, hAr43, hexp_lin, htail_bd⟩ :=
    hc₀ c ((le_max_left _ _).trans hc)
  have hc0 : 0 < c := by linarith [le_max_right c₀ 2]
  have hbody' := hbody₂ ε hε c hc₀₂
  have hH : CtRealChartHyp ε c C₂ := ⟨hbody', hC₂, hc3, hsm⟩
  have hRm : R ≤ ctRmax ctChartC1 c := hR.2.trans (ctRmax_mono hc0.le hc₁.le hle)
  have hR1 : 1 ≤ R := hR1_lb.trans hR.1
  have ha_abs : |ctPhiR ε c R| < langerRadius c :=
    hH.abs_ctPhiR_lt (u := R) (by rw [abs_of_pos (by linarith only [hR1])]; exact hRm)
  have ha_lb : (c₁ ^ 2 / 2) * c ^ (2 / 3 : ℝ) ≤ ctPhiR ε c R := by
    have h := (abs_le.1 (hH.abs_ctPhiR_sub_le (u := R) (by rw [abs_of_pos (by linarith only [hR1])]; exact hRm))).1
    have hc23 : 1 ≤ c ^ (2 / 3 : ℝ) := by
      have := Real.one_le_rpow (by linarith only [hc3] : (1 : ℝ) ≤ c) (by norm_num : (0 : ℝ) ≤ 2 / 3)
      exact this
    have hc_small : C₂ * c ^ (-(1 / 3 : ℝ)) ≤ (c₁ ^ 2 / 2) * c ^ (2 / 3 : ℝ) := by
      --Wait: we didn't add `C₂ c^{-1/3} ≤ c₁^2/2 * c^{2/3}` to `hev` of `psiR_pos_half_moment_le`!
      -- Let's check: `C₂ * c^{-1/3} ≤ 1/2` is `hsm`, so we just need `1 ≤ c₁^2 * c^{2/3}` -> `(c₁^2 / 2) * c^{2/3} ≥ 1/2`!
      nlinarith only [hR1_lb, hsm]
    linarith only [h, hR.1, hc_small]
  have hx1_le : Real.log c ≤ ctPhiR ε c R := hlog_ub.trans ha_lb
  have hlog2 : 2 ≤ Real.log c := (le_max_left _ _).trans hlog_lc
  have hlog0 : 0 < Real.log c := by linarith only [hlog2]
  have hk_log : 1 ≤ langerLobeK * Real.log c := by
    have hk1 : langerLobeK⁻¹ ≤ Real.log c := (le_max_left _ _).trans ((le_max_right _ _).trans hlog_lc)
    rw [← div_le_iff₀' langerLobeK_pos]
    simpa [div_eq_mul_inv] using hk1
  have hpow_log : (1 + Real.log c) ^ (1 / 2 : ℝ) ≤ Real.log c := by
    have hsq : 1 + Real.log c ≤ (Real.log c) ^ 2 := by nlinarith only [hlog2]
    have := Real.rpow_le_rpow (by linarith only [hlog0]) hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [← Real.rpow_natCast (Real.log c) 2, ← Real.rpow_mul hlog0.le,
      show ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] at this
  have hexp_log : Real.exp (-5 * (langerLobeK * Real.log c) ^ (3 / 2 : ℝ)) ≤ c⁻¹ := by
    have hlk : (5 * langerLobeK ^ (3 / 2 : ℝ))⁻¹ ^ 2 ≤ Real.log c :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hlog_lc)
    have hpos_k : 0 < 5 * langerLobeK ^ (3 / 2 : ℝ) := by have := langerLobeK_pos; positivity
    have hsqrt : (5 * langerLobeK ^ (3 / 2 : ℝ))⁻¹ ≤ (Real.log c) ^ (1 / 2 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) hlk (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] at this
    have hmul : 1 ≤ (Real.log c) ^ (1 / 2 : ℝ) * (5 * langerLobeK ^ (3 / 2 : ℝ)) := by
      rw [inv_eq_one_div, div_le_iff₀' hpos_k] at hsqrt
      linarith only [hsqrt]
    have h32 : Real.log c ≤ 5 * (langerLobeK * Real.log c) ^ (3 / 2 : ℝ) := by
      have hrp : (langerLobeK * Real.log c) ^ (3 / 2 : ℝ) =
          langerLobeK ^ (3 / 2 : ℝ) * ((Real.log c) ^ (1 / 2 : ℝ) * Real.log c) := by
        rw [Real.mul_rpow langerLobeK_pos.le hlog0.le,
          show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hlog0, Real.rpow_one]
      rw [hrp]
      calc Real.log c = 1 * Real.log c := by ring
        _ ≤ ((Real.log c) ^ (1 / 2 : ℝ) * (5 * langerLobeK ^ (3 / 2 : ℝ))) * Real.log c :=
            mul_le_mul_of_nonneg_right hmul hlog0.le
        _ = _ := by ring
    calc Real.exp (-5 * (langerLobeK * Real.log c) ^ (3 / 2 : ℝ))
        ≤ Real.exp (-Real.log c) := Real.exp_le_exp.2 (by linarith only [h32])
      _ = c⁻¹ := by rw [Real.exp_neg, Real.exp_log hc0]
  set a := ctPhiR ε c R with ha
  have hΨ_cont : ContinuousOn (fun x => (1 + x) ^ (1 / 2 : ℝ) * |hankelPsiR c f x|) (Icc 0 a) := by
    have hA_pos := langerRadius_pos hc0
    have h1 : ContinuousOn (fun x : ℝ => (1 + x) ^ (1 / 2 : ℝ)) (Icc 0 a) :=
      ContinuousOn.rpow_const (by fun_prop) fun x hx => Or.inl (by linarith only [hx.1])
    have h2 : ContinuousOn (fun x => |hankelPsiR c f x|) (Icc 0 a) :=
      continuous_abs.comp_continuousOn ((continuousOn_hankelPsiR hc0 hf).mono fun x hx =>
        ⟨by linarith only [hx.1, hA_pos], by linarith only [hx.2, (abs_le.1 ha_abs.le).2]⟩)
    exact h1.mul h2
  have hi1 : IntervalIntegrable (fun x => (1 + x) ^ (1 / 2 : ℝ) * |hankelPsiR c f x|) volume 0 (Real.log c) :=
    (hΨ_cont.mono (Icc_subset_Icc_right hx1_le)).intervalIntegrable_of_Icc hlog0.le
  have hi2 : IntervalIntegrable (fun x => (1 + x) ^ (1 / 2 : ℝ) * |hankelPsiR c f x|) volume (Real.log c) a :=
    (hΨ_cont.mono (Icc_subset_Icc_left hlog0.le)).intervalIntegrable_of_Icc hx1_le
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  -- Part 1: `0 .. log c`
  have hpart1 : ∫ x in (0 : ℝ)..(Real.log c), (1 + x) ^ (1 / 2 : ℝ) * |hankelPsiR c f x| ≤ 2 * Real.log c := by
    have hA_pos := langerRadius_pos hc0
    have hΨ1 : ContinuousOn (fun x => |hankelPsiR c f x|) (Icc 0 (Real.log c)) :=
      continuous_abs.comp_continuousOn ((continuousOn_hankelPsiR hc0 hf).mono fun x hx =>
        ⟨by linarith only [hx.1, hA_pos], by linarith only [hx.2, hx1_le, (abs_le.1 ha_abs.le).2]⟩)
    have hmono := intervalIntegral.integral_mono_on hlog0.le hi1 ((hΨ1.const_mul (Real.log c)).intervalIntegrable_of_Icc hlog0.le)
      fun x hx => by
        have h1 : (1 + x) ^ (1 / 2 : ℝ) ≤ (1 + Real.log c) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by linarith only [hx.1]) (by linarith only [hx.2]) (by norm_num)
        exact mul_le_mul_of_nonneg_right (h1.trans hpow_log) (abs_nonneg _)
    rw [intervalIntegral.integral_const_mul] at hmono
    have hmass := hankel_psi_abs_mass (by linarith only [hc3] : (5000 : ℝ) ≤ c) hf hε hM
    have hle_m : ∫ x in (0 : ℝ)..(Real.log c), |hankelPsiR c f x| ≤ 1 + 2 * langerRadius c * hankelRinf c := by
      have hsub : (∫ x in (0 : ℝ)..(Real.log c), |hankelPsiR c f x|) ≤
          ∫ x in (-langerRadius c)..(langerRadius c), |hankelPsiR c f x| :=
        intervalIntegral.integral_mono_interval
          (by linarith only [hA_pos] : -(langerRadius c) ≤ 0)
          hlog0.le
          (by linarith only [hx1_le, (abs_le.1 ha_abs.le).2] : Real.log c ≤ langerRadius c)
          (Eventually.of_forall fun _ => abs_nonneg _)
          (by
            refine ContinuousOn.intervalIntegrable ?_
            rw [uIcc_of_le (by linarith only [hA_pos] : -(langerRadius c) ≤ langerRadius c)]
            exact continuous_abs.comp_continuousOn (continuousOn_hankelPsiR hc0 hf))
      exact hsub.trans hmass
    have hle2 : ∫ x in (0 : ℝ)..(Real.log c), |hankelPsiR c f x| ≤ 2 := by linarith only [hle_m, hAr1]
    calc _ ≤ Real.log c * ∫ x in (0 : ℝ)..(Real.log c), |hankelPsiR c f x| := hmono
      _ ≤ Real.log c * 2 := mul_le_mul_of_nonneg_left hle2 hlog0.le
      _ = 2 * Real.log c := by ring
  -- Part 2: `log c .. a`
  have hpart2 : ∫ x in (Real.log c)..a, (1 + x) ^ (1 / 2 : ℝ) * |hankelPsiR c f x| ≤ Real.log c := by
    have hA_pos := langerRadius_pos hc0
    have hΨ2 : ContinuousOn (fun x => |hankelPsiR c f x|) (Icc (Real.log c) a) :=
      continuous_abs.comp_continuousOn ((continuousOn_hankelPsiR hc0 hf).mono fun x hx =>
        ⟨by linarith only [hx.1, hlog0, hA_pos], by linarith only [hx.2, (abs_le.1 ha_abs.le).2]⟩)
    have hmono := intervalIntegral.integral_mono_on hx1_le hi2
      ((hΨ2.const_mul ((1 + langerRadius c) ^ (1 / 2 : ℝ))).intervalIntegrable_of_Icc hx1_le)
      fun x hx => by
        have h1 : (1 + x) ^ (1 / 2 : ℝ) ≤ (1 + langerRadius c) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by linarith only [hx.1, hlog0]) (by linarith only [hx.2, (abs_le.1 ha_abs.le).2]) (by norm_num)
        exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    rw [intervalIntegral.integral_const_mul] at hmono
    have ht1 : Real.exp (-(1 / 25) * c) ≤ c ^ (-(4 / 3) : ℝ) := by
      have : 0 ≤ Real.exp (-(1 / 25) * c) := Real.exp_pos _ |>.le
      linarith only [hexp_lin, this]
    have hr0 : 0 ≤ hankelRinf c := hankelRinf_nonneg (by linarith only [hc3]) hf hε hM
    have ht2 : (a - Real.log c) * hankelRinf c ≤ langerRadius c * hankelRinf c := by
      gcongr; linarith only [hlog0, (abs_le.1 ha_abs.le).2]
    have ht3 : langerRadius c * hankelRinf c ≤ c ^ (-(4 / 3) : ℝ) := by
      have : 0 ≤ langerRadius c * hankelRinf c := mul_nonneg (langerRadius_pos hc0).le hr0
      linarith only [hAr43, this]
    have htail := psi_abs_tail hc3 hf hε hM hlog0.le hx1_le (abs_le.1 ha_abs.le).2 hk_log
    have hbd_int : ∫ x in (Real.log c)..a, |hankelPsiR c f x| ≤
        8 * (c⁻¹ + c ^ (-(4 / 3) : ℝ)) + c ^ (-(4 / 3) : ℝ) := by
      calc _ ≤ 8 * (Real.exp (-5 * (langerLobeK * Real.log c) ^ (3 / 2 : ℝ)) + Real.exp (-(1 / 25) * c)) +
              (a - Real.log c) * hankelRinf c := htail
        _ ≤ 8 * (c⁻¹ + c ^ (-(4 / 3) : ℝ)) + langerRadius c * hankelRinf c := by gcongr
        _ ≤ 8 * (c⁻¹ + c ^ (-(4 / 3) : ℝ)) + c ^ (-(4 / 3) : ℝ) := by gcongr
    have hA_pos := langerRadius_pos hc0
    have hpowA_nn : 0 ≤ (1 + langerRadius c) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith only [hA_pos]) _
    calc _ ≤ (1 + langerRadius c) ^ (1 / 2 : ℝ) * ∫ x in (Real.log c)..a, |hankelPsiR c f x| := hmono
      _ ≤ (1 + langerRadius c) ^ (1 / 2 : ℝ) * (8 * (c⁻¹ + c ^ (-(4 / 3) : ℝ)) + c ^ (-(4 / 3) : ℝ)) :=
          mul_le_mul_of_nonneg_left hbd_int hpowA_nn
      _ ≤ 1 := htail_bd
      _ ≤ Real.log c := by linarith only [hlog2]
  linarith only [hpart1, hpart2]

/-- info: 'FormalResearch.SignUncertainty.hankel_subchart_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_subchart_tail_le

/-- info: 'FormalResearch.SignUncertainty.psiR_pos_half_moment_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms psiR_pos_half_moment_le
