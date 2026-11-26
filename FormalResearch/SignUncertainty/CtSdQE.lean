module

public import FormalResearch.SignUncertainty.CtSdPull
public import FormalResearch.SignUncertainty.CtBinetComplex
public import FormalResearch.SignUncertainty.BinetVertical

/-!
# The amplitude data `SdAmp` for the concrete chart (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 (the expansion of `Q_ε` and the Binet factor).
**Proved.**  On the polydisc, `Q(s) = Q_ε(s;β)` has the Taylor control `|Q - Q_0 - i h̃ s| ≤ C(|a| + |s|²)`,
`E(s) = e^{-B_c(i T(s;β))}` is holomorphic with `|E - 1| ≤ C c^{-1}|s|`, and the bracket `1 + (s²+a)Q` is bounded.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real

set_option linter.unusedSectionVars false

namespace FormalResearch.SignUncertainty.CtSd

open FormalResearch.SignUncertainty.CtChart

set_option maxHeartbeats 1600000 in
theorem sdAmp_real {ε : ℝ} {ϑ : ℂ → ℂ} {ρ : ℝ} (hA : AnalyticAt ℂ ϑ 0) (hreg : ChartReg ε ϑ ρ) (hρ : 0 < ρ)
    {Cβ : ℝ} (hCβ : 0 ≤ Cβ) :
    ∃ ρ1 CQ CE CB : ℝ, 0 < ρ1 ∧ ρ1 ≤ ρ ∧ ρ1 ≤ 1 ∧ 0 ≤ CQ ∧ 0 ≤ CE ∧ 0 ≤ CB ∧
      ∀ {c lam ρ0 β a : ℝ}, 2 ≤ c → 0 < lam → c * lam ^ 3 = 1 → 0 < ρ0 → ρ0 ≤ ρ1 → |β| < ρ1 → |β| ≤ Cβ * |a| → |a| ≤ 1 →
        SdAmp lam ρ0 (a : ℂ) (Qgeo (0, 0)) (Complex.I * htil ϑ (0, 0))
          (fun z => Qeps ϑ (z, (β : ℂ))) (fun z => dyF (Qeps ϑ) (z, (β : ℂ))) (Efun c (β : ℂ)) CQ CE CB ∧
        DifferentiableOn ℂ (Efun c (β : ℂ)) (ball 0 ρ0) := by
  obtain ⟨C, ρ', hρ', hexp⟩ := Qeps_expansion hA
  obtain ⟨K, r, hr, hL⟩ := lipschitz_of_cd contDiffAt_Tf
  have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
  set ρ1 : ℝ := min (min (min (min ρ ρ') r) 1) (1 / (2 * (K + 1))) with hρ1
  have hρ10 : 0 < ρ1 := lt_min (lt_min (lt_min (lt_min hρ hρ') hr) one_pos) (by positivity)
  have hρ1ρ : ρ1 ≤ ρ := (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hρ1ρ' : ρ1 ≤ ρ' := (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hρ1r : ρ1 ≤ r := ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hρ11 : ρ1 ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hρ1K : ρ1 ≤ 1 / (2 * (K + 1)) := min_le_right _ _
  set CQ : ℝ := |C| * (1 + Cβ) with hCQ
  have hCQ0 : 0 ≤ CQ := by positivity
  set MQ : ℝ := ‖Qgeo ((0 : ℂ), (0 : ℂ))‖ + ‖Complex.I * htil ϑ (0, 0)‖ + 2 * CQ with hMQ
  have hMQ0 : 0 ≤ MQ := by positivity
  refine ⟨ρ1, CQ, 8 * K, 1 + 2 * MQ, hρ10, hρ1ρ, hρ11, hCQ0, by positivity, by positivity, ?_⟩
  intro c lam ρ0 β a hc hlam hlc hρ0 hρ01 hβ haβ ha1
  have hc0 : 0 < c := by linarith
  have hβC : ‖(β : ℂ)‖ < ρ1 := by simpa using hβ
  have hβρ : ‖(β : ℂ)‖ < ρ := lt_of_lt_of_le hβC hρ1ρ
  have hbn : ‖(β : ℂ)‖ ≤ Cβ * ‖(a : ℂ)‖ := by simpa using haβ
  have han : ‖(a : ℂ)‖ ≤ 1 := by simpa using ha1
  have hzρ : ∀ z : ℂ, z ∈ ball (0 : ℂ) ρ0 → ‖z‖ < ρ1 := fun z hz => by
    rw [mem_ball, dist_zero_right] at hz; exact lt_of_lt_of_le hz hρ01
  -- Lipschitz control of `Tf(·, β)`
  have hTf : ∀ z : ℂ, z ∈ ball (0 : ℂ) ρ0 → ‖Tf (z, (β : ℂ))‖ ≤ K * ‖z‖ := by
    intro z hz
    have hz1 := hzρ z hz
    have h1 := hL.dist_le_mul (z, (β : ℂ)) (mem_ball_prod (hz1.trans_le hρ1r) (hβC.trans_le hρ1r))
      (0, (β : ℂ)) (mem_ball_prod (by simpa using hr) (hβC.trans_le hρ1r))
    rw [dist_eq_norm, dist_eq_norm, Tf_zero_left, sub_zero] at h1
    refine h1.trans (le_of_eq ?_)
    congr 1
    rw [show ((z, (β : ℂ)) - ((0 : ℂ), (β : ℂ))) = (z, (0 : ℂ)) by simp, Prod.norm_def]
    simp
  have hTh : ∀ z : ℂ, z ∈ ball (0 : ℂ) ρ0 → ‖Tf (z, (β : ℂ))‖ ≤ 1 / 2 := by
    intro z hz
    have := hTf z hz
    have hz1 := hzρ z hz
    have h2 : K * ‖z‖ ≤ K * ρ1 := mul_le_mul_of_nonneg_left hz1.le hK0
    have h3 : K * ρ1 ≤ K * (1 / (2 * (K + 1))) := mul_le_mul_of_nonneg_left hρ1K hK0
    have h4 : K * (1 / (2 * (K + 1))) ≤ 1 / 2 := by
      rw [show K * (1 / (2 * (K + 1))) = (K / (K + 1)) / 2 by field_simp]
      have : K / (K + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    linarith
  -- differentiability of `E`
  have hEd : DifferentiableOn ℂ (Efun c (β : ℂ)) (ball 0 ρ0) := by
    intro z hz
    have hz1 := hzρ z hz
    have hTd : DifferentiableAt ℂ (fun z' : ℂ => Tf (z', (β : ℂ))) z :=
      (hreg z β (hz1.trans_le hρ1ρ) hβρ).2.1.differentiableAt
    have hIm : Tf (z, (β : ℂ)) ∈ {τ : ℂ | -1 < τ.im} := by
      have := hTh z hz
      show -1 < (Tf (z, (β : ℂ))).im
      have h2 : |(Tf (z, (β : ℂ))).im| ≤ ‖Tf (z, (β : ℂ))‖ := Complex.abs_im_le_norm _
      have := (abs_le.1 (h2.trans this)).1
      linarith
    have hB := (BinetDecay.differentiableOn_binetDiff_vertical hc0 _ hIm).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hIm)
    have := (hB.comp z hTd).neg.cexp
    exact this.differentiableWithinAt
  refine ⟨⟨hCQ0, by positivity, by positivity, ?_, ?_, ?_, ?_, hEd.continuousOn, ?_, ?_⟩, hEd⟩
  · intro z hz
    have hz1 := hzρ z hz
    have hd := (hreg z β (hz1.trans_le hρ1ρ) hβρ).2.2.2.2.2.2.1
    have := hasDerivAt_slice1 (q := (z, (β : ℂ))) hd
    simpa [dyF] using this
  · intro z hz
    have hz1 := hzρ z hz
    have hc1 := (hreg z β (hz1.trans_le hρ1ρ) hβρ).2.2.2.2.2.2.2.1
    have hcomp : ContinuousAt (fun z' : ℂ => (z', (β : ℂ))) z := by fun_prop
    exact (ContinuousAt.comp (f := fun z' : ℂ => (z', (β : ℂ))) hc1 hcomp).continuousWithinAt
  · intro z hz
    have hz1 := hzρ z hz
    have := (hexp z β (hz1.trans_le hρ1ρ') (hβC.trans_le hρ1ρ')).1
    refine this.trans ?_
    have h1 : |C| * (‖(β : ℂ)‖ + ‖z‖ ^ 2) ≤ CQ * (‖(a : ℂ)‖ + ‖z‖ ^ 2) := by
      rw [hCQ]
      have : ‖(β : ℂ)‖ + ‖z‖ ^ 2 ≤ (1 + Cβ) * (‖(a : ℂ)‖ + ‖z‖ ^ 2) := by
        nlinarith [norm_nonneg (a : ℂ), sq_nonneg ‖z‖, mul_nonneg hCβ (sq_nonneg ‖z‖)]
      calc |C| * (‖(β : ℂ)‖ + ‖z‖ ^ 2) ≤ |C| * ((1 + Cβ) * (‖(a : ℂ)‖ + ‖z‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg C)
        _ = _ := by ring
    exact (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans h1
  · intro z hz
    have hz1 := hzρ z hz
    have := (hexp z β (hz1.trans_le hρ1ρ') (hβC.trans_le hρ1ρ')).2
    refine this.trans ?_
    have : ‖(β : ℂ)‖ ≤ Cβ * ‖(a : ℂ)‖ := hbn
    calc C * (‖z‖ + ‖(β : ℂ)‖) ≤ |C| * (‖z‖ + ‖(β : ℂ)‖) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * ((1 + Cβ) * (‖z‖ + ‖(a : ℂ)‖)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
          nlinarith [norm_nonneg (a : ℂ), norm_nonneg z, mul_nonneg hCβ (norm_nonneg z)]
      _ = CQ * (‖z‖ + ‖(a : ℂ)‖) := by rw [hCQ]; ring
  · intro z hz
    have hz1 := hzρ z hz
    have h := BinetDecay.norm_exp_neg_binetDiff_sub_one hc (ζ := Complex.I * Tf (z, (β : ℂ))) (by
      rw [norm_mul, Complex.norm_I, one_mul]; exact hTh z hz)
    rw [norm_mul, Complex.norm_I, one_mul] at h
    unfold Efun
    refine h.trans ?_
    have hcl : 1 / c = lam ^ 3 := by field_simp; linarith
    calc 8 * ‖Tf (z, (β : ℂ))‖ / c ≤ 8 * (K * ‖z‖) / c := by
          gcongr; exact hTf z hz
      _ = 8 * K * lam ^ 3 * ‖z‖ := by rw [← hcl]; ring
  · intro z hz
    have hz1 := hzρ z hz
    have hzn : ‖z‖ < 1 := lt_of_lt_of_le hz1 hρ11
    have hQ := (hexp z β (hz1.trans_le hρ1ρ') (hβC.trans_le hρ1ρ')).1
    have h1 : |C| * (‖(β : ℂ)‖ + ‖z‖ ^ 2) ≤ CQ * (‖(a : ℂ)‖ + ‖z‖ ^ 2) := by
      rw [hCQ]
      have : ‖(β : ℂ)‖ + ‖z‖ ^ 2 ≤ (1 + Cβ) * (‖(a : ℂ)‖ + ‖z‖ ^ 2) := by
        nlinarith [norm_nonneg (a : ℂ), sq_nonneg ‖z‖, mul_nonneg hCβ (sq_nonneg ‖z‖)]
      calc |C| * (‖(β : ℂ)‖ + ‖z‖ ^ 2) ≤ |C| * ((1 + Cβ) * (‖(a : ℂ)‖ + ‖z‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg C)
        _ = _ := by ring
    have hQb : ‖Qeps ϑ (z, (β : ℂ))‖ ≤ MQ := by
      have e : Qeps ϑ (z, (β : ℂ)) = Qgeo (0, 0) + Complex.I * htil ϑ (0, 0) * z +
          (Qeps ϑ (z, (β : ℂ)) - Qgeo (0, 0) - Complex.I * htil ϑ (0, 0) * z) := by ring
      rw [e]
      refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
      rw [norm_mul]
      have h2 : ‖Complex.I * htil ϑ (0, 0)‖ * ‖z‖ ≤ ‖Complex.I * htil ϑ (0, 0)‖ :=
        mul_le_of_le_one_right (norm_nonneg _) hzn.le
      have h3 : ‖Qeps ϑ (z, (β : ℂ)) - Qgeo (0, 0) - Complex.I * htil ϑ (0, 0) * z‖ ≤ 2 * CQ := by
        refine hQ.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans (h1.trans ?_))
        have : ‖(a : ℂ)‖ + ‖z‖ ^ 2 ≤ 2 := by nlinarith [norm_nonneg z]
        nlinarith [mul_le_mul_of_nonneg_left this hCQ0]
      rw [hMQ]; linarith
    have hza : ‖z ^ 2 + (a : ℂ)‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_pow]; nlinarith [norm_nonneg z]
    generalize Qeps ϑ (z, (β : ℂ)) = q at hQb ⊢
    have hq0 := norm_nonneg q
    have h5 : ‖1 + (z ^ 2 + (a : ℂ)) * q‖ ≤ 1 + ‖z ^ 2 + (a : ℂ)‖ * ‖q‖ := by
      have := norm_add_le (1 : ℂ) ((z ^ 2 + (a : ℂ)) * q)
      rwa [norm_one, norm_mul] at this
    have h6 : ‖z ^ 2 + (a : ℂ)‖ * ‖q‖ ≤ 2 * MQ :=
      (mul_le_mul hza hQb hq0 (by norm_num))
    linarith

end FormalResearch.SignUncertainty.CtSd
