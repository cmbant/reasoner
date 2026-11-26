module

public import Mathlib
public import FormalResearch.ModularBootstrap.FiveTerm.LowerGoodArea
public import FormalResearch.ModularBootstrap.FiveTerm.LowerGoodWtilde

/-!
# Unfolding the Airy circle quantity `η` to half-sector integrals of `G_reg`

The mechanism shared by Paper I (`constant_terms_lower.tex`, `ct:dyadic` (2), last paragraph; `ap:lemU`) and Paper II
(`LowerFirstGood`, `lowerFirstGood_of_chart_on_band`): for an abstract density `Ψ̃ : ℂ → ℂ`, continuous on a disc `|ũ| ≤ B`, and a
chart `φ_c` with `φ_c(u) = u + O(c^{-1/3})`, `φ_c'(u) = 1 + O(c⁻¹)` on `|u| ≤ R_max = 4 r₀²`, the circle quantity

`η(R) = ∮_{|ũ|=R} |Ψ̃| / |e| |dũ| + ∮_{|u|=R} |Ψ̃(φ_c(u)) φ_c'(u)| / |e| |du|`   (`e = airyEnv`, `airyEta`)

is bounded, for `R = r²`, `r ∈ [r₀, (3/2) r₀]`, by the two half-sector integrals of the regularised Airy-unfolded test
`G_reg(w) = (1 - w²/A²)² w Ψ̃(-w²) e^{(4/3) i w³}` (`airyGReg`) along the arcs `|w| = r` and `|w̃(w)| ≈ r`, `w̃` the
`φ_c`-transported coordinate (`lowerGoodWtilde`).  The proof substitutes `θ = 2φ - π` (the circle `|u| = r²` is the image of the
upper half arc `u = -w²`), uses `|e(-w²)| = 1/|exp((4/3) i w³)|` on the upper half-plane (`lowerGood_airyEnv_neg_sq_of_im_pos`), the
envelope comparison `e(φ_c(u)) ≤ e^{C} e(u)` (`lowerGood_airyEnv_ratio_le`) and `|1 - w²/A²|² ≥ 1/2` on `|w| ≤ A/4`.

Proved: `airy_eta_le_arcs` (no hypothesis on `Ψ̃` beyond continuity on `|u| ≤ B`).  Instances: Paper I `ct_eta_transfer`
(`CtDyadicRadius`, `Ψ̃ = hankelPsi c f`, `B = langerRadius c`) and Paper II `lowerFirstGood_eta_le` (`Ψ̃ = virasoroPsiTilde c g`).
-/

@[expose] public section

open Complex MeasureTheory Set Metric intervalIntegral
open scoped Real ENNReal

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.ModularBootstrap.FiveTerm

/-- **Regularised Airy-unfolded test** `G_reg(w) = (1 - w²/A²)² w Ψ̃(-w²) exp((4/3) i w³)` for an abstract density `Ψ̃`. -/
noncomputable def airyGReg (Ψ : ℂ → ℂ) (A : ℝ) (w : ℂ) : ℂ :=
  (1 - w ^ 2 / (A : ℂ) ^ 2) ^ 2 * w * Ψ (-(w ^ 2)) * Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)

/-- The transported density `f(u) = Ψ̃(φ(u)) φ'(u)` for a chart `φ`. -/
noncomputable def airyF (Ψ Φ : ℂ → ℂ) (u : ℂ) : ℂ := Ψ (Φ u) * deriv Φ u

/-- **The circle quantity** `η(R) = ∫_0^{2π} R (‖Ψ̃(u)‖ + ‖Ψ̃(φ(u)) φ'(u)‖) / e(u) dθ`, `u = R e^{iθ}`, `e = airyEnv`
(`|dũ| = R dθ`). -/
noncomputable def airyEta (Ψ Φ : ℂ → ℂ) (R : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * π),
    R * (‖Ψ (circleMap 0 R θ)‖ + ‖airyF Ψ Φ (circleMap 0 R θ)‖) / airyEnv (circleMap 0 R θ)

/-- `G_reg` is continuous on `|w| ≤ A` as soon as `Ψ̃` is continuous on `|ũ| ≤ B` and `A² ≤ B`. -/
lemma airyGReg_continuousOn {Ψ : ℂ → ℂ} {A B : ℝ} (hA0 : 0 < A) (hAB : A ^ 2 ≤ B)
    (hΨ : ContinuousOn Ψ (closedBall (0 : ℂ) B)) : ContinuousOn (airyGReg Ψ A) (closedBall (0 : ℂ) A) := by
  have hpsi : ContinuousOn (fun z : ℂ => Ψ (-(z ^ 2))) (closedBall (0 : ℂ) A) :=
    hΨ.comp (by fun_prop) fun z hz => by
      rw [mem_closedBall_zero_iff] at hz ⊢
      rw [norm_neg, norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg z) hz 2).trans hAB
  have hAc : (A : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (pow_pos hA0 2).ne'
  unfold airyGReg
  refine ContinuousOn.mul (ContinuousOn.mul (Continuous.continuousOn ?_) hpsi) (Continuous.continuousOn ?_)
  · fun_prop (disch := exact hAc)
  · fun_prop

/-- **`η` unfolds to the two half-sector integrals of `G_reg`** (`ap:lemU`; `ct:dyadic` (2), Paper I; `LowerFirstGood`, Paper II).
Let `r₀ = c₁ c^{1/3} ≥ 10`, `A ≥ 9 r₀`, `A² ≤ B`, `Ψ̃` continuous on `|ũ| ≤ B`, and `φ_c` a holomorphic chart on a disc of radius
`> R_max = 4 r₀²`, real on the real axis, with `|φ_c(u) - u| ≤ C_φ c^{-1/3} ≤ r₀²/256` and `|φ_c'(u) - 1| ≤ C_φ c⁻¹ ≤ 1/4` on
`|u| ≤ R_max`.  Then for every `r ∈ [r₀, (3/2) r₀]` both arc integrals of `G_reg` (along `w = re^{iφ}` and along its `φ_c`-transport
`w̃(w)`) are continuous in `φ` on `[0, π]`, and
`η(r²) ≤ 2 (2 ∫_0^π r‖G_reg(re^{iφ})‖ dφ + 8 e^{5 c₁ C_φ} ∫_0^π r‖G_reg(w̃(re^{iφ}))‖ dφ)`.  Proved. -/
theorem airy_eta_le_arcs {c1 c Cφ r₀ A B : ℝ} {phi : ℝ → ℂ → ℂ} {Ψ : ℂ → ℂ}
    (hr₀_10 : 10 ≤ r₀) (hCφ : 0 ≤ Cφ)
    (h_err : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ r₀ ^ 2 / 256)
    (h_der : Cφ * c ^ (-1 : ℝ) ≤ 1 / 4)
    (hc_pos : 0 < c) (hr₀_def : r₀ = c1 * c ^ (1 / 3 : ℝ)) (hA9 : 9 * r₀ ≤ A) (hAB : A ^ 2 ≤ B)
    (hΨ : ContinuousOn Ψ (closedBall (0 : ℂ) B))
    (hρ : ∃ ρ : ℝ, lowerRmax c1 c < ρ ∧ DifferentiableOn ℂ (phi c) (ball 0 ρ))
    (him : ∀ x : ℝ, |x| ≤ lowerRmax c1 c → (phi c (x : ℂ)).im = 0)
    (hcl : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      ‖phi c u - u‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (phi c) u - 1‖ ≤ Cφ * c ^ (-1 : ℝ))
    {C_env : ℝ} (hC_env : C_env = 5 * c1 * Cφ) :
    ∀ r ∈ Icc r₀ (3 / 2 * r₀),
      ContinuousOn (fun φ : ℝ => r * ‖airyGReg Ψ A ((r : ℂ) * Complex.exp (φ * I))‖) (Icc 0 π) ∧
      ContinuousOn (fun φ : ℝ => r * ‖airyGReg Ψ A (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖)
        (Icc 0 π) ∧
      airyEta Ψ (phi c) (r ^ 2) ≤
        2 * (2 * (∫ φ in (0 : ℝ)..π, r * ‖airyGReg Ψ A ((r : ℂ) * Complex.exp (φ * I))‖) +
          8 * Real.exp C_env * (∫ φ in (0 : ℝ)..π,
            r * ‖airyGReg Ψ A (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖)) := by
  have hr₀_pos : 0 < r₀ := by linarith
  have hA0 : 0 < A := by linarith
  intro r hr
  have hr_pos : 0 < r := by linarith [hr.1]
  have h_cont_1 : ContinuousOn (fun φ : ℝ => r * ‖airyGReg Ψ A ((r : ℂ) * Complex.exp (φ * I))‖) (Icc 0 π) := by
    have han := airyGReg_continuousOn hA0 hAB hΨ
    refine continuousOn_const.mul (han.norm.comp (by fun_prop) fun φ _ => ?_)
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr_pos,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    have : 9 / 4 * r₀ ≤ A / 4 := by
      linarith only [hA9]
    linarith [hr.2]
  have h_cont_2 : ContinuousOn (fun φ : ℝ => r * ‖airyGReg Ψ A (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖) (Icc 0 π) := by
    have han := airyGReg_continuousOn hA0 hAB hΨ
    have hwt_cont := lowerGood_wtilde_continuousOn hr₀_10 h_err hcl hρ hr₀_def hc_pos
    obtain ⟨h_wt_main, _, _, _, _, _⟩ :=
      lowerGood_wtilde_props hr₀_10 hCφ h_err h_der hρ him hcl hr₀_def hc_pos
    refine continuousOn_const.mul (han.norm.comp (hwt_cont.comp (by fun_prop) fun φ _ => ?_) fun φ _ => ?_)
    · refine ⟨?_, ?_⟩ <;>
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr_pos,
            Complex.norm_exp_ofReal_mul_I, mul_one]
          linarith [hr.1, hr.2]
    · have hnorm_w : ‖(r : ℂ) * Complex.exp (φ * I)‖ = r := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr_pos,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      have hwm := h_wt_main ((r : ℂ) * Complex.exp (φ * I)) (by rw [hnorm_w]; linarith [hr.1])
        (by rw [hnorm_w]; linarith [hr.2])
      rw [mem_closedBall_zero_iff]
      have : 9 / 4 * r₀ ≤ A / 4 := by
        linarith only [hA9]
      linarith [hwm.2.2.2.1]
  refine ⟨h_cont_1, h_cont_2, ?_⟩
  have hRmax_eq : lowerRmax c1 c = 4 * r₀ ^ 2 := by
    unfold lowerRmax
    rw [hr₀_def, mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]
    norm_num; ring
  -- Rewrite `∫ 0..2π` to `∫ (-π)..π` and substitute `θ = 2φ - π`
  let H : ℂ → ℝ := fun u =>
    r ^ 2 * (‖Ψ u‖ + ‖airyF Ψ (phi c) u‖) / airyEnv u
  have hF_eq : airyEta Ψ (phi c) (r ^ 2) = ∫ θ in (0 : ℝ)..(2 * π), H (circleMap 0 (r ^ 2) θ) := by
    rfl
  have h_cont_H : Continuous (fun θ : ℝ => H (circleMap 0 (r ^ 2) θ)) := by
    have h_mem : ∀ θ : ℝ, circleMap 0 (r ^ 2) θ ∈ closedBall (0 : ℂ) (B) := fun θ => by
      rw [mem_closedBall_zero_iff, norm_circleMap_zero, abs_of_pos (sq_pos_of_pos hr_pos)]
      have h1 : r ^ 2 ≤ lowerRmax c1 c := by rw [hRmax_eq]; nlinarith only [hr.2, hr₀_pos, hr_pos]
      have h2 : lowerRmax c1 c ≤ A ^ 2 := by
        rw [hRmax_eq]
        have h94 : 9 / 4 * r₀ ≤ A / 4 := by
          linarith only [hA9]
        have hA_ge : 9 * r₀ ≤ A := by linarith only [h94]
        calc 4 * r₀ ^ 2 ≤ (9 * r₀) ^ 2 := by nlinarith only [hr₀_pos]
          _ ≤ A ^ 2 := pow_le_pow_left₀ (by positivity) hA_ge 2
      exact h1.trans (h2.trans hAB)
    have h_mem_phi : ∀ θ : ℝ, phi c (circleMap 0 (r ^ 2) θ) ∈ closedBall (0 : ℂ) (B) := fun θ => by
      rw [mem_closedBall_zero_iff]
      have h1 : ‖circleMap 0 (r ^ 2) θ‖ ≤ lowerRmax c1 c := by
        rw [norm_circleMap_zero, abs_of_pos (sq_pos_of_pos hr_pos), hRmax_eq]; nlinarith only [hr.2, hr₀_pos, hr_pos]
      have h2 := (hcl _ h1).1
      calc ‖phi c (circleMap 0 (r ^ 2) θ)‖
          = ‖(phi c (circleMap 0 (r ^ 2) θ) - circleMap 0 (r ^ 2) θ) + circleMap 0 (r ^ 2) θ‖ := by ring_nf
        _ ≤ ‖phi c (circleMap 0 (r ^ 2) θ) - circleMap 0 (r ^ 2) θ‖ + ‖circleMap 0 (r ^ 2) θ‖ := norm_add_le _ _
        _ ≤ r₀ ^ 2 / 256 + 9 / 4 * r₀ ^ 2 := add_le_add (h2.trans h_err) (by
            rw [norm_circleMap_zero, abs_of_pos (sq_pos_of_pos hr_pos)]; nlinarith only [hr.2, hr_pos, hr₀_pos])
        _ ≤ A ^ 2 := by
            have h94 : 9 / 4 * r₀ ≤ A / 4 := by
              linarith only [hA9]
            have hA_ge : 9 * r₀ ≤ A := by linarith only [h94]
            have hsq : 81 * r₀ ^ 2 ≤ A ^ 2 := by
              calc 81 * r₀ ^ 2 = (9 * r₀) ^ 2 := by ring
                _ ≤ A ^ 2 := pow_le_pow_left₀ (by positivity) hA_ge 2
            nlinarith only [hsq, sq_nonneg r₀]
        _ ≤ B := hAB
    have h_cont_psi : Continuous (fun θ : ℝ => Ψ (circleMap 0 (r ^ 2) θ)) :=
      hΨ.comp_continuous (continuous_circleMap 0 (r ^ 2)) h_mem
    have h_cont_f : Continuous (fun θ : ℝ => airyF Ψ (phi c) (circleMap 0 (r ^ 2) θ)) := by
      have h_eq_f : (fun θ : ℝ => airyF Ψ (phi c) (circleMap 0 (r ^ 2) θ)) =
          fun θ => Ψ (phi c (circleMap 0 (r ^ 2) θ)) *
            deriv (phi c) (circleMap 0 (r ^ 2) θ) := by
        rfl
      rw [h_eq_f]
      obtain ⟨ρ, hρ_gt, hdiff⟩ := hρ
      have h_in_ball : ∀ θ : ℝ, circleMap 0 (r ^ 2) θ ∈ ball (0 : ℂ) ρ := fun θ => by
        rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos (sq_pos_of_pos hr_pos)]
        have : r ^ 2 ≤ lowerRmax c1 c := by rw [hRmax_eq]; nlinarith [hr.2]
        exact this.trans_lt hρ_gt
      have h_cont_phi : Continuous (fun θ : ℝ => phi c (circleMap 0 (r ^ 2) θ)) :=
        hdiff.continuousOn.comp_continuous (continuous_circleMap 0 (r ^ 2)) h_in_ball
      have h_cont_dphi : Continuous (fun θ : ℝ => deriv (phi c) (circleMap 0 (r ^ 2) θ)) :=
        (hdiff.analyticOnNhd isOpen_ball).deriv.continuousOn.comp_continuous
          (continuous_circleMap 0 (r ^ 2)) h_in_ball
      exact (hΨ.comp_continuous h_cont_phi h_mem_phi).mul h_cont_dphi
    have h_cont_env : Continuous (fun θ : ℝ => airyEnv (circleMap 0 (r ^ 2) θ)) := by
      unfold airyEnv
      exact Real.continuous_exp.comp (continuous_const.mul (by
        -- continuous_re_cpow_three_halves
        have : Continuous (fun z : ℂ => (z ^ (3 / 2 : ℂ)).re) := by
          have heq : (fun z : ℂ => (z ^ (3 / 2 : ℂ)).re) =
              fun z => 3 * z.re * √((‖z‖ + z.re) / 2) - 2 * (√((‖z‖ + z.re) / 2)) ^ 3 := by
            ext z; rw [re_cpow_three_halves_eq]
            have h1 := airySqrtRe_sq_sub z
            have h2 := airySqrtRe_sq_add z
            have hnn : 0 ≤ airySqrtRe z := airySqrtRe_nonneg z
            have hsq : airySqrtRe z ^ 2 = (‖z‖ + z.re) / 2 := by linarith
            have hsq2 : √((‖z‖ + z.re) / 2) = airySqrtRe z := by rw [← hsq, Real.sqrt_sq hnn]
            rw [hsq2]
          rw [heq]; fun_prop
        exact this.comp (continuous_circleMap 0 (r ^ 2))))
    exact (continuous_const.mul (h_cont_psi.norm.add h_cont_f.norm)).div h_cont_env
      fun θ => (airyEnv_pos _).ne'
  have h_per : ∫ θ in (0 : ℝ)..(2 * π), H (circleMap 0 (r ^ 2) θ) =
      ∫ θ in (-π)..π, H (circleMap 0 (r ^ 2) θ) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (h_cont_H.intervalIntegrable (μ := volume) 0 π) (h_cont_H.intervalIntegrable (μ := volume) π (2 * π))
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (h_cont_H.intervalIntegrable (μ := volume) (-π) 0) (h_cont_H.intervalIntegrable (μ := volume) 0 π)
    have h_shift : ∫ θ in π..(2 * π), H (circleMap 0 (r ^ 2) θ) =
        ∫ θ in (-π)..0, H (circleMap 0 (r ^ 2) θ) := by
      have hcomp := intervalIntegral.integral_comp_add_right
        (fun θ : ℝ => H (circleMap 0 (r ^ 2) θ)) (2 * π) (a := -π) (b := 0)
      simp only [zero_add, show -π + 2 * π = π by ring] at hcomp
      rw [← hcomp]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      have hcm : circleMap 0 (r ^ 2) (θ + 2 * π) = circleMap 0 (r ^ 2) θ := by
        simp [circleMap, add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I]
      rw [hcm]
    linarith
  have h_sub : ∫ θ in (-π)..π, H (circleMap 0 (r ^ 2) θ) =
      2 * ∫ φ in (0 : ℝ)..π, H (-(((r : ℂ) * Complex.exp (φ * I)) ^ 2)) := by
    have h1 := intervalIntegral.integral_comp_sub_right
      (fun θ : ℝ => H (circleMap 0 (r ^ 2) θ)) π (a := 0) (b := 2 * π)
    simp only [zero_sub, show 2 * π - π = π by ring] at h1
    have h2 := intervalIntegral.integral_comp_mul_left
      (fun x : ℝ => H (circleMap 0 (r ^ 2) (x - π))) two_ne_zero (a := 0) (b := π)
    simp only [mul_zero] at h2
    have h2' : ∫ x in (0 : ℝ)..(2 * π), H (circleMap 0 (r ^ 2) (x - π)) =
        2 * ∫ φ in (0 : ℝ)..π, H (circleMap 0 (r ^ 2) (2 * φ - π)) := by
      rw [h2]; ring
    rw [← h1, h2']
    have h_congr : ∫ φ in (0 : ℝ)..π, H (circleMap 0 (r ^ 2) (2 * φ - π)) =
        ∫ φ in (0 : ℝ)..π, H (-(((r : ℂ) * Complex.exp (φ * I)) ^ 2)) := by
      refine intervalIntegral.integral_congr fun φ _ => ?_
      have hcm : circleMap 0 (r ^ 2) (2 * φ - π) = -(((r : ℂ) * Complex.exp (φ * I)) ^ 2) := by
        rw [circleMap, zero_add, mul_pow, ← Complex.exp_nat_mul]
        have hexp : Complex.exp (((2 * φ - π : ℝ) : ℂ) * I) = -Complex.exp ((2 : ℕ) * (φ * I)) := by
          rw [show ((2 * φ - π : ℝ) : ℂ) * I = ((2 : ℕ) * (φ * I)) + (-(π : ℂ) * I) by push_cast; ring,
            Complex.exp_add, show -(π : ℂ) * I = -(π * I) by ring, Complex.exp_neg,
            Complex.exp_pi_mul_I]
          ring
        rw [hexp]; push_cast; ring
      rw [hcm]
    rw [h_congr]
  rw [hF_eq, h_per, h_sub]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  -- Pointwise bound on `φ ∈ (0, π)`
  have h_pt : ∀ φ ∈ Ioo (0 : ℝ) π,
      H (-(((r : ℂ) * Complex.exp (φ * I)) ^ 2)) ≤
        2 * (r * ‖airyGReg Ψ A ((r : ℂ) * Complex.exp (φ * I))‖) +
        8 * Real.exp C_env * (r * ‖airyGReg Ψ A (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖) := by
    intro φ hφ
    set w : ℂ := (r : ℂ) * Complex.exp (φ * I) with hw_def
    have hw_norm : ‖w‖ = r := by
      rw [hw_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr_pos,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hw_im : 0 < w.im := by
      have : w.im = r * Real.sin φ := by
        rw [hw_def, Complex.exp_mul_I]
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.add_re, Complex.add_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
          Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
        ring
      rw [this]
      exact mul_pos hr_pos (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2)
    have hw_A4 : ‖w‖ ≤ A / 4 := by
      rw [hw_norm]
      have : 9 / 4 * r₀ ≤ A / 4 := by
        linarith only [hA9]
      linarith [hr.2]
    have h_pre_lb : ∀ z : ℂ, ‖z‖ ≤ A / 4 → 1 / 2 ≤ ‖(1 - z ^ 2 / (A : ℂ) ^ 2) ^ 2‖ := fun z hz => by
      have h1 : ‖z ^ 2 / (A : ℂ) ^ 2‖ ≤ 1 / 16 := by
        rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA0,
          div_le_iff₀ (pow_pos hA0 2)]
        nlinarith only [hz, norm_nonneg z, hA0]
      have h2 : 15 / 16 ≤ ‖1 - z ^ 2 / (A : ℂ) ^ 2‖ := by
        have := norm_sub_norm_le (1 : ℂ) (z ^ 2 / (A : ℂ) ^ 2)
        rw [norm_one] at this
        linarith
      rw [norm_pow]
      nlinarith only [h2]
    have h_env1 := lowerGood_airyEnv_neg_sq_of_im_pos hw_im
    have h_t1 : r ^ 2 * ‖Ψ (-(w ^ 2))‖ / airyEnv (-(w ^ 2)) ≤
        2 * (r * ‖airyGReg Ψ A w‖) := by
      have h_pre := h_pre_lb w hw_A4
      have hGreg : ‖airyGReg Ψ A w‖ =
          ‖(1 - w ^ 2 / (A : ℂ) ^ 2) ^ 2‖ * r * (‖Ψ (-(w ^ 2))‖ / airyEnv (-(w ^ 2))) := by
        unfold airyGReg
        rw [norm_mul, norm_mul, norm_mul, hw_norm, h_env1.2]
        have henv := airyEnv_pos (-(w ^ 2))
        field_simp [henv.ne']
      rw [hGreg]
      have h_ratio_nn : 0 ≤ ‖Ψ (-(w ^ 2))‖ / airyEnv (-(w ^ 2)) :=
        div_nonneg (norm_nonneg _) (airyEnv_pos _).le
      have h_sq_eq : r ^ 2 * ‖Ψ (-(w ^ 2))‖ / airyEnv (-(w ^ 2)) =
          r * r * (‖Ψ (-(w ^ 2))‖ / airyEnv (-(w ^ 2))) := by ring
      rw [h_sq_eq]
      nlinarith [mul_nonneg (sq_nonneg r) h_ratio_nn]
    obtain ⟨h_wt_main, h_wt_im, _, _, _, _⟩ :=
      lowerGood_wtilde_props hr₀_10 hCφ h_err h_der hρ him hcl hr₀_def hc_pos
    have hwm := h_wt_main w (by rw [hw_norm]; linarith [hr.1]) (by rw [hw_norm]; linarith [hr.2])
    have hwt_im : 0 < (lowerGoodWtilde phi c w).im := h_wt_im w (by rw [hw_norm]; exact hr.1)
      (by rw [hw_norm]; exact hr.2) hw_im
    have h_env2 := lowerGood_airyEnv_neg_sq_of_im_pos hwt_im
    have hwt_A4 : ‖lowerGoodWtilde phi c w‖ ≤ A / 4 := by
      refine hwm.2.2.2.1.trans ?_
      linarith only [hA9]
    have hwt_lb : r / 2 ≤ ‖lowerGoodWtilde phi c w‖ := by
      have := norm_sub_norm_le w (lowerGoodWtilde phi c w)
      rw [norm_sub_rev, hw_norm] at this
      linarith [hwm.2.2.1, hr.1]
    have hu_norm : ‖-(w ^ 2)‖ ≤ lowerRmax c1 c := by
      rw [norm_neg, norm_pow, hw_norm, hRmax_eq]; nlinarith only [hr.2, hr_pos, hr₀_pos]
    have h_dphi : ‖deriv (phi c) (-(w ^ 2))‖ ≤ 2 := by
      have h1 := (hcl _ hu_norm).2
      have := norm_sub_norm_le (deriv (phi c) (-(w ^ 2))) 1
      rw [norm_one] at this
      linarith [h1.trans h_der]
    have h_env_ratio : airyEnv (phi c (-(w ^ 2))) ≤ Real.exp C_env * airyEnv (-(w ^ 2)) := by
      set M_e : ℝ := (5 / 2 * r₀) ^ 2 with hM_e
      have hM_e_nn : 0 ≤ M_e := sq_nonneg _
      have h1 : ‖-(w ^ 2)‖ ≤ M_e := by
        rw [norm_neg, norm_pow, hw_norm, hM_e]; nlinarith only [hr.2, hr_pos, hr₀_pos]
      have h2 : ‖phi c (-(w ^ 2))‖ ≤ M_e := by
        have h_d := (hcl _ hu_norm).1.trans h_err
        calc ‖phi c (-(w ^ 2))‖
            = ‖(phi c (-(w ^ 2)) - -(w ^ 2)) + -(w ^ 2)‖ := by ring_nf
          _ ≤ ‖phi c (-(w ^ 2)) - -(w ^ 2)‖ + ‖-(w ^ 2)‖ := norm_add_le _ _
          _ ≤ r₀ ^ 2 / 256 + (3 / 2 * r₀) ^ 2 := add_le_add h_d
              (by rw [norm_neg, norm_pow, hw_norm]; nlinarith only [hr.2, hr_pos, hr₀_pos])
          _ ≤ M_e := by rw [hM_e]; nlinarith only [hr₀_pos]
      have hr_ratio := lowerGood_airyEnv_ratio_le hM_e_nn h2 h1
      have h_exp_bd : 2 * √M_e * ‖phi c (-(w ^ 2)) - -(w ^ 2)‖ ≤ C_env := by
        rw [hM_e, Real.sqrt_sq (by positivity)]
        calc 2 * (5 / 2 * r₀) * ‖phi c (-(w ^ 2)) - -(w ^ 2)‖
            ≤ 2 * (5 / 2 * r₀) * (Cφ * c ^ (-(1 / 3 : ℝ))) := by gcongr; exact (hcl _ hu_norm).1
          _ = 5 * c1 * Cφ * (c ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ))) := by rw [hr₀_def]; ring
          _ = C_env := by rw [← Real.rpow_add hc_pos, add_neg_cancel, Real.rpow_zero, mul_one, hC_env]
      exact hr_ratio.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h_exp_bd) (airyEnv_pos _).le)
    have h_t2 : r ^ 2 * ‖airyF Ψ (phi c) (-(w ^ 2))‖ / airyEnv (-(w ^ 2)) ≤
        8 * Real.exp C_env * (r * ‖airyGReg Ψ A (lowerGoodWtilde phi c w)‖) := by
      have hF_eq_norm : ‖airyF Ψ (phi c) (-(w ^ 2))‖ =
          ‖Ψ (phi c (-(w ^ 2)))‖ * ‖deriv (phi c) (-(w ^ 2))‖ := by
        unfold airyF; rw [norm_mul]
      have h_pre := h_pre_lb (lowerGoodWtilde phi c w) hwt_A4
      have hGreg : ‖airyGReg Ψ A (lowerGoodWtilde phi c w)‖ =
          ‖(1 - lowerGoodWtilde phi c w ^ 2 / (A : ℂ) ^ 2) ^ 2‖ *
            ‖lowerGoodWtilde phi c w‖ *
            (‖Ψ (phi c (-(w ^ 2)))‖ / airyEnv (phi c (-(w ^ 2)))) := by
        unfold airyGReg
        rw [norm_mul, norm_mul, norm_mul,
          ← inv_inv ‖Complex.exp (4 / 3 * I * lowerGoodWtilde phi c w ^ 3)‖,
          ← h_env2.2, hwm.1, neg_neg]
        have henv := airyEnv_pos (phi c (-(w ^ 2)))
        field_simp [henv.ne']
      have h_ratio_nn : 0 ≤ ‖Ψ (phi c (-(w ^ 2)))‖ / airyEnv (phi c (-(w ^ 2))) :=
        div_nonneg (norm_nonneg _) (airyEnv_pos _).le
      have h_ge : r / 4 * (‖Ψ (phi c (-(w ^ 2)))‖ / airyEnv (phi c (-(w ^ 2)))) ≤
          ‖airyGReg Ψ A (lowerGoodWtilde phi c w)‖ := by
        rw [hGreg]
        have h1 : 1 / 2 * (r / 2) ≤
            ‖(1 - lowerGoodWtilde phi c w ^ 2 / (A : ℂ) ^ 2) ^ 2‖ * ‖lowerGoodWtilde phi c w‖ := by
          gcongr
        calc r / 4 * (‖Ψ (phi c (-(w ^ 2)))‖ / airyEnv (phi c (-(w ^ 2))))
            = (1 / 2 * (r / 2)) * (‖Ψ (phi c (-(w ^ 2)))‖ / airyEnv (phi c (-(w ^ 2)))) := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_right h1 h_ratio_nn
      have h_step1 : r ^ 2 * ‖airyF Ψ (phi c) (-(w ^ 2))‖ / airyEnv (-(w ^ 2)) ≤
          2 * Real.exp C_env * r ^ 2 *
            (‖Ψ (phi c (-(w ^ 2)))‖ / airyEnv (phi c (-(w ^ 2)))) := by
        rw [hF_eq_norm]
        have henv1 := airyEnv_pos (-(w ^ 2))
        have henv2 := airyEnv_pos (phi c (-(w ^ 2)))
        rw [div_le_iff₀ henv1]
        calc r ^ 2 * (‖Ψ (phi c (-(w ^ 2)))‖ * ‖deriv (phi c) (-(w ^ 2))‖)
            ≤ r ^ 2 * (‖Ψ (phi c (-(w ^ 2)))‖ * 2) := by gcongr
          _ = 2 * r ^ 2 * (‖Ψ (phi c (-(w ^ 2)))‖ / airyEnv (phi c (-(w ^ 2)))) *
                airyEnv (phi c (-(w ^ 2))) := by field_simp [henv2.ne']
          _ ≤ 2 * r ^ 2 * (‖Ψ (phi c (-(w ^ 2)))‖ / airyEnv (phi c (-(w ^ 2)))) *
                (Real.exp C_env * airyEnv (-(w ^ 2))) := by gcongr
          _ = _ := by ring
      calc r ^ 2 * ‖airyF Ψ (phi c) (-(w ^ 2))‖ / airyEnv (-(w ^ 2))
          ≤ 2 * Real.exp C_env * r ^ 2 *
              (‖Ψ (phi c (-(w ^ 2)))‖ / airyEnv (phi c (-(w ^ 2)))) := h_step1
        _ = 8 * Real.exp C_env * (r * (r / 4 *
              (‖Ψ (phi c (-(w ^ 2)))‖ / airyEnv (phi c (-(w ^ 2)))))) := by ring
        _ ≤ 8 * Real.exp C_env * (r * ‖airyGReg Ψ A (lowerGoodWtilde phi c w)‖) := by gcongr
    calc H (-(w ^ 2))
        = r ^ 2 * ‖Ψ (-(w ^ 2))‖ / airyEnv (-(w ^ 2)) +
            r ^ 2 * ‖airyF Ψ (phi c) (-(w ^ 2))‖ / airyEnv (-(w ^ 2)) := by
          dsimp [H]; ring
      _ ≤ 2 * (r * ‖airyGReg Ψ A w‖) +
            8 * Real.exp C_env * (r * ‖airyGReg Ψ A (lowerGoodWtilde phi c w)‖) :=
          add_le_add h_t1 h_t2
  -- Integrate `h_pt` over `φ ∈ (0, π)`
  -- Actually `fun φ => H (-((r * exp(φ * I))^2))` is continuous directly by `h_cont_H`!
  have h_int_H' : IntervalIntegrable (fun φ : ℝ => H (-(((r : ℂ) * Complex.exp (φ * I)) ^ 2))) volume 0 π := by
    have h_eq : (fun φ : ℝ => H (-(((r : ℂ) * Complex.exp (φ * I)) ^ 2))) =
        fun φ => H (circleMap 0 (r ^ 2) (2 * φ - π)) := by
      ext φ; congr 1
      rw [circleMap, zero_add, mul_pow, ← Complex.exp_nat_mul]
      have hexp : Complex.exp (((2 * φ - π : ℝ) : ℂ) * I) = -Complex.exp ((2 : ℕ) * (φ * I)) := by
        rw [show ((2 * φ - π : ℝ) : ℂ) * I = ((2 : ℕ) * (φ * I)) + (-(π : ℂ) * I) by push_cast; ring,
          Complex.exp_add, show -(π : ℂ) * I = -(π * I) by ring, Complex.exp_neg,
          Complex.exp_pi_mul_I]
        ring
      rw [hexp]; push_cast; ring
    rw [h_eq]
    exact (h_cont_H.comp (by fun_prop)).intervalIntegrable 0 π
  have h_mono := intervalIntegral.integral_mono_ae_restrict Real.pi_pos.le h_int_H'
    ((h_cont_1.intervalIntegrable_of_Icc Real.pi_pos.le).const_mul 2 |>.add
      ((h_cont_2.intervalIntegrable_of_Icc Real.pi_pos.le).const_mul (8 * Real.exp C_env)))
    (by
      have h0 : ∀ᵐ φ ∂(volume : Measure ℝ), φ ≠ (0 : ℝ) :=
        ae_iff.mpr (by simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, measure_singleton])
      have hπ : ∀ᵐ φ ∂(volume : Measure ℝ), φ ≠ π :=
        ae_iff.mpr (by simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, measure_singleton])
      filter_upwards [ae_restrict_of_ae h0, ae_restrict_of_ae hπ,
        ae_restrict_mem measurableSet_Icc] with φ hφ0 hφπ hmem
      exact h_pt φ ⟨lt_of_le_of_ne hmem.1 hφ0.symm, lt_of_le_of_ne hmem.2 hφπ⟩)
  refine h_mono.trans_eq ?_
  rw [intervalIntegral.integral_add
    ((h_cont_1.intervalIntegrable_of_Icc Real.pi_pos.le).const_mul 2)
    ((h_cont_2.intervalIntegrable_of_Icc Real.pi_pos.le).const_mul (8 * Real.exp C_env)),
    intervalIntegral.integral_const_mul (2 : ℝ),
    intervalIntegral.integral_const_mul (8 * Real.exp C_env)]

/-- info: 'FormalResearch.SignUncertainty.airy_eta_le_arcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airy_eta_le_arcs

end FormalResearch.SignUncertainty
