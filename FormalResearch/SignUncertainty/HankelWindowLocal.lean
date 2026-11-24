module

public import FormalResearch.SignUncertainty.HankelLocalDensity

/-!
# The local density with a window bound on `W̃_c` (`teb:mellin` (2)--(3); M5-S6b)

`hankel_local_density_window` refines `hankel_local_density_bound`: when `‖W̃_c(σ + iy)‖ ≤ W` is known only for
`|y - τ₀| ≤ h` (the window around the stationary point), the vertical piece of the contour shift is bounded by
`(10/9)² W P √(π/(2cσ/5))` inside the window plus `(4/3) P e^{-(2/5) c σ h²}` outside it (where the absolute
bound `‖J‖ ≤ 2 e^{c Re Φ}` of `norm_hankelJ_le` is used); the connectors are as before.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Asymptotics

/-- **Local density bound with a window** (proved).  `P = e^{c Re Φ(ζ₊; ℓ)}`, `ζ₊ = σ + iτ₀`. -/
theorem hankel_local_density_window {c ε : ℝ} (hc : 2 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) (ℓ : ℂ) (hl : ℓ.re ≤ 1 / 200)
    {σ τ0 : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 0.035) (hτ0 : |τ0| ≤ 0.035)
    (hcrit : gSer etaC ((σ : ℂ) + (τ0 : ℂ) * Complex.I) + ℓ = 0) {h W : ℝ} (hh : 0 ≤ h) (hW0 : 0 ≤ W)
    (hW : ∀ y : ℝ, |y| ≤ 1 / 3 → |y - τ0| ≤ h →
      ‖hankelWt c f ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ W) :
    ‖∫ τ in (-(1 / 3 : ℝ))..(1 / 3), hankelJ c f ℓ (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      Real.exp (c * (hankelLocPhi ℓ ((σ : ℂ) + (τ0 : ℂ) * Complex.I)).re) *
        ((100 / 81) * W * Real.sqrt (Real.pi / ((2 / 5) * c * σ)) +
          (4 / 3) * Real.exp (-((2 / 5) * c * σ * h ^ 2)) +
          2 * (2 * Real.exp (-(0.035 * c * σ)) / (0.07 * c))) := by
  have hc0 : 0 < c := by linarith
  set P := Real.exp (c * (hankelLocPhi ℓ ((σ : ℂ) + (τ0 : ℂ) * Complex.I)).re) with hP
  have hP0 : 0 < P := Real.exp_pos _
  set F := hankelJ c f ℓ with hF
  set z : ℂ := (σ : ℂ) + ((-(1 / 3 : ℝ) : ℝ) : ℂ) * Complex.I with hz
  set w : ℂ := ((1 / 10 : ℝ) : ℂ) + ((1 / 3 : ℝ) : ℂ) * Complex.I with hw
  have hzre : z.re = σ := by simp [hz]
  have hzim : z.im = -(1 / 3) := by simp [hz]
  have hwre : w.re = 1 / 10 := by simp [hw]
  have hwim : w.im = 1 / 3 := by simp [hw]
  have hdiff : DifferentiableOn ℂ F (uIcc z.re w.re ×ℂ uIcc z.im w.im) := by
    refine (hankelJ_differentiableOn hc0 hf ℓ).mono ?_
    intro p hp
    obtain ⟨hpre, hpim⟩ := hp
    rw [hzre, hwre, uIcc_of_le (by linarith)] at hpre
    rw [hzim, hwim, uIcc_of_le (by norm_num)] at hpim
    have hpn : ‖p‖ < 1 := by
      have := norm_line_lt (σ := p.re) (τ := p.im)
        (by rw [abs_of_pos (by linarith [hpre.1])]; linarith [hpre.2])
        (abs_le.2 ⟨by linarith [hpim.1], hpim.2⟩)
      rwa [Complex.re_add_im] at this
    exact ⟨by linarith [hpre.1], by linarith [hpre.2], hpn⟩
  have hC := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hdiff
  simp only [hzre, hzim, hwre, hwim] at hC
  set Ar : ℂ := ∫ y : ℝ in (-(1 / 3 : ℝ))..(1 / 3), F (((1 / 10 : ℝ) : ℂ) + (y : ℂ) * Complex.I) with hAr
  set Al : ℂ := ∫ y : ℝ in (-(1 / 3 : ℝ))..(1 / 3), F ((σ : ℂ) + (y : ℂ) * Complex.I) with hAl
  set B : ℂ := ∫ x : ℝ in σ..(1 / 10), F ((x : ℂ) + ((-(1 / 3 : ℝ) : ℝ) : ℂ) * Complex.I) with hB
  set T : ℂ := ∫ x : ℝ in σ..(1 / 10), F ((x : ℂ) + ((1 / 3 : ℝ) : ℂ) * Complex.I) with hT
  have hrel : Ar = Al + Complex.I * (B - T) := by
    simp only [smul_eq_mul] at hC
    linear_combination (-Complex.I) * hC + (Ar - Al) * Complex.I_sq
  -- the vertical piece, with the window
  have hvert : ‖Al‖ ≤ (100 / 81) * W * P * Real.sqrt (Real.pi / ((2 / 5) * c * σ)) +
      P * Real.exp (-((2 / 5) * c * σ * h ^ 2)) * (4 / 3) := by
    have hb0 : 0 < (2 / 5) * c * σ := by positivity
    have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := -(1 / 3 : ℝ)) (b := 1 / 3)
      (f := fun y : ℝ => F ((σ : ℂ) + (y : ℂ) * Complex.I))
      (g := fun y : ℝ => (100 / 81) * W * P * Real.exp (-((2 / 5) * c * σ) * (y - τ0) ^ 2) +
        2 * P * Real.exp (-((2 / 5) * c * σ * h ^ 2))) (by norm_num)
      (Eventually.of_forall fun y hy => by
        have hy' : y ∈ Icc (-(1 / 3 : ℝ)) (1 / 3) := ⟨hy.1.le, hy.2⟩
        have hyabs : |y| ≤ 1 / 3 := abs_le.2 hy'
        have h2 := hankelLocPhi_vert_gauss ℓ hc0 hσ0 (by linarith) (hτ0.trans (by norm_num)) hcrit y hy'
        have hG0 := Real.exp_pos (-((2 / 5) * c * σ) * (y - τ0) ^ 2)
        have hH0 := Real.exp_pos (-((2 / 5) * c * σ * h ^ 2))
        have hre : 0 < ((σ : ℂ) + (y : ℂ) * Complex.I).re := by simpa using hσ0
        have hre1 : ((σ : ℂ) + (y : ℂ) * Complex.I).re ≤ 1 / 10 := by simp; linarith
        have him : |((σ : ℂ) + (y : ℂ) * Complex.I).im| ≤ 1 / 3 := by simpa using hyabs
        by_cases hin : |y - τ0| ≤ h
        · have h1 := norm_hankelJ_le_wt hc f ℓ hre hre1
          have hWy := hW y hyabs hin
          have hE := Real.exp_pos (c * (hankelLocPhi ℓ ((σ : ℂ) + (y : ℂ) * Complex.I)).re)
          calc ‖F ((σ : ℂ) + (y : ℂ) * Complex.I)‖
              ≤ (10 / 9) * (10 / 9) * Real.exp (c * (hankelLocPhi ℓ ((σ : ℂ) + (y : ℂ) * Complex.I)).re) *
                ‖hankelWt c f ((σ : ℂ) + (y : ℂ) * Complex.I)‖ := h1
            _ ≤ (10 / 9) * (10 / 9) * (P * Real.exp (-((2 / 5) * c * σ) * (y - τ0) ^ 2)) * W := by gcongr
            _ ≤ _ := by nlinarith [mul_pos hP0 hH0]
        · push Not at hin
          have h1 := norm_hankelJ_le hc hf hε hM ℓ hre hre1 him
          have hsq : h ^ 2 ≤ (y - τ0) ^ 2 := by
            have : |h| ≤ |y - τ0| := by rw [abs_of_nonneg hh]; exact hin.le
            exact sq_le_sq.2 this
          have hexp : Real.exp (-((2 / 5) * c * σ) * (y - τ0) ^ 2) ≤ Real.exp (-((2 / 5) * c * σ * h ^ 2)) := by
            apply Real.exp_le_exp.2
            nlinarith [mul_le_mul_of_nonneg_left hsq hb0.le]
          have hW1 : 0 ≤ (100 / 81) * W * P * Real.exp (-((2 / 5) * c * σ) * (y - τ0) ^ 2) := by positivity
          calc ‖F ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ _ := h1
            _ ≤ 2 * (P * Real.exp (-((2 / 5) * c * σ) * (y - τ0) ^ 2)) := by gcongr
            _ ≤ 2 * (P * Real.exp (-((2 / 5) * c * σ * h ^ 2))) := by gcongr
            _ ≤ _ := by nlinarith)
      (by apply Continuous.intervalIntegrable; fun_prop)
    refine hle.trans ?_
    have hgi : IntervalIntegrable (fun y : ℝ => Real.exp (-((2 / 5) * c * σ) * (y - τ0) ^ 2)) volume
        (-(1 / 3 : ℝ)) (1 / 3) := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [intervalIntegral.integral_add (hgi.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul]
    have hgint := hankel_gauss_interval_le hb0 τ0
    have e1 : -((2 / 5) * c * σ) = -((2 / 5) * c * σ) := rfl
    have hcoef : 0 ≤ (100 / 81) * W * P := by positivity
    have hG : ∫ x : ℝ in (-(1 / 3 : ℝ))..(1 / 3), Real.exp (-((2 / 5) * c * σ) * (x - τ0) ^ 2) ≤
        Real.sqrt (Real.pi / ((2 / 5) * c * σ)) := hgint
    have hc2 : ∫ _x : ℝ in (-(1 / 3 : ℝ))..(1 / 3), 2 * P * Real.exp (-((2 / 5) * c * σ * h ^ 2)) =
        2 * P * Real.exp (-((2 / 5) * c * σ * h ^ 2)) * (2 / 3) := by
      rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
    rw [hc2]
    have := mul_le_mul_of_nonneg_left hG hcoef
    nlinarith
  -- the connectors
  have hconn : ∀ τ : ℝ, τ ^ 2 = 1 / 9 →
      ‖∫ x : ℝ in σ..(1 / 10), F ((x : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        2 * P * Real.exp (-(0.035 * c * σ)) / (0.07 * c) := by
    intro τ hτ
    have hτa := hankel_abs_eq_third hτ
    have ha : 0 < 0.07 * c := by positivity
    have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := σ) (b := 1 / 10)
      (f := fun x : ℝ => F ((x : ℂ) + (τ : ℂ) * Complex.I))
      (g := fun x : ℝ => 2 * P * Real.exp (-(0.035 * c * σ)) * Real.exp (-(0.07 * c) * (x - σ)))
      (by linarith)
      (Eventually.of_forall fun x hx => by
        have h1 := norm_hankelJ_le hc hf hε hM ℓ (ζ := (x : ℂ) + (τ : ℂ) * Complex.I)
          (by simp; linarith [hx.1]) (by simp; linarith [hx.2]) (by simpa using hτa)
        have h2 := hankelLocPhi_conn_total ℓ hl (c := c) hσ0 hσ hτ0 hcrit hτ hx.1.le (by linarith [hx.2])
        have h3 : Real.exp (c * (hankelLocPhi ℓ ((x : ℂ) + (τ : ℂ) * Complex.I)).re) ≤
            P * (Real.exp (-(0.035 * c * σ)) * Real.exp (-(0.07 * c) * (x - σ))) := by
          rw [hP, ← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.2
          nlinarith
        calc ‖F ((x : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ _ := h1
          _ ≤ 2 * (P * (Real.exp (-(0.035 * c * σ)) * Real.exp (-(0.07 * c) * (x - σ)))) := by gcongr
          _ = _ := by ring)
      (by apply Continuous.intervalIntegrable; fun_prop)
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have := hankel_exp_interval_le ha (show σ ≤ 1 / 10 by linarith)
    calc 2 * P * Real.exp (-(0.035 * c * σ)) * ∫ x : ℝ in σ..(1 / 10), Real.exp (-(0.07 * c) * (x - σ))
        ≤ 2 * P * Real.exp (-(0.035 * c * σ)) * (1 / (0.07 * c)) := by gcongr
      _ = _ := by field_simp
  have hB' := hconn (-(1 / 3)) (by norm_num)
  have hT' := hconn (1 / 3) (by norm_num)
  have hnorm : ‖Ar‖ ≤ ‖Al‖ + ‖B‖ + ‖T‖ := by
    rw [hrel]
    calc ‖Al + Complex.I * (B - T)‖ ≤ ‖Al‖ + ‖Complex.I * (B - T)‖ := norm_add_le _ _
      _ ≤ ‖Al‖ + (‖B‖ + ‖T‖) := by
        rw [norm_mul, Complex.norm_I, one_mul]; gcongr; exact norm_sub_le _ _
      _ = _ := by ring
  have hB'' : ‖B‖ ≤ 2 * P * Real.exp (-(0.035 * c * σ)) / (0.07 * c) := hB'
  have hT'' : ‖T‖ ≤ 2 * P * Real.exp (-(0.035 * c * σ)) / (0.07 * c) := hT'
  calc ‖Ar‖ ≤ ‖Al‖ + ‖B‖ + ‖T‖ := hnorm
    _ ≤ ((100 / 81) * W * P * Real.sqrt (Real.pi / ((2 / 5) * c * σ)) +
      P * Real.exp (-((2 / 5) * c * σ * h ^ 2)) * (4 / 3)) +
        2 * P * Real.exp (-(0.035 * c * σ)) / (0.07 * c) +
        2 * P * Real.exp (-(0.035 * c * σ)) / (0.07 * c) := by
        gcongr
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.hankel_local_density_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_local_density_window

end FormalResearch.SignUncertainty
