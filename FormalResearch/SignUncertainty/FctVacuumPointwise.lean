/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctVacuumCancel

/-!
# `VacPointwise` for the concrete datum: the pointwise facts of `fct:physical-budget` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:physical-budget` (a), (c), with Lemma `fct:comp-D` (1) (`(fct:Dstar-inner)`).

For the concrete datum `P = vacP` (`I_osc^{DH₀}(1 + Δ_curv ∘ τ₀)`, `vacD P = D_*`) and `u = m(t)`, `t = τ₀(u)`:
`D_*(u) = I_fl(u) · Q(t)`, `Q = r₀(t) e^{v(t)} (1 + Δ_curv(t)) - 1`.  **Proved here:**

* `vacQD_bounds`: `|Q| ≲ τ₁⁴` on `(0, 2τ₁]` (from the exact inner form `(fct:v-inner)`: `r₀ e^v = e^{-K₄t⁴ + αt² - Δ_curv}`),
  `|Q| ≲ t² + τ₁²` on `(0, 1/8]` (`|r₀ - 1| ≲ t²`, `|v| ≲ τ₁²`, `|Δ_curv| ≲ τ₁³`), `|Q| ≲ 1` on `[1/8, ∞)`
  (`r₀ ≲ 1`, from `F₀ ≲ e^{-πt}` and `m ≤ πt/2`), and `|Δ_curv| ≲ τ₁³ ≤ 1/2` everywhere;
* `uctM_two_gt_31`: `m(2τ₁) > 3.1 m(τ₁)` (so `τ₀(3.1 δ_L) < 2τ₁`);
* `vacPointwise_concrete`: the structure `VacPointwise` (measurability of `P`, `P ≥ 0` and the three bounds on `D_*`) for the concrete datum.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.CohnElkies FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCompD
  FormalResearch.SignUncertainty.FctPhiKill FormalResearch.SignUncertainty.FctMoment

/-- The pointwise facts on `P` (measurability, `P ≥ 0`, and the three pointwise bounds on `D_* = vacD P` from `(fct:Dstar-inner)`) used by
the vacuum integral. -/
structure VacPointwise (K a δ : ℝ) (P : ℝ → ℝ) : Prop where
  hPm : Measurable P
  hP0 : ∀ u, 0 < u → 0 ≤ P u
  hDin : ∀ u ∈ Icc δ (31 / 10 * δ), |vacD P u| ≤ K * Real.sqrt u
  hDmid : ∀ u ∈ Icc (3 * δ) (144 * δ), |vacD P u| ≤ K * a ^ 6 * u ^ (-(3 / 2 : ℝ))
  hDfar : ∀ u, 144 * δ ≤ u → |vacD P u| ≤ K * u ^ (-(1 / 2 : ℝ))

lemma kmono {x y K K' : ℝ} (hy : 0 ≤ y) (h : x ≤ K * y) (hK : K ≤ K') : x ≤ K' * y :=
  h.trans (mul_le_mul_of_nonneg_right hK hy)

lemma VacPointwise.mono {K K' a δ : ℝ} {P : ℝ → ℝ} (V : VacPointwise K a δ P) (hK : K ≤ K') (hδ : 0 ≤ δ) :
    VacPointwise K' a δ P := by
  refine ⟨V.hPm, V.hP0, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · exact kmono (Real.sqrt_nonneg u) (V.hDin u hu) hK
  · have hu0 : 0 ≤ u := by nlinarith [hu.1]
    have := V.hDmid u hu
    calc |vacD P u| ≤ K * a ^ 6 * u ^ (-(3 / 2 : ℝ)) := this
      _ ≤ K' * a ^ 6 * u ^ (-(3 / 2 : ℝ)) := by gcongr
  · have hu0 : 0 ≤ u := by nlinarith [hu]
    exact kmono (Real.rpow_nonneg hu0 _) (V.hDfar u hu) hK

/-! ### The data in the `t`-variable -/

/-- `Q(t) = r₀(t) e^{v(t)} (1 + Δ_curv(t)) - 1`, so that `D_*(m(t)) = I_fl(m(t)) Q(t)`. -/
noncomputable def vacQD (kind : StripKernelChoice) (K4 c α τ₁ t : ℝ) : ℝ :=
  stripR0 kind t * Real.exp (vTotal kind K4 c α τ₁ t) * (1 + stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t) - 1

lemma stripR0_pos (kind : StripKernelChoice) {t : ℝ} (ht : 0 < t) : 0 < stripR0 kind t := by
  unfold stripR0
  rw [ite_eq_right_iff.mpr fun h => absurd h ht.ne', abs_of_pos ht]
  have hmt := uctM_pos ht
  have hmd := uctMderiv_pos ht
  have hH : 0 < ‖stripH0 kind ((t : ℂ) * Complex.I)‖ := by
    cases kind
    · rw [norm_stripH0_star_imag ht]; positivity
    · rw [norm_stripH0_ce_imag ht]; positivity
  have := uctAlphaOsc_pos
  have := uctAlphaFl_pos
  positivity

lemma uctIfl_pos' {u : ℝ} (hu : 0 < u) : 0 < uctIfl u := by
  unfold uctIfl
  have := uctAlphaFl_pos
  positivity

/-- `P(u) = I_fl(u) · r₀(τ₀ u) e^{v(τ₀ u)} (1 + Δ_curv(τ₀ u))` for `u > 0`. -/
lemma vacP_eq (kind : StripKernelChoice) (K4 c α τ₁ : ℝ) {u : ℝ} (hu : 0 < u) :
    vacP kind K4 c α τ₁ u = uctIfl u * (vacQD kind K4 c α τ₁ (tau0 u) + 1) := by
  have ht := tau0_pos hu
  have hm : uctM (tau0 u) = u := ceEll_tau0 hu
  have h := stripR0_eq_div (kind := kind) ht
  rw [hm] at h
  have hfl := (uctIfl_pos' hu).ne'
  have hI : stripIosc kind u = stripR0 kind (tau0 u) * uctIfl u := by rw [h]; field_simp
  unfold vacP stripIoscD vacQD
  rw [hI]; ring

lemma vacD_eq (kind : StripKernelChoice) (K4 c α τ₁ : ℝ) {u : ℝ} (hu : 0 < u) :
    vacD (vacP kind K4 c α τ₁) u = uctIfl u * vacQD kind K4 c α τ₁ (tau0 u) := by
  unfold vacD
  rw [vacP_eq kind K4 c α τ₁ hu]; ring

/-! ### The ratio `r₀` -/

/-- `|r₀(t) - 1| ≤ C t²` on `(0, 1/8]` (`even_smooth_taylor_bound` for `r0Smooth`). -/
lemma stripR0_sub_one_le (kind : StripKernelChoice) :
    ∃ C ≥ 0, ∀ t ∈ Ioc (0 : ℝ) (1 / 8), |stripR0 kind t - 1| ≤ C * t ^ 2 := by
  obtain ⟨a, C, hC, hbd⟩ := even_smooth_taylor_bound (g := r0Smooth kind) (contDiffOn_r0Smooth kind)
    (fun t ht => r0Smooth_even ht) 1
  have h0 := hbd 0 ⟨le_rfl, by norm_num⟩
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.val_zero, mul_zero, pow_zero, mul_one,
    Finset.sum_singleton, r0Smooth_zero, zero_pow (two_ne_zero), mul_zero] at h0
  have ha : a 0 = 1 := by
    have := abs_nonpos_iff.mp h0
    linarith
  refine ⟨C, hC, fun t ht => ?_⟩
  have h := hbd t ⟨ht.1.le, ht.2⟩
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.val_zero, mul_zero, pow_zero, mul_one,
    Finset.sum_singleton, ha] at h
  rw [← r0Smooth_eq_stripR0 (by rw [abs_of_pos ht.1]; linarith [ht.2])]
  simpa using h

lemma uctM_le_linear {t : ℝ} (ht : 0 < t) : uctM t ≤ π * t / 2 := by
  have hx : 0 < π * t / 2 := by positivity
  have h := ceEll_lt hx
  have hs : π * t / 2 ≤ 3 * Real.sqrt (1 + (π * t / 2) ^ 2 / 3) := by
    have h3 : 0 ≤ Real.sqrt (1 + (π * t / 2) ^ 2 / 3) := Real.sqrt_nonneg _
    have h4 : Real.sqrt (1 + (π * t / 2) ^ 2 / 3) ^ 2 = 1 + (π * t / 2) ^ 2 / 3 :=
      Real.sq_sqrt (by positivity)
    nlinarith [sq_nonneg (π * t / 2 - 3 * Real.sqrt (1 + (π * t / 2) ^ 2 / 3))]
  have hpos : 0 < 3 * Real.sqrt (1 + (π * t / 2) ^ 2 / 3) := by positivity
  have h2 : (π * t / 2) ^ 2 / (3 * Real.sqrt (1 + (π * t / 2) ^ 2 / 3)) ≤ π * t / 2 := by
    rw [div_le_iff₀ hpos]; nlinarith
  exact (h.le.trans h2)

/-- `r₀(t) ≤ R` on `[1/8, ∞)` (`F₀ ≲ e^{-πt}`, `m ≤ πt/2`, `m' ≥ 1/(50(1+t))`). -/
lemma stripR0_large_le (kind : StripKernelChoice) : ∃ R ≥ 0, ∀ t : ℝ, 1 / 8 ≤ t → stripR0 kind t ≤ R := by
  obtain ⟨K, hK0, hK⟩ := vacF0_bounds kind
  obtain ⟨hmd, -⟩ := uct_m_lower_large
  have hfl := uctAlphaFl_pos
  refine ⟨50 * K * (24 * Real.exp 1) / uctAlphaFl, by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hF := (hK t ht0).2 ht
  have hm := uctM_pos ht0
  have hmd0 := uctMderiv_pos ht0
  set s : ℝ := π * t / 2 with hs
  have hts : t ≤ s := by rw [hs]; nlinarith [Real.pi_gt_three]
  have hms : uctM t ≤ s := uctM_le_linear ht0
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hm32 : uctM t ^ (3 / 2 : ℝ) ≤ (1 + s) ^ 2 := by
    calc uctM t ^ (3 / 2 : ℝ) ≤ (1 + s) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow hm.le (by linarith) (by norm_num)
      _ ≤ (1 + s) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (1 + s) ^ 2 := by rw [Real.rpow_two]
  have hm32p : 0 ≤ uctM t ^ (3 / 2 : ℝ) := Real.rpow_nonneg hm.le _
  have hX : uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ = vacF0 kind t * uctM t := by
    unfold vacF0; field_simp
  have hexp : (1 + s) ^ 4 ≤ 24 * Real.exp (1 + s) := by
    have := Real.pow_div_factorial_le_exp (1 + s) (by linarith) 4
    rw [div_le_iff₀ (by norm_num [Nat.factorial])] at this
    norm_num [Nat.factorial] at this
    linarith
  have hdecay : Real.exp (-(π * t)) * Real.exp (1 + s) ≤ Real.exp 1 := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : π * t = 2 * s := by rw [hs]; ring
    rw [this]; linarith
  unfold stripR0
  rw [ite_eq_right_iff.mpr fun h => absurd h ht0.ne', abs_of_pos ht0]
  rw [div_le_iff₀ (by positivity)]
  have hmdl : 1 / 50 / (1 + t) ≤ uctMderiv t := hmd t ht
  have hrhs : (50 * K * (24 * Real.exp 1) / uctAlphaFl) * (uctAlphaFl * uctMderiv t) ≥
      (50 * K * (24 * Real.exp 1) / uctAlphaFl) * (uctAlphaFl * (1 / 50 / (1 + t))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmdl hfl.le) (by positivity)
  have hE0 := Real.exp_pos (-(π * t))
  have h1 : (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖) * uctM t ^ (3 / 2 : ℝ) ≤
      K * Real.exp (-(π * t)) * ((1 + s) * (1 + s) ^ 2) := by
    rw [hX]
    have hF0 := vacF0_nonneg kind ht0
    calc vacF0 kind t * uctM t * uctM t ^ (3 / 2 : ℝ) = vacF0 kind t * (uctM t * uctM t ^ (3 / 2 : ℝ)) := by ring
      _ ≤ (K * Real.exp (-(π * t))) * ((1 + s) * (1 + s) ^ 2) := by
          apply mul_le_mul hF (mul_le_mul (by linarith) hm32 hm32p (by linarith)) (by positivity)
          positivity
  have h2 : (50 * K * (24 * Real.exp 1) / uctAlphaFl) * (uctAlphaFl * (1 / 50 / (1 + t))) =
      K * (24 * Real.exp 1) / (1 + t) := by
    field_simp
  refine h1.trans ?_
  refine le_trans ?_ hrhs
  rw [h2]
  have hpos : 0 < 1 + t := by linarith
  rw [le_div_iff₀ hpos]
  have h3 : K * Real.exp (-(π * t)) * ((1 + s) * (1 + s) ^ 2) * (1 + t) ≤
      K * (Real.exp (-(π * t)) * (1 + s) ^ 4) := by
    have hX : 0 ≤ (1 + s) * (1 + s) ^ 2 := by positivity
    have h5 : (1 + s) * (1 + s) ^ 2 * (1 + t) ≤ (1 + s) ^ 4 := by
      calc (1 + s) * (1 + s) ^ 2 * (1 + t) ≤ (1 + s) * (1 + s) ^ 2 * (1 + s) :=
            mul_le_mul_of_nonneg_left (by linarith only [hts]) hX
        _ = (1 + s) ^ 4 := by ring
    calc K * Real.exp (-(π * t)) * ((1 + s) * (1 + s) ^ 2) * (1 + t) =
          (K * Real.exp (-(π * t))) * ((1 + s) * (1 + s) ^ 2 * (1 + t)) := by ring
      _ ≤ (K * Real.exp (-(π * t))) * (1 + s) ^ 4 := mul_le_mul_of_nonneg_left h5 (mul_nonneg hK0 hE0.le)
      _ = _ := by ring
  refine h3.trans ?_
  have h4 : Real.exp (-(π * t)) * (1 + s) ^ 4 ≤ 24 * Real.exp 1 := by
    calc Real.exp (-(π * t)) * (1 + s) ^ 4 ≤ Real.exp (-(π * t)) * (24 * Real.exp (1 + s)) :=
          mul_le_mul_of_nonneg_left hexp hE0.le
      _ = 24 * (Real.exp (-(π * t)) * Real.exp (1 + s)) := by ring
      _ ≤ 24 * Real.exp 1 := by linarith only [hdecay]
  calc K * (Real.exp (-(π * t)) * (1 + s) ^ 4) ≤ K * (24 * Real.exp 1) := mul_le_mul_of_nonneg_left h4 hK0
    _ = _ := by ring

/-! ### Bounds on `Q` -/

lemma inner_Q_real {x Δ : ℝ} (hx : |x| ≤ 1) (hΔ : |Δ| ≤ 1 / 2) :
    |Real.exp x * (Real.exp (-Δ) * (1 + Δ)) - 1| ≤ 4 * |x| + 3 * Δ ^ 2 := by
  have h1 := Real.abs_exp_sub_one_le hx
  have h2 := Real.abs_exp_sub_one_sub_id_le (x := -Δ) (by rw [abs_neg]; linarith)
  have hΔ2 : Δ ^ 2 ≤ 1 / 4 := by nlinarith [abs_le.mp hΔ]
  have hΔ1 : |1 + Δ| ≤ 3 / 2 := by rw [abs_le] at *; constructor <;> linarith
  have hF : |Real.exp (-Δ) * (1 + Δ) - 1| ≤ 3 * Δ ^ 2 := by
    have e : Real.exp (-Δ) * (1 + Δ) - 1 = (Real.exp (-Δ) - 1 - (-Δ)) * (1 + Δ) - Δ ^ 2 := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_pow, sq_abs]
    have : |Real.exp (-Δ) - 1 - (-Δ)| * |1 + Δ| ≤ (-Δ) ^ 2 * (3 / 2) :=
      mul_le_mul h2 hΔ1 (abs_nonneg _) (sq_nonneg _)
    nlinarith [sq_nonneg Δ]
  have hF1 : |Real.exp (-Δ) * (1 + Δ)| ≤ 2 := by
    have := abs_sub_abs_le_abs_sub (Real.exp (-Δ) * (1 + Δ)) 1
    rw [abs_one] at this
    nlinarith
  have e : Real.exp x * (Real.exp (-Δ) * (1 + Δ)) - 1 =
      (Real.exp x - 1) * (Real.exp (-Δ) * (1 + Δ)) + (Real.exp (-Δ) * (1 + Δ) - 1) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have := mul_le_mul h1 hF1 (abs_nonneg _) (by positivity)
  nlinarith

lemma outer_Q_real {r v Δ : ℝ} (hv : |v| ≤ 1) (hΔ : |Δ| ≤ 1 / 2) :
    |r * Real.exp v * (1 + Δ) - 1| ≤ 9 / 2 * |r - 1| + 3 * |v| + |Δ| := by
  have h1 := Real.abs_exp_sub_one_le hv
  have hev : |Real.exp v| ≤ 3 := by
    have := abs_sub_abs_le_abs_sub (Real.exp v) 1
    rw [abs_one] at this; nlinarith
  have hΔ1 : |1 + Δ| ≤ 3 / 2 := by rw [abs_le] at *; constructor <;> linarith
  have e : r * Real.exp v * (1 + Δ) - 1 = (r - 1) * (Real.exp v * (1 + Δ)) + (Real.exp v - 1) * (1 + Δ) + Δ := by ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) le_rfl)
  · rw [abs_mul, abs_mul]
    have := mul_le_mul hev hΔ1 (abs_nonneg _) (by norm_num)
    nlinarith [abs_nonneg (r - 1)]
  · rw [abs_mul]
    have := mul_le_mul h1 hΔ1 (abs_nonneg _) (by positivity)
    nlinarith

/-- `|Δ_curv(t)| ≤ C τ₁³` for every `t > 0` (the three ranges of `stripDeltaCurv_bounds` combined). -/
lemma stripDeltaCurv_le_all (kind : StripKernelChoice) :
    ∃ τ₀ > 0, τ₀ ≤ 1 / 100 ∧ ∀ K4 : ℝ, 1 ≤ K4 → ∃ C ≥ 0, ∀ {c α τ₁ : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τ₀ →
      τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 →
      ∀ t : ℝ, 0 < t → |stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t| ≤ C * τ₁ ^ 3 := by
  obtain ⟨τ₀, hτ₀, hτ₀100, hd⟩ := stripDeltaCurv_bounds kind
  refine ⟨τ₀, hτ₀, hτ₀100, fun K4 hK4 => ?_⟩
  obtain ⟨C, hC, hCb⟩ := hd K4 hK4
  refine ⟨C, hC, fun {c α τ₁} hc hτ₁ hτ₁₀ hce hα t ht => ?_⟩
  obtain ⟨h1, h2, h3, -⟩ := hCb hc hτ₁ hτ₁₀ hce hα
  have hτ1 : τ₁ ≤ 1 := by linarith
  have hτ3 : 0 ≤ C * τ₁ ^ 3 := by positivity
  rcases le_or_gt t (12 * τ₁) with h12 | h12
  · exact h1 t ht h12
  rcases le_or_gt t (1 / 8) with h18 | h18
  · refine (h2 t h12.le h18).trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : (12 * τ₁) ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ (by positivity) h12.le 4
    have h7 : C * τ₁ ^ 7 = (C * τ₁ ^ 3) * τ₁ ^ 4 := by ring
    rw [h7]
    have : τ₁ ^ 4 ≤ t ^ 4 := by nlinarith [pow_pos hτ₁ 4]
    exact mul_le_mul_of_nonneg_left this hτ3
  · refine (h3 t h18.le).trans ?_
    have hex : (1 + t) * Real.exp (-(π / 2) * t) ≤ 1 := by
      have h1 : 1 + t ≤ Real.exp ((π / 2) * t) := by
        have := Real.add_one_le_exp ((π / 2) * t)
        nlinarith [Real.pi_gt_three]
      have h2 : Real.exp (-(π / 2) * t) * Real.exp ((π / 2) * t) = 1 := by
        rw [← Real.exp_add]; simp
      calc (1 + t) * Real.exp (-(π / 2) * t) ≤ Real.exp ((π / 2) * t) * Real.exp (-(π / 2) * t) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = 1 := by rw [mul_comm]; exact h2
    have h7 : τ₁ ^ 7 ≤ τ₁ ^ 3 := pow_le_pow_of_le_one hτ₁.le hτ1 (by norm_num)
    calc C * τ₁ ^ 7 * ((1 + t) * Real.exp (-(π / 2) * t)) ≤ C * τ₁ ^ 7 * 1 :=
          mul_le_mul_of_nonneg_left hex (by positivity)
      _ ≤ C * τ₁ ^ 3 := by rw [mul_one]; exact mul_le_mul_of_nonneg_left h7 hC

lemma inner_bound_real {K4 α τ₁ t Δ CD : ℝ} (hK4 : 0 ≤ K4) (hτ : 0 < τ₁) (hτ1 : τ₁ ≤ 1) (ht : 0 < t)
    (ht2 : t ≤ 2 * τ₁) (hα : |α| ≤ τ₁ ^ 2) (hΔt : |Δ| ≤ CD * τ₁ ^ 3) (hΔ12 : |Δ| ≤ 1 / 2)
    (hKτ : (16 * K4 + 4) * τ₁ ≤ 1 / 2) :
    |Real.exp (-(K4 * t ^ 4) + α * t ^ 2) * (Real.exp (-Δ) * (1 + Δ)) - 1| ≤
      (4 * (16 * K4 + 4) + 3 * CD ^ 2) * τ₁ ^ 4 := by
  have hτ4 : τ₁ ^ 4 ≤ τ₁ := pow_le_of_le_one hτ.le hτ1 (by norm_num)
  have h4 : t ^ 4 ≤ 16 * τ₁ ^ 4 := by
    have := pow_le_pow_left₀ ht.le ht2 4; calc t ^ 4 ≤ (2 * τ₁) ^ 4 := this
      _ = 16 * τ₁ ^ 4 := by ring
  have h2 : t ^ 2 ≤ 4 * τ₁ ^ 2 := by
    have := pow_le_pow_left₀ ht.le ht2 2; calc t ^ 2 ≤ (2 * τ₁) ^ 2 := this
      _ = 4 * τ₁ ^ 2 := by ring
  have h2a : |α * t ^ 2| ≤ 4 * τ₁ ^ 4 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
    calc |α| * t ^ 2 ≤ τ₁ ^ 2 * (4 * τ₁ ^ 2) := mul_le_mul hα h2 (sq_nonneg t) (sq_nonneg τ₁)
      _ = 4 * τ₁ ^ 4 := by ring
  have h4a : |K4 * t ^ 4| ≤ 16 * K4 * τ₁ ^ 4 := by
    rw [abs_mul, abs_of_nonneg hK4, abs_of_nonneg (by positivity)]
    calc K4 * t ^ 4 ≤ K4 * (16 * τ₁ ^ 4) := mul_le_mul_of_nonneg_left h4 hK4
      _ = 16 * K4 * τ₁ ^ 4 := by ring
  have hxb : |-(K4 * t ^ 4) + α * t ^ 2| ≤ (16 * K4 + 4) * τ₁ ^ 4 := by
    calc |-(K4 * t ^ 4) + α * t ^ 2| ≤ |-(K4 * t ^ 4)| + |α * t ^ 2| := abs_add_le _ _
      _ ≤ 16 * K4 * τ₁ ^ 4 + 4 * τ₁ ^ 4 := by rw [abs_neg]; exact add_le_add h4a h2a
      _ = (16 * K4 + 4) * τ₁ ^ 4 := by ring
  have hx1 : |-(K4 * t ^ 4) + α * t ^ 2| ≤ 1 := by
    refine hxb.trans ?_
    calc (16 * K4 + 4) * τ₁ ^ 4 ≤ (16 * K4 + 4) * τ₁ :=
          mul_le_mul_of_nonneg_left hτ4 (by positivity)
      _ ≤ 1 / 2 := hKτ
      _ ≤ 1 := by norm_num
  have hΔ2 : Δ ^ 2 ≤ CD ^ 2 * τ₁ ^ 4 := by
    have h := sq_le_sq' (by linarith [abs_nonneg Δ, neg_abs_le Δ, le_abs_self Δ] : -(CD * τ₁ ^ 3) ≤ Δ)
      (le_trans (le_abs_self Δ) hΔt)
    calc Δ ^ 2 ≤ (CD * τ₁ ^ 3) ^ 2 := h
      _ = CD ^ 2 * τ₁ ^ 6 := by ring
      _ ≤ CD ^ 2 * τ₁ ^ 4 := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hτ.le hτ1 (by norm_num)) (sq_nonneg CD)
  have := inner_Q_real hx1 hΔ12
  calc _ ≤ 4 * |-(K4 * t ^ 4) + α * t ^ 2| + 3 * Δ ^ 2 := this
    _ ≤ 4 * ((16 * K4 + 4) * τ₁ ^ 4) + 3 * (CD ^ 2 * τ₁ ^ 4) := by linarith only [hxb, hΔ2]
    _ = _ := by ring

/-- **Bounds on `Q = r₀ e^v (1 + Δ_curv) - 1`** for the concrete datum (`(fct:Dstar-inner)` and its continuation):
`|Δ_curv| ≤ 1/2` everywhere, `|Q| ≤ C τ₁⁴` on `(0, 2τ₁]`, `|Q| ≤ C (t² + τ₁²)` on `(0, 1/8]`, `|Q| ≤ C` on `[1/8, ∞)`. -/
theorem vacQD_bounds (kind : StripKernelChoice) :
    ∀ K4 : ℝ, 1 ≤ K4 → ∃ C ≥ 0, ∃ τ₀ > 0, τ₀ ≤ 1 / 100 ∧ ∀ {c α τ₁ : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τ₀ →
      τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 →
      (∀ t : ℝ, 0 < t → |stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t| ≤ 1 / 2) ∧
      (∀ t : ℝ, 0 < t → t ≤ 2 * τ₁ → |vacQD kind K4 c α τ₁ t| ≤ C * τ₁ ^ 4) ∧
      (∀ t : ℝ, 0 < t → t ≤ 1 / 8 → |vacQD kind K4 c α τ₁ t| ≤ C * (t ^ 2 + τ₁ ^ 2)) ∧
      (∀ t : ℝ, 1 / 8 ≤ t → |vacQD kind K4 c α τ₁ t| ≤ C) := by
  obtain ⟨τa, hτa, hτa100, hΔall⟩ := stripDeltaCurv_le_all kind
  obtain ⟨τb, hτb, hV⟩ := vTotal_bounds kind
  obtain ⟨τc, hτc, hτc20, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpart1⟩ :=
    fct_comp_D_part1 kind
  obtain ⟨Cr, hCr, hr⟩ := stripR0_sub_one_le kind
  obtain ⟨R, hR0, hR⟩ := stripR0_large_le kind
  intro K4 hK4
  obtain ⟨CD, hCD, hΔ⟩ := hΔall K4 hK4
  obtain ⟨M, hM0, hVb⟩ := hV K4 hK4
  have hK40 : 0 ≤ K4 := by linarith
  set C1 : ℝ := 4 * (16 * K4 + 4) + 3 * CD ^ 2 with hC1
  set C2 : ℝ := max (9 / 2 * Cr) (3 * M + CD) with hC2
  set C3 : ℝ := 3 / 2 * R + 1 with hC3
  refine ⟨max C1 (max C2 C3), by positivity, min (min (min τa τb) (min τc (1 / 100)))
    (min (1 / (2 * (M + CD + 1))) (1 / (2 * (16 * K4 + 4)))),
    lt_min (lt_min (lt_min hτa hτb) (lt_min hτc (by norm_num))) (lt_min (by positivity) (by positivity)),
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)),
    fun {c α τ₁} hc hτ₁ hτ₁₀ hce hα => ?_⟩
  have hτa' : τ₁ ≤ τa := hτ₁₀.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hτb' : τ₁ ≤ τb := hτ₁₀.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hτc' : τ₁ ≤ τc := hτ₁₀.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hτ100 : τ₁ ≤ 1 / 100 := hτ₁₀.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hτM : τ₁ ≤ 1 / (2 * (M + CD + 1)) := hτ₁₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτK : τ₁ ≤ 1 / (2 * (16 * K4 + 4)) := hτ₁₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hτ1 : τ₁ ≤ 1 := by linarith
  have hτ2 : τ₁ ^ 2 ≤ τ₁ := pow_le_of_le_one hτ₁.le hτ1 (by norm_num)
  have hτ3 : τ₁ ^ 3 ≤ τ₁ ^ 2 := pow_le_pow_of_le_one hτ₁.le hτ1 (by norm_num)
  have hτ4 : τ₁ ^ 4 ≤ τ₁ ^ 2 := pow_le_pow_of_le_one hτ₁.le hτ1 (by norm_num)
  have hτ6 : τ₁ ^ 6 ≤ τ₁ ^ 4 := pow_le_pow_of_le_one hτ₁.le hτ1 (by norm_num)
  have hCDτ : CD * τ₁ ≤ 1 / 2 := by
    have : τ₁ * (2 * (M + CD + 1)) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hτM
    linarith only [this, mul_nonneg hM0 hτ₁.le, mul_nonneg hCD hτ₁.le, hτ₁.le]
  have hMτ : M * τ₁ ≤ 1 / 2 := by
    have : τ₁ * (2 * (M + CD + 1)) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hτM
    linarith only [this, mul_nonneg hM0 hτ₁.le, mul_nonneg hCD hτ₁.le, hτ₁.le]
  have hKτ : (16 * K4 + 4) * τ₁ ≤ 1 / 2 := by
    have : τ₁ * (2 * (16 * K4 + 4)) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hτK
    linarith only [this]
  have hΔb : ∀ t : ℝ, 0 < t → |stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t| ≤ 1 / 2 := fun t ht =>
    (hΔ hc hτ₁ hτa' hce hα t ht).trans (by linarith only [mul_le_mul_of_nonneg_left (hτ3.trans hτ2) hCD, hCDτ])
  obtain ⟨hv_cont, hv_bd, hv_zero⟩ := hVb hc hτ₁ hτb' hce hα
  have hvτ : ∀ t, |vTotal kind K4 c α τ₁ t| ≤ 1 := fun t =>
    (hv_bd t).trans (by linarith only [mul_le_mul_of_nonneg_left hτ2 hM0, hMτ])
  refine ⟨hΔb, fun t ht ht2 => ?_, fun t ht ht8 => ?_, fun t ht8 => ?_⟩
  · -- inner
    obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _, _, hinner, _⟩ := hpart1 hK4 hc hτ₁ hτc' hce hα
    have hin := ((hinner t (by rw [abs_of_pos ht]; exact ht2)).2.2.2.2.2 ht.ne').2.2
    have hr0 := stripR0_pos kind ht
    have hratio : stripIosc kind (uctM t) / uctIfl (uctM t) = stripR0 kind t := (stripR0_eq_div ht).symm
    rw [hratio] at hin
    set Δ := stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t with hΔdef
    have hexp : stripR0 kind t * Real.exp (vTotal kind K4 c α τ₁ t) * (1 + Δ) =
        Real.exp (-(K4 * t ^ 4) + α * t ^ 2) * (Real.exp (-Δ) * (1 + Δ)) := by
      rw [hin, show -Real.log (stripR0 kind t) - K4 * t ^ 4 - Δ + α * t ^ 2 =
        -Real.log (stripR0 kind t) + ((-(K4 * t ^ 4) + α * t ^ 2) + -Δ) by ring, Real.exp_add, Real.exp_add, Real.exp_neg,
        Real.exp_log hr0]
      field_simp
    have := inner_bound_real hK40 hτ₁ hτ1 ht ht2 hα (hΔ hc hτ₁ hτa' hce hα t ht) (hΔb t ht) hKτ
    unfold vacQD
    rw [hexp]
    refine this.trans ?_
    rw [← hC1]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · -- up to `1/8`
    have hr' := hr t ⟨ht, ht8⟩
    have hv' := hv_bd t
    have hΔt : |stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t| ≤ CD * τ₁ ^ 2 :=
      (hΔ hc hτ₁ hτa' hce hα t ht).trans (mul_le_mul_of_nonneg_left hτ3 hCD)
    have := outer_Q_real (r := stripR0 kind t) (hvτ t) (hΔb t ht)
    unfold vacQD
    refine this.trans ?_
    have h1 : 9 / 2 * |stripR0 kind t - 1| ≤ C2 * t ^ 2 := by
      calc 9 / 2 * |stripR0 kind t - 1| ≤ 9 / 2 * (Cr * t ^ 2) := by linarith
        _ = (9 / 2 * Cr) * t ^ 2 := by ring
        _ ≤ C2 * t ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg t)
    have h2 : 3 * |vTotal kind K4 c α τ₁ t| + |stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t| ≤ C2 * τ₁ ^ 2 := by
      calc _ ≤ 3 * (M * τ₁ ^ 2) + CD * τ₁ ^ 2 := by linarith
        _ = (3 * M + CD) * τ₁ ^ 2 := by ring
        _ ≤ C2 * τ₁ ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg τ₁)
    calc _ ≤ C2 * t ^ 2 + C2 * τ₁ ^ 2 := by linarith
      _ = C2 * (t ^ 2 + τ₁ ^ 2) := by ring
      _ ≤ _ := by
        have : C2 ≤ max C1 (max C2 C3) := (le_max_left _ _).trans (le_max_right _ _)
        exact mul_le_mul_of_nonneg_right this (by positivity)
  · -- large `t`
    have ht0 : 0 < t := by linarith
    have hv0 : vTotal kind K4 c α τ₁ t = 0 := hv_zero t (by linarith)
    have hΔt := hΔb t ht0
    have hr := hR t ht8
    have hr0 := stripR0_pos kind ht0
    unfold vacQD
    rw [hv0, Real.exp_zero, mul_one]
    have hΔ1 : |1 + stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t| ≤ 3 / 2 := by
      rw [abs_le] at *; constructor <;> linarith
    have : |stripR0 kind t * (1 + stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t)| ≤ R * (3 / 2) := by
      rw [abs_mul, abs_of_pos hr0]
      exact mul_le_mul hr hΔ1 (abs_nonneg _) hR0
    calc _ ≤ |stripR0 kind t * (1 + stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t)| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ C3 := by rw [abs_one, hC3]; linarith
      _ ≤ max C1 (max C2 C3) := (le_max_right C2 C3).trans (le_max_right C1 _)

/-- `m(2τ) > 3.1 m(τ)` for `0 < τ ≤ 1/20` (the sharpening of `saddleTau0_three_uctM_bounds` from `3` to `3.1`). -/
lemma uctM_two_gt_31 {τ : ℝ} (hτ : 0 < τ) (hτ20 : τ ≤ 1 / 20) : 31 / 10 * uctM τ < uctM (2 * τ) := by
  have hx1 : 0 < π * τ / 2 := by positivity
  have hx1_le : π * τ / 2 ≤ 1 / 2 := by nlinarith [Real.pi_lt_four]
  have hx2 : 0 < π * (2 * τ) / 2 := by positivity
  have hx2_le : π * (2 * τ) / 2 ≤ 1 / 2 := by nlinarith [Real.pi_lt_four]
  have h1 := ceEll_taylor4 hx1 hx1_le
  have h2 := ceEll_taylor4 hx2 hx2_le
  rw [abs_le] at h1 h2
  set x : ℝ := π * τ / 2 with hxdef
  have hx_lt : x ≤ 1 / 10 := by rw [hxdef]; nlinarith [Real.pi_lt_four]
  have hx2_eq : π * (2 * τ) / 2 = 2 * x := by rw [hxdef]; ring
  rw [hx2_eq] at h2
  have hx2_le_100 : x ^ 2 ≤ 1 / 100 := by
    have := pow_le_pow_left₀ hx1.le hx_lt 2; norm_num at this; exact this
  have hx4_le : x ^ 4 ≤ (1 / 100) * x ^ 2 := by
    rw [show x ^ 4 = x ^ 2 * x ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hx2_le_100 (sq_nonneg x)
  have hx6_le : x ^ 6 ≤ (1 / 10000) * x ^ 2 := by
    rw [show x ^ 6 = x ^ 2 * x ^ 4 by ring]
    calc x ^ 2 * x ^ 4 ≤ (1 / 100) * ((1 / 100) * x ^ 2) :=
          mul_le_mul hx2_le_100 hx4_le (pow_nonneg hx1.le 4) (by norm_num)
      _ = (1 / 10000) * x ^ 2 := by ring
  have hx_sq_pos : 0 < x ^ 2 := sq_pos_of_pos hx1
  have hx4_nn : 0 ≤ x ^ 4 := pow_nonneg hx1.le 4
  have hx6_nn : 0 ≤ x ^ 6 := pow_nonneg hx1.le 6
  have hu := h1.2
  have hl := h2.1
  have e : (2 * x) ^ 2 / 3 - 7 / 90 * (2 * x) ^ 4 - 20 * (2 * x) ^ 6 =
      (4 / 3) * x ^ 2 - (56 / 45) * x ^ 4 - 1280 * x ^ 6 := by ring
  unfold uctM
  rw [hx2_eq]
  show 31 / 10 * ceEll x < ceEll (2 * x)
  nlinarith only [hu, hl, e, hx4_le, hx6_le, hx_sq_pos, hx4_nn, hx6_nn]

/-! ### Measurability and positivity of `P` -/

lemma measurable_uctM : Measurable uctM := by
  unfold uctM ceEll
  have : Measurable Real.tanh := by
    unfold Real.tanh; fun_prop
  fun_prop

lemma measurable_uctMderiv : Measurable uctMderiv := by
  unfold uctMderiv uctEllDeriv
  fun_prop

lemma measurable_stripIosc (kind : StripKernelChoice) : Measurable (stripIosc kind) := by
  cases kind
  · unfold stripIosc uctIoscStar uctHstar
    have := tau0_measurable
    have := measurable_uctMderiv
    fun_prop
  · unfold stripIosc uctIoscCE uctHCE
    have := tau0_measurable
    have := measurable_uctMderiv
    fun_prop

lemma measurable_stripDeltaCurv (c : ℝ) (θ : ℝ → ℝ) : Measurable (stripDeltaCurv c θ) := by
  unfold stripDeltaCurv
  have h1 : Measurable (deriv θ) := measurable_deriv θ
  have h2 : Measurable (iteratedDeriv 2 θ) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]; exact measurable_deriv _
  have := measurable_uctMderiv
  have := measurable_uctM
  fun_prop

lemma measurable_vacP (kind : StripKernelChoice) {K4 c α τ₁ : ℝ} (hv : Continuous (vTotal kind K4 c α τ₁)) :
    Measurable (vacP kind K4 c α τ₁) := by
  unfold vacP stripIoscD
  have := tau0_measurable
  have := measurable_stripIosc kind
  have := measurable_stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁))
  have := hv.measurable
  fun_prop

/-! ### Assembly -/

lemma tau0_lt_of_lt {u τ : ℝ} (hτ : 0 < τ) (hu : 0 < u) (h : u < uctM τ) : tau0 u < τ := by
  by_contra hle
  push Not at hle
  have := uctM_strictMonoOn.monotoneOn (mem_Ioi.mpr hτ) (mem_Ioi.mpr (tau0_pos hu)) hle
  have hm : uctM (tau0 u) = u := ceEll_tau0 hu
  linarith

lemma le_tau0_of_le {u τ : ℝ} (hτ : 0 < τ) (hu : uctM τ ≤ u) : τ ≤ tau0 u := by
  have hu0 : 0 < u := (uctM_pos hτ).trans_le hu
  by_contra hlt
  push Not at hlt
  have := uctM_strictMonoOn (mem_Ioi.mpr (tau0_pos hu0)) (mem_Ioi.mpr hτ) hlt
  have hm : uctM (tau0 u) = u := ceEll_tau0 hu0
  linarith

lemma rpow_three_halves_mul {u : ℝ} (hu : 0 < u) : u ^ (-(3 / 2 : ℝ)) * u = u ^ (-(1 / 2 : ℝ)) := by
  have := Real.rpow_add hu (-(3 / 2 : ℝ)) 1
  rw [Real.rpow_one] at this
  rw [← this]; norm_num

lemma rpow_three_halves_mul_sq {u : ℝ} (hu : 0 < u) : u ^ (-(3 / 2 : ℝ)) * u ^ 2 = Real.sqrt u := by
  have := Real.rpow_add hu (-(3 / 2 : ℝ)) 2
  rw [Real.rpow_two] at this
  rw [← this, Real.sqrt_eq_rpow]; norm_num

lemma abs_vacD_le (kind : StripKernelChoice) (K4 c α τ₁ : ℝ) {u : ℝ} (hu : 0 < u) {B : ℝ}
    (hB : |vacQD kind K4 c α τ₁ (tau0 u)| ≤ B) :
    |vacD (vacP kind K4 c α τ₁) u| ≤ uctAlphaFl * u ^ (-(3 / 2 : ℝ)) * B := by
  rw [vacD_eq kind K4 c α τ₁ hu, abs_mul, abs_of_pos (uctIfl_pos' hu)]
  exact mul_le_mul_of_nonneg_left hB (uctIfl_pos' hu).le

/-- **`VacPointwise` for the concrete datum** (`fct:physical-budget` (a), (c) with `(fct:Dstar-inner)`): for every `K4 ≥ 1` there are
`K` and `τ₀ > 0` such that, for `τ₁ ≤ τ₀`, `τ₁⁴ c = 1`, `|α| ≤ τ₁²`, `a³ = τ₁`, the pointwise facts on `P = vacP` hold:
measurability, `P ≥ 0`, `|D_*| ≤ K √u` on `[δ_L, 3.1 δ_L]`, `|D_*| ≤ K a⁶ u^{-3/2}` on `[3δ_L, 144 δ_L]` and `|D_*| ≤ K u^{-1/2}` on
`[144 δ_L, ∞)`, with `δ_L = m(τ₁)`. -/
theorem vacPointwise_concrete (kind : StripKernelChoice) :
    ∀ K4 : ℝ, 1 ≤ K4 → ∃ K : ℝ, ∃ τ₀ > 0, 1 ≤ K ∧ ∀ {c α τ₁ a : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τ₀ →
      τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 → 0 < a → a ^ 3 = τ₁ →
      VacPointwise K a (uctM τ₁) (vacP kind K4 c α τ₁) := by
  intro K4 hK4
  obtain ⟨CQ, hCQ, τq, hτq, hτq100, hQ⟩ := vacQD_bounds kind K4 hK4
  obtain ⟨τb, hτb, hV⟩ := vTotal_bounds kind
  obtain ⟨cm, hcm, hcm_bd⟩ := uct_m_lower_small
  obtain ⟨Cu, hCu, hCu_bd⟩ := uct_m_upper_small
  obtain ⟨-, hm_large⟩ := uct_m_lower_large
  obtain ⟨M, hM0, hVb⟩ := hV K4 hK4
  have hm18 : 0 < uctM (1 / 8) := uctM_pos (by norm_num)
  have hfl := uctAlphaFl_pos
  set K : ℝ := 1 + uctAlphaFl * CQ * (cm⁻¹ ^ 2 + 144 * Cu * cm⁻¹ + 1 + 2 * cm⁻¹ + (uctM (1 / 8))⁻¹) with hK
  have hKpos : 0 ≤ uctAlphaFl * CQ * (cm⁻¹ ^ 2 + 144 * Cu * cm⁻¹ + 1 + 2 * cm⁻¹ + (uctM (1 / 8))⁻¹) := by positivity
  refine ⟨K, min (min τq τb) (uctM (1 / 8) / (144 * Cu + 1)), lt_min (lt_min hτq hτb) (by positivity),
    by rw [hK]; linarith, fun {c α τ₁ a} hc hτ₁ hτ₁₀ hce hα ha ha3 => ?_⟩
  have hτq' : τ₁ ≤ τq := hτ₁₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hτb' : τ₁ ≤ τb := hτ₁₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hτm : τ₁ ≤ uctM (1 / 8) / (144 * Cu + 1) := hτ₁₀.trans (min_le_right _ _)
  have hτ100 : τ₁ ≤ 1 / 100 := hτq'.trans hτq100
  have hτ1 : τ₁ ≤ 1 := by linarith
  obtain ⟨hΔb, hQin, hQmid, hQlarge⟩ := hQ hc hτ₁ hτq' hce hα
  obtain ⟨hv_cont, -, -⟩ := hVb hc hτ₁ hτb' hce hα
  have hδ_lo : cm * τ₁ ^ 2 ≤ uctM τ₁ := (hcm_bd τ₁ ⟨hτ₁, by linarith⟩).1
  have hδ_hi : uctM τ₁ ≤ Cu * τ₁ ^ 2 := hCu_bd τ₁ ⟨hτ₁, by linarith⟩
  have hδ0 : 0 < uctM τ₁ := uctM_pos hτ₁
  have ha6 : a ^ 6 = τ₁ ^ 2 := by rw [← ha3]; ring
  have hCu144 : 144 * Cu * τ₁ ^ 2 < uctM (1 / 8) := by
    have h1 : τ₁ * (144 * Cu + 1) ≤ uctM (1 / 8) := by rwa [le_div_iff₀ (by positivity)] at hτm
    have h2 : τ₁ ^ 2 ≤ τ₁ := pow_le_of_le_one hτ₁.le hτ1 (by norm_num)
    linarith only [mul_le_mul_of_nonneg_left h2 (show 0 ≤ 144 * Cu by positivity), h1, hτ₁]
  refine ⟨measurable_vacP kind hv_cont, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · -- `P ≥ 0`
    rw [vacP_eq kind K4 c α τ₁ hu]
    have ht := tau0_pos hu
    have h1 : 0 < 1 + stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) (tau0 u) := by
      have := abs_le.mp (hΔb _ ht); linarith [this.1]
    have : vacQD kind K4 c α τ₁ (tau0 u) + 1 = stripR0 kind (tau0 u) * Real.exp (vTotal kind K4 c α τ₁ (tau0 u)) *
        (1 + stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) (tau0 u)) := by unfold vacQD; ring
    rw [this]
    have := stripR0_pos kind ht
    have := uctIfl_pos' hu
    positivity
  · -- inner
    have hu0 : 0 < u := hδ0.trans_le hu.1
    have ht := tau0_pos hu0
    have hlt : u < uctM (2 * τ₁) := lt_of_le_of_lt hu.2 (by
      have := uctM_two_gt_31 hτ₁ (by linarith); linarith)
    have ht2 : tau0 u ≤ 2 * τ₁ := (tau0_lt_of_lt (by positivity) hu0 hlt).le
    have hB := hQin _ ht ht2
    have h1 := abs_vacD_le kind K4 c α τ₁ hu0 hB
    refine h1.trans ?_
    have hu_lo : cm * τ₁ ^ 2 ≤ u := hδ_lo.trans hu.1
    have hτ4 : τ₁ ^ 4 ≤ u ^ 2 / cm ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : (cm * τ₁ ^ 2) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hu_lo 2
      calc τ₁ ^ 4 * cm ^ 2 = (cm * τ₁ ^ 2) ^ 2 := by ring
        _ ≤ u ^ 2 := this
    calc uctAlphaFl * u ^ (-(3 / 2 : ℝ)) * (CQ * τ₁ ^ 4) ≤ uctAlphaFl * u ^ (-(3 / 2 : ℝ)) * (CQ * (u ^ 2 / cm ^ 2)) := by
          gcongr
      _ = (uctAlphaFl * CQ * cm⁻¹ ^ 2) * (u ^ (-(3 / 2 : ℝ)) * u ^ 2) := by field_simp
      _ = (uctAlphaFl * CQ * cm⁻¹ ^ 2) * Real.sqrt u := by rw [rpow_three_halves_mul_sq hu0]
      _ ≤ K * Real.sqrt u := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg u)
          rw [hK]
          have : cm⁻¹ ^ 2 ≤ cm⁻¹ ^ 2 + 144 * Cu * cm⁻¹ + 1 + 2 * cm⁻¹ + (uctM (1 / 8))⁻¹ := by
            have : 0 ≤ 144 * Cu * cm⁻¹ + 1 + 2 * cm⁻¹ + (uctM (1 / 8))⁻¹ := by positivity
            linarith
          linarith only [mul_le_mul_of_nonneg_left this (show 0 ≤ uctAlphaFl * CQ by positivity)]
  · -- middle
    have hu0 : 0 < u := by have := hδ0; linarith [hu.1]
    have ht := tau0_pos hu0
    have hmt : uctM (tau0 u) = u := ceEll_tau0 hu0
    have ht18 : tau0 u ≤ 1 / 8 := by
      by_contra hgt
      push Not at hgt
      have h1 := hm_large _ hgt.le
      rw [hmt] at h1
      linarith only [h1, hu.2, hδ_hi, hCu144]
    have hτt : τ₁ ≤ tau0 u := le_tau0_of_le hτ₁ (by linarith [hu.1])
    have hB := hQmid _ ht ht18
    have h1 := abs_vacD_le kind K4 c α τ₁ hu0 hB
    refine h1.trans ?_
    have ht2 : tau0 u ^ 2 ≤ 144 * Cu / cm * τ₁ ^ 2 := by
      have := (hcm_bd _ ⟨ht, ht18⟩).1
      rw [hmt] at this
      rw [div_mul_eq_mul_div, le_div_iff₀ hcm]
      linarith only [this, hu.2, hδ_hi]
    have hB2 : CQ * (tau0 u ^ 2 + τ₁ ^ 2) ≤ CQ * (144 * Cu / cm + 1) * τ₁ ^ 2 := by
      linarith only [mul_le_mul_of_nonneg_left ht2 hCQ]
    rw [ha6]
    calc uctAlphaFl * u ^ (-(3 / 2 : ℝ)) * (CQ * (tau0 u ^ 2 + τ₁ ^ 2)) ≤
          uctAlphaFl * u ^ (-(3 / 2 : ℝ)) * (CQ * (144 * Cu / cm + 1) * τ₁ ^ 2) := by gcongr
      _ = (uctAlphaFl * CQ * (144 * Cu * cm⁻¹ + 1)) * τ₁ ^ 2 * u ^ (-(3 / 2 : ℝ)) := by field_simp
      _ ≤ K * τ₁ ^ 2 * u ^ (-(3 / 2 : ℝ)) := by
          have hp : 0 ≤ τ₁ ^ 2 * u ^ (-(3 / 2 : ℝ)) := by positivity
          have : uctAlphaFl * CQ * (144 * Cu * cm⁻¹ + 1) ≤ K := by
            rw [hK]
            have : 144 * Cu * cm⁻¹ + 1 ≤ cm⁻¹ ^ 2 + 144 * Cu * cm⁻¹ + 1 + 2 * cm⁻¹ + (uctM (1 / 8))⁻¹ := by
              have : 0 ≤ cm⁻¹ ^ 2 + 2 * cm⁻¹ + (uctM (1 / 8))⁻¹ := by positivity
              linarith
            linarith only [mul_le_mul_of_nonneg_left this (show 0 ≤ uctAlphaFl * CQ by positivity)]
          have hp' := mul_le_mul_of_nonneg_right this hp
          calc _ = (uctAlphaFl * CQ * (144 * Cu * cm⁻¹ + 1)) * (τ₁ ^ 2 * u ^ (-(3 / 2 : ℝ))) := by ring
            _ ≤ K * (τ₁ ^ 2 * u ^ (-(3 / 2 : ℝ))) := hp'
            _ = _ := by ring
  · -- far
    have hu0 : 0 < u := by have := hδ0; nlinarith [hu]
    have ht := tau0_pos hu0
    have hmt : uctM (tau0 u) = u := ceEll_tau0 hu0
    have hτt : τ₁ ≤ tau0 u := le_tau0_of_le hτ₁ (by linarith)
    have hKfar : ∀ L : ℝ, 0 ≤ L → L ≤ 2 * cm⁻¹ + (uctM (1 / 8))⁻¹ →
        uctAlphaFl * CQ * L ≤ K := by
      intro L hL0 hL
      rw [hK]
      have : L ≤ cm⁻¹ ^ 2 + 144 * Cu * cm⁻¹ + 1 + 2 * cm⁻¹ + (uctM (1 / 8))⁻¹ := by
        have : 0 ≤ cm⁻¹ ^ 2 + 144 * Cu * cm⁻¹ + 1 := by positivity
        linarith
      linarith only [mul_le_mul_of_nonneg_left this (show 0 ≤ uctAlphaFl * CQ by positivity)]
    rcases le_or_gt (tau0 u) (1 / 8) with ht18 | ht18
    · have hB := hQmid _ ht ht18
      have ht2 : tau0 u ^ 2 ≤ u / cm := by
        have := (hcm_bd _ ⟨ht, ht18⟩).1
        rw [hmt] at this
        rw [le_div_iff₀ hcm]; linarith only [this]
      have hτ2 : τ₁ ^ 2 ≤ tau0 u ^ 2 := pow_le_pow_left₀ hτ₁.le hτt 2
      have hB2 : CQ * (tau0 u ^ 2 + τ₁ ^ 2) ≤ (2 * CQ * cm⁻¹) * u := by
        have : tau0 u ^ 2 + τ₁ ^ 2 ≤ 2 * (u / cm) := by linarith
        calc CQ * (tau0 u ^ 2 + τ₁ ^ 2) ≤ CQ * (2 * (u / cm)) := mul_le_mul_of_nonneg_left this hCQ
          _ = (2 * CQ * cm⁻¹) * u := by field_simp
      refine (abs_vacD_le kind K4 c α τ₁ hu0 (hB.trans hB2)).trans ?_
      calc uctAlphaFl * u ^ (-(3 / 2 : ℝ)) * ((2 * CQ * cm⁻¹) * u) =
            (uctAlphaFl * CQ * (2 * cm⁻¹)) * (u ^ (-(3 / 2 : ℝ)) * u) := by ring
        _ = (uctAlphaFl * CQ * (2 * cm⁻¹)) * u ^ (-(1 / 2 : ℝ)) := by rw [rpow_three_halves_mul hu0]
        _ ≤ K * u ^ (-(1 / 2 : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hu0.le _)
            have h0 : 0 ≤ (uctM (1 / 8))⁻¹ := by positivity
            exact hKfar _ (by positivity) (by linarith only [h0])
    · have hB := hQlarge _ ht18.le
      have hm18' : uctM (1 / 8) ≤ u := by rw [← hmt]; exact hm_large _ ht18.le
      have hB2 : CQ ≤ (CQ * (uctM (1 / 8))⁻¹) * u := by
        calc CQ = (CQ * (uctM (1 / 8))⁻¹) * uctM (1 / 8) := by field_simp
          _ ≤ (CQ * (uctM (1 / 8))⁻¹) * u := mul_le_mul_of_nonneg_left hm18' (by positivity)
      refine (abs_vacD_le kind K4 c α τ₁ hu0 (hB.trans hB2)).trans ?_
      calc uctAlphaFl * u ^ (-(3 / 2 : ℝ)) * ((CQ * (uctM (1 / 8))⁻¹) * u) =
            (uctAlphaFl * CQ * (uctM (1 / 8))⁻¹) * (u ^ (-(3 / 2 : ℝ)) * u) := by ring
        _ = (uctAlphaFl * CQ * (uctM (1 / 8))⁻¹) * u ^ (-(1 / 2 : ℝ)) := by rw [rpow_three_halves_mul hu0]
        _ ≤ K * u ^ (-(1 / 2 : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hu0.le _)
            have h0 : 0 ≤ cm⁻¹ := by positivity
            exact hKfar _ (by positivity) (by linarith only [h0])

/-- info: 'FormalResearch.SignUncertainty.FctSym.stripR0_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripR0_sub_one_le

/-- info: 'FormalResearch.SignUncertainty.FctSym.stripR0_large_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripR0_large_le

/-- info: 'FormalResearch.SignUncertainty.FctSym.stripDeltaCurv_le_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripDeltaCurv_le_all

/-- info: 'FormalResearch.SignUncertainty.FctSym.vacQD_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vacQD_bounds

/-- info: 'FormalResearch.SignUncertainty.FctSym.uctM_two_gt_31' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uctM_two_gt_31

/-- info: 'FormalResearch.SignUncertainty.FctSym.vacPointwise_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vacPointwise_concrete

end FormalResearch.SignUncertainty.FctSym
