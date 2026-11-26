module

public import FormalResearch.ModularBootstrap.FiveTerm.CombData
public import FormalResearch.ModularBootstrap.FiveTerm.OuterHbarIm

/-!
# The elementary part `a_rest` of the amplitude (FIVE-S, `cts:outer-strip`)

`a = a_xb + a_rest` with `a_xb = (1/4) log x_T + (1/4) log b_T - (1/2) log ξ*` (the part whose strip integral is
`(1/4) log K`, `OuterKfun`) and
`a_rest(t) = 2 log Λ(t) + (5/2) log cosh(πt/4) + (3/4) log cosh(πt/2) - (1/2) log cosh(πt)`.
`a_rest` is an admissible amplitude (`StripOuter.Amp`), bounded below and of linear growth `(π/2)|t|`.
Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-- `a_rest(t) = 2 log Λ + (5/2) log cosh(πt/4) + (3/4) log cosh(πt/2) - (1/2) log cosh(πt)`. -/
noncomputable def aRest (t : ℝ) : ℝ :=
  2 * Real.log (lamT t) + (5 / 2) * Real.log (Real.cosh (π * t / 4)) +
    (3 / 4) * Real.log (Real.cosh (π * t / 2)) - (1 / 2) * Real.log (Real.cosh (π * t))

/-- `a_xb = (1/4) log x_T + (1/4) log b_T - (1/2) log ξ*`. -/
noncomputable def aXb (t : ℝ) : ℝ :=
  (1 / 4) * Real.log (xT t) + (1 / 4) * Real.log (bT t) - (1 / 2) * Real.log xiStar

lemma aAmp_eq_aXb_add_aRest (t : ℝ) : aAmp t = aXb t + aRest t := by
  unfold aAmp aXb aRest; ring

lemma exp_four_aXb (t : ℝ) : Real.exp (4 * aXb t) = xT t * bT t / xiStar ^ 2 := by
  have hx := xT_pos t
  have hb := bT_pos t
  have hxi := xiStar_pos
  have : 4 * aXb t = Real.log (xT t * bT t / xiStar ^ 2) := by
    unfold aXb
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul hx.ne' hb.ne', Real.log_pow]
    push_cast; ring
  rw [this, Real.exp_log (by positivity)]

lemma continuous_aRest : Continuous aRest := by
  unfold aRest
  have hc : ∀ c : ℝ, Continuous fun t : ℝ => Real.cosh (π * t / c) :=
    fun c => Real.continuous_cosh.comp (by fun_prop)
  have h1 := (Real.continuous_cosh.comp (continuous_const.mul continuous_id : Continuous fun t : ℝ => π * t)).log
    (fun t => (Real.cosh_pos _).ne')
  exact (((continuous_const.mul (continuous_lamT.log (fun t => (lamT_pos t).ne'))).add
    (continuous_const.mul ((hc 4).log (fun t => (Real.cosh_pos _).ne')))).add
    (continuous_const.mul ((hc 2).log (fun t => (Real.cosh_pos _).ne')))).sub (continuous_const.mul h1)

lemma aRest_even (t : ℝ) : aRest (-t) = aRest t := by
  unfold aRest
  have h1 : π * (-t) / 4 = -(π * t / 4) := by ring
  have h2 : π * (-t) / 2 = -(π * t / 2) := by ring
  have h3 : π * (-t) = -(π * t) := by ring
  have hl : lamT (-t) = lamT t := by unfold lamT; rw [xT_even]
  rw [hl, h1, h2, h3, Real.cosh_neg, Real.cosh_neg, Real.cosh_neg]

lemma aRest_ge (t : ℝ) : -((13 / 4) * Real.log 2) ≤ aRest t := by
  unfold aRest
  have hpi := Real.pi_pos
  have h4 : 0 ≤ Real.log (lamT t) := Real.log_nonneg (one_le_lamT t)
  have h5 := le_log_cosh (π * t / 4)
  have h6 := le_log_cosh (π * t / 2)
  have h7 := log_cosh_le (π * t)
  have e5 : |π * t / 4| = π * |t| / 4 := by rw [abs_div, abs_mul, abs_of_pos hpi]; norm_num
  have e6 : |π * t / 2| = π * |t| / 2 := by rw [abs_div, abs_mul, abs_of_pos hpi]; norm_num
  have e7 : |π * t| = π * |t| := by rw [abs_mul, abs_of_pos hpi]
  rw [e5] at h5; rw [e6] at h6; rw [e7] at h7
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [abs_nonneg t]

lemma aRest_le (t : ℝ) : aRest t ≤ (π / 2) * |t| +
    ((1 / 2) * Real.log 2 - 2 * Real.log (1 - Real.exp (-(4 * π * xiStar)))) := by
  unfold aRest
  have hxi := xiStar_pos
  have hpi := Real.pi_pos
  have h4 : Real.log (lamT t) ≤ Real.log (1 / (1 - Real.exp (-(4 * π * xiStar)))) :=
    Real.log_le_log (lamT_pos t) (lamT_le t)
  have h4' : Real.log (1 / (1 - Real.exp (-(4 * π * xiStar)))) =
      -Real.log (1 - Real.exp (-(4 * π * xiStar))) := by rw [one_div, Real.log_inv]
  have h5 := log_cosh_le (π * t / 4)
  have h6 := log_cosh_le (π * t / 2)
  have h7 := le_log_cosh (π * t)
  have e5 : |π * t / 4| = π * |t| / 4 := by rw [abs_div, abs_mul, abs_of_pos hpi]; norm_num
  have e6 : |π * t / 2| = π * |t| / 2 := by rw [abs_div, abs_mul, abs_of_pos hpi]; norm_num
  have e7 : |π * t| = π * |t| := by rw [abs_mul, abs_of_pos hpi]
  rw [e5] at h5; rw [e6] at h6; rw [e7] at h7
  nlinarith [abs_nonneg t]

lemma expBdd_of_bounds {a : ℝ → ℝ} {m α β : ℝ} (hα : 0 ≤ α) (hm : ∀ t, m ≤ a t)
    (hb : ∀ t, a t ≤ α * |t| + β) : ExpBdd a := by
  refine ⟨|m| + α + |β|, fun t => ?_⟩
  have h1 : |t| ≤ Real.exp |t| := by
    have := Real.add_one_le_exp |t|; linarith
  have h2 : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
  have hup : a t ≤ (|m| + α + |β|) * Real.exp |t| := by
    have := hb t
    nlinarith [le_abs_self β, abs_nonneg m, abs_nonneg t, mul_nonneg (abs_nonneg m) (by linarith : 0 ≤ Real.exp |t| - 1),
      mul_nonneg (abs_nonneg β) (by linarith : 0 ≤ Real.exp |t| - 1),
      mul_nonneg hα (by linarith : 0 ≤ Real.exp |t| - |t|)]
  have hlo : -((|m| + α + |β|) * Real.exp |t|) ≤ a t := by
    have := hm t
    nlinarith [neg_abs_le m, abs_nonneg m, abs_nonneg β, mul_nonneg (abs_nonneg m) (by linarith : 0 ≤ Real.exp |t| - 1),
      mul_nonneg hα (by linarith : 0 ≤ Real.exp |t|),
      mul_nonneg (abs_nonneg β) (by linarith : 0 ≤ Real.exp |t|)]
  exact abs_le.mpr ⟨hlo, hup⟩

/-- Complex extension of `a_rest`. -/
noncomputable def aRestC (ζ : ℂ) : ℂ :=
  2 * Complex.log (lamC ζ) + (5 / 2) * Complex.log (Complex.cosh ((π : ℂ) * ζ / 4)) +
    (3 / 4) * Complex.log (Complex.cosh ((π : ℂ) * ζ / 2)) - (1 / 2) * Complex.log (Complex.cosh ((π : ℂ) * ζ))

lemma diff_aRestC_of_good {ζ : ℂ} (h : GoodAt ζ) : DifferentiableAt ℂ aRestC ζ := by
  unfold aRestC
  have h3 := h.diff_lamC
  have e3 : DifferentiableAt ℂ (fun ζ => Complex.log (lamC ζ)) ζ := h3.clog h.c7
  have e4 : DifferentiableAt ℂ (fun ζ => Complex.log (Complex.cosh ((π : ℂ) * ζ / 4))) ζ :=
    DifferentiableAt.clog (by fun_prop) h.c8
  have e5 : DifferentiableAt ℂ (fun ζ => Complex.log (Complex.cosh ((π : ℂ) * ζ / 2))) ζ :=
    DifferentiableAt.clog (by fun_prop) h.c9
  have e6 : DifferentiableAt ℂ (fun ζ => Complex.log (Complex.cosh ((π : ℂ) * ζ))) ζ :=
    DifferentiableAt.clog (by fun_prop) h.c1
  fun_prop

lemma aRestC_ofReal (t : ℝ) : aRestC (t : ℂ) = ((aRest t : ℝ) : ℂ) := by
  unfold aRestC aRest
  rw [lamC_ofReal]
  have h4 : Complex.cosh ((π : ℂ) * (t : ℂ) / 4) = ((Real.cosh (π * t / 4) : ℝ) : ℂ) := by simp
  have h2 : Complex.cosh ((π : ℂ) * (t : ℂ) / 2) = ((Real.cosh (π * t / 2) : ℝ) : ℂ) := by simp
  have h1 : Complex.cosh ((π : ℂ) * (t : ℂ)) = ((Real.cosh (π * t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cosh]; push_cast; rfl
  rw [h4, h2, h1]
  rw [← Complex.ofReal_log (lamT_pos t).le, ← Complex.ofReal_log (Real.cosh_pos _).le,
    ← Complex.ofReal_log (Real.cosh_pos _).le, ← Complex.ofReal_log (Real.cosh_pos _).le]
  push_cast
  ring

/-- **`a_rest` is an admissible amplitude.** -/
theorem amp_aRest : Amp aRest := by
  refine ⟨continuous_aRest, aRest_even,
    expBdd_of_bounds (by positivity : (0 : ℝ) ≤ π / 2) aRest_ge aRest_le, fun y₀ => ?_⟩
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_goodAt y₀)
  refine ⟨R, hR, aRestC, ?_, fun t _ => ?_⟩
  · intro ζ hζ
    exact (diff_aRestC_of_good (hball ζ hζ)).differentiableWithinAt
  · rw [aRestC_ofReal]

/-- `Im h̄_{a_rest}(iτ) = F_{a_rest}(τ)` once `a_rest` is locally Lipschitz (proved in `OuterRestDeriv`). -/
lemma aRest_wlog : ∃ M : ℝ, ∀ t, |aRest t| ≤ M * wlog t :=
  abs_le_wlog_of_bounds (by positivity : (0 : ℝ) ≤ π / 2) aRest_ge aRest_le

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.amp_aRest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_aRest

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
