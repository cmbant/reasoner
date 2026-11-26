module

public import FormalResearch.SignUncertainty.CtOuterEntire
public import FormalResearch.SignUncertainty.CtOuterBdryDeriv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Moment functional and boundary phase `ϑ_D` for `fct:moment-solver` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, §2.1 equations `(fct:thD-def)`, `(fct:moments)`
and the quantitative phase estimate in the proof of Lemma `fct:moment-solver`.

For a real smooth compactly supported function `v : ℝ → ℝ`:
* `fctWeight t = cosh(πt) / sinh(πt)^2` (the even positive weight `w(t)` on `ℝ \ {0}`);
* `fctThetaD v τ = ∫ z, (v (τ + z) - v τ) / sinh (π * z)` (the boundary phase `ϑ_D(τ)`, equal to
  `CtOuter.bdryF v τ` by `fctThetaD_eq_bdryF`, and to `p.v. ∫ v(t) / sinh(π(t - τ)) dt` since `1/sinh(πz)` is odd);
* `fctMoment k v = (1 / π) * ∫_{t > 0} v^{(2k+1)}(t) / sinh(πt) dt` (the integrated-by-parts form of the
  paper's Hadamard finite-part moment `ℳ_k[v] = f.p. ∫_0^∞ v(t) w^{(2k)}(t) dt` in `(fct:moments)`).

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.FctMoment

/-- The weight `w(t) = cosh(πt) / sinh(πt)²` of `(fct:moments)`. -/
noncomputable def fctWeight (t : ℝ) : ℝ :=
  Real.cosh (π * t) / Real.sinh (π * t) ^ 2

/-- The boundary phase `ϑ_D(τ) = ∫ (v(τ+z) - v(τ)) / sinh(πz) dz` of `(fct:thD-def)`.
Identical to `CtOuter.bdryF v τ` (`fctThetaD_eq_bdryF`). -/
noncomputable def fctThetaD (v : ℝ → ℝ) (τ : ℝ) : ℝ :=
  ∫ z : ℝ, (v (τ + z) - v τ) / Real.sinh (π * z)

/-- `fctThetaD` coincides identically with `CtOuter.bdryF`
(`F_a(τ) = ∫ (a(t) - a(τ)) / sinh(π(t - τ)) dt`), via the translation `z = t - τ` (`CtOuter.bdryF_eq_shift`). -/
lemma fctThetaD_eq_bdryF (v : ℝ → ℝ) (τ : ℝ) :
    fctThetaD v τ = FormalResearch.SignUncertainty.CtOuter.bdryF v τ :=
  (FormalResearch.SignUncertainty.CtOuter.bdryF_eq_shift v τ).symm

lemma fctThetaD_eq_bdryF_fun :
    fctThetaD = FormalResearch.SignUncertainty.CtOuter.bdryF :=
  funext fun v => funext fun τ => fctThetaD_eq_bdryF v τ

/-- The moment functional `ℳ_k[v] = (1/π) ∫_{t > 0} v^{(2k+1)}(t) / sinh(πt) dt`, which is the
integrated-by-parts form of the paper's Hadamard finite-part moment
`ℳ_k[v] := f.p. ∫_0^∞ v(t) w^{(2k)}(t) dt` in `(fct:moments)`.
Using `w(t) = -(1/π) ∂_t(sinh(πt)⁻¹)` and integrating by parts `2k + 1` times on `(ε, ∞)` as `ε ↓ 0`,
for smooth even `v` with compact support and `v(0) = 0` all odd-pole boundary terms at `0` cancel the
Hadamard finite-part subtraction and boundary terms at `∞` vanish (`ibp_sinh_odd_pole`). -/
noncomputable def fctMoment (k : ℕ) (v : ℝ → ℝ) : ℝ :=
  (1 / π) * ∫ t in Ioi (0 : ℝ), iteratedDeriv (2 * k + 1) v t / Real.sinh (π * t)

/-! ### Elementary `sinh` bounds -/

lemma hasDerivAt_sinh_real (x : ℝ) : HasDerivAt Real.sinh (Real.cosh x) x := by
  have heq : Real.sinh = fun t => (Real.exp t - Real.exp (-t)) / 2 := funext Real.sinh_eq
  rw [heq]
  have h1 := Real.hasDerivAt_exp x
  have h2 : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-x)) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  refine ((h1.sub h2).div_const 2).congr_deriv ?_
  rw [Real.cosh_eq]; ring

lemma contDiff_sinh_real : ContDiff ℝ (⊤ : ℕ∞) Real.sinh := by
  have heq : Real.sinh = fun t => (Real.exp t - Real.exp (-t)) / 2 := funext Real.sinh_eq
  rw [heq]
  exact ((Real.contDiff_exp.of_le le_top).sub
    ((Real.contDiff_exp.of_le le_top).comp contDiff_neg)).div_const 2

lemma one_le_cosh_real (x : ℝ) : 1 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  have h1 := Real.add_one_le_exp x
  have h2 := Real.add_one_le_exp (-x)
  linarith

lemma self_le_sinh_nonneg {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.sinh x := by
  have hmono : MonotoneOn (fun t => Real.sinh t - t) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (contDiff_sinh_real.continuous.sub continuous_id).continuousOn
      ((contDiff_sinh_real.differentiable (by simp)).sub differentiable_id).differentiableOn
      fun t _ => ?_
    have hd : HasDerivAt (fun s => Real.sinh s - s) (Real.cosh t - 1) t :=
      (hasDerivAt_sinh_real t).sub (hasDerivAt_id t)
    rw [hd.deriv]
    linarith [one_le_cosh_real t]
  have := hmono (show (0 : ℝ) ∈ Ici 0 from le_rfl) hx hx
  simp only [Real.sinh_zero, sub_zero] at this
  linarith

lemma sinh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x :=
  lt_of_lt_of_le hx (self_le_sinh_nonneg hx.le)

lemma sinh_neg_of_neg {x : ℝ} (hx : x < 0) : Real.sinh x < 0 := by
  have := sinh_pos_of_pos (neg_pos.mpr hx)
  rw [Real.sinh_neg] at this; linarith

lemma sinh_pi_ne_zero {z : ℝ} (hz : z ≠ 0) : Real.sinh (π * z) ≠ 0 := by
  rcases lt_or_gt_of_ne hz with h | h
  · exact (sinh_neg_of_neg (mul_neg_of_pos_of_neg Real.pi_pos h)).ne
  · exact (sinh_pos_of_pos (mul_pos Real.pi_pos h)).ne'

lemma abs_mul_inv_sinh_le (z : ℝ) : |z / Real.sinh (π * z)| ≤ 1 / π := by
  by_cases hz : z = 0
  · simp [hz]; positivity
  have hpi : 0 < π := Real.pi_pos
  have h1 : π * |z| ≤ |Real.sinh (π * z)| := by
    rcases lt_or_gt_of_ne hz with h | h
    · have h' : 0 < -z := neg_pos.mpr h
      rw [abs_of_neg h, abs_of_neg (sinh_neg_of_neg (by nlinarith)), ← Real.sinh_neg,
        show -(π * z) = π * (-z) by ring]
      exact self_le_sinh_nonneg (show 0 ≤ π * (-z) by positivity)
    · rw [abs_of_pos h, abs_of_pos (sinh_pos_of_pos (by positivity))]
      exact self_le_sinh_nonneg (by positivity)
  have hsh : 0 < |Real.sinh (π * z)| := lt_of_lt_of_le (by positivity) h1
  rw [abs_div, div_le_div_iff₀ hsh hpi]
  linarith

lemma abs_inv_sinh_le_exp {z : ℝ} (hz : 1 ≤ |z|) :
    |1 / Real.sinh (π * z)| ≤ 4 * Real.exp (-(π * |z|)) := by
  have hpi : 0 < π := Real.pi_pos
  have hpi2 : 2 < π := by linarith [Real.pi_gt_three]
  have h1 : Real.exp (π * |z|) / 4 ≤ |Real.sinh (π * z)| := by
    have habs : |Real.sinh (π * z)| = Real.sinh (π * |z|) := by
      rcases le_or_gt 0 z with h | h
      · rw [abs_of_nonneg h, abs_of_nonneg (le_trans (by positivity) (self_le_sinh_nonneg (by positivity)))]
      · rw [abs_of_neg h, abs_of_neg (sinh_neg_of_neg (by nlinarith)), ← Real.sinh_neg]
        ring_nf
    rw [habs, Real.sinh_eq]
    have hexp : 2 ≤ Real.exp (π * |z|) := by
      have hge1 : 1 ≤ π * |z| := by nlinarith
      have := Real.add_one_le_exp (π * |z|)
      linarith
    have hinv : Real.exp (-(π * |z|)) ≤ Real.exp (π * |z|) / 2 := by
      rw [Real.exp_neg]
      have hpos : 0 < Real.exp (π * |z|) := Real.exp_pos _
      rw [le_div_iff₀ two_pos, inv_mul_eq_div, div_le_iff₀ hpos]
      nlinarith
    linarith
  have hsh : 0 < |Real.sinh (π * z)| := lt_of_lt_of_le (by positivity) h1
  rw [abs_div, abs_one, Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hsh (Real.exp_pos _)]
  linarith

/-! ### Parity of iterated derivatives -/

lemma iteratedDeriv_even_or_odd (f : ℝ → ℝ) (h : ∀ t, f (-t) = f t) (n : ℕ) (t : ℝ) :
    iteratedDeriv n f (-t) = (-1 : ℝ) ^ n * iteratedDeriv n f t := by
  have h1 := iteratedDeriv_comp_neg n f t
  have hfun : (fun x => f (-x)) = f := funext h
  rw [hfun, smul_eq_mul] at h1
  have hsq : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
  calc iteratedDeriv n f (-t)
      = (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * iteratedDeriv n f (-t)) := by
        rw [← mul_assoc, hsq, one_mul]
    _ = (-1 : ℝ) ^ n * iteratedDeriv n f t := by rw [← h1]

lemma iteratedDeriv_odd_zero {f : ℝ → ℝ} (h : ∀ t, f (-t) = f t) (k : ℕ) :
    iteratedDeriv (2 * k + 1) f 0 = 0 := by
  have h1 := iteratedDeriv_even_or_odd f h (2 * k + 1) 0
  have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [neg_zero, hpow] at h1
  linarith

lemma iteratedDeriv_odd_fn (f : ℝ → ℝ) (h : ∀ t, f (-t) = -f t) (n : ℕ) (t : ℝ) :
    iteratedDeriv n f (-t) = (-1 : ℝ) ^ (n + 1) * iteratedDeriv n f t := by
  have h1 := iteratedDeriv_comp_neg n f t
  have hfun : (fun x => f (-x)) = -f := funext h
  rw [hfun, iteratedDeriv_neg, smul_eq_mul] at h1
  have hsq : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
  calc iteratedDeriv n f (-t)
      = (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * iteratedDeriv n f (-t)) := by
        rw [← mul_assoc, hsq, one_mul]
    _ = (-1 : ℝ) ^ n * (-iteratedDeriv n f t) := by rw [← h1]
    _ = (-1 : ℝ) ^ (n + 1) * iteratedDeriv n f t := by rw [pow_succ]; ring

lemma iteratedDeriv_even_zero_of_odd {f : ℝ → ℝ} (h : ∀ t, f (-t) = -f t) (k : ℕ) :
    iteratedDeriv (2 * k) f 0 = 0 := by
  have h1 := iteratedDeriv_odd_fn f h (2 * k) 0
  have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [neg_zero, hpow] at h1
  linarith

/-! ### Helper lemmas for `ContDiff ℝ (⊤ : ℕ∞)` and `iteratedDeriv` -/

lemma contDiff_iteratedDeriv_infty {v : ℝ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (r : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv r v) := by
  rw [iteratedDeriv_eq_iterate]; exact hv.iterate_deriv r

lemma hasCompactSupport_iteratedDeriv {v : ℝ → ℝ} (hs : HasCompactSupport v) (r : ℕ) :
    HasCompactSupport (iteratedDeriv r v) := by
  induction r with
  | zero => simpa using hs
  | succ r ih => rw [iteratedDeriv_succ]; exact ih.deriv

lemma iteratedDeriv_iteratedDeriv_eq (f : ℝ → ℝ) (j r : ℕ) :
    iteratedDeriv j (iteratedDeriv r f) = iteratedDeriv (j + r) f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih, ← iteratedDeriv_succ, Nat.succ_add]

lemma iteratedDeriv_congr_on_open {f g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (heq : EqOn f g U) (n : ℕ) {t : ℝ} (ht : t ∈ U) :
    iteratedDeriv n f t = iteratedDeriv n g t :=
  (Filter.eventuallyEq_of_mem (hU.mem_nhds ht) heq).iteratedDeriv n |>.eq_of_nhds

/-! ### Difference-quotient integrability and differentiation under the integral -/

lemma norm_diff_div_sinh_le {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) {M0 M1 : ℝ}
    (hM0 : ∀ t, |g t| ≤ M0) (hM1 : ∀ t, |deriv g t| ≤ M1) (τ z : ℝ) :
    |(g (τ + z) - g τ) / Real.sinh (π * z)| ≤
      if |z| ≤ 1 then M1 / π else 8 * M0 * Real.exp (-(π * |z|)) := by
  split_ifs with hz
  · have hdiff : |g (τ + z) - g τ| ≤ M1 * |z| := by
      have hd : ∀ x, HasDerivAt g (deriv g x) x := fun x =>
        (hg.differentiable (by simp) x).hasDerivAt
      have hlip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := g) (f' := deriv g) (s := univ) (C := M1)
        (fun x _ => (hd x).hasDerivWithinAt)
        (fun x _ => by simpa [Real.norm_eq_abs] using hM1 x)
        convex_univ (mem_univ τ) (mem_univ (τ + z))
      simpa [Real.norm_eq_abs, add_sub_cancel_left] using hlip
    by_cases hz0 : z = 0
    · simp only [hz0, add_zero, sub_self, zero_div, abs_zero]
      have hM1_nn : 0 ≤ M1 := le_trans (abs_nonneg _) (hM1 0)
      positivity
    · rw [abs_div]
      calc |g (τ + z) - g τ| / |Real.sinh (π * z)|
          ≤ (M1 * |z|) / |Real.sinh (π * z)| :=
            div_le_div_of_nonneg_right hdiff (abs_nonneg _)
        _ = M1 * |z / Real.sinh (π * z)| := by rw [abs_div, mul_div_assoc]
        _ ≤ M1 * (1 / π) := by
            have hM1_nn : 0 ≤ M1 := le_trans (abs_nonneg _) (hM1 0)
            exact mul_le_mul_of_nonneg_left (abs_mul_inv_sinh_le z) hM1_nn
        _ = M1 / π := by ring
  · have hz1 : 1 ≤ |z| := le_of_not_ge hz
    have hnum : |g (τ + z) - g τ| ≤ 2 * M0 := by
      calc |g (τ + z) - g τ| ≤ |g (τ + z)| + |g τ| := abs_sub _ _
        _ ≤ M0 + M0 := add_le_add (hM0 _) (hM0 _)
        _ = 2 * M0 := by ring
    rw [abs_div]
    calc |g (τ + z) - g τ| / |Real.sinh (π * z)|
        = |g (τ + z) - g τ| * |1 / Real.sinh (π * z)| := by
          rw [abs_div, abs_one, mul_one_div]
      _ ≤ (2 * M0) * (4 * Real.exp (-(π * |z|))) :=
          mul_le_mul hnum (abs_inv_sinh_le_exp hz1) (abs_nonneg _)
            (by linarith [le_trans (abs_nonneg _) (hM0 0)])
      _ = 8 * M0 * Real.exp (-(π * |z|)) := by ring

lemma integrable_dom_sinh (M0 M1 : ℝ) :
    Integrable (fun z : ℝ => if |z| ≤ 1 then M1 / π else 8 * M0 * Real.exp (-(π * |z|))) := by
  have hexp : Integrable (fun z : ℝ => Real.exp (-(π * |z|))) := by
    have h1 : IntegrableOn (fun z : ℝ => Real.exp ((-π) * z)) (Ioi 0) :=
      integrableOn_exp_mul_Ioi (show -π < 0 by linarith [Real.pi_pos]) 0
    have h2 : IntegrableOn (fun z : ℝ => Real.exp (π * z)) (Iic 0) :=
      integrableOn_exp_mul_Iic Real.pi_pos 0
    have hpos : IntegrableOn (fun z : ℝ => Real.exp (-(π * |z|))) (Ioi 0) :=
      h1.congr_fun (fun z hz => by rw [abs_of_pos (mem_Ioi.mp hz)]; ring_nf) measurableSet_Ioi
    have hneg : IntegrableOn (fun z : ℝ => Real.exp (-(π * |z|))) (Iic 0) :=
      h2.congr_fun (fun z hz => by
        rw [abs_of_nonpos (mem_Iic.mp hz)]; ring_nf) measurableSet_Iic
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact hneg.union hpos
  have h1 : Integrable (Set.indicator (Icc (-1 : ℝ) 1) (fun _ => M1 / π)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (hs := measure_Icc_lt_top.ne)
  have h2 : Integrable (Set.indicator (Icc (-1 : ℝ) 1)ᶜ (fun z : ℝ => 8 * M0 * Real.exp (-(π * |z|)))) :=
    (hexp.const_mul (8 * M0)).indicator measurableSet_Icc.compl
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : |z| ≤ 1
  · have hmem : z ∈ Icc (-1 : ℝ) 1 := abs_le.mp hz
    simp [hz, hmem]
  · have hmem : z ∉ Icc (-1 : ℝ) 1 := fun h => hz (abs_le.mpr h)
    simp [hz, hmem]

lemma aestronglyMeasurable_diff_div_sinh {g : ℝ → ℝ} (hg : Continuous g) (τ : ℝ) :
    AEStronglyMeasurable (fun z : ℝ => (g (τ + z) - g τ) / Real.sinh (π * z)) volume := by
  have hnum : Measurable (fun z : ℝ => g (τ + z) - g τ) :=
    (hg.comp (continuous_const.add continuous_id)).sub continuous_const |>.measurable
  have hden : Measurable (fun z : ℝ => Real.sinh (π * z)) :=
    (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).measurable
  exact (hnum.div hden).aestronglyMeasurable

lemma fctThetaD_integrable {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) {M0 M1 : ℝ}
    (hM0 : ∀ t, |g t| ≤ M0) (hM1 : ∀ t, |deriv g t| ≤ M1) (τ : ℝ) :
    Integrable (fun z : ℝ => (g (τ + z) - g τ) / Real.sinh (π * z)) := by
  refine (integrable_dom_sinh M0 M1).mono' (aestronglyMeasurable_diff_div_sinh hg.continuous τ)
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact norm_diff_div_sinh_le hg hM0 hM1 τ z

lemma hasDerivAt_fctThetaD {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) {M0 M1 M2 : ℝ}
    (hM0 : ∀ t, |g t| ≤ M0) (hM1 : ∀ t, |deriv g t| ≤ M1)
    (hM2 : ∀ t, |deriv (deriv g) t| ≤ M2) (τ : ℝ) :
    HasDerivAt (fctThetaD g) (fctThetaD (deriv g) τ) τ := by
  have hg' : ContDiff ℝ (⊤ : ℕ∞) (deriv g) := by
    simpa [iteratedDeriv_one] using contDiff_iteratedDeriv_infty hg 1
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun τ z => (g (τ + z) - g τ) / Real.sinh (π * z))
    (F' := fun τ z => (deriv g (τ + z) - deriv g τ) / Real.sinh (π * z))
    (bound := fun z => if |z| ≤ 1 then M2 / π else 8 * M1 * Real.exp (-(π * |z|)))
    (x₀ := τ) (s := univ) univ_mem
    (Filter.Eventually.of_forall fun x => aestronglyMeasurable_diff_div_sinh hg.continuous x)
    (fctThetaD_integrable hg hM0 hM1 τ)
    (aestronglyMeasurable_diff_div_sinh hg'.continuous τ)
    (Filter.Eventually.of_forall fun z x _ => by
      rw [Real.norm_eq_abs]
      exact norm_diff_div_sinh_le hg' hM1 hM2 x z)
    (integrable_dom_sinh M1 M2)
    (Filter.Eventually.of_forall fun z x _ => by
      have h1 : HasDerivAt (fun t => g (t + z)) (deriv g (x + z)) x := by
        have hcomp := (hg.differentiable (by simp) (x + z)).hasDerivAt.comp x
          ((hasDerivAt_id x).add_const z)
        simpa [Function.comp_def] using hcomp
      have h2 : HasDerivAt g (deriv g x) x := (hg.differentiable (by simp) x).hasDerivAt
      exact (h1.sub h2).div_const (Real.sinh (π * z)))
  exact h.2

lemma exists_bound_iteratedDeriv_of_compact {v : ℝ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hsupp : HasCompactSupport v) (r : ℕ) :
    ∃ M ≥ 0, ∀ t, |iteratedDeriv r v t| ≤ M := by
  have hc : Continuous (iteratedDeriv r v) := (contDiff_iteratedDeriv_infty hv r).continuous
  have hs : HasCompactSupport (iteratedDeriv r v) := hasCompactSupport_iteratedDeriv hsupp r
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  exact (Real.norm_eq_abs _ ▸ hM t).trans (le_max_left _ _)

lemma hasDerivAt_fctThetaD_of_compact {v : ℝ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hsupp : HasCompactSupport v) (τ : ℝ) :
    HasDerivAt (fctThetaD v) (fctThetaD (deriv v) τ) τ := by
  obtain ⟨M0, _, hM0⟩ := exists_bound_iteratedDeriv_of_compact hv hsupp 0
  obtain ⟨M1, _, hM1⟩ := exists_bound_iteratedDeriv_of_compact hv hsupp 1
  obtain ⟨M2, _, hM2⟩ := exists_bound_iteratedDeriv_of_compact hv hsupp 2
  exact hasDerivAt_fctThetaD hv (by simpa using hM0)
    (by simpa [iteratedDeriv_one] using hM1)
    (by intro t; have := hM2 t; rwa [iteratedDeriv_succ, iteratedDeriv_one] at this) τ

lemma iteratedDeriv_fctThetaD {v : ℝ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hsupp : HasCompactSupport v) :
    ∀ r : ℕ, iteratedDeriv r (fctThetaD v) = fctThetaD (iteratedDeriv r v) := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    ext τ
    have hvr : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv r v) := contDiff_iteratedDeriv_infty hv r
    have hsr : HasCompactSupport (iteratedDeriv r v) := hasCompactSupport_iteratedDeriv hsupp r
    rw [(hasDerivAt_fctThetaD_of_compact hvr hsr τ).deriv, ← iteratedDeriv_succ]

lemma contDiff_fctThetaD_nat (n : ℕ) :
    ∀ {v : ℝ → ℝ}, ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v → ContDiff ℝ (n : ℕ∞) (fctThetaD v) := by
  induction n with
  | zero =>
    intro v hv hsupp
    simpa [contDiff_zero] using continuous_iff_continuousAt.mpr fun τ =>
      (hasDerivAt_fctThetaD_of_compact hv hsupp τ).continuousAt
  | succ n ih =>
    intro v hv hsupp
    have hcast : (((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) = ((n : ℕ∞) : WithTop ℕ∞) + 1 := by
      norm_cast
    rw [hcast, contDiff_succ_iff_deriv]
    refine ⟨fun τ => (hasDerivAt_fctThetaD_of_compact hv hsupp τ).differentiableAt, by simp, ?_⟩
    have hdeq : deriv (fctThetaD v) = fctThetaD (deriv v) := by
      ext τ; exact (hasDerivAt_fctThetaD_of_compact hv hsupp τ).deriv
    rw [hdeq]
    exact ih (by simpa [iteratedDeriv_one] using contDiff_iteratedDeriv_infty hv 1) hsupp.deriv

lemma contDiff_fctThetaD {v : ℝ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hsupp : HasCompactSupport v) :
    ContDiff ℝ (⊤ : ℕ∞) (fctThetaD v) :=
  contDiff_infty.mpr fun n => contDiff_fctThetaD_nat n hv hsupp

lemma fctThetaD_odd {v : ℝ → ℝ} (heven : ∀ t, v (-t) = v t) (τ : ℝ) :
    fctThetaD v (-τ) = -fctThetaD v τ := by
  unfold fctThetaD
  rw [← integral_neg]
  have hsub := integral_neg_eq_self (fun z : ℝ => (v (-τ + z) - v (-τ)) / Real.sinh (π * z)) volume
  rw [← hsub]
  congr 1; ext z
  have h1 : -τ + -z = -(τ + z) := by ring
  rw [h1, heven (τ + z), heven τ, mul_neg, Real.sinh_neg, div_neg]

/-! ### Connection between `fctMoment` and `fctThetaD`, linearity, and IBP identity -/

lemma iteratedDeriv_odd_fctThetaD_zero {v : ℝ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hsupp : HasCompactSupport v) (heven : ∀ t, v (-t) = v t) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (fctThetaD v) 0 = 2 * π * fctMoment k v := by
  rw [iteratedDeriv_fctThetaD hv hsupp (2 * k + 1)]
  unfold fctThetaD fctMoment
  have h0 : iteratedDeriv (2 * k + 1) v 0 = 0 := iteratedDeriv_odd_zero heven k
  have hpar : ∀ z, iteratedDeriv (2 * k + 1) v (-z) = -iteratedDeriv (2 * k + 1) v z := by
    intro z
    have := iteratedDeriv_even_or_odd v heven (2 * k + 1) z
    have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [hpow] at this; linarith
  have hsimpl : (fun z : ℝ => (iteratedDeriv (2 * k + 1) v (0 + z) - iteratedDeriv (2 * k + 1) v 0) /
      Real.sinh (π * z)) =
      fun z : ℝ => iteratedDeriv (2 * k + 1) v z / Real.sinh (π * z) := by
    ext z; simp [h0]
  rw [hsimpl]
  have hint : Integrable (fun z : ℝ => iteratedDeriv (2 * k + 1) v z / Real.sinh (π * z)) := by
    obtain ⟨M0, _, hM0⟩ := exists_bound_iteratedDeriv_of_compact hv hsupp (2 * k + 1)
    obtain ⟨M1, _, hM1⟩ := exists_bound_iteratedDeriv_of_compact hv hsupp (2 * k + 2)
    have hi := fctThetaD_integrable (contDiff_iteratedDeriv_infty hv (2 * k + 1)) hM0
      (fun t => by rw [← iteratedDeriv_succ]; exact hM1 t) 0
    rwa [hsimpl] at hi
  have hsplit : ∫ z : ℝ, iteratedDeriv (2 * k + 1) v z / Real.sinh (π * z) =
      (∫ z in Iic (0 : ℝ), iteratedDeriv (2 * k + 1) v z / Real.sinh (π * z)) +
      (∫ z in Ioi (0 : ℝ), iteratedDeriv (2 * k + 1) v z / Real.sinh (π * z)) := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn hint.integrableOn,
      Iic_union_Ioi, setIntegral_univ]
  have hneg : ∫ z in Iic (0 : ℝ), iteratedDeriv (2 * k + 1) v z / Real.sinh (π * z) =
      ∫ z in Ioi (0 : ℝ), iteratedDeriv (2 * k + 1) v z / Real.sinh (π * z) := by
    have hcomp := integral_comp_neg_Ioi (c := (0 : ℝ))
      (f := fun z : ℝ => iteratedDeriv (2 * k + 1) v z / Real.sinh (π * z))
    simp only [neg_zero] at hcomp
    rw [← hcomp]
    refine setIntegral_congr_fun measurableSet_Ioi fun z _ => ?_
    rw [hpar z, mul_neg, Real.sinh_neg, neg_div_neg_eq]
  rw [hsplit, hneg]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp; ring

lemma fctMoment_linear {v₁ v₂ : ℝ → ℝ} (hv₁ : ContDiff ℝ (⊤ : ℕ∞) v₁) (hs₁ : HasCompactSupport v₁)
    (he₁ : ∀ t, v₁ (-t) = v₁ t) (hv₂ : ContDiff ℝ (⊤ : ℕ∞) v₂) (hs₂ : HasCompactSupport v₂)
    (he₂ : ∀ t, v₂ (-t) = v₂ t) (a b : ℝ) (k : ℕ) :
    fctMoment k (fun t => a * v₁ t + b * v₂ t) = a * fctMoment k v₁ + b * fctMoment k v₂ := by
  have hint : ∀ {v : ℝ → ℝ}, ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v → (∀ t, v (-t) = v t) →
      IntegrableOn (fun t : ℝ => iteratedDeriv (2 * k + 1) v t / Real.sinh (π * t)) (Ioi 0) := by
    intro v hv hs he
    obtain ⟨M0, _, hM0⟩ := exists_bound_iteratedDeriv_of_compact hv hs (2 * k + 1)
    obtain ⟨M1, _, hM1⟩ := exists_bound_iteratedDeriv_of_compact hv hs (2 * k + 2)
    have h0 := iteratedDeriv_odd_zero he k
    have hi := fctThetaD_integrable (contDiff_iteratedDeriv_infty hv (2 * k + 1)) hM0
      (fun t => by rw [← iteratedDeriv_succ]; exact hM1 t) 0
    have hsimp : (fun z : ℝ => (iteratedDeriv (2 * k + 1) v (0 + z) - iteratedDeriv (2 * k + 1) v 0) /
        Real.sinh (π * z)) = fun z => iteratedDeriv (2 * k + 1) v z / Real.sinh (π * z) := by
      ext z; simp [h0]
    rw [hsimp] at hi
    exact hi.integrableOn
  have h1 := hint hv₁ hs₁ he₁
  have h2 := hint hv₂ hs₂ he₂
  unfold fctMoment
  have hid : iteratedDeriv (2 * k + 1) (fun t => a * v₁ t + b * v₂ t) =
      fun t => a * iteratedDeriv (2 * k + 1) v₁ t + b * iteratedDeriv (2 * k + 1) v₂ t := by
    ext t
    have hcd1 : ContDiffAt ℝ ((2 * k + 1 : ℕ) : WithTop ℕ∞) (fun s => a * v₁ s) t :=
      (hv₁.const_smul a).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    have hcd2 : ContDiffAt ℝ ((2 * k + 1 : ℕ) : WithTop ℕ∞) (fun s => b * v₂ s) t :=
      (hv₂.const_smul b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    rw [show (fun s => a * v₁ s + b * v₂ s) = (fun s => a * v₁ s) + (fun s => b * v₂ s) from rfl,
      iteratedDeriv_add hcd1 hcd2, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  rw [hid]
  have hfun : (fun t : ℝ => (a * iteratedDeriv (2 * k + 1) v₁ t +
      b * iteratedDeriv (2 * k + 1) v₂ t) / Real.sinh (π * t)) =
      fun t => a * (iteratedDeriv (2 * k + 1) v₁ t / Real.sinh (π * t)) +
        b * (iteratedDeriv (2 * k + 1) v₂ t / Real.sinh (π * t)) := by
    ext t; ring
  rw [hfun, integral_add (h1.const_mul a) (h2.const_mul b),
    integral_const_mul, integral_const_mul]
  ring

/-! ### Integration by parts: `ℳ_k[v] = ∫_{t>0} v(t) w^{(2k)}(t) dt` when `v = 0` near `0` -/

lemma hasDerivAt_inv_sinh (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun s => 1 / Real.sinh (π * s)) (-π * fctWeight t) t := by
  have hsh : Real.sinh (π * t) ≠ 0 := sinh_pi_ne_zero ht
  have h1 : HasDerivAt (fun s => Real.sinh (π * s)) (Real.cosh (π * t) * π) t := by
    simpa [Function.comp_def] using (hasDerivAt_sinh_real (π * t)).comp t ((hasDerivAt_id t).const_mul π)
  have h2 := h1.inv hsh
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => one_div _) |>.congr_deriv ?_
  unfold fctWeight; ring

lemma contDiffOn_inv_sinh : ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => 1 / Real.sinh (π * s)) (Ioi 0) := by
  refine contDiffOn_const.div ?_ (fun s hs => sinh_pi_ne_zero (mem_Ioi.mp hs).ne')
  exact contDiff_sinh_real.comp_contDiffOn (contDiffOn_const.mul contDiffOn_id)

lemma iteratedDeriv_succ_inv_sinh (n : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv (n + 1) (fun s : ℝ => 1 / Real.sinh (π * s)) t =
      -π * iteratedDeriv n fctWeight t := by
  rw [iteratedDeriv_succ']
  have heq : EqOn (deriv (fun s : ℝ => 1 / Real.sinh (π * s))) (fun s => -π * fctWeight s) (Ioi 0) := by
    intro s hs; exact (hasDerivAt_inv_sinh s (mem_Ioi.mp hs).ne').deriv
  rw [iteratedDeriv_congr_on_open isOpen_Ioi heq n ht]
  exact iteratedDeriv_const_mul_field (c := -π) (f := fctWeight) (n := n) (x := t)

/-- Repeated integration by parts on `[r, R]` when `g` vanishes near the endpoints. -/
lemma intervalIntegral_iteratedDeriv_mul {g h : ℝ → ℝ} {r R : ℝ} (hrR : r < R)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiffOn ℝ (⊤ : ℕ∞) h (Ioi 0)) (hr0 : 0 < r)
    (hvan : ∀ m : ℕ, iteratedDeriv m g r = 0 ∧ iteratedDeriv m g R = 0) :
    ∀ m : ℕ, ∫ t in r..R, iteratedDeriv m g t * h t =
      (-1 : ℝ) ^ m * ∫ t in r..R, g t * iteratedDeriv m h t := by
  intro m
  induction m generalizing h with
  | zero => simp
  | succ m ih =>
    have hsub : Icc r R ⊆ Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le hr0 ht.1
    have hsub_u : uIcc r R ⊆ Ioi (0 : ℝ) := by rwa [uIcc_of_le hrR.le]
    have hdh : ContDiffOn ℝ (⊤ : ℕ∞) (deriv h) (Ioi 0) :=
      hh.deriv_of_isOpen isOpen_Ioi (by simp)
    have hstep : ∫ t in r..R, iteratedDeriv (m + 1) g t * h t =
        -(∫ t in r..R, iteratedDeriv m g t * deriv h t) := by
      have hibp := intervalIntegral.integral_deriv_mul_eq_sub
        (u := iteratedDeriv m g) (v := h)
        (u' := iteratedDeriv (m + 1) g) (v' := deriv h) (a := r) (b := R)
        (fun t _ => by
          rw [iteratedDeriv_succ]
          exact ((contDiff_iteratedDeriv_infty hg m).differentiable (by simp) t).hasDerivAt)
        (fun t ht => ((hh.differentiableOn (by simp) t (hsub_u ht)).differentiableAt
          (isOpen_Ioi.mem_nhds (hsub_u ht))).hasDerivAt)
        ((contDiff_iteratedDeriv_infty hg (m + 1)).continuous.intervalIntegrable _ _)
        ((hdh.continuousOn.mono hsub).intervalIntegrable_of_Icc hrR.le)
      have hint1 : IntervalIntegrable (fun x => iteratedDeriv (m + 1) g x * h x) volume r R :=
        (((contDiff_iteratedDeriv_infty hg (m + 1)).continuous.continuousOn.mul
          (hh.continuousOn.mono hsub))).intervalIntegrable_of_Icc hrR.le
      have hint2 : IntervalIntegrable (fun x => iteratedDeriv m g x * deriv h x) volume r R :=
        (((contDiff_iteratedDeriv_infty hg m).continuous.continuousOn.mul
          (hdh.continuousOn.mono hsub))).intervalIntegrable_of_Icc hrR.le
      rw [intervalIntegral.integral_add hint1 hint2, (hvan m).2, (hvan m).1] at hibp
      linarith
    rw [hstep, ih hdh]
    have heq : ∀ t ∈ uIcc r R, g t * iteratedDeriv m (deriv h) t = g t * iteratedDeriv (m + 1) h t := by
      intro t _
      rw [iteratedDeriv_succ']
    rw [intervalIntegral.integral_congr heq]
    ring

lemma fctMoment_eq_integral_weight {v : ℝ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hsupp : HasCompactSupport v) {r : ℝ} (hr : 0 < r) (hvan : ∀ t ∈ Ioo (0 : ℝ) r, v t = 0) (k : ℕ) :
    fctMoment k v = ∫ t in Ioi (0 : ℝ), v t * iteratedDeriv (2 * k) fctWeight t := by
  obtain ⟨R, hR⟩ := hsupp.isCompact.isBounded.subset_closedBall (0 : ℝ)
  set R' : ℝ := max (max R 0 + 2) (r + 1) with hR'def
  have hrR : r < R' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hR0 : 0 ≤ max R 0 := le_max_right _ _
  have hR'gt : max R 0 < R' - 1 := by
    have : max R 0 + 2 ≤ R' := le_max_left _ _
    linarith
  have hv_zero_left : ∀ m : ℕ, ∀ t ∈ Ioo (0 : ℝ) r, iteratedDeriv m v t = 0 := by
    intro m t ht
    have heq : v =ᶠ[𝓝 t] 0 := Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) fun s hs => hvan s hs
    simpa using (heq.iteratedDeriv m).eq_of_nhds
  have hv_zero_right : ∀ m : ℕ, ∀ t, max R 0 < t → iteratedDeriv m v t = 0 := by
    intro m t ht
    have heq : v =ᶠ[𝓝 t] 0 := Filter.eventually_of_mem (Ioi_mem_nhds ht) fun s hs => by
      by_contra hne
      have hmem : s ∈ tsupport v := subset_tsupport v hne
      have hball := Metric.mem_closedBall.mp (hR hmem)
      rw [Real.dist_eq, sub_zero] at hball
      have hspos : 0 < s := lt_of_le_of_lt hR0 (mem_Ioi.mp hs)
      rw [abs_of_pos hspos] at hball
      have : R ≤ max R 0 := le_max_left _ _
      linarith [mem_Ioi.mp hs]
    simpa using (heq.iteratedDeriv m).eq_of_nhds
  have hvan_end : ∀ m : ℕ, iteratedDeriv m v (r / 2) = 0 ∧ iteratedDeriv m v R' = 0 := fun m =>
    ⟨hv_zero_left m (r / 2) ⟨by positivity, by linarith⟩, hv_zero_right m R' (by linarith)⟩
  have hibp := intervalIntegral_iteratedDeriv_mul (r := r / 2) (R := R') (by linarith)
    hv contDiffOn_inv_sinh (by positivity) hvan_end (2 * k + 1)
  have hrhs : ∫ t in (r / 2)..R', v t * iteratedDeriv (2 * k + 1) (fun s => 1 / Real.sinh (π * s)) t =
      -π * ∫ t in (r / 2)..R', v t * iteratedDeriv (2 * k) fctWeight t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by linarith)] at ht
    rw [iteratedDeriv_succ_inv_sinh (2 * k) (by linarith [ht.1])]
    ring
  rw [hrhs] at hibp
  have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [hpow] at hibp
  have h1 : (1 / π) * ∫ t in (r / 2)..R', iteratedDeriv (2 * k + 1) v t / Real.sinh (π * t) =
      ∫ t in (r / 2)..R', v t * iteratedDeriv (2 * k) fctWeight t := by
    have hpi : π ≠ 0 := Real.pi_ne_zero
    have hdiv : ∀ t, iteratedDeriv (2 * k + 1) v t / Real.sinh (π * t) =
        iteratedDeriv (2 * k + 1) v t * (1 / Real.sinh (π * t)) := fun t => by ring
    simp_rw [hdiv]
    rw [hibp]; field_simp
  have hsubIoc : Ioc (r / 2) R' ⊆ Ioi (0 : ℝ) := fun t ht => lt_trans (by positivity) ht.1
  have hIoc_lhs : ∫ t in Ioi (0 : ℝ), iteratedDeriv (2 * k + 1) v t / Real.sinh (π * t) =
      ∫ t in (r / 2)..R', iteratedDeriv (2 * k + 1) v t / Real.sinh (π * t) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet hsubIoc
      (Filter.Eventually.of_forall fun t ht => ?_)
    have hnot : ¬ (r / 2 < t ∧ t ≤ R') := ht.2
    rcases le_or_gt t (r / 2) with hle | hgt
    · rw [hv_zero_left (2 * k + 1) t ⟨ht.1, by linarith⟩, zero_div]
    · have : R' < t := not_le.mp fun hle => hnot ⟨hgt, hle⟩
      rw [hv_zero_right (2 * k + 1) t (by linarith), zero_div]
  have hIoc_rhs : ∫ t in Ioi (0 : ℝ), v t * iteratedDeriv (2 * k) fctWeight t =
      ∫ t in (r / 2)..R', v t * iteratedDeriv (2 * k) fctWeight t := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet hsubIoc
      (Filter.Eventually.of_forall fun t ht => ?_)
    have hnot : ¬ (r / 2 < t ∧ t ≤ R') := ht.2
    rcases le_or_gt t (r / 2) with hle | hgt
    · rw [hvan t ⟨ht.1, by linarith⟩, zero_mul]
    · have : R' < t := not_le.mp fun hle => hnot ⟨hgt, hle⟩
      have := hv_zero_right 0 t (by linarith)
      simp only [iteratedDeriv_zero] at this
      rw [this, zero_mul]
  unfold fctMoment
  rw [hIoc_lhs, hIoc_rhs, h1]

/-! ### Decomposition `w(t) = 1/(π²t²) + w_0(t)` with `w_0` smooth on `(-1, 1)` -/

/-- Smooth remainder `w_0(t) = w(t) - 1/(π²t²)` extended smoothly to `(-1, 1)` via `CtOuter.kappaFn`. -/
noncomputable def fctWeightRem (t : ℝ) : ℝ :=
  -(1 / π) * (deriv CtOuter.kappaFn (t : ℂ)).re

lemma contDiffOn_fctWeightRem : ContDiffOn ℝ (⊤ : ℕ∞) fctWeightRem (Ioo (-1 : ℝ) 1) := by
  have hC : ContDiffOn ℂ (⊤ : ℕ∞) CtOuter.kappaFn (Metric.ball 0 1) :=
    (CtOuter.differentiableOn_kappaFn.contDiffOn Metric.isOpen_ball).of_le (le_top)
  have hCd : ContDiffOn ℂ (⊤ : ℕ∞) (deriv CtOuter.kappaFn) (Metric.ball 0 1) :=
    hC.deriv_of_isOpen Metric.isOpen_ball (by simp)
  have hR : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => (deriv CtOuter.kappaFn (t : ℂ)).re) (Ioo (-1 : ℝ) 1) := by
    have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => deriv CtOuter.kappaFn (t : ℂ)) (Ioo (-1 : ℝ) 1) :=
      (hCd.restrict_scalars ℝ).comp (Complex.ofRealCLM.contDiff.of_le le_top).contDiffOn fun t ht => by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_lt]
        exact ht
    exact (Complex.reCLM.contDiff.of_le le_top).comp_contDiffOn hcomp
  exact contDiffOn_const.mul hR

lemma fctWeight_eq_inv_sq_add_rem {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    fctWeight t = 1 / (π ^ 2 * t ^ 2) + fctWeightRem t := by
  have hopen : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have htball : (t : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
  have hda : DifferentiableAt ℂ CtOuter.kappaFn (t : ℂ) :=
    CtOuter.differentiableOn_kappaFn.differentiableAt (hopen.mem_nhds htball)
  have hreal : HasDerivAt (fun s : ℝ => (CtOuter.kappaFn (s : ℂ)).re)
      (deriv CtOuter.kappaFn (t : ℂ)).re t := by
    have h1 := hda.hasDerivAt.comp_ofReal
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
  have hkappa_real : ∀ s : ℝ, s ≠ 0 →
      (CtOuter.kappaFn (s : ℂ)).re = 1 / Real.sinh (π * s) - 1 / (π * s) := by
    intro s _
    unfold CtOuter.kappaFn
    have h1 : Complex.sinh ((π : ℂ) * (s : ℂ)) = ((Real.sinh (π * s) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Complex.ofReal_sinh]
    rw [h1]
    have h2 : (1 : ℂ) / ((Real.sinh (π * s) : ℝ) : ℂ) - 1 / ((π : ℂ) * (s : ℂ)) =
        (((1 / Real.sinh (π * s) - 1 / (π * s) : ℝ)) : ℂ) := by push_cast; rfl
    rw [h2, Complex.ofReal_re]
  have hderiv_direct : HasDerivAt (fun s : ℝ => 1 / Real.sinh (π * s) - 1 / (π * s))
      (-π * fctWeight t + 1 / (π * t ^ 2)) t := by
    have h1 := hasDerivAt_inv_sinh t ht0.ne'
    have h2 : HasDerivAt (fun s : ℝ => 1 / (π * s)) (-(1 / (π * t ^ 2))) t := by
      have hm : HasDerivAt (fun s : ℝ => π * s) π t := by
        simpa using (hasDerivAt_id t).const_mul π
      have hi := hm.inv (mul_ne_zero Real.pi_pos.ne' ht0.ne')
      refine hi.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => one_div _) |>.congr_deriv ?_
      have hpi := Real.pi_pos.ne'
      have htne := ht0.ne'
      field_simp
    have hsub := h1.sub h2
    refine hsub.congr_deriv ?_; ring
  have hev : (fun s : ℝ => 1 / Real.sinh (π * s) - 1 / (π * s)) =ᶠ[𝓝 t]
      fun s : ℝ => (CtOuter.kappaFn (s : ℂ)).re :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht0) fun s hs => (hkappa_real s (mem_Ioi.mp hs).ne').symm
  have heq_deriv := (hreal.congr_of_eventuallyEq hev).unique hderiv_direct
  unfold fctWeightRem
  rw [heq_deriv]
  have hpi := Real.pi_pos.ne'
  field_simp; ring

lemma iteratedDeriv_inv_sq (m : ℕ) {t : ℝ} (ht : t ≠ 0) :
    iteratedDeriv m (fun s : ℝ => s ^ (-2 : ℤ)) t =
      (-1 : ℝ) ^ m * ((m + 1).factorial : ℝ) * t ^ (-((m + 2 : ℕ) : ℤ)) := by
  induction m generalizing t with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv m (fun s : ℝ => s ^ (-2 : ℤ)) =ᶠ[𝓝 t]
        fun s : ℝ => (-1 : ℝ) ^ m * ((m + 1).factorial : ℝ) * s ^ (-((m + 2 : ℕ) : ℤ)) :=
      Filter.eventually_of_mem (isOpen_ne.mem_nhds ht) fun s hs => ih hs
    rw [hev.deriv_eq]
    have hd := (hasDerivAt_zpow (-((m + 2 : ℕ) : ℤ)) t (Or.inl ht)).const_mul
      ((-1 : ℝ) ^ m * ((m + 1).factorial : ℝ))
    rw [hd.deriv]
    have hexp : (-((m + 2 : ℕ) : ℤ) - 1) = -((m + 1 + 2 : ℕ) : ℤ) := by omega
    rw [hexp, show m + 1 + 1 = (m + 1) + 1 from rfl, Nat.factorial_succ (m + 1)]
    push_cast
    rw [pow_succ]
    ring

lemma iteratedDeriv_fctWeight_decomp (k : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    iteratedDeriv (2 * k) fctWeight t =
      ((2 * k + 1).factorial : ℝ) / (π ^ 2 * t ^ (2 + 2 * k)) +
        iteratedDeriv (2 * k) fctWeightRem t := by
  have heq : EqOn fctWeight (fun s => (1 / π ^ 2) * s ^ (-2 : ℤ) + fctWeightRem s) (Ioo 0 1) := by
    intro s hs
    rw [fctWeight_eq_inv_sq_add_rem hs.1 hs.2]
    have h1 : 1 / (π ^ 2 * s ^ 2) = 1 / π ^ 2 * s ^ (-2 : ℤ) := by
      rw [zpow_neg, zpow_ofNat]; ring
    rw [h1]
  have h1 := iteratedDeriv_congr_on_open isOpen_Ioo heq (2 * k) ⟨ht0, ht1⟩
  rw [h1]
  have hcd1 : ContDiffAt ℝ ((2 * k : ℕ) : WithTop ℕ∞) (fun s : ℝ => (1 / π ^ 2) * s ^ (-2 : ℤ)) t := by
    have hz : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => s ^ (-2 : ℤ)) t := by
      have : (fun s : ℝ => s ^ (-2 : ℤ)) = fun s => (s ^ 2)⁻¹ := by ext s; rw [zpow_neg, zpow_ofNat]
      rw [this]
      exact (contDiffAt_id.pow 2).inv (pow_ne_zero 2 ht0.ne')
    exact (contDiffAt_const.mul hz).of_le (WithTop.coe_le_coe.mpr le_top)
  have hcd2 : ContDiffAt ℝ ((2 * k : ℕ) : WithTop ℕ∞) fctWeightRem t :=
    (contDiffOn_fctWeightRem.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, ht1⟩)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  rw [show (fun s : ℝ => (1 / π ^ 2) * s ^ (-2 : ℤ) + fctWeightRem s) =
      (fun s : ℝ => (1 / π ^ 2) * s ^ (-2 : ℤ)) + fctWeightRem from rfl,
    iteratedDeriv_add hcd1 hcd2, iteratedDeriv_const_mul_field, iteratedDeriv_inv_sq (2 * k) ht0.ne']
  have hpow : (-1 : ℝ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
  rw [hpow, one_mul, zpow_neg, zpow_natCast]
  have hexp : 2 * k + 2 = 2 + 2 * k := by omega
  rw [hexp]; ring

lemma exists_bound_fctWeightRem (k : ℕ) :
    ∃ B ≥ 0, ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), |iteratedDeriv (2 * k) fctWeightRem t| ≤ B := by
  have hcd : ∀ n : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv n fctWeightRem) (Ioo (-1 : ℝ) 1) := by
    intro n
    induction n with
    | zero => simpa using contDiffOn_fctWeightRem
    | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioo (by simp)
  have hc : ContinuousOn (iteratedDeriv (2 * k) fctWeightRem) (Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    (hcd (2 * k)).continuousOn.mono fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 0, le_max_right _ _, fun t ht => ?_⟩
  exact (Real.norm_eq_abs _ ▸ hM t ht).trans (le_max_left _ _)

/-! ### Quantitative phase bound on `|t| ≤ 12 τ₁` -/

lemma abs_le_of_iteratedDeriv_zero {g : ℝ → ℝ} {m : ℕ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hzero : ∀ j < m, iteratedDeriv j g 0 = 0) {B R : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ s, |s| ≤ R → |iteratedDeriv m g s| ≤ B) :
    ∀ t, |t| ≤ R → |g t| ≤ B * |t| ^ m := by
  induction m generalizing g with
  | zero =>
    intro t ht
    simpa using hbound t ht
  | succ m ih =>
    intro t ht
    have hderiv_bound : ∀ s, |s| ≤ R → |deriv g s| ≤ B * |s| ^ m := by
      refine ih (by simpa [iteratedDeriv_one] using contDiff_iteratedDeriv_infty hg 1)
        (fun j hj => ?_) (fun s hs => ?_)
      · rw [← iteratedDeriv_succ']; exact hzero (j + 1) (Nat.succ_lt_succ hj)
      · rw [← iteratedDeriv_succ']; exact hbound s hs
    have h0 : g 0 = 0 := by simpa using hzero 0 (Nat.zero_lt_succ m)
    have hlip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := g) (f' := deriv g) (s := Icc (-|t|) |t|) (C := B * |t| ^ m)
      (fun x _ => (hg.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
      (fun x hx => by
        have hxabs : |x| ≤ |t| := abs_le.mpr hx
        rw [Real.norm_eq_abs]
        exact (hderiv_bound x (hxabs.trans ht)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) hxabs m) hB))
      (convex_Icc _ _)
      ⟨by linarith [abs_nonneg t], abs_nonneg t⟩
      (abs_le.mp le_rfl)
    rw [h0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hlip
    simpa [pow_succ, mul_assoc] using hlip

/-- Quantitative bound on `ϑ_D^{(r)}(t)` for `|t| ≤ 12 τ₁` (last display of `fct:moment-solver`). -/
lemma abs_iteratedDeriv_fctThetaD_le {v : ℝ → ℝ} {N : ℕ} {τ₁ M : ℝ} {C_v : ℕ → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (heven : ∀ t, v (-t) = v t)
    (hsupp : Function.support v ⊆ Ioo (-10 * τ₁) (10 * τ₁))
    (hτ₁ : 0 < τ₁) (hM : 0 ≤ M)
    (hmom : ∀ k < N, fctMoment k v = 0)
    (hC_v : ∀ r t, |iteratedDeriv r v t| ≤ C_v r * M * τ₁ ^ ((2 : ℤ) - r))
    (r : ℕ) (t : ℝ) (ht : |t| ≤ 12 * τ₁) :
    |iteratedDeriv r (fctThetaD v) t| ≤
      (46 / π) * max (C_v (r + 1)) (C_v (2 * N + 2)) * M * τ₁ ^ ((2 : ℤ) - r) *
        min 1 ((|t| / τ₁) ^ (2 * N + 1 - r)) := by
  have hcomp : HasCompactSupport v :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (hsupp.trans Ioo_subset_Icc_self)
  have hunif : ∀ j : ℕ, ∀ s : ℝ, |s| ≤ 12 * τ₁ →
      |iteratedDeriv j (fctThetaD v) s| ≤ (46 / π) * C_v (j + 1) * M * τ₁ ^ ((2 : ℤ) - j) := by
    intro j s hs
    rw [iteratedDeriv_fctThetaD hv hcomp j]
    unfold fctThetaD
    set g := iteratedDeriv j v
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_iteratedDeriv_infty hv j
    have hg_zero : ∀ u, 10 * τ₁ < |u| → g u = 0 := by
      intro u hu
      have hopen : IsOpen {x : ℝ | 10 * τ₁ < |x|} := isOpen_lt continuous_const continuous_abs
      have heq : v =ᶠ[𝓝 u] 0 := Filter.eventually_of_mem (hopen.mem_nhds hu) fun x hx => by
        by_contra hne
        have := hsupp hne
        have hlt : |x| < 10 * τ₁ := abs_lt.mpr ⟨by linarith [this.1], this.2⟩
        have hx' : 10 * τ₁ < |x| := hx
        linarith
      simpa using (heq.iteratedDeriv j).eq_of_nhds
    set R : ℝ := 23 * τ₁
    have hR : 0 < R := by positivity
    obtain ⟨M0, _, hM0⟩ := exists_bound_iteratedDeriv_of_compact hv hcomp j
    obtain ⟨M1, _, hM1⟩ := exists_bound_iteratedDeriv_of_compact hv hcomp (j + 1)
    have hint : Integrable (fun z : ℝ => (g (s + z) - g s) / Real.sinh (π * z)) :=
      fctThetaD_integrable hg hM0 (fun t => by rw [← iteratedDeriv_succ]; exact hM1 t) s
    have hcompl_zero : ∫ z in (Icc (-R) R)ᶜ, (g (s + z) - g s) / Real.sinh (π * z) = 0 := by
      have hcongr : EqOn (fun z : ℝ => (g (s + z) - g s) / Real.sinh (π * z))
          (fun z : ℝ => (-g s) / Real.sinh (π * z)) (Icc (-R) R)ᶜ := by
        intro z hz
        have hzabs : R < |z| := by
          by_contra hle
          exact hz (abs_le.mp (not_lt.mp hle))
        have hsz : 10 * τ₁ < |s + z| := by
          have htri : |z| - |s| ≤ |s + z| := by
            have := abs_sub_abs_le_abs_sub z (-s)
            simpa [sub_neg_eq_add, add_comm] using this
          linarith
        dsimp only
        rw [hg_zero (s + z) hsz]; ring
      rw [setIntegral_congr_fun measurableSet_Icc.compl hcongr]
      have hneg : ∫ z in (Icc (-R) R)ᶜ, (-g s) / Real.sinh (π * z) =
          -(∫ z in (Icc (-R) R)ᶜ, (-g s) / Real.sinh (π * z)) := by
        rw [← integral_neg]
        have hind : ∀ (f : ℝ → ℝ), ∫ z in (Icc (-R) R)ᶜ, f z =
            ∫ z : ℝ, (Icc (-R) R)ᶜ.indicator f z := fun f =>
          (integral_indicator measurableSet_Icc.compl).symm
        rw [hind, hind]
        have hcomp_neg := integral_neg_eq_self
          ((Icc (-R) R)ᶜ.indicator (fun z : ℝ => (-g s) / Real.sinh (π * z))) volume
        rw [← hcomp_neg]
        congr 1; ext z
        by_cases hz : z ∈ (Icc (-R) R)ᶜ
        · have hnz : -z ∈ (Icc (-R) R)ᶜ := fun h => hz ⟨by linarith [h.2], by linarith [h.1]⟩
          simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hnz, mul_neg, Real.sinh_neg, div_neg]
        · have hnz : -z ∉ (Icc (-R) R)ᶜ := fun h => hz fun h' => h ⟨by linarith [h'.2], by linarith [h'.1]⟩
          simp [Set.indicator_of_notMem hz, Set.indicator_of_notMem hnz]
      linarith
    have hsplit : ∫ z : ℝ, (g (s + z) - g s) / Real.sinh (π * z) =
        ∫ z in Icc (-R) R, (g (s + z) - g s) / Real.sinh (π * z) := by
      have hu := integral_add_compl (s := Icc (-R) R) measurableSet_Icc hint
      rw [hcompl_zero, add_zero] at hu
      exact hu.symm
    rw [hsplit]
    set B1 : ℝ := C_v (j + 1) * M * τ₁ ^ ((2 : ℤ) - ↑(j + 1))
    have hB1_nn : 0 ≤ B1 := le_trans (abs_nonneg _) (hC_v (j + 1) 0)
    have hpt : ∀ z ∈ Icc (-R) R,
        ‖(g (s + z) - g s) / Real.sinh (π * z)‖ ≤ B1 / π := by
      intro z _
      rw [Real.norm_eq_abs]
      have hdiff : |g (s + z) - g s| ≤ B1 * |z| := by
        have hlip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := g) (f' := deriv g) (s := univ) (C := B1)
          (fun x _ => (hg.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
          (fun x _ => by
            rw [Real.norm_eq_abs]
            show |deriv (iteratedDeriv j v) x| ≤ B1
            rw [← iteratedDeriv_succ]
            exact hC_v (j + 1) x)
          convex_univ (mem_univ s) (mem_univ (s + z))
        simpa [Real.norm_eq_abs, add_sub_cancel_left] using hlip
      by_cases hz0 : z = 0
      · simp only [hz0, add_zero, sub_self, zero_div, abs_zero]; positivity
      · rw [abs_div]
        calc |g (s + z) - g s| / |Real.sinh (π * z)|
            ≤ (B1 * |z|) / |Real.sinh (π * z)| :=
              div_le_div_of_nonneg_right hdiff (abs_nonneg _)
          _ = B1 * |z / Real.sinh (π * z)| := by rw [abs_div, mul_div_assoc]
          _ ≤ B1 * (1 / π) := mul_le_mul_of_nonneg_left (abs_mul_inv_sinh_le z) hB1_nn
          _ = B1 / π := by ring
    have hnorm := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (hs := measure_Icc_lt_top) hpt
    rw [Real.norm_eq_abs, Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at hnorm
    have hpow : τ₁ ^ ((2 : ℤ) - ↑(j + 1)) * τ₁ = τ₁ ^ ((2 : ℤ) - ↑j) := by
      rw [show (2 : ℤ) - ↑j = ((2 : ℤ) - ↑(j + 1)) + 1 by omega, zpow_add₀ hτ₁.ne', zpow_one]
    calc |∫ z in Icc (-R) R, (g (s + z) - g s) / Real.sinh (π * z)|
        ≤ (B1 / π) * (R - -R) := hnorm
      _ = (46 / π) * C_v (j + 1) * M * (τ₁ ^ ((2 : ℤ) - ↑(j + 1)) * τ₁) := by
          simp only [B1, R]; ring
      _ = (46 / π) * C_v (j + 1) * M * τ₁ ^ ((2 : ℤ) - ↑j) := by rw [hpow]
  have hC_nn : ∀ j : ℕ, 0 ≤ C_v j * M := fun j => by
    have := le_trans (abs_nonneg _) (hC_v j 0)
    have htp : 0 < τ₁ ^ ((2 : ℤ) - ↑j) := zpow_pos hτ₁ _
    nlinarith [mul_nonneg_iff.mp this]
  have hbd1 : |iteratedDeriv r (fctThetaD v) t| ≤
      (46 / π) * max (C_v (r + 1)) (C_v (2 * N + 2)) * M * τ₁ ^ ((2 : ℤ) - ↑r) := by
    have hu := hunif r t ht
    have htp : 0 ≤ τ₁ ^ ((2 : ℤ) - ↑r) := (zpow_pos hτ₁ _).le
    have hpi : 0 ≤ 46 / π := by positivity
    calc |iteratedDeriv r (fctThetaD v) t|
        ≤ (46 / π) * (C_v (r + 1) * M) * τ₁ ^ ((2 : ℤ) - ↑r) := by linarith
      _ ≤ (46 / π) * (max (C_v (r + 1)) (C_v (2 * N + 2)) * M) * τ₁ ^ ((2 : ℤ) - ↑r) := by
          gcongr; exact le_max_left _ _
      _ = (46 / π) * max (C_v (r + 1)) (C_v (2 * N + 2)) * M * τ₁ ^ ((2 : ℤ) - ↑r) := by ring
  rcases le_or_gt τ₁ |t| with hge | hlt
  · have hratio : 1 ≤ (|t| / τ₁) ^ (2 * N + 1 - r) :=
      one_le_pow₀ ((one_le_div hτ₁).mpr hge)
    rw [min_eq_left hratio, mul_one]
    exact hbd1
  · have hratio : (|t| / τ₁) ^ (2 * N + 1 - r) ≤ 1 :=
      pow_le_one₀ (by positivity) ((div_le_one hτ₁).mpr hlt.le)
    rw [min_eq_right hratio]
    by_cases hr : 2 * N + 1 ≤ r
    · have hsub : 2 * N + 1 - r = 0 := Nat.sub_eq_zero_of_le hr
      rw [hsub, pow_zero, mul_one]
      exact hbd1
    · have hr' : r < 2 * N + 1 := Nat.lt_of_not_ge hr
      have hzero : ∀ j < 2 * N + 1 - r,
          iteratedDeriv j (iteratedDeriv r (fctThetaD v)) 0 = 0 := by
        intro j hj
        rw [iteratedDeriv_iteratedDeriv_eq]
        rcases Nat.even_or_odd (j + r) with ⟨k, hk⟩ | ⟨k, hk⟩
        · rw [show j + r = 2 * k by omega]
          exact iteratedDeriv_even_zero_of_odd (fctThetaD_odd heven) k
        · rw [hk, iteratedDeriv_odd_fctThetaD_zero hv hcomp heven k, hmom k (by omega), mul_zero]
      have htop_bound : ∀ s, |s| ≤ τ₁ →
          |iteratedDeriv (2 * N + 1 - r) (iteratedDeriv r (fctThetaD v)) s| ≤
            (46 / π) * C_v (2 * N + 2) * M * τ₁ ^ ((2 : ℤ) - ↑(2 * N + 1)) := by
        intro s hs
        rw [iteratedDeriv_iteratedDeriv_eq, show 2 * N + 1 - r + r = 2 * N + 1 by omega]
        exact hunif (2 * N + 1) s (by linarith)
      have hB_nn : 0 ≤ (46 / π) * C_v (2 * N + 2) * M * τ₁ ^ ((2 : ℤ) - ↑(2 * N + 1)) := by
        have h1 := hC_nn (2 * N + 2)
        have h2 : 0 ≤ τ₁ ^ ((2 : ℤ) - ↑(2 * N + 1)) := (zpow_pos hτ₁ _).le
        have h3 : 0 ≤ 46 / π := by positivity
        nlinarith [mul_nonneg h3 h1]
      have htay := abs_le_of_iteratedDeriv_zero
        (contDiff_iteratedDeriv_infty (contDiff_fctThetaD hv hcomp) r) hzero hB_nn htop_bound t hlt.le
      have hpow_id : τ₁ ^ ((2 : ℤ) - ↑(2 * N + 1)) * |t| ^ (2 * N + 1 - r) =
          τ₁ ^ ((2 : ℤ) - ↑r) * (|t| / τ₁) ^ (2 * N + 1 - r) := by
        have htau : τ₁ ^ ((2 : ℤ) - ↑r) / τ₁ ^ (2 * N + 1 - r) =
            τ₁ ^ ((2 : ℤ) - ↑(2 * N + 1)) := by
          rw [← zpow_natCast τ₁, ← zpow_sub₀ hτ₁.ne']
          congr 1; omega
        rw [div_pow, mul_div_assoc', mul_comm (τ₁ ^ ((2 : ℤ) - ↑r)), mul_div_assoc, htau, mul_comm]
      calc |iteratedDeriv r (fctThetaD v) t|
          ≤ (46 / π) * C_v (2 * N + 2) * M * τ₁ ^ ((2 : ℤ) - ↑(2 * N + 1)) *
              |t| ^ (2 * N + 1 - r) := htay
        _ = (46 / π) * (C_v (2 * N + 2) * M) *
              (τ₁ ^ ((2 : ℤ) - ↑(2 * N + 1)) * |t| ^ (2 * N + 1 - r)) := by ring
        _ = (46 / π) * (C_v (2 * N + 2) * M) *
              (τ₁ ^ ((2 : ℤ) - ↑r) * (|t| / τ₁) ^ (2 * N + 1 - r)) := by rw [hpow_id]
        _ ≤ (46 / π) * (max (C_v (r + 1)) (C_v (2 * N + 2)) * M) *
              (τ₁ ^ ((2 : ℤ) - ↑r) * (|t| / τ₁) ^ (2 * N + 1 - r)) := by
            have h1 : 0 ≤ 46 / π := by positivity
            have h2 : 0 ≤ τ₁ ^ ((2 : ℤ) - ↑r) * (|t| / τ₁) ^ (2 * N + 1 - r) :=
              mul_nonneg (zpow_pos hτ₁ _).le (pow_nonneg (by positivity) _)
            gcongr; exact le_max_right _ _
        _ = (46 / π) * max (C_v (r + 1)) (C_v (2 * N + 2)) * M * τ₁ ^ ((2 : ℤ) - ↑r) *
              (|t| / τ₁) ^ (2 * N + 1 - r) := by ring

end FormalResearch.SignUncertainty.FctMoment
