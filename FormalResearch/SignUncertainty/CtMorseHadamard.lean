module

public import FormalResearch.SignUncertainty.CtMorseKernel
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Hadamard quotients `h(x)/x = ∫₀¹ h'(tx) dt` and their derivatives

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:morse-expansion`.  **Proved.**

`tay k H (x) = ∫₀¹ t^k H(tx) dt`.  For `h ∈ C^n_c` with `h(0) = 0`, `g = tay 0 h'` satisfies `x g(x) = h(x)`, is `C^{n-1}` with compact support,
and `g^{(i)} = tay i h^{(i+1)}` (so `|g^{(i)}| ≤ sup|h^{(i+1)}| / (i+1)`, `g^{(i)}(0) = h^{(i+1)}(0)/(i+1)`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtMorse

/-- `tay k H x = ∫₀¹ t^k H(tx) dt`. -/
noncomputable def tay (k : ℕ) (H : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, ((t : ℝ) : ℂ) ^ k * H (t * x)

lemma tay_zero (k : ℕ) (H : ℝ → ℂ) : tay k H 0 = H 0 / ((k : ℂ) + 1) := by
  unfold tay
  simp only [mul_zero]
  have : ∫ t in (0 : ℝ)..1, ((t : ℝ) : ℂ) ^ k * H 0 = (∫ t in (0 : ℝ)..1, ((t : ℝ) : ℂ) ^ k) * H 0 :=
    intervalIntegral.integral_mul_const _ _
  rw [this]
  have h2 : ∫ t in (0 : ℝ)..1, ((t : ℝ) : ℂ) ^ k = (1 / ((k : ℂ) + 1)) := by
    have : ∫ t in (0 : ℝ)..1, ((t : ℝ) : ℂ) ^ k = ((∫ t in (0 : ℝ)..1, t ^ k : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]; simp
    rw [this, integral_pow]
    push_cast; simp
  rw [h2]; ring

lemma norm_tay_le {H : ℝ → ℂ} (hc : Continuous H) {B : ℝ} (hB : ∀ x, ‖H x‖ ≤ B) (k : ℕ) (x : ℝ) :
    ‖tay k H x‖ ≤ B / ((k : ℝ) + 1) := by
  unfold tay
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (zero_le_one) (g := fun t : ℝ => B * t ^ k)
    (f := fun t : ℝ => ((t : ℝ) : ℂ) ^ k * H (t * x))
    (Eventually.of_forall fun t ht => by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      calc t ^ k * ‖H (t * x)‖ ≤ t ^ k * B := mul_le_mul_of_nonneg_left (hB _) (by have := ht.1; positivity)
        _ = B * t ^ k := mul_comm _ _)
    (Continuous.intervalIntegrable (by fun_prop) 0 1)
  rw [intervalIntegral.integral_const_mul, integral_pow] at this
  simpa [div_eq_mul_inv] using this

lemma continuous_tay {H : ℝ → ℂ} (hc : Continuous H) (k : ℕ) : Continuous (tay k H) := by
  unfold tay
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun x t => ((t : ℝ) : ℂ) ^ k * H (t * x)) ?_ 0 1
  have : Continuous fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) ^ k * H (p.2 * p.1) :=
    ((Complex.continuous_ofReal.comp continuous_snd).pow k).mul (hc.comp (continuous_snd.mul continuous_fst))
  exact this

/-- Differentiation under the integral: `d/dx tay k H = tay (k+1) H'`. -/
lemma hasDerivAt_tay {H H' : ℝ → ℂ} (hH : ∀ x, HasDerivAt H (H' x) x) (hc' : Continuous H')
    (hcs : HasCompactSupport H') (k : ℕ) (x : ℝ) : HasDerivAt (tay k H) (tay (k + 1) H' x) x := by
  have hcH : Continuous H := continuous_iff_continuousAt.mpr fun x => (hH x).continuousAt
  obtain ⟨B, hB⟩ := hc'.bounded_above_of_compact_support hcs
  have hmeas : ∀ y : ℝ, AEStronglyMeasurable (fun t : ℝ => ((t : ℝ) : ℂ) ^ k * H (t * y)) (volume.restrict (Ι (0 : ℝ) 1)) := by
    intro y
    have : Continuous fun t : ℝ => ((t : ℝ) : ℂ) ^ k * H (t * y) :=
      ((Complex.continuous_ofReal).pow k).mul (hcH.comp (continuous_id.mul continuous_const))
    exact this.aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun t : ℝ => ((t : ℝ) : ℂ) ^ (k + 1) * H' (t * x)) (volume.restrict (Ι (0 : ℝ) 1)) := by
    have : Continuous fun t : ℝ => ((t : ℝ) : ℂ) ^ (k + 1) * H' (t * x) :=
      ((Complex.continuous_ofReal).pow _).mul (hc'.comp (continuous_id.mul continuous_const))
    exact this.aestronglyMeasurable
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := (0 : ℝ)) (b := 1)
    (F := fun y t => ((t : ℝ) : ℂ) ^ k * H (t * y)) (F' := fun y t => ((t : ℝ) : ℂ) ^ (k + 1) * H' (t * y))
    (x₀ := x) (s := univ) (bound := fun _ => B) Filter.univ_mem (Eventually.of_forall hmeas)
    ((Continuous.intervalIntegrable (by
      have : Continuous fun t : ℝ => ((t : ℝ) : ℂ) ^ k * H (t * x) :=
        ((Complex.continuous_ofReal).pow k).mul (hcH.comp (continuous_id.mul continuous_const))
      exact this) 0 1)) hmeas'
    (Eventually.of_forall fun t ht y _ => by
      have ht' : t ∈ Ioc (0 : ℝ) 1 := by rwa [uIoc_of_le zero_le_one] at ht
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht'.1]
      have h1 : t ^ (k + 1) ≤ 1 := pow_le_one₀ ht'.1.le ht'.2
      calc t ^ (k + 1) * ‖H' (t * y)‖ ≤ 1 * B :=
            mul_le_mul h1 (hB _) (norm_nonneg _) zero_le_one
        _ = B := one_mul B)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht y _ => by
      have h1 : HasDerivAt (fun y : ℝ => t * y) t y := by simpa using (hasDerivAt_id y).const_mul t
      have h2 := (hH (t * y)).scomp y h1
      have h3 := h2.const_mul (((t : ℝ) : ℂ) ^ k)
      refine h3.congr_deriv ?_
      simp only [pow_succ, Complex.real_smul]
      ring)
  exact this.2

/-- Support condition: `f` vanishes for `|x| > a`. -/
def Supp (a : ℝ) (f : ℝ → ℂ) : Prop := ∀ x : ℝ, a < |x| → f x = 0

lemma Supp.hasCompactSupport {a : ℝ} {f : ℝ → ℂ} (h : Supp a f) : HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun x hx => h x ?_
  by_contra hle
  exact hx (abs_le.mp (not_lt.mp hle))

lemma Supp.deriv {a : ℝ} {f : ℝ → ℂ} (h : Supp a f) : Supp a (deriv f) := by
  intro x hx
  have hev : f =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
    have : ∀ᶠ y : ℝ in 𝓝 x, a < |y| := (continuous_abs.tendsto x).eventually (lt_mem_nhds hx)
    filter_upwards [this] with y hy using h y hy
  rw [hev.deriv_eq]; simp

lemma Supp.iteratedDeriv {a : ℝ} {f : ℝ → ℂ} (h : Supp a f) (j : ℕ) : Supp a (iteratedDeriv j f) := by
  induction j with
  | zero => simpa using h
  | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv

lemma Supp.mono {a b : ℝ} {f : ℝ → ℂ} (h : Supp a f) (hab : a ≤ b) : Supp b f :=
  fun x hx => h x (lt_of_le_of_lt hab hx)

section Had

variable {h : ℝ → ℂ} {n : ℕ} {a : ℝ}

/-- The Hadamard quotient `g = tay 0 h'`, `h(x) = x g(x)`. -/
noncomputable def hadG (h : ℝ → ℂ) : ℝ → ℂ := tay 0 (iteratedDeriv 1 h)

lemma iteratedDeriv_hadG (hh : ContDiff ℝ n h) (hs : Supp a h) {i : ℕ} (hi : i + 1 ≤ n) :
    iteratedDeriv i (hadG h) = tay i (iteratedDeriv (i + 1) h) := by
  induction i with
  | zero => simp [hadG]
  | succ i ih =>
    have hi' : i + 1 ≤ n := by omega
    rw [iteratedDeriv_succ, ih hi']
    funext x
    have hd : ∀ y, HasDerivAt (iteratedDeriv (i + 1) h) (iteratedDeriv (i + 2) h y) y := by
      intro y
      have := (hh.differentiable_iteratedDeriv (i + 1) (by exact_mod_cast hi)) y
      have h2 := this.hasDerivAt
      rwa [← iteratedDeriv_succ] at h2
    have hc : Continuous (iteratedDeriv (i + 2) h) := hh.continuous_iteratedDeriv (i + 2) (by exact_mod_cast hi)
    exact (hasDerivAt_tay hd hc ((hs.iteratedDeriv (i + 2)).hasCompactSupport) i x).deriv

lemma contDiff_hadG (hh : ContDiff ℝ (n + 1 : ℕ) h) (hs : Supp a h) : ContDiff ℝ n (hadG h) := by
  have key : ContDiff ℝ ((n : ℕ∞)) (hadG h) := by
    rw [contDiff_iff_iteratedDeriv]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hi' : i + 1 ≤ n + 1 := by have : i ≤ n := by exact_mod_cast hi
                                     omega
      rw [iteratedDeriv_hadG hh hs hi']
      exact continuous_tay (hh.continuous_iteratedDeriv (i + 1) (by exact_mod_cast hi')) i
    · have hi' : i + 1 < n + 1 := by have : i < n := by exact_mod_cast hi
                                     omega
      have hi2 : i + 1 ≤ n + 1 := hi'.le
      rw [iteratedDeriv_hadG hh hs hi2]
      intro x
      have hd : ∀ y, HasDerivAt (iteratedDeriv (i + 1) h) (iteratedDeriv (i + 2) h y) y := by
        intro y
        have := (hh.differentiable_iteratedDeriv (i + 1) (by exact_mod_cast hi')) y
        have h2 := this.hasDerivAt
        rwa [← iteratedDeriv_succ] at h2
      have hc : Continuous (iteratedDeriv (i + 2) h) :=
        hh.continuous_iteratedDeriv (i + 2) (by exact_mod_cast hi')
      exact (hasDerivAt_tay hd hc ((hs.iteratedDeriv (i + 2)).hasCompactSupport) i x).differentiableAt
  exact_mod_cast key

lemma mul_hadG (hh : ContDiff ℝ 1 h) (h0 : h 0 = 0) (x : ℝ) : (x : ℂ) * hadG h x = h x := by
  unfold hadG tay
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => h (t * x)) (x • iteratedDeriv 1 h (t * x)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => t * x) x t := by simpa using (hasDerivAt_id t).mul_const x
    have h2 := ((hh.differentiable (by simp)) (t * x)).hasDerivAt
    rw [← iteratedDeriv_one] at h2
    exact h2.scomp t h1
  have hcont : Continuous fun t : ℝ => x • iteratedDeriv 1 h (t * x) := by
    have := hh.continuous_iteratedDeriv 1 (by simp)
    exact (this.comp (continuous_id.mul continuous_const)).const_smul x
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hcont.intervalIntegrable 0 1)
  simp only [one_mul, zero_mul, h0, sub_zero] at this
  rw [← this, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [pow_zero, one_mul, Complex.real_smul]

lemma supp_hadG (hh : ContDiff ℝ 1 h) (h0 : h 0 = 0) (ha : 0 ≤ a) (hs : Supp a h) : Supp a (hadG h) := by
  intro x hx
  have hx0 : (x : ℂ) ≠ 0 := by
    have : x ≠ 0 := by intro h'; rw [h', abs_zero] at hx; linarith
    exact_mod_cast this
  have := mul_hadG hh h0 x
  rw [hs x hx] at this
  exact (mul_eq_zero.mp this).resolve_left hx0

end Had

end FormalResearch.SignUncertainty.CtMorse
