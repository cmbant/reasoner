module

public import FormalResearch.SignUncertainty.CtOuterMain
public import FormalResearch.SignUncertainty.CtOuterPoisson
public import FormalResearch.SignUncertainty.CtOuterTheta

/-!
# `uct:outer-growth`: growth of `e^{-h}` on the strip

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:outer-growth` (Section "Growth of the outer
function").  **Proved.**

With `h = outerHbar` the continuous extension to `closedStrip` of the strip integral `outerH`
(`ct:outer`), `G_- = ζ^{1/2}(1-ζ)^{1/2}e^h`, `G_+ = b_{1/2} G_-` (`outerG`/`outerGbar`):

* `outerHbar_zero`, `outerHbar_one`: `h(0) = h(1) = 0` (and `h` is real on `[0,1]`: `outerHbar_real_of_re`);
* `H0_zero`, `exists_holo_H1`: `h` extends holomorphically to `D(0,1/2)` (the function `H0` of `ct:outer`) and,
  by `h(1-ζ) = h(ζ)`, to `D(1,1/2)` (`H1 ζ = H0 (1-ζ)`), and the extensions agree with `outerHbar` on `closedStrip`;
* `re_outerH_ge`, `re_outerHbar_ge`: `Re h(σ+iτ) ≥ -2 log(1+|τ|) - C` on `S`, resp. `closedStrip`
  (the Poisson representation `re_outerH`, `u_r ≥ ½ log(6/π²) - log(1+t²)`, and
  `1+|t| ≤ (1+|τ|)(1+|τ-t|)`);
* `norm_exp_neg_outerHbar_le`: `|e^{-h(ζ)}| ≤ C (1+τ²)` on `closedStrip`;
* `outerGbar_inv_le`: `|G_ε(ζ)|⁻¹ ≤ C' (1+τ²)` on `closedStrip` for `|τ| ≥ 1/2`, all `ε` (the Blaschke factor only enters for `ε = 1`).

The bound on the two discs of the TeX statement (`e^{-h}` bounded on `D(0,1/2)`, `D(1,1/2)`) is not formalised
separately: on `closedStrip` it is the strip bound, and off `closedStrip` it is continuity of the holomorphic
extension on compact subdiscs.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory FormalResearch.StripPoisson
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- The Poisson tail weight `w(s) = (16/π) e^{-(π/2)|s|}`. -/
noncomputable def poissonW (s : ℝ) : ℝ := 16 / π * Real.exp (-(π / 2) * |s|)

lemma integrable_poissonW : Integrable poissonW :=
  (integrable_exp_neg_abs' (c := π / 2) (by positivity)).const_mul (16 / π)

lemma poissonW_nonneg (s : ℝ) : 0 ≤ poissonW s := by unfold poissonW; positivity

/-- `P(s) log(1+|s|) ≤ log 2 · P(s) + w(s)` for the strip Poisson kernel. -/
lemma poissonK_log_le {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (s : ℝ) :
    Real.log (1 + |s|) * poissonK x s ≤ Real.log 2 * poissonK x s + poissonW s := by
  have hP : 0 ≤ poissonK x s := (poissonK_pos h0 h1 s).le
  have hW := poissonW_nonneg s
  rcases le_or_gt |s| 1 with hs | hs
  · have : Real.log (1 + |s|) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) (by linarith)
    nlinarith
  · have hPb := poissonK_le h0 h1 hs.le
    have hlog : Real.log (1 + |s|) ≤ |s| := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + |s|)
      linarith
    have hl0 : 0 ≤ Real.log (1 + |s|) := Real.log_nonneg (by linarith [abs_nonneg s])
    have hl2 : 0 ≤ Real.log 2 * poissonK x s := mul_nonneg (Real.log_nonneg (by norm_num)) hP
    have hxe : |s| * Real.exp (-(π / 2) * |s|) ≤ 2 / π := by
      have hu : (π / 2 * |s|) * Real.exp (-(π / 2 * |s|)) ≤ 1 := by
        have := Real.add_one_le_exp (π / 2 * |s|)
        have h5 : 0 < Real.exp (π / 2 * |s|) := Real.exp_pos _
        rw [Real.exp_neg, mul_inv_le_iff₀ h5]
        linarith
      have e : |s| * Real.exp (-(π / 2) * |s|) = 2 / π * ((π / 2 * |s|) * Real.exp (-(π / 2 * |s|))) := by
        have := Real.pi_pos
        field_simp
      rw [e]
      have := Real.pi_pos
      calc 2 / π * ((π / 2 * |s|) * Real.exp (-(π / 2 * |s|))) ≤ 2 / π * 1 :=
            mul_le_mul_of_nonneg_left hu (by positivity)
        _ = _ := by ring
    have hsplit : Real.exp (-(π * |s|)) = Real.exp (-(π / 2) * |s|) * Real.exp (-(π / 2) * |s|) := by
      rw [← Real.exp_add]; congr 1; ring
    have key : Real.log (1 + |s|) * poissonK x s ≤ poissonW s := by
      calc Real.log (1 + |s|) * poissonK x s ≤ |s| * (8 * Real.exp (-(π * |s|))) :=
            mul_le_mul hlog hPb hP (abs_nonneg s)
        _ = 8 * (|s| * Real.exp (-(π / 2) * |s|)) * Real.exp (-(π / 2) * |s|) := by rw [hsplit]; ring
        _ ≤ 8 * (2 / π) * Real.exp (-(π / 2) * |s|) := by
            gcongr
        _ = poissonW s := by unfold poissonW; ring
    linarith

lemma log_one_add_sq_le_add (τ t : ℝ) :
    Real.log (1 + t ^ 2) ≤ 2 * Real.log (1 + |τ|) + 2 * Real.log (1 + |τ - t|) := by
  have h1 : 1 + t ^ 2 ≤ ((1 + |τ|) * (1 + |τ - t|)) ^ 2 := by
    have ht : |t| ≤ |τ| + |τ - t| := by
      calc |t| = |τ - (τ - t)| := by ring_nf
        _ ≤ |τ| + |τ - t| := by simpa using abs_sub (τ) (τ - t)
    have h2 : 1 + |t| ≤ (1 + |τ|) * (1 + |τ - t|) := by
      nlinarith [abs_nonneg τ, abs_nonneg (τ - t)]
    have h3 : 0 ≤ 1 + |t| := by positivity
    calc 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
      _ ≤ _ := pow_le_pow_left₀ h3 h2 2
  have hpos : 0 < 1 + t ^ 2 := by positivity
  calc Real.log (1 + t ^ 2) ≤ Real.log (((1 + |τ|) * (1 + |τ - t|)) ^ 2) := Real.log_le_log hpos h1
    _ = 2 * Real.log (1 + |τ|) + 2 * Real.log (1 + |τ - t|) := by
        rw [Real.log_pow, Real.log_mul (by positivity) (by positivity)]
        push_cast; ring

/-- Lower bound of the real part of `h` on the open strip. -/
theorem re_outerH_ge : ∃ C : ℝ, ∀ ζ ∈ strip, -2 * Real.log (1 + |ζ.im|) - C ≤ (outerH ζ).re := by
  set A : ℝ := (1 / 2) * Real.log (6 / π ^ 2) with hA
  set K : ℝ := ∫ s : ℝ, poissonW s with hK
  refine ⟨-A + 2 * Real.log 2 + 2 * K, fun ζ hζ => ?_⟩
  set x : ℝ := ζ.re with hx
  set y : ℝ := ζ.im with hy
  have hre := re_outerH hζ
  have hPint : Integrable (poissonK x) := integrable_poissonK hζ.1 hζ.2
  have hPpos : ∀ s, 0 ≤ poissonK x s := fun s => (poissonK_pos hζ.1 hζ.2 s).le
  set f : ℝ → ℝ := fun t => (A - 2 * Real.log (1 + |y|) - 2 * Real.log 2) * poissonK x (y - t) -
    2 * poissonW (y - t) with hf
  have hfint : Integrable f :=
    (((hPint.comp_sub_left y).const_mul _).sub ((integrable_poissonW.comp_sub_left y).const_mul 2))
  have hint1 : Integrable fun t : ℝ => uR t * poissonK x (y - t) := by
    refine ((integrable_integrand hζ).re).congr (Eventually.of_forall fun t => ?_)
    simp only [RCLike.re_to_complex]
    rw [div_eq_mul_inv, ← one_div, Complex.re_ofReal_mul, re_inv_sin_arg hζ]
  have hpt : ∀ t : ℝ, f t ≤ uR t * poissonK x (y - t) := by
    intro t
    have hP := hPpos (y - t)
    have h1 := uR_ge t
    have h2 := log_one_add_sq_le_add y t
    have h3 := poissonK_log_le hζ.1 hζ.2 (y - t)
    have h4 : (A - 2 * Real.log (1 + |y|) - 2 * Real.log (1 + |y - t|)) * poissonK x (y - t) ≤
        uR t * poissonK x (y - t) :=
      mul_le_mul_of_nonneg_right (by linarith) hP
    simp only [hf]
    nlinarith
  have hI : ∫ t : ℝ, f t ≤ ∫ t : ℝ, uR t * poissonK x (y - t) := integral_mono hfint hint1 hpt
  have hcalc : ∫ t : ℝ, f t = (A - 2 * Real.log (1 + |y|) - 2 * Real.log 2) - 2 * K := by
    rw [hf, integral_sub ((hPint.comp_sub_left y).const_mul _) ((integrable_poissonW.comp_sub_left y).const_mul 2),
      integral_const_mul, integral_const_mul, integral_sub_left_eq_self (poissonK x) volume y,
      integral_sub_left_eq_self poissonW volume y, integral_poissonK hζ.1 hζ.2]
    ring
  rw [hre]
  linarith

/-- Lower bound of the real part of `h` on the closed strip. -/
theorem re_outerHbar_ge : ∃ C : ℝ, ∀ ζ ∈ closedStrip, -2 * Real.log (1 + |ζ.im|) - C ≤ (outerHbar ζ).re := by
  obtain ⟨C, hC⟩ := re_outerH_ge
  refine ⟨C, fun ζ hζ => ?_⟩
  have := neBot_nhdsWithin_strip hζ
  have hf : Tendsto (fun ξ => (outerH ξ).re) (𝓝[strip] ζ) (𝓝 (outerHbar ζ).re) :=
    (Complex.continuous_re.tendsto _).comp (outerHbar_tendsto hζ)
  have hg : Tendsto (fun ξ : ℂ => -2 * Real.log (1 + |ξ.im|) - C) (𝓝[strip] ζ)
      (𝓝 (-2 * Real.log (1 + |ζ.im|) - C)) := by
    have : Continuous fun ξ : ℂ => -2 * Real.log (1 + |ξ.im|) - C := by
      refine Continuous.sub (Continuous.mul continuous_const (Continuous.log ?_ ?_)) continuous_const
      · fun_prop
      · intro ξ; positivity
    exact (this.tendsto ζ).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hg hf ?_
  filter_upwards [self_mem_nhdsWithin] with ξ hξ using hC ξ hξ

/-- **`uct:outer-growth` (growth).** `|e^{-h(σ+iτ)}| ≤ C(1+τ²)` on the closed strip. -/
theorem norm_exp_neg_outerHbar_le :
    ∃ C : ℝ, ∀ ζ ∈ closedStrip, ‖Complex.exp (-outerHbar ζ)‖ ≤ C * (1 + ζ.im ^ 2) := by
  obtain ⟨C, hC⟩ := re_outerHbar_ge
  refine ⟨2 * Real.exp C, fun ζ hζ => ?_⟩
  rw [Complex.norm_exp, Complex.neg_re]
  have h1 := hC ζ hζ
  set y : ℝ := |ζ.im| with hy
  have hy0 : 0 ≤ y := abs_nonneg _
  have h2 : Real.exp (-(outerHbar ζ).re) ≤ Real.exp (2 * Real.log (1 + y) + C) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (2 * Real.log (1 + y) + C) = (1 + y) ^ 2 * Real.exp C := by
    rw [Real.exp_add, mul_comm 2, Real.exp_mul, Real.exp_log (by linarith)]
    norm_cast
  have h4 : (1 + y) ^ 2 ≤ 2 * (1 + ζ.im ^ 2) := by
    have := sq_abs ζ.im
    nlinarith [sq_nonneg (y - 1)]
  calc Real.exp (-(outerHbar ζ).re) ≤ (1 + y) ^ 2 * Real.exp C := h3 ▸ h2
    _ ≤ 2 * (1 + ζ.im ^ 2) * Real.exp C := mul_le_mul_of_nonneg_right h4 (Real.exp_pos C).le
    _ = _ := by ring

/-- `h` is real on `[0,1]`. -/
lemma outerHbar_real_of_re {ζ : ℂ} (hζ : ζ ∈ closedStrip) (him : ζ.im = 0) : (outerHbar ζ).im = 0 := by
  have h := outerHbar_conj hζ
  have hc : starRingEnd ℂ ζ = ζ := by
    apply Complex.ext <;> simp [him]
  rw [hc] at h
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-- `h(0) = 0`. -/
theorem outerHbar_zero : outerHbar 0 = 0 := by
  have hcl : (0 : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  have him := outerHbar_real_of_re hcl (by simp)
  have hre := re_outerHbar_left 0
  simp only [Complex.ofReal_zero, mul_zero, uR_zero] at hre
  exact Complex.ext hre him

/-- `h(1) = 0`. -/
theorem outerHbar_one : outerHbar 1 = 0 := by
  have hcl : (0 : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  have := outerHbar_oneSub hcl
  simpa [outerHbar_zero] using this

lemma H0_zero : H0 0 = 0 := by
  have h := outerHbar_eq_H0 (ζ := 0) ⟨by simp, by simp⟩ (by simp)
  rw [← h, outerHbar_zero]

/-- `h` extends holomorphically to `D(1, 1/2)` as `H1 ζ = H0 (1 - ζ)`, agreeing with `outerHbar` on `closedStrip`. -/
theorem exists_holo_H1 : ∃ H1 : ℂ → ℂ, DifferentiableOn ℂ H1 (ball (1 : ℂ) (1 / 2)) ∧ H1 1 = 0 ∧
    ∀ ζ ∈ closedStrip, ζ ∈ ball (1 : ℂ) (1 / 2) → outerHbar ζ = H1 ζ := by
  refine ⟨fun ζ => H0 (1 - ζ), ?_, by simp [H0_zero], fun ζ hζ hb => ?_⟩
  · refine differentiableOn_H0.comp (by fun_prop : Differentiable ℂ fun z : ℂ => 1 - z).differentiableOn ?_
    intro z hz
    simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hz
  · have hm : (1 - ζ) ∈ closedStrip := ⟨by simp; exact hζ.2, by simp; exact hζ.1⟩
    have hb' : (1 - ζ) ∈ ball (0 : ℂ) (1 / 2) := by
      simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hb
    show outerHbar ζ = H0 (1 - ζ)
    rw [← outerHbar_eq_H0 hm hb', outerHbar_oneSub hζ]

lemma exists_norm_bHalf_lower : ∃ c : ℝ, 0 < c ∧ ∀ ζ ∈ closedStrip, 1 / 2 ≤ |ζ.im| → c ≤ ‖bHalf ζ‖ := by
  set S0 : ℝ := Real.sinh (π / 4) ^ 2 with hS0
  have hS0pos : 0 < S0 := by
    have : 0 < Real.sinh (π / 4) := Real.sinh_pos_iff.mpr (by positivity)
    positivity
  refine ⟨Real.sqrt (S0 / (1 + S0)), Real.sqrt_pos.mpr (by positivity), fun ζ hζ hτ => ?_⟩
  set S : ℝ := Real.sinh (bArg ζ).im ^ 2 with hS
  have hy : π / 4 ≤ |(bArg ζ).im| := by
    rw [bArg_im, abs_neg, abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
    nlinarith [Real.pi_pos]
  have hSS : S0 ≤ S := by
    rw [hS0, hS]
    have h1 : Real.sinh (π / 4) ≤ Real.sinh |(bArg ζ).im| := Real.sinh_le_sinh.mpr hy
    have h2 : Real.sinh |(bArg ζ).im| ^ 2 = Real.sinh (bArg ζ).im ^ 2 := by
      rcases abs_cases (bArg ζ).im with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
      · rw [h, Real.sinh_neg, neg_sq]
    rw [← h2]
    exact pow_le_pow_left₀ (by have := Real.sinh_pos_iff.mpr (by positivity : 0 < π / 4); positivity) h1 2
  have hS0' : 0 ≤ S := by rw [hS]; positivity
  have hsin := Real.sin_sq_add_cos_sq (bArg ζ).re
  have hcpos := cos_bArg_pos hζ
  have hd := norm_bHalf_sq ζ
  have hden : 0 < Real.cos (bArg ζ).re ^ 2 + S := by positivity
  have hnum : S / (1 + S) ≤ ‖bHalf ζ‖ ^ 2 := by
    rw [hd, div_le_div_iff₀ (by positivity) hden]
    nlinarith [sq_nonneg (Real.sin (bArg ζ).re), mul_nonneg hS0' (sq_nonneg (Real.sin (bArg ζ).re))]
  have hmono : S0 / (1 + S0) ≤ S / (1 + S) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  exact Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hmono.trans hnum⟩

/-- **`uct:outer-growth` (consequence).** `|G_ε(σ+iτ)|⁻¹ ≤ C'(1+τ²)` on `closedStrip` for `|τ| ≥ 1/2`, all `ε` (the Blaschke factor only enters for `ε = 1`). -/
theorem outerGbar_inv_le {ε : ℝ} :
    ∃ C : ℝ, ∀ ζ ∈ closedStrip, 1 / 2 ≤ |ζ.im| → ‖(outerGbar ε ζ)⁻¹‖ ≤ C * (1 + ζ.im ^ 2) := by
  obtain ⟨C, hC⟩ := norm_exp_neg_outerHbar_le
  obtain ⟨c, hc, hcb⟩ := exists_norm_bHalf_lower
  set c' : ℝ := min 1 c with hc'
  have hc'pos : 0 < c' := lt_min one_pos hc
  refine ⟨2 / c' * C, fun ζ hζ hτ => ?_⟩
  have hbB : c' ≤ ‖(if ε = 1 then bHalf ζ else 1)‖ := by
    by_cases h : ε = 1
    · simp only [h, ↓reduceIte]; exact (min_le_right _ _).trans (hcb ζ hζ hτ)
    · simp only [h, ↓reduceIte, norm_one]; exact min_le_left _ _
  have hz : 1 / 2 ≤ ‖ζ‖ := hτ.trans (by simpa using Complex.abs_im_le_norm ζ)
  have hz1 : 1 / 2 ≤ ‖1 - ζ‖ := hτ.trans (by
    have := Complex.abs_im_le_norm (1 - ζ)
    simpa using this)
  have hsq : 1 / 2 ≤ ‖ζ ^ (1 / 2 : ℂ)‖ * ‖(1 - ζ) ^ (1 / 2 : ℂ)‖ := by
    rw [norm_cpow_half, norm_cpow_half, ← Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    have h4 : (1 / 4 : ℝ) ≤ ‖ζ‖ * ‖1 - ζ‖ := by nlinarith
    calc (1 / 2 : ℝ) = (1 / 4 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) h4 (by norm_num)
  have hnorm : ‖outerGbar ε ζ‖ =
      ‖(if ε = 1 then bHalf ζ else 1)‖ * (‖ζ ^ (1 / 2 : ℂ)‖ * ‖(1 - ζ) ^ (1 / 2 : ℂ)‖ *
        ‖Complex.exp (outerHbar ζ)‖) := by
    unfold outerGbar outerGm
    rw [norm_mul, norm_mul, norm_mul]
  have hexp : ‖Complex.exp (outerHbar ζ)‖ * ‖Complex.exp (-outerHbar ζ)‖ = 1 := by
    rw [← norm_mul, ← Complex.exp_add]; simp
  have hepos : 0 < ‖Complex.exp (outerHbar ζ)‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hGpos : 0 < ‖outerGbar ε ζ‖ := by
    rw [hnorm]
    have : 0 < ‖(if ε = 1 then bHalf ζ else 1)‖ := lt_of_lt_of_le hc'pos hbB
    have h2 : 0 < ‖ζ ^ (1 / 2 : ℂ)‖ * ‖(1 - ζ) ^ (1 / 2 : ℂ)‖ := lt_of_lt_of_le (by norm_num) hsq
    exact mul_pos this (mul_pos h2 hepos)
  have hlow : c' * (1 / 2) * ‖Complex.exp (outerHbar ζ)‖ ≤ ‖outerGbar ε ζ‖ := by
    rw [hnorm]
    calc c' * (1 / 2) * ‖Complex.exp (outerHbar ζ)‖
        ≤ ‖(if ε = 1 then bHalf ζ else 1)‖ * (‖ζ ^ (1 / 2 : ℂ)‖ * ‖(1 - ζ) ^ (1 / 2 : ℂ)‖) *
          ‖Complex.exp (outerHbar ζ)‖ := by
          gcongr
      _ = _ := by ring
  rw [norm_inv]
  have hCe := hC ζ hζ
  have hinv : (‖outerGbar ε ζ‖)⁻¹ ≤ (c' * (1 / 2) * ‖Complex.exp (outerHbar ζ)‖)⁻¹ :=
    inv_anti₀ (by positivity) hlow
  have e : (c' * (1 / 2) * ‖Complex.exp (outerHbar ζ)‖)⁻¹ = 2 / c' * ‖Complex.exp (-outerHbar ζ)‖ := by
    have : ‖Complex.exp (-outerHbar ζ)‖ = (‖Complex.exp (outerHbar ζ)‖)⁻¹ := by
      rw [Complex.exp_neg, norm_inv]
    rw [this]; field_simp
  calc (‖outerGbar ε ζ‖)⁻¹ ≤ 2 / c' * ‖Complex.exp (-outerHbar ζ)‖ := e ▸ hinv
    _ ≤ 2 / c' * (C * (1 + ζ.im ^ 2)) := mul_le_mul_of_nonneg_left hCe (by positivity)
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.CtOuter.norm_exp_neg_outerHbar_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_exp_neg_outerHbar_le

/-- info: 'FormalResearch.SignUncertainty.CtOuter.outerGbar_inv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerGbar_inv_le

/-- info: 'FormalResearch.SignUncertainty.CtOuter.exists_holo_H1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_holo_H1

end FormalResearch.SignUncertainty.CtOuter
