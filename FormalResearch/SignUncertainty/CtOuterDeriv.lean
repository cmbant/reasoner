module

public import FormalResearch.SignUncertainty.CtOuterTheta

/-!
# The derivative of `h` at the edge point `0` (`ct:outer` (2), Taylor coefficients)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, proof of `ct:outer` (2) ("Exact Taylor coefficients":
`h'(0) = 2π ∫_0^∞ u_r(t) cosh(πt)/sinh²(πt) dt`).  **Proved.**

* `uR_sq_bound`: `|u_r(t)| ≤ C t²` for `|t| ≤ 1/2` (holomorphic extension, evenness, `u_r(0) = 0`);
* `hasDerivAt_outerH`: the derivative of `h` on `S` is `∫ u_r(t) (-π cos(π(ζ - it)) / sin²(π(ζ - it))) dt`;
* `deriv_H0_zero`: `H₀'(0) = ∫_ℝ u_r(t) π cosh(πt)/sinh²(πt) dt` (dominated convergence as `Re ζ → 0⁺`).
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

lemma utilde0_neg (z : ℂ) : utilde0 (-z) = utilde0 z := by
  unfold utilde0
  rw [mul_neg, sinhT_neg, sinhQ_neg, neg_sq]

/-- `|u_r(t)| ≤ C t²` near `0`. -/
lemma uR_sq_bound : ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 / 2 → |uR t| ≤ C * t ^ 2 := by
  have hdiff := differentiableOn_utilde0
  have hopen : IsOpen (ball (0 : ℂ) (3 / 5)) := isOpen_ball
  have hmem0 : (0 : ℂ) ∈ ball (0 : ℂ) (3 / 5) := mem_ball_self (by norm_num)
  have hnhds : ball (0 : ℂ) (3 / 5) ∈ 𝓝 (0 : ℂ) := hopen.mem_nhds hmem0
  have hv0 : utilde0 0 = 0 := by simp [utilde0, sinhT_zero, sinhQ_zero]
  -- `v z = z * w z`, `w = dslope v 0`
  set w : ℂ → ℂ := dslope utilde0 0 with hw
  have hwd : DifferentiableOn ℂ w (ball (0 : ℂ) (3 / 5)) := (differentiableOn_dslope hnhds).mpr hdiff
  have hw0 : w 0 = 0 := by
    rw [hw, dslope_same]
    have h1 : deriv (fun z => utilde0 (-z)) 0 = - deriv utilde0 (-0) := deriv_comp_neg _ _
    have h2 : (fun z => utilde0 (-z)) = utilde0 := funext utilde0_neg
    rw [h2, neg_zero] at h1
    linear_combination (1 / 2 : ℂ) * h1
  have hvw : ∀ z, utilde0 z = z * w z := by
    intro z
    by_cases hz : z = 0
    · subst hz; simp [hv0]
    · rw [hw, dslope_of_ne _ hz, slope_def_module, smul_eq_mul, hv0, sub_zero]; field_simp; simp
  set u : ℂ → ℂ := dslope w 0 with hu
  have hud : DifferentiableOn ℂ u (ball (0 : ℂ) (3 / 5)) := (differentiableOn_dslope hnhds).mpr hwd
  have hwu : ∀ z, w z = z * u z := by
    intro z
    by_cases hz : z = 0
    · subst hz; simp [hw0]
    · rw [hu, dslope_of_ne _ hz, slope_def_module, smul_eq_mul, hw0, sub_zero]; field_simp; simp
  have hcb : closedBall (0 : ℂ) (1 / 2) ⊆ ball (0 : ℂ) (3 / 5) := closedBall_subset_ball (by norm_num)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn (hud.continuousOn.mono hcb)
  refine ⟨M, fun t ht => ?_⟩
  have htb : (t : ℂ) ∈ closedBall (0 : ℂ) (1 / 2) := by
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]; exact ht
  have h1 := utilde0_ofReal (t := t) (by linarith [ht])
  have h2 : ‖utilde0 (t : ℂ)‖ ≤ M * t ^ 2 := by
    rw [hvw, hwu, ← mul_assoc, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← sq]
    calc |t| ^ 2 * ‖u t‖ ≤ |t| ^ 2 * M := by
          exact mul_le_mul_of_nonneg_left (hM _ htb) (sq_nonneg _)
      _ = M * t ^ 2 := by rw [sq_abs]; ring
  rw [h1, Complex.norm_real, Real.norm_eq_abs] at h2
  exact h2

/-- Explicit `ζ`-derivative of the kernel. -/
lemma hasDerivAt_kernel {ζ : ℂ} (hζ : ζ ∈ strip) (t : ℝ) :
    HasDerivAt (fun z : ℂ => (uR t : ℂ) / Complex.sin (π * (z - Complex.I * t)))
      (-(uR t : ℂ) * π * Complex.cos (π * (ζ - Complex.I * t)) / Complex.sin (π * (ζ - Complex.I * t)) ^ 2) ζ := by
  have hne := sin_arg_ne_zero t hζ
  have h1 : HasDerivAt (fun z : ℂ => π * (z - Complex.I * t)) (π : ℂ) ζ := by
    simpa using ((hasDerivAt_id ζ).sub_const (Complex.I * t)).const_mul (π : ℂ)
  have h2 : HasDerivAt (fun z : ℂ => Complex.sin (π * (z - Complex.I * t)))
      (Complex.cos (π * (ζ - Complex.I * t)) * π) ζ := h1.csin
  have h3 := (hasDerivAt_const ζ (uR t : ℂ)).div h2 hne
  convert h3 using 1
  ring

lemma hasDerivAt_outerH {ζ : ℂ} (hζ : ζ ∈ strip) :
    HasDerivAt outerH (∫ t : ℝ, -(uR t : ℂ) * π * Complex.cos (π * (ζ - Complex.I * t)) /
      Complex.sin (π * (ζ - Complex.I * t)) ^ 2) ζ := by
  have h := hasDerivAt_outerH_gen hζ
  convert h using 2
  ext t
  exact ((hasDerivAt_kernel hζ t).deriv).symm

lemma hasDerivAt_H0_real {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    HasDerivAt H0 (∫ t : ℝ, -(uR t : ℂ) * π * Complex.cos (π * ((x : ℂ) - Complex.I * t)) /
      Complex.sin (π * ((x : ℂ) - Complex.I * t)) ^ 2) (x : ℂ) := by
  have hs : (x : ℂ) ∈ strip := ⟨by simpa using hx0, by simp; linarith⟩
  have hb : (x : ℂ) ∈ ball (0 : ℂ) (1 / 2) := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hx1
  have hev : outerH =ᶠ[𝓝 (x : ℂ)] H0 := by
    filter_upwards [isOpen_strip.mem_nhds hs, isOpen_ball.mem_nhds hb] with z hz1 hz2 using
      outerH_eq_H0 hz1 hz2
  exact (hasDerivAt_outerH hs).congr_of_eventuallyEq hev.symm

/-- The majorant `π |u_r(t)| cosh(πt)/sinh²(πt)`. -/
noncomputable def derivMajorant (t : ℝ) : ℝ := π * |uR t| * Real.cosh (π * t) / Real.sinh (π * t) ^ 2

lemma derivMajorant_nonneg (t : ℝ) : 0 ≤ derivMajorant t := by
  unfold derivMajorant; positivity

/-- `sinh(πs) ≥ ((1 - e^{-2πm})/2) e^{πs}` for `s ≥ m > 0`. -/
lemma sinh_pi_lower {m s : ℝ} (hs : m ≤ s) :
    (1 - Real.exp (-(2 * π * m))) / 2 * Real.exp (π * s) ≤ Real.sinh (π * s) := by
  set q : ℝ := Real.exp (-(2 * π * m)) with hqdef
  have hexp : Real.exp (-(2 * π * s)) ≤ q := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  set E : ℝ := Real.exp (π * s) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE' : Real.exp (-(π * s)) = E⁻¹ := Real.exp_neg _
  have hsq : Real.exp (-(2 * π * s)) = E⁻¹ ^ 2 := by
    rw [← hE', ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [Real.sinh_eq, hE']
  have h1 : E⁻¹ ≤ q * E := by
    have : E⁻¹ ^ 2 ≤ q := hsq ▸ hexp
    have e : E⁻¹ = E⁻¹ ^ 2 * E := by field_simp
    calc E⁻¹ = E⁻¹ ^ 2 * E := e
      _ ≤ q * E := mul_le_mul_of_nonneg_right this hEpos.le
  nlinarith

lemma integrable_derivMajorant : Integrable derivMajorant := by
  obtain ⟨C, hC⟩ := uR_sq_bound
  have hpi := Real.pi_pos
  set q : ℝ := Real.exp (-(2 * π * (1 / 2))) with hqdef
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hqpos : 0 < 1 - q := by linarith
  set K : ℝ := 4 / (1 - q) ^ 2 with hK
  have hKpos : 0 < K := by positivity
  have hC0 : 0 ≤ C := by
    have h1 := hC (1 / 4) (by norm_num [abs_of_pos])
    have h2 : 0 ≤ |uR (1 / 4)| := abs_nonneg _
    nlinarith
  set M₀ : ℝ := C * Real.cosh (π / 2) / π with hM₀
  have hM₀0 : 0 ≤ M₀ := by have := Real.cosh_pos (π / 2); positivity
  have hint := (integrable_log_weight (C := 2 * C0 + M₀ / (π * K)) (by
      have := C0_nonneg; positivity)).const_mul (π * K * Real.exp (π / 2))
  refine Integrable.mono' hint ?_ (Eventually.of_forall fun t => ?_)
  · have hc : Continuous fun t : ℝ => π * |uR t| * Real.cosh (π * t) := by
      have := continuous_uR; fun_prop
    have hd : Continuous fun t : ℝ => Real.sinh (π * t) ^ 2 := by fun_prop
    exact (hc.measurable.div hd.measurable).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (derivMajorant_nonneg t)]
    unfold derivMajorant
    have hlog0 : 0 ≤ Real.log (1 + t ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg t])
    have hC0' := C0_nonneg
    have hB : 0 ≤ (Real.log (1 + t ^ 2) + (2 * C0 + M₀ / (π * K))) * Real.exp (-(π * |t|)) := by positivity
    by_cases ht : t = 0
    · subst ht
      simp only [uR_zero, abs_zero, mul_zero, zero_mul, zero_div]
      positivity
    have hsh : Real.sinh (π * t) ≠ 0 := Real.sinh_eq_zero.not.mpr (mul_ne_zero hpi.ne' ht)
    have hsq : Real.sinh (π * t) ^ 2 = Real.sinh (π * |t|) ^ 2 := by
      rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
      · rw [h, mul_neg, Real.sinh_neg, neg_sq]
    have hcos : Real.cosh (π * t) = Real.cosh (π * |t|) := by
      rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
      · rw [h, mul_neg, Real.cosh_neg]
    rw [hsq, hcos]
    rcases le_or_gt |t| (1 / 2) with hle | hgt
    · have hsinh : π * |t| ≤ Real.sinh (π * |t|) := Real.self_le_sinh_iff.mpr (by positivity)
      have hcosh : Real.cosh (π * |t|) ≤ Real.cosh (π / 2) := by
        apply Real.cosh_le_cosh.mpr
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ π * |t|), abs_of_pos (by positivity : (0 : ℝ) < π / 2)]
        nlinarith
      have hu : |uR t| ≤ C * t ^ 2 := hC t hle
      have hpos : 0 < |t| := abs_pos.mpr ht
      have hnear : π * |uR t| * Real.cosh (π * |t|) / Real.sinh (π * |t|) ^ 2 ≤ M₀ := by
        rw [div_le_iff₀ (by positivity)]
        have hcp : 0 < Real.cosh (π * |t|) := Real.cosh_pos _
        calc π * |uR t| * Real.cosh (π * |t|) ≤ π * (C * t ^ 2) * Real.cosh (π / 2) := by gcongr
          _ = (C * Real.cosh (π / 2) / π) * (π * |t|) ^ 2 := by
              rw [mul_pow, sq_abs]; field_simp
          _ ≤ M₀ * Real.sinh (π * |t|) ^ 2 := by gcongr
      have hexp1 : 1 ≤ Real.exp (π / 2) * Real.exp (-(π * |t|)) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
      have hE0 : 0 < Real.exp (π / 2) := Real.exp_pos _
      have hdrop : π * K * Real.exp (π / 2) * ((M₀ / (π * K)) * Real.exp (-(π * |t|))) ≤
          π * K * Real.exp (π / 2) * ((Real.log (1 + t ^ 2) + (2 * C0 + M₀ / (π * K))) * Real.exp (-(π * |t|))) := by
        gcongr
        linarith
      have e1 : π * K * Real.exp (π / 2) * ((M₀ / (π * K)) * Real.exp (-(π * |t|))) =
          M₀ * (Real.exp (π / 2) * Real.exp (-(π * |t|))) := by
        field_simp
      have : M₀ ≤ M₀ * (Real.exp (π / 2) * Real.exp (-(π * |t|))) := by nlinarith
      linarith
    · set E : ℝ := Real.exp (π * |t|) with hE
      have hEpos : 0 < E := Real.exp_pos _
      have hsl := sinh_pi_lower (m := 1 / 2) (s := |t|) hgt.le
      rw [← hqdef, ← hE] at hsl
      have hcosh : Real.cosh (π * |t|) ≤ E := by
        rw [Real.cosh_eq]
        have : Real.exp (-(π * |t|)) ≤ E := by
          rw [hE]; exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg t])
        linarith
      have hE' : Real.exp (-(π * |t|)) = E⁻¹ := Real.exp_neg _
      have hs2 : ((1 - q) / 2 * E) ^ 2 ≤ Real.sinh (π * |t|) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hsl 2
      have hu : |uR t| ≤ Real.log (1 + t ^ 2) + 2 * C0 := abs_uR_le' t
      have hcp : 0 < Real.cosh (π * |t|) := Real.cosh_pos _
      have hfar : π * |uR t| * Real.cosh (π * |t|) / Real.sinh (π * |t|) ^ 2 ≤
          π * K * ((Real.log (1 + t ^ 2) + 2 * C0) * Real.exp (-(π * |t|))) := by
        rw [div_le_iff₀ (by positivity)]
        have h3 : π * |uR t| * Real.cosh (π * |t|) ≤ π * (Real.log (1 + t ^ 2) + 2 * C0) * E := by gcongr
        calc π * |uR t| * Real.cosh (π * |t|) ≤ π * (Real.log (1 + t ^ 2) + 2 * C0) * E := h3
          _ = π * K * ((Real.log (1 + t ^ 2) + 2 * C0) * Real.exp (-(π * |t|))) * ((1 - q) / 2 * E) ^ 2 := by
              rw [hE', hK]; field_simp; ring
          _ ≤ π * K * ((Real.log (1 + t ^ 2) + 2 * C0) * Real.exp (-(π * |t|))) * Real.sinh (π * |t|) ^ 2 := by
              gcongr
      have hdrop : π * K * ((Real.log (1 + t ^ 2) + 2 * C0) * Real.exp (-(π * |t|))) ≤
          π * K * Real.exp (π / 2) * ((Real.log (1 + t ^ 2) + (2 * C0 + M₀ / (π * K))) * Real.exp (-(π * |t|))) := by
        have he1 : 1 ≤ Real.exp (π / 2) := Real.one_le_exp (by positivity)
        have hexn : 0 ≤ Real.exp (-(π * |t|)) := (Real.exp_pos _).le
        have hmm : 0 ≤ M₀ / (π * K) := by positivity
        have : (Real.log (1 + t ^ 2) + 2 * C0) * Real.exp (-(π * |t|)) ≤
            Real.exp (π / 2) * ((Real.log (1 + t ^ 2) + (2 * C0 + M₀ / (π * K))) * Real.exp (-(π * |t|))) := by
          have : (Real.log (1 + t ^ 2) + 2 * C0) ≤ Real.exp (π / 2) * (Real.log (1 + t ^ 2) + (2 * C0 + M₀ / (π * K))) := by
            nlinarith
          nlinarith
        calc _ ≤ π * K * (Real.exp (π / 2) * ((Real.log (1 + t ^ 2) + (2 * C0 + M₀ / (π * K))) * Real.exp (-(π * |t|)))) := by
              gcongr
          _ = _ := by ring
      linarith

/-- The integrand of the derivative of `h` at `ζ = x ∈ (0,1)`. -/
noncomputable def derivIntegrand (x t : ℝ) : ℂ :=
  -(uR t : ℂ) * π * Complex.cos (π * ((x : ℂ) - Complex.I * t)) /
    Complex.sin (π * ((x : ℂ) - Complex.I * t)) ^ 2

lemma norm_derivIntegrand_le {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (t : ℝ) :
    ‖derivIntegrand x t‖ ≤ derivMajorant t := by
  by_cases ht : t = 0
  · subst ht; simp [derivIntegrand, uR_zero, derivMajorant]
  have hxs : (x : ℂ) ∈ strip := ⟨by simpa using hx0, by simpa using hx1⟩
  have hsh : Real.sinh (π * t) ≠ 0 := Real.sinh_eq_zero.not.mpr (mul_ne_zero Real.pi_pos.ne' ht)
  have hs1 := norm_sin_arg_sq (x : ℂ) t
  have hc1 := norm_cos_sq (↑π * ((x : ℂ) - Complex.I * t))
  rw [re_arg, im_arg] at hc1
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_sub, mul_neg, Real.sinh_neg, neg_sq] at hs1 hc1
  have hsin2 : Real.sinh (π * t) ^ 2 ≤ ‖Complex.sin (π * ((x : ℂ) - Complex.I * t))‖ ^ 2 := by
    rw [hs1]; nlinarith [sq_nonneg (Real.sin (π * x))]
  have hcos : ‖Complex.cos (π * ((x : ℂ) - Complex.I * t))‖ ≤ Real.cosh (π * t) := by
    have : ‖Complex.cos (π * ((x : ℂ) - Complex.I * t))‖ ^ 2 ≤ Real.cosh (π * t) ^ 2 := by
      rw [hc1, Real.cosh_sq]; nlinarith [Real.cos_sq_le_one (π * x)]
    exact abs_le_of_sq_le_sq' this (Real.cosh_pos _).le |>.2
  have hpos : 0 < Real.sinh (π * t) ^ 2 := by positivity
  unfold derivIntegrand derivMajorant
  rw [norm_div, norm_pow, norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [div_le_div_iff₀ (lt_of_lt_of_le hpos hsin2) hpos]
  have h1 : |uR t| * π * ‖Complex.cos (π * ((x : ℂ) - Complex.I * t))‖ ≤ π * |uR t| * Real.cosh (π * t) := by
    calc |uR t| * π * ‖Complex.cos (π * ((x : ℂ) - Complex.I * t))‖ =
          π * |uR t| * ‖Complex.cos (π * ((x : ℂ) - Complex.I * t))‖ := by ring
      _ ≤ π * |uR t| * Real.cosh (π * t) := mul_le_mul_of_nonneg_left hcos (by positivity)
  calc |uR t| * π * ‖Complex.cos (π * ((x : ℂ) - Complex.I * t))‖ * Real.sinh (π * t) ^ 2
      ≤ π * |uR t| * Real.cosh (π * t) * Real.sinh (π * t) ^ 2 := by gcongr
    _ ≤ π * |uR t| * Real.cosh (π * t) * ‖Complex.sin (π * ((x : ℂ) - Complex.I * t))‖ ^ 2 := by
        gcongr

lemma continuous_derivIntegrand {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Continuous (derivIntegrand x) := by
  have hxs : (x : ℂ) ∈ strip := ⟨by simpa using hx0, by simpa using hx1⟩
  unfold derivIntegrand
  have := continuous_uR
  refine Continuous.div (by fun_prop) (by fun_prop) (fun t => ?_)
  exact pow_ne_zero 2 (sin_arg_ne_zero t hxs)

/-- The value at `x = 0`. -/
lemma derivIntegrand_zero {t : ℝ} (ht : t ≠ 0) :
    derivIntegrand 0 t = ((uR t * (π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2) : ℝ) : ℂ) := by
  have hsh : Real.sinh (π * t) ≠ 0 := Real.sinh_eq_zero.not.mpr (mul_ne_zero Real.pi_pos.ne' ht)
  have hshC : (Real.sinh (π * t) : ℂ) ≠ 0 := by exact_mod_cast hsh
  have e : (π : ℂ) * (((0 : ℝ) : ℂ) - Complex.I * t) = ((-(π * t) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  unfold derivIntegrand
  rw [e, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Real.cosh_neg,
    Real.sinh_neg]
  push_cast
  field_simp
  simp [Complex.I_sq]
  ring

lemma tendsto_derivIntegral :
    Tendsto (fun x : ℝ => ∫ t : ℝ, derivIntegrand x t) (𝓝[>] 0)
      (𝓝 (∫ t : ℝ, ((uR t * (π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2) : ℝ) : ℂ))) := by
  refine tendsto_integral_filter_of_dominated_convergence derivMajorant ?_ ?_ integrable_derivMajorant ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact (continuous_derivIntegrand hx.1 hx.2).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact Eventually.of_forall fun t => norm_derivIntegrand_le hx.1 hx.2 t
  · have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
      simpa using (Set.countable_singleton (0 : ℝ)).ae_notMem volume
    filter_upwards [hne] with t ht
    have hsh : Real.sinh (π * t) ≠ 0 := Real.sinh_eq_zero.not.mpr (mul_ne_zero Real.pi_pos.ne' ht)
    have hden : Complex.sin (π * (((0 : ℝ) : ℂ) - Complex.I * t)) ≠ 0 := by
      intro h
      have h1 := norm_sin_arg_sq (((0 : ℝ) : ℂ)) t
      rw [h, norm_zero] at h1
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_sub, mul_neg, Real.sinh_neg, neg_sq, mul_zero,
        Real.sin_zero] at h1
      have : Real.sinh (π * t) ^ 2 = 0 := by linarith
      exact hsh (pow_eq_zero_iff (two_ne_zero) |>.mp this)
    have hc : ContinuousAt (fun x : ℝ => derivIntegrand x t) 0 := by
      unfold derivIntegrand
      refine ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hden)
    have := hc.tendsto
    rw [derivIntegrand_zero ht] at this
    exact this.mono_left nhdsWithin_le_nhds |>.congr' (by filter_upwards with x; rfl)

/-- **`ct:outer` (2): `H₀'(0) = h'(0) = ∫_ℝ u_r(t) π cosh(πt)/sinh²(πt) dt`.** -/
theorem deriv_H0_zero :
    deriv H0 0 = ∫ t : ℝ, ((uR t * (π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2) : ℝ) : ℂ) := by
  have hcont : ContinuousAt (deriv H0) 0 :=
    (differentiableOn_H0.deriv isOpen_ball).continuousOn.continuousAt
      (isOpen_ball.mem_nhds (mem_ball_self (by norm_num)))
  have h2 : Tendsto (fun x : ℝ => deriv H0 (x : ℂ)) (𝓝[>] 0) (𝓝 (deriv H0 0)) := by
    have := hcont.tendsto.comp (Complex.continuous_ofReal.tendsto 0)
    exact (this.mono_left nhdsWithin_le_nhds)
  have h3 : ∀ᶠ x : ℝ in 𝓝[>] 0, deriv H0 (x : ℂ) = ∫ t : ℝ, derivIntegrand x t := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with x hx
    exact (hasDerivAt_H0_real hx.1 hx.2).deriv
  exact tendsto_nhds_unique (h2.congr' h3) tendsto_derivIntegral

end FormalResearch.SignUncertainty.CtOuter
