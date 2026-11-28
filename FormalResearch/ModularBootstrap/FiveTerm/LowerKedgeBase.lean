module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerDualIdLeft
public import FormalResearch.ModularBootstrap.FiveTerm.LowerChartMain
public import FormalResearch.ModularBootstrap.FiveTerm.LowerVirasoroPsi
public import FormalResearch.SignUncertainty.CtChartTaylor
public import FormalResearch.SignUncertainty.CtChartIft
public import FormalResearch.SignUncertainty.CtChartGerm
public import FormalResearch.SignUncertainty.CtCfuEven

/-!
# Complexified Edge Frequency, Slit Map, and Virasoro Germ Data (`LowerKedgeBase`)

Base holomorphic infrastructure near `0` for the Virasoro CFU construction (`cts:cauchy-dual` Step 4):

* `virEdgeFC z`, `virEdgeFC' z`, `yVirC v`: complexified edge frequency `F(z)`, derivative `F'(z)`,
  and slit map `y(F(v)) = sinh(πv) / ((1 + cosh(πv)²)^{1/2} + √2)` on `{|z.im| < 1/2}`.
* `virPhi0C v`, `virPhiDualC v x'`: complexified dual edge phase agreeing with `phiDual v x'` on `ℝ`.
* `virF1`: even factorization `virEdgeFC z - xiStar = z² virF1(z²)` near `0`.
* `virNC`, `virNtC`, `virPC`, `virFC`, `virDC`, `virAC`, `virLC`, `virXPrimeOfBeta`: Virasoro
  polynomial-germ data and the exact derivative relation `deriv virPC β = (virNC β - virNtC β) / 2`.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Saddle
open FormalResearch.SignUncertainty.CtChart
open FormalResearch.SignUncertainty.CtCfu

noncomputable section

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### 1. Complexified `virEdgeFC`, `yVirC`, and `virPhiDualC` on `{|z.im| < 1/2}` -/

/-- Complexified edge frequency `F(z) = π⁻¹ log(cosh(πz) + (1 + cosh(πz)²)^{1/2})`. -/
def virEdgeFC (z : ℂ) : ℂ :=
  Complex.log (Complex.cosh ((π : ℂ) * z) +
    (1 + Complex.cosh ((π : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)) / (π : ℂ)

/-- Complexified first derivative `F'(z) = sinh(πz) / (1 + cosh(πz)²)^{1/2}`. -/
def virEdgeFC' (z : ℂ) : ℂ :=
  Complex.sinh ((π : ℂ) * z) / (1 + Complex.cosh ((π : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)

/-- Complexified slit coordinate `y(F(v)) = sinh(πv) / ((1 + cosh(πv)²)^{1/2} + √2)` (odd across `0`). -/
def yVirC (v : ℂ) : ℂ :=
  Complex.sinh ((π : ℂ) * v) /
    ((1 + Complex.cosh ((π : ℂ) * v) ^ 2) ^ (1 / 2 : ℂ) + ((√2 : ℝ) : ℂ))

/-- Odd base phase `φ₀(v) = (4π/3) ∫₀¹ (F(t v) - ξ_*) v dt`. -/
def virPhi0C (v : ℂ) : ℂ :=
  ((4 * π / 3 : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1, (virEdgeFC ((t : ℂ) * v) - (xiStar : ℂ)) * v

/-- Complexified dual edge phase `φ(v; x') = φ₀(v) - (4π/3)(x' - ξ_*) v`. -/
def virPhiDualC (v x' : ℂ) : ℂ :=
  virPhi0C v - ((4 * π / 3 : ℝ) : ℂ) * (x' - (xiStar : ℂ)) * v

lemma isOpen_virStrip : IsOpen {z : ℂ | |z.im| < 1 / 2} :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

lemma cosh_pi_re_pos {z : ℂ} (hz : |z.im| < 1 / 2) :
    0 < (Complex.cosh ((π : ℂ) * z)).re := by
  have hre : (Complex.cosh ((π : ℂ) * z)).re = Real.cosh (π * z.re) * Real.cos (π * z.im) := by
    have hmul : (π : ℂ) * z = ((π * z.re : ℝ) : ℂ) + ((π * z.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hmul, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  rw [hre]
  have hcos : 0 < Real.cos (π * z.im) := by
    apply Real.cos_pos_of_mem_Ioo
    rw [abs_lt] at hz
    have := Real.pi_pos
    exact ⟨by nlinarith, by nlinarith⟩
  exact mul_pos (Real.cosh_pos _) hcos

lemma one_add_cosh_pi_sq_slit {z : ℂ} (hz : |z.im| < 1 / 2) :
    1 + Complex.cosh ((π : ℂ) * z) ^ 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (1 + Complex.cosh ((π : ℂ) * z) ^ 2).im = 0
  · left
    have him_eq : (1 + Complex.cosh ((π : ℂ) * z) ^ 2).im =
        2 * (Complex.cosh ((π : ℂ) * z)).re * (Complex.cosh ((π : ℂ) * z)).im := by
      rw [Complex.add_im, Complex.one_im, zero_add, sq, Complex.mul_im]; ring
    rw [him_eq] at him
    have hre_pos : 0 < (Complex.cosh ((π : ℂ) * z)).re := cosh_pi_re_pos hz
    have him_zero : (Complex.cosh ((π : ℂ) * z)).im = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · linarith
      · exact h
    have hsq_re : (1 + Complex.cosh ((π : ℂ) * z) ^ 2).re =
        1 + (Complex.cosh ((π : ℂ) * z)).re ^ 2 - (Complex.cosh ((π : ℂ) * z)).im ^ 2 := by
      rw [Complex.add_re, Complex.one_re, sq, Complex.mul_re]; ring
    rw [hsq_re, him_zero]
    nlinarith [sq_nonneg (Complex.cosh ((π : ℂ) * z)).re]
  · right; exact him

lemma sqrt_one_add_cosh_re_pos {z : ℂ} (hz : |z.im| < 1 / 2) :
    0 < ((1 + Complex.cosh ((π : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)).re := by
  set w : ℂ := 1 + Complex.cosh ((π : ℂ) * z) ^ 2
  have hw : w ∈ Complex.slitPlane := one_add_cosh_pi_sq_slit hz
  have hw_ne : w ≠ 0 := Complex.slitPlane_ne_zero hw
  have harg_ne : w.arg ≠ π := (Complex.mem_slitPlane_iff_arg.mp hw).1
  have harg_lt : w.arg < π := lt_of_le_of_ne (Complex.arg_le_pi w) harg_ne
  have harg_gt : -π < w.arg := Complex.neg_pi_lt_arg w
  have hpow : w ^ (1 / 2 : ℂ) =
      (((‖w‖ ^ (1 / 2 : ℝ) : ℝ)) : ℂ) * Complex.exp (((w.arg / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero hw_ne, Complex.log, add_mul, Complex.exp_add]
    congr 1
    · rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hw_ne), Complex.ofReal_exp]
      congr 1; push_cast; ring
    · congr 1; push_cast; ring
  rw [hpow, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hw_ne) _)
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)

private lemma log_arg_slit_strip {z : ℂ} (hz : |z.im| < 1 / 2) :
    Complex.cosh ((π : ℂ) * z) + (1 + Complex.cosh ((π : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ) ∈
      Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  rw [Complex.add_re]
  exact add_pos (cosh_pi_re_pos hz) (sqrt_one_add_cosh_re_pos hz)

lemma hasDerivAt_virEdgeFC {z : ℂ} (hz : |z.im| < 1 / 2) :
    HasDerivAt virEdgeFC (virEdgeFC' z) z := by
  have hlin : HasDerivAt (fun w : ℂ => (π : ℂ) * w) (π : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (π : ℂ)
  have hch : HasDerivAt (fun w : ℂ => Complex.cosh ((π : ℂ) * w))
      (Complex.sinh ((π : ℂ) * z) * (π : ℂ)) z :=
    (Complex.hasDerivAt_cosh ((π : ℂ) * z)).comp z hlin
  have hsq : HasDerivAt (fun w : ℂ => 1 + Complex.cosh ((π : ℂ) * w) ^ 2)
      (2 * Complex.cosh ((π : ℂ) * z) * (Complex.sinh ((π : ℂ) * z) * (π : ℂ))) z := by
    have h1 := ((hch.pow 2).const_add 1)
    refine h1.congr_deriv ?_; ring
  have hslit := one_add_cosh_pi_sq_slit hz
  have hsqrt : HasDerivAt (fun w : ℂ => (1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (1 + Complex.cosh ((π : ℂ) * z) ^ 2) ^ ((1 / 2 : ℂ) - 1) *
        (2 * Complex.cosh ((π : ℂ) * z) * Complex.sinh ((π : ℂ) * z) * (π : ℂ))) z := by
    have h1 := (hsq.cpow_const hslit (c := (1 / 2 : ℂ)))
    refine h1.congr_deriv ?_; ring
  set S : ℂ := (1 + Complex.cosh ((π : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)
  have hS_ne : S ≠ 0 := by
    have hre := sqrt_one_add_cosh_re_pos hz
    intro h0
    have h0' : (0 : ℂ).re = S.re := congrArg Complex.re h0.symm
    rw [Complex.zero_re] at h0'
    exact lt_irrefl (0 : ℝ) (by linarith only [hre, h0'])
  have hS_sq : S ^ 2 = 1 + Complex.cosh ((π : ℂ) * z) ^ 2 := by
    dsimp [S]
    rw [sq, ← Complex.cpow_add _ _ (Complex.slitPlane_ne_zero hslit)]
    norm_num
  have hpow_neg : (1 + Complex.cosh ((π : ℂ) * z) ^ 2) ^ ((1 / 2 : ℂ) - 1) = S⁻¹ := by
    rw [Complex.cpow_sub _ _ (Complex.slitPlane_ne_zero hslit), Complex.cpow_one]
    change S / (1 + Complex.cosh ((π : ℂ) * z) ^ 2) = S⁻¹
    rw [← hS_sq, sq]
    field_simp [hS_ne]
  have hsum := hch.add hsqrt
  have hlog := (Complex.hasDerivAt_log (log_arg_slit_strip hz)).comp z hsum
  have hdiv := hlog.div_const (π : ℂ)
  refine hdiv.congr_deriv ?_
  unfold virEdgeFC'
  have hA_ne : Complex.cosh ((π : ℂ) * z) + S ≠ 0 :=
    Complex.slitPlane_ne_zero (log_arg_slit_strip hz)
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  rw [show (Complex.cosh ((π : ℂ) * z) + (1 + Complex.cosh ((π : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)) =
      Complex.cosh ((π : ℂ) * z) + S from rfl]
  rw [hpow_neg]
  change (Complex.cosh ((π : ℂ) * z) + S)⁻¹ *
      (Complex.sinh ((π : ℂ) * z) * (π : ℂ) +
        (1 / 2 : ℂ) * S⁻¹ * (2 * Complex.cosh ((π : ℂ) * z) * Complex.sinh ((π : ℂ) * z) * (π : ℂ))) / (π : ℂ) =
      Complex.sinh ((π : ℂ) * z) / S
  field_simp [hS_ne, hA_ne, hpi]
  ring

lemma differentiableOn_virEdgeFC : DifferentiableOn ℂ virEdgeFC {z : ℂ | |z.im| < 1 / 2} :=
  fun _ hz => (hasDerivAt_virEdgeFC hz).differentiableAt.differentiableWithinAt

lemma analyticOnNhd_virEdgeFC : AnalyticOnNhd ℂ virEdgeFC {z : ℂ | |z.im| < 1 / 2} :=
  differentiableOn_virEdgeFC.analyticOnNhd isOpen_virStrip

lemma differentiableOn_virEdgeFC' : DifferentiableOn ℂ virEdgeFC' {z : ℂ | |z.im| < 1 / 2} := by
  intro z hz
  have hlin : DifferentiableAt ℂ (fun w : ℂ => (π : ℂ) * w) z := by fun_prop
  have hch : DifferentiableAt ℂ (fun w : ℂ => Complex.cosh ((π : ℂ) * w)) z :=
    (Complex.differentiable_cosh _).comp z hlin
  have hsh : DifferentiableAt ℂ (fun w : ℂ => Complex.sinh ((π : ℂ) * w)) z :=
    (Complex.differentiable_sinh _).comp z hlin
  have hsqrt : DifferentiableAt ℂ (fun w : ℂ => (1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)) z :=
    ((differentiableAt_const _).add (hch.pow 2)).cpow_const (one_add_cosh_pi_sq_slit hz)
  have hne : (1 + Complex.cosh ((π : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
    have hre := sqrt_one_add_cosh_re_pos hz
    intro h0; rw [h0, Complex.zero_re] at hre; exact lt_irrefl _ hre
  exact (hsh.div hsqrt hne).differentiableWithinAt

lemma analyticOnNhd_virEdgeFC' : AnalyticOnNhd ℂ virEdgeFC' {z : ℂ | |z.im| < 1 / 2} :=
  differentiableOn_virEdgeFC'.analyticOnNhd isOpen_virStrip

lemma virEdgeFC_neg (z : ℂ) : virEdgeFC (-z) = virEdgeFC z := by
  unfold virEdgeFC; rw [mul_neg, Complex.cosh_neg]

lemma virEdgeFC_conj {z : ℂ} (hz : |z.im| < 1 / 2) :
    virEdgeFC (starRingEnd ℂ z) = starRingEnd ℂ (virEdgeFC z) := by
  have harg := log_arg_slit_strip hz
  have hsq := one_add_cosh_pi_sq_slit hz
  have hc_arg : Complex.cosh ((π : ℂ) * starRingEnd ℂ z) = starRingEnd ℂ (Complex.cosh ((π : ℂ) * z)) := by
    rw [show (π : ℂ) * starRingEnd ℂ z = starRingEnd ℂ ((π : ℂ) * z) by simp, Complex.cosh_conj]
  have h1c : 1 + Complex.cosh ((π : ℂ) * starRingEnd ℂ z) ^ 2 =
      starRingEnd ℂ (1 + Complex.cosh ((π : ℂ) * z) ^ 2) := by
    rw [hc_arg]; simp
  have hs_c : (1 + Complex.cosh ((π : ℂ) * starRingEnd ℂ z) ^ 2) ^ (1 / 2 : ℂ) =
      starRingEnd ℂ ((1 + Complex.cosh ((π : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)) := by
    have hc := Complex.cpow_conj (1 + Complex.cosh ((π : ℂ) * z) ^ 2) (1 / 2 : ℂ)
      (Complex.mem_slitPlane_iff_arg.mp hsq).1
    have h12 : starRingEnd ℂ (1 / 2 : ℂ) = (1 / 2 : ℂ) := by rw [map_div₀, map_one, map_ofNat]
    rw [h12] at hc
    rw [h1c, hc, Complex.conj_conj]
  unfold virEdgeFC
  rw [map_div₀, Complex.conj_ofReal]
  congr 1
  rw [hc_arg]
  have h1c' : 1 + (starRingEnd ℂ (Complex.cosh ((π : ℂ) * z))) ^ 2 =
      1 + Complex.cosh ((π : ℂ) * starRingEnd ℂ z) ^ 2 := by rw [hc_arg]
  rw [h1c', hs_c, ← map_add, Complex.log_conj _ (Complex.mem_slitPlane_iff_arg.mp harg).1]

lemma virEdgeFC_ofReal (v : ℝ) : virEdgeFC (v : ℂ) = (edgeF v : ℂ) := by
  unfold virEdgeFC edgeF Real.arsinh
  have hch : Complex.cosh ((π : ℂ) * (v : ℂ)) = ((Real.cosh (π * v) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]
  have h1 : 1 + ((Real.cosh (π * v) : ℝ) : ℂ) ^ 2 = ((1 + Real.cosh (π * v) ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  have hpos1 : 0 ≤ 1 + Real.cosh (π * v) ^ 2 := by positivity
  have hsqrt : ((1 + Real.cosh (π * v) ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((√(1 + Real.cosh (π * v) ^ 2) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hpos1,
      ← Real.sqrt_eq_rpow]
  have hpos_sum : 0 < Real.cosh (π * v) + √(1 + Real.cosh (π * v) ^ 2) := by positivity
  rw [hch, h1, hsqrt, ← Complex.ofReal_add, ← Complex.ofReal_log hpos_sum.le]
  push_cast; rfl

lemma virEdgeFC'_ofReal (v : ℝ) : virEdgeFC' (v : ℂ) = (edgeF' v : ℂ) := by
  unfold virEdgeFC' edgeF'
  have hsh : Complex.sinh ((π : ℂ) * (v : ℂ)) = ((Real.sinh (π * v) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh]
  have hch : 1 + Complex.cosh ((π : ℂ) * (v : ℂ)) ^ 2 = ((1 + Real.cosh (π * v) ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]; push_cast; ring
  have hsqrt : ((1 + Real.cosh (π * v) ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((√(1 + Real.cosh (π * v) ^ 2) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow]
  rw [hsh, hch, hsqrt]; push_cast; rfl

lemma virEdgeFC_zero : virEdgeFC 0 = (xiStar : ℂ) := by
  simpa [edgeF_zero] using virEdgeFC_ofReal 0

lemma virEdgeFC'_zero : virEdgeFC' 0 = 0 := by simp [virEdgeFC']

lemma deriv_virEdgeFC_eq {z : ℂ} (hz : |z.im| < 1 / 2) : deriv virEdgeFC z = virEdgeFC' z :=
  (hasDerivAt_virEdgeFC hz).deriv

lemma deriv_virEdgeFC_zero : deriv virEdgeFC 0 = 0 := by
  rw [deriv_virEdgeFC_eq (by simp)]; exact virEdgeFC'_zero

lemma virEdgeFC''_ofReal (v : ℝ) :
    deriv (deriv virEdgeFC) (v : ℂ) = ((edgeF'' v : ℝ) : ℂ) := by
  have hv_mem : (v : ℂ) ∈ {z : ℂ | |z.im| < 1 / 2} := by simp
  have hd : DifferentiableOn ℂ (deriv virEdgeFC) {z : ℂ | |z.im| < 1 / 2} := by
    intro z hz
    have hdiff := (analyticOnNhd_virEdgeFC' z hz).differentiableAt
    exact (hdiff.congr_of_eventuallyEq (by
      filter_upwards [isOpen_virStrip.mem_nhds hz] with w hw using deriv_virEdgeFC_eq hw)).differentiableWithinAt
  have hd_at : HasDerivAt (deriv virEdgeFC) (deriv (deriv virEdgeFC) (v : ℂ)) (v : ℂ) :=
    (hd.differentiableAt (isOpen_virStrip.mem_nhds hv_mem)).hasDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => deriv virEdgeFC (t : ℂ)) (deriv (deriv virEdgeFC) (v : ℂ)) v :=
    hd_at.comp_ofReal
  have heq : (fun t : ℝ => deriv virEdgeFC (t : ℂ)) = fun t : ℝ => (edgeF' t : ℂ) := by
    ext t; rw [deriv_virEdgeFC_eq (by simp)]; exact virEdgeFC'_ofReal t
  rw [heq] at hcomp
  exact hcomp.unique (hasDerivAt_edgeF' v).ofReal_comp

lemma virEdgeFC''_zero : deriv (deriv virEdgeFC) 0 = ((π / √2 : ℝ) : ℂ) := by
  have h1 := virEdgeFC''_ofReal 0
  simp only [Complex.ofReal_zero] at h1
  rw [h1]
  congr 1
  unfold edgeF''
  rw [mul_zero, Real.cosh_zero, one_pow]
  have hpow : (1 + 1 : ℝ) ^ (3 / 2 : ℝ) = 2 * √2 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
      Real.rpow_one, ← Real.sqrt_eq_rpow]; ring
  rw [hpow]
  have h2ne : √2 ≠ 0 := by positivity
  field_simp [h2ne]

lemma virEdgeFC''_conj {z : ℂ} (hz : |z.im| < 1 / 2) :
    deriv (deriv virEdgeFC) (starRingEnd ℂ z) = starRingEnd ℂ (deriv (deriv virEdgeFC) z) := by
  have h1 : ∀ w, |w.im| < 1 / 2 →
      deriv virEdgeFC (starRingEnd ℂ w) = starRingEnd ℂ (deriv virEdgeFC w) := fun w hw => by
    have hd : HasDerivAt virEdgeFC (deriv virEdgeFC w) w :=
      (analyticOnNhd_virEdgeFC w hw).differentiableAt.hasDerivAt
    have hev : (fun u => starRingEnd ℂ (virEdgeFC (starRingEnd ℂ u))) =ᶠ[𝓝 (starRingEnd ℂ w)] virEdgeFC := by
      have hmem : starRingEnd ℂ w ∈ {z : ℂ | |z.im| < 1 / 2} := by simpa [Complex.conj_im] using hw
      filter_upwards [isOpen_virStrip.mem_nhds hmem] with u hu
      have hu' : |(starRingEnd ℂ u).im| < 1 / 2 := by simpa [Complex.conj_im] using hu
      have hcc := virEdgeFC_conj hu'
      rw [Complex.conj_conj] at hcc
      rw [hcc]
    rw [← (Filter.EventuallyEq.deriv_eq hev)]
    exact (hasDerivAt_conj_conj hd).deriv
  have hd2 : HasDerivAt (deriv virEdgeFC) (deriv (deriv virEdgeFC) z) z := by
    have hdiff' := (analyticOnNhd_virEdgeFC' z hz).differentiableAt
    exact (hdiff'.congr_of_eventuallyEq (by
      filter_upwards [isOpen_virStrip.mem_nhds hz] with w hw using deriv_virEdgeFC_eq hw)).hasDerivAt
  have hev2 : (fun u => starRingEnd ℂ (deriv virEdgeFC (starRingEnd ℂ u))) =ᶠ[𝓝 (starRingEnd ℂ z)]
      deriv virEdgeFC := by
    have hmem : starRingEnd ℂ z ∈ {z : ℂ | |z.im| < 1 / 2} := by simpa [Complex.conj_im] using hz
    filter_upwards [isOpen_virStrip.mem_nhds hmem] with u hu
    have hu' : |(starRingEnd ℂ u).im| < 1 / 2 := by simpa [Complex.conj_im] using hu
    have hcc := h1 (starRingEnd ℂ u) hu'
    rw [Complex.conj_conj] at hcc
    rw [hcc]
  rw [← (Filter.EventuallyEq.deriv_eq hev2)]
  exact (hasDerivAt_conj_conj hd2).deriv

lemma virEdgeFC''_neg {z : ℂ} (hz : |z.im| < 1 / 2) :
    deriv (deriv virEdgeFC) (-z) = deriv (deriv virEdgeFC) z := by
  have hm : |(-z).im| < 1 / 2 := by simpa using hz
  have hd1 : ∀ w, |w.im| < 1 / 2 → deriv virEdgeFC (-w) = -deriv virEdgeFC w := fun w hw => by
    have hm_w : |(-w).im| < 1 / 2 := by simpa using hw
    rw [deriv_virEdgeFC_eq hm_w, deriv_virEdgeFC_eq hw]
    unfold virEdgeFC'
    rw [mul_neg, Complex.sinh_neg, Complex.cosh_neg]
    ring
  have hd2 : HasDerivAt (deriv virEdgeFC) (deriv (deriv virEdgeFC) z) z := by
    have hdiff' := (analyticOnNhd_virEdgeFC' z hz).differentiableAt
    exact (hdiff'.congr_of_eventuallyEq (by
      filter_upwards [isOpen_virStrip.mem_nhds hz] with w hw using deriv_virEdgeFC_eq hw)).hasDerivAt
  have hev : (fun u => -deriv virEdgeFC (-u)) =ᶠ[𝓝 (-z)] deriv virEdgeFC := by
    filter_upwards [isOpen_virStrip.mem_nhds hm] with u hu
    have hu' : |(-u).im| < 1 / 2 := by simpa using hu
    have hdu := hd1 (-u) hu'
    rw [neg_neg] at hdu
    rw [hdu]
  have hcomp : HasDerivAt (fun u => -deriv virEdgeFC (-u)) (deriv (deriv virEdgeFC) z) (-z) := by
    have hsub : HasDerivAt (fun u : ℂ => -u) (-1) (-z) := hasDerivAt_neg (-z)
    have h0 : HasDerivAt (deriv virEdgeFC) (deriv (deriv virEdgeFC) z) (-(-z)) := by simpa using hd2
    have h1 := (h0.comp (-z) hsub).neg
    refine h1.congr_deriv ?_; ring
  rw [← (Filter.EventuallyEq.deriv_eq hev)]
  exact hcomp.deriv

lemma differentiableOn_yVirC : DifferentiableOn ℂ yVirC {v : ℂ | |v.im| < 1 / 2} := by
  intro v hv
  have hlin : DifferentiableAt ℂ (fun w : ℂ => (π : ℂ) * w) v := by fun_prop
  have hch : DifferentiableAt ℂ (fun w : ℂ => Complex.cosh ((π : ℂ) * w)) v :=
    (Complex.differentiable_cosh _).comp v hlin
  have hsh : DifferentiableAt ℂ (fun w : ℂ => Complex.sinh ((π : ℂ) * w)) v :=
    (Complex.differentiable_sinh _).comp v hlin
  have hsqrt : DifferentiableAt ℂ (fun w : ℂ => (1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)) v :=
    ((differentiableAt_const _).add (hch.pow 2)).cpow_const (one_add_cosh_pi_sq_slit hv)
  have hden_ne : (1 + Complex.cosh ((π : ℂ) * v) ^ 2) ^ (1 / 2 : ℂ) + ((√2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have hre := sqrt_one_add_cosh_re_pos hv
    have hs2 : (0 : ℝ) < √2 := by positivity
    have := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this
    linarith
  exact (hsh.div (hsqrt.add (differentiableAt_const _)) hden_ne).differentiableWithinAt

lemma analyticOnNhd_yVirC : AnalyticOnNhd ℂ yVirC {v : ℂ | |v.im| < 1 / 2} :=
  differentiableOn_yVirC.analyticOnNhd isOpen_virStrip

lemma yVirC_neg (v : ℂ) : yVirC (-v) = -yVirC v := by
  unfold yVirC
  rw [mul_neg, Complex.sinh_neg, Complex.cosh_neg]
  ring

lemma yVirC_conj {v : ℂ} (hv : |v.im| < 1 / 2) :
    yVirC (starRingEnd ℂ v) = starRingEnd ℂ (yVirC v) := by
  have hsq := one_add_cosh_pi_sq_slit hv
  have hc_arg : Complex.cosh ((π : ℂ) * starRingEnd ℂ v) = starRingEnd ℂ (Complex.cosh ((π : ℂ) * v)) := by
    rw [show (π : ℂ) * starRingEnd ℂ v = starRingEnd ℂ ((π : ℂ) * v) by simp, Complex.cosh_conj]
  have hs_arg : Complex.sinh ((π : ℂ) * starRingEnd ℂ v) = starRingEnd ℂ (Complex.sinh ((π : ℂ) * v)) := by
    rw [show (π : ℂ) * starRingEnd ℂ v = starRingEnd ℂ ((π : ℂ) * v) by simp, Complex.sinh_conj]
  have h1c : 1 + Complex.cosh ((π : ℂ) * starRingEnd ℂ v) ^ 2 =
      starRingEnd ℂ (1 + Complex.cosh ((π : ℂ) * v) ^ 2) := by
    rw [hc_arg]; simp
  have hs_c : (1 + Complex.cosh ((π : ℂ) * starRingEnd ℂ v) ^ 2) ^ (1 / 2 : ℂ) =
      starRingEnd ℂ ((1 + Complex.cosh ((π : ℂ) * v) ^ 2) ^ (1 / 2 : ℂ)) := by
    have hc := Complex.cpow_conj (1 + Complex.cosh ((π : ℂ) * v) ^ 2) (1 / 2 : ℂ)
      (Complex.mem_slitPlane_iff_arg.mp hsq).1
    have h12 : starRingEnd ℂ (1 / 2 : ℂ) = (1 / 2 : ℂ) := by rw [map_div₀, map_one, map_ofNat]
    rw [h12] at hc
    rw [h1c, hc, Complex.conj_conj]
  unfold yVirC
  rw [map_div₀, map_add, Complex.conj_ofReal, hs_arg, hs_c]

lemma yVirC_ofReal_nonneg {v : ℝ} (hv : 0 ≤ v) :
    yVirC (v : ℂ) = (lowerY (edgeF v) : ℂ) := by
  unfold yVirC lowerY
  have hsh : Complex.sinh ((π : ℂ) * (v : ℂ)) = ((Real.sinh (π * v) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh]
  have hch : 1 + Complex.cosh ((π : ℂ) * (v : ℂ)) ^ 2 = ((1 + Real.cosh (π * v) ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]; push_cast; ring
  have hsqrt : ((1 + Real.cosh (π * v) ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((√(1 + Real.cosh (π * v) ^ 2) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow]
  rw [hsh, hch, hsqrt]
  have hcoshF : Real.cosh (π * edgeF v) = √(1 + Real.cosh (π * v) ^ 2) := by
    unfold edgeF
    have hpi : π ≠ 0 := Real.pi_pos.ne'
    rw [mul_div_cancel₀ _ hpi, Real.cosh_arsinh]
  rw [hcoshF]
  set R : ℝ := √(1 + Real.cosh (π * v) ^ 2)
  have hR_sq : R ^ 2 = 1 + Real.cosh (π * v) ^ 2 := Real.sq_sqrt (by positivity)
  have hsh_sq : Real.sinh (π * v) ^ 2 = R ^ 2 - 2 := by
    have := Real.cosh_sq_sub_sinh_sq (π * v)
    linarith only [hR_sq, this]
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < R + √2 := by positivity
  have hdiv_eq : (R - √2) / (R + √2) = (Real.sinh (π * v) / (R + √2)) ^ 2 := by
    calc (R - √2) / (R + √2)
        = ((R - √2) * (R + √2)) / (R + √2) ^ 2 := by field_simp [hp.ne']
      _ = (R ^ 2 - √2 ^ 2) / (R + √2) ^ 2 := by ring
      _ = Real.sinh (π * v) ^ 2 / (R + √2) ^ 2 := by rw [h2, hsh_sq]
      _ = (Real.sinh (π * v) / (R + √2)) ^ 2 := (div_pow _ _ 2).symm
  rw [hdiv_eq, Real.sqrt_sq (div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le hv)) hp.le)]
  push_cast; rfl

lemma virPhiDualC_ofReal (v x' : ℝ) : virPhiDualC (v : ℂ) (x' : ℂ) = (phiDual v x' : ℂ) := by
  unfold virPhiDualC virPhi0C phiDual
  have hint_eq : (∫ t in (0 : ℝ)..1, (virEdgeFC ((t : ℂ) * (v : ℂ)) - (xiStar : ℂ)) * (v : ℂ)) =
      ((∫ u in (0 : ℝ)..v, (edgeF u - xiStar) : ℝ) : ℂ) := by
    have hcongr : ∫ t in (0 : ℝ)..1, (virEdgeFC ((t : ℂ) * (v : ℂ)) - (xiStar : ℂ)) * (v : ℂ) =
        ∫ t in (0 : ℝ)..1, (((edgeF (t * v) - xiStar) * v : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [← Complex.ofReal_mul, virEdgeFC_ofReal]
      push_cast; ring
    rw [hcongr, intervalIntegral.integral_ofReal]
    congr 1
    by_cases hv0 : v = 0
    · simp [hv0]
    · have hsub := intervalIntegral.integral_comp_mul_right (fun u : ℝ => edgeF u - xiStar) hv0
        (a := (0 : ℝ)) (b := 1)
      simp only [zero_mul, one_mul, smul_eq_mul] at hsub
      have hswap : ∫ t in (0 : ℝ)..1, (edgeF (t * v) - xiStar) * v =
          (∫ t in (0 : ℝ)..1, edgeF (t * v) - xiStar) * v :=
        intervalIntegral.integral_mul_const _ _
      rw [hswap, hsub]
      field_simp [hv0]
  have hsplit : ∫ u in (0 : ℝ)..v, (edgeF u - x') =
      (∫ u in (0 : ℝ)..v, (edgeF u - xiStar)) - (x' - xiStar) * v := by
    have hcF : Continuous (fun u : ℝ => edgeF u - xiStar) :=
      (continuous_iff_continuousAt.mpr fun u => (hasDerivAt_edgeF u).continuousAt).sub continuous_const
    have h_fn : (fun u : ℝ => edgeF u - x') = fun u : ℝ => (edgeF u - xiStar) - (x' - xiStar) := by
      ext u; ring
    rw [h_fn, intervalIntegral.integral_sub (hcF.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rw [hint_eq, hsplit]
  push_cast; ring

/-! ### 2. Even factorization of `virEdgeFC z - xiStar = z² virF1 (z²)` and Virasoro `CtChartData` -/

/-- Taylor coefficient `(F(z) - ξ_*) / z² = ∫₀¹ (1 - t) F''(t z) dt` (even near `0`). -/
def virEdgeF1Even (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (1 - (t : ℂ)) * deriv (deriv virEdgeFC) ((t : ℂ) * z)

private lemma analyticAt_virEdgeFC2_0 :
    AnalyticAt ℂ (deriv (deriv virEdgeFC)) 0 := by
  have hderiv_an : AnalyticOnNhd ℂ (deriv virEdgeFC) {z : ℂ | |z.im| < 1 / 2} := by
    intro w hw
    exact (analyticOnNhd_virEdgeFC' w hw).congr (by
      filter_upwards [isOpen_virStrip.mem_nhds hw] with u hu using (deriv_virEdgeFC_eq hu).symm)
  exact (hderiv_an.deriv 0 (by simp))

private lemma virEdgeF1Even_contDiffAt : ContDiffAt ℂ ∞' virEdgeF1Even 0 := by
  unfold virEdgeF1Even
  refine contDiffAt_segInt (F := fun z w : ℂ => (1 - w) * deriv (deriv virEdgeFC) (w * z)) ?_
  intro t _
  have hcd : ContDiffAt ℂ ∞' (deriv (deriv virEdgeFC)) ((fun p : ℂ × ℂ => p.2 * p.1) (0, (t : ℂ))) := by
    simpa using analyticAt_virEdgeFC2_0.contDiffAt
  have hcomp : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => deriv (deriv virEdgeFC) (p.2 * p.1)) (0, (t : ℂ)) :=
    ContDiffAt.comp (g := deriv (deriv virEdgeFC)) (f := fun p : ℂ × ℂ => p.2 * p.1) (0, (t : ℂ)) hcd
      (contDiff_snd.mul contDiff_fst).contDiffAt
  exact (contDiff_const.sub contDiff_snd).contDiffAt.mul hcomp

private lemma virEdgeF1Even_even (z : ℂ) (hz : ‖z‖ < 1 / 2) :
    virEdgeF1Even (-z) = virEdgeF1Even z := by
  unfold virEdgeF1Even
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  have htz : |((t : ℂ) * z).im| < 1 / 2 := by
    have : ((t : ℂ) * z).im = t * z.im := by simp
    rw [this, abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans_lt ((Complex.abs_im_le_norm z).trans_lt hz)
  have hmul : (t : ℂ) * (-z) = -((t : ℂ) * z) := by ring
  rw [hmul, virEdgeFC''_neg htz]

private lemma virEdgeFC_taylor_eq {z : ℂ} (hz : ‖z‖ < 1 / 2) :
    virEdgeFC z - (xiStar : ℂ) = z ^ 2 * virEdgeF1Even z := by
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, |((0 : ℂ) + (t : ℂ) * (z - 0)).im| < 1 / 2 := fun t ht => by
    have him : ((0 : ℂ) + (t : ℂ) * (z - 0)).im = t * z.im := by simp
    rw [him, abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans_lt ((Complex.abs_im_le_norm z).trans_lt hz)
  have hderiv_an : AnalyticOnNhd ℂ (deriv virEdgeFC) {w : ℂ | |w.im| < 1 / 2} := by
    intro w hw
    exact (analyticOnNhd_virEdgeFC' w hw).congr (by
      filter_upwards [isOpen_virStrip.mem_nhds hw] with u hu using (deriv_virEdgeFC_eq hu).symm)
  have h1 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt virEdgeFC (deriv virEdgeFC ((0 : ℂ) + (t : ℂ) * (z - 0)))
      ((0 : ℂ) + (t : ℂ) * (z - 0)) := fun t ht => by
    rw [deriv_virEdgeFC_eq (hseg t ht)]
    exact hasDerivAt_virEdgeFC (hseg t ht)
  have h2 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (deriv virEdgeFC)
      (deriv (deriv virEdgeFC) ((0 : ℂ) + (t : ℂ) * (z - 0))) ((0 : ℂ) + (t : ℂ) * (z - 0)) := fun t ht =>
    (hderiv_an _ (hseg t ht)).differentiableAt.hasDerivAt
  have hc2 : ContinuousOn (fun t : ℝ => deriv (deriv virEdgeFC) ((0 : ℂ) + (t : ℂ) * (z - 0))) (Icc 0 1) := by
    intro t ht
    have hcd : ContinuousAt (deriv (deriv virEdgeFC)) ((0 : ℂ) + (t : ℂ) * (z - 0)) :=
      (hderiv_an.deriv _ (hseg t ht)).continuousAt
    have hlin : ContinuousAt (fun s : ℝ => (0 : ℂ) + (s : ℂ) * (z - 0)) t := by fun_prop
    exact (ContinuousAt.comp (g := deriv (deriv virEdgeFC))
      (f := fun s : ℝ => (0 : ℂ) + (s : ℂ) * (z - 0)) hcd hlin).continuousWithinAt
  have ht2 := taylor2_seg h1 h2 hc2
  simp only [zero_add, sub_zero, virEdgeFC_zero, deriv_virEdgeFC_zero, zero_mul] at ht2
  exact ht2

lemma exists_virF1_temp :
    ∃ gh : ℂ → ℂ, AnalyticAt ℂ gh 0 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), virEdgeF1Even z = gh (z ^ 2) := by
  let g_even : ℂ → ℂ := fun z => (virEdgeF1Even z + virEdgeF1Even (-z)) / 2
  have hg_an : AnalyticAt ℂ g_even 0 := by
    have h1 : AnalyticAt ℂ virEdgeF1Even 0 := analyticAt_of_cd virEdgeF1Even_contDiffAt
    have hneg : AnalyticAt ℂ (fun z : ℂ => -z) 0 := analyticAt_id.neg
    have h2 : AnalyticAt ℂ (fun z => virEdgeF1Even (-z)) 0 := by
      change AnalyticAt ℂ (virEdgeF1Even ∘ fun z : ℂ => -z) 0
      exact AnalyticAt.comp (g := virEdgeF1Even) (f := fun z : ℂ => -z) (by simpa using h1) hneg
    exact (h1.add h2).div analyticAt_const (by norm_num)
  have hg_ev : ∀ x, g_even (-x) = g_even x := fun x => by dsimp [g_even]; rw [neg_neg, add_comm]
  obtain ⟨gh, hgh_an, hgh_eq⟩ := exists_sq_of_even hg_an hg_ev
  refine ⟨gh, hgh_an, ?_⟩
  have hball : ∀ᶠ z in 𝓝 (0 : ℂ), ‖z‖ < 1 / 2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
    simpa using hz
  filter_upwards [hgh_eq, hball] with z hz hzb
  rw [← hz]
  dsimp [g_even]
  rw [virEdgeF1Even_even z hzb]
  ring

/-- Analytic function `virF1` solving `virEdgeFC z - xiStar = z² virF1(z²)` near `0`. -/
def virF1 : ℂ → ℂ := Classical.choose exists_virF1_temp

lemma analyticAt_virF1 : AnalyticAt ℂ virF1 0 := (Classical.choose_spec exists_virF1_temp).1
lemma contDiffAt_virF1 : ContDiffAt ℂ ∞' virF1 0 := analyticAt_virF1.contDiffAt

lemma virEdgeFC_sub_xiStar_eq :
    ∀ᶠ z in 𝓝 (0 : ℂ), virEdgeFC z - (xiStar : ℂ) = z ^ 2 * virF1 (z ^ 2) := by
  have hball : ∀ᶠ z in 𝓝 (0 : ℂ), ‖z‖ < 1 / 2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
    simpa using hz
  filter_upwards [(Classical.choose_spec exists_virF1_temp).2, hball] with z hz hzb
  rw [virEdgeFC_taylor_eq hzb]
  change z ^ 2 * virEdgeF1Even z = z ^ 2 * Classical.choose exists_virF1_temp (z ^ 2)
  rw [hz]

lemma virF1_zero : virF1 0 = ((π / (2 * √2) : ℝ) : ℂ) := by
  have h0 : virEdgeF1Even 0 = virF1 0 := by
    have hs := (Classical.choose_spec exists_virF1_temp).2.self_of_nhds
    simpa [virF1] using hs
  rw [← h0]
  unfold virEdgeF1Even
  simp only [mul_zero, virEdgeFC''_zero]
  have hconst : ∫ t in (0 : ℝ)..1, (1 - (t : ℂ)) * ((π / √2 : ℝ) : ℂ) =
      (((∫ t in (0 : ℝ)..1, (1 - t) * (π / √2) : ℝ)) : ℂ) := by
    have hfn : (fun t : ℝ => (1 - (t : ℂ)) * ((π / √2 : ℝ) : ℂ)) =
        fun t : ℝ => (((1 - t) * (π / √2) : ℝ) : ℂ) := by ext t; push_cast; ring
    rw [hfn, intervalIntegral.integral_ofReal]
  rw [hconst]
  congr 1
  have hlin : ∫ t in (0 : ℝ)..1, (1 - t) = (1 / 2 : ℝ) := by
    have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => -(1 - s) ^ 2 / 2) (1 - t) t := fun t _ => by
      have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := (hasDerivAt_id t).const_sub 1
      have h2 := ((h1.pow 2).neg.div_const 2)
      refine h2.congr_deriv ?_; ring
    have hint : IntervalIntegrable (fun t : ℝ => 1 - t) volume 0 1 :=
      (Continuous.sub continuous_const continuous_id).intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    norm_num
  rw [intervalIntegral.integral_mul_const, hlin]
  ring

lemma virF1_conj : ∀ᶠ w in 𝓝 (0 : ℂ), virF1 (starRingEnd ℂ w) = starRingEnd ℂ (virF1 w) := by
  obtain ⟨r, hr, hball_an⟩ := Metric.eventually_nhds_iff_ball.mp
    (analyticAt_virF1.eventually_analyticAt)
  have hev_z := Metric.eventually_nhds_iff_ball.mp
    ((Classical.choose_spec exists_virF1_temp).2.and (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 2)))
  obtain ⟨rz, hrz, hrz_spec⟩ := hev_z
  have heq_pos : ∀ x : ℝ, 0 < x → x < min r (rz ^ 2) → virF1 (x : ℂ) = starRingEnd ℂ (virF1 (starRingEnd ℂ (x : ℂ))) := by
    intro x hx0 hx_lt
    have hx_rz2 : x < rz ^ 2 := hx_lt.trans_le (min_le_right _ _)
    set s : ℝ := √x
    have hs_pos : 0 < s := Real.sqrt_pos.mpr hx0
    have hs_rz : ‖(s : ℂ)‖ < rz := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs_pos]
      rw [← Real.sqrt_sq hrz.le]
      exact Real.sqrt_lt_sqrt hx0.le hx_rz2
    have hsp := hrz_spec (s : ℂ) (mem_ball_zero_iff.mpr hs_rz)
    have hreal_F1 : (virEdgeF1Even (s : ℂ)).im = 0 := by
      have hconj_s : virEdgeF1Even (starRingEnd ℂ (s : ℂ)) = starRingEnd ℂ (virEdgeF1Even (s : ℂ)) := by
        unfold virEdgeF1Even
        rw [← intInt_conj]
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le zero_le_one] at ht
        have htz : |((t : ℂ) * (s : ℂ)).im| < 1 / 2 := by
          have : ((t : ℂ) * (s : ℂ)).im = 0 := by simp
          rw [this]; norm_num
        have he : (t : ℂ) * starRingEnd ℂ (s : ℂ) = starRingEnd ℂ ((t : ℂ) * (s : ℂ)) := by simp
        rw [he, virEdgeFC''_conj htz, map_mul, map_sub, map_one, Complex.conj_ofReal]
      rw [Complex.conj_ofReal] at hconj_s
      exact (Complex.conj_eq_iff_im.mp hconj_s.symm)
    have hs2 : (s : ℂ) ^ 2 = (x : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hx0.le]
    have hval : virF1 ((s : ℂ) ^ 2) = virEdgeF1Even (s : ℂ) := (hsp.1).symm
    have him : (virF1 (x : ℂ)).im = 0 := by rw [← hs2, hval]; exact hreal_F1
    rw [Complex.conj_ofReal]
    exact (Complex.conj_eq_iff_im.mpr him).symm
  have hr2 : 0 < min r (rz ^ 2) := lt_min hr (sq_pos_of_pos hrz)
  have heq : EqOn virF1 (fun w => starRingEnd ℂ (virF1 (starRingEnd ℂ w))) (ball 0 (min r (rz ^ 2))) := by
    have han1 : AnalyticOnNhd ℂ virF1 (ball 0 (min r (rz ^ 2))) :=
      fun w hw => hball_an w (ball_subset_ball (min_le_left _ _) hw)
    have hdiff2 : DifferentiableOn ℂ (fun w => starRingEnd ℂ (virF1 (starRingEnd ℂ w))) (ball 0 (min r (rz ^ 2))) := by
      intro w hw
      have hw' : starRingEnd ℂ w ∈ ball (0 : ℂ) r := by
        simpa using (ball_subset_ball (min_le_left _ _) hw)
      have hd := hasDerivAt_conj_conj (hball_an _ hw').differentiableAt.hasDerivAt
      rw [Complex.conj_conj] at hd
      exact hd.differentiableAt.differentiableWithinAt
    have han2 : AnalyticOnNhd ℂ (fun w => starRingEnd ℂ (virF1 (starRingEnd ℂ w))) (ball 0 (min r (rz ^ 2))) :=
      hdiff2.analyticOnNhd isOpen_ball
    refine han1.eqOn_of_preconnected_of_frequently_eq han2 (convex_ball _ _).isPreconnected
      (mem_ball_self hr2) ?_
    rw [frequently_iff]
    intro U hU
    rw [mem_nhdsWithin] at hU
    obtain ⟨V, hV_open, h0V, hVU⟩ := hU
    obtain ⟨δ, hδ_pos, hδball⟩ := Metric.isOpen_iff.mp hV_open 0 h0V
    set t : ℝ := min (δ / 2) (min r (rz ^ 2) / 2)
    have ht0 : 0 < t := lt_min (half_pos hδ_pos) (half_pos hr2)
    refine ⟨(t : ℂ), hVU ⟨hδball ?_, by simp [ht0.ne']⟩, heq_pos t ht0 ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      exact (min_le_left _ _).trans_lt (half_lt_self hδ_pos)
    · exact (min_le_right _ _).trans_lt (half_lt_self hr2)
  filter_upwards [Metric.ball_mem_nhds 0 hr2] with w hw
  have hw' : starRingEnd ℂ w ∈ ball (0 : ℂ) (min r (rz ^ 2)) := by simpa using hw
  have := heq hw'
  dsimp only at this
  rw [Complex.conj_conj] at this
  exact this

/-! ### 3. Virasoro `L_vir`, `p_vir`, `d_vir`, `a_vir`, and `deriv virPC β = (virNC β - virNtC β) / 2` -/

def virNC (w : ℂ) : ℂ := ((4 * π / 3 : ℝ) : ℂ) * virF1 w

def virNtC (w : ℂ) : ℂ :=
  ((4 * π / 3 : ℝ) : ℂ) * ∫ s in (0 : ℝ)..1, ((s : ℝ) : ℂ) ^ 2 * virF1 (((s : ℝ) : ℂ) ^ 2 * w)

def virPC (w : ℂ) : ℂ := w * virNtC w

def virPC2 : ℂ → ℂ := deriv (deriv virPC)

def virFC (β : ℂ) : ℂ := virNC β - virNtC β

def virDC (β : ℂ) : ℂ := Complex.exp (Complex.log ((3 / 2 : ℂ) * virFC β) / 3)

def virAC (β : ℂ) : ℂ := -(virDC β) ^ 2 * β

def virLC (β : ℂ) : ℂ := β * virNC β

def virXPrimeOfBeta (β : ℂ) : ℂ := (xiStar : ℂ) + β * virF1 β

noncomputable def virD0 : ℝ := (2 * π ^ 2 / (3 * √2)) ^ (1 / 3 : ℝ)

lemma virD0_pos : 0 < virD0 := by unfold virD0; positivity

lemma virD0C_ne : ((virD0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast virD0_pos.ne'

lemma virD0C_cube : ((virD0 : ℝ) : ℂ) ^ 3 = ((2 * π ^ 2 / (3 * √2) : ℝ) : ℂ) := by
  have h1 : virD0 ^ 3 = 2 * π ^ 2 / (3 * √2) := by
    unfold virD0; rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  exact_mod_cast h1

lemma contDiffAt_virNC : ContDiffAt ℂ ∞' virNC 0 := contDiffAt_const.mul contDiffAt_virF1

lemma contDiffAt_virNtC : ContDiffAt ℂ ∞' virNtC 0 := by
  unfold virNtC
  refine contDiffAt_const.mul (contDiffAt_segInt (F := fun w s : ℂ => s ^ 2 * virF1 (s ^ 2 * w)) ?_)
  intro s _
  have hcd : ContDiffAt ℂ ∞' virF1 ((fun p : ℂ × ℂ => p.2 ^ 2 * p.1) (0, (s : ℂ))) := by
    simpa using contDiffAt_virF1
  have hcomp : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => virF1 (p.2 ^ 2 * p.1)) (0, (s : ℂ)) :=
    ContDiffAt.comp (g := virF1) (f := fun p : ℂ × ℂ => p.2 ^ 2 * p.1) (0, (s : ℂ)) hcd
      ((contDiff_snd.pow 2).mul contDiff_fst).contDiffAt
  exact (contDiff_snd.pow 2).contDiffAt.mul hcomp

lemma contDiffAt_virPC : ContDiffAt ℂ ∞' virPC 0 := contDiffAt_id.mul contDiffAt_virNtC
lemma analyticAt_virPC : AnalyticAt ℂ virPC 0 := analyticAt_of_cd contDiffAt_virPC
lemma analyticAt_virNC : AnalyticAt ℂ virNC 0 := analyticAt_of_cd contDiffAt_virNC
lemma analyticAt_virNtC : AnalyticAt ℂ virNtC 0 := analyticAt_of_cd contDiffAt_virNtC
lemma analyticAt_virPC2 : AnalyticAt ℂ virPC2 0 := analyticAt_virPC.deriv.deriv
lemma contDiffAt_virPC2 : ContDiffAt ℂ ∞' virPC2 0 := analyticAt_virPC2.contDiffAt
lemma contDiffAt_virFC : ContDiffAt ℂ ∞' virFC 0 := contDiffAt_virNC.sub contDiffAt_virNtC

lemma virNC_zero : virNC 0 = ((2 * π ^ 2 / (3 * √2) : ℝ) : ℂ) := by
  unfold virNC; rw [virF1_zero]; push_cast
  have h2 : √2 ≠ 0 := by positivity
  field_simp [h2]; ring

lemma virNtC_zero : virNtC 0 = ((2 * π ^ 2 / (9 * √2) : ℝ) : ℂ) := by
  unfold virNtC
  simp only [mul_zero, virF1_zero]
  have hconst : ∫ s in (0 : ℝ)..1, ((s : ℝ) : ℂ) ^ 2 * ((π / (2 * √2) : ℝ) : ℂ) =
      (((∫ s in (0 : ℝ)..1, s ^ 2 * (π / (2 * √2)) : ℝ)) : ℂ) := by
    have hfn : (fun s : ℝ => ((s : ℝ) : ℂ) ^ 2 * ((π / (2 * √2) : ℝ) : ℂ)) =
        fun s : ℝ => (((s ^ 2 * (π / (2 * √2)) : ℝ)) : ℂ) := by ext s; push_cast; ring
    rw [hfn, intervalIntegral.integral_ofReal]
  rw [hconst, intervalIntegral.integral_mul_const]
  have h13 : ∫ s in (0 : ℝ)..1, s ^ 2 = (1 / 3 : ℝ) := by norm_num
  rw [h13]
  push_cast
  have h2 : √2 ≠ 0 := by positivity
  field_simp [h2]; ring

lemma virFC_zero : virFC 0 = ((4 * π ^ 2 / (9 * √2) : ℝ) : ℂ) := by
  unfold virFC; rw [virNC_zero, virNtC_zero]; push_cast
  have h2 : √2 ≠ 0 := by positivity
  field_simp [h2]; ring

lemma three_half_virFC_zero : (3 / 2 : ℂ) * virFC 0 = ((virD0 : ℝ) : ℂ) ^ 3 := by
  rw [virFC_zero, virD0C_cube]; push_cast
  have h2 : √2 ≠ 0 := by positivity
  field_simp [h2]; ring

lemma slit_three_half_virFC_zero : (3 / 2 : ℂ) * virFC 0 ∈ Complex.slitPlane := by
  rw [three_half_virFC_zero]
  have : ((virD0 : ℝ) : ℂ) ^ 3 = ((virD0 ^ 3 : ℝ) : ℂ) := by push_cast; ring
  rw [this]
  exact Complex.ofReal_mem_slitPlane.mpr (pow_pos virD0_pos 3)

lemma contDiffAt_virDC : ContDiffAt ℂ ∞' virDC 0 := by
  unfold virDC
  refine Complex.contDiff_exp.contDiffAt.comp 0 ?_
  exact ((Complex.contDiffAt_log slit_three_half_virFC_zero).comp 0
    (contDiffAt_const.mul contDiffAt_virFC)).div_const _

lemma virDC_zero : virDC 0 = ((virD0 : ℝ) : ℂ) := by
  unfold virDC
  rw [three_half_virFC_zero]
  have hpos : 0 < virD0 := virD0_pos
  have : ((virD0 : ℝ) : ℂ) ^ 3 = ((virD0 ^ 3 : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_log (by positivity), Real.log_pow]
  have h3 : ((((3 : ℕ) : ℝ) * Real.log virD0 : ℝ) : ℂ) / 3 = ((Real.log virD0 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h3, ← Complex.ofReal_exp, Real.exp_log hpos]

lemma virDC_cube : ∀ᶠ β in 𝓝 (0 : ℂ), virDC β ^ 3 = (3 / 2 : ℂ) * virFC β := by
  have hc : ContinuousAt (fun β => (3 / 2 : ℂ) * virFC β) 0 := (contDiffAt_const.mul contDiffAt_virFC).continuousAt
  filter_upwards [hc.eventually_ne (by rw [three_half_virFC_zero]; exact pow_ne_zero 3 virD0C_ne)] with β hβ
  unfold virDC
  rw [← Complex.exp_nat_mul]
  have : (↑(3 : ℕ) : ℂ) * (Complex.log ((3 / 2 : ℂ) * virFC β) / 3) = Complex.log ((3 / 2 : ℂ) * virFC β) := by
    push_cast; ring
  rw [this, Complex.exp_log hβ]

lemma virNC_conj : ∀ᶠ w in 𝓝 (0 : ℂ), virNC (starRingEnd ℂ w) = starRingEnd ℂ (virNC w) := by
  filter_upwards [virF1_conj] with w hw
  unfold virNC; rw [hw, map_mul, Complex.conj_ofReal]

lemma virNtC_conj : ∀ᶠ w in 𝓝 (0 : ℂ), virNtC (starRingEnd ℂ w) = starRingEnd ℂ (virNtC w) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp virF1_conj
  filter_upwards [Metric.ball_mem_nhds 0 hr] with w hw
  unfold virNtC
  rw [map_mul, Complex.conj_ofReal, ← intInt_conj]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  have hmem : ((s : ℝ) : ℂ) ^ 2 * w ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    have hsn : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    calc s ^ 2 * ‖w‖ ≤ 1 * ‖w‖ := by gcongr
      _ = ‖w‖ := one_mul _
      _ < r := mem_ball_zero_iff.mp hw
  have hfc := hball _ hmem
  have he : ((s : ℝ) : ℂ) ^ 2 * starRingEnd ℂ w = starRingEnd ℂ (((s : ℝ) : ℂ) ^ 2 * w) := by simp
  rw [he, hfc, map_mul, map_pow, Complex.conj_ofReal]

lemma virPC_conj : ∀ᶠ w in 𝓝 (0 : ℂ), virPC (starRingEnd ℂ w) = starRingEnd ℂ (virPC w) := by
  filter_upwards [virNtC_conj] with w hw
  unfold virPC; rw [hw, map_mul]

lemma virFC_conj : ∀ᶠ β in 𝓝 (0 : ℂ), virFC (starRingEnd ℂ β) = starRingEnd ℂ (virFC β) := by
  filter_upwards [virNC_conj, virNtC_conj] with β h1 h2
  unfold virFC; rw [h1, h2, map_sub]

lemma virDC_conj : ∀ᶠ β in 𝓝 (0 : ℂ), virDC (starRingEnd ℂ β) = starRingEnd ℂ (virDC β) := by
  have hc : ContinuousAt (fun β => (3 / 2 : ℂ) * virFC β) 0 := (contDiffAt_const.mul contDiffAt_virFC).continuousAt
  have hs : ∀ᶠ β in 𝓝 (0 : ℂ), (3 / 2 : ℂ) * virFC β ∈ Complex.slitPlane :=
    hc.eventually (Complex.isOpen_slitPlane.mem_nhds slit_three_half_virFC_zero)
  filter_upwards [hs, virFC_conj] with β hβ hfc
  unfold virDC
  have e1 : (3 / 2 : ℂ) * virFC (starRingEnd ℂ β) = starRingEnd ℂ ((3 / 2 : ℂ) * virFC β) := by
    rw [hfc, map_mul, map_div₀, map_ofNat, map_ofNat]
  rw [e1, Complex.log_conj _ (Complex.mem_slitPlane_iff_arg.mp hβ).1, ← Complex.exp_conj]
  congr 1; rw [map_div₀, map_ofNat]

lemma virPhi0C_eq_mul_virPC : ∀ᶠ v in 𝓝 (0 : ℂ), virPhi0C v = v * virPC (v ^ 2) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp virEdgeFC_sub_xiStar_eq
  filter_upwards [Metric.ball_mem_nhds 0 hr] with v hv
  unfold virPhi0C virPC virNtC
  have hcongr : ∫ t in (0 : ℝ)..1, (virEdgeFC ((t : ℂ) * v) - (xiStar : ℂ)) * v =
      v ^ 3 * ∫ t in (0 : ℝ)..1, ((t : ℝ) : ℂ) ^ 2 * virF1 (((t : ℝ) : ℂ) ^ 2 * v ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    have hmem : (t : ℂ) * v ∈ ball (0 : ℂ) r := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖v‖ ≤ 1 * ‖v‖ := by gcongr; exact ht.2
        _ = ‖v‖ := one_mul _
        _ < r := mem_ball_zero_iff.mp hv
    rw [hball _ hmem]
    ring
  rw [hcongr]; ring

lemma deriv_virPC_eq : ∀ᶠ β in 𝓝 (0 : ℂ), deriv virPC β = (virNC β - virNtC β) / 2 := by
  obtain ⟨r1, hr1, hphi_eq⟩ := Metric.eventually_nhds_iff_ball.mp virPhi0C_eq_mul_virPC
  obtain ⟨r2, hr2, hsub_eq⟩ := Metric.eventually_nhds_iff_ball.mp virEdgeFC_sub_xiStar_eq
  obtain ⟨r3, hr3, hPC_an⟩ := Metric.eventually_nhds_iff_ball.mp analyticAt_virPC.eventually_analyticAt
  obtain ⟨r4, hr4, hNC_an⟩ := Metric.eventually_nhds_iff_ball.mp analyticAt_virNC.eventually_analyticAt
  obtain ⟨r5, hr5, hNtC_an⟩ := Metric.eventually_nhds_iff_ball.mp analyticAt_virNtC.eventually_analyticAt
  let r : ℝ := min (min r1 r2) (min r3 (min r4 r5))
  have hr : 0 < r := lt_min (lt_min hr1 hr2) (lt_min hr3 (lt_min hr4 hr5))
  have hr_1 : r ≤ r1 := (min_le_left _ _).trans (min_le_left _ _)
  have hr_2 : r ≤ r2 := (min_le_left _ _).trans (min_le_right _ _)
  have hr_3 : r ≤ r3 := (min_le_right _ _).trans (min_le_left _ _)
  have hr_4 : r ≤ r4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr_5 : r ≤ r5 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have han_lhs : AnalyticOnNhd ℂ (deriv virPC) (ball 0 r) := fun w hw => by
    have hball : AnalyticOnNhd ℂ virPC (ball 0 r3) := hPC_an
    exact hball.deriv w (ball_subset_ball hr_3 hw)
  have han_rhs : AnalyticOnNhd ℂ (fun β => (virNC β - virNtC β) / 2) (ball 0 r) := fun w hw =>
    ((hNC_an w (ball_subset_ball hr_4 hw)).sub (hNtC_an w (ball_subset_ball hr_5 hw))).div
      analyticAt_const (by norm_num)
  have heq_pos : ∀ β : ℝ, 0 < β → β < min r (r ^ 2) → deriv virPC (β : ℂ) = (virNC (β : ℂ) - virNtC (β : ℂ)) / 2 := by
    intro β hβ0 hβ_lt
    set v : ℝ := √β
    have hv0 : 0 < v := Real.sqrt_pos.mpr hβ0
    have hv_r : v < r := by
      rw [← Real.sqrt_sq hr.le]
      exact Real.sqrt_lt_sqrt hβ0.le (hβ_lt.trans_le (min_le_right _ _))
    have hv_mem : (v : ℂ) ∈ ball (0 : ℂ) r := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv0]; exact hv_r
    have hv2_mem : ((v : ℂ) ^ 2) ∈ ball (0 : ℂ) r := by
      rw [mem_ball_zero_iff, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv0,
        Real.sq_sqrt hβ0.le]
      exact hβ_lt.trans_le (min_le_left _ _)
    have hd1 : HasDerivAt (fun x : ℝ => virPhi0C (x : ℂ))
        (((4 * π / 3 : ℝ) : ℂ) * (virEdgeFC (v : ℂ) - (xiStar : ℂ))) v := by
      have hreal : ∀ x : ℝ, virPhi0C (x : ℂ) = (((4 * π / 3) * ∫ u in (0 : ℝ)..x, (edgeF u - xiStar) : ℝ) : ℂ) := by
        intro x
        have h := virPhiDualC_ofReal x xiStar
        unfold virPhiDualC phiDual at h
        simp only [sub_self, mul_zero, zero_mul, sub_zero] at h ⊢
        exact h
      have hcontF : Continuous (fun u : ℝ => edgeF u - xiStar) :=
        (continuous_iff_continuousAt.mpr fun u => (hasDerivAt_edgeF u).continuousAt).sub continuous_const
      have hd_int : HasDerivAt (fun x : ℝ => ∫ u in (0 : ℝ)..x, (edgeF u - xiStar)) (edgeF v - xiStar) v :=
        intervalIntegral.integral_hasDerivAt_right (hcontF.intervalIntegrable 0 v)
          (hcontF.stronglyMeasurableAtFilter _ _) hcontF.continuousAt
      have hdC := (hd_int.const_mul (4 * π / 3)).ofReal_comp
      refine (hdC.congr_of_eventuallyEq (Eventually.of_forall fun x => (hreal x))).congr_deriv ?_
      rw [virEdgeFC_ofReal]; push_cast; ring
    have hd2 : HasDerivAt (fun x : ℝ => (x : ℂ) * virPC ((x : ℂ) ^ 2))
        (virPC ((v : ℂ) ^ 2) + 2 * (v : ℂ) ^ 2 * deriv virPC ((v : ℂ) ^ 2)) v := by
      have hidC : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 v := (hasDerivAt_id v).ofReal_comp
      have hsq : HasDerivAt (fun x : ℝ => (x : ℂ) ^ 2) (2 * (v : ℂ)) v := by
        have hp := (hasDerivAt_pow 2 (v : ℂ)).comp_ofReal
        exact hp.congr_deriv (by simp)
      have hpc : HasDerivAt virPC (deriv virPC ((v : ℂ) ^ 2)) ((v : ℂ) ^ 2) :=
        (hPC_an _ (ball_subset_ball hr_3 hv2_mem)).differentiableAt.hasDerivAt
      have hcomp := hidC.mul (hpc.comp v hsq)
      refine hcomp.congr_deriv ?_
      change 1 * virPC ((v : ℂ) ^ 2) + (v : ℂ) * (deriv virPC ((v : ℂ) ^ 2) * (2 * (v : ℂ))) =
        virPC ((v : ℂ) ^ 2) + 2 * (v : ℂ) ^ 2 * deriv virPC ((v : ℂ) ^ 2)
      ring
    have hev_eq : (fun x : ℝ => (x : ℂ) * virPC ((x : ℂ) ^ 2)) =ᶠ[𝓝 v] fun x : ℝ => virPhi0C (x : ℂ) := by
      filter_upwards [Metric.ball_mem_nhds v (sub_pos.mpr hv_r)] with x hx
      have hx_mem : (x : ℂ) ∈ ball (0 : ℂ) r1 := by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        have hx1 : |x - v| < r - v := by simpa [Real.dist_eq] using hx
        have hxa : |x| < r := by
          have := abs_sub_abs_le_abs_sub x v
          rw [abs_of_pos hv0] at this
          linarith [abs_le.mp hx1.le]
        exact hxa.trans_le hr_1
      exact (hphi_eq _ hx_mem).symm
    have heq_d := hd1.unique (hd2.congr_of_eventuallyEq hev_eq.symm)
    rw [hsub_eq _ (ball_subset_ball hr_2 hv_mem)] at heq_d
    have hv2_ne : ((v : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hv0.ne')
    have hvir_eq : (v : ℂ) ^ 2 = (β : ℂ) := by rw [← Complex.ofReal_pow, Real.sq_sqrt hβ0.le]
    have hpc_exp : virPC ((v : ℂ) ^ 2) = (v : ℂ) ^ 2 * virNtC ((v : ℂ) ^ 2) := rfl
    rw [hpc_exp] at heq_d
    rw [← hvir_eq]
    have hmul_eq : (v : ℂ) ^ 2 * (2 * deriv virPC ((v : ℂ) ^ 2) - (virNC ((v : ℂ) ^ 2) - virNtC ((v : ℂ) ^ 2))) = 0 := by
      unfold virNC
      linear_combination -heq_d
    have hzero := (mul_eq_zero.mp hmul_eq).resolve_left hv2_ne
    linear_combination hzero / 2
  have heq : EqOn (deriv virPC) (fun β => (virNC β - virNtC β) / 2) (ball 0 r) := by
    refine han_lhs.eqOn_of_preconnected_of_frequently_eq han_rhs (convex_ball _ _).isPreconnected
      (mem_ball_self hr) ?_
    rw [frequently_iff]
    intro U hU
    rw [mem_nhdsWithin] at hU
    obtain ⟨V, hV_open, h0V, hVU⟩ := hU
    obtain ⟨δ, hδ_pos, hδball⟩ := Metric.isOpen_iff.mp hV_open 0 h0V
    set t : ℝ := min (δ / 2) (min r (r ^ 2) / 2)
    have ht0 : 0 < t := lt_min (half_pos hδ_pos) (half_pos (lt_min hr (sq_pos_of_pos hr)))
    refine ⟨(t : ℂ), hVU ⟨hδball ?_, by simp [ht0.ne']⟩, heq_pos t ht0 ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      exact (min_le_left _ _).trans_lt (half_lt_self hδ_pos)
    · exact (min_le_right _ _).trans_lt (half_lt_self (lt_min hr (sq_pos_of_pos hr)))
  filter_upwards [Metric.ball_mem_nhds 0 hr] with β hβ
  exact heq hβ

end

end FormalResearch.ModularBootstrap.FiveTerm
