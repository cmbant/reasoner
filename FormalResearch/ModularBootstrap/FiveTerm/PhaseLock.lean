module

public import FormalResearch.ModularBootstrap.Upper.Saddle.EdgePhaseZero

/-!
# The exact phase-locking identity on the upper strip edge (`cts:phaselock`, Proposition C2)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, §`cts:s2`.

With `F(v) = π⁻¹ arsinh(cosh πv)` (`edgeF`), `v_x = F⁻¹(x) = π⁻¹ arccosh(sinh πx) = (3/4) ρ_U(x)`
(`vTip`), `b_x = v_x + i/2`, `Φ₀ = edgePhi0Blaschke` (the leading Blaschke potential of Lemma `SD_0`)
and `N = cumulN` (the counting function `N(x) = ½ ∫_{ξ_*}^x ρ_U`):

* `phaseLock_identity` (`cts:pl-id`): for every `x ≥ ξ_*`,
  `Im Φ₀(b_x) + (4π/3) x v_x = 2π N(x)`, with zero additive constant.
* `negBlaschkeT_tip_eq_exp` and `absentCharge_phase` (`cts:dth0`): for `x > ξ_*`, with
  `ψ(x) = arctan(sinh(π v_x)/√2) ∈ (0, π/2)`, `-T_{ξ_*}(b_x) = e^{-2iψ}`, and
  `(-T_{ξ_*}(b_x))^{-3/2} b_x^{1/2} = |b_x|^{1/2} e^{iΔθ₀(x)}`,
  `Δθ₀(x) = 3ψ(x) + ½ arctan(1/(2 v_x))` (principal branches; `-3/2` power is the one continuous from
  `v_x = 0`, which for `ψ ∈ (0, π/2)` is the principal power). The paper's `arg` is the continuous
  determination (it exceeds `π` when `ψ > π/3`), so the statement is given as an equality with the
  polar form rather than with `Complex.arg`.

* §4, the slit parametrisation `z = iy ↔ x` of `cts:s3` (`cosh πx = √2 (1+y²)/(1-y²)`):
  `psiTip_eq_two_arctan` (`ψ = 2 arctan y`), `edgeF'_vTip_eq` (`F'(v_x) = 2y/(1+y²)`), and the
  detuning facts of `cts:eta-opt`: `cosh_two_pi_etaStar` (`cosh 2πη_* = 1 + F'(v_x)²`) and
  `etaStar_lt_quarter` (`η_* < π⁻¹ arsinh(1/√2) < 1/4`).

Everything is proved unconditionally, using Lemma `SD_0` (`edgePhi0Blaschke_deriv_edge`,
`phiZeta_half_I`) from the existing Paper II lane.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Saddle

/-! ### 1. The edge abscissa `v_x = F⁻¹(x)` -/

/-- `v_x = π⁻¹ arccosh(sinh πx)`, the inverse `F⁻¹(x)` of `F(v) = π⁻¹ arsinh(cosh πv)`. -/
noncomputable def vTip (x : ℝ) : ℝ := arccoshR (Real.sinh (π * x)) / π

lemma one_le_sinh_pi_mul {x : ℝ} (hx : xiStar ≤ x) : 1 ≤ Real.sinh (π * x) := by
  rw [← sinh_pi_mul_xiStar]
  exact Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left hx Real.pi_pos.le)

lemma vTip_eq_rhoU {x : ℝ} (hx : xiStar ≤ x) : vTip x = 3 / 4 * rhoU x := by
  rw [rhoU_eq_of_ge hx]
  unfold vTip
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  field_simp

lemma vTip_xiStar : vTip xiStar = 0 := by
  rw [vTip_eq_rhoU le_rfl, rhoU_xiStar, mul_zero]

lemma vTip_nonneg {x : ℝ} (hx : xiStar ≤ x) : 0 ≤ vTip x := by
  rw [vTip_eq_rhoU hx]
  exact mul_nonneg (by norm_num) (rhoU_nonneg x)

lemma vTip_pos {x : ℝ} (hx : xiStar < x) : 0 < vTip x := by
  rw [vTip_eq_rhoU hx.le]
  exact mul_pos (by norm_num) (rhoU_pos hx)

lemma cosh_pi_mul_vTip {x : ℝ} (hx : xiStar ≤ x) : Real.cosh (π * vTip x) = Real.sinh (π * x) := by
  unfold vTip
  rw [mul_div_cancel₀ _ Real.pi_pos.ne']
  exact cosh_arccoshR (one_le_sinh_pi_mul hx)

/-- `F(v_x) = x`. -/
lemma edgeF_vTip {x : ℝ} (hx : xiStar ≤ x) : edgeF (vTip x) = x := by
  unfold edgeF
  rw [cosh_pi_mul_vTip hx, Real.arsinh_sinh]
  field_simp

lemma continuousOn_vTip : ContinuousOn vTip (Ici xiStar) := by
  have h : ContinuousOn (fun x => 3 / 4 * rhoU x) (Ici xiStar) :=
    continuousOn_const.mul continuousOn_rhoU
  exact h.congr fun x hx => vTip_eq_rhoU hx

lemma hasDerivAt_vTip {x : ℝ} (hx : xiStar < x) : HasDerivAt vTip (3 / 4 * rhoUDeriv x) x := by
  have h := (hasDerivAt_rhoU hx).const_mul (3 / 4 : ℝ)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with t ht
  exact vTip_eq_rhoU (le_of_lt ht)

/-! ### 2. The identity `Im Φ₀(b_x) + (4π/3) x v_x = 2π N(x)` -/

/-- The upper-edge point `b_x = v_x + i/2`. -/
noncomputable def bTip (x : ℝ) : ℂ := (vTip x : ℂ) + Complex.I / 2

lemma bTip_im (x : ℝ) : (bTip x).im = 1 / 2 := by simp [bTip]

lemma bTip_mem_combNMid (x : ℝ) : bTip x ∈ combNMid := by
  change |(bTip x).im - 1 / 2| < 17 / 64
  rw [bTip_im]; norm_num

lemma continuousOn_bTip : ContinuousOn bTip (Ici xiStar) := by
  unfold bTip
  exact (Complex.continuous_ofReal.comp_continuousOn continuousOn_vTip).add continuousOn_const

lemma hasDerivAt_bTip {x : ℝ} (hx : xiStar < x) :
    HasDerivAt bTip (((3 / 4 * rhoUDeriv x : ℝ)) : ℂ) x := by
  unfold bTip
  exact ((hasDerivAt_vTip hx).ofReal_comp).add_const _

/-- Defect function whose vanishing is `cts:pl-id`. -/
private noncomputable def phaseLockDefect (x : ℝ) : ℝ :=
  (edgePhi0Blaschke (bTip x)).im + 4 * π / 3 * x * vTip x - 2 * π * cumulN x

private lemma continuousOn_phaseLockDefect : ContinuousOn phaseLockDefect (Ici xiStar) := by
  have hΦ : ContinuousOn (fun x => edgePhi0Blaschke (bTip x)) (Ici xiStar) := by
    intro y hy
    have hc : ContinuousAt edgePhi0Blaschke (bTip y) :=
      ((edgePhi0Blaschke_analyticOnNhd (bTip y) (bTip_mem_combNMid y)).continuousAt)
    exact hc.comp_continuousWithinAt (continuousOn_bTip y hy)
  unfold phaseLockDefect
  exact (Complex.continuous_im.comp_continuousOn hΦ).add
    ((continuousOn_const.mul continuousOn_id).mul continuousOn_vTip) |>.sub
    (continuousOn_const.mul continuousOn_cumulN)

private lemma hasDerivAt_phaseLockDefect {x : ℝ} (hx : xiStar < x) :
    HasDerivAt phaseLockDefect 0 x := by
  have hb := hasDerivAt_bTip hx
  have hΦ : HasDerivAt edgePhi0Blaschke (-(4 * (π : ℂ) * Complex.I / 3) * (x : ℂ)) (bTip x) := by
    have hd : HasDerivAt edgePhi0Blaschke (deriv edgePhi0Blaschke (bTip x)) (bTip x) :=
      ((edgePhi0Blaschke_analyticOnNhd (bTip x) (bTip_mem_combNMid x)).differentiableAt).hasDerivAt
    have h2 : deriv edgePhi0Blaschke (bTip x) =
        -(4 * (π : ℂ) * Complex.I / 3) * (x : ℂ) := by
      have := edgePhi0Blaschke_deriv_edge (vTip x)
      rw [edgeF_vTip hx.le] at this
      exact this
    rwa [h2] at hd
  have hcomp := hΦ.scomp x hb
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hcomp
  have hv := hasDerivAt_vTip hx
  have hN := hasDerivAt_cumulN hx
  have hxv : HasDerivAt (fun y : ℝ => 4 * π / 3 * y * vTip y)
      (4 * π / 3 * 1 * vTip x + 4 * π / 3 * x * (3 / 4 * rhoUDeriv x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => 4 * π / 3 * y) (4 * π / 3 * 1) x :=
      (hasDerivAt_id x).const_mul _
    exact h1.mul hv
  have hsum := (him.add hxv).sub (hN.const_mul (2 * π))
  refine hsum.congr_deriv ?_
  have hvx : vTip x = 3 / 4 * rhoU x := vTip_eq_rhoU hx.le
  simp only [Complex.imCLM_apply, smul_eq_mul]
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  simp only [Complex.mul_im, Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  rw [hvx]
  ring

/-- **`cts:phaselock`, identity (`cts:pl-id`).** For every `x ≥ ξ_*`,
`Im Φ₀(b_x) + (4π/3) x v_x = 2π N(x)` with zero additive constant. -/
theorem phaseLock_identity {x : ℝ} (hx : xiStar ≤ x) :
    (edgePhi0Blaschke (bTip x)).im + 4 * π / 3 * x * vTip x = 2 * π * cumulN x := by
  have h0 : phaseLockDefect xiStar = 0 := by
    have hb : bTip xiStar = Complex.I / 2 := by simp [bTip, vTip_xiStar]
    unfold phaseLockDefect
    rw [hb, vTip_xiStar, cumulN_xiStar]
    have : edgePhi0Blaschke (Complex.I / 2) = 0 := by
      unfold edgePhi0Blaschke
      simp [phiZeta_half_I]
    simp [this]
  rcases hx.eq_or_lt with h | h
  · rw [← h]
    have := h0
    unfold phaseLockDefect at this
    linarith
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope phaseLockDefect (fun _ => (0 : ℝ)) h
      ((continuousOn_phaseLockDefect).mono (Icc_subset_Ici_self))
      (fun y hy => hasDerivAt_phaseLockDefect hy.1)
    have h1 : phaseLockDefect x = 0 := by
      have hne : x - xiStar ≠ 0 := (sub_pos.mpr h).ne'
      rw [h0] at hc'
      field_simp at hc'
      linarith
    unfold phaseLockDefect at h1
    linarith

/-! ### 3. The absent-charge and Hankel-prefactor phase (`cts:dth0`) -/

/-- `ψ(x) = arctan(sinh(π v_x)/√2)` (the phase of `-T_{ξ_*}(b_x)` is `-2ψ`). -/
noncomputable def psiTip (x : ℝ) : ℝ := Real.arctan (Real.sinh (π * vTip x) / √2)

lemma psiTip_pos {x : ℝ} (hx : xiStar < x) : 0 < psiTip x := by
  unfold psiTip
  apply Real.arctan_pos.mpr
  have : 0 < Real.sinh (π * vTip x) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos (vTip_pos hx))
  positivity

lemma psiTip_lt (x : ℝ) : psiTip x < π / 2 := Real.arctan_lt_pi_div_two _

lemma cosh_pi_xiStar : Real.cosh (π * xiStar) = √2 := by
  have h := Real.cosh_sq (π * xiStar)
  rw [sinh_pi_mul_xiStar] at h
  rw [← Real.sqrt_sq (Real.cosh_pos (π * xiStar)).le, h]
  norm_num

/-- `tanh A tanh B = (cosh(A+B) - cosh(A-B)) / (cosh(A+B) + cosh(A-B))`. -/
lemma tanh_mul_tanh_eq {A B : ℂ} (h : Complex.cosh (A + B) + Complex.cosh (A - B) ≠ 0) :
    Complex.tanh A * Complex.tanh B =
      (Complex.cosh (A + B) - Complex.cosh (A - B)) / (Complex.cosh (A + B) + Complex.cosh (A - B)) := by
  have hs : Complex.cosh (A + B) + Complex.cosh (A - B) = 2 * (Complex.cosh A * Complex.cosh B) := by
    rw [Complex.cosh_add, Complex.cosh_sub]; ring
  have hd : Complex.cosh (A + B) - Complex.cosh (A - B) = 2 * (Complex.sinh A * Complex.sinh B) := by
    rw [Complex.cosh_add, Complex.cosh_sub]; ring
  rw [hs] at h ⊢
  rw [hd]
  have h' : Complex.cosh A * Complex.cosh B ≠ 0 := right_ne_zero_of_mul h
  have hA : Complex.cosh A ≠ 0 := left_ne_zero_of_mul h'
  have hB : Complex.cosh B ≠ 0 := right_ne_zero_of_mul h'
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.tanh_eq_sinh_div_cosh]
  field_simp

/-- `cosh(π b_x) = i sinh(π v_x)`. -/
lemma cosh_pi_mul_bTip (x : ℝ) :
    Complex.cosh ((π : ℂ) * bTip x) = Complex.I * (Real.sinh (π * vTip x) : ℂ) := by
  have h : (π : ℂ) * bTip x = ((π * vTip x : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I := by
    unfold bTip; push_cast; ring
  rw [h, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  push_cast
  ring

/-- `-T_{ξ_*}(b_x) = (√2 - i sinh πv_x)/(√2 + i sinh πv_x)`. -/
lemma negBlaschkeT_tip_eq_div (x : ℝ) :
    -(blaschkeT (xiStar : ℂ) (bTip x)) =
      (((√2 : ℝ) : ℂ) - Complex.I * (Real.sinh (π * vTip x) : ℂ)) /
        (((√2 : ℝ) : ℂ) + Complex.I * (Real.sinh (π * vTip x) : ℂ)) := by
  set S : ℝ := Real.sinh (π * vTip x) with hS
  have hcξ : Complex.cosh ((π : ℂ) * (xiStar : ℂ)) = ((√2 : ℝ) : ℂ) := by
    have h1 : ((π * xiStar : ℝ) : ℂ) = (π : ℂ) * (xiStar : ℂ) := by push_cast; rfl
    rw [← h1, ← Complex.ofReal_cosh, cosh_pi_xiStar]
  have hsum : (π : ℂ) * (bTip x - (xiStar : ℂ)) / 2 + (π : ℂ) * (bTip x + (xiStar : ℂ)) / 2 =
      (π : ℂ) * bTip x := by ring
  have hdiff : (π : ℂ) * (bTip x - (xiStar : ℂ)) / 2 - (π : ℂ) * (bTip x + (xiStar : ℂ)) / 2 =
      -((π : ℂ) * (xiStar : ℂ)) := by ring
  have hne : Complex.I * (S : ℂ) + ((√2 : ℝ) : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  unfold blaschkeT
  rw [tanh_mul_tanh_eq (by rw [hsum, hdiff, Complex.cosh_neg, hcξ, cosh_pi_mul_bTip]; exact hne),
    hsum, hdiff, Complex.cosh_neg, hcξ, cosh_pi_mul_bTip, neg_div', add_comm (Complex.I * (S : ℂ))]
  rw [← hS]
  ring

/-- `-T_{ξ_*}(b_x) = e^{-2iψ(x)}` (`cts:dth0`, first step). -/
theorem negBlaschkeT_tip_eq_exp (x : ℝ) :
    -(blaschkeT (xiStar : ℂ) (bTip x)) = Complex.exp (-((2 * psiTip x : ℝ) : ℂ) * Complex.I) := by
  rw [negBlaschkeT_tip_eq_div]
  set S : ℝ := Real.sinh (π * vTip x) with hS
  set ρ : ℝ := √(2 + S ^ 2) with hρ
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr (by positivity)
  have hρ2 : ρ ^ 2 = 2 + S ^ 2 := Real.sq_sqrt (by positivity)
  have hsq : √(1 + (S / √2) ^ 2) = ρ / √2 := by
    have : 1 + (S / √2) ^ 2 = (2 + S ^ 2) / 2 := by rw [div_pow, hu]; ring
    rw [this, Real.sqrt_div (by positivity)]
  have hcos : Real.cos (psiTip x) = √2 / ρ := by
    unfold psiTip; rw [Real.cos_arctan, hsq]; field_simp
  have hsin : Real.sin (psiTip x) = S / ρ := by
    unfold psiTip; rw [Real.sin_arctan, hsq]; field_simp; rfl
  have hE : Complex.exp ((psiTip x : ℂ) * Complex.I) =
      (((√2 : ℝ) : ℂ) + Complex.I * (S : ℂ)) / (ρ : ℂ) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]
    have : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
    push_cast
    ring
  have hexp : Complex.exp (-((2 * psiTip x : ℝ) : ℂ) * Complex.I) =
      (Complex.exp ((psiTip x : ℂ) * Complex.I) * Complex.exp ((psiTip x : ℂ) * Complex.I))⁻¹ := by
    rw [← Complex.exp_add, ← Complex.exp_neg]
    congr 1; push_cast; ring
  rw [hexp, hE]
  have hρc : (ρ : ℂ) ^ 2 = 2 + (S : ℂ) ^ 2 := by exact_mod_cast hρ2
  have huc : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast hu
  have hne : (((√2 : ℝ) : ℂ) + Complex.I * (S : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hne2 : (((√2 : ℝ) : ℂ) - Complex.I * (S : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hρne : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  field_simp
  have hI := Complex.I_sq
  linear_combination (-(1 : ℂ)) * hρc + (-(S : ℂ) ^ 2) * hI + (1 : ℂ) * huc

lemma norm_bTip_sq (x : ℝ) : ‖bTip x‖ ^ 2 = vTip x ^ 2 + 1 / 4 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [bTip]
  ring

/-- `b_x = |b_x| (cos θ + i sin θ)` with `θ = arctan(1/(2 v_x))`. -/
lemma bTip_eq_polar {x : ℝ} (hx : xiStar < x) :
    bTip x = ((‖bTip x‖ : ℝ) : ℂ) *
      (Complex.cos ((Real.arctan (1 / (2 * vTip x)) : ℝ) : ℂ) +
        Complex.sin ((Real.arctan (1 / (2 * vTip x)) : ℝ) : ℂ) * Complex.I) := by
  have hv := vTip_pos hx
  set v := vTip x with hvdef
  set r := ‖bTip x‖ with hr
  have hr2 : r ^ 2 = v ^ 2 + 1 / 4 := norm_bTip_sq x
  have hr0 : 0 < r := by
    have : 0 < r ^ 2 := by rw [hr2]; positivity
    exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at this; simp at this)
  have hsq : √(1 + (1 / (2 * v)) ^ 2) = r / v := by
    have : 1 + (1 / (2 * v)) ^ 2 = (r / v) ^ 2 := by
      rw [div_pow r v 2, hr2]; field_simp; ring
    rw [this, Real.sqrt_sq (by positivity)]
  have hcos : Real.cos (Real.arctan (1 / (2 * v))) = v / r := by
    rw [Real.cos_arctan, hsq]; field_simp
  have hsin : Real.sin (Real.arctan (1 / (2 * v))) = 1 / (2 * r) := by
    rw [Real.sin_arctan, hsq]; field_simp
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]
  have : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  unfold bTip
  push_cast
  rw [← hvdef]
  field_simp

/-- `b_x^{1/2} = |b_x|^{1/2} e^{iθ/2}` (principal branch). -/
lemma bTip_cpow_half {x : ℝ} (hx : xiStar < x) :
    (bTip x) ^ (1 / 2 : ℂ) = ((√‖bTip x‖ : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((Real.arctan (1 / (2 * vTip x)) / 2 : ℝ) : ℂ)) := by
  have hθ0 : 0 < Real.arctan (1 / (2 * vTip x)) :=
    Real.arctan_pos.mpr (by have := vTip_pos hx; positivity)
  have hθ1 := Real.arctan_lt_pi_div_two (1 / (2 * vTip x))
  have hr0 : 0 < ‖bTip x‖ := by
    have : 0 < ‖bTip x‖ ^ 2 := by rw [norm_bTip_sq]; have := vTip_pos hx; positivity
    exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at this; simp at this)
  have hne : bTip x ≠ 0 := norm_pos_iff.mp hr0
  have harg : Complex.arg (bTip x) = Real.arctan (1 / (2 * vTip x)) := by
    conv_lhs => rw [bTip_eq_polar hx]
    exact Complex.arg_mul_cos_add_sin_mul_I hr0 ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [Complex.cpow_def_of_ne_zero hne, Complex.log, harg, add_mul, Complex.exp_add]
  congr 1
  · have h : ((Real.log ‖bTip x‖ : ℝ) : ℂ) * (1 / 2 : ℂ) = ((Real.log ‖bTip x‖ * (1 / 2) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hr0, Real.sqrt_eq_rpow]
  · congr 1; push_cast; ring

/-- **`cts:phaselock`, phase formula (`cts:dth0`).** For `x > ξ_*`,
`(-T_{ξ_*}(b_x))^{-3/2} b_x^{1/2} = |b_x|^{1/2} exp(i Δθ₀(x))` with
`Δθ₀(x) = 3ψ(x) + ½ arctan(1/(2 v_x))` (principal branches; the `-3/2` power is the one continuous
from `v_x = 0`). -/
theorem absentCharge_phase {x : ℝ} (hx : xiStar < x) :
    (-(blaschkeT (xiStar : ℂ) (bTip x))) ^ (-(3 / 2 : ℂ)) * (bTip x) ^ (1 / 2 : ℂ) =
      ((√‖bTip x‖ : ℝ) : ℂ) * Complex.exp (Complex.I *
        ((3 * psiTip x + 1 / 2 * Real.arctan (1 / (2 * vTip x)) : ℝ) : ℂ)) := by
  have hψ0 := psiTip_pos hx
  have hψ1 := psiTip_lt x
  rw [negBlaschkeT_tip_eq_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp; linarith [Real.pi_pos]) (by simp; linarith [Real.pi_pos]),
    bTip_cpow_half hx]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ### 4. The slit parametrisation `z = iy ↔ x` and the detuning `η_*` (`cts:s3`, `cts:eta-opt`) -/

/-- Slit parametrisation (`cts:s3`): if `y ∈ (0,1)` and `cosh(πx) = √2 (1+y²)/(1-y²)` then
`sinh(π v_x) = 2√2 y/(1-y²)`. -/
lemma sinh_pi_vTip_eq {x y : ℝ} (hx : xiStar < x) (hy0 : 0 < y) (hy1 : y < 1)
    (hxy : Real.cosh (π * x) = √2 * (1 + y ^ 2) / (1 - y ^ 2)) :
    Real.sinh (π * vTip x) = 2 * √2 * y / (1 - y ^ 2) := by
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith only [hy0, hy1]
  have hS0 : 0 < Real.sinh (π * vTip x) :=
    Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos (vTip_pos hx))
  have hS2 : Real.sinh (π * vTip x) ^ 2 = Real.cosh (π * x) ^ 2 - 2 := by
    have h1 := Real.cosh_sq (π * vTip x)
    have h2 := Real.cosh_sq (π * x)
    rw [cosh_pi_mul_vTip hx.le] at h1
    nlinarith only [h1, h2]
  have hT0 : 0 ≤ 2 * √2 * y / (1 - y ^ 2) := by positivity
  rw [← sq_eq_sq₀ hS0.le hT0, hS2, hxy, div_pow, div_pow, mul_pow, mul_pow, hu]
  field_simp
  linear_combination (-2 * y ^ 2) * hu

/-- `ψ(x) = 2 arctan y` for the slit parametrisation (`e^{-iψ} = σ(iy)`, `cts:sigma`). -/
theorem psiTip_eq_two_arctan {x y : ℝ} (hx : xiStar < x) (hy0 : 0 < y) (hy1 : y < 1)
    (hxy : Real.cosh (π * x) = √2 * (1 + y ^ 2) / (1 - y ^ 2)) :
    psiTip x = 2 * Real.arctan y := by
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith only [hy0, hy1]
  unfold psiTip
  rw [sinh_pi_vTip_eq hx hy0 hy1 hxy,
    show 2 * √2 * y / (1 - y ^ 2) / √2 = 2 * y / (1 - y ^ 2) by field_simp]
  have h : y * y < 1 := by nlinarith only [hy0, hy1]
  have := Real.arctan_add h
  rw [show 2 * y / (1 - y ^ 2) = (y + y) / (1 - y * y) by ring, ← this]
  ring

/-- `F'(v_x) = 2y/(1+y²)` for the slit parametrisation (`cts:s3`). -/
theorem edgeF'_vTip_eq {x y : ℝ} (hx : xiStar < x) (hy0 : 0 < y) (hy1 : y < 1)
    (hxy : Real.cosh (π * x) = √2 * (1 + y ^ 2) / (1 - y ^ 2)) :
    edgeF' (vTip x) = 2 * y / (1 + y ^ 2) := by
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith only [hy0, hy1]
  unfold edgeF'
  have hsq : √(1 + Real.cosh (π * vTip x) ^ 2) = Real.cosh (π * x) := by
    rw [cosh_pi_mul_vTip hx.le]
    have := Real.cosh_sq (π * x)
    rw [show 1 + Real.sinh (π * x) ^ 2 = Real.cosh (π * x) ^ 2 by linarith]
    exact Real.sqrt_sq (Real.cosh_pos _).le
  rw [hsq, sinh_pi_vTip_eq hx hy0 hy1 hxy, hxy]
  field_simp

/-- The optimal detuning `η_*(x)`: `sinh(π η_*) = F'(v_x)/√2` (`cts:eta-opt`). -/
noncomputable def etaStar (x : ℝ) : ℝ := Real.arsinh (edgeF' (vTip x) / √2) / π

/-- `cosh(2π η_*(x)) = 1 + F'(v_x)²` (`cts:eta-opt`). -/
theorem cosh_two_pi_etaStar (x : ℝ) :
    Real.cosh (2 * π * etaStar x) = 1 + edgeF' (vTip x) ^ 2 := by
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have h : π * etaStar x = Real.arsinh (edgeF' (vTip x) / √2) := by
    unfold etaStar; field_simp
  rw [show 2 * π * etaStar x = 2 * (π * etaStar x) by ring, Real.cosh_two_mul, h]
  have := Real.cosh_sq (Real.arsinh (edgeF' (vTip x) / √2))
  rw [Real.sinh_arsinh] at this ⊢
  rw [this, div_pow, hu]
  ring

lemma arsinh_inv_sqrt_two_lt : Real.arsinh (1 / √2) < π / 4 := by
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : 1 / √2 < π / 4 := by
    rw [div_lt_div_iff₀ hu0 (by norm_num)]
    nlinarith only [Real.pi_gt_d2, hu, hu0]
  have h2 : π / 4 ≤ Real.sinh (π / 4) := Real.self_le_sinh_iff.mpr (by positivity)
  rw [← Real.sinh_lt_sinh, Real.sinh_arsinh]
  linarith

/-- `sup_x η_*(x) = π⁻¹ arsinh(1/√2) < 1/4` (`cts:eta-opt`): `η_*(x) < π⁻¹ arsinh(1/√2) < 1/4`
for every `x`. -/
theorem etaStar_lt_quarter (x : ℝ) : etaStar x < Real.arsinh (1 / √2) / π ∧
    Real.arsinh (1 / √2) / π < 1 / 4 := by
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_⟩
  · unfold etaStar
    apply div_lt_div_of_pos_right _ Real.pi_pos
    apply Real.arsinh_lt_arsinh.mpr
    rw [div_lt_div_iff_of_pos_right hu0]
    unfold edgeF'
    have h1 := Real.cosh_sq (π * vTip x)
    rw [div_lt_one (Real.sqrt_pos.mpr (by positivity))]
    apply Real.lt_sqrt_of_sq_lt
    nlinarith only [h1]
  · rw [div_lt_iff₀ Real.pi_pos]
    linarith [arsinh_inv_sqrt_two_lt]

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.phaseLock_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.phaseLock_identity

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.negBlaschkeT_tip_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.negBlaschkeT_tip_eq_exp

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.absentCharge_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.absentCharge_phase

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.psiTip_eq_two_arctan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.psiTip_eq_two_arctan

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.edgeF'_vTip_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.edgeF'_vTip_eq

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.cosh_two_pi_etaStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.cosh_two_pi_etaStar

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.etaStar_lt_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.etaStar_lt_quarter
