module

public import FormalResearch.ModularBootstrap.Blowup.TipMap
public import Mathlib.Analysis.SpecialFunctions.Bessel

/-!
# Blow-up of the potential and complex weight: Lemmas T2 and T3 (`blowup_limit.tex`)

Formalizes **Lemma T2** (blow-up of the strip harmonic majorant `U + Re L` at the fold tip)
and **Lemma T3** (complex-argument Bessel `I_0` asymptotic for `V(c' b^2 / 3)` and `W(b)`)
from `CFT/modular_bootstrap/paper/blowup_limit.tex`:

* `ofReal_mul_cpow`: `(a : ℂ) * z ^ w` identity `((a : ℂ) * z) ^ w = (a : ℂ) ^ w * z ^ w`
  for `0 < a : ℝ` and arbitrary `z : ℂ`.
* `LemmaGPotentialInput`: named analytic input encapsulating the Lemma G harmonic-majorant
  formula `U(b) + Re L(b) = Re(-K (ξ_* - b)^{3/2} A(b - ξ_*))` near `ξ_*` (with
  `lemmaGPotentialInput_nonvacuous`). Not proved here because the slit-strip harmonic-measure
  integral representation of `U` on `ℂ` lives upstream in Lemma G (`lower_o1_two_edge.tex`).
* `lemma_T2`: **Lemma T2** (`c'(U + Re L)(ξ_* + ε ζ) = Re(-K(-ζ)^{3/2} A(ε ζ)) = tipH ζ + O(ε|ζ|^{5/2})`).
* `KalphaC`, `V_C`, `besselI0C`, `W_C`: entire weight `V(t) = K_a(t) - 2 K_{a-1}(t) + K_{a-2}(t)`
  defined via Mathlib's `Complex.regularizedHGFun 0 {1}` (`I_0(z) = J_0(iz)`), with
  `V_C_entire` and `W_C_entire` proved unconditionally.
* `BesselI0Asymptotic`: classical Hankel/Laplace large-argument asymptotic for `I_0(z)` in the
  sector `Re z ≥ 2, |Im z| ≤ Re z` (with `besselI0Asymptotic_nonvacuous`), not proved here.
* `lemma_T3`, `lemma_T3_W_bound`: **Lemma T3** for `V_C(c' b^2 / 3)` and `W_C c' b`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap

/-! ### Helper: `((a : ℂ) * z) ^ w = (a : ℂ) ^ w * z ^ w` for `0 < a : ℝ` -/

lemma ofReal_mul_cpow {a : ℝ} (ha : 0 < a) (z w : ℂ) :
    ((a : ℂ) * z) ^ w = (a : ℂ) ^ w * z ^ w := by
  rcases eq_or_ne z 0 with rfl | hz
  · rcases eq_or_ne w 0 with rfl | hw
    · simp
    · simp [Complex.zero_cpow hw]
  have ha_c : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have harg : (a : ℂ).arg + z.arg ∈ Ioc (-π) π := by
    rw [Complex.arg_ofReal_of_nonneg ha.le, zero_add]
    exact ⟨Complex.neg_pi_lt_arg z, Complex.arg_le_pi z⟩
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero ha_c hz),
    Complex.log_mul ha_c hz harg, add_mul, Complex.exp_add,
    ← Complex.cpow_def_of_ne_zero ha_c, ← Complex.cpow_def_of_ne_zero hz]

/-! ### Section 1: Lemma G potential input and Lemma T2 (blow-up of the potential) -/

/-- Named upstream input for **Lemma T2** (`lower_o1_two_edge.tex`, Lemma G, eq. (239)-(266) and
`blowup_limit.tex`, Lemma `bl:T2`): near `ξ_*`, the slit-strip harmonic majorant `U` satisfies
`U(b) + Re L(b) = Re(-K (ξ_* - b)^{3/2} A(b - ξ_*))` with `A` analytic near `0`, real on `ℝ`,
and `A(0) = 1`.
Not proved here because `lower_o1_two_edge.tex`'s conformal harmonic-measure identity for `U` on `ℂ`
is upstream of `Blowup/`. -/
structure LemmaGPotentialInput where
  U : ℂ → ℝ
  A : ℂ → ℂ
  r_A : ℝ
  hr_A_pos : 0 < r_A
  hA_an : AnalyticOnNhd ℂ A (ball 0 r_A)
  hA_0 : A 0 = 1
  hA_real : ∀ x : ℝ, |x| < r_A → (A (x : ℂ)).im = 0
  U_add_L_near_tip : ∀ b ∈ ball (xiStar : ℂ) r_A, ¬ (b.im = 0 ∧ xiStar ≤ b.re) →
    U b + (tipL b).re = (-KTip * ((xiStar : ℂ) - b) ^ (3 / 2 : ℂ) * A (b - (xiStar : ℂ))).re

/-- Non-vacuity witness for `LemmaGPotentialInput`. -/
theorem lemmaGPotentialInput_nonvacuous : Nonempty LemmaGPotentialInput :=
  ⟨{
    U := fun b => (-KTip * ((xiStar : ℂ) - b) ^ (3 / 2 : ℂ)).re - (tipL b).re
    A := fun _ => 1
    r_A := 1
    hr_A_pos := one_pos
    hA_an := fun _ _ => analyticAt_const
    hA_0 := rfl
    hA_real := fun _ _ => Complex.one_im
    U_add_L_near_tip := fun _ _ _ => by simp
  }⟩

/-- **Lemma T2** (`blowup_limit.tex`, Lemma `bl:T2`): blow-up of the slit-strip potential
at the fold tip. Proved from `LemmaGPotentialInput` via `c' ε^{3/2} = 1` and the mean-value
bound on `A(ε ζ) - 1`. -/
theorem lemma_T2 (pg : LemmaGPotentialInput) :
    ∃ ρ₂ C_T2 : ℝ, 0 < ρ₂ ∧ 0 ≤ C_T2 ∧
      ∀ {c' : ℝ} {ζ : ℂ}, 0 < c' → ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re) →
        tipEps c' * ‖ζ‖ ≤ ρ₂ →
        let ε := tipEps c'
        c' * (pg.U (bScale c' ζ) + (tipL (bScale c' ζ)).re) =
          (-KTip * (-ζ) ^ (3 / 2 : ℂ) * pg.A ((ε : ℂ) * ζ)).re ∧
        |c' * (pg.U (bScale c' ζ) + (tipL (bScale c' ζ)).re) - tipH ζ| ≤
          C_T2 * ε * ‖ζ‖ ^ (5 / 2 : ℝ) := by
  let ρ₂ : ℝ := pg.r_A / 2
  have hρ₂_pos : 0 < ρ₂ := by positivity [pg.hr_A_pos]
  have hcl_sub : closedBall (0 : ℂ) ρ₂ ⊆ ball 0 pg.r_A :=
    closedBall_subset_ball (by dsimp [ρ₂]; linarith [pg.hr_A_pos])
  obtain ⟨M_A, hM_A⟩ := (isCompact_closedBall (0 : ℂ) ρ₂).exists_bound_of_continuousOn
    (pg.hA_an.deriv.continuousOn.mono hcl_sub)
  let C_A : ℝ := max M_A 0
  have hCA_nn : 0 ≤ C_A := le_max_right _ _
  have hA'_bd : ∀ w ∈ closedBall (0 : ℂ) ρ₂, ‖deriv pg.A w‖ ≤ C_A := fun w hw =>
    (hM_A w hw).trans (le_max_left _ _)
  let C_T2 : ℝ := KTip * C_A
  refine ⟨ρ₂, C_T2, hρ₂_pos, mul_nonneg KTip_pos.le hCA_nn, ?_⟩
  intro c' ζ hc' hζ hεζ
  set ε := tipEps c'
  have hε_pos : 0 < ε := tipEps_pos hc'
  have hεζ_norm : ‖(ε : ℂ) * ζ‖ ≤ ρ₂ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε_pos]
    exact hεζ
  have hb_ball : bScale c' ζ ∈ ball (xiStar : ℂ) pg.r_A := by
    rw [mem_ball, dist_eq_norm]
    have hsub : bScale c' ζ - (xiStar : ℂ) = (ε : ℂ) * ζ := by unfold bScale; ring
    rw [hsub]
    exact hεζ_norm.trans_lt (by dsimp [ρ₂]; linarith [pg.hr_A_pos])
  have hb_slit : ¬ ((bScale c' ζ).im = 0 ∧ xiStar ≤ (bScale c' ζ).re) := by
    intro ⟨him, hre⟩
    apply hζ
    unfold bScale at him hre
    have him' : (0 : ℝ) + ε * ζ.im = 0 := by
      simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using him
    have hre' : xiStar + ε * ζ.re ≥ xiStar := by
      simpa [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] using hre
    have hzim : ζ.im = 0 := by
      have : ε * ζ.im = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hε_pos.ne'
    have hzre : 0 ≤ ζ.re := nonneg_of_mul_nonneg_right (by linarith) hε_pos
    exact ⟨hzim, hzre⟩
  have hU := pg.U_add_L_near_tip (bScale c' ζ) hb_ball hb_slit
  have hb_sub : bScale c' ζ - (xiStar : ℂ) = (ε : ℂ) * ζ := by unfold bScale; ring
  have hxi_sub : (xiStar : ℂ) - bScale c' ζ = (ε : ℂ) * (-ζ) := by unfold bScale; ring
  rw [hb_sub, hxi_sub] at hU
  have hpow : ((ε : ℂ) * (-ζ)) ^ (3 / 2 : ℂ) =
      ((ε ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (-ζ) ^ (3 / 2 : ℂ) := by
    rw [ofReal_mul_cpow hε_pos (-ζ) (3 / 2 : ℂ),
      show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hε_pos.le]
  have hscaled : c' * (pg.U (bScale c' ζ) + (tipL (bScale c' ζ)).re) =
      (-KTip * (-ζ) ^ (3 / 2 : ℂ) * pg.A ((ε : ℂ) * ζ)).re := by
    rw [hU, hpow]
    have hc_prod : (c' : ℂ) * ((ε ^ (3 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
      exact_mod_cast tipEps_mul_self_cube hc'
    have hmul_c : ((c' : ℝ) : ℂ) *
        (-(KTip : ℂ) * (((ε ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (-ζ) ^ (3 / 2 : ℂ)) * pg.A ((ε : ℂ) * ζ)) =
        -(KTip : ℂ) * (-ζ) ^ (3 / 2 : ℂ) * pg.A ((ε : ℂ) * ζ) := by
      calc ((c' : ℝ) : ℂ) *
            (-(KTip : ℂ) * (((ε ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (-ζ) ^ (3 / 2 : ℂ)) *
              pg.A ((ε : ℂ) * ζ))
          = -(((c' : ℂ) * ((ε ^ (3 / 2 : ℝ) : ℝ) : ℂ)) *
              ((KTip : ℂ) * (-ζ) ^ (3 / 2 : ℂ) * pg.A ((ε : ℂ) * ζ))) := by ring
        _ = -(KTip : ℂ) * (-ζ) ^ (3 / 2 : ℂ) * pg.A ((ε : ℂ) * ζ) := by
            rw [hc_prod, one_mul]; ring
    rw [← Complex.re_ofReal_mul, hmul_c]
  refine ⟨hscaled, ?_⟩
  rw [hscaled]
  unfold tipH
  have hdiff : (-KTip * (-ζ) ^ (3 / 2 : ℂ) * pg.A ((ε : ℂ) * ζ)).re -
      (-KTip * ((-ζ) ^ (3 / 2 : ℂ)).re) =
      (-KTip * (-ζ) ^ (3 / 2 : ℂ) * (pg.A ((ε : ℂ) * ζ) - 1)).re := by
    have h1 : -KTip * ((-ζ) ^ (3 / 2 : ℂ)).re = (-(KTip : ℂ) * (-ζ) ^ (3 / 2 : ℂ)).re := by
      have hsub : (-(KTip : ℂ) * (-ζ) ^ (3 / 2 : ℂ)) =
          ((-KTip : ℝ) : ℂ) * (-ζ) ^ (3 / 2 : ℂ) := by push_cast; ring
      rw [hsub, Complex.re_ofReal_mul]
    rw [h1, ← Complex.sub_re]
    congr 1; ring
  rw [hdiff]
  have hmvt : ‖pg.A ((ε : ℂ) * ζ) - 1‖ ≤ C_A * (ε * ‖ζ‖) := by
    have h0_cl : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ₂ := mem_closedBall_self hρ₂_pos.le
    have hw_cl : (ε : ℂ) * ζ ∈ closedBall (0 : ℂ) ρ₂ := by
      simpa [mem_closedBall, dist_zero_right] using hεζ_norm
    have hdiff_on : ∀ w ∈ closedBall (0 : ℂ) ρ₂, DifferentiableAt ℂ pg.A w := fun w hw =>
      (pg.hA_an w (hcl_sub hw)).differentiableAt
    have h := (convex_closedBall (0 : ℂ) ρ₂).norm_image_sub_le_of_norm_deriv_le
      hdiff_on hA'_bd h0_cl hw_cl
    rw [pg.hA_0, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε_pos] at h
    exact h
  have hnorm_cpow : ‖(-ζ) ^ (3 / 2 : ℂ)‖ = ‖ζ‖ ^ (3 / 2 : ℝ) := by
    rcases eq_or_ne ζ 0 with rfl | hζ_ne
    · simp [Complex.zero_cpow (by norm_num : (3 / 2 : ℂ) ≠ 0),
        Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    · have hne : -ζ ≠ 0 := neg_ne_zero.mpr hζ_ne
      have hexp : ‖(-ζ) ^ (3 / 2 : ℂ)‖ = Real.exp (Real.log ‖-ζ‖ * (3 / 2 : ℝ)) := by
        rw [Complex.cpow_def_of_ne_zero hne, Complex.norm_exp]
        congr 1
        have hre : (3 / 2 : ℂ).re = 3 / 2 := by norm_num
        have him : (3 / 2 : ℂ).im = 0 := by norm_num
        rw [Complex.mul_re, Complex.log_re, hre, him, mul_zero, sub_zero]
      rw [hexp, norm_neg, Real.rpow_def_of_pos (norm_pos_iff.mpr hζ_ne)]
  have hrpow_52 : ‖ζ‖ ^ (3 / 2 : ℝ) * ‖ζ‖ = ‖ζ‖ ^ (5 / 2 : ℝ) := by
    rcases eq_or_ne ζ 0 with rfl | hζ_ne
    · simp [Real.zero_rpow (by norm_num : (5 / 2 : ℝ) ≠ 0)]
    · rw [← Real.rpow_add_one (norm_pos_iff.mpr hζ_ne).ne',
        show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num]
  calc |(-KTip * (-ζ) ^ (3 / 2 : ℂ) * (pg.A ((ε : ℂ) * ζ) - 1)).re|
      ≤ ‖-KTip * (-ζ) ^ (3 / 2 : ℂ) * (pg.A ((ε : ℂ) * ζ) - 1)‖ := Complex.abs_re_le_norm _
    _ = KTip * ‖ζ‖ ^ (3 / 2 : ℝ) * ‖pg.A ((ε : ℂ) * ζ) - 1‖ := by
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos KTip_pos, hnorm_cpow]
    _ ≤ KTip * ‖ζ‖ ^ (3 / 2 : ℝ) * (C_A * (ε * ‖ζ‖)) :=
        mul_le_mul_of_nonneg_left hmvt
          (mul_nonneg KTip_pos.le (Real.rpow_nonneg (norm_nonneg _) _))
    _ = C_T2 * ε * (‖ζ‖ ^ (3 / 2 : ℝ) * ‖ζ‖) := by dsimp [C_T2]; ring
    _ = C_T2 * ε * ‖ζ‖ ^ (5 / 2 : ℝ) := by rw [hrpow_52]

/-! ### Section 2: Entire Bessel weight `K_α`, `V`, `W`, `I_0`, and Lemma T3 -/

/-- Entire kernel `K_α(t) = I_0(4π √(α t)) = ₀F₁(1; 4π^2 α t)`. -/
noncomputable def KalphaC (α t : ℂ) : ℂ :=
  Complex.regularizedHGFun 0 {(1 : ℂ)} (4 * (π : ℂ) ^ 2 * α * t)

/-- Entire modular bootstrap weight `V(t) = K_a(t) - 2 K_{a-1}(t) + K_{a-2}(t)` (`a = c'/12`). -/
noncomputable def V_C (c' t : ℂ) : ℂ :=
  KalphaC (c' / 12) t - 2 * KalphaC (c' / 12 - 1) t + KalphaC (c' / 12 - 2) t

/-- Complex modified Bessel function `I_0(z) = J_0(i z) = ₀F₁(1; z^2 / 4)`. -/
noncomputable def besselI0C (z : ℂ) : ℂ :=
  Complex.besselJ 0 (I * z)

/-- Rescaled tip weight `W(b) = ε (2c'/3) b V(c' b^2 / 3)` (`blowup_limit.tex`, §1). -/
noncomputable def W_C (c' : ℝ) (b : ℂ) : ℂ :=
  ((tipEps c' : ℝ) : ℂ) * ((2 * c' / 3 : ℝ) : ℂ) * b * V_C (c' : ℂ) ((c' : ℂ) * b ^ 2 / 3)

lemma besselI0C_eq_hgfun (z : ℂ) :
    besselI0C z = Complex.regularizedHGFun 0 {(1 : ℂ)} (z ^ 2 / 4) := by
  unfold besselI0C
  rw [Complex.besselJ_def]
  dsimp only
  rw [Complex.cpow_zero, one_mul, zero_add]
  congr 1
  rw [div_pow, mul_pow, Complex.I_sq]
  ring

lemma besselI0C_entire : Differentiable ℂ besselI0C := by
  have heq : besselI0C = fun z => Complex.regularizedHGFun 0 {(1 : ℂ)} (z ^ 2 / 4) :=
    funext besselI0C_eq_hgfun
  rw [heq]
  intro z
  exact (Complex.analyticAt_regularizedHGFun_zero _).differentiableAt.comp z
    (((differentiableAt_id).pow 2).div_const 4)

lemma KalphaC_entire (α : ℂ) : Differentiable ℂ (KalphaC α) := fun t => by
  unfold KalphaC
  exact (Complex.analyticAt_regularizedHGFun_zero _).differentiableAt.comp t
    (differentiableAt_const _ |>.mul differentiableAt_id)

lemma V_C_entire (c' : ℂ) : Differentiable ℂ (V_C c') :=
  ((KalphaC_entire _).sub ((KalphaC_entire _).const_mul 2)).add (KalphaC_entire _)

lemma W_C_entire (c' : ℝ) : Differentiable ℂ (W_C c') := by
  unfold W_C
  have h1 : Differentiable ℂ (fun b : ℂ =>
      ((tipEps c' : ℝ) : ℂ) * ((2 * c' / 3 : ℝ) : ℂ) * b) :=
    differentiable_const _ |>.mul differentiable_id
  have h2 : Differentiable ℂ (fun b : ℂ => V_C (c' : ℂ) ((c' : ℂ) * b ^ 2 / 3)) :=
    (V_C_entire (c' : ℂ)).comp (((differentiable_id.pow 2).const_mul _).div_const 3)
  exact h1.mul h2

lemma KalphaC_eq_besselI0C {α c' : ℝ} (hα : 0 ≤ α) (hc' : 0 ≤ c') (b : ℂ) :
    KalphaC (α : ℂ) ((c' : ℂ) * b ^ 2 / 3) =
      besselI0C (4 * (π : ℂ) * b * ((√(α * c' / 3) : ℝ) : ℂ)) := by
  rw [besselI0C_eq_hgfun]
  unfold KalphaC
  congr 1
  have hsq : ((√(α * c' / 3) : ℝ) : ℂ) ^ 2 = ((α * c' / 3 : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity)
  rw [mul_pow, hsq]
  push_cast
  ring

/-- Classical large-argument Hankel/Laplace asymptotic for `I_0(z)` (`blowup_limit.tex`, Lemma `bl:T3`
and `lower_o1_two_edge.tex`, Lemma B(c)): uniformly for `Re z ≥ 2` and `|Im z| ≤ Re z`,
`I_0(z) = as(z) (1 + O(1/|z|))`. Not proved here because Laplace's method / steepest descent
for Bessel integrals is a classical analytic input lacking in Mathlib. -/
def BesselI0Asymptotic : Prop :=
  ∃ C_I0 : ℝ, 0 ≤ C_I0 ∧
    ∀ z : ℂ, 2 ≤ z.re → |z.im| ≤ z.re →
      ‖besselI0C z - asC z‖ ≤ (C_I0 / ‖z‖) * ‖asC z‖

/-- Specification consistency for `BesselI0Asymptotic`: `asC` itself satisfies the bound with `C = 0`. -/
theorem besselI0Asymptotic_nonvacuous :
    ∃ (I0approx : ℂ → ℂ) (C_I0 : ℝ), 0 ≤ C_I0 ∧
      ∀ z : ℂ, 2 ≤ z.re → |z.im| ≤ z.re →
        ‖I0approx z - asC z‖ ≤ (C_I0 / ‖z‖) * ‖asC z‖ :=
  ⟨asC, 0, le_rfl, fun z _ _ => by simp⟩

private lemma sqrt_two_gt_1414_pw : (1.414 : ℝ) < √2 := by
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.414)]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

private lemma sqrt_two_lt_1415_pw : √2 < (1.415 : ℝ) := by
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.415)]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma xiStar_gt_028 : (0.28 : ℝ) < xiStar := by
  unfold xiStar
  rw [lt_div_iff₀ Real.pi_pos, ← Real.sinh_lt_sinh, Real.sinh_arsinh]
  have hpi : 0.28 * π < (0.88 : ℝ) := by nlinarith [Real.pi_lt_d4]
  have hmono : Real.sinh (0.28 * π) < Real.sinh 0.88 := Real.sinh_strictMono hpi
  have hexp_ub : Real.exp (0.88 : ℝ) ≤ 2.412 := by
    have h6 := Real.exp_bound' (x := (0.88 : ℝ)) (by norm_num) (by norm_num) (n := 6) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.factorial] at h6
    norm_num at h6 ⊢
    linarith
  have hexp_neg_lb : (0.414 : ℝ) ≤ Real.exp (-0.88) := by
    rw [Real.exp_neg]
    exact (le_inv_comm₀ (Real.exp_pos 0.88) (by norm_num)).mp (by linarith)
  have hsinh_lt : Real.sinh (0.88 : ℝ) < 1 := by
    rw [Real.sinh_eq]
    linarith
  exact hmono.trans hsinh_lt

lemma xiStar_lt_029 : xiStar < (0.29 : ℝ) := by
  unfold xiStar
  rw [div_lt_iff₀ Real.pi_pos, ← Real.sinh_lt_sinh, Real.sinh_arsinh]
  have hpi : (0.91 : ℝ) < 0.29 * π := by nlinarith [Real.pi_gt_d4]
  have hmono : Real.sinh (0.91 : ℝ) < Real.sinh (0.29 * π) := Real.sinh_strictMono hpi
  have hexp_lb : (2.47 : ℝ) ≤ Real.exp (0.91 : ℝ) := by
    have h5 := Real.sum_le_exp_of_nonneg (x := (0.91 : ℝ)) (by norm_num) 5
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.factorial] at h5
    norm_num at h5 ⊢
    linarith
  have hexp_neg_ub : Real.exp (-0.91 : ℝ) ≤ 0.41 := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos 0.91) (by norm_num)).mpr (by linarith)
  have hsinh_gt : (1 : ℝ) < Real.sinh (0.91 : ℝ) := by
    rw [Real.sinh_eq]
    linarith
  exact hsinh_gt.trans hmono

private lemma exp_neg_four_pi_xiStar :
    Complex.exp (-4 * (π : ℂ) * (xiStar : ℂ)) = (((√2 - 1) ^ 4 : ℝ) : ℂ) := by
  have hexp_real : Real.exp (-(π * xiStar)) = √2 - 1 := by
    have hsinh : Real.sinh (π * xiStar) = 1 := sinh_pi_mul_xiStar
    have hsq : Real.cosh (π * xiStar) = √2 := by
      have hid := Real.cosh_sq_sub_sinh_sq (π * xiStar)
      rw [hsinh, one_pow] at hid
      have hpos : 0 < Real.cosh (π * xiStar) := Real.cosh_pos _
      have h2 : Real.cosh (π * xiStar) ^ 2 = 2 := by linarith
      rw [← Real.sqrt_sq hpos.le, h2]
    have hsub : Real.cosh (π * xiStar) - Real.sinh (π * xiStar) = Real.exp (-(π * xiStar)) := by
      rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]; ring
    linarith
  have h4 : Real.exp (-4 * π * xiStar) = (Real.exp (-(π * xiStar))) ^ 4 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [show -4 * (π : ℂ) * (xiStar : ℂ) = ((-4 * π * xiStar : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, h4, hexp_real]

private lemma norm_exp_sub_one_le_of_re_nonpos {w : ℂ} (hw : w.re ≤ 0) :
    ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ := by
  by_cases h1 : ‖w‖ ≤ 1
  · exact Complex.norm_exp_sub_one_le h1
  · have hge : 1 ≤ ‖w‖ := le_of_not_ge h1
    have hexp_le : ‖Complex.exp w‖ ≤ 1 := by
      rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hw
    calc ‖Complex.exp w - 1‖ ≤ ‖Complex.exp w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith
      _ = 2 := by norm_num
      _ ≤ 2 * ‖w‖ := by linarith

/-- **Lemma T3** (`blowup_limit.tex`, Lemma `bl:T3`, first display): uniform complex asymptotic
for `V(c' b^2 / 3)` on `|b - ξ_*| ≤ 0.1`, `c' ≥ 39`, proved from `BesselI0Asymptotic`. -/
theorem lemma_T3 (hI0 : BesselI0Asymptotic) :
    ∃ C_V : ℝ, 0 ≤ C_V ∧
      ∀ {c' : ℝ} {b : ℂ}, 39 ≤ c' → b ∈ closedBall (xiStar : ℂ) 0.1 →
        ∃ ε_V : ℂ,
          V_C (c' : ℂ) ((c' : ℂ) * b ^ 2 / 3) =
            asC ((c' : ℂ) * tipL b) *
              ((1 - Complex.exp (-4 * (π : ℂ) * b)) ^ 2 + ε_V) ∧
          ‖ε_V‖ ≤ C_V / c' := by
  obtain ⟨C_I0, hCI0_nn, hI0_bd⟩ := hI0
  let C_j : ℝ := 12 * C_I0 + 400
  let C_V : ℝ := 4 * C_j
  refine ⟨C_V, by dsimp [C_V, C_j]; positivity, fun {c' b} hc' hb => ?_⟩
  have hc'_pos : 0 < c' := by linarith
  have hb_norm : ‖b - (xiStar : ℂ)‖ ≤ 0.1 := by
    simpa [dist_eq_norm] using mem_closedBall.mp hb
  have hdiff_re : |b.re - xiStar| ≤ 0.1 := by
    simpa [Complex.sub_re] using (Complex.abs_re_le_norm (b - (xiStar : ℂ))).trans hb_norm
  have hdiff_im : |b.im| ≤ 0.1 := by
    simpa [Complex.sub_im] using (Complex.abs_im_le_norm (b - (xiStar : ℂ))).trans hb_norm
  have hb_re_lo : (0.18 : ℝ) < b.re := by linarith [(abs_le.mp hdiff_re).1, xiStar_gt_028]
  have hb_re_hi : b.re < (0.39 : ℝ) := by linarith [(abs_le.mp hdiff_re).2, xiStar_lt_029]
  have hb_im_le_re : |b.im| ≤ b.re := by linarith
  have hb_norm_le : ‖b‖ ≤ 0.5 := by
    calc ‖b‖ ≤ |b.re| + |b.im| := Complex.norm_le_abs_re_add_abs_im b
      _ = b.re + |b.im| := by rw [abs_of_pos (by linarith)]
      _ ≤ 0.39 + 0.1 := by linarith
      _ ≤ 0.5 := by norm_num
  let z₀ : ℂ := (c' : ℂ) * tipL b
  have hz₀_eq : z₀ = ((c' * (2 * π / 3) : ℝ) : ℂ) * b := by
    dsimp [z₀]; unfold tipL; push_cast; ring
  have hc2pi3_pos : 0 < c' * (2 * π / 3) := by positivity
  have hz₀_re : z₀.re = (c' * (2 * π / 3)) * b.re := by
    rw [hz₀_eq, Complex.re_ofReal_mul]
  have hz₀_im : z₀.im = (c' * (2 * π / 3)) * b.im := by
    rw [hz₀_eq, Complex.im_ofReal_mul]
  have hz₀_norm_le : ‖z₀‖ ≤ 1.1 * c' := by
    rw [hz₀_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc2pi3_pos]
    have h2pi3_le : 2 * π / 3 ≤ 2.1 := by nlinarith [Real.pi_lt_d4]
    calc c' * (2 * π / 3) * ‖b‖ ≤ c' * 2.1 * 0.5 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2pi3_le hc'_pos.le) hb_norm_le (norm_nonneg _)
            (by positivity)
      _ ≤ 1.1 * c' := by linarith
  have hz₀_re_ge : 0.36 * c' ≤ z₀.re := by
    rw [hz₀_re]
    have h2pi3_ge : 2 ≤ 2 * π / 3 := by nlinarith [Real.pi_gt_d4]
    nlinarith
  have hz₀_ne : z₀ ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hz₀_re_ge; linarith
  have hpi_ne : (2 * (π : ℂ) * z₀) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) hz₀_ne
  have has0_ne : asC z₀ ≠ 0 := by
    unfold asC
    refine div_ne_zero (Complex.exp_ne_zero _) ?_
    exact (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi_ne))
  -- Core estimate for each `j ∈ {0, 1, 2}`:
  have hj_bound : ∀ j : ℕ, j ≤ 2 → ∃ err_j : ℂ,
      KalphaC ((c' / 12 - (j : ℝ) : ℝ) : ℂ) ((c' : ℂ) * b ^ 2 / 3) =
        asC z₀ * (Complex.exp (-4 * (π : ℂ) * (j : ℂ) * b) + err_j) ∧
      ‖err_j‖ ≤ C_j / c' := by
    intro j hj
    have hj_r : (j : ℝ) ≤ 2 := by exact_mod_cast hj
    have hα_pos : 0 < c' / 12 - (j : ℝ) := by linarith
    let r : ℝ := √(1 - 12 * (j : ℝ) / c')
    have hrad_ge : (1 : ℝ) / 3 ≤ 1 - 12 * (j : ℝ) / c' := by
      have h1 : 12 * (j : ℝ) / c' ≤ 24 / 39 := by
        calc 12 * (j : ℝ) / c' ≤ 24 / c' := by gcongr; linarith
          _ ≤ 24 / 39 := by gcongr
      linarith
    have hrad_le : 1 - 12 * (j : ℝ) / c' ≤ 1 := by
      have : 0 ≤ 12 * (j : ℝ) / c' := by positivity
      linarith
    have hr_pos : 0 < r := Real.sqrt_pos.mpr (by linarith)
    have hr_gt_half : (1 / 2 : ℝ) < r := by
      rw [show (1 / 2 : ℝ) = √(1 / 4 : ℝ) by norm_num [Real.sqrt_div, Real.sqrt_one]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    have hr_le1 : r ≤ 1 := Real.sqrt_le_one.mpr hrad_le
    let zj : ℂ := (r : ℂ) * z₀
    have hK_eq : KalphaC ((c' / 12 - (j : ℝ) : ℝ) : ℂ) ((c' : ℂ) * b ^ 2 / 3) = besselI0C zj := by
      rw [KalphaC_eq_besselI0C hα_pos.le hc'_pos.le b]
      congr 1
      have hsqrt_id : 4 * π * √((c' / 12 - (j : ℝ)) * c' / 3) = c' * (2 * π / 3) * r := by
        have harg : (c' / 12 - (j : ℝ)) * c' / 3 = (c' / 6) ^ 2 * (1 - 12 * (j : ℝ) / c') := by
          field_simp [hc'_pos.ne']; ring
        rw [harg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
        dsimp [r]; ring
      rw [show 4 * (π : ℂ) * b * ((√((c' / 12 - (j : ℝ)) * c' / 3) : ℝ) : ℂ) =
          ((4 * π * √((c' / 12 - (j : ℝ)) * c' / 3) : ℝ) : ℂ) * b by push_cast; ring,
        hsqrt_id]
      rw [show zj = ((c' * (2 * π / 3) * r : ℝ) : ℂ) * b by
        dsimp [zj]; rw [hz₀_eq]; push_cast; ring]
    have hzj_re : 2 ≤ zj.re := by
      rw [show zj = (r : ℂ) * z₀ from rfl, Complex.re_ofReal_mul]
      calc (2 : ℝ) ≤ (1 / 2 : ℝ) * (0.36 * 39) := by norm_num
        _ ≤ r * (0.36 * c') := by gcongr
        _ ≤ r * z₀.re := by gcongr
    have hzj_im : |zj.im| ≤ zj.re := by
      rw [show zj = (r : ℂ) * z₀ from rfl, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
        abs_mul, abs_of_pos hr_pos, hz₀_im, hz₀_re, abs_mul, abs_of_pos hc2pi3_pos]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb_im_le_re hc2pi3_pos.le) hr_pos.le
    have hzj_norm : 0.18 * c' ≤ ‖zj‖ := by
      have hzj_eq_re : zj.re = r * z₀.re := Complex.re_ofReal_mul r z₀
      calc 0.18 * c' = (1 / 2 : ℝ) * (0.36 * c') := by ring
        _ ≤ r * z₀.re := mul_le_mul hr_gt_half.le hz₀_re_ge (by positivity) hr_pos.le
        _ = zj.re := hzj_eq_re.symm
        _ ≤ |zj.re| := le_abs_self _
        _ ≤ ‖zj‖ := Complex.abs_re_le_norm zj
    have hzj_norm_pos : 0 < ‖zj‖ := lt_of_lt_of_le (by positivity) hzj_norm
    have hI0_z := hI0_bd zj hzj_re hzj_im
    -- Relate `asC zj` to `asC z₀`:
    have has_ratio : asC zj = asC z₀ *
        (((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-((1 - r : ℝ) : ℂ) * z₀)) := by
      unfold asC
      have hden : (2 * (π : ℂ) * zj) ^ (1 / 2 : ℂ) =
          ((√r : ℝ) : ℂ) * (2 * (π : ℂ) * z₀) ^ (1 / 2 : ℂ) := by
        rw [show 2 * (π : ℂ) * zj = (r : ℂ) * (2 * (π : ℂ) * z₀) by dsimp [zj]; ring,
          ofReal_mul_cpow hr_pos (2 * (π : ℂ) * z₀) (1 / 2 : ℂ),
          show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
          ← Complex.ofReal_cpow hr_pos.le, ← Real.sqrt_eq_rpow]
      have hexp_zj : Complex.exp zj =
          Complex.exp z₀ * Complex.exp (-((1 - r : ℝ) : ℂ) * z₀) := by
        rw [← Complex.exp_add]; congr 1; dsimp [zj]; push_cast; ring
      have hsqrt_inv : ((√r : ℝ) : ℂ)⁻¹ = ((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
        rw [Real.sqrt_eq_rpow, ← Complex.ofReal_inv, ← Real.rpow_neg hr_pos.le]
      rw [hden, hexp_zj, ← hsqrt_inv]
      have hsqrt_c : ((√r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr_pos).ne'
      have h2pi_c : (2 * (π : ℂ) * z₀) ^ (1 / 2 : ℂ) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl hpi_ne)
      field_simp [hsqrt_c, h2pi_c]
    -- Bound `(r^(-1/2) - 1)` and `exp(-δ) - 1`:
    let η : ℝ := 1 - r - 6 * (j : ℝ) / c'
    have hη_nn : 0 ≤ η := by
      dsimp [η]
      have h1 : 0 ≤ 1 - 6 * (j : ℝ) / c' := by
        have : 6 * (j : ℝ) / c' ≤ 12 / 39 := by
          calc 6 * (j : ℝ) / c' ≤ 12 / c' := by gcongr; linarith
            _ ≤ 12 / 39 := by gcongr
        linarith
      have hsq_le : r ^ 2 ≤ (1 - 6 * (j : ℝ) / c') ^ 2 := by
        have hexp : (1 - 6 * (j : ℝ) / c') ^ 2 = 1 - 12 * (j : ℝ) / c' + (6 * (j : ℝ) / c') ^ 2 := by
          ring
        rw [Real.sq_sqrt (by linarith), hexp]
        linarith only [sq_nonneg (6 * (j : ℝ) / c')]
      have := Real.sqrt_le_sqrt hsq_le
      rw [Real.sqrt_sq h1, Real.sqrt_sq hr_pos.le] at this
      linarith
    have hη_le : η ≤ 144 / c' ^ 2 := by
      have hsum_ge1 : (1 : ℝ) ≤ (1 - 6 * (j : ℝ) / c') + r := by
        have h1 : 6 * (j : ℝ) / c' ≤ 12 / 39 := by
          calc 6 * (j : ℝ) / c' ≤ 12 / c' := by gcongr; linarith
            _ ≤ 12 / 39 := by gcongr
        linarith
      have hdiff_sq : ((1 - 6 * (j : ℝ) / c') + r) * η = (6 * (j : ℝ) / c') ^ 2 := by
        have hsq : r ^ 2 = 1 - 12 * (j : ℝ) / c' := Real.sq_sqrt (by linarith)
        dsimp [η]; linear_combination -hsq
      have hnum_le : (6 * (j : ℝ) / c') ^ 2 ≤ 144 / c' ^ 2 := by
        have : 6 * (j : ℝ) ≤ 12 := by linarith
        calc (6 * (j : ℝ) / c') ^ 2 ≤ (12 / c') ^ 2 := by gcongr
          _ = 144 / c' ^ 2 := by ring
      nlinarith
    let δ : ℂ := (η : ℂ) * z₀
    have hδ_re : (-δ).re ≤ 0 := by
      rw [show (-δ).re = -η * z₀.re by dsimp [δ]; simp]
      have hηz : 0 ≤ η * z₀.re := mul_nonneg hη_nn (by linarith only [hz₀_re_ge, hc'_pos])
      linarith only [hηz]
    have hδ_norm : ‖-δ‖ ≤ 158.4 / c' := by
      rw [norm_neg]; dsimp [δ]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη_nn]
      calc η * ‖z₀‖ ≤ (144 / c' ^ 2) * (1.1 * c') :=
            mul_le_mul hη_le hz₀_norm_le (norm_nonneg _) (by positivity)
        _ = 158.4 / c' := by field_simp [hc'_pos.ne']; ring
    have hexp_split : Complex.exp (-((1 - r : ℝ) : ℂ) * z₀) =
        Complex.exp (-4 * (π : ℂ) * (j : ℂ) * b) * Complex.exp (-δ) := by
      rw [← Complex.exp_add]
      congr 1
      dsimp [δ, η]
      rw [hz₀_eq]
      push_cast
      field_simp [hc'_pos.ne']
      ring
    have hexp_jb_norm : ‖Complex.exp (-4 * (π : ℂ) * (j : ℂ) * b)‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      have hre_eq : (-4 * (π : ℂ) * (j : ℂ) * b).re = -4 * π * (j : ℝ) * b.re := by
        have h1 : (-4 * (π : ℂ) * (j : ℂ) : ℂ) = ((-4 * π * (j : ℝ) : ℝ) : ℂ) := by push_cast; ring
        rw [h1, Complex.re_ofReal_mul]
      rw [hre_eq]
      have : 0 ≤ 4 * π * (j : ℝ) * b.re := by positivity
      linarith only [this]
    have hr_pow_bd : |r ^ (-(1 / 2 : ℝ)) - 1| ≤ 48 / c' := by
      have hsqrt_r_ge : (1 / √2 : ℝ) < √r := by
        rw [show (1 / √2 : ℝ) = √(1 / 2 : ℝ) by rw [Real.sqrt_div (by norm_num), Real.sqrt_one]]
        exact Real.sqrt_lt_sqrt (by norm_num) hr_gt_half
      have hden_ge : (1 / 2 : ℝ) ≤ √r * (1 + √r) := by
        have h1 : √(1 / 2 : ℝ) * √(1 / 2 : ℝ) = 1 / 2 := Real.mul_self_sqrt (by norm_num)
        have hsq_half : (1 / 2 : ℝ) ≤ √r * √r := by rw [Real.mul_self_sqrt hr_pos.le]; exact hr_gt_half.le
        have hmul_pos : 0 ≤ √r := Real.sqrt_nonneg _
        calc (1 / 2 : ℝ) ≤ √r * √r := hsq_half
          _ ≤ √r * (1 + √r) := by nlinarith only [hmul_pos]
      have h_id : (r ^ (-(1 / 2 : ℝ)) - 1) * (√r * (1 + √r)) = 1 - r := by
        rw [Real.rpow_neg hr_pos.le, ← Real.sqrt_eq_rpow]
        have hsq : √r ^ 2 = r := Real.sq_sqrt hr_pos.le
        have hne : √r ≠ 0 := (Real.sqrt_pos.mpr hr_pos).ne'
        field_simp [hne]; linear_combination -hsq
      have hr_pow_ge1 : 1 ≤ r ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hr_pos.le, one_le_inv₀ (Real.rpow_pos_of_pos hr_pos _)]
        exact Real.rpow_le_one hr_pos.le hr_le1 (by norm_num)
      have h1_sub_r : 1 - r ≤ 24 / c' := by
        have h1 : (1 + r) * (1 - r) = 12 * (j : ℝ) / c' := by
          have hsq : r ^ 2 = 1 - 12 * (j : ℝ) / c' := Real.sq_sqrt (by linarith only [hrad_ge])
          linarith only [hsq, show (1 + r) * (1 - r) = 1 - r ^ 2 by ring]
        have h12 : 12 * (j : ℝ) / c' ≤ 24 / c' :=
          div_le_div_of_nonneg_right (by linarith only [hj_r]) hc'_pos.le
        have h_ir_nn : 0 ≤ 1 - r := by linarith only [hr_le1]
        have h_1r_ge1 : 1 ≤ 1 + r := by linarith only [hr_pos]
        calc 1 - r ≤ (1 + r) * (1 - r) := le_mul_of_one_le_left h_ir_nn h_1r_ge1
          _ = 12 * (j : ℝ) / c' := h1
          _ ≤ 24 / c' := h12
      have h0 : 0 ≤ r ^ (-(1 / 2 : ℝ)) - 1 := sub_nonneg.mpr hr_pow_ge1
      have h_mul : (r ^ (-(1 / 2 : ℝ)) - 1) * (1 / 2 : ℝ) ≤ 24 / c' :=
        calc (r ^ (-(1 / 2 : ℝ)) - 1) * (1 / 2 : ℝ)
            ≤ (r ^ (-(1 / 2 : ℝ)) - 1) * (√r * (1 + √r)) := mul_le_mul_of_nonneg_left hden_ge h0
          _ = 1 - r := h_id
          _ ≤ 24 / c' := h1_sub_r
      rw [abs_of_nonneg h0]
      calc r ^ (-(1 / 2 : ℝ)) - 1
          = 2 * ((r ^ (-(1 / 2 : ℝ)) - 1) * (1 / 2 : ℝ)) := by ring
        _ ≤ 2 * (24 / c') := mul_le_mul_of_nonneg_left h_mul (by norm_num)
        _ = 48 / c' := by ring
    have hr_pow_le2' : ‖((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hr_pos.le _),
        Real.rpow_neg hr_pos.le]
      rw [inv_le_comm₀ (Real.rpow_pos_of_pos hr_pos _) (by norm_num)]
      have hsqrt_ge : (1 / 2 : ℝ) ≤ √r := by
        have : (1 / 4 : ℝ) ≤ r := by linarith only [hrad_ge, hr_gt_half]
        have : √(1 / 4 : ℝ) ≤ √r := Real.sqrt_le_sqrt this
        rwa [show √(1 / 4 : ℝ) = 1 / 2 by norm_num [Real.sqrt_div, Real.sqrt_one]] at this
      rw [← Real.sqrt_eq_rpow]
      linarith only [hsqrt_ge]
    let mainFac : ℂ := Complex.exp (-4 * (π : ℂ) * (j : ℂ) * b)
    let asympFac : ℂ := (((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-((1 - r : ℝ) : ℂ) * z₀))
    let diff1 : ℂ := besselI0C zj - asC zj
    let err_j : ℂ := diff1 / asC z₀ + (asympFac - mainFac)
    refine ⟨err_j, ?_, ?_⟩
    · have has_mul : asC z₀ * asympFac = asC zj := has_ratio.symm
      rw [hK_eq]
      calc besselI0C zj = (besselI0C zj - asC zj) + asC z₀ * asympFac := by rw [has_mul]; ring
        _ = asC z₀ * (mainFac + err_j) := by
            dsimp [err_j, diff1, mainFac]; field_simp [has0_ne]; ring
    · have has_rel : ‖asC zj‖ / ‖asC z₀‖ ≤ 2 := by
        rw [has_ratio, norm_mul, norm_mul, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr has0_ne)]
        have hexp_re_le : ‖Complex.exp (-((1 - r : ℝ) : ℂ) * z₀)‖ ≤ 1 := by
          rw [Complex.norm_exp, Real.exp_le_one_iff]
          have h1 : (-((1 - r : ℝ) : ℂ) * z₀).re = -(1 - r) * z₀.re := by
            rw [show -((1 - r : ℝ) : ℂ) = ((-(1 - r) : ℝ) : ℂ) by push_cast; rfl,
              Complex.re_ofReal_mul]
          rw [h1]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by linarith)) (by linarith)
        calc ‖((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖Complex.exp (-((1 - r : ℝ) : ℂ) * z₀)‖
            ≤ 2 * 1 := mul_le_mul hr_pow_le2' hexp_re_le (norm_nonneg _) (by norm_num)
          _ = 2 := mul_one 2
      have hterm1 : ‖diff1 / asC z₀‖ ≤ (2 * C_I0 / 0.18) / c' := by
        rw [norm_div]
        calc ‖besselI0C zj - asC zj‖ / ‖asC z₀‖
            ≤ ((C_I0 / ‖zj‖) * ‖asC zj‖) / ‖asC z₀‖ :=
              div_le_div_of_nonneg_right hI0_z (norm_nonneg _)
          _ = (C_I0 / ‖zj‖) * (‖asC zj‖ / ‖asC z₀‖) := by ring
          _ ≤ (C_I0 / (0.18 * c')) * 2 :=
              mul_le_mul (div_le_div_of_nonneg_left hCI0_nn (by positivity) hzj_norm)
                has_rel (by positivity) (by positivity)
          _ = (2 * C_I0 / 0.18) / c' := by ring
      have hterm2 : ‖asympFac - mainFac‖ ≤ 366 / c' := by
        have hid : asympFac - mainFac =
            (((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) - 1) * (mainFac * Complex.exp (-δ)) +
              mainFac * (Complex.exp (-δ) - 1) := by
          dsimp [asympFac, mainFac]; rw [hexp_split]; ring
        have hexp_δ_le1 : ‖Complex.exp (-δ)‖ ≤ 1 := by
          rw [Complex.norm_exp, Real.exp_le_one_iff]; exact hδ_re
        have hexp_δ_sub : ‖Complex.exp (-δ) - 1‖ ≤ 316.8 / c' := by
          calc ‖Complex.exp (-δ) - 1‖ ≤ 2 * ‖-δ‖ := norm_exp_sub_one_le_of_re_nonpos hδ_re
            _ ≤ 2 * (158.4 / c') := by gcongr
            _ = 316.8 / c' := by ring
        have hr_c : ‖((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) - 1‖ ≤ 48 / c' := by
          rw [show (((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) - 1) = (((r ^ (-(1 / 2 : ℝ)) - 1 : ℝ) : ℂ)) by
            push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
          exact hr_pow_bd
        rw [hid]
        calc ‖(((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) - 1) * (mainFac * Complex.exp (-δ)) +
                mainFac * (Complex.exp (-δ) - 1)‖
            ≤ ‖(((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) - 1)‖ * (‖mainFac‖ * ‖Complex.exp (-δ)‖) +
                ‖mainFac‖ * ‖Complex.exp (-δ) - 1‖ := by
              refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
              · rw [norm_mul, norm_mul]
              · rw [norm_mul]
          _ ≤ (48 / c') * (1 * 1) + 1 * (316.8 / c') := by
              gcongr
          _ ≤ 366 / c' := by
              rw [mul_one, mul_one, one_mul, ← add_div]
              exact div_le_div_of_nonneg_right (by norm_num) hc'_pos.le
      calc ‖err_j‖ ≤ ‖diff1 / asC z₀‖ + ‖asympFac - mainFac‖ := norm_add_le _ _
        _ ≤ (2 * C_I0 / 0.18) / c' + 366 / c' := add_le_add hterm1 hterm2
        _ ≤ C_j / c' := by
            rw [← add_div]
            refine div_le_div_of_nonneg_right ?_ hc'_pos.le
            dsimp [C_j]
            have : (2 * C_I0 / 0.18 : ℝ) = (100 / 9 : ℝ) * C_I0 := by ring
            linarith only [hCI0_nn, this]
  obtain ⟨err₀, hK0, herr0⟩ := hj_bound 0 (by norm_num)
  obtain ⟨err₁, hK1, herr1⟩ := hj_bound 1 (by norm_num)
  obtain ⟨err₂, hK2, herr2⟩ := hj_bound 2 (by norm_num)
  let ε_V : ℂ := err₀ - 2 * err₁ + err₂
  refine ⟨ε_V, ?_, ?_⟩
  · unfold V_C
    have h0' : KalphaC ((c' : ℂ) / 12) ((c' : ℂ) * b ^ 2 / 3) =
        asC z₀ * (1 + err₀) := by
      simpa using hK0
    have h1' : KalphaC ((c' : ℂ) / 12 - 1) ((c' : ℂ) * b ^ 2 / 3) =
        asC z₀ * (Complex.exp (-4 * (π : ℂ) * b) + err₁) := by
      simpa using hK1
    have h2' : KalphaC ((c' : ℂ) / 12 - 2) ((c' : ℂ) * b ^ 2 / 3) =
        asC z₀ * (Complex.exp (-4 * (π : ℂ) * (2 : ℂ) * b) + err₂) := by
      simpa using hK2
    rw [h0', h1', h2']
    have hexp2 : Complex.exp (-4 * (π : ℂ) * (2 : ℂ) * b) =
        (Complex.exp (-4 * (π : ℂ) * b)) ^ 2 := by
      rw [sq, ← Complex.exp_add]; congr 1; ring
    rw [hexp2]
    change asC z₀ * (1 + err₀) - 2 * (asC z₀ * (Complex.exp (-4 * (π : ℂ) * b) + err₁)) +
        asC z₀ * ((Complex.exp (-4 * (π : ℂ) * b)) ^ 2 + err₂) =
      asC z₀ * ((1 - Complex.exp (-4 * (π : ℂ) * b)) ^ 2 + ε_V)
    dsimp [ε_V]
    ring
  · have hnorm_tri : ‖ε_V‖ ≤ ‖err₀‖ + 2 * ‖err₁‖ + ‖err₂‖ := by
      have h2err : ‖(2 : ℂ) * err₁‖ = 2 * ‖err₁‖ := by
        rw [norm_mul, Complex.norm_ofNat]
      calc ‖err₀ - 2 * err₁ + err₂‖ ≤ ‖err₀ - 2 * err₁‖ + ‖err₂‖ := norm_add_le _ _
        _ ≤ (‖err₀‖ + ‖(2 : ℂ) * err₁‖) + ‖err₂‖ :=
            add_le_add (norm_sub_le err₀ ((2 : ℂ) * err₁)) le_rfl
        _ = ‖err₀‖ + 2 * ‖err₁‖ + ‖err₂‖ := by rw [h2err]
    calc ‖ε_V‖ ≤ ‖err₀‖ + 2 * ‖err₁‖ + ‖err₂‖ := hnorm_tri
      _ ≤ C_j / c' + 2 * (C_j / c') + C_j / c' :=
          add_le_add (add_le_add herr0 (mul_le_mul_of_nonneg_left herr1 (by norm_num))) herr2
      _ = C_V / c' := by dsimp [C_V]; ring

/-- **Lemma T3 (rescaled weight)** (`blowup_limit.tex`, Lemma `bl:T3`, second display):
for `c' ≥ 39` and `ε |ζ| ≤ ρ₃`,
`W_C c' (bScale c' ζ) = κ_c e^{c' L(b)} (1 + O(ε (1 + |ζ|) + 1/c'))`. -/
theorem lemma_T3_W_bound (hI0 : BesselI0Asymptotic) :
    ∃ ρ₃ C_W : ℝ, 0 < ρ₃ ∧ 0 ≤ C_W ∧
      ∀ {c' : ℝ} {ζ : ℂ}, 39 ≤ c' → tipEps c' * ‖ζ‖ ≤ ρ₃ →
        let b := bScale c' ζ
        ‖W_C c' b - (kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ ≤
          C_W * (tipEps c' * (1 + ‖ζ‖) + 1 / c') *
            ‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ := by
  obtain ⟨C_V, hCV_nn, hT3⟩ := lemma_T3 hI0
  let denomFn : ℂ → ℂ := fun b => (2 * (π : ℂ) * tipL b) ^ (1 / 2 : ℂ)
  let baseFn : ℂ → ℂ := fun b => ((2 / 3 : ℝ) : ℂ) * b / denomFn b
  let prefactor : ℂ → ℂ := fun b => baseFn b * (1 - Complex.exp (-4 * (π : ℂ) * b)) ^ 2
  have hre_pos_on : ∀ b ∈ ball (xiStar : ℂ) 0.15, (2 * (π : ℂ) * tipL b).re > 0 := by
    intro b hb
    have hb_norm : ‖b - (xiStar : ℂ)‖ ≤ 0.15 := by
      simpa [dist_eq_norm] using (mem_ball.mp hb).le
    have hdiff_re : |b.re - xiStar| ≤ 0.15 := by
      simpa [Complex.sub_re] using (Complex.abs_re_le_norm (b - (xiStar : ℂ))).trans hb_norm
    have hbre : (0.13 : ℝ) < b.re := by linarith [(abs_le.mp hdiff_re).1, xiStar_gt_028]
    have hmul : 2 * (π : ℂ) * tipL b = ((4 * π ^ 2 / 3 : ℝ) : ℂ) * b := by
      unfold tipL; push_cast; ring
    rw [hmul, Complex.re_ofReal_mul]
    positivity
  have hdenom_an : AnalyticOnNhd ℂ denomFn (ball (xiStar : ℂ) 0.15) := fun b hb => by
    have hlin : AnalyticAt ℂ (fun w => 2 * (π : ℂ) * tipL w) b := by
      unfold tipL
      exact analyticAt_const.mul (analyticAt_const.mul analyticAt_id)
    exact hlin.cpow analyticAt_const (Complex.mem_slitPlane_iff.mpr (Or.inl (hre_pos_on b hb)))
  have hdenom_ne : ∀ b ∈ ball (xiStar : ℂ) 0.15, denomFn b ≠ 0 := by
    intro b hb
    dsimp [denomFn]
    refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
    intro h0
    have h := hre_pos_on b hb
    rw [h0, Complex.zero_re] at h
    exact lt_irrefl 0 h
  have hbase_an : AnalyticOnNhd ℂ baseFn (ball (xiStar : ℂ) 0.15) := fun b hb =>
    (analyticAt_const.mul analyticAt_id).div (hdenom_an b hb) (hdenom_ne b hb)
  have hpre_an : AnalyticOnNhd ℂ prefactor (ball (xiStar : ℂ) 0.15) := fun b hb =>
    (hbase_an b hb).mul ((analyticAt_const.sub
      (analyticAt_const.mul analyticAt_id |>.cexp)).pow 2)
  have hsub_cl : closedBall (xiStar : ℂ) 0.1 ⊆ ball (xiStar : ℂ) 0.15 :=
    closedBall_subset_ball (by norm_num)
  obtain ⟨M_der, hM_der⟩ := (isCompact_closedBall (xiStar : ℂ) 0.1).exists_bound_of_continuousOn
    (hpre_an.deriv.continuousOn.mono hsub_cl)
  obtain ⟨M_base, hM_base⟩ := (isCompact_closedBall (xiStar : ℂ) 0.1).exists_bound_of_continuousOn
    (hbase_an.continuousOn.mono hsub_cl)
  let C_der : ℝ := max M_der 0
  let C_base : ℝ := max M_base 0
  have hCder_nn : 0 ≤ C_der := le_max_right _ _
  have hCbase_nn : 0 ≤ C_base := le_max_right _ _
  have hk0_pos : 0 < kappa0 := kappa0_pos
  let C_W : ℝ := max (C_der / kappa0) (C_base * C_V / kappa0)
  have hCW_nn : 0 ≤ C_W := le_trans (div_nonneg hCder_nn hk0_pos.le) (le_max_left _ _)
  refine ⟨0.1, C_W, by norm_num, hCW_nn, ?_⟩
  intro c' ζ hc' hεζ
  set b := bScale c' ζ
  have hc'_pos : 0 < c' := by linarith
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  have hb_cl : b ∈ closedBall (xiStar : ℂ) 0.1 := by
    rw [mem_closedBall, dist_eq_norm]
    have hsub : b - (xiStar : ℂ) = ((tipEps c' : ℝ) : ℂ) * ζ := by
      dsimp [b]; unfold bScale; ring
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε_pos]
    exact hεζ
  have hpre_at_xi : prefactor (xiStar : ℂ) = (kappa0 : ℂ) := by
    have htip : (2 * (π : ℂ) * tipL (xiStar : ℂ)) =
        ((2 * π * ((2 / 3 : ℝ) * Real.arsinh 1) : ℝ) : ℂ) := by
      unfold tipL xiStar
      have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      push_cast
      field_simp [hpi]
    have hden_pos : 0 < 2 * π * ((2 / 3 : ℝ) * Real.arsinh 1) := by
      have : 0 < Real.arsinh 1 := by
        rw [← Real.arsinh_zero]; exact Real.arsinh_strictMono one_pos
      positivity
    have hden_eq : denomFn (xiStar : ℂ) =
        ((√(2 * π * ((2 / 3 : ℝ) * Real.arsinh 1)) : ℝ) : ℂ) := by
      dsimp [denomFn]
      rw [htip, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow hden_pos.le, ← Real.sqrt_eq_rpow]
    dsimp [prefactor, baseFn]
    rw [hden_eq, exp_neg_four_pi_xiStar]
    unfold kappa0
    push_cast; ring
  have hpre_lip : ‖prefactor b - (kappa0 : ℂ)‖ ≤ C_der * (tipEps c' * ‖ζ‖) := by
    rw [← hpre_at_xi]
    have hconv : Convex ℝ (closedBall (xiStar : ℂ) 0.1) := convex_closedBall _ _
    have hdiff_cl : ∀ w ∈ closedBall (xiStar : ℂ) 0.1, DifferentiableAt ℂ prefactor w :=
      fun w hw => (hpre_an w (hsub_cl hw)).differentiableAt
    have hmvt := hconv.norm_image_sub_le_of_norm_deriv_le hdiff_cl
      (fun w hw => (hM_der w hw).trans (le_max_left M_der 0))
      (mem_closedBall_self (by norm_num)) hb_cl
    have hsub : b - (xiStar : ℂ) = ((tipEps c' : ℝ) : ℂ) * ζ := by
      dsimp [b]; unfold bScale; ring
    rwa [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε_pos] at hmvt
  obtain ⟨ε_V, hV_eq, hεV⟩ := hT3 hc' hb_cl
  have hW_split : W_C c' b - (kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b) =
      ((c' ^ (-(1 / 6 : ℝ)) : ℝ) : ℂ) * Complex.exp ((c' : ℂ) * tipL b) *
        ((prefactor b - (kappa0 : ℂ)) + baseFn b * ε_V) := by
    have hre_pos : (2 * (π : ℂ) * tipL b).re > 0 := hre_pos_on b (hsub_cl hb_cl)
    have harg_w : -(π : ℝ) < (2 * (π : ℂ) * tipL b).arg ∧
        (2 * (π : ℂ) * tipL b).arg ≤ π :=
      ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
    have has_split : asC ((c' : ℂ) * tipL b) =
        Complex.exp ((c' : ℂ) * tipL b) /
          (((c' ^ (1 / 2 : ℝ) : ℝ) : ℂ) * denomFn b) := by
      unfold asC
      dsimp [denomFn]
      have hmul : 2 * (π : ℂ) * ((c' : ℂ) * tipL b) = (c' : ℂ) * (2 * (π : ℂ) * tipL b) := by ring
      rw [hmul, ofReal_mul_cpow hc'_pos,
        show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow hc'_pos.le]
    have hc_pow_rel : ((tipEps c' : ℝ) : ℂ) * ((2 * c' / 3 : ℝ) : ℂ) /
        ((c' ^ (1 / 2 : ℝ) : ℝ) : ℂ) =
        ((c' ^ (-(1 / 6 : ℝ)) : ℝ) : ℂ) * ((2 / 3 : ℝ) : ℂ) := by
      have hreal : tipEps c' * (2 * c' / 3) / (c' ^ (1 / 2 : ℝ)) =
          c' ^ (-(1 / 6 : ℝ)) * (2 / 3 : ℝ) := by
        unfold tipEps
        rw [div_eq_mul_inv, ← Real.rpow_neg hc'_pos.le]
        have hc1 : c' = c' ^ (1 : ℝ) := (Real.rpow_one c').symm
        calc c' ^ (-(2 / 3 : ℝ)) * (2 * c' / 3) * c' ^ (-(1 / 2 : ℝ))
            = (2 / 3 : ℝ) * (c' ^ (-(2 / 3 : ℝ)) * c' ^ (1 : ℝ) * c' ^ (-(1 / 2 : ℝ))) := by
              rw [← hc1]; ring
          _ = (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ) + 1 + -(1 / 2 : ℝ)) := by
              rw [← Real.rpow_add hc'_pos, ← Real.rpow_add hc'_pos]
          _ = c' ^ (-(1 / 6 : ℝ)) * (2 / 3 : ℝ) := by norm_num; ring
      exact_mod_cast hreal
    have hden_ne : denomFn b ≠ 0 := hdenom_ne b (hsub_cl hb_cl)
    have hc12_ne : ((c' ^ (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hc'_pos _).ne'
    have hW_id : W_C c' b =
        ((c' ^ (-(1 / 6 : ℝ)) : ℝ) : ℂ) * Complex.exp ((c' : ℂ) * tipL b) *
          (prefactor b + baseFn b * ε_V) := by
      unfold W_C
      rw [hV_eq, has_split]
      dsimp [prefactor, baseFn]
      calc ((tipEps c' : ℝ) : ℂ) * ((2 * c' / 3 : ℝ) : ℂ) * b *
            (Complex.exp ((c' : ℂ) * tipL b) / (((c' ^ (1 / 2 : ℝ) : ℝ) : ℂ) * denomFn b) *
              ((1 - Complex.exp (-4 * (π : ℂ) * b)) ^ 2 + ε_V))
          = (((tipEps c' : ℝ) : ℂ) * ((2 * c' / 3 : ℝ) : ℂ) / ((c' ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
              Complex.exp ((c' : ℂ) * tipL b) *
                (b / denomFn b * ((1 - Complex.exp (-4 * (π : ℂ) * b)) ^ 2 + ε_V)) := by
            field_simp [hden_ne, hc12_ne]
        _ = ((c' ^ (-(1 / 6 : ℝ)) : ℝ) : ℂ) * Complex.exp ((c' : ℂ) * tipL b) *
              (((2 / 3 : ℝ) : ℂ) * b / denomFn b * (1 - Complex.exp (-4 * (π : ℂ) * b)) ^ 2 +
                ((2 / 3 : ℝ) : ℂ) * b / denomFn b * ε_V) := by
            rw [hc_pow_rel]; ring
    have hkap_eq : (kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b) =
        ((c' ^ (-(1 / 6 : ℝ)) : ℝ) : ℂ) * Complex.exp ((c' : ℂ) * tipL b) * (kappa0 : ℂ) := by
      unfold kappaC
      push_cast; ring
    rw [hW_id, hkap_eq]; ring
  have hkap_norm : ‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ =
      c' ^ (-(1 / 6 : ℝ)) * kappa0 * ‖Complex.exp ((c' : ℂ) * tipL b)‖ := by
    have hpos : 0 < kappaC c' := mul_pos (Real.rpow_pos_of_pos hc'_pos _) hk0_pos
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    unfold kappaC; ring
  have hpref_norm : ‖((c' ^ (-(1 / 6 : ℝ)) : ℝ) : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ =
      ‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ / kappa0 := by
    rw [hkap_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hc'_pos _)]
    field_simp [hk0_pos.ne']
  have hbase_le : ‖baseFn b‖ ≤ C_base := (hM_base b hb_cl).trans (le_max_left _ _)
  have hbracket : ‖(prefactor b - (kappa0 : ℂ)) + baseFn b * ε_V‖ ≤
      kappa0 * (C_W * (tipEps c' * (1 + ‖ζ‖) + 1 / c')) := by
    have h1 : ‖prefactor b - (kappa0 : ℂ)‖ ≤ C_der * (tipEps c' * ‖ζ‖) := hpre_lip
    have h2 : ‖baseFn b * ε_V‖ ≤ C_base * C_V * (1 / c') := by
      rw [norm_mul]
      calc ‖baseFn b‖ * ‖ε_V‖ ≤ C_base * (C_V / c') :=
            mul_le_mul hbase_le hεV (norm_nonneg _) hCbase_nn
        _ = C_base * C_V * (1 / c') := by ring
    have hder_cw : C_der ≤ kappa0 * C_W := by
      have : C_der / kappa0 ≤ C_W := le_max_left _ _
      exact (div_le_iff₀ hk0_pos).mp this |>.trans_eq (mul_comm _ _)
    have hbase_cw : C_base * C_V ≤ kappa0 * C_W := by
      have : C_base * C_V / kappa0 ≤ C_W := le_max_right _ _
      exact (div_le_iff₀ hk0_pos).mp this |>.trans_eq (mul_comm _ _)
    calc ‖(prefactor b - (kappa0 : ℂ)) + baseFn b * ε_V‖
        ≤ ‖prefactor b - (kappa0 : ℂ)‖ + ‖baseFn b * ε_V‖ := norm_add_le _ _
      _ ≤ C_der * (tipEps c' * ‖ζ‖) + C_base * C_V * (1 / c') := add_le_add h1 h2
      _ ≤ (kappa0 * C_W) * (tipEps c' * (1 + ‖ζ‖)) + (kappa0 * C_W) * (1 / c') := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul hder_cw (by nlinarith [hε_pos.le]) (by positivity)
              (mul_nonneg hk0_pos.le hCW_nn)
          · exact mul_le_mul_of_nonneg_right hbase_cw (by positivity)
      _ = kappa0 * (C_W * (tipEps c' * (1 + ‖ζ‖) + 1 / c')) := by ring
  dsimp only
  rw [show W_C c' b - (kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b) = _ from hW_split,
    norm_mul, hpref_norm]
  calc (‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ / kappa0) *
        ‖(prefactor b - (kappa0 : ℂ)) + baseFn b * ε_V‖
      ≤ (‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ / kappa0) *
          (kappa0 * (C_W * (tipEps c' * (1 + ‖ζ‖) + 1 / c'))) :=
        mul_le_mul_of_nonneg_left hbracket (div_nonneg (norm_nonneg _) hk0_pos.le)
    _ = C_W * (tipEps c' * (1 + ‖ζ‖) + 1 / c') *
          ‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ := by
        field_simp [hk0_pos.ne']

end FormalResearch.ModularBootstrap

section AxiomChecks
open FormalResearch.ModularBootstrap

/-- info: 'FormalResearch.ModularBootstrap.lemmaGPotentialInput_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemmaGPotentialInput_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.lemma_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T2

/-- info: 'FormalResearch.ModularBootstrap.V_C_entire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms V_C_entire

/-- info: 'FormalResearch.ModularBootstrap.W_C_entire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms W_C_entire

/-- info: 'FormalResearch.ModularBootstrap.besselI0Asymptotic_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselI0Asymptotic_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.lemma_T3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T3

/-- info: 'FormalResearch.ModularBootstrap.lemma_T3_W_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T3_W_bound

end AxiomChecks
