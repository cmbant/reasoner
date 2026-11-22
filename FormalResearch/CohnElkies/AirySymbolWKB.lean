module

public import FormalResearch.CohnElkies.AiryNicholsonIntegral
public import FormalResearch.Special.AiryBiReal
public import FormalResearch.Special.AiryAsymReal

/-!
# Negative-Axis Airy WKB Representation and All-Order Symbol Decomposition

Source: `CFT/sign_uncertainty/paper/ce_cr_airy_wkb_derivatives.tex`, §§2–4
(Lemmas W.2(b)–(c), W.3(b), W.4(b), Proposition W.5, and Proposition W.6 / `(CR.14)`).
Unconditional Nicholson integral and phase-correction bounds live in
`FormalResearch.CohnElkies.AiryNicholsonIntegral`.

## Main definitions
* `airyMod`, `airyTheta0`, `airyTheta`: exact modulus `M(x)`, leading phase
  `ϑ(x) = (2/3) x^{3/2} + π/4`, and exact phase `θ(x) = π/2 - ϑ(x) - ϖ(x)`.
* `airyP1`, `airyQ1`, `airyRho`, `airyP2`, `airyQ2`: exact WKB envelopes of Proposition W.5.
* `CardinalResolventCoeffs`: inherited `(CR.21)` coefficient hypotheses for Proposition W.6.

## Main results
* Unconditional: `airyDeriv_neg_w2c` (Lemma W.2(c)), `airyP1_sub_one_isSymbol`,
  `airyP2_sub_one_isSymbol`, `airyQ1_isSymbol`, `airyQ2_isSymbol` (Proposition W.5).
* Conditional on `hNicholson : ∀ x > 0, airyAi (-x) ^ 2 + airyBi (-x) ^ 2 = nicholsonIntegral x`
  (DLMF 9.11.4, `R2`): `airyMod_isSymbol`, `deriv_airyMod_isSymbol`, `logDeriv_airyMod_isSymbol`
  (Lemma W.3(b)), `airy_neg_phase_rep`, `airy_W2b` (Lemmas W.2(b) & W.4(b)),
  `airy_neg_osc_extract`, `airyDeriv_neg_osc_extract`, `airyAi_neg_two_term_asymp` (Proposition W.5),
  `cardinalResolventCoeffs_nonvacuous`, and `cardinal_symbol_decomp` (Proposition W.6 / `(CR.14)`).
-/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped ContDiff Real Topology
open FormalResearch.Asymptotics FormalResearch.Special

namespace FormalResearch.CohnElkies

/-! ### Definitions -/

/-- Exact modulus `M(x) = √(Ai(-x)² + Bi(-x)²)`. -/
noncomputable def airyMod (x : ℝ) : ℝ :=
  √(airyAi (-x) ^ 2 + airyBi (-x) ^ 2)

/-- Leading WKB phase `ϑ(x) = (2/3) x^{3/2} + π/4`. -/
noncomputable def airyTheta0 (x : ℝ) : ℝ :=
  (2 / 3 : ℝ) * x ^ (3 / 2 : ℝ) + π / 4

/-- Exact phase `θ(x) = π/2 - ϑ(x) - ϖ(x)`. -/
noncomputable def airyTheta (x : ℝ) : ℝ :=
  π / 2 - airyTheta0 x - phaseCorr x

/-- WKB envelopes `P₁, Q₁, ρ, P₂, Q₂` of Proposition W.5. -/
noncomputable def airyP1 (x : ℝ) : ℝ :=
  (1 + nicholsonErr x) ^ (1 / 2 : ℝ) * Real.cos (phaseCorr x)

noncomputable def airyQ1 (x : ℝ) : ℝ :=
  (1 + nicholsonErr x) ^ (1 / 2 : ℝ) * Real.sin (phaseCorr x)

noncomputable def airyRho (x : ℝ) : ℝ :=
  x ^ (-(1 / 2 : ℝ)) * (1 / (4 * x) - _root_.deriv nicholsonErr x / (2 * (1 + nicholsonErr x)))

noncomputable def airyP2 (x : ℝ) : ℝ :=
  (1 + nicholsonErr x) ^ (-(1 / 2 : ℝ)) * Real.cos (phaseCorr x) - airyRho x * airyQ1 x

noncomputable def airyQ2 (x : ℝ) : ℝ :=
  -(1 + nicholsonErr x) ^ (-(1 / 2 : ℝ)) * Real.sin (phaseCorr x) - airyRho x * airyP1 x


/-! ### Lemma W.2(c), W.3(b), W.2(b), and W.4(b): exact modulus and phase -/

theorem airyMod_pos (x : ℝ) : 0 < airyMod x := by
  unfold airyMod
  rw [Real.sqrt_pos]
  by_contra hle
  push Not at hle
  have hA0 : airyAi (-x) = 0 := by nlinarith [sq_nonneg (airyAi (-x)), sq_nonneg (airyBi (-x))]
  have hB0 : airyBi (-x) = 0 := by nlinarith [sq_nonneg (airyAi (-x)), sq_nonneg (airyBi (-x))]
  have hw := airyWronskian_real (-x)
  rw [hA0, hB0, zero_mul, mul_zero, sub_zero] at hw
  exact (one_div_ne_zero Real.pi_pos.ne') hw.symm

theorem contDiff_airyBi : ContDiff ℝ ∞ airyBi := by
  have h : ContDiff ℂ ⊤ airyBiC := differentiable_airyBiC.contDiff
  have h2 : ContDiff ℝ ⊤ (fun x : ℝ => airyBiC (x : ℂ)) :=
    (h.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
  exact ((Complex.reCLM.contDiff.comp h2 : ContDiff ℝ ⊤ fun x : ℝ => (airyBiC (x : ℂ)).re)).of_le
    le_top

theorem contDiff_airyMod : ContDiff ℝ ∞ airyMod := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hne : airyAi (-x) ^ 2 + airyBi (-x) ^ 2 ≠ 0 := by
    have hp := airyMod_pos x
    unfold airyMod at hp
    exact (Real.sqrt_pos.mp hp).ne'
  have hAi : ContDiff ℝ ∞ (fun t => airyAi (-t)) :=
    (contDiff_airyAi.of_le le_top).comp contDiff_neg
  have hBi : ContDiff ℝ ∞ (fun t => airyBi (-t)) :=
    contDiff_airyBi.comp contDiff_neg
  exact (Real.contDiffAt_sqrt hne).comp x ((hAi.pow 2).add (hBi.pow 2)).contDiffAt

private lemma hasDerivAt_airyMod (x : ℝ) :
    HasDerivAt airyMod
      ((-airyAi (-x) * airyAi' (-x) - airyBi (-x) * airyBiDeriv (-x)) / airyMod x) x := by
  have hpos : 0 < airyAi (-x) ^ 2 + airyBi (-x) ^ 2 := by
    have hp := airyMod_pos x; unfold airyMod at hp; exact Real.sqrt_pos.mp hp
  have hA : HasDerivAt (fun t => airyAi (-t)) (-airyAi' (-x)) x := by
    convert ((hasDerivAt_airyAi (-x)).comp x (hasDerivAt_neg x)) using 1
    · rfl
    · ring
  have hB : HasDerivAt (fun t => airyBi (-t)) (-airyBiDeriv (-x)) x := by
    convert ((hasDerivAt_airyBi (-x)).comp x (hasDerivAt_neg x)) using 1
    · rfl
    · ring
  have hsum : HasDerivAt (fun t => airyAi (-t) ^ 2 + airyBi (-t) ^ 2)
      (2 * (-airyAi (-x) * airyAi' (-x) - airyBi (-x) * airyBiDeriv (-x))) x := by
    have h1 := ((hA.pow 2).add (hB.pow 2))
    convert h1 using 1; ring
  have hsqrt := (Real.hasDerivAt_sqrt hpos.ne').comp x hsum
  refine hsqrt.congr_deriv ?_
  change 1 / (2 * airyMod x) * _ = _
  have hm : airyMod x ≠ 0 := (airyMod_pos x).ne'
  field_simp

/-- **Lemma W.2(c)** (unconditional on `ℝ`):
`Ai'(-x) = -(M'(x)/M(x)) Ai(-x) - Bi(-x)/(π M(x)²)`. -/
theorem airyDeriv_neg_w2c (x : ℝ) :
    airyAi' (-x) =
      -(_root_.deriv airyMod x / airyMod x) * airyAi (-x) - airyBi (-x) / (π * airyMod x ^ 2) := by
  have hd : _root_.deriv airyMod x =
      (-airyAi (-x) * airyAi' (-x) - airyBi (-x) * airyBiDeriv (-x)) / airyMod x :=
    (hasDerivAt_airyMod x).deriv
  have hm : airyMod x ≠ 0 := (airyMod_pos x).ne'
  have hmsq : airyMod x ^ 2 = airyAi (-x) ^ 2 + airyBi (-x) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hw := airyWronskian_real (-x)
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have hpi_hw : π * (airyAi (-x) * airyBiDeriv (-x) - airyAi' (-x) * airyBi (-x)) = 1 := by
    rw [hw]; field_simp
  rw [hd]
  field_simp
  rw [hmsq]
  linear_combination -airyBi (-x) * hpi_hw

private lemma continuousOn_phaseIntegrand_mod :
    ContinuousOn (fun t : ℝ => 1 / (π * airyMod t ^ 2) - t ^ (1 / 2 : ℝ)) (Set.Icc 0 1) := by
  have hM : Continuous airyMod := contDiff_airyMod.continuous
  refine ContinuousOn.sub ?_ (continuousOn_id.rpow_const fun _ _ => Or.inr (by norm_num))
  exact continuousOn_const.div (continuousOn_const.mul (hM.pow 2).continuousOn)
    fun t _ => mul_ne_zero Real.pi_pos.ne' (sq_pos_of_pos (airyMod_pos t)).ne'

section GivenNicholson

variable (hNicholson : ∀ x > 0, airyAi (-x) ^ 2 + airyBi (-x) ^ 2 = nicholsonIntegral x)

include hNicholson

lemma airyMod_sq_eq {x : ℝ} (hx : 0 < x) :
    airyMod x ^ 2 = (1 + nicholsonErr x) / (π * x ^ (1 / 2 : ℝ)) := by
  have hmsq : airyMod x ^ 2 = nicholsonIntegral x := by
    unfold airyMod
    rw [Real.sq_sqrt (by positivity), hNicholson x hx]
  have hne1 : π ≠ 0 := Real.pi_pos.ne'
  have hne2 : x ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  rw [hmsq]
  unfold nicholsonErr
  field_simp
  ring

lemma one_add_nicholsonErr_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < 1 + nicholsonErr x := by
  have h1 : 0 < airyMod x ^ 2 := sq_pos_of_pos (airyMod_pos x)
  have h2 := airyMod_sq_eq hNicholson hx
  have hden : 0 < π * x ^ (1 / 2 : ℝ) := mul_pos Real.pi_pos (Real.rpow_pos_of_pos hx _)
  rw [h2, div_pos_iff_of_pos_right hden] at h1
  exact h1

/-- **Lemma W.3(b), modulus identity**: `M(x) = π^{-1/2} x^{-1/4} (1 + E(x))^{1/2}` for `x > 0`. -/
theorem airyMod_eq_rpow_one_add {x : ℝ} (hx : 0 < x) :
    airyMod x = π ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 4 : ℝ)) * (1 + nicholsonErr x) ^ (1 / 2 : ℝ) := by
  have hE : 0 ≤ 1 + nicholsonErr x := (one_add_nicholsonErr_pos_of_pos hNicholson hx).le
  have hsq : airyMod x ^ 2 =
      (π ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 4 : ℝ)) * (1 + nicholsonErr x) ^ (1 / 2 : ℝ)) ^ 2 := by
    rw [airyMod_sq_eq hNicholson hx, mul_pow, mul_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le,
      ← Real.rpow_natCast, ← Real.rpow_mul hx.le,
      ← Real.rpow_natCast, ← Real.rpow_mul hE]
    norm_num
    rw [Real.rpow_neg_one, Real.rpow_neg hx.le]
    field_simp
  have hrhs_nn : 0 ≤ π ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 4 : ℝ)) * (1 + nicholsonErr x) ^ (1 / 2 : ℝ) := by
    positivity
  exact (sq_eq_sq₀ (airyMod_pos x).le hrhs_nn).mp hsq

/-- **Lemma W.3(b), inverse square modulus**: `1 / (π M(x)²) = x^{1/2} (1 + E(x))⁻¹` for `x > 0`. -/
theorem inv_pi_airyMod_sq_eq {x : ℝ} (hx : 0 < x) :
    1 / (π * airyMod x ^ 2) = x ^ (1 / 2 : ℝ) * (1 + nicholsonErr x)⁻¹ := by
  rw [airyMod_sq_eq hNicholson hx]
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have hE : 1 + nicholsonErr x ≠ 0 := (one_add_nicholsonErr_pos_of_pos hNicholson hx).ne'
  field_simp

/-- **Lemma W.3(b), logarithmic derivative**: `M'/M = -1/(4x) + E'/(2(1+E))` for `x > 0`. -/
theorem logDeriv_airyMod_eq {x : ℝ} (hx : 0 < x) :
    _root_.deriv airyMod x / airyMod x =
      -(1 / (4 * x)) + _root_.deriv nicholsonErr x / (2 * (1 + nicholsonErr x)) := by
  have hM : HasDerivAt airyMod (_root_.deriv airyMod x) x :=
    (hasDerivAt_airyMod x).differentiableAt.hasDerivAt
  have hL : HasDerivAt (fun t => airyMod t ^ 2) (2 * airyMod x * _root_.deriv airyMod x) x :=
    (hM.fun_pow 2).congr_deriv (by ring)
  have hE : HasDerivAt nicholsonErr (_root_.deriv nicholsonErr x) x :=
    ((contDiffOn_nicholsonErr_Ioi.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt
      (by simp)).hasDerivAt
  have hx12 : HasDerivAt (fun t => t ^ (-(1 / 2 : ℝ))) (-(1 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ))) x := by
    convert Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hx.ne') using 1; norm_num
  have hR_fn : Set.EqOn (fun t => airyMod t ^ 2)
      (fun t => π⁻¹ * t ^ (-(1 / 2 : ℝ)) * (1 + nicholsonErr t)) (Set.Ioi 0) := by
    intro t ht
    rw [Set.mem_Ioi] at ht
    dsimp only
    rw [airyMod_sq_eq hNicholson ht, Real.rpow_neg ht.le]
    ring
  have hR : HasDerivAt (fun t => π⁻¹ * t ^ (-(1 / 2 : ℝ)) * (1 + nicholsonErr t))
      (π⁻¹ * (-(1 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ)) * (1 + nicholsonErr x) +
        x ^ (-(1 / 2 : ℝ)) * _root_.deriv nicholsonErr x)) x := by
    have h1 := ((hx12.const_mul π⁻¹).mul (hE.const_add 1))
    convert h1 using 1; ring
  have heq_deriv := (hL.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx) fun t ht => (hR_fn ht).symm)).unique hR
  have hm_ne : airyMod x ≠ 0 := (airyMod_pos x).ne'
  have hmsq : airyMod x ^ 2 = π⁻¹ * x ^ (-(1 / 2 : ℝ)) * (1 + nicholsonErr x) :=
    hR_fn hx
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have hxpow : x ^ (-(1 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have hE_ne : 1 + nicholsonErr x ≠ 0 := (one_add_nicholsonErr_pos_of_pos hNicholson hx).ne'
  have hx32 : x ^ (-(3 / 2 : ℝ)) = x⁻¹ * x ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one x, ← Real.rpow_add hx]; norm_num
  have hdiv : _root_.deriv airyMod x / airyMod x =
      (2 * airyMod x * _root_.deriv airyMod x) / (2 * airyMod x ^ 2) := by
    field_simp
  rw [hdiv, heq_deriv, hmsq, hx32]
  field_simp
  ring

/-- **Lemma W.3(b)**: `M ∈ 𝒮_{1/4}`. -/
theorem airyMod_isSymbol : IsSymbol (1 / 4) airyMod := by
  have h1 : IsSymbol (1 / 4) (fun x : ℝ => π ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 4 : ℝ))) :=
    (IsSymbol.rpow_neg (1 / 4)).const_mul _
  have h2 : IsSymbol 0 (fun x => (1 + nicholsonErr x) ^ (1 / 2 : ℝ)) :=
    one_add_nicholsonErr_rpow_isSymbol (1 / 2)
  have hprod := h1.mul h2
  rw [add_zero] at hprod
  refine hprod.congr fun x hx => ?_
  have hxpos : 0 < x := by linarith [Set.mem_Ici.mp hx]
  exact (airyMod_eq_rpow_one_add hNicholson hxpos).symm

/-- **Lemma W.3(b)**: `M' ∈ 𝒮_{5/4}`. -/
theorem deriv_airyMod_isSymbol : IsSymbol (5 / 4) (_root_.deriv airyMod) := by
  simpa only [show (1 / 4 : ℝ) + 1 = 5 / 4 by norm_num] using
    (airyMod_isSymbol hNicholson).deriv_of_contDiff contDiff_airyMod

/-- **Lemma W.3(b)**: `M'/M ∈ 𝒮_1`. -/
theorem logDeriv_airyMod_isSymbol :
    IsSymbol 1 (fun x => _root_.deriv airyMod x / airyMod x) := by
  have h1 : IsSymbol 1 (fun x : ℝ => -(1 / 4 : ℝ) * x⁻¹) := IsSymbol.inv.const_mul _
  have hEd : IsSymbol 4 (_root_.deriv nicholsonErr) := by
    simpa only [show (3 : ℝ) + 1 = 4 by norm_num] using
      nicholsonErr_isSymbol.deriv isOpen_Ioi
        (fun _ h => by rw [Set.mem_Ioi]; linarith [Set.mem_Ici.mp h]) contDiffOn_nicholsonErr_Ioi
  have h2 : IsSymbol 4 (fun x => (1 / 2 : ℝ) * _root_.deriv nicholsonErr x * (1 + nicholsonErr x)⁻¹) := by
    simpa only [add_zero] using (hEd.const_mul (1 / 2)).mul one_add_nicholsonErr_inv_isSymbol
  have hsum := h1.add h2
  have hmin : min (1 : ℝ) 4 = 1 := by norm_num
  rw [hmin] at hsum
  refine hsum.congr fun x hx => ?_
  have hxpos : 0 < x := by linarith [Set.mem_Ici.mp hx]
  rw [logDeriv_airyMod_eq hNicholson hxpos]
  field_simp

private lemma phaseIntegrand_eq_mod {t : ℝ} (ht : 0 < t) :
    phaseIntegrand t = 1 / (π * airyMod t ^ 2) - t ^ (1 / 2 : ℝ) := by
  unfold phaseIntegrand
  rw [sub_mul, one_mul, mul_comm _ (t ^ (1 / 2 : ℝ)), ← inv_pi_airyMod_sq_eq hNicholson ht]

private lemma integrableOn_phaseIntegrand_pos {x : ℝ} (hx : 0 < x) :
    IntegrableOn phaseIntegrand (Set.Ioi x) := by
  rcases le_or_gt 1 x with hx1 | hx1
  · exact integrableOn_phaseIntegrand_of_ge_one hx1
  · rw [← Set.Ioc_union_Ioi_eq_Ioi hx1.le]
    refine IntegrableOn.union ?_ (integrableOn_phaseIntegrand_of_ge_one le_rfl)
    have hcont : ContinuousOn (fun t : ℝ => 1 / (π * airyMod t ^ 2) - t ^ (1 / 2 : ℝ))
        (Set.Icc x 1) :=
      continuousOn_phaseIntegrand_mod.mono fun t ht => ⟨by linarith [ht.1], ht.2⟩
    refine (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self |>.congr_fun
      (fun t ht => ?_) measurableSet_Ioc
    exact (phaseIntegrand_eq_mod hNicholson (lt_of_lt_of_le hx ht.1.le)).symm

private lemma hasDerivAt_phaseCorr_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt phaseCorr (1 / (π * airyMod x ^ 2) - x ^ (1 / 2 : ℝ)) x := by
  have heq : Set.EqOn phaseCorr
      (fun y => (∫ t in (1 : ℝ)..y, (1 / (π * airyMod t ^ 2) - t ^ (1 / 2 : ℝ))) -
        ∫ t in Set.Ioi 1, phaseIntegrand t) (Set.Ioi 0) := by
    intro y hy
    rw [Set.mem_Ioi] at hy
    have hsub := intervalIntegral.integral_Ioi_sub_Ioi'
      (integrableOn_phaseIntegrand_of_ge_one le_rfl)
      (integrableOn_phaseIntegrand_pos hNicholson hy)
    have hint_eq : (∫ t in (1 : ℝ)..y, phaseIntegrand t) =
        ∫ t in (1 : ℝ)..y, (1 / (π * airyMod t ^ 2) - t ^ (1 / 2 : ℝ)) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
      have htpos : 0 < t := by
        rw [Set.mem_uIoc] at ht
        rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
      exact phaseIntegrand_eq_mod hNicholson htpos
    unfold phaseCorr
    change -∫ t in Set.Ioi y, phaseIntegrand t = _
    linarith
  let gmod : ℝ → ℝ := fun t => 1 / (π * airyMod t ^ 2) - t ^ (1 / 2 : ℝ)
  have hcont : ContinuousAt gmod x := by
    have hM := contDiff_airyMod.continuous.continuousAt (x := x)
    have hr := (Real.continuousAt_rpow_const x (1 / 2 : ℝ) (Or.inl hx.ne'))
    exact (continuousAt_const.div (continuousAt_const.mul (hM.pow 2))
      (mul_ne_zero Real.pi_pos.ne' (sq_pos_of_pos (airyMod_pos x)).ne')).sub hr
  have hg_cont : ContinuousOn gmod (Set.Ioi 0) :=
    (continuousOn_const.div (continuousOn_const.mul (contDiff_airyMod.continuous.pow 2).continuousOn)
      fun t _ => mul_ne_zero Real.pi_pos.ne' (sq_pos_of_pos (airyMod_pos t)).ne').sub
      (continuousOn_id.rpow_const fun _ _ => Or.inr (by norm_num))
  have hi : IntervalIntegrable gmod volume 1 x :=
    ContinuousOn.intervalIntegrable (hg_cont.mono fun t ht => by
      rw [Set.mem_uIcc] at ht; rw [Set.mem_Ioi]; rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith)
  have hd := intervalIntegral.integral_hasDerivAt_right hi
    (hg_cont.stronglyMeasurableAtFilter isOpen_Ioi x hx) hcont
  exact (hd.sub_const _).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx) fun y hy => heq hy)

private lemma hasDerivAt_airyTheta_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt airyTheta (-(1 / (π * airyMod x ^ 2))) x := by
  have h1 : HasDerivAt airyTheta0 (x ^ (1 / 2 : ℝ)) x := by
    have hr := (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ)) (Or.inl hx.ne')).const_mul (2 / 3 : ℝ)
    have h2 : HasDerivAt airyTheta0 ((2 / 3 : ℝ) * ((3 / 2 : ℝ) * x ^ ((3 / 2 : ℝ) - 1))) x := by
      unfold airyTheta0; simpa using hr.add_const (π / 4)
    refine h2.congr_deriv ?_
    have : (3 / 2 : ℝ) - 1 = 1 / 2 := by norm_num
    rw [this]; ring
  have h2 := hasDerivAt_phaseCorr_pos hNicholson hx
  unfold airyTheta
  exact (((hasDerivAt_const x (π / 2)).sub h1).sub h2).congr_deriv (by ring)

/-- **Lemma W.2(b) and Lemma W.4(b)**: for all `x > 0`,
`Ai(-x) = M(x) cos θ(x)` and `Bi(-x) = M(x) sin θ(x)`. -/
theorem airy_neg_phase_rep {x : ℝ} (hx : 0 < x) :
    airyAi (-x) = airyMod x * Real.cos (airyTheta x) ∧
      airyBi (-x) = airyMod x * Real.sin (airyTheta x) := by
  let U : ℝ → ℂ := fun t => (((airyAi (-t) : ℝ) : ℂ) + I * ((airyBi (-t) : ℝ) : ℂ)) / (airyMod t : ℂ)
  let Z : ℝ → ℂ := fun t => U t * Complex.exp (-I * (airyTheta t : ℂ))
  have hU_deriv : ∀ t : ℝ, HasDerivAt U
      ((-I / (((π * airyMod t ^ 2 : ℝ) : ℂ))) * U t) t := by
    intro t
    have hA : HasDerivAt (fun u : ℝ => ((airyAi (-u) : ℝ) : ℂ)) ((-airyAi' (-t) : ℝ) : ℂ) t := by
      simpa using ((hasDerivAt_airyAi (-t)).comp t (hasDerivAt_neg t)).ofReal_comp
    have hB : HasDerivAt (fun u : ℝ => ((airyBi (-u) : ℝ) : ℂ)) ((-airyBiDeriv (-t) : ℝ) : ℂ) t := by
      simpa using ((hasDerivAt_airyBi (-t)).comp t (hasDerivAt_neg t)).ofReal_comp
    have hM : HasDerivAt (fun u : ℝ => (airyMod u : ℂ)) ((_root_.deriv airyMod t : ℝ) : ℂ) t := by
      have hm := hasDerivAt_airyMod t
      rw [← hm.deriv] at hm
      exact hm.ofReal_comp
    have hm_ne : (airyMod t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (airyMod_pos t).ne'
    have hdiv := (hA.add (hB.const_mul I)).div hM hm_ne
    refine hdiv.congr_deriv ?_
    have hM_deriv : _root_.deriv airyMod t =
        (-airyAi (-t) * airyAi' (-t) - airyBi (-t) * airyBiDeriv (-t)) / airyMod t :=
      (hasDerivAt_airyMod t).deriv
    have hm_r : airyMod t ≠ 0 := (airyMod_pos t).ne'
    have hmsq : airyMod t ^ 2 = airyAi (-t) ^ 2 + airyBi (-t) ^ 2 := Real.sq_sqrt (by positivity)
    have hw := airyWronskian_real (-t)
    have hpi : π ≠ 0 := Real.pi_pos.ne'
    have hpi_hw : π * (airyAi (-t) * airyBiDeriv (-t) - airyAi' (-t) * airyBi (-t)) = 1 := by
      rw [hw]; field_simp
    have hpi_c : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi
    dsimp [U]
    rw [hM_deriv]
    push_cast
    field_simp [hm_ne, hpi_c]
    rw [← Complex.ofReal_pow, hmsq]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.neg_im]
      linear_combination airyBi (-t) * hpi_hw
    · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.neg_im]
      linear_combination -airyAi (-t) * hpi_hw
  have hZ_deriv : ∀ t > 0, HasDerivAt Z 0 t := by
    intro t ht
    have h1 := hU_deriv t
    have hth : HasDerivAt (fun u : ℝ => -I * (airyTheta u : ℂ))
        (-I * ((-(1 / (π * airyMod t ^ 2)) : ℝ) : ℂ)) t :=
      ((hasDerivAt_airyTheta_pos hNicholson ht).ofReal_comp).const_mul (-I)
    have h2 : HasDerivAt (fun u : ℝ => Complex.exp (-I * (airyTheta u : ℂ)))
        ((I / (((π * airyMod t ^ 2 : ℝ) : ℂ))) * Complex.exp (-I * (airyTheta t : ℂ))) t := by
      refine hth.cexp.congr_deriv ?_
      push_cast; ring
    refine (h1.mul h2).congr_deriv ?_
    ring
  have hZ_lim : Tendsto Z atTop (𝓝 1) := by
    obtain ⟨CE, _, hE_asymp⟩ := (one_add_nicholsonErr_rpow_sub_one_isSymbol (-(1 / 2 : ℝ))).abs_le
    obtain ⟨CW, _, hW_asymp⟩ := phaseCorr_isSymbol.abs_le
    set Ctot : ℝ := (1 / 4 : ℝ) * (√π * (32 / 27 : ℝ) ^ (1 / 2 : ℝ)) + CE + CW
    have hbd : ∀ᶠ t in atTop, ‖Z t - 1‖ ≤ Ctot * t ^ (-(3 / 2 : ℝ)) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht1
      have htpos : 0 < t := by linarith
      have hAi := airyAi_neg_asymptotic htpos
      have hBi := airyBi_neg_asymptotic htpos
      have hcos : Real.cos (2 / 3 * t ^ (3 / 2 : ℝ) - π / 4) = Real.sin (airyTheta0 t) := by
        unfold airyTheta0
        rw [show (2 / 3 : ℝ) * t ^ (3 / 2 : ℝ) - π / 4 =
            ((2 / 3 : ℝ) * t ^ (3 / 2 : ℝ) + π / 4) - π / 2 by ring, Real.cos_sub_pi_div_two]
      have hsin : -Real.sin (2 / 3 * t ^ (3 / 2 : ℝ) - π / 4) = Real.cos (airyTheta0 t) := by
        unfold airyTheta0
        rw [show (2 / 3 : ℝ) * t ^ (3 / 2 : ℝ) - π / 4 =
            ((2 / 3 : ℝ) * t ^ (3 / 2 : ℝ) + π / 4) - π / 2 by ring,
          Real.sin_sub_pi_div_two, neg_neg]
      rw [hcos] at hAi
      have hBi' : |airyBi (-t) - 1 / √π * t ^ (-(1 / 4 : ℝ)) * Real.cos (airyTheta0 t)| ≤
          1 / 8 * t ^ (-(7 / 4 : ℝ)) := by
        rw [← hsin]; simpa [sub_neg_eq_add, mul_neg] using hBi
      have hexp0 : Complex.exp (I * ((π / 2 - airyTheta0 t : ℝ) : ℂ)) =
          ((Real.sin (airyTheta0 t) : ℝ) : ℂ) + I * ((Real.cos (airyTheta0 t) : ℝ) : ℂ) := by
        rw [mul_comm I, Complex.exp_ofReal_mul_I, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
        ring
      have hsqrt_pi : 1 / √π = π ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_neg Real.pi_pos.le, one_div]
      set L : ℂ := ((π ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (I * ((π / 2 - airyTheta0 t : ℝ) : ℂ))
      have hnum_err : ‖(((airyAi (-t) : ℝ) : ℂ) + I * ((airyBi (-t) : ℝ) : ℂ)) - L‖ ≤
          1 / 4 * t ^ (-(7 / 4 : ℝ)) := by
        have hdiff : (((airyAi (-t) : ℝ) : ℂ) + I * ((airyBi (-t) : ℝ) : ℂ)) - L =
            ((airyAi (-t) - 1 / √π * t ^ (-(1 / 4 : ℝ)) * Real.sin (airyTheta0 t) : ℝ) : ℂ) +
              I * ((airyBi (-t) - 1 / √π * t ^ (-(1 / 4 : ℝ)) * Real.cos (airyTheta0 t) : ℝ) : ℂ) := by
          dsimp [L]; rw [hexp0, hsqrt_pi]; push_cast; ring
        rw [hdiff]
        calc ‖_ + _‖
            ≤ ‖((airyAi (-t) - 1 / √π * t ^ (-(1 / 4 : ℝ)) * Real.sin (airyTheta0 t) : ℝ) : ℂ)‖ +
                ‖I * ((airyBi (-t) - 1 / √π * t ^ (-(1 / 4 : ℝ)) * Real.cos (airyTheta0 t) : ℝ) : ℂ)‖ :=
              norm_add_le _ _
          _ = |airyAi (-t) - 1 / √π * t ^ (-(1 / 4 : ℝ)) * Real.sin (airyTheta0 t)| +
                |airyBi (-t) - 1 / √π * t ^ (-(1 / 4 : ℝ)) * Real.cos (airyTheta0 t)| := by
              rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
                Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ 1 / 8 * t ^ (-(7 / 4 : ℝ)) + 1 / 8 * t ^ (-(7 / 4 : ℝ)) := add_le_add hAi hBi'
          _ = 1 / 4 * t ^ (-(7 / 4 : ℝ)) := by ring
      have hM_eq := airyMod_eq_rpow_one_add hNicholson htpos
      have hLM : L / (airyMod t : ℂ) =
          (((1 + nicholsonErr t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            Complex.exp (I * ((π / 2 - airyTheta0 t : ℝ) : ℂ)) := by
        have hpi0 : π ^ (-(1 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos Real.pi_pos _).ne'
        have ht0 : t ^ (-(1 / 4 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos htpos _).ne'
        have hE0 : 0 < 1 + nicholsonErr t := one_add_nicholsonErr_pos_of_pos hNicholson htpos
        have hrpow_inv : ((1 + nicholsonErr t) ^ (1 / 2 : ℝ))⁻¹ =
            (1 + nicholsonErr t) ^ (-(1 / 2 : ℝ)) := by
          rw [Real.rpow_neg hE0.le]
        have hcoeff : (π ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 4 : ℝ))) / airyMod t =
            (1 + nicholsonErr t) ^ (-(1 / 2 : ℝ)) := by
          rw [hM_eq, ← hrpow_inv]
          field_simp [hpi0, ht0]
        dsimp [L]
        rw [mul_div_right_comm, ← Complex.ofReal_div, hcoeff]
      have hM_low : (π ^ (-(1 / 2 : ℝ)) * (27 / 32 : ℝ) ^ (1 / 2 : ℝ)) * t ^ (-(1 / 4 : ℝ)) ≤
          airyMod t := by
        rw [hM_eq]
        have h1 : (27 / 32 : ℝ) ^ (1 / 2 : ℝ) ≤ (1 + nicholsonErr t) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) (one_add_nicholsonErr_ge_of_ge_one ht1) (by norm_num)
        calc (π ^ (-(1 / 2 : ℝ)) * (27 / 32 : ℝ) ^ (1 / 2 : ℝ)) * t ^ (-(1 / 4 : ℝ))
            = π ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 4 : ℝ)) * (27 / 32 : ℝ) ^ (1 / 2 : ℝ) := by ring
          _ ≤ π ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 4 : ℝ)) * (1 + nicholsonErr t) ^ (1 / 2 : ℝ) := by
              gcongr
      have hU1 : ‖U t - L / (airyMod t : ℂ)‖ ≤
          (1 / 4 : ℝ) * (√π * (32 / 27 : ℝ) ^ (1 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ)) := by
        rw [show U t - L / (airyMod t : ℂ) =
            ((((airyAi (-t) : ℝ) : ℂ) + I * ((airyBi (-t) : ℝ) : ℂ)) - L) / (airyMod t : ℂ) by
          dsimp [U]; ring, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (airyMod_pos t)]
        have hden_eq : (π ^ (-(1 / 2 : ℝ)) * (27 / 32 : ℝ) ^ (1 / 2 : ℝ))⁻¹ =
            √π * (32 / 27 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [mul_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg Real.pi_pos.le, neg_neg,
            ← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 27 / 32), inv_div]
        have hpow_div : t ^ (-(7 / 4 : ℝ)) / t ^ (-(1 / 4 : ℝ)) = t ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_sub htpos]; norm_num
        calc ‖(((airyAi (-t) : ℝ) : ℂ) + I * ((airyBi (-t) : ℝ) : ℂ)) - L‖ / airyMod t
            ≤ (1 / 4 * t ^ (-(7 / 4 : ℝ))) /
                ((π ^ (-(1 / 2 : ℝ)) * (27 / 32 : ℝ) ^ (1 / 2 : ℝ)) * t ^ (-(1 / 4 : ℝ))) :=
              div_le_div₀ (by positivity) hnum_err
                (mul_pos (mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (by positivity))
                  (Real.rpow_pos_of_pos htpos _)) hM_low
          _ = (1 / 4 : ℝ) * (π ^ (-(1 / 2 : ℝ)) * (27 / 32 : ℝ) ^ (1 / 2 : ℝ))⁻¹ *
                (t ^ (-(7 / 4 : ℝ)) / t ^ (-(1 / 4 : ℝ))) := by ring
          _ = (1 / 4 : ℝ) * (√π * (32 / 27 : ℝ) ^ (1 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ)) := by
              rw [hden_eq, hpow_div]
      have hU2 : ‖L / (airyMod t : ℂ) - Complex.exp (I * ((π / 2 - airyTheta0 t : ℝ) : ℂ))‖ ≤
          CE * t ^ (-(3 / 2 : ℝ)) := by
        rw [hLM, ← sub_one_mul, norm_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I, mul_one,
          ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        have hE1 := hE_asymp t ht1
        have htle : t ^ (-3 : ℝ) ≤ t ^ (-(3 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
        exact hE1.trans (mul_le_mul_of_nonneg_left htle (by linarith))
      have hexp_mul : Complex.exp (I * ((π / 2 - airyTheta0 t : ℝ) : ℂ)) *
          Complex.exp (-I * (airyTheta t : ℂ)) = Complex.exp (I * (phaseCorr t : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        unfold airyTheta
        push_cast; ring
      have hphase_exp : ‖Complex.exp (I * (phaseCorr t : ℂ)) - 1‖ ≤ CW * t ^ (-(3 / 2 : ℝ)) := by
        let f : ℝ → ℂ := fun u => Complex.exp (I * (u : ℂ))
        have hf : ∀ u : ℝ, DifferentiableAt ℝ f u := fun u =>
          (((hasDerivAt_id u).ofReal_comp.const_mul I).cexp).differentiableAt
        have hnorm_deriv : ∀ u : ℝ, ‖deriv f u‖ ≤ 1 := fun u => by
          have hd : HasDerivAt f (I * Complex.exp (I * (u : ℂ))) u :=
            (((hasDerivAt_id u).ofReal_comp.const_mul I).cexp).congr_deriv (by simp [mul_comm])
          rw [hd.deriv, norm_mul, Complex.norm_I, one_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I]
        have hmvt := convex_univ.norm_image_sub_le_of_norm_deriv_le (fun u _ => hf u)
          (fun u _ => hnorm_deriv u) (Set.mem_univ 0) (Set.mem_univ (phaseCorr t))
        simp only [f, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_zero,
          Real.norm_eq_abs] at hmvt
        calc ‖Complex.exp (I * (phaseCorr t : ℂ)) - 1‖ ≤ 1 * |phaseCorr t| := hmvt
          _ = |phaseCorr t| := one_mul _
          _ ≤ CW * t ^ (-(3 / 2 : ℝ)) := by simpa using hW_asymp t ht1
      have hZ_split : Z t - 1 =
          ((U t - L / (airyMod t : ℂ)) +
            (L / (airyMod t : ℂ) - Complex.exp (I * ((π / 2 - airyTheta0 t : ℝ) : ℂ)))) *
            Complex.exp (-I * (airyTheta t : ℂ)) + (Complex.exp (I * (phaseCorr t : ℂ)) - 1) := by
        dsimp [Z]
        rw [← hexp_mul]
        ring
      have hnorm_exp_th : ‖Complex.exp (-I * (airyTheta t : ℂ))‖ = 1 := by
        rw [show -I * (airyTheta t : ℂ) = ((-airyTheta t : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      rw [hZ_split]
      calc ‖_ + _‖
          ≤ ‖(U t - L / (airyMod t : ℂ)) +
              (L / (airyMod t : ℂ) - Complex.exp (I * ((π / 2 - airyTheta0 t : ℝ) : ℂ)))‖ *
              ‖Complex.exp (-I * (airyTheta t : ℂ))‖ +
              ‖Complex.exp (I * (phaseCorr t : ℂ)) - 1‖ := by
            rw [← norm_mul]; exact norm_add_le _ _
        _ ≤ (‖U t - L / (airyMod t : ℂ)‖ +
              ‖L / (airyMod t : ℂ) - Complex.exp (I * ((π / 2 - airyTheta0 t : ℝ) : ℂ))‖) * 1 +
              ‖Complex.exp (I * (phaseCorr t : ℂ)) - 1‖ := by
            rw [hnorm_exp_th]; gcongr; exact norm_add_le _ _
        _ ≤ ((1 / 4 : ℝ) * (√π * (32 / 27 : ℝ) ^ (1 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ)) +
              CE * t ^ (-(3 / 2 : ℝ))) + CW * t ^ (-(3 / 2 : ℝ)) := by
            rw [mul_one]; exact add_le_add (add_le_add hU1 hU2) hphase_exp
        _ = Ctot * t ^ (-(3 / 2 : ℝ)) := by dsimp [Ctot]; ring
    refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      hbd ?_)
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul Ctot
  have hZ_const : ∀ y ≥ x, Z y = Z x := fun y hy => by
    have hcont : ContinuousOn Z (Set.Icc x y) := fun t ht =>
      (hZ_deriv t (lt_of_lt_of_le hx ht.1)).continuousAt.continuousWithinAt
    have hd : ∀ t ∈ Set.Ico x y, HasDerivWithinAt Z 0 (Set.Ici t) t := fun t ht =>
      (hZ_deriv t (lt_of_lt_of_le hx ht.1)).hasDerivWithinAt
    exact constant_of_has_deriv_right_zero hcont hd y ⟨hy, le_rfl⟩
  have hZx_eq_one : Z x = 1 := by
    have hconst_lim : Tendsto Z atTop (𝓝 (Z x)) :=
      tendsto_const_nhds.congr' ((eventually_ge_atTop x).mono fun y hy => (hZ_const y hy).symm)
    exact tendsto_nhds_unique hconst_lim hZ_lim
  have hU_eq : ((airyAi (-x) : ℝ) : ℂ) + I * ((airyBi (-x) : ℝ) : ℂ) =
      (airyMod x : ℂ) * Complex.exp (I * (airyTheta x : ℂ)) := by
    have hm_ne : (airyMod x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (airyMod_pos x).ne'
    have hZ1 : U x * Complex.exp (-I * (airyTheta x : ℂ)) = 1 := hZx_eq_one
    have hU' : U x = Complex.exp (I * (airyTheta x : ℂ)) := by
      calc U x = (U x * Complex.exp (-I * (airyTheta x : ℂ))) * Complex.exp (I * (airyTheta x : ℂ)) := by
            rw [mul_assoc, ← Complex.exp_add]; simp
        _ = Complex.exp (I * (airyTheta x : ℂ)) := by rw [hZ1, one_mul]
    dsimp [U] at hU'
    exact (div_eq_iff hm_ne).mp hU' |>.trans (mul_comm _ _)
  have hre := congrArg Complex.re hU_eq
  have him := congrArg Complex.im hU_eq
  rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_comm I, Complex.exp_ofReal_mul_I_re] at hre
  rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_comm I, Complex.exp_ofReal_mul_I_im] at him
  exact ⟨by linarith, by linarith⟩

theorem airy_neg_phase_rep_theta0 {x : ℝ} (hx : 0 < x) :
    airyAi (-x) = airyMod x * Real.sin (airyTheta0 x + phaseCorr x) ∧
      airyBi (-x) = airyMod x * Real.cos (airyTheta0 x + phaseCorr x) := by
  obtain ⟨hA, hB⟩ := airy_neg_phase_rep hNicholson hx
  have hth : airyTheta x = π / 2 - (airyTheta0 x + phaseCorr x) := by unfold airyTheta; ring
  rw [hth, Real.cos_pi_div_two_sub] at hA
  rw [hth, Real.sin_pi_div_two_sub] at hB
  exact ⟨hA, hB⟩

/-- **Lemma W.2(b)**: `α := airyTheta` is continuous on `(0, ∞)`, satisfies
`Ai = M cos α`, `Bi = M sin α`, and `α' = -1/(π M²)`. -/
theorem airy_W2b :
    ContinuousOn airyTheta (Set.Ioi 0) ∧
      ∀ x > 0, airyAi (-x) = airyMod x * Real.cos (airyTheta x) ∧
        airyBi (-x) = airyMod x * Real.sin (airyTheta x) ∧
        HasDerivAt airyTheta (-(1 / (π * airyMod x ^ 2))) x := by
  refine ⟨fun x hx => (hasDerivAt_airyTheta_pos hNicholson hx).continuousAt.continuousWithinAt,
    fun x hx => ?_⟩
  obtain ⟨hA, hB⟩ := airy_neg_phase_rep hNicholson hx
  exact ⟨hA, hB, hasDerivAt_airyTheta_pos hNicholson hx⟩

/-! ### Proposition W.5: exact oscillation extraction with `𝒮` envelopes -/

/-- **Proposition W.5, identity for `Ai(-x)`**: for all `x > 0`,
`Ai(-x) = π^{-1/2} x^{-1/4} (sin ϑ(x) P₁(x) + cos ϑ(x) Q₁(x))`. -/
theorem airy_neg_osc_extract {x : ℝ} (hx : 0 < x) :
    airyAi (-x) = π ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 4 : ℝ)) *
      (Real.sin (airyTheta0 x) * airyP1 x + Real.cos (airyTheta0 x) * airyQ1 x) := by
  obtain ⟨hA, _⟩ := airy_neg_phase_rep_theta0 hNicholson hx
  rw [hA, airyMod_eq_rpow_one_add hNicholson hx, Real.sin_add]
  unfold airyP1 airyQ1
  ring

/-- **Proposition W.5, identity for `Ai'(-x)`**: for all `x > 0`,
`Ai'(-x) = -π^{-1/2} x^{1/4} (cos ϑ(x) P₂(x) + sin ϑ(x) Q₂(x))`. -/
theorem airyDeriv_neg_osc_extract {x : ℝ} (hx : 0 < x) :
    airyAi' (-x) = -π ^ (-(1 / 2 : ℝ)) * x ^ (1 / 4 : ℝ) *
      (Real.cos (airyTheta0 x) * airyP2 x + Real.sin (airyTheta0 x) * airyQ2 x) := by
  have hw2c := airyDeriv_neg_w2c x
  have hA := airy_neg_osc_extract hNicholson hx
  obtain ⟨_, hB⟩ := airy_neg_phase_rep_theta0 hNicholson hx
  have hlog : -(_root_.deriv airyMod x / airyMod x) = x ^ (1 / 2 : ℝ) * airyRho x := by
    rw [logDeriv_airyMod_eq hNicholson hx]
    unfold airyRho
    have hxpow : x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hx, add_neg_cancel, Real.rpow_zero]
    calc -( -(1 / (4 * x)) + _root_.deriv nicholsonErr x / (2 * (1 + nicholsonErr x)) )
        = 1 * (1 / (4 * x) - _root_.deriv nicholsonErr x / (2 * (1 + nicholsonErr x))) := by ring
      _ = (x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ))) * _ := by rw [hxpow]
      _ = x ^ (1 / 2 : ℝ) * (x ^ (-(1 / 2 : ℝ)) * _) := by ring
  have hM_inv : 1 / (π * airyMod x) =
      π ^ (-(1 / 2 : ℝ)) * x ^ (1 / 4 : ℝ) * (1 + nicholsonErr x) ^ (-(1 / 2 : ℝ)) := by
    rw [airyMod_eq_rpow_one_add hNicholson hx]
    have hE0 := one_add_nicholsonErr_pos_of_pos hNicholson hx
    have hpi : π ^ (-(1 / 2 : ℝ)) * π ^ (1 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add Real.pi_pos, neg_add_cancel, Real.rpow_zero]
    have hpi1 : π ^ (-(1 / 2 : ℝ)) * π ^ (-(1 / 2 : ℝ)) = π⁻¹ := by
      rw [← Real.rpow_add Real.pi_pos]; norm_num; exact Real.rpow_neg_one π
    have hxpow : x ^ (1 / 4 : ℝ) * x ^ (-(1 / 4 : ℝ)) = 1 := by
      rw [← Real.rpow_add hx, add_neg_cancel, Real.rpow_zero]
    have hEpow : (1 + nicholsonErr x) ^ (-(1 / 2 : ℝ)) * (1 + nicholsonErr x) ^ (1 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hE0, neg_add_cancel, Real.rpow_zero]
    have hm_ne : π * (π ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 4 : ℝ)) *
        (1 + nicholsonErr x) ^ (1 / 2 : ℝ)) ≠ 0 := by
      positivity
    rw [div_eq_iff hm_ne]
    calc (1 : ℝ) = (π * π⁻¹) * (x ^ (1 / 4 : ℝ) * x ^ (-(1 / 4 : ℝ))) *
          ((1 + nicholsonErr x) ^ (-(1 / 2 : ℝ)) * (1 + nicholsonErr x) ^ (1 / 2 : ℝ)) := by
          rw [mul_inv_cancel₀ Real.pi_pos.ne', hxpow, hEpow]; ring
      _ = _ := by rw [← hpi1]; ring
  have hB_term : airyBi (-x) / (π * airyMod x ^ 2) =
      π ^ (-(1 / 2 : ℝ)) * x ^ (1 / 4 : ℝ) * (1 + nicholsonErr x) ^ (-(1 / 2 : ℝ)) *
        (Real.cos (airyTheta0 x) * Real.cos (phaseCorr x) -
          Real.sin (airyTheta0 x) * Real.sin (phaseCorr x)) := by
    have hm_ne : airyMod x ≠ 0 := (airyMod_pos x).ne'
    have h1 : airyBi (-x) / (π * airyMod x ^ 2) = (1 / (π * airyMod x)) * Real.cos (airyTheta0 x + phaseCorr x) := by
      rw [hB]; field_simp
    rw [h1, hM_inv, Real.cos_add]
  have hx14 : x ^ (1 / 2 : ℝ) * x ^ (-(1 / 4 : ℝ)) = x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hx]; norm_num
  rw [hw2c, hlog, hA, hB_term]
  unfold airyP2 airyQ2
  calc x ^ (1 / 2 : ℝ) * airyRho x * (π ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 4 : ℝ)) *
        (Real.sin (airyTheta0 x) * airyP1 x + Real.cos (airyTheta0 x) * airyQ1 x)) -
      π ^ (-(1 / 2 : ℝ)) * x ^ (1 / 4 : ℝ) * (1 + nicholsonErr x) ^ (-(1 / 2 : ℝ)) *
        (Real.cos (airyTheta0 x) * Real.cos (phaseCorr x) -
          Real.sin (airyTheta0 x) * Real.sin (phaseCorr x))
      = π ^ (-(1 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * x ^ (-(1 / 4 : ℝ))) * airyRho x *
          (Real.sin (airyTheta0 x) * airyP1 x + Real.cos (airyTheta0 x) * airyQ1 x) -
        π ^ (-(1 / 2 : ℝ)) * x ^ (1 / 4 : ℝ) * (1 + nicholsonErr x) ^ (-(1 / 2 : ℝ)) *
          (Real.cos (airyTheta0 x) * Real.cos (phaseCorr x) -
            Real.sin (airyTheta0 x) * Real.sin (phaseCorr x)) := by ring
    _ = -π ^ (-(1 / 2 : ℝ)) * x ^ (1 / 4 : ℝ) *
          (Real.cos (airyTheta0 x) * ((1 + nicholsonErr x) ^ (-(1 / 2 : ℝ)) * Real.cos (phaseCorr x) -
            airyRho x * airyQ1 x) +
          Real.sin (airyTheta0 x) * (-(1 + nicholsonErr x) ^ (-(1 / 2 : ℝ)) * Real.sin (phaseCorr x) -
            airyRho x * airyP1 x)) := by rw [hx14]; ring

end GivenNicholson

/-! ### Unconditional symbol memberships in Proposition W.5 -/

private lemma cos_phaseCorr_sub_one_isSymbol : IsSymbol 3 (fun x => Real.cos (phaseCorr x) - 1) := by
  let G : ℝ → ℝ := fun s => Real.cos s - 1
  have hG : ContDiff ℝ ∞ G := (Real.contDiff_cos.sub contDiff_const).of_le le_top
  have hG0 : G 0 = 0 := by simp [G]
  have hG'0 : _root_.deriv G 0 = 0 := by
    have hd : HasDerivAt G (-Real.sin 0) 0 := (Real.hasDerivAt_cos 0).sub_const (1 : ℝ)
    rw [hd.deriv]; simp
  simpa [G, show (2 : ℝ) * (3 / 2 : ℝ) = 3 by norm_num] using
    phaseCorr_isSymbol.comp_vanish_deriv_of_contDiff (by norm_num) hG hG0 hG'0

private lemma cos_phaseCorr_isSymbol : IsSymbol 0 (fun x => Real.cos (phaseCorr x)) := by
  have h := cos_phaseCorr_sub_one_isSymbol.add (IsSymbol.const le_rfl (1 : ℝ))
  have hmin : min (3 : ℝ) 0 = 0 := by norm_num
  rw [hmin] at h
  exact h.congr fun x _ => by ring

private lemma sin_phaseCorr_isSymbol : IsSymbol (3 / 2) (fun x => Real.sin (phaseCorr x)) := by
  have h := phaseCorr_isSymbol.comp_sub_zero_of_contDiff (by norm_num) (Real.contDiff_sin.of_le le_top)
  simpa using h

/-- **Proposition W.5**: `P₁ - 1 ∈ 𝒮_3`. -/
theorem airyP1_sub_one_isSymbol : IsSymbol 3 (fun x => airyP1 x - 1) := by
  have h1 := (one_add_nicholsonErr_rpow_sub_one_isSymbol (1 / 2)).mul cos_phaseCorr_isSymbol
  rw [add_zero] at h1
  have h := h1.add cos_phaseCorr_sub_one_isSymbol
  rw [min_self] at h
  exact h.congr fun x _ => by unfold airyP1; ring

/-- **Proposition W.5**: `Q₁ ∈ 𝒮_{3/2}`. -/
theorem airyQ1_isSymbol : IsSymbol (3 / 2) airyQ1 := by
  have h := (one_add_nicholsonErr_rpow_isSymbol (1 / 2)).mul sin_phaseCorr_isSymbol
  rw [zero_add] at h
  exact h.congr fun x _ => by unfold airyQ1; rfl

private lemma airyRho_isSymbol : IsSymbol (3 / 2) airyRho := by
  have h1 : IsSymbol 1 (fun x : ℝ => (1 / 4 : ℝ) * x⁻¹) := IsSymbol.inv.const_mul _
  have hEd : IsSymbol 4 (_root_.deriv nicholsonErr) := by
    simpa only [show (3 : ℝ) + 1 = 4 by norm_num] using
      nicholsonErr_isSymbol.deriv isOpen_Ioi
        (fun _ h => by rw [Set.mem_Ioi]; linarith [Set.mem_Ici.mp h]) contDiffOn_nicholsonErr_Ioi
  have h2 : IsSymbol 4 (fun x => (1 / 2 : ℝ) * _root_.deriv nicholsonErr x * (1 + nicholsonErr x)⁻¹) := by
    simpa only [add_zero] using (hEd.const_mul (1 / 2)).mul one_add_nicholsonErr_inv_isSymbol
  have hsub := h1.sub h2
  have hmin : min (1 : ℝ) 4 = 1 := by norm_num
  rw [hmin] at hsub
  have hrpow : IsSymbol (1 / 2) (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) := IsSymbol.rpow_neg (1 / 2)
  have hprod := hrpow.mul hsub
  rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num] at hprod
  refine hprod.congr fun x _ => ?_
  unfold airyRho
  field_simp

/-- **Proposition W.5**: `P₂ - 1 ∈ 𝒮_3`. -/
theorem airyP2_sub_one_isSymbol : IsSymbol 3 (fun x => airyP2 x - 1) := by
  have h1 := ((one_add_nicholsonErr_rpow_sub_one_isSymbol (-(1 / 2))).mul cos_phaseCorr_isSymbol).add
    cos_phaseCorr_sub_one_isSymbol
  rw [add_zero, min_self] at h1
  have h2 := airyRho_isSymbol.mul airyQ1_isSymbol
  rw [show (3 / 2 : ℝ) + (3 / 2 : ℝ) = 3 by norm_num] at h2
  have h := h1.sub h2
  rw [min_self] at h
  exact h.congr fun x _ => by unfold airyP2; ring

/-- **Proposition W.5**: `Q₂ ∈ 𝒮_{3/2}`. -/
theorem airyQ2_isSymbol : IsSymbol (3 / 2) airyQ2 := by
  have h1 := ((one_add_nicholsonErr_rpow_isSymbol (-(1 / 2))).mul sin_phaseCorr_isSymbol).neg
  rw [zero_add] at h1
  have hP1 : IsSymbol 0 airyP1 := by
    have hp := airyP1_sub_one_isSymbol.add (IsSymbol.const le_rfl (1 : ℝ))
    have hmin : min (3 : ℝ) 0 = 0 := by norm_num
    rw [hmin] at hp
    exact hp.congr fun x _ => by ring
  have h2 := airyRho_isSymbol.mul hP1
  rw [add_zero] at h2
  have h := h1.sub h2
  rw [min_self] at h
  exact h.congr fun x _ => by unfold airyQ2; ring

/-- **Proposition W.5, two-term asymptotic corollary**:
`Ai(-x) = π^{-1/2} x^{-1/4} (sin ϑ(x) - (5/48) x^{-3/2} cos ϑ(x) + O(x^{-3}))` for `x ≥ 1`. -/
theorem airyAi_neg_two_term_asymp
    (hNicholson : ∀ x > 0, airyAi (-x) ^ 2 + airyBi (-x) ^ 2 = nicholsonIntegral x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ 1,
      |airyAi (-x) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 4 : ℝ)) *
        (Real.sin (airyTheta0 x) - (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ)) * Real.cos (airyTheta0 x))| ≤
        C * x ^ (-(13 / 4 : ℝ)) := by
  obtain ⟨CP1, hCP1, hP1bd⟩ := airyP1_sub_one_isSymbol.abs_le
  obtain ⟨CE, hCE, hEbd⟩ := (one_add_nicholsonErr_rpow_sub_one_isSymbol (1 / 2)).abs_le
  obtain ⟨CW, hCW, hWbd⟩ := phaseCorr_isSymbol.abs_le
  obtain ⟨CWa, hCWa, hWa⟩ := phaseCorr_asymp
  set C : ℝ := π ^ (-(1 / 2 : ℝ)) * (CP1 + CE * CW + CW ^ 2 + CWa)
  refine ⟨C, by positivity, fun x hx => ?_⟩
  have hxpos : 0 < x := by linarith
  have hsin_diff : ∀ u : ℝ, |Real.sin u - u| ≤ u ^ 2 := fun u => by
    have hmvt : |Real.sin u - u| ≤ |u| * |u| := by
      let g : ℝ → ℝ := fun t => Real.sin t - t
      have hg : ∀ t : ℝ, DifferentiableAt ℝ g t := fun t =>
        ((Real.hasDerivAt_sin t).sub (hasDerivAt_id t)).differentiableAt
      have hderiv_bd : ∀ t ∈ Set.Icc (min 0 u) (max 0 u), |deriv g t| ≤ |u| := fun t ht => by
        have hd : deriv g t = Real.cos t - 1 := ((Real.hasDerivAt_sin t).sub (hasDerivAt_id t)).deriv
        rw [hd]
        have hcos_lip := Real.abs_cos_sub_cos_le t 0
        rw [Real.cos_zero, sub_zero] at hcos_lip
        have ht_le : |t| ≤ |u| := by
          rcases le_or_gt 0 u with hu | hu
          · rw [min_eq_left hu, max_eq_right hu] at ht
            rw [abs_of_nonneg ht.1, abs_of_nonneg hu]; exact ht.2
          · rw [min_eq_right hu.le, max_eq_left hu.le] at ht
            rw [abs_of_nonpos ht.2, abs_of_nonpos hu.le]; linarith [ht.1]
        exact hcos_lip.trans ht_le
      rcases le_or_gt 0 u with hu | hu
      · have hm := (convex_Icc (min 0 u) (max 0 u)).norm_image_sub_le_of_norm_deriv_le
          (fun t _ => hg t) hderiv_bd ⟨min_le_left 0 u, le_max_left 0 u⟩ ⟨min_le_right 0 u, le_max_right 0 u⟩
        simpa [g] using hm
      · have hm := (convex_Icc (min 0 u) (max 0 u)).norm_image_sub_le_of_norm_deriv_le
          (fun t _ => hg t) hderiv_bd ⟨min_le_right 0 u, le_max_right 0 u⟩ ⟨min_le_left 0 u, le_max_left 0 u⟩
        simpa [g, abs_sub_comm] using hm
    simpa [sq, abs_mul_abs_self] using hmvt
  have hQ1 : |airyQ1 x + (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ))| ≤
      (CE * CW + CW ^ 2 + CWa) * x ^ (-3 : ℝ) := by
    have hsplit : airyQ1 x + (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ)) =
        ((1 + nicholsonErr x) ^ (1 / 2 : ℝ) - 1) * Real.sin (phaseCorr x) +
          (Real.sin (phaseCorr x) - phaseCorr x) + (phaseCorr x + (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ))) := by
      unfold airyQ1; ring
    have hsin_le : |Real.sin (phaseCorr x)| ≤ |phaseCorr x| := Real.abs_sin_le_abs
    have hpow3 : x ^ (-(9 / 2 : ℝ)) ≤ x ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    have hpow_sq : (CW * x ^ (-(3 / 2 : ℝ))) ^ 2 = CW ^ 2 * x ^ (-3 : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (x ^ (-(3 / 2 : ℝ))) 2, ← Real.rpow_mul hxpos.le]; norm_num
    have hpow_mul : x ^ (-3 : ℝ) * x ^ (-(3 / 2 : ℝ)) ≤ x ^ (-3 : ℝ) := by
      have hx1 : x ^ (-(3 / 2 : ℝ)) ≤ 1 := by
        simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one hx (by norm_num : -(3 / 2 : ℝ) ≤ 0)
      calc x ^ (-3 : ℝ) * x ^ (-(3 / 2 : ℝ)) ≤ x ^ (-3 : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hx1 (Real.rpow_nonneg hxpos.le _)
        _ = x ^ (-3 : ℝ) := mul_one _
    have h1 : |((1 + nicholsonErr x) ^ (1 / 2 : ℝ) - 1) * Real.sin (phaseCorr x)| ≤
        CE * CW * x ^ (-3 : ℝ) := by
      rw [abs_mul]
      calc |((1 + nicholsonErr x) ^ (1 / 2 : ℝ) - 1)| * |Real.sin (phaseCorr x)|
          ≤ (CE * x ^ (-3 : ℝ)) * |phaseCorr x| :=
            mul_le_mul (hEbd x hx) hsin_le (abs_nonneg _) (by positivity)
        _ ≤ (CE * x ^ (-3 : ℝ)) * (CW * x ^ (-(3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left (hWbd x hx) (by positivity)
        _ = CE * CW * (x ^ (-3 : ℝ) * x ^ (-(3 / 2 : ℝ))) := by ring
        _ ≤ CE * CW * x ^ (-3 : ℝ) := by gcongr
    have h2 : |Real.sin (phaseCorr x) - phaseCorr x| ≤ CW ^ 2 * x ^ (-3 : ℝ) := by
      refine (hsin_diff _).trans ?_
      calc phaseCorr x ^ 2 = |phaseCorr x| ^ 2 := (sq_abs _).symm
        _ ≤ (CW * x ^ (-(3 / 2 : ℝ))) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hWbd x hx) 2
        _ = CW ^ 2 * x ^ (-3 : ℝ) := hpow_sq
    have h3 : |phaseCorr x + (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ))| ≤ CWa * x ^ (-3 : ℝ) :=
      (hWa x hx).trans (mul_le_mul_of_nonneg_left hpow3 hCWa)
    rw [hsplit]
    calc |_ + _ + _| ≤ |((1 + nicholsonErr x) ^ (1 / 2 : ℝ) - 1) * Real.sin (phaseCorr x)| +
            |Real.sin (phaseCorr x) - phaseCorr x| +
            |phaseCorr x + (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ))| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by linarith
  have hextract := airy_neg_osc_extract hNicholson hxpos
  have hdiff : airyAi (-x) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 4 : ℝ)) *
      (Real.sin (airyTheta0 x) - (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ)) * Real.cos (airyTheta0 x)) =
      π ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 4 : ℝ)) *
        (Real.sin (airyTheta0 x) * (airyP1 x - 1) +
          Real.cos (airyTheta0 x) * (airyQ1 x + (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ)))) := by
    rw [hextract]; ring
  rw [hdiff, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos Real.pi_pos _),
    abs_of_pos (Real.rpow_pos_of_pos hxpos _)]
  have hbr : |Real.sin (airyTheta0 x) * (airyP1 x - 1) +
      Real.cos (airyTheta0 x) * (airyQ1 x + (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ)))| ≤
      (CP1 + CE * CW + CW ^ 2 + CWa) * x ^ (-3 : ℝ) := by
    calc |Real.sin (airyTheta0 x) * (airyP1 x - 1) +
          Real.cos (airyTheta0 x) * (airyQ1 x + (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ)))|
        ≤ |Real.sin (airyTheta0 x) * (airyP1 x - 1)| +
            |Real.cos (airyTheta0 x) * (airyQ1 x + (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ)))| :=
          abs_add_le _ _
      _ ≤ 1 * |airyP1 x - 1| + 1 * |airyQ1 x + (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ))| := by
          rw [abs_mul, abs_mul]
          exact add_le_add
            (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _))
            (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _))
      _ ≤ CP1 * x ^ (-3 : ℝ) + (CE * CW + CW ^ 2 + CWa) * x ^ (-3 : ℝ) := by
          rw [one_mul, one_mul]; exact add_le_add (hP1bd x hx) hQ1
      _ = (CP1 + CE * CW + CW ^ 2 + CWa) * x ^ (-3 : ℝ) := by ring
  have hpow13 : x ^ (-(1 / 4 : ℝ)) * x ^ (-3 : ℝ) = x ^ (-(13 / 4 : ℝ)) := by
    rw [← Real.rpow_add hxpos]; norm_num
  calc π ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 4 : ℝ)) *
        |Real.sin (airyTheta0 x) * (airyP1 x - 1) +
          Real.cos (airyTheta0 x) * (airyQ1 x + (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ)))|
      ≤ π ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 4 : ℝ)) *
          ((CP1 + CE * CW + CW ^ 2 + CWa) * x ^ (-3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hbr (by positivity)
    _ = C * (x ^ (-(1 / 4 : ℝ)) * x ^ (-3 : ℝ)) := by dsimp [C]; ring
    _ = C * x ^ (-(13 / 4 : ℝ)) := by rw [hpow13]

/-! ### Proposition W.6 (`(CR.14)`): all-order symbol decomposition -/

/-- Inherited `(CR.21)` coefficient hypotheses for Proposition W.6 (`(CR.14)`). -/
structure CardinalResolventCoeffs (x₀ : ℝ) (q A B C : ℝ → ℝ) : Prop where
  hx₀ : 1 ≤ x₀
  hq : IsWeightedSymbolOn x₀ 0 q q
  hA : IsWeightedSymbolOn x₀ 2 q (fun x => A x - q x / x)
  hB : IsWeightedSymbolOn x₀ 3 q B
  hC : IsWeightedSymbolOn x₀ 3 q (fun x => C x - q x / x ^ 2)

/-- Non-vacuity witness for `CardinalResolventCoeffs`: `x₀ = 1`, `q = 1`, `A = 1/x`, `B = 0`,
`C = 1/x²`. -/
theorem cardinalResolventCoeffs_nonvacuous :
    CardinalResolventCoeffs 1 (fun _ => 1) (fun x => 1 / x) (fun _ => 0) (fun x => 1 / x ^ 2) where
  hx₀ := le_rfl
  hq := by
    have h := IsSymbol.const le_rfl (1 : ℝ)
    exact ⟨h.1, fun j => by
      obtain ⟨C, hC, hb⟩ := h.2 j
      exact ⟨C, hC, fun x hx => by simpa using hb x hx⟩⟩
  hA := (IsWeightedSymbolOn.zero 1 2 (fun _ => 1)).congr fun x _ => by simp
  hB := IsWeightedSymbolOn.zero 1 3 (fun _ => 1)
  hC := (IsWeightedSymbolOn.zero 1 3 (fun _ => 1)).congr fun x _ => by simp

/-- **Proposition W.6 (`(CR.14)`)**: all-order weighted symbol decomposition of
`S_h(-x) = A(x) Ai(-x)² + B(x) Ai(-x) Ai'(-x) + C(x) Ai'(-x)²` on `[x₀, ∞)`. -/
theorem cardinal_symbol_decomp
    (hNicholson : ∀ x > 0, airyAi (-x) ^ 2 + airyBi (-x) ^ 2 = nicholsonIntegral x)
    {x₀ : ℝ} {q A B C : ℝ → ℝ} (hCR : CardinalResolventCoeffs x₀ q A B C) :
    ∃ D₀ D₁ D₂ : ℝ → ℝ,
      IsWeightedSymbolOn x₀ (5 / 2) q D₀ ∧
      IsWeightedSymbolOn x₀ (5 / 2) q D₁ ∧
      IsWeightedSymbolOn x₀ (5 / 2) q D₂ ∧
      ∀ x ≥ x₀,
        A x * airyAi (-x) ^ 2 + B x * airyAi (-x) * airyAi' (-x) + C x * airyAi' (-x) ^ 2 =
          q x / (π * x ^ (3 / 2 : ℝ)) + D₀ x +
            D₁ x * Real.cos (2 * airyTheta0 x) + D₂ x * Real.sin (2 * airyTheta0 x) := by
  have hx₀pos : 0 < x₀ := by linarith [hCR.hx₀]
  let δA : ℝ → ℝ := fun x => A x - q x / x
  let δC : ℝ → ℝ := fun x => C x - q x / x ^ 2
  let δP₁ : ℝ → ℝ := fun x => airyP1 x - 1
  let δP₂ : ℝ → ℝ := fun x => airyP2 x - 1
  let Δ₁ : ℝ → ℝ := fun x => 2 * δP₁ x + δP₁ x ^ 2
  let Δ₂ : ℝ → ℝ := fun x => 2 * δP₂ x + δP₂ x ^ 2
  have hP1s : IsSymbolOn x₀ 0 airyP1 := by
    have h := (airyP1_sub_one_isSymbol.add (IsSymbol.const le_rfl 1)).mono_domain hCR.hx₀
    rw [show min (3 : ℝ) 0 = 0 by norm_num] at h
    exact h.congr fun x _ => by ring
  have hP2s : IsSymbolOn x₀ 0 airyP2 := by
    have h := (airyP2_sub_one_isSymbol.add (IsSymbol.const le_rfl 1)).mono_domain hCR.hx₀
    rw [show min (3 : ℝ) 0 = 0 by norm_num] at h
    exact h.congr fun x _ => by ring
  have hQ1s : IsSymbolOn x₀ (3 / 2) airyQ1 := airyQ1_isSymbol.mono_domain hCR.hx₀
  have hQ2s : IsSymbolOn x₀ (3 / 2) airyQ2 := airyQ2_isSymbol.mono_domain hCR.hx₀
  have hQ1_0 : IsSymbolOn x₀ 0 airyQ1 := hQ1s.mono_exp hx₀pos (by norm_num)
  have hQ2_0 : IsSymbolOn x₀ 0 airyQ2 := hQ2s.mono_exp hx₀pos (by norm_num)
  have hΔ₁ : IsSymbolOn x₀ 3 Δ₁ := by
    have hd1 := airyP1_sub_one_isSymbol.mono_domain hCR.hx₀
    have h := (hd1.const_mul 2).add hx₀pos (hd1.pow hx₀pos 2)
    rw [show min (3 : ℝ) ((2 : ℕ) * 3) = 3 by norm_num] at h
    exact h
  have hΔ₂ : IsSymbolOn x₀ 3 Δ₂ := by
    have hd2 := airyP2_sub_one_isSymbol.mono_domain hCR.hx₀
    have h := (hd2.const_mul 2).add hx₀pos (hd2.pow hx₀pos 2)
    rw [show min (3 : ℝ) ((2 : ℕ) * 3) = 3 by norm_num] at h
    exact h
  have hQ1sq : IsSymbolOn x₀ 3 (fun x => airyQ1 x ^ 2) := by
    simpa only [show ((2 : ℕ) : ℝ) * (3 / 2 : ℝ) = 3 by norm_num] using hQ1s.pow hx₀pos 2
  have hQ2sq : IsSymbolOn x₀ 3 (fun x => airyQ2 x ^ 2) := by
    simpa only [show ((2 : ℕ) : ℝ) * (3 / 2 : ℝ) = 3 by norm_num] using hQ2s.pow hx₀pos 2
  have hP1sq : IsSymbolOn x₀ 0 (fun x => airyP1 x ^ 2) := by
    simpa using hP1s.pow hx₀pos 2
  have hP2sq : IsSymbolOn x₀ 0 (fun x => airyP2 x ^ 2) := by
    simpa using hP2s.pow hx₀pos 2
  have hQ1sq_0 : IsSymbolOn x₀ 0 (fun x => airyQ1 x ^ 2) := hQ1sq.mono_exp hx₀pos (by norm_num)
  have hQ2sq_0 : IsSymbolOn x₀ 0 (fun x => airyQ2 x ^ 2) := hQ2sq.mono_exp hx₀pos (by norm_num)
  have hP1Q1 : IsSymbolOn x₀ (3 / 2) (fun x => airyP1 x * airyQ1 x) := by
    simpa using hP1s.mul hx₀pos hQ1s
  have hP2Q2 : IsSymbolOn x₀ (3 / 2) (fun x => airyP2 x * airyQ2 x) := by
    simpa using hP2s.mul hx₀pos hQ2s
  have hP1Q1_0 : IsSymbolOn x₀ 0 (fun x => airyP1 x * airyQ1 x) := hP1Q1.mono_exp hx₀pos (by norm_num)
  have hP2Q2_0 : IsSymbolOn x₀ 0 (fun x => airyP2 x * airyQ2 x) := hP2Q2.mono_exp hx₀pos (by norm_num)
  have hxr32 : IsSymbolOn x₀ (3 / 2) (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) := IsSymbolOn.rpow_neg hx₀pos _
  have hxr12 : IsSymbolOn x₀ (1 / 2) (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) := IsSymbolOn.rpow_neg hx₀pos _
  have hxp12 : IsSymbolOn x₀ (-(1 / 2)) (fun x : ℝ => x ^ (1 / 2 : ℝ)) := IsSymbolOn.rpow hx₀pos _
  let D₀ : ℝ → ℝ := fun x =>
    (1 / (2 * π)) * (q x * (x ^ (-(3 / 2 : ℝ)) * (Δ₁ x + airyQ1 x ^ 2 + Δ₂ x + airyQ2 x ^ 2))) +
    (1 / (2 * π)) * (δA x * (x ^ (-(1 / 2 : ℝ)) * (airyP1 x ^ 2 + airyQ1 x ^ 2)) +
      δC x * (x ^ (1 / 2 : ℝ) * (airyP2 x ^ 2 + airyQ2 x ^ 2))) -
    (1 / (2 * π)) * (B x * (airyP1 x * airyQ2 x + airyQ1 x * airyP2 x))
  let D₁ : ℝ → ℝ := fun x =>
    (1 / (2 * π)) * (q x * (x ^ (-(3 / 2 : ℝ)) * (-Δ₁ x + airyQ1 x ^ 2 + Δ₂ x - airyQ2 x ^ 2))) +
    (1 / (2 * π)) * (δA x * (x ^ (-(1 / 2 : ℝ)) * (-airyP1 x ^ 2 + airyQ1 x ^ 2)) +
      δC x * (x ^ (1 / 2 : ℝ) * (airyP2 x ^ 2 - airyQ2 x ^ 2))) -
    (1 / (2 * π)) * (B x * (airyQ1 x * airyP2 x - airyP1 x * airyQ2 x))
  let D₂ : ℝ → ℝ := fun x =>
    (1 / π) * (q x * (x ^ (-(3 / 2 : ℝ)) * (airyP1 x * airyQ1 x + airyP2 x * airyQ2 x))) +
    (1 / π) * (δA x * (x ^ (-(1 / 2 : ℝ)) * (airyP1 x * airyQ1 x)) +
      δC x * (x ^ (1 / 2 : ℝ) * (airyP2 x * airyQ2 x))) -
    (1 / (2 * π)) * (B x * (airyP1 x * airyP2 x + airyQ1 x * airyQ2 x))
  have w_q : ∀ {S : ℝ → ℝ}, IsSymbolOn x₀ 1 S →
      IsWeightedSymbolOn x₀ (5 / 2) q (fun x => q x * (x ^ (-(3 / 2 : ℝ)) * S x)) := by
    intro S hS
    have h := IsWeightedSymbolOn.of_symbol hx₀pos hCR.hq (hxr32.mul hx₀pos hS)
    rwa [show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num] at h
  have w_AC : ∀ {S₁ S₂ : ℝ → ℝ}, IsSymbolOn x₀ 0 S₁ → IsSymbolOn x₀ 0 S₂ →
      IsWeightedSymbolOn x₀ (5 / 2) q (fun x =>
        δA x * (x ^ (-(1 / 2 : ℝ)) * S₁ x) + δC x * (x ^ (1 / 2 : ℝ) * S₂ x)) := by
    intro S₁ S₂ hS₁ hS₂
    have ha := hCR.hA.mul_symbol hx₀pos (hxr12.mul hx₀pos hS₁)
    have hc := hCR.hC.mul_symbol hx₀pos (hxp12.mul hx₀pos hS₂)
    rw [add_zero, show (2 : ℝ) + 1 / 2 = 5 / 2 by norm_num] at ha
    rw [add_zero, show (3 : ℝ) + -(1 / 2 : ℝ) = 5 / 2 by norm_num] at hc
    simpa using ha.add hx₀pos hc
  have w_B : ∀ {S : ℝ → ℝ}, IsSymbolOn x₀ 0 S →
      IsWeightedSymbolOn x₀ (5 / 2) q (fun x => B x * S x) := by
    intro S hS
    have h := (hCR.hB.mul_symbol hx₀pos hS).mono_exp hx₀pos (by norm_num : (5 / 2 : ℝ) ≤ 3 + 0)
    exact h
  have hD₀ : IsWeightedSymbolOn x₀ (5 / 2) q D₀ := by
    have h1 := w_q ((((hΔ₁.add hx₀pos hQ1sq).add hx₀pos hΔ₂).add hx₀pos hQ2sq).mono_exp
      hx₀pos (by norm_num : (1 : ℝ) ≤ min (min (min 3 3) 3) 3))
    have h2 := w_AC (hP1sq.add hx₀pos hQ1sq_0 |>.mono_exp hx₀pos (by norm_num))
      (hP2sq.add hx₀pos hQ2sq_0 |>.mono_exp hx₀pos (by norm_num))
    have h3 := w_B (((hP1s.mul hx₀pos hQ2_0).add hx₀pos (hQ1_0.mul hx₀pos hP2s)).mono_exp
      hx₀pos (by norm_num))
    simpa only [min_self] using ((h1.const_mul _).add hx₀pos (h2.const_mul _)).sub hx₀pos (h3.const_mul _)
  have hD₁ : IsWeightedSymbolOn x₀ (5 / 2) q D₁ := by
    have h1 := w_q ((((hΔ₁.neg.add hx₀pos hQ1sq).add hx₀pos hΔ₂).sub hx₀pos hQ2sq).mono_exp
      hx₀pos (by norm_num : (1 : ℝ) ≤ min (min (min 3 3) 3) 3))
    have h2 := w_AC ((hP1sq.neg.add hx₀pos hQ1sq_0).mono_exp hx₀pos (by norm_num))
      ((hP2sq.sub hx₀pos hQ2sq_0).mono_exp hx₀pos (by norm_num))
    have h3 := w_B (((hQ1_0.mul hx₀pos hP2s).sub hx₀pos (hP1s.mul hx₀pos hQ2_0)).mono_exp
      hx₀pos (by norm_num))
    simpa only [min_self] using ((h1.const_mul _).add hx₀pos (h2.const_mul _)).sub hx₀pos (h3.const_mul _)
  have hD₂ : IsWeightedSymbolOn x₀ (5 / 2) q D₂ := by
    have h1 := w_q ((hP1Q1.add hx₀pos hP2Q2).mono_exp hx₀pos (by norm_num : (1 : ℝ) ≤ min (3 / 2) (3 / 2)))
    have h2 := w_AC hP1Q1_0 hP2Q2_0
    have h3 := w_B (((hP1s.mul hx₀pos hP2s).add hx₀pos (hQ1_0.mul hx₀pos hQ2_0)).mono_exp
      hx₀pos (by norm_num))
    simpa only [min_self] using ((h1.const_mul _).add hx₀pos (h2.const_mul _)).sub hx₀pos (h3.const_mul _)
  refine ⟨D₀, D₁, D₂, hD₀, hD₁, hD₂, fun x hx => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le hx₀pos hx
  have hAi := airy_neg_osc_extract hNicholson hxpos
  have hAi' := airyDeriv_neg_osc_extract hNicholson hxpos
  have hpi_sq : (π ^ (-(1 / 2 : ℝ))) ^ 2 = π⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]; norm_num; exact Real.rpow_neg_one π
  have hx_neg12 : (x ^ (-(1 / 4 : ℝ))) ^ 2 = x ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; norm_num
  have hx_pos12 : (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; norm_num
  have hx_zero : x ^ (-(1 / 4 : ℝ)) * x ^ (1 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hxpos, neg_add_cancel, Real.rpow_zero]
  have hx_neg32 : x ^ (-(1 / 2 : ℝ)) / x = x ^ (-(3 / 2 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one x, ← Real.rpow_add hxpos]; norm_num
  have hx_pos32 : x ^ (1 / 2 : ℝ) / x ^ 2 = x ^ (-(3 / 2 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_natCast x 2, ← Real.rpow_neg hxpos.le, ← Real.rpow_add hxpos]
    norm_num
  have hA_eq : A x = q x / x + δA x := by dsimp [δA]; ring
  have hC_eq : C x = q x / x ^ 2 + δC x := by dsimp [δC]; ring
  have hP1_sq_eq : airyP1 x ^ 2 = 1 + Δ₁ x := by dsimp [Δ₁, δP₁]; ring
  have hP2_sq_eq : airyP2 x ^ 2 = 1 + Δ₂ x := by dsimp [Δ₂, δP₂]; ring
  have hs2 : Real.sin (airyTheta0 x) ^ 2 = (1 - Real.cos (2 * airyTheta0 x)) / 2 := by
    rw [Real.cos_two_mul_eq_one_sub]; ring
  have hc2 : Real.cos (airyTheta0 x) ^ 2 = (1 + Real.cos (2 * airyTheta0 x)) / 2 := by
    rw [Real.cos_two_mul]; ring
  have hsc : Real.sin (airyTheta0 x) * Real.cos (airyTheta0 x) = Real.sin (2 * airyTheta0 x) / 2 := by
    rw [Real.sin_two_mul]; ring
  have hAi_sq : airyAi (-x) ^ 2 = π⁻¹ * x ^ (-(1 / 2 : ℝ)) *
      ((1 - Real.cos (2 * airyTheta0 x)) / 2 +
        Δ₁ x * (1 - Real.cos (2 * airyTheta0 x)) / 2 +
        airyQ1 x ^ 2 * (1 + Real.cos (2 * airyTheta0 x)) / 2 +
        airyP1 x * airyQ1 x * Real.sin (2 * airyTheta0 x)) := by
    rw [hAi, mul_pow, mul_pow, hpi_sq, hx_neg12]
    linear_combination π⁻¹ * x ^ (-(1 / 2 : ℝ)) * (airyP1 x ^ 2 * hs2 + airyQ1 x ^ 2 * hc2 +
      2 * airyP1 x * airyQ1 x * hsc + ((1 - Real.cos (2 * airyTheta0 x)) / 2) * hP1_sq_eq)
  have hAi'_sq : airyAi' (-x) ^ 2 = π⁻¹ * x ^ (1 / 2 : ℝ) *
      ((1 + Real.cos (2 * airyTheta0 x)) / 2 +
        Δ₂ x * (1 + Real.cos (2 * airyTheta0 x)) / 2 +
        airyQ2 x ^ 2 * (1 - Real.cos (2 * airyTheta0 x)) / 2 +
        airyP2 x * airyQ2 x * Real.sin (2 * airyTheta0 x)) := by
    rw [hAi', mul_pow, mul_pow, neg_pow_two, hpi_sq, hx_pos12]
    linear_combination π⁻¹ * x ^ (1 / 2 : ℝ) * (airyP2 x ^ 2 * hc2 + airyQ2 x ^ 2 * hs2 +
      2 * airyP2 x * airyQ2 x * hsc + ((1 + Real.cos (2 * airyTheta0 x)) / 2) * hP2_sq_eq)
  have hAi_Ai' : airyAi (-x) * airyAi' (-x) = -π⁻¹ *
      ((airyP1 x * airyQ2 x + airyQ1 x * airyP2 x) / 2 +
        (airyQ1 x * airyP2 x - airyP1 x * airyQ2 x) / 2 * Real.cos (2 * airyTheta0 x) +
        (airyP1 x * airyP2 x + airyQ1 x * airyQ2 x) / 2 * Real.sin (2 * airyTheta0 x)) := by
    rw [hAi, hAi']
    have hpi_prod : π ^ (-(1 / 2 : ℝ)) * -π ^ (-(1 / 2 : ℝ)) = -π⁻¹ := by
      calc π ^ (-(1 / 2 : ℝ)) * -π ^ (-(1 / 2 : ℝ)) = -(π ^ (-(1 / 2 : ℝ))) ^ 2 := by ring
        _ = -π⁻¹ := by rw [hpi_sq]
    calc (π ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 4 : ℝ)) *
            (Real.sin (airyTheta0 x) * airyP1 x + Real.cos (airyTheta0 x) * airyQ1 x)) *
          (-π ^ (-(1 / 2 : ℝ)) * x ^ (1 / 4 : ℝ) *
            (Real.cos (airyTheta0 x) * airyP2 x + Real.sin (airyTheta0 x) * airyQ2 x))
        = (π ^ (-(1 / 2 : ℝ)) * -π ^ (-(1 / 2 : ℝ))) * (x ^ (-(1 / 4 : ℝ)) * x ^ (1 / 4 : ℝ)) *
            ((airyP1 x * airyQ2 x) * Real.sin (airyTheta0 x) ^ 2 +
              (airyQ1 x * airyP2 x) * Real.cos (airyTheta0 x) ^ 2 +
              (airyP1 x * airyP2 x + airyQ1 x * airyQ2 x) *
                (Real.sin (airyTheta0 x) * Real.cos (airyTheta0 x))) := by ring
      _ = -π⁻¹ * _ := by rw [hpi_prod, hx_zero, mul_one, hs2, hc2, hsc]; ring
  rw [hA_eq, hC_eq, mul_assoc (B x), hAi_sq, hAi'_sq, hAi_Ai']
  dsimp [D₀, D₁, D₂]
  have hqA : q x / x * (π⁻¹ * x ^ (-(1 / 2 : ℝ))) = q x / (π * x ^ (3 / 2 : ℝ)) := by
    calc q x / x * (π⁻¹ * x ^ (-(1 / 2 : ℝ))) = q x * π⁻¹ * (x ^ (-(1 / 2 : ℝ)) / x) := by ring
      _ = q x * π⁻¹ * x ^ (-(3 / 2 : ℝ)) := by rw [hx_neg32]
      _ = q x / (π * x ^ (3 / 2 : ℝ)) := by rw [Real.rpow_neg hxpos.le]; ring
  have hqC : q x / x ^ 2 * (π⁻¹ * x ^ (1 / 2 : ℝ)) = q x / (π * x ^ (3 / 2 : ℝ)) := by
    calc q x / x ^ 2 * (π⁻¹ * x ^ (1 / 2 : ℝ)) = q x * π⁻¹ * (x ^ (1 / 2 : ℝ) / x ^ 2) := by ring
      _ = q x * π⁻¹ * x ^ (-(3 / 2 : ℝ)) := by rw [hx_pos32]
      _ = q x / (π * x ^ (3 / 2 : ℝ)) := by rw [Real.rpow_neg hxpos.le]; ring
  have hr1 : q x / x * (π⁻¹ * x ^ (-(1 / 2 : ℝ))) = π⁻¹ * q x * x ^ (-(3 / 2 : ℝ)) := by
    rw [← hx_neg32]; ring
  have hr2 : q x / x ^ 2 * (π⁻¹ * x ^ (1 / 2 : ℝ)) = π⁻¹ * q x * x ^ (-(3 / 2 : ℝ)) := by
    rw [← hx_pos32]; ring
  linear_combination
    (1 - Real.cos (2 * airyTheta0 x)) / 2 * hqA +
    (1 + Real.cos (2 * airyTheta0 x)) / 2 * hqC +
    (Δ₁ x * (1 - Real.cos (2 * airyTheta0 x)) / 2 +
      airyQ1 x ^ 2 * (1 + Real.cos (2 * airyTheta0 x)) / 2 +
      airyP1 x * airyQ1 x * Real.sin (2 * airyTheta0 x)) * hr1 +
    (Δ₂ x * (1 + Real.cos (2 * airyTheta0 x)) / 2 +
      airyQ2 x ^ 2 * (1 - Real.cos (2 * airyTheta0 x)) / 2 +
      airyP2 x * airyQ2 x * Real.sin (2 * airyTheta0 x)) * hr2


/-! ### Axiom verification -/

/-- info: 'FormalResearch.CohnElkies.airy_neg_phase_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.airy_neg_phase_rep

/-- info: 'FormalResearch.CohnElkies.airyDeriv_neg_w2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.airyDeriv_neg_w2c

/-- info: 'FormalResearch.CohnElkies.airy_neg_osc_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.airy_neg_osc_extract

/-- info: 'FormalResearch.CohnElkies.airyDeriv_neg_osc_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.airyDeriv_neg_osc_extract

/-- info: 'FormalResearch.CohnElkies.airyAi_neg_two_term_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.airyAi_neg_two_term_asymp

/-- info: 'FormalResearch.CohnElkies.cardinal_symbol_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_symbol_decomp

end FormalResearch.CohnElkies
