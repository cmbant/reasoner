module

public import FormalResearch.Asymptotics.SymbolClass
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Nicholson Integral Error and Phase Correction Symbol Bounds (Lemmas W.3(a) and W.4(a))

Source: `CFT/sign_uncertainty/paper/ce_cr_airy_wkb_derivatives.tex`, §§2–3
(Lemma W.3(a) and Lemma W.4(a)).

Unconditional (zero Airy or DLMF axioms):
* `nicholsonIntegral`, `nicholsonErr`, `nicholsonH`: Nicholson's integral representation of
  `Ai(-x)² + Bi(-x)²` (DLMF 9.11.4, `R2`), `E(x) = π x^{1/2} nicholsonIntegral x - 1`, and `H(y)`.
* `nicholsonErr_eq_H`: `E(x) = H(1 / (12 x³))` for `x > 0`.
* `nicholsonErr_neg_and_abs_le`, `nicholsonErr_asymp`, `nicholsonErr_isSymbol`: Lemma W.3(a).
* `one_add_nicholsonErr_rpow_sub_one_isSymbol`, `one_add_nicholsonErr_inv_isSymbol`.
* `phaseCorr`, `phaseCorr_isSymbol`, `phaseCorr_asymp`: Lemma W.4(a).
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ContDiff Real Topology
open FormalResearch.Asymptotics

namespace FormalResearch.CohnElkies

/-! ### Definitions -/

/-- Nicholson's integral representation of `Ai(-x)² + Bi(-x)²` (DLMF 9.11.4, `R2`). -/
noncomputable def nicholsonIntegral (x : ℝ) : ℝ :=
  π ^ (-(3 / 2 : ℝ)) *
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * t - t ^ 3 / 12) * t ^ (-(1 / 2 : ℝ))

/-- Normalized modulus error `E(x) = π x^{1/2} nicholsonIntegral x - 1`. -/
noncomputable def nicholsonErr (x : ℝ) : ℝ :=
  π * x ^ (1 / 2 : ℝ) * nicholsonIntegral x - 1

/-- Integral representation `H(y) = π^{-1/2} ∫_0^∞ s^{-1/2} e^{-s} (e^{-y s³} - 1) ds`. -/
noncomputable def nicholsonH (y : ℝ) : ℝ :=
  π ^ (-(1 / 2 : ℝ)) *
    ∫ s in Set.Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * (Real.exp (-y * s ^ 3) - 1)

/-- Exact phase correction `ϖ(x) = -∫_x^∞ ((1 + E(t))⁻¹ - 1) t^{1/2} dt`. -/
noncomputable def phaseCorr (x : ℝ) : ℝ :=
  -∫ t in Set.Ioi x, ((1 + nicholsonErr t)⁻¹ - 1) * t ^ (1 / 2 : ℝ)


/-! ### Elementary Gamma and exponential bounds -/

private lemma zero_le_exp_neg_sub_one_add {u : ℝ} : 0 ≤ Real.exp (-u) - 1 + u := by
  linarith [Real.add_one_le_exp (-u)]

private lemma exp_neg_sub_one_add_le_sq {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) - 1 + u ≤ u ^ 2 / 2 := by
  let φ : ℝ → ℝ := fun t => t ^ 2 / 2 - (Real.exp (-t) - 1 + t)
  have hmono : MonotoneOn φ (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact ((continuous_pow 2 |>.div_const 2).sub
        (((continuous_neg.rexp).sub continuous_const).add continuous_id)).continuousOn
    · intro t _
      exact (((hasDerivAt_pow 2 t).div_const 2).sub
        (((hasDerivAt_neg t).exp.sub_const 1).add (hasDerivAt_id t))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have hd : HasDerivAt φ (t + Real.exp (-t) - 1) t := by
        have h1 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
          simpa using (hasDerivAt_pow 2 t).div_const 2
        have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s) - 1 + s) (-Real.exp (-t) + 1) t :=
          (((hasDerivAt_neg t).exp.sub_const 1).fun_add (hasDerivAt_id t)).congr_deriv (by ring)
        exact (h1.fun_sub h2).congr_deriv (by ring)
      rw [hd.deriv]
      linarith [Real.add_one_le_exp (-t)]
  have h0 : φ 0 ≤ φ u := hmono (le_rfl : (0 : ℝ) ∈ Set.Ici 0) hu hu
  dsimp [φ] at h0
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, neg_zero,
    Real.exp_zero, sub_self, add_zero] at h0
  linarith

private lemma gamma_three_mul_add_half_integrable (k : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ (3 * k : ℕ) * s ^ (-(1 / 2 : ℝ)) * Real.exp (-s)) (Set.Ioi 0) := by
  have hg := Real.GammaIntegral_convergent (s := (3 * k : ℝ) + 1 / 2) (by positivity)
  refine hg.congr_fun (fun s hs => ?_) measurableSet_Ioi
  rw [Set.mem_Ioi] at hs
  rw [← Real.rpow_natCast s (3 * k), mul_assoc, mul_comm (s ^ (-(1 / 2 : ℝ))) (Real.exp (-s)),
    ← mul_assoc, mul_comm (s ^ ((3 * k : ℕ) : ℝ)) (Real.exp (-s)), mul_assoc,
    ← Real.rpow_add hs, show ((3 * k : ℕ) : ℝ) + -(1 / 2 : ℝ) = (3 * k : ℝ) + 1 / 2 - 1 by push_cast; ring]

private lemma integral_gamma_three_mul_add_half (k : ℕ) :
    ∫ s in Set.Ioi (0 : ℝ), s ^ (3 * k : ℕ) * s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) =
      Real.Gamma ((3 * k : ℝ) + 1 / 2) := by
  rw [Real.Gamma_eq_integral (by positivity)]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rw [Set.mem_Ioi] at hs
  rw [← Real.rpow_natCast s (3 * k), mul_assoc, mul_comm (s ^ (-(1 / 2 : ℝ))) (Real.exp (-s)),
    ← mul_assoc, mul_comm (s ^ ((3 * k : ℕ) : ℝ)) (Real.exp (-s)), mul_assoc,
    ← Real.rpow_add hs, show ((3 * k : ℕ) : ℝ) + -(1 / 2 : ℝ) = (3 * k : ℝ) + 1 / 2 - 1 by push_cast; ring]

private lemma integral_rpow_neg_half_exp_neg :
    ∫ s in Set.Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) = √π := by
  have h := integral_gamma_three_mul_add_half 0
  rw [show (3 * ((0 : ℕ) : ℝ) + 1 / 2 : ℝ) = 1 / 2 by norm_num, Real.Gamma_one_half_eq] at h
  simpa using h

private lemma gamma_seven_halves : Real.Gamma (7 / 2 : ℝ) = (15 / 8 : ℝ) * √π := by
  have h1 : Real.Gamma (7 / 2 : ℝ) = (5 / 2 : ℝ) * Real.Gamma (5 / 2 : ℝ) := by
    rw [show (7 / 2 : ℝ) = (5 / 2 : ℝ) + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  have h2 : Real.Gamma (5 / 2 : ℝ) = (3 / 2 : ℝ) * Real.Gamma (3 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = (3 / 2 : ℝ) + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  have h3 : Real.Gamma (3 / 2 : ℝ) = (1 / 2 : ℝ) * Real.Gamma (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  rw [h1, h2, h3, Real.Gamma_one_half_eq]
  ring

private lemma integral_cube_rpow_neg_half_exp_neg :
    ∫ s in Set.Ioi (0 : ℝ), s ^ (3 : ℕ) * s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) = (15 / 8 : ℝ) * √π := by
  have h := integral_gamma_three_mul_add_half 1
  rw [show (3 * ((1 : ℕ) : ℝ) + 1 / 2 : ℝ) = 7 / 2 by norm_num, gamma_seven_halves] at h
  simpa using h

private lemma pi_rpow_neg_half_mul_sqrt : π ^ (-(1 / 2 : ℝ)) * √π = 1 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos, neg_add_cancel, Real.rpow_zero]

/-! ### Nicholson identity `nicholsonErr_eq_H` and smoothness of `nicholsonH` -/

private noncomputable def hIntegrand (k : ℕ) (y s : ℝ) : ℝ :=
  if k = 0 then s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * (Real.exp (-y * s ^ 3) - 1)
  else (-s ^ 3) ^ k * s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * Real.exp (-y * s ^ 3)

private lemma integrableOn_hIntegrand {k : ℕ} {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (hIntegrand k y) (Set.Ioi 0) := by
  refine (gamma_three_mul_add_half_integrable k).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    cases k with
    | zero =>
      refine ((continuousOn_id.rpow_const (fun _ h => Or.inl (ne_of_gt h))).mul
        continuousOn_id.neg.rexp).mul ?_
      exact (((continuousOn_const.mul (continuousOn_id.pow 3)).rexp).sub continuousOn_const)
    | succ k =>
      refine (((((continuousOn_id.pow 3).neg.pow (k + 1)).mul
        (continuousOn_id.rpow_const (fun _ h => Or.inl (ne_of_gt h)))).mul
        continuousOn_id.neg.rexp).mul
        ((continuousOn_const.mul (continuousOn_id.pow 3)).rexp))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
    rw [Set.mem_Ioi] at hs
    have hexp_le : Real.exp (-y * s ^ 3) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [pow_pos hs 3])
    have hexp_pos : 0 < Real.exp (-y * s ^ 3) := Real.exp_pos _
    cases k with
    | zero =>
      simp only [hIntegrand, ↓reduceIte, mul_zero, pow_zero, one_mul, Real.norm_eq_abs, abs_mul]
      have h1 : |Real.exp (-y * s ^ 3) - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      rw [abs_of_pos (Real.rpow_pos_of_pos hs _), abs_of_pos (Real.exp_pos (-s))]
      exact mul_le_of_le_one_right (by positivity) h1
    | succ k =>
      simp only [hIntegrand, Nat.succ_ne_zero, ↓reduceIte, Real.norm_eq_abs, abs_mul, abs_pow,
        abs_neg]
      rw [abs_of_pos hs, abs_of_pos (Real.rpow_pos_of_pos hs _),
        abs_of_pos (Real.exp_pos (-s)), abs_of_pos hexp_pos, ← pow_mul, mul_comm 3 (k + 1)]
      exact mul_le_of_le_one_right (by positivity) hexp_le

/-- Exact integral scaling identity: `E(x) = H(1 / (12 x³))` for `x > 0`. -/
theorem nicholsonErr_eq_H {x : ℝ} (hx : 0 < x) :
    nicholsonErr x = nicholsonH (1 / (12 * x ^ 3)) := by
  let g : ℝ → ℝ := fun t => Real.exp (-x * t - t ^ 3 / 12) * t ^ (-(1 / 2 : ℝ))
  have hchg := MeasureTheory.integral_comp_mul_left_Ioi g 0 (inv_pos.mpr hx)
  rw [mul_zero, inv_inv, smul_eq_mul] at hchg
  have hI : ∫ t in Set.Ioi (0 : ℝ), g t = x⁻¹ * ∫ s in Set.Ioi (0 : ℝ), g (x⁻¹ * s) := by
    rw [hchg, ← mul_assoc, inv_mul_cancel₀ hx.ne', one_mul]
  have hcong : ∫ s in Set.Ioi (0 : ℝ), g (x⁻¹ * s) =
      x ^ (1 / 2 : ℝ) * ∫ s in Set.Ioi (0 : ℝ),
        s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * Real.exp (-(1 / (12 * x ^ 3)) * s ^ 3) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [Set.mem_Ioi] at hs
    have hrpow : (x⁻¹ * s) ^ (-(1 / 2 : ℝ)) = x ^ (1 / 2 : ℝ) * s ^ (-(1 / 2 : ℝ)) := by
      rw [Real.mul_rpow (inv_pos.mpr hx).le hs.le, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le,
        neg_neg]
    have hexp : Real.exp (-x * (x⁻¹ * s) - (x⁻¹ * s) ^ 3 / 12) =
        Real.exp (-s) * Real.exp (-(1 / (12 * x ^ 3)) * s ^ 3) := by
      rw [← Real.exp_add]
      congr 1
      have hxne : x ≠ 0 := hx.ne'
      field_simp; ring
    dsimp [g]
    rw [hrpow, hexp]
    ring
  have h1 : (1 : ℝ) = π ^ (-(1 / 2 : ℝ)) *
      ∫ s in Set.Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) := by
    rw [integral_rpow_neg_half_exp_neg, pi_rpow_neg_half_mul_sqrt]
  have hint1 : IntegrableOn (fun s : ℝ =>
      s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * Real.exp (-(1 / (12 * x ^ 3)) * s ^ 3)) (Set.Ioi 0) := by
    refine (gamma_three_mul_add_half_integrable 0).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact ((continuousOn_id.rpow_const (fun _ h => Or.inl (ne_of_gt h))).mul
        continuousOn_id.neg.rexp).mul ((continuousOn_const.mul (continuousOn_id.pow 3)).rexp)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
      rw [Set.mem_Ioi] at hs
      have hle : Real.exp (-(1 / (12 * x ^ 3)) * s ^ 3) ≤ 1 :=
        Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity))
      simp only [mul_zero, pow_zero, one_mul, Real.norm_eq_abs, abs_mul]
      rw [abs_of_pos (Real.rpow_pos_of_pos hs _), abs_of_pos (Real.exp_pos (-s)),
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (by positivity) hle
  have hint0 : IntegrableOn (fun s : ℝ => s ^ (-(1 / 2 : ℝ)) * Real.exp (-s)) (Set.Ioi 0) := by
    simpa using gamma_three_mul_add_half_integrable 0
  have hmain : π * x ^ (1 / 2 : ℝ) * nicholsonIntegral x =
      π ^ (-(1 / 2 : ℝ)) * ∫ s in Set.Ioi (0 : ℝ),
        s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * Real.exp (-(1 / (12 * x ^ 3)) * s ^ 3) := by
    unfold nicholsonIntegral
    change π * x ^ (1 / 2 : ℝ) * (π ^ (-(3 / 2 : ℝ)) * ∫ t in Set.Ioi 0, g t) = _
    rw [hI, hcong]
    have hxpow : x ^ (1 / 2 : ℝ) * (x⁻¹ * x ^ (1 / 2 : ℝ)) = 1 := by
      rw [← mul_assoc, mul_comm (x ^ (1 / 2 : ℝ)) x⁻¹, mul_assoc, ← Real.rpow_add hx]
      norm_num
      exact inv_mul_cancel₀ hx.ne'
    have hpipow : π * π ^ (-(3 / 2 : ℝ)) = π ^ (-(1 / 2 : ℝ)) := by
      conv_lhs => lhs; rw [← Real.rpow_one π]
      rw [← Real.rpow_add Real.pi_pos]
      norm_num
    calc π * x ^ (1 / 2 : ℝ) * (π ^ (-(3 / 2 : ℝ)) * (x⁻¹ * (x ^ (1 / 2 : ℝ) *
          ∫ s in Set.Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) *
            Real.exp (-(1 / (12 * x ^ 3)) * s ^ 3))))
        = (π * π ^ (-(3 / 2 : ℝ))) * (x ^ (1 / 2 : ℝ) * (x⁻¹ * x ^ (1 / 2 : ℝ))) *
            ∫ s in Set.Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) *
              Real.exp (-(1 / (12 * x ^ 3)) * s ^ 3) := by ring
      _ = π ^ (-(1 / 2 : ℝ)) *
            ∫ s in Set.Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) *
              Real.exp (-(1 / (12 * x ^ 3)) * s ^ 3) := by rw [hxpow, hpipow, mul_one]
  unfold nicholsonErr nicholsonH
  rw [hmain]
  conv_lhs => rhs; rw [h1]
  rw [← mul_sub, ← MeasureTheory.integral_sub hint1 hint0]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  ring

private noncomputable def nicholsonHDeriv (k : ℕ) (y : ℝ) : ℝ :=
  π ^ (-(1 / 2 : ℝ)) * ∫ s in Set.Ioi (0 : ℝ), hIntegrand k y s

private lemma nicholsonHDeriv_zero : nicholsonHDeriv 0 = nicholsonH := by
  ext y; rfl

private lemma hasDerivAt_nicholsonHDeriv (k : ℕ) {y₀ : ℝ} (hy₀ : 0 < y₀) :
    HasDerivAt (nicholsonHDeriv k) (nicholsonHDeriv (k + 1) y₀) y₀ := by
  have hs : Metric.ball y₀ (y₀ / 2) ∈ 𝓝 y₀ := Metric.ball_mem_nhds y₀ (half_pos hy₀)
  have hpos_ball : ∀ y ∈ Metric.ball y₀ (y₀ / 2), 0 < y := fun y hy => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy; linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun y s => hIntegrand k y s)
    (F' := fun y s => hIntegrand (k + 1) y s)
    hs
    (Eventually.of_forall fun y => by
      cases k with
      | zero =>
        have hcont : ContinuousOn (hIntegrand 0 y) (Set.Ioi 0) :=
          ((continuousOn_id.rpow_const (fun _ h => Or.inl (ne_of_gt h))).mul
            continuousOn_id.neg.rexp).mul
            (((continuousOn_const.mul (continuousOn_id.pow 3)).rexp).sub continuousOn_const)
        exact hcont.aestronglyMeasurable measurableSet_Ioi
      | succ k =>
        have hcont : ContinuousOn (hIntegrand (k + 1) y) (Set.Ioi 0) :=
          ((((continuousOn_id.pow 3).neg.pow (k + 1)).mul
            (continuousOn_id.rpow_const (fun _ h => Or.inl (ne_of_gt h)))).mul
            continuousOn_id.neg.rexp).mul
            ((continuousOn_const.mul (continuousOn_id.pow 3)).rexp)
        exact hcont.aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_hIntegrand hy₀.le)
    (by
      have hcont : ContinuousOn (hIntegrand (k + 1) y₀) (Set.Ioi 0) :=
        ((((continuousOn_id.pow 3).neg.pow (k + 1)).mul
          (continuousOn_id.rpow_const (fun _ h => Or.inl (ne_of_gt h)))).mul
          continuousOn_id.neg.rexp).mul
          ((continuousOn_const.mul (continuousOn_id.pow 3)).rexp)
      exact hcont.aestronglyMeasurable measurableSet_Ioi)
    (bound := fun s => s ^ (3 * (k + 1) : ℕ) * s ^ (-(1 / 2 : ℝ)) * Real.exp (-s))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs_oi y hy => by
      rw [Set.mem_Ioi] at hs_oi
      have hy_pos := hpos_ball y hy
      have hexp_le : Real.exp (-y * s ^ 3) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [pow_pos hs_oi 3])
      simp only [hIntegrand, Nat.succ_ne_zero, ↓reduceIte, Real.norm_eq_abs, abs_mul, abs_pow,
        abs_neg]
      rw [abs_of_pos hs_oi, abs_of_pos (Real.rpow_pos_of_pos hs_oi _),
        abs_of_pos (Real.exp_pos (-s)), abs_of_pos (Real.exp_pos _), ← pow_mul, mul_comm 3 (k + 1)]
      exact mul_le_of_le_one_right (by positivity) hexp_le))
    (gamma_three_mul_add_half_integrable (k + 1))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s _ y _ => by
      have hd_exp : HasDerivAt (fun u : ℝ => Real.exp (-u * s ^ 3))
          (-s ^ 3 * Real.exp (-y * s ^ 3)) y := by
        have hlin : HasDerivAt (fun u : ℝ => -u * s ^ 3) (-s ^ 3) y := by
          simpa using (hasDerivAt_neg y).mul_const (s ^ 3)
        exact (hlin.exp).congr_deriv (by ring)
      cases k with
      | zero =>
        simp only [hIntegrand, ↓reduceIte, Nat.succ_ne_zero]
        exact ((hd_exp.sub_const 1).const_mul _).congr_deriv (by ring)
      | succ k =>
        simp only [hIntegrand, Nat.succ_ne_zero, ↓reduceIte]
        exact (hd_exp.const_mul _).congr_deriv (by rw [pow_succ]; ring)))
  exact key.2.const_mul (π ^ (-(1 / 2 : ℝ)))

private lemma contDiffOn_nicholsonHDeriv :
    ∀ n k : ℕ, ContDiffOn ℝ n (nicholsonHDeriv k) (Set.Ioi 0) := by
  intro n
  induction n with
  | zero =>
    intro k
    change ContDiffOn ℝ 0 (nicholsonHDeriv k) (Set.Ioi 0)
    rw [contDiffOn_zero]
    intro y hy
    exact (hasDerivAt_nicholsonHDeriv k hy).continuousAt.continuousWithinAt
  | succ n ih =>
    intro k
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy => (hasDerivAt_nicholsonHDeriv k hy).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have heq : Set.EqOn (_root_.deriv (nicholsonHDeriv k)) (nicholsonHDeriv (k + 1)) (Set.Ioi 0) :=
      fun y hy => (hasDerivAt_nicholsonHDeriv k hy).deriv
    exact (ih (k + 1)).congr fun y hy => heq hy

private lemma contDiffOn_nicholsonH : ContDiffOn ℝ ∞ nicholsonH (Set.Ioi 0) := by
  rw [← nicholsonHDeriv_zero, contDiffOn_infty]
  exact fun n => contDiffOn_nicholsonHDeriv n 0

private lemma iteratedDeriv_nicholsonH (k : ℕ) :
    ∀ {y : ℝ}, 0 < y → iteratedDeriv k nicholsonH y = nicholsonHDeriv k y := by
  have hgen : ∀ k m : ℕ, ∀ {y : ℝ}, 0 < y →
      iteratedDeriv k (nicholsonHDeriv m) y = nicholsonHDeriv (k + m) y := by
    intro k
    induction k with
    | zero => intro m y _; simp
    | succ k ih =>
      intro m y hy
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv k (nicholsonHDeriv m) =ᶠ[𝓝 y] nicholsonHDeriv (k + m) := by
        filter_upwards [Ioi_mem_nhds hy] with u hu
        exact ih m hu
      rw [hev.deriv_eq, (hasDerivAt_nicholsonHDeriv (k + m) hy).deriv, Nat.succ_add]
  intro y hy
  rw [← nicholsonHDeriv_zero, hgen k 0 hy, add_zero]

private lemma abs_iteratedDeriv_nicholsonH_le (k : ℕ) (hk : 1 ≤ k) {y : ℝ} (hy : 0 < y) :
    |iteratedDeriv k nicholsonH y| ≤ π ^ (-(1 / 2 : ℝ)) * Real.Gamma ((3 * k : ℝ) + 1 / 2) := by
  rw [iteratedDeriv_nicholsonH k hy]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  unfold nicholsonHDeriv
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos Real.pi_pos _), ← integral_gamma_three_mul_add_half (m + 1)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg Real.pi_pos.le _)
  refine (MeasureTheory.norm_integral_le_integral_norm (fun s => hIntegrand (m + 1) y s)).trans ?_
  refine MeasureTheory.integral_mono_of_nonneg ?_ (gamma_three_mul_add_half_integrable (m + 1)) ?_
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun _ _ => norm_nonneg _)
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => by
      rw [Set.mem_Ioi] at hs
      have hexp_le : Real.exp (-y * s ^ 3) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [pow_pos hs 3])
      simp only [hIntegrand, Nat.succ_ne_zero, ↓reduceIte, Real.norm_eq_abs, abs_mul, abs_pow,
        abs_neg]
      rw [abs_of_pos hs, abs_of_pos (Real.rpow_pos_of_pos hs _),
        abs_of_pos (Real.exp_pos (-s)), abs_of_pos (Real.exp_pos _), ← pow_mul, mul_comm 3 (m + 1)]
      exact mul_le_of_le_one_right (by positivity) hexp_le)

/-! ### Lemma W.3(a): bounds, expansion, and symbol class of `nicholsonErr` -/

private lemma nicholsonH_neg_and_le {y : ℝ} (hy : 0 < y) :
    -(15 / 8 : ℝ) * y ≤ nicholsonH y ∧ nicholsonH y < 0 := by
  have hint_H : IntegrableOn (fun s : ℝ =>
      s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * (Real.exp (-y * s ^ 3) - 1)) (Set.Ioi 0) :=
    integrableOn_hIntegrand (k := 0) hy.le
  have hint_pos : IntegrableOn (fun s : ℝ =>
      s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * (1 - Real.exp (-y * s ^ 3))) (Set.Ioi 0) :=
    hint_H.neg.congr_fun (fun s _ => by dsimp; ring) measurableSet_Ioi
  constructor
  · have hlow : -(15 / 8 : ℝ) * y = π ^ (-(1 / 2 : ℝ)) *
        ∫ s in Set.Ioi (0 : ℝ), -(y * (s ^ (3 : ℕ) * s ^ (-(1 / 2 : ℝ)) * Real.exp (-s))) := by
      rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul,
        integral_cube_rpow_neg_half_exp_neg]
      calc -(15 / 8 : ℝ) * y = (-(15 / 8 : ℝ) * y) * 1 := (mul_one _).symm
        _ = (-(15 / 8 : ℝ) * y) * (π ^ (-(1 / 2 : ℝ)) * √π) := by
            rw [pi_rpow_neg_half_mul_sqrt]
        _ = _ := by ring
    rw [hlow, nicholsonH]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg Real.pi_pos.le _)
    refine MeasureTheory.setIntegral_mono_on
      ((gamma_three_mul_add_half_integrable 1).const_mul y).neg hint_H measurableSet_Ioi
      fun s hs => ?_
    rw [Set.mem_Ioi] at hs
    have hexp : -(y * s ^ 3) ≤ Real.exp (-y * s ^ 3) - 1 := by
      rw [show -y * s ^ 3 = -(y * s ^ 3) by ring]
      linarith [zero_le_exp_neg_sub_one_add (u := y * s ^ 3)]
    have hb : 0 ≤ s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) := by positivity
    nlinarith
  · have hpos_int : 0 < ∫ s in Set.Ioi (0 : ℝ),
        s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * (1 - Real.exp (-y * s ^ 3)) := by
      rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae]
      · have hsup : (Function.support (fun s : ℝ =>
            s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * (1 - Real.exp (-y * s ^ 3)))) ∩ Set.Ioi 0 =
            Set.Ioi 0 := by
          rw [Set.inter_eq_right]
          intro s hs
          rw [Set.mem_Ioi] at hs
          rw [Function.mem_support]
          have h1 : Real.exp (-y * s ^ 3) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [pow_pos hs 3])
          exact mul_ne_zero (mul_ne_zero (Real.rpow_pos_of_pos hs _).ne' (Real.exp_pos _).ne')
            (by linarith)
        rw [hsup, Real.volume_Ioi]
        exact pos_iff_ne_zero.mpr ENNReal.top_ne_zero
      · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => by
          rw [Set.mem_Ioi] at hs
          have h1 : Real.exp (-y * s ^ 3) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by nlinarith [pow_pos hs 3])
          exact mul_nonneg (by positivity) (by linarith))
      · exact hint_pos
    have hneg_eq : nicholsonH y = -(π ^ (-(1 / 2 : ℝ)) * ∫ s in Set.Ioi (0 : ℝ),
        s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * (1 - Real.exp (-y * s ^ 3))) := by
      unfold nicholsonH
      have : (fun s : ℝ => s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * (Real.exp (-y * s ^ 3) - 1)) =
          fun s : ℝ => -(s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * (1 - Real.exp (-y * s ^ 3))) := by
        ext s; ring
      rw [this, MeasureTheory.integral_neg, mul_neg]
    rw [hneg_eq]
    exact neg_lt_zero.mpr (mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) hpos_int)

/-- **Lemma W.3(a), pointwise sign and bound**: for all `x > 0`,
`-(5/32) x^{-3} ≤ E(x) < 0`. -/
theorem nicholsonErr_neg_and_abs_le {x : ℝ} (hx : 0 < x) :
    -(5 / 32 : ℝ) * x ^ (-3 : ℝ) ≤ nicholsonErr x ∧ nicholsonErr x < 0 := by
  rw [nicholsonErr_eq_H hx]
  have hy : 0 < 1 / (12 * x ^ 3) := by positivity
  obtain ⟨h1, h2⟩ := nicholsonH_neg_and_le hy
  have h5 : -(5 / 32 : ℝ) * x ^ (-3 : ℝ) = -(15 / 8 : ℝ) * (1 / (12 * x ^ 3)) := by
    rw [Real.rpow_neg hx.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  exact ⟨h5 ▸ h1, h2⟩

theorem abs_nicholsonErr_le {x : ℝ} (hx : 0 < x) :
    |nicholsonErr x| ≤ (5 / 32 : ℝ) * x ^ (-3 : ℝ) := by
  obtain ⟨h1, h2⟩ := nicholsonErr_neg_and_abs_le hx
  rw [abs_of_neg h2]
  linarith

/-- **Lemma W.3(a), two-term expansion**: `|E(x) + (5/32) x^{-3}| ≤ C x^{-6}` for `x ≥ 1`. -/
theorem nicholsonErr_asymp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ 1, |nicholsonErr x + (5 / 32 : ℝ) * x ^ (-3 : ℝ)| ≤ C * x ^ (-6 : ℝ) := by
  set M₀ : ℝ := π ^ (-(1 / 2 : ℝ)) * Real.Gamma ((3 * 2 : ℝ) + 1 / 2) / 2
  refine ⟨M₀ / 144, by positivity [Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < (3 * 2 : ℝ) + 1 / 2)],
    fun x hx => ?_⟩
  have hxpos : 0 < x := by linarith
  set y : ℝ := 1 / (12 * x ^ 3)
  have hy : 0 < y := by positivity
  rw [nicholsonErr_eq_H hxpos]
  have h15 : (5 / 32 : ℝ) * x ^ (-3 : ℝ) = (15 / 8 : ℝ) * y := by
    dsimp [y]
    rw [Real.rpow_neg hxpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [h15]
  have hint_lin : IntegrableOn (fun s : ℝ =>
      s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * (y * s ^ 3)) (Set.Ioi 0) :=
    MeasureTheory.IntegrableOn.congr_fun
      ((gamma_three_mul_add_half_integrable 1).const_mul y)
      (fun s _ => by ring) measurableSet_Ioi
  have hsum : nicholsonH y + (15 / 8 : ℝ) * y = π ^ (-(1 / 2 : ℝ)) * ∫ s in Set.Ioi (0 : ℝ),
      s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * (Real.exp (-y * s ^ 3) - 1 + y * s ^ 3) := by
    have h15' : (15 / 8 : ℝ) * y = π ^ (-(1 / 2 : ℝ)) *
        ∫ s in Set.Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * (y * s ^ 3) := by
      have heq : (fun s : ℝ => s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * (y * s ^ 3)) =
          (fun s : ℝ => y * (s ^ (3 : ℕ) * s ^ (-(1 / 2 : ℝ)) * Real.exp (-s))) := by
        ext s; ring
      rw [heq, MeasureTheory.integral_const_mul, integral_cube_rpow_neg_half_exp_neg]
      calc (15 / 8 : ℝ) * y = (15 / 8 * y) * 1 := by ring
        _ = (15 / 8 * y) * (π ^ (-(1 / 2 : ℝ)) * √π) := by
            rw [pi_rpow_neg_half_mul_sqrt]
        _ = _ := by ring
    unfold nicholsonH
    have hadd := MeasureTheory.integral_add (integrableOn_hIntegrand (k := 0) hy.le) hint_lin
    dsimp [hIntegrand] at hadd
    rw [h15', ← mul_add, ← hadd]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    ring
  have hnonneg : 0 ≤ nicholsonH y + (15 / 8 : ℝ) * y := by
    rw [hsum]
    refine mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _) ?_
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
    rw [Set.mem_Ioi] at hs
    rw [show -y * s ^ 3 = -(y * s ^ 3) by ring]
    exact mul_nonneg (by positivity) zero_le_exp_neg_sub_one_add
  have hupper : nicholsonH y + (15 / 8 : ℝ) * y ≤ M₀ * y ^ 2 := by
    rw [hsum]
    have hbd_int : (∫ s in Set.Ioi (0 : ℝ),
        s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * (Real.exp (-y * s ^ 3) - 1 + y * s ^ 3)) ≤
        ∫ s in Set.Ioi (0 : ℝ),
          (y ^ 2 / 2) * (s ^ (3 * 2 : ℕ) * s ^ (-(1 / 2 : ℝ)) * Real.exp (-s)) := by
      refine MeasureTheory.setIntegral_mono_on
        (((integrableOn_hIntegrand (k := 0) hy.le).add hint_lin).congr_fun
          (fun s _ => by dsimp [hIntegrand]; ring) measurableSet_Ioi)
        ((gamma_three_mul_add_half_integrable 2).const_mul (y ^ 2 / 2))
        measurableSet_Ioi fun s hs => ?_
      rw [Set.mem_Ioi] at hs
      have hsq := exp_neg_sub_one_add_le_sq (mul_nonneg hy.le (pow_nonneg hs.le 3))
      have h6 : (y * s ^ 3) ^ 2 / 2 = y ^ 2 / 2 * s ^ (3 * 2 : ℕ) := by ring
      rw [show -y * s ^ 3 = -(y * s ^ 3) by ring]
      calc s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * (Real.exp (-(y * s ^ 3)) - 1 + y * s ^ 3)
          ≤ s ^ (-(1 / 2 : ℝ)) * Real.exp (-s) * ((y * s ^ 3) ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (y ^ 2 / 2) * (s ^ (3 * 2 : ℕ) * s ^ (-(1 / 2 : ℝ)) * Real.exp (-s)) := by
            rw [h6]; ring
    have hRHS : π ^ (-(1 / 2 : ℝ)) * ∫ s in Set.Ioi (0 : ℝ),
        (y ^ 2 / 2) * (s ^ (3 * 2 : ℕ) * s ^ (-(1 / 2 : ℝ)) * Real.exp (-s)) = M₀ * y ^ 2 := by
      rw [MeasureTheory.integral_const_mul, integral_gamma_three_mul_add_half 2]
      dsimp [M₀]; ring
    calc π ^ (-(1 / 2 : ℝ)) * ∫ s in Set.Ioi (0 : ℝ), _
        ≤ π ^ (-(1 / 2 : ℝ)) * ∫ s in Set.Ioi (0 : ℝ),
            (y ^ 2 / 2) * (s ^ (3 * 2 : ℕ) * s ^ (-(1 / 2 : ℝ)) * Real.exp (-s)) :=
          mul_le_mul_of_nonneg_left hbd_int (Real.rpow_nonneg Real.pi_pos.le _)
      _ = M₀ * y ^ 2 := hRHS
  have hy2 : y ^ 2 = x ^ (-6 : ℝ) / 144 := by
    dsimp [y]
    rw [Real.rpow_neg hxpos.le, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [abs_of_nonneg hnonneg]
  calc nicholsonH y + (15 / 8 : ℝ) * y ≤ M₀ * y ^ 2 := hupper
    _ = M₀ / 144 * x ^ (-6 : ℝ) := by rw [hy2]; ring

/-- **Lemma W.3(a), symbol class**: `nicholsonErr ∈ 𝒮_3`. -/
theorem nicholsonErr_isSymbol : IsSymbol 3 nicholsonErr := by
  let y : ℝ → ℝ := fun x => (1 / 12 : ℝ) * x ^ (-3 : ℝ)
  have hy : IsSymbol 3 y := (IsSymbol.rpow_neg 3).const_mul (1 / 12)
  have hcomp : IsSymbol 3 (fun x => nicholsonH (y x)) := by
    refine IsSymbolOn.comp_Ioi zero_lt_one (by norm_num) hy
      (fun x hx => by dsimp [y]; positivity)
      contDiffOn_nicholsonH
      ⟨15 / 8, by norm_num, fun x hx => ?_⟩
      (fun k hk => ⟨π ^ (-(1 / 2 : ℝ)) * Real.Gamma ((3 * k : ℝ) + 1 / 2),
        by positivity [Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (3 * k : ℝ) + 1 / 2)],
        fun u hu => abs_iteratedDeriv_nicholsonH_le k hk hu⟩)
    have hxpos : 0 < x := by linarith
    have hy_eq : y x = 1 / (12 * x ^ 3) := by
      dsimp [y]
      rw [Real.rpow_neg hxpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [hy_eq, ← nicholsonErr_eq_H hxpos]
    calc |nicholsonErr x| ≤ (5 / 32 : ℝ) * x ^ (-3 : ℝ) := abs_nicholsonErr_le hxpos
      _ = (15 / 8 : ℝ) * (1 / (12 * x ^ 3)) := by
        rw [Real.rpow_neg hxpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
  refine hcomp.congr fun x hx => ?_
  have hxpos : 0 < x := by linarith [Set.mem_Ici.mp hx]
  have hy_eq : y x = 1 / (12 * x ^ 3) := by
    dsimp [y]
    rw [Real.rpow_neg hxpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [nicholsonErr_eq_H hxpos, hy_eq]

lemma contDiffOn_nicholsonErr_Ioi : ContDiffOn ℝ ∞ nicholsonErr (Set.Ioi 0) := by
  let y : ℝ → ℝ := fun x => (1 / 12 : ℝ) * x ^ (-3 : ℝ)
  have hy_cd : ContDiffOn ℝ ∞ y (Set.Ioi 0) := fun x hx => by
    exact (contDiffWithinAt_const.mul
      ((Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt))
  have hmaps : Set.MapsTo y (Set.Ioi 0) (Set.Ioi 0) := fun x hx => by
    rw [Set.mem_Ioi] at hx ⊢; dsimp [y]; positivity
  refine (contDiffOn_nicholsonH.comp hy_cd hmaps).congr fun x hx => ?_
  rw [Set.mem_Ioi] at hx
  have hy_eq : y x = 1 / (12 * x ^ 3) := by
    dsimp [y]
    rw [Real.rpow_neg hx.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  dsimp only [Function.comp_def]
  rw [nicholsonErr_eq_H hx, hy_eq]

private lemma one_add_nicholsonErr_ge_of_ge_two_thirds {x : ℝ} (hx : 2 / 3 < x) :
    121 / 256 ≤ 1 + nicholsonErr x := by
  have hxpos : 0 < x := by linarith
  have h1 := (nicholsonErr_neg_and_abs_le hxpos).1
  have h2 : x ^ (-3 : ℝ) ≤ (2 / 3 : ℝ) ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hx.le (by norm_num)
  have h3 : (2 / 3 : ℝ) ^ (-3 : ℝ) = 27 / 8 := by norm_num
  linarith

lemma one_add_nicholsonErr_ge_of_ge_one {x : ℝ} (hx : 1 ≤ x) :
    27 / 32 ≤ 1 + nicholsonErr x := by
  have hxpos : 0 < x := by linarith
  have h1 := (nicholsonErr_neg_and_abs_le hxpos).1
  have h2 : x ^ (-3 : ℝ) ≤ (1 : ℝ) ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos zero_lt_one hx (by norm_num)
  norm_num at h2
  rw [Real.rpow_neg hxpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
  linarith

/-- `(1 + E(x))^p - 1 ∈ 𝒮_3` unconditionally for every real exponent `p`. -/
theorem one_add_nicholsonErr_rpow_sub_one_isSymbol (p : ℝ) :
    IsSymbol 3 (fun x => (1 + nicholsonErr x) ^ p - 1) := by
  let G : ℝ → ℝ := fun s => (1 + s) ^ p - 1
  have hG : ContDiffOn ℝ ∞ G (Set.Ioo (-(1 / 2)) (1 / 2)) := fun s hs => by
    have hne : 1 + s ≠ 0 := by linarith [hs.1]
    exact (((Real.contDiffAt_rpow_const_of_ne hne).comp s
      (contDiffAt_const.add contDiffAt_id)).sub contDiffAt_const).contDiffWithinAt
  have hrange : ∀ x ≥ (1 : ℝ), nicholsonErr x ∈ Set.Icc (-(5 / 32 : ℝ)) 0 := fun x hx => by
    have hxpos : 0 < x := by linarith
    obtain ⟨h1, h2⟩ := nicholsonErr_neg_and_abs_le hxpos
    have hxle : x ^ (-3 : ℝ) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one hx (by norm_num : (-3 : ℝ) ≤ 0)
    exact ⟨by linarith, h2.le⟩
  simpa [G] using nicholsonErr_isSymbol.comp_sub_zero (by norm_num)
    (a := -(1 / 2)) (a' := -(5 / 32)) (b' := 0) (b := 1 / 2)
    (by norm_num) (by norm_num) le_rfl (by norm_num) hrange hG

theorem one_add_nicholsonErr_rpow_isSymbol (p : ℝ) :
    IsSymbol 0 (fun x => (1 + nicholsonErr x) ^ p) := by
  have h := (one_add_nicholsonErr_rpow_sub_one_isSymbol p).add (IsSymbol.const le_rfl (1 : ℝ))
  have hmin : min (3 : ℝ) 0 = 0 := by norm_num
  rw [hmin] at h
  exact h.congr fun x _ => by ring

theorem one_add_nicholsonErr_inv_isSymbol :
    IsSymbol 0 (fun x => (1 + nicholsonErr x)⁻¹) :=
  (one_add_nicholsonErr_rpow_isSymbol (-1)).congr fun x _ => by rw [Real.rpow_neg_one]

/-! ### Lemma W.4(a): symbol class and two-term expansion of `phaseCorr` -/

noncomputable def phaseIntegrand (t : ℝ) : ℝ :=
  ((1 + nicholsonErr t)⁻¹ - 1) * t ^ (1 / 2 : ℝ)

private lemma phaseIntegrand_isSymbol : IsSymbol (5 / 2) phaseIntegrand := by
  have h1 : IsSymbol 3 (fun t => (1 + nicholsonErr t)⁻¹ - 1) :=
    (one_add_nicholsonErr_rpow_sub_one_isSymbol (-1)).congr fun t _ => by rw [Real.rpow_neg_one]
  have h2 : IsSymbol (-(1 / 2 : ℝ)) (fun t : ℝ => t ^ (1 / 2 : ℝ)) := by
    simpa using IsSymbol.rpow (1 / 2 : ℝ)
  have hprod := h1.mul h2
  rw [show (3 : ℝ) + -(1 / 2 : ℝ) = 5 / 2 by norm_num] at hprod
  exact hprod

private lemma contDiffOn_phaseIntegrand_two_thirds :
    ContDiffOn ℝ ∞ phaseIntegrand (Set.Ioi (2 / 3)) := fun t ht => by
  have ht0 : t ∈ Set.Ioi (0 : ℝ) := by rw [Set.mem_Ioi] at ht ⊢; linarith
  have hE : ContDiffAt ℝ ∞ nicholsonErr t :=
    contDiffOn_nicholsonErr_Ioi.contDiffAt (isOpen_Ioi.mem_nhds ht0)
  have hne : 1 + nicholsonErr t ≠ 0 := by
    linarith [one_add_nicholsonErr_ge_of_ge_two_thirds ht]
  have hrpow : ContDiffAt ℝ ∞ (fun s : ℝ => s ^ (1 / 2 : ℝ)) t :=
    Real.contDiffAt_rpow_const_of_ne (ne_of_gt ht0)
  exact ((((contDiffAt_const.add hE).inv hne).sub contDiffAt_const).mul hrpow).contDiffWithinAt

lemma integrableOn_phaseIntegrand_of_ge_one {x : ℝ} (hx : 1 ≤ x) :
    IntegrableOn phaseIntegrand (Set.Ioi x) := by
  obtain ⟨C, hC, hbd⟩ := phaseIntegrand_isSymbol.abs_le
  have hdom : IntegrableOn (fun t : ℝ => C * t ^ (-(5 / 2 : ℝ))) (Set.Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(5 / 2 : ℝ) < -1) (by linarith)).const_mul C
  refine hdom.mono' ?_ ?_
  · exact (contDiffOn_phaseIntegrand_two_thirds.continuousOn.mono
      (fun t ht => by rw [Set.mem_Ioi] at ht ⊢; linarith)).aestronglyMeasurable measurableSet_Ioi
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => by
      rw [Set.mem_Ioi] at ht
      rw [Real.norm_eq_abs]
      exact hbd t (by linarith))

private lemma integrableOn_phaseIntegrand_of_gt_two_thirds {x : ℝ} (hx : 2 / 3 < x) :
    IntegrableOn phaseIntegrand (Set.Ioi x) := by
  rcases le_or_gt 1 x with hx1 | hx1
  · exact integrableOn_phaseIntegrand_of_ge_one hx1
  · rw [← Set.Ioc_union_Ioi_eq_Ioi hx1.le]
    refine IntegrableOn.union ?_ (integrableOn_phaseIntegrand_of_ge_one le_rfl)
    rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (contDiffOn_phaseIntegrand_two_thirds.continuousOn.mono
      fun t (ht : t ∈ Set.Icc x 1) => by rw [Set.mem_Ioi]; linarith [ht.1]).integrableOn_compact
      isCompact_Icc

private lemma hasDerivAt_phaseCorr_of_gt_two_thirds {x : ℝ} (hx : 2 / 3 < x) :
    HasDerivAt phaseCorr (phaseIntegrand x) x := by
  have heq : Set.EqOn phaseCorr
      (fun y => (∫ t in (1 : ℝ)..y, phaseIntegrand t) - ∫ t in Set.Ioi 1, phaseIntegrand t)
      (Set.Ioi (2 / 3)) := by
    intro y hy
    have hsub := intervalIntegral.integral_Ioi_sub_Ioi'
      (integrableOn_phaseIntegrand_of_ge_one le_rfl)
      (integrableOn_phaseIntegrand_of_gt_two_thirds hy)
    unfold phaseCorr
    change -∫ t in Set.Ioi y, phaseIntegrand t = _
    linarith
  have hd_int : HasDerivAt (fun y => ∫ t in (1 : ℝ)..y, phaseIntegrand t) (phaseIntegrand x) x := by
    have hcont : ContinuousAt phaseIntegrand x :=
      (contDiffOn_phaseIntegrand_two_thirds.continuousOn.continuousAt
        (isOpen_Ioi.mem_nhds hx))
    have hi : IntervalIntegrable phaseIntegrand volume 1 x := by
      refine ContinuousOn.intervalIntegrable ?_
      exact contDiffOn_phaseIntegrand_two_thirds.continuousOn.mono fun t ht => by
        rw [Set.mem_uIcc] at ht
        rw [Set.mem_Ioi]
        rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    exact intervalIntegral.integral_hasDerivAt_right hi
      (contDiffOn_phaseIntegrand_two_thirds.continuousOn.stronglyMeasurableAtFilter isOpen_Ioi x hx)
      hcont
  exact (hd_int.sub_const _).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx) fun y hy => heq hy)

/-- **Lemma W.4(a), symbol class**: `phaseCorr ∈ 𝒮_{3/2}`. -/
theorem phaseCorr_isSymbol : IsSymbol (3 / 2) phaseCorr := by
  have hcd : ContDiffOn ℝ ∞ phaseCorr (Set.Ici 1) := by
    have hcd_open : ContDiffOn ℝ ∞ phaseCorr (Set.Ioi (2 / 3)) := by
      rw [contDiffOn_infty]
      intro n
      induction n with
      | zero =>
        change ContDiffOn ℝ 0 phaseCorr (Set.Ioi (2 / 3))
        rw [contDiffOn_zero]
        intro x hx
        exact (hasDerivAt_phaseCorr_of_gt_two_thirds hx).continuousAt.continuousWithinAt
      | succ n ih =>
        rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
        refine ⟨fun x hx => (hasDerivAt_phaseCorr_of_gt_two_thirds hx).differentiableAt.differentiableWithinAt,
          fun h => absurd h (by simp), ?_⟩
        have heq : Set.EqOn (_root_.deriv phaseCorr) phaseIntegrand (Set.Ioi (2 / 3)) :=
          fun x hx => (hasDerivAt_phaseCorr_of_gt_two_thirds hx).deriv
        exact (contDiffOn_phaseIntegrand_two_thirds.of_le (by simp)).congr fun x hx => heq hx
    exact hcd_open.mono fun x hx => by rw [Set.mem_Ioi]; linarith [Set.mem_Ici.mp hx]
  refine ⟨hcd, fun j => ?_⟩
  cases j with
  | zero =>
    obtain ⟨C, hC, hbd⟩ := phaseIntegrand_isSymbol.abs_le
    refine ⟨(2 / 3 : ℝ) * C, by positivity, fun x hx => ?_⟩
    have hxpos : 0 < x := by linarith
    have hint_dom : IntegrableOn (fun t : ℝ => C * t ^ (-(5 / 2 : ℝ))) (Set.Ioi x) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : -(5 / 2 : ℝ) < -1) hxpos).const_mul C
    have hle : |∫ t in Set.Ioi x, phaseIntegrand t| ≤
        ∫ t in Set.Ioi x, C * t ^ (-(5 / 2 : ℝ)) := by
      refine (MeasureTheory.norm_integral_le_integral_norm phaseIntegrand).trans ?_
      refine MeasureTheory.integral_mono_of_nonneg ?_ hint_dom ?_
      · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun _ _ => norm_nonneg _)
      · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => by
          rw [Set.mem_Ioi] at ht; dsimp only; rw [Real.norm_eq_abs]; exact hbd t (by linarith))
    have heval : (∫ t in Set.Ioi x, C * t ^ (-(5 / 2 : ℝ))) = (2 / 3 : ℝ) * C * x ^ (-(3 / 2 : ℝ)) := by
      rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : -(5 / 2 : ℝ) < -1) hxpos]
      norm_num; ring
    simp only [iteratedDerivWithin_zero, Nat.cast_zero, sub_zero]
    unfold phaseCorr
    rw [abs_neg]
    exact hle.trans_eq heval
  | succ m =>
    obtain ⟨C, hC, hbd⟩ := phaseIntegrand_isSymbol.2 m
    refine ⟨C, hC, fun x hx => ?_⟩
    have heq : Set.EqOn (_root_.derivWithin phaseCorr (Set.Ici 1)) phaseIntegrand (Set.Ici 1) :=
      fun y hy => (hasDerivAt_phaseCorr_of_gt_two_thirds (by linarith [Set.mem_Ici.mp hy])).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Ici 1 y hy)
    have hxI : x ∈ Set.Ici (1 : ℝ) := hx
    rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr heq hxI]
    have hexp : -(3 / 2 : ℝ) - ((m + 1 : ℕ) : ℝ) = -(5 / 2 : ℝ) - (m : ℝ) := by
      push_cast; ring
    rw [hexp]
    exact hbd x hx

/-- **Lemma W.4(a), two-term expansion**: `|ϖ(x) + (5/48) x^{-3/2}| ≤ C x^{-9/2}` for `x ≥ 1`. -/
theorem phaseCorr_asymp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ 1,
      |phaseCorr x + (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ))| ≤ C * x ^ (-(9 / 2 : ℝ)) := by
  obtain ⟨CE, hCE, hE_asymp⟩ := nicholsonErr_asymp
  set K : ℝ := (32 / 27 : ℝ) * (CE + (25 / 1024 : ℝ))
  have hK : 0 ≤ K := by positivity
  refine ⟨(2 / 9 : ℝ) * K, by positivity, fun x hx => ?_⟩
  have hxpos : 0 < x := by linarith
  have hlead : (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ)) =
      ∫ t in Set.Ioi x, (5 / 32 : ℝ) * t ^ (-(5 / 2 : ℝ)) := by
    rw [MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num : -(5 / 2 : ℝ) < -1) hxpos]
    norm_num; ring
  have hint_lead : IntegrableOn (fun t : ℝ => (5 / 32 : ℝ) * t ^ (-(5 / 2 : ℝ))) (Set.Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(5 / 2 : ℝ) < -1) hxpos).const_mul _
  have hdiff_eq : phaseCorr x + (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ)) =
      -∫ t in Set.Ioi x, (phaseIntegrand t - (5 / 32 : ℝ) * t ^ (-(5 / 2 : ℝ))) := by
    have hsub := MeasureTheory.integral_sub (integrableOn_phaseIntegrand_of_ge_one hx) hint_lead
    unfold phaseCorr
    change (-∫ t in Set.Ioi x, phaseIntegrand t) + (5 / 48 : ℝ) * x ^ (-(3 / 2 : ℝ)) =
      -∫ t in Set.Ioi x, (phaseIntegrand t - (5 / 32 : ℝ) * t ^ (-(5 / 2 : ℝ)))
    rw [hlead]
    linarith
  have hint_dom : IntegrableOn (fun t : ℝ => K * t ^ (-(11 / 2 : ℝ))) (Set.Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(11 / 2 : ℝ) < -1) hxpos).const_mul K
  have hpt : ∀ t > x, |phaseIntegrand t - (5 / 32 : ℝ) * t ^ (-(5 / 2 : ℝ))| ≤
      K * t ^ (-(11 / 2 : ℝ)) := by
    intro t ht
    have ht1 : 1 ≤ t := by linarith
    have htpos : 0 < t := by linarith
    have hE1 : 27 / 32 ≤ 1 + nicholsonErr t := one_add_nicholsonErr_ge_of_ge_one ht1
    have hEabs : |nicholsonErr t| ≤ (5 / 32 : ℝ) * t ^ (-3 : ℝ) := abs_nicholsonErr_le htpos
    have hE2 := hE_asymp t ht1
    have hid : ((1 + nicholsonErr t)⁻¹ - 1) - (5 / 32 : ℝ) * t ^ (-3 : ℝ) =
        (-(nicholsonErr t + (5 / 32 : ℝ) * t ^ (-3 : ℝ)) -
          (5 / 32 : ℝ) * t ^ (-3 : ℝ) * nicholsonErr t) / (1 + nicholsonErr t) := by
      have hne : 1 + nicholsonErr t ≠ 0 := by linarith
      field_simp; ring
    have hnum : |(-(nicholsonErr t + (5 / 32 : ℝ) * t ^ (-3 : ℝ)) -
          (5 / 32 : ℝ) * t ^ (-3 : ℝ) * nicholsonErr t)| ≤
        (CE + 25 / 1024 : ℝ) * t ^ (-6 : ℝ) := by
      have htri := abs_sub (-(nicholsonErr t + (5 / 32 : ℝ) * t ^ (-3 : ℝ)))
        ((5 / 32 : ℝ) * t ^ (-3 : ℝ) * nicholsonErr t)
      rw [abs_neg] at htri
      have hmul : |(5 / 32 : ℝ) * t ^ (-3 : ℝ) * nicholsonErr t| ≤ (25 / 1024 : ℝ) * t ^ (-6 : ℝ) := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        calc (5 / 32 : ℝ) * t ^ (-3 : ℝ) * |nicholsonErr t|
            ≤ (5 / 32 : ℝ) * t ^ (-3 : ℝ) * ((5 / 32 : ℝ) * t ^ (-3 : ℝ)) :=
              mul_le_mul_of_nonneg_left hEabs (by positivity)
          _ = (25 / 1024 : ℝ) * (t ^ (-3 : ℝ) * t ^ (-3 : ℝ)) := by ring
          _ = (25 / 1024 : ℝ) * t ^ (-6 : ℝ) := by rw [← Real.rpow_add htpos]; norm_num
      linarith
    have hfrac : |((1 + nicholsonErr t)⁻¹ - 1) - (5 / 32 : ℝ) * t ^ (-3 : ℝ)| ≤ K * t ^ (-6 : ℝ) := by
      rw [hid, abs_div, abs_of_pos (by linarith : 0 < 1 + nicholsonErr t)]
      calc |(-(nicholsonErr t + (5 / 32 : ℝ) * t ^ (-3 : ℝ)) -
              (5 / 32 : ℝ) * t ^ (-3 : ℝ) * nicholsonErr t)| / (1 + nicholsonErr t)
          ≤ ((CE + 25 / 1024 : ℝ) * t ^ (-6 : ℝ)) / (27 / 32 : ℝ) :=
            div_le_div₀ (by positivity) hnum (by norm_num) hE1
        _ = K * t ^ (-6 : ℝ) := by dsimp [K]; ring
    have hsplit : phaseIntegrand t - (5 / 32 : ℝ) * t ^ (-(5 / 2 : ℝ)) =
        (((1 + nicholsonErr t)⁻¹ - 1) - (5 / 32 : ℝ) * t ^ (-3 : ℝ)) * t ^ (1 / 2 : ℝ) := by
      have hpow : t ^ (-3 : ℝ) * t ^ (1 / 2 : ℝ) = t ^ (-(5 / 2 : ℝ)) := by
        rw [← Real.rpow_add htpos]; norm_num
      dsimp [phaseIntegrand]; rw [← hpow]; ring
    have hpow2 : t ^ (-6 : ℝ) * t ^ (1 / 2 : ℝ) = t ^ (-(11 / 2 : ℝ)) := by
      rw [← Real.rpow_add htpos]; norm_num
    rw [hsplit, abs_mul, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
    calc |((1 + nicholsonErr t)⁻¹ - 1) - (5 / 32 : ℝ) * t ^ (-3 : ℝ)| * t ^ (1 / 2 : ℝ)
        ≤ (K * t ^ (-6 : ℝ)) * t ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hfrac (Real.rpow_nonneg htpos.le _)
      _ = K * t ^ (-(11 / 2 : ℝ)) := by rw [← hpow2]; ring
  rw [hdiff_eq, abs_neg]
  have hle : |∫ t in Set.Ioi x, (phaseIntegrand t - (5 / 32 : ℝ) * t ^ (-(5 / 2 : ℝ)))| ≤
      ∫ t in Set.Ioi x, K * t ^ (-(11 / 2 : ℝ)) := by
    refine (MeasureTheory.norm_integral_le_integral_norm
      (fun t => phaseIntegrand t - (5 / 32 : ℝ) * t ^ (-(5 / 2 : ℝ)))).trans ?_
    refine MeasureTheory.integral_mono_of_nonneg ?_ hint_dom ?_
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun _ _ => norm_nonneg _)
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => by
        rw [Set.mem_Ioi] at ht; dsimp only; rw [Real.norm_eq_abs]; exact hpt t ht)
  have heval : (∫ t in Set.Ioi x, K * t ^ (-(11 / 2 : ℝ))) = (2 / 9 : ℝ) * K * x ^ (-(9 / 2 : ℝ)) := by
    rw [MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num : -(11 / 2 : ℝ) < -1) hxpos]
    norm_num; ring
  exact hle.trans_eq heval


/-! ### Axiom verification -/

/-- info: 'FormalResearch.CohnElkies.nicholsonErr_neg_and_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.nicholsonErr_neg_and_abs_le

/-- info: 'FormalResearch.CohnElkies.nicholsonErr_isSymbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.nicholsonErr_isSymbol

/-- info: 'FormalResearch.CohnElkies.phaseCorr_isSymbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.phaseCorr_isSymbol

/-- info: 'FormalResearch.CohnElkies.phaseCorr_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.phaseCorr_asymp

end FormalResearch.CohnElkies
