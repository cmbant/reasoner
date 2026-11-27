/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctDescentRay
public import FormalResearch.CohnElkies.MellinT3Complete
public import FormalResearch.CohnElkies.MellinAiryToolkit
public import FormalResearch.CohnElkies.MellinT3Taylor

/-!
# Global tangent lower bound `(e)` along vertical rays (`fct:splitting` (1))

Paper I (`constant_terms_five.tex`), Lemma FCT.6 (`fct:splitting`), proof step (e), together with
the uniform upper bound `|L₁| ≤ C c^{-2/3}` from `fct:warp-asymp` (1) and the half-strip upper
bound `Re g_tan(σ + iu) ≤ -log((π/2) u)` for `0 ≤ σ ≤ 1/2`, `u ≥ 1`.

* `abs_fctWarpL1_le`: from `FctWarpSolveStmt K4`, `|fctWarpL1 h ε c| ≤ C c^{-2/3}` for `c ≥ c₀`.
* `re_stripG_le_of_re_le_half`: for `0 ≤ σ ≤ 1/2` and `1 ≤ u`,
  `(stripG (σ + i u)).re ≤ -Real.log ((π / 2) * u)`.
* `fctRayP_lower_large_im`: for `|L₁| ≤ 1/8`, `0 ≤ σ ≤ 1/2`, `1 ≤ u`,
  `(1 / 12) * Real.log (2 + u) ≤ ‖fctRayP L₁ (σ + i u)‖`.
* `fctRayP_lower_interior`: for `|L₁| ≤ Lmax`, `5/16 ≤ σ ≤ 7/16`, `0 ≤ u`,
  `q₀ * Real.log (2 + u) ≤ ‖fctRayP L₁ (σ + i u)‖` (step `(e)` of `FctRayStmt`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty

/-! ### `L₁ = O(c^{-2/3})` from `FctWarpSolveStmt` -/

/-- From `FctWarpSolveStmt K4` (`|T₁ - Δ₅^ε(c)| ≤ C c⁻¹` with `T₁ = (c/π²) e^{L₁}`),
`|L₁| ≤ C₁ c^{-2/3}` for all `ε = ±1` and large `c`. -/
theorem abs_fctWarpL1_le {K4 : ℝ} (h : FctWarpSolveStmt K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 1 ≤ c₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      |fctWarpL1 h ε c| ≤ C * c ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨Cz, c0z, hz⟩ := fctWarpZero_of_solve h
  set K_delta : ℝ := |airyOrderCoeff| + max |ctKappa 1| |ctKappa (-1)| + |ctC1Langer| +
    max |ctD2star 1| |ctD2star (-1)|
  set C_rat : ℝ := π ^ 2 * (|Cz| + K_delta)
  have hK0 : 0 ≤ K_delta := by positivity
  have hCr0 : 0 ≤ C_rat := by positivity
  set c₀ : ℝ := max (max c0z 1) ((2 * C_rat + 1) ^ 2)
  have hc01 : 1 ≤ c₀ := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨2 * C_rat, c₀, by positivity, hc01, fun ε c hε hc => ?_⟩
  have hcz : c0z ≤ c := hc.trans' ((le_max_left _ _).trans (le_max_left _ _))
  have hc1 : 1 ≤ c := hc.trans' hc01
  have hcpos : 0 < c := by linarith
  have hT1 := (hz ε c hε hcz).1
  have hκ : |ctKappa ε| ≤ max |ctKappa 1| |ctKappa (-1)| :=
    hε.elim (fun h1 => h1 ▸ le_max_left _ _) (fun h1 => h1 ▸ le_max_right _ _)
  have hd2 : |ctD2star ε| ≤ max |ctD2star 1| |ctD2star (-1)| :=
    hε.elim (fun h1 => h1 ▸ le_max_left _ _) (fun h1 => h1 ▸ le_max_right _ _)
  have hc_p13 : (1 : ℝ) ≤ c ^ (1 / 3 : ℝ) := Real.one_le_rpow hc1 (by norm_num)
  have hc_m13 : c ^ (-(1 / 3 : ℝ)) ≤ c ^ (1 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hc_m23 : c ^ (-(2 / 3 : ℝ)) ≤ c ^ (1 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hc_inv : c⁻¹ ≤ c ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_neg_one c]
    exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hDelta_bd : |ctDelta5 ε c - c / π ^ 2| ≤ K_delta * c ^ (1 / 3 : ℝ) := by
    have hsplit : ctDelta5 ε c - c / π ^ 2 =
        airyOrderCoeff * c ^ (1 / 3 : ℝ) + ctKappa ε + ctC1Langer * c ^ (-(1 / 3 : ℝ)) +
          ctD2star ε * c ^ (-(2 / 3 : ℝ)) := by
      unfold ctDelta5; ring
    rw [hsplit]
    calc |airyOrderCoeff * c ^ (1 / 3 : ℝ) + ctKappa ε + ctC1Langer * c ^ (-(1 / 3 : ℝ)) +
            ctD2star ε * c ^ (-(2 / 3 : ℝ))|
        ≤ |airyOrderCoeff * c ^ (1 / 3 : ℝ)| + |ctKappa ε| +
            |ctC1Langer * c ^ (-(1 / 3 : ℝ))| + |ctD2star ε * c ^ (-(2 / 3 : ℝ))| := by
          have h1 := abs_add_le (airyOrderCoeff * c ^ (1 / 3 : ℝ) + ctKappa ε +
            ctC1Langer * c ^ (-(1 / 3 : ℝ))) (ctD2star ε * c ^ (-(2 / 3 : ℝ)))
          have h2 := abs_add_le (airyOrderCoeff * c ^ (1 / 3 : ℝ) + ctKappa ε)
            (ctC1Langer * c ^ (-(1 / 3 : ℝ)))
          have h3 := abs_add_le (airyOrderCoeff * c ^ (1 / 3 : ℝ)) (ctKappa ε)
          linarith
      _ = |airyOrderCoeff| * c ^ (1 / 3 : ℝ) + |ctKappa ε| +
            |ctC1Langer| * c ^ (-(1 / 3 : ℝ)) + |ctD2star ε| * c ^ (-(2 / 3 : ℝ)) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hcpos _),
            abs_of_pos (Real.rpow_pos_of_pos hcpos _), abs_of_pos (Real.rpow_pos_of_pos hcpos _)]
      _ ≤ |airyOrderCoeff| * c ^ (1 / 3 : ℝ) + max |ctKappa 1| |ctKappa (-1)| * c ^ (1 / 3 : ℝ) +
            |ctC1Langer| * c ^ (1 / 3 : ℝ) + max |ctD2star 1| |ctD2star (-1)| * c ^ (1 / 3 : ℝ) := by
          have hκ' : |ctKappa ε| ≤ max |ctKappa 1| |ctKappa (-1)| * c ^ (1 / 3 : ℝ) :=
            hκ.trans (le_mul_of_one_le_right (by positivity) hc_p13)
          gcongr
      _ = K_delta * c ^ (1 / 3 : ℝ) := by simp only [K_delta]; ring
  have hT1_sub : |fctWarpT1 h ε c - c / π ^ 2| ≤ (|Cz| + K_delta) * c ^ (1 / 3 : ℝ) := by
    have heq : fctWarpT1 h ε c - c / π ^ 2 = (fctWarpT1 h ε c - ctDelta5 ε c) + (ctDelta5 ε c - c / π ^ 2) := by ring
    rw [heq]
    calc |(fctWarpT1 h ε c - ctDelta5 ε c) + (ctDelta5 ε c - c / π ^ 2)|
        ≤ |fctWarpT1 h ε c - ctDelta5 ε c| + |ctDelta5 ε c - c / π ^ 2| := abs_add_le _ _
      _ ≤ |Cz| * c⁻¹ + K_delta * c ^ (1 / 3 : ℝ) := by
          exact add_le_add (hT1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))) hDelta_bd
      _ ≤ |Cz| * c ^ (1 / 3 : ℝ) + K_delta * c ^ (1 / 3 : ℝ) := by gcongr
      _ = (|Cz| + K_delta) * c ^ (1 / 3 : ℝ) := by ring
  set u : ℝ := π ^ 2 * fctWarpT1 h ε c / c - 1
  have hu_eq : u = (π ^ 2 / c) * (fctWarpT1 h ε c - c / π ^ 2) := by
    dsimp [u]; field_simp [hcpos.ne', Real.pi_ne_zero]
  have hpow_mul : c ^ (-(2 / 3 : ℝ)) = c⁻¹ * c ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_neg_one c, ← Real.rpow_add hcpos]
    norm_num
  have hu_bd : |u| ≤ C_rat * c ^ (-(2 / 3 : ℝ)) := by
    rw [hu_eq, abs_mul, abs_of_pos (by positivity : 0 < π ^ 2 / c)]
    calc (π ^ 2 / c) * |fctWarpT1 h ε c - c / π ^ 2|
        ≤ (π ^ 2 / c) * ((|Cz| + K_delta) * c ^ (1 / 3 : ℝ)) := by gcongr
      _ = C_rat * (c⁻¹ * c ^ (1 / 3 : ℝ)) := by simp only [C_rat]; ring
      _ = C_rat * c ^ (-(2 / 3 : ℝ)) := by rw [hpow_mul]
  have hu_half : |u| ≤ 1 / 2 := by
    have hcr : C_rat ≤ (c ^ (1 / 2 : ℝ) - 1) / 2 ∨ True := Or.inr trivial
    have hsq : (2 * C_rat + 1) ^ 2 ≤ c := hc.trans' (le_max_right _ _)
    have hsqrt : 2 * C_rat + 1 ≤ Real.sqrt c := (Real.le_sqrt_of_sq_le hsq)
    have hpow_le : (2 * C_rat + 1 : ℝ) ≤ c ^ (2 / 3 : ℝ) := by
      rw [Real.sqrt_eq_rpow] at hsqrt
      exact hsqrt.trans (Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num))
    have hc23_pos : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hcpos _
    have hinv23 : C_rat * c ^ (-(2 / 3 : ℝ)) ≤ 1 / 2 := by
      rw [Real.rpow_neg hcpos.le, ← div_eq_mul_inv, div_le_div_iff₀ hc23_pos (by norm_num)]
      linarith
    exact hu_bd.trans hinv23
  have h1u_ge : 1 / 2 ≤ 1 + u := by linarith [(abs_le.mp hu_half).1]
  have h1u_pos : 0 < 1 + u := by linarith
  have hL1_eq : fctWarpL1 h ε c = Real.log (1 + u) := by
    rw [← physL1_fctWarpT1 h hcpos]
    simp [u]
  have hlog_bd : |Real.log (1 + u)| ≤ 2 * |u| := by
    rw [abs_le]
    constructor
    · have h1 : Real.log ((1 + u)⁻¹) ≤ (1 + u)⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr h1u_pos)
      rw [Real.log_inv] at h1
      have h2 : (1 + u)⁻¹ - 1 = (-u) / (1 + u) := by field_simp [h1u_pos.ne']; ring
      rw [h2] at h1
      have h3 : (-u) / (1 + u) ≤ |u| / (1 / 2) := by
        exact div_le_div₀ (abs_nonneg u) (neg_le_abs u) (by positivity) h1u_ge
      linarith
    · have h1 : Real.log (1 + u) ≤ (1 + u) - 1 := Real.log_le_sub_one_of_pos h1u_pos
      have h2 : u ≤ |u| := le_abs_self u
      linarith [abs_nonneg u]
  rw [hL1_eq]
  exact hlog_bd.trans ((mul_le_mul_of_nonneg_left hu_bd (by norm_num)).trans_eq (by ring))

/-! ### Complex `tan` modulus and `Re g_tan(σ + iu)` on `{0 ≤ σ ≤ 1/2, u ≥ 1}` -/

lemma norm_sq_complex_sin (x y : ℝ) :
    ‖Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 = Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  have heq : Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I) =
      ((Real.sin x * Real.cosh y : ℝ) : ℂ) + ((Real.cos x * Real.sinh y : ℝ) : ℂ) * Complex.I := by
    rw [Complex.sin_add, Complex.sin_mul_I, Complex.cos_mul_I]
    push_cast; ring
  rw [heq, Complex.sq_norm, Complex.normSq_add_mul_I]
  have h1 := Real.sin_sq_add_cos_sq x
  have h2 := Real.cosh_sq_sub_sinh_sq y
  nlinarith

lemma norm_sq_complex_cos (x y : ℝ) :
    ‖Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 = Real.cos x ^ 2 + Real.sinh y ^ 2 := by
  have heq : Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I) =
      ((Real.cos x * Real.cosh y : ℝ) : ℂ) + ((-(Real.sin x * Real.sinh y) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.cos_add, Complex.sin_mul_I, Complex.cos_mul_I]
    push_cast; ring
  rw [heq, Complex.sq_norm, Complex.normSq_add_mul_I]
  have h1 := Real.sin_sq_add_cos_sq x
  have h2 := Real.cosh_sq_sub_sinh_sq y
  nlinarith

/-- For `0 ≤ σ ≤ 1/2` and `u : ℝ`, `‖tan(π(σ+iu)/2)‖ ≤ 1`. -/
lemma norm_complex_tan_le_one {σ u : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1 / 2) :
    ‖Complex.tan ((π : ℂ) * ((σ : ℂ) + (u : ℂ) * Complex.I) / 2)‖ ≤ 1 := by
  set x : ℝ := π * σ / 2
  set y : ℝ := π * u / 2
  have hw : (π : ℂ) * ((σ : ℂ) + (u : ℂ) * Complex.I) / 2 = (x : ℂ) + (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [x, y]
  rw [hw]
  have hcos_sq : Real.sin x ^ 2 ≤ Real.cos x ^ 2 := by
    have hx0 : 0 ≤ 2 * x := by simp only [x]; positivity
    have hx1 : 2 * x ≤ π / 2 := by simp only [x]; nlinarith [Real.pi_pos]
    have hc : 0 ≤ Real.cos (2 * x) := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hx1⟩
    rw [Real.cos_two_mul'] at hc
    have hsc := Real.sin_sq_add_cos_sq x
    linarith
  have hnorm_sq : ‖Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ≤
      ‖Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 := by
    rw [norm_sq_complex_sin, norm_sq_complex_cos]; linarith
  have hnorm_le : ‖Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      ‖Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
    exact le_of_sq_le_sq hnorm_sq (norm_nonneg _)
  have hcos_ne : Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    intro hzero
    have hsq0 : ‖Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 = 0 := by simp [hzero]
    rw [norm_sq_complex_cos] at hsq0
    have hcosx0 : Real.cos x = 0 := by nlinarith [sq_nonneg (Real.cos x), sq_nonneg (Real.sinh y)]
    have hx_lt : x < π / 2 := by simp only [x]; nlinarith [Real.pi_pos]
    have hx_gt : - (π / 2) < x := by simp only [x]; nlinarith [Real.pi_pos]
    exact (Real.cos_pos_of_mem_Ioo ⟨hx_gt, hx_lt⟩).ne' hcosx0
  rw [Complex.tan_eq_sin_div_cos, norm_div]
  exact div_le_one_of_le₀ hnorm_le (norm_nonneg _)

/-- For `0 ≤ σ ≤ 1/2` and `1 ≤ u`, `(stripG (σ + i u)).re ≤ -Real.log ((π / 2) * u)`. -/
lemma re_stripG_le_of_re_le_half {σ u : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1 / 2) (hu : 1 ≤ u) :
    (stripG ((σ : ℂ) + (u : ℂ) * Complex.I)).re ≤ -Real.log (π / 2 * u) := by
  set t : ℂ := (σ : ℂ) + (u : ℂ) * Complex.I
  set w : ℂ := (π : ℂ) * t / 2
  have ht_ne : t ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp [t] at him
    linarith
  have hw_ne : w ≠ 0 := by
    simp only [w]
    exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) ht_ne) (by norm_num)
  have htan_pos : 0 < ‖Complex.tan w‖ := by
    rw [norm_pos_iff, Complex.tan_eq_sin_div_cos]
    have hsin_ne : Complex.sin w ≠ 0 := by
      intro hzero
      have hw' : w = ((π * σ / 2 : ℝ) : ℂ) + ((π * u / 2 : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [w, t]
      have hsq : ‖Complex.sin (((π * σ / 2 : ℝ) : ℂ) + ((π * u / 2 : ℝ) : ℂ) * Complex.I)‖ ^ 2 = 0 := by
        rw [← hw', hzero, norm_zero]; norm_num
      rw [norm_sq_complex_sin] at hsq
      have hsh0 : Real.sinh (π * u / 2) = 0 := by nlinarith [sq_nonneg (Real.sin (π * σ / 2)), sq_nonneg (Real.sinh (π * u / 2))]
      have hsh_pos : 0 < Real.sinh (π * u / 2) := Real.sinh_pos_iff.mpr (by positivity)
      linarith
    have hcos_ne : Complex.cos w ≠ 0 := by
      intro hzero
      have hw' : w = ((π * σ / 2 : ℝ) : ℂ) + ((π * u / 2 : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [w, t]
      have hsq : ‖Complex.cos (((π * σ / 2 : ℝ) : ℂ) + ((π * u / 2 : ℝ) : ℂ) * Complex.I)‖ ^ 2 = 0 := by
        rw [← hw', hzero, norm_zero]; norm_num
      rw [norm_sq_complex_cos] at hsq
      have hsh0 : Real.sinh (π * u / 2) = 0 := by nlinarith [sq_nonneg (Real.cos (π * σ / 2)), sq_nonneg (Real.sinh (π * u / 2))]
      have hsh_pos : 0 < Real.sinh (π * u / 2) := Real.sinh_pos_iff.mpr (by positivity)
      linarith
    exact div_ne_zero hsin_ne hcos_ne
  have htan_le : ‖Complex.tan w‖ ≤ 1 := norm_complex_tan_le_one h0 h1
  have hw_ge : π / 2 * u ≤ ‖w‖ := by
    have hw_norm : ‖w‖ = (π / 2) * ‖t‖ := by
      rw [show w = ((π / 2 : ℝ) : ℂ) * t by simp only [w]; push_cast; ring, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < π / 2)]
    have him : u ≤ ‖t‖ := by
      have : |t.im| ≤ ‖t‖ := Complex.abs_im_le_norm t
      simpa [t, abs_of_nonneg (by linarith : 0 ≤ u)] using this
    rw [hw_norm]
    exact mul_le_mul_of_nonneg_left him (by positivity)
  have hre : (stripG t).re = Real.log (‖Complex.tan w‖ / ‖w‖) := by
    simp only [stripG, ht_ne, ↓reduceIte, Complex.log_re]
    rw [show (π : ℂ) * t / 2 = w from rfl, norm_div]
  rw [hre, Real.log_div htan_pos.ne' (norm_pos_iff.mpr hw_ne).ne']
  have hlog_tan : Real.log ‖Complex.tan w‖ ≤ 0 := Real.log_nonpos htan_pos.le htan_le
  have hlog_w : Real.log (π / 2 * u) ≤ Real.log ‖w‖ := Real.log_le_log (by positivity) hw_ge
  linarith

/-- For `|L₁| ≤ 1/8`, `0 ≤ σ ≤ 1/2`, and `1 ≤ u`,
`(1 / 12) * Real.log (2 + u) ≤ ‖fctRayP L₁ (σ + i u)‖`. -/
lemma fctRayP_lower_large_im {L1 σ u : ℝ} (hL1 : |L1| ≤ 1 / 8)
    (h0 : 0 ≤ σ) (h1 : σ ≤ 1 / 2) (hu : 1 ≤ u) :
    (1 / 12 : ℝ) * Real.log (2 + u) ≤ ‖fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)‖ := by
  have hre_le := re_stripG_le_of_re_le_half h0 h1 hu
  have htri : -((stripG ((σ : ℂ) + (u : ℂ) * Complex.I)).re) - |L1| ≤
      ‖fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)‖ := by
    have h1 := Complex.abs_re_le_norm (fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I))
    have h2 : -((fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)).re) ≤
        |(fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)).re| := neg_le_abs _
    have h3 : (fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)).re =
        (stripG ((σ : ℂ) + (u : ℂ) * Complex.I)).re + L1 := by
      simp [fctRayP]
    rw [h3] at h1 h2
    linarith [le_abs_self L1]
  have hlog_pi2 : (1 / 3 : ℝ) ≤ Real.log (π / 2) := by
    have h3 : Real.exp (1 : ℝ) < (3 / 2 : ℝ) ^ 3 := by linarith [Real.exp_one_lt_d9]
    have hpow : (Real.exp (1 / 3 : ℝ)) ^ 3 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hlt : Real.exp (1 / 3 : ℝ) < 3 / 2 := by
      have : (Real.exp (1 / 3 : ℝ)) ^ 3 < (3 / 2 : ℝ) ^ 3 := by linarith
      exact lt_of_pow_lt_pow_left₀ 3 (by norm_num) this
    have hlt2 : Real.exp (1 / 3 : ℝ) < π / 2 := hlt.trans (by linarith [Real.pi_gt_three])
    exact (Real.le_log_iff_exp_le (by positivity)).mpr hlt2.le
  by_cases hu4 : u ≤ 4
  · have hlog_neg : Real.log (π / 2) ≤ -(stripG ((σ : ℂ) + (u : ℂ) * Complex.I)).re := by
      have hle := Real.log_le_log (by positivity : 0 < π / 2) (by nlinarith [Real.pi_pos] : π / 2 ≤ π / 2 * u)
      linarith
    have hlog2u : Real.log (2 + u) ≤ 2 := by
      have he2 : (6 : ℝ) ≤ Real.exp 2 := by
        have h := Real.exp_one_gt_d9
        have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      exact (Real.log_le_log (by linarith) (by linarith : 2 + u ≤ 6)).trans
        ((Real.log_le_iff_le_exp (by positivity)).mpr he2)
    calc (1 / 12 : ℝ) * Real.log (2 + u) ≤ (1 / 12) * 2 := by gcongr
      _ = 1 / 6 := by norm_num
      _ ≤ 1 / 3 - 1 / 8 := by norm_num
      _ ≤ Real.log (π / 2) - |L1| := by linarith
      _ ≤ -(stripG ((σ : ℂ) + (u : ℂ) * Complex.I)).re - |L1| := by linarith
      _ ≤ ‖fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)‖ := htri
  · push Not at hu4
    have hpiu : 2 + u ≤ π / 2 * u := by nlinarith [Real.pi_gt_d4]
    have hlog2u : Real.log (2 + u) ≤ Real.log (π / 2 * u) :=
      Real.log_le_log (by linarith) hpiu
    have hlog_ge1 : (1 : ℝ) ≤ Real.log (2 + u) := by
      have : Real.exp 1 ≤ 2 + u := by linarith [Real.exp_one_lt_d9]
      exact (Real.le_log_iff_exp_le (by linarith)).mpr this
    calc (1 / 12 : ℝ) * Real.log (2 + u) ≤ Real.log (2 + u) - 1 / 8 := by linarith
      _ ≤ Real.log (π / 2 * u) - |L1| := by linarith
      _ ≤ -(stripG ((σ : ℂ) + (u : ℂ) * Complex.I)).re - |L1| := by linarith
      _ ≤ ‖fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)‖ := htri

/-! ### Small and intermediate `u` on `5/16 ≤ σ ≤ 7/16`, and `(e)` -/

private lemma stripG_re_small_im {σ u : ℝ} (h0 : 5 / 16 ≤ σ) (h1 : σ ≤ 7 / 16)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 200) :
    (1 / 50 : ℝ) ≤ (stripG ((σ : ℂ) + (u : ℂ) * Complex.I)).re := by
  have hreal_lb : (225 / 3072 : ℝ) ≤ stripGReal σ := by
    have hsum := stripGReal_hasSum (by rw [abs_lt]; constructor <;> linarith : |σ| < 1)
    have hle0 : stripGCoeff 0 * σ ^ (2 * 0 + 2) ≤ stripGReal σ := by
      rw [← hsum.tsum_eq]
      exact hsum.summable.le_tsum 0 (fun k _ => mul_nonneg (stripGCoeff_pos k).le (by positivity))
    rw [stripGCoeff_zero, Nat.mul_zero, zero_add] at hle0
    have hpi3 : (9 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
    have hσ2 : (5 / 16 : ℝ) ^ 2 ≤ σ ^ 2 := by nlinarith
    calc (225 / 3072 : ℝ) = (9 / 12 : ℝ) * (5 / 16) ^ 2 := by norm_num
      _ ≤ (π ^ 2 / 12) * σ ^ 2 := by gcongr
      _ ≤ stripGReal σ := hle0
  have hdiff_bd : ‖stripG ((σ : ℂ) + (u : ℂ) * Complex.I) - stripG (σ : ℂ)‖ ≤ 10 * u := by
    let γ : ℝ → ℂ := fun s => (σ : ℂ) + (s : ℂ) * Complex.I
    have hdiff : ∀ s ∈ Icc (0 : ℝ) u,
        HasDerivWithinAt (fun x : ℝ => stripG (γ x)) (Complex.I * deriv stripG (γ s)) (Icc 0 u) s := by
      intro s _
      have hs_mem : γ s ∈ edgeStrip := by
        show |(γ s).re| < 1
        simp only [γ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero]
        rw [abs_lt]; constructor <;> linarith
      have hg : HasDerivAt stripG (deriv stripG (γ s)) (γ s) :=
        (differentiableOn_stripG.differentiableAt (isOpen_edgeStrip.mem_nhds hs_mem)).hasDerivAt
      exact (hasDerivAt_ray (ζ := (σ : ℂ)) (s := s) hg).hasDerivWithinAt
    have hnb : ∀ s ∈ Icc (0 : ℝ) u, ‖Complex.I * deriv stripG (γ s)‖ ≤ 10 := by
      intro s _
      rw [norm_mul, Complex.norm_I, one_mul]
      have hd := norm_deriv_stripG_le (t := γ s) (by simp [γ]; linarith) (by simp [γ]; linarith)
      have hsin_lb : (1 / 2 : ℝ) ≤ Real.sin (5 * π / 16) := by
        have hsin_mono := Real.strictMonoOn_sin.monotoneOn
          ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
          ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
          (by nlinarith [Real.pi_pos] : π / 4 ≤ 5 * π / 16)
        rw [Real.sin_pi_div_four] at hsin_mono
        have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt_of_sq_le (by norm_num)).trans_eq rfl
        linarith
      have hpi_div : π / Real.sin (5 * π / 16) ≤ 6.4 := by
        rw [div_le_iff₀ (by linarith)]
        linarith [Real.pi_lt_d2]
      linarith
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hdiff hnb (convex_Icc 0 u)
      ⟨le_rfl, hu0⟩ ⟨hu0, le_rfl⟩
    simpa [γ, Real.norm_eq_abs, abs_of_nonneg hu0] using hmvt
  have hofReal : (stripG (σ : ℂ)).re = stripGReal σ := by
    rw [stripG_ofReal (by linarith) (by linarith), Complex.ofReal_re]
  have hre_diff : |(stripG ((σ : ℂ) + (u : ℂ) * Complex.I)).re - (stripG (σ : ℂ)).re| ≤ 10 * u := by
    have := Complex.abs_re_le_norm (stripG ((σ : ℂ) + (u : ℂ) * Complex.I) - stripG (σ : ℂ))
    simpa [Complex.sub_re] using this.trans hdiff_bd
  rw [hofReal] at hre_diff
  linarith [(abs_le.mp hre_diff).1]

private lemma stripG_im_mid_im {σ u : ℝ} (h0 : 5 / 16 ≤ σ) (h1 : σ ≤ 7 / 16)
    (hu0 : 1 / 200 ≤ u) (hu1 : u ≤ 1) :
    (1 / 10000 : ℝ) ≤ (stripG ((σ : ℂ) + (u : ℂ) * Complex.I)).im := by
  have hσ0 : 0 < σ := by linarith
  have hσ1 : σ < 1 := by linarith
  have hut : 0 < u := by linarith
  rw [im_stripG_eq hσ0 hσ1 hut]
  have hge := (im_stripG_ge hσ0 hσ1 hut).2.2.2
  have hdg := (stripG_deriv_bounds hσ0 hσ1).1
  have hdg_lo : (15 / 44 : ℝ) ≤ π / Real.sin (π * σ) - 1 / σ := by
    have h1 : (15 / 44 : ℝ) = 3 / 4 * (5 / 16) / (1 - 5 / 16) := by norm_num
    have h2 : 3 / 4 * (5 / 16) / (1 - 5 / 16) ≤ 3 / 4 * σ / (1 - σ) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    linarith
  have hterm1 : (1 / 1000 : ℝ) ≤ (π / Real.sin (π * σ) - 1 / σ) * u := by
    calc (1 / 1000 : ℝ) ≤ (15 / 44) * (1 / 200) := by norm_num
      _ ≤ (π / Real.sin (π * σ) - 1 / σ) * u := mul_le_mul hdg_lo hu0 (by norm_num) (by positivity)
  have hterm2 : (1 / 1000 : ℝ) ≤ σ / u := by
    rw [le_div_iff₀ hut]; linarith
  have hmin : (1 / 1000 : ℝ) ≤ min ((π / Real.sin (π * σ) - 1 / σ) * u) (min 1 (σ / u)) :=
    le_min hterm1 (le_min (by norm_num) hterm2)
  linarith

/-- Explicit-constant form of `fctRayP_lower_interior` for disc perturbation arguments. -/
lemma fctRayP_lower_interior_const {L1 : ℝ} (hL1 : |L1| ≤ 1 / 100)
    {σ u : ℝ} (h0 : 5 / 16 ≤ σ) (h1 : σ ≤ 7 / 16) (hu0 : 0 ≤ u) :
    (1 / 40000 : ℝ) * Real.log (2 + u) ≤ ‖fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)‖ := by
  by_cases hu1 : 1 ≤ u
  · have hbig := fctRayP_lower_large_im (L1 := L1) (σ := σ) (u := u) (hL1.trans (by norm_num))
      (by linarith) (by linarith) hu1
    have hlog_nn : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
    exact (mul_le_mul_of_nonneg_right (by norm_num) hlog_nn).trans hbig
  · push Not at hu1
    have hlog_le : Real.log (2 + u) ≤ 2 := by
      have he2 : (3 : ℝ) ≤ Real.exp 2 := by
        have h := Real.exp_one_gt_d9
        have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      exact (Real.log_le_log (by linarith) (by linarith : 2 + u ≤ 3)).trans
        ((Real.log_le_iff_le_exp (by positivity)).mpr he2)
    have hconst : (1 / 20000 : ℝ) ≤ ‖fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)‖ := by
      by_cases husm : u ≤ 1 / 200
      · have hre := stripG_re_small_im h0 h1 hu0 husm
        have htri : (stripG ((σ : ℂ) + (u : ℂ) * Complex.I)).re - |L1| ≤
            ‖fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)‖ := by
          have h2 : (fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)).re ≤
              ‖fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)‖ :=
            (le_abs_self _).trans (Complex.abs_re_le_norm _)
          simp only [fctRayP, Complex.add_re, Complex.ofReal_re] at h2
          unfold fctRayP
          linarith [neg_abs_le L1]
        linarith
      · push Not at husm
        have him := stripG_im_mid_im h0 h1 husm.le hu1.le
        have htri : (stripG ((σ : ℂ) + (u : ℂ) * Complex.I)).im ≤
            ‖fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)‖ := by
          have h2 : (fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)).im ≤
              ‖fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)‖ :=
            (le_abs_self _).trans (Complex.abs_im_le_norm _)
          simpa [fctRayP] using h2
        linarith
    have h1 : (1 / 40000 : ℝ) * Real.log (2 + u) ≤ 1 / 20000 := by linarith
    exact h1.trans hconst

/-- **Tangent lower bound along the interior ray** (`fct:splitting` (1), step `(e)`):
for `|L₁| ≤ 1/100`, `5/16 ≤ σ ≤ 7/16`, `0 ≤ u`, `1/40000 * Real.log (2 + u) ≤ ‖fctRayP L₁ (σ + i u)‖`. -/
theorem fctRayP_lower_interior :
    ∃ q0 Lmax : ℝ, 0 < q0 ∧ 0 < Lmax ∧ ∀ L1 : ℝ, |L1| ≤ Lmax →
      ∀ σ u : ℝ, 5 / 16 ≤ σ → σ ≤ 7 / 16 → 0 ≤ u →
        q0 * Real.log (2 + u) ≤ ‖fctRayP L1 ((σ : ℂ) + (u : ℂ) * Complex.I)‖ :=
  ⟨1 / 40000, 1 / 100, by norm_num, by norm_num, fun _ hL1 _ _ h0 h1 hu0 =>
    fctRayP_lower_interior_const hL1 h0 h1 hu0⟩

/-- info: 'FormalResearch.SignUncertainty.abs_fctWarpL1_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_fctWarpL1_le

/-- info: 'FormalResearch.SignUncertainty.fctRayP_lower_large_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctRayP_lower_large_im

/-- info: 'FormalResearch.SignUncertainty.fctRayP_lower_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctRayP_lower_interior

end FormalResearch.SignUncertainty
