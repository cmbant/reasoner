module

public import FormalResearch.SignUncertainty.WindowTranslation

/-!
# `main_line_diff` for an arbitrary symbol (F2a helper for `uct:seed-asymp` (1))

`main_line_diff_sym`: the proof of `main_line_diff` (`WindowTranslation`) uses the lift symbol only through the bound
`|Sy(w)| ≤ C_W (1+|Im w|)^{-5/2}` on `Re w ≥ 0`; stated here for any `Sy : ℂ → ℂ`.  The kernel-difference integral
`∫ (K₀(εw,ξ) - exp(π²w³/36 + (π²S+ε/2)w)) Sy(w) dv` on `Re w = 1` is `O(ε²)`.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

theorem main_line_diff_sym (Sw CW : ℝ) (hCW : 0 < CW) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Sy : ℂ → ℂ},
      (∀ {w : ℂ}, 0 ≤ w.re → w.re ≤ 1 → ‖Sy w‖ ≤ CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) →
      ∀ {c ε ξ S : ℝ}, 0 < ε → c * ε ^ 3 = 1 → ε ≤ 1 / 32 → 0 < ξ →
      Real.log (Real.pi ^ 2 * ξ) = Real.pi ^ 2 * ε ^ 2 * S → |S| ≤ Sw →
      ‖∫ v : ℝ, (mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ -
            refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)) *
          Sy ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ C * ε ^ 2 := by
  have hpi : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  obtain ⟨Cp, hCp, hpoly⟩ := cube_le_exp_sq (a := Real.pi ^ 2 / 24) (by positivity)
  set B₀ : ℝ := 2 * Real.exp (1 + Real.pi ^ 2 * Sw) with hB₀
  set E : ℝ := Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * Sw + 1) with hE
  set Cexp : ℝ := 6 * (56 / 3 : ℝ) ^ 3 with hCexp
  set Ca : ℝ := 11 * Real.exp (11 * 32) * E * CW * Cp with hCa
  set Cb : ℝ := CW * (B₀ + E) * Cexp with hCb
  set G : ℝ := ∫ v : ℝ, Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2) with hG
  set J : ℝ := ∫ v : ℝ, (1 + |v|) ^ (-(5 / 2 : ℝ)) with hJ
  have hGint : Integrable fun v : ℝ => Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hG0 : 0 ≤ G := integral_nonneg fun v => (Real.exp_pos _).le
  have hJ0 : 0 ≤ J := integral_nonneg fun v => Real.rpow_nonneg (by positivity) _
  have hCa0 : 0 ≤ Ca := by positivity
  have hCb0 : 0 ≤ Cb := by positivity
  refine ⟨Ca * G + Cb * J + 1, by positivity, fun {Sy} hW {c ε ξ S} hε hcube hε1 hξ hL hS => ?_⟩
  have hε2 : ε ≤ 1 / 2 := by linarith
  have hc := eps_cube_inv hε hcube
  obtain ⟨V, hV1, hV5, hεV⟩ := exists_scale hε hε1
  have hSw : S ≤ Sw := (le_abs_self S).trans hS
  have hSabs : |S| ≤ Sw := hS
  have hexpV := exp_neg_sq_le hε hV1 hV5
  have hcε : c * ε = V ^ 5 := by
    have : c * ε = (c * ε ^ 3) * (ε ^ 2)⁻¹ := by field_simp
    rw [this, hcube, one_mul]
    have : V ^ 5 = (ε ^ 2)⁻¹ := by field_simp; linarith
    rw [this]
  -- the pointwise bound
  have hpt : ∀ v : ℝ, ‖(mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ -
            refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)) *
          Sy ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤
        ε ^ 2 * (Ca * Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2) + Cb * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by
    intro v
    have hWv := hW (w := (1 : ℂ) + (v : ℂ) * Complex.I) (by simp) (by simp)
    have him : ((1 : ℂ) + (v : ℂ) * Complex.I).im = v := by simp
    rw [him] at hWv
    have hEref : Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * S + ε / 2) ≤ E := by
      rw [hE]; apply Real.exp_le_exp.mpr; nlinarith only [hSw, hε2, mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.2 hSw)]
    have hp1 : 0 ≤ (1 + |v|) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    rw [norm_mul]
    by_cases hv : |v| ≤ V
    · -- near region
      have hζ : ε * (1 + |v|) ≤ 1 / 4 := by nlinarith only [hε1, hεV, mul_nonneg hε.le (sub_nonneg.2 hv)]
      have hM : ε ^ 2 * (1 + |v|) ^ 5 ≤ 32 := by
        have h1 : (1 + |v|) ^ 5 ≤ (2 * V) ^ 5 := by
          apply pow_le_pow_left₀ (by positivity); linarith
        calc ε ^ 2 * (1 + |v|) ^ 5 ≤ ε ^ 2 * (2 * V) ^ 5 := by gcongr
          _ = 32 * (ε ^ 2 * V ^ 5) := by ring
          _ = 32 := by rw [hV5]; ring
      have hk := K0_near_approx hε hcube hξ hL hζ hM
      have h1 : ‖mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ -
          refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤
          11 * Real.exp (11 * 32) * (ε ^ 2 * (1 + |v|) ^ 5) * (E * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12))) := by
        refine hk.trans ?_
        gcongr
      have h2 : (1 + |v|) ^ 5 * (1 + |v|) ^ (-(5 / 2 : ℝ)) * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12)) ≤
          Cp * Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2) := by
        have h3 := rpow_five_mul_neg_le (t := 1 + |v|) (by linarith [abs_nonneg v])
        have h4 := hpoly v
        calc (1 + |v|) ^ 5 * (1 + |v|) ^ (-(5 / 2 : ℝ)) * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12))
            ≤ (1 + |v|) ^ 3 * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12)) := by gcongr
          _ ≤ (Cp * Real.exp (Real.pi ^ 2 / 24 * v ^ 2)) * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12)) := by gcongr
          _ = Cp * Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2) := by
              rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      calc ‖mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ -
            refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)‖ *
            ‖Sy ((1 : ℂ) + (v : ℂ) * Complex.I)‖
          ≤ (11 * Real.exp (11 * 32) * (ε ^ 2 * (1 + |v|) ^ 5) * (E * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12)))) *
            (CW * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by gcongr
        _ = 11 * Real.exp (11 * 32) * E * CW * ε ^ 2 *
            ((1 + |v|) ^ 5 * (1 + |v|) ^ (-(5 / 2 : ℝ)) * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12))) := by ring
        _ ≤ 11 * Real.exp (11 * 32) * E * CW * ε ^ 2 * (Cp * Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2)) := by gcongr
        _ = ε ^ 2 * (Ca * Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2)) := by rw [hCa]; ring
        _ ≤ _ := by
            have : 0 ≤ ε ^ 2 * (Cb * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by positivity
            nlinarith only [this]
    · -- far region
      have hv' : V < |v| := not_le.mp hv
      have hv2 : V ^ 2 ≤ v ^ 2 := by rw [← sq_abs v]; exact pow_le_pow_left₀ (by linarith) hv'.le 2
      have hmin : V ^ 2 ≤ min (v ^ 2) (c * ε) := by
        refine le_min hv2 ?_
        rw [hcε]; exact pow_le_pow_right₀ hV1 (by norm_num)
      have hK := norm_K0_line_le (v := v) hε hcube hε2 hξ hL
      have hK' : ‖mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ‖ ≤ B₀ * (Cexp * ε ^ 2) := by
        refine hK.trans ?_
        have h1 : Real.exp (-((3 / 56 : ℝ) * min (v ^ 2) (c * ε))) ≤ Real.exp (-((3 / 56 : ℝ) * V ^ 2)) := by
          apply Real.exp_le_exp.mpr; linarith only [hmin]
        have h2 : 2 * Real.exp (1 + Real.pi ^ 2 * |S|) ≤ B₀ := by
          rw [hB₀]
          have := Real.exp_le_exp.mpr (by nlinarith only [hSabs, mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.2 hSabs)] : 1 + Real.pi ^ 2 * |S| ≤ 1 + Real.pi ^ 2 * Sw)
          linarith
        exact mul_le_mul h2 (h1.trans hexpV) (Real.exp_pos _).le (by positivity)
      have hR : ‖refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ E * (Cexp * ε ^ 2) := by
        rw [norm_refKernel_line]
        have h1 : Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12)) ≤ Cexp * ε ^ 2 := by
          refine le_trans ?_ hexpV
          apply Real.exp_le_exp.mpr
          nlinarith only [hv2, hpi, mul_nonneg (sub_nonneg.2 hpi.le) (sq_nonneg v), sq_nonneg V]
        exact mul_le_mul hEref h1 (Real.exp_pos _).le (by positivity)
      have hdiff : ‖mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ -
          refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ (B₀ + E) * (Cexp * ε ^ 2) := by
        refine (norm_sub_le _ _).trans ?_
        linarith
      calc ‖mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ -
            refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)‖ *
            ‖Sy ((1 : ℂ) + (v : ℂ) * Complex.I)‖
          ≤ ((B₀ + E) * (Cexp * ε ^ 2)) * (CW * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by gcongr
        _ = ε ^ 2 * (Cb * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by rw [hCb]; ring
        _ ≤ _ := by
            have : 0 ≤ ε ^ 2 * (Ca * Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2)) := by positivity
            nlinarith only [this]
  have hPsi : Integrable fun v : ℝ => ε ^ 2 * (Ca * Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2) +
      Cb * (1 + |v|) ^ (-(5 / 2 : ℝ))) :=
    ((hGint.const_mul Ca).add (integrable_one_add_abs_rpow.const_mul Cb)).const_mul _
  refine (norm_integral_le_of_norm_le hPsi (ae_of_all _ hpt)).trans ?_
  rw [integral_const_mul, integral_add (hGint.const_mul Ca) (integrable_one_add_abs_rpow.const_mul Cb),
    integral_const_mul, integral_const_mul]
  have hε2' : 0 ≤ ε ^ 2 := by positivity
  nlinarith only [hε2']

/-! ### The shift of `I_main` and of the reference integral -/


/-- info: 'FormalResearch.SignUncertainty.main_line_diff_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms main_line_diff_sym

end FormalResearch.SignUncertainty
