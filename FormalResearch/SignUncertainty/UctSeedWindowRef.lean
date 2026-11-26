module

public import FormalResearch.SignUncertainty.UctSeedWindowDiff

/-!
# The reference-symbol difference on the line `Re w = 1` (F2a helper for `uct:seed-asymp` (1))

`ref_symbol_diff`: if two symbols `Sy, Ey` have weighted bounds on `Re w = 1` and differ by `O(ε²)` on the window
`ε(1+|v|) ≤ 1/4`, then `∫ refKernel S ε (1+iv) (Sy - Ey)(1+iv) dv = O(ε²)` (Gaussian decay of the reference kernel on the
line, `norm_refKernel_line`, and `exp_neg_sq_le` for the tail `|v| > V = ε^{-2/5}`).
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

theorem ref_symbol_diff (Sw Cd CW CE : ℝ) (hCd : 0 ≤ Cd) (hCW : 0 ≤ CW) (hCE : 0 ≤ CE) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Sy Ey : ℂ → ℂ} {ε S : ℝ}, 0 < ε → ε ≤ 1 / 32 → |S| ≤ Sw →
      (∀ v : ℝ, ‖Sy ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ CW * (1 + |v|) ^ (-(5 / 2 : ℝ))) →
      (∀ v : ℝ, ‖Ey ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ CE * (1 + |v|) ^ (-(5 / 2 : ℝ))) →
      (∀ v : ℝ, ε * (1 + |v|) ≤ 1 / 4 →
        ‖Sy ((1 : ℂ) + (v : ℂ) * Complex.I) - Ey ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ Cd * ε ^ 2) →
      ‖∫ v : ℝ, refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I) *
          (Sy ((1 : ℂ) + (v : ℂ) * Complex.I) - Ey ((1 : ℂ) + (v : ℂ) * Complex.I))‖ ≤ C * ε ^ 2 := by
  have hpi : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  set Eref : ℝ := Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * Sw + 1) with hEref0
  set Cexp : ℝ := 6 * (56 / 3 : ℝ) ^ 3 with hCexp
  set Ca : ℝ := Eref * Cd with hCa
  set Cb : ℝ := Eref * Cexp * (CW + CE) with hCb
  set G : ℝ := ∫ v : ℝ, Real.exp (-(Real.pi ^ 2 / 12) * v ^ 2) with hG
  set J : ℝ := ∫ v : ℝ, (1 + |v|) ^ (-(5 / 2 : ℝ)) with hJ
  have hGint : Integrable fun v : ℝ => Real.exp (-(Real.pi ^ 2 / 12) * v ^ 2) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hG0 : 0 ≤ G := integral_nonneg fun v => (Real.exp_pos _).le
  have hJ0 : 0 ≤ J := integral_nonneg fun v => Real.rpow_nonneg (by positivity) _
  have hEr0 : 0 < Eref := Real.exp_pos _
  have hCa0 : 0 ≤ Ca := by positivity
  have hCb0 : 0 ≤ Cb := by positivity
  refine ⟨Ca * G + Cb * J + 1, by positivity, fun {Sy Ey} {ε S} hε hε1 hS hSy hEy hnear => ?_⟩
  have hε2 : ε ≤ 1 / 2 := by linarith
  obtain ⟨V, hV1, hV5, hεV⟩ := exists_scale hε hε1
  have hSw : S ≤ Sw := (le_abs_self S).trans hS
  have hexpV := exp_neg_sq_le hε hV1 hV5
  have hpt : ∀ v : ℝ, ‖refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I) *
          (Sy ((1 : ℂ) + (v : ℂ) * Complex.I) - Ey ((1 : ℂ) + (v : ℂ) * Complex.I))‖ ≤
        ε ^ 2 * (Ca * Real.exp (-(Real.pi ^ 2 / 12) * v ^ 2) + Cb * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by
    intro v
    have hp1 : 0 ≤ (1 + |v|) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    have hexpv : Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12)) = Real.exp (-(Real.pi ^ 2 / 12) * v ^ 2) := by
      congr 1; ring
    have hEreff : Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * S + ε / 2) ≤ Eref := by
      rw [hEref0]; apply Real.exp_le_exp.mpr
      nlinarith only [hSw, hε2, mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.2 hSw)]
    rw [norm_mul, norm_refKernel_line, hexpv]
    by_cases hv : |v| ≤ V
    · have hζ : ε * (1 + |v|) ≤ 1 / 4 := by nlinarith only [hε1, hεV, mul_nonneg hε.le (sub_nonneg.2 hv)]
      have hd := hnear v hζ
      calc Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * S + ε / 2) * Real.exp (-(Real.pi ^ 2 / 12) * v ^ 2) *
            ‖Sy ((1 : ℂ) + (v : ℂ) * Complex.I) - Ey ((1 : ℂ) + (v : ℂ) * Complex.I)‖
          ≤ Eref * Real.exp (-(Real.pi ^ 2 / 12) * v ^ 2) * (Cd * ε ^ 2) := by gcongr
        _ = ε ^ 2 * (Ca * Real.exp (-(Real.pi ^ 2 / 12) * v ^ 2)) := by rw [hCa]; ring
        _ ≤ _ := by
            have : 0 ≤ ε ^ 2 * (Cb * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by positivity
            nlinarith only [this]
    · have hv' : V < |v| := not_le.mp hv
      have hv2 : V ^ 2 ≤ v ^ 2 := by rw [← sq_abs v]; exact pow_le_pow_left₀ (by linarith) hv'.le 2
      have h1 : Real.exp (-(Real.pi ^ 2 / 12) * v ^ 2) ≤ Cexp * ε ^ 2 := by
        refine le_trans ?_ hexpV
        apply Real.exp_le_exp.mpr
        nlinarith only [hv2, hpi, mul_nonneg (sub_nonneg.2 hpi.le) (sq_nonneg v), sq_nonneg V]
      have hdiff : ‖Sy ((1 : ℂ) + (v : ℂ) * Complex.I) - Ey ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤
          (CW + CE) * (1 + |v|) ^ (-(5 / 2 : ℝ)) := by
        refine (norm_sub_le _ _).trans ?_
        have := hSy v
        have := hEy v
        linarith
      calc Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * S + ε / 2) * Real.exp (-(Real.pi ^ 2 / 12) * v ^ 2) *
            ‖Sy ((1 : ℂ) + (v : ℂ) * Complex.I) - Ey ((1 : ℂ) + (v : ℂ) * Complex.I)‖
          ≤ (Eref * (Cexp * ε ^ 2)) * ((CW + CE) * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by gcongr
        _ = ε ^ 2 * (Cb * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by rw [hCb]; ring
        _ ≤ _ := by
            have : 0 ≤ ε ^ 2 * (Ca * Real.exp (-(Real.pi ^ 2 / 12) * v ^ 2)) := by positivity
            nlinarith only [this]
  have hPsi : Integrable fun v : ℝ => ε ^ 2 * (Ca * Real.exp (-(Real.pi ^ 2 / 12) * v ^ 2) +
      Cb * (1 + |v|) ^ (-(5 / 2 : ℝ))) :=
    ((hGint.const_mul Ca).add (integrable_one_add_abs_rpow.const_mul Cb)).const_mul _
  refine (norm_integral_le_of_norm_le hPsi (ae_of_all _ hpt)).trans ?_
  rw [integral_const_mul, integral_add (hGint.const_mul Ca) (integrable_one_add_abs_rpow.const_mul Cb),
    integral_const_mul, integral_const_mul]
  have hε2' : 0 ≤ ε ^ 2 := by positivity
  nlinarith only [hε2']

/-- Multiplying the reference kernel by `e^{-λ ε w}` with `λ = θ + 1/2` shifts its linear coefficient to `π² S - θ ε`. -/
lemma refKernel_mul_exp (S ε θ : ℝ) (w : ℂ) :
    refKernel S ε w * Complex.exp (-(((θ + 1 / 2 : ℝ)) : ℂ) * ((ε : ℂ) * w)) = refKernel S (-2 * θ * ε) w := by
  unfold refKernel
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma integrable_line_weight {F : ℂ → ℂ} {B : ℝ} (hc : ContinuousOn F {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1})
    (hb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖F w‖ ≤ B * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) :
    Integrable fun v : ℝ => F ((1 : ℂ) + (v : ℂ) * Complex.I) := by
  have hline : Continuous fun v : ℝ => ((1 : ℂ) + (v : ℂ) * Complex.I) := by fun_prop
  have hmem : ∀ v : ℝ, ((1 : ℂ) + (v : ℂ) * Complex.I) ∈ {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} := fun v => by simp
  have hc1 : Continuous fun v : ℝ => F ((1 : ℂ) + (v : ℂ) * Complex.I) := hc.comp_continuous hline hmem
  refine (integrable_weight B).mono' hc1.aestronglyMeasurable (ae_of_all _ fun v => ?_)
  have := hb ((1 : ℂ) + (v : ℂ) * Complex.I) (by simp) (by simp)
  simpa using this

/-- info: 'FormalResearch.SignUncertainty.ref_symbol_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ref_symbol_diff

end FormalResearch.SignUncertainty
