module

public import FormalResearch.SignUncertainty.BinetFubini

/-!
# Vertical-line decay of the Binet remainder (`ct:dual-id` (1))

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:dual-id` (1).

**Proved**: for `Re w > 0` and `r ≥ 0`, `‖B_Bin^{(r)}(w)‖ ≤ r! 2^{r-1} / |w|^{r+1}`
(decay in `|w|`, not only in `Re w`).
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open FormalResearch.Asymptotics

namespace FormalResearch.SignUncertainty.BinetDecay

lemma integral_inv_pow_shift {m : ℝ} (hm : 0 < m) (k : ℕ) :
    IntegrableOn (fun s : ℝ => ((s + m) ^ (k + 2))⁻¹) (Ioi 0) ∧
    ∫ s in Ioi (0 : ℝ), ((s + m) ^ (k + 2))⁻¹ = (1 / ((k : ℝ) + 1)) * (m ^ (k + 1))⁻¹ := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun s : ℝ => -(1 / ((k : ℝ) + 1)) * ((s + m) ^ (k + 1))⁻¹)
      (((x + m) ^ (k + 2))⁻¹) x := by
    intro x hx
    have hpos : 0 < x + m := by have : (0 : ℝ) ≤ x := hx; linarith
    have h1 : HasDerivAt (fun s : ℝ => (s + m) ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * (x + m) ^ k) x := by
      have := ((hasDerivAt_id x).add_const m).fun_pow (k + 1)
      simpa using this
    have h2 := (h1.inv (pow_ne_zero _ hpos.ne')).const_mul (-(1 / ((k : ℝ) + 1)))
    refine h2.congr_deriv ?_
    push_cast
    field_simp
    ring
  have hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ ((x + m) ^ (k + 2))⁻¹ := fun x hx => by
    have : 0 < x + m := by have : (0 : ℝ) < x := hx; linarith
    positivity
  have hlim : Tendsto (fun s : ℝ => -(1 / ((k : ℝ) + 1)) * ((s + m) ^ (k + 1))⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => (s + m) ^ (k + 1)) atTop atTop :=
      (tendsto_pow_atTop (Nat.succ_ne_zero k)).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
    simpa using h.inv_tendsto_atTop.const_mul (-(1 / ((k : ℝ) + 1)))
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hnn hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hnn hlim]
  simp

/-- `|s + w| ≥ (s + |w|)/2` for `s ≥ 0`, `Re w ≥ 0`. -/
lemma half_le_norm_add {w : ℂ} (hw : 0 ≤ w.re) {s : ℝ} (hs : 0 ≤ s) :
    (s + ‖w‖) / 2 ≤ ‖(s : ℂ) + w‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hw2 : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, zero_add]
  nlinarith [mul_nonneg hs hw, sq_nonneg (s - ‖w‖), norm_nonneg w]


/-- **Decay of the derivatives of the Binet remainder in `|w|`.**  For `Re w > 0`,
`‖B_Bin^{(r)}(w)‖ ≤ r! 2^{r+2} / (8 |w|^{r+1})`. -/
theorem binetRem_iteratedDeriv_decay (r : ℕ) {w : ℂ} (hw : 0 < w.re) :
    ‖iteratedDeriv r binetRem w‖ ≤ (r.factorial : ℝ) * 2 ^ (r + 2) / (8 * ‖w‖ ^ (r + 1)) := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by simp [h] at hw)
  rw [iteratedDeriv_binetRem_P2 r hw, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  obtain ⟨hint, hval⟩ := integral_inv_pow_shift hwn r
  have hg : Integrable (fun s : ℝ => (((r + 1).factorial : ℝ) * 2 ^ (r + 2) / 8) * ((s + ‖w‖) ^ (r + 2))⁻¹)
      (volume.restrict (Ioi (0 : ℝ))) := hint.const_mul _
  refine (norm_integral_le_of_norm_le hg ?_).trans ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have hs' : (0 : ℝ) ≤ s := le_of_lt hs
    have hlow := half_le_norm_add hw.le hs'
    have hpos : 0 < (s + ‖w‖) / 2 := by positivity
    rw [norm_mul, Complex.norm_real, norm_div, Complex.norm_natCast, norm_pow,
      Real.norm_of_nonneg (binP2_nonneg s)]
    have hp : ((s + ‖w‖) / 2) ^ (r + 2) ≤ ‖(s : ℂ) + w‖ ^ (r + 2) := pow_le_pow_left₀ hpos.le hlow _
    calc binP2 s * (((r + 1).factorial : ℝ) / ‖(s : ℂ) + w‖ ^ (r + 2))
        ≤ (1 / 8) * (((r + 1).factorial : ℝ) / ((s + ‖w‖) / 2) ^ (r + 2)) := by
          refine mul_le_mul (binP2_le s) ?_ (by positivity) (by norm_num)
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hp
      _ = (((r + 1).factorial : ℝ) * 2 ^ (r + 2) / 8) * ((s + ‖w‖) ^ (r + 2))⁻¹ := by
          rw [div_pow]
          field_simp
  · rw [integral_const_mul, hval]
    have hfac : ((r + 1).factorial : ℝ) = ((r : ℝ) + 1) * r.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac]
    have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    exact le_rfl

/-- info: 'FormalResearch.SignUncertainty.BinetDecay.binetRem_iteratedDeriv_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binetRem_iteratedDeriv_decay

end FormalResearch.SignUncertainty.BinetDecay
