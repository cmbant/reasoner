module

public import FormalResearch.SignUncertainty.MellinMajorantH
public import FormalResearch.CohnElkies.MellinKernel
public import FormalResearch.CohnElkies.MellinEdgeValues

/-!
# `ℋ̂ = ℋ` on `0 ≤ Re ζ < 1` (`gt:7.4(2)`)

`hInt` (`MellinMajorantH`) is built from the Binet branch of `log Γ`; `stripH` (`CohnElkies.MellinKernel`)
is `∫_0^ζ log((1-t) tan(π t/2)/t) dt` with the principal logarithm. Both integrands have exponential
`R(t) = Γ((1+t)/2) Γ((3-t)/2) / (Γ((2+t)/2) Γ((2-t)/2))` and are continuous on `0 ≤ Re t < 1`, and they agree at
`t = 0` (`log (π/2)`), so they coincide there (an integer-valued continuous function along each ray is `0`).

* `gammaR_eq`, `exp_hLog`: the Gamma ratio is `R`, and `exp (hLog z) = R z`.
* `hLog_eq_stripHIntegrand`, `hInt_eq_stripH`, `re_hInt_imag`: the identification on `0 ≤ Re ζ < 1` and the
  left-edge value `Re ℋ̂(iτ) = τ arctan τ - (1/2) log(1+τ²)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special.ComplexStirling FormalResearch.CohnElkies

/-- The Gamma ratio equals the elementary function `R(w) = (1-w) tan(π w/2) / w`. -/
theorem gammaR_eq {w : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hre0 : -1 < w.re) (hre1 : w.re < 2) :
    Complex.Gamma ((1 + w) / 2) * Complex.Gamma ((3 - w) / 2) /
        (Complex.Gamma ((2 + w) / 2) * Complex.Gamma ((2 - w) / 2)) =
      (1 - w) * Complex.tan (Real.pi * w / 2) / w := by
  have hsin : Complex.sin (Real.pi * w / 2) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
    have hwk : w = 2 * k := by
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      apply mul_left_cancel₀ hpi
      linear_combination (2 : ℂ) * hk
    have hre : w.re = 2 * (k : ℝ) := by rw [hwk]; simp
    have hk1 : (-1 : ℝ) < 2 * k := by linarith
    have hk2 : (2 * k : ℝ) < 2 := by linarith
    have hk3 : (k : ℝ) < 1 := by linarith
    have hk4 : (-1 : ℝ) < k := by linarith
    have hk5 : k < 1 := by exact_mod_cast hk3
    have hk6 : -1 < k := by exact_mod_cast hk4
    have : k = 0 := by omega
    apply hw0; rw [hwk, this]; simp
  have hcos : Complex.cos (Real.pi * w / 2) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h
    have hwk : w = 2 * k + 1 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      apply mul_left_cancel₀ hpi
      linear_combination (2 : ℂ) * hk
    have hre : w.re = 2 * (k : ℝ) + 1 := by rw [hwk]; simp
    have hk3 : (k : ℝ) < 1 / 2 := by linarith
    have hk4 : (-1 : ℝ) < k := by linarith
    have hk5 : k < 1 := by
      have : (k : ℝ) < 1 := by linarith
      exact_mod_cast this
    have hk6 : -1 < k := by exact_mod_cast hk4
    have : k = 0 := by omega
    apply hw1; rw [hwk, this]; simp
  have hA := Complex.Gamma_mul_Gamma_one_sub ((1 + w) / 2)
  have hB := Complex.Gamma_mul_Gamma_one_sub (w / 2)
  have e1 : (1 : ℂ) - (1 + w) / 2 = (1 - w) / 2 := by ring
  have e2 : (3 - w) / 2 = (1 - w) / 2 + 1 := by ring
  have e3 : (2 + w) / 2 = w / 2 + 1 := by ring
  have e4 : (2 - w) / 2 = 1 - w / 2 := by ring
  have hsin1 : Complex.sin (Real.pi * ((1 + w) / 2)) = Complex.cos (Real.pi * w / 2) := by
    have : (Real.pi : ℂ) * ((1 + w) / 2) = Real.pi * w / 2 + Real.pi / 2 := by ring
    rw [this, Complex.sin_add_pi_div_two]
  have hne1 : (1 - w) / 2 ≠ 0 := by
    intro h; apply hw1; linear_combination (-2 : ℂ) * h
  have hne2 : w / 2 ≠ 0 := by
    intro h; apply hw0; linear_combination (2 : ℂ) * h
  rw [e1] at hA
  rw [e2, e3, e4, Complex.Gamma_add_one _ hne1, Complex.Gamma_add_one _ hne2]
  rw [hsin1] at hA
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hA' : Complex.Gamma ((1 + w) / 2) * Complex.Gamma ((1 - w) / 2) =
      Real.pi / Complex.cos (Real.pi * w / 2) := hA
  have hB' : Complex.Gamma (w / 2) * Complex.Gamma (1 - w / 2) =
      Real.pi / Complex.sin (Real.pi * (w / 2)) := hB
  have hB'' : Complex.Gamma (w / 2) * Complex.Gamma (1 - w / 2) =
      Real.pi / Complex.sin (Real.pi * w / 2) := by rw [hB']; congr 2; ring
  have hnum : Complex.Gamma ((1 + w) / 2) * ((1 - w) / 2 * Complex.Gamma ((1 - w) / 2)) =
      (1 - w) / 2 * (Real.pi / Complex.cos (Real.pi * w / 2)) := by
    rw [← hA']; ring
  have hden : w / 2 * Complex.Gamma (w / 2) * Complex.Gamma (1 - w / 2) =
      w / 2 * (Real.pi / Complex.sin (Real.pi * w / 2)) := by
    rw [← hB'']; ring
  rw [Complex.tan_eq_sin_div_cos]
  rw [show Complex.Gamma ((1 + w) / 2) * ((1 - w) / 2 * Complex.Gamma ((1 - w) / 2)) /
      (w / 2 * Complex.Gamma (w / 2) * Complex.Gamma (1 - w / 2)) =
      ((1 - w) / 2 * (Real.pi / Complex.cos (Real.pi * w / 2))) /
      (w / 2 * (Real.pi / Complex.sin (Real.pi * w / 2))) by rw [hnum, hden] ]
  field_simp

/-- The value of the Gamma ratio at `0` is `π/2`. -/
theorem gammaR_zero : Complex.Gamma ((1 + 0) / 2) * Complex.Gamma ((3 - 0) / 2) /
    (Complex.Gamma ((2 + 0) / 2) * Complex.Gamma ((2 - 0) / 2)) = ((Real.pi / 2 : ℝ) : ℂ) := by
  have h1 : (1 + 0 : ℂ) / 2 = 1 / 2 := by norm_num
  have h2 : (3 - 0 : ℂ) / 2 = 1 / 2 + 1 := by norm_num
  have h3 : (2 + 0 : ℂ) / 2 = 1 := by norm_num
  have h4 : (2 - 0 : ℂ) / 2 = 1 := by norm_num
  rw [h1, h2, h3, h4, Complex.Gamma_add_one _ (by norm_num), Complex.Gamma_one,
    Complex.Gamma_one_half_eq]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : (Real.pi : ℂ) ^ (1 / 2 : ℂ) * (Real.pi : ℂ) ^ (1 / 2 : ℂ) = Real.pi := by
    rw [← Complex.cpow_add _ _ hpi]; norm_num
  have hs0 : (Real.pi : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  push_cast
  field_simp
  linear_combination hs

/-- `exp (hLog z)` is the Gamma ratio `R(z)` on `-1 < Re z < 2`. -/
theorem exp_hLog {z : ℂ} (hz : z ∈ hStrip) :
    Complex.exp (hLog z) = Complex.Gamma ((1 + z) / 2) * Complex.Gamma ((3 - z) / 2) /
        (Complex.Gamma ((2 + z) / 2) * Complex.Gamma ((2 - z) / 2)) := by
  obtain ⟨h0, h1⟩ := hz
  have p1 : 0 < ((1 + z) / 2).re := by simp; linarith
  have p2 : 0 < ((3 - z) / 2).re := by simp; linarith
  have p3 : 0 < ((2 + z) / 2).re := by simp; linarith
  have p4 : 0 < ((2 - z) / 2).re := by simp; linarith
  unfold hLog
  rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_add, exp_binetLogGamma p1,
    exp_binetLogGamma p2, exp_binetLogGamma p3, exp_binetLogGamma p4, div_div]

/-- The Gamma ratio `R(z)` does not vanish on `-1 < Re z < 2`. -/
theorem exp_hLog_ne_zero {z : ℂ} (hz : z ∈ hStrip) :
    Complex.Gamma ((1 + z) / 2) * Complex.Gamma ((3 - z) / 2) /
        (Complex.Gamma ((2 + z) / 2) * Complex.Gamma ((2 - z) / 2)) ≠ 0 := by
  obtain ⟨h0, h1⟩ := hz
  have p1 : 0 < ((1 + z) / 2).re := by simp; linarith
  have p2 : 0 < ((3 - z) / 2).re := by simp; linarith
  have p3 : 0 < ((2 + z) / 2).re := by simp; linarith
  have p4 : 0 < ((2 - z) / 2).re := by simp; linarith
  exact div_ne_zero (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos p1)
    (Complex.Gamma_ne_zero_of_re_pos p2)) (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos p3)
    (Complex.Gamma_ne_zero_of_re_pos p4))

/-- `hLog 0 = log (π/2)`. -/
theorem hLog_zero : hLog 0 = ((Real.log (Real.pi / 2) : ℝ) : ℂ) := by
  have hr : hLog 0 = (((Real.log (Real.Gamma (1 / 2)) + Real.log (Real.Gamma (3 / 2))
      - Real.log (Real.Gamma 1) - Real.log (Real.Gamma 1)) : ℝ) : ℂ) := by
    unfold hLog
    have e1 : ((1 + 0 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((3 - 0 : ℂ) / 2) = ((3 / 2 : ℝ) : ℂ) := by push_cast; ring
    have e3 : ((2 + 0 : ℂ) / 2) = ((1 : ℝ) : ℂ) := by push_cast; ring
    have e4 : ((2 - 0 : ℂ) / 2) = ((1 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, e3, e4, binetLogGamma_ofReal (by norm_num), binetLogGamma_ofReal (by norm_num),
      binetLogGamma_ofReal (by norm_num)]
    push_cast; ring
  have hexp := exp_hLog (zero_mem_hStrip)
  rw [gammaR_zero, hr, ← Complex.ofReal_exp] at hexp
  have h' := Complex.ofReal_injective hexp
  rw [hr, ← Real.log_exp (Real.log (Real.Gamma (1 / 2)) + Real.log (Real.Gamma (3 / 2))
      - Real.log (Real.Gamma 1) - Real.log (Real.Gamma 1)), h']

/-- A continuous function on `[0, 1]` with `exp ∘ φ = 1` and `φ 0 = 0` vanishes at `1`. -/
theorem eq_zero_of_exp_eq_one_of_continuousOn {φ : ℝ → ℂ} (hc : ContinuousOn φ (Icc 0 1))
    (hexp : ∀ s ∈ Icc (0 : ℝ) 1, Complex.exp (φ s) = 1) (h0 : φ 0 = 0) : φ 1 = 0 := by
  have hint : ∀ s ∈ Icc (0 : ℝ) 1, ∃ n : ℤ, φ s = n * (2 * Real.pi * Complex.I) := fun s hs =>
    Complex.exp_eq_one_iff.mp (hexp s hs)
  set ψ : ℝ → ℝ := fun s => (φ s).im / (2 * Real.pi) with hψ
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hψc : ContinuousOn ψ (Icc 0 1) := (Complex.continuous_im.comp_continuousOn hc).div_const _
  have hψint : ∀ s ∈ Icc (0 : ℝ) 1, ∃ n : ℤ, ψ s = n := by
    intro s hs
    obtain ⟨n, hn⟩ := hint s hs
    refine ⟨n, ?_⟩
    simp only [hψ, hn, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
      Complex.I_re, Complex.I_im]
    simp
  have hψ0 : ψ 0 = 0 := by simp [hψ, h0]
  obtain ⟨n, hn⟩ := hint 1 (by simp)
  obtain ⟨n', hn'⟩ := hψint 1 (by simp)
  have hnn : (n' : ℝ) = n := by
    rw [← hn']
    simp only [hψ, hn, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
      Complex.I_re, Complex.I_im]
    simp
  have hn'n : n' = n := by exact_mod_cast hnn
  have hn0 : n = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hle : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
      have hmem : (-(1 : ℝ) / 2) ∈ Icc (ψ 1) (ψ 0) := by
        rw [hn', hψ0, hn'n]; constructor <;> linarith
      obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc' zero_le_one hψc hmem
      obtain ⟨m, hm⟩ := hψint s hs
      rw [hm] at hsv
      have h2 : ((2 * m : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by push_cast; linarith
      have h3 : 2 * m = -1 := by exact_mod_cast h2
      omega
    · have hge : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have hmem : ((1 : ℝ) / 2) ∈ Icc (ψ 0) (ψ 1) := by
        rw [hn', hψ0, hn'n]; constructor <;> linarith
      obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc zero_le_one hψc hmem
      obtain ⟨m, hm⟩ := hψint s hs
      rw [hm] at hsv
      have h2 : ((2 * m : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by push_cast; linarith
      have h3 : 2 * m = 1 := by exact_mod_cast h2
      omega
  rw [hn, hn0]; simp

/-- The Binet-branch integrand `hLog` equals the principal-branch integrand on `0 ≤ Re t < 1`. -/
theorem hLog_eq_stripHIntegrand {t : ℂ} (ht0 : 0 ≤ t.re) (ht1 : t.re < 1) :
    hLog t = stripHIntegrand t := by
  have htS : t ∈ hStrip := ⟨by linarith, by linarith⟩
  have hre : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ ((s : ℂ) * t).re ∧ ((s : ℂ) * t).re < 1 := by
    intro s hs
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    refine ⟨mul_nonneg hs.1 ht0, ?_⟩
    by_cases hs0 : s = 0
    · simp [hs0]
    · have hs_pos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      nlinarith [hs.2, mul_pos hs_pos (sub_pos.mpr ht1)]
  have hcont1 : ContinuousOn (fun s : ℝ => hLog ((s : ℂ) * t)) (Icc 0 1) :=
    continuousOn_hLog.comp (by fun_prop) (fun s hs => smul_mem_hStrip htS hs)
  have hcont2 : ContinuousOn (fun s : ℝ => stripHIntegrand ((s : ℂ) * t)) (Icc 0 1) := by
    have h : ContinuousOn (fun s : ℝ => Complex.log (1 - (s : ℂ) * t) + stripG ((s : ℂ) * t) +
        Complex.log (Real.pi / 2)) (Icc 0 1) :=
      ((continuousOn_log_one_sub_mul ht1).add (continuousOn_stripG_unit ht0 ht1)).add
        continuousOn_const
    exact h.congr fun s hs => stripHIntegrand_eq (hre s hs).1 (hre s hs).2
  have hmain := eq_zero_of_exp_eq_one_of_continuousOn
    (φ := fun s : ℝ => hLog ((s : ℂ) * t) - stripHIntegrand ((s : ℂ) * t))
    (hcont1.sub hcont2) ?_ ?_
  · simpa [sub_eq_zero] using hmain
  · intro s hs
    obtain ⟨h0, h1⟩ := hre s hs
    have hmS : ((s : ℂ) * t) ∈ hStrip := smul_mem_hStrip htS hs
    rw [Complex.exp_sub, exp_hLog hmS]
    by_cases hz : (s : ℂ) * t = 0
    · rw [hz]
      have : stripHIntegrand 0 = Complex.log (Real.pi / 2) := by simp [stripHIntegrand]
      have hpi2 : ((Real.pi / 2 : ℝ) : ℂ) = (Real.pi : ℂ) / 2 := by push_cast; rfl
      have hpi2ne : (Real.pi : ℂ) / 2 ≠ 0 :=
        div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) two_ne_zero
      rw [this, Complex.exp_log hpi2ne, gammaR_zero, hpi2]
      exact div_self hpi2ne
    · have hne1 : (s : ℂ) * t ≠ 1 := fun h => by
        have := congrArg Complex.re h; rw [Complex.one_re] at this; linarith
      rw [gammaR_eq hz hne1 hmS.1 hmS.2]
      have hR : (1 - (s : ℂ) * t) * Complex.tan (Real.pi * ((s : ℂ) * t) / 2) / ((s : ℂ) * t) ≠ 0 := by
        rw [← gammaR_eq hz hne1 hmS.1 hmS.2]
        exact exp_hLog_ne_zero hmS
      simp only [stripHIntegrand, hz, ↓reduceIte]
      rw [Complex.exp_log hR]
      exact div_self hR
  · have h0 : stripHIntegrand 0 = Complex.log (Real.pi / 2) := by simp [stripHIntegrand]
    simp only [Complex.ofReal_zero, zero_mul, hLog_zero, h0]
    rw [Complex.ofReal_log (by positivity)]
    simp

/-- `ℋ̂ = ℋ` on `0 ≤ Re ζ < 1`. -/
theorem hInt_eq_stripH {ζ : ℂ} (hζ0 : 0 ≤ ζ.re) (hζ1 : ζ.re < 1) : hInt ζ = stripH ζ := by
  unfold hInt stripH
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  have hsre0 : 0 ≤ ((s : ℂ) * ζ).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hs.1 hζ0
  have hsre1 : ((s : ℂ) * ζ).re < 1 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    by_cases hs0 : s = 0
    · simp [hs0]
    · have hs_pos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      nlinarith [hs.2, mul_pos hs_pos (sub_pos.mpr hζ1)]
  simp only [hLog_eq_stripHIntegrand hsre0 hsre1]
  ring

/-- Real part of `ℋ̂` on the imaginary axis (`gt:7.4(2)`, left edge). -/
theorem re_hInt_imag (τ : ℝ) :
    (hInt ((τ : ℂ) * Complex.I)).re = τ * Real.arctan τ - (1 / 2) * Real.log (1 + τ ^ 2) := by
  rw [hInt_eq_stripH (by simp) (by simp)]
  exact re_stripH_imag τ

/-- info: 'FormalResearch.SignUncertainty.gammaR_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gammaR_eq

/-- info: 'FormalResearch.SignUncertainty.gammaR_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gammaR_zero

/-- info: 'FormalResearch.SignUncertainty.exp_hLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exp_hLog

/-- info: 'FormalResearch.SignUncertainty.exp_hLog_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exp_hLog_ne_zero

/-- info: 'FormalResearch.SignUncertainty.hLog_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hLog_zero

/-- info: 'FormalResearch.SignUncertainty.eq_zero_of_exp_eq_one_of_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_zero_of_exp_eq_one_of_continuousOn

/-- info: 'FormalResearch.SignUncertainty.hLog_eq_stripHIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hLog_eq_stripHIntegrand

/-- info: 'FormalResearch.SignUncertainty.hInt_eq_stripH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hInt_eq_stripH

/-- info: 'FormalResearch.SignUncertainty.re_hInt_imag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms re_hInt_imag

end FormalResearch.SignUncertainty
