module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3Jets
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG1Jet

/-!
# `Gout` on the real segment `(0, 1/4)` (FIVE-0b, `ctu:jets`, `g₃`, step 4)

For `0 < x < 1/4` the Virasoro outer function is real and positive,
`Gout x = exp(Re h̄_a(ε(x))) √(1-x) (1+x)⁻² (tip x)^{-1/4}` with `ε(x) = (4/π) arctan x` and
`tip x = arccos(m(x))/arsinh √(1 - m(x)²)`, `m(x) = 2√2 x/(1+x²)`.  Hence
`log Re Gout x = Re h̄_a(ε x) + ½ log(1-x) - 2 log(1+x) - ¼ log tip x` (`log_gout_real`).  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- The real tip function `arccos m / arsinh √(1 - m²)` evaluated at `m(x)`. -/
noncomputable def tipR (x : ℝ) : ℝ := Real.arccos (mR x) / phiR (mR x)

/-- The real edge point `ε(x) = (4/π) arctan x` of the strip. -/
noncomputable def epsR (x : ℝ) : ℝ := 4 / π * Real.arctan x

lemma mC_real (x : ℝ) : mC (x : ℂ) = ((mR x : ℝ) : ℂ) := by
  unfold mC mR; push_cast; ring

lemma mR_pos {x : ℝ} (h0 : 0 < x) : 0 < mR x := by
  unfold mR; positivity

lemma mR_lt_one {x : ℝ} (h0 : 0 < x) (h4 : x < 1 / 4) : mR x < 1 := by
  unfold mR
  have h2 : √2 < 15 / 8 := by
    rw [show (15 / 8 : ℝ) = √((15 / 8) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [div_lt_one (by positivity)]
  nlinarith only [h2, h0, h4, sq_nonneg x]

lemma tipR_pos {x : ℝ} (h0 : 0 < x) (h4 : x < 1 / 4) : 0 < tipR x := by
  have hm := mR_lt_one h0 h4
  have hm0 := mR_pos h0
  unfold tipR phiR
  have h1 : 0 < Real.arccos (mR x) := Real.arccos_pos.mpr hm
  have h2 : 0 < 1 - mR x ^ 2 := by nlinarith only [hm, hm0]
  have h3 : 0 < Real.arsinh (√(1 - mR x ^ 2)) := Real.arsinh_pos_iff.mpr (Real.sqrt_pos.mpr h2)
  positivity

lemma tipE_real {m : ℝ} (h0 : 0 < m) (h1 : m < 1) :
    tipE (m : ℂ) = ((Real.arccos m / √(1 - m ^ 2) : ℝ) : ℂ) := by
  have hc : 0 < 1 - m ^ 2 := by nlinarith only [h0, h1]
  have hn : ‖(m : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]; exact h1
  rw [← sInt_sub_one_sq hn (by simpa using h0)]
  have e : (m : ℂ) ^ 2 - 1 = -(((1 - m ^ 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [e, sInt_neg_real hc (by nlinarith only [h0])]
  rw [Real.arccos_eq_arcsin h0.le]

lemma tipExt_real {x : ℝ} (h0 : 0 < x) (h4 : x < 1 / 4) : tipExt (x : ℂ) = ((tipR x : ℝ) : ℂ) := by
  have hm := mR_lt_one h0 h4
  have hm0 := mR_pos h0
  have hc : 0 < 1 - mR x ^ 2 := by nlinarith only [hm, hm0]
  have hne : 1 + (x : ℂ) ^ 2 ≠ 0 := by
    have : (1 + (x : ℂ) ^ 2) = ((1 + x ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast (by positivity : (1 + x ^ 2 : ℝ) ≠ 0)
  unfold tipExt
  rw [uC_eq_one_sub_mC_sq hne, mC_real, tipE_real hm0 hm]
  have e : 1 - ((mR x : ℝ) : ℂ) ^ 2 = ((1 - mR x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e, sInt_pos_real hc]
  have hs : 0 < √(1 - mR x ^ 2) := Real.sqrt_pos.mpr hc
  have hA : 0 < Real.arsinh (√(1 - mR x ^ 2)) := Real.arsinh_pos_iff.mpr hs
  unfold tipR phiR
  rw [← Complex.ofReal_div]
  congr 1
  field_simp

lemma epsR_mem {x : ℝ} (h0 : 0 < x) (h4 : x < 1 / 4) : 0 < epsR x ∧ epsR x < 1 := by
  have hpi := Real.pi_pos
  unfold epsR
  have h1 : 0 < Real.arctan x := Real.arctan_pos.mpr h0
  have h2 : Real.arctan x < π / 4 := by
    rw [← Real.arctan_one]
    exact Real.arctan_strictMono (by linarith)
  refine ⟨by positivity, ?_⟩
  rw [div_mul_eq_mul_div, div_lt_one hpi]
  linarith

lemma sInv_real {x : ℝ} : sInv (x : ℂ) = ((epsR x : ℝ) : ℂ) := by
  unfold sInv epsR
  rw [← Complex.ofReal_arctan]; push_cast; ring

lemma hbarA_real_im {a : ℝ → ℝ} (ha : Amp a) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    hbarA a (ε : ℂ) = (((hbarA a (ε : ℂ)).re : ℝ) : ℂ) := by
  have hcl : (ε : ℂ) ∈ closedStrip := ⟨by simpa using h0.le, by simpa using h1.le⟩
  have := hbarA_conj ha hcl
  rw [Complex.conj_ofReal] at this
  have him := congrArg Complex.im this
  simp at him
  exact Complex.ext (by simp) (by simpa using (by linarith : (hbarA a (ε : ℂ)).im = 0))

/-- The real value of `Gout` on `(0, 1/4)`. -/
noncomputable def goutR (x : ℝ) : ℝ :=
  Real.exp (hbarA aAmp (epsR x : ℂ)).re * √(1 - x) / (1 + x) ^ 2 * tipR x ^ (-(1 / 4 : ℝ))

lemma gout_real {x : ℝ} (h0 : 0 < x) (h4 : x < 1 / 4) : Gout (x : ℂ) = ((goutR x : ℝ) : ℂ) := by
  obtain ⟨he0, he1⟩ := epsR_mem h0 h4
  have hx1 : (x : ℂ) ∈ closure halfDisc :=
    subset_closure ⟨by simpa [abs_of_pos h0] using (by linarith : x < 1), by simpa using h0⟩
  have hn : ‖(x : ℂ)‖ < 1 / 4 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]; exact h4
  have ht := tipR_pos h0 h4
  unfold Gout goutR
  rw [qBd_eq_tipExt hx1 hn, tipExt_real h0 h4, sInv_real, hbarA_real_im amp_aAmp he0 he1]
  have e1 : (1 - (x : ℂ)) ^ (1 / 2 : ℂ) = ((√(1 - x) : ℝ) : ℂ) := by
    have h := Complex.ofReal_cpow (by linarith : 0 ≤ 1 - x) (1 / 2 : ℝ)
    rw [show (((1 / 2 : ℝ)) : ℂ) = (1 / 2 : ℂ) by push_cast; ring] at h
    rw [show (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) by push_cast; ring, ← h, ← Real.sqrt_eq_rpow]
  have e2 : ((tipR x : ℝ) : ℂ) ^ (-(1 / 4 : ℂ)) = ((tipR x ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) := by
    have h := Complex.ofReal_cpow ht.le (-(1 / 4 : ℝ))
    push_cast at h
    exact h.symm
  simp only [Complex.ofReal_re]
  rw [e1, e2, ← Complex.ofReal_exp]
  push_cast
  ring

lemma gout_re_pos {x : ℝ} (h0 : 0 < x) (h4 : x < 1 / 4) : 0 < (Gout (x : ℂ)).re := by
  rw [gout_real h0 h4, Complex.ofReal_re]
  have := tipR_pos h0 h4
  unfold goutR
  have h1 : 0 < 1 - x := by linarith
  positivity

/-- **The logarithm of `Gout` on the real segment.** -/
lemma log_gout_real {x : ℝ} (h0 : 0 < x) (h4 : x < 1 / 4) :
    Real.log (Gout (x : ℂ)).re = (hbarA aAmp (epsR x : ℂ)).re + Real.log (1 - x) / 2 -
      2 * Real.log (1 + x) - Real.log (tipR x) / 4 := by
  rw [gout_real h0 h4, Complex.ofReal_re]
  have ht := tipR_pos h0 h4
  have h1 : 0 < 1 - x := by linarith
  have h2 : 0 < 1 + x := by linarith
  unfold goutR
  rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_sqrt h1.le, Real.log_pow,
    Real.log_rpow ht]
  push_cast
  ring

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.log_gout_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.log_gout_real

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gout_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gout_re_pos
