module

public import FormalResearch.CohnElkies.ComplexEdgePhase

/-!
# Small-argument expansion of `S̃₀` (`lem:radial-compactness`, Step 3)

`‖g(z) - π² z²/12‖ ≤ 10 ‖z‖⁴` for `‖z‖ ≤ 1/4` (`g = stripG`), hence
`‖S̃₀(ζ) - π² ζ³/36‖ ≤ 10 ‖ζ‖⁵` for `‖ζ‖ ≤ 1/4` (`stripS0Tilde_sub_le`): the complex expansion behind the
limit `c S̃₀(c^{-1/3} w) → π² w³/36`.
-/

@[expose] public section

open Complex Set Filter Topology intervalIntegral MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

lemma tan_div_sub_le {x : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ ≤ 2 / 5) :
    ‖Complex.tan x / x - 1 - x ^ 2 / 3‖ ≤ ‖x‖ ^ 4 := by
  have ha : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set a := ‖x‖ with hadef
  have hs := Complex.sin_bound (x := x) (by linarith)
  have hc := Complex.cos_bound (x := x) (by linarith)
  set P : ℂ := Complex.sin x - (x - x ^ 3 / 6) with hP
  set Q : ℂ := Complex.cos x - (1 - x ^ 2 / 2) with hQ
  have hcos : 1 / 2 ≤ ‖Complex.cos x‖ := by
    have h1 : ‖Complex.cos x - 1‖ ≤ a ^ 2 / 2 + a ^ 4 * (5 / 96) := by
      have : Complex.cos x - 1 = Q - x ^ 2 / 2 := by rw [hQ]; ring
      rw [this]
      calc ‖Q - x ^ 2 / 2‖ ≤ ‖Q‖ + ‖x ^ 2 / 2‖ := norm_sub_le _ _
        _ ≤ a ^ 4 * (5 / 96) + a ^ 2 / 2 := by
          gcongr
          simp [norm_pow, hadef]
        _ = _ := by ring
    have h2 : ‖(1 : ℂ)‖ - ‖Complex.cos x - 1‖ ≤ ‖Complex.cos x‖ := by
      have := norm_sub_norm_le (1 : ℂ) (1 - Complex.cos x)
      rw [norm_sub_rev] at this
      simpa using this
    simp only [norm_one] at h2
    have ha2 : a ^ 2 ≤ 4 / 25 := by nlinarith
    have ha4 : a ^ 4 ≤ 16 / 625 := by
      have : a ^ 4 = (a ^ 2) ^ 2 := by ring
      rw [this]; nlinarith [sq_nonneg a]
    linarith
  have hcne : Complex.cos x ≠ 0 := by
    intro h; rw [h] at hcos; simp at hcos; linarith
  have key : Complex.tan x / x - 1 - x ^ 2 / 3 =
      (P + x ^ 5 / 6 - x * Q * (1 + x ^ 2 / 3)) / (x * Complex.cos x) := by
    rw [Complex.tan_eq_sin_div_cos, hP, hQ]
    field_simp
    ring
  rw [key, norm_div, norm_mul]
  have hden : a * (1 / 2) ≤ a * ‖Complex.cos x‖ := by gcongr
  have hnum : ‖P + x ^ 5 / 6 - x * Q * (1 + x ^ 2 / 3)‖ ≤
      a ^ 5 / 100 + a ^ 5 / 6 + a * (a ^ 4 * (5 / 96)) * (1 + a ^ 2 / 3) := by
    calc ‖P + x ^ 5 / 6 - x * Q * (1 + x ^ 2 / 3)‖
        ≤ ‖P‖ + ‖x ^ 5 / 6‖ + ‖x * Q * (1 + x ^ 2 / 3)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ a ^ 5 / 100 + a ^ 5 / 6 + a * (a ^ 4 * (5 / 96)) * (1 + a ^ 2 / 3) := by
          gcongr
          · simp [norm_pow, hadef]
          · rw [norm_mul, norm_mul]
            refine mul_le_mul (mul_le_mul le_rfl hc (norm_nonneg _) ha.le) ?_ (norm_nonneg _)
              (by positivity)
            calc ‖1 + x ^ 2 / 3‖ ≤ ‖(1 : ℂ)‖ + ‖x ^ 2 / 3‖ := norm_add_le _ _
              _ = 1 + a ^ 2 / 3 := by simp [norm_pow, hadef]
  rw [div_le_iff₀ (by positivity)]
  refine hnum.trans ?_
  have : a ^ 4 * (a * ‖Complex.cos x‖) ≥ a ^ 4 * (a * (1 / 2)) := by gcongr
  nlinarith [pow_pos ha 5, pow_pos ha 4, pow_pos ha 6, pow_pos ha 7]

lemma stripG_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    ‖stripG z - (Real.pi ^ 2 / 12 : ℂ) * z ^ 2‖ ≤ 10 * ‖z‖ ^ 4 := by
  by_cases hz0 : z = 0
  · subst hz0; simp [stripG]
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  set x : ℂ := (Real.pi : ℂ) * z / 2 with hx
  have hxn : ‖x‖ = Real.pi * ‖z‖ / 2 := by
    rw [hx, norm_div, norm_mul]; simp [abs_of_pos hpi0]
  have hx0 : x ≠ 0 := by
    rw [hx]; exact div_ne_zero (mul_ne_zero (by exact_mod_cast hpi0.ne') hz0) two_ne_zero
  have hxle : ‖x‖ ≤ 2 / 5 := by
    rw [hxn]; nlinarith [norm_nonneg z]
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have ht := tan_div_sub_le hx0 hxle
  set t : ℂ := Complex.tan x / x - 1 with htdef
  have hx2 : ‖x ^ 2 / 3‖ = ‖x‖ ^ 2 / 3 := by simp [norm_pow]
  have htn : ‖t‖ ≤ ‖x‖ ^ 2 / 3 + ‖x‖ ^ 4 := by
    have : t = (t - x ^ 2 / 3) + x ^ 2 / 3 := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [hx2]
    have : ‖t - x ^ 2 / 3‖ ≤ ‖x‖ ^ 4 := by
      have e : t - x ^ 2 / 3 = Complex.tan x / x - 1 - x ^ 2 / 3 := rfl
      rw [e]; exact ht
    linarith
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have htn2 : ‖t‖ ≤ 1 / 2 := by
    refine htn.trans ?_
    nlinarith [sq_nonneg ‖x‖, pow_pos hxpos 3]
  have hlog := Complex.norm_log_one_add_sub_self_le (z := t) (by linarith)
  have hg : stripG z = Complex.log (1 + t) := by
    rw [stripG, ite_eq_right hz0, htdef]; congr 1; ring
  have hinv : (1 - ‖t‖)⁻¹ / 2 ≤ 1 := by
    rw [div_le_iff₀ (by norm_num), inv_le_iff_one_le_mul₀ (by linarith)]; nlinarith
  have hlog2 : ‖Complex.log (1 + t) - t‖ ≤ ‖t‖ ^ 2 := by
    calc ‖Complex.log (1 + t) - t‖ ≤ ‖t‖ ^ 2 * (1 - ‖t‖)⁻¹ / 2 := hlog
      _ = ‖t‖ ^ 2 * ((1 - ‖t‖)⁻¹ / 2) := by ring
      _ ≤ ‖t‖ ^ 2 * 1 := by gcongr
      _ = _ := by ring
  have hpz : (Real.pi ^ 2 / 12 : ℂ) * z ^ 2 = x ^ 2 / 3 := by
    rw [hx]; ring
  rw [hg, hpz]
  have e : Complex.log (1 + t) - x ^ 2 / 3 = (Complex.log (1 + t) - t) + (t - x ^ 2 / 3) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖t - x ^ 2 / 3‖ ≤ ‖x‖ ^ 4 := ht
  have h2 : ‖t‖ ^ 2 ≤ (‖x‖ ^ 2 / 3 + ‖x‖ ^ 4) ^ 2 := by gcongr
  have h3 : (‖x‖ ^ 2 / 3 + ‖x‖ ^ 4) ^ 2 ≤ ‖x‖ ^ 4 / 2 := by
    have : ‖x‖ ^ 2 ≤ 4 / 25 := by nlinarith
    nlinarith [pow_pos hxpos 4, pow_pos hxpos 6, pow_pos hxpos 8]
  have h4 : ‖x‖ ^ 4 ≤ (62 / 10) * ‖z‖ ^ 4 := by
    rw [hxn]
    have : (Real.pi * ‖z‖ / 2) ^ 4 = (Real.pi / 2) ^ 4 * ‖z‖ ^ 4 := by ring
    rw [this]
    have : (Real.pi / 2) ^ 4 ≤ 62 / 10 := by
      have : Real.pi / 2 ≤ 1.575 := by linarith
      calc (Real.pi / 2) ^ 4 ≤ 1.575 ^ 4 := by gcongr
        _ ≤ 62 / 10 := by norm_num
    nlinarith [pow_pos hzn 4]
  nlinarith [pow_pos hzn 4]

lemma stripS0Tilde_sub_le {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1 / 4) :
    ‖stripS0Tilde ζ - (Real.pi ^ 2 / 36 : ℂ) * ζ ^ 3‖ ≤ 10 * ‖ζ‖ ^ 5 := by
  have hmaps : ∀ s ∈ Icc (0 : ℝ) 1, (s : ℂ) * ζ ∈ edgeStrip := by
    intro s hs
    simp only [edgeStrip, Set.mem_ofPred_eq]
    have h1 : |((s : ℂ) * ζ).re| ≤ ‖(s : ℂ) * ζ‖ := Complex.abs_re_le_norm _
    have h2 : ‖(s : ℂ) * ζ‖ ≤ ‖ζ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1]
      nlinarith [norm_nonneg ζ, hs.2]
    linarith
  have hcont : ContinuousOn (fun s : ℝ => stripG ((s : ℂ) * ζ) * ζ) (Icc 0 1) :=
    ((continuousOn_stripG.comp (by fun_prop) hmaps).mul continuousOn_const)
  have hI : IntervalIntegrable (fun s : ℝ => stripG ((s : ℂ) * ζ) * ζ) volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one
  have hI2 : IntervalIntegrable (fun s : ℝ => (Real.pi ^ 2 / 12 : ℂ) * ((s : ℂ) * ζ) ^ 2 * ζ) volume 0 1 :=
    (by fun_prop : Continuous fun s : ℝ => (Real.pi ^ 2 / 12 : ℂ) * ((s : ℂ) * ζ) ^ 2 * ζ).intervalIntegrable _ _
  have hval : ∫ s in (0 : ℝ)..1, (Real.pi ^ 2 / 12 : ℂ) * ((s : ℂ) * ζ) ^ 2 * ζ =
      (Real.pi ^ 2 / 36 : ℂ) * ζ ^ 3 := by
    have : ∀ s : ℝ, (Real.pi ^ 2 / 12 : ℂ) * ((s : ℂ) * ζ) ^ 2 * ζ =
        ((Real.pi ^ 2 / 12 : ℂ) * ζ ^ 3) * ((s ^ 2 : ℝ) : ℂ) := fun s => by push_cast; ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, integral_pow]
    push_cast; ring
  unfold stripS0Tilde
  rw [← hval, ← intervalIntegral.integral_sub hI hI2]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun s : ℝ => stripG ((s : ℂ) * ζ) * ζ - (Real.pi ^ 2 / 12 : ℂ) * ((s : ℂ) * ζ) ^ 2 * ζ)
    (C := 10 * ‖ζ‖ ^ 5) (fun s hs => by
      rw [uIoc_of_le zero_le_one] at hs
      have hsn : ‖(s : ℂ) * ζ‖ ≤ ‖ζ‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1.le]
        nlinarith [norm_nonneg ζ, hs.2]
      have h4 := stripG_sub_le (z := (s : ℂ) * ζ) (hsn.trans hζ)
      have : stripG ((s : ℂ) * ζ) * ζ - (Real.pi ^ 2 / 12 : ℂ) * ((s : ℂ) * ζ) ^ 2 * ζ =
          (stripG ((s : ℂ) * ζ) - (Real.pi ^ 2 / 12 : ℂ) * ((s : ℂ) * ζ) ^ 2) * ζ := by ring
      rw [this, norm_mul]
      calc ‖stripG ((s : ℂ) * ζ) - (Real.pi ^ 2 / 12 : ℂ) * ((s : ℂ) * ζ) ^ 2‖ * ‖ζ‖
          ≤ 10 * ‖(s : ℂ) * ζ‖ ^ 4 * ‖ζ‖ := by gcongr
        _ ≤ 10 * ‖ζ‖ ^ 4 * ‖ζ‖ := by gcongr
        _ = 10 * ‖ζ‖ ^ 5 := by ring)
  simpa using this

/-- info: 'FormalResearch.SignUncertainty.stripS0Tilde_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripS0Tilde_sub_le

end FormalResearch.SignUncertainty
