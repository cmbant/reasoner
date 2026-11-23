module

public import FormalResearch.SignUncertainty.RadialKernelLimit
public import FormalResearch.SignUncertainty.DeepLobeKernel
public import FormalResearch.SignUncertainty.DeepLobeRegionII

/-!
# Domination of the rescaled kernel (`lem:radial-compactness`, Step 3)

For `c ≥ 1000` and `|s| ≤ S` with `π² ε_c² S ≤ 1/2`:
`‖K_c(1+iv, s)‖ ≤ 4 e^{4/9 + π² S} (1 + v²/100)^{-300/56}` (`radialK_norm_le`), uniformly in `c`: the Gaussian
range `|ε_c v| ≤ 1` and the polynomial tail beyond it are one bound, from `lobeU τ ≥ (1/2) log(1+τ²)` and the
monotonicity of `m log(1 + x/m)` in `m`.
-/

@[expose] public section

open Complex Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

lemma lobeU_ge_half_log (τ : ℝ) : (1 / 2 : ℝ) * Real.log (1 + τ ^ 2) ≤ lobeU τ := by
  unfold lobeU
  have h0 : 0 ≤ max 0 (Real.log |τ|) := le_max_left _ _
  by_cases h : |τ| ≤ 1
  · have hτ : τ ^ 2 ≤ 1 := by nlinarith [abs_nonneg τ, sq_abs τ]
    rw [min_eq_left hτ]
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + τ ^ 2)
    linarith
  · push_neg at h
    have hτ : 1 ≤ τ ^ 2 := by nlinarith [abs_nonneg τ, sq_abs τ]
    rw [min_eq_right hτ]
    have hlog : 0 < Real.log |τ| := Real.log_pos h
    rw [max_eq_right hlog.le]
    have h1 : Real.log (1 + τ ^ 2) ≤ Real.log (2 * τ ^ 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log (2 * τ ^ 2) = Real.log 2 + 2 * Real.log |τ| := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_abs]; push_cast; ring
    have h3 := Real.log_two_lt_d9
    linarith

lemma m_log_mono {m x : ℝ} (hm : 100 ≤ m) (hx : 0 ≤ x) :
    100 * Real.log (1 + x / 100) ≤ m * Real.log (1 + x / m) := by
  have hm0 : 0 < m := by linarith
  have hxm : 0 ≤ x / m := by positivity
  have hb := one_add_mul_self_le_rpow_one_add (s := x / m) (by linarith) (p := m / 100)
    (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have e : m / 100 * (x / m) = x / 100 := by field_simp
  rw [e] at hb
  have hl := Real.log_le_log (by positivity) hb
  rw [Real.log_rpow (by positivity)] at hl
  nlinarith

lemma radialEps_le_tenth {c : ℝ} (hc : 1000 ≤ c) : radialEps c ≤ 1 / 10 := by
  have hc0 : 0 < c := by linarith
  have he0 := radialEps_pos hc0
  have hcube := radialEps_cube hc0
  by_contra h; push_neg at h
  have : (1 / 10 : ℝ) ^ 3 < radialEps c ^ 3 := by gcongr
  nlinarith [pow_pos he0 3]

lemma radialK_norm_le {c s S v : ℝ} (hc : 1000 ≤ c) (hs : |s| ≤ S)
    (hS : Real.pi ^ 2 * radialEps c ^ 2 * S ≤ 1 / 2) :
    ‖radialK c (1 + (v : ℂ) * Complex.I) s‖ ≤
      4 * Real.exp (4 / 9 + Real.pi ^ 2 * S) * (1 + v ^ 2 / 100) ^ (-(300 / 56 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  set e := radialEps c with hedef
  have he0 : 0 < e := radialEps_pos hc0
  have he10 : e ≤ 1 / 10 := radialEps_le_tenth hc
  have hcube : c * e ^ 3 = 1 := radialEps_cube hc0
  have hpi := Real.pi_pos
  set ξ := radialXi c s with hξdef
  have hπξ : Real.pi ^ 2 * ξ = 1 + Real.pi ^ 2 * e ^ 2 * s := by
    simp only [hξdef, radialXi, hedef]; field_simp
  have hs' : |Real.pi ^ 2 * e ^ 2 * s| ≤ 1 / 2 := by
    rw [abs_mul]
    calc |Real.pi ^ 2 * e ^ 2| * |s| ≤ (Real.pi ^ 2 * e ^ 2) * S := by
          rw [abs_of_nonneg (by positivity)]; gcongr
      _ ≤ 1 / 2 := by nlinarith
  have hξ : 0 < ξ := by
    have : 0 < Real.pi ^ 2 * ξ := by rw [hπξ]; have := neg_abs_le (Real.pi ^ 2 * e ^ 2 * s); linarith
    exact pos_of_mul_pos_right this (by positivity)
  have hζ : (e : ℂ) * (1 + (v : ℂ) * Complex.I) = (e : ℂ) + ((e * v : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hK := norm_mellinK0_vert_le (c := c) (ξ := ξ) (s := e) (τ := e * v) hc0 hξ he0 (by linarith)
  have hKe : radialK c (1 + (v : ℂ) * Complex.I) s = mellinK0 c ((e : ℂ) + ((e * v : ℝ) : ℂ) * Complex.I) ξ := by
    show mellinK0 c ((e : ℂ) * (1 + (v : ℂ) * Complex.I)) ξ = _
    rw [hζ]
  rw [hKe]
  refine hK.trans ?_
  -- the three factors
  have hm : c * e = 1 / e ^ 2 := by field_simp; nlinarith [hcube]
  have hm100 : 100 ≤ c * e := by
    rw [hm, le_div_iff₀ (by positivity)]; nlinarith
  have hee : e ^ 2 = 1 / (c * e) := by rw [hm]; field_simp
  have P1 : 2 * Real.exp (1 / (4 * c)) ≤ 4 := by
    have : Real.exp (1 / (4 * c)) ≤ 11 / 10 := exp_le_of_small (by positivity) (by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
    linarith
  have P2 : Real.exp (c * ((4 / 9 : ℝ) * e ^ 3 + e * Real.log (Real.pi ^ 2 * ξ))) ≤
      Real.exp (4 / 9 + Real.pi ^ 2 * S) := by
    refine Real.exp_le_exp.mpr ?_
    have hlog : Real.log (Real.pi ^ 2 * ξ) ≤ Real.pi ^ 2 * e ^ 2 * s := by
      have := Real.log_le_sub_one_of_pos (by rw [hπξ]; have := neg_abs_le (Real.pi ^ 2 * e ^ 2 * s); linarith :
        0 < Real.pi ^ 2 * ξ)
      linarith [hπξ]
    have h1 : c * (e * Real.log (Real.pi ^ 2 * ξ)) ≤ c * (e * (Real.pi ^ 2 * e ^ 2 * s)) := by
      gcongr
    have h2 : c * (e * (Real.pi ^ 2 * e ^ 2 * s)) = Real.pi ^ 2 * s * (c * e ^ 3) := by ring
    rw [hcube, mul_one] at h2
    have h3 : Real.pi ^ 2 * s ≤ Real.pi ^ 2 * S := by
      have := (abs_le.mp hs).2; nlinarith
    have h4 : c * ((4 / 9 : ℝ) * e ^ 3) = 4 / 9 := by
      have : c * ((4 / 9 : ℝ) * e ^ 3) = (4 / 9) * (c * e ^ 3) := by ring
      rw [this, hcube]; ring
    nlinarith
  have P3 : Real.exp (-(c * (2 * (3 / 56 : ℝ) * e * lobeU (e * v)))) ≤
      (1 + v ^ 2 / 100) ^ (-(300 / 56 : ℝ)) := by
    have hl := lobeU_ge_half_log (e * v)
    have hmono := m_log_mono (m := c * e) (x := v ^ 2) hm100 (sq_nonneg v)
    have hev : (e * v) ^ 2 = v ^ 2 / (c * e) := by rw [mul_pow, hee]; ring
    rw [hev] at hl
    rw [Real.rpow_def_of_pos (by positivity)]
    refine Real.exp_le_exp.mpr ?_
    have : c * (2 * (3 / 56 : ℝ) * e * lobeU (e * v)) ≥
        (3 / 56 : ℝ) * (c * e * Real.log (1 + v ^ 2 / (c * e))) := by
      have : c * (2 * (3 / 56 : ℝ) * e * lobeU (e * v)) = (3 / 28 : ℝ) * (c * e) * lobeU (e * v) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ (3 / 28 : ℝ) * (c * e))
      nlinarith
    nlinarith [hmono]
  calc 2 * Real.exp (1 / (4 * c)) * Real.exp (c * ((4 / 9 : ℝ) * e ^ 3 + e * Real.log (Real.pi ^ 2 * ξ))) *
        Real.exp (-(c * (2 * (3 / 56 : ℝ) * e * lobeU (e * v))))
      ≤ 4 * Real.exp (4 / 9 + Real.pi ^ 2 * S) * (1 + v ^ 2 / 100) ^ (-(300 / 56 : ℝ)) := by
        gcongr

/-- info: 'FormalResearch.SignUncertainty.radialK_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radialK_norm_le

end FormalResearch.SignUncertainty
