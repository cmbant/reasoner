import Mathlib

/-!
# Exact arithmetic of paper P's corollaries

Pure real arithmetic on values proved elsewhere (the inputs are the closed forms `F_K`, `F_C`,
`ξ_inv` stated in the paper, not derived here):
the eight-qubit and extensive reversals (`cor:calgeom-spin1extensive`), the universal four-qubit
bound (`cor:fourdecoh`), the marginal region of `conj:maxchiral`, and the exact success probabilities
of the three- and four-copy tests (Section 6).
-/

open Real

namespace FormalResearch.FrameFree

/-! ### Eight-qubit reversal, `cor:calgeom-spin1extensive` (b) -/

/-- Chiral distance of `M₄ ⊗ ψ_{U_θ}`: `F_K = (4/9)(1+s)/2`. -/
noncomputable def CK8 (s : ℝ) : ℝ := -log (4 / 9 * ((1 + s) / 2))

/-- Exponent of `M₄ ⊗ ψ_{U_θ}`: `F_C = (1/2)(1+s)/2`, `ξ = -log F_C`. -/
noncomputable def xi8 (s : ℝ) : ℝ := -log (1 / 2 * ((1 + s) / 2))

theorem CK8_eq (s : ℝ) (hs : 0 ≤ s) : CK8 s = log (9 / (2 * (1 + s))) := by
  unfold CK8
  rw [← log_inv]
  congr 1
  field_simp
  norm_num

theorem xi8_eq (s : ℝ) (hs : 0 ≤ s) : xi8 s = log (4 / (1 + s)) := by
  unfold xi8
  rw [← log_inv]
  congr 1
  field_simp
  norm_num

/-- `C_K(Ψ) > log 4 = C_K(Φ)` iff `s < 1/8`. -/
theorem CK8_gt_iff (s : ℝ) (hs : 0 ≤ s) : log 4 < CK8 s ↔ s < 1 / 8 := by
  rw [CK8_eq s hs]
  have h1 : 0 < 1 + s := by linarith
  rw [Real.log_lt_log_iff (by norm_num) (by positivity), lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

/-- `ξ(Ψ) < log 4 = ξ(Φ)` iff `s > 0`. -/
theorem xi8_lt_iff (s : ℝ) (hs : 0 ≤ s) : xi8 s < log 4 ↔ 0 < s := by
  rw [xi8_eq s hs]
  have h1 : 0 < 1 + s := by linarith
  rw [Real.log_lt_log_iff (by positivity) (by norm_num), div_lt_iff₀ h1]
  constructor <;> intro h <;> linarith

/-- The chiral advantage `log(9/(8(1+s)))` and the operational deficit `log(1+s)` add to `log(9/8)`. -/
theorem advantage_deficit (s : ℝ) (hs : 0 ≤ s) :
    (CK8 s - log 4) + (log 4 - xi8 s) = log (9 / 8) := by
  rw [CK8_eq s hs, xi8_eq s hs]
  have h1 : 0 < 1 + s := by linarith
  have : log (9 / (2 * (1 + s))) - log (4 / (1 + s)) = log (9 / 8) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp; norm_num
  linarith

theorem advantage_eq (s : ℝ) (hs : 0 ≤ s) : CK8 s - log 4 = log (9 / (8 * (1 + s))) := by
  rw [CK8_eq s hs, ← Real.log_div (by positivity) (by norm_num)]
  have h1 : 0 < 1 + s := by linarith
  congr 1; field_simp; norm_num

theorem deficit_eq (s : ℝ) (hs : 0 ≤ s) : log 4 - xi8 s = log (1 + s) := by
  have h1 : 0 < 1 + s := by linarith
  rw [xi8_eq s hs, ← Real.log_div (by norm_num) (by positivity)]
  congr 1; field_simp

/-! ### Extensive blocks of four, `cor:calgeom-spin1extensive` (a) -/

/-- `C_K(M₄^{⊗m}) - ξ(M₄^{⊗m}) = m(log(9/4) - log 2) = m log(9/8)`. -/
theorem blocks_of_four (m : ℕ) : m * log (9 / 4) - m * log 2 = m * log (9 / 8) := by
  have : log (9 / 4) - log 2 = log (9 / 8) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [← mul_sub, this]

/-! ### Universal four-qubit bound, `cor:fourdecoh` -/

/-- `max(1-p, φp) ≥ φ/(1+φ)`, hence `e^{-ξ} ≥ φ/(1+φ)`. -/
theorem max_branch_bound (φ p : ℝ) (hφ : 0 < φ) :
    φ / (1 + φ) ≤ max (1 - p) (φ * p) := by
  by_contra h
  push Not at h
  have h1 := lt_of_le_of_lt (le_max_left _ _) h
  have h2 := lt_of_le_of_lt (le_max_right _ _) h
  have hp : 0 < 1 + φ := by linarith
  rw [lt_div_iff₀ hp] at h1 h2
  nlinarith

theorem one_add_inv_floor : 1 + 1 / (169 / 196 : ℝ) = 365 / 169 := by norm_num

/-- With the analytic three-qubit floor `169/196`, `ξ ≤ log(365/169)`. -/
theorem universal_bound_value : (169 / 196 : ℝ) / (1 + 169 / 196) = 169 / 365 := by norm_num

/-- `φ p ≥ 1/2` as soon as `p ≥ 98/169` (the open region of `conj:expceiling` begins below this). -/
theorem ceiling_region (p : ℝ) (hp : 98 / 169 ≤ p) : 1 / 2 ≤ 169 / 196 * p := by linarith

/-- `p² · 169/196 > 4/9` iff `p > 28/39` (marginal region of `conj:maxchiral`). -/
theorem marginal_region (p : ℝ) (hp : 0 ≤ p) : 4 / 9 < p ^ 2 * (169 / 196) ↔ 28 / 39 < p := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    nlinarith

/-! ### Success probabilities, Section 6 -/

/-- Native three-copy test: `1/2 + 3/128`. -/
theorem native_three : (1 : ℝ) / 2 + 3 / 128 = 67 / 128 := by norm_num

/-- `1/128` below the optimum `17/32`. -/
theorem native_three_gap : (17 : ℝ) / 32 - 67 / 128 = 1 / 128 := by norm_num

/-- Three-copy law at the probe: `P_e(3) = 1/2 - (2/3)·(3/64) = 15/32`, success `17/32`. -/
theorem probe_three : 1 - ((1 : ℝ) / 2 - 2 / 3 * (3 / 64)) = 17 / 32 := by norm_num

/-- `M₄` at three copies: `‖t‖ = 3·(√3/72)²`-norm gives `P_e(3) = 17/36`. -/
theorem m4_three (t : ℝ) (ht : t ^ 2 = 3 * (Real.sqrt 3 / 72) ^ 2) (h0 : 0 ≤ t) :
    (1 : ℝ) / 2 - 2 / 3 * t = 17 / 36 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have : t ^ 2 = (1 / 24) ^ 2 := by rw [ht]; nlinarith
  have : t = 1 / 24 := by nlinarith [sq_nonneg (t - 1 / 24), sq_nonneg (t + 1 / 24)]
  rw [this]; norm_num

/-- Four-copy optimum `(287 + 12√3)/512 = 1/2 + (31 + 12√3)/512`. -/
theorem four_copy_optimum :
    (1 : ℝ) / 2 + (1 / 4) * ((31 + 12 * Real.sqrt 3) / 128) = (287 + 12 * Real.sqrt 3) / 512 := by ring

/-- Table of `tab:fewcopy`: increasing success probabilities. -/
theorem fewcopy_order :
    (67 : ℝ) / 128 < 17 / 32 ∧ (17 : ℝ) / 32 < 137 / 256 ∧
      (137 : ℝ) / 256 < 1095 / 2048 + Real.sqrt 3 / 32 ∧
      1095 / 2048 + Real.sqrt 3 / 32 < (287 + 12 * Real.sqrt 3) / 512 := by
  have h3 : (1.732 : ℝ) < Real.sqrt 3 := by
    rw [show (1.732 : ℝ) = Real.sqrt (1.732 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h4 : Real.sqrt 3 < 1.7321 := by
    rw [show (1.7321 : ℝ) = Real.sqrt (1.7321 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨by norm_num, by norm_num, by linarith, by linarith⟩

/-! ### Odd-signal values of the code state, `thm:codechirality` -/

/-- The seed `r = (2√3/5, 2√3/5, 1/5)` is a unit Bloch vector and `3xyz/32 = 9/1000`. -/
theorem code_seed :
    (2 * Real.sqrt 3 / 5) ^ 2 + (2 * Real.sqrt 3 / 5) ^ 2 + (1 / 5 : ℝ) ^ 2 = 1 ∧
      3 * (2 * Real.sqrt 3 / 5) * (2 * Real.sqrt 3 / 5) * (1 / 5) / 32 = 9 / 1000 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor <;> nlinarith [h3]

end FormalResearch.FrameFree
