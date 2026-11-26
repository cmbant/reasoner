module

public import FormalResearch.SignUncertainty.HankelPowerSeries

/-!
# The Hankel Langer chart: coefficient series (`gt:7.7b` (0))

Source: `CFT/sign_uncertainty/paper/langer_transport.tex`, Lemma 7.7b (0).  With `η_j := η_D(2j+2) ∈ (0, 1)`
(`η_0 = π²/12`) the series of `g(z) = log(tan(πz/2)/(πz/2))` and `V(z) = S̃(z) - z g(z)` are
`(12/π²) g(z) = z² (1 + ε(z²))` and `-(18/π²) V(z) = z³ E(z²)` with
`1 + ε(w) = ∑ aG_j w^j`, `E(w) = ∑ aE_j w^j`, `aG_j = (12/π²) η_j/(j+1)`, `aE_j = (36/π²) η_j/(2j+3)`.
Only the properties `0 < η_j ≤ 1`, `η_0 = π²/12` enter (`LangerEta`); the Dirichlet-eta identification is
separate.  This module proves, in the variable `w = z²`: `aG_0 = aE_0 = 1`, `0 < aG_j ≤ 6/π²`,
`0 < aE_j ≤ 36/(5π²)` for `j ≥ 1`, the norm bounds `‖ε(w)‖ ≤ ε_h`, `‖E(w) - 1‖ ≤ ε_E` on `‖w‖ ≤ q = ϱ²`,
`ϱ = 0.035`, with `ε_h ≤ 7.46·10⁻⁴`, `ε_E ≤ 8.95·10⁻⁴`, and the derivative bounds.
-/

@[expose] public section

open Complex Filter Topology Set Metric
open scoped Real

namespace FormalResearch.SignUncertainty

/-- The properties of the coefficients `η_j = η_D(2j+2)` used by the chart. -/
structure LangerEta (η : ℕ → ℝ) : Prop where
  pos : ∀ j, 0 < η j
  le_one : ∀ j, η j ≤ 1
  zero : η 0 = π ^ 2 / 12

section Coeffs

variable {η : ℕ → ℝ}

/-- Coefficients of `(12/π²) g(z)/z²` in `w = z²`. -/
noncomputable def aG (η : ℕ → ℝ) (j : ℕ) : ℝ := 12 / π ^ 2 * η j / ((j : ℝ) + 1)

/-- Coefficients of `E` in `w = z²`. -/
noncomputable def aE (η : ℕ → ℝ) (j : ℕ) : ℝ := 36 / π ^ 2 * η j / (2 * (j : ℝ) + 3)

lemma aG_zero (h : LangerEta η) : aG η 0 = 1 := by
  unfold aG; rw [h.zero]; field_simp; norm_num

lemma aE_zero (h : LangerEta η) : aE η 0 = 1 := by
  unfold aE; rw [h.zero]; field_simp; norm_num

lemma aG_pos (h : LangerEta η) (j : ℕ) : 0 < aG η j := by
  unfold aG; have := h.pos j; positivity

lemma aE_pos (h : LangerEta η) (j : ℕ) : 0 < aE η j := by
  unfold aE; have := h.pos j; positivity

lemma aG_le (h : LangerEta η) {j : ℕ} (hj : 1 ≤ j) : aG η j ≤ 6 / π ^ 2 := by
  have h1 := h.le_one j
  have hj' : (2 : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hj
  have hp : 0 < π ^ 2 := by positivity
  have hq : aG η j = (12 * η j / ((j : ℝ) + 1)) / π ^ 2 := by unfold aG; ring
  rw [hq]
  refine div_le_div_of_nonneg_right ?_ hp.le
  rw [div_le_iff₀ (by linarith)]
  linarith

lemma aE_le (h : LangerEta η) {j : ℕ} (hj : 1 ≤ j) : aE η j ≤ 36 / (5 * π ^ 2) := by
  have h1 := h.le_one j
  have hj' : (5 : ℝ) ≤ 2 * (j : ℝ) + 3 := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hp : 0 < π ^ 2 := by positivity
  have hq : aE η j = (36 * η j / (2 * (j : ℝ) + 3)) / π ^ 2 := by unfold aE; ring
  have hq2 : 36 / (5 * π ^ 2) = (36 / 5) / π ^ 2 := by field_simp
  rw [hq, hq2]
  refine div_le_div_of_nonneg_right ?_ hp.le
  rw [div_le_iff₀ (by linarith)]
  have := h.pos j
  nlinarith

lemma abs_aG_le (h : LangerEta η) {j : ℕ} (hj : 1 ≤ j) : |aG η j| ≤ 6 / π ^ 2 := by
  rw [abs_of_pos (aG_pos h j)]; exact aG_le h hj

lemma abs_aE_le (h : LangerEta η) {j : ℕ} (hj : 1 ≤ j) : |aE η j| ≤ 36 / (5 * π ^ 2) := by
  rw [abs_of_pos (aE_pos h j)]; exact aE_le h hj

lemma abs_aG_le_one (h : LangerEta η) (j : ℕ) : |aG η j| ≤ 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [aG_zero h]; simp
  · refine (abs_aG_le h hj).trans ?_
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]

lemma abs_aE_le_one (h : LangerEta η) (j : ℕ) : |aE η j| ≤ 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [aE_zero h]; simp
  · refine (abs_aE_le h hj).trans ?_
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]

/-- `1 + ε(w) = ∑ aG_j w^j`. -/
noncomputable def chartEps (η : ℕ → ℝ) (w : ℂ) : ℂ := psW (aG η) w - 1

/-- `E(w) = ∑ aE_j w^j`. -/
noncomputable def chartE (η : ℕ → ℝ) (w : ℂ) : ℂ := psW (aE η) w

lemma norm_chartEps_le (h : LangerEta η) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖chartEps η w‖ ≤ 6 / π ^ 2 * ‖w‖ / (1 - ‖w‖) := by
  have := norm_psW_sub_le (a := aG η) (B := 6 / π ^ 2) (fun j hj => abs_aG_le h hj) hw
  rw [aG_zero h] at this
  unfold chartEps; simpa using this

lemma norm_chartE_sub_one_le (h : LangerEta η) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖chartE η w - 1‖ ≤ 36 / (5 * π ^ 2) * ‖w‖ / (1 - ‖w‖) := by
  have := norm_psW_sub_le (a := aE η) (B := 36 / (5 * π ^ 2)) (fun j hj => abs_aE_le h hj) hw
  rw [aE_zero h] at this
  unfold chartE; simpa using this

lemma hasDerivAt_chartEps (h : LangerEta η) {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (chartEps η) (psWD (aG η) w) w := by
  have := hasDerivAt_psW (a := aG η) (B := 1) (abs_aG_le_one h) hw
  exact this.sub_const 1

lemma hasDerivAt_chartE (h : LangerEta η) {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (chartE η) (psWD (aE η) w) w :=
  hasDerivAt_psW (a := aE η) (B := 1) (abs_aE_le_one h) hw

lemma norm_deriv_chartEps_le (h : LangerEta η) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖psWD (aG η) w‖ ≤ 6 / π ^ 2 / (1 - ‖w‖) ^ 2 :=
  norm_psWD_le (fun _j hj => abs_aG_le h hj) hw

lemma norm_deriv_chartE_le (h : LangerEta η) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖psWD (aE η) w‖ ≤ 36 / (5 * π ^ 2) / (1 - ‖w‖) ^ 2 :=
  norm_psWD_le (fun _j hj => abs_aE_le h hj) hw

/-! ### The constants of `gt:7.7b` -/

/-- `ϱ = 0.035` and `q = ϱ²`. -/
noncomputable def chartVarrho : ℝ := 0.035

lemma chartEpsH_le : 6 / π ^ 2 * (0.035 ^ 2) / (1 - 0.035 ^ 2) ≤ 7.46e-4 := by
  have hp : (9.869 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d4]
  rw [div_le_iff₀ (by norm_num)]
  have : 6 / π ^ 2 ≤ 6 / 9.869 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  have h2 : (6 / 9.869 : ℝ) * 0.035 ^ 2 ≤ 7.46e-4 * (1 - 0.035 ^ 2) := by norm_num
  nlinarith

lemma chartEpsE_le : 36 / (5 * π ^ 2) * (0.035 ^ 2) / (1 - 0.035 ^ 2) ≤ 8.95e-4 := by
  have hp : (9.869 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d4]
  rw [div_le_iff₀ (by norm_num)]
  have : 36 / (5 * π ^ 2) ≤ 36 / (5 * 9.869) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h2 : (36 / (5 * 9.869) : ℝ) * 0.035 ^ 2 ≤ 8.95e-4 * (1 - 0.035 ^ 2) := by norm_num
  nlinarith

end Coeffs

/-- info: 'FormalResearch.SignUncertainty.norm_chartEps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_chartEps_le

/-- info: 'FormalResearch.SignUncertainty.norm_chartE_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_chartE_sub_one_le

end FormalResearch.SignUncertainty
