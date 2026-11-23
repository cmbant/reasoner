module

public import Mathlib

/-!
# Bounded-coefficient power series in the unit disc

The Langer chart of `gt:7.7b` (`CFT/sign_uncertainty/paper/langer_transport.tex`) is built from the even power
series `g(z) = ∑ η_{2j+2}/(j+1) z^{2j+2}` with coefficients in `(0, 1]`.  Writing `w = z²` the pieces are
power series `psW a w = ∑ a_j w^j` with bounded real coefficients on `‖w‖ < 1`.  This module records the generic
facts used there: the norm bounds `‖psW a w - a₀‖ ≤ B r/(1-r)`, differentiability, and the derivative bound
`‖psWD a w‖ ≤ B/(1-r)²` (`r = ‖w‖`).
-/

@[expose] public section

open Complex Filter Topology Set Metric

namespace FormalResearch.SignUncertainty

/-- The power series `∑_j a_j w^j` with real coefficients, as a function of a complex `w`. -/
noncomputable def psW (a : ℕ → ℝ) (w : ℂ) : ℂ := ∑' j : ℕ, (a j : ℂ) * w ^ j

/-- Its derivative series `∑_j (j+1) a_{j+1} w^j`. -/
noncomputable def psWD (a : ℕ → ℝ) (w : ℂ) : ℂ :=
  ∑' j : ℕ, (a (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ) * w ^ j

section Bounds

variable {a : ℕ → ℝ} {B : ℝ}

lemma summable_psW {w : ℂ} (ha : ∀ j, |a j| ≤ B) (hw : ‖w‖ < 1) :
    Summable (fun j : ℕ => ‖(a j : ℂ) * w ^ j‖) := by
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg w) hw).mul_left B)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (ha j) (by positivity)

lemma norm_psW_sub_le {w : ℂ} (ha : ∀ j, 1 ≤ j → |a j| ≤ B) (hw : ‖w‖ < 1) :
    ‖psW a w - a 0‖ ≤ B * ‖w‖ / (1 - ‖w‖) := by
  set r := ‖w‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg w
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (ha 1 le_rfl)
  have hbd : ∀ j : ℕ, ‖(a (j + 1) : ℂ) * w ^ (j + 1)‖ ≤ B * r * r ^ j := by
    intro j
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, pow_succ]
    calc |a (j + 1)| * (r ^ j * r) ≤ B * (r ^ j * r) :=
          mul_le_mul_of_nonneg_right (ha (j + 1) (by omega)) (by positivity)
      _ = B * r * r ^ j := by ring
  have hs : Summable (fun j : ℕ => (a (j + 1) : ℂ) * w ^ (j + 1)) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hw).mul_left (B * r)) hbd
  have hs0 : Summable (fun j : ℕ => (a j : ℂ) * w ^ j) := by
    rw [← summable_nat_add_iff 1]; exact hs
  have heq : psW a w - a 0 = ∑' j : ℕ, (a (j + 1) : ℂ) * w ^ (j + 1) := by
    unfold psW
    rw [hs0.tsum_eq_zero_add]; simp
  rw [heq]
  calc ‖∑' j : ℕ, (a (j + 1) : ℂ) * w ^ (j + 1)‖
      ≤ ∑' j : ℕ, B * r * r ^ j :=
        (norm_tsum_le_tsum_norm hs.norm).trans
          (Summable.tsum_le_tsum hbd hs.norm ((summable_geometric_of_lt_one hr0 hw).mul_left (B * r)))
    _ = B * r / (1 - r) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hw]; field_simp


lemma summable_deriv_majorant {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (B : ℝ) :
    Summable (fun j : ℕ => B * ((j : ℝ) * ρ ^ (j - 1))) := by
  rw [← summable_nat_add_iff 1]
  have h1 : Summable (fun j : ℕ => ((j : ℝ) * ρ ^ j)) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := ρ) (by rwa [Real.norm_eq_abs, abs_of_nonneg hρ0])
  have h2 : Summable (fun j : ℕ => ρ ^ j) := summable_geometric_of_lt_one hρ0 hρ
  have := (h1.add h2).mul_left B
  refine this.congr (fun j => ?_)
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  ring

lemma hasDerivAt_psW (ha : ∀ j, |a j| ≤ B) {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (psW a) (psWD a w) w := by
  obtain ⟨ρ, hwρ, hρ1⟩ := exists_between hw
  have hρ0 : 0 ≤ ρ := (norm_nonneg w).trans hwρ.le
  have hu := summable_deriv_majorant hρ0 hρ1 B
  have hg : ∀ (j : ℕ) (y : ℂ), y ∈ ball (0 : ℂ) ρ →
      HasDerivAt (fun y : ℂ => (a j : ℂ) * y ^ j) ((a j : ℂ) * ((j : ℂ) * y ^ (j - 1))) y :=
    fun j y _ => (hasDerivAt_pow j y).const_mul _
  have hg' : ∀ (j : ℕ) (y : ℂ), y ∈ ball (0 : ℂ) ρ →
      ‖(a j : ℂ) * ((j : ℂ) * y ^ (j - 1))‖ ≤ B * ((j : ℝ) * ρ ^ (j - 1)) := by
    intro j y hy
    have hyρ : ‖y‖ ≤ ρ := by simpa using (mem_ball_zero_iff.1 hy).le
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
    have h1 : ‖y‖ ^ (j - 1) ≤ ρ ^ (j - 1) := pow_le_pow_left₀ (norm_nonneg y) hyρ _
    have h2 : (j : ℝ) * ‖y‖ ^ (j - 1) ≤ (j : ℝ) * ρ ^ (j - 1) :=
      mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg j)
    exact mul_le_mul (ha j) h2 (by positivity) ((abs_nonneg _).trans (ha j))
  have hs0 : Summable (fun j : ℕ => (a j : ℂ) * (0 : ℂ) ^ j) := by
    refine summable_of_ne_finset_zero (s := {0}) (fun j hj => ?_)
    have : j ≠ 0 := by simpa using hj
    simp [this]
  have hD := hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball (0 : ℂ) ρ).isPreconnected
    hg hg' (mem_ball_self (by linarith [norm_nonneg w] : (0 : ℝ) < ρ)) hs0
    (mem_ball_zero_iff.2 hwρ)
  have hsum : Summable (fun j : ℕ => (a j : ℂ) * ((j : ℂ) * w ^ (j - 1))) :=
    Summable.of_norm_bounded hu (fun j => hg' j w (mem_ball_zero_iff.2 hwρ))
  have heq : (∑' j : ℕ, (a j : ℂ) * ((j : ℂ) * w ^ (j - 1))) = psWD a w := by
    rw [hsum.tsum_eq_zero_add]
    simp only [psWD, Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel]
    refine tsum_congr (fun j => ?_)
    push_cast; ring
  unfold psW
  rw [← heq]
  exact hD

lemma norm_psWD_le (ha : ∀ j, 1 ≤ j → |a j| ≤ B) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖psWD a w‖ ≤ B / (1 - ‖w‖) ^ 2 := by
  set r := ‖w‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg w
  have hbd : ∀ j : ℕ, ‖(a (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ) * w ^ j‖ ≤ B * (((j : ℝ) + 1) * r ^ j) := by
    intro j
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
    push_cast
    calc |a (j + 1)| * ((j : ℝ) + 1) * r ^ j = |a (j + 1)| * (((j : ℝ) + 1) * r ^ j) := by ring
      _ ≤ B * (((j : ℝ) + 1) * r ^ j) :=
          mul_le_mul_of_nonneg_right (ha _ (by omega)) (by positivity)
  have hsum : HasSum (fun j : ℕ => ((j : ℝ) + 1) * r ^ j) ((1 - r) ^ 2)⁻¹ := by
    have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := r)
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
    have h2 := hasSum_geometric_of_lt_one hr0 hw
    have := h1.add h2
    convert this using 1
    · ext j; ring
    · have : (1 - r) ≠ 0 := by linarith
      field_simp; ring
  have hs : Summable (fun j : ℕ => ‖(a (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ) * w ^ j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hbd (hsum.summable.mul_left B)
  unfold psWD
  calc ‖∑' j : ℕ, (a (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ) * w ^ j‖
      ≤ ∑' j : ℕ, ‖(a (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ) * w ^ j‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ, B * (((j : ℝ) + 1) * r ^ j) := Summable.tsum_le_tsum hbd hs (hsum.summable.mul_left B)
    _ = B / (1 - r) ^ 2 := by rw [tsum_mul_left, hsum.tsum_eq]; ring

end Bounds

/-- info: 'FormalResearch.SignUncertainty.norm_psW_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_psW_sub_le

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_psW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_psW

/-- info: 'FormalResearch.SignUncertainty.norm_psWD_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_psWD_le

end FormalResearch.SignUncertainty
