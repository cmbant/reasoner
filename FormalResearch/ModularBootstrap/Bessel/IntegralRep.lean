module

public import FormalResearch.ModularBootstrap.Bessel.Defs
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Integral representation of `I₀` and `I₁`, and consequences

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma B (`vlo:Bessel`), proof of (c)
and (d): the classical representation `I₀(z) = π⁻¹ ∫₀^π e^{z cos θ} dθ`, proved here from the power
series by Wallis' cosine moments and termwise integration, and likewise
`(z/2) S₁(z²/4) = I₁(z) = π⁻¹ ∫₀^π e^{z cos θ} cos θ dθ`.

Consequences used by the paper: `I₀(z) ≤ e^z` (`besselI0_le_exp`), `I₁ ≤ I₀` (`besselI1_le_besselI0`),
`e^{-z} I₀(z)` is nonincreasing (equivalently `(log I₀)' ≤ 1`; `besselI0_le_mul_exp`),
and `I₂ ≥ I₀/2` for `z ≥ 4` (`besselI2_ge_half`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Finset intervalIntegral
open scoped Nat

namespace FormalResearch.ModularBootstrap.Bessel

/-- Normalised cosine moments `π⁻¹ ∫₀^π cos^n θ dθ`. -/
noncomputable def cosMoment (n : ℕ) : ℝ := (∫ x in (0 : ℝ)..π, cos x ^ n) / π

lemma cosMoment_zero : cosMoment 0 = 1 := by
  simp [cosMoment, pi_ne_zero]

lemma cosMoment_one : cosMoment 1 = 0 := by
  simp [cosMoment]

lemma cosMoment_add_two (n : ℕ) :
    cosMoment (n + 2) = ((n : ℝ) + 1) / ((n : ℝ) + 2) * cosMoment n := by
  unfold cosMoment
  rw [integral_cos_pow]
  simp [mul_div_assoc]

lemma cosMoment_odd (k : ℕ) : cosMoment (2 * k + 1) = 0 := by
  induction k with
  | zero => simpa using cosMoment_one
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, cosMoment_add_two, ih, mul_zero]

lemma cosMoment_even (k : ℕ) :
    cosMoment (2 * k) = ((2 * k)! : ℝ) / (4 ^ k * ((k ! : ℝ)) ^ 2) := by
  induction k with
  | zero => simp [cosMoment_zero]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, cosMoment_add_two, ih]
    have h1 : ((2 * (k + 1))! : ℝ) = (2 * k + 2) * (2 * k + 1) * ((2 * k)! : ℝ) := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [show 2 * k + 2 = 2 * (k + 1) by ring, h1, Nat.factorial_succ]
    push_cast
    have : (k ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have h2 : ((2 * k)! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
    ring

/-- Termwise-integrated exponential series: `Σ_n z^n/n! · c_{n+m} = π⁻¹ ∫ e^{z cos θ} cos^m θ`. -/
lemma hasSum_cosMoment (z : ℝ) (m : ℕ) :
    HasSum (fun n : ℕ => z ^ n / (n ! : ℝ) * cosMoment (n + m))
      ((∫ θ in (0 : ℝ)..π, exp (z * cos θ) * cos θ ^ m) / π) := by
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := π)
    (F := fun (n : ℕ) (θ : ℝ) => (z * cos θ) ^ n / (n ! : ℝ) * cos θ ^ m)
    (f := fun θ => exp (z * cos θ) * cos θ ^ m)
    (fun n θ => |z| ^ n / (n ! : ℝ))
    (fun n => by fun_prop)
    (fun n => Filter.Eventually.of_forall fun θ _ => by
      have hc : |cos θ| ≤ 1 := abs_cos_le_one θ
      have hnorm : ‖(z * cos θ) ^ n / (n ! : ℝ) * cos θ ^ m‖
          = (|z| ^ n / (n ! : ℝ)) * (|cos θ| ^ n * |cos θ| ^ m) := by
        rw [Real.norm_eq_abs]
        simp only [abs_mul, abs_pow, abs_div, Nat.abs_cast]
        ring
      rw [hnorm]
      have h3 : 0 ≤ |z| ^ n / (n ! : ℝ) := by positivity
      have h1 : |cos θ| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
      have h2 : |cos θ| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
      calc (|z| ^ n / (n ! : ℝ)) * (|cos θ| ^ n * |cos θ| ^ m)
          ≤ (|z| ^ n / (n ! : ℝ)) * 1 := by
            gcongr
            calc |cos θ| ^ n * |cos θ| ^ m ≤ 1 * 1 := by gcongr
              _ = 1 := by norm_num
        _ = _ := by ring)
    (Filter.Eventually.of_forall fun θ _ => Real.summable_pow_div_factorial |z|)
    (by simp)
    (Filter.Eventually.of_forall fun θ _ => by
      have h := (NormedSpace.expSeries_div_hasSum_exp (z * cos θ)).mul_right (cos θ ^ m)
      rw [← Real.exp_eq_exp_ℝ] at h
      exact h)
  have key2 := key.div_const π
  convert key2 using 1
  ext n
  have hint : ∫ θ in (0 : ℝ)..π, (z * cos θ) ^ n / (n ! : ℝ) * cos θ ^ m
      = z ^ n / (n ! : ℝ) * ∫ θ in (0 : ℝ)..π, cos θ ^ (n + m) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext θ
    rw [mul_pow, pow_add]; ring
  rw [hint]
  unfold cosMoment
  ring

/-- Reindexing of a series supported on even indices. -/
lemma hasSum_even_of_hasSum {f : ℕ → ℝ} {a : ℝ} (h : HasSum f a) (hodd : ∀ k, f (2 * k + 1) = 0) :
    HasSum (fun k => f (2 * k)) a := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simp only at h; omega
  show HasSum (f ∘ fun k : ℕ => 2 * k) a
  rw [hinj.hasSum_iff]
  · exact h
  · intro n hn
    have : n % 2 = 1 := by
      by_contra h2
      exact hn ⟨n / 2, by simp; omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    exact hodd k

/-- Reindexing of a series supported on odd indices. -/
lemma hasSum_odd_of_hasSum {f : ℕ → ℝ} {a : ℝ} (h : HasSum f a) (heven : ∀ k, f (2 * k) = 0) :
    HasSum (fun k => f (2 * k + 1)) a := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by simp only at h; omega
  show HasSum (f ∘ fun k : ℕ => 2 * k + 1) a
  rw [hinj.hasSum_iff]
  · exact h
  · intro n hn
    have : n % 2 = 0 := by
      by_contra h2
      exact hn ⟨n / 2, by simp; omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    exact heven k

/-- **Integral representation of `I₀`** (`vlo:Bessel`, proof of (c)):
`I₀(z) = π⁻¹ ∫₀^π e^{z cos θ} dθ`. -/
theorem besselI0_integral (z : ℝ) :
    besselI0 z = (∫ θ in (0 : ℝ)..π, exp (z * cos θ)) / π := by
  have h := hasSum_cosMoment z 0
  simp only [add_zero, pow_zero, mul_one] at h
  have h2 := hasSum_even_of_hasSum h (fun k => by simp [cosMoment_odd])
  have h3 : HasSum (besselTerm 0 (z ^ 2 / 4)) ((∫ θ in (0 : ℝ)..π, exp (z * cos θ)) / π) := by
    convert h2 using 1
    ext k
    simp only [cosMoment_even]
    unfold besselTerm
    have : (k ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have h2 : ((2 * k)! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [show (k + 0)! = k ! from rfl, div_pow, ← pow_mul]
    field_simp
  rw [besselI0_eq]
  exact h3.tsum_eq

/-- **Integral representation of `I₁`**: `I₁(z) = π⁻¹ ∫₀^π e^{z cos θ} cos θ dθ`. -/
theorem besselI1_integral (z : ℝ) :
    besselI 1 z = (∫ θ in (0 : ℝ)..π, exp (z * cos θ) * cos θ) / π := by
  have h := hasSum_cosMoment z 1
  simp only [pow_one] at h
  have h2 := hasSum_odd_of_hasSum h (fun k => by
    simp [cosMoment_odd])
  have h3 : HasSum (fun k => (z / 2) * besselTerm 1 (z ^ 2 / 4) k)
      ((∫ θ in (0 : ℝ)..π, exp (z * cos θ) * cos θ) / π) := by
    convert h2 using 1
    ext k
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, cosMoment_even]
    unfold besselTerm
    have : (k ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have h2 : ((2 * k + 1)! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h4 : ((2 * (k + 1))! : ℝ) = (2 * k + 2) * ((2 * k + 1)! : ℝ) := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
    rw [h4, Nat.factorial_succ k, div_pow, ← pow_mul]
    push_cast
    field_simp
    ring
  unfold besselI
  rw [pow_one, ← h3.tsum_eq, tsum_mul_left]
  rfl

/-- `I₀(z) ≤ e^z` for `z ≥ 0` (`vlo:Bessel`, proof of (d)). -/
theorem besselI0_le_exp {z : ℝ} (hz : 0 ≤ z) : besselI0 z ≤ exp z := by
  rw [besselI0_integral, div_le_iff₀ pi_pos]
  calc ∫ θ in (0 : ℝ)..π, exp (z * cos θ) ≤ ∫ θ in (0 : ℝ)..π, exp z := by
        refine intervalIntegral.integral_mono_on pi_pos.le ?_ ?_ fun θ _ => ?_
        · exact (by fun_prop : Continuous fun θ : ℝ => exp (z * cos θ)).intervalIntegrable _ _
        · exact intervalIntegrable_const
        · exact exp_le_exp.mpr (by nlinarith [cos_le_one θ])
    _ = exp z * π := by simp [mul_comm]

/-- `I₁(z) ≤ I₀(z)` (`vlo:Bessel`, proof of (d)). -/
theorem besselI1_le_besselI0 (z : ℝ) : besselI 1 z ≤ besselI0 z := by
  rw [besselI1_integral, besselI0_integral]
  gcongr 1
  refine intervalIntegral.integral_mono_on pi_pos.le ?_ ?_ fun θ _ => ?_
  · exact (by fun_prop : Continuous fun θ : ℝ => exp (z * cos θ) * cos θ).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun θ : ℝ => exp (z * cos θ)).intervalIntegrable _ _
  · nlinarith [cos_le_one θ, exp_pos (z * cos θ)]

/-- `e^{-z} I₀(z) = π⁻¹ ∫₀^π e^{-z(1 - cos θ)} dθ`. -/
lemma exp_neg_mul_besselI0 (z : ℝ) :
    exp (-z) * besselI0 z = (∫ θ in (0 : ℝ)..π, exp (-(z * (1 - cos θ)))) / π := by
  rw [besselI0_integral, mul_div_assoc', ← intervalIntegral.integral_const_mul]
  congr 2; ext θ
  rw [← exp_add]; congr 1; ring

/-- `e^{-z} I₀(z)` is nonincreasing (equivalently `(log I₀)' ≤ 1`). -/
theorem exp_neg_mul_besselI0_antitone {z w : ℝ} (hzw : z ≤ w) :
    exp (-w) * besselI0 w ≤ exp (-z) * besselI0 z := by
  rw [exp_neg_mul_besselI0, exp_neg_mul_besselI0]
  gcongr 1
  refine intervalIntegral.integral_mono_on pi_pos.le ?_ ?_ fun θ _ => ?_
  · exact (by fun_prop : Continuous fun θ : ℝ => exp (-(w * (1 - cos θ)))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun θ : ℝ => exp (-(z * (1 - cos θ)))).intervalIntegrable _ _
  · exact exp_le_exp.mpr (by nlinarith [cos_le_one θ])

/-- `I₀(w) ≤ e^{w - z} I₀(z)` for `z ≤ w`: the consequence of `(log I₀)' = I₁/I₀ ≤ 1` used in
`vlo:Bessel` (d). -/
theorem besselI0_le_mul_exp {z w : ℝ} (hzw : z ≤ w) :
    besselI0 w ≤ exp (w - z) * besselI0 z := by
  have h := exp_neg_mul_besselI0_antitone hzw
  have h2 := mul_le_mul_of_nonneg_left h (exp_pos w).le
  rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul] at h2
  calc besselI0 w ≤ exp w * (exp (-z) * besselI0 z) := h2
    _ = exp (w - z) * besselI0 z := by rw [← mul_assoc, ← exp_add]; ring_nf

/-- `I₂(z) = I₀(z) - 2 I₁(z) / z` for `z > 0`. -/
theorem besselI2_eq {z : ℝ} (hz : 0 < z) : besselI 2 z = besselI0 z - 2 / z * besselI 1 z := by
  have h := besselS_recurrence (y := z ^ 2 / 4) (by positivity)
  unfold besselI
  have : (z / 2) ^ 2 = z ^ 2 / 4 := by ring
  rw [this, h, besselI0_eq]
  simp only [pow_one]
  field_simp

/-- For `z ≥ 4`, `I₂(z) ≥ I₀(z)/2` (uses `0 ≤ I₁ ≤ I₀`; `vlo:Bessel` (d)). -/
theorem besselI2_ge_half {z : ℝ} (hz : 4 ≤ z) : besselI0 z / 2 ≤ besselI 2 z := by
  have hz0 : 0 < z := by linarith
  rw [besselI2_eq hz0]
  have h1 := besselI1_le_besselI0 z
  have h2 : 2 / z ≤ 1 / 2 := by rw [div_le_div_iff₀ hz0 (by norm_num)]; linarith
  have h3 : 0 ≤ besselI 1 z := besselI_nonneg 1 hz0.le
  have h4 : 0 ≤ besselI0 z := besselI_nonneg 0 hz0.le
  nlinarith [mul_le_mul h2 h1 h3 (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselI0_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselI0_integral

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselI1_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselI1_integral

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselI0_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselI0_le_exp

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselI1_le_besselI0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselI1_le_besselI0

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselI0_le_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselI0_le_mul_exp

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselI2_ge_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselI2_ge_half

end FormalResearch.ModularBootstrap.Bessel
