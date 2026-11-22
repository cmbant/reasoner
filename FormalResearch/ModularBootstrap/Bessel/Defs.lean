module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Modified Bessel functions `I₀, I₁, I₂` by power series

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma B (`vlo:Bessel`).

Mathlib has no modified Bessel functions, so they are defined here by their power series
`I_m(z) = (z/2)^m Σ_k (z²/4)^k / (k! (k+m)!)` (`besselI m z`, built from `besselS m y`).  This file
only has the algebra of the series: summability, nonnegativity, monotonicity, and the termwise
identity `y S₂(y) = S₀(y) - S₁(y)` (i.e. `I₂ = I₀ - 2 I₁ / z`).  The integral representation is in
`Bessel.IntegralRep`.
-/

@[expose] public section

open Filter Topology Finset
open scoped Nat

namespace FormalResearch.ModularBootstrap.Bessel

/-- General term of the Bessel series: `y^k / (k! (k+m)!)`. -/
noncomputable def besselTerm (m : ℕ) (y : ℝ) (k : ℕ) : ℝ := y ^ k / ((k ! : ℝ) * ((k + m)! : ℝ))

/-- `S_m(y) = Σ_k y^k / (k! (k+m)!)`, so that `I_m(z) = (z/2)^m S_m(z²/4)`. -/
noncomputable def besselS (m : ℕ) (y : ℝ) : ℝ := ∑' k, besselTerm m y k

/-- Modified Bessel function of the first kind and integer order `m`, by its power series
`I_m(z) = Σ_k (z/2)^{2k+m} / (k! (k+m)!)`. -/
noncomputable def besselI (m : ℕ) (z : ℝ) : ℝ := (z / 2) ^ m * besselS m (z ^ 2 / 4)

/-- `I₀(z) = Σ_k (z²/4)^k / (k!)²`. -/
noncomputable abbrev besselI0 (z : ℝ) : ℝ := besselI 0 z

lemma besselTerm_nonneg {m : ℕ} {y : ℝ} (hy : 0 ≤ y) (k : ℕ) : 0 ≤ besselTerm m y k := by
  unfold besselTerm; positivity

lemma besselTerm_le_exp {m : ℕ} {y : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    besselTerm m y k ≤ y ^ k / (k ! : ℝ) := by
  unfold besselTerm
  have h1 : (1 : ℝ) ≤ ((k + m)! : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hk : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_div_iff₀ (by positivity) hk]
  have : 0 ≤ y ^ k * (k ! : ℝ) := by positivity
  nlinarith

lemma summable_besselTerm (m : ℕ) {y : ℝ} (hy : 0 ≤ y) : Summable (besselTerm m y) :=
  Summable.of_nonneg_of_le (besselTerm_nonneg hy) (besselTerm_le_exp hy)
    (Real.summable_pow_div_factorial y)

lemma besselS_hasSum (m : ℕ) {y : ℝ} (hy : 0 ≤ y) : HasSum (besselTerm m y) (besselS m y) :=
  (summable_besselTerm m hy).hasSum

lemma besselS_nonneg (m : ℕ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ besselS m y :=
  tsum_nonneg (besselTerm_nonneg hy)

lemma besselTerm_le_besselS (m : ℕ) {y : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    besselTerm m y k ≤ besselS m y :=
  (summable_besselTerm m hy).le_tsum k fun j _ => besselTerm_nonneg hy j

lemma besselS_mono (m : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : besselS m x ≤ besselS m y := by
  refine hasSum_le (fun k => ?_) (besselS_hasSum m hx) (besselS_hasSum m (hx.trans hxy))
  unfold besselTerm
  gcongr

lemma besselS_zero_arg (m : ℕ) : besselS m 0 = 1 / (m ! : ℝ) := by
  have h : HasSum (besselTerm m 0) (1 / (m ! : ℝ)) := by
    convert hasSum_ite_eq 0 (1 / (m ! : ℝ)) using 1
    ext k
    rcases k with _ | k
    · simp [besselTerm]
    · simp [besselTerm]
  exact h.tsum_eq

lemma one_le_besselS_zero {y : ℝ} (hy : 0 ≤ y) : 1 ≤ besselS 0 y := by
  have := besselS_mono 0 le_rfl hy
  rw [besselS_zero_arg] at this
  simpa using this

lemma besselI_nonneg (m : ℕ) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ besselI m z := by
  unfold besselI
  have := besselS_nonneg m (y := z ^ 2 / 4) (by positivity)
  positivity

lemma besselI0_eq (z : ℝ) : besselI0 z = besselS 0 (z ^ 2 / 4) := by simp [besselI]

lemma one_le_besselI0 (z : ℝ) : 1 ≤ besselI0 z := by
  rw [besselI0_eq]; exact one_le_besselS_zero (by positivity)

lemma besselI0_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : besselI0 x ≤ besselI0 y := by
  rw [besselI0_eq, besselI0_eq]
  exact besselS_mono 0 (by positivity) (by gcongr)

/-- The leading term of `I₂`: `I₂(z) ≥ z²/8`. -/
lemma besselI2_ge (z : ℝ) : z ^ 2 / 8 ≤ besselI 2 z := by
  unfold besselI
  have h := besselTerm_le_besselS 2 (y := z ^ 2 / 4) (by positivity) 0
  have h0 : besselTerm 2 (z ^ 2 / 4) 0 = 1 / 2 := by simp [besselTerm]
  rw [h0] at h
  have : (z / 2) ^ 2 = z ^ 2 / 4 := by ring
  rw [this]
  nlinarith [sq_nonneg z]

/-- Termwise recurrence `y · S₂(y) = S₀(y) - S₁(y)` (that is, `I₂ = I₀ - 2 I₁ / z`). -/
lemma besselS_recurrence {y : ℝ} (hy : 0 ≤ y) :
    y * besselS 2 y = besselS 0 y - besselS 1 y := by
  have h0 := besselS_hasSum 0 hy
  have h1 := besselS_hasSum 1 hy
  have hd := h0.sub h1
  -- `f k = S₀-term - S₁-term = y^k * k / (k! (k+1)!)`, and `f 0 = 0`
  have hf : ∀ k : ℕ, besselTerm 0 y k - besselTerm 1 y k = y ^ k * k / ((k ! : ℝ) * ((k + 1)! : ℝ)) := by
    intro k
    unfold besselTerm
    rw [show (k + 0)! = k ! from rfl, Nat.factorial_succ]
    push_cast
    have : (k ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp
    ring
  have hd' : HasSum (fun k : ℕ => y ^ k * k / ((k ! : ℝ) * ((k + 1)! : ℝ)))
      (besselS 0 y - besselS 1 y) := by
    convert hd using 1; ext k; exact (hf k).symm
  rw [← hasSum_nat_add_iff' 1] at hd'
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, zero_div,
    sub_zero] at hd'
  have h2 := (besselS_hasSum 2 hy).mul_left y
  have : (fun k : ℕ => y * besselTerm 2 y k) = fun k : ℕ => y ^ (k + 1) * ((k + 1 : ℕ) : ℝ) /
      (((k + 1)! : ℝ) * (((k + 1) + 1)! : ℝ)) := by
    ext k
    unfold besselTerm
    rw [Nat.factorial_succ k]
    push_cast
    have : (k ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp
    ring
  rw [this] at h2
  exact h2.unique hd'

end FormalResearch.ModularBootstrap.Bessel
