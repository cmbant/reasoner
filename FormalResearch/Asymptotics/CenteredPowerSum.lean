module

public import Mathlib

/-!
# Centered power sums and Bernoulli polynomials

`centeredPowerSum p n = ∑_{k<p} (k - (p-1)/2)^n` is the power sum `S_n(p)` over the `p` equally
spaced points `-(p-1)/2, -(p-3)/2, …, (p-1)/2` (the centred integers or half-integers).  For even
`n = 2r` it is a Bernoulli polynomial value,

  `S_{2r}(p) = 2 B_{2r+1}((p+1)/2) / (2r+1)`   (`centeredPowerSum_even_eq_bernoulliFun`),

valid for every `p, r ∈ ℕ` (for `r = 0` it reads `S_0(p) = p`).  The proof telescopes the
difference equation `B_{n+1}(x+1) - B_{n+1}(x) = (n+1) x^n` (`bernoulli_telescope`) and uses the
reflection `B_{n}(1-x) = (-1)^n B_n(x)`; both are Mathlib's `Polynomial.bernoulli` facts.

Also recorded: the odd sums vanish (`centeredPowerSum_odd`), the bound
`|S_n(p)| ≤ p (p/2)^n` (`abs_centeredPowerSum_le`) and `S_2(p) = p(p²-1)/12`
(`centeredPowerSum_two`).
-/

@[expose] public section

namespace FormalResearch.Asymptotics

open Finset Polynomial

/-- `S_n(p) = ∑_{k<p} (k - (p-1)/2)^n`: the `n`-th power sum of the `p` points
`-(p-1)/2, …, (p-1)/2`. -/
noncomputable def centeredPowerSum (p n : ℕ) : ℝ :=
  ∑ k ∈ range p, ((k : ℝ) - ((p : ℝ) - 1) / 2) ^ n

/-- Telescoping: `(m+1) ∑_{k<p} (a+k)^m = B_{m+1}(a+p) - B_{m+1}(a)`. -/
theorem bernoulli_telescope (m : ℕ) (a : ℚ) (p : ℕ) :
    ((m : ℚ) + 1) * ∑ k ∈ range p, (a + k) ^ m =
      (Polynomial.bernoulli (m + 1)).eval (a + p) - (Polynomial.bernoulli (m + 1)).eval a := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [sum_range_succ, mul_add, ih]
    have h := bernoulli_eval_one_add (m + 1) (a + p)
    rw [show a + ((p + 1 : ℕ) : ℚ) = 1 + (a + p) by push_cast; ring, h]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

/-- The rational form of the Bernoulli evaluation of an even centred power sum. -/
theorem centeredPowerSum_even_rat (p r : ℕ) :
    ((2 * r : ℚ) + 1) * ∑ k ∈ range p, ((k : ℚ) - ((p : ℚ) - 1) / 2) ^ (2 * r) =
      2 * (Polynomial.bernoulli (2 * r + 1)).eval (((p : ℚ) + 1) / 2) := by
  have h := bernoulli_telescope (2 * r) (-(((p : ℚ) - 1) / 2)) p
  have e2 : -(((p : ℚ) - 1) / 2) + p = ((p : ℚ) + 1) / 2 := by ring
  have e3 : -(((p : ℚ) - 1) / 2) = 1 - ((p : ℚ) + 1) / 2 := by ring
  rw [e2, e3, bernoulli_eval_one_sub] at h
  have e1 : ∀ k : ℕ, 1 - ((p : ℚ) + 1) / 2 + k = (k : ℚ) - ((p : ℚ) - 1) / 2 := fun k => by ring
  simp only [e1] at h
  push_cast at h
  rw [h]
  have : (-1 : ℚ) ^ (2 * r + 1) = -1 := by rw [pow_succ, pow_mul]; simp
  rw [this]; ring

lemma bernoulliFun_ratCast (k : ℕ) (q : ℚ) :
    bernoulliFun k (q : ℝ) = (((Polynomial.bernoulli k).eval q : ℚ) : ℝ) := by
  unfold bernoulliFun
  rw [Polynomial.eval_map]
  have := Polynomial.eval₂_at_apply (p := Polynomial.bernoulli k) (algebraMap ℚ ℝ) q
  simpa using this

/-- **`S_{2r}(p) = 2 B_{2r+1}((p+1)/2) / (2r+1)`** for all `p, r ∈ ℕ`
(`B_n = bernoulliFun n` the Bernoulli polynomials). -/
theorem centeredPowerSum_even_eq_bernoulliFun (p r : ℕ) :
    centeredPowerSum p (2 * r) = 2 * bernoulliFun (2 * r + 1) (((p : ℝ) + 1) / 2) / (2 * r + 1) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (centeredPowerSum_even_rat p r)
  have e : (((p : ℝ) + 1) / 2) = ((((p : ℚ) + 1) / 2 : ℚ) : ℝ) := by push_cast; ring
  rw [e, bernoulliFun_ratCast]
  push_cast at h
  unfold centeredPowerSum
  rw [eq_div_iff (by positivity)]
  linarith

/-- Odd centred power sums vanish. -/
theorem centeredPowerSum_odd (p r : ℕ) : centeredPowerSum p (2 * r + 1) = 0 := by
  unfold centeredPowerSum
  have h := Finset.sum_range_reflect (fun k : ℕ => ((k : ℝ) - ((p : ℝ) - 1) / 2) ^ (2 * r + 1)) p
  have h2 : ∀ k ∈ range p, ((((p - 1 - k : ℕ)) : ℝ) - ((p : ℝ) - 1) / 2) ^ (2 * r + 1) =
      -(((k : ℝ) - ((p : ℝ) - 1) / 2) ^ (2 * r + 1)) := by
    intro k hk
    have hk' : k < p := mem_range.1 hk
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    rw [← Odd.neg_pow (by simp)]
    congr 1; ring
  rw [sum_congr rfl h2, sum_neg_distrib] at h
  linarith

/-- `|S_n(p)| ≤ p (p/2)^n`. -/
theorem abs_centeredPowerSum_le (p n : ℕ) :
    |centeredPowerSum p n| ≤ p * ((p : ℝ) / 2) ^ n := by
  unfold centeredPowerSum
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ k ∈ range p, |((k : ℝ) - ((p : ℝ) - 1) / 2) ^ n| ≤ ((p : ℝ) / 2) ^ n := by
    intro k hk
    have hk' : k < p := mem_range.1 hk
    rw [abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ n
    have h1 : (k : ℝ) + 1 ≤ p := by exact_mod_cast hk'
    have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [abs_le]; constructor <;> linarith
  calc _ ≤ ∑ k ∈ range p, ((p : ℝ) / 2) ^ n := sum_le_sum this
    _ = _ := by simp

private theorem bernoulliFun_eq_sum' (n : ℕ) (a : ℝ) :
    bernoulliFun n a =
      ∑ i ∈ range (n + 1), (_root_.bernoulli i : ℝ) * (Nat.choose n i : ℝ) * a ^ (n - i) := by
  simp [bernoulliFun, Polynomial.bernoulli, Polynomial.eval_map, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_monomial]

/-- `S_2(p) = p (p²-1) / 12`. -/
theorem centeredPowerSum_two (p : ℕ) :
    centeredPowerSum p 2 = (p : ℝ) * ((p : ℝ) ^ 2 - 1) / 12 := by
  have h := centeredPowerSum_even_eq_bernoulliFun p 1
  simp only [mul_one] at h
  rw [h]
  have h3 : ∀ y : ℝ, bernoulliFun 3 y = y ^ 3 - 3 / 2 * y ^ 2 + y / 2 := by
    intro y
    rw [bernoulliFun_eq_sum']
    have h3 : _root_.bernoulli 3 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
    simp [sum_range_succ, _root_.bernoulli_two, _root_.bernoulli_one, _root_.bernoulli_zero, h3]
    ring
  norm_num [h3]
  ring

/-- info: 'FormalResearch.Asymptotics.centeredPowerSum_even_eq_bernoulliFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms centeredPowerSum_even_eq_bernoulliFun

/-- info: 'FormalResearch.Asymptotics.centeredPowerSum_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms centeredPowerSum_odd

end FormalResearch.Asymptotics
