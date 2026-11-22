/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Tactic.LinearCombination

/-!
# Complex numbers off the integers and off the poles of `Γ`

Bookkeeping for parameters that avoid the integers or the nonpositive integers, and the
density argument extending an identity of continuous functions from the non-integers to
all of `ℂ`.

## Main results

* `Complex.eq_of_continuous_of_eq_off_int`: two continuous functions on `ℂ` that agree off the
  integers agree everywhere.
* `Complex.ne_neg_natCast_of_ne_intCast`, `Complex.add_one_ne_intCast_of_ne_intCast`:
  bookkeeping for non-integer parameters.
* `Complex.add_natCast_ne_zero_of_ne_neg_natCast`, `Complex.add_natCast_ne_zero_of_re_pos`,
  `Complex.one_div_two_ne_neg_natCast`, `Complex.three_div_two_ne_neg_natCast`: parameters off
  the poles of `Γ`.
* `Complex.forall_of_mem_integerComplement`, `Complex.mem_integerComplement_of_forall`,
  `Complex.not_neg_nat_of_mem_integerComplement`: membership in `ℂ \ ℤ` (Mathlib's
  `Complex.integerComplement`).
* `Complex.integerComplement_nhdsWithin_neBot`, `Complex.eq_of_continuousAt_of_integerComplement`:
  every point is a limit of nonintegers, so two functions continuous at `b` that agree off the
  integers agree at `b`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Complex

/-- Two continuous functions on `ℂ` that agree off the integers agree everywhere. -/
theorem eq_of_continuous_of_eq_off_int {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ μ : ℂ, (∀ n : ℤ, μ ≠ n) → f μ = g μ) (μ : ℂ) : f μ = g μ := by
  have hd : Dense (Set.range (fun n : ℤ => (n : ℂ)))ᶜ :=
    (Set.countable_range _).dense_compl ℂ
  exact congrFun (hf.ext_on hd hg fun ν hν => h ν fun n hn => hν ⟨n, hn.symm⟩) μ

/-- A non-integer is not a nonpositive integer. -/
theorem ne_neg_natCast_of_ne_intCast {b : ℂ} (hb : ∀ k : ℤ, b ≠ k) : ∀ k : ℕ, b ≠ -k :=
  fun k h => hb (-(k : ℤ)) (by rw [h]; push_cast; ring)

/-- If `ν` is not an integer, neither is `ν + 1`. -/
theorem add_one_ne_intCast_of_ne_intCast {ν : ℂ} (hν : ∀ k : ℤ, ν ≠ k) :
    ∀ k : ℤ, ν + 1 ≠ k := fun k h =>
  hν (k - 1) (by push_cast; linear_combination h)

/-- If `l` is not a nonpositive integer, then `l + n ≠ 0` for every natural `n`. -/
theorem add_natCast_ne_zero_of_ne_neg_natCast {l : ℂ} (hl : ∀ n : ℕ, l ≠ -n) (n : ℕ) :
    l + n ≠ 0 := fun h => hl n (eq_neg_of_add_eq_zero_left h)

/-- If `Re a > 0`, then `a + n ≠ 0` for every natural `n`. -/
theorem add_natCast_ne_zero_of_re_pos {a : ℂ} (ha : 0 < a.re) (k : ℕ) : a + k ≠ 0 := by
  intro h
  have := congrArg re h
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- `1/2` is not a nonpositive integer. -/
theorem one_div_two_ne_neg_natCast : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
  have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]

/-- `3/2` is not a nonpositive integer. -/
theorem three_div_two_ne_neg_natCast : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
  have := congrArg re h
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- A noninteger complex number is not a nonpositive integer. -/
theorem not_neg_nat_of_mem_integerComplement {c : ℂ} (hc : c ∈ integerComplement) :
    ∀ k : ℕ, c ≠ -(k : ℂ) := fun k h => hc ⟨-k, by rw [h]; push_cast; ring⟩

/-- A complex number different from every integer lies in `ℂ \ ℤ`. -/
theorem mem_integerComplement_of_forall {c : ℂ} (hc : ∀ k : ℤ, c ≠ k) : c ∈ integerComplement :=
  fun ⟨k, hk⟩ => hc k hk.symm

/-- A point of `ℂ \ ℤ` differs from every integer. -/
theorem forall_of_mem_integerComplement {c : ℂ} (hc : c ∈ integerComplement) : ∀ k : ℤ, c ≠ k :=
  fun k hk => hc ⟨k, hk.symm⟩

/-- Every complex `b` is an accumulation point of `ℂ \ ℤ`. -/
theorem integerComplement_nhdsWithin_neBot (b : ℂ) : (𝓝[integerComplement] b).NeBot := by
  have hd : Dense integerComplement :=
    (Set.countable_range (fun k : ℤ => (k : ℂ))).dense_compl ℂ
  exact mem_closure_iff_nhdsWithin_neBot.mp (hd b)

/-- Two functions continuous at `b` that agree at all noninteger points agree at `b`. -/
theorem eq_of_continuousAt_of_integerComplement {f g : ℂ → ℂ} {b : ℂ} (hf : ContinuousAt f b)
    (hg : ContinuousAt g b) (h : ∀ c ∈ integerComplement, f c = g c) : f b = g b := by
  have := integerComplement_nhdsWithin_neBot b
  exact tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun c hc => (h c hc).symm))

end Complex
