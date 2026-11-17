module

public import FormalResearch.Special.BarnesG

/-!
# Barnes' `G` as an entire function

`barnesG w = G(w + n) ∏_{k<n} 1/Γ(w+k)` for any `n` with `Re (w+n) > 0` (independent of `n` by the
functional equation `G(w+1) = Γ(w) G(w)` of `BarnesG`).  Since `1/Γ` is entire (Mathlib), this
extends `G` from `Re w > 0` to an entire function.  Proved:

* `differentiable_barnesG` : `G` is entire; `barnesG_eq_barnesG0` : it agrees with `barnesG0` on
  `Re w > 0`; `barnesG_one : G(1) = 1`;
* `barnesG_add_one` : `G(w+1) = Γ(w) G(w)` for all `w ≠ 0` (at `w = -m`, `m ≥ 1`, both sides are `0`
  with Mathlib's junk value `Γ(-m) = 0`; at `w = 0` the functional equation reads `1 = ∞ · 0`);
* `barnesG_eq_zero_iff` : the zeros of `G` are exactly `0, -1, -2, …`.

The orders of the zeros (`m+1` at `-m`) are in `BarnesZeroOrder`.  Not formalised: the Hadamard
product representation of `G` (order 2) and the Weierstrass product convergence on all of `ℂ`.
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set Complex

/-- The `n`-th shifted representative of `G`. -/
noncomputable def barnesGn (n : ℕ) (w : ℂ) : ℂ :=
  barnesG0 (w + n) * ∏ k ∈ Finset.range n, (1 / Gamma (w + k))

lemma barnesGn_succ {n : ℕ} {w : ℂ} (hw : 0 < (w + n).re) : barnesGn (n + 1) w = barnesGn n w := by
  unfold barnesGn
  have hΓ : Gamma (w + n) ≠ 0 := Gamma_ne_zero (mem_rhp_ne_neg_nat (by simpa [rhp] using hw))
  rw [Finset.prod_range_succ, show w + ((n + 1 : ℕ) : ℂ) = (w + n) + 1 by push_cast; ring,
    barnesG0_add_one hw]
  field_simp

lemma barnesGn_eq_of_le {n m : ℕ} {w : ℂ} (hn : 0 < (w + n).re) (hnm : n ≤ m) :
    barnesGn m w = barnesGn n w := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [barnesGn_succ, ih]
    have : (0 : ℝ) ≤ (m : ℝ) - n := by
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      linarith
    simp only [Complex.add_re, Complex.natCast_re] at hn ⊢
    linarith

/-- The number of shifts used at `w`. -/
noncomputable def barnesShift (w : ℂ) : ℕ := ⌊-w.re⌋₊ + 1

lemma barnesShift_pos (w : ℂ) : 0 < (w + barnesShift w).re := by
  have := Nat.lt_floor_add_one (-w.re)
  have h : (w + (barnesShift w : ℂ)).re = w.re + (barnesShift w : ℝ) := by simp
  rw [h]
  unfold barnesShift
  push_cast
  linarith

/-- **Barnes' `G` function**, entire. -/
noncomputable def barnesG (w : ℂ) : ℂ := barnesGn (barnesShift w) w

lemma barnesG_eq_barnesGn {n : ℕ} {w : ℂ} (hn : 0 < (w + n).re) : barnesG w = barnesGn n w := by
  unfold barnesG
  rcases le_total (barnesShift w) n with h | h
  · rw [barnesGn_eq_of_le (barnesShift_pos w) h]
  · rw [barnesGn_eq_of_le hn h]

lemma barnesG_eq_barnesG0 {w : ℂ} (hw : 0 < w.re) : barnesG w = barnesG0 w := by
  rw [barnesG_eq_barnesGn (n := 0) (by simpa using hw)]
  simp [barnesGn]

lemma differentiableAt_barnesGn (n : ℕ) {w : ℂ} (hw : 0 < (w + n).re) :
    DifferentiableAt ℂ (barnesGn n) w := by
  unfold barnesGn
  refine DifferentiableAt.mul ?_ ?_
  · exact ((hasDerivAt_barnesG0 hw).comp_add_const w (n : ℂ)).differentiableAt
  · have : ∀ k : ℕ, DifferentiableAt ℂ (fun w => 1 / Gamma (w + k)) w := fun k => by
      have h := (differentiable_one_div_Gamma.comp (differentiable_id.add_const (k : ℂ))) w
      simp only [Function.comp_def, id, one_div] at h ⊢
      exact h
    exact DifferentiableAt.fun_finsetProd (fun k _ => this k)

theorem differentiable_barnesG : Differentiable ℂ barnesG := by
  intro w
  have hev : barnesG =ᶠ[𝓝 w] barnesGn (barnesShift w) := by
    have ho : IsOpen {u : ℂ | 0 < (u + (barnesShift w : ℂ)).re} :=
      isOpen_lt continuous_const (continuous_re.comp (continuous_id.add continuous_const))
    filter_upwards [ho.mem_nhds (barnesShift_pos w)] with u hu using barnesG_eq_barnesGn hu
  exact (differentiableAt_barnesGn _ (barnesShift_pos w)).congr_of_eventuallyEq hev

lemma barnesG_one : barnesG 1 = 1 := by
  rw [barnesG_eq_barnesG0 (by simp), barnesG0_one]


lemma barnesGn_eq_zero_iff (n : ℕ) (w : ℂ) :
    barnesGn n w = 0 ↔ ∃ k < n, ∃ m : ℕ, w + k = -(m : ℂ) := by
  unfold barnesGn
  rw [mul_eq_zero, Finset.prod_eq_zero_iff]
  simp only [barnesG0_ne_zero, false_or, Finset.mem_range, one_div, inv_eq_zero, Gamma_eq_zero_iff]

/-- The zeros of Barnes' `G` are exactly `0, -1, -2, …`. -/
theorem barnesG_eq_zero_iff (w : ℂ) : barnesG w = 0 ↔ ∃ m : ℕ, w = -(m : ℂ) := by
  unfold barnesG
  rw [barnesGn_eq_zero_iff]
  constructor
  · rintro ⟨k, -, m, h⟩
    exact ⟨m + k, by push_cast; linear_combination h⟩
  · rintro ⟨m, h⟩
    exact ⟨0, by unfold barnesShift; omega, m, by simp [h]⟩

lemma barnesGn_succ_shift (n : ℕ) (w : ℂ) :
    barnesGn (n + 1) w = (1 / Gamma w) * barnesGn n (w + 1) := by
  unfold barnesGn
  rw [Finset.prod_range_succ']
  have h1 : w + ((n + 1 : ℕ) : ℂ) = (w + 1) + n := by push_cast; ring
  have h2 : ∀ k : ℕ, w + ((k + 1 : ℕ) : ℂ) = (w + 1) + k := fun k => by push_cast; ring
  simp only [h1, h2, Nat.cast_zero, add_zero]
  ring

/-- **Functional equation** `G(w+1) = Γ(w) G(w)` for `w ≠ 0`.  At `w = 0` it reads `1 = ∞ · 0`. -/
theorem barnesG_add_one {w : ℂ} (hw : w ≠ 0) : barnesG (w + 1) = Gamma w * barnesG w := by
  by_cases hpole : ∃ m : ℕ, w = -(m : ℂ)
  · obtain ⟨m, rfl⟩ := hpole
    have hm : m ≠ 0 := fun h => hw (by simp [h])
    have h0 : barnesG (-(m : ℂ) + 1) = 0 := by
      rw [barnesG_eq_zero_iff]
      refine ⟨m - 1, ?_⟩
      have : ((m - 1 : ℕ) : ℂ) = (m : ℂ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hm)]; simp
      rw [this]; ring
    rw [h0, Gamma_neg_nat_eq_zero, zero_mul]
  · have hΓ : Gamma w ≠ 0 := fun h => hpole ((Gamma_eq_zero_iff w).mp h)
    set n := barnesShift w
    have hpos : 0 < (w + n).re := barnesShift_pos w
    have e1 : barnesG (w + 1) = barnesGn n (w + 1) := by
      refine barnesG_eq_barnesGn ?_
      simp only [Complex.add_re, Complex.one_re, Complex.natCast_re] at hpos ⊢; linarith
    have e2 : barnesG w = barnesGn (n + 1) w := by
      refine barnesG_eq_barnesGn ?_
      simp only [Complex.add_re, Complex.natCast_re, Nat.cast_add, Nat.cast_one, Complex.one_re] at hpos ⊢
      linarith
    rw [e1, e2, barnesGn_succ_shift]
    field_simp

lemma barnesG_ne_zero_of_re_pos {w : ℂ} (hw : 0 < w.re) : barnesG w ≠ 0 := by
  rw [barnesG_eq_barnesG0 hw]; exact barnesG0_ne_zero w

/-- info: 'FormalResearch.Special.Barnes.barnesG_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms barnesG_add_one

/-- info: 'FormalResearch.Special.Barnes.differentiable_barnesG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiable_barnesG

/-- info: 'FormalResearch.Special.Barnes.barnesG_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms barnesG_eq_zero_iff

end FormalResearch.Special.Barnes
