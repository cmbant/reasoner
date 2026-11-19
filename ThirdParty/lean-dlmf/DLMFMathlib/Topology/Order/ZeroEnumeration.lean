/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Enumerating the positive zeros of a real function

Many special functions have their positive zeros separated by an explicit sequence
`0 = t₀ < t₁ < t₂ < ⋯ → ∞`: exactly one zero lies in each open interval `(tₙ, tₙ₊₁)` and none at the
separating points. This file turns such a separation into the standard enumeration of the zeros
by `k ↦ (the zero with exactly k smaller positive zeros)`, which is how zero sequences such as
the zeros of the cosine and sine integrals (DLMF §6.13) are specified.

## Main results

* `zcount_existsUnique_zero`: a continuous strictly increasing function changing sign on `[a, b]`
  has exactly one zero in `(a, b)`.
* `zcount_enum`: from a separating sequence to the enumeration by number of smaller zeros.
-/

@[expose] public section

open Set Filter

/-- A continuous strictly increasing function that is negative at `a` and positive at `b` has
exactly one zero in `(a, b)`. -/
theorem zcount_existsUnique_zero {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn G (Icc a b)) (hm : StrictMonoOn G (Icc a b)) (ha : G a < 0)
    (hb : 0 < G b) : ∃! x, x ∈ Ioo a b ∧ G x = 0 := by
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo hab hc ⟨ha, hb⟩
  refine ⟨x, ⟨hx, hx0⟩, fun y ⟨hy, hy0⟩ => ?_⟩
  exact hm.injOn (Ioo_subset_Icc_self hy) (Ioo_subset_Icc_self hx) (hy0.trans hx0.symm)

/-- **Enumeration of separated zeros.** If `0 = t₀ < t₁ < ⋯` is unbounded, `P` holds at exactly
one point of each `(tₙ, tₙ₊₁)` and at none of the `tₙ₊₁`, then the `k`-th positive point of `P`
(the one with exactly `k` smaller positive points) is well defined, lies in `(t_k, t_{k+1})`, and
these points are strictly increasing and exhaust the positive points of `P`. -/
theorem zcount_enum {P : ℝ → Prop} {t : ℕ → ℝ} (ht0 : t 0 = 0) (htm : StrictMono t)
    (htu : ∀ x, ∃ n, x ≤ t n) (hu : ∀ n, ∃! x, x ∈ Ioo (t n) (t (n + 1)) ∧ P x)
    (he : ∀ n, ¬ P (t (n + 1))) :
    ∃ z : ℕ → ℝ, StrictMono z ∧ (∀ n, z n ∈ Ioo (t n) (t (n + 1))) ∧
      (∀ x, 0 < x → (P x ↔ ∃ k, z k = x)) ∧
      (∀ k, 0 < z k ∧ P (z k) ∧ {y : ℝ | 0 < y ∧ y < z k ∧ P y}.ncard = k) ∧
      ∀ k, Classical.epsilon (fun x : ℝ => 0 < x ∧ P x ∧
        {y : ℝ | 0 < y ∧ y < x ∧ P y}.ncard = k) = z k := by
  choose z hz hzu using hu
  have hzI : ∀ n, z n ∈ Ioo (t n) (t (n + 1)) := fun n => (hz n).1
  have hzP : ∀ n, P (z n) := fun n => (hz n).2
  have hmono : StrictMono z := strictMono_nat_of_lt_succ fun n =>
    (hzI n).2.trans_le (htm.monotone (Nat.le_refl _) |>.trans (le_of_lt (hzI (n + 1)).1))
  have htpos : ∀ n, 0 ≤ t n := fun n => ht0 ▸ htm.monotone (Nat.zero_le n)
  have hzpos : ∀ n, 0 < z n := fun n => (htpos n).trans_lt (hzI n).1
  have hall : ∀ x, 0 < x → P x → ∃ k, z k = x := by
    intro x hx hPx
    have hex : ∃ n, x ≤ t n := htu x
    classical
    set n := Nat.find hex
    have hn : x ≤ t n := Nat.find_spec hex
    have hn0 : n ≠ 0 := by
      intro h; rw [h, ht0] at hn; linarith
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hlt : t m < x := by
      by_contra hle
      exact Nat.find_min hex (show m < n by omega) (not_lt.mp hle)
    have hne : x ≠ t (m + 1) := fun h => he m (h ▸ hPx)
    have hxI : x ∈ Ioo (t m) (t (m + 1)) :=
        ⟨hlt, lt_of_le_of_ne (by rw [← Nat.succ_eq_add_one, ← hm]; exact hn) hne⟩
    exact ⟨m, (hzu m x ⟨hxI, hPx⟩).symm⟩
  have hiff : ∀ x, 0 < x → (P x ↔ ∃ k, z k = x) := fun x hx =>
    ⟨hall x hx, fun ⟨k, hk⟩ => hk ▸ hzP k⟩
  have hcard : ∀ k, {y : ℝ | 0 < y ∧ y < z k ∧ P y}.ncard = k := by
    intro k
    have hset : {y : ℝ | 0 < y ∧ y < z k ∧ P y} = z '' Iio k := by
      ext y
      constructor
      · rintro ⟨hy0, hyk, hPy⟩
        obtain ⟨j, rfl⟩ := hall y hy0 hPy
        exact ⟨j, hmono.lt_iff_lt.mp hyk, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨hzpos j, hmono hj, hzP j⟩
    rw [hset, ncard_image_of_injective _ hmono.injective, ← Finset.coe_range, ncard_coe_finset,
      Finset.card_range]
  have hspec : ∀ k, 0 < z k ∧ P (z k) ∧ {y : ℝ | 0 < y ∧ y < z k ∧ P y}.ncard = k :=
    fun k => ⟨hzpos k, hzP k, hcard k⟩
  refine ⟨z, hmono, hzI, hiff, hspec, fun k => ?_⟩
  have he' := Classical.epsilon_spec (p := fun x : ℝ => 0 < x ∧ P x ∧
    {y : ℝ | 0 < y ∧ y < x ∧ P y}.ncard = k) ⟨z k, hspec k⟩
  obtain ⟨h0, hP, hc⟩ := he'
  obtain ⟨j, hj⟩ := hall _ h0 hP
  rw [← hj] at hc ⊢
  rw [hcard j] at hc
  rw [hc]
