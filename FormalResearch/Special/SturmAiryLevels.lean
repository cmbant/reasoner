module

public import Mathlib

/-!
# Counting the points where a strictly increasing function meets a lattice of levels

A purely real-variable lemma used for the Prüfer angle `θ` of a solution of `y'' = q y`: if `g` is
continuous and strictly increasing on `[a, b]` and `c ∈ ℝ`, then the points `x ∈ (a, b]` with
`g x ∈ c + πℤ` are in bijection with the integers `k` with `g a < c + kπ ≤ g b`, so their number is
`⌊(g b - c)/π⌋ - ⌊(g a - c)/π⌋`.

* `AtLevel g c x`: `g x = c + kπ` for some integer `k`.
* `Levels.ncard_levels`, `Levels.finite_levels`: the count by floors (and finiteness).
* `Levels.level_succ`: if `g a = c + kπ`, `g b = c + k'π` and there is no level point strictly between
  `a` and `b`, then `k' = k + 1`.
* `Levels.ncard_window`: if `g b = g a + π` then, for every `c`, exactly one point of `(a, b]` is at
  a level `c + πℤ` (`Levels.exists_unique_window`); it lies in `(a, b)` when `g b` is not at level
  `c` (`Levels.exists_unique_window_Ioo`).
* `Levels.exists_unique_level`: `g a < L ≤ g b` gives a unique `x ∈ (a, b]` with `g x = L`.

All proved; no ODE input.
-/

@[expose] public section

open Set

namespace FormalResearch.Special.SturmAiry

/-- `g x = c + kπ` for some integer `k`. -/
def AtLevel (g : ℝ → ℝ) (c x : ℝ) : Prop := ∃ k : ℤ, g x = c + k * Real.pi

namespace Levels

variable {g : ℝ → ℝ} {a b : ℝ}

private theorem floor_level {t c : ℝ} {k : ℤ} (h : t = c + k * Real.pi) :
    ⌊(t - c) / Real.pi⌋ = k := by
  rw [h, add_sub_cancel_left, mul_div_cancel_right₀ _ Real.pi_ne_zero, Int.floor_intCast]

private theorem floor_bounds (hab : a ≤ b) (hm : StrictMonoOn g (Icc a b)) (c : ℝ) {x : ℝ}
    (hx : x ∈ Icc a b) :
    ⌊(g a - c) / Real.pi⌋ ≤ ⌊(g x - c) / Real.pi⌋ ∧
      ⌊(g x - c) / Real.pi⌋ ≤ ⌊(g b - c) / Real.pi⌋ := by
  have h1 : g a ≤ g x := hm.monotoneOn ⟨le_rfl, hab⟩ hx hx.1
  have h2 : g x ≤ g b := hm.monotoneOn hx ⟨hab, le_rfl⟩ hx.2
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le),
    Int.floor_mono (div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le)⟩

private theorem levels_mapsTo (hab : a ≤ b) (hm : StrictMonoOn g (Icc a b)) (c : ℝ) :
    MapsTo (fun x => ⌊(g x - c) / Real.pi⌋) {x | x ∈ Ioc a b ∧ AtLevel g c x}
      (Ioc ⌊(g a - c) / Real.pi⌋ ⌊(g b - c) / Real.pi⌋) := by
  rintro x ⟨hx, k, hk⟩
  have hxI : x ∈ Icc a b := Ioc_subset_Icc_self hx
  have hfl : ⌊(g x - c) / Real.pi⌋ = k := floor_level hk
  refine ⟨?_, (floor_bounds hab hm c hxI).2⟩
  show ⌊(g a - c) / Real.pi⌋ < ⌊(g x - c) / Real.pi⌋
  rw [hfl]
  refine Int.floor_lt.2 ((div_lt_iff₀ Real.pi_pos).2 ?_)
  have := hm ⟨le_rfl, hab⟩ hxI hx.1
  linarith

private theorem levels_injOn (hm : StrictMonoOn g (Icc a b)) (c : ℝ) :
    InjOn (fun x => ⌊(g x - c) / Real.pi⌋) {x | x ∈ Ioc a b ∧ AtLevel g c x} := by
  rintro x ⟨hx, k, hk⟩ x' ⟨hx', k', hk'⟩ h
  have h2 : ⌊(g x - c) / Real.pi⌋ = ⌊(g x' - c) / Real.pi⌋ := h
  rw [floor_level hk, floor_level hk'] at h2
  subst h2
  exact hm.injOn (Ioc_subset_Icc_self hx) (Ioc_subset_Icc_self hx') (by rw [hk, hk'])

/-- The levels `c + πℤ` met by `g` in `(a, b]` form a finite set. -/
theorem finite_levels (hab : a ≤ b) (hm : StrictMonoOn g (Icc a b)) (c : ℝ) :
    {x | x ∈ Ioc a b ∧ AtLevel g c x}.Finite :=
  Set.Finite.of_injOn (levels_mapsTo hab hm c) (levels_injOn hm c) (Set.finite_Ioc _ _)

/-- **Count by floors.**  For `g` continuous and strictly increasing on `[a, b]`, the number of
`x ∈ (a, b]` with `g x ∈ c + πℤ` is `⌊(g b - c)/π⌋ - ⌊(g a - c)/π⌋`. -/
theorem ncard_levels (hab : a ≤ b) (hc : ContinuousOn g (Icc a b)) (hm : StrictMonoOn g (Icc a b))
    (c : ℝ) :
    (({x | x ∈ Ioc a b ∧ AtLevel g c x}).ncard : ℤ) =
      ⌊(g b - c) / Real.pi⌋ - ⌊(g a - c) / Real.pi⌋ := by
  have h1 : ({x | x ∈ Ioc a b ∧ AtLevel g c x}).ncard =
      (Ioc ⌊(g a - c) / Real.pi⌋ ⌊(g b - c) / Real.pi⌋).ncard := by
    refine Set.ncard_congr (fun x _ => ⌊(g x - c) / Real.pi⌋) (fun x hx => levels_mapsTo hab hm c hx)
      (fun x x' hx hx' h => levels_injOn hm c hx hx' h) ?_
    intro k hk
    have hlo : g a < c + k * Real.pi := by
      have := (div_lt_iff₀ Real.pi_pos).1 (Int.floor_lt.1 hk.1)
      linarith
    have hhi : c + k * Real.pi ≤ g b := by
      have := (le_div_iff₀ Real.pi_pos).1 (Int.le_floor.1 hk.2)
      linarith
    obtain ⟨x, hx, hxk⟩ := intermediate_value_Icc hab hc (show c + k * Real.pi ∈ Icc (g a) (g b)
      from ⟨hlo.le, hhi⟩)
    have hxa : a < x := lt_of_le_of_ne hx.1 (by rintro rfl; linarith)
    exact ⟨x, ⟨⟨hxa, hx.2⟩, k, hxk⟩, floor_level hxk⟩
  rw [h1, ← Finset.coe_Ioc, Set.ncard_coe_finset, Int.card_Ioc]
  exact Int.toNat_of_nonneg (sub_nonneg.2 (floor_bounds hab hm c ⟨hab, le_rfl⟩).1)

/-- Consecutive level points differ by one level: if `g a = c + kπ`, `g b = c + k'π`, `a < b`, and
no `x ∈ (a, b)` is at a level `c + πℤ`, then `k' = k + 1`. -/
theorem level_succ (hab : a < b) (hc : ContinuousOn g (Icc a b)) (hm : StrictMonoOn g (Icc a b))
    {c : ℝ} {k k' : ℤ} (ha : g a = c + k * Real.pi) (hb : g b = c + k' * Real.pi)
    (hne : ∀ x ∈ Ioo a b, ¬ AtLevel g c x) : k' = k + 1 := by
  have h := ncard_levels hab.le hc hm c
  rw [floor_level ha, floor_level hb] at h
  have hS : {x | x ∈ Ioc a b ∧ AtLevel g c x} = {b} := by
    ext x
    constructor
    · rintro ⟨hx, hl⟩
      rcases hx.2.eq_or_lt with h | h
      · exact h
      · exact (hne x ⟨hx.1, h⟩ hl).elim
    · rintro (rfl : x = b)
      exact ⟨⟨hab, le_rfl⟩, k', hb⟩
  rw [hS, Set.ncard_singleton] at h
  push_cast at h
  omega

/-- If `g b = g a + π` (a window of one period), exactly one `x ∈ (a, b]` is at a level `c + πℤ`,
for every `c`. -/
theorem ncard_window (hab : a ≤ b) (hc : ContinuousOn g (Icc a b)) (hm : StrictMonoOn g (Icc a b))
    (hw : g b = g a + Real.pi) (c : ℝ) :
    ({x | x ∈ Ioc a b ∧ AtLevel g c x}).ncard = 1 := by
  have h := ncard_levels hab hc hm c
  have e : (g b - c) / Real.pi = (g a - c) / Real.pi + 1 := by
    rw [hw]; field_simp; ring
  rw [e, Int.floor_add_one] at h
  have : (({x | x ∈ Ioc a b ∧ AtLevel g c x}).ncard : ℤ) = 1 := by rw [h]; ring
  exact_mod_cast this

/-- **Window lemma**: if `g b = g a + π`, there is exactly one `x ∈ (a, b]` at a level `c + πℤ`. -/
theorem exists_unique_window (hab : a ≤ b) (hc : ContinuousOn g (Icc a b))
    (hm : StrictMonoOn g (Icc a b)) (hw : g b = g a + Real.pi) (c : ℝ) :
    ∃! x, x ∈ Ioc a b ∧ AtLevel g c x := by
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.1 (ncard_window hab hc hm hw c)
  have hxx : x ∈ {x | x ∈ Ioc a b ∧ AtLevel g c x} := by rw [hx]; rfl
  refine ⟨x, hxx, fun y hy => ?_⟩
  have : y ∈ ({x} : Set ℝ) := by rw [← hx]; exact hy
  exact this

/-- As `exists_unique_window`, with the point in the open interval when `g b` is not at level `c`. -/
theorem exists_unique_window_Ioo (hab : a ≤ b) (hc : ContinuousOn g (Icc a b))
    (hm : StrictMonoOn g (Icc a b)) (hw : g b = g a + Real.pi) (c : ℝ) (hb : ¬ AtLevel g c b) :
    ∃! x, x ∈ Ioo a b ∧ AtLevel g c x := by
  obtain ⟨x, ⟨hx, hl⟩, hu⟩ := exists_unique_window hab hc hm hw c
  have hxb : x ≠ b := fun h => hb (h ▸ hl)
  exact ⟨x, ⟨⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩, hl⟩, fun y hy =>
    hu y ⟨⟨hy.1.1, hy.1.2.le⟩, hy.2⟩⟩

/-- **Level crossing**: if `g a < L ≤ g b`, exactly one `x ∈ (a, b]` has `g x = L`. -/
theorem exists_unique_level (hab : a ≤ b) (hc : ContinuousOn g (Icc a b))
    (hm : StrictMonoOn g (Icc a b)) {L : ℝ} (hlo : g a < L) (hhi : L ≤ g b) :
    ∃! x, x ∈ Ioc a b ∧ g x = L := by
  obtain ⟨x, hx, hxL⟩ := intermediate_value_Icc hab hc (show L ∈ Icc (g a) (g b) from ⟨hlo.le, hhi⟩)
  have hxa : a < x := lt_of_le_of_ne hx.1 (by rintro rfl; linarith)
  exact ⟨x, ⟨⟨hxa, hx.2⟩, hxL⟩, fun y hy =>
    hm.injOn (Ioc_subset_Icc_self hy.1) hx (hy.2.trans hxL.symm)⟩

end Levels

/-- info: 'FormalResearch.Special.SturmAiry.Levels.ncard_levels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.Levels.ncard_levels

/-- info: 'FormalResearch.Special.SturmAiry.Levels.level_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.Levels.level_succ

/-- info: 'FormalResearch.Special.SturmAiry.Levels.exists_unique_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.Levels.exists_unique_window

/-- info: 'FormalResearch.Special.SturmAiry.Levels.exists_unique_window_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.Levels.exists_unique_window_Ioo

/-- info: 'FormalResearch.Special.SturmAiry.Levels.exists_unique_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.Levels.exists_unique_level

end FormalResearch.Special.SturmAiry
