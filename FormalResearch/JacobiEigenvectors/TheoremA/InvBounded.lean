module

public import Mathlib

/-!
# Paper J, Layer 2: bounded-derivative classes (L2.E, support for `InvCoeffs`)

Source: Paper J `thmA.tex`, proof of `cor:eigen` (b)(iii) ("`x_r in C^{M+1-r}([0, pi L])`, uniformly in `mu`").  The paper takes the uniformity "by compactness"; the frozen `InvExpansion` asks for an explicit bound `Cx`
(finding F-BB-3), and since the parameter space is an abstract compact set with no continuity in `mu`, the bound must come from quantitative estimates.  This file provides the elementary calculus for them.

## Proved here

* `BD I m C g`: `g` is `C^m` on `I` with explicit derivatives, all of order `<= m` bounded by `C` (an inductive predicate: a bound for `g` and a derivative function `g'` with `BD I (m-1) C g'`).
* Closure: `BD.add`, `BD.neg`, `BD.sub`, `BD.const`, `BD.mul_exists` (product; the constant depends on `(m, C_1, C_2)` only), `BD.inv_exists` (reciprocal of a function bounded away from `0`), `BD.mono_m`, `BD.mono_C`.
* `BD.contDiffOn_bound`: on `I = [a, b]` a `BD` function is `ContDiffOn m` with `|iteratedDerivWithin i g I y| <= C` for `i <= m` (the form used by `InvExpansion`).

## Differences from the paper

The constants are existentially quantified before the functions, so they are uniform over any family (here `mu in K`).

## Not formalised

Nothing: the file is self-contained calculus.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA.InvBD

open Set

/-- `g` is `C^m` on `I` with all derivatives of order `<= m` bounded by `C`, the derivatives being given by explicit functions
(`HasDerivWithinAt`), so that the closure properties below are proved by plain induction and the constants depend on `(m, C)` only. -/
def BD (I : Set ℝ) : ℕ → ℝ → (ℝ → ℝ) → Prop
  | 0, C, g => ContinuousOn g I ∧ ∀ y ∈ I, |g y| ≤ C
  | m + 1, C, g => (∀ y ∈ I, |g y| ≤ C) ∧ ∃ g' : ℝ → ℝ, (∀ y ∈ I, HasDerivWithinAt g (g' y) I y) ∧ BD I m C g'

variable {I : Set ℝ}

lemma BD.bound : ∀ {m : ℕ} {C : ℝ} {g : ℝ → ℝ}, BD I m C g → ∀ y ∈ I, |g y| ≤ C
  | 0, _, _, h => h.2
  | _ + 1, _, _, h => h.1

lemma BD.continuousOn : ∀ {m : ℕ} {C : ℝ} {g : ℝ → ℝ}, BD I m C g → ContinuousOn g I
  | 0, _, _, h => h.1
  | _ + 1, _, _, h => by
    obtain ⟨-, g', hg, -⟩ := h
    exact fun y hy => (hg y hy).continuousWithinAt

lemma BD.mono_m : ∀ {m : ℕ} {C : ℝ} {g : ℝ → ℝ}, BD I (m + 1) C g → BD I m C g
  | 0, C, g, h => ⟨h.continuousOn, h.bound⟩
  | m + 1, C, g, h => by
    obtain ⟨hb, g', hg, hg'⟩ := h
    exact ⟨hb, g', hg, hg'.mono_m⟩

lemma BD.mono_le {m n : ℕ} (hmn : m ≤ n) {C : ℝ} {g : ℝ → ℝ} (h : BD I n C g) : BD I m C g := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n hmn ih => exact ih h.mono_m

lemma BD.mono_C : ∀ {m : ℕ} {C C' : ℝ} {g : ℝ → ℝ}, C ≤ C' → BD I m C g → BD I m C' g
  | 0, _, _, _, hC, h => ⟨h.1, fun y hy => (h.2 y hy).trans hC⟩
  | m + 1, _, _, _, hC, h => by
    obtain ⟨hb, g', hg, hg'⟩ := h
    exact ⟨fun y hy => (hb y hy).trans hC, g', hg, hg'.mono_C hC⟩

lemma BD.const (m : ℕ) : ∀ c : ℝ, BD I m |c| (fun _ => c) := by
  induction m with
  | zero => exact fun c => ⟨continuousOn_const, fun _ _ => le_rfl⟩
  | succ m ih => exact fun c => ⟨fun _ _ => le_rfl, fun _ => 0, fun y _ => hasDerivWithinAt_const y I c, (ih 0).mono_C (by simp)⟩

lemma BD.add : ∀ {m : ℕ} {C1 C2 : ℝ} {f g : ℝ → ℝ}, BD I m C1 f → BD I m C2 g → BD I m (C1 + C2) (fun y => f y + g y)
  | 0, _, _, _, _, hf, hg => ⟨hf.1.add hg.1, fun y hy => (abs_add_le _ _).trans (add_le_add (hf.2 y hy) (hg.2 y hy))⟩
  | m + 1, _, _, _, _, hf, hg => by
    obtain ⟨hfb, f', hf', hf''⟩ := hf
    obtain ⟨hgb, g', hg', hg''⟩ := hg
    exact ⟨fun y hy => (abs_add_le _ _).trans (add_le_add (hfb y hy) (hgb y hy)), fun y => f' y + g' y,
      fun y hy => (hf' y hy).add (hg' y hy), hf''.add hg''⟩

lemma BD.neg : ∀ {m : ℕ} {C : ℝ} {f : ℝ → ℝ}, BD I m C f → BD I m C (fun y => -f y)
  | 0, _, _, hf => ⟨hf.1.neg, fun y hy => by simpa using hf.2 y hy⟩
  | m + 1, _, _, hf => by
    obtain ⟨hfb, f', hf', hf''⟩ := hf
    exact ⟨fun y hy => by simpa using hfb y hy, fun y => -f' y, fun y hy => (hf' y hy).neg, hf''.neg⟩

lemma BD.sub {m : ℕ} {C1 C2 : ℝ} {f g : ℝ → ℝ} (hf : BD I m C1 f) (hg : BD I m C2 g) : BD I m (C1 + C2) (fun y => f y - g y) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

/-- Product: the constant depends on `(m, C1, C2)` only. -/
lemma BD.mul_exists (m : ℕ) (C1 C2 : ℝ) : ∃ C3 : ℝ, ∀ f g : ℝ → ℝ, BD I m C1 f → BD I m C2 g → BD I m C3 (fun y => f y * g y) := by
  induction m with
  | zero =>
    refine ⟨C1 * C2, fun f g hf hg => ⟨hf.1.mul hg.1, fun y hy => ?_⟩⟩
    rw [abs_mul]
    exact mul_le_mul (hf.2 y hy) (hg.2 y hy) (abs_nonneg _) ((abs_nonneg _).trans (hf.2 y hy))
  | succ m ih =>
    obtain ⟨C3, h3⟩ := ih
    refine ⟨max (C1 * C2) (C3 + C3), fun f g hf hg => ?_⟩
    have hfm := hf.mono_m
    have hgm := hg.mono_m
    obtain ⟨hfb, f', hf', hf''⟩ := hf
    obtain ⟨hgb, g', hg', hg''⟩ := hg
    refine ⟨fun y hy => ?_, fun y => f' y * g y + f y * g' y, fun y hy => (hf' y hy).mul (hg' y hy), ?_⟩
    · rw [abs_mul]
      exact (mul_le_mul (hfb y hy) (hgb y hy) (abs_nonneg _) ((abs_nonneg _).trans (hfb y hy))).trans (le_max_left _ _)
    · exact ((h3 f' g hf'' hgm).add (h3 f g' hfm hg'')).mono_C (le_max_right _ _)

/-- Reciprocal of a function bounded away from `0`: the constant depends on `(m, C, c)` only. -/
lemma BD.inv_exists (m : ℕ) (C c : ℝ) (hc : 0 < c) :
    ∃ C' : ℝ, ∀ g : ℝ → ℝ, BD I m C g → (∀ y ∈ I, c ≤ |g y|) → BD I m C' (fun y => (g y)⁻¹) := by
  induction m with
  | zero =>
    refine ⟨c⁻¹, fun g hg hlow => ⟨?_, fun y hy => ?_⟩⟩
    · exact hg.1.inv₀ (fun y hy => by have := hlow y hy; intro h; rw [h, abs_zero] at this; linarith)
    · rw [abs_inv]
      exact inv_anti₀ hc (hlow y hy)
  | succ m ih =>
    obtain ⟨Cm, hCm⟩ := ih
    obtain ⟨C4, h4⟩ := BD.mul_exists (I := I) m Cm Cm
    obtain ⟨C5, h5⟩ := BD.mul_exists (I := I) m C C4
    refine ⟨max c⁻¹ C5, fun g hg hlow => ?_⟩
    have hgm := hg.mono_m
    obtain ⟨hgb, g', hg', hg''⟩ := hg
    have hne : ∀ y ∈ I, g y ≠ 0 := fun y hy h => by have := hlow y hy; rw [h, abs_zero] at this; linarith
    have hinv := hCm g hgm hlow
    refine ⟨fun y hy => ?_, fun y => -(g' y * ((g y)⁻¹ * (g y)⁻¹)), fun y hy => ?_, ?_⟩
    · rw [abs_inv]
      exact (inv_anti₀ hc (hlow y hy)).trans (le_max_left _ _)
    · have := (hg' y hy).inv (hne y hy)
      convert this using 1
      have := hne y hy
      field_simp
    · exact ((h5 g' _ hg'' (h4 _ _ hinv hinv)).neg).mono_C (le_max_right _ _)

/-- A `BD` function is `C^m` with the iterated derivatives (within `[a, b]`) bounded by `C`. -/
lemma BD.contDiffOn_bound {a b : ℝ} (hab : a < b) : ∀ (m : ℕ) (C : ℝ) (g : ℝ → ℝ), BD (Icc a b) m C g →
    ContDiffOn ℝ (m : WithTop ℕ∞) g (Icc a b) ∧ ∀ i ≤ m, ∀ y ∈ Icc a b, |iteratedDerivWithin i g (Icc a b) y| ≤ C := by
  intro m
  induction m with
  | zero =>
    intro C g hg
    refine ⟨?_, fun i hi y hy => ?_⟩
    · exact contDiffOn_zero.2 hg.1
    · have : i = 0 := by omega
      subst this
      simpa [iteratedDerivWithin_zero] using hg.2 y hy
  | succ m ih =>
    intro C g hg
    obtain ⟨hb, g', hg', hg''⟩ := hg
    obtain ⟨hc', hbd'⟩ := ih C g' hg''
    have hU := uniqueDiffOn_Icc hab
    have hdw : ∀ y ∈ Icc a b, derivWithin g (Icc a b) y = g' y := fun y hy => (hg' y hy).derivWithin (hU y hy)
    refine ⟨?_, fun i hi y hy => ?_⟩
    · have := (contDiffOn_succ_iff_derivWithin (n := m) (f := g) hU).2 ⟨fun y hy => (hg' y hy).differentiableWithinAt,
        fun h => absurd h (by exact_mod_cast WithTop.coe_ne_top), hc'.congr (fun y hy => hdw y hy)⟩
      exact_mod_cast this
    · rcases i with _ | i
      · simpa [iteratedDerivWithin_zero] using hb y hy
      · rw [iteratedDerivWithin_succ']
        have heq : iteratedDerivWithin i (derivWithin g (Icc a b)) (Icc a b) y = iteratedDerivWithin i g' (Icc a b) y := by
          exact iteratedDerivWithin_congr (fun z hz => hdw z hz) hy
        rw [heq]
        exact hbd' i (by omega) y hy

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.InvBD.BD.mul_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.InvBD.BD.mul_exists

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.InvBD.BD.inv_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.InvBD.BD.inv_exists

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.InvBD.BD.contDiffOn_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.InvBD.BD.contDiffOn_bound

end FormalResearch.JacobiEigenvectors.TheoremA.InvBD
