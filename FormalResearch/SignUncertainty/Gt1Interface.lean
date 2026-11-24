module

public import FormalResearch.SignUncertainty.MiddleBandTransfer
public import FormalResearch.CohnElkies.HighBandUniform

/-!
# `GT.1` interface: closure of `Gt1Bounds`, linearity in the seed, and the single named input

`Gt1Bounds A W` (`MiddleBandTransfer.lean`) packages the `GT.1` symbol bounds of one symbol.  This module proves its closure under sums and scalar
multiples and the linearity `liftW (airySeedU2 a b c₀) = a liftW f₁ + b liftW g₁ + c₀ liftW g₁'`, and defines the **single named input**
`Gt1BasisInput m` (the `GT.1` bounds for the three basis seeds of the spline-multiplied lift, uniform in `δ₀ ∈ [0, 2]`) from which the bounds for every
`airySeedU2 a b c₀` follow (`gt1Bounds_airySeedU2`).  `Gt1BasisInput m` is discharged for `m ≥ 3` by `gt1BasisInput` (`Gt1NegTail.lean`), without changing any downstream statement.

Status: proved.  `Gt1BasisInput m` itself is not proved in this module (see `Gt1NegTail.lean`).
-/

@[expose] public section

open Set

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

theorem Gt1Bounds.mono {A B : ℝ} {W : ℝ → ℂ} (h : A ≤ B) (hW : Gt1Bounds A W) : Gt1Bounds B W := by
  obtain ⟨W1, W2, W3, hd, hl, hh, h0, hH⟩ := hW
  have key : ∀ t : ℝ, ∀ x : ℝ, ∀ s : ℝ, x ≤ A * |s| ^ t → x ≤ B * |s| ^ t := fun t x s hx =>
    hx.trans (mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (abs_nonneg _) _))
  refine ⟨W1, W2, W3, hd, fun s hs hs1 => ?_, fun s hs => ?_, h0.trans h, fun s hs hs1 => ?_⟩
  · obtain ⟨a, b, c⟩ := hl s hs hs1
    exact ⟨key _ _ _ a, key _ _ _ b, key _ _ _ c⟩
  · obtain ⟨a, b, c, d⟩ := hh s hs
    exact ⟨key _ _ _ a, key _ _ _ b, key _ _ _ c, key _ _ _ d⟩
  · exact key _ _ _ (hH s hs hs1)

theorem Gt1Bounds.add {A B : ℝ} {W V : ℝ → ℂ} (hW : Gt1Bounds A W) (hV : Gt1Bounds B V) :
    Gt1Bounds (A + B) (fun v => W v + V v) := by
  obtain ⟨W1, W2, W3, hd, hl, hh, h0, hH⟩ := hW
  obtain ⟨V1, V2, V3, hd', hl', hh', h0', hH'⟩ := hV
  have comb : ∀ (t : ℝ) (x y : ℂ) (s : ℝ), ‖x‖ ≤ A * |s| ^ t → ‖y‖ ≤ B * |s| ^ t → ‖x + y‖ ≤ (A + B) * |s| ^ t :=
    fun t x y s hx hy => (norm_add_le _ _).trans (by rw [add_mul]; exact add_le_add hx hy)
  refine ⟨fun s => W1 s + V1 s, fun s => W2 s + V2 s, fun s => W3 s + V3 s, fun s hs => ?_, fun s hs hs1 => ?_,
    fun s hs => ?_, ?_, fun s hs hs1 => ?_⟩
  · exact ⟨(hd s hs).1.add (hd' s hs).1, (hd s hs).2.1.add (hd' s hs).2.1, (hd s hs).2.2.add (hd' s hs).2.2⟩
  · obtain ⟨a, b, c⟩ := hl s hs hs1
    obtain ⟨a', b', c'⟩ := hl' s hs hs1
    exact ⟨comb _ _ _ _ a a', comb _ _ _ _ b b', comb _ _ _ _ c c'⟩
  · obtain ⟨a, b, c, d⟩ := hh s hs
    obtain ⟨a', b', c', d'⟩ := hh' s hs
    exact ⟨comb _ _ _ _ a a', comb _ _ _ _ b b', comb _ _ _ _ c c', comb _ _ _ _ d d'⟩
  · exact (norm_add_le _ _).trans (add_le_add h0 h0')
  · have := comb (1 / 2 : ℝ) (W s - W 0) (V s - V 0) s (hH s hs hs1) (hH' s hs hs1)
    refine le_of_eq_of_le ?_ this
    congr 1; ring

theorem Gt1Bounds.smul {A : ℝ} {W : ℝ → ℂ} (t : ℂ) (hW : Gt1Bounds A W) : Gt1Bounds (‖t‖ * A) (fun v => t * W v) := by
  obtain ⟨W1, W2, W3, hd, hl, hh, h0, hH⟩ := hW
  have sc : ∀ (e : ℝ) (x : ℂ) (s : ℝ), ‖x‖ ≤ A * |s| ^ e → ‖t * x‖ ≤ ‖t‖ * A * |s| ^ e := fun e x s hx => by
    rw [norm_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  refine ⟨fun s => t * W1 s, fun s => t * W2 s, fun s => t * W3 s, fun s hs => ?_, fun s hs hs1 => ?_,
    fun s hs => ?_, ?_, fun s hs hs1 => ?_⟩
  · exact ⟨(hd s hs).1.const_mul t, (hd s hs).2.1.const_mul t, (hd s hs).2.2.const_mul t⟩
  · obtain ⟨a, b, c⟩ := hl s hs hs1
    exact ⟨sc _ _ _ a, sc _ _ _ b, sc _ _ _ c⟩
  · obtain ⟨a, b, c, d⟩ := hh s hs
    exact ⟨sc _ _ _ a, sc _ _ _ b, sc _ _ _ c, sc _ _ _ d⟩
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left h0 (norm_nonneg _)
  · have := sc (1 / 2 : ℝ) (W s - W 0) s (hH s hs hs1)
    refine le_of_eq_of_le ?_ this
    congr 1; ring

theorem liftW_airySeedU2_lin (a b c₀ δ₀ : ℝ) (m : ℕ) (v : ℝ) :
    liftW (airySeedU2 a b c₀) δ₀ m v = (a : ℂ) * liftW (airySeedU2 1 0 0) δ₀ m v + (b : ℂ) * liftW (airySeedU2 0 1 0) δ₀ m v +
      (c₀ : ℂ) * liftW (airySeedU2 0 0 1) δ₀ m v := by
  unfold liftW
  exact liftSymbol_airySeedU2_lin a b c₀ δ₀ m (by simp)

/-- **The single named input of the middle band**: the `GT.1` bounds for the symbols `W(v) = M_ψ(iv) X̃(i c_s v)` of the three basis seeds
`f₁, g₁, g₁'`, uniform in `δ₀ ∈ [0, 2]` (spline order `m`). -/
def Gt1BasisInput (m : ℕ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ δ₀ : ℝ, δ₀ ∈ Icc (0 : ℝ) 2 →
    Gt1Bounds A (liftW (airySeedU2 1 0 0) δ₀ m) ∧ Gt1Bounds A (liftW (airySeedU2 0 1 0) δ₀ m) ∧
      Gt1Bounds A (liftW (airySeedU2 0 0 1) δ₀ m)

/-- The `GT.1` bounds for every one-level seed with coefficients `(a, b, c₀)`, with constant linear in `|a| + |b| + |c₀|`. -/
theorem gt1Bounds_airySeedU2 {m : ℕ} (h : Gt1BasisInput m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ a b c₀ δ₀ : ℝ, δ₀ ∈ Icc (0 : ℝ) 2 →
      Gt1Bounds (A * (|a| + |b| + |c₀|)) (liftW (airySeedU2 a b c₀) δ₀ m) := by
  obtain ⟨A, hA, hb⟩ := h
  refine ⟨A, hA, fun a b c₀ δ₀ hδ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hb δ₀ hδ
  have hsum := ((h1.smul (a : ℂ)).add (h2.smul (b : ℂ))).add (h3.smul (c₀ : ℂ))
  have heq : liftW (airySeedU2 a b c₀) δ₀ m = fun v => ((a : ℂ) * liftW (airySeedU2 1 0 0) δ₀ m v +
      (b : ℂ) * liftW (airySeedU2 0 1 0) δ₀ m v) + (c₀ : ℂ) * liftW (airySeedU2 0 0 1) δ₀ m v := by
    funext v; rw [liftW_airySeedU2_lin]
  rw [heq]
  refine hsum.mono ?_
  simp only [Complex.norm_real, Real.norm_eq_abs]
  nlinarith

/-- info: 'FormalResearch.SignUncertainty.Gt1Bounds.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Gt1Bounds.mono

/-- info: 'FormalResearch.SignUncertainty.Gt1Bounds.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Gt1Bounds.add

/-- info: 'FormalResearch.SignUncertainty.Gt1Bounds.smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Gt1Bounds.smul

/-- info: 'FormalResearch.SignUncertainty.liftW_airySeedU2_lin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftW_airySeedU2_lin

/-- info: 'FormalResearch.SignUncertainty.gt1Bounds_airySeedU2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gt1Bounds_airySeedU2

end FormalResearch.SignUncertainty
