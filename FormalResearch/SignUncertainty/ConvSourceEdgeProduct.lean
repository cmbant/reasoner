module

public import FormalResearch.SignUncertainty.Gt1Interface

/-!
# Leibniz product of a `GT.1` symbol with a Laplace-transform factor (M6, `ceo:conv` (4), `ceo:O11ak`)

`W_{S_c}(iv) = W_{g_1}(iv) · ŵ_c(c_s v)` (`ceo:conv` (3)): the symbol of the convolution source is the `GT.1` symbol of the seed `g_1` times the
Fourier transform of the weight.  This module has only the algebra of the Leibniz step:

* `LapBounds B Λ`: the bounds `(ceo:conv.5)` for a factor `Λ : ℝ → ℂ` on the real line: `|Λ| ≤ B`, `|∂^k Λ| ≤ B |s|^{1/2-k}` for `0 < |s| ≤ 1`,
  `|∂^k Λ| ≤ B |s|^{-k-1}` for `|s| ≥ 1` (`k = 1, 2, 3`), and the `1/2`-Hölder bound at `0`;
* `LapBounds.add`, `LapBounds.smul`: closure;
* `Gt1Bounds.mul_lap`: `Gt1Bounds A U` and `LapBounds B Λ` give `Gt1Bounds (9 A B) (U · Λ)` (class: proved).

The Laplace factor of the actual weight is in `ConvSourceEdgeLap`.
-/

@[expose] public section

open Set

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- **`(ceo:conv.5)` on the real line** for a factor `Λ`: bounded by `B`, three derivatives off `0` with `|Λ^{(k)}| ≤ B |s|^{1/2-k}` for
`0 < |s| ≤ 1`, `|Λ^{(k)}| ≤ B |s|^{-k-1}` for `|s| ≥ 1` (`k = 1, 2, 3`), and `|Λ(s) - Λ(0)| ≤ B |s|^{1/2}` for `0 < |s| ≤ 1`. -/
def LapBounds (B : ℝ) (Λ : ℝ → ℂ) : Prop :=
  ∃ Λ1 Λ2 Λ3 : ℝ → ℂ,
    (∀ s : ℝ, s ≠ 0 → HasDerivAt Λ (Λ1 s) s ∧ HasDerivAt Λ1 (Λ2 s) s ∧ HasDerivAt Λ2 (Λ3 s) s) ∧
    (∀ s : ℝ, ‖Λ s‖ ≤ B) ∧
    (∀ s : ℝ, 0 < |s| → |s| ≤ 1 → ‖Λ1 s‖ ≤ B * |s| ^ (-(1 / 2) : ℝ) ∧ ‖Λ2 s‖ ≤ B * |s| ^ (-(3 / 2) : ℝ) ∧
      ‖Λ3 s‖ ≤ B * |s| ^ (-(5 / 2) : ℝ)) ∧
    (∀ s : ℝ, 1 ≤ |s| → ‖Λ1 s‖ ≤ B * |s| ^ (-2 : ℝ) ∧ ‖Λ2 s‖ ≤ B * |s| ^ (-3 : ℝ) ∧ ‖Λ3 s‖ ≤ B * |s| ^ (-4 : ℝ)) ∧
    (∀ s : ℝ, 0 < |s| → |s| ≤ 1 → ‖Λ s - Λ 0‖ ≤ B * |s| ^ (1 / 2 : ℝ))

theorem LapBounds.nonneg {B : ℝ} {Λ : ℝ → ℂ} (h : LapBounds B Λ) : 0 ≤ B := by
  obtain ⟨_, _, _, _, hb, _⟩ := h
  exact (norm_nonneg _).trans (hb 0)

theorem LapBounds.mono {A B : ℝ} {Λ : ℝ → ℂ} (h : A ≤ B) (hΛ : LapBounds A Λ) : LapBounds B Λ := by
  obtain ⟨Λ1, Λ2, Λ3, hd, hb, hl, hh, hH⟩ := hΛ
  have key : ∀ (t : ℝ) (x : ℂ) (s : ℝ), ‖x‖ ≤ A * |s| ^ t → ‖x‖ ≤ B * |s| ^ t := fun t x s hx =>
    hx.trans (mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (abs_nonneg _) _))
  refine ⟨Λ1, Λ2, Λ3, hd, fun s => (hb s).trans h, fun s hs hs1 => ?_, fun s hs => ?_, fun s hs hs1 => ?_⟩
  · obtain ⟨a, b, c⟩ := hl s hs hs1
    exact ⟨key _ _ _ a, key _ _ _ b, key _ _ _ c⟩
  · obtain ⟨a, b, c⟩ := hh s hs
    exact ⟨key _ _ _ a, key _ _ _ b, key _ _ _ c⟩
  · exact key _ _ _ (hH s hs hs1)

theorem LapBounds.add {A B : ℝ} {Λ Μ : ℝ → ℂ} (hΛ : LapBounds A Λ) (hΜ : LapBounds B Μ) :
    LapBounds (A + B) (fun s => Λ s + Μ s) := by
  obtain ⟨Λ1, Λ2, Λ3, hd, hb, hl, hh, hH⟩ := hΛ
  obtain ⟨Μ1, Μ2, Μ3, hd', hb', hl', hh', hH'⟩ := hΜ
  have comb : ∀ (t : ℝ) (x y : ℂ) (s : ℝ), ‖x‖ ≤ A * |s| ^ t → ‖y‖ ≤ B * |s| ^ t → ‖x + y‖ ≤ (A + B) * |s| ^ t :=
    fun t x y s hx hy => (norm_add_le _ _).trans (by rw [add_mul]; exact add_le_add hx hy)
  refine ⟨fun s => Λ1 s + Μ1 s, fun s => Λ2 s + Μ2 s, fun s => Λ3 s + Μ3 s, fun s hs => ?_,
    fun s => (norm_add_le _ _).trans (add_le_add (hb s) (hb' s)), fun s hs hs1 => ?_, fun s hs => ?_, fun s hs hs1 => ?_⟩
  · exact ⟨(hd s hs).1.add (hd' s hs).1, (hd s hs).2.1.add (hd' s hs).2.1, (hd s hs).2.2.add (hd' s hs).2.2⟩
  · obtain ⟨a, b, c⟩ := hl s hs hs1
    obtain ⟨a', b', c'⟩ := hl' s hs hs1
    exact ⟨comb _ _ _ _ a a', comb _ _ _ _ b b', comb _ _ _ _ c c'⟩
  · obtain ⟨a, b, c⟩ := hh s hs
    obtain ⟨a', b', c'⟩ := hh' s hs
    exact ⟨comb _ _ _ _ a a', comb _ _ _ _ b b', comb _ _ _ _ c c'⟩
  · have := comb (1 / 2 : ℝ) (Λ s - Λ 0) (Μ s - Μ 0) s (hH s hs hs1) (hH' s hs hs1)
    refine le_of_eq_of_le ?_ this
    congr 1; ring

theorem LapBounds.smul {A : ℝ} {Λ : ℝ → ℂ} (t : ℂ) (hΛ : LapBounds A Λ) : LapBounds (‖t‖ * A) (fun s => t * Λ s) := by
  obtain ⟨Λ1, Λ2, Λ3, hd, hb, hl, hh, hH⟩ := hΛ
  have sc : ∀ (e : ℝ) (x : ℂ) (s : ℝ), ‖x‖ ≤ A * |s| ^ e → ‖t * x‖ ≤ ‖t‖ * A * |s| ^ e := fun e x s hx => by
    rw [norm_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  refine ⟨fun s => t * Λ1 s, fun s => t * Λ2 s, fun s => t * Λ3 s, fun s hs => ?_,
    fun s => ?_, fun s hs hs1 => ?_, fun s hs => ?_, fun s hs hs1 => ?_⟩
  · exact ⟨(hd s hs).1.const_mul t, (hd s hs).2.1.const_mul t, (hd s hs).2.2.const_mul t⟩
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hb s) (norm_nonneg _)
  · obtain ⟨a, b, c⟩ := hl s hs hs1
    exact ⟨sc _ _ _ a, sc _ _ _ b, sc _ _ _ c⟩
  · obtain ⟨a, b, c⟩ := hh s hs
    exact ⟨sc _ _ _ a, sc _ _ _ b, sc _ _ _ c⟩
  · have := sc (1 / 2 : ℝ) (Λ s - Λ 0) s (hH s hs hs1)
    refine le_of_eq_of_le ?_ this
    congr 1; ring

private lemma rp_small {t a b : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hab : b ≤ a) : t ^ a ≤ t ^ b :=
  Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hab

private lemma rp_big {t a b : ℝ} (ht1 : 1 ≤ t) (hab : a ≤ b) : t ^ a ≤ t ^ b :=
  Real.rpow_le_rpow_of_exponent_le ht1 hab

private lemma rp_mul {t : ℝ} (ht0 : 0 < t) (a b : ℝ) : t ^ a * t ^ b = t ^ (a + b) :=
  (Real.rpow_add ht0 a b).symm

private lemma nm {x y : ℂ} {a b : ℝ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) : ‖x * y‖ ≤ a * b :=
  (norm_mul_le _ _).trans (mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx))

/-- **The Leibniz step**: `Gt1Bounds A U` and `LapBounds B Λ` give `Gt1Bounds (9 A B) (U · Λ)` (class: proved). -/
theorem Gt1Bounds.mul_lap {A B : ℝ} {U Λ : ℝ → ℂ} (hU : Gt1Bounds A U) (hΛ : LapBounds B Λ) :
    Gt1Bounds (9 * A * B) (fun v => U v * Λ v) := by
  obtain ⟨U1, U2, U3, hUd, hUl, hUh, hU0, hUH⟩ := hU
  obtain ⟨L1, L2, L3, hLd, hLb, hLl, hLh, hLH⟩ := hΛ
  have hA : 0 ≤ A := (norm_nonneg _).trans hU0
  have hB : 0 ≤ B := (norm_nonneg _).trans (hLb 0)
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  refine ⟨fun s => U1 s * Λ s + U s * L1 s, fun s => U2 s * Λ s + 2 * (U1 s * L1 s) + U s * L2 s,
    fun s => U3 s * Λ s + 3 * (U2 s * L1 s) + 3 * (U1 s * L2 s) + U s * L3 s, fun s hs => ?_, fun s hs hs1 => ?_,
    fun s hs => ?_, ?_, fun s hs hs1 => ?_⟩
  · obtain ⟨u1, u2, u3⟩ := hUd s hs
    obtain ⟨l1, l2, l3⟩ := hLd s hs
    refine ⟨u1.mul l1, ?_, ?_⟩
    · exact ((u2.mul l1).add (u1.mul l2)).congr_deriv (by ring)
    · exact (((u3.mul l1).add ((u2.mul l2).const_mul 2)).add (u1.mul l3)).congr_deriv (by ring)
  · -- small `|s| ≤ 1`
    obtain ⟨u1b, u2b, u3b⟩ := hUl s hs hs1
    obtain ⟨l1b, l2b, l3b⟩ := hLl s hs hs1
    have hUb : ‖U s‖ ≤ 2 * A := by
      have h1 : |s| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (abs_nonneg _) hs1 (by norm_num)
      have h2 : ‖U s‖ ≤ ‖U 0‖ + ‖U s - U 0‖ := norm_le_insert' _ _
      have h3 := hUH s hs hs1
      have h4 := mul_le_mul_of_nonneg_left h1 hA
      linarith
    have hΛb := hLb s
    set t : ℝ := |s| with ht
    have p1 : 0 ≤ t ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hs.le _
    have p2 : 0 ≤ t ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hs.le _
    have p3 : 0 ≤ t ^ (-(5 / 2) : ℝ) := Real.rpow_nonneg hs.le _
    have q12 : t ^ (-(1 / 2) : ℝ) ≤ t ^ (-(3 / 2) : ℝ) := rp_small hs hs1 (by norm_num)
    have q23 : t ^ (-(3 / 2) : ℝ) ≤ t ^ (-(5 / 2) : ℝ) := rp_small hs hs1 (by norm_num)
    have m11 : t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) ≤ t ^ (-(5 / 2) : ℝ) := by
      rw [rp_mul hs]; exact rp_small hs hs1 (by norm_num)
    have m11' : t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) ≤ t ^ (-(3 / 2) : ℝ) := by
      rw [rp_mul hs]; exact rp_small hs hs1 (by norm_num)
    have m12 : t ^ (-(1 / 2) : ℝ) * t ^ (-(3 / 2) : ℝ) ≤ t ^ (-(5 / 2) : ℝ) := by
      rw [rp_mul hs]; exact rp_small hs hs1 (by norm_num)
    refine ⟨?_, ?_, ?_⟩
    · have e1 := nm u1b hΛb
      have e2 := nm hUb l1b
      refine (norm_add_le _ _).trans ?_
      linarith [mul_nonneg hAB p1]
    · have e1 := nm u2b hΛb
      have e2 := nm u1b l1b
      have e3 := nm hUb l2b
      have e22 : ‖(2 : ℂ) * (U1 s * L1 s)‖ ≤ 2 * (A * t ^ (-(1 / 2) : ℝ) * (B * t ^ (-(1 / 2) : ℝ))) := by
        rw [norm_mul]; simpa using mul_le_mul_of_nonneg_left e2 (by norm_num : (0 : ℝ) ≤ 2)
      refine (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add e1 e22)) e3).trans ?_)
      have := mul_le_mul_of_nonneg_left m11' hAB
      linarith [mul_nonneg hAB p2, mul_nonneg hAB (mul_nonneg p1 p1)]
    · have e1 := nm u3b hΛb
      have e2 := nm u2b l1b
      have e3 := nm u1b l2b
      have e4 := nm hUb l3b
      have e22 : ‖(3 : ℂ) * (U2 s * L1 s)‖ ≤ 3 * (A * t ^ (-(3 / 2) : ℝ) * (B * t ^ (-(1 / 2) : ℝ))) := by
        rw [norm_mul]; simpa using mul_le_mul_of_nonneg_left e2 (by norm_num : (0 : ℝ) ≤ 3)
      have e33 : ‖(3 : ℂ) * (U1 s * L2 s)‖ ≤ 3 * (A * t ^ (-(1 / 2) : ℝ) * (B * t ^ (-(3 / 2) : ℝ))) := by
        rw [norm_mul]; simpa using mul_le_mul_of_nonneg_left e3 (by norm_num : (0 : ℝ) ≤ 3)
      have m21 : t ^ (-(3 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) ≤ t ^ (-(5 / 2) : ℝ) := by
        rw [rp_mul hs]; exact rp_small hs hs1 (by norm_num)
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add e1 e22)) e33)) e4 |>.trans ?_)
      have h21 := mul_le_mul_of_nonneg_left m21 hAB
      have h12 := mul_le_mul_of_nonneg_left m12 hAB
      linarith [mul_nonneg hAB p3]
  · -- large `|s| ≥ 1`
    obtain ⟨u0b, u1b, u2b, u3b⟩ := hUh s hs
    obtain ⟨l1b, l2b, l3b⟩ := hLh s hs
    have hΛb := hLb s
    have hs0 : 0 < |s| := lt_of_lt_of_le one_pos hs
    set t : ℝ := |s| with ht
    have p1 : 0 ≤ t ^ (-(5 / 2) : ℝ) := Real.rpow_nonneg hs0.le _
    have p2 : 0 ≤ t ^ (-(7 / 2) : ℝ) := Real.rpow_nonneg hs0.le _
    have p3 : 0 ≤ t ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg hs0.le _
    have p4 : 0 ≤ t ^ (-(11 / 2) : ℝ) := Real.rpow_nonneg hs0.le _
    refine ⟨?_, ?_, ?_, ?_⟩
    · have e1 := nm u0b hΛb
      linarith [mul_nonneg hAB p1]
    · have e1 := nm u1b hΛb
      have e2 := nm u0b l1b
      have m1 : t ^ (-(5 / 2) : ℝ) * t ^ (-2 : ℝ) ≤ t ^ (-(7 / 2) : ℝ) := by
        rw [rp_mul hs0]; exact rp_big hs (by norm_num)
      refine (norm_add_le _ _).trans (add_le_add e1 e2 |>.trans ?_)
      have h1 := mul_le_mul_of_nonneg_left m1 hAB
      linarith [mul_nonneg hAB p2]
    · have e1 := nm u2b hΛb
      have e2 := nm u1b l1b
      have e3 := nm u0b l2b
      have e22 : ‖(2 : ℂ) * (U1 s * L1 s)‖ ≤ 2 * (A * t ^ (-(7 / 2) : ℝ) * (B * t ^ (-2 : ℝ))) := by
        rw [norm_mul]; simpa using mul_le_mul_of_nonneg_left e2 (by norm_num : (0 : ℝ) ≤ 2)
      have m1 : t ^ (-(7 / 2) : ℝ) * t ^ (-2 : ℝ) ≤ t ^ (-(9 / 2) : ℝ) := by
        rw [rp_mul hs0]; exact rp_big hs (by norm_num)
      have m2 : t ^ (-(5 / 2) : ℝ) * t ^ (-3 : ℝ) ≤ t ^ (-(9 / 2) : ℝ) := by
        rw [rp_mul hs0]; exact rp_big hs (by norm_num)
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add e1 e22)) e3 |>.trans ?_)
      have h1 := mul_le_mul_of_nonneg_left m1 hAB
      have h2 := mul_le_mul_of_nonneg_left m2 hAB
      linarith [mul_nonneg hAB p3]
    · have e1 := nm u3b hΛb
      have e2 := nm u2b l1b
      have e3 := nm u1b l2b
      have e4 := nm u0b l3b
      have e22 : ‖(3 : ℂ) * (U2 s * L1 s)‖ ≤ 3 * (A * t ^ (-(9 / 2) : ℝ) * (B * t ^ (-2 : ℝ))) := by
        rw [norm_mul]; simpa using mul_le_mul_of_nonneg_left e2 (by norm_num : (0 : ℝ) ≤ 3)
      have e33 : ‖(3 : ℂ) * (U1 s * L2 s)‖ ≤ 3 * (A * t ^ (-(7 / 2) : ℝ) * (B * t ^ (-3 : ℝ))) := by
        rw [norm_mul]; simpa using mul_le_mul_of_nonneg_left e3 (by norm_num : (0 : ℝ) ≤ 3)
      have m1 : t ^ (-(9 / 2) : ℝ) * t ^ (-2 : ℝ) ≤ t ^ (-(11 / 2) : ℝ) := by
        rw [rp_mul hs0]; exact rp_big hs (by norm_num)
      have m2 : t ^ (-(7 / 2) : ℝ) * t ^ (-3 : ℝ) ≤ t ^ (-(11 / 2) : ℝ) := by
        rw [rp_mul hs0]; exact rp_big hs (by norm_num)
      have m3 : t ^ (-(5 / 2) : ℝ) * t ^ (-4 : ℝ) ≤ t ^ (-(11 / 2) : ℝ) := by
        rw [rp_mul hs0]; exact rp_big hs (by norm_num)
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add e1 e22)) e33)) e4 |>.trans ?_)
      have h1 := mul_le_mul_of_nonneg_left m1 hAB
      have h2 := mul_le_mul_of_nonneg_left m2 hAB
      have h3 := mul_le_mul_of_nonneg_left m3 hAB
      linarith [mul_nonneg hAB p4]
  · rw [norm_mul]
    have := mul_le_mul hU0 (hLb 0) (norm_nonneg _) hA
    linarith
  · have h1 := hUH s hs hs1
    have h2 := hLH s hs hs1
    have hUs : ‖U 0‖ ≤ A := hU0
    have e1 := nm h1 (hLb s)
    have e2 := nm hUs h2
    have hsp : (U s * Λ s - U 0 * Λ 0) = (U s - U 0) * Λ s + U 0 * (Λ s - Λ 0) := by ring
    rw [hsp]
    refine (norm_add_le _ _).trans (add_le_add e1 e2 |>.trans ?_)
    linarith [mul_nonneg hAB (Real.rpow_nonneg (abs_nonneg s) (1 / 2 : ℝ))]

/-- info: 'FormalResearch.SignUncertainty.Gt1Bounds.mul_lap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Gt1Bounds.mul_lap

end FormalResearch.SignUncertainty
