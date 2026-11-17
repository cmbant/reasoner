module

public import Mathlib

/-!
# The adiabatic invariant of `f'' = -w² f` and its exact second-order corrections

For functions `f, g = f', w` with `g' = -w² f` and `w' = -x/w` (so `w² = L - x²`, the Weber equation `f'' = (x² - L) f` in the
oscillatory region), the quantity
`T = w f² + g²/w` is the (squared) WKB amplitude: `T' = γ (g² - w² f²)` with `γ = x/w³`.  Pointwise exact identities (all
checked symbolically, `sympy`, scratch, and proved here by `field_simp; ring`):

* `U = T - γ f g + (γ'/2) f²` has `U' = (γ''/2) f²` (`hasDerivAt_invU`), where `γ' = w⁻³ + 3x² w⁻⁵`, `γ'' = 9x w⁻⁵ + 15 x³ w⁻⁷`;
  so `U` differs from `T` by `O(γ) T` and moves by `O(∫ γ'' w⁻¹) T`: **`T` is constant to second order**;
* `f² = T/(2w) + R' - (ρ/2) f²` with `R = -f g/(2w²) + x f²/(2w⁴)`, `ρ = w⁻⁴ + 4x² w⁻⁶` (`mass_identity`): the mass of `f` on an
  interval is half of `∫ T/w` up to boundary terms.

This module holds only the generic calculus; the estimates on the Hermite bulk are in `HermiteKappaBulk`.
**Claim class: proved** (exact identities).
-/

@[expose] public section

open Real

namespace FormalResearch.Special

/-- The WKB amplitude `T = w f² + g²/w`. -/
noncomputable def invT (w f g : ℝ → ℝ) (y : ℝ) : ℝ := w y * f y ^ 2 + g y ^ 2 / w y
/-- `γ = x/w³`. -/
noncomputable def invGam (w : ℝ → ℝ) (y : ℝ) : ℝ := y / w y ^ 3
/-- `γ' = w⁻³ + 3x² w⁻⁵`. -/
noncomputable def invGam1 (w : ℝ → ℝ) (y : ℝ) : ℝ := 1 / w y ^ 3 + 3 * y ^ 2 / w y ^ 5
/-- `γ'' = 9x w⁻⁵ + 15x³ w⁻⁷`. -/
noncomputable def invGam2 (w : ℝ → ℝ) (y : ℝ) : ℝ := 9 * y / w y ^ 5 + 15 * y ^ 3 / w y ^ 7
/-- The corrected invariant `U = T - γ f g + γ' f²/2`. -/
noncomputable def invU (w f g : ℝ → ℝ) (y : ℝ) : ℝ :=
  invT w f g y - invGam w y * f y * g y + invGam1 w y * f y ^ 2 / 2
/-- `R = -f g/(2w²) + x f²/(2w⁴)`. -/
noncomputable def invR (w f g : ℝ → ℝ) (y : ℝ) : ℝ := -(f y * g y) / (2 * w y ^ 2) + y * f y ^ 2 / (2 * w y ^ 4)
/-- `ρ = w⁻⁴ + 4x² w⁻⁶`. -/
noncomputable def invRho (w : ℝ → ℝ) (y : ℝ) : ℝ := 1 / w y ^ 4 + 4 * y ^ 2 / w y ^ 6
/-- `Γ₂ = (2s/5) w⁻⁵ + c x`, a primitive majorant of `ρ/(2w)` (for `x ≤ s`, `w⁻⁵ ≤ 2c`). -/
noncomputable def invBig2 (s c : ℝ) (w : ℝ → ℝ) (y : ℝ) : ℝ := 2 * s / 5 / w y ^ 5 + c * y
/-- `Γ = (9/8) w⁻⁴ + (5/4) L w⁻⁶`, a primitive majorant of `γ''/(2w)`. -/
noncomputable def invBig (L : ℝ) (w : ℝ → ℝ) (y : ℝ) : ℝ := 9 / 8 / w y ^ 4 + 5 / 4 * L / w y ^ 6

section deriv

variable {f g w : ℝ → ℝ} {x : ℝ}

/-- Hypotheses at a point: `f' = g`, `g' = -w² f`, `w' = -x/w`, `w ≠ 0`. -/
structure InvAt (f g w : ℝ → ℝ) (x : ℝ) : Prop where
  hf : HasDerivAt f (g x) x
  hg : HasDerivAt g (-(w x ^ 2) * f x) x
  hw : HasDerivAt w (-x / w x) x
  w0 : w x ≠ 0

lemma InvAt.hasDerivAt_wpow (h : InvAt f g w x) (k : ℕ) :
    HasDerivAt (fun y => w y ^ k) ((k : ℝ) * w x ^ (k - 1) * (-x / w x)) x := h.hw.pow k

lemma InvAt.hasDerivAt_T (h : InvAt f g w x) :
    HasDerivAt (invT w f g) (invGam w x * (g x ^ 2 - w x ^ 2 * f x ^ 2)) x := by
  have h1 := h.hw.mul ((h.hf).mul (h.hf))
  have h2 := ((h.hg).mul (h.hg)).div h.hw h.w0
  have := h1.add h2
  have e : invT w f g = fun y => w y * (f y * f y) + (g y * g y) / w y := by
    funext y; simp only [invT]; ring
  rw [e]
  refine this.congr_deriv ?_
  have := h.w0
  simp only [invGam, Pi.mul_apply]
  field_simp
  ring

lemma InvAt.hasDerivAt_Gam (h : InvAt f g w x) : HasDerivAt (invGam w) (invGam1 w x) x := by
  have h3 := h.hasDerivAt_wpow 3
  have := (hasDerivAt_id x).div h3 (pow_ne_zero 3 h.w0)
  have e : invGam w = fun y => id y / w y ^ 3 := by funext y; simp [invGam]
  rw [e]
  refine this.congr_deriv ?_
  have := h.w0
  simp only [invGam1, id]
  field_simp
  ring

lemma InvAt.hasDerivAt_Gam1 (h : InvAt f g w x) : HasDerivAt (invGam1 w) (invGam2 w x) x := by
  have h3 := h.hasDerivAt_wpow 3
  have h5 := h.hasDerivAt_wpow 5
  have a1 := (hasDerivAt_const x (1 : ℝ)).div h3 (pow_ne_zero 3 h.w0)
  have a2 := (((hasDerivAt_id x).pow 2).const_mul 3).div h5 (pow_ne_zero 5 h.w0)
  have := a1.add a2
  have e : invGam1 w = fun y => (fun _ => (1 : ℝ)) y / w y ^ 3 + (3 * id y ^ 2) / w y ^ 5 := by
    funext y; simp [invGam1]
  rw [e]
  refine this.congr_deriv ?_
  have := h.w0
  simp only [invGam2, id]
  try simp only [Pi.pow_apply, id]
  field_simp
  ring

lemma InvAt.hasDerivAt_U (h : InvAt f g w x) :
    HasDerivAt (invU w f g) (invGam2 w x * f x ^ 2 / 2) x := by
  have hT := h.hasDerivAt_T
  have hG := h.hasDerivAt_Gam
  have hG1 := h.hasDerivAt_Gam1
  have a1 := (hG.mul h.hf).mul h.hg
  have a2 := (hG1.mul (h.hf.mul h.hf)).div_const 2
  have := (hT.sub a1).add a2
  have e : invU w f g = fun y => invT w f g y - invGam w y * f y * g y +
      invGam1 w y * (f y * f y) / 2 := by
    funext y; simp only [invU]; ring
  rw [e]
  refine this.congr_deriv ?_
  have := h.w0
  simp only [invGam, invGam1, invGam2, Pi.mul_apply]
  field_simp
  ring

/-- The mass identity, differentiated: `R' = f² - T/(2w) + (ρ/2) f²`. -/
lemma InvAt.hasDerivAt_R (h : InvAt f g w x) :
    HasDerivAt (invR w f g) (f x ^ 2 - invT w f g x / (2 * w x) + invRho w x * f x ^ 2 / 2) x := by
  have w2 : HasDerivAt (fun y => w y ^ 2) (((2 : ℕ) : ℝ) * w x ^ (2 - 1) * (-x / w x)) x := h.hasDerivAt_wpow 2
  have w4 : HasDerivAt (fun y => w y ^ 4) (((4 : ℕ) : ℝ) * w x ^ (4 - 1) * (-x / w x)) x := h.hasDerivAt_wpow 4
  have a1 := (((h.hf.mul h.hg)).neg).div (w2.const_mul 2) (by have := h.w0; positivity)
  have a2 := (((hasDerivAt_id x).mul (h.hf.mul h.hf))).div (w4.const_mul 2) (by have := h.w0; positivity)
  have := a1.add a2
  have e : invR w f g = fun y => (-(f y * g y)) / (2 * w y ^ 2) + (id y * (f y * f y)) / (2 * w y ^ 4) := by
    funext y; simp only [invR, id]; ring
  rw [e]
  refine this.congr_deriv ?_
  have := h.w0
  simp only [invT, invRho, id]
  try simp only [Pi.mul_apply, Pi.neg_apply, id]
  field_simp
  ring

lemma InvAt.hasDerivAt_Big (L : ℝ) (h : InvAt f g w x) :
    HasDerivAt (invBig L w) (3 * x * (5 * L + 3 * w x ^ 2) / (2 * w x ^ 8)) x := by
  have w4 := h.hasDerivAt_wpow 4
  have w6 := h.hasDerivAt_wpow 6
  have a1 := (hasDerivAt_const x (9 / 8 : ℝ)).div w4 (pow_ne_zero 4 h.w0)
  have a2 := (hasDerivAt_const x (5 / 4 * L : ℝ)).div w6 (pow_ne_zero 6 h.w0)
  have := a1.add a2
  have e : invBig L w = fun y => (fun _ => (9 / 8 : ℝ)) y / w y ^ 4 + (fun _ => (5 / 4 * L : ℝ)) y / w y ^ 6 := by
    funext y; simp [invBig]
  rw [e]
  refine this.congr_deriv ?_
  have := h.w0
  field_simp
  ring

lemma InvAt.hasDerivAt_Big2 (s c : ℝ) (h : InvAt f g w x) :
    HasDerivAt (invBig2 s c w) (2 * s * x / w x ^ 7 + c) x := by
  have w5 := h.hasDerivAt_wpow 5
  have a1 := (hasDerivAt_const x (2 * s / 5 : ℝ)).div w5 (pow_ne_zero 5 h.w0)
  have a2 := (hasDerivAt_id x).const_mul c
  have := a1.add a2
  have e : invBig2 s c w = fun y => (fun _ => (2 * s / 5 : ℝ)) y / w y ^ 5 + c * id y := by
    funext y; simp [invBig2]
  rw [e]
  refine this.congr_deriv ?_
  have := h.w0
  field_simp
  ring

end deriv

end FormalResearch.Special
