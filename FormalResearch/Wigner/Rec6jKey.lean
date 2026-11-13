module

public import Mathlib

/-!
# Reduced polynomial identity behind the `6j` recurrence

`Q6` is the quadratic (in the summation index `t`) of the telescoping certificate for the
three-term recurrence of Racah's `6j` sum in the first argument `f` (DLMF 34.5.11).  It is
defined in the symmetric variables of the seven linear forms below (`Q6sym`); expanded in the spins
and `t` it is the explicit polynomial with about `400` monomials.
`rec6_key` is the polynomial identity left after cancelling the common factor `(a₃+1)(a₄+1)` of
all five summand-like products.  It is stated with the seven linear forms
`a₁ = t-f-j₂-j₃`, `a₂ = t-f-l₂-l₃`, `a₃ = t-l₁-j₂-l₃`, `a₄ = t-l₁-l₂-j₃`,
`b₁ = f+j₂+l₁+l₂-t`, `b₂ = j₂+j₃+l₂+l₃-t`, `b₃ = j₃+f+l₃+l₁-t` as separate variables; the
spins and `t` are linear combinations of them.  The identity is symmetric under `a₁ ↔ a₂`,
`a₃ ↔ a₄`, `b₁ ↔ b₃`, so it is proved (`rec6_key_sym`) in the symmetric functions of these pairs, and each
factor is bridged to those variables by a small `subst; ring` lemma.
-/

@[expose] public section

namespace FormalResearch.Wigner

/-- The quadratic of the telescoping certificate of the `6j` recurrence, in the symmetric
variables `s = a₁+a₂`, `p = a₁a₂`, `u = a₃+a₄`, `v = a₃a₄`, `w = b₁+b₃+2`, `z = (b₁+1)(b₃+1)`,
`y = b₂+1` of its seven linear forms. -/
noncomputable def Q6sym (s p u v w z y : ℝ) : ℝ :=
  (p * ((u + w - 2) * (w * (u + w) + v) + 2 * z) + z * (u + w) * (u + w + y - 2) * (s + y)) / 2

/-- The quadratic of the telescoping certificate of the `6j` recurrence. -/
noncomputable def Q6 (f j₂ j₃ l₁ l₂ l₃ t : ℝ) : ℝ :=
  Q6sym ((t - f - j₂ - j₃) + (t - f - l₂ - l₃)) ((t - f - j₂ - j₃) * (t - f - l₂ - l₃))
    ((t - l₁ - j₂ - l₃) + (t - l₁ - l₂ - j₃)) ((t - l₁ - j₂ - l₃) * (t - l₁ - l₂ - j₃))
    ((f + j₂ + l₁ + l₂ - t) + (j₃ + f + l₃ + l₁ - t) + 2)
    (((f + j₂ + l₁ + l₂ - t) + 1) * ((j₃ + f + l₃ + l₁ - t) + 1)) ((j₂ + j₃ + l₂ + l₃ - t) + 1)

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ### Symmetric reduction

All five summand-like products and `Q6` are symmetric under `a₁ ↔ a₂`, `a₃ ↔ a₄`, `b₁ ↔ b₃`, so the
identity is a polynomial identity in the symmetric functions `s = a₁+a₂`, `p = a₁a₂`, `u = a₃+a₄`,
`v = a₃a₄`, `w = b₁+b₃+2`, `z = (b₁+1)(b₃+1)`, `y = b₂+1` (`rec6_key_sym`).  Each factor of
`rec6_key` is bridged to these variables by a small `subst; ring` lemma. -/

/-- The spin polynomial multiplying the first product, in the symmetric variables. -/
noncomputable def K6sym (s p u v w z y : ℝ) : ℝ :=
  (u + w - 1) * (
    p*u^2 + p*u*w - p*u - 2*p*v - p*w + 2*p*z - s*u*v - s*u*w*y + s*u*y + s*u*z - s*v*w - 2*s*v*y
    + 2*s*v - s*w^2*y + s*w*y + s*w*z + 2*s*y*z - 2*s*z - u^2*w*y + u^2*y + u^2*z - 2*u*v*y + u*v
    - 2*u*w^2*y - u*w*y^2 + 4*u*w*y + 2*u*w*z + u*y^2 + 2*u*y*z - 2*u*y - 3*u*z - 2*v*w*y + v*w
    - 2*v*y^2 + 4*v*y - 2*v - w^3*y - w^2*y^2 + 3*w^2*y + w^2*z + w*y^2 + 2*w*y*z - 2*w*y - 3*w*z
    + 2*y^2*z - 4*y*z + 2*z) / 2

/-- The spin polynomial multiplying the second product. -/
noncomputable def B6sym (s p u v w z y : ℝ) : ℝ :=
  (u + w - 2) * (v^2 + v*w*u + z*(u^2 - 2*v) + w^2*v + w*z*u + z^2) / 2

/-- The spin polynomial multiplying the third product. -/
noncomputable def C6sym (s p u v w z y : ℝ) : ℝ :=
  (u + w) * (p + s*y + y^2) * (p + s*(u + w + y - 2) + (u + w + y - 2)^2) / 2

lemma rec6_key_sym (s p u v w z y : ℝ) :
    K6sym s p u v w z y * ((p + s + 1) * z) - B6sym s p u v w z y * (p * (p + s + 1))
      - C6sym s p u v w z y * ((z - w + 1) * z)
      + (s + u + w + y - 1) * Q6sym (s + 2) (p + s + 1) (u + 2) (v + u + 1) (w - 2) (z - w + 1) (y - 1) *
          ((y - 1) * z)
      + v * (p + s + 1) * Q6sym s p u v w z y = 0 := by
  unfold K6sym B6sym C6sym Q6sym
  ring

section bridge

variable (t f j₂ j₃ l₁ l₂ l₃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ s p u v w z y : ℝ)
  (ha₁ : a₁ = t - f - j₂ - j₃) (ha₂ : a₂ = t - f - l₂ - l₃) (ha₃ : a₃ = t - l₁ - j₂ - l₃)
  (ha₄ : a₄ = t - l₁ - l₂ - j₃) (hb₁ : b₁ = f + j₂ + l₁ + l₂ - t)
  (hb₂ : b₂ = j₂ + j₃ + l₂ + l₃ - t) (hb₃ : b₃ = j₃ + f + l₃ + l₁ - t)
  (hs : s = a₁ + a₂) (hp : p = a₁ * a₂) (hu : u = a₃ + a₄) (hv : v = a₃ * a₄)
  (hw : w = b₁ + b₃ + 2) (hz : z = (b₁ + 1) * (b₃ + 1)) (hy : y = b₂ + 1)

include ha₁ ha₂ ha₃ ha₄ hb₁ hb₂ hb₃ hs hp hu hv hw hz hy in
lemma rec6k_Q0 : Q6 f j₂ j₃ l₁ l₂ l₃ t = Q6sym s p u v w z y := by
  unfold Q6
  subst hs hp hu hv hw hz hy ha₁ ha₂ ha₃ ha₄ hb₁ hb₂ hb₃
  rfl

include ha₁ ha₂ ha₃ ha₄ hb₁ hb₂ hb₃ hs hp hu hv hw hz hy in
lemma rec6k_Q1 : Q6 f j₂ j₃ l₁ l₂ l₃ (t + 1) =
    Q6sym (s + 2) (p + s + 1) (u + 2) (v + u + 1) (w - 2) (z - w + 1) (y - 1) := by
  unfold Q6
  subst hs hp hu hv hw hz hy ha₁ ha₂ ha₃ ha₄ hb₁ hb₂ hb₃
  congr 1 <;> ring

include ha₁ ha₂ ha₃ ha₄ hb₁ hb₂ hb₃ hs hu hw hy in
lemma rec6k_t : t + 2 = s + u + w + y - 1 := by
  subst hs hu hw hy ha₁ ha₂ ha₃ ha₄ hb₁ hb₂ hb₃
  ring

variable (hf : f = (a₃ + a₄ + b₁ + b₃) / 2) (hj₂ : j₂ = (a₂ + a₄ + b₁ + b₂) / 2)
  (hj₃ : j₃ = (a₂ + a₃ + b₂ + b₃) / 2) (hl₁ : l₁ = (a₁ + a₂ + b₁ + b₃) / 2)
  (hl₂ : l₂ = (a₁ + a₃ + b₁ + b₂) / 2) (hl₃ : l₃ = (a₁ + a₄ + b₂ + b₃) / 2)

include hf hj₂ hj₃ hl₁ hl₂ hl₃ hs hp hu hv hw hz hy in
lemma rec6k_C1 :
    (2 * f + 1) *
          (((j₃ * (j₃ + 1) + j₂ * (j₂ + 1) - f * (f + 1)) *
              (l₃ * (l₃ + 1) + l₂ * (l₂ + 1) - f * (f + 1))) -
            2 * (j₃ * (j₃ + 1) * (l₃ * (l₃ + 1)) + j₂ * (j₂ + 1) * (l₂ * (l₂ + 1)) -
              f * (f + 1) * (l₁ * (l₁ + 1)))) = K6sym s p u v w z y := by
  unfold K6sym
  subst hs hp hu hv hw hz hy hf hj₂ hj₃ hl₁ hl₂ hl₃
  ring

include hf hj₂ hj₃ hl₁ hl₂ hl₃ hs hp hu hv hw hz hy in
lemma rec6k_C2 :
    f * ((f + 1 + j₂ - j₃) * (f + 1 - j₂ + j₃) * (f + 1 + l₂ - l₃) * (f + 1 - l₂ + l₃)) =
      B6sym s p u v w z y := by
  have e1 : f + 1 + j₂ - j₃ = a₄ + b₁ + 1 := by subst hf hj₂ hj₃; ring
  have e2 : f + 1 - j₂ + j₃ = a₃ + b₃ + 1 := by subst hf hj₂ hj₃; ring
  have e3 : f + 1 + l₂ - l₃ = a₃ + b₁ + 1 := by subst hf hl₂ hl₃; ring
  have e4 : f + 1 - l₂ + l₃ = a₄ + b₃ + 1 := by subst hf hl₂ hl₃; ring
  have e5 : f = (u + w - 2) / 2 := by subst hu hw hf; ring
  rw [e1, e2, e3, e4, e5]
  unfold B6sym
  subst hu hv hw hz
  ring

include hf hj₂ hj₃ hl₁ hl₂ hl₃ hs hp hu hv hw hz hy in
lemma rec6k_C3 :
    (f + 1) * ((j₂ + j₃ + 1 - f) * (j₂ + j₃ + 1 + f) * (l₂ + l₃ + 1 - f) * (l₂ + l₃ + 1 + f)) =
      C6sym s p u v w z y := by
  have e1 : j₂ + j₃ + 1 - f = a₂ + y := by subst hy hf hj₂ hj₃; ring
  have e2 : j₂ + j₃ + 1 + f = a₂ + (u + w + y - 2) := by subst hu hw hy hf hj₂ hj₃; ring
  have e3 : l₂ + l₃ + 1 - f = a₁ + y := by subst hy hf hl₂ hl₃; ring
  have e4 : l₂ + l₃ + 1 + f = a₁ + (u + w + y - 2) := by subst hu hw hy hf hl₂ hl₃; ring
  have e5 : f + 1 = (u + w) / 2 := by subst hu hw hf; ring
  rw [e1, e2, e3, e4, e5]
  unfold C6sym
  subst hs hp
  ring

end bridge

lemma rec6k_X1 (a₁ a₂ b₁ b₃ s p z : ℝ) (hs : s = a₁ + a₂) (hp : p = a₁ * a₂)
    (hz : z = (b₁ + 1) * (b₃ + 1)) :
    (a₁ + 1) * (a₂ + 1) * (b₁ + 1) * (b₃ + 1) = (p + s + 1) * z := by
  subst hs hp hz; ring

lemma rec6k_X2 (a₁ a₂ s p : ℝ) (hs : s = a₁ + a₂) (hp : p = a₁ * a₂) :
    a₁ * (a₁ + 1) * a₂ * (a₂ + 1) = p * (p + s + 1) := by
  subst hs hp; ring

lemma rec6k_X3 (b₁ b₃ w z : ℝ) (hw : w = b₁ + b₃ + 2) (hz : z = (b₁ + 1) * (b₃ + 1)) :
    b₁ * (b₁ + 1) * b₃ * (b₃ + 1) = (z - w + 1) * z := by
  subst hw hz; ring

lemma rec6k_X4 (b₁ b₂ b₃ z y : ℝ) (hy : y = b₂ + 1) (hz : z = (b₁ + 1) * (b₃ + 1)) :
    b₂ * (b₁ + 1) * (b₃ + 1) = (y - 1) * z := by
  subst hy hz; ring

lemma rec6k_X5 (a₁ a₂ a₃ a₄ s p u v : ℝ) (hs : s = a₁ + a₂) (hp : p = a₁ * a₂) (hv : v = a₃ * a₄) :
    a₃ * a₄ * ((a₁ + 1) * (a₂ + 1)) = v * (p + s + 1) := by
  subst hs hp hv; ring

/-- The reduced polynomial identity behind the `6j` recurrence. -/
lemma rec6_key (t f j₂ j₃ l₁ l₂ l₃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ : ℝ)
    (ha₁ : a₁ = t - f - j₂ - j₃) (ha₂ : a₂ = t - f - l₂ - l₃) (ha₃ : a₃ = t - l₁ - j₂ - l₃)
    (ha₄ : a₄ = t - l₁ - l₂ - j₃) (hb₁ : b₁ = f + j₂ + l₁ + l₂ - t)
    (hb₂ : b₂ = j₂ + j₃ + l₂ + l₃ - t) (hb₃ : b₃ = j₃ + f + l₃ + l₁ - t) :
    (2 * f + 1) *
          (((j₃ * (j₃ + 1) + j₂ * (j₂ + 1) - f * (f + 1)) *
              (l₃ * (l₃ + 1) + l₂ * (l₂ + 1) - f * (f + 1))) -
            2 * (j₃ * (j₃ + 1) * (l₃ * (l₃ + 1)) + j₂ * (j₂ + 1) * (l₂ * (l₂ + 1)) -
              f * (f + 1) * (l₁ * (l₁ + 1)))) *
        ((a₁ + 1) * (a₂ + 1) * (b₁ + 1) * (b₃ + 1))
      - f * ((f + 1 + j₂ - j₃) * (f + 1 - j₂ + j₃) * (f + 1 + l₂ - l₃) * (f + 1 - l₂ + l₃)) *
        (a₁ * (a₁ + 1) * a₂ * (a₂ + 1))
      - (f + 1) * ((j₂ + j₃ + 1 - f) * (j₂ + j₃ + 1 + f) * (l₂ + l₃ + 1 - f) * (l₂ + l₃ + 1 + f)) *
        (b₁ * (b₁ + 1) * b₃ * (b₃ + 1))
      + (t + 2) * Q6 f j₂ j₃ l₁ l₂ l₃ (t + 1) * (b₂ * (b₁ + 1) * (b₃ + 1))
      + a₃ * a₄ * ((a₁ + 1) * (a₂ + 1)) * Q6 f j₂ j₃ l₁ l₂ l₃ t = 0 := by
  have hf : f = (a₃ + a₄ + b₁ + b₃) / 2 := by rw [ha₃, ha₄, hb₁, hb₃]; ring
  have hj₂ : j₂ = (a₂ + a₄ + b₁ + b₂) / 2 := by rw [ha₂, ha₄, hb₁, hb₂]; ring
  have hj₃ : j₃ = (a₂ + a₃ + b₂ + b₃) / 2 := by rw [ha₂, ha₃, hb₂, hb₃]; ring
  have hl₁ : l₁ = (a₁ + a₂ + b₁ + b₃) / 2 := by rw [ha₁, ha₂, hb₁, hb₃]; ring
  have hl₂ : l₂ = (a₁ + a₃ + b₁ + b₂) / 2 := by rw [ha₁, ha₃, hb₁, hb₂]; ring
  have hl₃ : l₃ = (a₁ + a₄ + b₂ + b₃) / 2 := by rw [ha₁, ha₄, hb₂, hb₃]; ring
  obtain ⟨s, hs⟩ : ∃ s, s = a₁ + a₂ := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = a₁ * a₂ := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = a₃ + a₄ := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = a₃ * a₄ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = b₁ + b₃ + 2 := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = (b₁ + 1) * (b₃ + 1) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = b₂ + 1 := ⟨_, rfl⟩
  rw [rec6k_C1 f j₂ j₃ l₁ l₂ l₃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ s p u v w z y hs hp hu hv hw hz hy hf hj₂ hj₃ hl₁ hl₂ hl₃,
    rec6k_C2 f j₂ j₃ l₁ l₂ l₃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ s p u v w z y hs hp hu hv hw hz hy hf hj₂ hj₃ hl₁ hl₂ hl₃,
    rec6k_C3 f j₂ j₃ l₁ l₂ l₃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ s p u v w z y hs hp hu hv hw hz hy hf hj₂ hj₃ hl₁ hl₂ hl₃,
    rec6k_Q1 t f j₂ j₃ l₁ l₂ l₃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ s p u v w z y ha₁ ha₂ ha₃ ha₄ hb₁ hb₂ hb₃ hs hp hu hv hw hz hy,
    rec6k_Q0 t f j₂ j₃ l₁ l₂ l₃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ s p u v w z y ha₁ ha₂ ha₃ ha₄ hb₁ hb₂ hb₃ hs hp hu hv hw hz hy,
    rec6k_t t f j₂ j₃ l₁ l₂ l₃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ s u w y ha₁ ha₂ ha₃ ha₄ hb₁ hb₂ hb₃ hs hu hw hy,
    rec6k_X1 a₁ a₂ b₁ b₃ s p z hs hp hz, rec6k_X2 a₁ a₂ s p hs hp,
    rec6k_X3 b₁ b₃ w z hw hz, rec6k_X4 b₁ b₂ b₃ z y hy hz, rec6k_X5 a₁ a₂ a₃ a₄ s p u v hs hp hv]
  exact rec6_key_sym s p u v w z y

end FormalResearch.Wigner
