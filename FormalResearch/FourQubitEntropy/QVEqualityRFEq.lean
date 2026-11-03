module

public import FormalResearch.FourQubitEntropy.QVEqualityCore

/-!
# Equality case of `prop:fqe-critical-variance` (RF): the real-algebra core

Paper E, `renyi_compatibility.tex`.  For `0 < s < 1` equality `F = (3/2)s² - s³` in (RF) forces
`X = Y = s²` and both `A = (m_i²)` and `B = (n_i²)` to be rearrangements of `((1+2s)/3, (1-s)/3, (1-s)/3)`
(the upper sign of the cubic discriminant identity, `triple_structure`), and `κ > 0`
(`rf_equality_core`).
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.QVEquality

/-- A nonnegative-triple version: `a = b` case of the structure of the equality in `rp_bound`. -/
theorem triple_structure_aux {a b c r : ℝ} (hs : a + b + c = 1) (hr : 0 < r)
    (hX : r ^ 2 = 1 - 3 * (a * b + a * c + b * c)) (h27 : 27 * (a * b * c) = gfun r) (hab : a = b) :
    a = (1 - r) / 3 ∧ b = (1 - r) / 3 ∧ c = (1 + 2 * r) / 3 := by
  subst hab
  have hc : c = 1 - 2 * a := by linarith
  subst hc
  have h1 : (r - (1 - 3 * a)) * (r + (1 - 3 * a)) = 0 := by nlinarith
  rcases mul_eq_zero.mp h1 with h | h
  · have ha : a = (1 - r) / 3 := by linarith
    refine ⟨ha, ha, by rw [ha]; ring⟩
  · exfalso
    have ha : a = (1 + r) / 3 := by linarith
    subst ha
    unfold gfun at h27
    nlinarith [pow_pos hr 3]

/-- **Structure of equality in `rp_bound`** for `r > 0`: the triple is a rearrangement of
`((1+2r)/3, (1-r)/3, (1-r)/3)`. -/
theorem triple_structure {a b c r : ℝ} (hs : a + b + c = 1) (hr : 0 < r)
    (hX : r ^ 2 = 1 - 3 * (a * b + a * c + b * c)) (h27 : 27 * (a * b * c) = gfun r) :
    (a = (1 + 2 * r) / 3 ∧ b = (1 - r) / 3 ∧ c = (1 - r) / 3) ∨
    (a = (1 - r) / 3 ∧ b = (1 + 2 * r) / 3 ∧ c = (1 - r) / 3) ∨
    (a = (1 - r) / 3 ∧ b = (1 - r) / 3 ∧ c = (1 + 2 * r) / 3) := by
  have hc' : c = 1 - a - b := by linarith
  have disc : 4 * (r ^ 2) ^ 3 - (27 * (a * b * c) - 1 + 3 * r ^ 2) ^ 2
      = 27 * ((a - b) * (b - c) * (a - c)) ^ 2 := by
    rw [hX, hc']; ring
  have hg : 27 * (a * b * c) - 1 + 3 * r ^ 2 = 2 * r ^ 3 := by rw [h27]; unfold gfun; ring
  rw [hg] at disc
  have hD : ((a - b) * (b - c) * (a - c)) ^ 2 = 0 := by nlinarith
  have hD' : (a - b) * (b - c) * (a - c) = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hD
  rcases mul_eq_zero.mp hD' with h | h
  · rcases mul_eq_zero.mp h with h | h
    · -- a = b
      obtain ⟨e1, e2, e3⟩ := triple_structure_aux hs hr hX h27 (by linarith)
      exact Or.inr (Or.inr ⟨e1, e2, e3⟩)
    · -- b = c
      obtain ⟨e1, e2, e3⟩ := triple_structure_aux (a := b) (b := c) (c := a) (by linarith) hr
        (by rw [hX]; ring) (by rw [← h27]; ring) (by linarith)
      exact Or.inl ⟨e3, e1, e2⟩
  · -- a = c
    obtain ⟨e1, e2, e3⟩ := triple_structure_aux (a := a) (b := c) (c := b) (by linarith) hr
      (by rw [hX]; ring) (by rw [← h27]; ring) (by linarith)
    exact Or.inr (Or.inl ⟨e1, e3, e2⟩)

theorem eq_of_prod {x y G : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxG : x ≤ G) (hyG : y ≤ G) (hG : 0 < G)
    (h : x * y = G ^ 2) : x = G ∧ y = G := by
  constructor <;> nlinarith

theorem le_one_of_fourth {x P : ℝ} (hx : 0 ≤ x) (hP : P ≤ 1) (h : x ^ 4 = P) : x ≤ 1 := by
  by_contra hc; push Not at hc
  have : 1 < x ^ 4 := one_lt_pow₀ hc (by norm_num)
  linarith

/-- **Equality in the core inequality** `27 κ = g(ξζ)` with `0 < ξζ < 1`: `ξ = ζ`, `κ > 0`, and `A`, `B` are
rearrangements of `((1+2s)/3, (1-s)/3, (1-s)/3)`, `s = ξ²`. -/
theorem rf_equality_core {A0 A1 A2 B0 B1 B2 κ ξ ζ : ℝ}
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hAs : A0 + A1 + A2 = 1)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hBs : B0 + B1 + B2 = 1)
    (hκ : κ ^ 2 = A0 * A1 * A2 * (B0 * B1 * B2))
    (hξ : 0 ≤ ξ) (hξ4 : ξ ^ 4 = 1 - 3 * (A0 * A1 + A0 * A2 + A1 * A2))
    (hζ : 0 ≤ ζ) (hζ4 : ζ ^ 4 = 1 - 3 * (B0 * B1 + B0 * B2 + B1 * B2))
    (h : 27 * κ = gfun (ξ * ζ)) (hs0 : 0 < ξ * ζ) (hs1 : ξ * ζ < 1) :
    ξ = ζ ∧ 0 < κ ∧
      ((A0 = (1 + 2 * ξ ^ 2) / 3 ∧ A1 = (1 - ξ ^ 2) / 3 ∧ A2 = (1 - ξ ^ 2) / 3) ∨
        (A0 = (1 - ξ ^ 2) / 3 ∧ A1 = (1 + 2 * ξ ^ 2) / 3 ∧ A2 = (1 - ξ ^ 2) / 3) ∨
        (A0 = (1 - ξ ^ 2) / 3 ∧ A1 = (1 - ξ ^ 2) / 3 ∧ A2 = (1 + 2 * ξ ^ 2) / 3)) ∧
      ((B0 = (1 + 2 * ξ ^ 2) / 3 ∧ B1 = (1 - ξ ^ 2) / 3 ∧ B2 = (1 - ξ ^ 2) / 3) ∨
        (B0 = (1 - ξ ^ 2) / 3 ∧ B1 = (1 + 2 * ξ ^ 2) / 3 ∧ B2 = (1 - ξ ^ 2) / 3) ∨
        (B0 = (1 - ξ ^ 2) / 3 ∧ B1 = (1 - ξ ^ 2) / 3 ∧ B2 = (1 + 2 * ξ ^ 2) / 3)) := by
  have hXb := X_bounds hA0 hA1 hA2 hAs
  have hYb := X_bounds hB0 hB1 hB2 hBs
  have hξ1 : ξ ≤ 1 := le_one_of_fourth hξ hXb.2 hξ4
  have hζ1 : ζ ≤ 1 := le_one_of_fourth hζ hYb.2 hζ4
  have h1 := rp_bound (r := ξ ^ 2) hAs (by positivity) (by rw [← hξ4]; ring)
  have h2 := rp_bound (r := ζ ^ 2) hBs (by positivity) (by rw [← hζ4]; ring)
  have e3A : 0 ≤ A0 * A1 * A2 := by positivity
  have e3B : 0 ≤ B0 * B1 * B2 := by positivity
  have hgξ := gfun_nonneg (sq_nonneg ξ)
  have hgζ := gfun_nonneg (sq_nonneg ζ)
  have hq : 0 ≤ ξ * ζ := hs0.le
  have hgs : 0 < gfun (ξ * ζ) := by
    unfold gfun; have : 0 < 1 - ξ * ζ := by linarith
    positivity
  have hκpos : 0 < κ := by linarith
  have hprod : (27 * (A0 * A1 * A2)) * (27 * (B0 * B1 * B2)) = gfun (ξ * ζ) ^ 2 := by
    have : (27 * κ) ^ 2 = (27 * (A0 * A1 * A2)) * (27 * (B0 * B1 * B2)) := by rw [mul_pow, hκ]; ring
    rw [← this, h]
  have hmid : (27 * (A0 * A1 * A2)) * (27 * (B0 * B1 * B2)) ≤ gfun (ξ ^ 2) * gfun (ζ ^ 2) :=
    mul_le_mul h1 h2 (by positivity) hgξ
  have hT := transfer_le hξ hξ1 hζ hζ1
  have hTid := transfer_id ξ ζ
  have hd : (ξ - ζ) ^ 2 = 0 := by
    have hw : 0 ≤ (1 - ξ ^ 2) * (1 - ζ ^ 2) := mul_nonneg (by nlinarith) (by nlinarith)
    have hQ : 0 ≤ (1 - ξ ^ 2) * (1 - ζ ^ 2) * (6 * (ξ * ζ) * (ξ * ζ + 2) + 2 * (ξ - ζ) ^ 2) := by
      positivity
    have hzero : gfun (ξ * ζ) ^ 2 - gfun (ξ ^ 2) * gfun (ζ ^ 2) = 0 := by
      apply le_antisymm
      · linarith
      · linarith
    rw [hzero] at hTid
    have hd0 : 0 ≤ (ξ - ζ) ^ 2 := sq_nonneg _
    have hR : 0 ≤ (ξ - ζ) ^ 2 * ((1 - ξ ^ 2) * (1 - ζ ^ 2) * (6 * (ξ * ζ) * (ξ * ζ + 2) + 2 * (ξ - ζ) ^ 2)) :=
      mul_nonneg hd0 hQ
    have hR2 : 0 ≤ (ξ - ζ) ^ 2 * ((ξ - ζ) ^ 2 * (1 + 2 * (ξ * ζ)) ^ 2) :=
      mul_nonneg hd0 (mul_nonneg hd0 (sq_nonneg _))
    have hsum : (ξ - ζ) ^ 2 * ((ξ - ζ) ^ 2 * (1 + 2 * (ξ * ζ)) ^ 2) = 0 := by
      have e : (ξ - ζ) ^ 2 * ((1 - ξ ^ 2) * (1 - ζ ^ 2) * (6 * (ξ * ζ) * (ξ * ζ + 2) + 2 * (ξ - ζ) ^ 2)
        + (ξ - ζ) ^ 2 * (1 + 2 * (ξ * ζ)) ^ 2) =
        (ξ - ζ) ^ 2 * ((1 - ξ ^ 2) * (1 - ζ ^ 2) * (6 * (ξ * ζ) * (ξ * ζ + 2) + 2 * (ξ - ζ) ^ 2)) +
        (ξ - ζ) ^ 2 * ((ξ - ζ) ^ 2 * (1 + 2 * (ξ * ζ)) ^ 2) := by ring
      rw [e] at hTid
      linarith
    rcases mul_eq_zero.mp hsum with h0 | h0
    · exact h0
    · rcases mul_eq_zero.mp h0 with h3 | h3
      · exact h3
      · exfalso
        have : 0 < (1 + 2 * (ξ * ζ)) ^ 2 := by positivity
        linarith
  have hξζ : ξ = ζ := by
    have : ξ - ζ = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hd
    linarith
  subst hξζ
  -- now ζ = ξ
  have hG : 0 < gfun (ξ ^ 2) := by
    have : ξ * ξ = ξ ^ 2 := by ring
    rw [this] at hgs; exact hgs
  have hp : (27 * (A0 * A1 * A2)) * (27 * (B0 * B1 * B2)) = gfun (ξ ^ 2) ^ 2 := by
    rw [hprod]; have : ξ * ξ = ξ ^ 2 := by ring
    rw [this]
  obtain ⟨hEA, hEB⟩ := eq_of_prod (by positivity) (by positivity) h1 h2 hG hp
  have hξ2 : 0 < ξ ^ 2 := by
    have : 0 < ξ := by
      rcases hξ.lt_or_eq with h' | h'
      · exact h'
      · exfalso; rw [← h'] at hs0; simp at hs0
    positivity
  refine ⟨rfl, hκpos, triple_structure hAs hξ2 (by rw [← hξ4]; ring) hEA,
    triple_structure hBs hξ2 (by rw [← hζ4]; ring) hEB⟩

end FormalResearch.FourQubitEntropy.QVEquality
