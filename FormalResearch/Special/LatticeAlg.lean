module

public import FormalResearch.Special.LatticeLevels

/-!
# Collecting the error terms of `latticeII_bound`

With `M = 4m`, `m ≥ 1`, `ε ≤ 1`, the error of `latticeII_bound` is at most
`C_φ (A₁ e^{-κX} + A₂ ε + A₃ e^{-2πm y₁})`, with `A_i` depending only on
`κ, r, r₀, y₁, K` (and not on `m, X, ε, C_φ`).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex

theorem explicit_total_le (κ r r0 y1 K : ℝ) (hκ : 0 < κ) (hr : 0 < r) (hr0 : 0 < r0) (hy1 : 0 < y1)
    (hK : 0 ≤ K) :
    ∃ A1 A2 A3 : ℝ, 0 ≤ A1 ∧ 0 ≤ A2 ∧ 0 ≤ A3 ∧ ∀ (Cφ ε X m : ℝ), 0 ≤ Cφ → 0 ≤ ε → ε ≤ 1 → 1 ≤ m →
      (1 / 2 + ε) * (2 * (Cφ * Real.exp (-κ * X))) +
      ε * (Cφ * Real.exp (κ * r0) / r0 * (2 / κ)) +
      (Cφ * Real.exp (κ * r0) / r0 * wconst κ * ε * (1 + 4 * (4 * m + 2 * ε + 1) / m) +
        (Cφ * Real.exp (κ * r0) / r0 * Real.exp (-κ * X) / m +
          1 / 12 * (2 * smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m K * y1 * Real.exp (-κ * X) +
            2 * smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m K / κ *
              Real.exp (-(2 * Real.pi * m * y1))))) ≤
      Cφ * (A1 * Real.exp (-κ * X) + A2 * ε + A3 * Real.exp (-(2 * Real.pi * m * y1))) := by
  set c0 : ℝ := Real.exp (κ * r0) / r0 with hc0
  set c1 : ℝ := c0 * (Real.exp (κ * r) / r + K) with hc1
  have hc0p : 0 < c0 := by positivity
  have hc1p : 0 ≤ c1 := by positivity
  have hwc : 0 ≤ wconst κ := by
    unfold wconst
    have : Real.exp (-κ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have : 0 < 1 - Real.exp (-κ) := by linarith
    positivity
  refine ⟨3 + c0 + c1 * y1 / 6, 2 * c0 / κ + 29 * c0 * wconst κ, c1 / (6 * κ),
    by positivity, by positivity, by positivity, ?_⟩
  intro Cφ ε X m hCφ hε hε1 hm
  have hm0 : 0 < m := by linarith
  have eX := (Real.exp_pos (-κ * X)).le
  have eY := (Real.exp_pos (-(2 * Real.pi * m * y1))).le
  -- the smooth constant
  have hCw : smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m K ≤ Cφ * c1 := by
    unfold smoothCw
    have h1 : Cφ * Real.exp (κ * r0) / r0 = Cφ * c0 := by rw [hc0]; ring
    rw [h1]
    have h2 : Real.exp (κ * r) / (r * m) ≤ Real.exp (κ * r) / r := by
      rw [div_le_div_iff₀ (by positivity) hr]
      nlinarith [mul_nonneg (Real.exp_pos (κ * r)).le (mul_nonneg hr.le (sub_nonneg.mpr hm))]
    have h3 : K / m ^ 2 ≤ K := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hK (sq_nonneg (m - 1)), mul_nonneg hK (sub_nonneg.mpr hm)]
    have : Cφ * c0 * (Real.exp (κ * r) / (r * m) + K / m ^ 2) ≤ Cφ * c0 * (Real.exp (κ * r) / r + K) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc _ ≤ _ := this
      _ = Cφ * c1 := by rw [hc1]; ring
  have hCw0 : 0 ≤ smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m K := by
    unfold smoothCw; positivity
  have hfac : 1 + 4 * (4 * m + 2 * ε + 1) / m ≤ 29 := by
    rw [show 1 + 4 * (4 * m + 2 * ε + 1) / m = 17 + (8 * ε + 4) / m by field_simp; ring]
    have : (8 * ε + 4) / m ≤ 12 := by
      rw [div_le_iff₀ hm0]; nlinarith
    linarith
  have hfac0 : 0 ≤ 1 + 4 * (4 * m + 2 * ε + 1) / m := by positivity
  have t1 : (1 / 2 + ε) * (2 * (Cφ * Real.exp (-κ * X))) ≤ 3 * (Cφ * Real.exp (-κ * X)) := by
    nlinarith [mul_nonneg hCφ eX]
  have t3 : Cφ * Real.exp (κ * r0) / r0 * wconst κ * ε * (1 + 4 * (4 * m + 2 * ε + 1) / m) ≤
      Cφ * (29 * c0 * wconst κ * ε) := by
    have e : Cφ * Real.exp (κ * r0) / r0 * wconst κ * ε * (1 + 4 * (4 * m + 2 * ε + 1) / m) =
        (Cφ * c0 * wconst κ * ε) * (1 + 4 * (4 * m + 2 * ε + 1) / m) := by rw [hc0]; ring
    rw [e]
    have : 0 ≤ Cφ * c0 * wconst κ * ε := by positivity
    nlinarith
  have t4 : Cφ * Real.exp (κ * r0) / r0 * Real.exp (-κ * X) / m ≤ Cφ * c0 * Real.exp (-κ * X) := by
    have e : Cφ * Real.exp (κ * r0) / r0 * Real.exp (-κ * X) / m =
        (Cφ * c0 * Real.exp (-κ * X)) / m := by rw [hc0]; ring
    rw [e, div_le_iff₀ hm0]
    have : 0 ≤ Cφ * c0 * Real.exp (-κ * X) := by positivity
    nlinarith
  have t5 : 1 / 12 * (2 * smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m K * y1 * Real.exp (-κ * X) +
      2 * smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m K / κ * Real.exp (-(2 * Real.pi * m * y1))) ≤
      Cφ * (c1 * y1 / 6 * Real.exp (-κ * X) + c1 / (6 * κ) * Real.exp (-(2 * Real.pi * m * y1))) := by
    have a1 : smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m K * y1 * Real.exp (-κ * X) ≤
        Cφ * c1 * y1 * Real.exp (-κ * X) := by
      have := mul_le_mul_of_nonneg_right hCw (mul_nonneg hy1.le eX)
      nlinarith
    have a2 : smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m K / κ * Real.exp (-(2 * Real.pi * m * y1)) ≤
        Cφ * c1 / κ * Real.exp (-(2 * Real.pi * m * y1)) := by
      have := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hCw hκ.le) eY
      exact this
    have e1 : 2 * smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m K / κ * Real.exp (-(2 * Real.pi * m * y1)) =
        2 * (smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m K / κ * Real.exp (-(2 * Real.pi * m * y1))) := by ring
    rw [e1]
    have e2 : Cφ * (c1 * y1 / 6 * Real.exp (-κ * X) + c1 / (6 * κ) * Real.exp (-(2 * Real.pi * m * y1))) =
        1 / 12 * (2 * (Cφ * c1 * y1 * Real.exp (-κ * X)) +
          2 * (Cφ * c1 / κ * Real.exp (-(2 * Real.pi * m * y1)))) := by
      field_simp; ring
    rw [e2]
    linarith [a1, a2]
  have t2 : ε * (Cφ * Real.exp (κ * r0) / r0 * (2 / κ)) = Cφ * (2 * c0 / κ * ε) := by
    rw [hc0]; ring
  calc _ ≤ 3 * (Cφ * Real.exp (-κ * X)) + Cφ * (2 * c0 / κ * ε) +
        (Cφ * (29 * c0 * wconst κ * ε) + (Cφ * c0 * Real.exp (-κ * X) +
          Cφ * (c1 * y1 / 6 * Real.exp (-κ * X) + c1 / (6 * κ) * Real.exp (-(2 * Real.pi * m * y1))))) := by
        rw [← t2]; linarith
    _ = _ := by ring

end FormalResearch.Special.Lattice
