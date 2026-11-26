module

public import Mathlib

/-!
# A barrier lemma for linear differential inequalities (phase-free; Riccati asymptotics)

If `h' ≥ p h` on `[x₀, ∞)` with `p ≥ 1` and `h` is bounded above, then `h ≤ 0` there.  This is the comparison step
for the unstable branch of a Riccati equation: the recessive solution `Ai'/Ai` of `F' = x - F²` is repelling
forward in `x`, so the error `e = F - F_N` of a truncated formal series satisfies `e' = p e - r` with `p ≥ √x`, and
two applications (to `e - ρ` and `-e - ρ`) give `|e| ≤ ρ` as soon as `p ρ - ρ' ≥ |r|` and `e` is bounded.

Statements: `nonpos_of_deriv_ge_mul` (the barrier), `abs_le_of_riccati_barrier` (two-sided form).  Proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace FormalResearch.Asymptotics

/-- Barrier on `(x₀, ∞)`: `h' ≥ p h`, `p ≥ 1` continuous, `h` bounded above implies `h ≤ 0`. -/
lemma nonpos_of_deriv_ge_mul_aux {h h' p : ℝ → ℝ} {x0 M : ℝ}
    (hd : ∀ x, x0 < x → HasDerivAt h (h' x) x) (hp : ∀ x, x0 < x → 1 ≤ p x)
    (hpc : ∀ x, x0 < x → ContinuousAt p x) (hge : ∀ x, x0 < x → p x * h x ≤ h' x)
    (hM : ∀ x, x0 < x → h x ≤ M) : ∀ x, x0 < x → h x ≤ 0 := by
  intro x1 hx1
  by_contra hcon
  have hcon : 0 < h x1 := not_le.mp hcon
  have hM0 : 0 ≤ M := hcon.le.trans (hM x1 hx1)
  -- primitive of p from x1
  set Q : ℝ → ℝ := fun x => ∫ s in x1..x, p s with hQ
  have hpint : ∀ a b, x1 ≤ a → x1 ≤ b → IntervalIntegrable p MeasureTheory.volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    intro s hs
    have : x1 ≤ s := by
      rcases Set.mem_uIcc.mp hs with h | h
      · exact ha.trans h.1
      · exact hb.trans h.1
    exact (hpc s (hx1.trans_le this)).continuousWithinAt
  have hpO : ContinuousOn p (Ioi x1) :=
    fun x hx => (hpc x (hx1.trans hx)).continuousWithinAt
  have hQd : ∀ x, x1 < x → HasDerivAt Q (p x) x := by
    intro x hx
    exact intervalIntegral.integral_hasDerivAt_right (hpint x1 x le_rfl hx.le)
      (hpO.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hpc x (hx1.trans hx))
  have hQge : ∀ x, x1 ≤ x → x - x1 ≤ Q x := by
    intro x hx
    have : ∫ s in x1..x, (1 : ℝ) ≤ ∫ s in x1..x, p s :=
      intervalIntegral.integral_mono_on hx (by simp) (hpint x1 x le_rfl hx)
        (fun s hs => hp s (hx1.trans_le hs.1))
    simpa using this
  set φ : ℝ → ℝ := fun x => h x * Real.exp (-Q x) with hφ
  have hφd : ∀ x, x1 < x → HasDerivAt φ ((h' x - p x * h x) * Real.exp (-Q x)) x := by
    intro x hx
    have := (hd x (hx1.trans hx)).mul ((hQd x hx).neg.exp)
    refine this.congr_deriv ?_
    simp only [Pi.neg_apply]
    ring
  have hφmono : MonotoneOn φ (Ici x1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici x1)
    · intro x hx
      by_cases hx0 : x = x1
      · subst hx0
        have hc : ContinuousAt h x := (hd x hx1).continuousAt
        have hQc : ContinuousWithinAt Q (Ici x) x := by
          have h1 : ContinuousOn Q (Icc x (x + 1)) := by
            have := intervalIntegral.continuousOn_primitive_interval (a := x) (b := x + 1)
              (f := p) (μ := MeasureTheory.volume) (by
                rw [uIcc_of_le (by linarith : x ≤ x + 1)]
                exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
                  (hpint x (x + 1) le_rfl (by linarith)))
            simpa [uIcc_of_le (by linarith : x ≤ x + 1)] using this
          have h2 := h1 x ⟨le_rfl, by linarith⟩
          exact h2.mono_of_mem_nhdsWithin (by
            have : Icc x (x + 1) ∈ 𝓝[Ici x] x := Icc_mem_nhdsGE (by linarith)
            exact this)
        exact (hc.continuousWithinAt).mul (hQc.neg.rexp)
      · have hx' : x1 < x := lt_of_le_of_ne hx (Ne.symm hx0)
        exact (hφd x hx').continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hφd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hφd x hx).deriv]
      exact mul_nonneg (by linarith [hge x (hx1.trans hx)]) (Real.exp_pos _).le
  have hφ1 : 0 < φ x1 := mul_pos hcon (Real.exp_pos _)
  -- choose X large
  obtain ⟨X, hX1, hX⟩ : ∃ X, x1 ≤ X ∧ M * Real.exp (-(X - x1)) < φ x1 := by
    have hlim : Tendsto (fun X : ℝ => M * Real.exp (-(X - x1))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun X : ℝ => -(X - x1)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_right atTop (-x1) tendsto_id)
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul M
    obtain ⟨X, hX⟩ := (hlim.eventually (gt_mem_nhds hφ1)).and (eventually_ge_atTop x1) |>.exists
    exact ⟨X, hX.2, hX.1⟩
  have hmon := hφmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hX1) hX1
  have hXx : x0 < X := hx1.trans_le hX1
  have hle : φ X ≤ M * Real.exp (-(X - x1)) := by
    have h1 : h X ≤ M := hM X hXx
    have h2 : Real.exp (-Q X) ≤ Real.exp (-(X - x1)) := Real.exp_le_exp.mpr (by linarith [hQge X hX1])
    calc φ X = h X * Real.exp (-Q X) := rfl
      _ ≤ M * Real.exp (-Q X) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ M * Real.exp (-(X - x1)) := mul_le_mul_of_nonneg_left h2 hM0
  linarith

/-- **Barrier lemma.** If `h' ≥ p h` on `[x₀, ∞)` with `p ≥ 1` (continuous), `h` differentiable and bounded above,
then `h ≤ 0` on `[x₀, ∞)`. -/
theorem nonpos_of_deriv_ge_mul {h h' p : ℝ → ℝ} {x0 M : ℝ}
    (hd : ∀ x, x0 ≤ x → HasDerivAt h (h' x) x) (hp : ∀ x, x0 ≤ x → 1 ≤ p x)
    (hpc : ∀ x, x0 ≤ x → ContinuousAt p x) (hge : ∀ x, x0 ≤ x → p x * h x ≤ h' x)
    (hM : ∀ x, x0 ≤ x → h x ≤ M) : ∀ x, x0 ≤ x → h x ≤ 0 := by
  have h1 := nonpos_of_deriv_ge_mul_aux (x0 := x0) (M := M) (fun x hx => hd x hx.le)
    (fun x hx => hp x hx.le) (fun x hx => hpc x hx.le) (fun x hx => hge x hx.le) (fun x hx => hM x hx.le)
  intro x hx
  rcases hx.eq_or_lt with h0 | hlt
  · have hc : ContinuousAt h x := (hd x le_rfl).continuousAt
    have hlim : Tendsto h (𝓝[>] x) (𝓝 (h x)) := hc.continuousWithinAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with y hy using h1 y (by rw [h0]; exact hy)
  · exact h1 x hlt

end FormalResearch.Asymptotics
