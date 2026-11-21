module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# A product of two resolvent factors as an average of squared resolvents (CR.18)

Source: `CFT/sign_uncertainty/paper/ce_cardinal_resolvent.tex`, identity (CR.18) (label `cecr:CR.18`).

**Statement proved** (`resolvent_product_eq_integral`, proved): for real `s r h E` with `0 < 1 + s h E` and
`0 < 1 + r h E`,
`1 / ((1 + s h E)(1 + r h E)) = ∫ ω in 0..1, 1 / (1 + h (ω s + (1 - ω) r) E)^2`.

The proof is the fundamental theorem of calculus with the explicit antiderivative
`G(ω) = ω / ((1 + r h E) (1 + h E (ω s + (1 - ω) r)))`, whose derivative is `1 / u(ω)^2` with
`u(ω) = 1 + h E (ω s + (1 - ω) r)` identically in `s`, `r`; so the case `s = r` needs no separate argument and
no division by `s - r` appears.

**Positivity used.** The identity only needs `u(ω) ≠ 0` on `[0, 1]`. Since `u` is affine with values
`1 + r h E` and `1 + s h E` at the endpoints, this holds exactly when those two numbers have the same strict sign;
the hypotheses here are the paper's (both positive). `h`, `E` need not be non-negative.

See `FormalResearch.CohnElkies.StieltjesMixture` for the positive measure `Λ_{h,p}` and mixture identities
(CR.19)–(CR.20) built on top of this scalar identity.
-/

@[expose] public section

namespace FormalResearch.CohnElkies

open intervalIntegral

/-- **CR.18** (scalar form): the product of two Stieltjes-type resolvent factors is the average over
`ω ∈ [0, 1]` of the square of a single resolvent factor with the affine parameter `ω s + (1 - ω) r`. -/
theorem resolvent_product_eq_integral (s r h E : ℝ)
    (hs : 0 < 1 + s * h * E) (hr : 0 < 1 + r * h * E) :
    1 / ((1 + s * h * E) * (1 + r * h * E)) =
      ∫ ω in (0 : ℝ)..1, 1 / (1 + h * (ω * s + (1 - ω) * r) * E) ^ 2 := by
  -- The affine denominator has no zero on [0, 1]: it is a convex combination of the two positive endpoint values.
  have hu : ∀ ω ∈ Set.uIcc (0 : ℝ) 1, 1 + h * (ω * s + (1 - ω) * r) * E ≠ 0 := by
    intro ω hω
    rw [Set.uIcc_of_le zero_le_one] at hω
    obtain ⟨h0, h1⟩ := hω
    have e : 1 + h * (ω * s + (1 - ω) * r) * E
        = (1 - ω) * (1 + r * h * E) + ω * (1 + s * h * E) := by ring
    rw [e]
    rcases eq_or_lt_of_le h1 with h1' | h1'
    · subst h1'
      simpa using hs.ne'
    · have hpos1 : 0 < (1 - ω) * (1 + r * h * E) := mul_pos (by linarith) hr
      have hnn2 : 0 ≤ ω * (1 + s * h * E) := mul_nonneg h0 hs.le
      exact (add_pos_of_pos_of_nonneg hpos1 hnn2).ne'
  have hA : (1 + r * h * E) ≠ 0 := hr.ne'
  -- The antiderivative `G(ω) = ω / (A u(ω))` with `A = 1 + r h E`.
  have key : ∀ ω ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => x / ((1 + r * h * E) * (1 + h * (x * s + (1 - x) * r) * E)))
        (1 / (1 + h * (ω * s + (1 - ω) * r) * E) ^ 2) ω := by
    intro ω hω
    have hu' : HasDerivAt (fun x : ℝ => 1 + h * (x * s + (1 - x) * r) * E) (h * (s - r) * E) ω := by
      have hlin : HasDerivAt (fun x : ℝ => x * s + (1 - x) * r) (s - r) ω := by
        have h1 : HasDerivAt (fun x : ℝ => x * s) s ω := by
          simpa using (hasDerivAt_id' ω).mul_const s
        have h2 : HasDerivAt (fun x : ℝ => (1 - x) * r) (-r) ω := by
          simpa using ((hasDerivAt_const ω (1 : ℝ)).sub (hasDerivAt_id' ω)).mul_const r
        convert h1.add h2 using 1
      exact ((hlin.const_mul h).mul_const E).const_add 1
    have hd : HasDerivAt (fun x : ℝ => (1 + r * h * E) * (1 + h * (x * s + (1 - x) * r) * E))
        ((1 + r * h * E) * (h * (s - r) * E)) ω := hu'.const_mul (1 + r * h * E)
    have hne : (1 + r * h * E) * (1 + h * (ω * s + (1 - ω) * r) * E) ≠ 0 :=
      mul_ne_zero hA (hu ω hω)
    have hdiv := (hasDerivAt_id' ω).div hd hne
    convert hdiv using 1
    have hu0 := hu ω hω
    -- Cross-multiplied, the identity is polynomial: numerator `A u - ω A h (s - r) E = A^2`.
    rw [div_eq_div_iff (pow_ne_zero 2 hu0) (pow_ne_zero 2 hne)]
    ring
  -- Continuity of the integrand on `[0, 1]`, for the fundamental theorem of calculus.
  have hint : IntervalIntegrable (fun ω : ℝ => 1 / (1 + h * (ω * s + (1 - ω) * r) * E) ^ 2)
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · apply Continuous.continuousOn
      fun_prop
    · intro ω hω
      exact pow_ne_zero 2 (hu ω hω)
  rw [integral_eq_sub_of_hasDerivAt (fun ω hω => key ω hω) hint]
  have hu1 : (1 : ℝ) + h * (1 * s + (1 - 1) * r) * E = 1 + s * h * E := by ring
  simp only [zero_div, sub_zero, hu1]
  ring

/-- info: 'FormalResearch.CohnElkies.resolvent_product_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms resolvent_product_eq_integral

end FormalResearch.CohnElkies
