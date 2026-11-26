module

public import FormalResearch.SignUncertainty.CtSdContour

/-!
# Line-segment path integrals (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 (contour `Γ_SD`: the pieces are line segments).
**Proved.**  `lineInt z₀ d a b f = ∫_a^b f(z₀ + t d) d dt`, the fundamental theorem of calculus along a line, and the norm bound.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex

namespace FormalResearch.SignUncertainty.CtSd

/-- `∫_a^b f(z₀ + t d) d dt`: the integral of `f` along the segment `t ↦ z₀ + t d`. -/
noncomputable def lineInt (z₀ d : ℂ) (a b : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∫ t in a..b, f (z₀ + (t : ℂ) * d) * d

lemma hasDerivAt_line (z₀ d : ℂ) (t : ℝ) : HasDerivAt (fun t : ℝ => z₀ + (t : ℂ) * d) d t := by
  have := ((hasDerivAt_id (t : ℂ)).mul_const d).const_add z₀
  simpa using this.comp_ofReal

/-- Fundamental theorem of calculus along a segment. -/
theorem lineInt_ftc {Ψ Ψ' : ℂ → ℂ} {z₀ d : ℂ} {a b : ℝ} (hab : a ≤ b)
    (hΨ : ∀ t ∈ Icc a b, HasDerivAt Ψ (Ψ' (z₀ + (t : ℂ) * d)) (z₀ + (t : ℂ) * d))
    (hc : ContinuousOn (fun t : ℝ => Ψ' (z₀ + (t : ℂ) * d)) (Icc a b)) :
    lineInt z₀ d a b Ψ' = Ψ (z₀ + (b : ℂ) * d) - Ψ (z₀ + (a : ℂ) * d) := by
  unfold lineInt
  have hd : ∀ t ∈ Icc a b, HasDerivAt (fun t : ℝ => Ψ (z₀ + (t : ℂ) * d)) (Ψ' (z₀ + (t : ℂ) * d) * d) t := by
    intro t ht
    have h := (hΨ t ht).scomp t (hasDerivAt_line z₀ d t)
    have e : Ψ' (z₀ + (t : ℂ) * d) * d = d • Ψ' (z₀ + (t : ℂ) * d) := by rw [smul_eq_mul]; ring
    rw [e]; exact h
  have hint : IntervalIntegrable (fun t : ℝ => Ψ' (z₀ + (t : ℂ) * d) * d) volume a b :=
    (hc.mul continuousOn_const).intervalIntegrable_of_Icc hab
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (by rwa [uIcc_of_le hab] at ht)) hint

/-- Norm bound for a segment integral. -/
theorem norm_lineInt_le {z₀ d : ℂ} {a b : ℝ} (hab : a ≤ b) (f : ℂ → ℂ) :
    ‖lineInt z₀ d a b f‖ ≤ ∫ t in a..b, ‖f (z₀ + (t : ℂ) * d)‖ * ‖d‖ := by
  unfold lineInt
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans (le_of_eq ?_)
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [norm_mul]

/-- Path independence along a segment from `z₀ + a d` to `z₀ + b d` for `s^{1/2} g(s)`. -/
theorem lineInt_csr {r0 : ℝ} (hr0 : 0 < r0) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 r0)) :
    ∃ Φ : ℂ → ℂ, ∀ (z₀ d : ℂ) (a b : ℝ), a ≤ b → (∀ t ∈ Icc a b, z₀ + (t : ℂ) * d ∈ ball (0 : ℂ) r0 ∧
        0 ≤ (z₀ + (t : ℂ) * d).re) → (∀ t ∈ Ioc a b, z₀ + (t : ℂ) * d ≠ 0) →
      lineInt z₀ d a b (fun z => csr z * g z) = Φ (z₀ + (b : ℂ) * d) - Φ (z₀ + (a : ℂ) * d) := by
  obtain ⟨Φ, hΦ⟩ := pint_csr hr0 hg
  refine ⟨Φ, fun z₀ d a b hab hmem hne => ?_⟩
  have := hΦ (fun t : ℝ => z₀ + (t : ℂ) * d) (fun _ => d) a b hab (fun t _ => hasDerivAt_line z₀ d t)
    continuousOn_const hmem hne
  exact this

end FormalResearch.SignUncertainty.CtSd
