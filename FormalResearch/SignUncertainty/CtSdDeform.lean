module

public import FormalResearch.SignUncertainty.CtSdSegRem
public import FormalResearch.SignUncertainty.CtSdEval0

/-!
# Contour deformation of `[0,R]` to the chain and the connecting segment (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3.  **Proved.**
For `g` holomorphic on `B(0,R₀)`, `R < R₀`, and any chain `Γ` from `0` to `R e^{iπ/6}`:
`∫_{[0,R]} s^{1/2} g = ∫_Γ s^{1/2} g + ∫_{Re^{iπ/6} → R} s^{1/2} g` (one primitive serves all three).
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtSd

/-- A chain integral is the difference of a primitive, for any primitive satisfying the line law. -/
lemma Chain3.int_eq_of_lines {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) {g : ℂ → ℂ} {Φ : ℂ → ℂ}
    (hΦ : ∀ (z₀ d : ℂ) (a b : ℝ), a ≤ b → (∀ t ∈ Icc a b, z₀ + (t : ℂ) * d ∈ ball (0 : ℂ) R₀ ∧
        0 ≤ (z₀ + (t : ℂ) * d).re) → (∀ t ∈ Ioc a b, z₀ + (t : ℂ) * d ≠ 0) →
      lineInt z₀ d a b (fun z => csr z * g z) = Φ (z₀ + (b : ℂ) * d) - Φ (z₀ + (a : ℂ) * d)) :
    ch.int (fun z => csr z * g z) = Φ p - Φ 0 := by
  have e1 := hΦ ch.q1.z0 ch.q1.d ch.q1.a ch.q1.b ch.ok1.1 ch.ok1.2.1 ch.ok1.2.2
  have e2 := hΦ ch.q2.z0 ch.q2.d ch.q2.a ch.q2.b ch.ok2.1 ch.ok2.2.1 ch.ok2.2.2
  have e3 := hΦ ch.q3.z0 ch.q3.d ch.q3.a ch.q3.b ch.ok3.1 ch.ok3.2.1 ch.ok3.2.2
  unfold Chain3.int
  rw [e1, e2, e3]
  have h0 : ch.q1.z0 + (ch.q1.a : ℂ) * ch.q1.d = 0 := ch.h0
  have h12 : ch.q1.z0 + (ch.q1.b : ℂ) * ch.q1.d = ch.q2.z0 + (ch.q2.a : ℂ) * ch.q2.d := ch.h12
  have h23 : ch.q2.z0 + (ch.q2.b : ℂ) * ch.q2.d = ch.q3.z0 + (ch.q3.a : ℂ) * ch.q3.d := ch.h23
  have h3 : ch.q3.z0 + (ch.q3.b : ℂ) * ch.q3.d = p := ch.h3
  rw [h0, h12, h23, h3]
  ring

lemma segZ0_add_segD (R : ℝ) : segZ0 R + ((1 : ℝ) : ℂ) * segD R = (R : ℂ) := by
  unfold segZ0 segD; push_cast; ring

/-- **Deformation.** -/
theorem deform_real {R₀ R : ℝ} (hR0 : 0 < R₀) (hRR : R < R₀) (hR : 0 < R) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 R₀)) (ch : Chain3 R₀ (segZ0 R)) :
    lineInt 0 1 0 R (fun z => csr z * g z) =
      ch.int (fun z => csr z * g z) + lineInt (segZ0 R) (segD R) 0 1 (fun z => csr z * g z) := by
  obtain ⟨Φ, hΦ⟩ := lineInt_csr hR0 hg
  have hch := ch.int_eq_of_lines hΦ
  have hreal := hΦ 0 1 0 R hR.le (fun t ht => ⟨by
      simp only [zero_add, mul_one, mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg ht.1]; linarith [ht.2], by simpa using ht.1⟩)
    (fun t ht => by simpa using ht.1.ne')
  have hseg := hΦ (segZ0 R) (segD R) 0 1 zero_le_one (fun t ht => by
      have hR' : 0 ≤ R := hR.le
      refine ⟨?_, ?_⟩
      · have := norm_segPt_le hR' ht.1 ht.2
        have e : segZ0 R + (t : ℂ) * segD R = segPt R t := rfl
        rw [e, mem_ball, dist_zero_right]; linarith
      · have := segPt_re_ge hR' ht.1 ht.2
        have hs := sqrt3_bounds
        have e : segZ0 R + (t : ℂ) * segD R = segPt R t := rfl
        rw [e]; nlinarith [mul_nonneg hR' ht.1])
    (fun t ht => by
      have e : segZ0 R + (t : ℂ) * segD R = segPt R t := rfl
      rw [e]
      exact segPt_ne_zero hR.le ht.1.le ht.2 hR)
  rw [hch, hreal, hseg]
  have a1 : (0 : ℂ) + ((R : ℝ) : ℂ) * 1 = (R : ℂ) := by simp
  have a2 : (0 : ℂ) + ((0 : ℝ) : ℂ) * 1 = 0 := by simp
  have a4 : segZ0 R + ((0 : ℝ) : ℂ) * segD R = segZ0 R := by simp
  rw [a1, a2, segZ0_add_segD, a4]
  ring

/-- info: 'FormalResearch.SignUncertainty.CtSd.deform_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deform_real

end FormalResearch.SignUncertainty.CtSd
