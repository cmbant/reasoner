module

public import FormalResearch.Special.AiryRankDecayKernel

/-!
# Hilbert–Schmidt error of the separated kernel (explicit `R`, `n`)

**Proved.**  Let `a ∈ ℝ`, `R ≥ 8` with `2|a| ≤ R`, `n ∈ ℕ`, `B = airyRankKer R (n+1)` the rank-`≤ n+1` kernel
of `AiryRankDecayKernel`.  Then (`airy_hs_bound`), with `M = airyChebM R = 3 exp((2/3)(17R/8)^{3/2})`,

`∬_{s > a, ζ > 0} (Ai(s+ζ) - B(s,ζ))² ≤ (2M/2^n)² (R - a) R + 9 e^{-a} exp(-(2/3)(R/2)^{3/2})`

(as a Lebesgue integral in `[0, ∞]`; no integrability hypotheses are needed).  Proof: on the box
`{s ≤ R, ζ ≤ R}` the pointwise Chebyshev bound (`abs_airy_sub_airyRankKer_le`) and the box area `(R-a)R`;
off the box `B = 0` and `s + ζ ≥ R/2 ≥ 4`, where `Ai(s+ζ)² ≤ 9 e^{-s} e^{-ζ} exp(-(2/3)(R/2)^{3/2})`
(`airyAi_sq_le_tail`), whose double integral over `(a,∞)×(0,∞)` is `e^{-a}` times the constant.  Both
pieces are products, so `lintegral_prod_mul` computes them.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace FormalResearch.Special

lemma lintegral_prod_mul_set {u v : ℝ → ℝ≥0∞} (hu : Measurable u) (hv : Measurable v)
    (s t : Set ℝ) :
    ∫⁻ p in s ×ˢ t, u p.1 * v p.2 = (∫⁻ x in s, u x) * ∫⁻ y in t, v y := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul hu.aemeasurable hv.aemeasurable]

lemma lintegral_indicator_Iic_Ioi (a R : ℝ) :
    ∫⁻ x in Ioi a, (Iic R).indicator (fun _ => (1 : ℝ≥0∞)) x = ENNReal.ofReal (R - a) := by
  rw [lintegral_indicator_const measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
    one_mul]
  have : Iic R ∩ Ioi a = Ioc a R := by
    ext x; simp [and_comm]
  rw [this, Real.volume_Ioc]

lemma lintegral_exp_neg_Ioi (c : ℝ) :
    ∫⁻ x in Ioi c, ENNReal.ofReal (Real.exp (-x)) = ENNReal.ofReal (Real.exp (-c)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi c)
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le), integral_exp_neg_Ioi]

/-- **Explicit Hilbert–Schmidt error** of the rank-`(n+1)` Chebyshev kernel. -/
theorem airy_hs_bound {a R : ℝ} (hR : 8 ≤ R) (haR : 2 * |a| ≤ R) (n : ℕ) :
    ∫⁻ p in Ioi a ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal ((airyAi (p.1 + p.2) - airyRankKer R (n + 1) p.1 p.2) ^ 2) ≤
      ENNReal.ofReal ((2 * airyChebM R / 2 ^ n) ^ 2 * ((R - a) * R)) +
        ENNReal.ofReal (9 * Real.exp (-(2 / 3) * (R / 2) ^ (3 / 2 : ℝ)) * Real.exp (-a)) := by
  have hR0 : 0 < R := by linarith
  have ha1 : |a| ≤ R / 2 := by linarith
  have ha2 : -(R / 2) ≤ a := by linarith [neg_abs_le a]
  have ha3 : a ≤ R / 2 := by linarith [le_abs_self a]
  set b : ℝ := 2 * airyChebM R / 2 ^ n with hb
  set τ : ℝ := 9 * Real.exp (-(2 / 3) * (R / 2) ^ (3 / 2 : ℝ)) with hτ
  have hτ0 : 0 ≤ τ := by positivity
  set u : ℝ → ℝ≥0∞ := (Iic R).indicator (fun _ => (1 : ℝ≥0∞)) with hu
  set e : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-x)) with he
  have hum : Measurable u := measurable_const.indicator measurableSet_Iic
  have hem : Measurable e := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_neg)
  set H : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (b ^ 2) * (u p.1 * u p.2) +
    ENNReal.ofReal τ * (e p.1 * e p.2) with hH
  have hmono : ∫⁻ p in Ioi a ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal ((airyAi (p.1 + p.2) - airyRankKer R (n + 1) p.1 p.2) ^ 2) ≤
      ∫⁻ p in Ioi a ×ˢ Ioi (0 : ℝ), H p := by
    refine setLIntegral_mono' (measurableSet_Ioi.prod measurableSet_Ioi) fun p hp => ?_
    obtain ⟨s, ζ⟩ := p
    have hs : a < s := hp.1
    have hζ : 0 < ζ := hp.2
    by_cases hA : s ≤ R ∧ ζ ≤ R
    · have hsR : |s| ≤ R := abs_le.2 ⟨by linarith, hA.1⟩
      have h1 := abs_airy_sub_airyRankKer_le hR0 hsR hζ.le hA.2 n
      have h2 : (airyAi (s + ζ) - airyRankKer R (n + 1) s ζ) ^ 2 ≤ b ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have hus : u s = 1 := by simp [hu, hA.1]
      have huζ : u ζ = 1 := by simp [hu, hA.2]
      refine (ENNReal.ofReal_le_ofReal h2).trans ?_
      simp only [hH, hus, huζ, mul_one]
      exact le_self_add
    · have hker : airyRankKer R (n + 1) s ζ = 0 := by
        by_cases h : s ≤ R
        · exact airyRankKer_eq_zero_of_ζ _ _ (by by_contra hc; exact hA ⟨h, not_lt.1 hc⟩)
        · exact airyRankKer_eq_zero_of_s _ _ (not_le.1 h)
      have hx : R / 2 ≤ s + ζ := by
        by_cases h : s ≤ R
        · have : R < ζ := by by_contra hc; exact hA ⟨h, not_lt.1 hc⟩
          linarith
        · linarith [not_le.1 h]
      have h1 := airyAi_sq_le_tail (x := s + ζ) (y := R / 2) (by linarith) hx
      rw [hker, sub_zero]
      have h3 : ENNReal.ofReal (airyAi (s + ζ) ^ 2) ≤
          ENNReal.ofReal τ * (e s * e ζ) := by
        refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
        simp only [he]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hτ0]
        congr 1
        rw [show -(s + ζ) = -s + -ζ by ring, Real.exp_add, hτ]
        ring
      refine h3.trans ?_
      simp only [hH]
      exact le_add_self
  refine hmono.trans (le_of_eq ?_)
  have hm1 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (b ^ 2) * (u p.1 * u p.2) :=
    measurable_const.mul ((hum.comp measurable_fst).mul (hum.comp measurable_snd))
  simp only [hH]
  rw [lintegral_add_left hm1,
    lintegral_const_mul (f := fun p : ℝ × ℝ => u p.1 * u p.2) _
      ((hum.comp measurable_fst).mul (hum.comp measurable_snd)),
    lintegral_const_mul (f := fun p : ℝ × ℝ => e p.1 * e p.2) _
      ((hem.comp measurable_fst).mul (hem.comp measurable_snd)),
    lintegral_prod_mul_set hum hum, lintegral_prod_mul_set hem hem]
  simp only [hu, he]
  rw [lintegral_indicator_Iic_Ioi, lintegral_indicator_Iic_Ioi,
    lintegral_exp_neg_Ioi, lintegral_exp_neg_Ioi, neg_zero, Real.exp_zero, ENNReal.ofReal_one,
    sub_zero]
  rw [mul_one, ← ENNReal.ofReal_mul (by linarith : 0 ≤ R - a), ← ENNReal.ofReal_mul (sq_nonneg b),
    ← ENNReal.ofReal_mul hτ0]

/-- info: 'FormalResearch.Special.airy_hs_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_hs_bound

end FormalResearch.Special
