module

public import FormalResearch.SignUncertainty.BinetP2
public import FormalResearch.SignUncertainty.BinetGamma

/-!
# Derivatives of the Binet remainder as integrals against `P₂`

**Proved**: for `Re w > 0` and `r ≥ 0`,
`B_Bin^{(r)}(w) = (-1)^r (r+1)! ∫₀^∞ P₂(s) (s+w)^{-(r+2)} ds`,
by Fubini from `μ_Bin(t) = t ∫₀^∞ e^{-ts} P₂(s) ds` (`laplace_binP2`).
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open FormalResearch.Asymptotics

namespace FormalResearch.SignUncertainty.BinetDecay

/-- The integrand `(s, t) ↦ P₂(s) t^{r+1} e^{-t(s+w)}` of the Fubini exchange. -/
noncomputable def fub (r : ℕ) (w : ℂ) (t s : ℝ) : ℂ :=
  (binP2 s : ℂ) * ((t : ℂ) ^ (r + 1) * Complex.exp (-((t : ℂ) * ((s : ℂ) + w))))

lemma measurable_fub (r : ℕ) (w : ℂ) : Measurable (Function.uncurry (fub r w)) := by
  unfold fub Function.uncurry
  have h1 : Measurable fun p : ℝ × ℝ => (binP2 p.2 : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_binP2.comp measurable_snd)
  have h2 : Measurable fun p : ℝ × ℝ => ((p.1 : ℂ) ^ (r + 1) *
      Complex.exp (-((p.1 : ℂ) * ((p.2 : ℂ) + w)))) := by fun_prop
  exact h1.mul h2

lemma norm_fub (r : ℕ) {w : ℂ} (t s : ℝ) (ht : 0 < t) :
    ‖fub r w t s‖ = (t ^ (r + 1) * Real.exp (-(t * w.re))) * (Real.exp (-(t * s)) * binP2 s) := by
  unfold fub
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg ht.le, Real.norm_of_nonneg (binP2_nonneg s)]
  have : (-((t : ℂ) * ((s : ℂ) + w))).re = -(t * s) + -(t * w.re) := by
    simp [mul_add]; ring
  rw [this, Real.exp_add]
  ring

lemma inner_fub (r : ℕ) (w : ℂ) {t : ℝ} (ht : 0 < t) :
    ∫ s in Ioi (0 : ℝ), fub r w t s =
      (muBin t : ℂ) * (t : ℂ) ^ r * Complex.exp (-((t : ℂ) * w)) := by
  have hl := laplace_binP2 ht
  have hlc : ∫ s in Ioi (0 : ℝ), Complex.exp (-((t : ℂ) * (s : ℂ))) * (binP2 s : ℂ) =
      ((muBin t / t : ℝ) : ℂ) := by
    rw [← hl, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    simp [Complex.ofReal_exp]
  have : ∀ s : ℝ, fub r w t s = ((t : ℂ) ^ (r + 1) * Complex.exp (-((t : ℂ) * w))) *
      (Complex.exp (-((t : ℂ) * (s : ℂ))) * (binP2 s : ℂ)) := by
    intro s
    unfold fub
    rw [show -((t : ℂ) * ((s : ℂ) + w)) = -((t : ℂ) * (s : ℂ)) + -((t : ℂ) * w) by ring,
      Complex.exp_add]
    ring
  simp_rw [this]
  rw [integral_const_mul, hlc]
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  push_cast
  field_simp
  ring

lemma outer_fub (r : ℕ) {w : ℂ} (hw : 0 < w.re) {s : ℝ} (hs : 0 < s) :
    ∫ t in Ioi (0 : ℝ), fub r w t s =
      (binP2 s : ℂ) * (((r + 1).factorial : ℂ) / ((s : ℂ) + w) ^ (r + 2)) := by
  unfold fub
  rw [integral_const_mul]
  have hre : 0 < ((s : ℂ) + w).re := by simp; linarith
  have := integral_pow_exp_cpx (r + 1) hre
  rw [this]


lemma integral_norm_fub (r : ℕ) {w : ℂ} {t : ℝ} (ht : 0 < t) :
    ∫ s in Ioi (0 : ℝ), ‖fub r w t s‖ =
      t ^ r * Real.exp (-(t * w.re)) * muBin t := by
  have hl := laplace_binP2 ht
  have : ∀ s : ℝ, ‖fub r w t s‖ = (t ^ (r + 1) * Real.exp (-(t * w.re))) *
      (Real.exp (-(t * s)) * binP2 s) := fun s => norm_fub r t s ht
  simp_rw [this]
  rw [integral_const_mul, hl]
  have ht0 : t ≠ 0 := ht.ne'
  field_simp
  ring

lemma integrable_fub (r : ℕ) {w : ℂ} (hw : 0 < w.re) :
    Integrable (Function.uncurry (fub r w))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [integrable_prod_iff (measurable_fub r w).aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    have hI := (integrableOn_exp_mul_binP2 ht').const_mul (t ^ (r + 1) * Real.exp (-(t * w.re)))
    refine Integrable.mono' hI ?_ ?_
    · exact ((measurable_fub r w).of_uncurry_left).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s _ => ?_)
      exact (norm_fub r t s ht').le
  · have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ r * Real.exp (-(t * w.re)) * muBin t)
        (volume.restrict (Ioi (0 : ℝ))) := by
      refine AEStronglyMeasurable.mul ?_ (muBin_continuousOn.aestronglyMeasurable measurableSet_Ioi)
      exact (by fun_prop : Continuous fun t : ℝ => t ^ r * Real.exp (-(t * w.re))).aestronglyMeasurable
    have hI : IntegrableOn (fun t : ℝ => (1 / 12 : ℝ) * (t ^ r * Real.exp (-(w.re * t)))) (Ioi 0) :=
      (integrableOn_pow_exp_real hw r).const_mul _
    have hint : Integrable (fun t : ℝ => t ^ r * Real.exp (-(t * w.re)) * muBin t)
        (volume.restrict (Ioi (0 : ℝ))) := by
      refine Integrable.mono' hI hmeas ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht' : (0 : ℝ) < t := ht
      rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (muBin_pos ht').le), mul_comm t w.re]
      calc t ^ r * Real.exp (-(w.re * t)) * muBin t
          ≤ t ^ r * Real.exp (-(w.re * t)) * (1 / 12) :=
            mul_le_mul_of_nonneg_left (muBin_le ht') (by positivity)
        _ = 1 / 12 * (t ^ r * Real.exp (-(w.re * t))) := by ring
    refine hint.congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    exact (integral_norm_fub r ht).symm

/-- **Derivatives of the Binet remainder as `P₂`-integrals.**  For `Re w > 0`,
`B_Bin^{(r)}(w) = (-1)^r (r+1)! ∫₀^∞ P₂(s) (s+w)^{-(r+2)} ds`. -/
theorem iteratedDeriv_binetRem_P2 (r : ℕ) {w : ℂ} (hw : 0 < w.re) :
    iteratedDeriv r binetRem w =
      (-1 : ℂ) ^ r * ∫ s in Ioi (0 : ℝ),
        (binP2 s : ℂ) * (((r + 1).factorial : ℂ) / ((s : ℂ) + w) ^ (r + 2)) := by
  rw [iteratedDeriv_binetRem r hw]
  congr 1
  have h1 : ∫ t in Ioi (0 : ℝ), (muBin t : ℂ) * (t : ℂ) ^ r * Complex.exp (-((t : ℂ) * w)) =
      ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), fub r w t s :=
    (setIntegral_congr_fun measurableSet_Ioi (fun t ht => (inner_fub r w ht).symm))
  rw [h1, integral_integral_swap (integrable_fub r hw)]
  exact setIntegral_congr_fun measurableSet_Ioi (fun s hs => outer_fub r hw hs)

/-- info: 'FormalResearch.SignUncertainty.BinetDecay.iteratedDeriv_binetRem_P2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iteratedDeriv_binetRem_P2

end FormalResearch.SignUncertainty.BinetDecay
