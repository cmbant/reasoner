module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Contour deformation for `∫ s^{1/2} g(s) ds` (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 ("deform `[0,s₁]` by Cauchy's theorem to
`Γ_SD ∪ Γ_arc`").  **Proved.**  For `g` holomorphic on a disc `B(0,r₀)`, `Φ(s) = F(s^{1/2})` with `F' = 2u² g(u²)` on `B(0,√r₀)`
is a primitive of `s^{1/2} g(s)` on `B(0,r₀) ∩ (ℂ ∖ (-∞,0])`, continuous on `B(0,r₀) ∩ {Re ≥ 0}`; hence the integral along any
`C¹` path from the origin in the closed right half-plane depends only on the endpoint.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex

namespace FormalResearch.SignUncertainty.CtSd

/-- The principal square root `z^{1/2}` (the one used in `ray1`). -/
noncomputable def csr (z : ℂ) : ℂ := z ^ (1 / 2 : ℂ)

lemma csr_sq (z : ℂ) : csr z ^ 2 = z := by
  unfold csr
  have := Complex.cpow_ofNat_inv_pow z 2
  rwa [one_div]

lemma norm_csr (z : ℂ) : ‖csr z‖ = Real.sqrt ‖z‖ := by
  have h : ‖csr z‖ ^ 2 = ‖z‖ := by rw [← norm_pow, csr_sq]
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

lemma continuousAt_csr {z : ℂ} (hz : 0 ≤ z.re ∨ z.im ≠ 0) : ContinuousAt csr z :=
  continuousAt_cpow_const_of_re_pos hz (by norm_num)

lemma hasDerivAt_csr {z : ℂ} (hz : z ∈ slitPlane) : HasDerivAt csr (csr z / (2 * z)) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have h := (Complex.hasStrictDerivAt_cpow_const (c := (1 / 2 : ℂ)) hz).hasDerivAt
  refine h.congr_deriv ?_
  rw [Complex.cpow_sub _ _ hz0, Complex.cpow_one]
  unfold csr
  field_simp

lemma re_nonneg_or_im (z : ℂ) (h : z ∈ slitPlane) : 0 ≤ z.re ∨ z.im ≠ 0 :=
  h.imp le_of_lt id

/-- A primitive of `s^{1/2} g(s)` on the slit disc. -/
theorem sqrt_primitive {r0 : ℝ} (hr0 : 0 < r0) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 r0)) :
    ∃ Φ : ℂ → ℂ, (∀ s ∈ ball (0 : ℂ) r0, s ∈ slitPlane → HasDerivAt Φ (csr s * g s) s) ∧
      ∀ s ∈ ball (0 : ℂ) r0, (0 ≤ s.re ∨ s.im ≠ 0) → ContinuousAt Φ s := by
  have hsq : MapsTo (fun u : ℂ => u ^ 2) (ball (0 : ℂ) (Real.sqrt r0)) (ball (0 : ℂ) r0) := by
    intro u hu
    rw [mem_ball_zero_iff] at hu ⊢
    rw [norm_pow]
    have h0 : 0 ≤ ‖u‖ := norm_nonneg u
    calc ‖u‖ ^ 2 < Real.sqrt r0 ^ 2 := by gcongr
      _ = r0 := Real.sq_sqrt hr0.le
  have hh : DifferentiableOn ℂ (fun u : ℂ => 2 * u ^ 2 * g (u ^ 2)) (ball (0 : ℂ) (Real.sqrt r0)) :=
    (by fun_prop : Differentiable ℂ fun u : ℂ => 2 * u ^ 2).differentiableOn.mul (hg.comp (by fun_prop : Differentiable ℂ fun u : ℂ => u ^ 2).differentiableOn hsq)
  obtain ⟨F, hF⟩ := hh.isExactOn_ball
  have hmem : ∀ s ∈ ball (0 : ℂ) r0, csr s ∈ ball (0 : ℂ) (Real.sqrt r0) := by
    intro s hs
    rw [mem_ball_zero_iff] at hs ⊢
    rw [norm_csr]
    exact Real.sqrt_lt_sqrt (norm_nonneg _) hs
  refine ⟨fun s => F (csr s), ?_, ?_⟩
  · intro s hs hsl
    have hs0 : s ≠ 0 := slitPlane_ne_zero hsl
    have h1 := hasDerivAt_csr hsl
    have h2 := hF _ (hmem s hs)
    have h3 := HasDerivAt.comp s h2 h1
    refine h3.congr_deriv ?_
    simp only []
    rw [csr_sq]
    field_simp
  · intro s hs hre
    have hc := continuousAt_csr hre
    have hFc : ContinuousAt F (csr s) := (hF _ (hmem s hs)).continuousAt
    exact hFc.comp hc

lemma mem_slit_of_re_nonneg {z : ℂ} (h : 0 ≤ z.re) (hz : z ≠ 0) : z ∈ slitPlane := by
  rcases h.lt_or_eq with h1 | h1
  · exact Or.inl h1
  · right
    intro him
    apply hz
    apply Complex.ext
    · simp [← h1]
    · simpa using him

/-- **Path independence.**  There is a primitive `Φ` of `s^{1/2} g(s)` such that, along every `C¹` path in `B(0,r₀) ∩ {Re ≥ 0}` which
avoids `0` after its starting point, `∫ s^{1/2} g(s) ds = Φ(end) - Φ(start)`. -/
theorem pint_csr {r0 : ℝ} (hr0 : 0 < r0) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 r0)) :
    ∃ Φ : ℂ → ℂ, ∀ (γ γ' : ℝ → ℂ) (a b : ℝ), a ≤ b → (∀ t ∈ Icc a b, HasDerivAt γ (γ' t) t) →
      ContinuousOn γ' (Icc a b) → (∀ t ∈ Icc a b, γ t ∈ ball (0 : ℂ) r0 ∧ 0 ≤ (γ t).re) →
      (∀ t ∈ Ioc a b, γ t ≠ 0) →
      ∫ t in a..b, csr (γ t) * g (γ t) * γ' t = Φ (γ b) - Φ (γ a) := by
  obtain ⟨Φ, hΦ1, hΦ2⟩ := sqrt_primitive hr0 hg
  refine ⟨Φ, fun γ γ' a b hab hγ hγ' hmem hne => ?_⟩
  have hγc : ContinuousOn γ (Icc a b) := fun t ht => (hγ t ht).continuousAt.continuousWithinAt
  have hΦc : ContinuousOn (fun t => Φ (γ t)) (Icc a b) := by
    intro t ht
    have hre : 0 ≤ (γ t).re ∨ (γ t).im ≠ 0 := Or.inl (hmem t ht).2
    exact ((hΦ2 _ (hmem t ht).1 hre).comp_continuousWithinAt (hγc t ht))
  have hderiv : ∀ t ∈ Ioo a b, HasDerivAt (fun t => Φ (γ t)) (csr (γ t) * g (γ t) * γ' t) t := by
    intro t ht
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    have hsl := mem_slit_of_re_nonneg (hmem t ht').2 (hne t ⟨ht.1, ht.2.le⟩)
    have h := (hΦ1 _ (hmem t ht').1 hsl).scomp t (hγ t ht')
    have e : csr (γ t) * g (γ t) * γ' t = γ' t • (csr (γ t) * g (γ t)) := by rw [smul_eq_mul]; ring
    rw [e]
    exact h
  have hcont : ContinuousOn (fun t => csr (γ t) * g (γ t) * γ' t) (Icc a b) := by
    have h1 : ContinuousOn (fun t => csr (γ t)) (Icc a b) := fun t ht =>
      ((continuousAt_csr (Or.inl (hmem t ht).2)).comp_continuousWithinAt (hγc t ht))
    have h2 : ContinuousOn (fun t => g (γ t)) (Icc a b) :=
      hg.continuousOn.comp hγc (fun t ht => (hmem t ht).1)
    exact (h1.mul h2).mul hγ'
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hΦc hderiv (hcont.intervalIntegrable_of_Icc hab)

end FormalResearch.SignUncertainty.CtSd
