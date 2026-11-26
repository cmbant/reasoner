module

public import Mathlib
public import FormalResearch.SignUncertainty.CtChartComplex
public import FormalResearch.SignUncertainty.CtCfuAnalytic
public import FormalResearch.SignUncertainty.CtCfuTheta

/-!
# `ct:cfu`: analyticity of `ψ_ε` across `a = 0`, and `CtChartComplex` (unconditional)

`constant_terms_lower.tex`, Lemma `ct:cfu` Step 2 (`ψ_ε(a) := h_ε(-a, a)` extends analytically to `|a| ≤ a₀`) and `ct:phic-exp`.
**Proved**, unconditional (`ε = ±1`):

* `exists_complex_extension`: a real-analytic `f : ℝ → ℝ` at `0` is the restriction of a function holomorphic on a disc and
  real-symmetric (complexification of the power series);
* `ctPsi_eq_psiOf`: near `0⁻` the Lean `ctPsi ε` equals `psiOf th = θ̂(z_A)/d(z_A)` (`τ₀ = √z_A`, `θ_ε(τ) = τ θ̂(τ²)`), analytic at `0`
  (`analyticAt_psiOf`);
* `ctPsiAnalytic`: `CtPsiAnalytic ε`;
* `ct_chart_complex`: `∃ c₁₀ > 0, ∀ 0 < c₁ ≤ c₁₀, CtChartComplex c₁` (via `ct_chart_complex_of_analytic`).
-/

@[expose] public section

open Complex Metric Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- **Complexification of a real-analytic germ.** -/
theorem exists_complex_extension {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ (ρ : ℝ) (F : ℂ → ℂ), 0 < ρ ∧ DifferentiableOn ℂ F (ball 0 ρ) ∧
      (∀ z ∈ ball (0 : ℂ) ρ, F (starRingEnd ℂ z) = starRingEnd ℂ (F z)) ∧
      ∀ x : ℝ, |x| < ρ → F (x : ℂ) = (f x : ℂ) := by
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨s0, hs0pos, hs0R⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hs0 : (0 : ℝ) < s0 := by exact_mod_cast hs0pos
  set a : ℕ → ℝ := fun j => p.coeff j with ha
  have hnorm : ∀ j, ‖p j‖ = |a j| := fun j => by rw [p.norm_apply_eq_norm_coef, Real.norm_eq_abs]
  set q : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (fun j => ((a j : ℝ) : ℂ)) with hq
  have hrad : (s0 : ENNReal) ≤ q.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
    refine q.le_radius_of_summable_norm ?_
    have h := p.summable_norm_mul_pow (r := t) (ht.trans_le (hs0R.le.trans hp.r_le))
    refine h.congr fun j => ?_
    rw [hq, FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, hnorm, Real.norm_eq_abs]
  have hqpos : 0 < q.radius := lt_of_lt_of_le (by exact_mod_cast hs0pos) hrad
  have hbq := q.hasFPowerSeriesOnBall hqpos
  have hmem : ∀ z : ℂ, ‖z‖ < s0 → z ∈ Metric.eball (0 : ℂ) q.radius := by
    intro z hz
    rw [Metric.mem_eball, edist_zero_right]
    have : (‖z‖₊ : ENNReal) < s0 := by
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnNorm]; exact hz
    exact this.trans_le hrad
  have hsum : ∀ z : ℂ, ‖z‖ < s0 → HasSum (fun j => ((a j : ℝ) : ℂ) * z ^ j) (q.sum z) := by
    intro z hz
    have h1 := hbq.hasSum (y := z) (hmem z hz)
    simp only [zero_add] at h1
    refine h1.congr_fun fun j => ?_
    rw [hq, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  refine ⟨s0, q.sum, hs0, ?_, ?_, ?_⟩
  · intro z hz
    refine (hbq.differentiableOn.mono ?_ z hz)
    intro w hw
    exact hmem w (by simpa using hw)
  · intro z hz
    have hz' : ‖z‖ < s0 := by simpa using hz
    have h1 := (hsum z hz').star
    have h2 := hsum (starRingEnd ℂ z) (by rw [Complex.norm_conj]; exact hz')
    have h1' : HasSum (fun j => ((a j : ℝ) : ℂ) * (starRingEnd ℂ z) ^ j) (starRingEnd ℂ (q.sum z)) := by
      refine h1.congr_fun fun j => ?_
      simp
    exact h2.unique h1'
  · intro x hx
    have hx' : ‖(x : ℂ)‖ < s0 := by simpa [Real.norm_eq_abs] using hx
    have h1 := hsum (x : ℂ) hx'
    have hxb : (x : ℝ) ∈ Metric.eball (0 : ℝ) R := by
      rw [Metric.mem_eball, edist_zero_right]
      have : (‖x‖₊ : ENNReal) < s0 := by
        rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnNorm, Real.norm_eq_abs]; exact hx
      exact this.trans hs0R
    have h2 := hp.hasSum hxb
    simp only [zero_add] at h2
    have h3 : HasSum (fun j => a j * x ^ j) (f x) := by
      refine h2.congr_fun fun j => ?_
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
    have h4 : HasSum (fun j => (((a j * x ^ j : ℝ)) : ℂ)) ((f x : ℝ) : ℂ) := Complex.hasSum_ofReal.mpr h3
    have h4' : HasSum (fun j => ((a j : ℝ) : ℂ) * (x : ℂ) ^ j) ((f x : ℝ) : ℂ) := by
      refine h4.congr_fun fun j => ?_
      push_cast; ring
    exact h1.unique h4'

open FormalResearch.SignUncertainty.CtCfu CtOuter in
/-- **`ctPsi ε` is `ψ_ε = θ̂(z_A)/d(z_A)` near `0⁻`** (`ct:psi-def`, Step 2 of `ct:cfu`), with `psiOf th` analytic at `0`. -/
lemma ctPsi_eq_psiOf {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ th : ℝ → ℝ, AnalyticAt ℝ th 0 ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ a ∈ Ioo (-ρ) 0, ctPsi ε a = psiOf th a := by
  obtain ⟨th, hth, hrel, -, -⟩ := theta_hat hε
  have htau : Tendsto tau0 (𝓝 0) (𝓝 0) := by
    have h : Tendsto tau0 (𝓝 0) (𝓝 (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp tendsto_zA
    rwa [Real.sqrt_zero] at h
  have hev : ∀ᶠ a in 𝓝 (0 : ℝ), (zA a ∈ Ioo (-rr) rr ∧ 0 < fF (zA a) ∧ AFp (zA a) ≠ 0) ∧ AF (zA a) = a :=
    zA_good.and AF_zA_eventually
  have hev2 : ∀ᶠ a in 𝓝 (0 : ℝ), outerTheta ε (tau0 a) = tau0 a * th (tau0 a ^ 2) := htau.eventually hrel
  obtain ⟨ρ3, hρ3, h3⟩ := Metric.eventually_nhds_iff.mp (hev.and hev2)
  refine ⟨th, hth, ρ3, hρ3, fun a ha => ?_⟩
  have ha3 : dist a 0 < ρ3 := by
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨ha.1, by linarith [ha.2, hρ3]⟩
  obtain ⟨⟨hg, hr⟩, hrel2⟩ := h3 ha3
  obtain ⟨h0, hm, hphi, hsq⟩ := tau0_props ha.2 hr hg
  have hspec : 0 < ctTau0 a ∧
      FormalResearch.CohnElkies.edgePhi (hankelEdgeM (ctTau0 a)) (ctTau0 a) = (2 / 3) * (-a) ^ ((3 : ℝ) / 2) :=
    Classical.epsilon_spec (p := fun τ : ℝ => 0 < τ ∧
      FormalResearch.CohnElkies.edgePhi (hankelEdgeM τ) τ = (2 / 3) * (-a) ^ ((3 : ℝ) / 2)) ⟨tau0 a, h0, hphi⟩
  have hct : ctTau0 a = tau0 a := by
    have hmono := critical_value_strictMonoOn
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hmono (mem_Ici.mpr hspec.1.le) (mem_Ici.mpr h0.le) hlt
      simp only at this
      linarith [hspec.2]
    · have := hmono (mem_Ici.mpr h0.le) (mem_Ici.mpr hspec.1.le) hgt
      simp only at this
      linarith [hspec.2]
  unfold ctPsi psiOf
  rw [hct, hrel2, hsq]
  have hz := zA_pos ha.2 hr
  have hτ2 : tau0 a ^ 2 = zA a := Real.sq_sqrt hz.le
  rw [hτ2]
  have hdpos : 0 < dF (zA a) := by
    obtain ⟨-, h2, -⟩ := hg
    unfold dF; positivity
  field_simp

/-- **`ψ_ε` is analytic across `a = 0`** (`ct:cfu` Step 2: `ψ_ε(a) = h_ε(-a, a)`; `ct:psi-def`), for `ε = ±1`. -/
theorem ctPsiAnalytic {ε : ℝ} (hε : ε = 1 ∨ ε = -1) : CtPsiAnalytic ε := by
  obtain ⟨th, hth, ρ1, hρ1, heq⟩ := ctPsi_eq_psiOf hε
  obtain ⟨ρ2, F, hρ2, hd, hconj, hval⟩ := exists_complex_extension (CtCfu.analyticAt_psiOf hth)
  refine ⟨min ρ1 ρ2, F, lt_min hρ1 hρ2, hd.mono (ball_subset_ball (min_le_right _ _)),
    fun z hz => hconj z (ball_subset_ball (min_le_right _ _) hz), fun a h1 h2 => ?_⟩
  have ha1 : -ρ1 < a := lt_of_le_of_lt (by linarith [min_le_left ρ1 ρ2]) h1
  have ha2 : |a| < ρ2 := by
    rw [abs_of_neg h2]; linarith [min_le_right ρ1 ρ2]
  rw [hval a ha2, heq a ⟨ha1, h2⟩]

/-- **The complex chart `φ_c = û⁻¹` of `ct:cfu`** (`CtChartComplex`; `ct:phic-exp`): there is `c₁₀ > 0` such that for every
`0 < c₁ ≤ c₁₀` the holomorphic continuation of the Langer chart to a disc of radius `> R_max = 4c₁²c^{2/3}` exists, is real on the real
axis, and satisfies `|φ_c(u) - u| ≤ C c^{-1/3}`, `|φ_c'(u) - 1| ≤ C c^{-1}` for `|u| ≤ R_max`, `c ≥ c₀(c₁)`; unconditional. -/
theorem ct_chart_complex : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → CtChartComplex c₁ :=
  ct_chart_complex_of_analytic (ctPsiAnalytic (Or.inl rfl)) (ctPsiAnalytic (Or.inr rfl))

/-- info: 'FormalResearch.SignUncertainty.ct_chart_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_chart_complex

end FormalResearch.SignUncertainty
