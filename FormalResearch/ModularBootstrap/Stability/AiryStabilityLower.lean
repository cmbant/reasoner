module

public import FormalResearch.ModularBootstrap.Stability.AiryStabilityBase
public import FormalResearch.SignUncertainty.RadialRigidity

/-!
# Theorem B-stab (`rem:thmBstab`), lower bound

Source: `CFT/modular_bootstrap/paper/remainder.tex`, Theorem B-stab; proof of
`soft_edge_two_level_stability.tex`, Theorem `se:terminal-stability` (lower bound), at `m = 1`.

`airy_stab_lower`: for every `θ < 1/‖G_Ai‖₁` there is `δ₀ > 0` such that for `0 < δ < δ₀` and every
`0 ≠ f ∈ 𝒢` with `f ≥ 0` on `(-∞, a₁ + δ]`,
`θ δ ≤ ∫ f / ‖f‖₁`.

Proof (the paper's): a counterexample sequence, normalised to `‖f_n‖₁ = 1`, satisfies the density
hypotheses (`AiryG.densityHyp`, sharp envelope of Theorem Q (2)), so by `Blowup.airy_norm_limit_deriv`
it converges with its first derivative locally uniformly to `G_Ai/‖G_Ai‖₁` (the equality case of
Theorem B).  The sign `f_n(a₁ + δ_n) ≥ 0` and the mean value theorem give
`f_n(a₁) ≥ δ_n (Ai'(a₁)²/‖G_Ai‖₁ - o(1))`, and the quadrature `∫ f_n ≥ f_n(a₁)/Ai'(a₁)²`
(`AiryG.quadrature_ge`) gives `∫ f_n ≥ δ_n (1/‖G_Ai‖₁ - o(1))`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Stability

open FormalResearch.Special FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.SignUncertainty

/-- The value of `(G_Ai/‖G_Ai‖₁)'` at `a₁`. -/
lemma airyProfile_deriv_re :
    (deriv airyProfile (airyZero 1 : ℂ)).re = -(airyAi' (airyZero 1)) ^ 2 / profileMass airyExtremal := by
  have hd : HasDerivAt airyProfile ((((profileMass airyExtremal)⁻¹ : ℝ) : ℂ) *
      deriv airyExtremal (airyZero 1 : ℂ)) (airyZero 1 : ℂ) :=
    (differentiable_airyExtremal (airyZero 1 : ℂ)).hasDerivAt.const_mul _
  rw [hd.deriv, airyExtremal_deriv_airyZero_one, deriv_airyAiC_ofReal]
  rw [show -((airyAi' (airyZero 1) : ℂ)) ^ 2 = (((-(airyAi' (airyZero 1)) ^ 2 : ℝ)) : ℂ) by
    push_cast; ring, Complex.re_ofReal_mul, Complex.ofReal_re]
  ring

theorem airy_stab_lower {θ : ℝ} (hθ : θ < (profileMass airyExtremal)⁻¹) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ f : ℂ → ℂ, AiryG f →
      (∃ x : ℝ, f (x : ℂ) ≠ 0) → (∀ x : ℝ, x ≤ airyZero 1 + δ → 0 ≤ (f (x : ℂ)).re) →
      θ * δ ≤ (∫ x : ℝ, (f (x : ℂ)).re) / ∫ x : ℝ, ‖f (x : ℂ)‖ := by
  set M := profileMass airyExtremal with hM
  have hMpos : 0 < M := airyExtremalProfile.mass_pos
  have hMinv : 0 < M⁻¹ := inv_pos.mpr hMpos
  by_cases hθ0 : θ ≤ 0
  · refine ⟨1, one_pos, fun δ hδ _ f hf hne hnn => ?_⟩
    have h1 := (hf.quadrature_ge (fun x hx => hnn x (by linarith))).1
    have h2 : 0 ≤ ∫ x : ℝ, ‖f (x : ℂ)‖ := integral_nonneg fun x => norm_nonneg _
    have : θ * δ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hθ0 hδ.le
    exact this.trans (div_nonneg h1 h2)
  push Not at hθ0
  by_contra hcon
  push Not at hcon
  -- a counterexample sequence
  have hseq : ∀ n : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 / ((n : ℝ) + 1) ∧ ∃ f : ℂ → ℂ, AiryG f ∧
      (∃ x : ℝ, f (x : ℂ) ≠ 0) ∧ (∀ x : ℝ, x ≤ airyZero 1 + δ → 0 ≤ (f (x : ℂ)).re) ∧
      (∫ x : ℝ, (f (x : ℂ)).re) / (∫ x : ℝ, ‖f (x : ℂ)‖) < θ * δ := by
    intro n
    obtain ⟨δ, h1, h2, f, hf, hne, hnn, hlt⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨δ, h1, h2, f, hf, hne, hnn, hlt⟩
  choose δ hδ0 hδlt f hf hne hnn hlt using hseq
  -- normalisation
  set N : ℕ → ℝ := fun n => ∫ x : ℝ, ‖f n (x : ℂ)‖ with hN
  have hNpos : ∀ n, 0 < N n := fun n => by
    obtain ⟨x, hx⟩ := hne n
    exact integral_norm_pos_of_ne_zero (hf n).diff (hf n).integrable hx
  set g : ℕ → ℂ → ℂ := fun n u => (((N n)⁻¹ : ℝ) : ℂ) * f n u with hg
  have hgG : ∀ n, AiryG (g n) := fun n => (hf n).smul _
  have hgn : ∀ n, ∫ x : ℝ, ‖g n (x : ℂ)‖ = 1 := by
    intro n
    simp only [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hNpos n))]
    rw [integral_const_mul]
    exact inv_mul_cancel₀ (hNpos n).ne'
  have hgnn : ∀ n x, x ≤ airyZero 1 + δ n → 0 ≤ (g n (x : ℂ)).re := by
    intro n x hx
    simp only [hg, Complex.re_ofReal_mul]
    exact mul_nonneg (inv_nonneg.mpr (hNpos n).le) (hnn n x hx)
  have hgint : ∀ n, ∫ x : ℝ, (g n (x : ℂ)).re = (N n)⁻¹ * ∫ x : ℝ, (f n (x : ℂ)).re := by
    intro n
    simp only [hg, Complex.re_ofReal_mul]
    exact integral_const_mul _ _
  have hε0 : ∀ n, 0 ≤ ∫ x : ℝ, (g n (x : ℂ)).re := fun n =>
    ((hgG n).quadrature_ge fun x hx => hgnn n x (by linarith [hδ0 n])).1
  have hεlt : ∀ n, ∫ x : ℝ, (g n (x : ℂ)).re < θ * δ n := fun n => by
    rw [hgint n, ← div_eq_inv_mul]; exact hlt n
  have hδtend : Tendsto δ atTop (𝓝 0) := by
    refine squeeze_zero (fun n => (hδ0 n).le) (fun n => (hδlt n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- the density sequence
  set R : ℕ → ℝ := fun n => (n : ℝ) + 1 + |airyZero 1| with hR
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have := abs_nonneg (airyZero 1); have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); simp only [hR]; linarith
  have hRtend : Tendsto R atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    have := abs_nonneg (airyZero 1); simp only [hR]; linarith
  have hε_tend : Tendsto (fun n => ∫ x : ℝ, (g n (x : ℂ)).re) atTop (𝓝 0) := by
    refine squeeze_zero hε0 (fun n => (hεlt n).le) ?_
    simpa using hδtend.const_mul θ
  have hτ_tend : Tendsto (fun n => tailBound (4 * π)⁻¹ (R n)) atTop (𝓝 0) :=
    (tailBound_tendsto_real _).comp hRtend
  have hS : DensitySeq (4 * π)⁻¹ R (fun _ => 0)
      (fun n => (∫ x : ℝ, (g n (x : ℂ)).re) + tailBound (4 * π)⁻¹ (R n)) g
      (fun n => airyZero 1 + δ n) :=
    { hC0 := by positivity
      hR := hRtend
      hς0 := Eventually.of_forall fun _ => le_rfl
      hς := tendsto_const_nhds
      hδ := by simpa using hε_tend.add hτ_tend
      hspec := fun n => (hgG n).densityHyp (hgn n) (hR1 n)
        (by have := abs_nonneg (airyZero 1); have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
            have := hδ0 n
            have hle := neg_abs_le (airyZero 1)
            simp only [hR]; linarith) (hgnn n) (hε0 n) }
  have hbd : ∃ x₀, ∀ n, x₀ ≤ airyZero 1 + δ n := ⟨airyZero 1, fun n => by linarith [hδ0 n]⟩
  have huT : ∀ x < airyZero 1, ∀ᶠ n in atTop, x ≤ airyZero 1 + δ n := fun x hx =>
    Eventually.of_forall fun n => by linarith [hδ0 n]
  -- derivative convergence on a compact interval around `a₁`
  set m : ℕ := ⌈|airyZero 1|⌉₊ + 2 with hm
  have hmball : ∀ x ∈ Icc (airyZero 1) (airyZero 1 + 1), ((x : ℝ) : ℂ) ∈ ball (0 : ℂ) ((m : ℝ) + 1) := by
    intro x hx
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |airyZero 1| ≤ (⌈|airyZero 1|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : |x| ≤ |airyZero 1| + 1 := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2, neg_abs_le (airyZero 1), le_abs_self (airyZero 1)]
    simp only [hm, Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hderiv := airy_norm_limit_deriv hS hbd huT m
  have hK : IsCompact ((fun x : ℝ => (x : ℂ)) '' Icc (airyZero 1) (airyZero 1 + 1)) :=
    isCompact_Icc.image continuous_ofReal
  have hKsub : ((fun x : ℝ => (x : ℂ)) '' Icc (airyZero 1) (airyZero 1 + 1)) ⊆
      ball (0 : ℂ) ((m : ℝ) + 1) := by
    rintro _ ⟨x, hx, rfl⟩; exact hmball x hx
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hderiv _ hKsub hK
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  -- continuity of `deriv airyProfile` at `a₁`
  have hPd : Differentiable ℂ airyProfile := normProfile_differentiable airyExtremalProfile
  have hPcont : ContinuousAt (fun x : ℝ => (deriv airyProfile (x : ℂ)).re) (airyZero 1) :=
    (Complex.continuous_re.comp (hPd.deriv.continuous.comp continuous_ofReal)).continuousAt
  have hc₁ : 0 < (airyAi' (airyZero 1)) ^ 2 := by
    have h := airyZero_deriv_ne_zero 1
    rw [deriv_airyAiC_ofReal] at h
    have h' : airyAi' (airyZero 1) ≠ 0 := by exact_mod_cast h
    positivity
  set c₁ := (airyAi' (airyZero 1)) ^ 2 with hc₁def
  set ε' : ℝ := (M⁻¹ - θ) * c₁ / 4 with hε'
  have hε'pos : 0 < ε' := by
    have : 0 < M⁻¹ - θ := by linarith
    positivity
  obtain ⟨ρ, hρ, hρP⟩ := Metric.continuousAt_iff.mp hPcont ε' hε'pos
  have hev1 := hunif ε' hε'pos
  have hev2 : ∀ᶠ n in atTop, δ n < min ρ 1 := hδtend.eventually (gt_mem_nhds (lt_min hρ one_pos))
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  -- mean value theorem on `[a₁, a₁ + δ_n]`
  have hδn := hδ0 n
  have hδρ : δ n < ρ := lt_of_lt_of_le hn2 (min_le_left _ _)
  have hδ1 : δ n < 1 := lt_of_lt_of_le hn2 (min_le_right _ _)
  set φ : ℝ → ℝ := fun t => (g n (t : ℂ)).re with hφ
  have hφd : ∀ x : ℝ, HasDerivAt φ ((deriv (g n) (x : ℂ)).re) x := fun x =>
    hasDerivAt_re_ofReal (hgG n).diff x
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope φ (fun x => (deriv (g n) (x : ℂ)).re)
    (show airyZero 1 < airyZero 1 + δ n by linarith)
    (fun x _ => (hφd x).continuousAt.continuousWithinAt) (fun x _ => hφd x)
  have hξK : ξ ∈ Icc (airyZero 1) (airyZero 1 + 1) := ⟨hξ.1.le, by linarith [hξ.2]⟩
  have hξdist : dist (deriv (g n) (ξ : ℂ)) (deriv airyProfile (ξ : ℂ)) < ε' := by
    have := hn1 (ξ : ℂ) ⟨ξ, hξK, rfl⟩
    rwa [dist_comm] at this
  have hξre : (deriv (g n) (ξ : ℂ)).re ≤ (deriv airyProfile (airyZero 1 : ℂ)).re + 2 * ε' := by
    have h1 : |(deriv (g n) (ξ : ℂ)).re - (deriv airyProfile (ξ : ℂ)).re| < ε' := by
      have hre : |(deriv (g n) (ξ : ℂ) - deriv airyProfile (ξ : ℂ)).re| ≤
          ‖deriv (g n) (ξ : ℂ) - deriv airyProfile (ξ : ℂ)‖ := Complex.abs_re_le_norm _
      have hlt' : ‖deriv (g n) (ξ : ℂ) - deriv airyProfile (ξ : ℂ)‖ < ε' := by
        simpa [dist_eq_norm] using hξdist
      simpa [Complex.sub_re] using lt_of_le_of_lt hre hlt'
    have h2 : |(deriv airyProfile (ξ : ℂ)).re - (deriv airyProfile (airyZero 1 : ℂ)).re| < ε' := by
      have := hρP (x := ξ) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hξ.1, hξ.2])
      simpa [Real.dist_eq] using this
    rw [abs_lt] at h1 h2
    linarith [h1.2, h2.2]
  -- `φ(a₁ + δ) ≥ 0`, hence `φ(a₁) ≥ -δ (P'(a₁) + 2ε')`
  have hφtop : 0 ≤ φ (airyZero 1 + δ n) := hgnn n _ le_rfl
  have hslope : (φ (airyZero 1 + δ n) - φ (airyZero 1)) = δ n * (deriv (g n) (ξ : ℂ)).re := by
    rw [hξeq, show airyZero 1 + δ n - airyZero 1 = δ n by ring]
    field_simp
  have hφa : -(δ n * ((deriv airyProfile (airyZero 1 : ℂ)).re + 2 * ε')) ≤ φ (airyZero 1) := by
    have := mul_le_mul_of_nonneg_left hξre hδn.le
    linarith
  rw [airyProfile_deriv_re] at hφa
  -- quadrature
  have hquad := ((hgG n).quadrature_ge fun x hx => hgnn n x (by linarith [hδ0 n])).2
  have hφa' : δ n * (c₁ / M - 2 * ε') ≤ φ (airyZero 1) := by
    refine le_trans (le_of_eq ?_) hφa
    rw [hc₁def]; ring
  have hint_lb : δ n * (M⁻¹ - 2 * ε' / c₁) ≤ ∫ x : ℝ, (g n (x : ℂ)).re := by
    refine le_trans ?_ hquad
    rw [le_div_iff₀ hc₁]
    refine le_trans (le_of_eq ?_) hφa'
    field_simp
  have hfin := lt_of_le_of_lt hint_lb (hεlt n)
  have hcancel : M⁻¹ - 2 * ε' / c₁ < θ := by
    have := (mul_lt_mul_iff_of_pos_left hδn).mp (by linarith [hfin] : δ n * (M⁻¹ - 2 * ε' / c₁) < δ n * θ)
    exact this
  have hcalc : 2 * ε' / c₁ = (M⁻¹ - θ) / 2 := by rw [hε']; field_simp; ring
  rw [hcalc] at hcancel
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Stability.airy_stab_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_stab_lower

end FormalResearch.ModularBootstrap.Stability
