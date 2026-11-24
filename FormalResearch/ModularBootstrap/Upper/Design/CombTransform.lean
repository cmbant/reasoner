module

public import FormalResearch.ModularBootstrap.Upper.Design.DesignCombProps
public import FormalResearch.ModularBootstrap.Upper.Design.AmplitudeLogDeriv
public import FormalResearch.ModularBootstrap.Upper.Saddle.EdgePhaseZero
public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeGlobalBound
public import FormalResearch.ModularBootstrap.Upper.Design.CombTransformAbs

/-!
# Lemma `Φ`, "Consequently": the transform of a finite modification of the comb

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Lemma `Φ` (`ut:Phi`): "`h₀ = sech²(πb/2)
B_D^{(f)}` satisfies all hypotheses of Lemma `SD_H`, `SD_G`, `SD_0` and `SD_V` on `𝒩` with uniform
constants; hence on `x ≥ ξ_I = ξ_* + c'^{-θ}` (any fixed `θ < 2/3`),
`|ĥ₀(c'x²/3)| ≤ 𝒜_x (1 + O(c'^{-1+3θ/2}))`".

* `designProfile`: `h₀ = sech²(πb/2) B_D^{(f)}` (`designComb`, `Design.PerturbP`);
  `designPhi1 = Φ₁^{(f)} + Δ_D`; `combAmplitude` = the comb-independent amplitude `𝒜_x` of `(SD.4)`
  (the `sdvPrefactor` with `Φ₁ = 0`; for the design `Re Φ₁ = 0` on `E₊`, so it is the true prefactor).
* `designProfile_edgeHankelHyp`: hypotheses of `SD_H` (`EdgeHankelHyp h₀ π 8`), whence the Hankel
  edge representation (`edge_hankel_representation`) and `SD_G` (`designProfile_global_bound`).
* `designProfile_sdvHypotheses`: `SDVHypotheses` for `h₀`, with `Φ₀ = edgePhi0Blaschke`
  (`edgePhaseData_blaschke`, `SD_0`), `Φ₁ = designPhi1`, `H₀ = hankel0`, `ε_H = hankelEps`,
  `δ = 1/8`, and constants `M, M'` uniform in `c'`, in the family and in `x ≥ ξ_*`.
* `lemma_Phi_transform`: the final bound
  `‖ĥ₀(c'x²/3)‖ ≤ 𝒜_x (1 + C c'^{-1+3θ/2})` for `x ≥ ξ_* + c'^{-θ}`, `0 < θ < 2/3`.

**Differences with the paper.**  The formal `SD_V` is applied with `δ = 1/8` instead of `δ = 1/4`
(the formal `EdgePhaseData` is proved for `δ < 1/4`).  `SD_V` needs `|h| ≤ C e^{-a|v|}` only on
`1/2 - δ ≤ Im b ≤ 1/2` (where `|B_D| ≤ 1`), as in the paper; `SD_H` needs it on all of
`0 ≤ Im b ≤ 1/2`, again with `|B_D| ≤ 1`; `h` is required continuous up to the real axis.

Each of these has an `_of_decomp` / `_of_admissible` form for an abstract finite modification whose
`DesignPhiDecomp` carries a derivative bound `B` independent of `c'` and of the cut `N` (the form needed when `N`
grows with `c'`, e.g. the ramped comb): the thresholds in `c'` and the constants depend on `f`, `B` (and `θ`) only.
The compact-family statements above are corollaries (with `B = C λ ≤ C` from `lemma_Phi_b`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Design

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle

/-! ### 1. Definitions -/

/-- `Φ₁^{(f)} + Δ_D`. -/
noncomputable def designPhi1 (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) (b : ℂ) : ℂ :=
  phi1Comb c' f η₀ b + designDelta c' f N η₀ σ ε b

/-- `h₀ = sech²(π b / 2) B_D^{(f)}(b)`. -/
noncomputable def designProfile (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) (b : ℂ) : ℂ :=
  sechSqProfile b * designComb c' f N η₀ σ ε b

/-! ### 2. Differentiability of `Φ₁^{(f)}` -/

lemma phi1Comb_eq_phi1CombDeriv_zero (c' : ℝ) (f : ℕ) (η₀ : ℝ) :
    phi1Comb c' f η₀ = phi1CombDeriv 0 c' f η₀ := by
  funext w
  simp [phi1Comb, phi1CombDeriv, barPhi, barPhiDeriv, deltaDetComb, deltaDetCombDeriv,
    emRem, emRemDeriv, combPhiDeriv_zero]

lemma hasDerivAt_phi1Comb {c' : ℝ} (hc' : 0 < c') (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) (hgap_half : siteGap c' 1 ≤ 1 / 2)
    (hgap_k : ∀ k : ℕ, 1 ≤ k → siteGap c' k ≤ siteGap c' 1) {b : ℂ} (hb : b ∈ combNMid) :
    HasDerivAt (phi1Comb c' f η₀) (phi1CombDeriv 1 c' f η₀ b) b := by
  rw [phi1Comb_eq_phi1CombDeriv_zero]
  have hd1 : HasDerivAt (fun _ : ℂ => (if (0 : ℕ) = 0 then (π : ℂ) * Complex.I else 0)) 0 b :=
    hasDerivAt_const _ _
  have hd2 := (hasDerivAt_barPhiDeriv (i := 0) (by omega) hc' f hf hb).const_mul
    ((2 * n1Comb f : ℝ) : ℂ)
  have hd3 := hasDerivAt_deltaDetCombDeriv (i := 0) (by omega) hc' f hf hη₀0 hη₀1 hgap_half hgap_k hb
  have hd4 := hasDerivAt_emRemDeriv (i := 0) (by omega) hc' f hf hb
  have htot := ((hd1.sub hd2).add hd3).add hd4
  exact htot.congr_deriv (by unfold phi1CombDeriv; simp)

lemma differentiableOn_phi1Comb {c' : ℝ} (hc' : 0 < c') (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ}
    (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) (hgap_half : siteGap c' 1 ≤ 1 / 2)
    (hgap_k : ∀ k : ℕ, 1 ≤ k → siteGap c' k ≤ siteGap c' 1) :
    DifferentiableOn ℂ (phi1Comb c' f η₀) combNMid := fun _ hb =>
  (hasDerivAt_phi1Comb hc' f hf hη₀0 hη₀1 hgap_half hgap_k hb).differentiableAt.differentiableWithinAt

lemma differentiableOn_designDelta {c' : ℝ} {f N : ℕ} {η₀ : ℝ} {σ ε : ℕ → ℝ}
    (hA : DesignAdmissible c' f N η₀ σ ε) :
    DifferentiableOn ℂ (designDelta c' f N η₀ σ ε) combNOpen := by
  rw [designDelta_eq_dphi]
  intro b hb
  have hzf := ofReal_memCombZ hA.first
  have hzf0 := ofReal_memCombZ hA.ref_first
  have hpl : ∀ j ∈ Finset.range (N - f),
      ((designSite c' σ (f + 1 + j) : ℂ) + (ε (f + 1 + j) : ℂ) * Complex.I) ∈ combZ ∧
      ((designSite c' σ (f + 1 + j) : ℂ) - (ε (f + 1 + j) : ℂ) * Complex.I) ∈ combZ ∧
      ((chiQuantile c' ((f + 1 + j : ℕ) : ℝ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + j) : ℝ) : ℂ) * Complex.I) ∈ combZ ∧
      ((chiQuantile c' ((f + 1 + j : ℕ) : ℝ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + j) : ℝ) : ℂ) * Complex.I) ∈ combZ := fun j hj => by
    have hj' := Finset.mem_range.mp hj
    exact ⟨memCombZ_of_re_nonneg (hA.site j hj') (hA.width j hj'),
      memCombZ_of_re_nonneg' (hA.site j hj') (hA.width j hj'),
      memCombZ_of_re_nonneg (hA.ref_site j hj') (hA.ref_width j hj'),
      memCombZ_of_re_nonneg' (hA.ref_site j hj') (hA.ref_width j hj')⟩
  have hd : ∀ ζ' ζ : ℂ, ζ' ∈ combZ → ζ ∈ combZ → DifferentiableAt ℂ (dphi ζ' ζ) b := fun ζ' ζ h' h => by
    unfold dphi
    exact ((hasDerivAt_phiZeta_b hb (combZ_subset_combZOpen h')).differentiableAt).sub
      ((hasDerivAt_phiZeta_b hb (combZ_subset_combZOpen h)).differentiableAt)
  refine DifferentiableAt.differentiableWithinAt ?_
  refine (hd _ _ hzf hzf0).add (DifferentiableAt.fun_sum fun j hj => ?_)
  exact (hd _ _ (hpl j hj).1 (hpl j hj).2.2.1).add (hd _ _ (hpl j hj).2.1 (hpl j hj).2.2.2)

/-- **Uniform bounds for `Φ₁^{(f)} + Δ_D`, from a phase decomposition.**  There is `A ≥ 0` (depending on `f`
only: `A = C₁ n₁^{(f)}`, Lemma `K3`) such that for `c'` large (threshold independent of the cut `N`), every
admissible finite modification with `DesignPhiDecomp c' f N η₀ σ ε B` (any `B`) has `Φ₁ = Φ₁^{(f)} + Δ_D`
holomorphic on `combNMid` and its first two derivatives bounded by `A + B` on `𝒩`. -/
theorem designPhi1_bounds_of_decomp (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ) (B : ℝ),
      DesignAdmissible c' f N η₀ σ ε → DesignPhiDecomp c' f N η₀ σ ε B →
      DifferentiableOn ℂ (designPhi1 c' f N η₀ σ ε) combNMid ∧
      ∀ b ∈ combN, ‖deriv (designPhi1 c' f N η₀ σ ε) b‖ ≤ A + B ∧
        ‖deriv (deriv (designPhi1 c' f N η₀ σ ε)) b‖ ≤ A + B := by
  obtain ⟨C₁, hC₁, hK3⟩ := edgePhase_bounds
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  have hn1 : 0 ≤ n1Comb f := by
    unfold n1Comb
    have : (1 : ℝ) ≤ f := by exact_mod_cast hf
    linarith
  refine ⟨C₁ * n1Comb f, by positivity, ?_⟩
  filter_upwards [hK3, h_ev, eventually_gt_atTop 0] with c' hK
    ⟨hgap_k, hgap_1_bd, hcd1_bd, hgap_1⟩ hc' N σ ε B hA hDec
  have hphi := differentiableOn_phi1Comb hc' f hf hη₀0 hη₀1 hgap_1 hgap_k
  have hdelta := differentiableOn_designDelta hA
  have hΦ1 : DifferentiableOn ℂ (designPhi1 c' f N η₀ σ ε) combNMid := by
    intro b hb
    exact (hphi b hb).add ((hdelta.mono combNMid_subset_combNOpen) b hb)
  refine ⟨hΦ1, fun b hb => ?_⟩
  have hbm := combN_subset_combNMid hb
  have hbo := combNMid_subset_combNOpen hbm
  have hcd1 : ContDiffAt ℂ 2 (phi1Comb c' f η₀) b :=
    ((hphi.analyticOnNhd isOpen_combNMid) b hbm).contDiffAt
  have hcd2 : ContDiffAt ℂ 2 (designDelta c' f N η₀ σ ε) b :=
    ((hdelta.analyticOnNhd isOpen_combNOpen) b hbo).contDiffAt
  have hsum : ∀ i : ℕ, i ≤ 2 → iteratedDeriv i (designPhi1 c' f N η₀ σ ε) b =
      iteratedDeriv i (phi1Comb c' f η₀) b + iteratedDeriv i (designDelta c' f N η₀ σ ε) b :=
    fun i hi => iteratedDeriv_fun_add (hcd1.of_le (by exact_mod_cast hi))
      (hcd2.of_le (by exact_mod_cast hi))
  have hbd : ∀ i : ℕ, i ≤ 2 → ‖iteratedDeriv i (designPhi1 c' f N η₀ σ ε) b‖ ≤
      C₁ * n1Comb f + B := fun i hi => by
    rw [hsum i hi]
    refine (norm_add_le _ _).trans ?_
    have h1 := (hK f hf hη₀0 hη₀1 i hi hb).2.1
    have h2 := hDec.2.2.2 i hi b hb
    linarith
  have e1 : deriv (designPhi1 c' f N η₀ σ ε) b = iteratedDeriv 1 (designPhi1 c' f N η₀ σ ε) b := by
    rw [iteratedDeriv_one]
  have e2 : deriv (deriv (designPhi1 c' f N η₀ σ ε)) b =
      iteratedDeriv 2 (designPhi1 c' f N η₀ σ ε) b := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [e1, e2]
  exact ⟨hbd 1 (by norm_num), hbd 2 le_rfl⟩

/-- Uniform bounds for `Φ₁^{(f)} + Δ_D` on `𝒩`: it is holomorphic on `|Im b - 1/2| < 17/64`, and its
first two derivatives are bounded on `𝒩` uniformly in `c'` and in the family (`K3` for `Φ₁^{(f)}`,
`lemma_Phi_b` for `Δ_D`). -/
theorem designPhi1_bounds (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) (hE : 0 ≤ E) {η₀ : ℝ}
    (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      DesignAdmissible c' f N η₀ σ ε ∧
      DifferentiableOn ℂ (designPhi1 c' f N η₀ σ ε) combNMid ∧
      DesignPhiDecomp c' f N η₀ σ ε B ∧
      ∀ b ∈ combN, ‖deriv (designPhi1 c' f N η₀ σ ε) b‖ ≤ B ∧
        ‖deriv (deriv (designPhi1 c' f N η₀ σ ε)) b‖ ≤ B := by
  obtain ⟨A, hA0, hAev⟩ := designPhi1_bounds_of_decomp f hf hη₀0 hη₀1
  obtain ⟨CΦ, hCΦ, hΦ⟩ := lemma_Phi_b f N hf hfN M E hE hη₀0 hη₀1
  refine ⟨A + CΦ, by positivity, ?_⟩
  filter_upwards [hAev, hΦ, designAdmissible_eventually f N hf hfN M E hη₀0 hη₀1,
    tendsto_lambdaComb_atTop.eventually_le_const (zero_lt_one : (0 : ℝ) < 1)]
    with c' hAb hD hAd hlam1 σ ε hσ hε
  have hA := hAd σ ε hσ hε
  have hDec : DesignPhiDecomp c' f N η₀ σ ε CΦ :=
    (hD σ ε hσ hε).mono (by nlinarith)
  obtain ⟨hdiff, hder⟩ := hAb N σ ε CΦ hA hDec
  exact ⟨hA, hdiff, hDec.mono (by linarith), fun b hb => hder b hb⟩

/-! ### 3. Hypotheses of `SD_H` and `SD_G` -/

/-- The hypotheses of Lemma `SD_H` for `h₀ = sech² B_D^{(f)}` (`a = π`, `C = 8`), and `|B_D| = 1`
on `E₊` (the input of `SD_G`), for every admissible finite modification, for `c'` large with a threshold
independent of the cut `N` and of the data. -/
theorem designProfile_edgeHankelHyp_of_admissible (f : ℕ) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ), DesignAdmissible c' f N η₀ σ ε →
      EdgeHankelHyp (designProfile c' f N η₀ σ ε) π 8 ∧
      (∀ v : ℝ, ‖designComb c' f N η₀ σ ε ((v : ℂ) + Complex.I / 2)‖ = 1) := by
  filter_upwards [combTail_K1a_unif hη₀0 hη₀1] with c' hT N σ ε hA
  obtain ⟨hT1, hT2, hT3, _⟩ := hT N
  obtain ⟨hK1, hK2, hK3⟩ := designComb_K1a hA hT1 hT2 hT3
  refine ⟨?_, fun v => hK2 (by simp [abs_of_pos])⟩
  refine ⟨fun r => ?_, ?_, ?_, fun b h0 h1 => ?_⟩
  · unfold designProfile
    rw [edgeHankelHyp_sech.even r, designComb_neg]
  · unfold designProfile
    exact edgeHankelHyp_sech.holo.mul (hK3.mono fun b hb => by
      have : |b.im| < 7 / 8 := by
        rw [abs_of_pos hb.1]; linarith [hb.2]
      exact this)
  · unfold designProfile
    exact edgeHankelHyp_sech.cont.mul (hK3.continuousOn.mono fun b hb => by
      have : |b.im| < 7 / 8 := by
        rw [abs_of_nonneg hb.1]; linarith [hb.2]
      exact this)
  · unfold designProfile
    rw [norm_mul]
    have h2 := edgeHankelHyp_sech.decay b h0 h1
    have h3 : ‖designComb c' f N η₀ σ ε b‖ ≤ 1 := hK1 (by rw [abs_of_nonneg h0]; exact h1)
    calc ‖sechSqProfile b‖ * ‖designComb c' f N η₀ σ ε b‖ ≤ (8 * Real.exp (-π * |b.re|)) * 1 :=
          mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
      _ = 8 * Real.exp (-π * |b.re|) := mul_one _

/-- The hypotheses of Lemma `SD_H` for `h₀ = sech² B_D^{(f)}` (`a = π`, `C = 8`), and `|B_D| = 1`
on `E₊` (the input of `SD_G`), uniformly over the compact family. -/
theorem designProfile_edgeHankelHyp (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) {η₀ : ℝ}
    (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      EdgeHankelHyp (designProfile c' f N η₀ σ ε) π 8 ∧
      (∀ v : ℝ, ‖designComb c' f N η₀ σ ε ((v : ℂ) + Complex.I / 2)‖ = 1) := by
  filter_upwards [designAdmissible_eventually f N hf hfN M E hη₀0 hη₀1,
    designProfile_edgeHankelHyp_of_admissible f hη₀0 hη₀1] with c' hAd h σ ε hσ hε
  exact h N σ ε (hAd σ ε hσ hε)

/-- **Lemma `SD_G` for `h₀ = sech² B_D^{(f)}`, any admissible finite modification**: with the absolute
constant `K` of `edge_global_bound`, `e^{c'L(x)} ‖ĥ₀(c'x²/3)‖ ≤ K √(c'/x)` for all `x > 0`, for `c'` large
(threshold independent of the cut `N` and of the data). -/
theorem designProfile_global_bound_of_admissible (f : ℕ) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ), DesignAdmissible c' f N η₀ σ ε →
      ∀ x : ℝ, 0 < x → Real.exp (c' * edgeL x) *
        ‖edgeHankel c' (designProfile c' f N η₀ σ ε) (c' * x ^ 2 / 3)‖ ≤ K * √(c' / x) := by
  obtain ⟨K, hK0, hK⟩ := edge_global_bound
  refine ⟨K, hK0, ?_⟩
  filter_upwards [designProfile_edgeHankelHyp_of_admissible f hη₀0 hη₀1, eventually_gt_atTop 0]
    with c' hP hc' N σ ε hA x hx
  obtain ⟨hh, hB⟩ := hP N σ ε hA
  have hsech : EdgeSechBound (designProfile c' f N η₀ σ ε) 1 :=
    edgeSechBound_of_unit (B := designComb c' f N η₀ σ ε) hB
  have := hK (designProfile c' f N η₀ σ ε) π 8 1 Real.pi_pos hh zero_le_one hsech c' x hc' hx
  simpa using this

/-- **Lemma `SD_G` for `h₀ = sech² B_D^{(f)}`**: with the absolute constant `K` of
`edge_global_bound`, `e^{c'L(x)} ‖ĥ₀(c'x²/3)‖ ≤ K √(c'/x)` for all `x > 0`, uniformly over the
compact family and for large `c'`. -/
theorem designProfile_global_bound (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) {η₀ : ℝ}
    (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      ∀ x : ℝ, 0 < x → Real.exp (c' * edgeL x) *
        ‖edgeHankel c' (designProfile c' f N η₀ σ ε) (c' * x ^ 2 / 3)‖ ≤ K * √(c' / x) := by
  obtain ⟨K, hK0, hK⟩ := designProfile_global_bound_of_admissible f hη₀0 hη₀1
  refine ⟨K, hK0, ?_⟩
  filter_upwards [designAdmissible_eventually f N hf hfN M E hη₀0 hη₀1, hK] with c' hAd h σ ε hσ hε
  exact h N σ ε (hAd σ ε hσ hε)

/-! ### 4. Hypotheses of `SD_0` and `SD_V` -/

lemma exp_designPhi1_eq {c' : ℝ} {f N : ℕ} {η₀ : ℝ} {σ ε : ℕ → ℝ} {B : ℝ}
    (hDec : DesignPhiDecomp c' f N η₀ σ ε B) {b : ℂ} (hb : b ∈ combN) :
    Complex.exp ((c' : ℂ) * edgePhi0Blaschke b + designPhi1 c' f N η₀ σ ε b) =
      designComb c' f N η₀ σ ε b := by
  obtain ⟨h1, h2⟩ := hDec.1 b hb
  rw [← h2, h1]
  unfold designPhi1
  rw [edgePhi0Blaschke_eq_phi0]
  congr 1
  ring

lemma re_designPhi1_edge {c' : ℝ} {f N : ℕ} {η₀ : ℝ} {σ ε : ℕ → ℝ} {B : ℝ}
    (hDec : DesignPhiDecomp c' f N η₀ σ ε B) {b : ℂ} (hb : b.im = 1 / 2) :
    (designPhi1 c' f N η₀ σ ε b).re = 0 := hDec.2.2.1 b hb

/-- The finite modifications `designComb` carry a `PhaseComb` with `Φ₁ = designPhi1` (the abstract interface of
`designProfile_sdvHypotheses_of_decomp` and `lemma_Phi_transform_of_decomp`). -/
theorem designComb_phaseComb_of_decomp (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ) (B : ℝ),
      DesignAdmissible c' f N η₀ σ ε → DesignPhiDecomp c' f N η₀ σ ε B →
      PhaseComb c' (A + B) (designComb c' f N η₀ σ ε) (designPhi1 c' f N η₀ σ ε) := by
  obtain ⟨A, hA0, hBev⟩ := designPhi1_bounds_of_decomp f hf hη₀0 hη₀1
  refine ⟨A, hA0, ?_⟩
  filter_upwards [hBev, combTail_K1a_unif hη₀0 hη₀1] with c' hBd hTd N σ ε B hA hDec
  obtain ⟨hT1, hT2, hT3, hT4⟩ := hTd N
  obtain ⟨hK1, -, -⟩ := designComb_K1a hA hT1 hT2 hT3
  obtain ⟨hΦ1, hder⟩ := hBd N σ ε B hA hDec
  refine ⟨fun b hb => hK1 hb, fun _ hb => exp_designPhi1_eq hDec hb, hΦ1, hder,
    fun b hb => re_designPhi1_edge hDec hb, fun b hb => ?_⟩
  exact designComb_neg_conj c' f N η₀ σ ε b (hT4 (by rw [hb]; norm_num))

/-- **The hypotheses of Lemma `SD_V` for `h₀ = sech² B_D^{(f)}`, from a phase decomposition.**  There is
`A ≥ 0` (depending on `f` only) such that for `c'` large (threshold independent of the cut `N`, of `B` and
of the data), every `N`, every admissible finite modification with `DesignPhiDecomp c' f N η₀ σ ε B` and every
`x ≥ ξ_*`, `SDVHypotheses Φ₀ x c' (1/8) (𝒜₀ + A + B) (𝒜₀' + A + B) sech² Φ₁ H₀¹ ε_H` holds with
`Φ₀ = edgePhi0Blaschke` and `Φ₁ = Φ₁^{(f)} + Δ_D`; `𝒜₀, 𝒜₀'` (`ampM0`, `ampM0'`) are absolute. -/
theorem designProfile_sdvHypotheses_of_decomp (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ) (B : ℝ),
      DesignAdmissible c' f N η₀ σ ε → DesignPhiDecomp c' f N η₀ σ ε B →
      ∀ x : ℝ, xiStar ≤ x →
        SDVHypotheses edgePhi0Blaschke x c' (1 / 8) (ampM0 + (A + B)) (ampM0' + (A + B))
          sechSqProfile (designPhi1 c' f N η₀ σ ε) hankel0 hankelEps := by
  obtain ⟨A, hA0, hPC⟩ := designComb_phaseComb_of_decomp f hf hη₀0 hη₀1
  refine ⟨A, hA0, ?_⟩
  filter_upwards [hPC, eventually_ge_atTop (6 / (π * xiStar))] with c' hP hc6 N σ ε B hA hDec x hx
  exact sdvHypotheses_of_phase hc6 (hP N σ ε B hA hDec) hx

/-- **The hypotheses of Lemma `SD_V` for `h₀ = sech² B_D^{(f)}`.**  There are constants `M₁, M₂`
such that for `c'` large, uniformly in the compact family and in `x ≥ ξ_*`,
`SDVHypotheses Φ₀ x c' (1/8) M₁ M₂ sech² Φ₁ H₀¹ ε_H` holds with `Φ₀ = edgePhi0Blaschke`,
`Φ₁ = Φ₁^{(f)} + Δ_D`. -/
theorem designProfile_sdvHypotheses (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) (hE : 0 ≤ E)
    {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ,
      (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      ∀ x : ℝ, xiStar ≤ x →
        SDVHypotheses edgePhi0Blaschke x c' (1 / 8) M₁ M₂ sechSqProfile
          (designPhi1 c' f N η₀ σ ε) hankel0 hankelEps := by
  obtain ⟨A, hA0, hSDV⟩ := designProfile_sdvHypotheses_of_decomp f hf hη₀0 hη₀1
  obtain ⟨CΦ, hCΦ, hΦ⟩ := lemma_Phi_b f N hf hfN M E hE hη₀0 hη₀1
  have hc1 := cosC_pos
  refine ⟨ampM0 + (A + CΦ), ampM0' + (A + CΦ), ?_, ?_, ?_⟩
  · unfold ampM0; positivity
  · unfold ampM0'; positivity
  filter_upwards [hSDV, hΦ, designAdmissible_eventually f N hf hfN M E hη₀0 hη₀1,
    tendsto_lambdaComb_atTop.eventually_le_const (zero_lt_one : (0 : ℝ) < 1)]
    with c' hS hD hAd hlam1 σ ε hσ hε x hx
  have hDec : DesignPhiDecomp c' f N η₀ σ ε CΦ := (hD σ ε hσ hε).mono (by nlinarith)
  exact hS N σ ε CΦ (hAd σ ε hσ hε) hDec x hx

/-! ### 5. The transform bound -/

/-- `(SD.1)`: the Hankel transform of `h₀` is the edge integral of `SD_V`. -/
lemma edgeHankel_designProfile_eq_sdvIntegral {c' : ℝ} {f N : ℕ} {η₀ : ℝ} {σ ε : ℕ → ℝ} {B : ℝ}
    (hh : EdgeHankelHyp (designProfile c' f N η₀ σ ε) π 8)
    (hDec : DesignPhiDecomp c' f N η₀ σ ε B) {x : ℝ} (hc : 0 < c') (hx : 0 < x) :
    edgeHankel c' (designProfile c' f N η₀ σ ε) (c' * x ^ 2 / 3) =
      ((sdvIntegral edgePhi0Blaschke c' x sechSqProfile (designPhi1 c' f N η₀ σ ε) hankel0 : ℂ)) := by
  exact edgeHankel_eq_sdvIntegral_of_eq (fun b hb => exp_designPhi1_eq hDec hb) hh hc hx

/-- **Lemma `Φ`, "Consequently"** (`ut:Phi`), for an abstract finite modification with a phase
decomposition of derivative bound `B ≥ 0` (independent of `c'` and of the cut `N`): for fixed `f ≥ 1`,
`η₀ ∈ [0, 1/4]`, `0 < θ < 2/3` there is `C = C(f, B, θ) ≥ 0` such that for `c'` large, **every cut `N`**,
every admissible finite modification with `DesignPhiDecomp c' f N η₀ σ ε B` and every `x ≥ ξ_I = ξ_* +
c'^{-θ}`, `|ĥ₀(c'x²/3)| ≤ 𝒜_x (1 + C c'^{-1+3θ/2})`.  Neither `C` nor the threshold depends on `N`, `x`
or the data.  (The ramped comb uses `θ = 3/5`.) -/
theorem lemma_Phi_transform_of_decomp (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) {B : ℝ} (hB : 0 ≤ B) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ), DesignAdmissible c' f N η₀ σ ε →
      DesignPhiDecomp c' f N η₀ σ ε B →
      ∀ x : ℝ, xiStar + c' ^ (-θ) ≤ x →
        ‖edgeHankel c' (designProfile c' f N η₀ σ ε) (c' * x ^ 2 / 3)‖ ≤
          combAmplitude c' x * (1 + C * c' ^ (-1 + 3 * θ / 2)) := by
  obtain ⟨A, hA0, hPC⟩ := designComb_phaseComb_of_decomp f hf hη₀0 hη₀1
  obtain ⟨C, hC, hT⟩ := lemma_Phi_transform_of_phase (Mφ := A + B) (by positivity) hθ0 hθ1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hPC, hT, designProfile_edgeHankelHyp_of_admissible f hη₀0 hη₀1]
    with c' hP hT' hH N σ ε hA hDec x hx
  exact hT' _ _ (hP N σ ε B hA hDec) (hH N σ ε hA).1 x hx

/-- **Lemma `Φ`, "Consequently"** (`ut:Phi`): for `h₀ = sech²(πb/2) B_D^{(f)}` in a compact family,
`c'` large, `0 < θ < 2/3` and every `x ≥ ξ_I = ξ_* + c'^{-θ}`,
`|ĥ₀(c'x²/3)| ≤ 𝒜_x (1 + C c'^{-1+3θ/2})`, with `C` independent of `c'`, `x` and the family. -/
theorem lemma_Phi_transform (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) (hE : 0 ≤ E) {η₀ : ℝ}
    (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      ∀ x : ℝ, xiStar + c' ^ (-θ) ≤ x →
        ‖edgeHankel c' (designProfile c' f N η₀ σ ε) (c' * x ^ 2 / 3)‖ ≤
          combAmplitude c' x * (1 + C * c' ^ (-1 + 3 * θ / 2)) := by
  obtain ⟨CΦ, hCΦ, hΦ⟩ := lemma_Phi_b f N hf hfN M E hE hη₀0 hη₀1
  obtain ⟨C, hC, hT⟩ := lemma_Phi_transform_of_decomp f hf hη₀0 hη₀1 hCΦ hθ0 hθ1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hT, hΦ, designAdmissible_eventually f N hf hfN M E hη₀0 hη₀1,
    tendsto_lambdaComb_atTop.eventually_le_const (zero_lt_one : (0 : ℝ) < 1)]
    with c' hTc hD hAd hlam1 σ ε hσ hε x hx
  exact hTc N σ ε (hAd σ ε hσ hε) ((hD σ ε hσ hε).mono (by nlinarith)) x hx

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.designPhi1_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designPhi1_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.designProfile_edgeHankelHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designProfile_edgeHankelHyp

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.designProfile_global_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designProfile_global_bound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.designProfile_sdvHypotheses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designProfile_sdvHypotheses

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.lemma_Phi_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Phi_transform

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.designPhi1_bounds_of_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designPhi1_bounds_of_decomp

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.designProfile_edgeHankelHyp_of_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designProfile_edgeHankelHyp_of_admissible

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.designProfile_global_bound_of_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designProfile_global_bound_of_admissible

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.designProfile_sdvHypotheses_of_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designProfile_sdvHypotheses_of_decomp

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.lemma_Phi_transform_of_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Phi_transform_of_decomp

end FormalResearch.ModularBootstrap.Upper.Design
