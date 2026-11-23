module

public import FormalResearch.ModularBootstrap.Upper.Design.DesignCombProps
public import FormalResearch.ModularBootstrap.Upper.Design.AmplitudeLogDeriv
public import FormalResearch.ModularBootstrap.Upper.Saddle.EdgePhaseZero
public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeGlobalBound

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

/-- The comb-independent amplitude `𝒜_x = 2 e^{-2πnx/3} |ℰ(b_x)| |1 + ε_H(k b_x)|
(|b_x|/(x F'(v_x)))^{1/2}` of `(SD.4)` for `ℰ = sech²(π b/2)` (the factor `e^{Re Φ₁(b_x)}` is `1`
for the combs of Lemma `Φ`, see `designPhi1_re_edge`). -/
noncomputable def combAmplitude (n x : ℝ) : ℝ :=
  sdvPrefactor n x sechSqProfile (fun _ => 0) hankelEps

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

lemma sechSqProfile_neg_conj (b : ℂ) :
    sechSqProfile (-(starRingEnd ℂ b)) = starRingEnd ℂ (sechSqProfile b) := by
  unfold sechSqProfile
  have h1 : (π : ℂ) * -(starRingEnd ℂ b) / 2 = -(starRingEnd ℂ ((π : ℂ) * b / 2)) := by
    rw [map_div₀, map_mul, Complex.conj_ofReal, map_ofNat]; ring
  rw [h1, Complex.cosh_neg, Complex.cosh_conj]
  simp

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
  obtain ⟨A, hA0, hBev⟩ := designPhi1_bounds_of_decomp f hf hη₀0 hη₀1
  have hc1 := cosC_pos
  refine ⟨A, hA0, ?_⟩
  filter_upwards [hBev, combTail_K1a_unif hη₀0 hη₀1,
    eventually_ge_atTop (6 / (π * xiStar))] with c' hBd hTd hbig N σ ε B hA hDec x hx
  obtain ⟨hT1, hT2, hT3, hT4⟩ := hTd N
  obtain ⟨hΦ1, hder⟩ := hBd N σ ε B hA hDec
  have hc'pos : 0 < c' := lt_of_lt_of_le (by have := xiStar_pos; positivity) hbig
  have hk8 : 8 ≤ sdvWave c' x := by
    unfold sdvWave
    have hxi := xiStar_pos
    have h1 : 6 / (π * xiStar) * (π * xiStar) = 6 := by field_simp
    nlinarith [mul_le_mul hbig hx hxi.le hc'pos.le, Real.pi_pos]
  have hkpos : 0 < sdvWave c' x := by linarith
  obtain ⟨hK1, hK2, hK3⟩ := designComb_K1a hA hT1 hT2 hT3
  have hstrip : edgeStrip (1 / 8) ⊆ combN := fun b hb => by
    have hb' : |b.im - 1 / 2| ≤ 1 / 8 := hb
    exact le_trans hb' (by norm_num)
  obtain ⟨hAn, hNz, hL1, hL2⟩ := sdvAmplitude_fields (x := x) (n := c') hk8 hΦ1
    (fun b hb => (hder b (hstrip hb)).1) (fun b hb => (hder b (hstrip hb)).2)
  refine ⟨hAn, hNz, ?_, hL1, hL2, ?_, ?_, ?_⟩
  · intro b hb
    have hb' : |b.im - 1 / 2| ≤ 1 / 8 := hb
    have him : 0 < ((sdvWave c' x : ℂ) * b).im := by
      rw [Complex.im_ofReal_mul]
      exact mul_pos hkpos (by linarith [(abs_le.mp hb').1])
    rw [hankel0_eq_leading_mul him]
    rfl
  · refine ⟨8, π, by norm_num, Real.pi_pos, fun v t ht0 ht1 => ?_⟩
    have hbim : (((v : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
    have hbre : (((v : ℂ) + (t : ℂ) * Complex.I)).re = v := by simp
    have hbc : (v : ℂ) + (t : ℂ) * Complex.I ∈ combN := by
      change |((v : ℂ) + (t : ℂ) * Complex.I).im - 1 / 2| ≤ 1 / 4
      rw [hbim, abs_le]; constructor <;> linarith
    rw [norm_mul, exp_designPhi1_eq hDec hbc]
    have h2 := edgeHankelHyp_sech.decay ((v : ℂ) + (t : ℂ) * Complex.I) (by rw [hbim]; linarith)
      (by rw [hbim]; exact ht1)
    rw [hbre] at h2
    have h3 : ‖designComb c' f N η₀ σ ε ((v : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 :=
      hK1 (by rw [hbim, abs_of_nonneg (by linarith)]; exact ht1)
    calc _ ≤ (8 * Real.exp (-π * |v|)) * 1 := mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
      _ = 8 * Real.exp (-π * |v|) := mul_one _
  · refine ⟨1, fun b hb => ?_⟩
    have hb' : |b.im - 1 / 2| ≤ 1 / 8 := hb
    have him : 0 < ((sdvWave c' x : ℂ) * b).im := by
      rw [Complex.im_ofReal_mul]
      exact mul_pos hkpos (by linarith [(abs_le.mp hb').1])
    exact norm_one_add_hankelEps_le him
  · intro v
    dsimp only
    have hb_im : (((v : ℂ) + Complex.I / 2)).im = 1 / 2 := by simp
    have hbm_im : (((-v : ℂ) + Complex.I / 2)).im = 1 / 2 := by simp
    have hbc : (v : ℂ) + Complex.I / 2 ∈ combN := by
      change |((v : ℂ) + Complex.I / 2).im - 1 / 2| ≤ 1 / 4
      rw [hb_im]; norm_num
    have hbmc : (-v : ℂ) + Complex.I / 2 ∈ combN := by
      change |((-v : ℂ) + Complex.I / 2).im - 1 / 2| ≤ 1 / 4
      rw [hbm_im]; norm_num
    have hneg : (-v : ℂ) + Complex.I / 2 = -(starRingEnd ℂ ((v : ℂ) + Complex.I / 2)) := by
      rw [map_add, Complex.conj_ofReal, map_div₀, Complex.conj_I, map_ofNat]; ring
    have hk : ((sdvWave c' x : ℂ) * ((-v : ℂ) + Complex.I / 2)) =
        -(starRingEnd ℂ ((sdvWave c' x : ℂ) * ((v : ℂ) + Complex.I / 2))) := by
      rw [hneg, map_mul, Complex.conj_ofReal]; ring
    have hh : ∀ z : ℂ, z ∈ combN → sechSqProfile z *
        Complex.exp ((c' : ℂ) * edgePhi0Blaschke z + designPhi1 c' f N η₀ σ ε z) =
        designProfile c' f N η₀ σ ε z := fun z hz => by
      rw [exp_designPhi1_eq hDec hz]; rfl
    rw [hh _ hbmc, hh _ hbc, hk, hankel0_reflection]
    have hsym : designProfile c' f N η₀ σ ε (-(starRingEnd ℂ ((v : ℂ) + Complex.I / 2))) =
        starRingEnd ℂ (designProfile c' f N η₀ σ ε ((v : ℂ) + Complex.I / 2)) := by
      unfold designProfile
      rw [sechSqProfile_neg_conj, designComb_neg_conj c' f N η₀ σ ε _
        (hT4 (by rw [hb_im]; norm_num)), map_mul]
    rw [← hneg] at hsym
    rw [hsym, hneg]
    simp only [map_mul]
    ring

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
  rw [edge_hankel_representation Real.pi_pos hh hc hx]
  unfold sdvIntegral sdvWave
  have hpref : (2 * (π : ℂ) * (c' : ℂ) / 3) = ((2 * π * c' / 3 : ℝ) : ℂ) := by push_cast; ring
  rw [hpref]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hbc : (v : ℂ) + Complex.I / 2 ∈ combN := by
    change |((v : ℂ) + Complex.I / 2).im - 1 / 2| ≤ 1 / 4
    simp
  have := exp_designPhi1_eq hDec hbc
  simp only
  rw [this]
  rfl

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
  obtain ⟨A, hA0, hSDV⟩ := designProfile_sdvHypotheses_of_decomp f hf hη₀0 hη₀1
  have hc1' := cosC_pos
  have hM₁ : 0 ≤ ampM0 + (A + B) := by unfold ampM0; positivity
  have hM₂ : 0 ≤ ampM0' + (A + B) := by unfold ampM0'; positivity
  obtain ⟨C₃, C₄, hΦ⟩ := edgePhaseData_blaschke
  have hEP := hΦ (1 / 8) (by norm_num) (by norm_num)
  have hC₃ : 0 ≤ C₃ := (norm_nonneg _).trans (hEP.deriv3_bound (Complex.I / 2) (by
    change |(Complex.I / 2 : ℂ).im - 1 / 2| ≤ 1 / 8
    simp))
  have hC₄ : 0 ≤ C₄ := (norm_nonneg _).trans (hEP.deriv4_bound (Complex.I / 2) (by
    change |(Complex.I / 2 : ℂ).im - 1 / 2| ≤ 1 / 8
    simp))
  obtain ⟨N₀, CSD, hN₀, hCSD, hSD⟩ := lemma_SD_V (δ := 1 / 8) (C₃ := C₃) (C₄ := C₄) (M := ampM0 + (A + B))
    (M' := ampM0' + (A + B)) (by norm_num) (by norm_num) hC₃ hC₄ hM₁ hM₂
  obtain ⟨cm, hcm, hmx⟩ := sdv_uniform_mX_cubed
  have hexp : 0 < 1 - 3 * θ / 2 := by linarith
  refine ⟨CSD / cm, by positivity, ?_⟩
  filter_upwards [hSDV, designProfile_edgeHankelHyp_of_admissible f hη₀0 hη₀1,
    (tendsto_rpow_atTop hexp).eventually_ge_atTop (N₀ / cm), eventually_ge_atTop (1 : ℝ)]
    with c' hS hH hbig hc1 N σ ε hA hDec x hx
  obtain ⟨hh, -⟩ := hH N σ ε hA
  have hc'pos : 0 < c' := lt_of_lt_of_le one_pos hc1
  have hxpos : 0 < c' ^ (-θ) := Real.rpow_pos_of_pos hc'pos _
  have hxξ : xiStar < x := by linarith
  have hxpos' : 0 < x := lt_trans xiStar_pos hxξ
  have hEq := edgeHankel_designProfile_eq_sdvIntegral hh hDec hc'pos hxpos'
  set P : ℝ := c' ^ (1 - 3 * θ / 2) with hP
  have hPpos : 0 < P := Real.rpow_pos_of_pos hc'pos _
  have hq : c' ^ (-(3 * θ / 2)) ≤ (x - xiStar) ^ (3 / 2 : ℝ) := by
    have h1 : (c' ^ (-θ)) ^ (3 / 2 : ℝ) ≤ (x - xiStar) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hxpos.le (by linarith) (by norm_num)
    have h2 : (c' ^ (-θ)) ^ (3 / 2 : ℝ) = c' ^ (-(3 * θ / 2)) := by
      rw [← Real.rpow_mul hc'pos.le]; congr 1; ring
    rwa [h2] at h1
  have hq1 : c' ^ (-(3 * θ / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hc1 (by linarith)
  have hmX : cm * c' ^ (-(3 * θ / 2)) ≤ mX x ^ 3 :=
    (mul_le_mul_of_nonneg_left (le_min hq1 hq) hcm.le).trans (hmx x hxξ)
  have hPeq : P = c' * c' ^ (-(3 * θ / 2)) := by
    rw [hP, ← Real.rpow_one_add' hc'pos.le (by linarith)]; congr 1
  have hcm_mX : cm * P ≤ c' * mX x ^ 3 := by
    rw [hPeq]
    calc cm * (c' * c' ^ (-(3 * θ / 2))) = c' * (cm * c' ^ (-(3 * θ / 2))) := by ring
      _ ≤ c' * mX x ^ 3 := mul_le_mul_of_nonneg_left hmX hc'pos.le
  have hN : N₀ ≤ c' * mX x ^ 3 := by
    have := (div_le_iff₀ hcm).1 hbig
    linarith
  obtain ⟨err, herr, hint⟩ := hSD hxξ hc'pos hN hEP (hS N σ ε B hA hDec x (by linarith))
  have hre : (designPhi1 c' f N η₀ σ ε (bX x)).re = 0 :=
    re_designPhi1_edge hDec (by simp [bX])
  have hpref : sdvPrefactor c' x sechSqProfile (designPhi1 c' f N η₀ σ ε) hankelEps =
      combAmplitude c' x := by
    unfold combAmplitude sdvPrefactor
    simp [hre]
  have hA0 : 0 ≤ combAmplitude c' x := by
    unfold combAmplitude sdvPrefactor
    positivity
  have herr' : |err| ≤ CSD / cm * c' ^ (-1 + 3 * θ / 2) := by
    have h1 : c' ^ (-1 + 3 * θ / 2) = P⁻¹ := by
      rw [hP, ← Real.rpow_neg hc'pos.le]; congr 1; ring
    rw [h1]
    refine herr.trans ?_
    have hpos : 0 < c' * mX x ^ 3 := lt_of_lt_of_le (mul_pos hcm hPpos) hcm_mX
    calc CSD / (c' * mX x ^ 3) ≤ CSD / (cm * P) :=
          div_le_div_of_nonneg_left hCSD (mul_pos hcm hPpos) hcm_mX
      _ = CSD / cm * P⁻¹ := by field_simp
  rw [hEq, hint, Complex.norm_real, Real.norm_eq_abs, hpref, abs_mul, abs_of_nonneg hA0]
  refine mul_le_mul_of_nonneg_left ?_ hA0
  calc |Real.cos (sdvPhase edgePhi0Blaschke c' x sechSqProfile (designPhi1 c' f N η₀ σ ε)
        hankelEps) + err| ≤ |Real.cos _| + |err| := abs_add_le _ _
    _ ≤ 1 + |err| := by gcongr; exact Real.abs_cos_le_one _
    _ ≤ _ := by linarith

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
