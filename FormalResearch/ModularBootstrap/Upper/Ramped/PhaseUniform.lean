module

public import FormalResearch.ModularBootstrap.Upper.Membership.DesignMembership

/-!
# Phase machinery for the ramped comb, uniform in the cut `N` (squared pair-change interface)

Sources: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Lemma `Φ` (`ut:Phi`) with the pair-change bound
`(PC)` (`eq:ut:PC`); `CFT/notes/n2_ramped_comb.tex`, Lemma `U*` (`rem:thmU`), step "phase and membership".

The ramped comb changes `N ≍ 0.036 c'` pairs of the reference comb, so no constant may depend on the cut `N`.
The general statements are proved in place, for an abstract finite modification `designComb c' f N η₀ σ ε`:

* `Design.iteratedDeriv_designDelta_le_sq` (`PerturbPhi.lean`): `(PC)` in the squared form,
  `‖∂_b^i Δ_D‖ ≤ K · designPairChange` on `𝒩` for `i ≤ 2`, with an absolute `K`;
* `Design.designPhiDecomp_of_pairChange`: `DesignPhiDecomp c' f N η₀ σ ε (K P)` for `c' ≥ c₀(f, η₀)`, every
  `N`, every admissible modification with `designPairChange ≤ P`;
* `Design.designProfile_sdvHypotheses_of_decomp`, `Design.lemma_Phi_transform_of_decomp`,
  `Design.designProfile_global_bound_of_admissible` (`CombTransform.lean`) and
  `Membership.design_k7_of_decomp` (`DesignMembership.lean`): the hypotheses of `SD_V`, the transform bound of
  Lemma `Φ`, `SD_G`, and Lemma `K7`, from a `DesignPhiDecomp` of derivative bound `B`.

This file packages them for the consumer (the ramped instantiation) in terms of the single hypothesis
`PhaseHyp c' f N η₀ σ ε P` (a cut `N ≥ f`, an admissible modification, total pair change at most `P`), and
proves it is satisfiable (`phaseHyp_reference`).

**What the instantiation must verify** (all other hypotheses are discharged here for `c'` large, with a threshold
independent of `N`, `P` and the data).  With `ℓ_k = siteGap c' k`, `χ_k = chiQuantile c' k`,
`ε⁰_k = η₀ ℓ_k` (`η₀ = 1/4` for the reference comb), `χ'_k = designSite c' σ k = ξ_* + λ σ_k` and
`ε_k = ε (f + 1 + j)` the modified widths:

1. `f ≤ N`, `χ'_f ≥ 0`, `χ'_k ≥ 0` and `|ε_k| ≤ 1/8` for the modified pairs.  The width condition is automatic
   for `ε_k = η_k ℓ_k` with `0 ≤ η_k ≤ 1/4` (`abs_height_le_eighth`);
2. the total pair change `designPairChange` is at most a constant `P` independent of `c'` and `N`.  By
   `designPairChange_eq` it is `|χ'_f - χ_f| + Σ_j |ε_j² - ε⁰_j²| + 2 Σ_j |χ'_j - χ_j|`, i.e. the sum of the
   three quantities `|Δ_f| + 2 Σ_j |Δ_j|` (site displacements, `Σ |Δ_k| = O(λ)` from
   `|σ_k - Φ_k| ≤ C k^{-4/3}`) and `Σ_j |ε_j² - ε⁰_j²| = O(c'^{-1})` (for heights `η_k ≤ 1/4` this is at most
   `(1/16) Σ ℓ_k²` over the changed pairs).

The consequences are, for `P ≥ 0` fixed: `DesignPhiDecomp (K P)` (`K` absolute), the `SD_V` hypotheses with
constants `𝒜₀ + A + K P`, `𝒜₀' + A + K P` (`A = A(f)`), the transform bound
`‖ĥ₀(c'x²/3)‖ ≤ 𝒜_x (1 + C c'^{-1+3θ/2})` for `x ≥ ξ_* + c'^{-θ}`, any `0 < θ < 2/3` (the ramped comb uses `θ = 3/5`),
the global bound `e^{c'L(x)}‖ĥ₀(c'x²/3)‖ ≤ K_G √(c'/x)` and the conclusion of Lemma `K7`
(`g = ½(h₀ - ĥ₀)` in the test class, `g_vac = ½ h_{0,vac} - π ∫ h₀ V`, `|h_{0,vac}| ≤ 8` for `Q = (1-q)²`).

`phase_packageP` and `phase_k7W` are the order-`p` and every-weight forms (`FW-SD`, `fw:FWM`); `phase_package`
and `phase_k7` (weight `1`) keep their statements.

All results are proved unconditionally.
-/

@[expose] public section

open Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Membership FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle FormalResearch.ModularBootstrap.Crossing

/-! ### 1. The hypothesis -/

/-- The single hypothesis of the phase package: a cut `N ≥ f`, admissible data (modified sites `≥ 0`,
modified widths `≤ 1/8`; reference data are admissible for `c'` large) and total pair change at most `P`. -/
def PhaseHyp (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) (P : ℝ) : Prop :=
  f ≤ N ∧ DesignAdmissible c' f N η₀ σ ε ∧ designPairChange c' f N η₀ σ ε ≤ P

/-- The total pair change is the first-site displacement, the sum of the squared-width changes and twice the
sum of the site displacements. -/
lemma designPairChange_eq (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) :
    designPairChange c' f N η₀ σ ε =
      |designSite c' σ f - chiQuantile c' (f : ℝ)| +
        ∑ j ∈ Finset.range (N - f), |ε (f + 1 + j) ^ 2 - (η₀ * siteGap c' (f + 1 + j)) ^ 2| +
        2 * ∑ j ∈ Finset.range (N - f),
          |designSite c' σ (f + 1 + j) - chiQuantile c' ((f + 1 + j : ℕ) : ℝ)| := by
  unfold designPairChange
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Heights `η ℓ_k` with `η ∈ [0, 1/4]` are at most `1/8` for every index `k ≥ 1`, for `c'` large. -/
lemma abs_height_le_eighth :
    ∀ᶠ c' in atTop, ∀ k : ℕ, 1 ≤ k → ∀ η : ℝ, 0 ≤ η → η ≤ 1 / 4 →
      |η * siteGap c' k| ≤ 1 / 8 := by
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  filter_upwards [h_ev, eventually_gt_atTop 0] with c' ⟨hgap_k, _, _, hgap_1⟩ hc' k hk η hη0 hη1
  have hga := siteGap_nonneg hc' hk
  rw [abs_of_nonneg (mul_nonneg hη0 hga)]
  calc η * siteGap c' k ≤ (1 / 4) * (1 / 2) :=
        mul_le_mul hη1 ((hgap_k k hk).trans hgap_1) hga (by norm_num)
    _ = 1 / 8 := by norm_num

/-- `PhaseHyp` from its elementary form: `f ≤ N`, modified sites `≥ 0`, modified widths `≤ 1/8` and a bound on
the total pair change; the threshold in `c'` depends on `f` and `η₀` only. -/
theorem phaseHyp_of_nonneg (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ) (P : ℝ), f ≤ N → 0 ≤ designSite c' σ f →
      (∀ i < N - f, 0 ≤ designSite c' σ (f + 1 + i)) → (∀ i < N - f, |ε (f + 1 + i)| ≤ 1 / 8) →
      designPairChange c' f N η₀ σ ε ≤ P → PhaseHyp c' f N η₀ σ ε P := by
  filter_upwards [designAdmissible_of_nonneg f hf hη₀0 hη₀1] with c' h N σ ε P hfN h0 hs hw hP
  exact ⟨hfN, h N σ ε hfN h0 hs hw, hP⟩

/-! ### 2. The package -/

/-- **Phase package** (`ut:Phi` with `(PC)`; `SD_V`, `SD_G`; uniform in `N`).  Fix `f ≥ 1`, `η₀ ∈ [0, 1/4]`,
`P ≥ 0` and `0 < θ < 2/3`.  There are `K, A, C, K_G ≥ 0` (`K` absolute) and `c₀` such that for every `c' ≥ c₀`,
every cut `N` and all data with `PhaseHyp c' f N η₀ σ ε P` (modified sites `≥ 0`, widths `≤ 1/8`, total pair change
`≤ P`):

* `DesignPhiDecomp c' f N η₀ σ ε (K P)`: `log B_D = c' Φ₀ + Φ₁^{(f)} + Δ_D`, `Re (Φ₁^{(f)} + Δ_D) = 0` on `E₊`,
  `‖Δ_D^{(i)}‖ ≤ K P` on `𝒩`;
* `SDVHypotheses` of Lemma `SD_V` for `h₀ = sech² B_D` at every `x ≥ ξ_*` (`δ = 1/8`, constants `𝒜₀ + A + K P`,
  `𝒜₀' + A + K P`);
* the transform bound `‖ĥ₀(c' x²/3)‖ ≤ 𝒜_x (1 + C c'^{-1+3θ/2})` for `x ≥ ξ_* + c'^{-θ}`;
* the global bound `e^{c' L(x)} ‖ĥ₀(c' x²/3)‖ ≤ K_G √(c'/x)` for every `x > 0`. -/
theorem phase_package (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) {P : ℝ}
    (hP : 0 ≤ P) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) :
    ∃ K A C KG : ℝ, 0 < K ∧ 0 ≤ A ∧ 0 ≤ C ∧ 0 ≤ KG ∧ ∀ᶠ c' in atTop,
      ∀ (N : ℕ) (σ ε : ℕ → ℝ), PhaseHyp c' f N η₀ σ ε P →
        DesignPhiDecomp c' f N η₀ σ ε (K * P) ∧
        (∀ x : ℝ, xiStar ≤ x →
          SDVHypotheses edgePhi0Blaschke x c' (1 / 8) (ampM0 + (A + K * P))
            (ampM0' + (A + K * P)) sechSqProfile (designPhi1 c' f N η₀ σ ε) hankel0 hankelEps) ∧
        (∀ x : ℝ, xiStar + c' ^ (-θ) ≤ x →
          ‖edgeHankel c' (designProfile c' f N η₀ σ ε) (c' * x ^ 2 / 3)‖ ≤
            combAmplitude c' x * (1 + C * c' ^ (-1 + 3 * θ / 2))) ∧
        (∀ x : ℝ, 0 < x → Real.exp (c' * edgeL x) *
          ‖edgeHankel c' (designProfile c' f N η₀ σ ε) (c' * x ^ 2 / 3)‖ ≤ KG * √(c' / x)) := by
  obtain ⟨K, hK, hdec⟩ := designPhiDecomp_of_pairChange
  obtain ⟨A, hA0, hsdv⟩ := designProfile_sdvHypotheses_of_decomp f hf hη₀0 hη₀1
  obtain ⟨C, hC, htr⟩ := lemma_Phi_transform_of_decomp f hf hη₀0 hη₀1 (mul_nonneg hK.le hP) hθ0 hθ1
  obtain ⟨KG, hKG, hglob⟩ := designProfile_global_bound_of_admissible f hη₀0 hη₀1
  refine ⟨K, A, C, KG, hK, hA0, hC, hKG, ?_⟩
  filter_upwards [hdec f hf hη₀0 hη₀1, hsdv, htr, hglob] with c' h1 h2 h3 h4 N σ ε ⟨hfN, hA, hpc⟩
  have hD := h1 N σ ε P hfN hA hpc
  exact ⟨hD, fun x hx => h2 N σ ε (K * P) hA hD x hx, fun x hx => h3 N σ ε hA hD x hx,
    fun x hx => h4 N σ ε hA x hx⟩

/-- **Phase package at every order `p`** (`ut:Phi` with `(PC)`; `FW-SD`, `SD_G` at order `p`; uniform in `N`).
Fix `p`, `f ≥ 1`, `η₀ ∈ [0, 1/4]`, `P ≥ 0` and `0 < θ < 2/3`.  There are `K, A, C_ε, C, K_G ≥ 0` (`K` absolute)
and `c₀` such that for every `c' ≥ c₀`, every cut `N` and all data with `PhaseHyp c' f N η₀ σ ε P`:

* `DesignPhiDecomp c' f N η₀ σ ε (K P)`;
* the amplitude hypotheses of `FW-SD` at order `p` (`FWSDAmplitudeInput`, `δ = 1/8`, constants
  `𝒜₀ + A + K P`, `𝒜₀' + A + K P`, `C_ε`) at every `x ≥ x_I`;
* the transform bound `‖(𝓗_{p+1} h₀)(c' x²/3)‖ ≤ 𝒜_x R_p(x) (1 + C c'^{-1+3θ/2})` for `x ≥ ξ_* + c'^{-θ}`;
* the global bound `e^{c' L(x)} ‖(𝓗_{p+1} h₀)(c' x²/3)‖ ≤ K_G √(c'/x) x^{-p}` for `x > 0` with `4π c' x/3 ≥ 1`.

At `p = 0` the last two are the corresponding parts of `phase_package`. -/
theorem phase_packageP (p f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) {P : ℝ}
    (hP : 0 ≤ P) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) :
    ∃ K A Cε C KG : ℝ, 0 < K ∧ 0 ≤ A ∧ 0 ≤ Cε ∧ 0 ≤ C ∧ 0 ≤ KG ∧ ∀ᶠ c' in atTop,
      ∀ (N : ℕ) (σ ε : ℕ → ℝ), PhaseHyp c' f N η₀ σ ε P →
        DesignPhiDecomp c' f N η₀ σ ε (K * P) ∧
        FWSDAmplitudeInput p c' (designPhi1 c' f N η₀ σ ε) (1 / 8) (ampM0 + (A + K * P))
          (ampM0' + (A + K * P)) Cε ∧
        (∀ x : ℝ, xiStar + c' ^ (-θ) ≤ x →
          ‖edgeHankelP p c' (designProfile c' f N η₀ σ ε) (c' * x ^ 2 / 3)‖ ≤
            combAmplitude c' x * fwsdRatio p x * (1 + C * c' ^ (-1 + 3 * θ / 2))) ∧
        (∀ x : ℝ, 0 < x → 1 ≤ 4 * π * c' * x / 3 → Real.exp (c' * edgeL x) *
          ‖edgeHankelP p c' (designProfile c' f N η₀ σ ε) (c' * x ^ 2 / 3)‖ ≤
            KG * √(c' / x) * (1 / x) ^ p) := by
  obtain ⟨K, hK, hdec⟩ := designPhiDecomp_of_pairChange
  obtain ⟨A, Cε, hA0, hCε, hfw⟩ := design_fwsdAmplitudeInput_of_decomp p f hf hη₀0 hη₀1
  obtain ⟨C, hC, htr⟩ :=
    lemma_Phi_transform_of_decomp_P p f hf hη₀0 hη₀1 (mul_nonneg hK.le hP) hθ0 hθ1
  obtain ⟨KG, hKG, hglob⟩ := designProfile_global_bound_of_admissible_P p f hη₀0 hη₀1
  refine ⟨K, A, Cε, C, KG, hK, hA0, hCε, hC, hKG, ?_⟩
  filter_upwards [hdec f hf hη₀0 hη₀1, hfw, htr, hglob] with c' h1 h2 h3 h4 N σ ε ⟨hfN, hA, hpc⟩
  have hD := h1 N σ ε P hfN hA hpc
  exact ⟨hD, h2 N σ ε (K * P) hA hD, fun x hx => h3 N σ ε hA hD x hx,
    fun x hx hk => h4 N σ ε hA x hx hk⟩

/-- **Lemma `K7` for the ramped combs** (`cmb:K7` at every weight `w = prob.w`, uniform in `N`).  For a
fixed-weight problem, `f ≥ 1`, `η₀ ∈ [0, 1/4]` and `P ≥ 0` there is `K > 0` (absolute) such that for `c'` large, every cut `N` and
all data with `PhaseHyp c' f N η₀ σ ε P`: `h₀ = sech² B_D` and `ĥ₀` decay like `C e^{-c'L - πx}`,
`g = ½(h₀ - ĥ₀)` is in the test class (membership in `Ā`), `g_vac = ½ h_{0,vac} - π ∫ h₀ V`, and
`|½ h_{0,vac}| ≤ 2^m` (`|h_{0,vac}| ≤ 8` for `m = 2`, by `K7ConclusionW.norm_vac_le_eight`). -/
theorem phase_k7W {prob : FixedWeightProblem} (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ}
    (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) {P : ℝ} (hP : 0 ≤ P) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ), PhaseHyp c' f N η₀ σ ε P →
      K7ConclusionW prob c' (designComb c' f N η₀ σ ε) := by
  obtain ⟨K, hK, hdec⟩ := designPhiDecomp_of_pairChange
  refine ⟨K, hK, ?_⟩
  filter_upwards [hdec f hf hη₀0 hη₀1,
    design_k7_of_decompW (prob := prob) f hf hη₀0 hη₀1 (mul_nonneg hK.le hP)]
    with c' h1 h2 N σ ε ⟨hfN, hA, hpc⟩
  exact h2 N σ ε hfN hA (h1 N σ ε P hfN hA hpc)

/-- **Lemma `K7` for the ramped combs** (`cmb:K7` at `w = 1`, uniform in `N`).  For a fixed-weight problem with
`w = 1`, `f ≥ 1`, `η₀ ∈ [0, 1/4]` and `P ≥ 0` there is `K > 0` (absolute) such that for `c'` large, every cut `N` and
all data with `PhaseHyp c' f N η₀ σ ε P`: `h₀ = sech² B_D` and `ĥ₀` decay like `C e^{-c'L - πx}`,
`g = ½(h₀ - ĥ₀)` is in the test class (membership in `Ā`), `g_vac = ½ h_{0,vac} - π ∫ h₀ V`, and
`|½ h_{0,vac}| ≤ 2^m` (`|h_{0,vac}| ≤ 8` for `m = 2`, by `K7Conclusion.norm_vac_le_eight`). -/
theorem phase_k7 {prob : FixedWeightProblem} (hw : prob.w = 1) (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ}
    (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) {P : ℝ} (hP : 0 ≤ P) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ), PhaseHyp c' f N η₀ σ ε P →
      K7Conclusion prob c' (designComb c' f N η₀ σ ε) := by
  obtain ⟨K, hK, h⟩ := phase_k7W (prob := prob) f hf hη₀0 hη₀1 hP
  exact ⟨K, hK, h.mono fun _ hc N σ ε hph => (hc N σ ε hph).toK7Conclusion hw⟩

/-! ### 3. Non-vacuity -/

/-- The reference comb itself (`σ_k = (χ_k - ξ_*)/λ`, `ε_k = η₀ ℓ_k`) satisfies `PhaseHyp` with `P = 0`
for every cut `N ≥ f` and `c'` large, so the hypothesis of the package is satisfiable (and the package applies
with a threshold independent of `N`). -/
theorem phaseHyp_reference (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ N : ℕ, f ≤ N → ∃ σ ε : ℕ → ℝ, PhaseHyp c' f N η₀ σ ε 0 := by
  filter_upwards [phaseHyp_of_nonneg f hf hη₀0 hη₀1, abs_height_le_eighth,
    eventually_gt_atTop (0 : ℝ)] with c' hP hh hc' N hfN
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _
  set σ : ℕ → ℝ := fun k => (chiQuantile c' (k : ℝ) - xiStar) / lambdaComb c' with hσ
  have hsite : ∀ k : ℕ, designSite c' σ k = chiQuantile c' (k : ℝ) := fun k => by
    unfold designSite
    rw [hσ]
    field_simp
    ring
  have hnn : ∀ k : ℕ, 1 ≤ k → N ≥ k → 0 ≤ designSite c' σ k := fun k hk hkN => by
    rw [hsite]
    exact xiStar_pos.le.trans (refSite_bounds hc' hk hkN).1
  refine ⟨σ, fun k => η₀ * siteGap c' k, hP N _ _ 0 hfN (hnn f hf hfN)
    (fun i hi => hnn _ (by omega) (by omega)) (fun i hi => hh _ (by omega) η₀ hη₀0 hη₀1) ?_⟩
  rw [designPairChange_eq]
  simp [hsite]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.phase_package' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phase_package

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.phase_k7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phase_k7

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.phaseHyp_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phaseHyp_reference

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.phase_packageP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phase_packageP

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.phase_k7W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phase_k7W

end FormalResearch.ModularBootstrap.Upper.Ramped
