module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroCombK7
public import FormalResearch.ModularBootstrap.Upper.Assembly.BumpedDesignWindow
public import FormalResearch.ModularBootstrap.Upper.Positivity.PropositionIIIRegionII
public import FormalResearch.ModularBootstrap.Upper.Bump.PhaseHyp
public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeGlobalBoundP

/-!
# The bumped two-zero comb at every weight: membership, order-`p` transform bounds (`ut:T2`, `fw:s1`)

Source: `upper_transfer.tex`, Theorem T2 (`ut:T2`) at fixed `(w, Q)` (Proposition W1.5(a), `wone:clark`): the comb of
`ut:T2` is `B₂ = T_{χ(p)} B₁` (`TwoZeroDesign.twoZeroComb`, `B₁` the `f = 2` finite modification); at `w > 1` the test is
`g_w = ½(h₂^{(p)} - 𝓗_w h₂^{(p)})` with the macroscopic detuning bump of `fw:s1` applied to `B₁`
(`bumpedComb`: base `(f, N₀) = (2, n + 2)`, cut `N' ≥ n + 2`).

* `TwoZeroDesign.bumpComb bd d c N' = T_{χ(p)} · bumpedComb bd c 2 (n+2) N' (1/4) σ ε`: the bumped two-zero comb;
* `twoZeroBump_phaseHyp`: the bumped base satisfies `PhaseHyp … 2` for every cut `N' ≥ n + 2` (threshold independent of
  `N'`, uniform on a compact family);
* `twoZeroBump_innerCombHyp`, `twoZeroBump_phaseComb`: hypotheses (i), (iii) of `K7` and the abstract `PhaseComb`;
* `twoZeroBump_k7W`: Lemma `K7` at every weight for `T_{χ(p)} B^{(p)}` (membership of `g_w` in `Ā_w`, decay, vacuum
  identity, `|½ h_{vac}| ≤ 2^m`): `fw:FWM` for the product, uniform in the cut and on a compact family;
* `twoZeroBump_globalP`: `SD_G` at order `p` (`fw:e1.3`): `e^{c'L} ‖𝓗_{p+1} h₂^{(p)}‖ ≤ K √(c'/x) x^{-p}`;
* `twoZeroBump_transformP`: Lemma `Φ` at order `p` (`fw:e1.4`): `‖𝓗_{p+1} h₂^{(p)}‖ ≤ 𝒜_x R_p (1 + C c'^{-1+3θ/2})`
  (`|T_{χ(p)}| = 1` on the saddle line, so the amplitude is that of `sech²`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Hankel FormalResearch.ModularBootstrap.Upper.Saddle
  FormalResearch.ModularBootstrap.Upper.Bump FormalResearch.ModularBootstrap.Upper.Ramped
  FormalResearch.ModularBootstrap.Upper.Positivity

/-! ### 1. The bumped two-zero comb -/

namespace TwoZeroDesign

variable {n : ℕ}

/-- The bumped `f = 2` finite modification of a two-zero design (base cut `n + 2`, cut `N'`). -/
noncomputable def bumpedBase (bd : BumpData) (d : TwoZeroDesign n) (c : ℝ) (N' : ℕ) : ℂ → ℂ :=
  bumpedComb bd c 2 (n + 2) N' (1 / 4) d.sigmaSeq (fun k => lambdaComb c * d.epsHatSite k)

/-- The bumped two-zero comb `T_{χ(p)} B₁^{(p)}`. -/
noncomputable def bumpComb (bd : BumpData) (d : TwoZeroDesign n) (c : ℝ) (N' : ℕ) : ℂ → ℂ :=
  fun b => blaschkeT ((d.chiP c : ℝ) : ℂ) b * d.bumpedBase bd c N' b

lemma bumpedBase_eq (bd : BumpData) (d : TwoZeroDesign n) (c : ℝ) (N' : ℕ) :
    d.bumpedBase bd c N' = designComb c 2 N' (1 / 4) (bumpSigma c (n + 2) d.sigmaSeq)
      (bumpEps bd c (n + 2) (1 / 4) (fun k => lambdaComb c * d.epsHatSite k)) := rfl

end TwoZeroDesign

open TwoZeroDesign

/-- The bumped base satisfies `PhaseHyp … 2` for every cut `N' ≥ n + 2`, uniformly on a compact family. -/
theorem twoZeroBump_phaseHyp (bd : BumpData) {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' →
      PhaseHyp c 2 N' (1 / 4) (bumpSigma c (n + 2) d.sigmaSeq)
        (bumpEps bd c (n + 2) (1 / 4) (fun k => lambdaComb c * d.epsHatSite k)) 2 := by
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  filter_upwards [phaseHyp_compact 2 (n + 2) (by norm_num) (by omega) M E (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumped_phaseHyp bd 2 (by norm_num) (η₀ := 1 / 4) (by norm_num) le_rfl,
    eventually_gt_atTop (0 : ℝ)] with c hc hb' hc0 d hd N' hN'
  have hl := Upper.Window.Cardy.lambdaComb_pos' hc0
  have hfb := comb_family_bounds (E := E) hl (hb d hd)
  have h1 := hc d.sigmaSeq (fun k => lambdaComb c * d.epsHatSite k) hfb.1 hfb.2
  have h2 := hb' (n + 2) N' d.sigmaSeq (fun k => lambdaComb c * d.epsHatSite k) 1 h1 hN'
  norm_num at h2
  exact h2

/-- Hypotheses (i), (iii) of `K7` for the bumped two-zero comb, every cut `N' ≥ n + 2`. -/
theorem twoZeroBump_innerCombHyp (bd : BumpData) {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' → InnerCombHyp c (d.bumpComb bd c N') := by
  filter_upwards [twoZeroBump_phaseHyp bd hK hA,
    designComb_innerCombHyp_of_admissible 2 (by norm_num) (η₀ := 1 / 4) (by norm_num) le_rfl]
    with c hph hin d hd N' hN'
  obtain ⟨hfN, hAd, -⟩ := hph d hd N' hN'
  exact (hin N' _ _ hfN hAd).mul_blaschkeT (d.chiP c)

/-- The abstract `PhaseComb` of the bumped two-zero comb (input of `SD_V`, `FW-SD`, `Φ`), uniformly on a compact
family and in the cut. -/
theorem twoZeroBump_phaseComb (bd : BumpData) {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ Mφ : ℝ, 0 ≤ Mφ ∧ ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' →
      PhaseComb c Mφ (d.bumpComb bd c N')
        (fun b => designPhi1 c 2 N' (1 / 4) (bumpSigma c (n + 2) d.sigmaSeq)
          (bumpEps bd c (n + 2) (1 / 4) (fun k => lambdaComb c * d.epsHatSite k)) b +
            tPhase ((d.chiP c : ℝ) : ℂ) b) := by
  obtain ⟨S, hS0, hS⟩ := hK.exists_sigmaP_bound
  obtain ⟨K, hKpos, hdec⟩ := designPhiDecomp_of_pairChange
  obtain ⟨A, hA0, hPC⟩ := designComb_phaseComb_of_decomp 2 (by norm_num) (η₀ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨Cφ, hCφ, hmul⟩ := PhaseComb.mul_blaschkeT
  refine ⟨(A + K * 2) + (π + Cφ), by positivity, ?_⟩
  filter_upwards [twoZeroBump_phaseHyp bd hK hA, hdec 2 (by norm_num) (η₀ := 1 / 4) (by norm_num) le_rfl,
    hPC, eventually_lambda_small S] with c hph hdc hpc ⟨hl, hlS⟩ d hd N' hN'
  obtain ⟨hfN, hAd, hpch⟩ := hph d hd N' hN'
  have hDec := hdc N' _ _ 2 hfN hAd hpch
  have hP := hpc N' _ _ (K * 2) hAd hDec
  have hχ : 0 ≤ d.chiP c := by
    have := chiP_ge (hS d hd) hl hlS
    linarith [xiStar_pos]
  exact hmul hP hχ

/-- **Lemma `K7` at every weight for the bumped two-zero comb** (`fw:FWM`, `ut:T2`, `ut:Vac` with `(f, r) = (2, 1)`):
for `c` large, every `d ∈ 𝒦` and every cut `N' ≥ n + 2`, `h₂^{(p)}` and `𝓗_w h₂^{(p)}` decay like `C e^{-c'L - πx}`,
`g_w = ½(h₂^{(p)} - 𝓗_w h₂^{(p)}) ∈ Ā_w`, the vacuum identity holds and `|½ h_{vac}| ≤ 2^m`. -/
theorem twoZeroBump_k7W (prob : FixedWeightProblem) (bd : BumpData) {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' → K7ConclusionW prob c (d.bumpComb bd c N') := by
  obtain ⟨S, hS0, hS⟩ := hK.exists_sigmaP_bound
  obtain ⟨K, hKpos, hdec⟩ := designPhiDecomp_of_pairChange
  obtain ⟨A, hA0, hPC⟩ := designComb_phaseComb_of_decomp 2 (by norm_num) (η₀ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨A', hA'0, hPh⟩ := designComb_combPhaseData_of_decomp 2 (by norm_num) (η₀ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨Cφ, hCφ, hmulP⟩ := PhaseComb.mul_blaschkeT
  obtain ⟨Cφ', hCφ', hmulD⟩ := CombPhaseData.mul_blaschkeT
  obtain ⟨Cε, c₁, hCε, hc₁, hF⟩ := fwsdAmplitudeInput_of_phase (prob.w - 1)
  have hc1 := cosC_pos
  have hM₁ : 0 ≤ ampM0 + ((A + K * 2) + (π + Cφ)) := by unfold ampM0; positivity
  have hM₂ : 0 ≤ ampM0' + ((A + K * 2) + (π + Cφ)) := by unfold ampM0'; positivity
  obtain ⟨c₀, hc₀, hK7⟩ := k7_membership_vacuum_of_fwsd (prob := prob) hM₁ hM₂ hCε
  filter_upwards [twoZeroBump_phaseHyp bd hK hA, hdec 2 (by norm_num) (η₀ := 1 / 4) (by norm_num) le_rfl,
    hPC, hPh, twoZeroBump_innerCombHyp bd hK hA, eventually_ge_atTop c₀, eventually_ge_atTop c₁,
    eventually_ge_atTop (12 * prob.totalShift), eventually_lambda_small S]
    with c hph hdc hpc hphd hin hc hc₁' hsh ⟨hl, hlS⟩ d hd N' hN'
  obtain ⟨hfN, hAd, hpch⟩ := hph d hd N' hN'
  have hDec := hdc N' _ _ 2 hfN hAd hpch
  have hP := hpc N' _ _ (K * 2) hAd hDec
  have hχ : 0 ≤ d.chiP c := by
    have := chiP_ge (hS d hd) hl hlS
    linarith [xiStar_pos]
  have hPT := hmulP hP hχ
  have hD := hmulD (hphd N' _ _ (K * 2) hAd hDec) hχ
  exact hK7 hc (by linarith) (hin d hd N' hN') hD (hF hc₁' hPT)

/-- `SD_G` at order `p` (`fw:e1.3`) for the bumped two-zero comb: for `x > 0` with `4π c x/3 ≥ 1`,
`e^{c L(x)} ‖𝓗_{p+1} h₂^{(p)}(c x²/3)‖ ≤ K √(c/x) x^{-p}`, uniformly on a compact family and in the cut. -/
theorem twoZeroBump_globalP (bd : BumpData) (p : ℕ) {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' → ∀ x : ℝ, 0 < x →
      1 ≤ 4 * π * c * x / 3 →
      Real.exp (c * edgeL x) *
        ‖edgeHankelP p c (fun b => sechSqProfile b * d.bumpComb bd c N' b) (c * x ^ 2 / 3)‖ ≤
          K * √(c / x) * (1 / x) ^ p := by
  obtain ⟨K, hK0, hKe⟩ := edge_global_bound_P p
  refine ⟨K, hK0, ?_⟩
  filter_upwards [twoZeroBump_innerCombHyp bd hK hA, eventually_gt_atTop (0 : ℝ)]
    with c hI hc d hd N' hN' x hx hk
  have h := hKe (combH0 (d.bumpComb bd c N')) π 8 1 Real.pi_pos (hI d hd N' hN').edgeHankelHyp zero_le_one
    (hI d hd N' hN').edgeSechBound c x hc hx hk
  rw [mul_one] at h
  exact h

/-- Lemma `Φ` at order `p` (`fw:e1.4`) for the bumped two-zero comb: for `0 < θ < 2/3` there is `C` such that for `c`
large, `d ∈ 𝒦`, `N' ≥ n + 2` and `x ≥ ξ_* + c^{-θ}`,
`‖𝓗_{p+1} h₂^{(p)}(c x²/3)‖ ≤ 𝒜_x R_p(x) (1 + C c^{-1+3θ/2})`. -/
theorem twoZeroBump_transformP (bd : BumpData) (p : ℕ) {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' → ∀ x : ℝ, xiStar + c ^ (-θ) ≤ x →
      ‖edgeHankelP p c (fun b => sechSqProfile b * d.bumpComb bd c N' b) (c * x ^ 2 / 3)‖ ≤
        combAmplitude c x * fwsdRatio p x * (1 + C * c ^ (-1 + 3 * θ / 2)) := by
  obtain ⟨Mφ, hMφ, hP⟩ := twoZeroBump_phaseComb bd hK hA
  obtain ⟨C, hC, hT⟩ := lemma_Phi_transform_of_phase_P p hMφ hθ0 hθ1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hP, hT, twoZeroBump_innerCombHyp bd hK hA] with c hP' hT' hI d hd N' hN' x hx
  exact hT' _ _ (hP' d hd N' hN') (hI d hd N' hN').edgeHankelHyp x hx

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_phaseHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_phaseHyp

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_k7W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_k7W

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_globalP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_globalP

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_transformP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_transformP

end FormalResearch.ModularBootstrap.TwoLevel
