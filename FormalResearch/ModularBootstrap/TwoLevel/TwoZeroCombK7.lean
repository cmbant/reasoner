module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroCombPhase
public import FormalResearch.ModularBootstrap.Upper.Membership.DesignMembership

/-!
# `K7` membership, vacuum identity and the transform bound for `T_{χ(p)} B₁` (`upper_transfer.tex`, `ut:T2`)

Source: `ut:T2`, "Phase and membership": `B₂ = T_{χ(p)} B₁`, `h₂ = sech²(πb/2) B₂`, `B₁ = d.comb c'` the `f = 2` design
comb.  Since `|T_{χ(p)}| ≤ 1` on the strip, `= 1` on `E_±`, and `T_{χ(p)} = e^{iπ + φ_{χ(p)}}` (`K1`), the comb `B₂` satisfies
the hypotheses of Lemmas `SD_H`, `SD_G`, `SD_0`, `SD_V`, `K7` with the phase `Φ₁ = designPhi1 + iπ + φ_{χ(p)}`.
For every compact family `𝒦` of admissible designs, for `c'` large and every `d ∈ 𝒦` (no condition on the sign of
`p`, `χ(p) ≥ ξ_*/2 > 0`):

* `twoZeroComb_innerCombHyp`: hypotheses (i), (iii) of `K7` (`InnerCombHyp`; (iii) from `|T| ≤ 1` and the design comb);
* `twoZeroComb_combPhaseData`: hypothesis (ii) (`CombPhaseData`) with `Φ₁ = twoZeroPhi1`;
* `twoZeroComb_phaseComb`, `twoZeroComb_sdvAmplitudeInput`: the `SD_V` amplitude input (`SDVAmplitudeInput`);
* `twoZeroComb_k7_membership_vacuum`: for `prob.w = 1`, `g = ½(h₂ - ĥ₂) ∈ Ā` (`TestClass`), decay
  `|h₂|, |ĥ₂| ≤ C(c') e^{-c'L - πx}`, the vacuum identity `g_vac = ½ h_{2,vac} - π ∫ h₂ V` and
  `|½ h_{2,vac}| ≤ 2^m` (`K7Conclusion`);
* `twoZeroComb_phi_transform`: `Lemma Φ` for `h₂`: `|ĥ₂(c'x²/3)| ≤ 𝒜_x (1 + C c'^{-1+3θ/2})` for `x ≥ ξ_* + c'^{-θ}`
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

/-! ### 1. The parameters of the design comb, uniformly on a compact family -/

namespace TwoZeroDesign

variable {n : ℕ}

/-- The phase `Φ₁ = Φ₁^{(2)} + Δ₁ + iπ + φ_{χ(p)}` of `B₂ = T_{χ(p)} B₁` on `𝒩`. -/
noncomputable def twoZeroPhi1 (d : TwoZeroDesign n) (c' : ℝ) (b : ℂ) : ℂ :=
  designPhi1 c' 2 (n + 2) (1 / 4) d.sigmaSeq (fun k => lambdaComb c' * d.epsHatSite k) b +
    tPhase ((d.chiP c' : ℝ) : ℂ) b

/-- The scaled sites and widths of the design comb are bounded on a compact family of admissible designs. -/
lemma IsCompactFamily.exists_comb_bounds {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ M E : ℝ, 0 ≤ M ∧ 0 ≤ E ∧ ∀ d ∈ 𝒦, (∀ k, 2 ≤ k → k ≤ n + 2 → |d.sigmaSeq k| ≤ M) ∧
      (∀ k, 2 < k → k ≤ n + 2 → 0 ≤ d.epsHatSite k ∧ d.epsHatSite k ≤ E) := by
  obtain ⟨R, hR, hb⟩ := hK.exists_bound
  have hκ := kappaAiry_pos
  refine ⟨R / kappaAiry + 1, R / kappaAiry + 1, by positivity, by positivity, fun d hd => ?_⟩
  obtain ⟨-, hq, hse⟩ := hb d hd
  obtain ⟨hσF, hsite⟩ := d.toModified_bounds (hA d hd) hq hse
  refine ⟨fun k hk2 hkN => ?_, fun k hk hkN => ?_⟩
  · rcases Nat.eq_or_lt_of_le hk2 with rfl | hk3
    · simpa [sigmaSeq] using hσF
    · have := (hsite k (Finset.mem_Icc.2 ⟨hk3, hkN⟩)).1
      simpa [sigmaSeq, show k ≠ 2 by omega] using this
  · have := hsite k (Finset.mem_Icc.2 ⟨hk, hkN⟩)
    exact ⟨this.2.1, this.2.2⟩

/-- The comb `T_{χ(p)} B₁` is `blaschkeT χ(p) · designComb`. -/
lemma twoZeroComb_eq (d : TwoZeroDesign n) (c' : ℝ) :
    d.twoZeroComb c' = fun b => blaschkeT ((d.chiP c' : ℝ) : ℂ) b *
      designComb c' 2 (n + 2) (1 / 4) d.sigmaSeq (fun k => lambdaComb c' * d.epsHatSite k) b := rfl

lemma twoZeroPhi1_eq (d : TwoZeroDesign n) (c' : ℝ) :
    d.twoZeroPhi1 c' = fun b =>
      designPhi1 c' 2 (n + 2) (1 / 4) d.sigmaSeq (fun k => lambdaComb c' * d.epsHatSite k) b +
        tPhase ((d.chiP c' : ℝ) : ℂ) b := rfl

/-- The family hypotheses of `Upper.Design`/`Upper.Membership` (`|σ_k| ≤ M`, `0 ≤ ε_k ≤ E λ`) hold for the design comb. -/
lemma comb_family_bounds {M E : ℝ} {d : TwoZeroDesign n} {c' : ℝ} (hl : 0 < lambdaComb c')
    (h : (∀ k, 2 ≤ k → k ≤ n + 2 → |d.sigmaSeq k| ≤ M) ∧
      (∀ k, 2 < k → k ≤ n + 2 → 0 ≤ d.epsHatSite k ∧ d.epsHatSite k ≤ E)) :
    (∀ k, 2 ≤ k → k ≤ n + 2 → |d.sigmaSeq k| ≤ M) ∧
      (∀ k, 2 < k → k ≤ n + 2 →
        0 ≤ lambdaComb c' * d.epsHatSite k ∧ lambdaComb c' * d.epsHatSite k ≤ E * lambdaComb c') :=
  ⟨h.1, fun k hk hkN => ⟨mul_nonneg hl.le (h.2 k hk hkN).1, by
    have := mul_le_mul_of_nonneg_left (h.2 k hk hkN).2 hl.le
    linarith⟩⟩

end TwoZeroDesign

/-! ### 2. Hypotheses of Lemma `K7` -/

open TwoZeroDesign

/-- Hypotheses (i) and (iii) of `K7` for `B₂ = T_{χ(p)} B₁`, uniformly on a compact family. -/
theorem twoZeroComb_innerCombHyp {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, InnerCombHyp c' (d.twoZeroComb c') := by
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  obtain ⟨S, hS0, hS⟩ := hK.exists_sigmaP_bound
  filter_upwards [designComb_innerCombHyp 2 (n + 2) (by norm_num) (by omega) M E
    (by norm_num : (0 : ℝ) ≤ 1 / 4) le_rfl, eventually_lambda_small S] with c' hI ⟨hl, hlS⟩ d hd
  have hI' := hI d.sigmaSeq (fun k => lambdaComb c' * d.epsHatSite k) (comb_family_bounds hl (hb d hd)).1
    (comb_family_bounds hl (hb d hd)).2
  exact hI'.mul_blaschkeT (d.chiP c')

/-- Hypothesis (ii) of `K7` for `B₂`: `log B₂ = c'Φ₀ + Φ₁` on `𝒩`, `Φ₁ = twoZeroPhi1`, `Re Φ₁ = 0` on `E₊`,
`|Φ₁^{(i)}| ≤ M_φ` on `𝒩`, `i ≤ 2`, uniformly on a compact family. -/
theorem twoZeroComb_combPhaseData {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ Mφ : ℝ, 0 ≤ Mφ ∧ ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦,
      CombPhaseData c' Mφ (d.twoZeroComb c') (d.twoZeroPhi1 c') := by
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  obtain ⟨S, hS0, hS⟩ := hK.exists_sigmaP_bound
  obtain ⟨M₀, hM₀, hP⟩ := designComb_combPhaseData 2 (n + 2) (by norm_num) (by omega) M E hE
    (by norm_num : (0 : ℝ) ≤ 1 / 4) le_rfl
  obtain ⟨Cφ, hCφ, hmul⟩ := CombPhaseData.mul_blaschkeT
  refine ⟨M₀ + (π + Cφ), by positivity, ?_⟩
  filter_upwards [hP, eventually_lambda_small S] with c' hP' ⟨hl, hlS⟩ d hd
  have h := hP' d.sigmaSeq (fun k => lambdaComb c' * d.epsHatSite k)
    (comb_family_bounds hl (hb d hd)).1 (comb_family_bounds hl (hb d hd)).2
  have hχ : 0 ≤ d.chiP c' := by
    have := chiP_ge (hS d hd) hl hlS
    linarith [xiStar_pos]
  exact hmul h hχ

/-- The abstract `PhaseComb` of `B₂`, uniformly on a compact family (input of `SD_V` and `Φ`). -/
theorem twoZeroComb_phaseComb {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ Mφ : ℝ, 0 ≤ Mφ ∧ ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦,
      PhaseComb c' Mφ (d.twoZeroComb c') (d.twoZeroPhi1 c') := by
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  obtain ⟨S, hS0, hS⟩ := hK.exists_sigmaP_bound
  obtain ⟨A, hA0, hPC⟩ := designComb_phaseComb_of_decomp 2 (by norm_num) (η₀ := 1 / 4)
    (by norm_num) le_rfl
  obtain ⟨CΦ, hCΦ, hΦ⟩ := lemma_Phi_b 2 (n + 2) (by norm_num) (by omega) M E hE
    (by norm_num : (0 : ℝ) ≤ 1 / 4) le_rfl
  obtain ⟨Cφ, hCφ, hmul⟩ := PhaseComb.mul_blaschkeT
  refine ⟨(A + CΦ) + (π + Cφ), by positivity, ?_⟩
  filter_upwards [hPC, hΦ, designAdmissible_eventually 2 (n + 2) (by norm_num) (by omega) M E
    (by norm_num : (0 : ℝ) ≤ 1 / 4) le_rfl, eventually_lambda_small S,
    tendsto_lambdaComb_atTop.eventually_le_const (zero_lt_one : (0 : ℝ) < 1)]
    with c' hPC' hΦ' hAd ⟨hl, hlS⟩ hl1 d hd
  have hfb := comb_family_bounds hl (hb d hd)
  have hDec : DesignPhiDecomp c' 2 (n + 2) (1 / 4) d.sigmaSeq (fun k => lambdaComb c' * d.epsHatSite k) CΦ :=
    (hΦ' _ _ hfb.1 hfb.2).mono (by nlinarith)
  have h := hPC' (n + 2) d.sigmaSeq (fun k => lambdaComb c' * d.epsHatSite k) CΦ
    (hAd _ _ hfb.1 hfb.2) hDec
  have hχ : 0 ≤ d.chiP c' := by
    have := chiP_ge (hS d hd) hl hlS
    linarith [xiStar_pos]
  exact hmul h hχ

/-- `SDVAmplitudeInput` for `B₂` (the named amplitude input of `saddleTailBound_of_sdv`): `SDVHypotheses` of
`lemma_SD_V` with `δ = 1/8` at every `x ≥ x_I`, uniformly on a compact family. -/
theorem twoZeroComb_sdvAmplitudeInput {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦,
      SDVAmplitudeInput c' (d.twoZeroPhi1 c') (1 / 8) M₁ M₂ := by
  obtain ⟨Mφ, hMφ, hP⟩ := twoZeroComb_phaseComb hK hA
  have hc1 := cosC_pos
  refine ⟨ampM0 + Mφ, ampM0' + Mφ, by unfold ampM0; positivity, by unfold ampM0'; positivity, ?_⟩
  filter_upwards [hP, eventually_ge_atTop (6 / (π * xiStar)), eventually_gt_atTop (0 : ℝ)]
    with c' hP' hc6 hpos d hd x hx
  refine sdvHypotheses_of_phase hc6 (hP' d hd) (le_trans ?_ hx)
  unfold xI
  have := Real.rpow_pos_of_pos hpos (-(3 / 5 : ℝ))
  linarith

/-- **Lemma `K7` for `B₂ = T_{χ(p)} B₁`** (`ut:T2`, "Phase and membership"; `cmb:K7` at `w = 1`).  For every
fixed-weight problem with `w = 1`, every compact family of admissible designs, `c'` large and `d ∈ 𝒦`:
`h₂ = sech²(πb/2) B₂` and `ĥ₂` decay like `C(c') e^{-c'L(x) - πx}`, `g = ½(h₂ - ĥ₂) ∈ Ā` (`TestClass`), the vacuum
identity `g_vac = ½ h_{2,vac} - π ∫ h₂ V` holds and `|½ h_{2,vac}| ≤ 2^m` (`K7Conclusion`).  No assumption on the
sign of `p` or on `χ(p) ≥ ξ_*`. -/
theorem twoZeroComb_k7_membership_vacuum {prob : FixedWeightProblem} (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, K7Conclusion prob c' (d.twoZeroComb c') := by
  obtain ⟨M₁, M₂, hM₁, hM₂, hS⟩ := twoZeroComb_sdvAmplitudeInput hK hA
  obtain ⟨Mφ, hMφ, hP⟩ := twoZeroComb_combPhaseData hK hA
  obtain ⟨c₀, hc₀, hK7⟩ := k7_membership_vacuum_of_sdv (prob := prob) hw hM₁ hM₂
  filter_upwards [hS, hP, twoZeroComb_innerCombHyp hK hA, eventually_ge_atTop c₀,
    eventually_ge_atTop (12 * prob.totalShift)] with c' hs hp hi hc hsh d hd
  exact hK7 hc (by linarith) (hi d hd) (hp d hd) (hs d hd)

/-! ### 3. Lemma `Φ` for `h₂` -/

/-- **Lemma `Φ`, "Consequently", for `h₂ = sech² T_{χ(p)} B₁`** (`ut:T2`, `ut:Phi`): for `0 < θ < 2/3` there is `C`
such that for `c'` large, `d ∈ 𝒦` and `x ≥ ξ_* + c'^{-θ}`,
`‖ĥ₂(c'x²/3)‖ ≤ 𝒜_x (1 + C c'^{-1+3θ/2})`; the amplitude is that of `sech²` since `|T_{χ(p)}| = 1` on `E₊`. -/
theorem twoZeroComb_phi_transform {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, xiStar + c' ^ (-θ) ≤ x →
      ‖edgeHankel c' (fun b => sechSqProfile b * d.twoZeroComb c' b) (c' * x ^ 2 / 3)‖ ≤
        combAmplitude c' x * (1 + C * c' ^ (-1 + 3 * θ / 2)) := by
  obtain ⟨Mφ, hMφ, hP⟩ := twoZeroComb_phaseComb hK hA
  obtain ⟨C, hC, hT⟩ := lemma_Phi_transform_of_phase hMφ hθ0 hθ1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hP, hT, twoZeroComb_innerCombHyp hK hA] with c' hP' hT' hI d hd x hx
  exact hT' _ _ (hP' d hd) (hI d hd).edgeHankelHyp x hx

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroComb_innerCombHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroComb_innerCombHyp

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroComb_combPhaseData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroComb_combPhaseData

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroComb_sdvAmplitudeInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroComb_sdvAmplitudeInput

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroComb_k7_membership_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroComb_k7_membership_vacuum

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroComb_phi_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroComb_phi_transform

end FormalResearch.ModularBootstrap.TwoLevel
