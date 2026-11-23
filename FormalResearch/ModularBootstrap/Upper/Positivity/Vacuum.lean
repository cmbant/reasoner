module

public import FormalResearch.ModularBootstrap.Upper.Positivity.VacuumMain

/-!
# Proposition V: vacuum of the designs (`ut:Vac`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Proposition V (`ut:Vac`).  For the designs
`D(N, η_*, d)` (`f = 1`, `w = 1`, `Q = (1-q)²`, `C_* = CStar`, `FK_c = FKc 1 1 c'`, `V_D = windowIntegralVD`
`= ∫ W du`) with `g = ½ (h₀ - ĥ₀)` (`pairOdd`), `g_vac = designGVac` (`Crossing.FixedWeightProblem.gVac`),
and `∫ Ψ_g du = -g_vac / (2π)` (the identity of §4: `Ψ_g` itself is not formalised, so `psiIntegral` is
defined by that identity):

* (i) `proposition_V_i`: for every `ε > 0` and large `c'`,
  `(2 / FK_c) ∫ Ψ_g du - C_* V_D ≤ ε` (`limsup ≤ 0`; no sign assumption on `V_D`);
* (ii) `proposition_V_ii`: if `V_D < 0` then for large `c'`, `g_vac > 0` and
  `g_vac ≥ π C_* |V_D| FK_c / 4`.

Inputs: `design1_k7_membership_vacuum` (`g_vac = ½ h_{0,vac} - π V_c`, `‖½ h_{0,vac}‖ ≤ 4`) and
`vacuum_core` (`V_c ≤ FK_c (C_* V_D + ε)`), with `FK_c ≫ √c'`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.WeightAxioms FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Window.Cardy
  FormalResearch.ModularBootstrap.Upper.Membership

/-- `g_vac` of the `f = 1` finite modification with offsets `σs`: `g = ½ (h₀ - ĥ₀)`, `h₀ = combProfile`,
`ĥ₀ = hankelTransform 1 h₀`. -/
noncomputable def sigGVac (N : ℕ) (η : ℝ) (σs : ℕ → ℝ) (c' : ℝ) : ℝ :=
  virasoroProblem.gVac (c' / 12)
    (pairOdd (combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)))
      (hankelTransform 1 (combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)))))

/-- `∫ Ψ_g du = -g_vac / (2π)` (`ut:s4`) for offsets `σs`. -/
noncomputable def sigPsiIntegral (N : ℕ) (η : ℝ) (σs : ℕ → ℝ) (c' : ℝ) : ℝ := -sigGVac N η σs c' / (2 * π)

/-- `g_vac` of the design `D(N, η_*, d)`: `g = ½ (h₀ - ĥ₀)`, `h₀ = combProfile`, `ĥ₀ = hankelTransform 1 h₀`. -/
noncomputable def designGVac (N : ℕ) (η d c' : ℝ) : ℝ := sigGVac N η (designSigma1 d) c'

/-- `∫ Ψ_g du = -g_vac / (2π)` (`ut:s4`). -/
noncomputable def designPsiIntegral (N : ℕ) (η d c' : ℝ) : ℝ := -designGVac N η d c' / (2 * π)

/-- `g_vac ≥ -4 - π V_c` for the finite modifications with offsets `σs` (vacuum identity, `|½ h_{0,vac}| ≤ 4`). -/
theorem sigGVac_ge (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∀ᶠ c' in atTop, -4 - π * (∫ t in Ioi 0,
        combProfile c' (designComb c' 1 N (1 / 4) (σs) (designWidth1 c' η)) t *
          virasoroProblem.cardyV (c' / 12) t) ≤ sigGVac N η σs c' := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k, 1 ≤ k → k ≤ N → |σs k| ≤ M :=
    ⟨∑ k ∈ Finset.Icc 1 N, |σs k|, fun k hk hkN =>
      Finset.single_le_sum (f := fun j => |σs j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_Icc.mpr ⟨hk, hkN⟩)⟩
  filter_upwards [sig1_k7_membership_vacuum (prob := virasoroProblem) rfl N hN hη0 hη1 σs M hM]
    with c' hK7
  obtain ⟨C, hC0, -, -, -, hvac, hn⟩ := hK7
  have hre := congrArg Complex.re hvac
  rw [Complex.ofReal_re, Complex.sub_re] at hre
  have h2 : ((π : ℂ) * ((∫ t in Ioi (0 : ℝ),
      combProfile c' (designComb c' 1 N (1 / 4) (σs) (designWidth1 c' η)) t *
        virasoroProblem.cardyV (c' / 12) t : ℝ) : ℂ)).re = π * (∫ t in Ioi (0 : ℝ),
      combProfile c' (designComb c' 1 N (1 / 4) (σs) (designWidth1 c' η)) t *
        virasoroProblem.cardyV (c' / 12) t) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [h2] at hre
  have h3 := (Complex.abs_re_le_norm _).trans hn
  have h4 : (2 : ℝ) ^ virasoroProblem.m = 4 := by norm_num [virasoroProblem_m]
  rw [h4] at h3
  have := (abs_le.mp h3).1
  unfold sigGVac
  linarith

/-- `g_vac ≥ -4 - π V_c` for the designs (vacuum identity, `|½ h_{0,vac}| ≤ 4`). -/
theorem designGVac_ge (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d : ℝ) :
    ∀ᶠ c' in atTop, -4 - π * (∫ t in Ioi 0,
        combProfile c' (designComb c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' η)) t *
          virasoroProblem.cardyV (c' / 12) t) ≤ designGVac N η d c' :=
  sigGVac_ge N hN hη0 hη1 (designSigma1 d)

/-- **Proposition V (i)** (`ut:Vac`) for the `f = 1` finite modifications with arbitrary offsets `σs`
(`V = windowIntegralSig`): see `proposition_V_i`, the case `σs = designSigma1 d`. -/
theorem proposition_V_i_sig (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c' in atTop, 2 * sigPsiIntegral N η σs c' / FKc 1 1 c' - CStar * windowIntegralSig N η σs ≤ ε := by
  have hπ := Real.pi_pos
  filter_upwards [sigGVac_ge N hN hη0 hη1 σs, vacuum_core_sig N hN hη0 hη1 σs (half_pos hε),
    FKc_ge_mul_sqrt (8 / (π * ε)), eventually_gt_atTop (1 : ℝ)] with c' hg hc hFKbig hc1
  have hcpos : 0 < c' := by linarith
  have hFK := FKc_pos (q := 1) one_pos 1 hcpos
  have hsc : 1 ≤ √c' := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hc1.le
  have h8 : 8 / (π * ε) ≤ FKc 1 1 c' := by
    refine le_trans ?_ hFKbig
    exact le_mul_of_one_le_right (by positivity) hsc
  have h9 : 8 ≤ π * ε * FKc 1 1 c' := by
    have := (div_le_iff₀ (by positivity)).mp h8
    linarith
  unfold sigPsiIntegral
  rw [sub_le_iff_le_add, div_le_iff₀ hFK]
  have e : 2 * (-sigGVac N η σs c' / (2 * π)) = -sigGVac N η σs c' / π := by field_simp
  rw [e, div_le_iff₀ hπ]
  nlinarith [mul_le_mul_of_nonneg_left (show _ ≤ _ from hc) hπ.le]

/-- **Proposition V (i)** (`ut:Vac`). -/
theorem proposition_V_i (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c' in atTop, 2 * designPsiIntegral N η d c' / FKc 1 1 c' - CStar * windowIntegralVD N η d ≤ ε :=
  by
  have h := proposition_V_i_sig N hN hη0 hη1 (designSigma1 d) hε
  simpa only [designPsiIntegral, designGVac, sigPsiIntegral, windowIntegralVD_eq_sig] using h

/-- **Proposition V (ii)** (`ut:Vac`) for arbitrary offsets `σs`: see `proposition_V_ii`. -/
theorem proposition_V_ii_sig (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ)
    (hV : windowIntegralSig N η σs < 0) :
    ∀ᶠ c' in atTop, 0 < sigGVac N η σs c' ∧
      π * CStar * |windowIntegralSig N η σs| * FKc 1 1 c' / 4 ≤ sigGVac N η σs c' := by
  have hπ := Real.pi_pos
  have hC := CStar_pos
  have hVa : 0 < |windowIntegralSig N η σs| := abs_pos.mpr hV.ne
  have hε : 0 < CStar * |windowIntegralSig N η σs| / 2 := by positivity
  filter_upwards [sigGVac_ge N hN hη0 hη1 σs, vacuum_core_sig N hN hη0 hη1 σs hε,
    FKc_ge_mul_sqrt (16 / (π * CStar * |windowIntegralSig N η σs|)), eventually_gt_atTop (1 : ℝ)]
    with c' hg hc hFKbig hc1
  have hcpos : 0 < c' := by linarith
  have hFK := FKc_pos (q := 1) one_pos 1 hcpos
  have hsc : 1 ≤ √c' := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hc1.le
  have hpos : 0 < π * CStar * |windowIntegralSig N η σs| := by positivity
  have h8 : 16 / (π * CStar * |windowIntegralSig N η σs|) ≤ FKc 1 1 c' :=
    le_trans (le_mul_of_one_le_right (by positivity) hsc) hFKbig
  have h9 : 16 ≤ π * CStar * |windowIntegralSig N η σs| * FKc 1 1 c' := by
    have := (div_le_iff₀ hpos).mp h8
    linarith
  have habs : |windowIntegralSig N η σs| = -windowIntegralSig N η σs := abs_of_neg hV
  have hVc : π * (∫ t in Ioi 0,
        combProfile c' (designComb c' 1 N (1 / 4) (σs) (designWidth1 c' η)) t *
          virasoroProblem.cardyV (c' / 12) t) ≤
      -(π * CStar * |windowIntegralSig N η σs| * FKc 1 1 c' / 2) := by
    have := mul_le_mul_of_nonneg_left hc hπ.le
    rw [habs] at this ⊢
    nlinarith
  have hlow : π * CStar * |windowIntegralSig N η σs| * FKc 1 1 c' / 4 ≤ sigGVac N η σs c' := by
    linarith
  exact ⟨lt_of_lt_of_le (by positivity) hlow, hlow⟩

/-- **Proposition V (ii)** (`ut:Vac`): if `V_D < 0` then `g_vac ≥ π C_* |V_D| FK_c / 4 > 0` for large `c'`. -/
theorem proposition_V_ii (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d : ℝ)
    (hV : windowIntegralVD N η d < 0) :
    ∀ᶠ c' in atTop, 0 < designGVac N η d c' ∧
      π * CStar * |windowIntegralVD N η d| * FKc 1 1 c' / 4 ≤ designGVac N η d c' :=
  by
  rw [windowIntegralVD_eq_sig] at hV ⊢
  exact proposition_V_ii_sig N hN hη0 hη1 (designSigma1 d) hV

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_V_i_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_V_i_sig

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_V_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_V_i

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_V_ii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_V_ii

end FormalResearch.ModularBootstrap.Upper.Positivity
