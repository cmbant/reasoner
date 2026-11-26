module

public import FormalResearch.ModularBootstrap.Mixtures.VacTwoZeroCore

/-!
# `pmix:vac` for `(f, r) = (2, 1)`: the transfer package for a common source

`positive_mixtures.tex`, Proposition PM.9 (`pmix:vac`) and `pmix:fixed-transfer` at `(f, r) = (2, 1)`, for every `CommonSource`
(in particular every mixture, `MixtureData.commonSource`).  `SrcTwoZeroTransferData C 𝒦` is `TwoZeroTransferData` (W-T2w,
`ut:T2`) with the weight `V_s = C.src.cardyV` of the source in place of the single weight `(w, 1)`: the normalisation is
`F^{mix}_{2,c} = twoZeroFSrc C.src c = A(ξ_*) F_{2,c}^{(w,1)}`, the density is `Ψ^{mix}_g = g V_s J = psiAirySrc`, and the test function
is the bumped two-zero functional `twoZeroBumpG triv d c` of `ut:T2` at the trivial product.

* `twoZeroBump_fields_eventually_src`, `twoZeroBump_integrable_src`: `testClass`, `decay`, `pos`, `integrable`;
* `twoZeroBump_window_field_src`: the window limit `|(F^{mix})^{-1} Ψ^{mix}_g - C₂ W_2| ≤ ε` (two-sided, on `[-R, R]`);
* `twoZeroBump_limsup_field_src`: the second limit, one-sided: `(F^{mix})^{-1} ∫ Ψ^{mix}_g ≤ C₂ ∫ W_2 + ε` (the same form as W-T2w;
  the paper's two-sided limit is not formalised at any weight);
* `twoZeroBump_vac_eventually_src`: vacuum positivity `κ c^{3/2} ≤ g_vac` when `∫ W_2 ≤ -δ`;
* **`twoSimpleZeroTransfer_src`**: the package, for every compact family `𝒦` of admissible two-zero designs.

All results are proved unconditionally.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Mixtures

open Real Filter Topology Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.Upper.Window.Cardy
  FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Rigidity
  FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Positivity
  FormalResearch.ModularBootstrap.Upper.Assembly FormalResearch.ModularBootstrap.Upper.Bump
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.TwoLevel FormalResearch.Special
open TwoZeroDesign

/-- `F^{mix}_{2,c} ≍ c^{3/2}` (`F_asymp`). -/
lemma twoZeroFSrc_asymp (C : CommonSource) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ c : ℝ, 0 < c →
      A * c ^ ((3 : ℝ) / 2) ≤ twoZeroFSrc C.src c ∧ twoZeroFSrc C.src c ≤ B * c ^ ((3 : ℝ) / 2) := by
  obtain ⟨A, B, hA, hB, h⟩ := twoZeroF_asymp C.src.triv
  have hAs := C.ampl_pos xiStar_pos
  refine ⟨C.src.ampl xiStar * A, C.src.ampl xiStar * B, by positivity, by positivity, fun c hc => ?_⟩
  rw [twoZeroFSrc_eq]
  obtain ⟨h1, h2⟩ := h c hc
  exact ⟨by nlinarith only [mul_le_mul_of_nonneg_left h1 hAs.le],
    by nlinarith only [mul_le_mul_of_nonneg_left h2 hAs.le]⟩

/-- `testClass`, `decay`, `pos` for the source: `g = twoZeroBumpG triv d c`. -/
theorem twoZeroBump_fields_eventually_src (C : CommonSource) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c : ℝ in atTop, 0 < c ∧ ∀ d ∈ 𝒦, TestClass C.src (c / 12) (twoZeroBumpG C.src.triv d c) ∧
      (∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ t : ℝ, 0 ≤ t →
        |twoZeroBumpG C.src.triv d c t| ≤
          C0 * Real.exp (-4 * π * Real.sqrt (c / 12 * t) - π * Real.sqrt (3 * t / c))) ∧
      ∀ t : ℝ, tAiry c d.q + 1 ≤ t → 0 < twoZeroBumpG C.src.triv d c t := by
  filter_upwards [twoZeroBump_fields_eventually C.src.triv hK hA, eventually_ge_atTop (12 * C.a₀)]
    with c hT hcA0
  have hcA : C.a₀ ≤ c / 12 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 12)]
    linarith
  refine ⟨hT.1, fun d hd => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hT.2 d hd
  exact ⟨(C.at_ hcA).testClass_of_trivial h1, h2, h3⟩

/-- `Ψ^{mix}_g ∈ L¹(du)`. -/
theorem twoZeroBump_integrable_src (C : CommonSource) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦, Integrable (psiAirySrc C.src c (twoZeroBumpG C.src.triv d c)) := by
  filter_upwards [twoZeroBump_fields_eventually_src C hK hA, eventually_ge_atTop (12 * C.a₀)]
    with c hT hcA0 d hd
  have hcA : C.a₀ ≤ c / 12 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 12)]
    linarith
  exact integrable_psiAirySrc hT.1 (C.at_ hcA) ((hT.2 d hd).1)

/-- **`pmix:fixed-transfer`, first limit, `(f, r) = (2, 1)`, for the bumped functional with the cut of `ut:T2`.** -/
theorem twoZeroBump_window_field_src (C : CommonSource) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦, ∀ u ∈ Icc (-R) R,
      |(twoZeroFSrc C.src c)⁻¹ * psiAirySrc C.src c (twoZeroBumpG C.src.triv d c) u -
        twoZeroC₂ * d.Wr u| ≤ ε := by
  intro R hR ε hε
  filter_upwards [twoZeroBump_window_limit_src C (probBump C.src.triv) hK hA hR hε] with c h d hd u hu
  exact h d hd _ (le_bumpCut (probBump C.src.triv) (n + 2) c) u hu

/-- **The second limit, `(f, r) = (2, 1)`** (`pmix:fixed-transfer`, one-sided): for `ε > 0`, `c` large and `d ∈ 𝒦`,
`(F^{mix}_{2,c})^{-1} ∫ Ψ^{mix}_g du ≤ C₂ ∫ W_2 + ε`. -/
theorem twoZeroBump_limsup_field_src (C : CommonSource) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦,
      (twoZeroFSrc C.src c)⁻¹ * (∫ u, psiAirySrc C.src c (twoZeroBumpG C.src.triv d c) u) ≤
        twoZeroC₂ * (∫ u, d.Wr u) + ε := by
  intro ε hε
  have hAs := C.ampl_pos xiStar_pos
  have htv := (C.at_ (le_refl C.a₀)).tv_pos
  have hπ := Real.pi_pos
  filter_upwards [twoZeroBump_vacuum_core_src C (probBump C.src.triv) hK hA hε,
    twoZeroBump_gVac_bounds_src C (probBump C.src.triv) hK hA,
    eventually_gt_atTop (0 : ℝ),
    twoZeroF_eventually_ge C.src.triv (C.src.tv / (π * ε * C.src.ampl xiStar))]
    with c hV hg hc hFbig d hd
  have hFpos := twoZeroFSrc_pos C hc
  have hN := le_bumpCut (probBump C.src.triv) (n + 2) c
  rw [integral_psiAirySrc C.src hc, twoZeroBumpG_eq]
  refine limsup_arith (I := ∫ t in Ioi 0, combProfile c (d.bumpComb (probBump C.src.triv) c
      (bumpCut (probBump C.src.triv) (n + 2) c)) t * C.src.cardyV (c / 12) t)
    hFpos (hg d hd _ hN).2 ?_ ?_
  · have : 2 * twoZeroC₂ = CStar * kappaAiry := by unfold twoZeroC₂; ring
    rw [this]
    exact hV d hd _ hN
  · rw [twoZeroFSrc_eq]
    rw [div_le_iff₀ (by positivity)] at hFbig
    nlinarith only [hFbig, mul_pos hπ hε, hAs]

/-- **Vacuum positivity, `(f, r) = (2, 1)`** (`pmix:vac`): if `∫ W_2 ≤ -δ` on `𝒦`, there are `κ > 0` and a threshold beyond which
`κ c^{3/2} ≤ g_vac` for all `d ∈ 𝒦`. -/
theorem twoZeroBump_vac_eventually_src (C : CommonSource) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm)
    (hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ 𝒦, ∫ u, d.Wr u ≤ -δ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦,
      κ * c ^ ((3 : ℝ) / 2) ≤ C.src.gVac (c / 12) (twoZeroBumpG C.src.triv d c) := by
  obtain ⟨δ, hδ0, hW⟩ := hδ
  have hC := CStar_pos
  have hκ := kappaAiry_pos
  have hAs := C.ampl_pos xiStar_pos
  have htv := (C.at_ (le_refl C.a₀)).tv_pos
  obtain ⟨A, B, hA0, hB0, hAB⟩ := twoZeroFSrc_asymp C
  have hK0 : 0 < CStar * kappaAiry := by positivity
  have hε : 0 < CStar * kappaAiry * δ / 2 := by positivity
  have hπ := Real.pi_pos
  have hpos : 0 < π * (CStar * kappaAiry) * δ / 4 := by positivity
  refine ⟨π * (CStar * kappaAiry) * δ / 4 * A, by positivity, ?_⟩
  filter_upwards [twoZeroBump_vacuum_core_src C (probBump C.src.triv) hK hA hε,
    twoZeroBump_gVac_bounds_src C (probBump C.src.triv) hK hA,
    eventually_gt_atTop (0 : ℝ),
    twoZeroF_eventually_ge C.src.triv (C.src.tv / (π * (CStar * kappaAiry) * δ / 4 * C.src.ampl xiStar))]
    with c hV hg hc hFbig d hd
  have hFpos := twoZeroFSrc_pos C hc
  have hN := le_bumpCut (probBump C.src.triv) (n + 2) c
  have hbig : C.src.tv ≤ π * (CStar * kappaAiry) * δ / 4 * twoZeroFSrc C.src c := by
    rw [twoZeroFSrc_eq]
    rw [div_le_iff₀ (by positivity)] at hFbig
    nlinarith only [hFbig]
  have h := vac_arith (F := twoZeroFSrc C.src c) (K := CStar * kappaAiry) (δ := δ) hFpos hK0
    (hg d hd _ hN).2 (hW d hd) rfl (hV d hd _ hN) hbig
  have h2 := mul_le_mul_of_nonneg_left (hAB c hc).1 hpos.le
  rw [twoZeroBumpG_eq]
  linarith

/-! ### The package -/

/-- **`TwoZeroTransferData` for a source** (`pmix:fixed-transfer` at `(f, r) = (2, 1)`): the data `F`, `C₂`, `g`, and the fields
`testClass`, `decay`, `pos`, `window`, `integrable`, `limsup_le`, `vac` with the weight `V_s` of `src` and `Ā_s = TestClass src`. -/
structure SrcTwoZeroTransferData (C : CommonSource) {n : ℕ} (𝒦 : Set (TwoZeroDesign n)) where
  c₀ : ℝ
  C₂ : ℝ
  F : ℝ → ℝ
  g : TwoZeroDesign n → ℝ → ℝ → ℝ
  c₀_pos : 0 < c₀
  C₂_pos : 0 < C₂
  F_asymp : ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ c : ℝ, c₀ ≤ c →
    A * c ^ ((3 : ℝ) / 2) ≤ F c ∧ F c ≤ B * c ^ ((3 : ℝ) / 2)
  testClass : ∀ c : ℝ, c₀ ≤ c → ∀ d ∈ 𝒦, TestClass C.src (c / 12) (g d c)
  decay : ∀ c : ℝ, c₀ ≤ c → ∀ d ∈ 𝒦, ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ t : ℝ, 0 ≤ t →
    |g d c t| ≤ C0 * Real.exp (-4 * π * Real.sqrt (c / 12 * t) - π * Real.sqrt (3 * t / c))
  pos : ∀ c : ℝ, c₀ ≤ c → ∀ d ∈ 𝒦, ∀ t : ℝ, tAiry c d.q + 1 ≤ t → 0 < g d c t
  window : ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦, ∀ u ∈ Icc (-R) R,
    |(F c)⁻¹ * psiAirySrc C.src c (g d c) u - C₂ * d.Wr u| ≤ ε
  integrable : ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦, Integrable (psiAirySrc C.src c (g d c))
  limsup_le : ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦,
    (F c)⁻¹ * (∫ u, psiAirySrc C.src c (g d c) u) ≤ C₂ * (∫ u, d.Wr u) + ε
  vac : (∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ 𝒦, ∫ u, d.Wr u ≤ -δ) → ∃ κ : ℝ, 0 < κ ∧
    ∀ c : ℝ, c₀ ≤ c → ∀ d ∈ 𝒦, κ * c ^ ((3 : ℝ) / 2) ≤ C.src.gVac (c / 12) (g d c)

/-- A threshold for the `vac` field. -/
lemma twoZeroBump_vac_threshold_src (C : CommonSource) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ c₂ : ℝ, (∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ 𝒦, ∫ u, d.Wr u ≤ -δ) → ∃ κ : ℝ, 0 < κ ∧
      ∀ c : ℝ, c₂ ≤ c → ∀ d ∈ 𝒦,
        κ * c ^ ((3 : ℝ) / 2) ≤ C.src.gVac (c / 12) (twoZeroBumpG C.src.triv d c) := by
  by_cases hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ 𝒦, ∫ u, d.Wr u ≤ -δ
  · obtain ⟨κ, hκ, h⟩ := twoZeroBump_vac_eventually_src C hK hA hδ
    obtain ⟨c₁, hc₁⟩ := eventually_atTop.mp h
    exact ⟨c₁, fun _ => ⟨κ, hκ, fun c hc d hd => hc₁ c hc d hd⟩⟩
  · exact ⟨0, fun h => absurd h hδ⟩

/-- **`pmix:vac` / `pmix:fixed-transfer` at `(f, r) = (2, 1)`, for every common source**: for every `n ≥ 1` and every compact family `𝒦`
of admissible two-simple-zero designs, `SrcTwoZeroTransferData C 𝒦` exists.  The second limit is one-sided
(`limsup_le`), as in the single-weight `twoSimpleZeroTransfer_all`. -/
theorem twoSimpleZeroTransfer_src (C : CommonSource) {n : ℕ} (𝒦 : Set (TwoZeroDesign n))
    (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) : Nonempty (SrcTwoZeroTransferData C 𝒦) := by
  obtain ⟨c₁, h1⟩ := eventually_atTop.mp (twoZeroBump_fields_eventually_src C hK hA)
  obtain ⟨c₂, h2⟩ := twoZeroBump_vac_threshold_src C hK hA
  have hc₀ : 0 < max (max c₁ c₂) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hge : ∀ c : ℝ, max (max c₁ c₂) 1 ≤ c → c₁ ≤ c ∧ c₂ ≤ c := fun c hc =>
    ⟨(le_max_left _ _).trans ((le_max_left _ _).trans hc),
      (le_max_right _ _).trans ((le_max_left _ _).trans hc)⟩
  obtain ⟨A, B, hA0, hB0, hAB⟩ := twoZeroFSrc_asymp C
  refine ⟨{ c₀ := max (max c₁ c₂) 1
            C₂ := twoZeroC₂
            F := twoZeroFSrc C.src
            g := twoZeroBumpG C.src.triv
            c₀_pos := hc₀
            C₂_pos := twoZeroC₂_pos
            F_asymp := ⟨A, B, hA0, hB0, fun c hc => hAB c (hc₀.trans_le hc)⟩
            testClass := fun c hc d hd => (h1 c (hge c hc).1).2 d hd |>.1
            decay := fun c hc d hd => ((h1 c (hge c hc).1).2 d hd).2.1
            pos := fun c hc d hd => ((h1 c (hge c hc).1).2 d hd).2.2
            window := twoZeroBump_window_field_src C hK hA
            integrable := twoZeroBump_integrable_src C hK hA
            limsup_le := twoZeroBump_limsup_field_src C hK hA
            vac := fun hδ => ?_ }⟩
  obtain ⟨κ, hκ, h⟩ := h2 hδ
  exact ⟨κ, hκ, fun c hc d hd => h c (hge c hc).2 d hd⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.twoZeroBump_window_limit_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_window_limit_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.twoZeroBump_vacuum_core_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_vacuum_core_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.twoZeroBump_gVac_bounds_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_gVac_bounds_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.twoZeroBump_limsup_field_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_limsup_field_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.twoZeroBump_vac_eventually_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_vac_eventually_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.twoSimpleZeroTransfer_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoSimpleZeroTransfer_src

end FormalResearch.ModularBootstrap.Mixtures
