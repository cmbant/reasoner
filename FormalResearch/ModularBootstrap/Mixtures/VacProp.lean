module

public import FormalResearch.ModularBootstrap.Mixtures.VacCore

/-!
# `pmix:vac` for `(f, r) = (1, 0)`: Proposition V (i), (ii) and Property (P) for a common source

`positive_mixtures.tex`, Proposition PM.9 (`pmix:vac`) with `(f, r) = (1, 0)`, and the proof of `pmix:rigidity`(a)
("`pmix:vac` at `(f, r) = (1, 0)` gives Property (P) and the transfer of `𝓕_1`").

* `bumpSig_k7_src`: item (1) of `pmix:vac`: for `c'` with `c'/12 ≥ a₀` the test `g_w = ½(h^{(p)} - 𝓗_w h^{(p)})` is in the source test
  class, and `g_vac = ½ ∑_j coef_j H₀(b_{a - shift_j}) - π ∫_0^∞ h^{(p)} V_s dt` with comb term `≤ ‖λ‖_TV` (`pmix:crossing`(b), `k7_src`);
* `proposition_V_i_bumped_src`, `proposition_V_ii_bumped_src`: Proposition V (i), (ii) for `V_s`:
  `limsup (2/FK^{mix}) ∫ Ψ^{mix} du ≤ C_* V_D` and `V_D < 0 ⟹ g_vac ≥ π C_* |V_D| FK^{mix}/4 > 0`;
* `bumpG_good_src`, `bumpG_pos_src`, `bump_psi_limsup_src`: (P1), (P2), (P4) for `bumpG triv d N η σs`;
* `SrcEventualCombData`: the statements (P1)-(P4) of a design window for the source (the analogue of `EventualCombData`, with `V_s` in
  place of `prob.cardyV`); **`bumpEventualSrc`** is the instance for every window `D` whose profile is the Airy window `sigWinW N η σs`
  of an `f = 1` modification (first site anywhere, so the families `D(N, η_*, d)`, the displaced and the far-first-site families, i.e. `𝓕_1`
  with any terminal site `q < 0`), and **`pmix_vac_f1`** collects (1) and (2) of `pmix:vac` at `(f, r) = (1, 0)`.

Difference from the paper: the second limit is one-sided (`limsup ≤`), as in W-P5 (see `PM2_DESIGN.md`).
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
  FormalResearch.ModularBootstrap.Upper.Hankel FormalResearch.Special

/-- `g_vac` of the bumped `f = 1` finite modification for the source, `g_w = ½(h^{(p)} - 𝓗_w h^{(p)})`. -/
noncomputable def bumpSigGVacSrc (C : CommonSource) (d : BumpData) (N N' : ℕ) (η : ℝ) (σs : ℕ → ℝ)
    (c' : ℝ) : ℝ :=
  C.src.gVac (c' / 12)
    (pairOdd (combProfile c' (bumpSigComb d c' N N' η σs))
      (hankelTransform C.src.w (combProfile c' (bumpSigComb d c' N N' η σs))))

lemma bumpSigGVacSrc_eq (C : CommonSource) (d : BumpData) (N : ℕ) (η : ℝ) (σs : ℕ → ℝ) (c : ℝ) :
    bumpSigGVacSrc C d N (bumpCut d N c) η σs c = C.src.gVac (c / 12) (bumpG C.src.triv d N η σs c) := rfl

/-- **Item (1) of `pmix:vac` and the vacuum identity** (`pmix:crossing`(b)): `g_vac ≥ -‖λ‖_TV - π ∫_0^∞ h^{(p)} V_s`. -/
theorem bumpSigGVac_ge_src (C : CommonSource) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      TestClass C.src (c' / 12) (pairOdd (combProfile c' (bumpSigComb d c' N N' η σs))
        (hankelTransform C.src.w (combProfile c' (bumpSigComb d c' N N' η σs)))) ∧
      -C.src.tv - π * (∫ t in Ioi 0, combProfile c' (bumpSigComb d c' N N' η σs) t *
          C.src.cardyV (c' / 12) t) ≤ bumpSigGVacSrc C d N N' η σs c' := by
  filter_upwards [bumpSig_k7W C.src.triv d N hN hη0 hη1 σs, bumpSig_phaseHyp d N hN hη0 hη1 σs,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    eventually_ge_atTop (12 * C.a₀), eventually_gt_atTop (0 : ℝ)] with c' hK7 hph hin hcA hc0 N' hNN'
  have hcA' : C.a₀ ≤ c' / 12 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 12)]
    linarith
  have hAt : C.F.At (c' / 12) := C.at_ hcA'
  obtain ⟨hfN, hA, -⟩ := hph N' hNN'
  have hI : InnerCombHyp c' (bumpSigComb d c' N N' η σs) := hin N' _ _ hfN hA
  obtain ⟨hTest, hid, hn⟩ := k7_src hc0 hAt hI (hK7 N' hNN')
  refine ⟨hTest, ?_⟩
  have hre := congrArg Complex.re hid
  rw [← Complex.ofReal_mul, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re] at hre
  have h3 := (Complex.abs_re_le_norm _).trans hn
  have := (abs_le.mp h3).1
  unfold bumpSigGVacSrc
  rw [hre]
  linarith only [this]

/-- **Proposition V (i)** (`ut:Vac`) for the bumped `f = 1` designs and the source `V_s`, uniform in the cut `N' ≥ N`: for every `ε > 0` and
large `c'`, `(2/FK^{mix}) ∫ Ψ^{mix} du - C_* V_D ≤ ε` (`∫ Ψ^{mix} du = -g_vac/(2π)`). -/
theorem proposition_V_i_bumped_src (C : CommonSource) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      2 * (-bumpSigGVacSrc C d N N' η σs c' / (2 * π)) / FKc C.src.qMix 1 c' -
        CStar * windowIntegralSig N η σs ≤ ε := by
  have hπ := Real.pi_pos
  have htv := (C.at_ (le_refl C.a₀)).tv_pos
  filter_upwards [bumpSigGVac_ge_src C d N hN hη0 hη1 σs,
    vacuum_core_bumped_src C d N hN hη0 hη1 σs (half_pos hε),
    FKc_ge_mul_sqrt_of_pos C.qMix_pos (2 * C.src.tv / (π * ε)),
    eventually_gt_atTop (1 : ℝ)] with c' hg hc hFKbig hc1 N' hNN'
  have hcpos : 0 < c' := by linarith
  have hFK := FKc_pos C.qMix_pos 1 hcpos
  have hsc : 1 ≤ √c' := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hc1.le
  have h8 : 2 * C.src.tv / (π * ε) ≤ FKc C.src.qMix 1 c' :=
    le_trans (le_mul_of_one_le_right (by positivity) hsc) hFKbig
  have h9 : 2 * C.src.tv ≤ π * ε * FKc C.src.qMix 1 c' := by
    have := (div_le_iff₀ (by positivity)).mp h8
    linarith
  have hg' := (hg N' hNN').2
  have hc' := hc N' hNN'
  rw [sub_le_iff_le_add, div_le_iff₀ hFK]
  have e : 2 * (-bumpSigGVacSrc C d N N' η σs c' / (2 * π)) =
      -bumpSigGVacSrc C d N N' η σs c' / π := by
    field_simp
  rw [e, div_le_iff₀ hπ]
  nlinarith only [mul_le_mul_of_nonneg_left hc' hπ.le, hg', h9]

/-- **Proposition V (ii)** for the source: if `V_D < 0` then for large `c'`, `g_vac > 0` and
`g_vac ≥ π C_* |V_D| FK^{mix}/4`. -/
theorem proposition_V_ii_bumped_src (C : CommonSource) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) (hV : windowIntegralSig N η σs < 0) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      0 < bumpSigGVacSrc C d N N' η σs c' ∧
        π * CStar * |windowIntegralSig N η σs| * FKc C.src.qMix 1 c' / 4 ≤
          bumpSigGVacSrc C d N N' η σs c' := by
  have hπ := Real.pi_pos
  have hC := CStar_pos
  have htv := (C.at_ (le_refl C.a₀)).tv_pos
  have hVa : 0 < |windowIntegralSig N η σs| := abs_pos.mpr hV.ne
  have hε : 0 < CStar * |windowIntegralSig N η σs| / 2 := by positivity
  filter_upwards [bumpSigGVac_ge_src C d N hN hη0 hη1 σs,
    vacuum_core_bumped_src C d N hN hη0 hη1 σs hε,
    FKc_ge_mul_sqrt_of_pos C.qMix_pos
      (4 * C.src.tv / (π * CStar * |windowIntegralSig N η σs|)),
    eventually_gt_atTop (1 : ℝ)] with c' hg hc hFKbig hc1 N' hNN'
  have hcpos : 0 < c' := by linarith
  have hFK := FKc_pos C.qMix_pos 1 hcpos
  have hsc : 1 ≤ √c' := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hc1.le
  have hpos : 0 < π * CStar * |windowIntegralSig N η σs| := by positivity
  have h8 : 4 * C.src.tv / (π * CStar * |windowIntegralSig N η σs|) ≤ FKc C.src.qMix 1 c' :=
    le_trans (le_mul_of_one_le_right (by positivity) hsc) hFKbig
  have h9 : 4 * C.src.tv ≤ π * CStar * |windowIntegralSig N η σs| * FKc C.src.qMix 1 c' := by
    have := (div_le_iff₀ hpos).mp h8
    linarith
  have habs : |windowIntegralSig N η σs| = -windowIntegralSig N η σs := abs_of_neg hV
  have hVc : π * (∫ t in Ioi 0,
        combProfile c' (bumpSigComb d c' N N' η σs) t * C.src.cardyV (c' / 12) t) ≤
      -(π * CStar * |windowIntegralSig N η σs| * FKc C.src.qMix 1 c' / 2) := by
    have := mul_le_mul_of_nonneg_left (hc N' hNN') hπ.le
    rw [habs] at this ⊢
    nlinarith only [this]
  have hlow : π * CStar * |windowIntegralSig N η σs| * FKc C.src.qMix 1 c' / 4 ≤
      bumpSigGVacSrc C d N N' η σs c' := by
    linarith only [(hg N' hNN').2, hVc, h9]
  exact ⟨lt_of_lt_of_le (by positivity) hlow, hlow⟩

/-! ### (P1), (P2), (P4) for `bumpG` -/

/-- (P1): membership in the source test class and the exponential decay of `g_w = bumpG triv`. -/
theorem bumpG_good_src (C : CommonSource) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∀ᶠ c in atTop, 0 < c ∧ TestClass C.src (c / 12) (bumpG C.src.triv d N η σs c) ∧
      ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ t : ℝ, 0 ≤ t →
        |bumpG C.src.triv d N η σs c t| ≤ C0 * Real.exp (-4 * π * √(c / 12 * t) - π * √(3 * t / c)) := by
  filter_upwards [bumpG_good C.src.triv d N hN hη0 hη1 σs, eventually_ge_atTop (12 * C.a₀)]
    with c hgood hcA
  obtain ⟨hc, hT, hdec⟩ := hgood
  have hcA' : C.a₀ ≤ c / 12 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 12)]
    linarith
  exact ⟨hc, (C.at_ hcA').testClass_of_trivial hT, hdec⟩

/-- (P4): `∫ Ψ^{mix} du ≤ V_D + ε` for the scaled window density of `bumpG`. -/
theorem bump_psi_limsup_src (C : CommonSource) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop,
      ∫ u, psiScaleSrc C.src c * psiAirySrc C.src c (bumpG C.src.triv d N η σs c) u ≤
        windowIntegralSig N η σs + ε := by
  have hCs := CStar_pos
  filter_upwards [proposition_V_i_bumped_src C d N hN hη0 hη1 σs (ε := ε * CStar) (by positivity),
    eventually_gt_atTop (0 : ℝ)] with c hV hc0
  have hV' := hV (bumpCut d N c) (le_bumpCut d N c)
  have hFK := FKc_pos C.qMix_pos 1 hc0
  rw [integral_const_mul, integral_psiAirySrc C.src hc0]
  have e : psiScaleSrc C.src c * (-C.src.gVac (c / 12) (bumpG C.src.triv d N η σs c) / (2 * π)) =
      (2 * (-bumpSigGVacSrc C d N (bumpCut d N c) η σs c / (2 * π)) / FKc C.src.qMix 1 c) / CStar := by
    unfold psiScaleSrc
    rw [bumpSigGVacSrc_eq C d N η σs c]
    field_simp
  rw [e, div_le_iff₀ hCs]
  have : windowIntegralSig N η σs * CStar + ε * CStar = CStar * windowIntegralSig N η σs + ε * CStar := by ring
  linarith

/-! ### Property (P): eventual comb data for a source -/

/-- The statements `(P1)`-`(P4)` of `sr:P` for one design window `D` and the source `src`, for large `c`
(the analogue of `Upper.Assembly.EventualCombData`, `V_s` in place of `prob.cardyV`). -/
structure SrcEventualCombData (src : ShiftSource) (D : Window) where
  g : ℝ → ℝ → ℝ
  scale : ℝ → ℝ
  tf : ℝ → ℝ
  good : ∀ᶠ c in atTop, 0 < c ∧ 0 < scale c ∧ TestClass src (c / 12) (g c) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      |g c t| ≤ C * Real.exp (-4 * π * √(c / 12 * t) - π * √(3 * t / c))) ∧
    0 ≤ tf c + 1 ∧ ∀ t : ℝ, tf c + 1 ≤ t → 0 ≤ g c t
  theta : Tendsto (fun c => uAiry c (tf c + 1)) atTop (𝓝 D.uF)
  window : ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∀ᶠ c in atTop, ∀ u ∈ Icc (-R) R,
    |scale c * psiAirySrc src c (g c) u - D.W u| ≤ ε
  limsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ c in atTop,
    ∫ u, scale c * psiAirySrc src c (g c) u ≤ D.V + ε

/-- **Property (P) of `sr:P` for a common source, `(f, r) = (1, 0)`** (`pmix:vac`; `bumpEventual` for the source): for every window `D`
whose profile is the Airy window `sigWinW N η σs` of the `f = 1` modification with offsets `σs` and whose first site is
`u_f = -κ σ_1`, the bumped design `g_w = bumpG triv` (the bump of `rpParams (w - 1)`) satisfies (P1)-(P4) for the source, with the scale
`2/(C_* FK^{mix}_c)`. -/
noncomputable def bumpEventualSrc (C : CommonSource) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) (D : Window) (hW : D.W = sigWinW N η σs)
    (hF : D.uF = -(kappaAiry * σs 1)) : SrcEventualCombData C.src D where
  g := bumpG C.src.triv (rpParams (C.src.triv.w - 1)).bumpData N η σs
  scale := psiScaleSrc C.src
  tf := sigTf σs
  good := by
    filter_upwards [bumpG_good_src C (rpParams (C.src.triv.w - 1)).bumpData N hN hη.le hη1 σs,
      bumpG_pos C.src.triv N hN hη hη1 σs] with c hgood hpos
    obtain ⟨hc, hT, hdec⟩ := hgood
    refine ⟨hc, psiScaleSrc_pos C hc, hT, hdec, ?_, fun t ht => (hpos t ht).le⟩
    unfold sigTf; positivity
  theta := by rw [hF]; exact uAiry_sigTf σs
  window := fun R hR ε hε => by
    rw [hW]; exact bump_psi_uniform_src C _ N hN hη hη1 σs hR hε
  limsup := fun ε hε => by
    have hV : D.V = windowIntegralSig N η σs := by
      unfold Window.V windowIntegralSig; rw [hW]; rfl
    rw [hV]; exact bump_psi_limsup_src C _ N hN hη.le hη1 σs hε

/-- **`pmix:vac`, `(f, r) = (1, 0)`** (Proposition PM.9, items (1), (2) with the first limit and the one-sided second limit): for a
common source `C`, `N ≥ 1`, `0 < η_* ≤ 1/4` and offsets `σs` (the window `W = sigWinW N η σs`, `V_D = windowIntegralSig N η σs`), the test
`g_w = bumpG triv` of the bump `rpParams (w - 1)` satisfies, for large `c` (with `FK^{mix} = FKc 𝔮_mix 1 c`):
(1) `g_w ∈ Ā_{w,src}`, `|g_w| ≤ C e^{-4π√(a t) - π x}`, `g_w > 0` on `t ≥ t_f + 1`;
(2) `(2/(C_* FK^{mix})) Ψ^{mix}_{g_w} → W` locally uniformly, `limsup (2/(C_* FK^{mix})) ∫ Ψ^{mix} du ≤ V_D`, and if `V_D < 0`
then `g_vac ≥ π C_* |V_D| FK^{mix}/4 > 0` (along every cut). -/
theorem pmix_vac_f1 (C : CommonSource) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) :
    let g := bumpG C.src.triv (rpParams (C.src.w - 1)).bumpData N η σs
    (∀ᶠ c in atTop, 0 < c ∧ TestClass C.src (c / 12) (g c) ∧
      (∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ t : ℝ, 0 ≤ t →
        |g c t| ≤ C0 * Real.exp (-4 * π * √(c / 12 * t) - π * √(3 * t / c))) ∧
      ∀ t : ℝ, sigTf σs c + 1 ≤ t → 0 < g c t) ∧
    (∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∀ᶠ c in atTop, ∀ u ∈ Icc (-R) R,
      |psiScaleSrc C.src c * psiAirySrc C.src c (g c) u - sigWinW N η σs u| ≤ ε) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ c in atTop,
      ∫ u, psiScaleSrc C.src c * psiAirySrc C.src c (g c) u ≤ windowIntegralSig N η σs + ε) ∧
    (windowIntegralSig N η σs < 0 → ∀ᶠ c in atTop,
      0 < C.src.gVac (c / 12) (g c) ∧
        π * CStar * |windowIntegralSig N η σs| * FKc C.src.qMix 1 c / 4 ≤ C.src.gVac (c / 12) (g c)) := by
  intro g
  refine ⟨?_, fun R hR ε hε => bump_psi_uniform_src C _ N hN hη hη1 σs hR hε,
    fun ε hε => bump_psi_limsup_src C _ N hN hη.le hη1 σs hε, fun hV => ?_⟩
  · filter_upwards [bumpG_good_src C (rpParams (C.src.w - 1)).bumpData N hN hη.le hη1 σs,
      bumpG_pos C.src.triv N hN hη hη1 σs] with c hgood hpos
    obtain ⟨hc, hT, hdec⟩ := hgood
    exact ⟨hc, hT, hdec, hpos⟩
  · filter_upwards [proposition_V_ii_bumped_src C (rpParams (C.src.w - 1)).bumpData N hN hη.le hη1 σs hV]
      with c h
    exact h (bumpCut _ N c) (le_bumpCut _ N c)

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.bumpSigGVac_ge_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpSigGVac_ge_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.proposition_V_i_bumped_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_V_i_bumped_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.proposition_V_ii_bumped_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_V_ii_bumped_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.bumpEventualSrc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpEventualSrc

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_vac_f1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_vac_f1

end FormalResearch.ModularBootstrap.Mixtures
