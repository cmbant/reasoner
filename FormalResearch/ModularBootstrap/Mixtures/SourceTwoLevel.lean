module

public import FormalResearch.ModularBootstrap.Mixtures.SourceRigidity
public import FormalResearch.ModularBootstrap.Mixtures.VacTwoZero
public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidity
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroTransferW

/-!
# Consumer ports for `CommonSource` two-level Clark rigidity (`pmix:rigidity`(b))

`positive_mixtures.tex`, Theorem PM.12 (`pmix:rigidity`, part (b)): consumes
`twoSimpleZeroTransfer_src` (`Mixtures.VacTwoZero`), `twoZeroNegativeVacuum`, and
`twoZeroIdealApprox` (`TwoLevel.*`) to deliver:

* `src_designPropertyP_twoZero`: Property `sr:P` for `twoZeroClass` on any `SourceCrossingSequence`;
* `src_two_level_exclusion`: strict exclusion tests and non-existence of crossing measures on
  `{t₁} ∪ [t₂, ∞)` for any `A₁ < A_opt` and `A₂ > A_2^*(A₁)`;
* `SrcTwoLevelSequence`, `src_theorem_two_six`, `src_tendsto_atom_weight`: Clark measure vague
  convergence `μ_j → μ_α` (`α = clarkAngle (-A₁ / c_*)`) and atom weight recovery at `u(t₁)`;
* `src_two_level_constrained_attainment`: constrained primal attainment at `B_n` on `{t₁} ∪ [B_n, ∞)`.

All results are proved unconditionally.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ModularBootstrap
  FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.FixedWeight
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.TwoLevel

/-! ### 1. `SrcTwoZeroTransferData` -> `DesignPropertyP S.μS twoZeroClass` -/

private lemma srcTwoZero_F_pos {C : CommonSource} {n : ℕ} {d : TwoZeroDesign n}
    (X : SrcTwoZeroTransferData C {d}) {c : ℝ} (hc : X.c₀ ≤ c) : 0 < X.F c := by
  obtain ⟨A, B, hA, _, h⟩ := X.F_asymp
  have hc0 : 0 < c := lt_of_lt_of_le X.c₀_pos hc
  exact lt_of_lt_of_le (by positivity) (h c hc).1

/-- For a single two-simple-zero design `d`, `SrcTwoZeroTransferData C {d}` provides
`SrcEventualCombData` for `twoZeroWin d hd`. -/
noncomputable def SrcTwoZeroTransferData.toEventual {C : CommonSource} {n : ℕ} {d : TwoZeroDesign n}
    (hd : d.Adm) (X : SrcTwoZeroTransferData C {d}) :
    SrcEventualCombData C.src (twoZeroWin d hd) where
  g := X.g d
  scale c := (X.C₂ * X.F c)⁻¹
  tf c := tAiry c d.q
  good := by
    filter_upwards [eventually_ge_atTop X.c₀] with c hc
    have hc0 : 0 < c := lt_of_lt_of_le X.c₀_pos hc
    have hF : 0 < X.F c := srcTwoZero_F_pos X hc
    have hC2 := X.C₂_pos
    refine ⟨hc0, by positivity, X.testClass c hc d rfl, X.decay c hc d rfl, ?_,
      fun t ht => (X.pos c hc d rfl t ht).le⟩
    linarith [tAiry_nonneg hc0 d.q]
  theta := by
    rw [twoZeroWin_uF]
    exact tendsto_uAiry_tAiry_add_one d.q
  window R hR ε hε := by
    simp only [twoZeroWin_W]
    have hC2 := X.C₂_pos
    filter_upwards [X.window R hR (X.C₂ * ε) (mul_pos hC2 hε), eventually_ge_atTop X.c₀]
      with c hw hc u hu
    have hF := (srcTwoZero_F_pos X hc).ne'
    have hw' := hw d rfl u hu
    have e : (X.C₂ * X.F c)⁻¹ * psiAirySrc C.src c (X.g d c) u - d.Wr u =
        X.C₂⁻¹ * ((X.F c)⁻¹ * psiAirySrc C.src c (X.g d c) u - X.C₂ * d.Wr u) := by
      field_simp
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hC2)]
    calc X.C₂⁻¹ * |(X.F c)⁻¹ * psiAirySrc C.src c (X.g d c) u - X.C₂ * d.Wr u|
        ≤ X.C₂⁻¹ * (X.C₂ * ε) := mul_le_mul_of_nonneg_left hw' (inv_pos.2 hC2).le
      _ = ε := by field_simp
  limsup ε hε := by
    have hV : (twoZeroWin d hd).V = ∫ u, d.Wr u := rfl
    rw [hV]
    have hC2 := X.C₂_pos
    filter_upwards [X.limsup_le (X.C₂ * ε) (mul_pos hC2 hε), eventually_ge_atTop X.c₀]
      with c hlim hc
    have hlim' := hlim d rfl
    have e : ∫ u, (X.C₂ * X.F c)⁻¹ * psiAirySrc C.src c (X.g d c) u =
        X.C₂⁻¹ * ((X.F c)⁻¹ * ∫ u, psiAirySrc C.src c (X.g d c) u) := by
      rw [integral_const_mul]; field_simp
    rw [e]
    calc X.C₂⁻¹ * ((X.F c)⁻¹ * ∫ u, psiAirySrc C.src c (X.g d c) u)
        ≤ X.C₂⁻¹ * ((X.C₂ * ∫ u, d.Wr u) + X.C₂ * ε) :=
          mul_le_mul_of_nonneg_left hlim' (inv_pos.2 hC2).le
      _ = (∫ u, d.Wr u) + ε := by field_simp

/-- **Property `sr:P` for the two-simple-zero windows on every `CommonSource`**
(`pmix:vac` at `(2, 1)` -> `sr:P`). -/
theorem src_designPropertyP_twoZero (C : CommonSource) (S : SourceCrossingSequence C) :
    DesignPropertyP S.μS twoZeroClass := by
  refine src_designPropertyP_of_comb S fun D hD => ?_
  obtain ⟨n, hn, d, hd, rfl⟩ := hD
  obtain ⟨X⟩ := twoSimpleZeroTransfer_src C (𝒦 := {d})
    (isCompactFamily_singleton d)
    (fun d' h => by rw [mem_singleton_iff.1 h]; exact hd)
  exact ⟨(X.toEventual hd).toComb S⟩

/-! ### 2. Two-level exclusion above `A₂*(A₁)` (`pmix:rigidity`(b)) -/

/-- Exclusion test functional of `pmix:rigidity`(b) for a `CommonSource`: for `A₁ < A_opt` and
`δ > 0`, for large `c` there is `g ∈ Ā_{w,src}` with `g_vac > 0`, `g(t₁) > 0`, and `g > 0` on
`[t₂, ∞)` where `t₂ = levelTime (A₂*(A₁) + δ) c`. -/
theorem src_exists_two_level_exclusion_functional (C : CommonSource) {A₁ δ : ℝ}
    (hA₁ : A₁ < Aopt) (hδ : 0 < δ) :
    ∀ᶠ c : ℝ in atTop, ∃ g : ℝ → ℝ, TestClass C.src (c / 12) g ∧ 0 < C.src.gVac (c / 12) g ∧
      0 < g (levelTime A₁ c) ∧ ∀ t, levelTime (A2star A₁ + δ) c ≤ t → 0 < g t := by
  have hcs := cStar_pos
  have hu₁ : airyZero 1 < -A₁ / cStar := mem_gap_one_of_lt_Aopt hA₁
  set u₁ : ℝ := -A₁ / cStar
  set α : ℝ := clarkAngle u₁
  have hz₁ : clarkNode α 1 = u₁ := (clarkAngle_spec hu₁).2
  have hsin : Real.sin α ≠ 0 := sin_clarkAngle_ne_zero hu₁
  have hz₂ : clarkNode α 2 < 0 := clarkNode_two_lt_zero α
  have hA2 : A2star A₁ = -(cStar * clarkNode α 2) := by
    unfold A2star
    rw [abs_of_neg hz₂]; ring
  obtain ⟨K, hK3, hKclose⟩ : ∃ K : ℕ, 3 ≤ K ∧ clarkNode α 2 - δ / (3 * cStar) < windowOptimum α K := by
    have h := (tendsto_windowOptimum hsin).eventually
      (lt_mem_nhds (show clarkNode α 2 - δ / (3 * cStar) < clarkNode α 2 by linarith [show 0 < δ / (3 * cStar) by positivity]))
    exact (h.and (eventually_ge_atTop 3)).exists.imp fun K hK => ⟨hK.2, hK.1⟩
  set us : ℝ := windowOptimum α K
  have hus_le : windowInt α K us ≤ 0 := (windowOptimum_isGreatest hsin hK3).1
  set u₂ : ℝ := us - δ / (6 * cStar)
  have hslope := windowSlope_pos hsin hK3
  have hint : windowInt α K u₂ < 0 := by
    have h1 := windowInt_affine hsin hK3 u₂
    have h2 := windowInt_affine hsin hK3 us
    have : 0 < δ / (6 * cStar) := by positivity
    nlinarith
  have hu₂pos : -(cStar * u₂) < A2star A₁ + δ := by
    rw [hA2]
    have : δ / (3 * cStar) * cStar = δ / 3 := by field_simp
    have h6 : δ / (6 * cStar) * cStar = δ / 6 := by field_simp
    have hlt : cStar * (clarkNode α 2 - δ / (3 * cStar)) < cStar * us :=
      mul_lt_mul_of_pos_left hKclose hcs
    nlinarith
  obtain ⟨n, hn, d, hd, hdq, hdp, hneg⟩ := twoZeroNegativeVacuum α hsin K hK3 u₂ hint
  obtain ⟨X⟩ := twoSimpleZeroTransfer_src C (𝒦 := {d})
    (isCompactFamily_singleton d)
    (fun d' h => by rw [mem_singleton_iff.1 h]; exact hd)
  obtain ⟨κ, hκ, hvac⟩ := X.vac ⟨-∫ u, d.Wr u, by linarith, fun d' h => by
    rw [mem_singleton_iff.1 h]; linarith⟩
  have hw₁ : 0 < d.Wr u₁ := d.Wr_pos_of_gt hd (by rw [← hz₁]; exact hdp)
  have hwin := X.window (|u₁| + 1) (by positivity) (X.C₂ * d.Wr u₁ / 4)
    (div_pos (mul_pos X.C₂_pos hw₁) (by norm_num))
  have hulim := tendsto_uAiry_levelTime A₁
  have hWr_ev : ∀ᶠ c : ℝ in atTop, d.Wr u₁ / 2 < d.Wr (uAiry c (levelTime A₁ c)) :=
    (d.continuous_Wr.continuousAt.tendsto.comp hulim).eventually (lt_mem_nhds (by linarith))
  have hIcc : ∀ᶠ c : ℝ in atTop, uAiry c (levelTime A₁ c) ∈ Icc (-(|u₁| + 1)) (|u₁| + 1) :=
    hulim.eventually (Icc_mem_nhds (by linarith [neg_abs_le u₁]) (by linarith [le_abs_self u₁]))
  have hpt := eventually_tAiry_add_one_le_levelTime (u := u₂) (B := A2star A₁ + δ) (by linarith)
  filter_upwards [eventually_ge_atTop X.c₀, hwin, hWr_ev, hIcc, hpt, eventually_le_levelTime A₁ 1,
    eventually_ge_atTop (12 * C.a₀), eventually_gt_atTop (0 : ℝ)] with
    c hc hw hWr hI hpt' ht1 hc12 hc0
  have hF := srcTwoZero_F_pos X hc
  have hC2 := X.C₂_pos
  have hAt : C.F.At (c / 12) := C.at_ (by linarith)
  refine ⟨X.g d c, X.testClass c hc d rfl, ?_, ?_, ?_⟩
  · have := hvac c hc d rfl
    have h3 : 0 < c ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hc0 _
    exact lt_of_lt_of_le (by positivity) this
  · set t₁ : ℝ := levelTime A₁ c
    have ht0 : 0 ≤ t₁ := by linarith
    have hψ := psiAirySrc_uAiry C.src hc0 (X.g d c) ht0
    have hw' := hw d rfl _ hI
    have hlow : 0 < (X.F c)⁻¹ * psiAirySrc C.src c (X.g d c) (uAiry c t₁) := by
      have := (abs_le.1 hw').1
      have h2 : 0 < X.C₂ * d.Wr u₁ := mul_pos hC2 hw₁
      nlinarith [mul_lt_mul_of_pos_left hWr hC2]
    have hpsi : 0 < psiAirySrc C.src c (X.g d c) (uAiry c t₁) := by
      by_contra hle
      push Not at hle
      have := mul_nonpos_of_nonneg_of_nonpos (inv_pos.2 hF).le hle
      linarith
    rw [hψ] at hpsi
    have hV0 : 0 ≤ C.src.cardyV (c / 12) t₁ := hAt.nonneg_V ht0
    have hJ : 0 < jAiry c t₁ := jAiry_pos hc0 (by linarith)
    by_contra hle
    push Not at hle
    have h1 : X.g d c t₁ * C.src.cardyV (c / 12) t₁ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hV0
    have := mul_nonpos_of_nonpos_of_nonneg h1 hJ.le
    linarith
  · intro t ht
    refine X.pos c hc d rfl t ?_
    rw [hdq]; linarith

/-- **`pmix:rigidity`(b), strict exclusion above `A₂*(A₁)`**: for any `A₁ < A_opt` and `δ > 0`,
for all large `c` there is a test `g ∈ Ā_{w,src}` strictly positive on `{levelTime A₁ c} ∪ [levelTime (A₂*(A₁)+δ) c, ∞)`
with `g_vac > 0`, and hence no mixed crossing measure is carried by that set. -/
theorem src_two_level_exclusion (C : CommonSource) {A₁ δ : ℝ} (hA₁ : A₁ < Aopt) (hδ : 0 < δ) :
    ∀ᶠ c : ℝ in atTop,
      (∃ g : ℝ → ℝ, TestClass C.src (c / 12) g ∧ 0 < C.src.gVac (c / 12) g ∧
        0 ≤ g (levelTime A₁ c) ∧ ∀ t, levelTime (A2star A₁ + δ) c ≤ t → 0 < g t) ∧
      ∀ meas : SourceCrossingMeasure C.src (c / 12),
        ¬ meas.ν ({levelTime A₁ c} ∪ Ici (levelTime (A2star A₁ + δ) c))ᶜ = 0 := by
  filter_upwards [src_exists_two_level_exclusion_functional C hA₁ hδ,
    eventually_ge_atTop (12 * C.a₀), eventually_le_levelTime A₁ 0,
    eventually_gt_atTop (0 : ℝ)] with c hg hc12 hlt hc0
  have hAt : C.F.At (c / 12) := C.at_ (by linarith)
  refine ⟨?_, fun meas hν => ?_⟩
  · obtain ⟨g, h1, h2, h3, h4⟩ := hg
    exact ⟨g, h1, h2, h3.le, h4⟩
  · obtain ⟨g, h1, h2, h3, h4⟩ := hg
    have hc_lt : levelTime A₁ c < levelTime (A2star A₁ + δ) c :=
      levelTime_lt hc0 (by linarith [(A2star_mem_Ioo hA₁).1])
    have hnu_iio : meas.ν (Iio (levelTime A₁ c)) = 0 :=
      measure_mono_null (fun t ht => by
        rintro (rfl | ht')
        · exact absurd rfl (ne_of_lt ht)
        · exact not_le.2 (ht.trans hc_lt) (mem_Ici.1 ht')) hν
    have hae : ∀ᵐ t ∂meas.ν, t ∈ ({levelTime A₁ c} ∪ Ici (levelTime (A2star A₁ + δ) c)) :=
      (measure_eq_zero_iff_ae_notMem.1 hν).mono fun _ ht => not_not.1 ht
    obtain ⟨hint, hle⟩ := (pmix_crossing_a hAt meas h1).1 ⟨levelTime (A2star A₁ + δ) c, fun t ht => (h4 t ht).le⟩
    have hnn : 0 ≤ᵐ[meas.ν] g := hae.mono fun t ht => by
      rcases ht with rfl | ht
      · exact h3.le
      · exact (h4 t (mem_Ici.1 ht)).le
    have hI : 0 ≤ ∫ t, g t ∂meas.ν := integral_nonneg_of_ae hnn
    linarith

/-! ### 3. Two-level crossing sequences and Clark rigidity (`pmix:rigidity`(b)) -/

/-- A sequence of `CommonSource` crossing measures supported on `{t₁} ∪ [τ, ∞)` with
`t₁ = ξ̄ c + A₁ c^{1/3} + o(c^{1/3})` and `τ ≥ ξ̄ c + (A₂*(A₁) - o(1)) c^{1/3}`. -/
structure SrcTwoLevelSequence (C : CommonSource) (A₁ : ℝ) where
  c : ℕ → ℝ
  meas : ∀ j, SourceCrossingMeasure C.src (c j / 12)
  t₁ : ℕ → ℝ
  τ : ℕ → ℝ
  tendsto_c : Tendsto c atTop atTop
  c_pos : ∀ j, 0 < c j
  shift_le : ∀ j, 12 * C.a₀ ≤ c j
  t₁_pos : ∀ j, 0 < t₁ j
  lowest : ∀ j, (meas j).ν (Iio (t₁ j)) = 0
  supp : ∀ j, (meas j).ν ({t₁ j} ∪ Ici (τ j))ᶜ = 0
  t₁_asymp : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, |t₁ j - levelTime A₁ (c j)| ≤ ε * (c j) ^ ((1 : ℝ) / 3)
  τ_lower : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, levelTime (A2star A₁ - ε) (c j) ≤ τ j

namespace SrcTwoLevelSequence

variable {C : CommonSource} {A₁ : ℝ} (S : SrcTwoLevelSequence C A₁)

def toCrossingSequence : SourceCrossingSequence C where
  c := S.c
  τ := S.t₁
  meas := S.meas
  tendsto_c := S.tendsto_c
  c_pos := S.c_pos
  shift_le := S.shift_le
  τ_pos := S.t₁_pos
  gap := S.lowest

noncomputable def μ (j : ℕ) : Measure ℝ := S.toCrossingSequence.μS j

instance (j : ℕ) : IsLocallyFiniteMeasure (S.μ j) :=
  isLocallyFiniteMeasure_spectralMeasureSrc C (S.c_pos j) (S.shift_le j) (S.meas j) (S.t₁_pos j) (S.lowest j)

lemma μ_Ioi_null (j : ℕ) : S.μ j (Ioi (uAiry (S.c j) (S.t₁ j))) = 0 :=
  S.toCrossingSequence.supp j

theorem spectral_gap_null (j : ℕ) :
    S.μ j (Ioo (uAiry (S.c j) (S.τ j)) (uAiry (S.c j) (S.t₁ j))) = 0 := by
  have hc := S.c_pos j
  unfold μ SourceCrossingSequence.μS spectralMeasureSrc
  change ((((S.meas j).ν.restrict (Ioi 0)).withDensity (spectralDensitySrc C.src (S.c j))).map
    (uAiry (S.c j))) _ = 0
  rw [Measure.map_apply (continuous_uAiry _).measurable measurableSet_Ioo]
  refine withDensity_absolutelyContinuous _ _ ?_
  have hsub : uAiry (S.c j) ⁻¹' Ioo (uAiry (S.c j) (S.τ j)) (uAiry (S.c j) (S.t₁ j)) ⊆
      ({S.t₁ j} ∪ Ici (S.τ j))ᶜ := fun t ht => by
    obtain ⟨h1, h2⟩ := ht
    have ha : S.t₁ j < t := by
      by_contra h
      exact absurd (uAiry_antitone hc (not_lt.1 h)) (not_le.2 h2)
    have hb : t < S.τ j := by
      by_contra h
      exact absurd (uAiry_antitone hc (not_lt.1 h)) (not_le.2 h1)
    rintro (h | h)
    · exact ha.ne' h
    · exact absurd (mem_Ici.1 h) (not_le.2 hb)
  refine le_antisymm ?_ bot_le
  calc ((S.meas j).ν.restrict (Ioi 0)) _ ≤ (S.meas j).ν _ := Measure.restrict_le_self _
    _ ≤ (S.meas j).ν ({S.t₁ j} ∪ Ici (S.τ j))ᶜ := measure_mono hsub
    _ = 0 := S.supp j

theorem tendsto_uAiry_t₁ : Tendsto (fun j => uAiry (S.c j) (S.t₁ j)) atTop (𝓝 (-A₁ / cStar)) := by
  have hcs := cStar_pos
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set ε : ℝ := δ * cStar / 3
  have hε : 0 < ε := by positivity
  have h1 := (tendsto_uAiry_levelTime (A₁ + ε)).comp S.tendsto_c
  have h2 : ∀ᶠ j in atTop, -A₁ / cStar - δ < uAiry (S.c j) (levelTime (A₁ + ε) (S.c j)) := by
    refine h1.eventually (lt_mem_nhds ?_)
    have : -(A₁ + ε) / cStar = -A₁ / cStar - δ / 3 := by dsimp [ε]; field_simp; ring
    linarith
  have h3 := (tendsto_uAiry_levelTime (A₁ - ε)).comp S.tendsto_c
  have h4 : ∀ᶠ j in atTop, uAiry (S.c j) (levelTime (A₁ - ε) (S.c j)) < -A₁ / cStar + δ := by
    refine h3.eventually (gt_mem_nhds ?_)
    have : -(A₁ - ε) / cStar = -A₁ / cStar + δ / 3 := by dsimp [ε]; field_simp; ring
    linarith
  filter_upwards [S.t₁_asymp ε hε, h2, h4] with j hbd ha hb
  have hpos := S.c_pos j
  have hup : S.t₁ j ≤ levelTime (A₁ + ε) (S.c j) := by
    have := (abs_le.1 hbd).2
    have e : levelTime (A₁ + ε) (S.c j) - levelTime A₁ (S.c j) = ε * (S.c j) ^ ((1 : ℝ) / 3) := by
      rw [levelTime_sub]; ring
    linarith
  have hlo : levelTime (A₁ - ε) (S.c j) ≤ S.t₁ j := by
    have := (abs_le.1 hbd).1
    have e : levelTime A₁ (S.c j) - levelTime (A₁ - ε) (S.c j) = ε * (S.c j) ^ ((1 : ℝ) / 3) := by
      rw [levelTime_sub]; ring
    linarith
  have h1' := ha.trans_le (uAiry_antitone hpos hup)
  have h2' := (uAiry_antitone hpos hlo).trans_lt hb
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

theorem eventually_uAiry_τ_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, uAiry (S.c j) (S.τ j) ≤ -A2star A₁ / cStar + ε := by
  have hcs := cStar_pos
  set δ : ℝ := ε * cStar / 2
  have hδ : 0 < δ := by positivity
  have hlim := (tendsto_uAiry_levelTime (A2star A₁ - δ)).comp S.tendsto_c
  have h1 : ∀ᶠ j in atTop, uAiry (S.c j) (levelTime (A2star A₁ - δ) (S.c j)) <
      -A2star A₁ / cStar + ε := by
    refine hlim.eventually (gt_mem_nhds ?_)
    have : -(A2star A₁ - δ) / cStar = -A2star A₁ / cStar + ε / 2 := by dsimp [δ]; field_simp; ring
    linarith
  filter_upwards [S.τ_lower δ hδ, h1] with j hj1 hj2
  exact ((uAiry_antitone (S.c_pos j) hj1).trans_lt hj2).le

noncomputable def twoLevelSupport (hA : A₁ < Aopt) :
    TwoLevelSupport S.μ (clarkNode (clarkAngle (-A₁ / cStar)) 1)
      (clarkNode (clarkAngle (-A₁ / cStar)) 2) where
  s₁ j := uAiry (S.c j) (S.t₁ j)
  s₂ j := uAiry (S.c j) (S.τ j)
  tendsto_s₁ := by
    rw [(clarkAngle_spec (mem_gap_one_of_lt_Aopt hA)).2]
    exact S.tendsto_uAiry_t₁
  s₂_le ε hε := by
    have h := S.eventually_uAiry_τ_le hε
    have e : -A2star A₁ / cStar = clarkNode (clarkAngle (-A₁ / cStar)) 2 := by
      rw [A2star_eq_neg_cStar_mul hA]
      have := cStar_pos
      field_simp
    rw [e] at h
    exact h
  null_top := S.μ_Ioi_null
  null_gap := S.spectral_gap_null

end SrcTwoLevelSequence

/-- **`pmix:rigidity`(b), Clark vague limit**: for any `SrcTwoLevelSequence C A₁` with
`A₁ < A_opt`, the normalised spectral measures converge vaguely to `clarkMeasure α`,
`α = clarkAngle (-A₁ / c_*)`. -/
theorem src_theorem_two_six (C : CommonSource) {A₁ : ℝ} (hA : A₁ < Aopt)
    (S : SrcTwoLevelSequence C A₁) :
    IsVagueLimit atTop S.μ (clarkMeasure (clarkAngle (-A₁ / cStar))) := by
  have hu₁ := mem_gap_one_of_lt_Aopt hA
  have hα : Real.sin (clarkAngle (-A₁ / cStar)) ≠ 0 := sin_clarkAngle_ne_zero hu₁
  have hP : DesignPropertyP S.μ twoZeroClass := src_designPropertyP_twoZero C S.toCrossingSequence
  set T := S.twoLevelSupport hA
  have hz1 : clarkNode (clarkAngle (-A₁ / cStar)) 2 < clarkNode (clarkAngle (-A₁ / cStar)) 1 :=
    clarkNode_lt_of_lt le_rfl (by norm_num) _
  have hz2 : clarkNode (clarkAngle (-A₁ / cStar)) 2 < 0 := clarkNode_two_lt_zero _
  have hbd : LocallyBounded S.μ := locallyBounded_of_support hz1 hz2 T hP
  intro g hg hcs
  rw [Filter.tendsto_iff_ultrafilter]
  intro 𝒰 h𝒰
  obtain ⟨ν, hlf, hν⟩ := exists_vagueLimit S.μ hbd 𝒰 h𝒰
  have hae := T.ae_vagueLimit h𝒰 hν
  have hB := T.ae_le_eventually (show (0 : ℝ) < 1 by norm_num)
  have hI : ∀ δ : IdealDatum, δ.Adm →
      IdealIneq ν (clarkNode (clarkAngle (-A₁ / cStar)) 1 + 1) δ.win δ.q (∫ u, δ.win u) :=
    fun δ hδ => idealIneq_of_approx hbd h𝒰 hν hP hB (twoZeroIdealApprox δ hδ).some
  have := measure_eq_clarkMeasure hα hae hI
  rw [← this]
  exact hν g hg hcs

/-- **`pmix:rigidity`(b), atom weight recovery**: the normalised weight at `u(t₁^{(j)})`
converges to `1 / K(z₁, z₁)`. -/
theorem src_tendsto_atom_weight (C : CommonSource) {A₁ : ℝ} (hA : A₁ < Aopt)
    (S : SrcTwoLevelSequence C A₁) :
    Tendsto (fun j => (S.μ j {uAiry (S.c j) (S.t₁ j)}).toReal) atTop
      (𝓝 (clarkKernel (clarkAngle (-A₁ / cStar)) 1)⁻¹) := by
  let α := clarkAngle (-A₁ / cStar)
  have hvl := src_theorem_two_six C hA S
  let T := S.twoLevelSupport hA
  have hz1 : clarkNode α 2 < clarkNode α 1 := clarkNode_lt_of_lt le_rfl (by norm_num) _
  let ε : ℝ := (clarkNode α 1 - clarkNode α 2) / 2
  have hε0 : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨g, hgK, hgU, hgcs, _⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_Icc : IsCompact (Icc (clarkNode α 1 - ε / 2) (clarkNode α 1 + ε / 2)))
    (isOpen_Ioo : IsOpen (Ioo (clarkNode α 1 - ε) (clarkNode α 1 + ε))).isClosed_compl
    (disjoint_compl_right_iff_subset.mpr fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hlim := hvl g g.continuous hgcs
  have hν : ∫ u, g u ∂(clarkMeasure α) = (clarkKernel α 1)⁻¹ := by
    rw [node_integral_eq_tsum_atoms (cNode_injective α) (clarkMeasure_compl_range α) g.continuous hgcs,
      tsum_eq_single 0]
    · rw [clarkMeasure_singleton, ENNReal.toReal_ofReal (cWeight_pos α 0).le]
      have h1 : g (cNode α 0) = 1 := hgK ⟨by show _ ≤ clarkNode α 1; linarith, by show clarkNode α 1 ≤ _; linarith⟩
      rw [h1, one_mul]; rfl
    · intro i hi
      have hle : cNode α i ≤ clarkNode α 2 := by
        have := (cNode_strictAnti α).antitone (show 1 ≤ i by omega)
        simpa [cNode] using this
      have : g (cNode α i) = 0 := hgU (fun hmem => by
        dsimp [ε] at hmem; linarith [hmem.1, hle])
      rw [this, zero_mul]
  rw [hν] at hlim
  refine hlim.congr' ?_
  have e1 := T.s₂_le ε hε0
  have e2 : ∀ᶠ j in atTop, T.s₁ j ∈ Icc (clarkNode α 1 - ε / 2) (clarkNode α 1 + ε / 2) :=
    T.tendsto_s₁.eventually (Icc_mem_nhds (by linarith) (by linarith))
  filter_upwards [e1, e2] with j h1 h2
  have hae : ∀ᵐ u ∂(S.μ j), g u = Set.indicator {T.s₁ j} (fun _ => (1 : ℝ)) u := by
    filter_upwards [ae_le_of_supp (T.null_top j), measure_eq_zero_iff_ae_notMem.1 (T.null_gap j)]
      with u hu1 hu2
    by_cases hh : u ≤ T.s₂ j
    · rw [hgU (fun hmem => by
        dsimp [α, ε] at h1 hmem; linarith [hmem.1])]
      have hne : u ∉ ({T.s₁ j} : Set ℝ) := fun hu => by
        rw [mem_singleton_iff] at hu; subst hu
        dsimp [α, ε] at h1 h2; linarith [h2.1]
      simp [hne]
    · push Not at hh
      have : T.s₁ j ≤ u := by
        by_contra hcon
        exact hu2 ⟨hh, not_le.1 hcon⟩
      have hu : u = T.s₁ j := le_antisymm hu1 this
      subst hu
      rw [hgK h2]; simp
  rw [integral_congr_ae hae, integral_indicator_const _ (measurableSet_singleton _)]
  simp only [Measure.real, smul_eq_mul, mul_one]
  rfl

/-- **`pmix:rigidity`(b), constrained primal attainment at a prescribed first level `t₁ > 0`**:
for any `12 C.a₀ ≤ c̃`, there is a maximal threshold `B = constrainedThresholdS C.src c̃ {t₁} ≥ T_V(c̃)`
attained by a crossing measure on `{t₁} ∪ [B, ∞)`, and every `τ ∈ (0, B)` admits a crossing
measure on `{t₁} ∪ [τ, ∞)`. -/
theorem src_two_level_constrained_attainment (C : CommonSource) {cTilde t₁ : ℝ}
    (hc : 12 * C.a₀ ≤ cTilde) (ht₁ : 0 < t₁) :
    let B := constrainedThresholdS C.src cTilde {t₁}
    C.src.T_V cTilde ≤ B ∧ 0 < B ∧
      (∃ meas : SourceCrossingMeasure C.src (cTilde / 12), meas.ν ({t₁} ∪ Ici B)ᶜ = 0) ∧
      ∀ τ : ℝ, 0 < τ → τ < B →
        ∃ meas : SourceCrossingMeasure C.src (cTilde / 12), meas.ν ({t₁} ∪ Ici τ)ᶜ = 0 := by
  have h := (pmix_duality_common C hc).some.duality_E_b isCompact_singleton
    (singleton_subset_iff.2 ht₁)
  exact ⟨h.1.1, h.2.1.1, h.2.1.2, h.2.2.2⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.src_designPropertyP_twoZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms src_designPropertyP_twoZero

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.src_two_level_exclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms src_two_level_exclusion

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.src_theorem_two_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms src_theorem_two_six

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.src_tendsto_atom_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms src_tendsto_atom_weight

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.src_two_level_constrained_attainment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms src_two_level_constrained_attainment

end FormalResearch.ModularBootstrap.Mixtures
