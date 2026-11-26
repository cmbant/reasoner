module

public import FormalResearch.ModularBootstrap.Duality.ThermalSeparation
public import FormalResearch.ModularBootstrap.Duality.VagueDomination

/-!
# Reserve separation (Theorem E(c), `ds:E`(c), `dual_spectrum.tex`)

Fix a fixed weight `(w, Q)`, `DualSetupCore prob cTilde β₀ T₀`, a closed `X ⊆ [T₀, ∞)` and a
positive measure `σ` on `ℝ`, finite on compacts, carried by `X`, with `h ∈ L¹(σ)` (`h` the dual
majorant of `ds:M`).  Write a *span test* for `g = Σ_{β∈B} l_β Ξ_β + μ h` with `μ ≥ 0`
(`g ∈ span{Ξ_β} + ℝ_{≥0} h`).

* `exists_crossing_dominating` (the separation step): if `r ≥ 0`, `r ∫ h dσ < C₀` and every span
  test `g ≥ 0` on `X` obeys `r ∫ g dσ ≤ -g_vac`, then there is a crossing measure `ν` carried by
  `X` with `r σ ≤ ν`, `w_* ∈ L¹(ν)`, `∫ w_* dν ≤ C₀`.
* `theorem_E_c_separation`: the case `r = 1` (the first assertion of `ds:E`(c)).
* `theorem_E_c_reserve`: if `X` carries a crossing measure and `0 < ∫ h dσ`, the largest `r` such
  that a crossing measure on `X` dominates `r σ` exists (`IsGreatest`) and equals
  `R_X(σ) = inf {-g_vac / ∫ g dσ}` over span tests `g ≥ 0` on `X` with `∫ g dσ > 0`
  (`ds:reserve-max`); moreover `R_X(σ) ≤ C₀ / ∫ h dσ`.
* `theorem_E_c_reserve_testClass`: if `X` contains a terminal ray, `R_X(σ)` is the same infimum
  over all `g ∈ Ā_w` nonnegative on `X` (denominator `∫⁻ g dσ ∈ (0, ∞]`; an infinite denominator
  gives ratio `0`).

Compared with the paper: the hypothesis `∫_X e^{-2πβt} dσ < ∞` is not assumed, because it follows
from `h ∈ L¹(σ)` (`exp_le_const_wStar`, `w_* ≤ h`), and `h ∈ L¹(σ)` is the content of
`∫ h dσ < ∞`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality

section Integrability

variable {prob : FixedWeightProblem} {cTilde β₀ T₀ : ℝ} {X : Set ℝ} {σ : Measure ℝ}

lemma ae_mem_of_null (hσ : σ Xᶜ = 0) : ∀ᵐ y ∂σ, y ∈ X := by
  have : ∀ᵐ y ∂σ, y ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 hσ
  filter_upwards [this] with y hy using by simpa using hy

/-- `w̃ ∈ L¹(σ)` when `h ∈ L¹(σ)` and `σ` is carried by `X ⊆ [T₀, ∞)` (`w_* ≤ h` there). -/
lemma integrable_wTilde_of_h (S : DualSetupCore prob cTilde β₀ T₀) (hX : X ⊆ Ici T₀)
    (hσ : σ Xᶜ = 0) (hh : Integrable (hMaj prob.w (cTilde / 12) β₀) σ) :
    Integrable (wTilde (cTilde / 12) β₀ T₀) σ := by
  refine hh.mono' (measurable_wTilde _ _ _).aestronglyMeasurable ?_
  filter_upwards [ae_mem_of_null hσ] with y hy
  have hy0 := hX hy
  rw [Real.norm_eq_abs, abs_of_pos (wTilde_pos S.ha_pos S.hβ₀ S.hT₀pos y), wTilde_of_le hy0]
  exact wStar_le_hMaj prob.hw S.ha_pos S.hβ₀ (by linarith [S.hβ₀2]) S.hT₀ hy0

/-- `f̃_β ∈ L¹(σ)` for every `β > 0`, when `h ∈ L¹(σ)` (`Ξ_β = o(w_*)` and `w_* ≤ h`). -/
lemma integrable_fTilde_of_h (S : DualSetupCore prob cTilde β₀ T₀) (hX : X ⊆ Ici T₀)
    (hσ : σ Xᶜ = 0) [IsFiniteMeasureOnCompacts σ]
    (hh : Integrable (hMaj prob.w (cTilde / 12) β₀) σ) {β : ℝ} (hβ : 0 < β) :
    Integrable (fTilde prob.w T₀ β) σ := by
  have hw := integrable_wTilde_of_h S hX hσ hh
  obtain ⟨K, hK, hKd⟩ := fTilde_decay (w := prob.w) S.ha_pos S.hβ₀ S.hT₀pos hβ hX 1 one_pos
  have hf := continuous_fTilde prob.w T₀ β
  have h1 : IntegrableOn (fTilde prob.w T₀ β) K σ := hf.continuousOn.integrableOn_compact hK
  have h2 : IntegrableOn (fTilde prob.w T₀ β) Kᶜ σ := by
    refine Integrable.mono' (hw.mono_measure Measure.restrict_le_self)
      hf.aestronglyMeasurable ?_
    rw [ae_restrict_iff' hK.isClosed.measurableSet.compl]
    filter_upwards [ae_mem_of_null hσ] with y hy hyK
    have := hKd y hy hyK
    rw [Real.norm_eq_abs]
    linarith
  have := h1.union h2
  rwa [union_compl_self, integrableOn_univ] at this

lemma integrable_thermalDiff_of_h (S : DualSetupCore prob cTilde β₀ T₀) (hX : X ⊆ Ici T₀)
    (hσ : σ Xᶜ = 0) [IsFiniteMeasureOnCompacts σ]
    (hh : Integrable (hMaj prob.w (cTilde / 12) β₀) σ) {β : ℝ} (hβ : 0 < β) :
    Integrable (thermalDiff prob.w β) σ := by
  refine (integrable_fTilde_of_h S hX hσ hh hβ).congr ?_
  filter_upwards [ae_mem_of_null hσ] with y hy using fTilde_of_le (hX hy)

/-- The integral of a span test against `σ`. -/
lemma integral_spanTest (S : DualSetupCore prob cTilde β₀ T₀) (hX : X ⊆ Ici T₀)
    (hσ : σ Xᶜ = 0) [IsFiniteMeasureOnCompacts σ]
    (hh : Integrable (hMaj prob.w (cTilde / 12) β₀) σ) {B : Finset ℝ} (hB : ∀ β ∈ B, 0 < β)
    (l : ℝ → ℝ) (μ : ℝ) :
    Integrable (spanTest prob.w (cTilde / 12) β₀ B l μ) σ ∧
    ∫ t, spanTest prob.w (cTilde / 12) β₀ B l μ t ∂σ =
      ∑ β ∈ B, l β * ∫ t, thermalDiff prob.w β t ∂σ + μ * ∫ t, hMaj prob.w (cTilde / 12) β₀ t ∂σ := by
  have hXi : ∀ β ∈ B, Integrable (fun t => l β * thermalDiff prob.w β t) σ := fun β hβ =>
    (integrable_thermalDiff_of_h S hX hσ hh (hB β hβ)).const_mul _
  have hsum : Integrable (fun t => ∑ β ∈ B, l β * thermalDiff prob.w β t) σ :=
    integrable_finsetSum _ hXi
  refine ⟨hsum.add (hh.const_mul μ), ?_⟩
  unfold spanTest
  rw [integral_add hsum (hh.const_mul μ), integral_finsetSum _ hXi, integral_const_mul]
  congr 1
  exact Finset.sum_congr rfl fun β _ => integral_const_mul _ _

end Integrability

section Separation

variable {prob : FixedWeightProblem} {cTilde β₀ T₀ : ℝ} {X : Set ℝ} {σ : Measure ℝ}

/-- **Reserve separation** (`ds:E`(c), the separation step): for `r ≥ 0` with `r ∫ h dσ < C₀`,
if `r ∫ g dσ ≤ -g_vac` for every span test `g = Σ l_β Ξ_β + μ h` (`μ ≥ 0`) nonnegative on `X`, then
there is a crossing measure `ν` carried by `X` with `r σ ≤ ν`, `w_* ∈ L¹(ν)`, `∫ w_* dν ≤ C₀`. -/
theorem exists_crossing_dominating (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ}
    (hXc : IsClosed X) (hX : X ⊆ Ici T₀) {σ : Measure ℝ} [IsFiniteMeasureOnCompacts σ]
    (hσ : σ Xᶜ = 0) (hh : Integrable (hMaj prob.w (cTilde / 12) β₀) σ) {r : ℝ} (hr : 0 ≤ r)
    (hbud : r * ∫ t, hMaj prob.w (cTilde / 12) β₀ t ∂σ < dualC0 prob (cTilde / 12) β₀)
    (hH : ∀ (B : Finset ℝ) (_ : ∀ β ∈ B, 0 < β) (l : ℝ → ℝ) (μ : ℝ), 0 ≤ μ →
      (∀ t ∈ X, 0 ≤ spanTest prob.w (cTilde / 12) β₀ B l μ t) →
      r * ∫ t, spanTest prob.w (cTilde / 12) β₀ B l μ t ∂σ ≤
        -prob.gVac (cTilde / 12) (spanTest prob.w (cTilde / 12) β₀ B l μ)) :
    ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12), meas.ν Xᶜ = 0 ∧
      ENNReal.ofReal r • σ ≤ meas.ν ∧ Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  classical
  have ha0 := S.ha_pos
  have hC₀ : 0 < dualC0 prob (cTilde / 12) β₀ := dualC0_pos prob ha0 S.hβ₀ (by linarith [S.hβ₀2])
  set C₀ := dualC0 prob (cTilde / 12) β₀ with hC₀def
  set H := ∫ t, hMaj prob.w (cTilde / 12) β₀ t ∂σ with hHdef
  have hC₀' : 0 < C₀ - r * H := by linarith
  have hfint := fun β (hβ : 0 < β) => integrable_fTilde_of_h S hX hσ hh hβ
  have hfeq : ∀ β : ℝ, 0 < β → ∫ t, fTilde prob.w T₀ β t ∂σ = ∫ t, thermalDiff prob.w β t ∂σ :=
    fun β _ => integral_congr_ae (by
      filter_upwards [ae_mem_of_null hσ] with y hy using fTilde_of_le (hX hy))
  obtain ⟨ν, hνf, hνsupp, hνbud, hνmom⟩ := farkas_separation (Y := ℝ)
    (I := {β : ℝ // 0 < β}) (w := wTilde (cTilde / 12) β₀ T₀) (X := fun _ => X)
    (continuous_wTilde ha0 S.hT₀pos) (wTilde_pos ha0 S.hβ₀ S.hT₀pos) hC₀' (fun _ => hXc)
    (fun _ _ _ => le_rfl)
    (f := fun i => fTilde prob.w T₀ i.1) (fun i => continuous_fTilde _ _ _)
    (fun i => fTilde_decay ha0 S.hβ₀ S.hT₀pos i.2 hX)
    (a := fun i => crossingRHS prob (cTilde / 12) i.1 - r * ∫ t, fTilde prob.w T₀ i.1 t ∂σ)
    (fun j u lam b hb hnn => by
      obtain ⟨B, hB, l, hsumB, hg⟩ := span_of_ratio prob S hX u lam b hb hnn
      have h1 := hH B hB l b hb hg
      obtain ⟨-, hint⟩ := integral_spanTest S hX hσ hh hB l b
      rw [hint, hsumB (fun β => ∫ t, thermalDiff prob.w β t ∂σ),
        gVac_spanTest prob S.ha ha0 hB l b, hsumB (fun β => crossingRHS prob (cTilde / 12) β)] at h1
      have e1 : ∑ i ∈ u, lam i * (crossingRHS prob (cTilde / 12) i.1 -
          r * ∫ t, fTilde prob.w T₀ i.1 t ∂σ) =
          ∑ i ∈ u, lam i * crossingRHS prob (cTilde / 12) i.1 -
            r * ∑ i ∈ u, lam i * ∫ t, thermalDiff prob.w i.1 t ∂σ := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hfeq i.1 i.2]; ring
      rw [e1]
      nlinarith [h1])
  simp only [iInter_const] at hνsupp
  -- the measure `ν̃ + r σ`
  have := hνf
  have hσr : IsFiniteMeasureOnCompacts (ENNReal.ofReal r • σ) :=
    IsFiniteMeasureOnCompacts.smul σ ENNReal.ofReal_ne_top
  have : IsFiniteMeasureOnCompacts (ν + ENNReal.ofReal r • σ) :=
    ⟨fun K hK => by
      rw [add_apply]; exact ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hσr.lt_top_of_isCompact hK⟩⟩
  have hwT := integrable_wTilde_of_h S hX hσ hh
  have hwTσ : ∫⁻ y, ENNReal.ofReal (wTilde (cTilde / 12) β₀ T₀ y) ∂σ =
      ENNReal.ofReal (∫ y, wTilde (cTilde / 12) β₀ T₀ y ∂σ) :=
    (ofReal_integral_eq_lintegral_ofReal hwT
      (Eventually.of_forall fun y => (wTilde_pos ha0 S.hβ₀ S.hT₀pos y).le)).symm
  have hs0 : 0 ≤ ∫ y, wTilde (cTilde / 12) β₀ T₀ y ∂σ :=
    integral_nonneg fun y => (wTilde_pos ha0 S.hβ₀ S.hT₀pos y).le
  have hsH : ∫ y, wTilde (cTilde / 12) β₀ T₀ y ∂σ ≤ H := by
    refine integral_mono_ae hwT hh ?_
    filter_upwards [ae_mem_of_null hσ] with y hy
    rw [wTilde_of_le (hX hy)]
    exact wStar_le_hMaj prob.hw ha0 S.hβ₀ (by linarith [S.hβ₀2]) S.hT₀ (hX hy)
  have hbud' : ∫⁻ y, ENNReal.ofReal (wTilde (cTilde / 12) β₀ T₀ y) ∂(ν + ENNReal.ofReal r • σ) ≤
      ENNReal.ofReal C₀ := by
    rw [lintegral_add_measure, lintegral_smul_measure, hwTσ]
    calc _ ≤ ENNReal.ofReal (C₀ - r * H) +
          ENNReal.ofReal r * ENNReal.ofReal (∫ y, wTilde (cTilde / 12) β₀ T₀ y ∂σ) :=
          add_le_add_left hνbud _
      _ = ENNReal.ofReal ((C₀ - r * H) + r * ∫ y, wTilde (cTilde / 12) β₀ T₀ y ∂σ) := by
          rw [ENNReal.ofReal_add hC₀'.le (mul_nonneg hr hs0), ENNReal.ofReal_mul hr]
      _ ≤ ENNReal.ofReal C₀ := ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_left hsH hr])
  have hsupp' : (ν + ENNReal.ofReal r • σ) Xᶜ = 0 := by
    rw [add_apply, smul_apply, hνsupp, hσ]; simp
  obtain ⟨meas, hmeas, hint, hle⟩ := exists_crossing_of_moments prob S (ν := ν + ENNReal.ofReal r • σ)
    hX hsupp' hbud' (fun β hβ => by
      have h1 := hνmom ⟨β, hβ⟩
      have h2 : Integrable (fTilde prob.w T₀ β) (ENNReal.ofReal r • σ) :=
        (hfint β hβ).smul_measure ENNReal.ofReal_ne_top
      rw [integral_add_measure h1.1 h2, h1.2, integral_smul_measure, ENNReal.toReal_ofReal hr,
        smul_eq_mul]
      ring)
  refine ⟨meas, hmeas ▸ hsupp', hmeas ▸ Measure.le_add_left le_rfl, hmeas ▸ hint, hmeas ▸ hle⟩

end Separation

section Reserve

variable {prob : FixedWeightProblem} {cTilde β₀ T₀ : ℝ}

/-- **Theorem E(c), first assertion** (`ds:E`(c)): if every span test `g ∈ span{Ξ_β} + ℝ_{≥0} h`
which is nonnegative on `X` obeys `-g_vac ≥ ∫ g dσ`, and `∫ h dσ < C₀`, then there is a crossing
measure `ν` carried by `X` with `ν ≥ σ`. -/
theorem theorem_E_c_separation (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ} (hXc : IsClosed X)
    (hX : X ⊆ Ici T₀) {σ : Measure ℝ} [IsFiniteMeasureOnCompacts σ] (hσ : σ Xᶜ = 0)
    (hh : Integrable (hMaj prob.w (cTilde / 12) β₀) σ)
    (hbud : ∫ t, hMaj prob.w (cTilde / 12) β₀ t ∂σ < dualC0 prob (cTilde / 12) β₀)
    (hH : ∀ (B : Finset ℝ) (_ : ∀ β ∈ B, 0 < β) (l : ℝ → ℝ) (μ : ℝ), 0 ≤ μ →
      (∀ t ∈ X, 0 ≤ spanTest prob.w (cTilde / 12) β₀ B l μ t) →
      ∫ t, spanTest prob.w (cTilde / 12) β₀ B l μ t ∂σ ≤
        -prob.gVac (cTilde / 12) (spanTest prob.w (cTilde / 12) β₀ B l μ)) :
    ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12), meas.ν Xᶜ = 0 ∧ σ ≤ meas.ν ∧
      Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  obtain ⟨meas, h1, h2, h3, h4⟩ := exists_crossing_dominating S hXc hX hσ hh (r := 1) zero_le_one
    (by simpa using hbud) (fun B hB l μ hμ hg => by simpa using hH B hB l μ hμ hg)
  exact ⟨meas, h1, by simpa using h2, h3, h4⟩

/-- The ratios `-g_vac / ∫ g dσ` of `ds:reserve-max`, over span tests `g ∈ span{Ξ_β} + ℝ_{≥0} h`
which are nonnegative on `X` and have `∫ g dσ > 0`. -/
def reserveRatios (prob : FixedWeightProblem) (cTilde β₀ : ℝ) (X : Set ℝ) (σ : Measure ℝ) :
    Set ℝ :=
  {x | ∃ (B : Finset ℝ) (l : ℝ → ℝ) (μ : ℝ), (∀ β ∈ B, 0 < β) ∧ 0 ≤ μ ∧
    (∀ t ∈ X, 0 ≤ spanTest prob.w (cTilde / 12) β₀ B l μ t) ∧
    0 < ∫ t, spanTest prob.w (cTilde / 12) β₀ B l μ t ∂σ ∧
    x = -prob.gVac (cTilde / 12) (spanTest prob.w (cTilde / 12) β₀ B l μ) /
      ∫ t, spanTest prob.w (cTilde / 12) β₀ B l μ t ∂σ}

/-- `R_X(σ)` of `ds:reserve-max`. -/
noncomputable def reserveMax (prob : FixedWeightProblem) (cTilde β₀ : ℝ) (X : Set ℝ)
    (σ : Measure ℝ) : ℝ :=
  sInf (reserveRatios prob cTilde β₀ X σ)

/-- A crossing measure `ν ≥ r σ` carried by `X` bounds `r` by every ratio. -/
lemma le_ratio_of_dominating (S : DualSetupCore prob cTilde β₀ T₀)
    (meas : AdmissibleCrossingMeasure prob (cTilde / 12)) {X : Set ℝ} (hν : meas.ν Xᶜ = 0)
    {σ : Measure ℝ} {r : ℝ} (hr : 0 ≤ r) (hdom : ENNReal.ofReal r • σ ≤ meas.ν)
    {B : Finset ℝ} (hB : ∀ β ∈ B, 0 < β) (l : ℝ → ℝ) (μ : ℝ)
    (hnn : ∀ t ∈ X, 0 ≤ spanTest prob.w (cTilde / 12) β₀ B l μ t) :
    r * ∫ t, spanTest prob.w (cTilde / 12) β₀ B l μ t ∂σ ≤
      -prob.gVac (cTilde / 12) (spanTest prob.w (cTilde / 12) β₀ B l μ) := by
  obtain ⟨hint, hval⟩ := crossing_pairing_span prob S.hc_pos S.hc S.hβ₀ S.hβ₀2 meas hB l μ
  rw [IntegrableOn, Duality.restrict_Ici_eq_self meas] at hint
  rw [Duality.restrict_Ici_eq_self meas] at hval
  have hae : 0 ≤ᵐ[meas.ν] spanTest prob.w (cTilde / 12) β₀ B l μ := by
    filter_upwards [ae_mem_of_null hν] with t ht using hnn t ht
  have h1 := integral_mono_measure hdom hae hint
  rw [integral_smul_measure, ENNReal.toReal_ofReal hr, smul_eq_mul] at h1
  rw [gVac_spanTest prob S.ha S.ha_pos hB l μ]
  linarith

/-- `h ≥ 0` on `X ⊆ [T₀, ∞)`. -/
lemma hMaj_nonneg_on (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ} (hX : X ⊆ Ici T₀) :
    ∀ t ∈ X, 0 ≤ hMaj prob.w (cTilde / 12) β₀ t := fun t ht =>
  (wStar_pos S.ha_pos.le S.hβ₀ (S.hT₀pos.le.trans (hX ht))).le.trans
    (wStar_le_hMaj prob.hw S.ha_pos S.hβ₀ (by linarith [S.hβ₀2]) S.hT₀ (hX ht))

/-- The test `h` itself has ratio `C₀ / ∫ h dσ`. -/
lemma hRatio_h (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ} (hX : X ⊆ Ici T₀)
    {σ : Measure ℝ} (hHpos : 0 < ∫ t, hMaj prob.w (cTilde / 12) β₀ t ∂σ) :
    dualC0 prob (cTilde / 12) β₀ / ∫ t, hMaj prob.w (cTilde / 12) β₀ t ∂σ ∈
      reserveRatios prob cTilde β₀ X σ := by
  have hspan_h : spanTest prob.w (cTilde / 12) β₀ (∅ : Finset ℝ) (fun _ => (0 : ℝ)) 1 =
      hMaj prob.w (cTilde / 12) β₀ := by
    funext t; simp [spanTest]
  refine ⟨∅, fun _ => 0, 1, fun β hβ => absurd hβ (Finset.notMem_empty β), zero_le_one,
    fun t ht => by rw [hspan_h]; exact hMaj_nonneg_on S hX t ht, by rw [hspan_h]; exact hHpos, ?_⟩
  rw [gVac_spanTest prob S.ha S.ha_pos (fun β hβ => absurd hβ (Finset.notMem_empty β)), hspan_h]
  simp

/-- **Theorem E(c), reserve formula** (`ds:reserve-max`, `dual_spectrum.tex`): let `X ⊆ [T₀, ∞)` be
closed and carry a crossing measure, and let `σ` be a positive measure, finite on compacts and
carried by `X`, with `h ∈ L¹(σ)` and `0 < ∫ h dσ`.  Then the largest `r ≥ 0` such that some crossing
measure on `X` dominates `r σ` exists (attained by a crossing measure), and equals
`R_X(σ) = inf {-g_vac / ∫ g dσ}` over span tests `g ≥ 0` on `X` with `∫ g dσ > 0`; moreover
`R_X(σ) ≤ C₀ / ∫ h dσ`. -/
theorem theorem_E_c_reserve (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ} (hXc : IsClosed X)
    (hX : X ⊆ Ici T₀) {σ : Measure ℝ} [IsFiniteMeasureOnCompacts σ] (hσ : σ Xᶜ = 0)
    (hh : Integrable (hMaj prob.w (cTilde / 12) β₀) σ)
    (hHpos : 0 < ∫ t, hMaj prob.w (cTilde / 12) β₀ t ∂σ)
    (hcross : ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12), meas.ν Xᶜ = 0) :
    IsGreatest {r : ℝ | 0 ≤ r ∧ ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν Xᶜ = 0 ∧ ENNReal.ofReal r • σ ≤ meas.ν} (reserveMax prob cTilde β₀ X σ) ∧
      reserveMax prob cTilde β₀ X σ ≤
        dualC0 prob (cTilde / 12) β₀ / ∫ t, hMaj prob.w (cTilde / 12) β₀ t ∂σ := by
  classical
  have ha0 := S.ha_pos
  have hC₀ : 0 < dualC0 prob (cTilde / 12) β₀ := dualC0_pos prob ha0 S.hβ₀ (by linarith [S.hβ₀2])
  set C₀ := dualC0 prob (cTilde / 12) β₀ with hC₀def
  set H := ∫ t, hMaj prob.w (cTilde / 12) β₀ t ∂σ with hHdef
  obtain ⟨meas0, hν0⟩ := hcross
  set R := reserveMax prob cTilde β₀ X σ with hRdef
  have hh_nn := hMaj_nonneg_on S hX
  have hxh := hRatio_h S hX hHpos
  have hne : (reserveRatios prob cTilde β₀ X σ).Nonempty := ⟨_, hxh⟩
  have hnn_ratio : ∀ x ∈ reserveRatios prob cTilde β₀ X σ, 0 ≤ x := by
    rintro x ⟨B, l, μ, hB, hμ, hg, hpos, rfl⟩
    exact div_nonneg (neg_nonneg.2 (noSpanFeasible_of_crossingMeasure prob S.hc_pos S.hc S.hβ₀
      S.hβ₀2 meas0 hν0 B hB l μ hg)) hpos.le
  have hbdd : BddBelow (reserveRatios prob cTilde β₀ X σ) := ⟨0, hnn_ratio⟩
  have hR0 : 0 ≤ R := le_csInf hne hnn_ratio
  have hRle : R ≤ C₀ / H := csInf_le hbdd hxh
  refine ⟨⟨⟨hR0, ?_⟩, ?_⟩, hRle⟩
  · -- attainment
    have hRH : R * H ≤ C₀ := by
      have := mul_le_mul_of_nonneg_right hRle hHpos.le
      rwa [div_mul_cancel₀ _ hHpos.ne'] at this
    let r : ℕ → ℝ := fun n => R - R / ((n : ℝ) + 1)
    have hr_le : ∀ n, r n ≤ R := fun n => by
      have : 0 ≤ R / ((n : ℝ) + 1) := div_nonneg hR0 (by positivity)
      show R - R / ((n : ℝ) + 1) ≤ R; linarith
    have hr_nn : ∀ n, 0 ≤ r n := fun n => by
      have h1 : R / ((n : ℝ) + 1) ≤ R := div_le_self hR0 (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      show 0 ≤ R - R / ((n : ℝ) + 1); linarith
    have hr_bud : ∀ n, r n * H < C₀ := fun n => by
      have h1 : r n * H ≤ R * H := mul_le_mul_of_nonneg_right (hr_le n) hHpos.le
      rcases hR0.eq_or_lt with h0 | h0
      · have : r n = 0 := le_antisymm (h0 ▸ hr_le n) (hr_nn n)
        rw [this]; linarith
      · have hn : 0 < R / ((n : ℝ) + 1) := div_pos h0 (by positivity)
        have : r n < R := by show R - R / ((n : ℝ) + 1) < R; linarith
        nlinarith [mul_lt_mul_of_pos_right this hHpos]
    have hsep : ∀ n, ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12), meas.ν Xᶜ = 0 ∧
        ENNReal.ofReal (r n) • σ ≤ meas.ν := fun n => by
      obtain ⟨meas, h1, h2, -⟩ := exists_crossing_dominating S hXc hX hσ hh (hr_nn n) (hr_bud n)
        (fun B hB l μ hμ hg => by
          have hI := (integral_spanTest S hX hσ hh hB l μ).1
          have h0 : 0 ≤ ∫ t, spanTest prob.w (cTilde / 12) β₀ B l μ t ∂σ :=
            integral_nonneg_of_ae (by
              filter_upwards [ae_mem_of_null hσ] with t ht using hg t ht)
          rcases h0.eq_or_lt with hz | hpos
          · rw [← hz, mul_zero]
            exact neg_nonneg.2 (noSpanFeasible_of_crossingMeasure prob S.hc_pos S.hc S.hβ₀ S.hβ₀2
              meas0 hν0 B hB l μ hg)
          · have hmem : -prob.gVac (cTilde / 12) (spanTest prob.w (cTilde / 12) β₀ B l μ) /
                ∫ t, spanTest prob.w (cTilde / 12) β₀ B l μ t ∂σ ∈
                reserveRatios prob cTilde β₀ X σ := ⟨B, l, μ, hB, hμ, hg, hpos, rfl⟩
            have h1 : R ≤ -prob.gVac (cTilde / 12) (spanTest prob.w (cTilde / 12) β₀ B l μ) /
                ∫ t, spanTest prob.w (cTilde / 12) β₀ B l μ t ∂σ := csInf_le hbdd hmem
            rw [le_div_iff₀ hpos] at h1
            nlinarith [mul_le_mul_of_nonneg_right (hr_le n) hpos.le])
      exact ⟨meas, h1, h2⟩
    choose meas hmsupp hmdom using hsep
    let 𝒰 : Ultrafilter ℕ := Ultrafilter.of atTop
    have h𝒰 : (𝒰 : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
    obtain ⟨meas', hlim, hsupp', -, -⟩ := theorem_E_a_compactness prob S (X := fun _ => X)
      (fun _ => hXc) (fun _ _ _ => le_rfl) hX meas hmsupp 𝒰 h𝒰
    simp only [iInter_const] at hsupp'
    have : ∀ j, IsFiniteMeasureOnCompacts (meas j).ν := fun j => (meas j).isFiniteMeasureOnCompacts
    have := meas'.isFiniteMeasureOnCompacts
    have hrt : Tendsto r atTop (𝓝 R) := by
      have h1 : Tendsto (fun n : ℕ => R / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv, mul_comm] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul R
      simpa using (tendsto_const_nhds (x := R)).sub h1
    exact ⟨meas', hsupp', hlim.smul_le (hrt.mono_left h𝒰) hr_nn hmdom⟩
  · -- maximality
    rintro r ⟨hr, meas, hν, hdom⟩
    refine le_csInf hne ?_
    rintro x ⟨B, l, μ, hB, hμ, hg, hpos, rfl⟩
    rw [le_div_iff₀ hpos]
    exact le_ratio_of_dominating S meas hν hr hdom hB l μ hg

/-- **Theorem E(c), reserve formula over the whole test class** (`ds:reserve-max`, last
sentence): if `X` contains a terminal ray, `R_X(σ)` is also the infimum of
`-g_vac / ∫ g dσ` over all `g ∈ Ā_w` nonnegative on `X` with `∫ g dσ > 0`; the integral is the
`[0, ∞]`-valued `∫⁻ g dσ`, and an infinite denominator gives ratio `0`. -/
theorem theorem_E_c_reserve_testClass (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ}
    (hXc : IsClosed X) (hX : X ⊆ Ici T₀) (hray : ∃ τ, Ici τ ⊆ X) {σ : Measure ℝ}
    [IsFiniteMeasureOnCompacts σ] (hσ : σ Xᶜ = 0)
    (hh : Integrable (hMaj prob.w (cTilde / 12) β₀) σ)
    (hHpos : 0 < ∫ t, hMaj prob.w (cTilde / 12) β₀ t ∂σ)
    (hcross : ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12), meas.ν Xᶜ = 0) :
    ENNReal.ofReal (reserveMax prob cTilde β₀ X σ) =
      ⨅ (g : ℝ → ℝ) (_ : TestClass prob (cTilde / 12) g) (_ : ∀ t ∈ X, 0 ≤ g t)
        (_ : 0 < ∫⁻ t, ENNReal.ofReal (g t) ∂σ),
        ENNReal.ofReal (-prob.gVac (cTilde / 12) g) / ∫⁻ t, ENNReal.ofReal (g t) ∂σ := by
  classical
  obtain ⟨⟨⟨hR0, meas, hν, hdom⟩, -⟩, -⟩ := theorem_E_c_reserve S hXc hX hσ hh hHpos hcross
  obtain ⟨τ, hτ⟩ := hray
  set R := reserveMax prob cTilde β₀ X σ with hRdef
  obtain ⟨meas0, hν0⟩ := hcross
  have hne : (reserveRatios prob cTilde β₀ X σ).Nonempty := ⟨_, hRatio_h S hX hHpos⟩
  apply le_antisymm
  · refine le_iInf fun g => le_iInf fun hg => le_iInf fun hnn => le_iInf fun hL => ?_
    obtain ⟨hint, hle⟩ := lemma_fwX_one_sided_unconditional prob S.ha S.ha_pos meas hg
      (T := τ) (fun t ht => hnn t (hτ ht))
    rw [IntegrableOn, Duality.restrict_Ici_eq_self meas] at hint
    rw [Duality.restrict_Ici_eq_self meas] at hle
    have hae : ∀ᵐ t ∂meas.ν, 0 ≤ g t := by
      filter_upwards [ae_mem_of_null hν] with t ht using hnn t ht
    have h1 : ENNReal.ofReal (∫ t, g t ∂meas.ν) = ∫⁻ t, ENNReal.ofReal (g t) ∂meas.ν :=
      ofReal_integral_eq_lintegral_ofReal hint hae
    set L := ∫⁻ t, ENNReal.ofReal (g t) ∂σ with hLdef
    have h2 : ENNReal.ofReal R * L ≤ ENNReal.ofReal (-prob.gVac (cTilde / 12) g) := by
      calc ENNReal.ofReal R * L = ∫⁻ t, ENNReal.ofReal (g t) ∂(ENNReal.ofReal R • σ) := by
            rw [lintegral_smul_measure, smul_eq_mul]
        _ ≤ ∫⁻ t, ENNReal.ofReal (g t) ∂meas.ν := lintegral_mono' hdom le_rfl
        _ = ENNReal.ofReal (∫ t, g t ∂meas.ν) := h1.symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
    by_cases hLtop : L = ⊤
    · have : ENNReal.ofReal R = 0 := by
        by_contra hne0
        rw [hLtop, ENNReal.mul_top hne0] at h2
        exact absurd (top_le_iff.1 h2) ENNReal.ofReal_ne_top
      rw [this]; exact zero_le
    · exact (ENNReal.le_div_iff_mul_le (Or.inl hL.ne') (Or.inl hLtop)).2 h2
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hlt : R < R + ε := by simpa using hε
    obtain ⟨x, hx, hxlt⟩ := exists_lt_of_csInf_lt hne hlt
    obtain ⟨B, l, μ, hB, hμ, hg, hpos, rfl⟩ := hx
    have hI := (integral_spanTest S hX hσ hh hB l μ).1
    have hL : ∫⁻ t, ENNReal.ofReal (spanTest prob.w (cTilde / 12) β₀ B l μ t) ∂σ =
        ENNReal.ofReal (∫ t, spanTest prob.w (cTilde / 12) β₀ B l μ t ∂σ) :=
      (ofReal_integral_eq_lintegral_ofReal hI (by
        filter_upwards [ae_mem_of_null hσ] with t ht using hg t ht)).symm
    have hLpos : 0 < ∫⁻ t, ENNReal.ofReal (spanTest prob.w (cTilde / 12) β₀ B l μ t) ∂σ := by
      rw [hL]; exact ENNReal.ofReal_pos.2 hpos
    refine le_trans (iInf_le _ (spanTest prob.w (cTilde / 12) β₀ B l μ))
      (le_trans (iInf_le _ (spanTest_mem prob S.ha S.ha_pos hB l μ))
        (le_trans (iInf_le _ hg) (le_trans (iInf_le _ hLpos) ?_)))
    rw [hL, ← ENNReal.ofReal_div_of_pos hpos]
    calc _ ≤ ENNReal.ofReal (R + ε) := ENNReal.ofReal_le_ofReal hxlt.le
      _ = ENNReal.ofReal R + ε := by
          rw [ENNReal.ofReal_add hR0 (NNReal.coe_nonneg ε), ENNReal.ofReal_coe_nnreal]

end Reserve

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.exists_crossing_dominating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.exists_crossing_dominating

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.theorem_E_c_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.theorem_E_c_separation

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.theorem_E_c_reserve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.theorem_E_c_reserve

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.theorem_E_c_reserve_testClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.theorem_E_c_reserve_testClass

end FormalResearch.ModularBootstrap.FixedWeight
