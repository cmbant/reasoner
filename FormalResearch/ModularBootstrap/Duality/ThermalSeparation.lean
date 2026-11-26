module

public import FormalResearch.ModularBootstrap.Duality.SpanTests
public import FormalResearch.ModularBootstrap.Duality.PositiveExtension
public import FormalResearch.ModularBootstrap.TwoLevel.ConstrainedDuality

/-!
# Thermal separation (Theorem E(a), `ds:E`(a), `dual_spectrum.tex`)

For every fixed weight `(w, Q)` (`prob : FixedWeightProblem`), `c̃ > 0`, `c̃ ≥ 12 S`, and
`DualSetupCore prob cTilde β₀ T₀` (`β₀ ∈ (0, 1/2]`, `t₀^*(w, β₀) ≤ T₀ > 0`), and any closed
`X ⊆ [T₀, ∞)`:

* `theorem_E_a`: (i) there is a positive crossing measure carried by `X` iff (ii) no test
  `g = Σ l_β Ξ_β + μ h` of `span{Ξ_β, h}` which is nonnegative on `X` has `g_vac > 0`
  (`NoSpanFeasible`); every crossing measure on `X` has `∫ w_* dν ≤ C₀`; and if `X` contains a
  terminal ray these are equivalent to the absence of a strictly feasible `g ∈ Ā_w` on `X`.
* `theorem_E_a_finite`: under (ii), for every finite `B ⊂ (0, ∞)` there is a positive measure on
  `X` with at most `|B| + 1` atoms, `∫ w_* dν ≤ C₀` and `∫ Ξ_β dν = a_β` for `β ∈ B`.
* `theorem_E_a_decreasing`: if (ii) holds on closed `X_0 ⊇ X_1 ⊇ ⋯ ⊆ [T₀, ∞)`, there is a crossing
  measure on `⋂ X_j` (with `∫ w_* dν ≤ C₀`).
* `theorem_E_a_compactness`: crossing measures `ν_j` on `X_j` have a vague limit (along every
  ultrafilter `≤ atTop`; the paper says "subsequence") which is a crossing measure on `⋂ X_j` with
  the budget.

The proofs use the generic positive-extension lemma `Duality.farkas_separation` (`ds:farkas`)
with `Y = ℝ`, constraints `Ξ_β` (`β > 0`), weight `w_*`, and the harmless modification
`w̃(t) = w_*(max t T₀)`, `f̃_β(t) = Ξ_β(max t T₀)` which makes everything continuous on `ℝ` and
agrees with `w_*`, `Ξ_β` on `[T₀, ∞)` where all the measures live.  They replace the `[0,1]`
compactification of `Duality/Compactness` and `FixedWeight/StrongDuality`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality

/-! ### The modified data on `ℝ` -/

/-- `w̃(t) = w_*(max t T₀)`. -/
noncomputable def wTilde (a β₀ T₀ t : ℝ) : ℝ := wStar a β₀ (max t T₀)

/-- `f̃_β(t) = Ξ_β(max t T₀)`. -/
noncomputable def fTilde (w : ℕ) (T₀ β t : ℝ) : ℝ := thermalDiff w β (max t T₀)

lemma wTilde_of_le {a β₀ T₀ t : ℝ} (ht : T₀ ≤ t) : wTilde a β₀ T₀ t = wStar a β₀ t := by
  unfold wTilde; rw [max_eq_left ht]

lemma fTilde_of_le {w : ℕ} {T₀ β t : ℝ} (ht : T₀ ≤ t) : fTilde w T₀ β t = thermalDiff w β t := by
  unfold fTilde; rw [max_eq_left ht]

lemma continuous_wTilde {a β₀ T₀ : ℝ} (ha : 0 < a) (hT₀ : 0 < T₀) :
    Continuous (wTilde a β₀ T₀) := by
  unfold wTilde
  exact (continuousOn_wStar ha).comp_continuous (continuous_id.max continuous_const)
    fun y => (hT₀.le.trans (le_max_right y T₀) : (0 : ℝ) ≤ max y T₀)

lemma wTilde_pos {a β₀ T₀ : ℝ} (ha : 0 < a) (hβ₀ : 0 < β₀) (hT₀ : 0 < T₀) (t : ℝ) :
    0 < wTilde a β₀ T₀ t :=
  wStar_pos ha.le hβ₀ (hT₀.le.trans (le_max_right t T₀))

lemma continuous_fTilde (w : ℕ) (T₀ β : ℝ) : Continuous (fTilde w T₀ β) := by
  unfold fTilde thermalDiff; fun_prop

lemma measurable_wTilde (a β₀ T₀ : ℝ) : Measurable (wTilde a β₀ T₀) :=
  (measurable_wStar a β₀).comp (measurable_id.max measurable_const)

/-- The decay hypothesis of `ds:farkas`: `|f̃_β| ≤ ε w̃` on `[T₀, ∞)` outside a compact set. -/
lemma fTilde_decay {w : ℕ} {a β₀ T₀ β : ℝ} (ha : 0 < a) (hβ₀ : 0 < β₀) (hT₀ : 0 < T₀)
    (hβ : 0 < β) {X : Set ℝ} (hX : X ⊆ Ici T₀) :
    ∀ ε > 0, ∃ K : Set ℝ, IsCompact K ∧ ∀ y ∈ X, y ∉ K → |fTilde w T₀ β y| ≤ ε * wTilde a β₀ T₀ y := by
  intro ε hε
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.1 (tendsto_thermalDiff_div_wStar (w := w) (a := a) ha.le hβ₀ hβ) ε hε
  refine ⟨Icc T₀ (max R T₀), isCompact_Icc, fun y hy hyK => ?_⟩
  have hyT : T₀ ≤ y := hX hy
  have hyR : R ≤ y := by
    by_contra h
    exact hyK ⟨hyT, ((not_le.1 h).le.trans (le_max_left R T₀))⟩
  have h1 := hR y hyR
  rw [Real.dist_eq, sub_zero] at h1
  rw [fTilde_of_le hyT, wTilde_of_le hyT]
  have hw := wStar_pos ha.le hβ₀ (hT₀.le.trans hyT)
  rw [abs_div, abs_of_pos hw, div_lt_iff₀ hw] at h1
  linarith

/-! ### Crossing measures from moments -/

/-- **Crossing measure from moments**: a measure `ν` on `ℝ`, finite on compacts, carried by
`X ⊆ [T₀, ∞)`, with weighted budget `∫ w̃ dν ≤ C₀` and `∫ f̃_β dν = a_β` for all `β > 0`, is a
crossing measure (conditions (Z1), (Z2)) with `∫ w_* dν ≤ C₀`. -/
theorem exists_crossing_of_moments (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {ν : Measure ℝ} [IsFiniteMeasureOnCompacts ν]
    {X : Set ℝ} (hX : X ⊆ Ici T₀) (hν : ν Xᶜ = 0)
    (hbud : ∫⁻ y, ENNReal.ofReal (wTilde (cTilde / 12) β₀ T₀ y) ∂ν ≤
      ENNReal.ofReal (dualC0 prob (cTilde / 12) β₀))
    (hmom : ∀ β : ℝ, 0 < β → ∫ y, fTilde prob.w T₀ β y ∂ν = crossingRHS prob (cTilde / 12) β) :
    ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12), meas.ν = ν ∧
      Integrable (wStar (cTilde / 12) β₀) ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  have ha0 := S.ha_pos
  set a := cTilde / 12 with ha_def
  have hC₀ : 0 < dualC0 prob a β₀ := dualC0_pos prob ha0 S.hβ₀ (by linarith [S.hβ₀2])
  have hmae : ∀ᵐ y ∂ν, y ∈ X := by
    have : ∀ᵐ y ∂ν, y ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with y hy using by simpa using hy
  have hwae : wStar a β₀ =ᵐ[ν] wTilde a β₀ T₀ := by
    filter_upwards [hmae] with y hy using (wTilde_of_le (hX hy)).symm
  have hwTint : Integrable (wTilde a β₀ T₀) ν := by
    refine ⟨(measurable_wTilde a β₀ T₀).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => (wTilde_pos ha0 S.hβ₀ S.hT₀pos y).le)]
    exact lt_of_le_of_lt hbud ENNReal.ofReal_lt_top
  have hwint : Integrable (wStar a β₀) ν := hwTint.congr hwae.symm
  have hIio : ν (Iio 0) = 0 :=
    measure_mono_null (fun y hy => fun hyX => by
      have := hX hyX; simp only [mem_Iio, mem_Ici] at hy this; linarith [S.hT₀pos]) hν
  have hrestr : ν.restrict (Ici 0) = ν := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, show {x : ℝ | x ∉ Ici 0} = Iio 0 by ext t; simp]
    exact hIio
  refine ⟨{ ν := ν
            supp_nonneg := hIio
            finite_laplace := fun {β} hβ => ?_
            crossing := fun {β} hβ => ?_ }, rfl, hwint, ?_⟩
  · obtain ⟨C, _, hC⟩ := exp_le_const_wStar (a := a) (β₀ := β₀) ha0.le S.hβ₀ hβ
    refine Integrable.integrableOn ?_
    refine (hwint.const_mul C).mono' (by fun_prop : Continuous fun t : ℝ =>
      Real.exp (-2 * π * β * t)).aestronglyMeasurable ?_
    filter_upwards [hmae] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hC y (S.hT₀pos.le.trans (hX hy))
  · show ∫ t in Ici 0, thermalDiff prob.w β t ∂ν = _
    have hm := hmom β hβ
    unfold crossingRHS at hm
    rw [hrestr, ← hm]
    refine integral_congr_ae ?_
    filter_upwards [hmae] with y hy
    exact (fTilde_of_le (hX hy)).symm
  · have h1 : ∫ t, wStar a β₀ t ∂ν = ∫ t, wTilde a β₀ T₀ t ∂ν := integral_congr_ae hwae
    rw [h1]
    have h2 := ofReal_integral_eq_lintegral_ofReal hwTint
      (Eventually.of_forall fun y => (wTilde_pos ha0 S.hβ₀ S.hT₀pos y).le)
    exact (ENNReal.ofReal_le_ofReal_iff hC₀.le).1 (h2.trans_le hbud)

/-- The budget of a crossing measure carried by `X ⊆ [T₀, ∞)`: `w_* ∈ L¹(ν)` and `∫ w_* dν ≤ C₀`
(because `w_* ≤ h` on `[T₀, ∞)` and `∫ h dν = C₀` exactly). -/
theorem crossing_budget (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) (meas : AdmissibleCrossingMeasure prob (cTilde / 12))
    {X : Set ℝ} (hX : X ⊆ Ici T₀) (hν : meas.ν Xᶜ = 0) :
    Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  have ha0 := S.ha_pos
  have hpair := crossing_pairing_span prob S.hc_pos S.hc S.hβ₀ S.hβ₀2 meas (B := ∅)
    (fun β hβ => absurd hβ (Finset.notMem_empty β)) (fun _ => 0) 1
  have hfun : spanTest prob.w (cTilde / 12) β₀ (∅ : Finset ℝ) (fun _ => (0 : ℝ)) 1 =
      hMaj prob.w (cTilde / 12) β₀ := by
    funext t; simp [spanTest]
  rw [hfun] at hpair
  obtain ⟨hhint, hhval⟩ := hpair
  rw [Duality.restrict_Ici_eq_self meas] at hhval
  rw [IntegrableOn, Duality.restrict_Ici_eq_self meas] at hhint
  have hmae : ∀ᵐ y ∂meas.ν, y ∈ X := by
    have : ∀ᵐ y ∂meas.ν, y ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with y hy using by simpa using hy
  have hle : ∀ᵐ y ∂meas.ν, wStar (cTilde / 12) β₀ y ≤ hMaj prob.w (cTilde / 12) β₀ y := by
    filter_upwards [hmae] with y hy
    exact wStar_le_hMaj prob.hw ha0 S.hβ₀ (by linarith [S.hβ₀2]) S.hT₀ (hX hy)
  have hnn : ∀ᵐ y ∂meas.ν, 0 ≤ wStar (cTilde / 12) β₀ y := by
    filter_upwards [hmae] with y hy
    exact (wStar_pos ha0.le S.hβ₀ (S.hT₀pos.le.trans (hX hy))).le
  have hwint : Integrable (wStar (cTilde / 12) β₀) meas.ν :=
    hhint.mono' (measurable_wStar _ _).aestronglyMeasurable (by
      filter_upwards [hle, hnn] with y h1 h2
      rw [Real.norm_eq_abs, abs_of_nonneg h2]; exact h1)
  have hv : ∫ t, hMaj prob.w (cTilde / 12) β₀ t ∂meas.ν = dualC0 prob (cTilde / 12) β₀ := by
    rw [hhval]; simp
  exact ⟨hwint, hv ▸ integral_mono_ae hwint hhint hle⟩

/-! ### (i) ⇒ (ii) and the finite-dimensional hypothesis -/

/-- Condition (ii) of `ds:E`(a): no test `g = Σ_{β ∈ B} l_β Ξ_β + μ h` which is nonnegative on `X`
has `g_vac > 0`. -/
def NoSpanFeasible (prob : FixedWeightProblem) (cTilde β₀ : ℝ) (X : Set ℝ) : Prop :=
  ∀ (B : Finset ℝ), (∀ β ∈ B, 0 < β) → ∀ (l : ℝ → ℝ) (μ : ℝ),
    (∀ t ∈ X, 0 ≤ spanTest prob.w (cTilde / 12) β₀ B l μ t) →
      prob.gVac (cTilde / 12) (spanTest prob.w (cTilde / 12) β₀ B l μ) ≤ 0

/-- (i) ⇒ (ii): a crossing measure carried by `X` excludes every span test feasible on `X`. -/
theorem noSpanFeasible_of_crossingMeasure (prob : FixedWeightProblem) {cTilde β₀ : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde) (hβ₀ : 0 < β₀) (hβ₀2 : β₀ ≤ 1 / 2)
    (meas : AdmissibleCrossingMeasure prob (cTilde / 12)) {X : Set ℝ} (hν : meas.ν Xᶜ = 0) :
    NoSpanFeasible prob cTilde β₀ X := by
  intro B hB l μ hnn
  have ha : prob.totalShift ≤ cTilde / 12 := by linarith
  have ha0 : 0 < cTilde / 12 := by linarith
  obtain ⟨-, hval⟩ := crossing_pairing_span prob hc_pos hc hβ₀ hβ₀2 meas hB l μ
  have hvac := gVac_spanTest prob ha ha0 hB l μ (β₀ := β₀)
  have hae : ∀ᵐ t ∂meas.ν, 0 ≤ spanTest prob.w (cTilde / 12) β₀ B l μ t := by
    have : ∀ᵐ y ∂meas.ν, y ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with y hy using hnn y (by simpa using hy)
  rw [Duality.restrict_Ici_eq_self meas] at hval
  have h0 : 0 ≤ ∫ t, spanTest prob.w (cTilde / 12) β₀ B l μ t ∂meas.ν := integral_nonneg_of_ae hae
  rw [hvac]
  linarith

/-- A finite combination `b + Σ λ_i f̃_i / w̃ ≥ 0` on `X` (`b ≥ 0`) is a span test: there are
`B ⊂ (0, ∞)` and `l` with `Σ_{β∈B} l_β F_β = Σ_{i∈u} λ_i F_i` for every `F`, and
`Σ l_β Ξ_β + b h ≥ 0` on `X` (because `w_* ≤ h` on `[T₀, ∞)`). -/
lemma span_of_ratio (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ} (hX : X ⊆ Ici T₀)
    (u : Finset {β : ℝ // 0 < β}) (lam : {β : ℝ // 0 < β} → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hnn : ∀ y ∈ X, 0 ≤ b + ∑ i ∈ u, lam i * (fTilde prob.w T₀ i.1 y / wTilde (cTilde / 12) β₀ T₀ y)) :
    ∃ (B : Finset ℝ) (_ : ∀ β ∈ B, 0 < β) (l : ℝ → ℝ),
      (∀ F : ℝ → ℝ, ∑ β ∈ B, l β * F β = ∑ i ∈ u, lam i * F i.1) ∧
      ∀ t ∈ X, 0 ≤ spanTest prob.w (cTilde / 12) β₀ B l b t := by
  classical
  have ha0 := S.ha_pos
  set B : Finset ℝ := u.image Subtype.val with hBdef
  have hB : ∀ β ∈ B, 0 < β := fun β hβ => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hβ; exact i.2
  set l : ℝ → ℝ := fun β => if h : 0 < β then lam ⟨β, h⟩ else 0 with hl
  have hl' : ∀ i : {β : ℝ // 0 < β}, l i.1 = lam i := fun i => by simp [hl, i.2]
  have hsumB : ∀ F : ℝ → ℝ, ∑ β ∈ B, l β * F β = ∑ i ∈ u, lam i * F i.1 := by
    intro F
    rw [hBdef, Finset.sum_image (fun i _ j _ h => Subtype.val_injective h)]
    exact Finset.sum_congr rfl fun i _ => by rw [hl']
  refine ⟨B, hB, l, hsumB, fun t ht => ?_⟩
  have ht0 := hX ht
  have hw := wStar_pos ha0.le S.hβ₀ (S.hT₀pos.le.trans ht0)
  have hM := wStar_le_hMaj prob.hw ha0 S.hβ₀ (by linarith [S.hβ₀2]) S.hT₀ ht0
  have h1 := hnn t ht
  rw [wTilde_of_le ht0] at h1
  have h1' : ∀ i ∈ u, fTilde prob.w T₀ i.1 t = thermalDiff prob.w i.1 t := fun i _ => fTilde_of_le ht0
  have h2 : 0 ≤ b * wStar (cTilde / 12) β₀ t + ∑ i ∈ u, lam i * thermalDiff prob.w i.1 t := by
    have e : b + ∑ i ∈ u, lam i * (fTilde prob.w T₀ i.1 t / wStar (cTilde / 12) β₀ t) =
        (b * wStar (cTilde / 12) β₀ t + ∑ i ∈ u, lam i * thermalDiff prob.w i.1 t) /
          wStar (cTilde / 12) β₀ t := by
      rw [add_div, Finset.sum_div, mul_div_assoc, div_self hw.ne', mul_one]
      congr 1
      exact Finset.sum_congr rfl fun i hi => by rw [h1' i hi]; ring
    rw [e] at h1
    exact (div_nonneg_iff.1 h1).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 hw)
  unfold spanTest
  rw [hsumB (fun β => thermalDiff prob.w β t)]
  nlinarith [mul_le_mul_of_nonneg_left hM hb]

/-- The dual inequality for finitely many constraints on one set `X ⊆ [T₀, ∞)`, in the
normalisation of `ds:farkas` (`w̃`, `f̃_β`), from `NoSpanFeasible`. -/
lemma dual_inequality_of_noSpan (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ} (hX : X ⊆ Ici T₀)
    (hns : NoSpanFeasible prob cTilde β₀ X)
    (u : Finset {β : ℝ // 0 < β}) (lam : {β : ℝ // 0 < β} → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hnn : ∀ y ∈ X, 0 ≤ b + ∑ i ∈ u, lam i * (fTilde prob.w T₀ i.1 y / wTilde (cTilde / 12) β₀ T₀ y)) :
    0 ≤ b * dualC0 prob (cTilde / 12) β₀ +
      ∑ i ∈ u, lam i * crossingRHS prob (cTilde / 12) i.1 := by
  obtain ⟨B, hB, l, hsumB, hg⟩ := span_of_ratio prob S hX u lam b hb hnn
  have := hns B hB l b hg
  rw [gVac_spanTest prob S.ha S.ha_pos hB l b, hsumB (fun β => crossingRHS prob (cTilde / 12) β)] at this
  linarith

/-! ### The theorem -/

/-- **Theorem E(a), existence for decreasing supports** (`ds:E`(a), last clause): if (ii) holds on
closed `X_0 ⊇ X_1 ⊇ ⋯` inside `[T₀, ∞)` then there is a crossing measure carried by `⋂ X_j`, with
`∫ w_* dν ≤ C₀`. -/
theorem theorem_E_a_decreasing (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {X : ℕ → Set ℝ} (hXc : ∀ j, IsClosed (X j))
    (hXa : Antitone X) (hX : X 0 ⊆ Ici T₀) (hns : ∀ j, NoSpanFeasible prob cTilde β₀ (X j)) :
    ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12), meas.ν (⋂ j, X j)ᶜ = 0 ∧
      Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  have ha0 := S.ha_pos
  have hC₀ : 0 < dualC0 prob (cTilde / 12) β₀ := dualC0_pos prob ha0 S.hβ₀ (by linarith [S.hβ₀2])
  have hX' : ∀ j, X j ⊆ Ici T₀ := fun j => (hXa (Nat.zero_le j)).trans hX
  obtain ⟨ν, hνf, hνsupp, hνbud, hνmom⟩ := farkas_separation (Y := ℝ)
    (I := {β : ℝ // 0 < β}) (w := wTilde (cTilde / 12) β₀ T₀)
    (continuous_wTilde ha0 S.hT₀pos) (wTilde_pos ha0 S.hβ₀ S.hT₀pos) hC₀ hXc hXa
    (f := fun i => fTilde prob.w T₀ i.1) (fun i => continuous_fTilde _ _ _)
    (fun i => fTilde_decay ha0 S.hβ₀ S.hT₀pos i.2 hX)
    (a := fun i => crossingRHS prob (cTilde / 12) i.1)
    (fun j u lam b hb hnn => dual_inequality_of_noSpan prob S (hX' j) (hns j) u lam b hb hnn)
  obtain ⟨meas, hmeas, hint, hle⟩ := exists_crossing_of_moments prob S
    (X := ⋂ j, X j) (fun y hy => hX (mem_iInter.1 hy 0)) hνsupp hνbud
    (fun β hβ => (hνmom ⟨β, hβ⟩).2)
  exact ⟨meas, hmeas ▸ hνsupp, hmeas ▸ hint, hmeas ▸ hle⟩

/-- **Theorem E(a)** (`ds:E`(a), `dual_spectrum.tex`) at every fixed weight `(w, Q)`: for a closed
`X ⊆ [T₀, ∞)`, (i) a positive crossing measure carried by `X` exists iff (ii) no test of
`span{Ξ_β, h}` nonnegative on `X` has `g_vac > 0`.  Moreover every crossing measure carried by `X`
has `w_* ∈ L¹` and `∫ w_* dν ≤ C₀`, and if `X` contains a terminal ray, (i), (ii) are equivalent
to the absence of a strictly feasible `g ∈ Ā_w` on `X`. -/
theorem theorem_E_a (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀) :
    ((∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12), meas.ν Xᶜ = 0) ↔
      NoSpanFeasible prob cTilde β₀ X) ∧
    (∀ meas : AdmissibleCrossingMeasure prob (cTilde / 12), meas.ν Xᶜ = 0 →
      Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
        ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀) ∧
    ((∃ τ, Ici τ ⊆ X) →
      (NoSpanFeasible prob cTilde β₀ X ↔ ∀ g, ¬ prob.IsFeasibleOn (cTilde / 12) X g)) := by
  refine ⟨⟨?_, ?_⟩, fun meas hν => crossing_budget prob S meas hX hν, fun hray => ⟨?_, ?_⟩⟩
  · rintro ⟨meas, hν⟩
    exact noSpanFeasible_of_crossingMeasure prob S.hc_pos S.hc S.hβ₀ S.hβ₀2 meas hν
  · intro hns
    obtain ⟨meas, hν, -⟩ := theorem_E_a_decreasing prob S (X := fun _ => X) (fun _ => hXc)
      (fun _ _ _ => le_rfl) hX (fun _ => hns)
    exact ⟨meas, by simpa using hν⟩
  · intro hns
    obtain ⟨meas, hν⟩ : ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12), meas.ν Xᶜ = 0 := by
      obtain ⟨meas, hν, -⟩ := theorem_E_a_decreasing prob S (X := fun _ => X) (fun _ => hXc)
        (fun _ _ _ => le_rfl) hX (fun _ => hns)
      exact ⟨meas, by simpa using hν⟩
    obtain ⟨τ, hτ⟩ := hray
    exact fun g => not_feasible_of_crossingMeasure prob S.ha S.ha_pos meas hν hτ g
  · intro hno B hB l μ hnn
    have hmem := spanTest_mem prob S.ha S.ha_pos (β₀ := β₀) hB l μ
    by_contra hpos
    exact hno _ ⟨hmem, not_le.1 hpos, hnn⟩

/-- **Theorem E(a), finite atomic solutions** (`ds:E`(a)): under (ii), for every finite
`B ⊂ (0, ∞)` the moments `∫ Ξ_β dν = a_β` (`β ∈ B`) are attained exactly by a positive measure
`ν = Σ_k r_k δ_{y_k}` carried by `X`, with at most `|B| + 1` atoms and `∫ w_* dν = Σ r_k w_*(y_k) ≤ C₀`. -/
theorem theorem_E_a_finite (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀)
    (hns : NoSpanFeasible prob cTilde β₀ X) (B : Finset ℝ) (hB : ∀ β ∈ B, 0 < β) :
    ∃ (ι : Type) (_ : Fintype ι) (y : ι → ℝ) (r : ι → ℝ), Fintype.card ι ≤ B.card + 1 ∧
      (∀ k, y k ∈ X) ∧ (∀ k, 0 ≤ r k) ∧ ∑ k, r k * wStar (cTilde / 12) β₀ (y k) ≤
        dualC0 prob (cTilde / 12) β₀ ∧
      ∀ β ∈ B, ∑ k, r k * thermalDiff prob.w β (y k) = crossingRHS prob (cTilde / 12) β := by
  classical
  have ha0 := S.ha_pos
  have hC₀ : 0 < dualC0 prob (cTilde / 12) β₀ := dualC0_pos prob ha0 S.hβ₀ (by linarith [S.hβ₀2])
  obtain ⟨ι, hι, y, r, hcard, hyX, hr, hbud, hmom⟩ := farkas_finite (Y := ℝ)
    (I := {β : ℝ // 0 < β}) hXc (w := wTilde (cTilde / 12) β₀ T₀)
    (continuous_wTilde ha0 S.hT₀pos) (wTilde_pos ha0 S.hβ₀ S.hT₀pos) hC₀
    (f := fun i => fTilde prob.w T₀ i.1) (fun i => continuous_fTilde _ _ _)
    (fun i => fTilde_decay ha0 S.hβ₀ S.hT₀pos i.2 hX)
    (a := fun i => crossingRHS prob (cTilde / 12) i.1)
    (B.subtype (fun β => 0 < β))
    (fun lam b hb hnn => dual_inequality_of_noSpan prob S hX hns _ lam b hb hnn)
  refine ⟨ι, hι, y, r, hcard.trans (by
      have : (B.subtype (fun β => 0 < β)).card ≤ B.card := by
        rw [Finset.card_subtype]; exact Finset.card_filter_le _ _
      omega), hyX, hr, ?_, fun β hβ => ?_⟩
  · refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) hbud
    rw [wTilde_of_le (hX (hyX k))]
  · have := hmom ⟨β, hB β hβ⟩ (by simpa using hβ)
    simp only at this
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => by rw [fTilde_of_le (hX (hyX k))]

/-- The moments of a crossing measure carried by `X ⊆ [T₀, ∞)` in the normalisation `f̃_β`. -/
lemma crossing_moment_fTilde (prob : FixedWeightProblem) {a T₀ : ℝ}
    (meas : AdmissibleCrossingMeasure prob a) {X : Set ℝ} (hX : X ⊆ Ici T₀) (hν : meas.ν Xᶜ = 0)
    {β : ℝ} (hβ : 0 < β) : ∫ y, fTilde prob.w T₀ β y ∂meas.ν = crossingRHS prob a β := by
  have hmae : ∀ᵐ y ∂meas.ν, y ∈ X := by
    have : ∀ᵐ y ∂meas.ν, y ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with y hy using by simpa using hy
  have h1 := meas.crossing hβ
  rw [Duality.restrict_Ici_eq_self meas] at h1
  unfold crossingRHS
  rw [← h1]
  refine integral_congr_ae ?_
  filter_upwards [hmae] with y hy using fTilde_of_le (hX hy)

/-- The weighted budget `∫ w̃ dν ≤ C₀` of a crossing measure carried by `X ⊆ [T₀, ∞)`. -/
lemma crossing_lintegral_budget (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) (meas : AdmissibleCrossingMeasure prob (cTilde / 12))
    {X : Set ℝ} (hX : X ⊆ Ici T₀) (hν : meas.ν Xᶜ = 0) :
    ∫⁻ y, ENNReal.ofReal (wTilde (cTilde / 12) β₀ T₀ y) ∂meas.ν ≤
      ENNReal.ofReal (dualC0 prob (cTilde / 12) β₀) := by
  have ha0 := S.ha_pos
  obtain ⟨hint, hle⟩ := crossing_budget prob S meas hX hν
  have hmae : ∀ᵐ y ∂meas.ν, y ∈ X := by
    have : ∀ᵐ y ∂meas.ν, y ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with y hy using by simpa using hy
  have hnn : ∀ᵐ y ∂meas.ν, 0 ≤ wStar (cTilde / 12) β₀ y := by
    filter_upwards [hmae] with y hy
    exact (wStar_pos ha0.le S.hβ₀ (S.hT₀pos.le.trans (hX hy))).le
  have h1 : ∫⁻ y, ENNReal.ofReal (wTilde (cTilde / 12) β₀ T₀ y) ∂meas.ν =
      ∫⁻ y, ENNReal.ofReal (wStar (cTilde / 12) β₀ y) ∂meas.ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [hmae] with y hy using by rw [wTilde_of_le (hX hy)]
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint hnn]
  exact ENNReal.ofReal_le_ofReal hle

/-- **Theorem E(a), compactness** (`ds:E`(a), last clause): crossing measures `ν_j` carried by
decreasing closed `X_j ⊆ [T₀, ∞)` have, along every ultrafilter `𝒰 ≤ atTop`, a vague limit which is
a crossing measure carried by `⋂ X_j`, with `w_* ∈ L¹` and `∫ w_* dν ≤ C₀`. -/
theorem theorem_E_a_compactness (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {X : ℕ → Set ℝ} (hXc : ∀ j, IsClosed (X j))
    (hXa : Antitone X) (hX : X 0 ⊆ Ici T₀)
    (meas : ℕ → AdmissibleCrossingMeasure prob (cTilde / 12)) (hsupp : ∀ j, (meas j).ν (X j)ᶜ = 0)
    (𝒰 : Ultrafilter ℕ) (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) :
    ∃ meas' : AdmissibleCrossingMeasure prob (cTilde / 12),
      IsVagueLimitAlong (𝒰 : Filter ℕ) (fun j => (meas j).ν) meas'.ν ∧
      meas'.ν (⋂ j, X j)ᶜ = 0 ∧ Integrable (wStar (cTilde / 12) β₀) meas'.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas'.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  have ha0 := S.ha_pos
  have hC₀ : 0 < dualC0 prob (cTilde / 12) β₀ := dualC0_pos prob ha0 S.hβ₀ (by linarith [S.hβ₀2])
  have hX' : ∀ j, X j ⊆ Ici T₀ := fun j => (hXa (Nat.zero_le j)).trans hX
  have : ∀ j, IsFiniteMeasureOnCompacts (meas j).ν := fun j => (meas j).isFiniteMeasureOnCompacts
  obtain ⟨ν, hνf, hlim, hνsupp, hνbud, hνmom⟩ := farkas_compactness (Y := ℝ)
    (I := {β : ℝ // 0 < β}) (w := wTilde (cTilde / 12) β₀ T₀)
    (continuous_wTilde ha0 S.hT₀pos) (wTilde_pos ha0 S.hβ₀ S.hT₀pos) hC₀ hXc hXa
    (f := fun i => fTilde prob.w T₀ i.1) (fun i => continuous_fTilde _ _ _)
    (fun i => fTilde_decay ha0 S.hβ₀ S.hT₀pos i.2 hX)
    (a := fun i => crossingRHS prob (cTilde / 12) i.1) (fun j => (meas j).ν) hsupp
    (fun j => crossing_lintegral_budget prob S (meas j) (hX' j) (hsupp j))
    (fun j i => crossing_moment_fTilde prob (meas j) (hX' j) (hsupp j) i.2) 𝒰 h𝒰
  obtain ⟨meas', hmeas, hint, hle⟩ := exists_crossing_of_moments prob S
    (X := ⋂ j, X j) (fun y hy => hX (mem_iInter.1 hy 0)) hνsupp hνbud
    (fun β hβ => (hνmom ⟨β, hβ⟩).2)
  exact ⟨meas', hmeas ▸ hlim, hmeas ▸ hνsupp, hmeas ▸ hint, hmeas ▸ hle⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.theorem_E_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.theorem_E_a

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.theorem_E_a_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.theorem_E_a_finite

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.theorem_E_a_decreasing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.theorem_E_a_decreasing

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.theorem_E_a_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.theorem_E_a_compactness

end FormalResearch.ModularBootstrap.FixedWeight
