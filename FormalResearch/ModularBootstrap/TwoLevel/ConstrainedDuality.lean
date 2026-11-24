module

public import FormalResearch.ModularBootstrap.FixedWeight.StrongDuality

/-!
# Strong duality on a constrained admissible set (Theorem E with `X` in place of `[τ, ∞)`)

`dual_spectrum.tex`, Theorem E (`ds:E`) and `virasoro_two_level.tex`, proof of Corollary 2.4 (`gt:2.4`):
the proof of Theorem E(a), (b) repeats verbatim with the admissible set `[τ, ∞)` replaced by any
closed `X ⊆ [T₀, ∞)`, in particular `X = {t₁} ∪ [τ, ∞)`.

For `prob : FixedWeightProblem` and `a = c̃/12` a functional is *feasible on `X`* when `g ∈ Ā` (`TestClass`),
`g_vac > 0` and `g ≥ 0` on `X` (`IsFeasibleOn`; on `X = [T, ∞)` it is `IsFeasible a T`).

* `exists_crossingMeasure_of_not_feasible`: if no functional is feasible on the closed set `X ⊆ [T₀, ∞)`, there
  is a crossing measure `ν` with `ν (Xᶜ) = 0`, `w_* ∈ L¹(ν)` and `∫ w_* dν ≤ C₀`.
* `not_feasible_of_crossingMeasure`: conversely a crossing measure supported on `X` excludes every feasible
  functional on `X` (Lemma FW-X (1)).
* `constrained_strong_duality`: both directions, for every fixed weight `(w, Q)` under `DualSetupCore`
  (`DualSetup` without the unused `T₀ < T_V(c̃)`).
* `constrained_strong_duality_two_level`: the instance `X = {t₁} ∪ [τ, ∞)`.

Section 1 contains the general finite moment problem, compactness and transport statements. They
generalise `dual_inequality`, `exists_atomic_approx`, `exists_measure_exact`, `exists_crossingMeasure_of_limit`
and `pullMeasure_Iio_eq_zero` (the `X = [T, ∞)` instances).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real NNReal BoundedContinuousFunction

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality

/-! ### Section 1: the general lemmas -/

/-- `DualSetup` without the hypothesis `T₀ < T_V(c̃)`. -/
structure DualSetupCore (prob : FixedWeightProblem) (cTilde β₀ T₀ : ℝ) : Prop where
  hc_pos : 0 < cTilde
  hc : 12 * prob.totalShift ≤ cTilde
  hβ₀ : 0 < β₀
  hβ₀2 : β₀ ≤ 1 / 2
  hT₀ : t0Star prob.w β₀ ≤ T₀
  hT₀pos : 0 < T₀

lemma DualSetup.toCore {prob : FixedWeightProblem} {cTilde β₀ T₀ : ℝ}
    (S : DualSetup prob cTilde β₀ T₀) : DualSetupCore prob cTilde β₀ T₀ :=
  ⟨S.hc_pos, S.hc, S.hβ₀, S.hβ₀2, S.hT₀, S.hT₀pos⟩

lemma DualSetupCore.ha {prob : FixedWeightProblem} {cTilde β₀ T₀ : ℝ}
    (h : DualSetupCore prob cTilde β₀ T₀) : prob.totalShift ≤ cTilde / 12 := by
  linarith [h.hc]

lemma DualSetupCore.ha_pos {prob : FixedWeightProblem} {cTilde β₀ T₀ : ℝ}
    (h : DualSetupCore prob cTilde β₀ T₀) : 0 < cTilde / 12 := by
  linarith [h.hc_pos]

/-- Feasibility of `g ∈ Ā_w` on a set `X`: `g_vac > 0` and `g ≥ 0` on `X`. -/
def _root_.FormalResearch.ModularBootstrap.Crossing.FixedWeightProblem.IsFeasibleOn
    (prob : FixedWeightProblem) (a : ℝ) (X : Set ℝ) (g : ℝ → ℝ) : Prop :=
  TestClass prob a g ∧ 0 < prob.gVac a g ∧ ∀ t ∈ X, 0 ≤ g t

lemma isFeasibleOn_Ici_iff (prob : FixedWeightProblem) (a T : ℝ) (g : ℝ → ℝ) :
    prob.IsFeasibleOn a (Ici T) g ↔ prob.IsFeasible a T g := by
  unfold FixedWeightProblem.IsFeasibleOn FixedWeightProblem.IsFeasible
  simp only [mem_Ici, ge_iff_le]

/-- The dual inequality on a set `X ⊆ [T₀, ∞)` with no feasible functional (generalises
`dual_inequality`, the case `X = [T, ∞)`). -/
lemma dual_inequality_on (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ} (hX : X ⊆ Ici T₀)
    (hno : ∀ g, ¬ prob.IsFeasibleOn (cTilde / 12) X g)
    {ι : Type*} [Fintype ι] (β : ι → ℝ) (hβ : ∀ i, 0 < β i)
    (l : ι → ℝ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hnn : ∀ t ∈ X,
      0 ≤ ∑ i, l i * (thermalDiff prob.w (β i) t / wStar (cTilde / 12) β₀ t) + μ) :
    0 ≤ ∑ i, l i * crossingRHS prob (cTilde / 12) (β i) + μ * dualC0 prob (cTilde / 12) β₀ := by
  by_contra hneg
  push Not at hneg
  have ha := S.ha
  have ha0 := S.ha_pos
  set a := cTilde / 12 with ha_def
  let g : ℝ → ℝ := fun t => (∑ i, l i * thermalDiff prob.w (β i) t) + μ * hMaj prob.w a β₀ t
  have hXi : ∀ i, TestClass prob a (thermalDiff prob.w (β i)) := fun i =>
    thermalDiff_mem_TestClass prob ha (hβ i)
  have hsum := Duality.testClass_sum (a := a) (Finset.univ : Finset ι) l
    (fun i => thermalDiff prob.w (β i)) (fun i _ => hXi i)
  have hhM := hMaj_mem_TestClass prob (β₀ := β₀) ha ha0
  have hgT : TestClass prob a g := hsum.add (hhM.smul μ)
  have hvac : prob.gVac a g =
      ∑ i, l i * prob.gVac a (thermalDiff prob.w (β i)) + μ * prob.gVac a (hMaj prob.w a β₀) := by
    have := prob.gVac_add hsum (hhM.smul μ)
    rw [prob.gVac_smul μ hhM, Duality.gVac_sum _ l _ (fun i _ => hXi i)] at this
    exact this
  have hvac' : prob.gVac a g =
      -(∑ i, l i * crossingRHS prob a (β i) + μ * dualC0 prob a β₀) := by
    rw [hvac, hMaj_vac prob ha ha0]
    simp_rw [gVac_thermalDiff_eq_neg]
    have hsum_neg : ∑ i, l i * -crossingRHS prob a (β i) = -∑ i, l i * crossingRHS prob a (β i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum_neg]
    ring
  refine hno g ⟨hgT, ?_, ?_⟩
  · rw [hvac']; linarith
  · intro t ht
    have ht0 : T₀ ≤ t := hX ht
    have hw := wStar_pos ha0.le S.hβ₀ (S.hT₀pos.le.trans ht0)
    have hM := wStar_le_hMaj prob.hw ha0 S.hβ₀ (by linarith [S.hβ₀2]) S.hT₀ ht0
    have h1 := hnn t ht
    have h2 : 0 ≤ (∑ i, l i * thermalDiff prob.w (β i) t + μ * wStar a β₀ t) / wStar a β₀ t := by
      have heq : (∑ i, l i * thermalDiff prob.w (β i) t + μ * wStar a β₀ t) / wStar a β₀ t =
          ∑ i, l i * (thermalDiff prob.w (β i) t / wStar a β₀ t) + μ := by
        rw [add_div, Finset.sum_div, mul_div_assoc, div_self hw.ne', mul_one]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [heq]; exact h1
    have h4 : 0 ≤ ∑ i, l i * thermalDiff prob.w (β i) t + μ * wStar a β₀ t := by
      rcases div_nonneg_iff.mp h2 with ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · exact absurd h (not_le.mpr hw)
    show 0 ≤ (∑ i, l i * thermalDiff prob.w (β i) t) + μ * hMaj prob.w a β₀ t
    nlinarith [mul_le_mul_of_nonneg_left hM hμ]

/-- Theorem E(a) on a set `X ⊆ [T₀, ∞)` with no feasible functional: finite positive atomic
measures on `X` with `∑ c_k ≤ C₀` solving finitely many crossing equations up to `ε` (generalises
`exists_atomic_approx`). -/
theorem exists_atomic_approx_on (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ} (hX : X ⊆ Ici T₀)
    (hno : ∀ g, ¬ prob.IsFeasibleOn (cTilde / 12) X g)
    (B : Finset ℝ) (hB : ∀ β ∈ B, 0 < β) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (t : Fin N → ℝ) (c : Fin N → ℝ), (∀ k, t k ∈ X) ∧ (∀ k, 0 ≤ c k) ∧
      ∑ k, c k ≤ dualC0 prob (cTilde / 12) β₀ ∧
      ∀ β ∈ B, |∑ k, c k * (thermalDiff prob.w β (t k) / wStar (cTilde / 12) β₀ (t k)) -
        crossingRHS prob (cTilde / 12) β| < ε := by
  have hC0 : 0 < dualC0 prob (cTilde / 12) β₀ :=
    dualC0_pos prob S.ha_pos S.hβ₀ (by linarith [S.hβ₀2])
  obtain ⟨N, x, c, hc, hs, hd⟩ := farkas_approx (ι := B) (X := {t : ℝ // t ∈ X})
    (fun i x => thermalDiff prob.w i x.1 / wStar (cTilde / 12) β₀ x.1)
    (fun i => crossingRHS prob (cTilde / 12) i) hC0
    (fun l μ hμ hnn => dual_inequality_on prob S hX hno (fun i : B => (i : ℝ))
      (fun i => hB i i.2) l hμ (fun t ht => hnn ⟨t, ht⟩)) hε
  refine ⟨N, fun k => (x k).1, c, fun k => (x k).2, hc, hs, fun β hβ => ?_⟩
  exact hd ⟨β, hβ⟩

/-- **Theorem E(a)+(b), exactness on `[0, 1]`**, with an abstract cut-off `ζ` vanishing on the image of `X`
(generalises `exists_measure_exact`, the case `X = [T, ∞)`, `ζ = ζ_T`). -/
theorem exists_measure_exact_on (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ} (hX : X ⊆ Ici T₀)
    (hno : ∀ g, ¬ prob.IsFeasibleOn (cTilde / 12) X g)
    (ζ : Ecoord →ᵇ ℝ) (hζ : ∀ t ∈ X, ζ (toE T₀ t) = 0) :
    ∃ μ : FiniteMeasure Ecoord, (μ.mass : ℝ) ≤ dualC0 prob (cTilde / 12) β₀ ∧
      ∫ x, ζ x ∂(μ : Measure Ecoord) = 0 ∧
      ∀ (β : ℝ) (hβ : 0 < β),
        ∫ x, FtildeB (w := prob.w) (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀)
          S.ha_pos S.hβ₀ S.hT₀pos hβ x ∂(μ : Measure Ecoord) =
          crossingRHS prob (cTilde / 12) β := by
  have ha0 := S.ha_pos
  have hC0 : 0 < dualC0 prob (cTilde / 12) β₀ :=
    dualC0_pos prob ha0 S.hβ₀ (by linarith [S.hβ₀2])
  set C : ℝ≥0 := (dualC0 prob (cTilde / 12) β₀).toNNReal with hC
  have hCcoe : (C : ℝ) = dualC0 prob (cTilde / 12) β₀ := Real.coe_toNNReal _ hC0.le
  obtain ⟨μ, hμK, hμ⟩ := exists_exact_of_approx (isCompact_Kset C ζ) (isClosed_Kset C ζ)
    (J := {β : ℝ // 0 < β})
    (fun j => FtildeB (w := prob.w) (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀)
      ha0 S.hβ₀ S.hT₀pos j.2)
    (fun j => crossingRHS prob (cTilde / 12) j.1) (fun u n => by
      obtain ⟨N, t, c, ht, hc, hs, hd⟩ := exists_atomic_approx_on prob S hX hno
        (u.image Subtype.val) (fun β hβ => by
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hβ; exact j.2)
        (by positivity : (0 : ℝ) < 1 / (n + 1))
      let μ : FiniteMeasure Ecoord := ⟨atomMeasure T₀ t c, inferInstance⟩
      have hint := integral_atomMeasure T₀ t c hc
      refine ⟨μ, ⟨?_, ?_⟩, fun j hj => ?_⟩
      · show (μ.mass : ℝ) ≤ C
        rw [finiteMeasure_mass_coe, hCcoe]
        show (atomMeasure T₀ t c).real univ ≤ _
        rw [atomMeasure_real_univ T₀ t c hc]; exact hs
      · show ∫ x, ζ x ∂(atomMeasure T₀ t c) = 0
        rw [hint]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hζ _ (ht k), mul_zero]
      · show |∫ x, _ ∂(atomMeasure T₀ t c) - _| ≤ _
        rw [hint]
        have := hd j.1 (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
        refine le_of_lt ?_
        convert this using 3
        refine Finset.sum_congr rfl fun k _ => ?_
        have e : (FtildeB (w := prob.w) (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀)
            ha0 S.hβ₀ S.hT₀pos j.2) (toE T₀ (t k)) =
            Ftilde prob.w (cTilde / 12) β₀ T₀ j.1 (toE T₀ (t k)) := rfl
        rw [e, Ftilde_toE _ _ _ _ _ (hX (ht k))])
  refine ⟨μ, ?_, hμK.2, fun β hβ => hμ ⟨β, hβ⟩⟩
  have := hμK.1
  rw [← hCcoe]; exact_mod_cast this

end FormalResearch.ModularBootstrap.FixedWeight

namespace FormalResearch.ModularBootstrap.Duality

open FormalResearch.ModularBootstrap.Crossing

section

variable {a β₀ T₀ : ℝ} (μ : Measure Ecoord) [IsFiniteMeasure μ]

/-- Support of the pulled-back measure: if a cut-off `ζ ≥ 0` has `∫ ζ dμ = 0` and `ζ s = 0`, `s > 0`
forces `τ(s) ∈ X` for a measurable `X`, then `pullMeasure a β₀ T₀ μ` vanishes on `Xᶜ` (generalises
`pullMeasure_Iio_eq_zero`, the case `X = [T, ∞)`, `ζ = ζ_T`). -/
lemma pullMeasure_compl_eq_zero {X : Set ℝ} (hXm : MeasurableSet X) {ζ : Ecoord →ᵇ ℝ}
    (hζ0 : ∀ s, 0 ≤ ζ s) (hζX : ∀ s : Ecoord, 0 < s.1 → ζ s = 0 → tauE T₀ s ∈ X)
    (hζ : ∫ s, ζ s ∂μ = 0) :
    pullMeasure a β₀ T₀ μ Xᶜ = 0 := by
  have hae : ζ =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg hζ0 (BoundedContinuousFunction.integrable μ _)).1 hζ
  have hnull : μ {s : Ecoord | tauE T₀ s ∉ X ∧ 0 < s.1} = 0 := by
    refine measure_mono_null (fun s hs => ?_) (ae_iff.1 hae)
    simp only [mem_ofPred_eq, Pi.zero_apply]
    intro h0
    exact hs.1 (hζX s hs.2 h0)
  have h1 : (Measure.map (tauE T₀) (μ.restrict posSet)) Xᶜ = 0 := by
    rw [Measure.map_apply (measurable_tauE T₀) hXm.compl,
      Measure.restrict_apply (measurable_tauE T₀ hXm.compl)]
    refine measure_mono_null (fun s hs => ?_) hnull
    exact ⟨hs.1, hs.2⟩
  exact withDensity_absolutelyContinuous _ _ h1

end

end FormalResearch.ModularBootstrap.Duality

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality

/-- **Theorem E(b), transport**, with an abstract cut-off (generalises `exists_crossingMeasure_of_limit`):
the measure `ν` obtained from the limit measure `μ` vanishes on `Xᶜ` whenever `∫ ζ dμ = 0` for a cut-off
`ζ ≥ 0` whose zero set in `{s > 0}` lies over `X`. -/
theorem exists_crossingMeasure_of_limit_on (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) (μ : FiniteMeasure Ecoord)
    (hmass : (μ.mass : ℝ) ≤ dualC0 prob (cTilde / 12) β₀)
    (hcross : ∀ (β : ℝ) (hβ : 0 < β),
      ∫ x, FtildeB (w := prob.w) (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀)
        S.ha_pos S.hβ₀ S.hT₀pos hβ x ∂(μ : Measure Ecoord) =
        crossingRHS prob (cTilde / 12) β) :
    ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      (∀ {X : Set ℝ}, MeasurableSet X → ∀ ζ : Ecoord →ᵇ ℝ, (∀ s, 0 ≤ ζ s) →
        (∀ s : Ecoord, 0 < s.1 → ζ s = 0 → tauE T₀ s ∈ X) →
        ∫ x, ζ x ∂(μ : Measure Ecoord) = 0 → meas.ν Xᶜ = 0) ∧
      Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  have ha0 := S.ha_pos
  set a := cTilde / 12 with ha_def
  set ν := pullMeasure a β₀ T₀ (μ : Measure Ecoord) with hν
  have hIio0 : ν (Iio 0) = 0 :=
    measure_mono_null (Iio_subset_Iio S.hT₀pos.le) (pullMeasure_Iio_T₀ (μ : Measure Ecoord))
  have hrestr : ν.restrict (Ici 0) = ν := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, show {x : ℝ | x ∉ Ici 0} = Iio 0 by ext t; simp]
    exact hIio0
  have hint_le : ∀ {g : ℝ → ℝ}, Measurable g → ∀ M : ℝ, (∀ t, T₀ ≤ t → |g t| ≤ M * wStar a β₀ t) →
      Integrable g ν := fun hg M hM =>
    integrable_pullMeasure_of_le ha0 S.hβ₀ S.hT₀pos (μ : Measure Ecoord) hg M hM
  have hw_int : Integrable (wStar a β₀) ν := by
    refine hint_le (measurable_wStar a β₀) 1 fun t ht => ?_
    rw [abs_of_pos (wStar_pos ha0.le S.hβ₀ (S.hT₀pos.le.trans ht)), one_mul]
  refine ⟨{ ν := ν
            supp_nonneg := hIio0
            finite_laplace := fun {β} hβ => ?_
            crossing := fun {β} hβ => ?_ }, fun {X} hXm ζ hζ0 hζX hζ => ?_, hw_int, ?_⟩
  · obtain ⟨C, _, hC⟩ := exp_le_const_wStar (a := a) (β₀ := β₀) ha0.le S.hβ₀ hβ
    refine (hint_le (by fun_prop) C fun t ht => ?_).integrableOn
    rw [abs_of_pos (Real.exp_pos _)]
    exact hC t (S.hT₀pos.le.trans ht)
  · show ∫ t in Ici 0, thermalDiff prob.w β t ∂ν = _
    rw [hrestr]
    have hmeas : Measurable (thermalDiff prob.w β) := by unfold thermalDiff; fun_prop
    rw [hν, integral_pullMeasure ha0 S.hβ₀ S.hT₀pos (μ : Measure Ecoord) hmeas]
    have hF : ∫ s in posSet, thermalDiff prob.w β (tauE T₀ s) / wStar a β₀ (tauE T₀ s)
          ∂(μ : Measure Ecoord) =
        ∫ s, Ftilde prob.w a β₀ T₀ β s ∂(μ : Measure Ecoord) := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := posSet)
        (f := Ftilde prob.w a β₀ T₀ β)]
      · refine setIntegral_congr_fun measurableSet_posSet fun s hs => ?_
        have : s.1 ≠ 0 := hs.ne'
        simp [Ftilde, this]
      · intro s hs
        have : s.1 = 0 := by
          have h0 := s.2.1
          by_contra hne
          exact hs (lt_of_le_of_ne h0 (Ne.symm hne))
        simp [Ftilde, this]
    rw [hF]
    exact hcross β hβ
  · exact pullMeasure_compl_eq_zero (a := a) (β₀ := β₀) (μ : Measure Ecoord) hXm hζ0 hζX hζ
  · show ∫ t, wStar a β₀ t ∂ν ≤ dualC0 prob a β₀
    rw [hν, integral_pullMeasure ha0 S.hβ₀ S.hT₀pos (μ : Measure Ecoord) (measurable_wStar a β₀)]
    have h1 : ∫ s in posSet, wStar a β₀ (tauE T₀ s) / wStar a β₀ (tauE T₀ s)
          ∂(μ : Measure Ecoord) =
        ∫ _s in posSet, (1 : ℝ) ∂(μ : Measure Ecoord) := by
      refine setIntegral_congr_fun measurableSet_posSet fun s hs => ?_
      exact div_self (wStar_tauE_pos ha0 S.hβ₀ S.hT₀pos hs).ne'
    rw [h1, setIntegral_const, smul_eq_mul, mul_one]
    refine le_trans ?_ hmass
    rw [finiteMeasure_mass_coe]
    exact measureReal_mono (subset_univ _)

/-- The cut-off `s ↦ dist (s, τ(X))` on `[0, 1]` for a closed set `X ⊆ [T₀, ∞)`. -/
noncomputable def cutoffOfSet (T₀ : ℝ) (X : Set ℝ) : Ecoord →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun s => Metric.infDist s (toE T₀ '' X), Metric.continuous_infDist_pt _⟩

lemma cutoffOfSet_nonneg (T₀ : ℝ) (X : Set ℝ) (s : Ecoord) : 0 ≤ cutoffOfSet T₀ X s :=
  Metric.infDist_nonneg

lemma cutoffOfSet_toE {T₀ : ℝ} {X : Set ℝ} {t : ℝ} (ht : t ∈ X) :
    cutoffOfSet T₀ X (toE T₀ t) = 0 :=
  Metric.infDist_zero_of_mem ⟨t, ht, rfl⟩

lemma tauE_mem_of_cutoffOfSet_eq_zero {T₀ : ℝ} {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀)
    (hne : X.Nonempty) {s : Ecoord} (hs : 0 < s.1) (h0 : cutoffOfSet T₀ X s = 0) :
    tauE T₀ s ∈ X := by
  have hE : (toE T₀ '' X).Nonempty := hne.image _
  have hcl : s ∈ closure (toE T₀ '' X) :=
    (Metric.mem_closure_iff_infDist_zero hE).2 h0
  obtain ⟨x, hxE, hxlim⟩ := mem_closure_iff_seq_limit.1 hcl
  have hτ : Tendsto (fun n => tauE T₀ (x n)) atTop (𝓝 (tauE T₀ s)) :=
    (continuousAt_tauE T₀ hs).tendsto.comp hxlim
  refine hXc.mem_of_tendsto hτ (Eventually.of_forall fun n => ?_)
  obtain ⟨t, ht, hxt⟩ := hxE n
  rw [← hxt, tauE_toE (hX ht)]
  exact ht

/-- **Theorem E with a constrained admissible set** (`dual_spectrum.tex`, `ds:E`(a), (b), repeated on a closed
`X ⊆ [T₀, ∞)`; `virasoro_two_level.tex`, `gt:2.4`): if no `g ∈ Ā` has `g_vac > 0` and `g ≥ 0` on `X`, there is a
crossing measure supported on `X` with `w_* ∈ L¹(ν)` and `∫ w_* dν ≤ C₀`. -/
theorem exists_crossingMeasure_of_not_feasible (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀)
    (hno : ∀ g, ¬ prob.IsFeasibleOn (cTilde / 12) X g) :
    ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν Xᶜ = 0 ∧ Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  have hne : X.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    obtain ⟨T, -, g, hg⟩ := prob.feasible_nonempty S.hc
    exact hno g ⟨hg.1, hg.2.1, by simp [hemp]⟩
  obtain ⟨μ, hmass, hζ, hcross⟩ := exists_measure_exact_on prob S hX hno (cutoffOfSet T₀ X)
    fun t ht => cutoffOfSet_toE ht
  obtain ⟨meas, hsupp, hint, hle⟩ := exists_crossingMeasure_of_limit_on prob S μ hmass hcross
  exact ⟨meas, hsupp hXc.measurableSet (cutoffOfSet T₀ X) (cutoffOfSet_nonneg T₀ X)
    (fun s hs h0 => tauE_mem_of_cutoffOfSet_eq_zero hXc hX hne hs h0) hζ, hint, hle⟩

/-- A crossing measure supported on `X ⊇ [τ, ∞)` excludes every functional feasible on `X`
(Lemma FW-X (1), `crossing_sum_rule.tex`; the converse of `exists_crossingMeasure_of_not_feasible`). -/
theorem not_feasible_of_crossingMeasure (prob : FixedWeightProblem) {a : ℝ}
    (ha : prob.totalShift ≤ a) (ha_pos : 0 < a) (meas : AdmissibleCrossingMeasure prob a)
    {X : Set ℝ} (hν : meas.ν Xᶜ = 0) {τ : ℝ} (hτ : Ici τ ⊆ X) (g : ℝ → ℝ) :
    ¬ prob.IsFeasibleOn a X g := by
  rintro ⟨hg, hvac, hnn⟩
  obtain ⟨-, hle⟩ := lemma_fwX_one_sided_unconditional prob ha ha_pos meas hg
    (T := τ) (fun t ht => hnn t (hτ ht))
  have hae : ∀ᵐ t ∂meas.ν, 0 ≤ g t := by
    have : ∀ᵐ t ∂meas.ν, t ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with t ht using hnn t (by simpa using ht)
  rw [restrict_Ici_eq_self meas] at hle
  have h0 : 0 ≤ ∫ t, g t ∂meas.ν := integral_nonneg_of_ae hae
  linarith

/-- **Constrained strong duality** (`dual_spectrum.tex`, `ds:E`, with `X` in place of `[τ, ∞)`): for a closed
`X ⊆ [T₀, ∞)` containing a ray `[τ, ∞)`, at every fixed weight `(w, Q)`, no `g ∈ Ā` has `g_vac > 0` and `g ≥ 0`
on `X` if and only if there is a crossing measure supported on `X` (with `∫ w_* dν ≤ C₀`). -/
theorem constrained_strong_duality (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀)
    (hray : ∃ τ, Ici τ ⊆ X) :
    (∀ g, ¬ prob.IsFeasibleOn (cTilde / 12) X g) ↔
      ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν Xᶜ = 0 ∧ Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
        ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  refine ⟨exists_crossingMeasure_of_not_feasible prob S hXc hX, ?_⟩
  rintro ⟨meas, hν, -, -⟩
  obtain ⟨τ, hτ⟩ := hray
  exact fun g => not_feasible_of_crossingMeasure prob S.ha S.ha_pos meas hν hτ g

/-- The two-level instance of `constrained_strong_duality`, `X = {t₁} ∪ [τ, ∞)`
(`virasoro_two_level.tex`, proof of `gt:2.4`, first bullet): no `g ∈ Ā` with `g_vac > 0`, `g(t₁) ≥ 0` and
`g ≥ 0` on `[τ, ∞)` if and only if there is a crossing measure supported on `{t₁} ∪ [τ, ∞)`. -/
theorem constrained_strong_duality_two_level (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {t₁ τ : ℝ} (ht₁ : T₀ ≤ t₁) (hτ : T₀ ≤ τ) :
    (∀ g, ¬ (TestClass prob (cTilde / 12) g ∧ 0 < prob.gVac (cTilde / 12) g ∧ 0 ≤ g t₁ ∧
        ∀ t, τ ≤ t → 0 ≤ g t)) ↔
      ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν ({t₁} ∪ Ici τ)ᶜ = 0 ∧ Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
        ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  have hXc : IsClosed ({t₁} ∪ Ici τ : Set ℝ) := isClosed_singleton.union isClosed_Ici
  have hX : ({t₁} ∪ Ici τ : Set ℝ) ⊆ Ici T₀ := by
    rintro t (rfl | ht)
    · exact ht₁
    · exact hτ.trans ht
  have hfe : ∀ g, prob.IsFeasibleOn (cTilde / 12) ({t₁} ∪ Ici τ) g ↔
      (TestClass prob (cTilde / 12) g ∧ 0 < prob.gVac (cTilde / 12) g ∧ 0 ≤ g t₁ ∧
        ∀ t, τ ≤ t → 0 ≤ g t) := fun g => by
    unfold FixedWeightProblem.IsFeasibleOn
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, h3 t₁ (Or.inl rfl), fun t ht => h3 t (Or.inr ht)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, h2, ?_⟩
      rintro t (rfl | ht)
      · exact h3
      · exact h4 t ht
  have := constrained_strong_duality prob S hXc hX ⟨τ, subset_union_right⟩
  simpa only [hfe] using this

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.constrained_strong_duality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.constrained_strong_duality

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.constrained_strong_duality_two_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.constrained_strong_duality_two_level

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.exists_crossingMeasure_of_not_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.exists_crossingMeasure_of_not_feasible

end FormalResearch.ModularBootstrap.FixedWeight
