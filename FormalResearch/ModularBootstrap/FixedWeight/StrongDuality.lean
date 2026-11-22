module

public import FormalResearch.ModularBootstrap.FixedWeight.MomentProblem
public import FormalResearch.ModularBootstrap.Duality.Compactness
public import FormalResearch.ModularBootstrap.Duality.LimitMeasure
public import FormalResearch.ModularBootstrap.Duality.StrongDuality

/-!
# Strong Duality with Attainment at Fixed Weight `(w, Q)` (Theorem E of `dual_spectrum.tex`)

Generalises `Duality.Coordinates`, `Duality.Compactness`, `Duality.LimitMeasure`, and
`Duality.StrongDuality` (`CFT/modular_bootstrap/paper/dual_spectrum.tex`, Theorem E, `ds:E`)
to every fixed-weight problem `prob : FixedWeightProblem` with `c̃ > 0`, `c̃ ≥ 12 S`, and
`T_V(c̃) > 0` (`DualSetup prob cTilde β₀ T₀`):

* `theorem_E_b`: for `T₀ ≤ T < T_V(c̃)` there is a crossing measure `ν_T` supported on `[T, ∞)`
  with `∫ w_* dν_T ≤ C₀`.
* `theorem_E_c`: there is a crossing measure `ν_*` supported on `[T_V, ∞)` with `∫ w_* dν_* ≤ C₀`
  and `min supp ν_* = T_V(c̃)`.
* `theorem_E`: both, and `T_V(c̃) = max {τ > 0 : a crossing measure at gap τ exists}` (`IsGreatest`).
* `virasoro_theorem_E`: re-derives `Duality.theorem_E` as an instance of `FixedWeight.theorem_E`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real NNReal BoundedContinuousFunction

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality

/-! ### Section 1: Continuous test functions `Ξ_β^{(w)} / w_*` on `[0, 1]` -/

/-- The function `s ↦ Ξ_β^{(w)}(τ s) / w_*(τ s)` for `s > 0` and `0` at `s = 0`. -/
noncomputable def Ftilde (w : ℕ) (a β₀ T₀ β : ℝ) (s : Ecoord) : ℝ :=
  if s.1 = 0 then 0 else thermalDiff w β (tauE T₀ s) / wStar a β₀ (tauE T₀ s)

lemma Ftilde_toE (w : ℕ) (a β₀ T₀ β : ℝ) {t : ℝ} (ht : T₀ ≤ t) :
    Ftilde w a β₀ T₀ β (toE T₀ t) = thermalDiff w β t / wStar a β₀ t := by
  have := (toE_pos ht).ne'
  simp [Ftilde, this, tauE_toE ht]

lemma continuous_Ftilde {w : ℕ} {a β₀ T₀ β : ℝ}
    (ha : 0 < a) (hβ₀ : 0 < β₀) (hT₀ : 0 < T₀) (hβ : 0 < β) :
    Continuous (Ftilde w a β₀ T₀ β) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  by_cases h0 : s₀.1 = 0
  · have hF0 : Ftilde w a β₀ T₀ β s₀ = 0 := by simp [Ftilde, h0]
    rw [ContinuousAt, hF0, Metric.tendsto_nhds]
    intro ε hε
    have hlim := tendsto_thermalDiff_div_wStar (w := w) (a := a) ha.le hβ₀ hβ
    rw [Metric.tendsto_atTop] at hlim
    obtain ⟨R, hR⟩ := hlim ε hε
    let R' : ℝ := max (R - T₀ + 1) 1
    have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hnhd : {s : Ecoord | s.1 < R'⁻¹} ∈ 𝓝 s₀ := by
      refine IsOpen.mem_nhds (isOpen_lt continuous_subtype_val continuous_const) ?_
      simp [h0, hR'pos]
    filter_upwards [hnhd] with s hs
    by_cases hs0 : s.1 = 0
    · simp [Ftilde, hs0, hε]
    · have hspos : 0 < s.1 := lt_of_le_of_ne s.2.1 (Ne.symm hs0)
      have h1 : R' < s.1⁻¹ := by rw [lt_inv_comm₀ hR'pos hspos]; exact hs
      have h2 : R ≤ tauE T₀ s := by
        unfold tauE
        have : R - T₀ + 1 ≤ R' := le_max_left _ _
        linarith
      have := hR (tauE T₀ s) h2
      rw [Real.dist_eq, sub_zero] at this
      have hF : Ftilde w a β₀ T₀ β s = thermalDiff w β (tauE T₀ s) / wStar a β₀ (tauE T₀ s) := by
        simp [Ftilde, hs0]
      rw [Real.dist_eq, sub_zero, hF]
      exact this
  · have hpos : 0 < s₀.1 := lt_of_le_of_ne s₀.2.1 (Ne.symm h0)
    have hτ := continuousAt_tauE T₀ hpos
    have hT : 0 < tauE T₀ s₀ := lt_of_lt_of_le hT₀ (tauE_ge hpos)
    have hg : ContinuousAt (fun t => thermalDiff w β t / wStar a β₀ t) (tauE T₀ s₀) := by
      have hw : ContinuousAt (wStar a β₀) (tauE T₀ s₀) :=
        (continuousOn_wStar ha).continuousAt (Ici_mem_nhds hT)
      refine ContinuousAt.div (by unfold thermalDiff; fun_prop) hw ?_
      exact (wStar_pos ha.le hβ₀ hT.le).ne'
    have hcomp : ContinuousAt (fun s => thermalDiff w β (tauE T₀ s) / wStar a β₀ (tauE T₀ s)) s₀ :=
      hg.comp hτ
    refine hcomp.congr ?_
    have : {s : Ecoord | s.1 ≠ 0} ∈ 𝓝 s₀ :=
      (isOpen_ne_fun continuous_subtype_val continuous_const).mem_nhds h0
    filter_upwards [this] with s hs
    simp [Ftilde, hs]

/-- `Ftilde` as a bounded continuous function on `[0, 1]`. -/
noncomputable def FtildeB {w : ℕ} {a β₀ T₀ β : ℝ}
    (ha : 0 < a) (hβ₀ : 0 < β₀) (hT₀ : 0 < T₀) (hβ : 0 < β) :
    Ecoord →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨Ftilde w a β₀ T₀ β, continuous_Ftilde ha hβ₀ hT₀ hβ⟩

/-! ### Section 2: Compactness and transport to crossing measures -/

/-- **Theorem E(a)+(b), exactness on `[0, 1]`** at fixed weight `(w, Q)`. -/
theorem exists_measure_exact (prob : FixedWeightProblem) {cTilde β₀ T₀ T : ℝ}
    (S : DualSetup prob cTilde β₀ T₀) (hT₀T : T₀ ≤ T) (hTV : T < prob.T_V cTilde) :
    ∃ μ : FiniteMeasure Ecoord, (μ.mass : ℝ) ≤ dualC0 prob (cTilde / 12) β₀ ∧
      ∫ x, zetaB T₀ T x ∂(μ : Measure Ecoord) = 0 ∧
      ∀ (β : ℝ) (hβ : 0 < β),
        ∫ x, FtildeB (w := prob.w) (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀)
          S.ha_pos S.hβ₀ S.hT₀pos hβ x ∂(μ : Measure Ecoord) =
          crossingRHS prob (cTilde / 12) β := by
  have ha0 := S.ha_pos
  have hC0 : 0 < dualC0 prob (cTilde / 12) β₀ :=
    dualC0_pos prob ha0 S.hβ₀ (by linarith [S.hβ₀2])
  set C : ℝ≥0 := (dualC0 prob (cTilde / 12) β₀).toNNReal with hC
  have hCcoe : (C : ℝ) = dualC0 prob (cTilde / 12) β₀ := Real.coe_toNNReal _ hC0.le
  obtain ⟨μ, hμK, hμ⟩ := exists_exact_of_approx (isCompact_Kset C (zetaB T₀ T))
    (isClosed_Kset C (zetaB T₀ T))
    (J := {β : ℝ // 0 < β})
    (fun j => FtildeB (w := prob.w) (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀)
      ha0 S.hβ₀ S.hT₀pos j.2)
    (fun j => crossingRHS prob (cTilde / 12) j.1) (fun u n => by
      obtain ⟨N, t, c, ht, hc, hs, hd⟩ := exists_atomic_approx prob S hT₀T hTV
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
      · show ∫ x, zetaB T₀ T x ∂(atomMeasure T₀ t c) = 0
        rw [hint]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [zetaB_toE hT₀T (ht k), mul_zero]
      · show |∫ x, _ ∂(atomMeasure T₀ t c) - _| ≤ _
        rw [hint]
        have := hd j.1 (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
        refine le_of_lt ?_
        convert this using 3
        refine Finset.sum_congr rfl fun k _ => ?_
        have e : (FtildeB (w := prob.w) (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀)
            ha0 S.hβ₀ S.hT₀pos j.2) (toE T₀ (t k)) =
            Ftilde prob.w (cTilde / 12) β₀ T₀ j.1 (toE T₀ (t k)) := rfl
        rw [e, Ftilde_toE _ _ _ _ _ (hT₀T.trans (ht k))])
  refine ⟨μ, ?_, hμK.2, fun β hβ => hμ ⟨β, hβ⟩⟩
  have := hμK.1
  rw [← hCcoe]; exact_mod_cast this

/-- **Theorem E(b), transport** at fixed weight `(w, Q)`. -/
theorem exists_crossingMeasure_of_limit (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetup prob cTilde β₀ T₀) (μ : FiniteMeasure Ecoord)
    (hmass : (μ.mass : ℝ) ≤ dualC0 prob (cTilde / 12) β₀)
    (hcross : ∀ (β : ℝ) (hβ : 0 < β),
      ∫ x, FtildeB (w := prob.w) (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀)
        S.ha_pos S.hβ₀ S.hT₀pos hβ x ∂(μ : Measure Ecoord) =
        crossingRHS prob (cTilde / 12) β) :
    ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      (∀ T, T₀ ≤ T → ∫ x, zetaB T₀ T x ∂(μ : Measure Ecoord) = 0 → meas.ν (Iio T) = 0) ∧
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
            crossing := fun {β} hβ => ?_ }, fun T hT hζ => ?_, hw_int, ?_⟩
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
  · exact pullMeasure_Iio_eq_zero (a := a) (β₀ := β₀) (μ : Measure Ecoord) hT hζ
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

/-! ### Section 3: Theorem E (`ds:E`) for every `(w, Q)` -/

/-- **Theorem E(b)** (`dual_spectrum.tex`, `ds:E`) for every fixed weight `(w, Q)`:
for `T₀ ≤ T < T_V(c̃)` there is a crossing measure supported on `[T, ∞)` with `∫ w_* dν ≤ C₀`. -/
theorem theorem_E_b (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetup prob cTilde β₀ T₀) {T : ℝ} (hT₀T : T₀ ≤ T) (hTV : T < prob.T_V cTilde) :
    ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (Iio T) = 0 ∧ Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  obtain ⟨μ, hmass, hζ, hcross⟩ := exists_measure_exact prob S hT₀T hTV
  obtain ⟨meas, hsupp, hint, hle⟩ := exists_crossingMeasure_of_limit prob S μ hmass hcross
  exact ⟨meas, hsupp T hT₀T hζ, hint, hle⟩

/-- The crossing exactness condition on measures on `[0, 1]` is weakly closed. -/
lemma isClosed_crossing_exact (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetup prob cTilde β₀ T₀) :
    IsClosed {μ : FiniteMeasure Ecoord | ∀ (β : ℝ) (hβ : 0 < β),
      ∫ x, FtildeB (w := prob.w) (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀)
        S.ha_pos S.hβ₀ S.hT₀pos hβ x ∂(μ : Measure Ecoord) =
        crossingRHS prob (cTilde / 12) β} := by
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun β => isClosed_iInter fun hβ => ?_
  exact isClosed_eq (continuous_integral_finiteMeasure _) continuous_const

/-- **Theorem E(c)** (`dual_spectrum.tex`, `ds:E`) for every fixed weight `(w, Q)`:
the limit measure `ν_*` along `T_n ↑ T_V` is a crossing measure supported on `[T_V, ∞)`,
with `∫ w_* dν_* ≤ C₀` and `min supp ν_* = T_V`. -/
theorem theorem_E_c (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetup prob cTilde β₀ T₀) :
    ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (Iio (prob.T_V cTilde)) = 0 ∧
      (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (prob.T_V cTilde + ε))) ∧
      Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  set TV := prob.T_V cTilde with hTVdef
  have hTV0 : T₀ < TV := S.hT₀V
  have hC0 : 0 < dualC0 prob (cTilde / 12) β₀ :=
    dualC0_pos prob S.ha_pos S.hβ₀ (by linarith [S.hβ₀2])
  set C : ℝ≥0 := (dualC0 prob (cTilde / 12) β₀).toNNReal with hC
  have hCcoe : (C : ℝ) = dualC0 prob (cTilde / 12) β₀ := Real.coe_toNNReal _ hC0.le
  let Tn : ℕ → ℝ := fun n => TV - (TV - T₀) / (n + 2)
  have hTn0 : ∀ n, T₀ ≤ Tn n := fun n => by
    have : (TV - T₀) / (n + 2) ≤ TV - T₀ :=
      div_le_self (by linarith) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    show T₀ ≤ TV - (TV - T₀) / (n + 2); linarith
  have hTnV : ∀ n, Tn n < TV := fun n => by
    have : 0 < (TV - T₀) / (n + 2) :=
      div_pos (by linarith) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    show TV - (TV - T₀) / (n + 2) < TV; linarith
  have hTnmono : ∀ n, Tn n ≤ Tn (n + 1) := fun n => by
    show TV - (TV - T₀) / (n + 2) ≤ TV - (TV - T₀) / ((n + 1 : ℕ) + 2)
    have h1 : (TV - T₀) / (((n + 1 : ℕ) : ℝ) + 2) ≤ (TV - T₀) / (n + 2) := by
      refine div_le_div_of_nonneg_left (by linarith)
        (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) ?_
      push_cast; linarith
    linarith
  let A : ℕ → Set (FiniteMeasure Ecoord) := fun n =>
    Kset C (zetaB T₀ (Tn n)) ∩ {μ : FiniteMeasure Ecoord | ∀ (β : ℝ) (hβ : 0 < β),
      ∫ x, FtildeB (w := prob.w) (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀)
        S.ha_pos S.hβ₀ S.hT₀pos hβ x ∂(μ : Measure Ecoord) =
        crossingRHS prob (cTilde / 12) β}
  have hAcl : ∀ n, IsClosed (A n) := fun n =>
    (isClosed_Kset C _).inter (isClosed_crossing_exact prob S)
  have hA0 : IsCompact (A 0) :=
    (isCompact_Kset C _).inter_right (isClosed_crossing_exact prob S)
  have hAne : ∀ n, (A n).Nonempty := fun n => by
    obtain ⟨μ, hmass, hζ, hcross⟩ := exists_measure_exact prob S (hTn0 n) (hTnV n)
    refine ⟨μ, ⟨?_, hζ⟩, hcross⟩
    show μ.mass ≤ C
    rw [← NNReal.coe_le_coe, hCcoe]; exact hmass
  have hAmono : ∀ n, A (n + 1) ⊆ A n := by
    rintro n μ ⟨⟨hm, hζ⟩, hc⟩
    refine ⟨⟨hm, ?_⟩, hc⟩
    have h1 : ∫ x, zetaB T₀ (Tn n) x ∂(μ : Measure Ecoord) ≤
        ∫ x, zetaB T₀ (Tn (n + 1)) x ∂(μ : Measure Ecoord) :=
      integral_mono (BoundedContinuousFunction.integrable _ _)
        (BoundedContinuousFunction.integrable _ _) fun s => zetaB_mono (hTn0 n) (hTnmono n) s
    have h2 : 0 ≤ ∫ x, zetaB T₀ (Tn n) x ∂(μ : Measure Ecoord) :=
      integral_nonneg fun s => zetaB_nonneg _ _ s
    show ∫ x, zetaB T₀ (Tn n) x ∂(μ : Measure Ecoord) = 0
    have : ∫ x, zetaB T₀ (Tn (n + 1)) x ∂(μ : Measure Ecoord) = 0 := hζ
    linarith
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed A hAmono
    hAne hA0 hAcl
  rw [mem_iInter] at hμ
  obtain ⟨⟨hm0, _⟩, hcross⟩ := hμ 0
  have hmass : (μ.mass : ℝ) ≤ dualC0 prob (cTilde / 12) β₀ := by
    rw [← hCcoe]; exact_mod_cast hm0
  obtain ⟨meas, hsupp, hint, hle⟩ := exists_crossingMeasure_of_limit prob S μ hmass hcross
  have hn : ∀ n, meas.ν (Iio (Tn n)) = 0 := fun n =>
    hsupp (Tn n) (hTn0 n) ((hμ n).1.2)
  have hTVzero : meas.ν (Iio TV) = 0 := by
    refine measure_mono_null (fun t ht => ?_) (measure_iUnion_null hn)
    simp only [mem_Iio] at ht
    obtain ⟨n, hn'⟩ := exists_nat_gt ((TV - T₀) / (TV - t))
    have hpos : 0 < TV - t := by linarith
    have : (TV - T₀) / (n + 2) < TV - t := by
      rw [div_lt_iff₀ (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)]
      have := (div_lt_iff₀ hpos).mp hn'
      nlinarith
    refine mem_iUnion.mpr ⟨n, ?_⟩
    show t < TV - (TV - T₀) / (n + 2)
    linarith
  refine ⟨meas, hTVzero, fun ε hε => ?_, hint, hle⟩
  by_contra hcon
  have hz : meas.ν (Iio (TV + ε)) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hcon)
  obtain ⟨_, hle', _⟩ := Duality.proposition_D1 prob (cTilde := cTilde) (τ := TV + ε)
    S.hc S.hc_pos (by linarith [S.hT₀pos]) ⟨meas, hz⟩
  linarith

/-- **Theorem E** (`dual_spectrum.tex`, `ds:E`) for every fixed weight `(w, Q)` with `c̃ > 0`,
`c̃ ≥ 12 S`, and `T_V(c̃) > 0` (packaged as `DualSetup prob cTilde β₀ T₀`):
* (b) for `T₀ ≤ T < T_V(c̃)` there is a crossing measure `ν_T` supported on `[T, ∞)` with
  `∫ w_* dν_T ≤ C₀`;
* (c) there is a crossing measure `ν_*` supported on `[T_V, ∞)` with `∫ w_* dν_* ≤ C₀` and
  `min supp ν_* = T_V(c̃)`;
* hence `T_V(c̃) = max {τ > 0 : a crossing measure at gap τ exists}` (`IsGreatest`). -/
theorem theorem_E (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetup prob cTilde β₀ T₀) :
    (∀ T, T₀ ≤ T → T < prob.T_V cTilde →
      ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν (Iio T) = 0 ∧ Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
        ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀) ∧
    (∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (Iio (prob.T_V cTilde)) = 0 ∧
      (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (prob.T_V cTilde + ε))) ∧
      Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀) ∧
    IsGreatest {τ : ℝ | 0 < τ ∧ HasCrossingMeasureAt prob (cTilde / 12) τ}
      (prob.T_V cTilde) := by
  have hc := theorem_E_c prob S
  refine ⟨fun T hT hTV => theorem_E_b prob S hT hTV, hc, ?_, ?_⟩
  · obtain ⟨meas, h1, _⟩ := hc
    exact ⟨lt_trans S.hT₀pos S.hT₀V, meas, h1⟩
  · rintro τ ⟨hτ, hex⟩
    exact (Duality.proposition_D1 prob (cTilde := cTilde) (τ := τ) S.hc S.hc_pos hτ hex).2.1

/-- Spinless Virasoro instance of `theorem_E`, recovering `Duality.theorem_E`. -/
theorem virasoro_theorem_E {cTilde β₀ T₀ : ℝ} (S : Duality.DualSetup cTilde β₀ T₀) :
    (∀ T, T₀ ≤ T → T < virasoroProblem.T_V cTilde →
      ∃ meas : AdmissibleCrossingMeasure virasoroProblem (cTilde / 12),
        meas.ν (Iio T) = 0 ∧ Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
        ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ Duality.dualC0 (cTilde / 12) β₀) ∧
    (∃ meas : AdmissibleCrossingMeasure virasoroProblem (cTilde / 12),
      meas.ν (Iio (virasoroProblem.T_V cTilde)) = 0 ∧
      (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (virasoroProblem.T_V cTilde + ε))) ∧
      Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ Duality.dualC0 (cTilde / 12) β₀) ∧
    IsGreatest {τ : ℝ | 0 < τ ∧ HasCrossingMeasureAt virasoroProblem (cTilde / 12) τ}
      (virasoroProblem.T_V cTilde) := by
  simpa only [dualC0_virasoro] using theorem_E virasoroProblem (DualSetup.of_virasoro S)

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.theorem_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.theorem_E

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.theorem_E_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.theorem_E_b

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.theorem_E_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.theorem_E_c

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.virasoro_theorem_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.virasoro_theorem_E

end FormalResearch.ModularBootstrap.FixedWeight