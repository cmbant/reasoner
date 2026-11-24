module

public import FormalResearch.ModularBootstrap.TwoLevel.ConstrainedDuality
public import FormalResearch.ModularBootstrap.TwoLevel.TheoremTwoOne
public import FormalResearch.ModularBootstrap.FixedWeight.OptimalMeasure
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedFinal

/-!
# Corollary 2.4: crossing measures below the Clark--Airy curve (`virasoro_two_level.tex`, `gt:2.4`)

Notation: `c' = c̃`, `t_i = ξ̄ c' + A_i c'^{1/3}` (`levelTime A_i c'`), `a = c'/12`, `A_opt`, `A_2^*(A₁) = A2star A₁`.

* `eventually_not_feasibleOn_two_level`: for `A₁ < A_opt` and every `A₂ < A_2^*(A₁)`, for all large `c'` no
  `g ∈ Ā` has `g_vac > 0`, `g(t₁) ≥ 0` and `g ≥ 0` on `[t₂, ∞)` (second bullet of the proof; Theorem 2.1,
  `concrete_two_level_eventually`).
* `corollary_two_four_of_upper`: for `A₁ < A_opt`, `A₂ < A_2^*(A₁)` and `TheoremC15UpperInput prob`
  (`T_V ≤ T_* + O(1)`), for all large `c'` there is a crossing measure `ν` with
  `supp ν ⊆ {t₁} ∪ [t₂, ∞)`, `ν({t₁}) > 0`, `w_* ∈ L¹(ν)` and `∫ w_* dν ≤ C₀` (`β₀ = 1/2`); with
  `A_opt < A₂` this is the statement of `gt:2.4`, and `A₂ ≤ A_opt` is the "lower requirement" remark.
* `corollary_two_four`: the same at every `prob` with `prob.w = 1`, with `TheoremC15UpperInput` discharged by
  `Upper.Ramped.theoremC15UpperInput_prob`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight
open FormalResearch.ModularBootstrap.TipFront

/-- The level time `t = ξ̄ c' + A c'^{1/3}` of `gt:2.4`. -/
noncomputable def levelTime (A c' : ℝ) : ℝ := xiBar * c' + A * c' ^ ((1 : ℝ) / 3)

lemma levelTime_sub (A B c' : ℝ) :
    levelTime A c' - levelTime B c' = (A - B) * c' ^ ((1 : ℝ) / 3) := by
  unfold levelTime; ring

lemma levelTime_lt {A B c' : ℝ} (hc' : 0 < c') (h : A < B) : levelTime A c' < levelTime B c' := by
  have := levelTime_sub B A c'
  have h3 : 0 < c' ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc' _
  nlinarith

lemma levelTime_mono {A B c' : ℝ} (hc' : 0 ≤ c') (h : A ≤ B) : levelTime A c' ≤ levelTime B c' := by
  have := levelTime_sub B A c'
  have h3 : 0 ≤ c' ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hc' _
  nlinarith

lemma levelTime_TStar (c' : ℝ) : levelTime Aopt c' = TStar c' := rfl

/-- `levelTime A c' → ∞`, in the form `T ≤ levelTime A c'` eventually. -/
lemma eventually_le_levelTime (A T : ℝ) : ∀ᶠ c' : ℝ in atTop, T ≤ levelTime A c' := by
  have hxi : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
  filter_upwards [eventually_ge_atTop (((|A| + |T|) / xiBar + 1) ^ 3)] with c hc
  have hK : 0 ≤ (|A| + |T|) / xiBar := by positivity
  have hM1 : 1 ≤ (|A| + |T|) / xiBar + 1 := by linarith
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc
  set u : ℝ := c ^ ((1 : ℝ) / 3) with hu
  have hu3 : u ^ 3 = c := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hupos : 0 < u := Real.rpow_pos_of_pos hc0 _
  have hMu : (|A| + |T|) / xiBar + 1 ≤ u := by
    by_contra hlt
    push Not at hlt
    have : u ^ 3 < ((|A| + |T|) / xiBar + 1) ^ 3 := pow_lt_pow_left₀ hlt hupos.le (by norm_num)
    linarith
  have hu1 : 1 ≤ u := by linarith
  have hCx : (|A| + |T|) / xiBar < u := by linarith
  have hCx' : |A| + |T| < xiBar * u := by rwa [div_lt_iff₀ hxi, mul_comm] at hCx
  have h2 : xiBar * u ≤ xiBar * u ^ 2 := by
    have : u ≤ u ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this hxi.le
  have h3 : |A| + |T| ≤ xiBar * u ^ 2 := by linarith
  have h4 : 0 ≤ u * (xiBar * u ^ 2 - (|A| + |T|)) := mul_nonneg hupos.le (by linarith)
  have hA := neg_abs_le A
  have hT := le_abs_self T
  unfold levelTime
  rw [← hu, ← hu3]
  have hT1 : T ≤ |T| * u := by nlinarith [abs_nonneg T]
  have hA1 : -|A| * u ≤ A * u := mul_le_mul_of_nonneg_right hA hupos.le
  nlinarith [abs_nonneg T, abs_nonneg A]

/-- **Corollary 2.4, second bullet of the proof**: for `A₁ < A_opt` and `A₂ < A_2^*(A₁)`, for all large `c'`
no `g ∈ Ā` has `g_vac > 0`, `g(t₁) ≥ 0` and `g ≥ 0` on `[t₂, ∞)`; this is Theorem 2.1
(`concrete_two_level_eventually`). -/
theorem eventually_not_feasibleOn_two_level (prob : FixedWeightProblem) {A₁ A₂ : ℝ}
    (hA₁ : A₁ < Aopt) (hA₂ : A₂ < A2star A₁) :
    ∀ᶠ c' : ℝ in atTop, ∀ g,
      ¬ prob.IsFeasibleOn (c' / 12) ({levelTime A₁ c'} ∪ Ici (levelTime A₂ c')) g := by
  classical
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  set S : Set ℝ := {c' | ∃ g, prob.IsFeasibleOn (c' / 12)
    ({levelTime A₁ c'} ∪ Ici (levelTime A₂ c')) g} with hS
  have hfreq : ∃ᶠ c' : ℝ in atTop, c' ∈ S := hcon.mono fun c h => by
    push Not at h; exact h
  let p : Filter ℝ := atTop ⊓ 𝓟 S
  have hne : p.NeBot := Filter.frequently_iff_neBot.mp hfreq
  have : p.IsCountablyGenerated := inferInstance
  have hc' : Tendsto (fun c : ℝ => c) p atTop := inf_le_left
  have hmem : ∀ᶠ c : ℝ in p, c ∈ S :=
    Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall fun c hc => hc)
  let g : ℝ → ℝ → ℝ := fun c => if h : c ∈ S then Classical.choose h else 0
  have hg_spec : ∀ c (h : c ∈ S), prob.IsFeasibleOn (c / 12)
      ({levelTime A₁ c} ∪ Ici (levelTime A₂ c)) (g c) := fun c h => by
    simp only [g, h, dite_true]; exact Classical.choose_spec h
  have hg : ∀ᶠ c : ℝ in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c / 12) T (g c) := by
    filter_upwards [hmem] with c hc
    obtain ⟨h1, h2, h3⟩ := hg_spec c hc
    exact ⟨levelTime A₂ c, (show prob.IsFeasible (c / 12) (levelTime A₂ c) (g c) from
      ⟨h1, h2, fun t ht => h3 t (Or.inr ht)⟩).isWeaklyFeasible⟩
  have hpin : ∀ᶠ c : ℝ in p, 0 ≤ g c (levelTime A₁ c) := by
    filter_upwards [hmem] with c hc
    exact (hg_spec c hc).2.2 _ (Or.inl rfl)
  have hts : Tendsto (fun c : ℝ => (levelTime A₁ c - xiBar * c) / c ^ ((1 : ℝ) / 3)) p (nhds A₁) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hc'.eventually (eventually_gt_atTop (0 : ℝ))] with c hc
    have : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
    unfold levelTime
    field_simp
    ring
  set ε : ℝ := (A2star A₁ - A₂) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have h21 := concrete_two_level_eventually prob hc' g hg hA₁ (fun c => levelTime A₁ c) hts hpin
    ε hεpos
  have hpos : ∀ᶠ c : ℝ in p, 0 < c ∧ 0 ≤ levelTime A₂ c :=
    hc'.eventually ((eventually_gt_atTop (0 : ℝ)).and (eventually_le_levelTime A₂ 0))
  obtain ⟨c, hc1, ⟨hc0, hlt⟩, hcS⟩ := (h21.and (hpos.and hmem)).exists
  have hthr : leastThreshold (g c) ≤ levelTime A₂ c :=
    leastThreshold_le hlt fun t ht => (hg_spec c hcS).2.2 t (Or.inr ht)
  have h3 : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
  have h4 : (leastThreshold (g c) - xiBar * c) / c ^ ((1 : ℝ) / 3) ≤ A₂ := by
    rw [div_le_iff₀ h3]
    unfold levelTime at hthr
    linarith
  linarith

/-- The common eventual conditions in the proof of `corollary_two_four_of_upper` at `A_opt < A₂`. -/
private lemma corollary_two_four_core (prob : FixedWeightProblem)
    (hHi : TheoremC15UpperInput prob) {A₁ A₂ : ℝ}
    (hA₁ : A₁ < Aopt) (hA₂ : Aopt < A₂) (hA₂' : A₂ < A2star A₁) :
    ∀ᶠ c' : ℝ in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c' / 12),
      meas.ν ({levelTime A₁ c'} ∪ Ici (levelTime A₂ c'))ᶜ = 0 ∧ 0 < meas.ν {levelTime A₁ c'} ∧
      Integrable (wStar (c' / 12) (1 / 2)) meas.ν ∧
      ∫ t, wStar (c' / 12) (1 / 2) t ∂meas.ν ≤ dualC0 prob (c' / 12) (1 / 2) := by
  obtain ⟨c₂, D, hc₂, hD, hTV⟩ := hHi
  set T₀ : ℝ := max (t0Star prob.w (1 / 2)) 1 with hT₀
  have hgap : 0 < A₂ - Aopt := by linarith
  have hroot : ∀ᶠ c' : ℝ in atTop, D / (A₂ - Aopt) < c' ^ ((1 : ℝ) / 3) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually_gt_atTop _
  filter_upwards [eventually_ge_atTop c₂, hroot, eventually_le_levelTime A₁ T₀,
    eventually_not_feasibleOn_two_level prob hA₁ hA₂'] with c' hc₂c' hr ht₁ hno
  have hshift : 12 * prob.totalShift ≤ c' := (le_max_right _ _).trans (hc₂.trans hc₂c')
  have hc0 : 0 < c' := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans (hc₂.trans hc₂c'))
  have hT₀pos : 0 < T₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have S : DualSetupCore prob c' (1 / 2) T₀ :=
    ⟨hc0, hshift, by norm_num, le_rfl, le_max_left _ _, hT₀pos⟩
  have hlt : levelTime A₁ c' < levelTime A₂ c' := levelTime_lt hc0 (hA₁.trans hA₂)
  have hXc : IsClosed ({levelTime A₁ c'} ∪ Ici (levelTime A₂ c') : Set ℝ) :=
    isClosed_singleton.union isClosed_Ici
  have hX : ({levelTime A₁ c'} ∪ Ici (levelTime A₂ c') : Set ℝ) ⊆ Ici T₀ := by
    rintro t (rfl | ht)
    · exact ht₁
    · exact ht₁.trans (hlt.le.trans ht)
  obtain ⟨meas, hν, hint, hle⟩ := exists_crossingMeasure_of_not_feasible prob S hXc hX hno
  refine ⟨meas, hν, ?_, hint, hle⟩
  by_contra hzero
  have hz1 : meas.ν {levelTime A₁ c'} = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hzero)
  have hz : meas.ν (Iio (levelTime A₂ c')) = 0 := by
    refine measure_mono_null (fun t ht => ?_) (measure_union_null hν hz1)
    by_cases h : t ∈ ({levelTime A₁ c'} ∪ Ici (levelTime A₂ c') : Set ℝ)
    · rcases h with h | h
      · exact Or.inr h
      · exact absurd h (not_le.mpr ht)
    · exact Or.inl h
  have hτ : 0 < levelTime A₂ c' := lt_of_lt_of_le hT₀pos (ht₁.trans hlt.le)
  have hD1 := (Duality.proposition_D1 prob (cTilde := c') hshift hc0 hτ ⟨meas, hz⟩).2.1
  have hup := hTV hc₂c'
  have hdiff : levelTime A₂ c' - TStar c' = (A₂ - Aopt) * c' ^ ((1 : ℝ) / 3) :=
    levelTime_sub A₂ Aopt c'
  have : D < (A₂ - Aopt) * c' ^ ((1 : ℝ) / 3) := by
    rwa [div_lt_iff₀ hgap, mul_comm] at hr
  linarith

/-- **Corollary 2.4** (`virasoro_two_level.tex`, `gt:2.4`) at an arbitrary fixed weight `(w, Q)` given
`TheoremC15UpperInput prob`: for `A₁ < A_opt` and every `A₂ < A_2^*(A₁)`, for all large `c'` there is a crossing
measure `ν` supported on `{t₁} ∪ [t₂, ∞)` with `ν({t₁}) > 0`, `w_* ∈ L¹(ν)` and `∫ w_* dν ≤ C₀`
(`β₀ = 1/2`). For `A_opt < A₂` this is `gt:2.4`; `A₂ ≤ A_opt` is the remark on lower requirements
(an intermediate `Ã₂ ∈ (max{A₂, A_opt}, A_2^*(A₁))` is used, as in the TeX). -/
theorem corollary_two_four_of_upper (prob : FixedWeightProblem) (hHi : TheoremC15UpperInput prob)
    {A₁ A₂ : ℝ} (hA₁ : A₁ < Aopt) (hA₂ : A₂ < A2star A₁) :
    ∀ᶠ c' : ℝ in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c' / 12),
      meas.ν ({levelTime A₁ c'} ∪ Ici (levelTime A₂ c'))ᶜ = 0 ∧ 0 < meas.ν {levelTime A₁ c'} ∧
      Integrable (wStar (c' / 12) (1 / 2)) meas.ν ∧
      ∫ t, wStar (c' / 12) (1 / 2) t ∂meas.ν ≤ dualC0 prob (c' / 12) (1 / 2) := by
  have hopt := (A2star_mem_Ioo hA₁).1
  set Ã : ℝ := (max A₂ Aopt + A2star A₁) / 2 with hÃ
  have h1 : max A₂ Aopt < Ã := by
    have : max A₂ Aopt < A2star A₁ := max_lt hA₂ hopt
    rw [hÃ]; linarith
  have h2 : Ã < A2star A₁ := by
    have : max A₂ Aopt < A2star A₁ := max_lt hA₂ hopt
    rw [hÃ]; linarith
  have hAo : Aopt < Ã := (le_max_right _ _).trans_lt h1
  have hA2 : A₂ < Ã := (le_max_left _ _).trans_lt h1
  filter_upwards [corollary_two_four_core prob hHi hA₁ hAo h2, eventually_ge_atTop (0 : ℝ)]
    with c' ⟨meas, hν, hpos, hint, hle⟩ hc0
  refine ⟨meas, measure_mono_null (fun t ht => ?_) hν, hpos, hint, hle⟩
  rintro (h | h)
  · exact ht (Or.inl h)
  · exact ht (Or.inr ((levelTime_mono hc0 hA2.le).trans h))

/-- **Corollary 2.4, unconditional for weight-one problems** (`prob.w = 1`): `TheoremC15UpperInput prob` is
`Upper.Ramped.theoremC15UpperInput_prob`. -/
theorem corollary_two_four (prob : FixedWeightProblem) (hw : prob.w = 1)
    {A₁ A₂ : ℝ} (hA₁ : A₁ < Aopt) (hA₂ : A₂ < A2star A₁) :
    ∀ᶠ c' : ℝ in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c' / 12),
      meas.ν ({levelTime A₁ c'} ∪ Ici (levelTime A₂ c'))ᶜ = 0 ∧ 0 < meas.ν {levelTime A₁ c'} ∧
      Integrable (wStar (c' / 12) (1 / 2)) meas.ν ∧
      ∫ t, wStar (c' / 12) (1 / 2) t ∂meas.ν ≤ dualC0 prob (c' / 12) (1 / 2) :=
  corollary_two_four_of_upper prob (Upper.Ramped.theoremC15UpperInput_prob prob hw) hA₁ hA₂

/-- Non-vacuity of the open range of `gt:2.4`: `A_opt < A_2^*(A₁)` for `A₁ < A_opt`, so the interval
`A_opt < A₂ < A_2^*(A₁)` is nonempty. -/
theorem exists_A₂_between {A₁ : ℝ} (hA₁ : A₁ < Aopt) : ∃ A₂ : ℝ, Aopt < A₂ ∧ A₂ < A2star A₁ :=
  exists_between (A2star_mem_Ioo hA₁).1

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.eventually_not_feasibleOn_two_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eventually_not_feasibleOn_two_level

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.corollary_two_four_of_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corollary_two_four_of_upper

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.corollary_two_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corollary_two_four

end FormalResearch.ModularBootstrap.TwoLevel
