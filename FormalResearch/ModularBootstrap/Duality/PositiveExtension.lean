module

public import FormalResearch.ModularBootstrap.Duality.VagueCompactness
public import FormalResearch.ModularBootstrap.Duality.FiniteAtomic

/-!
# Positive extension with a moment bound (`ds:farkas`, Lemma `F_sep`)

`dual_spectrum.tex`, Lemma `F_sep` (`ds:farkas`) in the generality of a locally compact, second
countable Hausdorff space `Y` (the paper's "moreover" clause asks for metrizability of the one-point
compactification, which is this hypothesis; the existence clause is stated there for locally compact
Hausdorff `Y`, here second countability is assumed throughout).

Data: closed sets `X₀ ⊇ X₁ ⊇ ⋯`, `X = ⋂ X_j`; a continuous `w > 0` (`w_*`); continuous functions
`f_i` (`i ∈ I`, any index type of `Type`) with `f_i / w → 0` at infinity (`hdecay`: for every
`ε > 0`, `|f_i| ≤ ε w` on `X₀` outside a compact set; this is the paper's `f_i / w_* ∈ C₀(Y)`,
restricted to the common support, which is all the proof uses); prescribed moments `a_i`;
`C₀ > 0`; and the separation hypothesis (`ds:positive-moments`): for every `j`, finite subfamily
`u`, coefficients `λ` and `b ≥ 0`, `b + Σ λ_i f_i / w ≥ 0` on `X_j` forces `b C₀ + Σ λ_i a_i ≥ 0`.

* `farkas_separation`: there is a positive Radon measure `ν` with `ν (Xᶜ) = 0`, `∫ w dν ≤ C₀` and
  `∫ f_i dν = a_i` (`f_i ∈ L¹(ν)`).
* `farkas_finite`: for a finite subfamily `u` and a single `X_j` the measure can be taken finitely
  atomic with at most `|u| + 1` atoms (Carathéodory), and the separation hypothesis is needed only
  for that `j` and the subfamily `u`.
* `farkas_compactness`: any family of positive measures on the `X_j` with the budget and all moments
  has a vague limit (along any ultrafilter) with the same budget and moments on `X`; this needs only
  the decay hypothesis, not the separation hypothesis.

The proof differs from the paper's (Hahn–Banach on `C(Y ∪ {∞})` and Riesz): a finite subfamily is
solved exactly by finite-dimensional Farkas separation and Carathéodory
(`Duality.exists_atomic_exact`); the infinitely many constraints and the decreasing supports are
then handled by one vague limit along an ultrafilter on `Finset I × ℕ`
(`VagueCompactness`).  The symmetry clause of the paper (a symmetry of `Y` preserving all `ν_j`
preserves the limit) is not formalised.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Duality

section Atomic

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [T2Space Y]
  {ι : Type*} [Fintype ι]

/-- The finite atomic measure `Σ_k r_k δ_{y_k}` (weights `r_k ≥ 0`). -/
noncomputable def atomicMeasure (y : ι → Y) (r : ι → ℝ) : Measure Y :=
  ∑ k, ENNReal.ofReal (r k) • Measure.dirac (y k)

instance (y : ι → Y) (r : ι → ℝ) : IsFiniteMeasure (atomicMeasure y r) :=
  ⟨by simp [atomicMeasure, ENNReal.sum_lt_top]⟩

lemma integrable_atomic (y : ι → Y) (r : ι → ℝ) (g : Y → ℝ) : Integrable g (atomicMeasure y r) := by
  unfold atomicMeasure
  rw [integrable_finsetSum_measure]
  intro k _
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma integral_atomic (y : ι → Y) {r : ι → ℝ} (hr : ∀ k, 0 ≤ r k) (g : Y → ℝ) :
    ∫ x, g x ∂(atomicMeasure y r) = ∑ k, r k * g (y k) := by
  unfold atomicMeasure
  rw [integral_finsetSum_measure (fun k _ => (integrable_dirac (by simp)).smul_measure
    ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hr k), smul_eq_mul]

lemma lintegral_atomic (y : ι → Y) (r : ι → ℝ) (g : Y → ℝ≥0∞) :
    ∫⁻ x, g x ∂(atomicMeasure y r) = ∑ k, ENNReal.ofReal (r k) * g (y k) := by
  unfold atomicMeasure
  rw [lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

omit [TopologicalSpace Y] [BorelSpace Y] [T2Space Y] in
lemma atomic_null (y : ι → Y) (r : ι → ℝ) {S : Set Y} (hS : MeasurableSet S) (hy : ∀ k, y k ∉ S) :
    atomicMeasure y r S = 0 := by
  simp [atomicMeasure, Measure.dirac_apply' _ hS, hy]

end Atomic

section Farkas

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **Compactness and moment passage** (the general core of `ds:farkas`): a family `μ_p` of
measures on `Y`, indexed by `p ∈ 𝒥`, with weighted budget `∫ w dμ_p ≤ C₀`, eventually carried by
each `X_j`, and eventually satisfying the moment `∫ f_i dμ_p = a_i`, has along an ultrafilter `𝒰`
a vague limit carried by `⋂ X_j`, with the budget and all moments `∫ f_i dν = a_i`. -/
theorem exists_limit_measure {I : Type*} {𝒥 : Type*} (𝒰 : Ultrafilter 𝒥) (μ : 𝒥 → Measure Y)
    [∀ p, IsFiniteMeasureOnCompacts (μ p)] {w : Y → ℝ} (hw : Continuous w) (hwpos : ∀ y, 0 < w y)
    {C₀ : ℝ} (hC₀ : 0 < C₀) (hbμ : ∀ p, ∫⁻ y, ENNReal.ofReal (w y) ∂(μ p) ≤ ENNReal.ofReal C₀)
    {X : ℕ → Set Y} (hXc : ∀ j, IsClosed (X j))
    (hsupp : ∀ j₀, ∀ᶠ p in (𝒰 : Filter 𝒥), μ p (X j₀)ᶜ = 0)
    {f : I → Y → ℝ} (hf : ∀ i, Continuous (f i))
    (hdecay : ∀ i, ∀ ε > 0, ∃ K : Set Y, IsCompact K ∧ ∀ y ∈ X 0, y ∉ K → |f i y| ≤ ε * w y)
    {a : I → ℝ} (hmom : ∀ i, ∀ᶠ p in (𝒰 : Filter 𝒥), ∫ y, f i y ∂(μ p) = a i) :
    ∃ ν : Measure Y, IsFiniteMeasureOnCompacts ν ∧ IsVagueLimitAlong (𝒰 : Filter 𝒥) μ ν ∧
      ν (⋂ j, X j)ᶜ = 0 ∧ ∫⁻ y, ENNReal.ofReal (w y) ∂ν ≤ ENNReal.ofReal C₀ ∧
      ∀ i, Integrable (f i) ν ∧ ∫ y, f i y ∂ν = a i := by
  -- local boundedness of the masses
  have hbd : ∀ K : Set Y, IsCompact K → ∃ M : ℝ, ∀ p, (μ p K).toReal ≤ M := by
    intro K hK
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, fun p => by simp⟩
    obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hne hw.continuousOn
    set m := w y₀ with hm
    have hmpos : 0 < m := hwpos y₀
    refine ⟨C₀ / m, fun p => ?_⟩
    have h1 : ENNReal.ofReal m * μ p K ≤ ENNReal.ofReal C₀ := by
      calc ENNReal.ofReal m * μ p K = ∫⁻ y in K, ENNReal.ofReal m ∂(μ p) :=
            (setLIntegral_const K _).symm
        _ ≤ ∫⁻ y in K, ENNReal.ofReal (w y) ∂(μ p) :=
            setLIntegral_mono' hK.measurableSet fun y hy =>
              ENNReal.ofReal_le_ofReal (isMinOn_iff.1 hmin y hy)
        _ ≤ ∫⁻ y, ENNReal.ofReal (w y) ∂(μ p) := setLIntegral_le_lintegral _ _
        _ ≤ _ := hbμ p
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hmpos.le, ENNReal.toReal_ofReal hC₀.le] at h2
    rw [le_div_iff₀ hmpos]; linarith
  obtain ⟨ν, hν, hlim⟩ := exists_vagueLimitAlong μ hbd 𝒰
  have hbν : ∫⁻ y, ENNReal.ofReal (w y) ∂ν ≤ ENNReal.ofReal C₀ :=
    hlim.lintegral_le hw (fun y => (hwpos y).le) hC₀.le (Eventually.of_forall hbμ)
  have hνj : ∀ j, ν (X j)ᶜ = 0 := fun j =>
    hlim.measure_open_eq_zero (hXc j).isOpen_compl (hsupp j)
  have hμ0 : ∀ᶠ p in (𝒰 : Filter 𝒥), μ p (X 0)ᶜ = 0 := hsupp 0
  refine ⟨ν, hν, hlim, ?_, hbν, fun i => ⟨?_, ?_⟩⟩
  · rw [compl_iInter]; exact measure_iUnion_null hνj
  · obtain ⟨K, hK, hKd⟩ := hdecay i 1 one_pos
    refine integrable_of_decay (hνj 0) hw (fun y => (hwpos y).le)
      (lt_of_le_of_lt hbν ENNReal.ofReal_lt_top) (hf i) ⟨K, hK, fun y hy hyK => ?_⟩
    simpa using hKd y hy hyK
  · have h1 := hlim.tendsto_integral hμ0 (hνj 0) hw (fun y => (hwpos y).le) hC₀.le
      (Eventually.of_forall hbμ) hbν (hf i) (hdecay i)
    have h2 : Tendsto (fun p => ∫ y, f i y ∂(μ p)) (𝒰 : Filter 𝒥) (𝓝 (a i)) :=
      tendsto_const_nhds.congr' ((hmom i).mono fun p hp => hp.symm)
    exact tendsto_nhds_unique h1 h2

/-- **Compactness clause of `ds:farkas`**: a sequence of positive measures `ν_j`, carried by the
closed sets `X_j`, with `∫ w dν_j ≤ C₀` and all moments `∫ f_i dν_j = a_i`, has along every
ultrafilter `𝒰 ≤ atTop` a vague limit carried by `X = ⋂ X_j` with the same budget and moments.
Only the decay of `f_i / w`, not the separation hypothesis, is used. -/
theorem farkas_compactness {I : Type*} {w : Y → ℝ} (hw : Continuous w) (hwpos : ∀ y, 0 < w y)
    {C₀ : ℝ} (hC₀ : 0 < C₀) {X : ℕ → Set Y} (hXc : ∀ j, IsClosed (X j)) (hXa : Antitone X)
    {f : I → Y → ℝ} (hf : ∀ i, Continuous (f i))
    (hdecay : ∀ i, ∀ ε > 0, ∃ K : Set Y, IsCompact K ∧ ∀ y ∈ X 0, y ∉ K → |f i y| ≤ ε * w y)
    {a : I → ℝ} (ν : ℕ → Measure Y) [∀ j, IsFiniteMeasureOnCompacts (ν j)]
    (hsupp : ∀ j, ν j (X j)ᶜ = 0)
    (hbudget : ∀ j, ∫⁻ y, ENNReal.ofReal (w y) ∂(ν j) ≤ ENNReal.ofReal C₀)
    (hmom : ∀ j i, ∫ y, f i y ∂(ν j) = a i) (𝒰 : Ultrafilter ℕ) (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) :
    ∃ ν' : Measure Y, IsFiniteMeasureOnCompacts ν' ∧ IsVagueLimitAlong (𝒰 : Filter ℕ) ν ν' ∧
      ν' (⋂ j, X j)ᶜ = 0 ∧ ∫⁻ y, ENNReal.ofReal (w y) ∂ν' ≤ ENNReal.ofReal C₀ ∧
      ∀ i, Integrable (f i) ν' ∧ ∫ y, f i y ∂ν' = a i := by
  refine exists_limit_measure 𝒰 ν hw hwpos hC₀ hbudget hXc (fun j₀ => ?_) hf hdecay
    (fun i => Eventually.of_forall fun j => hmom j i)
  filter_upwards [h𝒰 (eventually_ge_atTop j₀)] with j hj
  exact measure_mono_null (compl_subset_compl.2 (hXa hj)) (hsupp j)

omit [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] in
/-- **Finite step of `ds:farkas`** (Carathéodory): for one closed set `X` and a finite subfamily
`u` of constraints satisfying the separation hypothesis, the moments `a_i` (`i ∈ u`) are attained
exactly by a positive combination of at most `|u| + 1` point masses `y_k ∈ X` with weighted budget
`Σ_k r_k w(y_k) ≤ C₀`. -/
theorem farkas_finite {I : Type} {X : Set Y} (hXc : IsClosed X) {w : Y → ℝ} (hw : Continuous w)
    (hwpos : ∀ y, 0 < w y) {C₀ : ℝ} (hC₀ : 0 < C₀) {f : I → Y → ℝ} (hf : ∀ i, Continuous (f i))
    (hdecay : ∀ i, ∀ ε > 0, ∃ K : Set Y, IsCompact K ∧ ∀ y ∈ X, y ∉ K → |f i y| ≤ ε * w y)
    {a : I → ℝ} (u : Finset I)
    (H : ∀ (lam : I → ℝ) (b : ℝ), 0 ≤ b →
      (∀ y ∈ X, 0 ≤ b + ∑ i ∈ u, lam i * (f i y / w y)) → 0 ≤ b * C₀ + ∑ i ∈ u, lam i * a i) :
    ∃ (ι : Type) (_ : Fintype ι) (y : ι → Y) (r : ι → ℝ), Fintype.card ι ≤ u.card + 1 ∧
      (∀ k, y k ∈ X) ∧ (∀ k, 0 ≤ r k) ∧ ∑ k, r k * w (y k) ≤ C₀ ∧
      ∀ i ∈ u, ∑ k, r k * f i (y k) = a i := by
  classical
  set Φ : Y → (u → ℝ) := fun y i => f i.1 y / w y with hΦdef
  have hΦ : Continuous Φ := continuous_pi fun i => (hf i.1).div hw fun y => (hwpos y).ne'
  have hdec : ∀ ε > 0, ∃ K : Set Y, IsCompact K ∧ ∀ y ∈ X, y ∉ K → ‖Φ y‖ ≤ ε := by
    intro ε hε
    choose K hK hKd using fun i : u => hdecay i.1 ε hε
    refine ⟨⋃ i : u, K i, isCompact_iUnion hK, fun y hy hyK => ?_⟩
    refine (pi_norm_le_iff_of_nonneg hε.le).2 fun i => ?_
    have hyi : y ∉ K i := fun h => hyK (mem_iUnion.2 ⟨i, h⟩)
    have := hKd i y hy hyi
    rw [Real.norm_eq_abs, hΦdef]
    simp only [abs_div, abs_of_pos (hwpos y)]
    rw [div_le_iff₀ (hwpos y)]
    exact this
  obtain ⟨ι, hι, y, c, hcard, hyX, hc, hsum, hmom⟩ := exists_atomic_exact Φ hΦ hXc hdec hC₀
    (fun i : u => a i.1) (fun l μ hμ hnn => by
      have := H (fun i => if h : i ∈ u then l ⟨i, h⟩ else 0) μ hμ (fun y hy => by
        have h1 := hnn y hy
        have e : ∑ i ∈ u, (fun i => if h : i ∈ u then l ⟨i, h⟩ else 0) i * (f i y / w y) =
            ∑ i : u, l i * Φ y i := by
          rw [← Finset.sum_coe_sort u]
          exact Finset.sum_congr rfl fun i _ => by simp [hΦdef]
        linarith)
      have e2 : ∑ i ∈ u, (fun i => if h : i ∈ u then l ⟨i, h⟩ else 0) i * a i =
          ∑ i : u, l i * a i.1 := by
        rw [← Finset.sum_coe_sort u]
        exact Finset.sum_congr rfl fun i _ => by simp
      linarith)
  refine ⟨ι, hι, y, fun k => c k / w (y k), by simpa using hcard, hyX,
    fun k => div_nonneg (hc k) (hwpos _).le, ?_, fun i hi => ?_⟩
  · calc ∑ k, c k / w (y k) * w (y k) = ∑ k, c k :=
          Finset.sum_congr rfl fun k _ => div_mul_cancel₀ _ (hwpos _).ne'
      _ ≤ C₀ := hsum
  · have := hmom ⟨i, hi⟩
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => by simp only [hΦdef]; field_simp

/-- **`ds:farkas`** (Lemma `F_sep`, positive extension with a moment bound), see the module
docstring for the hypotheses: under the separation hypothesis `H` for every `X_j`, there is a
positive Radon measure `ν` carried by `X = ⋂ X_j` with `∫ w dν ≤ C₀` and `f_i ∈ L¹(ν)`,
`∫ f_i dν = a_i` for every constraint `i`. -/
theorem farkas_separation {I : Type} {w : Y → ℝ} (hw : Continuous w) (hwpos : ∀ y, 0 < w y)
    {C₀ : ℝ} (hC₀ : 0 < C₀) {X : ℕ → Set Y} (hXc : ∀ j, IsClosed (X j)) (hXa : Antitone X)
    {f : I → Y → ℝ} (hf : ∀ i, Continuous (f i))
    (hdecay : ∀ i, ∀ ε > 0, ∃ K : Set Y, IsCompact K ∧ ∀ y ∈ X 0, y ∉ K → |f i y| ≤ ε * w y)
    {a : I → ℝ}
    (H : ∀ (j : ℕ) (u : Finset I) (lam : I → ℝ) (b : ℝ), 0 ≤ b →
      (∀ y ∈ X j, 0 ≤ b + ∑ i ∈ u, lam i * (f i y / w y)) → 0 ≤ b * C₀ + ∑ i ∈ u, lam i * a i) :
    ∃ ν : Measure Y, IsFiniteMeasureOnCompacts ν ∧ ν (⋂ j, X j)ᶜ = 0 ∧
      ∫⁻ y, ENNReal.ofReal (w y) ∂ν ≤ ENNReal.ofReal C₀ ∧
      ∀ i, Integrable (f i) ν ∧ ∫ y, f i y ∂ν = a i := by
  classical
  have hX0 : ∀ j, X j ⊆ X 0 := fun j => hXa (Nat.zero_le j)
  have hfin : ∀ p : Finset I × ℕ, ∃ (ι : Type) (_ : Fintype ι) (y : ι → Y) (r : ι → ℝ),
      Fintype.card ι ≤ p.1.card + 1 ∧ (∀ k, y k ∈ X p.2) ∧ (∀ k, 0 ≤ r k) ∧
      ∑ k, r k * w (y k) ≤ C₀ ∧ ∀ i ∈ p.1, ∑ k, r k * f i (y k) = a i := fun p =>
    farkas_finite (hXc p.2) hw hwpos hC₀ hf
      (fun i ε hε => by
        obtain ⟨K, hK, hKd⟩ := hdecay i ε hε
        exact ⟨K, hK, fun y hy hyK => hKd y (hX0 p.2 hy) hyK⟩) p.1 (fun lam b hb hnn => H p.2 p.1 lam b hb hnn)
  choose ι hι y r _ hyX hr hbud hmom using hfin
  let μ : Finset I × ℕ → Measure Y := fun p => by
    let _ := hι p
    exact atomicMeasure (y p) (r p)
  have hμfin : ∀ p, IsFiniteMeasureOnCompacts (μ p) := fun p => by
    have := hι p
    exact inferInstance
  have : ∀ p, IsFiniteMeasureOnCompacts (μ p) := hμfin
  have hbμ : ∀ p, ∫⁻ y', ENNReal.ofReal (w y') ∂(μ p) ≤ ENNReal.ofReal C₀ := by
    intro p
    let _ := hι p
    show ∫⁻ y', ENNReal.ofReal (w y') ∂(atomicMeasure (y p) (r p)) ≤ _
    rw [lintegral_atomic]
    calc ∑ k, ENNReal.ofReal (r p k) * ENNReal.ofReal (w (y p k))
        = ENNReal.ofReal (∑ k, r p k * w (y p k)) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun k _ => mul_nonneg (hr p k) (hwpos _).le]
          exact Finset.sum_congr rfl fun k _ => (ENNReal.ofReal_mul (hr p k)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hbud p)
  have hμsupp : ∀ p j₀, p.2 ≥ j₀ → μ p (X j₀)ᶜ = 0 := by
    intro p j₀ hp
    let _ := hι p
    refine atomic_null (y p) (r p) (hXc j₀).isOpen_compl.measurableSet fun k hk => ?_
    exact hk (hXa hp (hyX p k))
  have hdir : Nonempty (Finset I × ℕ) := ⟨(∅, 0)⟩
  let 𝒰 : Ultrafilter (Finset I × ℕ) := Ultrafilter.of atTop
  have h𝒰 : (𝒰 : Filter (Finset I × ℕ)) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨ν, hν, -, hsupp, hbudg, hmo⟩ := exists_limit_measure 𝒰 μ hw hwpos hC₀ hbμ hXc
    (fun j₀ => by
      filter_upwards [h𝒰 (eventually_ge_atTop ((∅ : Finset I), j₀))] with p hp
      exact hμsupp p j₀ hp.2) hf hdecay (a := a) (fun i => by
      filter_upwards [h𝒰 (eventually_ge_atTop (({i} : Finset I), 0))] with p hp
      let _ := hι p
      show ∫ y', f i y' ∂(atomicMeasure (y p) (r p)) = a i
      rw [integral_atomic (y p) (hr p)]
      exact hmom p i (hp.1 (Finset.mem_singleton_self i)))
  exact ⟨ν, hν, hsupp, hbudg, hmo⟩

end Farkas

/-- info: 'FormalResearch.ModularBootstrap.Duality.farkas_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.farkas_separation

/-- info: 'FormalResearch.ModularBootstrap.Duality.farkas_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.farkas_finite

/-- info: 'FormalResearch.ModularBootstrap.Duality.farkas_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.farkas_compactness

end FormalResearch.ModularBootstrap.Duality
