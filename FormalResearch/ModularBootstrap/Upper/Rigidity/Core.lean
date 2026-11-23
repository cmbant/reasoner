module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Design

/-!
# Measure-level core of the rigidity proofs

Utilities and the basic inequality (Step 1 of `sr:Sigma`):

* `cutoff A B`: the piecewise-linear cutoff, `= 1` on `[A, B]`, supported in `[A-1, B+1]`;
* `abs_integral_le_of_zero_outside`, `const_mul_measure_le_integral`: integral estimates;
* `basic_inequality`: for a vague limit `ν` of `μ_j` along an ultrafilter and a design test
  `T : DesignTest μ D`, `∫ cutoff A B · W_𝔇 dν ≤ V_𝔇` once `cutoff = 1` on `[u_f - 1, a₁ + 1]`
  (the cutoff version of `(I)`, `sr:eI`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.Special

/-- Piecewise-linear cutoff: `1` on `[A, B]`, `0` outside `(A - 1, B + 1)`, values in `[0, 1]`. -/
noncomputable def cutoff (A B : ℝ) (u : ℝ) : ℝ :=
  max 0 (min 1 (min (u - A + 1) (B + 1 - u)))

lemma cutoff_continuous (A B : ℝ) : Continuous (cutoff A B) := by
  unfold cutoff; fun_prop

lemma cutoff_nonneg (A B u : ℝ) : 0 ≤ cutoff A B u := le_max_left _ _

lemma cutoff_le_one (A B u : ℝ) : cutoff A B u ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma cutoff_eq_one {A B u : ℝ} (h1 : A ≤ u) (h2 : u ≤ B) : cutoff A B u = 1 := by
  unfold cutoff
  have : min 1 (min (u - A + 1) (B + 1 - u)) = 1 :=
    min_eq_left (le_min (by linarith) (by linarith))
  rw [this]; exact max_eq_right zero_le_one

lemma cutoff_eq_zero {A B u : ℝ} (h : u ≤ A - 1 ∨ B + 1 ≤ u) : cutoff A B u = 0 := by
  unfold cutoff
  rcases h with h | h
  · have : min 1 (min (u - A + 1) (B + 1 - u)) ≤ 0 :=
      (min_le_right _ _).trans ((min_le_left _ _).trans (by linarith))
    exact max_eq_left this
  · have : min 1 (min (u - A + 1) (B + 1 - u)) ≤ 0 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith))
    exact max_eq_left this

lemma cutoff_hasCompactSupport (A B : ℝ) : HasCompactSupport (cutoff A B) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := A - 1) (b := B + 1)) fun x hx => ?_
  refine cutoff_eq_zero ?_
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · exact Or.inl h.le
  · exact Or.inr h.le

lemma HasCompactSupport.mul_cutoff {g : ℝ → ℝ} (A B : ℝ) :
    HasCompactSupport (fun u => cutoff A B u * g u) :=
  (cutoff_hasCompactSupport A B).mul_right

/-- `|∫ f dμ| ≤ B μ(K)` if `f` vanishes off the compact `K` and `|f| ≤ B` on `K`. -/
lemma abs_integral_le_of_zero_outside {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {f : ℝ → ℝ}
    {K : Set ℝ} (hK : IsCompact K) (hzero : ∀ x ∉ K, f x = 0) {B : ℝ}
    (hB : ∀ x ∈ K, |f x| ≤ B) : |∫ u, f u ∂μ| ≤ B * (μ K).toReal := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := K) (f := f) hK.measure_lt_top
    (C := B) (fun x hx => by simpa [Real.norm_eq_abs] using hB x hx)
  simpa [Real.norm_eq_abs, Measure.real] using this

/-- A lower bound `f ≥ c` on a measurable set `S` and `f ≥ 0` almost everywhere off `S` give
`c μ(S) ≤ ∫ f dμ` (`c` of either sign). -/
lemma const_mul_measure_le_integral {μ : Measure ℝ} {f : ℝ → ℝ} (hf : Integrable f μ)
    {S : Set ℝ} (hS : MeasurableSet S) (hSfin : μ S < ∞) {c : ℝ}
    (h1 : ∀ u ∈ S, c ≤ f u) (h0 : ∀ᵐ u ∂μ, u ∉ S → 0 ≤ f u) :
    c * (μ S).toReal ≤ ∫ u, f u ∂μ := by
  have hg : Integrable (S.indicator fun _ => c) μ := (integrable_indicator_iff hS).2
    (integrableOn_const hSfin.ne)
  have := integral_mono_ae hg hf (by
    filter_upwards [h0] with u hu
    by_cases hu' : u ∈ S
    · simpa [Set.indicator_of_mem hu'] using h1 u hu'
    · simpa [Set.indicator_of_notMem hu'] using hu hu')
  rwa [integral_indicator_const _ hS, smul_eq_mul, Measure.real, mul_comm] at this

lemma ae_le_of_supp {μ : Measure ℝ} {s : ℝ} (h : μ (Ioi s) = 0) : ∀ᵐ u ∂μ, u ≤ s := by
  have := measure_eq_zero_iff_ae_notMem.1 h
  filter_upwards [this] with u hu
  exact not_lt.mp hu

/-- The spectral measures `μ_j` live on `u ≤ s_j = u(τ_j)`, with (Gap) `limsup s_j ≤ a₁`. -/
structure SpectralData where
  μ : ℕ → Measure ℝ
  s : ℕ → ℝ
  locFin : ∀ j, IsLocallyFiniteMeasure (μ j)
  supp : ∀ j, μ j (Ioi (s j)) = 0
  gap : ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop, s j ≤ airyZero 1 + δ

attribute [instance] SpectralData.locFin

namespace SpectralData

variable (S : SpectralData)

lemma ae_le (j : ℕ) : ∀ᵐ u ∂(S.μ j), u ≤ S.s j := ae_le_of_supp (S.supp j)

lemma ae_le_of_gap {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ j in atTop, ∀ᵐ u ∂(S.μ j), u ≤ airyZero 1 + δ := by
  filter_upwards [S.gap δ hδ] with j hj
  filter_upwards [S.ae_le j] with u hu using hu.trans hj

end SpectralData

/-- **Basic inequality** (Step 1 of `sr:Sigma`, `(I)` of `sr:eI` in cutoff form).  If `ν` is a vague
limit of the `μ_j` along `𝒰 ≤ atTop` and `μ_j` has locally bounded masses, then for every design
test `T` and every cutoff equal to `1` on `[u_f - 1, a₁ + 1]`:
`∫ cutoff · W_𝔇 dν ≤ V_𝔇`. -/
theorem basic_inequality (S : SpectralData) (hbd : LocallyBounded S.μ) {𝒰 : Ultrafilter ℕ}
    (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) {ν : Measure ℝ} (hν : IsVagueLimit 𝒰 S.μ ν)
    {D : Window} (T : DesignTest S.μ D) {A B : ℝ} (hA : A ≤ D.uF - 1) (hB : airyZero 1 + 1 ≤ B) :
    ∫ u, cutoff A B u * D.W u ∂ν ≤ D.V := by
  set K : Set ℝ := Icc (A - 1) (B + 1) with hKdef
  have hKc : IsCompact K := isCompact_Icc
  obtain ⟨M, hM⟩ := hbd K hKc
  set M' : ℝ := max M 0 with hM'
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.1 T.window_limit) K hKc
  have key : ∀ ε : ℝ, 0 < ε → ∫ u, cutoff A B u * D.W u ∂ν ≤ D.V + ε * (1 + M') := by
    intro ε hε
    have hev : ∀ᶠ j in atTop, ∫ u, cutoff A B u * D.W u ∂(S.μ j) ≤ D.V + ε * (1 + M') := by
      have h1 : ∀ᶠ j in atTop, D.uF - 1 < T.θ j :=
        T.theta_tendsto.eventually (lt_mem_nhds (by linarith))
      have h2 := S.ae_le_of_gap (δ := 1) one_pos
      have h3 := T.limsup_le ε hε
      have h4 : ∀ᶠ j in atTop, ∀ x ∈ K, dist (D.W x) (T.Ψ j x) < ε :=
        Metric.tendstoUniformlyOn_iff.1 hunif ε hε
      filter_upwards [h1, h2, h3, h4, hM] with j hj1 hj2 hj3 hj4 hj5
      -- the cutoff only removes nonnegative mass
      have hint1 : Integrable (fun u => cutoff A B u * T.Ψ j u) (S.μ j) := by
        refine (T.integrable_mu j).bdd_mul (c := 1) ?_ ?_
        · exact (cutoff_continuous A B).aestronglyMeasurable
        · exact Eventually.of_forall fun u => by
            rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg A B u)]; exact cutoff_le_one A B u
      have hle1 : ∫ u, cutoff A B u * T.Ψ j u ∂(S.μ j) ≤ ∫ u, T.Ψ j u ∂(S.μ j) := by
        refine integral_mono_ae hint1 (T.integrable_mu j) ?_
        filter_upwards [hj2] with u hu
        by_cases hcase : D.uF - 1 ≤ u
        · rw [cutoff_eq_one (A := A) (B := B) (by linarith) (by linarith)]; linarith
        · push Not at hcase
          have hnn := T.nonneg j u (by linarith)
          have := cutoff_le_one A B u
          nlinarith [cutoff_nonneg A B u]
      -- compare with the limit window
      have hint2 : Integrable (fun u => cutoff A B u * D.W u) (S.μ j) :=
        integrable_of_cs ((cutoff_continuous A B).mul D.continuous)
          (HasCompactSupport.mul_cutoff A B)
      have hdiff : |∫ u, (cutoff A B u * T.Ψ j u - cutoff A B u * D.W u) ∂(S.μ j)| ≤
          ε * (S.μ j K).toReal := by
        refine abs_integral_le_of_zero_outside hKc (fun x hx => ?_) (fun x hx => ?_)
        · have : cutoff A B x = 0 := by
            refine cutoff_eq_zero ?_
            simp only [hKdef, mem_Icc, not_and_or, not_le] at hx
            rcases hx with h | h
            · exact Or.inl h.le
            · exact Or.inr h.le
          simp [this]
        · rw [← mul_sub, abs_mul, abs_of_nonneg (cutoff_nonneg A B x)]
          have := hj4 x hx
          rw [Real.dist_eq, abs_sub_comm] at this
          calc cutoff A B x * |T.Ψ j x - D.W x| ≤ 1 * ε := by
                exact mul_le_mul (cutoff_le_one A B x) this.le (abs_nonneg _) zero_le_one
            _ = ε := one_mul ε
      have hmass : ε * (S.μ j K).toReal ≤ ε * M' :=
        mul_le_mul_of_nonneg_left (hj5.trans (le_max_left _ _)) hε.le
      rw [integral_sub hint1 hint2] at hdiff
      have hcross := T.crossing j
      have : ∫ u, cutoff A B u * D.W u ∂(S.μ j) ≤
          ∫ u, cutoff A B u * T.Ψ j u ∂(S.μ j) + ε * M' := by
        have := (abs_le.mp (hdiff.trans hmass)).1
        linarith
      linarith
    have hlim := hν (fun u => cutoff A B u * D.W u) ((cutoff_continuous A B).mul D.continuous)
      (HasCompactSupport.mul_cutoff A B)
    exact le_of_tendsto hlim (Filter.Eventually.filter_mono h𝒰 hev)
  refine le_of_forall_pos_le_add fun η hη => ?_
  have h1M : 0 < 1 + M' := by positivity
  have := key (η / (1 + M')) (by positivity)
  rwa [div_mul_cancel₀ _ h1M.ne'] at this

/-- `∫ cutoff · Ψ_j dμ_j → ∫ cutoff · W_𝔇 dν` along any filter `l ≤ atTop` along which
`μ_j → ν` vaguely (the test functions converge locally uniformly and the masses of compacta are
bounded). -/
theorem tendsto_cutoff_integral (S : SpectralData) (hbd : LocallyBounded S.μ) {l : Filter ℕ}
    (hl : l ≤ atTop) {ν : Measure ℝ} (hν : IsVagueLimit l S.μ ν)
    {D : Window} (T : DesignTest S.μ D) (A B : ℝ) :
    Tendsto (fun j => ∫ u, cutoff A B u * T.Ψ j u ∂(S.μ j)) l
      (𝓝 (∫ u, cutoff A B u * D.W u ∂ν)) := by
  set K : Set ℝ := Icc (A - 1) (B + 1) with hKdef
  have hKc : IsCompact K := isCompact_Icc
  obtain ⟨M, hM⟩ := hbd K hKc
  set M' : ℝ := max M 0 with hM'
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.1 T.window_limit) K hKc
  have hlim := hν (fun u => cutoff A B u * D.W u) ((cutoff_continuous A B).mul D.continuous)
    (HasCompactSupport.mul_cutoff A B)
  have hdiff : Tendsto (fun j => ∫ u, cutoff A B u * T.Ψ j u ∂(S.μ j) -
      ∫ u, cutoff A B u * D.W u ∂(S.μ j)) l (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε' : 0 < ε / (2 * (1 + M')) := by positivity
    have h4 : ∀ᶠ j in atTop, ∀ x ∈ K, dist (D.W x) (T.Ψ j x) < ε / (2 * (1 + M')) :=
      Metric.tendstoUniformlyOn_iff.1 hunif _ hε'
    filter_upwards [Filter.Eventually.filter_mono hl h4, Filter.Eventually.filter_mono hl hM]
      with j hj4 hj5
    have hint1 : Integrable (fun u => cutoff A B u * T.Ψ j u) (S.μ j) := by
      refine (T.integrable_mu j).bdd_mul (c := 1) ?_ ?_
      · exact (cutoff_continuous A B).aestronglyMeasurable
      · exact Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg A B u)]; exact cutoff_le_one A B u
    have hint2 : Integrable (fun u => cutoff A B u * D.W u) (S.μ j) :=
      integrable_of_cs ((cutoff_continuous A B).mul D.continuous) (HasCompactSupport.mul_cutoff A B)
    have hdiff' : |∫ u, (cutoff A B u * T.Ψ j u - cutoff A B u * D.W u) ∂(S.μ j)| ≤
        ε / (2 * (1 + M')) * (S.μ j K).toReal := by
      refine abs_integral_le_of_zero_outside hKc (fun x hx => ?_) (fun x hx => ?_)
      · have : cutoff A B x = 0 := by
          refine cutoff_eq_zero ?_
          simp only [hKdef, mem_Icc, not_and_or, not_le] at hx
          rcases hx with h | h
          · exact Or.inl h.le
          · exact Or.inr h.le
        simp [this]
      · rw [← mul_sub, abs_mul, abs_of_nonneg (cutoff_nonneg A B x)]
        have := hj4 x hx
        rw [Real.dist_eq, abs_sub_comm] at this
        calc cutoff A B x * |T.Ψ j x - D.W x| ≤ 1 * (ε / (2 * (1 + M'))) :=
              mul_le_mul (cutoff_le_one A B x) this.le (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
    rw [integral_sub hint1 hint2] at hdiff'
    rw [Real.dist_eq, sub_zero]
    have hmass : ε / (2 * (1 + M')) * (S.μ j K).toReal ≤ ε / (2 * (1 + M')) * M' :=
      mul_le_mul_of_nonneg_left (hj5.trans (le_max_left _ _)) hε'.le
    have hlt : ε / (2 * (1 + M')) * M' < ε := by
      have h1 : 0 ≤ M' := le_max_right _ _
      have : ε / (2 * (1 + M')) * M' = ε * (M' / (2 * (1 + M'))) := by ring
      rw [this]
      have : M' / (2 * (1 + M')) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      nlinarith
    exact lt_of_le_of_lt (hdiff'.trans hmass) hlt
  have := hdiff.add hlim
  simpa using this.congr fun j => by ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.basic_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.basic_inequality

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.tendsto_cutoff_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.tendsto_cutoff_integral

end FormalResearch.ModularBootstrap.Upper.Rigidity
