module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Core

/-!
# The basic inequality `(I)` for an arbitrary support bound (`spectral_rigidity.tex`, proof of `sr:Sigma`, Step 1)

`basic_inequality_of_support` is `Upper.Rigidity.basic_inequality` with the hypothesis `μ_j` supported on `u ≤ a₁ + δ`
replaced by `μ_j` supported on `u ≤ B` for an arbitrary level `B`, which Theorem 2.6 (`gt:2.6`) needs: the atom at the
first level `t₁` sits at `u₁ = -A₁/c_*`, which may exceed `a₁ + 1`.  `basic_inequality` is the case `B = a₁ + 1`
(`SpectralData.ae_le_of_gap`); the in-place re-derivation is prepared as a patch (see the report).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal Real

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.Special

/-- **Basic inequality** (Step 1 of `sr:Sigma`, `(I)` of `sr:eI` in cutoff form) for abstract spectral measures:
if the `μ_j` have locally bounded masses, `ν` is a vague limit along `𝒰 ≤ atTop`, `μ_j` is eventually supported
on `u ≤ B`, then for every design test `T` and every cutoff with `A ≤ u_f - 1`:
`∫ cutoff A B · W_𝔇 dν ≤ V_𝔇`. -/
theorem basic_inequality_of_support {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)]
    (hbd : LocallyBounded μ) {𝒰 : Ultrafilter ℕ}
    (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) {ν : Measure ℝ} (hν : IsVagueLimit 𝒰 μ ν)
    {D : Window} (T : DesignTest μ D) {A B : ℝ} (hA : A ≤ D.uF - 1)
    (hB : ∀ᶠ j in atTop, ∀ᵐ u ∂(μ j), u ≤ B) :
    ∫ u, cutoff A B u * D.W u ∂ν ≤ D.V := by
  set K : Set ℝ := Icc (A - 1) (B + 1) with hKdef
  have hKc : IsCompact K := isCompact_Icc
  obtain ⟨M, hM⟩ := hbd K hKc
  set M' : ℝ := max M 0 with hM'
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.1 T.window_limit) K hKc
  have key : ∀ ε : ℝ, 0 < ε → ∫ u, cutoff A B u * D.W u ∂ν ≤ D.V + ε * (1 + M') := by
    intro ε hε
    have hev : ∀ᶠ j in atTop, ∫ u, cutoff A B u * D.W u ∂(μ j) ≤ D.V + ε * (1 + M') := by
      have h1 : ∀ᶠ j in atTop, D.uF - 1 < T.θ j :=
        T.theta_tendsto.eventually (lt_mem_nhds (by linarith))
      have h2 := hB
      have h3 := T.limsup_le ε hε
      have h4 : ∀ᶠ j in atTop, ∀ x ∈ K, dist (D.W x) (T.Ψ j x) < ε :=
        Metric.tendstoUniformlyOn_iff.1 hunif ε hε
      filter_upwards [h1, h2, h3, h4, hM] with j hj1 hj2 hj3 hj4 hj5
      -- the cutoff only removes nonnegative mass
      have hint1 : Integrable (fun u => cutoff A B u * T.Ψ j u) (μ j) := by
        refine (T.integrable_mu j).bdd_mul (c := 1) ?_ ?_
        · exact (cutoff_continuous A B).aestronglyMeasurable
        · exact Eventually.of_forall fun u => by
            rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg A B u)]; exact cutoff_le_one A B u
      have hle1 : ∫ u, cutoff A B u * T.Ψ j u ∂(μ j) ≤ ∫ u, T.Ψ j u ∂(μ j) := by
        refine integral_mono_ae hint1 (T.integrable_mu j) ?_
        filter_upwards [hj2] with u hu
        by_cases hcase : D.uF - 1 ≤ u
        · rw [cutoff_eq_one (A := A) (B := B) (by linarith) hu]; linarith
        · push Not at hcase
          have hnn := T.nonneg j u (by linarith)
          have := cutoff_le_one A B u
          nlinarith [cutoff_nonneg A B u]
      -- compare with the limit window
      have hint2 : Integrable (fun u => cutoff A B u * D.W u) (μ j) :=
        integrable_of_cs ((cutoff_continuous A B).mul D.continuous)
          (HasCompactSupport.mul_cutoff A B)
      have hdiff : |∫ u, (cutoff A B u * T.Ψ j u - cutoff A B u * D.W u) ∂(μ j)| ≤
          ε * (μ j K).toReal := by
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
      have hmass : ε * (μ j K).toReal ≤ ε * M' :=
        mul_le_mul_of_nonneg_left (hj5.trans (le_max_left _ _)) hε.le
      rw [integral_sub hint1 hint2] at hdiff
      have hcross := T.crossing j
      have : ∫ u, cutoff A B u * D.W u ∂(μ j) ≤
          ∫ u, cutoff A B u * T.Ψ j u ∂(μ j) + ε * M' := by
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

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.basic_inequality_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.basic_inequality_of_support

end FormalResearch.ModularBootstrap.Upper.Rigidity
