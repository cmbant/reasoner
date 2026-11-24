module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityAtomic
public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityIdeal
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroTransfer

/-!
# From two-simple-zero designs to the ideal inequality (`virasoro_two_level.tex`, `gt:2.6`, *Designs and their limits*)

`TwoZeroApprox δ`: a sequence of admissible two-simple-zero designs `𝔇_i` (`TwoZeroDesign`) with the zeros `p, q` of the
ideal datum `δ` whose windows `W_{𝔇_i}` converge to the ideal window `Re F_δ` pointwise, boundedly on compacta, with
`limsup ∫ W_{𝔇_i} ≤ ∫ F_δ` (`ε_k → 0`, `N → ∞`, `η_* → 0` of the TeX).
`TwoZeroIdealApprox` is the statement that every admissible ideal datum has such an approximation: a statement about
the explicit product windows alone (no comb, no spectral measure).

* `idealIneq_of_approx`: **the ideal inequality**.  If the `μ_j` carry design tests for every window of `twoZeroClass`
  (`designPropertyP_twoZero`, from `TwoSimpleZeroTransfer`) and `ν` is a vague limit of the `μ_j`, then
  `∫ cutoff_{A,B} · Re F_δ dν ≤ ∫ F_δ` for `A ≤ q - 2`, for every admissible `δ` with a `TwoZeroApprox δ`.
  (`basic_inequality_of_support` for each design, then the limit along the approximation by dominated convergence.)
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Rigidity

namespace IdealDatum

/-- Admissibility of an ideal datum: `q < p`, `q < 0`, `K ≥ 2`, the sites `s_k` (`3 ≤ k ≤ K`) are negative, pairwise
distinct and distinct from the Airy zeros `a_j`, `j > K` (so that every approximating design is admissible). -/
def Adm (δ : IdealDatum) : Prop :=
  δ.q < δ.p ∧ δ.q < 0 ∧ 2 ≤ δ.K ∧ (∀ k, 3 ≤ k → k ≤ δ.K → δ.s k < 0) ∧
    (∀ j k, 3 ≤ j → j ≤ δ.K → 3 ≤ k → k ≤ δ.K → δ.s j = δ.s k → j = k) ∧
    (∀ k, 3 ≤ k → k ≤ δ.K → ∀ j, δ.K < j → δ.s k ≠ airyZero j)

end IdealDatum

/-- An approximation of the ideal window of `δ` by admissible two-simple-zero designs. -/
structure TwoZeroApprox (δ : IdealDatum) where
  n : ℕ → ℕ
  d : ∀ i, TwoZeroDesign (n i)
  n_pos : ∀ i, 1 ≤ n i
  adm : ∀ i, (d i).Adm
  q_eq : ∀ i, (d i).q = δ.q
  bdd : ∀ R : ℝ, ∃ M : ℝ, ∀ i, ∀ u ∈ Icc (-R) R, |(d i).Wr u| ≤ M
  tendsto_pt : ∀ u, Tendsto (fun i => (d i).Wr u) atTop (𝓝 (δ.win u))
  limsup_le : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∫ u, (d i).Wr u ≤ (∫ u, δ.win u) + ε

/-- **Named hypothesis (window analysis, no comb): every admissible ideal datum is a limit of two-simple-zero
designs** (`ε_k → 0`, `N → ∞`, `η_* → 0`: window limit and vacuum limsup). -/
def TwoZeroIdealApprox : Prop := ∀ δ : IdealDatum, δ.Adm → Nonempty (TwoZeroApprox δ)

/-- **The ideal inequality** for a vague limit `ν`. -/
theorem idealIneq_of_approx {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)]
    (hbd : LocallyBounded μ) {𝒰 : Ultrafilter ℕ} (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) {ν : Measure ℝ}
    [IsLocallyFiniteMeasure ν] (hν : IsVagueLimit 𝒰 μ ν) (hP : DesignPropertyP μ twoZeroClass) {B : ℝ}
    (hB : ∀ᶠ j in atTop, ∀ᵐ u ∂(μ j), u ≤ B) {δ : IdealDatum} (X : TwoZeroApprox δ) :
    IdealIneq ν B δ.win δ.q (∫ u, δ.win u) := by
  intro A hA
  have hineq : ∀ i, ∫ u, cutoff A B u * (X.d i).Wr u ∂ν ≤ ∫ u, (X.d i).Wr u := by
    intro i
    obtain ⟨T⟩ := hP _ (twoZeroWin_mem (X.n_pos i) (X.d i) (X.adm i))
    have := basic_inequality_of_support hbd h𝒰 hν T (A := A) (B := B)
      (by simp only [twoZeroWin_uF, X.q_eq]; linarith) hB
    simp only [twoZeroWin_W] at this
    exact this
  -- dominated convergence on `[A - 1, B + 1]`
  obtain ⟨M, hM⟩ := X.bdd (max |A - 1| |B + 1|)
  have hconv : Tendsto (fun i => ∫ u, cutoff A B u * (X.d i).Wr u ∂ν) atTop
      (𝓝 (∫ u, cutoff A B u * δ.win u ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence
      (Set.indicator (Icc (A - 1) (B + 1)) (fun _ => M)) (fun i => ?_) ?_ (fun i => ?_) ?_
    · exact ((cutoff_continuous A B).mul (X.d i).continuous_Wr).aestronglyMeasurable
    · exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const isCompact_Icc.measure_lt_top.ne)
    · refine Eventually.of_forall fun u => ?_
      by_cases hu : u ∈ Icc (A - 1) (B + 1)
      · rw [Set.indicator_of_mem hu, Real.norm_eq_abs, abs_mul, abs_of_nonneg (cutoff_nonneg A B u)]
        have hR : u ∈ Icc (-(max |A - 1| |B + 1|)) (max |A - 1| |B + 1|) := by
          constructor
          · have h1 := le_abs_self (-(A - 1)); have h2 := abs_neg (A - 1)
            have h3 : |A - 1| ≤ max |A - 1| |B + 1| := le_max_left _ _
            linarith [hu.1, neg_abs_le (A - 1)]
          · have h3 : |B + 1| ≤ max |A - 1| |B + 1| := le_max_right _ _
            linarith [hu.2, le_abs_self (B + 1)]
        calc cutoff A B u * |(X.d i).Wr u| ≤ 1 * |(X.d i).Wr u| :=
              mul_le_mul_of_nonneg_right (cutoff_le_one A B u) (abs_nonneg _)
          _ ≤ M := by rw [one_mul]; exact hM i u hR
      · have : cutoff A B u = 0 := by
          refine cutoff_eq_zero ?_
          simp only [mem_Icc, not_and_or, not_le] at hu
          rcases hu with h | h
          · exact Or.inl h.le
          · exact Or.inr h.le
        rw [Set.indicator_of_notMem hu, this, zero_mul, norm_zero]
    · refine Eventually.of_forall fun u => ?_
      exact (X.tendsto_pt u).const_mul (cutoff A B u)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hev : ∀ᶠ i in atTop, ∫ u, cutoff A B u * (X.d i).Wr u ∂ν ≤ (∫ u, δ.win u) + ε := by
    filter_upwards [X.limsup_le ε hε] with i hi
    exact (hineq i).trans hi
  exact le_of_tendsto hconv hev

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.idealIneq_of_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealIneq_of_approx

end FormalResearch.ModularBootstrap.TwoLevel
