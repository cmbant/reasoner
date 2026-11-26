module

public import FormalResearch.ModularBootstrap.Duality.VagueCompactness
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Topology.Instances.Int

/-!
# Vague closedness of integer counting measures (`int:int-closed`, Lemma INT-4A)

`CFT/modular_bootstrap/paper/integrality.tex`, Lemma INT-4A: if `Y` is a closed subset of `ℝ^d`
(here any proper metric space, with its Borel σ-algebra) and `ν_k` are locally finite positive
integer-weighted atomic measures on `Y` converging vaguely to a positive Radon measure `ν`, then
`ν` is locally finite atomic with positive integer weights, `ν = ∑_{x ∈ supp ν} ν{x} δ_x`,
`ν{x} ∈ ℤ_{≥ 1}` on the support, and the support is discrete and closed.

*Vague convergence* is `Duality.IsVagueLimitAlong` (continuous compactly supported test functions),
along any filter (in particular `atTop` on `ℕ`, or an ultrafilter).

Proof (as in the paper): for a relatively compact open `U` with `ν (∂U) = 0` the Urysohn sandwich
gives `ν_j U → ν U`, so `ν U ∈ ℕ`; balls of radius off the countable set of charged spheres give
`ν {x} ∈ ℕ`, and `ν {x} ≥ 1` on the support; a compact set carries at most `ν K` support points.

Statements are in the paper's class **proved**.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace FormalResearch.ModularBootstrap.Integrality

open FormalResearch.ModularBootstrap.Duality

variable {Y : Type*} [MetricSpace Y] [ProperSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- `ν` is a *locally finite positive integer-weighted atomic measure* on `Y`
(the paper's "integer counting measure"): `ν = ∑_{x ∈ S} d_x δ_x` with `d_x ∈ ℤ_{≥ 1}` on a set
`S` meeting every compact set in a finite set (so `S` is discrete and closed). -/
def IsIntegerCounting (ν : Measure Y) : Prop :=
  ∃ (S : Set Y) (d : Y → ℕ), (∀ K : Set Y, IsCompact K → (S ∩ K).Finite) ∧
    (∀ x ∈ S, 1 ≤ d x) ∧
    ν = Measure.sum (fun x : S => (d x : ℝ≥0∞) • Measure.dirac (x : Y))

open Classical in
/-- An integer counting measure gives integer mass to every measurable set with compact closure. -/
lemma IsIntegerCounting.exists_nat {ν : Measure Y} (h : IsIntegerCounting ν) {A : Set Y}
    (hA : MeasurableSet A) (hc : IsCompact (closure A)) : ∃ n : ℕ, ν A = n := by
  obtain ⟨S, d, hS, -, rfl⟩ := h
  have hfin : {x : S | (x : Y) ∈ closure A}.Finite :=
    ((hS _ hc).preimage Subtype.val_injective.injOn).subset (fun x hx => ⟨x.2, hx⟩)
  refine ⟨∑ x ∈ hfin.toFinset, (if (x : Y) ∈ A then d x else 0), ?_⟩
  rw [Measure.sum_apply _ hA, tsum_eq_sum (s := hfin.toFinset)]
  · push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : (x : Y) ∈ A <;> simp [Measure.dirac_apply' _ hA, hx]
  · intro x hx
    have : (x : Y) ∉ A := fun h => hx (by simpa using subset_closure h)
    simp [Measure.dirac_apply' _ hA, this]

/-- An integer counting measure is finite on compact sets. -/
lemma IsIntegerCounting.isFiniteMeasureOnCompacts {ν : Measure Y} (h : IsIntegerCounting ν) :
    IsFiniteMeasureOnCompacts ν := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨n, hn⟩ := h.exists_nat hK.isClosed.measurableSet (by rwa [hK.isClosed.closure_eq])
  rw [hn]
  exact ENNReal.natCast_lt_top n

section Sandwich

/-- Upper bound of a `[0,1]`-valued test function supported in a finite-mass measurable set. -/
lemma integral_le_measure_toReal {μ : Measure Y} {A : Set Y} (hA : MeasurableSet A)
    (hfin : μ A < ∞) {φ : Y → ℝ} (h0 : ∀ x, 0 ≤ φ x) (h1 : ∀ x, φ x ≤ 1)
    (hz : ∀ x, x ∉ A → φ x = 0) : ∫ x, φ x ∂μ ≤ (μ A).toReal := by
  have hφ : ∀ x, φ x ≤ A.indicator (fun _ => (1 : ℝ)) x := fun x => by
    by_cases hx : x ∈ A <;> simp [hx, h1 x, hz x]
  have hint : Integrable (A.indicator fun _ => (1 : ℝ)) μ :=
    (integrable_indicator_iff hA).2 (integrableOn_const hfin.ne)
  calc ∫ x, φ x ∂μ ≤ ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall h0) hint (Eventually.of_forall hφ)
    _ = (μ A).toReal := by
        rw [integral_indicator_const _ hA]; simp [Measure.real]

/-- Lower bound by a test function which is `≥ 1` on `A`. -/
lemma measure_toReal_le_integral {μ : Measure Y} {A : Set Y} {φ : Y → ℝ}
    (hφ : Integrable φ μ) (h0 : ∀ x, 0 ≤ φ x) (h1 : ∀ x ∈ A, 1 ≤ φ x) :
    (μ A).toReal ≤ ∫ x, φ x ∂μ := by
  have h := hφ.measure_le_integral (Eventually.of_forall h0) h1
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (integral_nonneg h0)] at this

variable {𝒥 : Type*} {l : Filter 𝒥} {μ : 𝒥 → Measure Y} {ν : Measure Y}

/-- Urysohn sandwich: a vague limit converges on relatively compact open sets with null
frontier. -/
theorem tendsto_measure_toReal_of_vagueLimit [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    [IsFiniteMeasureOnCompacts ν] (hν : IsVagueLimitAlong l μ ν) {U : Set Y} (hU : IsOpen U)
    (hc : IsCompact (closure U)) (hb : ν (frontier U) = 0) :
    Tendsto (fun j => (μ j U).toReal) l (𝓝 (ν U).toReal) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hfinν : ν U < ∞ := (measure_mono (subset_closure : U ⊆ closure U)).trans_lt hc.measure_lt_top
  have hfinμ : ∀ j, μ j U < ∞ := fun j =>
    (measure_mono (subset_closure : U ⊆ closure U)).trans_lt hc.measure_lt_top
  have hcl : ν (closure U) = ν U := by
    refine le_antisymm ?_ (measure_mono subset_closure)
    calc ν (closure U) ≤ ν (U ∪ frontier U) := by rw [← closure_eq_self_union_frontier]
      _ ≤ ν U + ν (frontier U) := measure_union_le _ _
      _ = ν U := by rw [hb, add_zero]
  have hε4 : (0 : ℝ) < ε / 4 := by positivity
  have hε4' : ENNReal.ofReal (ε / 4) ≠ 0 := by simpa using hε4
  -- inner approximation
  obtain ⟨K, hKU, hKc, hK⟩ := hU.measurableSet.exists_isCompact_lt_add (μ := ν) hfinν.ne hε4'
  have hK' : (ν U).toReal < (ν K).toReal + ε / 4 := by
    have hKfin : ν K < ∞ := hKc.measure_lt_top
    have := (ENNReal.toReal_lt_toReal hfinν.ne (ENNReal.add_ne_top.2 ⟨hKfin.ne, ENNReal.ofReal_ne_top⟩)).2 hK
    rwa [ENNReal.toReal_add hKfin.ne ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε4.le] at this
  obtain ⟨fm, hfm1, hfm0, hfmc, hfm01⟩ := exists_continuous_one_zero_of_isCompact hKc
    hU.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKU)
  -- outer approximation
  obtain ⟨V, hCV, hVo, hV⟩ := hc.exists_isOpen_lt_add (μ := ν) hε4'
  have hVfin : ν V < ∞ := hV.trans (ENNReal.add_lt_top.2 ⟨hc.measure_lt_top, ENNReal.ofReal_lt_top⟩)
  obtain ⟨fp, hfp1, hfp0, hfpc, hfp01⟩ := exists_continuous_one_zero_of_isCompact hc
    hVo.isClosed_compl (disjoint_compl_right_iff_subset.mpr hCV)
  have hV' : (ν V).toReal < (ν U).toReal + ε / 4 := by
    have := (ENNReal.toReal_lt_toReal hVfin.ne (ENNReal.add_ne_top.2
      ⟨hc.measure_lt_top.ne, ENNReal.ofReal_ne_top⟩)).2 hV
    rwa [ENNReal.toReal_add hc.measure_lt_top.ne ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε4.le,
      hcl] at this
  have hlm := Metric.tendsto_nhds.1 (hν fm fm.continuous hfmc) (ε / 4) hε4
  have hlp := Metric.tendsto_nhds.1 (hν fp fp.continuous hfpc) (ε / 4) hε4
  filter_upwards [hlm, hlp] with j hjm hjp
  rw [Real.dist_eq] at hjm hjp ⊢
  have hm_int : Integrable fm ν := integrable_of_cs' fm.continuous hfmc
  have hp_int : Integrable fp (μ j) := integrable_of_cs' fp.continuous hfpc
  have a1 : (ν K).toReal ≤ ∫ x, fm x ∂ν :=
    measure_toReal_le_integral hm_int (fun x => (hfm01 x).1) (fun x hx => by simp [hfm1 hx])
  have a2 : ∫ x, fm x ∂(μ j) ≤ (μ j U).toReal :=
    integral_le_measure_toReal hU.measurableSet (hfinμ j) (fun x => (hfm01 x).1)
      (fun x => (hfm01 x).2) (fun x hx => hfm0 (by simpa using hx))
  have a3 : (μ j U).toReal ≤ ∫ x, fp x ∂(μ j) :=
    measure_toReal_le_integral hp_int (fun x => (hfp01 x).1)
      (fun x hx => by simp [hfp1 (subset_closure hx)])
  have a4 : ∫ x, fp x ∂ν ≤ (ν V).toReal :=
    integral_le_measure_toReal hVo.measurableSet hVfin (fun x => (hfp01 x).1)
      (fun x => (hfp01 x).2) (fun x hx => hfp0 (by simpa using hx))
  rw [abs_lt] at hjm hjp ⊢
  constructor <;> linarith [hjm.1, hjm.2, hjp.1, hjp.2]

end Sandwich

section Limit

variable {𝒥 : Type*} {l : Filter 𝒥} {μ : 𝒥 → Measure Y} {ν : Measure Y}

/-- A limit of natural numbers (along a filter that is not `⊥`) is a natural number. -/
lemma exists_nat_of_tendsto [l.NeBot] {a : 𝒥 → ℝ} {L : ℝ} (h : Tendsto a l (𝓝 L))
    (hn : ∀ j, ∃ n : ℕ, a j = n) : ∃ n : ℕ, L = n := by
  have hcl : IsClosed (Set.range ((↑) : ℤ → ℝ) ∩ Set.Ici 0) :=
    Int.isClosedEmbedding_coe_real.isClosed_range.inter isClosed_Ici
  have hmem : L ∈ Set.range ((↑) : ℤ → ℝ) ∩ Set.Ici 0 :=
    hcl.mem_of_tendsto h (Eventually.of_forall fun j => by
      obtain ⟨n, hn⟩ := hn j
      exact ⟨⟨(n : ℤ), by simp [hn]⟩, by rw [hn]; exact Nat.cast_nonneg n⟩)
  obtain ⟨⟨z, hz⟩, h0⟩ := hmem
  refine ⟨z.toNat, ?_⟩
  have : (0 : ℝ) ≤ z := by rw [hz]; exact h0
  have hz0 : 0 ≤ z := by exact_mod_cast this
  rw [← hz]; exact_mod_cast (Int.toNat_of_nonneg hz0).symm

/-- Integer mass of balls whose sphere is `ν`-null. -/
theorem exists_nat_ball_of_vagueLimit [l.NeBot] (hμ : ∀ j, IsIntegerCounting (μ j))
    [IsFiniteMeasureOnCompacts ν] (hν : IsVagueLimitAlong l μ ν) (x : Y) {r : ℝ}
    (hr : ν (Metric.sphere x r) = 0) : ∃ n : ℕ, ν (Metric.ball x r) = n := by
  have : ∀ j, IsFiniteMeasureOnCompacts (μ j) := fun j => (hμ j).isFiniteMeasureOnCompacts
  have hc : IsCompact (closure (Metric.ball x r)) :=
    (isCompact_closedBall x r).of_isClosed_subset isClosed_closure Metric.closure_ball_subset_closedBall
  have hlim := tendsto_measure_toReal_of_vagueLimit hν Metric.isOpen_ball hc
    (measure_mono_null Metric.frontier_ball_subset_sphere hr)
  obtain ⟨n, hn⟩ := exists_nat_of_tendsto hlim fun j => by
    obtain ⟨m, hm⟩ := (hμ j).exists_nat Metric.isOpen_ball.measurableSet hc
    exact ⟨m, by simp [hm]⟩
  refine ⟨n, ?_⟩
  have hfin : ν (Metric.ball x r) < ∞ :=
    (measure_mono (subset_closure : Metric.ball x r ⊆ closure (Metric.ball x r))).trans_lt
      hc.measure_lt_top
  rw [← ENNReal.ofReal_toReal hfin.ne, hn]; simp

omit [BorelSpace Y] in
/-- Spheres around `x` carry no mass for arbitrarily small radii. -/
lemma exists_null_radius (ν : Measure Y) [IsFiniteMeasureOnCompacts ν] [BorelSpace Y] (x : Y)
    (m : ℕ) : ∃ r : ℝ, 0 < r ∧ r < 1 / ((m : ℝ) + 1) ∧ ν (Metric.sphere x r) = 0 := by
  have hcount : {r : ℝ | 0 < ν (Metric.sphere x r)}.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion (μ := ν)
      (As := fun r : ℝ => Metric.sphere x r) (fun r => Metric.isClosed_sphere.measurableSet)
      (fun r r' hrr' => Set.disjoint_left.2 fun y hy hy' => hrr' (by
        simp only [Metric.mem_sphere] at hy hy'; rw [← hy, hy']))
  by_contra hcon
  push Not at hcon
  have hsub : Set.Ioo (0 : ℝ) (1 / ((m : ℝ) + 1)) ⊆ {r : ℝ | 0 < ν (Metric.sphere x r)} := by
    intro r hr
    exact pos_iff_ne_zero.2 (hcon r hr.1 hr.2)
  have := Cardinal.Real.Ioo_countable_iff.1 (hcount.mono hsub)
  have h1 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  linarith

/-- The mass of a point is a natural number, and is `≥ 1` on the support. -/
theorem exists_nat_singleton_of_vagueLimit [l.NeBot] (hμ : ∀ j, IsIntegerCounting (μ j))
    [IsFiniteMeasureOnCompacts ν] (hν : IsVagueLimitAlong l μ ν) (x : Y) :
    ∃ n : ℕ, ν {x} = n ∧ (x ∈ ν.support → 1 ≤ n) := by
  choose r hr0 hr1 hr2 using exists_null_radius ν x
  have hn : ∀ m, ∃ n : ℕ, ν (Metric.ball x (r m)) = n := fun m =>
    exists_nat_ball_of_vagueLimit hμ hν x (hr2 m)
  choose n hn using hn
  have hfin : ν {x} < ∞ := isCompact_singleton.measure_lt_top
  -- the balls of radius `1/(m+1)` shrink to `{x}`
  have hb : Tendsto (fun m : ℕ => ν (Metric.ball x (1 / ((m : ℝ) + 1)))) atTop (𝓝 (ν {x})) := by
    have hanti : Antitone (fun m : ℕ => Metric.ball x (1 / ((m : ℝ) + 1))) := by
      intro a b hab
      refine Metric.ball_subset_ball ?_
      have : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hab 1
      exact one_div_le_one_div_of_le (by positivity) this
    have h0 := tendsto_measure_iInter_atTop (μ := ν) (fun m => Metric.isOpen_ball.nullMeasurableSet)
      hanti ⟨0, ((measure_mono Metric.ball_subset_closedBall).trans_lt
        (isCompact_closedBall x _).measure_lt_top).ne⟩
    have hint : (⋂ m : ℕ, Metric.ball x (1 / ((m : ℝ) + 1))) = {x} := by
      ext y
      simp only [mem_iInter, Metric.mem_ball, mem_singleton_iff]
      constructor
      · intro h
        by_contra hy
        have hpos : 0 < dist y x := dist_pos.2 hy
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
        exact absurd (h m) (not_lt.2 hm.le)
      · rintro rfl m; simpa using by positivity
    rw [hint] at h0
    exact h0
  have hsq : Tendsto (fun m => ν (Metric.ball x (r m))) atTop (𝓝 (ν {x})) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun m => measure_mono (by simpa using hr0 m))
      (fun m => measure_mono (Metric.ball_subset_ball (hr1 m).le))
  have hreal : Tendsto (fun m : ℕ => (n m : ℝ)) atTop (𝓝 (ν {x}).toReal) := by
    have := (ENNReal.tendsto_toReal hfin.ne).comp hsq
    refine this.congr fun m => ?_
    simp [hn m]
  obtain ⟨k, hk⟩ := exists_nat_of_tendsto hreal fun m => ⟨n m, rfl⟩
  refine ⟨k, ?_, fun hx => ?_⟩
  · rw [← ENNReal.ofReal_toReal hfin.ne, hk]; simp
  · have hpos : ∀ m, 1 ≤ n m := fun m => by
      have h1 : 0 < ν (Metric.ball x (r m)) :=
        (Measure.mem_support_iff_forall x).1 hx _ (Metric.ball_mem_nhds x (hr0 m))
      rw [hn m] at h1
      exact_mod_cast h1
    have := ge_of_tendsto' hreal fun m => (by exact_mod_cast hpos m : (1 : ℝ) ≤ n m)
    rw [hk] at this
    exact_mod_cast this

/-- **`int:int-closed`** (Lemma INT-4A, vague closedness of integer counting measures).  Let `Y` be
a closed subset of `ℝ^d` (more generally a proper metric space) and let `μ j` be locally finite
positive integer-weighted atomic measures on `Y` converging vaguely, along a filter `l ≠ ⊥`, to a
positive Radon measure `ν` on `Y`.  Then `ν = ∑_{x ∈ supp ν} ν{x} δ_x`, with `ν{x} ∈ ℤ_{≥ 1}` on the
support and the support meeting every compact set in a finite set (hence discrete and closed). -/
theorem int_closed [l.NeBot] (hμ : ∀ j, IsIntegerCounting (μ j))
    [IsFiniteMeasureOnCompacts ν] (hν : IsVagueLimitAlong l μ ν) :
    (∀ x ∈ ν.support, ∃ n : ℕ, 1 ≤ n ∧ ν {x} = n) ∧
      (∀ K : Set Y, IsCompact K → (ν.support ∩ K).Finite) ∧
      ν = Measure.sum (fun x : ν.support => ν {(x : Y)} • Measure.dirac (x : Y)) := by
  have hs := exists_nat_singleton_of_vagueLimit hμ hν
  choose d hd hd1 using hs
  -- a compact set carries at most `ν K` support points
  have hfinS : ∀ K : Set Y, IsCompact K → (ν.support ∩ K).Finite := by
    intro K hK
    by_contra hinf
    obtain ⟨t, htS, htc⟩ := (Set.not_finite.1 hinf).exists_subset_card_eq (⌈(ν K).toReal⌉₊ + 1)
    have h1 : ∀ y ∈ t, (1 : ℝ≥0∞) ≤ ν {y} := fun y hy => by
      rw [hd y]; exact_mod_cast hd1 y (htS hy).1
    have h2 : ((t.card : ℕ) : ℝ≥0∞) ≤ ν (t : Set Y) := by
      have hsum : ν (t : Set Y) = ∑ y ∈ t, ν {y} := by
        rw [← measure_biUnion_finset (s := t) (f := fun y => ({y} : Set Y))
          (by intro a _ b _ hab; simp [Function.onFun, hab]) (fun _ _ => measurableSet_singleton _)]
        congr 1; ext y; simp
      rw [hsum]
      calc ((t.card : ℕ) : ℝ≥0∞) = ∑ _y ∈ t, (1 : ℝ≥0∞) := by simp
        _ ≤ ∑ y ∈ t, ν {y} := Finset.sum_le_sum h1
    have h3 : ν (t : Set Y) ≤ ν K := measure_mono fun y hy => (htS hy).2
    have h4 := h2.trans h3
    have hKfin : ν K < ∞ := hK.measure_lt_top
    have h5 : (t.card : ℝ) ≤ (ν K).toReal := by
      have := ENNReal.toReal_mono hKfin.ne h4
      simpa using this
    rw [htc] at h5
    push_cast at h5
    linarith [Nat.le_ceil (ν K).toReal]
  refine ⟨fun x hx => ⟨d x, hd1 x hx, hd x⟩, hfinS, ?_⟩
  -- the support is countable, and `ν` is carried by it
  have hcount : ν.support.Countable := by
    have : ν.support = ⋃ n, ν.support ∩ compactCovering Y n := by
      rw [← inter_iUnion, iUnion_compactCovering, inter_univ]
    rw [this]
    exact countable_iUnion fun n => (hfinS _ (isCompact_compactCovering Y n)).countable
  ext A hA
  have h1 : ν (A ∩ ν.support) = ν A := measure_inter_conull Measure.measure_compl_support
  have hcA : (A ∩ ν.support).Countable := hcount.mono inter_subset_right
  have h2 : ν (A ∩ ν.support) = ∑' x : ↥(A ∩ ν.support), ν {(x : Y)} := by
    have := measure_biUnion (μ := ν) hcA (f := fun y => ({y} : Set Y))
      (by intro a _ b _ hab; simp [Function.onFun, hab]) (fun _ _ => measurableSet_singleton _)
    rwa [Set.biUnion_of_singleton] at this
  rw [← h1, h2, Measure.sum_apply _ hA, tsum_subtype (A ∩ ν.support) (fun y => ν {y})]
  have h3 : ∀ x : ν.support, ((ν {(x : Y)} • Measure.dirac (x : Y)) A) =
      A.indicator (fun y => ν {y}) (x : Y) := by
    intro x
    by_cases hx : (x : Y) ∈ A <;> simp [Measure.dirac_apply' _ hA, hx]
  rw [tsum_congr h3, tsum_subtype ν.support (fun y => A.indicator (fun y => ν {y}) y)]
  refine tsum_congr fun y => ?_
  rw [Set.indicator_indicator, inter_comm]


open Classical in
/-- **`int:int-closed`** in the form `IsIntegerCounting ν`. -/
theorem isIntegerCounting_of_vagueLimit [l.NeBot] (hμ : ∀ j, IsIntegerCounting (μ j))
    [IsFiniteMeasureOnCompacts ν] (hν : IsVagueLimitAlong l μ ν) : IsIntegerCounting ν := by
  obtain ⟨h1, h2, h3⟩ := int_closed hμ hν
  choose d hd1 hd using h1
  refine ⟨ν.support, fun x => if hx : x ∈ ν.support then d x hx else 0, h2, fun x hx => ?_, ?_⟩
  · simpa [hx] using hd1 x hx
  · refine h3.trans ?_
    congr 1
    funext x
    simp [x.2, hd x x.2]

/-- Sequence form of `int:int-closed`. -/
theorem int_closed_nat {μ : ℕ → Measure Y} (hμ : ∀ k, IsIntegerCounting (μ k)) {ν : Measure Y}
    [IsFiniteMeasureOnCompacts ν] (hν : IsVagueLimitAlong atTop μ ν) : IsIntegerCounting ν :=
  isIntegerCounting_of_vagueLimit hμ hν

end Limit

/-- info: 'FormalResearch.ModularBootstrap.Integrality.int_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms int_closed

/-- info: 'FormalResearch.ModularBootstrap.Integrality.isIntegerCounting_of_vagueLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isIntegerCounting_of_vagueLimit

end FormalResearch.ModularBootstrap.Integrality
