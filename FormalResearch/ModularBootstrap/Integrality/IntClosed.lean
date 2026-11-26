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

end FormalResearch.ModularBootstrap.Integrality
