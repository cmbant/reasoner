module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Weak compactness of positive measures on a compact space

Generic input for the limit steps (b), (c) of Theorem E (`dual_spectrum.tex`, `ds:E`):
on a compact Hausdorff space `E`, the finite measures of mass at most `C` form a weakly compact set
(Mathlib: `isCompact_setOfPred_finiteMeasure_le_of_compactSpace`, Riesz–Markov–Kakutani). Here we
add the finite-intersection argument: if finitely many linear constraints
`∫ F_j dμ = c_j` can be met up to any `ε` inside a compact set `K`, they can be met exactly.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal BoundedContinuousFunction

namespace FormalResearch.ModularBootstrap.Duality

section

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]

/-- Integration against a bounded continuous function is weakly continuous on finite measures. -/
lemma continuous_integral_finiteMeasure (g : E →ᵇ ℝ) :
    Continuous fun μ : FiniteMeasure E => ∫ x, g x ∂(μ : Measure E) := by
  rw [continuous_iff_continuousAt]
  intro μ
  exact FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 tendsto_id g

/-- Finite-intersection property: if every finite family of the constraints `∫ F_j dμ = c_j` is
met up to every `ε > 0` by some `μ ∈ K` (`K` weakly compact), then all of them hold exactly for one
`μ ∈ K`. -/
theorem exists_exact_of_approx {K : Set (FiniteMeasure E)} (hK : IsCompact K) (hKcl : IsClosed K)
    {J : Type*} (F : J → E →ᵇ ℝ) (c : J → ℝ)
    (H : ∀ (u : Finset J) (n : ℕ), ∃ μ ∈ K, ∀ j ∈ u, |∫ x, F j x ∂(μ : Measure E) - c j| ≤ 1 / (n + 1)) :
    ∃ μ ∈ K, ∀ j, ∫ x, F j x ∂(μ : Measure E) = c j := by
  classical
  let t : Finset J × ℕ → Set (FiniteMeasure E) := fun p =>
    K ∩ ⋂ j ∈ p.1, {μ | |∫ x, F j x ∂(μ : Measure E) - c j| ≤ 1 / (p.2 + 1)}
  have htcl : ∀ p, IsClosed (t p) := by
    intro p
    refine hKcl.inter ?_
    refine isClosed_biInter fun j _ => ?_
    exact isClosed_le (by
      have := continuous_integral_finiteMeasure (F j)
      fun_prop) continuous_const
  have htc : ∀ p, IsCompact (t p) := fun p => hK.inter_right (by
    refine isClosed_biInter fun j _ => ?_
    exact isClosed_le (by
      have := continuous_integral_finiteMeasure (F j)
      fun_prop) continuous_const)
  have htn : ∀ p, (t p).Nonempty := by
    intro p
    obtain ⟨μ, hμ, h⟩ := H p.1 p.2
    exact ⟨μ, hμ, by simpa using h⟩
  have htd : Directed (· ⊇ ·) t := by
    intro p q
    refine ⟨(p.1 ∪ q.1, max p.2 q.2), ?_, ?_⟩
    · rintro μ ⟨hμK, hμ⟩
      refine ⟨hμK, ?_⟩
      simp only [mem_iInter, mem_ofPred_eq] at hμ ⊢
      intro j hj
      refine (hμ j (Finset.mem_union_left _ hj)).trans ?_
      gcongr; exact le_max_left _ _
    · rintro μ ⟨hμK, hμ⟩
      refine ⟨hμK, ?_⟩
      simp only [mem_iInter, mem_ofPred_eq] at hμ ⊢
      intro j hj
      refine (hμ j (Finset.mem_union_right _ hj)).trans ?_
      gcongr; exact le_max_right _ _
  have hne : Nonempty (Finset J × ℕ) := ⟨(∅, 0)⟩
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn htc htcl
  rw [mem_iInter] at hμ
  have hμK : μ ∈ K := (hμ (∅, 0)).1
  refine ⟨μ, hμK, fun j => ?_⟩
  have hle : ∀ n : ℕ, |∫ x, F j x ∂(μ : Measure E) - c j| ≤ 1 / (n + 1) := by
    intro n
    have := (hμ ({j}, n)).2
    simp only [mem_iInter, mem_ofPred_eq, Finset.mem_singleton, forall_eq] at this
    exact this
  have h0 : |∫ x, F j x ∂(μ : Measure E) - c j| ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    linarith [hle n]
  have := abs_nonpos_iff.1 h0
  linarith

end

/-- info: 'FormalResearch.ModularBootstrap.Duality.exists_exact_of_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.exists_exact_of_approx

end FormalResearch.ModularBootstrap.Duality
