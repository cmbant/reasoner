module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Exact finite atomic solutions of finitely many moment constraints

The finite-dimensional core of `ds:farkas` and `ds:E`(a) (`dual_spectrum.tex`): if

* `Φ : Y → ℝⁿ` is continuous and tends to `0` at infinity along the closed set `X`
  (`‖Φ y‖ ≤ ε` outside a compact set, for every `ε > 0`),
* the dual inequalities hold: `l · Φ(y) + μ ≥ 0` on `X` with `μ ≥ 0` forces `l · a + μ C ≥ 0`,

then the target `a` is attained *exactly* by `Σ_k c_k Φ(y_k)` with at most `n + 1` atoms
`y_k ∈ X`, `c_k ≥ 0`, `Σ_k c_k ≤ C`.

The proof is Hahn–Banach separation from the compact convex set `C · conv({0} ∪ Φ(X))`
(compact by Carathéodory, `isCompact_convexHull_of_isCompact`), followed by Carathéodory.
-/

@[expose] public section

open Set Filter Topology Module
open scoped Pointwise

namespace FormalResearch.ModularBootstrap.Duality

/-- **Carathéodory with the dimension bound**: a point of `conv S` in a finite-dimensional space is
a convex combination of at most `dim + 1` points of `S`. -/
lemma exists_caratheodory {E : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} {x : E} (hx : x ∈ convexHull ℝ S) :
    ∃ (ι : Type) (_ : Fintype ι) (z : ι → E) (w : ι → ℝ), range z ⊆ S ∧ (∀ i, 0 < w i) ∧
      ∑ i, w i = 1 ∧ ∑ i, w i • z i = x ∧ Fintype.card ι ≤ finrank ℝ E + 1 := by
  obtain ⟨ι, hι, z, w, hzS, hai, hw, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hx
  refine ⟨ι, hι, z, w, hzS, hw, hw1, hwz, ?_⟩
  have h1 := AffineIndependent.card_le_finrank_succ hai
  have h2 : finrank ℝ (vectorSpan ℝ (range z)) ≤ finrank ℝ E := Submodule.finrank_le _
  omega

/-- The convex hull of a compact set in a finite-dimensional normed space is compact. -/
theorem isCompact_convexHull_of_isCompact {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hS : IsCompact S) : IsCompact (convexHull ℝ S) := by
  classical
  set n := finrank ℝ E with hn
  let Δ : Set (Fin (n + 1) → ℝ) := {lam | (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1}
  have hΔ : IsCompact Δ := by
    have hcl : IsClosed Δ := by
      have h1 : IsClosed {lam : Fin (n + 1) → ℝ | ∀ i, 0 ≤ lam i} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
      have h2 : IsClosed {lam : Fin (n + 1) → ℝ | ∑ i, lam i = 1} :=
        isClosed_eq (continuous_finsetSum (X := Fin (n + 1) → ℝ)
          (f := fun (i : Fin (n + 1)) (lam : Fin (n + 1) → ℝ) => lam i) _
          fun i _ => continuous_apply i) continuous_const
      exact h1.inter h2
    refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset hcl ?_
    intro lam hlam i _
    refine ⟨hlam.1 i, ?_⟩
    rw [← hlam.2]
    exact Finset.single_le_sum (f := lam) (fun j _ => hlam.1 j) (Finset.mem_univ i)
  let D : Set ((Fin (n + 1) → ℝ) × (Fin (n + 1) → E)) := Δ ×ˢ Set.pi univ fun _ => S
  have hD : IsCompact D := hΔ.prod (isCompact_univ_pi fun _ => hS)
  let f : ((Fin (n + 1) → ℝ) × (Fin (n + 1) → E)) → E := fun p => ∑ i, p.1 i • p.2 i
  have hf : Continuous f := by fun_prop
  have himg : f '' D = convexHull ℝ S := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨lam, z⟩, ⟨hlam, hz⟩, rfl⟩
      exact (convex_convexHull ℝ S).sum_mem (fun i _ => hlam.1 i) hlam.2
        (fun i _ => subset_convexHull ℝ S (hz i (mem_univ i)))
    · intro x hx
      obtain ⟨ι, hι, z, w, hzS, hw, hw1, hwz, hcard⟩ := exists_caratheodory hx
      have hSne : S.Nonempty := by
        by_contra h
        rw [not_nonempty_iff_eq_empty] at h
        simp [h] at hx
      obtain ⟨s0, hs0⟩ := hSne
      have hcard' : Fintype.card ι ≤ Fintype.card (Fin (n + 1)) := by simpa using hcard
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard'
      refine ⟨(Function.extend e w 0, Function.extend e z (fun _ => s0)), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · intro j
        show 0 ≤ Function.extend e w 0 j
        by_cases hj : ∃ i, e i = j
        · obtain ⟨i, rfl⟩ := hj
          rw [e.injective.extend_apply]; exact (hw i).le
        · rw [Function.extend_apply' _ _ _ hj]; simp
      · show ∑ j, Function.extend e w 0 j = 1
        rw [← hw1]
        symm
        refine Fintype.sum_of_injective e e.injective w _ ?_ ?_
        · intro j hj
          rw [Function.extend_apply' _ _ _ (by simpa using hj)]; rfl
        · intro i; rw [e.injective.extend_apply]
      · intro j _
        show Function.extend e z (fun _ => s0) j ∈ S
        by_cases hj : ∃ i, e i = j
        · obtain ⟨i, rfl⟩ := hj
          rw [e.injective.extend_apply]; exact hzS ⟨i, rfl⟩
        · rw [Function.extend_apply' _ _ _ hj]; exact hs0
      · rw [← hwz]
        show ∑ j, Function.extend e w 0 j • Function.extend e z (fun _ => s0) j = _
        symm
        refine Fintype.sum_of_injective e e.injective (fun i => w i • z i) _ ?_ ?_
        · intro j hj
          rw [Function.extend_apply' _ _ _ (by simpa using hj)]; simp
        · intro i; simp only [e.injective.extend_apply]
  rw [← himg]
  exact hD.image hf

/-- `{0} ∪ Φ(X)` is compact when `Φ` is continuous and small at infinity along the closed set `X`. -/
lemma isCompact_insert_image {Y : Type*} [TopologicalSpace Y] {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (Φ : Y → E)
    (hΦ : Continuous Φ) {X : Set Y} (hXc : IsClosed X)
    (hdec : ∀ ε > 0, ∃ K : Set Y, IsCompact K ∧ ∀ y ∈ X, y ∉ K → ‖Φ y‖ ≤ ε) :
    IsCompact (insert (0 : E) (Φ '' X)) := by
  obtain ⟨K1, hK1, h1⟩ := hdec 1 one_pos
  have hbd : Bornology.IsBounded (insert (0 : E) (Φ '' X)) := by
    have hc : IsCompact (Φ '' (X ∩ K1)) := (hK1.inter_left hXc).image hΦ
    refine (Bornology.IsBounded.insert (hc.isBounded.union
      ((Metric.isBounded_closedBall (x := (0 : E)) (r := 1)))) 0).subset ?_
    -- need: Φ '' X ⊆ ...
    intro v hv
    rcases hv with rfl | ⟨y, hy, rfl⟩
    · exact Or.inl rfl
    · by_cases hyK : y ∈ K1
      · exact Or.inr (Or.inl ⟨y, ⟨hy, hyK⟩, rfl⟩)
      · exact Or.inr (Or.inr (by simpa using h1 y hy hyK))
  have hcl : IsClosed (insert (0 : E) (Φ '' X)) := by
    rw [← closure_subset_iff_isClosed]
    intro s hs
    by_cases hs0 : s = 0
    · simp [hs0]
    have hsn : 0 < ‖s‖ := norm_pos_iff.2 hs0
    obtain ⟨K, hK, hKd⟩ := hdec (‖s‖ / 4) (by positivity)
    have hc : IsCompact (Φ '' (X ∩ K)) := (hK.inter_left hXc).image hΦ
    have hmem : s ∈ closure (Φ '' (X ∩ K)) := by
      rw [Metric.mem_closure_iff]
      intro δ hδ
      obtain ⟨v, hv, hdv⟩ := Metric.mem_closure_iff.1 hs (min δ (‖s‖ / 4)) (by positivity)
      have hdv1 : dist s v < δ := lt_of_lt_of_le hdv (min_le_left _ _)
      have hdv2 : dist s v < ‖s‖ / 4 := lt_of_lt_of_le hdv (min_le_right _ _)
      have hvn : ‖s‖ / 4 < ‖v‖ := by
        have := norm_sub_norm_le s v
        rw [dist_eq_norm] at hdv2
        linarith
      rcases hv with rfl | ⟨y, hy, rfl⟩
      · simp at hvn; linarith
      · by_cases hyK : y ∈ K
        · exact ⟨Φ y, ⟨y, ⟨hy, hyK⟩, rfl⟩, hdv1⟩
        · exact absurd (hKd y hy hyK) (not_le.2 hvn)
    rw [hc.isClosed.closure_eq] at hmem
    obtain ⟨y, ⟨hy, -⟩, rfl⟩ := hmem
    exact Or.inr ⟨y, hy, rfl⟩
  exact Metric.isCompact_of_isClosed_isBounded hcl hbd

/-- **Exact finite atomic solution** (Farkas separation plus Carathéodory): see the module
docstring. -/
theorem exists_atomic_exact {Y : Type*} [TopologicalSpace Y] {u : Type} [Fintype u]
    (Φ : Y → (u → ℝ)) (hΦ : Continuous Φ) {X : Set Y} (hXc : IsClosed X)
    (hdec : ∀ ε > 0, ∃ K : Set Y, IsCompact K ∧ ∀ y ∈ X, y ∉ K → ‖Φ y‖ ≤ ε)
    {C : ℝ} (hC : 0 < C) (a : u → ℝ)
    (H : ∀ (l : u → ℝ) (μ : ℝ), 0 ≤ μ → (∀ y ∈ X, 0 ≤ ∑ i, l i * Φ y i + μ) →
      0 ≤ ∑ i, l i * a i + μ * C) :
    ∃ (ι : Type) (_ : Fintype ι) (y : ι → Y) (c : ι → ℝ), Fintype.card ι ≤ Fintype.card u + 1 ∧
      (∀ k, y k ∈ X) ∧ (∀ k, 0 ≤ c k) ∧ ∑ k, c k ≤ C ∧ ∀ i, ∑ k, c k * Φ (y k) i = a i := by
  classical
  set V0 : Set (u → ℝ) := insert 0 (Φ '' X) with hV0
  have hV0c : IsCompact V0 := isCompact_insert_image Φ hΦ hXc hdec
  set K : Set (u → ℝ) := C • convexHull ℝ V0 with hK
  have hKc : IsCompact K := (isCompact_convexHull_of_isCompact hV0c).smul C
  have hKconv : Convex ℝ K := (convex_convexHull ℝ V0).smul C
  have haK : a ∈ K := by
    by_contra hna
    obtain ⟨l, t, hlt, hb⟩ := geometric_hahn_banach_point_closed hKconv hKc.isClosed hna
    have hexp : ∀ v : u → ℝ, l v = ∑ i, v i * l (Pi.single i 1) := fun v => by
      have := LinearMap.pi_apply_eq_sum_univ (l : (u → ℝ) →ₗ[ℝ] ℝ) v
      rw [show (l : (u → ℝ) →ₗ[ℝ] ℝ) v = l v from rfl] at this
      rw [this]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
        funext j; simp [Pi.single_apply, eq_comm]
      simp [e]
    set li : u → ℝ := fun i => l (Pi.single i 1) with hli
    have hKmem : ∀ v ∈ V0, C • v ∈ K := fun v hv =>
      Set.smul_mem_smul_set (subset_convexHull ℝ V0 hv)
    have h0 : t < 0 := by
      have := hb (C • 0) (hKmem 0 (Set.mem_insert _ _))
      simpa using this
    have hx : ∀ y ∈ X, t < C * ∑ i, li i * Φ y i := by
      intro y hy
      have := hb _ (hKmem (Φ y) (Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩))
      rw [hexp] at this
      calc t < ∑ i, (C • Φ y) i * li i := this
        _ = C * ∑ i, li i * Φ y i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
    set μ : ℝ := -t / C with hμ
    have hμ0 : 0 < μ := div_pos (by linarith) hC
    have hdual : ∀ y ∈ X, 0 ≤ ∑ i, li i * Φ y i + μ := by
      intro y hy
      have h1 := hx y hy
      have h2 : C * μ = -t := by rw [hμ]; field_simp
      have h3 : 0 < C * (∑ i, li i * Φ y i + μ) := by nlinarith
      exact le_of_lt ((mul_pos_iff_of_pos_left hC).1 h3)
    have key := H li μ hμ0.le hdual
    have e1 : ∑ i, li i * a i = l a := by
      rw [hexp a]; exact Finset.sum_congr rfl fun i _ => by ring
    have e : C * μ = -t := by rw [hμ]; field_simp
    nlinarith
  -- Carathéodory
  obtain ⟨b, hb, rfl⟩ := haK
  obtain ⟨ι, hι, z, w, hzS, hw, hw1, hwz, hcard⟩ := exists_caratheodory hb
  rw [finrank_fintype_fun_eq_card] at hcard
  -- keep only the atoms which are images of points of `X`
  let P : ι → Prop := fun k => ∃ y ∈ X, Φ y = z k
  let κ : Type := {k : ι // P k}
  have : Fintype κ := Fintype.ofFinite _
  have hzP : ∀ k, ¬ P k → z k = 0 := by
    intro k hk
    rcases hzS ⟨k, rfl⟩ with h | ⟨y, hy, hyk⟩
    · exact h
    · exact absurd ⟨y, hy, hyk⟩ hk
  choose ypt hypX hypΦ using fun k : κ => k.2
  refine ⟨κ, inferInstance, ypt, fun k => C * w k.1, ?_, hypX, fun k => by
    have := hw k.1; positivity, ?_, ?_⟩
  · calc Fintype.card κ ≤ Fintype.card ι := Fintype.card_subtype_le _
      _ ≤ _ := hcard
  · calc ∑ k : κ, C * w k.1 ≤ ∑ k : ι, C * w k := by
          rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp) (fun k => C * w k)]
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro k _ _; have := hw k; positivity
      _ = C := by rw [← Finset.mul_sum, hw1, mul_one]
  · intro i
    have hi := congrFun hwz i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
    have hsum : ∑ k : ι, w k * z k i = ∑ k : κ, w k.1 * z k.1 i := by
      rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp) (fun k => w k * z k i),
        Finset.sum_filter_of_ne]
      intro k _ hne
      by_contra hk
      exact hne (by rw [hzP k hk]; simp)
    show ∑ k : κ, C * w k.1 * Φ (ypt k) i = (C • b) i
    calc ∑ k : κ, C * w k.1 * Φ (ypt k) i = C * ∑ k : κ, w k.1 * z k.1 i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [hypΦ k]; ring
      _ = C * ∑ k : ι, w k * z k i := by rw [hsum]
      _ = (C • b) i := by rw [hi]; simp

/-- info: 'FormalResearch.ModularBootstrap.Duality.exists_atomic_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.exists_atomic_exact

/-- info: 'FormalResearch.ModularBootstrap.Duality.isCompact_convexHull_of_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.isCompact_convexHull_of_isCompact

end FormalResearch.ModularBootstrap.Duality
