module

public import FormalResearch.MatrixAnalysis.Spectral.SpecMap

/-!
# Lidskii's theorem (abstract layer)

Namespace `FormalResearch.MatrixAnalysis.Spectral`.  Claim class: **proved** (no hypothesis, no new axiom).

For symmetric operators `A, B` on an `N`-dimensional inner product space over `ℝ` or `ℂ`, with descending
eigenvalues `α_j = μ_j(A)`, `β_j = μ_j(B)` and `γ_i = μ_i(A - B)`:

* `lidskii_sum_le` (**Lidskii–Wielandt**): for every index set `J` of cardinality `k`,
  `Σ_{j∈J} (α_j - β_j) ≤ Σ_{i<k} γ_i`.
* `lidskii_sum_le_shift`: `Σ_{j∈J} (α_j - β_j) ≤ |J| c + Σ_i max(γ_i - c, 0)` for every real `c` and every `J`
  (`c = 0`: `≤ Σ_i max(γ_i, 0) = tr (A-B)_+`).
* `lidskii_abs_sum_le` (**Lidskii, trace-norm form**): `Σ_j |α_j - β_j| ≤ Σ_i |γ_i|`.

The proof follows Bhatia, *Matrix Analysis*, Thm III.4.1 (second proof): replace `C = A - B` by its positive
part `P` (`C ⪯ P`, `P ⪰ 0`, `tr P = Σ max(γ_i, 0)`); monotonicity gives `α_j ≤ μ_j(B + P)`, and
`μ_j(B + P) - β_j ≥ 0` has total `tr P`.  It uses only `Spectral.MinMax`, `Spectral.Weyl` (monotonicity and
scalar shifts) and trace additivity (`Spectral.KyFan`).

Not formalised here: Wielandt's minimax principle, the general majorization (Lidskii) form
`α↓ - β↓ ≺ γ` for convex test functions, and Hoffman–Wielandt (see `Spectral.HoffmanWielandt` if present).
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis.Spectral

open Module

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {N : ℕ} (hN : finrank 𝕜 E = N)

section Core

variable {A B P : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hP : P.IsSymmetric)

include hA hB hP in
/-- **Core of Lidskii.**  If `rq A ≤ rq B + c ‖·‖² + rq P` with `P ⪰ 0` then for every index set `J`,
`Σ_{j∈J} (μ_j(A) - μ_j(B)) ≤ |J| c + tr P`, where `tr P = Σ_j Re⟪b_j, P b_j⟫` in any orthonormal basis. -/
theorem lidskii_core (c : ℝ) (hle : ∀ x, rq A x ≤ rq B x + c * ‖x‖ ^ 2 + rq P x)
    (hpos : ∀ x, 0 ≤ rq P x) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E)
    (J : Finset (Fin N)) :
    ∑ j ∈ J, (hA.eigenvalues hN j - hB.eigenvalues hN j) ≤ J.card * c + ∑ i, rq P (b i) := by
  have hBP := hB.add hP
  have h1 : ∀ j, hA.eigenvalues hN j ≤ hBP.eigenvalues hN j + c := by
    intro j
    rw [← eigenvalue_add_scalar hBP hN c j]
    refine eigenvalue_mono hA (hBP.add (isSymmetric_scalar c)) hN (fun x => ?_) j
    rw [rq_add, rq_add, rq_scalar]
    linarith [hle x]
  have h2 : ∀ j, hB.eigenvalues hN j ≤ hBP.eigenvalues hN j :=
    fun j => eigenvalue_mono hB hBP hN (fun x => by rw [rq_add]; linarith [hpos x]) j
  have htr : ∑ j, (hBP.eigenvalues hN j - hB.eigenvalues hN j) = ∑ i, rq P (b i) := by
    rw [Finset.sum_sub_distrib, sum_eigenvalues_eq_sum_rq hBP hN b, sum_eigenvalues_eq_sum_rq hB hN b]
    simp only [rq_add, Finset.sum_add_distrib]
    ring
  calc ∑ j ∈ J, (hA.eigenvalues hN j - hB.eigenvalues hN j)
      ≤ ∑ j ∈ J, (hBP.eigenvalues hN j - hB.eigenvalues hN j + c) :=
        Finset.sum_le_sum fun j _ => by linarith [h1 j]
    _ = ∑ j ∈ J, (hBP.eigenvalues hN j - hB.eigenvalues hN j) + J.card * c := by
        rw [Finset.sum_add_distrib]; simp
    _ ≤ ∑ j, (hBP.eigenvalues hN j - hB.eigenvalues hN j) + J.card * c := by
        gcongr ?_ + _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun j _ _ => sub_nonneg.mpr (h2 j)
    _ = _ := by rw [htr]; ring

end Core

section Parts

variable {C : E →ₗ[𝕜] E} (hC : C.IsSymmetric)

include hC in
/-- Positive part of `C - c` in the eigenbasis of `C`. -/
theorem exists_posPart (c : ℝ) :
    ∃ P : E →ₗ[𝕜] E, P.IsSymmetric ∧ (∀ x, 0 ≤ rq P x) ∧ (∀ x, rq C x ≤ c * ‖x‖ ^ 2 + rq P x) ∧
      ∑ j, rq P (hC.eigenvectorBasis hN j) = ∑ i, max (hC.eigenvalues hN i - c) 0 := by
  refine ⟨dop (hC.eigenvectorBasis hN) (fun i => max (hC.eigenvalues hN i - c) 0),
    isSymmetric_dop _ _, fun x => ?_, fun x => ?_, ?_⟩
  · rw [rq_dop]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (le_max_right _ _) (by positivity)
  · rw [rq_dop, rq_eq_sum hC hN, norm_sq_eq_sum hC hN, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    nlinarith [le_max_left (hC.eigenvalues hN i - c) 0, sq_nonneg ‖inner 𝕜 (hC.eigenvectorBasis hN i) x‖]
  · simp_rw [rq_dop_basis]

include hC in
/-- Negative part of `C` in the eigenbasis of `C`. -/
theorem exists_negPart :
    ∃ P : E →ₗ[𝕜] E, P.IsSymmetric ∧ (∀ x, 0 ≤ rq P x) ∧ (∀ x, - rq C x ≤ rq P x) ∧
      ∑ j, rq P (hC.eigenvectorBasis hN j) = ∑ i, max (- hC.eigenvalues hN i) 0 := by
  refine ⟨dop (hC.eigenvectorBasis hN) (fun i => max (- hC.eigenvalues hN i) 0),
    isSymmetric_dop _ _, fun x => ?_, fun x => ?_, ?_⟩
  · rw [rq_dop]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (le_max_right _ _) (by positivity)
  · rw [rq_dop, rq_eq_sum hC hN, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    nlinarith [le_max_left (- hC.eigenvalues hN i) 0, sq_nonneg ‖inner 𝕜 (hC.eigenvectorBasis hN i) x‖]
  · simp_rw [rq_dop_basis]

end Parts

section Main

variable {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)

include hA hB in
/-- **Lidskii, shifted form.**  For every real `c` and index set `J`,
`Σ_{j∈J} (μ_j(A) - μ_j(B)) ≤ |J| c + Σ_i max(μ_i(A-B) - c, 0)`. -/
theorem lidskii_sum_le_shift (c : ℝ) (J : Finset (Fin N)) :
    ∑ j ∈ J, (hA.eigenvalues hN j - hB.eigenvalues hN j) ≤
      J.card * c + ∑ i, max ((hA.sub hB).eigenvalues hN i - c) 0 := by
  obtain ⟨P, hP, hpos, hle, htr⟩ := exists_posPart hN (hA.sub hB) c
  have := lidskii_core hN hA hB hP c (fun x => by
    have := hle x
    rw [rq_sub] at this
    linarith) hpos ((hA.sub hB).eigenvectorBasis hN) J
  rwa [htr] at this

include hA hB in
/-- **Lidskii–Wielandt theorem.**  For every index set `J` of cardinality `k`,
`Σ_{j∈J} (μ_j(A) - μ_j(B)) ≤ Σ_{i<k} μ_i(A - B)`. -/
theorem lidskii_sum_le (J : Finset (Fin N)) :
    ∑ j ∈ J, (hA.eigenvalues hN j - hB.eigenvalues hN j) ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < J.card), (hA.sub hB).eigenvalues hN i := by
  obtain ⟨c, hc1, hc2⟩ := exists_threshold (fun i => (hA.sub hB).eigenvalues hN i)
    ((hA.sub hB).eigenvalues_antitone hN) J.card
  have h := lidskii_sum_le_shift hN hA hB c J
  have hkN : J.card ≤ N := by simpa using Finset.card_le_univ J
  have hsum : ∑ i, max ((hA.sub hB).eigenvalues hN i - c) 0 =
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < J.card),
        ((hA.sub hB).eigenvalues hN i - c) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : (i : ℕ) < J.card
    · simp only [hi, ite_true]
      exact max_eq_left (by linarith [hc1 i hi])
    · simp only [hi, ite_false]
      exact max_eq_right (by linarith [hc2 i (not_lt.mp hi)])
  rw [hsum] at h
  simp only [Finset.sum_sub_distrib, Finset.sum_const, card_filter_lt_fin hkN, nsmul_eq_mul] at h ⊢
  linarith

include hA hB in
/-- **Lidskii, trace-norm form.**  `Σ_j |μ_j(A) - μ_j(B)| ≤ Σ_i |μ_i(A - B)|`. -/
theorem lidskii_abs_sum_le :
    ∑ j, |hA.eigenvalues hN j - hB.eigenvalues hN j| ≤ ∑ i, |(hA.sub hB).eigenvalues hN i| := by
  set δ : Fin N → ℝ := fun j => hA.eigenvalues hN j - hB.eigenvalues hN j with hδ
  set γ : Fin N → ℝ := fun i => (hA.sub hB).eigenvalues hN i with hγ
  have hpos : ∑ j ∈ Finset.univ.filter (fun j => 0 ≤ δ j), δ j ≤ ∑ i, max (γ i) 0 := by
    have := lidskii_sum_le_shift hN hA hB 0 (Finset.univ.filter (fun j => 0 ≤ δ j))
    simpa only [mul_zero, zero_add, sub_zero] using this
  have hneg : ∑ j ∈ Finset.univ.filter (fun j => ¬ 0 ≤ δ j), (- δ j) ≤ ∑ i, max (- γ i) 0 := by
    obtain ⟨P, hP, hpos, hle, htr⟩ := exists_negPart hN (hA.sub hB)
    have := lidskii_core hN hB hA hP 0 (fun x => by
      have := hle x
      rw [rq_sub] at this
      linarith) hpos ((hA.sub hB).eigenvectorBasis hN) (Finset.univ.filter (fun j => ¬ 0 ≤ δ j))
    rw [htr] at this
    simp only [mul_zero, zero_add] at this
    refine le_trans (le_of_eq ?_) this
    exact Finset.sum_congr rfl fun j _ => by simp [hδ]
  have h1 : ∑ j, |δ j| = ∑ j ∈ Finset.univ.filter (fun j => 0 ≤ δ j), δ j +
      ∑ j ∈ Finset.univ.filter (fun j => ¬ 0 ≤ δ j), (- δ j) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => 0 ≤ δ j)]
    congr 1
    · exact Finset.sum_congr rfl fun j hj => abs_of_nonneg (Finset.mem_filter.mp hj).2
    · exact Finset.sum_congr rfl fun j hj => abs_of_neg (not_le.mp (Finset.mem_filter.mp hj).2)
  have h2 : ∑ i, |γ i| = ∑ i, max (γ i) 0 + ∑ i, max (- γ i) 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases le_total 0 (γ i) with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring
  rw [h1, h2]
  linarith

end Main


/-- info: 'FormalResearch.MatrixAnalysis.Spectral.lidskii_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.lidskii_core

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.lidskii_sum_le_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.lidskii_sum_le_shift

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.lidskii_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.lidskii_sum_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.lidskii_abs_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.lidskii_abs_sum_le

end FormalResearch.MatrixAnalysis.Spectral
