import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Polynomial images: basic inputs

Namespace `FormalResearch.FrameFree.PolyImage`.  Elementary inputs to the Euclidean density of polynomial images
(`PolyImageClosure`, `ZClosureDischarge`):

* `dense_eval_ne_zero`: the complement of the zero set of a nonzero polynomial is Euclidean-dense;
* `exists_root_near`: a monic polynomial over `ℂ` with small value at `b` has a root near `b`
  (`‖r - b‖ ^ deg ≤ ‖G b‖`, from `‖G b‖ = ∏ ‖b - rᵢ‖`);
* `exists_algHom_ker_eq`: every maximal ideal of a finitely generated `ℂ`-algebra is the kernel of a
  `ℂ`-algebra map to `ℂ` (Nullstellensatz, weak form), and `algHom_eq_of_ker_eq`.
-/

namespace FormalResearch.FrameFree.PolyImage

open Polynomial

/-- The complement of the zero set of a nonzero polynomial is dense. -/
theorem dense_eval_ne_zero {σ : Type*} {c : MvPolynomial σ ℂ} (hc : c ≠ 0) :
    Dense {x : σ → ℂ | MvPolynomial.eval x c ≠ 0} := by
  classical
  rw [dense_iff_inter_open]
  intro U hU ⟨x₀, hx₀⟩
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hU x₀ hx₀
  apply hc
  refine MvPolynomial.funext_set (fun i => if i ∈ I then u i else Set.univ) (fun i => ?_) ?_
  · by_cases hi : i ∈ I
    · simp only [hi, ite_true]
      exact infinite_of_mem_nhds (x₀ i) ((hu i hi).1.mem_nhds (hu i hi).2)
    · simp only [hi, ite_false]; exact Set.infinite_univ
  · intro x hx
    by_contra hx0
    have hxU : x ∈ U := hsub fun i hi => by
      have := hx i (Set.mem_univ i)
      have hi' : i ∈ I := hi
      simpa [hi'] using this
    have : x ∈ U ∩ {x : σ → ℂ | MvPolynomial.eval x c ≠ 0} := ⟨hxU, by simpa using hx0⟩
    rw [hne] at this
    exact this

/-- `∏ ‖b - rᵢ‖ ≥ m ^ card` when every factor is `≥ m ≥ 0`. -/
theorem pow_card_le_prod_real (m : ℝ) (hm : 0 ≤ m) (s : Multiset ℝ) (h : ∀ x ∈ s, m ≤ x) :
    m ^ Multiset.card s ≤ s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, Multiset.prod_cons, pow_succ, mul_comm]
    have ha : m ≤ a := h a (Multiset.mem_cons_self _ _)
    exact mul_le_mul ha (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)) (by positivity)
      (hm.trans ha)

/-- A monic polynomial of positive degree over `ℂ` has a root `r` with `‖r - b‖ ^ deg ≤ ‖G b‖`. -/
theorem exists_root_near (G : ℂ[X]) (hG : G.Monic) (hn : 0 < G.natDegree) (b : ℂ) :
    ∃ r : ℂ, G.IsRoot r ∧ ‖r - b‖ ^ G.natDegree ≤ ‖G.eval b‖ := by
  have hsplit : G.roots.card = G.natDegree :=
    (Polynomial.Splits.natDegree_eq_card_roots (IsAlgClosed.splits G)).symm
  have hG0 : G ≠ 0 := hG.ne_zero
  have hne : G.roots ≠ 0 := by
    intro h; rw [h] at hsplit; simp at hsplit; omega
  have hprod : G = (G.roots.map fun r => (Polynomial.X - Polynomial.C r)).prod :=
    (Polynomial.Splits.eq_prod_roots_of_monic (IsAlgClosed.splits G) hG)
  let D : Multiset ℝ := G.roots.map fun r => ‖r - b‖
  have hDne : D ≠ 0 := by simpa [D] using hne
  obtain ⟨m, hmD, hmin⟩ : ∃ m ∈ D, ∀ x ∈ D, m ≤ x := by
    refine ⟨D.toFinset.min' (by simpa [Multiset.toFinset_nonempty] using hDne), ?_, ?_⟩
    · simpa using Finset.min'_mem D.toFinset _
    · intro x hx
      exact Finset.min'_le _ _ (by simpa using hx)
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hmD
  refine ⟨r, (Polynomial.mem_roots hG0).1 hr, ?_⟩
  have hev : ‖G.eval b‖ = D.prod := by
    have h1 : G.eval b = (G.roots.map fun r => b - r).prod := by
      conv_lhs => rw [hprod]
      rw [Polynomial.eval_multiset_prod, Multiset.map_map]
      simp
    have h2 := map_multiset_prod (normHom : ℂ →*₀ ℝ) (G.roots.map fun r => b - r)
    rw [h1]
    simp only [normHom_apply] at h2
    rw [h2, Multiset.map_map]
    simp [D, norm_sub_rev]
  rw [hev]
  have := pow_card_le_prod_real ‖r - b‖ (norm_nonneg _) D hmin
  simpa [D, hsplit] using this

section MaxPoint

variable {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]

/-- Every maximal ideal of a finitely generated `ℂ`-algebra is the kernel of a `ℂ`-algebra map to `ℂ`. -/
theorem exists_algHom_ker_eq (q : Ideal A) [hq : q.IsMaximal] :
    ∃ η : A →ₐ[ℂ] ℂ, RingHom.ker η = q := by
  let _ : Field (A ⧸ q) := Ideal.Quotient.field q
  have : Algebra.FiniteType ℂ (A ⧸ q) := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : Module.Finite ℂ (A ⧸ q) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ q)
  have : Algebra.IsAlgebraic ℂ (A ⧸ q) := Algebra.IsAlgebraic.of_finite ℂ _
  let φ : (A ⧸ q) →ₐ[ℂ] ℂ := IsAlgClosed.lift
  refine ⟨φ.comp (Ideal.Quotient.mkₐ ℂ q), ?_⟩
  have hφ : Function.Injective φ := (φ : (A ⧸ q) →+* ℂ).injective
  ext a
  simp only [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [show (0 : ℂ) = φ 0 from (map_zero φ).symm, hφ.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

end MaxPoint

/-- Two `ℂ`-algebra maps to `ℂ` with the same kernel are equal. -/
theorem algHom_eq_of_ker_eq {A : Type*} [CommRing A] [Algebra ℂ A] {ζ η : A →ₐ[ℂ] ℂ}
    (h : RingHom.ker (ζ : A →+* ℂ) = RingHom.ker (η : A →+* ℂ)) : ζ = η := by
  ext a
  have h1 : a - algebraMap ℂ A (ζ a) ∈ RingHom.ker (ζ : A →+* ℂ) := by simp
  rw [h] at h1
  simp at h1
  linear_combination -h1

end FormalResearch.FrameFree.PolyImage
