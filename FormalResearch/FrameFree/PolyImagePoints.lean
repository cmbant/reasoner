import Mathlib
import FormalResearch.FrameFree.PolyImageBasic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Polynomial images: topological and combinatorial helpers

Namespace `FormalResearch.FrameFree.PolyImage`.

* `exists_forall_sum_ne_zero`: finitely many nonzero vectors admit a linear form not vanishing on any of them;
* `continuous_eval_map`: `x ↦ (M.map (eval x)).eval b` is continuous for `M ∈ ℂ[σ][T]`;
* `eventually_roots_bounded`: roots of the specialisations `M.map (eval x)` of a monic `M` are bounded for `x` near
  a point (Cauchy bound).
-/

namespace FormalResearch.FrameFree.PolyImage

open Polynomial Filter Topology

theorem exists_forall_sum_ne_zero {ι : Type*} [Fintype ι] (S : Finset (ι → ℂ))
    (hS : ∀ s ∈ S, s ≠ 0) : ∃ κ : ι → ℂ, ∀ s ∈ S, ∑ i, κ i * s i ≠ 0 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let q : (ι → ℂ) → ℂ[X] := fun s => ∑ i, Polynomial.C (s i) * Polynomial.X ^ (e i : ℕ)
  have hq0 : ∀ s ∈ S, q s ≠ 0 := by
    intro s hs h
    obtain ⟨i0, hi0⟩ : ∃ i, s i ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hS s hs (funext hcon)
    have := congrArg (fun p : ℂ[X] => p.coeff (e i0 : ℕ)) h
    simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single i0] at this
    · simp at this; exact hi0 this
    · intro j _ hj
      have : (e i0 : ℕ) ≠ e j := fun h => hj (e.injective (Fin.ext h.symm))
      simp [this]
    · simp
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (S.biUnion fun s => (q s).roots.toFinset)
  refine ⟨fun i => t ^ (e i : ℕ), fun s hs => ?_⟩
  have : Polynomial.eval t (q s) ≠ 0 := by
    intro h0
    apply ht
    refine Finset.mem_biUnion.2 ⟨s, hs, ?_⟩
    simpa [Multiset.mem_toFinset, Polynomial.mem_roots (hq0 s hs)] using h0
  convert this using 1
  simp only [q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem continuous_eval_map {σ : Type*} (M : (MvPolynomial σ ℂ)[X]) (b : ℂ) :
    Continuous fun x : σ → ℂ => (M.map (MvPolynomial.eval x)).eval b := by
  simp_rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  refine continuous_finsetSum _ fun i _ => ?_
  exact (MvPolynomial.continuous_eval _).mul continuous_const

theorem eventually_roots_bounded {σ : Type*} (M : (MvPolynomial σ ℂ)[X]) (hM : M.Monic) (w : σ → ℂ) :
    ∃ R : ℝ, ∀ᶠ x in 𝓝 w, ∀ t : ℂ, (M.map (MvPolynomial.eval x)).IsRoot t → ‖t‖ ≤ R := by
  let G : (σ → ℂ) → ℝ := fun x => 1 + ∑ i ∈ Finset.range M.natDegree, ‖MvPolynomial.eval x (M.coeff i)‖
  have hG : Continuous G :=
    continuous_const.add (continuous_finsetSum _ fun i _ =>
      (MvPolynomial.continuous_eval _).norm)
  refine ⟨G w + 1, ?_⟩
  have hev : ∀ᶠ x in 𝓝 w, G x < G w + 1 := hG.continuousAt.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hev] with x hx t ht
  have hmon : (M.map (MvPolynomial.eval x)).Monic := hM.map _
  have hnd : (M.map (MvPolynomial.eval x)).natDegree = M.natDegree := hM.natDegree_map _
  have h1 := Polynomial.IsRoot.norm_lt_cauchyBound hmon.ne_zero ht
  have h2 : ((M.map (MvPolynomial.eval x)).cauchyBound : ℝ) ≤ G x := by
    unfold Polynomial.cauchyBound
    rw [hmon.leadingCoeff]
    simp only [nnnorm_one, div_one, hnd, NNReal.coe_add, NNReal.coe_one]
    have : ((Finset.sup (Finset.range M.natDegree)
        (fun i => ‖(M.map (MvPolynomial.eval x)).coeff i‖₊) : NNReal) : ℝ) ≤
        ∑ i ∈ Finset.range M.natDegree, ‖MvPolynomial.eval x (M.coeff i)‖ := by
      have hh : Finset.sup (Finset.range M.natDegree)
          (fun i => ‖(M.map (MvPolynomial.eval x)).coeff i‖₊) ≤
          ∑ i ∈ Finset.range M.natDegree, ‖(M.map (MvPolynomial.eval x)).coeff i‖₊ :=
        Finset.sup_le fun i hi => Finset.single_le_sum (f := fun i => ‖(M.map (MvPolynomial.eval x)).coeff i‖₊)
          (fun _ _ => zero_le) hi
      have := NNReal.coe_le_coe.2 hh
      simpa [Polynomial.coeff_map] using this
    simp only [G]
    linarith
  have : ‖t‖ < G x := by
    have := NNReal.coe_lt_coe.2 h1
    simpa using this.trans_le h2
  linarith

end FormalResearch.FrameFree.PolyImage
