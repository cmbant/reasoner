module

public import FormalResearch.Special.JacobiOrth

/-!
# Jacobi polynomials: zeros

For natural parameters `a b : ℕ`, the Jacobi polynomial `P_n^{(a,b)}` has `n` distinct real zeros, all
in the open interval `(-1, 1)` (DLMF 18.16, introduction; Szegő, *Orthogonal Polynomials*,
Theorem 3.3.1).

The proof is the classical sign-change argument, run through the factorisation of `P` instead of
an enumeration of sign changes. Let `M` be the multiset of roots of `P` in `(-1,1)`, `T = ∏_{x∈M}(X-x)`
and `P = T r`, so `r` has no zero in `(-1,1)` and hence constant sign there (intermediate value
theorem). Let `q = ∏_{x ∈ M.toFinset} (X - x)^{(mult x) mod 2}`. Then `T q` is a product of even
powers, hence nonnegative, so `w q P = w (T q) r` has constant sign on `(-1,1)` and is nonzero at
some point; its integral is therefore nonzero. Orthogonality to lower degrees
(`jacobi_orthogonal_lowerDegree`) forces `n ≤ deg q = ∑ (mult x) mod 2 ≤ ∑ mult x = |M| ≤ n`, and
equality throughout gives all multiplicities `1`, all `n` roots in `(-1,1)`.

## Main results

* `roots_of_orth`: abstract form, for any nonzero `P` of degree `≤ n` orthogonal to all polynomials
  of degree `< n` for a continuous weight positive on `(-1,1)`;
* `jacobi_roots_nodup`: `(jacobi a b n).roots.Nodup`;
* `jacobi_roots_card`: `(jacobi a b n).roots.card = n`, and `jacobi_roots_toFinset_card`;
* `jacobi_roots_mem`: every root lies in `(-1, 1)`;
* `jacobi_splits`, `jacobi_separable`: `P_n^{(a,b)}` splits over `ℝ` and is separable;
* `jacobi_natDegree`, `jacobi_ne_zero`: `deg P_n^{(a,b)} = n`.
-/

@[expose] public section

namespace FormalResearch.Special

open Polynomial MeasureTheory intervalIntegral

/-- A continuous function without zeros on `(-1,1)` has constant sign there. -/
lemma const_sign_of_ne_zero (g : ℝ → ℝ) (hg : Continuous g)
    (h0 : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, g x ≠ 0) :
    (∀ x ∈ Set.Ioo (-1 : ℝ) 1, 0 < g x) ∨ (∀ x ∈ Set.Ioo (-1 : ℝ) 1, g x < 0) := by
  have key : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ y ∈ Set.Ioo (-1 : ℝ) 1, 0 < g x → 0 < g y := by
    intro x hx y hy hgx
    by_contra hgy
    have hgy' : g y < 0 := lt_of_le_of_ne (not_lt.mp hgy) (h0 y hy)
    have hsub : Set.uIcc x y ⊆ Set.Ioo (-1 : ℝ) 1 :=
      Set.ordConnected_Ioo.uIcc_subset hx hy
    have h := intermediate_value_uIcc (a := x) (b := y) hg.continuousOn
    have hmem : (0 : ℝ) ∈ Set.uIcc (g x) (g y) := by
      rw [Set.mem_uIcc]; right; exact ⟨hgy'.le, hgx.le⟩
    obtain ⟨z, hz, hgz⟩ := h hmem
    exact h0 z (hsub hz) hgz
  by_cases hex : ∃ x ∈ Set.Ioo (-1 : ℝ) 1, 0 < g x
  · obtain ⟨x, hx, hgx⟩ := hex
    exact Or.inl fun y hy => key x hx y hy hgx
  · right
    intro y hy
    push Not at hex
    exact lt_of_le_of_ne (hex y hy) (h0 y hy)

/-- A continuous function of constant sign on `(-1,1)`, nonzero at one point there, has nonzero
integral. -/
lemma integral_ne_zero_of_sign (f : ℝ → ℝ) (hf : Continuous f)
    (hs : (∀ x ∈ Set.Ioo (-1 : ℝ) 1, 0 ≤ f x) ∨ (∀ x ∈ Set.Ioo (-1 : ℝ) 1, f x ≤ 0))
    (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo (-1 : ℝ) 1) (hne : f x₀ ≠ 0) :
    ∫ x in (-1 : ℝ)..1, f x ≠ 0 := by
  have aux : ∀ g : ℝ → ℝ, Continuous g → (∀ x ∈ Set.Ioo (-1 : ℝ) 1, 0 ≤ g x) → 0 < g x₀ →
      0 < ∫ x in (-1 : ℝ)..1, g x := by
    intro g hg hnn hpos
    have hcl : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ g x := by
      intro x hx
      have hc : IsClosed {x : ℝ | 0 ≤ g x} := isClosed_le continuous_const hg
      have : closure (Set.Ioo (-1 : ℝ) 1) ⊆ {x : ℝ | 0 ≤ g x} := hc.closure_subset_iff.mpr hnn
      rw [closure_Ioo (by norm_num)] at this
      exact this hx
    exact intervalIntegral.integral_pos (by norm_num) hg.continuousOn
      (fun x hx => hcl x ⟨hx.1.le, hx.2⟩) ⟨x₀, ⟨hx₀.1.le, hx₀.2.le⟩, hpos⟩
  rcases hs with hs | hs
  · exact (aux f hf hs (lt_of_le_of_ne (hs x₀ hx₀) (Ne.symm hne))).ne'
  · have h := aux (fun x => -f x) hf.neg (fun x hx => neg_nonneg.mpr (hs x hx))
      (neg_pos.mpr (lt_of_le_of_ne (hs x₀ hx₀) hne))
    rw [intervalIntegral.integral_neg] at h
    intro h0; rw [h0] at h; simp at h

/-- Abstract version of the zeros theorem. -/
theorem roots_of_orth (wt : ℝ → ℝ) (hwc : Continuous wt)
    (hwp : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, 0 < wt x)
    (P : ℝ[X]) (n : ℕ) (hP0 : P ≠ 0) (hPn : P.natDegree ≤ n)
    (horth : ∀ q : ℝ[X], q.natDegree < n →
      ∫ x in (-1 : ℝ)..1, wt x * q.eval x * P.eval x = 0) :
    P.roots.Nodup ∧ P.roots.card = n ∧ ∀ x ∈ P.roots, -1 < x ∧ x < 1 := by
  classical
  set M : Multiset ℝ := P.roots.filter (fun x => -1 < x ∧ x < 1) with hM
  set T : ℝ[X] := (M.map fun a => X - C a).prod with hT
  have hMle : M ≤ P.roots := Multiset.filter_le _ _
  have hTP : T ∣ P :=
    (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hMle)).trans (prod_multiset_X_sub_C_dvd P)
  obtain ⟨r, hr⟩ := hTP
  have hTm : T.Monic := monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hT0 : T ≠ 0 := hTm.ne_zero
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact hP0 hr
  have hTroots : T.roots = M := roots_multiset_prod_X_sub_C M
  have hTdeg : T.natDegree = M.card := natDegree_multiset_prod_X_sub_C_eq_card M
  -- `r` has no roots in `(-1,1)`
  have hrne : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, r.eval x ≠ 0 := by
    intro x hx hrx
    have hrm : 0 < rootMultiplicity x r := (rootMultiplicity_pos hr0).mpr hrx
    have h1 : rootMultiplicity x P = rootMultiplicity x T + rootMultiplicity x r := by
      rw [hr]; exact rootMultiplicity_mul (hr ▸ hP0)
    have h2 : rootMultiplicity x T = rootMultiplicity x P := by
      rw [← count_roots, ← count_roots, hTroots, hM]
      exact Multiset.count_filter_of_pos ⟨hx.1, hx.2⟩
    omega
  have hsign := const_sign_of_ne_zero (fun x => r.eval x) r.continuous hrne
  -- the odd-multiplicity part
  set F : Finset ℝ := M.toFinset with hF
  set c : ℝ → ℕ := fun x => M.count x with hc
  have hTprod : T = ∏ x ∈ F, (X - C x) ^ c x := Finset.prod_multiset_map_count M _
  set q : ℝ[X] := ∏ x ∈ F, (X - C x) ^ (c x % 2) with hq
  have hqdeg : q.natDegree = ∑ x ∈ F, c x % 2 := by
    rw [hq, natDegree_prod_of_monic _ _ (fun x _ => (monic_X_sub_C x).pow _)]
    simp [natDegree_pow]
  have hsumc : ∑ x ∈ F, c x = M.card := Multiset.toFinset_sum_count_eq M
  have hMcard : M.card ≤ P.roots.card := Multiset.card_le_card hMle
  have hPcard : P.roots.card ≤ n := (card_roots' P).trans hPn
  have hq0 : q ≠ 0 := (monic_prod_of_monic _ _ (fun x _ => (monic_X_sub_C x).pow _)).ne_zero
  have hTq : T * q = ∏ x ∈ F, (X - C x) ^ (c x + c x % 2) := by
    rw [hTprod, hq, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun x _ => (pow_add _ _ _).symm)
  have hTqnn : ∀ y : ℝ, 0 ≤ (T * q).eval y := by
    intro y
    rw [hTq, eval_prod]
    refine Finset.prod_nonneg (fun x _ => ?_)
    rw [eval_pow]
    exact Even.pow_nonneg ⟨(c x + c x % 2) / 2, by omega⟩ _
  -- orthogonality gives `n ≤ deg q`
  have hnq : n ≤ q.natDegree := by
    by_contra hlt
    push Not at hlt
    have h0 := horth q hlt
    set f : ℝ → ℝ := fun x => wt x * q.eval x * P.eval x with hf
    have hfc : Continuous f := by
      have := q.continuous; have := P.continuous
      simp only [hf]; fun_prop
    have hfe : ∀ x, f x = wt x * (T * q).eval x * r.eval x := by
      intro x; simp only [hf, hr, eval_mul]; ring
    have hsg : (∀ x ∈ Set.Ioo (-1 : ℝ) 1, 0 ≤ f x) ∨ (∀ x ∈ Set.Ioo (-1 : ℝ) 1, f x ≤ 0) := by
      rcases hsign with h | h
      · left; intro x hx; rw [hfe]
        exact mul_nonneg (mul_nonneg (hwp x hx).le (hTqnn x)) (h x hx).le
      · right; intro x hx; rw [hfe]
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hwp x hx).le (hTqnn x)) (h x hx).le
    have hqP : q * P ≠ 0 := mul_ne_zero hq0 hP0
    obtain ⟨x₀, hx₀, hx₀n⟩ := (Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1)).exists_notMem_finset
      (q * P).roots.toFinset
    have hqPx : (q * P).eval x₀ ≠ 0 := by
      intro h
      exact hx₀n (Multiset.mem_toFinset.mpr ((mem_roots hqP).mpr h))
    have hfx : f x₀ ≠ 0 := by
      have : f x₀ = wt x₀ * (q * P).eval x₀ := by simp only [hf, eval_mul]; ring
      rw [this]; exact mul_ne_zero (hwp x₀ hx₀).ne' hqPx
    exact integral_ne_zero_of_sign f hfc hsg x₀ hx₀ hfx h0
  -- squeeze
  have hqle : ∑ x ∈ F, c x % 2 ≤ ∑ x ∈ F, c x :=
    Finset.sum_le_sum (fun x _ => Nat.mod_le _ _)
  have hMeq : M = P.roots := Multiset.eq_of_le_of_card_le hMle (by omega)
  have hcardn : P.roots.card = n := by omega
  have hsumeq : ∑ x ∈ F, c x % 2 = ∑ x ∈ F, c x := by omega
  have hall := (Finset.sum_eq_sum_iff_of_le (fun x _ => Nat.mod_le (c x) 2)).mp hsumeq
  refine ⟨?_, hcardn, ?_⟩
  · rw [Multiset.nodup_iff_count_le_one]
    intro a
    by_cases ha : a ∈ F
    · have h1 := hall a ha
      have h2 : 0 < c a := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp ha)
      have : c a = M.count a := rfl
      rw [← hMeq]
      omega
    · rw [← hMeq, Multiset.count_eq_zero.mpr (fun h => ha (Multiset.mem_toFinset.mpr h))]
      omega
  · intro x hx
    rw [← hMeq] at hx
    have := (Multiset.mem_filter.mp hx).2
    exact this

lemma jacobi_ne_zero (a b n : ℕ) : jacobi (a : ℝ) (b : ℝ) n ≠ 0 := by
  intro h
  have := jacobi_coeff_self_ne_zero (a : ℝ) (b : ℝ) (by positivity) (by positivity) n
  rw [h] at this
  simp at this

/-- `jacobi a b n` has degree exactly `n`. -/
lemma jacobi_natDegree (a b n : ℕ) : (jacobi (a : ℝ) (b : ℝ) n).natDegree = n :=
  le_antisymm (natDegree_jacobi_le _ _ _)
    (le_natDegree_of_ne_zero (jacobi_coeff_self_ne_zero (a : ℝ) (b : ℝ) (by positivity)
      (by positivity) n))

/-- The zeros of `P_n^{(a,b)}` are simple, `n` in number, and lie in `(-1,1)`
(DLMF 18.16, Szegő Theorem 3.3.1), in the combined form. -/
theorem jacobi_roots_spec (a b n : ℕ) :
    (jacobi (a : ℝ) (b : ℝ) n).roots.Nodup ∧ (jacobi (a : ℝ) (b : ℝ) n).roots.card = n ∧
      ∀ x ∈ (jacobi (a : ℝ) (b : ℝ) n).roots, -1 < x ∧ x < 1 := by
  refine roots_of_orth (fun x => (1 - x) ^ a * (1 + x) ^ b) (by fun_prop) ?_
    (jacobi (a : ℝ) (b : ℝ) n) n (jacobi_ne_zero a b n) (jacobi_natDegree a b n).le ?_
  · intro x hx
    have h1 : 0 < 1 - x := by linarith [hx.2]
    have h2 : 0 < 1 + x := by linarith [hx.1]
    positivity
  · intro q hq
    exact jacobi_orthogonal_lowerDegree a b n q hq

/-- `P_n^{(a,b)}` has `n` distinct roots, i.e. its roots form a multiset without repetition. -/
theorem jacobi_roots_nodup (a b n : ℕ) : (jacobi (a : ℝ) (b : ℝ) n).roots.Nodup :=
  (jacobi_roots_spec a b n).1

/-- `P_n^{(a,b)}` has exactly `n` roots (with multiplicity), so it splits over `ℝ`. -/
theorem jacobi_roots_card (a b n : ℕ) : (jacobi (a : ℝ) (b : ℝ) n).roots.card = n :=
  (jacobi_roots_spec a b n).2.1

/-- `P_n^{(a,b)}` has `n` distinct real roots. -/
theorem jacobi_roots_toFinset_card (a b n : ℕ) :
    (jacobi (a : ℝ) (b : ℝ) n).roots.toFinset.card = n := by
  classical
  rw [Multiset.toFinset_card_of_nodup (jacobi_roots_nodup a b n), jacobi_roots_card]

/-- `P_n^{(a,b)}` splits over `ℝ`. -/
theorem jacobi_splits (a b n : ℕ) : (jacobi (a : ℝ) (b : ℝ) n).Splits := by
  rw [splits_iff_card_roots, jacobi_roots_card, jacobi_natDegree]

/-- `P_n^{(a,b)}` is separable (all `n` zeros are simple). -/
theorem jacobi_separable (a b n : ℕ) : (jacobi (a : ℝ) (b : ℝ) n).Separable :=
  (nodup_roots_iff_of_splits (jacobi_ne_zero a b n) (jacobi_splits a b n)).mp
    (jacobi_roots_nodup a b n)

/-- All roots of `P_n^{(a,b)}` lie in the open interval `(-1, 1)`. -/
theorem jacobi_roots_mem (a b n : ℕ) (x : ℝ) (hx : (jacobi (a : ℝ) (b : ℝ) n).eval x = 0) :
    -1 < x ∧ x < 1 :=
  (jacobi_roots_spec a b n).2.2 x ((mem_roots (jacobi_ne_zero a b n)).mpr hx)

/-- info: 'FormalResearch.Special.jacobi_roots_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_roots_spec

/-- info: 'FormalResearch.Special.jacobi_roots_toFinset_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_roots_toFinset_card

/-- info: 'FormalResearch.Special.jacobi_separable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_separable

/-- info: 'FormalResearch.Special.jacobi_roots_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_roots_mem

end FormalResearch.Special
