import Mathlib
import FormalResearch.FourQubitEntropy.SevenQubitMajorantDegree

/-!
# Hermite converse for the degree of a sharp scalar entropy majorant

Completes `prop:seven-entropy-majorant-degree`
(`ResearchNotes/QI/seven_qubit_entanglement/seven_qubit_entropy_joint.tex`) by the converse half
that `SevenQubitMajorantDegree.lean` left out.

* `hermite_exists`: Hermite interpolation of degree `< 2|A|` for any values and slopes at the
  finite node set `A` (injectivity from `eq_zero_of_double_roots`, then a dimension count).
* `hermite_remainder_neg`: the sign of the Hermite remainder, `f t ≤ H t` for `f = -t log t`,
  `t ∈ (0,1) \ A`.  Proved as in the note by the auxiliary polynomial `H + c ∏ (X-a)^2` and
  iterated Rolle (`exists_zero_iter`), which yields `c (2k)! = f^{(2k)}(ξ) < 0`; this avoids
  quoting a Hermite remainder formula from Mathlib.
* `hermite_majorizes` / `hermite_majorant_exists`: the interpolant majorizes `f` on all of `[0,1]`
  (nodes by equality, endpoints by continuity).
* `majorant_degree_isLeast` (and `_logb_two` for `-t log₂ t`, the paper's `f`): for `k ≥ 2`
  interior nodes the least degree of a polynomial majorant touching at all nodes is exactly
  `2k - 1` (lower bound from `majorant_degree_lower_bound`).

All proved; no hypotheses beyond `0 < a < 1` for the nodes.  The seven-qubit application is in
`SevenQubitMajorantDegreeSeven.lean`.
-/

open Set Polynomial

namespace FormalResearch.FourQubitEntropy

namespace MajorantDegree

/-- A real polynomial of degree `< 2|A|` with a double root at every node of the finite set `A`
is zero. -/
theorem eq_zero_of_double_roots (A : Finset ℝ) (p : ℝ[X]) (hp : p.natDegree < 2 * A.card)
    (h0 : ∀ a ∈ A, p.eval a = 0) (h1 : ∀ a ∈ A, (derivative p).eval a = 0) : p = 0 := by
  classical
  by_contra hne
  have hle : (2 • A.val : Multiset ℝ) ≤ p.roots := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_nsmul, Polynomial.count_roots]
    by_cases ha : a ∈ A
    · rw [Multiset.count_eq_one_of_mem A.nodup ha]
      have := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hne).2 ⟨h0 a ha, h1 a ha⟩
      omega
    · rw [Multiset.count_eq_zero_of_notMem (by simpa using ha)]; simp
  have h2 := Multiset.card_le_card hle
  have h3 := Polynomial.card_roots' p
  simp only [Multiset.card_nsmul, Finset.card_val] at h2
  omega

/-- **Hermite interpolation** (existence).  For a finite set `A` of nodes and prescribed values
`v a`, slopes `w a` there is a real polynomial of degree `< 2|A|` with `H a = v a` and
`H' a = w a` for all `a ∈ A`.  (Linear algebra: the evaluation map on `degreeLT ℝ (2|A|)` is
injective by `eq_zero_of_double_roots`, hence bijective by dimension count.) -/
theorem hermite_exists (A : Finset ℝ) (v w : ℝ → ℝ) :
    ∃ H : ℝ[X], H ∈ degreeLT ℝ (2 * A.card) ∧
      (∀ a ∈ A, H.eval a = v a) ∧ ∀ a ∈ A, (derivative H).eval a = w a := by
  classical
  let T : degreeLT ℝ (2 * A.card) →ₗ[ℝ] (A → ℝ) × (A → ℝ) :=
    (LinearMap.pi fun a : A => (Polynomial.leval (a : ℝ)).comp (degreeLT ℝ (2 * A.card)).subtype).prod
      (LinearMap.pi fun a : A => (Polynomial.leval (a : ℝ)).comp
        ((derivative (R := ℝ)).comp (degreeLT ℝ (2 * A.card)).subtype))
  have hT : ∀ p, T p = (fun a : A => (p : ℝ[X]).eval (a : ℝ),
      fun a : A => (derivative (p : ℝ[X])).eval (a : ℝ)) := fun p => rfl
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hT, Prod.mk_eq_zero] at hp
    by_cases h0 : (p : ℝ[X]) = 0
    · exact Subtype.ext h0
    · have hpd : (p : ℝ[X]).natDegree < 2 * A.card :=
        (natDegree_lt_iff_degree_lt h0).2 (Polynomial.mem_degreeLT.1 p.2)
      exact Subtype.ext (eq_zero_of_double_roots A p hpd (fun a ha => congrFun hp.1 ⟨a, ha⟩)
        (fun a ha => congrFun hp.2 ⟨a, ha⟩))
  have hdim : Module.finrank ℝ (degreeLT ℝ (2 * A.card)) =
      Module.finrank ℝ ((A → ℝ) × (A → ℝ)) := by
    rw [(degreeLTEquiv ℝ (2 * A.card)).finrank_eq, Module.finrank_prod]
    simp
    ring
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  obtain ⟨p, hp⟩ := hsurj (fun a : A => v a, fun a : A => w a)
  rw [hT] at hp
  simp only [Prod.mk.injEq] at hp
  refine ⟨p, p.2, fun a ha => ?_, fun a ha => ?_⟩
  · exact congrFun hp.1 ⟨a, ha⟩
  · exact congrFun hp.2 ⟨a, ha⟩

/-- The nodal polynomial `∏_{a ∈ A} (X - a)^2`: monic of degree `2|A|`. -/
noncomputable def nodal (A : Finset ℝ) : ℝ[X] := ∏ a ∈ A, (X - C a) ^ 2

theorem nodal_monic (A : Finset ℝ) : (nodal A).Monic :=
  monic_prod_of_monic _ _ fun a _ => (monic_X_sub_C a).pow 2

theorem nodal_natDegree (A : Finset ℝ) : (nodal A).natDegree = 2 * A.card := by
  unfold nodal
  rw [natDegree_prod_of_monic _ _ fun a _ => (monic_X_sub_C a).pow 2]
  simp [natDegree_pow, mul_comm]

theorem nodal_eval_nonneg (A : Finset ℝ) (t : ℝ) : 0 ≤ (nodal A).eval t := by
  unfold nodal
  rw [eval_prod]
  exact Finset.prod_nonneg fun a _ => by simp [sq_nonneg]

theorem nodal_eval_pos (A : Finset ℝ) {t : ℝ} (ht : t ∉ A) : 0 < (nodal A).eval t := by
  unfold nodal
  rw [eval_prod]
  exact Finset.prod_pos fun a ha => by
    have : t - a ≠ 0 := sub_ne_zero.2 fun h => ht (h ▸ ha)
    simpa using pow_pos (abs_pos.2 this) 2 |>.trans_eq (by simp [sq_abs])

theorem nodal_double_root (A : Finset ℝ) {a : ℝ} (ha : a ∈ A) :
    (nodal A).eval a = 0 ∧ (derivative (nodal A)).eval a = 0 := by
  have hne : nodal A ≠ 0 := (nodal_monic A).ne_zero
  have hdvd : (X - C a) ^ 2 ∣ nodal A := Finset.dvd_prod_of_mem (fun a => (X - C a) ^ 2) ha
  have hm : 1 < (nodal A).rootMultiplicity a := by
    have := (le_rootMultiplicity_iff hne).2 hdvd
    omega
  exact (one_lt_rootMultiplicity_iff_isRoot hne).1 hm

/-- The `2k`-th derivative of a polynomial of degree `≤ 2k` is the constant
`(2k)! * coeff_{2k}`. -/
theorem eval_iterate_derivative_top (q : ℝ[X]) (n : ℕ) (hq : q.natDegree ≤ n) (x : ℝ) :
    (derivative^[n] q).eval x = (n.factorial : ℝ) * q.coeff n := by
  have hd : (derivative^[n] q).natDegree ≤ 0 := by
    have := natDegree_iterate_derivative q n
    omega
  rw [eq_C_of_natDegree_le_zero hd, eval_C, coeff_iterate_derivative]
  simp [Nat.descFactorial_self]

/-- **Hermite remainder inequality** (interior, off-node form).  Let `H` have degree `< 2|A|`
and match `f = -t log t` and `f'` at every node of the nonempty node set `A ⊂ (0,1)`.  Then
`f t ≤ H t` for every `t ∈ (0,1) \ A`.  Proof as in the note: with `c` chosen so that
`q = H + c ∏ (X - a)^2` also interpolates at `t`, `q - f` has `2|A|` distinct zeros of its
derivative (the nodes and the Rolle points), hence `(q - f)^{(2|A|)}` vanishes at some `ξ`; this
gives `c (2|A|)! = f^{(2|A|)}(ξ) < 0`. -/
theorem hermite_remainder_neg (A : Finset ℝ) (hA : A.Nonempty)
    (hA01 : ∀ a ∈ A, 0 < a ∧ a < 1) (H : ℝ[X]) (hH : H ∈ degreeLT ℝ (2 * A.card))
    (h0 : ∀ a ∈ A, H.eval a = Real.negMulLog a)
    (h1 : ∀ a ∈ A, (derivative H).eval a = -Real.log a - 1)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (htA : t ∉ A) :
    Real.negMulLog t ≤ H.eval t := by
  classical
  have hk : 0 < A.card := Finset.card_pos.2 hA
  have hHd : H.natDegree < 2 * A.card ∨ H = 0 := by
    by_cases h : H = 0
    · exact Or.inr h
    · exact Or.inl ((natDegree_lt_iff_degree_lt h).2 (Polynomial.mem_degreeLT.1 hH))
  set P := nodal A with hP
  have hPpos : 0 < P.eval t := nodal_eval_pos A htA
  set c : ℝ := (Real.negMulLog t - H.eval t) / P.eval t with hc
  have hcP : c * P.eval t = Real.negMulLog t - H.eval t := by
    rw [hc]; field_simp
  suffices hcneg : c < 0 by
    have := mul_neg_of_neg_of_pos hcneg hPpos
    linarith
  set q : ℝ[X] := H + C c * P with hq
  have hqd : q.natDegree ≤ 2 * A.card := by
    have h1 : (C c * P).natDegree ≤ 2 * A.card := by
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [hP, nodal_natDegree]
    have h2 : H.natDegree ≤ 2 * A.card := by
      rcases hHd with h | h
      · omega
      · rw [h]; simp
    exact (natDegree_add_le _ _).trans (max_le h2 h1)
  have hqc : q.coeff (2 * A.card) = c := by
    have hH' : H.coeff (2 * A.card) = 0 := by
      rcases hHd with h | h
      · exact coeff_eq_zero_of_natDegree_lt h
      · rw [h]; simp
    have hP' : P.coeff (2 * A.card) = 1 := by
      have := (nodal_monic A).coeff_natDegree
      rwa [nodal_natDegree] at this
    rw [hq, coeff_add, coeff_C_mul, hH', hP']; ring
  set g : ℕ → ℝ → ℝ := fun n x => (derivative^[n] q).eval x - negMulLogDeriv n x with hg
  have hgd : ∀ n, ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt (g n) (g (n + 1) x) x := by
    intro n x hx
    have h1 := Polynomial.hasDerivAt (derivative^[n] q) x
    have h2 := hasDerivAt_negMulLogDeriv n hx.1
    have := h1.fun_sub h2
    simpa only [hg, Function.iterate_succ_apply'] using this
  have hqa : ∀ a ∈ A, q.eval a = Real.negMulLog a ∧
      (derivative q).eval a = -Real.log a - 1 := by
    intro a ha
    obtain ⟨e0, e1⟩ := nodal_double_root A ha
    refine ⟨?_, ?_⟩
    · simp only [hq, eval_add, eval_mul, eval_C, hP, e0, h0 a ha]; ring
    · simp only [hq, derivative_add, derivative_mul, derivative_C, zero_mul, zero_add, eval_add, eval_mul, eval_C, hP, e1, h1 a ha]; ring
  have hg0 : ∀ a ∈ A, g 0 a = 0 := fun a ha => by
    simp [hg, negMulLogDeriv, (hqa a ha).1]
  have hg1 : ∀ a ∈ A, g 1 a = 0 := fun a ha => by
    simp [hg, negMulLogDeriv, (hqa a ha).2]
  have hgt : g 0 t = 0 := by
    have : q.eval t = Real.negMulLog t := by
      simp only [hq, eval_add, eval_mul, eval_C]; rw [hcP]; ring
    simp [hg, negMulLogDeriv, this]
  -- zeros of g 0: nodes and t
  have hcard0 : (insert t A).card = A.card + 1 := Finset.card_insert_of_notMem htA
  obtain ⟨S, hSc, hS⟩ := rolle_step (hgd 0) (insert t A) A.card
    (fun x hx => by
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ⟨ht, hgt⟩
      · exact ⟨hA01 x hx, hg0 x hx⟩) hcard0
  have hdisj : Disjoint A S := Finset.disjoint_left.2 fun a haA haS =>
    (hS a haS).2.1 (Finset.mem_insert_of_mem haA)
  have hcard : (A ∪ S).card = (2 * A.card - 1) + 1 := by
    rw [Finset.card_union_of_disjoint hdisj, hSc]; omega
  have hzs : ∀ y ∈ A ∪ S, y ∈ Ioo (0:ℝ) 1 ∧ (fun n => g (n + 1)) 0 y = 0 := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact ⟨hA01 y hy, hg1 y hy⟩
    · obtain ⟨h1, _, ⟨x, hx, hxy⟩, ⟨x', hx', hyx'⟩⟩ := hS y hy
      have hxI : x ∈ Ioo (0:ℝ) 1 := by
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact ht
        · exact hA01 x hx
      have hxI' : x' ∈ Ioo (0:ℝ) 1 := by
        rcases Finset.mem_insert.1 hx' with rfl | hx'
        · exact ht
        · exact hA01 x' hx'
      exact ⟨⟨by linarith [hxI.1], by linarith [hxI'.2]⟩, h1⟩
  obtain ⟨x, hx, hx0⟩ := exists_zero_iter (2 * A.card - 1) (fun n => g (n + 1))
    (fun n => hgd (n + 1)) (A ∪ S) hzs hcard
  have hx0' : g (2 * A.card) x = 0 := by
    have : g (2 * A.card - 1 + 1) x = 0 := hx0
    rwa [show 2 * A.card - 1 + 1 = 2 * A.card by omega] at this
  simp only [hg] at hx0'
  rw [eval_iterate_derivative_top q _ hqd, hqc,
    show 2 * A.card = (2 * (A.card - 1)) + 2 by omega] at hx0'
  simp only [negMulLogDeriv] at hx0'
  have hodd : Odd (2 * (A.card - 1) + 1) := odd_two_mul_add_one _
  rw [hodd.neg_one_pow, neg_one_mul, neg_div] at hx0'
  have hfac : (0:ℝ) < ((2 * (A.card - 1) + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hfac2 : (0:ℝ) < ((2 * (A.card - 1)).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hxp : 0 < x ^ (2 * (A.card - 1) + 1) := pow_pos hx.1 _
  have hneg : ((2 * (A.card - 1) + 2).factorial : ℝ) * c =
      -((2 * (A.card - 1)).factorial : ℝ) / x ^ (2 * (A.card - 1) + 1) := by
    have e := neg_div (x ^ (2 * (A.card - 1) + 1)) ((2 * (A.card - 1)).factorial : ℝ)
    linarith
  have : ((2 * (A.card - 1) + 2).factorial : ℝ) * c < 0 := by
    rw [hneg]; exact div_neg_of_neg_of_pos (by linarith) hxp
  exact neg_of_mul_neg_right this hfac.le

/-- **Hermite majorant on `[0,1]`.**  A polynomial `H` of degree `< 2|A|` matching `-t log t` and
its derivative at every node of the nonempty set `A ⊂ (0,1)` majorizes `-t log t` on all of
`[0,1]` (off-node interior points by `hermite_remainder_neg`; nodes by equality; the endpoints
by continuity). -/
theorem hermite_majorizes (A : Finset ℝ) (hA : A.Nonempty)
    (hA01 : ∀ a ∈ A, 0 < a ∧ a < 1) (H : ℝ[X]) (hH : H ∈ degreeLT ℝ (2 * A.card))
    (h0 : ∀ a ∈ A, H.eval a = Real.negMulLog a)
    (h1 : ∀ a ∈ A, (derivative H).eval a = -Real.log a - 1) :
    ∀ t ∈ Icc (0:ℝ) 1, Real.negMulLog t ≤ H.eval t := by
  classical
  have hcl : IsClosed {t : ℝ | Real.negMulLog t ≤ H.eval t} :=
    isClosed_le Real.continuous_negMulLog (Polynomial.continuous H)
  have hsub : Ioo (0:ℝ) 1 ⊆ {t : ℝ | Real.negMulLog t ≤ H.eval t} := by
    intro t ht
    by_cases htA : t ∈ A
    · exact (h0 t htA).ge
    · exact hermite_remainder_neg A hA hA01 H hH h0 h1 ht htA
  have := closure_minimal hsub hcl
  rw [closure_Ioo (zero_ne_one' ℝ)] at this
  exact this

/-- **Hermite converse (existence of a majorant of degree `≤ 2k-1`).**  For any nonempty finite
set `A ⊂ (0,1)` of `k` nodes there is a polynomial `H` of degree `≤ 2k - 1` that touches
`-t log t` with matching derivative at every node and majorizes it on `[0,1]`. -/
theorem hermite_majorant_exists (A : Finset ℝ) (hA : A.Nonempty)
    (hA01 : ∀ a ∈ A, 0 < a ∧ a < 1) :
    ∃ H : ℝ[X], H.natDegree ≤ 2 * A.card - 1 ∧
      (∀ a ∈ A, H.eval a = Real.negMulLog a ∧ (derivative H).eval a = -Real.log a - 1) ∧
      ∀ t ∈ Icc (0:ℝ) 1, Real.negMulLog t ≤ H.eval t := by
  obtain ⟨H, hH, h0, h1⟩ := hermite_exists A Real.negMulLog (fun a => -Real.log a - 1)
  have hk : 0 < A.card := Finset.card_pos.2 hA
  refine ⟨H, ?_, fun a ha => ⟨h0 a ha, h1 a ha⟩,
    hermite_majorizes A hA hA01 H hH h0 h1⟩
  by_cases h : H = 0
  · simp [h]
  · have := (natDegree_lt_iff_degree_lt h).2 (Polynomial.mem_degreeLT.1 hH)
    omega

/-- **`prop:seven-entropy-majorant-degree`, sharp form (natural log).**  For `k ≥ 2` interior
nodes, the least degree of a polynomial majorant of `-t log t` on `[0,1]` touching it at all the
nodes is exactly `2k - 1`: the lower bound is `majorant_degree_lower_bound`, attainment is the
Hermite interpolant of `hermite_majorant_exists`. -/
theorem majorant_degree_isLeast (A : Finset ℝ) (hA : 2 ≤ A.card)
    (hA01 : ∀ a ∈ A, 0 < a ∧ a < 1) :
    IsLeast {d : ℕ | ∃ q : ℝ[X], q.natDegree = d ∧
      (∀ t ∈ Icc (0:ℝ) 1, Real.negMulLog t ≤ q.eval t) ∧ ∀ a ∈ A, q.eval a = Real.negMulLog a}
      (2 * A.card - 1) := by
  have hne : A.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨H, hd, hint, hmaj⟩ := hermite_majorant_exists A hne hA01
  constructor
  · refine ⟨H, le_antisymm hd ?_, hmaj, fun a ha => (hint a ha).1⟩
    exact majorant_degree_lower_bound A hA hA01 H hmaj fun a ha => (hint a ha).1
  · rintro d ⟨q, rfl, hq, hqa⟩
    exact majorant_degree_lower_bound A hA hA01 q hq hqa

/-- **`prop:seven-entropy-majorant-degree`, sharp form for the base-2 entropy
`f(t) = -t log₂ t`** exactly as stated in the paper: for `k ≥ 2` interior nodes the minimal degree
of a polynomial majorant of `f` on `[0,1]` touching `f` at all nodes is `2k - 1` (the Hermite
interpolant, rescaled by `1 / ln 2`, attains it). -/
theorem majorant_degree_isLeast_logb_two (A : Finset ℝ) (hA : 2 ≤ A.card)
    (hA01 : ∀ a ∈ A, 0 < a ∧ a < 1) :
    IsLeast {d : ℕ | ∃ q : ℝ[X], q.natDegree = d ∧
      (∀ t ∈ Icc (0:ℝ) 1, -t * Real.logb 2 t ≤ q.eval t) ∧
        ∀ a ∈ A, q.eval a = -a * Real.logb 2 a}
      (2 * A.card - 1) := by
  have hne : A.Nonempty := Finset.card_pos.1 (by omega)
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have key : ∀ t : ℝ, -t * Real.logb 2 t = (Real.log 2)⁻¹ * Real.negMulLog t := fun t => by
    rw [Real.logb, Real.negMulLog]; field_simp
  obtain ⟨H, hd, hint, hmaj⟩ := hermite_majorant_exists A hne hA01
  constructor
  · have hqmaj : ∀ t ∈ Icc (0:ℝ) 1, -t * Real.logb 2 t ≤ (C (Real.log 2)⁻¹ * H).eval t := by
      intro t ht
      rw [key, eval_mul, eval_C]
      exact mul_le_mul_of_nonneg_left (hmaj t ht) (inv_nonneg.2 hl.le)
    have hqa : ∀ a ∈ A, (C (Real.log 2)⁻¹ * H).eval a = -a * Real.logb 2 a := by
      intro a ha
      rw [key, eval_mul, eval_C, (hint a ha).1]
    refine ⟨C (Real.log 2)⁻¹ * H, le_antisymm ((natDegree_C_mul_le _ _).trans hd) ?_, hqmaj, hqa⟩
    exact majorant_degree_lower_bound_logb_two A hA hA01 _ hqmaj hqa
  · rintro d ⟨q, rfl, hq, hqa⟩
    exact majorant_degree_lower_bound_logb_two A hA hA01 q hq hqa

end MajorantDegree
end FormalResearch.FourQubitEntropy
