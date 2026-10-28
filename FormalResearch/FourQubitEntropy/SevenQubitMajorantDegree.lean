import Mathlib

/-!
# Minimum degree of a sharp scalar entropy majorant

Formalizes the lower-bound half of `prop:seven-entropy-majorant-degree`
(`ResearchNotes/QI/seven_qubit_entanglement/seven_qubit_entropy_joint.tex`).

Let `f(t) = -t log t` (`Real.negMulLog`) on `[0,1]`.  If `A` is a finite set of `k ≥ 2` interior
nodes `0 < a < 1` and a real polynomial `q` satisfies `q ≥ f` on `[0,1]` and `q a = f a` for all
`a ∈ A`, then `2k - 1 ≤ q.natDegree`
(`majorant_degree_lower_bound`; the base-2 entropy `-t log₂ t` is
`majorant_degree_lower_bound_logb_two`).

Proof, as in the note: `h = q - f ≥ 0` has an interior minimum at each node, so `h'` vanishes
there; Rolle's theorem gives `k - 1` further zeros of `h'` strictly between the nodes, so `h'`
has `2k - 1` distinct zeros in `(0,1)`, and iterated Rolle gives a zero of `h^{(2k-1)}`.  If
`natDegree q < 2k - 1` then `h^{(2k-1)} = -f^{(2k-1)}`, which is a nonzero multiple of
`t^{-(2k-2)}` (`negMulLogDeriv`), a contradiction.  Derivatives are tracked through an explicit
sequence `g : ℕ → ℝ → ℝ` with `HasDerivAt (g n) (g (n+1)) x` on `(0,1)`, not `iteratedDeriv`.

Not in this file: the converse half of the proposition (the degree-`(2k-1)` Hermite interpolant
matching `f, f'` at all nodes majorizes `f`) is `SevenQubitMajorantDegreeConverse`, and the
seven-qubit application (four distinct nodes, degree seven) is `SevenQubitMajorantDegreeSeven`.  The `k = 2` (cubic) case of
the Hermite majorization is in `HermiteMajorant.lean`.
-/

open Set Polynomial

namespace FormalResearch.FourQubitEntropy

namespace MajorantDegree

/-- Rolle step on a finite set of zeros in `(0,1)`: if `g` has `n+1` distinct zeros in `(0,1)`
then `g'` has `n` distinct zeros in `(0,1)`, each strictly between two zeros of `g` and
different from all of them. -/
theorem rolle_step {g g' : ℝ → ℝ} (hd : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt g (g' x) x) :
    ∀ (s : Finset ℝ) (n : ℕ), (∀ x ∈ s, x ∈ Ioo (0:ℝ) 1 ∧ g x = 0) → s.card = n + 1 →
      ∃ s' : Finset ℝ, s'.card = n ∧
        ∀ y ∈ s', g' y = 0 ∧ y ∉ s ∧ (∃ x ∈ s, x < y) ∧ (∃ x ∈ s, y < x) := by
  intro s
  induction s using Finset.induction_on_max with
  | empty => intro n _ hc; simp at hc
  | insert M T hT ih =>
    intro n hz hc
    have hMT : M ∉ T := fun h => lt_irrefl _ (hT M h)
    rw [Finset.card_insert_of_notMem hMT] at hc
    have hcT : T.card = n := by omega
    rcases n with _ | n
    · exact ⟨∅, by simp, by simp⟩
    · have hne : T.Nonempty := by rw [← Finset.card_pos]; omega
      obtain ⟨s', hs'c, hs'⟩ := ih n (fun x hx => hz x (Finset.mem_insert_of_mem hx)) hcT
      have hM'T : T.max' hne ∈ T := Finset.max'_mem T hne
      have hM'M : T.max' hne < M := hT _ hM'T
      obtain ⟨hM'I, hM'0⟩ := hz _ (Finset.mem_insert_of_mem hM'T)
      obtain ⟨hMI, hM0⟩ := hz M (Finset.mem_insert_self M T)
      have hin : ∀ x ∈ Ioo (T.max' hne) M, x ∈ Ioo (0:ℝ) 1 := fun x hx =>
        ⟨by linarith [hM'I.1, hx.1], by linarith [hMI.2, hx.2]⟩
      have hcont : ContinuousOn g (Icc (T.max' hne) M) := fun x hx => by
        have hx' : x ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hM'I.1, hx.1], by linarith [hMI.2, hx.2]⟩
        exact (hd x hx').continuousAt.continuousWithinAt
      obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_zero (f := g) (f' := g') hM'M hcont
        (by rw [hM'0, hM0]) (fun x hx => hd x (hin x hx))
      have hcs' : c ∉ s' := fun h => by
        obtain ⟨_, _, _, x, hx, hcx⟩ := hs' c h
        have := Finset.le_max' T x hx
        linarith [hc1.1]
      refine ⟨insert c s', by rw [Finset.card_insert_of_notMem hcs', hs'c], ?_⟩
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · refine ⟨hc2, ?_, ⟨_, Finset.mem_insert_of_mem hM'T, hc1.1⟩,
          ⟨M, Finset.mem_insert_self _ _, hc1.2⟩⟩
        intro h
        rcases Finset.mem_insert.1 h with h | h
        · linarith [hc1.2]
        · have := Finset.le_max' T y h
          linarith [hc1.1]
      · obtain ⟨h1, h2, ⟨x, hx, hxy⟩, ⟨x', hx', hyx'⟩⟩ := hs' y hy
        refine ⟨h1, ?_, ⟨x, Finset.mem_insert_of_mem hx, hxy⟩,
          ⟨x', Finset.mem_insert_of_mem hx', hyx'⟩⟩
        intro h
        rcases Finset.mem_insert.1 h with h | h
        · have := Finset.le_max' T x' hx'
          linarith
        · exact h2 h

/-- Iterated Rolle: `m+1` distinct zeros of `g 0` in `(0,1)` force a zero of `g m` in `(0,1)`,
for a sequence `g` with `g (n+1)` the derivative of `g n` on `(0,1)`. -/
theorem exists_zero_iter (m : ℕ) : ∀ (g : ℕ → ℝ → ℝ),
    (∀ n, ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt (g n) (g (n + 1) x) x) →
    ∀ s : Finset ℝ, (∀ x ∈ s, x ∈ Ioo (0:ℝ) 1 ∧ g 0 x = 0) → s.card = m + 1 →
      ∃ x ∈ Ioo (0:ℝ) 1, g m x = 0 := by
  induction m with
  | zero =>
    intro g _ s hs hc
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hc
    have hxs : x ∈ s := by simp [hx]
    exact ⟨x, (hs x hxs).1, (hs x hxs).2⟩
  | succ m ih =>
    intro g hg s hs hc
    obtain ⟨s', hc', hs'⟩ := rolle_step (hg 0) s (m + 1) hs hc
    refine ih (fun n => g (n + 1)) (fun n => hg (n + 1)) s' (fun y hy => ?_) hc'
    obtain ⟨h1, _, ⟨x, hx, hxy⟩, ⟨x', hx', hyx'⟩⟩ := hs' y hy
    exact ⟨⟨by linarith [(hs x hx).1.1], by linarith [(hs x' hx').1.2]⟩, h1⟩

/-- The derivatives of `Real.negMulLog` on `(0,∞)`: `f' = -log t - 1` and
`f^{(n+2)}(t) = (-1)^(n+1) n! / t^(n+1)`. -/
noncomputable def negMulLogDeriv : ℕ → ℝ → ℝ
  | 0 => Real.negMulLog
  | 1 => fun x => -Real.log x - 1
  | (n + 2) => fun x => (-1 : ℝ) ^ (n + 1) * (n.factorial : ℝ) / x ^ (n + 1)

theorem hasDerivAt_negMulLogDeriv (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (negMulLogDeriv n) (negMulLogDeriv (n + 1) x) x := by
  rcases n with _ | _ | n
  · exact Real.hasDerivAt_negMulLog hx.ne'
  · have h := ((Real.hasDerivAt_log hx.ne').neg.sub_const 1)
    have e1 : negMulLogDeriv 1 = fun x => (-Real.log) x - 1 := by
      funext y; simp [negMulLogDeriv]
    have e2 : negMulLogDeriv 2 x = -x⁻¹ := by
      simp [negMulLogDeriv, neg_div]
    show HasDerivAt (negMulLogDeriv 1) (negMulLogDeriv 2 x) x
    rw [e1, e2]; exact h
  · have h1 := ((hasDerivAt_pow (n + 1) x).inv (pow_ne_zero _ hx.ne')).const_mul
      ((-1 : ℝ) ^ (n + 1) * (n.factorial : ℝ))
    have h2 : negMulLogDeriv (n + 2) = fun x => (-1 : ℝ) ^ (n + 1) * (n.factorial : ℝ) *
        (x ^ (n + 1))⁻¹ := by
      funext y; simp [negMulLogDeriv, div_eq_mul_inv]
    rw [h2]
    convert h1 using 1
    simp only [negMulLogDeriv, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp

theorem negMulLogDeriv_ne_zero (n : ℕ) {x : ℝ} (hx : 0 < x) : negMulLogDeriv (n + 2) x ≠ 0 := by
  simp only [negMulLogDeriv]
  have := Nat.factorial_pos n
  positivity

/-- **Lower bound for a sharp scalar entropy majorant.**  Let `A` be a finite set of at least two
interior nodes of `[0,1]` and `q` a real polynomial with `q ≥ -t log t` on `[0,1]` and
`q a = -a log a` at every node.  Then `2 |A| - 1 ≤ natDegree q`.  (Proved.) -/
theorem majorant_degree_lower_bound (A : Finset ℝ) (hA : 2 ≤ A.card)
    (hA01 : ∀ a ∈ A, 0 < a ∧ a < 1) (q : ℝ[X])
    (hq : ∀ t ∈ Icc (0:ℝ) 1, Real.negMulLog t ≤ q.eval t)
    (hint : ∀ a ∈ A, q.eval a = Real.negMulLog a) :
    2 * A.card - 1 ≤ q.natDegree := by
  by_contra hlt
  push Not at hlt
  -- the derivative sequence of `h = q - f`
  set g : ℕ → ℝ → ℝ := fun n x => (derivative^[n] q).eval x - negMulLogDeriv n x with hg
  have hgd : ∀ n, ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt (g n) (g (n + 1) x) x := by
    intro n x hx
    have h1 := Polynomial.hasDerivAt (derivative^[n] q) x
    have h2 := hasDerivAt_negMulLogDeriv n hx.1
    have := h1.fun_sub h2
    simpa only [hg, Function.iterate_succ_apply'] using this
  have hg0 : ∀ a ∈ A, g 0 a = 0 := fun a ha => by
    simp [hg, negMulLogDeriv, hint a ha]
  -- `h' = 0` at each node (interior minimum)
  have hg1 : ∀ a ∈ A, g 1 a = 0 := by
    intro a ha
    have hmin : IsLocalMin (g 0) a := by
      refine Filter.mem_of_superset (Icc_mem_nhds (hA01 a ha).1 (hA01 a ha).2) fun t ht => ?_
      have := hq t ht
      have h3 := hint a ha
      simp only [mem_ofPred_eq, hg, negMulLogDeriv]
      simp only [Function.iterate_zero, id_eq]
      linarith
    exact hmin.hasDerivAt_eq_zero (hgd 0 a ⟨(hA01 a ha).1, (hA01 a ha).2⟩)
  -- Rolle between the nodes
  obtain ⟨S, hSc, hS⟩ := rolle_step (hgd 0) A (A.card - 1)
    (fun a ha => ⟨hA01 a ha, hg0 a ha⟩) (by omega)
  have hdisj : Disjoint A S := Finset.disjoint_left.2 fun a haA haS => (hS a haS).2.1 haA
  have hcard : (A ∪ S).card = (2 * A.card - 2) + 1 := by
    rw [Finset.card_union_of_disjoint hdisj, hSc]; omega
  have hzs : ∀ y ∈ A ∪ S, y ∈ Ioo (0:ℝ) 1 ∧ (fun n => g (n + 1)) 0 y = 0 := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact ⟨hA01 y hy, hg1 y hy⟩
    · obtain ⟨h1, _, ⟨x, hx, hxy⟩, ⟨x', hx', hyx'⟩⟩ := hS y hy
      exact ⟨⟨by linarith [(hA01 x hx).1], by linarith [(hA01 x' hx').2]⟩, h1⟩
  obtain ⟨x, hx, hx0⟩ := exists_zero_iter (2 * A.card - 2) (fun n => g (n + 1))
    (fun n => hgd (n + 1)) (A ∪ S) hzs hcard
  obtain ⟨N, hN⟩ : ∃ N, 2 * A.card - 2 + 1 = N + 2 := ⟨2 * A.card - 3, by omega⟩
  have hx0' : g (N + 2) x = 0 := by
    have : g (2 * A.card - 2 + 1) x = 0 := hx0
    rwa [hN] at this
  have hzero : derivative^[N + 2] q = 0 :=
    Polynomial.iterate_derivative_eq_zero (by omega)
  simp only [hg, hzero, eval_zero, zero_sub, neg_eq_zero] at hx0'
  exact negMulLogDeriv_ne_zero N hx.1 hx0'

/-- The same lower bound for the base-2 entropy function `f(t) = -t log₂ t`. -/
theorem majorant_degree_lower_bound_logb_two (A : Finset ℝ) (hA : 2 ≤ A.card)
    (hA01 : ∀ a ∈ A, 0 < a ∧ a < 1) (q : ℝ[X])
    (hq : ∀ t ∈ Icc (0:ℝ) 1, -t * Real.logb 2 t ≤ q.eval t)
    (hint : ∀ a ∈ A, q.eval a = -a * Real.logb 2 a) :
    2 * A.card - 1 ≤ q.natDegree := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have key : ∀ t : ℝ, Real.log 2 * (-t * Real.logb 2 t) = Real.negMulLog t := fun t => by
    rw [Real.logb, Real.negMulLog]
    field_simp
  refine le_trans (majorant_degree_lower_bound A hA hA01 (C (Real.log 2) * q) ?_ ?_)
    (natDegree_C_mul_le _ _)
  · intro t ht
    rw [← key]
    simpa using mul_le_mul_of_nonneg_left (hq t ht) hl.le
  · intro a ha
    rw [← key]; simp [hint a ha]

end MajorantDegree

end FormalResearch.FourQubitEntropy
