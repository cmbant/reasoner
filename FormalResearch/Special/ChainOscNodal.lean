module

public import FormalResearch.Special.ChainOscCount

/-!
# Chain oscillation, part 2: the nodal (sign-change) form of Sturm oscillation for Jacobi matrices

For a finite real Jacobi matrix `J_{m+1}` (diagonal `b`, off-diagonal `a`) with **positive** links
`a_0, …, a_{m-1} > 0`, and an eigenvalue `λ` having exactly `k` eigenvalues strictly below it
(the `k`-th eigenvalue in ascending order, 0-indexed), every eigenvector `v` has exactly `m - k`
nodes, `cho_nodal (extVec v) m = m - k`, where the nodal count of a sequence `u` is

  `#{ j < m : u_j u_{j+1} < 0 } + #{ 0 < j < m : u_j = 0 }`

(a sign change between neighbours, or an interior zero, which by the recurrence is always flanked by
entries of opposite signs, so it is exactly one sign change).  Equivalently the `j`-th eigenvalue
from the top (`j = m - k`) has `j` sign changes (the top eigenvector, Perron–Frobenius, has none).

Main results.

* `cho_sturm_count` : for every real `x` and every `j`, the nodal count of the Sturm sequence
  `P_0(x), …, P_j(x)` equals the number of zeros of `P_j` strictly above `x` (any `x`, zeros allowed);
  this is the classical Sturm theorem, proved here from `Jacobi.jacP_interlacing` and the counting
  lemma `cho_count_step`.
* `cho_nodal_eigenvector` : the eigenvector statement above.

Claim class: proved.  Not formalised: the physical instantiation (that the `3j` / `6j` Hahn and Racah
chains are the eigenvectors of such Jacobi matrices with spectrum the physical lattice
`x_n = xLat n`, hence have `m - n` nodes) and the comparison with the Airy phase
(see the handoff of round 39).
-/

@[expose] public section

namespace FormalResearch.Special

open FormalResearch.Jacobi Finset Polynomial Matrix

/-- Nodal count of `u_0, …, u_m`: sign changes `u_j u_{j+1} < 0` plus interior zeros. -/
noncomputable def cho_nodal (u : ℕ → ℝ) (m : ℕ) : ℕ :=
  ((range m).filter (fun j => u j * u (j + 1) < 0)).card +
    ((range m).filter (fun j => 0 < j ∧ u j = 0)).card

theorem cho_nodal_zero (u : ℕ → ℝ) : cho_nodal u 0 = 0 := by simp [cho_nodal]

theorem cho_nodal_succ (u : ℕ → ℝ) (m : ℕ) :
    cho_nodal u (m + 1) = cho_nodal u m + (if u m * u (m + 1) < 0 then 1 else 0) +
      (if 0 < m ∧ u m = 0 then 1 else 0) := by
  unfold cho_nodal
  rw [Finset.range_add_one, filter_insert, filter_insert]
  by_cases h1 : u m * u (m + 1) < 0 <;> by_cases h2 : 0 < m ∧ u m = 0 <;>
    simp [h1, h2, card_insert_of_notMem] <;> omega

/-- Two root sequences of the same polynomial give the same count. -/
theorem cho_cnt_rootSeq {p : ℝ[X]} {n : ℕ} {f g : ℕ → ℝ} (hf : RootSeq p n f) (hg : RootSeq p n g)
    (x : ℝ) : cho_cnt f n x = cho_cnt g n x := by
  have key : ∀ h : ℕ → ℝ, RootSeq p n h → p.roots = (range n).val.map h := by
    intro h hh
    have e : (range n).val.map (fun i => X - C (h i)) = ((range n).val.map h).map (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [hh, Finset.prod_eq_multiset_prod, e, roots_multiset_prod_X_sub_C]
  have hm : (range n).val.map f = (range n).val.map g := by rw [← key f hf, ← key g hg]
  have cnt : ∀ h : ℕ → ℝ, cho_cnt h n x = Multiset.card (((range n).val.map h).filter (fun y => x < y)) := by
    intro h
    unfold cho_cnt
    rw [Multiset.filter_map, Multiset.card_map]
    rfl
  rw [cnt f, cnt g, hm]

/-- **Sturm's theorem for the recurrence polynomials**, in nodal form: the number of nodes of
`P_0(x), …, P_j(x)` equals the number of zeros of `P_j` strictly greater than `x`. -/
theorem cho_sturm_count (b a : ℕ → ℝ) (x : ℝ) :
    ∀ j : ℕ, (∀ i, i < j → a i ≠ 0) → ∀ μ : ℕ → ℝ, RootSeq (jacP b a j) j μ →
      cho_nodal (fun i => (jacP b a i).eval x) j = cho_cnt μ j x := by
  intro j
  induction j with
  | zero => intro _ μ _; simp [cho_nodal_zero, cho_cnt_zero]
  | succ j ih =>
    intro ha θ hθ
    have ha0 : ∀ i, i < j → a i ≠ 0 := fun i hi => ha i (by omega)
    obtain ⟨μ', θ', hμ', hθ', hI⟩ := jacP_interlacing b a j ha0
    have IH := ih ha0 μ' hμ'
    have hθc := cho_cnt_rootSeq hθ hθ' x
    obtain ⟨F1, F2, F3, F4⟩ := cho_count_step (μ := μ') (θ := θ') x j hI
    rw [hθc, cho_nodal_succ, IH]
    set Pj := (jacP b a j).eval x with hPj
    set Pj1 := (jacP b a (j + 1)).eval x with hPj1
    have zj : Pj = 0 ↔ ∃ i, i < j ∧ μ' i = x := by
      rw [hPj, rootSeq_eval_eq_zero_iff hμ' x]
    have zj1 : Pj1 = 0 ↔ ∃ i, i < j + 1 ∧ θ' i = x := by
      rw [hPj1, rootSeq_eval_eq_zero_iff hθ' x]
    by_cases h0 : Pj = 0
    · -- `P_j(x) = 0`, hence `j > 0`
      have hjpos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with rfl | h
        · exfalso; simp [hPj] at h0
        · exact h
      have := F3 (zj.mp h0)
      rw [h0, zero_mul, cho_if_neg (lt_irrefl _), cho_if_pos ⟨hjpos, rfl⟩]
      omega
    · by_cases h1 : Pj1 = 0
      · have := F4 (zj1.mp h1)
        have e : ¬ Pj * Pj1 < 0 := by rw [h1, mul_zero]; exact lt_irrefl _
        have e2 : ¬ (0 < j ∧ Pj = 0) := fun h => h0 h.2
        rw [cho_if_neg e, cho_if_neg e2]; omega
      · -- both nonzero: sign rule
        have s1 := cho_sign_prod μ' x j (fun i hi h => h0 (zj.mpr ⟨i, hi, h⟩))
        have s2 := cho_sign_prod θ' x (j + 1) (fun i hi h => h1 (zj1.mpr ⟨i, hi, h⟩))
        have ev1 : Pj = ∏ i ∈ range j, (x - μ' i) := by
          rw [hPj, hμ', eval_prod]; simp
        have ev2 : Pj1 = ∏ i ∈ range (j + 1), (x - θ' i) := by
          rw [hPj1, hθ', eval_prod]; simp
        rw [← ev1] at s1
        rw [← ev2] at s2
        have e2 : ¬ (0 < j ∧ Pj = 0) := fun h => h0 h.2
        rw [cho_if_neg e2, add_zero]
        rcases (by omega : cho_cnt θ' (j + 1) x = cho_cnt μ' j x ∨
            cho_cnt θ' (j + 1) x = cho_cnt μ' j x + 1) with e | e
        · rw [e] at s2
          have : 0 < Pj * Pj1 := by
            have : 0 < ((-1 : ℝ) ^ cho_cnt μ' j x * Pj) * ((-1 : ℝ) ^ cho_cnt μ' j x * Pj1) :=
              mul_pos s1 s2
            nlinarith [this, show ((-1 : ℝ) ^ cho_cnt μ' j x) ^ 2 = 1 by rw [← pow_mul, mul_comm, pow_mul]; simp]
          rw [cho_if_neg (not_lt.mpr this.le)]; omega
        · rw [e, pow_succ] at s2
          have : Pj * Pj1 < 0 := by
            have : 0 < ((-1 : ℝ) ^ cho_cnt μ' j x * Pj) * ((-1 : ℝ) ^ cho_cnt μ' j x * (-1) * Pj1) :=
              mul_pos s1 s2
            nlinarith [this, show ((-1 : ℝ) ^ cho_cnt μ' j x) ^ 2 = 1 by rw [← pow_mul, mul_comm, pow_mul]; simp]
          rw [cho_if_pos this]; omega

/-- **Nodal Sturm oscillation for Jacobi eigenvectors.**  Let `J_{m+1}` have positive links
`a_0, …, a_{m-1}`, let `λ` be an eigenvalue with exactly `k` eigenvalues strictly below it, and `v` an
eigenvector.  Then the sequence `v_0, …, v_m` has exactly `m - k` nodes (sign changes, an interior zero
counting as one sign change).  In particular the top eigenvector (`k = m`) has none, and the
bottom one (`k = 0`) alternates in sign (`m` nodes). -/
theorem cho_nodal_eigenvector (m : ℕ) {b a : ℕ → ℝ} (ha : ∀ j, j < m → 0 < a j) {lam : ℝ} {k : ℕ}
    (hk : {x : ℝ | IsEigenval (jacobiMatrix (m + 1) b a) x ∧ x < lam}.ncard = k)
    {v : Fin (m + 1) → ℝ} (hv0 : v ≠ 0) (hv : jacobiMatrix (m + 1) b a *ᵥ v = lam • v) :
    cho_nodal (extVec v) m = m - k := by
  have haN : ∀ j, j < m → a j ≠ 0 := fun j hj => (ha j hj).ne'
  have haN' : ∀ j, j + 1 < m + 1 → a j ≠ 0 := fun j hj => haN j (by omega)
  obtain ⟨μ, θ, hμ, hθ, hI⟩ := jacP_interlacing b a m haN
  have hroot : (jacP b a (m + 1)).eval lam = 0 := eval_jacP_eq_zero_of_eigen haN' hv hv0
  obtain ⟨k0, hk0, hθk0⟩ := (rootSeq_eval_eq_zero_iff hθ lam).mp hroot
  have hset : {x : ℝ | IsEigenval (jacobiMatrix (m + 1) b a) x ∧ x < lam} =
      ↑((range k0).image θ) := by
    ext x
    simp only [Set.mem_ofPred_eq, coe_image, coe_range, Set.mem_image, Set.mem_Iio]
    rw [jacobi_isEigenval_iff haN', rootSeq_eval_eq_zero_iff hθ]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hlt⟩
      refine ⟨i, ?_, rfl⟩
      by_contra hge
      have := hI.theta_mono (by omega : k0 ≤ i) (by omega)
      linarith
    · rintro ⟨i, hi, rfl⟩
      refine ⟨⟨i, by omega, rfl⟩, ?_⟩
      rw [← hθk0]
      exact hI.theta_strictMono hi (by omega)
  have hinj : Set.InjOn θ (range k0 : Finset ℕ) := by
    intro i hi j hj hij
    have hi' := mem_range.mp (mem_coe.mp hi)
    have hj' := mem_range.mp (mem_coe.mp hj)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hI.theta_strictMono hlt (by omega); linarith
    · have := hI.theta_strictMono hlt (by omega); linarith
  have hkk : k0 = k := by
    rw [hset, Set.ncard_coe_finset, card_image_of_injOn hinj, card_range] at hk
    exact hk
  subst hkk
  -- the count of zeros of `P_m` above `λ = θ_{k0}`
  have hcnt : cho_cnt μ m lam = m - k0 := by
    unfold cho_cnt
    have : (range m).filter (fun i => lam < μ i) = Ico k0 m := by
      ext i
      simp only [mem_filter, mem_range, mem_Ico]
      constructor
      · rintro ⟨hi, h⟩
        refine ⟨?_, hi⟩
        by_contra hlt
        have h1 := (hI i hi).2
        have h2 := hI.theta_mono (by omega : i + 1 ≤ k0) (by omega)
        linarith
      · rintro ⟨h1, h2⟩
        refine ⟨h2, ?_⟩
        have := (hI k0 (by omega)).1
        have := hI.mu_mono h1 h2
        linarith
    rw [this, Nat.card_Ico]
  have hS := cho_sturm_count b a lam m haN μ hμ
  rw [hcnt] at hS
  rw [← hS]
  -- compare the eigenvector with the Sturm sequence
  have hprod := eigen_prod_eq (m + 1) b a (extVec v) lam (eigenvec_row hv)
  have hu0 : extVec v 0 ≠ 0 := eigenvec_zero_ne haN' hv hv0
  have hw : ∀ i, i ≤ m → 0 < ∏ l ∈ range i, a l := fun i hi =>
    prod_pos fun l hl => ha l (by have := mem_range.mp hl; omega)
  have hzero : ∀ i, i < m → (extVec v i = 0 ↔ (jacP b a i).eval lam = 0) := by
    intro i hi
    have e1 := hprod i (by omega)
    have w1 := hw i (by omega)
    constructor
    · intro h
      rw [h, zero_mul] at e1
      exact (mul_eq_zero.mp e1.symm).resolve_left hu0
    · intro h
      rw [h, mul_zero] at e1
      exact (mul_eq_zero.mp e1).resolve_right w1.ne'
  have hneg : ∀ i, i < m →
      (extVec v i * extVec v (i + 1) < 0 ↔ (jacP b a i).eval lam * (jacP b a (i + 1)).eval lam < 0) := by
    intro i hi
    have e1 := hprod i (by omega)
    have e2 := hprod (i + 1) (by omega)
    rw [prod_range_succ] at e2
    have w1 := hw i (by omega)
    have w2 := hw (i + 1) (by omega)
    rw [prod_range_succ] at w2
    have key : (extVec v i * extVec v (i + 1)) * ((∏ l ∈ range i, a l) * ((∏ l ∈ range i, a l) * a i)) =
        (extVec v 0) ^ 2 * ((jacP b a i).eval lam * (jacP b a (i + 1)).eval lam) := by
      have : (extVec v i * extVec v (i + 1)) * ((∏ l ∈ range i, a l) * ((∏ l ∈ range i, a l) * a i)) =
          (extVec v i * ∏ l ∈ range i, a l) * (extVec v (i + 1) * ((∏ l ∈ range i, a l) * a i)) := by ring
      rw [this, e1, e2]; ring
    have hc : 0 < (∏ l ∈ range i, a l) * ((∏ l ∈ range i, a l) * a i) := mul_pos w1 w2
    have hu2 : 0 < (extVec v 0) ^ 2 := by positivity
    constructor
    · intro h
      have : (extVec v i * extVec v (i + 1)) * ((∏ l ∈ range i, a l) * ((∏ l ∈ range i, a l) * a i)) < 0 :=
        mul_neg_of_neg_of_pos h hc
      rw [key] at this
      by_contra hn
      push Not at hn
      nlinarith [mul_nonneg hu2.le hn]
    · intro h
      have : (extVec v 0) ^ 2 * ((jacP b a i).eval lam * (jacP b a (i + 1)).eval lam) < 0 :=
        mul_neg_of_pos_of_neg hu2 h
      rw [← key] at this
      by_contra hn
      push Not at hn
      nlinarith [mul_nonneg hn hc.le]
  unfold cho_nodal
  congr 1
  · apply congrArg
    apply filter_congr
    intro i hi
    exact hneg i (mem_range.mp hi)
  · apply congrArg
    apply filter_congr
    intro i hi
    rw [hzero i (mem_range.mp hi)]

/-- info: 'FormalResearch.Special.cho_nodal_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cho_nodal_eigenvector

/-- info: 'FormalResearch.Special.cho_sturm_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cho_sturm_count

/-- **Ascending eigenvalues with their nodal counts.**  For positive links, the spectrum of `J_{m+1}` is
a strictly increasing list `θ_0 < ⋯ < θ_m`, and every eigenvector for `θ_i` has exactly `m - i` nodes. -/
theorem cho_eigen_ascending (m : ℕ) {b a : ℕ → ℝ} (ha : ∀ j, j < m → 0 < a j) :
    ∃ θ : ℕ → ℝ, (∀ i j, i < j → j ≤ m → θ i < θ j) ∧
      (∀ x, IsEigenval (jacobiMatrix (m + 1) b a) x ↔ ∃ i, i ≤ m ∧ θ i = x) ∧
      ∀ i, i ≤ m → ∀ v : Fin (m + 1) → ℝ, v ≠ 0 →
        jacobiMatrix (m + 1) b a *ᵥ v = θ i • v → cho_nodal (extVec v) m = m - i := by
  have haN : ∀ j, j < m → a j ≠ 0 := fun j hj => (ha j hj).ne'
  have haN' : ∀ j, j + 1 < m + 1 → a j ≠ 0 := fun j hj => haN j (by omega)
  obtain ⟨μ, θ, hμ, hθ, hI⟩ := jacP_interlacing b a m haN
  have hE : ∀ x, IsEigenval (jacobiMatrix (m + 1) b a) x ↔ ∃ i, i ≤ m ∧ θ i = x := by
    intro x
    rw [jacobi_isEigenval_iff haN', rootSeq_eval_eq_zero_iff hθ]
    exact ⟨fun ⟨i, hi, h⟩ => ⟨i, by omega, h⟩, fun ⟨i, hi, h⟩ => ⟨i, by omega, h⟩⟩
  refine ⟨θ, fun i j hij hj => hI.theta_strictMono hij hj, hE, ?_⟩
  intro i hi v hv0 hv
  apply cho_nodal_eigenvector m ha _ hv0 hv
  have hset : {x : ℝ | IsEigenval (jacobiMatrix (m + 1) b a) x ∧ x < θ i} =
      ↑((range i).image θ) := by
    ext x
    simp only [Set.mem_ofPred_eq, coe_image, coe_range, Set.mem_image, Set.mem_Iio]
    rw [hE]
    constructor
    · rintro ⟨⟨l, hl, rfl⟩, hlt⟩
      refine ⟨l, ?_, rfl⟩
      by_contra hge
      have := hI.theta_mono (by omega : i ≤ l) hl
      linarith
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, by omega, rfl⟩, hI.theta_strictMono hl hi⟩
  have hinj : Set.InjOn θ (range i : Finset ℕ) := by
    intro p hp q hq hpq
    have hp' := mem_range.mp (mem_coe.mp hp)
    have hq' := mem_range.mp (mem_coe.mp hq)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hI.theta_strictMono hlt (by omega); linarith
    · have := hI.theta_strictMono hlt (by omega); linarith
  rw [hset, Set.ncard_coe_finset, card_image_of_injOn hinj, card_range]

/-- info: 'FormalResearch.Special.cho_eigen_ascending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cho_eigen_ascending

end FormalResearch.Special
