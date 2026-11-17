module

public import FormalResearch.Jacobi.Basic

/-!
# Strict interlacing of the zeros of consecutive Jacobi polynomials

For a Jacobi matrix with nonzero links the monic polynomials `P_j = jacP b a j` of the leading
`j × j` blocks (three-term recurrence `P_{j+2} = (X - b_{j+1}) P_{j+1} - a_j² P_j`) satisfy the
classical Sturm / Cauchy interlacing, here proved from the recurrence alone (Cauchy interlacing for
general Hermitian matrices is not in Mathlib; for tridiagonal matrices the recurrence suffices):

`jacP_interlacing` : for `1 ≤ m ≤ n` (all links `a_0 … a_{m-2}` nonzero) there are `μ_0 … μ_{m-2}`,
`θ_0 … θ_{m-1}` with `P_{m-1} = ∏ (X - μ_i)`, `P_m = ∏ (X - θ_i)` and
`θ_0 < μ_0 < θ_1 < μ_1 < ⋯ < μ_{m-2} < θ_{m-1}`.
In particular `P_m` has `m` distinct real zeros, i.e. a Jacobi matrix with nonzero links has simple
real spectrum, and its zeros strictly interlace those of the next-smaller leading block.

Source: Weyl P5 `dirichlet_block_audit.md`, proof of Theorem SP ("Strict Jacobi interlacing puts the
zeros `θ_i` of `P_{n-1}` in `λ_0 < θ_0 < λ_1 < ⋯ < θ_{n-2} < λ_{n-1}`").

Claim class: proved.  The induction is the standard one: at the zeros `θ_k` of `P_{m+1}` the
recurrence gives `P_{m+2}(θ_k) = -a_m² P_m(θ_k)`, whose sign alternates by the induction hypothesis;
the intermediate value theorem produces a zero in every gap and beyond both ends, and `m + 2` zeros of
a monic polynomial of degree `m + 2` are all of them.
-/

@[expose] public section

namespace FormalResearch.Jacobi

open Polynomial Finset

/-- `p` is the monic polynomial with the first `m` entries of `θ` as zeros. -/
def RootSeq (p : ℝ[X]) (m : ℕ) (θ : ℕ → ℝ) : Prop := p = ∏ i ∈ range m, (X - C (θ i))

/-- Strict interlacing `θ_0 < μ_0 < θ_1 < ⋯ < μ_{m-1} < θ_m`. -/
def Interlaces (m : ℕ) (μ θ : ℕ → ℝ) : Prop := ∀ k, k < m → θ k < μ k ∧ μ k < θ (k + 1)

namespace Interlaces

variable {m : ℕ} {μ θ : ℕ → ℝ}

theorem theta_strictMono (h : Interlaces m μ θ) {i j : ℕ} (hij : i < j) (hj : j ≤ m) :
    θ i < θ j := by
  induction j with
  | zero => omega
  | succ j ih =>
    have h1 := (h j (by omega)).1.trans (h j (by omega)).2
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt | heq
    · exact (ih hlt (by omega)).trans h1
    · rw [heq]; exact h1

theorem theta_mono (h : Interlaces m μ θ) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m) : θ i ≤ θ j := by
  rcases hij.lt_or_eq with hlt | heq
  · exact (h.theta_strictMono hlt hj).le
  · rw [heq]

theorem mu_strictMono (h : Interlaces m μ θ) {i j : ℕ} (hij : i < j) (hj : j < m) :
    μ i < μ j := by
  have h1 := (h i (by omega)).2
  have h2 := (h j hj).1
  have := h.theta_mono (by omega : i + 1 ≤ j) (by omega)
  linarith

theorem mu_mono (h : Interlaces m μ θ) {i j : ℕ} (hij : i ≤ j) (hj : j < m) : μ i ≤ μ j := by
  rcases hij.lt_or_eq with hlt | heq
  · exact (h.mu_strictMono hlt hj).le
  · rw [heq]

/-- Sign of `∏_{i<m} (θ_k - μ_i)` at `θ_k`: `(-1)^{m-k}`. -/
theorem sign_prod (h : Interlaces m μ θ) {k : ℕ} (hk : k ≤ m) :
    0 < (-1 : ℝ) ^ (m - k) * ∏ i ∈ range m, (θ k - μ i) := by
  rw [← prod_range_mul_prod_Ico _ hk]
  have h1 : 0 < ∏ i ∈ range k, (θ k - μ i) := by
    apply prod_pos
    intro i hi
    have hi' := mem_range.mp hi
    have := (h i (by omega)).2
    have := h.theta_mono (by omega : i + 1 ≤ k) hk
    linarith
  have h2 : ∏ i ∈ Ico k m, (θ k - μ i) = (-1) ^ (m - k) * ∏ i ∈ Ico k m, (μ i - θ k) := by
    have : ∀ i ∈ Ico k m, θ k - μ i = (-1) * (μ i - θ k) := fun i _ => by ring
    rw [prod_congr rfl this, prod_mul_distrib, prod_const, Nat.card_Ico]
  have h3 : 0 < ∏ i ∈ Ico k m, (μ i - θ k) := by
    apply prod_pos
    intro i hi
    have hi' := mem_Ico.mp hi
    have := (h k (by omega)).1
    have := h.mu_mono hi'.1 hi'.2
    linarith
  rw [h2]
  have : (-1 : ℝ) ^ (m - k) * ((∏ i ∈ range k, (θ k - μ i)) *
      ((-1) ^ (m - k) * ∏ i ∈ Ico k m, (μ i - θ k))) =
      (∏ i ∈ range k, (θ k - μ i)) * ∏ i ∈ Ico k m, (μ i - θ k) := by
    rw [← mul_assoc, mul_comm ((-1 : ℝ) ^ (m - k)), mul_assoc, ← mul_assoc ((-1 : ℝ) ^ (m - k)),
      ← mul_pow]
    simp
  rw [this]
  exact mul_pos h1 h3

end Interlaces

/-! ### Real-analysis helpers -/

theorem exists_root_of_sign_change {p : ℝ[X]} {x y : ℝ} (hxy : x < y)
    (h : p.eval x * p.eval y < 0) : ∃ z, x < z ∧ z < y ∧ p.eval z = 0 := by
  have hc : ContinuousOn (fun t => p.eval t) (Set.Icc x y) := p.continuous.continuousOn
  rcases lt_or_gt_of_ne (show p.eval x ≠ 0 by rintro h0; simp [h0] at h) with hx | hx
  · have hy : 0 < p.eval y := by
      by_contra hy; have hy := not_lt.mp hy; nlinarith
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo hxy.le hc (show (0 : ℝ) ∈ Set.Ioo _ _ from ⟨hx, hy⟩)
    exact ⟨z, hz.1, hz.2, hz0⟩
  · have hy : p.eval y < 0 := by
      by_contra hy; have hy := not_lt.mp hy; nlinarith
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo' hxy.le hc (show (0 : ℝ) ∈ Set.Ioo _ _ from ⟨hy, hx⟩)
    exact ⟨z, hz.1, hz.2, hz0⟩

theorem monic_pos_atTop {p : ℝ[X]} (hp : p.Monic) (hd : 0 < p.natDegree) :
    ∃ R, ∀ x, R ≤ x → 0 < p.eval x := by
  have ht := Polynomial.tendsto_atTop_of_leadingCoeff_nonneg p (by
    rw [degree_eq_natDegree hp.ne_zero]; exact_mod_cast hd) (by rw [hp.leadingCoeff]; norm_num)
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp (ht.eventually_gt_atTop 0)
  exact ⟨R, hR⟩

theorem monic_sign_atBot {p : ℝ[X]} (hp : p.Monic) (hd : 0 < p.natDegree) :
    ∃ R, ∀ x, x ≤ R → 0 < (-1 : ℝ) ^ p.natDegree * p.eval x := by
  set q : ℝ[X] := (-1) ^ p.natDegree * p.comp (-X) with hq
  have hqm : q.Monic := hp.neg_one_pow_natDegree_mul_comp_neg_X
  have hqd : 0 < q.natDegree := by
    have hc : (-1 : ℝ[X]) ^ p.natDegree = C ((-1 : ℝ) ^ p.natDegree) := by simp
    rw [hq, hc, natDegree_C_mul (pow_ne_zero _ (by norm_num)), natDegree_comp]
    simp [hd]
  obtain ⟨R, hR⟩ := monic_pos_atTop hqm hqd
  refine ⟨-R, fun x hx => ?_⟩
  have := hR (-x) (by linarith)
  simpa [hq] using this

/-- The sign alternation turned into a strict sign change. -/
theorem mul_neg_of_alt {s x y : ℝ} (hs : s ^ 2 = 1) (h1 : 0 < s * x) (h2 : 0 < -s * y) :
    x * y < 0 := by
  have e : (s * x) * (-s * y) = -(x * y) := by linear_combination (-(x * y)) * hs
  have := mul_pos h1 h2
  linarith

/-- One interlacing step: from `P_m, P_{m+1}` interlaced to `P_{m+1}, P_{m+2}` interlaced. -/
theorem interlace_step {m : ℕ} {b a : ℕ → ℝ} (hm : a m ≠ 0) {μ θ : ℕ → ℝ}
    (hμ : RootSeq (jacP b a m) m μ) (hθ : RootSeq (jacP b a (m + 1)) (m + 1) θ)
    (hI : Interlaces m μ θ) :
    ∃ ν : ℕ → ℝ, RootSeq (jacP b a (m + 2)) (m + 2) ν ∧ Interlaces (m + 1) θ ν := by
  set P := jacP b a (m + 2) with hP
  have hPm : P.Monic := jacP_monic b a _
  have hPd : P.natDegree = m + 2 := jacP_natDegree b a _
  -- values at the zeros `θ_k`
  have hval : ∀ k, k ≤ m → 0 < (-1 : ℝ) ^ (m + 1 - k) * P.eval (θ k) := by
    intro k hk
    have h1 : (jacP b a (m + 1)).eval (θ k) = 0 := by
      rw [hθ, eval_prod]
      exact prod_eq_zero (i := k) (mem_range.mpr (by omega)) (by simp)
    have h2 : (jacP b a m).eval (θ k) = ∏ i ∈ range m, (θ k - μ i) := by
      rw [hμ, eval_prod]; simp
    have h3 : P.eval (θ k) = -(a m ^ 2) * ∏ i ∈ range m, (θ k - μ i) := by
      rw [hP, jacP_succ_succ, eval_sub, eval_mul, h1, eval_mul, eval_C, h2]
      simp
    have h4 := hI.sign_prod hk
    have h5 : (-1 : ℝ) ^ (m + 1 - k) = -(-1) ^ (m - k) := by
      rw [show m + 1 - k = (m - k) + 1 by omega, pow_succ]; ring
    rw [h3, h5]
    have h6 : 0 < a m ^ 2 := by positivity
    have := mul_pos h6 h4
    nlinarith
  have hsq : ∀ k : ℕ, ((-1 : ℝ) ^ k) ^ 2 = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  -- existence of the new zeros
  have hex : ∀ i : ℕ, ∃ z : ℝ, i ≤ m + 1 →
      (P.eval z = 0 ∧ (0 < i → θ (i - 1) < z) ∧ (i ≤ m → z < θ i)) := by
    intro i
    by_cases hi : i ≤ m + 1
    swap
    · exact ⟨0, fun h => absurd h hi⟩
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      obtain ⟨R, hR⟩ := monic_sign_atBot hPm (by omega)
      rw [hPd] at hR
      have hx := hR (min R (θ 0 - 1)) (min_le_left _ _)
      have hlt : min R (θ 0 - 1) < θ 0 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hneg : P.eval (min R (θ 0 - 1)) * P.eval (θ 0) < 0 := by
        have := hval 0 (by omega)
        simp only [Nat.sub_zero] at this
        have hs : ((-1 : ℝ) ^ (m + 1)) = -(-1) ^ (m + 2) := by rw [pow_succ _ (m + 1)]; ring
        rw [hs] at this
        exact mul_neg_of_alt (hsq (m + 2)) hx (by linarith)
      obtain ⟨z, hz1, hz2, hz3⟩ := exists_root_of_sign_change hlt hneg
      exact ⟨z, fun _ => ⟨hz3, fun h => absurd h (lt_irrefl 0), fun _ => hz2⟩⟩
    · by_cases hlast : i = m + 1
      · subst hlast
        obtain ⟨R, hR⟩ := monic_pos_atTop hPm (by omega)
        have hx := hR (max R (θ m + 1)) (le_max_left _ _)
        have hlt : θ m < max R (θ m + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
        have hneg : P.eval (θ m) * P.eval (max R (θ m + 1)) < 0 := by
          have := hval m le_rfl
          simp only [Nat.add_sub_cancel_left, pow_one] at this
          nlinarith
        obtain ⟨z, hz1, hz2, hz3⟩ := exists_root_of_sign_change hlt hneg
        exact ⟨z, fun _ => ⟨hz3, fun _ => by simpa using hz1, fun h => absurd h (by omega)⟩⟩
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        have hi' : i' + 1 ≤ m := by omega
        have h1 := hval i' (by omega)
        have h2 := hval (i' + 1) hi'
        have hlt : θ i' < θ (i' + 1) := hI.theta_strictMono (by omega) (by omega)
        have hs : ((-1 : ℝ) ^ (m + 1 - i')) = -(-1) ^ (m + 1 - (i' + 1)) := by
          rw [show m + 1 - i' = (m + 1 - (i' + 1)) + 1 by omega, pow_succ]; ring
        rw [hs] at h1
        have hneg : P.eval (θ i') * P.eval (θ (i' + 1)) < 0 := by
          rw [mul_comm]; exact mul_neg_of_alt (hsq _) h2 h1
        obtain ⟨z, hz1, hz2, hz3⟩ := exists_root_of_sign_change hlt hneg
        exact ⟨z, fun _ => ⟨hz3, fun _ => by simpa using hz1, fun _ => hz2⟩⟩
  choose ν hν using hex
  have hint : Interlaces (m + 1) θ ν := by
    intro k hk
    refine ⟨(hν k (by omega)).2.2 (by omega), ?_⟩
    have := (hν (k + 1) (by omega)).2.1 (by omega)
    simpa using this
  refine ⟨ν, ?_, hint⟩
  -- `P = ∏ (X - ν_i)` : `m + 2` distinct zeros of a monic polynomial of degree `m + 2`
  have hinj : Set.InjOn ν (range (m + 2) : Finset ℕ) := by
    intro i hi j hj hij
    have hi' := mem_range.mp (mem_coe.mp hi)
    have hj' := mem_range.mp (mem_coe.mp hj)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hint.theta_strictMono hlt (by omega); linarith
    · have := hint.theta_strictMono hlt (by omega); linarith
  have hcard : ((range (m + 2)).image ν).card = m + 2 := by
    rw [card_image_of_injOn hinj, card_range]
  have hQm : (∏ i ∈ range (m + 2), (X - C (ν i))).Monic :=
    monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)
  have hQd : (∏ i ∈ range (m + 2), (X - C (ν i))).natDegree = m + 2 := by
    simp
  unfold RootSeq
  apply eq_of_degree_sub_lt_of_eval_finset_eq (s := (range (m + 2)).image ν)
  · rw [hcard]
    have := degree_sub_lt_left (p := P) (q := ∏ i ∈ range (m + 2), (X - C (ν i)))
      (by rw [degree_eq_natDegree hPm.ne_zero, degree_eq_natDegree hQm.ne_zero, hPd, hQd])
      hPm.ne_zero (by rw [hPm.leadingCoeff, hQm.leadingCoeff])
    refine lt_of_lt_of_eq this ?_
    rw [degree_eq_natDegree hPm.ne_zero, hPd]
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    have hi' := mem_range.mp hi
    rw [(hν i (by omega)).1, eval_prod]
    exact (prod_eq_zero hi (by simp)).symm

/-- **Strict interlacing of consecutive Jacobi polynomials.**  If `a_0, …, a_{m-1}` are nonzero then
`P_m` and `P_{m+1}` have the simple real zeros `μ_0 < ⋯ < μ_{m-1}` and `θ_0 < ⋯ < θ_m` with
`θ_0 < μ_0 < θ_1 < ⋯ < μ_{m-1} < θ_m`. -/
theorem jacP_interlacing (b a : ℕ → ℝ) (m : ℕ) (ha : ∀ j, j < m → a j ≠ 0) :
    ∃ μ θ : ℕ → ℝ, RootSeq (jacP b a m) m μ ∧ RootSeq (jacP b a (m + 1)) (m + 1) θ ∧
      Interlaces m μ θ := by
  induction m with
  | zero =>
    refine ⟨fun _ => 0, fun _ => b 0, ?_, ?_, fun k hk => absurd hk (by omega)⟩
    · simp [RootSeq]
    · simp [RootSeq, jacP_one]
  | succ m ih =>
    obtain ⟨μ, θ, hμ, hθ, hI⟩ := ih (fun j hj => ha j (by omega))
    obtain ⟨ν, hν, hint⟩ := interlace_step (ha m (by omega)) hμ hθ hI
    exact ⟨θ, ν, hθ, hν, hint⟩

/-- info: 'FormalResearch.Jacobi.jacP_interlacing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacP_interlacing

end FormalResearch.Jacobi
