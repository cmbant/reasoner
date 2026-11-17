module

public import FormalResearch.Jacobi.Basic

/-!
# Theorem ER: eigenvector reconstruction by the recurrence (Weyl P5/M7, general Jacobi form)

Source: `Weyl/P5/notes/m7_review_and_open_gates.md` §B, Theorem ER, eqs. (ER.1)–(ER.2) (PR 250,
head `cfad461d2`).  For a real Jacobi matrix with diagonal `b_j` and nonzero links `t_j = a_j`
and a spectral parameter `λ`, put

`q_0 = 1`, `q_1 = (λ - b_0)/a_0`, `q_{j+1} = ((λ - b_j) q_j - a_{j-1} q_{j-1}) / a_j`   (ER.1)

(`jacQ b a lam`).  Then `q_j = P_j(λ) / ∏_{i<j} a_i` (`jacQ_eq`), and

* `jacobi_reconstruct` : **(ER.2)** every unit eigenvector `v` of `J_n` for `λ` whose first
  component has the sign `σ ∈ {±1}` (`σ v_0 > 0`) equals `σ q / ‖q‖₂` exactly;
* `jacobi_reconstruct_eigenvec` : conversely, if `P_n(λ) = 0` then `q/‖q‖₂` is a unit eigenvector
  (the recurrence closes at the last site exactly when `λ` is an eigenvalue).

Claim class: proved.  What the physical statement needs and is NOT formalised: that the Wigner `6j`
transform `U` satisfies `J U = U diag(d(d+1))` with `J` an irreducible Jacobi matrix with explicit
nonzero links (the exact W2 link formula or SF.5), and the border parity `σ_d = (-1)^{z_0+d-d_0}` of
R0(d); here these enter as the hypotheses `ha` and the sign `σ`.  The `O(n²)` operation count and the
floating-point instability remark of the note are not formalised.
-/

@[expose] public section

namespace FormalResearch.Jacobi

open Matrix Polynomial Finset

/-- The recurrence (ER.1): `q_0 = 1`, `q_1 = (λ - b_0)/a_0`,
`q_{j+2} = ((λ - b_{j+1}) q_{j+1} - a_j q_j) / a_{j+1}`. -/
noncomputable def jacQ (b a : ℕ → ℝ) (lam : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => (lam - b 0) / a 0
  | (j + 2) => ((lam - b (j + 1)) * jacQ b a lam (j + 1) - a j * jacQ b a lam j) / a (j + 1)

/-- `q_j = P_j(λ) / ∏_{i<j} a_i` whenever the links `a_0, …, a_{j-1}` are nonzero. -/
theorem jacQ_eq (b a : ℕ → ℝ) (lam : ℝ) :
    ∀ j, (∀ i, i < j → a i ≠ 0) → jacQ b a lam j = (jacP b a j).eval lam / ∏ i ∈ range j, a i := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro ha
    match j, ih, ha with
    | 0, _, _ => simp [jacQ]
    | 1, _, ha =>
      have := ha 0 (by omega)
      simp [jacQ, jacP_one]
    | (j + 2), ih, ha =>
      have e1 := ih (j + 1) (by omega) (fun i hi => ha i (by omega))
      have e0 := ih j (by omega) (fun i hi => ha i (by omega))
      have hj : a j ≠ 0 := ha j (by omega)
      have hj1 : a (j + 1) ≠ 0 := ha (j + 1) (by omega)
      have hp : ∏ i ∈ range j, a i ≠ 0 := prod_ne_zero_iff.mpr (fun i hi => ha i (by
        have := mem_range.mp hi; omega))
      rw [jacQ, e1, e0, jacP_succ_succ]
      simp only [eval_sub, eval_mul, eval_X, eval_C, prod_range_succ]
      field_simp

/-- Euclidean norm of the first `n` entries of a sequence. -/
noncomputable def seqNorm (n : ℕ) (q : ℕ → ℝ) : ℝ := Real.sqrt (∑ j ∈ range n, q j ^ 2)

theorem seqNorm_pos {n : ℕ} (hn : 0 < n) (q : ℕ → ℝ) (h0 : q 0 ≠ 0) : 0 < seqNorm n q := by
  unfold seqNorm
  apply Real.sqrt_pos.mpr
  have : 0 < q 0 ^ 2 := by positivity
  have h1 : q 0 ^ 2 ≤ ∑ j ∈ range n, q j ^ 2 :=
    single_le_sum (f := fun j => q j ^ 2) (fun j _ => by positivity) (mem_range.mpr hn)
  linarith

/-- Every eigenvector is its first component times the recurrence sequence `q`. -/
theorem jacobi_eigenvec_eq_q {n : ℕ} {b a : ℕ → ℝ} (ha : ∀ j, j + 1 < n → a j ≠ 0) {lam : ℝ}
    {v : Fin n → ℝ} (hv : jacobiMatrix n b a *ᵥ v = lam • v) (i : Fin n) :
    v i = extVec v 0 * jacQ b a lam i := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  rw [jacQ_eq b a lam i (fun l hl => ha l (by have := i.2; omega)), extVec_of_lt v hn]
  exact jacobi_eigenvec_eq ha hv i

/-- **Theorem ER (eq. (ER.2)), general Jacobi form.**  Let `v` be a unit eigenvector of the Jacobi
matrix `J_n` (nonzero links) for the eigenvalue `λ`, and let `σ = ±1` be the known sign of its first
component (`0 < σ v_0`).  Then `v = σ q / ‖q‖₂` with `q` the recurrence (ER.1). -/
theorem jacobi_reconstruct {n : ℕ} {b a : ℕ → ℝ} (ha : ∀ j, j + 1 < n → a j ≠ 0) {lam : ℝ}
    {v : Fin n → ℝ} (hv : jacobiMatrix n b a *ᵥ v = lam • v) (hunit : ∑ j, v j ^ 2 = 1)
    {σ : ℝ} (hσ : σ ^ 2 = 1) (hsign : 0 < σ * extVec v 0) (j : Fin n) :
    v j = σ * jacQ b a lam j / seqNorm n (jacQ b a lam) := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) j.2
  have hvq : ∀ i : Fin n, v i = extVec v 0 * jacQ b a lam i := jacobi_eigenvec_eq_q ha hv
  have hq0 : jacQ b a lam 0 = 1 := rfl
  have hsum : ∑ j, v j ^ 2 = extVec v 0 ^ 2 * ∑ i ∈ range n, jacQ b a lam i ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => jacQ b a lam i ^ 2) n, mul_sum]
    exact sum_congr rfl (fun i _ => by rw [hvq i]; ring)
  have hQ : 0 < ∑ i ∈ range n, jacQ b a lam i ^ 2 := by
    have h1 : jacQ b a lam 0 ^ 2 ≤ ∑ i ∈ range n, jacQ b a lam i ^ 2 :=
      single_le_sum (f := fun i => jacQ b a lam i ^ 2) (fun i _ => by positivity)
        (mem_range.mpr hn)
    rw [hq0] at h1; linarith
  have hN : seqNorm n (jacQ b a lam) ^ 2 = ∑ i ∈ range n, jacQ b a lam i ^ 2 :=
    Real.sq_sqrt hQ.le
  have hNpos : 0 < seqNorm n (jacQ b a lam) := Real.sqrt_pos.mpr hQ
  -- `v_0 = σ / ‖q‖`
  have h0sq : extVec v 0 ^ 2 = 1 / seqNorm n (jacQ b a lam) ^ 2 := by
    rw [hN, eq_div_iff hQ.ne']
    rw [hsum] at hunit; linarith
  have h0 : extVec v 0 = σ / seqNorm n (jacQ b a lam) := by
    have hσ0 : σ ≠ 0 := by rintro rfl; simp at hsign
    have e : (extVec v 0) ^ 2 = (σ / seqNorm n (jacQ b a lam)) ^ 2 := by
      rw [h0sq, div_pow, hσ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp e with h | h
    · exact h
    · exfalso
      rw [h] at hsign
      have : σ * (-(σ / seqNorm n (jacQ b a lam))) = -(σ ^ 2 / seqNorm n (jacQ b a lam)) := by ring
      rw [this, hσ] at hsign
      have : 0 < 1 / seqNorm n (jacQ b a lam) := by positivity
      linarith [show (1 : ℝ) / seqNorm n (jacQ b a lam) = 1 / seqNorm n (jacQ b a lam) from rfl]
  rw [hvq j, h0]
  ring

/-- The reconstruction closes: if `λ` is a root of `P_n` (an eigenvalue of `J_n`) then the unit
vector `q/‖q‖₂` is an eigenvector. -/
theorem jacobi_reconstruct_eigenvec {n : ℕ} {b a : ℕ → ℝ} (ha : ∀ j, j + 1 < n → a j ≠ 0)
    {lam : ℝ} (hroot : (jacP b a n).eval lam = 0) :
    ∃ v : Fin n → ℝ, jacobiMatrix n b a *ᵥ v = lam • v ∧ ∑ j, v j ^ 2 = 1 ∧ 0 < extVec v 0 ∧
      ∀ j : Fin n, v j = jacQ b a lam j / seqNorm n (jacQ b a lam) := by
  obtain ⟨w, hw0, hw⟩ := exists_eigenvec_of_root ha hroot
  have hn : 0 < n := by
    by_contra h
    exact hw0 (funext fun j => absurd j.2 (by omega))
  have hwq : ∀ i : Fin n, w i = extVec w 0 * jacQ b a lam i := jacobi_eigenvec_eq_q ha hw
  have h0 : extVec w 0 ≠ 0 := eigenvec_zero_ne ha hw hw0
  have hq0 : jacQ b a lam 0 = 1 := rfl
  have hQ : 0 < ∑ i ∈ range n, jacQ b a lam i ^ 2 := by
    have h1 : jacQ b a lam 0 ^ 2 ≤ ∑ i ∈ range n, jacQ b a lam i ^ 2 :=
      single_le_sum (f := fun i => jacQ b a lam i ^ 2) (fun i _ => by positivity)
        (mem_range.mpr hn)
    rw [hq0] at h1; linarith
  have hN : seqNorm n (jacQ b a lam) ^ 2 = ∑ i ∈ range n, jacQ b a lam i ^ 2 :=
    Real.sq_sqrt hQ.le
  have hNpos : 0 < seqNorm n (jacQ b a lam) := Real.sqrt_pos.mpr hQ
  set N := seqNorm n (jacQ b a lam) with hNdef
  have hv : (fun j : Fin n => jacQ b a lam j / N) = (1 / (extVec w 0 * N)) • w := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hwq j]
    field_simp
  refine ⟨fun j => jacQ b a lam j / N, ?_, ?_, ?_, fun j => rfl⟩
  · rw [hv, mulVec_smul, hw, smul_comm]
  · have : ∑ j : Fin n, (jacQ b a lam j / N) ^ 2 = (∑ i ∈ range n, jacQ b a lam i ^ 2) / N ^ 2 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => (jacQ b a lam i / N) ^ 2) n, sum_div]
      exact sum_congr rfl (fun i _ => by rw [div_pow])
    rw [this, ← hN]
    exact div_self (by positivity)
  · rw [extVec_of_lt _ hn]
    show 0 < jacQ b a lam 0 / N
    rw [hq0]; positivity

/-- info: 'FormalResearch.Jacobi.jacobi_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_reconstruct

/-- info: 'FormalResearch.Jacobi.jacobi_reconstruct_eigenvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_reconstruct_eigenvec

end FormalResearch.Jacobi
