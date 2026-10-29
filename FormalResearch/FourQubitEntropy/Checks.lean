import FormalResearch.FourQubitEntropy.EqualityMain

/-!
# Sanity checks and corollaries for the four-qubit entropy note

Concrete states on which the definitions of `Statement.lean` are evaluated (so that the main
theorems are not vacuous), the exact form of the purity identity, the criticality of the zeros of
`F`, the moment line `T ≤ 5/12 + 17/12 (P - 1)` and its sharpness, the Tsallis-2 corollary, the
invariants of `M₄`, and one-cut rigidity for the cut `12|34`.
-/

open scoped ComplexConjugate Matrix

namespace FormalResearch.FourQubitEntropy

section Concrete

/-- `|0000⟩`. -/
def prodState : Psi := fun a b c d => if a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 then 1 else 0
/-- `(|00⟩+|11⟩)/√2 ⊗ (|00⟩+|11⟩)/√2` on pairs `(12)(34)`. -/
noncomputable def bell2 : Psi := fun a b c d => if a = b ∧ c = d then 1 / 2 else 0
/-- Cluster state `½(|0000⟩+|0011⟩+|1100⟩-|1111⟩)`. -/
noncomputable def cluster4 : Psi := fun a b c d =>
  if a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 then 1 / 2 else
  if a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 1 then 1 / 2 else
  if a = 1 ∧ b = 1 ∧ c = 0 ∧ d = 0 then 1 / 2 else
  if a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 then -1 / 2 else 0

macro "eval_state " d:ident : tactic => `(tactic| (
  (try simp only [normSqPsi, $d:ident, Fin.sum_univ_two])
  <;> simp [$d:ident, normSqPsi, purity, cubicMoment, blochSq, expectation, actOn, red12, red13, red14,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_prod_type, pauliX, pauliY, pauliZ,
    Fin.sum_univ_four, map_ofNat, map_neg, map_div₀, map_one]
  <;> norm_num))

theorem prod_vals : normSqPsi prodState = 1 ∧ purity prodState = 3 ∧ cubicMoment prodState = 3 ∧
    blochSq prodState = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> eval_state prodState

theorem bell2_vals : normSqPsi bell2 = 1 ∧ purity bell2 = 3 / 2 ∧ cubicMoment bell2 = 9 / 8 ∧
    blochSq bell2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> eval_state bell2

theorem cluster4_vals : normSqPsi cluster4 = 1 ∧ purity cluster4 = 1 ∧ cubicMoment cluster4 = 3 / 8 ∧
    blochSq cluster4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> eval_state cluster4

theorem prod_F : sexticF prodState = 3 := by
  obtain ⟨h1, h2, h3, -⟩ := prod_vals
  unfold sexticF; rw [h1, h2, h3]; norm_num

theorem bell2_F : sexticF bell2 = 0 := by
  obtain ⟨h1, h2, h3, -⟩ := bell2_vals
  unfold sexticF; rw [h1, h2, h3]; norm_num

theorem cluster4_F : sexticF cluster4 = 1 / 2 := by
  obtain ⟨h1, h2, h3, -⟩ := cluster4_vals
  unfold sexticF; rw [h1, h2, h3]; norm_num

/-- The moment inequality `F ≥ (3/4) n W₁` (`sexticF_ge`) holds with equality at every product state;
here `|0000⟩` (`F = 3`, `n = 1`, `W₁ = 4`). -/
theorem prod_attains_sexticF_ge :
    sexticF prodState = 3 / 4 * (normSqPsi prodState * blochSq prodState) := by
  obtain ⟨h1, -, -, h4⟩ := prod_vals
  rw [prod_F, h1, h4]; norm_num

/-- **`3/4` is the best constant** in `c · n W₁ ≤ F`. (Product states have `τ = 0`, where the paper's
stronger `thm:fqe-general-envelope` (`GeneralEnvelope.lean`) also reads `F ≥ (3/4) W₁`.) -/
theorem sexticF_ge_sharp (c : ℝ) (h : ∀ ψ : Psi, c * (normSqPsi ψ * blochSq ψ) ≤ sexticF ψ) :
    c ≤ 3 / 4 := by
  have := h prodState
  rw [prod_attains_sexticF_ge] at this
  obtain ⟨h1, -, -, h4⟩ := prod_vals
  rw [h1, h4] at this
  linarith

end Concrete

section Identities

/-- The purity identity with `τ` identified: `2P = 2n² + W₁ + |ψᵀ ε^{⊗4} ψ|²`. -/
theorem purity_identity_exact (ψ : Psi) :
    2 * purity ψ = 2 * normSqPsi ψ ^ 2 + blochSq ψ + Complex.normSq (spinFlipForm ψ) := by
  have hd := purityDefect_zero ψ ψ.conj
  simp only [purityDefect, toAdd_complex, toMul_complex, toSub_complex, lit_complex] at hd
  rw [W1gen_eq, normG_eq, spinFlipForm_conj, Complex.mul_conj, tr2_marg12, tr2_marg13, tr2_marg14,
    trace_sq_real (red12_herm ψ), trace_sq_real (red13_herm ψ), trace_sq_real (red14_herm ψ)] at hd
  have hc : (((2 * purity ψ - 2 * normSqPsi ψ ^ 2 - blochSq ψ - Complex.normSq (spinFlipForm ψ) : ℝ)) : ℂ) = 0 := by
    unfold purity
    push_cast at hd ⊢
    linear_combination hd
  have : (2 * purity ψ - 2 * normSqPsi ψ ^ 2 - blochSq ψ - Complex.normSq (spinFlipForm ψ) : ℝ) = 0 := by
    exact_mod_cast hc
  linarith

/-- A unit vector has `P = 1` exactly when `W₁ = 0` and `ψᵀ ε^{⊗4} ψ = 0`. -/
theorem purity_eq_one_iff (ψ : Psi) (hn : normSqPsi ψ = 1) :
    purity ψ = 1 ↔ blochSq ψ = 0 ∧ spinFlipForm ψ = 0 := by
  constructor
  · exact purity_one_forces ψ hn
  · rintro ⟨hW, hτ⟩
    have := purity_identity_exact ψ
    rw [hn, hW, hτ] at this
    simp at this
    linarith

/-- At a zero of `F` every single-qubit Bloch component vanishes (the zeros are critical). -/
theorem sexticF_zero_bloch (ψ : Psi) (hn : normSqPsi ψ = 1) (hF : sexticF ψ = 0) :
    blochSq ψ = 0 := by
  have h := sexticF_ge ψ
  rw [hn, hF] at h
  have := blochSq_nonneg ψ
  linarith

/-- The moment line: `T ≤ 5/12 + 17/12 (P - 1)` for unit vectors. -/
theorem cubicMoment_le_line (ψ : Psi) (hn : normSqPsi ψ = 1) :
    cubicMoment ψ ≤ 5 / 12 + 17 / 12 * (purity ψ - 1) := by
  have h := sexticF_nonneg ψ
  unfold sexticF at h
  rw [hn] at h
  linarith

/-- The moment line is sharp at `(P, T) = (3/2, 9/8)`, attained by a product of two Bell pairs. -/
theorem bell2_on_line : cubicMoment bell2 = 5 / 12 + 17 / 12 * (purity bell2 - 1) := by
  obtain ⟨-, h2, h3, -⟩ := bell2_vals
  rw [h2, h3]; norm_num

/-- Tsallis-2 (linear) entropy of the three marginals containing qubit `1` is `1 - P/3`; it is
at most `2/3`, with equality exactly when `P = 1`. -/
theorem tsallis2_le (ψ : Psi) (hn : normSqPsi ψ = 1) :
    ((1 - (Matrix.trace (red12 ψ * red12 ψ)).re) + (1 - (Matrix.trace (red13 ψ * red13 ψ)).re)
      + (1 - (Matrix.trace (red14 ψ * red14 ψ)).re)) / 3 ≤ 2 / 3 := by
  have := purity_ge ψ
  unfold purity at this
  rw [hn] at this
  linarith

theorem cluster4_tsallis2_max :
    ((1 - (Matrix.trace (red12 cluster4 * red12 cluster4)).re)
      + (1 - (Matrix.trace (red13 cluster4 * red13 cluster4)).re)
      + (1 - (Matrix.trace (red14 cluster4 * red14 cluster4)).re)) / 3 = 2 / 3 := by
  obtain ⟨-, h2, -, -⟩ := cluster4_vals
  unfold purity at h2
  linarith

end Identities

section M4Values

private theorem quad_sq {R : Mat4} (hq : (R - (1 / 6 : ℂ) • 1) * (R - (1 / 2 : ℂ) • 1) = 0) :
    R * R = (2 / 3 : ℂ) • R - (1 / 12 : ℂ) • 1 := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, Matrix.mul_one, Matrix.one_mul] at hq
  have : R * R = (1 / 6 + 1 / 2 : ℂ) • R - (1 / 6 * (1 / 2) : ℂ) • 1 := by
    rw [← sub_eq_zero, ← hq]; module
  rw [this]; norm_num

theorem quad_traces {R : Mat4} (hq : (R - (1 / 6 : ℂ) • 1) * (R - (1 / 2 : ℂ) • 1) = 0)
    (ht : Matrix.trace R = 1) :
    (Matrix.trace (R * R)).re = 1 / 3 ∧ (Matrix.trace (R * R * R)).re = 5 / 36 := by
  have h2 := quad_sq hq
  have t2 : Matrix.trace (R * R) = 1 / 3 := by
    rw [h2, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, ht, Matrix.trace_one]
    simp; norm_num
  refine ⟨by rw [t2]; norm_num, ?_⟩
  have : R * R * R = (2 / 3 : ℂ) • (R * R) - (1 / 12 : ℂ) • R := by
    rw [h2]; simp [sub_mul]; rw [h2]; module
  rw [this, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, ht, t2]
  norm_num

/-- `M₄` has `P = 1`, `T = 5/12`, `F = 0` and vanishing Bloch vectors. -/
theorem M4_invariants : purity M4 = 1 ∧ cubicMoment M4 = 5 / 12 ∧ sexticF M4 = 0 ∧
    blochSq M4 = 0 := by
  have t12 : Matrix.trace (red12 M4) = 1 := by rw [trace_red12, M4_unit]; simp
  have t13 : Matrix.trace (red13 M4) = 1 := by rw [trace_red13, M4_unit]; simp
  have t14 : Matrix.trace (red14 M4) = 1 := by rw [trace_red14, M4_unit]; simp
  obtain ⟨a12, b12⟩ := quad_traces M4_cutQuadratics.q12 t12
  obtain ⟨a13, b13⟩ := quad_traces M4_cutQuadratics.q13 t13
  obtain ⟨a14, b14⟩ := quad_traces M4_cutQuadratics.q14 t14
  have hP : purity M4 = 1 := by unfold purity; rw [a12, a13, a14]; norm_num
  have hT : cubicMoment M4 = 5 / 12 := by unfold cubicMoment; rw [b12, b13, b14]; norm_num
  have hF : sexticF M4 = 0 := by unfold sexticF; rw [M4_unit, hP, hT]; norm_num
  exact ⟨hP, hT, hF, sexticF_zero_bloch M4 M4_unit hF⟩

end M4Values

section Rigidity

/-- One-cut rigidity for the cut `12|34`: a unit vector with `P = 1` and the two-eigenvalue
spectrum `{1/6, 1/2}` on that cut is local-unitarily `M₄` or `conj M₄`. -/
theorem one_cut_rigidity_12 (ψ : Psi) (hn : normSqPsi ψ = 1) (hP : purity ψ = 1)
    (hq : (red12 ψ - (1 / 6 : ℂ) • 1) * (red12 ψ - (1 / 2 : ℂ) • 1) = 0) :
    LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ := by
  obtain ⟨hW, hτ⟩ := purity_one_forces ψ hn hP
  rcases classify ψ hn hW hq hτ with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

end Rigidity

/-! The following results do not use the sextic identity of `Identity.lean`. -/

/-- info: 'FormalResearch.FourQubitEntropy.purity_identity_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms purity_identity_exact

/-- info: 'FormalResearch.FourQubitEntropy.purity_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms purity_eq_one_iff

/-- info: 'FormalResearch.FourQubitEntropy.one_cut_rigidity_12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_cut_rigidity_12

/-- info: 'FormalResearch.FourQubitEntropy.cluster4_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cluster4_vals

end FormalResearch.FourQubitEntropy
