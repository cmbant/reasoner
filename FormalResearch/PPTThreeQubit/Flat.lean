module

public import FormalResearch.PPTThreeQubit.FlatPauli

/-!
# Flat three-qubit states are fully PPT with rank profile `(r, r, r, r)`

Source: `QI/hidden_entanglement/ppt_three_qubit/relaxations_and_scope.tex`,
`sec:ppt3-flat` (the paragraph before `rem:ppt3-flat-profile`).

A three-qubit state `ρ` is *flat* (`IsFlat3`) if it is PSD of trace one and every proper marginal is
maximally mixed (the three two-qubit marginals `AB, AC, BC` and the three one-qubit marginals).
Index convention as in `Basic.lean` (`|abc⟩ = 4a + 2b + c`); marginals are the explicit partial
traces over the bit of the traced-out qubits.

Covered (proved):
* `pauli_expand`: the Pauli expansion `M = (1/8) ∑_{pqr} tr(P_p⊗P_q⊗P_r M) P_p⊗P_q⊗P_r` of any
  `8 × 8` matrix (completeness of the Pauli basis);
* `flat_form`: a flat state is `I/8 + T` with `T` a real combination of the 27 three-body Pauli
  products (`FlatPauli.flatRho`) -- only the three two-qubit marginals are used;
* `flat_pt_conj`: `σ_y^{(c)} ρ^{T_c} σ_y^{(c)} = (σ_y⊗σ_y⊗σ_y) conj(ρ) (σ_y⊗σ_y⊗σ_y)` for each `c`;
* `flat_fully_ppt`: every `ρ^{T_c}` is PSD and `rank ρ^{T_c} = rank ρ`, i.e. fully PPT with rank
  profile `(r, r, r, r)`.
Deviation from the paper's wording: the coefficients of `T` are real (the paper says "a combination
of three-body Pauli products"; Hermiticity of `ρ` forces them real, and for non-real coefficients the
identity `= J ρ J⁻¹` is false).  Not covered: the invariance "under invertible local filtering" of
the profile (a separate remark in the paper), and `rem:ppt3-flat-profile`.
-/

@[expose] public section


namespace FormalResearch.PPTThreeQubit.Flat

open Matrix
open scoped ComplexOrder

noncomputable section

lemma sum5 (f : Fin 4 → Fin 4 → Fin 4 → Fin 8 → Fin 8 → ℂ) :
    ∑ p, ∑ q, ∑ r, ∑ l, ∑ k, f p q r l k = ∑ l, ∑ k, ∑ p, ∑ q, ∑ r, f p q r l k := by
  have h1 : ∀ p q, ∑ r, ∑ l, ∑ k, f p q r l k = ∑ l, ∑ k, ∑ r, f p q r l k := by
    intro p q
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
  have h2 : ∀ p, ∑ q, ∑ l, ∑ k, ∑ r, f p q r l k = ∑ l, ∑ k, ∑ q, ∑ r, f p q r l k := by
    intro p
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
  have h3 : ∑ p, ∑ l, ∑ k, ∑ q, ∑ r, f p q r l k = ∑ l, ∑ k, ∑ p, ∑ q, ∑ r, f p q r l k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
  simp only [h1, h2, h3]

/-- The four Paulis `(1, σ_x, σ_y, σ_z)`. -/
def pauli : Fin 4 → M2 := ![1, σx, σy, σz]
lemma pauli_zero : pauli 0 = 1 := rfl
lemma pauli_succ (i : Fin 3) : pauli i.succ = σ i := by fin_cases i <;> rfl

/-- `P_p ⊗ P_q ⊗ P_r` over the four Paulis (the 64 Pauli basis elements). -/
def P4 (p q r : Fin 4) : M8 := pauli3 (pauli p) (pauli q) (pauli r)

lemma pauli_comp (a b c d : Fin 2) :
    ∑ p, pauli p a b * pauli p c d = if a = d ∧ b = c then 2 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Fin.sum_univ_four, pauli, σx, σy, σz] <;> norm_num

lemma eq_bits {i j : Fin 8} : i = j ↔ bA i = bA j ∧ bB i = bB j ∧ bC i = bC j :=
  ⟨fun h => by simp [h], fun ⟨a, b, c⟩ => by rw [← ix_bits i, ← ix_bits j, a, b, c]⟩

lemma comp8 (l k i j : Fin 8) :
    ∑ p, ∑ q, ∑ r, P4 p q r l k * P4 p q r i j = if k = i ∧ l = j then 8 else 0 := by
  have h : ∀ p q r, P4 p q r l k * P4 p q r i j =
      (pauli p (bA l) (bA k) * pauli p (bA i) (bA j)) *
      (pauli q (bB l) (bB k) * pauli q (bB i) (bB j)) *
      (pauli r (bC l) (bC k) * pauli r (bC i) (bC j)) := by
    intro p q r; simp only [P4, pauli3, of_apply]; ring
  simp only [h]
  have : ∀ f g h' : Fin 4 → ℂ, ∑ p, ∑ q, ∑ r, f p * g q * h' r = (∑ p, f p) * (∑ q, g q) * (∑ r, h' r) := by
    intro f g h'; simp only [Fin.sum_univ_four]; ring
  have hiff : (k = i ∧ l = j) ↔ ((bA l = bA j ∧ bA k = bA i) ∧ (bB l = bB j ∧ bB k = bB i) ∧
      (bC l = bC j ∧ bC k = bC i)) := by
    rw [eq_bits (i := k), eq_bits (i := l)]; tauto
  rw [this, pauli_comp, pauli_comp, pauli_comp]
  rw [if_congr hiff rfl rfl]
  by_cases hA : bA l = bA j ∧ bA k = bA i <;> by_cases hB : bB l = bB j ∧ bB k = bB i <;>
    by_cases hC : bC l = bC j ∧ bC k = bC i <;> simp [hA, hB, hC] <;> norm_num

/-- `sec:ppt3-flat` (completeness of the Pauli basis): `M = (1/8) ∑_{pqr} tr(P_pqr M) P_pqr`
for every `8 × 8` matrix.  (Proved.) -/
theorem pauli_expand (M : M8) :
    M = (1 / 8 : ℂ) • ∑ p, ∑ q, ∑ r, trace (P4 p q r * M) • P4 p q r := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.sum_apply, trace, diag_apply, mul_apply, smul_eq_mul, Finset.sum_mul]
  rw [sum5]
  have : ∀ l k, ∑ p, ∑ q, ∑ r, P4 p q r l k * M k l * P4 p q r i j
      = M k l * if k = i ∧ l = j then 8 else 0 := by
    intro l k
    rw [← comp8, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  simp only [this, mul_ite, ite_and]
  simp
  ring

/-! ### Flat states -/

/-- The marginal on `AB`: partial trace over `C`. -/
def margAB (ρ : M8) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun x y => ∑ c, ρ (ix x.1 x.2 c) (ix y.1 y.2 c)
/-- The marginal on `AC`: partial trace over `B`. -/
def margAC (ρ : M8) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun x y => ∑ b, ρ (ix x.1 b x.2) (ix y.1 b y.2)
/-- The marginal on `BC`: partial trace over `A`. -/
def margBC (ρ : M8) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun x y => ∑ a, ρ (ix a x.1 x.2) (ix a y.1 y.2)
/-- The marginal on `A`. -/
def margA (ρ : M8) : M2 := Matrix.of fun a a' => ∑ b, ∑ c, ρ (ix a b c) (ix a' b c)
/-- The marginal on `B`. -/
def margB (ρ : M8) : M2 := Matrix.of fun b b' => ∑ a, ∑ c, ρ (ix a b c) (ix a b' c)
/-- The marginal on `C`. -/
def margC (ρ : M8) : M2 := Matrix.of fun c c' => ∑ a, ∑ b, ρ (ix a b c) (ix a b c')

/-- Flat three-qubit state: PSD, trace one, every proper marginal maximally mixed. -/
def IsFlat3 (ρ : M8) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1 ∧
  margAB ρ = (1 / 4 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ∧
  margAC ρ = (1 / 4 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ∧
  margBC ρ = (1 / 4 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ∧
  margA ρ = (1 / 2 : ℂ) • (1 : M2) ∧ margB ρ = (1 / 2 : ℂ) • (1 : M2) ∧
  margC ρ = (1 / 2 : ℂ) • (1 : M2)

lemma trace_AB (P Q : M2) (ρ : M8) (h : margAB ρ = (1 / 4 : ℂ) • 1) :
    trace (pauli3 P Q 1 * ρ) = (1 / 4) * (trace P * trace Q) := by
  have : trace (pauli3 P Q 1 * ρ) =
      ∑ x : Fin 2 × Fin 2, ∑ y : Fin 2 × Fin 2, P x.1 y.1 * Q x.2 y.2 * margAB ρ y x := by
    simp [trace, mul_apply, pauli3, margAB, sum_fin8, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.one_apply]
    ring
  rw [this, h]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, trace, Matrix.one_apply]
  ring

lemma trace_AC (P R : M2) (ρ : M8) (h : margAC ρ = (1 / 4 : ℂ) • 1) :
    trace (pauli3 P 1 R * ρ) = (1 / 4) * (trace P * trace R) := by
  have : trace (pauli3 P 1 R * ρ) =
      ∑ x : Fin 2 × Fin 2, ∑ y : Fin 2 × Fin 2, P x.1 y.1 * R x.2 y.2 * margAC ρ y x := by
    simp [trace, mul_apply, pauli3, margAC, sum_fin8, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.one_apply]
    ring
  rw [this, h]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, trace, Matrix.one_apply]
  ring

lemma trace_BC (Q R : M2) (ρ : M8) (h : margBC ρ = (1 / 4 : ℂ) • 1) :
    trace (pauli3 1 Q R * ρ) = (1 / 4) * (trace Q * trace R) := by
  have : trace (pauli3 1 Q R * ρ) =
      ∑ x : Fin 2 × Fin 2, ∑ y : Fin 2 × Fin 2, Q x.1 y.1 * R x.2 y.2 * margBC ρ y x := by
    simp [trace, mul_apply, pauli3, margBC, sum_fin8, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.one_apply]
    ring
  rw [this, h]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, trace, Matrix.one_apply]
  ring


lemma trace_pauli (p : Fin 4) : trace (pauli p) = if p = 0 then 2 else 0 := by
  fin_cases p <;> simp [pauli, σx, σy, σz, trace, Fin.sum_univ_two]

lemma σ_herm (i : Fin 3) : (σ i)ᴴ = σ i := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [σ, σx, σy, σz, conjTranspose_apply]

lemma P3_herm (i j k : Fin 3) : (P3 i j k)ᴴ = P3 i j k := by
  simp [P3, pauli3_conjTranspose, σ_herm]

lemma trace_P4_zero {ρ : M8} (h : IsFlat3 ρ) (p q r : Fin 4)
    (h1 : p = 0 ∨ q = 0 ∨ r = 0) (h2 : ¬ (p = 0 ∧ q = 0 ∧ r = 0)) :
    trace (P4 p q r * ρ) = 0 := by
  obtain ⟨-, -, hAB, hAC, hBC, -⟩ := h
  rcases h1 with rfl | rfl | rfl
  · have := trace_BC (pauli q) (pauli r) ρ hBC
    simp only [P4, pauli_zero] at this ⊢
    rw [this, trace_pauli, trace_pauli]
    by_cases hq : q = 0 <;> by_cases hr : r = 0 <;> simp_all
  · have := trace_AC (pauli p) (pauli r) ρ hAC
    simp only [P4, pauli_zero] at this ⊢
    rw [this, trace_pauli, trace_pauli]
    by_cases hq : p = 0 <;> by_cases hr : r = 0 <;> simp_all
  · have := trace_AB (pauli p) (pauli q) ρ hAB
    simp only [P4, pauli_zero] at this ⊢
    rw [this, trace_pauli, trace_pauli]
    by_cases hq : p = 0 <;> by_cases hr : q = 0 <;> simp_all


lemma P4_succ (i j k : Fin 3) : P4 i.succ j.succ k.succ = P3 i j k := by
  simp [P4, P3, pauli_succ]

lemma P4_zero : P4 0 0 0 = 1 := by simp [P4, pauli_zero, pauli3_one]

lemma sum4_succ {M : Type*} [AddCommMonoid M] (f : Fin 4 → M) :
    ∑ p, f p = f 0 + ∑ i : Fin 3, f i.succ := Fin.sum_univ_succ f

lemma flat_sum {ρ : M8} (h : IsFlat3 ρ) :
    ∑ p, ∑ q, ∑ r, trace (P4 p q r * ρ) • P4 p q r
      = (1 : M8) + ∑ i, ∑ j, ∑ k, trace (P3 i j k * ρ) • P3 i j k := by
  have hg : ∀ p q r : Fin 4, trace (P4 p q r * ρ) • P4 p q r =
      (if p = 0 then if q = 0 then if r = 0 then (1 : M8) else 0 else 0 else 0) +
      (if p = 0 then 0 else if q = 0 then 0 else if r = 0 then 0 else
        trace (P4 p q r * ρ) • P4 p q r) := by
    intro p q r
    by_cases hp : p = 0 <;> by_cases hq : q = 0 <;> by_cases hr : r = 0
    · subst hp hq hr; simp [P4_zero, h.2.1]
    all_goals first
      | (rw [trace_P4_zero h p q r (by tauto) (by tauto)]; simp [hp, hq, hr])
      | simp [hp, hq, hr]
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => hg p q r]
  simp only [Finset.sum_add_distrib]
  congr 1
  · simp
  · simp only [sum4_succ]
    simp [P4_succ]


/-- `sec:ppt3-flat`: a flat state is `I/8 + T`, `T` a real combination of the 27 three-body
Pauli products.  (Proved.) -/
theorem flat_form {ρ : M8} (h : IsFlat3 ρ) : ∃ t : Fin 3 → Fin 3 → Fin 3 → ℝ, ρ = flatRho t := by
  refine ⟨fun i j k => (trace (P3 i j k * ρ)).re / 8, ?_⟩
  have hre : ∀ i j k, ((trace (P3 i j k * ρ)).re : ℂ) = trace (P3 i j k * ρ) := by
    intro i j k
    rw [← Complex.conj_eq_iff_re]
    have hh : ρᴴ = ρ := h.1.isHermitian.eq
    have : star (trace (P3 i j k * ρ)) = trace (P3 i j k * ρ) := by
      rw [← trace_conjTranspose, conjTranspose_mul, hh, P3_herm, trace_mul_comm]
    exact this
  have e := pauli_expand ρ
  rw [flat_sum h] at e
  have key : ∀ i j k, (1 / 8 : ℂ) • (trace (P3 i j k * ρ) • P3 i j k) =
      (((trace (P3 i j k * ρ)).re / 8 : ℝ) : ℂ) • P3 i j k := by
    intro i j k
    rw [smul_smul]
    congr 1
    rw [Complex.ofReal_div, hre]
    simp; ring
  conv_lhs => rw [e]
  simp only [flatRho, flatT, smul_add, Finset.smul_sum, key]

/-- `sec:ppt3-flat`: for a flat state, `σ_y^{(c)} ρ^{T_c} σ_y^{(c)} = (σ_y⊗σ_y⊗σ_y) conj(ρ)
(σ_y⊗σ_y⊗σ_y)` (`= I/8 - T`) for each qubit `c = A, B, C`.  (Proved.) -/
theorem flat_pt_conj {ρ : M8} (hρ : IsFlat3 ρ) :
    yA * ptA ρ * yA = yyy * ρ.map (starRingEnd ℂ) * yyy ∧
    yB * ptB ρ * yB = yyy * ρ.map (starRingEnd ℂ) * yyy ∧
    yC * ptC ρ * yC = yyy * ρ.map (starRingEnd ℂ) * yyy := by
  obtain ⟨t, rfl⟩ := flat_form hρ
  exact ⟨(flat_pt_A t).trans (yyy_conj t).symm, (flat_pt_B t).trans (yyy_conj t).symm,
    (flat_pt_C t).trans (yyy_conj t).symm⟩

/-- `sec:ppt3-flat` (headline): every flat three-qubit state is fully PPT with rank profile
`(r, r, r, r)`, `r = rank ρ`: each partial transpose `ρ^{T_c}` is positive semidefinite and has the
same rank as `ρ`.  (Proved; flatness = PSD, trace one, all proper marginals maximally mixed.) -/
theorem flat_fully_ppt {ρ : M8} (hρ : IsFlat3 ρ) :
    ((ptA ρ).PosSemidef ∧ (ptB ρ).PosSemidef ∧ (ptC ρ).PosSemidef) ∧
    ((ptA ρ).rank = ρ.rank ∧ (ptB ρ).rank = ρ.rank ∧ (ptC ρ).rank = ρ.rank) := by
  obtain ⟨t, ht⟩ := flat_form hρ
  have hpsd : (flatRho t).PosSemidef := ht ▸ hρ.1
  rw [ht]
  exact ⟨⟨(pt_psd_rank_A t hpsd).1, (pt_psd_rank_B t hpsd).1, (pt_psd_rank_C t hpsd).1⟩,
    (pt_psd_rank_A t hpsd).2, (pt_psd_rank_B t hpsd).2, (pt_psd_rank_C t hpsd).2⟩

/-- info: 'FormalResearch.PPTThreeQubit.Flat.pauli_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauli_expand

/-- info: 'FormalResearch.PPTThreeQubit.Flat.flat_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flat_form

/-- info: 'FormalResearch.PPTThreeQubit.Flat.flat_pt_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flat_pt_conj

/-- info: 'FormalResearch.PPTThreeQubit.Flat.flat_fully_ppt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flat_fully_ppt

end

end FormalResearch.PPTThreeQubit.Flat
