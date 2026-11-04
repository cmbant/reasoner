module

public import FormalResearch.NQubit.Pauli.Conjugation
public import FormalResearch.NQubit.Reduced.Purity

/-!
# Branch states and the time-reversal purification `Ω_z`

For `f g : Ψ m`, `branchState f g : Ψ (m + 1)` has the two branches `f`, `g` on the first qubit, and
`omegaState z = (|0⟩ z + |1⟩ Θ z)/√2`.

* `pexp_omegaState`, `pauliSq_omegaState`: on words that are the identity on the first qubit only even weights
  survive, and they equal those of `z`;
* `weightEnumExcl_omegaState`, `cutPuritySumExcl_omegaState`, `cutPuritySum_omegaState`: the weight and purity
  enumerators of `Ω_z` in terms of those of `z`;
* `nsq_omegaState`: `‖Ω_z‖ = ‖z‖`;
* `Θ_omegaState_odd`: `Θ Ω_z = -Ω_z` for odd `m`, and `tau_omegaState_odd`: `τ(Ω_z) = ‖z‖⁴` for odd `m`.
-/

@[expose] public section


open scoped ComplexConjugate BigOperators
open scoped Matrix
open FormalResearch.NQubit.Pauli
open FormalResearch.NQubit.Reduced

namespace FormalResearch.NQubit.TimeReversal

/-! ### The branch states `Ω_z` -/

theorem sum_cfg_succ {m : ℕ} (F : Cfg (m + 1) → ℂ) :
    ∑ x, F x = ∑ c : Fin 2, ∑ x' : Cfg m, F (Fin.cons c x') := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 2)) F, Fintype.sum_prod_type]
  rfl

theorem sum_word_succ {m : ℕ} {R : Type*} [AddCommMonoid R] (F : (Fin (m + 1) → Fin 4) → R) :
    ∑ a, F a = ∑ c : Fin 4, ∑ a' : Fin m → Fin 4, F (Fin.cons c a') := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 4)) F, Fintype.sum_prod_type]
  rfl

/-- Two branches on the distinguished qubit `0`. -/
def branchState {m : ℕ} (f g : Ψ m) : Ψ (m + 1) := fun x => if x 0 = 0 then f (Fin.tail x) else g (Fin.tail x)

theorem branchState_cons {m : ℕ} (f g : Ψ m) (c : Fin 2) (x' : Cfg m) :
    branchState f g (Fin.cons c x') = if c = 0 then f x' else g x' := by
  simp [branchState]

/-- `|Ω_z⟩ = (|0⟩ z + |1⟩ Θ_m z)/√2`. -/
noncomputable def omegaState {m : ℕ} (z : Ψ m) : Ψ (m + 1) :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • branchState z (Θ z)

theorem pexp_branchState {m : ℕ} (f g : Ψ m) (a' : Fin m → Fin 4) :
    pexp (branchState f g) (Fin.cons 0 a') = pexp f a' + pexp g a' := by
  have h1 : (pauliSU 0 : Op1) = 1 := rfl
  unfold pexp ip rot
  simp only [sum_cfg_succ, Fin.sum_univ_two, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    branchState_cons, h1]
  simp [Matrix.one_apply]

theorem pexp_omegaState {m : ℕ} (z : Ψ m) (a' : Fin m → Fin 4) :
    pexp (omegaState z) (Fin.cons 0 a') = (1 / 2 : ℂ) * (pexp z a' + conj (pexp z a')) := by
  unfold omegaState
  rw [pexp_smul, pexp_branchState, pexp_Θ]
  have : conj (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [show ((Real.sqrt 2)⁻¹ : ℝ) * (Real.sqrt 2)⁻¹ = 1 / 2 by
      rw [← mul_inv, h2]; norm_num]
    push_cast; ring
  simpa using congrArg (· * (pexp z a' + conj (pexp z a'))) this

/-- The Pauli weights of `Ω_z` on words that are the identity on the distinguished qubit:
only even weights survive, and they equal those of `z`. -/
theorem pauliSq_omegaState {m : ℕ} (z : Ψ m) (a' : Fin m → Fin 4) :
    pauliSq (omegaState z) (Fin.cons 0 a') = if Even (pauliWeight a') then pauliSq z a' else 0 := by
  unfold pauliSq
  rw [pexp_omegaState, conj_pexp]
  rcases Nat.even_or_odd (pauliWeight a') with h | h
  · simp only [h, ↓reduceIte, h.neg_one_pow]
    have : (1 / 2 : ℂ) * (pexp z a' + 1 * pexp z a') = pexp z a' := by ring
    rw [this]
  · have hn : ¬ Even (pauliWeight a') := Nat.not_even_iff_odd.mpr h
    simp only [hn, ↓reduceIte, h.neg_one_pow]
    simp


theorem pauliWeight_cons {m : ℕ} (c : Fin 4) (a' : Fin m → Fin 4) :
    pauliWeight (Fin.cons c a' : Fin (m + 1) → Fin 4) = (if c ≠ 0 then 1 else 0) + pauliWeight a' := by
  have h : ∀ {k : ℕ} (b : Fin k → Fin 4), pauliWeight b = ∑ i, if b i ≠ 0 then 1 else 0 := by
    intro k b; unfold pauliWeight; rw [Finset.card_filter]
  rw [h, h, Fin.sum_univ_succ]
  simp

/-- The Pauli weight enumerator of `Ω_z` on the original qubits (coefficient form). -/
theorem weightEnumExcl_omegaState {m : ℕ} (z : Ψ m) (j : ℕ) :
    weightEnumExcl (omegaState z) 0 j = if Even j then weightEnum z j else 0 := by
  have hset : (wsupp (Finset.univ.erase (0 : Fin (m + 1)))).filter (fun a => pauliWeight a = j)
      = Finset.univ.filter (fun a : Fin (m + 1) → Fin 4 => a 0 = 0 ∧ pauliWeight a = j) := by
    ext a
    rw [Finset.mem_filter, Finset.mem_filter, mem_wsupp]
    have key : ∀ i : Fin (m + 1), i ∉ Finset.univ.erase (0 : Fin (m + 1)) ↔ i = 0 := by
      intro i; simp
    simp only [key, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1 0 rfl, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun i hi => by subst hi; exact h1, h2⟩
  unfold weightEnumExcl
  rw [hset, Finset.sum_filter, sum_word_succ]
  simp only [Fin.sum_univ_four, Fin.cons_zero]
  have h1 : ((1 : Fin 4) = 0) = False := by decide
  have h2 : ((2 : Fin 4) = 0) = False := by decide
  have h3 : ((3 : Fin 4) = 0) = False := by decide
  simp only [h1, h2, h3, false_and, ite_false, Finset.sum_const_zero, add_zero, true_and,
    pauliWeight_cons, pauliSq_omegaState]
  have key : ∀ x : Fin m → Fin 4, (if (if (0 : Fin 4) ≠ 0 then 1 else 0) + pauliWeight x = j then
      (if Even (pauliWeight x) then pauliSq z x else 0) else 0)
      = if Even j then (if pauliWeight x = j then pauliSq z x else 0) else 0 := by
    intro x
    by_cases h : pauliWeight x = j <;> simp [h]
  simp only [key]
  unfold weightEnum
  rw [Finset.sum_filter]
  split_ifs <;> simp

/-- Coefficient form: the purity enumerator of subsets of the original qubits. -/
theorem cutPuritySumExcl_omegaState {m : ℕ} (z : Ψ m) (r : ℕ) :
    (2 : ℝ) ^ r * cutPuritySumOn (omegaState z) (Finset.univ.erase 0) r =
      ∑ j ∈ Finset.range (m + 1),
        (if j ≤ r then (if Even j then (Nat.choose (m - j) (r - j) : ℝ) else 0) else 0) * weightEnum z j := by
  rw [two_pow_mul_Q, Finset.sum_range_succ]
  have hlast : (if m + 1 ≤ r then (Nat.choose (m + 1 - 1 - (m + 1)) (r - (m + 1)) : ℝ) else 0)
      * weightEnumExcl (omegaState z) 0 (m + 1) = 0 := by
    rw [weightEnumExcl_omegaState]
    have : weightEnum z (m + 1) = 0 := weightEnum_eq_zero_of_gt z (Nat.lt_succ_self m)
    by_cases h : Even (m + 1) <;> simp [h, this]
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weightEnumExcl_omegaState]
  by_cases hj : j ≤ r <;> by_cases he : Even j <;> simp [hj, he]

/-! ### Normalisation and the symmetry `Θ Ω_z = -Ω_z` for odd `m` -/

theorem ip_branchState {m : ℕ} (f g f' g' : Ψ m) :
    ip (branchState f g) (branchState f' g') = ip f f' + ip g g' := by
  unfold ip
  simp only [sum_cfg_succ, Fin.sum_univ_two, branchState_cons]
  simp

theorem ip_smul_smul {n : ℕ} (c : ℂ) (ψ φ : Ψ n) : ip (c • ψ) (c • φ) = (conj c * c) * ip ψ φ := by
  unfold ip
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem coef_sq : conj (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [show ((Real.sqrt 2)⁻¹ : ℝ) * (Real.sqrt 2)⁻¹ = 1 / 2 by rw [← mul_inv, h2]; norm_num]
  push_cast; ring

/-- `‖Ω_z‖ = ‖z‖`. -/
theorem nsq_omegaState {m : ℕ} (z : Ψ m) : nsq (omegaState z) = nsq z := by
  have h : (nsq (omegaState z) : ℂ) = (nsq z : ℂ) := by
    rw [← ip_self, ← ip_self]
    unfold omegaState
    rw [ip_smul_smul, ip_branchState, ip_self, ip_self, nsq_Θ, coef_sq]
    ring
  exact_mod_cast h

theorem Θ_branchState {m : ℕ} (f g : Ψ m) : Θ (branchState f g) = branchState (Θ g) (-(Θ f)) := by
  have key : ∀ (c : Fin 2) (x' : Cfg m), Θ (branchState f g) (Fin.cons c x')
      = branchState (Θ g) (-(Θ f)) (Fin.cons c x') := by
    intro c x'
    rw [branchState_cons]
    unfold Θ
    simp only [sum_cfg_succ, Fin.sum_univ_two, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      branchState_cons]
    fin_cases c <;> simp [eps]
  funext x
  have := key (x 0) (Fin.tail x)
  simpa [Fin.cons_self_tail] using this

theorem Θ_smul {n : ℕ} (c : ℂ) (ψ : Ψ n) : Θ (c • ψ) = conj c • Θ ψ := by
  funext x
  simp only [Θ, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- For odd `m`, `Θ_{m+1} Ω_z = -Ω_z` (`J_{m+1}Ω_z = -Ω_z`). -/
theorem Θ_omegaState_odd {m : ℕ} (hm : Odd m) (z : Ψ m) : Θ (omegaState z) = -omegaState z := by
  unfold omegaState
  rw [Θ_smul, Θ_branchState, Θ_Θ, hm.neg_one_pow, Complex.conj_ofReal]
  funext x
  simp [branchState]
  split_ifs <;> simp

/-- For odd `m` and any `z`, `τ_{m+1}(Ω_z) = ‖z‖⁴`: the intrinsic characterisation `τ = 1`
(the intrinsic characterisation `τ = 1`, forward direction). -/
theorem tau_omegaState_odd {m : ℕ} (hm : Odd m) (z : Ψ m) : tau (omegaState z) = nsq z * nsq z := by
  unfold tau
  rw [Θ_omegaState_odd hm]
  have : ip (omegaState z) (-omegaState z) = -(nsq (omegaState z) : ℂ) := by
    unfold ip; simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [← ip_self]; rfl
  rw [this, Complex.normSq_neg, Complex.normSq_ofReal, nsq_omegaState]

/-- At coefficient level: the size-`k` purity sum of `Ω_z` is the sum of the
enumerator coefficients of `Q_z` at `k` and at `m + 1 - k`. -/
theorem cutPuritySum_omegaState {m : ℕ} (z : Ψ m) (k : ℕ) (hk : k ≤ m + 1) :
    cutPuritySum (omegaState z) k =
      (∑ j ∈ Finset.range (m + 1),
        (if j ≤ k then (if Even j then (Nat.choose (m - j) (k - j) : ℝ) else 0) else 0) * weightEnum z j) / 2 ^ k
      + (∑ j ∈ Finset.range (m + 1),
        (if j ≤ m + 1 - k then (if Even j then (Nat.choose (m - j) (m + 1 - k - j) : ℝ) else 0) else 0)
          * weightEnum z j) / 2 ^ (m + 1 - k) := by
  rw [cutPuritySum_split (omegaState z) 0 k hk, ← cutPuritySumExcl_omegaState, ← cutPuritySumExcl_omegaState]
  field_simp

end FormalResearch.NQubit.TimeReversal
