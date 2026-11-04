module

public import FormalResearch.NQubit.Foundations

/-!
# Pauli weight distribution and the global parity identity (any number of qubits)

Everything is for an arbitrary number `n` of qubits, with `Ψ n = (Fin n → Fin 2) → ℂ` and the time reversal
`Θ ψ = ε^{⊗n} ψ̄` of `NQubit/Foundations.lean` (`Θ`, `ip`, `nsq`, `rot`, `pauliSU`).

**Pauli convention.**  `pauliSU = {1, -iσₓ, -iσ_y, -iσ_z}` (the `SU(2)` representatives), so
`pexp ψ a = ⟨ψ | ⊗ᵢ pauliSU (aᵢ) ψ⟩` is the expectation of the Hermitian Pauli word `P_a` up to the phase
`(-i)^{pauliWeight a}`; squared moduli are unaffected.

* `pauliSq ψ a = |pexp ψ a|² = ⟨ψ|P_a|ψ⟩²` is the squared Pauli expectation of the Hermitian word `P_a`;
* `weightEnum ψ j = Σ_{pauliWeight a = j} pauliSq ψ a` is the Pauli weight distribution;
* `tau ψ = |⟨ψ, Θψ⟩|² = |ψᵀ ε^{⊗n} ψ|²`.

Main results (all **proved**, no hypotheses beyond `nsq ψ = 1` where stated):

* `sum_weightEnum`: `Σ_j A_j = 2^n ‖ψ‖⁴`;
* `sum_signed_weightEnum`: `Σ_j (-1)^j A_j = 2^n τ`;
* `parity_odd`, `parity_even`: `Σ_{j odd} A_j = 2^{n-1}(1 - τ)` and `Σ_{j even} A_j = 2^{n-1}(1 + τ)` for unit `ψ`;
* `tau_eq_zero_of_odd`: `τ = 0` for odd `n`; `tau_le`;
* `tau_eq_one_iff_odd_vanish` (even `n`): `τ = 1` iff every odd-weight Pauli expectation vanishes.
-/

@[expose] public section


open scoped ComplexConjugate BigOperators

namespace FormalResearch.NQubit.Pauli

/-- Configurations of `n` qubits. -/
abbrev Cfg (n : ℕ) := Fin n → Fin 2

/-- Weight of a Pauli word `a ∈ {I,X,Y,Z}ⁿ` (letter `0` is the identity). -/
def pauliWeight {n : ℕ} (a : Fin n → Fin 4) : ℕ := (Finset.univ.filter fun i => a i ≠ 0).card

/-- `⟨ψ | ⊗ᵢ pauliSU(aᵢ) ψ⟩`: the Pauli expectation up to the phase `(-i)^{pauliWeight a}`. -/
noncomputable def pexp {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) : ℂ :=
  ip ψ (rot (fun i => pauliSU (a i)) ψ)

/-- Squared Pauli expectation `⟨ψ|P_a|ψ⟩²`. -/
noncomputable def pauliSq {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) : ℝ := Complex.normSq (pexp ψ a)

/-- Pauli weight distribution `A_j = Σ_{pauliWeight P = j} ⟨P⟩²`. -/
noncomputable def weightEnum {n : ℕ} (ψ : Ψ n) (j : ℕ) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin n → Fin 4 => pauliWeight a = j), pauliSq ψ a

/-- The time-reversal overlap `τ_n = |⟨ψ, Θψ⟩|²`. -/
noncomputable def tau {n : ℕ} (ψ : Ψ n) : ℝ := Complex.normSq (ip ψ (Θ ψ))

theorem pauliWeight_le {n : ℕ} (a : Fin n → Fin 4) : pauliWeight a ≤ n := by
  unfold pauliWeight
  calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
    _ = n := by simp

theorem pauliSq_nonneg {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) : 0 ≤ pauliSq ψ a := Complex.normSq_nonneg _

theorem weightEnum_nonneg {n : ℕ} (ψ : Ψ n) (j : ℕ) : 0 ≤ weightEnum ψ j :=
  Finset.sum_nonneg fun a _ => pauliSq_nonneg ψ a

theorem weightEnum_eq_zero_of_gt {n : ℕ} (ψ : Ψ n) {j : ℕ} (h : n < j) : weightEnum ψ j = 0 := by
  unfold weightEnum
  apply Finset.sum_eq_zero
  intro a ha
  have := (Finset.mem_filter.mp ha).2
  have := pauliWeight_le a
  omega

/-- `Σ_j A_j = Σ_a pauliSq` (regrouping by weight). -/
theorem sum_weightEnum_eq {n : ℕ} (ψ : Ψ n) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.range (n + 1), f j * weightEnum ψ j = ∑ a : Fin n → Fin 4, f (pauliWeight a) * pauliSq ψ a := by
  unfold weightEnum
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin n → Fin 4)))
    (t := Finset.range (n + 1)) (g := pauliWeight) (fun a _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (pauliWeight_le a)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.mp ha).2]

/-! ### Generalised Pauli averaging -/

theorem wavg_aux {A X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (s : Finset A) (M : A → X → Y → ℂ) (w : A → ℂ) (K : X → Y → X → Y → ℂ)
    (h : ∀ x y x' y', ∑ a ∈ s, w a * (M a x y * conj (M a x' y')) = K x y x' y')
    (ψ : X → ℂ) (ψ' : Y → ℂ) :
    ∑ a ∈ s, w a * ((Complex.normSq (∑ x, conj (ψ x) * ∑ y, M a x y * ψ' y) : ℝ) : ℂ)
      = ∑ x, ∑ y, ∑ x', ∑ y', (conj (ψ x) * ψ' y * (ψ x' * conj (ψ' y'))) * K x y x' y' := by
  have h1 : ∀ a, w a * ((Complex.normSq (∑ x, conj (ψ x) * ∑ y, M a x y * ψ' y) : ℝ) : ℂ)
      = ∑ x, ∑ y, ∑ x', ∑ y', (conj (ψ x) * ψ' y * (ψ x' * conj (ψ' y'))) *
          (w a * (M a x y * conj (M a x' y'))) := by
    intro a
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, Complex.conj_conj]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => ?_
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [← Finset.mul_sum, h]

/-- One-qubit signed completeness: `Σ_b s_b U_b(x,y) \overline{U_b(x',y')} = 2 ε(x,y') ε(y,x')`
with `s_0 = 1`, `s_b = -1` otherwise. -/
theorem pauliSU_signed (x y x' y' : Fin 2) :
    ∑ b : Fin 4, (if b = 0 then (1 : ℂ) else -1) * (pauliSU b x y * conj (pauliSU b x' y'))
      = 2 * (eps x y' * eps y x') := by
  fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;>
    simp [pauliSU, eps, Fin.sum_univ_four] <;> norm_num

theorem pauli_signed_prod {n : ℕ} (x y x' y' : Cfg n) :
    ∑ a : Fin n → Fin 4, (∏ i, (if a i = 0 then (1 : ℂ) else -1)) *
        ((∏ i, pauliSU (a i) (x i) (y i)) * conj (∏ i, pauliSU (a i) (x' i) (y' i)))
      = (2 : ℂ) ^ n * ∏ i, (eps (x i) (y' i) * eps (y i) (x' i)) := by
  simp_rw [map_prod, ← Finset.prod_mul_distrib]
  rw [sum_prod_pi (fun i b => (if b = 0 then (1 : ℂ) else -1) *
    (pauliSU b (x i) (y i) * conj (pauliSU b (x' i) (y' i))))]
  simp_rw [pauliSU_signed]
  rw [Finset.prod_mul_distrib]
  simp

theorem conj_eps (a b : Fin 2) : conj (eps a b) = eps a b := by
  fin_cases a <;> fin_cases b <;> simp [eps]

theorem pexp_unfold {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) :
    pexp ψ a = ∑ x, conj (ψ x) * ∑ y, (∏ i, pauliSU (a i) (x i) (y i)) * ψ y := rfl

theorem pauliSq_cast {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) :
    (pauliSq ψ a : ℂ) = (Complex.normSq (∑ x, conj (ψ x) * ∑ y, (∏ i, pauliSU (a i) (x i) (y i)) * ψ y) : ℝ) := rfl

/-- `(-1)^{pauliWeight a} = ∏ᵢ s(aᵢ)`. -/
theorem signprod_eq {n : ℕ} (a : Fin n → Fin 4) :
    (∏ i, (if a i = 0 then (1 : ℂ) else -1)) = (-1 : ℂ) ^ pauliWeight a := by
  unfold pauliWeight
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]

/-- `Σ_a (-1)^{pauliWeight a} ⟨P_a⟩² = 2^n τ_n`. -/
theorem sum_signed_pauliSq {n : ℕ} (ψ : Ψ n) :
    ∑ a : Fin n → Fin 4, (-1 : ℝ) ^ pauliWeight a * pauliSq ψ a = (2 : ℝ) ^ n * tau ψ := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← signprod_eq, pauliSq_cast]
  rw [wavg_aux Finset.univ (fun (a : Fin n → Fin 4) (x y : Cfg n) => ∏ i, pauliSU (a i) (x i) (y i))
    (fun a => ∏ i, (if a i = 0 then (1 : ℂ) else -1))
    (fun x y x' y' => (2 : ℂ) ^ n * ∏ i, (eps (x i) (y' i) * eps (y i) (x' i)))
    (fun x y x' y' => pauli_signed_prod x y x' y') ψ ψ]
  -- now collapse
  have hT : ((tau ψ : ℝ) : ℂ) = (∑ x, conj (ψ x) * ∑ y, (∏ i, eps (x i) (y i)) * conj (ψ y)) *
      (∑ x, ψ x * ∑ y, (∏ i, eps (x i) (y i)) * ψ y) := by
    have e1 : ip ψ (Θ ψ) = ∑ x, conj (ψ x) * ∑ y, (∏ i, eps (x i) (y i)) * conj (ψ y) := rfl
    have e2 : conj (ip ψ (Θ ψ)) = ∑ x, ψ x * ∑ y, (∏ i, eps (x i) (y i)) * ψ y := by
      rw [e1]
      simp only [map_sum, map_mul, map_prod, Complex.conj_conj, conj_eps]
    unfold tau
    rw [Complex.normSq_eq_conj_mul_self]
    rw [mul_comm, ← e1, ← e2]
  rw [hT]
  have hterm : ∀ x y x' y' : Cfg n,
      (conj (ψ x) * ψ y * (ψ x' * conj (ψ y'))) *
        ((2 : ℂ) ^ n * ∏ i, (eps (x i) (y' i) * eps (y i) (x' i)))
      = (2 : ℂ) ^ n * ((conj (ψ x) * ((∏ i, eps (x i) (y' i)) * conj (ψ y'))) *
          (ψ y * ((∏ i, eps (y i) (x' i)) * ψ x'))) := by
    intro x y x' y'
    rw [Finset.prod_mul_distrib]; ring
  simp_rw [hterm]
  simp_rw [← Finset.mul_sum]
  congr 1
  have hT1 : (∑ x, conj (ψ x) * ∑ y, (∏ i, eps (x i) (y i)) * conj (ψ y))
      = ∑ x, ∑ y', conj (ψ x) * ((∏ i, eps (x i) (y' i)) * conj (ψ y')) := by
    simp only [Finset.mul_sum]
  have hT2 : (∑ x, ψ x * ∑ y, (∏ i, eps (x i) (y i)) * ψ y)
      = ∑ y, ∑ x', ψ y * ((∏ i, eps (y i) (x' i)) * ψ x') := by
    simp only [Finset.mul_sum]
  rw [hT1, hT2, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Finset.sum_comm

/-- `Σ_a ⟨P_a⟩² = 2^n ‖ψ‖⁴` (Pauli completeness). -/
theorem sum_pauliSq {n : ℕ} (ψ : Ψ n) : ∑ a : Fin n → Fin 4, pauliSq ψ a = (2 : ℝ) ^ n * (nsq ψ * nsq ψ) :=
  pauli_average ψ ψ

/-- `Σ_j A_j = 2^n ‖ψ‖⁴`. -/
theorem sum_weightEnum {n : ℕ} (ψ : Ψ n) :
    ∑ j ∈ Finset.range (n + 1), weightEnum ψ j = (2 : ℝ) ^ n * (nsq ψ * nsq ψ) := by
  have := sum_weightEnum_eq ψ (fun _ => 1)
  simp only [one_mul] at this
  rw [this]; exact sum_pauliSq ψ

/-- `Σ_j (-1)^j A_j = 2^n τ_n`. -/
theorem sum_signed_weightEnum {n : ℕ} (ψ : Ψ n) :
    ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * weightEnum ψ j = (2 : ℝ) ^ n * tau ψ := by
  rw [sum_weightEnum_eq ψ (fun j => (-1 : ℝ) ^ j)]
  exact sum_signed_pauliSq ψ

/-- `τ_n ≤ ‖ψ‖⁴` (Cauchy–Schwarz, `Θ` is norm-preserving). -/
theorem tau_le {n : ℕ} (ψ : Ψ n) : tau ψ ≤ nsq ψ * nsq ψ := by
  have h := normSq_ip_le ψ (Θ ψ)
  rw [nsq_Θ] at h
  exact h

theorem tau_nonneg {n : ℕ} (ψ : Ψ n) : 0 ≤ tau ψ := Complex.normSq_nonneg _

/-- For odd `n`, `τ_n = 0` (Kramers: `Θ² = -1`). -/
theorem tau_eq_zero_of_odd {n : ℕ} (hn : Odd n) (ψ : Ψ n) : tau ψ = 0 := by
  unfold tau; rw [ip_Θ_self_odd hn]; simp

/-- Twice the odd-weight Pauli mass: `2 Σ_{pauliWeight P odd} ⟨P⟩² = 2^n (‖ψ‖⁴ - τ_n)`. -/
theorem two_mul_sum_odd {n : ℕ} (ψ : Ψ n) :
    2 * ∑ a : Fin n → Fin 4, (if Odd (pauliWeight a) then pauliSq ψ a else 0)
      = (2 : ℝ) ^ n * (nsq ψ * nsq ψ - tau ψ) := by
  have h1 := sum_pauliSq ψ
  have h2 := sum_signed_pauliSq ψ
  have : ∀ a : Fin n → Fin 4, 2 * (if Odd (pauliWeight a) then pauliSq ψ a else 0)
      = pauliSq ψ a - (-1 : ℝ) ^ pauliWeight a * pauliSq ψ a := by
    intro a
    rcases Nat.even_or_odd (pauliWeight a) with h | h
    · simp [h.neg_one_pow, Nat.not_odd_iff_even.mpr h]
    · simp [h.neg_one_pow, h]; ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun a _ => this a, Finset.sum_sub_distrib, h1, h2]
  ring

/-- `Σ_a` over even words: `2 Σ_{pauliWeight P even} ⟨P⟩² = 2^n (‖ψ‖⁴ + τ_n)`. -/
theorem two_mul_sum_even {n : ℕ} (ψ : Ψ n) :
    2 * ∑ a : Fin n → Fin 4, (if Even (pauliWeight a) then pauliSq ψ a else 0)
      = (2 : ℝ) ^ n * (nsq ψ * nsq ψ + tau ψ) := by
  have h1 := sum_pauliSq ψ
  have h2 := sum_signed_pauliSq ψ
  have : ∀ a : Fin n → Fin 4, 2 * (if Even (pauliWeight a) then pauliSq ψ a else 0)
      = pauliSq ψ a + (-1 : ℝ) ^ pauliWeight a * pauliSq ψ a := by
    intro a
    rcases Nat.even_or_odd (pauliWeight a) with h | h
    · simp [h.neg_one_pow, h]; ring
    · simp [h.neg_one_pow, Nat.not_even_iff_odd.mpr h]
  rw [Finset.mul_sum, Finset.sum_congr rfl fun a _ => this a, Finset.sum_add_distrib, h1, h2]
  ring

/-- **Global Pauli parity (odd part).** For a unit vector,
`Σ_{j odd} A_j = 2^{n-1}(1 - τ_n)`, stated as `2 Σ_{j odd} A_j = 2^n (1 - τ_n)`. -/
theorem parity_odd {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) :
    2 * ∑ j ∈ (Finset.range (n + 1)).filter Odd, weightEnum ψ j = (2 : ℝ) ^ n * (1 - tau ψ) := by
  have h := two_mul_sum_odd ψ
  rw [hψ] at h
  have e : ∑ j ∈ (Finset.range (n + 1)).filter Odd, weightEnum ψ j
      = ∑ a : Fin n → Fin 4, (if Odd (pauliWeight a) then pauliSq ψ a else 0) := by
    have := sum_weightEnum_eq ψ (fun j => if Odd j then 1 else 0)
    rw [Finset.sum_filter]
    simp only [ite_mul, one_mul, zero_mul] at this
    rw [this]
  rw [e, h]; ring

/-- **Global Pauli parity (even part).** `2 Σ_{j even} A_j = 2^n (1 + τ_n)`. -/
theorem parity_even {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) :
    2 * ∑ j ∈ (Finset.range (n + 1)).filter Even, weightEnum ψ j = (2 : ℝ) ^ n * (1 + tau ψ) := by
  have h := two_mul_sum_even ψ
  rw [hψ] at h
  have e : ∑ j ∈ (Finset.range (n + 1)).filter Even, weightEnum ψ j
      = ∑ a : Fin n → Fin 4, (if Even (pauliWeight a) then pauliSq ψ a else 0) := by
    have := sum_weightEnum_eq ψ (fun j => if Even j then 1 else 0)
    rw [Finset.sum_filter]
    simp only [ite_mul, one_mul, zero_mul] at this
    rw [this]
  rw [e, h]; ring

/-- For odd `n`, exactly half of the Pauli weight is odd: `Σ_{j odd} A_j = 2^{n-1}`. -/
theorem parity_odd_of_odd {n : ℕ} (hn : Odd n) (ψ : Ψ n) (hψ : nsq ψ = 1) :
    2 * ∑ j ∈ (Finset.range (n + 1)).filter Odd, weightEnum ψ j = (2 : ℝ) ^ n := by
  rw [parity_odd ψ hψ, tau_eq_zero_of_odd hn]; ring

/-- **Global Pauli parity (last assertion).** For a unit vector, `τ_n = 1` iff every odd-weight
Pauli expectation vanishes (for odd `n` both sides are false). -/
theorem tau_eq_one_iff_odd_vanish {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) :
    tau ψ = 1 ↔ ∀ a : Fin n → Fin 4, Odd (pauliWeight a) → pauliSq ψ a = 0 := by
  have h := two_mul_sum_odd ψ
  rw [hψ] at h
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hnn : ∀ a ∈ (Finset.univ : Finset (Fin n → Fin 4)),
      0 ≤ (if Odd (pauliWeight a) then pauliSq ψ a else 0) := fun a _ => by
    split_ifs
    · exact pauliSq_nonneg ψ a
    · exact le_rfl
  constructor
  · intro ht a ha
    rw [ht] at h
    have hsum : ∑ a : Fin n → Fin 4, (if Odd (pauliWeight a) then pauliSq ψ a else 0) = 0 := by
      have : (2 : ℝ) * ∑ a : Fin n → Fin 4, (if Odd (pauliWeight a) then pauliSq ψ a else 0) = 0 := by
        rw [h]; ring
      linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum a (Finset.mem_univ a)
    simpa [ha] using this
  · intro hall
    have hsum : ∑ a : Fin n → Fin 4, (if Odd (pauliWeight a) then pauliSq ψ a else 0) = 0 :=
      Finset.sum_eq_zero fun a _ => by
        split_ifs with ha
        · exact hall a ha
        · rfl
    rw [hsum] at h
    have : (2 : ℝ) ^ n * (1 * 1 - tau ψ) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hpos.ne'
    linarith

end FormalResearch.NQubit.Pauli
