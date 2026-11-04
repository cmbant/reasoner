module

public import Mathlib

/-!
# `n`-qubit vectors

`n`-qubit vectors in the product basis (`Ψ n`), the inner product `ip` and squared norm `nsq`, local
`SU(2)^n` rotations `rot u`, the antiunitary time reversal `Θψ = ε^{⊗n} ψ̄` (with `Θ² = (-1)^n` and
`⟨ψ|Θψ⟩ = 0` for odd `n`), and the Pauli average
`∑_P |⟨ψ|P φ⟩|² = 2^n ‖ψ‖² ‖φ‖²` over the `4^n` Pauli products.
-/

@[expose] public section


open scoped ComplexConjugate Matrix BigOperators

namespace FormalResearch.NQubit

/-- `n`-qubit vectors, in the product basis. -/
abbrev Ψ (n : ℕ) := (Fin n → Fin 2) → ℂ

/-- One-qubit operators. -/
abbrev Op1 := Matrix (Fin 2) (Fin 2) ℂ

/-- `u ∈ SU(2)`. -/
def SU2 (u : Op1) : Prop := uᴴ * u = 1 ∧ u.det = 1

/-- The local operator `u₁ ⊗ ⋯ ⊗ uₙ`. -/
noncomputable def rot {n : ℕ} (u : Fin n → Op1) (ψ : Ψ n) : Ψ n :=
  fun x => ∑ y, (∏ i, u i (x i) (y i)) * ψ y

/-- Inner product, conjugate-linear in the first slot. -/
noncomputable def ip {n : ℕ} (ψ φ : Ψ n) : ℂ := ∑ x, conj (ψ x) * φ x

/-- Squared norm. -/
noncomputable def nsq {n : ℕ} (ψ : Ψ n) : ℝ := ∑ x, Complex.normSq (ψ x)

/-- `ε = iσ_y`. -/
def eps : Op1 := !![0, 1; -1, 0]

/-- Time reversal `Θψ = ε^{⊗n} ψ̄`. -/
noncomputable def Θ {n : ℕ} (ψ : Ψ n) : Ψ n :=
  fun x => ∑ y, (∏ i, eps (x i) (y i)) * conj (ψ y)

/-- The pointwise conjugate. -/
def cj {n : ℕ} (ψ : Ψ n) : Ψ n := fun x => conj (ψ x)

theorem Θ_eq_rot {n : ℕ} (ψ : Ψ n) : Θ ψ = rot (fun _ => eps) (cj ψ) := rfl

/-- Product over independent sites of a sum over the local basis. -/
theorem sum_prod_pi {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] (f : ι → κ → ℂ) :
    ∑ x : ι → κ, ∏ i, f i (x i) = ∏ i, ∑ b, f i b := by
  have := Finset.sum_prod_piFinset (ι := ι) (Finset.univ : Finset κ) f
  simpa [Fintype.piFinset_univ] using this

theorem rot_one {n : ℕ} (ψ : Ψ n) : rot (fun _ => (1 : Op1)) ψ = ψ := by
  funext x
  simp only [rot, Matrix.one_apply]
  simp_rw [Finset.prod_boole]
  have h : ∀ y : Fin n → Fin 2, (∀ i, x i = y i) ↔ x = y := fun y => (funext_iff).symm
  simp [h]

theorem rot_comp {n : ℕ} (u v : Fin n → Op1) (ψ : Ψ n) :
    rot u (rot v ψ) = rot (fun i => u i * v i) ψ := by
  funext x
  simp only [rot, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h : ∑ y : Fin n → Fin 2, (∏ i, u i (x i) (y i)) * ∏ i, v i (y i) (z i)
      = ∏ i, (u i * v i) (x i) (z i) := by
    simp_rw [← Finset.prod_mul_distrib]
    rw [sum_prod_pi (fun i b => u i (x i) b * v i b (z i))]
    simp [Matrix.mul_apply]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, h]

theorem conj_rot {n : ℕ} (u : Fin n → Op1) (ψ : Ψ n) :
    cj (rot u ψ) = rot (fun i => (u i).map conj) (cj ψ) := by
  funext x
  simp [cj, rot, map_sum, map_mul, map_prod]

theorem ip_aux {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] (U : X → Y → ℂ)
    (key : ∀ y z, ∑ x, conj (U x y) * U x z = if y = z then 1 else 0) (ψ φ : Y → ℂ) :
    ∑ x, conj (∑ y, U x y * ψ y) * ∑ z, U x z * φ z = ∑ y, conj (ψ y) * φ y := by
  have h1 : ∀ x, conj (∑ y, U x y * ψ y) * ∑ z, U x z * φ z
      = ∑ y, ∑ z, (conj (ψ y) * φ z) * (conj (U x y) * U x z) := by
    intro x
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [map_mul]
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, key]
  simp

theorem ip_rot {n : ℕ} (u : Fin n → Op1) (hu : ∀ i, (u i)ᴴ * u i = 1) (ψ φ : Ψ n) :
    ip (rot u ψ) (rot u φ) = ip ψ φ := by
  have key : ∀ y z : Fin n → Fin 2, ∑ x : Fin n → Fin 2, (∏ i, conj (u i (x i) (y i))) * ∏ i, u i (x i) (z i)
      = if y = z then 1 else 0 := by
    intro y z
    simp_rw [← Finset.prod_mul_distrib]
    rw [sum_prod_pi (fun i b => conj (u i b (y i)) * u i b (z i))]
    have : ∀ i, ∑ b, conj (u i b (y i)) * u i b (z i) = if y i = z i then 1 else 0 := by
      intro i
      have := congrFun (congrFun (hu i) (y i)) (z i)
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using this
    simp_rw [this]
    rw [Finset.prod_boole]
    simp [funext_iff]
  have := ip_aux (fun (x y : Fin n → Fin 2) => ∏ i, u i (x i) (y i))
    (by intro y z; simpa [map_prod] using key y z) ψ φ
  simpa [ip, rot] using this

/-! ### `SU(2)` facts -/

theorem SU2_unitary {u : Op1} (h : SU2 u) : uᴴ * u = 1 := h.1

theorem SU2_mul {u v : Op1} (hu : SU2 u) (hv : SU2 v) : SU2 (u * v) := by
  refine ⟨?_, by rw [Matrix.det_mul, hu.2, hv.2, one_mul]⟩
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, hu.1, Matrix.one_mul, hv.1]

theorem SU2_adjoint {u : Op1} (h : SU2 u) : SU2 uᴴ := by
  refine ⟨?_, by rw [Matrix.det_conjTranspose, h.2]; simp⟩
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.mp h.1

theorem SU2_one : SU2 (1 : Op1) := ⟨by simp, by simp⟩

theorem SU2_eps : SU2 eps := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> simp [eps, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [eps, Matrix.det_fin_two]

/-- For `u ∈ SU(2)`, the conjugate of `u` is `ε⁻¹ u ε`: `ε ū = u ε`. -/
theorem SU2_eps_conj {u : Op1} (h : SU2 u) : eps * u.map conj = u * eps := by
  have hadj : uᴴ = u.adjugate := by
    have h1 : u * u.adjugate = 1 := by rw [Matrix.mul_adjugate, h.2]; simp
    calc uᴴ = uᴴ * (u * u.adjugate) := by rw [h1, Matrix.mul_one]
      _ = u.adjugate := by rw [← Matrix.mul_assoc, h.1, Matrix.one_mul]
  have e00 := congrFun (congrFun hadj 0) 0
  have e01 := congrFun (congrFun hadj 0) 1
  have e10 := congrFun (congrFun hadj 1) 0
  have e11 := congrFun (congrFun hadj 1) 1
  simp [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps, Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11]

/-! ### `Θ` -/

theorem Θ_rot {n : ℕ} (u : Fin n → Op1) (hu : ∀ i, SU2 (u i)) (ψ : Ψ n) :
    Θ (rot u ψ) = rot u (Θ ψ) := by
  rw [Θ_eq_rot, Θ_eq_rot, conj_rot, rot_comp, rot_comp]
  congr 1
  funext i
  exact SU2_eps_conj (hu i)

theorem cj_cj {n : ℕ} (ψ : Ψ n) : cj (cj ψ) = ψ := by
  funext x; simp [cj]

theorem eps_conj_map : eps.map conj = eps := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [eps]

theorem eps_mul_eps : eps * eps = (-1 : ℂ) • (1 : Op1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [eps, Matrix.mul_apply, Fin.sum_univ_two]

theorem rot_const_smul {n : ℕ} (c : ℂ) (ψ : Ψ n) :
    rot (fun _ => c • (1 : Op1)) ψ = c ^ n • ψ := by
  funext x
  have h : ∀ y : Fin n → Fin 2, (∏ i, (c • (1 : Op1)) (x i) (y i)) = c ^ n * ∏ i, (1 : Op1) (x i) (y i) := by
    intro y
    simp [Finset.prod_mul_distrib]
  have := congrFun (rot_one ψ) x
  simp only [rot, h] at this ⊢
  simp only [mul_assoc, ← Finset.mul_sum, this]
  simp

/-- `Θ² = (-1)^n`. -/
theorem Θ_Θ {n : ℕ} (ψ : Ψ n) : Θ (Θ ψ) = ((-1 : ℂ) ^ n) • ψ := by
  rw [Θ_eq_rot, Θ_eq_rot, conj_rot, cj_cj, rot_comp]
  simp only [eps_conj_map, eps_mul_eps]
  exact rot_const_smul (-1) ψ

theorem ip_self {n : ℕ} (ψ : Ψ n) : ip ψ ψ = (nsq ψ : ℂ) := by
  simp [ip, nsq, Complex.normSq_eq_conj_mul_self]

theorem nsq_rot {n : ℕ} (u : Fin n → Op1) (hu : ∀ i, SU2 (u i)) (ψ : Ψ n) :
    nsq (rot u ψ) = nsq ψ := by
  have := ip_rot u (fun i => (hu i).1) ψ ψ
  rw [ip_self, ip_self] at this
  exact_mod_cast this

theorem nsq_cj {n : ℕ} (ψ : Ψ n) : nsq (cj ψ) = nsq ψ := by
  simp [nsq, cj]

/-- `‖Θψ‖ = ‖ψ‖`. -/
theorem nsq_Θ {n : ℕ} (ψ : Ψ n) : nsq (Θ ψ) = nsq ψ := by
  rw [Θ_eq_rot, nsq_rot _ (fun _ => SU2_eps), nsq_cj]

/-- `Θ` is antiunitary. -/
theorem ip_Θ_Θ {n : ℕ} (ψ φ : Ψ n) : ip (Θ ψ) (Θ φ) = conj (ip ψ φ) := by
  rw [Θ_eq_rot, Θ_eq_rot, ip_rot _ (fun _ => SU2_unitary SU2_eps)]
  simp [ip, cj, map_sum]

/-! ### Odd `n`: the time-reversal overlap vanishes -/

theorem eps_swap (a b : Fin 2) : eps b a = - eps a b := by
  fin_cases a <;> fin_cases b <;> simp [eps]

theorem eps_prod_swap {n : ℕ} (x y : Fin n → Fin 2) :
    ∏ i, eps (y i) (x i) = (-1) ^ n * ∏ i, eps (x i) (y i) := by
  have h : ∀ i, eps (y i) (x i) = (-1) * eps (x i) (y i) := by
    intro i; rw [eps_swap]; ring
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp

/-- **Odd `n`.** For odd `n`, `⟨ψ|Θψ⟩ = 0` for every `ψ`. -/
theorem ip_Θ_self_odd {n : ℕ} (hn : Odd n) (ψ : Ψ n) : ip ψ (Θ ψ) = 0 := by
  set S := ∑ x, ∑ y, (∏ i, eps (x i) (y i)) * (conj (ψ x) * conj (ψ y)) with hS
  have h : ip ψ (Θ ψ) = S := by
    simp only [ip, Θ, Finset.mul_sum, hS]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have h2 : S = -S := by
    calc S = ∑ y, ∑ x, (∏ i, eps (x i) (y i)) * (conj (ψ x) * conj (ψ y)) := Finset.sum_comm
      _ = ∑ y, ∑ x, -((∏ i, eps (y i) (x i)) * (conj (ψ y) * conj (ψ x))) := by
          refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
          rw [eps_prod_swap x y, hn.neg_one_pow]; ring
      _ = -S := by simp [hS, Finset.sum_neg_distrib]
  rw [h]
  exact self_eq_neg.mp h2

/-- For odd `n`, `Θ² = -1` (Kramers). -/
theorem Θ_Θ_odd {n : ℕ} (hn : Odd n) (ψ : Ψ n) : Θ (Θ ψ) = - ψ := by
  rw [Θ_Θ, hn.neg_one_pow]; simp

/-! ### Rotation overlap -/

theorem normSq_ip_le {n : ℕ} (ψ φ : Ψ n) : Complex.normSq (ip ψ φ) ≤ nsq ψ * nsq φ := by
  have h1 : ‖ip ψ φ‖ ≤ ∑ x, ‖ψ x‖ * ‖φ x‖ := by
    refine (norm_sum_le _ _).trans ?_
    simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x => ‖ψ x‖) (fun x => ‖φ x‖)
  rw [Complex.normSq_eq_norm_sq]
  have h0 : 0 ≤ ‖ip ψ φ‖ := norm_nonneg _
  calc ‖ip ψ φ‖ ^ 2 ≤ (∑ x, ‖ψ x‖ * ‖φ x‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2
    _ = _ := by simp [nsq, Complex.normSq_eq_norm_sq]

/-- The four elements `1, -iσ_x, -iσ_y, -iσ_z` of `SU(2)`; the Pauli matrices up to phases. -/
def pauliSU : Fin 4 → Op1 :=
  ![1, !![0, -Complex.I; -Complex.I, 0], !![0, -1; 1, 0], !![-Complex.I, 0; 0, Complex.I]]

theorem pauliSU_su2 (a : Fin 4) : SU2 (pauliSU a) := by
  fin_cases a
  · exact SU2_one
  all_goals
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [pauliSU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    · simp [pauliSU, Matrix.det_fin_two]

/-- One-qubit identity `∑_P P_{xy} \overline{P_{x'y'}} = 2 δ_{xx'} δ_{yy'}`. -/
theorem pauliSU_sum (x y x' y' : Fin 2) :
    ∑ a : Fin 4, pauliSU a x y * conj (pauliSU a x' y') = if x = x' ∧ y = y' then 2 else 0 := by
  fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;>
    simp [pauliSU, Fin.sum_univ_four] <;> norm_num

/-- Abstract averaging identity: a family `M a` with `∑_a M a x y \overline{M a x' y'} = c δδ`
has `∑_a |⟨ψ|M a φ⟩|² = c ‖ψ‖² ‖φ‖²`. -/
theorem avg_aux {A X Y : Type*} [Fintype A] [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (M : A → X → Y → ℂ) (c : ℝ)
    (h : ∀ x y x' y', ∑ a, M a x y * conj (M a x' y') = if x = x' ∧ y = y' then (c : ℂ) else 0)
    (ψ : X → ℂ) (φ : Y → ℂ) :
    ∑ a, Complex.normSq (∑ x, conj (ψ x) * ∑ y, M a x y * φ y)
      = c * ((∑ x, Complex.normSq (ψ x)) * ∑ y, Complex.normSq (φ y)) := by
  apply Complex.ofReal_injective
  push_cast
  have h1 : ∀ a, ((Complex.normSq (∑ x, conj (ψ x) * ∑ y, M a x y * φ y) : ℝ) : ℂ)
      = ∑ x, ∑ y, ∑ x', ∑ y', (conj (ψ x) * φ y * (ψ x' * conj (φ y'))) *
          (M a x y * conj (M a x' y')) := by
    intro a
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, Complex.conj_conj]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => by ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ x, ∑ a, ∑ y, ∑ x', ∑ y', (conj (ψ x) * φ y * (ψ x' * conj (φ y'))) *
          (M a x y * conj (M a x' y'))
      = ∑ y, ∑ x', ∑ y', (conj (ψ x) * φ y * (ψ x' * conj (φ y'))) *
          (if x = x' ∧ y = y' then (c : ℂ) else 0) := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y' _ => ?_
    rw [← Finset.mul_sum, h]
  simp_rw [h2]
  simp only [mul_ite, mul_zero]
  simp [ite_and, Finset.sum_ite_eq]
  simp only [Complex.normSq_eq_conj_mul_self]
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- The Pauli-product family satisfies the hypothesis of `avg_aux` with `c = 2^n`. -/
theorem pauli_prod_sum {n : ℕ} (x y x' y' : Fin n → Fin 2) :
    ∑ a : Fin n → Fin 4, (∏ i, pauliSU (a i) (x i) (y i)) * conj (∏ i, pauliSU (a i) (x' i) (y' i))
      = if x = x' ∧ y = y' then (((2 : ℝ) ^ n : ℝ) : ℂ) else 0 := by
  simp_rw [map_prod, ← Finset.prod_mul_distrib]
  rw [sum_prod_pi (fun i b => pauliSU b (x i) (y i) * conj (pauliSU b (x' i) (y' i)))]
  simp_rw [pauliSU_sum]
  by_cases hxy : x = x' ∧ y = y'
  · obtain ⟨rfl, rfl⟩ := hxy
    simp
  · rw [ite_eq_right_iff.mpr fun h => absurd h hxy]
    have : ∃ i, ¬ (x i = x' i ∧ y i = y' i) := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hxy ⟨funext fun i => (hc i).1, funext fun i => (hc i).2⟩
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right_iff.mpr fun h => absurd h hi)

/-- Pauli average: `∑_{P} |⟨ψ|P φ⟩|² = 2^n ‖ψ‖² ‖φ‖²`, the sum over the `4^n` products
`⊗ σ_{a_i}` (up to phases, `⊗ pauliSU (a i)`). -/
theorem pauli_average {n : ℕ} (ψ φ : Ψ n) :
    ∑ a : Fin n → Fin 4, Complex.normSq (ip ψ (rot (fun i => pauliSU (a i)) φ))
      = (2 : ℝ) ^ n * (nsq ψ * nsq φ) :=
  avg_aux (fun (a : Fin n → Fin 4) (x y : Fin n → Fin 2) => ∏ i, pauliSU (a i) (x i) (y i))
    ((2 : ℝ) ^ n) pauli_prod_sum ψ φ

theorem sum_append {m n : ℕ} (f : (Fin (m + n) → Fin 2) → ℂ) :
    ∑ x, f x = ∑ a : Fin m → Fin 2, ∑ b : Fin n → Fin 2, f (Fin.append a b) := by
  rw [← (Fin.appendEquiv m n).sum_comp, Fintype.sum_prod_type]
  rfl

end FormalResearch.NQubit
