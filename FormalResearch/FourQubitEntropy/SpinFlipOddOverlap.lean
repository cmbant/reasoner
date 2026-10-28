import FormalResearch.FourQubitEntropy.SpinFlipReduced
import FormalResearch.FourQubitEntropy.SpinFlipOddSector

/-!
# The spin-flip overlap `R_ρ` of a reduced state in Pauli coordinates

Source: `ResearchNotes/QI/seven_qubit_entanglement/spinflip_tradeoff.tex` (QIprojects PR #200),
`lem:odd-sector`, first part: for a `k`-qubit state `ρ_S`, `R_{ρ_S} = tr(ρ_S ρ̃_S)`,
`ρ̃_S = σ_y^{⊗k} ρ̄_S σ_y^{⊗k}`, satisfies `R_{ρ_S} = 2^{-k} Σ_{supp P ⊆ S} (-1)^{wt P} ⟨P⟩²`.

Here `ρ_S = rdm ψ S` is the explicit partial trace of `SpinFlipReduced.lean`, `sigY` the Pauli matrix `σ_y`,
`rdmTilde ψ S = σ_y^{⊗k} ρ̄_S σ_y^{⊗k}` and `Rspin ψ S = tr(ρ_S ρ̃_S)`.

* `kernel_signed_supp`: the signed completeness kernel on words supported in `S`;
* `two_pow_mul_Rspin`: `2^{|S|} R_{ρ_S} = Σ_{a ∈ wsupp S} (-1)^{wt a} ⟨P_a⟩²`  (proved for every `S`);
* `oddPur_eq`: `oddPur ψ S = ½(tr ρ_S² - Re R_{ρ_S})`, i.e. the Pauli-sector definition of
  `SpinFlipOddSector.lean` is `½(tr ρ_S² - R_{ρ_S})` (`lem:odd-sector`, second formula).
Claim class: **proved**.
-/

open scoped ComplexConjugate BigOperators
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.SpinFlip

variable {n : ℕ}

theorem kernel_signed_supp (S : Finset (Fin n)) (x y x' y' : Cfg n) :
    ∑ a ∈ wsupp S, (∏ i, (if a i = 0 then (1 : ℂ) else -1)) *
        ((∏ i, pauliSU (a i) (x i) (y i)) * conj (∏ i, pauliSU (a i) (x' i) (y' i)))
      = ∏ i, (if i ∈ S then 2 * (eps (x i) (y' i) * eps (y i) (x' i))
          else if (x i = y i ∧ x' i = y' i) then 1 else 0) := by
  simp_rw [map_prod]
  simp_rw [← Finset.prod_mul_distrib]
  unfold wsupp
  rw [← Finset.prod_univ_sum (fun i => if i ∈ S then (Finset.univ : Finset (Fin 4)) else {0})
    (fun i b => (if b = 0 then (1 : ℂ) else -1) *
      (pauliSU b (x i) (y i) * conj (pauliSU b (x' i) (y' i))))]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S
  · simp only [hi, ite_true]; exact pauliSU_signed _ _ _ _
  · simp only [hi, ite_false, Finset.sum_singleton]
    by_cases h1 : x i = y i <;> by_cases h2 : x' i = y' i <;> simp [pauliSU, h1, h2]

/-- `∏_{i ∈ S} ε(x_i, y_i)`, for full configurations. -/
noncomputable def epsS (S : Finset (Fin n)) (x y : Cfg n) : ℂ := ∏ i ∈ S, eps (x i) (y i)

/-- `∏_{i ∈ S} ε(x_i, y_i)` for configurations of `S`. -/
noncomputable def epsOn (S : Finset (Fin n)) (x y : CfgOn S) : ℂ := ∏ i : {i // i ∈ S}, eps (x i) (y i)

theorem epsS_glue (S : Finset (Fin n)) (x y : CfgOn S) (t t' : CfgOff S) :
    epsS S (glue S x t) (glue S y t') = epsOn S x y := by
  unfold epsS epsOn
  rw [← Finset.prod_coe_sort S]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [glue, i.2]

theorem kernel_factor (S : Finset (Fin n)) (x y x' y' : Cfg n) :
    ∏ i, (if i ∈ S then 2 * (eps (x i) (y' i) * eps (y i) (x' i))
          else if (x i = y i ∧ x' i = y' i) then 1 else 0)
      = 2 ^ S.card * (epsS S x y' * epsS S y x') *
          (if ∀ i, i ∉ S → (x i = y i ∧ x' i = y' i) then 1 else 0) := by
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_mul_distrib,
    Finset.prod_const]
  have h1 : ∏ i ∈ Finset.univ.filter (fun i => i ∉ S), (if (x i = y i ∧ x' i = y' i) then (1 : ℂ) else 0)
      = if ∀ i, i ∉ S → (x i = y i ∧ x' i = y' i) then 1 else 0 := by
    rw [Finset.prod_boole]
    simp
  rw [h1]
  unfold epsS
  rw [Finset.prod_mul_distrib]

/-- The Pauli matrix `σ_y`. -/
def sigY : Op1 := !![0, -Complex.I; Complex.I, 0]

/-- `σ_y^{⊗k}` on the qubits of `S`. -/
noncomputable def spinFlipMat (S : Finset (Fin n)) : Matrix (CfgOn S) (CfgOn S) ℂ :=
  fun x y => ∏ i : {i // i ∈ S}, sigY (x i) (y i)

/-- `ρ̃_S = σ_y^{⊗k} ρ̄_S σ_y^{⊗k}`. -/
noncomputable def rdmTilde (ψ : Ψ n) (S : Finset (Fin n)) : Matrix (CfgOn S) (CfgOn S) ℂ :=
  spinFlipMat S * (rdm ψ S).map conj * spinFlipMat S

/-- The spin-flip overlap `R_{ρ_S} = tr(ρ_S ρ̃_S)`. -/
noncomputable def Rspin (ψ : Ψ n) (S : Finset (Fin n)) : ℂ := (rdm ψ S * rdmTilde ψ S).trace

theorem sigY_eps (a b c d : Fin 2) : sigY a b * sigY c d = eps a b * eps d c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [sigY, eps]

theorem spinFlip_mul (S : Finset (Fin n)) (v p q u : CfgOn S) :
    spinFlipMat S v p * spinFlipMat S q u = epsOn S v p * epsOn S u q := by
  unfold spinFlipMat epsOn
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => sigY_eps _ _ _ _

theorem ite_t_of {α : Type*} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem ite_f_of {α : Type*} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

/-- Pair collapse: configurations agreeing off `S` are pairs `(glue v t, glue u t)`. -/
theorem pair_collapse (S : Finset (Fin n)) (F : Cfg n → Cfg n → ℂ) :
    ∑ x, ∑ y, F x y * (if ∀ i, i ∉ S → x i = y i then 1 else 0)
      = ∑ v : CfgOn S, ∑ u : CfgOn S, ∑ t : CfgOff S, F (glue S v t) (glue S u t) := by
  simp only [sum_cfg_glue S]
  have hI : ∀ (v u : CfgOn S) (tx ty : CfgOff S),
      (∀ i, i ∉ S → glue S v tx i = glue S u ty i) ↔ tx = ty := by
    intro v u tx ty
    constructor
    · intro h
      funext ⟨i, hi⟩
      simpa [glue, hi] using h i hi
    · rintro rfl i hi
      simp [glue, hi]
  simp only [hI]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]

theorem sum4_swap {α : Type*} [Fintype α] (f : α → α → α → α → ℂ) :
    ∑ x, ∑ y, ∑ x', ∑ y', f x y x' y' = ∑ x', ∑ y', ∑ x, ∑ y, f x y x' y' := by
  calc ∑ x, ∑ y, ∑ x', ∑ y', f x y x' y'
      = ∑ x, ∑ x', ∑ y, ∑ y', f x y x' y' := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x', ∑ x, ∑ y, ∑ y', f x y x' y' := Finset.sum_comm
    _ = ∑ x', ∑ x, ∑ y', ∑ y, f x y x' y' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x', ∑ y', ∑ x, ∑ y, f x y x' y' := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem Rspin_expand (ψ : Ψ n) (S : Finset (Fin n)) :
    Rspin ψ S = ∑ u, ∑ v, ∑ q, ∑ p, ∑ t', ∑ t,
      ψ (glue S u t) * conj (ψ (glue S v t)) *
        (spinFlipMat S v p * (conj (ψ (glue S p t')) * ψ (glue S q t')) * spinFlipMat S q u) := by
  unfold Rspin rdmTilde
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, rdm, map_sum, map_mul,
    Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]

theorem sum_move4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d
      = ∑ b, ∑ a, ∑ c, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, ∑ d, f a b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- **`lem:odd-sector`, first part (signed form).**
`2^{|S|} R_{ρ_S} = Σ_{a ∈ wsupp S} (-1)^{wt a} ⟨P_a⟩²`. -/
theorem two_pow_mul_Rspin (ψ : Ψ n) (S : Finset (Fin n)) :
    (2 : ℂ) ^ S.card * Rspin ψ S = ∑ a ∈ wsupp S, (((-1 : ℝ) ^ wt a * pw ψ a : ℝ) : ℂ) := by
  have h := wavg_aux (wsupp S)
    (fun (a : Fin n → Fin 4) (x y : Cfg n) => ∏ i, pauliSU (a i) (x i) (y i))
    (fun a => ∏ i, (if a i = 0 then (1 : ℂ) else -1))
    (fun x y x' y' => (2 : ℂ) ^ S.card * (epsS S x y' * epsS S y x') *
      (if ∀ i, i ∉ S → (x i = y i ∧ x' i = y' i) then 1 else 0))
    (fun x y x' y' => by rw [kernel_signed_supp, kernel_factor]) ψ ψ
  have hL : ∑ a ∈ wsupp S, (∏ i, (if a i = 0 then (1 : ℂ) else -1)) *
      ((Complex.normSq (∑ x, conj (ψ x) * ∑ y, (∏ i, pauliSU (a i) (x i) (y i)) * ψ y) : ℝ) : ℂ)
      = ∑ a ∈ wsupp S, (((-1 : ℝ) ^ wt a * pw ψ a : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [signprod_eq]
    push_cast
    rfl
  rw [← hL, h]
  -- split the indicator and collapse the two pairs
  have hI : ∀ x y x' y' : Cfg n,
      (if ∀ i, i ∉ S → (x i = y i ∧ x' i = y' i) then (1 : ℂ) else 0)
        = (if ∀ i, i ∉ S → x' i = y' i then 1 else 0) * (if ∀ i, i ∉ S → x i = y i then 1 else 0) := by
    intro x y x' y'
    by_cases h1 : ∀ i, i ∉ S → x' i = y' i
    · by_cases h2 : ∀ i, i ∉ S → x i = y i
      · have h3 : ∀ i, i ∉ S → (x i = y i ∧ x' i = y' i) := fun i hi => ⟨h2 i hi, h1 i hi⟩
        rw [ite_t_of h3, ite_t_of h1, ite_t_of h2, one_mul]
      · have h3 : ¬ ∀ i, i ∉ S → (x i = y i ∧ x' i = y' i) := fun h => h2 fun i hi => (h i hi).1
        rw [ite_f_of h3, ite_f_of h2, mul_zero]
    · have h3 : ¬ ∀ i, i ∉ S → (x i = y i ∧ x' i = y' i) := fun h => h1 fun i hi => (h i hi).2
      rw [ite_f_of h3, ite_f_of h1, zero_mul]
  set H : Cfg n → Cfg n → Cfg n → Cfg n → ℂ := fun x y x' y' =>
    conj (ψ x) * ψ y * (ψ x' * conj (ψ y')) *
      ((2 : ℂ) ^ S.card * (epsS S x y' * epsS S y x')) with hH
  have step1 : ∀ x y : Cfg n,
      ∑ x', ∑ y', conj (ψ x) * ψ y * (ψ x' * conj (ψ y')) *
        ((2 : ℂ) ^ S.card * (epsS S x y' * epsS S y x') *
          (if ∀ i, i ∉ S → (x i = y i ∧ x' i = y' i) then 1 else 0))
      = (∑ x', ∑ y', H x y x' y' * (if ∀ i, i ∉ S → x' i = y' i then 1 else 0)) *
          (if ∀ i, i ∉ S → x i = y i then 1 else 0) := by
    intro x y
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y' _ => ?_
    rw [hI]; simp only [hH]; ring
  simp_rw [step1]
  rw [pair_collapse S (fun x y => ∑ x', ∑ y', H x y x' y' *
    (if ∀ i, i ∉ S → x' i = y' i then 1 else 0))]
  have step2 : ∀ (v u : CfgOn S) (t : CfgOff S),
      ∑ x', ∑ y', H (glue S v t) (glue S u t) x' y' *
        (if ∀ i, i ∉ S → x' i = y' i then 1 else 0)
      = ∑ q : CfgOn S, ∑ p : CfgOn S, ∑ t' : CfgOff S,
        (2 : ℂ) ^ S.card * (conj (ψ (glue S v t)) * ψ (glue S u t) *
          (ψ (glue S q t') * conj (ψ (glue S p t'))) * (epsOn S v p * epsOn S u q)) := by
    intro v u t
    rw [pair_collapse S (fun x' y' => H (glue S v t) (glue S u t) x' y')]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ =>
      Finset.sum_congr rfl fun t' _ => ?_
    simp only [hH, epsS_glue]
    ring
  simp_rw [step2]
  rw [Rspin_expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [sum_move4 (fun (t : CfgOff S) (q p : CfgOn S) (t' : CfgOff S) =>
    (2 : ℂ) ^ S.card * (conj (ψ (glue S v t)) * ψ (glue S i t) *
      (ψ (glue S q t') * conj (ψ (glue S p t'))) * (epsOn S v p * epsOn S i q)))]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun t' _ => Finset.sum_congr rfl fun t _ => ?_
  have := spinFlip_mul S v p q i
  calc _ = 2 ^ S.card * (conj (ψ (glue S v t)) * ψ (glue S i t) *
      (ψ (glue S q t') * conj (ψ (glue S p t'))) * (spinFlipMat S v p * spinFlipMat S q i)) := by ring
    _ = _ := by rw [this]

/-- **`lem:odd-sector`, second part.**  The Pauli-sector quantity `oddPur ψ S` equals
`½ (tr ρ_S² - R_{ρ_S})` with `R_{ρ_S} = tr(ρ_S ρ̃_S)` for the explicit spin-flip `ρ̃_S = σ_y^{⊗|S|} ρ̄_S σ_y^{⊗|S|}`. -/
theorem oddPur_eq_half_sub_Rspin (ψ : Ψ n) (S : Finset (Fin n)) :
    ((oddPur ψ S : ℝ) : ℂ) = (((rdm ψ S) * (rdm ψ S)).trace - Rspin ψ S) / 2 := by
  have h2 : (2 : ℂ) ^ S.card ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [trace_rdm_sq]
  have hR : Rspin ψ S = (2 : ℂ)⁻¹ ^ S.card * ∑ a ∈ wsupp S, (((-1 : ℝ) ^ wt a * pw ψ a : ℝ) : ℂ) := by
    rw [← two_pow_mul_Rspin, ← mul_assoc, inv_pow, inv_mul_cancel₀ h2, one_mul]
  rw [hR]
  unfold oddPur
  have hsplit : ∑ a ∈ wsupp S, pw ψ a - ∑ a ∈ wsupp S, (-1 : ℝ) ^ wt a * pw ψ a
      = 2 * ∑ a ∈ (wsupp S).filter (fun a => Odd (wt a)), pw ψ a := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ho : Odd (wt a)
    · rw [ite_t_of ho, ho.neg_one_pow]; ring
    · have he : Even (wt a) := Nat.not_odd_iff_even.mp ho
      rw [ite_f_of ho, he.neg_one_pow]; ring
  have hc : (((∑ a ∈ wsupp S, pw ψ a) / 2 ^ S.card : ℝ) : ℂ) - (2 : ℂ)⁻¹ ^ S.card *
      ∑ a ∈ wsupp S, (((-1 : ℝ) ^ wt a * pw ψ a : ℝ) : ℂ)
      = (((∑ a ∈ wsupp S, pw ψ a - ∑ a ∈ wsupp S, (-1 : ℝ) ^ wt a * pw ψ a) / 2 ^ S.card : ℝ) : ℂ) := by
    push_cast
    rw [inv_pow]
    field_simp
  rw [hc, hsplit]
  push_cast
  ring

end FormalResearch.FourQubitEntropy.SpinFlip
