import FormalResearch.FourQubitEntropy.SevenQubitIcoPurity

/-!
# Pauli expansion of cut purities (part A: the algebra)

For a finite set `κ` of qubits and a matrix `M` on `κ → Bool`, write `trP M ν = ∑_{a,b} M a b ∏ᵢ σ_{νᵢ}(bᵢ,aᵢ)`
for the Pauli coefficient `tr (M P_ν)` of the Pauli string `ν : κ → Fin 4`. Two weighted
Parseval-type identities are proved for `M = ∑_r |Ψ(·,r)⟩⟨Ψ(·,r)|` (a reduced state):

* `sum_sq_trP`: `∑_ν |tr(M P_ν)|² = 2^{|κ|} ∑_{a,b} |M_{ab}|²`   (purity);
* `sum_sign_sq_trP`: `∑_ν (-1)^{wt ν} |tr(M P_ν)|² = 2^{|κ|} ∑_{r,r'} |A_{rr'}|² ≥ 0`
  with `A_{rr'} = ∑_{x,y} Ψ(x,r) ε(x,y) Ψ(y,r')` (the spin-flip / shadow positivity of Rains).
-/

open scoped ComplexConjugate
open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

/-- The Pauli matrices `I, X, Y, Z` in the computational basis (`false = 0`, `true = 1`), row `a`, column `b`. -/
def pauli (m : Fin 4) (a b : Bool) : ℂ :=
  match m with
  | 0 => if a = b then 1 else 0
  | 1 => if a = b then 0 else 1
  | 2 => if a = b then 0 else if a then Complex.I else -Complex.I
  | 3 => if a = b then (if a then -1 else 1) else 0

/-- The antisymmetric tensor `ε` of a qubit. -/
def eps (a b : Bool) : ℂ := if a = b then 0 else if a then -1 else 1

/-- Completeness of the Pauli matrices: `∑_m σ_m(a,b) conj σ_m(a',b') = 2 δ_{aa'} δ_{bb'}`. -/
theorem pauli_complete (a b a' b' : Bool) :
    ∑ m : Fin 4, pauli m a b * conj (pauli m a' b') = if a = a' ∧ b = b' then 2 else 0 := by
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp [Fin.sum_univ_four, pauli] <;> norm_num

/-- Sign-twisted completeness: `∑_m s_m σ_m(a,b) conj σ_m(a',b') = 2 ε(a,b') ε(b,a')`, `s_0 = 1`, `s_{1,2,3} = -1`. -/
theorem pauli_complete_sign (a b a' b' : Bool) :
    ∑ m : Fin 4, (if m = 0 then (1 : ℂ) else -1) * (pauli m a b * conj (pauli m a' b')) =
      2 * (eps a b' * eps b a') := by
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp [Fin.sum_univ_four, pauli, eps] <;> norm_num

section Algebra

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The Pauli coefficient `tr (M P_ν) = ∑_{a,b} M a b ∏ᵢ σ_{νᵢ}(bᵢ, aᵢ)`. -/
def trP (M : (κ → Bool) → (κ → Bool) → ℂ) (ν : κ → Fin 4) : ℂ :=
  ∑ a, ∑ b, M a b * ∏ i, pauli (ν i) (b i) (a i)

theorem trP_mul_conj (M : (κ → Bool) → (κ → Bool) → ℂ) (ν : κ → Fin 4) :
    trP M ν * conj (trP M ν) =
      ∑ a, ∑ a', ∑ b, ∑ b', (M a b * conj (M a' b')) *
        ∏ i, (pauli (ν i) (b i) (a i) * conj (pauli (ν i) (b' i) (a' i))) := by
  unfold trP
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun a' _ => ?_
  simp only [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun b' _ => ?_
  simp only [map_mul, map_prod, Finset.prod_mul_distrib]
  ring

/-- Weighted Parseval: summing `ω`-weighted squared Pauli coefficients over all Pauli strings. -/
theorem weighted_sum (ω : Fin 4 → ℂ) (M : (κ → Bool) → (κ → Bool) → ℂ) :
    ∑ ν : κ → Fin 4, (∏ i, ω (ν i)) * (trP M ν * conj (trP M ν)) =
      ∑ a, ∑ a', ∑ b, ∑ b', (M a b * conj (M a' b')) *
        ∏ i, (∑ m, ω m * (pauli m (b i) (a i) * conj (pauli m (b' i) (a' i)))) := by
  have h1 : ∀ ν : κ → Fin 4, (∏ i, ω (ν i)) * (trP M ν * conj (trP M ν)) =
      ∑ a, ∑ a', ∑ b, ∑ b', (M a b * conj (M a' b')) *
        ∏ i, (ω (ν i) * (pauli (ν i) (b i) (a i) * conj (pauli (ν i) (b' i) (a' i)))) := by
    intro ν
    rw [trP_mul_conj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp only [Finset.prod_mul_distrib]
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin 4)))
    (fun i m => ω m * (pauli m (b i) (a i) * conj (pauli m (b' i) (a' i)))), Fintype.piFinset_univ]

/-- Parseval for the unweighted sum: `∑_ν |tr(M P_ν)|² = 2^{|κ|} ∑_{a,b} |M_{ab}|²`. -/
theorem sum_sq_trP (M : (κ → Bool) → (κ → Bool) → ℂ) :
    ∑ ν : κ → Fin 4, Complex.normSq (trP M ν) =
      2 ^ Fintype.card κ * ∑ a, ∑ b, Complex.normSq (M a b) := by
  apply Complex.ofReal_injective
  have h := weighted_sum (fun _ => (1 : ℂ)) M
  have hk : ∀ a a' b b' : κ → Bool,
      ∏ i, (∑ m : Fin 4, pauli m (b i) (a i) * conj (pauli m (b' i) (a' i))) =
        if b = b' ∧ a = a' then 2 ^ Fintype.card κ else 0 := by
    intro a a' b b'
    simp only [pauli_complete]
    rw [Finset.prod_ite_zero]
    simp [funext_iff, forall_and, Finset.prod_const]
  simp only [one_mul, Finset.prod_const_one, hk] at h
  push_cast
  simp only [← Complex.mul_conj]
  rw [h]
  simp only [mul_ite, mul_zero, ite_and, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

theorem six_swap {A R : Type*} [Fintype A] [Fintype R] (F : A → A → A → A → R → R → ℂ) :
    ∑ a, ∑ a', ∑ b, ∑ b', ∑ r, ∑ r', F a a' b b' r r' =
      ∑ r, ∑ r', ∑ b, ∑ a', ∑ a, ∑ b', F a a' b b' r r' := by
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ?_ _ _ ?_
  · exact
    { toFun := fun p => (p.2.2.2.2.1, p.2.2.2.2.2, p.2.2.1, p.2.1, p.1, p.2.2.2.1)
      invFun := fun q => (q.2.2.2.2.1, q.2.2.2.1, q.2.2.1, q.2.2.2.2.2, q.1, q.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · intro p; rfl

/-- `ε` on strings of qubits. -/
def epsV (x y : κ → Bool) : ℂ := ∏ i, eps (x i) (y i)

theorem conj_eps (a b : Bool) : conj (eps a b) = eps a b := by
  cases a <;> cases b <;> simp [eps]

omit [DecidableEq κ] in
theorem conj_epsV (x y : κ → Bool) : conj (epsV x y) = epsV x y := by
  simp [epsV, map_prod, conj_eps]

/-- The spin-flip form `A_{rr'} = ∑_{x,y} Ψ(x,r) ε(x,y) Ψ(y,r')`. -/
def flipForm {ρ : Type*} [Fintype ρ] [DecidableEq ρ] (Ψ : (κ → Bool) → (ρ → Bool) → ℂ) (r r' : ρ → Bool) : ℂ :=
  ∑ x, ∑ y, Ψ x r * epsV x y * Ψ y r'

/-- Sign-weighted Parseval (shadow positivity of Rains): for `M = ∑_r |Ψ(·,r)⟩⟨Ψ(·,r)|`,
`∑_ν (-1)^{wt ν} |tr(M P_ν)|² = 2^{|κ|} ∑_{r,r'} |A_{rr'}|² ≥ 0`. -/
theorem sum_sign_sq_trP {ρ : Type*} [Fintype ρ] [DecidableEq ρ] (Ψ : (κ → Bool) → (ρ → Bool) → ℂ) :
    ∑ ν : κ → Fin 4, (∏ i, (if ν i = 0 then (1 : ℝ) else -1)) *
        Complex.normSq (trP (fun a b => ∑ r, Ψ a r * conj (Ψ b r)) ν) =
      2 ^ Fintype.card κ * ∑ r, ∑ r', Complex.normSq (flipForm Ψ r r') := by
  apply Complex.ofReal_injective
  have h := weighted_sum (fun m : Fin 4 => if m = 0 then (1 : ℂ) else -1)
    (fun a b => ∑ r, Ψ a r * conj (Ψ b r))
  have hk : ∀ a a' b b' : κ → Bool,
      ∏ i, (∑ m : Fin 4, (if m = 0 then (1 : ℂ) else -1) *
        (pauli m (b i) (a i) * conj (pauli m (b' i) (a' i)))) =
        2 ^ Fintype.card κ * (epsV b a' * epsV a b') := by
    intro a a' b b'
    simp only [fun i => pauli_complete_sign (b i) (a i) (b' i) (a' i), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, epsV]
  simp only [hk] at h
  have hL : ((∑ ν : κ → Fin 4, (∏ i, (if ν i = 0 then (1 : ℝ) else -1)) *
        Complex.normSq (trP (fun a b => ∑ r, Ψ a r * conj (Ψ b r)) ν) : ℝ) : ℂ) =
      ∑ ν : κ → Fin 4, (∏ i, (if ν i = 0 then (1 : ℂ) else -1)) *
        (trP (fun a b => ∑ r, Ψ a r * conj (Ψ b r)) ν *
          conj (trP (fun a b => ∑ r, Ψ a r * conj (Ψ b r)) ν)) := by
    have hc : ∀ m : Fin 4, (((if m = 0 then (1 : ℝ) else -1 : ℝ)) : ℂ) =
        if m = 0 then 1 else -1 := by
      intro m; split_ifs <;> simp
    push_cast
    simp only [hc, Complex.mul_conj]
  rw [hL, h]
  push_cast
  simp only [← Complex.mul_conj, flipForm, map_sum, Finset.mul_sum,
    Finset.sum_mul]
  refine (six_swap _).trans ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  refine Finset.sum_congr rfl fun r' _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a' _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b' _ => ?_
  simp only [map_mul, conj_epsV, Complex.conj_conj]
  ring

end Algebra

end FormalResearch.FourQubitEntropy.SevenQubitConseq
