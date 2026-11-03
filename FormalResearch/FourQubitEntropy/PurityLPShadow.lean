module

public import FormalResearch.FourQubitEntropy.SpinFlipPauli

/-!
# Rains' shadow inequalities for pure `n`-qubit states

Source: `ResearchNotes/QI/seven_qubit_entanglement/even_qubit_purity_minima.tex` (the sentence after `eq:as`:
the coefficients `S_j` of `S(x,y) = Σ_j A_j ((x+3y)/2)^{n-j} ((y-x)/2)^j` are non-negative; Rains,
*Quantum shadow enumerators*, quant-ph/9611001).

`A ψ j` is the Pauli weight distribution of `SpinFlipPauli.lean`.  `S(x,y)` is homogeneous of degree `n`, so its
coefficient `S_i` of `x^{n-i} y^i` is the coefficient of `y^i` in `S(1,y)`; `shadowPoly ψ` is `S(1,y)`
(a `Polynomial ℝ`) and `shadowCoeff ψ i` is `S_i`.

**Proof used here (self-contained, not Rains' original).**  Give each qubit a *type* `τ ∈ {0,1,2,3}`.
Type `0` flips the qubit (kernel `ε`, weight `+1` on `I`, `-1` on `X,Y,Z`); type `c ∈ {1,2,3}` marks the axis `c`
(kernel `Z`, `1`, `X` for `c = 1,2,3`, weight `-1` on `c` and `+1` on the other two axes).  For every
type vector `t`, `Σ_P (∏ᵢ w_{tᵢ}(Pᵢ)) ⟨P⟩² = 2^n |β_t|²` (`sum_wloc_pw`) with `β_t = Σ_{x,y} ψ_x ψ_y ∏ κ_{tᵢ}(xᵢ,yᵢ)`;
this is the Pauli-completeness computation with a modified sign pattern.  Summing `y^{#{i : tᵢ ≠ 0}}`
over all `t` the weights multiply to `(1+3y)^{n-wt P} (y-1)^{wt P}` (`sum_over_types`), which is
`2^n S(1,y)`; hence `S_i = Σ_{t : #nonflip = i} |β_t|² ≥ 0` (`shadow_nonneg`, **proved**, for every vector).
-/

@[expose] public section


open scoped ComplexConjugate BigOperators
open FormalResearch.FrameFree.NQubit
open Polynomial

namespace FormalResearch.FourQubitEntropy.PurityLP

open FormalResearch.FourQubitEntropy.SpinFlip

/-- Per-qubit sign pattern of type `τ` on the letter `b` (`0 = I`, `1,2,3 = X,Y,Z`). -/
def wloc (τ b : Fin 4) : ℝ :=
  if τ = 0 then (if b = 0 then 1 else -1) else (if b = τ then -1 else 1)

/-- Per-qubit kernel of type `τ` (`ε`, `Z`, `1`, `X`). -/
def kap : Fin 4 → Op1 := ![eps, !![1, 0; 0, -1], !![1, 0; 0, 1], !![0, 1; 1, 0]]

theorem conj_kap (τ : Fin 4) (x y : Fin 2) : conj (kap τ x y) = kap τ x y := by
  fin_cases τ <;> fin_cases x <;> fin_cases y <;> simp [kap, eps]

theorem loc_kernel (τ : Fin 4) (x y x' y' : Fin 2) :
    ∑ b : Fin 4, (wloc τ b : ℂ) * (pauliSU b x y * conj (pauliSU b x' y'))
      = 2 * (kap τ x y' * kap τ y x') := by
  fin_cases τ <;> fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;>
    simp [wloc, pauliSU, kap, eps, Fin.sum_univ_four] <;> norm_num

theorem kernel_prod {n : ℕ} (t : Fin n → Fin 4) (x y x' y' : Cfg n) :
    ∑ a : Fin n → Fin 4, (∏ i, (wloc (t i) (a i) : ℂ)) *
        ((∏ i, pauliSU (a i) (x i) (y i)) * conj (∏ i, pauliSU (a i) (x' i) (y' i)))
      = (2 : ℂ) ^ n * ∏ i, (kap (t i) (x i) (y' i) * kap (t i) (y i) (x' i)) := by
  simp_rw [map_prod, ← Finset.prod_mul_distrib]
  rw [sum_prod_pi (fun i b => (wloc (t i) b : ℂ) *
    (pauliSU b (x i) (y i) * conj (pauliSU b (x' i) (y' i))))]
  simp_rw [loc_kernel]
  rw [Finset.prod_mul_distrib]
  simp

/-- `β_t = Σ_{x,y} ψ_x ψ_y ∏ᵢ κ_{tᵢ}(xᵢ,yᵢ)`. -/
noncomputable def bil {n : ℕ} (ψ : Ψ n) (t : Fin n → Fin 4) : ℂ :=
  ∑ x, ∑ y, ψ x * ψ y * ∏ i, kap (t i) (x i) (y i)

/-- `Σ_P (∏ᵢ w_{tᵢ}(Pᵢ)) ⟨P⟩² = 2^n |β_t|²`. -/
theorem sum_wloc_pw {n : ℕ} (ψ : Ψ n) (t : Fin n → Fin 4) :
    ∑ a : Fin n → Fin 4, (∏ i, wloc (t i) (a i)) * pw ψ a
      = (2 : ℝ) ^ n * Complex.normSq (bil ψ t) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [pw_cast]
  rw [wavg_aux Finset.univ (fun (a : Fin n → Fin 4) (x y : Cfg n) => ∏ i, pauliSU (a i) (x i) (y i))
    (fun a => ∏ i, (wloc (t i) (a i) : ℂ))
    (fun x y x' y' => (2 : ℂ) ^ n * ∏ i, (kap (t i) (x i) (y' i) * kap (t i) (y i) (x' i)))
    (fun x y x' y' => kernel_prod t x y x' y') ψ ψ]
  have hc : conj (bil ψ t) = ∑ x, ∑ y, conj (ψ x) * conj (ψ y) * ∏ i, kap (t i) (x i) (y i) := by
    unfold bil
    simp only [map_sum, map_mul, map_prod, conj_kap]
  rw [Complex.normSq_eq_conj_mul_self, hc]
  unfold bil
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y' _ => ?_
  rw [Finset.prod_mul_distrib]
  ring


/-! ### Summing over type vectors -/

/-- The number of non-flip positions of a type vector. -/
def nzc {n : ℕ} (t : Fin n → Fin 4) : ℕ := (Finset.univ.filter fun i => t i ≠ 0).card

/-- Regrouping a sum over Pauli words by weight (polynomial-valued version of `SpinFlip.sum_A_eq`). -/
theorem sum_A_poly {n : ℕ} (ψ : Ψ n) (g : ℕ → ℝ[X]) :
    ∑ a : Fin n → Fin 4, C (pw ψ a) * g (wt a)
      = ∑ j ∈ Finset.range (n + 1), C (A ψ j) * g j := by
  unfold A
  simp_rw [map_sum, Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin n → Fin 4)))
    (t := Finset.range (n + 1)) (g := wt)
    (fun a _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (wt_le a)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.mp ha).2]

theorem local_factor (b : Fin 4) :
    ∑ τ : Fin 4, (if τ ≠ 0 then (X : ℝ[X]) else 1) * C (wloc τ b)
      = if b = 0 then 1 + 3 * X else X - 1 := by
  fin_cases b <;> simp [wloc, Fin.sum_univ_four] <;> ring

theorem prod_local {n : ℕ} (a : Fin n → Fin 4) :
    ∏ i, (if a i = 0 then (1 + 3 * X : ℝ[X]) else X - 1)
      = (1 + 3 * X) ^ (n - wt a) * (X - 1) ^ wt a := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (Finset.univ.filter fun i => ¬ a i = 0).card = wt a := rfl
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => a i = 0)
  have h3 : (Finset.univ.filter fun i => a i = 0).card = n - wt a := by
    rw [Finset.card_univ, Fintype.card_fin] at h2
    omega
  rw [h1, h3]

/-- `Σ_t y^{#nonflip t} · 2^n |β_t|² = 2^n S(1,y)·` (before the factor `2^{-n}`). -/
theorem sum_over_types {n : ℕ} (ψ : Ψ n) :
    ∑ t : Fin n → Fin 4, (X : ℝ[X]) ^ nzc t * C ((2 : ℝ) ^ n * Complex.normSq (bil ψ t))
      = ∑ j ∈ Finset.range (n + 1), C (A ψ j) * ((1 + 3 * X) ^ (n - j) * (X - 1) ^ j) := by
  rw [← sum_A_poly ψ (fun j => (1 + 3 * X) ^ (n - j) * (X - 1) ^ j)]
  have h1 : ∀ t : Fin n → Fin 4, C ((2 : ℝ) ^ n * Complex.normSq (bil ψ t))
      = ∑ a : Fin n → Fin 4, C (∏ i, wloc (t i) (a i)) * C (pw ψ a) := by
    intro t
    rw [← sum_wloc_pw, map_sum]
    simp only [map_mul]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : ∀ t : Fin n → Fin 4, (X : ℝ[X]) ^ nzc t * (C (∏ i, wloc (t i) (a i)) * C (pw ψ a))
      = C (pw ψ a) * ∏ i, ((if t i ≠ 0 then (X : ℝ[X]) else 1) * C (wloc (t i) (a i))) := by
    intro t
    rw [Finset.prod_mul_distrib, map_prod]
    have : (∏ i, (if t i ≠ 0 then (X : ℝ[X]) else 1)) = X ^ nzc t := by
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      rfl
    rw [this]; ring
  simp_rw [h2]
  rw [← Finset.mul_sum]
  congr 1
  have h3 : ∑ t : Fin n → Fin 4, ∏ i, ((if t i ≠ 0 then (X : ℝ[X]) else 1) * C (wloc (t i) (a i)))
      = ∏ i, ∑ τ : Fin 4, (if τ ≠ 0 then (X : ℝ[X]) else 1) * C (wloc τ (a i)) := by
    rw [Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 4)))
      (fun i τ => (if τ ≠ 0 then (X : ℝ[X]) else 1) * C (wloc τ (a i))), Fintype.piFinset_univ]
  rw [h3]
  simp_rw [local_factor]
  exact prod_local a


/-! ### The shadow polynomial and its coefficients -/

/-- `S(1,y) = Σ_j A_j ((1+3y)/2)^{n-j} ((y-1)/2)^j`, i.e. `S(x,y)` at `x = 1`. -/
noncomputable def shadowPoly {n : ℕ} (ψ : Ψ n) : ℝ[X] :=
  ∑ j ∈ Finset.range (n + 1),
    C (A ψ j) * ((C (1 / 2) * (1 + 3 * X)) ^ (n - j) * (C (1 / 2) * (X - 1)) ^ j)

/-- The shadow coefficient `S_i`: the coefficient of `x^{n-i} y^i` in `S(x,y)`. -/
noncomputable def shadowCoeff {n : ℕ} (ψ : Ψ n) (i : ℕ) : ℝ := (shadowPoly ψ).coeff i

theorem shadowPoly_eq {n : ℕ} (ψ : Ψ n) :
    shadowPoly ψ = C ((1 / 2 : ℝ) ^ n) *
      ∑ j ∈ Finset.range (n + 1), C (A ψ j) * ((1 + 3 * X) ^ (n - j) * (X - 1) ^ j) := by
  unfold shadowPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [mul_pow, mul_pow]
  have : (C (1 / 2 : ℝ) : ℝ[X]) ^ (n - j) * C (1 / 2 : ℝ) ^ j = C ((1 / 2 : ℝ) ^ n) := by
    rw [← map_pow, ← map_pow, ← map_mul, ← pow_add, Nat.sub_add_cancel hj']
  calc C (A ψ j) * (C (1 / 2 : ℝ) ^ (n - j) * (1 + 3 * X) ^ (n - j) *
        (C (1 / 2 : ℝ) ^ j * (X - 1) ^ j))
      = C (A ψ j) * ((C (1 / 2 : ℝ) ^ (n - j) * C (1 / 2 : ℝ) ^ j) *
        ((1 + 3 * X) ^ (n - j) * (X - 1) ^ j)) := by ring
    _ = _ := by rw [this]; ring

/-- **Rains' shadow inequalities** (`even_qubit_purity_minima.tex`, after `eq:as`): every coefficient `S_i`
of `S(x,y) = Σ_j A_j ((x+3y)/2)^{n-j}((y-x)/2)^j` is non-negative, for every `n`-qubit vector (in particular
every pure state).  `S_i = Σ_{t : #nonflip(t) = i} |β_t|² ≥ 0`. -/
theorem shadow_nonneg {n : ℕ} (ψ : Ψ n) (i : ℕ) : 0 ≤ shadowCoeff ψ i := by
  unfold shadowCoeff
  rw [shadowPoly_eq, ← sum_over_types, coeff_C_mul, finsetSum_coeff]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ => ?_)
  rw [mul_comm, coeff_C_mul_X_pow]
  split_ifs
  · exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)
  · exact le_rfl


/-! ### Explicit rational form of the shadow coefficients -/

/-- The coefficient of `A_j` in `S_i`: `2^{-n} Σ_r C(n-j,r) 3^r C(j,i-r) (-1)^{j-(i-r)}`
(computable, for the kernel-checked dual certificates). -/
def shQ (n i j : ℕ) : ℚ :=
  (1 / 2 ^ n) * ∑ r ∈ Finset.range (i + 1),
    ((Nat.choose (n - j) r : ℚ) * 3 ^ r * (Nat.choose j (i - r) : ℚ) *
      (if (j - (i - r)) % 2 = 0 then 1 else -1))

theorem coeff_one_add_three_pow (m p : ℕ) :
    ((1 + 3 * X : ℝ[X]) ^ m).coeff p = 3 ^ p * (m.choose p : ℝ) := by
  have h : (1 + 3 * X : ℝ[X]) = C 3 * (X + C (1 / 3)) := by
    rw [mul_add, ← C_mul]
    have : (C (3 : ℝ) : ℝ[X]) = 3 := map_ofNat C 3
    rw [← this]; norm_num; ring
  rw [h, mul_pow, ← C_pow, coeff_C_mul, coeff_X_add_C_pow]
  by_cases hp : p ≤ m
  · have : (3 : ℝ) ^ m = 3 ^ p * 3 ^ (m - p) := by rw [← pow_add, Nat.add_sub_cancel' hp]
    rw [this]
    have h2 : (3 : ℝ) ^ (m - p) * (1 / 3) ^ (m - p) = 1 := by
      rw [← mul_pow]; norm_num
    calc (3 : ℝ) ^ p * 3 ^ (m - p) * ((1 / 3) ^ (m - p) * (m.choose p : ℝ))
        = 3 ^ p * (3 ^ (m - p) * (1 / 3) ^ (m - p)) * (m.choose p : ℝ) := by ring
      _ = _ := by rw [h2]; ring
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

theorem coeff_X_sub_one_pow (j q : ℕ) :
    ((X - 1 : ℝ[X]) ^ j).coeff q = (-1) ^ (j - q) * (j.choose q : ℝ) := by
  have h : (X - 1 : ℝ[X]) = X + C (-1) := by simp [sub_eq_add_neg]
  rw [h, coeff_X_add_C_pow]

theorem neg_one_pow_ite (k : ℕ) : ((-1 : ℝ) ^ k) = if k % 2 = 0 then 1 else -1 := by
  by_cases h : k % 2 = 0
  · simp only [h, ite_true]; exact Even.neg_one_pow (Nat.even_iff.mpr h)
  · simp only [h, ite_false]; exact Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))

theorem coeff_shadow_term (n i j : ℕ) (hj : j ≤ n) :
    ((C (1 / 2 : ℝ) * (1 + 3 * X)) ^ (n - j) * (C (1 / 2 : ℝ) * (X - 1)) ^ j).coeff i
      = (shQ n i j : ℝ) := by
  rw [mul_pow, mul_pow]
  have : (C (1 / 2 : ℝ) : ℝ[X]) ^ (n - j) * (1 + 3 * X) ^ (n - j) *
      (C (1 / 2 : ℝ) ^ j * (X - 1) ^ j)
      = C ((1 / 2 : ℝ) ^ n) * ((1 + 3 * X) ^ (n - j) * (X - 1) ^ j) := by
    have e : (C (1 / 2 : ℝ) : ℝ[X]) ^ (n - j) * C (1 / 2 : ℝ) ^ j = C ((1 / 2 : ℝ) ^ n) := by
      rw [← map_pow, ← map_pow, ← map_mul, ← pow_add, Nat.sub_add_cancel hj]
    calc _ = (C (1 / 2 : ℝ) ^ (n - j) * C (1 / 2 : ℝ) ^ j) *
          ((1 + 3 * X) ^ (n - j) * (X - 1) ^ j) := by ring
      _ = _ := by rw [e]
  rw [this, coeff_C_mul, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold shQ
  push_cast
  simp only [coeff_one_add_three_pow, coeff_X_sub_one_pow, neg_one_pow_ite]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> push_cast <;> simp only [one_div, inv_pow] <;> ring

/-- `S_i = Σ_j shQ n i j · A_j`. -/
theorem shadowCoeff_eq_lin {n : ℕ} (ψ : Ψ n) (i : ℕ) :
    shadowCoeff ψ i = ∑ j ∈ Finset.range (n + 1), (shQ n i j : ℝ) * A ψ j := by
  unfold shadowCoeff shadowPoly
  rw [finsetSum_coeff]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [coeff_C_mul, coeff_shadow_term n i j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
  ring

end FormalResearch.FourQubitEntropy.PurityLP
