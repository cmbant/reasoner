module

public import FormalResearch.FourQubitEntropy.SpinFlipReduced
public import FormalResearch.FourQubitEntropy.SpinFlipOddSector

/-!
# The quantities of the Rains LP, for `n`-qubit pure states (Stage 1)

Source: `ResearchNotes/QI/seven_qubit_entanglement/even_qubit_purity_minima.tex`, the paragraph around `eq:as`
(`thm:lptable`).  Everything is reused from `SpinFlipPauli.lean`, `SpinFlipPurity.lean`, `SpinFlipReduced.lean`
and `SpinFlipOddSector.lean`; this file only checks that the quantities there are the paper's:

* `pauliMat`, `pauliExp ψ a = ⟨ψ|P_a|ψ⟩` for the genuine Hermitian Pauli string `P_a = ⊗ᵢ {I,X,Y,Z}`; `pexp`
  (with the phase-adjusted `pauliSU`) satisfies `pw ψ a = ⟨ψ|P_a|ψ⟩²` (`pw_eq_pauliExp_sq`), so
  `SpinFlip.A ψ j = Σ_{wt P = j} ⟨ψ|P|ψ⟩²` is the paper's `A_j`;
* `A_zero`: `A_0 = 1` for a unit vector; `SpinFlip.sum_A`: `Σ_j A_j = 2^n`;
* `piMean ψ k = C(n,k)^{-1} Σ_{|S| = k} tr (ρ_S²)` with `ρ_S = rdm ψ S` the explicit partial trace;
  `piMean_eq_purMean` identifies it with `SpinFlip.purMean`;
* `purMean_eq_lin`: `a_s = Σ_j aQ n s j · A_j`, `aQ n s j = C(n-j,s-j)/(2^s C(n,s))` for `j ≤ s` (`eq:as`);
* `purMean_compl`: `a_s = a_{n-s}` for a pure state.
-/

@[expose] public section


open scoped ComplexConjugate BigOperators
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.PurityLP

open FormalResearch.FourQubitEntropy.SpinFlip

/-- The genuine Hermitian Pauli matrices `I, X, Y, Z`. -/
def pauliMat : Fin 4 → Op1 :=
  ![1, !![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

/-- `pauliSU b = (-i)^{[b ≠ 0]} · pauliMat b`. -/
theorem pauliSU_eq (b : Fin 4) :
    pauliSU b = (if b = 0 then (1 : ℂ) else -Complex.I) • pauliMat b := by
  fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [pauliSU, pauliMat]

theorem conj_pauliMat (b : Fin 4) (x y : Fin 2) : conj (pauliMat b x y) = pauliMat b y x := by
  fin_cases b <;> fin_cases x <;> fin_cases y <;> simp [pauliMat]

/-- `⟨ψ| P_a |ψ⟩` for the Hermitian Pauli string `P_a = ⊗ᵢ pauliMat (a i)`. -/
noncomputable def pauliExp {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) : ℂ :=
  ip ψ (rot (fun i => pauliMat (a i)) ψ)

theorem pexp_eq {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) :
    pexp ψ a = (∏ i, (if a i = 0 then (1 : ℂ) else -Complex.I)) * pauliExp ψ a := by
  unfold pexp pauliExp ip rot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [pauliSU_eq, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

theorem normSq_phase {n : ℕ} (a : Fin n → Fin 4) :
    Complex.normSq (∏ i, (if a i = 0 then (1 : ℂ) else -Complex.I)) = 1 := by
  rw [map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs <;> simp

/-- `⟨ψ|P_a|ψ⟩` is real. -/
theorem pauliExp_im {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) : (pauliExp ψ a).im = 0 := by
  have h : conj (pauliExp ψ a) = pauliExp ψ a := by
    unfold pauliExp ip rot
    simp only [map_sum, map_mul, map_prod, Complex.conj_conj, conj_pauliMat]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  have := congrArg Complex.im h
  simp at this
  linarith

/-- **`SpinFlip.pw` is `⟨ψ|P|ψ⟩²`** for the genuine Hermitian Pauli string. -/
theorem pw_eq_pauliExp_sq {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) :
    pw ψ a = (pauliExp ψ a).re ^ 2 := by
  unfold pw
  rw [pexp_eq, map_mul, normSq_phase, one_mul, Complex.normSq_apply, pauliExp_im]
  ring

/-- `A_j = Σ_{wt P = j} ⟨ψ|P|ψ⟩²` with genuine Pauli strings. -/
theorem A_eq_sum_pauliExp {n : ℕ} (ψ : Ψ n) (j : ℕ) :
    A ψ j = ∑ a ∈ Finset.univ.filter (fun a : Fin n → Fin 4 => wt a = j), (pauliExp ψ a).re ^ 2 := by
  unfold A
  exact Finset.sum_congr rfl fun a _ => pw_eq_pauliExp_sq ψ a

theorem wt_eq_zero_iff {n : ℕ} (a : Fin n → Fin 4) : wt a = 0 ↔ a = fun _ => 0 := by
  unfold wt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h; funext i; by_contra hi; exact h (Finset.mem_univ i) hi
  · rintro rfl i _; simp

/-- `A_0 = 1` for a unit vector. -/
theorem A_zero {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) : A ψ 0 = 1 := by
  unfold A
  have : Finset.univ.filter (fun a : Fin n → Fin 4 => wt a = 0) = {fun _ => 0} := by
    ext a; simp [wt_eq_zero_iff]
  rw [this, Finset.sum_singleton]
  unfold pw pexp
  have h1 : (fun i : Fin n => pauliSU ((fun _ => (0 : Fin 4)) i)) = fun _ => (1 : Op1) := by
    funext i; rfl
  rw [h1, rot_one, ip_self, hψ]
  simp

/-! ### The mean purities `a_s` -/

/-- `π_k(ψ) = C(n,k)^{-1} Σ_{|S|=k} tr(ρ_S²)` with `ρ_S` the explicit partial trace. -/
noncomputable def piMean {n : ℕ} (ψ : Ψ n) (k : ℕ) : ℝ :=
  (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (Matrix.trace (rdm ψ S * rdm ψ S)).re)
    / (Nat.choose n k : ℝ)

theorem piMean_eq_purMean {n : ℕ} (ψ : Ψ n) (k : ℕ) : piMean ψ k = purMean ψ k := by
  unfold piMean purMean Pur PurU
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← purC_eq_trace]
  rfl

/-- The coefficient of `A_j` in `a_s` (`eq:as`). -/
def aQ (n s j : ℕ) : ℚ :=
  if j ≤ s then (Nat.choose (n - j) (s - j) : ℚ) / (2 ^ s * (Nat.choose n s : ℚ)) else 0

/-- **`eq:as`**: `a_s = (2^s C(n,s))^{-1} Σ_{j ≤ s} C(n-j,s-j) A_j`. -/
theorem purMean_eq_lin {n : ℕ} (ψ : Ψ n) {s : ℕ} (hs : s ≤ n) :
    purMean ψ s = ∑ j ∈ Finset.range (n + 1), (aQ n s j : ℝ) * A ψ j := by
  have h := Pur_eq ψ s
  have hC : (Nat.choose n s : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hs).ne'
  have h2 : (2 : ℝ) ^ s ≠ 0 := by positivity
  unfold purMean
  rw [div_eq_iff hC]
  have h3 : Pur ψ s = (∑ j ∈ Finset.range (n + 1),
      (if j ≤ s then (Nat.choose (n - j) (s - j) : ℝ) else 0) * A ψ j) / 2 ^ s := by
    rw [← h]; field_simp
  rw [h3, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold aQ
  by_cases hj : j ≤ s
  · simp only [hj, ite_true]; push_cast; field_simp
  · simp [hj]

/-- **`a_s = a_{n-s}`** for a pure state. -/
theorem purMean_compl {n : ℕ} (ψ : Ψ n) {s : ℕ} (hs : s ≤ n) : purMean ψ s = purMean ψ (n - s) := by
  unfold purMean
  rw [Pur_compl ψ s hs, ← Nat.choose_symm hs]

end FormalResearch.FourQubitEntropy.PurityLP
