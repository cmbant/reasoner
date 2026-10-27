import Mathlib
import FormalResearch.FrameFree.IsotypicBlind

/-!
# Isotypic blindness: the local label projectors (Paper P `thm:isotypicblind`)

Namespace `FormalResearch.FrameFree.IsotypicBlind`.  Claim class: **proved** (no hypothesis, no new axiom).
Continues `IsotypicBlind.lean` (read its header for the statement and for what is not formalized).

* `spinTensor P = ⊗_a P_a` on `Fin n × Fin k`, `P_a` acting on the `k` copies of spin `a`;
  it is symmetric and commutes with `ε^{⊗nk}` when every `P_a` does (`spinTensor_symm`,
  `spinTensor_comm_eps`);
* `casimirJ2 k`, `specProj k S t`, `totalSpinProj k m` and the joint label projector `labelProj k m`;
* `labelProb k m ψ = ⟨ψ^{⊗k}|Π_m|ψ^{⊗k}⟩` and the theorem `isotypic_blind`:
  `labelProb k m (Θψ) = labelProb k m ψ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
open FormalResearch.FrameFree.Twirls
open FormalResearch.FrameFree.NQubit (Ψ Θ eps)

namespace FormalResearch.FrameFree.IsotypicBlind

/-! ### Tensor products over spins of operators on the copies -/

section Spin

variable {n k : ℕ}

/-- `⊗_a P_a` on the slots `Fin n × Fin k`: `P_a` acts on the `k` copies of spin `a`. -/
noncomputable def spinTensor (P : Fin n → OpS (Fin k)) : OpS (Fin n × Fin k) :=
  Matrix.of fun x y => ∏ a, P a (fun c => x (a, c)) (fun c => y (a, c))

theorem spinTensor_mul (P Q : Fin n → OpS (Fin k)) :
    spinTensor P * spinTensor Q = spinTensor (fun a => P a * Q a) := by
  ext x z
  simp only [Matrix.mul_apply, spinTensor, Matrix.of_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Equiv.sum_comp (Equiv.curry (Fin n) (Fin k) (Fin 2)).symm]
  rw [← NQubit.sum_prod_pi (fun a b => P a (fun c => x (a, c)) b * Q a b (fun c => z (a, c)))]
  rfl

theorem spinTensor_transpose (P : Fin n → OpS (Fin k)) :
    (spinTensor P)ᵀ = spinTensor (fun a => (P a)ᵀ) := by
  ext x y
  simp [spinTensor]

theorem spinTensor_symm {P : Fin n → OpS (Fin k)} (h : ∀ a, (P a)ᵀ = P a) :
    (spinTensor P)ᵀ = spinTensor P := by
  rw [spinTensor_transpose]
  congr 1
  funext a
  exact h a

theorem epsOp_eq_spinTensor :
    epsOp (Fin n × Fin k) = spinTensor (fun _ => epsOp (Fin k)) := by
  ext x y
  simp only [epsOp, tensOp, spinTensor, Matrix.of_apply]
  rw [Fintype.prod_prod_type]

theorem spinTensor_comm_eps {P : Fin n → OpS (Fin k)}
    (h : ∀ a, P a * epsOp (Fin k) = epsOp (Fin k) * P a) :
    spinTensor P * epsOp (Fin n × Fin k) = epsOp (Fin n × Fin k) * spinTensor P := by
  rw [epsOp_eq_spinTensor, spinTensor_mul, spinTensor_mul]
  congr 1
  funext a
  exact h a

/-- **Any** family of local operators, symmetric and commuting with the spin flip `ε^{⊗k}` of the `k`
copies of its spin, has the same joint expectation in `ψ^{⊗k}` and `(Θψ)^{⊗k}`. -/
theorem expect_spinTensor_theta {P : Fin n → OpS (Fin k)} (hs : ∀ a, (P a)ᵀ = P a)
    (hc : ∀ a, P a * epsOp (Fin k) = epsOp (Fin k) * P a) (ψ : Ψ n) :
    expect (spinTensor P) (copyState k (Θ ψ)) = expect (spinTensor P) (copyState k ψ) :=
  expect_copyState_theta_of_symm (spinTensor_symm hs) (spinTensor_comm_eps hc) ψ

end Spin

/-! ### Casimir and total-spin projectors of `k` qubits -/

section Casimir

variable {k : ℕ}

/-- `∑_{c<d} P_{(c d)}`: the sum of the transposition operators of the `k` copies. -/
noncomputable def swapSum (k : ℕ) : OpS (Fin k) :=
  ∑ c, ∑ d ∈ Finset.Ioi c, permOp (Equiv.swap c d)

/-- The Casimir `J² = (3k/4 - k(k-1)/4)·1 + ∑_{c<d} P_{(c d)}` of `k` qubits, a real combination of copy
permutations (Dirac identity `σ_c·σ_d = 2 P_{(c d)} - 1`; `J² = j(j+1)` on total spin `j`). -/
noncomputable def casimirJ2 (k : ℕ) : OpS (Fin k) :=
  ((3 * (k : ℝ) / 4 - k * (k - 1) / 4) : ℝ) • (1 : OpS (Fin k)) + swapSum k

theorem permOp_transpose' {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) :
    (permOp σ)ᵀ = permOp σ⁻¹ := by
  ext x y
  have h := congrFun (congrFun (permOp_conjTranspose σ) x) y
  have h2 := congrFun (congrFun (permOp_map_conj σ) y) x
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def] at h h2
  simp only [Matrix.transpose_apply]
  rw [← h, h2]

theorem permOp_swap_transpose (c d : Fin k) : (permOp (Equiv.swap c d))ᵀ = permOp (Equiv.swap c d) := by
  rw [permOp_transpose', Equiv.swap_inv]

theorem swapSum_symm : (swapSum k)ᵀ = swapSum k := by
  simp only [swapSum, Matrix.transpose_sum, permOp_swap_transpose]

theorem casimirJ2_symm : (casimirJ2 k)ᵀ = casimirJ2 k := by
  simp only [casimirJ2, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, swapSum_symm]

theorem swapSum_comm : Commute (swapSum k) (epsOp (Fin k)) := by
  refine Commute.sum_left _ _ _ fun c _ => Commute.sum_left _ _ _ fun d _ => ?_
  exact (epsOp_commute_permOp _).symm

theorem casimirJ2_comm : Commute (casimirJ2 k) (epsOp (Fin k)) :=
  ((Commute.one_left _).smul_left _).add_left swapSum_comm

/-- The Lagrange polynomial `∏_{s ∈ S∖{t}} (X - s)/(t - s)`. -/
noncomputable def lagrange (S : Finset ℝ) (t : ℝ) : Polynomial ℝ :=
  ∏ s ∈ S.erase t, (Polynomial.C ((t - s)⁻¹) * (Polynomial.X - Polynomial.C s))

/-- The spectral projector onto the eigenvalue `t` of the Casimir, for a finite set `S` of eigenvalues
(Lagrange form: a real polynomial in `J²`). -/
noncomputable def specProj (k : ℕ) (S : Finset ℝ) (t : ℝ) : OpS (Fin k) :=
  Polynomial.aeval (casimirJ2 k) (lagrange S t)

/-- A real polynomial in a symmetric operator commuting with the flip is symmetric and commutes with it. -/
theorem aeval_symm_comm {T : OpS (Fin k)} (hs : Tᵀ = T) (hc : Commute T (epsOp (Fin k)))
    (p : Polynomial ℝ) :
    (Polynomial.aeval T p)ᵀ = Polynomial.aeval T p ∧ Commute (Polynomial.aeval T p) (epsOp (Fin k)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨?_, ?_⟩
    · rw [map_add, Matrix.transpose_add, hp.1, hq.1]
    · rw [map_add]; exact hp.2.add_left hq.2
  | monomial m a =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    refine ⟨?_, (hc.pow_left m).smul_left a⟩
    rw [Matrix.transpose_smul, Matrix.transpose_pow, hs]

theorem specProj_symm (S : Finset ℝ) (t : ℝ) : (specProj k S t)ᵀ = specProj k S t :=
  (aeval_symm_comm casimirJ2_symm casimirJ2_comm _).1

theorem specProj_comm (S : Finset ℝ) (t : ℝ) :
    specProj k S t * epsOp (Fin k) = epsOp (Fin k) * specProj k S t :=
  (aeval_symm_comm casimirJ2_symm casimirJ2_comm _).2

/-- `J²` on total spin `j = k/2 - m`. -/
noncomputable def spinEig (k m : ℕ) : ℝ := ((k : ℝ) / 2 - m) * ((k : ℝ) / 2 - m + 1)

/-- The possible eigenvalues `j(j+1)` of `J²` on `k` qubits: `j = k/2, k/2 - 1, …`. -/
noncomputable def spinSpec (k : ℕ) : Finset ℝ := (Finset.range (k / 2 + 1)).image (spinEig k)

/-- The projector onto total spin `j = k/2 - m` of `k` qubits. -/
noncomputable def totalSpinProj (k m : ℕ) : OpS (Fin k) := specProj k (spinSpec k) (spinEig k m)

/-- The joint label projector `Π_m = ⊗_a P^{(a)}_{j_a}`, `j_a = k/2 - m_a`. -/
noncomputable def labelProj {n : ℕ} (k : ℕ) (m : Fin n → ℕ) : OpS (Fin n × Fin k) :=
  spinTensor fun a => totalSpinProj k (m a)

end Casimir

/-! ### Isotypic blindness -/

section Blind

variable {n : ℕ}

/-- Probability of the joint local label `m` in `ψ^{⊗k}`: `⟨ψ^{⊗k}|Π_m|ψ^{⊗k}⟩`. -/
noncomputable def labelProb (k : ℕ) (m : Fin n → ℕ) (ψ : Ψ n) : ℂ :=
  expect (labelProj k m) (copyState k ψ)

/-- Real part of `labelProb` (the probability: `labelProb` is real because `Π_m` is Hermitian, which is
not needed for the equality below and not formalized). -/
noncomputable def labelDist (k : ℕ) (m : Fin n → ℕ) (ψ : Ψ n) : ℝ := (labelProb k m ψ).re

/-- **Theorem `thm:isotypicblind` (Isotypic blindness).**  For every `n`, `k`, every `ψ` (unit or not)
and every joint local label `m`, `k` copies of `Θψ` give the same label probability as `k` copies
of `ψ`. -/
theorem isotypic_blind (k : ℕ) (m : Fin n → ℕ) (ψ : Ψ n) :
    labelProb k m (Θ ψ) = labelProb k m ψ :=
  expect_spinTensor_theta (fun _ => specProj_symm _ _) (fun _ => specProj_comm _ _) ψ

theorem labelDist_theta (k : ℕ) (m : Fin n → ℕ) (ψ : Ψ n) :
    labelDist k m (Θ ψ) = labelDist k m ψ := by
  rw [labelDist, labelDist, isotypic_blind]

/-- Any event on the label tuple (any classical post-processing) has equal probability. -/
theorem sum_labelProb_eq (k : ℕ) (A : Finset (Fin n → ℕ)) (ψ : Ψ n) :
    ∑ m ∈ A, labelProb k m (Θ ψ) = ∑ m ∈ A, labelProb k m ψ :=
  Finset.sum_congr rfl fun m _ => isotypic_blind k m ψ

/-- Pushforward of the label distribution under any function `g` of the label tuple. -/
theorem sum_labelDist_fiber_eq {β : Type*} [DecidableEq β] (k : ℕ) (A : Finset (Fin n → ℕ))
    (g : (Fin n → ℕ) → β) (b : β) (ψ : Ψ n) :
    ∑ m ∈ A.filter (fun m => g m = b), labelDist k m (Θ ψ)
      = ∑ m ∈ A.filter (fun m => g m = b), labelDist k m ψ :=
  Finset.sum_congr rfl fun m _ => labelDist_theta k m ψ

/-- The same for an arbitrary family of local projectors (symmetric and commuting with `ε^{⊗k}`). -/
theorem labelProb_theta_eq_of_family {k : ℕ} {P : Fin n → OpS (Fin k)} (hs : ∀ a, (P a)ᵀ = P a)
    (hc : ∀ a, P a * epsOp (Fin k) = epsOp (Fin k) * P a) (ψ : Ψ n) :
    expect (spinTensor P) (copyState k (Θ ψ)) = expect (spinTensor P) (copyState k ψ) :=
  expect_spinTensor_theta hs hc ψ

end Blind

end FormalResearch.FrameFree.IsotypicBlind
