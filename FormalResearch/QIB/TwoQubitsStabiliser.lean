import Mathlib
import FormalResearch.QIB.TwoQubitsCollective

/-!
# Every two-qubit vector has a nonzero `sl₂` stabiliser; Leibniz rule on `d` copies

Namespace `FormalResearch.QIB.TwoQubits`.  Claim class: **proved** (finite linear algebra).

* `exists_two_qubit_killer`: for every `x : (Fin 2 → Fin 2) → ℂ` there are `(α, β, γ) ≠ 0` with
  `(A ⊗ 1 + 1 ⊗ A) x = 0` for `A = α H₁ + β E₁ + γ F₁` (explicit stabiliser; the `3×3` system has
  determinant zero);
* `Lc_mulVec_copies`: hence `Lc d A` kills `x^{⊗d}` (Leibniz rule).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Matrix
open FormalResearch.FrameFree.Helstrom

namespace FormalResearch.QIB.TwoQubits

theorem sum_fn_two (f : (Fin 2 → Fin 2) → ℂ) : ∑ t : Fin 2 → Fin 2, f t = ∑ a : Fin 2, ∑ b : Fin 2, f ![a, b] := by
  rw [← (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm.sum_comp, Fintype.sum_prod_type]
  rfl

theorem coll_fin_two_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (s t : Fin 2 → Fin 2) :
    coll (I := Fin 2) A s t = A (s 0) (t 0) * (1 : Matrix (Fin 2) (Fin 2) ℂ) (s 1) (t 1)
      + (1 : Matrix (Fin 2) (Fin 2) ℂ) (s 0) (t 0) * A (s 1) (t 1) := by
  simp [coll, emb, kron, Fin.sum_univ_two, Fin.prod_univ_two]

theorem coll_mulVec_two (A : Matrix (Fin 2) (Fin 2) ℂ) (x : (Fin 2 → Fin 2) → ℂ) (s : Fin 2 → Fin 2) :
    (coll (I := Fin 2) A *ᵥ x) s = ∑ c, A (s 0) c * x ![c, s 1] + ∑ c, A (s 1) c * x ![s 0, c] := by
  simp only [Matrix.mulVec, dotProduct, coll_fin_two_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [sum_fn_two]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Matrix.one_apply]
  · rw [sum_fn_two]
    simp only [Fin.sum_univ_two, Matrix.one_apply]
    generalize s 0 = a
    fin_cases a <;> simp

def H1 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def E1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
def F1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

theorem matTriple_H1E1F1 : FormalResearch.QIB.Sl2Kernel.MatTriple H1 E1 F1 where
  HE := by ext i j; fin_cases i <;> fin_cases j <;> simp [H1, E1] <;> norm_num
  HF := by ext i j; fin_cases i <;> fin_cases j <;> simp [H1, F1] <;> norm_num
  EF := by ext i j; fin_cases i <;> fin_cases j <;> simp [H1, E1, F1]

/-- Every two-qubit vector is killed by a nonzero element of `sl₂(ℂ)` acting collectively. -/
theorem exists_two_qubit_killer (x : (Fin 2 → Fin 2) → ℂ) :
    ∃ α β γ : ℂ, (α ≠ 0 ∨ β ≠ 0 ∨ γ ≠ 0) ∧
      coll (I := Fin 2) (α • H1 + β • E1 + γ • F1) *ᵥ x = 0 := by
  have key : ∀ α β γ : ℂ, 2 * α * x ![0, 0] + β * (x ![0, 1] + x ![1, 0]) = 0 →
      γ * x ![0, 0] + β * x ![1, 1] = 0 →
      γ * (x ![0, 1] + x ![1, 0]) - 2 * α * x ![1, 1] = 0 →
      coll (I := Fin 2) (α • H1 + β • E1 + γ • F1) *ᵥ x = 0 := by
    intro α β γ h1 h2 h3
    funext s
    rw [coll_mulVec_two]
    obtain ⟨a, b, rfl⟩ : ∃ a b : Fin 2, s = ![a, b] := ⟨s 0, s 1, by ext i; fin_cases i <;> rfl⟩
    fin_cases a <;> fin_cases b <;>
      simp [H1, E1, F1, Fin.sum_univ_two] <;>
      first | linear_combination h1 | linear_combination h2 | linear_combination h3
  by_cases h00 : x ![0, 0] = 0
  · by_cases h11 : x ![1, 1] = 0
    · refine ⟨1, 0, 0, Or.inl one_ne_zero, key 1 0 0 ?_ ?_ ?_⟩ <;> simp [h00, h11]
    · refine ⟨x ![1, 1] * (x ![0, 1] + x ![1, 0]), 0 * 1, 2 * x ![1, 1] ^ 2, Or.inr (Or.inr ?_), key _ _ _ ?_ ?_ ?_⟩
      · exact mul_ne_zero two_ne_zero (pow_ne_zero 2 h11)
      · simp [h00]
      · simp [h00]
      · ring
  · refine ⟨(x ![0, 1] + x ![1, 0]) * x ![0, 0], -2 * x ![0, 0] ^ 2, 2 * x ![0, 0] * x ![1, 1],
      Or.inr (Or.inl ?_), key _ _ _ ?_ ?_ ?_⟩
    · exact mul_ne_zero (by norm_num) (pow_ne_zero 2 h00)
    · ring
    · ring
    · ring

/-- A factor killed by `Y` kills the tensor power. -/
theorem emb_mulVec_pow {d : ℕ} {α : Type*} [Fintype α] [DecidableEq α] (j : Fin d)
    (Y : Matrix α α ℂ) (x : α → ℂ) (hx : Y *ᵥ x = 0) :
    emb j Y *ᵥ (fun s : Fin d → α => ∏ i, x (s i)) = 0 := by
  unfold emb
  rw [kron_mulVec_prod (fun i => if i = j then Y else 1) (fun _ => x)]
  funext s
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hx])

/-- Leibniz rule: if the collective operator `coll A` kills `x` on one copy, then `Lc d A` kills
`x^{⊗ d}`. -/
theorem Lc_mulVec_copies (d : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (x : (Fin 2 → Fin 2) → ℂ)
    (hx : coll (I := Fin 2) A *ᵥ x = 0) : Lc d A *ᵥ copies d x = 0 := by
  unfold Lc coll copies
  rw [Matrix.sum_mulVec]
  exact Finset.sum_eq_zero fun j _ => emb_mulVec_pow j _ x hx

end FormalResearch.QIB.TwoQubits
