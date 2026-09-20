import Mathlib

namespace FormalResearch.Gaudin

/-- One-coordinate Hamming mismatch. -/
def bitMismatch (a b : Bool) : Nat := if a = b then 0 else 1

theorem bitMismatch_self (a : Bool) : bitMismatch a a = 0 := by
  simp [bitMismatch]

theorem bitMismatch_symm (a b : Bool) : bitMismatch a b = bitMismatch b a := by
  by_cases h : a = b
  · subst b; simp [bitMismatch]
  · have h' : b ≠ a := by simpa [eq_comm] using h
    simp [bitMismatch, h, h']

theorem bitMismatch_triangle (a b c : Bool) :
    bitMismatch a c ≤ bitMismatch a b + bitMismatch b c := by
  cases a <;> cases b <;> cases c <;> decide

def hamming {ι : Type*} [Fintype ι] (a b : ι → Bool) : Nat :=
  ∑ i, bitMismatch (a i) (b i)

theorem hamming_self {ι : Type*} [Fintype ι] (a : ι → Bool) : hamming a a = 0 := by
  simp [hamming, bitMismatch]

theorem hamming_symm {ι : Type*} [Fintype ι] (a b : ι → Bool) :
    hamming a b = hamming b a := by
  unfold hamming
  apply Finset.sum_congr rfl
  intro i hi
  exact bitMismatch_symm _ _

theorem hamming_triangle {ι : Type*} [Fintype ι] (a b c : ι → Bool) :
    hamming a c ≤ hamming a b + hamming b c := by
  unfold hamming
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i hi => bitMismatch_triangle (a i) (b i) (c i)

/-- Weighted mismatch distance used by the Gaudin transition metric once edge and vertex
incidence data are encoded as Boolean indicator functions. -/
def weightedTreeDistance {E V : Type*} [Fintype E] [Fintype V]
    (ell nu : Nat) (e₁ e₂ : E → Bool) (v₁ v₂ : V → Bool) : Nat :=
  ell * hamming e₁ e₂ + nu * hamming v₁ v₂

theorem weightedTreeDistance_symm {E V : Type*} [Fintype E] [Fintype V]
    (ell nu : Nat) (e₁ e₂ : E → Bool) (v₁ v₂ : V → Bool) :
    weightedTreeDistance ell nu e₁ e₂ v₁ v₂ =
      weightedTreeDistance ell nu e₂ e₁ v₂ v₁ := by
  simp [weightedTreeDistance, hamming_symm]

theorem weightedTreeDistance_triangle {E V : Type*} [Fintype E] [Fintype V]
    (ell nu : Nat)
    (e₁ e₂ e₃ : E → Bool) (v₁ v₂ v₃ : V → Bool) :
    weightedTreeDistance ell nu e₁ e₃ v₁ v₃ ≤
      weightedTreeDistance ell nu e₁ e₂ v₁ v₂ +
      weightedTreeDistance ell nu e₂ e₃ v₂ v₃ := by
  have he := hamming_triangle e₁ e₂ e₃
  have hv := hamming_triangle v₁ v₂ v₃
  unfold weightedTreeDistance
  calc
    ell * hamming e₁ e₃ + nu * hamming v₁ v₃ ≤
        ell * (hamming e₁ e₂ + hamming e₂ e₃) +
          nu * (hamming v₁ v₂ + hamming v₂ v₃) := by
            exact Nat.add_le_add (Nat.mul_le_mul_left ell he) (Nat.mul_le_mul_left nu hv)
    _ = (ell * hamming e₁ e₂ + nu * hamming v₁ v₂) +
          (ell * hamming e₂ e₃ + nu * hamming v₂ v₃) := by
            simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm]

end FormalResearch.Gaudin
