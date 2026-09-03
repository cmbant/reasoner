import Mathlib
import FormalResearch.QIB1.ApolarFullRank

namespace FormalResearch.QIB1

open scoped BigOperators

/-- Real scalar extension of the full apolar differential matrix. -/
def apolarFullR (d : Nat) : Matrix (Fin (d - 2)) (Fin (d + 1)) ℝ :=
  fun r k => (apolarFull d r k : ℝ)

/-- Coefficient vector of `(x + b y)^d` in the monomial basis indexed by
y-degree. -/
def apolarCoherent (d : Nat) (b : ℝ) : Fin (d + 1) → ℝ :=
  fun k => (d.choose k.val : ℝ) * b ^ k.val

/-- The two columns which can contribute to row `r`. -/
def apolarColOne {d : Nat} (r : Fin (d - 2)) : Fin (d + 1) :=
  ⟨r.val + 1, by omega⟩

def apolarColThree {d : Nat} (r : Fin (d - 2)) : Fin (d + 1) :=
  ⟨r.val + 3, by omega⟩

/-- Two successive Pascal ratio identities combine to the coefficient equality
needed for cancellation between the `3∂ₓ²∂ᵧ` and `-∂ᵧ³` columns. -/
theorem apolar_choose_two_step (d r : Nat) :
    d.choose (r + 1) * (d - (r + 1)) * (d - (r + 2)) =
      d.choose (r + 3) * (r + 3) * (r + 2) := by
  have h1 :
      d.choose (r + 2) * (r + 2) =
        d.choose (r + 1) * (d - (r + 1)) := by
    simpa [Nat.add_assoc] using Nat.choose_succ_right_eq d (r + 1)
  have h2 :
      d.choose (r + 3) * (r + 3) =
        d.choose (r + 2) * (d - (r + 2)) := by
    simpa [Nat.add_assoc] using Nat.choose_succ_right_eq d (r + 2)
  calc
    d.choose (r + 1) * (d - (r + 1)) * (d - (r + 2)) =
        (d.choose (r + 2) * (r + 2)) * (d - (r + 2)) := by rw [h1]
    _ = (d.choose (r + 2) * (d - (r + 2))) * (r + 2) := by ring
    _ = (d.choose (r + 3) * (r + 3)) * (r + 2) := by rw [h2]
    _ = d.choose (r + 3) * (r + 3) * (r + 2) := by ring

/-- Every row of the full matrix has exactly the two expected nonzero
contributions. -/
theorem apolarFullR_mulVec_row {d : Nat} (v : Fin (d + 1) → ℝ)
    (r : Fin (d - 2)) :
    (apolarFullR d).mulVec v r =
      (apolarPivot d r.val : ℝ) * v (apolarColOne r) -
        ((r.val + 3 : Nat) : ℝ) * ((r.val + 2 : Nat) : ℝ) *
          ((r.val + 1 : Nat) : ℝ) * v (apolarColThree r) := by
  classical
  simp [apolarFullR, apolarFull, Matrix.mulVec, dotProduct,
    apolarColOne, apolarColThree]

/-- Exact coherent-state factorization of one apolar row. -/
theorem apolarFullR_coherent_row {d : Nat} (hd : 3 ≤ d) (b : ℝ)
    (r : Fin (d - 2)) :
    (apolarFullR d).mulVec (apolarCoherent d b) r =
      ((d.choose (r.val + 1) * (d - (r.val + 1)) *
          (d - (r.val + 2)) * (r.val + 1) : Nat) : ℝ) *
        b ^ (r.val + 1) * (3 - b^2) := by
  rw [apolarFullR_mulVec_row]
  simp only [apolarCoherent, apolarColOne, apolarColThree]
  have hr3 : r.val + 3 ≤ d := by omega
  have hr1 : r.val + 1 ≤ d := by omega
  have hr2 : r.val + 2 ≤ d := by omega
  have hp : b ^ (r.val + 3) = b ^ (r.val + 1) * b^2 := by
    rw [show r.val + 3 = (r.val + 1) + 2 by omega, pow_add]
  have hchoose := apolar_choose_two_step d r.val
  have hchooseR :
      ((d.choose (r.val + 1) * (d - (r.val + 1)) *
          (d - (r.val + 2)) : Nat) : ℝ) =
        ((d.choose (r.val + 3) * (r.val + 3) * (r.val + 2) : Nat) : ℝ) := by
    exact_mod_cast hchoose
  rw [hp]
  unfold apolarPivot
  push_cast [Nat.cast_sub hr1, Nat.cast_sub hr2]
  rw [show
      (d.choose (r.val + 3) : ℝ) * (r.val + 3) * (r.val + 2) =
        (d.choose (r.val + 1) : ℝ) * (d - (r.val + 1)) *
          (d - (r.val + 2)) by exact hchooseR.symm]
  ring

/-- Therefore every valence root `b(3-b²)=0` gives a coherent kernel vector. -/
theorem apolarCoherent_mem_kernel {d : Nat} (hd : 3 ≤ d) (b : ℝ)
    (hb : b = 0 ∨ b^2 = 3) :
    apolarCoherent d b ∈ LinearMap.ker (apolarFullR d).mulVecLin := by
  rw [LinearMap.mem_ker]
  ext r
  rw [apolarFullR_coherent_row hd b r]
  rcases hb with rfl | hb
  · simp
  · rw [hb]
    ring

/-- The two nontrivial real valence directions `b=±√3` are exact kernel
vectors. -/
theorem apolarCoherent_sqrt_three_mem_kernel {d : Nat} (hd : 3 ≤ d) :
    apolarCoherent d (Real.sqrt 3) ∈ LinearMap.ker (apolarFullR d).mulVecLin ∧
      apolarCoherent d (-Real.sqrt 3) ∈ LinearMap.ker (apolarFullR d).mulVecLin := by
  have hs : (Real.sqrt 3)^2 = 3 := by norm_num
  constructor
  · exact apolarCoherent_mem_kernel hd _ (Or.inr hs)
  · apply apolarCoherent_mem_kernel hd _ (Or.inr ?_)
    rw [neg_sq]
    exact hs

end FormalResearch.QIB1
