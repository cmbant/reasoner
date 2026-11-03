module

public import ThreeCopyQutritWerner.TwoCutDefs

@[expose] public section


/-!
# The bi-antisymmetric defect is a sum of squares

Appendix A uses `e(u, v) = ‖(I - F_L)(I - F_R)(u ⊗ v)‖²/4 ≥ 0`, where
`F_L`, `F_R` swap the `L`, resp. `R`, parts of two replicas.  Here this is proved in
the contraction form of `biDefect`:

`4 * biDefect u v = ∑ₚ |((1 - F_L)(1 - F_R)(u ⊗ v)) p|²`,

hence `0 ≤ biDefect u v`.  The abstract step: for commuting involutions `σ`, `τ` of
a finite index type and `g = f - f∘σ - f∘τ + f∘σ∘τ`, one has
`∑ conj(g) g = 4 ∑ conj(g) f`, because `g∘σ = -g` and `g∘τ = -g`.
-/

noncomputable section

open scoped ComplexConjugate

namespace ThreeCopyQutritWerner

section Abstract

variable {I : Type*} (σ τ : I ≃ I)

/-- `f - f ∘ σ - f ∘ τ + f ∘ σ ∘ τ`, the image of `f` under `(1 - σ)(1 - τ)`. -/
def antisymm4 (f : I → ℂ) (p : I) : ℂ := f p - f (σ p) - f (τ p) + f (σ (τ p))

theorem antisymm4_left (hσ : ∀ p, σ (σ p) = p) (hc : ∀ p, σ (τ p) = τ (σ p)) (f : I → ℂ)
    (p : I) : antisymm4 σ τ f (σ p) = -antisymm4 σ τ f p := by
  have e1 : τ (σ p) = σ (τ p) := (hc p).symm
  have e2 : σ (τ (σ p)) = τ p := by rw [e1, hσ]
  unfold antisymm4
  rw [hσ p, e2, e1]
  ring

theorem antisymm4_right (hτ : ∀ p, τ (τ p) = p) (f : I → ℂ) (p : I) :
    antisymm4 σ τ f (τ p) = -antisymm4 σ τ f p := by
  unfold antisymm4
  rw [hτ p]
  ring

variable [Fintype I]

theorem sum_conj_antisymm4_mul_comp_left (hσ : ∀ p, σ (σ p) = p)
    (hc : ∀ p, σ (τ p) = τ (σ p)) (f F : I → ℂ) :
    ∑ p, conj (antisymm4 σ τ f p) * F (σ p) = -∑ p, conj (antisymm4 σ τ f p) * F p := by
  calc ∑ p, conj (antisymm4 σ τ f p) * F (σ p)
      = ∑ p, conj (antisymm4 σ τ f (σ p)) * F (σ (σ p)) :=
        (Fintype.sum_equiv σ (fun p => conj (antisymm4 σ τ f (σ p)) * F (σ (σ p)))
          (fun q => conj (antisymm4 σ τ f q) * F (σ q)) (fun _ => rfl)).symm
    _ = ∑ p, -(conj (antisymm4 σ τ f p) * F p) :=
        Finset.sum_congr rfl fun p _ => by
          rw [antisymm4_left σ τ hσ hc f p, hσ p, map_neg, neg_mul]
    _ = -∑ p, conj (antisymm4 σ τ f p) * F p := Finset.sum_neg_distrib _

theorem sum_conj_antisymm4_mul_comp_right (hτ : ∀ p, τ (τ p) = p) (f F : I → ℂ) :
    ∑ p, conj (antisymm4 σ τ f p) * F (τ p) = -∑ p, conj (antisymm4 σ τ f p) * F p := by
  calc ∑ p, conj (antisymm4 σ τ f p) * F (τ p)
      = ∑ p, conj (antisymm4 σ τ f (τ p)) * F (τ (τ p)) :=
        (Fintype.sum_equiv τ (fun p => conj (antisymm4 σ τ f (τ p)) * F (τ (τ p)))
          (fun q => conj (antisymm4 σ τ f q) * F (τ q)) (fun _ => rfl)).symm
    _ = ∑ p, -(conj (antisymm4 σ τ f p) * F p) :=
        Finset.sum_congr rfl fun p _ => by
          rw [antisymm4_right σ τ hτ f p, hτ p, map_neg, neg_mul]
    _ = -∑ p, conj (antisymm4 σ τ f p) * F p := Finset.sum_neg_distrib _

/-- `∑ conj(g) g = 4 ∑ conj(g) f` for `g = (1 - σ)(1 - τ) f` with commuting involutions. -/
theorem sum_conj_antisymm4_mul_self (hσ : ∀ p, σ (σ p) = p) (hτ : ∀ p, τ (τ p) = p)
    (hc : ∀ p, σ (τ p) = τ (σ p)) (f : I → ℂ) :
    ∑ p, conj (antisymm4 σ τ f p) * antisymm4 σ τ f p =
      4 * ∑ p, conj (antisymm4 σ τ f p) * f p := by
  have h1 : ∑ p, conj (antisymm4 σ τ f p) * f (σ p) =
      -∑ p, conj (antisymm4 σ τ f p) * f p :=
    sum_conj_antisymm4_mul_comp_left σ τ hσ hc f f
  have h2 : ∑ p, conj (antisymm4 σ τ f p) * f (τ p) =
      -∑ p, conj (antisymm4 σ τ f p) * f p :=
    sum_conj_antisymm4_mul_comp_right σ τ hτ f f
  have h3 : ∑ p, conj (antisymm4 σ τ f p) * f (σ (τ p)) =
      -∑ p, conj (antisymm4 σ τ f p) * f (σ p) :=
    sum_conj_antisymm4_mul_comp_right σ τ hτ f (fun q => f (σ q))
  have hp : ∀ p, conj (antisymm4 σ τ f p) * antisymm4 σ τ f p =
      conj (antisymm4 σ τ f p) * f p - conj (antisymm4 σ τ f p) * f (σ p)
        - conj (antisymm4 σ τ f p) * f (τ p) + conj (antisymm4 σ τ f p) * f (σ (τ p)) := by
    intro p
    have e : antisymm4 σ τ f p = f p - f (σ p) - f (τ p) + f (σ (τ p)) := rfl
    rw [e]
    ring
  calc ∑ p, conj (antisymm4 σ τ f p) * antisymm4 σ τ f p
      = ∑ p, (conj (antisymm4 σ τ f p) * f p - conj (antisymm4 σ τ f p) * f (σ p)
          - conj (antisymm4 σ τ f p) * f (τ p) + conj (antisymm4 σ τ f p) * f (σ (τ p))) :=
        Finset.sum_congr rfl fun p _ => hp p
    _ = ∑ p, conj (antisymm4 σ τ f p) * f p - ∑ p, conj (antisymm4 σ τ f p) * f (σ p)
          - ∑ p, conj (antisymm4 σ τ f p) * f (τ p)
          + ∑ p, conj (antisymm4 σ τ f p) * f (σ (τ p)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = 4 * ∑ p, conj (antisymm4 σ τ f p) * f p := by
        rw [h3, h1, h2]
        ring

end Abstract

section Helpers

theorem ofReal_vecNormSq {ι : Type*} [Fintype ι] (u : ι → ℂ) :
    ((vecNormSq u : ℝ) : ℂ) = ∑ x, conj (u x) * u x := by
  unfold vecNormSq
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun x _ => Complex.normSq_eq_conj_mul_self

theorem conj_braket {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    conj (braket u v) = braket v u := by
  unfold braket
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, Complex.conj_conj]
  exact mul_comm _ _

theorem sum_perm_lrlr {A B : Type*} [Fintype A] [Fintype B] (G : A → B → A → B → ℂ) :
    ∑ l, ∑ r, ∑ l', ∑ r', G l r l' r' = ∑ r, ∑ r', ∑ l', ∑ l, G l r l' r' := by
  calc ∑ l, ∑ r, ∑ l', ∑ r', G l r l' r'
      = ∑ r, ∑ l, ∑ l', ∑ r', G l r l' r' := Finset.sum_comm
    _ = ∑ r, ∑ l, ∑ r', ∑ l', G l r l' r' :=
        Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ r, ∑ r', ∑ l, ∑ l', G l r l' r' :=
        Finset.sum_congr rfl fun r _ => Finset.sum_comm
    _ = ∑ r, ∑ r', ∑ l', ∑ l, G l r l' r' :=
        Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => Finset.sum_comm

theorem sum_perm_llrr {A B : Type*} [Fintype A] [Fintype B] (G : A → B → A → B → ℂ) :
    ∑ l, ∑ r, ∑ l', ∑ r', G l r l' r' = ∑ l, ∑ l', ∑ r', ∑ r, G l r l' r' := by
  refine Finset.sum_congr rfl fun l _ => ?_
  calc ∑ r, ∑ l', ∑ r', G l r l' r'
      = ∑ l', ∑ r, ∑ r', G l r l' r' := Finset.sum_comm
    _ = ∑ l', ∑ r', ∑ r, G l r l' r' := Finset.sum_congr rfl fun l' _ => Finset.sum_comm

end Helpers

section Concrete

variable {L R : Type*}

/-- Exchange the `L` components of a pair of indices of `L × R` (the replica swap `F_L`). -/
def swapLeft : ((L × R) × (L × R)) ≃ ((L × R) × (L × R)) where
  toFun p := ((p.2.1, p.1.2), (p.1.1, p.2.2))
  invFun p := ((p.2.1, p.1.2), (p.1.1, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exchange the `R` components of a pair of indices of `L × R` (the replica swap `F_R`). -/
def swapRight : ((L × R) × (L × R)) ≃ ((L × R) × (L × R)) where
  toFun p := ((p.1.1, p.2.2), (p.2.1, p.1.2))
  invFun p := ((p.1.1, p.2.2), (p.2.1, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- `((1 - F_L)(1 - F_R)(u ⊗ v)) p`: the vector whose squared norm is `4 e(u, v)` (Appendix A), at the
index pair `p`. -/
def biAnti (u v : L × R → ℂ) (p : (L × R) × (L × R)) : ℂ :=
  u p.1 * v p.2 - u (p.2.1, p.1.2) * v (p.1.1, p.2.2) - u (p.1.1, p.2.2) * v (p.2.1, p.1.2)
    + u p.2 * v p.1

variable [Fintype L] [Fintype R]

theorem sum_conj_tensor_self (u v : L × R → ℂ) :
    ∑ p : (L × R) × (L × R), conj (u p.1 * v p.2) * (u p.1 * v p.2) =
      ((vecNormSq u * vecNormSq v : ℝ) : ℂ) := by
  calc ∑ p : (L × R) × (L × R), conj (u p.1 * v p.2) * (u p.1 * v p.2)
      = ∑ p : (L × R) × (L × R), (conj (u p.1) * u p.1) * (conj (v p.2) * v p.2) :=
        Finset.sum_congr rfl fun p _ => by rw [map_mul]; ring
    _ = (∑ x, conj (u x) * u x) * (∑ y, conj (v y) * v y) :=
        sum_prod_single (fun x => conj (u x) * u x) (fun y => conj (v y) * v y)
    _ = ((vecNormSq u * vecNormSq v : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul, ofReal_vecNormSq, ofReal_vecNormSq]

theorem sum_conj_tensor_swap (u v : L × R → ℂ) :
    ∑ p : (L × R) × (L × R), conj (u p.2 * v p.1) * (u p.1 * v p.2) =
      ((Complex.normSq (braket v u) : ℝ) : ℂ) := by
  calc ∑ p : (L × R) × (L × R), conj (u p.2 * v p.1) * (u p.1 * v p.2)
      = ∑ p : (L × R) × (L × R), (conj (v p.1) * u p.1) * (conj (u p.2) * v p.2) :=
        Finset.sum_congr rfl fun p _ => by rw [map_mul]; ring
    _ = (∑ x, conj (v x) * u x) * (∑ y, conj (u y) * v y) :=
        sum_prod_single (fun x => conj (v x) * u x) (fun y => conj (u y) * v y)
    _ = ((Complex.normSq (braket v u) : ℝ) : ℂ) := by
        rw [Complex.normSq_eq_conj_mul_self, conj_braket v u]
        unfold braket
        ring

theorem sum_conj_tensor_swapLeft (u v : L × R → ℂ) :
    ∑ p : (L × R) × (L × R), conj (u (p.2.1, p.1.2) * v (p.1.1, p.2.2)) * (u p.1 * v p.2) =
      ((frobSq (ptraceL (ketBra u v)) : ℝ) : ℂ) := by
  have hT : ∀ r r' : R, ((Complex.normSq (ptraceL (ketBra u v) r r') : ℝ) : ℂ) =
      ∑ l', ∑ l, conj (u (l', r) * v (l, r')) * (u (l, r) * v (l', r')) := by
    intro r r'
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [ptraceL, ketBra, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  calc ∑ p : (L × R) × (L × R), conj (u (p.2.1, p.1.2) * v (p.1.1, p.2.2)) * (u p.1 * v p.2)
      = ∑ l, ∑ r, ∑ l', ∑ r', conj (u (l', r) * v (l, r')) * (u (l, r) * v (l', r')) := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ r, ∑ r', ∑ l', ∑ l, conj (u (l', r) * v (l, r')) * (u (l, r) * v (l', r')) :=
        sum_perm_lrlr (fun l r l' r' => conj (u (l', r) * v (l, r')) * (u (l, r) * v (l', r')))
    _ = ∑ r, ∑ r', ((Complex.normSq (ptraceL (ketBra u v) r r') : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => (hT r r').symm
    _ = ((frobSq (ptraceL (ketBra u v)) : ℝ) : ℂ) := by
        simp only [frobSq, Complex.ofReal_sum]

theorem sum_conj_tensor_swapRight (u v : L × R → ℂ) :
    ∑ p : (L × R) × (L × R), conj (u (p.1.1, p.2.2) * v (p.2.1, p.1.2)) * (u p.1 * v p.2) =
      ((frobSq (ptraceR (ketBra u v)) : ℝ) : ℂ) := by
  have hT : ∀ l l' : L, ((Complex.normSq (ptraceR (ketBra u v) l l') : ℝ) : ℂ) =
      ∑ r', ∑ r, conj (u (l, r') * v (l', r)) * (u (l, r) * v (l', r')) := by
    intro l l'
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [ptraceR, ketBra, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun r' _ => Finset.sum_congr rfl fun r _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  calc ∑ p : (L × R) × (L × R), conj (u (p.1.1, p.2.2) * v (p.2.1, p.1.2)) * (u p.1 * v p.2)
      = ∑ l, ∑ r, ∑ l', ∑ r', conj (u (l, r') * v (l', r)) * (u (l, r) * v (l', r')) := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ l, ∑ l', ∑ r', ∑ r, conj (u (l, r') * v (l', r)) * (u (l, r) * v (l', r')) :=
        sum_perm_llrr (fun l r l' r' => conj (u (l, r') * v (l', r)) * (u (l, r) * v (l', r')))
    _ = ∑ l, ∑ l', ((Complex.normSq (ptraceR (ketBra u v) l l') : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => (hT l l').symm
    _ = ((frobSq (ptraceR (ketBra u v)) : ℝ) : ℂ) := by
        simp only [frobSq, Complex.ofReal_sum]

/-- Appendix A: `4 e(u, v)` is the squared norm of `(1 - F_L)(1 - F_R)(u ⊗ v)`. -/
theorem four_mul_biDefect (u v : L × R → ℂ) :
    4 * biDefect u v = ∑ p : (L × R) × (L × R), Complex.normSq (biAnti u v p) := by
  have hσ : ∀ p : (L × R) × (L × R), swapLeft (swapLeft p) = p := fun _ => rfl
  have hτ : ∀ p : (L × R) × (L × R), swapRight (swapRight p) = p := fun _ => rfl
  have hc : ∀ p : (L × R) × (L × R), swapLeft (swapRight p) = swapRight (swapLeft p) :=
    fun _ => rfl
  have key : ∑ p : (L × R) × (L × R), conj (biAnti u v p) * biAnti u v p =
      4 * ∑ p : (L × R) × (L × R), conj (biAnti u v p) * (u p.1 * v p.2) :=
    sum_conj_antisymm4_mul_self swapLeft swapRight hσ hτ hc (fun q => u q.1 * v q.2)
  have hp : ∀ p : (L × R) × (L × R), conj (biAnti u v p) * (u p.1 * v p.2) =
      conj (u p.1 * v p.2) * (u p.1 * v p.2)
        - conj (u (p.2.1, p.1.2) * v (p.1.1, p.2.2)) * (u p.1 * v p.2)
        - conj (u (p.1.1, p.2.2) * v (p.2.1, p.1.2)) * (u p.1 * v p.2)
        + conj (u p.2 * v p.1) * (u p.1 * v p.2) := by
    intro p
    unfold biAnti
    rw [map_add, map_sub, map_sub]
    ring
  have hgf : ∑ p : (L × R) × (L × R), conj (biAnti u v p) * (u p.1 * v p.2) =
      ((vecNormSq u * vecNormSq v : ℝ) : ℂ) - ((frobSq (ptraceL (ketBra u v)) : ℝ) : ℂ)
        - ((frobSq (ptraceR (ketBra u v)) : ℝ) : ℂ)
        + ((Complex.normSq (braket v u) : ℝ) : ℂ) := by
    calc ∑ p : (L × R) × (L × R), conj (biAnti u v p) * (u p.1 * v p.2)
        = ∑ p : (L × R) × (L × R), (conj (u p.1 * v p.2) * (u p.1 * v p.2)
            - conj (u (p.2.1, p.1.2) * v (p.1.1, p.2.2)) * (u p.1 * v p.2)
            - conj (u (p.1.1, p.2.2) * v (p.2.1, p.1.2)) * (u p.1 * v p.2)
            + conj (u p.2 * v p.1) * (u p.1 * v p.2)) :=
          Finset.sum_congr rfl fun p _ => hp p
      _ = (∑ p : (L × R) × (L × R), conj (u p.1 * v p.2) * (u p.1 * v p.2))
            - (∑ p : (L × R) × (L × R),
                conj (u (p.2.1, p.1.2) * v (p.1.1, p.2.2)) * (u p.1 * v p.2))
            - (∑ p : (L × R) × (L × R),
                conj (u (p.1.1, p.2.2) * v (p.2.1, p.1.2)) * (u p.1 * v p.2))
            + (∑ p : (L × R) × (L × R), conj (u p.2 * v p.1) * (u p.1 * v p.2)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = _ := by
          rw [sum_conj_tensor_self u v, sum_conj_tensor_swapLeft u v,
            sum_conj_tensor_swapRight u v, sum_conj_tensor_swap u v]
  have hC : ((4 * biDefect u v : ℝ) : ℂ) =
      ((∑ p : (L × R) × (L × R), Complex.normSq (biAnti u v p) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    calc ((4 * biDefect u v : ℝ) : ℂ)
        = 4 * (((vecNormSq u * vecNormSq v : ℝ) : ℂ)
            - ((frobSq (ptraceL (ketBra u v)) : ℝ) : ℂ)
            - ((frobSq (ptraceR (ketBra u v)) : ℝ) : ℂ)
            + ((Complex.normSq (braket v u) : ℝ) : ℂ)) := by
          unfold biDefect ptraceNormSq
          push_cast
          ring
      _ = ∑ p : (L × R) × (L × R), conj (biAnti u v p) * biAnti u v p := by rw [key, hgf]
      _ = ∑ p : (L × R) × (L × R), ((Complex.normSq (biAnti u v p) : ℝ) : ℂ) :=
          Finset.sum_congr rfl fun p _ => Complex.normSq_eq_conj_mul_self.symm
  exact Complex.ofReal_injective hC

/-- Appendix A: the defect `e(u, v)` is nonnegative. -/
theorem biDefect_nonneg (u v : L × R → ℂ) : 0 ≤ biDefect u v := by
  have h := four_mul_biDefect u v
  have hs : 0 ≤ ∑ p : (L × R) × (L × R), Complex.normSq (biAnti u v p) :=
    Finset.sum_nonneg fun p _ => Complex.normSq_nonneg _
  linarith

end Concrete

end ThreeCopyQutritWerner

end
