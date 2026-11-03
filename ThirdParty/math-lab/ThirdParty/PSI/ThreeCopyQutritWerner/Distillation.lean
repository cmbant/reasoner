module

public import ThreeCopyQutritWerner.Basic

@[expose] public section


/-!
# Operational (local rank-two filter) form of distillability

`IsOneCopyRankTwoDetectable` and `IsThreeCopyRankTwoDetectable` in `Basic` are stated in the
Schmidt-rank-two form.  This module states the operational form, "some local
filter `A ⊗ B` onto two qubits produces an NPT two-qubit operator", and proves
that for a Hermitian `ρ` it is equivalent to the Schmidt-rank-two criterion.
-/

noncomputable section

open scoped BigOperators ComplexOrder
open Matrix

namespace ThreeCopyQutritWerner

variable {m n : Type*}

section Helpers

theorem sum_comm_13 {β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ] (G : β → γ → δ → ℂ) :
    ∑ b, ∑ c, ∑ d, G b c d = ∑ d, ∑ c, ∑ b, G b c d := by
  calc ∑ b, ∑ c, ∑ d, G b c d = ∑ c, ∑ b, ∑ d, G b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, G b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ b, G b c d := Finset.sum_comm

theorem sum_comm_22 {X P : Type*} [Fintype X] [Fintype P] (F : X → X → P → P → ℂ) :
    ∑ x, ∑ y, ∑ p, ∑ q, F x y p q = ∑ p, ∑ q, ∑ x, ∑ y, F x y p q := by
  calc ∑ x, ∑ y, ∑ p, ∑ q, F x y p q
      = ∑ x, ∑ p, ∑ y, ∑ q, F x y p q := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ p, ∑ x, ∑ y, ∑ q, F x y p q := Finset.sum_comm
    _ = ∑ p, ∑ x, ∑ q, ∑ y, F x y p q :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ p, ∑ q, ∑ x, ∑ y, F x y p q := Finset.sum_congr rfl fun p _ => Finset.sum_comm

theorem star_sum_mul_mul_sum {X Y : Type*} [Fintype X] [Fintype Y] (a : X → ℂ) (r : ℂ)
    (b : Y → ℂ) :
    star (∑ x, a x) * r * (∑ y, b y) = ∑ x, ∑ y, star (a x) * r * b y := by
  rw [star_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]

end Helpers

/-- The sesquilinear expectation is Mathlib's `star φ ⬝ᵥ M *ᵥ φ`. -/
theorem expectation_eq_dotProduct {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (φ : ι → ℂ) :
    expectation M φ = star φ ⬝ᵥ (M *ᵥ φ) := by
  have h : ∀ x : ι, ∑ y, star (φ x) * M x y * φ y = star φ x * (M *ᵥ φ) x := by
    intro x
    show _ = star (φ x) * ∑ y, M x y * φ y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => mul_assoc _ _ _
  unfold expectation
  show (∑ x, ∑ y, star (φ x) * M x y * φ y) = ∑ x, star φ x * (M *ᵥ φ) x
  exact Finset.sum_congr rfl fun x _ => h x

/-- The expectation of a Hermitian matrix is real. -/
theorem expectation_im_eq_zero_of_isHermitian {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ)
    (hM : M.IsHermitian) (φ : ι → ℂ) : (expectation M φ).im = 0 := by
  have hstar : star (expectation M φ) = expectation M φ := by
    unfold expectation
    rw [star_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [star_mul', star_star, hM.apply]
    ring
  have h2 : (star (expectation M φ)).im = -(expectation M φ).im := by
    first | exact Complex.conj_im _ | simp
  rw [hstar] at h2
  linarith

/-- A Hermitian complex matrix fails to be positive semidefinite exactly when
some vector has negative expectation. -/
theorem not_posSemidef_iff_exists_expectation_re_neg {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    ¬ M.PosSemidef ↔ ∃ φ : ι → ℂ, (expectation M φ).re < 0 := by
  constructor
  · intro h
    by_contra hcon
    have hall : ∀ φ : ι → ℂ, 0 ≤ star φ ⬝ᵥ (M *ᵥ φ) := by
      intro φ
      have him := expectation_im_eq_zero_of_isHermitian M hM φ
      have hre : 0 ≤ (expectation M φ).re := by
        by_contra hneg
        exact hcon ⟨φ, not_le.mp hneg⟩
      have hnn : 0 ≤ expectation M φ := Complex.nonneg_iff.mpr ⟨hre, by simp [him]⟩
      rw [expectation_eq_dotProduct] at hnn
      exact hnn
    exact h (Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hM, hall⟩)
  · rintro ⟨φ, hφ⟩ h
    have h1 : 0 ≤ star φ ⬝ᵥ (M *ᵥ φ) := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2 φ
    rw [← expectation_eq_dotProduct] at h1
    exact absurd hφ (not_lt.mpr (Complex.nonneg_iff.mp h1).1)

/-- The partial-transpose expectation as a sum over the entries of `ρ`. -/
theorem expectation_partialTranspose_eq_sum [Fintype m] [Fintype n]
    (ρ : Matrix (m × n) (m × n) ℂ) (ψ : m × n → ℂ) :
    expectation (partialTranspose ρ) ψ =
      ∑ p : m × n, ∑ q : m × n, star (ψ (p.1, q.2)) * ρ p q * ψ (q.1, p.2) := by
  unfold expectation partialTranspose
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact sum_comm_13 (fun b c d => star (ψ (a, b)) * ρ (a, d) (c, b) * ψ (c, d))

/-- Pull-back identity: the partial-transpose expectation of the filtered
operator in `φ` is the partial-transpose expectation of `ρ` in the vector
`(A ⊗ B)^† φ` (with the conjugation convention of `partialTranspose`). -/
theorem expectation_partialTranspose_localFilter [Fintype m] [Fintype n]
    (A : Matrix (Fin 2) m ℂ) (B : Matrix (Fin 2) n ℂ)
    (ρ : Matrix (m × n) (m × n) ℂ) (φ : Fin 2 × Fin 2 → ℂ) :
    expectation (partialTranspose (localFilter A B ρ)) φ =
      expectation (partialTranspose ρ)
        (fun p => ∑ y : Fin 2 × Fin 2, star (A y.1 p.1) * B y.2 p.2 * φ y) := by
  rw [expectation_partialTranspose_eq_sum ρ]
  have h1 : expectation (partialTranspose (localFilter A B ρ)) φ =
      ∑ x : Fin 2 × Fin 2, ∑ y : Fin 2 × Fin 2, ∑ p : m × n, ∑ q : m × n,
        star (φ x) *
          (A x.1 p.1 * B y.2 p.2 * ρ p q * star (A y.1 q.1) * star (B x.2 q.2)) * φ y := by
    unfold expectation partialTranspose localFilter
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [h1, sum_comm_22]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [star_sum_mul_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [star_mul', star_star]
  ring

theorem partialTranspose_isHermitian (M : Matrix (m × n) (m × n) ℂ) (hM : M.IsHermitian) :
    (partialTranspose M).IsHermitian :=
  Matrix.IsHermitian.ext fun x y => hM.apply (x.1, y.2) (y.1, x.2)

theorem localFilter_isHermitian [Fintype m] [Fintype n] (A : Matrix (Fin 2) m ℂ)
    (B : Matrix (Fin 2) n ℂ) (ρ : Matrix (m × n) (m × n) ℂ) (hρ : ρ.IsHermitian) :
    (localFilter A B ρ).IsHermitian := by
  refine Matrix.IsHermitian.ext fun x y => ?_
  unfold localFilter
  rw [star_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [star_mul', star_star, hρ.apply]
  ring

theorem tripleCopy_isHermitian (ρ : Matrix (m × n) (m × n) ℂ) (hρ : ρ.IsHermitian) :
    (tripleCopy ρ).IsHermitian := by
  refine Matrix.IsHermitian.ext fun x y => ?_
  unfold tripleCopy
  rw [star_mul', star_mul', hρ.apply, hρ.apply, hρ.apply]

/-- Horodecki / DiVincenzo et al. criterion in elementary form: a local
rank-two filter producing an NPT two-qubit operator exists iff some vector of
Schmidt rank at most two has negative expectation in `ρ^Γ`. -/
theorem exists_filter_isNPT_iff [Fintype m] [Fintype n] (ρ : Matrix (m × n) (m × n) ℂ)
    (hρ : ρ.IsHermitian) :
    (∃ (A : Matrix (Fin 2) m ℂ) (B : Matrix (Fin 2) n ℂ), IsNPT (localFilter A B ρ)) ↔
      ∃ ψ : m × n → ℂ, SchmidtRankLE 2 ψ ∧ (expectation (partialTranspose ρ) ψ).re < 0 := by
  constructor
  · rintro ⟨A, B, hNPT⟩
    have hH : (partialTranspose (localFilter A B ρ)).IsHermitian :=
      partialTranspose_isHermitian _ (localFilter_isHermitian A B ρ hρ)
    unfold IsNPT at hNPT
    obtain ⟨φ, hφ⟩ := (not_posSemidef_iff_exists_expectation_re_neg _ hH).mp hNPT
    rw [expectation_partialTranspose_localFilter] at hφ
    refine ⟨fun p => ∑ y : Fin 2 × Fin 2, star (A y.1 p.1) * B y.2 p.2 * φ y, ?_, hφ⟩
    unfold SchmidtRankLE
    refine ⟨fun k a => star (A k a), fun k b => ∑ y2 : Fin 2, B y2 b * φ (k, y2),
      fun a b => ?_⟩
    show (∑ y : Fin 2 × Fin 2, star (A y.1 a) * B y.2 b * φ y) =
      ∑ k : Fin 2, star (A k a) * ∑ y2 : Fin 2, B y2 b * φ (k, y2)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y2 _ => mul_assoc _ _ _
  · rintro ⟨ψ, hSR, hneg⟩
    unfold SchmidtRankLE at hSR
    obtain ⟨u, v, hψ⟩ := hSR
    obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin 2) m ℂ, ∀ k a, A k a = star (u k a) :=
      ⟨Matrix.of fun k a => star (u k a), fun k a => rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin 2) n ℂ, ∀ k b, B k b = v k b :=
      ⟨Matrix.of fun k b => v k b, fun k b => rfl⟩
    obtain ⟨φ, hφ⟩ : ∃ φ : Fin 2 × Fin 2 → ℂ, ∀ y, φ y = if y.1 = y.2 then 1 else 0 :=
      ⟨fun y => if y.1 = y.2 then 1 else 0, fun y => rfl⟩
    have hfun : (fun p : m × n =>
        ∑ y : Fin 2 × Fin 2, star (A y.1 p.1) * B y.2 p.2 * φ y) = ψ := by
      funext p
      obtain ⟨a, b⟩ := p
      rw [hψ a b]
      simp only [hA, hB, hφ, star_star]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single k (fun y2 _ hne => by simp [Ne.symm hne])
        (fun h => absurd (Finset.mem_univ k) h)]
      simp
    refine ⟨A, B, ?_⟩
    unfold IsNPT
    refine (not_posSemidef_iff_exists_expectation_re_neg _
      (partialTranspose_isHermitian _ (localFilter_isHermitian A B ρ hρ))).mpr ⟨φ, ?_⟩
    rw [expectation_partialTranspose_localFilter, hfun]
    exact hneg

/-- For Hermitian `ρ` the operational one-copy definition agrees with the
Schmidt-rank-two form used in `Basic`. -/
theorem isOneCopyFilterDistillable_iff [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ρ : Matrix (m × n) (m × n) ℂ) (hρ : ρ.IsHermitian) :
    IsOneCopyFilterDistillable ρ ↔ IsOneCopyRankTwoDetectable ρ := by
  unfold IsOneCopyFilterDistillable IsOneCopyRankTwoDetectable
  exact exists_filter_isNPT_iff ρ hρ

/-- For Hermitian `ρ` the operational three-copy definition agrees with the
Schmidt-rank-two form used in `Basic`. -/
theorem isThreeCopyFilterDistillable_iff [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (ρ : Matrix (m × n) (m × n) ℂ) (hρ : ρ.IsHermitian) :
    IsThreeCopyFilterDistillable ρ ↔ IsThreeCopyRankTwoDetectable ρ := by
  unfold IsThreeCopyFilterDistillable IsThreeCopyRankTwoDetectable
  exact exists_filter_isNPT_iff (tripleCopy ρ) (tripleCopy_isHermitian ρ hρ)

/-- A Hermitian operator is NPT iff some vector has negative expectation in
its partial transpose. -/
theorem isNPT_iff_exists_expectation_re_neg [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (ρ : Matrix (m × n) (m × n) ℂ) (hρ : ρ.IsHermitian) :
    IsNPT ρ ↔ ∃ ψ : m × n → ℂ, (expectation (partialTranspose ρ) ψ).re < 0 := by
  unfold IsNPT
  exact not_posSemidef_iff_exists_expectation_re_neg _ (partialTranspose_isHermitian ρ hρ)

end ThreeCopyQutritWerner
