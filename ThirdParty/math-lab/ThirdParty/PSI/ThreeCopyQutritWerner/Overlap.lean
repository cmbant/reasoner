module

public import ThreeCopyQutritWerner.WernerState

@[expose] public section


/-!
# Singlet-fraction bound for separable protocols on three copies

Manuscript Corollary 2.2, overlap bound: every trace-preserving separable operation from three
copies to two qubits, for example a deterministic two-way LOCC map, has overlap at most `1/2`
with a maximally entangled two-qubit state.

Model (explicit, a modelling choice): a protocol is a finite family of product Kraus pairs
`A k : Matrix (Fin 2) (m × m × m) ℂ`, `B k : Matrix (Fin 2) (n × n × n) ℂ` (a separable
operation); its output on `ρ^{⊗3}` is `Σ_k (A_k ⊗ B_k) ρ^{⊗3} (A_k ⊗ B_k)†` (`sepOutput`).
Every LOCC protocol with finitely many outcomes has this form; that inclusion is not
formalized here.  The bound is proved for all separable operations, with the output trace
in place of `1`; trace preservation gives output trace one (`trace_sepOutput`).

No separability theorem for two-qubit PPT states is used: the output has positive partial
transpose, and the singlet test vector bounds the overlap.
-/

noncomputable section

open scoped ComplexOrder

namespace ThreeCopyQutritWerner

/-- `|01⟩ - |10⟩` (unnormalized singlet). -/
def singletVec : Fin 2 × Fin 2 → ℂ := fun x =>
  if x.1 = 0 ∧ x.2 = 1 then 1 else if x.1 = 1 ∧ x.2 = 0 then -1 else 0

/-- Two-qubit identity: `⟨s, σ^Γ s⟩ = Tr σ - ⟨|00⟩+|11⟩, σ (|00⟩+|11⟩)⟩` for the singlet `s`. -/
theorem expectation_partialTranspose_singletVec (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    expectation (partialTranspose σ) singletVec = σ.trace - expectation σ omegaVec₂ := by
  simp only [expectation, partialTranspose, singletVec, omegaVec₂, Matrix.trace,
    Matrix.diag_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  norm_num
  ring

section Sums

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem expectation_sum (M : κ → Matrix ι ι ℂ) (φ : ι → ℂ) :
    expectation (∑ k, M k) φ = ∑ k, expectation (M k) φ := by
  unfold expectation
  calc ∑ x, ∑ y, star (φ x) * (∑ k, M k) x y * φ y
      = ∑ x, ∑ y, ∑ k, star (φ x) * M k x y * φ y := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
    _ = ∑ k, ∑ y, ∑ x, star (φ x) * M k x y * φ y := sum_comm_13 _
    _ = ∑ k, ∑ x, ∑ y, star (φ x) * M k x y * φ y :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm

theorem partialTranspose_sum {m n : Type*} (M : κ → Matrix (m × n) (m × n) ℂ) :
    partialTranspose (∑ k, M k) = ∑ k, partialTranspose (M k) := by
  ext x y
  simp only [partialTranspose, Matrix.sum_apply]

end Sums

/-- The vector pulled back from a two-qubit vector through local filters has Schmidt rank at
most two. -/
theorem schmidtRankLE_filterPullback {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix (Fin 2) m ℂ) (B : Matrix (Fin 2) n ℂ) (φ : Fin 2 × Fin 2 → ℂ) :
    SchmidtRankLE 2 (fun p : m × n => ∑ y : Fin 2 × Fin 2, star (A y.1 p.1) * B y.2 p.2 * φ y) := by
  unfold SchmidtRankLE
  refine ⟨fun k a => star (A k a), fun k b => ∑ y2 : Fin 2, B y2 b * φ (k, y2), fun a b => ?_⟩
  show (∑ y : Fin 2 × Fin 2, star (A y.1 a) * B y.2 b * φ y) =
    ∑ k : Fin 2, star (A k a) * ∑ y2 : Fin 2, B y2 b * φ (k, y2)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y2 _ => mul_assoc _ _ _

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- If no Schmidt-rank-two vector detects three copies of `ρ`, the output of every separable
operation has a positive semidefinite partial transpose (as a quadratic form). -/
theorem re_expectation_partialTranspose_sepOutput_nonneg {K : ℕ}
    (A : Fin K → Matrix (Fin 2) (m × m × m) ℂ) (B : Fin K → Matrix (Fin 2) (n × n × n) ℂ)
    (ρ : Matrix (m × n) (m × n) ℂ) (hnd : ¬ IsThreeCopyRankTwoDetectable ρ)
    (φ : Fin 2 × Fin 2 → ℂ) :
    0 ≤ (expectation (partialTranspose (sepOutput A B ρ)) φ).re := by
  unfold sepOutput
  rw [partialTranspose_sum, expectation_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun k _ => ?_
  rw [expectation_partialTranspose_localFilter]
  by_contra hneg
  exact hnd ⟨_, schmidtRankLE_filterPullback (A k) (B k) φ, lt_of_not_ge hneg⟩

/-- Corollary 2.2, for separable operations: if no Schmidt-rank-two vector
detects three copies of `ρ`, every separable operation on three copies has overlap with the
maximally entangled two-qubit state at most half of its output trace. -/
theorem maxEntOverlap_sepOutput_le {K : ℕ} (A : Fin K → Matrix (Fin 2) (m × m × m) ℂ)
    (B : Fin K → Matrix (Fin 2) (n × n × n) ℂ) (ρ : Matrix (m × n) (m × n) ℂ)
    (hnd : ¬ IsThreeCopyRankTwoDetectable ρ) :
    maxEntOverlap (sepOutput A B ρ) ≤ (sepOutput A B ρ).trace.re / 2 := by
  have h := re_expectation_partialTranspose_sepOutput_nonneg A B ρ hnd singletVec
  rw [expectation_partialTranspose_singletVec, Complex.sub_re] at h
  unfold maxEntOverlap
  linarith

section TracePreserving

/-- Regroup `(A₁A₂A₃, B₁B₂B₃)` as `(A₁B₁, A₂B₂, A₃B₃)`. -/
def copyEquiv (m n : Type*) : (m × m × m) × (n × n × n) ≃ (m × n) × (m × n) × (m × n) where
  toFun x := ((x.1.1, x.2.1), (x.1.2.1, x.2.2.1), (x.1.2.2, x.2.2.2))
  invFun y := ((y.1.1, y.2.1.1, y.2.2.1), (y.1.2, y.2.1.2, y.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Trace of a locally filtered operator, in terms of `A†A` and `B†B`. -/
theorem trace_localFilter {p q : Type*} [Fintype p] [Fintype q] (A : Matrix (Fin 2) p ℂ)
    (B : Matrix (Fin 2) q ℂ) (M : Matrix (p × q) (p × q) ℂ) :
    (localFilter A B M).trace =
      ∑ u : p × q, ∑ v : p × q, M u v *
        ((∑ i : Fin 2, star (A i v.1) * A i u.1) * (∑ j : Fin 2, star (B j v.2) * B j u.2)) := by
  calc (localFilter A B M).trace
      = ∑ i : Fin 2, ∑ j : Fin 2, ∑ u : p × q, ∑ v : p × q,
          A i u.1 * B j u.2 * M u v * star (A i v.1) * star (B j v.2) := by
        simp only [Matrix.trace, Matrix.diag_apply, localFilter]
        exact Fintype.sum_prod_type _
    _ = ∑ u : p × q, ∑ v : p × q, ∑ i : Fin 2, ∑ j : Fin 2,
          A i u.1 * B j u.2 * M u v * star (A i v.1) * star (B j v.2) := sum_comm_22 _
    _ = _ := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

end TracePreserving

/-- Trace preservation (`Σ_k (A_k ⊗ B_k)† (A_k ⊗ B_k) = I`, entrywise) gives
`Tr (output) = Tr ρ^{⊗3}`. -/
theorem trace_sepOutput {K : ℕ} (A : Fin K → Matrix (Fin 2) (m × m × m) ℂ)
    (B : Fin K → Matrix (Fin 2) (n × n × n) ℂ) (ρ : Matrix (m × n) (m × n) ℂ)
    (htp : ∀ u v : (m × m × m) × (n × n × n),
      ∑ k, (∑ i : Fin 2, star (A k i v.1) * A k i u.1) *
        (∑ j : Fin 2, star (B k j v.2) * B k j u.2) = if u = v then 1 else 0) :
    (sepOutput A B ρ).trace = (tripleCopy ρ).trace := by
  unfold sepOutput
  rw [Matrix.trace_sum]
  simp only [trace_localFilter]
  rw [Finset.sum_comm]
  have h : ∀ u : (m × m × m) × (n × n × n),
      ∑ k : Fin K, ∑ v : (m × m × m) × (n × n × n), tripleCopy ρ u v *
        ((∑ i : Fin 2, star (A k i v.1) * A k i u.1) * (∑ j : Fin 2, star (B k j v.2) * B k j u.2))
        = tripleCopy ρ u u := by
    intro u
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, htp]
    rw [Finset.sum_eq_single u]
    · simp
    · intro v _ hv
      simp [Ne.symm hv]
    · intro hu
      exact absurd (Finset.mem_univ u) hu
  calc ∑ u : (m × m × m) × (n × n × n), ∑ k : Fin K, ∑ v : (m × m × m) × (n × n × n),
        tripleCopy ρ u v * ((∑ i : Fin 2, star (A k i v.1) * A k i u.1) *
          (∑ j : Fin 2, star (B k j v.2) * B k j u.2))
      = ∑ u : (m × m × m) × (n × n × n), tripleCopy ρ u u := Finset.sum_congr rfl fun u _ => h u
    _ = (tripleCopy ρ).trace := rfl

theorem trace_tripleCopy (ρ : Matrix (m × n) (m × n) ℂ) :
    (tripleCopy ρ).trace = ρ.trace ^ 3 := by
  have h : (tripleCopy ρ).trace =
      ∑ y : (m × n) × (m × n) × (m × n), ρ y.1 y.1 * ρ y.2.1 y.2.1 * ρ y.2.2 y.2.2 :=
    Fintype.sum_equiv (copyEquiv m n) _ _ (fun _ => rfl)
  rw [h]
  calc ∑ y : (m × n) × (m × n) × (m × n), ρ y.1 y.1 * ρ y.2.1 y.2.1 * ρ y.2.2 y.2.2
      = ∑ p₁ : m × n, ∑ p₂ : m × n, ∑ p₃ : m × n, ρ p₁ p₁ * ρ p₂ p₂ * ρ p₃ p₃ := by
        simp only [Fintype.sum_prod_type]
    _ = ρ.trace ^ 3 := by
        rw [pow_three]
        simp only [Matrix.trace, Matrix.diag_apply]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p₁ _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p₂ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p₃ _ => ?_
        ring

/-- Corollary 2.2, at `d = 3` for `α ≤ 0` (unconditional): a trace-preserving
separable operation on three copies of `ρ_{3,α}` has overlap at most `1/2` with the maximally
entangled two-qubit state. -/
theorem werner_three_maxEntOverlap_le_of_nonpos {α : ℝ} (h0 : α ≤ 0) {K : ℕ}
    (A : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (B : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (htp : ∀ u v : (Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3),
      ∑ k, (∑ i : Fin 2, star (A k i v.1) * A k i u.1) *
        (∑ j : Fin 2, star (B k j v.2) * B k j u.2) = if u = v then 1 else 0) :
    maxEntOverlap (sepOutput A B (werner 3 α)) ≤ 1 / 2 := by
  have h := maxEntOverlap_sepOutput_le A B (werner 3 α)
    (not_isThreeCopyRankTwoDetectable_werner_three_of_nonpos h0)
  rw [trace_sepOutput A B _ htp, trace_tripleCopy,
    trace_werner 3 α (by norm_num) (by intro h; norm_num at h; linarith)] at h
  simpa using h

/-- Corollary 2.2, at `d = 3`, CONDITIONAL on the qutrit endpoint inequality
`hq` (open claim T2.1a): for `0 ≤ α ≤ 1/2`, a trace-preserving separable operation on three
copies of `ρ_{3,α}` has overlap at most `1/2` with the maximally entangled two-qubit state. -/
theorem werner_three_maxEntOverlap_le_of_endpoint {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2)
    (hq : ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 → 0 ≤ endpointEnergy C) {K : ℕ}
    (A : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (B : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (htp : ∀ u v : (Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3),
      ∑ k, (∑ i : Fin 2, star (A k i v.1) * A k i u.1) *
        (∑ j : Fin 2, star (B k j v.2) * B k j u.2) = if u = v then 1 else 0) :
    maxEntOverlap (sepOutput A B (werner 3 α)) ≤ 1 / 2 := by
  have h := maxEntOverlap_sepOutput_le A B (werner 3 α)
    (not_isThreeCopyRankTwoDetectable_werner_three_of_endpoint h0 h1 hq)
  rw [trace_sepOutput A B _ htp, trace_tripleCopy,
    trace_werner 3 α (by norm_num) (by intro h; norm_num at h; linarith)] at h
  simpa using h

end ThreeCopyQutritWerner

end
