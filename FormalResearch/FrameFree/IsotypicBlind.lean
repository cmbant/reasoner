import Mathlib
import FormalResearch.FrameFree.Foundations
import FormalResearch.FrameFree.TwirlsTwirl

/-!
# Isotypic blindness (Paper P `thm:isotypicblind`, recalled from QI-A `thm:isotypicblind`)

Namespace `FormalResearch.FrameFree.IsotypicBlind`.  Claim class: **proved** (no hypothesis, no new axiom).

The `n` spins of one copy of `ψ` are the first coordinate and the `k` copies the second coordinate of the
slots `ι = Fin n × Fin k`; `copyState ψ k = ψ^{⊗k}`.  `ε^{⊗ι}` is `epsOp ι` (`TwirlsTwirl`).

**Core (`expect_flip`).**  For *every* operator `E` on `ι` qubits commuting with the spin flip `ε^{⊗ι}`,
`⟨(Θψ)^{⊗k}|E|(Θψ)^{⊗k}⟩ = ⟨ψ^{⊗k}|Eᵀ|ψ^{⊗k}⟩` (`expect_copyState_theta`).  Hence the two expectations agree
for symmetric `E` (`expect_copyState_theta_of_symm`), are complex conjugate for real `E`
(`expect_copyState_theta_of_real`: in particular for every real combination of copy permutations,
`expect_copyState_theta_of_mem_permSpan`) and agree for real Hermitian `E`.

**Labels.**  The local label of spin `a` is the total spin `j` of its `k` copies, i.e. the eigenvalue
`j(j+1)` of the Casimir `J² = (3k/4 - k(k-1)/4) 1 + ∑_{c<d} P_{(c d)}` of `(ℂ²)^{⊗k}` (Dirac identity; here
`casimirJ2` is *defined* by this real combination of transpositions).  The label projector is the
Lagrange (spectral) polynomial `specProj k S t = ∏_{s ∈ S∖{t}} (J² - s)/(t - s)` for a finite set `S` of
eigenvalues (any `S` containing the spectrum of `J²`, which is `{j(j+1)}`, gives the spectral projector);
the joint label projector is `Π_λ = ⊗_a P_{λ_a}^{(a)}` (`spinTensor`).  Joint label distribution
`labelProb k m ψ = ⟨ψ^{⊗k}|Π_m|ψ^{⊗k}⟩`.

**`isotypic_blind`.**  For all `n, k`, every `ψ` (unit or not), every label tuple `m`:
`labelProb k m (Θψ) = labelProb k m ψ`; so the label distributions of `k` copies of `ψ` and `Θψ` coincide
(`labelDist`, `sum_labelProb_eq` for events, `labelProb_theta_eq_of_family` for any family of
symmetric `ε`-commuting local projectors).  Not formalized: that `Σ_m Π_m = 1` and that the nodes
`spinSpec k` exhaust the spectrum of `casimirJ2 k` (so that `specProj` is literally the orthogonal
projector onto total spin `j`), and the Dirac identity `J² = Σ J_i²`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
open FormalResearch.FrameFree.Twirls
open FormalResearch.FrameFree.NQubit (Ψ Θ eps)

namespace FormalResearch.FrameFree.IsotypicBlind

/-! ### Expectation values and the flip -/

section Expect

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `⟨v|E v⟩` for a vector `v` on the slots `ι`. -/
noncomputable def expect (E : OpS ι) (v : (ι → Fin 2) → ℂ) : ℂ := star v ⬝ᵥ (E *ᵥ v)

theorem expect_mulVec (F E : OpS ι) (w : (ι → Fin 2) → ℂ) :
    expect E (F *ᵥ w) = expect (Fᴴ * E * F) w := by
  unfold expect
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- `⟨v̄|E v̄⟩ = ⟨v|Eᵀ v⟩`. -/
theorem expect_star (E : OpS ι) (v : (ι → Fin 2) → ℂ) : expect E (star v) = expect Eᵀ v := by
  unfold expect
  rw [star_star, Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.mulVec_transpose]

/-- `epsOp` is real. -/
theorem epsOp_map_conj : (epsOp ι).map conj = epsOp ι := by
  ext x y
  simp only [epsOp, tensOp, Matrix.of_apply, Matrix.map_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have := congrFun (congrFun NQubit.eps_conj_map (x i)) (y i)
  simpa using this

/-- **Core.**  An operator commuting with the spin flip `ε^{⊗ι}` has, in the flipped state `ε^{⊗ι} v̄`, the
expectation `⟨v|Eᵀ v⟩`. -/
theorem expect_flip (E : OpS ι) (hE : E * epsOp ι = epsOp ι * E) (v : (ι → Fin 2) → ℂ) :
    expect E (epsOp ι *ᵥ star v) = expect Eᵀ v := by
  rw [expect_mulVec, Matrix.mul_assoc, hE, ← Matrix.mul_assoc, epsOp_unitary, Matrix.one_mul,
    expect_star]

theorem conj_expect (E : OpS ι) (v : (ι → Fin 2) → ℂ) : conj (expect E v) = expect Eᴴ v := by
  unfold expect
  change star (star v ⬝ᵥ (E *ᵥ v)) = _
  rw [← star_dotProduct, Matrix.star_mulVec, Matrix.dotProduct_mulVec]

/-- Symmetric operators commuting with the flip have equal expectation in `v` and in `ε^{⊗ι} v̄`. -/
theorem expect_flip_of_symm {E : OpS ι} (hs : Eᵀ = E) (hE : E * epsOp ι = epsOp ι * E)
    (v : (ι → Fin 2) → ℂ) : expect E (epsOp ι *ᵥ star v) = expect E v := by
  rw [expect_flip E hE, hs]

/-- Real operators commuting with the flip: the expectation in `ε^{⊗ι} v̄` is the conjugate. -/
theorem expect_flip_of_real {E : OpS ι} (hr : E.map conj = E) (hE : E * epsOp ι = epsOp ι * E)
    (v : (ι → Fin 2) → ℂ) : expect E (epsOp ι *ᵥ star v) = conj (expect E v) := by
  have : Eᵀ = Eᴴ := by
    ext x y
    have := congrFun (congrFun hr y) x
    simpa [Matrix.conjTranspose_apply] using this.symm
  rw [expect_flip E hE, conj_expect, this]

end Expect

/-! ### Real combinations of permutations -/

section PermSpan

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real span of all slot permutation operators (so a fortiori of the block-preserving ones). -/
noncomputable def permSpan (ι : Type*) [Fintype ι] [DecidableEq ι] : Submodule ℝ (OpS ι) :=
  Submodule.span ℝ (Set.range (permOp (ι := ι)))

theorem permSpan_real {E : OpS ι} (hE : E ∈ permSpan ι) : E.map conj = E := by
  induction hE using Submodule.span_induction with
  | mem x hx => obtain ⟨σ, rfl⟩ := hx; exact permOp_map_conj σ
  | zero => ext x y; simp
  | add x y _ _ hx hy =>
    ext a b
    have h1 := congrFun (congrFun hx a) b
    have h2 := congrFun (congrFun hy a) b
    simp only [Matrix.map_apply, Matrix.add_apply, map_add] at h1 h2 ⊢
    rw [h1, h2]
  | smul r x _ hx =>
    ext a b
    have h1 := congrFun (congrFun hx a) b
    simp only [Matrix.map_apply] at h1
    simp only [Matrix.map_apply, Matrix.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, h1]

theorem permSpan_comm {E : OpS ι} (hE : E ∈ permSpan ι) : E * epsOp ι = epsOp ι * E := by
  induction hE using Submodule.span_induction with
  | mem x hx => obtain ⟨σ, rfl⟩ := hx; exact (epsOp_commute_permOp σ).symm
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.mul_add, hx, hy]
  | smul r x _ hx => rw [Matrix.smul_mul, Matrix.mul_smul, hx]

/-- Every real combination of slot permutations has conjugate expectations in `v` and `ε^{⊗ι} v̄`. -/
theorem expect_flip_of_mem_permSpan {E : OpS ι} (hE : E ∈ permSpan ι) (v : (ι → Fin 2) → ℂ) :
    expect E (epsOp ι *ᵥ star v) = conj (expect E v) :=
  expect_flip_of_real (permSpan_real hE) (permSpan_comm hE) v

end PermSpan

/-! ### `k` copies of an `n`-qubit vector and time reversal -/

section Copies

variable {n k : ℕ}

/-- `ψ^{⊗k}` on the slots `Fin n × Fin k` (slot `(a, c)`: spin `a` of copy `c`). -/
noncomputable def copyState (k : ℕ) (ψ : Ψ n) : (Fin n × Fin k → Fin 2) → ℂ :=
  fun x => ∏ c, ψ (fun a => x (a, c))

/-- `(Θψ)^{⊗k} = ε^{⊗nk} conj (ψ^{⊗k})`. -/
theorem copyState_theta (ψ : Ψ n) :
    copyState k (Θ ψ) = epsOp (Fin n × Fin k) *ᵥ star (copyState k ψ) := by
  funext x
  have h := sum_copies (α := Fin n) (γ := Fin k)
    (fun c b => (∏ i, eps (x (i, c)) (b i)) * conj (ψ b))
  simp only [copyState, NQubit.Θ]
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, epsOp, tensOp, Matrix.of_apply, Pi.star_apply, copyState]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib, Fintype.prod_prod_type_right]
  congr 1
  exact (map_prod (starRingEnd ℂ) _ _).symm

/-- **Core, copy form.**  Any `E` commuting with `ε^{⊗nk}` has expectation `⟨ψ^{⊗k}|Eᵀ|ψ^{⊗k}⟩` in
`(Θψ)^{⊗k}`. -/
theorem expect_copyState_theta (E : OpS (Fin n × Fin k)) (hE : E * epsOp _ = epsOp _ * E) (ψ : Ψ n) :
    expect E (copyState k (Θ ψ)) = expect Eᵀ (copyState k ψ) := by
  rw [copyState_theta, expect_flip E hE]

theorem expect_copyState_theta_of_symm {E : OpS (Fin n × Fin k)} (hs : Eᵀ = E)
    (hE : E * epsOp _ = epsOp _ * E) (ψ : Ψ n) :
    expect E (copyState k (Θ ψ)) = expect E (copyState k ψ) := by
  rw [copyState_theta, expect_flip_of_symm hs hE]

theorem expect_copyState_theta_of_real {E : OpS (Fin n × Fin k)} (hr : E.map conj = E)
    (hE : E * epsOp _ = epsOp _ * E) (ψ : Ψ n) :
    expect E (copyState k (Θ ψ)) = conj (expect E (copyState k ψ)) := by
  rw [copyState_theta, expect_flip_of_real hr hE]

theorem expect_copyState_theta_of_mem_permSpan {E : OpS (Fin n × Fin k)} (hE : E ∈ permSpan _)
    (ψ : Ψ n) :
    expect E (copyState k (Θ ψ)) = conj (expect E (copyState k ψ)) := by
  rw [copyState_theta, expect_flip_of_mem_permSpan hE]

end Copies

end FormalResearch.FrameFree.IsotypicBlind
