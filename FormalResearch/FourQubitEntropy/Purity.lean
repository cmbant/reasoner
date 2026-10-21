import FormalResearch.FourQubitEntropy.MomentInequality

/-!
# The purity identity

`P = n² + ½ (W₁ + τ)` with `τ = |ψᵀ σ_y^{⊗4} ψ|²`; in particular `P ≥ n²`, so `P ≥ 1` for unit
states. Here `σ_y^{⊗4} = ε^{⊗4}` since `σ_y = -i ε`, and `ψᵀ ε^{⊗4} ψ` is written with integer
coefficients so that the identity is a polynomial identity.
-/

open scoped ComplexConjugate
open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

section Generic

variable {α : Type} [RingOps α]

/-- `ψᵀ ε^{⊗4} ψ`. -/
def spinFlipForm (z : State α) : α :=
  sum4 fun a b c d =>
    lit (sgn a * sgn b * sgn c * sgn d) * (z a b c d * z (1 - a) (1 - b) (1 - c) (1 - d))

/-- `2P - 2n² - W₁ - τ`, which is identically zero. -/
def purityDefect (z w : State α) : α :=
  let n := normG z w
  lit 2 * (tr2 (marg12 z w) + tr2 (marg13 z w) + tr2 (marg14 z w)) - lit 2 * (n * n)
    - W1gen z w - spinFlipForm z * spinFlipForm w

end Generic

theorem purityDefect_check : purityDefect zSP wSP = [] := by
  native_decide

section Transfer

variable {α β : Type} [RingOps α] [RingOps β] {f : α → β}

theorem OpsHom.spinFlipForm (hf : OpsHom f) (z : State α) :
    f (spinFlipForm z) = spinFlipForm (z.map f) := by
  simp [FormalResearch.FourQubitEntropy.spinFlipForm, hf.sum4, hf.mul', hf.lit', State.map]

theorem OpsHom.purityDefect (hf : OpsHom f) (z w : State α) :
    f (purityDefect z w) = purityDefect (z.map f) (w.map f) := by
  simp only [FormalResearch.FourQubitEntropy.purityDefect, hf.add', hf.sub', hf.mul', hf.lit',
    hf.normG, hf.W1gen, hf.tr2, hf.marg12, hf.marg13, hf.marg14, hf.spinFlipForm]

end Transfer

theorem purityDefect_zero (z w : State ℂ) : purityDefect z w = 0 := by
  have h := (opsHom_evSP (varValues z w)).purityDefect zSP wSP
  rw [map_zSP, map_wSP, purityDefect_check] at h
  exact h.symm

theorem spinFlipForm_conj (ψ : Psi) :
    spinFlipForm ψ.conj = (starRingEnd ℂ) (spinFlipForm ψ) := by
  have h := opsHom_conj.spinFlipForm ψ
  rw [h]
  rfl

/-- The identity `2P = 2n² + W₁ + τ`, with `τ ≥ 0`. -/
theorem purity_identity (ψ : Psi) :
    ∃ τ : ℝ, 0 ≤ τ ∧ 2 * purity ψ = 2 * normSqPsi ψ ^ 2 + blochSq ψ + τ := by
  have hd := purityDefect_zero ψ ψ.conj
  obtain ⟨τ, hτ, e⟩ : NonnegReal (spinFlipForm ψ * spinFlipForm ψ.conj) := by
    rw [spinFlipForm_conj]; exact NonnegReal.mul_conj _
  refine ⟨τ, hτ, ?_⟩
  simp only [purityDefect, toAdd_complex, toMul_complex, toSub_complex, lit_complex] at hd
  rw [W1gen_eq, normG_eq, e, tr2_marg12, tr2_marg13, tr2_marg14,
    trace_sq_real (red12_herm ψ), trace_sq_real (red13_herm ψ), trace_sq_real (red14_herm ψ)] at hd
  have hc : (((2 * purity ψ - 2 * normSqPsi ψ ^ 2 - blochSq ψ - τ : ℝ)) : ℂ) = 0 := by
    unfold purity
    push_cast at hd ⊢
    linear_combination hd
  have : (2 * purity ψ - 2 * normSqPsi ψ ^ 2 - blochSq ψ - τ : ℝ) = 0 := by exact_mod_cast hc
  linarith

/-- `P ≥ n²`. -/
theorem purity_ge (ψ : Psi) : normSqPsi ψ ^ 2 ≤ purity ψ := by
  obtain ⟨τ, hτ, h⟩ := purity_identity ψ
  have := blochSq_nonneg ψ
  linarith

end FormalResearch.FourQubitEntropy
