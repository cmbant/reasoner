module

public import FormalResearch.FourQubitEntropy.SevenQubitShadowComplementModel
public import FormalResearch.FourQubitEntropy.SevenQubitShadowComplementPauli

/-!
# Local shadow and complement asymmetry for odd `n` (`prop:shadow-complement`)

`QI/multiqubit_entanglement/seven_qubit_entanglement/shadow_equality_geometry.tex`, `prop:shadow-complement`.

The abstract spin-flip model (`IsSpinFlip`, `shadowQ_eq`, `shadowQ_eq_trace`, ...) is in
`SevenQubitShadowComplementModel.lean`; the concrete instance and the Pauli expansions of `ρ̄` are in
`SevenQubitShadowComplementPauli.lean`. This module assembles the proposition for an arbitrary (not
necessarily normalized) `n`-qubit vector `ψ : Ψ (m + 1)`, `n = m + 1` odd (`m` even), and a distinguished
qubit `s`; no hypothesis other than `Even m` is assumed.

* `ρ̄ = ∑_a |u_a⟩⟨u_a|` is the reduced state on the other `m` qubits, `u_a = branchVec ψ s a`
  (`ψ = |0⟩_s u₀ + |1⟩_s u₁`); `rdm_eq_sum` identifies it with the explicit partial trace `rdm`.
* `J = J_m = ε^{⊗m} K` is `spinFlipOp (univ.erase s)`; it is an antiunitary involution for `m` even
  (`isSpinFlip_spinFlipOp`).
* `B_j = weightEnumExcl ψ s j = ∑_{wt P = j} (tr ρ̄ P)²`, the Pauli weight coefficients of `ρ̄`, `P` ranging over the
  Hermitian Pauli strings on the other `m` qubits (`weightEnumExcl_eq_sum_trace_sq`).
* `q_s = shadowQ J z` with `z = branchVec ψ s`.

Headline results (proved, no hypotheses beyond `Even m`):

* `odd_weight_identities`: the two boxed identities `∑_{j odd} B_j = 2^{n-2} tr ρ_s² - 2^{n-3} q_s` and
  `‖ρ̄ - Jρ̄J⁻¹‖₂² = 2^{3-n} ∑_{j odd} B_j` (stated with `m = n - 1`, as `2^m/2 · tr ρ_s² - 2^m/4 · q_s`
  and `2^m · ‖·‖₂² = 4 ∑_odd B`), where `tr ρ_s² = cutPurity ψ {s}` and `‖A‖₂² = hsNormSq A = Re tr(A† A)`.
  Its inputs are the Pauli expansions `2^m tr ρ̄² = ∑_j B_j` (`two_pow_mul_cutPurity_erase`) and
  `2^m tr(ρ̄ J ρ̄ J⁻¹) = ∑_j (-1)^j B_j` (`two_pow_mul_sum_Tm`, via the library's `two_pow_mul_Rspin`), the identities
  `q_s = 2 tr(ρ̄ J ρ̄ J⁻¹)` (`shadowQ_eq_trace`), `tr ρ̄² = tr ρ_s²` (`cutPurity_erase`) and
  `‖ρ̄ - Jρ̄J⁻¹‖₂² = 2 tr ρ̄² - 2 tr(ρ̄ J ρ̄ J⁻¹)` (`hsNormSq_rho_sub_rhoFlip`), and the real arithmetic
  `odd_weight_arith`.
* `takagi_frobenius`, `shadowQ_takagi`, `odd_weight_takagi`: if the normalized overlap matrix `T̂ = 2T` has a
  Takagi factorization `T̂ = U diag(t) Uᵀ` (`U` unitary, `t` real), then `q_s = (t₁² + t₂²)/2`, and for
  `tr ρ_s² = 1/2` (`ρ_s = I/2`) `∑_{j odd} B_j = 2^{n-3}(1 - (t₁² + t₂²)/2)`.

Not covered: existence of the Takagi factorization and the basis independence of the `t_i`; the distinguished qubit
`s` is an arbitrary `Fin (m + 1)`, and `n = 1` (`m = 0`) is included.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.SevenQubitShadowComplement

open Finset Matrix
open scoped InnerProductSpace ComplexConjugate
open FormalResearch.NQubit.Reduced
open FormalResearch.NQubit (Ψ)

/-! ### The odd-weight identities: real arithmetic -/

/-- The arithmetic core of `prop:shadow-complement`, with `m = n - 1` (so `2^m/2 = 2^{n-2}`,
`2^m/4 = 2^{n-3}`, `2^{3-n} = 4/2^m`). Inputs: `P = tr ρ̄²`, `C = tr(ρ̄ J ρ̄ J⁻¹)`, `r = tr ρ_s²`, `q = q_s`,
`d = ‖ρ̄ - Jρ̄J⁻¹‖₂²`, and the Pauli expansions `2^m P = ∑_j B_j`, `2^m C = ∑_j (-1)^j B_j`. Every hypothesis is
discharged for the concrete model in `odd_weight_identities`. -/
theorem odd_weight_arith {m : ℕ} (B : ℕ → ℝ) (P C q r d : ℝ)
    (hP : (2 : ℝ) ^ m * P = ∑ j ∈ range (m + 1), B j)
    (hC : (2 : ℝ) ^ m * C = ∑ j ∈ range (m + 1), (-1) ^ j * B j)
    (hq : q = 2 * C) (hr : P = r) (hd : d = 2 * P - 2 * C) :
    ∑ j ∈ (range (m + 1)).filter Odd, B j = (2 : ℝ) ^ m / 2 * r - (2 : ℝ) ^ m / 4 * q ∧
    (2 : ℝ) ^ m * d = 4 * ∑ j ∈ (range (m + 1)).filter Odd, B j := by
  have key : ∑ j ∈ range (m + 1), B j - ∑ j ∈ range (m + 1), (-1) ^ j * B j =
      2 * ∑ j ∈ (range (m + 1)).filter Odd, B j := by
    rw [← Finset.sum_sub_distrib, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases Nat.even_or_odd j with he | ho
    · simp [he.neg_one_pow, Nat.not_odd_iff_even.2 he]
    · simp [ho.neg_one_pow, ho]; ring
  subst hr hq hd
  constructor
  · nlinarith [hP, hC, key]
  · nlinarith [hP, hC, key]

/-! ### The boxed identities of `prop:shadow-complement` -/

/-- **`prop:shadow-complement`, boxed identities (unconditional).** For every (not necessarily normalized)
`n`-qubit vector `ψ = |0⟩_s u₀ + |1⟩_s u₁`, `n = m + 1` odd, with `B_j = weightEnumExcl ψ s j` the Pauli weight
coefficients of `ρ̄`, `J = ε^{⊗m} K` (`spinFlipOp`), `q_s = ∑_α |⟨z, σ_α^{(s)} J_n z⟩|²` (`shadowQ`), and
`‖A‖₂² = Re tr(A† A)`:
`∑_{j odd} B_j = 2^m/2 · tr ρ_s² - 2^m/4 · q_s` and `2^m ‖ρ̄ - Jρ̄J⁻¹‖₂² = 4 ∑_{j odd} B_j`. -/
theorem odd_weight_identities {m : ℕ} (hm : Even m) (ψ : Ψ (m + 1)) (s : Fin (m + 1)) :
    ∑ j ∈ (range (m + 1)).filter Odd, weightEnumExcl ψ s j =
        (2 : ℝ) ^ m / 2 * cutPurity ψ {s}
          - (2 : ℝ) ^ m / 4 * shadowQ (spinFlipOp (univ.erase s)) (branchVec ψ s) ∧
    (2 : ℝ) ^ m * hsNormSq (rho (branchVec ψ s) - rhoFlip (spinFlipOp (univ.erase s)) (branchVec ψ s)) =
        4 * ∑ j ∈ (range (m + 1)).filter Odd, weightEnumExcl ψ s j := by
  have h : IsSpinFlip (spinFlipOp (univ.erase s)) :=
    isSpinFlip_spinFlipOp _ (by rw [card_erase_univ]; exact hm)
  refine odd_weight_arith (weightEnumExcl ψ s)
    (LinearMap.trace ℂ (CfgSpace (univ.erase s)) (rho (branchVec ψ s) ∘ₗ rho (branchVec ψ s))).re
    (LinearMap.trace ℂ (CfgSpace (univ.erase s))
      (rho (branchVec ψ s) ∘ₗ rhoFlip (spinFlipOp (univ.erase s)) (branchVec ψ s))).re
    _ (cutPurity ψ {s}) _ ?_ ?_ ?_ (trace_rho_rho_eq ψ s) (hsNormSq_rho_sub_rhoFlip h _)
  · rw [trace_rho_rho_eq, ← cutPurity_erase]
    exact two_pow_mul_cutPurity_erase ψ s
  · rw [trace_rho_rhoFlip_re]
    exact two_pow_mul_sum_Tm ψ s
  · rw [trace_rho_rhoFlip_re, shadowQ_eq h]

/-! ### Takagi data -/

section Takagi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sum_norm_sq_eq_trace (M : Matrix ι ι ℂ) :
    ∑ a, ∑ b, ‖M a b‖ ^ 2 = (Matrix.trace (Mᴴ * M)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]

/-- If `T̂ = U diag(t) Uᵀ` with `U` unitary and `t` real, then `∑ |T̂_{ab}|² = ∑ t_i²`. -/
theorem takagi_frobenius (U : Matrix ι ι ℂ) (hU : star U * U = 1) (t : ι → ℝ) :
    ∑ a, ∑ b, ‖(U * Matrix.diagonal (fun i => (t i : ℂ)) * Uᵀ) a b‖ ^ 2 = ∑ i, t i ^ 2 := by
  set D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (t i : ℂ)) with hD
  have hDH : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1
    ext i
    simp
  have h1 : (U * D * Uᵀ)ᴴ * (U * D * Uᵀ) = (Uᵀ)ᴴ * (D * (star U * U) * D) * Uᵀ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDH]
    simp only [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
  have h2 : Uᵀ * (Uᵀ)ᴴ = 1 := by
    have := congrArg Matrix.transpose hU
    rw [Matrix.transpose_mul, Matrix.transpose_one] at this
    have e : (star U)ᵀ = (Uᵀ)ᴴ := by
      ext i j
      simp [Matrix.transpose_apply, Matrix.conjTranspose_apply, Matrix.star_apply]
    rw [e] at this
    exact this
  rw [sum_norm_sq_eq_trace, h1, hU, Matrix.mul_one, hD, Matrix.diagonal_mul_diagonal]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.trace_diagonal]
  simp [← Complex.ofReal_mul, Complex.re_sum, sq]

end Takagi

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {J : E →ₛₗ[starRingEnd ℂ] E}

/-- Normalized Schmidt branches (`ρ_s = I/2`, `T̂ = 2T`) with a Takagi factorization
`T̂ = U diag(t) Uᵀ`: `q_s = (t₁² + t₂²)/2`. -/
theorem shadowQ_takagi (h : IsSpinFlip J) (z : Fin 2 → E) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : star U * U = 1) (t : Fin 2 → ℝ)
    (hT : ∀ a b, (U * Matrix.diagonal (fun i => (t i : ℂ)) * Uᵀ) a b = 2 * Tm J z a b) :
    shadowQ J z = (t 0 ^ 2 + t 1 ^ 2) / 2 := by
  have h1 := takagi_frobenius U hU t
  simp only [Fin.sum_univ_two, hT, norm_mul, Complex.norm_two, mul_pow] at h1
  rw [shadowQ_eq h]
  simp only [Fin.sum_univ_two]
  linarith

end Abstract

/-- **The Takagi form of the first boxed identity.** If `tr ρ_s² = 1/2` (`ρ_s = I/2`) and the normalized overlap
matrix `T̂ = 2T` of the branches has a Takagi factorization `T̂ = U diag(t) Uᵀ` (`U` unitary, `t` real), then
`∑_{j odd} B_j = 2^{n-3} (1 - (t₁² + t₂²)/2)` (here `2^{n-3} = 2^m/4`). -/
theorem odd_weight_takagi {m : ℕ} (hm : Even m) (ψ : Ψ (m + 1)) (s : Fin (m + 1))
    (hr : cutPurity ψ {s} = 1 / 2) (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : star U * U = 1)
    (t : Fin 2 → ℝ)
    (hT : ∀ a b, (U * Matrix.diagonal (fun i => (t i : ℂ)) * Uᵀ) a b =
      2 * Tm (spinFlipOp (univ.erase s)) (branchVec ψ s) a b) :
    ∑ j ∈ (range (m + 1)).filter Odd, weightEnumExcl ψ s j =
      (2 : ℝ) ^ m / 4 * (1 - (t 0 ^ 2 + t 1 ^ 2) / 2) := by
  have h : IsSpinFlip (spinFlipOp (univ.erase s)) :=
    isSpinFlip_spinFlipOp _ (by rw [card_erase_univ]; exact hm)
  have := (odd_weight_identities hm ψ s).1
  rw [this, hr, shadowQ_takagi h _ U hU t hT]
  ring

end FormalResearch.FourQubitEntropy.SevenQubitShadowComplement

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitShadowComplement.odd_weight_identities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.SevenQubitShadowComplement.odd_weight_identities

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitShadowComplement.odd_weight_takagi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.SevenQubitShadowComplement.odd_weight_takagi
