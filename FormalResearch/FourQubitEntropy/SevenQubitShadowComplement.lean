import Mathlib

/-!
# Local shadow and complement asymmetry for odd `n` (`prop:shadow-complement`)

`ResearchNotes/QI/seven_qubit_entanglement/shadow_equality_geometry.tex`, `prop:shadow-complement`.
Setting: `z = |0⟩ u₀ + |1⟩ u₁` with `u_a` vectors of the (arbitrary finite-dimensional) complement
space `E`, which carries the antiunitary involution `J = J_m` (`IsSpinFlip`: conjugate-linear,
`⟨Jx, Jy⟩ = conj ⟨x, y⟩`, `J² = 1`; the case `J_m = ε^{⊗m} K` with `m` even is an instance, but
nothing about qubits is used). The distinguished site carries `ε = ((0,1),(-1,0))`, so
`J_n z = ε ⊗ J_m` acts as `(J_n z)_a = ∑_b ε_{ab} J(u_b)`.

Proved here (all statements are Lean theorems about the abstract model):

* `IsSpinFlip.inner_symm`: `T_{ab} = ⟨u_a, J u_b⟩` is symmetric ("`T^{(s)}` is complex symmetric").
* `shadowQ_eq`: `q_s = ∑_{α∈{x,y,z}} |⟨z, σ_α^{(s)} J_n z⟩|² = 2 ‖T‖_F²`.
* `shadowQ_eq_trace`: `q_s = 2 tr(ρ J ρ J⁻¹)` with `ρ = ∑_a |u_a⟩⟨u_a|` (here `J⁻¹ = J`; the
  conjugated operator is `rhoFlip` and `rhoFlip_apply` shows `rhoFlip x = J (ρ (J x))`).
* `odd_weight_identities`: the two boxed identities `∑_{j odd} B_j = 2^{n-2} tr ρ_s² - 2^{n-3} q_s` and
  `‖ρ - JρJ⁻¹‖₂² = 2^{3-n} ∑_{j odd} B_j` (stated with `m = n - 1`, as `2^m/2 · r - 2^m/4 · q` and
  `2^m · d = 4 ∑_odd B`), **conditional on the Pauli-expansion inputs** passed as hypotheses:
  `2^m tr ρ̄² = ∑_j B_j`, `2^m tr(ρ̄ J ρ̄ J⁻¹) = ∑_j (-1)^j B_j`, `q = 2 tr(ρ̄ J ρ̄ J⁻¹)`,
  `tr ρ̄² = tr ρ_s²` and `d = tr ρ̄² + tr (Jρ̄J⁻¹)² - 2 tr(ρ̄ J ρ̄ J⁻¹)` with `tr (Jρ̄J⁻¹)² = tr ρ̄²`.
  The Pauli expansion itself (`J P J⁻¹ = (-1)^{wt P} P` on `m` qubits and the reduced-state
  expansion) is **not** formalized; this is only the arithmetic consequence.
* `takagi_frobenius`, `shadowQ_takagi`: if the normalized overlap matrix `T̂ = 2T` has a Takagi
  factorization `T̂ = U diag(t) Uᵀ` (`U` unitary, `t` real), then `‖T̂‖_F² = t₁² + t₂²` and
  `q_s = (t₁² + t₂²)/2`. Existence of the Takagi factorization and the basis independence of the `t_i`
  are not formalized.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitShadowComplement

open Finset Matrix
open scoped InnerProductSpace ComplexConjugate

/-! ### The abstract model -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `J` is an antiunitary involution. -/
structure IsSpinFlip (J : E →ₛₗ[starRingEnd ℂ] E) : Prop where
  inner_map : ∀ x y, ⟪J x, J y⟫_ℂ = conj ⟪x, y⟫_ℂ
  invol : ∀ x, J (J x) = x

variable {J : E →ₛₗ[starRingEnd ℂ] E}

theorem IsSpinFlip.inner_symm (h : IsSpinFlip J) (u v : E) : ⟪u, J v⟫_ℂ = ⟪v, J u⟫_ℂ := by
  have h1 := h.inner_map u (J v)
  rw [h.invol] at h1
  calc ⟪u, J v⟫_ℂ = conj (conj ⟪u, J v⟫_ℂ) := (Complex.conj_conj _).symm
    _ = conj ⟪J u, v⟫_ℂ := by rw [← h1]
    _ = ⟪v, J u⟫_ℂ := inner_conj_symm _ _

/-- `ε = ((0, 1), (-1, 0))` on the distinguished qubit. -/
def eps : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- `σ_x, σ_y, σ_z` (indices `0, 1, 2`). -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

/-- `J_n z = (ε ⊗ J_m) z`: `(J_n z)_a = ∑_b ε_{ab} J(z_b)`. -/
def Jn (J : E →ₛₗ[starRingEnd ℂ] E) (z : Fin 2 → E) : Fin 2 → E :=
  fun a => ∑ b, eps a b • J (z b)

/-- `⟨z, σ_α^{(s)} J_n z⟩`. -/
noncomputable def amp (J : E →ₛₗ[starRingEnd ℂ] E) (α : Fin 3) (z : Fin 2 → E) : ℂ :=
  ∑ a, ⟪z a, ∑ c, pauli α a c • Jn J z c⟫_ℂ

/-- `T_{ab} = ⟨u_a, J u_b⟩`. -/
noncomputable def Tm (J : E →ₛₗ[starRingEnd ℂ] E) (z : Fin 2 → E) (a b : Fin 2) : ℂ := ⟪z a, J (z b)⟫_ℂ

/-- `q_s = ∑_α |⟨z, σ_α^{(s)} J_n z⟩|²`. -/
noncomputable def shadowQ (J : E →ₛₗ[starRingEnd ℂ] E) (z : Fin 2 → E) : ℝ :=
  ∑ α, ‖amp J α z‖ ^ 2

theorem amp_eq (z : Fin 2 → E) (α : Fin 3) :
    amp J α z = ∑ a, ∑ b, (pauli α * eps) a b * Tm J z a b := by
  simp only [amp, Jn, Tm, inner_sum, inner_smul_right, Matrix.mul_apply, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem shadowQ_eq (h : IsSpinFlip J) (z : Fin 2 → E) :
    shadowQ J z = 2 * ∑ a, ∑ b, ‖Tm J z a b‖ ^ 2 := by
  have hs : Tm J z 1 0 = Tm J z 0 1 := h.inner_symm _ _
  simp only [shadowQ, amp_eq, Fin.sum_univ_three, Fin.sum_univ_two, pauli, eps, Matrix.mul_apply,
    Complex.sq_norm, Complex.normSq_apply]
  simp [hs]
  ring


/-! ### `q_s = 2 tr(ρ J ρ J⁻¹)` -/

section Trace

variable [FiniteDimensional ℂ E]

/-- The rank-one operator `|v⟩⟨v|`. -/
noncomputable def rank1 (v : E) : E →ₗ[ℂ] E := (innerₛₗ ℂ v).smulRight v

/-- `ρ = ∑_a |u_a⟩⟨u_a|`. -/
noncomputable def rho (z : Fin 2 → E) : E →ₗ[ℂ] E := ∑ a, rank1 (z a)

/-- `J ρ J⁻¹ = ∑_a |J u_a⟩⟨J u_a|` (`J⁻¹ = J`); `rhoFlip_apply` identifies it with `x ↦ J (ρ (J x))`. -/
noncomputable def rhoFlip (J : E →ₛₗ[starRingEnd ℂ] E) (z : Fin 2 → E) : E →ₗ[ℂ] E :=
  ∑ a, rank1 (J (z a))

omit [FiniteDimensional ℂ E] in
theorem rhoFlip_apply (h : IsSpinFlip J) (z : Fin 2 → E) (x : E) :
    rhoFlip J z x = J (rho z (J x)) := by
  simp only [rhoFlip, rho, rank1, LinearMap.sum_apply, LinearMap.smulRight_apply, innerₛₗ_apply_apply,
    map_sum, map_smulₛₗ]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 := h.inner_map (z a) (J x)
  rw [h.invol] at h1
  rw [← h1]

theorem trace_rank1_comp (v w : E) :
    LinearMap.trace ℂ E (rank1 v ∘ₗ rank1 w) = ⟪v, w⟫_ℂ * ⟪w, v⟫_ℂ := by
  have : rank1 v ∘ₗ rank1 w = ((⟪v, w⟫_ℂ • innerₛₗ ℂ w : E →ₗ[ℂ] ℂ)).smulRight v := by
    ext x
    simp only [LinearMap.comp_apply, rank1, LinearMap.smulRight_apply, innerₛₗ_apply_apply,
      LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [smul_smul, mul_comm]
  rw [this, LinearMap.trace_smulRight]
  simp

/-- `tr(ρ · JρJ⁻¹) = ∑_{a,b} |T_{ab}|²`. -/
theorem trace_rho_rhoFlip (z : Fin 2 → E) :
    LinearMap.trace ℂ E (rho z ∘ₗ rhoFlip J z) = ∑ a, ∑ b, ((‖Tm J z a b‖ ^ 2 : ℝ) : ℂ) := by
  have hc : rho z ∘ₗ rhoFlip J z = ∑ a, ∑ b, rank1 (z a) ∘ₗ rank1 (J (z b)) := by
    ext x
    simp [rho, rhoFlip]
  rw [hc]
  simp only [map_sum, trace_rank1_comp]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have e : ⟪J (z b), z a⟫_ℂ = conj (Tm J z a b) := (inner_conj_symm (J (z b)) (z a)).symm
  rw [e]
  show Tm J z a b * conj (Tm J z a b) = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- `prop:shadow-complement`: `q_s = 2 tr(ρ J ρ J⁻¹)` (as complex numbers). -/
theorem shadowQ_eq_trace (h : IsSpinFlip J) (z : Fin 2 → E) :
    (shadowQ J z : ℂ) = 2 * LinearMap.trace ℂ E (rho z ∘ₗ rhoFlip J z) := by
  rw [shadowQ_eq h, trace_rho_rhoFlip]
  push_cast
  rfl

end Trace


/-! ### The odd-weight identities (arithmetic consequence of the Pauli expansions) -/

/-- The two boxed identities of `prop:shadow-complement`, with `m = n - 1` (so `2^m/2 = 2^{n-2}`,
`2^m/4 = 2^{n-3}`, `2^{3-n} = 4/2^m`). Inputs, all passed as hypotheses: `P = tr ρ̄²`,
`C = tr(ρ̄ J ρ̄ J⁻¹)`, `r = tr ρ_s²`, `q = q_s`, `d = ‖ρ̄ - Jρ̄J⁻¹‖₂²`, and the Pauli expansions
`2^m P = ∑_j B_j`, `2^m C = ∑_j (-1)^j B_j`. -/
theorem odd_weight_identities {m : ℕ} (B : ℕ → ℝ) (P C q r d : ℝ)
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

/-- The Takagi form of the first boxed identity for `ρ_s = I/2` (`r = 1/2`):
`∑_{j odd} B_j = 2^{n-3} (1 - (t₁² + t₂²)/2)` (here `2^{n-3} = 2^m/4`). -/
theorem odd_weight_takagi {m : ℕ} (B : ℕ → ℝ) (P C q d t₀ t₁ : ℝ)
    (hP : (2 : ℝ) ^ m * P = ∑ j ∈ range (m + 1), B j)
    (hC : (2 : ℝ) ^ m * C = ∑ j ∈ range (m + 1), (-1) ^ j * B j)
    (hq : q = 2 * C) (hr : P = 1 / 2) (hd : d = 2 * P - 2 * C)
    (hqt : q = (t₀ ^ 2 + t₁ ^ 2) / 2) :
    ∑ j ∈ (range (m + 1)).filter Odd, B j = (2 : ℝ) ^ m / 4 * (1 - (t₀ ^ 2 + t₁ ^ 2) / 2) := by
  have := (odd_weight_identities B P C q (1 / 2) d hP hC hq hr hd).1
  rw [this, hqt]
  ring

end Abstract

end FormalResearch.FourQubitEntropy.SevenQubitShadowComplement
