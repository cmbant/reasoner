module

public import Mathlib

/-!
# The abstract spin-flip model of `prop:shadow-complement`

`QI/multiqubit_entanglement/seven_qubit_entanglement/shadow_equality_geometry.tex`, `prop:shadow-complement`.
Setting: `z = |0⟩ u₀ + |1⟩ u₁` with `u_a` vectors of the (arbitrary finite-dimensional) complement
space `E`, which carries the antiunitary involution `J = J_m` (`IsSpinFlip`: conjugate-linear,
`⟨Jx, Jy⟩ = conj ⟨x, y⟩`, `J² = 1`; the concrete `J_m = ε^{⊗m} K` with `m` even is an instance, see
`SevenQubitShadowComplementPauli.lean`, but nothing about qubits is used here). The distinguished site
carries `ε = ((0,1),(-1,0))`, so `J_n z = ε ⊗ J_m` acts as `(J_n z)_a = ∑_b ε_{ab} J(u_b)`.

Proved here (all statements are Lean theorems about the abstract model):

* `IsSpinFlip.inner_symm`: `T_{ab} = ⟨u_a, J u_b⟩` is symmetric ("`T^{(s)}` is complex symmetric").
* `shadowQ_eq`: `q_s = ∑_{α∈{x,y,z}} |⟨z, σ_α^{(s)} J_n z⟩|² = 2 ‖T‖_F²`.
* `shadowQ_eq_trace`: `q_s = 2 tr(ρ J ρ J⁻¹)` with `ρ = ∑_a |u_a⟩⟨u_a|` (here `J⁻¹ = J`; the
  conjugated operator is `rhoFlip` and `rhoFlip_apply` shows `rhoFlip x = J (ρ (J x))`).
* `trace_rho_rho`, `trace_rhoFlip_rhoFlip`, `hsNormSq_rho_sub_rhoFlip`: `tr ρ² = ∑ |⟨u_a,u_b⟩|²`,
  `tr (JρJ⁻¹)² = tr ρ²` and `‖ρ - JρJ⁻¹‖₂² = 2 tr ρ² - 2 tr(ρ J ρ J⁻¹)`, the Hilbert–Schmidt norm
  being `hsNormSq A = Re tr(A† A)`.
-/

@[expose] public section


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

/-- `tr(ρ · JρJ⁻¹) = ∑_{a,b} |T_{ab}|²` as a real number. -/
theorem trace_rho_rhoFlip_re (z : Fin 2 → E) :
    (LinearMap.trace ℂ E (rho z ∘ₗ rhoFlip J z)).re = ∑ a, ∑ b, ‖Tm J z a b‖ ^ 2 := by
  rw [trace_rho_rhoFlip]
  simp only [Complex.re_sum, Complex.ofReal_re]

/-- `prop:shadow-complement`: `q_s = 2 tr(ρ J ρ J⁻¹)` (as complex numbers). -/
theorem shadowQ_eq_trace (h : IsSpinFlip J) (z : Fin 2 → E) :
    (shadowQ J z : ℂ) = 2 * LinearMap.trace ℂ E (rho z ∘ₗ rhoFlip J z) := by
  rw [shadowQ_eq h, trace_rho_rhoFlip]
  push_cast
  rfl

omit [FiniteDimensional ℂ E] in
theorem inner_mul_inner_swap (v w : E) : ⟪v, w⟫_ℂ * ⟪w, v⟫_ℂ = ((‖⟪v, w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  have e : ⟪w, v⟫_ℂ = conj ⟪v, w⟫_ℂ := (inner_conj_symm w v).symm
  rw [e, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- `tr ρ² = ∑_{a,b} |⟨u_a, u_b⟩|²`. -/
theorem trace_rho_rho (z : Fin 2 → E) :
    LinearMap.trace ℂ E (rho z ∘ₗ rho z) = ∑ a, ∑ b, ((‖⟪z a, z b⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  have hc : rho z ∘ₗ rho z = ∑ a, ∑ b, rank1 (z a) ∘ₗ rank1 (z b) := by
    ext x
    simp [rho]
  rw [hc]
  simp only [map_sum, trace_rank1_comp]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => inner_mul_inner_swap _ _

/-- `tr (JρJ⁻¹)² = tr ρ²` (`J` is antiunitary). -/
theorem trace_rhoFlip_rhoFlip (h : IsSpinFlip J) (z : Fin 2 → E) :
    LinearMap.trace ℂ E (rhoFlip J z ∘ₗ rhoFlip J z) = LinearMap.trace ℂ E (rho z ∘ₗ rho z) := by
  have hc : rhoFlip J z ∘ₗ rhoFlip J z = ∑ a, ∑ b, rank1 (J (z a)) ∘ₗ rank1 (J (z b)) := by
    ext x
    simp [rhoFlip]
  rw [hc, trace_rho_rho]
  simp only [map_sum, trace_rank1_comp, h.inner_map]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← map_mul, inner_mul_inner_swap, Complex.conj_ofReal]

/-- The Hilbert–Schmidt norm squared `‖A‖₂² = Re tr(A† A)`. -/
noncomputable def hsNormSq (A : E →ₗ[ℂ] E) : ℝ :=
  (LinearMap.trace ℂ E (LinearMap.adjoint A ∘ₗ A)).re

omit [FiniteDimensional ℂ E] in
theorem rank1_isSymmetric (v : E) : (rank1 v).IsSymmetric := by
  intro x y
  simp only [rank1, LinearMap.smulRight_apply, innerₛₗ_apply_apply, inner_smul_left,
    inner_smul_right]
  rw [← inner_conj_symm v x]
  simp [mul_comm]

omit [FiniteDimensional ℂ E] in
theorem rho_isSymmetric (z : Fin 2 → E) : (rho z).IsSymmetric := by
  intro x y
  simp only [rho, LinearMap.sum_apply, sum_inner, inner_sum]
  exact Finset.sum_congr rfl fun a _ => rank1_isSymmetric (z a) x y

omit [FiniteDimensional ℂ E] in
theorem rhoFlip_isSymmetric (z : Fin 2 → E) : (rhoFlip J z).IsSymmetric := by
  intro x y
  simp only [rhoFlip, LinearMap.sum_apply, sum_inner, inner_sum]
  exact Finset.sum_congr rfl fun a _ => rank1_isSymmetric (J (z a)) x y

/-- **`‖ρ - JρJ⁻¹‖₂² = 2 tr ρ² - 2 tr(ρ J ρ J⁻¹)`** (as real parts). -/
theorem hsNormSq_rho_sub_rhoFlip (h : IsSpinFlip J) (z : Fin 2 → E) :
    hsNormSq (rho z - rhoFlip J z) =
      2 * (LinearMap.trace ℂ E (rho z ∘ₗ rho z)).re
        - 2 * (LinearMap.trace ℂ E (rho z ∘ₗ rhoFlip J z)).re := by
  have hs : (rho z - rhoFlip J z).IsSymmetric := (rho_isSymmetric z).sub (rhoFlip_isSymmetric z)
  unfold hsNormSq
  rw [hs.adjoint_eq]
  have e : (rho z - rhoFlip J z) ∘ₗ (rho z - rhoFlip J z) =
      rho z ∘ₗ rho z + rhoFlip J z ∘ₗ rhoFlip J z - rho z ∘ₗ rhoFlip J z - rhoFlip J z ∘ₗ rho z := by
    ext x
    simp
    abel
  have hcomm : LinearMap.trace ℂ E (rhoFlip J z ∘ₗ rho z) = LinearMap.trace ℂ E (rho z ∘ₗ rhoFlip J z) :=
    LinearMap.trace_comp_comm' _ _
  rw [e, map_sub, map_sub, map_add, trace_rhoFlip_rhoFlip h, hcomm]
  simp only [Complex.sub_re, Complex.add_re]
  ring

end Trace

end Abstract

end FormalResearch.FourQubitEntropy.SevenQubitShadowComplement
