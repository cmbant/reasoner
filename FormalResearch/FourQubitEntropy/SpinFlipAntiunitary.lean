import Mathlib
import FormalResearch.QIB.KramersHalfFilling

/-!
# Antiunitary spin-flip purification, abstract form (`prop:antiunitary-purification`)

Source: `ResearchNotes/QI/seven_qubit_entanglement/spinflip_graph_parity.tex`,
`prop:antiunitary-purification` (QIprojects PR #200).

`E` is a complex inner-product space and `Θ : E →ₛₗ[conj] E` an antilinear map with the antiunitary
inner-product identity `⟪Θ u, Θ v⟫ = conj ⟪u, v⟫` (`FormalResearch.QIB.IsAntiunitary`), `Θ² = η`, `η = ±1`
(for the tensor product of local antiunitaries `Θ = ⊗ Θ_i`, `η = ∏ η_i`).  For a unit `z` the
ordinary-site reduction of `Ω_z = (|0⟩ z + |1⟩ Θ z)/√2` is `ρ = ½(|z⟩⟨z| + |Θz⟩⟨Θz|)` (the statement of the
paper; that the reduction of `Ω_z` *is* this operator is the trivial partial trace over the distinguished
qubit, carried out concretely for qubits in `SpinFlipOmega.lean`).

* `rhoOrd_comm`: `Θ ρ Θ⁻¹ = ρ`, i.e. `Θ (ρ x) = ρ (Θ x)`;
* `expect_odd`: a symmetric observable with `Θ O Θ⁻¹ = -O` has `tr(ρ O) = ½(⟪z,Oz⟫ + ⟪Θz,OΘz⟫) = 0`;
* `even_finrank_of_kramers`, `even_finrank_eigenspace`: if `η = -1` then every `Θ`-invariant subspace has
  even complex dimension; hence every eigenspace of a symmetric operator commuting with `Θ` is even
  dimensional (the Kramers pairing `Θ_S² = -1`, `prod_{i∈S} η_i = -1`).

Claim class: **proved**.  Only the structural (`Θ² = ±1`, `Θ` antiunitary) hypotheses are used, so the
statement is dimension-independent as in the paper.
-/

open scoped InnerProductSpace ComplexConjugate
open FormalResearch.QIB

namespace FormalResearch.FourQubitEntropy.SpinFlip

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `ρ_ord = ½(|z⟩⟨z| + |Θz⟩⟨Θz|)` as a map `x ↦ ½(⟪z,x⟫ z + ⟪Θz,x⟫ Θz)`. -/
noncomputable def rhoOrd (Θ : E →ₛₗ[starRingEnd ℂ] E) (z x : E) : E :=
  (1 / 2 : ℂ) • (⟪z, x⟫_ℂ • z + ⟪Θ z, x⟫_ℂ • Θ z)

/-- **`Θ ρ_ord Θ⁻¹ = ρ_ord`.** -/
theorem rhoOrd_comm (Θ : E →ₛₗ[starRingEnd ℂ] E) (hΘ : IsAntiunitary (fun v => Θ v))
    (η : ℂ) (hη : η = 1 ∨ η = -1) (hΘΘ : ∀ v, Θ (Θ v) = η • v) (z x : E) :
    Θ (rhoOrd Θ z x) = rhoOrd Θ z (Θ x) := by
  have hη' : conj η = η := by rcases hη with rfl | rfl <;> simp
  have hη2 : η * η = 1 := by rcases hη with rfl | rfl <;> simp
  have h1 : ⟪Θ z, Θ x⟫_ℂ = ⟪x, z⟫_ℂ := by
    have := hΘ z x
    simp only at this
    rw [this]; exact inner_conj_symm x z
  have h2 : ⟪z, Θ x⟫_ℂ = η * ⟪x, Θ z⟫_ℂ := by
    have := hΘ (Θ z) x
    simp only at this
    rw [hΘΘ z, inner_smul_left, hη'] at this
    have e : η * ⟪z, Θ x⟫_ℂ = ⟪x, Θ z⟫_ℂ := by rw [this]; exact inner_conj_symm x (Θ z)
    linear_combination η * e - ⟪z, Θ x⟫_ℂ * hη2
  unfold rhoOrd
  rw [map_smulₛₗ, map_add, map_smulₛₗ, map_smulₛₗ, hΘΘ z, h1, h2]
  have c1 : conj ⟪z, x⟫_ℂ = ⟪x, z⟫_ℂ := inner_conj_symm x z
  have c2 : conj ⟪Θ z, x⟫_ℂ = ⟪x, Θ z⟫_ℂ := inner_conj_symm x (Θ z)
  have c3 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one]; congr 1; exact map_ofNat _ 2
  rw [c3, c1, c2, smul_smul, mul_comm ⟪x, Θ z⟫_ℂ η, add_comm]

/-- **Odd observables have zero expectation on `ρ_ord`.** `O` symmetric with `Θ O Θ⁻¹ = -O` (i.e.
`O (Θ v) = -Θ (O v)`): `tr(ρ_ord O) = ½(⟪z,Oz⟫ + ⟪Θz, O Θz⟫) = 0`. -/
theorem expect_odd (Θ : E →ₛₗ[starRingEnd ℂ] E) (hΘ : IsAntiunitary (fun v => Θ v))
    (O : E →ₗ[ℂ] E) (hO : O.IsSymmetric) (hodd : ∀ v, O (Θ v) = -Θ (O v)) (z : E) :
    ⟪z, O z⟫_ℂ + ⟪Θ z, O (Θ z)⟫_ℂ = 0 := by
  have h1 : conj ⟪z, O z⟫_ℂ = ⟪z, O z⟫_ℂ := by
    rw [inner_conj_symm]; exact hO z z
  have h2 : ⟪Θ z, O (Θ z)⟫_ℂ = -conj ⟪z, O z⟫_ℂ := by
    rw [hodd, inner_neg_right]
    have := hΘ z (O z)
    simp only at this
    rw [this]
  rw [h2, h1]; ring

end Abstract

section Kramers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- `span{q, Θ q}` is a `Θ`-invariant plane for a unit vector `q` when `Θ² = -1`. -/
theorem finrank_span_pair (Θ : E →ₛₗ[starRingEnd ℂ] E) (hΘ : IsAntiunitary (fun v => Θ v))
    (hK : IsKramers (fun v => Θ v)) {q : E} (hq : ‖q‖ = 1) :
    Module.finrank ℂ (Submodule.span ℂ {q, Θ q} : Submodule ℂ E) = 2 := by
  classical
  have hq' : ‖Θ q‖ = 1 := by rw [hΘ.norm_eq]; exact hq
  have hperp : ⟪q, Θ q⟫_ℂ = 0 := kramers_inner_self hΘ hK q
  have hperp' : ⟪Θ q, q⟫_ℂ = 0 := by rw [← inner_conj_symm, hperp]; simp
  have hne : q ≠ Θ q := by
    intro h
    rw [← h] at hperp
    simp [inner_self_eq_norm_sq_to_K, hq] at hperp
  have hs : Orthonormal ℂ ((↑) : ({q, Θ q} : Set E) → E) := by
    rw [orthonormal_subtype_iff_ite]
    intro v hv w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hw
    rcases hv with h | h <;> rcases hw with h' | h' <;> subst h <;> subst h'
    · simp [inner_self_eq_norm_sq_to_K, hq]
    · simp [hne, hperp]
    · simp [hne.symm, hperp']
    · simp [inner_self_eq_norm_sq_to_K, hq']
  have := finrank_span_set_eq_card (R := ℂ) (s := ({q, Θ q} : Set E))
    (hs.linearIndependent : LinearIndepOn ℂ id ({q, Θ q} : Set E))
  rw [this]
  simp [Set.toFinset_insert, Finset.card_pair hne]

/-- If `Θ² = -1`, every `Θ`-invariant subspace has even complex dimension. -/
theorem even_finrank_of_kramers (Θ : E →ₛₗ[starRingEnd ℂ] E) (hΘ : IsAntiunitary (fun v => Θ v))
    (hK : IsKramers (fun v => Θ v)) :
    ∀ (d : ℕ) (W : Submodule ℂ E), Module.finrank ℂ W = d → (∀ w ∈ W, Θ w ∈ W) → Even d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro W hd hW
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · exact ⟨0, rfl⟩
    · -- a unit vector in `W`
      obtain ⟨x, hxW, hx0⟩ : ∃ x ∈ W, x ≠ 0 := by
        by_contra hcon
        have : W = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro y hy
          by_contra hy0
          exact hcon ⟨y, hy, hy0⟩
        rw [this] at hd; simp at hd; omega
      obtain ⟨q, hqW, hq⟩ : ∃ q ∈ W, ‖q‖ = 1 := by
        refine ⟨((‖x‖⁻¹ : ℝ) : ℂ) • x, W.smul_mem _ hxW, ?_⟩
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)
      have hP2 : Module.finrank ℂ (Submodule.span ℂ {q, Θ q} : Submodule ℂ E) = 2 :=
        finrank_span_pair Θ hΘ hK hq
      have hPW : (Submodule.span ℂ {q, Θ q} : Submodule ℂ E) ≤ W := by
        rw [Submodule.span_le]
        intro z hz
        rcases hz with h | h
        · rw [h]; exact hqW
        · rw [Set.mem_singleton_iff.mp h]; exact hW q hqW
      have hPΘ : ∀ p ∈ (Submodule.span ℂ {q, Θ q} : Submodule ℂ E), Θ p ∈ Submodule.span ℂ {q, Θ q} := by
        intro p hp
        rw [Submodule.mem_span_pair] at hp ⊢
        obtain ⟨α, β, hαβ⟩ := hp
        refine ⟨-conj β, conj α, ?_⟩
        rw [← hαβ, map_add, map_smulₛₗ, map_smulₛₗ]
        have := hK q
        simp only at this
        rw [this]
        simp [neg_smul, add_comm]
      have hsum := Submodule.finrank_add_inf_finrank_orthogonal hPW
      rw [hP2, hd] at hsum
      have hW'Θ : ∀ w ∈ (Submodule.span ℂ {q, Θ q} : Submodule ℂ E)ᗮ ⊓ W,
          Θ w ∈ (Submodule.span ℂ {q, Θ q} : Submodule ℂ E)ᗮ ⊓ W := by
        intro w hw
        refine ⟨(Submodule.mem_orthogonal _ _).mpr ?_, hW w hw.2⟩
        intro p hp
        have hp' : -Θ p ∈ (Submodule.span ℂ {q, Θ q} : Submodule ℂ E) :=
          Submodule.neg_mem _ (hPΘ p hp)
        have h0 : ⟪-Θ p, w⟫_ℂ = 0 := (Submodule.mem_orthogonal _ w).mp hw.1 _ hp'
        have := hΘ (-Θ p) w
        simp only at this
        rw [map_neg, hK p, neg_neg, h0] at this
        simpa using this
      have hlt : Module.finrank ℂ ((Submodule.span ℂ {q, Θ q} : Submodule ℂ E)ᗮ ⊓ W : Submodule ℂ E) < d := by
        omega
      have := ih _ hlt _ rfl hW'Θ
      have h2 : d = 2 + Module.finrank ℂ ((Submodule.span ℂ {q, Θ q} : Submodule ℂ E)ᗮ ⊓ W : Submodule ℂ E) := by
        omega
      rw [h2]
      exact (even_two.add this)

/-- Kramers pairing: every eigenspace of a symmetric operator commuting with `Θ` (`Θ² = -1`) has even
complex dimension, i.e. every eigenvalue of the (Hermitian) reduced matrix is even-degenerate. -/
theorem even_finrank_eigenspace (Θ : E →ₛₗ[starRingEnd ℂ] E) (hΘ : IsAntiunitary (fun v => Θ v))
    (hK : IsKramers (fun v => Θ v)) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric)
    (hcomm : ∀ v, Θ (A v) = A (Θ v)) (μ : ℂ) :
    Even (Module.finrank ℂ (Module.End.eigenspace A μ)) := by
  by_cases hμ : Module.End.eigenspace A μ = ⊥
  · rw [hμ]; simp
  · have hreal : conj μ = μ := by
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
      have := hA.conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨hv, hv0⟩)
      exact this
    refine even_finrank_of_kramers Θ hΘ hK _ (Module.End.eigenspace A μ) rfl ?_
    intro w hw
    rw [Module.End.mem_eigenspace_iff] at hw ⊢
    rw [← hcomm, hw, map_smulₛₗ, hreal]

end Kramers

end FormalResearch.FourQubitEntropy.SpinFlip
