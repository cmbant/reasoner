module

public import Mathlib

/-!
# Equality step of the five-copy certificate: tangent line, then `t = 0` (abstract linear algebra)

`lem:fivecopy-tangent-line` and the shortcut of `thm:fivecopy-family-equality`
(`ResearchNotes/QI/seven_qubit_entanglement/moment_orbit_rigidity.tex`).  Nothing here mentions seven qubits, five copies or the
certificate data; the moment space `M`, the base point `X₀`, the tangent `X₀'`, the face maps `Γ_b` and the
probes are arguments.  This is needed only for the *equality* statement (uniqueness of the icosahedral
orbit), not for `SevenPurityBound`.

* `mem_span_of_critical_vanish`: if every functional killing `X₀` and `X₀'` kills `x`, then
  `x ∈ span{X₀, X₀'}`.
* `tangent_line`: if the critical functionals are the combinations `x ↦ ∑_b tr[W_b S_b W_bᵀ Γ_b(x)]` and a point
  `x` has `W_bᵀ Γ_b(x) W_b = 0` for every `b`, then `x ∈ span{X₀,X₀'}`; if `ν X₀ = 1`, `ν X₀' = 0`,
  `ν x = 1` then `x = X₀ + t X₀'`.
* `tangent_coeff_zero`: if `H` and `H²` (a linear functional equal to the square on actual states) have
  `H X₀' ≠ 0` and `H₂ X₀' = 2 (H X₀)(H X₀')`, then `t = 0` (the shortcut `(h+96t)² = h² + 192 h t`).
* `equality_moment`, `equality_moment_centred`: the moment-level equality step of `thm:fivecopy-family-equality`
  (tangent line, then `t = 0` from a critical functional equal to `(H − H X₀)²`), for abstract `H` with `H X₀' ≠ 0`.
  The family value `H(ψ_y) = 155 + 96y` that supplies `H X₀' ≠ 0`, and the passage from the moment to the orbit
  (`thm:moment-orbit-rigidity`), are not formalised here.
-/

@[expose] public section


open Matrix

namespace FormalResearch.FourQubitEntropy.SevenFiveCopy

section
variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- A point on which every functional vanishing at `X₀` and `X₀'` vanishes lies on the tangent line. -/
theorem mem_span_of_critical_vanish (X₀ X₀' x : M)
    (h : ∀ f : Module.Dual ℝ M, f X₀ = 0 → f X₀' = 0 → f x = 0) :
    ∃ a t : ℝ, x = a • X₀ + t • X₀' := by
  by_contra hne
  have hx : x ∉ Submodule.span ℝ {X₀, X₀'} := by
    intro hx
    obtain ⟨a, t, e⟩ := Submodule.mem_span_pair.mp hx
    exact hne ⟨a, t, e.symm⟩
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have h0 : f X₀ = 0 := by
    have : f X₀ ∈ (Submodule.span ℝ {X₀, X₀'}).map f :=
      ⟨X₀, Submodule.subset_span (by simp), rfl⟩
    rw [hmap] at this; simpa using this
  have h1 : f X₀' = 0 := by
    have : f X₀' ∈ (Submodule.span ℝ {X₀, X₀'}).map f :=
      ⟨X₀', Submodule.subset_span (by simp), rfl⟩
    rw [hmap] at this; simpa using this
  exact hf (h f h0 h1)

variable {ι : Type*} [Fintype ι] {n m : ι → ℕ}

/-- **Tangent-line lemma.**  `Γ b : M → Sym_{n b}`, probes `W b` (`n b × m b`).  If every critical functional is
`x ↦ ∑_b tr[W_b S_b W_bᵀ Γ_b(x)]` for some matrices `S_b`, and `W_bᵀ Γ_b(x) W_b = 0` for all `b`, then
`x` lies in the span of `X₀` and `X₀'`. -/
theorem tangent_line (Γ : ∀ b, M →ₗ[ℝ] Matrix (Fin (n b)) (Fin (n b)) ℝ)
    (W : ∀ b, Matrix (Fin (n b)) (Fin (m b)) ℝ) (X₀ X₀' x : M)
    (hspan : ∀ f : Module.Dual ℝ M, f X₀ = 0 → f X₀' = 0 →
      ∃ S : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℝ,
        ∀ y, f y = ∑ b, ((W b * S b * (W b)ᵀ) * Γ b y).trace)
    (hx : ∀ b, (W b)ᵀ * Γ b x * W b = 0) :
    ∃ a t : ℝ, x = a • X₀ + t • X₀' := by
  refine mem_span_of_critical_vanish X₀ X₀' x fun f h0 h1 => ?_
  obtain ⟨S, hS⟩ := hspan f h0 h1
  rw [hS]
  refine Finset.sum_eq_zero fun b _ => ?_
  have : ((W b * S b * (W b)ᵀ) * Γ b x).trace = (S b * ((W b)ᵀ * Γ b x * W b)).trace := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm (W b)]
    simp only [← Matrix.mul_assoc]
  rw [this, hx b]; simp

/-- Normalising along the tangent line: `ν X₀ = 1`, `ν X₀' = 0`, `ν x = 1` give `x = X₀ + t X₀'`. -/
theorem tangent_line_normalised (ν : M →ₗ[ℝ] ℝ) (X₀ X₀' x : M) (h0 : ν X₀ = 1) (h1 : ν X₀' = 0)
    (hx : ν x = 1) (hl : ∃ a t : ℝ, x = a • X₀ + t • X₀') : ∃ t : ℝ, x = X₀ + t • X₀' := by
  obtain ⟨a, t, e⟩ := hl
  have : a = 1 := by
    have := congrArg ν e
    simp [h0, h1, hx] at this
    linarith
  exact ⟨t, by rw [e, this, one_smul]⟩

/-- **The shortcut.**  If `x = X₀ + t X₀'`, `H₂ x = (H x)²`, `H₂ X₀ = (H X₀)²`, `H₂ X₀' = 2 (H X₀)(H X₀')`
and `H X₀' ≠ 0` (in the paper `H = 104 S₁ − 25 ℰ₂`, `H(ψ_x) = 155 + 96 x`), then `t = 0`. -/
theorem tangent_coeff_zero (H H₂ : M →ₗ[ℝ] ℝ) (X₀ X₀' x : M) (t : ℝ) (hx : x = X₀ + t • X₀')
    (hsq : H₂ x = H x ^ 2) (h0 : H₂ X₀ = H X₀ ^ 2) (h1 : H₂ X₀' = 2 * H X₀ * H X₀')
    (hd : H X₀' ≠ 0) : t = 0 := by
  subst hx
  simp only [map_add, map_smul, smul_eq_mul, h0, h1] at hsq
  have : t ^ 2 * (H X₀') ^ 2 = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h
  · exact pow_eq_zero_iff (by norm_num) |>.mp h
  · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) hd

/-- Equality step: the critical-functional hypothesis, normalisation and the `H`, `H²` shortcut give
`x = X₀`. -/
theorem equality_moment (Γ : ∀ b, M →ₗ[ℝ] Matrix (Fin (n b)) (Fin (n b)) ℝ)
    (W : ∀ b, Matrix (Fin (n b)) (Fin (m b)) ℝ) (ν H H₂ : M →ₗ[ℝ] ℝ) (X₀ X₀' x : M)
    (hspan : ∀ f : Module.Dual ℝ M, f X₀ = 0 → f X₀' = 0 →
      ∃ S : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℝ,
        ∀ y, f y = ∑ b, ((W b * S b * (W b)ᵀ) * Γ b y).trace)
    (hx : ∀ b, (W b)ᵀ * Γ b x * W b = 0)
    (hν0 : ν X₀ = 1) (hν1 : ν X₀' = 0) (hνx : ν x = 1)
    (hsq : H₂ x = H x ^ 2) (h0 : H₂ X₀ = H X₀ ^ 2) (h1 : H₂ X₀' = 2 * H X₀ * H X₀')
    (hd : H X₀' ≠ 0) : x = X₀ := by
  obtain ⟨t, ht⟩ := tangent_line_normalised ν X₀ X₀' x hν0 hν1 hνx
    (tangent_line Γ W X₀ X₀' x hspan hx)
  have := tangent_coeff_zero H H₂ X₀ X₀' x t ht hsq h0 h1 hd
  rw [ht, this, zero_smul, add_zero]

/-- **Equality step, centred form** (`thm:fivecopy-family-equality`): `K` is a critical functional (`K X₀ = K X₀' = 0`)
that equals `(H − H X₀)²` at `x`; with `H X₀' ≠ 0` this forces `x = X₀`. -/
theorem equality_moment_centred (Γ : ∀ b, M →ₗ[ℝ] Matrix (Fin (n b)) (Fin (n b)) ℝ)
    (W : ∀ b, Matrix (Fin (n b)) (Fin (m b)) ℝ) (ν H K : M →ₗ[ℝ] ℝ) (X₀ X₀' x : M)
    (hspan : ∀ f : Module.Dual ℝ M, f X₀ = 0 → f X₀' = 0 →
      ∃ S : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℝ,
        ∀ y, f y = ∑ b, ((W b * S b * (W b)ᵀ) * Γ b y).trace)
    (hx : ∀ b, (W b)ᵀ * Γ b x * W b = 0)
    (hν0 : ν X₀ = 1) (hν1 : ν X₀' = 0) (hνx : ν x = 1)
    (hK : K x = (H x - H X₀) ^ 2) (hK0 : K X₀ = 0) (hK1 : K X₀' = 0)
    (hd : H X₀' ≠ 0) : x = X₀ := by
  obtain ⟨t, ht⟩ := tangent_line_normalised ν X₀ X₀' x hν0 hν1 hνx
    (tangent_line Γ W X₀ X₀' x hspan hx)
  have hK' : K x = 0 := by rw [ht, map_add, map_smul, hK0, hK1, smul_zero, add_zero]
  have hH : H x - H X₀ = t * H X₀' := by rw [ht, map_add, map_smul, smul_eq_mul]; ring
  rw [hK, hH] at hK'
  have ht0 : t = 0 := by
    rcases mul_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hK') with h | h
    · exact h
    · exact absurd h hd
  rw [ht, ht0, zero_smul, add_zero]

end

#print axioms equality_moment
#print axioms equality_moment_centred

end FormalResearch.FourQubitEntropy.SevenFiveCopy
