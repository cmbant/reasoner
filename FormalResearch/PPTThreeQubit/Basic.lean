module

public import Mathlib

/-!
# Three-qubit conventions for the rank-five fully-PPT family

Source: `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/family.tex`
(`eq:ppt3-vectors`, `eq:ppt3-curve`, `sec:ppt3-witness`) and
`fully_ppt_three_qubit_gme.tex` in the QIprojects repository.

Conventions.  A three-qubit vector is a function `Fin 8 → ℂ`; the basis vector `|abc⟩` has index
`4a + 2b + c` (qubit `A` is the most significant bit).  `ω = e^{2πi/3}` is the explicit complex
number `-1/2 + (√3/2) i`.  The vectors `u_s, v, w, e, o` of `eq:ppt3-vectors` are listed
coordinate-wise, `B_s = [u_s, v, w, e, o]` is the `8 × 5` matrix of their columns, and `q_s` is
the curve of `eq:ppt3-curve`.

A vector is a *cut-product* across a cut if it is a tensor product of a one-qubit vector on the
cut-off qubit and a two-qubit vector on the other two.  `IsBiseparable ρ` is the standard
finite-decomposition definition: `ρ` is a finite sum of rank-one operators `|φ⟩⟨φ|`, each `φ` a
cut-product across some cut (positive weights are absorbed in `φ`).  GME is its negation.
-/

@[expose] public section


namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-- The primitive cube root of unity `ω = e^{2πi/3} = -1/2 + (√3/2) i`. -/
def ω : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

private lemma sqrt3_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

/-- `ω² + ω + 1 = 0`. -/
theorem ω_sq_add_ω_add_one : ω ^ 2 + ω + 1 = 0 := by
  apply Complex.ext <;> simp [ω, sq] <;> nlinarith [sqrt3_mul_self]

/-- `ω³ = 1`. -/
theorem ω_cube : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * ω_sq_add_ω_add_one

/-- Complex conjugation sends `ω` to `ω²`. -/
theorem star_ω : star ω = ω ^ 2 := by
  have h : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  rw [h]
  exact Complex.ext (by norm_num [ω]) (by norm_num [ω])

/-- `ω ≠ ω²`, i.e. `ω² - ω ≠ 0`. -/
theorem ω_sq_sub_ne : ω ^ 2 - ω ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [ω, sq] at this
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith

/-- `|ω|² = 1`. -/
theorem normSq_ω : Complex.normSq ω = 1 := by
  simp [ω, Complex.normSq_apply]
  nlinarith [sqrt3_mul_self]

/-- `|ω²|² = 1`. -/
theorem normSq_ω_sq : Complex.normSq (ω ^ 2) = 1 := by
  rw [map_pow, normSq_ω]; simp

/-- The vector `u_s = |000⟩ - s(|011⟩ + |101⟩ + |110⟩)` of `eq:ppt3-vectors` (`s = 1` gives `u`). -/
def uVec (s : ℝ) : Fin 8 → ℂ := ![1, 0, 0, -s, 0, -s, -s, 0]

/-- `v = |111⟩`. -/
def vVec : Fin 8 → ℂ := ![0, 0, 0, 0, 0, 0, 0, 1]

/-- `w = |001⟩ + |010⟩ + |100⟩`. -/
def wVec : Fin 8 → ℂ := ![0, 1, 1, 0, 1, 0, 0, 0]

/-- `e = |011⟩ + ω|101⟩ + ω²|110⟩`. -/
def eVec : Fin 8 → ℂ := ![0, 0, 0, 1, 0, ω, ω ^ 2, 0]

/-- `o = |100⟩ + ω|010⟩ + ω²|001⟩`. -/
def oVec : Fin 8 → ℂ := ![0, ω ^ 2, ω, 0, 1, 0, 0, 0]

/-- The columns `(u_s, v, w, e, o)`. -/
def bCols (s : ℝ) : Fin 5 → Fin 8 → ℂ := ![uVec s, vVec, wVec, eVec, oVec]

/-- The `8 × 5` matrix `B_s = [u_s, v, w, e, o]` (`sec:ppt3-witness`). -/
def Bs (s : ℝ) : Matrix (Fin 8) (Fin 5) ℂ := Matrix.of fun i a => bCols s a i

/-- The curve `q_s(z)` of `eq:ppt3-curve`, in the coordinates `(u_s, v, w, e, o)`. -/
def qs (s : ℝ) (z : ℂ) : Fin 5 → ℂ :=
  ![2 * z, -(z ^ 2 * (z ^ 2 + 3 * s)), z ^ 2 - s, -(z * (z ^ 2 + s)), z ^ 2 + s]

/-- The diagonal of `H_s = diag(-12 s³, 1, 11 s², -6 s, 14 s²)` (`prop:ppt3-witness`(b)). -/
def hDiag (s : ℝ) : Fin 5 → ℝ := ![-12 * s ^ 3, 1, 11 * s ^ 2, -6 * s, 14 * s ^ 2]

/-- The witness matrix `H_s` of `prop:ppt3-witness`(b). -/
def Hs (s : ℝ) : Matrix (Fin 5) (Fin 5) ℂ := Matrix.diagonal fun a => (hDiag s a : ℂ)

/-- The real quadratic form `re(c† H_s c) = ∑ₐ h_a |c_a|²`. -/
def formH (s : ℝ) (c : Fin 5 → ℂ) : ℝ := ∑ a, hDiag s a * Complex.normSq (c a)

theorem formH_eq_re (s : ℝ) (c : Fin 5 → ℂ) :
    (star c ⬝ᵥ (Hs s *ᵥ c)).re = formH s c := by
  simp [Hs, formH, dotProduct, mulVec_diagonal, Complex.re_sum, Complex.normSq_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Product across the cut `A|BC`: `x(a,b,c) = α(a) μ(b,c)`. -/
def IsProdA (x : Fin 8 → ℂ) : Prop :=
  ∃ (α : Fin 2 → ℂ) (μ : Fin 4 → ℂ), ∀ i : Fin 8,
    x i = α ⟨i.val / 4, by omega⟩ * μ ⟨i.val % 4, by omega⟩

/-- Product across the cut `B|AC`: `x(a,b,c) = β(b) μ(a,c)`. -/
def IsProdB (x : Fin 8 → ℂ) : Prop :=
  ∃ (β : Fin 2 → ℂ) (μ : Fin 4 → ℂ), ∀ i : Fin 8,
    x i = β ⟨i.val / 2 % 2, by omega⟩ * μ ⟨2 * (i.val / 4) + i.val % 2, by omega⟩

/-- Product across the cut `C|AB`: `x(a,b,c) = γ(c) μ(a,b)`. -/
def IsProdC (x : Fin 8 → ℂ) : Prop :=
  ∃ (γ : Fin 2 → ℂ) (μ : Fin 4 → ℂ), ∀ i : Fin 8,
    x i = γ ⟨i.val % 2, by omega⟩ * μ ⟨i.val / 2, by omega⟩

/-- A vector which is a product across at least one of the three single-qubit cuts. -/
def IsCutProduct (x : Fin 8 → ℂ) : Prop := IsProdA x ∨ IsProdB x ∨ IsProdC x

/-- Biseparability of a three-qubit operator, in the standard finite-decomposition form: `ρ` is a
finite sum of rank-one operators `|φᵢ⟩⟨φᵢ|`, each `φᵢ` a cut-product across some cut (positive
weights absorbed into `φᵢ`). -/
def IsBiseparable (ρ : Matrix (Fin 8) (Fin 8) ℂ) : Prop :=
  ∃ (n : ℕ) (φ : Fin n → Fin 8 → ℂ), (∀ i, IsCutProduct (φ i)) ∧
    ρ = ∑ i, vecMulVec (φ i) (star (φ i))

/-- Genuine multipartite entanglement: not biseparable. -/
def IsGME (ρ : Matrix (Fin 8) (Fin 8) ℂ) : Prop := ¬ IsBiseparable ρ

end

end FormalResearch.PPTThreeQubit
