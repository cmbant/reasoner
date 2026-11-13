module

public import Mathlib

/-!
# Uniqueness of the affine `3j` midpoint: the exact algebraic core (Weyl P2, `prop:3junique`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `prop:3junique` and its proof.

The proposition re-centres `Ñ = N+δ`, `x̃ = (2μ+η)/Ñ` and asks that the continuum operator have no
generic `O(Ñ^{-1})` term.  The analytic step (expanding the discrete recurrence into a continuum
operator) is not formalised.  What the proof actually uses, and what is proved here exactly, is:

1. `affine_center_eq`: the canonical coordinate is `x = (ÑX-η)/(Ñ-δ) = (X-ηε)/(1-δε)`,
   `X = x̃`, `ε = 1/Ñ`; and `affX_expansion` gives its exact expansion
   `x = X + ε(δX-η) + ε² δ(δX-η)/(1-δε)`.
2. `wigner_principal_affine`: for the leading Wigner operator `(1-x²)∂_x² - 2x∂_x` the chain rule
   gives **exactly** (not only to first order) coefficients `A = (1-δε)² - (X-ηε)²` of `∂_X²` and
   `B = -2(X-ηε)` of `∂_X`; `principal_coeffs` expands them:
   `A = (1-X²) + ε(2Xη-2δ) + ε²(δ²-η²)`, `B = -2X + 2ηε`, which are the paper's `O(ε)`
   coefficients `2Xη-2δ` and `2η`.
3. `affine_midpoint_unique`: if the `O(ε)` zeroth-order coefficient `c(X) J_L + g(X)` (with `c`
   the multiplier of the whole equation, `J_L = L(L+1)`, and `g` independent of the rank) vanishes
   for all ranks, then `c = 0`; if then the principal `O(ε)` coefficient
   `2Xη - 2δ + c(X)(1-X²)` vanishes identically, `δ = η = 0`.  This is the logical content of the
   proof of `prop:3junique`, with the `O(ε)` coefficients as hypotheses (the paper's analytic
   identification of them is not re-derived here).  The converse (`affine_trivial`) is that for
   `δ = η = 0` the coefficients are unchanged.
-/

@[expose] public section

namespace FormalResearch.Racah

/-- The affine map `X ↦ x = (X-ηε)/(1-δε)` between the shifted and the canonical coordinate. -/
noncomputable def affX (δ η ε X : ℝ) : ℝ := (X - η * ε) / (1 - δ * ε)

/-- `x = 2μ/N = (ÑX-η)/(Ñ-δ)` for `Ñ = N+δ`, `X = (2μ+η)/Ñ`, `ε = 1/Ñ` (`eq:3jaffine`). -/
lemma affine_center_eq (N δ η μ : ℝ) (hN : N ≠ 0) (hÑ : N + δ ≠ 0) :
    2 * μ / N = affX δ η (1 / (N + δ)) ((2 * μ + η) / (N + δ)) := by
  unfold affX
  have h1 : 1 - δ * (1 / (N + δ)) = N / (N + δ) := by field_simp; ring
  rw [h1]
  field_simp
  ring

/-- Exact expansion of the affine change of variables:
`x = X + ε(δX-η) + ε² δ(δX-η)/(1-δε)`. -/
lemma affX_expansion (δ η ε X : ℝ) (h : 1 - δ * ε ≠ 0) :
    affX δ η ε X = X + ε * (δ * X - η) + ε ^ 2 * (δ * (δ * X - η) / (1 - δ * ε)) := by
  have e : X - η * ε = (1 - δ * ε) * (X + ε * (δ * X - η)) + δ * ε ^ 2 * (δ * X - η) := by ring
  unfold affX
  rw [e, add_div, mul_div_cancel_left₀ _ h]
  ring

/-- Coefficient of `∂_X²` after the change of variables. -/
def Acoef (δ η ε X : ℝ) : ℝ := (1 - δ * ε) ^ 2 - (X - η * ε) ^ 2

/-- Coefficient of `∂_X` after the change of variables. -/
def Bcoef (η ε X : ℝ) : ℝ := -2 * (X - η * ε)

/-- The `O(ε)` coefficients of the transformed Wigner operator: `2Xη-2δ` for `∂_X²` (and a
pure `ε²` remainder), `2η` for `∂_X`. -/
lemma principal_coeffs (δ η ε X : ℝ) :
    Acoef δ η ε X = (1 - X ^ 2) + ε * (2 * X * η - 2 * δ) + ε ^ 2 * (δ ^ 2 - η ^ 2) ∧
    Bcoef η ε X = -2 * X + ε * (2 * η) := by
  exact ⟨by unfold Acoef; ring, by unfold Bcoef; ring⟩

/-- With `δ = η = 0` the coefficients are those of the untransformed Wigner operator. -/
lemma affine_trivial (ε X : ℝ) : Acoef 0 0 ε X = 1 - X ^ 2 ∧ Bcoef 0 ε X = -2 * X := by
  exact ⟨by unfold Acoef; ring, by unfold Bcoef; ring⟩

/-- **Chain rule for the leading Wigner operator.**  For `f` twice differentiable
(`f' = f'`, `f'' = (f')'`) and `φ(X) = (X-ηε)/(1-δε)`, `g = f ∘ φ`:
`g' = a f'(φ)`, `g'' = a² f''(φ)` with `a = 1/(1-δε)`, and
`(1-φ²) f''(φ) - 2φ f'(φ) = A g'' + B g'` with the exact coefficients `A, B` above. -/
theorem wigner_principal_affine (δ η ε : ℝ) (h : 1 - δ * ε ≠ 0) (f f' f'' : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y) (X : ℝ) :
    HasDerivAt (fun Y => f (affX δ η ε Y)) (1 / (1 - δ * ε) * f' (affX δ η ε X)) X ∧
    HasDerivAt (fun Y => 1 / (1 - δ * ε) * f' (affX δ η ε Y))
      ((1 / (1 - δ * ε)) ^ 2 * f'' (affX δ η ε X)) X ∧
    (1 - affX δ η ε X ^ 2) * f'' (affX δ η ε X) - 2 * affX δ η ε X * f' (affX δ η ε X) =
      Acoef δ η ε X * ((1 / (1 - δ * ε)) ^ 2 * f'' (affX δ η ε X))
        + Bcoef η ε X * (1 / (1 - δ * ε) * f' (affX δ η ε X)) := by
  have hφ : HasDerivAt (affX δ η ε) (1 / (1 - δ * ε)) X := by
    have := ((hasDerivAt_id X).sub_const (η * ε)).div_const (1 - δ * ε)
    exact this
  refine ⟨?_, ?_, ?_⟩
  · have := (hf (affX δ η ε X)).comp X hφ
    rw [mul_comm] at this
    exact this
  · have := ((hf' (affX δ η ε X)).comp X hφ).const_mul (1 / (1 - δ * ε))
    have e : (1 / (1 - δ * ε)) * (f'' (affX δ η ε X) * (1 / (1 - δ * ε))) =
        (1 / (1 - δ * ε)) ^ 2 * f'' (affX δ η ε X) := by ring
    rw [e] at this
    exact this
  · have hX : X - η * ε = affX δ η ε X * (1 - δ * ε) := by
      unfold affX; rw [div_mul_cancel₀ _ h]
    unfold Acoef Bcoef
    rw [hX]
    generalize affX δ η ε X = φ
    generalize f'' φ = u
    generalize f' φ = v
    field_simp
    ring

/-- **Algebraic core of `prop:3junique`.**  Let `c(X)` be the `O(ε)` multiplier of the whole
equation and `g₀(X)` the rank-independent part of the `O(ε)` zeroth-order coefficient, so that
the zeroth-order `O(ε)` coefficient at rank `L` is `c(X) L(L+1) + g₀(X)`; and let the principal
`O(ε)` coefficient be `2Xη - 2δ + c(X)(1-X²)`.  If both vanish identically (no generic `O(ε)`
term at fixed `X`), then `c ≡ 0`, `δ = 0` and `η = 0`. -/
theorem affine_midpoint_unique (δ η : ℝ) (c g₀ : ℝ → ℝ)
    (hrank : ∀ (X : ℝ) (L : ℕ), c X * ((L : ℝ) * (L + 1)) + g₀ X = 0)
    (hprin : ∀ X : ℝ, 2 * X * η - 2 * δ + c X * (1 - X ^ 2) = 0) :
    (∀ X, c X = 0) ∧ δ = 0 ∧ η = 0 := by
  have hc : ∀ X, c X = 0 := by
    intro X
    have h0 := hrank X 0
    have h1 := hrank X 1
    simp at h0 h1
    linarith
  have hp : ∀ X : ℝ, 2 * X * η - 2 * δ = 0 := by
    intro X; have := hprin X; rw [hc X] at this; linarith
  have h0 := hp 0
  have h1 := hp 1
  refine ⟨hc, ?_, ?_⟩ <;> linarith

/-- Conversely `δ = η = 0` (with `c = g₀ = 0`) satisfies the hypotheses: the Regge midpoint
`N = j_-+j_++1`, `x = 2μ/N` has no `O(ε)` term in the affine class. -/
theorem affine_midpoint_trivial (X : ℝ) (L : ℕ) :
    (0 : ℝ) * ((L : ℝ) * (L + 1)) + 0 = 0 ∧ 2 * X * 0 - 2 * 0 + 0 * (1 - X ^ 2) = 0 := by
  constructor <;> ring

/-- info: 'FormalResearch.Racah.affine_midpoint_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms affine_midpoint_unique

/-- info: 'FormalResearch.Racah.wigner_principal_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wigner_principal_affine

/-- info: 'FormalResearch.Racah.affine_center_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms affine_center_eq

end FormalResearch.Racah
