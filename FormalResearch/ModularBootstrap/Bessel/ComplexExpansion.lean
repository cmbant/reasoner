module

public import FormalResearch.ModularBootstrap.Bessel.VAsymptotic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Lemma B (c), complex-neighbourhood statement: isolated as a named hypothesis

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma B (`vlo:Bessel`), part (c), second
and third sentences: for every compact `I ⊂ (0,∞)` the expansion
`V(c'b²/3) = as(c'L(b)) [(1 - e^{-4πb})² + O_I(c'^{-1})]` holds holomorphically and uniformly on a
small fixed complex neighbourhood of `I` (principal square root), and Cauchy's estimate gives the
same `O_I(c'^{-1})` bound for every fixed `b`-derivative of the bracket error on `I`.

**This is not proved here.**  The real-`x` case (`Bessel.besselV_asymptotic`) is proved with explicit
constants.  The complex statement needs the complex Laplace asymptotic of `I₀` in a closed sector
`|arg z| ≤ π/2 - ε` plus Cauchy derivative estimates, neither of which is formalised.  It is stated
as the Prop `BesselComplexExpansion I` so that downstream results can take it as an explicit
hypothesis; nothing is assumed globally.  No theorem of this repository depends on it, and its non-vacuity
is exactly the (open here) truth of the paper statement; the `n = 0`, real-`b` shadow of the statement
is the proved `besselV_asymptotic`.
-/

@[expose] public section

open Complex

namespace FormalResearch.ModularBootstrap.Bessel

/-- `V(t) = Σ_k v_k t^k` for complex `t` (entire; `v_k = besselVCoeff a k`). -/
noncomputable def besselVC (a : ℝ) (t : ℂ) : ℂ := ∑' k : ℕ, (besselVCoeff a k : ℂ) * t ^ k

/-- `as(z) = e^z/√(2πz)` with the principal square root. -/
noncomputable def besselAsC (z : ℂ) : ℂ := cexp z / (2 * (Real.pi : ℂ) * z) ^ (1 / 2 : ℂ)

/-- The bracket error `E_{c'}(b) = V(c'b²/3)/as(c'L(b)) - (1 - e^{-4πb})²` (complex `b`). -/
noncomputable def besselErrC (c' : ℝ) (b : ℂ) : ℂ :=
  besselVC (c' / 12) ((c' : ℂ) * b ^ 2 / 3) / besselAsC ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3)) -
    (1 - cexp (-(4 * (Real.pi : ℂ) * b))) ^ 2

/-- **Hypothesis (paper, Lemma B (c), complex part), not proved.** For a compact `I ⊂ (0,∞)`
there are `δ, C, c₀` such that for `c' ≥ c₀` the bracket error is `≤ C/c'` on the
`δ`-neighbourhood of `I`, and for each `n` there is `C_n` with
`|∂_b^n E_{c'}| ≤ C_n/c'` on `I`. -/
def BesselComplexExpansion (I : Set ℝ) : Prop :=
  IsCompact I → I ⊆ Set.Ioi 0 →
  ∃ δ : ℝ, 0 < δ ∧ ∃ C c₀ : ℝ,
    (∀ c' : ℝ, c₀ ≤ c' → ∀ b : ℂ, (∃ x ∈ I, ‖b - (x : ℂ)‖ < δ) → ‖besselErrC c' b‖ ≤ C / c') ∧
    ∀ n : ℕ, ∃ Cn : ℝ, ∀ c' : ℝ, c₀ ≤ c' → ∀ x ∈ I,
      ‖iteratedDeriv n (besselErrC c') (x : ℂ)‖ ≤ Cn / c'

end FormalResearch.ModularBootstrap.Bessel
