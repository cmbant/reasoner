module

public import FormalResearch.ModularBootstrap.FiveTerm.UpperSmoothEnv
public import FormalResearch.ModularBootstrap.FiveTerm.UpperDetuning
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroDatum

/-!
# FIVE-S: strip structure of the Virasoro outer function (statements)

Work package FIVE-S of Paper II (`CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`): the shared input
of `cts:smooth-env` (2)-(3) (FIVE-U) and of `cts:cauchy-dual` Step 2 (FIVE-L).  This module only *states* the
four targets as `Prop`s over the existing `Gout` (`VirasoroOuter`); the proofs live in the other `Outer*` modules
(see `FIVES_DESIGN.md` for the status table).

* `OuterS1` (`cts:main` Piece 3 and `cts:cauchy-dual` Step 2, factorisation `G_outer = (1+z²)⁻¹ H₃^{1/4} G̃`):
  the continuous branch `θ_out` of `arg G_outer(iy)`, the function `H₃`, and `G̃`.
* `OuterS2` (`cts:cauchy-dual` Step 2, eq. `cts:theta-deriv`, and the first bullet of `cts:smooth-env` (3)):
  `|∂_x^j θ_out(y(x))| ≤ C min(r,1)^{1/2-j} e^{-πx}`, `r = x - ξ_*`, `j = 1, 2`.
* `OuterS3` (`cts:smooth-env` (2)): the extension of `ℰ_δ` and the branch-point factorisation.
* `OuterS4` (`cts:smooth-env` (3)): `OuterS4a` (the `δφ_δ'`, `δφ_δ''` bounds) and `OuterS4b` (the `C²` bounds on `ΔΦ_δ`).

**Paper findings built into the statements** (see `FIVES_DESIGN.md`): the bound `min(r^{1/2-j}, (1+x)e^{-πx})` of the
paper cannot hold at the tip (`θ_out(y(x)) = g₁ y(x) + …`, `y(x) ≍ r^{1/2}`, so `∂_x θ_out ≍ r^{-1/2}` while
`(1+x)e^{-πx}` is bounded) nor for `j = 0` at infinity (`θ_out(y(x)) → -π/4`, numerically), so `OuterS2` states the
combined bound `C min(r,1)^{1/2-j} e^{-πx}` (`r^{1/2-j}` at the tip, `e^{-πx}` at infinity; the literal `r^{1/2-j} e^{-πx}`
would be false at infinity because `r^{-1/2} → 0`) and, for `j = 0`, `|θ_out| ≤ C r^{1/2}` and the exponential approach to a
limit.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-! ### Coordinates -/

/-- `y(x) = √((cosh πx - √2)/(cosh πx + √2))`: the point `z = i y(x)` of the slit with `Re b = x`. -/
noncomputable def yOfX (x : ℝ) : ℝ := √((Real.cosh (π * x) - √2) / (Real.cosh (π * x) + √2))

/-- `τ(x) = (2/π) arccosh(cosh(πx)/√2)`: the strip height with `tanh(πτ/4) = y(x)` (`x ≥ ξ_*`). -/
noncomputable def tauOfX (x : ℝ) : ℝ := (2 / π) * Real.arcosh (Real.cosh (π * x) / √2)

/-- The continuous branch of `arg G_outer(iτ-point)` in the strip variable: with `y = tanh(πτ/4)`,
`θ_out = Im h̄_a(iτ) - (5/2) arctan y + (1/4) arctan(2 v_x)` (the arguments of the explicit factors
`(1-z)^{1/2}(1+z)^{-2}` and `Ŝ^{-1/4}` of `Gout`; `vT` is the odd extension of `v_x`). -/
noncomputable def thetaOutT (τ : ℝ) : ℝ :=
  (hbarA aAmp ((τ : ℂ) * Complex.I)).im - (5 / 2) * Real.arctan (Real.tanh (π * τ / 4)) +
    (1 / 4) * Real.arctan (2 * vT τ)

/-- `θ_out(y)`, `y ∈ (-1, 1)` (`θ_out(y) = arg G_outer(iy)`, continuous, odd, `θ_out(0) = 0`). -/
noncomputable def thetaOut (y : ℝ) : ℝ := thetaOutT ((4 / π) * Real.artanh y)

/-- `x ↦ θ_out(y(x))` for `x ≥ ξ_*`. -/
noncomputable def thetaOutX (x : ℝ) : ℝ := thetaOutT (tauOfX x)

/-! ### `H₃` and `G̃` -/

/-- `H₃(z) = (1 + sin πs) S(cos πs)²/(π² ξ_*²)` with `s = (4/π) arctan z`, `cos πs = u(z)`, `S = sInt`.
This is the paper's `H₃ = -i (b²/ξ_*²)(ζ+i)/(ζ-i)` (`b² = u S(u)²/π²`, `ζ = e^{iπs}`, and
`u/(ζ - i) = e^{-iπs}(ζ + i)/2`), written without the removable pole. -/
noncomputable def H3 (z : ℂ) : ℂ :=
  (1 + Complex.sin (π * sInv z)) * sInt (uC z) ^ 2 / ((π : ℂ) ^ 2 * (xiStar : ℂ) ^ 2)

/-- `G̃ = (1+z²) G_outer / H₃^{1/4}` for a chosen fourth root `R4` of `H₃`. -/
noncomputable def Gtilde (R4 : ℂ → ℂ) (z : ℂ) : ℂ := (1 + z ^ 2) * Gout z / R4 z

/-- `Ũ₀ = -(3/2) log 2 - 2 log(1 - e^{-4πξ_*})`. -/
noncomputable def Utilde0 : ℝ := -(3 / 2) * Real.log 2 - 2 * Real.log (1 - Real.exp (-(4 * π * xiStar)))

/-- **`OuterS1`** (`cts:main` Piece 3; `cts:cauchy-dual` Step 2): bridge to `Gout` and the factorisation
`G_outer = (1+z²)⁻¹ H₃^{1/4} G̃`.

1. (bridge) `G_outer(iy) = W_slit(y) e^{iθ_out(y)}` on `(0,1)`, and `θ_out` is odd, continuous on `(-1,1)`,
   vanishes at `0`;
2. `H₃` is holomorphic and zero-free on `Ω`, `H₃(0) = 1`, positive on `(0,1)`, `|H₃(iy)| = (x(y)/ξ_*)²`
   (`xOf`), and has a holomorphic fourth root `R4` on `Ω`, positive on `(0,1)`;
3. `G̃ = (1+z²) G_outer/R4` is holomorphic and zero-free on `Ω`, and on the slit
   `log|G̃(iy)| = Ũ₀ + 2 log(1+ρ) - ½ log(1+ρ⁴) + 2 log(1 - e^{-4π x(y)})`, `ρ = (1-y)/(1+y)`
   (`Ũ(u) - Ũ₀` of `cts:cauchy-dual` Step 2 at `u = ρ²`). -/
def OuterS1 : Prop :=
  (∀ y ∈ Ioo (0 : ℝ) 1, Gout (Complex.I * (y : ℂ)) = (Wslit y : ℂ) * Complex.exp (Complex.I * (thetaOut y : ℂ))) ∧
  thetaOut 0 = 0 ∧ (∀ y, thetaOut (-y) = -thetaOut y) ∧ ContinuousOn thetaOut (Ioo (-1 : ℝ) 1) ∧
  DifferentiableOn ℂ H3 halfDisc ∧ (∀ z ∈ halfDisc, H3 z ≠ 0) ∧ H3 0 = 1 ∧
  (∀ r ∈ Ioo (0 : ℝ) 1, 0 < (H3 (r : ℂ)).re ∧ (H3 (r : ℂ)).im = 0) ∧
  (∀ y ∈ Ioo (0 : ℝ) 1, ‖H3 (Complex.I * (y : ℂ))‖ = (xOf y / xiStar) ^ 2) ∧
  ∃ R4 : ℂ → ℂ, DifferentiableOn ℂ R4 halfDisc ∧ (∀ z ∈ halfDisc, R4 z ^ 4 = H3 z) ∧
    (∀ r ∈ Ioo (0 : ℝ) 1, 0 < (R4 (r : ℂ)).re ∧ (R4 (r : ℂ)).im = 0) ∧
    DifferentiableOn ℂ (Gtilde R4) halfDisc ∧ (∀ z ∈ halfDisc, Gtilde R4 z ≠ 0) ∧
    ∀ y ∈ Ioo (0 : ℝ) 1,
      Real.log ‖Gtilde R4 (Complex.I * (y : ℂ))‖ =
        Utilde0 + 2 * Real.log (1 + (1 - y) / (1 + y)) - (1 / 2) * Real.log (1 + ((1 - y) / (1 + y)) ^ 4) +
          2 * Real.log (1 - Real.exp (-(4 * π * xOf y)))

/-- **`OuterS2`** (`cts:cauchy-dual` Step 2, eq. `cts:theta-deriv`; `cts:smooth-env` (3), first bullet):
there is `C` such that, with `r = x - ξ_*` and `r̃ = min(r, 1)`, `θ_out(y(x))` is twice differentiable on `x > ξ_*`
and for all `x > ξ_*`: `|θ_out(y(x))| ≤ C r^{1/2}` (`x ≤ ξ_* + 1`), `|∂_x θ_out(y(x))| ≤ C r̃^{-1/2} e^{-πx}`,
`|∂_x² θ_out(y(x))| ≤ C r̃^{-3/2} e^{-πx}`, and `θ_out(y(x))` has a limit `L` with `|θ_out(y(x)) - L| ≤ C e^{-πx}`.
(The paper's `C min(r^{1/2-j}, (1+x)e^{-πx})` is read as this combined bound: `r̃^{1/2-j}` is `r^{1/2-j}` at the tip and `1`
at infinity; see the module docstring.) -/
def OuterS2 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    (∀ x : ℝ, xiStar < x → x ≤ xiStar + 1 → |thetaOutX x| ≤ C * (x - xiStar) ^ ((1 : ℝ) / 2)) ∧
    (∀ x : ℝ, xiStar < x → DifferentiableAt ℝ thetaOutX x ∧ DifferentiableAt ℝ (deriv thetaOutX) x) ∧
    (∀ x : ℝ, xiStar < x →
      |deriv thetaOutX x| ≤ C * (min (x - xiStar) 1) ^ (-(1 : ℝ) / 2) * Real.exp (-(π * x))) ∧
    (∀ x : ℝ, xiStar < x →
      |deriv (deriv thetaOutX) x| ≤ C * (min (x - xiStar) 1) ^ (-(3 : ℝ) / 2) * Real.exp (-(π * x))) ∧
    ∃ L : ℝ, ∀ x : ℝ, xiStar < x → |thetaOutX x - L| ≤ C * Real.exp (-(π * x))

/-! ### The strip objects of `cts:smooth-env` -/

/-- `ζ_D(b) = √((√2 - cosh πb)/(√2 + cosh πb))` (`cts:unfold`). -/
noncomputable def zetaD (b : ℂ) : ℂ :=
  ((√2 - Complex.cosh (π * b)) / (√2 + Complex.cosh (π * b))) ^ (1 / 2 : ℂ)

/-- The slit phase `δφ_δ(x) = arg F_δ(iy(x)) = -θ_out(y(x)) + arg m_δ(iy(x))`, with
`arg m_δ(iy) = ½(arctan((1-δ)y) - arctan y)`. -/
noncomputable def dphi (δ x : ℝ) : ℝ :=
  -thetaOutX x + (1 / 2) * (Real.arctan ((1 - δ) * yOfX x) - Real.arctan (yOfX x))

/-- `φ_y'(b) = π (1/sinh π(b-y) + 1/sinh π(b+y))`, the derivative of `φ_y = log(-T_y)`,
`T_y(b) = tanh(π(b-y)/2) tanh(π(b+y)/2)`. -/
noncomputable def phiYDeriv (y : ℝ) (b : ℂ) : ℂ :=
  π * (1 / Complex.sinh (π * (b - y)) + 1 / Complex.sinh (π * (b + y)))

/-- The holomorphic branch `φ_y(b) = log(-T_y(b))` on the strip `0 < Im b < 1` with `φ_y(i/2) = 0`
(straight-line primitive of `phiYDeriv`). -/
noncomputable def phiY (y : ℝ) (b : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, phiYDeriv y (Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2)) * (b - Complex.I / 2)

/-- `ΔΦ_δ(b) = (1/π) ∫_{ξ_*}^∞ δφ_δ'(y) log(-T_y(b)) dy`. -/
noncomputable def DeltaPhi (δ : ℝ) (b : ℂ) : ℂ :=
  (1 / (π : ℂ)) * ∫ y in Ioi xiStar, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b

/-- `ℰ_δ(b) = F_δ(ζ_D(b)) e^{-ΔΦ_δ(b)}`, the stripped envelope. -/
noncomputable def Estripped (δ : ℝ) (b : ℂ) : ℂ := fDelta Gout δ (zetaD b) * Complex.exp (-DeltaPhi δ b)

/-- `η_δ ∈ (0,1/2)`: `sin(πη_δ) = √2 (2δ - δ²)/(2 - 2δ + δ²)`. -/
noncomputable def etaDelta (δ : ℝ) : ℝ := Real.arcsin (√2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2)) / π

/-- The band `{|Im b - 1/2| < ε}` around `E_+`. -/
def bandUpper (ε : ℝ) : Set ℂ := {b : ℂ | |b.im - 1 / 2| < ε}

/-- **`OuterS3`** (`cts:smooth-env` (2)): there are `δ₀ ∈ (0,1/4)` with `η_{δ₀} < 1/16` and `C` such that for
`δ ∈ (0, δ₀)`:

* `ℰ_δ` agrees on `D_* ∩ {0 < Im b}` (where `ℰ_δ` is defined by `Estripped`) with an even zero-free holomorphic
  `Ee` on `{|Im b| < 1/2 + η_δ}`, strictly positive on `ℝ`;
* on `{|Im b - 1/2| < 1/16}`, `Ee(b) = (1 - (1-δ) ζ_D(b))^{-1/2} Esm(b)` with `Esm` holomorphic and zero-free,
  `C⁻¹ (1+|Re b|)^{-1/2} e^{-2π|Re b|} ≤ |Esm(b)| ≤ C (1+|Re b|)^{-1/2} e^{-2π|Re b|}`,
  `|(log Esm)'| + |(log Esm)''| ≤ C`;
* on `{|Im b| ≤ 1/2 + η_δ/2}`, `|Ee(b)| ≤ C (min(1, |b - i/2|, |b + i/2|) + δ)^{-1/2} (1+|Re b|)^{-1/2} e^{-2π|Re b|}`;
* the boundary identities `Ee(x) e^{Re ΔΦ_δ(x)} = |F_δ(iy(x))|` for `x ≥ ξ_*` (and `|Ee(v_x + i/2)| = |F_δ(e^{-iψ(x)})|`,
  with `e^{-iψ(x)} = conj (wPt y(x))`, `v_x = vOf y(x)`) for `x > ξ_*`. -/
def OuterS3 : Prop :=
  ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 < 1 / 4 ∧ etaDelta δ0 < 1 / 16 ∧ ∃ C : ℝ, 0 < C ∧
    ∀ δ : ℝ, 0 < δ → δ < δ0 →
      ∃ Ee Esm : ℂ → ℂ,
        DifferentiableOn ℂ Ee {b : ℂ | |b.im| < 1 / 2 + etaDelta δ} ∧
        (∀ b : ℂ, |b.im| < 1 / 2 + etaDelta δ → Ee b ≠ 0) ∧
        (∀ b : ℂ, Ee (-b) = Ee b) ∧ (∀ x : ℝ, 0 < (Ee (x : ℂ)).re ∧ (Ee (x : ℂ)).im = 0) ∧
        (∀ b : ℂ, 0 < b.im → |b.im| < 1 / 2 → ¬ (b.im = 0 ∧ xiStar ≤ |b.re|) → Ee b = Estripped δ b) ∧
        DifferentiableOn ℂ Esm (bandUpper (1 / 16)) ∧ (∀ b ∈ bandUpper (1 / 16), Esm b ≠ 0) ∧
        (∀ b ∈ bandUpper (1 / 16), Ee b = (1 - ((1 - δ : ℝ) : ℂ) * zetaD b) ^ (-(1 / 2 : ℂ)) * Esm b) ∧
        (∀ b ∈ bandUpper (1 / 16),
          C⁻¹ * ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) ≤ ‖Esm b‖ ∧
          ‖Esm b‖ ≤ C * ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|)))) ∧
        (∀ b ∈ bandUpper (1 / 16),
          ‖logDeriv Esm b‖ + ‖deriv (logDeriv Esm) b‖ ≤ C) ∧
        (∀ b : ℂ, |b.im| ≤ 1 / 2 + etaDelta δ / 2 →
          ‖Ee b‖ ≤ C * (min 1 (min ‖b - Complex.I / 2‖ ‖b + Complex.I / 2‖) + δ) ^ (-(1 : ℝ) / 2) *
            ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|)))) ∧
        (∀ x : ℝ, xiStar ≤ x →
          ‖Ee (x : ℂ)‖ * Real.exp (DeltaPhi δ (x : ℂ)).re = ‖fDelta Gout δ (Complex.I * (yOfX x : ℂ))‖) ∧
        (∀ x : ℝ, xiStar < x →
          ‖Ee ((vOf (yOfX x) : ℂ) + Complex.I / 2)‖ =
            ‖fDelta Gout δ (starRingEnd ℂ (wPt (yOfX x)))‖)

/-- **`OuterS4a`** (`cts:smooth-env` (3), phase bounds): there is `C` such that for `δ ∈ (0, 1/4)`, `x > ξ_*`,
`r̃ = min(x - ξ_*, 1)`: `|δφ_δ'(x)| ≤ C r̃^{-1/2} e^{-πx}` and `|δφ_δ''(x)| ≤ C r̃^{-3/2} e^{-πx}`.
(The paper's `r^{-1/2} e^{-πx}`, `r^{-3/2} e^{-πx}` with `r = x - ξ_*` cannot hold for large `x`: at infinity
`δφ_δ' ≍ e^{-πx}` with a `δ`-dependent nonzero constant coming from `½ (arctan((1-δ)y) - arctan y)'`, while `r^{-1/2} → 0`.) -/
def OuterS4a : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 4 → ∀ x : ℝ, xiStar < x →
    |deriv (dphi δ) x| ≤ C * (min (x - xiStar) 1) ^ (-(1 : ℝ) / 2) * Real.exp (-(π * x)) ∧
    |deriv (deriv (dphi δ)) x| ≤ C * (min (x - xiStar) 1) ^ (-(3 : ℝ) / 2) * Real.exp (-(π * x))

/-- **`OuterS4b`** (`cts:smooth-env` (3), potential): there are `δ₀` (as in `OuterS3`) and `C` such that for
`δ ∈ (0, δ₀)`, `ΔΦ_δ` is holomorphic on `{|Im b - 1/2| < 1/4}` with `Re ΔΦ_δ = 0` on `E_+` and
`|∂_b^j ΔΦ_δ| ≤ C`, `j = 0, 1, 2` (on the open band; the closed-band bounds follow by continuity). -/
def OuterS4b : Prop :=
  ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 < 1 / 4 ∧ etaDelta δ0 < 1 / 16 ∧ ∃ C : ℝ, 0 < C ∧
    ∀ δ : ℝ, 0 < δ → δ < δ0 →
      DifferentiableOn ℂ (DeltaPhi δ) (bandUpper (1 / 4)) ∧
      (∀ v : ℝ, (DeltaPhi δ ((v : ℂ) + Complex.I / 2)).re = 0) ∧
      (∀ b ∈ bandUpper (1 / 4),
        ‖DeltaPhi δ b‖ ≤ C ∧ ‖deriv (DeltaPhi δ) b‖ ≤ C ∧ ‖deriv (deriv (DeltaPhi δ)) b‖ ≤ C)

/-- **`OuterS4`** (`cts:smooth-env` (3), phase and potential): `OuterS4a ∧ OuterS4b`. -/
def OuterS4 : Prop := OuterS4a ∧ OuterS4b

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
