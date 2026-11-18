module

public import Mathlib

/-!
# Paper J, charts: the parabolic-cylinder (Weber) special-function hypotheses

Source: Paper J `charts.tex`: Section "The model ladders and their envelopes" (`lem:cha-weber-ladder`, `lem:cha-PCenv`,
`lem:cha-weber-env`, `lem:cha-W0`), `thmA.tex` (eq:tha-conn).  Proofs of the paper: DLMF 12.2, 12.8, Olver's uniform expansions
(`app_engine.tex`, `app:cha-PCenv`).

This file defines the envelope functions (`k2`, `Mbal`, `Ewell`, `Ebar`, `kappaBal`, `Molv`) concretely and collects, in one Prop-valued
structure `ParabolicCylinderFacts`, **all facts about the functions `U(a,z), V(a,z)` that Layers 2--3 use**.  Nothing in Mathlib
defines `U, V`; they are data of the structure (`pc.U`, `pc.V`).  Layer 4 supplies the instance: define `U, V` (DLMF 12.2) and prove
the fields.  A toy instance does not exist: every field concerns the actual parabolic-cylinder functions (the envelope and
connection fields fail for any other pair, since they pin down the Wronskian, the recurrences and the oscillation).

## Fields, with the statement each stands for and the Layer-4 result that discharges it

| field | statement | discharged by |
|---|---|---|
| `smooth`, `ode_U`, `ode_V`, `wronsk` | `U,V` entire, `y'' = (z^2/4 + a) y`, `Wr{U,V} = sqrt(2/pi)` | DLMF 12.2.2, 12.2.4, 12.2.10 |
| `shift_*` | the four `a`-shift relations (lem:cha-weber-ladder (2)) | DLMF 12.8.2, 12.8.3, 12.8.6, 12.8.7 |
| `reflect` | connection formula `U(a,-z) = -sin(pi a) U + cos(pi a) Gamma(1/2-a) V`, `a <= 0` (eq:tha-conn) | DLMF 12.2.15--16 |
| `env_well`, `env_bar`, `beyond` | `lem:cha-PCenv` (1b), (2), (3) | Olver 1997, Ch. 11 Thm 3.1, Ch. 6 Thm 2.2; Riccati comparison |
| `phase_osc` | oscillatory phase expansion of the Weber branch on `|t| <= 1 - eps` (lem:smo-bulkphase (1)) | DLMF 12.10.18 |

`phase_osc` is about the model functions only (no eigenvalue or eigenvector estimate).  The all-order phase expansion of the
comparison sequences (lem:smo-bulkphase (4), DLMF 12.10.35 + Stirling) is *not* a field here: it needs the chart data and is the field
`phase` of `BulkPhaseInputs` (`Charts/BulkWeber.lean`).

## Honest differences

* `reflect` is required for `a <= 0` only (the paper uses it there); for `a > 0` the connection data enter through `kappaBal` and `Ebar` only.
* the signs of `shift_V*` follow the DLMF as recalled (12.8.6: `V' - z V/2 - (a-1/2) V(a-1) = 0`; 12.8.7: `V' + z V/2 - V(a+1) = 0`);
  they must be re-checked against DLMF at the start of Layer 4 (item F-DLMF of `PLAN.md`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Set Real intervalIntegral

/-- `k_2(a,Z) = max(|Z^2/4 + a|, max(|a|,1)^{1/3})` (the two-sided Olver modulus scale, uniform through the Airy layer). -/
def k2 (a z : ℝ) : ℝ := max |z ^ 2 / 4 + a| (max |a| 1 ^ ((1 : ℝ) / 3))

/-- `M_bal(a,Z) = k_2^{-1/4}`. -/
def Mbal (a z : ℝ) : ℝ := (k2 a z) ^ (-(1 : ℝ) / 4)

/-- The well weight `E_well(a,Z)` (eq:cha-Ewell), `a <= 0`, `Z >= 0`: `1` up to the turning point `2 sqrt|a|`, then
`exp(-int_{2 sqrt|a|}^Z sqrt(t^2/4 - |a|) dt)`. -/
def Ewell (a z : ℝ) : ℝ :=
  if 2 * Real.sqrt |a| < z then Real.exp (-(∫ t in (2 * Real.sqrt |a|)..z, Real.sqrt (t ^ 2 / 4 - |a|))) else 1

/-- The barrier weight `E_bar(a,Z) = exp(-int_0^Z sqrt(t^2/4 + a) dt)`, `a > 0`. -/
def Ebar (a z : ℝ) : ℝ := Real.exp (-(∫ t in (0 : ℝ)..z, Real.sqrt (t ^ 2 / 4 + a)))

/-- The recessive weight `E(a,Z)`: `E_well(a,|Z|)` for `a <= 0` and `E_bar(a,Z)` for `a > 0` (`Z >= 0` side). -/
def Erec (a z : ℝ) : ℝ := if a ≤ 0 then Ewell a |z| else Ebar a z

/-- The balancing constant `kappa_bal(a)`: `Gamma(1/2 - a)^{-1/2}` for `a <= 0`, `(2 pi)^{-1/4} sqrt(Gamma(1/2 + a))` for `a > 0`. -/
def kappaBal (a : ℝ) : ℝ :=
  if a ≤ 0 then (Real.Gamma (1 / 2 - a)) ^ (-(1 : ℝ) / 2)
  else (2 * Real.pi) ^ (-(1 : ℝ) / 4) * Real.sqrt (Real.Gamma (1 / 2 + a))

/-- `U`-based balanced function `u~ = kappa_bal U` (`a <= 0`) / `u~_+` (`a > 0`) of lem:cha-PCenv. -/
def ut (U : ℝ → ℝ → ℝ) (a z : ℝ) : ℝ := kappaBal a * U a z

/-- `v~ = sqrt(pi/2) kappa_bal^{-1} V` (`a <= 0`). -/
def vt (V : ℝ → ℝ → ℝ) (a z : ℝ) : ℝ := Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * V a z

/-- The two-sided Olver modulus `M_Olv(a,Z)` (eq:cha-Molv), resonance-insensitive:
`E_U = sqrt(U^2 + U'^2/k_2)`, `E_V = sqrt(V^2 + V'^2/k_2)`; `M_Olv = E_U` for `Z >= 0` or `a > 0`, else
`sqrt(E_U^2 + Gamma(1/2-a)^2 E_V(|Z|)^2)`. -/
def Molv (U V : ℝ → ℝ → ℝ) (a z : ℝ) : ℝ :=
  let EU := fun w : ℝ => Real.sqrt (U a w ^ 2 + deriv (U a) w ^ 2 / k2 a w)
  let EV := fun w : ℝ => Real.sqrt (V a w ^ 2 + deriv (V a) w ^ 2 / k2 a w)
  if 0 ≤ z ∨ 0 < a then EU z
  else Real.sqrt (EU z ^ 2 + Real.Gamma (1 / 2 - a) ^ 2 * EV |z| ^ 2)

/-- **The special-function facts of Layers 2--3** (see the module docstring for the table).  `cPC, CPC` are the universal
constants of lem:cha-PCenv. -/
structure ParabolicCylinderFacts (U V : ℝ → ℝ → ℝ) (cPC CPC : ℝ) : Prop where
  cPC_pos : 0 < cPC
  cPC_le : cPC ≤ CPC
  smooth_U : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => U p.1 p.2)
  smooth_V : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => V p.1 p.2)
  ode_U : ∀ a z, deriv (deriv (U a)) z = (z ^ 2 / 4 + a) * U a z
  ode_V : ∀ a z, deriv (deriv (V a)) z = (z ^ 2 / 4 + a) * V a z
  wronsk : ∀ a z, U a z * deriv (V a) z - deriv (U a) z * V a z = Real.sqrt (2 / Real.pi)
  /-- DLMF 12.8.2. -/
  shift_U_up : ∀ a z, deriv (U a) z + z / 2 * U a z + (a + 1 / 2) * U (a + 1) z = 0
  /-- DLMF 12.8.3. -/
  shift_U_dn : ∀ a z, deriv (U a) z - z / 2 * U a z + U (a - 1) z = 0
  /-- DLMF 12.8.6 (sign convention to be rechecked). -/
  shift_V_dn : ∀ a z, deriv (V a) z - z / 2 * V a z - (a - 1 / 2) * V (a - 1) z = 0
  /-- DLMF 12.8.7. -/
  shift_V_up : ∀ a z, deriv (V a) z + z / 2 * V a z - V (a + 1) z = 0
  /-- DLMF 12.2.15--16 (eq:tha-conn): the connection formula, `a <= 0`. -/
  reflect : ∀ a ≤ 0, ∀ z, U a (-z) = -Real.sin (Real.pi * a) * U a z
      + Real.cos (Real.pi * a) * Real.Gamma (1 / 2 - a) * V a z
  /-- lem:cha-PCenv (1b), `a <= 0`, `Z >= 0`: `sqrt(u~^2 + u~'^2/k_2) <= C E_well M_bal` and the same for `v~` with `E_well^{-1}`. -/
  env_well : ∀ a ≤ 0, ∀ z, 0 ≤ z →
    Real.sqrt (ut U a z ^ 2 + (kappaBal a * deriv (U a) z) ^ 2 / k2 a z) ≤ CPC * Ewell a z * Mbal a z ∧
    Real.sqrt (vt V a z ^ 2 + (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (V a) z) ^ 2 / k2 a z)
      ≤ CPC * (Ewell a z)⁻¹ * Mbal a z
  /-- lem:cha-PCenv (2), `a > 0`: the pair `u~_+ = kappa_bal U(a,Z)`, `w~_+ = kappa_bal U(a,-Z)` (all `Z`). -/
  env_bar : ∀ a, 0 < a → ∀ z,
    Real.sqrt ((kappaBal a * U a z) ^ 2 + (kappaBal a * deriv (U a) z) ^ 2 / k2 a z) ≤ CPC * Ebar a z * Mbal a z ∧
    Real.sqrt ((kappaBal a * U a (-z)) ^ 2 + (kappaBal a * deriv (fun w => U a (-w)) z) ^ 2 / k2 a z)
      ≤ CPC * (Ebar a z)⁻¹ * Mbal a z
  /-- lem:cha-PCenv (3): beyond the turning point `Z >= 2 sqrt A`, `A = max(-a,0)`: `|U'| <= 4 k_2^{1/2} |U|` and
  `kappa_bal |U| >= c_3 E M_bal`, `c_3 = c_PC/sqrt 17`. -/
  beyond : ∀ a z, 2 * Real.sqrt (max (-a) 0) ≤ z →
    |deriv (U a) z| ≤ 4 * Real.sqrt (k2 a z) * |U a z| ∧
    cPC / Real.sqrt 17 * Erec a z * Mbal a z ≤ |kappaBal a * U a z|
  /-- the oscillatory phase expansion of the Weber branch (lem:smo-bulkphase (1), DLMF 12.10.18): for `t in [-1+eps, 1-eps]`,
  `mu^2 = 2n+1`, `U(-mu^2/2, mu t sqrt 2) = 2 g(mu)/(1-t^2)^{1/4} [cos(mu^2 eta(t) - pi/4) + O(mu^{-2})]`, `eta = (arccos t - t sqrt(1-t^2))/2`,
  with `g(mu) > 0` independent of `t`, uniformly on compacts. -/
  phase_osc : ∀ eps : ℝ, 0 < eps → eps < 1 → ∃ C μ0 : ℝ, ∃ g : ℝ → ℝ, (∀ μ, 0 < g μ) ∧ ∀ μ : ℝ, μ0 ≤ μ → ∀ t : ℝ,
    |t| ≤ 1 - eps →
      |U (-(μ ^ 2) / 2) (μ * t * Real.sqrt 2) - 2 * g μ / (1 - t ^ 2) ^ ((1 : ℝ) / 4)
        * Real.cos (μ ^ 2 * ((Real.arccos t - t * Real.sqrt (1 - t ^ 2)) / 2) - Real.pi / 4)|
        ≤ C * μ⁻¹ ^ 2 * (2 * g μ / (1 - t ^ 2) ^ ((1 : ℝ) / 4))

end FormalResearch.JacobiEigenvectors.Charts
