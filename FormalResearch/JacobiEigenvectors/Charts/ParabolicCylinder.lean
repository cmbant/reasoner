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
| `reflect`, `reflect_V` | connection formula `U(a,-z) = -sin(pi a) U + cos(pi a) Gamma(1/2-a) V`, and its companion `V(a,-z) = cos(pi a)/Gamma(1/2-a) U + sin(pi a) V`, `a <= 0` (eq:tha-conn, `M_-(a)` of lem:cha-PCenv (1a)) | DLMF 12.2.15--16 with 12.2.7 |
| `env_well`, `env_bar`, `beyond` | `lem:cha-PCenv` (1b), (2), (3) | Olver 1997, Ch. 11 Thm 3.1, Ch. 6 Thm 2.2; Riccati comparison |
| `molv_well`, `molv_bar` | `eq:cha-MolvEquiv`, `eq:cha-envbar` (the two-sided equivalence of `M_Olv` with `kappa^{-1} W M_bal`; lower bound inside the well) | Olver, as `env_well`; **added in round 3** (finding F-W2-6) |
| `V_growth` | the growing solution `V` is positive and `V'/V >= c_V k_2^{1/2}` beyond the turning point (the forward ratio `r_2 = e^{-theta}(1+O(h)) < 1` of the dominant member, app_thmA Step 3 (ii)) | Riccati comparison / Olver; **added in round 3** (finding F-W2-6) |
| `phase_osc` | oscillatory phase expansion of the Weber branch on `|t| <= 1 - eps` (lem:smo-bulkphase (1)) | DLMF 12.10.18 |

`phase_osc` is about the model functions only (no eigenvalue or eigenvector estimate).  The all-order phase expansion of the
comparison sequences (lem:smo-bulkphase (4), DLMF 12.10.35 + Stirling) is *not* a field here: it needs the chart data and is the field
`phase` of `BulkPhaseInputs` (`Charts/BulkWeber.lean`).

## Round 3 additions (finding F-W2-6; `Charts/SoftParabolicCylinder.lean`, `TheoremA/SoftProof.lean`)

`reflect_V`, `molv_well`, `molv_bar`, `V_growth` were added because the corrected soft-edge chain (three patches for `a <= 0`, swapped pair `(v~, -u~)` after `Z = 0`) and the conversion
of the engine bound to the paper's `lambda_L M_Olv(a,-Z)` need them and they follow from no other field.  All four are classical facts about `U, V` (no eigenvalue or eigenvector content) and were
checked numerically with mpmath 1.3.0 (scratch, not committed; `V(a,z) := Gamma(1/2+a)/pi (sin(pi a) U(a,z) + U(a,-z))`):
`reflect_V` to `2e-31` (`a in {0, -0.25, -0.3, -1.7, -2.2, -5.37}`, `z in {-1.3, 0, 0.7, 2.1}`); `molv_well`: `M_Olv kappa / (W_well M_bal) in [0.63, 1.74]` (`a in {-0.01, ..., -15.3}` incl. `a = -n - 1/2 + 10^{-5}` near resonance, `z in [-12, 12]`),
so `c_PC <= 0.63`, `C_PC >= 1.74` (compatible with `cPC_le` and the audit values above: `c_PC <= 1.7` is replaced by `c_PC <= 0.63`); `molv_bar`: ratio `in [0.89, 1.19]`; `V_growth`: `V > 0` and `V'/(V k_2^{1/2}) in [0.095, 1.003]` on `z >= 2 sqrt(max(-a,0))` (`a in {-20.3, ..., 30}`),
so `c_V = 0.09` works.  The *absorption* `Lambda h^{-m} (E_{j_1}/E_n)^2 <= e^{-c/h}` is **not** a field: it follows from the chart fields (`zeta_deriv`, `zeta_far`, `muS_bd`) and the definition of `Ewell` (an integral of an explicit function).

## Honest differences

* `reflect` is required for `a <= 0` only (the paper uses it there); for `a > 0` the connection data enter through `kappaBal` and `Ebar` only.
* the shift relations `shift_V*` are DLMF 12.8.6 (`V' - z V/2 - (a-1/2) V(a-1) = 0`) and 12.8.7 (`V' + z V/2 - V(a+1) = 0`).

## Round 2 audit (soundness and non-vacuity; finding F-DLMF closed)

`U, V` cannot be instantiated in Lean (no definition in Mathlib), so the fields were checked **numerically against the classical functions**
(mpmath 1.3.0 `pcfu`, with `V(a,z) := (1/pi) Gamma(1/2 + a) [sin(pi a) U(a,z) + U(a,-z)]`, DLMF 12.2.7; 30 digits, `a in {0.3, -1.7, 2.2, -0.25}`, `z in {-1.3, 0.7, 2.1}`):

* `wronsk`, `ode_U`, `ode_V`, `shift_U_up` (DLMF 12.8.2), `shift_U_dn` (12.8.3), `shift_V_dn` (12.8.6), `shift_V_up` (12.8.7), `reflect` (12.2.15--16 with
  `pi / Gamma(1/2 + a) = cos(pi a) Gamma(1/2 - a)`) hold to `1e-30`; the sign-flipped `shift_V_dn` (`+ (a - 1/2) V(a-1)`) fails (residual `O(1)`).
  **The signs recalled in the freeze are correct.**
* `phase_osc` (DLMF 12.10.18): for `mu in {6, 6.3, 12, 12.37, 24}`, `|t| <= 0.8`, the relative error against `2 g/(1-t^2)^{1/4} cos(mu^2 eta - pi/4)` is `0.65/mu^2 .. 0.82/mu^2`
  (so `C ~ 1` works) and the fitted `g(mu)` is `t`-independent to the displayed precision (`g` is astronomically large, which is why it is existential).
* `env_well`, `env_bar`, `beyond` (lem:cha-PCenv (1b), (2), (3)): over `a in {-30.13, ..., 0}` (well), `a in {0.05, ..., 30}` (barrier), `Z in [-12, 16]`, the ratios
  `sqrt(u~^2 + u~'^2/k_2)/(E M_bal) in [0.63, 1.06]`, `sqrt(v~^2 + v~'^2/k_2) E/M_bal in [1.02, 1.58]`, barrier pair `in [0.89, 1.19]`, `kappa_bal |U|/(E M_bal) in [0.43, 0.99]`
  (barrier `[0.61, 0.99]`), `|U'|/(k_2^{1/2} |U|) in [0.48, 1.16] <= 4`.  So `c_PC <= 1.7 <= sqrt 17 * 0.43` and `C_PC >= 1.6` are simultaneously satisfiable: `cPC_le`
  and `beyond`'s constant `c_PC/sqrt 17` are consistent.

Redundancy (harmless, kept so that downstream proofs may cite either): `ode_U`, `ode_V` follow from the four shift relations (differentiate `shift_U_dn`, use `shift_U_up` at `a-1`; the same for `V`).
`smooth_*` is `ContDiff ℝ ⊤`, i.e. analytic in the current Mathlib convention for `⊤ : WithTop ℕ∞`, which `U, V` are.  No field is a conclusion of Theorem A or B; the fields are mutually consistent
(they all hold for the genuine `U, V`).
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

/-- The two-sided well weight `W_well` of eq:cha-MolvEquiv: `E_well(a,Z)` for `Z >= 0` and `E_well(a,|Z|)^{-1}` for `Z < 0`. -/
def Wwell (a z : ℝ) : ℝ := if 0 ≤ z then Ewell a z else (Ewell a |z|)⁻¹

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
  /-- DLMF 12.8.6 (signs verified numerically, see the module docstring). -/
  shift_V_dn : ∀ a z, deriv (V a) z - z / 2 * V a z - (a - 1 / 2) * V (a - 1) z = 0
  /-- DLMF 12.8.7. -/
  shift_V_up : ∀ a z, deriv (V a) z + z / 2 * V a z - V (a + 1) z = 0
  /-- DLMF 12.2.15--16 (eq:tha-conn): the connection formula, `a <= 0`. -/
  reflect : ∀ a ≤ 0, ∀ z, U a (-z) = -Real.sin (Real.pi * a) * U a z
      + Real.cos (Real.pi * a) * Real.Gamma (1 / 2 - a) * V a z
  /-- DLMF 12.2.15--16 with 12.2.7 (**round 3**): the companion of `reflect`, `V(a,-z) = cos(pi a)/Gamma(1/2-a) U(a,z) + sin(pi a) V(a,z)`, `a <= 0`
  (no singularity at the resonances `cos(pi a) = 0`).  With `reflect` it is the matrix `M_-(a)` of lem:cha-PCenv (1a) (see `pcSwap_eq_pcMinus`). -/
  reflect_V : ∀ a ≤ 0, ∀ z, V a (-z) = Real.cos (Real.pi * a) / Real.Gamma (1 / 2 - a) * U a z
      + Real.sin (Real.pi * a) * V a z
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
  /-- eq:cha-MolvEquiv (**round 3**; lem:cha-PCenv (1b)), `a <= 0`, all `Z`: `c_PC kappa^{-1} W_well M_bal <= M_Olv <= C_PC kappa^{-1} W_well M_bal`.  The upper half
  is the envelope bound; the lower half inside the well (`|Z| < 2 sqrt(-a)`), where `beyond` says nothing, is the new content. -/
  molv_well : ∀ a ≤ 0, ∀ z, cPC * (kappaBal a)⁻¹ * Wwell a z * Mbal a z ≤ Molv U V a z ∧
    Molv U V a z ≤ CPC * (kappaBal a)⁻¹ * Wwell a z * Mbal a z
  /-- eq:cha-envbar (**round 3**), `a > 0`, all `Z`: `c_PC kappa^{-1} E_bar M_bal <= M_Olv <= C_PC kappa^{-1} E_bar M_bal`. -/
  molv_bar : ∀ a, 0 < a → ∀ z, cPC * (kappaBal a)⁻¹ * Ebar a z * Mbal a z ≤ Molv U V a z ∧
    Molv U V a z ≤ CPC * (kappaBal a)⁻¹ * Ebar a z * Mbal a z
  /-- growth of the dominant solution (**round 3**; app_thmA Step 3 (ii): `r_2 = e^{-theta}(1 + O(h)) < 1`): there is `c_V > 0` with `V(a,z) > 0` and `V'(a,z) >= c_V k_2^{1/2} V(a,z)`
  for `z >= 2 sqrt(max(-a,0))` (beyond the turning point; every `z >= 0` if `a >= 0`). -/
  V_growth : ∃ cV : ℝ, 0 < cV ∧ ∀ a z, 2 * Real.sqrt (max (-a) 0) ≤ z →
    0 < V a z ∧ cV * Real.sqrt (k2 a z) * V a z ≤ deriv (V a) z
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
