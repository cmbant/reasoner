module

public import FormalResearch.ModularBootstrap.Spin.Defs

/-!
# SPIN-F target statements as `Prop`s

Index of the nine Paper II targets of work package SPIN-F
(`CFT/modular_bootstrap/paper/spinning_foundations.tex` and `spinning_calibration.tex`).
Each target is stated here as a closed `Prop` using the concrete definitions of `Spin.Defs`,
with the paper's quantifiers and constant dependencies documented on each definition.

| paper label | `Prop` name(s) | source |
|---|---|---|
| `spinnotes:S1` (a)–(e) | `SpinS1a`, `SpinS1b`, `SpinS1c`, `SpinS1d`, `SpinS1e` | `spinning_foundations.tex` |
| `spinnotes:S21` | `SpinS21` | `spinning_foundations.tex` |
| `spinnotes:S22` | `SpinS22` | `spinning_foundations.tex` |
| `spinnotes:S22b` | `SpinS22b` | `spinning_foundations.tex` |
| `spinnotes:S23` | `SpinS23` | `spinning_foundations.tex` |
| `spinnotes:S24` | `SpinS24` | `spinning_foundations.tex` |
| `spinnotes:S3` | `SpinS3` | `spinning_foundations.tex` |
| `scal:C1` | `ScalC1` | `spinning_calibration.tex` |
| `scal:C3` | `ScalC3` | `spinning_calibration.tex` |
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Bessel
open FormalResearch.ModularBootstrap.LP

/-! ### Complex reduced partition function (for `spinnotes:S1`(a)) -/

/-- Complex two-variable reduced partition function
`\widehat Z(z_1, z_2) = e^{\pi a (z_1 + z_2)} (1 - e^{-2\pi z_1})(1 - e^{-2\pi z_2})
  + \iint e^{-2\pi (z_1 t_L + z_2 t_R)} d\nu(t_L, t_R)`
on `{Re z_1 > 0} × {Re z_2 > 0}`. -/
noncomputable def spinZHatC (a : ℝ) (ν : Measure (ℝ × ℝ)) (z₁ z₂ : ℂ) : ℂ :=
  Complex.exp (π * (a : ℂ) * (z₁ + z₂)) *
    (1 - Complex.exp (-2 * π * z₁)) * (1 - Complex.exp (-2 * π * z₂)) +
  ∫ p : ℝ × ℝ, Complex.exp (-2 * π * (z₁ * (p.1 : ℂ) + z₂ * (p.2 : ℂ))) ∂ν

/-! ### Theorem S1 (`spinnotes:S1`) -/

/-- **`spinnotes:S1`(a) (Crossing).**
For any `a ≥ 2` and positive measure `ν` on `[0, ∞)²` with finite diagonal Laplace transform
`∫ e^{-2π β (t_L + t_R)} dν < ∞` for all `β > 0`:
1. `spinZHatC a ν` is separately holomorphic on `{Re z_1 > 0} × {Re z_2 > 0}`;
2. Euclidean modular `S`-invariance (`z_2 = \bar z_1`) is equivalent to independent
   real-temperature crossing `(sd:eSD1)` for `β_L, β_R > 0`;
3. independent real-temperature crossing is equivalent to the vanishing of all two-variable odd
   Laguerre moments (`m + n` odd) built from `L_m^{(-1/2)}(4π t_L) L_n^{(-1/2)}(4π t_R) e^{-2π t}`.

No free constants. -/
def SpinS1a : Prop :=
  ∀ {a : ℝ}, 2 ≤ a → ∀ (ν : Measure (ℝ × ℝ)),
    ν ({p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}ᶜ) = 0 →
    (∀ {β : ℝ}, 0 < β → Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) ν) →
    ((∀ z₂ : ℂ, 0 < z₂.re → DifferentiableOn ℂ (fun z₁ => spinZHatC a ν z₁ z₂) {z : ℂ | 0 < z.re}) ∧
     (∀ z₁ : ℂ, 0 < z₁.re → DifferentiableOn ℂ (fun z₂ => spinZHatC a ν z₁ z₂) {z : ℂ | 0 < z.re})) ∧
    ((∀ z : ℂ, 0 < z.re →
        spinZHatC a ν z (starRingEnd ℂ z) =
          (z * starRingEnd ℂ z) ^ (-(1 / 2 : ℂ)) * spinZHatC a ν z⁻¹ (starRingEnd ℂ z)⁻¹) ↔
      (∀ {βL βR : ℝ}, 0 < βL → 0 < βR →
        ∫ p : ℝ × ℝ, spinThermalX βL βR p.1 p.2 ∂ν = -spinThermalXVac a βL βR)) ∧
    ((∀ {βL βR : ℝ}, 0 < βL → 0 < βR →
        ∫ p : ℝ × ℝ, spinThermalX βL βR p.1 p.2 ∂ν = -spinThermalXVac a βL βR) ↔
      (∀ m n : ℕ, Odd (m + n) →
        ∫ p : ℝ × ℝ, lagPsi (1 / 2) m p.1 * lagPsi (1 / 2) n p.2 ∂ν =
          -(∫ p : ℝ × ℝ, lagPsi (1 / 2) m (p.1 ^ 2 / 2) * lagPsi (1 / 2) n (p.2 ^ 2 / 2) *
              spinV1 a p.1 * spinV1 a p.2)))

/-- **`spinnotes:S1`(b) (Cardy harmonics and radial subspace).**
For all `a ≥ 2`, `ℓ : ℕ`, and `t ≥ 0`:
- `V_{2,\ell}(t) = 2π [I_{4\ell}(4π√(at)) - 2 (-1)^\ell T_{2\ell}(1/(a-1)) I_{4\ell}(4π√((a-1)t))
    + I_{4\ell}(4π√((a-2)t))]`;
- `V_{2,0}(t) = ρ_C(t) = virasoroProblem.cardyDensity a t`;
- the radial lift `g ↦ spinRadialLift g` identifies `TestClass virasoroProblem a` with the
  `O(2)`-radial subspace of `SpinTestClass a`, with `M_2[Φ_g] = 2π M[g]` and
  `(Φ_g)_vac = g_vac`.

No free constants. -/
def SpinS1b : Prop :=
  ∀ {a : ℝ}, 2 ≤ a →
    (∀ (ℓ : ℕ) {t : ℝ}, 0 ≤ t →
      spinV2Harmonic a ℓ t =
        2 * π * (besselI (4 * ℓ) (4 * π * Real.sqrt (a * t)) -
          2 * (-1 : ℝ) ^ ℓ * (Polynomial.Chebyshev.T ℝ (2 * ℓ : ℤ)).eval (1 / (a - 1)) *
            besselI (4 * ℓ) (4 * π * Real.sqrt ((a - 1) * t)) +
          besselI (4 * ℓ) (4 * π * Real.sqrt ((a - 2) * t)))) ∧
    (∀ {t : ℝ}, 0 ≤ t → spinV2Harmonic a 0 t = virasoroProblem.cardyDensity a t) ∧
    (∀ (g : ℝ → ℝ),
      (TestClass virasoroProblem a g ↔ SpinTestClass a (spinRadialLift g)) ∧
      (TestClass virasoroProblem a g →
        spinM2 a (spinRadialLift g) = 2 * π * virasoroProblem.cardyNorm a g ∧
        spinPhiVac a (spinRadialLift g) = virasoroProblem.gVac a g))

/-- **`spinnotes:S1`(c) (Primal hierarchy).**
For all `c ≥ 40`,
`\Delta_{\rm int}(c) ≤ \Delta_L(c) ≤ \Delta_{\rm spin}(c) ≤ \Delta_{\rm best}^{\rm spinless}(c)`.

No free constants. -/
def SpinS1c : Prop :=
  ∀ {c : ℝ}, 40 ≤ c →
    spinDeltaInt c ≤ spinDeltaL c ∧
    spinDeltaL c ≤ spinDeltaSpin c ∧
    spinDeltaSpin c ≤ virasoroProblem.Delta_best (c - 1)

/-- **`spinnotes:S1`(d) (Certification).**
For `c ≥ 25` (`a = (c - 1) / 12`), if `Φ ∈ \overline{\mathcal A}_{\rm spin}` satisfies
`Φ ≥ 0` on `\Omega_L(T)` and `Φ_vac > 0`, then no positive crossing measure satisfying `(sd:eSD1)`
is supported on `\Omega_L(T)`.

No free constants. -/
def SpinS1d : Prop :=
  ∀ {c T : ℝ}, 25 ≤ c → ∀ {Φ : ℝ × ℝ → ℝ},
    SpinIsFeasible (SpinTestClass ((c - 1) / 12)) liouvilleCone ((c - 1) / 12) T Φ →
    ¬ ∃ meas : SpinCrossingMeasure ((c - 1) / 12), meas.ν (liouvilleCone T)ᶜ = 0

/-- **`spinnotes:S1`(e) (Strong duality).**
For `c ≥ 25` (`a = (c - 1) / 12`):
- when `T(\overline{\mathcal A}_{\rm spin}; \Omega_L) > 0`,
  `\Delta_L(c) = \Delta_{\rm spin}(c) = a + \tau_{\max}(\Omega_L)` with attainment by a positive
  crossing measure on `\Omega_L(\tau_{\max}(\Omega_L))`;
- on `\Omega_{\mathbb Z}`, when `T(\mathcal B; \Omega_{\mathbb Z}) > 0`,
  `T(\mathcal B; \Omega_{\mathbb Z}) = \tau_{\max}(\Omega_{\mathbb Z})` with attainment.

No free constants. -/
def SpinS1e : Prop :=
  ∀ {c : ℝ}, 25 ≤ c →
    (0 < spinThrInf (SpinTestClass ((c - 1) / 12)) liouvilleCone ((c - 1) / 12) →
      spinDeltaL c = spinDeltaSpin c ∧
      spinDeltaL c = (c - 1) / 12 + spinTauMax ((c - 1) / 12) liouvilleCone ∧
      ∃ meas : SpinCrossingMeasure ((c - 1) / 12),
        meas.ν (liouvilleCone (spinTauMax ((c - 1) / 12) liouvilleCone))ᶜ = 0) ∧
    (0 < spinThrInf (SpinCertifiedClass ((c - 1) / 12)) integerSpinCone ((c - 1) / 12) →
      spinThrInf (SpinCertifiedClass ((c - 1) / 12)) integerSpinCone ((c - 1) / 12) =
        spinTauMax ((c - 1) / 12) integerSpinCone ∧
      ∃ meas : SpinCrossingMeasure ((c - 1) / 12),
        meas.ν (integerSpinCone (spinTauMax ((c - 1) / 12) integerSpinCone))ᶜ = 0)

/-! ### Lemma S2.1 (`spinnotes:S21`) -/

/-- **`spinnotes:S21` (Weighted control of the full spinning test class).**
For all `c ≥ 40` (`a = (c - 1) / 12`) and `Φ ∈ \overline{\mathcal A}_{\rm spin}`,
`‖Φ‖_∞ ≤ ‖Φ‖_1 ≤ 3.2 M_2[Φ]`.

All constants are explicit (`3.2 = 32 / 10`), independent of `c` and `Φ`. -/
def SpinS21 : Prop :=
  ∀ {c : ℝ}, 40 ≤ c → ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass ((c - 1) / 12) Φ →
    (∀ p : ℝ × ℝ, |Φ p| ≤ ∫ q : ℝ × ℝ, |Φ q|) ∧
    (∫ q : ℝ × ℝ, |Φ q| ≤ (32 / 10 : ℝ) * spinM2 ((c - 1) / 12) Φ)

/-! ### Lemma S2.2 (`spinnotes:S22`) -/

/-- **`spinnotes:S22` (Uniform bistrip bound and outward `L^1` control).**
For `c ≥ 40` (`a = (c - 1) / 12`) and `Φ ∈ \overline{\mathcal A}_{\rm spin}`:
1. `\mathcal D_a \mathcal G` (`spinDaC a Φ`) is separately holomorphic on `\mathcal S_{1/2}²`,
   agrees with `spinDa a Φ` on `ℝ²`, and satisfies the charge-independent bistrip bound
   `|(\mathcal D_a \mathcal G)(b_L, b_R)| ≤ (1 + 4 (Re b_L)²)(1 + 4 (Re b_R)²) M_2[Φ]`
   for `|Im b_L|, |Im b_R| ≤ 1/2`.
2. The outward difference `\Delta_a \mathcal G` satisfies
   `∬ |\Delta_a \mathcal G| w_c ⊗ w_c ≤ (1 + λ^{-1})² M_2[Φ] ≤ 4 M_2[Φ]`.
3. By contrast, `‖\mathcal D_a \mathcal G‖_{L^1(w_c ⊗ w_c)} / M_2[Φ]` is unbounded on
   `\overline{\mathcal A}_{\rm spin}`.

All constants are explicit and independent of `a, c, Φ`. -/
def SpinS22 : Prop :=
  ∀ {c : ℝ}, 40 ≤ c →
    (∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass ((c - 1) / 12) Φ →
      let a := (c - 1) / 12
      (∀ bR ∈ spinStrip (1 / 2),
        DifferentiableOn ℂ (fun bL => spinDaC a Φ bL bR) (spinStrip (1 / 2))) ∧
      (∀ bL ∈ spinStrip (1 / 2),
        DifferentiableOn ℂ (fun bR => spinDaC a Φ bL bR) (spinStrip (1 / 2))) ∧
      (∀ xL xR : ℝ, spinDaC a Φ (xL : ℂ) (xR : ℂ) = ((spinDa a Φ xL xR : ℝ) : ℂ)) ∧
      (∀ bL bR : ℂ, |bL.im| ≤ 1 / 2 → |bR.im| ≤ 1 / 2 →
        ‖spinDaC a Φ bL bR‖ ≤ (1 + 4 * bL.re ^ 2) * (1 + 4 * bR.re ^ 2) * spinM2 a Φ) ∧
      Integrable (fun p : ℝ × ℝ => |spinDeltaA a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) ∧
      (∫ p : ℝ × ℝ, |spinDeltaA a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) ≤
        (1 + (spinLambda a)⁻¹) ^ 2 * spinM2 a Φ) ∧
    (∀ K : ℝ, ∃ Φ : ℝ × ℝ → ℝ, SpinTestClass ((c - 1) / 12) Φ ∧
      0 < spinM2 ((c - 1) / 12) Φ ∧
      K * spinM2 ((c - 1) / 12) Φ <
        ∫ p : ℝ × ℝ, |spinDa ((c - 1) / 12) Φ p.1 p.2| *
          spinWc ((c - 1) / 12) p.1 * spinWc ((c - 1) / 12) p.2)

/-! ### Lemma S2.2' (`spinnotes:S22b`) -/

/-- Slit integral `S_d = ∫_{|s| ≥ b_*} a e^{n L(s)} |\Delta_a \mathcal G(s + d, s - d)| ds`
(`spinnotes:S22b`, with `n = 12 a`). -/
noncomputable def spinSlitIntegral (a : ℝ) (Φ : ℝ × ℝ → ℝ) (d : ℝ) : ℝ :=
  ∫ s in {s : ℝ | spinBStar a ≤ |s|},
    a * Real.exp (12 * a * spinL s) * |spinDeltaA a Φ (s + d) (s - d)|

/-- **`spinnotes:S22b` (Slit-strip fold estimate with no polynomial charge loss).**
There exist absolute constants `k ≥ 0`, `C > 0`, `κ > 0`, `δ₀ > 0`, and `n₀ ≥ 39`
(independent of `n, d, Φ, R`) such that for all `c ≥ n₀ + 1` (`n = c - 1`, `a = n / 12`,
`ε = n^{-2/3}`, `b_* = \gamma_a \xi_*`, `D = 3 b_* / 4`) and every `Φ ∈ \overline{\mathcal A}_{\rm spin}`
with `M_2[Φ] = 1`:
- (a) `∫_{|d| ≤ D} S_d dd ≤ C` (with `S_d` integrable on `[-D, D]`);
- (b) for `|ξ| < b_*`, `δ = b_* - |ξ|`, `|d| ≤ D`:
  `a e^{n L(ξ)} |\Delta_a \mathcal G(ξ + d, ξ - d)| ≤ C n^k (1 + S_d) δ^{-1} e^{-κ n δ^{3/2}}`;
- (c) for any `R ≥ 1` and `δ ∈ [R ε, δ₀]`, (b) holds with `k = 0` (constants independent of `R`). -/
def SpinS22b : Prop :=
  ∃ (k C κ δ₀ n₀ : ℝ), 0 ≤ k ∧ 0 < C ∧ 0 < κ ∧ 0 < δ₀ ∧ 39 ≤ n₀ ∧
    ∀ {c : ℝ}, n₀ + 1 ≤ c →
      let n := c - 1
      let a := n / 12
      let ε := n ^ (-(2 / 3 : ℝ))
      let bStar := spinBStar a
      let D := 3 * bStar / 4
      ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ → spinM2 a Φ = 1 →
        (IntegrableOn (spinSlitIntegral a Φ) (Icc (-D) D) ∧
          ∫ d in Icc (-D) D, spinSlitIntegral a Φ d ≤ C) ∧
        (∀ ξ d : ℝ, |ξ| < bStar → |d| ≤ D →
          let δ := bStar - |ξ|
          a * Real.exp (n * spinL ξ) * |spinDeltaA a Φ (ξ + d) (ξ - d)| ≤
            C * n ^ k * (1 + spinSlitIntegral a Φ d) * δ⁻¹ *
              Real.exp (-κ * n * δ ^ (3 / 2 : ℝ))) ∧
        (∀ R : ℝ, 1 ≤ R → ∀ ξ d : ℝ, |ξ| < bStar → |d| ≤ D →
          let δ := bStar - |ξ|
          R * ε ≤ δ → δ ≤ δ₀ →
          a * Real.exp (n * spinL ξ) * |spinDeltaA a Φ (ξ + d) (ξ - d)| ≤
            C * (1 + spinSlitIntegral a Φ d) * δ⁻¹ *
              Real.exp (-κ * n * δ ^ (3 / 2 : ℝ)))

/-! ### Lemma S2.3 (`spinnotes:S23`) -/

/-- **`spinnotes:S23` (Longitudinal scalar reduction).**
There exists an absolute constant `C > 0` (independent of `c, Φ`) such that for all `c ≥ 40`
(`n = c - 1`, `a = n / 12`) and `Φ ∈ \overline{\mathcal A}_{\rm spin}`:
- `G_{\rm eff}` is even and holomorphic on `\mathcal S_{1/2}`;
- `|G_{\rm eff}(b)| ≤ C n² M_2[Φ]` on `\mathcal S_{1/2}`;
- `∫_ℝ |G_{\rm eff}(x)| a e^{n L(x)} dx ≤ C M_2[Φ]`;
- if `x₁ ≥ 0` and `\mathcal G(ξ + d, ξ - d) ≥ 0` on `ξ² + d² ≥ x₁²`, then
  `Re G_{\rm eff}(x) ≥ 0` for `|x| ≥ x₁`. -/
def SpinS23 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {c : ℝ}, 40 ≤ c →
      let n := c - 1
      let a := n / 12
      ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ →
        (∀ b : ℂ, spinGeff a Φ (-b) = spinGeff a Φ b) ∧
        DifferentiableOn ℂ (spinGeff a Φ) (spinStrip (1 / 2)) ∧
        (∀ b ∈ spinStrip (1 / 2), ‖spinGeff a Φ b‖ ≤ C * n ^ 2 * spinM2 a Φ) ∧
        Integrable (fun x : ℝ => ‖spinGeff a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)) ∧
        (∫ x : ℝ, ‖spinGeff a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)) ≤ C * spinM2 a Φ ∧
        (∀ x₁ : ℝ, 0 ≤ x₁ →
          (∀ ξ d : ℝ, x₁ ^ 2 ≤ ξ ^ 2 + d ^ 2 → 0 ≤ spinG a Φ (ξ + d) (ξ - d)) →
          ∀ x : ℝ, x₁ ≤ |x| → 0 ≤ (spinGeff a Φ (x : ℂ)).re)

/-! ### Lemma S2.4 (`spinnotes:S24`) -/

/-- **`spinnotes:S24` (Sub-bistrip holomorphy, derivative bounds, and double inward telescope).**
1. For every `c ≥ 25` (`a = (c - 1) / 12`) and `0 < θ < 1/2`, there exists `C(a, θ) > 0`
   (depending only on `a, θ`, independent of `Φ`) such that for all `Φ ∈ \overline{\mathcal A}_{\rm spin}`:
   `I_\theta[Φ] ≤ C(a, θ) M_2[Φ]`, `spinGC a Φ` is separately holomorphic on `\mathcal S_{1/2}²`,
   agrees with `spinG a Φ` on `ℝ²`, and satisfies `|spinGC a Φ b_L b_R| ≤ C(a, θ) M_2[Φ]` on
   `|Im b_L|, |Im b_R| ≤ θ`.
2. For every `c ≥ 40` (`a = (c - 1) / 12`) and `Φ ∈ \overline{\mathcal A}_{\rm spin}`:
   on `‖b_L‖, ‖b_R‖ ≤ 1/2`, `|(\mathcal D_a \mathcal G)(b_L, b_R)| ≤ 64 M_2[Φ] ‖b_L‖² ‖b_R‖²`,
   and for all `b_L, b_R ∈ \mathcal S_{1/2}`, the double inward telescope
   `∑_{m, ℓ ≥ 0} (\mathcal D_a \mathcal G)(\gamma_a^m b_L, \gamma_a^\ell b_R)`
   converges to `\mathcal G(b_L, b_R) - \mathcal G(b_L, 0) - \mathcal G(0, b_R) + \mathcal G(0, 0)`. -/
def SpinS24 : Prop :=
  (∀ {c : ℝ}, 25 ≤ c → ∀ {θ : ℝ}, 0 < θ → θ < 1 / 2 →
    ∃ C : ℝ, 0 < C ∧
      ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass ((c - 1) / 12) Φ →
        let a := (c - 1) / 12
        Integrable (fun p : ℝ × ℝ => |Φ p| * Real.cosh (4 * π * Real.sqrt a * θ * p.1) *
          Real.cosh (4 * π * Real.sqrt a * θ * p.2)) ∧
        spinITheta a θ Φ ≤ C * spinM2 a Φ ∧
        (∀ bR ∈ spinStrip (1 / 2),
          DifferentiableOn ℂ (fun bL => spinGC a Φ bL bR) (spinStrip (1 / 2))) ∧
        (∀ bL ∈ spinStrip (1 / 2),
          DifferentiableOn ℂ (fun bR => spinGC a Φ bL bR) (spinStrip (1 / 2))) ∧
        (∀ xL xR : ℝ, spinGC a Φ (xL : ℂ) (xR : ℂ) = ((spinG a Φ xL xR : ℝ) : ℂ)) ∧
        (∀ bL bR : ℂ, |bL.im| ≤ θ → |bR.im| ≤ θ → ‖spinGC a Φ bL bR‖ ≤ C * spinM2 a Φ)) ∧
  (∀ {c : ℝ}, 40 ≤ c → ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass ((c - 1) / 12) Φ →
    let a := (c - 1) / 12
    (∀ bL bR : ℂ, ‖bL‖ ≤ 1 / 2 → ‖bR‖ ≤ 1 / 2 →
      ‖spinDaC a Φ bL bR‖ ≤ 64 * spinM2 a Φ * ‖bL‖ ^ 2 * ‖bR‖ ^ 2) ∧
    (∀ bL ∈ spinStrip (1 / 2), ∀ bR ∈ spinStrip (1 / 2),
      HasSum (fun q : ℕ × ℕ =>
        spinDaC a Φ ((spinGamma a ^ q.1 : ℝ) * bL) ((spinGamma a ^ q.2 : ℝ) * bR))
        (spinGC a Φ bL bR - spinGC a Φ bL 0 - spinGC a Φ 0 bR + spinGC a Φ 0 0)))

/-! ### Theorem S3 (`spinnotes:S3`) -/

/-- **`spinnotes:S3` (Large-`c` continuous-spin slope).**
With `1 / \Lambda_V = 1 / 12 + \xi_*² / 3`, there exist absolute constants `C, C_+, c₀ > 0`
(`c₀ ≥ 40`) such that for all `c ≥ c₀`:
`(c - 1)/\Lambda_V - C (c - 1)^{1/3} (\log(c - 1))^{2/3} ≤ \Delta_L(c) ≤ \Delta_{\rm spin}(c)
  ≤ \Delta_{\rm best}^{\rm spinless}(c) ≤ (c - 1)/\Lambda_V + A_{\rm opt} (c - 1)^{1/3} + C_+`. -/
def SpinS3 : Prop :=
  ∃ (C C_plus c₀ : ℝ), 0 < C ∧ 0 < C_plus ∧ 40 ≤ c₀ ∧
    ∀ {c : ℝ}, c₀ ≤ c →
      (c - 1) / lambdaV - C * (c - 1) ^ ((1 : ℝ) / 3) * (Real.log (c - 1)) ^ ((2 : ℝ) / 3) ≤
        spinDeltaL c ∧
      spinDeltaL c ≤ spinDeltaSpin c ∧
      spinDeltaSpin c ≤ virasoroProblem.Delta_best (c - 1) ∧
      virasoroProblem.Delta_best (c - 1) ≤
        (c - 1) / lambdaV + Aopt * (c - 1) ^ ((1 : ℝ) / 3) + C_plus

/-! ### Proposition C1 (`scal:C1`) -/

/-- **`scal:C1` (Calibrated adjoint ratio).**
There exist absolute constants `C, C₁, r₀ > 0` (independent of `c, ξ, d`) such that for all
`c ≥ 40` (`n = c - 1`, `a = n / 12`) and all `ξ, d : ℝ` with `|d| ≤ ξ`:
1. `0 ≤ R_c(ξ, d) ≤ exp(-½ (ξ² - ξ_*²)² - d² / σ₀²) + C / n`;
2. near `(ξ_*, 0)` (`|ξ - ξ_*| + |d| ≤ r₀`), `|R_c(ξ, d) - 1| ≤ C₁ ((ξ - ξ_*)² + d² + n⁻¹)`. -/
def ScalC1 : Prop :=
  ∃ (C C₁ r₀ : ℝ), 0 < C ∧ 0 < C₁ ∧ 0 < r₀ ∧
    ∀ {c : ℝ}, 40 ≤ c →
      let n := c - 1
      let a := n / 12
      ∀ ξ d : ℝ, |d| ≤ ξ →
        (0 ≤ spinRc a ξ d ∧
          spinRc a ξ d ≤
            Real.exp (-(1 / 2 : ℝ) * (ξ ^ 2 - xiStar ^ 2) ^ 2 - d ^ 2 / spinSigma0 ^ 2) + C / n) ∧
        (|ξ - xiStar| + |d| ≤ r₀ →
          |spinRc a ξ d - 1| ≤ C₁ * ((ξ - xiStar) ^ 2 + d ^ 2 + n⁻¹))

/-! ### Lemma C3 (`scal:C3`) -/

/-- **`scal:C3` (Bounded outward inverse away from the axes).**
For every `r > 0`, there exists `C_r > 0` (depending only on `r`, independent of `c, Φ, N`)
such that for all `c ≥ 40` (`a = (c - 1) / 12`) and `Φ ∈ \overline{\mathcal A}_{\rm spin}`,
on `K_r = {x_L, x_R ≥ r}`:
1. `∫_{K_r} |\mathcal G| w_c ⊗ w_c ≤ (1 - e^{-4π r})^{-2} ‖\Delta_a \mathcal G‖_{L^1(w_c ⊗ w_c)}`;
2. for every `N : ℕ`, the tail sum over `m + ℓ ≥ N` of the dilated `\Delta_a \mathcal G` integrals
   over `K_r` is at most `C_r (N + 1) e^{-4π r N} ‖\Delta_a \mathcal G‖_{L^1(w_c ⊗ w_c)}`. -/
def ScalC3 : Prop :=
  ∀ {r : ℝ}, 0 < r →
    ∃ C_r : ℝ, 0 < C_r ∧
      ∀ {c : ℝ}, 40 ≤ c →
        let a := (c - 1) / 12
        ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ →
          (∫ p in {p : ℝ × ℝ | r ≤ p.1 ∧ r ≤ p.2},
            |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) ≤
            (1 - Real.exp (-4 * π * r)) ^ (-2 : ℤ) *
              (∫ p : ℝ × ℝ, |spinDeltaA a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) ∧
          ∀ N : ℕ,
            (∑' q : {q : ℕ × ℕ // N ≤ q.1 + q.2},
              ∫ p in {p : ℝ × ℝ | r ≤ p.1 ∧ r ≤ p.2},
                |spinDeltaA a Φ (spinLambda a ^ q.1.1 * p.1) (spinLambda a ^ q.1.2 * p.2)| *
                  spinWc a p.1 * spinWc a p.2) ≤
              C_r * ((N : ℝ) + 1) * Real.exp (-4 * π * r * (N : ℝ)) *
                (∫ p : ℝ × ℝ, |spinDeltaA a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2)

end FormalResearch.ModularBootstrap.Spin
