module

public import FormalResearch.ModularBootstrap.Spin.ScalC1
public import FormalResearch.ModularBootstrap.Spin.ScalC3
public import FormalResearch.ModularBootstrap.Spin.SpinD3W
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.LangerChart

/-!
# SPIN-S4 Statements (`CFT/modular_bootstrap/paper/spinning_s4.tex`)

Formal statements (as named `Prop`s, mirroring `Spin/Statements.lean` and `Spin/SpinDStatements.lean`)
of all fourteen `result` environments in `CFT/modular_bootstrap/paper/spinning_s4.tex`:
- `SpinS4` (`s4:S4`, Theorem S4): sharp Airy coefficient on the continuous-spin Liouville cone,
  the slack-feasible threshold obstruction `(s4:eSlack)`, strong duality & attainment, and the
  wider-cone extension `{t_L, t_R ≥ -η a}` (`0 ≤ η < 1/2`).
- Section 2 (`s4:2.1`–`s4:2.4`): `SpinS4_2_1`, `SpinS4_2_2`, `SpinS4_2_3`, `SpinS4_2_4`.
- Section 3 (`s4:3.3`, `s4:3.4`): `SpinS4_3_3`, `SpinS4_3_4`.
- Section 4 (`s4:4.1`–`s4:4.3`): `SpinS4_4_1`, `SpinS4_4_2`, `SpinS4_4_3`.
- Section 5 (`s4:5.1`, `s4:5.2`): `SpinS4_5_1`, `SpinS4_5_2`.
- Section 6 (`s4:6.1`, `s4:4.4`): `SpinS4_6_1`, `SpinS4_4_4`.

Unconditional: no placeholders and no added axioms; the open analytic estimates remain named `Prop`s, while
`Spin/SpinS4Assembly.lean` assembles `SpinS4_4_4` and `SpinS4` from them and the already-proved
`SpinS1c`, `SpinS1e`, `SpinS3`, `SpinS24`, and `SpinDSD`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Finset
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.ConcreteBootstrap

/-! ### Helper definitions for `spinning_s4.tex` -/

/-- Analytic continuation of `spinEvalT Φ` to `(t_L, t_R) ∈ {-η a ≤ t_L, t_R}` (`0 ≤ η < 1/2`)
using the Fourier-odd holomorphic continuation `spinGC a Φ` (`|Im b| < 1/2`).
On `t_L, t_R ≥ 0`, for `a > 0` and `Φ ∈ SpinTestClass a`, this agrees with `spinEvalT Φ`. -/
noncomputable def spinEvalWider (a : ℝ) (Φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (spinGC a Φ
    (Complex.sqrt (2 * (p.1 : ℂ)) / (2 * (Real.sqrt a : ℂ)))
    (Complex.sqrt (2 * (p.2 : ℂ)) / (2 * (Real.sqrt a : ℂ)))).re

/-- Wider-cone primal infimum over `widerCone a η T = {t_L, t_R ≥ -η a, t_L + t_R ≥ T}`
using the Fourier-analytic evaluation `spinEvalWider`. -/
noncomputable def spinWiderThr (C : (ℝ × ℝ → ℝ) → Prop) (a η : ℝ) : ℝ :=
  sInf {T : ℝ | 0 < T ∧ ∃ Φ, C Φ ∧ 0 < spinPhiVac a Φ ∧
    ∀ p ∈ widerCone a η T, 0 ≤ spinEvalWider a Φ p}

/-- Standing slack-feasible normalised test hypothesis `(s4:eH)` at `c ≥ 40` (`n = c - 1`,
`a = n / 12`) with gap-disc radius `x₁ ≥ 0`. -/
def SpinSlackHyp (c x₁ : ℝ) (Φ : ℝ × ℝ → ℝ) : Prop :=
  let a := (c - 1) / 12
  0 ≤ x₁ ∧ SpinTestClass a Φ ∧ spinM2 a Φ = 1 ∧ -(c - 1)⁻¹ ≤ spinPhiVac a Φ ∧
    ∀ ξ d : ℝ, x₁ ^ 2 ≤ ξ ^ 2 + d ^ 2 → 0 ≤ spinG a Φ (ξ + d) (ξ - d)

/-- Transverse distance `d_△(x_L, x_R) = ½ ||x_L| - |x_R||` and cutoff `v = min(d_△², 1)`
for `(s4:eP.1)`. -/
noncomputable def spinTransDist (p : ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) * abs (|p.1| - |p.2|)

/-- Longitudinal midpoint coordinate `b_△(x_L, x_R) = ½ (|x_L| + |x_R|)` (`(s4:eR.1)`). -/
noncomputable def spinLongDist (p : ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) * (|p.1| + |p.2|)

/-- Positive-mass angular variance `V_{+,n}` (`(s4:eP.1)`). -/
noncomputable def spinPosAngVar (a : ℝ) (Φ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, min (spinTransDist p ^ 2) 1 * max (spinG a Φ p.1 p.2) 0 *
    spinWc a p.1 * spinWc a p.2

/-- Calibrated vacuum integral `I_{cal,n} = ∫_ℝ a e^{n L(b)} G_{cal}(b) db` (`(s4:eP.0)`). -/
noncomputable def spinCalInt (c : ℝ) (Φ : ℝ × ℝ → ℝ) : ℝ :=
  let n := c - 1
  let a := n / 12
  ∫ b : ℝ, a * Real.exp (n * spinL b) * (spinGcal a Φ (b : ℂ)).re

/-- Calibrated projection applied separately to a nonnegative measurable slice `G_±(x_L, x_R)`:
`4 F(ξ_*)² ∫ h_b^{cal}(d) G(b + d, b - d) dd` (`(s4:sec2.4)`). -/
noncomputable def spinCalProjFn (G : ℝ × ℝ → ℝ) (b : ℝ) : ℝ :=
  4 * spinCalF xiStar ^ 2 *
    ∫ d : ℝ, (spinHbCal (b : ℂ) d).re * G (b + d, b - d)

/-- Positive calibrated projected Borel measures `ρ_n^±` on `[0, ∞)` (`(s4:eR.1)`). -/
noncomputable def spinRhoProjMeasure (c : ℝ) (G : ℝ × ℝ → ℝ) : Measure ℝ :=
  Measure.map abs (volume.withDensity fun b : ℝ =>
    ENNReal.ofReal (((c - 1) / 12) * Real.exp ((c - 1) * spinL b) * max (spinCalProjFn G b) 0))

/-- Longitudinal marginal Borel measures `η_n^±` on `[0, ∞)` (`(s4:eR.1)`). -/
noncomputable def spinEtaProjMeasure (a : ℝ) (G : ℝ × ℝ → ℝ) : Measure ℝ :=
  Measure.map spinLongDist (volume.withDensity fun p : ℝ × ℝ =>
    ENNReal.ofReal (max (G p) 0 * spinWc a p.1 * spinWc a p.2))

/-- Real truncated outward inverse `G_n^{[N]}(x_L, x_R) = ∑_{0 ≤ j, ℓ < N} Δ_a G(λ^j x_L, λ^ℓ x_R)`
(`(s4:eO1.1)`). -/
noncomputable def spinTruncInv (a : ℝ) (N : ℕ) (Φ : ℝ × ℝ → ℝ) (xL xR : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N,
    spinDeltaA a Φ (spinLambda a ^ j * xL) (spinLambda a ^ ℓ * xR)

/-- Complex truncated outward inverse `G_n^{[N]}(b_L, b_R)` (`(s4:sec4.1)`). -/
noncomputable def spinTruncInvC (a : ℝ) (N : ℕ) (Φ : ℝ × ℝ → ℝ) (bL bR : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N,
    spinDeltaAC a Φ ((spinLambda a ^ j : ℝ) * bL) ((spinLambda a ^ ℓ : ℝ) * bR)

/-- Adaptive transverse-slice integral `Q_{n,χ}(b)` (`(s4:eO2.2)`). -/
noncomputable def spinQSlice (c : ℝ) (N : ℕ) (Φ : ℝ × ℝ → ℝ) (χ : ℝ → ℝ) (b : ℂ) : ℂ :=
  let n := c - 1
  let ε := n ^ (-(2 / 3 : ℝ))
  let a := n / 12
  ∫ d : ℝ, (χ (d / Real.sqrt ε) : ℂ) * spinTruncInvC a N Φ (b + (d : ℂ)) (b - (d : ℂ))

/-- Rescaled Airy profile `H_n(ζ) = ε a e^{n k (ξ_* + ε ζ)} Q_{n,χ}(ξ_* + ε ζ)` (`(s4:eO2.3)`). -/
noncomputable def spinHProfile (c : ℝ) (N : ℕ) (Φ : ℝ × ℝ → ℝ) (χ : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  let n := c - 1
  let ε := n ^ (-(2 / 3 : ℝ))
  let a := n / 12
  let k : ℝ := 2 * π / 3
  ((ε * a : ℝ) : ℂ) * Complex.exp ((n * k : ℂ) * ((xiStar : ℂ) + (ε : ℂ) * ζ)) *
    spinQSlice c N Φ χ ((xiStar : ℂ) + (ε : ℂ) * ζ)

/-- Normalised calibrated real Airy profile `F_n(u) = ε a e^{n k (ξ_* + ε u)} G_{cal}(ξ_* + ε u)`
(`(s4:eW11)`, `(s4:eO0.3)`). -/
noncomputable def spinFProfile (c : ℝ) (Φ : ℝ × ℝ → ℝ) (u : ℝ) : ℝ :=
  let n := c - 1
  let ε := n ^ (-(2 / 3 : ℝ))
  let a := n / 12
  a * ε * Real.exp (n * spinL (xiStar + ε * u)) *
    (spinGcal a Φ ((xiStar + ε * u : ℝ) : ℂ)).re

/-- Real `L^1`-norm `L_n = B_n = ∫_ℝ a e^{n L(b)} |G_{cal}(b)| db` of the calibrated scalar
(`(s4:eW11)`, `(s4:sec5)`). -/
noncomputable def spinCalNorm (c : ℝ) (Φ : ℝ × ℝ → ℝ) : ℝ :=
  let n := c - 1
  let a := n / 12
  ∫ b : ℝ, a * Real.exp (n * spinL b) * |(spinGcal a Φ (b : ℂ)).re|

/-- Normalised complex Langer profile `P̃(u) = a e^{n k b(u)} (-b'(u)) G_{cal}(b(u)) / B_n`
(`(s4:eE3)`), using the exact analytic inverse Langer chart `b(u) = virasoroBChart (c - 1) u`. -/
noncomputable def spinPtilde (c : ℝ) (Φ : ℝ × ℝ → ℝ) (u : ℂ) : ℂ :=
  let n := c - 1
  let a := n / 12
  let k : ℝ := 2 * π / 3
  let b := virasoroBChart n
  ((a : ℂ) * Complex.exp ((n * k : ℂ) * b u) * (-deriv b u) * spinGcal a Φ (b u)) /
    (spinCalNorm c Φ : ℂ)

/-- Real Airy fold/entropy exponent `H(ζ)` / `e(u) = exp(-4/3 Re u^{3/2})` (`(s4:eE4)`). -/
noncomputable def spinAiryEnv (u : ℂ) : ℝ :=
  Real.exp (-(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re)

/-! ### Section 2 statements (`s4:2.1`–`s4:2.4`) -/

/-- **`s4:2.1` (Theorem 2.1, fold-localised negative mass at the `log n` scale).** -/
def SpinS4_2_1 : Prop :=
  ∀ {C_x p : ℝ}, 0 < p →
    ∃ K_p C_p c₀ : ℝ, 0 < K_p ∧ 0 < C_p ∧ 40 ≤ c₀ ∧
      ∀ {c : ℝ}, c₀ ≤ c →
        let n := c - 1
        let a := n / 12
        let δ := K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n
        ∀ {x₁ : ℝ}, 0 ≤ x₁ → x₁ ≤ xiStar + C_x * n ^ (-(2 / 3 : ℝ)) →
          ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ → spinM2 a Φ = 1 →
            ∫ p_xy in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧
                (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧
                (q.1 + q.2) / 2 < xiStar - δ},
              |spinG a Φ p_xy.1 p_xy.2| * spinWc a p_xy.1 * spinWc a p_xy.2 ≤
                C_p * n ^ (-p)

/-- **`s4:2.2` (Lemma 2.2, positive-mass angular-variance penalty).** -/
def SpinS4_2_2 : Prop :=
  ∃ (c_σ C c₀ : ℝ), 0 < c_σ ∧ 0 < C ∧ 40 ≤ c₀ ∧
    ∀ {c : ℝ}, c₀ ≤ c →
      let n := c - 1
      let a := n / 12
      ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ → spinM2 a Φ = 1 →
        c_σ * spinPosAngVar a Φ - C / n ≤
          ∫ p : ℝ × ℝ, (1 - spinRc a ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)) *
            max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2

/-- **`s4:2.3` (Corollary 2.3, calibrated vacuum remainder).** -/
def SpinS4_2_3 : Prop :=
  ∀ {C_x : ℝ}, ∃ (c_σ C c₀ : ℝ), 0 < c_σ ∧ 0 < C ∧ 40 ≤ c₀ ∧
    ∀ {c x₁ : ℝ}, c₀ ≤ c →
      let n := c - 1
      let a := n / 12
      let δ_n := n ^ (-(2 / 3 : ℝ)) * Real.log n
      0 ≤ x₁ → x₁ ≤ xiStar + C_x * n ^ (-(2 / 3 : ℝ)) →
        ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ → spinM2 a Φ = 1 →
          (∀ ξ d : ℝ, x₁ ^ 2 ≤ ξ ^ 2 + d ^ 2 → 0 ≤ spinG a Φ (ξ + d) (ξ - d)) →
          spinCalInt c Φ ≤ -spinPhiVac a Φ - c_σ * spinPosAngVar a Φ + C * δ_n ∧
          spinCalInt c Φ ≤ -spinPhiVac a Φ + C * δ_n ∧
          (-(c - 1)⁻¹ ≤ spinPhiVac a Φ → spinCalInt c Φ ≤ (C + 1) * δ_n)

/-- **`s4:2.4` (Lemma 2.4, comparison of the calibrated projection with longitudinal marginals).** -/
def SpinS4_2_4 : Prop :=
  ∀ {C_x p r₀ : ℝ}, 2 < p → 0 < r₀ → r₀ < xiStar →
    ∃ (C C_p c₀ : ℝ), 0 < C ∧ 0 < C_p ∧ 40 ≤ c₀ ∧
      ∀ {c x₁ : ℝ}, c₀ ≤ c →
        let n := c - 1
        let a := n / 12
        let δ_n := n ^ (-(2 / 3 : ℝ)) * Real.log n
        x₁ ≤ xiStar + C_x * n ^ (-(2 / 3 : ℝ)) →
        ∀ {Φ : ℝ × ℝ → ℝ}, SpinSlackHyp c x₁ Φ →
          let Gplus := fun q : ℝ × ℝ => max (spinG a Φ q.1 q.2) 0
          let Gminus := fun q : ℝ × ℝ => max (-spinG a Φ q.1 q.2) 0
          let ρplus := spinRhoProjMeasure c Gplus
          let ρminus := spinRhoProjMeasure c Gminus
          let ηplus := spinEtaProjMeasure a Gplus
          let ηminus := spinEtaProjMeasure a Gminus
          (∀ E : Set ℝ, MeasurableSet E →
            |(ρminus E).toReal - (ηminus E).toReal| ≤ C * δ_n) ∧
          (ρplus (Ici 0)).toReal ≤ (ηplus (Ici 0)).toReal + C / n ∧
          (ηminus (Ici 0)).toReal - C * δ_n ≤ (ρminus (Ici 0)).toReal ∧
          (ρminus (Icc 0 (xiStar - r₀))).toReal ≤ C * δ_n + C_p * n ^ (-p)

/-! ### Section 3 statements (`s4:3.3`, `s4:3.4`) -/

/-- **`s4:3.3` (Theorem 3.3, fixed Airy-window tightness of the negative weighted mass).** -/
def SpinS4_3_3 : Prop :=
  ∀ {C_x : ℝ}, 0 < C_x →
    ∃ (C c_exp R₀ : ℝ), 0 < C ∧ 0 < c_exp ∧ 0 < R₀ ∧
      ∀ {R : ℝ}, R₀ ≤ R →
        ∀ᶠ n' : ℝ in atTop,
          let c := n' + 1
          let ε := n' ^ (-(2 / 3 : ℝ))
          let a := n' / 12
          ∀ {x₁ : ℝ} {Φ : ℝ × ℝ → ℝ},
            |x₁ - xiStar| ≤ C_x * ε → SpinSlackHyp c x₁ Φ →
              ∫ p in {q : ℝ × ℝ | (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4 < x₁ ^ 2 ∧
                  spinLongDist q ≤ xiStar - ε * R},
                max (-spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2 ≤
                  C * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))

/-- **`s4:3.4` (Theorem 3.4, local scalar vanishing implies global scalar vanishing).** -/
def SpinS4_3_4 : Prop :=
  ∀ {C_x : ℝ} {cSeq : ℕ → ℝ} {xSeq : ℕ → ℝ} {ΦSeq : ℕ → ℝ × ℝ → ℝ},
    0 < C_x →
    Tendsto cSeq atTop atTop →
    (∀ k, let n := cSeq k - 1; |xSeq k - xiStar| ≤ C_x * n ^ (-(2 / 3 : ℝ)) ∧
      SpinSlackHyp (cSeq k) (xSeq k) (ΦSeq k)) →
    (∀ R : ℝ, 0 < R →
      Tendsto (fun k => ∫ u in Icc (-R) R, |spinFProfile (cSeq k) (ΦSeq k) u|) atTop (𝓝 0)) →
    Tendsto (fun k => spinCalNorm (cSeq k) (ΦSeq k)) atTop (𝓝 0)

/-! ### Section 4 statements (`s4:4.1`–`s4:4.3`) -/

/-- **`s4:4.1` (Lemma 4.1, charge-uniform truncated weighted inverse and polynomial strip bound).** -/
def SpinS4_4_1 : Prop :=
  ∀ {r₀ V : ℝ}, 0 < r₀ → 0 < V →
    ∃ (C_r C_V c₀ : ℝ), 0 < C_r ∧ 0 < C_V ∧ 40 ≤ c₀ ∧
      ∀ {c : ℝ}, c₀ ≤ c →
        let n := c - 1
        let a := n / 12
        let ε := n ^ (-(2 / 3 : ℝ))
        let N := Nat.ceil (Real.log n)
        let γN := spinGamma a * (spinLambda a ^ (N - 1))⁻¹
        ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ → spinM2 a Φ = 1 →
          ∫ p in {q : ℝ × ℝ | r₀ ≤ q.1 ∧ r₀ ≤ q.2},
            |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 ≤
              C_r * ((N : ℝ) + 1) * Real.exp (-4 * π * r₀ * (N : ℝ)) ∧
          ∫ p in {q : ℝ × ℝ | r₀ ≤ q.1 ∧ r₀ ≤ q.2},
            |spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 ≤ C_r ∧
          ∀ (d : ℝ) (b : ℂ), |d| ≤ V * Real.sqrt ε → |b.im| ≤ γN / 2 →
            ‖spinTruncInvC a N Φ (b + (d : ℂ)) (b - (d : ℂ))‖ ≤
              C_V * (N : ℝ) ^ 2 * (1 + |b.re| ^ 2) ^ 2

/-- **`s4:4.2` (Lemma 4.2, uniform adaptive transverse-slice normal family).** -/
def SpinS4_4_2 : Prop :=
  ∀ {V : ℝ}, 0 < V →
    ∀ {R : ℝ}, 0 < R →
      ∃ (C_RV c₀ : ℝ), 0 < C_RV ∧ 40 ≤ c₀ ∧
        ∀ {c : ℝ}, c₀ ≤ c →
          let n := c - 1
          let a := n / 12
          let N := Nat.ceil (Real.log n)
          ∀ {Φ : ℝ × ℝ → ℝ} {χ : ℝ → ℝ},
            SpinTestClass a Φ → spinM2 a Φ = 1 →
            Measurable χ → (∀ v, 0 ≤ χ v ∧ χ v ≤ 1) → (∀ v, V < |v| → χ v = 0) →
            DifferentiableOn ℂ (spinHProfile c N Φ χ) (Metric.closedBall (0 : ℂ) R) ∧
            (∀ ζ ∈ Metric.closedBall (0 : ℂ) R, ‖spinHProfile c N Φ χ ζ‖ ≤ C_RV)

/-- **`s4:4.3` (Theorem 4.3, global non-vanishing and restricted observability).** -/
def SpinS4_4_3 : Prop :=
  ∀ {C₀ : ℝ} {aJ bJ : ℝ}, 0 < C₀ → C₀ < aJ → aJ < bJ →
    ∃ (κ_J κ_obs c₀ : ℝ), 0 < κ_J ∧ 0 < κ_obs ∧ 40 ≤ c₀ ∧
      ∀ {c x₁ : ℝ}, c₀ ≤ c →
        let n := c - 1
        let ε := n ^ (-(2 / 3 : ℝ))
        |x₁ - xiStar| ≤ C₀ * ε →
        ∀ {Φ : ℝ × ℝ → ℝ}, SpinSlackHyp c x₁ Φ →
          κ_J ≤ ∫ u in Icc aJ bJ, spinFProfile c Φ u ∧
          κ_obs * spinM2 (n / 12) Φ ≤ spinCalNorm c Φ

/-! ### Section 5 statements (`s4:5.1`, `s4:5.2`) -/

/-- **`s4:5.1` (Theorem 5.1, source-independent scalar complex Langer majorant).** -/
def SpinS4_5_1 : Prop :=
  ∀ {κ : ℝ}, 0 < κ →
    ∃ (c₀ C_κ C₂ r_d cA : ℝ), 40 ≤ c₀ ∧ 0 < C_κ ∧ 0 < C₂ ∧ 0 < r_d ∧ 0 < cA ∧
      (∀ {R : ℝ}, 0 < R → ∃ C_κR : ℝ, 0 < C_κR ∧
        ∀ {c x₁ : ℝ}, c₀ ≤ c →
          let n := c - 1
          let a := n / 12
          ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ →
            (∀ b : ℝ, x₁ ≤ b → 0 ≤ (spinGcal a Φ (b : ℂ)).re) →
            κ * spinM2 a Φ ≤ spinCalNorm c Φ → spinCalNorm c Φ ≤ C_κ * spinM2 a Φ →
            AnalyticOnNhd ℂ (spinPtilde c Φ) (Metric.ball (0 : ℂ) (r_d * n ^ (2 / 3 : ℝ))) ∧
            (∀ u : ℝ, u ∈ Metric.ball (0 : ℝ) (r_d * n ^ (2 / 3 : ℝ)) →
              (spinPtilde c Φ (u : ℂ)).im = 0) ∧
            (∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ (cA * n ^ (1 / 3 : ℝ)) ^ 2 →
              0 < (u ^ (1 / 2 : ℂ)).re →
              ‖spinPtilde c Φ u‖ ≤ C_κ * spinAiryEnv u *
                Real.exp (C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re) /
                  (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)) ∧
            (∀ u : ℂ, ‖u‖ ≤ R → ‖u‖ ≤ (cA * n ^ (1 / 3 : ℝ)) ^ 2 →
              ‖spinPtilde c Φ u‖ ≤ C_κR))

/-- **`s4:5.2` (Proposition 5.2, exact Langer Jacobian identity and truncated real-integral bound).** -/
def SpinS4_5_2 : Prop :=
  ∀ {C₀ κ : ℝ}, 0 < C₀ → 0 < κ →
    ∃ (r₀ C_κ c₀ : ℝ), 0 < r₀ ∧ r₀ < xiStar ∧ 0 < C_κ ∧ 40 ≤ c₀ ∧
      ∀ {c x₁ : ℝ}, c₀ ≤ c →
        let n := c - 1
        let a := n / 12
        let ε := n ^ (-(2 / 3 : ℝ))
        |x₁ - xiStar| ≤ C₀ * ε →
        ∀ {Φ : ℝ × ℝ → ℝ}, SpinSlackHyp c x₁ Φ →
          κ ≤ spinCalNorm c Φ →
          let I_b := Icc (xiStar - r₀) (xiStar + r₀)
          let u_hi := virasoroUChart n ((xiStar - r₀) ^ 2 / 3)
          let u_lo := virasoroUChart n ((xiStar + r₀) ^ 2 / 3)
          (∫ u in Icc u_lo u_hi, (spinPtilde c Φ (u : ℂ)).re) =
            (spinCalNorm c Φ)⁻¹ *
              ∫ b in I_b, a * Real.exp (n * spinL b) * (spinGcal a Φ (b : ℂ)).re ∧
          (∫ u in Icc u_lo u_hi, (spinPtilde c Φ (u : ℂ)).re) ≤
            C_κ * n ^ (-(2 / 3 : ℝ)) * Real.log n

/-! ### Section 6 statements (`s4:6.1`, `s4:4.4`) and Headline Theorem S4 (`s4:S4`) -/

/-- **`s4:6.1` (Theorem 6.1, robust scalar transfer of the Langer-disc argument under a small
positive integral defect).** -/
def SpinS4_6_1 : Prop :=
  ∃ (C_minus c₁ : ℝ), 0 < C_minus ∧ 40 ≤ c₁ ∧
    ∀ {c : ℝ}, c₁ ≤ c →
      let n := c - 1
      let a := n / 12
      let T_minus := xiBar * n + Aopt * n ^ ((1 : ℝ) / 3) - C_minus * Real.log n
      0 < T_minus ∧
      (∀ {T : ℝ}, T < T_minus → ∀ {Φ : ℝ × ℝ → ℝ}, ¬ SpinIsSlackFeasible a T Φ) ∧
      n / lambdaV + Aopt * n ^ ((1 : ℝ) / 3) - C_minus * Real.log n ≤ spinDeltaL c

/-- **`s4:4.4` (Corollary 6.2, sharp Airy coefficient on the Liouville cone relative to Section 0.2).** -/
def SpinS4_4_4 : Prop :=
  ∃ (C_minus C_plus c₁ : ℝ), 0 < C_minus ∧ 0 < C_plus ∧ 40 ≤ c₁ ∧
    ∀ {c : ℝ}, c₁ ≤ c →
      (c - 1) / lambdaV + Aopt * (c - 1) ^ ((1 : ℝ) / 3) - C_minus * Real.log (c - 1) ≤
        spinDeltaL c ∧
      spinDeltaL c ≤ spinDeltaSpin c ∧
      spinDeltaSpin c ≤ virasoroProblem.Delta_best (c - 1) ∧
      virasoroProblem.Delta_best (c - 1) ≤
        (c - 1) / lambdaV + Aopt * (c - 1) ^ ((1 : ℝ) / 3) + C_plus

/-- **`s4:S4` (Theorem S4, continuous-spin sharp Airy coefficient on the Liouville cone and
wider cones).**
States all conclusions of `spinning_s4.tex` Theorem S4:
1. Two-sided chain `(c - 1)/Λ_V + A_opt (c - 1)^{1/3} - C_- log(c - 1) ≤ Δ_Liouv ≤ Δ_spin ≤ Δ_best^{spinless} ≤ (c - 1)/Λ_V + A_opt (c - 1)^{1/3} + C_+`;
2. Positive threshold `T_- > 0` and slack-feasible obstruction `(s4:eSlack)` (`¬ SpinIsSlackFeasible a T Φ` for `T < T_-`);
3. Strong duality & attainment (`0 < T_L`, `Δ_Liouv = a + τ_max(Ω_L)`, attained by a crossing measure);
4. Wider-cone extension for every `η ∈ [0, 1/2)` using the Fourier-analytic `spinWiderThr`. -/
def SpinS4 : Prop :=
  ∃ (C_minus C_plus c₁ : ℝ), 0 < C_minus ∧ 0 < C_plus ∧ 40 ≤ c₁ ∧
    ∀ {c : ℝ}, c₁ ≤ c →
      let n := c - 1
      let a := n / 12
      let T_minus := xiBar * n + Aopt * n ^ ((1 : ℝ) / 3) - C_minus * Real.log n
      0 < T_minus ∧
      n / lambdaV + Aopt * n ^ ((1 : ℝ) / 3) - C_minus * Real.log n ≤ spinDeltaL c ∧
      spinDeltaL c ≤ spinDeltaSpin c ∧
      spinDeltaSpin c ≤ virasoroProblem.Delta_best n ∧
      virasoroProblem.Delta_best n ≤ n / lambdaV + Aopt * n ^ ((1 : ℝ) / 3) + C_plus ∧
      (∀ {T : ℝ}, T < T_minus → ∀ {Φ : ℝ × ℝ → ℝ}, ¬ SpinIsSlackFeasible a T Φ) ∧
      0 < spinThrInf (SpinTestClass a) liouvilleCone a ∧
      spinDeltaL c = a + spinTauMax a liouvilleCone ∧
      (∃ meas : SpinCrossingMeasure a,
        meas.ν (liouvilleCone (spinTauMax a liouvilleCone))ᶜ = 0) ∧
      (∀ {η : ℝ}, 0 ≤ η → η < 1 / 2 →
        spinDeltaL c ≤ a + spinWiderThr (SpinTestClass a) a η ∧
        spinDeltaSpin c ≤ a + spinWiderThr (SpinTestClassJ a) a η ∧
        a + spinWiderThr (SpinCertifiedClass a) a η ≤ virasoroProblem.Delta_best n)

end FormalResearch.ModularBootstrap.Spin
