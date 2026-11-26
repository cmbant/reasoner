module

public import FormalResearch.ModularBootstrap.Spin.SpinDDefs
public import FormalResearch.ModularBootstrap.Spin.Statements

/-!
# SPIN-D statements (`spinning_dual.tex`), as `Prop`s

Skeleton index of all eight results of `CFT/modular_bootstrap/paper/spinning_dual.tex`, plus the
LP2 dependency `DslReserve` (`dsl:reserve` in `dual_spectrum_limit.tex`):

| paper label | `Prop` | status |
|---|---|---|
| `sd:M` | `SpinDM` | proved (`SpinDMP.lean`) |
| `sd:P` | `SpinDP` | proved (`SpinDMP.lean`) |
| `sd:SD` | `SpinDSD` | stated as `Prop` |
| `sd:W` | `SpinDW` | stated as `Prop` |
| `sd:V` | `SpinDV` | stated as `Prop` |
| `sd:A` | `SpinDA` | stated as `Prop` |
| `sd:LP` (i), (ii) | `SpinDLPi`, `SpinDLPii`, `SpinDLP` | (i) proved (`SpinDLPi.lean`), (ii) assembled from (i)+`sd:P`+`sd:SD` |
| `sd:R` | `SpinDR` | proved (`SpinDAssembly.lean`) |
| `dsl:reserve` (LP2) | `DslReserve` | stated as `Prop` |
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.LP
open FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight
open FormalResearch.ModularBootstrap.Upper.Rigidity

/-- **`sd:M`** (Lemma SD-M: majorant and thermal tests in the spin-resolving class).
For `a ≥ 2` (`c ≥ 25`), `0 < T₀`, `0 < β₀ ≤ 1/2` with `t0 β₀ ≤ T₀`:
- (a) the radial lift `Φ_h` of `hMaj a β₀` lies in `SpinTestClassJ a ∩ SpinCertifiedClass a`,
  has `Φ_vac = -C₀ < 0`, and dominates `w_* > 0` on `{t_L + t_R ≥ T₀}`;
- (b) every swap-symmetrised thermal test `𝔛_β` lies in `SpinTestClassJ a` with vacuum value
  `X_{β,vac}`;
- (c) for every `B ≥ 0` and `m > 0`, `e^{-2π m t} / w_*(t)` is bounded on `[-2B, ∞)` and tends to
  `0` as `t → ∞`, and `|X_β| ≤ C e^{-2π m_β t}` on `E_B`. -/
def SpinDM : Prop :=
  ∀ {a : ℝ}, 2 ≤ a →
    (∀ {T₀ β₀ : ℝ}, 0 < T₀ → 0 < β₀ → β₀ ≤ 1 / 2 → t0 β₀ ≤ T₀ →
      SpinTestClassJ a (spinRadialLift (hMaj a β₀)) ∧
      SpinCertifiedClass a (spinRadialLift (hMaj a β₀)) ∧
      spinPhiVac a (spinRadialLift (hMaj a β₀)) = -dualC0 a β₀ ∧
      0 < dualC0 a β₀ ∧
      ∀ tL tR : ℝ, T₀ ≤ tL + tR →
        0 < wStar a β₀ (tL + tR) ∧ wStar a β₀ (tL + tR) ≤ hMaj a β₀ (tL + tR)) ∧
    (∀ {βL βR : ℝ}, 0 < βL → 0 < βR →
      SpinTestClassJ a (spinSymThermalX_r βL βR) ∧
      spinPhiVac a (spinSymThermalX_r βL βR) = spinThermalXVac a βL βR) ∧
    (∀ {β₀ B : ℝ}, 0 < β₀ → β₀ ≤ 1 / 2 → 0 ≤ B →
      (∀ {m : ℝ}, 0 < m →
        (∃ C : ℝ, ∀ t : ℝ, -2 * B ≤ t → Real.exp (-2 * π * m * t) / wStar a β₀ t ≤ C) ∧
        Tendsto (fun t : ℝ => Real.exp (-2 * π * m * t) / wStar a β₀ t) atTop (𝓝 0)) ∧
      (∀ {βL βR : ℝ}, 0 < βL → 0 < βR →
        ∃ C : ℝ, ∀ p ∈ spinConeB B,
          |spinThermalX βL βR p.1 p.2| ≤
            C * Real.exp (-2 * π * min (min βL βR) (min βL⁻¹ βR⁻¹) * (p.1 + p.2))))

/-- **`sd:P`** (Lemma SD-P: weak duality for the certified class `\mathcal B`).
For `a ≥ 2`, `B ≥ 0`, `τ > 0`, and a positive crossing measure `ν` carried by
`X ⊆ E_B ∩ {t_L + t_R ≥ τ}`:
- every `Φ ∈ SpinCertifiedT a` is `ν`-integrable with `∫ Φ dν = -Φ_vac`;
- every `𝔛_β` (`β_L, β_R > 0`) is `ν`-integrable with `∫ 𝔛_β dν = -X_{β,vac}`;
- the joint Laplace transform `∫ e^{-2π(β_L t_L + β_R t_R)} dν` is finite for all `β_L, β_R > 0`. -/
def SpinDP : Prop :=
  ∀ {a B τ : ℝ}, 2 ≤ a → 0 ≤ B → 0 < τ →
    ∀ {X : Set (ℝ × ℝ)}, X ⊆ spinConeB B ∩ {p : ℝ × ℝ | τ ≤ p.1 + p.2} →
    ∀ meas : SpinCrossingMeasureOn a X,
      (∀ Φ, SpinCertifiedT a Φ → Integrable Φ meas.ν ∧ ∫ p, Φ p ∂meas.ν = -spinVacT a Φ) ∧
      (∀ {βL βR : ℝ}, 0 < βL → 0 < βR →
        Integrable (fun p : ℝ × ℝ => spinSymThermalX βL βR p.1 p.2) meas.ν ∧
        ∫ p : ℝ × ℝ, spinSymThermalX βL βR p.1 p.2 ∂meas.ν = -spinThermalXVac a βL βR) ∧
      (∀ {βL βR : ℝ}, 0 < βL → 0 < βR →
        Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * (βL * p.1 + βR * p.2))) meas.ν)

/-- **`sd:SD`** (Theorem SD: strong duality and attainment on closed swap-invariant cones
`X_τ = F ∪ Ω(τ)` in `E_B`).
For `a ≥ 2`, `B ≥ 0`, closed swap-invariant `Ω ⊆ E_B`, compact swap-invariant
`F ⊆ Ω ∩ {t_L + t_R > 0}` (possibly empty), with `T := spinCertifiedThr a Ω F > 0`:
- `T` is the maximum of `{τ > 0 : ∃ crossing measure on F ∪ Ω(τ)}`, attained by a swap-invariant
  measure;
- scalar comparison `T ≤ constrainedThreshold virasoroProblem (12 * a) ((t_L + t_R) '' F)`;
- in the quadrant `Ω = E_0` with `F = ∅`, `0 < T_Ω = T_Ω^J = T_Ω^{\mathcal B}`. -/
def SpinDSD : Prop :=
  (∀ {a B : ℝ}, 2 ≤ a → 0 ≤ B →
    ∀ {Ω F : Set (ℝ × ℝ)}, IsClosed Ω → IsSwapInvariantSet Ω → Ω ⊆ spinConeB B →
      IsCompact F → IsSwapInvariantSet F → F ⊆ Ω ∩ {p : ℝ × ℝ | 0 < p.1 + p.2} →
      0 < spinCertifiedThr a Ω F →
      IsGreatest {τ : ℝ | 0 < τ ∧ Nonempty (SpinCrossingMeasureOn a (F ∪ spinConeSlice Ω τ))}
        (spinCertifiedThr a Ω F) ∧
      (∃ meas : SpinCrossingMeasureOn a (F ∪ spinConeSlice Ω (spinCertifiedThr a Ω F)),
        IsSwapInvariantMeasure meas.ν) ∧
      spinCertifiedThr a Ω F ≤
        constrainedThreshold virasoroProblem (12 * a) ((fun p : ℝ × ℝ => p.1 + p.2) '' F)) ∧
  (∀ {a : ℝ}, 2 ≤ a →
    0 < spinThrInf (SpinTestClass a) liouvilleCone a ∧
    spinThrInf (SpinTestClass a) liouvilleCone a = spinThrInf (SpinTestClassJ a) liouvilleCone a ∧
    spinThrInf (SpinTestClassJ a) liouvilleCone a = spinCertifiedThr a (spinConeB 0) ∅)

/-- **`sd:W`** (Proposition SD-W: weak duality for the full continuous class `\overline{\mathcal A}_{\rm spin}`
on the quadrant). -/
def SpinDW : Prop :=
  ∀ {a : ℝ}, 2 ≤ a → ∀ meas : SpinCrossingMeasure a,
    ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ →
    ∀ {T : ℝ}, 0 < T → (∀ p ∈ liouvilleCone T, 0 ≤ spinEvalT Φ p) →
      Integrable (spinEvalT Φ) meas.ν ∧
      ∫ p, spinEvalT Φ p ∂meas.ν ≤ -spinPhiVac a Φ ∧
      ((∀ᵐ p ∂meas.ν, 0 ≤ spinEvalT Φ p) → spinPhiVac a Φ ≤ 0) ∧
      ((∀ᵐ p ∂meas.ν, 0 ≤ spinEvalT Φ p) → 0 ≤ spinPhiVac a Φ →
        spinPhiVac a Φ = 0 ∧ ∀ᵐ p ∂meas.ν, spinEvalT Φ p = 0)

/-- **`sd:V`** (Lemma SD-V: Mehler continuity on `\overline{\mathcal A}_{\rm spin}`).
For `a ≥ 2`, there is `C_a > 0` such that for every `D_4`-invariant bounded measurable `h`
(`|h| ≤ M`) and every `Φ ∈ \overline{\mathcal A}_{\rm spin}`:
- `|∬ (A_r Φ) h V_1 ⊗ V_1| ≤ C_a M M_2[Φ]` uniformly for `r ∈ [1/2, 1)`;
- `lim_{r ↑ 1} ∬ (A_r Φ) h V_1 ⊗ V_1 = ∬ Φ h V_1 ⊗ V_1`. -/
def SpinDV : Prop :=
  ∀ {a : ℝ}, 2 ≤ a →
    ∃ C : ℝ, 0 < C ∧
      ∀ {h : ℝ × ℝ → ℝ} {M : ℝ}, 0 ≤ M → Measurable h → IsD4Invariant h → (∀ p, |h p| ≤ M) →
      ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ →
        (∀ r ∈ Ico (1 / 2 : ℝ) 1,
          |∫ p : ℝ × ℝ, spinMehlerOp r Φ p * h p * spinV1 a p.1 * spinV1 a p.2| ≤
            C * M * spinM2 a Φ) ∧
        Tendsto (fun r => ∫ p : ℝ × ℝ, spinMehlerOp r Φ p * h p * spinV1 a p.1 * spinV1 a p.2)
          (𝓝[<] 1) (𝓝 (∫ p : ℝ × ℝ, Φ p * h p * spinV1 a p.1 * spinV1 a p.2))

/-- **`sd:A`** (Proposition SD-A: attainment of the continuous-spin test infimum on the quadrant
with optional compact prescribed sites `F`, and complementary slackness). -/
def SpinDA : Prop :=
  ∀ {a : ℝ}, 2 ≤ a →
    ∀ {F : Set (ℝ × ℝ)}, IsCompact F → IsSwapInvariantSet F →
      F ⊆ spinConeB 0 ∩ {p : ℝ × ℝ | 0 < p.1 + p.2} →
      let TF := sInf {T : ℝ | 0 < T ∧ ∃ Φ, SpinTestClass a Φ ∧ 0 < spinPhiVac a Φ ∧
        ∀ p ∈ F ∪ spinConeSlice (spinConeB 0) T, 0 ≤ spinEvalT Φ p}
      ∃ Φs : ℝ × ℝ → ℝ,
        SpinTestClass a Φs ∧
        spinM2 a Φs = 1 ∧
        spinPhiVac a Φs = 0 ∧
        (∀ p ∈ F ∪ spinConeSlice (spinConeB 0) TF, 0 ≤ spinEvalT Φs p) ∧
        (∀ meas : SpinCrossingMeasureOn a (F ∪ spinConeSlice (spinConeB 0) TF),
          ∀ᵐ p ∂meas.ν, spinEvalT Φs p = 0)

/-- **`sd:LP`(i)** (Theorem SD-LP, part (i): finite-order odd Laguerre infeasibility iff existence
of a swap-invariant crossing measure on closed swap-invariant `X ⊆ E_B ∩ {t ≥ T₀}`). -/
def SpinDLPi : Prop :=
  ∀ {a B T₀ : ℝ}, 2 ≤ a → 0 ≤ B → 0 < T₀ →
    ∀ {X : Set (ℝ × ℝ)}, IsClosed X → IsSwapInvariantSet X →
      X ⊆ spinConeB B ∩ {p : ℝ × ℝ | T₀ ≤ p.1 + p.2} →
      ((∀ N q, ¬ spinOddLagFeasible a N X q) ↔
        ∃ meas : SpinCrossingMeasureOn a X, IsSwapInvariantMeasure meas.ν)

/-- **`sd:LP`(ii)** (Theorem SD-LP, part (ii): `T_{Ω,F}^{[∞]} = T_{Ω,F}^{\mathcal B} = τ_{\max}`). -/
def SpinDLPii : Prop :=
  ∀ {a B : ℝ}, 2 ≤ a → 0 ≤ B →
    ∀ {Ω F : Set (ℝ × ℝ)}, IsClosed Ω → IsSwapInvariantSet Ω → Ω ⊆ spinConeB B →
      IsCompact F → IsSwapInvariantSet F → F ⊆ Ω ∩ {p : ℝ × ℝ | 0 < p.1 + p.2} →
      0 < spinCertifiedThr a Ω F →
      spinLagThrInf a Ω F = ENNReal.ofReal (spinCertifiedThr a Ω F) ∧
      IsGreatest {τ : ℝ | 0 < τ ∧ Nonempty (SpinCrossingMeasureOn a (F ∪ spinConeSlice Ω τ))}
        (spinCertifiedThr a Ω F)

/-- **`sd:LP`** (Theorem SD-LP, parts (i) and (ii) combined). -/
def SpinDLP : Prop := SpinDLPi ∧ SpinDLPii

/-- **`sd:R`** (Corollary SD-R: resolving spin does not change the Airy distribution of dimensions).
For any sequence `c_j → ∞` (`c_j ≥ 25`) and positive crossing measures `ν_j` on subsets of
`E_{B_j} ∩ {t_L + t_R ≥ τ_j}` (`τ_j > 0`, `B_j ≥ 0`) satisfying the scalar gap condition
`GapCondition (c_j - 1) τ_j`, the rescaled spectral measures of the dimension marginals
`ν_j^{rad} = (t_L + t_R)_* ν_j` satisfy `SigmaConclusion` (in particular vague convergence to
`airyMeasure = ∑_k Ai'(a_k)^{-2} δ_{a_k}`). -/
def SpinDR : Prop :=
  ∀ (cSeq τSeq BSeq : ℕ → ℝ),
    Tendsto cSeq atTop atTop →
    (∀ j, 25 ≤ cSeq j) →
    (∀ j, 0 < τSeq j) →
    (∀ j, 0 ≤ BSeq j) →
    GapCondition (fun j => cSeq j - 1) τSeq →
    ∀ (meas : ∀ j, SpinCrossingMeasureOn ((cSeq j - 1) / 12)
      (spinConeB (BSeq j) ∩ {p : ℝ × ℝ | τSeq j ≤ p.1 + p.2})),
      SigmaConclusion (fun j =>
        spectralMeasure virasoroProblem (cSeq j - 1) (spinRadMarginal (meas j).ν))

/-- **`dsl:reserve`** (Theorem LP-R, `dual_spectrum_limit.tex`, work package LP2; stated here as
its own `Prop` for the `d = 2` swap-symmetric spinning setting).
Given a positive measure `σ` on a closed swap-invariant `X ⊆ E_B ∩ {t ≥ T₀}` (`T₀ > 0`) with
`∫ e^{-2π s (t_L + t_R)} dσ < ∞` for some `0 < s < 1`, there exists a crossing measure `ν ≥ σ`
on `X` iff `∫ e^{-2π t} q dσ ≤ -Φ_vac(e^{-2π t} q)` for all `q ∈ ⋃_N \mathcal Q_N` nonnegative
on `X`. -/
def DslReserve : Prop :=
  ∀ {a B T₀ s : ℝ}, 2 ≤ a → 0 ≤ B → 0 < T₀ → 0 < s → s < 1 →
    ∀ {X : Set (ℝ × ℝ)}, IsClosed X → IsSwapInvariantSet X →
      X ⊆ spinConeB B ∩ {p : ℝ × ℝ | T₀ ≤ p.1 + p.2} →
    ∀ (σ : Measure (ℝ × ℝ)), σ Xᶜ = 0 → IsSwapInvariantMeasure σ →
      Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * s * (p.1 + p.2))) σ →
      ((∃ meas : SpinCrossingMeasureOn a X, IsSwapInvariantMeasure meas.ν ∧ σ ≤ meas.ν) ↔
        ∀ N q, q ∈ spinOddLagPolySpace N → (∀ p ∈ X, 0 ≤ q p) →
          ∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) * q p ∂σ ≤
            -spinVacT a (fun p => Real.exp (-2 * π * (p.1 + p.2)) * q p))

end FormalResearch.ModularBootstrap.Spin
