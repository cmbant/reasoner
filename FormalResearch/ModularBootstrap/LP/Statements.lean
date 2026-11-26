module

public import FormalResearch.ModularBootstrap.LP.DerivLimit
public import FormalResearch.ModularBootstrap.LP.PositiveRay
public import FormalResearch.ModularBootstrap.LP.LaguerreSharp

/-!
# LP1 target statements, as `Prop`s

Index of the Paper II targets of work package LP1 (`CFT/modular_bootstrap/paper/dual_spectrum.tex`,
`dual_spectrum_limit.tex`).  Each target is stated once here as a closed `Prop` (so that a reader can
check the quantifiers in one place) and proved by the theorem of its home module (`*_holds`).  Nothing
is re-proved here, and no hypothesis restates a conclusion.  The status table is in `LP/LP1_DESIGN.md`.

| paper label | statement | home theorem |
|---|---|---|
| `ds:mom` (abstract odd family, Laguerre instance) | `DsMom`, `DsMomLaguerre` | `ds_mom`, `ds_mom_laguerre` |
| `ds:mom`, Laguerre constant `C_w = (2+w)/(2π)` | `DsMomLaguerreConst` | `lagP_oddFam_sharp` |
| `ds:mom`, mass bound | `DsMomMass` | `ds_mom_mass` |
| `dsl:poly-compact` | `DslPolyCompact` | `poly_compact`, `poly_compact_invariant` |
| `dsl:positive-ray` | `DslPositiveRay` | `positive_ray` |
| `ds:cay` | `DsCay` | `ds_cay_series`, `ds_cay_iff` |
| `ds:cont` | `DsCont` (real analytic `v`) | `ds_cont`, `ds_cont_complex` |
| `ds:LP` (i)-(iii) | `DsLPi`, `DsLPii`, `DsLPiii` | `ds_LP_i`, `ds_LP_ii`, `ds_LP_iii` |
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.Duality
  FormalResearch.ModularBootstrap.FixedWeight

namespace FormalResearch.ModularBootstrap.LP

/-- `ds:mom` for an abstract odd family `p_k` with the growth bounds `OddFam`. -/
def DsMom : Prop :=
  ∀ {C : ℝ} {p : ℕ → C(ℝ, ℝ)}, OddFam C p → ∀ (μ₀ : Measure ℝ), μ₀ (Iio 0) = 0 →
    Integrable (fun t => Real.exp (π * t)) μ₀ → ∀ {M : ℝ}, 0 ≤ M →
    ∃ C₁ : ℝ, 0 < C₁ ∧
      (∀ μ : Measure ℝ, μ (Iio 0) = 0 → μ univ ≤ ENNReal.ofReal M → ∀ K : ℕ,
        (∀ k ≤ K, Integrable (fun t : ℝ => t ^ k) μ) →
        (∀ k ≤ K, Odd k → ∫ t, p k t ∂μ = ∫ t, p k t ∂μ₀) →
        ∀ k : ℕ, 1 ≤ k → k + 1 ≤ K → ∫ t, t ^ k ∂μ ≤ (C₁ * k) ^ k) ∧
      (∀ μ : Measure ℝ, μ (Iio 0) = 0 → μ univ ≤ ENNReal.ofReal M →
        (∀ k : ℕ, Integrable (fun t : ℝ => t ^ k) μ) →
        (∀ k : ℕ, Odd k → ∫ t, p k t ∂μ = ∫ t, p k t ∂μ₀) →
        Integrable (fun t => Real.exp (t / (2 * Real.exp 1 * C₁))) μ ∧
          ∫ t, Real.exp (t / (2 * Real.exp 1 * C₁)) ∂μ ≤ M + 1)

theorem dsMom_holds : DsMom := fun hF μ₀ hμ₀ hint _ hM => ds_mom hF μ₀ hμ₀ hint hM

/-- `ds:mom` for the monic Laguerre polynomials `P_k = lagP w k`, `w > 0`. -/
def DsMomLaguerre : Prop :=
  ∀ {w : ℝ}, 0 < w → ∀ (μ₀ : Measure ℝ), μ₀ (Iio 0) = 0 →
    Integrable (fun t => Real.exp (π * t)) μ₀ → ∀ {M : ℝ}, 0 ≤ M →
    ∃ C₁ : ℝ, 0 < C₁ ∧
      (∀ μ : Measure ℝ, μ (Iio 0) = 0 → μ univ ≤ ENNReal.ofReal M → ∀ K : ℕ,
        (∀ k ≤ K, Integrable (fun t : ℝ => t ^ k) μ) →
        (∀ k ≤ K, Odd k → ∫ t, lagP w k t ∂μ = ∫ t, lagP w k t ∂μ₀) →
        ∀ k : ℕ, 1 ≤ k → k + 1 ≤ K → ∫ t, t ^ k ∂μ ≤ (C₁ * k) ^ k) ∧
      (∀ μ : Measure ℝ, μ (Iio 0) = 0 → μ univ ≤ ENNReal.ofReal M →
        (∀ k : ℕ, Integrable (fun t : ℝ => t ^ k) μ) →
        (∀ k : ℕ, Odd k → ∫ t, lagP w k t ∂μ = ∫ t, lagP w k t ∂μ₀) →
        Integrable (fun t => Real.exp (t / (2 * Real.exp 1 * C₁))) μ ∧
          ∫ t, Real.exp (t / (2 * Real.exp 1 * C₁)) ∂μ ≤ M + 1)

theorem dsMomLaguerre_holds : DsMomLaguerre := fun hw μ₀ hμ₀ hint _ hM =>
  ds_mom_laguerre hw μ₀ hμ₀ hint hM

/-- `ds:mom`, Laguerre clause: the monic Laguerre family at weight `w > 0` satisfies the hypotheses of
`ds:mom` with the paper's constant `C_w = (2+w)/(2π)`. -/
def DsMomLaguerreConst : Prop := ∀ {w : ℝ}, 0 < w → OddFam ((2 + w) / (2 * π)) (lagPC w)

theorem dsMomLaguerreConst_holds : DsMomLaguerreConst := fun hw => lagP_oddFam_sharp hw

/-- info: 'FormalResearch.ModularBootstrap.LP.dsMomLaguerreConst_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dsMomLaguerreConst_holds

/-- `ds:mom`, last sentence: the mass bound from the first odd equation (`T₀ > w/(4π)`). -/
def DsMomMass : Prop :=
  ∀ {w T₀ : ℝ} {μ₀ μ : Measure ℝ}, w / (4 * π) < T₀ → μ (Iio T₀) = 0 →
    Integrable (lagP w 1) μ → ∫ t, lagP w 1 t ∂μ = ∫ t, lagP w 1 t ∂μ₀ →
    μ univ ≤ ENNReal.ofReal ((∫ t, lagP w 1 t ∂μ₀) / (T₀ - w / (4 * π)))

theorem dsMomMass_holds : DsMomMass := fun hT hμ hP hL => ds_mom_mass hT hμ hP hL

/-- `dsl:poly-compact` for an abstract odd family: a positive functional on `⋃ V_N` satisfying the
reference odd equations is a positive Radon measure with an `e^{εt}` moment; and a finite group
preserving the data gives an invariant measure. -/
def DslPolyCompact.{u} : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {C T₀ : ℝ} {p : ℕ → C(ℝ, ℝ)} {t : C(X, ℝ)} {V : ℕ → Submodule ℝ C(X, ℝ)},
    PolyCompactHyp C p T₀ t V → ∀ (μ₀ : Measure ℝ), μ₀ (Iio 0) = 0 →
    Integrable (fun s => Real.exp (π * s)) μ₀ →
    ∀ (L : polyUnion V →ₗ[ℝ] ℝ), (∀ v : polyUnion V, (∀ x, 0 ≤ v.1 x) → 0 ≤ L v) →
    RefOdd p t V μ₀ L →
    (∃ μ : Measure X, μ.Regular ∧
      (∀ f ∈ FormalResearch.Measure.polyGrowth t, Integrable f μ) ∧
      (∀ v : polyUnion V, ∫ x, v.1 x ∂μ = L v) ∧
      ∃ ε : ℝ, 0 < ε ∧ Integrable (fun x => Real.exp (ε * t x)) μ) ∧
    ∀ (G : Type u) [Group G] [Finite G] [MulAction G X] [ContinuousConstSMul G X],
      (∀ (g : G) (x : X), t (g • x) = t x) →
      (∀ (g : G) (N : ℕ), Odd N → ∀ v ∈ V N, FormalResearch.Measure.actComp g v ∈ V N) →
      (∀ (g : G) (v v' : polyUnion V),
        (v' : C(X, ℝ)) = FormalResearch.Measure.actComp g v → L v' = L v) →
      ∃ μ : Measure X, μ.Regular ∧
        (∀ f ∈ FormalResearch.Measure.polyGrowth t, Integrable f μ) ∧
        (∀ v : polyUnion V, ∫ x, v.1 x ∂μ = L v) ∧
        (∃ ε : ℝ, 0 < ε ∧ Integrable (fun x => Real.exp (ε * t x)) μ) ∧
        ∀ g : G, Measure.map (fun x => g • x) μ = μ

theorem dslPolyCompact_holds : DslPolyCompact.{u} :=
  fun _ _ _ _ _ _ _ _ _ _ _ h μ₀ hμ₀ hint L hL hodd =>
    ⟨poly_compact h μ₀ hμ₀ hint L hL hodd, fun _ _ _ _ _ htg hVg hLg =>
      poly_compact_invariant h μ₀ hμ₀ hint L hL hodd htg hVg hLg⟩

/-- `dsl:positive-ray`: for `w, T₀ > 0` some `p ∈ ⋃ O_N` satisfies `p ≥ 1` on `[T₀, ∞)`. -/
def DslPositiveRay : Prop :=
  ∀ {w T₀ : ℝ}, 0 < w → 0 < T₀ → ∃ (N : ℕ) (p : ℝ → ℝ), p ∈ oddSpan w N ∧ ∀ t, T₀ ≤ t → 1 ≤ p t

theorem dslPositiveRay_holds : DslPositiveRay := fun hw hT₀ => positive_ray hw hT₀

/-- `ds:cay`: the Cayley expansion of the Laplace pairing, and its uniqueness form. -/
def DsCay : Prop :=
  ∀ {w : ℝ}, 0 < w → ∀ {θ : ℝ}, 0 < θ → θ < 1 →
    (∀ {ν ν' : Measure ℝ}, ν (Iio 0) = 0 → ν' (Iio 0) = 0 →
      Integrable (fun t => Real.exp (-2 * Real.pi * sTheta θ * t)) ν →
      Integrable (fun t => Real.exp (-2 * Real.pi * sTheta θ * t)) ν' →
      ((∀ β, sTheta θ < β → β < 1 / sTheta θ → ∫ t, xiW w β t ∂ν = ∫ t, xiW w β t ∂ν') ↔
        ∀ k : ℕ, Odd k → ∫ t, lagPsi w k t ∂ν = ∫ t, lagPsi w k t ∂ν'))

theorem dsCay_holds : DsCay := fun hw _ hθ0 hθ1 _ _ hν hν' hint hint' =>
  ds_cay_iff hw hθ0 hθ1 hν hν' hint hint'

/-- `ds:cont` (real-analytic form): a crossing relation on `(s, 1/s)` against a real-analytic source
`v` on `(0, ∞)`, for a measure on `[0, ∞)` with finite Laplace transform at `s`, extends to all
`β > 0`, with finiteness of the Laplace transform everywhere. -/
def DsCont : Prop :=
  ∀ {w : ℝ} {v : ℝ → ℝ}, AnalyticOnNhd ℝ v (Ioi 0) → ∀ {ν : Measure ℝ}, ν (Iio 0) = 0 →
    ∀ {s : ℝ}, 0 < s → s < 1 → LapFin ν s →
    (∀ β, s < β → β < 1 / s → lapZ ν β + v β = β ^ (-w) * (lapZ ν (1 / β) + v (1 / β))) →
    (∀ β, 0 < β → LapFin ν β) ∧
      ∀ β, 0 < β → lapZ ν β + v β = β ^ (-w) * (lapZ ν (1 / β) + v (1 / β))

theorem dsCont_holds : DsCont := fun hv _ hν _ hs0 hs1 hZs hcross => ds_cont hv hν hs0 hs1 hZs hcross

/-- `ds:LP`(i): no finite odd-Laguerre test is nonnegative on a closed `X ⊆ [T₀, ∞)` with
`g_vac > 0` iff a crossing measure carried by `X` exists. -/
def DsLPi : Prop :=
  ∀ (prob : FixedWeightProblem) {a : ℝ}, prob.totalShift ≤ a → ∀ {T₀ : ℝ}, 0 < T₀ →
    ∀ {X : Set ℝ}, IsClosed X → X ⊆ Ici T₀ →
    ((∀ N p, ¬ OddFeasible prob a N X p) ↔
      ∃ meas : AdmissibleCrossingMeasure prob a, meas.ν Xᶜ = 0)

theorem dsLPi_holds : DsLPi := fun _ _ ha _ hT₀ _ hXc hX => ds_LP_i ha hT₀ hXc hX

/-- `ds:LP`(ii): for closed `F ⊆ [T₀, ∞)`, if `T₀ < T_F^{[∞]} < ∞` then `T_F^{[∞]}` is the largest
`τ` for which a crossing measure carried by `F ∪ [τ, ∞)` exists. -/
def DsLPii : Prop :=
  ∀ (prob : FixedWeightProblem) {cTilde : ℝ}, 0 < cTilde → 12 * prob.totalShift ≤ cTilde →
    ∀ {T₀ : ℝ}, 0 < T₀ → ∀ {F : Set ℝ}, IsClosed F → F ⊆ Ici T₀ →
    ENNReal.ofReal T₀ < thrInf prob (cTilde / 12) F → thrInf prob (cTilde / 12) F < ⊤ →
    IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (F ∪ Ici τ)ᶜ = 0} (thrInf prob (cTilde / 12) F).toReal

theorem dsLPii_holds : DsLPii := fun _ _ hc_pos hc _ hT₀ _ hFc hF hlow hfin =>
  ds_LP_ii hc_pos hc hT₀ hFc hF hlow hfin

/-- `ds:LP`(iii): at every charge with `T_V > 0`, `T_V = T_∅^{[∞]} = lim_N T_∅^{[N]} =
inf_P T_∅^{[2P+1]}`, and `T_V` is the largest gap of a crossing measure. -/
def DsLPiii : Prop :=
  ∀ (prob : FixedWeightProblem) {cTilde : ℝ}, 0 < cTilde → 12 * prob.totalShift ≤ cTilde →
    0 < prob.T_V cTilde →
    thrInf prob (cTilde / 12) ∅ = ENNReal.ofReal (prob.T_V cTilde) ∧
    Tendsto (fun N => thrN prob (cTilde / 12) ∅ N) atTop (𝓝 (ENNReal.ofReal (prob.T_V cTilde))) ∧
    (⨅ P : ℕ, thrN prob (cTilde / 12) ∅ (2 * P + 1)) = ENNReal.ofReal (prob.T_V cTilde) ∧
    IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (Ici τ)ᶜ = 0} (prob.T_V cTilde)

theorem dsLPiii_holds : DsLPiii := fun _ _ hc_pos hc hTV => ds_LP_iii hc_pos hc hTV

/-- info: 'FormalResearch.ModularBootstrap.LP.dsMom_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dsMom_holds

/-- info: 'FormalResearch.ModularBootstrap.LP.dsMomLaguerre_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dsMomLaguerre_holds

/-- info: 'FormalResearch.ModularBootstrap.LP.dsMomMass_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dsMomMass_holds

/-- info: 'FormalResearch.ModularBootstrap.LP.dslPolyCompact_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dslPolyCompact_holds

/-- info: 'FormalResearch.ModularBootstrap.LP.dslPositiveRay_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dslPositiveRay_holds

/-- info: 'FormalResearch.ModularBootstrap.LP.dsCay_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dsCay_holds

/-- info: 'FormalResearch.ModularBootstrap.LP.dsCont_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dsCont_holds

/-- info: 'FormalResearch.ModularBootstrap.LP.dsLPi_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dsLPi_holds

/-- info: 'FormalResearch.ModularBootstrap.LP.dsLPii_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dsLPii_holds

/-- info: 'FormalResearch.ModularBootstrap.LP.dsLPiii_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dsLPiii_holds

end FormalResearch.ModularBootstrap.LP
