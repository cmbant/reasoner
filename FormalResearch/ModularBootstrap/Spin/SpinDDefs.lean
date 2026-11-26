module

public import FormalResearch.ModularBootstrap.Spin.Defs
public import FormalResearch.ModularBootstrap.LP.LaguerreGen
public import FormalResearch.ModularBootstrap.Duality.DualMajorant
public import FormalResearch.ModularBootstrap.Duality.ConstrainedThreshold
public import FormalResearch.ModularBootstrap.Upper.Rigidity.Wiring

/-!
# SPIN-D definitions: cones, general crossing measures, certified & Laguerre classes, Mehler operator

Concrete definitions supporting the eight results of `CFT/modular_bootstrap/paper/spinning_dual.tex`
(`sd:M`, `sd:P`, `sd:SD`, `sd:W`, `sd:V`, `sd:A`, `sd:LP`, `sd:R`), reusing `Spin/Defs.lean`,
`LP/LaguerreGen.lean`, `Duality/DualMajorant.lean`, and `Upper/Rigidity/Wiring.lean`.
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

/-! ### Section 1: Swap invariance and shifted cones `E_B`, `Ω(T)` -/

/-- Swap invariance of a set `S ⊆ ℝ × ℝ` under `(t_L, t_R) ↦ (t_R, t_L)`. -/
def IsSwapInvariantSet (S : Set (ℝ × ℝ)) : Prop :=
  ∀ p : ℝ × ℝ, p ∈ S → p.swap ∈ S

/-- Swap invariance of a measure `ν` on `ℝ × ℝ` under `(t_L, t_R) ↦ (t_R, t_L)`. -/
def IsSwapInvariantMeasure (ν : Measure (ℝ × ℝ)) : Prop :=
  Measure.map Prod.swap ν = ν

/-- Shifted quadrant `E_B = [-B, ∞)²` (`spinning_dual.tex`, Section 1). -/
def spinConeB (B : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | -B ≤ p.1 ∧ -B ≤ p.2}

/-- Gap slice `Ω(T) = Ω ∩ {t_L + t_R ≥ T}`. -/
def spinConeSlice (Ω : Set (ℝ × ℝ)) (T : ℝ) : Set (ℝ × ℝ) :=
  Ω ∩ {p : ℝ × ℝ | T ≤ p.1 + p.2}

lemma isClosed_spinConeB (B : ℝ) : IsClosed (spinConeB B) :=
  (isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_const continuous_snd)

lemma isClosed_spinConeSlice {Ω : Set (ℝ × ℝ)} (hΩ : IsClosed Ω) (T : ℝ) :
    IsClosed (spinConeSlice Ω T) :=
  hΩ.inter (isClosed_le continuous_const (continuous_fst.add continuous_snd))

lemma isSwapInvariantSet_spinConeB (B : ℝ) : IsSwapInvariantSet (spinConeB B) :=
  fun _ ⟨h1, h2⟩ => ⟨h2, h1⟩

lemma isSwapInvariantSet_spinConeSlice {Ω : Set (ℝ × ℝ)} (hΩ : IsSwapInvariantSet Ω) (T : ℝ) :
    IsSwapInvariantSet (spinConeSlice Ω T) :=
  fun p ⟨hpΩ, hsum⟩ => ⟨hΩ p hpΩ, by
    change T ≤ p.2 + p.1
    change T ≤ p.1 + p.2 at hsum
    linarith⟩

lemma spinConeSlice_quadrant (T : ℝ) :
    spinConeSlice (spinConeB 0) T = liouvilleCone T := by
  ext p
  simp [spinConeSlice, spinConeB, liouvilleCone, and_assoc]

/-! ### Section 2: General-support crossing measures `(sd:eSD1)` and dimension marginals -/

/-- Positive two-variable crossing measure carried by `X ⊆ ℝ × ℝ` satisfying `(sd:eSD1)`:
diagonal Laplace finiteness `∫ e^{-2π β (t_L + t_R)} dν < ∞` for all `β > 0`, and
`∫ X_{β_L, β_R} dν = -X_{β_L, β_R, vac}` for all `β_L, β_R > 0`. -/
structure SpinCrossingMeasureOn (a : ℝ) (X : Set (ℝ × ℝ)) where
  ν : Measure (ℝ × ℝ)
  supp : ν Xᶜ = 0
  finite_laplace : ∀ {β : ℝ}, 0 < β →
    Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) ν
  crossing : ∀ {βL βR : ℝ}, 0 < βL → 0 < βR →
    ∫ p : ℝ × ℝ, spinThermalX βL βR p.1 p.2 ∂ν = -spinThermalXVac a βL βR

/-- Convert a quadrant `SpinCrossingMeasure` into `SpinCrossingMeasureOn a (spinConeB 0)`. -/
def SpinCrossingMeasure.toOn {a : ℝ} (meas : SpinCrossingMeasure a) :
    SpinCrossingMeasureOn a (spinConeB 0) where
  ν := meas.ν
  supp := by
    have heq : spinConeB 0 = {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} := by
      ext p; simp [spinConeB]
    rw [heq]; exact meas.supp_quad
  finite_laplace := meas.finite_laplace
  crossing := meas.crossing

/-- Convert a `SpinCrossingMeasureOn a X` with `X ⊆ spinConeB 0` into `SpinCrossingMeasure a`. -/
def SpinCrossingMeasureOn.toQuadrant {a : ℝ} {X : Set (ℝ × ℝ)}
    (hX : X ⊆ spinConeB 0) (meas : SpinCrossingMeasureOn a X) :
    SpinCrossingMeasure a where
  ν := meas.ν
  supp_quad := by
    have hsub : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}ᶜ ⊆ Xᶜ := by
      intro p hp hpX
      apply hp
      have h0 := hX hpX
      simp only [spinConeB, neg_zero, mem_ofPred_eq] at h0
      exact h0
    exact measure_mono_null hsub meas.supp
  finite_laplace := meas.finite_laplace
  crossing := meas.crossing

/-- Total-dimension push-forward (radial marginal) `ν^{rad} = (t_L + t_R)_* ν`. -/
noncomputable def spinRadMarginal (ν : Measure (ℝ × ℝ)) : Measure ℝ :=
  ν.map (fun p : ℝ × ℝ => p.1 + p.2)

lemma spinThermalX_diag_pos {β : ℝ} (hβ : 0 < β) (tL tR : ℝ) :
    spinThermalX β β tL tR = thermalDiff 1 β (tL + tR) := by
  unfold spinThermalX thermalDiff
  have h1 : β * tL + β * tR = β * (tL + tR) := by ring
  have h2 : tL / β + tR / β = (tL + tR) / β := by ring
  have hpow : (β * β) ^ (-(1 / 2 : ℝ)) = β ^ (-(1 : ℝ)) := by
    rw [← pow_two, ← Real.rpow_natCast β 2, ← Real.rpow_mul hβ.le]
    norm_num
  rw [h1, h2, hpow]
  simp only [Nat.cast_one]
  ring_nf

lemma spinThermalXVac_diag_pos (a : ℝ) {β : ℝ} (hβ : 0 < β) :
    spinThermalXVac a β β = virasoroProblem.gVac a (thermalDiff 1 β) := by
  rw [← virasoroProblem_w, virasoroProblem.gVac_thermalDiff a hβ]
  unfold spinThermalXVac spinVacuumV spinVacuumQ
  rw [virasoroProblem_w, virasoroProblem_nullPoly, virasoroProblem_nullPoly]
  have hpow : (β * β) ^ (-(1 / 2 : ℝ)) = β ^ (-(1 : ℝ)) := by
    rw [← pow_two, ← Real.rpow_natCast β 2, ← Real.rpow_mul hβ.le]
    norm_num
  have hexp1 : Real.exp (π * a * β) * Real.exp (π * a * β) = Real.exp (2 * π * a * β) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp2 : Real.exp (π * a * β⁻¹) * Real.exp (π * a * β⁻¹) = Real.exp (2 * π * a / β) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hexp3 : Real.exp (-2 * π * β⁻¹) = Real.exp (-2 * π / β) := by
    rw [div_eq_mul_inv]
  rw [hpow, hexp3]
  simp only [Nat.cast_one]
  calc Real.exp (π * a * β) * (1 - Real.exp (-2 * π * β)) *
          (Real.exp (π * a * β) * (1 - Real.exp (-2 * π * β))) -
        β ^ (-(1 : ℝ)) * (Real.exp (π * a * β⁻¹) * (1 - Real.exp (-2 * π / β)) *
          (Real.exp (π * a * β⁻¹) * (1 - Real.exp (-2 * π / β))))
      = (Real.exp (π * a * β) * Real.exp (π * a * β)) * (1 - Real.exp (-2 * π * β)) ^ 2 -
        β ^ (-(1 : ℝ)) * (Real.exp (π * a * β⁻¹) * Real.exp (π * a * β⁻¹)) *
          (1 - Real.exp (-2 * π / β)) ^ 2 := by ring
    _ = Real.exp (2 * π * a * β) * (1 - Real.exp (-2 * π * β)) ^ 2 -
        β ^ (-(1 : ℝ)) * Real.exp (2 * π * a / β) * (1 - Real.exp (-2 * π / β)) ^ 2 := by
        rw [hexp1, hexp2]

/-- The radial marginal `(t_L + t_R)_* ν` of any `SpinCrossingMeasureOn a X` supported on
`{t_L + t_R ≥ 0}` is a spinless Virasoro `AdmissibleCrossingMeasure virasoroProblem a`. -/
noncomputable def SpinCrossingMeasureOn.toRadAdmissible {a : ℝ} {X : Set (ℝ × ℝ)}
    (hX : X ⊆ {p : ℝ × ℝ | 0 ≤ p.1 + p.2}) (meas : SpinCrossingMeasureOn a X) :
    AdmissibleCrossingMeasure virasoroProblem a where
  ν := spinRadMarginal meas.ν
  supp_nonneg := by
    unfold spinRadMarginal
    have hmeas : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
    rw [Measure.map_apply hmeas measurableSet_Iio]
    have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Iio 0 ⊆ Xᶜ := by
      intro p hp hpX
      have h0 : 0 ≤ p.1 + p.2 := hX hpX
      have hlt : p.1 + p.2 < 0 := hp
      linarith
    exact measure_mono_null hsub meas.supp
  finite_laplace := by
    intro β hβ
    have hmeas : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
    have hint : Integrable (fun t : ℝ => Real.exp (-2 * π * β * t)) (spinRadMarginal meas.ν) := by
      unfold spinRadMarginal
      rw [integrable_map_measure (by fun_prop : Continuous fun t : ℝ => Real.exp (-2 * π * β * t)).aestronglyMeasurable
        hmeas.aemeasurable]
      exact meas.finite_laplace hβ
    exact hint.integrableOn
  crossing := by
    intro β hβ
    have hmeas : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
    have hsupp0 : spinRadMarginal meas.ν (Iio 0) = 0 := by
      unfold spinRadMarginal
      rw [Measure.map_apply hmeas measurableSet_Iio]
      have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Iio 0 ⊆ Xᶜ := by
        intro p hp hpX
        have h0 : 0 ≤ p.1 + p.2 := hX hpX
        have hlt : p.1 + p.2 < 0 := hp
        linarith
      exact measure_mono_null hsub meas.supp
    have hrestr : (spinRadMarginal meas.ν).restrict (Ici 0) = spinRadMarginal meas.ν := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      have : ∀ᵐ t ∂(spinRadMarginal meas.ν), t ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 hsupp0
      filter_upwards [this] with t ht using not_lt.1 ht
    rw [virasoroProblem_w, hrestr]
    unfold spinRadMarginal
    rw [integral_map hmeas.aemeasurable (by unfold thermalDiff; fun_prop :
      Continuous (thermalDiff 1 β)).aestronglyMeasurable]
    have heq : (fun p : ℝ × ℝ => thermalDiff 1 β (p.1 + p.2)) =
        fun p : ℝ × ℝ => spinThermalX β β p.1 p.2 := by
      ext p; exact (spinThermalX_diag_pos hβ p.1 p.2).symm
    rw [heq, meas.crossing hβ hβ, spinThermalXVac_diag_pos a hβ]
    unfold FixedWeightProblem.gVac FixedWeightProblem.cardyDensity
    have hmul : (fun t : ℝ => thermalDiff 1 β t * (2 * π * virasoroProblem.cardyV a t)) =
        fun t : ℝ => (2 * π) * (thermalDiff 1 β t * virasoroProblem.cardyV a t) := by
      ext t; ring
    rw [hmul, integral_const_mul]
    ring

lemma SpinCrossingMeasureOn.toRadAdmissible_atGap {a : ℝ} {X : Set (ℝ × ℝ)} {τ : ℝ}
    (hτ : 0 ≤ τ) (hX : X ⊆ {p : ℝ × ℝ | τ ≤ p.1 + p.2}) (meas : SpinCrossingMeasureOn a X) :
    IsAtGap (meas.toRadAdmissible (hX.trans fun _ hp => hτ.trans hp)) τ := by
  change (spinRadMarginal meas.ν) (Iio τ) = 0
  unfold spinRadMarginal
  have hmeas : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  rw [Measure.map_apply hmeas measurableSet_Iio]
  have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Iio τ ⊆ Xᶜ := by
    intro p hp hpX
    have hge : τ ≤ p.1 + p.2 := hX hpX
    have hlt : p.1 + p.2 < τ := hp
    linarith
  exact measure_mono_null hsub meas.supp

/-! ### Section 3: Swap-symmetrised thermal tests, certified class on `E_B`, and `Q_N` -/

/-- Swap-symmetrised thermal test `\mathfrak X_{\boldsymbol\beta} = ½ (X_{(β_L,β_R)} + X_{(β_R,β_L)})`. -/
noncomputable def spinSymThermalX (βL βR tL tR : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (spinThermalX βL βR tL tR + spinThermalX βR βL tL tR)

/-- Pullback of a `(t_L, t_R)`-coordinate function to `(r_L, r_R)` coordinates via `t_u = r_u² / 2`. -/
noncomputable def spinLiftTToR (Φ : ℝ × ℝ → ℝ) (r : ℝ × ℝ) : ℝ :=
  Φ (r.1 ^ 2 / 2, r.2 ^ 2 / 2)

/-- Swap-symmetrised thermal test in `(r_L, r_R)` coordinates. -/
noncomputable def spinSymThermalX_r (βL βR : ℝ) : ℝ × ℝ → ℝ :=
  spinLiftTToR (fun p => spinSymThermalX βL βR p.1 p.2)

/-- Vacuum value of a `(t_L, t_R)`-coordinate test via its `(r_L, r_R)` pullback. -/
noncomputable def spinVacT (a : ℝ) (Φ : ℝ × ℝ → ℝ) : ℝ :=
  spinPhiVac a (spinLiftTToR Φ)

/-- Swap-symmetrised odd two-variable Laguerre basis function in `(t_L, t_R)` coordinates:
`½ (ψ_m(t_L) ψ_n(t_R) + ψ_m(t_R) ψ_n(t_L))` with `ψ_k = LP.lagPsi (1/2) k`. -/
noncomputable def spinOddLagBasisT (m n : ℕ) (p : ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) * (lagPsi (1 / 2) m p.1 * lagPsi (1 / 2) n p.2 +
    lagPsi (1 / 2) m p.2 * lagPsi (1 / 2) n p.1)

/-- Certified class `\mathcal B` in `(t_L, t_R)` coordinates (`spinning_dual.tex`, Section 1):
real span of swap-symmetrised odd Laguerre functions (`m + n` odd) and radial lifts
`(t_L, t_R) ↦ hMaj a β₀ (t_L + t_R)` (`0 < β₀ ≤ 1/2`). Defined on all of `E_B`. -/
def SpinCertifiedT (a : ℝ) (Φ : ℝ × ℝ → ℝ) : Prop :=
  Φ ∈ Submodule.span ℝ
    ({f : ℝ × ℝ → ℝ | ∃ m n : ℕ, Odd (m + n) ∧ f = spinOddLagBasisT m n} ∪
     {f : ℝ × ℝ → ℝ | ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 / 2 ∧ f = fun p => hMaj a β₀ (p.1 + p.2)})

/-- Certified-class strict primal infimum `T_{Ω,F}^{\mathcal B}` on `X_T = F ∪ Ω(T)`. -/
noncomputable def spinCertifiedThr (a : ℝ) (Ω F : Set (ℝ × ℝ)) : ℝ :=
  sInf {T : ℝ | 0 < T ∧ ∃ Φ, SpinCertifiedT a Φ ∧ 0 < spinVacT a Φ ∧
    ∀ p ∈ F ∪ spinConeSlice Ω T, 0 ≤ Φ p}

/-- Swap-symmetrised odd Laguerre polynomial basis element
`½ (L_m^{(-1/2)}(4π t_L) L_n^{(-1/2)}(4π t_R) + L_m^{(-1/2)}(4π t_R) L_n^{(-1/2)}(4π t_L))`. -/
noncomputable def spinOddLagPolyBasis (m n : ℕ) (p : ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) * (lagL (1 / 2) m (4 * π * p.1) * lagL (1 / 2) n (4 * π * p.2) +
    lagL (1 / 2) m (4 * π * p.2) * lagL (1 / 2) n (4 * π * p.1))

/-- Finite-order swap-symmetric odd Laguerre polynomial space `\mathcal Q_N` (`spinning_dual.tex`,
Section 1.2). -/
def spinOddLagPolySpace (N : ℕ) : Submodule ℝ (ℝ × ℝ → ℝ) :=
  Submodule.span ℝ
    {q : ℝ × ℝ → ℝ | ∃ m n : ℕ, Odd (m + n) ∧ m + n ≤ N ∧ q = spinOddLagPolyBasis m n}

lemma exp_mul_spinOddLagPolyBasis (m n : ℕ) (p : ℝ × ℝ) :
    Real.exp (-2 * π * (p.1 + p.2)) * spinOddLagPolyBasis m n p = spinOddLagBasisT m n p := by
  unfold spinOddLagPolyBasis spinOddLagBasisT lagPsi
  have hexp : Real.exp (-2 * π * (p.1 + p.2)) =
      Real.exp (-2 * π * p.1) * Real.exp (-2 * π * p.2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  ring

lemma exp_mul_mem_SpinCertifiedT {a : ℝ} {N : ℕ} {q : ℝ × ℝ → ℝ}
    (hq : q ∈ spinOddLagPolySpace N) :
    SpinCertifiedT a (fun p => Real.exp (-2 * π * (p.1 + p.2)) * q p) := by
  unfold SpinCertifiedT
  refine Submodule.span_induction
    (p := fun q _ => (fun p => Real.exp (-2 * π * (p.1 + p.2)) * q p) ∈ Submodule.span ℝ
      ({f : ℝ × ℝ → ℝ | ∃ m n : ℕ, Odd (m + n) ∧ f = spinOddLagBasisT m n} ∪
       {f : ℝ × ℝ → ℝ | ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 / 2 ∧ f = fun p => hMaj a β₀ (p.1 + p.2)}))
    ?_ ?_ ?_ ?_ hq
  · rintro f ⟨m, n, hmn, -, rfl⟩
    have heq : (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 + p.2)) * spinOddLagPolyBasis m n p) =
        spinOddLagBasisT m n := funext (exp_mul_spinOddLagPolyBasis m n)
    rw [heq]
    exact Submodule.subset_span (Or.inl ⟨m, n, hmn, rfl⟩)
  · have : (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 + p.2)) * (0 : ℝ × ℝ → ℝ) p) = 0 := by
      ext p; simp
    rw [this]; exact Submodule.zero_mem _
  · intro f g _ _ hf hg
    have : (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 + p.2)) * (f + g) p) =
        (fun p => Real.exp (-2 * π * (p.1 + p.2)) * f p) +
        (fun p => Real.exp (-2 * π * (p.1 + p.2)) * g p) := by
      ext p; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ hf hg
  · intro c f _ hf
    have : (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 + p.2)) * (c • f) p) =
        c • (fun p => Real.exp (-2 * π * (p.1 + p.2)) * f p) := by
      ext p; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this]; exact Submodule.smul_mem _ c hf

/-- Feasibility of a finite-order odd Laguerre polynomial `q ∈ \mathcal Q_N` on `X ⊆ ℝ × ℝ`. -/
def spinOddLagFeasible (a : ℝ) (N : ℕ) (X : Set (ℝ × ℝ)) (q : ℝ × ℝ → ℝ) : Prop :=
  q ∈ spinOddLagPolySpace N ∧
    (∀ p ∈ X, 0 ≤ Real.exp (-2 * π * (p.1 + p.2)) * q p) ∧
    0 < spinVacT a (fun p => Real.exp (-2 * π * (p.1 + p.2)) * q p)

/-- Order-`N` spinning primal infimum `T_{Ω,F}^{[N]}` in `[0, ∞]`. -/
noncomputable def spinLagThrN (a : ℝ) (Ω F : Set (ℝ × ℝ)) (N : ℕ) : ℝ≥0∞ :=
  ⨅ (T : ℝ) (_ : 0 < T ∧ ∃ q, spinOddLagFeasible a N (F ∪ spinConeSlice Ω T) q),
    ENNReal.ofReal T

/-- Infinite-order spinning primal infimum `T_{Ω,F}^{[\infty]} = \inf_N T_{Ω,F}^{[N]}` in `[0, ∞]`. -/
noncomputable def spinLagThrInf (a : ℝ) (Ω F : Set (ℝ × ℝ)) : ℝ≥0∞ :=
  ⨅ N : ℕ, spinLagThrN a Ω F N

/-! ### Section 4: Two-dimensional Mehler operator `A_r` (`sd:V`) -/

/-- One-dimensional Mehler kernel in `r_L` coordinates (`x = √(2π) r_L`):
`K_r^{(r)}(r_L, u) = √(2 / (1 - r)) exp(-π ((1 - r)/(1 + r)) r_L² - π ((1 + r)/(1 - r)) (u - (2√r/(1+r)) r_L)²)`. -/
noncomputable def spinMehlerKernel1D (r x u : ℝ) : ℝ :=
  Real.sqrt (2 / (1 - r)) *
    Real.exp (-π * ((1 - r) / (1 + r)) * x ^ 2 -
      π * ((1 + r) / (1 - r)) * (u - (2 * Real.sqrt r / (1 + r)) * x) ^ 2)

/-- Two-dimensional tensor Mehler operator `(A_r Φ)(r_L, r_R) = ∬ K_r^{(r)}(r_L, u) K_r^{(r)}(r_R, v) Φ(u, v) du dv`
on even-in-each-coordinate functions (`spinning_dual.tex`, Lemma SD-V). -/
noncomputable def spinMehlerOp (r : ℝ) (Φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ q : ℝ × ℝ, spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 * Φ q

end FormalResearch.ModularBootstrap.Spin
