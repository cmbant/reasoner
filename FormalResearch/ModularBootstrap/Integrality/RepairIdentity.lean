module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Projection identity for the radial and tensor-cosine repairs (`int:repair-identity`)

`CFT/modular_bootstrap/paper/integrality.tex`, Lemma INT-R0, at function level.  The measure space
`(T, m)`, the symmetric kernel `k`, the transform `U g (t) = ∫ k(t,s) g(s) dm(s)`, the finite signed
measure `η = ηp - ηm` and `h_η(t) = ∫ k(t,s) dη(s)` are as in the lemma.  The correction
`f` (supported in the band) is the solution of `f + P U f = P h_η` on the band, `‖f‖₂ ≤ Λ ‖P h_η‖₂`
(`Λ = ‖A⁻¹‖`); its existence from `‖P U P‖ < 1` is the operator-theoretic input, not part of this
file.  `D η = (I + U*)(η - f dm)` is encoded by its pairing `repairPairing` with test functions and by
its density `h_η - U f` off the band.  Proved: (a) `D η` agrees with `η` on the band, (b) it pairs to zero
against every crossing test `g` with `U g = -g` (absolute convergence of the pairings is a hypothesis,
as in the paper), (c) the off-band density bound.
-/

@[expose] public section

open MeasureTheory Set

namespace FormalResearch.ModularBootstrap.Integrality

variable {T : Type*} [MeasurableSpace T]

/-- Cauchy--Schwarz for the integral of a product of `L²` functions. -/
lemma cs_integral {μ : Measure T} {a b : T → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    |∫ x, a x * b x ∂μ| ≤ Real.sqrt (∫ x, a x ^ 2 ∂μ) * Real.sqrt (∫ x, b x ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (f := fun x => |a x|) (g := fun x => |b x|)
    (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (by rw [show ENNReal.ofReal 2 = 2 by simp]; exact ha.abs)
    (by rw [show ENNReal.ofReal 2 = 2 by simp]; exact hb.abs)
  simp only [Real.rpow_two, sq_abs, one_div] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, one_div]
  calc |∫ x, a x * b x ∂μ| ≤ ∫ x, |a x * b x| ∂μ := by
        simpa using abs_integral_le_integral_abs (f := fun x => a x * b x) (μ := μ)
    _ = ∫ x, |a x| * |b x| ∂μ := by simp [abs_mul]
    _ ≤ _ := h

/-- The transform `U g (t) = ∫ k(t,s) g(s) dm(s)`. -/
noncomputable def kerTransform (m : Measure T) (k : T → T → ℝ) (g : T → ℝ) (t : T) : ℝ :=
  ∫ s, k t s * g s ∂m

/-- The dual density `h_η(t) = ∫ k(t,s) dη(s)` of `η = ηp - ηm`. -/
noncomputable def kerDual (k : T → T → ℝ) (ηp ηm : Measure T) (t : T) : ℝ :=
  ∫ s, k t s ∂ηp - ∫ s, k t s ∂ηm

/-- Pairing of `D η = (I + U*)(η - f dm)` with a test function `g`: the measure part
`∫ g dη - ∫ g f dm` plus the density part `∫ g (h_η - U f) dm`. -/
noncomputable def repairPairing (m ηp ηm : Measure T) (k : T → T → ℝ) (f g : T → ℝ) : ℝ :=
  (∫ s, g s ∂ηp - ∫ s, g s ∂ηm) - ∫ s, g s * f s ∂m +
    ∫ t, g t * (kerDual k ηp ηm t - kerTransform m k f t) ∂m

/-- **(a)** `D η` equals `η` on the band: for test functions supported in the band. -/
theorem repair_identity_band {m ηp ηm : Measure T} {k : T → T → ℝ} {f : T → ℝ} {band : Set T}
    (hsol : ∀ᵐ t ∂m, t ∈ band → f t + kerTransform m k f t = kerDual k ηp ηm t)
    {g : T → ℝ} (hg : ∀ t, t ∉ band → g t = 0) :
    repairPairing m ηp ηm k f g = ∫ s, g s ∂ηp - ∫ s, g s ∂ηm := by
  have h : ∫ t, g t * (kerDual k ηp ηm t - kerTransform m k f t) ∂m = ∫ s, g s * f s ∂m := by
    refine integral_congr_ae ?_
    filter_upwards [hsol] with t ht
    by_cases hb : t ∈ band
    · rw [← ht hb]; ring
    · simp [hg t hb]
  unfold repairPairing
  rw [h]; ring

/-- **(b)** `D η` pairs to zero against every absolutely integrable crossing test `g` with
`U g = -g` (symmetric kernel; the Fubini hypotheses are the paper's absolute convergence). -/
theorem repair_identity_cross [SigmaFinite m] {ηp ηm : Measure T} [IsFiniteMeasure ηp]
    [IsFiniteMeasure ηm] {k : T → T → ℝ} (hsymm : ∀ s t, k s t = k t s) {f g : T → ℝ}
    (hg : ∀ t, kerTransform m k g t = -g t)
    (hF1 : Integrable (fun p : T × T => g p.1 * k p.1 p.2) (m.prod ηp))
    (hF2 : Integrable (fun p : T × T => g p.1 * k p.1 p.2) (m.prod ηm))
    (hF3 : Integrable (fun p : T × T => g p.1 * (k p.1 p.2 * f p.2)) (m.prod m)) :
    repairPairing m ηp ηm k f g = 0 := by
  have hsw : ∀ (η : Measure T) [IsFiniteMeasure η],
      Integrable (fun p : T × T => g p.1 * k p.1 p.2) (m.prod η) →
      ∫ t, g t * ∫ s, k t s ∂η ∂m = -∫ s, g s ∂η := by
    intro η _ hF
    have h1 : ∀ t, g t * ∫ s, k t s ∂η = ∫ s, g t * k t s ∂η := fun t =>
      (integral_const_mul _ _).symm
    simp_rw [h1]
    rw [integral_integral_swap hF]
    have h2 : ∀ s, ∫ t, g t * k t s ∂m = -g s := by
      intro s
      have := hg s
      unfold kerTransform at this
      rw [← this]
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
        show g t * k t s = k s t * g t
        rw [hsymm s t]; ring)
    simp_rw [h2]
    exact integral_neg _
  have hsw3 : ∫ t, g t * kerTransform m k f t ∂m = -∫ s, g s * f s ∂m := by
    unfold kerTransform
    have h1 : ∀ t, g t * ∫ s, k t s * f s ∂m = ∫ s, g t * (k t s * f s) ∂m := fun t =>
      (integral_const_mul _ _).symm
    simp_rw [h1]
    rw [integral_integral_swap hF3]
    have h2 : ∀ s, ∫ t, g t * (k t s * f s) ∂m = -(g s * f s) := by
      intro s
      have := hg s
      unfold kerTransform at this
      have h3 : ∫ t, g t * (k t s * f s) ∂m = (∫ t, k s t * g t ∂m) * f s := by
        rw [← integral_mul_const]
        exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
          show g t * (k t s * f s) = k s t * g t * f s
          rw [hsymm s t]; ring)
      rw [h3, this]; ring
    simp_rw [h2]
    exact integral_neg _
  have i1 : Integrable (fun t => g t * ∫ s, k t s ∂ηp) m := by
    have := hF1.integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp [integral_const_mul]
  have i2 : Integrable (fun t => g t * ∫ s, k t s ∂ηm) m := by
    have := hF2.integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp [integral_const_mul]
  have i3 : Integrable (fun t => g t * kerTransform m k f t) m := by
    have := hF3.integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp [kerTransform, integral_const_mul]
  have h4 : ∫ t, g t * (kerDual k ηp ηm t - kerTransform m k f t) ∂m =
      (∫ t, g t * ∫ s, k t s ∂ηp ∂m - ∫ t, g t * ∫ s, k t s ∂ηm ∂m) -
        ∫ t, g t * kerTransform m k f t ∂m := by
    calc ∫ t, g t * (kerDual k ηp ηm t - kerTransform m k f t) ∂m
        = ∫ t, ((g t * ∫ s, k t s ∂ηp - g t * ∫ s, k t s ∂ηm) - g t * kerTransform m k f t) ∂m :=
          integral_congr_ae (Filter.Eventually.of_forall fun t => by simp only [kerDual]; ring)
      _ = ∫ t, (g t * ∫ s, k t s ∂ηp - g t * ∫ s, k t s ∂ηm) ∂m -
            ∫ t, g t * kerTransform m k f t ∂m := integral_sub (i1.sub i2) i3
      _ = _ := by rw [integral_sub i1 i2]
  unfold repairPairing
  rw [h4, hsw ηp hF1, hsw ηm hF2, hsw3]
  ring

/-- **(c)** Off the band the density of `D η` is `h_η - U f`, bounded by `|h_η(t)|` plus
`‖k(t,·)‖_{L²(band)} · Λ · ‖P h_η‖₂`. -/
theorem repair_identity_bound {m ηp ηm : Measure T} {k : T → T → ℝ} {f : T → ℝ} {band : Set T}
    (hf0 : ∀ t, t ∉ band → f t = 0) (hf : MemLp f 2 m) (t : T)
    (hk : MemLp (fun s => k t s) 2 (m.restrict band)) {Λ : ℝ}
    (hΛ : ∫ s, f s ^ 2 ∂m ≤ Λ ^ 2 * ∫ s in band, kerDual k ηp ηm s ^ 2 ∂m) (hΛ0 : 0 ≤ Λ) :
    |kerDual k ηp ηm t - kerTransform m k f t| ≤ |kerDual k ηp ηm t| +
      Real.sqrt (∫ s in band, k t s ^ 2 ∂m) * (Λ * Real.sqrt (∫ s in band, kerDual k ηp ηm s ^ 2 ∂m)) := by
  have h1 : kerTransform m k f t = ∫ s in band, k t s * f s ∂m := by
    unfold kerTransform
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => by
      simp [hf0 s hs]).symm
  have h2 : ∫ s, f s ^ 2 ∂m = ∫ s in band, f s ^ 2 ∂m :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => by simp [hf0 s hs]).symm
  have hfb : MemLp f 2 (m.restrict band) := hf.mono_measure Measure.restrict_le_self
  have hcs := cs_integral hk hfb
  have h3 : Real.sqrt (∫ s in band, f s ^ 2 ∂m) ≤ Λ * Real.sqrt (∫ s in band, kerDual k ηp ηm s ^ 2 ∂m) := by
    rw [← h2]
    calc Real.sqrt (∫ s, f s ^ 2 ∂m) ≤ Real.sqrt (Λ ^ 2 * ∫ s in band, kerDual k ηp ηm s ^ 2 ∂m) :=
          Real.sqrt_le_sqrt hΛ
      _ = Λ * Real.sqrt (∫ s in band, kerDual k ηp ηm s ^ 2 ∂m) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΛ0]
  have h4 : |kerTransform m k f t| ≤ Real.sqrt (∫ s in band, k t s ^ 2 ∂m) *
      (Λ * Real.sqrt (∫ s in band, kerDual k ηp ηm s ^ 2 ∂m)) := by
    rw [h1]
    refine hcs.trans ?_
    rw [← h2] at *
    gcongr
  calc |kerDual k ηp ηm t - kerTransform m k f t| ≤ |kerDual k ηp ηm t| + |kerTransform m k f t| :=
        abs_sub _ _
    _ ≤ _ := by gcongr

/-- info: 'FormalResearch.ModularBootstrap.Integrality.repair_identity_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms repair_identity_band

/-- info: 'FormalResearch.ModularBootstrap.Integrality.repair_identity_cross' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms repair_identity_cross

/-- info: 'FormalResearch.ModularBootstrap.Integrality.repair_identity_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms repair_identity_bound

end FormalResearch.ModularBootstrap.Integrality
