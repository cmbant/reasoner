module

public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import FormalResearch.ModularBootstrap.Duality.Primal.CompactMass
public import FormalResearch.ModularBootstrap.Spin.SpinD3V
public import FormalResearch.ModularBootstrap.Spin.SpinD3W
public import FormalResearch.ModularBootstrap.Spin.SpinD2SD
public import FormalResearch.ModularBootstrap.Spin.SpinD2SDQuad
public import FormalResearch.ModularBootstrap.Spin.SpinDStatements

/-!
# SPIN-D Proposition SD-A (`sd:A`): Attainment and Complementary Slackness

Proves `theorem spinDA : SpinDA` unconditionally for all `a ≥ 2`:
given compact swap-invariant `F ⊆ spinConeB 0 ∩ {t_L + t_R > 0}`, the strict full-class
threshold `TF` equals the certified threshold `spinCertifiedThr a (spinConeB 0) F > 0`,
and there exists an extremal `Φs ∈ SpinTestClass a` with `spinM2 a Φs = 1`,
`spinPhiVac a Φs = 0`, `spinEvalT Φs ≥ 0` on `F ∪ spinConeSlice (spinConeB 0) TF`,
and `∀ meas : SpinCrossingMeasureOn a (F ∪ spinConeSlice (spinConeB 0) TF),
∀ᵐ p ∂meas.ν, spinEvalT Φs p = 0`.

## Proof strategy (unconditional, no `SpinS24` needed)
1. **Uniform Lipschitz bound**: from `spinTestClass_exp_L1_le_M2` (`SpinD3V.lean`) and
   Fourier oddness `spinToEuc Φ = -𝓕 (spinToEuc Φ)`, every `Φ ∈ SpinTestClass a` satisfies
   `|Φ p - Φ q| ≤ C_L * spinM2 a Φ * dist p q` globally on `ℝ × ℝ`.
2. **Arzelà–Ascoli diagonalization**: any `M_2`-normalized sequence `Φ_j ∈ SpinTestClass a`
   has a subsequence converging uniformly on every `closedBall (0 : ℝ × ℝ) (m + 1)`.
3. **`L¹` & Fourier-oddness stability**: the uniform exponential-weighted `L¹` bound
   controls the tails uniformly in `j`, giving `Φ_{φ j} → Φs` in `L¹(ℝ × ℝ)` and hence
   `𝓕 (spinToEuc Φs) = -spinToEuc Φs`.
4. **Compact negative mass (`Duality.compact_negative_mass`) + `spinDSD_cone` + `spinDW`**:
   yields `spinM2 a Φs = 1`, `spinPhiVac a Φs = 0`, nonnegativity on `F ∪ Ω(TF)`, and
   complementary slackness against every crossing measure on `F ∪ Ω(TF)`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Metric
open scoped Real ENNReal FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight

private noncomputable def aE2ToProd : RadialSpace 1 ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))

private lemma aVolume_preserving_e2ToProd : MeasurePreserving aE2ToProd volume volume :=
  (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp (PiLp.volume_preserving_ofLp (Fin 2))

/-! ### Section 1: Uniform Lipschitz bound on `SpinTestClass a` -/

private lemma norm_exp_I_sub_exp_I_le (u v : ℝ) :
    ‖Complex.exp ((u : ℂ) * Complex.I) - Complex.exp ((v : ℂ) * Complex.I)‖ ≤ |u - v| := by
  have hfac : Complex.exp ((u : ℂ) * Complex.I) - Complex.exp ((v : ℂ) * Complex.I) =
      Complex.exp ((v : ℂ) * Complex.I) * (Complex.exp (((u - v : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2; push_cast; ring
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  set θ : ℝ := u - v
  have hre : (Complex.exp ((θ : ℂ) * Complex.I) - 1).re = Real.cos θ - 1 := by
    rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.one_re]
  have him : (Complex.exp ((θ : ℂ) * Complex.I) - 1).im = Real.sin θ := by
    rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, sub_zero]
  have hsq : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have h1 := Real.cos_two_mul (θ / 2)
      have h2 := Real.sin_sq_add_cos_sq (θ / 2)
      have h3 : 2 * (θ / 2) = θ := by ring
      rw [h3] at h1
      linarith
    have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
      have h1 := Real.sin_two_mul (θ / 2)
      have h3 : 2 * (θ / 2) = θ := by ring
      rwa [h3] at h1
    have hsc := Real.sin_sq_add_cos_sq (θ / 2)
    rw [hcos, hsin]
    nlinarith
  have hnorm_eq : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
    have h1 := congrArg Real.sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq_eq_abs, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h1
    exact h1
  rw [hnorm_eq]
  have hsin_le := Real.abs_sin_le_abs (x := θ / 2)
  rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hsin_le
  linarith

private lemma norm_fourierChar_sub_le (t s : ℝ) :
    ‖(Real.fourierChar t : ℂ) - (Real.fourierChar s : ℂ)‖ ≤ 2 * π * |t - s| := by
  have hchar : ∀ x : ℝ, (Real.fourierChar x : ℂ) = Complex.exp (((2 * π * x : ℝ) : ℂ) * Complex.I) := by
    intro x
    rw [Real.fourierChar_apply]
  rw [hchar t, hchar s]
  calc ‖Complex.exp (((2 * π * t : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((2 * π * s : ℝ) : ℂ) * Complex.I)‖
      ≤ |2 * π * t - 2 * π * s| := norm_exp_I_sub_exp_I_le _ _
    _ = 2 * π * |t - s| := by
        rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 * π)]

private lemma spinD3A_exp_L1_both {a : ℝ} (ha : 2 ≤ a) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ →
        Integrable (fun p : ℝ × ℝ => |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.1|)) volume ∧
        Integrable (fun p : ℝ × ℝ => |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.2|)) volume ∧
        (∫ p : ℝ × ℝ, |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.1|)) ≤ C * spinM2 a Φ ∧
        (∫ p : ℝ × ℝ, |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.2|)) ≤ C * spinM2 a Φ := by
  obtain ⟨C, hC_pos, hC⟩ := spinTestClass_exp_L1_le_M2 ha
  refine ⟨C, hC_pos, fun {Φ} hΦ => ?_⟩
  obtain ⟨hint1, hle1⟩ := hC hΦ
  have hmp : MeasurePreserving (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ) volume volume := by
    rw [Measure.volume_eq_prod]; exact Measure.measurePreserving_swap
  have hswap_eq : (fun p : ℝ × ℝ => |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.2|)) =
      (fun p : ℝ × ℝ => |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.1|)) ∘
        (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ) := by
    ext p
    change |Φ (p.1, p.2)| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.2|) =
      |Φ (p.2, p.1)| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.2|)
    rw [hΦ.d4_inv.2.2 p.1 p.2]
  have hint2 : Integrable (fun p : ℝ × ℝ => |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.2|)) volume := by
    rw [hswap_eq]; exact hmp.integrable_comp_of_integrable hint1
  have hle2 : (∫ p : ℝ × ℝ, |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.2|)) ≤ C * spinM2 a Φ := by
    rw [hswap_eq]
    have heq := hmp.integral_comp'
      (g := fun p : ℝ × ℝ => |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.1|))
    change (∫ p : ℝ × ℝ, |Φ (MeasurableEquiv.prodComm p)| *
      Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |(MeasurableEquiv.prodComm p).1|)) ≤ C * spinM2 a Φ
    rw [heq]; exact hle1
  exact ⟨hint1, hint2, hle1, hle2⟩

/-- Global uniform Lipschitz bound on `SpinTestClass a` (`a ≥ 2`), proved unconditionally from
`spinTestClass_exp_L1_le_M2` and Fourier oddness `spinToEuc Φ = -𝓕 (spinToEuc Φ)`. -/
private lemma spinD3A_lipschitz {a : ℝ} (ha : 2 ≤ a) :
    ∃ L : ℝ, 0 < L ∧
      ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ →
        ∀ p q : ℝ × ℝ, |Φ p - Φ q| ≤ L * spinM2 a Φ * dist p q := by
  obtain ⟨C, hC_pos, hC⟩ := spinD3A_exp_L1_both ha
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr (by linarith)
  set c : ℝ := (1 / 3 : ℝ) * π * Real.sqrt a
  have hc : 0 < c := by positivity
  refine ⟨2 * π * (2 * C / c), by positivity, fun {Φ} hΦ p q => ?_⟩
  obtain ⟨hint1, hint2, hle1, hle2⟩ := hC hΦ
  -- Use `spinToEuc Φ x = -𝓕 (spinToEuc Φ) x`
  have hrep : ∀ r : ℝ × ℝ, (Φ r : ℂ) =
      -(∫ ξ : ℝ × ℝ, Real.fourierChar (-(ξ.1 * r.1 + ξ.2 * r.2)) • (Φ ξ : ℂ)) := by
    intro r
    let x : RadialSpace 1 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![r.1, r.2]
    have hx0 : x 0 = r.1 := rfl
    have hx1 : x 1 = r.2 := rfl
    have hodd := congrFun hΦ.fourier_odd x
    simp only [Pi.neg_apply] at hodd
    have hval : spinToEuc Φ x = (Φ r : ℂ) := by
      simp [spinToEuc, hx0, hx1]
    have hF : 𝓕 (spinToEuc Φ) x =
        ∫ ξ : ℝ × ℝ, Real.fourierChar (-(ξ.1 * r.1 + ξ.2 * r.2)) • (Φ ξ : ℂ) := by
      rw [Real.fourier_eq]
      rw [← aVolume_preserving_e2ToProd.integral_comp'
        (g := fun ξ : ℝ × ℝ => Real.fourierChar (-(ξ.1 * r.1 + ξ.2 * r.2)) • (Φ ξ : ℂ))]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      have hinner : ⟪y, x⟫ = y 0 * r.1 + y 1 * r.2 := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, Fin.sum_univ_two, hx0, hx1, mul_comm]
      have he1 : (aE2ToProd y).1 = y 0 := rfl
      have he2 : (aE2ToProd y).2 = y 1 := rfl
      rw [hinner, he1, he2]; rfl
    rw [hval] at hodd
    rw [← hF, hodd, neg_neg]
  have hint_char : ∀ r : ℝ × ℝ,
      Integrable (fun ξ : ℝ × ℝ => Real.fourierChar (-(ξ.1 * r.1 + ξ.2 * r.2)) • (Φ ξ : ℂ)) := by
    intro r
    refine hΦ.int.norm.mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · have hΦc : Continuous Φ := hΦ.cont
      have hcont : Continuous (fun ξ : ℝ × ℝ =>
          Complex.exp (((2 * π * -(ξ.1 * r.1 + ξ.2 * r.2) : ℝ) : ℂ) * Complex.I) * (Φ ξ : ℂ)) :=
        (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp
            (continuous_const.mul (((continuous_fst.mul continuous_const).add
              (continuous_snd.mul continuous_const)).neg))).mul continuous_const)).mul
          (Complex.continuous_ofReal.comp hΦc)
      have heq : (fun ξ : ℝ × ℝ => Real.fourierChar (-(ξ.1 * r.1 + ξ.2 * r.2)) • (Φ ξ : ℂ)) =
          fun ξ => Complex.exp (((2 * π * -(ξ.1 * r.1 + ξ.2 * r.2) : ℝ) : ℂ) * Complex.I) * (Φ ξ : ℂ) := by
        ext ξ
        rw [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
      rw [heq]; exact hcont.aestronglyMeasurable
    · rw [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real]
  have hsub : (Φ p : ℂ) - (Φ q : ℂ) =
      ∫ ξ : ℝ × ℝ,
        ((Real.fourierChar (-(ξ.1 * q.1 + ξ.2 * q.2)) : ℂ) -
         (Real.fourierChar (-(ξ.1 * p.1 + ξ.2 * p.2)) : ℂ)) * (Φ ξ : ℂ) := by
    rw [hrep p, hrep q, sub_neg_eq_add, add_comm, ← sub_eq_add_neg,
        ← integral_sub (hint_char q) (hint_char p)]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [Circle.smul_def, smul_eq_mul, sub_mul]
  have habs_le : |Φ p - Φ q| ≤
      ∫ ξ : ℝ × ℝ, (2 * π * dist p q / c) *
        (|Φ ξ| * Real.exp (c * |ξ.1|) + |Φ ξ| * Real.exp (c * |ξ.2|)) := by
    have hnorm : |Φ p - Φ q| = ‖(Φ p : ℂ) - (Φ q : ℂ)‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, hsub]
    calc ‖∫ ξ : ℝ × ℝ,
          ((Real.fourierChar (-(ξ.1 * q.1 + ξ.2 * q.2)) : ℂ) -
           (Real.fourierChar (-(ξ.1 * p.1 + ξ.2 * p.2)) : ℂ)) * (Φ ξ : ℂ)‖
        ≤ ∫ ξ : ℝ × ℝ,
          ‖((Real.fourierChar (-(ξ.1 * q.1 + ξ.2 * q.2)) : ℂ) -
            (Real.fourierChar (-(ξ.1 * p.1 + ξ.2 * p.2)) : ℂ)) * (Φ ξ : ℂ)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ ξ : ℝ × ℝ, (2 * π * dist p q / c) *
          (|Φ ξ| * Real.exp (c * |ξ.1|) + |Φ ξ| * Real.exp (c * |ξ.2|)) := by
          refine integral_mono ?_ ((hint1.add hint2).const_mul _) fun ξ => ?_
          · exact ((hint_char q).sub (hint_char p)).congr (Eventually.of_forall fun ξ => by
              simp only [Pi.sub_apply, Circle.smul_def, smul_eq_mul, sub_mul]) |>.norm
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have h1 := norm_fourierChar_sub_le (-(ξ.1 * q.1 + ξ.2 * q.2)) (-(ξ.1 * p.1 + ξ.2 * p.2))
            have h2 : |-(ξ.1 * q.1 + ξ.2 * q.2) - -(ξ.1 * p.1 + ξ.2 * p.2)| ≤
                (|ξ.1| + |ξ.2|) * dist p q := by
              have heq : -(ξ.1 * q.1 + ξ.2 * q.2) - -(ξ.1 * p.1 + ξ.2 * p.2) =
                  ξ.1 * (p.1 - q.1) + ξ.2 * (p.2 - q.2) := by ring
              rw [heq]
              have hd1 : |p.1 - q.1| ≤ dist p q := by
                rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_left _ _
              have hd2 : |p.2 - q.2| ≤ dist p q := by
                rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_right _ _
              calc |ξ.1 * (p.1 - q.1) + ξ.2 * (p.2 - q.2)|
                  ≤ |ξ.1 * (p.1 - q.1)| + |ξ.2 * (p.2 - q.2)| := abs_add_le _ _
                _ = |ξ.1| * |p.1 - q.1| + |ξ.2| * |p.2 - q.2| := by rw [abs_mul, abs_mul]
                _ ≤ |ξ.1| * dist p q + |ξ.2| * dist p q :=
                    add_le_add (mul_le_mul_of_nonneg_left hd1 (abs_nonneg _))
                      (mul_le_mul_of_nonneg_left hd2 (abs_nonneg _))
                _ = (|ξ.1| + |ξ.2|) * dist p q := by ring
            have hexp1 : |ξ.1| ≤ Real.exp (c * |ξ.1|) / c := by
              have := Real.add_one_le_exp (c * |ξ.1|)
              rw [le_div_iff₀ hc]; linarith
            have hexp2 : |ξ.2| ≤ Real.exp (c * |ξ.2|) / c := by
              have := Real.add_one_le_exp (c * |ξ.2|)
              rw [le_div_iff₀ hc]; linarith
            have h3 : ‖(Real.fourierChar (-(ξ.1 * q.1 + ξ.2 * q.2)) : ℂ) -
                (Real.fourierChar (-(ξ.1 * p.1 + ξ.2 * p.2)) : ℂ)‖ ≤
                (2 * π * dist p q / c) * (Real.exp (c * |ξ.1|) + Real.exp (c * |ξ.2|)) := by
              calc ‖(Real.fourierChar (-(ξ.1 * q.1 + ξ.2 * q.2)) : ℂ) -
                    (Real.fourierChar (-(ξ.1 * p.1 + ξ.2 * p.2)) : ℂ)‖
                  ≤ 2 * π * |-(ξ.1 * q.1 + ξ.2 * q.2) - -(ξ.1 * p.1 + ξ.2 * p.2)| := h1
                _ ≤ 2 * π * ((|ξ.1| + |ξ.2|) * dist p q) :=
                    mul_le_mul_of_nonneg_left h2 (by positivity)
                _ ≤ 2 * π * ((Real.exp (c * |ξ.1|) / c + Real.exp (c * |ξ.2|) / c) * dist p q) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_right (add_le_add hexp1 hexp2) dist_nonneg) (by positivity)
                _ = (2 * π * dist p q / c) * (Real.exp (c * |ξ.1|) + Real.exp (c * |ξ.2|)) := by ring
            calc ‖(Real.fourierChar (-(ξ.1 * q.1 + ξ.2 * q.2)) : ℂ) -
                  (Real.fourierChar (-(ξ.1 * p.1 + ξ.2 * p.2)) : ℂ)‖ * |Φ ξ|
                ≤ (2 * π * dist p q / c) * (Real.exp (c * |ξ.1|) + Real.exp (c * |ξ.2|)) * |Φ ξ| :=
                  mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
              _ = (2 * π * dist p q / c) *
                  (|Φ ξ| * Real.exp (c * |ξ.1|) + |Φ ξ| * Real.exp (c * |ξ.2|)) := by ring
  calc |Φ p - Φ q|
      ≤ (2 * π * dist p q / c) *
          ((∫ ξ : ℝ × ℝ, |Φ ξ| * Real.exp (c * |ξ.1|)) +
           (∫ ξ : ℝ × ℝ, |Φ ξ| * Real.exp (c * |ξ.2|))) := by
        rw [integral_const_mul, integral_add hint1 hint2] at habs_le; exact habs_le
    _ ≤ (2 * π * dist p q / c) * (C * spinM2 a Φ + C * spinM2 a Φ) :=
        mul_le_mul_of_nonneg_left (add_le_add hle1 hle2) (by positivity)
    _ = 2 * π * (2 * C / c) * spinM2 a Φ * dist p q := by ring

/-! ### Section 2: Arzelà–Ascoli diagonal subsequence on `ℝ × ℝ` -/

private lemma spinD3A_arzela_single_ball
    {F : ℕ → ℝ × ℝ → ℝ} {r B L : ℝ} (_hB : 0 ≤ B) (hL : 0 ≤ L)
    (hCont : ∀ n, Continuous (F n))
    (hBd : ∀ n, ∀ p : ℝ × ℝ, |F n p| ≤ B)
    (hLip : ∀ n, ∀ p q : ℝ × ℝ, |F n p - F n q| ≤ L * dist p q) :
    ∃ (ψ : ℕ → ℕ) (g : ℝ × ℝ → ℝ), StrictMono ψ ∧
      TendstoUniformlyOn (fun k => F (ψ k)) g atTop (closedBall (0 : ℝ × ℝ) r) := by
  classical
  let X := closedBall (0 : ℝ × ℝ) r
  have : CompactSpace X := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℝ × ℝ) r)
  let bcf : ℕ → BoundedContinuousFunction X ℝ := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨fun x => F n x.1, (hCont n).comp continuous_subtype_val⟩
  have hin_s : ∀ (f : BoundedContinuousFunction X ℝ) (x : X),
      f ∈ Set.range bcf → f x ∈ closedBall (0 : ℝ) B := by
    rintro f x ⟨n, rfl⟩
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
    exact hBd n x.1
  have heq : Equicontinuous (fun f : Set.range bcf => (f.1 : X → ℝ)) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_pair]
    intro ε hε
    refine ⟨ball x₀ (ε / (2 * (L + 1))), Metric.ball_mem_nhds x₀ (div_pos hε (by linarith)),
      fun y hy z hz ⟨f, hf⟩ => ?_⟩
    obtain ⟨n, rfl⟩ := hf
    change dist (F n y.1) (F n z.1) < ε
    rw [Real.dist_eq]
    have hyx : dist y.1 x₀.1 < ε / (2 * (L + 1)) := by
      simpa [Metric.mem_ball, Subtype.dist_eq] using hy
    have hzx : dist z.1 x₀.1 < ε / (2 * (L + 1)) := by
      simpa [Metric.mem_ball, Subtype.dist_eq] using hz
    have hyz : dist y.1 z.1 < ε / (L + 1) := by
      calc dist y.1 z.1 ≤ dist y.1 x₀.1 + dist x₀.1 z.1 := dist_triangle _ _ _
        _ = dist y.1 x₀.1 + dist z.1 x₀.1 := by rw [dist_comm x₀.1 z.1]
        _ < ε / (2 * (L + 1)) + ε / (2 * (L + 1)) := add_lt_add hyx hzx
        _ = ε / (L + 1) := by field_simp [(by linarith : L + 1 ≠ 0)]; ring
    calc |F n y.1 - F n z.1| ≤ L * dist y.1 z.1 := hLip n y.1 z.1
      _ ≤ L * (ε / (L + 1)) := mul_le_mul_of_nonneg_left hyz.le hL
      _ < (L + 1) * (ε / (L + 1)) := by
          have : 0 < ε / (L + 1) := div_pos hε (by linarith)
          nlinarith
      _ = ε := by field_simp [(by linarith : L + 1 ≠ 0)]
  have hcomp : IsCompact (closure (Set.range bcf)) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℝ) B) (isCompact_closedBall 0 B)
      (Set.range bcf) hin_s heq
  obtain ⟨g₀, -, ψ, hψ_mono, hψ_tend⟩ := hcomp.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  let g : ℝ × ℝ → ℝ := fun p => if hp : p ∈ X then g₀ ⟨p, hp⟩ else 0
  refine ⟨ψ, g, hψ_mono, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rw [Metric.tendsto_atTop] at hψ_tend
  obtain ⟨K, hK⟩ := hψ_tend ε hε
  filter_upwards [Filter.eventually_ge_atTop K] with k hk p hp
  have hg_eq : g p = g₀ ⟨p, hp⟩ := by
    dsimp only [g]; split_ifs with h
    · rfl
    · exact absurd hp h
  have hcoe : dist (bcf (ψ k) ⟨p, hp⟩) (g₀ ⟨p, hp⟩) ≤ dist (bcf (ψ k)) g₀ :=
    BoundedContinuousFunction.dist_coe_le_dist (x := (⟨p, hp⟩ : X))
  calc dist (g p) (F (ψ k) p)
      = dist (g₀ ⟨p, hp⟩) (bcf (ψ k) ⟨p, hp⟩) := by rw [hg_eq]; rfl
    _ = dist (bcf (ψ k) ⟨p, hp⟩) (g₀ ⟨p, hp⟩) := dist_comm _ _
    _ ≤ dist (bcf (ψ k)) g₀ := hcoe
    _ < ε := hK k hk

private lemma spinD3A_arzela_diagonal
    {F : ℕ → ℝ × ℝ → ℝ} {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hCont : ∀ n, Continuous (F n))
    (hBd : ∀ n, ∀ p : ℝ × ℝ, |F n p| ≤ B)
    (hLip : ∀ n, ∀ p q : ℝ × ℝ, |F n p - F n q| ≤ L * dist p q) :
    ∃ (φ : ℕ → ℕ) (G : ℝ × ℝ → ℝ), StrictMono φ ∧ Continuous G ∧
      ∀ m : ℕ, TendstoUniformlyOn (fun k => F (φ k)) G atTop (closedBall (0 : ℝ × ℝ) ((m : ℝ) + 1)) := by
  classical
  let PSub (m : ℕ) (ψ : ℕ → ℕ) : Prop :=
    StrictMono ψ ∧ ∃ g : ℝ × ℝ → ℝ,
      TendstoUniformlyOn (fun k => F (ψ k)) g atTop (closedBall (0 : ℝ × ℝ) ((m : ℝ) + 1))
  let step : ∀ (m : ℕ) (p : { ψ : ℕ → ℕ // PSub m ψ }),
      { ψ' : ℕ → ℕ // PSub (m + 1) ψ' ∧ ∃ α : ℕ → ℕ, StrictMono α ∧ ψ' = p.1 ∘ α } :=
    fun m p => by
      obtain ⟨ψ, hψ_mono, _⟩ := p
      have hex := spinD3A_arzela_single_ball (F := fun n => F (ψ n)) (r := ((m + 1 : ℕ) : ℝ) + 1)
        hB hL (fun n => hCont (ψ n)) (fun n => hBd (ψ n)) (fun n => hLip (ψ n))
      let α := Classical.choose hex
      let g := Classical.choose (Classical.choose_spec hex)
      have hspec := Classical.choose_spec (Classical.choose_spec hex)
      exact ⟨ψ ∘ α, ⟨hψ_mono.comp hspec.1, g, hspec.2⟩, α, hspec.1, rfl⟩
  let ψ0_ex := spinD3A_arzela_single_ball (F := F) (r := ((0 : ℕ) : ℝ) + 1) hB hL hCont hBd hLip
  let base : { ψ : ℕ → ℕ // PSub 0 ψ } :=
    ⟨Classical.choose ψ0_ex, (Classical.choose_spec (Classical.choose_spec ψ0_ex)).1,
      Classical.choose (Classical.choose_spec ψ0_ex),
      (Classical.choose_spec (Classical.choose_spec ψ0_ex)).2⟩
  let seq : ∀ m : ℕ, { ψ : ℕ → ℕ // PSub m ψ } := fun m => Nat.rec base (fun k pk => ⟨(step k pk).1, (step k pk).2.1⟩) m
  have hsub_step : ∀ m : ℕ, ∃ α : ℕ → ℕ, StrictMono α ∧ (seq (m + 1)).1 = (seq m).1 ∘ α :=
    fun m => (step m (seq m)).2.2
  have hsub_le : ∀ {m n : ℕ}, m ≤ n → ∃ α : ℕ → ℕ, StrictMono α ∧ (seq n).1 = (seq m).1 ∘ α := by
    intro m n hmn
    induction hmn with
    | refl => exact ⟨id, strictMono_id, rfl⟩
    | @step k _ ih =>
      obtain ⟨α₁, hα₁, h1⟩ := ih
      obtain ⟨α₂, hα₂, h2⟩ := hsub_step k
      exact ⟨α₁ ∘ α₂, hα₁.comp hα₂, by rw [h2, h1]; rfl⟩
  let φ : ℕ → ℕ := fun n => (seq n).1 n
  have hφ_mono : StrictMono φ := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    obtain ⟨α, hα, heq⟩ := hsub_step n
    have h1 : φ (n + 1) = (seq n).1 (α (n + 1)) := by
      dsimp [φ]; rw [heq]; rfl
    have h2 : n < α (n + 1) := lt_of_lt_of_le (Nat.lt_succ_self n) (hα.id_le (n + 1))
    rw [h1]
    exact (seq n).2.1 h2
  -- Define limit `G` from the `m`-th ball limit `g_m`
  have hg_ex : ∀ m : ℕ, ∃ g : ℝ × ℝ → ℝ,
      TendstoUniformlyOn (fun k => F ((seq m).1 k)) g atTop (closedBall (0 : ℝ × ℝ) ((m : ℝ) + 1)) :=
    fun m => (seq m).2.2
  choose g hg using hg_ex
  let G : ℝ × ℝ → ℝ := fun p => g (Nat.ceil (dist p 0)) p
  have hg_agree : ∀ {m n : ℕ}, m ≤ n → ∀ p ∈ closedBall (0 : ℝ × ℝ) ((m : ℝ) + 1), g n p = g m p := by
    intro m n hmn p hp
    obtain ⟨α, hα, heq⟩ := hsub_le hmn
    have hp_n : p ∈ closedBall (0 : ℝ × ℝ) ((n : ℝ) + 1) :=
      closedBall_subset_closedBall (by exact_mod_cast Nat.add_le_add_right hmn 1) hp
    have ht1 : Tendsto (fun k => F ((seq n).1 k) p) atTop (𝓝 (g n p)) :=
      (hg n).tendsto_at hp_n
    have ht2 : Tendsto (fun k => F ((seq n).1 k) p) atTop (𝓝 (g m p)) :=
      (((hg m).tendsto_at hp).comp hα.tendsto_atTop).congr fun k => by
        simp only [Function.comp_apply, heq]
    exact tendsto_nhds_unique ht1 ht2
  have hG_eq : ∀ m : ℕ, ∀ p ∈ closedBall (0 : ℝ × ℝ) ((m : ℝ) + 1), G p = g m p := by
    intro m p hp
    dsimp [G]
    set k := Nat.ceil (dist p 0)
    have hpk : p ∈ closedBall (0 : ℝ × ℝ) ((k : ℝ) + 1) := by
      rw [mem_closedBall]; linarith [Nat.le_ceil (dist p 0)]
    rcases le_total k m with hkm | hmk
    · exact (hg_agree hkm p hpk).symm
    · exact hg_agree hmk p hp
  have hunif : ∀ m : ℕ, TendstoUniformlyOn (fun k => F (φ k)) G atTop (closedBall (0 : ℝ × ℝ) ((m : ℝ) + 1)) := by
    intro m
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hgm := (Metric.tendstoUniformlyOn_iff.mp (hg m)) ε hε
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hgm
    filter_upwards [Filter.eventually_ge_atTop (max K m)] with k hk p hp
    have hkm : m ≤ k := (le_max_right K m).trans hk
    have hkK : K ≤ k := (le_max_left K m).trans hk
    obtain ⟨α, hα, heq⟩ := hsub_le hkm
    have hφk : φ k = (seq m).1 (α k) := by dsimp [φ]; rw [heq]; rfl
    have hαk : K ≤ α k := hkK.trans (hα.id_le k)
    rw [hG_eq m p hp, hφk]
    exact hK (α k) hαk p hp
  have hG_cont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro p
    set m : ℕ := Nat.ceil (dist p 0) + 1
    have hball : closedBall (0 : ℝ × ℝ) ((m : ℝ) + 1) ∈ 𝓝 p := by
      refine Filter.mem_of_superset (Metric.ball_mem_nhds p zero_lt_one) fun q hq => ?_
      rw [mem_closedBall]
      have h1 : dist q 0 ≤ dist q p + dist p 0 := dist_triangle _ _ _
      have h2 : dist q p < 1 := Metric.mem_ball.mp hq
      have h3 : dist p 0 ≤ (Nat.ceil (dist p 0) : ℝ) := Nat.le_ceil _
      have hm : (m : ℝ) = (Nat.ceil (dist p 0) : ℝ) + 1 := by push_cast [m]; rfl
      linarith
    have hcon : ContinuousOn G (closedBall (0 : ℝ × ℝ) ((m : ℝ) + 1)) :=
      (hunif m).continuousOn (Eventually.of_forall fun k => (hCont (φ k)).continuousOn).frequently
    exact hcon.continuousAt hball
  exact ⟨φ, G, hφ_mono, hG_cont, hunif⟩

/-! ### Section 3: `L¹` convergence and Fourier-oddness stability -/

private lemma spinD3A_L1_and_fourier_limit {a : ℝ} (ha : 2 ≤ a)
    {Φ : ℕ → ℝ × ℝ → ℝ} {Φs : ℝ × ℝ → ℝ}
    (hΦ : ∀ j, SpinTestClass a (Φ j))
    (hM2 : ∀ j, spinM2 a (Φ j) = 1)
    (hCont : Continuous Φs)
    (hunif : ∀ m : ℕ, TendstoUniformlyOn Φ Φs atTop (closedBall (0 : ℝ × ℝ) ((m : ℝ) + 1))) :
    IsD4Invariant Φs ∧
    Integrable Φs volume ∧
    Tendsto (fun j => ∫ p : ℝ × ℝ, |Φ j p - Φs p|) atTop (𝓝 0) ∧
    𝓕 (spinToEuc Φs) = -spinToEuc Φs := by
  have hpt : ∀ p : ℝ × ℝ, Tendsto (fun j => Φ j p) atTop (𝓝 (Φs p)) := by
    intro p
    set m := Nat.ceil (dist p 0)
    have hp : p ∈ closedBall (0 : ℝ × ℝ) ((m : ℝ) + 1) := by
      rw [mem_closedBall]; linarith [Nat.le_ceil (dist p 0)]
    exact (hunif m).tendsto_at hp
  have hd4 : IsD4Invariant Φs := by
    refine ⟨fun x y => ?_, fun x y => ?_, fun x y => ?_⟩
    · have h1 := hpt (-x, y)
      have h2 := hpt (x, y)
      simp_rw [(hΦ _).d4_inv.1 x y] at h1
      exact tendsto_nhds_unique h1 h2
    · have h1 := hpt (x, -y)
      have h2 := hpt (x, y)
      simp_rw [(hΦ _).d4_inv.2.1 x y] at h1
      exact tendsto_nhds_unique h1 h2
    · have h1 := hpt (y, x)
      have h2 := hpt (x, y)
      simp_rw [(hΦ _).d4_inv.2.2 x y] at h1
      exact tendsto_nhds_unique h1 h2
  -- Uniform exponential tail bound outside `closedBall 0 R`
  obtain ⟨C, hC_pos, hC⟩ := spinD3A_exp_L1_both ha
  set c : ℝ := (1 / 3 : ℝ) * π * Real.sqrt a
  have hc : 0 < c := by positivity
  have htail_j : ∀ (j : ℕ) (R : ℝ), 0 ≤ R →
      ∫ p in (closedBall (0 : ℝ × ℝ) R)ᶜ, |Φ j p| ≤ 2 * C * Real.exp (-c * R) := by
    intro j R hR
    obtain ⟨hint1, hint2, hle1, hle2⟩ := hC (hΦ j)
    rw [hM2 j, mul_one] at hle1 hle2
    have hdom : Integrable (fun p : ℝ × ℝ =>
        Real.exp (-c * R) * (|Φ j p| * Real.exp (c * |p.1|) + |Φ j p| * Real.exp (c * |p.2|))) :=
      (hint1.add hint2).const_mul _
    calc ∫ p in (closedBall (0 : ℝ × ℝ) R)ᶜ, |Φ j p|
        = ∫ p : ℝ × ℝ, ((closedBall (0 : ℝ × ℝ) R)ᶜ).indicator (fun p => |Φ j p|) p :=
          (integral_indicator isClosed_closedBall.measurableSet.compl).symm
      _ ≤ ∫ p : ℝ × ℝ, Real.exp (-c * R) *
            (|Φ j p| * Real.exp (c * |p.1|) + |Φ j p| * Real.exp (c * |p.2|)) := by
          refine integral_mono ((hΦ j).int.norm.indicator isClosed_closedBall.measurableSet.compl)
            hdom fun p => ?_
          by_cases hp : p ∈ (closedBall (0 : ℝ × ℝ) R)ᶜ
          · rw [Set.indicator_of_mem hp]
            have hgt : R < max |p.1| |p.2| := by
              have h1 : R < dist p (0 : ℝ × ℝ) := by
                simpa only [mem_compl_iff, mem_closedBall, not_le] using hp
              simpa only [Prod.dist_eq, Real.dist_eq, sub_zero, Prod.fst_zero, Prod.snd_zero] using h1
            have h1le : 1 ≤ Real.exp (-c * R) * (Real.exp (c * |p.1|) + Real.exp (c * |p.2|)) := by
              rcases le_total |p.1| |p.2| with h12 | h21
              · rw [max_eq_right h12] at hgt
                have he : 1 ≤ Real.exp (-c * R) * Real.exp (c * |p.2|) := by
                  rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
                have hpos : 0 ≤ Real.exp (-c * R) * Real.exp (c * |p.1|) := by positivity
                linarith
              · rw [max_eq_left h21] at hgt
                have he : 1 ≤ Real.exp (-c * R) * Real.exp (c * |p.1|) := by
                  rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
                have hpos : 0 ≤ Real.exp (-c * R) * Real.exp (c * |p.2|) := by positivity
                linarith
            have hmul := mul_le_mul_of_nonneg_left h1le (abs_nonneg (Φ j p))
            linarith
          · rw [Set.indicator_of_notMem hp]; positivity
      _ = Real.exp (-c * R) *
            ((∫ p : ℝ × ℝ, |Φ j p| * Real.exp (c * |p.1|)) +
             (∫ p : ℝ × ℝ, |Φ j p| * Real.exp (c * |p.2|))) := by
          rw [integral_const_mul, integral_add hint1 hint2]
      _ ≤ Real.exp (-c * R) * (C + C) :=
          mul_le_mul_of_nonneg_left (add_le_add hle1 hle2) (Real.exp_pos _).le
      _ = 2 * C * Real.exp (-c * R) := by ring
  -- Fatou gives the same tail bound for `Φs` and `Integrable Φs volume`
  have htail_s_lint : ∀ R : ℝ, 0 ≤ R →
      ∫⁻ p in (closedBall (0 : ℝ × ℝ) R)ᶜ, ENNReal.ofReal |Φs p| ≤
        ENNReal.ofReal (2 * C * Real.exp (-c * R)) := by
    intro R hR
    have hliminf : ∀ p : ℝ × ℝ, ENNReal.ofReal |Φs p| =
        Filter.liminf (fun j => ENNReal.ofReal |Φ j p|) atTop := fun p =>
      (((ENNReal.continuous_ofReal.comp continuous_abs).tendsto (Φs p)).comp (hpt p)).liminf_eq.symm
    calc ∫⁻ p in (closedBall (0 : ℝ × ℝ) R)ᶜ, ENNReal.ofReal |Φs p|
        = ∫⁻ p in (closedBall (0 : ℝ × ℝ) R)ᶜ,
            Filter.liminf (fun j => ENNReal.ofReal |Φ j p|) atTop := by
          simp_rw [hliminf]
      _ ≤ Filter.liminf (fun j => ∫⁻ p in (closedBall (0 : ℝ × ℝ) R)ᶜ, ENNReal.ofReal |Φ j p|) atTop :=
          lintegral_liminf_le fun j =>
            (ENNReal.continuous_ofReal.comp (continuous_abs.comp (hΦ j).cont)).measurable
      _ ≤ ENNReal.ofReal (2 * C * Real.exp (-c * R)) := by
          refine Filter.liminf_le_of_frequently_le' (Eventually.of_forall fun j => ?_).frequently
          have hja : IntegrableOn (fun p : ℝ × ℝ => |Φ j p|) (closedBall (0 : ℝ × ℝ) R)ᶜ volume :=
            (hΦ j).int.norm.integrableOn.congr (Eventually.of_forall fun _ => Real.norm_eq_abs _)
          rw [← ofReal_integral_eq_lintegral_ofReal hja (Eventually.of_forall fun _ => abs_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (htail_j j R hR)
  have hΦs_int : Integrable Φs volume := by
    have hcomp_int : IntegrableOn Φs (closedBall (0 : ℝ × ℝ) 1) volume :=
      hCont.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)
    have htail_int : IntegrableOn Φs (closedBall (0 : ℝ × ℝ) 1)ᶜ volume := by
      refine ⟨hCont.aestronglyMeasurable, ?_⟩
      have h1 := htail_s_lint 1 zero_le_one
      have heq : (∫⁻ p in (closedBall (0 : ℝ × ℝ) 1)ᶜ, ‖Φs p‖ₑ) =
          ∫⁻ p in (closedBall (0 : ℝ × ℝ) 1)ᶜ, ENNReal.ofReal |Φs p| := by
        refine lintegral_congr fun p => ?_
        rw [← Real.eNorm_eq_ofReal_abs]
      rw [hasFiniteIntegral_iff_eNorm, heq]
      exact lt_of_le_of_lt h1 ENNReal.ofReal_lt_top
    have hunion : (closedBall (0 : ℝ × ℝ) 1) ∪ (closedBall (0 : ℝ × ℝ) 1)ᶜ = Set.univ :=
      Set.union_compl_self _
    have h1 := hcomp_int.union htail_int
    rwa [hunion, integrableOn_univ] at h1
  have htail_s : ∀ R : ℝ, 0 ≤ R →
      ∫ p in (closedBall (0 : ℝ × ℝ) R)ᶜ, |Φs p| ≤ 2 * C * Real.exp (-c * R) := by
    intro R hR
    have h1 := htail_s_lint R hR
    have hsa : IntegrableOn (fun p : ℝ × ℝ => |Φs p|) (closedBall (0 : ℝ × ℝ) R)ᶜ volume :=
      hΦs_int.norm.integrableOn.congr (Eventually.of_forall fun _ => Real.norm_eq_abs _)
    rw [← ofReal_integral_eq_lintegral_ofReal hsa (Eventually.of_forall fun _ => abs_nonneg _)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  -- `L¹` convergence `∫ |Φ j - Φs| → 0`
  have hL1_tend : Tendsto (fun j => ∫ p : ℝ × ℝ, |Φ j p - Φs p|) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- Choose `m : ℕ` so `4 * C * exp(-c * (m + 1)) < ε / 2`
    have hex_m : ∃ m : ℕ, 4 * C * Real.exp (-c * ((m : ℝ) + 1)) < ε / 2 := by
      have ht : Tendsto (fun m : ℕ => 4 * C * Real.exp (-c * ((m : ℝ) + 1))) atTop (𝓝 0) := by
        have h1 : Tendsto (fun m : ℕ => -c * ((m : ℝ) + 1)) atTop atBot := by
          have h2 : Tendsto (fun m : ℕ => c * ((m : ℝ) + 1)) atTop atTop :=
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop hc
          exact (tendsto_neg_atTop_atBot.comp h2).congr fun m => by
            simp only [Function.comp_apply, neg_mul]
        simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (4 * C)
      exact (ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))).exists
    obtain ⟨m, hm⟩ := hex_m
    set R : ℝ := (m : ℝ) + 1
    have hR : 0 ≤ R := by positivity
    have hvol_lt : volume (closedBall (0 : ℝ × ℝ) R) < ∞ :=
      (isCompact_closedBall (0 : ℝ × ℝ) R).measure_lt_top
    set V : ℝ := (volume (closedBall (0 : ℝ × ℝ) R)).toReal
    have hV_nn : 0 ≤ V := ENNReal.toReal_nonneg
    have hδ : 0 < ε / (2 * (V + 1)) := by positivity
    have hu := (Metric.tendstoUniformlyOn_iff.mp (hunif m)) (ε / (2 * (V + 1))) hδ
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hu
    refine ⟨N, fun j hj => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
    have hdiff_int : Integrable (fun p : ℝ × ℝ => |Φ j p - Φs p|) :=
      ((hΦ j).int.sub hΦs_int).norm
    have hsplit : (∫ p : ℝ × ℝ, |Φ j p - Φs p|) =
        (∫ p in closedBall (0 : ℝ × ℝ) R, |Φ j p - Φs p|) +
        (∫ p in (closedBall (0 : ℝ × ℝ) R)ᶜ, |Φ j p - Φs p|) := by
      rw [← integral_indicator isClosed_closedBall.measurableSet,
          ← integral_indicator isClosed_closedBall.measurableSet.compl,
          ← integral_add (hdiff_int.indicator isClosed_closedBall.measurableSet)
            (hdiff_int.indicator isClosed_closedBall.measurableSet.compl)]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      dsimp only
      by_cases hp : p ∈ closedBall (0 : ℝ × ℝ) R
      · have hpc : p ∉ (closedBall (0 : ℝ × ℝ) R)ᶜ := not_not.mpr hp
        rw [Set.indicator_of_mem hp, Set.indicator_of_notMem hpc, add_zero]
      · have hpc : p ∈ (closedBall (0 : ℝ × ℝ) R)ᶜ := hp
        rw [Set.indicator_of_notMem hp, Set.indicator_of_mem hpc, zero_add]
    have hcore : (∫ p in closedBall (0 : ℝ × ℝ) R, |Φ j p - Φs p|) < ε / 2 := by
      have h1 : (∫ p in closedBall (0 : ℝ × ℝ) R, |Φ j p - Φs p|) ≤
          ∫ _ in closedBall (0 : ℝ × ℝ) R, (ε / (2 * (V + 1))) := by
        refine setIntegral_mono_on hdiff_int.integrableOn (integrableOn_const hvol_lt.ne)
          isClosed_closedBall.measurableSet fun p hp => ?_
        have hd := hN j hj p hp
        rw [Real.dist_eq, abs_sub_comm] at hd
        exact hd.le
      rw [setIntegral_const, smul_eq_mul, Measure.real_def] at h1
      have h2 : V * (ε / (2 * (V + 1))) < ε / 2 := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
      linarith
    have htail : (∫ p in (closedBall (0 : ℝ × ℝ) R)ᶜ, |Φ j p - Φs p|) ≤
        4 * C * Real.exp (-c * R) := by
      have hja : IntegrableOn (fun p : ℝ × ℝ => |Φ j p|) (closedBall (0 : ℝ × ℝ) R)ᶜ volume :=
        (hΦ j).int.norm.integrableOn.congr (Eventually.of_forall fun _ => Real.norm_eq_abs _)
      have hsa : IntegrableOn (fun p : ℝ × ℝ => |Φs p|) (closedBall (0 : ℝ × ℝ) R)ᶜ volume :=
        hΦs_int.norm.integrableOn.congr (Eventually.of_forall fun _ => Real.norm_eq_abs _)
      have h1 : (∫ p in (closedBall (0 : ℝ × ℝ) R)ᶜ, |Φ j p - Φs p|) ≤
          ∫ p in (closedBall (0 : ℝ × ℝ) R)ᶜ, (|Φ j p| + |Φs p|) :=
        setIntegral_mono_on hdiff_int.integrableOn (hja.add hsa)
          isClosed_closedBall.measurableSet.compl fun p _ => abs_sub _ _
      rw [integral_add hja hsa] at h1
      linarith [htail_j j R hR, htail_s R hR]
    linarith
  -- Fourier oddness passes to the limit via `L¹` convergence
  have hfodd : 𝓕 (spinToEuc Φs) = -spinToEuc Φs := by
    ext ξ
    simp only [Pi.neg_apply]
    have hF_tend : Tendsto (fun j => 𝓕 (spinToEuc (Φ j)) ξ) atTop (𝓝 (𝓕 (spinToEuc Φs) ξ)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hL1_tend) ε hε
      refine ⟨N, fun j hj => ?_⟩
      rw [dist_eq_norm, Real.fourier_eq, Real.fourier_eq]
      have hint_j : Integrable (fun x : RadialSpace 1 =>
          Real.fourierChar (-⟪x, ξ⟫) • spinToEuc (Φ j) x) := by
        have hbase : Integrable (fun x : RadialSpace 1 => |Φ j (aE2ToProd x)|) :=
          aVolume_preserving_e2ToProd.integrable_comp_of_integrable (hΦ j).int.norm
        refine hbase.mono' ?_ (Eventually.of_forall fun x => ?_)
        · have hcont : Continuous (fun x : RadialSpace 1 =>
              Complex.exp (((2 * π * -⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * spinToEuc (Φ j) x) := by
            have h0 : Continuous (fun x : RadialSpace 1 => x 0) :=
              (continuous_apply (0 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
            have h1 : Continuous (fun x : RadialSpace 1 => x 1) :=
              (continuous_apply (1 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
            have hsp : Continuous (spinToEuc (Φ j)) :=
              Complex.continuous_ofReal.comp ((hΦ j).cont.comp (h0.prodMk h1))
            fun_prop
          have heq : (fun x : RadialSpace 1 => Real.fourierChar (-⟪x, ξ⟫) • spinToEuc (Φ j) x) =
              fun x => Complex.exp (((2 * π * -⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * spinToEuc (Φ j) x := by
            ext x; rw [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
          rw [heq]; exact hcont.aestronglyMeasurable
        · rw [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul, spinToEuc,
              Complex.norm_real, Real.norm_eq_abs]; rfl
      have hint_s : Integrable (fun x : RadialSpace 1 =>
          Real.fourierChar (-⟪x, ξ⟫) • spinToEuc Φs x) := by
        have hbase : Integrable (fun x : RadialSpace 1 => |Φs (aE2ToProd x)|) :=
          aVolume_preserving_e2ToProd.integrable_comp_of_integrable hΦs_int.norm
        refine hbase.mono' ?_ (Eventually.of_forall fun x => ?_)
        · have hcont : Continuous (fun x : RadialSpace 1 =>
              Complex.exp (((2 * π * -⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * spinToEuc Φs x) := by
            have h0 : Continuous (fun x : RadialSpace 1 => x 0) :=
              (continuous_apply (0 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
            have h1 : Continuous (fun x : RadialSpace 1 => x 1) :=
              (continuous_apply (1 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
            have hsp : Continuous (spinToEuc Φs) :=
              Complex.continuous_ofReal.comp (hCont.comp (h0.prodMk h1))
            fun_prop
          have heq : (fun x : RadialSpace 1 => Real.fourierChar (-⟪x, ξ⟫) • spinToEuc Φs x) =
              fun x => Complex.exp (((2 * π * -⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) * spinToEuc Φs x := by
            ext x; rw [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
          rw [heq]; exact hcont.aestronglyMeasurable
        · rw [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul, spinToEuc,
              Complex.norm_real, Real.norm_eq_abs]; rfl
      rw [← integral_sub hint_j hint_s]
      have hle : ‖∫ x : RadialSpace 1,
            (Real.fourierChar (-⟪x, ξ⟫) • spinToEuc (Φ j) x -
             Real.fourierChar (-⟪x, ξ⟫) • spinToEuc Φs x)‖ ≤
          ∫ p : ℝ × ℝ, |Φ j p - Φs p| := by
        calc ‖∫ x : RadialSpace 1,
              (Real.fourierChar (-⟪x, ξ⟫) • spinToEuc (Φ j) x -
               Real.fourierChar (-⟪x, ξ⟫) • spinToEuc Φs x)‖
            ≤ ∫ x : RadialSpace 1,
              ‖Real.fourierChar (-⟪x, ξ⟫) • spinToEuc (Φ j) x -
               Real.fourierChar (-⟪x, ξ⟫) • spinToEuc Φs x‖ :=
              norm_integral_le_integral_norm _
          _ = ∫ x : RadialSpace 1, |Φ j (aE2ToProd x) - Φs (aE2ToProd x)| := by
              refine integral_congr_ae (Eventually.of_forall fun x => ?_)
              dsimp only
              rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, ← mul_sub,
                  norm_mul, Circle.norm_coe, one_mul, spinToEuc, spinToEuc, ← Complex.ofReal_sub,
                  Complex.norm_real, Real.norm_eq_abs]; rfl
          _ = ∫ p : ℝ × ℝ, |Φ j p - Φs p| :=
              aVolume_preserving_e2ToProd.integral_comp' (g := fun p : ℝ × ℝ => |Φ j p - Φs p|)
      have hdist := hN j hj
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at hdist
      linarith
    have hneg_tend : Tendsto (fun j => 𝓕 (spinToEuc (Φ j)) ξ) atTop (𝓝 (-spinToEuc Φs ξ)) := by
      have heq : (fun j => 𝓕 (spinToEuc (Φ j)) ξ) = fun j => -spinToEuc (Φ j) ξ := by
        ext j; exact congrFun (hΦ j).fourier_odd ξ
      rw [heq]
      exact (Complex.continuous_ofReal.neg.tendsto (Φs (ξ 0, ξ 1))).comp (hpt (ξ 0, ξ 1))
    exact tendsto_nhds_unique hF_tend hneg_tend
  exact ⟨hd4, hΦs_int, hL1_tend, hfodd⟩

/-! ### Section 4: Nonemptiness of the certified feasible set with compact prescribed sites `F` -/

private lemma spinCertifiedThr_quadrant_F_nonempty {a : ℝ} (ha : 2 ≤ a)
    {F : Set (ℝ × ℝ)} (hFc : IsCompact F) (hFs : IsSwapInvariantSet F)
    (hFsub : F ⊆ spinConeB 0 ∩ {p : ℝ × ℝ | 0 < p.1 + p.2}) :
    {T : ℝ | 0 < T ∧ ∃ Φ, SpinCertifiedT a Φ ∧ 0 < spinVacT a Φ ∧
      ∀ p ∈ F ∪ spinConeSlice (spinConeB 0) T, 0 ≤ Φ p}.Nonempty := by
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hc_pos : (0 : ℝ) < 12 * a := by linarith
  have hc_shift : 12 * virasoroProblem.totalShift ≤ 12 * a := by
    rw [virasoroProblem_totalShift]; linarith
  let F_rad : Set ℝ := (fun p : ℝ × ℝ => p.1 + p.2) '' F
  have hFrad_c : IsCompact F_rad := hFc.image (continuous_fst.add continuous_snd)
  have hFrad_sub : F_rad ⊆ Ioi (0 : ℝ) := by
    rintro _ ⟨p, hpF, rfl⟩; exact (hFsub hpF).2
  obtain ⟨τ₁, hτ₁, g₁, hg₁⟩ := exists_feasible_of_compact virasoroProblem hc_pos hc_shift
    hFrad_c hFrad_sub
  have hne : (constrainedGaps virasoroProblem (12 * a) F_rad).Nonempty := ⟨τ₁, hτ₁, g₁, hg₁⟩
  set T₁ : ℝ := max 1 (constrainedThreshold virasoroProblem (12 * a) F_rad + 1)
  have hT₁_pos : 0 < T₁ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hm_ex : ∃ m : ℝ, 0 < m ∧ F ⊆ {p : ℝ × ℝ | m ≤ p.1 + p.2} := by
    rcases F.eq_empty_or_nonempty with rfl | hFne
    · exact ⟨1, one_pos, empty_subset _⟩
    · obtain ⟨p₀, hp₀F, hp₀min⟩ := hFc.exists_isMinOn hFne
        (continuous_fst.add continuous_snd).continuousOn
      exact ⟨p₀.1 + p₀.2, (hFsub hp₀F).2, fun p hp => isMinOn_iff.1 hp₀min p hp⟩
  obtain ⟨m, hm_pos, hFm⟩ := hm_ex
  set X : Set (ℝ × ℝ) := F ∪ spinConeSlice (spinConeB 0) T₁
  have hno : ∀ N q, ¬ spinOddLagFeasible a N X q := by
    rintro N q ⟨hq_mem, hq_nn, hq_vac⟩
    have hmem : T₁ ∈ {T : ℝ | 0 < T ∧ ∃ Φ, SpinCertifiedT a Φ ∧ 0 < spinVacT a Φ ∧
        ∀ p ∈ F ∪ spinConeSlice (spinConeB 0) T, 0 ≤ Φ p} :=
      ⟨hT₁_pos, fun p => Real.exp (-2 * π * (p.1 + p.2)) * q p,
        exp_mul_mem_SpinCertifiedT hq_mem, hq_vac, hq_nn⟩
    rw [hemp] at hmem
    exact hmem
  have hXc : IsClosed X := hFc.isClosed.union (isClosed_spinConeSlice (isClosed_spinConeB 0) T₁)
  have hXs : IsSwapInvariantSet X :=
    fun p hp => hp.elim (fun h => Or.inl (hFs p h))
      (fun h => Or.inr (isSwapInvariantSet_spinConeSlice (isSwapInvariantSet_spinConeB 0) T₁ p h))
  have hXsub : X ⊆ spinConeB 0 ∩ {p : ℝ × ℝ | min m T₁ ≤ p.1 + p.2} := by
    rintro p (hpF | ⟨hpΩ, hpT⟩)
    · exact ⟨(hFsub hpF).1, (min_le_left m T₁).trans (hFm hpF)⟩
    · exact ⟨hpΩ, (min_le_right m T₁).trans hpT⟩
  obtain ⟨meas, -⟩ := (spinDLPi ha le_rfl (lt_min hm_pos hT₁_pos) hXc hXs hXsub).1 hno
  let meas_12 : SpinCrossingMeasureOn (12 * a / 12) X :=
    { ν := meas.ν
      supp := meas.supp
      finite_laplace := meas.finite_laplace
      crossing := fun hL hR => by rw [show 12 * a / 12 = a by ring]; exact meas.crossing hL hR }
  let rad_meas : AdmissibleCrossingMeasure virasoroProblem (12 * a / 12) :=
    meas_12.toRadAdmissible (fun _ hp => (lt_min hm_pos hT₁_pos).le.trans (hXsub hp).2)
  have hrad_supp : rad_meas.ν (F_rad ∪ Ici T₁)ᶜ = 0 := by
    change spinRadMarginal meas.ν (F_rad ∪ Ici T₁)ᶜ = 0
    unfold spinRadMarginal
    have hmeas_sum : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
    rw [Measure.map_apply hmeas_sum (hFrad_c.isClosed.union isClosed_Ici).measurableSet.compl]
    have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' (F_rad ∪ Ici T₁)ᶜ ⊆ Xᶜ := by
      intro p hp hpX
      apply hp
      rcases hpX with hpF | ⟨_, hpT⟩
      · exact Or.inl ⟨p, hpF, rfl⟩
      · exact Or.inr hpT
    exact measure_mono_null hsub meas.supp
  have hle := le_constrainedThreshold_of_crossingMeasure virasoroProblem hc_pos hc_shift hne rad_meas hrad_supp
  have hgt : constrainedThreshold virasoroProblem (12 * a) F_rad < T₁ :=
    lt_of_lt_of_le (by linarith) (le_max_right _ _)
  linarith

/-! ### Section 5: Main Theorem `spinDA` (`sd:A`) -/

set_option maxHeartbeats 600000 in
/-- **`sd:A`** (Proposition SD-A: attainment of the continuous-spin test infimum on the quadrant
with optional compact prescribed sites `F`, and complementary slackness), proved unconditionally
for all `a ≥ 2`. -/
theorem spinDA : SpinDA := by
  intro a ha F hFc hFs hFsub
  dsimp only
  set S_F : Set ℝ := {T : ℝ | 0 < T ∧ ∃ Φ, SpinTestClass a Φ ∧ 0 < spinPhiVac a Φ ∧
    ∀ p ∈ F ∪ spinConeSlice (spinConeB 0) T, 0 ≤ spinEvalT Φ p} with hSF_def
  set TF : ℝ := sInf S_F with hTF_def
  -- Step 1: `TF = spinCertifiedThr a (spinConeB 0) F > 0`, and there is an attaining crossing measure
  have hcert_ne := spinCertifiedThr_quadrant_F_nonempty ha hFc hFs hFsub
  set TcertF : ℝ := spinCertifiedThr a (spinConeB 0) F with hTcertF_def
  have hSF_ne : S_F.Nonempty := by
    obtain ⟨T, hT0, Φ, hΦc, hΦvac, hΦnn⟩ := hcert_ne
    refine ⟨T, hT0, spinLiftTToR Φ, (spinLiftTToR_mem_SpinTestClassJ ha hΦc).base,
      hΦvac, fun p hp => ?_⟩
    have hp0 : 0 ≤ p.1 ∧ 0 ≤ p.2 := by
      rcases hp with hpF | ⟨hpΩ, _⟩
      · have h := (hFsub hpF).1; simp only [spinConeB, neg_zero, mem_ofPred_eq] at h; exact h
      · simp only [spinConeB, neg_zero, mem_ofPred_eq] at hpΩ; exact hpΩ
    have heval : spinEvalT (spinLiftTToR Φ) p = Φ p := by
      unfold spinEvalT spinLiftTToR
      rw [Real.sq_sqrt (by linarith [hp0.1]), Real.sq_sqrt (by linarith [hp0.2])]
      simp
    rw [heval]; exact hΦnn p hp
  have hTF_le_cert : TF ≤ TcertF := by
    rw [hTF_def, hTcertF_def]; unfold spinCertifiedThr
    refine le_csInf hcert_ne ?_
    rintro T ⟨hT0, Φ, hΦc, hΦvac, hΦnn⟩
    refine csInf_le ⟨0, fun τ hτ => hτ.1.le⟩ ⟨hT0, spinLiftTToR Φ,
      (spinLiftTToR_mem_SpinTestClassJ ha hΦc).base, hΦvac, fun p hp => ?_⟩
    have hp0 : 0 ≤ p.1 ∧ 0 ≤ p.2 := by
      rcases hp with hpF | ⟨hpΩ, _⟩
      · have h := (hFsub hpF).1; simp only [spinConeB, neg_zero, mem_ofPred_eq] at h; exact h
      · simp only [spinConeB, neg_zero, mem_ofPred_eq] at hpΩ; exact hpΩ
    have heval : spinEvalT (spinLiftTToR Φ) p = Φ p := by
      unfold spinEvalT spinLiftTToR
      rw [Real.sq_sqrt (by linarith [hp0.1]), Real.sq_sqrt (by linarith [hp0.2])]
      simp
    rw [heval]; exact hΦnn p hp
  have hTempty_le_TF : spinThrInf (SpinTestClass a) liouvilleCone a ≤ TF := by
    rw [hTF_def]; unfold spinThrInf
    refine le_csInf hSF_ne ?_
    rintro T ⟨hT0, Φ, hΦ, hΦvac, hΦnn⟩
    refine csInf_le ⟨0, fun τ hτ => hτ.1.le⟩ ⟨hT0, Φ, hΦ, hΦvac, fun p hp => ?_⟩
    apply hΦnn p (Or.inr _)
    rwa [spinConeSlice_quadrant]
  have hTempty_pos : 0 < spinThrInf (SpinTestClass a) liouvilleCone a :=
    (spinThrInf_quadrant_hierarchy ha).1
  have hTF_pos : 0 < TF := lt_of_lt_of_le hTempty_pos hTempty_le_TF
  have hTcertF_pos : 0 < TcertF := lt_of_lt_of_le hTF_pos hTF_le_cert
  obtain ⟨_, ⟨meas₀, _⟩, _⟩ := spinDSD_cone ha le_rfl (isClosed_spinConeB 0)
    (isSwapInvariantSet_spinConeB 0) Subset.rfl hFc hFs hFsub hTcertF_pos
  have hTcertF_le_TF : TcertF ≤ TF := by
    rw [hTF_def]
    refine le_csInf hSF_ne ?_
    rintro T ⟨hT0, Φ, hΦ, hΦvac, hΦnn⟩
    by_contra hlt
    push Not at hlt
    have hΦnn_cone : ∀ p ∈ liouvilleCone T, 0 ≤ spinEvalT Φ p := fun p hp =>
      hΦnn p (Or.inr (by rwa [spinConeSlice_quadrant]))
    have hsubQ : F ∪ spinConeSlice (spinConeB 0) TcertF ⊆ spinConeB 0 :=
      union_subset (hFsub.trans inter_subset_left) inter_subset_left
    have hW := spinDW ha (meas₀.toQuadrant hsubQ) hΦ hT0 hΦnn_cone
    have hnn_int : 0 ≤ ∫ p, spinEvalT Φ p ∂meas₀.ν := by
      refine integral_nonneg_of_ae ?_
      have : ∀ᵐ p ∂meas₀.ν, p ∉ (F ∪ spinConeSlice (spinConeB 0) TcertF)ᶜ :=
        measure_eq_zero_iff_ae_notMem.1 meas₀.supp
      filter_upwards [this] with p hp
      rcases not_not.mp hp with hpF | ⟨hpΩ, hpT⟩
      · exact hΦnn p (Or.inl hpF)
      · exact hΦnn p (Or.inr ⟨hpΩ, hlt.le.trans hpT⟩)
    have hle_vac : ∫ p, spinEvalT Φ p ∂meas₀.ν ≤ -spinPhiVac a Φ := hW.2.1
    linarith
  have hTF_eq_cert : TF = TcertF := le_antisymm hTF_le_cert hTcertF_le_TF
  have hmeas₀_TF : SpinCrossingMeasureOn a (F ∪ spinConeSlice (spinConeB 0) TF) := by
    rwa [hTF_eq_cert]
  -- Step 2: Construct an `M_2`-normalized strictly feasible minimizing sequence `(T_j, Φ_j)`
  have hex_seq : ∀ j : ℕ, ∃ (Tj : ℝ) (Φj : ℝ × ℝ → ℝ),
      TF ≤ Tj ∧ Tj < TF + 1 / ((j : ℝ) + 1) ∧
      SpinTestClass a Φj ∧ spinM2 a Φj = 1 ∧ 0 < spinPhiVac a Φj ∧
      (∀ p ∈ F ∪ spinConeSlice (spinConeB 0) Tj, 0 ≤ spinEvalT Φj p) := by
    intro j
    have hlt : TF < TF + 1 / ((j : ℝ) + 1) := lt_add_of_pos_right TF (by positivity)
    obtain ⟨Tj, hTj_mem, hTj_lt⟩ := exists_lt_of_csInf_lt hSF_ne hlt
    have hTF_le_Tj : TF ≤ Tj := csInf_le ⟨0, fun τ hτ => hτ.1.le⟩ hTj_mem
    obtain ⟨_, Ψ, hΨ, hΨ_vac, hΨ_nn⟩ := hTj_mem
    have hM2_pos : 0 < spinM2 a Ψ := by
      have hvac_le : spinPhiVac a Ψ ≤ spinM2 a Ψ := by
        unfold spinPhiVac spinM2
        calc -(∫ p : ℝ × ℝ, Ψ p * spinV1 a p.1 * spinV1 a p.2)
            ≤ |∫ p : ℝ × ℝ, Ψ p * spinV1 a p.1 * spinV1 a p.2| := neg_le_abs _
          _ ≤ ∫ p : ℝ × ℝ, |Ψ p * spinV1 a p.1 * spinV1 a p.2| := abs_integral_le_integral_abs
          _ = ∫ p : ℝ × ℝ, |Ψ p| * spinV1 a p.1 * spinV1 a p.2 := by
              refine integral_congr_ae (Eventually.of_forall fun p => ?_)
              dsimp only
              rw [abs_mul, abs_mul, abs_of_nonneg (spinV1_nonneg ha p.1),
                  abs_of_nonneg (spinV1_nonneg ha p.2)]
      linarith
    let c : ℝ := (spinM2 a Ψ)⁻¹
    have hc_pos : 0 < c := inv_pos.mpr hM2_pos
    let Φj : ℝ × ℝ → ℝ := fun p => c * Ψ p
    have hΦj : SpinTestClass a Φj := by
      refine ⟨continuous_const.mul hΨ.cont,
        hΨ.int.const_mul c,
        ⟨fun x y => by simp [Φj, hΨ.d4_inv.1], fun x y => by simp [Φj, hΨ.d4_inv.2.1],
         fun x y => by simp [Φj, hΨ.d4_inv.2.2]⟩,
        ?_, ?_⟩
      · have hto : spinToEuc Φj = (c : ℂ) • spinToEuc Ψ := by
          ext x; simp [spinToEuc, Φj]
        ext w
        rw [hto, Real.fourier_eq]
        simp only [Pi.neg_apply, Pi.smul_apply]
        have h1 : (∫ v : RadialSpace 1, Real.fourierChar (-⟪v, w⟫) • ((c : ℂ) • spinToEuc Ψ v)) =
            (c : ℂ) • ∫ v : RadialSpace 1, Real.fourierChar (-⟪v, w⟫) • spinToEuc Ψ v := by
          rw [← integral_smul]
          refine integral_congr_ae (Eventually.of_forall fun v => ?_)
          simp only [Circle.smul_def, smul_eq_mul]; ring
        rw [h1, ← Real.fourier_eq, hΨ.fourier_odd, Pi.neg_apply, smul_neg]
      · have heq : (fun p : ℝ × ℝ => |Φj p| * spinV1 a p.1 * spinV1 a p.2) =
            fun p => c * (|Ψ p| * spinV1 a p.1 * spinV1 a p.2) := by
          ext p; simp only [Φj, abs_mul, abs_of_pos hc_pos]; ring
        rw [heq]; exact hΨ.int_M2.const_mul c
    have hΦj_M2 : spinM2 a Φj = 1 := by
      unfold spinM2
      have heq : (fun p : ℝ × ℝ => |Φj p| * spinV1 a p.1 * spinV1 a p.2) =
          fun p => c * (|Ψ p| * spinV1 a p.1 * spinV1 a p.2) := by
        ext p; simp only [Φj, abs_mul, abs_of_pos hc_pos]; ring
      rw [heq, integral_const_mul]
      exact inv_mul_cancel₀ hM2_pos.ne'
    have hΦj_vac : 0 < spinPhiVac a Φj := by
      unfold spinPhiVac
      have heq : (fun p : ℝ × ℝ => Φj p * spinV1 a p.1 * spinV1 a p.2) =
          fun p => c * (Ψ p * spinV1 a p.1 * spinV1 a p.2) := by
        ext p; simp only [Φj]; ring
      rw [heq, integral_const_mul]
      unfold spinPhiVac at hΨ_vac
      nlinarith
    have hΦj_nn : ∀ p ∈ F ∪ spinConeSlice (spinConeB 0) Tj, 0 ≤ spinEvalT Φj p := by
      intro p hp
      unfold spinEvalT; dsimp [Φj]
      exact mul_nonneg hc_pos.le (hΨ_nn p hp)
    exact ⟨Tj, Φj, hTF_le_Tj, hTj_lt, hΦj, hΦj_M2, hΦj_vac, hΦj_nn⟩
  choose Tseq Φseq hTF_le_Tseq hTseq_lt hΦseq hΦseq_M2 hΦseq_vac hΦseq_nn using hex_seq
  -- Step 3: Extract locally uniformly convergent subsequence via Arzelà–Ascoli
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := spinTestClass_L1_le_M2 ha
  obtain ⟨L, hL_pos, hL⟩ := spinD3A_lipschitz ha
  have hBd : ∀ j, ∀ p : ℝ × ℝ, |Φseq j p| ≤ C₀ := fun j p => by
    have := (hC₀ (hΦseq j)).1 p; rwa [hΦseq_M2 j, mul_one] at this
  have hLip : ∀ j, ∀ p q : ℝ × ℝ, |Φseq j p - Φseq j q| ≤ L * dist p q := fun j p q => by
    have := hL (hΦseq j) p q; rwa [hΦseq_M2 j, mul_one] at this
  obtain ⟨φ, Φs, hφ_mono, hΦs_cont, hunif⟩ :=
    spinD3A_arzela_diagonal hC₀_pos.le hL_pos.le (fun j => (hΦseq j).cont) hBd hLip
  -- Step 4: `IsD4Invariant Φs`, `Integrable Φs volume`, and `𝓕 (spinToEuc Φs) = -spinToEuc Φs`
  obtain ⟨hΦs_d4, hΦs_int, -, hΦs_fodd⟩ :=
    spinD3A_L1_and_fourier_limit ha (fun j => hΦseq (φ j)) (fun j => hΦseq_M2 (φ j)) hΦs_cont hunif
  -- Step 5: Apply `Duality.compact_negative_mass` with `μ = V_1(p.1) V_1(p.2) dp`
  let μ : Measure (ℝ × ℝ) :=
    volume.withDensity (fun p : ℝ × ℝ => ENNReal.ofReal (spinV1 a p.1 * spinV1 a p.2))
  have hmeas_V : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (spinV1 a p.1 * spinV1 a p.2)) := by
    have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
    exact ENNReal.measurable_ofReal.comp
      ((hV.comp continuous_fst).measurable.mul (hV.comp continuous_snd).measurable)
  have : IsFiniteMeasureOnCompacts μ := by
    refine ⟨fun K hK => ?_⟩
    have hV_cont : Continuous (fun p : ℝ × ℝ => spinV1 a p.1 * spinV1 a p.2) := by
      have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
      exact (hV.comp continuous_fst).mul (hV.comp continuous_snd)
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hV_cont.continuousOn
    rw [withDensity_apply _ hK.measurableSet]
    calc ∫⁻ p in K, ENNReal.ofReal (spinV1 a p.1 * spinV1 a p.2)
        ≤ ∫⁻ _ in K, ENNReal.ofReal (max M 0) := by
          refine setLIntegral_mono_ae aemeasurable_const (Eventually.of_forall fun p hp => ?_)
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := hM p hp
          rw [Real.norm_of_nonneg (mul_nonneg (spinV1_nonneg ha p.1) (spinV1_nonneg ha p.2))] at h1
          exact h1.trans (le_max_left _ _)
      _ = ENNReal.ofReal (max M 0) * volume K := setLIntegral_const K _
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
  have hμ_int_iff : ∀ g : ℝ × ℝ → ℝ, Integrable g μ ↔
      Integrable (fun p : ℝ × ℝ => g p * spinV1 a p.1 * spinV1 a p.2) volume := by
    intro g
    rw [integrable_withDensity_iff_integrable_smul₀' hmeas_V.aemeasurable
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have heq : (fun p : ℝ × ℝ => (ENNReal.ofReal (spinV1 a p.1 * spinV1 a p.2)).toReal • g p) =
        fun p => g p * spinV1 a p.1 * spinV1 a p.2 := by
      ext p
      rw [ENNReal.toReal_ofReal (mul_nonneg (spinV1_nonneg ha p.1) (spinV1_nonneg ha p.2)),
          smul_eq_mul]; ring
    rw [heq]
  have hμ_int_eq : ∀ g : ℝ × ℝ → ℝ,
      ∫ p : ℝ × ℝ, g p ∂μ = ∫ p : ℝ × ℝ, g p * spinV1 a p.1 * spinV1 a p.2 := by
    intro g
    rw [integral_withDensity_eq_integral_toReal_smul hmeas_V
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (mul_nonneg (spinV1_nonneg ha p.1) (spinV1_nonneg ha p.2)),
        smul_eq_mul]; ring
  set mK : ℕ := Nat.ceil (Real.sqrt (2 * (TF + 1)))
  set K : Set (ℝ × ℝ) := closedBall (0 : ℝ × ℝ) ((mK : ℝ) + 1)
  have hK_neg : ∀ j : ℕ, ∀ p : ℝ × ℝ, p ∉ K → 0 ≤ Φseq (φ j) p := by
    intro j p hp
    have hgt : (mK : ℝ) + 1 < dist p (0 : ℝ × ℝ) := by
      simpa only [K, mem_closedBall, not_le] using hp
    have hmax : Real.sqrt (2 * (TF + 1)) < max |p.1| |p.2| := by
      have h1 : Real.sqrt (2 * (TF + 1)) ≤ mK := Nat.le_ceil _
      have h2 : dist p (0 : ℝ × ℝ) = max |p.1| |p.2| := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; simp
      linarith
    have hsq : 2 * (TF + 1) < p.1 ^ 2 + p.2 ^ 2 := by
      have h1 : 2 * (TF + 1) < (max |p.1| |p.2|) ^ 2 := by
        have := pow_lt_pow_left₀ hmax (Real.sqrt_nonneg _) (by norm_num : 2 ≠ 0)
        rwa [Real.sq_sqrt (by linarith)] at this
      rcases le_total |p.1| |p.2| with h12 | h21
      · rw [max_eq_right h12, sq_abs] at h1; nlinarith [sq_nonneg p.1]
      · rw [max_eq_left h21, sq_abs] at h1; nlinarith [sq_nonneg p.2]
    have hTj_le : Tseq (φ j) ≤ TF + 1 := by
      have h1 : 1 / ((φ j : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) (φ j)]) (by positivity)
      linarith [hTseq_lt (φ j)]
    have hmem : (p.1 ^ 2 / 2, p.2 ^ 2 / 2) ∈ F ∪ spinConeSlice (spinConeB 0) (Tseq (φ j)) :=
      Or.inr ⟨⟨by simp; positivity, by simp; positivity⟩, by change Tseq (φ j) ≤ p.1 ^ 2 / 2 + p.2 ^ 2 / 2; linarith⟩
    have hge := hΦseq_nn (φ j) _ hmem
    unfold spinEvalT at hge
    have heq : Φseq (φ j) (Real.sqrt (2 * (p.1 ^ 2 / 2)), Real.sqrt (2 * (p.2 ^ 2 / 2))) = Φseq (φ j) p := by
      have h1 : Real.sqrt (2 * (p.1 ^ 2 / 2)) = |p.1| := by
        rw [show 2 * (p.1 ^ 2 / 2) = p.1 ^ 2 by ring, Real.sqrt_sq_eq_abs]
      have h2 : Real.sqrt (2 * (p.2 ^ 2 / 2)) = |p.2| := by
        rw [show 2 * (p.2 ^ 2 / 2) = p.2 ^ 2 by ring, Real.sqrt_sq_eq_abs]
      rw [h1, h2]
      rcases le_total 0 p.1 with hp1 | hp1 <;> rcases le_total 0 p.2 with hp2 | hp2
      · rw [abs_of_nonneg hp1, abs_of_nonneg hp2]
      · rw [abs_of_nonneg hp1, abs_of_nonpos hp2, (hΦseq (φ j)).d4_inv.2.1]
      · rw [abs_of_nonpos hp1, abs_of_nonneg hp2, (hΦseq (φ j)).d4_inv.1]
      · rw [abs_of_nonpos hp1, abs_of_nonpos hp2, (hΦseq (φ j)).d4_inv.1, (hΦseq (φ j)).d4_inv.2.1]
    rwa [heq] at hge
  have hpt : ∀ p : ℝ × ℝ, Tendsto (fun j => Φseq (φ j) p) atTop (𝓝 (Φs p)) := by
    intro p
    set m := Nat.ceil (dist p 0)
    have hp : p ∈ closedBall (0 : ℝ × ℝ) ((m : ℝ) + 1) := by
      rw [mem_closedBall]; linarith [Nat.le_ceil (dist p 0)]
    exact (hunif m).tendsto_at hp
  have hfi : ∀ j, Integrable (Φseq (φ j)) μ := fun j => by
    rw [hμ_int_iff]
    refine (hΦseq (φ j)).int_M2.mono'
      ((((hΦseq (φ j)).cont.mul ((by unfold spinV1; fun_prop : Continuous (spinV1 a)).comp continuous_fst)).mul
        ((by unfold spinV1; fun_prop : Continuous (spinV1 a)).comp continuous_snd))).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (spinV1_nonneg ha p.1),
        abs_of_nonneg (spinV1_nonneg ha p.2)]
  have hnorm_μ : ∀ j, ∫ p : ℝ × ℝ, |Φseq (φ j) p| ∂μ = 1 := fun j => by
    rw [hμ_int_eq]; exact hΦseq_M2 (φ j)
  have hint_μ : ∀ j, ∫ p : ℝ × ℝ, Φseq (φ j) p ∂μ ≤ 0 := fun j => by
    rw [hμ_int_eq]
    have := hΦseq_vac (φ j)
    unfold spinPhiVac at this; linarith
  obtain ⟨hΦs_int_μ, _, hΦs_int_le0, _, hΦs_eq_part⟩ :=
    Duality.compact_negative_mass (μ := μ) (f := fun j => Φseq (φ j)) (F := Φs) (K := K)
      (isCompact_closedBall 0 _) (fun j => (hΦseq (φ j)).cont.measurable)
      (fun j => (hΦseq (φ j)).cont.continuousOn) hfi hnorm_μ hint_μ hK_neg hpt (hunif mK)
  have hΦs_m2_int : Integrable (fun p : ℝ × ℝ => |Φs p| * spinV1 a p.1 * spinV1 a p.2) volume := by
    rw [← hμ_int_iff]; exact hΦs_int_μ.abs
  have hΦs : SpinTestClass a Φs := ⟨hΦs_cont, hΦs_int, hΦs_d4, hΦs_fodd, hΦs_m2_int⟩
  have hΦs_vac_nn : 0 ≤ spinPhiVac a Φs := by
    unfold spinPhiVac; rw [← hμ_int_eq]; linarith
  -- Step 6: Nonnegativity of `spinEvalT Φs` on `F ∪ spinConeSlice (spinConeB 0) TF`
  have hΦs_nn : ∀ p ∈ F ∪ spinConeSlice (spinConeB 0) TF, 0 ≤ spinEvalT Φs p := by
    rintro p (hpF | ⟨hpΩ, hpTF⟩)
    · exact ge_of_tendsto (hpt _) (Eventually.of_forall fun j => hΦseq_nn (φ j) p (Or.inl hpF))
    · have hgt_nn : ∀ q ∈ spinConeB 0, TF < q.1 + q.2 → 0 ≤ spinEvalT Φs q := by
        intro q hqΩ hqTF
        have hev : ∀ᶠ j in atTop, Tseq (φ j) ≤ q.1 + q.2 := by
          have ht : Tendsto (fun j : ℕ => TF + 1 / ((φ j : ℝ) + 1)) atTop (𝓝 TF) := by
            have hinv : Tendsto (fun j : ℕ => 1 / ((φ j : ℝ) + 1)) atTop (𝓝 0) :=
              tendsto_const_nhds.div_atTop
                ((tendsto_natCast_atTop_atTop.comp hφ_mono.tendsto_atTop).atTop_add tendsto_const_nhds)
            simpa using tendsto_const_nhds.add hinv
          filter_upwards [ht.eventually (gt_mem_nhds hqTF)] with j hj
          linarith [hTseq_lt (φ j)]
        exact ge_of_tendsto (hpt _) (hev.mono fun j hj => hΦseq_nn (φ j) q (Or.inr ⟨hqΩ, hj⟩))
      -- Approximate `p` by `p_n = (p.1 + 1/(n+1), p.2)` which has `p_n.1 + p_n.2 > TF`
      have hcont_eval : Continuous (spinEvalT Φs) := by
        unfold spinEvalT
        exact hΦs_cont.comp ((Real.continuous_sqrt.comp (continuous_const.mul continuous_fst)).prodMk
          (Real.continuous_sqrt.comp (continuous_const.mul continuous_snd)))
      have hp_tend : Tendsto (fun n : ℕ => (p.1 + 1 / ((n : ℝ) + 1), p.2)) atTop (𝓝 p) := by
        have h1 : Tendsto (fun n : ℕ => p.1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 p.1) := by
          have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
            tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          simpa using tendsto_const_nhds.add hinv
        exact h1.prodMk_nhds tendsto_const_nhds
      refine ge_of_tendsto ((hcont_eval.tendsto p).comp hp_tend) (Eventually.of_forall fun n => ?_)
      simp only [spinConeB, neg_zero, mem_ofPred_eq] at hpΩ
      change TF ≤ p.1 + p.2 at hpTF
      have hpos_n : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      refine hgt_nn (p.1 + 1 / ((n : ℝ) + 1), p.2)
        ⟨by change -0 ≤ p.1 + 1 / ((n : ℝ) + 1); linarith [hpΩ.1],
         by change -0 ≤ p.2; linarith [hpΩ.2]⟩
        (by dsimp only; linarith)
  -- Step 7: `spinDW` against `hmeas₀_TF` gives `spinPhiVac a Φs = 0` and `spinM2 a Φs = 1`,
  -- and against any `meas` on `F ∪ Ω(TF)` gives complementary slackness!
  have hΦs_nn_cone : ∀ p ∈ liouvilleCone TF, 0 ≤ spinEvalT Φs p := fun p hp =>
    hΦs_nn p (Or.inr (by rwa [spinConeSlice_quadrant]))
  have hsubQ_TF : F ∪ spinConeSlice (spinConeB 0) TF ⊆ spinConeB 0 :=
    union_subset (hFsub.trans inter_subset_left) inter_subset_left
  have hpair_any : ∀ meas : SpinCrossingMeasureOn a (F ∪ spinConeSlice (spinConeB 0) TF),
      Integrable (spinEvalT Φs) meas.ν ∧
      0 ≤ ∫ p, spinEvalT Φs p ∂meas.ν ∧
      ∫ p, spinEvalT Φs p ∂meas.ν ≤ -spinPhiVac a Φs := by
    intro meas
    have hW := spinDW ha (meas.toQuadrant hsubQ_TF) hΦs hTF_pos hΦs_nn_cone
    have hnn_int : 0 ≤ ∫ p, spinEvalT Φs p ∂meas.ν := by
      refine integral_nonneg_of_ae ?_
      have : ∀ᵐ p ∂meas.ν, p ∉ (F ∪ spinConeSlice (spinConeB 0) TF)ᶜ :=
        measure_eq_zero_iff_ae_notMem.1 meas.supp
      filter_upwards [this] with p hp using hΦs_nn p (not_not.mp hp)
    exact ⟨hW.1, hnn_int, hW.2.1⟩
  have hΦs_vac0 : spinPhiVac a Φs = 0 := by
    have ⟨_, h0, hle⟩ := hpair_any hmeas₀_TF
    linarith
  have hΦs_int_μ_ge0 : 0 ≤ ∫ p : ℝ × ℝ, Φs p ∂μ := by
    rw [hμ_int_eq]; unfold spinPhiVac at hΦs_vac0; linarith
  have hΦs_M2 : spinM2 a Φs = 1 := by
    have h1 := (hΦs_eq_part hΦs_int_μ_ge0).2.1
    rw [hμ_int_eq] at h1; exact h1
  refine ⟨Φs, hΦs, hΦs_M2, hΦs_vac0, hΦs_nn, fun meas => ?_⟩
  obtain ⟨hint, h0, hle⟩ := hpair_any meas
  have hint0 : ∫ p, spinEvalT Φs p ∂meas.ν = 0 := by linarith
  have hae_nn : 0 ≤ᵐ[meas.ν] spinEvalT Φs := by
    have : ∀ᵐ p ∂meas.ν, p ∉ (F ∪ spinConeSlice (spinConeB 0) TF)ᶜ :=
      measure_eq_zero_iff_ae_notMem.1 meas.supp
    filter_upwards [this] with p hp using hΦs_nn p (not_not.mp hp)
  exact (integral_eq_zero_iff_of_nonneg_ae hae_nn hint).mp hint0

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDA

end FormalResearch.ModularBootstrap.Spin
