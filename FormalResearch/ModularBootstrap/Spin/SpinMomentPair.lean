module

public import FormalResearch.ModularBootstrap.Spin.SpinMomentRad

/-!
# SPIN-M part 2b: Exact weight-5 pairing (`sd:spinmoment-pair`) via `fw:abel`(3)

* `spinMoment_pair`: for `a ≥ 2`, `B ≥ 0`, `τ > 0`, a crossing measure `meas : SpinCrossingMeasureOn a X`
  with `X ⊆ spinConeB B ∩ {p | τ ≤ p.1 + p.2}`, and any test `g ∈ Ā_5(a)` satisfying fixed-charge
  sub-Gaussian decay `|g(t)| ≤ C_g exp(-4π √(a t) - δ √t)` (`δ > 0`), proves integrability of all
  three pieces and the exact pairing identity
  `∫ g dM = ∫₀^∞ g(t) H_C(t) dt + ∫ (K* g) dν₀` (`ν₀ = spinRadMarginal meas.ν`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal Nat

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing

private lemma spinVacuumV_expand (a y : ℝ) :
    spinVacuumV a y y =
      Real.exp (2 * π * a * y) - 2 * Real.exp (2 * π * (a - 1) * y) + Real.exp (2 * π * (a - 2) * y) := by
  unfold spinVacuumV spinVacuumQ
  have h1 : Real.exp (π * a * y) * Real.exp (π * a * y) = Real.exp (2 * π * a * y) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (2 * π * a * y) * Real.exp (-2 * π * y) = Real.exp (2 * π * (a - 1) * y) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (2 * π * a * y) * (Real.exp (-2 * π * y) * Real.exp (-2 * π * y)) =
      Real.exp (2 * π * (a - 2) * y) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc Real.exp (π * a * y) * (1 - Real.exp (-2 * π * y)) *
        (Real.exp (π * a * y) * (1 - Real.exp (-2 * π * y)))
      = (Real.exp (π * a * y) * Real.exp (π * a * y)) *
          (1 - 2 * Real.exp (-2 * π * y) + Real.exp (-2 * π * y) * Real.exp (-2 * π * y)) := by ring
    _ = Real.exp (2 * π * a * y) -
          2 * (Real.exp (2 * π * a * y) * Real.exp (-2 * π * y)) +
          Real.exp (2 * π * a * y) * (Real.exp (-2 * π * y) * Real.exp (-2 * π * y)) := by
          rw [h1]; ring
    _ = _ := by rw [h2, h3]

private lemma spinVacuumV_hasDerivAt (a y : ℝ) :
    HasDerivAt (fun x => spinVacuumV a x x)
      (2 * π * (a * Real.exp (2 * π * a * y) - 2 * (a - 1) * Real.exp (2 * π * (a - 1) * y) +
        (a - 2) * Real.exp (2 * π * (a - 2) * y))) y := by
  have heq : (fun x => spinVacuumV a x x) = fun x =>
      Real.exp (2 * π * a * x) - 2 * Real.exp (2 * π * (a - 1) * x) + Real.exp (2 * π * (a - 2) * x) :=
    funext (spinVacuumV_expand a)
  rw [heq]
  have hlin : ∀ c : ℝ, HasDerivAt (fun x : ℝ => c * x) c y := fun c => by
    simpa using (hasDerivAt_id y).const_mul c
  have hd1 := (hlin (2 * π * a)).exp
  have hd2 := ((hlin (2 * π * (a - 1))).exp).const_mul 2
  have hd3 := (hlin (2 * π * (a - 2))).exp
  exact ((hd1.sub hd2).add hd3).congr_deriv (by ring)

lemma spinMomentF0_hasDerivAt_all {a B : ℝ} (hB : 0 ≤ B) {X : Set (ℝ × ℝ)}
    (hX : X ⊆ spinConeB B) (meas : SpinCrossingMeasureOn a X) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (spinMomentF0 a meas.ν)
      ((-2 * π * ∫ p : ℝ × ℝ, (p.1 + p.2) * Real.exp (-2 * π * y * (p.1 + p.2)) ∂meas.ν) +
        2 * π * (a * Real.exp (2 * π * a * y) - 2 * (a - 1) * Real.exp (2 * π * (a - 1) * y) +
          (a - 2) * Real.exp (2 * π * (a - 2) * y))) y := by
  have h1 : HasDerivAt (fun x => ∫ p : ℝ × ℝ, Real.exp (-2 * π * x * (p.1 + p.2)) ∂meas.ν)
      (-2 * π * ∫ p : ℝ × ℝ, (p.1 + p.2) * Real.exp (-2 * π * y * (p.1 + p.2)) ∂meas.ν) y := by
    have hae : ∀ᵐ p ∂meas.ν, p ∈ spinConeB B := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 meas.supp] with p hp
      by_contra hpB; exact hp (fun hpX => hpB (hX hpX))
    let β0 : ℝ := y / 2
    have hβ0 : 0 < β0 := half_pos hy
    let bound : ℝ × ℝ → ℝ := fun p =>
      2 * π * Real.exp (2 * π * y * (2 * B)) * (p.1 + p.2 + 2 * (2 * B)) *
        Real.exp (-2 * π * β0 * (p.1 + p.2))
    have hF_meas : ∀ᶠ x in 𝓝 y, AEStronglyMeasurable
        (fun p : ℝ × ℝ => Real.exp (-2 * π * x * (p.1 + p.2))) meas.ν :=
      Eventually.of_forall fun x => (by fun_prop : Continuous fun p : ℝ × ℝ => _).aestronglyMeasurable
    have hF'_meas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => -2 * π * (p.1 + p.2) * Real.exp (-2 * π * y * (p.1 + p.2))) meas.ν :=
      (by fun_prop : Continuous fun p : ℝ × ℝ => _).aestronglyMeasurable
    have hbound_int : Integrable bound meas.ν := by
      have hpow := spin_pow_add_exp_integrable (hX.trans (spinConeB_subset_add (by linarith : B ≤ 2 * B))) meas 1 hβ0
      exact (hpow.const_mul (2 * π * Real.exp (2 * π * y * (2 * B)))).congr
        (Eventually.of_forall fun p => by dsimp [bound]; rw [pow_one]; ring)
    have h_bound : ∀ᵐ p ∂meas.ν, ∀ x ∈ Metric.ball y (y / 2),
        ‖-2 * π * (p.1 + p.2) * Real.exp (-2 * π * x * (p.1 + p.2))‖ ≤ bound p := by
      filter_upwards [hae] with p hp x hx
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
      have hx_lo : β0 ≤ x := by dsimp [β0]; linarith
      have hsum : 0 ≤ p.1 + p.2 + 2 * (2 * B) := by linarith [hp.1, hp.2]
      have h1' : |p.1 + p.2| ≤ p.1 + p.2 + 2 * (2 * B) := by rw [abs_le]; constructor <;> linarith [hp.1, hp.2]
      have hexp : -2 * π * x * (p.1 + p.2) ≤ -2 * π * β0 * (p.1 + p.2) + 2 * π * y * (2 * B) := by
        have hp12 : β0 * (p.1 + p.2 + 2 * B) ≤ x * (p.1 + p.2 + 2 * B) :=
          mul_le_mul_of_nonneg_right hx_lo (by linarith [hp.1, hp.2])
        have hyB : (x - β0) * (2 * B) ≤ y * (2 * B) :=
          mul_le_mul_of_nonneg_right (by dsimp [β0]; linarith) (by positivity)
        have hx' : β0 * (p.1 + p.2) - x * (p.1 + p.2) ≤ y * (2 * B) := by linarith
        have := mul_le_mul_of_nonneg_left hx' (by positivity : 0 ≤ 2 * π); linarith
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        show |-2 * π| = 2 * π by rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num, abs_of_pos Real.pi_pos],
        abs_of_pos (Real.exp_pos _)]
      calc 2 * π * |p.1 + p.2| * Real.exp (-2 * π * x * (p.1 + p.2))
          ≤ 2 * π * (p.1 + p.2 + 2 * (2 * B)) *
              Real.exp (-2 * π * β0 * (p.1 + p.2) + 2 * π * y * (2 * B)) := by gcongr
        _ = bound p := by rw [Real.exp_add]; dsimp [bound]; ring
    have h_diff : ∀ᵐ p ∂meas.ν, ∀ x ∈ Metric.ball y (y / 2),
        HasDerivAt (fun x' : ℝ => Real.exp (-2 * π * x' * (p.1 + p.2)))
          (-2 * π * (p.1 + p.2) * Real.exp (-2 * π * x * (p.1 + p.2))) x :=
      Eventually.of_forall fun p x _ => by
        have hlin : HasDerivAt (fun x' : ℝ => -2 * π * x' * (p.1 + p.2)) (-2 * π * (p.1 + p.2)) x := by
          simpa [mul_assoc] using ((hasDerivAt_id x).const_mul (-2 * π)).mul_const (p.1 + p.2)
        exact hlin.exp.congr_deriv (by ring)
    have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds y (half_pos hy))
      hF_meas (meas.finite_laplace hy) hF'_meas h_bound hbound_int h_diff).2
    rw [show (fun p : ℝ × ℝ => -2 * π * (p.1 + p.2) * Real.exp (-2 * π * y * (p.1 + p.2))) =
        fun p => (-2 * π) * ((p.1 + p.2) * Real.exp (-2 * π * y * (p.1 + p.2))) by ext p; ring,
      integral_const_mul] at key
    exact key
  exact h1.add (spinVacuumV_hasDerivAt a y)

lemma spinOpA_F0_eq {a B : ℝ} (hB : 0 ≤ B) {X : Set (ℝ × ℝ)} (hX : X ⊆ spinConeB B)
    (meas : SpinCrossingMeasureOn a X) {y : ℝ} (hy : 0 < y) :
    spinOpA (spinMomentF0 a meas.ν) y =
      -((∫ p : ℝ × ℝ, Real.exp (-2 * π * y * (p.1 + p.2)) ∂meas.ν) + spinVacuumV a y y) / (2 * y ^ 2) -
        ((-2 * π * ∫ p : ℝ × ℝ, (p.1 + p.2) * Real.exp (-2 * π * y * (p.1 + p.2)) ∂meas.ν) +
          2 * π * (a * Real.exp (2 * π * a * y) - 2 * (a - 1) * Real.exp (2 * π * (a - 1) * y) +
            (a - 2) * Real.exp (2 * π * (a - 2) * y))) / y := by
  unfold spinOpA
  rw [(spinMomentF0_hasDerivAt_all hB hX meas hy).deriv]
  unfold spinMomentF0; rfl

lemma spinOpA_sub_S5 {a B : ℝ} (hB : 0 ≤ B) {X : Set (ℝ × ℝ)} (hX : X ⊆ spinConeB B)
    (meas : SpinCrossingMeasureOn a X) {b : ℝ} (hb : 0 < b) :
    2 * spinOpA (spinMomentF0 a meas.ν) b =
      spinOpA (spinMomentF0 a meas.ν) b - b ^ (-5 : ℝ) * spinOpA (spinMomentF0 a meas.ν) b⁻¹ := by
  have hF0_inv : ∀ {y : ℝ}, 0 < y → spinMomentF0 a meas.ν y = y⁻¹ * spinMomentF0 a meas.ν y⁻¹ := fun {y} hy => by
    have hc := meas.crossing hy hy
    have hx : (fun p : ℝ × ℝ => spinThermalX y y p.1 p.2) =
        fun p : ℝ × ℝ => Real.exp (-2 * π * y * (p.1 + p.2)) -
          y⁻¹ * Real.exp (-2 * π * y⁻¹ * (p.1 + p.2)) := by
      ext p; unfold spinThermalX
      have hpow : (y * y) ^ (-(1 / 2 : ℝ)) = y⁻¹ := by
        rw [← pow_two, ← Real.rpow_natCast y 2, ← Real.rpow_mul hy.le]; norm_num; exact Real.rpow_neg_one y
      rw [hpow]; congr 1 <;> [ring_nf; ring_nf]
    rw [hx, integral_sub (meas.finite_laplace hy) ((meas.finite_laplace (inv_pos.mpr hy)).const_mul _),
      integral_const_mul] at hc
    unfold spinThermalXVac at hc
    have hpow : (y * y) ^ (-(1 / 2 : ℝ)) = y⁻¹ := by
      rw [← pow_two, ← Real.rpow_natCast y 2, ← Real.rpow_mul hy.le]; norm_num; exact Real.rpow_neg_one y
    rw [hpow] at hc
    unfold spinMomentF0; linarith
  have hdb_inv := spinMomentF0_hasDerivAt_all hB hX meas (inv_pos.mpr hb)
  have hdb := spinMomentF0_hasDerivAt_all hB hX meas hb
  have hinv_b : HasDerivAt (fun x : ℝ => x⁻¹) (-b ^ (-2 : ℤ)) b :=
    (hasDerivAt_inv hb.ne').congr_deriv (by rw [zpow_neg]; norm_cast)
  have hmul := hinv_b.mul (hdb_inv.comp b hinv_b)
  have hev : (fun x : ℝ => x⁻¹ * spinMomentF0 a meas.ν x⁻¹) =ᶠ[𝓝 b] spinMomentF0 a meas.ν := by
    filter_upwards [eventually_gt_nhds hb] with y hy; exact (hF0_inv hy).symm
  have hdb_eq : deriv (spinMomentF0 a meas.ν) b =
      -b ^ (-2 : ℤ) * spinMomentF0 a meas.ν b⁻¹ -
        b ^ (-3 : ℤ) * deriv (spinMomentF0 a meas.ν) b⁻¹ := by
    rw [(hmul.congr_of_eventuallyEq hev.symm).deriv, hdb_inv.deriv]
    have hz2 : b ^ (-2 : ℤ) = 1 / b ^ 2 := by rw [zpow_neg, one_div]; norm_cast
    have hz3 : b ^ (-3 : ℤ) = 1 / b ^ 3 := by rw [zpow_neg, one_div]; norm_cast
    dsimp only [Function.comp_def]
    rw [hz2, hz3]; field_simp [hb.ne']; ring
  unfold spinOpA
  rw [hF0_inv hb, hdb_eq]
  have hb5 : b ^ (-5 : ℝ) = 1 / b ^ 5 := by rw [Real.rpow_neg hb.le, one_div]; norm_cast
  have hz2 : b ^ (-2 : ℤ) = 1 / b ^ 2 := by rw [zpow_neg, one_div]; norm_cast
  have hz3 : b ^ (-3 : ℤ) = 1 / b ^ 3 := by rw [zpow_neg, one_div]; norm_cast
  rw [hb5, hz2, hz3]; field_simp [hb.ne']; ring

private lemma measurable_ofReal_comp {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun t => ENNReal.ofReal (f t)) :=
  ENNReal.measurable_ofReal.comp hf

private lemma integrableOn_mul_withDensity {d wBd f : ℝ → ℝ}
    (hd_meas : Measurable d) (hd_nn : ∀ t, 0 ≤ d t)
    (hd_wbd : IntegrableOn (fun t => d t * wBd t) (Ici 0))
    (hf_meas : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    {C : ℝ} (_hC : 0 ≤ C) (hf_bd : ∀ t, 0 ≤ t → |f t| ≤ C * wBd t) :
    IntegrableOn f (Ici 0) (volume.withDensity (fun t => ENNReal.ofReal (d t))) := by
  rw [IntegrableOn, restrict_withDensity measurableSet_Ici,
    integrable_withDensity_iff_integrable_smul' (measurable_ofReal_comp hd_meas)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine (hd_wbd.const_mul C).mono'
    (((hd_meas.aestronglyMeasurable).mul hf_meas).congr
      (Eventually.of_forall fun t => by
        dsimp only [Pi.mul_apply]; rw [ENNReal.toReal_ofReal (hd_nn t), smul_eq_mul])) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  rw [ENNReal.toReal_ofReal (hd_nn t), smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd_nn t)]
  calc d t * |f t| ≤ d t * (C * wBd t) := mul_le_mul_of_nonneg_left (hf_bd t (mem_Ici.1 ht)) (hd_nn t)
    _ = C * (d t * wBd t) := by ring

private lemma integrableOn_mul_of_withDensity {d f : ℝ → ℝ}
    (hd_meas : Measurable d) (hd_nn : ∀ t, 0 ≤ d t)
    (hwd : IntegrableOn f (Ici 0) (volume.withDensity (fun t => ENNReal.ofReal (d t)))) :
    IntegrableOn (fun t => d t * f t) (Ici 0) := by
  rw [IntegrableOn, restrict_withDensity measurableSet_Ici,
    integrable_withDensity_iff_integrable_smul' (measurable_ofReal_comp hd_meas)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hwd
  exact IntegrableOn.congr_fun hwd
    (fun t _ => by rw [ENNReal.toReal_ofReal (hd_nn t), smul_eq_mul]) measurableSet_Ici

private lemma max_neg_sub_max (x : ℝ) : max (-x) 0 - max x 0 = -x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_right (neg_nonpos.2 h), max_eq_left h]; ring
  · rw [max_eq_left (neg_nonneg.2 h), max_eq_right h]; ring

/-- **Exact weight-5 pairing (`sd:spinmoment-pair`, `spinning_airy_moment_proof.tex`)**.
For `a ≥ 2`, a crossing measure `meas` on `E_B ∩ {t_L + t_R ≥ τ}` (`τ > 0, B ≥ 0`), and any test
`g ∈ Ā_5(a)` satisfying fixed-charge sub-Gaussian decay `|g(t)| ≤ C_g exp(-4π √(a t) - δ √t)`
(`δ > 0`), we have the exact identity
`∫ g dM = ∫₀^∞ g(t) H_C(t) dt + ∫ (K* g) dν₀` (`ν₀ = spinRadMarginal meas.ν`). -/
theorem spinMoment_pair {a B τ : ℝ} (ha : 2 ≤ a) (hB : 0 ≤ B) (hτ : 0 < τ)
    {X : Set (ℝ × ℝ)} (hX : X ⊆ spinConeB B ∩ {p | τ ≤ p.1 + p.2})
    (meas : SpinCrossingMeasureOn a X)
    {g : ℝ → ℝ} (hg : TestClass spinMomentW5Prob a g)
    {δ C_g : ℝ} (hδ : 0 < δ) (hC_g : 0 ≤ C_g)
    (hdec : ∀ t : ℝ, 0 ≤ t → |g t| ≤ C_g * Real.exp (-4 * π * Real.sqrt (a * t) - δ * Real.sqrt t)) :
    IntegrableOn g (Ici 0) (spinMomentMeasure meas.ν) ∧
    IntegrableOn (fun t => g t * spinVacHC a t) (Ici 0) ∧
    IntegrableOn (spinVolterraAdjoint g) (Ici 0) (spinRadMarginal meas.ν) ∧
    ∫ t in Ici 0, g t ∂(spinMomentMeasure meas.ν) =
      (∫ t in Ici 0, g t * spinVacHC a t) +
        ∫ r in Ici 0, spinVolterraAdjoint g r ∂(spinRadMarginal meas.ν) := by
  have hcone : X ⊆ spinConeB B := hX.trans inter_subset_left
  let ν₀ : Measure ℝ := spinRadMarginal meas.ν
  let M : Measure ℝ := spinMomentMeasure meas.ν
  have hν₀_supp : ν₀ (Iio 0) = 0 := (meas.toRadAdmissible (hX.trans fun _ hp => hτ.le.trans hp.2)).supp_nonneg
  have hM_supp : M (Iio 0) = 0 := measure_mono_null (Iio_subset_Iio hτ.le) (spinMomentMeasure_Iio_eq_zero hX meas)
  obtain ⟨C_N, hCN, hcount⟩ := rad_counting_bound ha hτ hX meas
  have hν₀_fin : ∀ R : ℝ, ν₀ (Icc 0 R) < ⊤ := rad_Icc_lt_top hτ hX meas
  have hν₀_mono : Monotone (fun t : ℝ => (ν₀ (Icc 0 t)).toReal) := fun t₁ t₂ hle =>
    ENNReal.toReal_mono (hν₀_fin t₂).ne (measure_mono (Icc_subset_Icc_right hle))
  have hM_fin : ∀ R : ℝ, M (Icc 0 R) < ⊤ := spinMomentMeasure_Icc_lt_top hX meas
  let d₀ : ℝ := -2 * Real.sqrt 2 * π * Real.sqrt a
  let wBd : ℝ → ℝ := cardyWeight (-6) d₀
  have hwBd_eq : ∀ t : ℝ, 0 ≤ t → wBd t = (1 + 2 * t) ^ (-6 : ℝ) * Real.exp (-4 * π * Real.sqrt (a * t)) :=
    fun t ht => cardyWeight_wbd_eq (by linarith) ht
  have hwBd_nn : ∀ t : ℝ, 0 ≤ t → 0 ≤ wBd t := cardyWeight_wbd_nonneg d₀
  have hwBd_meas : Measurable wBd := measurable_cardyWeight_wbd d₀
  have hwBd_aem : AEStronglyMeasurable wBd (volume.restrict (Ici 0)) := hwBd_meas.aestronglyMeasurable
  have hwBd_M : IntegrableOn wBd (Ici 0) M := integrable_cardyWeight_spinMomentMeasure ha hB hτ hX meas
  have hm_volt : Measurable (spinVolterraDens ν₀) := by
    have : SigmaFinite ν₀ := sigmaFinite_of_Iio_null_Icc_lt_top hν₀_supp hν₀_fin
    exact measurable_spinVolterraDens ν₀
  have hm_hc : Measurable (spinVacHC a) := (continuous_spinVacHC a).measurable
  have hvolt_wbd : IntegrableOn (fun t => |spinVolterraDens ν₀ t| * wBd t) (Ici 0) := by
    refine (integrableOn_one_add_rpow_neg_two.const_mul (2 * C_N)).mono'
      ((hm_volt.abs.mul hwBd_meas).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht0 : 0 ≤ t := mem_Ici.1 ht
    have hv1 : |spinVolterraDens ν₀ t| ≤ t * (ν₀ (Icc 0 t)).toReal := spinVolterraDens_abs_le hν₀_supp hν₀_fin ht0
    have hv2 : (ν₀ (Icc 0 t)).toReal ≤ C_N * (1 + Real.sqrt t) * Real.exp (4 * π * Real.sqrt (a * t)) := hcount t ht0
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hwBd_nn t ht0)), hwBd_eq t ht0]
    calc |spinVolterraDens ν₀ t| * ((1 + 2 * t) ^ (-6 : ℝ) * Real.exp (-4 * π * Real.sqrt (a * t)))
        ≤ (t * (C_N * (1 + Real.sqrt t) * Real.exp (4 * π * Real.sqrt (a * t)))) *
            ((1 + 2 * t) ^ (-6 : ℝ) * Real.exp (-4 * π * Real.sqrt (a * t))) := by
            gcongr; exact hv1.trans (mul_le_mul_of_nonneg_left hv2 ht0)
      _ = C_N * (t * (1 + Real.sqrt t) * (1 + 2 * t) ^ (-6 : ℝ)) *
            (Real.exp (4 * π * Real.sqrt (a * t)) * Real.exp (-4 * π * Real.sqrt (a * t))) := by ring
      _ ≤ C_N * (2 * (1 + t) ^ (-2 : ℝ)) * 1 := by
            rw [← Real.exp_add, show 4 * π * Real.sqrt (a * t) + -4 * π * Real.sqrt (a * t) = 0 by ring, Real.exp_zero]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (rpow_cardy_mul_le_neg_two ht0) hCN.le) zero_le_one
      _ = (2 * C_N) * (1 + t) ^ (-2 : ℝ) := by ring
  obtain ⟨C_K, hCK, hK_le⟩ := cardyV_le_sub_exp (w := 5) (by norm_num) (by linarith : 0 ≤ a)
  have hhc_wbd : IntegrableOn (fun t => |spinVacHC a t| * wBd t) (Ici 0) := by
    let C_H : ℝ := (2 * a + 4) * (2 * π * C_K)
    refine (integrableOn_one_add_rpow_neg_two.const_mul C_H).mono'
      ((hm_hc.abs.mul hwBd_meas).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht0 : 0 ≤ t := mem_Ici.1 ht
    have hbd1 : |spinVacHC a t| ≤ (2 * a + 4) * spinVacuumD 5 a t := spinVacHC_abs_le ha ht0
    have hbd2 : spinVacuumD 5 a t ≤ 2 * π * C_K * (1 + t) ^ 4 * Real.exp (4 * π * Real.sqrt (a * t)) := by
      unfold spinVacuumD
      calc 2 * π * kernelK 5 a t ≤ 2 * π * (C_K * (1 + t) ^ (5 - 1) * Real.exp (4 * π * Real.sqrt (a * t))) := by gcongr; exact hK_le t ht0
        _ = _ := by norm_num; ring
    have hpow_le : (1 + t) ^ 4 * (1 + 2 * t) ^ (-6 : ℝ) ≤ (1 + t) ^ (-2 : ℝ) := by
      rw [← Real.rpow_natCast (1 + t) 4]
      calc (1 + t) ^ (4 : ℝ) * (1 + 2 * t) ^ (-6 : ℝ)
          ≤ (1 + t) ^ (4 : ℝ) * (1 + t) ^ (-6 : ℝ) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num))
              (by positivity)
        _ = (1 + t) ^ (-2 : ℝ) := by rw [← Real.rpow_add (by positivity)]; norm_num
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hwBd_nn t ht0)), hwBd_eq t ht0]
    calc |spinVacHC a t| * ((1 + 2 * t) ^ (-6 : ℝ) * Real.exp (-4 * π * Real.sqrt (a * t)))
        ≤ ((2 * a + 4) * (2 * π * C_K * (1 + t) ^ 4 * Real.exp (4 * π * Real.sqrt (a * t)))) *
            ((1 + 2 * t) ^ (-6 : ℝ) * Real.exp (-4 * π * Real.sqrt (a * t))) := by
            gcongr; exact hbd1.trans (mul_le_mul_of_nonneg_left hbd2 (by linarith))
      _ = C_H * ((1 + t) ^ 4 * (1 + 2 * t) ^ (-6 : ℝ)) *
            (Real.exp (4 * π * Real.sqrt (a * t)) * Real.exp (-4 * π * Real.sqrt (a * t))) := by dsimp [C_H]; ring
      _ ≤ C_H * (1 + t) ^ (-2 : ℝ) * 1 := by
            rw [← Real.exp_add, show 4 * π * Real.sqrt (a * t) + -4 * π * Real.sqrt (a * t) = 0 by ring, Real.exp_zero]; gcongr
      _ = C_H * (1 + t) ^ (-2 : ℝ) := by ring
  let dL : ℝ → ℝ := fun t => if 0 ≤ t then max (-spinVolterraDens ν₀ t) 0 + max (-spinVacHC a t) 0 else 0
  let dR : ℝ → ℝ := fun t => if 0 ≤ t then max (spinVolterraDens ν₀ t) 0 + max (spinVacHC a t) 0 else 0
  have hdL_nn : ∀ t, 0 ≤ dL t := fun t => by dsimp [dL]; split_ifs <;> positivity
  have hdR_nn : ∀ t, 0 ≤ dR t := fun t => by dsimp [dR]; split_ifs <;> positivity
  have hdL_meas : Measurable dL :=
    Measurable.ite measurableSet_Ici ((hm_volt.neg.max measurable_const).add (hm_hc.neg.max measurable_const)) measurable_const
  have hdR_meas : Measurable dR :=
    Measurable.ite measurableSet_Ici ((hm_volt.max measurable_const).add (hm_hc.max measurable_const)) measurable_const
  let μL : Measure ℝ := M + volume.withDensity (fun t => ENNReal.ofReal (dL t))
  let μR : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (dR t))
  have hwd_fin : ∀ {f : ℝ → ℝ} (hf : Measurable f) (hf_wbd : IntegrableOn (fun t => f t * wBd t) (Ici 0))
      (hf_nn : ∀ t, 0 ≤ f t) (R : ℝ),
      (volume.withDensity (fun t => ENNReal.ofReal (f t))) (Icc 0 R) < ⊤ := by
    intro f hf hf_wbd hf_nn R
    by_cases hR : 0 ≤ R
    · have hw_pos : 0 < wBd R := by
        unfold wBd cardyWeight
        exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.exp_pos _)
      have hw_mono : ∀ t ∈ Icc 0 R, wBd R ≤ wBd t := fun t ht => by
        rw [hwBd_eq t ht.1, hwBd_eq R hR]
        have hexp_le : Real.exp (-4 * π * Real.sqrt (a * R)) ≤ Real.exp (-4 * π * Real.sqrt (a * t)) := by
          refine Real.exp_le_exp.mpr ?_
          have hsq : Real.sqrt (a * t) ≤ Real.sqrt (a * R) :=
            Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ht.2 (by linarith))
          nlinarith [Real.pi_pos]
        refine mul_le_mul (Real.rpow_le_rpow_of_nonpos (by linarith [ht.1]) (by linarith [ht.2]) (by norm_num))
          hexp_le (Real.exp_pos _).le (Real.rpow_nonneg (by linarith [ht.1]) _)
      rw [withDensity_apply _ measurableSet_Icc]
      have hle_w : ∫⁻ t in Icc 0 R, ENNReal.ofReal (f t) ∂volume ≤
          ENNReal.ofReal (wBd R)⁻¹ * ∫⁻ t in Ici 0, ‖f t * wBd t‖ₑ ∂volume := by
        calc ∫⁻ t in Icc 0 R, ENNReal.ofReal (f t) ∂volume
            ≤ ∫⁻ t in Icc 0 R, ENNReal.ofReal ((wBd R)⁻¹ * (f t * wBd t)) ∂volume := by
              refine setLIntegral_mono' measurableSet_Icc fun t ht => ENNReal.ofReal_le_ofReal ?_
              calc f t = ((wBd R)⁻¹ * wBd R) * f t := by rw [inv_mul_cancel₀ hw_pos.ne', one_mul]
                _ ≤ ((wBd R)⁻¹ * wBd t) * f t :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hw_mono t ht) (by positivity)) (hf_nn t)
                _ = (wBd R)⁻¹ * (f t * wBd t) := by ring
          _ = ENNReal.ofReal (wBd R)⁻¹ * ∫⁻ t in Icc 0 R, ENNReal.ofReal (f t * wBd t) ∂volume := by
              simp_rw [ENNReal.ofReal_mul (inv_pos.mpr hw_pos).le]
              exact lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (hf.mul hwBd_meas))
          _ ≤ ENNReal.ofReal (wBd R)⁻¹ * ∫⁻ t in Icc 0 R, ‖f t * wBd t‖ₑ ∂volume := by
              refine mul_le_mul_of_nonneg_left (setLIntegral_mono' measurableSet_Icc fun t ht => ?_) (by positivity)
              rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (hf_nn t) (hwBd_nn t ht.1))]
          _ ≤ ENNReal.ofReal (wBd R)⁻¹ * ∫⁻ t in Ici 0, ‖f t * wBd t‖ₑ ∂volume :=
              mul_le_mul_of_nonneg_left (lintegral_mono_set Icc_subset_Ici_self) (by positivity)
      exact hle_w.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf_wbd.2)
    · rw [Icc_eq_empty_of_lt (by linarith), measure_empty]; exact ENNReal.zero_lt_top
  have hdL_wbd : IntegrableOn (fun t => dL t * wBd t) (Ici 0) := by
    refine (hvolt_wbd.add hhc_wbd).mono' ((hdL_meas.mul hwBd_meas).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have hw0 := hwBd_nn t (mem_Ici.1 ht)
    rw [Real.norm_of_nonneg (mul_nonneg (hdL_nn t) hw0)]
    dsimp [dL]; simp only [mem_Ici.1 ht, ↓reduceIte]
    have h1 : max (-spinVolterraDens ν₀ t) 0 ≤ |spinVolterraDens ν₀ t| := max_le (neg_le_abs _) (abs_nonneg _)
    have h2 : max (-spinVacHC a t) 0 ≤ |spinVacHC a t| := max_le (neg_le_abs _) (abs_nonneg _)
    calc (max (-spinVolterraDens ν₀ t) 0 + max (-spinVacHC a t) 0) * wBd t
        ≤ (|spinVolterraDens ν₀ t| + |spinVacHC a t|) * wBd t := by gcongr
      _ = _ := by ring
  have hdR_wbd : IntegrableOn (fun t => dR t * wBd t) (Ici 0) := by
    refine (hvolt_wbd.add hhc_wbd).mono' ((hdR_meas.mul hwBd_meas).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have hw0 := hwBd_nn t (mem_Ici.1 ht)
    rw [Real.norm_of_nonneg (mul_nonneg (hdR_nn t) hw0)]
    dsimp [dR]; simp only [mem_Ici.1 ht, ↓reduceIte]
    have h1 : max (spinVolterraDens ν₀ t) 0 ≤ |spinVolterraDens ν₀ t| := max_le (le_abs_self _) (abs_nonneg _)
    have h2 : max (spinVacHC a t) 0 ≤ |spinVacHC a t| := max_le (le_abs_self _) (abs_nonneg _)
    calc (max (spinVolterraDens ν₀ t) 0 + max (spinVacHC a t) 0) * wBd t
        ≤ (|spinVolterraDens ν₀ t| + |spinVacHC a t|) * wBd t := by gcongr
      _ = _ := by ring
  have hμL_fin : ∀ R, μL (Icc 0 R) < ⊤ := fun R =>
    ENNReal.add_lt_top.2 ⟨hM_fin R, hwd_fin hdL_meas hdL_wbd hdL_nn R⟩
  have hμR_fin : ∀ R, μR (Icc 0 R) < ⊤ := fun R => hwd_fin hdR_meas hdR_wbd hdR_nn R
  have : IsLocallyFiniteMeasure (radialOfReal μL) := isLocallyFinite_radialOfReal hμL_fin
  have : IsLocallyFiniteMeasure (radialOfReal μR) := isLocallyFinite_radialOfReal hμR_fin
  have hwBd_L : IntegrableOn wBd (Ici 0) μL := by
    refine IntegrableOn.add_measure hwBd_M ?_
    rw [IntegrableOn, restrict_withDensity measurableSet_Ici,
      integrable_withDensity_iff_integrable_smul' (measurable_ofReal_comp hdL_meas)
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    exact hdL_wbd.congr_fun (fun t _ => by dsimp only; rw [ENNReal.toReal_ofReal (hdL_nn t), smul_eq_mul]) measurableSet_Ici
  have hwBd_R : IntegrableOn wBd (Ici 0) μR := by
    rw [IntegrableOn, restrict_withDensity measurableSet_Ici,
      integrable_withDensity_iff_integrable_smul' (measurable_ofReal_comp hdR_meas)
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    exact hdR_wbd.congr_fun (fun t _ => by dsimp only; rw [ENNReal.toReal_ofReal (hdR_nn t), smul_eq_mul]) measurableSet_Ici
  have hW_radL : Integrable (euclideanWeight (-6) d₀) (radialOfReal μL) := by
    rw [show euclideanWeight (-6) d₀ = radialLiftReal 5 wBd from funext fun x =>
      (euclideanWeight_eq_cardyWeight (-6) d₀ x), integrable_radialOfReal_iff hwBd_meas]
    exact hwBd_L
  have hW_radR : Integrable (euclideanWeight (-6) d₀) (radialOfReal μR) := by
    rw [show euclideanWeight (-6) d₀ = radialLiftReal 5 wBd from funext fun x =>
      (euclideanWeight_eq_cardyWeight (-6) d₀ x), integrable_radialOfReal_iff hwBd_meas]
    exact hwBd_R
  have hgauss_from_wbd : ∀ {μ : Measure ℝ}, IntegrableOn wBd (Ici 0) μ →
      ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace 5 => Real.exp (-ε * ‖x‖ ^ 2)) (radialOfReal μ) := by
    intro μ hμ_wbd ε hε
    obtain ⟨Cε, hCε, hexp_bd⟩ := exp_neg_mul_le_cardyWeight hε (by linarith : 0 ≤ a)
    have hcont : Continuous (fun t : ℝ => Real.exp (-2 * ε * t)) := by fun_prop
    rw [show (fun x : RadialSpace 5 => Real.exp (-ε * ‖x‖ ^ 2)) =
        radialLiftReal 5 (fun t => Real.exp (-2 * ε * t)) from funext fun x => by
      unfold radialLiftReal; congr 1; ring]
    rw [integrable_radialOfReal_iff hcont.measurable]
    refine (hμ_wbd.const_mul Cε).mono' (hcont.aestronglyMeasurable.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hexp_bd t (mem_Ici.1 ht)
  have hgaussL : ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace 5 => Real.exp (-ε * ‖x‖ ^ 2)) (radialOfReal μL) :=
    fun hε => hgauss_from_wbd hwBd_L hε
  have hgaussR : ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace 5 => Real.exp (-ε * ‖x‖ ^ 2)) (radialOfReal μR) :=
    fun hε => hgauss_from_wbd hwBd_R hε
  have h_thermal : ∀ {β : ℝ}, 0 < β →
      ∫ x : RadialSpace 5, radialLiftReal 5 (thermalDiff 5 β) x ∂(radialOfReal μL) =
        ∫ x : RadialSpace 5, radialLiftReal 5 (thermalDiff 5 β) x ∂(radialOfReal μR) := by
    intro β hβ
    have hcont_td : Continuous (thermalDiff 5 β) := by unfold thermalDiff; fun_prop
    rw [integral_radialOfReal hcont_td.measurable, integral_radialOfReal hcont_td.measurable]
    have htd_wbd : ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ t : ℝ, 0 ≤ t → |thermalDiff 5 β t| ≤ Ct * wBd t := by
      obtain ⟨C1, hC1, h1⟩ := exp_neg_mul_le_cardyWeight (by positivity : 0 < π * β) (by linarith : 0 ≤ a)
      obtain ⟨C2, hC2, h2⟩ := exp_neg_mul_le_cardyWeight (by positivity : 0 < π * β⁻¹) (by linarith : 0 ≤ a)
      refine ⟨C1 + β ^ (-5 : ℝ) * C2, by positivity, fun t ht => ?_⟩
      unfold thermalDiff
      calc |Real.exp (-2 * π * β * t) - β ^ (-(5 : ℕ) : ℝ) * Real.exp (-2 * π * t / β)|
          ≤ Real.exp (-2 * π * β * t) + β ^ (-5 : ℝ) * Real.exp (-2 * π * β⁻¹ * t) := by
            refine (abs_sub _ _).trans_eq ?_
            rw [abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos (Real.rpow_pos_of_pos hβ _),
              abs_of_pos (Real.exp_pos _), div_eq_mul_inv]; ring_nf
        _ ≤ C1 * wBd t + β ^ (-5 : ℝ) * (C2 * wBd t) := by
            gcongr
            · simpa [mul_assoc] using (h1 t ht).trans_eq (by ring)
            · simpa [mul_assoc] using (h2 t ht).trans_eq (by ring)
        _ = (C1 + β ^ (-5 : ℝ) * C2) * wBd t := by ring
    obtain ⟨Ct, hCt, htd_le⟩ := htd_wbd
    have htd_M : IntegrableOn (thermalDiff 5 β) (Ici 0) M :=
      (hwBd_M.const_mul Ct).mono' (hcont_td.continuousOn.aestronglyMeasurable measurableSet_Ici) (by
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        rw [Real.norm_eq_abs]; exact htd_le t (mem_Ici.1 ht))
    have htd_L_wd : IntegrableOn (thermalDiff 5 β) (Ici 0) (volume.withDensity (fun t => ENNReal.ofReal (dL t))) :=
      integrableOn_mul_withDensity hdL_meas hdL_nn hdL_wbd
        (hcont_td.continuousOn.aestronglyMeasurable measurableSet_Ici) hCt htd_le
    have htd_R_wd : IntegrableOn (thermalDiff 5 β) (Ici 0) μR :=
      integrableOn_mul_withDensity hdR_meas hdR_nn hdR_wbd
        (hcont_td.continuousOn.aestronglyMeasurable measurableSet_Ici) hCt htd_le
    have hM_td : ∫ t in Ici 0, thermalDiff 5 β t ∂M =
        (2 * π) ^ (-2 : ℝ) * (spinMomentY a meas.ν β - β ^ (-5 : ℝ) * spinMomentY a meas.ν β⁻¹) +
          2 * (Real.exp (2 * π * (a - 1) * β) - β ^ (-5 : ℝ) * Real.exp (2 * π * (a - 1) / β)) := by
      have hM_lap : ∀ {y : ℝ}, 0 < y → ∫ t in Ici 0, Real.exp (-2 * π * y * t) ∂M =
          (2 * π) ^ (-2 : ℝ) * spinMomentY a meas.ν y + 2 * Real.exp (2 * π * (a - 1) * y) := fun {y} hy => by
        have hres : M.restrict (Ici 0) = M := by
          refine Measure.restrict_eq_self_of_ae_mem ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 hM_supp] with t ht using not_lt.1 ht
        rw [hres, integral_spinMomentMeasure (by fun_prop : Measurable fun t : ℝ => Real.exp (-2 * π * y * t))]
        unfold spinMomentY; rw [show (2 * π) ^ (-2 : ℝ) = ((2 * π) ^ 2)⁻¹ by rw [Real.rpow_neg (by positivity)]; norm_cast]
        field_simp [Real.pi_ne_zero]; ring
      have heq_td : (fun t => thermalDiff 5 β t) = fun t =>
          Real.exp (-2 * π * β * t) - β ^ (-5 : ℝ) * Real.exp (-2 * π * β⁻¹ * t) := by
        ext t; unfold thermalDiff
        rw [div_eq_mul_inv, show (-(5 : ℕ) : ℝ) = (-5 : ℝ) by norm_num]; ring_nf
      have hi1 : IntegrableOn (fun t => Real.exp (-2 * π * β * t)) (Ici 0) M :=
        (spinMomentMeasure_finite_laplace hcone meas hβ).integrableOn
      have hi2 : IntegrableOn (fun t => β ^ (-5 : ℝ) * Real.exp (-2 * π * β⁻¹ * t)) (Ici 0) M :=
        ((spinMomentMeasure_finite_laplace hcone meas (inv_pos.mpr hβ)).const_mul (β ^ (-5 : ℝ))).integrableOn
      rw [show ∫ t in Ici 0, thermalDiff 5 β t ∂M =
          ∫ t in Ici 0, (Real.exp (-2 * π * β * t) - β ^ (-5 : ℝ) * Real.exp (-2 * π * β⁻¹ * t)) ∂M from
          setIntegral_congr_fun measurableSet_Ici fun t _ => congrFun heq_td t,
        integral_sub hi1 hi2, integral_const_mul, hM_lap hβ, hM_lap (inv_pos.mpr hβ), div_eq_mul_inv]
      ring
    have hfub_exp : ∀ {y : ℝ}, 0 < y →
        IntegrableOn (fun t => spinVolterraDens ν₀ t * Real.exp (-2 * π * y * t)) (Ici 0) ∧
        ∫ t in Ici 0, spinVolterraDens ν₀ t * Real.exp (-2 * π * y * t) =
          ∫ r in Ici 0, Real.exp (-2 * π * y * r) * (r / (2 * π * y) - 1 / (2 * (2 * π * y) ^ 2)) ∂ν₀ := by
      intro y hy
      obtain ⟨Cy, hCy, hy_bd⟩ := exp_neg_mul_le_cardyWeight (by positivity : 0 < π * y) (by linarith : 0 ≤ a)
      have h_in_int : IntegrableOn (fun t : ℝ => t * |Real.exp (-2 * π * y * t)| * (ν₀ (Icc 0 t)).toReal) (Ici 0) := by
        refine (integrableOn_one_add_rpow_neg_two.const_mul (2 * C_N * Cy)).mono'
          (((by fun_prop : Continuous fun t : ℝ => t * |Real.exp (-2 * π * y * t)|).measurable.mul
            hν₀_mono.measurable).aestronglyMeasurable) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        have ht0 : 0 ≤ t := mem_Ici.1 ht
        have he_bd : Real.exp (-2 * π * y * t) ≤ Cy * wBd t := by
          simpa [wBd, mul_assoc] using (hy_bd t ht0).trans_eq (by ring)
        rw [Real.norm_of_nonneg (by positivity), abs_of_pos (Real.exp_pos _)]
        calc t * Real.exp (-2 * π * y * t) * (ν₀ (Icc 0 t)).toReal
            ≤ t * (Cy * wBd t) * (C_N * (1 + Real.sqrt t) * Real.exp (4 * π * Real.sqrt (a * t))) :=
              mul_le_mul (mul_le_mul_of_nonneg_left he_bd ht0)
                (by simpa [ν₀] using hcount t ht0) ENNReal.toReal_nonneg
                (mul_nonneg ht0 (mul_nonneg hCy.le (hwBd_nn t ht0)))
          _ = C_N * Cy * (t * (1 + Real.sqrt t) * (1 + 2 * t) ^ (-6 : ℝ)) *
                (Real.exp (-4 * π * Real.sqrt (a * t)) * Real.exp (4 * π * Real.sqrt (a * t))) := by
              rw [hwBd_eq t ht0]; ring
          _ ≤ C_N * Cy * (2 * (1 + t) ^ (-2 : ℝ)) * 1 := by
              rw [← Real.exp_add, show -4 * π * Real.sqrt (a * t) + 4 * π * Real.sqrt (a * t) = 0 by ring, Real.exp_zero]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (rpow_cardy_mul_le_neg_two ht0) (mul_nonneg hCN.le hCy.le)) zero_le_one
          _ = 2 * C_N * Cy * (1 + t) ^ (-2 : ℝ) := by ring
      obtain ⟨hL, _, hswap⟩ := spinMoment_fubini_on_Ici hν₀_supp hν₀_fin
        (by fun_prop : Measurable fun t : ℝ => Real.exp (-2 * π * y * t)) h_in_int
      refine ⟨hL, ?_⟩
      rw [hswap]
      refine setIntegral_congr_fun measurableSet_Ici fun r _ => (spinVolterra_exp_integral r hy).2
    have hK_td : ∫ t in Ici 0, spinVolterraDens ν₀ t * thermalDiff 5 β t =
        (∫ r in Ici 0, Real.exp (-2 * π * β * r) * (r / (2 * π * β) - 1 / (2 * (2 * π * β) ^ 2)) ∂ν₀) -
          β ^ (-5 : ℝ) * ∫ r in Ici 0, Real.exp (-2 * π * β⁻¹ * r) *
            (r / (2 * π * β⁻¹) - 1 / (2 * (2 * π * β⁻¹) ^ 2)) ∂ν₀ := by
      have heq : (fun t => spinVolterraDens ν₀ t * thermalDiff 5 β t) = fun t =>
          spinVolterraDens ν₀ t * Real.exp (-2 * π * β * t) -
            β ^ (-5 : ℝ) * (spinVolterraDens ν₀ t * Real.exp (-2 * π * β⁻¹ * t)) := by
        ext t; unfold thermalDiff
        rw [div_eq_mul_inv, show (-(5 : ℕ) : ℝ) = (-5 : ℝ) by norm_num]; ring_nf
      have h1 := hfub_exp hβ
      have h2 := hfub_exp (inv_pos.mpr hβ)
      rw [show ∫ t in Ici 0, spinVolterraDens ν₀ t * thermalDiff 5 β t =
          ∫ t in Ici 0, (spinVolterraDens ν₀ t * Real.exp (-2 * π * β * t) -
            β ^ (-5 : ℝ) * (spinVolterraDens ν₀ t * Real.exp (-2 * π * β⁻¹ * t))) from
          setIntegral_congr_fun measurableSet_Ici fun t _ => congrFun heq t,
        integral_sub h1.1 (h2.1.const_mul _), integral_const_mul, h1.2, h2.2]
    have hHC_td : ∫ t in Ici 0, spinVacHC a t * thermalDiff 5 β t =
        (∫ t in Ioi 0, spinVacHC a t * Real.exp (-2 * π * β * t)) -
          β ^ (-5 : ℝ) * ∫ t in Ioi 0, spinVacHC a t * Real.exp (-2 * π * β⁻¹ * t) := by
      have heq : (fun t => spinVacHC a t * thermalDiff 5 β t) = fun t =>
          spinVacHC a t * Real.exp (-2 * π * β * t) -
            β ^ (-5 : ℝ) * (spinVacHC a t * Real.exp (-2 * π * β⁻¹ * t)) := by
        ext t; unfold thermalDiff
        rw [div_eq_mul_inv, show (-(5 : ℕ) : ℝ) = (-5 : ℝ) by norm_num]; ring_nf
      have h1 := IntegrableOn.congr_set_ae (spinVacHC_laplace (a := a) hβ).1 Ioi_ae_eq_Ici.symm
      have h2 := IntegrableOn.congr_set_ae
        ((spinVacHC_laplace (a := a) (inv_pos.mpr hβ)).1.const_mul (β ^ (-5 : ℝ))) Ioi_ae_eq_Ici.symm
      rw [show ∫ t in Ici 0, spinVacHC a t * thermalDiff 5 β t =
          ∫ t in Ici 0, (spinVacHC a t * Real.exp (-2 * π * β * t) -
            β ^ (-5 : ℝ) * (spinVacHC a t * Real.exp (-2 * π * β⁻¹ * t))) from
          setIntegral_congr_fun measurableSet_Ici fun t _ => congrFun heq t,
        integral_sub h1 h2, integral_const_mul, integral_Ici_eq_integral_Ioi, integral_Ici_eq_integral_Ioi]
    have h_diff_eq : (∫ t in Ici 0, thermalDiff 5 β t ∂M) -
        (∫ t in Ici 0, spinVolterraDens ν₀ t * thermalDiff 5 β t) -
        (∫ t in Ici 0, spinVacHC a t * thermalDiff 5 β t) = 0 := by
      have h_sd := sd_eSD3 hB hcone meas hβ
      have h_s5 := spinOpA_sub_S5 hB hcone meas hβ
      have hA_b := spinOpA_F0_eq hB hcone meas hβ
      have hA_binv := spinOpA_F0_eq hB hcone meas (inv_pos.mpr hβ)
      have hrad_e0 : ∀ {y : ℝ}, 0 < y →
          ∫ p : ℝ × ℝ, Real.exp (-2 * π * y * (p.1 + p.2)) ∂meas.ν =
            ∫ r in Ici 0, Real.exp (-2 * π * y * r) ∂ν₀ := fun {y} _ => by
        have hr : ν₀.restrict (Ici 0) = ν₀ := by
          refine Measure.restrict_eq_self_of_ae_mem ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 hν₀_supp] with r hr using not_lt.1 hr
        rw [hr]; unfold ν₀ spinRadMarginal
        rw [integral_map (by fun_prop : Measurable fun p : ℝ × ℝ => p.1 + p.2).aemeasurable
          (by fun_prop : Continuous fun r : ℝ => Real.exp (-2 * π * y * r)).aestronglyMeasurable]
      have hrad_e1 : ∀ {y : ℝ}, 0 < y →
          ∫ p : ℝ × ℝ, (p.1 + p.2) * Real.exp (-2 * π * y * (p.1 + p.2)) ∂meas.ν =
            ∫ r in Ici 0, r * Real.exp (-2 * π * y * r) ∂ν₀ := fun {y} _ => by
        have hr : ν₀.restrict (Ici 0) = ν₀ := by
          refine Measure.restrict_eq_self_of_ae_mem ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 hν₀_supp] with r hr using not_lt.1 hr
        rw [hr]; unfold ν₀ spinRadMarginal
        rw [integral_map (by fun_prop : Measurable fun p : ℝ × ℝ => p.1 + p.2).aemeasurable
          (by fun_prop : Continuous fun r : ℝ => r * Real.exp (-2 * π * y * r)).aestronglyMeasurable]
      have hK_split : ∀ {y : ℝ}, 0 < y →
          ∫ r in Ici 0, Real.exp (-2 * π * y * r) * (r / (2 * π * y) - 1 / (2 * (2 * π * y) ^ 2)) ∂ν₀ =
            (1 / (2 * π * y)) * (∫ r in Ici 0, r * Real.exp (-2 * π * y * r) ∂ν₀) -
              (1 / (2 * (2 * π * y) ^ 2)) * (∫ r in Ici 0, Real.exp (-2 * π * y * r) ∂ν₀) := fun {y} hy => by
        let hrad := meas.toRadAdmissible (hX.trans fun _ hp => hτ.le.trans hp.2)
        have i0 : IntegrableOn (fun r : ℝ => Real.exp (-2 * π * y * r)) (Ici 0) ν₀ := hrad.finite_laplace hy
        have i1 : IntegrableOn (fun r : ℝ => r * Real.exp (-2 * π * y * r)) (Ici 0) ν₀ := by
          have hr : ν₀.restrict (Ici 0) = ν₀ := by
            refine Measure.restrict_eq_self_of_ae_mem ?_
            filter_upwards [measure_eq_zero_iff_ae_notMem.1 hν₀_supp] with r hr using not_lt.1 hr
          rw [IntegrableOn, hr]; unfold ν₀ spinRadMarginal
          rw [integrable_map_measure (by fun_prop : Continuous fun r : ℝ => r * Real.exp (-2 * π * y * r)).aestronglyMeasurable
            (by fun_prop : Measurable fun p : ℝ × ℝ => p.1 + p.2).aemeasurable]
          exact spin_sum_exp_integrable hB hcone meas hy
        have heq : (fun r : ℝ => Real.exp (-2 * π * y * r) * (r / (2 * π * y) - 1 / (2 * (2 * π * y) ^ 2))) =
            fun r => (1 / (2 * π * y)) * (r * Real.exp (-2 * π * y * r)) -
              (1 / (2 * (2 * π * y) ^ 2)) * Real.exp (-2 * π * y * r) := by ext r; ring
        rw [show ∫ r in Ici 0, Real.exp (-2 * π * y * r) * (r / (2 * π * y) - 1 / (2 * (2 * π * y) ^ 2)) ∂ν₀ =
            ∫ r in Ici 0, ((1 / (2 * π * y)) * (r * Real.exp (-2 * π * y * r)) -
              (1 / (2 * (2 * π * y) ^ 2)) * Real.exp (-2 * π * y * r)) ∂ν₀ from
            setIntegral_congr_fun measurableSet_Ici fun r _ => congrFun heq r,
          integral_sub (i1.const_mul _) (i0.const_mul _), integral_const_mul, integral_const_mul]
      rw [hM_td, hK_td, hHC_td, h_sd, h_s5, hA_b, hA_binv, hrad_e0 hβ, hrad_e1 hβ,
        hrad_e0 (inv_pos.mpr hβ), hrad_e1 (inv_pos.mpr hβ),
        hK_split hβ, hK_split (inv_pos.mpr hβ),
        (spinVacHC_laplace (a := a) hβ).2, (spinVacHC_laplace (a := a) (inv_pos.mpr hβ)).2,
        spinVacuumV_expand a β, spinVacuumV_expand a β⁻¹]
      have h2p : (2 * π) ^ (-2 : ℝ) = 1 / (2 * π) ^ 2 := by
        rw [Real.rpow_neg (by positivity), one_div]; norm_cast
      have hb3 : β ^ (-3 : ℝ) = 1 / β ^ 3 := by rw [Real.rpow_neg hβ.le, one_div]; norm_cast
      have hb4 : β ^ (-4 : ℝ) = 1 / β ^ 4 := by rw [Real.rpow_neg hβ.le, one_div]; norm_cast
      have hb5 : β ^ (-5 : ℝ) = 1 / β ^ 5 := by rw [Real.rpow_neg hβ.le, one_div]; norm_cast
      have hbi3 : (β⁻¹) ^ (-3 : ℝ) = β ^ 3 := by rw [Real.inv_rpow hβ.le, Real.rpow_neg hβ.le, inv_inv]; norm_cast
      have hbi4 : (β⁻¹) ^ (-4 : ℝ) = β ^ 4 := by rw [Real.inv_rpow hβ.le, Real.rpow_neg hβ.le, inv_inv]; norm_cast
      have hbi5 : (β⁻¹) ^ (-5 : ℝ) = β ^ 5 := by rw [Real.inv_rpow hβ.le, Real.rpow_neg hβ.le, inv_inv]; norm_cast
      rw [h2p, hb3, hb4, hb5, hbi3, hbi4, hbi5, div_eq_mul_inv]
      field_simp [hβ.ne', Real.pi_ne_zero]
      ring
    have hL_split : ∫ t in Ici 0, thermalDiff 5 β t ∂μL =
        (∫ t in Ici 0, thermalDiff 5 β t ∂M) +
          ∫ t in Ici 0, dL t * thermalDiff 5 β t := by
      rw [show μL = M + volume.withDensity (fun t => ENNReal.ofReal (dL t)) from rfl,
        Measure.restrict_add, integral_add_measure htd_M htd_L_wd,
        restrict_withDensity measurableSet_Ici,
        integral_withDensity_eq_integral_toReal_smul (measurable_ofReal_comp hdL_meas)
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      congr 1; refine setIntegral_congr_fun measurableSet_Ici fun t _ => by
        rw [ENNReal.toReal_ofReal (hdL_nn t), smul_eq_mul]
    have hR_split : ∫ t in Ici 0, thermalDiff 5 β t ∂μR =
        ∫ t in Ici 0, dR t * thermalDiff 5 β t := by
      rw [restrict_withDensity measurableSet_Ici,
        integral_withDensity_eq_integral_toReal_smul (measurable_ofReal_comp hdR_meas)
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      refine setIntegral_congr_fun measurableSet_Ici fun t _ => by
        rw [ENNReal.toReal_ofReal (hdR_nn t), smul_eq_mul]
    have hK_eq_sub : (∫ t in Ici 0, dL t * thermalDiff 5 β t) - ∫ t in Ici 0, dR t * thermalDiff 5 β t =
        -(∫ t in Ici 0, spinVolterraDens ν₀ t * thermalDiff 5 β t) -
          ∫ t in Ici 0, spinVacHC a t * thermalDiff 5 β t := by
      have h1 : IntegrableOn (fun t => spinVolterraDens ν₀ t * thermalDiff 5 β t) (Ici 0) :=
        (hvolt_wbd.const_mul Ct).mono' (hm_volt.mul hcont_td.measurable).aestronglyMeasurable (by
          filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
          rw [Real.norm_eq_abs, abs_mul]
          calc |spinVolterraDens ν₀ t| * |thermalDiff 5 β t|
              ≤ |spinVolterraDens ν₀ t| * (Ct * wBd t) := mul_le_mul_of_nonneg_left (htd_le t (mem_Ici.1 ht)) (abs_nonneg _)
            _ = _ := by ring)
      have h2 : IntegrableOn (fun t => spinVacHC a t * thermalDiff 5 β t) (Ici 0) :=
        (hhc_wbd.const_mul Ct).mono' (hm_hc.mul hcont_td.measurable).aestronglyMeasurable (by
          filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
          rw [Real.norm_eq_abs, abs_mul]
          calc |spinVacHC a t| * |thermalDiff 5 β t|
              ≤ |spinVacHC a t| * (Ct * wBd t) := mul_le_mul_of_nonneg_left (htd_le t (mem_Ici.1 ht)) (abs_nonneg _)
            _ = _ := by ring)
      have hl1 := integrableOn_mul_of_withDensity hdL_meas hdL_nn htd_L_wd
      have hr1 := integrableOn_mul_of_withDensity hdR_meas hdR_nn htd_R_wd
      rw [← integral_sub hl1 hr1, show ∫ t in Ici 0, (dL t * thermalDiff 5 β t - dR t * thermalDiff 5 β t) =
          ∫ t in Ici 0, -(spinVolterraDens ν₀ t * thermalDiff 5 β t + spinVacHC a t * thermalDiff 5 β t) from
          setIntegral_congr_fun measurableSet_Ici fun t ht => by
            have ht0 : 0 ≤ t := mem_Ici.1 ht
            dsimp [dL, dR]; simp only [ht0, ↓reduceIte]
            calc (max (-spinVolterraDens ν₀ t) 0 + max (-spinVacHC a t) 0) * thermalDiff 5 β t -
                  (max (spinVolterraDens ν₀ t) 0 + max (spinVacHC a t) 0) * thermalDiff 5 β t
                = ((max (-spinVolterraDens ν₀ t) 0 - max (spinVolterraDens ν₀ t) 0) +
                    (max (-spinVacHC a t) 0 - max (spinVacHC a t) 0)) * thermalDiff 5 β t := by ring
              _ = (-spinVolterraDens ν₀ t + -spinVacHC a t) * thermalDiff 5 β t := by
                    rw [max_neg_sub_max, max_neg_sub_max]
              _ = _ := by ring,
        integral_neg, integral_add h1 h2]
      ring
    rw [hL_split, hR_split]; linarith
  -- Apply fw:abel(3) to g
  obtain ⟨C_δ, hC_δ, hδ_bd⟩ := rpow_neg_six_le_exp_neg_sqrt hδ
  let C_w : ℝ := C_g * C_δ
  have hCw_nn : 0 ≤ C_w := by positivity
  have hg_wbd : ∀ t : ℝ, 0 ≤ t → |g t| ≤ C_w * wBd t := fun t ht => by
    calc |g t| ≤ C_g * Real.exp (-4 * π * Real.sqrt (a * t) - δ * Real.sqrt t) := hdec t ht
      _ = C_g * (Real.exp (-δ * Real.sqrt t) * Real.exp (-4 * π * Real.sqrt (a * t))) := by
          rw [← Real.exp_add]; congr 2; ring
      _ ≤ C_g * ((C_δ * (1 + 2 * t) ^ (-6 : ℝ)) * Real.exp (-4 * π * Real.sqrt (a * t))) := by
          gcongr; exact hδ_bd t ht
      _ = C_w * wBd t := by rw [hwBd_eq t ht]; dsimp [C_w]; ring
  have hg_euc : ∀ x : RadialSpace 5, |radialLiftReal 5 g x| ≤ C_w * euclideanWeight (-6) d₀ x := fun x => by
    rw [euclideanWeight_eq_cardyWeight (-6) d₀ x]
    exact hg_wbd (‖x‖ ^ 2 / 2) (by positivity)
  have hpair := lemma_fwA_part3_unconditional (radialOfReal μL) (radialOfReal μR)
    hgaussL hgaussR h_thermal hg.cont hg.int_lift hg.fourier_odd hCw_nn hg_euc hW_radL hW_radR
  have hg_ae : AEStronglyMeasurable g (M.restrict (Ici 0)) :=
    hg.cont.aestronglyMeasurable measurableSet_Ici
  have hg_M : IntegrableOn g (Ici 0) M := by
    refine (hwBd_M.const_mul C_w).mono' hg_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [Real.norm_eq_abs]; exact hg_wbd t (mem_Ici.1 ht)
  have hg_hc : IntegrableOn (fun t => g t * spinVacHC a t) (Ici 0) := by
    refine (hhc_wbd.const_mul C_w).mono'
      ((hg.cont.mul (continuous_spinVacHC a).continuousOn).aestronglyMeasurable measurableSet_Ici) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [Real.norm_eq_abs, abs_mul]
    calc |g t| * |spinVacHC a t| ≤ (C_w * wBd t) * |spinVacHC a t| :=
          mul_le_mul_of_nonneg_right (hg_wbd t (mem_Ici.1 ht)) (abs_nonneg _)
      _ = _ := by ring
  have hg_fub_int : IntegrableOn (fun t : ℝ => t * |g t| * (ν₀ (Icc 0 t)).toReal) (Ici 0) := by
    refine (integrableOn_one_add_rpow_neg_two.const_mul (2 * C_N * C_w)).mono'
      (((continuousOn_id.aestronglyMeasurable measurableSet_Ici).mul
        (hg.cont.abs.aestronglyMeasurable measurableSet_Ici)).mul hν₀_mono.measurable.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht0 : 0 ≤ t := mem_Ici.1 ht
    rw [Real.norm_of_nonneg (by positivity)]
    calc t * |g t| * (ν₀ (Icc 0 t)).toReal
        ≤ t * (C_w * wBd t) * (C_N * (1 + Real.sqrt t) * Real.exp (4 * π * Real.sqrt (a * t))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hg_wbd t ht0) ht0)
            (by simpa [ν₀] using hcount t ht0) ENNReal.toReal_nonneg
            (mul_nonneg ht0 (mul_nonneg hCw_nn (hwBd_nn t ht0)))
      _ = C_N * C_w * (t * (1 + Real.sqrt t) * (1 + 2 * t) ^ (-6 : ℝ)) *
            (Real.exp (-4 * π * Real.sqrt (a * t)) * Real.exp (4 * π * Real.sqrt (a * t))) := by
          rw [hwBd_eq t ht0]; ring
      _ ≤ C_N * C_w * (2 * (1 + t) ^ (-2 : ℝ)) * 1 := by
          rw [← Real.exp_add, show -4 * π * Real.sqrt (a * t) + 4 * π * Real.sqrt (a * t) = 0 by ring, Real.exp_zero]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (rpow_cardy_mul_le_neg_two ht0) (mul_nonneg hCN.le hCw_nn)) zero_le_one
      _ = 2 * C_N * C_w * (1 + t) ^ (-2 : ℝ) := by ring
  let g₀ : ℝ → ℝ := fun t => g (max t 0)
  have hg₀_cont : Continuous g₀ :=
    hg.cont.comp_continuous (continuous_id.max continuous_const) fun t => le_max_right t 0
  have hg₀_eq : ∀ t : ℝ, 0 ≤ t → g₀ t = g t := fun t ht => by dsimp [g₀]; rw [max_eq_left ht]
  have hg_fub_int₀ : IntegrableOn (fun t : ℝ => t * |g₀ t| * (ν₀ (Icc 0 t)).toReal) (Ici 0) :=
    hg_fub_int.congr_fun (fun t ht => by dsimp only; rw [hg₀_eq t (mem_Ici.1 ht)]) measurableSet_Ici
  obtain ⟨hg_K_int₀, hg_Ks_int₀, hg_fub_eq₀⟩ := spinMoment_fubini_on_Ici hν₀_supp hν₀_fin
    hg₀_cont.measurable hg_fub_int₀
  have hg_Ks_eq : ∀ r ∈ Ici (0 : ℝ), spinVolterraAdjoint g r = ∫ t in Ici r, (3 * r - t) / 2 * g₀ t := by
    intro r hr
    refine setIntegral_congr_fun measurableSet_Ici fun t ht => ?_
    rw [hg₀_eq t ((mem_Ici.1 hr).trans (mem_Ici.1 ht))]
  have hg_Ks_int : IntegrableOn (spinVolterraAdjoint g) (Ici 0) ν₀ :=
    hg_Ks_int₀.congr_fun (fun r hr => (hg_Ks_eq r hr).symm) measurableSet_Ici
  have hg_K_int : IntegrableOn (fun t => spinVolterraDens ν₀ t * g t) (Ici 0) :=
    hg_K_int₀.congr_fun (fun t ht => by dsimp only; rw [hg₀_eq t (mem_Ici.1 ht)]) measurableSet_Ici
  have hg_L_wd : IntegrableOn g (Ici 0) (volume.withDensity (fun t => ENNReal.ofReal (dL t))) :=
    integrableOn_mul_withDensity hdL_meas hdL_nn hdL_wbd (hg.cont.aestronglyMeasurable measurableSet_Ici)
      hCw_nn hg_wbd
  have hg_R_wd : IntegrableOn g (Ici 0) μR :=
    integrableOn_mul_withDensity hdR_meas hdR_nn hdR_wbd (hg.cont.aestronglyMeasurable measurableSet_Ici)
      hCw_nn hg_wbd
  have hg_pair_eq : ∫ t in Ici 0, g t ∂μL = ∫ t in Ici 0, g t ∂μR := by
    have heq : radialLiftReal 5 g = radialLiftReal 5 g₀ := funext fun x => by
      unfold radialLiftReal; exact (hg₀_eq (‖x‖ ^ 2 / 2) (by positivity)).symm
    have hpeq := hpair.2.2
    rw [heq, integral_radialOfReal hg₀_cont.measurable, integral_radialOfReal hg₀_cont.measurable] at hpeq
    calc ∫ t in Ici 0, g t ∂μL = ∫ t in Ici 0, g₀ t ∂μL :=
          setIntegral_congr_fun measurableSet_Ici fun t ht => (hg₀_eq t (mem_Ici.1 ht)).symm
      _ = ∫ t in Ici 0, g₀ t ∂μR := hpeq
      _ = ∫ t in Ici 0, g t ∂μR :=
          setIntegral_congr_fun measurableSet_Ici fun t ht => hg₀_eq t (mem_Ici.1 ht)
  have hL_split : ∫ t in Ici 0, g t ∂μL =
      (∫ t in Ici 0, g t ∂M) + ∫ t in Ici 0, dL t * g t := by
    have hL' : ∫ t in Ici 0, g₀ t ∂μL =
        (∫ t in Ici 0, g₀ t ∂M) + ∫ t in Ici 0, dL t * g₀ t := by
      have hg0_M : IntegrableOn g₀ (Ici 0) M := hg_M.congr_fun (fun t ht => (hg₀_eq t (mem_Ici.1 ht)).symm) measurableSet_Ici
      have hg0_wd : IntegrableOn g₀ (Ici 0) (volume.withDensity (fun t => ENNReal.ofReal (dL t))) :=
        hg_L_wd.congr_fun (fun t ht => (hg₀_eq t (mem_Ici.1 ht)).symm) measurableSet_Ici
      rw [show μL = M + volume.withDensity (fun t => ENNReal.ofReal (dL t)) from rfl,
        Measure.restrict_add, integral_add_measure hg0_M hg0_wd,
        restrict_withDensity measurableSet_Ici,
        integral_withDensity_eq_integral_toReal_smul (measurable_ofReal_comp hdL_meas)
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      congr 1; refine setIntegral_congr_fun measurableSet_Ici fun t _ => by
        rw [ENNReal.toReal_ofReal (hdL_nn t), smul_eq_mul]
    rw [setIntegral_congr_fun measurableSet_Ici fun t ht => (hg₀_eq t (mem_Ici.1 ht)).symm, hL']
    congr 1
    · exact setIntegral_congr_fun measurableSet_Ici fun t ht => hg₀_eq t (mem_Ici.1 ht)
    · exact setIntegral_congr_fun measurableSet_Ici fun t ht => by rw [hg₀_eq t (mem_Ici.1 ht)]
  have hR_split : ∫ t in Ici 0, g t ∂μR = ∫ t in Ici 0, dR t * g t := by
    have hR' : ∫ t in Ici 0, g₀ t ∂μR = ∫ t in Ici 0, dR t * g₀ t := by
      rw [restrict_withDensity measurableSet_Ici,
        integral_withDensity_eq_integral_toReal_smul (measurable_ofReal_comp hdR_meas)
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      refine setIntegral_congr_fun measurableSet_Ici fun t _ => by
        rw [ENNReal.toReal_ofReal (hdR_nn t), smul_eq_mul]
    rw [setIntegral_congr_fun measurableSet_Ici fun t ht => (hg₀_eq t (mem_Ici.1 ht)).symm, hR']
    exact setIntegral_congr_fun measurableSet_Ici fun t ht => by rw [hg₀_eq t (mem_Ici.1 ht)]
  have hg_dL_int := integrableOn_mul_of_withDensity hdL_meas hdL_nn hg_L_wd
  have hg_dR_int := integrableOn_mul_of_withDensity hdR_meas hdR_nn hg_R_wd
  have hg_sub_eq : (∫ t in Ici 0, dL t * g t) - ∫ t in Ici 0, dR t * g t =
      -(∫ t in Ici 0, spinVolterraDens ν₀ t * g t) - ∫ t in Ici 0, g t * spinVacHC a t := by
    rw [← integral_sub hg_dL_int hg_dR_int,
      show ∫ t in Ici 0, (dL t * g t - dR t * g t) =
          ∫ t in Ici 0, -(spinVolterraDens ν₀ t * g t + g t * spinVacHC a t) from
        setIntegral_congr_fun measurableSet_Ici fun t ht => by
          have ht0 : 0 ≤ t := mem_Ici.1 ht
          dsimp [dL, dR]; simp only [ht0, ↓reduceIte]
          calc (max (-spinVolterraDens ν₀ t) 0 + max (-spinVacHC a t) 0) * g t -
                (max (spinVolterraDens ν₀ t) 0 + max (spinVacHC a t) 0) * g t
              = ((max (-spinVolterraDens ν₀ t) 0 - max (spinVolterraDens ν₀ t) 0) +
                  (max (-spinVacHC a t) 0 - max (spinVacHC a t) 0)) * g t := by ring
            _ = (-spinVolterraDens ν₀ t + -spinVacHC a t) * g t := by
                  rw [max_neg_sub_max, max_neg_sub_max]
            _ = _ := by ring,
      integral_neg, integral_add hg_K_int hg_hc]
    ring
  have hg_K_fub : ∫ t in Ici 0, spinVolterraDens ν₀ t * g t =
      ∫ r in Ici 0, spinVolterraAdjoint g r ∂ν₀ := by
    calc ∫ t in Ici 0, spinVolterraDens ν₀ t * g t
        = ∫ t in Ici 0, spinVolterraDens ν₀ t * g₀ t :=
          setIntegral_congr_fun measurableSet_Ici fun t ht => by rw [hg₀_eq t (mem_Ici.1 ht)]
      _ = ∫ r in Ici 0, (∫ t in Ici r, (3 * r - t) / 2 * g₀ t) ∂ν₀ := hg_fub_eq₀
      _ = ∫ r in Ici 0, spinVolterraAdjoint g r ∂ν₀ :=
          setIntegral_congr_fun measurableSet_Ici fun r hr => (hg_Ks_eq r hr).symm
  refine ⟨hg_M, hg_hc, hg_Ks_int, ?_⟩
  linarith

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinMoment_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinMoment_pair

end FormalResearch.ModularBootstrap.Spin
