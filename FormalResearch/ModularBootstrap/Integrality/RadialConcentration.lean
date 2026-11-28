module

public import FormalResearch.ModularBootstrap.Integrality.FourierConcentration
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Radial Fourier Concentration Bound on `ℝ^{2w}` (`int:sonine`)

Lifts `fourier_concentration_1d` from `ℝ` to `EuclideanSpace ℝ (Fin (m + 1))` by a single
coordinate split (`Fin.succAbove 0`) and `m`-dimensional $L^2$ Plancherel
(`integral_norm_sq_fourierIntegral`), then specialises to `m + 1 = 2 * w` (`1 ≤ w`) on the ball
`closedBall 0 √(2 B)`:
`∫ ξ in closedBall 0 √(2 B), ‖𝓕 F ξ‖ ^ 2 ≤ (1 - ε_B) * ∫ x, ‖F x‖ ^ 2`, where
`ε_B = min (1 / 2) (1 / (1024 * π ^ 2 * B ^ 2 * exp (16 * π * B)))`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set
open scoped FourierTransform ComplexInnerProductSpace ENNReal

namespace FormalResearch.ModularBootstrap.Integrality

/-- Volume-preserving measurable equivalence splitting off coordinate `0` of
`EuclideanSpace ℝ (Fin (m + 1))`. -/
noncomputable def euclideanSpaceSuccEquiv (m : ℕ) :
    EuclideanSpace ℝ (Fin (m + 1)) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin m) :=
  (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin m → ℝ))))

lemma measurePreserving_euclideanSpaceSuccEquiv (m : ℕ) :
    MeasurePreserving (euclideanSpaceSuccEquiv m) volume volume := by
  unfold euclideanSpaceSuccEquiv
  exact ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin m))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).comp
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (m + 1))))

lemma euclideanSpaceSuccEquiv_symm_inner (m : ℕ) (x₀ ξ₀ : ℝ)
    (x' ξ' : EuclideanSpace ℝ (Fin m)) :
    inner ℝ ((euclideanSpaceSuccEquiv m).symm (x₀, x'))
        ((euclideanSpaceSuccEquiv m).symm (ξ₀, ξ')) =
      x₀ * ξ₀ + inner ℝ x' ξ' := by
  have h0 : ∀ a (b : EuclideanSpace ℝ (Fin m)), ((euclideanSpaceSuccEquiv m).symm (a, b)) 0 = a :=
    fun _ _ => rfl
  have hsucc : ∀ a (b : EuclideanSpace ℝ (Fin m)) (i : Fin m),
      ((euclideanSpaceSuccEquiv m).symm (a, b)) i.succ = b i := fun _ _ _ => rfl
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succ]
  simp [h0, hsucc, mul_comm]

lemma euclideanSpaceSuccEquiv_abs_fst_le_norm (m : ℕ)
    (ξ : EuclideanSpace ℝ (Fin (m + 1))) :
    |(euclideanSpaceSuccEquiv m ξ).1| ≤ ‖ξ‖ := by
  have h0 : (euclideanSpaceSuccEquiv m ξ).1 = ξ 0 := rfl
  rw [h0]
  exact PiLp.norm_apply_le ξ 0

lemma abs_fst_le_norm_euclideanSpaceSuccEquiv_symm (m : ℕ) (x₀ : ℝ)
    (x' : EuclideanSpace ℝ (Fin m)) :
    |x₀| ≤ ‖(euclideanSpaceSuccEquiv m).symm (x₀, x')‖ := by
  have h := euclideanSpaceSuccEquiv_abs_fst_le_norm m ((euclideanSpaceSuccEquiv m).symm (x₀, x'))
  simpa using h

/-- Fourier concentration on `EuclideanSpace ℝ (Fin (m + 1))` for functions supported in
`closedBall 0 R`. -/
theorem fourier_concentration_euclidean {m : ℕ} {R : ℝ} (hR : 0 < R)
    {F : EuclideanSpace ℝ (Fin (m + 1)) → ℂ}
    (hF_meas : AEStronglyMeasurable F volume) (hF_mem : MemLp F 2 volume)
    (hF_supp : ∀ x : EuclideanSpace ℝ (Fin (m + 1)), R < ‖x‖ → F x = 0) :
    ∫ ξ in Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) R, ‖𝓕 F ξ‖ ^ 2 ≤
      (1 - min (1 / 2 : ℝ) (1 / (256 * π ^ 2 * R ^ 4 * Real.exp (8 * π * R ^ 2)))) *
        ∫ x : EuclideanSpace ℝ (Fin (m + 1)), ‖F x‖ ^ 2 := by
  let e := euclideanSpaceSuccEquiv m
  have hmp : MeasurePreserving e volume volume := measurePreserving_euclideanSpaceSuccEquiv m
  have hmp_symm : MeasurePreserving e.symm volume volume := hmp.symm
  have hF_int : Integrable F volume := by
    have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) R)) :=
      isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
    have hIon : IntegrableOn F (Metric.closedBall 0 R) volume :=
      (hF_mem.restrict _).integrable (by norm_num)
    have heq : F = (Metric.closedBall 0 R).indicator F := by
      ext x
      by_cases hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) R
      · simp [hx]
      · have hlt : R < ‖x‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
        simp [hx, hF_supp x hlt]
    rw [heq, integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    exact hIon
  let Fs : ℝ × EuclideanSpace ℝ (Fin m) → ℂ := fun p => F (e.symm p)
  have hFs_int : Integrable Fs (volume.prod volume) :=
    (hmp_symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hF_int
  have hFs_mem : MemLp Fs 2 (volume.prod volume) :=
    hF_mem.comp_measurePreserving hmp_symm
  have hFs_meas : AEStronglyMeasurable Fs (volume.prod volume) := hFs_int.aestronglyMeasurable
  let G : ℝ → EuclideanSpace ℝ (Fin m) → ℂ := fun x₀ ξ' =>
    𝓕 (fun x' => Fs (x₀, x')) ξ'
  have hFs_prod_int : ∀ᵐ x₀ : ℝ ∂volume, Integrable (fun x' => Fs (x₀, x')) volume :=
    hFs_int.prod_right_ae
  have hFs_prod_mem : ∀ᵐ x₀ : ℝ ∂volume, MemLp (fun x' => Fs (x₀, x')) 2 volume := by
    have hsq : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin m) => ‖Fs p‖ ^ 2) (volume.prod volume) :=
      hFs_mem.norm.integrable_sq
    filter_upwards [hsq.prod_right_ae, hFs_prod_int] with x₀ hx₀ hx₀_int
    exact (memLp_two_iff_integrable_sq_norm hx₀_int.aestronglyMeasurable).mpr hx₀
  have hF_split : ∀ (ξ₀ : ℝ) (ξ' : EuclideanSpace ℝ (Fin m)),
      𝓕 F (e.symm (ξ₀, ξ')) = 𝓕 (fun x₀ => G x₀ ξ') ξ₀ := by
    intro ξ₀ ξ'
    rw [Real.fourier_eq', Real.fourier_eq']
    have hpre : ∫ v : EuclideanSpace ℝ (Fin (m + 1)),
        Complex.exp (↑(-2 * π * inner ℝ v (e.symm (ξ₀, ξ'))) * Complex.I) • F v =
        ∫ p : ℝ × EuclideanSpace ℝ (Fin m),
          Complex.exp (↑(-2 * π * (p.1 * ξ₀ + inner ℝ p.2 ξ')) * Complex.I) • Fs p := by
      have heq_int : ∫ p : ℝ × EuclideanSpace ℝ (Fin m),
          Complex.exp (↑(-2 * π * inner ℝ (e.symm p) (e.symm (ξ₀, ξ'))) * Complex.I) • F (e.symm p) =
          ∫ v : EuclideanSpace ℝ (Fin (m + 1)),
            Complex.exp (↑(-2 * π * inner ℝ v (e.symm (ξ₀, ξ'))) * Complex.I) • F v :=
        hmp_symm.integral_comp e.symm.measurableEmbedding
          (fun v => Complex.exp (↑(-2 * π * inner ℝ v (e.symm (ξ₀, ξ'))) * Complex.I) • F v)
      rw [← heq_int]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      have h_in : inner ℝ (e.symm p) (e.symm (ξ₀, ξ')) = p.1 * ξ₀ + inner ℝ p.2 ξ' :=
        euclideanSpaceSuccEquiv_symm_inner m p.1 ξ₀ p.2 ξ'
      dsimp only
      rw [h_in]
    rw [hpre]
    have hint_p : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
        Complex.exp (↑(-2 * π * (p.1 * ξ₀ + inner ℝ p.2 ξ')) * Complex.I) • Fs p) (volume.prod volume) := by
      refine hFs_int.norm.mono' ?_ ?_
      · simp only [smul_eq_mul]
        have hc : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
            Complex.exp (↑(-2 * π * (p.1 * ξ₀ + inner ℝ p.2 ξ')) * Complex.I)) := by fun_prop
        exact hc.aestronglyMeasurable.mul hFs_meas
      · refine Eventually.of_forall fun p => ?_
        rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [Measure.volume_eq_prod, integral_prod _ hint_p]
    refine integral_congr_ae (Eventually.of_forall fun x₀ => ?_)
    dsimp [G]
    rw [Real.fourier_eq']
    simp only [conj_trivial, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x' => ?_)
    dsimp only
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  let Fs₀ : ℝ × EuclideanSpace ℝ (Fin m) → ℂ := hFs_meas.mk Fs
  have hFs₀_meas : Measurable Fs₀ := hFs_meas.stronglyMeasurable_mk.measurable
  have hFs₀_ae : Fs =ᵐ[volume.prod volume] Fs₀ := hFs_meas.ae_eq_mk
  let G₀ : ℝ → EuclideanSpace ℝ (Fin m) → ℂ := fun x₀ ξ' =>
    ∫ x' : EuclideanSpace ℝ (Fin m),
      Complex.exp (↑(-2 * π * inner ℝ x' ξ') * Complex.I) • Fs₀ (x₀, x')
  have hG₀_joint_meas : StronglyMeasurable (fun q : ℝ × EuclideanSpace ℝ (Fin m) => G₀ q.1 q.2) := by
    refine StronglyMeasurable.integral_prod_right'
      (f := fun qp : (ℝ × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin m) =>
        Complex.exp (↑(-2 * π * inner ℝ qp.2 qp.1.2) * Complex.I) • Fs₀ (qp.1.1, qp.2)) ?_
    have hcont_e : Measurable (fun qp : (ℝ × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin m) =>
        Complex.exp (↑(-2 * π * inner ℝ qp.2 qp.1.2) * Complex.I)) := by
      have hc : Continuous (fun qp : (ℝ × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin m) =>
          Complex.exp (↑(-2 * π * inner ℝ qp.2 qp.1.2) * Complex.I)) := by fun_prop
      exact hc.measurable
    have hF_m : Measurable (fun qp : (ℝ × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin m) =>
        Fs₀ (qp.1.1, qp.2)) :=
      hFs₀_meas.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    exact (hcont_e.smul hF_m).stronglyMeasurable
  have hG_eq_ae_x0 : ∀ᵐ x₀ : ℝ ∂volume, ∀ ξ' : EuclideanSpace ℝ (Fin m), G x₀ ξ' = G₀ x₀ ξ' := by
    have hae_slices := Measure.ae_ae_of_ae_prod hFs₀_ae
    filter_upwards [hae_slices] with x₀ hx₀ ξ'
    dsimp [G, G₀]
    rw [Real.fourier_eq']
    refine integral_congr_ae ?_
    filter_upwards [hx₀] with x' hx'
    simp only [smul_eq_mul, hx']
  have hG_joint_meas : AEStronglyMeasurable (fun q : ℝ × EuclideanSpace ℝ (Fin m) => G q.1 q.2)
      (volume.prod volume) := by
    refine hG₀_joint_meas.aestronglyMeasurable.congr ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hG_eq_ae_x0] with q hq
    exact (hq q.2).symm
  have hFs_planch_x0 : ∀ᵐ x₀ : ℝ ∂volume,
      ∫ ξ' : EuclideanSpace ℝ (Fin m), ‖G x₀ ξ'‖ ^ 2 = ∫ x' : EuclideanSpace ℝ (Fin m), ‖Fs (x₀, x')‖ ^ 2 := by
    filter_upwards [hFs_prod_int, hFs_prod_mem] with x₀ h1 h2
    exact integral_norm_sq_fourierIntegral h1 h2
  have hG_mem_x0 : ∀ᵐ x₀ : ℝ ∂volume, Integrable (fun ξ' => ‖G x₀ ξ'‖ ^ 2) volume := by
    filter_upwards [hFs_prod_int, hFs_prod_mem] with x₀ h1 h2
    exact (fourierIntegral_memLp_two h1 h2).norm.integrable_sq
  have hFs_sq_int : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin m) => ‖Fs p‖ ^ 2) (volume.prod volume) :=
    hFs_mem.norm.integrable_sq
  have hG_sq_meas : AEStronglyMeasurable (fun q : ℝ × EuclideanSpace ℝ (Fin m) => ‖G q.1 q.2‖ ^ 2)
      (volume.prod volume) := by
    have hp : AEStronglyMeasurable ((fun q : ℝ × EuclideanSpace ℝ (Fin m) => ‖G q.1 q.2‖) ^ 2)
        (volume.prod volume) := hG_joint_meas.norm.pow 2
    exact hp
  have hG_sq_prod_int : Integrable (fun q : ℝ × EuclideanSpace ℝ (Fin m) => ‖G q.1 q.2‖ ^ 2)
      (volume.prod volume) := by
    rw [integrable_prod_iff hG_sq_meas]
    refine ⟨hG_mem_x0, ?_⟩
    have h_int_x0 : Integrable (fun x₀ => ∫ x', ‖Fs (x₀, x')‖ ^ 2) volume :=
      hFs_sq_int.integral_prod_left
    refine h_int_x0.congr ?_
    filter_upwards [hFs_planch_x0] with x₀ hx₀
    rw [← hx₀]
    refine integral_congr_ae (Eventually.of_forall fun ξ' => ?_)
    dsimp only
    rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hG_total : ∫ q : ℝ × EuclideanSpace ℝ (Fin m), ‖G q.1 q.2‖ ^ 2 =
      ∫ x : EuclideanSpace ℝ (Fin (m + 1)), ‖F x‖ ^ 2 := by
    rw [Measure.volume_eq_prod, integral_prod _ hG_sq_prod_int]
    have h1 : ∫ x₀ : ℝ, ∫ ξ' : EuclideanSpace ℝ (Fin m), ‖G x₀ ξ'‖ ^ 2 =
        ∫ x₀ : ℝ, ∫ x' : EuclideanSpace ℝ (Fin m), ‖Fs (x₀, x')‖ ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hFs_planch_x0] with x₀ hx₀
      exact hx₀
    rw [h1, ← integral_prod _ hFs_sq_int]
    exact hmp_symm.integral_comp e.symm.measurableEmbedding (fun x => ‖F x‖ ^ 2)
  have hG_slice_meas : ∀ ξ' : EuclideanSpace ℝ (Fin m),
      AEStronglyMeasurable (fun x₀ => G x₀ ξ') volume := fun ξ' => by
    have hsm : StronglyMeasurable (fun x₀ : ℝ => (fun q : ℝ × EuclideanSpace ℝ (Fin m) => G₀ q.1 q.2) (x₀, ξ')) :=
      hG₀_joint_meas.comp_measurable (measurable_id.prodMk measurable_const)
    refine hsm.aestronglyMeasurable.congr ?_
    filter_upwards [hG_eq_ae_x0] with x₀ hx₀
    exact (hx₀ ξ').symm
  have hG_symm : Integrable (fun p : EuclideanSpace ℝ (Fin m) × ℝ => ‖G p.2 p.1‖ ^ 2)
      (volume.prod volume) :=
    (Measure.measurePreserving_swap (μ := volume) (ν := volume)).integrable_comp_emb
      (MeasurableEquiv.prodComm (α := EuclideanSpace ℝ (Fin m)) (β := ℝ)).measurableEmbedding |>.mpr
      hG_sq_prod_int
  have hG_slice_int_ae : ∀ᵐ ξ' : EuclideanSpace ℝ (Fin m) ∂volume,
      Integrable (fun x₀ => ‖G x₀ ξ'‖ ^ 2) volume :=
    hG_symm.prod_right_ae
  have hG_slice_mem : ∀ᵐ ξ' : EuclideanSpace ℝ (Fin m) ∂volume,
      MemLp (fun x₀ => G x₀ ξ') 2 volume := by
    filter_upwards [hG_slice_int_ae] with ξ' hξ'
    exact (memLp_two_iff_integrable_sq_norm (hG_slice_meas ξ')).mpr hξ'
  have hG_slice_supp : ∀ ξ' : EuclideanSpace ℝ (Fin m), ∀ x₀ : ℝ, R < |x₀| → G x₀ ξ' = 0 := by
    intro ξ' x₀ hx₀
    have hzero : ∀ x' : EuclideanSpace ℝ (Fin m), Fs (x₀, x') = 0 := fun x' =>
      hF_supp _ (hx₀.trans_le (abs_fst_le_norm_euclideanSpaceSuccEquiv_symm m x₀ x'))
    dsimp [G]
    rw [Real.fourier_eq']
    simp [hzero]
  set ε_R : ℝ := min (1 / 2 : ℝ) (1 / (256 * π ^ 2 * R ^ 4 * Real.exp (8 * π * R ^ 2)))
  have h_1d_ae : ∀ᵐ ξ' : EuclideanSpace ℝ (Fin m) ∂volume,
      ∫ ξ₀ in Icc (-R) R, ‖𝓕 F (e.symm (ξ₀, ξ'))‖ ^ 2 ≤
        (1 - ε_R) * ∫ x₀ : ℝ, ‖G x₀ ξ'‖ ^ 2 := by
    filter_upwards [hG_slice_mem] with ξ' hmem
    have h1d := fourier_concentration_1d hR (hG_slice_meas ξ') hmem (hG_slice_supp ξ')
    simpa only [← hF_split] using h1d
  have hF_hat_mem : MemLp (𝓕 F) 2 volume := fourierIntegral_memLp_two hF_int hF_mem
  have hF_hat_sq_int : Integrable (fun ξ : EuclideanSpace ℝ (Fin (m + 1)) => ‖𝓕 F ξ‖ ^ 2) volume :=
    hF_hat_mem.norm.integrable_sq
  have hF_hat_prod_int : Integrable (fun p : EuclideanSpace ℝ (Fin m) × ℝ =>
      ‖𝓕 F (e.symm (p.2, p.1))‖ ^ 2) (volume.prod volume) := by
    have h1 : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin m) => ‖𝓕 F (e.symm p)‖ ^ 2)
        (volume.prod volume) :=
      (hmp_symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hF_hat_sq_int
    exact (Measure.measurePreserving_swap (μ := volume) (ν := volume)).integrable_comp_emb
      (MeasurableEquiv.prodComm (α := EuclideanSpace ℝ (Fin m)) (β := ℝ)).measurableEmbedding |>.mpr h1
  have h_ball_sub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) R ⊆
      e ⁻¹' (Icc (-R) R ×ˢ (univ : Set (EuclideanSpace ℝ (Fin m)))) := by
    intro ξ hξ
    have hnorm : ‖ξ‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hξ
    exact ⟨abs_le.mp ((euclideanSpaceSuccEquiv_abs_fst_le_norm m ξ).trans hnorm), mem_univ _⟩
  have h_ball_le : ∫ ξ in Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) R, ‖𝓕 F ξ‖ ^ 2 ≤
      ∫ ξ' : EuclideanSpace ℝ (Fin m), ∫ ξ₀ in Icc (-R) R, ‖𝓕 F (e.symm (ξ₀, ξ'))‖ ^ 2 := by
    have h1 : ∫ ξ in Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) R, ‖𝓕 F ξ‖ ^ 2 ≤
        ∫ ξ in e ⁻¹' (Icc (-R) R ×ˢ (univ : Set (EuclideanSpace ℝ (Fin m)))), ‖𝓕 F ξ‖ ^ 2 :=
      setIntegral_mono_set hF_hat_sq_int.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall fun _ hξ => h_ball_sub hξ)
    have h2 : ∫ ξ in e ⁻¹' (Icc (-R) R ×ˢ (univ : Set (EuclideanSpace ℝ (Fin m)))), ‖𝓕 F ξ‖ ^ 2 =
        ∫ p in Icc (-R) R ×ˢ (univ : Set (EuclideanSpace ℝ (Fin m))), ‖𝓕 F (e.symm p)‖ ^ 2 := by
      have h_eq := hmp_symm.setIntegral_preimage_emb e.symm.measurableEmbedding
        (fun ξ => ‖𝓕 F ξ‖ ^ 2) (e ⁻¹' (Icc (-R) R ×ˢ univ))
      have hpre : e.symm ⁻¹' (e ⁻¹' (Icc (-R) R ×ˢ univ)) = Icc (-R) R ×ˢ univ := by
        ext p; simp
      simpa [hpre] using h_eq.symm
    have h3 : ∫ p in Icc (-R) R ×ˢ (univ : Set (EuclideanSpace ℝ (Fin m))), ‖𝓕 F (e.symm p)‖ ^ 2 =
        ∫ ξ' : EuclideanSpace ℝ (Fin m), ∫ ξ₀ in Icc (-R) R, ‖𝓕 F (e.symm (ξ₀, ξ'))‖ ^ 2 := by
      have h_swap : ∫ p : ℝ × EuclideanSpace ℝ (Fin m),
          (Icc (-R) R ×ˢ (univ : Set (EuclideanSpace ℝ (Fin m)))).indicator
            (fun p => ‖𝓕 F (e.symm p)‖ ^ 2) p =
          ∫ ξ' : EuclideanSpace ℝ (Fin m),
            (∫ ξ₀ : ℝ, (Icc (-R) R).indicator (fun ξ₀ => ‖𝓕 F (e.symm (ξ₀, ξ'))‖ ^ 2) ξ₀) := by
        have hint_ind : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
            (Icc (-R) R ×ˢ (univ : Set (EuclideanSpace ℝ (Fin m)))).indicator
              (fun p => ‖𝓕 F (e.symm p)‖ ^ 2) p) (volume.prod volume) := by
          have hcomp : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin m) => ‖𝓕 F (e.symm p)‖ ^ 2)
              (volume.prod volume) :=
            (hmp_symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hF_hat_sq_int
          exact hcomp.indicator (measurableSet_Icc.prod MeasurableSet.univ)
        rw [Measure.volume_eq_prod, integral_prod_symm _ hint_ind]
        refine integral_congr_ae (Eventually.of_forall fun ξ' => ?_)
        refine integral_congr_ae (Eventually.of_forall fun ξ₀ => ?_)
        by_cases hξ₀ : ξ₀ ∈ Icc (-R) R <;> simp [hξ₀]
      rw [← integral_indicator (measurableSet_Icc.prod MeasurableSet.univ), h_swap]
      refine integral_congr_ae (Eventually.of_forall fun ξ' => ?_)
      dsimp only
      rw [integral_indicator measurableSet_Icc]
    exact h1.trans_eq (h2.trans h3)
  have h_lhs_int : Integrable (fun ξ' : EuclideanSpace ℝ (Fin m) =>
      ∫ ξ₀ in Icc (-R) R, ‖𝓕 F (e.symm (ξ₀, ξ'))‖ ^ 2) volume := by
    have hint_ind : Integrable (fun p : EuclideanSpace ℝ (Fin m) × ℝ =>
        if p.2 ∈ Icc (-R) R then ‖𝓕 F (e.symm (p.2, p.1))‖ ^ 2 else 0) (volume.prod volume) :=
      (hF_hat_prod_int.indicator
        (MeasurableSet.univ.prod (measurableSet_Icc (a := -R) (b := R)))).congr
        (Eventually.of_forall fun p => by by_cases hp : p.2 ∈ Icc (-R) R <;> simp [hp])
    refine hint_ind.integral_prod_left.congr (Eventually.of_forall fun ξ' => ?_)
    dsimp only
    rw [← integral_indicator (measurableSet_Icc (a := -R) (b := R))]
    refine integral_congr_ae (Eventually.of_forall fun ξ₀ => ?_)
    by_cases hξ₀ : ξ₀ ∈ Icc (-R) R <;> simp [hξ₀]
  have h_rhs_int : Integrable (fun ξ' : EuclideanSpace ℝ (Fin m) =>
      (1 - ε_R) * ∫ x₀ : ℝ, ‖G x₀ ξ'‖ ^ 2) volume :=
    (hG_symm.integral_prod_left).const_mul _
  calc ∫ ξ in Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) R, ‖𝓕 F ξ‖ ^ 2
      ≤ ∫ ξ' : EuclideanSpace ℝ (Fin m), ∫ ξ₀ in Icc (-R) R, ‖𝓕 F (e.symm (ξ₀, ξ'))‖ ^ 2 :=
        h_ball_le
    _ ≤ ∫ ξ' : EuclideanSpace ℝ (Fin m), (1 - ε_R) * ∫ x₀ : ℝ, ‖G x₀ ξ'‖ ^ 2 :=
        integral_mono_ae h_lhs_int h_rhs_int h_1d_ae
    _ = (1 - ε_R) * ∫ ξ' : EuclideanSpace ℝ (Fin m), ∫ x₀ : ℝ, ‖G x₀ ξ'‖ ^ 2 :=
        integral_const_mul _ _
    _ = (1 - ε_R) * ∫ q : ℝ × EuclideanSpace ℝ (Fin m), ‖G q.1 q.2‖ ^ 2 := by
        have h_prod : ∫ q : ℝ × EuclideanSpace ℝ (Fin m), ‖G q.1 q.2‖ ^ 2 =
            ∫ ξ' : EuclideanSpace ℝ (Fin m), ∫ x₀ : ℝ, ‖G x₀ ξ'‖ ^ 2 := by
          rw [Measure.volume_eq_prod, integral_prod_symm _ hG_sq_prod_int]
        rw [← h_prod]
    _ = (1 - ε_R) * ∫ x : EuclideanSpace ℝ (Fin (m + 1)), ‖F x‖ ^ 2 := by
        rw [hG_total]

/-- Radial Fourier concentration bound on `EuclideanSpace ℝ (Fin (2 * w))` (`1 ≤ w`, `B > 0`)
for functions supported in `closedBall 0 √(2 B)` (`int:sonine`):
`∫ ξ in closedBall 0 √(2 B), ‖𝓕 F ξ‖ ^ 2 ≤ (1 - ε_B) * ∫ x, ‖F x‖ ^ 2` where
`ε_B = min (1 / 2) (1 / (1024 * π ^ 2 * B ^ 2 * exp (16 * π * B)))`. -/
theorem fourier_concentration_radial {w : ℕ} (hw : 1 ≤ w) {B : ℝ} (hB : 0 < B)
    {F : EuclideanSpace ℝ (Fin (2 * w)) → ℂ}
    (hF_meas : AEStronglyMeasurable F volume) (hF_mem : MemLp F 2 volume)
    (hF_supp : ∀ x : EuclideanSpace ℝ (Fin (2 * w)), Real.sqrt (2 * B) < ‖x‖ → F x = 0) :
    ∫ ξ in Metric.closedBall (0 : EuclideanSpace ℝ (Fin (2 * w))) (Real.sqrt (2 * B)), ‖𝓕 F ξ‖ ^ 2 ≤
      (1 - min (1 / 2 : ℝ) (1 / (1024 * π ^ 2 * B ^ 2 * Real.exp (16 * π * B)))) *
        ∫ x : EuclideanSpace ℝ (Fin (2 * w)), ‖F x‖ ^ 2 := by
  have h2w : 2 * w = (2 * w - 1) + 1 := by omega
  let e_cast : Fin (2 * w) ≃ Fin ((2 * w - 1) + 1) := (Fin.castOrderIso h2w).toEquiv
  let L_iso : EuclideanSpace ℝ (Fin (2 * w)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin ((2 * w - 1) + 1)) :=
    { toFun := fun x => WithLp.toLp 2 (fun i => x (e_cast.symm i))
      invFun := fun y => WithLp.toLp 2 (fun i => y (e_cast i))
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp
      left_inv := fun x => by ext i; simp
      right_inv := fun y => by ext i; simp
      norm_map' := fun x => by
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
          PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
        exact Fintype.sum_equiv e_cast.symm _ (fun j => ‖x j‖ ^ 2) (fun _ => rfl) }
  let G : EuclideanSpace ℝ (Fin ((2 * w - 1) + 1)) → ℂ := F ∘ L_iso.symm
  have hmp_symm : MeasurePreserving L_iso.symm volume volume := L_iso.symm.measurePreserving
  have hG_meas : AEStronglyMeasurable G volume :=
    hF_meas.comp_measurePreserving hmp_symm
  have hG_mem : MemLp G 2 volume :=
    hF_mem.comp_measurePreserving hmp_symm
  have hG_supp : ∀ y : EuclideanSpace ℝ (Fin ((2 * w - 1) + 1)), Real.sqrt (2 * B) < ‖y‖ → G y = 0 := by
    intro y hy
    apply hF_supp (L_iso.symm y)
    simpa [L_iso.symm.norm_map] using hy
  have h_euc := fourier_concentration_euclidean (m := 2 * w - 1) (R := Real.sqrt (2 * B))
    (Real.sqrt_pos.mpr (by positivity)) hG_meas hG_mem hG_supp
  have h_lhs : ∫ ξ in Metric.closedBall (0 : EuclideanSpace ℝ (Fin (2 * w))) (Real.sqrt (2 * B)),
      ‖𝓕 F ξ‖ ^ 2 =
      ∫ η in Metric.closedBall (0 : EuclideanSpace ℝ (Fin ((2 * w - 1) + 1))) (Real.sqrt (2 * B)),
        ‖𝓕 G η‖ ^ 2 := by
    have hpre : L_iso.symm ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin (2 * w))) (Real.sqrt (2 * B)) =
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin ((2 * w - 1) + 1))) (Real.sqrt (2 * B)) := by
      ext η; simp [Metric.mem_closedBall, dist_zero_right]
    have h_eq := hmp_symm.setIntegral_preimage_emb L_iso.symm.toHomeomorph.measurableEmbedding
      (fun ξ => ‖𝓕 F ξ‖ ^ 2) (Metric.closedBall 0 (Real.sqrt (2 * B)))
    rw [hpre] at h_eq
    rw [← h_eq]
    refine setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet fun η _ => ?_
    rw [← Real.fourier_comp_linearIsometry L_iso.symm F η]
  have h_rhs : ∫ x : EuclideanSpace ℝ (Fin (2 * w)), ‖F x‖ ^ 2 =
      ∫ y : EuclideanSpace ℝ (Fin ((2 * w - 1) + 1)), ‖G y‖ ^ 2 := by
    exact (hmp_symm.integral_comp L_iso.symm.toHomeomorph.measurableEmbedding
      (fun x => ‖F x‖ ^ 2)).symm
  have hconst : (256 * π ^ 2 * (Real.sqrt (2 * B)) ^ 4 * Real.exp (8 * π * (Real.sqrt (2 * B)) ^ 2)) =
      1024 * π ^ 2 * B ^ 2 * Real.exp (16 * π * B) := by
    have hsq : (Real.sqrt (2 * B)) ^ 2 = 2 * B := Real.sq_sqrt (by positivity)
    have h4 : (Real.sqrt (2 * B)) ^ 4 = 4 * B ^ 2 := by
      calc (Real.sqrt (2 * B)) ^ 4 = ((Real.sqrt (2 * B)) ^ 2) ^ 2 := by ring
        _ = (2 * B) ^ 2 := by rw [hsq]
        _ = 4 * B ^ 2 := by ring
    rw [hsq, h4]
    ring_nf
  rw [h_lhs, h_rhs, ← hconst]
  exact h_euc

/-- info: 'FormalResearch.ModularBootstrap.Integrality.fourier_concentration_radial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourier_concentration_radial

end FormalResearch.ModularBootstrap.Integrality
