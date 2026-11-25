module

public import FormalResearch.SignUncertainty.EuclidRadialSlice
public import FormalResearch.ModularBootstrap.Upper.Membership.HankelFormula

/-!
# Fourier transform of a radial function on `ℝ^{n+1}` as a half-plane integral

For `G` continuous on `[0,∞)` with integrable radial lift `x ↦ G(‖x‖²/2)` on `ℝ^{n+1}` and `r ∈ ℝ`,
`𝓕 (G(‖·‖²/2)) (r e₀) = n V_n ∫_{ℝ × (0,∞)} ρ^{n-1} e^{-2πi u r} G((u²+ρ²)/2) d(u,ρ)`, `V_n` the volume
of the unit ball of `ℝ^n` (`fourier_radial_single`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform ENNReal

namespace FormalResearch.SignUncertainty

open FormalResearch.ModularBootstrap.Upper.Membership

/-- The slice integrand `e^{-2πiur} G((u²+ρ²)/2)`. -/
noncomputable def sliceF (G : ℝ → ℝ) (r u ρ : ℝ) : ℂ :=
  Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((u : ℂ) * (r : ℂ))) * (G ((u ^ 2 + ρ ^ 2) / 2) : ℂ)

/-- With the weight `ρ^{n-1}`. -/
noncomputable def sliceH (n : ℕ) (G : ℝ → ℝ) (r : ℝ) (p : ℝ × ℝ) : ℂ :=
  ((p.2 ^ (n - 1) : ℝ) : ℂ) * sliceF G r p.1 p.2

lemma continuous_sliceF {G : ℝ → ℝ} (hG : ContinuousOn G (Ici 0)) (r : ℝ) :
    Continuous fun p : ℝ × ℝ => sliceF G r p.1 p.2 := by
  unfold sliceF
  refine (Complex.continuous_exp.comp (by fun_prop)).mul (Complex.continuous_ofReal.comp ?_)
  exact hG.comp_continuous (by fun_prop) fun p => mem_Ici.mpr (by positivity)

lemma continuous_sliceH (n : ℕ) {G : ℝ → ℝ} (hG : ContinuousOn G (Ici 0)) (r : ℝ) :
    Continuous (sliceH n G r) := by
  unfold sliceH
  exact (Complex.continuous_ofReal.comp (continuous_snd.pow _)).mul (continuous_sliceF hG r)

lemma norm_sliceF (G : ℝ → ℝ) (r u ρ : ℝ) : ‖sliceF G r u ρ‖ = |G ((u ^ 2 + ρ ^ 2) / 2)| := by
  unfold sliceF
  rw [norm_mul, show -2 * (Real.pi : ℂ) * Complex.I * ((u : ℂ) * (r : ℂ)) =
    ((-2 * Real.pi * (u * r) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

lemma ball_volume_real_pos (n : ℕ) [NeZero n] : 0 < (volume (Metric.ball (0 : EuclSp n) 1)).toReal :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' (measure_ball_lt_top).ne

lemma integrable_sliceF_prod (n : ℕ) {G : ℝ → ℝ} (hG : ContinuousOn G (Ici 0))
    (hint : Integrable (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ))) (r : ℝ) :
    Integrable fun p : ℝ × EuclSp n => sliceF G r p.1 ‖p.2‖ := by
  set x₀ : EuclSp (n + 1) := EuclideanSpace.single (0 : Fin (n + 1)) r with hx₀
  set g : EuclSp (n + 1) → ℂ := fun x => (G (‖x‖ ^ 2 / 2) : ℂ) with hg
  have he_mp := measurePreserving_euclSplit n
  have hg_cont : Continuous g :=
    Complex.continuous_ofReal.comp (hG.comp_continuous ((continuous_norm.pow 2).div_const 2)
      fun v => mem_Ici.mpr (by positivity))
  have hint_four : Integrable fun v : EuclSp (n + 1) =>
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ)) * g v := by
    have haesm : AEStronglyMeasurable (fun v : EuclSp (n + 1) =>
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ)) * g v) volume :=
      ((Complex.continuous_exp.comp (by fun_prop)).mul hg_cont).aestronglyMeasurable
    refine ⟨haesm, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun v => ?_) hint.hasFiniteIntegral
    rw [← ofReal_norm, ← ofReal_norm, norm_mul,
      show -2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ) =
        ((-2 * Real.pi * inner ℝ v x₀ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  have hint_prod : Integrable fun p : ℝ × EuclSp n => sliceF G r p.1 ‖p.2‖ := by
    refine ((he_mp.symm.integrable_comp_emb (euclSplit n).symm.measurableEmbedding).mpr
      hint_four).congr (Eventually.of_forall fun p => ?_)
    rw [Function.comp_apply, hg]
    dsimp only [x₀]
    rw [euclSplit_symm_norm_sq, euclSplit_symm_inner]
    unfold sliceF
    push_cast; rfl
  exact hint_prod

lemma integrableOn_sliceH (n : ℕ) (hn : 1 ≤ n) {G : ℝ → ℝ} (hG : ContinuousOn G (Ici 0))
    (hint : Integrable (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ))) (r : ℝ) :
    IntegrableOn (sliceH n G r) ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)) := by
  have : NeZero n := ⟨by omega⟩
  have hint_prod := integrable_sliceF_prod n hG hint r
  have hdim : Module.finrank ℝ (EuclSp n) = n := finrank_euclideanSpace_fin
  have hV := ball_volume_real_pos n
  have hnV : ((n : ℝ) * (volume (Metric.ball (0 : EuclSp n) 1)).toReal) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hcont := continuous_sliceH n hG r
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  refine (integrable_prod_iff hcont.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · have hip : Integrable (fun p : ℝ × EuclSp n => sliceF G r p.1 ‖p.2‖) (volume.prod volume) := by
      rwa [Measure.volume_eq_prod] at hint_prod
    filter_upwards [hip.prod_right_ae] with u hu
    have h1 := (integrable_fun_norm_addHaar (volume : Measure (EuclSp n))
      (f := fun ρ => sliceF G r u ρ)).mp hu
    rw [hdim] at h1
    refine h1.congr_fun (fun ρ _ => ?_) measurableSet_Ioi
    simp only [sliceH, Complex.real_smul]
  · have hip : Integrable (fun p : ℝ × EuclSp n => sliceF G r p.1 ‖p.2‖) (volume.prod volume) := by
      rwa [Measure.volume_eq_prod] at hint_prod
    have h1 := hip.integral_norm_prod_left
    refine (h1.const_mul ((n * (volume (Metric.ball (0 : EuclSp n) 1)).toReal)⁻¹)).congr
      (Eventually.of_forall fun u => ?_)
    simp only
    have h := integral_fun_norm_addHaar (volume : Measure (EuclSp n)) (fun ρ => ‖sliceF G r u ρ‖)
    rw [hdim] at h
    simp only [nsmul_eq_mul, smul_eq_mul, Measure.real] at h
    rw [h]
    have : ∫ ρ in Ioi (0 : ℝ), ‖sliceH n G r (u, ρ)‖ =
        ∫ ρ in Ioi (0 : ℝ), ρ ^ (n - 1) * ‖sliceF G r u ρ‖ := by
      refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
      simp only [sliceH, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (pow_pos hρ _)]
    rw [this]
    field_simp

theorem fourier_radial_single (n : ℕ) (hn : 1 ≤ n) {G : ℝ → ℝ} (hG : ContinuousOn G (Ici 0))
    (hint : Integrable (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ))) (r : ℝ) :
    𝓕 (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) (EuclideanSpace.single (0 : Fin (n + 1)) r) =
      (((n : ℝ) * (volume (Metric.ball (0 : EuclSp n) 1)).toReal : ℝ) : ℂ) *
        ∫ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), sliceH n G r p := by
  have : NeZero n := ⟨by omega⟩
  set x₀ : EuclSp (n + 1) := EuclideanSpace.single (0 : Fin (n + 1)) r with hx₀
  set g : EuclSp (n + 1) → ℂ := fun x => (G (‖x‖ ^ 2 / 2) : ℂ) with hg
  have hfour_eq : 𝓕 g x₀ = ∫ v : EuclSp (n + 1),
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ)) * g v := by
    simp only [Real.fourier_eq', smul_eq_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    dsimp only
    refine congrArg (· * g v) (congrArg Complex.exp ?_)
    push_cast; ring
  have he_mp := measurePreserving_euclSplit n
  have hint_prod := integrable_sliceF_prod n hG hint r
  have hH_int := integrableOn_sliceH n hn hG hint r
  have hstep1 : ∫ v : EuclSp (n + 1),
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ)) * g v =
      ∫ u : ℝ, ∫ y : EuclSp n, sliceF G r u ‖y‖ := by
    rw [← he_mp.symm.integral_comp']
    have heq : (fun p : ℝ × EuclSp n => Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
          (inner ℝ ((euclSplit n).symm p) x₀ : ℂ)) * g ((euclSplit n).symm p)) =
        fun p : ℝ × EuclSp n => sliceF G r p.1 ‖p.2‖ := by
      ext ⟨u, y⟩
      rw [hg]
      dsimp only [x₀]
      rw [euclSplit_symm_norm_sq, euclSplit_symm_inner]
      unfold sliceF
      push_cast; rfl
    rw [heq, Measure.volume_eq_prod, integral_prod _ hint_prod]
  have hdim : Module.finrank ℝ (EuclSp n) = n := finrank_euclideanSpace_fin
  have hstep2 : ∀ u : ℝ, ∫ y : EuclSp n, sliceF G r u ‖y‖ =
      (((n : ℝ) * (volume (Metric.ball (0 : EuclSp n) 1)).toReal : ℝ) : ℂ) *
        ∫ ρ in Ioi (0 : ℝ), sliceH n G r (u, ρ) := by
    intro u
    have h := integral_fun_norm_addHaar (volume : Measure (EuclSp n)) (fun ρ => sliceF G r u ρ)
    rw [hdim] at h
    simp only [nsmul_eq_mul, Complex.real_smul, Measure.real] at h
    rw [h]
    simp only [sliceH]
    push_cast
    ring
  have hV := ball_volume_real_pos n
  have hnV : ((n : ℝ) * (volume (Metric.ball (0 : EuclSp n) 1)).toReal) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hstep3 : (∫ u : ℝ, ∫ ρ in Ioi (0 : ℝ), sliceH n G r (u, ρ)) =
      ∫ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), sliceH n G r p := by
    rw [Measure.volume_eq_prod] at hH_int ⊢
    have hprod := (setIntegral_prod (sliceH n G r) hH_int).symm
    simp_rw [setIntegral_univ] at hprod
    exact hprod
  rw [hfour_eq, hstep1]
  simp_rw [hstep2]
  rw [integral_const_mul, hstep3]

end FormalResearch.SignUncertainty
