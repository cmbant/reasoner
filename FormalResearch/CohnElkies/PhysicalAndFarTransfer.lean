module

public import FormalResearch.CohnElkies.MellinMainKernel
public import FormalResearch.CohnElkies.MovingDiagonalSource

/-!
# Physical-coordinate far transfer, compact contraction, and global GT.4 coverage

Formalization of `CFT/sign_uncertainty/paper/ce_physical_log_far.tex` and
`CFT/sign_uncertainty/paper/ce_o1_global_transfer.tex` (`origin/main`):

* **Section 1 — Lemma `FG.3` (`(cepf:FG.3a)`–`(cepf:FG.3)`):** unconditional pointwise bound
  `‖mainEdgeAmp κ m c τ‖ ≤ (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1`, integrability of `mainEdgeAmp`,
  definition of `mainTransferOp`, exact Fourier multiplier identity `(cepf:FG.3b)` for
  `f ∈ L¹(ℝ) ∩ H¹(ℝ)` in terms of `fourierPaper`, and uniform sup bound `(cepf:FG.3)`
  `‖mainTransferOp κ m c f L‖ ≤ ceCs⁻¹ * Real.sqrt (‖f‖₂ * ‖f'‖₂)`.
* **Section 2 — Theorem `PF.T(1)` (omitted region `X ≤ 2d`):** unconditional `O(c⁻¹ M L⁻²)`
  bound `omittedRegion_bound` for `0 < d < L_min / (8 * ceCs)`.
* **Section 3 — Macroscopic transfer (`PF.2L`, `PF.T(2)–(4)`) and `GT.3b`:**
  packaged stationary-phase interface `MacroscopicTransferPackage` (only the fields `GT.3b` uses) with
  non-vacuity witness, unconditional rescaled origin-mass bound `(cegt:GT3d)` from
  `twoScale_origin_mass`, and Lemma `GT.3b` (`(cegt:eqGT3b)` with `κ`-independent floor
  `b_F (1 + L)^{-3/2}`). The Route I consumers (Theorem `PF.2`, Theorem `PF.5`) and the `GT.4`
  coverage package `GT4CoverageBands` were removed (supplement part `ce_coherent_square_lift.tex`).
* **Section 4 — `GT.4` leading tip offset (`thm:ce-lift`, Route I):** unconditional exact leading tip
  offset `b₁² - c₁²` and `F_c^{(0)}(a₁) / (2 Ai'(a₁)²)` (plus origin-tuned `F_c(a₁) / (2 Ai'(a₁)²)`).
-/

@[expose] public section

open Real Complex MeasureTheory Set Filter
open FormalResearch.Special FormalResearch.Asymptotics
open scoped FourierTransform BigOperators Topology

namespace FormalResearch.CohnElkies

/-! ## Section 1: Lemma `FG.3` (`(cepf:FG.3a)`–`(cepf:FG.3)`) -/

/-- **Pointwise main-edge amplitude bound `(cepf:FG.3a)`:** for `κ : ℝ`, `m : ℕ`, `c > 0`, and `τ : ℝ`,
`‖mainEdgeAmp κ m c τ‖ ≤ (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))` and `‖mainEdgeAmp κ m c τ‖ ≤ 1`. -/
theorem norm_mainEdgeAmp_le (κ : ℝ) (m : ℕ) {c : ℝ} (hc : 0 < c) (τ : ℝ) :
    ‖mainEdgeAmp κ m c τ‖ ≤ (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) ∧ ‖mainEdgeAmp κ m c τ‖ ≤ 1 := by
  have hpow : ‖((1 : ℂ) - (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))‖ = (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
    rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real]
    have hnorm : ‖(1 : ℂ) - (τ : ℂ) * Complex.I‖ = (1 + τ ^ 2) ^ (1 / 2 : ℝ) := by
      rw [Complex.norm_def, Complex.normSq_apply, Real.sqrt_eq_rpow]; congr 1; simp; ring
    rw [hnorm, ← Real.rpow_mul (by positivity)]; norm_num
  have hbinet : ‖Complex.exp (binetDiff c ((τ : ℂ) * Complex.I))‖ ≤ 1 := by
    rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr (by simpa [binetDiff] using binetDiff_re_vertical_le hc zero_lt_one τ)
  have hbs : ‖bsplineImag (ceCs * κ / m) m τ‖ ≤ 1 := by
    unfold bsplineImag; rw [norm_pow, bsplineE1_eq_integral]
    exact pow_le_one₀ (norm_nonneg _)
      (by simpa [mul_assoc] using norm_bsplineKernel_le_of_re_ge (l := 0) le_rfl (by simp [Complex.mul_re] : -(0 : ℝ) ≤ _))
  have hbd : ‖mainEdgeAmp κ m c τ‖ ≤ (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
    unfold mainEdgeAmp; rw [norm_mul, norm_mul, hpow]
    calc (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) * ‖Complex.exp (binetDiff c ((τ : ℂ) * Complex.I))‖ * ‖bsplineImag (ceCs * κ / m) m τ‖
        ≤ (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) * 1 * 1 := by gcongr
      _ = (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by ring
  exact ⟨hbd, hbd.trans (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [sq_nonneg τ]) (by norm_num))⟩

/-- Integrability of `mainEdgeAmp κ m c` for `κ > 0`, `1 ≤ m`, `1 ≤ c`. -/
lemma integrable_mainEdgeAmp {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 1 ≤ c) :
    Integrable (mainEdgeAmp κ m c) := by
  obtain ⟨hcd, C_a, hCa, hbd⟩ := mainEdgeAmp_contDiff_and_bound hκ hm
  refine ((integrable_one_add_norm (E := ℝ) (r := (3 / 2 : ℝ))
    (by rw [Module.finrank_self]; norm_num)).const_mul C_a).mono'
    (hcd hc).continuous.aestronglyMeasurable (ae_of_all _ fun τ => ?_)
  have hm_r : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (3 / 2 : ℝ) ≤ (m : ℝ) + 1 / 2 := by linarith
  calc ‖mainEdgeAmp κ m c τ‖ ≤ C_a * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2) := hbd hc 0 (by decide) τ
    _ ≤ C_a * (1 + ‖τ‖) ^ (-(3 / 2 : ℝ)) := by
        rw [Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg τ]) (by linarith)) hCa.le

/-- The normalized Mellin convolution operator `(T_c f)(L)` of `(cepf:FG.3a)`:
`(T_c f)(L) = (c / (2π)) ∫_ℝ f(X) K_c(L - c_s X) dX`. -/
noncomputable def mainTransferOp (κ : ℝ) (m : ℕ) (c : ℝ) (f : ℝ → ℂ) (L : ℝ) : ℂ :=
  ((c : ℂ) / (2 * π)) * ∫ X : ℝ, f X * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)

lemma mainTransferOp_eq_opT (κ : ℝ) (m : ℕ) (c : ℝ) (f : ℝ → ℂ) (L : ℝ) :
    mainTransferOp κ m c f L = opT (mainEdgeAmp κ m c) edgeR c ceCs f L := by
  have hker : ∀ y : ℝ, mainEdgeKernel (mainEdgeAmp κ m c) c y = kernelPaper (mainEdgeAmp κ m c) edgeR c y := fun y => by
    unfold mainEdgeKernel kernelPaper; congr 1; ext τ; push_cast; ring_nf
  unfold mainTransferOp opT; push_cast; simp_rw [hker]

private lemma fourierPaper_eq_fourierIntegral {f : ℝ → ℂ} (ξ : ℝ) : fourierPaper f ξ = (𝓕 f) ((2 * π)⁻¹ * ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]; unfold fourierPaper; congr 1; ext x; rw [smul_eq_mul]; congr 2; push_cast
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hpi]

private lemma ae_comp_mul_left_of_ae {g h : ℝ → ℂ} (heq : g =ᵐ[volume] h) {a : ℝ} (ha : a ≠ 0) :
    (fun x : ℝ => g (a * x)) =ᵐ[volume] fun x : ℝ => h (a * x) := by
  refine ae_iff.mpr ?_
  change volume ((a * ·) ⁻¹' {u | ¬g u = h u}) = 0
  rw [Real.volume_preimage_mul_left ha, ae_iff.mp heq, mul_zero]

/-- Bridge: when `f ∈ L¹(ℝ)` and `WeakDerivL2 f f'`, `fourierPaperL2 h` agrees a.e. with
`fourierPaper f`. -/
theorem fourierPaperL2_ae_eq_fourierPaper {f f' : ℝ → ℂ} (hf1 : Integrable f) (h : WeakDerivL2 f f') :
    (fourierPaperL2 h : ℝ → ℂ) =ᵐ[volume] fourierPaper f := by
  set F : Lp ℂ 2 volume := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp.toLp f)
  have hF2 : MemLp (F : ℝ → ℂ) 2 volume := Lp.memLp F
  have hFour_bdd : Continuous (𝓕 f) ∧ ∀ ξ : ℝ, ‖𝓕 f ξ‖ ≤ ∫ x : ℝ, ‖f x‖ :=
    ⟨VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf1,
      fun ξ => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ ξ⟩
  let w : ℝ → ℝ := fun ξ => (1 + ξ ^ 2)⁻¹
  have hw_pos : ∀ ξ : ℝ, 0 < w ξ := fun ξ => by dsimp [w]; positivity
  have hw_le : ∀ ξ : ℝ, w ξ ≤ 1 := fun ξ => inv_le_one_of_one_le₀ (by linarith [sq_nonneg ξ])
  have hinv_tg : (fun ξ : ℝ => (w ξ : ℂ)).HasTemperateGrowth := by
    rw [show (fun ξ : ℝ => (w ξ : ℂ)) = Complex.ofReal ∘ fun ξ : ℝ => (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ) from
      funext fun ξ => by simp [w, Real.rpow_neg_one]]
    exact Complex.hasTemperateGrowth_ofReal.comp (Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (-1))
  let u : ℝ → ℂ := fun ξ => (w ξ : ℂ) * (F : ℝ → ℂ) ξ - (w ξ : ℂ) * (𝓕 f) ξ
  have hc_inv : Continuous (fun ξ : ℝ => (w ξ : ℂ)) :=
    Complex.continuous_ofReal.comp (((continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).add
      (continuous_id.pow 2)).inv₀ fun ξ => by dsimp; positivity)
  have hF_sq : Integrable (fun ξ : ℝ => ‖(w ξ : ℂ) * (F : ℝ → ℂ) ξ‖ ^ 2) :=
    ((memLp_two_iff_integrable_sq_norm hF2.aestronglyMeasurable).mp hF2).mono'
      ((hc_inv.aestronglyMeasurable.mul hF2.aestronglyMeasurable).norm.pow 2)
      (ae_of_all _ fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (hw_pos ξ)]
        exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (hw_pos ξ).le (hw_le ξ)))
  have hFf_sq : Integrable (fun ξ : ℝ => ‖(w ξ : ℂ) * (𝓕 f) ξ‖ ^ 2) :=
    (integrable_inv_one_add_sq.const_mul ((∫ x : ℝ, ‖f x‖) ^ 2)).mono'
      ((hc_inv.aestronglyMeasurable.mul hFour_bdd.1.aestronglyMeasurable).norm.pow 2)
      (ae_of_all _ fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (hw_pos ξ)]
        have h1 : w ξ ^ 2 ≤ w ξ := by dsimp [w]; rw [sq]; exact mul_le_of_le_one_right (hw_pos ξ).le (hw_le ξ)
        calc w ξ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 ≤ w ξ * (∫ x : ℝ, ‖f x‖) ^ 2 :=
              mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) (hFour_bdd.2 ξ) 2) (sq_nonneg _) (hw_pos ξ).le
          _ = (∫ x : ℝ, ‖f x‖) ^ 2 * (1 + ξ ^ 2)⁻¹ := by dsimp [w]; ring)
  have hu2 : MemLp u 2 volume :=
    ((memLp_two_iff_integrable_sq_norm (hc_inv.aestronglyMeasurable.mul hF2.aestronglyMeasurable)).mpr hF_sq).sub
      ((memLp_two_iff_integrable_sq_norm (hc_inv.aestronglyMeasurable.mul hFour_bdd.1.aestronglyMeasurable)).mpr hFf_sq)
  have htest : ∀ ψ : SchwartzMap ℝ ℂ,
      ∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * (F : ℝ → ℂ) ξ = ∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * (𝓕 f) ξ := fun ψ => by
    have hL : ∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * (F : ℝ → ℂ) ξ = inner ℂ (ψ.toLp 2 volume) F := by
      rw [MeasureTheory.L2.inner_def]; refine integral_congr_ae ?_
      filter_upwards [ψ.coeFn_toLp 2 volume] with ξ hξ; rw [hξ, RCLike.inner_apply, starRingEnd_apply]; ring
    have hpl : inner ℂ (ψ.toLp 2 volume) F = inner ℂ ((𝓕⁻ ψ).toLp 2 volume) (h.memLp.toLp f) := by
      have hstep := MeasureTheory.Lp.inner_fourier_eq (𝓕⁻ (ψ.toLp 2 volume)) (h.memLp.toLp f)
      have hFrfl : 𝓕 (h.memLp.toLp f) = F := rfl
      rwa [FourierInvPair.fourier_fourierInv_eq _, SchwartzMap.toLp_fourierInv_eq, hFrfl] at hstep
    have hR : inner ℂ ((𝓕⁻ ψ).toLp 2 volume) (h.memLp.toLp f) =
        ∫ x : ℝ, starRingEnd ℂ ((𝓕⁻ (ψ : ℝ → ℂ)) x) * f x := by
      rw [MeasureTheory.L2.inner_def]; refine integral_congr_ae ?_
      filter_upwards [(𝓕⁻ ψ).coeFn_toLp 2 volume, h.memLp.coeFn_toLp] with x hx1 hx2
      rw [hx1, hx2, congrFun (SchwartzMap.fourierInv_coe ψ) x, RCLike.inner_apply, starRingEnd_apply]; ring
    have hflip : (innerₛₗ ℝ).flip = (innerₛₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) := flip_innerₗ ℝ
    have hsesq := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ)
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf1 (ψ.integrable (μ := volume))
    rw [hflip] at hsesq; have hconj := congrArg (starRingEnd ℂ) hsesq
    rw [← integral_conj, ← integral_conj] at hconj
    change ∫ ξ : ℝ, starRingEnd ℂ (inner ℂ (𝓕 f ξ) (ψ ξ)) = ∫ x : ℝ, starRingEnd ℂ (inner ℂ (f x) (𝓕⁻ (ψ : ℝ → ℂ) x)) at hconj
    simp_rw [inner_conj_symm, RCLike.inner_apply, starRingEnd_apply] at hconj; rw [hL, hpl, hR]; simpa [mul_comm] using hconj.symm
  have hinner : ∀ η : SchwartzMap ℝ ℂ, inner ℂ (η.toLp 2 volume) (hu2.toLp u) = 0 := fun η => by
    let ψ : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ (fun ξ => (w ξ : ℂ)) η
    let ψ_conj : SchwartzMap ℝ ℂ := ψ.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)
    have hψ_eq : ∀ ξ : ℝ, starRingEnd ℂ (η ξ) * u ξ =
        starRingEnd ℂ (ψ ξ) * (F : ℝ → ℂ) ξ - starRingEnd ℂ (ψ ξ) * (𝓕 f) ξ := fun ξ => by
      have hψ := SchwartzMap.smulLeftCLM_apply_apply hinv_tg η ξ
      rw [smul_eq_mul] at hψ; rw [hψ, map_mul, Complex.conj_ofReal]; dsimp [u]; ring
    have h1 : Integrable (fun ξ : ℝ => starRingEnd ℂ (ψ ξ) * (F : ℝ → ℂ) ξ) :=
      (ψ_conj.memLp 2 volume).integrable_mul hF2
    have h2 : Integrable (fun ξ : ℝ => starRingEnd ℂ (ψ ξ) * (𝓕 f) ξ) :=
      ((ψ.integrable (μ := volume)).norm.const_mul (∫ x : ℝ, ‖f x‖)).mono'
        (ψ_conj.continuous.aestronglyMeasurable.mul hFour_bdd.1.aestronglyMeasurable)
        (ae_of_all _ fun ξ => by
          rw [norm_mul, Complex.norm_conj]
          exact (mul_le_mul_of_nonneg_left (hFour_bdd.2 ξ) (norm_nonneg _)).trans_eq (mul_comm _ _))
    rw [MeasureTheory.L2.inner_def]
    calc ∫ ξ : ℝ, inner ℂ ((η.toLp 2 volume : ℝ → ℂ) ξ) ((hu2.toLp u : ℝ → ℂ) ξ)
        = ∫ ξ : ℝ, starRingEnd ℂ (η ξ) * u ξ := by
          refine integral_congr_ae ?_
          filter_upwards [η.coeFn_toLp 2 volume, hu2.coeFn_toLp] with ξ h1' h2'
          rw [h1', h2', RCLike.inner_apply, starRingEnd_apply]; ring
      _ = (∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * (F : ℝ → ℂ) ξ) -
            ∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * (𝓕 f) ξ := by simp_rw [hψ_eq]; exact integral_sub h1 h2
      _ = 0 := sub_eq_zero.mpr (htest ψ)
  have hU0 : hu2.toLp u = 0 :=
    inner_self_eq_zero.mp <| congrFun
      ((SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top).equalizer
        (continuous_id.inner continuous_const) continuous_const (funext hinner)) (hu2.toLp u)
  have hu0 : u =ᵐ[volume] (0 : ℝ → ℂ) := hu2.coeFn_toLp.symm.trans (by rw [hU0]; exact Lp.coeFn_zero _ _ _)
  have hFae : (F : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
    filter_upwards [hu0] with ξ hξ
    have hmul0 : (w ξ : ℂ) * ((F : ℝ → ℂ) ξ - 𝓕 f ξ) = 0 := by dsimp [u] at hξ; linear_combination hξ
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul0).resolve_left (by exact_mod_cast (hw_pos ξ).ne'))
  filter_upwards [ae_comp_mul_left_of_ae hFae (by positivity : ((2 * π)⁻¹ : ℝ) ≠ 0)] with ξ hξ
  simpa [fourierPaperL2, F, fourierPaper_eq_fourierIntegral] using hξ

/-- **Exact Fourier multiplier representation `(cepf:FG.3b)`** for `f ∈ L¹(ℝ) ∩ H¹(ℝ)`:
`(T_c f)(L) = (1 / (2π)) ∫_ℝ a_c(w/c) e^{i c R(w/c)} f̂(c_s w) e^{i L w} dw`. -/
theorem mainTransferOp_eq_fourier_multiplier {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 1 ≤ m)
    {c : ℝ} (hc : 1 ≤ c) {f f' : ℝ → ℂ} (hf1 : Integrable f) (h : WeakDerivL2 f f') (L : ℝ) :
    mainTransferOp κ m c f L =
      (1 / (2 * π) : ℝ) • ∫ w : ℝ,
        mainEdgeAmp κ m c (w / c) * Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ)) *
          fourierPaper f (ceCs * w) * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ)) := by
  have hc0 : 0 < c := by linarith
  rw [mainTransferOp_eq_opT, opT_eq_fourier_multiplier hc0 ceCs_pos.ne'
    (integrable_mainEdgeAmp hκ hm hc) (fun τ => (norm_mainEdgeAmp_le κ m hc0 τ).2)
    edgeR_contDiff.continuous.measurable h L]
  congr 1
  let G : ℝ → (ℝ → ℂ) → ℂ := fun w g =>
    mainEdgeAmp κ m c (w / c) * Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ)) *
      g (ceCs * w) * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ))
  have hcov : ∀ g, ∫ w : ℝ, G w g = ((|ceCs⁻¹| : ℝ) : ℂ) * ∫ u : ℝ, G (ceCs⁻¹ * u) g := fun g => by
    have h1 := Measure.integral_comp_mul_left (fun u : ℝ => G (ceCs⁻¹ * u) g) ceCs
    rw [show (fun w : ℝ => G (ceCs⁻¹ * (ceCs * w)) g) = fun w => G w g from by
      ext w; dsimp [G]; simp [inv_mul_cancel_left₀ ceCs_pos.ne']] at h1
    simpa [Complex.real_smul] using h1
  have h_congr : ∫ u : ℝ, G (ceCs⁻¹ * u) (fourierPaperL2 h) = ∫ u : ℝ, G (ceCs⁻¹ * u) (fourierPaper f) := by
    refine integral_congr_ae ?_
    filter_upwards [fourierPaperL2_ae_eq_fourierPaper hf1 h] with u hu
    dsimp [G]; simp only [mul_inv_cancel_left₀ ceCs_pos.ne', hu]
  rw [hcov, hcov, h_congr]

/-- **Uniform `L^∞` bound `(cepf:FG.3)`:** for `κ > 0`, `m ≥ 1`, `c ≥ 1`, and `f ∈ H¹(ℝ)`
(`WeakDerivL2 f f'`), `‖mainTransferOp κ m c f L‖ ≤ ceCs⁻¹ * Real.sqrt (l2norm f * l2norm f')`. -/
theorem mainTransferOp_sup_norm_le {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 1 ≤ m)
    {c : ℝ} (hc : 1 ≤ c) {f f' : ℝ → ℂ} (h : WeakDerivL2 f f') (L : ℝ) :
    ‖mainTransferOp κ m c f L‖ ≤ ceCs⁻¹ * Real.sqrt (l2norm f * l2norm f') := by
  have hc0 : 0 < c := by linarith
  rw [mainTransferOp_eq_opT]
  simpa only [one_div, abs_of_pos ceCs_pos] using
    Tc_sup_bound hc0 ceCs_pos.ne' (integrable_mainEdgeAmp hκ hm hc)
      (fun τ => (norm_mainEdgeAmp_le κ m hc0 τ).2) edgeR_contDiff.continuous.measurable h L

/-! ## Section 2: Theorem `PF.T(1)` — omitted small-`X` region (`(cepf:PFT)`(1)) -/

/-- Continuity of `y ↦ mainEdgeKernel (mainEdgeAmp κ m c) c y`. -/
lemma continuous_mainEdgeKernel {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 1 ≤ c) :
    Continuous (mainEdgeKernel (mainEdgeAmp κ m c) c) := by
  refine MeasureTheory.continuous_of_dominated (bound := fun τ => ‖mainEdgeAmp κ m c τ‖)
    (fun y => (((mainEdgeAmp_contDiff_and_bound hκ hm).1 hc).continuous.aestronglyMeasurable.mul
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        ((continuous_const.mul continuous_id).add edgeR_contDiff.continuous)))).aestronglyMeasurable))
    (fun y => ae_of_all _ fun τ => by
      have hre : (Complex.I * (c : ℂ) * ((y * τ + edgeR τ : ℝ) : ℂ)).re = 0 := by
        rw [show Complex.I * (c : ℂ) * ((y * τ + edgeR τ : ℝ) : ℂ) =
          (((c * (y * τ + edgeR τ) : ℝ) : ℂ) * Complex.I) by push_cast; ring]; simp
      rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one])
    (integrable_mainEdgeAmp hκ hm hc).norm (ae_of_all _ fun τ => continuous_const.mul
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        ((continuous_id.mul continuous_const).add continuous_const)))))

/-- **Theorem `PF.T(1)` (omitted region `X ≤ 2d`):** for `κ > 0`, `m ≥ 4`, `L_min > 0`, and
`0 < d < L_min / (8 * ceCs)`, there is `C > 0` such that for all `c ≥ 2`, `L ≥ L_min`, and
`f : ℝ → ℂ` with `IntegrableOn f (Iic (2 * d))`, the normalized omitted-region integral is
`≤ C * c⁻¹ * M * L ^ (-2 : ℝ)`. -/
theorem omittedRegion_bound {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 4 ≤ m)
    {L_min d : ℝ} (hLmin : 0 < L_min) (_hd0 : 0 < d) (hd_lt : d < L_min / (8 * ceCs)) :
    ∃ C > 0, ∀ {c L : ℝ} {f : ℝ → ℂ}, 2 ≤ c → L_min ≤ L → IntegrableOn f (Iic (2 * d)) →
      let M := ∫ X in Iic (2 * d), ‖f X‖
      ‖((c : ℂ) / (2 * π)) *
          ∫ X in Iic (2 * d), f X * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖ ≤
        C * c⁻¹ * M * L ^ (-2 : ℝ) := by
  obtain ⟨C₁, hC₁, hdecay⟩ := mainEdgeKernel_right_decay hκ hm (by positivity : 0 < (3 / 4 : ℝ) * L_min)
  refine ⟨(8 * C₁) / (9 * π), by positivity, fun {c L f} hc hL hf => ?_⟩
  dsimp only
  have hc0 : 0 < c := by linarith
  have hL0 : 0 < L := hLmin.trans_le hL
  have hker_comp : Continuous (fun X : ℝ => mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)) :=
    (continuous_mainEdgeKernel hκ (by omega) (by linarith)).comp (continuous_const.sub (continuous_const.mul continuous_id))
  have hpt : ∀ X ∈ Iic (2 * d), ‖f X * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖ ≤
      ((16 / 9 : ℝ) * C₁ * c ^ (-2 : ℝ) * L ^ (-2 : ℝ)) * ‖f X‖ := fun X hX => by
    have hce_d : ceCs * (2 * d) < L_min / 4 := (mul_lt_mul_of_pos_left hd_lt (by positivity [ceCs_pos] : 0 < 2 * ceCs)).trans_eq'
      (by ring) |>.trans_eq (by field_simp [ceCs_pos.ne']; ring)
    have hy_ge_L : (3 / 4 : ℝ) * L ≤ L - ceCs * X := by have : ceCs * X ≤ ceCs * (2 * d) := mul_le_mul_of_nonneg_left hX ceCs_pos.le; linarith
    have hbd2 : (L - ceCs * X) ^ (-2 : ℝ) ≤ (16 / 9 : ℝ) * L ^ (-2 : ℝ) :=
      (Real.rpow_le_rpow_of_nonpos (by positivity) hy_ge_L (by norm_num)).trans_eq
        ((Real.mul_rpow (by norm_num) hL0.le).trans (by norm_num))
    rw [norm_mul]; have hbd1 := (hdecay hc (by nlinarith : (3 / 4 : ℝ) * L_min ≤ L - ceCs * X)).1
    exact (mul_le_mul_of_nonneg_left (hbd1.trans (mul_le_mul_of_nonneg_left hbd2 (by positivity))) (norm_nonneg _)).trans_eq (by ring)
  have hint_maj := hf.norm.const_mul ((16 / 9 : ℝ) * C₁ * c ^ (-2 : ℝ) * L ^ (-2 : ℝ))
  have hint_norm : IntegrableOn (fun X => ‖f X * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖) (Iic (2 * d)) :=
    hint_maj.mono' (hf.aestronglyMeasurable.mul hker_comp.aestronglyMeasurable).norm
      ((ae_restrict_mem measurableSet_Iic).mono fun X hX => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hpt X hX)
  have hint_le := (setIntegral_mono_on hint_norm hint_maj measurableSet_Iic hpt).trans_eq (integral_const_mul _ _)
  have hpre : ‖((c : ℂ) / (2 * π))‖ = c / (2 * π) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0,
      show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hc_mul : c * c ^ (-2 : ℝ) = c⁻¹ := by
    rw [show c * c ^ (-2 : ℝ) = c ^ (1 : ℝ) * c ^ (-2 : ℝ) by simp, ← Real.rpow_add hc0]
    norm_num; exact Real.rpow_neg_one c
  rw [norm_mul, hpre]
  calc (c / (2 * π)) * ‖∫ X in Iic (2 * d), f X * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖
      ≤ (c / (2 * π)) * ∫ X in Iic (2 * d), ‖f X * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ (c / (2 * π)) * (((16 / 9 : ℝ) * C₁ * c ^ (-2 : ℝ) * L ^ (-2 : ℝ)) * ∫ X in Iic (2 * d), ‖f X‖) :=
        mul_le_mul_of_nonneg_left hint_le (by positivity)
    _ = ((8 * C₁) / (9 * π)) * c⁻¹ * (∫ X in Iic (2 * d), ‖f X‖) * L ^ (-2 : ℝ) := by
        rw [← hc_mul]; ring

/-! ## Section 3: Macroscopic transfer package (`PF.2L`, `PF.T(2)–(4)`) and `GT.3b` -/

/-- Packaged smooth + coherent stationary-phase transfer interface (`PF.2L`, `PF.T(2)–(4)` of
`ce_physical_log_far.tex`), leaving the omitted region `X ≤ 2d` unconditional via `omittedRegion_bound`. -/
structure MacroscopicTransferPackage (κ : ℝ) (m : ℕ) (L_min d : ℝ) where
  c_T : ℝ
  hc_T : 2 ≤ c_T
  f : ℝ → ℝ → ℝ
  M : ℝ → ℝ
  B0 : ℝ → ℝ
  B : ℝ → ℝ
  b0 : ℝ → ℝ → ℝ
  cutoffOm : ℝ → ℝ
  cutoffOm_measurable : Measurable cutoffOm
  cutoffOm_bound : ∀ X : ℝ, |cutoffOm X| ≤ 1
  E_sm : ℝ → ℝ → ℂ
  T_plus : ℝ → ℝ → ℂ
  T_minus : ℝ → ℝ → ℂ
  f_int_om : ∀ {c : ℝ}, c_T ≤ c → IntegrableOn (fun X => (f c X : ℂ)) (Iic (2 * d))
  M_nonneg : ∀ {c : ℝ}, c_T ≤ c → 0 ≤ M c
  M_spec : ∀ {c : ℝ}, c_T ≤ c → (∫ X in Iic (2 * d), ‖(f c X : ℂ)‖) ≤ M c
  B0_nonneg : ∀ {c : ℝ}, c_T ≤ c → 0 ≤ B0 c
  exact_decomp : ∀ {c L : ℝ}, c_T ≤ c → L_min ≤ L →
    (ceK : ℂ) * mainTransferOp κ m c (fun X => (f c X : ℂ)) L =
      ((ceK / ceCs * b0 c (L / ceCs) : ℝ) : ℂ) +
        (ceK : ℂ) * (((c : ℂ) / (2 * π)) * ∫ X in Iic (2 * d),
          ((cutoffOm X * f c X : ℝ) : ℂ) * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)) +
        E_sm c L + T_plus c L + T_minus c L
  C_sm : ℝ
  hC_sm : 0 < C_sm
  smooth_bound : ∀ {c L : ℝ}, c_T ≤ c → L_min ≤ L →
    ‖E_sm c L‖ ≤ C_sm * B0 c * (c⁻¹ * L ^ (-2 : ℝ) + L ^ (-(3 / 2 : ℝ)) * ((c * L)⁻¹ + c ^ (-4 : ℝ) * L ^ (-5 : ℝ)))
  C_coh_glob : ℝ
  hC_coh_glob : 0 < C_coh_glob
  coherent_global_bound : ∀ {c L : ℝ}, c_T ≤ c → L_min ≤ L →
    (1 + L) ^ (3 / 2 : ℝ) * ‖T_plus c L + T_minus c L‖ ≤ C_coh_glob * B c

/-- Explicit non-vacuity witness for `MacroscopicTransferPackage`. -/
theorem macroscopicTransferPackage_nonvacuous {κ L_min d : ℝ} {m : ℕ} :
    Nonempty (MacroscopicTransferPackage κ m L_min d) :=
  ⟨{ c_T := 2, hc_T := le_rfl, f := fun _ _ => 0, M := fun _ => 0, B0 := fun _ => 0, B := fun _ => 0,
     b0 := fun _ _ => 0,
     cutoffOm := fun _ => 0, cutoffOm_measurable := measurable_const, cutoffOm_bound := fun _ => by norm_num,
     E_sm := fun _ _ => 0, T_plus := fun _ _ => 0, T_minus := fun _ _ => 0,
     f_int_om := fun _ => by simp, M_nonneg := fun _ => le_rfl, M_spec := fun _ => by simp,
     B0_nonneg := fun _ => le_rfl,
     exact_decomp := fun _ _ => by simp [mainTransferOp],
     C_sm := 1, hC_sm := one_pos, smooth_bound := fun _ _ => by simp,
     C_coh_glob := 1, hC_coh_glob := one_pos, coherent_global_bound := fun _ _ => by simp }⟩

private lemma omitted_cutoff_bound {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 4 ≤ m)
    {L_min d : ℝ} (hLmin : 0 < L_min) (hd0 : 0 < d) (hd_lt : d < L_min / (8 * ceCs))
    (pkg : MacroscopicTransferPackage κ m L_min d) :
    ∃ C_om > 0, ∀ {c L : ℝ}, pkg.c_T ≤ c → L_min ≤ L →
      ‖(ceK : ℂ) * (((c : ℂ) / (2 * π)) *
          ∫ X in Iic (2 * d), ((pkg.cutoffOm X * pkg.f c X : ℝ) : ℂ) *
            mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X))‖ ≤ C_om * c⁻¹ * pkg.M c * L ^ (-2 : ℝ) := by
  obtain ⟨C₀, hC₀, hom⟩ := omittedRegion_bound hκ hm hLmin hd0 hd_lt
  refine ⟨ceK * C₀, mul_pos ceK_pos hC₀, fun {c L} hc hL => ?_⟩
  have hc2 : 2 ≤ c := pkg.hc_T.trans hc; have hc0 : 0 ≤ c := by linarith
  have hf_int := pkg.f_int_om hc
  have hcut_int : IntegrableOn (fun X => ((pkg.cutoffOm X * pkg.f c X : ℝ) : ℂ)) (Iic (2 * d)) :=
    hf_int.norm.mono'
      (((Complex.continuous_ofReal.comp_aestronglyMeasurable pkg.cutoffOm_measurable.aestronglyMeasurable).mul
        hf_int.aestronglyMeasurable).congr (ae_of_all _ fun X => by simp [Complex.ofReal_mul]))
      (ae_of_all _ fun X => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (abs_nonneg _) (pkg.cutoffOm_bound X))
  have hM_le : (∫ X in Iic (2 * d), ‖((pkg.cutoffOm X * pkg.f c X : ℝ) : ℂ)‖) ≤ pkg.M c :=
    (setIntegral_mono_on hcut_int.norm hf_int.norm measurableSet_Iic fun X _ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) (pkg.cutoffOm_bound X)).trans (pkg.M_spec hc)
  have hL2nn : 0 ≤ L ^ (-2 : ℝ) := Real.rpow_nonneg (hLmin.trans_le hL).le (-2 : ℝ)
  have hM2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM_le (mul_nonneg hC₀.le (inv_nonneg.mpr hc0))) hL2nn
  rw [norm_mul, show ‖(ceK : ℂ)‖ = ceK by simp [ceK_pos.le]]
  exact (mul_le_mul_of_nonneg_left (hom hc2 hL hcut_int) ceK_pos.le).trans
    ((mul_le_mul_of_nonneg_left hM2 ceK_pos.le).trans_eq (by ring))

private lemma rpow_neg_third_mul_le {C margin c : ℝ} (hC : 0 < C) (hm : 0 < margin)
    (hc : (C / margin) ^ (3 : ℝ) + 1 ≤ c) : C * c ^ (-(1 / 3 : ℝ)) ≤ margin := by
  have hc0 : 0 < c := by linarith [Real.rpow_nonneg (div_pos hC hm).le (3 : ℝ)]
  have h1 : C / margin < c ^ (1 / 3 : ℝ) := by
    calc C / margin = ((C / margin) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by rw [← Real.rpow_mul (by positivity)]; norm_num
      _ < c ^ (1 / 3 : ℝ) := Real.rpow_lt_rpow (by positivity) (by linarith) (by norm_num)
  rw [Real.rpow_neg hc0.le, ← div_eq_mul_inv]
  exact (div_le_iff₀ (by positivity)).mpr (by linarith [(div_lt_iff₀ hm).mp h1])

private lemma rpow_neg_third_le_of_cube_le {a c : ℝ} (ha : 0 ≤ a) (hc0 : 0 < c) (hac : a ^ 3 ≤ c) :
    a * c ^ (-(1 / 3 : ℝ)) ≤ 1 := by
  have ha_le : a ≤ c ^ (1 / 3 : ℝ) := by
    calc a = (a ^ 3) ^ (1 / 3 : ℝ) := by rw [← Real.rpow_natCast a 3, ← Real.rpow_mul ha]; norm_num
      _ ≤ c ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hac (by norm_num)
  rw [Real.rpow_neg hc0.le]; exact (mul_inv_le_iff₀ (by positivity)).mpr (by simpa using ha_le)

private lemma c_inv_le_neg_third {c : ℝ} (hc1 : 1 ≤ c) : c⁻¹ ≤ c ^ (-(1 / 3 : ℝ)) :=
  (Real.rpow_neg_one c).symm ▸ Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)

private lemma div_rpow_neg_three_halves {L cs : ℝ} (hL : 0 < L) (hcs : 0 < cs) :
    (L / cs) ^ (-(3 / 2 : ℝ)) = cs ^ (3 / 2 : ℝ) * L ^ (-(3 / 2 : ℝ)) := by
  rw [Real.rpow_neg (div_nonneg hL.le hcs.le), Real.div_rpow hL.le hcs.le, inv_div, div_eq_mul_inv,
    Real.rpow_neg hL.le, mul_comm]

private lemma inv_cs_div_rpow_three_halves {L : ℝ} (hL : 0 < L) :
    1 / ceCs / (L / ceCs) ^ (3 / 2 : ℝ) = Real.sqrt ceCs * L ^ (-(3 / 2 : ℝ)) := by
  have hcs_half : ceCs ^ (3 / 2 : ℝ) / ceCs = Real.sqrt ceCs := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add ceCs_pos,
      Real.rpow_one, mul_div_cancel_right₀ _ ceCs_pos.ne']
  rw [div_eq_mul_inv (1 / ceCs), ← Real.rpow_neg (div_nonneg hL.le ceCs_pos.le),
    div_rpow_neg_three_halves hL ceCs_pos, ← hcs_half]; ring

private lemma smooth_err_on_tail {L_base C_sm C_B0 c L : ℝ} (hLb : 0 < L_base) (hL : L_base ≤ L)
    (hc1 : 1 ≤ c) (hCsm : 0 < C_sm) {B0c : ℝ} (hB0_nn : 0 ≤ B0c) (hB0_bd : B0c ≤ C_B0)
    {E : ℂ} (hE : ‖E‖ ≤ C_sm * B0c *
      (c⁻¹ * L ^ (-2 : ℝ) + L ^ (-(3 / 2 : ℝ)) * ((c * L)⁻¹ + c ^ (-4 : ℝ) * L ^ (-5 : ℝ)))) :
    ‖E‖ ≤ C_sm * C_B0 * (L_base ^ (-(1 / 2 : ℝ)) + L_base⁻¹ + L_base ^ (-5 : ℝ)) *
      c ^ (-(1 / 3 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
  have hL0 : 0 < L := hLb.trans_le hL
  have hc_rpow : c⁻¹ ≤ c ^ (-(1 / 3 : ℝ)) := c_inv_le_neg_third hc1
  have hc4_rpow : c ^ (-4 : ℝ) ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hL2 : L ^ (-2 : ℝ) ≤ L_base ^ (-(1 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    rw [show (-2 : ℝ) = -(1 / 2 : ℝ) + -(3 / 2 : ℝ) by norm_num, Real.rpow_add hL0]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hLb hL (by norm_num)) (Real.rpow_nonneg hL0.le _)
  have ha : c⁻¹ * L ^ (-2 : ℝ) ≤ L_base ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * L ^ (-(3 / 2 : ℝ)) :=
    (mul_le_mul hc_rpow hL2 (Real.rpow_nonneg hL0.le _) (by positivity)).trans_eq (by ring)
  have hb1 : (c * L)⁻¹ ≤ L_base⁻¹ * c ^ (-(1 / 3 : ℝ)) := by
    rw [mul_inv, mul_comm (L_base⁻¹)]; exact mul_le_mul hc_rpow (inv_anti₀ hLb hL) (by positivity) (by positivity)
  have hb2 : c ^ (-4 : ℝ) * L ^ (-5 : ℝ) ≤ L_base ^ (-5 : ℝ) * c ^ (-(1 / 3 : ℝ)) :=
    (mul_le_mul hc4_rpow (Real.rpow_le_rpow_of_nonpos hLb hL (by norm_num))
      (Real.rpow_nonneg hL0.le _) (by positivity)).trans_eq (by ring)
  have hbracket : c⁻¹ * L ^ (-2 : ℝ) + L ^ (-(3 / 2 : ℝ)) * ((c * L)⁻¹ + c ^ (-4 : ℝ) * L ^ (-5 : ℝ)) ≤
      (L_base ^ (-(1 / 2 : ℝ)) + L_base⁻¹ + L_base ^ (-5 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (Real.rpow_nonneg hL0.le (-(3 / 2 : ℝ)))]
  calc ‖E‖ ≤ C_sm * B0c * _ := hE
    _ ≤ (C_sm * C_B0) * ((L_base ^ (-(1 / 2 : ℝ)) + L_base⁻¹ + L_base ^ (-5 : ℝ)) *
          c ^ (-(1 / 3 : ℝ)) * L ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hB0_bd hCsm.le) hbracket (by positivity) (mul_nonneg hCsm.le (hB0_nn.trans hB0_bd))
    _ = _ := by ring

/-- **Unconditional rescaled origin-mass bound `(cegt:GT3d)`:** from `twoScale_origin_mass`,
for `p ∈ (1/2, 1)`, `lam > 0`, `θ ≥ 0`, `γ ≥ 0`, there is `C_M > 0` such that for all `c ≥ 1`,
`f_c(X) = rescaledTail (twoScaleS p lam γ θ c) (c^{-1/3}) X` is integrable on `ℝ` and satisfies
`∫ X in Iic (2 * d), ‖(f_c X : ℂ)‖ ≤ C_M`. -/
theorem twoScaleS_rescaled_mass_bound {p lam γ θ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1)
    (hlam : 0 < lam) (hθ : 0 ≤ θ) (hγ : 0 ≤ γ) :
    ∃ C_M > 0, ∀ {c d : ℝ}, 1 ≤ c →
      Integrable (fun X : ℝ => (rescaledTail (twoScaleS p lam γ θ c) (c ^ (-(1 / 3 : ℝ))) X : ℂ)) ∧
        ∫ X in Iic (2 * d), ‖(rescaledTail (twoScaleS p lam γ θ c) (c ^ (-(1 / 3 : ℝ))) X : ℂ)‖ ≤ C_M := by
  obtain ⟨_, hS_props, ⟨C₁, hC₁, hS_bd⟩, _⟩ := twoScale_origin_mass hp hlam hθ hγ
  let A : ℝ := θ * fracJ2 p * Real.sqrt lam + γ * (1 + (-airyDerivFirstZero)); let C_M : ℝ := |A| + C₁ + 1
  refine ⟨C_M, by positivity, fun {c d} hc => ?_⟩
  have hc0 : 0 < c := by linarith
  let ε : ℝ := c ^ (-(1 / 3 : ℝ)); have hε0 : 0 < ε := by positivity
  obtain ⟨hS_nn, hS_int, _⟩ := hS_props hc0.le
  let α : ℝ := -(ε ^ 2)⁻¹; have hα : α ≠ 0 := by dsimp [α]; exact neg_ne_zero.mpr (inv_ne_zero (by positivity))
  have hres_eq : (fun X : ℝ => rescaledTail (twoScaleS p lam γ θ c) ε X) =
      fun X : ℝ => ε ^ (-3 : ℝ) * twoScaleS p lam γ θ c (α * X) := by ext X; unfold rescaledTail; congr 2; dsimp [α]; ring
  have hres_intR : Integrable (fun X : ℝ => rescaledTail (twoScaleS p lam γ θ c) ε X) :=
    hres_eq ▸ (hS_int.comp_mul_left' hα).const_mul _
  have hS_upper : ∫ u : ℝ, twoScaleS p lam γ θ c u ≤ (|A| + C₁) * ε := by
    have hc_p := Real.rpow_le_rpow_of_exponent_le hc (by linarith [hp.1] : -(2 * p / 3 : ℝ) ≤ -(1 / 3 : ℝ))
    have hsub := (abs_le.mp (hS_bd hc0)).2
    have hA : A * ε ≤ |A| * ε := mul_le_mul_of_nonneg_right (le_abs_self A) hε0.le
    calc ∫ u : ℝ, twoScaleS p lam γ θ c u ≤ A * ε + C₁ * c ^ (-(2 * p / 3 : ℝ)) := by linarith
      _ ≤ |A| * ε + C₁ * ε := by gcongr
      _ = (|A| + C₁) * ε := by ring
  have hfull : ∫ X : ℝ, rescaledTail (twoScaleS p lam γ θ c) ε X ≤ C_M := by
    have hα_abs : |α⁻¹| = ε ^ 2 := by rw [abs_inv]; dsimp [α]; rw [abs_neg, abs_inv, abs_of_pos (by positivity), inv_inv]
    have hε_pow : ε ^ (-3 : ℝ) * ε ^ 2 * ε = 1 := by
      rw [show ε ^ (-3 : ℝ) * ε ^ 2 * ε = ε ^ (-3 : ℝ) * (ε ^ ((2 : ℕ) : ℝ) * ε ^ (1 : ℝ)) by
        rw [Real.rpow_natCast, Real.rpow_one]; ring, ← Real.rpow_add hε0, ← Real.rpow_add hε0]; norm_num
    rw [hres_eq, integral_const_mul, Measure.integral_comp_mul_left (twoScaleS p lam γ θ c) α, smul_eq_mul, hα_abs]
    calc ε ^ (-3 : ℝ) * (ε ^ 2 * ∫ u : ℝ, twoScaleS p lam γ θ c u) ≤ ε ^ (-3 : ℝ) * (ε ^ 2 * ((|A| + C₁) * ε)) := by gcongr
      _ = (|A| + C₁) * (ε ^ (-3 : ℝ) * ε ^ 2 * ε) := by ring
      _ ≤ C_M := by rw [hε_pow, mul_one]; dsimp [C_M]; linarith
  have hres_nn : ∀ X : ℝ, 0 ≤ rescaledTail (twoScaleS p lam γ θ c) ε X := fun X => by
    unfold rescaledTail; exact mul_nonneg (Real.rpow_nonneg hε0.le _) (hS_nn _)
  refine ⟨Complex.ofRealCLM.integrable_comp hres_intR, ?_⟩
  rw [show (fun X : ℝ => ‖(rescaledTail (twoScaleS p lam γ θ c) ε X : ℂ)‖) =
      fun X : ℝ => rescaledTail (twoScaleS p lam γ θ c) ε X from funext fun X => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hres_nn X)]]
  exact (setIntegral_le_integral hres_intR (ae_of_all _ hres_nn)).trans hfull

/-- **Lemma `GT.3b` (`ce_o1_global_transfer.tex`, `(cegt:eqGT3b)`):** far-Fourier transfer for `S_c`
on `L ≥ L_F`, proving the asymptotic `(cegt:eqGT3b)` and `κ`-independent floor `b_F (1 + L)^{-3/2}`. -/
theorem gt3b_far_fourier_transfer {p lam θ κ L_F d : ℝ} {m : ℕ}
    (hp : 0 < p) (hlam : 0 < lam) (hθ : 0 < θ) (hκ : 0 < κ) (hm : 4 ≤ m)
    (hLF : 0 < L_F) (hd0 : 0 < d) (hd_lt : d < L_F / (8 * ceCs))
    (pkg : MacroscopicTransferPackage κ m L_F d)
    {C_M C_B0 C_B C_r0 : ℝ} (hCM : 0 < C_M) (hCB0 : 0 < C_B0) (hCB : 0 < C_B) (hCr0 : 0 < C_r0)
    (hM_bd : ∀ {c : ℝ}, pkg.c_T ≤ c → pkg.M c ≤ C_M)
    (hB0_bd : ∀ {c : ℝ}, pkg.c_T ≤ c → pkg.B0 c ≤ C_B0)
    (hB_bd : ∀ {c : ℝ}, pkg.c_T ≤ c → pkg.B c ≤ C_B * c ^ (-(1 / 3 : ℝ)))
    (hb0_eq : ∀ {c X : ℝ}, pkg.c_T ≤ c → L_F / ceCs ≤ X →
      |pkg.b0 c X - θ * movingDiagQ p (lam * X) / (π * X ^ (3 / 2 : ℝ))| ≤ C_r0 * c ^ (-(1 / 3 : ℝ)) * X ^ (-(3 / 2 : ℝ))) :
    let b_F : ℝ := ceK * θ * Real.sqrt ceCs * movingDiagQ p (lam * L_F / ceCs) / π
    0 < b_F ∧
    (∃ C_err > 0, ∀ {c L : ℝ}, pkg.c_T ≤ c → L_F ≤ L →
      |((ceK : ℂ) * mainTransferOp κ m c (fun X => (pkg.f c X : ℂ)) L).re -
          ceK * θ / (π * ceCs) * movingDiagQ p (lam * L / ceCs) / (L / ceCs) ^ (3 / 2 : ℝ)| ≤
        C_err * c ^ (-(1 / 3 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ))) ∧
    (∀ {L : ℝ}, L_F ≤ L → b_F * (1 + L) ^ (-(3 / 2 : ℝ)) ≤
        ceK * θ / (π * ceCs) * movingDiagQ p (lam * L / ceCs) / (L / ceCs) ^ (3 / 2 : ℝ)) ∧
    (∃ c₀ ≥ pkg.c_T, ∀ {c L : ℝ}, c₀ ≤ c → L_F ≤ L →
      (b_F / 2) * (1 + L) ^ (-(3 / 2 : ℝ)) ≤ ((ceK : ℂ) * mainTransferOp κ m c (fun X => (pkg.f c X : ℂ)) L).re) := by
  dsimp only
  have hQ_pos : 0 < movingDiagQ p (lam * L_F / ceCs) := by
    have ht : 0 < lam * L_F / ceCs := div_pos (mul_pos hlam hLF) ceCs_pos
    have hφ1 : ceVarphiP p (lam * L_F / ceCs) < 1 := by
      unfold ceVarphiP; exact inv_lt_one_of_one_lt₀ (by linarith [Real.rpow_pos_of_pos ht p])
    have hφ0 : 0 < ceVarphiP p (lam * L_F / ceCs) := by unfold ceVarphiP; positivity
    unfold movingDiagQ; nlinarith
  let b_F : ℝ := ceK * θ * Real.sqrt ceCs * movingDiagQ p (lam * L_F / ceCs) / π
  have hbF_pos : 0 < b_F := div_pos (mul_pos (mul_pos (mul_pos ceK_pos hθ) (Real.sqrt_pos.mpr ceCs_pos)) hQ_pos) Real.pi_pos
  obtain ⟨C_om, hCom, hEom⟩ := omitted_cutoff_bound hκ hm hLF hd0 hd_lt pkg
  let K_L : ℝ := (1 / L_F + 1) ^ (3 / 2 : ℝ); have hKL_pos : 0 < K_L := by positivity
  have hL_to_one_add : ∀ {L : ℝ}, L_F ≤ L → L ^ (-(3 / 2 : ℝ)) ≤ K_L * (1 + L) ^ (-(3 / 2 : ℝ)) := fun {L} hL => by
    have hL0 : 0 < L := hLF.trans_le hL
    have h1L : 1 + L ≤ (1 / L_F + 1) * L := by
      calc 1 + L = (1 / L + 1) * L := by field_simp [hL0.ne']
        _ ≤ (1 / L_F + 1) * L := mul_le_mul_of_nonneg_right (by linarith [one_div_le_one_div_of_le hLF hL]) hL0.le
    calc L ^ (-(3 / 2 : ℝ)) = K_L * ((1 / L_F + 1) * L) ^ (-(3 / 2 : ℝ)) := by
          rw [Real.mul_rpow (by positivity) hL0.le, ← mul_assoc,
            show K_L * (1 / L_F + 1) ^ (-(3 / 2 : ℝ)) = 1 by dsimp [K_L]; rw [← Real.rpow_add (by positivity)]; simp]; ring
      _ ≤ K_L * (1 + L) ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) h1L (by norm_num)) hKL_pos.le
  let C_err : ℝ := C_om * C_M * L_F ^ (-(1 / 2 : ℝ)) * K_L + pkg.C_sm * C_B0 * (L_F ^ (-(1 / 2 : ℝ)) + L_F⁻¹ + L_F ^ (-5 : ℝ)) * K_L +
    pkg.C_coh_glob * C_B + (ceK / ceCs) * C_r0 * ceCs ^ (3 / 2 : ℝ) * K_L + 1
  have hCerr : 0 < C_err := by have := pkg.hC_sm; have := pkg.hC_coh_glob; positivity [ceCs_pos, ceK_pos]
  have h_err_bd : ∀ {c L : ℝ}, pkg.c_T ≤ c → L_F ≤ L →
      |((ceK : ℂ) * mainTransferOp κ m c (fun X => (pkg.f c X : ℂ)) L).re -
          ceK * θ / (π * ceCs) * movingDiagQ p (lam * L / ceCs) / (L / ceCs) ^ (3 / 2 : ℝ)| ≤
        C_err * c ^ (-(1 / 3 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := fun {c L} hc hL => by
    have hc1 : 1 ≤ c := by linarith [pkg.hc_T]
    have hL0 : 0 < L := hLF.trans_le hL
    have hL2_bd : L ^ (-2 : ℝ) ≤ L_F ^ (-(1 / 2 : ℝ)) * K_L * (1 + L) ^ (-(3 / 2 : ℝ)) := by
      rw [show (-2 : ℝ) = -(1 / 2 : ℝ) + -(3 / 2 : ℝ) by norm_num, Real.rpow_add hL0]
      exact (mul_le_mul (Real.rpow_le_rpow_of_nonpos hLF hL (by norm_num)) (hL_to_one_add hL)
        (Real.rpow_nonneg hL0.le _) (by positivity)).trans_eq (by ring)
    have hEom_bd : ‖(ceK : ℂ) * (((c : ℂ) / (2 * π)) * ∫ X in Iic (2 * d), ((pkg.cutoffOm X * pkg.f c X : ℝ) : ℂ) *
        mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X))‖ ≤
        (C_om * C_M * L_F ^ (-(1 / 2 : ℝ)) * K_L) * c ^ (-(1 / 3 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
      have h1 := mul_le_mul (mul_le_mul_of_nonneg_left (c_inv_le_neg_third hc1) hCom.le)
        (hM_bd hc) (pkg.M_nonneg hc) (by positivity)
      exact (hEom hc hL).trans ((mul_le_mul h1 hL2_bd (Real.rpow_nonneg hL0.le _) (by positivity)).trans_eq (by ring))
    have hEsm_bd : ‖pkg.E_sm c L‖ ≤ (pkg.C_sm * C_B0 * (L_F ^ (-(1 / 2 : ℝ)) + L_F⁻¹ + L_F ^ (-5 : ℝ)) * K_L) *
        c ^ (-(1 / 3 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
      have h1 := smooth_err_on_tail hLF hL hc1 pkg.hC_sm (pkg.B0_nonneg hc) (hB0_bd hc) (pkg.smooth_bound hc hL)
      have hpre_nn : 0 ≤ pkg.C_sm * C_B0 * (L_F ^ (-(1 / 2 : ℝ)) + L_F⁻¹ + L_F ^ (-5 : ℝ)) * c ^ (-(1 / 3 : ℝ)) := by
        have := pkg.hC_sm; positivity
      exact h1.trans ((mul_le_mul_of_nonneg_left (hL_to_one_add hL) hpre_nn).trans_eq (by ring))
    have hCoh_bd : ‖pkg.T_plus c L + pkg.T_minus c L‖ ≤
        (pkg.C_coh_glob * C_B) * c ^ (-(1 / 3 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
      have hdiv : ‖pkg.T_plus c L + pkg.T_minus c L‖ ≤ pkg.C_coh_glob * pkg.B c * (1 + L) ^ (-(3 / 2 : ℝ)) := by
        rw [Real.rpow_neg (by linarith : 0 ≤ 1 + L), ← div_eq_mul_inv]
        exact (le_div_iff₀' (Real.rpow_pos_of_pos (by linarith) _)).mpr (pkg.coherent_global_bound hc hL)
      calc ‖pkg.T_plus c L + pkg.T_minus c L‖ ≤ pkg.C_coh_glob * pkg.B c * (1 + L) ^ (-(3 / 2 : ℝ)) := hdiv
        _ ≤ pkg.C_coh_glob * (C_B * c ^ (-(1 / 3 : ℝ))) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
            have := pkg.hC_coh_glob; have := hB_bd hc
            have := Real.rpow_nonneg (by linarith : 0 ≤ 1 + L) (-(3 / 2 : ℝ)); gcongr
        _ = _ := by ring
    have hb0_bd : |(ceK / ceCs * pkg.b0 c (L / ceCs)) -
        ceK * θ / (π * ceCs) * movingDiagQ p (lam * L / ceCs) / (L / ceCs) ^ (3 / 2 : ℝ)| ≤
        ((ceK / ceCs) * C_r0 * ceCs ^ (3 / 2 : ℝ) * K_L) * c ^ (-(1 / 3 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
      have hsub := hb0_eq hc (div_le_div_of_nonneg_right hL ceCs_pos.le)
      have heq : (ceK / ceCs * pkg.b0 c (L / ceCs)) -
          ceK * θ / (π * ceCs) * movingDiagQ p (lam * L / ceCs) / (L / ceCs) ^ (3 / 2 : ℝ) =
          (ceK / ceCs) * (pkg.b0 c (L / ceCs) - θ * movingDiagQ p (lam * (L / ceCs)) / (π * (L / ceCs) ^ (3 / 2 : ℝ))) := by
        rw [show lam * (L / ceCs) = lam * L / ceCs by ring]; ring
      rw [heq, abs_mul, abs_of_pos (div_pos ceK_pos ceCs_pos)]
      have h2 : C_r0 * c ^ (-(1 / 3 : ℝ)) * (L / ceCs) ^ (-(3 / 2 : ℝ)) ≤
          C_r0 * c ^ (-(1 / 3 : ℝ)) * (ceCs ^ (3 / 2 : ℝ) * (K_L * (1 + L) ^ (-(3 / 2 : ℝ)))) := by
        rw [div_rpow_neg_three_halves hL0 ceCs_pos]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hL_to_one_add hL) (by positivity [ceCs_pos]))
          (mul_nonneg hCr0.le (Real.rpow_nonneg (by linarith) _))
      exact (mul_le_mul_of_nonneg_left (hsub.trans h2) (div_pos ceK_pos ceCs_pos).le).trans_eq (by ring)
    have hdec := congrArg Complex.re (pkg.exact_decomp hc hL)
    simp only [Complex.add_re, Complex.ofReal_re] at hdec; rw [hdec]
    set lead := ceK * θ / (π * ceCs) * movingDiagQ p (lam * L / ceCs) / (L / ceCs) ^ (3 / 2 : ℝ)
    set A₀ := ceK / ceCs * pkg.b0 c (L / ceCs)
    set omC := (ceK : ℂ) * (((c : ℂ) / (2 * π)) * ∫ X in Iic (2 * d),
      ((pkg.cutoffOm X * pkg.f c X : ℝ) : ℂ) * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X))
    have htri : |A₀ + omC.re + (pkg.E_sm c L).re + (pkg.T_plus c L).re + (pkg.T_minus c L).re - lead| ≤
        |A₀ - lead| + ‖omC‖ + ‖pkg.E_sm c L‖ + ‖pkg.T_plus c L + pkg.T_minus c L‖ := by
      rw [show A₀ + omC.re + (pkg.E_sm c L).re + (pkg.T_plus c L).re + (pkg.T_minus c L).re - lead =
          (A₀ - lead) + omC.re + (pkg.E_sm c L).re + (pkg.T_plus c L + pkg.T_minus c L).re by simp only [Complex.add_re]; ring]
      have ha1 := abs_add_le ((A₀ - lead) + omC.re + (pkg.E_sm c L).re) (pkg.T_plus c L + pkg.T_minus c L).re
      have ha2 := abs_add_le ((A₀ - lead) + omC.re) (pkg.E_sm c L).re
      have ha3 := abs_add_le (A₀ - lead) omC.re
      linarith [Complex.abs_re_le_norm omC, Complex.abs_re_le_norm (pkg.E_sm c L),
        Complex.abs_re_le_norm (pkg.T_plus c L + pkg.T_minus c L)]
    have hεL : 0 ≤ c ^ (-(1 / 3 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
    have hfactor : (C_om * C_M * L_F ^ (-(1 / 2 : ℝ)) * K_L) * c ^ (-(1 / 3 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) +
        (pkg.C_sm * C_B0 * (L_F ^ (-(1 / 2 : ℝ)) + L_F⁻¹ + L_F ^ (-5 : ℝ)) * K_L) * c ^ (-(1 / 3 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) +
        (pkg.C_coh_glob * C_B) * c ^ (-(1 / 3 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) +
        ((ceK / ceCs) * C_r0 * ceCs ^ (3 / 2 : ℝ) * K_L) * c ^ (-(1 / 3 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) ≤
        C_err * c ^ (-(1 / 3 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by dsimp [C_err]; nlinarith
    linarith [htri, hb0_bd, hEom_bd, hEsm_bd, hCoh_bd, hfactor]
  have hfloor_mono : ∀ {L : ℝ}, L_F ≤ L →
      b_F * (1 + L) ^ (-(3 / 2 : ℝ)) ≤ ceK * θ / (π * ceCs) * movingDiagQ p (lam * L / ceCs) / (L / ceCs) ^ (3 / 2 : ℝ) := fun {L} hL => by
    have hL0 : 0 < L := hLF.trans_le hL
    have hq_mono : movingDiagQ p (lam * L_F / ceCs) ≤ movingDiagQ p (lam * L / ceCs) := by
      have ht1 : 0 < lam * L_F / ceCs := div_pos (mul_pos hlam hLF) ceCs_pos
      have ht2 : 0 ≤ lam * L / ceCs := div_nonneg (mul_nonneg hlam.le hL0.le) ceCs_pos.le
      have hpow : (lam * L_F / ceCs) ^ p ≤ (lam * L / ceCs) ^ p :=
        Real.rpow_le_rpow ht1.le (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL hlam.le) ceCs_pos.le) hp.le
      have hφ_le : ceVarphiP p (lam * L / ceCs) ≤ ceVarphiP p (lam * L_F / ceCs) := by
        unfold ceVarphiP; exact inv_anti₀ (by linarith [Real.rpow_pos_of_pos ht1 p]) (by linarith)
      have hφ0 : 0 ≤ ceVarphiP p (lam * L / ceCs) := by unfold ceVarphiP; exact inv_nonneg.mpr (by linarith [Real.rpow_nonneg ht2 p])
      unfold movingDiagQ; nlinarith
    have hL_pow := Real.rpow_le_rpow_of_nonpos hL0 (by linarith : L ≤ 1 + L) (by norm_num : -(3 / 2 : ℝ) ≤ 0)
    have hpre0 : 0 ≤ ceK * θ / π := div_nonneg (mul_nonneg ceK_pos.le hθ.le) Real.pi_pos.le
    have hpre2 := mul_le_mul (mul_le_mul_of_nonneg_left hq_mono hpre0) hL_pow (Real.rpow_nonneg (by linarith) _)
      (mul_nonneg hpre0 (hQ_pos.le.trans hq_mono))
    calc b_F * (1 + L) ^ (-(3 / 2 : ℝ))
        = (ceK * θ / π * movingDiagQ p (lam * L_F / ceCs)) * (1 + L) ^ (-(3 / 2 : ℝ)) * Real.sqrt ceCs := by dsimp [b_F]; ring
      _ ≤ (ceK * θ / π * movingDiagQ p (lam * L / ceCs)) * L ^ (-(3 / 2 : ℝ)) * Real.sqrt ceCs := mul_le_mul_of_nonneg_right hpre2 (Real.sqrt_nonneg _)
      _ = ceK * θ / (π * ceCs) * movingDiagQ p (lam * L / ceCs) / (L / ceCs) ^ (3 / 2 : ℝ) := by
            rw [mul_assoc _ (L ^ (-(3 / 2 : ℝ))) (Real.sqrt ceCs), mul_comm (L ^ (-(3 / 2 : ℝ))) (Real.sqrt ceCs),
              ← inv_cs_div_rpow_three_halves hL0]; ring
  refine ⟨hbF_pos, ⟨C_err, hCerr, h_err_bd⟩, hfloor_mono, max pkg.c_T ((C_err / (b_F / 2)) ^ (3 : ℝ) + 1), le_max_left _ _, fun {c L} hc hL => ?_⟩
  have hcerr := rpow_neg_third_mul_le hCerr (half_pos hbF_pos) ((le_max_right _ _).trans hc)
  have herr := (abs_le.mp (h_err_bd ((le_max_left _ _).trans hc) hL)).1
  have hfl := hfloor_mono hL
  linarith [mul_le_mul_of_nonneg_right hcerr (Real.rpow_nonneg (by linarith : 0 ≤ 1 + L) (-(3 / 2 : ℝ)))]

/-! ## Section 4: Section `GT.4` (`thm:ce-lift`) — Leading tip offset -/

private lemma cardinalTailSqSum_zero_one {p : ℝ} (hp : 0 < p) :
    cardinalTailSqSum p 0 1 = -airyDerivFirstZero - cohnC airyDerivFirstZero 0 ^ 2 := by
  have hDh0 : cardinalDh p 0 = 0 := by
    unfold cardinalDh
    simp_rw [fun n : ℕ => show cohnC airyDerivFirstZero (n + 1) ^ 2 * (1 - ceVarphiP p (0 * cohnE (n + 1)) ^ 2) = 0 from
      by unfold ceVarphiP; rw [zero_mul, Real.zero_rpow hp.ne']; ring]
    exact tsum_zero
  have hbounds := cardinalEtaHat_bounds hp le_rfl zero_le_one le_rfl; dsimp only at hbounds
  have hη0 : cardinalEtaHat p 0 1 = 0 := by
    have : (airyDerivFirstZero - airyZero 1) * (cardinalDh p 0 + (1 - 1 ^ 2) * (-airyDerivFirstZero)) = 0 := by rw [hDh0]; ring
    linarith [hbounds.2.1, hbounds.2.2]
  have hsqrt : Real.sqrt (-airyDerivFirstZero - cardinalTailSqSum p 0 1) = 1 / (airyDerivFirstZero - airyZero 1) := by linarith [hbounds.1, hη0]
  have hc1 : cohnC airyDerivFirstZero 0 ^ 2 = (1 / (airyDerivFirstZero - airyZero 1)) ^ 2 := by
    unfold cohnC; rw [show airyZero 1 - airyDerivFirstZero = -(airyDerivFirstZero - airyZero 1) by ring, inv_neg, neg_sq, one_div]
  have hsq : -airyDerivFirstZero - cardinalTailSqSum p 0 1 = cohnC airyDerivFirstZero 0 ^ 2 := by
    rw [← Real.sq_sqrt (cardinalB0_well_defined hp le_rfl zero_le_one le_rfl).2.1.le, hsqrt, ← hc1]
  linarith

private lemma cardinalB0_sq_sub_cohnC_sq_eq {p h σ : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    cardinalB p h σ 0 ^ 2 - cohnC airyDerivFirstZero 0 ^ 2 =
      (1 - σ ^ 2) * (-airyDerivFirstZero - cohnC airyDerivFirstZero 0 ^ 2) + σ ^ 2 * cardinalDh p h := by
  let s0 : ℕ → ℝ := fun n => cohnC airyDerivFirstZero (n + 1) ^ 2
  let s1 : ℕ → ℝ := fun n => (cohnC airyDerivFirstZero (n + 1) * ceVarphiP p (h * cohnE (n + 1))) ^ 2
  have hs0_sum : Summable s0 := ((hasSum_nat_add_iff' (f := fun n => cardinalB p 0 1 n ^ 2) 1).mpr
    (cardinalB0_well_defined hp le_rfl zero_le_one le_rfl).2.2.1).summable.congr fun n => by
      dsimp only [cardinalB, ceVarphiP, s0]; rw [one_mul, zero_mul, Real.zero_rpow hp.ne']; ring
  have hs0_tsum : ∑' n : ℕ, s0 n = -airyDerivFirstZero - cohnC airyDerivFirstZero 0 ^ 2 := by
    rw [← cardinalTailSqSum_zero_one hp]; unfold cardinalTailSqSum
    exact tsum_congr fun n => by dsimp only [ceVarphiP, s0]; rw [one_mul, zero_mul, Real.zero_rpow hp.ne']; ring
  have hs1_sum : Summable s1 := ((hasSum_nat_add_iff' (f := fun n => cardinalB p h 1 n ^ 2) 1).mpr
    (cardinalB0_well_defined hp hh zero_le_one le_rfl).2.2.1).summable.congr fun n => by dsimp only [cardinalB, s1]; rw [one_mul]
  have htail_eq : cardinalTailSqSum p h σ = σ ^ 2 * ∑' n : ℕ, s1 n := by
    unfold cardinalTailSqSum; rw [← tsum_mul_left]; exact tsum_congr fun n => by dsimp [s1]; ring
  have hDh_eq : cardinalDh p h = ∑' n : ℕ, s0 n - ∑' n : ℕ, s1 n := by
    rw [← hs0_sum.tsum_sub hs1_sum]; unfold cardinalDh; exact tsum_congr fun n => by dsimp [s0, s1]; ring
  have hb0_sq : cardinalB p h σ 0 ^ 2 = -airyDerivFirstZero - cardinalTailSqSum p h σ := by
    change (-Real.sqrt (-airyDerivFirstZero - cardinalTailSqSum p h σ)) ^ 2 = _
    rw [neg_sq, Real.sq_sqrt (cardinalB0_well_defined hp hh hσ0 hσ1).2.1.le]
  rw [hb0_sq, htail_eq, show ∑' n : ℕ, s1 n = (-airyDerivFirstZero - cohnC airyDerivFirstZero 0 ^ 2) - cardinalDh p h
    by linarith [hs0_tsum, hDh_eq]]; ring

/-- **Unconditional exact leading tip offset (`GT.4`):**
`cardinalB p h σ 0 ^ 2 - cohnC airyDerivFirstZero 0 ^ 2 = (R (M - c₁²) + fracJ2 p √lam) ε + O(ε^{2p})`. -/
theorem cardinal_b1_sq_sub_c1_sq_asymptotic {p lam R : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1)
    (hlam : 0 < lam) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ {c : ℝ}, max 1 (R ^ 3) ≤ c →
      let ε : ℝ := c ^ (-(1 / 3 : ℝ)); let M : ℝ := -airyDerivFirstZero; let c₁ : ℝ := cohnC airyDerivFirstZero 0
      |cardinalB p (lam * ε ^ 2) (Real.sqrt (1 - R * ε)) 0 ^ 2 - c₁ ^ 2 -
          (R * (M - c₁ ^ 2) + fracJ2 p * Real.sqrt lam) * ε| ≤ C * ε ^ (2 * p) := by
  obtain ⟨C_D, hCD, hDh_bd⟩ := cardinalDh_asymptotic_pos hp
  have hp0 : 0 < p := by linarith [hp.1]
  have hJ2_nn : 0 ≤ fracJ2 p := (fracJ2_pos hp.1).le
  let J : ℝ := fracJ2 p * Real.sqrt lam; let C : ℝ := C_D * lam ^ p + R * (C_D * lam ^ p + J) + 1
  refine ⟨C, by positivity, fun {c} hc => ?_⟩; dsimp only
  have hc1 : 1 ≤ c := (le_max_left _ _).trans hc; have hc0 : 0 < c := by linarith
  let ε : ℝ := c ^ (-(1 / 3 : ℝ)); have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have hRε : R * ε ≤ 1 := rpow_neg_third_le_of_cube_le hR hc0 ((le_max_right _ _).trans hc)
  have hh0 : 0 < lam * ε ^ 2 := by positivity
  let σ : ℝ := Real.sqrt (1 - R * ε)
  have h_exact : cardinalB p (lam * ε ^ 2) σ 0 ^ 2 - cohnC airyDerivFirstZero 0 ^ 2 =
      R * ε * (-airyDerivFirstZero - cohnC airyDerivFirstZero 0 ^ 2) + (1 - R * ε) * cardinalDh p (lam * ε ^ 2) := by
    have h1 := cardinalB0_sq_sub_cohnC_sq_eq (σ := σ) hp0 hh0.le (Real.sqrt_nonneg _)
      (Real.sqrt_le_one.mpr (by linarith [mul_nonneg hR hε0.le]))
    rw [Real.sq_sqrt (by linarith), show 1 - (1 - R * ε) = R * ε by ring] at h1; exact h1
  have hDh_est : |cardinalDh p (lam * ε ^ 2) - J * ε| ≤ (C_D * lam ^ p) * ε ^ (2 * p) := by
    have h0 := hDh_bd hh0
    rw [Real.sqrt_mul hlam.le, Real.sqrt_sq hε0.le, Real.mul_rpow hlam.le (sq_nonneg ε),
      ← Real.rpow_natCast ε 2, ← Real.rpow_mul hε0.le, show ((2 : ℕ) : ℝ) * p = 2 * p by simp] at h0
    simpa [J, mul_assoc] using h0
  have hε_2p_le_ε : ε ^ (2 * p) ≤ ε := by
    conv_rhs => rw [← Real.rpow_one ε]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by linarith [hp.1])
  have hε_2_le_2p : ε ^ 2 ≤ ε ^ (2 * p) := by
    rw [← Real.rpow_natCast ε 2]; exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num; linarith [hp.2])
  have hDh_abs : |cardinalDh p (lam * ε ^ 2)| ≤ (C_D * lam ^ p + J) * ε := by
    have hJnn : 0 ≤ J := mul_nonneg hJ2_nn (Real.sqrt_nonneg _)
    calc |cardinalDh p (lam * ε ^ 2)| ≤ |cardinalDh p (lam * ε ^ 2) - J * ε| + |J * ε| := by
          simpa using abs_add_le (cardinalDh p (lam * ε ^ 2) - J * ε) (J * ε)
      _ ≤ (C_D * lam ^ p) * ε ^ (2 * p) + J * ε := by rw [abs_of_nonneg (mul_nonneg hJnn hε0.le)]; gcongr
      _ ≤ (C_D * lam ^ p + J) * ε := by linarith [mul_le_mul_of_nonneg_left hε_2p_le_ε (by positivity : 0 ≤ C_D * lam ^ p)]
  change |cardinalB p (lam * ε ^ 2) σ 0 ^ 2 - cohnC airyDerivFirstZero 0 ^ 2 -
      (R * (-airyDerivFirstZero - cohnC airyDerivFirstZero 0 ^ 2) + J) * ε| ≤ C * ε ^ (2 * p)
  rw [h_exact]
  calc |R * ε * (-airyDerivFirstZero - cohnC airyDerivFirstZero 0 ^ 2) +
          (1 - R * ε) * cardinalDh p (lam * ε ^ 2) -
          (R * (-airyDerivFirstZero - cohnC airyDerivFirstZero 0 ^ 2) + J) * ε|
      = |(cardinalDh p (lam * ε ^ 2) - J * ε) + (-(R * ε * cardinalDh p (lam * ε ^ 2)))| := by congr 1; ring
    _ ≤ |cardinalDh p (lam * ε ^ 2) - J * ε| + |-(R * ε * cardinalDh p (lam * ε ^ 2))| := abs_add_le _ _
    _ ≤ (C_D * lam ^ p) * ε ^ (2 * p) + R * ε * ((C_D * lam ^ p + J) * ε) := by
          rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hR, abs_of_pos hε0]; gcongr
    _ = (C_D * lam ^ p) * ε ^ (2 * p) + R * (C_D * lam ^ p + J) * ε ^ 2 := by ring
    _ ≤ C * ε ^ (2 * p) := by
          have := mul_le_mul_of_nonneg_left hε_2_le_2p (by positivity : 0 ≤ R * (C_D * lam ^ p + J))
          have h1 : 0 ≤ ε ^ (2 * p) := Real.rpow_nonneg hε0.le _; dsimp [C]; linarith

private lemma airyAi'_airyZero_one_ne : airyAi' (airyZero 1) ≠ 0 :=
  fun h => airyAi_ne_zero_of_deriv_zero h (airyAi_airyZero 1)

private lemma cohnL_at_a1_succ (n : ℕ) : cohnL (n + 1) (airyZero 1) = 0 := by
  rw [cohnL_of_ne (airyZero_lt_of_lt le_rfl (by omega : 1 < n + 2)).ne', airyAi_airyZero 1, zero_div]

private lemma twoScaleQ0_at_a1 (p lam R c : ℝ) :
    twoScaleQ0 p lam R c (airyZero 1) =
      (cohnC airyDerivFirstZero 0 ^ 2 -
        cardinalB p (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2) (Real.sqrt (1 - R * c ^ (-(1 / 3 : ℝ)))) 0 ^ 2) * airyAi' (airyZero 1) ^ 2 := by
  unfold twoScaleQ0 cardinalQ
  have hf1 : ceF1 (airyZero 1) = 0 := by unfold ceF1; rw [airyAi_airyZero 1, zero_mul]
  have hgd : ceG1Deriv airyDerivFirstZero (airyZero 1) = airyAi' (airyZero 1) ^ 2 * cohnC airyDerivFirstZero 0 ^ 2 := by
    unfold ceG1Deriv cohnC; rw [dslope_of_ne _ airyDerivFirstZero_spec.1.ne, slope_def_field, airyDerivFirstZero_spec.2.2, sub_zero]; ring
  have hH : cardinalH p (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2) (Real.sqrt (1 - R * c ^ (-(1 / 3 : ℝ)))) (airyZero 1) =
      cardinalB p (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2) (Real.sqrt (1 - R * c ^ (-(1 / 3 : ℝ)))) 0 * airyAi' (airyZero 1) := by
    unfold cardinalH; rw [tsum_eq_single 0]
    · exact congrArg _ (cohnL_self 0)
    · intro n hn; cases n with | zero => exact (hn rfl).elim | succ m => rw [cohnL_at_a1_succ m, mul_zero]
  unfold cardinalP; rw [hf1, hgd, hH]; ring

private lemma twoScaleS_at_a1 {p : ℝ} (hp : 0 < p) (lam γ θ c : ℝ) :
    twoScaleS p lam γ θ c (airyZero 1) = γ * c ^ (-(1 / 3 : ℝ)) * (1 + cohnC airyDerivFirstZero 0 ^ 2) * airyAi' (airyZero 1) ^ 2 := by
  unfold twoScaleS
  have hS_zero : movingDiagS p (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2) (airyZero 1) = 0 := by
    unfold movingDiagS
    simp_rw [fun n : ℕ => show cohnC airyDerivFirstZero n ^ 2 *
        (1 - ceVarphiP p (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2 * cohnE n) ^ 2) * cohnL n (airyZero 1) ^ 2 = 0 from by
      cases n with | zero => unfold cohnE ceVarphiP; rw [sub_self, mul_zero, Real.zero_rpow hp.ne']; ring | succ m => rw [cohnL_at_a1_succ m]; ring]
    exact tsum_zero
  have hS0 : ceS0 (airyZero 1) airyDerivFirstZero (airyZero 1) = (1 + cohnC airyDerivFirstZero 0 ^ 2) * airyAi' (airyZero 1) ^ 2 := by
    unfold ceS0 ceG1 ceG1Deriv cohnC
    rw [dslope_same, (hasDerivAt_airyAi (airyZero 1)).deriv, dslope_of_ne _ airyDerivFirstZero_spec.1.ne,
      slope_def_field, airyDerivFirstZero_spec.2.2, sub_zero]; ring
  rw [hS_zero, mul_zero, zero_add, hS0]; ring

/-- **Unconditional untuned tip offset (`GT.4`):**
`twoScaleF0 p lam γ θ R c (airyZero 1) / (2 * airyAi' (airyZero 1) ^ 2) = -(R(M - c₁²) + fracJ2 p √lam + (γ/2)(1 + c₁²)) ε + O(ε^{2p})`. -/
theorem twoScaleF0_at_a1_asymptotic {p lam R : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1)
    (hlam : 0 < lam) (hR : 0 ≤ R) (γ θ : ℝ) :
    ∃ C > 0, ∀ {c : ℝ}, max 1 (R ^ 3) ≤ c →
      let ε : ℝ := c ^ (-(1 / 3 : ℝ)); let M : ℝ := -airyDerivFirstZero; let c₁ : ℝ := cohnC airyDerivFirstZero 0
      |twoScaleF0 p lam γ θ R c (airyZero 1) / (2 * airyAi' (airyZero 1) ^ 2) -
          (-(R * (M - c₁ ^ 2) + fracJ2 p * Real.sqrt lam + (γ / 2) * (1 + c₁ ^ 2)) * ε)| ≤ C * ε ^ (2 * p) := by
  obtain ⟨C, hC, hbd⟩ := cardinal_b1_sq_sub_c1_sq_asymptotic hp hlam hR
  refine ⟨C, hC, fun {c} hc => ?_⟩
  have hF0_eq : twoScaleF0 p lam γ θ R c (airyZero 1) / (2 * airyAi' (airyZero 1) ^ 2) =
      -(cardinalB p (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2) (Real.sqrt (1 - R * c ^ (-(1 / 3 : ℝ)))) 0 ^ 2 -
          cohnC airyDerivFirstZero 0 ^ 2) - (γ / 2) * (1 + cohnC airyDerivFirstZero 0 ^ 2) * c ^ (-(1 / 3 : ℝ)) := by
    unfold twoScaleF0; rw [twoScaleQ0_at_a1, twoScaleS_at_a1 (by linarith [hp.1])]; field_simp [airyAi'_airyZero_one_ne]; ring
  rw [hF0_eq]; have hsub := hbd hc; dsimp only at hsub ⊢
  rw [show -(cardinalB p (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2) (Real.sqrt (1 - R * c ^ (-(1 / 3 : ℝ)))) 0 ^ 2 - cohnC airyDerivFirstZero 0 ^ 2) -
      (γ / 2) * (1 + cohnC airyDerivFirstZero 0 ^ 2) * c ^ (-(1 / 3 : ℝ)) - -(R * (-airyDerivFirstZero - cohnC airyDerivFirstZero 0 ^ 2) +
      fracJ2 p * Real.sqrt lam + γ / 2 * (1 + cohnC airyDerivFirstZero 0 ^ 2)) * c ^ (-(1 / 3 : ℝ)) =
      -(cardinalB p (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2) (Real.sqrt (1 - R * c ^ (-(1 / 3 : ℝ)))) 0 ^ 2 - cohnC airyDerivFirstZero 0 ^ 2 -
      (R * (-airyDerivFirstZero - cohnC airyDerivFirstZero 0 ^ 2) + fracJ2 p * Real.sqrt lam) * c ^ (-(1 / 3 : ℝ))) by ring, abs_neg]
  exact hsub

/-- Exact algebraic identity at `u = airyZero 1` between `twoScaleFc` and `twoScaleF0`. -/
lemma twoScaleFc_at_a1_exact_diff (p lam γ θ R Mpsi c : ℝ) :
    twoScaleFc p lam γ θ R Mpsi c (airyZero 1) / (2 * airyAi' (airyZero 1) ^ 2) =
      twoScaleF0 p lam γ θ R c (airyZero 1) / (2 * airyAi' (airyZero 1) ^ 2) + twoScaleEta p lam R Mpsi c := by
  unfold twoScaleFc twoScaleQc twoScaleF0
  have hg1 : ceG1 (airyZero 1) (airyZero 1) = airyAi' (airyZero 1) ^ 2 := by unfold ceG1; rw [dslope_same, (hasDerivAt_airyAi (airyZero 1)).deriv]
  rw [hg1]; field_simp [airyAi'_airyZero_one_ne]; ring

/-- **Origin-tuned tip offset (`GT.4`):**
`twoScaleFc p lam γ θ R (Mpsi c) c (airyZero 1) / (2 * airyAi' (airyZero 1) ^ 2) = -(R(M - c₁²) + fracJ2 p √lam + (γ/2)(1 + c₁²)) ε + O(ε^{2p})`. -/
theorem twoScaleFc_at_a1_asymptotic {p lam R : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1)
    (hlam : 0 < lam) (hR : 0 ≤ R) (γ θ : ℝ) {Mpsi : ℝ → ℝ} {c₁ C_Q : ℝ} (hC_Q : 0 < C_Q)
    (hMpsi : ∀ {c : ℝ}, c₁ ≤ c → 0 < Mpsi c ∧ Mpsi c ≤ 1)
    (hQ0_lap : ∀ {c : ℝ}, c₁ ≤ c → |airyTwistedLaplace (twoScaleQ0 p lam R c) (ceCs * c ^ (1 / 3 : ℝ))| ≤ C_Q * c ^ (-(5 / 6 : ℝ))) :
    ∃ c_min ≥ max 1 (R ^ 3), ∃ C > 0, ∀ {c : ℝ}, c_min ≤ c →
      let ε : ℝ := c ^ (-(1 / 3 : ℝ)); let M : ℝ := -airyDerivFirstZero; let c_node : ℝ := cohnC airyDerivFirstZero 0
      |twoScaleFc p lam γ θ R (Mpsi c) c (airyZero 1) / (2 * airyAi' (airyZero 1) ^ 2) -
          (-(R * (M - c_node ^ 2) + fracJ2 p * Real.sqrt lam + (γ / 2) * (1 + c_node ^ 2)) * ε)| ≤ C * ε ^ (2 * p) := by
  obtain ⟨C₀, hC₀, hF0⟩ := twoScaleF0_at_a1_asymptotic hp hlam hR γ θ
  obtain ⟨C_g, hCg, hg_lap⟩ := airyTwistedLaplace_ceG1_bound
  let c_lap : ℝ := max (max 1 c₁) ((2 * C_g / ceK) ^ (6 / 5 : ℝ) + 1); let C_eta : ℝ := 2 * C_Q / ceK
  refine ⟨max c_lap (max 1 (R ^ 3)), le_max_right _ _, C₀ + C_eta, by positivity [ceK_pos], fun {c} hc => ?_⟩
  have hc_lap := (le_max_left _ _).trans hc; have hc_R3 := (le_max_right _ _).trans hc
  have hc_c₁ : c₁ ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc_lap
  have hc1 : 1 ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc_lap
  have hc0 : 0 < c := by linarith
  have hM := hMpsi hc_c₁; have hg := hg_lap (by positivity : 0 ≤ c ^ (1 / 3 : ℝ))
  have hg_le : airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * c ^ (1 / 3 : ℝ)) ≤ ceK / 2 := by
    have hgt : (2 * C_g / ceK) ^ (6 / 5 : ℝ) < c := lt_of_lt_of_le (by linarith) ((le_max_right _ _).trans hc_lap)
    have hpow : (1 + c ^ (1 / 3 : ℝ)) ^ (-(5 / 2 : ℝ)) ≤ c ^ (-(5 / 6 : ℝ)) :=
      (Real.rpow_le_rpow_of_nonpos (by positivity) (le_add_of_nonneg_left zero_le_one) (by norm_num)).trans_eq
        (by rw [← Real.rpow_mul hc0.le]; norm_num)
    have hc56 : 2 * C_g / ceK < c ^ (5 / 6 : ℝ) := by
      calc 2 * C_g / ceK = ((2 * C_g / ceK) ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) := by rw [← Real.rpow_mul (by positivity [ceK_pos])]; norm_num
        _ < c ^ (5 / 6 : ℝ) := Real.rpow_lt_rpow (by positivity [ceK_pos]) hgt (by norm_num)
    have hCg_bd : C_g * c ^ (-(5 / 6 : ℝ)) ≤ ceK / 2 := by
      rw [Real.rpow_neg hc0.le, ← div_eq_mul_inv]; exact (div_le_iff₀ (by positivity)).mpr (by linarith [(div_lt_iff₀ ceK_pos).mp hc56])
    exact (hg.2.trans (mul_le_mul_of_nonneg_left hpow hCg.le)).trans hCg_bd
  have hden_ge : ceK / 2 ≤ ceK - Mpsi c * airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * c ^ (1 / 3 : ℝ)) := by
    linarith [mul_le_mul hM.2 hg_le hg.1 zero_le_one]
  have hη_bd : |twoScaleEta p lam R (Mpsi c) c| ≤ C_eta * (c ^ (-(1 / 3 : ℝ))) ^ (2 * p) := by
    have heta_56 : |twoScaleEta p lam R (Mpsi c) c| ≤ C_eta * c ^ (-(5 / 6 : ℝ)) := by
      unfold twoScaleEta; rw [abs_div, abs_mul, abs_of_pos hM.1, abs_of_pos (lt_of_lt_of_le (by positivity [ceK_pos]) hden_ge)]
      calc Mpsi c * |airyTwistedLaplace (twoScaleQ0 p lam R c) (ceCs * c ^ (1 / 3 : ℝ))| /
            (ceK - Mpsi c * airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * c ^ (1 / 3 : ℝ)))
          ≤ 1 * (C_Q * c ^ (-(5 / 6 : ℝ))) / (ceK / 2) :=
            div_le_div₀ (by positivity) (mul_le_mul hM.2 (hQ0_lap hc_c₁) (abs_nonneg _) zero_le_one) (by positivity [ceK_pos]) hden_ge
        _ = C_eta * c ^ (-(5 / 6 : ℝ)) := by dsimp [C_eta]; ring
    have hε_le : c ^ (-(5 / 6 : ℝ)) ≤ (c ^ (-(1 / 3 : ℝ))) ^ (2 * p) := by
      rw [← Real.rpow_mul hc0.le]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by linarith [hp.2])
    exact heta_56.trans (mul_le_mul_of_nonneg_left hε_le (by positivity [ceK_pos]))
  rw [twoScaleFc_at_a1_exact_diff]; have hF0c := hF0 hc_R3; dsimp only at hF0c ⊢
  set target := -(R * (-airyDerivFirstZero - cohnC airyDerivFirstZero 0 ^ 2) +
    fracJ2 p * Real.sqrt lam + γ / 2 * (1 + cohnC airyDerivFirstZero 0 ^ 2)) * c ^ (-(1 / 3 : ℝ))
  calc |twoScaleF0 p lam γ θ R c (airyZero 1) / (2 * airyAi' (airyZero 1) ^ 2) + twoScaleEta p lam R (Mpsi c) c - target|
      = |(twoScaleF0 p lam γ θ R c (airyZero 1) / (2 * airyAi' (airyZero 1) ^ 2) - target) + twoScaleEta p lam R (Mpsi c) c| := by congr 1; ring
    _ ≤ |twoScaleF0 p lam γ θ R c (airyZero 1) / (2 * airyAi' (airyZero 1) ^ 2) - target| + |twoScaleEta p lam R (Mpsi c) c| := abs_add_le _ _
    _ ≤ (C₀ + C_eta) * (c ^ (-(1 / 3 : ℝ))) ^ (2 * p) := by linarith

/-! ## Section 5: Axiom hygiene guards -/

/-- info: 'FormalResearch.CohnElkies.norm_mainEdgeAmp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.norm_mainEdgeAmp_le
/-- info: 'FormalResearch.CohnElkies.fourierPaperL2_ae_eq_fourierPaper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.fourierPaperL2_ae_eq_fourierPaper
/-- info: 'FormalResearch.CohnElkies.mainTransferOp_eq_fourier_multiplier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.mainTransferOp_eq_fourier_multiplier
/-- info: 'FormalResearch.CohnElkies.mainTransferOp_sup_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.mainTransferOp_sup_norm_le
/-- info: 'FormalResearch.CohnElkies.omittedRegion_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.omittedRegion_bound
/-- info: 'FormalResearch.CohnElkies.macroscopicTransferPackage_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.macroscopicTransferPackage_nonvacuous
/-- info: 'FormalResearch.CohnElkies.twoScaleS_rescaled_mass_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.twoScaleS_rescaled_mass_bound
/-- info: 'FormalResearch.CohnElkies.gt3b_far_fourier_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.gt3b_far_fourier_transfer
/-- info: 'FormalResearch.CohnElkies.cardinal_b1_sq_sub_c1_sq_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.cardinal_b1_sq_sub_c1_sq_asymptotic
/-- info: 'FormalResearch.CohnElkies.twoScaleF0_at_a1_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.twoScaleF0_at_a1_asymptotic
/-- info: 'FormalResearch.CohnElkies.twoScaleFc_at_a1_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.twoScaleFc_at_a1_asymptotic

end FormalResearch.CohnElkies

end
