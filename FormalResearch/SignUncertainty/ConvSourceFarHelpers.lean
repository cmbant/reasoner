module

public import FormalResearch.CohnElkies.PhysicalAndFarTransfer
public import FormalResearch.CohnElkies.MellinLiftIntegrals
public import FormalResearch.SignUncertainty.ConvSourceG1

/-!
# Analytical helpers for far-range transfer of the convolution source (`S3a`)

Reference: `CFT/sign_uncertainty/paper/ce_o1_global_transfer.tex` (`ceo:conv` (7)) and
`ce_physical_log_far.tex`.

Provides:
* `iMain_eq_mainTransferOp`: exact identity `c ξ I_main[F](ξ) = ceK · mainTransferOp κ m c (rescaledTail F ε) L`;
* `mainTransferOp_split_error`: uniform `O(c⁻¹ L⁻² ‖f‖₁ + c^{1/2} B_tail)` error estimate via `X ≤ a L` vs `X > a L`;
* `realConv`, `integrable_realConv`, `weakDerivL2_realConv`, `fourierPaper_realConv`: `L¹ ∩ H¹` convolution tools;
* `mainTransferOp_fourier_approx`: Plancherel + Cauchy–Schwarz error bound between `mainTransferOp κ m c (g * ρ_ε) L`
  and `ceCs⁻¹ g(L / ceCs)`.
-/

@[expose] public section

noncomputable section

open Real Complex MeasureTheory Set Filter
open FormalResearch.Special FormalResearch.Asymptotics
open scoped FourierTransform BigOperators Topology Convolution Pointwise

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-! ### 1. Exact identity between `iMain` and `mainTransferOp` -/

/-- Exact Fubini transfer identity for `I_main[F]`: for `F ∈ L¹(ℝ)`, `κ > 0`, `m ≥ 1`, `c ≥ 1`, `ξ > 0`,
`c ξ I_main[F](ξ) = ceK · mainTransferOp κ m c (rescaledTail F ε) L` where `ε = c^{-1/3}` and `L = log(π² ξ)`. -/
theorem iMain_eq_mainTransferOp {F : ℝ → ℝ} (hF : Integrable F)
    {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 1 ≤ m) {c ξ : ℝ} (hc : 1 ≤ c) (hξ : 0 < ξ) :
    (c : ℂ) * (ξ : ℂ) * iMain F (κ * liftEps c) m c ξ =
      (ceK : ℂ) * mainTransferOp κ m c (fun X => (rescaledTail F (liftEps c) X : ℂ)) (Real.log (Real.pi ^ 2 * ξ)) := by
  have hc0 : 0 < c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have ha1 : Integrable (mainEdgeAmp κ m c) := integrable_mainEdgeAmp hκ hm hc
  let L : ℝ := Real.log (Real.pi ^ 2 * ξ)
  have hfub := mainEdge_fubini_kernel hF ha1 hc0 L (ceK : ℂ)
  dsimp only at hfub
  have hbridge : ∀ τ : ℝ,
      iMainIntegrand F (κ * liftEps c) m c ξ ((liftEps c)⁻¹ * τ) =
        mainEdgeAmp κ m c τ *
          Complex.exp (Complex.I * (c : ℂ) * ((L * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ : ℝ) : ℂ)) *
            ((ceK : ℂ) * Complex.exp (Complex.I * (((ceCs * τ / liftEps c : ℝ) ^ 3 / 12 : ℝ) : ℂ)) *
              ∫ u : ℝ, (F u : ℂ) * Complex.exp (Complex.I * (((ceCs * τ / liftEps c) * u : ℝ) : ℂ))) := by
    intro τ
    unfold iMainIntegrand liftSymbol
    have hmul_eps : liftEps c * ((liftEps c)⁻¹ * τ) = τ := by field_simp [hε0.ne']
    have hlift_m : liftMultiplier (κ * liftEps c) m (((liftEps c)⁻¹ * τ : ℝ) * Complex.I) =
        bsplineImag (ceCs * κ / m) m τ := by
      unfold liftMultiplier bsplineImag
      congr 2
      push_cast
      field_simp [hε0.ne']
    rw [hmul_eps, hlift_m]
    obtain ⟨hK_eq, hF_eq⟩ := mainEdge_mellinK0_airyFtilde_bridge (κ := κ) (c := c) (m := m) hξ F τ
    have heps : liftEps c = c ^ (-(1 / 3 : ℝ)) := rfl
    have hce : (c ^ (-(1 / 3 : ℝ))) ≠ 0 := by rw [← heps]; exact hε0.ne'
    have hF_bridge : airyTwistedLaplaceC F ((ceCs : ℂ) * (((liftEps c)⁻¹ * τ : ℝ) * Complex.I)) =
        airyFtilde (fun z : ℂ => (F z.re : ℂ)) (-((ceCs * τ / c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)) := by
      simp only [airyTwistedLaplaceC, airyFtilde, airyFhat, airyPhiK]
      have hi3 : (Complex.I : ℂ) ^ 3 = -Complex.I := by
        calc (Complex.I : ℂ) ^ 3 = Complex.I ^ 2 * Complex.I := by ring
          _ = -Complex.I := by rw [Complex.I_sq]; ring
      have hpow3 : -(((ceCs : ℂ) * (((liftEps c)⁻¹ * τ : ℝ) * Complex.I)) ^ 3) / 12 =
          -(Complex.I * (-(((ceCs * τ / c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ))) ^ 3 / 12) := by
        rw [heps]
        push_cast
        rw [mul_pow, mul_pow, mul_pow, hi3]
        field_simp [hce]
      have hint_eq : (∫ u : ℝ, (F u : ℂ) * Complex.exp ((ceCs : ℂ) * (((liftEps c)⁻¹ * τ : ℝ) * Complex.I) * (u : ℂ))) =
          ∫ u : ℝ, ((fun z : ℂ => (F z.re : ℂ)) (u : ℂ)) *
            Complex.exp (-(Complex.I * (-((ceCs * τ / c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)) * (u : ℂ))) := by
        congr 1; funext u
        simp only [Complex.ofReal_re]
        congr 2
        rw [heps]; push_cast; field_simp [hce]
      rw [hpow3, hint_eq]
      rfl
    rw [hF_bridge, hF_eq]
    simp only [← heps]
    calc (mellinK0 c ((τ : ℂ) * Complex.I) ξ *
            (bsplineImag (ceCs * κ / m) m τ *
              ((ceK : ℂ) * Complex.exp (Complex.I * (((ceCs * τ / liftEps c : ℝ) ^ 3 / 12 : ℝ) : ℂ)) *
                ∫ u : ℝ, (F u : ℂ) * Complex.exp (Complex.I * (((ceCs * τ / liftEps c) * u : ℝ) : ℂ)))))
        = (mellinK0 c ((τ : ℂ) * Complex.I) ξ * bsplineImag (ceCs * κ / m) m τ) *
            ((ceK : ℂ) * Complex.exp (Complex.I * (((ceCs * τ / liftEps c : ℝ) ^ 3 / 12 : ℝ) : ℂ)) *
              ∫ u : ℝ, (F u : ℂ) * Complex.exp (Complex.I * (((ceCs * τ / liftEps c) * u : ℝ) : ℂ))) := by ring
      _ = _ := by rw [hK_eq]
  have hcov := Measure.integral_comp_mul_left (iMainIntegrand F (κ * liftEps c) m c ξ) (liftEps c)⁻¹
  simp only [abs_of_pos hε0, inv_inv, Complex.real_smul] at hcov
  have hv_int : ∫ v : ℝ, iMainIntegrand F (κ * liftEps c) m c ξ v =
      (((liftEps c)⁻¹ : ℝ) : ℂ) *
        ∫ τ : ℝ, mainEdgeAmp κ m c τ *
          Complex.exp (Complex.I * (c : ℂ) * ((L * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ : ℝ) : ℂ)) *
            ((ceK : ℂ) * Complex.exp (Complex.I * (((ceCs * τ / liftEps c : ℝ) ^ 3 / 12 : ℝ) : ℂ)) *
              ∫ u : ℝ, (F u : ℂ) * Complex.exp (Complex.I * (((ceCs * τ / liftEps c) * u : ℝ) : ℂ))) := by
    calc ∫ v : ℝ, iMainIntegrand F (κ * liftEps c) m c ξ v
        = (((liftEps c)⁻¹ : ℝ) : ℂ) * ((liftEps c : ℂ) * ∫ v : ℝ, iMainIntegrand F (κ * liftEps c) m c ξ v) := by
          rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hε0.ne', Complex.ofReal_one, one_mul]
      _ = (((liftEps c)⁻¹ : ℝ) : ℂ) * ∫ τ : ℝ, iMainIntegrand F (κ * liftEps c) m c ξ ((liftEps c)⁻¹ * τ) := by
          congr 1; exact hcov.symm
      _ = _ := by congr 1; exact integral_congr_ae (ae_of_all _ hbridge)
  unfold iMain
  rw [hv_int]
  have hξ_ne : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  have hscale : ∀ I_int : ℂ,
      (c : ℂ) * (ξ : ℂ) * (((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ((((liftEps c)⁻¹ : ℝ) : ℂ) * I_int)) =
        (c : ℂ) * ((2 * (Real.pi : ℂ))⁻¹ * (((liftEps c)⁻¹ : ℝ) : ℂ) * I_int) := fun I_int => by
    rw [show ((2 * Real.pi * ξ : ℝ) : ℂ) = (2 * (Real.pi : ℂ)) * (ξ : ℂ) by push_cast; ring, mul_inv]
    calc (c : ℂ) * (ξ : ℂ) * ((2 * (Real.pi : ℂ))⁻¹ * (ξ : ℂ)⁻¹ * ((((liftEps c)⁻¹ : ℝ) : ℂ) * I_int))
        = (ξ : ℂ) * (ξ : ℂ)⁻¹ * ((c : ℂ) * ((2 * (Real.pi : ℂ))⁻¹ * (((liftEps c)⁻¹ : ℝ) : ℂ) * I_int)) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hξ_ne, one_mul]
  rw [hscale]
  simp only [show liftEps c = c ^ (-(1 / 3 : ℝ)) from rfl, Complex.ofReal_inv] at *
  rw [hfub]
  unfold mainTransferOp
  ring

/-! ### 2. Error bound for `mainTransferOp` splitting at `X = a L` -/

/-- For `κ > 0`, `m ≥ 4`, `L_min > 0`, and `0 < a < ceCs⁻¹`, any `f ∈ L¹(ℝ)` satisfying
`‖f X‖ ≤ B_tail` on `{X > a L}` has `‖mainTransferOp κ m c f L‖ ≤ C₁ c⁻¹ L⁻² ‖f‖₁ + C₂ c^{1/2} B_tail`
for all `c ≥ 2` and `L ≥ L_min`. -/
theorem mainTransferOp_split_error {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 4 ≤ m)
    {L_min a : ℝ} (hLmin : 0 < L_min) (_ha0 : 0 < a) (ha1 : ceCs * a < 1) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ {c L B_tail : ℝ} {f : ℝ → ℂ}, 2 ≤ c → L_min ≤ L → 0 ≤ B_tail →
        Integrable f → (∀ X : ℝ, a * L < X → ‖f X‖ ≤ B_tail) →
        ‖mainTransferOp κ m c f L‖ ≤
          C₁ * c⁻¹ * L ^ (-2 : ℝ) * (∫ X : ℝ, ‖f X‖) + C₂ * c ^ (1 / 2 : ℝ) * B_tail := by
  have hd_pos : 0 < (1 - ceCs * a) * L_min := mul_pos (sub_pos.mpr ha1) hLmin
  obtain ⟨Ck, hCk, hdecay⟩ := mainEdgeKernel_right_decay hκ hm hd_pos
  obtain ⟨CL1, hCL1, hL1⟩ := mainEdgeKernel_L1_bound hκ hm
  have hcs0 : 0 < ceCs := ceCs_pos
  have hsub0 : 0 < 1 - ceCs * a := sub_pos.mpr ha1
  refine ⟨Ck * (1 - ceCs * a) ^ (-2 : ℝ) / (2 * Real.pi), CL1 / (2 * Real.pi * ceCs),
    div_pos (mul_pos hCk (Real.rpow_pos_of_pos hsub0 _)) (by positivity),
    div_pos hCL1 (by positivity), fun {c L B_tail f} hc hL hB hf1 htail => ?_⟩
  have hc0 : 0 < c := by linarith
  have hL0 : 0 < L := hLmin.trans_le hL
  obtain ⟨hK_int, hK_bd⟩ := hL1 hc
  have ha_amp : Integrable (mainEdgeAmp κ m c) := integrable_mainEdgeAmp hκ (by omega) (by linarith)
  set Ma : ℝ := ∫ τ : ℝ, ‖mainEdgeAmp κ m c τ‖
  have hK_le_Ma : ∀ y : ℝ, ‖mainEdgeKernel (mainEdgeAmp κ m c) c y‖ ≤ Ma := fun y => by
    unfold mainEdgeKernel
    refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (ae_of_all _ fun τ => ?_))
    dsimp only
    rw [norm_mul, show Complex.I * (c : ℂ) * ((y * τ + edgeR τ : ℝ) : ℂ) =
      ((c * (y * τ + edgeR τ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hKc : Continuous (fun y : ℝ => mainEdgeKernel (mainEdgeAmp κ m c) c y) := by
    refine continuous_of_dominated (bound := fun τ => ‖mainEdgeAmp κ m c τ‖) ?_ ?_ ha_amp.norm ?_
    · intro y
      have hphase : Continuous (fun τ : ℝ => Complex.exp (Complex.I * (c : ℂ) * ((y * τ + edgeR τ : ℝ) : ℂ))) :=
        Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
          ((continuous_const.mul continuous_id).add edgeR_contDiff.continuous)))
      exact ha_amp.aestronglyMeasurable.mul hphase.aestronglyMeasurable
    · exact fun y => ae_of_all _ fun τ => by
        rw [norm_mul, show Complex.I * (c : ℂ) * ((y * τ + edgeR τ : ℝ) : ℂ) =
          ((c * (y * τ + edgeR τ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
    · exact ae_of_all _ fun τ => by fun_prop
  have hmeas_K : AEStronglyMeasurable (fun X : ℝ => mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)) volume :=
    (hKc.comp (by fun_prop : Continuous fun X : ℝ => L - ceCs * X)).aestronglyMeasurable
  have hprod_int : Integrable (fun X : ℝ => f X * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)) := by
    refine (hf1.norm.const_mul Ma).mono' (hf1.aestronglyMeasurable.mul hmeas_K) (ae_of_all _ fun X => ?_)
    rw [norm_mul, mul_comm Ma]
    exact mul_le_mul_of_nonneg_left (hK_le_Ma _) (norm_nonneg _)
  have hdom_left : Integrable (fun X : ℝ => ‖f X‖) := hf1.norm
  have hK_shifted_int : Integrable (fun X : ℝ => ‖mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖) := by
    have h1 := ((hK_int.norm).comp_sub_left L).comp_mul_left' hcs0.ne'
    exact h1
  have hpiece_bd : ∀ X : ℝ,
      ‖f X * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖ ≤
        Ck * c ^ (-2 : ℝ) * (1 - ceCs * a) ^ (-2 : ℝ) * L ^ (-2 : ℝ) * ‖f X‖ +
          B_tail * ‖mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖ := by
    intro X
    rw [norm_mul]
    by_cases hX : X ≤ a * L
    · have hy_ge_L : (1 - ceCs * a) * L ≤ L - ceCs * X := by nlinarith [hX, hcs0]
      have hy_ge_d : (1 - ceCs * a) * L_min ≤ L - ceCs * X :=
        (mul_le_mul_of_nonneg_left hL hsub0.le).trans hy_ge_L
      have hKy := (hdecay hc hy_ge_d).1
      have hy_pow : (L - ceCs * X) ^ (-2 : ℝ) ≤ (1 - ceCs * a) ^ (-2 : ℝ) * L ^ (-2 : ℝ) := by
        rw [← Real.mul_rpow hsub0.le hL0.le]
        exact Real.rpow_le_rpow_of_nonpos (mul_pos hsub0 hL0) hy_ge_L (by norm_num)
      have hterm1 : ‖f X‖ * ‖mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖ ≤
          Ck * c ^ (-2 : ℝ) * (1 - ceCs * a) ^ (-2 : ℝ) * L ^ (-2 : ℝ) * ‖f X‖ := by
        calc ‖f X‖ * ‖mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖
            ≤ ‖f X‖ * (Ck * c ^ (-2 : ℝ) * (L - ceCs * X) ^ (-2 : ℝ)) := by gcongr
          _ ≤ ‖f X‖ * (Ck * c ^ (-2 : ℝ) * ((1 - ceCs * a) ^ (-2 : ℝ) * L ^ (-2 : ℝ))) := by gcongr
          _ = _ := by ring
      linarith [mul_nonneg hB (norm_nonneg (mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)))]
    · have hXgt : a * L < X := lt_of_not_ge hX
      have hfX := htail X hXgt
      have hterm2 : ‖f X‖ * ‖mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖ ≤
          B_tail * ‖mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖ := by gcongr
      have hterm1_nn : 0 ≤ Ck * c ^ (-2 : ℝ) * (1 - ceCs * a) ^ (-2 : ℝ) * L ^ (-2 : ℝ) * ‖f X‖ := by positivity
      linarith
  have hK_shifted_val : ∫ X : ℝ, ‖mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖ =
      ceCs⁻¹ * ∫ y : ℝ, ‖mainEdgeKernel (mainEdgeAmp κ m c) c y‖ := by
    have hcov := Measure.integral_comp_mul_left (fun u : ℝ => ‖mainEdgeKernel (mainEdgeAmp κ m c) c (L + u)‖) (-ceCs)
    rw [abs_inv, abs_neg, abs_of_pos hcs0, smul_eq_mul] at hcov
    have h1 : (fun X : ℝ => ‖mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖) =
        fun X => ‖mainEdgeKernel (mainEdgeAmp κ m c) c (L + (-ceCs) * X)‖ := by
      funext X; ring_nf
    rw [h1, hcov, integral_add_left_eq_self (fun y => ‖mainEdgeKernel (mainEdgeAmp κ m c) c y‖) L]
  unfold mainTransferOp
  rw [norm_mul]
  have hc2pi : ‖(c : ℂ) / (2 * (Real.pi : ℂ))‖ = c / (2 * Real.pi) := by
    rw [show (c : ℂ) / (2 * (Real.pi : ℂ)) = ((c / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hc2pi]
  have hint_le : ‖∫ X : ℝ, f X * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖ ≤
      (∫ X : ℝ, Ck * c ^ (-2 : ℝ) * (1 - ceCs * a) ^ (-2 : ℝ) * L ^ (-2 : ℝ) * ‖f X‖) +
        (∫ X : ℝ, B_tail * ‖mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖) := by
    calc ‖∫ X : ℝ, f X * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖
        ≤ ∫ X : ℝ, ‖f X * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ X : ℝ, (Ck * c ^ (-2 : ℝ) * (1 - ceCs * a) ^ (-2 : ℝ) * L ^ (-2 : ℝ) * ‖f X‖ +
            B_tail * ‖mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖) :=
          integral_mono hprod_int.norm ((hdom_left.const_mul _).add (hK_shifted_int.const_mul B_tail)) hpiece_bd
      _ = _ := integral_add (hdom_left.const_mul _) (hK_shifted_int.const_mul B_tail)
  rw [integral_const_mul, integral_const_mul, hK_shifted_val] at hint_le
  have h1 : (c / (2 * Real.pi)) * (Ck * c ^ (-2 : ℝ) * (1 - ceCs * a) ^ (-2 : ℝ) * L ^ (-2 : ℝ) * ∫ X : ℝ, ‖f X‖) =
      (Ck * (1 - ceCs * a) ^ (-2 : ℝ) / (2 * Real.pi)) * c⁻¹ * L ^ (-2 : ℝ) * ∫ X : ℝ, ‖f X‖ := by
    have hc_pow : c * c ^ (-2 : ℝ) = c⁻¹ := by
      calc c * c ^ (-2 : ℝ) = c ^ (1 : ℝ) * c ^ (-2 : ℝ) := by rw [Real.rpow_one]
        _ = c ^ (1 + (-2 : ℝ)) := (Real.rpow_add hc0 _ _).symm
        _ = c ^ (-1 : ℝ) := by norm_num
        _ = c⁻¹ := Real.rpow_neg_one c
    calc (c / (2 * Real.pi)) * (Ck * c ^ (-2 : ℝ) * (1 - ceCs * a) ^ (-2 : ℝ) * L ^ (-2 : ℝ) * ∫ X : ℝ, ‖f X‖)
        = (c * c ^ (-2 : ℝ)) * (Ck * (1 - ceCs * a) ^ (-2 : ℝ) / (2 * Real.pi)) * L ^ (-2 : ℝ) * ∫ X : ℝ, ‖f X‖ := by ring
      _ = _ := by rw [hc_pow]; ring
  have h2 : (c / (2 * Real.pi)) * (B_tail * (ceCs⁻¹ * ∫ y : ℝ, ‖mainEdgeKernel (mainEdgeAmp κ m c) c y‖)) ≤
      (CL1 / (2 * Real.pi * ceCs)) * c ^ (1 / 2 : ℝ) * B_tail := by
    have hc_pow : c * c ^ (-(1 / 2 : ℝ)) = c ^ (1 / 2 : ℝ) := by
      calc c * c ^ (-(1 / 2 : ℝ)) = c ^ (1 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
        _ = c ^ (1 + -(1 / 2 : ℝ)) := (Real.rpow_add hc0 _ _).symm
        _ = c ^ (1 / 2 : ℝ) := by norm_num
    calc (c / (2 * Real.pi)) * (B_tail * (ceCs⁻¹ * ∫ y : ℝ, ‖mainEdgeKernel (mainEdgeAmp κ m c) c y‖))
        ≤ (c / (2 * Real.pi)) * (B_tail * (ceCs⁻¹ * (CL1 * c ^ (-(1 / 2 : ℝ))))) := by gcongr
      _ = (CL1 / (2 * Real.pi * ceCs)) * (c * c ^ (-(1 / 2 : ℝ))) * B_tail := by ring
      _ = _ := by rw [hc_pow]
  calc (c / (2 * Real.pi)) * ‖∫ X : ℝ, f X * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)‖
      ≤ (c / (2 * Real.pi)) * ((Ck * c ^ (-2 : ℝ) * (1 - ceCs * a) ^ (-2 : ℝ) * L ^ (-2 : ℝ) * ∫ X : ℝ, ‖f X‖) +
          B_tail * (ceCs⁻¹ * ∫ y : ℝ, ‖mainEdgeKernel (mainEdgeAmp κ m c) c y‖)) := by gcongr
    _ = (c / (2 * Real.pi)) * (Ck * c ^ (-2 : ℝ) * (1 - ceCs * a) ^ (-2 : ℝ) * L ^ (-2 : ℝ) * ∫ X : ℝ, ‖f X‖) +
          (c / (2 * Real.pi)) * (B_tail * (ceCs⁻¹ * ∫ y : ℝ, ‖mainEdgeKernel (mainEdgeAmp κ m c) c y‖)) := by ring
    _ ≤ _ := by linarith [h1, h2]

/-! ### 3. Real convolution in `L¹ ∩ H¹` and `fourierPaper` -/

/-- Real-line convolution `(g * k)(X) = ∫ Y, g Y · k (X - Y)`. -/
noncomputable def realConv (g k : ℝ → ℝ) : ℝ → ℝ :=
  g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] k

lemma realConv_apply (g k : ℝ → ℝ) (X : ℝ) : realConv g k X = ∫ Y : ℝ, g Y * k (X - Y) := by
  simp [realConv, convolution_def]

lemma realConv_comm {g k : ℝ → ℝ} (_hg : Integrable g) (_hk : Integrable k) (X : ℝ) :
    realConv g k X = realConv k g X := by
  have h1 : realConv g k X = ∫ t : ℝ, g t * k (X - t) := by
    unfold realConv; rw [convolution_def]; rfl
  have h2 : realConv k g X = ∫ t : ℝ, k t * g (X - t) := by
    unfold realConv; rw [convolution_def]; rfl
  rw [h1, h2, ← integral_sub_left_eq_self _ volume X]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  ring_nf

lemma integrable_realConv {g k : ℝ → ℝ} (hg : Integrable g) (hk : Integrable k) :
    Integrable (realConv g k) :=
  hg.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hk

lemma l2_of_integrable_bdd {f : ℝ → ℝ} (hf1 : Integrable f) {M : ℝ} (hfM : ∀ x : ℝ, |f x| ≤ M) :
    MemLp (fun x => (f x : ℂ)) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm (Complex.ofRealCLM.integrable_comp hf1).aestronglyMeasurable).mpr ?_
  refine (hf1.norm.const_mul (max M 0)).mono'
    ((Complex.ofRealCLM.integrable_comp hf1).aestronglyMeasurable.norm.pow 2) (ae_of_all _ fun x => ?_)
  simp only [Complex.ofRealCLM_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs, sq]
  exact mul_le_mul_of_nonneg_right ((hfM x).trans (le_max_left _ _)) (abs_nonneg _)

lemma weakDerivL2_of_hasDerivAt {g g' : ℝ → ℝ} (hg1 : Integrable g) (hg'1 : Integrable g')
    {Mg Mg' : ℝ} (hgM : ∀ x, |g x| ≤ Mg) (hg'M : ∀ x, |g' x| ≤ Mg')
    (hderiv : ∀ x : ℝ, HasDerivAt g (g' x) x) :
    WeakDerivL2 (fun x => (g x : ℂ)) (fun x => (g' x : ℂ)) where
  memLp := l2_of_integrable_bdd hg1 hgM
  memLp_deriv := l2_of_integrable_bdd hg'1 hg'M
  ibp φ := by
    have hu : ∀ x ∈ tsupport (fun x => (g x : ℂ)), HasDerivAt (⇑φ) (deriv (⇑φ) x) x := fun x _ =>
      φ.differentiable.differentiableAt.hasDerivAt
    have hv : ∀ x ∈ tsupport (⇑φ), HasDerivAt (fun x => (g x : ℂ)) (g' x : ℂ) x := fun x _ =>
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hderiv x)).congr_deriv (by simp)
    have huv' : Integrable (fun x => φ x * (g' x : ℂ)) :=
      (φ.memLp 2 volume).integrable_mul (l2_of_integrable_bdd hg'1 hg'M)
    have hu'v : Integrable (fun x => deriv (⇑φ) x * (g x : ℂ)) := by
      have h : Integrable (fun x => (SchwartzMap.derivCLM ℂ ℂ φ) x * (g x : ℂ)) :=
        ((SchwartzMap.derivCLM ℂ ℂ φ).memLp 2 volume).integrable_mul (l2_of_integrable_bdd hg1 hgM)
      exact h.congr (ae_of_all _ fun x => rfl)
    have huv : Integrable (fun x => φ x * (g x : ℂ)) :=
      (φ.memLp 2 volume).integrable_mul (l2_of_integrable_bdd hg1 hgM)
    have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable hu hv huv' hu'v huv
    calc ∫ x : ℝ, deriv (⇑φ) x * (g x : ℂ)
        = - -∫ x : ℝ, deriv (⇑φ) x * (g x : ℂ) := (neg_neg _).symm
      _ = -∫ x : ℝ, φ x * (g' x : ℂ) := by rw [hibp]

lemma hasDerivAt_realConv {g g' k : ℝ → ℝ} (hg1 : Integrable g) (hg'1 : Integrable g') (hk1 : Integrable k)
    {Mg Mg' : ℝ} (hgM : ∀ x, |g x| ≤ Mg) (hg'M : ∀ x, |g' x| ≤ Mg')
    (hderiv : ∀ x : ℝ, HasDerivAt g (g' x) x) (X : ℝ) :
    HasDerivAt (realConv g k) (realConv g' k X) X := by
  have hg_cont : Continuous g := continuous_iff_continuousAt.mpr fun x => (hderiv x).continuousAt
  have hconv_eq : realConv g k = fun x => ∫ Z : ℝ, k Z * g (x - Z) := funext fun x => by
    rw [realConv_comm hg1 hk1, realConv_apply]
  have hconv_eq' : realConv g' k X = ∫ Z : ℝ, k Z * g' (X - Z) := by
    rw [realConv_comm hg'1 hk1, realConv_apply]
  rw [hconv_eq, hconv_eq']
  have hF_meas : ∀ x : ℝ, AEStronglyMeasurable (fun Z : ℝ => k Z * g (x - Z)) volume := fun x =>
    hk1.aestronglyMeasurable.mul (hg_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hF_int : Integrable (fun Z : ℝ => k Z * g (X - Z)) :=
    (hk1.norm.mul_const (max Mg 0)).mono' (hF_meas X) (ae_of_all _ fun Z => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left ((hgM _).trans (le_max_left _ _)) (abs_nonneg _))
  have hF'_meas : AEStronglyMeasurable (fun Z : ℝ => k Z * g' (X - Z)) volume := by
    have hm : AEStronglyMeasurable (fun Z : ℝ => g' (X - Z)) volume :=
      hg'1.aestronglyMeasurable.comp_quasiMeasurePreserving
        ((Measure.measurePreserving_sub_left volume X).quasiMeasurePreserving)
    exact hk1.aestronglyMeasurable.mul hm
  have hderiv_Z : ∀ᵐ Z ∂volume, ∀ x ∈ Metric.ball X 1,
      HasDerivAt (fun x : ℝ => k Z * g (x - Z)) (k Z * g' (x - Z)) x := by
    refine ae_of_all _ fun Z x _ => ?_
    have hd : HasDerivAt (fun t : ℝ => g (t - Z)) (g' (x - Z)) x :=
      ((hderiv (x - Z)).comp x ((hasDerivAt_id x).sub_const Z)).congr_deriv (by simp)
    exact hd.const_mul (k Z)
  have hbound_int : Integrable (fun Z : ℝ => ‖k Z‖ * max Mg' 0) := hk1.norm.mul_const _
  have hbound : ∀ᵐ Z ∂volume, ∀ x ∈ Metric.ball X 1, ‖k Z * g' (x - Z)‖ ≤ ‖k Z‖ * max Mg' 0 := by
    refine ae_of_all _ fun Z x _ => ?_
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((hg'M _).trans (le_max_left _ _)) (abs_nonneg _)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds X one_pos)
    (Eventually.of_forall hF_meas) hF_int hF'_meas hbound hbound_int hderiv_Z).2

lemma realConv_abs_le_meas {g k : ℝ → ℝ} (hg1 : Integrable g) (hk1 : Integrable k)
    {Mg : ℝ} (_hMg : 0 ≤ Mg) (hgM : ∀ x, |g x| ≤ Mg) (X : ℝ) :
    |realConv g k X| ≤ Mg * ∫ Z : ℝ, |k Z| := by
  rw [realConv_apply]
  have h_eq : ∫ Y : ℝ, g Y * k (X - Y) = ∫ Z : ℝ, g (X - Z) * k Z := by
    have h1 := integral_sub_left_eq_self (fun Y => g Y * k (X - Y)) volume X
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun Z => ?_)
    ring_nf
  rw [h_eq, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hint : Integrable (fun Z : ℝ => Mg * |k Z|) := hk1.norm.const_mul Mg
  have hm : AEStronglyMeasurable (fun Z : ℝ => ‖g (X - Z) * k Z‖) volume := by
    have hg_meas : AEStronglyMeasurable (fun Z : ℝ => g (X - Z)) volume :=
      hg1.aestronglyMeasurable.comp_quasiMeasurePreserving
        ((Measure.measurePreserving_sub_left volume X).quasiMeasurePreserving)
    exact (hg_meas.mul hk1.aestronglyMeasurable).norm
  have hint_prod : Integrable (fun Z : ℝ => ‖g (X - Z) * k Z‖) := by
    refine hint.mono' hm (ae_of_all _ fun Z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hgM _) (abs_nonneg _)
  exact (integral_mono hint_prod hint fun Z => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hgM _) (abs_nonneg _)).trans_eq (integral_const_mul Mg _)

lemma weakDerivL2_realConv {g g' k : ℝ → ℝ} (hg1 : Integrable g) (hg'1 : Integrable g') (hk1 : Integrable k)
    {Mg Mg' : ℝ} (hMg : 0 ≤ Mg) (hMg' : 0 ≤ Mg') (hgM : ∀ x, |g x| ≤ Mg) (hg'M : ∀ x, |g' x| ≤ Mg')
    (hderiv : ∀ x : ℝ, HasDerivAt g (g' x) x) :
    WeakDerivL2 (fun X => (realConv g k X : ℂ)) (fun X => (realConv g' k X : ℂ)) :=
  weakDerivL2_of_hasDerivAt (integrable_realConv hg1 hk1) (integrable_realConv hg'1 hk1)
    (realConv_abs_le_meas hg1 hk1 hMg hgM) (realConv_abs_le_meas hg'1 hk1 hMg' hg'M)
    (hasDerivAt_realConv hg1 hg'1 hk1 hgM hg'M hderiv)

lemma fourierPaper_realConv {g k : ℝ → ℝ} (hg1 : Integrable g) (hk1 : Integrable k)
    (hg_cont : Continuous g) (hk_cont : Continuous k) (ξ : ℝ) :
    fourierPaper (fun X => (realConv g k X : ℂ)) ξ =
      fourierPaper (fun Y => (g Y : ℂ)) ξ * fourierPaper (fun Z => (k Z : ℂ)) ξ := by
  unfold fourierPaper
  have hgC : Integrable (fun Y : ℝ => (g Y : ℂ)) := Complex.ofRealCLM.integrable_comp hg1
  have hkC : Integrable (fun Z : ℝ => (k Z : ℂ)) := Complex.ofRealCLM.integrable_comp hk1
  have hint_prod : Integrable (fun p : ℝ × ℝ =>
      Complex.exp (-(Complex.I * ((p.2 * ξ : ℝ) : ℂ))) * (g p.1 : ℂ) * (k (p.2 - p.1) : ℂ)) (volume.prod volume) := by
    refine (integrable_prod_iff ?_).mpr ⟨ae_of_all _ fun Y => ?_, ?_⟩
    · exact (((by fun_prop : Continuous fun p : ℝ × ℝ =>
          Complex.exp (-(Complex.I * ((p.2 * ξ : ℝ) : ℂ)))).mul
        ((Complex.continuous_ofReal.comp hg_cont).comp continuous_fst)).mul
        ((Complex.continuous_ofReal.comp hk_cont).comp (continuous_snd.sub continuous_fst))).aestronglyMeasurable
    · have hX : Integrable (fun X : ℝ => Complex.exp (-(Complex.I * ((X * ξ : ℝ) : ℂ))) * (k (X - Y) : ℂ)) := by
        have hk_sh : Integrable (fun X : ℝ => (k (X - Y) : ℂ)) := hkC.comp_sub_right Y
        refine hk_sh.norm.mono' ((by fun_prop : Continuous fun X : ℝ =>
            Complex.exp (-(Complex.I * ((X * ξ : ℝ) : ℂ)))).aestronglyMeasurable.mul hk_sh.aestronglyMeasurable)
          (ae_of_all _ fun X => ?_)
        rw [norm_mul, show -(Complex.I * ((X * ξ : ℝ) : ℂ)) = ((- (X * ξ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, one_mul]
      exact (hX.const_mul (g Y : ℂ)).congr (ae_of_all _ fun X => by ring)
    · have hnorm : (fun Y : ℝ => ∫ X : ℝ, ‖Complex.exp (-(Complex.I * ((X * ξ : ℝ) : ℂ))) * (g Y : ℂ) * (k (X - Y) : ℂ)‖) =
          fun Y : ℝ => |g Y| * ∫ Z : ℝ, |k Z| := funext fun Y => by
        have h1 : (fun X : ℝ => ‖Complex.exp (-(Complex.I * ((X * ξ : ℝ) : ℂ))) * (g Y : ℂ) * (k (X - Y) : ℂ)‖) =
            fun X : ℝ => |g Y| * |k (X - Y)| := funext fun X => by
          rw [norm_mul, norm_mul, show -(Complex.I * ((X * ξ : ℝ) : ℂ)) = ((- (X * ξ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        rw [h1, integral_const_mul, integral_sub_right_eq_self (fun Z => |k Z|) (μ := volume) Y]
      rw [hnorm]
      exact hg1.norm.mul_const _
  have hRHS : (∫ Y : ℝ, Complex.exp (-(Complex.I * ((Y * ξ : ℝ) : ℂ))) * (g Y : ℂ)) *
        (∫ Z : ℝ, Complex.exp (-(Complex.I * ((Z * ξ : ℝ) : ℂ))) * (k Z : ℂ)) =
      ∫ Y : ℝ, ∫ X : ℝ, Complex.exp (-(Complex.I * ((X * ξ : ℝ) : ℂ))) * (g Y : ℂ) * (k (X - Y) : ℂ) := by
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun Y => ?_)
    have hshift := integral_sub_right_eq_self
      (fun Z : ℝ => Complex.exp (-(Complex.I * ((Y * ξ : ℝ) : ℂ))) * (g Y : ℂ) *
        (Complex.exp (-(Complex.I * ((Z * ξ : ℝ) : ℂ))) * (k Z : ℂ))) (μ := volume) Y
    calc (Complex.exp (-(Complex.I * ((Y * ξ : ℝ) : ℂ))) * (g Y : ℂ)) *
          ∫ Z : ℝ, Complex.exp (-(Complex.I * ((Z * ξ : ℝ) : ℂ))) * (k Z : ℂ)
        = ∫ Z : ℝ, Complex.exp (-(Complex.I * ((Y * ξ : ℝ) : ℂ))) * (g Y : ℂ) *
            (Complex.exp (-(Complex.I * ((Z * ξ : ℝ) : ℂ))) * (k Z : ℂ)) := (integral_const_mul _ _).symm
      _ = ∫ X : ℝ, Complex.exp (-(Complex.I * ((Y * ξ : ℝ) : ℂ))) * (g Y : ℂ) *
            (Complex.exp (-(Complex.I * (((X - Y) * ξ : ℝ) : ℂ))) * (k (X - Y) : ℂ)) := hshift.symm
      _ = ∫ X : ℝ, Complex.exp (-(Complex.I * ((X * ξ : ℝ) : ℂ))) * (g Y : ℂ) * (k (X - Y) : ℂ) := by
          refine integral_congr_ae (ae_of_all _ fun X => ?_)
          dsimp only
          calc Complex.exp (-(Complex.I * ((Y * ξ : ℝ) : ℂ))) * (g Y : ℂ) *
                  (Complex.exp (-(Complex.I * (((X - Y) * ξ : ℝ) : ℂ))) * (k (X - Y) : ℂ))
              = (Complex.exp (-(Complex.I * ((Y * ξ : ℝ) : ℂ))) *
                  Complex.exp (-(Complex.I * (((X - Y) * ξ : ℝ) : ℂ)))) * (g Y : ℂ) * (k (X - Y) : ℂ) := by ring
            _ = Complex.exp (-(Complex.I * ((X * ξ : ℝ) : ℂ))) * (g Y : ℂ) * (k (X - Y) : ℂ) := by
                rw [← Complex.exp_add]; congr 2; push_cast; ring
  rw [hRHS, integral_integral_swap hint_prod]
  refine integral_congr_ae (ae_of_all _ fun X => ?_)
  dsimp only
  rw [realConv_apply]
  have hcm : (∫ Y : ℝ, Complex.exp (-(Complex.I * ((X * ξ : ℝ) : ℂ))) * (g Y : ℂ) * (k (X - Y) : ℂ)) =
      Complex.exp (-(Complex.I * ((X * ξ : ℝ) : ℂ))) * ∫ Y : ℝ, ((g Y * k (X - Y) : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun Y => ?_)
    push_cast; ring
  rw [hcm, integral_complex_ofReal]

/-! ### 4. Multiplier and rescaled `ceG1` Fourier approximation bounds -/

lemma abs_edgeR_le (τ : ℝ) : |edgeR τ| ≤ (Real.pi ^ 2 / 12) * |τ| ^ 3 := by
  have hzero : edgeR 0 = 0 := by unfold edgeR; simp
  have hderiv : ∀ t : ℝ, HasDerivAt edgeR (ceHth (Real.pi * t / 2)) t := hasDerivAt_edgeR
  have hbound : ∀ t ∈ segment ℝ (0 : ℝ) τ, ‖deriv edgeR t‖ ≤ (Real.pi ^ 2 / 12) * |τ| ^ 2 := by
    intro t ht
    rw [(hderiv t).deriv, Real.norm_of_nonneg (ceHth_nonneg _)]
    have hle := ceHth_le_sq_div_three (Real.pi * t / 2)
    have ht_abs : |t| ≤ |τ| := by
      rw [segment_eq_image] at ht
      rcases ht with ⟨s, hs, rfl⟩
      simp only [smul_eq_mul, mul_zero, zero_add] at *
      rw [abs_mul, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (abs_nonneg τ) hs.2
    calc ceHth (Real.pi * t / 2) ≤ (Real.pi * t / 2) ^ 2 / 3 := hle
      _ = (Real.pi ^ 2 / 12) * |t| ^ 2 := by rw [sq_abs]; ring
      _ ≤ (Real.pi ^ 2 / 12) * |τ| ^ 2 := by gcongr
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hderiv t).differentiableAt) hbound (convex_segment 0 τ)
    (left_mem_segment ℝ 0 τ) (right_mem_segment ℝ 0 τ)
  rw [hzero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at hmvt
  calc |edgeR τ| ≤ (Real.pi ^ 2 / 12) * |τ| ^ 2 * |τ| := hmvt
    _ = (Real.pi ^ 2 / 12) * |τ| ^ 3 := by ring

lemma norm_exp_I_mul_sub_one_le_two_rpow (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ 2 * |x| ^ (1 / 4 : ℝ) := by
  have h2 : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ 2 := by
    calc ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖
        ≤ ‖Complex.exp ((x : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [Complex.norm_exp_ofReal_mul_I, norm_one]
      _ = 2 := by norm_num
  by_cases hx : |x| ≤ 1
  · have hftc : Complex.exp ((x : ℂ) * Complex.I) - 1 =
        ∫ t in (0 : ℝ)..x, Complex.I * Complex.exp ((t : ℂ) * Complex.I) := by
      have hd : ∀ t ∈ uIcc (0 : ℝ) x,
          HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
            (Complex.I * Complex.exp ((t : ℂ) * Complex.I)) t := fun t _ => by
        exact ((Complex.hasDerivAt_exp _).comp t
          ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I)).congr_deriv (by simp; ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((by fun_prop : Continuous fun t : ℝ => Complex.I * Complex.exp ((t : ℂ) * Complex.I)).intervalIntegrable 0 x)]
      simp
    have hbd : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ |x| := by
      rw [hftc]
      have h_norm := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun t : ℝ => Complex.I * Complex.exp ((t : ℂ) * Complex.I)) (a := (0 : ℝ)) (b := x) (C := 1)
        (fun t _ => by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I])
      simpa using h_norm
    rcases eq_or_lt_of_le (abs_nonneg x) with hx0 | hxpos
    · rw [← hx0] at hbd ⊢; simpa using hbd
    · have hr : |x| ≤ |x| ^ (1 / 4 : ℝ) := by
        simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hxpos hx (by norm_num : (1 / 4 : ℝ) ≤ 1)
      linarith [hbd, hr, Real.rpow_nonneg (abs_nonneg x) (1 / 4 : ℝ)]
  · have hx1 : 1 ≤ |x| := (not_le.mp hx).le
    have hr : (1 : ℝ) ≤ |x| ^ (1 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    linarith [h2, hr]

theorem norm_mainEdgeAmp_phase_sub_one_le {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ C_m > 0, ∀ {c : ℝ}, 1 ≤ c → ∀ w : ℝ,
      ‖mainEdgeAmp κ m c (w / c) * Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ)) - 1‖ ≤
        C_m * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by
  obtain ⟨hcd, C_a, hCa, hbd⟩ := mainEdgeAmp_contDiff_and_bound hκ hm
  refine ⟨(C_a + 2) + (Real.pi ^ 2 / 12 + 2), by positivity, fun {c} hc w => ?_⟩
  have hc0 : 0 < c := by linarith
  have hc_pow : c ^ (-(1 / 4 : ℝ)) ≤ c ^ (-(1 / 6 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc (by norm_num)
  have h_amp : ‖mainEdgeAmp κ m c (w / c) - 1‖ ≤ (C_a + 2) * c ^ (-(1 / 4 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by
    have hnorm1 := (norm_mainEdgeAmp_le κ m hc0 (w / c)).2
    by_cases hwc : |w / c| ≤ 1
    · have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun τ _ => ((hcd hc).differentiable (by decide) τ))
        (fun τ _ => by
          have h1 := hbd hc 1 (by norm_num) τ
          rw [iteratedDeriv_one] at h1
          have hpow : (1 + |τ|) ^ (-(m : ℝ) - 1 / 2) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg τ]) (by linarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m])
          exact h1.trans (mul_le_of_le_one_right hCa.le hpow))
        convex_univ (mem_univ 0) (mem_univ (w / c))
      rw [mainEdgeAmp_zero, Real.norm_eq_abs, sub_zero] at hmvt
      have h_abs_wc : |w / c| ≤ |w / c| ^ (1 / 4 : ℝ) := by
        rcases eq_or_lt_of_le (abs_nonneg (w / c)) with h0 | hpos
        · rw [← h0]; simp
        · simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hpos hwc (by norm_num : (1 / 4 : ℝ) ≤ 1)
      have h_split : |w / c| ^ (1 / 4 : ℝ) = c ^ (-(1 / 4 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by
        rw [abs_div, abs_of_pos hc0, Real.div_rpow (abs_nonneg w) hc0.le, Real.rpow_neg hc0.le]
        ring
      calc ‖mainEdgeAmp κ m c (w / c) - 1‖ ≤ C_a * |w / c| := hmvt
        _ ≤ C_a * |w / c| ^ (1 / 4 : ℝ) := by gcongr
        _ = C_a * c ^ (-(1 / 4 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by rw [h_split]; ring
        _ ≤ (C_a + 2) * c ^ (-(1 / 4 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by
            have : 0 ≤ c ^ (-(1 / 4 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by positivity
            nlinarith
    · have hwc1 : 1 ≤ |w / c| := (not_le.mp hwc).le
      have hr : (1 : ℝ) ≤ |w / c| ^ (1 / 4 : ℝ) := Real.one_le_rpow hwc1 (by norm_num)
      have h_split : |w / c| ^ (1 / 4 : ℝ) = c ^ (-(1 / 4 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by
        rw [abs_div, abs_of_pos hc0, Real.div_rpow (abs_nonneg w) hc0.le, Real.rpow_neg hc0.le]
        ring
      have h2 : ‖mainEdgeAmp κ m c (w / c) - 1‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by linarith [norm_one (α := ℂ)])
      calc ‖mainEdgeAmp κ m c (w / c) - 1‖ ≤ 2 := h2
        _ ≤ 2 * |w / c| ^ (1 / 4 : ℝ) := by linarith
        _ = 2 * c ^ (-(1 / 4 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by rw [h_split]; ring
        _ ≤ (C_a + 2) * c ^ (-(1 / 4 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by
            have : 0 ≤ c ^ (-(1 / 4 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by positivity
            nlinarith [hCa]
  have h_phase : ‖Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ)) - 1‖ ≤
      (Real.pi ^ 2 / 12 + 2) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by
    have hnorm_e : ‖Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ)) - 1‖ ≤ 2 ∧
        ‖Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ)) - 1‖ ≤ |c * edgeR (w / c)| := by
      have hexp_eq : Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ)) =
          Complex.exp (((c * edgeR (w / c) : ℝ) : ℂ) * Complex.I) := by ring_nf
      rw [hexp_eq]
      refine ⟨(norm_sub_le _ _).trans (by rw [Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num), ?_⟩
      have hftc : Complex.exp (((c * edgeR (w / c) : ℝ) : ℂ) * Complex.I) - 1 =
          ∫ t in (0 : ℝ)..(c * edgeR (w / c)), Complex.I * Complex.exp ((t : ℂ) * Complex.I) := by
        have hd : ∀ t ∈ uIcc (0 : ℝ) (c * edgeR (w / c)),
            HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
              (Complex.I * Complex.exp ((t : ℂ) * Complex.I)) t := fun t _ =>
          ((Complex.hasDerivAt_exp _).comp t
            ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I)).congr_deriv (by simp; ring)
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
          ((by fun_prop : Continuous fun t : ℝ => Complex.I * Complex.exp ((t : ℂ) * Complex.I)).intervalIntegrable _ _)]
        simp
      rw [hftc]
      have h_norm := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun t : ℝ => Complex.I * Complex.exp ((t : ℂ) * Complex.I)) (a := (0 : ℝ)) (b := c * edgeR (w / c)) (C := 1)
        (fun t _ => by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I])
      simpa using h_norm
    by_cases hw : |w| ≤ c ^ (2 / 3 : ℝ)
    · have hR : |c * edgeR (w / c)| ≤ (Real.pi ^ 2 / 12) * c ^ (-2 : ℝ) * |w| ^ (3 : ℝ) := by
        rw [abs_mul, abs_of_pos hc0]
        have hwc3 : |w / c| ^ 3 = c ^ (-3 : ℝ) * |w| ^ (3 : ℝ) := by
          rw [abs_div, abs_of_pos hc0, div_pow, ← Real.rpow_natCast c 3, ← Real.rpow_natCast |w| 3,
            Real.rpow_neg hc0.le, div_eq_mul_inv]
          ring
        have hc12 : c * c ^ (-3 : ℝ) = c ^ (-2 : ℝ) := by
          calc c * c ^ (-3 : ℝ) = c ^ (1 : ℝ) * c ^ (-3 : ℝ) := by rw [Real.rpow_one]
            _ = c ^ (1 + (-3 : ℝ)) := (Real.rpow_add hc0 _ _).symm
            _ = c ^ (-2 : ℝ) := by norm_num
        calc c * |edgeR (w / c)| ≤ c * ((Real.pi ^ 2 / 12) * |w / c| ^ 3) := by gcongr; exact abs_edgeR_le _
          _ = (Real.pi ^ 2 / 12) * (c * c ^ (-3 : ℝ)) * |w| ^ (3 : ℝ) := by rw [hwc3]; ring
          _ = (Real.pi ^ 2 / 12) * c ^ (-2 : ℝ) * |w| ^ (3 : ℝ) := by rw [hc12]
      have hw_rpow : c ^ (-2 : ℝ) * |w| ^ (3 : ℝ) ≤ c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by
        rcases eq_or_lt_of_le (abs_nonneg w) with h0 | hwpos
        · rw [← h0]; simp
        · have h3 : |w| ^ (3 : ℝ) = |w| ^ (11 / 4 : ℝ) * |w| ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_add hwpos]; norm_num
          have h11 : |w| ^ (11 / 4 : ℝ) ≤ (c ^ (2 / 3 : ℝ)) ^ (11 / 4 : ℝ) :=
            Real.rpow_le_rpow (abs_nonneg w) hw (by norm_num)
          have hcexp : c ^ (-2 : ℝ) * (c ^ (2 / 3 : ℝ)) ^ (11 / 4 : ℝ) = c ^ (-(1 / 6 : ℝ)) := by
            rw [← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
          calc c ^ (-2 : ℝ) * |w| ^ (3 : ℝ)
              = (c ^ (-2 : ℝ) * |w| ^ (11 / 4 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by rw [h3]; ring
            _ ≤ (c ^ (-2 : ℝ) * (c ^ (2 / 3 : ℝ)) ^ (11 / 4 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by gcongr
            _ = c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by rw [hcexp]
      calc ‖Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ)) - 1‖
          ≤ |c * edgeR (w / c)| := hnorm_e.2
        _ ≤ (Real.pi ^ 2 / 12) * (c ^ (-2 : ℝ) * |w| ^ (3 : ℝ)) := by linarith
        _ ≤ (Real.pi ^ 2 / 12) * (c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ)) := by gcongr
        _ ≤ (Real.pi ^ 2 / 12 + 2) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by
            have : 0 ≤ c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by positivity
            nlinarith
    · have hw1 : c ^ (2 / 3 : ℝ) ≤ |w| := (not_le.mp hw).le
      have hr : c ^ (1 / 6 : ℝ) ≤ |w| ^ (1 / 4 : ℝ) := by
        calc c ^ (1 / 6 : ℝ) = (c ^ (2 / 3 : ℝ)) ^ (1 / 4 : ℝ) := by
              rw [← Real.rpow_mul hc0.le]; norm_num
          _ ≤ |w| ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) hw1 (by norm_num)
      have h1 : 1 ≤ c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by
        rw [Real.rpow_neg hc0.le, ← div_eq_inv_mul, one_le_div (by positivity)]
        exact hr
      calc ‖Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ)) - 1‖ ≤ 2 := hnorm_e.1
        _ ≤ 2 * (c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ)) := by linarith
        _ ≤ (Real.pi ^ 2 / 12 + 2) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by
            have : 0 ≤ c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by positivity
            nlinarith [Real.pi_pos]
  have hE1 : ‖Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ))‖ = 1 := by
    rw [show Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ) = ((c * edgeR (w / c) : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I]
  calc ‖mainEdgeAmp κ m c (w / c) * Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ)) - 1‖
      = ‖(mainEdgeAmp κ m c (w / c) - 1) * Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ)) +
          (Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ)) - 1)‖ := by ring_nf
    _ ≤ ‖(mainEdgeAmp κ m c (w / c) - 1) * Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ))‖ +
          ‖Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ)) - 1‖ := norm_add_le _ _
    _ = ‖mainEdgeAmp κ m c (w / c) - 1‖ + ‖Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ)) - 1‖ := by
          rw [norm_mul, hE1, mul_one]
    _ ≤ (C_a + 2) * c ^ (-(1 / 4 : ℝ)) * |w| ^ (1 / 4 : ℝ) +
          (Real.pi ^ 2 / 12 + 2) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by gcongr
    _ ≤ (C_a + 2) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) +
          (Real.pi ^ 2 / 12 + 2) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by gcongr
    _ = ((C_a + 2) + (Real.pi ^ 2 / 12 + 2)) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by ring

/-- Rescaled Airy ground-state kernel `ρ_ε(Z) = (ε²)⁻¹ ceG1 a₁ (-Z / ε²)`. -/
noncomputable def rescaledG1 (ε Z : ℝ) : ℝ := (ε ^ 2)⁻¹ * ceG1 (airyZero 1) (-Z / ε ^ 2)

lemma rescaledG1_nonneg (ε Z : ℝ) : 0 ≤ rescaledG1 ε Z :=
  mul_nonneg (inv_nonneg.mpr (sq_nonneg ε)) (convG1_nonneg _)

lemma rescaledG1_continuous {ε : ℝ} (_hε : 0 < ε) : Continuous (rescaledG1 ε) :=
  continuous_const.mul ((continuous_ceG1 (airyZero 1)).comp (by fun_prop))

lemma rescaledG1_integrable {ε : ℝ} (hε : 0 < ε) : Integrable (rescaledG1 ε) := by
  have h1 := ((ceG1_integrable).comp_mul_left' (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hε.ne')))).const_mul (ε ^ 2)⁻¹
  refine h1.congr (ae_of_all _ fun Z => ?_)
  simp [rescaledG1, div_eq_mul_inv, mul_comm]

lemma rescaledG1_integral {ε : ℝ} (hε : 0 < ε) : ∫ Z : ℝ, rescaledG1 ε Z = 1 := by
  have hcov := Measure.integral_comp_mul_left (ceG1 (airyZero 1)) (-(ε ^ 2)⁻¹)
  simp only [abs_inv, abs_neg, abs_of_pos (pow_pos hε 2), inv_inv, smul_eq_mul] at hcov
  have h_eq : (fun Z : ℝ => rescaledG1 ε Z) = fun Z => (ε ^ 2)⁻¹ * ceG1 (airyZero 1) (-(ε ^ 2)⁻¹ * Z) := by
    funext Z; unfold rescaledG1; ring
  have hε2 : ε ^ 2 ≠ 0 := (pow_pos hε 2).ne'
  rw [h_eq, integral_const_mul, hcov, ← mul_assoc, inv_mul_cancel₀ hε2, one_mul, ceG1_integral_eq_one]

lemma norm_fourierPaper_rescaledG1_le {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) :
    ‖fourierPaper (fun Z => (rescaledG1 ε Z : ℂ)) ξ‖ ≤ 1 := by
  unfold fourierPaper
  refine (norm_integral_le_integral_norm _).trans ?_
  have hnorm : (fun Z : ℝ => ‖Complex.exp (-(Complex.I * ((Z * ξ : ℝ) : ℂ))) * (rescaledG1 ε Z : ℂ)‖) =
      rescaledG1 ε := funext fun Z => by
    rw [norm_mul, show -(Complex.I * ((Z * ξ : ℝ) : ℂ)) = ((- (Z * ξ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (rescaledG1_nonneg ε Z)]
  rw [hnorm, rescaledG1_integral hε]

theorem norm_rescaledG1_fourier_sub_one_le :
    ∃ C_k > 0, ∀ {c : ℝ}, 1 ≤ c → ∀ w : ℝ,
      ‖fourierPaper (fun Z => (rescaledG1 (liftEps c) Z : ℂ)) (ceCs * w) - 1‖ ≤
        C_k * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by
  have hcs0 : 0 < ceCs := ceCs_pos
  obtain ⟨Cg, hCg, hG_poly⟩ := convG1_le_poly
  have hm_int : Integrable (fun u : ℝ => Cg * (1 + |u|) ^ (-(5 / 2 : ℝ)) * |u| ^ (1 / 4 : ℝ)) := by
    have h94 : Integrable (fun u : ℝ => (1 + |u|) ^ (-(9 / 4 : ℝ))) := by
      have hdom : Integrable (fun u : ℝ => 2 * (1 + u ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul 2
      refine hdom.mono' (Measurable.aestronglyMeasurable (by measurability)) (ae_of_all _ fun u => ?_)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      calc (1 + |u|) ^ (-(9 / 4 : ℝ)) ≤ (1 + |u|) ^ (-2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg u]) (by norm_num)
        _ = ((1 + |u|) ^ 2)⁻¹ := by rw [Real.rpow_neg (by positivity), Real.rpow_two]
        _ ≤ (1 + u ^ 2)⁻¹ := by gcongr; nlinarith [abs_nonneg u, sq_abs u]
        _ ≤ 2 * (1 + u ^ 2)⁻¹ := by linarith [inv_nonneg.mpr (by positivity : 0 ≤ 1 + u ^ 2)]
    refine (h94.const_mul Cg).mono' (Measurable.aestronglyMeasurable (by measurability)) (ae_of_all _ fun u => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : |u| ^ (1 / 4 : ℝ) ≤ (1 + |u|) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (abs_nonneg u) (by linarith) (by norm_num)
    calc Cg * (1 + |u|) ^ (-(5 / 2 : ℝ)) * |u| ^ (1 / 4 : ℝ)
        ≤ Cg * (1 + |u|) ^ (-(5 / 2 : ℝ)) * (1 + |u|) ^ (1 / 4 : ℝ) := by gcongr
      _ = Cg * ((1 + |u|) ^ (-(5 / 2 : ℝ)) * (1 + |u|) ^ (1 / 4 : ℝ)) := by ring
      _ = Cg * (1 + |u|) ^ (-(9 / 4 : ℝ)) := by
          rw [← Real.rpow_add (by positivity)]; norm_num
  set Mk : ℝ := ∫ u : ℝ, Cg * (1 + |u|) ^ (-(5 / 2 : ℝ)) * |u| ^ (1 / 4 : ℝ)
  have hMk_nn : 0 ≤ Mk := integral_nonneg fun u => by positivity
  refine ⟨2 * ceCs ^ (1 / 4 : ℝ) * (Mk + 1),
    mul_pos (mul_pos two_pos (Real.rpow_pos_of_pos hcs0 _)) (by linarith), fun {c} hc w => ?_⟩
  have hc0 : 0 < c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have h_one : (1 : ℂ) = ∫ Z : ℝ, (rescaledG1 (liftEps c) Z : ℂ) := by
    rw [integral_complex_ofReal, rescaledG1_integral hε0]; simp
  have hint_ker : Integrable (fun Z : ℝ => Complex.exp (-(Complex.I * ((Z * (ceCs * w) : ℝ) : ℂ))) *
      (rescaledG1 (liftEps c) Z : ℂ)) := by
    have h1 := Complex.ofRealCLM.integrable_comp (rescaledG1_integrable hε0)
    refine h1.norm.mono' ((by fun_prop : Continuous fun Z : ℝ => Complex.exp (-(Complex.I * ((Z * (ceCs * w) : ℝ) : ℂ)))).aestronglyMeasurable.mul h1.aestronglyMeasurable) (ae_of_all _ fun Z => ?_)
    rw [norm_mul, show -(Complex.I * ((Z * (ceCs * w) : ℝ) : ℂ)) = ((-(Z * (ceCs * w)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul, Complex.ofRealCLM_apply]
  have hint_rescaled : Integrable (fun Z : ℝ => (rescaledG1 (liftEps c) Z : ℂ)) :=
    Complex.ofRealCLM.integrable_comp (rescaledG1_integrable hε0)
  rw [fourierPaper, h_one, ← integral_sub hint_ker hint_rescaled]
  have h_rewrite : (fun Z : ℝ =>
      Complex.exp (-(Complex.I * ((Z * (ceCs * w) : ℝ) : ℂ))) * (rescaledG1 (liftEps c) Z : ℂ) -
        (rescaledG1 (liftEps c) Z : ℂ)) =
      fun Z : ℝ => (rescaledG1 (liftEps c) Z : ℂ) *
        (Complex.exp ((-(Z * (ceCs * w)) : ℝ) * Complex.I) - 1) := by
    funext Z; push_cast; ring_nf
  rw [h_rewrite]
  have hcov := Measure.integral_comp_mul_left
    (fun u : ℝ => (ceG1 (airyZero 1) u : ℂ) * (Complex.exp (((liftEps c ^ 2 * ceCs * w * u : ℝ) : ℂ) * Complex.I) - 1))
    (-(liftEps c ^ 2)⁻¹)
  simp only [abs_inv, abs_neg, abs_of_pos (pow_pos hε0 2), inv_inv, Complex.real_smul] at hcov
  have heq_integrand : (fun Z : ℝ => (rescaledG1 (liftEps c) Z : ℂ) *
      (Complex.exp ((-(Z * (ceCs * w)) : ℝ) * Complex.I) - 1)) =
      fun Z : ℝ => (((liftEps c ^ 2)⁻¹ : ℝ) : ℂ) *
        ((ceG1 (airyZero 1) (-(liftEps c ^ 2)⁻¹ * Z) : ℂ) *
          (Complex.exp (((liftEps c ^ 2 * ceCs * w * (-(liftEps c ^ 2)⁻¹ * Z) : ℝ) : ℂ) * Complex.I) - 1)) := by
    funext Z
    have hε2_ne : liftEps c ^ 2 ≠ 0 := pow_ne_zero 2 hε0.ne'
    have harg1 : -Z / liftEps c ^ 2 = -(liftEps c ^ 2)⁻¹ * Z := by ring
    have harg2 : liftEps c ^ 2 * ceCs * w * (-(liftEps c ^ 2)⁻¹ * Z) = -(Z * (ceCs * w)) := by
      field_simp [hε2_ne]
    simp only [rescaledG1, harg1, harg2]
    push_cast; ring
  rw [heq_integrand, integral_const_mul]
  have hcov_simp : (((liftEps c ^ 2)⁻¹ : ℝ) : ℂ) *
      ∫ Z : ℝ, (ceG1 (airyZero 1) (-(liftEps c ^ 2)⁻¹ * Z) : ℂ) *
        (Complex.exp (((liftEps c ^ 2 * ceCs * w * (-(liftEps c ^ 2)⁻¹ * Z) : ℝ) : ℂ) * Complex.I) - 1) =
      ∫ u : ℝ, (ceG1 (airyZero 1) u : ℂ) *
        (Complex.exp (((liftEps c ^ 2 * ceCs * w * u : ℝ) : ℂ) * Complex.I) - 1) := by
    have hε2_ne : liftEps c ^ 2 ≠ 0 := pow_ne_zero 2 hε0.ne'
    have hc' : (∫ Z : ℝ, (ceG1 (airyZero 1) (-(liftEps c ^ 2)⁻¹ * Z) : ℂ) *
          (Complex.exp (((liftEps c ^ 2 * ceCs * w * (-(liftEps c ^ 2)⁻¹ * Z) : ℝ) : ℂ) * Complex.I) - 1)) =
        ((liftEps c ^ 2 : ℝ) : ℂ) * ∫ u : ℝ, (ceG1 (airyZero 1) u : ℂ) *
          (Complex.exp (((liftEps c ^ 2 * ceCs * w * u : ℝ) : ℂ) * Complex.I) - 1) := by
      simpa only [Complex.real_smul] using hcov
    rw [hc', ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hε2_ne, Complex.ofReal_one, one_mul]
  rw [hcov_simp]
  have h_ptwise : ∀ u : ℝ,
      ‖(ceG1 (airyZero 1) u : ℂ) * (Complex.exp (((liftEps c ^ 2 * ceCs * w * u : ℝ) : ℂ) * Complex.I) - 1)‖ ≤
        (2 * ceCs ^ (1 / 4 : ℝ) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ)) *
          (Cg * (1 + |u|) ^ (-(5 / 2 : ℝ)) * |u| ^ (1 / 4 : ℝ)) := by
    intro u
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (convG1_nonneg u)]
    have h_exp := norm_exp_I_mul_sub_one_le_two_rpow (liftEps c ^ 2 * ceCs * w * u)
    have h_abs : |liftEps c ^ 2 * ceCs * w * u| ^ (1 / 4 : ℝ) =
        c ^ (-(1 / 6 : ℝ)) * ceCs ^ (1 / 4 : ℝ) * |w| ^ (1 / 4 : ℝ) * |u| ^ (1 / 4 : ℝ) := by
      have hε2 : liftEps c ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
        unfold liftEps
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
      have hc_16 : (c ^ (-(2 / 3 : ℝ))) ^ (1 / 4 : ℝ) = c ^ (-(1 / 6 : ℝ)) := by
        rw [← Real.rpow_mul hc0.le]; norm_num
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (pow_pos hε0 2), abs_of_pos hcs0, hε2,
        Real.mul_rpow (by positivity) (abs_nonneg u),
        Real.mul_rpow (by positivity) (abs_nonneg w),
        Real.mul_rpow (Real.rpow_nonneg hc0.le _) hcs0.le, hc_16]
    have hG := hG_poly u
    calc ceG1 (airyZero 1) u * ‖Complex.exp (((liftEps c ^ 2 * ceCs * w * u : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ (Cg * (1 + |u|) ^ (-(5 / 2 : ℝ))) * (2 * |liftEps c ^ 2 * ceCs * w * u| ^ (1 / 4 : ℝ)) := by
          gcongr
      _ = _ := by rw [h_abs]; ring
  have hint_lhs : Integrable (fun u : ℝ =>
      ‖(ceG1 (airyZero 1) u : ℂ) * (Complex.exp (((liftEps c ^ 2 * ceCs * w * u : ℝ) : ℂ) * Complex.I) - 1)‖) := by
    refine (hm_int.const_mul (2 * ceCs ^ (1 / 4 : ℝ) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ))).mono' ?_
      (ae_of_all _ fun u => ?_)
    · have hmeas := (Complex.ofRealCLM.integrable_comp ceG1_integrable).aestronglyMeasurable
      exact (hmeas.mul (by fun_prop)).norm
    · rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact h_ptwise u
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono hint_lhs (hm_int.const_mul _) h_ptwise).trans ?_
  rw [integral_const_mul]
  change (2 * ceCs ^ (1 / 4 : ℝ) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ)) * Mk ≤
      (2 * ceCs ^ (1 / 4 : ℝ) * (Mk + 1)) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ)
  have h1 : 0 ≤ ceCs ^ (1 / 4 : ℝ) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by positivity
  nlinarith

/-! ### 5. Fourier inversion and `mainTransferOp_fourier_approx` -/

lemma fourierPaper_inversion_at {g g' : ℝ → ℝ} (hg_cont : Continuous g) (hg1 : Integrable g)
    (hweak : WeakDerivL2 (fun x => (g x : ℂ)) (fun x => (g' x : ℂ))) (L : ℝ) :
    Integrable (fun w : ℝ => fourierPaper (fun x => (g x : ℂ)) (ceCs * w)) ∧
      ((ceCs⁻¹ * g (L / ceCs) : ℝ) : ℂ) =
        (1 / (2 * Real.pi) : ℝ) •
          ∫ w : ℝ, fourierPaper (fun x => (g x : ℂ)) (ceCs * w) * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ)) := by
  have hgC1 : Integrable (fun x => (g x : ℂ)) := Complex.ofRealCLM.integrable_comp hg1
  have hfL1 := (fourierPaper_L1_le_sqrt_mul_H1 hgC1 hweak).1
  have hcs0 : ceCs ≠ 0 := ceCs_pos.ne'
  have h_w_int : Integrable (fun w : ℝ => fourierPaper (fun x => (g x : ℂ)) (ceCs * w)) :=
    (integrable_comp_mul_left_iff _ hcs0).mpr hfL1
  refine ⟨h_w_int, ?_⟩
  have hFi : Integrable (𝓕 (fun x : ℝ => (g x : ℂ))) := by
    have heq : 𝓕 (fun x : ℝ => (g x : ℂ)) =
        fun η : ℝ => fourierPaper (fun x => (g x : ℂ)) (2 * Real.pi * η) := funext fun η => by
      rw [Real.fourier_real_eq_integral_exp_smul]; unfold fourierPaper; congr 1; funext x
      rw [smul_eq_mul]; congr 2; push_cast; ring
    rw [heq]
    exact (integrable_comp_mul_left_iff _ (by positivity : (2 * Real.pi) ≠ 0)).mpr hfL1
  have hinv := (Complex.continuous_ofReal.comp hg_cont).fourierInv_fourier_eq hgC1 hFi
  have hpt := congrFun hinv (L / ceCs)
  rw [Real.fourierInv_eq'] at hpt
  change (∫ v : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ v (L / ceCs)) * Complex.I) • 𝓕 (fun x : ℝ => (g x : ℂ)) v) =
      (g (L / ceCs) : ℂ) at hpt
  set β : ℝ := ceCs / (2 * Real.pi) with hβ_def
  have hβ_pos : 0 < β := div_pos ceCs_pos (by positivity)
  have hcov := Measure.integral_comp_mul_left
    (fun η : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ η (L / ceCs)) * Complex.I) * 𝓕 (fun x : ℝ => (g x : ℂ)) η) β
  simp only [abs_inv, abs_of_pos hβ_pos, Complex.real_smul] at hcov
  have h_int_eq : (fun w : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ (β * w) (L / ceCs)) * Complex.I) *
        𝓕 (fun x : ℝ => (g x : ℂ)) (β * w)) =
      fun w : ℝ => fourierPaper (fun x => (g x : ℂ)) (ceCs * w) * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ)) := by
    funext w
    have hfour : 𝓕 (fun x : ℝ => (g x : ℂ)) (β * w) = fourierPaper (fun x => (g x : ℂ)) (ceCs * w) := by
      rw [Real.fourier_real_eq_integral_exp_smul]; unfold fourierPaper; congr 1; funext x
      rw [smul_eq_mul]; congr 2; rw [hβ_def]; push_cast; field_simp [Real.pi_ne_zero]
    have hexp : Complex.exp (↑(2 * Real.pi * inner ℝ (β * w) (L / ceCs)) * Complex.I) =
        Complex.exp (Complex.I * ((L * w : ℝ) : ℂ)) := by
      congr 1
      simp only [RCLike.inner_apply, conj_trivial]
      rw [hβ_def]; push_cast; field_simp [Real.pi_ne_zero, hcs0]
    rw [hfour, hexp, mul_comm]
  rw [h_int_eq] at hcov
  have hcov_mul : ∫ η : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ η (L / ceCs)) * Complex.I) * 𝓕 (fun x : ℝ => (g x : ℂ)) η =
      (β : ℂ) * ∫ w : ℝ, fourierPaper (fun x => (g x : ℂ)) (ceCs * w) * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ)) := by
    rw [hcov, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hβ_pos.ne', Complex.ofReal_one, one_mul]
  calc ((ceCs⁻¹ * g (L / ceCs) : ℝ) : ℂ)
      = (ceCs : ℂ)⁻¹ * (g (L / ceCs) : ℂ) := by push_cast; ring
    _ = (ceCs : ℂ)⁻¹ * ∫ η : ℝ,
          Complex.exp (↑(2 * Real.pi * inner ℝ η (L / ceCs)) * Complex.I) • 𝓕 (fun x : ℝ => (g x : ℂ)) η := by
        rw [← hpt]
    _ = (ceCs : ℂ)⁻¹ * ((β : ℂ) *
          ∫ w : ℝ, fourierPaper (fun x => (g x : ℂ)) (ceCs * w) * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ))) := by
        have hsm : ∀ η : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ η (L / ceCs)) * Complex.I) • 𝓕 (fun x : ℝ => (g x : ℂ)) η =
            Complex.exp (↑(2 * Real.pi * inner ℝ η (L / ceCs)) * Complex.I) * 𝓕 (fun x : ℝ => (g x : ℂ)) η := fun _ => rfl
        simp_rw [hsm]
        rw [hcov_mul]
    _ = (1 / (2 * Real.pi) : ℝ) •
          ∫ w : ℝ, fourierPaper (fun x => (g x : ℂ)) (ceCs * w) * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ)) := by
        rw [Complex.real_smul, ← mul_assoc, hβ_def]; push_cast; field_simp [hcs0, Real.pi_ne_zero]

lemma integrable_rpow_half_div_one_add_sq :
    Integrable (fun t : ℝ => |t| ^ (1 / 2 : ℝ) / (1 + t ^ 2)) := by
  have hcont : Continuous (fun t : ℝ => |t| ^ (1 / 2 : ℝ) / (1 + t ^ 2)) :=
    (continuous_abs.rpow_const (fun _ => Or.inr (by norm_num))).div (by fun_prop) (fun t => by positivity)
  have h_pos : IntegrableOn (fun t : ℝ => |t| ^ (1 / 2 : ℝ) / (1 + t ^ 2)) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) zero_lt_one).mono'
      hcont.aestronglyMeasurable.restrict (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : 0 < t := zero_lt_one.trans ht1
    rw [Real.norm_of_nonneg (by positivity), abs_of_pos ht0]
    calc t ^ (1 / 2 : ℝ) / (1 + t ^ 2) ≤ t ^ (1 / 2 : ℝ) / t ^ 2 := by gcongr; linarith
      _ = t ^ (-(3 / 2 : ℝ)) := by
          rw [div_eq_mul_inv, ← Real.rpow_natCast t 2, ← Real.rpow_neg ht0.le, ← Real.rpow_add ht0]; norm_num
  have h_neg : IntegrableOn (fun t : ℝ => |t| ^ (1 / 2 : ℝ) / (1 + t ^ 2)) (Iio (-1)) := by
    have hcomp := h_pos.comp_neg
    have hset : -Ioi (1 : ℝ) = Iio (-1 : ℝ) := by ext t; simp [lt_neg]
    rw [hset] at hcomp
    refine hcomp.congr_fun (fun t _ => by simp [abs_neg]) measurableSet_Iio
  have h_mid : IntegrableOn (fun t : ℝ => |t| ^ (1 / 2 : ℝ) / (1 + t ^ 2)) (Icc (-1) 1) :=
    hcont.continuousOn.integrableOn_Icc
  have hU : (Iio (-1 : ℝ) ∪ Icc (-1) 1) ∪ Ioi 1 = (univ : Set ℝ) := by
    ext t
    simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    by_cases h1 : t < -1
    · left; left; exact h1
    · by_cases h2 : t ≤ 1
      · left; right; exact ⟨not_lt.mp h1, h2⟩
      · right; exact not_le.mp h2
  rw [← integrableOn_univ, ← hU]
  exact (h_neg.union h_mid).union h_pos

theorem mainTransferOp_fourier_approx {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ C_f > 0, ∀ {c L : ℝ} {g g' : ℝ → ℝ}, 1 ≤ c → 0 < L →
      Continuous g → Integrable g → Integrable g' →
      (∀ x : ℝ, HasDerivAt g (g' x) x) →
      (∃ Mg Mg' : ℝ, 0 ≤ Mg ∧ 0 ≤ Mg' ∧ (∀ x, |g x| ≤ Mg) ∧ (∀ x, |g' x| ≤ Mg')) →
      ‖mainTransferOp κ m c (fun X => (realConv g (rescaledG1 (liftEps c)) X : ℂ)) L -
          ((ceCs⁻¹ * g (L / ceCs) : ℝ) : ℂ)‖ ≤
        C_f * c ^ (-(1 / 6 : ℝ)) * L ^ (1 / 4 : ℝ) *
          Real.sqrt (L ^ (-2 : ℝ) * (∫ x : ℝ, |g x| ^ 2) + ∫ x : ℝ, |g' x| ^ 2) := by
  have hcs0 : 0 < ceCs := ceCs_pos
  obtain ⟨hcd, _, _, _⟩ := mainEdgeAmp_contDiff_and_bound hκ hm
  obtain ⟨C_m, hCm, hM_bd⟩ := norm_mainEdgeAmp_phase_sub_one_le hκ hm
  obtain ⟨C_k, hCk, hk_bd⟩ := norm_rescaledG1_fourier_sub_one_le
  set I0 : ℝ := ∫ t : ℝ, |t| ^ (1 / 2 : ℝ) / (1 + t ^ 2)
  have hI0_nn : 0 ≤ I0 := integral_nonneg fun t => by positivity
  have hcs1 : 1 ≤ ceCs := by
    have h3 : (1 : ℝ) ≤ ceCs ^ 3 := by
      unfold ceCs
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
      have hpi : 2 ≤ Real.pi := Real.two_le_pi
      nlinarith
    by_contra hlt
    rw [not_le] at hlt
    have : ceCs ^ 3 < 1 := pow_lt_one₀ ceCs_pos.le hlt (by norm_num)
    linarith
  have hcf_pos : 0 < ((C_m + C_k) / (2 * Real.pi)) * Real.sqrt (max I0 1 * (2 * Real.pi / ceCs)) := by
    positivity
  refine ⟨((C_m + C_k) / (2 * Real.pi)) * Real.sqrt (max I0 1 * (2 * Real.pi / ceCs)), hcf_pos,
    fun {c L g g'} hc hL hg_cont hg1 hg'1 hderiv ⟨Mg, Mg', hMg, hMg', hgM, hg'M⟩ => ?_⟩
  have hc0 : 0 < c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  let k : ℝ → ℝ := rescaledG1 (liftEps c)
  have hk1 : Integrable k := rescaledG1_integrable hε0
  have hk_cont : Continuous k := rescaledG1_continuous hε0
  let f : ℝ → ℂ := fun X => (realConv g k X : ℂ)
  let f' : ℝ → ℂ := fun X => (realConv g' k X : ℂ)
  have hf1 : Integrable f := Complex.ofRealCLM.integrable_comp (integrable_realConv hg1 hk1)
  have hf_weak : WeakDerivL2 f f' := weakDerivL2_realConv hg1 hg'1 hk1 hMg hMg' hgM hg'M hderiv
  have hg_weak : WeakDerivL2 (fun x => (g x : ℂ)) (fun x => (g' x : ℂ)) :=
    weakDerivL2_of_hasDerivAt hg1 hg'1 hgM hg'M hderiv
  have hmult := mainTransferOp_eq_fourier_multiplier hκ (by omega) hc hf1 hf_weak L
  obtain ⟨h_w_int, hinv⟩ := fourierPaper_inversion_at hg_cont hg1 hg_weak L
  have hfourier_conv : ∀ w : ℝ,
      fourierPaper f (ceCs * w) =
        fourierPaper (fun x => (g x : ℂ)) (ceCs * w) * fourierPaper (fun Z => (k Z : ℂ)) (ceCs * w) := fun w =>
    fourierPaper_realConv hg1 hk1 hg_cont hk_cont (ceCs * w)
  let M : ℝ → ℂ := fun w =>
    mainEdgeAmp κ m c (w / c) * Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ))
  let K : ℝ → ℂ := fun w => fourierPaper (fun Z => (k Z : ℂ)) (ceCs * w)
  let G : ℝ → ℂ := fun w => fourierPaper (fun x => (g x : ℂ)) (ceCs * w)
  have hM_cont : Continuous M :=
    ((hcd hc).continuous.comp (continuous_id.div_const c)).mul
      (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_const.mul (edgeR_contDiff.continuous.comp (continuous_id.div_const c))))))
  have hM1 : ∀ w : ℝ, ‖M w‖ ≤ 1 := fun w => by
    rw [norm_mul, show Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ) = ((c * edgeR (w / c) : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact (norm_mainEdgeAmp_le κ m hc0 (w / c)).2
  have hK1 : ∀ w : ℝ, ‖K w‖ ≤ 1 := fun w => norm_fourierPaper_rescaledG1_le hε0 (ceCs * w)
  have h_MK_sub : ∀ w : ℝ, ‖M w * K w - 1‖ ≤ (C_m + C_k) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := fun w => by
    calc ‖M w * K w - 1‖ = ‖(M w - 1) * K w + (K w - 1)‖ := by ring_nf
      _ ≤ ‖(M w - 1) * K w‖ + ‖K w - 1‖ := norm_add_le _ _
      _ ≤ ‖M w - 1‖ * 1 + ‖K w - 1‖ := by rw [norm_mul]; gcongr; exact hK1 w
      _ = ‖M w - 1‖ + ‖K w - 1‖ := by ring
      _ ≤ C_m * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) + C_k * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) :=
          add_le_add (hM_bd hc w) (hk_bd hc w)
      _ = (C_m + C_k) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ) := by ring
  have hint1 : Integrable (fun w : ℝ => M w * K w * G w * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ))) := by
    have hfL1 := (fourierPaper_L1_le_sqrt_mul_H1 hf1 hf_weak).1
    have hf_w : Integrable (fun w : ℝ => fourierPaper f (ceCs * w)) :=
      (integrable_comp_mul_left_iff _ hcs0.ne').mpr hfL1
    have h_eq : (fun w : ℝ => M w * K w * G w * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ))) =
        fun w => M w * fourierPaper f (ceCs * w) * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ)) := by
      funext w; dsimp [K, G]; rw [hfourier_conv w]; ring
    rw [h_eq]
    refine hf_w.norm.mono' ((hM_cont.aestronglyMeasurable.mul hf_w.aestronglyMeasurable).mul (by fun_prop))
      (ae_of_all _ fun w => ?_)
    have hexp : ‖Complex.exp (Complex.I * ((L * w : ℝ) : ℂ))‖ = 1 := by
      rw [show Complex.I * ((L * w : ℝ) : ℂ) = ((L * w : ℝ) : ℂ) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, norm_mul, hexp, mul_one]
    exact mul_le_of_le_one_left (norm_nonneg _) (hM1 w)
  have hint2 : Integrable (fun w : ℝ => G w * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ))) := by
    refine h_w_int.norm.mono' (h_w_int.aestronglyMeasurable.mul (by fun_prop)) (ae_of_all _ fun w => ?_)
    rw [norm_mul, show Complex.I * ((L * w : ℝ) : ℂ) = ((L * w : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hdiff_eq : mainTransferOp κ m c f L - ((ceCs⁻¹ * g (L / ceCs) : ℝ) : ℂ) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ w : ℝ, (M w * K w - 1) * G w * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ)) := by
    rw [hmult, hinv, ← smul_sub, ← integral_sub ?_ hint2]
    · congr 2; funext w
      have hw : mainEdgeAmp κ m c (w / c) * Complex.exp (Complex.I * ((c * edgeR (w / c) : ℝ) : ℂ)) *
          fourierPaper f (ceCs * w) * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ)) =
          M w * K w * G w * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ)) := by
        dsimp [M, K, G]; rw [hfourier_conv w]; ring
      rw [hw]; ring
    · refine hint1.congr (ae_of_all _ fun w => ?_)
      dsimp [M, K, G]; rw [hfourier_conv w]; ring
  let α : ℝ := L⁻¹
  have hα : 0 < α := inv_pos.mpr hL
  let φ : ℝ → ℝ := fun w => |w| ^ (1 / 2 : ℝ) / (α ^ 2 + w ^ 2)
  have h_scale_pt : ∀ w : ℝ, φ w = α ^ (-(3 / 2 : ℝ)) * (|α⁻¹ * w| ^ (1 / 2 : ℝ) / (1 + (α⁻¹ * w) ^ 2)) := fun w => by
    dsimp [φ]
    have h_abs : |α⁻¹ * w| ^ (1 / 2 : ℝ) = α ^ (-(1 / 2 : ℝ)) * |w| ^ (1 / 2 : ℝ) := by
      rw [abs_mul, abs_inv, abs_of_pos hα, Real.mul_rpow (inv_nonneg.mpr hα.le) (abs_nonneg w),
        Real.inv_rpow hα.le, Real.rpow_neg hα.le]
    have h_den : 1 + (α⁻¹ * w) ^ 2 = α ^ (-2 : ℝ) * (α ^ 2 + w ^ 2) := by
      rw [Real.rpow_neg hα.le, Real.rpow_two]; field_simp [hα.ne']
    rw [h_abs, h_den]
    have hpow : α ^ (-(3 / 2 : ℝ)) * α ^ (-(1 / 2 : ℝ)) / α ^ (-2 : ℝ) = 1 := by
      rw [← Real.rpow_add hα, div_eq_mul_inv, ← Real.rpow_neg hα.le, ← Real.rpow_add hα]
      norm_num
    have hden_ne : α ^ (-2 : ℝ) * (α ^ 2 + w ^ 2) ≠ 0 := by positivity
    have h_rew : α ^ (-(3 / 2 : ℝ)) * (α ^ (-(1 / 2 : ℝ)) * |w| ^ (1 / 2 : ℝ) / (α ^ (-2 : ℝ) * (α ^ 2 + w ^ 2))) =
        (α ^ (-(3 / 2 : ℝ)) * α ^ (-(1 / 2 : ℝ)) / α ^ (-2 : ℝ)) * (|w| ^ (1 / 2 : ℝ) / (α ^ 2 + w ^ 2)) := by
      field_simp [hα.ne', hden_ne]
    rw [h_rew, hpow, one_mul]
  have hφ_int : Integrable φ := by
    have hcov := (integrable_rpow_half_div_one_add_sq).comp_mul_left' (inv_ne_zero hα.ne')
    exact (hcov.const_mul (α ^ (-(3 / 2 : ℝ)))).congr (ae_of_all _ fun w => (h_scale_pt w).symm)
  have hφ_val : ∫ w : ℝ, φ w = L ^ (1 / 2 : ℝ) * I0 := by
    have hcov := Measure.integral_comp_mul_left (fun t : ℝ => |t| ^ (1 / 2 : ℝ) / (1 + t ^ 2)) α⁻¹
    simp only [abs_of_pos hα, inv_inv, smul_eq_mul] at hcov
    have h_eq : ∫ w : ℝ, φ w = α ^ (-(3 / 2 : ℝ)) * ∫ w : ℝ, |α⁻¹ * w| ^ (1 / 2 : ℝ) / (1 + (α⁻¹ * w) ^ 2) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ h_scale_pt)
    rw [h_eq, hcov, ← mul_assoc]
    have hpowL : α ^ (-(3 / 2 : ℝ)) * α = L ^ (1 / 2 : ℝ) := by
      calc α ^ (-(3 / 2 : ℝ)) * α = α ^ (-(3 / 2 : ℝ)) * α ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = α ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hα]; norm_num
        _ = L ^ (1 / 2 : ℝ) := by dsimp [α]; rw [Real.inv_rpow hL.le, Real.rpow_neg hL.le, inv_inv]
    rw [hpowL]
  obtain ⟨hFL1, hPlanchDeriv, hPlanchL2⟩ := integrable_fourier_H1 hg_weak
  let FL2 : ℝ → ℂ := ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hg_weak.memLp.toLp (fun x => (g x : ℂ))) : Lp ℂ 2 volume) : ℝ → ℂ)
  have hgC1 : Integrable (fun x => (g x : ℂ)) := Complex.ofRealCLM.integrable_comp hg1
  have hae_G : G =ᵐ[volume] fun w : ℝ => FL2 (((2 * Real.pi)⁻¹ * ceCs) * w) := by
    have hae := fourierPaperL2_ae_eq_fourierPaper hgC1 hg_weak
    rw [EventuallyEq, ae_iff]
    have hsub : {w : ℝ | ¬G w = FL2 ((2 * Real.pi)⁻¹ * ceCs * w)} =
        ceCs⁻¹ • {ξ : ℝ | ¬fourierPaperL2 hg_weak ξ = fourierPaper (fun x => (g x : ℂ)) ξ} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hcs0.ne'),
        inv_inv, smul_eq_mul, G, fourierPaperL2, FL2]
      rw [mul_assoc, eq_comm]
    have h0 : volume {ξ : ℝ | ¬fourierPaperL2 hg_weak ξ = fourierPaper (fun x => (g x : ℂ)) ξ} = 0 :=
      ae_iff.mp hae
    rw [hsub, Measure.addHaar_smul, h0, mul_zero]
  let ψ : ℝ → ℝ := fun w => (α ^ 2 + w ^ 2) * ‖G w‖ ^ 2
  have hFL2_2 : Integrable (fun η : ℝ => ‖FL2 η‖ ^ 2) := (Lp.memLp _).integrable_norm_pow two_ne_zero
  have hFL2_x2 : Integrable (fun η : ℝ => η ^ 2 * ‖FL2 η‖ ^ 2) := by
    have hG2 : Integrable (fun η : ℝ => ‖((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
        (hg_weak.memLp_deriv.toLp (fun x => (g' x : ℂ))) : Lp ℂ 2 volume) : ℝ → ℂ) η‖ ^ 2) :=
      (Lp.memLp _).integrable_norm_pow two_ne_zero
    have hae_d := fourierL2Deriv_ae hg_weak
    refine (hG2.const_mul (((2 * Real.pi) ^ 2)⁻¹)).congr ?_
    filter_upwards [hae_d] with η hη
    rw [hη, norm_mul]
    have hn : ‖2 * (Real.pi : ℂ) * Complex.I * (η : ℂ)‖ = 2 * Real.pi * |η| := by
      simp [Complex.norm_real, abs_of_pos Real.pi_pos]
    rw [hn]
    simp only [mul_pow, sq_abs]
    field_simp [Real.pi_ne_zero]
    rfl
  let γ : ℝ := (2 * Real.pi)⁻¹ * ceCs
  have hγ_pos : 0 < γ := by positivity
  have hψ_int : Integrable ψ := by
    have h1 : Integrable (fun w : ℝ => (α ^ 2 + (2 * Real.pi / ceCs) ^ 2 * (γ * w) ^ 2) * ‖FL2 (γ * w)‖ ^ 2) := by
      have ha1 := (hFL2_2.comp_mul_left' hγ_pos.ne').const_mul (α ^ 2)
      have hx1 := (hFL2_x2.comp_mul_left' hγ_pos.ne').const_mul ((2 * Real.pi / ceCs) ^ 2)
      refine (ha1.add hx1).congr (ae_of_all _ fun w => ?_)
      change α ^ 2 * ‖FL2 (γ * w)‖ ^ 2 + (2 * Real.pi / ceCs) ^ 2 * ((γ * w) ^ 2 * ‖FL2 (γ * w)‖ ^ 2) = _
      ring
    refine h1.congr ?_
    filter_upwards [hae_G] with w hw
    dsimp [ψ]
    rw [hw]
    have hwγ : w ^ 2 = (2 * Real.pi / ceCs) ^ 2 * (γ * w) ^ 2 := by
      dsimp [γ]; field_simp [Real.pi_ne_zero, hcs0.ne']
    rw [hwγ]
  have hψ_val : ∫ w : ℝ, ψ w ≤ (2 * Real.pi / ceCs) * (L ^ (-2 : ℝ) * (∫ x : ℝ, |g x| ^ 2) + ∫ x : ℝ, |g' x| ^ 2) := by
    have hae_ψ : ψ =ᵐ[volume] fun w : ℝ =>
        α ^ 2 * ‖FL2 (γ * w)‖ ^ 2 + (2 * Real.pi / ceCs) ^ 2 * ((γ * w) ^ 2 * ‖FL2 (γ * w)‖ ^ 2) := by
      filter_upwards [hae_G] with w hw
      dsimp [ψ]
      rw [hw]
      have hwγ : w ^ 2 = (2 * Real.pi / ceCs) ^ 2 * (γ * w) ^ 2 := by
        dsimp [γ]; field_simp [Real.pi_ne_zero, hcs0.ne']
      rw [hwγ]; ring
    rw [integral_congr_ae hae_ψ, integral_add ((hFL2_2.comp_mul_left' hγ_pos.ne').const_mul _)
        ((hFL2_x2.comp_mul_left' hγ_pos.ne').const_mul _),
      integral_const_mul, integral_const_mul]
    have hcov1 := Measure.integral_comp_mul_left (fun η : ℝ => ‖FL2 η‖ ^ 2) γ
    have hcov2 := Measure.integral_comp_mul_left (fun η : ℝ => η ^ 2 * ‖FL2 η‖ ^ 2) γ
    simp only [abs_inv, abs_of_pos hγ_pos, smul_eq_mul] at hcov1 hcov2
    have hγ_inv : γ⁻¹ = 2 * Real.pi / ceCs := by dsimp [γ]; field_simp [Real.pi_ne_zero, hcs0.ne']
    rw [hcov1, hcov2, hγ_inv]
    have hg_sq : ∫ x : ℝ, ‖(g x : ℂ)‖ ^ 2 = ∫ x : ℝ, |g x| ^ 2 :=
      integral_congr_ae (ae_of_all _ fun x => by dsimp only; rw [Complex.norm_real, Real.norm_eq_abs])
    have hg'_sq : ∫ x : ℝ, ‖(g' x : ℂ)‖ ^ 2 = ∫ x : ℝ, |g' x| ^ 2 :=
      integral_congr_ae (ae_of_all _ fun x => by dsimp only; rw [Complex.norm_real, Real.norm_eq_abs])
    have hη_x2 : (2 * Real.pi / ceCs) ^ 2 * ((2 * Real.pi / ceCs) * ∫ η : ℝ, η ^ 2 * ‖FL2 η‖ ^ 2) =
        (2 * Real.pi / ceCs) * ceCs ^ (-2 : ℝ) * ∫ x : ℝ, |g' x| ^ 2 := by
      rw [← hg'_sq, ← hPlanchDeriv]
      have hcs2 : ceCs ^ (-2 : ℝ) = (ceCs ^ 2)⁻¹ := by rw [Real.rpow_neg hcs0.le, Real.rpow_two]
      rw [hcs2]; field_simp [Real.pi_ne_zero, hcs0.ne']; ring
    have hη_2 : α ^ 2 * ((2 * Real.pi / ceCs) * ∫ η : ℝ, ‖FL2 η‖ ^ 2) =
        (2 * Real.pi / ceCs) * (L ^ (-2 : ℝ) * ∫ x : ℝ, |g x| ^ 2) := by
      rw [hPlanchL2, hg_sq]
      have hL2 : L ^ (-2 : ℝ) = α ^ 2 := by
        dsimp [α]; rw [Real.rpow_neg hL.le, Real.rpow_two, inv_pow]
      rw [hL2]; ring
    rw [hη_x2, hη_2]
    have hcs_neg2 : ceCs ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hcs1 (by norm_num)
    have h_g'_nn : 0 ≤ ∫ x : ℝ, |g' x| ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have h_mul : (2 * Real.pi / ceCs) * ceCs ^ (-2 : ℝ) * ∫ x : ℝ, |g' x| ^ 2 ≤
        (2 * Real.pi / ceCs) * ∫ x : ℝ, |g' x| ^ 2 := by
      calc (2 * Real.pi / ceCs) * ceCs ^ (-2 : ℝ) * ∫ x : ℝ, |g' x| ^ 2
          ≤ (2 * Real.pi / ceCs) * 1 * ∫ x : ℝ, |g' x| ^ 2 := by gcongr
        _ = (2 * Real.pi / ceCs) * ∫ x : ℝ, |g' x| ^ 2 := by ring
    linarith
  let H : ℝ → ℝ := fun w => |w| ^ (1 / 4 : ℝ) * ‖G w‖
  have hH_meas : AEStronglyMeasurable H volume :=
    ((continuous_abs.rpow_const (fun _ => Or.inr (by norm_num))).aestronglyMeasurable).mul h_w_int.aestronglyMeasurable.norm
  have hH_amgm : ∀ t : ℝ, 0 < t → ∀ w : ℝ, H w ≤ (t * φ w + t⁻¹ * ψ w) / 2 := fun t ht w => by
    dsimp [H, φ, ψ]
    have hαw : 0 < α ^ 2 + w ^ 2 := by positivity
    have hsq : 0 ≤ (Real.sqrt (t / (α ^ 2 + w ^ 2)) * |w| ^ (1 / 4 : ℝ) -
        Real.sqrt (t⁻¹ * (α ^ 2 + w ^ 2)) * ‖G w‖) ^ 2 := sq_nonneg _
    have h1 : Real.sqrt (t / (α ^ 2 + w ^ 2)) ^ 2 = t / (α ^ 2 + w ^ 2) := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt (t⁻¹ * (α ^ 2 + w ^ 2)) ^ 2 = t⁻¹ * (α ^ 2 + w ^ 2) := Real.sq_sqrt (by positivity)
    have h14 : (|w| ^ (1 / 4 : ℝ)) ^ 2 = |w| ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg w)]; norm_num
    have hcross : Real.sqrt (t / (α ^ 2 + w ^ 2)) * Real.sqrt (t⁻¹ * (α ^ 2 + w ^ 2)) = 1 := by
      rw [← Real.sqrt_mul (by positivity)]
      have heq : (t / (α ^ 2 + w ^ 2)) * (t⁻¹ * (α ^ 2 + w ^ 2)) = 1 := by
        field_simp [ht.ne', hαw.ne']
      rw [heq, Real.sqrt_one]
    have h_exp_sq : (Real.sqrt (t / (α ^ 2 + w ^ 2)) * |w| ^ (1 / 4 : ℝ) -
        Real.sqrt (t⁻¹ * (α ^ 2 + w ^ 2)) * ‖G w‖) ^ 2 =
        t * (|w| ^ (1 / 2 : ℝ) / (α ^ 2 + w ^ 2)) + t⁻¹ * ((α ^ 2 + w ^ 2) * ‖G w‖ ^ 2) -
          2 * (|w| ^ (1 / 4 : ℝ) * ‖G w‖) := by
      calc (Real.sqrt (t / (α ^ 2 + w ^ 2)) * |w| ^ (1 / 4 : ℝ) -
              Real.sqrt (t⁻¹ * (α ^ 2 + w ^ 2)) * ‖G w‖) ^ 2
          = Real.sqrt (t / (α ^ 2 + w ^ 2)) ^ 2 * (|w| ^ (1 / 4 : ℝ)) ^ 2 +
              Real.sqrt (t⁻¹ * (α ^ 2 + w ^ 2)) ^ 2 * ‖G w‖ ^ 2 -
              2 * (Real.sqrt (t / (α ^ 2 + w ^ 2)) * Real.sqrt (t⁻¹ * (α ^ 2 + w ^ 2))) *
                (|w| ^ (1 / 4 : ℝ) * ‖G w‖) := by ring
        _ = (t / (α ^ 2 + w ^ 2)) * |w| ^ (1 / 2 : ℝ) +
              (t⁻¹ * (α ^ 2 + w ^ 2)) * ‖G w‖ ^ 2 - 2 * 1 * (|w| ^ (1 / 4 : ℝ) * ‖G w‖) := by
            rw [h1, h2, h14, hcross]
        _ = _ := by ring
    linarith [hsq, h_exp_sq]
  have hH_int : Integrable H := by
    refine ((hφ_int.add hψ_int).div_const 2).mono' hH_meas (ae_of_all _ fun w => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
    have h_le := hH_amgm 1 one_pos w
    rwa [one_mul, inv_one, one_mul] at h_le
  set A' : ℝ := L ^ (1 / 2 : ℝ) * max I0 1
  set B' : ℝ := (2 * Real.pi / ceCs) * (L ^ (-2 : ℝ) * (∫ x : ℝ, |g x| ^ 2) + ∫ x : ℝ, |g' x| ^ 2)
  have hA'_pos : 0 < A' := by positivity
  have hg_nn : 0 ≤ ∫ x : ℝ, |g x| ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hg'_nn : 0 ≤ ∫ x : ℝ, |g' x| ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hB'_nn : 0 ≤ B' := by positivity
  have h_amgm_int : ∀ t : ℝ, 0 < t → ∫ w : ℝ, H w ≤ (t * A' + t⁻¹ * B') / 2 := fun t ht => by
    have h_rhs_int : Integrable (fun w => (t * φ w + t⁻¹ * ψ w) / 2) :=
      ((hφ_int.const_mul t).add (hψ_int.const_mul t⁻¹)).div_const 2
    have hm1 := integral_mono hH_int h_rhs_int (hH_amgm t ht)
    rw [integral_div, integral_add (hφ_int.const_mul t) (hψ_int.const_mul t⁻¹),
      integral_const_mul, integral_const_mul, hφ_val] at hm1
    have hA_le : L ^ (1 / 2 : ℝ) * I0 ≤ A' := by dsimp [A']; gcongr; exact le_max_left _ _
    have htA : t * (L ^ (1 / 2 : ℝ) * I0) ≤ t * A' := mul_le_mul_of_nonneg_left hA_le ht.le
    have htB : t⁻¹ * ∫ w : ℝ, ψ w ≤ t⁻¹ * B' := mul_le_mul_of_nonneg_left hψ_val (by positivity)
    linarith
  have hH_le_sqrt : ∫ w : ℝ, H w ≤ Real.sqrt (A' * B') := by
    rcases eq_or_lt_of_le hB'_nn with hB0 | hBpos
    · rw [← hB0, mul_zero, Real.sqrt_zero]
      by_contra hlt
      rw [not_le] at hlt
      let ε_t : ℝ := (∫ w : ℝ, H w) / A'
      have hεt : 0 < ε_t := div_pos hlt hA'_pos
      have h1 := h_amgm_int ε_t hεt
      rw [← hB0, mul_zero, add_zero] at h1
      have h2 : ε_t * A' = ∫ w : ℝ, H w := by dsimp [ε_t]; field_simp [hA'_pos.ne']
      linarith
    · let t : ℝ := Real.sqrt (B' / A')
      have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hBpos hA'_pos)
      have ht2 : t ^ 2 = B' / A' := Real.sq_sqrt (div_nonneg hB'_nn hA'_pos.le)
      have h1 := h_amgm_int t ht
      have h_id : (t * A' + t⁻¹ * B') / 2 = Real.sqrt (A' * B') := by
        have htA : t * A' = Real.sqrt (A' * B') := by
          have hs : Real.sqrt (A' * B') ^ 2 = (t * A') ^ 2 := by
            rw [Real.sq_sqrt (mul_nonneg hA'_pos.le hB'_nn), mul_pow, ht2]
            field_simp [hA'_pos.ne']
          have hnn1 : 0 ≤ t * A' := by positivity
          have hnn2 : 0 ≤ Real.sqrt (A' * B') := Real.sqrt_nonneg _
          exact ((sq_eq_sq₀ hnn2 hnn1).mp hs).symm
        have htB : t⁻¹ * B' = Real.sqrt (A' * B') := by
          have heq : t⁻¹ * B' = t * A' := by
            rw [← mul_right_inj' ht.ne']
            calc t * (t⁻¹ * B') = (t * t⁻¹) * B' := by ring
              _ = B' := by rw [mul_inv_cancel₀ ht.ne', one_mul]
              _ = (B' / A') * A' := by field_simp [hA'_pos.ne']
              _ = t ^ 2 * A' := by rw [ht2]
              _ = t * (t * A') := by ring
          rw [heq, htA]
        rw [htA, htB]; ring
      rwa [h_id] at h1
  have hdiff_meas : AEStronglyMeasurable
      (fun w : ℝ => (M w * K w - 1) * G w * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ))) volume := by
    have h_eq : (fun w : ℝ => (M w * K w - 1) * G w * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ))) =
        fun w : ℝ => M w * K w * G w * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ)) -
          G w * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ)) := funext fun w => by ring
    rw [h_eq]
    exact hint1.aestronglyMeasurable.sub hint2.aestronglyMeasurable
  have hdiff_int : Integrable (fun w : ℝ =>
      ‖(M w * K w - 1) * G w * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ))‖) :=
    (hH_int.const_mul ((C_m + C_k) * c ^ (-(1 / 6 : ℝ)))).mono' hdiff_meas.norm (ae_of_all _ fun w => by
      have hexp : ‖Complex.exp (Complex.I * ((L * w : ℝ) : ℂ))‖ = 1 := by
        rw [show Complex.I * ((L * w : ℝ) : ℂ) = ((L * w : ℝ) : ℂ) * Complex.I by ring,
          Complex.norm_exp_ofReal_mul_I]
      rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul, norm_mul, hexp, mul_one]
      have hmk := h_MK_sub w
      calc ‖M w * K w - 1‖ * ‖G w‖
          ≤ ((C_m + C_k) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ)) * ‖G w‖ := by gcongr
        _ = (C_m + C_k) * c ^ (-(1 / 6 : ℝ)) * H w := by dsimp [H]; ring)
  rw [hdiff_eq, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc (1 / (2 * Real.pi)) * ‖∫ w : ℝ, (M w * K w - 1) * G w * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ))‖
      ≤ (1 / (2 * Real.pi)) * ∫ w : ℝ, ‖(M w * K w - 1) * G w * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ))‖ := by
        gcongr; exact norm_integral_le_integral_norm _
    _ ≤ (1 / (2 * Real.pi)) * ∫ w : ℝ, (C_m + C_k) * c ^ (-(1 / 6 : ℝ)) * H w := by
        refine mul_le_mul_of_nonneg_left
          (integral_mono hdiff_int (hH_int.const_mul ((C_m + C_k) * c ^ (-(1 / 6 : ℝ)))) fun w => ?_)
          (by positivity)
        have hexp : ‖Complex.exp (Complex.I * ((L * w : ℝ) : ℂ))‖ = 1 := by
          rw [show Complex.I * ((L * w : ℝ) : ℂ) = ((L * w : ℝ) : ℂ) * Complex.I by ring,
            Complex.norm_exp_ofReal_mul_I]
        rw [norm_mul, norm_mul, hexp, mul_one]
        calc ‖M w * K w - 1‖ * ‖G w‖
            ≤ ((C_m + C_k) * c ^ (-(1 / 6 : ℝ)) * |w| ^ (1 / 4 : ℝ)) * ‖G w‖ := by gcongr; exact h_MK_sub w
          _ = (C_m + C_k) * c ^ (-(1 / 6 : ℝ)) * H w := by dsimp [H]; ring
    _ = ((C_m + C_k) / (2 * Real.pi)) * c ^ (-(1 / 6 : ℝ)) * ∫ w : ℝ, H w := by
        rw [integral_const_mul]; ring
    _ ≤ ((C_m + C_k) / (2 * Real.pi)) * c ^ (-(1 / 6 : ℝ)) * Real.sqrt (A' * B') := by
        gcongr
    _ = ((C_m + C_k) / (2 * Real.pi)) * Real.sqrt (max I0 1 * (2 * Real.pi / ceCs)) * c ^ (-(1 / 6 : ℝ)) *
          L ^ (1 / 4 : ℝ) * Real.sqrt (L ^ (-2 : ℝ) * (∫ x : ℝ, |g x| ^ 2) + ∫ x : ℝ, |g' x| ^ 2) := by
        have hsqrt_split : Real.sqrt (A' * B') =
            L ^ (1 / 4 : ℝ) * Real.sqrt (max I0 1 * (2 * Real.pi / ceCs)) *
              Real.sqrt (L ^ (-2 : ℝ) * (∫ x : ℝ, |g x| ^ 2) + ∫ x : ℝ, |g' x| ^ 2) := by
          have hAB_eq : A' * B' = (L ^ (1 / 4 : ℝ)) ^ 2 *
              ((max I0 1 * (2 * Real.pi / ceCs)) * (L ^ (-2 : ℝ) * (∫ x : ℝ, |g x| ^ 2) + ∫ x : ℝ, |g' x| ^ 2)) := by
            dsimp [A', B']
            have hL14 : (L ^ (1 / 4 : ℝ)) ^ 2 = L ^ (1 / 2 : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; norm_num
            rw [hL14]; ring
          rw [hAB_eq, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
            Real.sqrt_mul (by positivity)]
          ring
        rw [hsqrt_split]; ring

/-- info: 'FormalResearch.SignUncertainty.iMain_eq_mainTransferOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.iMain_eq_mainTransferOp

/-- info: 'FormalResearch.SignUncertainty.mainTransferOp_split_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.mainTransferOp_split_error

/-- info: 'FormalResearch.SignUncertainty.mainTransferOp_fourier_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.mainTransferOp_fourier_approx

end FormalResearch.SignUncertainty
