module

public import FormalResearch.CohnElkies.MellinLiftIntegrals
public import Mathlib.Analysis.Fourier.Inversion

/-!
# Window smoothing of a seed and the exact Airy inversion identity

Source: `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, `(e28)` (`M_ψ`, `W`) and the remark after
`(e311)` (`F̃_ψ(ω) = W(-iω/c_s)`), inverted by `gt:3.1`; it is the exact reference value of the
main-edge integral in `O.5`, `O.6`.

* `movAvg s Y (u) = ∫₀¹ Y(u + s r) dr = s⁻¹ ∫₀^s Y(u + t) dt`, and the `m`-fold B-spline window
  `windowSmooth δ₀ m X = (movAvg (δ₀/m))^[m] X`. (The `m`-fold iterate is the convolution of `X`
  with the `m`-fold B-spline density `ψ_m` of `(e28)` read as a composition of `m` uniform
  averages over `[0, δ₀/m]`; this is the definition used here.)
* `airyTwistedLaplaceC_movAvg`: `(M_s Y)~(i y) = E₁(y s) Y~(i y)` for `Re y ≥ 0`.
* `HasU2.movAvg`, `HasU2.windowSmooth`: `U.2` and continuity pass to the smoothed seed.
* `liftSymbol_eq_airyTwisted_windowSmooth`: `W_X(w) = F̃_ψ(i c_s w)` for `Re w ≥ 0`, with `F_ψ` the
  window smoothing of `X`.
* `HasU2.airy_inversion`: for a continuous `G` with `HasU2 G`,
  `G(-x) = c_s/(2π k) ∫_ℝ G̃(i c_s v) e^{i(c_s x v - π² v³/36)} dv` (Fourier inversion for the
  twisted transform), hence `airy_window_inversion` for `G = F_ψ` and the lift symbol `W_X`.

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real FourierTransform

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-! ### Moving averages and the twisted Laplace transform -/

/-- `(M_s Y)(u) = ∫₀¹ Y(u + s r) dr`. -/
noncomputable def movAvg (s : ℝ) (Y : ℝ → ℝ) (u : ℝ) : ℝ := ∫ r in (0 : ℝ)..1, Y (u + s * r)

theorem continuous_movAvg {Y : ℝ → ℝ} (hY : Continuous Y) (s : ℝ) : Continuous (movAvg s Y) := by
  unfold movAvg
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun u r => Y (u + s * r))
    (by fun_prop) 0 1

/-- Translation identity for the Fubini kernel: `Y(u + s r) e^{y u} = e^{-y s r} · g(u + s r)`, `g(v) = Y(v) e^{y v}`. -/
lemma movAvg_slice (Y : ℝ → ℝ) (s : ℝ) (y : ℂ) (r : ℝ) :
    (fun u : ℝ => (Y (u + s * r) : ℂ) * Complex.exp (y * (u : ℂ))) =
      fun u => Complex.exp (-(y * ((s * r : ℝ) : ℂ))) * ((Y (u + s * r) : ℂ) * Complex.exp (y * ((u + s * r : ℝ) : ℂ))) := by
  funext u
  rw [mul_left_comm, ← Complex.exp_add]
  push_cast
  congr 2; ring

/-- The Fubini kernel `(r, u) ↦ Y(u + s r) e^{y u}` is integrable on `(0,1] × ℝ`. -/
lemma integrable_movAvg_kernel {Y : ℝ → ℝ} (hYc : Continuous Y) (s : ℝ) {y : ℂ}
    (hint : Integrable (fun u : ℝ => (Y u : ℂ) * Complex.exp (y * (u : ℂ)))) :
    Integrable (fun p : ℝ × ℝ => (Y (p.2 + s * p.1) : ℂ) * Complex.exp (y * (p.2 : ℂ)))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => (Y (p.2 + s * p.1) : ℂ) * Complex.exp (y * (p.2 : ℂ)))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) :=
    (Continuous.mul (Complex.continuous_ofReal.comp (hYc.comp (by fun_prop))) (by fun_prop)).aestronglyMeasurable
  refine (integrable_prod_iff hmeas).mpr ⟨ae_of_all _ fun r => ?_, ?_⟩
  · dsimp only
    rw [movAvg_slice Y s y r]
    exact ((hint.comp_add_right (s * r)).const_mul _)
  · have hnorm : ∀ r : ℝ, ∫ u : ℝ, ‖(Y (u + s * r) : ℂ) * Complex.exp (y * (u : ℂ))‖ =
        Real.exp (-(y.re * (s * r))) * ∫ u : ℝ, ‖(Y u : ℂ) * Complex.exp (y * (u : ℂ))‖ := fun r => by
      rw [show (fun u : ℝ => ‖(Y (u + s * r) : ℂ) * Complex.exp (y * (u : ℂ))‖) =
          fun u => Real.exp (-(y.re * (s * r))) * ‖(Y (u + s * r) : ℂ) * Complex.exp (y * ((u + s * r : ℝ) : ℂ))‖ from by
        funext u
        rw [show ((Y (u + s * r) : ℂ) * Complex.exp (y * (u : ℂ))) = Complex.exp (-(y * ((s * r : ℝ) : ℂ))) *
          ((Y (u + s * r) : ℂ) * Complex.exp (y * ((u + s * r : ℝ) : ℂ))) from congrFun (movAvg_slice Y s y r) u]
        rw [norm_mul, norm_mul, Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; simp]
      rw [integral_const_mul]
      congr 1
      exact integral_add_right_eq_self (fun u : ℝ => ‖(Y u : ℂ) * Complex.exp (y * (u : ℂ))‖) (s * r)
    simp only [hnorm]
    exact (Continuous.integrableOn_Ioc (by fun_prop))

/-- Twisted Laplace transform of a moving average: `(M_s Y)~(i y) = E₁(y s) Y~(i y)` for `Re y ≥ 0`
(with the integrability of `(M_s Y) e^{y ·}`). -/
theorem airyTwistedLaplaceC_movAvg {Y : ℝ → ℝ} (hYc : Continuous Y) (s : ℝ) {y : ℂ}
    (hint : Integrable (fun u : ℝ => (Y u : ℂ) * Complex.exp (y * (u : ℂ)))) :
    Integrable (fun u : ℝ => ((movAvg s Y u : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) ∧
      airyTwistedLaplaceC (movAvg s Y) y = bsplineE1 (y * (s : ℂ)) * airyTwistedLaplaceC Y y := by
  have hK := integrable_movAvg_kernel hYc s hint
  have hrow : ∀ u : ℝ, ((movAvg s Y u : ℝ) : ℂ) * Complex.exp (y * (u : ℂ)) =
      ∫ r in Ioc (0 : ℝ) 1, (Y (u + s * r) : ℂ) * Complex.exp (y * (u : ℂ)) := fun u => by
    rw [integral_mul_const, movAvg, intervalIntegral.integral_of_le zero_le_one, ← integral_complex_ofReal]
  have hcol : ∀ r : ℝ, ∫ u : ℝ, (Y (u + s * r) : ℂ) * Complex.exp (y * (u : ℂ)) =
      Complex.exp (-(y * ((s * r : ℝ) : ℂ))) * ∫ u : ℝ, (Y u : ℂ) * Complex.exp (y * (u : ℂ)) := fun r => by
    calc ∫ u : ℝ, (Y (u + s * r) : ℂ) * Complex.exp (y * (u : ℂ)) =
          ∫ u : ℝ, Complex.exp (-(y * ((s * r : ℝ) : ℂ))) * ((Y (u + s * r) : ℂ) * Complex.exp (y * ((u + s * r : ℝ) : ℂ))) := by
          rw [movAvg_slice Y s y r]
      _ = Complex.exp (-(y * ((s * r : ℝ) : ℂ))) * ∫ u : ℝ, (Y (u + s * r) : ℂ) * Complex.exp (y * ((u + s * r : ℝ) : ℂ)) :=
          integral_const_mul _ _
      _ = _ := by rw [integral_add_right_eq_self (fun u : ℝ => (Y u : ℂ) * Complex.exp (y * (u : ℂ))) (s * r)]
  refine ⟨?_, ?_⟩
  · exact (hK.integral_prod_right).congr (ae_of_all _ fun u => by dsimp only; exact (hrow u).symm)
  · unfold airyTwistedLaplaceC
    simp_rw [hrow]
    rw [← integral_integral_swap (f := fun r u : ℝ => (Y (u + s * r) : ℂ) * Complex.exp (y * (u : ℂ))) hK]
    simp_rw [hcol]
    rw [integral_mul_const, bsplineE1_eq_integral, bsplineKernel, intervalIntegral.integral_of_le zero_le_one]
    have : ∀ r : ℝ, Complex.exp (-(y * ((s * r : ℝ) : ℂ))) = (r : ℂ) ^ 0 * Complex.exp (-(y * (s : ℂ)) * (r : ℂ)) := fun r => by
      push_cast; rw [pow_zero, one_mul]; congr 1; ring
    simp_rw [this]
    ring

/-! ### `U.2` and continuity for the smoothed seed -/

theorem HasU2.movAvg {X : ℝ → ℝ} (h : HasU2 X) (hc : Continuous X) {s : ℝ} (hs : 0 ≤ s) : HasU2 (movAvg s X) where
  integrable y hy := (airyTwistedLaplaceC_movAvg hc s (h.integrable y hy)).1
  differentiable := by
    have hE : DifferentiableOn ℂ (fun y : ℂ => bsplineE1 (y * (s : ℂ)) * airyTwistedLaplaceC X y) {y : ℂ | 0 < y.re} :=
      ((differentiable_bsplineE1.comp (differentiable_id.mul_const (s : ℂ))).differentiableOn).mul h.differentiable
    exact hE.congr fun y hy => (airyTwistedLaplaceC_movAvg hc s (h.integrable y (le_of_lt hy))).2
  rhp := by
    obtain ⟨C, hC, hb⟩ := h.rhp
    refine ⟨C, hC, fun w hw => ?_⟩
    have hy : 0 ≤ ((ceCs : ℂ) * w).re := by simp [Complex.mul_re, mul_nonneg ceCs_pos.le hw]
    rw [(airyTwistedLaplaceC_movAvg hc s (h.integrable _ hy)).2, norm_mul]
    have hre : 0 ≤ (((ceCs : ℂ) * w) * (s : ℂ)).re := by
      simp [Complex.mul_re, mul_nonneg (mul_nonneg ceCs_pos.le hw) hs]
    have h1 : ‖bsplineE1 (((ceCs : ℂ) * w) * (s : ℂ))‖ ≤ 1 := by
      have := (norm_iteratedDeriv_bsplineE1_le 0 hre).1
      rwa [iteratedDeriv_zero] at this
    calc ‖bsplineE1 (((ceCs : ℂ) * w) * (s : ℂ))‖ * ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖
        ≤ 1 * (C * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := mul_le_mul h1 (hb w hw) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

/-- The `m`-fold window smoothing `F_ψ` of a seed `X` (`m` averages over `[0, δ₀/m]`). -/
noncomputable def windowSmooth (δ₀ : ℝ) (m : ℕ) (X : ℝ → ℝ) : ℝ → ℝ := (movAvg (δ₀ / m))^[m] X

lemma iterate_movAvg_aux {X : ℝ → ℝ} (h : HasU2 X) (hc : Continuous X) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    Continuous ((movAvg s)^[n] X) ∧ HasU2 ((movAvg s)^[n] X) ∧
      ∀ y : ℂ, 0 ≤ y.re → airyTwistedLaplaceC ((movAvg s)^[n] X) y = bsplineE1 (y * (s : ℂ)) ^ n * airyTwistedLaplaceC X y := by
  induction n with
  | zero => exact ⟨hc, h, fun y _ => by simp⟩
  | succ n ih =>
    obtain ⟨hcn, hhn, hid⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨continuous_movAvg hcn s, hhn.movAvg hcn hs, fun y hy => ?_⟩
    rw [(airyTwistedLaplaceC_movAvg hcn s (hhn.integrable y hy)).2, hid y hy, pow_succ]; ring

theorem HasU2.windowSmooth {X : ℝ → ℝ} (h : HasU2 X) (hc : Continuous X) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) :
    HasU2 (windowSmooth δ₀ m X) :=
  (iterate_movAvg_aux h hc (div_nonneg hδ m.cast_nonneg) m).2.1

theorem continuous_windowSmooth {X : ℝ → ℝ} (h : HasU2 X) (hc : Continuous X) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) :
    Continuous (windowSmooth δ₀ m X) :=
  (iterate_movAvg_aux h hc (div_nonneg hδ m.cast_nonneg) m).1

/-- `W_X(w) = F̃_ψ(i c_s w)` for `Re w ≥ 0`, where `F_ψ = windowSmooth δ₀ m X`. -/
theorem liftSymbol_eq_airyTwisted_windowSmooth {X : ℝ → ℝ} (h : HasU2 X) (hc : Continuous X) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ)
    {w : ℂ} (hw : 0 ≤ w.re) :
    liftSymbol X δ₀ m w = airyTwistedLaplaceC (windowSmooth δ₀ m X) ((ceCs : ℂ) * w) := by
  have hy : 0 ≤ ((ceCs : ℂ) * w).re := by simp [Complex.mul_re, mul_nonneg ceCs_pos.le hw]
  rw [windowSmooth, (iterate_movAvg_aux h hc (div_nonneg hδ m.cast_nonneg) m).2.2 _ hy]
  unfold liftSymbol liftMultiplier
  congr 3
  push_cast; ring

/-! ### Airy inversion -/

lemma ceCs_cube' : ceCs ^ 3 = Real.pi ^ 2 / 3 := by
  unfold ceCs
  rw [← Real.rpow_natCast ((Real.pi ^ 2 / 3) ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul (by positivity)]; norm_num

/-- The twisted transform on the imaginary axis `G̃(i c_s v)` is continuous and integrable in `v`. -/
lemma HasU2.integrable_airyTwisted_imag {G : ℝ → ℝ} (h : HasU2 G) :
    Integrable fun v : ℝ => airyTwistedLaplaceC G ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) := by
  simpa [liftSymbol, liftMultiplier] using h.integrable_liftSymbol_imag (δ₀ := 0) le_rfl 0

lemma HasU2.continuous_airyTwisted_imag {G : ℝ → ℝ} (h : HasU2 G) :
    Continuous fun v : ℝ => airyTwistedLaplaceC G ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) :=
  h.continuousOn.comp_continuous (by fun_prop) fun v => by simp

/-- The Fourier transform of `G` at `-c_s v / (2π)` in terms of the twisted transform on the imaginary axis. -/
lemma fourier_eq_airyTwisted {G : ℝ → ℝ} (v : ℝ) :
    (𝓕 (fun u : ℝ => (G u : ℂ))) (-(ceCs * v) / (2 * Real.pi)) =
      (ceK : ℂ)⁻¹ * airyTwistedLaplaceC G ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) *
        Complex.exp (-(Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ))) := by
  have hk : (ceK : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ceK_pos.ne'
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hJ : ∫ u : ℝ, Complex.exp (((-2 * Real.pi * u * (-(ceCs * v) / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) • (G u : ℂ) =
      ∫ u : ℝ, (G u : ℂ) * Complex.exp (((ceCs : ℂ) * ((v : ℂ) * Complex.I)) * (u : ℂ)) := by
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    dsimp only
    rw [smul_eq_mul, mul_comm]
    congr 2
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
  have hcube : (((ceCs : ℂ) * ((v : ℂ) * Complex.I)) ^ 3) = -(Complex.I * ((ceCs ^ 3 * v ^ 3 : ℝ) : ℂ)) := by
    push_cast
    have : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
    calc ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) ^ 3 = (ceCs : ℂ) ^ 3 * (v : ℂ) ^ 3 * Complex.I ^ 3 := by ring
      _ = _ := by rw [this]; ring
  have hexp : Complex.exp (-(((ceCs : ℂ) * ((v : ℂ) * Complex.I)) ^ 3) / 12) =
      Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) := by
    rw [hcube, ceCs_cube']; congr 1; push_cast; ring
  have hT : airyTwistedLaplaceC G ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) =
      (ceK : ℂ) * Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) *
        ∫ u : ℝ, (G u : ℂ) * Complex.exp (((ceCs : ℂ) * ((v : ℂ) * Complex.I)) * (u : ℂ)) := by
    unfold airyTwistedLaplaceC; rw [hexp]
  have h1 : Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) *
      Complex.exp (-(Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ))) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [hJ, hT]
  calc _ = (ceK : ℂ)⁻¹ * (ceK : ℂ) * (Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) *
      Complex.exp (-(Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)))) * ∫ u : ℝ, (G u : ℂ) * Complex.exp (((ceCs : ℂ) * ((v : ℂ) * Complex.I)) * (u : ℂ)) := by
        rw [h1, inv_mul_cancel₀ hk]; ring
    _ = _ := by ring

/-- **Airy inversion** (`gt:3.1` inverted): for a continuous `G` with `HasU2 G`,
`G(-x) = c_s / (2π k) ∫_ℝ G̃(i c_s v) exp(i (c_s x v - π² v³ / 36)) dv`. -/
theorem HasU2.airy_inversion {G : ℝ → ℝ} (h : HasU2 G) (hc : Continuous G) (x : ℝ) :
    (G (-x) : ℂ) = ((ceCs : ℂ) / (2 * (Real.pi : ℂ) * (ceK : ℂ))) *
      ∫ v : ℝ, airyTwistedLaplaceC G ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) *
        Complex.exp (Complex.I * ((ceCs * x * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) := by
  have hk : (ceK : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ceK_pos.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcs : (ceCs : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ceCs_pos.ne'
  set f : ℝ → ℂ := fun u => (G u : ℂ) with hf
  have hf_int : Integrable f := by simpa [hf] using h.integrable 0 (by simp)
  have hf_cont : Continuous f := Complex.continuous_ofReal.comp hc
  set Φ : ℝ → ℂ := fun v => (ceK : ℂ)⁻¹ * airyTwistedLaplaceC G ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) *
    Complex.exp (-(Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ))) with hΦ
  have hΦ_int : Integrable Φ := by
    refine ((h.integrable_airyTwisted_imag.norm.const_mul ceK⁻¹)).mono' ?_ (ae_of_all _ fun v => ?_)
    · exact ((continuous_const.mul h.continuous_airyTwisted_imag).mul (by fun_prop)).aestronglyMeasurable
    · have h1 : ‖Complex.exp (-(Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)))‖ = 1 := by
        rw [show -(Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) = (((-(Real.pi ^ 2 / 36 * v ^ 3) : ℝ) : ℂ)) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      simp only [hΦ, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ceK_pos, h1, mul_one]
      exact le_of_eq rfl
  have hF : ∀ w : ℝ, 𝓕 f w = Φ (-(2 * Real.pi / ceCs) * w) := fun w => by
    have := fourier_eq_airyTwisted (G := G) (-(2 * Real.pi / ceCs) * w)
    rw [show -(ceCs * (-(2 * Real.pi / ceCs) * w)) / (2 * Real.pi) = w by
      field_simp [ceCs_pos.ne', Real.pi_ne_zero]] at this
    exact this
  have hR : (-(2 * Real.pi / ceCs) : ℝ) ≠ 0 := by
    exact neg_ne_zero.mpr (div_pos (by positivity) ceCs_pos).ne'
  have hF_int : Integrable (𝓕 f) := by
    rw [show 𝓕 f = fun w => Φ (-(2 * Real.pi / ceCs) * w) from funext hF]
    exact hΦ_int.comp_mul_left' hR
  have hinv := hf_int.fourierInv_fourier_eq hF_int hf_cont.continuousAt (v := -x)
  rw [Real.fourierInv_eq'] at hinv
  set R : ℝ := -(2 * Real.pi / ceCs) with hRdef
  set g : ℝ → ℂ := fun v => Complex.exp (((ceCs * x * v : ℝ) : ℂ) * Complex.I) * Φ v with hg
  have hgw : ∀ w : ℝ, Complex.exp (((2 * Real.pi * inner ℝ w (-x) : ℝ) : ℂ) * Complex.I) • 𝓕 f w = g (R * w) := fun w => by
    rw [hF w, smul_eq_mul, hg]
    dsimp only
    congr 3
    rw [real_inner_eq_re_inner] 
    simp [hRdef]; field_simp
  rw [integral_congr_ae (ae_of_all _ hgw), Measure.integral_comp_mul_left] at hinv
  have habs : |R⁻¹| = ceCs / (2 * Real.pi) := by
    rw [hRdef, abs_inv, abs_neg, abs_of_pos (div_pos (by positivity) ceCs_pos), inv_div]
  have hgi : ∫ y : ℝ, g y = (ceK : ℂ)⁻¹ * ∫ v : ℝ, airyTwistedLaplaceC G ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) *
      Complex.exp (Complex.I * ((ceCs * x * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    have hE : Complex.exp (Complex.I * ((ceCs * x * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) =
        Complex.exp (((ceCs * x * v : ℝ) : ℂ) * Complex.I) * Complex.exp (-(Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    simp only [hg, hΦ]
    rw [hE]; ring
  rw [habs, hgi, Complex.real_smul] at hinv
  rw [show (G (-x) : ℂ) = f (-x) from rfl, ← hinv]
  generalize (∫ v : ℝ, airyTwistedLaplaceC G ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) *
    Complex.exp (Complex.I * ((ceCs * x * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ))) = J
  push_cast
  field_simp

/-- **Exact reference identity** (`gt:3.1` inverted for the lift symbol): for a continuous seed with `HasU2`,
the window `F_ψ = windowSmooth δ₀ m X` satisfies
`F_ψ(-x) = c_s / (2π k) ∫_ℝ W_X(i v) exp(i (c_s x v - π² v³ / 36)) dv`. -/
theorem airy_window_inversion {X : ℝ → ℝ} (h : HasU2 X) (hc : Continuous X) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) (x : ℝ) :
    ((windowSmooth δ₀ m X (-x) : ℝ) : ℂ) = ((ceCs : ℂ) / (2 * (Real.pi : ℂ) * (ceK : ℂ))) *
      ∫ v : ℝ, liftSymbol X δ₀ m ((v : ℂ) * Complex.I) *
        Complex.exp (Complex.I * ((ceCs * x * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) := by
  rw [(h.windowSmooth hc hδ m).airy_inversion (continuous_windowSmooth h hc hδ m) x]
  congr 2
  funext v
  rw [liftSymbol_eq_airyTwisted_windowSmooth h hc hδ m (by simp)]

/-- The reference value of the main-edge integral in `O.5`, `O.6`: replacing `K₀(i ε v, ξ)` by the
pure Airy phase `exp(i (a v - π² v³/36))` gives exactly `(k / (c_s ξ)) F_ψ(-a / c_s)`; here
`k β₁ / (π² ξ) = k / (c_s ξ)` since `β₁ = π² / c_s`. -/
theorem airy_reference_identity {X : ℝ → ℝ} (h : HasU2 X) (hc : Continuous X) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) {ξ : ℝ} (hξ : 0 < ξ) (a : ℝ) :
    ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, liftSymbol X δ₀ m ((v : ℂ) * Complex.I) *
        Complex.exp (Complex.I * ((a * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) =
      ((ceK : ℂ) / ((ceCs : ℂ) * (ξ : ℂ))) * ((windowSmooth δ₀ m X (-(a / ceCs)) : ℝ) : ℂ) := by
  have hI := airy_window_inversion h hc hδ m (a / ceCs)
  have hcs : (ceCs : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ceCs_pos.ne'
  have hk : (ceK : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ceK_pos.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hξ' : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ.ne'
  have hax : ∀ v : ℝ, ceCs * (a / ceCs) * v = a * v := fun v => by field_simp [ceCs_pos.ne']
  simp_rw [hax] at hI
  rw [hI]
  generalize (∫ v : ℝ, liftSymbol X δ₀ m ((v : ℂ) * Complex.I) *
    Complex.exp (Complex.I * ((a * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ))) = J
  push_cast
  field_simp

/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplaceC_movAvg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.airyTwistedLaplaceC_movAvg
/-- info: 'FormalResearch.CohnElkies.HasU2.windowSmooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.HasU2.windowSmooth
/-- info: 'FormalResearch.CohnElkies.liftSymbol_eq_airyTwisted_windowSmooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.liftSymbol_eq_airyTwisted_windowSmooth
/-- info: 'FormalResearch.CohnElkies.HasU2.airy_inversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.HasU2.airy_inversion
/-- info: 'FormalResearch.CohnElkies.airy_window_inversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.airy_window_inversion
/-- info: 'FormalResearch.CohnElkies.airy_reference_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.airy_reference_identity

end FormalResearch.CohnElkies
