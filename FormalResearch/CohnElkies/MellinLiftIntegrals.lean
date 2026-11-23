module

public import FormalResearch.CohnElkies.AirySeedSymbols
public import FormalResearch.CohnElkies.MellinMainKernel

/-!
# The two-edge integrals `I_main[F]`, `I_dual[D]` of a Mellin lift of Airy seeds

Source: `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, `(e1)` (pairs `f[F,D]`), `(e28)`
(`M_ψ`, `W`) and Lemma `U.2` (`u1c:U2`), the inputs of `O.3(2)`, `O.5`, `O.6` and `O.11ak`.

For a seed `X : ℝ → ℝ`, a window width `δ₀` and a B-spline order `m`, the lift symbol is
`W_X(w) = M_ψ(w) · X̃(i c_s w)` with `M_ψ(w) = ((1 - e^{-c_s δ₀ w / m}) / (c_s δ₀ w / m))^m`
(`liftMultiplier`, `liftSymbol`; `X̃(i y)` is `airyTwistedLaplaceC X y`), and for `ε = c^{-1/3}`

* `I_main[F](ξ) = (2π ξ)⁻¹ ∫_ℝ K₀(i ε v, ξ) W_F(i v) dv`            (`iMain`),
* `I_dual[D](ξ) = (2π ξ)⁻¹ ∫_ℝ K₀(i ε v, ξ) W_D(c^{1/3} - i v) dv`   (`iDual`),

with `K₀ = mellinK0`. The definitions are total; for a seed with `HasU2` the two integrands are
continuous and integrable (`integrable_iMainIntegrand`, `integrable_iDualIntegrand`), so the
integrals are the genuine Lebesgue integrals. Also proved here: the exact imaginary-axis form of
`K₀` (`mellinK0_imag_eq`, `K₀(iτ, ξ) = (1 - iτ)^{-1/2} e^{B_c(iτ)} e^{i c Φ_Ph(τ; L)}` with
`Φ_Ph(τ; L) = L τ - π² τ³/36 + R(τ)`), and `HasU2.continuousOn` (continuity of the twisted Laplace
transform on the closed right half-plane).

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-! ### Continuity of the twisted Laplace transform on the closed right half-plane -/

/-- `U.2` gives continuity of `X̃(i ·)` on the closed right half-plane. -/
theorem HasU2.continuousOn {X : ℝ → ℝ} (h : HasU2 X) :
    ContinuousOn (airyTwistedLaplaceC X) {y : ℂ | 0 ≤ y.re} := by
  intro y₀ hy₀
  let R : ℝ := ‖y₀‖ + 1
  have hR0 : (0 : ℝ) ≤ R := by positivity
  have hint0 := h.integrable 0 (by simp)
  have hintR := h.integrable (R : ℂ) (by simpa using hR0)
  let bound : ℝ → ℝ := fun u => ‖(X u : ℂ) * Complex.exp ((0 : ℂ) * (u : ℂ))‖ + ‖(X u : ℂ) * Complex.exp ((R : ℂ) * (u : ℂ))‖
  have hbound_int : Integrable bound := hint0.norm.add hintR.norm
  have hint_c : ContinuousWithinAt (fun y : ℂ => ∫ u : ℝ, (X u : ℂ) * Complex.exp (y * (u : ℂ))) {y : ℂ | 0 ≤ y.re} y₀ := by
    refine continuousWithinAt_of_dominated (bound := bound) ?_ ?_ hbound_int (ae_of_all _ fun u => by fun_prop)
    · filter_upwards [self_mem_nhdsWithin] with y hy using (h.integrable y hy).aestronglyMeasurable
    · filter_upwards [inter_mem_nhdsWithin _ (Metric.ball_mem_nhds y₀ one_pos)] with y hy
      have hdist : ‖y - y₀‖ < 1 := by simpa [Complex.dist_eq] using Metric.mem_ball.mp hy.2
      have hyR : y.re ≤ R := (Complex.re_le_norm y).trans (by
        rw [show y = (y - y₀) + y₀ by ring]; exact (norm_add_le _ _).trans (by dsimp [R]; linarith))
      refine ae_of_all _ fun u => ?_
      have hy0 : 0 ≤ y.re := hy.1
      simp only [bound, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.zero_re, zero_mul, Real.exp_zero, mul_one]
      rcases lt_or_ge u 0 with hu | hu
      · have : Real.exp (y.re * u) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hy0 hu.le)
        have h2 : 0 ≤ ‖(X u : ℂ)‖ * Real.exp (R * u) := by positivity
        calc ‖(X u : ℂ)‖ * Real.exp (y.re * u) ≤ ‖(X u : ℂ)‖ * 1 := by gcongr
          _ ≤ _ := by linarith
      · have : Real.exp (y.re * u) ≤ Real.exp (R * u) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hyR hu)
        have h2 : 0 ≤ ‖(X u : ℂ)‖ := norm_nonneg _
        calc ‖(X u : ℂ)‖ * Real.exp (y.re * u) ≤ ‖(X u : ℂ)‖ * Real.exp (R * u) := by gcongr
          _ ≤ _ := by linarith
  exact (by fun_prop : ContinuousWithinAt (fun y : ℂ => (ceK : ℂ) * Complex.exp (-(y ^ 3) / 12)) {y : ℂ | 0 ≤ y.re} y₀).mul hint_c

/-! ### Definitions -/

/-- The scale `ε = c^{-1/3}`. -/
noncomputable def liftEps (c : ℝ) : ℝ := c ^ (-(1 / 3 : ℝ))

/-- The B-spline multiplier `M_ψ(w) = ((1 - e^{-c_s δ₀ w / m}) / (c_s δ₀ w / m))^m` of `(e28)`. -/
noncomputable def liftMultiplier (δ₀ : ℝ) (m : ℕ) (w : ℂ) : ℂ :=
  bsplineE1 (((ceCs * δ₀ / m : ℝ) : ℂ) * w) ^ m

/-- The lift symbol `W_X(w) = M_ψ(w) · X̃(i c_s w)` of `(e28)`. -/
noncomputable def liftSymbol (X : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) (w : ℂ) : ℂ :=
  liftMultiplier δ₀ m w * airyTwistedLaplaceC X ((ceCs : ℂ) * w)

/-- Integrand of `I_main` at `v`: `K₀(i ε v, ξ) W_F(i v)`. -/
noncomputable def iMainIntegrand (X : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) (c ξ : ℝ) (v : ℝ) : ℂ :=
  mellinK0 c (((liftEps c * v : ℝ) : ℂ) * Complex.I) ξ * liftSymbol X δ₀ m ((v : ℂ) * Complex.I)

/-- Integrand of `I_dual` at `v`: `K₀(i ε v, ξ) W_D(c^{1/3} - i v)`. -/
noncomputable def iDualIntegrand (D : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) (c ξ : ℝ) (v : ℝ) : ℂ :=
  mellinK0 c (((liftEps c * v : ℝ) : ℂ) * Complex.I) ξ *
    liftSymbol D δ₀ m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) - (v : ℂ) * Complex.I)

/-- `I_main[F](ξ) = (2π ξ)⁻¹ ∫_ℝ K₀(i ε v, ξ) W_F(i v) dv` (`(e1)`). -/
noncomputable def iMain (X : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) (c ξ : ℝ) : ℂ :=
  ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, iMainIntegrand X δ₀ m c ξ v

/-- `I_dual[D](ξ) = (2π ξ)⁻¹ ∫_ℝ K₀(i ε v, ξ) W_D(c^{1/3} - i v) dv` (`(e1)`). -/
noncomputable def iDual (D : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) (c ξ : ℝ) : ℂ :=
  ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, iDualIntegrand D δ₀ m c ξ v

lemma liftEps_pos {c : ℝ} (hc : 0 < c) : 0 < liftEps c := Real.rpow_pos_of_pos hc _

/-! ### The kernel `K₀` on the imaginary axis -/

/-- Exact imaginary-axis form of the Mellin-strip kernel:
`K₀(iτ, ξ) = (1 - iτ)^{-1/2} e^{B_c(iτ)} exp(i c (L τ - π² τ³/36 + R(τ)))`, `L = log(π² ξ)`. -/
theorem mellinK0_imag_eq (c ξ τ : ℝ) (hξ : 0 < ξ) :
    mellinK0 c ((τ : ℂ) * Complex.I) ξ =
      (1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) * Complex.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)) *
        Complex.exp (Complex.I * (c : ℂ) * ((Real.log (Real.pi ^ 2 * ξ) * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ : ℝ) : ℂ)) := by
  unfold mellinK0 mellinPhi
  have hlog : Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)) = (Real.log (Real.pi ^ 2 * ξ) : ℂ) := by
    rw [show (Real.pi : ℂ) ^ 2 * (ξ : ℂ) = ((Real.pi ^ 2 * ξ : ℝ) : ℂ) by push_cast; ring]; exact (Complex.ofReal_log (by positivity)).symm
  have hs : stripS0Tilde ((τ : ℂ) * Complex.I) = Complex.I * ((edgeR τ - Real.pi ^ 2 / 36 * τ ^ 3 : ℝ) : ℂ) := by
    have hed : edgeR5 τ = stripS0Tilde ((τ : ℂ) * Complex.I) - (Real.pi ^ 2 / 36 : ℂ) * ((τ : ℂ) * Complex.I) ^ 3 := rfl
    have hi3 : ((τ : ℂ) * Complex.I) ^ 3 = -(((τ ^ 3 : ℝ) : ℂ) * Complex.I) := by
      calc ((τ : ℂ) * Complex.I) ^ 3 = (τ : ℂ) ^ 3 * (Complex.I ^ 2 * Complex.I) := by ring
        _ = -(((τ ^ 3 : ℝ) : ℂ) * Complex.I) := by rw [Complex.I_sq]; push_cast; ring
    rw [hi3] at hed
    have hsub : stripS0Tilde ((τ : ℂ) * Complex.I) = Complex.I * (edgeR τ : ℂ) - Complex.I * ((Real.pi ^ 2 / 36 * τ ^ 3 : ℝ) : ℂ) := by
      have h' : Complex.I * (edgeR τ : ℂ) = stripS0Tilde ((τ : ℂ) * Complex.I) + Complex.I * ((Real.pi ^ 2 / 36 * τ ^ 3 : ℝ) : ℂ) := by
        rw [← edgeR5_eq_I_mul_edgeR, hed]; push_cast; ring
      linear_combination -h'
    rw [hsub]; push_cast; ring
  rw [hlog, hs]
  have hexp : (c : ℂ) * (Complex.I * ((edgeR τ - Real.pi ^ 2 / 36 * τ ^ 3 : ℝ) : ℂ) + (τ : ℂ) * Complex.I * (Real.log (Real.pi ^ 2 * ξ) : ℂ)) =
      Complex.I * (c : ℂ) * ((Real.log (Real.pi ^ 2 * ξ) * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ : ℝ) : ℂ) := by push_cast; ring
  rw [hexp]

/-- `K₀(i τ, ξ)` is continuous in `τ ∈ ℝ`. -/
theorem continuous_mellinK0_imag {c : ℝ} (hc : 0 < c) {ξ : ℝ} (hξ : 0 < ξ) :
    Continuous fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ := by
  have h : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ) = fun τ : ℝ =>
      (1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) * Complex.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)) *
        Complex.exp (Complex.I * (c : ℂ) * ((Real.log (Real.pi ^ 2 * ξ) * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ : ℝ) : ℂ)) :=
    funext fun τ => mellinK0_imag_eq c ξ τ hξ
  rw [h]
  have hB : Continuous fun τ : ℝ => FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I) := by
    unfold FormalResearch.Asymptotics.binetDiff
    exact (FormalResearch.Asymptotics.binetRem_differentiableOn.continuousOn.comp_continuous (by fun_prop)
      fun τ => by simp [hc]).sub continuous_const
  refine (Continuous.mul (Continuous.cpow (by fun_prop) continuous_const fun τ =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))) (Complex.continuous_exp.comp hB)).mul
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_)))
  exact ((continuous_const.mul continuous_id).sub (continuous_const.mul (continuous_id.pow 3))).add edgeR_contDiff.continuous

/-! ### Bounds on the lift symbol -/

lemma norm_liftMultiplier_le_one {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) {w : ℂ} (hw : 0 ≤ w.re) : ‖liftMultiplier δ₀ m w‖ ≤ 1 := by
  unfold liftMultiplier
  have hre : 0 ≤ ((((ceCs * δ₀ / m : ℝ) : ℂ)) * w).re := by
    rw [Complex.re_ofReal_mul]; exact mul_nonneg (div_nonneg (mul_nonneg ceCs_pos.le hδ) m.cast_nonneg) hw
  have := (norm_iteratedDeriv_bsplineE1_le 0 hre).1
  rw [iteratedDeriv_zero] at this
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) this

lemma one_add_abs_im_le_two_mul_norm_one_add {w : ℂ} (hw : 0 ≤ w.re) : 1 + |w.im| ≤ 2 * ‖1 + w‖ := by
  have h1 : 1 ≤ ‖1 + w‖ := by
    have : (1 : ℝ) ≤ (1 + w).re := by simpa using hw
    exact this.trans (Complex.re_le_norm _)
  have h2 : |w.im| ≤ ‖1 + w‖ := by
    have : |(1 + w).im| ≤ ‖1 + w‖ := Complex.abs_im_le_norm _
    simpa using this
  linarith

/-- The right-half-plane bound `‖W_X(w)‖ ≤ C ‖1 + w‖^{-5/2}` of `U.2(2)` (`(e28)`). -/
theorem HasU2.norm_liftSymbol_le {X : ℝ → ℝ} (h : HasU2 X) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) :
    ∃ C > 0, ∀ w : ℂ, 0 ≤ w.re → ‖liftSymbol X δ₀ m w‖ ≤ C * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := h.rhp
  refine ⟨C * 2 ^ (5 / 2 : ℝ), by positivity, fun w hw => ?_⟩
  have h1 : 0 < 1 + |w.im| := by positivity
  have hn : 0 < ‖1 + w‖ := by
    have : (1 : ℝ) ≤ (1 + w).re := by simpa using hw
    exact lt_of_lt_of_le one_pos (this.trans (Complex.re_le_norm _))
  have h2 := one_add_abs_im_le_two_mul_norm_one_add hw
  have hpow : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ 2 ^ (5 / 2 : ℝ) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
    have h3 : (1 + |w.im|) / 2 ≤ ‖1 + w‖ := by linarith
    calc ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ ((1 + |w.im|) / 2) ^ (-(5 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h3 (by norm_num)
      _ = 2 ^ (5 / 2 : ℝ) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
          rw [Real.div_rpow h1.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
          ring
  unfold liftSymbol
  rw [norm_mul]
  calc ‖liftMultiplier δ₀ m w‖ * ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ 1 * (C * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul (norm_liftMultiplier_le_one hδ m hw) (hb w hw) (norm_nonneg _) zero_le_one
    _ ≤ C * (2 ^ (5 / 2 : ℝ) * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hpow hC.le
    _ = _ := by ring

lemma integrable_one_add_abs_rpow : Integrable (fun v : ℝ => (1 + |v|) ^ (-(5 / 2 : ℝ))) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 5 / 2) (by simp; norm_num)
  simpa using this

lemma continuous_liftSymbol_of_re {X : ℝ → ℝ} (h : HasU2 X) (δ₀ : ℝ) (m : ℕ) {g : ℝ → ℂ} (hg : Continuous g)
    (hre : ∀ v, 0 ≤ (g v).re) : Continuous fun v : ℝ => liftSymbol X δ₀ m (g v) := by
  unfold liftSymbol liftMultiplier
  refine Continuous.mul ((differentiable_bsplineE1.continuous.comp (continuous_const.mul hg)).pow m) ?_
  exact h.continuousOn.comp_continuous (continuous_const.mul hg) fun v => by
    simp only [Set.mem_ofPred_eq, Complex.re_ofReal_mul]; exact mul_nonneg ceCs_pos.le (hre v)

/-- `W_X(i v)` is continuous and integrable in `v ∈ ℝ`. -/
theorem HasU2.integrable_liftSymbol_imag {X : ℝ → ℝ} (h : HasU2 X) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) :
    Integrable fun v : ℝ => liftSymbol X δ₀ m ((v : ℂ) * Complex.I) := by
  obtain ⟨C, hC, hb⟩ := h.norm_liftSymbol_le hδ m
  refine (integrable_one_add_abs_rpow.const_mul C).mono'
    (continuous_liftSymbol_of_re h δ₀ m (by fun_prop) fun v => by simp).aestronglyMeasurable
    (ae_of_all _ fun v => ?_)
  simpa using hb ((v : ℂ) * Complex.I) (by simp)

/-- `W_D(c^{1/3} - i v)` is continuous and integrable in `v ∈ ℝ`. -/
theorem HasU2.integrable_liftSymbol_dual {D : ℝ → ℝ} (h : HasU2 D) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    Integrable fun v : ℝ => liftSymbol D δ₀ m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) - (v : ℂ) * Complex.I) := by
  obtain ⟨C, hC, hb⟩ := h.norm_liftSymbol_le hδ m
  have hre : ∀ v : ℝ, 0 ≤ ((((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)) - (v : ℂ) * Complex.I).re := fun v => by
    simpa using Real.rpow_nonneg hc _
  refine (integrable_one_add_abs_rpow.const_mul C).mono'
    (continuous_liftSymbol_of_re h δ₀ m (by fun_prop) hre).aestronglyMeasurable (ae_of_all _ fun v => ?_)
  have := hb _ (hre v)
  simpa using this

/-! ### Integrability of the two-edge integrands -/

lemma norm_mellinK0_imag_le_one {c ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) (τ : ℝ) : ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖ ≤ 1 :=
  ((norm_mellinK0_imag_le hc hξ τ).2).trans (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg τ]) (by norm_num))

lemma continuous_mellinK0_scaled {c : ℝ} (hc : 0 < c) {ξ : ℝ} (hξ : 0 < ξ) :
    Continuous fun v : ℝ => mellinK0 c (((liftEps c * v : ℝ) : ℂ) * Complex.I) ξ :=
  (continuous_mellinK0_imag hc hξ).comp (continuous_const.mul continuous_id)

theorem HasU2.integrable_iMainIntegrand {X : ℝ → ℝ} (h : HasU2 X) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) {c : ℝ} (hc : 0 < c)
    {ξ : ℝ} (hξ : 0 < ξ) : Integrable (iMainIntegrand X δ₀ m c ξ) := by
  refine (h.integrable_liftSymbol_imag hδ m).norm.mono' ((continuous_mellinK0_scaled hc hξ).mul
    (continuous_liftSymbol_of_re h δ₀ m (by fun_prop) fun v => by simp)).aestronglyMeasurable (ae_of_all _ fun v => ?_)
  unfold iMainIntegrand
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_mellinK0_imag_le_one hc hξ _)

theorem HasU2.integrable_iDualIntegrand {D : ℝ → ℝ} (h : HasU2 D) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) {c : ℝ} (hc : 0 < c)
    {ξ : ℝ} (hξ : 0 < ξ) : Integrable (iDualIntegrand D δ₀ m c ξ) := by
  have hre : ∀ v : ℝ, 0 ≤ ((((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)) - (v : ℂ) * Complex.I).re := fun v => by
    simpa using Real.rpow_nonneg hc.le _
  refine (h.integrable_liftSymbol_dual hδ m hc.le).norm.mono' ((continuous_mellinK0_scaled hc hξ).mul
    (continuous_liftSymbol_of_re h δ₀ m (by fun_prop) hre)).aestronglyMeasurable (ae_of_all _ fun v => ?_)
  unfold iDualIntegrand
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_mellinK0_imag_le_one hc hξ _)

/-- info: 'FormalResearch.CohnElkies.HasU2.continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.HasU2.continuousOn
/-- info: 'FormalResearch.CohnElkies.mellinK0_imag_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.mellinK0_imag_eq
/-- info: 'FormalResearch.CohnElkies.continuous_mellinK0_imag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.continuous_mellinK0_imag
/-- info: 'FormalResearch.CohnElkies.HasU2.norm_liftSymbol_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.HasU2.norm_liftSymbol_le
/-- info: 'FormalResearch.CohnElkies.HasU2.integrable_liftSymbol_imag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.HasU2.integrable_liftSymbol_imag
/-- info: 'FormalResearch.CohnElkies.HasU2.integrable_liftSymbol_dual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.HasU2.integrable_liftSymbol_dual
/-- info: 'FormalResearch.CohnElkies.HasU2.integrable_iMainIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.HasU2.integrable_iMainIntegrand
/-- info: 'FormalResearch.CohnElkies.HasU2.integrable_iDualIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.HasU2.integrable_iDualIntegrand

end FormalResearch.CohnElkies
