module

public import FormalResearch.ModularBootstrap.Upper.Saddle.SDVprime
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lemma `SD_V`: Order-Zero Two-Saddle Descent

Source: `CFT/modular_bootstrap/paper/edge_transform_sd.tex`, Lemma `esd:lemma` (`SD_V`),
l.379–422 (`(SD.1)`, `(SD.3)–(SD.4)`).

Deduces Lemma `SD_V` directly as the order-zero Hankel specialization of `lemma_SD_V_prime`:
given the edge integral `(SD.1)` with Hankel asymptotic
`H₀^{(1)}(kb) = (2 / (π kb))^{1/2} e^{i(kb - π/4)} (1 + ε_H(kb))`, strip exponential decay of `h`,
log-derivative bounds on `A_x(b) = ℰ(b) e^{Φ₁(b)} b^{1/2} (1 + ε_H(kb))`, and edge reflection
symmetry, `(SD.3)–(SD.4)` holds uniformly for `n m_x³ ≥ N₀`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Saddle

/-! ### 1. Branch-cut `cpow` and strip integrability helpers -/

lemma mem_edgeStrip_im_pos {δ : ℝ} (hδ : δ ≤ 1 / 4) {b : ℂ} (hb : b ∈ edgeStrip δ) :
    0 < b.im := by
  have him : |b.im - 1 / 2| ≤ δ := hb
  linarith [(abs_le.mp him).1]

lemma mem_edgeStrip_norm_ge_quarter {δ : ℝ} (hδ : δ ≤ 1 / 4) {b : ℂ} (hb : b ∈ edgeStrip δ) :
    (1 / 4 : ℝ) ≤ ‖b‖ := by
  have him : |b.im - 1 / 2| ≤ δ := hb
  have h1 : (1 / 4 : ℝ) ≤ b.im := by linarith [(abs_le.mp him).1]
  have h2 : |b.im| ≤ ‖b‖ := Complex.abs_im_le_norm b
  rw [abs_of_pos (by linarith)] at h2
  linarith

lemma cpow_ofReal_pos_mul {k : ℝ} (hk : 0 < k) {b : ℂ} (hb : b ≠ 0) (r : ℂ) :
    ((k : ℂ) * b) ^ r = (k : ℂ) ^ r * b ^ r := by
  have hk_ne : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  have hkb_ne : (k : ℂ) * b ≠ 0 := mul_ne_zero hk_ne hb
  rw [Complex.cpow_def_of_ne_zero hkb_ne, Complex.cpow_def_of_ne_zero hk_ne,
    Complex.cpow_def_of_ne_zero hb, ← Complex.exp_add, ← add_mul]
  congr 1
  have hlog : Complex.log ((k : ℂ) * b) = Complex.log (k : ℂ) + Complex.log b := by
    apply Complex.ext
    · simp only [Complex.log_re, Complex.add_re, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hk]
      rw [Real.log_mul hk.ne' (norm_pos_iff.mpr hb).ne']
    · simp only [Complex.log_im, Complex.add_im, Complex.arg_ofReal_of_nonneg hk.le, zero_add]
      exact Complex.arg_real_mul b hk
  rw [hlog]

lemma inv_cpow_of_im_pos {b : ℂ} (hb : 0 < b.im) (r : ℂ) :
    b⁻¹ ^ r = (b ^ r)⁻¹ := by
  apply Complex.inv_cpow
  intro hpi
  rw [Complex.arg_eq_pi_iff] at hpi
  linarith [hpi.2]

lemma hankelZeroPrefactor_mul (k : ℝ) (hk : 0 < k) {b : ℂ} (hb : 0 < b.im) :
    ((2 : ℂ) / ((Real.pi : ℂ) * ((k : ℂ) * b))) ^ (1 / 2 : ℂ) * b =
      (√(2 / (Real.pi * k)) : ℂ) * b ^ (1 / 2 : ℂ) := by
  have hb_ne : b ≠ 0 := fun h => by simp [h] at hb
  have hc_pos : 0 < 2 / (Real.pi * k) := by positivity [Real.pi_pos]
  have hdiv : (2 : ℂ) / ((Real.pi : ℂ) * ((k : ℂ) * b)) =
      ((2 / (Real.pi * k) : ℝ) : ℂ) * b⁻¹ := by
    push_cast; ring
  have hhalf_c : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hpow_c : ((2 / (Real.pi * k) : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (√(2 / (Real.pi * k)) : ℂ) := by
    rw [hhalf_c, ← Complex.ofReal_cpow hc_pos.le, Real.sqrt_eq_rpow]
  have hcpow_neg : b ^ (-(1 / 2 : ℂ)) * b = b ^ (1 / 2 : ℂ) := by
    conv_lhs => rhs; rw [← Complex.cpow_one b]
    rw [← Complex.cpow_add _ _ hb_ne]
    norm_num
  rw [hdiv, cpow_ofReal_pos_mul hc_pos (inv_ne_zero hb_ne), inv_cpow_of_im_pos hb,
    ← Complex.cpow_neg, hpow_c, mul_assoc, hcpow_neg]

lemma integrable_one_add_abs_mul_exp_neg {a : ℝ} (ha : 0 < a) :
    Integrable (fun v : ℝ => (1 + |v|) * Real.exp (-a * |v|)) volume := by
  have h_half_pos : 0 < a / 2 := half_pos ha
  have h_exp_neg : Integrable (fun v : ℝ => Real.exp (-(a / 2) * |v|)) volume := by
    have h1 : IntegrableOn (fun v : ℝ => Real.exp (-(a / 2) * |v|)) (Iic 0) := by
      refine (integrableOn_exp_mul_Iic h_half_pos 0).congr_fun
        (fun v hv => ?_) measurableSet_Iic
      rw [mem_Iic] at hv
      rw [abs_of_nonpos hv, show -(a / 2) * -v = (a / 2) * v by ring]
    have h2 : IntegrableOn (fun v : ℝ => Real.exp (-(a / 2) * |v|)) (Ioi 0) := by
      refine (integrableOn_exp_mul_Ioi (by linarith : -(a / 2) < 0) 0).congr_fun
        (fun v hv => ?_) measurableSet_Ioi
      rw [mem_Ioi] at hv
      rw [abs_of_pos hv]
    have huniv : (univ : Set ℝ) = Iic 0 ∪ Ioi 0 := by ext v; simp
    rw [← integrableOn_univ, huniv]
    exact h1.union h2
  refine (h_exp_neg.const_mul (1 + 2 / a)).mono'
    ((by fun_prop : Continuous fun v : ℝ => (1 + |v|) * Real.exp (-a * |v|)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun v => ?_)
  have hv0 : 0 ≤ |v| := abs_nonneg v
  have h_lin : |v| ≤ (2 / a) * Real.exp ((a / 2) * |v|) := by
    have h1 : (a / 2) * |v| ≤ Real.exp ((a / 2) * |v|) := by
      linarith [Real.add_one_le_exp ((a / 2) * |v|)]
    calc |v| = (2 / a) * ((a / 2) * |v|) := by field_simp [ha.ne']
      _ ≤ (2 / a) * Real.exp ((a / 2) * |v|) := by gcongr
  have hexp_ge1 : 1 ≤ Real.exp ((a / 2) * |v|) := Real.one_le_exp (by positivity)
  have h_num : 1 + |v| ≤ (1 + 2 / a) * Real.exp ((a / 2) * |v|) := by
    calc 1 + |v| ≤ 1 * Real.exp ((a / 2) * |v|) + (2 / a) * Real.exp ((a / 2) * |v|) := by linarith
      _ = (1 + 2 / a) * Real.exp ((a / 2) * |v|) := by ring
  rw [Real.norm_of_nonneg (by positivity)]
  calc (1 + |v|) * Real.exp (-a * |v|)
      ≤ ((1 + 2 / a) * Real.exp ((a / 2) * |v|)) * Real.exp (-a * |v|) := by gcongr
    _ = (1 + 2 / a) * (Real.exp ((a / 2) * |v|) * Real.exp (-a * |v|)) := by ring
    _ = (1 + 2 / a) * Real.exp (-(a / 2) * |v|) := by
        rw [← Real.exp_add]; congr 2; ring

/-! ### 2. `SD_V` definitions and hypotheses (`esd:lemma`, `(SD.1)–(SD.4)`) -/

/-- Wavenumber `k = 4πnx / 3` appearing in `(SD.1)` and `(SD.4)`. -/
noncomputable def sdvWave (n x : ℝ) : ℝ :=
  4 * Real.pi * n * x / 3

/-- Order-zero amplitude `A_x(b) = ℰ(b) e^{Φ₁(b)} b^{1/2} (1 + ε_H(kb))` (`edge_transform_sd.tex`,
l.390). -/
noncomputable def sdvAmplitude (x n : ℝ) (ℰ Φ₁ εH : ℂ → ℂ) (b : ℂ) : ℂ :=
  ℰ b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ) * (1 + εH ((sdvWave n x : ℂ) * b))

/-- Envelope prefactor `𝒜_x` in `(SD.4)` (`edge_transform_sd.tex`, l.402–406). -/
noncomputable def sdvPrefactor (n x : ℝ) (ℰ Φ₁ εH : ℂ → ℂ) : ℝ :=
  2 * Real.exp (-2 * Real.pi * n * x / 3) * ‖ℰ (bX x)‖ *
    Real.exp (Φ₁ (bX x)).re * ‖1 + εH ((sdvWave n x : ℂ) * bX x)‖ *
    √(‖bX x‖ / (x * edgeF' (edgeV x)))

/-- Oscillatory saddle phase `Θ_x` in `(SD.4)` (`edge_transform_sd.tex`, l.407–408). -/
noncomputable def sdvPhase (Φ₀ : ℂ → ℂ) (n x : ℝ) (ℰ Φ₁ εH : ℂ → ℂ) : ℝ :=
  n * (Φ₀ (bX x)).im + sdvWave n x * edgeV x - Real.pi / 2 +
    Complex.arg (sdvAmplitude x n ℰ Φ₁ εH (bX x))

/-- Edge integral representation `(SD.1)` for `\widehat h(n x^2 / 3)` (`edge_transform_sd.tex`,
l.383–385). -/
noncomputable def sdvIntegral (Φ₀ : ℂ → ℂ) (n x : ℝ) (ℰ Φ₁ H0 : ℂ → ℂ) : ℂ :=
  ((2 * Real.pi * n / 3 : ℝ) : ℂ) *
    ∫ v : ℝ, (ℰ ((v : ℂ) + Complex.I / 2) *
      Complex.exp ((n : ℂ) * Φ₀ ((v : ℂ) + Complex.I / 2) + Φ₁ ((v : ℂ) + Complex.I / 2))) *
      H0 ((sdvWave n x : ℂ) * ((v : ℂ) + Complex.I / 2)) * ((v : ℂ) + Complex.I / 2)

/-- Abstract hypotheses of Lemma `SD_V` (`edge_transform_sd.tex`, `esd:lemma`, l.382–392):
analyticity and nonvanishing of `A_x` on `𝒩_δ`, Hankel asymptotic identity on `𝒩_δ`, uniform
log-derivative bounds `|(log A_x)'| ≤ M` and `|(log A_x)''| ≤ M'`, strip exponential decay of `h`,
boundedness of `1 + ε_H(kb)` on `𝒩_δ`, and edge reflection symmetry `ℐ(-b̄) = conj ℐ(b)`. -/
structure SDVHypotheses (Φ₀ : ℂ → ℂ) (x n δ M M' : ℝ) (ℰ Φ₁ H0 εH : ℂ → ℂ) : Prop where
  analytic : AnalyticOnNhd ℂ (sdvAmplitude x n ℰ Φ₁ εH) (edgeStrip δ)
  nonzero : ∀ b ∈ edgeStrip δ, sdvAmplitude x n ℰ Φ₁ εH b ≠ 0
  hankel : ∀ b ∈ edgeStrip δ,
    H0 ((sdvWave n x : ℂ) * b) =
      ((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * b))) ^ (1 / 2 : ℂ) *
        Complex.exp (Complex.I * ((sdvWave n x : ℂ) * b - Real.pi / 4)) *
        (1 + εH ((sdvWave n x : ℂ) * b))
  logDeriv_bound : ∀ b ∈ edgeStrip δ,
    ‖deriv (sdvAmplitude x n ℰ Φ₁ εH) b / sdvAmplitude x n ℰ Φ₁ εH b‖ ≤ M
  logDeriv2_bound : ∀ b ∈ edgeStrip δ,
    ‖deriv (fun z => deriv (sdvAmplitude x n ℰ Φ₁ εH) z / sdvAmplitude x n ℰ Φ₁ εH z) b‖ ≤ M'
  h_decay : ∃ C_h a_h : ℝ, 0 ≤ C_h ∧ 0 < a_h ∧
    ∀ v t : ℝ, 1 / 2 - δ ≤ t → t ≤ 1 / 2 →
      ‖ℰ ((v : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp ((n : ℂ) * Φ₀ ((v : ℂ) + (t : ℂ) * Complex.I) +
          Φ₁ ((v : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C_h * Real.exp (-a_h * |v|)
  eps_bound : ∃ C_ε : ℝ, ∀ b ∈ edgeStrip δ, ‖1 + εH ((sdvWave n x : ℂ) * b)‖ ≤ C_ε
  edge_symm : ∀ v : ℝ,
    let b : ℂ := (v : ℂ) + Complex.I / 2
    let bm : ℂ := (-v : ℂ) + Complex.I / 2
    let h : ℂ → ℂ := fun z => ℰ z * Complex.exp ((n : ℂ) * Φ₀ z + Φ₁ z)
    h bm * H0 ((sdvWave n x : ℂ) * bm) * bm =
      starRingEnd ℂ (h b * H0 ((sdvWave n x : ℂ) * b) * b)

/-! ### 3. Reduction from `SDVHypotheses` to `TwoSaddleAmplitude` and `SD_V'` -/

lemma sdv_integrand_eq {Φ₀ : ℂ → ℂ} {x n δ M M' : ℝ} {ℰ Φ₁ H0 εH : ℂ → ℂ}
    (hx : xiStar < x) (hn : 0 < n) (hδ : δ ≤ 1 / 4)
    (hH : SDVHypotheses Φ₀ x n δ M M' ℰ Φ₁ H0 εH)
    {b : ℂ} (hb : b ∈ edgeStrip δ) :
    (ℰ b * Complex.exp ((n : ℂ) * Φ₀ b + Φ₁ b)) *
        H0 ((sdvWave n x : ℂ) * b) * b =
      (√(2 / (Real.pi * sdvWave n x)) * Real.exp (-(sdvWave n x) / 2) : ℝ) *
        (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
          sdvAmplitude x n ℰ Φ₁ εH b * Complex.exp ((n : ℂ) * phiX Φ₀ x b)) := by
  have hk_pos : 0 < sdvWave n x := by
    have hxi : 0 < x := lt_trans (by simp [xiStar]; positivity) hx
    unfold sdvWave
    positivity [Real.pi_pos]
  have him_pos : 0 < b.im := mem_edgeStrip_im_pos hδ hb
  rw [hH.hankel b hb]
  have hmul : ((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * b))) ^ (1 / 2 : ℂ) * b =
      (√(2 / (Real.pi * sdvWave n x)) : ℂ) * b ^ (1 / 2 : ℂ) :=
    hankelZeroPrefactor_mul (sdvWave n x) hk_pos him_pos
  have hexp_phase : Complex.exp (Complex.I * ((sdvWave n x : ℂ) * b - Real.pi / 4)) =
      (Real.exp (-(sdvWave n x) / 2) : ℝ) * Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
        Complex.exp ((n : ℂ) * (Complex.I * (4 * Real.pi / 3) * (x : ℂ) * (b - Complex.I / 2))) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold sdvWave
    push_cast
    have hsplit : (n : ℂ) * (Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) * (b - Complex.I / 2)) =
        (n : ℂ) * (Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) * b) -
          ((n : ℂ) * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) / 2) * (Complex.I * Complex.I) := by
      ring
    rw [hsplit, Complex.I_mul_I]
    ring
  have hexp_n : Complex.exp ((n : ℂ) * Φ₀ b + Φ₁ b) *
        Complex.exp ((n : ℂ) * (Complex.I * (4 * Real.pi / 3) * (x : ℂ) * (b - Complex.I / 2))) =
      Complex.exp (Φ₁ b) * Complex.exp ((n : ℂ) * phiX Φ₀ x b) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold phiX
    ring
  calc (ℰ b * Complex.exp ((n : ℂ) * Φ₀ b + Φ₁ b)) *
        (((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * b))) ^ (1 / 2 : ℂ) *
          Complex.exp (Complex.I * ((sdvWave n x : ℂ) * b - Real.pi / 4)) *
          (1 + εH ((sdvWave n x : ℂ) * b))) * b
      = ℰ b * Complex.exp ((n : ℂ) * Φ₀ b + Φ₁ b) *
          (((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * b))) ^ (1 / 2 : ℂ) * b) *
          Complex.exp (Complex.I * ((sdvWave n x : ℂ) * b - Real.pi / 4)) *
          (1 + εH ((sdvWave n x : ℂ) * b)) := by ring
    _ = ℰ b * Complex.exp ((n : ℂ) * Φ₀ b + Φ₁ b) *
          ((√(2 / (Real.pi * sdvWave n x)) : ℂ) * b ^ (1 / 2 : ℂ)) *
          ((Real.exp (-(sdvWave n x) / 2) : ℝ) * Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
            Complex.exp ((n : ℂ) * (Complex.I * (4 * Real.pi / 3) * (x : ℂ) * (b - Complex.I / 2)))) *
          (1 + εH ((sdvWave n x : ℂ) * b)) := by rw [hmul, hexp_phase]
    _ = (√(2 / (Real.pi * sdvWave n x)) : ℂ) * (Real.exp (-(sdvWave n x) / 2) : ℝ) *
          (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
            (ℰ b * b ^ (1 / 2 : ℂ) * (1 + εH ((sdvWave n x : ℂ) * b)) *
              (Complex.exp ((n : ℂ) * Φ₀ b + Φ₁ b) *
                Complex.exp ((n : ℂ) * (Complex.I * (4 * Real.pi / 3) * (x : ℂ) * (b - Complex.I / 2)))))) := by
          ring
    _ = (√(2 / (Real.pi * sdvWave n x)) * Real.exp (-(sdvWave n x) / 2) : ℝ) *
          (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
            sdvAmplitude x n ℰ Φ₁ εH b * Complex.exp ((n : ℂ) * phiX Φ₀ x b)) := by
          rw [hexp_n]
          unfold sdvAmplitude
          push_cast
          ring

lemma twoSaddleAmplitude_of_sdv {Φ₀ : ℂ → ℂ} {x n δ M M' : ℝ} {ℰ Φ₁ H0 εH : ℂ → ℂ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (hx : xiStar < x) (hn : 0 < n)
    (hΦ : EdgePhaseData δ C₃ C₄ Φ₀) (hH : SDVHypotheses Φ₀ x n δ M M' ℰ Φ₁ H0 εH) :
    TwoSaddleAmplitude Φ₀ x n δ M M' (sdvAmplitude x n ℰ Φ₁ εH) := by
  let A := sdvAmplitude x n ℰ Φ₁ εH
  have hk_pos : 0 < sdvWave n x := by
    have hxi : 0 < x := lt_trans (by simp [xiStar]; positivity) hx
    unfold sdvWave
    positivity [Real.pi_pos]
  let c₀ : ℝ := √(2 / (Real.pi * sdvWave n x)) * Real.exp (-(sdvWave n x) / 2)
  have hc₀_pos : 0 < c₀ := by positivity
  obtain ⟨C_h, a_h, hCh_nn, hah_pos, hh_dec⟩ := hH.h_decay
  obtain ⟨C_ε, hCε⟩ := hH.eps_bound
  have hCε_nn : 0 ≤ C_ε := by
    have hb0 : bX x ∈ edgeStrip δ := bX_mem_edgeStrip hδ0.le x
    exact (norm_nonneg _).trans (hCε _ hb0)
  have hstrip_point_bd : ∀ v t : ℝ, 1 / 2 - δ ≤ t → t ≤ 1 / 2 →
      ‖A ((v : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I))‖ ≤
        (c₀⁻¹ * C_h * √(2 / (Real.pi * sdvWave n x)) * C_ε * Real.exp (-(sdvWave n x) * (1 / 2 - δ)) *
          (1 + ‖((v : ℂ) + (t : ℂ) * Complex.I)‖)) * Real.exp (-a_h * |v|) := by
    intro v t ht1 ht2
    have hb : (v : ℂ) + (t : ℂ) * Complex.I ∈ edgeStrip δ := by
      show |((v : ℂ) + (t : ℂ) * Complex.I).im - 1 / 2| ≤ δ
      have him : ((v : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      rw [him]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hid := sdv_integrand_eq hx hn hδ1 hH hb
    have hA_eq : A ((v : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I)) =
        ((c₀ : ℂ)⁻¹ * Complex.exp (Complex.I * (Real.pi / 4 : ℂ))) *
          ((ℰ ((v : ℂ) + (t : ℂ) * Complex.I) *
              Complex.exp ((n : ℂ) * Φ₀ ((v : ℂ) + (t : ℂ) * Complex.I) +
                Φ₁ ((v : ℂ) + (t : ℂ) * Complex.I))) *
            H0 ((sdvWave n x : ℂ) * ((v : ℂ) + (t : ℂ) * Complex.I)) *
            ((v : ℂ) + (t : ℂ) * Complex.I)) := by
      rw [hid]
      have h_pref_unit : Complex.exp (Complex.I * (Real.pi / 4 : ℂ)) *
          Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) = 1 := by
        rw [← Complex.exp_add]
        simp
      have hc₀_ne : (c₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc₀_pos.ne'
      calc A ((v : ℂ) + (t : ℂ) * Complex.I) *
            Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I))
          = 1 * (A ((v : ℂ) + (t : ℂ) * Complex.I) *
              Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I))) := (one_mul _).symm
        _ = ((c₀ : ℂ)⁻¹ * (c₀ : ℂ)) *
              ((Complex.exp (Complex.I * (Real.pi / 4 : ℂ)) *
                Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))) *
              (A ((v : ℂ) + (t : ℂ) * Complex.I) *
                Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I)))) := by
              rw [inv_mul_cancel₀ hc₀_ne, h_pref_unit]; ring
        _ = _ := by ring
    have he_unit : ‖Complex.exp (Complex.I * (Real.pi / 4 : ℂ))‖ = 1 := by
      rw [show Complex.I * (Real.pi / 4 : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    have hH0_bd : ‖H0 ((sdvWave n x : ℂ) * ((v : ℂ) + (t : ℂ) * Complex.I)) *
          ((v : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        √(2 / (Real.pi * sdvWave n x)) * C_ε * Real.exp (-(sdvWave n x) * (1 / 2 - δ)) *
          (1 + ‖((v : ℂ) + (t : ℂ) * Complex.I)‖) := by
      rw [hH.hankel _ hb]
      have him_pos : 0 < ((v : ℂ) + (t : ℂ) * Complex.I).im := mem_edgeStrip_im_pos hδ1 hb
      have hmul : ((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) *
            ((v : ℂ) + (t : ℂ) * Complex.I)))) ^ (1 / 2 : ℂ) *
            ((v : ℂ) + (t : ℂ) * Complex.I) =
          (√(2 / (Real.pi * sdvWave n x)) : ℂ) *
            ((v : ℂ) + (t : ℂ) * Complex.I) ^ (1 / 2 : ℂ) :=
        hankelZeroPrefactor_mul (sdvWave n x) hk_pos him_pos
      have h_eq : ((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) *
            ((v : ℂ) + (t : ℂ) * Complex.I)))) ^ (1 / 2 : ℂ) *
            Complex.exp (Complex.I * ((sdvWave n x : ℂ) * ((v : ℂ) + (t : ℂ) * Complex.I) -
              Real.pi / 4)) *
            (1 + εH ((sdvWave n x : ℂ) * ((v : ℂ) + (t : ℂ) * Complex.I))) *
            ((v : ℂ) + (t : ℂ) * Complex.I) =
          (√(2 / (Real.pi * sdvWave n x)) : ℂ) *
            ((v : ℂ) + (t : ℂ) * Complex.I) ^ (1 / 2 : ℂ) *
            Complex.exp (Complex.I * ((sdvWave n x : ℂ) * ((v : ℂ) + (t : ℂ) * Complex.I) -
              Real.pi / 4)) *
            (1 + εH ((sdvWave n x : ℂ) * ((v : ℂ) + (t : ℂ) * Complex.I))) := by
        rw [← hmul]; ring
      rw [h_eq, norm_mul, norm_mul, norm_mul]
      have h_sqrt_norm : ‖(√(2 / (Real.pi * sdvWave n x)) : ℂ)‖ =
          √(2 / (Real.pi * sdvWave n x)) := by
        rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have h_cpow_norm : ‖((v : ℂ) + (t : ℂ) * Complex.I) ^ (1 / 2 : ℂ)‖ ≤
          1 + ‖((v : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real,
          ← Real.sqrt_eq_rpow]
        rcases le_total ‖(v : ℂ) + (t : ℂ) * Complex.I‖ 1 with hle | hge
        · exact (Real.sqrt_le_one.mpr hle).trans (by linarith [norm_nonneg ((v : ℂ) + (t : ℂ) * Complex.I)])
        · have h1 : √‖(v : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(v : ℂ) + (t : ℂ) * Complex.I‖ := by
            calc √‖(v : ℂ) + (t : ℂ) * Complex.I‖ ≤ √(‖(v : ℂ) + (t : ℂ) * Complex.I‖ ^ 2) := by
                  gcongr; exact le_self_pow₀ hge (by decide)
              _ = ‖(v : ℂ) + (t : ℂ) * Complex.I‖ := Real.sqrt_sq (norm_nonneg _)
          linarith
      have h_exp_norm : ‖Complex.exp (Complex.I * ((sdvWave n x : ℂ) *
            ((v : ℂ) + (t : ℂ) * Complex.I) - Real.pi / 4))‖ ≤
          Real.exp (-(sdvWave n x) * (1 / 2 - δ)) := by
        rw [Complex.norm_exp]
        refine Real.exp_le_exp.mpr ?_
        have hre : (Complex.I * ((sdvWave n x : ℂ) *
            ((v : ℂ) + (t : ℂ) * Complex.I) - Real.pi / 4)).re = -(sdvWave n x) * t := by
          simp
        rw [hre]
        nlinarith
      rw [h_sqrt_norm]
      have h_ep : ‖1 + εH ((sdvWave n x : ℂ) * ((v : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C_ε :=
        hCε _ hb
      calc √(2 / (Real.pi * sdvWave n x)) *
            ‖((v : ℂ) + (t : ℂ) * Complex.I) ^ (1 / 2 : ℂ)‖ *
            ‖Complex.exp (Complex.I * ((sdvWave n x : ℂ) * ((v : ℂ) + (t : ℂ) * Complex.I) -
              Real.pi / 4))‖ *
            ‖1 + εH ((sdvWave n x : ℂ) * ((v : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ √(2 / (Real.pi * sdvWave n x)) * (1 + ‖(v : ℂ) + (t : ℂ) * Complex.I‖) *
              Real.exp (-(sdvWave n x) * (1 / 2 - δ)) * C_ε := by
            gcongr
        _ = √(2 / (Real.pi * sdvWave n x)) * C_ε * Real.exp (-(sdvWave n x) * (1 / 2 - δ)) *
              (1 + ‖(v : ℂ) + (t : ℂ) * Complex.I‖) := by ring
    rw [mul_assoc (ℰ _ * _)] at hA_eq
    rw [hA_eq, norm_mul, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hc₀_pos.le, he_unit, mul_one, norm_mul]
    calc c₀⁻¹ * (‖ℰ ((v : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * Φ₀ ((v : ℂ) + (t : ℂ) * Complex.I) +
            Φ₁ ((v : ℂ) + (t : ℂ) * Complex.I))‖ *
          ‖H0 ((sdvWave n x : ℂ) * ((v : ℂ) + (t : ℂ) * Complex.I)) *
            ((v : ℂ) + (t : ℂ) * Complex.I)‖)
        ≤ c₀⁻¹ * ((C_h * Real.exp (-a_h * |v|)) *
            (√(2 / (Real.pi * sdvWave n x)) * C_ε * Real.exp (-(sdvWave n x) * (1 / 2 - δ)) *
              (1 + ‖(v : ℂ) + (t : ℂ) * Complex.I‖))) := by
          gcongr
          exact hh_dec v t ht1 ht2
      _ = (c₀⁻¹ * C_h * √(2 / (Real.pi * sdvWave n x)) * C_ε *
            Real.exp (-(sdvWave n x) * (1 / 2 - δ)) * (1 + ‖(v : ℂ) + (t : ℂ) * Complex.I‖)) *
            Real.exp (-a_h * |v|) := by ring
  let K : ℝ := c₀⁻¹ * C_h * √(2 / (Real.pi * sdvWave n x)) * C_ε *
    Real.exp (-(sdvWave n x) * (1 / 2 - δ))
  have hK_nn : 0 ≤ K := by positivity
  have h_horiz_int : ∀ t : ℝ, 1 / 2 - δ ≤ t → t ≤ 1 / 2 →
      Integrable (fun v : ℝ => A ((v : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I))) volume := by
    intro t ht1 ht2
    have hcont : Continuous fun v : ℝ => A ((v : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I)) := by
      have hf : Continuous fun u : ℝ => (u : ℂ) + (t : ℂ) * Complex.I := by fun_prop
      refine Continuous.mul ?_ (Complex.continuous_exp.comp (continuous_const.mul ?_))
      · rw [continuous_iff_continuousAt]
        intro v
        have hmem : (v : ℂ) + (t : ℂ) * Complex.I ∈ edgeStrip δ := by
          show |((v : ℂ) + (t : ℂ) * Complex.I).im - 1 / 2| ≤ δ
          have him : ((v : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
          rw [him]
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        exact ContinuousAt.comp (g := fun z : ℂ => A z)
          (f := fun u : ℝ => (u : ℂ) + (t : ℂ) * Complex.I) (x := v)
          (hH.analytic _ hmem).continuousAt hf.continuousAt
      · rw [continuous_iff_continuousAt]
        intro v
        have hmem : (v : ℂ) + (t : ℂ) * Complex.I ∈ edgeStrip δ := by
          show |((v : ℂ) + (t : ℂ) * Complex.I).im - 1 / 2| ≤ δ
          have him : ((v : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
          rw [him]
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        exact ContinuousAt.comp (g := fun z : ℂ => phiX Φ₀ x z)
          (f := fun u : ℝ => (u : ℂ) + (t : ℂ) * Complex.I) (x := v)
          ((phiX_analyticOnNhd hΦ x) _ hmem).continuousAt hf.continuousAt
    have hint_dom : Integrable (fun v : ℝ => (K * (1 + |t|)) * ((1 + |v|) * Real.exp (-a_h * |v|))) volume :=
      (integrable_one_add_abs_mul_exp_neg hah_pos).const_mul (K * (1 + |t|))
    refine hint_dom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    have hpt := hstrip_point_bd v t ht1 ht2
    have h_norm_v : 1 + ‖(v : ℂ) + (t : ℂ) * Complex.I‖ ≤ (1 + |t|) * (1 + |v|) := by
      have h1 : ‖(v : ℂ) + (t : ℂ) * Complex.I‖ ≤ |v| + |t| := by
        calc ‖(v : ℂ) + (t : ℂ) * Complex.I‖
            ≤ ‖(v : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = |v| + |t| := by simp [Complex.norm_real]
      have h2 : 0 ≤ |t| * |v| := mul_nonneg (abs_nonneg t) (abs_nonneg v)
      nlinarith
    calc ‖A ((v : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ (K * (1 + ‖(v : ℂ) + (t : ℂ) * Complex.I‖)) * Real.exp (-a_h * |v|) := hpt
      _ ≤ (K * ((1 + |t|) * (1 + |v|))) * Real.exp (-a_h * |v|) := by gcongr
      _ = (K * (1 + |t|)) * ((1 + |v|) * Real.exp (-a_h * |v|)) := by ring
  have h_edge_int : Integrable (fun v : ℝ => A ((v : ℂ) + Complex.I / 2) *
      Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) volume := by
    have h12 : 1 / 2 - δ ≤ (1 / 2 : ℝ) := by linarith [hδ0]
    have hpt : (fun v : ℝ => A ((v : ℂ) + Complex.I / 2) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) =
        fun v : ℝ => A ((v : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I)) := by
      ext v
      have hz : (v : ℂ) + Complex.I / 2 = (v : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hz]
    rw [hpt]
    exact h_horiz_int (1 / 2) h12 le_rfl
  have h_lower_int : ∀ u₀ : ℝ, 0 < u₀ → u₀ ≤ δ →
      Integrable (fun v : ℝ => A ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)))) volume := by
    intro u₀ hu₀_pos hu₀_le
    simpa [mul_comm Complex.I _] using h_horiz_int (1 / 2 - u₀) (by linarith) (by linarith)
  have h_vert_bd : ∀ s : ℝ, |s| = 1 → ∀ u₀ : ℝ, 0 < u₀ → u₀ ≤ δ →
      Tendsto (fun R : ℝ => ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
        A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
        atTop (𝓝 0) := by
    intro s hs u₀ hu₀_pos hu₀_le
    have hbound : ∀ᶠ R : ℝ in atTop,
        ‖∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
          A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
            Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤
          (K * u₀) * ((2 + R) * Real.exp (-a_h * R)) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
      have ha_le : (1 / 2 - u₀ : ℝ) ≤ 1 / 2 := by linarith
      have hm_le : ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
            ‖A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
              Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤
          ∫ _t in (1 / 2 - u₀)..(1 / 2 : ℝ), K * (2 + R) * Real.exp (-a_h * R) := by
        refine intervalIntegral.integral_mono_on ha_le ?_ intervalIntegrable_const ?_
        · have hcont_seg : ContinuousOn (fun t : ℝ => A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
              Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
              (Icc (1 / 2 - u₀) (1 / 2 : ℝ)) := by
            have hf : Continuous fun y : ℝ => ((s * R : ℝ) : ℂ) + (y : ℂ) * Complex.I := by fun_prop
            refine ContinuousOn.mul ?_ (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_))
            · intro t ht
              have ht' : t ∈ Icc (1 / 2 - u₀) (1 / 2 : ℝ) := ht
              have hmem : ((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I ∈ edgeStrip δ := by
                show |(((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I).im - 1 / 2| ≤ δ
                have him : (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
                rw [him]
                exact abs_le.mpr ⟨by linarith [ht'.1], by linarith [ht'.2, hδ0]⟩
              exact ContinuousAt.comp_continuousWithinAt (g := fun z : ℂ => A z)
                (f := fun y : ℝ => ((s * R : ℝ) : ℂ) + (y : ℂ) * Complex.I)
                (s := Icc (1 / 2 - u₀) (1 / 2 : ℝ)) (x := t)
                (hH.analytic _ hmem).continuousAt hf.continuousWithinAt
            · intro t ht
              have ht' : t ∈ Icc (1 / 2 - u₀) (1 / 2 : ℝ) := ht
              have hmem : ((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I ∈ edgeStrip δ := by
                show |(((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I).im - 1 / 2| ≤ δ
                have him : (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
                rw [him]
                exact abs_le.mpr ⟨by linarith [ht'.1], by linarith [ht'.2, hδ0]⟩
              exact ContinuousAt.comp_continuousWithinAt (g := fun z : ℂ => phiX Φ₀ x z)
                (f := fun y : ℝ => ((s * R : ℝ) : ℂ) + (y : ℂ) * Complex.I)
                (s := Icc (1 / 2 - u₀) (1 / 2 : ℝ)) (x := t)
                ((phiX_analyticOnNhd hΦ x) _ hmem).continuousAt hf.continuousWithinAt
          apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le ha_le]
          exact hcont_seg.norm
        · intro t ht
          have ht1 : 1 / 2 - δ ≤ t := by linarith [ht.1]
          have ht2 : t ≤ 1 / 2 := ht.2
          have hpt := hstrip_point_bd (s * R) t ht1 ht2
          have habs : |s * R| = R := by rw [abs_mul, hs, one_mul, abs_of_nonneg hR]
          have h_norm_z : ‖((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ≤ 1 + R := by
            have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
            calc ‖((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I‖
                ≤ ‖((s * R : ℝ) : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
              _ = |s * R| + |t| := by simp [Complex.norm_real]
              _ ≤ R + 1 := by rw [habs]; linarith
              _ = 1 + R := by ring
          calc ‖A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
                Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
              ≤ (K * (1 + ‖((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I‖)) * Real.exp (-a_h * |s * R|) := hpt
            _ ≤ K * (1 + (1 + R)) * Real.exp (-a_h * R) := by rw [habs]; gcongr
            _ = K * (2 + R) * Real.exp (-a_h * R) := by ring
      have hn_int : ‖∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
            A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
              Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤
          ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
            ‖A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
              Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ :=
        intervalIntegral.norm_integral_le_integral_norm ha_le
      have hc_eq : ∫ _t in (1 / 2 - u₀)..(1 / 2 : ℝ), K * (2 + R) * Real.exp (-a_h * R) =
          (K * u₀) * ((2 + R) * Real.exp (-a_h * R)) := by
        simp only [intervalIntegral.integral_const, sub_sub_cancel, smul_eq_mul]
        ring
      exact hn_int.trans (hm_le.trans_eq hc_eq)
    have ht_zero : Tendsto (fun R : ℝ => (K * u₀) * ((2 + R) * Real.exp (-a_h * R))) atTop (𝓝 0) := by
      have hsub : Tendsto (fun R : ℝ => (2 + 2 / a_h) * (2 / (a_h * R))) atTop (𝓝 0) := by
        have hinv : Tendsto (fun R : ℝ => (2 * (2 + 2 / a_h) / a_h) / R) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        refine hinv.congr' (Filter.Eventually.of_forall fun R => by ring)
      have hsq : Tendsto (fun R : ℝ => (2 + R) * Real.exp (-a_h * R)) atTop (𝓝 0) := by
        refine squeeze_zero' ?_ ?_ hsub
        · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
          exact mul_nonneg (by linarith) (Real.exp_pos _).le
        · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
          have h1 : (a_h / 2) * R ≤ Real.exp ((a_h / 2) * R) := by
            linarith [Real.add_one_le_exp ((a_h / 2) * R)]
          have hR_le : R ≤ (2 / a_h) * Real.exp ((a_h / 2) * R) := by
            calc R = (2 / a_h) * ((a_h / 2) * R) := by field_simp [hah_pos.ne']
              _ ≤ (2 / a_h) * Real.exp ((a_h / 2) * R) := by gcongr
          have hexp_ge1 : 1 ≤ Real.exp ((a_h / 2) * R) := Real.one_le_exp (by positivity)
          have hnum : 2 + R ≤ (2 + 2 / a_h) * Real.exp ((a_h / 2) * R) := by linarith
          have h2 : Real.exp (-(a_h / 2) * R) ≤ 2 / (a_h * R) := by
            rw [show -(a_h / 2) * R = -((a_h / 2) * R) by ring, Real.exp_neg,
              inv_le_comm₀ (Real.exp_pos _) (by positivity)]
            simpa [one_div, inv_div, div_div, mul_comm, mul_assoc, div_eq_mul_inv] using
              (by linarith : (a_h * R / 2) ≤ Real.exp ((a_h / 2) * R))
          calc (2 + R) * Real.exp (-a_h * R)
              ≤ ((2 + 2 / a_h) * Real.exp ((a_h / 2) * R)) * Real.exp (-a_h * R) := by gcongr
            _ = (2 + 2 / a_h) * Real.exp (-(a_h / 2) * R) := by
                rw [mul_assoc, ← Real.exp_add]; congr 2; ring
            _ ≤ (2 + 2 / a_h) * (2 / (a_h * R)) := by gcongr
      simpa using hsq.const_mul (K * u₀)
    exact squeeze_zero_norm' hbound ht_zero
  have h_vert_R : ∀ u₀ : ℝ, 0 < u₀ → u₀ ≤ δ →
      Tendsto (fun R : ℝ => ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
        A ((R : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((R : ℂ) + (t : ℂ) * Complex.I)))
        atTop (𝓝 0) := fun u₀ hu₀_pos hu₀_le => by
    simpa using h_vert_bd 1 abs_one u₀ hu₀_pos hu₀_le
  have h_vert_L : ∀ u₀ : ℝ, 0 < u₀ → u₀ ≤ δ →
      Tendsto (fun R : ℝ => ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
        A ((-R : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((-R : ℂ) + (t : ℂ) * Complex.I)))
        atTop (𝓝 0) := fun u₀ hu₀_pos hu₀_le => by
    simpa [Complex.ofReal_neg] using h_vert_bd (-1) (by norm_num) u₀ hu₀_pos hu₀_le
  have h_symm : ∀ v : ℝ,
      Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * A ((-v : ℂ) + Complex.I / 2) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((-v : ℂ) + Complex.I / 2)) =
        starRingEnd ℂ (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * A ((v : ℂ) + Complex.I / 2) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) := by
    intro v
    have hb : (v : ℂ) + Complex.I / 2 ∈ edgeStrip δ := mem_edgeStrip_edge hδ0.le v
    have hbm : (-v : ℂ) + Complex.I / 2 ∈ edgeStrip δ := by
      simpa [Complex.ofReal_neg] using mem_edgeStrip_edge hδ0.le (-v)
    have h1 := sdv_integrand_eq hx hn hδ1 hH hb
    have h2 := sdv_integrand_eq hx hn hδ1 hH hbm
    have hs := hH.edge_symm v
    dsimp only at hs
    rw [h1, h2] at hs
    have hconj : starRingEnd ℂ ((c₀ : ℂ) * (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
          A ((v : ℂ) + Complex.I / 2) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2)))) =
        (c₀ : ℂ) * starRingEnd ℂ (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
          A ((v : ℂ) + Complex.I / 2) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) := by
      rw [map_mul, Complex.conj_ofReal]
    rw [hconj] at hs
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hc₀_pos.ne') hs
  exact ⟨hH.analytic, hH.nonzero, hH.logDeriv_bound, hH.logDeriv2_bound,
    h_edge_int, h_lower_int, h_vert_R, h_vert_L, h_symm⟩

/-! ### 4. Main theorems: Lemma `SD_V` (`esd:lemma`) and non-vacuity -/

/-- **Lemma `SD_V` (`edge_transform_sd.tex`, Lemma `esd:lemma`, l.379–410, `(SD.3)–(SD.4)`)**:
Order-zero two-saddle steepest-descent asymptotic for `\widehat h(n x^2 / 3)`. Constants `N₀ ≥ 1`
and `C ≥ 0` depend only on `(δ, C₃, C₄, M, M')`, uniformly in `(Φ₀, ℰ, Φ₁, H0, εH, x, n)`. -/
theorem lemma_SD_V {δ C₃ C₄ M M' : ℝ} (hδ : 0 < δ) (hδ_le : δ ≤ 1 / 4)
    (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄) (hM : 0 ≤ M) (hM' : 0 ≤ M') :
    ∃ N₀ C : ℝ, 1 ≤ N₀ ∧ 0 ≤ C ∧
      ∀ {Φ₀ : ℂ → ℂ} {x n : ℝ} {ℰ Φ₁ H0 εH : ℂ → ℂ},
        xiStar < x → 0 < n → N₀ ≤ n * mX x ^ 3 →
        EdgePhaseData δ C₃ C₄ Φ₀ →
        SDVHypotheses Φ₀ x n δ M M' ℰ Φ₁ H0 εH →
        ∃ err : ℝ,
          |err| ≤ C / (n * mX x ^ 3) ∧
          sdvIntegral Φ₀ n x ℰ Φ₁ H0 =
            ((sdvPrefactor n x ℰ Φ₁ εH *
              (Real.cos (sdvPhase Φ₀ n x ℰ Φ₁ εH) + err) : ℝ) : ℂ) := by
  obtain ⟨N₀, C, hN₀, hC, h_sdvp⟩ := lemma_SD_V_prime hδ hδ_le hC₃ hC₄ hM hM'
  refine ⟨N₀, C, hN₀, hC, fun {Φ₀ x n ℰ Φ₁ H0 εH} hx hn hnm hΦ hH => ?_⟩
  have hA := twoSaddleAmplitude_of_sdv hδ hδ_le hx hn hΦ hH
  obtain ⟨err, herr_le, h_edge_eq⟩ := h_sdvp hx hn hnm hΦ hA
  refine ⟨err, herr_le, ?_⟩
  have hk_pos : 0 < sdvWave n x := by
    have hxi : 0 < x := lt_trans (by simp [xiStar]; positivity) hx
    unfold sdvWave
    positivity [Real.pi_pos]
  let c₀ : ℝ := √(2 / (Real.pi * sdvWave n x)) * Real.exp (-(sdvWave n x) / 2)
  have h_int_eq : sdvIntegral Φ₀ n x ℰ Φ₁ H0 =
      ((2 * Real.pi * n / 3 : ℝ) : ℂ) * (c₀ : ℂ) *
        edgeIntegral Φ₀ x n (sdvAmplitude x n ℰ Φ₁ εH) := by
    unfold sdvIntegral edgeIntegral saddleIntegrand
    have h_fn : (fun v : ℝ => (ℰ ((v : ℂ) + Complex.I / 2) *
          Complex.exp ((n : ℂ) * Φ₀ ((v : ℂ) + Complex.I / 2) +
            Φ₁ ((v : ℂ) + Complex.I / 2))) *
          H0 ((sdvWave n x : ℂ) * ((v : ℂ) + Complex.I / 2)) * ((v : ℂ) + Complex.I / 2)) =
        fun v : ℝ => (c₀ : ℂ) * (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
          sdvAmplitude x n ℰ Φ₁ εH ((v : ℂ) + Complex.I / 2) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) := by
      ext v
      exact sdv_integrand_eq hx hn hδ_le hH (mem_edgeStrip_edge hδ.le v)
    rw [h_fn, integral_const_mul]
    ring
  have hx_pos : 0 < x := lt_trans (by simp [xiStar]; positivity) hx
  have hF'_pos : 0 < edgeF' (edgeV x) := edgeF'_pos (edgeV_pos hx)
  have ha_pos : 0 < alphaX x := alphaX_pos hx
  have h_sqrt_simp :
      (2 * Real.pi * n / 3) * √(2 / (Real.pi * sdvWave n x)) * √(2 * Real.pi / (n * alphaX x)) =
        √(1 / (x * edgeF' (edgeV x))) := by
    have hpi := Real.pi_pos
    have h1 : 0 ≤ 2 / (Real.pi * sdvWave n x) := by positivity
    have h2 : 0 ≤ 2 * Real.pi / (n * alphaX x) := by positivity
    have hprod : √(2 / (Real.pi * sdvWave n x)) * √(2 * Real.pi / (n * alphaX x)) =
        √((3 / (2 * Real.pi * n)) ^ 2 * (1 / (x * edgeF' (edgeV x)))) := by
      rw [← Real.sqrt_mul h1]
      congr 1
      unfold sdvWave alphaX
      field_simp [hpi.ne', hn.ne', hx_pos.ne', hF'_pos.ne']
      ring
    rw [mul_assoc (2 * Real.pi * n / 3), hprod, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    field_simp [hpi.ne', hn.ne']
  have h_amp_norm : ‖sdvAmplitude x n ℰ Φ₁ εH (bX x)‖ =
      ‖ℰ (bX x)‖ * Real.exp (Φ₁ (bX x)).re * √‖bX x‖ *
        ‖1 + εH ((sdvWave n x : ℂ) * bX x)‖ := by
    unfold sdvAmplitude
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real,
      ← Real.sqrt_eq_rpow]
  have h_pref_eq : (2 * Real.pi * n / 3) * c₀ *
        (2 * ‖sdvAmplitude x n ℰ Φ₁ εH (bX x)‖ * √(2 * Real.pi / (n * alphaX x))) =
      sdvPrefactor n x ℰ Φ₁ εH := by
    have hexp_wave : Real.exp (-(sdvWave n x) / 2) = Real.exp (-2 * Real.pi * n * x / 3) := by
      unfold sdvWave; congr 1; ring
    have hsqrt_bx : √‖bX x‖ * √(1 / (x * edgeF' (edgeV x))) =
        √(‖bX x‖ / (x * edgeF' (edgeV x))) := by
      rw [← Real.sqrt_mul (norm_nonneg _)]
      congr 1; ring
    calc (2 * Real.pi * n / 3) * c₀ *
          (2 * ‖sdvAmplitude x n ℰ Φ₁ εH (bX x)‖ * √(2 * Real.pi / (n * alphaX x)))
        = 2 * Real.exp (-(sdvWave n x) / 2) * ‖sdvAmplitude x n ℰ Φ₁ εH (bX x)‖ *
            ((2 * Real.pi * n / 3) * √(2 / (Real.pi * sdvWave n x)) *
              √(2 * Real.pi / (n * alphaX x))) := by
          dsimp [c₀]; ring
      _ = 2 * Real.exp (-2 * Real.pi * n * x / 3) *
            (‖ℰ (bX x)‖ * Real.exp (Φ₁ (bX x)).re * √‖bX x‖ *
              ‖1 + εH ((sdvWave n x : ℂ) * bX x)‖) *
            √(1 / (x * edgeF' (edgeV x))) := by
          rw [hexp_wave, h_amp_norm, h_sqrt_simp]
      _ = 2 * Real.exp (-2 * Real.pi * n * x / 3) * ‖ℰ (bX x)‖ * Real.exp (Φ₁ (bX x)).re *
            ‖1 + εH ((sdvWave n x : ℂ) * bX x)‖ *
            (√‖bX x‖ * √(1 / (x * edgeF' (edgeV x)))) := by ring
      _ = sdvPrefactor n x ℰ Φ₁ εH := by rw [hsqrt_bx]; rfl
  rw [h_int_eq, h_edge_eq]
  have hphase : n * (Φ₀ (bX x)).im + 4 * Real.pi * n * x / 3 * edgeV x - Real.pi / 2 +
        (sdvAmplitude x n ℰ Φ₁ εH (bX x)).arg =
      sdvPhase Φ₀ n x ℰ Φ₁ εH := by
    unfold sdvPhase sdvWave; rfl
  rw [hphase]
  calc ((2 * Real.pi * n / 3 : ℝ) : ℂ) * (c₀ : ℂ) *
        ((2 * ‖sdvAmplitude x n ℰ Φ₁ εH (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) *
          (Real.cos (sdvPhase Φ₀ n x ℰ Φ₁ εH) + err) : ℝ) : ℂ)
      = (((2 * Real.pi * n / 3) * c₀ *
          (2 * ‖sdvAmplitude x n ℰ Φ₁ εH (bX x)‖ * √(2 * Real.pi / (n * alphaX x))) : ℝ) : ℂ) *
          ((Real.cos (sdvPhase Φ₀ n x ℰ Φ₁ εH) + err : ℝ) : ℂ) := by
        push_cast; ring
    _ = ((sdvPrefactor n x ℰ Φ₁ εH *
          (Real.cos (sdvPhase Φ₀ n x ℰ Φ₁ εH) + err) : ℝ) : ℂ) := by
        rw [h_pref_eq]; push_cast; rfl

/-- **(SD.5) Uniform lower bound on `m_x^3`** (`edge_transform_sd.tex`, l.411–415):
there exists an absolute constant `c > 0` such that `c * min 1 (x - ξ_*)^{3/2} ≤ m_x^3` for
every `x > ξ_*`, so the error `C / (n m_x³)` in `lemma_SD_V` is `o(1)` uniformly on `x ≥ x_I(n)`
whenever `n (x_I - ξ_*)^{3/2} → ∞`. -/
theorem sdv_uniform_mX_cubed :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, xiStar < x →
      c * min 1 ((x - xiStar) ^ (3 / 2 : ℝ)) ≤ mX x ^ 3 := by
  obtain ⟨cm, _, hcm_pos, _, hm_unif⟩ := mX_uniform_bounds
  obtain ⟨cv, _, hcv_pos, _, hv_near⟩ := edgeV_near_xiStar_bounds
  let V₁ : ℝ := edgeV (xiStar + 1)
  have hV₁_pos : 0 < V₁ := edgeV_pos (by linarith)
  let c0 : ℝ := min 1 (min (cv * √1) (min V₁ (cm * min 1 (min cv V₁))))
  have hc0_pos : 0 < c0 := by positivity
  let c : ℝ := (cm * min 1 (min cv V₁)) ^ 3
  have hc_pos : 0 < c := by positivity
  refine ⟨c, hc_pos, fun x hx => ?_⟩
  have hmin_ge : min 1 (min cv V₁) * min 1 (√(x - xiStar)) ≤ min 1 (edgeV x) := by
    rcases le_or_gt x (xiStar + 1) with hx1 | hx1
    · have h_v := (hv_near x ⟨hx, hx1⟩).1
      have hx0 : 0 ≤ x - xiStar := by linarith
      have hsq1 : √(x - xiStar) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
      rw [min_eq_right hsq1]
      refine le_min ?_ ?_
      · calc min 1 (min cv V₁) * √(x - xiStar) ≤ 1 * 1 :=
              mul_le_mul (min_le_left _ _) hsq1 (Real.sqrt_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      · calc min 1 (min cv V₁) * √(x - xiStar)
            ≤ cv * √(x - xiStar) := by
              gcongr
              exact (min_le_right _ _).trans (min_le_left _ _)
          _ ≤ edgeV x := h_v
    · have hmono : V₁ ≤ edgeV x := by
        by_contra hlt
        push Not at hlt
        have hF1 : edgeF (edgeV x) < edgeF V₁ :=
          edgeF_strictMonoOn (edgeV_pos hx).le hV₁_pos.le hlt
        have hFx : edgeF (edgeV x) = x := edgeF_edgeV hx
        have hFV1 : edgeF V₁ = xiStar + 1 := edgeF_edgeV (by linarith)
        linarith
      have hsq1 : 1 ≤ √(x - xiStar) := Real.one_le_sqrt.mpr (by linarith)
      rw [min_eq_left hsq1, mul_one]
      exact le_min (min_le_left _ _) ((min_le_right _ _).trans (min_le_right _ _) |>.trans hmono)
  have hpow_min : min 1 ((x - xiStar) ^ (3 / 2 : ℝ)) = (min 1 (√(x - xiStar))) ^ 3 := by
    have hx0 : 0 ≤ x - xiStar := by linarith
    rcases le_or_gt (x - xiStar) 1 with h1 | h1
    · have hsq1 : √(x - xiStar) ≤ 1 := Real.sqrt_le_one.mpr h1
      have hpow1 : (x - xiStar) ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hx0 h1 (by positivity)
      rw [min_eq_right hpow1, min_eq_right hsq1, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul hx0]
      norm_num
    · have hsq1 : 1 ≤ √(x - xiStar) := Real.one_le_sqrt.mpr h1.le
      have hpow1 : 1 ≤ (x - xiStar) ^ (3 / 2 : ℝ) := Real.one_le_rpow h1.le (by positivity)
      rw [min_eq_left hpow1, min_eq_left hsq1, one_pow]
  have hm_lb : (cm * min 1 (min cv V₁)) * min 1 (√(x - xiStar)) ≤ mX x := by
    calc (cm * min 1 (min cv V₁)) * min 1 (√(x - xiStar))
        = cm * (min 1 (min cv V₁) * min 1 (√(x - xiStar))) := by ring
      _ ≤ cm * min 1 (edgeV x) := by gcongr
      _ ≤ mX x := (hm_unif x hx).1
  have hpow_le := pow_le_pow_left₀ (by positivity) hm_lb 3
  rw [mul_pow, ← hpow_min] at hpow_le
  exact hpow_le

private lemma sdv_cosh_re_im (z : ℂ) :
    (Complex.cosh z).re = Real.cosh z.re * Real.cos z.im ∧
      (Complex.cosh z).im = Real.sinh z.re * Real.sin z.im := by
  have hde : Complex.cosh z =
      (Real.cosh z.re : ℂ) * (Real.cos z.im : ℂ) +
        (Real.sinh z.re : ℂ) * ((Real.sin z.im : ℂ) * Complex.I) := by
    conv_lhs => rw [(Complex.re_add_im z).symm]
    rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hde]
  constructor <;>
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

private lemma sdv_sinh_re_im (z : ℂ) :
    (Complex.sinh z).re = Real.sinh z.re * Real.cos z.im ∧
      (Complex.sinh z).im = Real.cosh z.re * Real.sin z.im := by
  have hde : Complex.sinh z =
      (Real.sinh z.re : ℂ) * (Real.cos z.im : ℂ) +
        (Real.cosh z.re : ℂ) * ((Real.sin z.im : ℂ) * Complex.I) := by
    conv_lhs => rw [(Complex.re_add_im z).symm]
    rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hde]
  constructor <;>
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

private lemma sdv_cosh_strip_norm_lower {z : ℂ} (hz : |z.im| ≤ Real.pi / 4) :
    Real.cosh z.re / √2 ≤ ‖Complex.cosh z‖ := by
  have hri := sdv_cosh_re_im z
  have hcos : √2 / 2 ≤ Real.cos z.im := by
    rw [← Real.cos_pi_div_four, ← Real.cos_abs z.im]
    exact Real.strictAntiOn_cos.antitoneOn
      ⟨abs_nonneg _, hz.trans (by linarith [Real.pi_pos])⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩ hz
  have hcos_sq : (1 / 2 : ℝ) ≤ Real.cos z.im ^ 2 := by
    have h1 : (√2 / 2) ^ 2 ≤ Real.cos z.im ^ 2 := pow_le_pow_left₀ (by positivity) hcos 2
    have hsq : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
    calc (1 / 2 : ℝ) = (√2 / 2) ^ 2 := by rw [div_pow, hsq]; norm_num
      _ ≤ Real.cos z.im ^ 2 := h1
  have hnsq : ‖Complex.cosh z‖ ^ 2 = Real.cos z.im ^ 2 + Real.sinh z.re ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hri.1, hri.2]
    have h1 := Real.cosh_sq z.re
    have h2 := Real.sin_sq_add_cos_sq z.im
    calc (Real.cosh z.re * Real.cos z.im) * (Real.cosh z.re * Real.cos z.im) +
          (Real.sinh z.re * Real.sin z.im) * (Real.sinh z.re * Real.sin z.im)
        = (Real.sinh z.re ^ 2 + 1) * Real.cos z.im ^ 2 + Real.sinh z.re ^ 2 * Real.sin z.im ^ 2 := by
          rw [← sq, ← sq, mul_pow, mul_pow, h1]
      _ = Real.cos z.im ^ 2 + Real.sinh z.re ^ 2 * (Real.sin z.im ^ 2 + Real.cos z.im ^ 2) := by
          ring
      _ = Real.cos z.im ^ 2 + Real.sinh z.re ^ 2 := by rw [h2, mul_one]
  have hcosh1 : 1 ≤ Real.cosh z.re := Real.one_le_cosh z.re
  have hlb_sq : (Real.cosh z.re / √2) ^ 2 ≤ ‖Complex.cosh z‖ ^ 2 := by
    have hsq : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
    have hsh : Real.sinh z.re ^ 2 = Real.cosh z.re ^ 2 - 1 := by linarith [Real.cosh_sq z.re]
    rw [hnsq, div_pow, hsq, hsh]
    nlinarith [hcosh1, hcos_sq]
  have hsqrt := Real.sqrt_le_sqrt hlb_sq
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)] at hsqrt

private lemma sdv_sinh_norm_le_cosh (z : ℂ) : ‖Complex.sinh z‖ ≤ Real.cosh z.re := by
  have hri := sdv_sinh_re_im z
  have hnsq : ‖Complex.sinh z‖ ^ 2 ≤ Real.cosh z.re ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hri.1, hri.2]
    have hsh : Real.sinh z.re ^ 2 ≤ Real.cosh z.re ^ 2 := by linarith [Real.cosh_sq z.re]
    have h2 := Real.sin_sq_add_cos_sq z.im
    calc (Real.sinh z.re * Real.cos z.im) * (Real.sinh z.re * Real.cos z.im) +
          (Real.cosh z.re * Real.sin z.im) * (Real.cosh z.re * Real.sin z.im)
        = Real.sinh z.re ^ 2 * Real.cos z.im ^ 2 + Real.cosh z.re ^ 2 * Real.sin z.im ^ 2 := by ring
      _ ≤ Real.cosh z.re ^ 2 * Real.cos z.im ^ 2 + Real.cosh z.re ^ 2 * Real.sin z.im ^ 2 := by gcongr
      _ = Real.cosh z.re ^ 2 * (Real.sin z.im ^ 2 + Real.cos z.im ^ 2) := by ring
      _ = Real.cosh z.re ^ 2 := by rw [h2, mul_one]
  have hsqrt := Real.sqrt_le_sqrt hnsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (Real.cosh_pos _).le] at hsqrt

/-- Explicit canonical witness for `SD_V` with `Φ₁ = 0`, `ε_H = 0`, `x = ξ_* + 1`, `n = 1`,
`M = √2 / 2`, and `M' = 1 / 2`. -/
lemma sdv_canonical_witness {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ (C₃ C₄ : ℝ) (Φ₀ ℰ : ℂ → ℂ),
      EdgePhaseData δ C₃ C₄ Φ₀ ∧
      SDVHypotheses Φ₀ (xiStar + 1) 1 δ (√2 / 2) (1 / 2) ℰ (fun _ => 0)
        (fun z => ((2 : ℂ) / ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ) *
          Complex.exp (Complex.I * (z - Real.pi / 4)))
        (fun _ => 0) := by
  obtain ⟨C₃, C₄, Φ₀, hΦ⟩ := edgePhaseData_nonvacuous hδ0 hδ1
  let x : ℝ := xiStar + 1
  let n : ℝ := 1
  let c₀ : ℝ := (Φ₀ (Complex.I / 2)).im
  let pref : ℂ := Complex.exp (Complex.I * ((Real.pi / 4 - c₀ : ℝ) : ℂ))
  let A₀ : ℂ → ℂ := fun b => pref * (Complex.cosh ((b - Complex.I / 2) / 2))⁻¹
  let ℰ : ℂ → ℂ := fun b => A₀ b * b ^ (-(1 / 2 : ℂ))
  let Φ₁ : ℂ → ℂ := fun _ => 0
  let εH : ℂ → ℂ := fun _ => 0
  let H0 : ℂ → ℂ := fun z =>
    ((2 : ℂ) / ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * (z - Real.pi / 4))
  let M : ℝ := √2 / 2
  let M' : ℝ := 1 / 2
  have hx : xiStar < x := by dsimp [x]; linarith
  have hn : 0 < n := by norm_num [n]
  let U : Set ℂ := {b : ℂ | |b.im - 1 / 2| < 3 / 8}
  have hU_open : IsOpen U :=
    isOpen_lt ((continuous_abs.comp (Complex.continuous_im.sub continuous_const))) continuous_const
  have hstrip_U : edgeStrip δ ⊆ U := fun b hb => by
    have hb' : |b.im - 1 / 2| ≤ δ := hb
    exact lt_of_le_of_lt hb' (lt_of_le_of_lt hδ1 (by norm_num))
  have hz_pi4 : ∀ b ∈ U, |((b - Complex.I / 2) / 2).im| ≤ Real.pi / 4 := fun b hb => by
    have him : ((b - Complex.I / 2) / 2).im = (b.im - 1 / 2) / 2 := by simp
    rw [him, abs_div, abs_of_pos (zero_lt_two : (0 : ℝ) < 2)]
    have hb' : |b.im - 1 / 2| < 3 / 8 := hb
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    linarith
  have hcosh_ne : ∀ b ∈ U, Complex.cosh ((b - Complex.I / 2) / 2) ≠ 0 := fun b hb => by
    have hlb := sdv_cosh_strip_norm_lower (hz_pi4 b hb)
    have hpos : 0 < Real.cosh ((b - Complex.I / 2) / 2).re / √2 :=
      div_pos (Real.cosh_pos _) (Real.sqrt_pos.mpr zero_lt_two)
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hpos hlb))
  have h_ax_eq_U : ∀ b ∈ U, sdvAmplitude x n ℰ Φ₁ εH b = A₀ b := fun b hb => by
    have hb_im : 0 < b.im := by
      have hb' : |b.im - 1 / 2| < 3 / 8 := hb
      linarith [(abs_lt.mp hb').1]
    have hb_ne : b ≠ 0 := fun h => by simp [h] at hb_im
    unfold sdvAmplitude
    simp only [Φ₁, εH, Complex.exp_zero, mul_one, add_zero]
    dsimp [ℰ]
    rw [mul_assoc, ← Complex.cpow_add _ _ hb_ne]
    norm_num
  have hA₀_diff_U : DifferentiableOn ℂ A₀ U := by
    intro b hb
    have hlin : HasDerivAt (fun z : ℂ => (z - Complex.I / 2) / 2) (1 / 2 : ℂ) b := by
      simpa using ((hasDerivAt_id b).sub_const _).div_const (2 : ℂ)
    have hch : HasDerivAt (fun z : ℂ => Complex.cosh ((z - Complex.I / 2) / 2))
        (Complex.sinh ((b - Complex.I / 2) / 2) * (1 / 2 : ℂ)) b :=
      (Complex.hasDerivAt_cosh _).comp b hlin
    exact ((hch.inv (hcosh_ne b hb)).const_mul pref).differentiableAt.differentiableWithinAt
  have h_ax_ev : ∀ b ∈ U, sdvAmplitude x n ℰ Φ₁ εH =ᶠ[𝓝 b] A₀ := fun b hb =>
    Filter.eventually_of_mem (hU_open.mem_nhds hb) h_ax_eq_U
  have hA_an : AnalyticOnNhd ℂ (sdvAmplitude x n ℰ Φ₁ εH) (edgeStrip δ) := by
    intro b hb
    have hA₀_an : AnalyticOnNhd ℂ A₀ U := hA₀_diff_U.analyticOnNhd hU_open
    exact (hA₀_an b (hstrip_U hb)).congr (h_ax_ev b (hstrip_U hb)).symm
  have hA_ne : ∀ b ∈ edgeStrip δ, sdvAmplitude x n ℰ Φ₁ εH b ≠ 0 := fun b hb => by
    rw [h_ax_eq_U b (hstrip_U hb)]
    exact mul_ne_zero (Complex.exp_ne_zero _) (inv_ne_zero (hcosh_ne b (hstrip_U hb)))
  have h_hankel : ∀ b ∈ edgeStrip δ,
      H0 ((sdvWave n x : ℂ) * b) =
        ((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * b))) ^ (1 / 2 : ℂ) *
          Complex.exp (Complex.I * ((sdvWave n x : ℂ) * b - Real.pi / 4)) *
          (1 + εH ((sdvWave n x : ℂ) * b)) := fun b _ => by
    dsimp [H0, εH]; ring
  have hlogderiv_eq : ∀ b ∈ U,
      deriv A₀ b / A₀ b = -(1 / 2 : ℂ) * Complex.sinh ((b - Complex.I / 2) / 2) /
        Complex.cosh ((b - Complex.I / 2) / 2) := fun b hb => by
    have hlin : HasDerivAt (fun z : ℂ => (z - Complex.I / 2) / 2) (1 / 2 : ℂ) b := by
      simpa using ((hasDerivAt_id b).sub_const _).div_const (2 : ℂ)
    have hch : HasDerivAt (fun z : ℂ => Complex.cosh ((z - Complex.I / 2) / 2))
        (Complex.sinh ((b - Complex.I / 2) / 2) * (1 / 2 : ℂ)) b :=
      (Complex.hasDerivAt_cosh _).comp b hlin
    have hA_d := (hch.inv (hcosh_ne b hb)).const_mul pref
    change deriv (fun y => pref * (fun z => Complex.cosh ((z - Complex.I / 2) / 2))⁻¹ y) b / A₀ b = _
    rw [hA_d.deriv]
    have hne := hcosh_ne b hb
    have hpref : pref ≠ 0 := Complex.exp_ne_zero _
    dsimp [A₀]
    field_simp [hne, hpref]
  have hlogderiv_bd : ∀ b ∈ edgeStrip δ,
      ‖deriv (sdvAmplitude x n ℰ Φ₁ εH) b / sdvAmplitude x n ℰ Φ₁ εH b‖ ≤ M := fun b hb => by
    have hbU := hstrip_U hb
    rw [(h_ax_ev b hbU).deriv_eq, h_ax_eq_U b hbU, hlogderiv_eq b hbU]
    have hsh := sdv_sinh_norm_le_cosh ((b - Complex.I / 2) / 2)
    have hch := sdv_cosh_strip_norm_lower (hz_pi4 b hbU)
    have h12 : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by rw [norm_neg]; norm_num
    have hcosh_pos : 0 < Real.cosh ((b - Complex.I / 2) / 2).re := Real.cosh_pos _
    rw [norm_div, norm_mul, h12]
    calc (1 / 2) * ‖Complex.sinh ((b - Complex.I / 2) / 2)‖ /
          ‖Complex.cosh ((b - Complex.I / 2) / 2)‖
        ≤ (1 / 2) * Real.cosh ((b - Complex.I / 2) / 2).re /
            (Real.cosh ((b - Complex.I / 2) / 2).re / √2) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hsh (by norm_num))
            (div_pos hcosh_pos (Real.sqrt_pos.mpr zero_lt_two)) hch
      _ = M := by dsimp [M]; field_simp [hcosh_pos.ne']
  have hlogderiv2_bd : ∀ b ∈ edgeStrip δ,
      ‖deriv (fun z => deriv (sdvAmplitude x n ℰ Φ₁ εH) z /
        sdvAmplitude x n ℰ Φ₁ εH z) b‖ ≤ M' := fun b hb => by
    have hbU := hstrip_U hb
    let L₀ : ℂ → ℂ := fun z =>
      -(1 / 2 : ℂ) * Complex.sinh ((z - Complex.I / 2) / 2) / Complex.cosh ((z - Complex.I / 2) / 2)
    have hev : (fun z => deriv (sdvAmplitude x n ℰ Φ₁ εH) z / sdvAmplitude x n ℰ Φ₁ εH z) =ᶠ[𝓝 b] L₀ := by
      refine Filter.eventually_of_mem (hU_open.mem_nhds hbU) fun z hz => ?_
      dsimp only
      rw [(h_ax_ev z hz).deriv_eq, h_ax_eq_U z hz, hlogderiv_eq z hz]
    have hL₀_d : HasDerivAt L₀ (-(1 / 4 : ℂ) / Complex.cosh ((b - Complex.I / 2) / 2) ^ 2) b := by
      have hlin : HasDerivAt (fun z : ℂ => (z - Complex.I / 2) / 2) (1 / 2 : ℂ) b := by
        simpa using ((hasDerivAt_id b).sub_const _).div_const (2 : ℂ)
      have hsh : HasDerivAt (fun z : ℂ => Complex.sinh ((z - Complex.I / 2) / 2))
          (Complex.cosh ((b - Complex.I / 2) / 2) * (1 / 2 : ℂ)) b :=
        (Complex.hasDerivAt_sinh _).comp b hlin
      have hch : HasDerivAt (fun z : ℂ => Complex.cosh ((z - Complex.I / 2) / 2))
          (Complex.sinh ((b - Complex.I / 2) / 2) * (1 / 2 : ℂ)) b :=
        (Complex.hasDerivAt_cosh _).comp b hlin
      have hdiv := (hsh.const_mul (-(1 / 2 : ℂ))).div hch (hcosh_ne b hbU)
      refine hdiv.congr_deriv ?_
      let w : ℂ := (b - Complex.I / 2) / 2
      change (-(1 / 2 : ℂ) * (Complex.cosh w * (1 / 2)) * Complex.cosh w -
          -(1 / 2 : ℂ) * Complex.sinh w * (Complex.sinh w * (1 / 2))) / Complex.cosh w ^ 2 =
        -(1 / 4 : ℂ) / Complex.cosh w ^ 2
      have hsq_eq : Complex.cosh w ^ 2 - Complex.sinh w ^ 2 = 1 := by
        simpa [w, sq] using Complex.cosh_sq_sub_sinh_sq w
      calc (-(1 / 2 : ℂ) * (Complex.cosh w * (1 / 2)) * Complex.cosh w -
            -(1 / 2 : ℂ) * Complex.sinh w * (Complex.sinh w * (1 / 2))) / Complex.cosh w ^ 2
          = (-(1 / 4 : ℂ) * (Complex.cosh w ^ 2 - Complex.sinh w ^ 2)) / Complex.cosh w ^ 2 := by ring
        _ = -(1 / 4 : ℂ) / Complex.cosh w ^ 2 := by rw [hsq_eq, mul_one]
    rw [hev.deriv_eq, hL₀_d.deriv, norm_div, norm_pow]
    have h14 : ‖-(1 / 4 : ℂ)‖ = 1 / 4 := by rw [norm_neg]; norm_num
    have hch := sdv_cosh_strip_norm_lower (hz_pi4 b hbU)
    have hch_sq : 1 / 2 ≤ ‖Complex.cosh ((b - Complex.I / 2) / 2)‖ ^ 2 := by
      have h1 : 1 / √2 ≤ Real.cosh ((b - Complex.I / 2) / 2).re / √2 :=
        div_le_div_of_nonneg_right (Real.one_le_cosh _) (Real.sqrt_nonneg _)
      have h2 : (1 / √2) ^ 2 ≤ ‖Complex.cosh ((b - Complex.I / 2) / 2)‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) (h1.trans hch) 2
      have hsq : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
      calc (1 / 2 : ℝ) = (1 / √2) ^ 2 := by rw [div_pow, one_pow, hsq]
        _ ≤ ‖Complex.cosh ((b - Complex.I / 2) / 2)‖ ^ 2 := h2
    rw [h14]
    calc (1 / 4 : ℝ) / ‖Complex.cosh ((b - Complex.I / 2) / 2)‖ ^ 2
        ≤ (1 / 4 : ℝ) / (1 / 2) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hch_sq
      _ = M' := by dsimp [M']; norm_num
  have hA₀_exp_decay : ∀ v t : ℝ, |t - 1 / 2| ≤ δ →
      ‖A₀ ((v : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 * √2 * Real.exp (-|v| / 2) := fun v t ht => by
    have hz : (((v : ℂ) + (t : ℂ) * Complex.I - Complex.I / 2) / 2).re = v / 2 := by simp
    have hmemU : (v : ℂ) + (t : ℂ) * Complex.I ∈ U := hstrip_U (by simpa [edgeStrip] using ht)
    have hlb := sdv_cosh_strip_norm_lower (hz_pi4 _ hmemU)
    rw [hz] at hlb
    have hcosh_exp : Real.exp (|v| / 2) / 2 ≤ Real.cosh (v / 2) := by
      rw [Real.cosh_eq, add_div]
      rcases le_total 0 v with hv | hv
      · rw [abs_of_nonneg hv]; linarith [Real.exp_pos (-(v / 2))]
      · rw [abs_of_nonpos hv, neg_div]; linarith [Real.exp_pos (v / 2)]
    have hexp_inv : Real.exp (|v| / 2) / (2 * √2) ≤
        ‖Complex.cosh (((v : ℂ) + (t : ℂ) * Complex.I - Complex.I / 2) / 2)‖ := by
      calc Real.exp (|v| / 2) / (2 * √2) = (Real.exp (|v| / 2) / 2) / √2 := by ring
        _ ≤ Real.cosh (v / 2) / √2 := div_le_div_of_nonneg_right hcosh_exp (Real.sqrt_nonneg _)
        _ ≤ ‖Complex.cosh (((v : ℂ) + (t : ℂ) * Complex.I - Complex.I / 2) / 2)‖ := hlb
    have hpref_norm : ‖pref‖ = 1 := by
      dsimp [pref]; rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
    dsimp [A₀]
    rw [norm_mul, hpref_norm, one_mul, norm_inv]
    calc ‖Complex.cosh (((v : ℂ) + (t : ℂ) * Complex.I - Complex.I / 2) / 2)‖⁻¹
        ≤ (Real.exp (|v| / 2) / (2 * √2))⁻¹ := inv_anti₀ (by positivity) hexp_inv
      _ = 2 * √2 * Real.exp (-|v| / 2) := by
          rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, show -(|v| / 2) = -|v| / 2 by ring]
  have h_dec : ∃ C_h a_h : ℝ, 0 ≤ C_h ∧ 0 < a_h ∧
      ∀ v t : ℝ, 1 / 2 - δ ≤ t → t ≤ 1 / 2 →
        ‖ℰ ((v : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * Φ₀ ((v : ℂ) + (t : ℂ) * Complex.I) +
            Φ₁ ((v : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C_h * Real.exp (-a_h * |v|) := by
    refine ⟨4 * √2 * Real.exp (C₃ * δ ^ 3 / 6), 1 / 2, by positivity, by norm_num,
      fun v t ht1 ht2 => ?_⟩
    have ht_abs : |t - 1 / 2| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
    have hmem_strip : (v : ℂ) + (t : ℂ) * Complex.I ∈ edgeStrip δ := by
      simpa [edgeStrip] using ht_abs
    have hnorm_ge : (1 / 4 : ℝ) ≤ ‖(v : ℂ) + (t : ℂ) * Complex.I‖ :=
      mem_edgeStrip_norm_ge_quarter hδ1 hmem_strip
    have hcpow_le : ‖((v : ℂ) + (t : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))‖ ≤ 2 := by
      rw [show -(1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real,
        show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg (norm_nonneg _),
        ← Real.sqrt_eq_rpow]
      have hsq : (1 / 2 : ℝ) ≤ √‖(v : ℂ) + (t : ℂ) * Complex.I‖ := by
        rw [show (1 / 2 : ℝ) = √(1 / 4 : ℝ) by norm_num]
        exact Real.sqrt_le_sqrt hnorm_ge
      calc (√‖(v : ℂ) + (t : ℂ) * Complex.I‖)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by positivity) hsq
        _ = 2 := by norm_num
    have hΦ_re : (Φ₀ ((v : ℂ) + (t : ℂ) * Complex.I)).re ≤ C₃ * δ ^ 3 / 6 := by
      let u : ℝ := t - 1 / 2
      have hu_abs : |u| ≤ δ := by dsimp [u]; exact ht_abs
      have hu_nonpos : u ≤ 0 := by dsimp [u]; linarith
      have ht_Tay := phiX_re_normal_taylor hΦ hδ0.le x v u hu_abs
      have heq_pt : (v : ℂ) + Complex.I * ((1 / 2 + u : ℝ) : ℂ) =
          (v : ℂ) + (t : ℂ) * Complex.I := by apply Complex.ext <;> simp [u]
      rw [heq_pt] at ht_Tay
      have ht_le := (abs_le.mp ht_Tay).2
      have hphi_eq : (phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I)).re =
          (Φ₀ ((v : ℂ) + (t : ℂ) * Complex.I)).re - 4 * Real.pi / 3 * x * u := by
        unfold phiX
        have hsub : ((v : ℂ) + (t : ℂ) * Complex.I - Complex.I / 2) =
            (v : ℂ) + (u : ℂ) * Complex.I := by apply Complex.ext <;> simp [u]
        rw [hsub]
        simp [Complex.mul_re]
        ring
      have hF_pos : 0 < edgeF v := by
        unfold edgeF
        exact div_pos (Real.arsinh_pos_iff.mpr (Real.cosh_pos _)) Real.pi_pos
      have hC₃_nn : 0 ≤ C₃ :=
        (norm_nonneg _).trans (hΦ.deriv3_bound (bX x) (bX_mem_edgeStrip hδ0.le x))
      have hFu : (4 * Real.pi / 3) * u * edgeF v ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hu_nonpos)
          hF_pos.le
      have hC_le : C₃ * |u| ^ 3 / 6 ≤ C₃ * δ ^ 3 / 6 := by gcongr
      linarith
    have hA_bd := hA₀_exp_decay v t ht_abs
    dsimp [ℰ, Φ₁, n]
    simp only [one_mul, add_zero]
    rw [norm_mul, norm_mul, Complex.norm_exp]
    calc ‖A₀ ((v : ℂ) + (t : ℂ) * Complex.I)‖ *
          ‖((v : ℂ) + (t : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))‖ *
          Real.exp (Φ₀ ((v : ℂ) + (t : ℂ) * Complex.I)).re
        ≤ (2 * √2 * Real.exp (-|v| / 2)) * 2 * Real.exp (C₃ * δ ^ 3 / 6) := by
          gcongr
      _ = 4 * √2 * Real.exp (C₃ * δ ^ 3 / 6) * Real.exp (-(1 / 2) * |v|) := by
          rw [show -(1 / 2 : ℝ) * |v| = -|v| / 2 by ring]; ring
  have h_eps_bd : ∃ C_ε : ℝ, ∀ b ∈ edgeStrip δ,
      ‖1 + εH ((sdvWave n x : ℂ) * b)‖ ≤ C_ε := by
    refine ⟨1, fun b _ => ?_⟩
    simp [εH]
  have h_edge_symm : ∀ v : ℝ,
      let b : ℂ := (v : ℂ) + Complex.I / 2
      let bm : ℂ := (-v : ℂ) + Complex.I / 2
      let h : ℂ → ℂ := fun z => ℰ z * Complex.exp ((n : ℂ) * Φ₀ z + Φ₁ z)
      h bm * H0 ((sdvWave n x : ℂ) * bm) * bm =
        starRingEnd ℂ (h b * H0 ((sdvWave n x : ℂ) * b) * b) := by
    let symΦ : ℝ → ℂ := fun t => Φ₀ ((t : ℂ) + Complex.I / 2) + Φ₀ ((-t : ℂ) + Complex.I / 2)
    have h_deriv_sym : ∀ t : ℝ, HasDerivAt symΦ 0 t := fun t => by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) + Complex.I / 2) 1 t := by
        have h := (Complex.ofRealCLM.hasDerivAt (x := t)).add_const (Complex.I / 2)
        simp only [Complex.ofRealCLM_apply, Complex.ofReal_one] at h
        exact h
      have h2 : HasDerivAt (fun s : ℝ => ((-s : ℝ) : ℂ) + Complex.I / 2) (-1) t := by
        have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).neg).add_const (Complex.I / 2)
        simp only [Complex.ofRealCLM_apply, Complex.ofReal_one] at h
        simpa [Complex.ofReal_neg] using h
      have hp1 := (hΦ.holo _ (mem_edgeStrip_edge hδ0.le t)).differentiableAt.hasDerivAt.comp t h1
      have hp2 := (hΦ.holo _ (mem_edgeStrip_edge hδ0.le (-t))).differentiableAt.hasDerivAt.comp t h2
      rw [show (deriv Φ₀ ((t : ℂ) + Complex.I / 2)) =
          -(4 * (Real.pi : ℂ) * Complex.I / 3) * (edgeF t : ℂ) from hΦ.deriv_edge t] at hp1
      rw [show (deriv Φ₀ (((-t : ℝ) : ℂ) + Complex.I / 2)) =
          -(4 * (Real.pi : ℂ) * Complex.I / 3) * (edgeF (-t) : ℂ) from hΦ.deriv_edge (-t),
        edgeF_neg t] at hp2
      have hadd : HasDerivAt (fun s : ℝ => (Φ₀ ∘ fun u : ℝ => (u : ℂ) + Complex.I / 2) s +
            (Φ₀ ∘ fun u : ℝ => ((-u : ℝ) : ℂ) + Complex.I / 2) s) (0 : ℂ) t :=
        (hp1.fun_add hp2).congr_deriv (by ring)
      exact hadd.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => by simp [symΦ, Complex.ofReal_neg])
    have h_sym_const : ∀ v : ℝ, symΦ v = 2 * Φ₀ (Complex.I / 2) := fun v => by
      have h0 : ∀ t : ℝ, deriv symΦ t = 0 := fun t => (h_deriv_sym t).deriv
      have heq := is_const_of_deriv_eq_zero
        (fun t => (h_deriv_sym t).differentiableAt) h0 v 0
      exact by simpa [symΦ, two_mul] using heq
    have hΦ₀_eq : Φ₀ (Complex.I / 2) = Complex.I * (c₀ : ℂ) := by
      have hre : (Φ₀ (Complex.I / 2)).re = 0 := by simpa using hΦ.re_edge 0
      apply Complex.ext <;> simp [c₀, hre]
    have h_epref : Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * pref =
        Complex.exp (-Complex.I * (c₀ : ℂ)) := by
      dsimp [pref]; rw [← Complex.exp_add]; congr 1; push_cast; ring
    intro v
    dsimp only
    let b : ℂ := (v : ℂ) + Complex.I / 2
    let bm : ℂ := (-v : ℂ) + Complex.I / 2
    have hk_pos : 0 < sdvWave n x := by
      have hxi : 0 < x := lt_trans (by simp [xiStar]; positivity) hx
      unfold sdvWave; positivity [Real.pi_pos]
    have hb_strip : b ∈ edgeStrip δ := mem_edgeStrip_edge hδ0.le v
    have hbm_strip : bm ∈ edgeStrip δ := by
      simpa [bm, Complex.ofReal_neg] using mem_edgeStrip_edge hδ0.le (-v)
    have h_red : ∀ w ∈ edgeStrip δ,
        (ℰ w * Complex.exp ((n : ℂ) * Φ₀ w + Φ₁ w)) *
            H0 ((sdvWave n x : ℂ) * w) * w =
          (√(2 / (Real.pi * sdvWave n x)) * Real.exp (-(sdvWave n x) / 2) : ℝ) *
            (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * A₀ w *
              Complex.exp ((n : ℂ) * phiX Φ₀ x w)) := by
      intro w hw
      have him_pos : 0 < w.im := mem_edgeStrip_im_pos hδ1 hw
      have hw_ne : w ≠ 0 := fun h => by simp [h] at him_pos
      have hmul : ((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * w))) ^ (1 / 2 : ℂ) * w =
          (√(2 / (Real.pi * sdvWave n x)) : ℂ) * w ^ (1 / 2 : ℂ) :=
        hankelZeroPrefactor_mul (sdvWave n x) hk_pos him_pos
      have hexp_phase : Complex.exp (Complex.I * ((sdvWave n x : ℂ) * w - Real.pi / 4)) =
          (Real.exp (-(sdvWave n x) / 2) : ℝ) * Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
            Complex.exp ((n : ℂ) * (Complex.I * (4 * Real.pi / 3) * (x : ℂ) * (w - Complex.I / 2))) := by
        rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
        congr 1
        unfold sdvWave
        push_cast
        have hsplit : (n : ℂ) * (Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) * (w - Complex.I / 2)) =
            (n : ℂ) * (Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) * w) -
              ((n : ℂ) * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) / 2) * (Complex.I * Complex.I) := by
          ring
        rw [hsplit, Complex.I_mul_I]
        ring
      have hcpow_id : w ^ (-(1 / 2 : ℂ)) * w ^ (1 / 2 : ℂ) = 1 := by
        rw [← Complex.cpow_add _ _ hw_ne]; norm_num
      have hexp_phi : Complex.exp ((n : ℂ) * Φ₀ w + Φ₁ w) *
            Complex.exp ((n : ℂ) * (Complex.I * (4 * Real.pi / 3) * (x : ℂ) * (w - Complex.I / 2))) =
          Complex.exp ((n : ℂ) * phiX Φ₀ x w) := by
        simp only [Φ₁, add_zero]; rw [← Complex.exp_add]; congr 1; unfold phiX; ring
      dsimp [ℰ, H0]
      calc (A₀ w * w ^ (-(1 / 2 : ℂ)) * Complex.exp ((n : ℂ) * Φ₀ w + Φ₁ w)) *
            (((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * w))) ^ (1 / 2 : ℂ) *
              Complex.exp (Complex.I * ((sdvWave n x : ℂ) * w - Real.pi / 4))) * w
          = A₀ w * w ^ (-(1 / 2 : ℂ)) *
              (((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * w))) ^ (1 / 2 : ℂ) * w) *
              Complex.exp (Complex.I * ((sdvWave n x : ℂ) * w - Real.pi / 4)) *
              Complex.exp ((n : ℂ) * Φ₀ w + Φ₁ w) := by ring
        _ = (√(2 / (Real.pi * sdvWave n x)) * Real.exp (-(sdvWave n x) / 2) : ℝ) *
              (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * A₀ w *
                (w ^ (-(1 / 2 : ℂ)) * w ^ (1 / 2 : ℂ)) *
                (Complex.exp ((n : ℂ) * Φ₀ w + Φ₁ w) *
                  Complex.exp ((n : ℂ) * (Complex.I * (4 * Real.pi / 3) * (x : ℂ) * (w - Complex.I / 2))))) := by
            rw [hmul, hexp_phase]; push_cast; ring
        _ = _ := by rw [hcpow_id, mul_one, hexp_phi]
    rw [h_red bm hbm_strip, h_red b hb_strip, map_mul, Complex.conj_ofReal]
    congr 1
    have h_phi_rel : phiX Φ₀ x bm =
        starRingEnd ℂ (phiX Φ₀ x b) + 2 * Complex.I * (c₀ : ℂ) := by
      have hre0 : (phiX Φ₀ x b).re = 0 := phiX_re_edge hΦ x v
      have hconj : starRingEnd ℂ (phiX Φ₀ x b) = -phiX Φ₀ x b := by
        apply Complex.ext <;> simp [hre0]
      have hsum : phiX Φ₀ x b + phiX Φ₀ x bm = 2 * Complex.I * (c₀ : ℂ) := by
        unfold phiX
        have hv1 : b - Complex.I / 2 = (v : ℂ) := by dsimp [b]; ring
        have hv2 : bm - Complex.I / 2 = (-v : ℂ) := by dsimp [bm]; ring
        rw [hv1, hv2]
        have hs : Φ₀ ((v : ℂ) + Complex.I / 2) + Φ₀ ((-v : ℂ) + Complex.I / 2) =
            2 * Φ₀ (Complex.I / 2) := by
          simpa [symΦ, Complex.ofReal_neg] using h_sym_const v
        calc Φ₀ b + Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) * (v : ℂ) +
              (Φ₀ bm + Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) * (-v : ℂ))
            = Φ₀ ((v : ℂ) + Complex.I / 2) + Φ₀ ((-v : ℂ) + Complex.I / 2) := by
                dsimp [b, bm]; ring
          _ = 2 * Φ₀ (Complex.I / 2) := hs
          _ = 2 * Complex.I * (c₀ : ℂ) := by rw [hΦ₀_eq]; ring
      rw [hconj]
      linear_combination hsum
    have hcosh_even_real : (Complex.cosh ((bm - Complex.I / 2) / 2))⁻¹ =
        (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) := by
      have hz1 : (bm - Complex.I / 2) / 2 = -(((v / 2 : ℝ) : ℂ)) := by
        dsimp [bm]; push_cast; ring
      rw [hz1, Complex.cosh_neg, ← Complex.ofReal_cosh, ← Complex.ofReal_inv]
    have hcosh_pos_real : (Complex.cosh ((b - Complex.I / 2) / 2))⁻¹ =
        (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) := by
      have hz1 : (b - Complex.I / 2) / 2 = ((v / 2 : ℝ) : ℂ) := by
        dsimp [b]; push_cast; ring
      rw [hz1, ← Complex.ofReal_cosh, ← Complex.ofReal_inv]
    have h_exp_conj : Complex.exp (-Complex.I * (c₀ : ℂ) +
          (starRingEnd ℂ (phiX Φ₀ x b) + 2 * Complex.I * (c₀ : ℂ))) =
        starRingEnd ℂ (Complex.exp (-Complex.I * (c₀ : ℂ) + phiX Φ₀ x b)) := by
      rw [← Complex.exp_conj]
      congr 1
      rw [map_add, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
      ring
    dsimp [A₀, n]
    simp only [one_mul]
    calc Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
          (pref * (Complex.cosh ((bm - Complex.I / 2) / 2))⁻¹) * Complex.exp (phiX Φ₀ x bm)
        = (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * pref) *
            (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) * Complex.exp (phiX Φ₀ x bm) := by
          rw [hcosh_even_real]; ring
      _ = (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) *
            Complex.exp (-Complex.I * (c₀ : ℂ) +
              (starRingEnd ℂ (phiX Φ₀ x b) + 2 * Complex.I * (c₀ : ℂ))) := by
          rw [h_epref, h_phi_rel]
          calc Complex.exp (-Complex.I * (c₀ : ℂ)) * (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) *
                Complex.exp (starRingEnd ℂ (phiX Φ₀ x b) + 2 * Complex.I * (c₀ : ℂ))
              = (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) *
                  (Complex.exp (-Complex.I * (c₀ : ℂ)) *
                    Complex.exp (starRingEnd ℂ (phiX Φ₀ x b) + 2 * Complex.I * (c₀ : ℂ))) := by ring
            _ = _ := by rw [← Complex.exp_add]
      _ = starRingEnd ℂ ((((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) *
            Complex.exp (-Complex.I * (c₀ : ℂ) + phiX Φ₀ x b)) := by
          rw [h_exp_conj, map_mul, Complex.conj_ofReal]
      _ = starRingEnd ℂ (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
            (pref * (Complex.cosh ((b - Complex.I / 2) / 2))⁻¹) * Complex.exp (phiX Φ₀ x b)) := by
          congr 1
          rw [hcosh_pos_real]
          calc (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) *
                Complex.exp (-Complex.I * (c₀ : ℂ) + phiX Φ₀ x b)
              = (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) *
                  (Complex.exp (-Complex.I * (c₀ : ℂ)) * Complex.exp (phiX Φ₀ x b)) := by
                rw [← Complex.exp_add]
            _ = Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
                  (pref * (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ)) * Complex.exp (phiX Φ₀ x b) := by
                rw [← h_epref]; ring
  exact ⟨C₃, C₄, Φ₀, ℰ, hΦ,
    ⟨hA_an, hA_ne, h_hankel, hlogderiv_bd, hlogderiv2_bd, h_dec, h_eps_bd, h_edge_symm⟩⟩

/-- Non-vacuity of `lemma_SD_V`: for every `0 < δ ≤ 1/4`, there exist `C₃, C₄, Φ₀, x, n, M, M',
ℰ, Φ₁, H0, εH` satisfying `EdgePhaseData` and `SDVHypotheses`. -/
theorem sdv_nonvacuous {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ (C₃ C₄ : ℝ) (Φ₀ : ℂ → ℂ) (x n M M' : ℝ) (ℰ Φ₁ H0 εH : ℂ → ℂ),
      xiStar < x ∧ 0 < n ∧
      EdgePhaseData δ C₃ C₄ Φ₀ ∧ SDVHypotheses Φ₀ x n δ M M' ℰ Φ₁ H0 εH := by
  obtain ⟨C₃, C₄, Φ₀, ℰ, hΦ, hS⟩ := sdv_canonical_witness hδ0 hδ1
  exact ⟨C₃, C₄, Φ₀, xiStar + 1, 1, √2 / 2, 1 / 2, ℰ, _, _, _, by linarith, zero_lt_one, hΦ, hS⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Saddle.lemma_SD_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Saddle.lemma_SD_V

/-- info: 'FormalResearch.ModularBootstrap.Upper.Saddle.sdv_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Saddle.sdv_nonvacuous

end FormalResearch.ModularBootstrap.Upper.Saddle



