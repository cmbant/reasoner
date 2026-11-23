module

public import FormalResearch.ModularBootstrap.Upper.Saddle.EdgeNormalForm
public import FormalResearch.ModularBootstrap.Upper.Saddle.GaussianMoments
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Five-Piece Contour Deformation, Schwarz Reflection, and `(SD.8)` for `SD_V'`

Source: `edge_transform_sd.tex`, Lemma `esd:lemmap` (`SD_V'`), l.213–319.

For an abstract amplitude `A` satisfying `(i)–(iii)` of Lemma `SD_V'` (`TwoSaddleAmplitude`):
* **Amplitude bounds from `(i)`**: branch-free FTC along convex segments gives
  `‖A b‖ ≤ ‖A b₀‖ * exp(M * ‖b - b₀‖)` and the order-1 local Taylor expansion
  `A(b_x + r dir) / A(b_x) = 1 + a₁ dir r + O((M² + M') r²)`.
* **Five-piece Cauchy deformation**: compactness + `isExactOn_rect` deforms `E_+` on
  `[-R, R]` onto the symmetric five-piece contour, passing `R → ∞` via `(ii)`.
* **Edge reflection**: analytic continuation of `(iii)` under `b ↦ -\bar b` shows
  `e^{-iπ/4} 𝒥_A = 2 Re (𝒥_middle^+ + 𝒥_local^+ + 𝒥_outer^+)`.
* **Middle and outer estimates `(SD.8)`**: exponentially small relative error
  `C exp(-c n m_x³)` for `n m_x³` large depending only on `δ, C₃, M, M'`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Saddle

/-! ### 1. General amplitude hypotheses `(i)–(iii)` and branch-free logarithmic bounds -/

/-- General amplitude hypotheses `(i)–(iii)` of Lemma `SD_V'` (`edge_transform_sd.tex`,
l.213–222) on `𝒩_δ = edgeStrip δ` for `0 < δ ≤ 1/4`. -/
structure TwoSaddleAmplitude (Φ₀ : ℂ → ℂ) (x n δ M M' : ℝ) (A : ℂ → ℂ) : Prop where
  /-- Holomorphy on `𝒩_δ = {b : ℂ | |Im b - 1/2| ≤ δ}`. -/
  holo : AnalyticOnNhd ℂ A (edgeStrip δ)
  /-- Non-vanishing on `𝒩_δ`. -/
  nonzero : ∀ b ∈ edgeStrip δ, A b ≠ 0
  /-- Branch-free first logarithmic derivative bound `|A'(b) / A(b)| ≤ M` on `𝒩_δ`. -/
  logDeriv_bound : ∀ b ∈ edgeStrip δ, ‖deriv A b / A b‖ ≤ M
  /-- Branch-free second logarithmic derivative bound `|(A'/A)'(b)| ≤ M'` on `𝒩_δ`. -/
  logDeriv2_bound : ∀ b ∈ edgeStrip δ, ‖deriv (fun z => deriv A z / A z) b‖ ≤ M'
  /-- Absolute integrability of `A(b) e^{n φ_x(b)}` along `E_+ = ℝ + i/2`. -/
  edge_integrable : Integrable (fun v : ℝ =>
    A ((v : ℂ) + Complex.I / 2) *
      Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2)))
  /-- Absolute integrability along lower horizontal lines `Im b = 1/2 - u₀`, `0 < u₀ ≤ δ`. -/
  lower_integrable : ∀ u₀ : ℝ, 0 < u₀ → u₀ ≤ δ →
    Integrable (fun v : ℝ =>
      A ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))))
  /-- Right vertical closing segments from `1/2 - u₀` to `1/2` vanish as `v → +∞`. -/
  vertical_right_tendsto : ∀ u₀ : ℝ, 0 < u₀ → u₀ ≤ δ →
    Tendsto (fun R : ℝ => ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
      A ((R : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x ((R : ℂ) + (t : ℂ) * Complex.I)))
      atTop (𝓝 0)
  /-- Left vertical closing segments from `1/2 - u₀` to `1/2` vanish as `v → -∞`. -/
  vertical_left_tendsto : ∀ u₀ : ℝ, 0 < u₀ → u₀ ≤ δ →
    Tendsto (fun R : ℝ => ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
      A ((-R : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x ((-R : ℂ) + (t : ℂ) * Complex.I)))
      atTop (𝓝 0)
  /-- Edge reflection `(iii)`: `ℐ_A(-\bar b) = \overline{ℐ_A(b)}` on `E_+`. -/
  edge_reflection : ∀ v : ℝ,
    Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
      A ((-v : ℂ) + Complex.I / 2) *
      Complex.exp ((n : ℂ) * phiX Φ₀ x ((-v : ℂ) + Complex.I / 2)) =
    starRingEnd ℂ (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
      A ((v : ℂ) + Complex.I / 2) *
      Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2)))

lemma TwoSaddleAmplitude.M_nonneg {Φ₀ : ℂ → ℂ} {x n δ M M' : ℝ} {A : ℂ → ℂ}
    (hA : TwoSaddleAmplitude Φ₀ x n δ M M' A) (hδ : 0 ≤ δ) : 0 ≤ M :=
  (norm_nonneg _).trans (hA.logDeriv_bound (bX x) (bX_mem_edgeStrip hδ x))

lemma TwoSaddleAmplitude.M'_nonneg {Φ₀ : ℂ → ℂ} {x n δ M M' : ℝ} {A : ℂ → ℂ}
    (hA : TwoSaddleAmplitude Φ₀ x n δ M M' A) (hδ : 0 ≤ δ) : 0 ≤ M' :=
  (norm_nonneg _).trans (hA.logDeriv2_bound (bX x) (bX_mem_edgeStrip hδ x))

private lemma segment_mem_edgeStrip {δ : ℝ} {b₀ b₁ : ℂ} (hb₀ : b₀ ∈ edgeStrip δ)
    (hb₁ : b₁ ∈ edgeStrip δ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    b₀ + (t : ℂ) * (b₁ - b₀) ∈ edgeStrip δ := by
  have h1 : (1 - t) • b₀ + t • b₁ ∈ edgeStrip δ :=
    (edgeStrip_convex δ) hb₀ hb₁ (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have heq : (1 - t) • b₀ + t • b₁ = b₀ + (t : ℂ) * (b₁ - b₀) := by
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rwa [← heq]

/-- Branch-free logarithmic FTC: for any `b₀, b₁ ∈ edgeStrip δ`,
`A b₁ = A b₀ * exp(∫ t in 0..1, (A'(γ t) / A(γ t)) * (b₁ - b₀))`. -/
lemma amplitude_eq_mul_exp_logDeriv_integral {Φ₀ : ℂ → ℂ} {x n δ M M' : ℝ} {A : ℂ → ℂ}
    (hA : TwoSaddleAmplitude Φ₀ x n δ M M' A) {b₀ b₁ : ℂ}
    (hb₀ : b₀ ∈ edgeStrip δ) (hb₁ : b₁ ∈ edgeStrip δ) :
    A b₁ = A b₀ * Complex.exp (∫ t in (0 : ℝ)..1,
      (deriv A (b₀ + (t : ℂ) * (b₁ - b₀)) / A (b₀ + (t : ℂ) * (b₁ - b₀))) * (b₁ - b₀)) := by
  let L : ℂ → ℂ := fun z => deriv A z / A z
  let γ : ℝ → ℂ := fun t => b₀ + (t : ℂ) * (b₁ - b₀)
  let γ₀ : ℝ → ℂ := fun t => b₀ + ((Set.projIcc 0 1 zero_le_one t : ℝ) : ℂ) * (b₁ - b₀)
  have hL_an : AnalyticOnNhd ℂ L (edgeStrip δ) :=
    hA.holo.deriv.div hA.holo hA.nonzero
  have hγ₀_mem : ∀ t : ℝ, γ₀ t ∈ edgeStrip δ := fun t =>
    segment_mem_edgeStrip hb₀ hb₁ (Set.projIcc 0 1 zero_le_one t).2
  have hγ₀_cont : Continuous γ₀ :=
    continuous_const.add
      ((Complex.continuous_ofReal.comp
        (continuous_subtype_val.comp (continuous_projIcc (a := (0 : ℝ)) (b := 1)))).mul
        continuous_const)
  have hL_cont_all : Continuous (fun t : ℝ => L (γ₀ t) * (b₁ - b₀)) :=
    (hL_an.continuousOn.comp_continuous hγ₀_cont hγ₀_mem).mul continuous_const
  have hγ_deriv : ∀ t : ℝ, HasDerivAt γ (b₁ - b₀) t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * (b₁ - b₀)) (b₁ - b₀) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt).mul_const (b₁ - b₀)
    exact h1.const_add b₀
  let G : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, L (γ₀ s) * (b₁ - b₀)
  have hG_deriv_all : ∀ t : ℝ, HasDerivAt G (L (γ₀ t) * (b₁ - b₀)) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hL_cont_all.intervalIntegrable _ _)
      hL_cont_all.aestronglyMeasurable.stronglyMeasurableAtFilter hL_cont_all.continuousAt
  have hG_deriv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt G (L (γ t) * (b₁ - b₀)) t := fun t ht => by
    have h := hG_deriv_all t
    have hγ_eq : γ₀ t = γ t := by dsimp [γ₀, γ]; rw [Set.projIcc_of_mem zero_le_one ht]
    rwa [hγ_eq] at h
  let Φ : ℝ → ℂ := fun t => A (γ₀ t) * Complex.exp (-G t)
  have hΦ_deriv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Φ 0 t := fun t ht => by
    have ht_icc : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    have hev : (fun s : ℝ => A (γ₀ s)) =ᶠ[𝓝 t] (fun s : ℝ => A (γ s)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      dsimp [γ₀, γ]
      rw [Set.projIcc_of_mem zero_le_one (Ioo_subset_Icc_self hs)]
    have hA_d : HasDerivAt (fun s : ℝ => A (γ₀ s)) (deriv A (γ t) * (b₁ - b₀)) t := by
      have hc := (hA.holo _ (segment_mem_edgeStrip hb₀ hb₁ ht_icc)).differentiableAt.hasDerivAt
      exact (hc.comp t (hγ_deriv t)).congr_of_eventuallyEq hev
    have hE_d : HasDerivAt (fun s : ℝ => Complex.exp (-G s))
        (Complex.exp (-G t) * (-(L (γ t) * (b₁ - b₀)))) t :=
      (hG_deriv t ht_icc).neg.cexp
    have hmul := hA_d.mul hE_d
    refine hmul.congr_deriv ?_
    have hAne : A (γ t) ≠ 0 := hA.nonzero _ (segment_mem_edgeStrip hb₀ hb₁ ht_icc)
    have hγ_eq : γ₀ t = γ t := by dsimp [γ₀, γ]; rw [Set.projIcc_of_mem zero_le_one ht_icc]
    rw [hγ_eq]
    dsimp [L]
    field_simp [hAne]
    ring
  have hΦ_cont : Continuous Φ :=
    (hA.holo.continuousOn.comp_continuous hγ₀_cont hγ₀_mem).mul
      (continuous_iff_continuousAt.mpr fun t => (hG_deriv_all t).continuousAt).neg.cexp
  have hΦ_const : Φ 1 = Φ 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hΦ_cont.continuousOn
      hΦ_deriv (by simp : IntervalIntegrable (fun _ => (0 : ℂ)) volume 0 1)
    simp only [intervalIntegral.integral_zero] at h
    exact sub_eq_zero.mp h.symm
  have hγ₀1 : γ₀ 1 = b₁ := by
    dsimp [γ₀]
    rw [Set.projIcc_of_mem zero_le_one ⟨zero_le_one, le_rfl⟩]
    simp
  have hγ₀0 : γ₀ 0 = b₀ := by
    dsimp [γ₀]
    rw [Set.projIcc_of_mem zero_le_one ⟨le_rfl, zero_le_one⟩]
    simp
  have hG1 : G 1 = ∫ s in (0 : ℝ)..1, L (γ s) * (b₁ - b₀) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le zero_le_one] at hs
    dsimp [γ₀, γ]
    rw [Set.projIcc_of_mem zero_le_one hs]
  dsimp [Φ] at hΦ_const
  rw [hγ₀1, hγ₀0] at hΦ_const
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  rw [hG0, neg_zero, Complex.exp_zero, mul_one, hG1] at hΦ_const
  calc A b₁ = (A b₁ * Complex.exp (-(∫ s in (0 : ℝ)..1, L (γ s) * (b₁ - b₀)))) *
        Complex.exp (∫ s in (0 : ℝ)..1, L (γ s) * (b₁ - b₀)) := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = A b₀ * Complex.exp (∫ s in (0 : ℝ)..1, L (γ s) * (b₁ - b₀)) := by
          rw [hΦ_const]

/-- Global amplitude growth bound from `(i)`:
`‖A b‖ ≤ ‖A b₀‖ * exp(M * ‖b - b₀‖)` for any `b₀, b ∈ edgeStrip δ`. -/
lemma amplitude_growth_le {Φ₀ : ℂ → ℂ} {x n δ M M' : ℝ} {A : ℂ → ℂ}
    (hA : TwoSaddleAmplitude Φ₀ x n δ M M' A) {b₀ b : ℂ}
    (hb₀ : b₀ ∈ edgeStrip δ) (hb : b ∈ edgeStrip δ) :
    ‖A b‖ ≤ ‖A b₀‖ * Real.exp (M * ‖b - b₀‖) := by
  have heq := amplitude_eq_mul_exp_logDeriv_integral hA hb₀ hb
  rw [heq, norm_mul, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  let I : ℂ := ∫ t in (0 : ℝ)..1,
    (deriv A (b₀ + (t : ℂ) * (b - b₀)) / A (b₀ + (t : ℂ) * (b - b₀))) * (b - b₀)
  calc I.re ≤ ‖I‖ := Complex.re_le_norm I
    _ ≤ ∫ t in (0 : ℝ)..1,
        ‖(deriv A (b₀ + (t : ℂ) * (b - b₀)) / A (b₀ + (t : ℂ) * (b - b₀))) * (b - b₀)‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ _t in (0 : ℝ)..1, M * ‖b - b₀‖ := by
        have hL_an : AnalyticOnNhd ℂ (fun z => deriv A z / A z) (edgeStrip δ) :=
          hA.holo.deriv.div hA.holo hA.nonzero
        have hcont : ContinuousOn (fun t : ℝ =>
            ‖(deriv A (b₀ + (t : ℂ) * (b - b₀)) / A (b₀ + (t : ℂ) * (b - b₀))) * (b - b₀)‖)
            (Icc 0 1) := by
          refine ContinuousOn.norm (ContinuousOn.mul ?_ continuousOn_const)
          exact hL_an.continuousOn.comp (by fun_prop : Continuous fun t : ℝ =>
            b₀ + (t : ℂ) * (b - b₀)).continuousOn fun t ht => segment_mem_edgeStrip hb₀ hb ht
        refine intervalIntegral.integral_mono_on zero_le_one
          ((hcont.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable)
          intervalIntegrable_const fun t ht => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (hA.logDeriv_bound _ (segment_mem_edgeStrip hb₀ hb ht)) (norm_nonneg _)
    _ = M * ‖b - b₀‖ := by simp

private lemma complex_exp_sub_one_sub_id_le (w : ℂ) :
    ‖Complex.exp w - 1 - w‖ ≤ Real.exp ‖w‖ * ‖w‖ ^ 2 / 2 := by
  let g₁ : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * w) - 1
  let g₀ : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * w) - 1 - (t : ℂ) * w
  have hg₁_d : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt g₁ (w * Complex.exp ((t : ℂ) * w)) t := fun t _ => by
    have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * w) w t := by
      simpa using (Complex.ofRealCLM.hasDerivAt).mul_const w
    exact (hlin.cexp.sub_const 1).congr_deriv (by ring)
  have hg₀_d : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt g₀ (w * g₁ t) t := fun t _ => by
    have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * w) w t := by
      simpa using (Complex.ofRealCLM.hasDerivAt).mul_const w
    have he := hlin.cexp
    exact ((he.sub_const 1).sub hlin).congr_deriv (by dsimp [g₁]; ring)
  have hb1 : ∀ t ∈ uIcc (0 : ℝ) 1, ‖g₁ t‖ ≤ ‖w‖ * Real.exp ‖w‖ * |t| := fun t ht => by
    rw [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at ht
    have hftc : g₁ t = ∫ s in (0 : ℝ)..t, w * Complex.exp ((s : ℂ) * w) := by
      have hsub : uIcc 0 t ⊆ uIcc 0 1 := uIcc_subset_uIcc left_mem_uIcc
        ((Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)).symm ▸ ht)
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hg₁_d s (hsub hs))
        ((by fun_prop : Continuous fun s : ℝ => w * Complex.exp ((s : ℂ) * w)).intervalIntegrable 0 t)
      simpa [g₁] using h.symm
    rw [hftc]
    have hn := intervalIntegral.norm_integral_le_integral_norm
      (f := fun s : ℝ => w * Complex.exp ((s : ℂ) * w)) (μ := volume) ht.1
    have hm : ∫ s in (0 : ℝ)..t, ‖w * Complex.exp ((s : ℂ) * w)‖ ≤
        ∫ _s in (0 : ℝ)..t, ‖w‖ * Real.exp ‖w‖ := by
      refine intervalIntegral.integral_mono_on ht.1
        ((by fun_prop : Continuous fun s : ℝ => ‖w * Complex.exp ((s : ℂ) * w)‖).intervalIntegrable 0 t)
        intervalIntegrable_const fun s hs => ?_
      rw [norm_mul, Complex.norm_exp]
      have hre : ((s : ℂ) * w).re = s * w.re := by simp
      rw [hre]
      have hle : s * w.re ≤ ‖w‖ := by
        calc s * w.re ≤ s * |w.re| := mul_le_mul_of_nonneg_left (le_abs_self _) hs.1
          _ ≤ 1 * ‖w‖ := mul_le_mul (hs.2.trans ht.2) (Complex.abs_re_le_norm w) (abs_nonneg _) zero_le_one
          _ = ‖w‖ := one_mul _
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (norm_nonneg _)
    have hc : ∫ _s in (0 : ℝ)..t, ‖w‖ * Real.exp ‖w‖ = ‖w‖ * Real.exp ‖w‖ * t := by
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      ring
    rw [abs_of_nonneg ht.1]
    exact hn.trans (hm.trans_eq hc)
  have hftc0 : g₀ 1 = ∫ t in (0 : ℝ)..1, w * g₁ t := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hg₀_d t ht)
      ((by fun_prop : Continuous fun t : ℝ => w * g₁ t).intervalIntegrable 0 1)
    simpa [g₀] using h.symm
  have hn0 : ‖g₀ 1‖ ≤ ∫ t in (0 : ℝ)..1, ‖w * g₁ t‖ := by
    rw [hftc0]
    exact intervalIntegral.norm_integral_le_integral_norm (zero_le_one : (0 : ℝ) ≤ 1)
  have hm0 : ∫ t in (0 : ℝ)..1, ‖w * g₁ t‖ ≤ ∫ t in (0 : ℝ)..1, (‖w‖ ^ 2 * Real.exp ‖w‖) * t := by
    refine intervalIntegral.integral_mono_on (zero_le_one : (0 : ℝ) ≤ 1)
      ((by fun_prop : Continuous fun t : ℝ => ‖w * g₁ t‖).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun t : ℝ => (‖w‖ ^ 2 * Real.exp ‖w‖) * t).intervalIntegrable 0 1)
      fun t ht => ?_
    rw [norm_mul]
    have ht1 := hb1 t ((Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)).symm ▸ ht)
    rw [abs_of_nonneg ht.1] at ht1
    calc ‖w‖ * ‖g₁ t‖ ≤ ‖w‖ * (‖w‖ * Real.exp ‖w‖ * t) := mul_le_mul_of_nonneg_left ht1 (norm_nonneg _)
      _ = (‖w‖ ^ 2 * Real.exp ‖w‖) * t := by ring
  have hlin : ∫ t in (0 : ℝ)..1, (‖w‖ ^ 2 * Real.exp ‖w‖) * t = Real.exp ‖w‖ * ‖w‖ ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  simpa [g₀] using hn0.trans (hm0.trans_eq hlin)

/-- Order-1 local Taylor expansion of `A(b_x + r dir) / A(b_x)` along a unit-norm direction
`dir` inside `edgeStrip δ`, with `|a₁| ≤ M` and remainder `≤ (2 M² + M' / 2) r²` for `M |r| ≤ 1`. -/
lemma amplitude_taylor_order1 {Φ₀ : ℂ → ℂ} {x n δ M M' : ℝ} {A : ℂ → ℂ}
    (hA : TwoSaddleAmplitude Φ₀ x n δ M M' A) (hδ : 0 ≤ δ) {dir : ℂ} (hdir : ‖dir‖ = 1)
    {r : ℝ} (hmem : ∀ t ∈ uIcc 0 r, bX x + (t : ℂ) * dir ∈ edgeStrip δ)
    (hMr : M * |r| ≤ 1) :
    let a₁ : ℂ := deriv A (bX x) / A (bX x)
    ‖a₁‖ ≤ M ∧
    ‖A (bX x + (r : ℂ) * dir) / A (bX x) - 1 - a₁ * dir * (r : ℂ)‖ ≤
      (2 * M ^ 2 + M' / 2) * r ^ 2 := by
  let a₁ : ℂ := deriv A (bX x) / A (bX x)
  have ha₁ : ‖a₁‖ ≤ M := hA.logDeriv_bound (bX x) (bX_mem_edgeStrip hδ x)
  refine ⟨ha₁, ?_⟩
  let b₁ : ℂ := bX x + (r : ℂ) * dir
  have hb₀ : bX x ∈ edgeStrip δ := bX_mem_edgeStrip hδ x
  have hb₁ : b₁ ∈ edgeStrip δ := hmem r right_mem_uIcc
  let L : ℂ → ℂ := fun z => deriv A z / A z
  have hL_an : AnalyticOnNhd ℂ L (edgeStrip δ) := hA.holo.deriv.div hA.holo hA.nonzero
  have hA_eq := amplitude_eq_mul_exp_logDeriv_integral hA hb₀ hb₁
  have hAx_ne : A (bX x) ≠ 0 := hA.nonzero (bX x) hb₀
  let I₁ : ℂ := ∫ s in (0 : ℝ)..1, L (bX x + (s : ℂ) * (b₁ - bX x)) * (b₁ - bX x)
  have hdiv : A b₁ / A (bX x) = Complex.exp I₁ := by
    rw [hA_eq, mul_div_cancel_left₀ _ hAx_ne]
  have hI₁_eq : I₁ = ∫ t in (0 : ℝ)..r, L (bX x + (t : ℂ) * dir) * dir := by
    dsimp [I₁, b₁]
    have hsub : bX x + (r : ℂ) * dir - bX x = (r : ℂ) * dir := by ring
    simp_rw [hsub]
    rcases eq_or_ne r 0 with rfl | hr0
    · simp
    · have hconv : ∫ s in (0 : ℝ)..1, L (bX x + ((r * s : ℝ) : ℂ) * dir) * ((r : ℂ) * dir) =
          r • ∫ s in (0 : ℝ)..1, L (bX x + ((r * s : ℝ) : ℂ) * dir) * dir := by
        rw [← intervalIntegral.integral_smul]
        refine intervalIntegral.integral_congr fun s _ => ?_
        rw [Complex.real_smul]
        ring
      have hcov : ∫ s in (0 : ℝ)..1, L (bX x + ((r * s : ℝ) : ℂ) * dir) * dir =
          r⁻¹ • ∫ t in (0 : ℝ)..r, L (bX x + (t : ℂ) * dir) * dir := by
        simpa [mul_zero, mul_one] using intervalIntegral.integral_comp_mul_left
          (fun t : ℝ => L (bX x + (t : ℂ) * dir) * dir) hr0 (a := 0) (b := 1)
      calc ∫ s in (0 : ℝ)..1, L (bX x + (s : ℂ) * ((r : ℂ) * dir)) * ((r : ℂ) * dir)
          = ∫ s in (0 : ℝ)..1, L (bX x + ((r * s : ℝ) : ℂ) * dir) * ((r : ℂ) * dir) := by
              refine intervalIntegral.integral_congr fun s _ => ?_
              push_cast
              ring_nf
        _ = r • (r⁻¹ • ∫ t in (0 : ℝ)..r, L (bX x + (t : ℂ) * dir) * dir) := by
              rw [hconv, hcov]
        _ = ∫ t in (0 : ℝ)..r, L (bX x + (t : ℂ) * dir) * dir := smul_inv_smul₀ hr0 _
  have hI₁_norm : ‖I₁‖ ≤ M * |r| := by
    rw [hI₁_eq]
    have hn := intervalIntegral.norm_integral_le_abs_integral_norm
      (f := fun t => L (bX x + (t : ℂ) * dir) * dir) (μ := volume) (a := 0) (b := r)
    have h_abs_int : |∫ t in (0 : ℝ)..r, ‖L (bX x + (t : ℂ) * dir) * dir‖| ≤ M * |r| := by
      have hle : ∀ t ∈ uIcc 0 r, ‖L (bX x + (t : ℂ) * dir) * dir‖ ≤ M := fun t ht => by
        rw [norm_mul, hdir, mul_one]
        exact hA.logDeriv_bound _ (hmem t ht)
      have hcont : ContinuousOn (fun t : ℝ => ‖L (bX x + (t : ℂ) * dir) * dir‖) (uIcc 0 r) := by
        refine ContinuousOn.norm (ContinuousOn.mul ?_ continuousOn_const)
        exact hL_an.continuousOn.comp (by fun_prop : Continuous fun t : ℝ =>
          bX x + (t : ℂ) * dir).continuousOn fun t ht => hmem t ht
      rcases le_total 0 r with hr0 | hr0
      · rw [abs_of_nonneg (intervalIntegral.integral_nonneg hr0 fun _ _ => norm_nonneg _),
          abs_of_nonneg hr0]
        have hi := intervalIntegral.integral_mono_on hr0 hcont.intervalIntegrable
          (intervalIntegrable_const (μ := volume)) fun t ht => hle t ((Set.uIcc_of_le hr0).symm ▸ ht)
        simpa [smul_eq_mul, mul_comm] using hi
      · rw [intervalIntegral.integral_symm r 0, abs_neg,
          abs_of_nonneg (intervalIntegral.integral_nonneg hr0 fun _ _ => norm_nonneg _),
          abs_of_nonpos hr0]
        have hi := intervalIntegral.integral_mono_on hr0 (hcont.mono (by rw [uIcc_comm])).intervalIntegrable
          (intervalIntegrable_const (μ := volume)) fun t ht => hle t ((Set.uIcc_of_ge hr0).symm ▸ ht)
        simpa [smul_eq_mul, mul_comm, sub_eq_add_neg] using hi
    exact hn.trans h_abs_int
  have hI₁_lin : ‖I₁ - a₁ * dir * (r : ℂ)‖ ≤ M' * r ^ 2 / 2 := by
    rw [hI₁_eq]
    have h_diff_eq : (∫ t in (0 : ℝ)..r, L (bX x + (t : ℂ) * dir) * dir) - a₁ * dir * (r : ℂ) =
        ∫ t in (0 : ℝ)..r, (L (bX x + (t : ℂ) * dir) - L (bX x)) * dir := by
      have hconst : ∫ _t in (0 : ℝ)..r, a₁ * dir = a₁ * dir * (r : ℂ) := by
        simp only [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
        ring
      have hint1 : IntervalIntegrable (fun t : ℝ => L (bX x + (t : ℂ) * dir) * dir) volume 0 r := by
        refine (ContinuousOn.mul (hL_an.continuousOn.comp (by fun_prop : Continuous fun t : ℝ =>
          bX x + (t : ℂ) * dir).continuousOn fun t ht => hmem t ht)
          continuousOn_const).intervalIntegrable
      have hint2 : IntervalIntegrable (fun _ : ℝ => a₁ * dir) volume 0 r := intervalIntegrable_const
      rw [← hconst, ← intervalIntegral.integral_sub hint1 hint2]
      refine intervalIntegral.integral_congr fun t _ => ?_
      dsimp [L, a₁]
      ring
    rw [h_diff_eq]
    have hL_diff : ∀ t ∈ uIcc 0 r, ‖L (bX x + (t : ℂ) * dir) - L (bX x)‖ ≤ M' * |t| := fun t ht => by
      have hsub : uIcc 0 t ⊆ uIcc 0 r := uIcc_subset_uIcc left_mem_uIcc ht
      have hftc : L (bX x + (t : ℂ) * dir) - L (bX x) =
          ∫ s in (0 : ℝ)..t, deriv L (bX x + (s : ℂ) * dir) * dir := by
        have hd : ∀ s ∈ uIcc 0 t,
            HasDerivAt (fun u : ℝ => L (bX x + (u : ℂ) * dir))
              (deriv L (bX x + (s : ℂ) * dir) * dir) s := fun s hs => by
          have hc := (hL_an _ (hmem s (hsub hs))).differentiableAt.hasDerivAt
          have hl : HasDerivAt (fun u : ℝ => bX x + (u : ℂ) * dir) dir s := by
            have h1 := ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const dir).const_add (bX x)
            simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at h1
            exact h1
          exact hc.comp s hl
        have hcont_d : ContinuousOn (fun s : ℝ => deriv L (bX x + (s : ℂ) * dir) * dir) (uIcc 0 t) := by
          refine ContinuousOn.mul ?_ continuousOn_const
          exact hL_an.deriv.continuousOn.comp (by fun_prop : Continuous fun s : ℝ =>
            bX x + (s : ℂ) * dir).continuousOn fun s hs => hmem s (hsub hs)
        have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont_d.intervalIntegrable
        simpa using h.symm
      rw [hftc]
      have hle : ∀ s ∈ uIcc 0 t, ‖deriv L (bX x + (s : ℂ) * dir) * dir‖ ≤ M' := fun s hs => by
        rw [norm_mul, hdir, mul_one]
        exact hA.logDeriv2_bound _ (hmem s (hsub hs))
      have hcont_n : ContinuousOn (fun s : ℝ => ‖deriv L (bX x + (s : ℂ) * dir) * dir‖) (uIcc 0 t) := by
        refine ContinuousOn.norm (ContinuousOn.mul ?_ continuousOn_const)
        exact hL_an.deriv.continuousOn.comp (by fun_prop : Continuous fun s : ℝ =>
          bX x + (s : ℂ) * dir).continuousOn fun s hs => hmem s (hsub hs)
      rcases le_total 0 t with ht0 | ht0
      · have hn := intervalIntegral.norm_integral_le_integral_norm
          (f := fun s : ℝ => deriv L (bX x + (s : ℂ) * dir) * dir) (μ := volume) ht0
        rw [abs_of_nonneg ht0]
        have hi := intervalIntegral.integral_mono_on ht0 hcont_n.intervalIntegrable
          (intervalIntegrable_const (μ := volume)) fun s hs => hle s ((Set.uIcc_of_le ht0).symm ▸ hs)
        simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hi
        exact hn.trans (hi.trans_eq (mul_comm _ _))
      · have hsym : ∫ s in (0 : ℝ)..t, deriv L (bX x + (s : ℂ) * dir) * dir =
            -∫ s in t..(0 : ℝ), deriv L (bX x + (s : ℂ) * dir) * dir :=
          intervalIntegral.integral_symm t 0
        rw [hsym, norm_neg, abs_of_nonpos ht0]
        have hn := intervalIntegral.norm_integral_le_integral_norm
          (f := fun s : ℝ => deriv L (bX x + (s : ℂ) * dir) * dir) (μ := volume) ht0
        have hi := intervalIntegral.integral_mono_on ht0 (hcont_n.mono (by rw [uIcc_comm])).intervalIntegrable
          (intervalIntegrable_const (μ := volume)) fun s hs => hle s ((Set.uIcc_of_ge ht0).symm ▸ hs)
        simp only [intervalIntegral.integral_const, zero_sub, smul_eq_mul] at hi
        exact hn.trans (hi.trans_eq (mul_comm _ _))
    have hcont : ContinuousOn (fun t : ℝ => ‖(L (bX x + (t : ℂ) * dir) - L (bX x)) * dir‖)
        (uIcc 0 r) := by
      refine ContinuousOn.norm (ContinuousOn.mul ((ContinuousOn.sub ?_ continuousOn_const)) continuousOn_const)
      exact hL_an.continuousOn.comp (by fun_prop : Continuous fun t : ℝ =>
        bX x + (t : ℂ) * dir).continuousOn fun t ht => hmem t ht
    rcases le_total 0 r with hr0 | hr0
    · have hn := intervalIntegral.norm_integral_le_integral_norm
        (f := fun t => (L (bX x + (t : ℂ) * dir) - L (bX x)) * dir) (μ := volume) hr0
      have hi := intervalIntegral.integral_mono_on hr0 hcont.intervalIntegrable
        ((by fun_prop : Continuous fun t : ℝ => M' * t).intervalIntegrable (μ := volume) 0 r) fun t ht => by
          rw [norm_mul, hdir, mul_one]
          have h1 := hL_diff t ((Set.uIcc_of_le hr0).symm ▸ ht)
          rwa [abs_of_nonneg ht.1] at h1
      have hl : ∫ t in (0 : ℝ)..r, M' * t = M' * r ^ 2 / 2 := by
        rw [intervalIntegral.integral_const_mul, integral_id]; ring
      exact hn.trans (hi.trans_eq hl)
    · have hsym : ∫ t in (0 : ℝ)..r, (L (bX x + (t : ℂ) * dir) - L (bX x)) * dir =
          -∫ t in r..(0 : ℝ), (L (bX x + (t : ℂ) * dir) - L (bX x)) * dir :=
        intervalIntegral.integral_symm r 0
      rw [hsym, norm_neg]
      have hn := intervalIntegral.norm_integral_le_integral_norm
        (f := fun t => (L (bX x + (t : ℂ) * dir) - L (bX x)) * dir) (μ := volume) hr0
      have hi := intervalIntegral.integral_mono_on hr0 (hcont.mono (by rw [uIcc_comm])).intervalIntegrable
        ((by fun_prop : Continuous fun t : ℝ => M' * (-t)).intervalIntegrable (μ := volume) r 0) fun t ht => by
          rw [norm_mul, hdir, mul_one]
          have h1 := hL_diff t ((Set.uIcc_of_ge hr0).symm ▸ ht)
          rwa [abs_of_nonpos ht.2] at h1
      have hl : ∫ t in r..0, M' * (-t) = M' * r ^ 2 / 2 := by
        have hc := intervalIntegral.integral_comp_neg (a := r) (b := 0) (fun t : ℝ => M' * t)
        simp only [neg_zero] at hc
        rw [hc, intervalIntegral.integral_const_mul, integral_id]
        ring
      exact hn.trans (hi.trans_eq hl)
  have hexp_bd : ‖Complex.exp I₁ - 1 - I₁‖ ≤ 2 * M ^ 2 * r ^ 2 := by
    have h1 := complex_exp_sub_one_sub_id_le I₁
    have h_e : Real.exp ‖I₁‖ ≤ Real.exp 1 := Real.exp_le_exp.mpr (hI₁_norm.trans hMr)
    have h_e4 : Real.exp 1 / 2 ≤ 2 := by
      have := Real.exp_one_lt_d9
      linarith
    have hM_nn := hA.M_nonneg hδ
    have hsq : ‖I₁‖ ^ 2 ≤ (M * |r|) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hI₁_norm 2
    have hsq_eq : (M * |r|) ^ 2 = M ^ 2 * r ^ 2 := by rw [mul_pow, sq_abs]
    rw [hsq_eq] at hsq
    calc ‖Complex.exp I₁ - 1 - I₁‖
        ≤ Real.exp ‖I₁‖ * ‖I₁‖ ^ 2 / 2 := h1
      _ = (Real.exp ‖I₁‖ / 2) * ‖I₁‖ ^ 2 := by ring
      _ ≤ (Real.exp 1 / 2) * (M ^ 2 * r ^ 2) :=
          mul_le_mul (div_le_div_of_nonneg_right h_e (by norm_num)) hsq (by positivity) (by positivity)
      _ ≤ 2 * (M ^ 2 * r ^ 2) :=
          mul_le_mul_of_nonneg_right h_e4 (by positivity)
      _ = 2 * M ^ 2 * r ^ 2 := by ring
  rw [hdiv]
  calc ‖Complex.exp I₁ - 1 - a₁ * dir * (r : ℂ)‖
      = ‖(Complex.exp I₁ - 1 - I₁) + (I₁ - a₁ * dir * (r : ℂ))‖ := by ring_nf
    _ ≤ ‖Complex.exp I₁ - 1 - I₁‖ + ‖I₁ - a₁ * dir * (r : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 * M ^ 2 * r ^ 2 + M' * r ^ 2 / 2 := add_le_add hexp_bd hI₁_lin
    _ = (2 * M ^ 2 + M' / 2) * r ^ 2 := by ring

/-! ### 2. Uniform contour parameter `d` and five-piece definitions -/

/-- Uniform contour scaling constant `d > 0` depending only on `δ, C₃, M, M'`. -/
noncomputable def saddleScaleD (δ C₃ M M' : ℝ) : ℝ :=
  min (1 / 2)
    (min (√2 * δ)
      (min (1 / (max C₃ 0 + 1))
        (min (2 * √2 * Real.pi / (max C₃ 0 + 1))
          (min (1 / (max M 0 + 1)) (1 / (√(max M' 0) + 1))))))

lemma saddleScaleD_pos {δ : ℝ} (C₃ M M' : ℝ) (hδ : 0 < δ) :
    0 < saddleScaleD δ C₃ M M' := by
  unfold saddleScaleD
  have hpi := Real.pi_pos
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr zero_lt_two
  positivity

lemma saddleScaleD_le_half (δ C₃ M M' : ℝ) : saddleScaleD δ C₃ M M' ≤ 1 / 2 :=
  min_le_left _ _

lemma saddleScaleD_le_sqrt2_mul_delta (δ C₃ M M' : ℝ) : saddleScaleD δ C₃ M M' ≤ √2 * δ :=
  (min_le_right _ _).trans (min_le_left _ _)

lemma saddleScaleD_mul_C3_le_one {δ C₃ M M' : ℝ} (hC₃ : 0 ≤ C₃) :
    C₃ * saddleScaleD δ C₃ M M' ≤ 1 := by
  have h1 : saddleScaleD δ C₃ M M' ≤ 1 / (max C₃ 0 + 1) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  rw [max_eq_left hC₃] at h1
  calc C₃ * saddleScaleD δ C₃ M M'
      ≤ C₃ * (1 / (C₃ + 1)) := mul_le_mul_of_nonneg_left h1 hC₃
    _ = C₃ / (C₃ + 1) := by ring
    _ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)

lemma saddleScaleD_mul_C3_le_slope_const {δ C₃ M M' : ℝ} (hC₃ : 0 ≤ C₃) :
    C₃ * saddleScaleD δ C₃ M M' ≤ 2 * √2 * Real.pi := by
  have h1 : saddleScaleD δ C₃ M M' ≤ 2 * √2 * Real.pi / (max C₃ 0 + 1) :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  rw [max_eq_left hC₃] at h1
  have hpi := Real.pi_pos
  calc C₃ * saddleScaleD δ C₃ M M'
      ≤ C₃ * (2 * √2 * Real.pi / (C₃ + 1)) := mul_le_mul_of_nonneg_left h1 hC₃
    _ = (C₃ / (C₃ + 1)) * (2 * √2 * Real.pi) := by ring
    _ ≤ 1 * (2 * √2 * Real.pi) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact (div_le_one (by linarith)).mpr (by linarith)
    _ = 2 * √2 * Real.pi := one_mul _

lemma saddleScaleD_mul_M_le_one {δ C₃ M M' : ℝ} (hM : 0 ≤ M) :
    M * saddleScaleD δ C₃ M M' ≤ 1 := by
  have h1 : saddleScaleD δ C₃ M M' ≤ 1 / (max M 0 + 1) :=
    ((((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_left _ _)
  rw [max_eq_left hM] at h1
  calc M * saddleScaleD δ C₃ M M'
      ≤ M * (1 / (M + 1)) := mul_le_mul_of_nonneg_left h1 hM
    _ = M / (M + 1) := by ring
    _ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)

lemma saddleScaleD_sq_mul_M'_le_one {δ C₃ M M' : ℝ} (hδ : 0 < δ) (hM' : 0 ≤ M') :
    M' * saddleScaleD δ C₃ M M' ^ 2 ≤ 1 := by
  have h1 : saddleScaleD δ C₃ M M' ≤ 1 / (√(max M' 0) + 1) :=
    ((((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_right _ _)
  rw [max_eq_left hM'] at h1
  have hd_nn : 0 ≤ saddleScaleD δ C₃ M M' := (saddleScaleD_pos C₃ M M' hδ).le
  have hsq : saddleScaleD δ C₃ M M' ^ 2 ≤ (1 / (√M' + 1)) ^ 2 :=
    pow_le_pow_left₀ hd_nn h1 2
  calc M' * saddleScaleD δ C₃ M M' ^ 2
      ≤ M' * (1 / (√M' + 1)) ^ 2 := mul_le_mul_of_nonneg_left hsq hM'
    _ = √M' ^ 2 / (√M' + 1) ^ 2 := by rw [Real.sq_sqrt hM', div_pow, one_pow]; ring
    _ ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith [Real.sqrt_nonneg M'])

/-- Local half-length `ℓ = d m_x` and normal offset `u₀ = ℓ / √2`. -/
noncomputable def saddleLength (δ C₃ M M' x : ℝ) : ℝ :=
  saddleScaleD δ C₃ M M' * mX x

noncomputable def saddleU₀ (δ C₃ M M' x : ℝ) : ℝ :=
  saddleLength δ C₃ M M' x / √2

lemma saddleU₀_pos {δ C₃ M M' x : ℝ} (hδ : 0 < δ) (hx : xiStar < x) :
    0 < saddleU₀ δ C₃ M M' x := by
  unfold saddleU₀ saddleLength
  have hd := saddleScaleD_pos C₃ M M' hδ
  have hm := mX_pos hx
  positivity

lemma saddleU₀_le_delta {δ C₃ M M' x : ℝ} (hδ : 0 < δ) (hx : xiStar < x) :
    saddleU₀ δ C₃ M M' x ≤ δ := by
  unfold saddleU₀ saddleLength
  have hd : saddleScaleD δ C₃ M M' ≤ √2 * δ := saddleScaleD_le_sqrt2_mul_delta δ C₃ M M'
  have hm_nn : 0 ≤ mX x := (mX_pos hx).le
  have hm1 : mX x ≤ 1 := mX_le_one x
  have hd_nn : 0 ≤ saddleScaleD δ C₃ M M' := (saddleScaleD_pos C₃ M M' hδ).le
  calc saddleScaleD δ C₃ M M' * mX x / √2
      ≤ (√2 * δ) * 1 / √2 := by gcongr
    _ = δ := by
        have hs : √2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
        field_simp [hs]

lemma saddleLength_le_sqrt2_mul_delta {δ C₃ M M' x : ℝ} (hδ : 0 < δ) (hx : xiStar < x) :
    saddleLength δ C₃ M M' x ≤ √2 * δ := by
  have h1 := saddleU₀_le_delta (δ := δ) (C₃ := C₃) (M := M) (M' := M') (x := x) hδ hx
  unfold saddleU₀ at h1
  rwa [div_le_iff₀ (Real.sqrt_pos.mpr zero_lt_two), mul_comm] at h1

lemma saddleU₀_lt_edgeV {δ C₃ M M' x : ℝ} (hδ : 0 < δ) (hx : xiStar < x) :
    saddleU₀ δ C₃ M M' x < edgeV x := by
  unfold saddleU₀ saddleLength
  have hd : saddleScaleD δ C₃ M M' ≤ 1 / 2 := saddleScaleD_le_half δ C₃ M M'
  have hm_nn : 0 ≤ mX x := (mX_pos hx).le
  have hm_v : mX x ≤ edgeV x := mX_le_edgeV x
  have hv_pos : 0 < edgeV x := edgeV_pos hx
  have hs : 1 ≤ √2 := (Real.lt_sqrt_of_sq_lt (by norm_num)).le
  have h1 : saddleScaleD δ C₃ M M' * mX x / √2 ≤ edgeV x / 2 := by
    calc saddleScaleD δ C₃ M M' * mX x / √2
        ≤ saddleScaleD δ C₃ M M' * mX x / 1 :=
          div_le_div_of_nonneg_left
            (mul_nonneg (saddleScaleD_pos C₃ M M' hδ).le hm_nn) zero_lt_one hs
      _ = saddleScaleD δ C₃ M M' * mX x := div_one _
      _ ≤ (1 / 2) * edgeV x := mul_le_mul hd hm_v hm_nn (by norm_num)
      _ = edgeV x / 2 := by ring
  exact lt_of_le_of_lt h1 (half_lt_self hv_pos)

/-- Integrand `ℐ_A(b) = e^{-iπ/4} A(b) e^{n φ_x(b)}` of Lemma `SD_V'`. -/
noncomputable def saddleIntegrand (Φ₀ : ℂ → ℂ) (x n : ℝ) (A : ℂ → ℂ) (b : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * A b *
    Complex.exp ((n : ℂ) * phiX Φ₀ x b)

/-- Full edge integral `e^{-iπ/4} 𝒥_A = ∫_{E_+} ℐ_A(b) db`. -/
noncomputable def edgeIntegral (Φ₀ : ℂ → ℂ) (x n : ℝ) (A : ℂ → ℂ) : ℂ :=
  ∫ v : ℝ, saddleIntegrand Φ₀ x n A ((v : ℂ) + Complex.I / 2)

/-- Positive middle contour piece `∫₀^{v_x - u₀} ℐ_A(v + i(1/2 + u₀)) dv`. -/
noncomputable def middlePosIntegral (Φ₀ : ℂ → ℂ) (x n δ C₃ M M' : ℝ) (A : ℂ → ℂ) : ℂ :=
  ∫ v in (0 : ℝ)..(edgeV x - saddleU₀ δ C₃ M M' x),
    saddleIntegrand Φ₀ x n A ((v : ℂ) + Complex.I * ((1 / 2 + saddleU₀ δ C₃ M M' x : ℝ) : ℂ))

/-- Positive local steepest-descent piece `∫_{-ℓ}^{ℓ} ℐ_A(b_x + r e^{-iπ/4}) e^{-iπ/4} dr`. -/
noncomputable def localPosIntegral (Φ₀ : ℂ → ℂ) (x n δ C₃ M M' : ℝ) (A : ℂ → ℂ) : ℂ :=
  ∫ r in (-saddleLength δ C₃ M M' x)..(saddleLength δ C₃ M M' x),
    saddleIntegrand Φ₀ x n A
      (bX x + (r : ℂ) * Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))) *
      Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))

/-- Positive outer horizontal ray `∫_{v_x + u₀}^∞ ℐ_A(v + i(1/2 - u₀)) dv`. -/
noncomputable def outerPosIntegral (Φ₀ : ℂ → ℂ) (x n δ C₃ M M' : ℝ) (A : ℂ → ℂ) : ℂ :=
  ∫ v in Ioi (edgeV x + saddleU₀ δ C₃ M M' x),
    saddleIntegrand Φ₀ x n A ((v : ℂ) + Complex.I * ((1 / 2 - saddleU₀ δ C₃ M M' x : ℝ) : ℂ))

/-! ### 3. Cauchy deformation onto the symmetric five-piece contour -/

private lemma saddleIntegrand_analyticOnNhd {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ}
    (hΦ : EdgePhaseData δ C₃ C₄ Φ₀) {x n : ℝ} {M M' : ℝ} {A : ℂ → ℂ}
    (hA : TwoSaddleAmplitude Φ₀ x n δ M M' A) :
    AnalyticOnNhd ℂ (saddleIntegrand Φ₀ x n A) (edgeStrip δ) := fun b hb =>
  (analyticAt_const.mul (hA.holo b hb)).mul
    ((analyticAt_const.mul (phiX_analyticOnNhd hΦ x b hb)).cexp)

private lemma abs_sub_clamp_lt {lo hi t h : ℝ} (hlo : lo ≤ hi) (hh : 0 < h)
    (ht1 : lo - h < t) (ht2 : t < hi + h) :
    |t - min hi (max lo t)| < h := by
  rcases lt_or_ge t lo with htl | htl
  · rw [max_eq_left htl.le, min_eq_right hlo, abs_of_neg (sub_neg.mpr htl)]
    linarith
  · rcases le_or_gt t hi with hth | hth
    · rw [max_eq_right htl, min_eq_right hth, sub_self, abs_zero]
      exact hh
    · rw [max_eq_right htl, min_eq_left hth.le, abs_of_pos (sub_pos.mpr hth)]
      linarith

private lemma exists_rect_primitive_edgeStrip {f : ℂ → ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : AnalyticOnNhd ℂ f (edgeStrip δ)) {R : ℝ} (hR : 0 < R) :
    ∃ (U : Set ℂ) (P : ℂ → ℂ),
      IsOpen U ∧
      {z : ℂ | |z.re| ≤ R ∧ |z.im - 1 / 2| ≤ δ} ⊆ U ∧
      ContinuousOn f U ∧
      (∀ z ∈ U, HasDerivAt P (f z) z) := by
  let K : Set ℂ := {z : ℂ | |z.re| ≤ R ∧ |z.im - 1 / 2| ≤ δ}
  have hK_compact : IsCompact K := by
    have hsub : K ⊆ Metric.closedBall (0 : ℂ) (R + (δ + 1 / 2) + 1) := fun z hz => by
      rw [mem_closedBall_zero_iff]
      have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      have h2 : |z.im| ≤ δ + 1 / 2 := by
        have := abs_add_le (z.im - 1 / 2) (1 / 2 : ℝ)
        simp only [sub_add_cancel] at this
        linarith [hz.2, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith [hz.1]
    have hcl : IsClosed K :=
      (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
        (isClosed_le (continuous_abs.comp (Complex.continuous_im.sub continuous_const))
          continuous_const)
    exact (isCompact_closedBall (0 : ℂ) (R + (δ + 1 / 2) + 1)).of_isClosed_subset hcl hsub
  let W : Set ℂ := {z : ℂ | AnalyticAt ℂ f z}
  have hW_open : IsOpen W := isOpen_analyticAt ℂ f
  have hKW : K ⊆ W := fun z hz => hf z hz.2
  obtain ⟨ε, hε_pos, hε_thick⟩ := hK_compact.exists_thickening_subset_open hW_open hKW
  let a : ℝ := -R - ε / 2
  let b : ℝ := R + ε / 2
  let c : ℝ := 1 / 2 - δ - ε / 2
  let d : ℝ := 1 / 2 + δ + ε / 2
  let U : Set ℂ := {z : ℂ | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}
  have hU_open : IsOpen U := by
    have h1 : IsOpen {z : ℂ | a < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : IsOpen {z : ℂ | z.re < b} := isOpen_lt Complex.continuous_re continuous_const
    have h3 : IsOpen {z : ℂ | c < z.im} := isOpen_lt continuous_const Complex.continuous_im
    have h4 : IsOpen {z : ℂ | z.im < d} := isOpen_lt Complex.continuous_im continuous_const
    exact h1.inter (h2.inter (h3.inter h4))
  have hK_U : K ⊆ U := fun z hz => by
    have hzr : |z.re| ≤ R := hz.1
    have hzi : |z.im - 1 / 2| ≤ δ := hz.2
    rw [abs_le] at hzr hzi
    dsimp only [U, a, b, c, d]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hU_W : U ⊆ W := fun z hz => by
    apply hε_thick
    rw [Metric.mem_thickening_iff]
    let wre : ℝ := min R (max (-R) z.re)
    let wim : ℝ := min (1 / 2 + δ) (max (1 / 2 - δ) z.im)
    let w : ℂ := (wre : ℂ) + (wim : ℂ) * Complex.I
    refine ⟨w, And.intro ?_ ?_, ?_⟩
    · have hwre : w.re = wre := by simp [w]
      rw [hwre, abs_le]
      exact ⟨le_min (by linarith) (le_max_left _ _), min_le_left _ _⟩
    · have hwim : w.im = wim := by simp [w]
      rw [hwim, abs_le]
      exact ⟨by linarith [le_min (by linarith : 1 / 2 - δ ≤ 1 / 2 + δ) (le_max_left (1 / 2 - δ) z.im)],
        by linarith [min_le_left (1 / 2 + δ) (max (1 / 2 - δ) z.im)]⟩
    · rw [dist_eq_norm]
      have hre_d : |z.re - w.re| < ε / 2 := by
        have hwre : w.re = wre := by simp [w]
        rw [hwre]
        exact abs_sub_clamp_lt (by linarith) (half_pos hε_pos) hz.1 hz.2.1
      have him_d : |z.im - w.im| < ε / 2 := by
        have hwim : w.im = wim := by simp [w]
        rw [hwim]
        exact abs_sub_clamp_lt (by linarith) (half_pos hε_pos) hz.2.2.1 hz.2.2.2
      calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = |z.re - w.re| + |z.im - w.im| := by simp
        _ < ε / 2 + ε / 2 := add_lt_add hre_d him_d
        _ = ε := add_halves ε
  have hf_diff : DifferentiableOn ℂ f U := fun z hz => (hU_W hz).differentiableAt.differentiableWithinAt
  obtain ⟨P, hP⟩ := isExactOn_rect (a := a) (b := b) (c := c) (d := d)
    (by dsimp [a, b]; linarith) (by dsimp [c, d]; linarith) hf_diff
  exact ⟨U, P, hU_open, hK_U, hf_diff.continuousOn, hP⟩

private lemma affine_segment_integral_eq_sub {U : Set ℂ} {f P : ℂ → ℂ}
    (hf_cont : ContinuousOn f U) (hP : ∀ z ∈ U, HasDerivAt P (f z) z)
    {z₀ dir : ℂ} {a b : ℝ} (hab : a ≤ b)
    (hmem : ∀ t ∈ Icc a b, z₀ + (t : ℂ) * dir ∈ U) :
    ∫ t in a..b, f (z₀ + (t : ℂ) * dir) * dir = P (z₀ + (b : ℂ) * dir) - P (z₀ + (a : ℂ) * dir) := by
  let γ : ℝ → ℂ := fun t => z₀ + (t : ℂ) * dir
  have hγ_cont : Continuous γ := by fun_prop
  have hγ_d : ∀ t : ℝ, HasDerivAt γ dir t := fun t => by
    have h1 := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const dir).const_add z₀
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at h1
    exact h1
  have hP_cont : ContinuousOn (fun t => P (γ t)) (Icc a b) := fun t ht =>
    ((hP _ (hmem t ht)).continuousAt.comp_of_eq hγ_cont.continuousAt rfl).continuousWithinAt
  have hP_d : ∀ t ∈ Ioo a b, HasDerivAt (fun s => P (γ s)) (f (γ t) * dir) t := fun t ht =>
    (hP _ (hmem t (Ioo_subset_Icc_self ht))).comp t (hγ_d t)
  have hint : IntervalIntegrable (fun t => f (γ t) * dir) volume a b := by
    have hcont : ContinuousOn (fun t => f (γ t) * dir) (Icc a b) :=
      (hf_cont.comp hγ_cont.continuousOn hmem).mul continuousOn_const
    exact (hcont.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hP_cont hP_d hint

private lemma exp_I_pi_div_four_eq :
    Complex.exp (Complex.I * (Real.pi / 4 : ℂ)) =
      ((√2 / 2 : ℝ) : ℂ) + ((√2 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [show Complex.I * (Real.pi / 4 : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I, Real.cos_pi_div_four, Real.sin_pi_div_four]

private lemma exp_neg_I_pi_div_four_eq :
    Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) =
      ((√2 / 2 : ℝ) : ℂ) - ((√2 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [show -Complex.I * (Real.pi / 4 : ℂ) = ((-Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I, show -Real.pi / 4 = -(Real.pi / 4) by ring,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  ring

/-- Finite-`R` Cauchy contour equality between `E_+ ∩ [-R, R]` and the deformed 7-piece contour. -/
private lemma finite_five_piece_contour_eq {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ}
    (hΦ : EdgePhaseData δ C₃ C₄ Φ₀) {x n M M' : ℝ} (hδ : 0 < δ) (hx : xiStar < x)
    {A : ℂ → ℂ} (hA : TwoSaddleAmplitude Φ₀ x n δ M M' A) {R : ℝ}
    (hR : edgeV x + saddleU₀ δ C₃ M M' x + 1 ≤ R) :
    let u₀ := saddleU₀ δ C₃ M M' x
    let ℓ := saddleLength δ C₃ M M' x
    let f := saddleIntegrand Φ₀ x n A
    let dirR := Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))
    let dirL := Complex.exp (Complex.I * (Real.pi / 4 : ℂ))
    (∫ v in (-R)..R, f ((v : ℂ) + Complex.I / 2)) =
      -(Complex.I * ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ), f ((-R : ℂ) + (t : ℂ) * Complex.I)) +
      (∫ v in (-R)..(-(edgeV x + u₀)), f ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))) +
      (∫ r in (-ℓ)..ℓ, f ((-(edgeV x : ℂ) + Complex.I / 2) + (r : ℂ) * dirL) * dirL) +
      (∫ v in (-(edgeV x - u₀))..(edgeV x - u₀), f ((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ))) +
      (∫ r in (-ℓ)..ℓ, f (bX x + (r : ℂ) * dirR) * dirR) +
      (∫ v in (edgeV x + u₀)..R, f ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))) +
      (Complex.I * ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ), f ((R : ℂ) + (t : ℂ) * Complex.I)) := by
  intro u₀ ℓ f dirR dirL
  have hu₀_pos : 0 < u₀ := saddleU₀_pos hδ hx
  have hu₀_le : u₀ ≤ δ := saddleU₀_le_delta hδ hx
  have hu₀_lt_vx : u₀ < edgeV x := saddleU₀_lt_edgeV hδ hx
  have hvx_pos : 0 < edgeV x := edgeV_pos hx
  have hℓ_nn : 0 ≤ ℓ := by dsimp [ℓ, saddleLength]; exact mul_nonneg (saddleScaleD_pos C₃ M M' hδ).le (mX_pos hx).le
  have hR_pos : 0 < R := by linarith
  obtain ⟨U, P, _, hKU, hf_cont, hP⟩ :=
    exists_rect_primitive_edgeStrip hδ.le (saddleIntegrand_analyticOnNhd hΦ hA) hR_pos
  have hu_box : ∀ {z : ℂ}, |z.re| ≤ R → |z.im - 1 / 2| ≤ u₀ → z ∈ U := fun hre him =>
    hKU ⟨hre, him.trans hu₀_le⟩
  -- Edge integral
  have h_edge : ∫ v in (-R)..R, f ((v : ℂ) + Complex.I / 2) =
      P ((R : ℂ) + Complex.I / 2) - P ((-R : ℂ) + Complex.I / 2) := by
    have h := affine_segment_integral_eq_sub hf_cont hP (z₀ := Complex.I / 2) (dir := 1)
      (a := -R) (b := R) (by linarith) fun t ht => hu_box (by
        simp [Complex.add_re, abs_le, ht.1, ht.2]) (by simp [hu₀_pos.le])
    rw [show (∫ v in (-R)..R, f ((v : ℂ) + Complex.I / 2)) =
        ∫ t in (-R)..R, f (Complex.I / 2 + (t : ℂ) * 1) * 1 from
        intervalIntegral.integral_congr fun t _ => by rw [mul_one]; congr 1; ring, h]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  -- Vertical left
  have h_vL : Complex.I * ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ), f ((-R : ℂ) + (t : ℂ) * Complex.I) =
      P ((-R : ℂ) + Complex.I / 2) - P ((-R : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) := by
    have h := affine_segment_integral_eq_sub hf_cont hP (z₀ := (-R : ℂ)) (dir := Complex.I)
      (a := 1 / 2 - u₀) (b := 1 / 2) (by linarith) fun t ht => hu_box (by
        simp [abs_of_nonneg hR_pos.le]) (by
        simp [abs_le]; constructor <;> linarith [ht.1, ht.2])
    have hcomm : ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ), f ((-R : ℂ) + (t : ℂ) * Complex.I) * Complex.I =
        Complex.I * ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ), f ((-R : ℂ) + (t : ℂ) * Complex.I) := by
      rw [intervalIntegral.integral_mul_const, mul_comm]
    rw [← hcomm, h]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  -- Vertical right
  have h_vR : Complex.I * ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ), f ((R : ℂ) + (t : ℂ) * Complex.I) =
      P ((R : ℂ) + Complex.I / 2) - P ((R : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) := by
    have h := affine_segment_integral_eq_sub hf_cont hP (z₀ := (R : ℂ)) (dir := Complex.I)
      (a := 1 / 2 - u₀) (b := 1 / 2) (by linarith) fun t ht => hu_box (by
        simp [abs_of_nonneg hR_pos.le]) (by
        simp [abs_le]; constructor <;> linarith [ht.1, ht.2])
    have hcomm : ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ), f ((R : ℂ) + (t : ℂ) * Complex.I) * Complex.I =
        Complex.I * ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ), f ((R : ℂ) + (t : ℂ) * Complex.I) := by
      rw [intervalIntegral.integral_mul_const, mul_comm]
    rw [← hcomm, h]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  -- Outer left
  have h_oL : ∫ v in (-R)..(-(edgeV x + u₀)), f ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) =
      P ((-(edgeV x + u₀) : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) -
        P ((-R : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) := by
    have h := affine_segment_integral_eq_sub hf_cont hP
      (z₀ := Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) (dir := 1)
      (a := -R) (b := -(edgeV x + u₀)) (by linarith) fun t ht => hu_box (by
        simp [abs_le]; constructor <;> linarith [ht.1, ht.2]) (by
        simp [abs_of_nonneg hu₀_pos.le])
    rw [show (∫ v in (-R)..(-(edgeV x + u₀)), f ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))) =
        ∫ t in (-R)..(-(edgeV x + u₀)), f (Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ) + (t : ℂ) * 1) * 1 from
        intervalIntegral.integral_congr fun t _ => by rw [mul_one]; congr 1; ring, h]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  -- Outer right
  have h_oR : ∫ v in (edgeV x + u₀)..R, f ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) =
      P ((R : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) -
        P (((edgeV x + u₀ : ℝ) : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) := by
    have h := affine_segment_integral_eq_sub hf_cont hP
      (z₀ := Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) (dir := 1)
      (a := edgeV x + u₀) (b := R) (by linarith) fun t ht => hu_box (by
        simp [abs_le]; constructor <;> linarith [ht.1, ht.2]) (by
        simp [abs_of_nonneg hu₀_pos.le])
    rw [show (∫ v in (edgeV x + u₀)..R, f ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))) =
        ∫ t in (edgeV x + u₀)..R, f (Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ) + (t : ℂ) * 1) * 1 from
        intervalIntegral.integral_congr fun t _ => by rw [mul_one]; congr 1; ring, h]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  -- Middle
  have h_mid : ∫ v in (-(edgeV x - u₀))..(edgeV x - u₀), f ((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)) =
      P (((edgeV x - u₀ : ℝ) : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)) -
        P ((-(edgeV x - u₀) : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)) := by
    have h := affine_segment_integral_eq_sub hf_cont hP
      (z₀ := Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)) (dir := 1)
      (a := -(edgeV x - u₀)) (b := edgeV x - u₀) (by linarith) fun t ht => hu_box (by
        simp [abs_le]; constructor <;> linarith [ht.1, ht.2]) (by
        simp [abs_of_nonneg hu₀_pos.le])
    rw [show (∫ v in (-(edgeV x - u₀))..(edgeV x - u₀), f ((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ))) =
        ∫ t in (-(edgeV x - u₀))..(edgeV x - u₀), f (Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ) + (t : ℂ) * 1) * 1 from
        intervalIntegral.integral_congr fun t _ => by rw [mul_one]; congr 1; ring, h]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  -- Endpoint identities for local lines
  have h_u0_s2 : ℓ * (√2 / 2) = u₀ := by
    dsimp [u₀, saddleU₀, ℓ]
    have hs : √2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
    have hsq : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
    field_simp [hs]
    rw [hsq]
  have hdirL_re : dirL.re = √2 / 2 := by
    dsimp [dirL]; rw [exp_I_pi_div_four_eq]; simp
  have hdirL_im : dirL.im = √2 / 2 := by
    dsimp [dirL]; rw [exp_I_pi_div_four_eq]; simp
  have hdirR_re : dirR.re = √2 / 2 := by
    dsimp [dirR]; rw [exp_neg_I_pi_div_four_eq]; simp
  have hdirR_im : dirR.im = -(√2 / 2) := by
    dsimp [dirR]; rw [exp_neg_I_pi_div_four_eq]; simp
  have h_inv_sqrt2_pos : 0 < √2 / 2 := by positivity
  have hL_neg : (-(edgeV x : ℂ) + Complex.I / 2) + ((-ℓ : ℝ) : ℂ) * dirL =
      (-(edgeV x + u₀) : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hdirL_re]; linarith [h_u0_s2]
    · simp [hdirL_im]; linarith [h_u0_s2]
  have hL_pos : (-(edgeV x : ℂ) + Complex.I / 2) + (ℓ : ℂ) * dirL =
      (-(edgeV x - u₀) : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hdirL_re]; linarith [h_u0_s2]
    · simp [hdirL_im]; linarith [h_u0_s2]
  have hR_neg : bX x + ((-ℓ : ℝ) : ℂ) * dirR =
      (((edgeV x - u₀ : ℝ) : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)) := by
    apply Complex.ext
    · dsimp [bX]; simp [hdirR_re]; linarith [h_u0_s2]
    · dsimp [bX]; simp [hdirR_im]; linarith [h_u0_s2]
  have hR_pos : bX x + (ℓ : ℂ) * dirR =
      (((edgeV x + u₀ : ℝ) : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) := by
    apply Complex.ext
    · dsimp [bX]; simp [hdirR_re]; linarith [h_u0_s2]
    · dsimp [bX]; simp [hdirR_im]; linarith [h_u0_s2]
  -- Local left
  have h_locL : ∫ r in (-ℓ)..ℓ, f ((-(edgeV x : ℂ) + Complex.I / 2) + (r : ℂ) * dirL) * dirL =
      P ((-(edgeV x - u₀) : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)) -
        P ((-(edgeV x + u₀) : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) := by
    have h := affine_segment_integral_eq_sub hf_cont hP
      (z₀ := -(edgeV x : ℂ) + Complex.I / 2) (dir := dirL)
      (a := -ℓ) (b := ℓ) (by linarith) fun t ht => hu_box (by
        have hre : ((-(edgeV x : ℂ) + Complex.I / 2) + (t : ℂ) * dirL).re =
            -edgeV x + t * (√2 / 2) := by
          simp [hdirL_re]
        have h_t_bd : |t * (√2 / 2)| ≤ u₀ := by
          rw [abs_mul, abs_of_pos h_inv_sqrt2_pos]
          calc |t| * (√2 / 2) ≤ ℓ * (√2 / 2) := mul_le_mul_of_nonneg_right (abs_le.mpr ht) h_inv_sqrt2_pos.le
            _ = u₀ := h_u0_s2
        rw [hre, abs_le]
        rw [abs_le] at h_t_bd
        constructor <;> linarith [h_t_bd.1, h_t_bd.2]) (by
        have him : ((-(edgeV x : ℂ) + Complex.I / 2) + (t : ℂ) * dirL).im - 1 / 2 = t * (√2 / 2) := by
          simp [hdirL_im]
        rw [him, abs_mul, abs_of_pos h_inv_sqrt2_pos]
        calc |t| * (√2 / 2) ≤ ℓ * (√2 / 2) := mul_le_mul_of_nonneg_right (abs_le.mpr ht) h_inv_sqrt2_pos.le
          _ = u₀ := h_u0_s2)
    rw [h, hL_pos, hL_neg]
  -- Local right
  have h_locR : ∫ r in (-ℓ)..ℓ, f (bX x + (r : ℂ) * dirR) * dirR =
      P (((edgeV x + u₀ : ℝ) : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) -
        P (((edgeV x - u₀ : ℝ) : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)) := by
    have h := affine_segment_integral_eq_sub hf_cont hP
      (z₀ := bX x) (dir := dirR) (a := -ℓ) (b := ℓ) (by linarith) fun t ht => hu_box (by
        have hre : (bX x + (t : ℂ) * dirR).re = edgeV x + t * (√2 / 2) := by
          dsimp [bX]; simp [hdirR_re]
        have h_t_bd : |t * (√2 / 2)| ≤ u₀ := by
          rw [abs_mul, abs_of_pos h_inv_sqrt2_pos]
          calc |t| * (√2 / 2) ≤ ℓ * (√2 / 2) := mul_le_mul_of_nonneg_right (abs_le.mpr ht) h_inv_sqrt2_pos.le
            _ = u₀ := h_u0_s2
        rw [hre, abs_le]
        rw [abs_le] at h_t_bd
        constructor <;> linarith [h_t_bd.1, h_t_bd.2]) (by
        have him : (bX x + (t : ℂ) * dirR).im - 1 / 2 = -(t * (√2 / 2)) := by
          dsimp [bX]; simp [hdirR_im]
        rw [him, abs_neg, abs_mul, abs_of_pos h_inv_sqrt2_pos]
        calc |t| * (√2 / 2) ≤ ℓ * (√2 / 2) := mul_le_mul_of_nonneg_right (abs_le.mpr ht) h_inv_sqrt2_pos.le
          _ = u₀ := h_u0_s2)
    rw [h, hR_pos, hR_neg]
  rw [h_edge, h_vL, h_oL, h_locL, h_mid, h_locR, h_oR, h_vR]
  ring

/-! ### 4. Schwarz reflection extension and `e^{-iπ/4} 𝒥_A = 2 Re(...)` -/

private lemma saddleIntegrand_reflect {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ}
    (hΦ : EdgePhaseData δ C₃ C₄ Φ₀) {x n M M' : ℝ} (hδ : 0 < δ)
    {A : ℂ → ℂ} (hA : TwoSaddleAmplitude Φ₀ x n δ M M' A) :
    ∀ b ∈ edgeStrip δ,
      saddleIntegrand Φ₀ x n A (-starRingEnd ℂ b) =
        starRingEnd ℂ (saddleIntegrand Φ₀ x n A b) := by
  let f := saddleIntegrand Φ₀ x n A
  let U : Set ℂ := {z : ℂ | |z.im - 1 / 2| < δ}
  have hU_open : IsOpen U :=
    isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const
  have hU_conv : Convex ℝ U := by
    intro a ha b hb s t hs ht hst
    change |((s • a + t • b : ℂ).im) - 1 / 2| < δ
    have him : (s • a + t • b : ℂ).im - 1 / 2 = s * (a.im - 1 / 2) + t * (b.im - 1 / 2) := by
      simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      calc s * a.im + t * b.im - 1 / 2 = s * a.im + t * b.im - (s + t) * (1 / 2) := by rw [hst, one_mul]
        _ = s * (a.im - 1 / 2) + t * (b.im - 1 / 2) := by ring
    rw [him]
    calc |s * (a.im - 1 / 2) + t * (b.im - 1 / 2)|
        ≤ |s * (a.im - 1 / 2)| + |t * (b.im - 1 / 2)| := abs_add_le _ _
      _ = s * |a.im - 1 / 2| + t * |b.im - 1 / 2| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ < s * δ + t * δ := by
          rcases eq_or_lt_of_le hs with rfl | hs'
          · simp only [zero_mul, zero_add] at hst ⊢
            subst hst
            rw [one_mul, one_mul]
            exact hb
          · have h1 : s * |a.im - 1 / 2| < s * δ := mul_lt_mul_of_pos_left ha hs'
            have h2 : t * |b.im - 1 / 2| ≤ t * δ := mul_le_mul_of_nonneg_left (le_of_lt hb) ht
            linarith
      _ = δ := by rw [← add_mul, hst, one_mul]
  have hU_sub : U ⊆ edgeStrip δ := fun z (hz : |z.im - 1 / 2| < δ) => le_of_lt hz
  have hf_an : AnalyticOnNhd ℂ f U := (saddleIntegrand_analyticOnNhd hΦ hA).mono hU_sub
  let g : ℂ → ℂ := fun b => starRingEnd ℂ (f (-starRingEnd ℂ b))
  have hg_an : AnalyticOnNhd ℂ g U := by
    have hg_diff : DifferentiableOn ℂ g U := fun b hb => by
      have hb_flip : starRingEnd ℂ b ∈ {w : ℂ | |w.im + 1 / 2| < δ} := by
        change |(starRingEnd ℂ b).im + 1 / 2| < δ
        rw [Complex.conj_im]
        have : |-b.im + 1 / 2| = |b.im - 1 / 2| := by
          rw [← abs_neg]; congr 1; ring
        rw [this]
        exact hb
      let f_neg : ℂ → ℂ := fun w => f (-w)
      have hf_neg_diff : DifferentiableAt ℂ f_neg (starRingEnd ℂ b) := by
        have h_in_U : -starRingEnd ℂ b ∈ U := by
          change |(-starRingEnd ℂ b).im - 1 / 2| < δ
          have him : (-starRingEnd ℂ b).im = b.im := by simp
          rw [him]
          exact hb
        have hc := (hf_an _ h_in_U).differentiableAt
        exact hc.comp (starRingEnd ℂ b) (differentiableAt_id.neg)
      have hconj := hf_neg_diff.conj_conj
      rw [Complex.conj_conj] at hconj
      exact hconj.differentiableWithinAt
    exact hg_diff.analyticOnNhd hU_open
  have hI2 : Complex.I / 2 ∈ U := by
    change |(Complex.I / 2).im - 1 / 2| < δ
    simpa using hδ
  have hfreq : ∃ᶠ u in 𝓝[≠] (Complex.I / 2), f u = g u := by
    rw [Filter.frequently_iff]
    intro S hS
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hS
    obtain ⟨V, hV, hVS⟩ := hS
    obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.mem_nhds_iff.mp hV
    let v : ℝ := min (ε / 2) 1
    have hv_pos : 0 < v := lt_min (half_pos hε_pos) zero_lt_one
    refine ⟨(v : ℂ) + Complex.I / 2, hVS ⟨hε_ball ?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_right, Complex.norm_real, Real.norm_of_nonneg hv_pos.le]
      exact (min_le_left _ _).trans_lt (half_lt_self hε_pos)
    · intro heq
      have hre := congrArg Complex.re heq
      simp at hre
      linarith
    · dsimp [g]
      have hflip : -starRingEnd ℂ ((v : ℂ) + Complex.I / 2) = (-v : ℂ) + Complex.I / 2 := by
        apply Complex.ext
        · simp [map_ofNat]
        · simp [map_ofNat]; norm_num
      rw [hflip]
      have href := hA.edge_reflection v
      dsimp [f, saddleIntegrand]
      rw [href, Complex.conj_conj]
  have heqU : EqOn f g U :=
    hf_an.eqOn_of_preconnected_of_frequently_eq hg_an hU_conv.isPreconnected hI2 hfreq
  -- Extend from open U to closed edgeStrip δ by continuity
  intro b hb
  let seq : ℕ → ℂ := fun k => b - Complex.I * (((b.im - 1 / 2) / ((k : ℝ) + 2) : ℝ) : ℂ)
  have hseq_U : ∀ k : ℕ, seq k ∈ U := fun k => by
    change |(seq k).im - 1 / 2| < δ
    have hk_pos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have him : (seq k).im - 1 / 2 = (b.im - 1 / 2) * (1 - 1 / ((k : ℝ) + 2)) := by
      dsimp [seq]
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hfac_nn : 0 ≤ 1 - 1 / ((k : ℝ) + 2) := by
      rw [sub_nonneg, div_le_one hk_pos]
      linarith
    have hfac_lt : 1 - 1 / ((k : ℝ) + 2) < 1 := by
      have : 0 < 1 / ((k : ℝ) + 2) := one_div_pos.mpr hk_pos
      linarith
    rw [him, abs_mul, abs_of_nonneg hfac_nn]
    rcases eq_or_lt_of_le (abs_nonneg (b.im - 1 / 2)) with hb0 | hb0
    · rw [← hb0, zero_mul]; exact hδ
    · calc |b.im - 1 / 2| * (1 - 1 / ((k : ℝ) + 2))
          < |b.im - 1 / 2| * 1 := mul_lt_mul_of_pos_left hfac_lt hb0
        _ = |b.im - 1 / 2| := mul_one _
        _ ≤ δ := hb
  have hseq_tend : Tendsto seq atTop (𝓝 b) := by
    have h_zero : Tendsto (fun k : ℕ => Complex.I * (((b.im - 1 / 2) / ((k : ℝ) + 2) : ℝ) : ℂ))
        atTop (𝓝 0) := by
      have h_real : Tendsto (fun k : ℕ => (b.im - 1 / 2) / ((k : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa using tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp h_real)
    simpa [seq] using tendsto_const_nhds.sub h_zero
  have hf_cont_b : ContinuousWithinAt f (edgeStrip δ) b :=
    (saddleIntegrand_analyticOnNhd hΦ hA b hb).continuousAt.continuousWithinAt
  have hg_cont_b : ContinuousWithinAt g (edgeStrip δ) b := by
    have hb_flip : -starRingEnd ℂ b ∈ edgeStrip δ := by
      change |(-starRingEnd ℂ b).im - 1 / 2| ≤ δ
      have him : (-starRingEnd ℂ b).im = b.im := by simp
      rw [him]
      exact hb
    have h_f_cont : ContinuousAt f (-starRingEnd ℂ b) :=
      (saddleIntegrand_analyticOnNhd hΦ hA _ hb_flip).continuousAt
    have h_arg_cont : Continuous fun z : ℂ => -starRingEnd ℂ z := by fun_prop
    have h_g_cont : ContinuousAt g b :=
      Complex.continuous_conj.continuousAt.comp (h_f_cont.comp_of_eq h_arg_cont.continuousAt rfl)
    exact h_g_cont.continuousWithinAt
  have h_tend_f : Tendsto (fun k => f (seq k)) atTop (𝓝 (f b)) :=
    hf_cont_b.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hseq_tend
      (Eventually.of_forall fun k => hU_sub (hseq_U k)))
  have h_tend_g : Tendsto (fun k => g (seq k)) atTop (𝓝 (g b)) :=
    hg_cont_b.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hseq_tend
      (Eventually.of_forall fun k => hU_sub (hseq_U k)))
  have h_tend_eq : Tendsto (fun k => f (seq k)) atTop (𝓝 (g b)) :=
    h_tend_g.congr fun k => (heqU (hseq_U k)).symm
  have hfg : f b = g b := tendsto_nhds_unique h_tend_f h_tend_eq
  have hfg' : starRingEnd ℂ (f b) = f (-starRingEnd ℂ b) := by
    have h1 := congrArg (starRingEnd ℂ) hfg
    dsimp [g] at h1
    rwa [Complex.conj_conj] at h1
  exact hfg'.symm

/-- **Contour deformation + edge reflection**:
`e^{-iπ/4} 𝒥_A = 2 Re (𝒥_middle^+ + 𝒥_local^+ + 𝒥_outer^+)`. -/
lemma edgeIntegral_eq_two_mul_re_pos {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ}
    (hΦ : EdgePhaseData δ C₃ C₄ Φ₀) {x n M M' : ℝ} (hδ : 0 < δ) (hx : xiStar < x)
    {A : ℂ → ℂ} (hA : TwoSaddleAmplitude Φ₀ x n δ M M' A) :
    edgeIntegral Φ₀ x n A =
      ((2 * (middlePosIntegral Φ₀ x n δ C₃ M M' A +
        localPosIntegral Φ₀ x n δ C₃ M M' A +
        outerPosIntegral Φ₀ x n δ C₃ M M' A).re : ℝ) : ℂ) := by
  let u₀ := saddleU₀ δ C₃ M M' x
  let ℓ := saddleLength δ C₃ M M' x
  let f := saddleIntegrand Φ₀ x n A
  let dirR := Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))
  let dirL := Complex.exp (Complex.I * (Real.pi / 4 : ℂ))
  have hu₀_pos : 0 < u₀ := saddleU₀_pos hδ hx
  have hu₀_le : u₀ ≤ δ := saddleU₀_le_delta hδ hx
  have hu₀_lt_vx : u₀ < edgeV x := saddleU₀_lt_edgeV hδ hx
  have hf_edge_int : Integrable (fun v : ℝ => f ((v : ℂ) + Complex.I / 2)) := by
    have h := hA.edge_integrable.const_mul (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)))
    refine h.congr (Eventually.of_forall fun v => ?_)
    dsimp [f, saddleIntegrand]
    ring
  have hf_lower_int : Integrable (fun v : ℝ => f ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))) := by
    have h := (hA.lower_integrable u₀ hu₀_pos hu₀_le).const_mul
      (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)))
    refine h.congr (Eventually.of_forall fun v => ?_)
    dsimp [f, saddleIntegrand]
    ring
  have ht_edge : Tendsto (fun R : ℝ => ∫ v in (-R)..R, f ((v : ℂ) + Complex.I / 2))
      atTop (𝓝 (edgeIntegral Φ₀ x n A)) :=
    intervalIntegral_tendsto_integral hf_edge_int tendsto_neg_atTop_atBot tendsto_id
  let outerNeg := ∫ v in Iic (-(edgeV x + u₀)),
    f ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))
  have ht_oL : Tendsto (fun R : ℝ =>
      ∫ v in (-R)..(-(edgeV x + u₀)), f ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)))
      atTop (𝓝 outerNeg) :=
    intervalIntegral_tendsto_integral_Iic (-(edgeV x + u₀))
      hf_lower_int.integrableOn tendsto_neg_atTop_atBot
  have ht_oR : Tendsto (fun R : ℝ =>
      ∫ v in (edgeV x + u₀)..R, f ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)))
      atTop (𝓝 (outerPosIntegral Φ₀ x n δ C₃ M M' A)) :=
    intervalIntegral_tendsto_integral_Ioi (edgeV x + u₀) hf_lower_int.integrableOn tendsto_id
  have ht_vL : Tendsto (fun R : ℝ =>
      -(Complex.I * ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ), f ((-R : ℂ) + (t : ℂ) * Complex.I)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ =>
        -(Complex.I * (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
          ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ), A ((-R : ℂ) + (t : ℂ) * Complex.I) *
            Complex.exp ((n : ℂ) * phiX Φ₀ x ((-R : ℂ) + (t : ℂ) * Complex.I)))))
        atTop (𝓝 0) := by
      have h0 := hA.vertical_left_tendsto u₀ hu₀_pos hu₀_le
      simpa using (h0.const_mul (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)))).const_mul Complex.I |>.neg
    refine h1.congr fun R => ?_
    congr 2
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    dsimp [f, saddleIntegrand]
    ring
  have ht_vR : Tendsto (fun R : ℝ =>
      Complex.I * ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ), f ((R : ℂ) + (t : ℂ) * Complex.I))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ =>
        Complex.I * (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
          ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ), A ((R : ℂ) + (t : ℂ) * Complex.I) *
            Complex.exp ((n : ℂ) * phiX Φ₀ x ((R : ℂ) + (t : ℂ) * Complex.I))))
        atTop (𝓝 0) := by
      have h0 := hA.vertical_right_tendsto u₀ hu₀_pos hu₀_le
      simpa using (h0.const_mul (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)))).const_mul Complex.I
    refine h1.congr fun R => ?_
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    dsimp [f, saddleIntegrand]
    ring
  let locL := ∫ r in (-ℓ)..ℓ, f ((-(edgeV x : ℂ) + Complex.I / 2) + (r : ℂ) * dirL) * dirL
  let midAll := ∫ v in (-(edgeV x - u₀))..(edgeV x - u₀),
    f ((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ))
  have ht_rhs : Tendsto (fun R : ℝ =>
      -(Complex.I * ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ), f ((-R : ℂ) + (t : ℂ) * Complex.I)) +
      (∫ v in (-R)..(-(edgeV x + u₀)), f ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))) +
      locL + midAll + localPosIntegral Φ₀ x n δ C₃ M M' A +
      (∫ v in (edgeV x + u₀)..R, f ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))) +
      (Complex.I * ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ), f ((R : ℂ) + (t : ℂ) * Complex.I)))
      atTop (𝓝 (0 + outerNeg + locL + midAll + localPosIntegral Φ₀ x n δ C₃ M M' A +
        outerPosIntegral Φ₀ x n δ C₃ M M' A + 0)) :=
    ((((((ht_vL.add ht_oL).add tendsto_const_nhds).add tendsto_const_nhds).add
      tendsto_const_nhds).add ht_oR).add ht_vR)
  have ht_lhs_rhs : Tendsto (fun R : ℝ => ∫ v in (-R)..R, f ((v : ℂ) + Complex.I / 2))
      atTop (𝓝 (0 + outerNeg + locL + midAll + localPosIntegral Φ₀ x n δ C₃ M M' A +
        outerPosIntegral Φ₀ x n δ C₃ M M' A + 0)) := by
    refine ht_rhs.congr' ?_
    filter_upwards [eventually_ge_atTop (edgeV x + u₀ + 1)] with R hR
    exact (finite_five_piece_contour_eq hΦ hδ hx hA hR).symm
  have h_decomp : edgeIntegral Φ₀ x n A =
      outerNeg + locL + midAll + localPosIntegral Φ₀ x n δ C₃ M M' A +
        outerPosIntegral Φ₀ x n δ C₃ M M' A := by
    have h := tendsto_nhds_unique ht_edge ht_lhs_rhs
    simpa only [zero_add, add_zero] using h
  -- Now apply Schwarz reflection `b ↦ -\bar b` to `outerNeg`, `locL`, and the negative half of `midAll`
  have href := saddleIntegrand_reflect hΦ hδ hA
  have h_oL_eq : outerNeg = starRingEnd ℂ (outerPosIntegral Φ₀ x n δ C₃ M M' A) := by
    have ht1 : Tendsto (fun R : ℝ =>
        ∫ v in (-R)..(-(edgeV x + u₀)), f ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)))
        atTop (𝓝 outerNeg) := ht_oL
    have ht2 : Tendsto (fun R : ℝ =>
        starRingEnd ℂ (∫ w in (edgeV x + u₀)..R, f ((w : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))))
        atTop (𝓝 (starRingEnd ℂ (outerPosIntegral Φ₀ x n δ C₃ M M' A))) :=
      Complex.continuous_conj.continuousAt.tendsto.comp ht_oR
    have h_eq_R : ∀ R : ℝ,
        ∫ v in (-R)..(-(edgeV x + u₀)), f ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) =
        starRingEnd ℂ (∫ w in (edgeV x + u₀)..R, f ((w : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))) := by
      intro R
      have hcomm := (Complex.conjCLE : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm
        (hf_lower_int.intervalIntegrable (a := edgeV x + u₀) (b := R))
      simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] at hcomm
      have hsym : ∫ v in (-R)..(-(edgeV x + u₀)), f ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) =
          ∫ w in (edgeV x + u₀)..R, f ((-w : ℝ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) := by
        simpa [Complex.ofReal_neg] using intervalIntegral.integral_comp_neg
          (a := -R) (b := -(edgeV x + u₀))
          (fun w : ℝ => f ((-w : ℝ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)))
      have hcongr : ∫ w in (edgeV x + u₀)..R, f ((-w : ℝ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) =
          ∫ w in (edgeV x + u₀)..R,
            starRingEnd ℂ (f ((w : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))) := by
        refine intervalIntegral.integral_congr fun w _ => ?_
        have hmem : (w : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ) ∈ edgeStrip δ := by
          change |((w : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)).im - 1 / 2| ≤ δ
          simpa [abs_of_nonneg hu₀_pos.le] using hu₀_le
        have hfl : -starRingEnd ℂ ((w : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) =
            ((-w : ℝ) : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ) := by
          apply Complex.ext <;> simp
        rw [← hfl]
        exact href _ hmem
      exact hsym.trans (hcongr.trans hcomm)
    exact tendsto_nhds_unique ht1 (ht2.congr fun R => (h_eq_R R).symm)
  have h_locL_eq : locL = starRingEnd ℂ (localPosIntegral Φ₀ x n δ C₃ M M' A) := by
    dsimp [locL, localPosIntegral]
    have hdirR_im : dirR.im = -(√2 / 2) := by
      dsimp [dirR]; rw [exp_neg_I_pi_div_four_eq]; simp
    have h_inv_s2_pos : 0 < √2 / 2 := by positivity
    have h_l_inv_s2 : ℓ * (√2 / 2) = u₀ := by
      dsimp [u₀, saddleU₀, ℓ]
      have hs : √2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
      have hsq : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
      field_simp [hs]
      rw [hsq]
    have hℓ_nn : 0 ≤ ℓ := by dsimp [ℓ, saddleLength]; exact mul_nonneg (saddleScaleD_pos C₃ M M' hδ).le (mX_pos hx).le
    have hint_R : IntervalIntegrable (fun s : ℝ =>
        f (bX x + (s : ℂ) * dirR) * dirR) volume (-ℓ) ℓ := by
      have hmem_R : ∀ s ∈ Icc (-ℓ) ℓ, bX x + (s : ℂ) * dirR ∈ edgeStrip δ := fun s hs => by
        change |(bX x + (s : ℂ) * dirR).im - 1 / 2| ≤ δ
        have him : (bX x + (s : ℂ) * dirR).im - 1 / 2 = -(s * (√2 / 2)) := by
          dsimp [bX]; simp [hdirR_im]
        rw [him, abs_neg, abs_mul, abs_of_pos h_inv_s2_pos]
        exact (mul_le_mul_of_nonneg_right (abs_le.mpr hs) h_inv_s2_pos.le).trans
          (h_l_inv_s2.symm ▸ hu₀_le)
      exact ((ContinuousOn.mul ((saddleIntegrand_analyticOnNhd hΦ hA).continuousOn.comp
        (by fun_prop : Continuous fun s : ℝ => bX x + (s : ℂ) * dirR).continuousOn hmem_R)
        continuousOn_const).mono (by rw [Set.uIcc_of_le (by linarith)])).intervalIntegrable
    have hcomm := (Complex.conjCLE : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm hint_R
    simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] at hcomm
    have hsym : ∫ r in (-ℓ)..ℓ, f ((-(edgeV x : ℂ) + Complex.I / 2) + (r : ℂ) * dirL) * dirL =
        ∫ s in (-ℓ)..ℓ, f ((-(edgeV x : ℂ) + Complex.I / 2) + ((-s : ℝ) : ℂ) * dirL) * dirL := by
      simpa [Complex.ofReal_neg] using intervalIntegral.integral_comp_neg (a := -ℓ) (b := ℓ)
        (fun s : ℝ => f ((-(edgeV x : ℂ) + Complex.I / 2) + ((-s : ℝ) : ℂ) * dirL) * dirL)
    have hcongr : ∫ s in (-ℓ)..ℓ, f ((-(edgeV x : ℂ) + Complex.I / 2) + ((-s : ℝ) : ℂ) * dirL) * dirL =
        ∫ s in (-ℓ)..ℓ, starRingEnd ℂ (f (bX x + (s : ℂ) * dirR) * dirR) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le (by linarith)] at hs
      have hmem_R : bX x + (s : ℂ) * dirR ∈ edgeStrip δ := by
        change |(bX x + (s : ℂ) * dirR).im - 1 / 2| ≤ δ
        have him : (bX x + (s : ℂ) * dirR).im - 1 / 2 = -(s * (√2 / 2)) := by
          dsimp [bX]; simp [hdirR_im]
        rw [him, abs_neg, abs_mul, abs_of_pos h_inv_s2_pos]
        exact (mul_le_mul_of_nonneg_right (abs_le.mpr hs) h_inv_s2_pos.le).trans
          (h_l_inv_s2.symm ▸ hu₀_le)
      have hdir_conj : dirL = starRingEnd ℂ dirR := by
        dsimp [dirL, dirR]
        rw [← Complex.exp_conj]
        congr 1
        simp [map_ofNat]
      have hfl : -starRingEnd ℂ (bX x + (s : ℂ) * dirR) =
          (-(edgeV x : ℂ) + Complex.I / 2) + ((-s : ℝ) : ℂ) * dirL := by
        apply Complex.ext
        · dsimp [bX]
          simp [hdir_conj]
          ring
        · dsimp [bX]
          simp [hdir_conj]
      show f ((-(edgeV x : ℂ) + Complex.I / 2) + ((-s : ℝ) : ℂ) * dirL) * dirL =
        starRingEnd ℂ (f (bX x + (s : ℂ) * dirR) * dirR)
      rw [← hfl]
      dsimp only [f]
      rw [href _ hmem_R, hdir_conj, map_mul]
    exact hsym.trans (hcongr.trans hcomm)
  have h_mid_eq : midAll =
      middlePosIntegral Φ₀ x n δ C₃ M M' A +
        starRingEnd ℂ (middlePosIntegral Φ₀ x n δ C₃ M M' A) := by
    have hcont_m : ContinuousOn (fun v : ℝ => f ((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)))
        (Icc (-(edgeV x - u₀)) (edgeV x - u₀)) := by
      refine (saddleIntegrand_analyticOnNhd hΦ hA).continuousOn.comp
        ((by fun_prop : Continuous fun v : ℝ => (v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)).continuousOn)
        fun v _ => ?_
      change |((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)).im - 1 / 2| ≤ δ
      simpa [abs_of_nonneg hu₀_pos.le] using hu₀_le
    have hiL : IntervalIntegrable (fun v : ℝ => f ((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)))
        volume (-(edgeV x - u₀)) 0 :=
      (hcont_m.mono fun v hv => by
        rw [Set.uIcc_of_le (by linarith)] at hv
        exact ⟨hv.1, hv.2.trans (by linarith)⟩).intervalIntegrable
    have hiR : IntervalIntegrable (fun v : ℝ => f ((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)))
        volume 0 (edgeV x - u₀) :=
      (hcont_m.mono fun v hv => by
        rw [Set.uIcc_of_le (by linarith)] at hv
        exact ⟨(by linarith : -(edgeV x - u₀) ≤ 0).trans hv.1, hv.2⟩).intervalIntegrable
    have hsplit : midAll = (∫ v in (-(edgeV x - u₀))..0, f ((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ))) +
        middlePosIntegral Φ₀ x n δ C₃ M M' A :=
      (intervalIntegral.integral_add_adjacent_intervals hiL hiR).symm
    have hneg_half : ∫ v in (-(edgeV x - u₀))..0, f ((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)) =
        starRingEnd ℂ (middlePosIntegral Φ₀ x n δ C₃ M M' A) := by
      have hcomp := intervalIntegral.integral_comp_neg (a := -(edgeV x - u₀)) (b := 0)
        (fun w : ℝ => f ((w : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)))
      simp only [neg_neg, neg_zero] at hcomp
      have hcomm := (Complex.conjCLE : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm hiR
      simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] at hcomm
      have hcongr : ∫ w in (0 : ℝ)..(edgeV x - u₀), f ((-w : ℝ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)) =
          ∫ w in (0 : ℝ)..(edgeV x - u₀),
            starRingEnd ℂ (f ((w : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ))) := by
        refine intervalIntegral.integral_congr fun w _ => ?_
        have hmem : (w : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ) ∈ edgeStrip δ := by
          change |((w : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)).im - 1 / 2| ≤ δ
          simpa [abs_of_nonneg hu₀_pos.le] using hu₀_le
        have hfl : -starRingEnd ℂ ((w : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)) =
            ((-w : ℝ) : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ) := by
          apply Complex.ext <;> simp
        rw [← hfl]
        exact href _ hmem
      have hsym : ∫ v in (-(edgeV x - u₀))..0, f ((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)) =
          ∫ w in (0 : ℝ)..(edgeV x - u₀), f ((-w : ℝ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)) := by
        simpa [Complex.ofReal_neg] using intervalIntegral.integral_comp_neg
          (a := -(edgeV x - u₀)) (b := 0)
          (fun w : ℝ => f ((-w : ℝ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)))
      dsimp [middlePosIntegral]
      exact hsym.trans (hcongr.trans hcomm)
    rw [hsplit, hneg_half, add_comm]
  rw [h_decomp, h_oL_eq, h_locL_eq, h_mid_eq]
  set S := middlePosIntegral Φ₀ x n δ C₃ M M' A + localPosIntegral Φ₀ x n δ C₃ M M' A +
    outerPosIntegral Φ₀ x n δ C₃ M M' A
  have h_rearrange : starRingEnd ℂ (outerPosIntegral Φ₀ x n δ C₃ M M' A) +
      starRingEnd ℂ (localPosIntegral Φ₀ x n δ C₃ M M' A) +
      (middlePosIntegral Φ₀ x n δ C₃ M M' A + starRingEnd ℂ (middlePosIntegral Φ₀ x n δ C₃ M M' A)) +
      localPosIntegral Φ₀ x n δ C₃ M M' A + outerPosIntegral Φ₀ x n δ C₃ M M' A =
      S + starRingEnd ℂ S := by
    dsimp [S]
    simp only [map_add]
    ring
  rw [h_rearrange, Complex.add_conj]

/-! ### 5. Exponentially small middle and outer bounds `(SD.8)` -/

/-- Middle-segment bound in `(SD.8)`: for `n m_x³ ≥ max 1 (8 √2 / d²)`,
`‖middlePosIntegral‖ ≤ ‖A (b_x)‖ * √(2π / (n α_x)) * (C_mid * exp(-c_mid n m_x³))`. -/
lemma middlePosIntegral_bound {δ C₃ M M' : ℝ} (hδ : 0 < δ) (hC₃ : 0 ≤ C₃)
    (hM : 0 ≤ M) :
    ∃ c_mid C_mid : ℝ, 0 < c_mid ∧ 0 ≤ C_mid ∧
      ∀ {C₄ : ℝ} {Φ₀ : ℂ → ℂ} {x n : ℝ} {A : ℂ → ℂ},
        xiStar < x → 0 < n →
        max 1 (8 * √2 / saddleScaleD δ C₃ M M' ^ 2) ≤ n * mX x ^ 3 →
        EdgePhaseData δ C₃ C₄ Φ₀ →
        TwoSaddleAmplitude Φ₀ x n δ M M' A →
        ‖middlePosIntegral Φ₀ x n δ C₃ M M' A‖ ≤
          ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) *
            (C_mid * Real.exp (-c_mid * (n * mX x ^ 3))) := by
  obtain ⟨c₀, C₀, hc₀_pos, hC₀_pos, hm_unif⟩ := mX_uniform_bounds
  let d : ℝ := saddleScaleD δ C₃ M M'
  have hd_pos : 0 < d := saddleScaleD_pos C₃ M M' hδ
  let c_mid : ℝ := Real.pi * d ^ 2 / 4
  let C_mid : ℝ := 2 * √C₀ / (Real.pi ^ (3 / 2 : ℝ) * d)
  have hpi := Real.pi_pos
  have hc_mid_pos : 0 < c_mid := by positivity
  have hC_mid_nn : 0 ≤ C_mid := by positivity
  refine ⟨c_mid, C_mid, hc_mid_pos, hC_mid_nn, fun {C₄ Φ₀ x n A} hx hn hnm hΦ hA => ?_⟩
  let u₀ := saddleU₀ δ C₃ M M' x
  let ℓ := saddleLength δ C₃ M M' x
  have hu₀_pos : 0 < u₀ := saddleU₀_pos hδ hx
  have hu₀_le : u₀ ≤ δ := saddleU₀_le_delta hδ hx
  have hu₀_lt_vx : u₀ < edgeV x := saddleU₀_lt_edgeV hδ hx
  have hm_pos : 0 < mX x := mX_pos hx
  have hs_pos : 0 < slopeX x := slopeX_pos hx
  have ha_pos : 0 < alphaX x := alphaX_pos hx
  have h_unif := hm_unif x hx
  have hM_dom_outer : 8 * M ≤ n * u₀ * mX x := by
    have hMd : M * d ≤ 1 := saddleScaleD_mul_M_le_one hM
    have hnm' : 8 * √2 / d ^ 2 ≤ n * mX x ^ 3 := (le_max_right _ _).trans hnm
    have hs : 0 < √2 := Real.sqrt_pos.mpr zero_lt_two
    have h8 : 8 * M ≤ d / √2 * (n * mX x ^ 3) := by
      have h0 : 8 * √2 * (M * d) ≤ d ^ 2 * (n * mX x ^ 3) := by
        calc 8 * √2 * (M * d) ≤ 8 * √2 * 1 := mul_le_mul_of_nonneg_left hMd (by positivity)
          _ = d ^ 2 * (8 * √2 / d ^ 2) := by field_simp [hd_pos.ne']
          _ ≤ d ^ 2 * (n * mX x ^ 3) := mul_le_mul_of_nonneg_left hnm' (sq_nonneg d)
      refine le_of_mul_le_mul_left ?_ (show 0 < √2 * d by positivity)
      calc (√2 * d) * (8 * M) = 8 * √2 * (M * d) := by ring
        _ ≤ d ^ 2 * (n * mX x ^ 3) := h0
        _ = (√2 * d) * (d / √2 * (n * mX x ^ 3)) := by field_simp [hs.ne']
    have h1 : mX x ^ 2 ≤ mX x := by nlinarith [mX_le_one x]
    have h_lb : d / √2 * (n * mX x ^ 3) ≤ n * u₀ * mX x := by
      calc d / √2 * (n * mX x ^ 3) = (d / √2 * n * mX x) * mX x ^ 2 := by ring
        _ ≤ (d / √2 * n * mX x) * mX x := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = n * u₀ * mX x := by dsimp [u₀, saddleU₀, ℓ, saddleLength]; ring
    exact h8.trans h_lb
  have h_re_bd : ∀ v ∈ Icc (0 : ℝ) (edgeV x - u₀),
      ‖saddleIntegrand Φ₀ x n A ((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ))‖ ≤
        ‖A (bX x)‖ * Real.exp (-(Real.pi / 2 * n * u₀ * slopeX x) * (edgeV x - v)) := by
    intro v hv
    let w : ℂ := (v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)
    have hw_mem : w ∈ edgeStrip δ := by
      change |w.im - 1 / 2| ≤ δ
      simpa [w, abs_of_nonneg hu₀_pos.le] using hu₀_le
    have hA_bd := amplitude_growth_le hA (bX_mem_edgeStrip hδ.le x) hw_mem
    have hnorm_diff : ‖w - bX x‖ ≤ 2 * (edgeV x - v) := by
      have hsub : w - bX x = ((v - edgeV x : ℝ) : ℂ) + (u₀ : ℂ) * Complex.I := by
        dsimp [w, bX]; push_cast; ring
      rw [hsub]
      calc ‖((v - edgeV x : ℝ) : ℂ) + (u₀ : ℂ) * Complex.I‖
          ≤ ‖((v - edgeV x : ℝ) : ℂ)‖ + ‖(u₀ : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |v - edgeV x| + u₀ := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_nonneg hu₀_pos.le]
        _ = (edgeV x - v) + u₀ := by
            rw [abs_of_nonpos (by linarith [hv.2])]
            ring
        _ ≤ (edgeV x - v) + (edgeV x - v) := by linarith [hv.2]
        _ = 2 * (edgeV x - v) := by ring
    have h_phase_taylor := phiX_re_normal_taylor hΦ hδ.le x v u₀
      (by rw [abs_of_nonneg hu₀_pos.le]; exact hu₀_le)
    have h_chord := edgeF_chord_lower hx hv.1 (by linarith [hv.2])
    have hC₃ℓ : C₃ * ℓ ≤ 2 * √2 * Real.pi * slopeX x := by
      calc C₃ * ℓ = (C₃ * d) * mX x := by dsimp [ℓ, saddleLength]; ring
        _ ≤ (2 * √2 * Real.pi) * slopeX x :=
            mul_le_mul (saddleScaleD_mul_C3_le_slope_const hC₃) (mX_le_slopeX x)
              hm_pos.le (by positivity)
        _ = 2 * √2 * Real.pi * slopeX x := by ring
    have h_cub : C₃ * u₀ ^ 3 / 6 ≤ (Real.pi / 3) * u₀ * slopeX x * (edgeV x - v) := by
      have h_u0_def : ℓ = √2 * u₀ := by
        dsimp [ℓ, u₀, saddleU₀, saddleLength]
        have hs : √2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
        field_simp [hs]
      have h1 : C₃ * u₀ ^ 2 ≤ 2 * Real.pi * slopeX x * u₀ := by
        rw [h_u0_def] at hC₃ℓ
        have hs : 0 < √2 := Real.sqrt_pos.mpr zero_lt_two
        nlinarith
      calc C₃ * u₀ ^ 3 / 6 = (C₃ * u₀ ^ 2) * u₀ / 6 := by ring
        _ ≤ (2 * Real.pi * slopeX x * u₀) * u₀ / 6 := by gcongr
        _ = (Real.pi / 3) * u₀ * slopeX x * u₀ := by ring
        _ ≤ (Real.pi / 3) * u₀ * slopeX x * (edgeV x - v) := by gcongr; linarith [hv.2]
    have h_phi_re : (phiX Φ₀ x w).re ≤ -Real.pi * u₀ * slopeX x * (edgeV x - v) := by
      have ht := (abs_le.mp h_phase_taylor).2
      rw [abs_of_nonneg hu₀_pos.le] at ht
      have hlin : (4 * Real.pi / 3) * u₀ * (edgeF v - x) ≤
          -(4 * Real.pi / 3) * u₀ * slopeX x * (edgeV x - v) := by
        have h1 : (edgeF v - x) ≤ -slopeX x * (edgeV x - v) := by linarith
        nlinarith [mul_pos (by positivity : 0 < 4 * Real.pi / 3) hu₀_pos]
      dsimp [w]
      linarith
    have hM_dom : 2 * M ≤ (Real.pi / 2) * n * u₀ * slopeX x := by
      have h1 : 8 * M ≤ n * u₀ * slopeX x := hM_dom_outer.trans
        (mul_le_mul_of_nonneg_left (mX_le_slopeX x) (by positivity))
      have hpi3 : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
      nlinarith
    have hexp_le : n * (phiX Φ₀ x w).re + M * ‖w - bX x‖ ≤
        -(Real.pi / 2 * n * u₀ * slopeX x) * (edgeV x - v) := by
      have h1 : n * (phiX Φ₀ x w).re ≤ -Real.pi * n * u₀ * slopeX x * (edgeV x - v) := by
        calc n * (phiX Φ₀ x w).re ≤ n * (-Real.pi * u₀ * slopeX x * (edgeV x - v)) :=
            mul_le_mul_of_nonneg_left h_phi_re hn.le
          _ = -Real.pi * n * u₀ * slopeX x * (edgeV x - v) := by ring
      have h2 : M * ‖w - bX x‖ ≤ 2 * M * (edgeV x - v) := by
        calc M * ‖w - bX x‖ ≤ M * (2 * (edgeV x - v)) := mul_le_mul_of_nonneg_left hnorm_diff hM
          _ = 2 * M * (edgeV x - v) := by ring
      have h3 : 2 * M * (edgeV x - v) ≤ (Real.pi / 2 * n * u₀ * slopeX x) * (edgeV x - v) :=
        mul_le_mul_of_nonneg_right hM_dom (by linarith [hv.2])
      linarith
    have hnorm_s : ‖saddleIntegrand Φ₀ x n A w‖ =
        ‖A w‖ * Real.exp (n * (phiX Φ₀ x w).re) := by
      dsimp [saddleIntegrand]
      rw [norm_mul, norm_mul, show -Complex.I * (Real.pi / 4 : ℂ) =
        ((-Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp]
      simp
    rw [hnorm_s]
    calc ‖A w‖ * Real.exp (n * (phiX Φ₀ x w).re)
        ≤ (‖A (bX x)‖ * Real.exp (M * ‖w - bX x‖)) * Real.exp (n * (phiX Φ₀ x w).re) :=
            mul_le_mul_of_nonneg_right hA_bd (Real.exp_pos _).le
      _ = ‖A (bX x)‖ * Real.exp (n * (phiX Φ₀ x w).re + M * ‖w - bX x‖) := by
            rw [mul_assoc, ← Real.exp_add, add_comm]
      _ ≤ ‖A (bX x)‖ * Real.exp (-(Real.pi / 2 * n * u₀ * slopeX x) * (edgeV x - v)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (norm_nonneg _)
  let a_mid : ℝ := Real.pi / 2 * n * u₀ * slopeX x
  have ha_mid_pos : 0 < a_mid := by positivity
  have hn_int : ‖middlePosIntegral Φ₀ x n δ C₃ M M' A‖ ≤
      ∫ v in (0 : ℝ)..(edgeV x - u₀),
        ‖saddleIntegrand Φ₀ x n A ((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ))‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by linarith)
  have hcont_l : ContinuousOn (fun v : ℝ =>
      ‖saddleIntegrand Φ₀ x n A ((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ))‖)
      (Icc 0 (edgeV x - u₀)) := by
    refine ContinuousOn.norm ((saddleIntegrand_analyticOnNhd hΦ hA).continuousOn.comp
      ((by fun_prop : Continuous fun v : ℝ => (v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)).continuousOn)
      fun v _ => ?_)
    change |((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ)).im - 1 / 2| ≤ δ
    simpa [abs_of_nonneg hu₀_pos.le] using hu₀_le
  have hmono : ∫ v in (0 : ℝ)..(edgeV x - u₀),
      ‖saddleIntegrand Φ₀ x n A ((v : ℂ) + Complex.I * ((1 / 2 + u₀ : ℝ) : ℂ))‖ ≤
      ∫ v in (0 : ℝ)..(edgeV x - u₀), ‖A (bX x)‖ * Real.exp (-a_mid * (edgeV x - v)) :=
    intervalIntegral.integral_mono_on (by linarith)
      ((hcont_l.mono (by rw [Set.uIcc_of_le (by linarith)])).intervalIntegrable)
      ((by fun_prop : Continuous fun v : ℝ => ‖A (bX x)‖ * Real.exp (-a_mid * (edgeV x - v))).intervalIntegrable _ _)
      h_re_bd
  have h_eval_mid : ∫ v in (0 : ℝ)..(edgeV x - u₀),
      ‖A (bX x)‖ * Real.exp (-a_mid * (edgeV x - v)) ≤
      ‖A (bX x)‖ * Real.exp (-a_mid * u₀) / a_mid := by
    rw [intervalIntegral.integral_const_mul]
    have hftc : ∫ v in (0 : ℝ)..(edgeV x - u₀), Real.exp (-a_mid * (edgeV x - v)) =
        (Real.exp (-a_mid * u₀) - Real.exp (-a_mid * edgeV x)) / a_mid := by
      have hd : ∀ v ∈ uIcc (0 : ℝ) (edgeV x - u₀),
          HasDerivAt (fun t => Real.exp (-a_mid * (edgeV x - t)) / a_mid)
            (Real.exp (-a_mid * (edgeV x - v))) v := fun v _ => by
        have hlin : HasDerivAt (fun t => -a_mid * (edgeV x - t)) a_mid v := by
          have h1 : HasDerivAt (fun t => edgeV x - t) (-1) v := (hasDerivAt_id v).const_sub _
          exact (h1.const_mul (-a_mid)).congr_deriv (by ring)
        exact (hlin.exp.div_const a_mid).congr_deriv (by field_simp [ha_mid_pos.ne'])
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((by fun_prop : Continuous fun v => Real.exp (-a_mid * (edgeV x - v))).intervalIntegrable _ _)
      rw [h]
      have h1 : edgeV x - (edgeV x - u₀) = u₀ := by ring
      have h2 : edgeV x - 0 = edgeV x := sub_zero _
      rw [h1, h2]
      ring
    rw [hftc]
    have hexp_pos : 0 < Real.exp (-a_mid * edgeV x) := Real.exp_pos _
    have hle : (Real.exp (-a_mid * u₀) - Real.exp (-a_mid * edgeV x)) / a_mid ≤
        Real.exp (-a_mid * u₀) / a_mid := by
      gcongr; linarith
    calc ‖A (bX x)‖ * ((Real.exp (-a_mid * u₀) - Real.exp (-a_mid * edgeV x)) / a_mid)
        ≤ ‖A (bX x)‖ * (Real.exp (-a_mid * u₀) / a_mid) := by gcongr
      _ = ‖A (bX x)‖ * Real.exp (-a_mid * u₀) / a_mid := by ring
  -- Compare `1 / a_mid` with `√(2π / (n α_x)) * C_mid` and `a_mid * u₀` with `c_mid * n m_x³`
  have h_exp_cmp : c_mid * (n * mX x ^ 3) ≤ a_mid * u₀ := by
    have h1 : u₀ ^ 2 * slopeX x = (d ^ 2 / 2) * (mX x ^ 2 * slopeX x) := by
      dsimp [u₀, saddleU₀, ℓ, saddleLength]
      have hs : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
      rw [div_pow, hs]
      ring
    have h2 : mX x ^ 3 ≤ mX x ^ 2 * slopeX x :=
      (show mX x ^ 3 = mX x ^ 2 * mX x by ring) ▸ mul_le_mul_of_nonneg_left (mX_le_slopeX x) (sq_nonneg _)
    calc c_mid * (n * mX x ^ 3)
        = (Real.pi / 2 * n) * ((d ^ 2 / 2) * mX x ^ 3) := by dsimp [c_mid]; ring
      _ ≤ (Real.pi / 2 * n) * (u₀ ^ 2 * slopeX x) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc (d ^ 2 / 2) * mX x ^ 3 ≤ (d ^ 2 / 2) * (mX x ^ 2 * slopeX x) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
            _ = u₀ ^ 2 * slopeX x := h1.symm
      _ = a_mid * u₀ := by dsimp [a_mid]; ring
  have h_pref : 1 / a_mid ≤ √(2 * Real.pi / (n * alphaX x)) * C_mid := by
    have h_nm1 : 1 ≤ n * mX x ^ 3 := (le_max_left _ _).trans hnm
    have h_alpha_le : alphaX x ≤ C₀ * mX x := h_unif.2.2
    have h_sqrt_lb : 1 ≤ √(n * mX x ^ 3) := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt h_nm1
    have h_prod : Real.sqrt (n * alphaX x) / (Real.pi / 2 * n * u₀ * slopeX x) ≤
        √(2 * Real.pi) * C_mid := by
      have h_num : √(n * alphaX x) ≤ √C₀ * √(n * mX x) := by
        rw [← Real.sqrt_mul hC₀_pos.le]
        refine Real.sqrt_le_sqrt ?_
        calc n * alphaX x ≤ n * (C₀ * mX x) := mul_le_mul_of_nonneg_left h_alpha_le hn.le
          _ = C₀ * (n * mX x) := by ring
      have h_den : Real.pi / (2 * √2) * d * (n * mX x ^ 2) ≤ Real.pi / 2 * n * u₀ * slopeX x := by
        calc Real.pi / (2 * √2) * d * (n * mX x ^ 2)
            = (Real.pi / 2 * n * u₀) * mX x := by dsimp [u₀, saddleU₀, ℓ, saddleLength]; ring
          _ ≤ (Real.pi / 2 * n * u₀) * slopeX x :=
              mul_le_mul_of_nonneg_left (mX_le_slopeX x) (by positivity)
      have h_eq : √(n * mX x) / (n * mX x ^ 2) = 1 / √(n * mX x ^ 3) := by
        have h1 : 0 < √n := Real.sqrt_pos.mpr hn
        have h2 : 0 < √(mX x) := Real.sqrt_pos.mpr hm_pos
        have hsqn : √n ^ 2 = n := Real.sq_sqrt hn.le
        have hsqm : √(mX x) ^ 2 = mX x := Real.sq_sqrt hm_pos.le
        have hs1 : √(n * mX x) = √n * √(mX x) := Real.sqrt_mul hn.le (mX x)
        have hs3 : √(n * mX x ^ 3) = (√n * √(mX x)) * mX x := by
          rw [show n * mX x ^ 3 = (n * mX x) * mX x ^ 2 by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq hm_pos.le, hs1]
        rw [hs1, hs3, div_eq_div_iff (by positivity) (by positivity)]
        calc √n * √(mX x) * (√n * √(mX x) * mX x)
            = (√n ^ 2 * √(mX x) ^ 2) * mX x := by ring
          _ = 1 * (n * mX x ^ 2) := by rw [hsqn, hsqm]; ring
      calc √(n * alphaX x) / (Real.pi / 2 * n * u₀ * slopeX x)
          ≤ (√C₀ * √(n * mX x)) / (Real.pi / 2 * n * u₀ * slopeX x) :=
            div_le_div_of_nonneg_right h_num (by positivity)
        _ ≤ (√C₀ * √(n * mX x)) / (Real.pi / (2 * √2) * d * (n * mX x ^ 2)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) h_den
        _ = (2 * √2 * √C₀ / (Real.pi * d)) * (√(n * mX x) / (n * mX x ^ 2)) := by
            have hs2 : √2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
            field_simp [hpi.ne', hd_pos.ne', hn.ne', hm_pos.ne', hs2]
        _ = (2 * √2 * √C₀ / (Real.pi * d)) * (1 / √(n * mX x ^ 3)) := by rw [h_eq]
        _ ≤ (2 * √2 * √C₀ / (Real.pi * d)) * 1 := by
            gcongr; exact (div_le_one (by positivity)).mpr h_sqrt_lb
        _ = √(2 * Real.pi) * C_mid := by
            have hpi32 : Real.pi ^ (3 / 2 : ℝ) = Real.pi * √Real.pi := by
              rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hpi,
                Real.rpow_one, ← Real.sqrt_eq_rpow]
            dsimp [C_mid]
            rw [hpi32, Real.sqrt_mul zero_le_two]
            have hsr : √Real.pi ≠ 0 := (Real.sqrt_pos.mpr hpi).ne'
            have hs2 : √2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
            field_simp [hsr, hs2, hpi.ne', hd_pos.ne']
    have h_main : 1 / a_mid = √(2 * Real.pi / (n * alphaX x)) *
        (√(n * alphaX x) / (Real.pi / 2 * n * u₀ * slopeX x)) / √(2 * Real.pi) := by
      have h1 : 0 < √(n * alphaX x) := Real.sqrt_pos.mpr (by positivity)
      have h2 : 0 < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
      rw [Real.sqrt_div (by positivity)]
      dsimp [a_mid]
      field_simp [h1.ne', h2.ne']
    rw [h_main, div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))]
    exact (mul_le_mul_of_nonneg_left h_prod (Real.sqrt_nonneg _)).trans_eq (by ring)
  calc ‖middlePosIntegral Φ₀ x n δ C₃ M M' A‖
      ≤ ‖A (bX x)‖ * Real.exp (-a_mid * u₀) / a_mid :=
          (hn_int.trans hmono).trans h_eval_mid
    _ = ‖A (bX x)‖ * (1 / a_mid) * Real.exp (-a_mid * u₀) := by ring
    _ ≤ ‖A (bX x)‖ * (√(2 * Real.pi / (n * alphaX x)) * C_mid) *
          Real.exp (-c_mid * (n * mX x ^ 3)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h_pref (norm_nonneg _))
            (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)
    _ = ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) *
          (C_mid * Real.exp (-c_mid * (n * mX x ^ 3))) := by ring

/-- Outer-ray bound in `(SD.8)`: for `n m_x³ ≥ max 1 (8 √2 / d²)`,
`‖outerPosIntegral‖ ≤ ‖A (b_x)‖ * √(2π / (n α_x)) * (C_out * exp(-c_out n m_x³))`. -/
lemma outerPosIntegral_bound {δ C₃ M M' : ℝ} (hδ : 0 < δ) (hC₃ : 0 ≤ C₃)
    (hM : 0 ≤ M) :
    ∃ c_out C_out : ℝ, 0 < c_out ∧ 0 ≤ C_out ∧
      ∀ {C₄ : ℝ} {Φ₀ : ℂ → ℂ} {x n : ℝ} {A : ℂ → ℂ},
        xiStar < x → 0 < n →
        max 1 (8 * √2 / saddleScaleD δ C₃ M M' ^ 2) ≤ n * mX x ^ 3 →
        EdgePhaseData δ C₃ C₄ Φ₀ →
        TwoSaddleAmplitude Φ₀ x n δ M M' A →
        ‖outerPosIntegral Φ₀ x n δ C₃ M M' A‖ ≤
          ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) *
            (C_out * Real.exp (-c_out * (n * mX x ^ 3))) := by
  let d : ℝ := saddleScaleD δ C₃ M M'
  have hd_pos : 0 < d := saddleScaleD_pos C₃ M M' hδ
  let c_out : ℝ := d ^ 2 / 4
  let C_out : ℝ := 2 / (√Real.pi * d)
  have hpi := Real.pi_pos
  have hc_out_pos : 0 < c_out := by positivity
  have hC_out_nn : 0 ≤ C_out := by positivity
  refine ⟨c_out, C_out, hc_out_pos, hC_out_nn, fun {C₄ Φ₀ x n A} hx hn hnm hΦ hA => ?_⟩
  let u₀ := saddleU₀ δ C₃ M M' x
  let ℓ := saddleLength δ C₃ M M' x
  have hu₀_pos : 0 < u₀ := saddleU₀_pos hδ hx
  have hu₀_le : u₀ ≤ δ := saddleU₀_le_delta hδ hx
  have hm_pos : 0 < mX x := mX_pos hx
  have ha_pos : 0 < alphaX x := alphaX_pos hx
  let a_out : ℝ := 1 / 2 * n * alphaX x * u₀
  have ha_out_pos : 0 < a_out := by positivity
  have hM_dom_outer : 8 * M ≤ n * u₀ * mX x := by
    have hMd : M * d ≤ 1 := saddleScaleD_mul_M_le_one hM
    have hnm' : 8 * √2 / d ^ 2 ≤ n * mX x ^ 3 := (le_max_right _ _).trans hnm
    have hs : 0 < √2 := Real.sqrt_pos.mpr zero_lt_two
    have h8 : 8 * M ≤ d / √2 * (n * mX x ^ 3) := by
      have h0 : 8 * √2 * (M * d) ≤ d ^ 2 * (n * mX x ^ 3) := by
        calc 8 * √2 * (M * d) ≤ 8 * √2 * 1 := mul_le_mul_of_nonneg_left hMd (by positivity)
          _ = d ^ 2 * (8 * √2 / d ^ 2) := by field_simp [hd_pos.ne']
          _ ≤ d ^ 2 * (n * mX x ^ 3) := mul_le_mul_of_nonneg_left hnm' (sq_nonneg d)
      refine le_of_mul_le_mul_left ?_ (show 0 < √2 * d by positivity)
      calc (√2 * d) * (8 * M) = 8 * √2 * (M * d) := by ring
        _ ≤ d ^ 2 * (n * mX x ^ 3) := h0
        _ = (√2 * d) * (d / √2 * (n * mX x ^ 3)) := by field_simp [hs.ne']
    have h1 : mX x ^ 2 ≤ mX x := by nlinarith [mX_le_one x]
    have h_lb : d / √2 * (n * mX x ^ 3) ≤ n * u₀ * mX x := by
      calc d / √2 * (n * mX x ^ 3) = (d / √2 * n * mX x) * mX x ^ 2 := by ring
        _ ≤ (d / √2 * n * mX x) * mX x := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = n * u₀ * mX x := by dsimp [u₀, saddleU₀, ℓ, saddleLength]; ring
    exact h8.trans h_lb
  have hf_lower_int : Integrable (fun v : ℝ =>
      saddleIntegrand Φ₀ x n A ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))) := by
    have h := (hA.lower_integrable u₀ hu₀_pos hu₀_le).const_mul
      (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)))
    refine h.congr (Eventually.of_forall fun v => ?_)
    dsimp [saddleIntegrand]
    ring
  have h_re_bd : ∀ v ∈ Ioi (edgeV x + u₀),
      ‖saddleIntegrand Φ₀ x n A ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))‖ ≤
        ‖A (bX x)‖ * Real.exp (-a_out * (v - edgeV x)) := by
    intro v hv
    rw [mem_Ioi] at hv
    let w : ℂ := (v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)
    have hw_mem : w ∈ edgeStrip δ := by
      change |w.im - 1 / 2| ≤ δ
      simpa [w, abs_of_nonneg hu₀_pos.le] using hu₀_le
    have hA_bd := amplitude_growth_le hA (bX_mem_edgeStrip hδ.le x) hw_mem
    have hnorm_diff : ‖w - bX x‖ ≤ 2 * (v - edgeV x) := by
      have hsub : w - bX x = ((v - edgeV x : ℝ) : ℂ) + ((-u₀ : ℝ) : ℂ) * Complex.I := by
        dsimp [w, bX]; push_cast; ring
      rw [hsub]
      calc ‖((v - edgeV x : ℝ) : ℂ) + ((-u₀ : ℝ) : ℂ) * Complex.I‖
          ≤ ‖((v - edgeV x : ℝ) : ℂ)‖ + ‖((-u₀ : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |v - edgeV x| + |-u₀| := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, Complex.norm_I, mul_one]
        _ = (v - edgeV x) + u₀ := by
            rw [abs_of_pos (by linarith), abs_neg, abs_of_nonneg hu₀_pos.le]
        _ ≤ (v - edgeV x) + (v - edgeV x) := by linarith
        _ = 2 * (v - edgeV x) := by ring
    have h_phase_taylor := phiX_re_normal_taylor hΦ hδ.le x v (-u₀)
      (by rw [abs_neg, abs_of_nonneg hu₀_pos.le]; exact hu₀_le)
    have h_tan := edgeF_tangent_lower hx (v := v) (by linarith)
    have hC₃ℓ : C₃ * ℓ ≤ alphaX x := by
      calc C₃ * ℓ = (C₃ * d) * mX x := by dsimp [ℓ, saddleLength]; ring
        _ ≤ 1 * alphaX x := mul_le_mul (saddleScaleD_mul_C3_le_one hC₃) (mX_le_alphaX x)
            hm_pos.le zero_le_one
        _ = alphaX x := one_mul _
    have h_cub : C₃ * |-u₀| ^ 3 / 6 ≤ (alphaX x / 4) * u₀ * (v - edgeV x) := by
      rw [abs_neg, abs_of_nonneg hu₀_pos.le]
      have h_u0_def : ℓ = √2 * u₀ := by
        dsimp [ℓ, u₀, saddleU₀, saddleLength]
        have hs : √2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
        field_simp [hs]
      have h1 : C₃ * u₀ ^ 2 ≤ alphaX x * u₀ := by
        rw [h_u0_def] at hC₃ℓ
        have hs : 1 ≤ √2 := (Real.lt_sqrt_of_sq_lt (by norm_num)).le
        have hC₃u : C₃ * u₀ ≤ C₃ * (√2 * u₀) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hu₀_pos.le hs) hC₃
        calc C₃ * u₀ ^ 2 = (C₃ * u₀) * u₀ := by ring
          _ ≤ (C₃ * (√2 * u₀)) * u₀ := mul_le_mul_of_nonneg_right hC₃u hu₀_pos.le
          _ ≤ alphaX x * u₀ := mul_le_mul_of_nonneg_right hC₃ℓ hu₀_pos.le
      calc C₃ * u₀ ^ 3 / 6 = (C₃ * u₀ ^ 2) * u₀ / 6 := by ring
        _ ≤ (alphaX x * u₀) * u₀ / 6 := by gcongr
        _ = (alphaX x / 6) * u₀ * u₀ := by ring
        _ ≤ (alphaX x / 4) * u₀ * (v - edgeV x) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (by linarith [ha_pos]) hu₀_pos.le)
              (by linarith) hu₀_pos.le (by positivity)
    have h_phi_re : (phiX Φ₀ x w).re ≤ -(3 / 4) * alphaX x * u₀ * (v - edgeV x) := by
      have ht := (abs_le.mp h_phase_taylor).2
      rw [abs_neg, abs_of_nonneg hu₀_pos.le] at h_cub
      have hlin : (4 * Real.pi / 3) * (-u₀) * (edgeF v - x) ≤
          -alphaX x * u₀ * (v - edgeV x) := by
        have h1 : (4 * Real.pi / 3) * edgeF' (edgeV x) * (v - edgeV x) ≤
            (4 * Real.pi / 3) * (edgeF v - x) := by
          have : 0 ≤ 4 * Real.pi / 3 := by positivity
          nlinarith
        change alphaX x * (v - edgeV x) ≤ (4 * Real.pi / 3) * (edgeF v - x) at h1
        nlinarith [hu₀_pos]
      have h_w_eq : (v : ℂ) + Complex.I * ((1 / 2 + -u₀ : ℝ) : ℂ) = w := by
        dsimp [w]; push_cast; ring
      rw [h_w_eq, abs_neg, abs_of_nonneg hu₀_pos.le] at ht
      linarith
    have hM_dom : 2 * M ≤ (1 / 4) * n * alphaX x * u₀ := by
      have hn_ua_ge : 8 * M ≤ n * u₀ * alphaX x :=
        hM_dom_outer.trans (mul_le_mul_of_nonneg_left (mX_le_alphaX x) (by positivity))
      linarith
    have hexp_le : n * (phiX Φ₀ x w).re + M * ‖w - bX x‖ ≤ -a_out * (v - edgeV x) := by
      have h1 : n * (phiX Φ₀ x w).re ≤ -(3 / 4) * n * alphaX x * u₀ * (v - edgeV x) := by
        calc n * (phiX Φ₀ x w).re ≤ n * (-(3 / 4) * alphaX x * u₀ * (v - edgeV x)) :=
            mul_le_mul_of_nonneg_left h_phi_re hn.le
          _ = -(3 / 4) * n * alphaX x * u₀ * (v - edgeV x) := by ring
      have h2 : M * ‖w - bX x‖ ≤ 2 * M * (v - edgeV x) := by
        calc M * ‖w - bX x‖ ≤ M * (2 * (v - edgeV x)) := mul_le_mul_of_nonneg_left hnorm_diff hM
          _ = 2 * M * (v - edgeV x) := by ring
      have h3 : 2 * M * (v - edgeV x) ≤ ((1 / 4) * n * alphaX x * u₀) * (v - edgeV x) :=
        mul_le_mul_of_nonneg_right hM_dom (by linarith)
      dsimp [a_out]
      linarith
    have hnorm_s : ‖saddleIntegrand Φ₀ x n A w‖ =
        ‖A w‖ * Real.exp (n * (phiX Φ₀ x w).re) := by
      dsimp [saddleIntegrand]
      rw [norm_mul, norm_mul, show -Complex.I * (Real.pi / 4 : ℂ) =
        ((-Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp]
      simp
    rw [hnorm_s]
    calc ‖A w‖ * Real.exp (n * (phiX Φ₀ x w).re)
        ≤ (‖A (bX x)‖ * Real.exp (M * ‖w - bX x‖)) * Real.exp (n * (phiX Φ₀ x w).re) :=
            mul_le_mul_of_nonneg_right hA_bd (Real.exp_pos _).le
      _ = ‖A (bX x)‖ * Real.exp (n * (phiX Φ₀ x w).re + M * ‖w - bX x‖) := by
            rw [mul_assoc, ← Real.exp_add, add_comm]
      _ ≤ ‖A (bX x)‖ * Real.exp (-a_out * (v - edgeV x)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (norm_nonneg _)
  have h_dom_int : IntegrableOn (fun v : ℝ => ‖A (bX x)‖ * Real.exp (-a_out * (v - edgeV x)))
      (Ioi (edgeV x + u₀)) := by
    have heq : (fun v : ℝ => ‖A (bX x)‖ * Real.exp (-a_out * (v - edgeV x))) =
        fun v => (‖A (bX x)‖ * Real.exp (a_out * edgeV x)) * Real.exp (-a_out * v) := by
      ext v
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [heq]
    exact (integrableOn_exp_mul_Ioi (by linarith : -a_out < 0) (edgeV x + u₀)).const_mul _
  have h_eval_out : ∫ v in Ioi (edgeV x + u₀), ‖A (bX x)‖ * Real.exp (-a_out * (v - edgeV x)) =
      ‖A (bX x)‖ * Real.exp (-a_out * u₀) / a_out := by
    have heq : (fun v : ℝ => ‖A (bX x)‖ * Real.exp (-a_out * (v - edgeV x))) =
        fun v => (‖A (bX x)‖ * Real.exp (a_out * edgeV x)) * Real.exp (-a_out * v) := by
      ext v
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [heq, integral_const_mul, integral_Ioi_exp_neg_mul ha_out_pos]
    calc ‖A (bX x)‖ * Real.exp (a_out * edgeV x) * (Real.exp (-a_out * (edgeV x + u₀)) / a_out)
        = ‖A (bX x)‖ * (Real.exp (a_out * edgeV x) * Real.exp (-a_out * (edgeV x + u₀))) / a_out := by
            ring
      _ = ‖A (bX x)‖ * Real.exp (-a_out * u₀) / a_out := by
            rw [← Real.exp_add]
            congr 3
            ring
  have h_norm_le : ‖outerPosIntegral Φ₀ x n δ C₃ M M' A‖ ≤
      ‖A (bX x)‖ * Real.exp (-a_out * u₀) / a_out := by
    have h1 : ‖outerPosIntegral Φ₀ x n δ C₃ M M' A‖ ≤
        ∫ v in Ioi (edgeV x + u₀),
          ‖saddleIntegrand Φ₀ x n A ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))‖ :=
      norm_integral_le_integral_norm _
    have h2 : ∫ v in Ioi (edgeV x + u₀),
          ‖saddleIntegrand Φ₀ x n A ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ))‖ ≤
        ∫ v in Ioi (edgeV x + u₀), ‖A (bX x)‖ * Real.exp (-a_out * (v - edgeV x)) :=
      setIntegral_mono_on hf_lower_int.integrableOn.norm h_dom_int measurableSet_Ioi h_re_bd
    exact (h1.trans h2).trans_eq h_eval_out
  have h_exp_cmp : c_out * (n * mX x ^ 3) ≤ a_out * u₀ := by
    have h1 : u₀ ^ 2 * alphaX x = (d ^ 2 / 2) * (mX x ^ 2 * alphaX x) := by
      dsimp [u₀, saddleU₀, ℓ, saddleLength]
      have hs : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
      rw [div_pow, hs]
      ring
    have h2 : mX x ^ 3 ≤ mX x ^ 2 * alphaX x :=
      (show mX x ^ 3 = mX x ^ 2 * mX x by ring) ▸ mul_le_mul_of_nonneg_left (mX_le_alphaX x) (sq_nonneg _)
    calc c_out * (n * mX x ^ 3)
        = (1 / 2 * n) * ((d ^ 2 / 2) * mX x ^ 3) := by dsimp [c_out]; ring
      _ ≤ (1 / 2 * n) * (u₀ ^ 2 * alphaX x) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc (d ^ 2 / 2) * mX x ^ 3 ≤ (d ^ 2 / 2) * (mX x ^ 2 * alphaX x) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
            _ = u₀ ^ 2 * alphaX x := h1.symm
      _ = a_out * u₀ := by dsimp [a_out]; ring
  have h_pref : 1 / a_out ≤ √(2 * Real.pi / (n * alphaX x)) * C_out := by
    have h_nm1 : 1 ≤ n * mX x ^ 3 := (le_max_left _ _).trans hnm
    have h_sqrt_lb : 1 ≤ √(n * mX x ^ 3) := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt h_nm1
    have h_ux_lb : d / √2 ≤ u₀ * √(n * alphaX x) := by
      have h1 : √(n * mX x ^ 3) ≤ mX x * √(n * alphaX x) := by
        rw [show mX x ^ 3 = mX x ^ 2 * mX x by ring, mul_comm n (mX x ^ 2 * mX x), mul_assoc,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm_pos.le]
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (by nlinarith [hn.le, mX_le_alphaX x])) hm_pos.le
      calc d / √2 = (d / √2) * 1 := (mul_one _).symm
        _ ≤ (d / √2) * √(n * mX x ^ 3) := by gcongr
        _ ≤ (d / √2) * (mX x * √(n * alphaX x)) := by gcongr
        _ = u₀ * √(n * alphaX x) := by dsimp [u₀, saddleU₀, ℓ, saddleLength]; ring
    have hs2 : 0 < √2 := Real.sqrt_pos.mpr zero_lt_two
    have h_main : 1 / a_out = √(2 * Real.pi / (n * alphaX x)) *
        (2 / (√(2 * Real.pi) * (u₀ * √(n * alphaX x)))) := by
      have hna : 0 < √(n * alphaX x) := Real.sqrt_pos.mpr (by positivity)
      have h2p : 0 < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
      rw [Real.sqrt_div (by positivity)]
      dsimp [a_out]
      field_simp [hna.ne', h2p.ne']
      have hsq1 : √(n * alphaX x) ^ 2 = n * alphaX x := Real.sq_sqrt (by positivity)
      have hsq2 : √(2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
      nlinarith
    rw [h_main]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    calc 2 / (√(2 * Real.pi) * (u₀ * √(n * alphaX x)))
        ≤ 2 / (√(2 * Real.pi) * (d / √2)) := by
          refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
          exact mul_le_mul_of_nonneg_left h_ux_lb (Real.sqrt_nonneg _)
      _ = 2 / (√Real.pi * d) := by
          rw [Real.sqrt_mul zero_le_two]
          have hs : √2 ≠ 0 := hs2.ne'
          field_simp [hs]
      _ = C_out := rfl
  calc ‖outerPosIntegral Φ₀ x n δ C₃ M M' A‖
      ≤ ‖A (bX x)‖ * (1 / a_out) * Real.exp (-a_out * u₀) := by
          have h1 : ‖A (bX x)‖ * Real.exp (-a_out * u₀) / a_out =
              ‖A (bX x)‖ * (1 / a_out) * Real.exp (-a_out * u₀) := by ring
          exact h1 ▸ h_norm_le
    _ ≤ ‖A (bX x)‖ * (√(2 * Real.pi / (n * alphaX x)) * C_out) *
          Real.exp (-c_out * (n * mX x ^ 3)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h_pref (norm_nonneg _))
            (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)
    _ = ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) *
          (C_out * Real.exp (-c_out * (n * mX x ^ 3))) := by ring

/-- **(SD.8)** Combined exponential bound on the positive middle and outer contour integrals,
relative to `|A(b_x)| √(2π / (n α_x))`. Constants `c, C, N₀` depend only on `δ, C₃, M, M'`. -/
lemma middle_outer_pos_bound {δ C₃ M M' : ℝ} (hδ : 0 < δ) (hC₃ : 0 ≤ C₃)
    (hM : 0 ≤ M) :
    ∃ c_mo C_mo N_mo : ℝ, 0 < c_mo ∧ 0 ≤ C_mo ∧ 1 ≤ N_mo ∧
      ∀ {C₄ : ℝ} {Φ₀ : ℂ → ℂ} {x n : ℝ} {A : ℂ → ℂ},
        xiStar < x → 0 < n →
        N_mo ≤ n * mX x ^ 3 →
        EdgePhaseData δ C₃ C₄ Φ₀ →
        TwoSaddleAmplitude Φ₀ x n δ M M' A →
        ‖middlePosIntegral Φ₀ x n δ C₃ M M' A + outerPosIntegral Φ₀ x n δ C₃ M M' A‖ ≤
          ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) *
            (C_mo * Real.exp (-c_mo * (n * mX x ^ 3))) := by
  obtain ⟨c_mid, C_mid, hc_mid, hC_mid, hmid⟩ := middlePosIntegral_bound hδ hC₃ hM (M' := M')
  obtain ⟨c_out, C_out, hc_out, hC_out, hout⟩ := outerPosIntegral_bound hδ hC₃ hM (M' := M')
  refine ⟨min c_mid c_out, C_mid + C_out, max 1 (8 * √2 / saddleScaleD δ C₃ M M' ^ 2),
    lt_min hc_mid hc_out, add_nonneg hC_mid hC_out, le_max_left _ _,
    fun {C₄ Φ₀ x n A} hx hn hnm hΦ hA => ?_⟩
  have h1 := hmid hx hn hnm hΦ hA
  have h2 := hout hx hn hnm hΦ hA
  have hexp_pos : 0 ≤ n * mX x ^ 3 := by
    have := (mX_pos hx).le
    positivity
  have he1 : Real.exp (-c_mid * (n * mX x ^ 3)) ≤
      Real.exp (-min c_mid c_out * (n * mX x ^ 3)) := by
    refine Real.exp_le_exp.mpr ?_
    have : min c_mid c_out ≤ c_mid := min_le_left _ _
    nlinarith
  have he2 : Real.exp (-c_out * (n * mX x ^ 3)) ≤
      Real.exp (-min c_mid c_out * (n * mX x ^ 3)) := by
    refine Real.exp_le_exp.mpr ?_
    have : min c_mid c_out ≤ c_out := min_le_right _ _
    nlinarith
  have htri : ‖middlePosIntegral Φ₀ x n δ C₃ M M' A + outerPosIntegral Φ₀ x n δ C₃ M M' A‖ ≤
      ‖middlePosIntegral Φ₀ x n δ C₃ M M' A‖ + ‖outerPosIntegral Φ₀ x n δ C₃ M M' A‖ :=
    norm_add_le _ _
  have hpi := Real.pi_pos
  have ha_pos := alphaX_pos hx
  have hpref_nn : 0 ≤ ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) := by positivity
  calc ‖middlePosIntegral Φ₀ x n δ C₃ M M' A + outerPosIntegral Φ₀ x n δ C₃ M M' A‖
      ≤ ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (C_mid * Real.exp (-c_mid * (n * mX x ^ 3))) +
        ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (C_out * Real.exp (-c_out * (n * mX x ^ 3))) :=
          htri.trans (add_le_add h1 h2)
    _ ≤ ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) *
          (C_mid * Real.exp (-min c_mid c_out * (n * mX x ^ 3))) +
        ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) *
          (C_out * Real.exp (-min c_mid c_out * (n * mX x ^ 3))) := by
          refine add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he1 hC_mid) hpref_nn)
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he2 hC_out) hpref_nn)
    _ = ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) *
          ((C_mid + C_out) * Real.exp (-min c_mid c_out * (n * mX x ^ 3))) := by ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Saddle.edgeIntegral_eq_two_mul_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Saddle.edgeIntegral_eq_two_mul_re_pos

/-- info: 'FormalResearch.ModularBootstrap.Upper.Saddle.middle_outer_pos_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Saddle.middle_outer_pos_bound

end FormalResearch.ModularBootstrap.Upper.Saddle
