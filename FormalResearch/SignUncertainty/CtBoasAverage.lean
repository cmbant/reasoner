module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasWindow
public import FormalResearch.SignUncertainty.CtBoasFar

/-!
# `ct:boas` Step 5: Gaussian averaging over the frozen frequency (phase-free)

`constant_terms_lower.tex`, proof of `ct:boas`, Step 5 ("Averaging over `L₀` on the whole line, and the freezing
error").  For the centred Gaussian `G = gaussK W` of `CtBoasWindow`:

* `integral_gaussK_sq` (`∫ u² G = W²`), `integral_gaussK_abs_le` (`∫ |u| G ≤ W`), the moment bounds `k = 1, 2`;
* `block_average`: for a weight `ω ≥ 0` (the TeX's `Ω_near χ_j`), a phase factor `F` (`1 - 2 sin X`) and a frozen kernel
  `T L₀` (`1 + 2cos(ω₀(L - L₀) + φ₀)`), if the windowed frozen integrals `P(L₀) = ∫ G(L-L₀) h T_{L₀}` are `≥ -Pb`
  wherever `ω(L₀) > 0` (`ct:P-lb`) and the freezing error `D = ω F - ω(L₀) T_{L₀}` satisfies
  `|D| ≤ 1_Q(L)(A|u| + B u²) + Kd u²` (`u = L - L₀`), then
  `∫ ω h F ≥ -Pb ∫ω - (∫_Q |h|)(A W + B W²) - Kd W² ∫|h|`.
  The far pairs `|u| > δ` of the TeX are absorbed in the `Kd u²` term (`Kd = 6/δ²`, a Chebyshev tail instead of the
  exponential Gaussian tail; the polynomial bound suffices in the regime of the TeX).

**Proved** (real analysis only; no Hankel input).
-/

@[expose] public section

open MeasureTheory Set ProbabilityTheory
open scoped Real NNReal

namespace FormalResearch.SignUncertainty.CtBoasWindow

/-- `∫ u² G_W(u) du = W²`. -/
theorem integral_gaussK_sq {W : ℝ} (hW : 0 < W) : ∫ u, u ^ 2 * gaussK W u = W ^ 2 := by
  have hv : (⟨W ^ 2, by positivity⟩ : ℝ≥0) ≠ 0 := by
    intro h; have := congrArg Subtype.val h; exact (pow_pos hW 2).ne' this
  have h1 := variance_fun_id_gaussianReal (μ := 0) (v := (⟨W ^ 2, by positivity⟩ : ℝ≥0))
  rw [variance_eq_integral measurable_id'.aemeasurable] at h1
  have h0 : ∫ x : ℝ, x ∂gaussianReal 0 (⟨W ^ 2, by positivity⟩ : ℝ≥0) = 0 := integral_id_gaussianReal
  rw [h0] at h1
  simp only [sub_zero] at h1
  rw [integral_gaussianReal_eq_integral_smul hv] at h1
  replace h1 : ∫ x : ℝ, gaussianPDFReal 0 (⟨W ^ 2, by positivity⟩ : ℝ≥0) x • x ^ 2 = W ^ 2 := h1
  rw [← h1]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [gaussianPDFReal, gaussK, smul_eq_mul, sub_zero]
  have : √(2 * π * W ^ 2) = √(2 * π) * W := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hW.le]
  change u ^ 2 * (Real.exp (-(1 / (2 * W ^ 2)) * u ^ 2) / (√(2 * π) * W)) =
    (√(2 * π * W ^ 2))⁻¹ * Real.exp (-u ^ 2 / (2 * W ^ 2)) * u ^ 2
  rw [this]; field_simp

lemma integrable_gaussK_sq {W : ℝ} (hW : 0 < W) : Integrable fun u => u ^ 2 * gaussK W u := by
  by_contra hn
  have := integral_undef hn
  rw [integral_gaussK_sq hW] at this
  exact (pow_pos hW 2).ne' this

lemma integrable_gaussK_abs {W : ℝ} (hW : 0 < W) : Integrable fun u => |u| * gaussK W u := by
  have h1 : Integrable fun u => (u ^ 2 + W ^ 2) / (2 * W) * gaussK W u := by
    have := ((integrable_gaussK_sq hW).add ((integrable_gaussK hW).const_mul (W ^ 2))).div_const (2 * W)
    refine this.congr (ae_of_all _ fun u => ?_)
    simp only [Pi.add_apply]; ring
  refine h1.mono' (by
      have : Continuous fun u => |u| * gaussK W u := (continuous_abs).mul (continuous_gaussK W)
      exact this.aestronglyMeasurable) (ae_of_all _ fun u => ?_)
  have hg := gaussK_nonneg hW u
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hg)]
  refine mul_le_mul_of_nonneg_right ?_ hg
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (|u| - W), sq_abs u]

/-- `∫ |u| G_W(u) du ≤ W`. -/
theorem integral_gaussK_abs_le {W : ℝ} (hW : 0 < W) : ∫ u, |u| * gaussK W u ≤ W := by
  have h1 : Integrable fun u => (u ^ 2 + W ^ 2) / (2 * W) * gaussK W u := by
    have := ((integrable_gaussK_sq hW).add ((integrable_gaussK hW).const_mul (W ^ 2))).div_const (2 * W)
    refine this.congr (ae_of_all _ fun u => ?_)
    simp only [Pi.add_apply]; ring
  have h2 : ∫ u, (u ^ 2 + W ^ 2) / (2 * W) * gaussK W u = W := by
    have : ∀ u, (u ^ 2 + W ^ 2) / (2 * W) * gaussK W u =
        (u ^ 2 * gaussK W u + W ^ 2 * gaussK W u) / (2 * W) := fun u => by ring
    simp_rw [this]
    rw [integral_div, integral_add (integrable_gaussK_sq hW) ((integrable_gaussK hW).const_mul _),
      integral_gaussK_sq hW, integral_const_mul, integral_gaussK hW]
    field_simp; ring
  refine le_of_le_of_eq (integral_mono (integrable_gaussK_abs hW) h1 fun u => ?_) h2
  have hg := gaussK_nonneg hW u
  refine mul_le_mul_of_nonneg_right ?_ hg
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (|u| - W), sq_abs u]


/-- The Gaussian-weighted bound on the freezing error, integrated against `L₀` at fixed `L`. -/
lemma gauss_moment_poly {W : ℝ} (hW : 0 < W) {A B K : ℝ} (hA : 0 ≤ A) (L : ℝ)
    (Q : Set ℝ) :
    Integrable (fun L0 : ℝ => gaussK W (L - L0) * (Q.indicator (fun L => A * |L - L0| + B * (L - L0) ^ 2) L +
      K * (L - L0) ^ 2)) ∧
    ∫ L0, gaussK W (L - L0) * (Q.indicator (fun L => A * |L - L0| + B * (L - L0) ^ 2) L + K * (L - L0) ^ 2) ≤
      Q.indicator (fun _ => A * W + B * W ^ 2) L + K * W ^ 2 := by
  have e : ∀ L0 : ℝ, gaussK W (L - L0) * (Q.indicator (fun L => A * |L - L0| + B * (L - L0) ^ 2) L +
      K * (L - L0) ^ 2) = (Q.indicator (fun _ => (1 : ℝ)) L) * (A * (fun u => |u| * gaussK W u) (L - L0) +
        B * (fun u => u ^ 2 * gaussK W u) (L - L0)) + K * (fun u => u ^ 2 * gaussK W u) (L - L0) := by
    intro L0
    by_cases hL : L ∈ Q <;> simp [hL, Set.indicator] <;> ring
  simp_rw [e]
  have i1 := (integrable_gaussK_abs hW).comp_sub_left L
  have i2 := (integrable_gaussK_sq hW).comp_sub_left L
  have m1 : ∫ L0, (fun u => |u| * gaussK W u) (L - L0) = ∫ u, |u| * gaussK W u :=
    integral_sub_left_eq_self (fun u => |u| * gaussK W u) volume L
  have m2 : ∫ L0, (fun u => u ^ 2 * gaussK W u) (L - L0) = W ^ 2 := by
    rw [integral_sub_left_eq_self (fun u => u ^ 2 * gaussK W u) volume L]; exact integral_gaussK_sq hW
  have hab := integral_gaussK_abs_le hW
  have ia := (i1.const_mul A).add (i2.const_mul B)
  have ib := (ia.const_mul (Q.indicator (fun _ => (1 : ℝ)) L)).add (i2.const_mul K)
  refine ⟨ib, ?_⟩
  refine (integral_add (ia.const_mul _) (i2.const_mul K)).trans_le ?_
  have h3 : ∫ a, (Q.indicator (fun _ => (1 : ℝ)) L * ((fun t => A * (|L - t| * gaussK W (L - t))) +
      fun t => B * ((L - t) ^ 2 * gaussK W (L - t))) a) =
      Q.indicator (fun _ => (1 : ℝ)) L * (A * (∫ u, |u| * gaussK W u) + B * W ^ 2) := by
    rw [integral_const_mul]
    simp only [Pi.add_apply]
    rw [integral_add (i1.const_mul A) (i2.const_mul B), integral_const_mul, integral_const_mul]
    simp only at m1 m2
    rw [m1, m2]
  have h4 : ∫ a, K * ((L - a) ^ 2 * gaussK W (L - a)) = K * W ^ 2 := by
    rw [integral_const_mul]; simpa using congrArg (K * ·) m2
  rw [h3, h4]
  by_cases hL : L ∈ Q
  · simp only [hL, Set.indicator_of_mem, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hab hA]
  · simp [hL]


/-- **`ct:boas` Step 5, one block (the averaging over `L₀` and the freezing error).**  See the module docstring. -/
theorem block_average
    {W : ℝ} (hW : 0 < W) {h : ℝ → ℝ} (hh : Integrable h)
    {ω F : ℝ → ℝ} {T : ℝ → ℝ → ℝ}
    (hωm : Measurable ω) (hFm : Measurable F) (hTm : Measurable (fun p : ℝ × ℝ => T p.2 p.1))
    (hω0 : ∀ L, 0 ≤ ω L) (hω1 : ∀ L, ω L ≤ 1) (hωi : Integrable ω)
    (hF : ∀ L, |F L| ≤ 3) (hT : ∀ L0 L, |T L0 L| ≤ 3)
    {Pb : ℝ} (hP : ∀ L0, 0 < ω L0 → -Pb ≤ ∫ L, gaussK W (L - L0) * h L * T L0 L)
    {Q : Set ℝ} (hQ : MeasurableSet Q) {A B Kd : ℝ} (hA : 0 ≤ A) (hKd : 0 ≤ Kd)
    (hD : ∀ L L0, |ω L * F L - ω L0 * T L0 L| ≤
      Q.indicator (fun L => A * |L - L0| + B * (L - L0) ^ 2) L + Kd * (L - L0) ^ 2) :
    -(Pb * ∫ L, ω L) - ((∫ L in Q, |h L|) * (A * W + B * W ^ 2) + Kd * W ^ 2 * ∫ L, |h L|) ≤
      ∫ L, ω L * (h L * F L) := by
  set G := gaussK W with hG
  have hG0 : ∀ y, 0 ≤ G y := gaussK_nonneg hW
  have hhm : AEStronglyMeasurable h volume := hh.aestronglyMeasurable
  -- the base function `G(L - L₀)|h(L)|` is integrable on the product
  have hbase : Integrable (fun p : ℝ × ℝ => G (p.1 - p.2) * |h p.1|) (volume.prod volume) := by
    have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => G (p.1 - p.2) * |h p.1|) (volume.prod volume) :=
      ((continuous_gaussK W).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable.mul
        (hh.abs.aestronglyMeasurable.comp_fst)
    rw [integrable_prod_iff hm]
    refine ⟨ae_of_all _ fun L => ?_, ?_⟩
    · have := ((integrable_gaussK hW).comp_sub_left L).const_mul |h L|
      refine this.congr (ae_of_all _ fun L0 => ?_); simp only; ring
    · have : (fun L => ∫ L0, ‖G (L - L0) * |h L|‖) = fun L => |h L| := by
        funext L
        have : ∀ L0, ‖G (L - L0) * |h L|‖ = |h L| * G (L - L0) := fun L0 => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hG0 _) (abs_nonneg _))]; ring
        simp_rw [this]
        rw [integral_const_mul, integral_sub_left_eq_self G volume L, hG, integral_gaussK hW, mul_one]
      simp only [this]
      exact hh.abs
  -- measurability of the pieces
  have hωF : Measurable fun p : ℝ × ℝ => ω p.1 * F p.1 := (hωm.comp measurable_fst).mul (hFm.comp measurable_fst)
  have hΦm : ∀ k : ℝ × ℝ → ℝ, Measurable k → AEStronglyMeasurable (fun p : ℝ × ℝ => G (p.1 - p.2) * h p.1 * k p) (volume.prod volume) := by
    intro k hk
    exact ((((continuous_gaussK W).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable.mul
      (hh.aestronglyMeasurable.comp_fst))).mul hk.aestronglyMeasurable
  set T' : ℝ × ℝ → ℝ := fun p => ω p.2 * T p.2 p.1 with hT'
  have hT'm : Measurable T' := (hωm.comp measurable_snd).mul hTm
  set D : ℝ × ℝ → ℝ := fun p => ω p.1 * F p.1 - T' p with hDdef
  have hDm : Measurable D := hωF.sub hT'm
  have hT'b : ∀ p, |T' p| ≤ 3 := fun p => by
    simp only [hT', abs_mul]
    have := hT p.2 p.1; have h1 : |ω p.2| ≤ 1 := by rw [abs_of_nonneg (hω0 _)]; exact hω1 _
    nlinarith [abs_nonneg (T p.2 p.1), abs_nonneg (ω p.2)]
  have hDb : ∀ p, |D p| ≤ 6 := fun p => by
    simp only [hDdef]
    have h1 : |ω p.1| ≤ 1 := by rw [abs_of_nonneg (hω0 _)]; exact hω1 _
    have h2 : |ω p.1 * F p.1| ≤ 3 := by
      rw [abs_mul]; nlinarith [abs_nonneg (F p.1), abs_nonneg (ω p.1), hF p.1]
    have := abs_sub (ω p.1 * F p.1) (T' p)
    linarith [hT'b p]
  have hint : ∀ (k : ℝ × ℝ → ℝ) (C : ℝ), Measurable k → (∀ p, |k p| ≤ C) →
      Integrable (fun p : ℝ × ℝ => G (p.1 - p.2) * h p.1 * k p) (volume.prod volume) := by
    intro k C hk hkC
    refine (hbase.const_mul C).mono' (hΦm k hk) (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hG0 _)]
    have := hkC p
    calc G (p.1 - p.2) * |h p.1| * |k p| ≤ G (p.1 - p.2) * |h p.1| * C :=
          mul_le_mul_of_nonneg_left this (mul_nonneg (hG0 _) (abs_nonneg _))
      _ = C * (G (p.1 - p.2) * |h p.1|) := by ring
  have iΦ1 := hint T' 3 hT'm hT'b
  have iΦ2 := hint D 6 hDm hDb
  have iΦ := hint (fun p => ω p.1 * F p.1) 3 hωF (fun p => by
    rw [abs_mul]
    have h1 : |ω p.1| ≤ 1 := by rw [abs_of_nonneg (hω0 _)]; exact hω1 _
    nlinarith [abs_nonneg (F p.1), abs_nonneg (ω p.1), hF p.1])
  -- Φ = Φ₁ + Φ₂
  have hsplit : ∀ p : ℝ × ℝ, G (p.1 - p.2) * h p.1 * (ω p.1 * F p.1) =
      G (p.1 - p.2) * h p.1 * T' p + G (p.1 - p.2) * h p.1 * D p := fun p => by
    simp only [hDdef]; ring
  -- left side: ∫ Φ = ∫ ω h F
  have hL : ∫ p : ℝ × ℝ, G (p.1 - p.2) * h p.1 * (ω p.1 * F p.1) ∂(volume.prod volume) =
      ∫ L, ω L * (h L * F L) := by
    rw [integral_prod _ iΦ]
    refine integral_congr_ae (ae_of_all _ fun L => ?_)
    simp only
    have : ∀ L0, G (L - L0) * h L * (ω L * F L) = (ω L * (h L * F L)) * G (L - L0) := fun L0 => by ring
    simp_rw [this]
    rw [integral_const_mul, integral_sub_left_eq_self G volume L, hG, integral_gaussK hW, mul_one]
  -- Φ₁: swap order
  have hΦ1 : ∫ p : ℝ × ℝ, G (p.1 - p.2) * h p.1 * T' p ∂(volume.prod volume) =
      ∫ L0, ω L0 * ∫ L, gaussK W (L - L0) * h L * T L0 L := by
    rw [integral_prod_symm _ iΦ1]
    refine integral_congr_ae (ae_of_all _ fun L0 => ?_)
    simp only [hT']
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun L => ?_)
    ring
  have hΦ1i : Integrable (fun L0 => ω L0 * ∫ L, gaussK W (L - L0) * h L * T L0 L) := by
    have := iΦ1.integral_prod_right
    refine this.congr (ae_of_all _ fun L0 => ?_)
    simp only [hT']
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun L => ?_)
    ring
  have hP' : -(Pb * ∫ L, ω L) ≤ ∫ L0, ω L0 * ∫ L, gaussK W (L - L0) * h L * T L0 L := by
    have h1 : ∫ L0, (-Pb) * ω L0 = -(Pb * ∫ L, ω L) := by rw [integral_const_mul]; ring
    rw [← h1]
    refine integral_mono (hωi.const_mul _) hΦ1i fun L0 => ?_
    by_cases hz : 0 < ω L0
    · have := mul_le_mul_of_nonneg_left (hP L0 hz) (hω0 L0)
      linarith
    · have : ω L0 = 0 := le_antisymm (not_lt.mp hz) (hω0 L0)
      simp [this]
  -- the error term
  have hE : -(∫ L, |h L| * (Q.indicator (fun _ => A * W + B * W ^ 2) L + Kd * W ^ 2)) ≤
      ∫ p : ℝ × ℝ, G (p.1 - p.2) * h p.1 * D p ∂(volume.prod volume) := by
    have hn : Integrable (fun p : ℝ × ℝ => ‖G (p.1 - p.2) * h p.1 * D p‖) (volume.prod volume) := iΦ2.norm
    have h1 := neg_abs_le (∫ p : ℝ × ℝ, G (p.1 - p.2) * h p.1 * D p ∂(volume.prod volume))
    have h2 := norm_integral_le_integral_norm (μ := volume.prod volume)
      (fun p : ℝ × ℝ => G (p.1 - p.2) * h p.1 * D p)
    rw [Real.norm_eq_abs] at h2
    have h3 : ∫ p : ℝ × ℝ, ‖G (p.1 - p.2) * h p.1 * D p‖ ∂(volume.prod volume) ≤
        ∫ L, |h L| * (Q.indicator (fun _ => A * W + B * W ^ 2) L + Kd * W ^ 2) := by
      rw [integral_prod _ hn]
      have hrhs : Integrable (fun L => |h L| * (Q.indicator (fun _ => A * W + B * W ^ 2) L + Kd * W ^ 2)) := by
        have e : ∀ L, |h L| * (Q.indicator (fun _ => A * W + B * W ^ 2) L + Kd * W ^ 2) =
            Q.indicator (fun L => |h L| * (A * W + B * W ^ 2)) L + |h L| * (Kd * W ^ 2) := fun L => by
          by_cases hL : L ∈ Q <;> simp [hL, Set.indicator] <;> ring
        simp_rw [e]
        exact ((hh.abs.mul_const _).indicator hQ).add (hh.abs.mul_const _)
      refine integral_mono_of_nonneg (ae_of_all _ fun L => integral_nonneg fun _ => norm_nonneg _) hrhs
        (ae_of_all _ fun L => ?_)
      obtain ⟨hi, hb⟩ := gauss_moment_poly (W := W) hW (A := A) (B := B) (K := Kd) hA L Q
      have hpt : ∀ L0 : ℝ, ‖G (L - L0) * h L * D (L, L0)‖ ≤
          |h L| * (G (L - L0) * (Q.indicator (fun L => A * |L - L0| + B * (L - L0) ^ 2) L +
            Kd * (L - L0) ^ 2)) := fun L0 => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hG0 _)]
        have := hD L L0
        have e : D (L, L0) = ω L * F L - ω L0 * T L0 L := rfl
        rw [e]
        calc G (L - L0) * |h L| * |ω L * F L - ω L0 * T L0 L| ≤
            G (L - L0) * |h L| * (Q.indicator (fun L => A * |L - L0| + B * (L - L0) ^ 2) L +
              Kd * (L - L0) ^ 2) := mul_le_mul_of_nonneg_left this (mul_nonneg (hG0 _) (abs_nonneg _))
          _ = _ := by ring
      calc ∫ L0, ‖G (L - L0) * h L * D (L, L0)‖ ≤
          ∫ L0, |h L| * (G (L - L0) * (Q.indicator (fun L => A * |L - L0| + B * (L - L0) ^ 2) L +
            Kd * (L - L0) ^ 2)) :=
            integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hi.const_mul _)
              (ae_of_all _ hpt)
        _ = |h L| * ∫ L0, G (L - L0) * (Q.indicator (fun L => A * |L - L0| + B * (L - L0) ^ 2) L +
            Kd * (L - L0) ^ 2) := integral_const_mul _ _
        _ ≤ |h L| * (Q.indicator (fun _ => A * W + B * W ^ 2) L + Kd * W ^ 2) :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    linarith
  have hfin : ∫ L, |h L| * (Q.indicator (fun _ => A * W + B * W ^ 2) L + Kd * W ^ 2) =
      (∫ L in Q, |h L|) * (A * W + B * W ^ 2) + Kd * W ^ 2 * ∫ L, |h L| := by
    have e : ∀ L, |h L| * (Q.indicator (fun _ => A * W + B * W ^ 2) L + Kd * W ^ 2) =
        Q.indicator (fun L => |h L| * (A * W + B * W ^ 2)) L + |h L| * (Kd * W ^ 2) := fun L => by
      by_cases hL : L ∈ Q <;> simp [hL, Set.indicator] <;> ring
    simp_rw [e]
    rw [integral_add ((hh.abs.mul_const _).indicator hQ) (hh.abs.mul_const _),
      integral_indicator hQ, integral_mul_const, integral_mul_const]
    ring
  have hsum : ∫ p : ℝ × ℝ, G (p.1 - p.2) * h p.1 * (ω p.1 * F p.1) ∂(volume.prod volume) =
      (∫ p : ℝ × ℝ, G (p.1 - p.2) * h p.1 * T' p ∂(volume.prod volume)) +
      ∫ p : ℝ × ℝ, G (p.1 - p.2) * h p.1 * D p ∂(volume.prod volume) := by
    rw [← integral_add iΦ1 iΦ2]
    exact integral_congr_ae (ae_of_all _ hsplit)
  rw [← hL, hsum, hΦ1]
  linarith

/-- info: 'FormalResearch.SignUncertainty.CtBoasWindow.block_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms block_average

/-- info: 'FormalResearch.SignUncertainty.CtBoasWindow.integral_gaussK_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_gaussK_abs_le

end FormalResearch.SignUncertainty.CtBoasWindow
