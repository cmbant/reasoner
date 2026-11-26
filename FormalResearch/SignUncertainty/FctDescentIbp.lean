/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Two integrations by parts along the vertical ray (`fct:splitting` (1), proof of `(fct:F-38-bnd)`)

Paper I (`constant_terms_five.tex`), proof of Lemma FCT.6 (1): along `t = ζ + is`, `K₀A_ε = c⁻¹ ∂_t(e^{cΦ}) W` and two integrations by parts give
`cK₀Ψ_c(ζ) = e^{cΦ(ζ)}(W(ζ) - W'(ζ)/(cΦ'(ζ))) - c⁻¹ ∫ e^{cΦ}(W'/Φ')' dt`.

This file is the real-variable core, free of any complex analysis: for `e' = i c p e` (`e = e^{cΦ}`, `p = Φ'`), `‖e‖ ≤ ‖e(0)‖` and `w, w', w''`
of size `B e^{-3s}` (the paper's `C(1+s)^C e^{-πs}` is below `C' e^{-3s}`), `|p| ≥ q`, `|p'| ≤ D`:

`‖∫₀^∞ p e w ds - (i/c) e(0) w(0)‖ ≤ ‖e(0)‖ B (1/q + (1/q + D/q²)/3) / c²`   (`fctRay_ibp_bound`).

Class: proved.
-/
@[expose] public section

open Set Filter Topology MeasureTheory Complex

namespace FormalResearch.SignUncertainty

/-- A function continuous on `(0, ∞)` and bounded by `K e^{-a s}` there is integrable on `(0, ∞)` (`a > 0`). -/
lemma integrableOn_of_exp_bound {f : ℝ → ℂ} {K a : ℝ} (ha : 0 < a) (hf : ContinuousOn f (Ioi 0))
    (hb : ∀ s : ℝ, 0 < s → ‖f s‖ ≤ K * Real.exp (-a * s)) : IntegrableOn f (Ioi 0) := by
  have hg : IntegrableOn (fun s : ℝ => K * Real.exp (-a * s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 ha).const_mul K
  refine Integrable.mono' hg (hf.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs using hb s hs

/-- `∫₀^∞ e^{-3s} ds = 1/3`. -/
lemma integral_exp_neg_three : ∫ s : ℝ in Ioi 0, Real.exp (-3 * s) = 1 / 3 := by
  rw [integral_exp_mul_Ioi (by norm_num : (-3 : ℝ) < 0)]
  norm_num

/-- `e^{-3s} → 0`. -/
lemma tendsto_exp_neg_three : Tendsto (fun s : ℝ => Real.exp (-3 * s)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-3 : ℝ) < 0))

/-- One integration by parts on `(0, ∞)` for complex functions with `u v → 0` at `∞`. -/
lemma ibp_Ioi {u v u' v' : ℝ → ℂ} (hu : ∀ s, 0 ≤ s → HasDerivAt u (u' s) s)
    (hv : ∀ s, 0 ≤ s → HasDerivAt v (v' s) s)
    (h1 : IntegrableOn (fun s => u s * v' s) (Ioi 0)) (h2 : IntegrableOn (fun s => u' s * v s) (Ioi 0))
    (h0 : Tendsto (fun s => u s * v s) atTop (𝓝 0)) :
    ∫ s in Ioi 0, u s * v' s = -(u 0 * v 0) - ∫ s in Ioi 0, u' s * v s := by
  have hcont : ContinuousAt (fun s => u s * v s) 0 := (hu 0 le_rfl).continuousAt.mul (hv 0 le_rfl).continuousAt
  have := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (u := u) (v := v) (u' := u') (v' := v')
    (a' := u 0 * v 0) (b' := 0) (fun s hs => hu s (le_of_lt hs)) (fun s hs => hv s (le_of_lt hs)) h1 h2
    (hcont.tendsto.mono_left nhdsWithin_le_nhds) h0
  rw [this]; ring

/-- **The identity of the two integrations by parts**: for `e' = i c p e`, `p ≠ 0` and the decay of `e w`, `e w'/p`,
`∫₀^∞ p e w = (i/c) e(0) w(0) - e(0) w'(0)/(c² p(0)) - c⁻² ∫₀^∞ e (w''/p - w' p'/p²)`. -/
theorem fctRay_ibp_eq {c B q D : ℝ} (hc : 0 < c) (hq : 0 < q) (hD : 0 ≤ D) {e w w1 w2 p p1 : ℝ → ℂ}
    (he : ∀ s, 0 ≤ s → HasDerivAt e (I * c * p s * e s) s)
    (hw : ∀ s, 0 ≤ s → HasDerivAt w (w1 s) s) (hw1 : ∀ s, 0 ≤ s → HasDerivAt w1 (w2 s) s)
    (hp : ∀ s, 0 ≤ s → HasDerivAt p (p1 s) s)
    (hpq : ∀ s, 0 ≤ s → q ≤ ‖p s‖) (hp1 : ∀ s, 0 ≤ s → ‖p1 s‖ ≤ D)
    (he0 : ∀ s, 0 ≤ s → ‖e s‖ ≤ ‖e 0‖)
    (hb0 : ∀ s, 0 ≤ s → ‖w s‖ ≤ B * Real.exp (-3 * s)) (hb1 : ∀ s, 0 ≤ s → ‖w1 s‖ ≤ B * Real.exp (-3 * s))
    (hb2 : ∀ s, 0 ≤ s → ‖w2 s‖ ≤ B * Real.exp (-3 * s))
    (cw2 : ContinuousOn w2 (Ioi 0)) (cp1 : ContinuousOn p1 (Ioi 0)) :
    (∫ s in Ioi 0, p s * e s * w s) =
      (I / c) * e 0 * w 0 - e 0 * w1 0 / (c ^ 2 * p 0) -
        (1 / c ^ 2 : ℂ) * ∫ s in Ioi 0, e s * (w2 s / p s - w1 s * p1 s / p s ^ 2) := by
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hB : 0 ≤ B := by
    have := hb0 0 le_rfl
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have hpne : ∀ s, 0 ≤ s → p s ≠ 0 := fun s hs h => by
    have := hpq s hs; rw [h, norm_zero] at this; linarith
  have hIc : I * (c : ℂ) ≠ 0 := mul_ne_zero I_ne_zero hcc
  have hIcp : ∀ s, 0 ≤ s → I * (c : ℂ) * p s ≠ 0 := fun s hs => mul_ne_zero hIc (hpne s hs)
  have cont : ∀ {f f' : ℝ → ℂ}, (∀ s, 0 ≤ s → HasDerivAt f (f' s) s) → ContinuousOn f (Ioi 0) := fun hf =>
    fun s hs => (hf s (le_of_lt hs)).continuousAt.continuousWithinAt
  have ce := cont he
  have cw := cont hw
  have cw1 := cont hw1
  have cp := cont hp
  have cpi : ContinuousOn (fun s => (p s)⁻¹) (Ioi 0) := cp.inv₀ fun s hs => hpne s (le_of_lt hs)
  have hE0 : 0 ≤ ‖e 0‖ := norm_nonneg _
  -- growth of `p`
  have hpgrow : ∀ s, 0 ≤ s → ‖p s‖ ≤ (‖p 0‖ + D) * Real.exp s := by
    intro s hs
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := p) (f' := p1) (C := D) (s := Ici 0)
      (fun x hx => (hp x hx).hasDerivWithinAt) (fun x hx => hp1 x hx) (convex_Ici 0) (x := 0) (y := s)
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs)
    have h1 : ‖p s‖ ≤ ‖p 0‖ + D * s := by
      have := norm_sub_norm_le (p s) (p 0)
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs] at hmv
      linarith
    have h2 : s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
    have h3 : (1 : ℝ) ≤ Real.exp s := Real.one_le_exp hs
    nlinarith [norm_nonneg (p 0)]
  -- decay bounds
  have bew : ∀ s, 0 ≤ s → ‖e s * w s‖ ≤ ‖e 0‖ * B * Real.exp (-3 * s) := fun s hs => by
    rw [norm_mul]
    calc ‖e s‖ * ‖w s‖ ≤ ‖e 0‖ * (B * Real.exp (-3 * s)) :=
          mul_le_mul (he0 s hs) (hb0 s hs) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have bew1 : ∀ s, 0 ≤ s → ‖e s * w1 s‖ ≤ ‖e 0‖ * B * Real.exp (-3 * s) := fun s hs => by
    rw [norm_mul]
    calc ‖e s‖ * ‖w1 s‖ ≤ ‖e 0‖ * (B * Real.exp (-3 * s)) :=
          mul_le_mul (he0 s hs) (hb1 s hs) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have tend : ∀ {K : ℝ}, Tendsto (fun s : ℝ => K * Real.exp (-3 * s)) atTop (𝓝 0) := fun {K} => by
    simpa using tendsto_exp_neg_three.const_mul K
  -- step 1: `u = e`, `v = w`
  have hI1 : IntegrableOn (fun s => e s * w1 s) (Ioi 0) :=
    integrableOn_of_exp_bound (by norm_num : (0 : ℝ) < 3) (ce.mul cw1) fun s hs => bew1 s hs.le
  have hpew : ∀ s, 0 ≤ s → ‖(I * c * p s * e s) * w s‖ ≤
      (c * (‖p 0‖ + D) * (‖e 0‖ * B)) * Real.exp (-2 * s) := fun s hs => by
    have h1 : ‖(I * (c : ℂ) * p s * e s) * w s‖ = c * ‖p s‖ * ‖e s * w s‖ := by
      rw [show (I * (c : ℂ) * p s * e s) * w s = (I * (c : ℂ) * p s) * (e s * w s) by ring, norm_mul, norm_mul,
        norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    rw [h1]
    have h2 := hpgrow s hs
    have h3 := bew s hs
    have h4 : Real.exp (-3 * s) * Real.exp s = Real.exp (-2 * s) := by rw [← Real.exp_add]; ring_nf
    calc c * ‖p s‖ * ‖e s * w s‖ ≤ c * ((‖p 0‖ + D) * Real.exp s) * (‖e 0‖ * B * Real.exp (-3 * s)) := by
          gcongr
      _ = _ := by rw [← h4]; ring
  have hI2 : IntegrableOn (fun s => (I * c * p s * e s) * w s) (Ioi 0) :=
    integrableOn_of_exp_bound (by norm_num : (0 : ℝ) < 2) (((continuousOn_const.mul cp).mul ce).mul cw)
      fun s hs => hpew s hs.le
  have hS1 := ibp_Ioi (u := e) (v := w) (u' := fun s => I * c * p s * e s) (v' := w1) he hw hI1 hI2
    (squeeze_zero_norm' (by
      filter_upwards [Ici_mem_atTop (0 : ℝ)] with s hs using bew s hs) tend)
  -- step 2: `u = e`, `v = w1 / (i c p)`
  set v : ℝ → ℂ := fun s => w1 s / (I * c * p s) with hv
  set v' : ℝ → ℂ := fun s => (w2 s / p s - w1 s * p1 s / p s ^ 2) / (I * c) with hv'
  have hvd : ∀ s, 0 ≤ s → HasDerivAt v (v' s) s := fun s hs => by
    have := (hw1 s hs).div ((hp s hs).const_mul (I * (c : ℂ))) (hIcp s hs)
    refine this.congr_deriv ?_
    have := hpne s hs
    simp only [hv']
    field_simp
  have hvb : ∀ s, 0 ≤ s → ‖v s‖ ≤ B / (c * q) * Real.exp (-3 * s) := fun s hs => by
    have hps : 0 < ‖p s‖ := lt_of_lt_of_le hq (hpq s hs)
    simp only [hv, norm_div, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    rw [div_le_iff₀ (mul_pos hc hps)]
    have h1 : B / (c * q) * Real.exp (-3 * s) * (c * ‖p s‖) = B * Real.exp (-3 * s) * (‖p s‖ / q) := by
      field_simp
    rw [h1]
    refine (hb1 s hs).trans ?_
    have : 1 ≤ ‖p s‖ / q := by rw [le_div_iff₀ hq]; linarith [hpq s hs]
    nlinarith [mul_nonneg hB (Real.exp_pos (-3 * s)).le]
  have hv'b : ∀ s, 0 ≤ s → ‖v' s‖ ≤ B * (1 / q + D / q ^ 2) / c * Real.exp (-3 * s) := fun s hs => by
    have hps : 0 < ‖p s‖ := lt_of_lt_of_le hq (hpq s hs)
    have hex := Real.exp_pos (-3 * s)
    have t1 : ‖w2 s / p s‖ ≤ B * Real.exp (-3 * s) / q := by
      rw [norm_div]
      calc ‖w2 s‖ / ‖p s‖ ≤ ‖w2 s‖ / q := by gcongr; exact hpq s hs
        _ ≤ _ := by gcongr; exact hb2 s hs
    have t2 : ‖w1 s * p1 s / p s ^ 2‖ ≤ B * Real.exp (-3 * s) * D / q ^ 2 := by
      rw [norm_div, norm_mul, norm_pow]
      calc ‖w1 s‖ * ‖p1 s‖ / ‖p s‖ ^ 2 ≤ (B * Real.exp (-3 * s)) * D / q ^ 2 := by
            have := hpq s hs
            have := hb1 s hs
            have := hp1 s hs
            gcongr
        _ = _ := rfl
    simp only [hv', norm_div, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    rw [div_le_iff₀ hc]
    have := norm_sub_le (w2 s / p s) (w1 s * p1 s / p s ^ 2)
    have e1 : B * (1 / q + D / q ^ 2) / c * Real.exp (-3 * s) * c = B * Real.exp (-3 * s) / q + B * Real.exp (-3 * s) * D / q ^ 2 := by
      field_simp
    rw [e1]; linarith
  have hKv : ∀ s, 0 ≤ s → ‖e s * v' s‖ ≤ ‖e 0‖ * (B * (1 / q + D / q ^ 2) / c) * Real.exp (-3 * s) := fun s hs => by
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (he0 s hs) (hv'b s hs) (norm_nonneg _) hE0
  have cv' : ContinuousOn v' (Ioi 0) := by
    have : ContinuousOn (fun s => (w2 s * (p s)⁻¹ - w1 s * p1 s * ((p s)⁻¹) ^ 2) / (I * (c : ℂ))) (Ioi 0) :=
      ((cw2.mul cpi).sub ((cw1.mul cp1).mul (cpi.pow 2))).div_const _
    refine this.congr fun s hs => ?_
    simp only [hv']
    simp [div_eq_mul_inv]
  have hI3 : IntegrableOn (fun s => e s * v' s) (Ioi 0) :=
    integrableOn_of_exp_bound (by norm_num : (0 : ℝ) < 3) (ce.mul cv') fun s hs => hKv s hs.le
  have huv : ∀ s, 0 ≤ s → (I * c * p s * e s) * v s = e s * w1 s := fun s hs => by
    have := hIcp s hs
    have := hpne s hs
    simp only [hv]; field_simp
  have hI4 : IntegrableOn (fun s => (I * c * p s * e s) * v s) (Ioi 0) :=
    hI1.congr_fun (fun s hs => (huv s (le_of_lt hs)).symm) measurableSet_Ioi
  have hS2 := ibp_Ioi (u := e) (v := v) (u' := fun s => I * c * p s * e s) (v' := v') he hvd hI3 hI4
    (squeeze_zero_norm' (by
      filter_upwards [Ici_mem_atTop (0 : ℝ)] with s hs
      rw [norm_mul]
      calc ‖e s‖ * ‖v s‖ ≤ ‖e 0‖ * (B / (c * q) * Real.exp (-3 * s)) :=
            mul_le_mul (he0 s hs) (hvb s hs) (norm_nonneg _) hE0
        _ = ‖e 0‖ * (B / (c * q)) * Real.exp (-3 * s) := by ring) tend)
  -- assemble
  have hint1 : (∫ s in Ioi 0, (I * c * p s * e s) * w s) = I * c * ∫ s in Ioi 0, p s * e s * w s := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
  have hint2 : (∫ s in Ioi 0, (I * c * p s * e s) * v s) = ∫ s in Ioi 0, e s * w1 s :=
    setIntegral_congr_fun measurableSet_Ioi fun s hs => huv s (le_of_lt hs)
  have hint3 : (∫ s in Ioi 0, e s * v' s) =
      (1 / (I * c)) * ∫ s in Ioi 0, e s * (w2 s / p s - w1 s * p1 s / p s ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [hv']; ring
  rw [hint1] at hS1
  rw [hint2, hint3] at hS2
  have hp0 := hpne 0 le_rfl
  have hv0 : v 0 = w1 0 / (I * c * p 0) := rfl
  rw [hv0] at hS2
  set J := ∫ s in Ioi 0, p s * e s * w s
  set Q := ∫ s in Ioi 0, e s * (w2 s / p s - w1 s * p1 s / p s ^ 2)
  set X := ∫ s in Ioi 0, e s * w1 s
  have hJ : I * c * J = -(e 0 * w 0) - X := by linear_combination hS1
  have hX : X = -(e 0 * (w1 0 / (I * c * p 0))) - (1 / (I * c)) * Q := by
    linear_combination hS2
  have hI2 : (I : ℂ) ^ 2 = -1 := I_sq
  have : J = (-(e 0 * w 0) - X) / (I * c) := by field_simp; linear_combination hJ
  rw [this, hX]
  field_simp
  linear_combination (-(e 0 * w 0 * I * c * p 0) + e 0 * w1 0 + p 0 * Q) * hI2

/-- **Bound for the two integrations by parts** (`fct:splitting` (1)): `‖∫₀^∞ p e w - (i/c) e(0) w(0)‖ ≤ ‖e(0)‖ B (1/q + (1/q + D/q²)/3) / c²`. -/
theorem fctRay_ibp_bound {c B q D : ℝ} (hc : 0 < c) (hq : 0 < q) (hD : 0 ≤ D) {e w w1 w2 p p1 : ℝ → ℂ}
    (he : ∀ s, 0 ≤ s → HasDerivAt e (I * c * p s * e s) s)
    (hw : ∀ s, 0 ≤ s → HasDerivAt w (w1 s) s) (hw1 : ∀ s, 0 ≤ s → HasDerivAt w1 (w2 s) s)
    (hp : ∀ s, 0 ≤ s → HasDerivAt p (p1 s) s)
    (hpq : ∀ s, 0 ≤ s → q ≤ ‖p s‖) (hp1 : ∀ s, 0 ≤ s → ‖p1 s‖ ≤ D)
    (he0 : ∀ s, 0 ≤ s → ‖e s‖ ≤ ‖e 0‖)
    (hb0 : ∀ s, 0 ≤ s → ‖w s‖ ≤ B * Real.exp (-3 * s)) (hb1 : ∀ s, 0 ≤ s → ‖w1 s‖ ≤ B * Real.exp (-3 * s))
    (hb2 : ∀ s, 0 ≤ s → ‖w2 s‖ ≤ B * Real.exp (-3 * s))
    (cw2 : ContinuousOn w2 (Ioi 0)) (cp1 : ContinuousOn p1 (Ioi 0)) :
    ‖(∫ s in Ioi 0, p s * e s * w s) - (I / c) * e 0 * w 0‖ ≤
      ‖e 0‖ * B * (1 / q + (1 / q + D / q ^ 2) / 3) / c ^ 2 := by
  rw [fctRay_ibp_eq hc hq hD he hw hw1 hp hpq hp1 he0 hb0 hb1 hb2 cw2 cp1]
  have hB : 0 ≤ B := by
    have := hb0 0 le_rfl
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have hpne : ∀ s, 0 ≤ s → p s ≠ 0 := fun s hs h => by
    have := hpq s hs; rw [h, norm_zero] at this; linarith
  have hE0 : 0 ≤ ‖e 0‖ := norm_nonneg _
  set Q := ∫ s in Ioi 0, e s * (w2 s / p s - w1 s * p1 s / p s ^ 2) with hQ
  have hpt : ∀ s, 0 ≤ s → ‖e s * (w2 s / p s - w1 s * p1 s / p s ^ 2)‖ ≤
      ‖e 0‖ * (B * (1 / q + D / q ^ 2)) * Real.exp (-3 * s) := fun s hs => by
    have hps : 0 < ‖p s‖ := lt_of_lt_of_le hq (hpq s hs)
    have hex := Real.exp_pos (-3 * s)
    have t1 : ‖w2 s / p s‖ ≤ B * Real.exp (-3 * s) / q := by
      rw [norm_div]
      calc ‖w2 s‖ / ‖p s‖ ≤ ‖w2 s‖ / q := by gcongr; exact hpq s hs
        _ ≤ _ := by gcongr; exact hb2 s hs
    have t2 : ‖w1 s * p1 s / p s ^ 2‖ ≤ B * Real.exp (-3 * s) * D / q ^ 2 := by
      rw [norm_div, norm_mul, norm_pow]
      calc ‖w1 s‖ * ‖p1 s‖ / ‖p s‖ ^ 2 ≤ (B * Real.exp (-3 * s)) * D / q ^ 2 := by
            have := hpq s hs
            have := hb1 s hs
            have := hp1 s hs
            gcongr
        _ = _ := rfl
    have t3 := norm_sub_le (w2 s / p s) (w1 s * p1 s / p s ^ 2)
    rw [norm_mul]
    calc ‖e s‖ * ‖w2 s / p s - w1 s * p1 s / p s ^ 2‖ ≤ ‖e 0‖ * (B * (1 / q + D / q ^ 2) * Real.exp (-3 * s)) := by
          refine mul_le_mul (he0 s hs) ?_ (norm_nonneg _) hE0
          have e1 : B * (1 / q + D / q ^ 2) * Real.exp (-3 * s) =
              B * Real.exp (-3 * s) / q + B * Real.exp (-3 * s) * D / q ^ 2 := by field_simp
          rw [e1]; linarith
      _ = _ := by ring
  have hQb : ‖Q‖ ≤ ‖e 0‖ * (B * (1 / q + D / q ^ 2)) / 3 := by
    have hg : IntegrableOn (fun s : ℝ => ‖e 0‖ * (B * (1 / q + D / q ^ 2)) * Real.exp (-3 * s)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 3)).const_mul _
    have := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi 0)) hg
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs using hpt s (le_of_lt hs))
    refine this.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_exp_neg_three]; ring
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hp0 := hpne 0 le_rfl
  have hw10 : ‖w1 0‖ ≤ B := by
    have := hb1 0 le_rfl
    simpa using this
  have hA : ‖e 0 * w1 0 / (c ^ 2 * p 0)‖ ≤ ‖e 0‖ * B / q / c ^ 2 := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    have hq0 := hpq 0 le_rfl
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h5 : ‖e 0‖ * ‖w1 0‖ * q ≤ ‖e 0‖ * B * ‖p 0‖ := by gcongr
    nlinarith [h5, hc2]
  have hC : ‖(1 / c ^ 2 : ℂ) * Q‖ ≤ ‖e 0‖ * (B * (1 / q + D / q ^ 2)) / 3 / c ^ 2 := by
    rw [norm_mul]
    have : ‖(1 / c ^ 2 : ℂ)‖ = 1 / c ^ 2 := by
      rw [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    rw [this, one_div, inv_mul_eq_div]
    gcongr
  have e0 : (I / c) * e 0 * w 0 - e 0 * w1 0 / (c ^ 2 * p 0) - (1 / c ^ 2 : ℂ) * Q - (I / c) * e 0 * w 0 =
      -(e 0 * w1 0 / (c ^ 2 * p 0)) - (1 / c ^ 2 : ℂ) * Q := by ring
  rw [e0]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg]
  calc _ ≤ ‖e 0‖ * B / q / c ^ 2 + ‖e 0‖ * (B * (1 / q + D / q ^ 2)) / 3 / c ^ 2 := add_le_add hA hC
    _ = _ := by field_simp

end FormalResearch.SignUncertainty
