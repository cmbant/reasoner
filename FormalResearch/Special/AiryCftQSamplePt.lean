module

public import FormalResearch.Special.AiryCftQSample

/-!
# Pointwise bounds for the unfolded function `G = airyQG f` (Theorem Q (2), weak form)

Companions of `AiryCftQSample`, all **proved**, with the Hardy hypotheses of Theorem Q (`f` entire, `‖f(u)‖ ≤ C₀(1+|u|)^ν e(u)`, `f ∈ L¹(ℝ)`):

* `airyQ_far_le`: for real `c ≥ 1` (a point `u = -c² ≤ -1` of the band), with `r = 1/(4c²)`,
  `‖f(-c²)‖/c ≤ (4/π)(∫ ‖G(t)‖ r²/((t-c)²+r²) dt + e⁴ ∫ ‖G(t)‖ r²/((t+c)²+r²) dt)` (the single-point form of `airyQ_term_le`, used for
  the zeros of `P Ai + Q Ai'` as well);
* `airyQH f z = f(-z²) exp((4/3) i z³) = G(z)/z` (entire) and `airyQH_point`: for every fixed `w` there is an explicit constant `C(w)`
  (independent of `f`) with `‖H(w)‖ ≤ C(w) ∫_{x<0} ‖f‖`;
* `airyQ_pointwise_real`: for real `u ≤ -1`, `‖f(u)‖ ≤ (4/π)(1+e⁴) √(-u) ∫_{x<0} ‖f‖` with an absolute constant (Theorem Q (2) on the negative
  axis, `ψ ≤ C₁ ‖f‖_b |u|^{1/2}`);
* `airyQ_f_point`: hence `‖f(u)‖ ≤ C(u) ∫_{x<0} ‖f‖` at every fixed `u ∈ ℂ` (`f(u) = H(z₀) e^{-(4/3) i z₀³}` for `z₀² = -u`),
  in particular at the finitely many zeros of `P Ai + Q Ai'` with `t > -1`.

This is the pointwise bound of Theorem Q (2) of the note at a fixed point, with a non-sharp constant (Cauchy's formula on `|z| = |w|+1` instead
of the Poisson kernel); the sharp form `‖G(z)‖ ≤ ‖g‖₁/(π Im z)` is not formalised.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.Special

/-- **Single-point kernel bound** (`c ≥ 1`, `r = 1/(4c²)`). -/
lemma airyQ_far_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) {c : ℝ} (hc : 1 ≤ c) :
    ‖f (((-(c ^ 2) : ℝ)) : ℂ)‖ / c ≤ (4 / π) *
      ((∫ t : ℝ, ‖airyQG f (t : ℂ)‖ * ((1 / (4 * c ^ 2)) ^ 2 / ((t - c) ^ 2 + (1 / (4 * c ^ 2)) ^ 2))) +
        Real.exp 4 * ∫ t : ℝ, ‖airyQG f (t : ℂ)‖ * ((1 / (4 * c ^ 2)) ^ 2 / ((t + c) ^ 2 + (1 / (4 * c ^ 2)) ^ 2))) := by
  have hc0 : 0 < c := by linarith
  have hpt := airyQ_sample_pt hf hfi hC hb hc
  set r : ℝ := 1 / (4 * c ^ 2) with hr
  have hr0 : 0 < r := by positivity
  set J1 := ∫ t : ℝ, ‖airyQG f (t : ℂ)‖ / ((t - c) ^ 2 + r ^ 2)
  set J2 := ∫ t : ℝ, ‖airyQG f (t : ℂ)‖ / ((t + c) ^ 2 + r ^ 2)
  have e1 : (∫ t : ℝ, ‖airyQG f (t : ℂ)‖ * (r ^ 2 / ((t - c) ^ 2 + r ^ 2))) = r ^ 2 * J1 :=
    FormalResearch.Hardy.integral_weight_eq (fun t => ‖airyQG f (t : ℂ)‖) c r
  have e2 : (∫ t : ℝ, ‖airyQG f (t : ℂ)‖ * (r ^ 2 / ((t + c) ^ 2 + r ^ 2))) = r ^ 2 * J2 := by
    have := FormalResearch.Hardy.integral_weight_eq (fun t => ‖airyQG f (t : ℂ)‖) (-c) r
    simpa [sub_neg_eq_add] using this
  rw [e1, e2]
  have hfa : ‖f (((-(c ^ 2) : ℝ)) : ℂ)‖ = ‖airyQG f (c : ℂ)‖ / c := by
    rw [airyQ_norm_G_real, abs_of_pos hc0]
    field_simp
  rw [hfa]
  have hinv : 1 / c ^ 2 = 4 * r := by rw [hr]; field_simp
  have hpi := Real.pi_pos
  have h2 : ‖airyQG f (c : ℂ)‖ / c / c = (1 / c ^ 2) * ‖airyQG f (c : ℂ)‖ := by field_simp
  rw [h2, hinv]
  calc 4 * r * ‖airyQG f (c : ℂ)‖ ≤ 4 * r * ((r / π) * (J1 + Real.exp 4 * J2)) :=
        mul_le_mul_of_nonneg_left hpt (by positivity)
    _ = _ := by field_simp

/-- `H(z) = f(-z²) exp((4/3) i z³) = G(z)/z`. -/
noncomputable def airyQH (f : ℂ → ℂ) (z : ℂ) : ℂ := f (-(z ^ 2)) * cexp ((4 / 3 : ℂ) * I * z ^ 3)

lemma airyQG_eq_mul_H (f : ℂ → ℂ) (z : ℂ) : airyQG f z = z * airyQH f z := by
  unfold airyQG airyQH; ring

lemma airyQH_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Differentiable ℂ (airyQH f) := by
  unfold airyQH; fun_prop

lemma airyQH_refl (f : ℂ → ℂ) {w : ℂ} (hw : w.im ≤ 0) :
    ‖airyQH f w‖ ≤ ‖airyQH f (-w)‖ * Real.exp (8 * w.re ^ 2 * |w.im|) := by
  have hA : ‖cexp ((4 / 3 : ℂ) * I * w ^ 3)‖ = Real.exp (-(4 / 3) * (w ^ 3).im) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]
  have hB : ‖cexp ((4 / 3 : ℂ) * I * (-w) ^ 3)‖ = Real.exp ((4 / 3) * (w ^ 3).im) := by
    rw [Complex.norm_exp]; congr 1
    have : (-w) ^ 3 = -(w ^ 3) := by ring
    rw [this]; simp [Complex.mul_re, Complex.mul_im]
  have h1 : ‖airyQH f w‖ = ‖f (-(w ^ 2))‖ * Real.exp (-(4 / 3) * (w ^ 3).im) := by
    unfold airyQH; rw [norm_mul, hA]
  have h2 : ‖airyQH f (-w)‖ = ‖f (-(w ^ 2))‖ * Real.exp ((4 / 3) * (w ^ 3).im) := by
    unfold airyQH; rw [norm_mul, hB]
    have : (-w) ^ 2 = w ^ 2 := by ring
    rw [this]
  have hX : 0 ≤ ‖f (-(w ^ 2))‖ := norm_nonneg _
  have hE : Real.exp (-(4 / 3) * (w ^ 3).im) ≤ Real.exp ((4 / 3) * (w ^ 3).im) * Real.exp (8 * w.re ^ 2 * |w.im|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [im_pow_three, abs_of_nonpos hw]
    nlinarith [sq_nonneg w.re, mul_nonneg (sq_nonneg w.re) (neg_nonneg.mpr hw),
      mul_nonneg (neg_nonneg.mpr hw) (sq_nonneg w.im)]
  rw [h1, h2]
  calc ‖f (-(w ^ 2))‖ * Real.exp (-(4 / 3) * (w ^ 3).im)
      ≤ ‖f (-(w ^ 2))‖ * (Real.exp ((4 / 3) * (w ^ 3).im) * Real.exp (8 * w.re ^ 2 * |w.im|)) :=
        mul_le_mul_of_nonneg_left hE hX
    _ = _ := by ring

/-- **Fixed-point bound for `H`.**  For every `w` there is an explicit `C(w) ≥ 0`, independent of `f`, with
`‖H(w)‖ ≤ C(w) ∫_{x<0} ‖f‖`. -/
theorem airyQH_point (w : ℂ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : ℂ → ℂ} (_ : Differentiable ℂ f)
    (_ : Integrable (fun x : ℝ => f (x : ℂ))) {C₀ ν : ℝ} (_ : 0 ≤ C₀)
    (_ : ∀ u : ℂ, ‖f u‖ ≤ C₀ * (1 + ‖u‖) ^ ν * airyEnv u),
    ‖airyQH f w‖ ≤ C * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
  set ρ : ℝ := ‖w‖ + 1 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hpi := Real.pi_pos
  refine ⟨(1 + Real.exp (8 * ρ ^ 3)) / (4 * π * ρ), by positivity, fun {f} hf hfi {C₀ ν} hC hb => ?_⟩
  obtain ⟨h1, h2, h3⟩ := airyQ_hardy_hyp hf hfi hC hb
  have harc := FormalResearch.Hardy.hardy_arc_le_poly h1 h2 h3 hρ0
  rw [(airyQ_boundary hf hfi).2] at harc
  have hrefl : ∀ z : ℂ, ‖z‖ = ρ → z.im ≤ 0 → ‖airyQH f z‖ ≤ Real.exp (8 * ρ ^ 3) * ‖airyQH f (-z)‖ := by
    intro z hz hzi
    refine (airyQH_refl f hzi).trans ?_
    rw [mul_comm (Real.exp (8 * ρ ^ 3))]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hre : |z.re| ≤ ρ := by have := Complex.abs_re_le_norm z; rwa [hz] at this
    have him : |z.im| ≤ ρ := by have := Complex.abs_im_le_norm z; rwa [hz] at this
    have hsq : z.re ^ 2 ≤ ρ ^ 2 := by
      have := sq_le_sq' (by linarith [abs_nonneg z.re, (abs_le.mp hre).1] : -ρ ≤ z.re) (abs_le.mp hre).2
      exact this
    calc 8 * z.re ^ 2 * |z.im| ≤ 8 * ρ ^ 2 * ρ := by
          have := mul_le_mul hsq him (abs_nonneg _) (by positivity)
          linarith
      _ = 8 * ρ ^ 3 := by ring
  have hpt := FormalResearch.Hardy.hardy_point_le (airyQH_differentiable hf) (w := w) (ρ := ρ) (by rw [hρ]; linarith) hrefl
  have hgap : ρ - ‖w‖ = 1 := by rw [hρ]; ring
  rw [hgap, div_one] at hpt
  -- arc integral of H
  have harcH : ∫ θ in (0 : ℝ)..π, ‖airyQH f (circleMap 0 ρ θ)‖ ≤ (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) / (2 * ρ ^ 2) := by
    have e : ∀ θ : ℝ, ‖airyQH f (circleMap 0 ρ θ)‖ = ‖airyQG f (circleMap 0 ρ θ)‖ / ρ := by
      intro θ
      rw [airyQG_eq_mul_H, norm_mul]
      have : ‖circleMap 0 ρ θ‖ = ρ := by simp [abs_of_pos hρ0]
      rw [this]; field_simp
    simp_rw [e]
    rw [intervalIntegral.integral_div, le_div_iff₀ (by positivity)]
    have := harc
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hI0 : 0 ≤ ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := integral_nonneg fun x => norm_nonneg _
  refine hpt.trans ?_
  have hfac : 0 ≤ ρ * ((2 * π)⁻¹ * (1 + Real.exp (8 * ρ ^ 3))) := by positivity
  calc ρ * ((2 * π)⁻¹ * ((1 + Real.exp (8 * ρ ^ 3)) * ∫ θ in (0 : ℝ)..π, ‖airyQH f (circleMap 0 ρ θ)‖))
      = (ρ * ((2 * π)⁻¹ * (1 + Real.exp (8 * ρ ^ 3)))) * ∫ θ in (0 : ℝ)..π, ‖airyQH f (circleMap 0 ρ θ)‖ := by ring
    _ ≤ (ρ * ((2 * π)⁻¹ * (1 + Real.exp (8 * ρ ^ 3)))) * ((∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) / (2 * ρ ^ 2)) :=
        mul_le_mul_of_nonneg_left harcH hfac
    _ = _ := by field_simp; ring

/-- **Pointwise bound for `f` at a fixed point.**  For every `u ∈ ℂ` there is `C(u) ≥ 0` independent of `f` with
`‖f(u)‖ ≤ C(u) ∫_{x<0} ‖f‖`. -/
theorem airyQ_f_point (u : ℂ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : ℂ → ℂ} (_ : Differentiable ℂ f)
    (_ : Integrable (fun x : ℝ => f (x : ℂ))) {C₀ ν : ℝ} (_ : 0 ≤ C₀)
    (_ : ∀ u : ℂ, ‖f u‖ ≤ C₀ * (1 + ‖u‖) ^ ν * airyEnv u),
    ‖f u‖ ≤ C * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
  set z₀ : ℂ := (-u) ^ (1 / 2 : ℂ) with hz₀
  have hsq : -(z₀ ^ 2) = u := by rw [hz₀, cpow_half_sq]; ring
  obtain ⟨C, hC0, hC⟩ := airyQH_point z₀
  refine ⟨C * Real.exp ((4 / 3) * ‖z₀‖ ^ 3), by positivity, fun {f} hf hfi {C₀ ν} hC₀ hb => ?_⟩
  have h1 := hC hf hfi hC₀ hb
  have hH : airyQH f z₀ = f u * cexp ((4 / 3 : ℂ) * I * z₀ ^ 3) := by
    unfold airyQH; rw [hsq]
  have hn : ‖airyQH f z₀‖ = ‖f u‖ * Real.exp (-(4 / 3) * (z₀ ^ 3).im) := by
    rw [hH, norm_mul, Complex.norm_exp]
    congr 2; simp [Complex.mul_re, Complex.mul_im]
  have him : (z₀ ^ 3).im ≤ ‖z₀‖ ^ 3 := by
    calc (z₀ ^ 3).im ≤ ‖z₀ ^ 3‖ := Complex.im_le_norm _
      _ = ‖z₀‖ ^ 3 := norm_pow _ _
  have hexp : 1 ≤ Real.exp ((4 / 3) * (z₀ ^ 3).im) * Real.exp (-(4 / 3) * (z₀ ^ 3).im) := by
    rw [← Real.exp_add]; simp
  have hfu : ‖f u‖ = ‖airyQH f z₀‖ * Real.exp ((4 / 3) * (z₀ ^ 3).im) := by
    rw [hn, mul_assoc, ← Real.exp_add]; simp
  rw [hfu]
  have hI0 : 0 ≤ ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := integral_nonneg fun x => norm_nonneg _
  have hE : Real.exp ((4 / 3) * (z₀ ^ 3).im) ≤ Real.exp ((4 / 3) * ‖z₀‖ ^ 3) :=
    Real.exp_le_exp.mpr (by linarith)
  calc ‖airyQH f z₀‖ * Real.exp ((4 / 3) * (z₀ ^ 3).im)
      ≤ (C * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) * Real.exp ((4 / 3) * ‖z₀‖ ^ 3) :=
        mul_le_mul h1 hE (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- **Pointwise bound on the band (Theorem Q (2), real axis, `u ≤ -1`).**  `‖f(u)‖ ≤ (4/π)(1 + e⁴) √(-u) ∫_{x<0} ‖f‖`
(`ψ(u) = ‖f(u)‖/e(u) ≤ C ‖f‖_b |u|^{1/2}` on the negative axis, where `e = 1`; the note's constant `C₁` is absolute as here). -/
theorem airyQ_pointwise_real {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) {u : ℝ} (hu : u ≤ -1) :
    ‖f (u : ℂ)‖ ≤ (4 / π) * (1 + Real.exp 4) * √(-u) * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
  have hpi := Real.pi_pos
  set c : ℝ := √(-u) with hc
  have hc1 : 1 ≤ c := by
    rw [hc, show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hc0 : 0 < c := by linarith
  have hsq : -(c ^ 2) = u := by rw [hc, Real.sq_sqrt (by linarith)]; ring
  have hfar := airyQ_far_le hf hfi hC hb hc1
  rw [hsq] at hfar
  set r : ℝ := 1 / (4 * c ^ 2) with hr
  have hr0 : 0 < r := by positivity
  have hgi : Integrable (fun t : ℝ => ‖airyQG f (t : ℂ)‖) := (airyQ_boundary hf hfi).1.norm
  have hgint : ∫ t : ℝ, ‖airyQG f (t : ℂ)‖ = ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := (airyQ_boundary hf hfi).2
  have hk : ∀ s : ℝ, ∫ t : ℝ, ‖airyQG f (t : ℂ)‖ * (r ^ 2 / ((t - s) ^ 2 + r ^ 2)) ≤
      ∫ t : ℝ, ‖airyQG f (t : ℂ)‖ := by
    intro s
    refine integral_mono (integrable_mul_kern hgi s r hr0) hgi (fun t => ?_)
    have := FormalResearch.Hardy.kernel_term_le_one (d := t - s) hr0
    nlinarith [norm_nonneg (airyQG f (t : ℂ))]
  have h1 := hk c
  have h2 := hk (-c)
  simp only [sub_neg_eq_add] at h2
  rw [hgint] at h1 h2
  have hI0 : 0 ≤ ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := integral_nonneg fun x => norm_nonneg _
  have h3 : ‖f (u : ℂ)‖ / c ≤ (4 / π) * (1 + Real.exp 4) * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
    refine hfar.trans ?_
    have : (∫ t : ℝ, ‖airyQG f (t : ℂ)‖ * (r ^ 2 / ((t - c) ^ 2 + r ^ 2))) +
        Real.exp 4 * (∫ t : ℝ, ‖airyQG f (t : ℂ)‖ * (r ^ 2 / ((t + c) ^ 2 + r ^ 2))) ≤
        (1 + Real.exp 4) * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
      nlinarith [Real.exp_pos 4]
    calc 4 / π * _ ≤ 4 / π * ((1 + Real.exp 4) * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  rw [div_le_iff₀ hc0] at h3
  calc ‖f (u : ℂ)‖ ≤ (4 / π) * (1 + Real.exp 4) * (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) * c := h3
    _ = _ := by ring

/-- info: 'FormalResearch.Special.airyQ_pointwise_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_pointwise_real

/-- info: 'FormalResearch.Special.airyQ_f_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_f_point

end FormalResearch.Special
