module

public import FormalResearch.Special.AiryCftQSamplePt
public import FormalResearch.Complex.HardyPoint

/-!
# Theorem Q (2), sharp pointwise bound, and Corollary Q′ (vanishing moments)

CFT `AIRY_POISSON.md` §5, Theorem Q (2) and Corollary Q′, for `f` entire (complex-valued, no reality assumption) with
`‖f(u)‖ ≤ C (1+|u|)^ν e(u)` (any real `ν`) and `f ∈ L¹(ℝ)`; write `‖f‖_b = ∫_{x<0} ‖f‖` and `G = airyQG f`.  All **proved**.

* `airyQ_pointwise_sharp_z`, `airyQ_pointwise_sharp`: for `Im z > 0` (equivalently `u = -z² ∉ (-∞,0]`, `z = i √u`),
  `‖f(u)‖ ≤ ‖f‖_b e(u) / (4π |u|^{1/2} Re √u)`, i.e. `ψ(u) = ‖f(u)‖/e(u) ≤ ‖f‖_b/(4π |u|^{1/2} Re √u)`.  This is the
  note's `ψ(u) ≤ ‖f‖_b/(π |u|^{1/2} Re √u)` **with the improved constant `4π`** that the note attributes to the factorisation
  `H¹ = H²·H²`; here it comes directly from the circle mean of the Möbius transport `h = (G∘φ)φ'` at the centre
  (`Hardy.hardy_value_le`).  `airyQ_pointwise_sharp_pi` is the note's constant `π`.
* `airyQ_vanishing_moment`: Corollary Q′.  For every `λ ≥ 0`, `∫_0^∞ f(-v) sin((4/3) v^{3/2} + λ √v) dv = 0`; more generally, if
  `‖f(u)‖ ≤ C (1+|u|)^ν e(u) exp(-2 ε₀ Re √u)` with `ε₀ ≥ 0`, the same holds for all real `λ ≥ -2 ε₀` (`airyQ_vanishing_moment_decay`).
  Proof: `G(z) e^{iλz}` satisfies the hypotheses of `Hardy.hardy_integral_zero` (`|e^{iλz}| = e^{-λ Im z} ≤ e^{2ε₀ Im z}`, and
  `|f(-z²)|/e ≤ C … e^{-2ε₀ Im z}`), so `∫_ℝ G(x) e^{iλx} dx = 0`; the parts `x > 0` and `x < 0` combine to `i ∫_0^∞ f(-v) sin(…) dv`
  (substitution `v = x²`).  The statement is stated for complex-valued `f` (the sine is real, `f` is not required to be real).

The second half of Theorem Q (2) (`ψ ≤ C₁‖f‖_b|u|^{1/2}` for every `|u| ≥ 1`, hence `𝒢_N ⊂ 𝒢_{1/2}`) is `AiryCftQUniform`.
Not formalised: the Poisson representation `G(z) = ∫ P_z g` and the horizontal bound of Lemma H, the interpretation of Corollary Q′ as
`supp ĝ ⊂ [0,∞)`, and the resonance numerics for `f_m` (`verify_poisson_unfold.py` (5), numerical evidence in the note).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.Special

/-- **Theorem Q (2), sharp pointwise bound, unfolded form.**  For `Im z > 0`:
`‖f(-z²)‖ ≤ (4π |z| Im z)⁻¹ ‖f‖_b e(-z²)`. -/
theorem airyQ_pointwise_sharp_z {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) {z : ℂ} (hz : 0 < z.im) :
    ‖f (-(z ^ 2))‖ ≤ (4 * π * ‖z‖ * z.im)⁻¹ * (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) * airyEnv (-(z ^ 2)) := by
  have hpi := Real.pi_pos
  obtain ⟨h1, h2, h3⟩ := airyQ_hardy_hyp hf hfi hC hb
  have key := FormalResearch.Hardy.hardy_value_le h1 h2 h3 z.re hz
  have hzeq : (z.re : ℂ) + (z.im : ℂ) * I = z := by apply Complex.ext <;> simp
  rw [hzeq, (airyQ_boundary hf hfi).2, airyQ_norm_G f hz.le] at key
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 (fun h => by rw [h] at hz; simp at hz)
  have he := airyEnv_pos (-(z ^ 2))
  have hI0 : 0 ≤ ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := integral_nonneg fun x => norm_nonneg _
  have h4 : ‖f (-(z ^ 2))‖ / airyEnv (-(z ^ 2)) ≤
      (4 * π * z.im)⁻¹ * (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) / ‖z‖ := by
    rw [le_div_iff₀ hz0]; linarith
  rw [div_le_iff₀ he] at h4
  calc ‖f (-(z ^ 2))‖ ≤ (4 * π * z.im)⁻¹ * (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) / ‖z‖ * airyEnv (-(z ^ 2)) := h4
    _ = _ := by field_simp

/-- **Theorem Q (2), sharp pointwise bound.**  For `u ∉ (-∞, 0]` (`Re √u > 0`, principal branch):
`‖f(u)‖ ≤ ‖f‖_b e(u) / (4π |√u| Re √u)`, i.e. `ψ(u) ≤ ‖f‖_b/(4π |u|^{1/2} Re √u)`. -/
theorem airyQ_pointwise_sharp {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) {u : ℂ}
    (hu : 0 < (u ^ (1 / 2 : ℂ)).re) :
    ‖f u‖ ≤ (4 * π * ‖u ^ (1 / 2 : ℂ)‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹ * (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) * airyEnv u := by
  set s : ℂ := u ^ (1 / 2 : ℂ) with hs
  set z : ℂ := I * s with hz
  have hzim : z.im = s.re := by simp [hz]
  have hzn : ‖z‖ = ‖s‖ := by simp [hz]
  have hsq : -(z ^ 2) = u := by
    have : z ^ 2 = -(s ^ 2) := by rw [hz, mul_pow, Complex.I_sq]; ring
    rw [this, hs, cpow_half_sq]; ring
  have := airyQ_pointwise_sharp_z hf hfi hC hb (z := z) (by rw [hzim]; exact hu)
  rwa [hsq, hzim, hzn] at this

/-- The constant `π` of the note (a corollary of the `4π` bound). -/
theorem airyQ_pointwise_sharp_pi {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) {u : ℂ}
    (hu : 0 < (u ^ (1 / 2 : ℂ)).re) :
    ‖f u‖ ≤ (π * ‖u ^ (1 / 2 : ℂ)‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹ * (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) * airyEnv u := by
  have h := airyQ_pointwise_sharp hf hfi hC hb hu
  refine h.trans ?_
  have hpi := Real.pi_pos
  have hn : 0 < ‖u ^ (1 / 2 : ℂ)‖ := by
    refine norm_pos_iff.2 (fun h0 => ?_)
    rw [h0] at hu; simp at hu
  have hI0 : 0 ≤ ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := integral_nonneg fun x => norm_nonneg _
  have he := airyEnv_pos u
  gcongr
  nlinarith [mul_pos hn hu, mul_pos hpi (mul_pos hn hu)]

/-! ### Corollary Q′: vanishing moments -/

/-- `Re √(-z²) = Im z` for `Im z ≥ 0` (principal branch). -/
lemma airyQ_re_sqrt_neg_sq {z : ℂ} (hz : 0 ≤ z.im) : ((-(z ^ 2)) ^ (1 / 2 : ℂ)).re = z.im := by
  set s : ℂ := (-(z ^ 2)) ^ (1 / 2 : ℂ) with hs
  have hs2 : s ^ 2 = (-I * z) ^ 2 := by
    rw [hs, cpow_half_sq]; ring_nf; simp [Complex.I_sq]
  have hre : 0 ≤ s.re := cpow_half_re_nonneg _
  have hcases : s = -I * z ∨ s = I * z := by
    have : (s - (-I * z)) * (s + (-I * z)) = 0 := by linear_combination hs2
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hcases with h | h
  · rw [h]; simp
  · have h1 : s.re = -z.im := by rw [h]; simp
    linarith

/-- The real integrand `x f(-x²) e^{i(4x³/3 + l x)}` is `G(x) e^{ilx}`. -/
lemma airyQ_Gl_real (f : ℂ → ℂ) (l x : ℝ) :
    airyQG f (x : ℂ) * cexp (I * (l : ℂ) * (x : ℂ)) =
      ((x : ℂ) * f (((-(x ^ 2) : ℝ)) : ℂ)) * cexp (I * ((4 / 3 * x ^ 3 + l * x : ℝ) : ℂ)) := by
  unfold airyQG
  rw [mul_assoc, ← Complex.exp_add]
  have e1 : (-((x : ℂ) ^ 2)) = (((-(x ^ 2) : ℝ)) : ℂ) := by push_cast; ring
  rw [e1]
  congr 2
  push_cast
  ring

lemma airyQ_exp_sub_exp (θ : ℝ) :
    cexp (I * (θ : ℂ)) - cexp (I * ((-θ : ℝ) : ℂ)) = 2 * I * ((Real.sin θ : ℝ) : ℂ) := by
  have h1 : cexp (I * (θ : ℂ)) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h2 : cexp (I * ((-θ : ℝ) : ℂ)) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
    rw [mul_comm, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  rw [h1, h2]; ring

lemma airyQ_rpow_three_half {y : ℝ} (hy : 0 ≤ y) : (y ^ 2) ^ (3 / 2 : ℝ) = y ^ 3 := by
  rw [← Real.rpow_natCast y 2, ← Real.rpow_mul hy, ← Real.rpow_natCast y 3]
  norm_num

/-- **Unfolding of the moment.**  For integrable `A(x) = G(x) e^{ilx}`:
`∫_ℝ A = i ∫_0^∞ f(-v) sin((4/3) v^{3/2} + l √v) dv`. -/
lemma airyQ_Gl_integral (f : ℂ → ℂ) (l : ℝ)
    (hA : Integrable (fun x : ℝ => airyQG f (x : ℂ) * cexp (I * (l : ℂ) * (x : ℂ)))) :
    ∫ x : ℝ, airyQG f (x : ℂ) * cexp (I * (l : ℂ) * (x : ℂ)) =
      I * ∫ v in Ioi (0 : ℝ), f (((-v : ℝ)) : ℂ) *
        ((Real.sin (4 / 3 * v ^ (3 / 2 : ℝ) + l * √v) : ℝ) : ℂ) := by
  set A : ℝ → ℂ := fun x => airyQG f (x : ℂ) * cexp (I * (l : ℂ) * (x : ℂ)) with hAdef
  have hsplit : (∫ x in Ioi (0 : ℝ), A x) + (∫ x in (Ioi (0 : ℝ))ᶜ, A x) = ∫ x : ℝ, A x :=
    integral_add_compl measurableSet_Ioi hA
  rw [compl_Ioi] at hsplit
  have hneg : ∫ x in Iic (0 : ℝ), A x = ∫ x in Ioi (0 : ℝ), A (-x) := by
    have := integral_comp_neg_Ioi (0 : ℝ) A
    rw [neg_zero] at this
    exact this.symm
  have hAneg : IntegrableOn (fun x : ℝ => A (-x)) (Ioi 0) := (hA.comp_neg).integrableOn
  -- real form
  set P : ℝ → ℂ := fun y => (y : ℂ) * f (((-(y ^ 2) : ℝ)) : ℂ) with hP
  set θ : ℝ → ℝ := fun y => 4 / 3 * y ^ 3 + l * y with hθ
  have hAy : ∀ y : ℝ, A y = P y * cexp (I * (θ y : ℂ)) := fun y => airyQ_Gl_real f l y
  have hAmy : ∀ y : ℝ, A (-y) = -(P y) * cexp (I * ((-(θ y) : ℝ) : ℂ)) := by
    intro y
    rw [hAy]
    have h1 : P (-y) = -(P y) := by simp [hP]
    have h2 : θ (-y) = -(θ y) := by simp [hθ]; ring
    rw [h1, h2]
  have hcomb : ∀ y : ℝ, A y + A (-y) = 2 * I * (P y * ((Real.sin (θ y) : ℝ) : ℂ)) := by
    intro y
    rw [hAy y, hAmy y]
    have := airyQ_exp_sub_exp (θ y)
    linear_combination (P y) * this
  have hsum : ∫ x : ℝ, A x = ∫ x in Ioi (0 : ℝ), (A x + A (-x)) := by
    rw [integral_add hA.integrableOn hAneg, ← hsplit, hneg]
  -- substitution v = y²
  set g : ℝ → ℂ := fun v => f (((-v : ℝ)) : ℂ) * ((Real.sin (4 / 3 * v ^ (3 / 2 : ℝ) + l * √v) : ℝ) : ℂ) with hg
  have hsq : (fun x : ℝ => x ^ 2) '' Ioi (0 : ℝ) = Ioi 0 := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩; exact pow_pos hx 2
    · intro hv; exact ⟨Real.sqrt v, Real.sqrt_pos.2 hv, Real.sq_sqrt hv.le⟩
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x ^ 2) (2 * x) (Ioi 0) x := fun x hx => by
    simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ => x ^ 2) (Ioi 0) := fun a ha b hb hab => (sq_eq_sq₀ ha.le hb.le).1 hab
  have hchg : ∫ v in Ioi (0 : ℝ), g v = ∫ y in Ioi (0 : ℝ), |2 * y| • g (y ^ 2) := by
    have := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
      (f := fun x : ℝ => x ^ 2) (f' := fun x => 2 * x) measurableSet_Ioi hd hinj g
    rw [hsq] at this
    exact this
  have hpt : ∀ y ∈ Ioi (0 : ℝ), |2 * y| • g (y ^ 2) = 2 * (P y * ((Real.sin (θ y) : ℝ) : ℂ)) := by
    intro y hy
    have hy' : 0 < y := hy
    simp only [hg, hθ, hP]
    rw [abs_of_pos (by linarith), airyQ_rpow_three_half hy'.le, Real.sqrt_sq hy'.le, Complex.real_smul]
    push_cast
    ring_nf
  rw [hsum, hchg, ← MeasureTheory.integral_const_mul]
  have : ∫ x in Ioi (0 : ℝ), (A x + A (-x)) = ∫ y in Ioi (0 : ℝ), I * (2 * (P y * ((Real.sin (θ y) : ℝ) : ℂ))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    rw [hcomb]; ring
  rw [this]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [hpt y hy]

lemma airyQ_pow_bound {C ν : ℝ} (hC : 0 ≤ C) (z : ℂ) :
    ‖z‖ * (C * (1 + ‖z‖ ^ 2) ^ ν) ≤ C * (1 + ‖z‖) ^ (2 * ⌈max ν 0⌉₊ + 1) := by
  have h2 : (1 + ‖z‖ ^ 2) ^ ν ≤ (1 + ‖z‖) ^ (2 * ⌈max ν 0⌉₊) := by
    have hbase : 1 ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖z‖]
    calc (1 + ‖z‖ ^ 2) ^ ν ≤ (1 + ‖z‖ ^ 2) ^ (max ν 0) :=
          Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)
      _ ≤ (1 + ‖z‖ ^ 2) ^ ((⌈max ν 0⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase (Nat.le_ceil (max ν 0))
      _ = (1 + ‖z‖ ^ 2) ^ ⌈max ν 0⌉₊ := Real.rpow_natCast _ _
      _ ≤ ((1 + ‖z‖) ^ 2) ^ ⌈max ν 0⌉₊ := by
          gcongr
          nlinarith [norm_nonneg z]
      _ = (1 + ‖z‖) ^ (2 * ⌈max ν 0⌉₊) := by rw [← pow_mul]
  have hz0 : ‖z‖ ≤ 1 + ‖z‖ := by linarith
  calc ‖z‖ * (C * (1 + ‖z‖ ^ 2) ^ ν) ≤ ‖z‖ * (C * (1 + ‖z‖) ^ (2 * ⌈max ν 0⌉₊)) := by gcongr
    _ ≤ (1 + ‖z‖) * (C * (1 + ‖z‖) ^ (2 * ⌈max ν 0⌉₊)) := by gcongr
    _ = C * (1 + ‖z‖) ^ (2 * ⌈max ν 0⌉₊ + 1) := by ring

/-- **Corollary Q′ with extra decay.**  If `‖f(u)‖ ≤ C (1+|u|)^ν e(u) exp(-2ε₀ Re √u)` (any real `ε₀`), then for every real
`l ≥ -2ε₀`: `∫_0^∞ f(-v) sin((4/3) v^{3/2} + l √v) dv = 0` (in `ℂ`; `f` is not assumed real). -/
theorem airyQ_vanishing_moment_decay {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν ε₀ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u * Real.exp (-2 * ε₀ * (u ^ (1 / 2 : ℂ)).re))
    {l : ℝ} (hl : -2 * ε₀ ≤ l) :
    ∫ v in Ioi (0 : ℝ), f (((-v : ℝ)) : ℂ) * ((Real.sin (4 / 3 * v ^ (3 / 2 : ℝ) + l * √v) : ℝ) : ℂ) = 0 := by
  set Gl : ℂ → ℂ := fun z => airyQG f z * cexp (I * (l : ℂ) * z) with hGl
  have hdiff : Differentiable ℂ Gl := by
    simp only [hGl]
    exact (airyQ_differentiable_G hf).mul (by fun_prop)
  have hnorm_exp : ∀ z : ℂ, ‖cexp (I * (l : ℂ) * z)‖ = Real.exp (-(l * z.im)) := by
    intro z
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  have hgrow : ∀ z : ℂ, 0 ≤ z.im → ‖Gl z‖ ≤ C * (1 + ‖z‖) ^ (2 * ⌈max ν 0⌉₊ + 1) := by
    intro z hz
    have he := airyEnv_pos (-(z ^ 2))
    have h1 : ‖f (-(z ^ 2))‖ / airyEnv (-(z ^ 2)) ≤ C * (1 + ‖z‖ ^ 2) ^ ν * Real.exp (-((2 * ε₀) * z.im)) := by
      rw [div_le_iff₀ he]
      have := hb (-(z ^ 2))
      rw [norm_neg, norm_pow, airyQ_re_sqrt_neg_sq hz] at this
      calc ‖f (-(z ^ 2))‖ ≤ C * (1 + ‖z‖ ^ 2) ^ ν * airyEnv (-(z ^ 2)) * Real.exp (-2 * ε₀ * z.im) := this
        _ = _ := by rw [show -2 * ε₀ * z.im = -((2 * ε₀) * z.im) by ring]; ring
    have h2 : Real.exp (-((2 * ε₀) * z.im)) * Real.exp (-(l * z.im)) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.2
      nlinarith
    have hpow : 0 ≤ C * (1 + ‖z‖ ^ 2) ^ ν := by positivity
    show ‖airyQG f z * cexp (I * (l : ℂ) * z)‖ ≤ _
    rw [norm_mul, hnorm_exp, airyQ_norm_G f hz]
    calc ‖z‖ * (‖f (-(z ^ 2))‖ / airyEnv (-(z ^ 2))) * Real.exp (-(l * z.im))
        ≤ ‖z‖ * (C * (1 + ‖z‖ ^ 2) ^ ν * Real.exp (-((2 * ε₀) * z.im))) * Real.exp (-(l * z.im)) := by gcongr
      _ = ‖z‖ * (C * (1 + ‖z‖ ^ 2) ^ ν) * (Real.exp (-((2 * ε₀) * z.im)) * Real.exp (-(l * z.im))) := by ring
      _ ≤ ‖z‖ * (C * (1 + ‖z‖ ^ 2) ^ ν) * 1 := by gcongr
      _ ≤ _ := by rw [mul_one]; exact airyQ_pow_bound hC z
  have hint : Integrable (fun x : ℝ => Gl (x : ℂ)) := by
    have hbd := (airyQ_boundary hf hfi).1.norm
    refine Integrable.mono' hbd (hdiff.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    show ‖airyQG f (x : ℂ) * cexp (I * (l : ℂ) * (x : ℂ))‖ ≤ ‖airyQG f (x : ℂ)‖
    rw [norm_mul, hnorm_exp]
    simp
  have h0 := FormalResearch.Hardy.hardy_integral_zero hdiff.diffContOnCl hgrow hint
  have h1 := airyQ_Gl_integral f l hint
  have h2 : (I : ℂ) * ∫ v in Ioi (0 : ℝ), f (((-v : ℝ)) : ℂ) *
      ((Real.sin (4 / 3 * v ^ (3 / 2 : ℝ) + l * √v) : ℝ) : ℂ) = 0 := by
    rw [← h1]; exact h0
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h Complex.I_ne_zero
  · exact h

/-- **Corollary Q′ (vanishing moments).**  For every `λ ≥ 0` (here `l`) and every entire `f` with
`‖f(u)‖ ≤ C (1+|u|)^ν e(u)` (any real `ν`) and `f ∈ L¹(ℝ)`: `∫_0^∞ f(-v) sin((4/3) v^{3/2} + l √v) dv = 0`. -/
theorem airyQ_vanishing_moment {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) {l : ℝ} (hl : 0 ≤ l) :
    ∫ v in Ioi (0 : ℝ), f (((-v : ℝ)) : ℂ) * ((Real.sin (4 / 3 * v ^ (3 / 2 : ℝ) + l * √v) : ℝ) : ℂ) = 0 :=
  airyQ_vanishing_moment_decay (ε₀ := 0) hf hfi hC (fun u => by simpa using hb u) (by linarith)

/-- info: 'FormalResearch.Special.airyQ_vanishing_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_vanishing_moment

/-- info: 'FormalResearch.Special.airyQ_vanishing_moment_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_vanishing_moment_decay

/-- info: 'FormalResearch.Special.airyQ_pointwise_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_pointwise_sharp

end FormalResearch.Special
