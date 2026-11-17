module

public import FormalResearch.Special.AiryPwsDeriv
public import FormalResearch.Special.AiryEnvCalculus

/-!
# The class `G` and its Fourier transform on the closed upper half plane

`AiryClassG f` is the class `G` recalled in `CFT/notes/general_theorems.tex` (§0, used in §3): `f` entire, `f|_ℝ ∈ L¹(ℝ)` and
`‖f(z)‖ ≤ C (1+|z|)^N e(z)`, `e(z) = exp(-(4/3) Re z^{3/2})` (`airyEnv`).  (The paper's `G` consists of *real* functions;
reality is not used anywhere here, so this is the complex class `G_ℂ`.)

For `f ∈ G` and `Im ζ ≥ 0` the transform `f̂(ζ) = ∫_ℝ f(u) e^{-iζu} du` (`airyFhat`) converges absolutely
(`|f(u) e^{-iζu}| = |f(u)| e^{(Im ζ) u}`, and `e^{Ru} e(u) ≤ e^{R³/3+2/3} e^{-2u/3}` on `u ≥ 0` by Young's inequality
`Ru ≤ (2/3)u^{3/2} + R³/3`); it is holomorphic on `Im ζ > 0` and continuous on `Im ζ ≥ 0`
(`differentiableOn_airyFhat`, `continuousOn_airyFhat`).  The *twisted* transform is
`F̃(ζ) = k e^{-iζ³/12} f̂(ζ)`, `k = 2^{2/3}` (`airyFtilde`, `airyPhiK`).

**Not formalised** here: the bounds on `F̃` (`AiryPwsGrowth`, `AiryPwsMain`).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- **The class `G`**: entire, integrable on `ℝ`, with the Airy envelope bound times a polynomial. -/
structure AiryClassG (f : ℂ → ℂ) : Prop where
  differentiable : Differentiable ℂ f
  integrable : Integrable (fun x : ℝ => f (x : ℂ))
  bound : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N * airyEnv z

/-- `f̂(ζ) = ∫_ℝ f(u) e^{-iζu} du`. -/
noncomputable def airyFhat (f : ℂ → ℂ) (ζ : ℂ) : ℂ := ∫ u : ℝ, f (u : ℂ) * cexp (-(I * ζ * (u : ℂ)))

/-- The twisted transform `F̃(ζ) = k e^{-iζ³/12} f̂(ζ)`, `k = 2^{2/3}`. -/
noncomputable def airyFtilde (f : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  (airyPhiK : ℂ) * cexp (-(I * ζ ^ 3 / 12)) * airyFhat f ζ

/-! ### Real-line estimates -/

lemma norm_cexp_airyFhat (ζ : ℂ) (u : ℝ) : ‖cexp (-(I * ζ * (u : ℂ)))‖ = Real.exp (ζ.im * u) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma airyEnv_ofReal_nonneg {u : ℝ} (hu : 0 ≤ u) : airyEnv (u : ℂ) = Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by
  unfold airyEnv
  have : ((u : ℂ) ^ (3 / 2 : ℂ)).re = u ^ (3 / 2 : ℝ) := by
    have := Complex.ofReal_cpow hu (3 / 2 : ℝ)
    rw [show (((3 / 2 : ℝ)) : ℂ) = (3 / 2 : ℂ) by push_cast; ring] at this
    rw [← this, Complex.ofReal_re]
  rw [this]

/-- Young: `R u ≤ (2/3) u^{3/2} + R³/3` for `R, u ≥ 0`. -/
lemma airyPws_young_three_halves {R u : ℝ} (hR : 0 ≤ R) (hu : 0 ≤ u) :
    R * u ≤ (2 / 3) * u ^ (3 / 2 : ℝ) + R ^ 3 / 3 := by
  have h : u ^ (3 / 2 : ℝ) = (√u) ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu]; norm_num
  rw [h]
  have hu' : u = (√u) ^ 2 := (Real.sq_sqrt hu).symm
  set x := √u
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  rw [hu']
  nlinarith [mul_nonneg (sq_nonneg (x - R)) (by positivity : 0 ≤ 2 * x + R)]

lemma airyPws_sub_one_le_rpow_three_halves {u : ℝ} (hu : 0 ≤ u) : u - 1 ≤ u ^ (3 / 2 : ℝ) := by
  have h0 := Real.rpow_nonneg hu (3 / 2 : ℝ)
  rcases le_total u 1 with h1 | h1
  · linarith
  · have := Real.rpow_le_rpow_of_exponent_le h1 (show (1 : ℝ) ≤ 3 / 2 by norm_num)
    rw [Real.rpow_one] at this
    linarith

lemma exp_mul_airyEnv_le {R : ℝ} (hR : 0 ≤ R) {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (R * u) * airyEnv (u : ℂ) ≤ Real.exp (R ^ 3 / 3 + 2 / 3) * Real.exp (-(2 / 3) * u) := by
  rw [airyEnv_ofReal_nonneg hu, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have := airyPws_young_three_halves hR hu
  have := airyPws_sub_one_le_rpow_three_halves hu
  nlinarith

/-- The integrable majorant. -/
noncomputable def airyPwsDom (f : ℂ → ℂ) (C : ℝ) (N : ℕ) (δ R : ℝ) (u : ℝ) : ℝ :=
  if u < 0 then (1 + 1 / δ) * ‖f (u : ℂ)‖
  else C * Real.exp (R ^ 3 / 3 + 2 / 3) * ((1 + u) ^ (N + 1) * Real.exp (-(2 / 3) * u))

lemma integrable_airyPwsDom {f : ℂ → ℂ} (hf : AiryClassG f) {C : ℝ} {N : ℕ} (δ R : ℝ) :
    Integrable (airyPwsDom f C N δ R) := by
  have h1 : Integrable (fun u : ℝ => (Iio (0 : ℝ)).indicator (fun u => (1 + 1 / δ) * ‖f (u : ℂ)‖) u) :=
    (hf.integrable.norm.const_mul (1 + 1 / δ)).indicator measurableSet_Iio
  have h2 : Integrable (fun u : ℝ => (Ici (0 : ℝ)).indicator
      (fun u => C * Real.exp (R ^ 3 / 3 + 2 / 3) * ((1 + u) ^ (N + 1) * Real.exp (-(2 / 3) * u))) u) := by
    rw [integrable_indicator_iff measurableSet_Ici]
    have := ((airyPws_integrableOn_pow_mul_exp (N + 1) (by norm_num : (0 : ℝ) < 2 / 3)).const_mul
      (C * Real.exp (R ^ 3 / 3 + 2 / 3)))
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr this
  refine (h1.add h2).congr (Eventually.of_forall fun u => ?_)
  by_cases hu : u < 0
  · simp [airyPwsDom, hu, indicator_of_mem, mem_Iio]
  · simp [airyPwsDom, hu, mem_Iio, mem_Ici, not_lt.mp hu]

/-- Pointwise bound of the integrand and of `(1+|u|)` times it, for `δ ≤ Im ζ ≤ R`. -/
lemma airyPws_norm_integrand_le {f : ℂ → ℂ} {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hb : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N * airyEnv z) {δ R : ℝ} (hδ : 0 < δ) (ζ : ℂ)
    (h1 : δ ≤ ζ.im) (h2 : ζ.im ≤ R) (u : ℝ) :
    (1 + |u|) * ‖f (u : ℂ) * cexp (-(I * ζ * (u : ℂ)))‖ ≤ airyPwsDom f C N δ R u := by
  rw [norm_mul, norm_cexp_airyFhat]
  unfold airyPwsDom
  have hR : 0 ≤ R := by linarith
  by_cases hu : u < 0
  · simp only [hu, ↓reduceIte]
    rw [abs_of_neg hu]
    have hfn := norm_nonneg (f (u : ℂ))
    have e1 : Real.exp (ζ.im * u) ≤ Real.exp (δ * u) := Real.exp_le_exp.mpr (by nlinarith)
    have e2 : (1 - u) * Real.exp (δ * u) ≤ 1 + 1 / δ := by
      have a : Real.exp (δ * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have b : (-u) * Real.exp (δ * u) ≤ 1 / δ := by
        -- `x e^{-δ x} ≤ 1/δ` for `x = -u ≥ 0`
        have := Real.add_one_le_exp (-(δ * u) - 1)
        have h3 : Real.exp (-(δ * u) - 1) = Real.exp (-(δ * u)) * Real.exp (-1) := by
          rw [sub_eq_add_neg, Real.exp_add]
        have h4 : Real.exp (δ * u) * Real.exp (-(δ * u)) = 1 := by rw [← Real.exp_add]; simp
        have h5 : 0 < Real.exp (δ * u) := Real.exp_pos _
        have h6 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
        have h7 : 0 < Real.exp 1 := Real.exp_pos 1
        have h8 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
        -- -(δ u) ≤ e^{-(δu) - 1} * e ... use direct bound
        have h9 : -(δ * u) ≤ Real.exp (-(δ * u)) := by linarith [Real.add_one_le_exp (-(δ * u))]
        have h10 : (-(δ * u)) * Real.exp (δ * u) ≤ 1 := by
          calc (-(δ * u)) * Real.exp (δ * u) ≤ Real.exp (-(δ * u)) * Real.exp (δ * u) :=
                mul_le_mul_of_nonneg_right h9 h5.le
            _ = 1 := by rw [mul_comm, h4]
        rw [le_div_iff₀ hδ]
        nlinarith
      nlinarith
    calc (1 - u) * (‖f (u : ℂ)‖ * Real.exp (ζ.im * u)) ≤ (1 - u) * (‖f (u : ℂ)‖ * Real.exp (δ * u)) := by
          gcongr
          linarith
      _ = ((1 - u) * Real.exp (δ * u)) * ‖f (u : ℂ)‖ := by ring
      _ ≤ (1 + 1 / δ) * ‖f (u : ℂ)‖ := mul_le_mul_of_nonneg_right e2 hfn
  · simp only [hu, ↓reduceIte]
    have hu0 : 0 ≤ u := not_lt.mp hu
    rw [abs_of_nonneg hu0]
    have hf := hb (u : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0] at hf
    have e1 : Real.exp (ζ.im * u) ≤ Real.exp (R * u) := Real.exp_le_exp.mpr (by nlinarith)
    have e2 := exp_mul_airyEnv_le hR hu0
    have hfn := norm_nonneg (f (u : ℂ))
    have h0 : 0 ≤ C * (1 + u) ^ N * airyEnv (u : ℂ) := by
      have := airyEnv_pos (u : ℂ); positivity
    calc (1 + u) * (‖f (u : ℂ)‖ * Real.exp (ζ.im * u))
        ≤ (1 + u) * ((C * (1 + u) ^ N * airyEnv (u : ℂ)) * Real.exp (R * u)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hf e1 (Real.exp_pos _).le h0) (by linarith)
      _ = C * (1 + u) ^ (N + 1) * (Real.exp (R * u) * airyEnv (u : ℂ)) := by ring
      _ ≤ C * (1 + u) ^ (N + 1) * (Real.exp (R ^ 3 / 3 + 2 / 3) * Real.exp (-(2 / 3) * u)) := by
          gcongr
      _ = _ := by ring

/-- The same without the factor `1 + |u|`, for `0 ≤ Im ζ ≤ R`. -/
lemma airyPws_norm_integrand_le' {f : ℂ → ℂ} {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hb : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N * airyEnv z) {R : ℝ} (ζ : ℂ)
    (h1 : 0 ≤ ζ.im) (h2 : ζ.im ≤ R) (u : ℝ) :
    ‖f (u : ℂ) * cexp (-(I * ζ * (u : ℂ)))‖ ≤ airyPwsDom f C N 1 R u := by
  rw [norm_mul, norm_cexp_airyFhat]
  have hR : 0 ≤ R := by linarith
  by_cases hu : u < 0
  · simp only [airyPwsDom, hu, ↓reduceIte]
    have hfn := norm_nonneg (f (u : ℂ))
    have e1 : Real.exp (ζ.im * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc ‖f (u : ℂ)‖ * Real.exp (ζ.im * u) ≤ ‖f (u : ℂ)‖ * 1 := mul_le_mul_of_nonneg_left e1 hfn
      _ ≤ (1 + 1 / 1) * ‖f (u : ℂ)‖ := by linarith
  · simp only [airyPwsDom, hu, ↓reduceIte]
    have hu0 : 0 ≤ u := not_lt.mp hu
    have hf := hb (u : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0] at hf
    have e1 : Real.exp (ζ.im * u) ≤ Real.exp (R * u) := Real.exp_le_exp.mpr (by nlinarith)
    have e2 := exp_mul_airyEnv_le hR hu0
    have h0 : 0 ≤ C * (1 + u) ^ N * airyEnv (u : ℂ) := by
      have := airyEnv_pos (u : ℂ); positivity
    calc ‖f (u : ℂ)‖ * Real.exp (ζ.im * u)
        ≤ (C * (1 + u) ^ N * airyEnv (u : ℂ)) * Real.exp (R * u) :=
          mul_le_mul hf e1 (Real.exp_pos _).le h0
      _ = C * (1 + u) ^ N * (Real.exp (R * u) * airyEnv (u : ℂ)) := by ring
      _ ≤ C * (1 + u) ^ N * (Real.exp (R ^ 3 / 3 + 2 / 3) * Real.exp (-(2 / 3) * u)) := by gcongr
      _ ≤ C * (1 + u) ^ (N + 1) * (Real.exp (R ^ 3 / 3 + 2 / 3) * Real.exp (-(2 / 3) * u)) := by
          have : (1 + u) ^ N ≤ (1 + u) ^ (N + 1) := pow_le_pow_right₀ (by linarith) (by omega)
          gcongr
      _ = _ := by ring

lemma continuous_airyIntegrand {f : ℂ → ℂ} (hf : AiryClassG f) (ζ : ℂ) :
    Continuous fun u : ℝ => f (u : ℂ) * cexp (-(I * ζ * (u : ℂ))) := by
  have := hf.differentiable.continuous
  fun_prop

/-- `f̂` is continuous on the closed upper half plane. -/
theorem continuousOn_airyFhat {f : ℂ → ℂ} (hf : AiryClassG f) :
    ContinuousOn (airyFhat f) {ζ | 0 ≤ ζ.im} := by
  obtain ⟨C, N, hC, hb⟩ := hf.bound
  intro ζ0 hζ0
  have hmem : {ζ : ℂ | 0 ≤ ζ.im ∧ ζ.im < ζ0.im + 1} ∈ 𝓝[{ζ | 0 ≤ ζ.im}] ζ0 := by
    refine mem_nhdsWithin.mpr ⟨{ζ | ζ.im < ζ0.im + 1}, isOpen_lt Complex.continuous_im continuous_const,
      by simp, ?_⟩
    intro ζ hζ; exact ⟨hζ.2, hζ.1⟩
  have hcont : ContinuousOn (airyFhat f) {ζ : ℂ | 0 ≤ ζ.im ∧ ζ.im ≤ ζ0.im + 1} := by
    refine continuousOn_of_dominated (bound := airyPwsDom f C N 1 (ζ0.im + 1)) ?_ ?_
      (integrable_airyPwsDom hf _ _) ?_
    · intro ζ _; exact (continuous_airyIntegrand hf ζ).aestronglyMeasurable
    · intro ζ hζ
      exact Eventually.of_forall fun u => airyPws_norm_integrand_le' hC hb ζ hζ.1 hζ.2 u
    · exact Eventually.of_forall fun u => by
        have := hf.differentiable.continuous
        fun_prop
  have h2 : ContinuousWithinAt (airyFhat f) {ζ : ℂ | 0 ≤ ζ.im ∧ ζ.im ≤ ζ0.im + 1} ζ0 :=
    hcont ζ0 ⟨hζ0, by linarith⟩
  refine h2.mono_of_mem_nhdsWithin ?_
  filter_upwards [hmem] with ζ hζ using ⟨hζ.1, hζ.2.le⟩

/-- `f̂` is holomorphic on the open upper half plane. -/
theorem differentiableOn_airyFhat {f : ℂ → ℂ} (hf : AiryClassG f) :
    DifferentiableOn ℂ (airyFhat f) {ζ | 0 < ζ.im} := by
  obtain ⟨C, N, hC, hb⟩ := hf.bound
  intro ζ0 hζ0
  have hη : 0 < ζ0.im := hζ0
  refine DifferentiableAt.differentiableWithinAt ?_
  set δ := ζ0.im / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set R := ζ0.im + 1 with hR
  have hball : Metric.ball ζ0 (min δ 1) ∈ 𝓝 ζ0 := Metric.ball_mem_nhds _ (by positivity)
  have hbd : ∀ ζ ∈ Metric.ball ζ0 (min δ 1), δ ≤ ζ.im ∧ ζ.im ≤ R := by
    intro ζ hζ
    have h := Complex.abs_im_le_norm (ζ - ζ0)
    have h' : ‖ζ - ζ0‖ < min δ 1 := by simpa [dist_eq_norm] using hζ
    have := abs_le.mp (h.trans h'.le)
    simp only [Complex.sub_im] at this
    have hm1 := min_le_left δ 1
    have hm2 := min_le_right δ 1
    constructor <;> linarith [this.1, this.2]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (ζ : ℂ) (u : ℝ) => f (u : ℂ) * cexp (-(I * ζ * (u : ℂ))))
    (F' := fun (ζ : ℂ) (u : ℝ) => f (u : ℂ) * (cexp (-(I * ζ * (u : ℂ))) * (-(I * (u : ℂ)))))
    (s := Metric.ball ζ0 (min δ 1)) (x₀ := ζ0)
    (bound := airyPwsDom f C N δ R) hball
    (Eventually.of_forall fun ζ => (continuous_airyIntegrand hf ζ).aestronglyMeasurable)
    (by
      have := (integrable_airyPwsDom hf (C := C) (N := N) δ R)
      refine this.mono' (continuous_airyIntegrand hf ζ0).aestronglyMeasurable
        (Eventually.of_forall fun u => ?_)
      have h := airyPws_norm_integrand_le hC hb hδ0 ζ0 (R := R) (by linarith) (by linarith) u
      have h2 : 0 ≤ ‖f (u : ℂ) * cexp (-(I * ζ0 * (u : ℂ)))‖ := norm_nonneg _
      nlinarith [abs_nonneg u])
    (by
      refine Continuous.aestronglyMeasurable ?_
      have := hf.differentiable.continuous
      fun_prop)
    (Eventually.of_forall fun u ζ hζ => by
      have h := airyPws_norm_integrand_le hC hb hδ0 ζ (hbd ζ hζ).1 (hbd ζ hζ).2 u
      have e : ‖f (u : ℂ) * (cexp (-(I * ζ * (u : ℂ))) * (-(I * (u : ℂ))))‖ =
          |u| * ‖f (u : ℂ) * cexp (-(I * ζ * (u : ℂ)))‖ := by
        simp only [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
        ring
      rw [e]
      have h2 : 0 ≤ ‖f (u : ℂ) * cexp (-(I * ζ * (u : ℂ)))‖ := norm_nonneg _
      nlinarith [abs_nonneg u])
    (integrable_airyPwsDom hf _ _)
    (Eventually.of_forall fun u ζ _ => by
      have h1 : HasDerivAt (fun ζ : ℂ => -(I * ζ * (u : ℂ))) (-(I * (u : ℂ))) ζ := by
        have := (((hasDerivAt_id ζ).const_mul I).mul_const (u : ℂ)).neg
        convert this using 1
        · funext y; simp
        · simp
      have := (h1.cexp).const_mul (f (u : ℂ))
      simpa [mul_comm] using this)
  exact key.2.differentiableAt

/-- info: 'FormalResearch.Special.continuousOn_airyFhat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.continuousOn_airyFhat

/-- info: 'FormalResearch.Special.differentiableOn_airyFhat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.differentiableOn_airyFhat

end FormalResearch.Special
