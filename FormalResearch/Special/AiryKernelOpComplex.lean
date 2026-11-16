module

public import FormalResearch.Special.AiryKernelOpFormula
public import FormalResearch.Special.AiryZeros

/-!
# The Airy kernel for complex arguments: `K(x,y) = ∫_0^∞ Ai(x+t) Ai(y+t) dt`, `x, y ∈ ℂ`

`airyKerC x y` is the Airy kernel `(Ai(x)Ai'(y) - Ai'(x)Ai(y))/(x-y)` of the entire function `Ai = airyAiC`
(with `Ai'(x)² - x Ai(x)²` on the diagonal).  Using the exponential decay of `Ai(z₀ + t)`, `Ai'(z₀ + t)` along
real shifts (`airyRay_decay`, `AiryZeros`):

* `airyKerC_eq_integral`: `K(x,y) = ∫_{t > 0} Ai(x+t) Ai(y+t) dt` (`t` real, absolutely convergent,
  `integrableOn_airyAiC_shift_mul`) for all complex `x, y`;
* `airyKerC_comm`: symmetry; `airyKerC_ofReal`: agrees with `airyKer` on real arguments;
* `airyKerC_conj`: `K(x, x̄) = ∫_0^∞ |Ai(x+t)|² dt`, a nonnegative real number (`conj Ai(z) = Ai(z̄)`).

Not formalised: the growth bound `|K(x,x̄)| ≲ (1+|x|)^{1/2}e(x)` of the survey (it needs sector bounds on `Ai`).
-/

@[expose] public section

open Filter Topology MeasureTheory Set

namespace FormalResearch.Special

/-- The Airy kernel on `ℂ × ℂ`, continued to the diagonal by `K(x,x) = Ai'(x)² - x Ai(x)²`. -/
noncomputable def airyKerC (x y : ℂ) : ℂ :=
  if x = y then deriv airyAiC x ^ 2 - x * airyAiC x ^ 2
  else airyKernelXY airyAiC (deriv airyAiC) airyAiC (deriv airyAiC) x y

lemma airyKerC_of_ne {x y : ℂ} (h : x ≠ y) :
    airyKerC x y = airyKernelXY airyAiC (deriv airyAiC) airyAiC (deriv airyAiC) x y := by
  simp [airyKerC, h]

lemma airyKerC_self (x : ℂ) : airyKerC x x = deriv airyAiC x ^ 2 - x * airyAiC x ^ 2 := by
  simp [airyKerC]

/-! ### Decay along real shifts -/

lemma tendsto_airyRay_zero (z₀ : ℂ) :
    Tendsto (fun s : ℝ => airyAiC (z₀ + s)) atTop (𝓝 0) ∧
      Tendsto (fun s : ℝ => deriv airyAiC (z₀ + s)) atTop (𝓝 0) := by
  obtain ⟨C, hC, h⟩ := airyRay_decay z₀
  have hb : Tendsto (fun s : ℝ => C * Real.exp (-s)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  exact ⟨squeeze_zero_norm (fun s => (h s).1) hb, squeeze_zero_norm (fun s => (h s).2) hb⟩

lemma integrableOn_airyAiC_shift_mul (x y : ℂ) :
    IntegrableOn (fun t : ℝ => airyAiC (x + t) * airyAiC (y + t)) (Ioi 0) := by
  obtain ⟨Cx, hCx, hx⟩ := airyRay_decay x
  obtain ⟨Cy, hCy, hy⟩ := airyRay_decay y
  have hint := (integrableOn_exp_mul_Ioi (show (-2 : ℝ) < 0 by norm_num) 0).const_mul (Cx * Cy)
  refine Integrable.mono' hint ?_ ?_
  · exact ((continuous_airyRay x).mul (continuous_airyRay y)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [norm_mul]
    have h1 := (hx t).1
    have h2 := (hy t).1
    calc ‖airyAiC (x + t)‖ * ‖airyAiC (y + t)‖
        ≤ (Cx * Real.exp (-t)) * (Cy * Real.exp (-t)) := by
          have h1' : ‖airyAiC (x + t)‖ ≤ Cx * Real.exp (-t) := h1
          have h2' : ‖airyAiC (y + t)‖ ≤ Cy * Real.exp (-t) := h2
          exact mul_le_mul h1' h2' (norm_nonneg _) (by positivity)
      _ = Cx * Cy * Real.exp (-2 * t) := by
          rw [show -2 * t = -t + -t by ring, Real.exp_add]; ring

lemma hasDerivAt_airyKerC_shift {x y : ℂ} (hxy : x ≠ y) (s : ℝ) :
    HasDerivAt (fun w : ℝ => airyKernelXY airyAiC (deriv airyAiC) airyAiC (deriv airyAiC)
      (x + w) (y + w)) (-(airyAiC (x + s) * airyAiC (y + s))) s := by
  have h := isAirySol_airyAiC.hasDerivAt_airyKernelXY_shift isAirySol_airyAiC
    (x := x + s) (t := y + s) (by simpa using hxy)
  have h3 : HasDerivAt (fun u : ℂ => airyKernelXY airyAiC (deriv airyAiC) airyAiC (deriv airyAiC)
      (x + s + u) (y + s + u)) (-(airyAiC (x + s) * airyAiC (y + s))) ((s : ℂ) - s) := by
    simpa using h
  have h4 := h3.comp_sub_const (s : ℂ) (s : ℂ)
  have h5 := h4.comp_ofReal
  convert h5 using 1
  funext w
  congr 1 <;> ring

lemma tendsto_airyKernelXY_shiftC (x y : ℂ) :
    Tendsto (fun s : ℝ => airyKernelXY airyAiC (deriv airyAiC) airyAiC (deriv airyAiC)
      (x + s) (y + s)) atTop (𝓝 0) := by
  obtain ⟨hx0, hx1⟩ := tendsto_airyRay_zero x
  obtain ⟨hy0, hy1⟩ := tendsto_airyRay_zero y
  have h := ((hx0.mul hy1).sub (hx1.mul hy0)).div_const (x - y)
  simp only [mul_zero, sub_zero, zero_div] at h
  refine h.congr fun s => ?_
  simp only [airyKernelXY]
  rw [show x + (s : ℂ) - (y + s) = x - y by ring]

lemma tendsto_airy_energyC (x : ℂ) :
    Tendsto (fun s : ℝ => (x + s) * airyAiC (x + s) ^ 2 - deriv airyAiC (x + s) ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, h⟩ := airyRay_decay x
  obtain ⟨_, hx1⟩ := tendsto_airyRay_zero x
  have h2 : Tendsto (fun s : ℝ => deriv airyAiC (x + s) ^ 2) atTop (𝓝 0) := by
    simpa using hx1.pow 2
  have h1 : Tendsto (fun s : ℝ => (x + s) * airyAiC (x + s) ^ 2) atTop (𝓝 0) := by
    have e0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0)
    have e1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
    have hb := ((e0.const_mul (‖x‖)).add e1).const_mul (C ^ 2)
    simp only [pow_zero, one_mul, pow_one, mul_zero, add_zero] at hb
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 0] with s hs
    rw [norm_mul, norm_pow]
    have hn : ‖x + (s : ℂ)‖ ≤ ‖x‖ + s := by
      calc ‖x + (s : ℂ)‖ ≤ ‖x‖ + ‖(s : ℂ)‖ := norm_add_le _ _
        _ = ‖x‖ + s := by simp [abs_of_nonneg hs]
    have ha : ‖airyAiC (x + s)‖ ^ 2 ≤ C ^ 2 * Real.exp (-s) := by
      have := (h s).1
      have h0 : ‖airyAiC (x + s)‖ ≤ C * Real.exp (-s) := this
      calc ‖airyAiC (x + s)‖ ^ 2 ≤ (C * Real.exp (-s)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h0 2
        _ = C ^ 2 * Real.exp (-s) * Real.exp (-s) := by ring
        _ ≤ C ^ 2 * Real.exp (-s) * 1 := by
            gcongr
            exact Real.exp_le_one_iff.mpr (by linarith)
        _ = _ := by ring
    calc ‖x + (s : ℂ)‖ * ‖airyAiC (x + s)‖ ^ 2 ≤ (‖x‖ + s) * (C ^ 2 * Real.exp (-s)) :=
          mul_le_mul hn ha (by positivity) (by positivity)
      _ = _ := by ring
  simpa using h1.sub h2

/-- **The Airy kernel for complex arguments is a Gram integral**: for all `x, y ∈ ℂ`,
`K(x,y) = ∫_{t>0} Ai(x+t) Ai(y+t) dt` (real `t`, absolutely convergent). -/
theorem airyKerC_eq_integral (x y : ℂ) :
    airyKerC x y = ∫ t : ℝ in Ioi 0, airyAiC (x + t) * airyAiC (y + t) := by
  by_cases hxy : x = y
  · subst hxy
    rw [airyKerC_self]
    have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt (fun w : ℝ => ((x + (w : ℂ)) * airyAiC (x + w) ^ 2 -
        deriv airyAiC (x + w) ^ 2)) (airyAiC (x + s) ^ 2) s := by
      intro s _
      have h := (isAirySol_airyAiC.hasDerivAt_energy (x + s))
      have h2 : HasDerivAt (fun u : ℂ => (x + u) * airyAiC (x + u) ^ 2 - deriv airyAiC (x + u) ^ 2)
          (airyAiC (x + s) ^ 2) (s : ℂ) := by
        have := h.comp_const_add x (s : ℂ)
        exact this
      exact h2.comp_ofReal
    have hint : IntegrableOn (fun t : ℝ => airyAiC (x + t) ^ 2) (Ioi 0) := by
      simpa [sq] using integrableOn_airyAiC_shift_mul x x
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint (tendsto_airy_energyC x)
    simp only [sq] at h ⊢
    simp only [Complex.ofReal_zero, add_zero] at h
    rw [h]; ring
  · have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt (fun w : ℝ => airyKernelXY airyAiC (deriv airyAiC)
        airyAiC (deriv airyAiC) (x + w) (y + w)) (-(airyAiC (x + s) * airyAiC (y + s))) s :=
      fun s _ => hasDerivAt_airyKerC_shift hxy s
    have hint := (integrableOn_airyAiC_shift_mul x y).neg
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint (tendsto_airyKernelXY_shiftC x y)
    rw [integral_neg] at h
    rw [airyKerC_of_ne hxy]
    simp only [Complex.ofReal_zero, add_zero] at h
    linear_combination h

theorem airyKerC_comm (x y : ℂ) : airyKerC x y = airyKerC y x := by
  rw [airyKerC_eq_integral, airyKerC_eq_integral]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => mul_comm _ _)

/-- On real arguments the complex kernel is the real kernel `airyKer`. -/
theorem airyKerC_ofReal (x y : ℝ) : airyKerC (x : ℂ) (y : ℂ) = (airyKer x y : ℂ) := by
  rw [airyKerC_eq_integral, airyKer_eq_integral, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [← Complex.ofReal_add, ← Complex.ofReal_add, airyAiC_ofReal, airyAiC_ofReal,
    Complex.ofReal_mul]

/-- **`K(x, x̄) = ∫_0^∞ |Ai(x+t)|² dt`**, a nonnegative real number. -/
theorem airyKerC_conj (x : ℂ) :
    airyKerC x ((starRingEnd ℂ) x) =
      ((∫ t : ℝ in Ioi 0, ‖airyAiC (x + t)‖ ^ 2 : ℝ) : ℂ) := by
  rw [airyKerC_eq_integral, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  have : (starRingEnd ℂ) x + (t : ℂ) = (starRingEnd ℂ) (x + t) := by simp
  rw [this, ← conj_airyAiC, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem airyKerC_conj_nonneg (x : ℂ) :
    0 ≤ ∫ t : ℝ in Ioi 0, ‖airyAiC (x + t)‖ ^ 2 :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _

/-- info: 'FormalResearch.Special.airyKerC_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKerC_eq_integral

/-- info: 'FormalResearch.Special.airyKerC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKerC_ofReal

/-- info: 'FormalResearch.Special.airyKerC_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKerC_conj

end FormalResearch.Special
