module

public import FormalResearch.Special.AiryIdentities
public import FormalResearch.Special.AiryPositive

/-!
# The Airy kernel as a Gram integral: `K(x,y) = ∫_0^∞ Ai(x+t) Ai(y+t) dt`

For real `x, y` let `airyKer x y` be the Airy kernel, `(Ai(x)Ai'(y) - Ai'(x)Ai(y))/(x - y)` off the
diagonal and `Ai'(x)² - x Ai(x)²` on it.  Proved here:

* `airyKer_eq_integral`: `K(x,y) = ∫_{t>0} Ai(x+t) Ai(y+t) dt` for all real `x, y`, the integral being
  absolutely convergent (`integrableOn_airyAi_shift_mul`).  Off the diagonal this is the integrated shift
  identity `(∂_x + ∂_y)K = -Ai(x)Ai(y)` together with `K(x+s, y+s) → 0` (`s → ∞`); on the diagonal it is
  `integral_Ioi_airyAi_sq`.
* `airyKer_comm`, `airyKer_diag_nonneg`, `airyKer_diag_pos`: `K` is symmetric, `K(x,x) ≥ 0`, `K(x,x) > 0`.
* `airyKer_sq_le`: `K(x,y)² ≤ K(x,x) K(y,y)` (the `2 × 2` Gram determinant), `measurable_airyKer`.
* `airyKer_quad`: the quadratic form `∫ (Ai(x+t) + λ Ai(y+t))² dt = K(x,x) + 2λK(x,y) + λ²K(y,y)`.
  The diagonal integrals `∫_u^∞ K(s,s) ds` are in `AiryKernelOpBounds`.

**Real arguments only.**  The same Gram formula holds for complex `x, y` (`Ai` is entire), but this
needs a decay bound for `Ai(z)` along real shifts of complex `z`, which is not in the base library
(`AiryBound` is for real `x`); it is not formalised here.
-/

@[expose] public section

open Filter Topology MeasureTheory Set

namespace FormalResearch.Special

/-- The Airy kernel `K(x,y) = (Ai(x)Ai'(y) - Ai'(x)Ai(y))/(x-y)`, continued to the diagonal by
`K(x,x) = Ai'(x)² - x Ai(x)²` (the limit, `airyKernelAi_diag`). -/
noncomputable def airyKer (x y : ℝ) : ℝ :=
  if x = y then airyAi' x ^ 2 - x * airyAi x ^ 2 else airyKernelAi x y

lemma airyKer_of_ne {x y : ℝ} (h : x ≠ y) : airyKer x y = airyKernelAi x y := by simp [airyKer, h]

lemma airyKer_self (x : ℝ) : airyKer x x = airyAi' x ^ 2 - x * airyAi x ^ 2 := by simp [airyKer]

/-- Translation by `x` carries `Ioi 0` onto `Ioi x`. -/
lemma integral_Ioi_add_left (g : ℝ → ℝ) (x : ℝ) :
    ∫ t in Ioi 0, g (x + t) = ∫ t in Ioi x, g t := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) x).setIntegral_preimage_emb
    (measurableEmbedding_addLeft x) g (Ioi x)
  have hs : (fun t : ℝ => x + t) ⁻¹' Ioi x = Ioi 0 := by
    ext t; simp
  rw [hs] at h
  exact h

lemma integrableOn_Ioi_add_left {g : ℝ → ℝ} (x : ℝ) (hg : IntegrableOn g (Ioi x)) :
    IntegrableOn (fun t => g (x + t)) (Ioi 0) := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) x).integrableOn_comp_preimage
    (measurableEmbedding_addLeft x) (f := g) (s := Ioi x)
  have hs : (fun t : ℝ => x + t) ⁻¹' Ioi x = Ioi 0 := by
    ext t; simp
  rw [hs] at h
  exact h.mpr hg

lemma integrableOn_airyAi_shift_sq (x : ℝ) :
    IntegrableOn (fun t => airyAi (x + t) ^ 2) (Ioi 0) :=
  integrableOn_Ioi_add_left x (integrableOn_Ioi_airyAi_sq x)

lemma continuous_airyAi' : Continuous airyAi' :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAi' x).continuousAt

lemma continuous_airyAi : Continuous airyAi := differentiable_airyAi.continuous

/-- `Ai(x+t) Ai(y+t)` is integrable on `(0, ∞)`. -/
theorem integrableOn_airyAi_shift_mul (x y : ℝ) :
    IntegrableOn (fun t => airyAi (x + t) * airyAi (y + t)) (Ioi 0) := by
  refine Integrable.mono'
    (((integrableOn_airyAi_shift_sq x).add (integrableOn_airyAi_shift_sq y)).const_mul (1 / 2)) ?_ ?_
  · exact ((continuous_airyAi.comp (continuous_const.add continuous_id)).mul
      (continuous_airyAi.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (airyAi (x + t) + airyAi (y + t)),
      sq_nonneg (airyAi (x + t) - airyAi (y + t))]

lemma hasDerivAt_airyKernelAi_shift {x y : ℝ} (hxy : x ≠ y) (s : ℝ) :
    HasDerivAt (fun w => airyKernelAi (x + w) (y + w)) (-(airyAi (x + s) * airyAi (y + s))) s := by
  have h := airyKernelAi_shift (x := x + s) (t := y + s) (by simpa using hxy)
  have h3 : HasDerivAt (fun u => airyKernelAi (x + s + u) (y + s + u))
      (-(airyAi (x + s) * airyAi (y + s))) (s - s) := by simpa using h
  have h4 := h3.comp_sub_const s s
  convert h4 using 1
  funext w
  congr 1 <;> ring

lemma tendsto_airyKernelAi_shift {x y : ℝ} :
    Tendsto (fun s => airyKernelAi (x + s) (y + s)) atTop (𝓝 0) := by
  have hx : Tendsto (fun s : ℝ => x + s) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
  have hy : Tendsto (fun s : ℝ => y + s) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
  have h1 := ((tendsto_airyAi.comp hx).mul (tendsto_airyAi'.comp hy)).sub
    ((tendsto_airyAi'.comp hx).mul (tendsto_airyAi.comp hy))
  have h2 := h1.div_const (x - y)
  simp only [mul_zero, sub_zero, zero_div] at h2
  refine h2.congr fun s => ?_
  simp only [Function.comp_apply, airyKernelAi]
  rw [show x + s - (y + s) = x - y by ring]

/-- **The Airy kernel is a Gram integral**: for all real `x, y`,
`K(x,y) = ∫_{t > 0} Ai(x+t) Ai(y+t) dt`. -/
theorem airyKer_eq_integral (x y : ℝ) :
    airyKer x y = ∫ t in Ioi 0, airyAi (x + t) * airyAi (y + t) := by
  by_cases hxy : x = y
  · subst hxy
    rw [airyKer_self]
    simp_rw [← sq]
    rw [integral_Ioi_add_left (fun t => airyAi t ^ 2) x, integral_Ioi_airyAi_sq]
  · have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt (fun w => airyKernelAi (x + w) (y + w))
        (-(airyAi (x + s) * airyAi (y + s))) s := fun s _ => hasDerivAt_airyKernelAi_shift hxy s
    have hint := (integrableOn_airyAi_shift_mul x y).neg
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint
      (tendsto_airyKernelAi_shift (x := x) (y := y))
    rw [integral_neg] at h
    rw [airyKer_of_ne hxy]
    simp only [add_zero] at h
    linarith

theorem airyKer_comm (x y : ℝ) : airyKer x y = airyKer y x := by
  rw [airyKer_eq_integral, airyKer_eq_integral]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => mul_comm _ _)

/-- `K(x,x) = ∫_{t>0} Ai(x+t)²`. -/
theorem airyKer_self_eq_integral (x : ℝ) :
    airyKer x x = ∫ t in Ioi 0, airyAi (x + t) ^ 2 := by
  rw [airyKer_eq_integral]; simp_rw [← sq]

theorem airyKer_diag_nonneg (x : ℝ) : 0 ≤ airyKer x x := by
  rw [airyKer_self_eq_integral]
  exact setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _

/-- Quadratic form of the `2 × 2` Gram matrix: `∫ (Ai(x+t) + λ Ai(y+t))² = K(x,x) + 2λK(x,y) + λ²K(y,y)`. -/
lemma airyKer_quad (x y l : ℝ) :
    ∫ t in Ioi 0, (airyAi (x + t) + l * airyAi (y + t)) ^ 2 =
      airyKer x x + 2 * l * airyKer x y + l ^ 2 * airyKer y y := by
  have h1 := integrableOn_airyAi_shift_sq x
  have h2 := integrableOn_airyAi_shift_sq y
  have h3 := integrableOn_airyAi_shift_mul x y
  have e : ∀ t, (airyAi (x + t) + l * airyAi (y + t)) ^ 2 =
      airyAi (x + t) ^ 2 + (2 * l) * (airyAi (x + t) * airyAi (y + t)) +
        l ^ 2 * airyAi (y + t) ^ 2 := fun t => by ring
  simp_rw [e]
  have hA : IntegrableOn (fun t => airyAi (x + t) ^ 2 +
      (2 * l) * (airyAi (x + t) * airyAi (y + t))) (Ioi 0) := h1.add (h3.const_mul (2 * l))
  have hB : IntegrableOn (fun t => (2 * l) * (airyAi (x + t) * airyAi (y + t))) (Ioi 0) :=
    h3.const_mul (2 * l)
  have hC : IntegrableOn (fun t => l ^ 2 * airyAi (y + t) ^ 2) (Ioi 0) := h2.const_mul (l ^ 2)
  rw [integral_add hA hC, integral_add h1 hB,
    integral_const_mul, integral_const_mul,
    airyKer_self_eq_integral, airyKer_self_eq_integral, airyKer_eq_integral]

/-- Cauchy–Schwarz for the Gram matrix: `K(x,y)² ≤ K(x,x) K(y,y)`. -/
theorem airyKer_sq_le (x y : ℝ) : airyKer x y ^ 2 ≤ airyKer x x * airyKer y y := by
  have h : ∀ l : ℝ, 0 ≤ airyKer y y * (l * l) + 2 * airyKer x y * l + airyKer x x := by
    intro l
    have := airyKer_quad x y l
    have hn : 0 ≤ ∫ t in Ioi 0, (airyAi (x + t) + l * airyAi (y + t)) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
    nlinarith
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith

theorem measurable_airyKer : Measurable (fun p : ℝ × ℝ => airyKer p.1 p.2) := by
  have hm : Measurable (fun p : ℝ × ℝ => airyKernelAi p.1 p.2) := by
    unfold airyKernelAi
    have a := continuous_airyAi.measurable
    have b := continuous_airyAi'.measurable
    have : Measurable (fun p : ℝ × ℝ => airyAi p.1 * airyAi' p.2 - airyAi' p.1 * airyAi p.2) :=
      ((a.comp measurable_fst).mul (b.comp measurable_snd)).sub
        ((b.comp measurable_fst).mul (a.comp measurable_snd))
    exact this.div (measurable_fst.sub measurable_snd)
  have hd : Measurable (fun p : ℝ × ℝ => airyAi' p.1 ^ 2 - p.1 * airyAi p.1 ^ 2) :=
    ((continuous_airyAi'.measurable.comp measurable_fst).pow_const 2).sub
      (measurable_fst.mul ((continuous_airyAi.measurable.comp measurable_fst).pow_const 2))
  unfold airyKer
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) hd hm

/-- `K(x,x) > 0`: the integrand `Ai(x+t)²` is positive for `t > max 0 (-x)`, where `x + t ≥ 0`. -/
theorem airyKer_diag_pos (x : ℝ) : 0 < airyKer x x := by
  rw [airyKer_self_eq_integral]
  refine (integral_pos_iff_support_of_nonneg (fun _ => sq_nonneg _)
    (integrableOn_airyAi_shift_sq x)).mpr ?_
  set m := max 0 (-x) with hm
  have hsub : Ioi m ⊆ Function.support (fun t => airyAi (x + t) ^ 2) := by
    intro t ht
    have : 0 ≤ x + t := by
      have : -x < t := lt_of_le_of_lt (le_max_right _ _) ht
      linarith
    simpa [Function.mem_support] using (airyAi_pos this).ne'
  have hmeas : (volume.restrict (Ioi (0 : ℝ))) (Ioi m) = ⊤ := by
    rw [Measure.restrict_apply' measurableSet_Ioi]
    have : Ioi m ∩ Ioi (0 : ℝ) = Ioi m := inter_eq_left.mpr
      (Ioi_subset_Ioi (le_max_left _ _))
    rw [this, Real.volume_Ioi]
  exact lt_of_lt_of_le (by rw [hmeas]; exact ENNReal.zero_lt_top) (measure_mono hsub)

/-- info: 'FormalResearch.Special.airyKer_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKer_eq_integral

/-- info: 'FormalResearch.Special.airyKer_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKer_sq_le

/-- info: 'FormalResearch.Special.airyKer_diag_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKer_diag_pos

/-- info: 'FormalResearch.Special.measurable_airyKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.measurable_airyKer

end FormalResearch.Special
