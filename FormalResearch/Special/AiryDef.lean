module

public import FormalResearch.Special.AiryKernel

/-!
# The Airy function on `ℂ`: definition, entireness, differential equation

For `c > 0`, `k : ℕ` and `z : ℂ` put
`M_k(c, z) = (1/2π) ∫_ℝ (-t)^k exp(t³/3 - z t) ds`, `t = c + i s` (`airyMom k c z`).  The Airy
function is `Ai(z) = M_0(1, z)` (`airyAiC`).  Main results (all for the complex variable `z`):

* `hasDerivAt_airyMom`: `∂_z M_k = M_{k+1}` (differentiation under the integral sign), so every
  `M_k(c, ·)` is entire; in particular `Ai` is entire (`differentiable_airyAiC`);
* `airyMom_succ_succ`: `M_{k+2} = z M_k + k M_{k-1}` (fundamental theorem of calculus in `s`);
* `airyMom_indep`: `M_k(c, z)` does not depend on `c > 0` (differentiation in `c` plus the same
  identity, in place of Cauchy's theorem for the contour shift);
* `airyAiC_ode`: `Ai'' = z Ai`; `deriv_airyAiC`: `Ai' = M_1(c, ·)` for every `c > 0`.

Not formalised in this file: reality on `ℝ`, bounds, zeros, `Bi` (see `AiryReal`, `AiryBound`,
`AiryZeros`, `AiryRotation`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- `M_k(c, z) = (1/2π) ∫_ℝ (-t)^k exp(t³/3 - z t) ds`, `t = c + i s`. -/
noncomputable def airyMom (k : ℕ) (c : ℝ) (z : ℂ) : ℂ :=
  (1 / (2 * (π : ℂ))) * ∫ s, airyPoly k c z s

/-- The Airy function `Ai(z) = (1/2π) ∫_ℝ exp((1 + i s)³/3 - z (1 + i s)) ds` on `ℂ`. -/
noncomputable def airyAiC (z : ℂ) : ℂ := airyMom 0 1 z

lemma hasDerivAt_airyPoly_z (k : ℕ) (c : ℝ) (z : ℂ) (s : ℝ) :
    HasDerivAt (fun z : ℂ => airyPoly k c z s) (airyPoly (k + 1) c z s) z := by
  have h1 : HasDerivAt (fun z : ℂ => airyLine c s ^ 3 / 3 - z * airyLine c s) (-airyLine c s) z := by
    simpa using ((hasDerivAt_id z).mul_const (airyLine c s)).const_sub (airyLine c s ^ 3 / 3)
  have h2 := (h1.cexp.const_mul ((-airyLine c s) ^ k))
  refine h2.congr_deriv ?_
  unfold airyPoly airyKernel
  ring

/-- Differentiation under the integral sign: `∂_z M_k(c, z) = M_{k+1}(c, z)`. -/
lemma hasDerivAt_airyMom {c : ℝ} (hc : 0 < c) (k : ℕ) (z₀ : ℂ) :
    HasDerivAt (airyMom k c) (airyMom (k + 1) c z₀) z₀ := by
  have hs : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds _ one_pos
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (z : ℂ) (s : ℝ) => airyPoly k c z s)
    (F' := fun (z : ℂ) (s : ℝ) => airyPoly (k + 1) c z s) hs
    (Filter.Eventually.of_forall fun z => (continuous_airyPoly k c z).aestronglyMeasurable)
    (integrable_airyPoly hc k z₀) (continuous_airyPoly (k + 1) c z₀).aestronglyMeasurable
    (bound := fun s => Real.exp (c ^ 3 / 3 + (|z₀.re| + 1) * c + (|z₀.im| + 1) ^ 2 / (2 * c)) *
      ((|c| + |s|) ^ (k + 1) * Real.exp (-(c / 2) * s ^ 2)))
    (Filter.Eventually.of_forall fun s z hz => by
      have hz' : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
      have hre : |z.re| ≤ |z₀.re| + 1 := by
        have := (abs_sub_abs_le_abs_sub z.re z₀.re).trans
          ((Complex.abs_re_le_norm (z - z₀)).trans hz'.le)
        linarith
      have him : |z.im| ≤ |z₀.im| + 1 := by
        have := (abs_sub_abs_le_abs_sub z.im z₀.im).trans
          ((Complex.abs_im_le_norm (z - z₀)).trans hz'.le)
        linarith
      exact norm_airyPoly_le hc le_rfl le_rfl hre him (k + 1) s)
    (integrable_airyBound c (|z₀.re| + 1) (|z₀.im| + 1) c hc (k + 1))
    (Filter.Eventually.of_forall fun s z _ => hasDerivAt_airyPoly_z k c z s)
  have := key.2.const_mul (1 / (2 * (π : ℂ)))
  exact this


/-- `M_{k+2} = z M_k + k M_{k-1}` (integration by parts in `s`). -/
lemma airyMom_succ_succ {c : ℝ} (hc : 0 < c) (k : ℕ) (z : ℂ) :
    airyMom (k + 2) c z = z * airyMom k c z + k * airyMom (k - 1) c z := by
  unfold airyMom
  rw [integral_airyPoly_succ_succ hc k z]
  ring

lemma airyMom_two {c : ℝ} (hc : 0 < c) (z : ℂ) : airyMom 2 c z = z * airyMom 0 c z := by
  simpa using airyMom_succ_succ hc 0 z

lemma hasDerivAt_airyLine_c (s c : ℝ) : HasDerivAt (fun c : ℝ => airyLine c s) 1 c := by
  unfold airyLine
  simpa using (hasDerivAt_id c).ofReal_comp.add_const ((s : ℂ) * I)

/-- `∂_c (-t)^k K = (-t)^{k+2} K - z (-t)^k K - k (-t)^{k-1} K` (the Cauchy-Riemann equations
`∂_c = -i ∂_s` for the entire function `t ↦ (-t)^k exp(t³/3 - z t)`). -/
lemma hasDerivAt_airyPoly_c (k : ℕ) (c : ℝ) (z : ℂ) (s : ℝ) :
    HasDerivAt (fun c : ℝ => airyPoly k c z s)
      (airyPoly (k + 2) c z s - z * airyPoly k c z s - k * airyPoly (k - 1) c z s) c := by
  have hL := (hasDerivAt_airyLine_c s c).neg
  have hK : HasDerivAt (fun c : ℝ => airyKernel c z s) ((airyLine c s ^ 2 - z) * airyKernel c z s) c := by
    have h1 : HasDerivAt (fun c : ℝ => airyLine c s ^ 3 / 3 - z * airyLine c s)
        (airyLine c s ^ 2 - z) c := by
      have := (((hasDerivAt_airyLine_c s c).pow 3).div_const 3).sub
        ((hasDerivAt_airyLine_c s c).const_mul z)
      convert this using 1
      simp
    exact h1.cexp.congr_deriv (by unfold airyKernel; ring)
  have h := (hL.pow k).mul hK
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.neg_apply, airyPoly]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp; ring
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

/-- The moments do not depend on the abscissa `c > 0`: `∂_c M_k = 0`. -/
lemma hasDerivAt_airyMom_c {c : ℝ} (hc : 0 < c) (k : ℕ) (z : ℂ) :
    HasDerivAt (fun c : ℝ => airyMom k c z) 0 c := by
  have hs : Ioo (c / 2) (3 * c / 2) ∈ 𝓝 c := Ioo_mem_nhds (by linarith) (by linarith)
  have hc2 : 0 < c / 2 := by positivity
  set bd : ℕ → ℝ → ℝ := fun j s => Real.exp ((3 * c / 2) ^ 3 / 3 + |z.re| * (3 * c / 2) +
      |z.im| ^ 2 / (2 * (c / 2))) * ((|3 * c / 2| + |s|) ^ j * Real.exp (-(c / 2 / 2) * s ^ 2))
    with hbd
  have hbi : ∀ j, Integrable (bd j) := fun j =>
    integrable_airyBound (3 * c / 2) |z.re| |z.im| (c / 2) hc2 j
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (c : ℝ) (s : ℝ) => airyPoly k c z s)
    (F' := fun (c : ℝ) (s : ℝ) => airyPoly (k + 2) c z s - z * airyPoly k c z s -
      k * airyPoly (k - 1) c z s) hs
    (Filter.Eventually.of_forall fun c' => (continuous_airyPoly k c' z).aestronglyMeasurable)
    (integrable_airyPoly hc k z)
    (((continuous_airyPoly (k + 2) c z).sub ((continuous_airyPoly k c z).const_mul z)).sub
      ((continuous_airyPoly (k - 1) c z).const_mul _)).aestronglyMeasurable
    (bound := fun s => bd (k + 2) s + ‖z‖ * bd k s + k * bd (k - 1) s)
    (Filter.Eventually.of_forall fun s c' hc' => by
      have b2 := norm_airyPoly_le (z := z) hc2 hc'.1.le hc'.2.le le_rfl le_rfl (k + 2) s
      have b0 := norm_airyPoly_le (z := z) hc2 hc'.1.le hc'.2.le le_rfl le_rfl k s
      have b1 := norm_airyPoly_le (z := z) hc2 hc'.1.le hc'.2.le le_rfl le_rfl (k - 1) s
      calc ‖airyPoly (k + 2) c' z s - z * airyPoly k c' z s - k * airyPoly (k - 1) c' z s‖
          ≤ ‖airyPoly (k + 2) c' z s‖ + ‖z‖ * ‖airyPoly k c' z s‖ +
            k * ‖airyPoly (k - 1) c' z s‖ := by
            refine (norm_sub_le _ _).trans ?_
            gcongr
            · exact (norm_sub_le _ _).trans (by rw [norm_mul])
            · rw [norm_mul]; simp
        _ ≤ _ := by
            simp only [hbd]
            gcongr)
    (((hbi (k + 2)).add ((hbi k).const_mul ‖z‖)).add ((hbi (k - 1)).const_mul (k : ℝ)))
    (Filter.Eventually.of_forall fun s c' _ => hasDerivAt_airyPoly_c k c' z s)
  have h0 : ∫ s, (airyPoly (k + 2) c z s - z * airyPoly k c z s - k * airyPoly (k - 1) c z s) = 0 := by
    have i2 := integrable_airyPoly hc (k + 2) z
    have i0 := integrable_airyPoly hc k z
    have i1 := integrable_airyPoly hc (k - 1) z
    have ia : Integrable (fun s => airyPoly (k + 2) c z s - z * airyPoly k c z s) :=
      i2.sub (i0.const_mul z)
    have ib : Integrable (fun s => (k : ℂ) * airyPoly (k - 1) c z s) := i1.const_mul _
    rw [integral_sub ia ib, integral_sub i2 (i0.const_mul z), integral_const_mul,
      integral_const_mul, integral_airyPoly_succ_succ hc k z]
    ring
  have := key.2.const_mul (1 / (2 * (π : ℂ)))
  rw [h0, mul_zero] at this
  exact this


lemma airyMom_indep_aux {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℕ) (z : ℂ) :
    airyMom k b z = airyMom k a z := by
  have hd : ∀ x ∈ Icc a b, HasDerivAt (fun c : ℝ => airyMom k c z) 0 x :=
    fun x hx => hasDerivAt_airyMom_c (ha.trans_le hx.1) k z
  exact constant_of_has_deriv_right_zero
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt) b ⟨hab, le_rfl⟩

/-- **Contour independence**: `M_k(c, z)` does not depend on the abscissa `c > 0`.  In
particular `Ai(z) = (1/2π) ∫ exp((c+is)³/3 - z (c+is)) ds` for every `c > 0`. -/
theorem airyMom_indep {c : ℝ} (hc : 0 < c) (k : ℕ) (z : ℂ) : airyMom k c z = airyMom k 1 z := by
  rcases le_total c 1 with h | h
  · exact (airyMom_indep_aux hc h k z).symm
  · exact airyMom_indep_aux one_pos h k z

lemma airyAiC_eq_airyMom {c : ℝ} (hc : 0 < c) (z : ℂ) : airyAiC z = airyMom 0 c z :=
  (airyMom_indep hc 0 z).symm

lemma hasDerivAt_airyAiC_c {c : ℝ} (hc : 0 < c) (z : ℂ) :
    HasDerivAt airyAiC (airyMom 1 c z) z := by
  have : airyAiC = airyMom 0 c := funext fun z => airyAiC_eq_airyMom hc z
  rw [this]
  exact hasDerivAt_airyMom hc 0 z

/-- `Ai` is entire. -/
theorem differentiable_airyAiC : Differentiable ℂ airyAiC := fun z =>
  (hasDerivAt_airyAiC_c one_pos z).differentiableAt

/-- `Ai'(z) = M_1(c, z) = -(1/2π) ∫ (c + i s) exp((c+is)³/3 - z (c+is)) ds` for every `c > 0`. -/
theorem deriv_airyAiC {c : ℝ} (hc : 0 < c) (z : ℂ) : deriv airyAiC z = airyMom 1 c z :=
  (hasDerivAt_airyAiC_c hc z).deriv

theorem hasDerivAt_deriv_airyAiC (z : ℂ) :
    HasDerivAt (deriv airyAiC) (z * airyAiC z) z := by
  have h : deriv airyAiC = airyMom 1 1 := funext fun z => deriv_airyAiC one_pos z
  rw [h]
  have h2 : HasDerivAt (airyMom 1 1) (airyMom 2 1 z) z := hasDerivAt_airyMom one_pos 1 z
  rw [airyMom_two one_pos] at h2
  exact h2

/-- **The Airy equation** `Ai'' = z Ai` on `ℂ`. -/
theorem iteratedDeriv_two_airyAiC (z : ℂ) : iteratedDeriv 2 airyAiC z = z * airyAiC z := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact (hasDerivAt_deriv_airyAiC z).deriv

end FormalResearch.Special
