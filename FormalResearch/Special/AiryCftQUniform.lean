module

public import FormalResearch.Special.AiryCftQSharp
public import FormalResearch.Special.AiryCftSignUncertainty
public import FormalResearch.Complex.HardyPointReal

/-!
# Theorem Q (2), uniform collapse `𝒢_N ⊂ 𝒢_{1/2}`

CFT `AIRY_POISSON.md` §5, Theorem Q (2): for `f ∈ 𝒢_N` (`f` entire, `‖f(u)‖ ≤ C(1+|u|)^ν e(u)` for some real `ν`, `f ∈ L¹(ℝ)`),
`ψ(u) = ‖f(u)‖/e(u) ≤ C₁ ‖f‖_b |u|^{1/2}` for `|u| ≥ 1` with an absolute `C₁`; in particular `f ∈ 𝒢_{1/2}`, so `∪_N 𝒢_N = 𝒢_{1/2}`.  **Proved**:

* `airyQG_norm_le_sq`: `‖G(z)‖ ≤ C₁ |z|² ‖f‖_b` for `Im z ≥ 0`, `|z| ≥ 1`, `C₁ = 4(1 + e⁹)/π`.  For `Im z > δ := 1/(4|z|²)` it is the sharp
  pointwise bound `‖G(z)‖ ≤ ‖g‖₁/(4π Im z)` (`Hardy.hardy_value_le`); for `0 ≤ Im z ≤ δ` it is the weighted-arc bound at the point `z`
  from the circle `|w - Re z| = Im z + δ` (`Hardy.hardy_point_real_le`, reflection `w ↦ -w` of `airyQG_refl`, `8 (Re w)² |Im w| ≤ 9` there).
  (The note's argument averages `|G|` over a disc of radius `1/(4|z|²)` and uses the horizontal `L¹` bound of Lemma H, which is not formalised;
  the Cauchy formula on a circle about the real centre replaces it.)
* `airyQ_pointwise_uniform`: `‖f(u)‖ ≤ C₁ √|u| ‖f‖_b e(u)` for `|u| ≥ 1` (all `u ∈ ℂ`, not only the negative axis; the negative axis was
  `airyQ_pointwise_real`);
* `airyQ_mem_half`: `f ∈ 𝒢_{1/2}`: `‖f(u)‖ ≤ C' (1+|u|)^{1/2} e(u)` for all `u`, with `C'` depending on `f` (on the unit disc by
  continuity, `e ≥ exp(-(4/3)·8)` there).

Not formalised: the gain `ψ ≤ C‖f‖_b/|u|` on `|arg u| ≤ 2π/3` is the sharp bound `airyQ_pointwise_sharp` (`Re √u ≥ |u|^{1/2}/2` there); the
horizontal bound `∫ ‖G(x+iy)‖ dx ≤ ‖g‖₁`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.Special

/-- On the circle `|w - c| = r` with `r ≤ 1/(2 s²)`, `s ≥ max(1, |c|)`: `8 (Re w)² |Im w| ≤ 9`. -/
lemma airy_circle_exp_le_nine {c s r : ℝ} (hs : 1 ≤ s) (hc : |c| ≤ s) (hr0 : 0 < r) (hr : r ≤ 1 / (2 * s ^ 2))
    {w : ℂ} (hw : ‖w - (c : ℂ)‖ = r) : 8 * w.re ^ 2 * |w.im| ≤ 9 := by
  have hs0 : 0 < s := by linarith
  have him : |w.im| ≤ r := by
    have := Complex.abs_im_le_norm (w - (c : ℂ)); simpa [hw] using this
  have hre : |w.re - c| ≤ r := by
    have := Complex.abs_re_le_norm (w - (c : ℂ)); simpa [hw] using this
  have hre2 : |w.re| ≤ s + r := by
    have h1 := abs_le.mp hre
    have h2 := abs_le.mp hc
    rw [abs_le]; constructor <;> linarith
  have hsq : w.re ^ 2 ≤ (s + r) ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg w.re, (abs_le.mp hre2).1] : -(s + r) ≤ w.re) (abs_le.mp hre2).2
    exact this
  have hs2 : s ^ 2 * r ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hr (sq_nonneg s)
    calc s ^ 2 * r ≤ s ^ 2 * (1 / (2 * s ^ 2)) := this
      _ = 1 / 2 := by field_simp
  have hr1 : r ≤ 1 / 2 := by
    refine hr.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hsr : s * r ≤ 1 / 2 := by nlinarith
  have hkey : (s + r) ^ 2 * r ≤ 9 / 8 := by
    have e : (s + r) ^ 2 * r = s ^ 2 * r + 2 * (s * r) * r + r ^ 3 := by ring
    rw [e]
    have h3 : 2 * (s * r) * r ≤ 1 / 2 := by nlinarith
    have h4 : r ^ 3 ≤ 1 / 8 := by nlinarith [sq_nonneg r]
    linarith
  calc 8 * w.re ^ 2 * |w.im| ≤ 8 * (s + r) ^ 2 * r := by
        have := mul_le_mul hsq him (abs_nonneg _) (by positivity)
        linarith
    _ ≤ 9 := by nlinarith

/-- **`‖G(z)‖ ≤ C₁ |z|² ‖f‖_b`** for `Im z ≥ 0`, `|z| ≥ 1`. -/
theorem airyQG_norm_le_sq {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) {z : ℂ} (hz : 0 ≤ z.im)
    (hz1 : 1 ≤ ‖z‖) :
    ‖airyQG f z‖ ≤ (4 * (1 + Real.exp 9) / π) * ‖z‖ ^ 2 * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
  have hpi := Real.pi_pos
  obtain ⟨h1, h2, h3⟩ := airyQ_hardy_hyp hf hfi hC hb
  have hB := (airyQ_boundary hf hfi).2
  set B : ℝ := ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ with hBdef
  have hB0 : 0 ≤ B := integral_nonneg fun x => norm_nonneg _
  set s : ℝ := ‖z‖ with hsdef
  have hs0 : 0 < s := by linarith
  set δ : ℝ := 1 / (4 * s ^ 2) with hδ
  have hδ0 : 0 < δ := by positivity
  have hzeq : (z.re : ℂ) + (z.im : ℂ) * I = z := by apply Complex.ext <;> simp
  have hexp9 : 0 < Real.exp 9 := Real.exp_pos 9
  by_cases hy : δ < z.im
  · have key := FormalResearch.Hardy.hardy_value_le h1 h2 h3 z.re (lt_of_le_of_lt hδ0.le hy)
    rw [hzeq, hB] at key
    refine key.trans ?_
    have e1 : (4 * π * z.im)⁻¹ ≤ (4 * π * δ)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith [mul_pos hpi hδ0])
    have e2 : (4 * π * δ)⁻¹ = s ^ 2 / π := by rw [hδ]; field_simp
    calc (4 * π * z.im)⁻¹ * B ≤ (4 * π * δ)⁻¹ * B := by gcongr
      _ = s ^ 2 / π * B := by rw [e2]
      _ ≤ (4 * (1 + Real.exp 9) / π) * s ^ 2 * B := by
          have : 1 ≤ 4 * (1 + Real.exp 9) := by nlinarith
          have hq : 1 / π ≤ 4 * (1 + Real.exp 9) / π := by gcongr
          calc s ^ 2 / π * B = (1 / π) * s ^ 2 * B := by ring
            _ ≤ (4 * (1 + Real.exp 9) / π) * s ^ 2 * B := by gcongr
  · push Not at hy
    set r : ℝ := z.im + δ with hr
    have hr0 : 0 < r := by linarith
    have hrle : r ≤ 1 / (2 * s ^ 2) := by
      have : r ≤ 2 * δ := by linarith
      have e : 2 * δ = 1 / (2 * s ^ 2) := by rw [hδ]; field_simp; ring
      linarith
    have hcs : |z.re| ≤ s := Complex.abs_re_le_norm z
    have hwr : ‖z - (z.re : ℂ)‖ = z.im := by
      have : z - (z.re : ℂ) = (z.im : ℂ) * I := by apply Complex.ext <;> simp
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_nonneg hz]
    have hlt : ‖z - (z.re : ℂ)‖ < r := by rw [hwr]; linarith
    have hrefl : ∀ w : ℂ, ‖w - (z.re : ℂ)‖ = r → w.im ≤ 0 →
        ‖airyQG f w‖ ≤ Real.exp 9 * ‖airyQG f (-w)‖ := by
      intro w hw hwi
      refine (airyQG_refl f hwi).trans ?_
      rw [mul_comm (Real.exp 9)]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (airy_circle_exp_le_nine hz1 hcs hr0 hrle hw)) (norm_nonneg _)
    have key := FormalResearch.Hardy.hardy_point_real_le (airyQ_differentiable_G hf) h2 h3 z.re hr0 hexp9.le hrefl hlt
    rw [hwr, hB] at key
    refine key.trans ?_
    have e1 : r - z.im = δ := by rw [hr]; ring
    rw [e1]
    have e2 : (1 + Real.exp 9) * B / (π * δ) = (4 * (1 + Real.exp 9) / π) * s ^ 2 * B := by
      rw [hδ]; field_simp
    rw [e2]

/-- **Theorem Q (2), uniform collapse (all of `ℂ`).**  For `‖u‖ ≥ 1`: `‖f(u)‖ ≤ C₁ √‖u‖ ‖f‖_b e(u)`, `C₁ = 4(1 + e⁹)/π`. -/
theorem airyQ_pointwise_uniform {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) {u : ℂ} (hu : 1 ≤ ‖u‖) :
    ‖f u‖ ≤ (4 * (1 + Real.exp 9) / π) * √‖u‖ * (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) * airyEnv u := by
  have hpi := Real.pi_pos
  set s : ℂ := u ^ (1 / 2 : ℂ) with hs
  set z : ℂ := I * s with hz
  have hzim : z.im = s.re := by simp [hz]
  have hzim0 : 0 ≤ z.im := by rw [hzim]; exact cpow_half_re_nonneg u
  have hzn : ‖z‖ = ‖s‖ := by simp [hz]
  have hsn : ‖s‖ ^ 2 = ‖u‖ := norm_cpow_half_sq u
  have hsq : -(z ^ 2) = u := by
    have : z ^ 2 = -(s ^ 2) := by rw [hz, mul_pow, Complex.I_sq]; ring
    rw [this, hs, cpow_half_sq]; ring
  have hz1 : 1 ≤ ‖z‖ := by
    rw [hzn]
    by_contra h
    push Not at h
    have : ‖s‖ ^ 2 < 1 := by nlinarith [norm_nonneg s]
    linarith
  have hzpos : 0 < ‖z‖ := by linarith
  have hG := airyQG_norm_le_sq hf hfi hC hb hzim0 hz1
  rw [airyQ_norm_G f hzim0, hsq] at hG
  have he := airyEnv_pos u
  have hnormz : ‖z‖ = √‖u‖ := by
    rw [hzn, ← hsn, Real.sqrt_sq (norm_nonneg s)]
  have hB0 : 0 ≤ ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := integral_nonneg fun x => norm_nonneg _
  have h1 : ‖z‖ * (‖f u‖ / airyEnv u) ≤ (4 * (1 + Real.exp 9) / π) * ‖z‖ ^ 2 * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := hG
  have h2 : ‖f u‖ / airyEnv u ≤ (4 * (1 + Real.exp 9) / π) * ‖z‖ * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
    have : ‖z‖ * (‖f u‖ / airyEnv u) ≤ ‖z‖ * ((4 * (1 + Real.exp 9) / π) * ‖z‖ * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) := by
      calc ‖z‖ * (‖f u‖ / airyEnv u) ≤ _ := h1
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hzpos
  rw [div_le_iff₀ he] at h2
  rw [hnormz] at h2
  exact h2

/-- **`𝒢_N ⊂ 𝒢_{1/2}`**: every `f` of the class satisfies `‖f(u)‖ ≤ C' (1+|u|)^{1/2} e(u)` on all of `ℂ`. -/
theorem airyQ_mem_half {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ u : ℂ, ‖f u‖ ≤ C' * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by
  have hpi := Real.pi_pos
  set B : ℝ := ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ with hB
  have hB0 : 0 ≤ B := integral_nonneg fun x => norm_nonneg _
  set K : ℝ := 4 * (1 + Real.exp 9) / π with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf.continuous.continuousOn
  set e₀ : ℝ := Real.exp (-(4 / 3) * (1 + 1) ^ 3) with he₀
  have he₀pos : 0 < e₀ := Real.exp_pos _
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  refine ⟨max (K * B * 2) (max M 0 / e₀), by positivity, fun u => ?_⟩
  have hE := airyEnv_pos u
  by_cases hu : 1 ≤ ‖u‖
  · have h := airyQ_pointwise_uniform hf hfi hC hb hu
    refine h.trans ?_
    have h1 : √‖u‖ ≤ (1 + ‖u‖) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow (norm_nonneg u) (by linarith) (by norm_num)
    have h2 : K * √‖u‖ * B * airyEnv u ≤ (K * B) * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by
      calc K * √‖u‖ * B * airyEnv u = (K * B) * √‖u‖ * airyEnv u := by ring
        _ ≤ (K * B) * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by gcongr
    refine h2.trans ?_
    have : K * B ≤ max (K * B * 2) (max M 0 / e₀) := by
      have := le_max_left (K * B * 2) (max M 0 / e₀)
      nlinarith [mul_nonneg hK0 hB0]
    have hp : 0 ≤ (1 + ‖u‖) ^ (1 / 2 : ℝ) := by positivity
    gcongr
  · push Not at hu
    have hmem : u ∈ closedBall (0 : ℂ) 1 := by simpa using hu.le
    have h1 := (hM u hmem).trans (le_max_left M 0)
    have h2 := airyEnv_ge_of_norm_le (R := 1) hu.le
    have hp : 1 ≤ (1 + ‖u‖) ^ (1 / 2 : ℝ) :=
      Real.one_le_rpow (by linarith [norm_nonneg u]) (by norm_num)
    calc ‖f u‖ ≤ max M 0 := h1
      _ = (max M 0 / e₀) * e₀ := by field_simp
      _ ≤ (max M 0 / e₀) * airyEnv u := by gcongr
      _ ≤ max (K * B * 2) (max M 0 / e₀) * airyEnv u := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hE.le
      _ ≤ max (K * B * 2) (max M 0 / e₀) * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by
          have hm : 0 ≤ max (K * B * 2) (max M 0 / e₀) := by positivity
          have : max (K * B * 2) (max M 0 / e₀) ≤ max (K * B * 2) (max M 0 / e₀) * (1 + ‖u‖) ^ (1 / 2 : ℝ) := by
            nlinarith
          exact mul_le_mul_of_nonneg_right this hE.le

/-- info: 'FormalResearch.Special.airyQ_pointwise_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_pointwise_uniform

/-- info: 'FormalResearch.Special.airyQ_mem_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_mem_half

end FormalResearch.Special
