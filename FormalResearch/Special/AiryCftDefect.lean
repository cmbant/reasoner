module

public import FormalResearch.Special.AiryCftResidue
public import FormalResearch.Special.AiryCftZeros

/-!
# The residue-defect formula (Theorem D) on a good circle

Statement formalised (CFT/PR240 `AIRY_POISSON.md` Theorem D, proof there): for `f` entire and a zero-free circle `|u| = R`
enclosing the zeros `a_1, …, a_N` of `Ai`,

`P_R(f) = I_R(f) + (i/2)(A₊ + A₋)`,  `P_R(f) = Σ_{n ≤ N} f(a_n)/Ai'(a_n)²`,  `I_R(f) = ∫_{-R}^{R} f`,
`A₊ = ∫_{upper semicircle, R → -R} f R₊ du`, `A₋ = ∫_{lower semicircle, -R → R} f R₋ du`,
`R_± = (Bi ∓ iAi)/Ai`,

(the exact identity is an intermediate step of the proof of `airy_defect_bound`, not a separate Lean statement; the Lean
statement is the consequence)
and hence `|P_R(f) - I_R(f)| ≤ π R M` whenever `|f R_±| ≤ M` on the respective half circles
(`airy_defect_bound`; with the good-circle bounds `|R_±| e ≤ 30√π` of `AiryRatioBounds`, `M = 30√π · sup |f|/e`).

Proof here: the residue formula `cftCircle_residue` for `H = f Bi` and `Bi(a_n) = -1/(π Ai'(a_n))` (Wronskian) gives
`∮ f Bi/Ai = -2i P_R(f)`; on the upper (lower) half circle `Bi/Ai = R₊ + i` (`R₋ - i`); the `± i f` terms integrate over
the half circles by the fundamental theorem of calculus for an entire primitive `F` of `f` (Mathlib's
`Differentiable.isExactOn_univ`) to `∓ i (F(R) - F(-R))`, i.e. `-2i I_R(f)` in total.

Numerical check (mpmath, 70 digits): for `f(u) = (1+u) exp(-u²/50)` and the good circle `r = 10.52897…` (`k = 10`, seven
zeros inside) `P_r(f) = -16.95620038226354106191554…` and `I_r(f) + (i/2)(A₊ + A₋)` agree to `1.3·10⁻⁵⁰` (the quadrature
of `A_±` needs the high precision because `|R_+| ~ 1/e` is huge on the positive axis).

Here `f` is entire (the Cauchy step is the explicit primitive); the case of `f` only holomorphic near the closed disc
(the note's remark for `REMAINDER.md` Theorem L*) is `AiryCft2Ball` (`cft2_defect_ball`, `airy_defect_ball`), the general
pair `(N, M)` is `AiryCft2Generic` (`cft2_defect_bound`).  All proved.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.Special

/-- Arc integral of `f dw` against an entire primitive. -/
lemma cftDef_arc {F f : ℂ → ℂ} (hF : ∀ z, HasDerivAt F (f z) z) (hf : Continuous f) (R a b : ℝ) :
    ∫ θ in a..b, (circleMap 0 R θ * I) * f (circleMap 0 R θ) =
      F (circleMap 0 R b) - F (circleMap 0 R a) := by
  refine integral_eq_sub_of_hasDerivAt (f := fun θ : ℝ => F (circleMap 0 R θ))
    (f' := fun θ : ℝ => (circleMap 0 R θ * I) * f (circleMap 0 R θ)) (fun θ _ => ?_) ?_
  · have := (hF (circleMap 0 R θ)).scomp θ (hasDerivAt_circleMap 0 R θ)
    rw [smul_eq_mul] at this
    exact this
  · refine Continuous.intervalIntegrable ?_ _ _
    have : Continuous (circleMap 0 R) := continuous_circleMap 0 R
    fun_prop

lemma cftDef_diam {F f : ℂ → ℂ} (hF : ∀ z, HasDerivAt F (f z) z) (hf : Continuous f) (R : ℝ) :
    ∫ x in (-R)..R, f (x : ℂ) = F (R : ℂ) - F ((-R : ℝ) : ℂ) := by
  refine integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => F (x : ℂ)) (f' := fun x : ℝ => f (x : ℂ))
    (fun x _ => (hF (x : ℂ)).comp_ofReal) ?_
  exact (hf.comp Complex.continuous_ofReal).intervalIntegrable _ _

lemma cftDef_circleMap_zero (R : ℝ) : circleMap 0 R 0 = (R : ℂ) := by simp [circleMap]

lemma cftDef_circleMap_pi (R : ℝ) : circleMap 0 R π = ((-R : ℝ) : ℂ) := by
  simp [circleMap, Complex.exp_pi_mul_I]

lemma cftDef_circleMap_two_pi (R : ℝ) : circleMap 0 R (2 * π) = (R : ℂ) := by
  simp [circleMap, Complex.exp_two_pi_mul_I]

lemma cftDef_im_circleMap (R θ : ℝ) : (circleMap 0 R θ).im = R * Real.sin θ := by
  simp [circleMap, Complex.exp_ofReal_mul_I_im]

/-- `Bi(a_n) = -1/(π Ai'(a_n))` (Wronskian at a zero). -/
lemma cftDef_airyBiC_at_zero (n : ℕ) :
    airyBiC (airyZero n : ℂ) = -(1 / (π * deriv airyAiC (airyZero n : ℂ))) := by
  have hW := airyAiC_wronskian_airyBiC_eq (airyZero n : ℂ)
  rw [airyAiC_ofReal, airyAi_airyZero] at hW
  have hd := airyZero_deriv_ne_zero n
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [Complex.ofReal_zero, zero_mul, zero_sub] at hW
  push_cast at hW
  have h1 : airyBiC (airyZero n : ℂ) * deriv airyAiC (airyZero n : ℂ) = -(1 / (π : ℂ)) := by
    linear_combination -hW
  calc airyBiC (airyZero n : ℂ)
      = (airyBiC (airyZero n : ℂ) * deriv airyAiC (airyZero n : ℂ)) / deriv airyAiC (airyZero n : ℂ) := by
        field_simp
    _ = -(1 / (π : ℂ)) / deriv airyAiC (airyZero n : ℂ) := by rw [h1]
    _ = _ := by field_simp

/-- **Residue identity**: `∮_{|w|=R} f Bi/Ai = -2i Σ_{n ≤ N} f(a_n)/Ai'(a_n)²` for entire `f`. -/
lemma cftDef_residue {N : ℕ} {R : ℝ}
    (hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ∮ w in C(0, R), f w * airyBiC w / airyAiC w =
      -2 * I * ∑ n ∈ Finset.Icc 1 N, f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2 := by
  have h := cftCircle_residue hD (H := fun w => f w * airyBiC w) (hf.mul differentiable_airyBiC)
  rw [h, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [cftDef_airyBiC_at_zero n]
  have hd := airyZero_deriv_ne_zero n
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- **Theorem D (defect bound)** on a good circle: for `f` entire, if `‖f R_+‖ ≤ M` on the upper half circle and
`‖f R_-‖ ≤ M` on the lower one (`R_± = (Bi ∓ iAi)/Ai`), then
`‖Σ_{n ≤ N} f(a_n)/Ai'(a_n)² - ∫_{-R}^{R} f‖ ≤ π R M`. -/
theorem airy_defect_bound {N : ℕ} {R : ℝ}
    (hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {M : ℝ}
    (hp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im →
      ‖f w * ((airyBiC w - I * airyAiC w) / airyAiC w)‖ ≤ M)
    (hm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 →
      ‖f w * ((airyBiC w + I * airyAiC w) / airyAiC w)‖ ≤ M) :
    ‖(∑ n ∈ Finset.Icc 1 N, f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2) -
        ∫ x in (-R)..R, f (x : ℂ)‖ ≤ π * R * M := by
  have hR := hD.radius_pos
  obtain ⟨F, hF0, hF⟩ := (Differentiable.isExactOn_univ hf).with_val_at 0 0
  have hF' : ∀ z, HasDerivAt F (f z) z := fun z => hF z trivial
  set w : ℝ → ℂ := circleMap 0 R with hw
  have hwn : ∀ θ, ‖w θ‖ = R := fun θ => by
    rw [hw, norm_circleMap_zero, abs_of_pos hR]
  have hAi : ∀ θ, airyAiC (w θ) ≠ 0 := fun θ => hD.ne_zero_sphere (hwn θ)
  have hwc : Continuous w := continuous_circleMap 0 R
  set J : ℝ → ℂ := fun θ => (w θ * I) * f (w θ) with hJ
  have hJc : Continuous J := by rw [hJ]; have := hf.continuous; fun_prop
  set Rp : ℝ → ℂ := fun θ => (airyBiC (w θ) - I * airyAiC (w θ)) / airyAiC (w θ) with hRp
  set Rm : ℝ → ℂ := fun θ => (airyBiC (w θ) + I * airyAiC (w θ)) / airyAiC (w θ) with hRm
  have hBc : Continuous (fun θ => airyBiC (w θ)) := differentiable_airyBiC.continuous.comp hwc
  have hAc : Continuous (fun θ => airyAiC (w θ)) := differentiable_airyAiC.continuous.comp hwc
  have hRpc : Continuous Rp := by
    rw [hRp]; exact (hBc.sub (continuous_const.mul hAc)).div hAc hAi
  have hRmc : Continuous Rm := by
    rw [hRm]; exact (hBc.add (continuous_const.mul hAc)).div hAc hAi
  -- the circle integral as a `θ`-integral
  have hcirc : ∮ z in C(0, R), f z * airyBiC z / airyAiC z =
      ∫ θ in (0 : ℝ)..(2 * π), J θ * (airyBiC (w θ) / airyAiC (w θ)) := by
    rw [circleIntegral]
    refine integral_congr fun θ _ => ?_
    simp only [deriv_circleMap, smul_eq_mul, hJ, hw]
    ring
  have hΦc : Continuous (fun θ => J θ * (airyBiC (w θ) / airyAiC (w θ))) :=
    hJc.mul (hBc.div hAc hAi)
  -- upper and lower halves
  have hup : ∫ θ in (0 : ℝ)..π, J θ * (airyBiC (w θ) / airyAiC (w θ)) =
      (∫ θ in (0 : ℝ)..π, J θ * Rp θ) + I * (∫ θ in (0 : ℝ)..π, J θ) := by
    have h1 : IntervalIntegrable (fun θ => J θ * Rp θ) volume 0 π := (hJc.mul hRpc).intervalIntegrable 0 π
    have h2 : IntervalIntegrable (fun θ => I * J θ) volume 0 π := (hJc.const_mul I).intervalIntegrable 0 π
    rw [← intervalIntegral.integral_const_mul, ← integral_add h1 h2]
    refine integral_congr fun θ _ => ?_
    simp only [hRp]
    have := hAi θ
    field_simp
    ring
  have hlow : ∫ θ in π..(2 * π), J θ * (airyBiC (w θ) / airyAiC (w θ)) =
      (∫ θ in π..(2 * π), J θ * Rm θ) - I * (∫ θ in π..(2 * π), J θ) := by
    have h1 : IntervalIntegrable (fun θ => J θ * Rm θ) volume π (2 * π) :=
      (hJc.mul hRmc).intervalIntegrable π (2 * π)
    have h2 : IntervalIntegrable (fun θ => I * J θ) volume π (2 * π) :=
      (hJc.const_mul I).intervalIntegrable π (2 * π)
    rw [← intervalIntegral.integral_const_mul, ← integral_sub h1 h2]
    refine integral_congr fun θ _ => ?_
    simp only [hRm]
    have := hAi θ
    field_simp
    ring
  have hJup : ∫ θ in (0 : ℝ)..π, J θ = F (-(R : ℂ)) - F R := by
    have := cftDef_arc hF' hf.continuous R 0 π
    rw [cftDef_circleMap_pi, cftDef_circleMap_zero] at this
    simpa using this
  have hJlow : ∫ θ in π..(2 * π), J θ = F R - F (-(R : ℂ)) := by
    have := cftDef_arc hF' hf.continuous R π (2 * π)
    rw [cftDef_circleMap_pi, cftDef_circleMap_two_pi] at this
    simpa using this
  have hdiam := cftDef_diam hF' hf.continuous R
  have hdiam' : ∫ x in (-R)..R, f (x : ℂ) = F R - F (-(R : ℂ)) := by simpa using hdiam
  have hres := cftDef_residue hD hf
  rw [hcirc, ← integral_add_adjacent_intervals (hΦc.intervalIntegrable 0 π)
    (hΦc.intervalIntegrable π (2 * π)), hup, hlow, hJup, hJlow] at hres
  -- estimates on the two arcs
  have hA1 : ‖∫ θ in (0 : ℝ)..π, J θ * Rp θ‖ ≤ R * M * |π - 0| := by
    refine norm_integral_le_of_norm_le_const (fun θ hθ => ?_)
    rw [Set.uIoc_of_le Real.pi_pos.le] at hθ
    have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2
    have him : 0 ≤ (w θ).im := by rw [hw, cftDef_im_circleMap]; positivity
    have := hp (w θ) (hwn θ) him
    simp only [hJ, hRp]
    rw [norm_mul, norm_mul, norm_mul, hwn θ, Complex.norm_I, mul_one, mul_assoc, ← norm_mul]
    exact mul_le_mul_of_nonneg_left this hR.le
  have hA2 : ‖∫ θ in π..(2 * π), J θ * Rm θ‖ ≤ R * M * |2 * π - π| := by
    refine norm_integral_le_of_norm_le_const (fun θ hθ => ?_)
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
    have hsin : Real.sin θ ≤ 0 := by
      have h1 := Real.sin_nonneg_of_nonneg_of_le_pi (x := θ - π) (by linarith [hθ.1]) (by linarith [hθ.2])
      rw [Real.sin_sub_pi] at h1
      linarith
    have him : (w θ).im ≤ 0 := by
      rw [hw, cftDef_im_circleMap]; nlinarith
    have := hm (w θ) (hwn θ) him
    simp only [hJ, hRm]
    rw [norm_mul, norm_mul, norm_mul, hwn θ, Complex.norm_I, mul_one, mul_assoc, ← norm_mul]
    exact mul_le_mul_of_nonneg_left this hR.le
  -- assemble
  obtain ⟨S, hSdef⟩ : ∃ S : ℂ, S = ∑ n ∈ Finset.Icc 1 N, f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨A1, hA1def⟩ : ∃ A : ℂ, A = ∫ θ in (0 : ℝ)..π, J θ * Rp θ := ⟨_, rfl⟩
  obtain ⟨A2, hA2def⟩ : ∃ A : ℂ, A = ∫ θ in π..(2 * π), J θ * Rm θ := ⟨_, rfl⟩
  rw [← hSdef, ← hA1def, ← hA2def] at hres
  rw [← hA1def] at hA1
  rw [← hA2def] at hA2
  rw [← hSdef]
  have key : S - (∫ x in (-R)..R, f (x : ℂ)) = (I / 2) * (A1 + A2) := by
    rw [hdiam']
    have hI : I * I = -1 := Complex.I_mul_I
    linear_combination (-(I / 2)) * hres + (S - (F R - F (-(R : ℂ)))) * hI
  have hfin : ‖S - ∫ x in (-R)..R, f (x : ℂ)‖ ≤ π * R * M := by
    rw [key, norm_mul]
    have h2 : ‖I / 2‖ = 1 / 2 := by simp
    rw [h2]
    have h3 : ‖A1 + A2‖ ≤ 2 * (π * R * M) := by
      have := norm_add_le A1 A2
      rw [abs_of_pos (by linarith [Real.pi_pos] : (0 : ℝ) < π - 0)] at hA1
      rw [abs_of_pos (by linarith [Real.pi_pos] : (0 : ℝ) < 2 * π - π)] at hA2
      nlinarith
    linarith
  exact hfin

/-- info: 'FormalResearch.Special.airy_defect_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_defect_bound

end FormalResearch.Special
