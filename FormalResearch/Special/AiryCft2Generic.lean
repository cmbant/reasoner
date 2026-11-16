module

public import FormalResearch.Special.AiryCftDefect

/-!
# The residue-defect formula for a general pair `(N, M)` of entire functions

Generic complex analysis (no Airy function here): the proof of `airy_defect_bound` (Theorem D, `AiryCftDefect`) rewritten for
an arbitrary entire `N` with finitely many simple zeros `S ⊂ {|w| < R}` and an entire `M` (for the Airy case `N = Ai`,
`M = Bi`; for the Clark functions `N = P Ai + Q Ai'`, `M = P Bi + Q Bi'`, `AiryCft2ComboQuadrature`).

* `cft2_circleData_of_finset`: a `Finset ℂ` of zeros (instead of the `ℕ`-indexed list of `CftCircleData`): if `S` is a finite
  set of simple zeros of the entire `N`, all in `|w| < R`, and contains every zero in `|w| ≤ R`, then there are `c : ℕ → ℂ`,
  `s : Finset ℕ` with `CftCircleData N c s R` and `Σ_{i∈s} g(c_i) = Σ_{t∈S} g(t)` for all `g`.
* `cft2_defect_bound`: for entire `f` and `‖f (M/N - i)‖ ≤ B` on the upper half circle, `‖f (M/N + i)‖ ≤ B` on the lower
  half circle (`|w| = R`, `N ≠ 0` there):
  `‖-π Σ_{t∈S} f(t) M(t)/N'(t) - ∫_{-R}^{R} f‖ ≤ π R B`.

The weights `-π M(t)/N'(t)` are, for the Clark pair, `D(t)/N'(t)²` (`AiryCft2ComboQuadrature`).  Proved here: the
Cauchy-Goursat/primitive step is as in `AiryCftDefect` (entire `f`; the case `f` holomorphic only near the closed disc needs the
residue formula for `H` holomorphic on a disc and is not formalised).
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.Special

/-- A `Finset ℂ` of zeros as a `CftCircleData`. -/
lemma cft2_circleData_of_finset {f : ℂ → ℂ} {R : ℝ} (hf : Differentiable ℂ f) (hR : 0 < R) (S : Finset ℂ)
    (hin : ∀ t ∈ S, ‖t‖ < R) (hz : ∀ t ∈ S, f t = 0) (hs : ∀ t ∈ S, deriv f t ≠ 0)
    (hc : ∀ w : ℂ, ‖w‖ ≤ R → f w = 0 → w ∈ S) :
    ∃ (c : ℕ → ℂ) (s : Finset ℕ), CftCircleData f c s R ∧ ∀ g : ℂ → ℂ, ∑ i ∈ s, g (c i) = ∑ t ∈ S, g t := by
  classical
  set c : ℕ → ℂ := fun i => if h : i < S.card then ((S.equivFin.symm ⟨i, h⟩ : S) : ℂ) else 0 with hcdef
  have hcmem : ∀ i, i < S.card → c i ∈ S := by
    intro i hi
    rw [hcdef]; simp only [hi, dite_true]
    exact (S.equivFin.symm ⟨i, hi⟩).2
  refine ⟨c, Finset.range S.card, ⟨hf, hR, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi j hj hij
    have hi' : i < S.card := Finset.mem_range.mp hi
    have hj' : j < S.card := Finset.mem_range.mp hj
    simp only [hcdef, hi', hj', dite_true] at hij
    have := Subtype.ext hij
    have := S.equivFin.symm.injective this
    simpa using this
  · intro i hi
    exact hin _ (hcmem i (Finset.mem_range.mp hi))
  · intro i hi
    exact hz _ (hcmem i (Finset.mem_range.mp hi))
  · intro i hi
    exact hs _ (hcmem i (Finset.mem_range.mp hi))
  · intro w hw hw0
    have hwS := hc w hw hw0
    refine ⟨(S.equivFin ⟨w, hwS⟩ : ℕ), Finset.mem_range.mpr (S.equivFin ⟨w, hwS⟩).2, ?_⟩
    simp only [hcdef, (S.equivFin ⟨w, hwS⟩).2, dite_true, Fin.eta, Equiv.symm_apply_apply]
  · intro g
    rw [Finset.sum_range]
    have : ∀ i : Fin S.card, g (c i) = g ((S.equivFin.symm i : S) : ℂ) := by
      intro i
      simp only [hcdef, i.2, dite_true, Fin.eta]
    simp_rw [this]
    rw [← Finset.sum_coe_sort S g]
    exact Equiv.sum_comp S.equivFin.symm (fun x : S => g (x : ℂ))

/-- **Residue-defect bound for a general pair `(N, M)`.** `N`, `M`, `f` entire; `S` the finite set of the (simple) zeros of `N`
in `|w| ≤ R` (all in `|w| < R`).  If `‖f (M/N - i)‖ ≤ B` on the upper half circle and `‖f (M/N + i)‖ ≤ B` on the lower one,
then `‖-π Σ_{t∈S} f(t) M(t)/N'(t) - ∫_{-R}^{R} f‖ ≤ π R B`. -/
theorem cft2_defect_bound {N M f : ℂ → ℂ} {R : ℝ} (hN : Differentiable ℂ N) (hM : Differentiable ℂ M)
    (hf : Differentiable ℂ f) (hR : 0 < R) (S : Finset ℂ)
    (hin : ∀ t ∈ S, ‖t‖ < R) (hz : ∀ t ∈ S, N t = 0) (hs : ∀ t ∈ S, deriv N t ≠ 0)
    (hc : ∀ w : ℂ, ‖w‖ ≤ R → N w = 0 → w ∈ S) {B : ℝ}
    (hp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im → ‖f w * (M w / N w - I)‖ ≤ B)
    (hm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 → ‖f w * (M w / N w + I)‖ ≤ B) :
    ‖(-(π : ℂ)) * (∑ t ∈ S, f t * M t / deriv N t) - ∫ x in (-R)..R, f (x : ℂ)‖ ≤ π * R * B := by
  obtain ⟨c, s, hD, hsum⟩ := cft2_circleData_of_finset hN hR S hin hz hs hc
  obtain ⟨F, hF0, hF⟩ := (Differentiable.isExactOn_univ hf).with_val_at 0 0
  have hF' : ∀ z, HasDerivAt F (f z) z := fun z => hF z trivial
  set w : ℝ → ℂ := circleMap 0 R with hw
  have hwn : ∀ θ, ‖w θ‖ = R := fun θ => by
    rw [hw, norm_circleMap_zero, abs_of_pos hR]
  have hNw : ∀ θ, N (w θ) ≠ 0 := fun θ => hD.ne_zero_sphere (hwn θ)
  have hwc : Continuous w := continuous_circleMap 0 R
  set J : ℝ → ℂ := fun θ => (w θ * I) * f (w θ) with hJ
  have hJc : Continuous J := by rw [hJ]; have := hf.continuous; fun_prop
  set Rp : ℝ → ℂ := fun θ => M (w θ) / N (w θ) - I with hRp
  set Rm : ℝ → ℂ := fun θ => M (w θ) / N (w θ) + I with hRm
  have hMc : Continuous (fun θ => M (w θ)) := hM.continuous.comp hwc
  have hNc : Continuous (fun θ => N (w θ)) := hN.continuous.comp hwc
  have hQc : Continuous (fun θ => M (w θ) / N (w θ)) := hMc.div hNc hNw
  have hRpc : Continuous Rp := by rw [hRp]; exact hQc.sub continuous_const
  have hRmc : Continuous Rm := by rw [hRm]; exact hQc.add continuous_const
  -- the circle integral as a `θ`-integral
  have hcirc : ∮ z in C(0, R), f z * M z / N z =
      ∫ θ in (0 : ℝ)..(2 * π), J θ * (M (w θ) / N (w θ)) := by
    rw [circleIntegral]
    refine integral_congr fun θ _ => ?_
    simp only [deriv_circleMap, smul_eq_mul, hJ, hw]
    ring
  have hΦc : Continuous (fun θ => J θ * (M (w θ) / N (w θ))) := hJc.mul hQc
  have hup : ∫ θ in (0 : ℝ)..π, J θ * (M (w θ) / N (w θ)) =
      (∫ θ in (0 : ℝ)..π, J θ * Rp θ) + I * (∫ θ in (0 : ℝ)..π, J θ) := by
    have h1 : IntervalIntegrable (fun θ => J θ * Rp θ) volume 0 π := (hJc.mul hRpc).intervalIntegrable 0 π
    have h2 : IntervalIntegrable (fun θ => I * J θ) volume 0 π := (hJc.const_mul I).intervalIntegrable 0 π
    rw [← intervalIntegral.integral_const_mul, ← integral_add h1 h2]
    refine integral_congr fun θ _ => ?_
    simp only [hRp]
    ring
  have hlow : ∫ θ in π..(2 * π), J θ * (M (w θ) / N (w θ)) =
      (∫ θ in π..(2 * π), J θ * Rm θ) - I * (∫ θ in π..(2 * π), J θ) := by
    have h1 : IntervalIntegrable (fun θ => J θ * Rm θ) volume π (2 * π) :=
      (hJc.mul hRmc).intervalIntegrable π (2 * π)
    have h2 : IntervalIntegrable (fun θ => I * J θ) volume π (2 * π) :=
      (hJc.const_mul I).intervalIntegrable π (2 * π)
    rw [← intervalIntegral.integral_const_mul, ← integral_sub h1 h2]
    refine integral_congr fun θ _ => ?_
    simp only [hRm]
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
  -- the residue formula
  have hres : ∮ z in C(0, R), f z * M z / N z =
      2 * π * I * ∑ t ∈ S, f t * M t / deriv N t := by
    have h := cftCircle_residue hD (H := fun z => f z * M z) (hf.mul hM)
    rw [h]
    congr 1
    exact hsum (fun t => f t * M t / deriv N t)
  rw [hcirc, ← integral_add_adjacent_intervals (hΦc.intervalIntegrable 0 π)
    (hΦc.intervalIntegrable π (2 * π)), hup, hlow, hJup, hJlow] at hres
  -- estimates on the two arcs
  have hA1 : ‖∫ θ in (0 : ℝ)..π, J θ * Rp θ‖ ≤ R * B * |π - 0| := by
    refine norm_integral_le_of_norm_le_const (fun θ hθ => ?_)
    rw [Set.uIoc_of_le Real.pi_pos.le] at hθ
    have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2
    have him : 0 ≤ (w θ).im := by rw [hw, cftDef_im_circleMap]; positivity
    have := hp (w θ) (hwn θ) him
    simp only [hJ, hRp]
    rw [norm_mul, norm_mul, norm_mul, hwn θ, Complex.norm_I, mul_one, mul_assoc, ← norm_mul]
    exact mul_le_mul_of_nonneg_left this hR.le
  have hA2 : ‖∫ θ in π..(2 * π), J θ * Rm θ‖ ≤ R * B * |2 * π - π| := by
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
  obtain ⟨T, hTdef⟩ : ∃ T : ℂ, T = ∑ t ∈ S, f t * M t / deriv N t := ⟨_, rfl⟩
  obtain ⟨A1, hA1def⟩ : ∃ A : ℂ, A = ∫ θ in (0 : ℝ)..π, J θ * Rp θ := ⟨_, rfl⟩
  obtain ⟨A2, hA2def⟩ : ∃ A : ℂ, A = ∫ θ in π..(2 * π), J θ * Rm θ := ⟨_, rfl⟩
  rw [← hTdef, ← hA1def, ← hA2def] at hres
  rw [← hA1def] at hA1
  rw [← hA2def] at hA2
  rw [← hTdef]
  have key : (-(π : ℂ)) * T - (∫ x in (-R)..R, f (x : ℂ)) = (I / 2) * (A1 + A2) := by
    rw [hdiam']
    have hI : I * I = -1 := Complex.I_mul_I
    -- hres : 2πi T = A1 + iJ₁ + A2 - iJ₂ with J₁ = F(-R) - F R, J₂ = F R - F(-R)
    linear_combination (-(I / 2)) * hres - ((π : ℂ) * T + (F R - F (-(R : ℂ)))) * hI
  have hfin : ‖(-(π : ℂ)) * T - ∫ x in (-R)..R, f (x : ℂ)‖ ≤ π * R * B := by
    rw [key, norm_mul]
    have h2 : ‖I / 2‖ = 1 / 2 := by simp
    rw [h2]
    have h3 : ‖A1 + A2‖ ≤ 2 * (π * R * B) := by
      have := norm_add_le A1 A2
      rw [abs_of_pos (by linarith [Real.pi_pos] : (0 : ℝ) < π - 0)] at hA1
      rw [abs_of_pos (by linarith [Real.pi_pos] : (0 : ℝ) < 2 * π - π)] at hA2
      nlinarith
    linarith
  exact hfin

/-- info: 'FormalResearch.Special.cft2_circleData_of_finset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.cft2_circleData_of_finset

/-- info: 'FormalResearch.Special.cft2_defect_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.cft2_defect_bound

end FormalResearch.Special
