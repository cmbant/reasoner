import Mathlib

/-!
# The cubic majorant of `-x ln x`

`h(x) = a x³ + b x² + c x + d` is the cubic Hermite interpolant of `f(x) = -x ln x` at the nodes
`1/6` and `1/2` (it agrees with `f` and `f'` there), and `f ≤ h` on `[0, ∞)`. This is the
spectral input of the four-qubit entropy bound.

Proof. For `x > 0` write `h(x) - f(x) = x φ(x)` with `φ(x) = ln x + a x² + b x + c + d/x`. Then
`φ'(x) = 2a (x - 1/6)(x - s)(x - 1/2) / x²` with `1/6 < s < 1/2`, so `φ` decreases to `1/6`,
increases to `s`, decreases to `1/2` and increases after it, and `φ(1/6) = φ(1/2) = 0`.
-/

namespace FormalResearch.FourQubitEntropy

/-! ### Numerical bounds on `ln 3` -/

theorem log_three_lt : Real.log 3 < 8 / 7 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.add_one_le_exp (1 / 7 : ℝ)
  have : Real.exp (8 / 7) = Real.exp 1 * Real.exp (1 / 7) := by
    rw [← Real.exp_add]; norm_num
  rw [this]
  nlinarith [Real.exp_pos (1 / 7 : ℝ), Real.exp_pos 1]

theorem lt_log_three : 16 / 15 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 15 : ℝ) < 1 / (1 - 1 / 15) :=
    Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
  have : Real.exp (16 / 15) = Real.exp 1 * Real.exp (1 / 15) := by
    rw [← Real.exp_add]; norm_num
  rw [this]
  have h3 : (1 : ℝ) / (1 - 1 / 15) = 15 / 14 := by norm_num
  rw [h3] at h2
  nlinarith [Real.exp_pos (1 / 15 : ℝ), Real.exp_pos 1]

/-! ### The majorant -/

noncomputable def hermA : ℝ := 18 * Real.log 3 - 18
noncomputable def hermB : ℝ := 18 - 39 / 2 * Real.log 3
noncomputable def hermC : ℝ := Real.log 2 + 6 * Real.log 3 - 11 / 2
noncomputable def hermD : ℝ := 1 / 2 - 3 / 8 * Real.log 3

/-- The Hermite cubic. -/
noncomputable def hermCubic (x : ℝ) : ℝ := hermA * x ^ 3 + hermB * x ^ 2 + hermC * x + hermD

theorem hermA_pos : 0 < hermA := by
  have := lt_log_three; unfold hermA; linarith

theorem hermD_pos : 0 < hermD := by
  have := log_three_lt; unfold hermD; linarith

/-- The auxiliary function `φ`. -/
noncomputable def hermPhi (x : ℝ) : ℝ :=
  Real.log x + hermA * x ^ 2 + hermB * x + hermC + hermD / x

/-- The third root of `φ'`. -/
noncomputable def hermS : ℝ := 6 * hermD / hermA

theorem hermS_gt : 1 / 6 < hermS := by
  have ha := hermA_pos
  have := log_three_lt
  unfold hermS
  rw [lt_div_iff₀ ha]
  unfold hermD hermA; nlinarith

theorem hermS_lt : hermS < 1 / 2 := by
  have ha := hermA_pos
  have := lt_log_three
  unfold hermS
  rw [div_lt_iff₀ ha]
  unfold hermD hermA; nlinarith

theorem herm_poly (x : ℝ) :
    2 * hermA * (x - 1 / 6) * (x - hermS) * (x - 1 / 2)
      = x * (1 + 2 * hermA * x ^ 2 + hermB * x) - hermD := by
  have hs : hermS * hermA = 6 * hermD := by
    have := hermA_pos.ne'
    unfold hermS; field_simp
  have e := hs
  unfold hermA hermD at e
  unfold hermA hermB hermD
  linear_combination (-2 * (x ^ 2 - 2 / 3 * x + 1 / 12)) * e

theorem hermPhi_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt hermPhi
      (2 * hermA * (x - 1 / 6) * (x - hermS) * (x - 1 / 2) / x ^ 2) x := by
  have h1 : HasDerivAt (fun x => Real.log x + hermA * x ^ 2 + hermB * x + hermC + hermD / x)
      (1 / x + hermA * (2 * x) + hermB - hermD / x ^ 2) x := by
    have := ((((Real.hasDerivAt_log hx.ne').add ((hasDerivAt_pow 2 x).const_mul hermA)).add
      ((hasDerivAt_id x).const_mul hermB)).add_const hermC).add
      ((hasDerivAt_inv hx.ne').const_mul hermD)
    convert this using 1
    · funext y; simp [div_eq_mul_inv]
    · simp [div_eq_mul_inv]; ring
  refine (show HasDerivAt hermPhi _ x from h1).congr_deriv ?_
  rw [herm_poly]
  field_simp

/-- The derivative of `φ`. -/
noncomputable def hermPhi' (x : ℝ) : ℝ :=
  2 * hermA * (x - 1 / 6) * (x - hermS) * (x - 1 / 2) / x ^ 2

theorem hermPhi_continuousOn {D : Set ℝ} (hD : D ⊆ Set.Ioi 0) : ContinuousOn hermPhi D :=
  fun _ hx => (hermPhi_deriv (hD hx)).continuousAt.continuousWithinAt

theorem hermPhi_differentiableOn {D : Set ℝ} (hD : D ⊆ Set.Ioi 0) : DifferentiableOn ℝ hermPhi D :=
  fun _ hx => (hermPhi_deriv (hD hx)).differentiableAt.differentiableWithinAt

theorem hermPhi_monotoneOn {D : Set ℝ} (hc : Convex ℝ D) (hD : D ⊆ Set.Ioi 0)
    (h : ∀ x ∈ interior D, 0 ≤ hermPhi' x) : MonotoneOn hermPhi D := by
  refine monotoneOn_of_deriv_nonneg hc (hermPhi_continuousOn hD)
    (hermPhi_differentiableOn ((interior_subset).trans hD)) fun x hx => ?_
  rw [(hermPhi_deriv (hD (interior_subset hx))).deriv]
  exact h x hx

theorem hermPhi_antitoneOn {D : Set ℝ} (hc : Convex ℝ D) (hD : D ⊆ Set.Ioi 0)
    (h : ∀ x ∈ interior D, hermPhi' x ≤ 0) : AntitoneOn hermPhi D := by
  refine antitoneOn_of_deriv_nonpos hc (hermPhi_continuousOn hD)
    (hermPhi_differentiableOn ((interior_subset).trans hD)) fun x hx => ?_
  rw [(hermPhi_deriv (hD (interior_subset hx))).deriv]
  exact h x hx

theorem hermPhi_at_p : hermPhi (1 / 6) = 0 := by
  unfold hermPhi
  rw [one_div, Real.log_inv, show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  unfold hermA hermB hermC hermD
  field_simp
  ring

theorem hermPhi_at_q : hermPhi (1 / 2) = 0 := by
  unfold hermPhi
  rw [one_div, Real.log_inv]
  unfold hermA hermB hermC hermD
  field_simp
  ring

section Signs

variable {u v w : ℝ}

theorem sign_neg_neg_neg (hu : u ≤ 0) (hv : v ≤ 0) (hw : w ≤ 0) :
    2 * hermA * u * v * w ≤ 0 := by
  have ha := hermA_pos
  have e1 : 2 * hermA * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hu
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg_of_nonpos_of_nonpos e1 hv) hw

theorem sign_pos_neg_neg (hu : 0 ≤ u) (hv : v ≤ 0) (hw : w ≤ 0) :
    0 ≤ 2 * hermA * u * v * w := by
  have ha := hermA_pos
  have e1 : 0 ≤ 2 * hermA * u := by positivity
  exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos e1 hv) hw

theorem sign_pos_pos_neg (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : w ≤ 0) :
    2 * hermA * u * v * w ≤ 0 := by
  have ha := hermA_pos
  have e1 : 0 ≤ 2 * hermA * u * v := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos e1 hw

theorem sign_pos_pos_pos (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    0 ≤ 2 * hermA * u * v * w := by
  have ha := hermA_pos
  positivity

end Signs

/-- `φ ≥ 0` on `(0, ∞)`. -/
theorem hermPhi_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ hermPhi x := by
  have hs1 := hermS_gt
  have hs2 := hermS_lt
  have hp := hermPhi_at_p
  have hq := hermPhi_at_q
  rcases le_or_gt x (1 / 6) with h1 | h1
  · -- decreasing on (0, 1/6]
    have hm := hermPhi_antitoneOn (D := Set.Ioc 0 (1 / 6)) (convex_Ioc _ _)
      (fun y hy => hy.1) (by
        intro y hy
        rw [interior_Ioc] at hy
        exact div_nonpos_of_nonpos_of_nonneg
          (sign_neg_neg_neg (by linarith [hy.2]) (by linarith [hy.2]) (by linarith [hy.2]))
          (sq_nonneg _))
    have := hm ⟨hx, h1⟩ ⟨by norm_num, le_refl _⟩ h1
    linarith
  rcases le_or_gt x hermS with h2 | h2
  · have hm := hermPhi_monotoneOn (D := Set.Icc (1 / 6) hermS) (convex_Icc _ _)
      (fun y hy => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 6) hy.1) (by
        intro y hy
        rw [interior_Icc] at hy
        exact div_nonneg
          (sign_pos_neg_neg (by linarith [hy.1]) (by linarith [hy.2]) (by linarith [hy.2]))
          (sq_nonneg _))
    have := hm ⟨le_refl _, hs1.le⟩ ⟨h1.le, h2⟩ h1.le
    linarith
  rcases le_or_gt x (1 / 2) with h3 | h3
  · have hm := hermPhi_antitoneOn (D := Set.Icc hermS (1 / 2)) (convex_Icc _ _)
      (fun y hy => lt_of_lt_of_le (by linarith) hy.1) (by
        intro y hy
        rw [interior_Icc] at hy
        exact div_nonpos_of_nonpos_of_nonneg
          (sign_pos_pos_neg (by linarith [hy.1]) (by linarith [hy.1]) (by linarith [hy.2]))
          (sq_nonneg _))
    have := hm ⟨h2.le, h3⟩ ⟨hs2.le, le_refl _⟩ h3
    linarith
  · have hm := hermPhi_monotoneOn (D := Set.Ici (1 / 2)) (convex_Ici _)
      (fun y hy => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hy) (by
        intro y hy
        rw [interior_Ici] at hy
        have hy' : 1 / 2 < y := hy
        exact div_nonneg
          (sign_pos_pos_pos (by linarith) (by linarith) (by linarith))
          (sq_nonneg _))
    have := hm (Set.mem_Ici.2 (le_refl _)) (Set.mem_Ici.2 h3.le) h3.le
    linarith

/-- **Cubic majorant.** `-x ln x ≤ a x³ + b x² + c x + d` for `x ≥ 0`. -/
theorem negMulLog_le_hermCubic {x : ℝ} (hx : 0 ≤ x) : Real.negMulLog x ≤ hermCubic x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [hermCubic, hermD_pos.le]
  · have h := hermPhi_nonneg hx
    unfold hermPhi at h
    unfold Real.negMulLog hermCubic
    have : hermCubic x - Real.negMulLog x = x * hermPhi x := by
      unfold hermCubic Real.negMulLog hermPhi; field_simp; ring
    unfold hermPhi at this
    unfold hermCubic Real.negMulLog at this
    nlinarith [mul_nonneg hx.le h]

end FormalResearch.FourQubitEntropy
