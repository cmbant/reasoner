import FormalResearch.FourQubitEntropy.Majorant
import FormalResearch.FourQubitEntropy.HermiteMajorant

/-!
# The Hermite cubic of the Tsallis function majorizes it

For `0 < q < 2`, `q ≠ 1`, the function `f_q(x) = (x^q - x)/(1 - q)` (`f_q(0) = 0`) has
`f_q''' = q(2-q) x^{q-3} > 0` strictly decreasing, so by `hermite_positivity` its cubic Hermite
interpolant at `1/6, 1/2` majorizes it strictly off the nodes, and has positive cubic
coefficient. The explicit coefficients (in terms of `A = 6^{-q}`, `B = 2^{-q}`) are those of the
paper's divided-difference computation.

Paper: proof of `cor:fqe-tsallis` (spectral_corollaries.tex).
-/

namespace FormalResearch.FourQubitEntropy

open Real

/-- The Tsallis function `f_q(x) = (x^q - x)/(1 - q)`. -/
noncomputable def tsallisF (q x : ℝ) : ℝ := (x ^ q - x) / (1 - q)

/-- Hermite coefficients, `A = (1/6)^q`, `B = (1/2)^q`. -/
noncomputable def tsA (q : ℝ) : ℝ :=
  18 * (3 * (1 / 6 : ℝ) ^ q * q + 3 * (1 / 6 : ℝ) ^ q + (1 / 2 : ℝ) ^ q * q - 3 * (1 / 2 : ℝ) ^ q) / (1 - q)
noncomputable def tsB (q : ℝ) : ℝ :=
  3 * (21 * (1 / 6 : ℝ) ^ q * q + 18 * (1 / 6 : ℝ) ^ q + 5 * (1 / 2 : ℝ) ^ q * q - 18 * (1 / 2 : ℝ) ^ q) / (q - 1)
noncomputable def tsC (q : ℝ) : ℝ :=
  -(45 * (1 / 6 : ℝ) ^ q * q + 27 * (1 / 6 : ℝ) ^ q + 7 * (1 / 2 : ℝ) ^ q * q - 27 * (1 / 2 : ℝ) ^ q - 2) / (2 * (q - 1))
noncomputable def tsD (q : ℝ) : ℝ :=
  (9 * (1 / 6 : ℝ) ^ q * q + (1 / 2 : ℝ) ^ q * q - 4 * (1 / 2 : ℝ) ^ q) / (4 * (q - 1))

theorem tsF_d0 (q : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (tsallisF q) ((q * x ^ (q - 1) - 1) / (1 - q)) x := by
  have h := ((Real.hasDerivAt_rpow_const (p := q) (Or.inl hx.ne')).sub (hasDerivAt_id x)).div_const (1 - q)
  exact h

theorem tsF_d1 {q : ℝ} (hq : q ≠ 1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => (q * x ^ (q - 1) - 1) / (1 - q)) (-q * x ^ (q - 2)) x := by
  have h := (((Real.hasDerivAt_rpow_const (p := q - 1) (Or.inl hx.ne')).const_mul q).sub_const 1).div_const
    (1 - q)
  refine h.congr_deriv ?_
  have h1 : (1 - q) ≠ 0 := sub_ne_zero.2 (Ne.symm hq)
  rw [show q - 1 - 1 = q - 2 by ring]
  field_simp
  ring

theorem tsF_d2 (q : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => -q * x ^ (q - 2)) (-q * ((q - 2) * x ^ (q - 3))) x := by
  have h := (Real.hasDerivAt_rpow_const (p := q - 2) (Or.inl hx.ne')).const_mul (-q)
  refine h.congr_deriv ?_
  rw [show q - 2 - 1 = q - 3 by ring]

theorem cubic_d0 (a b c d x : ℝ) :
    HasDerivAt (cubicPoly a b c d) (3 * a * x ^ 2 + 2 * b * x + c) x := by
  have h := ((((hasDerivAt_pow 3 x).const_mul a).add ((hasDerivAt_pow 2 x).const_mul b)).add
    ((hasDerivAt_id x).const_mul c)).add_const d
  refine h.congr_deriv ?_
  simp; ring

theorem cubic_d1 (a b c d x : ℝ) :
    HasDerivAt (fun x => 3 * a * x ^ 2 + 2 * b * x + c) (6 * a * x + 2 * b) x := by
  have h := ((((hasDerivAt_pow 2 x).const_mul (3 * a)).add ((hasDerivAt_id x).const_mul (2 * b)))).add_const c
  refine h.congr_deriv ?_
  simp; ring

theorem cubic_d2 (a b x : ℝ) : HasDerivAt (fun x => 6 * a * x + 2 * b) (6 * a) x := by
  have h := (((hasDerivAt_id x).const_mul (6 * a))).add_const (2 * b)
  refine h.congr_deriv ?_
  simp

/-- The Hermite interpolation conditions for `f_q` at `1/6` and `1/2`. -/
theorem tsallis_interpolation {q : ℝ} (hq : q ≠ 1) :
    cubicPoly (tsA q) (tsB q) (tsC q) (tsD q) (1 / 6) = tsallisF q (1 / 6) ∧
    cubicPoly (tsA q) (tsB q) (tsC q) (tsD q) (1 / 2) = tsallisF q (1 / 2) ∧
    3 * tsA q * (1 / 6) ^ 2 + 2 * tsB q * (1 / 6) + tsC q
      = (q * (1 / 6 : ℝ) ^ (q - 1) - 1) / (1 - q) ∧
    3 * tsA q * (1 / 2) ^ 2 + 2 * tsB q * (1 / 2) + tsC q
      = (q * (1 / 2 : ℝ) ^ (q - 1) - 1) / (1 - q) := by
  have h1 : (1 - q) ≠ 0 := sub_ne_zero.2 (Ne.symm hq)
  have h2 : (q - 1) ≠ 0 := sub_ne_zero.2 hq
  have e6 : (1 / 6 : ℝ) ^ (q - 1) = (1 / 6 : ℝ) ^ q / (1 / 6) := Real.rpow_sub_one (by norm_num) q
  have e2 : (1 / 2 : ℝ) ^ (q - 1) = (1 / 2 : ℝ) ^ q / (1 / 2) := Real.rpow_sub_one (by norm_num) q
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cubicPoly tsA tsB tsC tsD tsallisF
    field_simp
    ring
  · unfold cubicPoly tsA tsB tsC tsD tsallisF
    field_simp
    ring
  · rw [e6]
    unfold tsA tsB tsC
    field_simp
    ring
  · rw [e2]
    unfold tsA tsB tsC
    field_simp
    ring

/-- The Hermite cubic of `f_q` at `1/6, 1/2` majorizes `f_q` on `[0,∞)`, strictly off the nodes,
and has positive cubic coefficient (`0 < q < 2`, `q ≠ 1`). -/
theorem tsallis_hermite {q : ℝ} (h0 : 0 < q) (h2 : q < 2) (h1 : q ≠ 1) :
    (∀ x, 0 ≤ x → x ≠ 1 / 6 → x ≠ 1 / 2 →
      tsallisF q x < cubicPoly (tsA q) (tsB q) (tsC q) (tsD q) x) ∧ 0 < tsA q := by
  obtain ⟨i0, i1, i2, i3⟩ := tsallis_interpolation h1
  set a := tsA q
  set b := tsB q
  set c := tsC q
  set d := tsD q
  have hne : (1 - q) ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have key := hermite_positivity (p := 1 / 6) (r := 1 / 2)
    (φ := fun x => cubicPoly a b c d x - tsallisF q x)
    (φ₁ := fun x => (3 * a * x ^ 2 + 2 * b * x + c) - (q * x ^ (q - 1) - 1) / (1 - q))
    (φ₂ := fun x => (6 * a * x + 2 * b) - (-q * x ^ (q - 2)))
    (φ₃ := fun x => 6 * a - (-q * ((q - 2) * x ^ (q - 3))))
    (by norm_num) (by norm_num)
    (by
      have hc1 : Continuous (cubicPoly a b c d) := by unfold cubicPoly; fun_prop
      have hc2 : Continuous (tsallisF q) := by
        unfold tsallisF
        exact ((Real.continuous_rpow_const h0.le).sub continuous_id).div_const _
      exact (hc1.sub hc2).continuousOn)
    (fun x hx => (cubic_d0 a b c d x).sub (tsF_d0 q hx))
    (fun x hx => (cubic_d1 a b c d x).sub (tsF_d1 h1 hx))
    (fun x hx => (cubic_d2 a b x).sub (tsF_d2 q hx))
    (by
      intro x hx y hy hxy
      have hlt : y ^ (q - 3) < x ^ (q - 3) := Real.rpow_lt_rpow_of_neg hx hxy (by linarith)
      have hq2 : q * (q - 2) < 0 := mul_neg_of_pos_of_neg h0 (by linarith)
      beta_reduce
      nlinarith)
    (sub_eq_zero.2 i0) (sub_eq_zero.2 i2) (sub_eq_zero.2 i1) (sub_eq_zero.2 i3)
  obtain ⟨hpos, u, hu, hu0⟩ := key
  refine ⟨fun x hx h6 h2' => ?_, ?_⟩
  · have := hpos x hx h6 h2'
    beta_reduce at this
    linarith
  · beta_reduce at hu0
    have hxu : 0 < u ^ (q - 3) := Real.rpow_pos_of_pos hu _
    have hq2 : q * (q - 2) < 0 := mul_neg_of_pos_of_neg h0 (by linarith)
    nlinarith

/-- info: 'FormalResearch.FourQubitEntropy.tsallis_hermite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tsallis_hermite

end FormalResearch.FourQubitEntropy
