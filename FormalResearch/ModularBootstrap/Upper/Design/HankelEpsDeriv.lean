module

public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelAsym

/-!
# Derivative bounds for the Hankel remainder `ε_H`

Source: `CFT/modular_bootstrap/paper/edge_transform_sd.tex`, Lemma `SD_V` (`esd:lemma`): the
nonvanishing amplitude `A_x(b) = ℰ(b) e^{Φ₁(b)} b^{1/2} (1 + ε_H(kb))` needs bounds on
`(log(1 + ε_H(k ·)))'` and `(log(1 + ε_H(k ·)))''`.  Since `1 + ε_H(z) = R(-iz)/√π` with `R = hankelR`
holomorphic on `Re w > 0` and `‖R(w) - √π‖ ≤ √π/(4‖w‖)`, Cauchy's estimates on a disc of radius
`Re w / 2` give, for `Re w > 0`,

* `norm_deriv_hankelR_le`: `‖R'(w)‖ ≤ √π / (Re w)²`;
* `norm_deriv2_hankelR_le`: `‖R''(w)‖ ≤ 8 √π / (Re w)³`;
* `hankelLogD`: the logarithmic derivative of `z ↦ R(-i k z)`, its derivative
  `hasDerivAt_hankelLogD` and the bounds `norm_hankelLogD_le`, `norm_deriv_hankelLogD_le`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex Metric Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Design

open FormalResearch.ModularBootstrap.Upper.Hankel

private lemma re_pos_of_mem_closedBall {w z : ℂ} (hz : z ∈ closedBall w (w.re / 2)) :
    w.re / 2 ≤ z.re := by
  have h1 : ‖z - w‖ ≤ w.re / 2 := by simpa [Complex.dist_eq] using hz
  have h2 := Complex.abs_re_le_norm (z - w)
  have h3 : (z - w).re = z.re - w.re := by simp
  rw [h3] at h2
  have := (abs_le.mp h2).1
  linarith

lemma differentiableOn_deriv_hankelR : DifferentiableOn ℂ (deriv hankelR) {w : ℂ | 0 < w.re} := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  exact (differentiableOn_hankelR.analyticOnNhd hopen).deriv.differentiableOn

lemma _root_.DifferentiableOn.diffContOnCl_of_closedBall {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (h : DifferentiableOn ℂ f (closedBall c r)) : DiffContOnCl ℂ f (ball c r) := by
  refine ⟨h.mono ball_subset_closedBall, ?_⟩
  exact h.continuousOn.mono (closure_ball_subset_closedBall)

/-- Cauchy estimate: `‖R'(w)‖ ≤ √π / (Re w)²` for `Re w > 0`. -/
theorem norm_deriv_hankelR_le {w : ℂ} (hw : 0 < w.re) : ‖deriv hankelR w‖ ≤ √π / w.re ^ 2 := by
  have hr : 0 < w.re / 2 := by positivity
  have hsp : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hdiff : DifferentiableOn ℂ (fun z => hankelR z - (√π : ℝ)) (closedBall w (w.re / 2)) :=
    (differentiableOn_hankelR.mono fun z hz => by
      have := re_pos_of_mem_closedBall hz
      change 0 < z.re
      linarith).sub_const _
  have hcl : DiffContOnCl ℂ (fun z => hankelR z - (√π : ℝ)) (ball w (w.re / 2)) :=
    hdiff.diffContOnCl_of_closedBall
  have hC : ∀ z ∈ sphere w (w.re / 2), ‖hankelR z - (√π : ℝ)‖ ≤ √π / (2 * w.re) := by
    intro z hz
    have hz' := re_pos_of_mem_closedBall (sphere_subset_closedBall hz)
    have hz0 : z ≠ 0 := by
      intro h; rw [h] at hz'; simp at hz'; linarith
    have hzn : w.re / 2 ≤ ‖z‖ := hz'.trans (Complex.re_le_norm z)
    refine (norm_hankelR_sub_le (by linarith) hz0).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hcl hC
  have e : deriv (fun z => hankelR z - (√π : ℝ)) w = deriv hankelR w := deriv_sub_const _
  rw [e] at this
  refine this.trans_eq ?_
  field_simp

/-- Cauchy estimate: `‖R''(w)‖ ≤ 8 √π / (Re w)³` for `Re w > 0`. -/
theorem norm_deriv2_hankelR_le {w : ℂ} (hw : 0 < w.re) :
    ‖deriv (deriv hankelR) w‖ ≤ 8 * √π / w.re ^ 3 := by
  have hr : 0 < w.re / 2 := by positivity
  have hsp : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hdiff : DifferentiableOn ℂ (deriv hankelR) (closedBall w (w.re / 2)) :=
    differentiableOn_deriv_hankelR.mono fun z hz => by
      have := re_pos_of_mem_closedBall hz
      change 0 < z.re
      linarith
  have hcl : DiffContOnCl ℂ (deriv hankelR) (ball w (w.re / 2)) :=
    hdiff.diffContOnCl_of_closedBall
  have hC : ∀ z ∈ sphere w (w.re / 2), ‖deriv hankelR z‖ ≤ 4 * √π / w.re ^ 2 := by
    intro z hz
    have hz' := re_pos_of_mem_closedBall (sphere_subset_closedBall hz)
    have hzpos : 0 < z.re := by linarith
    refine (norm_deriv_hankelR_le hzpos).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (w.re / 2) ^ 2 ≤ z.re ^ 2 := pow_le_pow_left₀ (by positivity) hz' 2
    nlinarith [mul_pos hsp hsp]
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hcl hC
  refine this.trans_eq ?_
  field_simp
  ring

/-- Lower bound `‖R(w)‖ ≥ (3/4)√π` for `Re w ≥ 0`, `‖w‖ ≥ 1`. -/
theorem norm_hankelR_ge {w : ℂ} (hw : 0 ≤ w.re) (hw1 : 1 ≤ ‖w‖) : 3 * √π / 4 ≤ ‖hankelR w‖ := by
  have hsp : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw1; linarith
  have h := norm_hankelR_sub_le hw hw0
  have h1 : √π / (4 * ‖w‖) ≤ √π / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : √π ≤ ‖hankelR w‖ + ‖hankelR w - (√π : ℝ)‖ := by
    have e : ‖((√π : ℝ) : ℂ)‖ = √π := by rw [Complex.norm_real, Real.norm_of_nonneg hsp.le]
    calc √π = ‖((√π : ℝ) : ℂ)‖ := e.symm
      _ = ‖((√π : ℝ) : ℂ) - hankelR w + hankelR w‖ := by ring_nf
      _ ≤ ‖((√π : ℝ) : ℂ) - hankelR w‖ + ‖hankelR w‖ := norm_add_le _ _
      _ = ‖hankelR w‖ + ‖hankelR w - (√π : ℝ)‖ := by rw [norm_sub_rev]; ring
  linarith

/-- The logarithmic derivative of `z ↦ R(-i k z)` (with the chain-rule factor `-i k`). -/
noncomputable def hankelLogD (k : ℝ) (z : ℂ) : ℂ :=
  (-Complex.I * (k : ℂ)) * deriv hankelR (-Complex.I * ((k : ℂ) * z)) /
    hankelR (-Complex.I * ((k : ℂ) * z))

lemma re_neg_I_mul_mul {k : ℝ} {z : ℂ} : (-Complex.I * ((k : ℂ) * z)).re = k * z.im := by
  simp [Complex.mul_re, Complex.mul_im]

lemma hasDerivAt_hankelR_comp {k : ℝ} {z : ℂ} (hz : 0 < k * z.im) :
    HasDerivAt (fun z => hankelR (-Complex.I * ((k : ℂ) * z)))
      ((-Complex.I * (k : ℂ)) * deriv hankelR (-Complex.I * ((k : ℂ) * z))) z := by
  have hw : 0 < (-Complex.I * ((k : ℂ) * z)).re := by rw [re_neg_I_mul_mul]; exact hz
  have hR : HasDerivAt hankelR (deriv hankelR (-Complex.I * ((k : ℂ) * z)))
      (-Complex.I * ((k : ℂ) * z)) :=
    (differentiableOn_hankelR (-Complex.I * ((k : ℂ) * z)) hw).differentiableAt
      (isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hw) |>.hasDerivAt
  have hlin : HasDerivAt (fun z : ℂ => -Complex.I * ((k : ℂ) * z)) (-Complex.I * (k : ℂ)) z :=
    (((hasDerivAt_id z).const_mul (k : ℂ)).const_mul (-Complex.I)).congr_deriv (by ring)
  have h := hR.comp z hlin
  exact h.congr_deriv (mul_comm _ _)

lemma hasDerivAt_deriv_hankelR_comp {k : ℝ} {z : ℂ} (hz : 0 < k * z.im) :
    HasDerivAt (fun z => deriv hankelR (-Complex.I * ((k : ℂ) * z)))
      ((-Complex.I * (k : ℂ)) * deriv (deriv hankelR) (-Complex.I * ((k : ℂ) * z))) z := by
  have hw : 0 < (-Complex.I * ((k : ℂ) * z)).re := by rw [re_neg_I_mul_mul]; exact hz
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hR : HasDerivAt (deriv hankelR) (deriv (deriv hankelR) (-Complex.I * ((k : ℂ) * z)))
      (-Complex.I * ((k : ℂ) * z)) :=
    (differentiableOn_deriv_hankelR (-Complex.I * ((k : ℂ) * z)) hw).differentiableAt
      (hopen.mem_nhds hw) |>.hasDerivAt
  have hlin : HasDerivAt (fun z : ℂ => -Complex.I * ((k : ℂ) * z)) (-Complex.I * (k : ℂ)) z :=
    (((hasDerivAt_id z).const_mul (k : ℂ)).const_mul (-Complex.I)).congr_deriv (by ring)
  have h := hR.comp z hlin
  exact h.congr_deriv (mul_comm _ _)

lemma deriv_hankelR_comp_div {k : ℝ} {z : ℂ} (hz : 0 < k * z.im) :
    deriv (fun z => hankelR (-Complex.I * ((k : ℂ) * z))) z /
        hankelR (-Complex.I * ((k : ℂ) * z)) = hankelLogD k z := by
  rw [(hasDerivAt_hankelR_comp hz).deriv]
  rfl

/-- Derivative of the logarithmic derivative `hankelLogD`, when `R(-ikz) ≠ 0`. -/
theorem hasDerivAt_hankelLogD {k : ℝ} {z : ℂ} (hz : 0 < k * z.im)
    (hne : hankelR (-Complex.I * ((k : ℂ) * z)) ≠ 0) :
    HasDerivAt (hankelLogD k)
      ((-Complex.I * (k : ℂ)) ^ 2 *
        (deriv (deriv hankelR) (-Complex.I * ((k : ℂ) * z)) /
            hankelR (-Complex.I * ((k : ℂ) * z)) -
          (deriv hankelR (-Complex.I * ((k : ℂ) * z)) /
            hankelR (-Complex.I * ((k : ℂ) * z))) ^ 2)) z := by
  have h1 := (hasDerivAt_deriv_hankelR_comp hz).const_mul (-Complex.I * (k : ℂ))
  have h2 := hasDerivAt_hankelR_comp hz
  have hd := h1.div h2 hne
  refine hd.congr_deriv ?_
  field_simp

/-- `‖(log R(-ik·))'‖ ≤ 4 k / (3 ρ²)` where `ρ = k Im z`, for `‖k z‖ ≥ 1`. -/
theorem norm_hankelLogD_le {k : ℝ} (hk : 0 < k) {z : ℂ} (hz : 0 < k * z.im)
    (hz1 : 1 ≤ ‖(k : ℂ) * z‖) : ‖hankelLogD k z‖ ≤ 4 * k / (3 * (k * z.im) ^ 2) := by
  have hsp : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hw : 0 < (-Complex.I * ((k : ℂ) * z)).re := by rw [re_neg_I_mul_mul]; exact hz
  have hwn : 1 ≤ ‖-Complex.I * ((k : ℂ) * z)‖ := by simpa using hz1
  have hR := norm_hankelR_ge hw.le hwn
  have hR' := norm_deriv_hankelR_le hw
  rw [re_neg_I_mul_mul] at hR'
  unfold hankelLogD
  have hpos : 0 < 3 * √π / 4 := by positivity
  rw [norm_div, norm_mul]
  have hk' : ‖-Complex.I * (k : ℂ)‖ = k := by simp [abs_of_pos hk]
  rw [hk']
  calc k * ‖deriv hankelR (-Complex.I * ((k : ℂ) * z))‖ /
        ‖hankelR (-Complex.I * ((k : ℂ) * z))‖
      ≤ k * (√π / (k * z.im) ^ 2) / (3 * √π / 4) := by
        apply div_le_div₀ (by positivity) (by gcongr) hpos hR
    _ = 4 * k / (3 * (k * z.im) ^ 2) := by field_simp

/-- `‖(hankelLogD k)'‖ ≤ k² (32 / (3 ρ³) + 16 / (9 ρ⁴))`, `ρ = k Im z`, for `‖k z‖ ≥ 1`. -/
theorem norm_deriv_hankelLogD_le {k : ℝ} (hk : 0 < k) {z : ℂ} (hz : 0 < k * z.im)
    (hz1 : 1 ≤ ‖(k : ℂ) * z‖) :
    ‖(-Complex.I * (k : ℂ)) ^ 2 *
        (deriv (deriv hankelR) (-Complex.I * ((k : ℂ) * z)) /
            hankelR (-Complex.I * ((k : ℂ) * z)) -
          (deriv hankelR (-Complex.I * ((k : ℂ) * z)) /
            hankelR (-Complex.I * ((k : ℂ) * z))) ^ 2)‖ ≤
      k ^ 2 * (32 / (3 * (k * z.im) ^ 3) + 16 / (9 * (k * z.im) ^ 4)) := by
  have hsp : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hw : 0 < (-Complex.I * ((k : ℂ) * z)).re := by rw [re_neg_I_mul_mul]; exact hz
  have hwn : 1 ≤ ‖-Complex.I * ((k : ℂ) * z)‖ := by simpa using hz1
  have hR := norm_hankelR_ge hw.le hwn
  have hR' := norm_deriv_hankelR_le hw
  have hR'' := norm_deriv2_hankelR_le hw
  rw [re_neg_I_mul_mul] at hR' hR''
  have hpos : 0 < 3 * √π / 4 := by positivity
  have hRpos : 0 < ‖hankelR (-Complex.I * ((k : ℂ) * z))‖ := lt_of_lt_of_le hpos hR
  have hk2 : ‖(-Complex.I * (k : ℂ)) ^ 2‖ = k ^ 2 := by simp [abs_of_pos hk]
  rw [norm_mul, hk2]
  have hq1 : ‖deriv hankelR (-Complex.I * ((k : ℂ) * z)) /
      hankelR (-Complex.I * ((k : ℂ) * z))‖ ≤ 4 / (3 * (k * z.im) ^ 2) := by
    rw [norm_div]
    calc _ ≤ (√π / (k * z.im) ^ 2) / (3 * √π / 4) := div_le_div₀ (by positivity) hR' hpos hR
      _ = 4 / (3 * (k * z.im) ^ 2) := by field_simp
  have hq2 : ‖deriv (deriv hankelR) (-Complex.I * ((k : ℂ) * z)) /
      hankelR (-Complex.I * ((k : ℂ) * z))‖ ≤ 32 / (3 * (k * z.im) ^ 3) := by
    rw [norm_div]
    calc _ ≤ (8 * √π / (k * z.im) ^ 3) / (3 * √π / 4) := div_le_div₀ (by positivity) hR'' hpos hR
      _ = 32 / (3 * (k * z.im) ^ 3) := by field_simp; norm_num
  gcongr
  calc _ ≤ ‖deriv (deriv hankelR) (-Complex.I * ((k : ℂ) * z)) /
        hankelR (-Complex.I * ((k : ℂ) * z))‖ + ‖(deriv hankelR (-Complex.I * ((k : ℂ) * z)) /
        hankelR (-Complex.I * ((k : ℂ) * z))) ^ 2‖ := norm_sub_le _ _
    _ ≤ 32 / (3 * (k * z.im) ^ 3) + (4 / (3 * (k * z.im) ^ 2)) ^ 2 := by
        rw [norm_pow]; gcongr
    _ = 32 / (3 * (k * z.im) ^ 3) + 16 / (9 * (k * z.im) ^ 4) := by
        congr 1; field_simp; ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.norm_deriv_hankelR_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_deriv_hankelR_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.norm_deriv2_hankelR_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_deriv2_hankelR_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.norm_hankelR_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_hankelR_ge

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.hasDerivAt_hankelLogD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_hankelLogD

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.norm_hankelLogD_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_hankelLogD_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.norm_deriv_hankelLogD_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_deriv_hankelLogD_le

end FormalResearch.ModularBootstrap.Upper.Design
