import FormalResearch.FourQubitEntropy.RenyiFullLHKappaData

/-!
# `K ≥ κ` on `[0,1]` (`(LH1)` of `lem:fqe-large-head-dual`)

The cubic Hermite interpolant of `K` at the double nodes `3/20` and `17/20` is a lower bound because
`K'''' > 0` (`hermite4_nonneg`); `κ` is its coefficientwise rational lower rounding
(`kap_le_hc`, generated).
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

noncomputable def cubp (c0 c1 c2 c3 z : ℝ) : ℝ := c0 + c1 * z + c2 * z ^ 2 + c3 * z ^ 3
noncomputable def cubp1 (c1 c2 c3 z : ℝ) : ℝ := c1 + 2 * c2 * z + 3 * c3 * z ^ 2
noncomputable def cubp2 (c2 c3 z : ℝ) : ℝ := 2 * c2 + 6 * c3 * z
noncomputable def cubp3 (c3 : ℝ) : ℝ := 6 * c3

section
variable {c0 c1 c2 c3 : ℝ}

theorem hasDerivAt_cubp (z : ℝ) : HasDerivAt (cubp c0 c1 c2 c3) (cubp1 c1 c2 c3 z) z := by
  have h : HasDerivAt (cubp c0 c1 c2 c3) (deriv (cubp c0 c1 c2 c3) z) z :=
    (by unfold cubp; fun_prop : DifferentiableAt ℝ (cubp c0 c1 c2 c3) z).hasDerivAt
  refine h.congr_deriv ?_
  unfold cubp cubp1
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_cubp1 (z : ℝ) : HasDerivAt (cubp1 c1 c2 c3) (cubp2 c2 c3 z) z := by
  have h : HasDerivAt (cubp1 c1 c2 c3) (deriv (cubp1 c1 c2 c3) z) z :=
    (by unfold cubp1; fun_prop : DifferentiableAt ℝ (cubp1 c1 c2 c3) z).hasDerivAt
  refine h.congr_deriv ?_
  unfold cubp1 cubp2
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_cubp2 (z : ℝ) : HasDerivAt (cubp2 c2 c3) (cubp3 c3) z := by
  have h : HasDerivAt (cubp2 c2 c3) (deriv (cubp2 c2 c3) z) z :=
    (by unfold cubp2; fun_prop : DifferentiableAt ℝ (cubp2 c2 c3) z).hasDerivAt
  refine h.congr_deriv ?_
  unfold cubp2 cubp3
  simp (disch := fun_prop)

end

/-- **`K ≥` the cubic Hermite interpolant at `3/20, 17/20`.** -/
theorem kfun_ge_hermite :
    ∀ z ∈ Icc (0 : ℝ) 1,
      cubp (hc0 (kfun qS (3 / 20)) (kf1 qS (3 / 20)) (kfun qS (17 / 20)) (kf1 qS (17 / 20)))
        (hc1 (kfun qS (3 / 20)) (kf1 qS (3 / 20)) (kfun qS (17 / 20)) (kf1 qS (17 / 20)))
        (hc2 (kfun qS (3 / 20)) (kf1 qS (3 / 20)) (kfun qS (17 / 20)) (kf1 qS (17 / 20)))
        (hc3 (kfun qS (3 / 20)) (kf1 qS (3 / 20)) (kfun qS (17 / 20)) (kf1 qS (17 / 20))) z ≤ kfun qS z := by
  set Kl := kfun qS (3 / 20) with hKl
  set K1l := kf1 qS (3 / 20) with hK1l
  set Ku := kfun qS (17 / 20) with hKu
  set K1u := kf1 qS (17 / 20) with hK1u
  set c0 := hc0 Kl K1l Ku K1u with hc0d
  set c1 := hc1 Kl K1l Ku K1u with hc1d
  set c2 := hc2 Kl K1l Ku K1u with hc2d
  set c3 := hc3 Kl K1l Ku K1u with hc3d
  have hq1 : 1 < qS := by unfold qS; norm_num
  have hq2 : qS < 2 := by unfold qS; norm_num
  have hI : ∀ z ∈ Ioo (0 : ℝ) 1, 0 < 1 + 2 * z ∧ 0 < 1 - z := fun z hz =>
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have key := hermite4_nonneg (A := 0) (B := 1) (l := 3 / 20) (u := 17 / 20) (by norm_num) (by norm_num)
    (by norm_num)
    (R := fun z => kfun qS z - cubp c0 c1 c2 c3 z) (R1 := fun z => kf1 qS z - cubp1 c1 c2 c3 z)
    (R2 := fun z => kf2 qS z - cubp2 c2 c3 z) (R3 := fun z => kf3 qS z - cubp3 c3)
    (R4 := fun z => kf4 qS z)
    ((kfun_continuousOn (by linarith)).sub (by
      intro z _; exact (hasDerivAt_cubp z).continuousAt.continuousWithinAt))
    ((kf1_continuousOn hq1.le).sub (by
      intro z _; exact (hasDerivAt_cubp1 z).continuousAt.continuousWithinAt))
    (fun z hz => (hasDerivAt_kfun (hI z hz).1 (hI z hz).2).sub (hasDerivAt_cubp z))
    (fun z hz => (hasDerivAt_kf1 (hI z hz).1 (hI z hz).2).sub (hasDerivAt_cubp1 z))
    (fun z hz => (hasDerivAt_kf2 (hI z hz).1 (hI z hz).2).sub (hasDerivAt_cubp2 z))
    (fun z hz => ((hasDerivAt_kf3 (hI z hz).1 (hI z hz).2).sub (hasDerivAt_const z (cubp3 c3))).congr_deriv
      (by simp))
    (fun z hz => (kf4_pos hq1 hq2 (hI z hz).1 (hI z hz).2).le)
    (by
      show kfun qS (3 / 20) - cubp c0 c1 c2 c3 (3 / 20) = 0
      have := hc_at_l Kl K1l Ku K1u
      unfold cubp
      rw [← hKl] at *
      linarith)
    (by
      show kfun qS (17 / 20) - cubp c0 c1 c2 c3 (17 / 20) = 0
      have := hc_at_u Kl K1l Ku K1u
      unfold cubp
      rw [← hKu] at *
      linarith)
    (by
      show kf1 qS (3 / 20) - cubp1 c1 c2 c3 (3 / 20) = 0
      have := hc_d_at_l Kl K1l Ku K1u
      unfold cubp1
      rw [← hK1l] at *
      linarith)
    (by
      show kf1 qS (17 / 20) - cubp1 c1 c2 c3 (17 / 20) = 0
      have := hc_d_at_u Kl K1l Ku K1u
      unfold cubp1
      rw [← hK1u] at *
      linarith)
  intro z hz
  have := key z hz
  linarith

/-- **`(LH1)`: `K ≥ κ` on `[0,1]`.** -/
theorem kap_le_kfun {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : kap z ≤ kfun qS z := by
  have h := kfun_ge_hermite z ⟨hz0, hz1⟩
  have h2 := kap_le_hc hz0
  unfold cubp at h
  linarith

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.kap_le_kfun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kap_le_kfun

end FormalResearch.FourQubitEntropy.RenyiFull
