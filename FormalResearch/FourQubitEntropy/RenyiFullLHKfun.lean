import FormalResearch.FourQubitEntropy.RenyiFullLHCurv
import FormalResearch.FourQubitEntropy.RenyiFullSHD

/-!
# The tail power sum `K(z) = ((1+2z)^q + 2(1-z)^q)/3^q` of the chart `(a, b, c, c)`

Paper E, `lem:fqe-large-head-curvature`, `lem:fqe-large-head-dual`: `K = Σ (λ_i/(1-a))^q` for the tail.
The derivatives up to order four are explicit; `K'''' > 0` on `(-1/2, 1)` gives the cubic Hermite
minorants (`hermite4_nonneg`); convexity gives the chord upper bound.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

noncomputable def kfun (q z : ℝ) : ℝ := ((1 + 2 * z) ^ q + 2 * (1 - z) ^ q) / 3 ^ q

noncomputable def kf1 (q z : ℝ) : ℝ :=
  q / 3 ^ q * (2 * (1 + 2 * z) ^ (q - 1) - 2 * (1 - z) ^ (q - 1))
noncomputable def kf2 (q z : ℝ) : ℝ :=
  q * (q - 1) / 3 ^ q * (4 * (1 + 2 * z) ^ (q - 2) + 2 * (1 - z) ^ (q - 2))
noncomputable def kf3 (q z : ℝ) : ℝ :=
  q * (q - 1) * (q - 2) / 3 ^ q * (8 * (1 + 2 * z) ^ (q - 3) - 2 * (1 - z) ^ (q - 3))
noncomputable def kf4 (q z : ℝ) : ℝ :=
  q * (q - 1) * (q - 2) * (q - 3) / 3 ^ q * (16 * (1 + 2 * z) ^ (q - 4) + 2 * (1 - z) ^ (q - 4))

theorem hasDerivAt_lin1 (p : ℝ) {z : ℝ} (hz : 0 < 1 + 2 * z) :
    HasDerivAt (fun z : ℝ => (1 + 2 * z) ^ p) (2 * p * (1 + 2 * z) ^ (p - 1)) z := by
  have := (((hasDerivAt_id z).const_mul 2).const_add 1).rpow_const (p := p) (Or.inl hz.ne')
  refine this.congr_deriv ?_
  simp only [id]
  ring

theorem hasDerivAt_lin2 (p : ℝ) {z : ℝ} (hz : 0 < 1 - z) :
    HasDerivAt (fun z : ℝ => (1 - z) ^ p) (-(p * (1 - z) ^ (p - 1))) z := by
  have := ((hasDerivAt_id z).const_sub 1).rpow_const (p := p) (Or.inl hz.ne')
  refine this.congr_deriv ?_
  simp only [id]
  ring

section KChain
variable {q z : ℝ}

theorem hasDerivAt_kfun (h1 : 0 < 1 + 2 * z) (h2 : 0 < 1 - z) : HasDerivAt (kfun q) (kf1 q z) z := by
  have := ((hasDerivAt_lin1 q h1).add ((hasDerivAt_lin2 q h2).const_mul 2)).div_const (3 ^ q)
  refine this.congr_deriv ?_
  unfold kf1
  ring

theorem hasDerivAt_kf1 (h1 : 0 < 1 + 2 * z) (h2 : 0 < 1 - z) : HasDerivAt (kf1 q) (kf2 q z) z := by
  have := (((hasDerivAt_lin1 (q - 1) h1).const_mul 2).sub
    ((hasDerivAt_lin2 (q - 1) h2).const_mul 2)).const_mul (q / 3 ^ q)
  refine this.congr_deriv ?_
  unfold kf2
  ring

theorem hasDerivAt_kf2 (h1 : 0 < 1 + 2 * z) (h2 : 0 < 1 - z) : HasDerivAt (kf2 q) (kf3 q z) z := by
  have := (((hasDerivAt_lin1 (q - 2) h1).const_mul 4).add
    ((hasDerivAt_lin2 (q - 2) h2).const_mul 2)).const_mul (q * (q - 1) / 3 ^ q)
  refine this.congr_deriv ?_
  unfold kf3
  ring_nf

theorem hasDerivAt_kf3 (h1 : 0 < 1 + 2 * z) (h2 : 0 < 1 - z) : HasDerivAt (kf3 q) (kf4 q z) z := by
  have := (((hasDerivAt_lin1 (q - 3) h1).const_mul 8).sub
    ((hasDerivAt_lin2 (q - 3) h2).const_mul 2)).const_mul (q * (q - 1) * (q - 2) / 3 ^ q)
  refine this.congr_deriv ?_
  unfold kf4
  ring_nf

end KChain


section Values
variable {q : ℝ}

theorem kfun_zero : kfun q 0 = 3 / 3 ^ q := by
  unfold kfun
  simp
  ring

theorem kfun_one (hq : 0 < q) : kfun q 1 = 1 := by
  unfold kfun
  have : (3 : ℝ) ^ q ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) q).ne'
  simp [Real.zero_rpow hq.ne']
  norm_num
  exact this

theorem kf1_zero : kf1 q 0 = 0 := by
  unfold kf1
  simp

theorem kf1_one (hq : 1 < q) : kf1 q 1 = 2 * q / 3 := by
  unfold kf1
  have h3 : (3 : ℝ) ^ q = 3 * 3 ^ (q - 1) := by
    rw [← Real.rpow_one_add' (by norm_num) (by linarith)]
    ring_nf
  have hp : (3 : ℝ) ^ (q - 1) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have : (3 : ℝ) ^ q ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) q).ne'
  simp [Real.zero_rpow (show q - 1 ≠ 0 by linarith)]
  norm_num
  rw [h3]
  field_simp

theorem kf4_pos (hq1 : 1 < q) (hq2 : q < 2) {z : ℝ} (h1 : 0 < 1 + 2 * z) (h2 : 0 < 1 - z) : 0 < kf4 q z := by
  unfold kf4
  have a1 : 0 < q * (q - 1) * (q - 2) * (q - 3) := by
    have : 0 < (q - 2) * (q - 3) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have : 0 < q * (q - 1) := mul_pos (by linarith) (by linarith)
    nlinarith [mul_pos ‹0 < q * (q - 1)› ‹0 < (q - 2) * (q - 3)›]
  have a3 : 0 < (3 : ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) q
  have b1 := Real.rpow_pos_of_pos h1 (q - 4)
  have b2 := Real.rpow_pos_of_pos h2 (q - 4)
  positivity

end Values


/-! ### The cubic Hermite minorant on `[0,1]` (nodes `0` and `1`) -/

noncomputable def Hh (K0 q z : ℝ) : ℝ :=
  K0 + (3 - 3 * K0 - 2 * q / 3) * z ^ 2 + (2 * q / 3 - 2 + 2 * K0) * z ^ 3
noncomputable def Hh1 (K0 q z : ℝ) : ℝ :=
  2 * (3 - 3 * K0 - 2 * q / 3) * z + 3 * (2 * q / 3 - 2 + 2 * K0) * z ^ 2
noncomputable def Hh2 (K0 q z : ℝ) : ℝ :=
  2 * (3 - 3 * K0 - 2 * q / 3) + 6 * (2 * q / 3 - 2 + 2 * K0) * z
noncomputable def Hh3 (K0 q : ℝ) : ℝ := 6 * (2 * q / 3 - 2 + 2 * K0)

section HChainK
variable {K0 q : ℝ}

theorem hasDerivAt_Hh (z : ℝ) : HasDerivAt (Hh K0 q) (Hh1 K0 q z) z := by
  have h : HasDerivAt (Hh K0 q) (deriv (Hh K0 q) z) z :=
    (by unfold Hh; fun_prop : DifferentiableAt ℝ (Hh K0 q) z).hasDerivAt
  refine h.congr_deriv ?_
  unfold Hh Hh1
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_Hh1 (z : ℝ) : HasDerivAt (Hh1 K0 q) (Hh2 K0 q z) z := by
  have h : HasDerivAt (Hh1 K0 q) (deriv (Hh1 K0 q) z) z :=
    (by unfold Hh1; fun_prop : DifferentiableAt ℝ (Hh1 K0 q) z).hasDerivAt
  refine h.congr_deriv ?_
  unfold Hh1 Hh2
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_Hh2 (z : ℝ) : HasDerivAt (Hh2 K0 q) (Hh3 K0 q) z := by
  have h : HasDerivAt (Hh2 K0 q) (deriv (Hh2 K0 q) z) z :=
    (by unfold Hh2; fun_prop : DifferentiableAt ℝ (Hh2 K0 q) z).hasDerivAt
  refine h.congr_deriv ?_
  unfold Hh2 Hh3
  simp (disch := fun_prop)

end HChainK

theorem kfun_continuousOn {q : ℝ} (hq : 0 ≤ q) : ContinuousOn (kfun q) (Icc 0 1) := by
  unfold kfun
  apply ContinuousOn.div_const
  apply ContinuousOn.add
  · apply ContinuousOn.rpow_const (by fun_prop)
    intro z hz; left; linarith [hz.1]
  · apply ContinuousOn.const_mul
    apply ContinuousOn.rpow_const (by fun_prop)
    intro z hz; right; exact hq

theorem kf1_continuousOn {q : ℝ} (hq : 1 ≤ q) : ContinuousOn (kf1 q) (Icc 0 1) := by
  unfold kf1
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.sub
  · apply ContinuousOn.const_mul
    apply ContinuousOn.rpow_const (by fun_prop)
    intro z hz; left; linarith [hz.1]
  · apply ContinuousOn.const_mul
    apply ContinuousOn.rpow_const (by fun_prop)
    intro z hz; right; linarith

/-- **`K ≥` its cubic Hermite interpolant at `0` and `1`** (`K'''' > 0`). -/
theorem kfun_ge_Hh {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) :
    ∀ z ∈ Icc (0 : ℝ) 1, Hh (kfun q 0) q z ≤ kfun q z := by
  set K0 := kfun q 0 with hK0
  have hI : ∀ z ∈ Ioo (0 : ℝ) 1, 0 < 1 + 2 * z ∧ 0 < 1 - z := fun z hz =>
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have key := hermite4_nonneg (A := 0) (B := 1) (l := 0) (u := 1) le_rfl zero_lt_one le_rfl
    (R := fun z => kfun q z - Hh K0 q z) (R1 := fun z => kf1 q z - Hh1 K0 q z)
    (R2 := fun z => kf2 q z - Hh2 K0 q z) (R3 := fun z => kf3 q z - Hh3 K0 q) (R4 := fun z => kf4 q z)
    ((kfun_continuousOn (by linarith)).sub (by
      intro z _; exact (hasDerivAt_Hh z).continuousAt.continuousWithinAt))
    ((kf1_continuousOn hq1.le).sub (by
      intro z _; exact (hasDerivAt_Hh1 z).continuousAt.continuousWithinAt))
    (fun z hz => (hasDerivAt_kfun (hI z hz).1 (hI z hz).2).sub (hasDerivAt_Hh z))
    (fun z hz => (hasDerivAt_kf1 (hI z hz).1 (hI z hz).2).sub (hasDerivAt_Hh1 z))
    (fun z hz => (hasDerivAt_kf2 (hI z hz).1 (hI z hz).2).sub (hasDerivAt_Hh2 z))
    (fun z hz => ((hasDerivAt_kf3 (hI z hz).1 (hI z hz).2).sub (hasDerivAt_const z (Hh3 K0 q))).congr_deriv
      (by simp))
    (fun z hz => (kf4_pos hq1 hq2 (hI z hz).1 (hI z hz).2).le)
    (by simp [Hh, hK0]) (by simp [hK0, kfun_one (by linarith : 0 < q), Hh]; ring)
    (by simp [kf1_zero, Hh1]) (by
      simp only [kf1_one hq1, Hh1]
      ring)
  intro z hz
  have := key z hz
  linarith

end FormalResearch.FourQubitEntropy.RenyiFull
