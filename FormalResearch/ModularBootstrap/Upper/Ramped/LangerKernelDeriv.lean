module

public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerKernelAux

/-!
# `(F2)`: derivative formulas for `y ↦ K(x, y)`

* `deriv_langerK_gt`, `deriv2_langerK_gt` (`y > x`) and `deriv_langerK_lt`, `deriv2_langerK_lt` (`0 < y < x`):
  `K = 𝔥(|x-y|) + 𝔥(x+y) - log|τ(x) - τ(y)|` differentiated explicitly (`𝔥 = combH`);
* `deriv_langerK_eq`, `deriv2_langerK_eq` (all `y > 0`):
  `K = L(x - y) - log D(x, y) + 𝔥(x + y)` with `L = log T` smooth, differentiated in terms of the
  derivatives of the difference quotient `D(x, ·)`;
* `deriv_langerD_eq_hadInt`, `deriv2_langerD_eq_hadInt`: near the diagonal `D(x,·)'` and `D(x,·)''` are the
  Hadamard integrals `∫ t τ''(x + t(y - x)) dt` and `∫ t² τ'''(x + t(y - x)) dt`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb

section Up

variable {x y : ℝ}

lemma deriv_langerK_gt (hx : 0 < x) (hxy : x < y) :
    deriv (langerK x) y = combHDeriv (y - x) + combHDeriv (x + y) -
      deriv langerTau y / (langerTau y - langerTau x) := by
  have hy : 0 < y := lt_trans hx hxy
  have hS : 0 < langerTau y - langerTau x := by
    have := langerTau_strictMonoOn (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) hxy; linarith
  have h1 : HasDerivAt (fun z => combH (z - x)) (combHDeriv (y - x)) y :=
    (hasDerivAt_combH (sub_pos.2 hxy)).comp_sub_const y x
  have h2 : HasDerivAt (fun z => combH (x + z)) (combHDeriv (x + y)) y :=
    (hasDerivAt_combH (by linarith : 0 < x + y)).comp_const_add x y
  have h3 : HasDerivAt (fun z => Real.log (langerTau z - langerTau x))
      (deriv langerTau y / (langerTau y - langerTau x)) y :=
    ((hasDerivAt_langerTau_pos hy).sub_const _).log hS.ne'
  have h := (h1.add h2).sub h3
  have heq : langerK x =ᶠ[𝓝 y] fun z => combH (z - x) + combH (x + z) -
      Real.log (langerTau z - langerTau x) := by
    filter_upwards [Ioi_mem_nhds hxy] with z hz
    exact langerK_gt hx hz
  exact (h.congr_of_eventuallyEq heq).deriv

lemma deriv2_langerK_gt (hx : 0 < x) (hxy : x < y) :
    deriv (deriv (langerK x)) y = combHSecond (y - x) + combHSecond (x + y) -
      (deriv (deriv langerTau) y * (langerTau y - langerTau x) - deriv langerTau y ^ 2) /
        (langerTau y - langerTau x) ^ 2 := by
  have hy : 0 < y := lt_trans hx hxy
  have hS : 0 < langerTau y - langerTau x := by
    have := langerTau_strictMonoOn (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) hxy; linarith
  have h1 : HasDerivAt (fun z => combHDeriv (z - x)) (combHSecond (y - x)) y :=
    (hasDerivAt_combHDeriv (sub_pos.2 hxy)).comp_sub_const y x
  have h2 : HasDerivAt (fun z => combHDeriv (x + z)) (combHSecond (x + y)) y :=
    (hasDerivAt_combHDeriv (by linarith : 0 < x + y)).comp_const_add x y
  have h3 : HasDerivAt (fun z => deriv langerTau z / (langerTau z - langerTau x))
      ((deriv (deriv langerTau) y * (langerTau y - langerTau x) - deriv langerTau y * deriv langerTau y) /
        (langerTau y - langerTau x) ^ 2) y :=
    (hasDerivAt_deriv_langerTau hy).div ((hasDerivAt_langerTau_pos hy).sub_const _) hS.ne'
  have h := (h1.add h2).sub h3
  have heq : deriv (langerK x) =ᶠ[𝓝 y] fun z => combHDeriv (z - x) + combHDeriv (x + z) -
      deriv langerTau z / (langerTau z - langerTau x) := by
    filter_upwards [Ioi_mem_nhds hxy] with z hz
    exact deriv_langerK_gt hx hz
  rw [(h.congr_of_eventuallyEq heq).deriv]
  ring

end Up

section Down

variable {x y : ℝ}

lemma deriv_langerK_lt (hy : 0 < y) (hxy : y < x) :
    deriv (langerK x) y = -combHDeriv (x - y) + combHDeriv (x + y) +
      deriv langerTau y / (langerTau x - langerTau y) := by
  have hx : 0 < x := lt_trans hy hxy
  have hS : 0 < langerTau x - langerTau y := by
    have := langerTau_strictMonoOn (Set.mem_Ioi.2 hy) (Set.mem_Ioi.2 hx) hxy; linarith
  have h1 : HasDerivAt (fun z => combH (x - z)) (-combHDeriv (x - y)) y :=
    (hasDerivAt_combH (sub_pos.2 hxy)).comp_const_sub x y
  have h2 : HasDerivAt (fun z => combH (x + z)) (combHDeriv (x + y)) y :=
    (hasDerivAt_combH (by linarith : 0 < x + y)).comp_const_add x y
  have h3 : HasDerivAt (fun z => Real.log (langerTau x - langerTau z))
      ((0 - deriv langerTau y) / (langerTau x - langerTau y)) y :=
    ((hasDerivAt_const y (langerTau x)).sub (hasDerivAt_langerTau_pos hy)).log hS.ne'
  have h := (h1.add h2).sub h3
  have heq : langerK x =ᶠ[𝓝 y] fun z => combH (x - z) + combH (x + z) -
      Real.log (langerTau x - langerTau z) := by
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < y from hy) hxy] with z hz
    exact langerK_lt hz.1 hz.2
  rw [(h.congr_of_eventuallyEq heq).deriv]
  ring

lemma deriv2_langerK_lt (hy : 0 < y) (hxy : y < x) :
    deriv (deriv (langerK x)) y = combHSecond (x - y) + combHSecond (x + y) +
      (deriv (deriv langerTau) y * (langerTau x - langerTau y) + deriv langerTau y ^ 2) /
        (langerTau x - langerTau y) ^ 2 := by
  have hx : 0 < x := lt_trans hy hxy
  have hS : 0 < langerTau x - langerTau y := by
    have := langerTau_strictMonoOn (Set.mem_Ioi.2 hy) (Set.mem_Ioi.2 hx) hxy; linarith
  have h1 : HasDerivAt (fun z => combHDeriv (x - z)) (-combHSecond (x - y)) y :=
    (hasDerivAt_combHDeriv (sub_pos.2 hxy)).comp_const_sub x y
  have h2 : HasDerivAt (fun z => combHDeriv (x + z)) (combHSecond (x + y)) y :=
    (hasDerivAt_combHDeriv (by linarith : 0 < x + y)).comp_const_add x y
  have h3 : HasDerivAt (fun z => deriv langerTau z / (langerTau x - langerTau z))
      ((deriv (deriv langerTau) y * (langerTau x - langerTau y) -
        deriv langerTau y * (0 - deriv langerTau y)) / (langerTau x - langerTau y) ^ 2) y :=
    (hasDerivAt_deriv_langerTau hy).div
      ((hasDerivAt_const y (langerTau x)).sub (hasDerivAt_langerTau_pos hy)) hS.ne'
  have h := ((h1.neg).add h2).add h3
  have heq : deriv (langerK x) =ᶠ[𝓝 y] fun z => -combHDeriv (x - z) + combHDeriv (x + z) +
      deriv langerTau z / (langerTau x - langerTau z) := by
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < y from hy) hxy] with z hz
    exact deriv_langerK_lt hz.1 hz.2
  rw [(h.congr_of_eventuallyEq heq).deriv]
  ring

end Down

/-! ### The general formula through the difference quotient -/

/-- `L = log T`, smooth on all of `ℝ`. -/
noncomputable def langerL (w : ℝ) : ℝ := Real.log (langerT w)

lemma contDiff_langerL (m : ℕ) : ContDiff ℝ m langerL :=
  (contDiff_langerT m).log fun w => (langerT_pos w).ne'

lemma langerK_eq_L {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    langerK x z = langerL (x - z) - Real.log (langerD x z) + combH (x + z) := by
  unfold langerK langerQ2 langerL combH
  rw [Real.log_div (langerT_pos _).ne' (langerD_pos hx hz).ne']

lemma contDiffOn_langerD (m : ℕ) {x : ℝ} (hx : 0 < x) : ContDiffOn ℝ m (langerD x) (Ioi 0) :=
  fun _ hz => (contDiffAt_langerD m hx hz).contDiffWithinAt

lemma hasDerivAt_langerD {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (langerD x) (deriv (langerD x) y) y :=
  (((contDiffOn_langerD 1 hx).differentiableOn one_ne_zero).differentiableAt
    (Ioi_mem_nhds hy)).hasDerivAt

lemma hasDerivAt_deriv_langerD {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (deriv (langerD x)) (deriv (deriv (langerD x)) y) y := by
  have h1 : ContDiffOn ℝ 1 (deriv (langerD x)) (Ioi 0) :=
    (contDiffOn_langerD 2 hx).deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact ((h1.differentiableOn one_ne_zero).differentiableAt (Ioi_mem_nhds hy)).hasDerivAt

lemma hasDerivAt_langerL (w : ℝ) : HasDerivAt langerL (deriv langerL w) w :=
  (((contDiff_langerL 1).differentiable one_ne_zero) w).hasDerivAt

lemma hasDerivAt_deriv_langerL (w : ℝ) : HasDerivAt (deriv langerL) (deriv (deriv langerL) w) w :=
  ((((contDiff_langerL 2).iterate_deriv' 1 1).differentiable one_ne_zero) w).hasDerivAt

lemma deriv_langerK_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    deriv (langerK x) y = -deriv langerL (x - y) -
      deriv (langerD x) y / langerD x y + combHDeriv (x + y) := by
  have hD := langerD_pos hx hy
  have g1 : HasDerivAt (fun z => langerL (x - z)) (-deriv langerL (x - y)) y :=
    (hasDerivAt_langerL (x - y)).comp_const_sub x y
  have g2 : HasDerivAt (fun z => Real.log (langerD x z))
      (deriv (langerD x) y / langerD x y) y := (hasDerivAt_langerD hx hy).log hD.ne'
  have g3 : HasDerivAt (fun z => combH (x + z)) (combHDeriv (x + y)) y :=
    (hasDerivAt_combH (by linarith : 0 < x + y)).comp_const_add x y
  have h := (g1.sub g2).add g3
  have heq : langerK x =ᶠ[𝓝 y] fun z => langerL (x - z) - Real.log (langerD x z) + combH (x + z) := by
    filter_upwards [Ioi_mem_nhds hy] with z hz
    exact langerK_eq_L hx hz
  rw [(h.congr_of_eventuallyEq heq).deriv]

lemma deriv2_langerK_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    deriv (deriv (langerK x)) y = deriv (deriv langerL) (x - y) -
      (deriv (deriv (langerD x)) y * langerD x y - deriv (langerD x) y ^ 2) / langerD x y ^ 2 +
        combHSecond (x + y) := by
  have hD := langerD_pos hx hy
  have g1 : HasDerivAt (fun z => -deriv langerL (x - z)) (deriv (deriv langerL) (x - y)) y :=
    ((hasDerivAt_deriv_langerL (x - y)).comp_const_sub x y).neg.congr_deriv (neg_neg _)
  have g2 : HasDerivAt (fun z => deriv (langerD x) z / langerD x z)
      ((deriv (deriv (langerD x)) y * langerD x y - deriv (langerD x) y * deriv (langerD x) y) /
        langerD x y ^ 2) y :=
    (hasDerivAt_deriv_langerD hx hy).div (hasDerivAt_langerD hx hy) hD.ne'
  have g3 : HasDerivAt (fun z => combHDeriv (x + z)) (combHSecond (x + y)) y :=
    (hasDerivAt_combHDeriv (by linarith : 0 < x + y)).comp_const_add x y
  have h := (g1.sub g2).add g3
  have heq : deriv (langerK x) =ᶠ[𝓝 y] fun z => -deriv langerL (x - z) -
      deriv (langerD x) z / langerD x z + combHDeriv (x + z) := by
    filter_upwards [Ioi_mem_nhds hy] with z hz
    exact deriv_langerK_eq hx hz
  rw [(h.congr_of_eventuallyEq heq).deriv]
  ring

/-! ### Near the diagonal: Hadamard integrals -/

open FormalResearch.Special in
lemma ball_subset_Ioi_of_le {x ρ : ℝ} (hρ : ρ ≤ x) : ball x ρ ⊆ Ioi 0 := by
  intro y hy
  rw [mem_ball, Real.dist_eq, abs_lt] at hy
  show 0 < y
  linarith [hy.1]

open FormalResearch.Special in
lemma langerD_eq_hadInt {x ρ y : ℝ} (hρ : ρ ≤ x) (hy : y ∈ ball x ρ) :
    langerD x y = hadInt (fun _ => 1) (deriv langerTau) x y := by
  have hF : ContDiffOn ℝ 1 langerTau (ball x ρ) :=
    (contDiffOn_langerTau 1).mono (ball_subset_Ioi_of_le hρ)
  exact dslope_eq_hadInt hF hy

open FormalResearch.Special in
lemma deriv_langerD_eq {x ρ y : ℝ} (hρ : ρ ≤ x) (hy : y ∈ ball x ρ) :
    deriv (langerD x) y = hadInt (fun t => t * 1) (deriv (deriv langerTau)) x y := by
  have hK : ContDiffOn ℝ 1 (deriv langerTau) (ball x ρ) :=
    contDiffOn_deriv_langerTau.mono (ball_subset_Ioi_of_le hρ)
  have h := hasDerivAt_hadInt (c := x) (ρ := ρ) (w := fun _ => 1) continuous_const hK hy
  have heq : langerD x =ᶠ[𝓝 y] hadInt (fun _ => 1) (deriv langerTau) x := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    exact langerD_eq_hadInt hρ hz
  exact (h.congr_of_eventuallyEq heq).deriv

open FormalResearch.Special in
lemma deriv2_langerD_eq {x ρ y : ℝ} (hρ : ρ ≤ x) (hy : y ∈ ball x ρ) :
    deriv (deriv (langerD x)) y =
      hadInt (fun t => t * (t * 1)) (deriv (deriv (deriv langerTau))) x y := by
  have hK : ContDiffOn ℝ 1 (deriv (deriv langerTau)) (ball x ρ) :=
    contDiffOn_deriv2_langerTau.mono (ball_subset_Ioi_of_le hρ)
  have h := hasDerivAt_hadInt (c := x) (ρ := ρ) (w := fun t => t * 1)
    (continuous_id.mul continuous_const) hK hy
  have heq : deriv (langerD x) =ᶠ[𝓝 y] hadInt (fun t => t * 1) (deriv (deriv langerTau)) x := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    exact deriv_langerD_eq hρ hz
  exact (h.congr_of_eventuallyEq heq).deriv

end FormalResearch.ModularBootstrap.Upper.Ramped
