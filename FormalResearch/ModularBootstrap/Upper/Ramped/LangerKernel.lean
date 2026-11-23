module

public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerSites
public import FormalResearch.ModularBootstrap.Upper.Comb.Factors

/-!
# `(F2)`: the smooth part `K(x, y)` of the site weight

`remainder.tex`, Proposition 1.2(2), input `(F2)`: `f_x(y) = log|τ(x) - τ(y)| + K(x, y)` with
`K = log Q + log tanh(π(x+y)/2)`, `Q = tanh(π(x-y)/2)/(τ(x) - τ(y))`.

`Q` is written as the quotient of two Hadamard difference quotients,
`Q(x,y) = T(x - y)/D(x,y)`, `T(w) = tanh(πw/2)/w` (`langerT`), `D(x,y) = (τ(x) - τ(y))/(x - y)`
(`langerD`, `dslope`), so that the removable singularity on the diagonal is built in.

* `langerQ`, `langerK`; `langerQ_pos`; `langerQ_diag` (`Q(x,x) = π/(2 τ'(x))`);
* `contDiffOn_langerK`: `y ↦ K(x,y)` is `C^m` on `(0, ∞)`;
* `langerK_gt`, `langerK_lt`: `K = 𝔥(|x-y|) + 𝔥(x+y) - log|τ(x) - τ(y)|` for `y ≠ x`
  (`𝔥 = combH = log tanh(π·/2)`), and `realLogT_eq_log_add_langerK`: `f_x(y) = log|τ(x)-τ(y)| + K(x,y)`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb

/-! ### `T(w) = tanh(πw/2)/w` -/

lemma contDiff_tanhHalf {n : ℕ∞} : ContDiff ℝ n (fun z : ℝ => Real.tanh (π * z / 2)) := by
  have h : (fun z : ℝ => Real.tanh (π * z / 2)) =
      fun z => Real.sinh (π * z / 2) / Real.cosh (π * z / 2) := by
    funext z; exact Real.tanh_eq_sinh_div_cosh _
  rw [h]
  exact (Real.contDiff_sinh.comp (by fun_prop)).div (Real.contDiff_cosh.comp (by fun_prop))
    fun z => (Real.cosh_pos _).ne'

/-- `T(w) = tanh(πw/2)/w`, with `T(0) = π/2` (Hadamard difference quotient of `tanh(π·/2)` at `0`). -/
noncomputable def langerT (w : ℝ) : ℝ := dslope (fun z : ℝ => Real.tanh (π * z / 2)) 0 w

lemma langerT_of_ne {w : ℝ} (hw : w ≠ 0) : langerT w = Real.tanh (π * w / 2) / w := by
  unfold langerT
  rw [dslope_of_ne _ hw, slope_def_field]
  simp

lemma hasDerivAt_tanhHalf_zero : HasDerivAt (fun z : ℝ => Real.tanh (π * z / 2)) (π / 2) 0 := by
  have h : (fun z : ℝ => Real.tanh (π * z / 2)) =
      fun z => Real.sinh (π * z / 2) / Real.cosh (π * z / 2) := by
    funext z; exact Real.tanh_eq_sinh_div_cosh _
  rw [h]
  have h1 : HasDerivAt (fun z : ℝ => π * z / 2) (π / 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul π).div_const 2
  have hs := (Real.hasDerivAt_sinh (π * 0 / 2)).comp 0 h1
  have hc := (Real.hasDerivAt_cosh (π * 0 / 2)).comp 0 h1
  have := hs.div hc (by simp)
  refine this.congr_deriv ?_
  simp

lemma langerT_zero : langerT 0 = π / 2 := by
  unfold langerT
  rw [dslope_same]
  exact hasDerivAt_tanhHalf_zero.deriv

lemma langerT_pos (w : ℝ) : 0 < langerT w := by
  by_cases hw : w = 0
  · rw [hw, langerT_zero]; positivity
  · rw [langerT_of_ne hw]
    rcases lt_or_gt_of_ne hw with h | h
    · have : Real.tanh (π * w / 2) < 0 := by
        have h1 := tanh_pos_of_pos (t := π * (-w) / 2) (by have := Real.pi_pos; nlinarith)
        have : Real.tanh (π * (-w) / 2) = - Real.tanh (π * w / 2) := by
          rw [← Real.tanh_neg]; congr 1; ring
        linarith
      exact div_pos_of_neg_of_neg this h
    · exact div_pos (tanh_pos_of_pos (by have := Real.pi_pos; positivity)) h

lemma contDiff_langerT (m : ℕ) : ContDiff ℝ m langerT := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w = 0
  · subst hw
    exact FormalResearch.Special.contDiffAt_dslope m contDiff_tanhHalf.contDiffAt
  · have heq : (fun z : ℝ => Real.tanh (π * z / 2) / z) =ᶠ[𝓝 w] langerT := by
      filter_upwards [isOpen_ne.mem_nhds (show w ∈ {z : ℝ | z ≠ 0} from hw)] with z hz
      exact (langerT_of_ne hz).symm
    refine ContDiffAt.congr_of_eventuallyEq ?_ heq.symm
    exact contDiff_tanhHalf.contDiffAt.div contDiffAt_id hw

/-! ### `D(x,y) = (τ(x) - τ(y))/(x - y)` -/

/-- `D(x, y) = (τ(x) - τ(y))/(x - y)` with the value `τ'(x)` on the diagonal. -/
noncomputable def langerD (x y : ℝ) : ℝ := dslope langerTau x y

lemma langerD_of_ne {x y : ℝ} (hxy : y ≠ x) :
    langerD x y = (langerTau x - langerTau y) / (x - y) := by
  unfold langerD
  rw [dslope_of_ne _ hxy, slope_def_field]
  have : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  field_simp
  ring

lemma langerD_diag {x : ℝ} : langerD x x = deriv langerTau x := by
  unfold langerD; rw [dslope_same]

lemma langerD_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < langerD x y := by
  by_cases hxy : y = x
  · subst hxy; rw [langerD_diag]; exact deriv_langerTau_pos hy
  · rw [langerD_of_ne hxy]
    rcases lt_or_gt_of_ne hxy with h | h
    · have := langerTau_strictMonoOn (Set.mem_Ioi.2 hy) (Set.mem_Ioi.2 hx) h
      exact div_pos (by linarith) (by linarith)
    · have := langerTau_strictMonoOn (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) h
      exact div_pos_of_neg_of_neg (by linarith) (by linarith)

lemma contDiffAt_langerD (m : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ContDiffAt ℝ m (langerD x) y := by
  by_cases hxy : y = x
  · subst hxy
    exact FormalResearch.Special.contDiffAt_dslope m
      (((contDiffOn_langerTau (m + 1)).contDiffAt (Ioi_mem_nhds hy)))
  · have heq : (fun z : ℝ => (langerTau z - langerTau x) / (z - x)) =ᶠ[𝓝 y] langerD x := by
      filter_upwards [isOpen_ne.mem_nhds (show y ∈ {z : ℝ | z ≠ x} from hxy)] with z hz
      unfold langerD
      rw [dslope_of_ne _ hz, slope_def_field]
    refine ContDiffAt.congr_of_eventuallyEq ?_ heq.symm
    have hτ : ContDiffAt ℝ m langerTau y := (contDiffOn_langerTau m).contDiffAt (Ioi_mem_nhds hy)
    exact (hτ.sub contDiffAt_const).div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.2 hxy)

/-! ### `Q` and `K` -/

/-- `Q(x,y) = tanh(π(x-y)/2)/(τ(x) - τ(y))`, with the value `π/(2τ'(x))` on the diagonal. -/
noncomputable def langerQ2 (x y : ℝ) : ℝ := langerT (x - y) / langerD x y

/-- `K(x,y) = log Q(x,y) + log tanh(π(x+y)/2)`. -/
noncomputable def langerK (x y : ℝ) : ℝ :=
  Real.log (langerQ2 x y) + Real.log (Real.tanh (π * (x + y) / 2))

lemma langerQ2_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < langerQ2 x y :=
  div_pos (langerT_pos _) (langerD_pos hx hy)

lemma langerQ2_of_ne {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : y ≠ x) :
    langerQ2 x y = Real.tanh (π * (x - y) / 2) / (langerTau x - langerTau y) := by
  unfold langerQ2
  have h1 : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  rw [langerT_of_ne h1, langerD_of_ne hxy]
  have h2 : langerTau x - langerTau y ≠ 0 := by
    intro h
    have h3 : langerD x y = 0 := by rw [langerD_of_ne hxy, h, zero_div]
    exact (langerD_pos hx hy).ne' h3
  field_simp

/-- `Q(x,x) = π/(2τ'(x))`. -/
lemma langerQ2_diag {x : ℝ} : langerQ2 x x = π / (2 * deriv langerTau x) := by
  unfold langerQ2
  rw [sub_self, langerT_zero, langerD_diag]
  rcases eq_or_ne (deriv langerTau x) 0 with h | h
  · simp [h]
  · field_simp

lemma contDiffOn_langerK (m : ℕ) {x : ℝ} (hx : 0 < x) :
    ContDiffOn ℝ m (langerK x) (Ioi 0) := by
  intro y hy
  have hy' : 0 < y := hy
  have hT : ContDiffAt ℝ m (fun z => langerT (x - z)) y :=
    ((contDiff_langerT m).contDiffAt).comp y (contDiffAt_const.sub contDiffAt_id)
  have hQ : ContDiffAt ℝ m (langerQ2 x) y :=
    hT.div (contDiffAt_langerD m hx hy') (langerD_pos hx hy').ne'
  have htanh : ContDiffAt ℝ m (fun z => Real.tanh (π * (x + z) / 2)) y :=
    (contDiff_tanhHalf.contDiffAt (x := x + y)).comp y (contDiffAt_const.add contDiffAt_id)
  have hpos : 0 < Real.tanh (π * (x + y) / 2) := tanh_pos_of_pos (by have := Real.pi_pos; positivity)
  have : ContDiffAt ℝ m (langerK x) y := by
    unfold langerK
    exact (hQ.log (langerQ2_pos hx hy').ne').add (htanh.log hpos.ne')
  exact this.contDiffWithinAt

/-! ### Explicit formulas away from the diagonal -/

lemma tanh_neg_half (w : ℝ) : Real.tanh (π * (-w) / 2) = -Real.tanh (π * w / 2) := by
  rw [← Real.tanh_neg]; congr 1; ring

/-- For `x < y`: `K(x,y) = 𝔥(y - x) + 𝔥(x + y) - log(τ(y) - τ(x))`. -/
lemma langerK_gt {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    langerK x y = combH (y - x) + combH (x + y) - Real.log (langerTau y - langerTau x) := by
  have hy : 0 < y := lt_trans hx hxy
  have hτ : 0 < langerTau y - langerTau x := by
    have := langerTau_strictMonoOn (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) hxy; linarith
  have hth : 0 < Real.tanh (π * (y - x) / 2) := tanh_pos_of_pos (by have := Real.pi_pos; nlinarith)
  unfold langerK combH
  rw [langerQ2_of_ne hx hy hxy.ne']
  have e1 : Real.tanh (π * (x - y) / 2) = -Real.tanh (π * (y - x) / 2) := by
    rw [← tanh_neg_half]; congr 1; ring
  have e2 : langerTau x - langerTau y = -(langerTau y - langerTau x) := by ring
  rw [e1, e2, neg_div_neg_eq, Real.log_div hth.ne' hτ.ne']
  ring

/-- For `0 < y < x`: `K(x,y) = 𝔥(x - y) + 𝔥(x + y) - log(τ(x) - τ(y))`. -/
lemma langerK_lt {x y : ℝ} (hy : 0 < y) (hxy : y < x) :
    langerK x y = combH (x - y) + combH (x + y) - Real.log (langerTau x - langerTau y) := by
  have hx : 0 < x := lt_trans hy hxy
  have hτ : 0 < langerTau x - langerTau y := by
    have := langerTau_strictMonoOn (Set.mem_Ioi.2 hy) (Set.mem_Ioi.2 hx) hxy; linarith
  have hth : 0 < Real.tanh (π * (x - y) / 2) := tanh_pos_of_pos (by have := Real.pi_pos; nlinarith)
  unfold langerK combH
  rw [langerQ2_of_ne hx hy hxy.ne, Real.log_div hth.ne' hτ.ne']
  ring

private lemma complex_tanh_ofReal' (x : ℝ) :
    Complex.tanh (x : ℂ) = ((Real.tanh x : ℝ) : ℂ) := by
  rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]

lemma realLogT_eq_combH {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : y ≠ x) :
    realLogT x y = combH |x - y| + combH (x + y) := by
  have hpi := Real.pi_pos
  have e : blaschkeT (y : ℂ) (x : ℂ) =
      ((Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2) : ℝ) : ℂ) := by
    unfold blaschkeT
    have h1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (y : ℂ)) / 2) = ((Real.tanh (π * (x - y) / 2) : ℝ) : ℂ) := by
      rw [← complex_tanh_ofReal']; congr 1; push_cast; ring
    have h2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (y : ℂ)) / 2) = ((Real.tanh (π * (x + y) / 2) : ℝ) : ℂ) := by
      rw [← complex_tanh_ofReal']; congr 1; push_cast; ring
    rw [h1, h2]; push_cast; ring
  have hp2 : 0 < Real.tanh (π * (x + y) / 2) := tanh_pos_of_pos (by positivity)
  have hne : Real.tanh (π * (x - y) / 2) ≠ 0 := by
    intro h
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have := tanh_pos_of_pos (t := π * (x - y) / 2) (by nlinarith)
      linarith
    · have := tanh_pos_of_pos (t := π * (y - x) / 2) (by nlinarith)
      rw [show π * (y - x) / 2 = π * (-(x - y)) / 2 by ring, tanh_neg_half, h] at this
      simp at this
  unfold realLogT
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hp2,
    Real.log_mul (abs_pos.2 hne).ne' hp2.ne']
  unfold combH
  congr 1
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · rw [abs_of_pos (sub_pos.2 hlt), abs_of_pos (tanh_pos_of_pos (by nlinarith))]
  · have h3 : x - y < 0 := by linarith
    rw [abs_of_neg h3, abs_of_neg, ← Real.tanh_neg]
    · congr 1; ring_nf
    · have : 0 < Real.tanh (π * (y - x) / 2) := tanh_pos_of_pos (by nlinarith)
      rw [show π * (y - x) / 2 = π * (-(x - y)) / 2 by ring, tanh_neg_half] at this
      linarith

/-- `f_x(y) = log|τ(x) - τ(y)| + K(x,y)` for `x, y > 0`, `y ≠ x`. -/
theorem realLogT_eq_log_add_langerK {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : y ≠ x) :
    realLogT x y = Real.log |langerTau x - langerTau y| + langerK x y := by
  rw [realLogT_eq_combH hx hy hxy]
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hτ : 0 < langerTau x - langerTau y := by
      have := langerTau_strictMonoOn (Set.mem_Ioi.2 hy) (Set.mem_Ioi.2 hx) hlt; linarith
    rw [langerK_lt hy hlt, abs_of_pos hτ, abs_of_pos (sub_pos.2 hlt)]
    ring
  · have hτ : langerTau x - langerTau y < 0 := by
      have := langerTau_strictMonoOn (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) hgt; linarith
    have e1 : |langerTau x - langerTau y| = langerTau y - langerTau x := by
      rw [abs_of_neg hτ]; ring
    have e2 : |x - y| = y - x := by
      rw [abs_of_neg (by linarith : x - y < 0)]; ring
    rw [langerK_gt hx hgt, e1, e2]
    ring

/-- `K(x, ξ_*) = K_*(x) = log[tanh(π|x-ξ_*|/2) tanh(π(x+ξ_*)/2)/|τ(x)|]` for `x ≠ ξ_*`. -/
theorem langerK_xiStar {x : ℝ} (hx : 0 < x) (hxs : x ≠ xiStar) :
    langerK x xiStar = Real.log (Real.tanh (π * |x - xiStar| / 2) *
      Real.tanh (π * (x + xiStar) / 2) / |langerTau x|) := by
  have hy := xiStar_pos
  have h := realLogT_eq_log_add_langerK hx hy (Ne.symm hxs)
  rw [langerTau_xiStar, sub_zero] at h
  have hτ : langerTau x ≠ 0 := by
    intro h0
    have : langerTau x = langerTau xiStar := by rw [h0, langerTau_xiStar]
    exact hxs (langerTau_strictMonoOn.injOn (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) this)
  have hab : 0 < |langerTau x| := abs_pos.2 hτ
  have e := realLogT_eq_combH hx hy (Ne.symm hxs)
  have hp1 : 0 < Real.tanh (π * |x - xiStar| / 2) :=
    tanh_pos_of_pos (by have := Real.pi_pos; have := abs_pos.2 (sub_ne_zero.2 hxs); positivity)
  have hp2 : 0 < Real.tanh (π * (x + xiStar) / 2) := tanh_pos_of_pos (by have := Real.pi_pos; positivity)
  rw [Real.log_div (mul_pos hp1 hp2).ne' hab.ne', Real.log_mul hp1.ne' hp2.ne']
  unfold combH at e
  linarith

end FormalResearch.ModularBootstrap.Upper.Ramped
