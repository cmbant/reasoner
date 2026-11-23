module

public import FormalResearch.ModularBootstrap.Upper.Ramped.ParamIntegral
public import FormalResearch.ModularBootstrap.Upper.Comb.ZeroLaw

/-!
# The Langer coordinate `τ` of the comb transfer: definitions and smoothness

`remainder.tex`, Proposition 1.2(1) (`rem:P1.2`): with `r = x - ξ_*`, `u(r) = sinh(π(ξ_* + r)) - 1`,
`H(r) = (4/(3π)) (u/r)^{1/2} ∫₀¹ 2 dt/(2 + u t²)^{1/2}`, `J(r) = ∫₀¹ 2 t² H(r t²) dt`,
`τ(ξ_* + r) = r (J(r)/(2 k_tip))^{2/3}`.

* `langerU`, `langerPsi`, `langerQ`, `langerH`, `langerJ`, `langerTau`: these definitions
  (`langerQ r = u(r)/r`, with the value `u'(0)` at `r = 0`, is the Hadamard quotient `dslope`).
* `contDiffOn_langerPsi`, `contDiffOn_langerH`, `contDiffOn_langerJ`: `ψ`, `H`, `J` are `C^m` for every `m`
  near the tip (`J` on `|r| < ξ_*`), by the reparametrised Hadamard integral of `ParamIntegral`.
* `langerH_pos`, `langerJ_pos`, `langerJ_zero`: `H > 0`, `J > 0` on `r > -ξ_*`, and `J(0) = 2 k_tip`.

Smoothness is proved in every order `m` (not only `C²`): the divided difference
`(τ(x) - τ(y))/(x - y)` of `(F2)` needs `τ ∈ C³` near the diagonal.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb

/-- `u(r) = sinh(π(ξ_* + r)) - 1`. -/
noncomputable def langerU (r : ℝ) : ℝ := Real.sinh (π * (xiStar + r)) - 1

/-- `ψ(u) = ∫₀¹ 2 dt / (2 + u t²)^{1/2}`. -/
noncomputable def langerPsi (u : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, 2 / √(2 + u * t ^ 2)

/-- The Hadamard quotient `u(r)/r` (value `u'(0)` at `r = 0`). -/
noncomputable def langerQ (r : ℝ) : ℝ := dslope langerU 0 r

/-- `H(r) = (4/(3π)) (u/r)^{1/2} ψ(u)`. -/
noncomputable def langerH (r : ℝ) : ℝ := (4 / (3 * π)) * √(langerQ r) * langerPsi (langerU r)

/-- `J(r) = ∫₀¹ 2 t² H(r t²) dt`. -/
noncomputable def langerJ (r : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, 2 * t ^ 2 * langerH (r * t ^ 2)

/-- The Langer coordinate `τ(ξ_* + r) = r (J(r)/(2 k_tip))^{2/3}`, as a function of `x = ξ_* + r`. -/
noncomputable def langerTau (x : ℝ) : ℝ :=
  (x - xiStar) * (langerJ (x - xiStar) / (2 * kTip)) ^ (2 / 3 : ℝ)

lemma langerU_zero : langerU 0 = 0 := by
  unfold langerU; rw [add_zero, mul_comm, ← mul_div_cancel_left₀ xiStar Real.pi_ne_zero]
  simp [mul_comm, sinh_pi_mul_xiStar]

lemma contDiff_langerU {n : ℕ∞} : ContDiff ℝ n langerU :=
  (Real.contDiff_sinh.comp (contDiff_const.mul (contDiff_const.add contDiff_id))).sub contDiff_const

lemma langerU_strictMono : StrictMono langerU := by
  intro a b hab
  unfold langerU
  have : Real.sinh (π * (xiStar + a)) < Real.sinh (π * (xiStar + b)) :=
    Real.sinh_lt_sinh.2 (by have := Real.pi_pos; nlinarith)
  linarith

lemma langerU_lt_two {r : ℝ} (hr : |r| < xiStar) : langerU r < 2 := by
  have hr' := (abs_lt.1 hr).2
  have h1 : Real.sinh (π * (xiStar + r)) < Real.sinh (π * (2 * xiStar)) :=
    Real.sinh_lt_sinh.2 (by have := Real.pi_pos; nlinarith)
  have h2 : Real.sinh (π * (2 * xiStar)) = 2 * √2 := by
    have hc : Real.cosh (π * xiStar) = √2 := by
      have := Real.cosh_sq (π * xiStar)
      rw [sinh_pi_mul_xiStar] at this
      have hpos := Real.cosh_pos (π * xiStar)
      rw [← Real.sqrt_sq hpos.le, this]; norm_num
    rw [show π * (2 * xiStar) = 2 * (π * xiStar) by ring, Real.sinh_two_mul, sinh_pi_mul_xiStar, hc]
    ring
  have hs : √2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold langerU; linarith

lemma neg_one_lt_langerU {r : ℝ} (hr : -xiStar < r) : -1 < langerU r := by
  have h1 : 0 < Real.sinh (π * (xiStar + r)) :=
    Real.sinh_pos_iff.2 (by have := Real.pi_pos; nlinarith [xiStar_pos])
  unfold langerU; linarith

lemma langerU_hasDerivAt (r : ℝ) :
    HasDerivAt langerU (π * Real.cosh (π * (xiStar + r))) r := by
  unfold langerU
  have h1 : HasDerivAt (fun r : ℝ => π * (xiStar + r)) π r := by
    simpa using ((hasDerivAt_id r).const_add xiStar).const_mul π
  have := (h1.sinh).sub_const 1
  simpa [mul_comm] using this

lemma langerQ_pos (r : ℝ) : 0 < langerQ r := by
  unfold langerQ
  by_cases hr : r = 0
  · subst hr
    rw [dslope_same, (langerU_hasDerivAt 0).deriv]
    have := Real.cosh_pos (π * (xiStar + 0)); have := Real.pi_pos; positivity
  · rw [dslope_of_ne _ hr, slope_def_field, langerU_zero, sub_zero]
    rcases lt_or_gt_of_ne hr with h | h
    · have := langerU_strictMono h; rw [langerU_zero] at this
      exact div_pos_of_neg_of_neg this (by linarith)
    · have := langerU_strictMono h; rw [langerU_zero] at this
      exact div_pos this (by linarith)

lemma langerQ_mul (r : ℝ) : langerQ r * r = langerU r := by
  unfold langerQ
  by_cases hr : r = 0
  · subst hr; simp [langerU_zero]
  · rw [dslope_of_ne _ hr, slope_def_field, langerU_zero, sub_zero, sub_zero]; field_simp

lemma contDiffOn_langerQ (m : ℕ) : ContDiffOn ℝ m langerQ (ball (0 : ℝ) xiStar) := by
  unfold langerQ
  exact FormalResearch.Special.contDiffOn_dslope m (contDiff_langerU.contDiffOn)

/-! ### The inner integral `ψ` -/

/-- The integrand profile `F(v) = 2/√(2+v)`. -/
noncomputable def langerF (v : ℝ) : ℝ := 2 / √(2 + v)

lemma contDiffOn_langerF (m : ℕ) : ContDiffOn ℝ m langerF (ball (0 : ℝ) 2) := by
  intro v hv
  have hv' : |v| < 2 := by simpa [Real.dist_eq] using hv
  have h2 : 0 < 2 + v := by linarith [(abs_lt.1 hv').1]
  have : ContDiffAt ℝ m langerF v := by
    unfold langerF
    exact contDiffAt_const.div ((contDiffAt_const.add contDiffAt_id).sqrt h2.ne')
      (Real.sqrt_pos.2 h2).ne'
  exact this.contDiffWithinAt

lemma langerPsi_eq_hadIntA (u : ℝ) :
    langerPsi u = hadIntA (fun t => t ^ 2) (fun _ => 1) langerF 0 u := by
  unfold langerPsi hadIntA langerF
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp [mul_comm]

lemma contDiffOn_langerPsi (m : ℕ) : ContDiffOn ℝ m langerPsi (ball (0 : ℝ) 2) := by
  have h := contDiffOn_hadIntA (c := 0) (ρ := 2) (a := fun t => t ^ 2) (by fun_prop)
    (fun t ht => ⟨by positivity, by nlinarith [ht.1, ht.2]⟩) m (fun _ => 1) langerF
    continuous_const (contDiffOn_langerF m)
  exact h.congr fun u _ => langerPsi_eq_hadIntA u

lemma langerPsi_pos {u : ℝ} (hu : -2 < u) : 0 < langerPsi u := by
  unfold langerPsi
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < 2 + u * t ^ 2 := by
    intro t ht
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have ht3 : 0 ≤ t ^ 2 := sq_nonneg t
    rcases le_or_gt 0 u with h | h <;> nlinarith
  have hcont : ContinuousOn (fun t : ℝ => 2 / √(2 + u * t ^ 2)) (Icc 0 1) := by
    refine continuousOn_const.div (by fun_prop) fun t ht => ?_
    exact (Real.sqrt_pos.2 (hpos t ht)).ne'
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable_of_Icc zero_le_one)
    (fun t ht => ?_) zero_lt_one
  have := hpos t ⟨ht.1.le, ht.2.le⟩
  have := Real.sqrt_pos.2 this
  positivity

/-! ### `H` and `J` -/

lemma abs_lt_of_mem_ball_xiStar {r : ℝ} (hr : r ∈ ball (0 : ℝ) xiStar) : |r| < xiStar := by
  simpa [Real.dist_eq] using hr

lemma langerU_mem_ball {r : ℝ} (hr : r ∈ ball (0 : ℝ) xiStar) : langerU r ∈ ball (0 : ℝ) 2 := by
  have h := abs_lt_of_mem_ball_xiStar hr
  have h1 := langerU_lt_two h
  have h2 := neg_one_lt_langerU (abs_lt.1 h).1
  rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith

lemma contDiffOn_langerH (m : ℕ) : ContDiffOn ℝ m langerH (ball (0 : ℝ) xiStar) := by
  intro r hr
  have hq : ContDiffAt ℝ m langerQ r :=
    (contDiffOn_langerQ m).contDiffAt (isOpen_ball.mem_nhds hr)
  have hpsi : ContDiffAt ℝ m langerPsi (langerU r) :=
    (contDiffOn_langerPsi m).contDiffAt (isOpen_ball.mem_nhds (langerU_mem_ball hr))
  have hu : ContDiffAt ℝ m langerU r := contDiff_langerU.contDiffAt
  have : ContDiffAt ℝ m langerH r := by
    unfold langerH
    exact (contDiffAt_const.mul (hq.sqrt (langerQ_pos r).ne')).mul (hpsi.comp r hu)
  exact this.contDiffWithinAt

lemma langerH_pos {r : ℝ} (hr : -xiStar < r) : 0 < langerH r := by
  unfold langerH
  have h1 := Real.sqrt_pos.2 (langerQ_pos r)
  have h2 : 0 < langerPsi (langerU r) :=
    langerPsi_pos (by linarith [neg_one_lt_langerU hr])
  have := Real.pi_pos
  positivity

lemma langerH_zero_eq : langerH 0 = 3 * kTip := by
  have hc : Real.cosh (π * xiStar) = √2 := by
    have := Real.cosh_sq (π * xiStar)
    rw [sinh_pi_mul_xiStar] at this
    have hpos := Real.cosh_pos (π * xiStar)
    rw [← Real.sqrt_sq hpos.le, this]; norm_num
  have hq0 : langerQ 0 = π * √2 := by
    unfold langerQ
    rw [dslope_same, (langerU_hasDerivAt 0).deriv, add_zero, hc]
  have hpsi0 : langerPsi (langerU 0) = √2 := by
    unfold langerPsi
    rw [langerU_zero]
    simp only [zero_mul, add_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
    have : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    linarith
  have hs : (0 : ℝ) < √π := Real.sqrt_pos.2 Real.pi_pos
  have hss : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  set a : ℝ := √(√2) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (Real.sqrt_pos.2 (by norm_num))
  have ha2 : a * a = √2 := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have h34 : (2 : ℝ) ^ (3 / 4 : ℝ) = a ^ 3 := by
    have : a = (2 : ℝ) ^ (1 / 4 : ℝ) := by
      rw [ha, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [this, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  unfold langerH kTip
  rw [hq0, hpsi0, h34, Real.sqrt_mul Real.pi_pos.le]
  change 4 / (3 * π) * (√π * a) * √2 = 3 * (4 * a ^ 3 / (9 * √π))
  have hpi := Real.pi_pos
  have h2 : √2 = a * a := ha2.symm
  rw [h2]
  field_simp
  nlinarith [hss]

lemma contDiffOn_langerJ (m : ℕ) : ContDiffOn ℝ m langerJ (ball (0 : ℝ) xiStar) := by
  have h := contDiffOn_hadIntA (c := 0) (ρ := xiStar) (a := fun t => t ^ 2) (by fun_prop)
    (fun t ht => ⟨by positivity, by nlinarith [ht.1, ht.2]⟩) m (fun t => 2 * t ^ 2) langerH
    (by fun_prop) (contDiffOn_langerH m)
  refine h.congr fun r _ => ?_
  unfold langerJ hadIntA
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp [mul_comm]

lemma langerJ_zero : langerJ 0 = 2 * kTip := by
  unfold langerJ
  simp only [zero_mul, langerH_zero_eq]
  have : ∀ t : ℝ, 2 * t ^ 2 * (3 * kTip) = (6 * kTip) * t ^ 2 := fun t => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

lemma langerJ_pos_ball {r : ℝ} (hr : r ∈ ball (0 : ℝ) xiStar) : 0 < langerJ r := by
  have hr' := abs_lt_of_mem_ball_xiStar hr
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, r * t ^ 2 ∈ ball (0 : ℝ) xiStar := by
    intro t ht
    rw [mem_ball, Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (sq_nonneg t)]
    have : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    calc |r| * t ^ 2 ≤ |r| * 1 := by gcongr
      _ < xiStar := by simpa using hr'
  have hcont : ContinuousOn (fun t : ℝ => 2 * t ^ 2 * langerH (r * t ^ 2)) (Icc 0 1) := by
    refine (by fun_prop : ContinuousOn (fun t : ℝ => 2 * t ^ 2) _).mul ?_
    exact (contDiffOn_langerH 0).continuousOn.comp (by fun_prop) hmem
  unfold langerJ
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (hcont.intervalIntegrable_of_Icc zero_le_one) (fun t ht => ?_) zero_lt_one
  have h1 := mem_ball.1 (hmem t ⟨ht.1.le, ht.2.le⟩)
  rw [Real.dist_eq, sub_zero] at h1
  have h2 := langerH_pos (r := r * t ^ 2) (by linarith [(abs_lt.1 h1).1])
  have : 0 < t := ht.1
  positivity

end FormalResearch.ModularBootstrap.Upper.Ramped
