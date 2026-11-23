module

public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerTauForms

/-!
# Proposition 1.2(1): the Langer coordinate `τ`

`remainder.tex`, Proposition 1.2(1) (`rem:P1.2`).  For `x ≥ ξ_*`, `τ = (N/k_tip)^{2/3}`
(`langerTau_eq_of_ge`), and for `0 < x ≤ ξ_*`, `τ = -(slitDeficit(ξ_* - x)/(2π k_tip))^{2/3}`
(`langerTau_eq_of_le`).  Main statement `langerTau_spec`:

* `τ` is `C^m` on `(0, ∞)` for every `m` (the paper claims real-analytic; every use below is a `C^m` bound,
  and `(F2)` needs `C³`),
* `τ(ξ_*) = 0`, `τ'(ξ_*) = 1`, `τ' > 0` on `(0, ∞)`,
* `N(x) = k_tip τ(x)^{3/2}` for `x ≥ ξ_*` (`N = cumulN`),
* `-(U + L)(x) = 2π k_tip |τ(x)|^{3/2}` for `0 < x ≤ ξ_*`
  (`U + L = majorantReal + slitL`, the harmonic majorant plus the slit potential, Lemma G).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb

/-! ### Smoothness of `ρ_U` and `N` off the tip -/

lemma contDiffAt_arccoshR {z : ℝ} (hz : 1 < z) {m : ℕ} : ContDiffAt ℝ m arccoshR z := by
  have hs : 0 < √(z ^ 2 - 1) := Real.sqrt_pos.2 (by nlinarith)
  have h1 : ContDiffAt ℝ m (fun x : ℝ => √(x ^ 2 - 1)) z :=
    ((contDiffAt_id.pow 2).sub contDiffAt_const).sqrt
      (by show z ^ 2 - 1 ≠ 0; have : 0 < z ^ 2 - 1 := by nlinarith
          exact this.ne')
  unfold arccoshR
  exact (contDiffAt_id.add h1).log (by have := hs; simp only [id]; linarith [hz])

lemma contDiffOn_rhoU (m : ℕ) : ContDiffOn ℝ m rhoU (Ioi xiStar) := by
  intro y hy
  have hy' : xiStar < y := hy
  have h1 : 1 < Real.sinh (π * y) := by
    rw [← sinh_pi_mul_xiStar]
    exact Real.sinh_lt_sinh.2 (by have := Real.pi_pos; nlinarith)
  have hsh : ContDiffAt ℝ m (fun y : ℝ => Real.sinh (π * y)) y :=
    Real.contDiff_sinh.contDiffAt.comp y (contDiffAt_const.mul contDiffAt_id)
  have hat : ContDiffAt ℝ m (fun y : ℝ => (4 / (3 * π)) * arccoshR (Real.sinh (π * y))) y :=
    contDiffAt_const.mul (ContDiffAt.comp y (g := arccoshR) (contDiffAt_arccoshR h1) hsh)
  have heq : (fun y : ℝ => (4 / (3 * π)) * arccoshR (Real.sinh (π * y))) =ᶠ[𝓝 y] rhoU := by
    filter_upwards [Ioi_mem_nhds hy'] with z hz
    exact (rhoU_eq_of_ge (le_of_lt hz)).symm
  exact (hat.congr_of_eventuallyEq heq.symm).contDiffWithinAt

lemma contDiffOn_cumulN (m : ℕ) : ContDiffOn ℝ m cumulN (Ioi xiStar) := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact continuousOn_cumulN.mono Ioi_subset_Ici_self
  | succ m ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy => (hasDerivAt_cumulN hy).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    have h2 : ContDiffOn ℝ m (fun y => rhoU y / 2) (Ioi xiStar) :=
      (contDiffOn_rhoU m).div_const 2
    exact h2.congr fun y hy => (hasDerivAt_cumulN hy).deriv

lemma cumulN_nonneg {x : ℝ} (hx : xiStar ≤ x) : 0 ≤ cumulN x := by
  have := cumulN_strictMonoOn.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  rwa [cumulN_xiStar] at this

lemma cumulN_pos {x : ℝ} (hx : xiStar < x) : 0 < cumulN x := by
  have := cumulN_strictMonoOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx.le) hx
  rwa [cumulN_xiStar] at this

/-! ### Formulas for `τ` -/

lemma langerJ_eq_of_pos {r : ℝ} (hr : 0 < r) :
    langerJ r = 2 * cumulN (xiStar + r) / r ^ (3 / 2 : ℝ) := by
  have h := langerJ_mul_rpow_of_pos hr
  have hp : 0 < r ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hr _
  have hint : ∫ s in (0 : ℝ)..r, rhoU (xiStar + s) = 2 * cumulN (xiStar + r) := by
    unfold cumulN
    have := intervalIntegral.integral_comp_add_left rhoU xiStar (a := 0) (b := r)
    rw [add_zero] at this
    rw [this]; ring
  rw [hint] at h
  rw [eq_div_iff hp.ne']; exact h

lemma langerTau_eq_of_gt {x : ℝ} (hx : xiStar < x) :
    langerTau x = (cumulN x / kTip) ^ (2 / 3 : ℝ) := by
  set r := x - xiStar with hr
  have hr0 : 0 < r := by linarith
  have hx' : xiStar + r = x := by rw [hr]; ring
  have hp : 0 < r ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hr0 _
  have hk := kTip_pos
  have hN := cumulN_pos hx
  unfold langerTau
  rw [← hr, langerJ_eq_of_pos hr0, hx']
  have e : 2 * cumulN x / r ^ (3 / 2 : ℝ) / (2 * kTip) = (cumulN x / kTip) / r ^ (3 / 2 : ℝ) := by
    field_simp
  rw [e, Real.div_rpow (by positivity) hp.le, ← Real.rpow_mul hr0.le]
  have : (3 / 2 : ℝ) * (2 / 3) = 1 := by norm_num
  rw [this, Real.rpow_one]
  field_simp

lemma langerTau_xiStar : langerTau xiStar = 0 := by
  unfold langerTau; simp

lemma langerTau_eq_of_ge {x : ℝ} (hx : xiStar ≤ x) :
    langerTau x = (cumulN x / kTip) ^ (2 / 3 : ℝ) := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, langerTau_xiStar, cumulN_xiStar, zero_div, Real.zero_rpow (by norm_num)]
  · exact langerTau_eq_of_gt h

/-- For `0 < x < ξ_*`: `τ(x) = -(D(x)/(2π k_tip))^{2/3}` with `D(x) = slitDeficit(ξ_* - x)`. -/
lemma langerTau_eq_of_lt {x : ℝ} (hx0 : 0 < x) (hx : x < xiStar) :
    langerTau x = -(slitDeficit (xiStar - x) / (2 * π * kTip)) ^ (2 / 3 : ℝ) := by
  set r := x - xiStar with hr
  have hr0 : r < 0 := by linarith
  have hr1 : -xiStar < r := by linarith
  set R := -r with hR
  have hR0 : 0 < R := by linarith
  have hRx : R = xiStar - x := by rw [hR, hr]; ring
  have hp : 0 < R ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hR0 _
  have hk := kTip_pos
  have hpi := Real.pi_pos
  have hJ := langerJ_pos_ball (r := r) (by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith)
  have hmul := langerJ_mul_rpow_of_neg hr1 hr0
  rw [← hR] at hmul
  unfold langerTau
  rw [← hr]
  have hD : slitDeficit (xiStar - x) = π * (langerJ r * R ^ (3 / 2 : ℝ)) := by
    rw [← hRx]; exact hmul.symm
  have e : langerJ r / (2 * kTip) = (slitDeficit (xiStar - x) / (2 * π * kTip)) / R ^ (3 / 2 : ℝ) := by
    rw [hD]; field_simp
  have hDnn : 0 ≤ slitDeficit (xiStar - x) / (2 * π * kTip) := by
    rw [hD]; positivity
  rw [e, Real.div_rpow hDnn hp.le, ← Real.rpow_mul hR0.le]
  have : (3 / 2 : ℝ) * (2 / 3) = 1 := by norm_num
  rw [this, Real.rpow_one]
  have : r = -R := by rw [hR]; ring
  rw [this]
  field_simp

lemma slitDeficit_zero : slitDeficit 0 = 0 := by
  unfold slitDeficit; simp

/-! ### Smoothness -/

lemma contDiffOn_langerTau (m : ℕ) : ContDiffOn ℝ m langerTau (Ioi 0) := by
  refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
  have hx0 : 0 < x := hx
  by_cases hxs : xiStar < x
  · refine ⟨Ioi xiStar, isOpen_Ioi, hxs, ?_⟩
    have h1 : ContDiffOn ℝ m (fun y => (cumulN y / kTip) ^ (2 / 3 : ℝ)) (Ioi 0 ∩ Ioi xiStar) := by
      intro y hy
      have hy' : xiStar < y := hy.2
      have hN : ContDiffAt ℝ m cumulN y := (contDiffOn_cumulN m).contDiffAt (Ioi_mem_nhds hy')
      have hk := kTip_pos
      have hNp := cumulN_pos hy'
      exact ((hN.div_const kTip).rpow_const_of_ne (by positivity)).contDiffWithinAt
    exact h1.congr fun y hy => langerTau_eq_of_gt hy.2
  · refine ⟨Iio (2 * xiStar), isOpen_Iio, by show x < 2 * xiStar; linarith [not_lt.1 hxs, xiStar_pos], ?_⟩
    intro y hy
    have hy1 : 0 < y := hy.1
    have hy2 : y < 2 * xiStar := hy.2
    have hyball : y - xiStar ∈ ball (0 : ℝ) xiStar := by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith
    have hJ : ContDiffAt ℝ m (fun y => langerJ (y - xiStar)) y :=
      ((contDiffOn_langerJ m).contDiffAt (isOpen_ball.mem_nhds hyball)).comp y
        (contDiffAt_id.sub contDiffAt_const)
    have hk := kTip_pos
    have hJp := langerJ_pos_ball hyball
    have : ContDiffAt ℝ m langerTau y := by
      unfold langerTau
      exact (contDiffAt_id.sub contDiffAt_const).mul
        ((hJ.div_const _).rpow_const_of_ne (by positivity))
    exact this.contDiffWithinAt

/-! ### Derivative of `τ` -/

lemma deriv_langerTau_pos_of_gt {x : ℝ} (hx : xiStar < x) : 0 < deriv langerTau x := by
  have hk := kTip_pos
  have hNp := cumulN_pos hx
  have h1 : HasDerivAt (fun y => cumulN y / kTip) (rhoU x / 2 / kTip) x :=
    (hasDerivAt_cumulN hx).div_const _
  have h2 := h1.rpow_const (p := (2 / 3 : ℝ)) (Or.inl (by positivity))
  have heq : (fun y => (cumulN y / kTip) ^ (2 / 3 : ℝ)) =ᶠ[𝓝 x] langerTau := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (langerTau_eq_of_gt hy).symm
  rw [(h2.congr_of_eventuallyEq heq.symm).deriv]
  have := rhoU_pos hx
  positivity

lemma deriv_langerTau_pos_of_lt {x : ℝ} (hx0 : 0 < x) (hx : x < xiStar) : 0 < deriv langerTau x := by
  have hk := kTip_pos
  have hpi := Real.pi_pos
  have hg : Continuous (fun s : ℝ => Real.arccos (Real.sinh (π * s))) :=
    Real.continuous_arccos.comp (Real.continuous_sinh.comp (continuous_const.mul continuous_id))
  set A : ℝ → ℝ := fun y => ∫ s in xiStar..y, Real.arccos (Real.sinh (π * s)) with hA
  have hAd : ∀ y, HasDerivAt A (Real.arccos (Real.sinh (π * y))) y := fun y =>
    (Continuous.integral_hasStrictDerivAt hg xiStar y).hasDerivAt
  have hDA : ∀ y, slitDeficit (xiStar - y) = -(4 / 3) * A y := by
    intro y
    unfold slitDeficit
    rw [sub_sub_cancel, intervalIntegral.integral_symm]
    simp only [hA]; ring
  set Bf : ℝ → ℝ := fun y => (-(4 / 3) * A y) / (2 * π * kTip) with hBf
  have hBd : HasDerivAt Bf ((-(4 / 3) * Real.arccos (Real.sinh (π * x))) / (2 * π * kTip)) x :=
    ((hAd x).const_mul (-(4 / 3))).div_const _
  have hBpos : 0 < Bf x := by
    have hball : (xiStar - x) ∈ ball (0 : ℝ) xiStar := by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith
    have hmul := langerJ_mul_rpow_of_neg (r := x - xiStar) (by linarith) (by linarith)
    have hJp := langerJ_pos_ball (r := x - xiStar) (by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith)
    have hR : -(x - xiStar) = xiStar - x := by ring
    rw [hR] at hmul
    have hRp : 0 < (xiStar - x) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hD : 0 < slitDeficit (xiStar - x) := by rw [← hmul]; positivity
    show 0 < (-(4 / 3) * A x) / (2 * π * kTip)
    rw [← hDA]; positivity
  have h2 := (hBd.rpow_const (p := (2 / 3 : ℝ)) (Or.inl hBpos.ne')).neg
  have heq : (fun y => -(Bf y) ^ (2 / 3 : ℝ)) =ᶠ[𝓝 x] langerTau := by
    have : Ioo 0 xiStar ∈ 𝓝 x := Ioo_mem_nhds hx0 hx
    filter_upwards [this] with y hy
    rw [langerTau_eq_of_lt hy.1 hy.2, hBf]
    simp only [hDA]
  rw [(h2.congr_of_eventuallyEq heq.symm).deriv]
  have hga : 0 < Real.arccos (Real.sinh (π * x)) := by
    rw [Real.arccos_pos]
    rw [← sinh_pi_mul_xiStar]
    exact Real.sinh_lt_sinh.2 (by nlinarith)
  have hp : 0 < Bf x ^ (2 / 3 - 1 : ℝ) := Real.rpow_pos_of_pos hBpos _
  have : 0 < -((-(4 / 3) * Real.arccos (Real.sinh (π * x))) / (2 * π * kTip) * (2 / 3) *
      Bf x ^ (2 / 3 - 1 : ℝ)) := by
    rw [neg_pos]
    have : (-(4 / 3) * Real.arccos (Real.sinh (π * x))) / (2 * π * kTip) < 0 := by
      apply div_neg_of_neg_of_pos
      · nlinarith
      · positivity
    nlinarith [mul_pos hp (by norm_num : (0:ℝ) < 2 / 3)]
  exact this

lemma hasDerivAt_langerTau_xiStar : HasDerivAt langerTau 1 xiStar := by
  have hk := kTip_pos
  have hball : (0 : ℝ) ∈ ball (0 : ℝ) xiStar := mem_ball_self xiStar_pos
  have hJc : ContDiffAt ℝ 1 langerJ 0 := (contDiffOn_langerJ 1).contDiffAt (isOpen_ball.mem_nhds hball)
  have hG : ContDiffAt ℝ 1 (fun x => (langerJ (x - xiStar) / (2 * kTip)) ^ (2 / 3 : ℝ)) xiStar := by
    have h1 : ContDiffAt ℝ 1 (fun x => langerJ (x - xiStar)) xiStar := by
      have h2 : ContDiffAt ℝ 1 langerJ (xiStar - xiStar) := by rw [sub_self]; exact hJc
      exact ContDiffAt.comp (f := fun x : ℝ => x - xiStar) xiStar h2
        (contDiffAt_id.sub contDiffAt_const)
    refine (h1.div_const _).rpow_const_of_ne ?_
    simp only [sub_self, langerJ_zero]
    positivity
  have h := ((hasDerivAt_id xiStar).sub_const xiStar).mul (hG.differentiableAt one_ne_zero).hasDerivAt
  have h' : HasDerivAt langerTau _ xiStar := h
  convert h' using 1
  simp only [id, sub_self, zero_mul, add_zero, one_mul, langerJ_zero]
  have : 2 * kTip / (2 * kTip) = 1 := by field_simp
  rw [this, Real.one_rpow]

lemma deriv_langerTau_xiStar : deriv langerTau xiStar = 1 := hasDerivAt_langerTau_xiStar.deriv

lemma deriv_langerTau_pos {x : ℝ} (hx : 0 < x) : 0 < deriv langerTau x := by
  rcases lt_trichotomy x xiStar with h | h | h
  · exact deriv_langerTau_pos_of_lt hx h
  · rw [h, deriv_langerTau_xiStar]; exact one_pos
  · exact deriv_langerTau_pos_of_gt h

lemma slitDeficit_pos_of_lt {R : ℝ} (hR0 : 0 < R) (hR : R < xiStar) : 0 < slitDeficit R := by
  have hmul := langerJ_mul_rpow_of_neg (r := -R) (by linarith) (by linarith)
  have hJp := langerJ_pos_ball (r := -R) (by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith)
  rw [neg_neg] at hmul
  have hRp : 0 < R ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hR0 _
  rw [← hmul]; have := Real.pi_pos; positivity

/-- `N(x) = k_tip τ(x)^{3/2}` for `x ≥ ξ_*`. -/
lemma cumulN_eq_kTip_mul_langerTau {x : ℝ} (hx : xiStar ≤ x) :
    cumulN x = kTip * langerTau x ^ (3 / 2 : ℝ) := by
  rw [langerTau_eq_of_ge hx, ← Real.rpow_mul (div_nonneg (cumulN_nonneg hx) kTip_pos.le)]
  have : (2 / 3 : ℝ) * (3 / 2) = 1 := by norm_num
  rw [this, Real.rpow_one]
  have := kTip_pos
  field_simp

/-- `-(U + L)(x) = 2π k_tip |τ(x)|^{3/2}` for `0 < x ≤ ξ_*`. -/
lemma neg_majorant_add_slitL_eq {x : ℝ} (hx0 : 0 < x) (hx : x ≤ xiStar) :
    -(majorantReal x + slitL x) = 2 * π * kTip * |langerTau x| ^ (3 / 2 : ℝ) := by
  have hk := kTip_pos
  have hpi := Real.pi_pos
  have hid := majorant_add_L_eq_neg_slitDeficit (x := x) (by rw [abs_of_pos hx0]; exact hx)
  rw [hid, abs_of_pos hx0, neg_neg]
  rcases hx.eq_or_lt with h | h
  · rw [h, sub_self, slitDeficit_zero, langerTau_xiStar]
    simp
  · have hD := slitDeficit_pos_of_lt (R := xiStar - x) (by linarith) (by linarith)
    rw [langerTau_eq_of_lt hx0 h, abs_neg, abs_of_nonneg (by positivity),
      ← Real.rpow_mul (by positivity)]
    have : (2 / 3 : ℝ) * (3 / 2) = 1 := by norm_num
    rw [this, Real.rpow_one]
    field_simp

/-- **Proposition 1.2(1)** (`rem:P1.2`): the Langer coordinate `τ`.  `τ` is `C^m` on `(0, ∞)` for every
`m` (the paper states real-analytic), `τ(ξ_*) = 0`, `τ'(ξ_*) = 1`, `τ' > 0`,
`N(x) = k_tip τ(x)^{3/2}` for `x ≥ ξ_*` and `-(U + L)(x) = 2π k_tip |τ(x)|^{3/2}` for `0 < x ≤ ξ_*`. -/
theorem langerTau_spec :
    (∀ m : ℕ, ContDiffOn ℝ m langerTau (Ioi 0)) ∧ langerTau xiStar = 0 ∧
      deriv langerTau xiStar = 1 ∧ (∀ x : ℝ, 0 < x → 0 < deriv langerTau x) ∧
      (∀ x : ℝ, xiStar ≤ x → cumulN x = kTip * langerTau x ^ (3 / 2 : ℝ)) ∧
      (∀ x : ℝ, 0 < x → x ≤ xiStar →
        -(majorantReal x + slitL x) = 2 * π * kTip * |langerTau x| ^ (3 / 2 : ℝ)) :=
  ⟨contDiffOn_langerTau, langerTau_xiStar, deriv_langerTau_xiStar, fun _ hx => deriv_langerTau_pos hx,
    fun _ hx => cumulN_eq_kTip_mul_langerTau hx, fun _ hx0 hx => neg_majorant_add_slitL_eq hx0 hx⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.langerTau_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerTau_spec

end FormalResearch.ModularBootstrap.Upper.Ramped
