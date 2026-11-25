module

public import FormalResearch.ModularBootstrap.SlitStrip.PoissonJensenInput

/-!
# Non-vacuity of the geometric `PoissonJensenInput`

`slitStripPoissonJensenInput` (real-slice data from the conformal map, harmonic majorant `U`
with proved `g_deficit`) is realised together with a `FixedGapInput` and an explicit
`WeaklyFeasibleTest` for every `c' ≥ c_PJ`, so the hypotheses that remain for `theorem_A_geometry`
(the Poisson--Jensen inequality `hPJ` and the Bessel/fixed-gap estimates) are jointly satisfiable
with the geometry actually proved.  The witness is the one of `slitStrip_hypotheses_nonvacuous`,
which only uses `0 ≤ slitMass ≤ 1`, `0 ≤ slitEntropy` and `U(x) = -(2π/3)x - slitDeficit(ξ_*-x)`,
the last being `majorant_add_L_eq_neg_slitDeficit`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap

private lemma slitMass_le_one' (x : ℝ) {y : ℝ} (hy : 0 < y) : slitMass x y ≤ 1 := by
  unfold slitMass
  calc ∫ σ in slitPreimage, poissonKernel x y σ
      ≤ ∫ σ : ℝ, poissonKernel x y σ :=
        setIntegral_le_integral (integrable_poissonKernel x hy)
          (Eventually.of_forall fun σ => poissonKernel_nonneg hy.le σ)
    _ = 1 := integral_poissonKernel x hy

private lemma slitDeficit_mono' {δ₁ δ₂ : ℝ} (h1 : 0 ≤ δ₁) (h12 : δ₁ ≤ δ₂) (_h2 : δ₂ ≤ xiStar) :
    slitDeficit δ₁ ≤ slitDeficit δ₂ := by
  unfold slitDeficit; gcongr
  have hint : IntervalIntegrable (fun s : ℝ => Real.arccos (Real.sinh (π * s)))
      volume (xiStar - δ₂) xiStar :=
    (Real.continuous_arccos.comp (Real.continuous_sinh.comp (by fun_prop))).intervalIntegrable _ _
  have hI1 : uIcc (xiStar - δ₂) (xiStar - δ₁) ⊆ uIcc (xiStar - δ₂) xiStar := by
    rw [uIcc_of_le (by linarith : xiStar - δ₂ ≤ xiStar - δ₁),
      uIcc_of_le (by linarith : xiStar - δ₂ ≤ xiStar)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have hI2 : uIcc (xiStar - δ₁) xiStar ⊆ uIcc (xiStar - δ₂) xiStar := by
    rw [uIcc_of_le (by linarith : xiStar - δ₁ ≤ xiStar),
      uIcc_of_le (by linarith : xiStar - δ₂ ≤ xiStar)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hsub := intervalIntegral.integral_add_adjacent_intervals (hint.mono_set hI1)
    (hint.mono_set hI2)
  have hnn : 0 ≤ ∫ s in (xiStar - δ₂)..(xiStar - δ₁), Real.arccos (Real.sinh (π * s)) :=
    intervalIntegral.integral_nonneg (by linarith) fun s _ => Real.arccos_nonneg _
  linarith


/-- On `[0, ξ_*)` the majorant is `-(2π/3) x - slitDeficit(ξ_* - x)`. -/
private lemma majorantReal_eq_of_mem {x : ℝ} (hx : x ∈ Ico 0 xiStar) :
    majorantReal x = -(2 * π / 3) * x - slitDeficit (xiStar - x) := by
  have habs : |x| = x := abs_of_nonneg hx.1
  have h := majorant_add_L_eq_neg_slitDeficit (x := x) (by rw [habs]; exact hx.2.le)
  rw [habs] at h
  unfold slitL at h
  rw [habs] at h
  linarith

/-- **Non-vacuity of the geometric `PoissonJensenInput`:** with `fg` suitable, every `c' ≥ 1` admits
a `WeaklyFeasibleTest` for `slitStripPoissonJensenInput 1 (log 3) 1`. -/
theorem slitStripPoissonJensenInput_nonvacuous :
    ∃ fg : FixedGapInput, ∀ c' : ℝ,
      (slitStripPoissonJensenInput 1 (Real.log 3) 1 le_rfl one_pos).c_PJ ≤ c' →
        Nonempty (WeaklyFeasibleTest
          (slitStripPoissonJensenInput 1 (Real.log 3) 1 le_rfl one_pos) fg c') := by
  let pj : PoissonJensenInput := slitStripPoissonJensenInput 1 (Real.log 3) 1 le_rfl one_pos
  let δ₀ : ℝ := xiStar - 0.05
  have hδ₀_pos : 0 < δ₀ := sub_pos.mpr xiStar_gt_005
  have hκ_pos : 0 < slitDeficit δ₀ :=
    lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos hδ₀_pos _))
      (slitDeficit_ge hδ₀_pos.le (by dsimp [δ₀]; linarith))
  let fg : FixedGapInput :=
    { c_deep := 1, C_deep := 1, κ_deep := slitDeficit δ₀,
      hc_deep := le_rfl, hC_deep := zero_le_one, hκ_deep := hκ_pos }
  refine ⟨fg, fun c' hc' => ?_⟩
  have hc'_pos : 0 < c' := zero_lt_one.trans_le hc'
  let T₀ : ℝ := c' * xiStar ^ 2 / 3
  let T₁ : ℝ := c' * (xiStar + 1) ^ 2 / 3
  have hT₀_pos : 0 < T₀ := by have := xiStar_pos; dsimp [T₀]; positivity
  have hT₀_lt_T₁ : T₀ < T₁ := by
    dsimp [T₀, T₁]; have : xiStar ^ 2 < (xiStar + 1) ^ 2 := by nlinarith [xiStar_pos]
    gcongr
  let V : ℝ → ℝ := fun t => Real.exp (c' * ((2 * π / 3) * Real.sqrt (3 * t / c'))) / Real.sqrt c'
  let W : ℝ → ℝ := fun t => slitDeficit (max 0 (xiStar - Real.sqrt (3 * t / c')))
  let g : ℝ → ℝ := fun t =>
    Real.exp (-c' * ((2 * π / 3) * Real.sqrt (3 * t / c')) - c' * W t - max 0 (t - T₁)) /
      Real.sqrt c'
  have hW_cont : Continuous W := by
    dsimp [W, slitDeficit]
    refine Continuous.const_mul ?_ _
    let F_int : ℝ → ℝ := fun a => ∫ s in (0 : ℝ)..a, Real.arccos (Real.sinh (π * s))
    have hint_arc : ∀ a b : ℝ, IntervalIntegrable (fun s => Real.arccos (Real.sinh (π * s)))
        volume a b := fun a b =>
      (Real.continuous_arccos.comp (Real.continuous_sinh.comp (by fun_prop))).intervalIntegrable a b
    have hsplit : ∀ δ : ℝ, ∫ s in (xiStar - δ)..xiStar, Real.arccos (Real.sinh (π * s)) =
        F_int xiStar - F_int (xiStar - δ) := fun δ => by
      dsimp [F_int]
      linarith [intervalIntegral.integral_add_adjacent_intervals (hint_arc 0 (xiStar - δ))
        (hint_arc (xiStar - δ) xiStar)]
    simp_rw [hsplit]
    exact continuous_const.sub ((intervalIntegral.continuous_primitive hint_arc 0).comp
      (continuous_const.sub (continuous_const.max
        (continuous_const.sub ((continuous_const.mul continuous_id).div_const c').sqrt))))
  have hg_cont : ContinuousOn g (Ici 0) :=
    (Continuous.rexp (((continuous_const.mul (continuous_const.mul
      (((continuous_const.mul continuous_id).div_const c').sqrt))).sub
      (continuous_const.mul hW_cont)).sub
      (continuous_const.max (continuous_id.sub continuous_const)))).div_const _ |>.continuousOn
  have hV_cont : ContinuousOn V (Ici 0) := by dsimp [V]; fun_prop
  have hV_nonneg : ∀ t ≥ 0, 0 ≤ V t := fun t _ => by dsimp [V]; positivity
  have hprod_eq : ∀ t : ℝ, |g t| * V t = c'⁻¹ * Real.exp (-c' * W t - max 0 (t - T₁)) := by
    intro t
    rw [abs_of_pos (by dsimp [g]; positivity : 0 < g t)]
    dsimp [g, V]
    have hsq : Real.sqrt c' * Real.sqrt c' = c' := Real.mul_self_sqrt hc'_pos.le
    rw [div_mul_div_comm, hsq, ← Real.exp_add]
    rw [show (-c' * (2 * π / 3 * Real.sqrt (3 * t / c')) - c' * W t - max 0 (t - T₁) +
      c' * (2 * π / 3 * Real.sqrt (3 * t / c'))) = -c' * W t - max 0 (t - T₁) by ring]
    ring
  have hprod_tail : ∀ t : ℝ, T₁ ≤ t → |g t| * V t = c'⁻¹ * Real.exp (T₁ - t) := by
    intro t ht; rw [hprod_eq t]
    have hge : xiStar ≤ Real.sqrt (3 * t / c') := by
      have harg : xiStar ^ 2 ≤ 3 * t / c' := by
        rw [le_div_iff₀ hc'_pos]; dsimp [T₀] at hT₀_lt_T₁; linarith [hT₀_lt_T₁.le.trans ht]
      simpa [Real.sqrt_sq xiStar_pos.le] using Real.sqrt_le_sqrt harg
    have hW0 : W t = 0 := by dsimp [W]; rw [max_eq_left (sub_nonpos.mpr hge)]; unfold slitDeficit; simp
    rw [hW0, mul_zero, zero_sub, max_eq_right (sub_nonneg.mpr ht)]; congr 2; ring
  have hint_tail : IntegrableOn (fun t => |g t| * V t) (Ioi T₁) :=
    IntegrableOn.congr_fun
      ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) T₁).const_mul (c'⁻¹ * Real.exp T₁))
      (fun t ht => by
        rw [hprod_tail t (mem_Ioi.mp ht).le, mul_assoc, ← Real.exp_add]; congr 2; ring)
      measurableSet_Ioi
  have hint_all : IntegrableOn (fun t => |g t| * V t) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (le_trans hT₀_pos.le hT₀_lt_T₁.le)]
    exact (((hg_cont.abs.mul hV_cont).mono fun t ht => mem_Ici.mpr ht.1).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self).union hint_tail
  let M : ℝ := ∫ t in Ioi 0, |g t| * V t
  have hmid_val : ∫ t in T₀..T₁, |g t| * V t = (2 * xiStar + 1) / 3 := by
    have heq : EqOn (fun t => |g t| * V t) (fun _ => c'⁻¹) (uIcc T₀ T₁) := by
      intro t ht
      rw [uIcc_of_le hT₀_lt_T₁.le, mem_Icc] at ht
      dsimp only; rw [hprod_eq t]
      have hge : xiStar ≤ Real.sqrt (3 * t / c') := by
        have harg : xiStar ^ 2 ≤ 3 * t / c' := by rw [le_div_iff₀ hc'_pos]; dsimp [T₀] at ht; linarith
        simpa [Real.sqrt_sq xiStar_pos.le] using Real.sqrt_le_sqrt harg
      have hW0 : W t = 0 := by dsimp [W]; rw [max_eq_left (sub_nonpos.mpr hge)]; unfold slitDeficit; simp
      rw [hW0, mul_zero, zero_sub, max_eq_left (sub_nonpos.mpr ht.2), neg_zero, Real.exp_zero, mul_one]
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_const, smul_eq_mul]
    dsimp [T₀, T₁]; field_simp [hc'_pos.ne']; ring
  have hM_lb : 1 / 3 < M := by
    have hsub : Ioc T₀ T₁ ⊆ Ioi 0 := Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hT₀_pos.le)
    have hle : ∫ t in Ioc T₀ T₁, |g t| * V t ≤ M :=
      setIntegral_mono_set hint_all (Eventually.of_forall fun t =>
        mul_nonneg (abs_nonneg _) (by dsimp [V]; positivity)) hsub.eventuallySubset
    rw [← intervalIntegral.integral_of_le hT₀_lt_T₁.le, hmid_val] at hle
    linarith [xiStar_pos]
  let t₁ : ℝ := T₁ + 2
  have ht₁_pos : 0 < t₁ := by dsimp [t₁]; linarith
  have ht₁_tail_val : ∫ t in Ioi t₁, |g t| * V t = c'⁻¹ * Real.exp (-2) := by
    have heq : EqOn (fun t => |g t| * V t) (fun t => (c'⁻¹ * Real.exp T₁) * Real.exp (-1 * t))
        (Ioi t₁) := fun t ht => by
      dsimp only; rw [hprod_tail t (by dsimp [t₁] at ht; linarith [mem_Ioi.mp ht]), mul_assoc, ← Real.exp_add]
      congr 2; ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
      integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) t₁, neg_one_mul]
    calc c'⁻¹ * Real.exp T₁ * (-Real.exp (-t₁) / -1)
        = c'⁻¹ * (Real.exp T₁ * Real.exp (-t₁)) := by ring
      _ = c'⁻¹ * Real.exp (T₁ - t₁) := by rw [← Real.exp_add, sub_eq_add_neg]
      _ = c'⁻¹ * Real.exp (-2) := by rw [show T₁ - t₁ = -2 by dsimp [t₁]; ring]
  have hhalf : M / 2 ≤ ∫ t in (0 : ℝ)..t₁, |g t| * V t := by
    have hsplit : (∫ t in Ioc 0 t₁, |g t| * V t) + (∫ t in Ioi t₁, |g t| * V t) = M := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
          (hint_all.mono_set Ioc_subset_Ioi_self) (hint_all.mono_set (Ioi_subset_Ioi ht₁_pos.le)),
        Ioc_union_Ioi_eq_Ioi ht₁_pos.le]
    rw [intervalIntegral.integral_of_le ht₁_pos.le]
    have hexp2 : Real.exp (-2 : ℝ) < 1 / 6 := by
      have h27 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h729 : (7.29 : ℝ) < Real.exp 2 := by
        have h3 : (2.7 : ℝ) ^ 2 < Real.exp 1 ^ 2 := by gcongr
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 2) (by norm_num)]; linarith
    have htail_lt : c'⁻¹ * Real.exp (-2) < M / 2 := by
      calc c'⁻¹ * Real.exp (-2) ≤ 1 * Real.exp (-2) :=
            mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hc') (Real.exp_pos _).le
        _ < 1 / 6 := by linarith
        _ < M / 2 := by linarith
    linarith
  have hsqrt_x : ∀ x : ℝ, 0 ≤ x → Real.sqrt (3 * (c' * x ^ 2 / 3) / c') = x := fun x hx => by
    rw [show 3 * (c' * x ^ 2 / 3) / c' = x ^ 2 by field_simp [hc'_pos.ne'] ]
    exact Real.sqrt_sq hx
  refine ⟨⟨g, V, V, M, t₁, lt_trans (by positivity) hM_lb, ht₁_pos.le, hg_cont, hV_cont, hV_nonneg,
    hint_all, rfl, fun x _ => by linarith [hV_nonneg (c' * x ^ 2 / 3) (by positivity)], ?_, ?_, ?_, hhalf⟩⟩
  · intro x hx
    have hCK : pj.C_K = 1 := rfl
    dsimp [V]; rw [hsqrt_x x (by linarith [hx.1]), hCK, one_mul]
  · intro x hx _
    have hT_le : c' * x ^ 2 / 3 ≤ T₁ := by
      dsimp [T₁]; have : x ^ 2 ≤ (xiStar + 1) ^ 2 := by nlinarith [hx.1, hx.2]
      gcongr
    have hW_eq : W (c' * x ^ 2 / 3) = slitDeficit (xiStar - x) := by
      dsimp [W]; rw [hsqrt_x x hx.1, max_eq_right (sub_nonneg.mpr hx.2.le)]
    rw [abs_of_pos (by dsimp [g]; positivity : 0 < g (c' * x ^ 2 / 3))]
    dsimp [g]
    rw [hsqrt_x x hx.1, hW_eq, max_eq_left (sub_nonpos.mpr hT_le), sub_zero,
      Real.log_div (Real.exp_pos _).ne' (Real.sqrt_pos.mpr hc'_pos).ne', Real.log_exp,
      Real.sqrt_eq_rpow, Real.log_rpow hc'_pos]
    have hlogM : 0 ≤ Real.log M + Real.log 3 := by
      rw [← Real.log_mul (lt_trans (by positivity) hM_lb).ne' (by norm_num)]
      exact Real.log_nonneg (by linarith)
    have hyp : 0 < pj.rs.yUHP (xiStar - x) :=
      sliceIm_pos ⟨sub_pos.mpr hx.2, by linarith [hx.1]⟩
    have hmle : pj.rs.slitMassAt x ≤ 1 := slitMass_le_one' _ hyp
    have hm_nn : 0 ≤ (5 / 2 : ℝ) * (1 - pj.rs.slitMassAt x) * Real.log c' :=
      mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hmle)) (Real.log_nonneg hc')
    have hs_nn : 0 ≤ pj.rs.slitEntropyAt x := slitEntropy_nonneg _ hyp.le
    have hcU : c' * pj.U x = -c' * (2 * π / 3 * x) - c' * slitDeficit (xiStar - x) := by
      change c' * majorantReal x = _
      rw [majorantReal_eq_of_mem hx]
      ring
    have hCPJ : pj.C_PJ = Real.log 3 := rfl
    rw [hcU, hCPJ]
    linarith
  · intro _
    let t₀ : ℝ := c' * (0.05 : ℝ) ^ 2 / 3
    have hle : ∀ t ∈ Icc 0 t₀, |g t| * V t ≤ c'⁻¹ * Real.exp (-fg.κ_deep * c') := by
      intro t ht; rw [hprod_eq t]
      have hx_le : Real.sqrt (3 * t / c') ≤ 0.05 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 0.05)]
        exact Real.sqrt_le_sqrt (by rw [div_le_iff₀ hc'_pos]; dsimp [t₀] at ht; linarith [ht.2])
      have hW_ge : fg.κ_deep ≤ W t := by
        dsimp [W, fg]
        rw [max_eq_right (by dsimp [δ₀] at *; linarith)]
        exact slitDeficit_mono' hδ₀_pos.le (by dsimp [δ₀]; linarith)
          (by linarith [Real.sqrt_nonneg (3 * t / c')])
      have : -c' * W t - max 0 (t - T₁) ≤ -fg.κ_deep * c' := by
        nlinarith [le_max_left 0 (t - T₁), hc'_pos]
      gcongr
    have hint_t₀ : IntervalIntegrable (fun t => |g t| * V t) volume 0 t₀ :=
      ((hg_cont.abs.mul hV_cont).mono fun t ht => mem_Ici.mpr ht.1).intervalIntegrable_of_Icc
        (by dsimp [t₀]; positivity)
    calc ∫ t in (0 : ℝ)..t₀, |g t| * V t
        ≤ ∫ _t in (0 : ℝ)..t₀, c'⁻¹ * Real.exp (-fg.κ_deep * c') :=
          intervalIntegral.integral_mono_on (by dsimp [t₀]; positivity) hint_t₀
            intervalIntegrable_const hle
      _ = ((0.05 : ℝ) ^ 2 / 3) * Real.exp (-fg.κ_deep * c') := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
          dsimp [t₀]; field_simp [hc'_pos.ne']
      _ ≤ (1 / 3 : ℝ) * Real.exp (-fg.κ_deep * c') := by gcongr; norm_num
      _ ≤ fg.C_deep * Real.exp (-fg.κ_deep * c') * M :=
          (mul_le_mul_of_nonneg_right hM_lb.le (Real.exp_pos _).le).trans_eq (by
            change _ = (1 : ℝ) * _ * _; ring)


/-! ### Axiom checks for the headline theorems -/

/-- info: 'FormalResearch.ModularBootstrap.slitStripPoissonJensenInput_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.slitStripPoissonJensenInput_nonvacuous

end FormalResearch.ModularBootstrap
