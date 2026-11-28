module

public import Mathlib
public import FormalResearch.SignUncertainty.CtChartInverse
public import FormalResearch.ModularBootstrap.FiveTerm.LowerMainDefs

/-!
# Generic Lemma FJ(2) and Odd Holomorphic Factorisation (`LowerFoldChart`)

Shared fold-chart infrastructure for `cts:cauchy-dual` (1), `cts:phic-exp`, and `fj:lemma` (2):

1. `odd_holomorphic_factor`: an odd holomorphic function `f` on `ball 0 ρ` (`0 < r < ρ`, `‖f‖ ≤ B`
   on `closedBall 0 r`, real-symmetric `f (conj z) = conj (f z)`) factors cleanly as `f z = z * g (z^2)`
   with `g` holomorphic and real-symmetric on `ball 0 (r^2)`, `g 0 = deriv f 0`,
   `deriv g 0 = iteratedDeriv 3 f 0 / 6`, `‖g w‖ ≤ (4/3) B / r` on `closedBall 0 (r^2/4)`,
   and `‖deriv g w‖ ≤ (32/3) B / r^3` on `closedBall 0 (r^2/8)`.
2. `fj_inverse_chart`: generic Lemma FJ(2) — given scales `(mu, lam)` with `lam c * mu c = c⁻¹`
   and a family of holomorphic real-symmetric shift functions `ψ c` on a fixed disc `ball 0 ρ₀`
   with uniform bounds and jet `ψ c 0 = β + O(c^{-1})`, `ψ' c 0 = γ + O(c^{-1/3})`, constructs
   the inverse chart `phi c` and proves holomorphy on `ball 0 ρ_c` (`ρ_c > lowerRmax c1 c`),
   real symmetry, `‖phi c u - u‖ ≤ C c^{-1/3}`, `‖deriv (phi c) u - 1‖ ≤ C c^{-1}`,
   real inversion `uhat c (phi c x).re = x`, and the `cts:phic-exp` expansion at `a₁`.
-/

@[expose] public section

open Complex Metric Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.SignUncertainty

noncomputable section

/-! ### 1. Odd holomorphic factorisation with uniform Cauchy bounds -/

private lemma hasDerivAt_conj_conj {g : ℂ → ℂ} {z d : ℂ}
    (hg : HasDerivAt g d (starRingEnd ℂ z)) :
    HasDerivAt (fun w : ℂ => starRingEnd ℂ (g (starRingEnd ℂ w))) (starRingEnd ℂ d) z := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at hg ⊢
  have hcont : Continuous fun t : ℂ => starRingEnd ℂ t := Complex.continuous_conj
  have htend : Tendsto (fun t : ℂ => starRingEnd ℂ t) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨by simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, map_eq_zero] using ht
  have hlim := (hcont.tendsto d).comp (hg.comp htend)
  refine hlim.congr' (Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, smul_eq_mul]
  rw [map_mul, map_inv₀, Complex.conj_conj, map_sub, map_add]

private lemma odd_tsum_part_sum (a : ℕ → ℂ) (z : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (2 * N), a n * ((z ^ n - (-z) ^ n) / 2) =
      ∑ k ∈ Finset.range N, a (2 * k + 1) * z ^ (2 * k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 2 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    have h_even : (-z) ^ (2 * N) = z ^ (2 * N) := by
      rw [pow_mul, pow_mul, neg_sq]
    have h_odd : (-z) ^ (2 * N + 1) = -z ^ (2 * N + 1) := by
      rw [pow_succ, pow_succ, h_even]; ring
    rw [h_even, h_odd]
    ring

/-- **Odd holomorphic factorisation**: if `f` is holomorphic on `ball 0 ρ`, `0 < r < ρ`,
`‖f‖ ≤ B` on `closedBall 0 r`, `f (-z) = -f z`, and `f (conj z) = conj (f z)`, then `f z = z * g (z^2)`
where `g` is holomorphic and real-symmetric on `ball 0 (r^2)`, `g 0 = deriv f 0`,
`deriv g 0 = iteratedDeriv 3 f 0 / 6`, and satisfies Cauchy bounds on `r^2 / 4` and `r^2 / 8`. -/
theorem odd_holomorphic_factor {f : ℂ → ℂ} {ρ r B : ℝ}
    (_hρ : 0 < ρ) (hr0 : 0 < r) (hr : r < ρ) (hB0 : 0 ≤ B)
    (hf : DifferentiableOn ℂ f (ball 0 ρ))
    (hB : ∀ z ∈ closedBall (0 : ℂ) r, ‖f z‖ ≤ B)
    (hodd : ∀ z ∈ ball (0 : ℂ) ρ, f (-z) = -f z)
    (hconj : ∀ z ∈ ball (0 : ℂ) ρ, f (starRingEnd ℂ z) = starRingEnd ℂ (f z)) :
    ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball 0 (r ^ 2)) ∧
      (∀ w ∈ ball (0 : ℂ) (r ^ 2), g (starRingEnd ℂ w) = starRingEnd ℂ (g w)) ∧
      (∀ z ∈ ball (0 : ℂ) r, f z = z * g (z ^ 2)) ∧
      g 0 = deriv f 0 ∧
      deriv g 0 = iteratedDeriv 3 f 0 / 6 ∧
      (∀ w ∈ closedBall (0 : ℂ) (r ^ 2 / 4), ‖g w‖ ≤ 4 / 3 * B / r) ∧
      (∀ w ∈ closedBall (0 : ℂ) (r ^ 2 / 8), ‖deriv g w‖ ≤ 32 / 3 * B / r ^ 3) := by
  let a : ℕ → ℂ := fun n => (Nat.factorial n : ℂ)⁻¹ * iteratedDeriv n f 0
  let b : ℕ → ℂ := fun k => a (2 * k + 1)
  have ha_bd : ∀ n : ℕ, ‖a n‖ ≤ B / r ^ n := fun n => by
    have hcl : DiffContOnCl ℂ f (ball 0 r) :=
      (hf.mono (closure_ball_subset_closedBall.trans (closedBall_subset_ball hr))).diffContOnCl
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr0 hcl
      fun z hz => hB z (sphere_subset_closedBall hz)
    have hfac_pos : (0 : ℝ) < Nat.factorial n := Nat.cast_pos.mpr (Nat.factorial_pos n)
    dsimp [a]
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (Nat.factorial n : ℝ)⁻¹ * ‖iteratedDeriv n f 0‖
        ≤ (Nat.factorial n : ℝ)⁻¹ * ((Nat.factorial n : ℝ) * B / r ^ n) := by gcongr
      _ = B / r ^ n := by field_simp [hfac_pos.ne']
  have hb_bd : ∀ k : ℕ, ‖b k‖ ≤ B / r ^ (2 * k + 1) := fun k => ha_bd (2 * k + 1)
  let q : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ b
  have hrad : ENNReal.ofReal (r ^ 2) ≤ q.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
    have ht_lt : (t : ℝ) < r ^ 2 := by
      have : (t : ENNReal) < ENNReal.ofReal (r ^ 2) := ht
      rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hr0)] at this
    refine q.le_radius_of_summable_norm ?_
    have hq_norm : ∀ k : ℕ, ‖q k‖ * (t : ℝ) ^ k ≤ (B / r) * ((t : ℝ) / r ^ 2) ^ k := fun k => by
      rw [FormalMultilinearSeries.ofScalars_norm]
      have hk := hb_bd k
      have hr_pow : r ^ (2 * k + 1) = r * (r ^ 2) ^ k := by rw [pow_succ', pow_mul]
      rw [hr_pow] at hk
      calc ‖b k‖ * (t : ℝ) ^ k
          ≤ (B / (r * (r ^ 2) ^ k)) * (t : ℝ) ^ k := by gcongr
        _ = (B / r) * ((t : ℝ) / r ^ 2) ^ k := by rw [div_pow]; ring
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg t.2 _)) hq_norm ?_
    exact (summable_geometric_of_lt_one (div_nonneg t.2 (sq_nonneg r))
      ((div_lt_one (sq_pos_of_pos hr0)).mpr ht_lt)).mul_left _
  have hr2_pos : 0 < r ^ 2 := sq_pos_of_pos hr0
  have hr2_enn_pos : 0 < ENNReal.ofReal (r ^ 2) := ENNReal.ofReal_pos.mpr hr2_pos
  have hq_pos : 0 < q.radius := lt_of_lt_of_le hr2_enn_pos hrad
  have hbq : HasFPowerSeriesOnBall q.sum q 0 (ENNReal.ofReal (r ^ 2)) :=
    (q.hasFPowerSeriesOnBall hq_pos).mono hr2_enn_pos hrad
  let g : ℂ → ℂ := q.sum
  have mem_eb : ∀ {w : ℂ}, w ∈ ball (0 : ℂ) (r ^ 2) → w ∈ Metric.eball (0 : ℂ) (ENNReal.ofReal (r ^ 2)) := by
    intro w hw
    rw [Metric.mem_eball, edist_zero_right, eNorm_eq_nnNorm, ← ENNReal.ofReal_coe_nnreal, coe_nnNorm]
    exact (ENNReal.ofReal_lt_ofReal_iff hr2_pos).mpr (mem_ball_zero_iff.mp hw)
  have hg_diff : DifferentiableOn ℂ g (ball 0 (r ^ 2)) := fun w hw =>
    (hbq.differentiableOn w (mem_eb hw)).differentiableAt (Metric.isOpen_eball.mem_nhds (mem_eb hw)) |>.differentiableWithinAt
  have hg_sum : ∀ w ∈ ball (0 : ℂ) (r ^ 2), HasSum (fun k : ℕ => b k * w ^ k) (g w) := by
    intro w hw
    have h1 := hbq.hasSum (mem_eb hw)
    simp only [zero_add] at h1
    refine h1.congr_fun fun k => ?_
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have hg_eq : ∀ z ∈ ball (0 : ℂ) r, f z = z * g (z ^ 2) := by
    intro z hz
    have hz_ball : z ∈ ball (0 : ℂ) ρ := ball_subset_ball hr.le hz
    have hz_lt : ‖z‖ < r := mem_ball_zero_iff.mp hz
    have hz2_ball : z ^ 2 ∈ ball (0 : ℂ) (r ^ 2) := by
      rw [mem_ball_zero_iff, norm_pow]; exact pow_lt_pow_left₀ hz_lt (norm_nonneg _) two_ne_zero
    have hf_sub : DifferentiableOn ℂ f (ball 0 r) := hf.mono (ball_subset_ball hr.le)
    have hs_pos := Complex.hasSum_taylorSeries_on_ball hf_sub hz
    have hs_neg := Complex.hasSum_taylorSeries_on_ball hf_sub (by simpa using hz : -z ∈ ball (0 : ℂ) r)
    have hs_comb : HasSum (fun n : ℕ => a n * ((z ^ n - (-z) ^ n) / 2)) (f z) := by
      have hsub := hs_pos.sub hs_neg
      have hdiv := hsub.div_const 2
      have hval : (f z - f (-z)) / 2 = f z := by rw [hodd z hz_ball]; ring
      rw [hval] at hdiv
      refine hdiv.congr_fun fun n => ?_
      dsimp [a]
      simp only [sub_zero]
      ring
    have hs_g := (hg_sum (z ^ 2) hz2_ball).mul_left z
    have hlim_g : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, b k * z ^ (2 * k + 1)) atTop (𝓝 (z * g (z ^ 2))) := by
      have h := hs_g.tendsto_sum_nat
      refine h.congr fun N => Finset.sum_congr rfl fun k _ => ?_
      dsimp [b]
      rw [← pow_mul, mul_left_comm, ← pow_succ']
    have hlim_f : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (2 * N), a n * ((z ^ n - (-z) ^ n) / 2))
        atTop (𝓝 (f z)) :=
      hs_comb.tendsto_sum_nat.comp (tendsto_atTop_atTop.mpr fun N => ⟨N, fun m hm => by omega⟩)
    have hlim_f' : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, a (2 * k + 1) * z ^ (2 * k + 1))
        atTop (𝓝 (f z)) :=
      hlim_f.congr fun N => odd_tsum_part_sum a z N
    exact tendsto_nhds_unique hlim_f' hlim_g
  have hg_zero : g 0 = deriv f 0 := by
    have h0 := hg_sum 0 (mem_ball_self hr2_pos)
    have hval : (fun k : ℕ => b k * (0 : ℂ) ^ k) = fun k => if k = 0 then b 0 else 0 := by
      ext k; cases k <;> simp
    rw [hval] at h0
    have hsum0 : HasSum (fun k : ℕ => if k = 0 then b 0 else (0 : ℂ)) (b 0) := by
      have hs := hasSum_single (0 : ℕ) (f := fun k => if k = 0 then b 0 else (0 : ℂ)) (fun k hk => by simp [hk])
      simpa only [ite_true] using hs
    have hgb0 : g 0 = b 0 := h0.unique hsum0
    rw [hgb0]
    dsimp [b, a]
    rw [iteratedDeriv_one]; norm_num
  have hg_deriv0 : deriv g 0 = iteratedDeriv 3 f 0 / 6 := by
    have hfa : HasFPowerSeriesAt g q 0 := hbq.hasFPowerSeriesAt
    have hd := hfa.hasDerivAt
    have hq1 : (q 1) (fun _ => 1) = b 1 := by
      change (FormalMultilinearSeries.ofScalars ℂ b 1) (fun _ => 1) = b 1
      rw [FormalMultilinearSeries.ofScalars_apply_eq]
      simp
    have h1 := hd.deriv
    rw [h1, hq1]
    dsimp [b, a]
    norm_num; ring
  have hg_conj : ∀ w ∈ ball (0 : ℂ) (r ^ 2), g (starRingEnd ℂ w) = starRingEnd ℂ (g w) := by
    let g_conj : ℂ → ℂ := fun w => starRingEnd ℂ (g (starRingEnd ℂ w))
    have hgc_diff : DifferentiableOn ℂ g_conj (ball 0 (r ^ 2)) := by
      intro w hw
      have hw' : starRingEnd ℂ w ∈ ball (0 : ℂ) (r ^ 2) := by
        simpa only [mem_ball_zero_iff, Complex.norm_conj] using hw
      have hdg := (hg_diff.differentiableAt (isOpen_ball.mem_nhds hw')).hasDerivAt
      exact (hasDerivAt_conj_conj hdg).differentiableAt.differentiableWithinAt
    have han_g : AnalyticOnNhd ℂ g (ball 0 (r ^ 2)) := hg_diff.analyticOnNhd isOpen_ball
    have han_gc : AnalyticOnNhd ℂ g_conj (ball 0 (r ^ 2)) := hgc_diff.analyticOnNhd isOpen_ball
    set w₀ : ℝ := r ^ 2 / 2
    have hw₀_pos : 0 < w₀ := by positivity
    have hw₀_mem : (w₀ : ℂ) ∈ ball (0 : ℂ) (r ^ 2) := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw₀_pos]
      dsimp [w₀]; linarith only [hr2_pos]
    have h_eqon : EqOn g g_conj (ball 0 (r ^ 2)) := by
      refine han_g.eqOn_of_preconnected_of_frequently_eq han_gc (convex_ball _ _).isPreconnected hw₀_mem ?_
      rw [frequently_iff]
      intro U hU
      rw [mem_nhdsWithin] at hU
      obtain ⟨V, hV_open, hw₀V, hVU⟩ := hU
      obtain ⟨δ, hδ_pos, hball⟩ := Metric.isOpen_iff.mp hV_open (w₀ : ℂ) hw₀V
      set x : ℝ := w₀ + min (δ / 2) (r ^ 2 / 4)
      have hxw : x ≠ w₀ := by
        have : 0 < min (δ / 2) (r ^ 2 / 4) := lt_min (half_pos hδ_pos) (by positivity)
        linarith only [this]
      have hreal_x : g (x : ℂ) = g_conj (x : ℂ) := by
        have hx0 : 0 < x := by
          have : 0 ≤ min (δ / 2) (r ^ 2 / 4) := le_min (half_pos hδ_pos).le (by positivity)
          linarith only [hw₀_pos, this]
        have hx_lt : x < r ^ 2 := by
          have h1 : min (δ / 2) (r ^ 2 / 4) ≤ r ^ 2 / 4 := min_le_right _ _
          dsimp [x, w₀]; linarith only [hr2_pos, h1]
        set t : ℝ := Real.sqrt x
        have ht_pos : 0 < t := Real.sqrt_pos.mpr hx0
        have ht_lt : t < r := by
          rw [← Real.sqrt_sq hr0.le]; exact Real.sqrt_lt_sqrt hx0.le hx_lt
        have ht_ball : (t : ℂ) ∈ ball (0 : ℂ) r := by
          rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]; exact ht_lt
        have ht2 : (t : ℂ) ^ 2 = (x : ℂ) := by norm_cast; exact Real.sq_sqrt hx0.le
        have hft : f (t : ℂ) = (t : ℂ) * g (x : ℂ) := by rw [← ht2]; exact hg_eq (t : ℂ) ht_ball
        have hf_conj : f (starRingEnd ℂ (t : ℂ)) = starRingEnd ℂ (f (t : ℂ)) :=
          hconj (t : ℂ) (ball_subset_ball hr.le ht_ball)
        have hf_im : (f (t : ℂ)).im = 0 := by
          have := congrArg Complex.im hf_conj
          simp only [Complex.conj_ofReal, Complex.conj_im] at this
          linarith only [this]
        have hgx_im : (g (x : ℂ)).im = 0 := by
          have him := congrArg Complex.im hft
          simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at him
          rw [hf_im] at him
          exact (mul_eq_zero.mp him.symm).resolve_left ht_pos.ne'
        dsimp [g_conj]
        apply Complex.ext <;> simp [hgx_im]
      refine ⟨(x : ℂ), hVU ⟨hball ?_, Complex.ofReal_injective.ne hxw⟩, hreal_x⟩
      rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      dsimp [x]
      rw [add_sub_cancel_left, abs_of_nonneg (le_min (half_pos hδ_pos).le (by positivity))]
      exact (min_le_left _ _).trans_lt (half_lt_self hδ_pos)
    intro w hw
    have hwc : starRingEnd ℂ w ∈ ball (0 : ℂ) (r ^ 2) := by
      simpa only [mem_ball_zero_iff, Complex.norm_conj] using hw
    have h := h_eqon hwc
    dsimp [g_conj] at h
    simpa only [Complex.conj_conj] using h
  have hg_bd : ∀ w ∈ closedBall (0 : ℂ) (r ^ 2 / 4), ‖g w‖ ≤ 4 / 3 * B / r := by
    intro w hw
    have hw_ball : w ∈ ball (0 : ℂ) (r ^ 2) := by
      rw [mem_closedBall_zero_iff] at hw
      rw [mem_ball_zero_iff]; linarith only [hw, hr2_pos]
    have hsum_w := hg_sum w hw_ball
    have hnorm_sum : HasSum (fun k : ℕ => ‖b k * w ^ k‖) (∑' k : ℕ, ‖b k * w ^ k‖) :=
      Summable.hasSum <| Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun k => by
          rw [norm_mul, norm_pow]
          have hw_le : ‖w‖ ≤ r ^ 2 / 4 := mem_closedBall_zero_iff.mp hw
          have hrp : r ^ (2 * k + 1) = r * (r ^ 2) ^ k := by rw [pow_succ', pow_mul]
          calc ‖b k‖ * ‖w‖ ^ k
              ≤ (B / (r * (r ^ 2) ^ k)) * (r ^ 2 / 4) ^ k := by
                have := hb_bd k; rw [hrp] at this
                exact mul_le_mul this (pow_le_pow_left₀ (norm_nonneg _) hw_le k) (by positivity) (by positivity)
            _ = (B / r) * (1 / 4 : ℝ) ^ k := by
              rw [div_pow, one_div, inv_pow]; field_simp [hr0.ne'])
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
    have hnorm_le : ‖g w‖ ≤ ∑' k : ℕ, ‖b k * w ^ k‖ := by
      rw [← hsum_w.tsum_eq]
      exact norm_tsum_le_tsum_norm hnorm_sum.summable
    have htsum_le : ∑' k : ℕ, ‖b k * w ^ k‖ ≤ ∑' k : ℕ, (B / r) * (1 / 4 : ℝ) ^ k := by
      refine Summable.tsum_le_tsum (fun k => ?_) hnorm_sum.summable
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
      rw [norm_mul, norm_pow]
      have hw_le : ‖w‖ ≤ r ^ 2 / 4 := mem_closedBall_zero_iff.mp hw
      have hrp : r ^ (2 * k + 1) = r * (r ^ 2) ^ k := by rw [pow_succ', pow_mul]
      calc ‖b k‖ * ‖w‖ ^ k
          ≤ (B / (r * (r ^ 2) ^ k)) * (r ^ 2 / 4) ^ k := by
            have := hb_bd k; rw [hrp] at this
            exact mul_le_mul this (pow_le_pow_left₀ (norm_nonneg _) hw_le k) (by positivity) (by positivity)
        _ = (B / r) * (1 / 4 : ℝ) ^ k := by
          rw [div_pow, one_div, inv_pow]; field_simp [hr0.ne']
    have hgeom : ∑' k : ℕ, (B / r) * (1 / 4 : ℝ) ^ k = 4 / 3 * B / r := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
    exact hnorm_le.trans (htsum_le.trans_eq hgeom)
  have hdg_bd : ∀ w ∈ closedBall (0 : ℂ) (r ^ 2 / 8), ‖deriv g w‖ ≤ 32 / 3 * B / r ^ 3 := by
    intro w hw
    have hr8 : 0 < r ^ 2 / 8 := by positivity
    have hsub : closedBall w (r ^ 2 / 8) ⊆ ball 0 (r ^ 2) := by
      intro z hz
      rw [mem_ball_zero_iff]
      have h1 : dist z w ≤ r ^ 2 / 8 := mem_closedBall.mp hz
      have h2 : ‖w‖ ≤ r ^ 2 / 8 := mem_closedBall_zero_iff.mp hw
      calc ‖z‖ ≤ ‖z - w‖ + ‖w‖ := norm_le_norm_sub_add z w
        _ ≤ r ^ 2 / 8 + r ^ 2 / 8 := add_le_add (by simpa [dist_eq_norm] using h1) h2
        _ < r ^ 2 := by linarith only [hr2_pos]
    have hcl : DiffContOnCl ℂ g (ball w (r ^ 2 / 8)) :=
      (hg_diff.mono (closure_ball_subset_closedBall.trans hsub)).diffContOnCl
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr8 hcl fun z hz => by
      refine hg_bd z ?_
      rw [mem_closedBall_zero_iff]
      have h1 : ‖z - w‖ = r ^ 2 / 8 := mem_sphere_iff_norm.mp hz
      have h2 : ‖w‖ ≤ r ^ 2 / 8 := mem_closedBall_zero_iff.mp hw
      calc ‖z‖ ≤ ‖z - w‖ + ‖w‖ := norm_le_norm_sub_add z w
        _ = r ^ 2 / 8 + ‖w‖ := by rw [h1]
        _ ≤ r ^ 2 / 8 + r ^ 2 / 8 := add_le_add le_rfl h2
        _ = r ^ 2 / 4 := by ring
    refine hcauchy.trans_eq ?_
    field_simp [hr0.ne']
    ring
  exact ⟨g, hg_diff, hg_conj, hg_eq, hg_zero, hg_deriv0, hg_bd, hdg_bd⟩

/-! ### 2. Generic Lemma FJ (2): scaled inverse chart and expansion -/

/-- Inverse coordinate map `ũ = fjUhat lam mu ψ c ũ := ũ + λ_c Re(ψ_c(μ_c ũ))` (`fj:lemma` (2)). -/
def fjUhat (lam mu : ℝ → ℝ) (ψ : ℝ → ℂ → ℂ) (c ũ : ℝ) : ℝ :=
  ũ + lam c * (ψ c ((mu c * ũ : ℝ) : ℂ)).re

/-- Generic Lemma FJ (2) (`fj:lemma` (2), `fj:inverse`): given `mu, lam : ℝ → ℝ` with `lam * mu = c⁻¹`
and `ψ : ℝ → ℂ → ℂ` real-symmetric holomorphic on `ball 0 ρ₀` (`0 < r₀ < ρ₀`) with uniform
bounds `‖ψ‖, ‖ψ'‖ ≤ M` on `closedBall 0 r₀` and uniform jet `ψ c 0 = β + O(c^{-1})`,
`ψ' c 0 = γ + O(c^{-1/3})`, constructs `phi : ℝ → ℂ → ℂ` such that `(phi, fjUhat lam mu ψ)`
satisfies the chart axioms of `LowerChart` (at constant `-lam c * β` written as `-c0/cStar`
when `lam c * β = c0 / cStar * c^{-(1/3)}`). -/
theorem fj_inverse_chart
    {mu lam : ℝ → ℝ} {ψ : ℝ → ℂ → ℂ} {c1 ρ0 r0 M c_ψ Cμ Clam β γ C_jet : ℝ}
    (hc1_pos : 0 < c1) (hρ0 : 0 < ρ0) (hr0 : 0 < r0) (hr0_ρ : r0 < ρ0) (hM : 0 ≤ M)
    (hCμ : 0 < Cμ) (hClam : 0 < Clam) (hC_jet : 0 ≤ C_jet)
    (hmu_pos : ∀ c : ℝ, 0 < c → 0 < mu c)
    (hlam_pos : ∀ c : ℝ, 0 < c → 0 < lam c)
    (hmu_lam : ∀ c : ℝ, 0 < c → lam c * mu c = c⁻¹)
    (hmu_ub : ∀ c : ℝ, 1 ≤ c → mu c ≤ Cμ * c ^ (-(2 / 3 : ℝ)))
    (hlam_ub : ∀ c : ℝ, 1 ≤ c → lam c ≤ Clam * c ^ (-(1 / 3 : ℝ)))
    (hc1_r0 : 4 * c1 ^ 2 * Cμ ≤ r0 / 4)
    (hψ_diff : ∀ c : ℝ, c_ψ ≤ c → DifferentiableOn ℂ (ψ c) (ball 0 ρ0))
    (hψ_conj : ∀ c : ℝ, c_ψ ≤ c → ∀ z ∈ ball (0 : ℂ) ρ0, ψ c (starRingEnd ℂ z) = starRingEnd ℂ (ψ c z))
    (hψ_bd : ∀ c : ℝ, c_ψ ≤ c → ∀ z ∈ closedBall (0 : ℂ) r0, ‖ψ c z‖ ≤ M ∧ ‖deriv (ψ c) z‖ ≤ M)
    (hψ_val : ∀ c : ℝ, c_ψ ≤ c → |(ψ c 0).re - β| ≤ C_jet * c ^ (-1 : ℝ))
    (hψ_der : ∀ c : ℝ, c_ψ ≤ c → |(deriv (ψ c) 0).re - γ| ≤ C_jet * c ^ (-(1 / 3 : ℝ)))
    {c0_const : ℝ}
    (hβ_eq : ∀ c : ℝ, 1 ≤ c → lam c * β = c0_const / cStar * c ^ (-(1 / 3 : ℝ))) :
    ∃ phi : ℝ → ℂ → ℂ,
      LowerChart c0_const γ c1 phi (fjUhat lam mu ψ) := by
  classical
  let C_inv := max (max (Clam * M) (2 * M))
    (4 * Clam * M / r0 * (Cμ * (|Special.airyZero 1| + Clam * M)) ^ 2 +
      Clam * C_jet + Clam * C_jet * (Cμ * (|Special.airyZero 1| + Clam * M)) + |γ| * Clam * M)
  have hev : ∀ᶠ c : ℝ in atTop,
      1 ≤ c ∧
      c_ψ ≤ c ∧
      c⁻¹ * M ≤ 1 / 2 ∧
      c⁻¹ * M ≤ r0 / 2 ∧
      Clam * M * c ^ (-(1 / 3 : ℝ)) ≤ 1 ∧
      mu c * |Special.airyZero 1| ≤ r0 / 4 ∧
      mu c * (|Special.airyZero 1| + Clam * M * c ^ (-(1 / 3 : ℝ))) ≤ r0 / 2 := by
    have hcm1 : Tendsto (fun c : ℝ => c⁻¹ * M) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.mul_const M
    have hcm13 : Tendsto (fun c : ℝ => (Clam * M) * c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul _
    have hc23 : Tendsto (fun c : ℝ => Cμ * |Special.airyZero 1| * c ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul _
    have hc23' : Tendsto (fun c : ℝ => Cμ * (|Special.airyZero 1| + 1) * c ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul _
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop c_ψ,
      hcm1.eventually (Iic_mem_nhds (by positivity : 0 < (1 / 2 : ℝ))),
      hcm1.eventually (Iic_mem_nhds (by positivity : 0 < r0 / 2)),
      hcm13.eventually (Iic_mem_nhds zero_lt_one),
      hc23.eventually (Iic_mem_nhds (by positivity : 0 < r0 / 4)),
      hc23'.eventually (Iic_mem_nhds (by positivity : 0 < r0 / 2))] with
        c h1 h2 h3 h4 h5 h6 h7
    refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
    · calc mu c * |Special.airyZero 1| ≤ Cμ * c ^ (-(2 / 3 : ℝ)) * |Special.airyZero 1| :=
            mul_le_mul_of_nonneg_right (hmu_ub c h1) (abs_nonneg _)
        _ = Cμ * |Special.airyZero 1| * c ^ (-(2 / 3 : ℝ)) := by ring
        _ ≤ r0 / 4 := h6
    · calc mu c * (|Special.airyZero 1| + Clam * M * c ^ (-(1 / 3 : ℝ)))
          ≤ Cμ * c ^ (-(2 / 3 : ℝ)) * (|Special.airyZero 1| + 1) :=
            mul_le_mul (hmu_ub c h1) (by linarith only [h5]) (by positivity) (by positivity)
        _ = Cμ * (|Special.airyZero 1| + 1) * c ^ (-(2 / 3 : ℝ)) := by ring
        _ ≤ r0 / 2 := h7
  obtain ⟨cc, hcc⟩ := eventually_atTop.1 hev
  let phi : ℝ → ℂ → ℂ := fun c u =>
    if h : 1 ≤ c ∧ c_ψ ≤ c ∧ c⁻¹ * M ≤ 1 / 2 ∧ c⁻¹ * M ≤ r0 / 2 then
      (Classical.choose (ct_inv_chart (hψ_diff c h.2.1) hr0_ρ hr0 (hψ_bd c h.2.1)
        (inv_nonneg.mpr (by linarith only [h.1])) h.2.2.1 h.2.2.2)) ((mu c : ℂ) * u) / (mu c : ℂ)
    else u
  refine ⟨phi, cc, C_inv, le_trans (by positivity) (le_max_left _ _), fun c hc => ?_⟩
  obtain ⟨hc1, hccψ, hcM12, hcMr0, hlamM1, hmu_a1, hmu_a1'⟩ := hcc c hc
  have hc_pos : 0 < c := by linarith only [hc1]
  have hμ_pos : 0 < mu c := hmu_pos c hc_pos
  have hlam_pos_c : 0 < lam c := hlam_pos c hc_pos
  have hμC : (mu c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ_pos.ne'
  let invEx := ct_inv_chart (hψ_diff c hccψ) hr0_ρ hr0 (hψ_bd c hccψ)
    (inv_nonneg.mpr hc_pos.le) hcM12 hcMr0
  let G : ℂ → ℂ := Classical.choose invEx
  have hG_spec : ∀ b ∈ ball (0 : ℂ) (r0 / 2), G b ∈ closedBall (0 : ℂ) r0 ∧ G b + (c⁻¹ : ℂ) * ψ c (G b) = b :=
    fun b hb => by simpa only [Complex.ofReal_inv] using (Classical.choose_spec invEx).1 b hb
  have hG_uniq : ∀ b ∈ ball (0 : ℂ) (r0 / 2), ∀ a ∈ closedBall (0 : ℂ) r0, a + (c⁻¹ : ℂ) * ψ c a = b → a = G b :=
    fun b hb a ha hrel => by
      refine (Classical.choose_spec invEx).2.1 b hb a ha ?_
      simpa only [Complex.ofReal_inv] using hrel
  have hG_deriv : ∀ b ∈ ball (0 : ℂ) (r0 / 2), HasDerivAt G (1 / (1 + (c⁻¹ : ℂ) * deriv (ψ c) (G b))) b :=
    fun b hb => by
      have hd : HasDerivAt G (1 / (1 + ((c⁻¹ : ℝ) : ℂ) * deriv (ψ c) (G b))) b :=
        (Classical.choose_spec invEx).2.2 b hb
      simpa only [Complex.ofReal_inv] using hd
  have hphi_eq : ∀ u : ℂ, phi c u = G ((mu c : ℂ) * u) / (mu c : ℂ) := fun u => by
    dsimp [phi]
    rw [dite_eq_left_of_eq_true (eq_true ⟨hc1, hccψ, hcM12, hcMr0⟩)]
  have hμ_Rmax : mu c * lowerRmax c1 c ≤ r0 / 4 := by
    unfold lowerRmax
    have hc23_pow : c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hc_pos, neg_add_cancel, Real.rpow_zero]
    calc mu c * (4 * c1 ^ 2 * c ^ (2 / 3 : ℝ))
        ≤ (Cμ * c ^ (-(2 / 3 : ℝ))) * (4 * c1 ^ 2 * c ^ (2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (hmu_ub c hc1) (by positivity)
      _ = (4 * c1 ^ 2 * Cμ) * (c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) := by ring
      _ = 4 * c1 ^ 2 * Cμ := by rw [hc23_pow, mul_one]
      _ ≤ r0 / 4 := hc1_r0
  let ρc : ℝ := r0 / (2 * mu c)
  have hRmax_lt : lowerRmax c1 c < ρc := by
    dsimp [ρc]
    rw [lt_div_iff₀ (by positivity)]
    linarith only [hμ_Rmax, hr0]
  have h_ball_mem : ∀ u ∈ ball (0 : ℂ) ρc, (mu c : ℂ) * u ∈ ball (0 : ℂ) (r0 / 2) := by
    intro u hu
    rw [mem_ball_zero_iff] at hu ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ_pos.le]
    rw [show ρc = r0 / (2 * mu c) from rfl, lt_div_iff₀ (by positivity)] at hu
    linarith only [hu]
  have hphi_hasDeriv : ∀ u ∈ ball (0 : ℂ) ρc,
      HasDerivAt (phi c) (1 / (1 + (c⁻¹ : ℂ) * deriv (ψ c) (G ((mu c : ℂ) * u)))) u := by
    intro u hu
    have hd1 : HasDerivAt (fun w => G ((mu c : ℂ) * w) / (mu c : ℂ))
        (1 / (1 + (c⁻¹ : ℂ) * deriv (ψ c) (G ((mu c : ℂ) * u)))) u := by
      have h1 := hG_deriv _ (h_ball_mem u hu)
      have h2 : HasDerivAt (fun w : ℂ => (mu c : ℂ) * w) (mu c : ℂ) u := by
        simpa using (hasDerivAt_id u).const_mul (mu c : ℂ)
      have h3 := (h1.comp u h2).div_const (mu c : ℂ)
      have heq : 1 / (1 + (c⁻¹ : ℂ) * deriv (ψ c) (G ((mu c : ℂ) * u))) * (mu c : ℂ) / (mu c : ℂ) =
          1 / (1 + (c⁻¹ : ℂ) * deriv (ψ c) (G ((mu c : ℂ) * u))) := by
        field_simp [hμC]
      simpa only [Function.comp_def, heq] using h3
    refine hd1.congr_of_eventuallyEq (Eventually.of_forall fun w => hphi_eq w)
  have hphi_diff : DifferentiableOn ℂ (phi c) (ball 0 ρc) :=
    fun u hu => (hphi_hasDeriv u hu).differentiableAt.differentiableWithinAt
  -- Conj symmetry on `ball 0 ρc`
  have hphi_conj : ∀ u ∈ ball (0 : ℂ) ρc, phi c (starRingEnd ℂ u) = starRingEnd ℂ (phi c u) := by
    intro u hu
    have hbu : (mu c : ℂ) * u ∈ ball (0 : ℂ) (r0 / 2) := h_ball_mem u hu
    have hbu_conj : (mu c : ℂ) * starRingEnd ℂ u ∈ ball (0 : ℂ) (r0 / 2) := by
      simpa only [mem_ball_zero_iff, norm_mul, Complex.norm_conj] using hbu
    obtain ⟨hG_mem, hG_rel⟩ := hG_spec _ hbu
    have hG_mem_ρ : G ((mu c : ℂ) * u) ∈ ball (0 : ℂ) ρ0 :=
      closedBall_subset_ball hr0_ρ hG_mem
    have h_conj_mem : starRingEnd ℂ (G ((mu c : ℂ) * u)) ∈ closedBall (0 : ℂ) r0 := by
      simpa only [mem_closedBall_zero_iff, Complex.norm_conj] using hG_mem
    have h_eq : starRingEnd ℂ (G ((mu c : ℂ) * u)) +
        (c⁻¹ : ℂ) * ψ c (starRingEnd ℂ (G ((mu c : ℂ) * u))) =
        (mu c : ℂ) * starRingEnd ℂ u := by
      rw [hψ_conj c hccψ _ hG_mem_ρ]
      have hcinv : starRingEnd ℂ (c⁻¹ : ℂ) = (c⁻¹ : ℂ) := by push_cast; simp
      calc starRingEnd ℂ (G ((mu c : ℂ) * u)) + (c⁻¹ : ℂ) * starRingEnd ℂ (ψ c (G ((mu c : ℂ) * u)))
          = starRingEnd ℂ (G ((mu c : ℂ) * u) + (c⁻¹ : ℂ) * ψ c (G ((mu c : ℂ) * u))) := by
            simp only [map_add, map_mul, hcinv]
        _ = starRingEnd ℂ ((mu c : ℂ) * u) := by rw [hG_rel]
        _ = (mu c : ℂ) * starRingEnd ℂ u := by simp only [map_mul, Complex.conj_ofReal]
    have hG_conj_eq : starRingEnd ℂ (G ((mu c : ℂ) * u)) = G ((mu c : ℂ) * starRingEnd ℂ u) :=
      hG_uniq _ hbu_conj _ h_conj_mem h_eq
    rw [hphi_eq, hphi_eq, ← hG_conj_eq, map_div₀, Complex.conj_ofReal]
  have hphi_im : ∀ x : ℝ, |x| ≤ lowerRmax c1 c → (phi c (x : ℂ)).im = 0 := by
    intro x hx
    have hx_ball : (x : ℂ) ∈ ball (0 : ℂ) ρc := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx.trans_lt hRmax_lt
    have h := hphi_conj (x : ℂ) hx_ball
    simp only [Complex.conj_ofReal] at h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith only [this]
  -- Bounds on `‖u‖ ≤ Rmax`
  have h_inv_rel : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      phi c u ∈ closedBall (0 : ℂ) (r0 / mu c) ∧
      (mu c : ℂ) * phi c u ∈ closedBall (0 : ℂ) r0 ∧
      phi c u + (lam c : ℂ) * ψ c ((mu c : ℂ) * phi c u) = u := by
    intro u hu
    have hu_ball : u ∈ ball (0 : ℂ) ρc := (mem_ball_zero_iff).mpr (hu.trans_lt hRmax_lt)
    obtain ⟨hG_mem, hG_rel⟩ := hG_spec _ (h_ball_mem u hu_ball)
    have hmu_phi : (mu c : ℂ) * phi c u = G ((mu c : ℂ) * u) := by
      rw [hphi_eq]; field_simp [hμC]
    have hphi_mem : phi c u ∈ closedBall (0 : ℂ) (r0 / mu c) := by
      rw [mem_closedBall_zero_iff, hphi_eq, norm_div, Complex.norm_real, Real.norm_of_nonneg hμ_pos.le]
      exact div_le_div_of_nonneg_right (mem_closedBall_zero_iff.mp hG_mem) hμ_pos.le
    refine ⟨hphi_mem, hmu_phi ▸ hG_mem, ?_⟩
    rw [hmu_phi]
    have hl : (lam c : ℂ) * (mu c : ℂ) = (c⁻¹ : ℂ) := by
      exact_mod_cast hmu_lam c hc_pos
    calc phi c u + (lam c : ℂ) * ψ c (G ((mu c : ℂ) * u))
        = (G ((mu c : ℂ) * u) + (lam c : ℂ) * (mu c : ℂ) * ψ c (G ((mu c : ℂ) * u))) / (mu c : ℂ) := by
          rw [hphi_eq]; field_simp [hμC]
      _ = (G ((mu c : ℂ) * u) + (c⁻¹ : ℂ) * ψ c (G ((mu c : ℂ) * u))) / (mu c : ℂ) := by rw [hl]
      _ = ((mu c : ℂ) * u) / (mu c : ℂ) := by rw [hG_rel]
      _ = u := by field_simp [hμC]
  have h_bds : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      ‖phi c u - u‖ ≤ C_inv * c ^ (-(1 / 3 : ℝ)) ∧
      ‖deriv (phi c) u - 1‖ ≤ C_inv * c ^ (-1 : ℝ) := by
    intro u hu
    obtain ⟨_, hmu_mem, hrel⟩ := h_inv_rel u hu
    have hψ_bds := hψ_bd c hccψ _ hmu_mem
    have h_diff_eq : phi c u - u = -((lam c : ℂ) * ψ c ((mu c : ℂ) * phi c u)) :=
      eq_neg_of_add_eq_zero_left (by linear_combination hrel)
    have h1 : ‖phi c u - u‖ ≤ C_inv * c ^ (-(1 / 3 : ℝ)) := by
      rw [h_diff_eq, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam_pos_c.le]
      have hlam_M : lam c * M ≤ C_inv * c ^ (-(1 / 3 : ℝ)) := by
        have hCM : Clam * M ≤ C_inv := le_trans (le_max_left _ _) (le_max_left _ _)
        have hpow_nn : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hc_pos.le _
        calc lam c * M ≤ (Clam * c ^ (-(1 / 3 : ℝ))) * M := mul_le_mul_of_nonneg_right (hlam_ub c hc1) hM
          _ = (Clam * M) * c ^ (-(1 / 3 : ℝ)) := by ring
          _ ≤ C_inv * c ^ (-(1 / 3 : ℝ)) := mul_le_mul_of_nonneg_right hCM hpow_nn
      exact (mul_le_mul_of_nonneg_left hψ_bds.1 hlam_pos_c.le).trans hlam_M
    have h2 : ‖deriv (phi c) u - 1‖ ≤ C_inv * c ^ (-1 : ℝ) := by
      have hu_ball : u ∈ ball (0 : ℂ) ρc := (mem_ball_zero_iff).mpr (hu.trans_lt hRmax_lt)
      have hd_eq : deriv (phi c) u = 1 / (1 + (c⁻¹ : ℂ) * deriv (ψ c) (G ((mu c : ℂ) * u))) :=
        (hphi_hasDeriv u hu_ball).deriv
      have hμ_eq : G ((mu c : ℂ) * u) = (mu c : ℂ) * phi c u := by
        rw [hphi_eq]; field_simp [hμC]
      rw [hμ_eq] at hd_eq
      set d := (c⁻¹ : ℂ) * deriv (ψ c) ((mu c : ℂ) * phi c u)
      have hd_norm : ‖d‖ ≤ c⁻¹ * M := by
        dsimp [d]
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc_pos.le]
        exact mul_le_mul_of_nonneg_left hψ_bds.2 (inv_nonneg.mpr hc_pos.le)
      have h1d_lb : 1 / 2 ≤ ‖(1 : ℂ) + d‖ := by
        have := norm_sub_norm_le (1 : ℂ) (-d)
        rw [sub_neg_eq_add, norm_one, norm_neg] at this
        linarith only [this, hd_norm, hcM12]
      have hne : (1 : ℂ) + d ≠ 0 := norm_pos_iff.mp (by linarith only [h1d_lb])
      have hdiv : 1 / (1 + d) - 1 = -d / (1 + d) := by field_simp [hne]; ring
      rw [hd_eq, hdiv, norm_div, norm_neg]
      calc ‖d‖ / ‖1 + d‖ ≤ (c⁻¹ * M) / (1 / 2) := div_le_div₀ (by positivity) hd_norm (by norm_num) h1d_lb
        _ = (2 * M) * c ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; ring
        _ ≤ C_inv * c ^ (-1 : ℝ) := by
            have : 2 * M ≤ C_inv := le_trans (le_max_right _ _) (le_max_left _ _)
            exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hc_pos.le _)
    exact ⟨h1, h2⟩
  -- Real inversion `uhat c (phi c x).re = x`
  have h_inv_real : ∀ x : ℝ, |x| ≤ lowerRmax c1 c → fjUhat lam mu ψ c (phi c (x : ℂ)).re = x := by
    intro x hx
    obtain ⟨_, _, hrel⟩ := h_inv_rel (x : ℂ) (by simpa [Complex.norm_real, Real.norm_eq_abs] using hx)
    have hpx : phi c (x : ℂ) = (((phi c (x : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext rfl (by rw [hphi_im x hx, Complex.ofReal_im])
    have hre := congrArg Complex.re hrel
    rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
    dsimp [fjUhat]
    have harg : (((mu c * (phi c (x : ℂ)).re : ℝ) : ℂ)) = (mu c : ℂ) * phi c (x : ℂ) := by
      conv_rhs => rw [hpx]
      push_cast; ring
    rw [harg]
    simpa using hre
  -- Expansion at `a₁`: `cts:phic-exp`
  have h_a1_exp : |(phi c (Special.airyZero 1 : ℂ)).re -
      (Special.airyZero 1 - c0_const / cStar * c ^ (-(1 / 3 : ℝ)) - γ * Special.airyZero 1 * c ^ (-1 : ℝ))| ≤
      C_inv * c ^ (-(4 / 3 : ℝ)) := by
    have ha1_abs_r0 : |Special.airyZero 1| ≤ r0 * c ^ (2 / 3 : ℝ) / (4 * mu c * c ^ (2 / 3 : ℝ)) + 0 ∨
        |(Special.airyZero 1 : ℂ).re| ≤ ‖(Special.airyZero 1 : ℂ)‖ := Or.inr (Complex.abs_re_le_norm _)
    -- Note: we only need `|a_1| ≤ lowerRmax c1 c` OR directly work inside `ball 0 ρc`!
    have ha1_ball : (Special.airyZero 1 : ℂ) ∈ ball (0 : ℂ) ρc := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      dsimp [ρc]
      rw [lt_div_iff₀ (by positivity)]
      linarith only [hmu_a1, hr0]
    obtain ⟨hGa1_mem, hGa1_rel⟩ := hG_spec _ (h_ball_mem _ ha1_ball)
    have hmu_pa1 : (mu c : ℂ) * phi c (Special.airyZero 1 : ℂ) = G ((mu c : ℂ) * (Special.airyZero 1 : ℂ)) := by
      rw [hphi_eq]; field_simp [hμC]
    have hrel_a1 : phi c (Special.airyZero 1 : ℂ) + (lam c : ℂ) * ψ c ((mu c : ℂ) * phi c (Special.airyZero 1 : ℂ)) =
        (Special.airyZero 1 : ℂ) := by
      have hl : (lam c : ℂ) * (mu c : ℂ) = (c⁻¹ : ℂ) := by exact_mod_cast hmu_lam c hc_pos
      calc phi c (Special.airyZero 1 : ℂ) + (lam c : ℂ) * ψ c ((mu c : ℂ) * phi c (Special.airyZero 1 : ℂ))
          = (G ((mu c : ℂ) * (Special.airyZero 1 : ℂ)) + (lam c : ℂ) * (mu c : ℂ) * ψ c (G ((mu c : ℂ) * (Special.airyZero 1 : ℂ)))) /
              (mu c : ℂ) := by
            rw [hmu_pa1, hphi_eq]; field_simp [hμC]
        _ = (G ((mu c : ℂ) * (Special.airyZero 1 : ℂ)) + (c⁻¹ : ℂ) * ψ c (G ((mu c : ℂ) * (Special.airyZero 1 : ℂ)))) /
              (mu c : ℂ) := by rw [hl]
        _ = ((mu c : ℂ) * (Special.airyZero 1 : ℂ)) / (mu c : ℂ) := by rw [hGa1_rel]
        _ = (Special.airyZero 1 : ℂ) := by field_simp [hμC]
    have hφa1_im : (phi c (Special.airyZero 1 : ℂ)).im = 0 := by
      have hconj_a1 := hphi_conj (Special.airyZero 1 : ℂ) ha1_ball
      simp only [Complex.conj_ofReal] at hconj_a1
      have := congrArg Complex.im hconj_a1
      simp only [Complex.conj_im] at this
      linarith only [this]
    have hφa1_sub : ‖phi c (Special.airyZero 1 : ℂ) - (Special.airyZero 1 : ℂ)‖ ≤ Clam * M * c ^ (-(1 / 3 : ℝ)) := by
      have hdeq : phi c (Special.airyZero 1 : ℂ) - (Special.airyZero 1 : ℂ) =
          -((lam c : ℂ) * ψ c ((mu c : ℂ) * phi c (Special.airyZero 1 : ℂ))) :=
        eq_neg_of_add_eq_zero_left (by linear_combination hrel_a1)
      have hbd := (hψ_bd c hccψ _ (hmu_pa1 ▸ hGa1_mem)).1
      rw [hdeq, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam_pos_c.le]
      calc lam c * ‖ψ c ((mu c : ℂ) * phi c (Special.airyZero 1 : ℂ))‖
          ≤ (Clam * c ^ (-(1 / 3 : ℝ))) * M := mul_le_mul (hlam_ub c hc1) hbd (norm_nonneg _) (by positivity)
        _ = Clam * M * c ^ (-(1 / 3 : ℝ)) := by ring
    set φa : ℝ := (phi c (Special.airyZero 1 : ℂ)).re
    have hφa_c : phi c (Special.airyZero 1 : ℂ) = (φa : ℂ) := Complex.ext rfl hφa1_im
    have hφa_sub_r : |φa - Special.airyZero 1| ≤ Clam * M * c ^ (-(1 / 3 : ℝ)) := by
      simpa [hφa_c, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hφa1_sub
    set w : ℝ := mu c * φa
    have hw_abs : |w| ≤ r0 / 2 := by
      dsimp [w]
      rw [abs_mul, abs_of_pos hμ_pos]
      have hφa_ub : |φa| ≤ |Special.airyZero 1| + Clam * M * c ^ (-(1 / 3 : ℝ)) := by
        calc |φa| = |(φa - Special.airyZero 1) + Special.airyZero 1| := by ring_nf
          _ ≤ |φa - Special.airyZero 1| + |Special.airyZero 1| := abs_add_le _ _
          _ ≤ Clam * M * c ^ (-(1 / 3 : ℝ)) + |Special.airyZero 1| := add_le_add hφa_sub_r le_rfl
          _ = _ := add_comm _ _
      exact (mul_le_mul_of_nonneg_left hφa_ub hμ_pos.le).trans hmu_a1'
    have hw_bound : |w| ≤ (Clam * M * 0 + Cμ * (|Special.airyZero 1| + Clam * M)) * c ^ (-(2 / 3 : ℝ)) := by
      have hc13_le1 : c ^ (-(1 / 3 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
      have hφa_ub : |φa| ≤ |Special.airyZero 1| + Clam * M := by
        calc |φa| = |(φa - Special.airyZero 1) + Special.airyZero 1| := by ring_nf
          _ ≤ |φa - Special.airyZero 1| + |Special.airyZero 1| := abs_add_le _ _
          _ ≤ Clam * M * 1 + |Special.airyZero 1| := by
            gcongr
            exact hφa_sub_r.trans (mul_le_mul_of_nonneg_left hc13_le1 (by positivity))
          _ = |Special.airyZero 1| + Clam * M := by ring
      dsimp [w]
      rw [abs_mul, abs_of_pos hμ_pos]
      calc mu c * |φa| ≤ (Cμ * c ^ (-(2 / 3 : ℝ))) * (|Special.airyZero 1| + Clam * M) :=
            mul_le_mul (hmu_ub c hc1) hφa_ub (abs_nonneg _) (by positivity)
        _ = (Clam * M * 0 + Cμ * (|Special.airyZero 1| + Clam * M)) * c ^ (-(2 / 3 : ℝ)) := by ring
    -- Real-valued Taylor remainder for `ψ` on `[-r0/2, r0/2]` via `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2`
    have hψ_t2 : |((ψ c (w : ℂ)).re - ((ψ c 0).re + (deriv (ψ c) 0).re * w))| ≤ (4 * M / r0) * w ^ 2 := by
      set g_rem : ℂ → ℂ := fun z => ψ c z - (ψ c 0 + deriv (ψ c) 0 * z)
      have hg_diff : DifferentiableOn ℂ g_rem (ball 0 r0) :=
        ((hψ_diff c hccψ).mono (ball_subset_ball hr0_ρ.le)).sub
          (differentiableOn_const _ |>.add (differentiableOn_const _ |>.mul differentiableOn_id))
      have hg0 : g_rem 0 = 0 := by simp [g_rem]
      have hdg0 : deriv g_rem 0 = 0 := by
        have hd : HasDerivAt g_rem (deriv (ψ c) 0 - (0 + deriv (ψ c) 0 * 1)) 0 :=
          ((hψ_diff c hccψ 0 (mem_ball_self hρ0)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hρ0))).hasDerivAt.sub
            ((hasDerivAt_const 0 (ψ c 0)).add ((hasDerivAt_id 0).const_mul (deriv (ψ c) 0)))
        simpa using hd.deriv
      have hdg_bd : ∀ z ∈ closedBall (0 : ℂ) (r0 / 2), ‖deriv (deriv g_rem) z‖ ≤ 4 * M / r0 := by
        intro z hz
        have hr4 : 0 < r0 / 2 := half_pos hr0
        have hsub : closedBall z (r0 / 2) ⊆ closedBall (0 : ℂ) r0 := by
          intro v hv
          rw [mem_closedBall_zero_iff]
          have h1 : ‖v - z‖ ≤ r0 / 2 := by simpa [dist_eq_norm] using mem_closedBall.mp hv
          have h2 : ‖z‖ ≤ r0 / 2 := mem_closedBall_zero_iff.mp hz
          calc ‖v‖ ≤ ‖v - z‖ + ‖z‖ := norm_le_norm_sub_add v z
            _ ≤ r0 / 2 + r0 / 2 := add_le_add h1 h2
            _ = r0 := by ring
        have hdψ' : DifferentiableOn ℂ (deriv (ψ c)) (ball 0 ρ0) :=
          (hψ_diff c hccψ).deriv isOpen_ball
        have h_cl : DiffContOnCl ℂ (deriv (ψ c)) (ball z (r0 / 2)) :=
          (hdψ'.mono (fun v hv => closedBall_subset_ball hr0_ρ (hsub (closure_ball_subset_closedBall hv)))).diffContOnCl
        have h_cauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr4 h_cl
          fun v hv => (hψ_bd c hccψ v (hsub (sphere_subset_closedBall hv))).2
        have hd_eq : ∀ᶠ u in 𝓝 z, deriv g_rem u = deriv (ψ c) u - deriv (ψ c) 0 := by
          filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr
            ((mem_closedBall_zero_iff.mp hz).trans_lt (half_lt_self hr0)))] with u hu
          have hdu := ((hψ_diff c hccψ).differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball hr0_ρ.le hu))).hasDerivAt
          have hd' : HasDerivAt g_rem (deriv (ψ c) u - (0 + deriv (ψ c) 0 * 1)) u :=
            hdu.sub ((hasDerivAt_const u (ψ c 0)).add ((hasDerivAt_id u).const_mul (deriv (ψ c) 0)))
          simpa using hd'.deriv
        have hdd_eq : deriv (deriv g_rem) z = deriv (deriv (ψ c)) z := by
          have : deriv (deriv g_rem) z = deriv (fun u => deriv (ψ c) u - deriv (ψ c) 0) z :=
            Filter.EventuallyEq.deriv_eq hd_eq
          rw [this]
          exact (((hdψ'.differentiableAt (isOpen_ball.mem_nhds (closedBall_subset_ball hr0_ρ (hsub (mem_closedBall_self hr4.le))))).hasDerivAt).sub_const _).deriv
        rw [hdd_eq]
        refine h_cauchy.trans ?_
        rw [div_div_eq_mul_div, mul_comm M 2]
        gcongr
        norm_num
      have hg'_bound : ∀ z ∈ closedBall (0 : ℂ) (r0 / 2), ‖deriv g_rem z‖ ≤ (4 * M / r0) * ‖z‖ := by
        intro z hz
        have hder : ∀ x ∈ closedBall (0 : ℂ) (r0 / 2),
            HasDerivWithinAt (deriv g_rem) (deriv (deriv g_rem) x) (closedBall (0 : ℂ) (r0 / 2)) x := by
          intro x hx
          have hx_ball : x ∈ ball (0 : ℂ) r0 := by
            rw [mem_ball_zero_iff]; have h2 := mem_closedBall_zero_iff.mp hx; linarith only [h2, hr0]
          exact ((hg_diff.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hx_ball)).hasDerivAt.hasDerivWithinAt
        have hmv := (convex_closedBall (0 : ℂ) (r0 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
          hder hdg_bd hz (mem_closedBall_self (half_pos hr0).le)
        simpa [hdg0] using hmv
      have hg_bound : ∀ z ∈ closedBall (0 : ℂ) (r0 / 2), ‖g_rem z‖ ≤ (4 * M / r0 * ‖z‖) * ‖z‖ := by
        intro z hz
        set Rz : ℝ := ‖z‖
        have hRz : Rz ≤ r0 / 2 := mem_closedBall_zero_iff.mp hz
        have hder : ∀ x ∈ closedBall (0 : ℂ) Rz,
            HasDerivWithinAt g_rem (deriv g_rem x) (closedBall (0 : ℂ) Rz) x := by
          intro x hx
          have hx_ball : x ∈ ball (0 : ℂ) r0 := by
            rw [mem_ball_zero_iff]; have h2 := mem_closedBall_zero_iff.mp hx; linarith only [h2, hRz, hr0]
          exact (hg_diff.differentiableAt (isOpen_ball.mem_nhds hx_ball)).hasDerivAt.hasDerivWithinAt
        have hmv := (convex_closedBall (0 : ℂ) Rz).norm_image_sub_le_of_norm_hasDerivWithin_le
          (C := 4 * M / r0 * Rz) hder
          (fun x hx => (hg'_bound x (closedBall_subset_closedBall hRz hx)).trans
            (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) (by positivity)))
          (mem_closedBall_zero_iff.mpr le_rfl) (mem_closedBall_self (norm_nonneg _))
        simpa [hg0] using hmv
      have hres := hg_bound (w : ℂ) (by rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hw_abs)
      rw [Complex.norm_real, Real.norm_eq_abs] at hres
      have hre_g : (g_rem (w : ℂ)).re = (ψ c (w : ℂ)).re - ((ψ c 0).re + (deriv (ψ c) 0).re * w) := by
        dsimp [g_rem]
        simp
      have habs : |(g_rem (w : ℂ)).re| ≤ ‖g_rem (w : ℂ)‖ := Complex.abs_re_le_norm _
      rw [hre_g] at habs
      calc |((ψ c (w : ℂ)).re - ((ψ c 0).re + (deriv (ψ c) 0).re * w))|
          ≤ ‖g_rem (w : ℂ)‖ := habs
        _ ≤ (4 * M / r0 * |w|) * |w| := hres
        _ = (4 * M / r0) * w ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
    have hre_a1 : φa - Special.airyZero 1 = -(lam c * (ψ c (w : ℂ)).re) := by
      have hre := congrArg Complex.re hrel_a1
      rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
      have harg : (w : ℂ) = (mu c : ℂ) * phi c (Special.airyZero 1 : ℂ) := by
        dsimp [w]; rw [hφa_c]; push_cast; ring
      rw [← harg] at hre
      change φa + lam c * (ψ c (w : ℂ)).re = Special.airyZero 1 at hre
      linarith only [hre]
    have h_main : lam c * (ψ c (w : ℂ)).re = Special.airyZero 1 - φa := by linarith only [hre_a1]
    have hβc : lam c * β = c0_const / cStar * c ^ (-(1 / 3 : ℝ)) := hβ_eq c hc1
    have hlam_mu_c : lam c * mu c = c ^ (-1 : ℝ) := by
      rw [hmu_lam c hc_pos, Real.rpow_neg_one]
    have hw_id : lam c * γ * w = γ * c ^ (-1 : ℝ) * φa := by
      change lam c * γ * (mu c * φa) = γ * c ^ (-1 : ℝ) * φa
      rw [← hlam_mu_c]; ring
    have hsplit : φa - (Special.airyZero 1 - c0_const / cStar * c ^ (-(1 / 3 : ℝ)) - γ * Special.airyZero 1 * c ^ (-1 : ℝ)) =
        -(lam c * ((ψ c (w : ℂ)).re - ((ψ c 0).re + (deriv (ψ c) 0).re * w)) +
          lam c * ((ψ c 0).re - β) +
          lam c * ((deriv (ψ c) 0).re - γ) * w +
          γ * (lam c * mu c) * (φa - Special.airyZero 1)) := by
      calc φa - (Special.airyZero 1 - c0_const / cStar * c ^ (-(1 / 3 : ℝ)) - γ * Special.airyZero 1 * c ^ (-1 : ℝ))
          = -(Special.airyZero 1 - φa) + lam c * β + γ * c ^ (-1 : ℝ) * φa - γ * c ^ (-1 : ℝ) * (φa - Special.airyZero 1) := by
            rw [hβc]; ring
        _ = -(lam c * (ψ c (w : ℂ)).re) + lam c * β + lam c * γ * w - γ * (lam c * mu c) * (φa - Special.airyZero 1) := by
            rw [← h_main, ← hw_id, hlam_mu_c]
        _ = _ := by ring
    rw [hsplit, abs_neg]
    set Kw : ℝ := Cμ * (|Special.airyZero 1| + Clam * M)
    have hKw_nn : 0 ≤ Kw := by positivity
    have hw_bd' : |w| ≤ Kw * c ^ (-(2 / 3 : ℝ)) := by simpa [Kw] using hw_bound
    have hlam_le : lam c ≤ Clam * c ^ (-(1 / 3 : ℝ)) := hlam_ub c hc1
    have hc43_nn : 0 ≤ c ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hc_pos.le _
    have ht1 : |lam c * ((ψ c (w : ℂ)).re - ((ψ c 0).re + (deriv (ψ c) 0).re * w))| ≤
        (4 * Clam * M / r0 * Kw ^ 2) * c ^ (-(4 / 3 : ℝ)) := by
      rw [abs_mul, abs_of_pos hlam_pos_c]
      have hw2 : w ^ 2 ≤ (Kw * c ^ (-(2 / 3 : ℝ))) ^ 2 := by
        rw [← sq_abs w]
        exact pow_le_pow_left₀ (abs_nonneg _) hw_bd' 2
      have hc53_le : c ^ (-(1 / 3 : ℝ)) * (c ^ (-(2 / 3 : ℝ))) ^ 2 ≤ c ^ (-(4 / 3 : ℝ)) := by
        have hpow : c ^ (-(1 / 3 : ℝ)) * (c ^ (-(2 / 3 : ℝ))) ^ 2 = c ^ (-(5 / 3 : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hc_pos.le, ← Real.rpow_add hc_pos]
          congr 1; norm_num
        rw [hpow]
        exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      calc lam c * |(ψ c (w : ℂ)).re - ((ψ c 0).re + (deriv (ψ c) 0).re * w)|
          ≤ (Clam * c ^ (-(1 / 3 : ℝ))) * ((4 * M / r0) * w ^ 2) :=
            mul_le_mul hlam_le hψ_t2 (abs_nonneg _) (by positivity)
        _ ≤ (Clam * c ^ (-(1 / 3 : ℝ))) * ((4 * M / r0) * (Kw * c ^ (-(2 / 3 : ℝ))) ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw2 (by positivity)) (by positivity)
        _ = (4 * Clam * M / r0 * Kw ^ 2) * (c ^ (-(1 / 3 : ℝ)) * (c ^ (-(2 / 3 : ℝ))) ^ 2) := by ring
        _ ≤ (4 * Clam * M / r0 * Kw ^ 2) * c ^ (-(4 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_left hc53_le (by positivity)
    have ht2 : |lam c * ((ψ c 0).re - β)| ≤ (Clam * C_jet) * c ^ (-(4 / 3 : ℝ)) := by
      rw [abs_mul, abs_of_pos hlam_pos_c]
      have hpow : c ^ (-(1 / 3 : ℝ)) * c ^ (-1 : ℝ) = c ^ (-(4 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc_pos]; congr 1; norm_num
      calc lam c * |(ψ c 0).re - β|
          ≤ (Clam * c ^ (-(1 / 3 : ℝ))) * (C_jet * c ^ (-1 : ℝ)) :=
            mul_le_mul hlam_le (hψ_val c hccψ) (abs_nonneg _) (by positivity)
        _ = (Clam * C_jet) * (c ^ (-(1 / 3 : ℝ)) * c ^ (-1 : ℝ)) := by ring
        _ = (Clam * C_jet) * c ^ (-(4 / 3 : ℝ)) := by rw [hpow]
    have ht3 : |lam c * ((deriv (ψ c) 0).re - γ) * w| ≤ (Clam * C_jet * Kw) * c ^ (-(4 / 3 : ℝ)) := by
      rw [abs_mul, abs_mul, abs_of_pos hlam_pos_c]
      have hpow : c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc_pos, ← Real.rpow_add hc_pos]; congr 1; norm_num
      calc lam c * |(deriv (ψ c) 0).re - γ| * |w|
          ≤ (Clam * c ^ (-(1 / 3 : ℝ))) * (C_jet * c ^ (-(1 / 3 : ℝ))) * (Kw * c ^ (-(2 / 3 : ℝ))) :=
            mul_le_mul (mul_le_mul hlam_le (hψ_der c hccψ) (abs_nonneg _) (by positivity))
              hw_bd' (abs_nonneg _) (by positivity)
        _ = (Clam * C_jet * Kw) * (c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ))) := by ring
        _ = (Clam * C_jet * Kw) * c ^ (-(4 / 3 : ℝ)) := by rw [hpow]
    have ht4 : |γ * (lam c * mu c) * (φa - Special.airyZero 1)| ≤ (|γ| * Clam * M) * c ^ (-(4 / 3 : ℝ)) := by
      rw [hlam_mu_c, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hc_pos.le _)]
      have hpow : c ^ (-1 : ℝ) * c ^ (-(1 / 3 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc_pos]; congr 1; norm_num
      calc |γ| * c ^ (-1 : ℝ) * |φa - Special.airyZero 1|
          ≤ |γ| * c ^ (-1 : ℝ) * (Clam * M * c ^ (-(1 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left hφa_sub_r (by positivity)
        _ = (|γ| * Clam * M) * (c ^ (-1 : ℝ) * c ^ (-(1 / 3 : ℝ))) := by ring
        _ = (|γ| * Clam * M) * c ^ (-(4 / 3 : ℝ)) := by rw [hpow]
    have htri : |lam c * ((ψ c (w : ℂ)).re - ((ψ c 0).re + (deriv (ψ c) 0).re * w)) +
        lam c * ((ψ c 0).re - β) + lam c * ((deriv (ψ c) 0).re - γ) * w +
        γ * (lam c * mu c) * (φa - Special.airyZero 1)| ≤
        (4 * Clam * M / r0 * Kw ^ 2 + Clam * C_jet + Clam * C_jet * Kw + |γ| * Clam * M) * c ^ (-(4 / 3 : ℝ)) := by
      have h1234 := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ht1 ht2)) ht3)) ht4)
      linarith only [h1234]
    have hCinv : 4 * Clam * M / r0 * Kw ^ 2 + Clam * C_jet + Clam * C_jet * Kw + |γ| * Clam * M ≤ C_inv := by
      dsimp [C_inv, Kw]
      exact le_max_right _ _
    exact htri.trans (mul_le_mul_of_nonneg_right hCinv hc43_nn)
  exact ⟨⟨ρc, hRmax_lt, hphi_diff⟩, hphi_im, h_bds, h_inv_real, h_a1_exp⟩

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.odd_holomorphic_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms odd_holomorphic_factor

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.fj_inverse_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fj_inverse_chart

end

end FormalResearch.ModularBootstrap.FiveTerm
