module

public import FormalResearch.ModularBootstrap.ChartGeometry.MidlineAndJunction
public import Mathlib.Analysis.Complex.AbsMax

/-!
# Quadrant Monotonicity of the Mellin Chart (Lemma J7Q, `vlo:J7Q`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J7, Lemma J7Q (`vlo:J7Q`,
lines 647–721).

Proves **Lemma J7Q** (`lemma_J7Q`):
* On the upper closed left half-strip `{0 ≤ Re ζ ≤ 1/2, 0 ≤ Im ζ}`:
  - `Re ω'(x + iy) ≤ 0` and `Im ω'(x + iy) ≤ 0` (`vlo:eOmegaQuadrant`).
  - The stronger cone estimate `0 ≤ -Im ω'(x + iy) ≤ -Re ω'(x + iy)` (`vlo:eOmegaCone`).
* Consequently, `0 ≤ Re ω(ζ)` throughout the entire closed left half-strip `{0 ≤ Re ζ ≤ 1/2}`
  (both for `Im ζ ≥ 0` and `Im ζ ≤ 0`).

Proof strategy: apply the maximum modulus principle (`Complex.norm_le_of_forall_mem_frontier_norm_le`)
on rectangles `(0, 1/2) × (0, Y)` to `exp(-i ω'(z))` and `exp((1 + i) ω'(z))`, using the
exact boundary signs on the bottom `[0, 1/2]`, left `i[0, Y]`, right `1/2 + i[0, Y]`, and top
`[0, 1/2] + iY` edges for sufficiently large `Y`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.ChartGeometry

open FormalResearch.ModularBootstrap.Chart

/-! ### Section 1: Boundary estimates on the four edges of `[0, 1/2] × [0, Y]` -/

private lemma deriv_chartOmega_bottom_edge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    (deriv chartOmega (x : ℂ)).im = 0 ∧ (deriv chartOmega (x : ℂ)).re ≤ 0 := by
  have hreal_Ioo : ∀ t ∈ Ioo (0 : ℝ) (1 / 2),
      (deriv chartOmega (t : ℂ)).im = 0 ∧ (deriv chartOmega (t : ℂ)).re ≤ 0 := by
    intro t ht
    have hne : (t : ℂ) ≠ 1 / 2 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith [ht.2]
    have hcos_pos : 0 < Real.cos (Real.pi * t) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, ht.1], by nlinarith [Real.pi_pos, ht.2]⟩
    have hsin_pos : 0 < Real.sin (Real.pi * t) :=
      Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos, ht.1]) (by nlinarith [Real.pi_pos, ht.2])
    have hcos_half_pos : 0 < Real.cos (Real.pi * t / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, ht.1], by nlinarith [Real.pi_pos, ht.2]⟩
    have hB_pos := chartB_pos_of_mem_Ioo ht
    have hQ_pos := chartQ_pos_of_mem_Ioo ht
    have hB_real : chartB (t : ℂ) = ((chartB (t : ℂ)).re : ℂ) := Complex.ext rfl hB_pos.2
    have hQ_real : chartQ (t : ℂ) = ((chartQ (t : ℂ)).re : ℂ) := Complex.ext rfl hQ_pos.2
    -- Note `deriv chartB t` and `deriv chartQ t` are negative real on (0, 1/2):
    have hB_antitone : AntitoneOn (fun s : ℝ => (chartB (s : ℂ)).re) (Ioo 0 (1 / 2)) := by
      intro a ha b hb hab
      dsimp only
      rw [chartB_ofReal_Icc ha.1.le ha.2.le, chartB_ofReal_Icc hb.1.le hb.2.le]
      simp only [Complex.ofReal_re]
      apply div_le_div_of_nonneg_right _ Real.pi_pos.le
      apply Real.arsinh_le_arsinh.mpr
      apply Real.sqrt_le_sqrt
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos, ha.1])
        (by nlinarith [Real.pi_pos, hb.2]) (by nlinarith [Real.pi_pos])
    have hQ_antitone : AntitoneOn (fun s : ℝ => (chartQ (s : ℂ)).re) (Ioo 0 (1 / 2)) := by
      intro a ha b hb hab
      dsimp only
      rw [chartQ_ofReal_Icc ha.1.le ha.2.le, chartQ_ofReal_Icc hb.1.le hb.2.le]
      simp only [Complex.ofReal_re]
      apply div_le_div_of_nonneg_right _ Real.pi_pos.le
      apply Real.arccos_le_arccos
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 2)
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos, ha.1])
        (by nlinarith [Real.pi_pos, hb.2]) (by nlinarith [Real.pi_pos])
    have hOm_antitone : AntitoneOn (fun s : ℝ => (chartOmega (s : ℂ)).re) (Ioo 0 (1 / 2)) := by
      intro a ha b hb hab
      have heq_a : (chartOmega (a : ℂ)).re =
          (2 * Real.pi / 3) * (chartB (a : ℂ)).re * (chartQ (a : ℂ)).re := by
        unfold chartOmega chartOmegaHalf
        simp only [Complex.ofReal_re, ha.2.le, ↓reduceIte]
        have hb_ra : chartB (a : ℂ) = ((chartB (a : ℂ)).re : ℂ) :=
          Complex.ext rfl (chartB_pos_of_mem_Ioo ha).2
        have hq_ra : chartQ (a : ℂ) = ((chartQ (a : ℂ)).re : ℂ) :=
          Complex.ext rfl (chartQ_pos_of_mem_Ioo ha).2
        rw [hb_ra, hq_ra]
        simp
      have heq_b : (chartOmega (b : ℂ)).re =
          (2 * Real.pi / 3) * (chartB (b : ℂ)).re * (chartQ (b : ℂ)).re := by
        unfold chartOmega chartOmegaHalf
        simp only [Complex.ofReal_re, hb.2.le, ↓reduceIte]
        have hb_rb : chartB (b : ℂ) = ((chartB (b : ℂ)).re : ℂ) :=
          Complex.ext rfl (chartB_pos_of_mem_Ioo hb).2
        have hq_rb : chartQ (b : ℂ) = ((chartQ (b : ℂ)).re : ℂ) :=
          Complex.ext rfl (chartQ_pos_of_mem_Ioo hb).2
        rw [hb_rb, hq_rb]
        simp
      change (chartOmega (b : ℂ)).re ≤ (chartOmega (a : ℂ)).re
      rw [heq_a, heq_b]
      have hb_le : (chartB (b : ℂ)).re ≤ (chartB (a : ℂ)).re := hB_antitone ha hb hab
      have hq_le : (chartQ (b : ℂ)).re ≤ (chartQ (a : ℂ)).re := hQ_antitone ha hb hab
      have hb_nn : 0 ≤ (chartB (b : ℂ)).re := (chartB_pos_of_mem_Ioo hb).1.le
      have hq_nn : 0 ≤ (chartQ (b : ℂ)).re := (chartQ_pos_of_mem_Ioo hb).1.le
      have ha_nn : 0 ≤ (chartB (a : ℂ)).re := (chartB_pos_of_mem_Ioo ha).1.le
      have hqa_nn : 0 ≤ (chartQ (a : ℂ)).re := (chartQ_pos_of_mem_Ioo ha).1.le
      have hpi_nn : 0 ≤ 2 * Real.pi / 3 := by positivity
      gcongr
    have h_om_im : ∀ s ∈ Ioo (0 : ℝ) (1 / 2), (chartOmega (s : ℂ)).im = 0 := fun s hs =>
      (chartOmega_ofReal_pos hs).2
    have hd_om : HasDerivAt chartOmega (deriv chartOmega (t : ℂ)) (t : ℂ) :=
      (analyticAt_chartOmega (by simp; exact ht.1.le) (by simp; linarith [ht.2])).differentiableAt.hasDerivAt
    have hline : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have hcomp := hd_om.comp t hline
    have hre_d : HasDerivAt (fun s : ℝ => (chartOmega (s : ℂ)).re) (deriv chartOmega (t : ℂ)).re t := by
      simpa [Function.comp_def] using Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomp
    have him_d : HasDerivAt (fun s : ℝ => (chartOmega (s : ℂ)).im) (deriv chartOmega (t : ℂ)).im t := by
      simpa [Function.comp_def] using Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hcomp
    have hev_im : (fun s : ℝ => (chartOmega (s : ℂ)).im) =ᶠ[𝓝 t] 0 := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact h_om_im s hs
    have him0 : (deriv chartOmega (t : ℂ)).im = 0 := by
      have h0 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
      exact (him_d.congr_of_eventuallyEq hev_im.symm).unique h0
    have hre_le : (deriv chartOmega (t : ℂ)).re ≤ 0 := by
      have hslope_tend : Tendsto (slope (fun s : ℝ => (chartOmega (s : ℂ)).re) t)
          (𝓝[>] t) (𝓝 (deriv chartOmega (t : ℂ)).re) := by
        have hgt : Tendsto (fun s : ℝ => s) (𝓝[>] t) (𝓝[≠] t) :=
          tendsto_nhdsWithin_mono_left (fun _ hs => ne_of_gt hs) tendsto_id
        exact (hasDerivAt_iff_tendsto_slope.mp hre_d).comp hgt
      refine le_of_tendsto hslope_tend ?_
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ht.1 ht.2)] with
        s (hs_gt : t < s) (hs_mem : s ∈ Ioo (0 : ℝ) (1 / 2))
      rw [slope_def_field]
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hOm_antitone ht hs_mem hs_gt.le))
        (sub_nonneg.mpr hs_gt.le)
    exact ⟨him0, hre_le⟩
  by_cases hmem : x ∈ Ioo (0 : ℝ) (1 / 2)
  · exact hreal_Ioo x hmem
  · -- Extend to endpoints x = 0 and x = 1/2 by continuity of deriv chartOmega on stripClosed
    have hcont : ContinuousAt (fun s : ℝ => deriv chartOmega (s : ℂ)) x := by
      refine (analyticAt_chartOmega (by simp; exact hx0) (by simp; linarith)).deriv.continuousAt.comp ?_
      fun_prop
    let s : ℕ → ℝ := fun n =>
      if x ≤ 0 then 1 / ((n : ℝ) + 4)
      else 1 / 2 - 1 / ((n : ℝ) + 4)
    have hs_mem : ∀ n : ℕ, s n ∈ Ioo (0 : ℝ) (1 / 2) := by
      intro n; dsimp [s]
      split_ifs with h0
      · have hn : (4 : ℝ) ≤ (n : ℝ) + 4 := by linarith
        exact ⟨by positivity, by rw [div_lt_iff₀ (by positivity)]; linarith⟩
      · have hn : (4 : ℝ) ≤ (n : ℝ) + 4 := by linarith
        have hlt : 1 / ((n : ℝ) + 4) < 1 / 2 := by rw [div_lt_iff₀ (by positivity)]; linarith
        have hpos_div : (0 : ℝ) < 1 / ((n : ℝ) + 4) := by positivity
        exact ⟨by linarith, by linarith⟩
    have hs_tend : Tendsto s atTop (𝓝 x) := by
      dsimp [s]
      split_ifs with h0
      · have hx_eq : x = 0 := le_antisymm h0 hx0
        subst hx_eq
        have h0' : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        refine (h0'.comp (tendsto_add_atTop_nat 3)).congr fun n => ?_
        simp only [Function.comp_def, one_div]; push_cast; ring
      · have hx_eq : x = 1 / 2 := by
          rcases lt_or_eq_of_le hx1 with hlt | rfl
          · exact False.elim (hmem ⟨lt_of_not_ge h0, hlt⟩)
          · rfl
        subst hx_eq
        have h0' : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h1' : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 4)) atTop (𝓝 0) := by
          refine (h0'.comp (tendsto_add_atTop_nat 3)).congr fun n => ?_
          simp only [Function.comp_def, one_div]; push_cast; ring
        simpa using tendsto_const_nhds.sub h1'
    have him_eq : (deriv chartOmega (x : ℂ)).im = 0 :=
      tendsto_nhds_unique ((Complex.continuous_im.continuousAt.comp hcont).tendsto.comp hs_tend)
        ((tendsto_const_nhds (x := (0 : ℝ))).congr fun n => ((hreal_Ioo _ (hs_mem n)).1).symm)
    have hre_le : (deriv chartOmega (x : ℂ)).re ≤ 0 :=
      le_of_tendsto ((Complex.continuous_re.continuousAt.comp hcont).tendsto.comp hs_tend)
        (Filter.Eventually.of_forall fun n => (hreal_Ioo _ (hs_mem n)).2)
    exact ⟨him_eq, hre_le⟩

private lemma xiStar_gt_pi_div_sixteen : Real.pi / 16 < xiStar := by
  unfold xiStar
  rw [div_lt_div_iff₀ (by norm_num) Real.pi_pos]
  have hexp_lt : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp23 : Real.exp (2 / 3 : ℝ) < 2 := by
    have hpow : Real.exp (2 / 3 : ℝ) ^ 3 = Real.exp 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (2 / 3 : ℝ) ^ 3 < 2 ^ 3 := by
      rw [hpow, h2]; nlinarith [Real.exp_pos 1]
    exact lt_of_pow_lt_pow_left₀ 3 (by norm_num) h3
  have hsh_lt : Real.sinh (2 / 3 : ℝ) < 1 := by
    rw [Real.sinh_eq]
    have hneg : 0 < Real.exp (-(2 / 3 : ℝ)) := Real.exp_pos _
    linarith
  have har_gt : (2 / 3 : ℝ) < Real.arsinh 1 := by
    rw [← Real.sinh_lt_sinh, Real.sinh_arsinh]
    exact hsh_lt
  have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi2 : Real.pi * Real.pi < 10 := by nlinarith [Real.pi_pos, hpi_lt]
  linarith [har_gt]

private lemma tanh_le_self_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    Real.tanh u ≤ u := by
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos u)]
  have hmono : MonotoneOn (fun t : ℝ => t * Real.cosh t - Real.sinh t) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop) fun t ht => ?_
    rw [interior_Ici] at ht
    have hd : HasDerivAt (fun s : ℝ => s * Real.cosh s - Real.sinh s) (t * Real.sinh t) t := by
      have h1 := ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)
      exact h1.congr_deriv (by simp)
    rw [hd.deriv]
    exact mul_nonneg ht.le (Real.sinh_nonneg_iff.mpr ht.le)
  have h0 := hmono (by simp : (0 : ℝ) ∈ Ici 0) hu hu
  simp only [zero_mul, Real.sinh_zero, sub_zero] at h0
  linarith

private lemma deriv_chartOmega_left_edge {y : ℝ} (hy : 0 ≤ y) :
    (deriv chartOmega (Complex.I * (y : ℂ))).re = -edgeNuDeriv y ∧
      (deriv chartOmega (Complex.I * (y : ℂ))).im = -edgeMuDeriv y ∧
      0 ≤ -(deriv chartOmega (Complex.I * (y : ℂ))).im ∧
      -(deriv chartOmega (Complex.I * (y : ℂ))).im ≤ -(deriv chartOmega (Complex.I * (y : ℂ))).re := by
  have hd : HasDerivAt chartOmega (deriv chartOmega (Complex.I * (y : ℂ))) (Complex.I * (y : ℂ)) :=
    (analyticAt_chartOmega (by simp) (by simp)).differentiableAt.hasDerivAt
  have hline : HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ)) Complex.I y := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul Complex.I
  have hcomp := hd.comp y hline
  have h_edge_d : HasDerivAt (fun t : ℝ => chartOmega (Complex.I * (t : ℂ)))
      ((edgeMuDeriv y : ℂ) - Complex.I * (edgeNuDeriv y : ℂ)) y := by
    have heq : (fun t : ℝ => chartOmega (Complex.I * (t : ℂ))) =
        (fun t : ℝ => (edgeMu t : ℂ) - Complex.I * (edgeNu t : ℂ)) := funext chartOmega_left_edge
    rw [heq]
    exact (hasDerivAt_edgeMu y).ofReal_comp.sub ((hasDerivAt_edgeNu y).ofReal_comp.const_mul Complex.I)
  have hu := hcomp.unique h_edge_d
  have hre_eq : (deriv chartOmega (Complex.I * (y : ℂ))).re = -edgeNuDeriv y := by
    have him := congrArg Complex.im hu
    simpa [Complex.mul_im] using him
  have him_eq : (deriv chartOmega (Complex.I * (y : ℂ))).im = -edgeMuDeriv y := by
    have hre := congrArg Complex.re hu
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub,
      Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, sub_zero] at hre
    linarith
  have hmu_nn : 0 ≤ edgeMuDeriv y := by
    unfold edgeMuDeriv
    exact mul_nonneg (by positivity [Real.pi_pos]) (edgeX0Deriv_nonneg hy)
  have hcone : edgeMuDeriv y ≤ edgeNuDeriv y := by
    unfold edgeMuDeriv edgeNuDeriv
    have hx_ge : xiStar ≤ edgeX0 y := xiStar_le_edgeX0 hy
    have hy0_nn : 0 ≤ edgeY0 y := by linarith [(edgeY0_bounds hy).1]
    have hx0d_nn : 0 ≤ edgeX0Deriv y := edgeX0Deriv_nonneg hy
    have hy0d_pos : 0 < edgeY0Deriv y := by linarith [(edgeY0Deriv_bounds y).1]
    by_cases hy0_half : edgeY0 y ≤ 1 / 2
    · have hratio : edgeX0Deriv y / edgeY0Deriv y = Real.tanh (Real.pi * y / 2) := by
        unfold edgeX0Deriv edgeY0Deriv
        have hch_pos : 0 < Real.cosh (Real.pi * y / 2) := Real.cosh_pos _
        have hrt_pos : 0 < √(Real.cosh (Real.pi * y)) := Real.sqrt_pos.mpr (Real.cosh_pos _)
        have hsq2_pos : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
        rw [Real.tanh_eq_sinh_div_cosh]
        field_simp [hch_pos.ne', hrt_pos.ne', hsq2_pos.ne']
      have hratio_le : edgeX0Deriv y / edgeY0Deriv y ≤ Real.pi * edgeY0 y := by
        rw [hratio]
        have h1 := tanh_le_self_of_nonneg (by positivity [Real.pi_pos] : 0 ≤ Real.pi * y / 2)
        have h2 := (edgeY0_bounds hy).1
        nlinarith [Real.pi_pos]
      have h_quad : edgeY0 y * (1 - 2 * edgeY0 y) ≤ 1 / 8 := by
        nlinarith [sq_nonneg (edgeY0 y - 1 / 4)]
      have h_inner : 0 ≤ 2 * edgeX0 y - (1 - 2 * edgeY0 y) * (edgeX0Deriv y / edgeY0Deriv y) := by
        have h12 : 0 ≤ 1 - 2 * edgeY0 y := by linarith
        have hprod : (1 - 2 * edgeY0 y) * (edgeX0Deriv y / edgeY0Deriv y) ≤
            (1 - 2 * edgeY0 y) * (Real.pi * edgeY0 y) :=
          mul_le_mul_of_nonneg_left hratio_le h12
        have hpi8 : (1 - 2 * edgeY0 y) * (Real.pi * edgeY0 y) ≤ Real.pi / 8 := by
          nlinarith [Real.pi_pos]
        have hxi := xiStar_gt_pi_div_sixteen
        linarith
      have hmul := mul_le_mul_of_nonneg_left h_inner hy0d_pos.le
      rw [mul_zero] at hmul
      have h_alg : edgeY0Deriv y * (2 * edgeX0 y - (1 - 2 * edgeY0 y) * (edgeX0Deriv y / edgeY0Deriv y)) =
          2 * edgeX0 y * edgeY0Deriv y + 2 * edgeX0Deriv y * edgeY0 y - edgeX0Deriv y := by
        field_simp [hy0d_pos.ne']; ring
      rw [h_alg] at hmul
      nlinarith [Real.pi_pos]
    · push Not at hy0_half
      have h1 : 0 ≤ (2 * edgeY0 y - 1) * edgeX0Deriv y := by nlinarith
      have h2 : 0 ≤ 2 * edgeX0 y * edgeY0Deriv y := by nlinarith [xiStar_pos]
      nlinarith [Real.pi_pos]
  refine ⟨hre_eq, him_eq, by linarith, by linarith⟩

/-- **Lemma J7Q (`vlo:J7Q`, `lower_o1_two_edge.tex`, lines 647–721)**:
Quadrant monotonicity of the Mellin chart on the closed left half-strip `{0 ≤ Re ζ ≤ 1/2}`:
1. On the upper closed left half-strip (`0 ≤ x ≤ 1/2`, `0 ≤ y`),
   `Re ω'(x + iy) ≤ 0` and `Im ω'(x + iy) ≤ 0` (`vlo:eOmegaQuadrant`), and in fact
   `0 ≤ -Im ω'(x + iy) ≤ -Re ω'(x + iy)` (`vlo:eOmegaCone`).
2. Throughout the closed left half-strip (`0 ≤ Re ζ ≤ 1/2`), `0 ≤ Re ω(ζ)`. -/
theorem lemma_J7Q :
    (∀ x y : ℝ, 0 ≤ x → x ≤ 1 / 2 → 0 ≤ y →
      (deriv chartOmega ((x : ℂ) + Complex.I * (y : ℂ))).re ≤ 0 ∧
      (deriv chartOmega ((x : ℂ) + Complex.I * (y : ℂ))).im ≤ 0 ∧
      0 ≤ -(deriv chartOmega ((x : ℂ) + Complex.I * (y : ℂ))).im ∧
      -(deriv chartOmega ((x : ℂ) + Complex.I * (y : ℂ))).im ≤
        -(deriv chartOmega ((x : ℂ) + Complex.I * (y : ℂ))).re) ∧
    (∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 / 2 → 0 ≤ (chartOmega ζ).re) := by
  obtain ⟨C₁, hC₁, hOm'_large⟩ := deriv_chartOmega_large_height
  obtain ⟨C₂, hC₂, hIm_large⟩ := im_deriv_chartOmega_large_height
  -- Choose Y₀ ≥ 2 large enough for the top edge:
  -- 1) C₂ * (1 + Y) * exp(-π Y) ≤ π / 3  (gives Im ω'(x + iY) ≤ 0)
  -- 2) (C₁ + C₂/2) * (1 + Y) * exp(-π Y) + π/6 ≤ (2π/3) * B_Y  (gives Re ω'(x + iY) - Im ω'(x + iY) ≤ 0)
  have hexp_tend : Tendsto (fun Y : ℝ => (1 + Y) * Real.exp (-Real.pi * Y)) atTop (𝓝 0) := by
    have h_u : Tendsto (fun u : ℝ => u * Real.exp (-u)) atTop (𝓝 0) := by
      simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h_pi : Tendsto (fun Y : ℝ => Real.pi * (1 + Y)) atTop atTop :=
      (tendsto_atTop_add_const_left atTop 1 tendsto_id).const_mul_atTop Real.pi_pos
    have hcomp := h_u.comp h_pi
    have heq : (fun Y : ℝ => (1 + Y) * Real.exp (-Real.pi * Y)) =
        (fun Y : ℝ => (Real.exp Real.pi / Real.pi) *
          ((Real.pi * (1 + Y)) * Real.exp (-(Real.pi * (1 + Y))))) := by
      ext Y
      rw [show -(Real.pi * (1 + Y)) = -Real.pi + (-Real.pi * Y) by ring, Real.exp_add, Real.exp_neg]
      field_simp [Real.pi_pos.ne', (Real.exp_pos Real.pi).ne']
    rw [heq]; simpa using tendsto_const_nhds.mul hcomp
  have hY₀_ev : ∀ᶠ (Y : ℝ) in atTop,
      2 ≤ Y ∧
      C₂ * (1 + Y) * Real.exp (-Real.pi * Y) ≤ Real.pi / 3 ∧
      C₁ * (1 + Y) * Real.exp (-Real.pi * Y) + Real.pi / 3 ≤ (2 * Real.pi / 3) * chartBTau Y := by
    have h1 : ∀ᶠ (Y : ℝ) in atTop, C₂ * (1 + Y) * Real.exp (-Real.pi * Y) ≤ Real.pi / 3 :=
      ((by simpa using hexp_tend.const_mul C₂ :
        Tendsto (fun Y : ℝ => C₂ * ((1 + Y) * Real.exp (-Real.pi * Y))) atTop (𝓝 0)).eventually
        (Iio_mem_nhds (by positivity : (0 : ℝ) < Real.pi / 3))).mono
        fun Y hY => by
          have : C₂ * ((1 + Y) * Real.exp (-Real.pi * Y)) ≤ Real.pi / 3 := le_of_lt hY
          linarith
    have h2 : ∀ᶠ (Y : ℝ) in atTop, C₁ * (1 + Y) * Real.exp (-Real.pi * Y) ≤ 1 :=
      ((by simpa using hexp_tend.const_mul C₁ :
        Tendsto (fun Y : ℝ => C₁ * ((1 + Y) * Real.exp (-Real.pi * Y))) atTop (𝓝 0)).eventually
        (Iio_mem_nhds zero_lt_one)).mono
        fun Y hY => by
          have : C₁ * ((1 + Y) * Real.exp (-Real.pi * Y)) ≤ 1 := le_of_lt hY
          linarith
    have h3 : ∀ᶠ (Y : ℝ) in atTop, 1 + Real.pi / 3 ≤ (2 * Real.pi / 3) * chartBTau Y := by
      filter_upwards [Ici_mem_atTop (3 : ℝ)] with Y hY
      rw [mem_Ici] at hY
      have hB : Y / 2 ≤ chartBTau Y := by
        unfold chartBTau
        have : 0 ≤ Real.log 2 / (2 * Real.pi) :=
          div_nonneg (Real.log_nonneg (by norm_num)) (by positivity [Real.pi_pos])
        linarith
      have hpi3 := Real.pi_gt_three
      nlinarith
    filter_upwards [eventually_ge_atTop 2, h1, h2, h3] with Y h2Y ha hb hc
    exact ⟨h2Y, ha, by linarith⟩
  have h_rect : ∀ x y : ℝ, 0 ≤ x → x ≤ 1 / 2 → 0 ≤ y →
      (deriv chartOmega ((x : ℂ) + Complex.I * (y : ℂ))).im ≤ 0 ∧
      (deriv chartOmega ((x : ℂ) + Complex.I * (y : ℂ))).re -
        (deriv chartOmega ((x : ℂ) + Complex.I * (y : ℂ))).im ≤ 0 := by
    intro x y hx0 hx1 hy0
    obtain ⟨Y, ⟨hY2, hY_c2, hY_c1⟩, hY_gt⟩ := (hY₀_ev.and (eventually_gt_atTop y)).exists
    let U : Set ℂ := Ioo (0 : ℝ) (1 / 2) ×ℂ Ioo (0 : ℝ) Y
    have hU_bdd : Bornology.IsBounded U :=
      (isBounded_Ioo (0 : ℝ) (1 / 2)).reProdIm (isBounded_Ioo (0 : ℝ) Y)
    have hU_cl : closure U = Icc (0 : ℝ) (1 / 2) ×ℂ Icc (0 : ℝ) Y := by
      rw [closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1 / 2),
        closure_Ioo (by linarith : (0 : ℝ) ≠ Y)]
    have hU_sub : closure U ⊆ stripClosed := by
      intro z hz
      rw [hU_cl] at hz
      exact ⟨hz.1.1, by linarith [hz.1.2]⟩
    have hdiff_cl : ContinuousOn (deriv chartOmega) (closure U) := fun z hz =>
      (analyticAt_chartOmega (hU_sub hz).1 (hU_sub hz).2).deriv.continuousAt.continuousWithinAt
    have hdiff_U : DifferentiableOn ℂ (deriv chartOmega) U := fun z hz =>
      (analyticAt_chartOmega (hU_sub (subset_closure hz)).1
        (hU_sub (subset_closure hz)).2).deriv.differentiableAt.differentiableWithinAt
    have h_bdy : ∀ z ∈ frontier U,
        (deriv chartOmega z).im ≤ 0 ∧ (deriv chartOmega z).re - (deriv chartOmega z).im ≤ 0 := by
      intro z hz
      have hz_cl : z ∈ Icc (0 : ℝ) (1 / 2) ×ℂ Icc (0 : ℝ) Y := hU_cl ▸ frontier_subset_closure hz
      have hz_not_U : z ∉ U := by
        intro hmem
        have hopen : IsOpen U := isOpen_Ioo.reProdIm isOpen_Ioo
        exact (hopen.frontier_eq ▸ hz).2 hmem
      have hz_eq : z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by apply Complex.ext <;> simp
      rcases eq_or_lt_of_le hz_cl.1.1 with hx_0 | hx_pos
      · -- Left edge: z.re = 0
        rw [hz_eq, ← hx_0, Complex.ofReal_zero, zero_add]
        have hL := deriv_chartOmega_left_edge hz_cl.2.1
        exact ⟨by linarith [hL.2.2.1], by linarith [hL.2.2.2]⟩
      · rcases eq_or_lt_of_le hz_cl.1.2 with hx_half | hx_lt
        · -- Right edge: z.re = 1/2
          rw [hz_eq, hx_half]
          have h12 : (((1 / 2 : ℝ) : ℂ) + Complex.I * (z.im : ℂ)) =
              (1 / 2 : ℂ) + Complex.I * (z.im : ℂ) := by push_cast; rfl
          rw [h12]
          have hR := deriv_chartOmega_midline_real_neg hz_cl.2.1
          exact ⟨hR.1.le, by linarith [hR.2]⟩
        · rcases eq_or_lt_of_le hz_cl.2.1 with hy_0 | hy_pos
          · -- Bottom edge: z.im = 0
            rw [hz_eq, ← hy_0, Complex.ofReal_zero, mul_zero, add_zero]
            have hB := deriv_chartOmega_bottom_edge hz_cl.1.1 hz_cl.1.2
            exact ⟨hB.1.le, by linarith [hB.2]⟩
          · rcases eq_or_lt_of_le hz_cl.2.2 with hy_Y | hy_lt
            · -- Top edge: z.im = Y
              rw [hz_eq, hy_Y]
              have hIm_est := hIm_large hz_cl.1.1 hz_cl.1.2 hY2
              have hOm_est := hOm'_large hz_cl.1.1 hz_cl.1.2 hY2
              have h_im_le : (deriv chartOmega ((z.re : ℂ) + Complex.I * (Y : ℂ))).im ≤ 0 := by
                have h1 := (abs_le.mp hIm_est).2
                have hmul : (1 / 2 - z.re) * (C₂ * (1 + Y) * Real.exp (-Real.pi * Y)) ≤
                    (1 / 2 - z.re) * (Real.pi / 3) :=
                  mul_le_mul_of_nonneg_left hY_c2 (by linarith [hz_cl.1.2])
                linarith
              have h_re_sub_im : (deriv chartOmega ((z.re : ℂ) + Complex.I * (Y : ℂ))).re -
                  (deriv chartOmega ((z.re : ℂ) + Complex.I * (Y : ℂ))).im ≤ 0 := by
                have hre_bd := (abs_le.mp ((Complex.abs_re_le_norm _).trans hOm_est)).2
                have hre_le : (deriv chartOmega ((z.re : ℂ) + Complex.I * (Y : ℂ))).re ≤
                    -(2 * Real.pi / 3) * chartBTau Y + C₁ * (1 + Y) * Real.exp (-Real.pi * Y) := by
                  have hsub : (deriv chartOmega ((z.re : ℂ) + Complex.I * (Y : ℂ)) -
                      (-((2 * Real.pi / 3 * chartBTau Y : ℝ) : ℂ) -
                        ((Real.pi / 3 * (1 / 2 - z.re) : ℝ) : ℂ) * Complex.I)).re =
                      (deriv chartOmega ((z.re : ℂ) + Complex.I * (Y : ℂ))).re +
                        (2 * Real.pi / 3) * chartBTau Y := by simp
                  linarith
                have him_ge : -(Real.pi / 3) * (1 / 2 - z.re) -
                    (1 / 2 - z.re) * C₂ * (1 + Y) * Real.exp (-Real.pi * Y) ≤
                    (deriv chartOmega ((z.re : ℂ) + Complex.I * (Y : ℂ))).im := by
                  have h1 := (abs_le.mp hIm_est).1
                  linarith
                have him_ge' : -(Real.pi / 3) ≤ (deriv chartOmega ((z.re : ℂ) + Complex.I * (Y : ℂ))).im := by
                  have h1 : (1 / 2 - z.re) * (C₂ * (1 + Y) * Real.exp (-Real.pi * Y)) ≤
                      (1 / 2) * (Real.pi / 3) := by
                    calc (1 / 2 - z.re) * (C₂ * (1 + Y) * Real.exp (-Real.pi * Y))
                        ≤ (1 / 2 - z.re) * (Real.pi / 3) :=
                          mul_le_mul_of_nonneg_left hY_c2 (by linarith [hz_cl.1.2])
                      _ ≤ (1 / 2) * (Real.pi / 3) := by nlinarith [hz_cl.1.1, Real.pi_pos]
                  have h2 : (Real.pi / 3) * (1 / 2 - z.re) ≤ (Real.pi / 3) * (1 / 2) := by
                    nlinarith [hz_cl.1.1, Real.pi_pos]
                  linarith
                linarith
              exact ⟨h_im_le, h_re_sub_im⟩
            · exact False.elim (hz_not_U ⟨⟨hx_pos, hx_lt⟩, ⟨hy_pos, hy_lt⟩⟩)
    let f₁ : ℂ → ℂ := fun z => Complex.exp (-Complex.I * deriv chartOmega z)
    let f₂ : ℂ → ℂ := fun z => Complex.exp ((1 + Complex.I) * deriv chartOmega z)
    have hf₁_d : DiffContOnCl ℂ f₁ U :=
      ⟨fun z hz => Complex.differentiableAt_exp.comp_differentiableWithinAt z
          ((hdiff_U z hz).const_mul (-Complex.I)),
        ContinuousOn.cexp (continuousOn_const.mul hdiff_cl)⟩
    have hf₂_d : DiffContOnCl ℂ f₂ U :=
      ⟨fun z hz => Complex.differentiableAt_exp.comp_differentiableWithinAt z
          ((hdiff_U z hz).const_mul (1 + Complex.I)),
        ContinuousOn.cexp (continuousOn_const.mul hdiff_cl)⟩
    have hf₁_bdy : ∀ z ∈ frontier U, ‖f₁ z‖ ≤ 1 := by
      intro z hz
      dsimp [f₁]
      rw [Complex.norm_exp, show (-Complex.I * deriv chartOmega z).re = (deriv chartOmega z).im by
        simp [Complex.mul_re]]
      exact Real.exp_le_one_iff.mpr (h_bdy z hz).1
    have hf₂_bdy : ∀ z ∈ frontier U, ‖f₂ z‖ ≤ 1 := by
      intro z hz
      dsimp [f₂]
      rw [Complex.norm_exp, show ((1 + Complex.I) * deriv chartOmega z).re =
          (deriv chartOmega z).re - (deriv chartOmega z).im by
        simp [Complex.mul_re]]
      exact Real.exp_le_one_iff.mpr (h_bdy z hz).2
    have hz_mem : (x : ℂ) + Complex.I * (y : ℂ) ∈ closure U := by
      rw [hU_cl]
      exact ⟨⟨by simpa using hx0, by simpa using hx1⟩, ⟨by simpa using hy0, by simpa using hY_gt.le⟩⟩
    have h1 := Complex.norm_le_of_forall_mem_frontier_norm_le hU_bdd hf₁_d hf₁_bdy hz_mem
    have h2 := Complex.norm_le_of_forall_mem_frontier_norm_le hU_bdd hf₂_d hf₂_bdy hz_mem
    dsimp [f₁, f₂] at h1 h2
    rw [Complex.norm_exp, show (-Complex.I * deriv chartOmega ((x : ℂ) + Complex.I * (y : ℂ))).re =
        (deriv chartOmega ((x : ℂ) + Complex.I * (y : ℂ))).im by simp [Complex.mul_re],
      Real.exp_le_one_iff] at h1
    rw [Complex.norm_exp, show ((1 + Complex.I) * deriv chartOmega ((x : ℂ) + Complex.I * (y : ℂ))).re =
        (deriv chartOmega ((x : ℂ) + Complex.I * (y : ℂ))).re -
          (deriv chartOmega ((x : ℂ) + Complex.I * (y : ℂ))).im by simp [Complex.mul_re],
      Real.exp_le_one_iff] at h2
    exact ⟨h1, h2⟩
  refine ⟨fun x y hx0 hx1 hy0 => ?_, fun ζ h0 h1 => ?_⟩
  · obtain ⟨him, hcone⟩ := h_rect x y hx0 hx1 hy0
    exact ⟨by linarith, him, by linarith, by linarith⟩
  · have h_nonneg : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 / 2 → 0 ≤ w.im → 0 ≤ (chartOmega w).re := by
      intro w hw0 hw1 hwim
      let g : ℝ → ℝ := fun t => (chartOmega ((t : ℂ) + Complex.I * (w.im : ℂ))).re
      have hg_anti : AntitoneOn g (Icc 0 (1 / 2)) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
        · refine Complex.continuous_re.comp_continuousOn ?_
          refine continuousOn_chartOmega.comp (by fun_prop) fun t ht => ?_
          exact ⟨by simp; exact ht.1, by simp; linarith [ht.2]⟩
        · intro t ht
          have htm := interior_subset ht
          have hd := (analyticAt_chartOmega (ζ := (t : ℂ) + Complex.I * (w.im : ℂ))
            (by simp; exact htm.1) (by simp; linarith [htm.2])).differentiableAt.hasDerivAt
          have hline : HasDerivAt (fun s : ℝ => (s : ℂ) + Complex.I * (w.im : ℂ)) 1 t := by
            simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const (Complex.I * (w.im : ℂ))
          exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hd.comp t hline)).differentiableAt.differentiableWithinAt
        · intro t ht
          have htm := interior_subset ht
          have hd := (analyticAt_chartOmega (ζ := (t : ℂ) + Complex.I * (w.im : ℂ))
            (by simp; exact htm.1) (by simp; linarith [htm.2])).differentiableAt.hasDerivAt
          have hline : HasDerivAt (fun s : ℝ => (s : ℂ) + Complex.I * (w.im : ℂ)) 1 t := by
            simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const (Complex.I * (w.im : ℂ))
          have hre_d : HasDerivAt g (deriv chartOmega ((t : ℂ) + Complex.I * (w.im : ℂ))).re t := by
            simpa [g, Function.comp_def] using
              Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hd.comp t hline)
          rw [hre_d.deriv]
          obtain ⟨him, hcone⟩ := h_rect t w.im htm.1 htm.2 hwim
          linarith
      have hdiff := hg_anti ⟨hw0, hw1⟩ ⟨by norm_num, le_rfl⟩ hw1
      have hw_eq : w = (w.re : ℂ) + Complex.I * (w.im : ℂ) := by apply Complex.ext <;> simp
      have hg_half : g (1 / 2) = 0 := by
        dsimp [g]
        have h12 : (((1 / 2 : ℝ) : ℂ) + Complex.I * (w.im : ℂ)) =
            (1 / 2 : ℂ) + Complex.I * (w.im : ℂ) := by push_cast; rfl
        rw [h12, chartOmega_midline_nonneg hwim]
        simp [Complex.mul_re, sq]
      rw [hg_half] at hdiff
      simpa [g, ← hw_eq] using hdiff
    by_cases hζim : 0 ≤ ζ.im
    · exact h_nonneg ζ h0 h1 hζim
    · push Not at hζim
      have hconj := chartOmega_conj h0 (by linarith)
      have hre : (chartOmega ζ).re = (chartOmega (starRingEnd ℂ ζ)).re := by
        rw [hconj, Complex.conj_re]
      rw [hre]
      exact h_nonneg (starRingEnd ℂ ζ) (by simpa using h0) (by simpa using h1) (by simp; linarith)

/-- info: 'FormalResearch.ModularBootstrap.ChartGeometry.lemma_J7Q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ChartGeometry.lemma_J7Q

end FormalResearch.ModularBootstrap.ChartGeometry