module

public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerKernelDeriv

/-!
# `(F2)`: `|∂_y^j K(x, y)| ≤ C (1 + y)^{-j}` (`j = 1, 2`)

`remainder.tex`, Proposition 1.2(2), input `(F2)`.  Main statement `langerK_deriv_bounds`: for every `r₀ > 0`
there is `C` with, for all `x ∈ X = [ξ_*/2, ξ_* + r₀]` and `y ≥ ξ_*`,
`|K_y(x,y)| ≤ C/(1+y)` and `|K_yy(x,y)| ≤ C/(1+y)²`.

Proof, with `δ = ξ_*/4`:  near the diagonal (`|y - x| < δ`) through the Hadamard integrals for `D(x, ·)'` and
`D(x, ·)''` (`τ ∈ C³`); for `y ≤ x - δ` and `x + δ ≤ y ≤ Y₁` by compactness (explicit formulas); for `y ≥ Y₁`
(`τ(Y₁) ≥ 2τ(ξ_* + r₀)`) through `τ'/τ ≲ 1/y`, `|τ''|/τ ≲ 1/y²` (`langerTau_large`) and the bounds on
`𝔥'`, `𝔥''` (`combH_bounds`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb FormalResearch.Special

/-- The interval of `x`: `X = [ξ_*/2, ξ_* + r₀]`. -/
def langerX (r0 : ℝ) : Set ℝ := Icc (xiStar / 2) (xiStar + r0)

lemma abs_hadInt_le {w K : ℝ → ℝ} {c q B M : ℝ} (hw : ∀ t ∈ Icc (0 : ℝ) 1, |w t| ≤ B)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, |K (c + t * (q - c))| ≤ M) (hB : 0 ≤ B) :
    |hadInt w K c q| ≤ B * M := by
  unfold hadInt
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t => w t * K (c + t * (q - c))) (C := B * M) (fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hw t ht') (hK t ht') (abs_nonneg _) hB)
  simpa using h

/-- Near the diagonal. -/
theorem langerK_deriv_bounds_near (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ C : ℝ, ∀ x ∈ langerX r0, ∀ y : ℝ, |y - x| < xiStar / 4 →
      |deriv (langerK x) y| ≤ C ∧ |deriv (deriv (langerK x)) y| ≤ C := by
  have hxs := xiStar_pos
  obtain ⟨c0, hc0, hc0le⟩ := langerTau_deriv_ge_const_of (a := xiStar / 4) (by linarith)
  obtain ⟨M, hM⟩ := langerTau_deriv_bound_compact3 (a := xiStar / 4)
    (b := xiStar + r0 + xiStar / 4) (by linarith)
  have hLc1 : Continuous (deriv langerL) := (contDiff_langerL 1).continuous_deriv le_rfl
  have hLd : ContDiff ℝ 2 (deriv langerL) := (contDiff_langerL 3).iterate_deriv' 2 1
  have hLc2 : Continuous (deriv (deriv langerL)) := hLd.continuous_deriv (by norm_num)
  obtain ⟨M1, hM1⟩ := (isCompact_Icc (a := -(xiStar / 4)) (b := xiStar / 4)).exists_bound_of_continuousOn
    hLc1.continuousOn
  obtain ⟨M2, hM2⟩ := (isCompact_Icc (a := -(xiStar / 4)) (b := xiStar / 4)).exists_bound_of_continuousOn
    hLc2.continuousOn
  obtain ⟨CH, hCH, hHb, _⟩ := combH_bounds
  have hM0 : 0 ≤ M := by
    have := (hM (xiStar / 4) ⟨le_rfl, by linarith⟩).1
    exact le_trans (abs_nonneg _) this
  have hM10 : 0 ≤ M1 := le_trans (norm_nonneg _) (hM1 0 ⟨by linarith, by linarith⟩)
  have hM20 : 0 ≤ M2 := le_trans (norm_nonneg _) (hM2 0 ⟨by linarith, by linarith⟩)
  refine ⟨M1 + M / c0 + 4 / (3 * xiStar) + (M2 + (M / c0 + (M / c0) ^ 2) + CH * (4 / (3 * xiStar)) ^ 2) + 1,
    fun x hx y hy => ?_⟩
  have hx0 : 0 < x := by linarith [hx.1]
  have hyb : |y - x| < xiStar / 4 := hy
  have hy1 := (abs_lt.1 hyb)
  have hy0 : 0 < y := by linarith [hx.1]
  have hρ : xiStar / 2 ≤ x := hx.1
  have hyball : y ∈ ball x (xiStar / 2) := by
    rw [mem_ball, Real.dist_eq]; exact lt_trans hyb (by linarith)
  have hyball' : y ∈ ball x (xiStar / 4) := by rw [mem_ball, Real.dist_eq]; exact hyb
  -- bounds on D, D', D''
  have hD : c0 ≤ langerD x y := langerD_ge (a := xiStar / 4) (by linarith) hc0le (by linarith [hx.1])
    (by linarith)
  have hDp : 0 < langerD x y := lt_of_lt_of_le hc0 hD
  have hmemI : ∀ t ∈ Icc (0 : ℝ) 1, x + t * (y - x) ∈ Icc (xiStar / 4) (xiStar + r0 + xiStar / 4) := by
    intro t ht
    have : |t * (y - x)| ≤ |y - x| := by
      rw [abs_mul, abs_of_nonneg ht.1]; exact mul_le_of_le_one_left (abs_nonneg _) ht.2
    have h3 := abs_le.1 (this.trans hyb.le)
    constructor <;> linarith [hx.1, hx.2]
  have hD1 : |deriv (langerD x) y| ≤ M := by
    rw [deriv_langerD_eq (ρ := xiStar / 2) hρ hyball]
    have := abs_hadInt_le (w := fun t => t * 1) (K := deriv (deriv langerTau)) (c := x) (q := y)
      (B := 1) (M := M) (fun t ht => by simp [abs_of_nonneg ht.1, ht.2])
      (fun t ht => (hM _ (hmemI t ht)).2.1) zero_le_one
    simpa using this
  have hD2 : |deriv (deriv (langerD x)) y| ≤ M := by
    rw [deriv2_langerD_eq (ρ := xiStar / 2) hρ hyball]
    have := abs_hadInt_le (w := fun t => t * (t * 1)) (K := deriv (deriv (deriv langerTau))) (c := x)
      (q := y) (B := 1) (M := M)
      (fun t ht => by
        have : t * (t * 1) ≤ 1 := by nlinarith [ht.1, ht.2]
        rw [abs_of_nonneg (by nlinarith [ht.1, ht.2])]; exact this)
      (fun t ht => (hM _ (hmemI t ht)).2.2) zero_le_one
    simpa using this
  -- L bounds
  have hw : x - y ∈ Icc (-(xiStar / 4)) (xiStar / 4) := ⟨by linarith, by linarith⟩
  have hL1 : |deriv langerL (x - y)| ≤ M1 := by simpa using hM1 _ hw
  have hL2 : |deriv (deriv langerL) (x - y)| ≤ M2 := by simpa using hM2 _ hw
  -- combH bounds
  have hz : 3 * xiStar / 4 ≤ x + y := by linarith [hx.1]
  have hzp : 0 < x + y := by linarith
  have hH1 : combHDeriv (x + y) ≤ 4 / (3 * xiStar) := by
    refine ((hHb (x + y) hzp).2.1).trans ?_
    rw [inv_eq_one_div, div_le_div_iff₀ hzp (by positivity)]; nlinarith
  have hH1p : 0 < combHDeriv (x + y) := (hHb (x + y) hzp).1
  have hH2 : |combHSecond (x + y)| ≤ CH * (4 / (3 * xiStar)) ^ 2 := by
    refine ((hHb (x + y) hzp).2.2.2.2).trans ?_
    have h4 : 1 / (x + y) ≤ 4 / (3 * xiStar) := by
      rw [div_le_div_iff₀ hzp (by positivity)]; nlinarith
    have h5 : (1 / (x + y)) ^ 2 ≤ (4 / (3 * xiStar)) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
    have : CH / (x + y) ^ 2 = CH * (1 / (x + y)) ^ 2 := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h5 hCH.le
  have hq1 : |deriv (langerD x) y / langerD x y| ≤ M / c0 := by
    rw [abs_div, abs_of_pos hDp]
    calc |deriv (langerD x) y| / langerD x y ≤ M / langerD x y :=
          div_le_div_of_nonneg_right hD1 hDp.le
      _ ≤ M / c0 := div_le_div_of_nonneg_left hM0 hc0 hD
  have hq2 : |deriv (deriv (langerD x)) y / langerD x y| ≤ M / c0 := by
    rw [abs_div, abs_of_pos hDp]
    calc |deriv (deriv (langerD x)) y| / langerD x y ≤ M / langerD x y :=
          div_le_div_of_nonneg_right hD2 hDp.le
      _ ≤ M / c0 := div_le_div_of_nonneg_left hM0 hc0 hD
  have hq3 : |(deriv (langerD x) y / langerD x y) ^ 2| ≤ (M / c0) ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hq1 2
  have pq : 0 ≤ M / c0 := div_nonneg hM0 hc0.le
  have pr : 0 ≤ CH * (4 / (3 * xiStar)) ^ 2 := mul_nonneg hCH.le (sq_nonneg _)
  have ps : 0 ≤ (M / c0) ^ 2 := sq_nonneg _
  constructor
  · rw [deriv_langerK_eq hx0 hy0]
    have a1 := abs_le.1 hL1
    have a2 := abs_le.1 hq1
    rw [abs_le]
    constructor <;> linarith
  · rw [deriv2_langerK_eq hx0 hy0]
    have e : (deriv (deriv (langerD x)) y * langerD x y - deriv (langerD x) y ^ 2) / langerD x y ^ 2 =
        deriv (deriv (langerD x)) y / langerD x y - (deriv (langerD x) y / langerD x y) ^ 2 := by
      field_simp
    rw [e]
    have a1 := abs_le.1 hL2
    have a2 := abs_le.1 hq2
    have a3 := abs_le.1 hq3
    have a4 := abs_le.1 hH2
    rw [abs_le]
    constructor <;> linarith

/-- `1/z ≤ A/(1+y)` when `z = y - x ≥ δ` (helper for the up regime). -/
lemma inv_le_of_ge {x y δ : ℝ} (hδ : 0 < δ) (hx : 0 < x) (hxy : x + δ ≤ y) :
    1 / (y - x) ≤ (1 + (1 + x) / δ) / (1 + y) := by
  have hyx : 0 < y - x := by linarith
  have hy1 : 0 < 1 + y := by linarith
  rw [div_le_div_iff₀ hyx hy1]
  have : (1 + x) / δ * (y - x) ≥ 1 + x := by
    rw [ge_iff_le, ← sub_nonneg]
    have : (1 + x) / δ * (y - x) - (1 + x) = (1 + x) / δ * (y - x - δ) := by
      field_simp
    rw [this]
    exact mul_nonneg (by positivity) (by linarith)
  nlinarith

/-- Below the diagonal: `ξ_* ≤ y ≤ x - δ`. -/
theorem langerK_deriv_bounds_down (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ C : ℝ, ∀ x ∈ langerX r0, ∀ y : ℝ, xiStar ≤ y → y ≤ x - xiStar / 4 →
      |deriv (langerK x) y| ≤ C ∧ |deriv (deriv (langerK x)) y| ≤ C := by
  have hxs := xiStar_pos
  obtain ⟨c0, hc0, hc0le⟩ := langerTau_deriv_ge_const_of (a := xiStar / 4) (by linarith)
  obtain ⟨M, hM⟩ := langerTau_deriv_bound_compact3 (a := xiStar / 4)
    (b := xiStar + r0 + xiStar / 4) (by linarith)
  obtain ⟨CH, hCH, hHb, _⟩ := combH_bounds
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (xiStar / 4) ⟨le_rfl, by linarith⟩).1
  set T1 : ℝ := M / (c0 * (xiStar / 4)) with hT1
  have hT10 : 0 ≤ T1 := by positivity
  refine ⟨4 / xiStar + 1 / xiStar + T1 + (CH * (4 / xiStar) ^ 2 + CH * (1 / xiStar) ^ 2 + T1 + T1 ^ 2) + 1,
    fun x hx y hy1 hy2 => ?_⟩
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith
  have hyx : y < x := by linarith
  have hI : y ∈ Icc (xiStar / 4) (xiStar + r0 + xiStar / 4) := ⟨by linarith, by linarith [hx.2]⟩
  have hS : c0 * (xiStar / 4) ≤ langerTau x - langerTau y := by
    have := langerTau_sub_ge (a := xiStar / 4) (c := c0) (by linarith) hc0le (by linarith) hyx.le
    have h2 : c0 * (xiStar / 4) ≤ c0 * (x - y) := mul_le_mul_of_nonneg_left (by linarith) hc0.le
    linarith
  have hSp : 0 < langerTau x - langerTau y := lt_of_lt_of_le (by positivity) hS
  have hr1 : |deriv langerTau y| / (langerTau x - langerTau y) ≤ T1 := by
    calc |deriv langerTau y| / (langerTau x - langerTau y) ≤ M / (langerTau x - langerTau y) :=
          div_le_div_of_nonneg_right (hM y hI).1 hSp.le
      _ ≤ T1 := div_le_div_of_nonneg_left hM0 (by positivity) hS
  have hr2 : |deriv (deriv langerTau) y| / (langerTau x - langerTau y) ≤ T1 := by
    calc |deriv (deriv langerTau) y| / (langerTau x - langerTau y) ≤ M / (langerTau x - langerTau y) :=
          div_le_div_of_nonneg_right (hM y hI).2.1 hSp.le
      _ ≤ T1 := div_le_div_of_nonneg_left hM0 (by positivity) hS
  -- combH bounds
  have hz1 : 0 < x - y := by linarith
  have hz2 : 0 < x + y := by linarith
  have h1a : 1 / (x - y) ≤ 4 / xiStar := by
    rw [div_le_div_iff₀ hz1 hxs]; nlinarith
  have h1b : 1 / (x + y) ≤ 1 / xiStar := by
    rw [div_le_div_iff₀ hz2 hxs]; nlinarith [hx.1]
  have hH1a : combHDeriv (x - y) ≤ 4 / xiStar := by
    refine ((hHb _ hz1).2.1).trans ?_; rwa [inv_eq_one_div]
  have hH1b : combHDeriv (x + y) ≤ 1 / xiStar := by
    refine ((hHb _ hz2).2.1).trans ?_; rwa [inv_eq_one_div]
  have hH1ap := (hHb _ hz1).1
  have hH1bp := (hHb _ hz2).1
  have hH2a : |combHSecond (x - y)| ≤ CH * (4 / xiStar) ^ 2 := by
    refine ((hHb _ hz1).2.2.2.2).trans ?_
    have h5 : (1 / (x - y)) ^ 2 ≤ (4 / xiStar) ^ 2 := pow_le_pow_left₀ (by positivity) h1a 2
    have : CH / (x - y) ^ 2 = CH * (1 / (x - y)) ^ 2 := by field_simp
    rw [this]; exact mul_le_mul_of_nonneg_left h5 hCH.le
  have hH2b : |combHSecond (x + y)| ≤ CH * (1 / xiStar) ^ 2 := by
    refine ((hHb _ hz2).2.2.2.2).trans ?_
    have h5 : (1 / (x + y)) ^ 2 ≤ (1 / xiStar) ^ 2 := pow_le_pow_left₀ (by positivity) h1b 2
    have : CH / (x + y) ^ 2 = CH * (1 / (x + y)) ^ 2 := by field_simp
    rw [this]; exact mul_le_mul_of_nonneg_left h5 hCH.le
  have pa : 0 ≤ CH * (4 / xiStar) ^ 2 := mul_nonneg hCH.le (sq_nonneg _)
  have pb : 0 ≤ CH * (1 / xiStar) ^ 2 := mul_nonneg hCH.le (sq_nonneg _)
  have pc : 0 ≤ T1 ^ 2 := sq_nonneg _
  have pd : 0 ≤ 4 / xiStar := by positivity
  have pe : 0 ≤ 1 / xiStar := by positivity
  constructor
  · rw [deriv_langerK_lt hy0 hyx]
    have e1 : |deriv langerTau y / (langerTau x - langerTau y)| ≤ T1 := by
      rwa [abs_div, abs_of_pos hSp]
    have a1 := abs_le.1 e1
    rw [abs_le]
    constructor <;> linarith
  · rw [deriv2_langerK_lt hy0 hyx]
    have e : (deriv (deriv langerTau) y * (langerTau x - langerTau y) + deriv langerTau y ^ 2) /
        (langerTau x - langerTau y) ^ 2 =
        deriv (deriv langerTau) y / (langerTau x - langerTau y) +
          (deriv langerTau y / (langerTau x - langerTau y)) ^ 2 := by
      field_simp
    rw [e]
    have e1 : |deriv langerTau y / (langerTau x - langerTau y)| ≤ T1 := by
      rwa [abs_div, abs_of_pos hSp]
    have e2 : |deriv (deriv langerTau) y / (langerTau x - langerTau y)| ≤ T1 := by
      rwa [abs_div, abs_of_pos hSp]
    have e3 : |(deriv langerTau y / (langerTau x - langerTau y)) ^ 2| ≤ T1 ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) e1 2
    have a2 := abs_le.1 e2
    have a3 := abs_le.1 e3
    have a4 := abs_le.1 hH2a
    have a5 := abs_le.1 hH2b
    rw [abs_le]
    constructor <;> linarith

/-- Ratios `τ'(y)/(τ(y) - τ(x))`, `τ''(y)/(τ(y) - τ(x))` for `y ≥ x + δ`. -/
theorem langerTau_ratio_bounds (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ x ∈ langerX r0, ∀ y : ℝ, x + xiStar / 4 ≤ y →
      0 < langerTau y - langerTau x ∧
      |deriv langerTau y| / (langerTau y - langerTau x) ≤ CT / (1 + y) ∧
      |deriv (deriv langerTau) y| / (langerTau y - langerTau x) ≤ CT / (1 + y) ^ 2 ∧
      (|deriv langerTau y| / (langerTau y - langerTau x)) ^ 2 ≤ CT / (1 + y) ^ 2 := by
  have hxs := xiStar_pos
  obtain ⟨c0, hc0, hc0le⟩ := langerTau_deriv_ge_const_of (a := xiStar / 2) (by linarith)
  have hτr : 0 < langerTau (xiStar + r0) := langerTau_pos_of_gt (by linarith)
  obtain ⟨Y, hYx, hY⟩ := exists_langerTau_ge (2 * langerTau (xiStar + r0))
  set Y1 : ℝ := max Y (xiStar + 1) with hY1
  have hY1a : Y ≤ Y1 := le_max_left _ _
  have hY1b : xiStar + 1 ≤ Y1 := le_max_right _ _
  obtain ⟨Cl, hCl, hl⟩ := langerTau_large (r1 := 1) one_pos
  obtain ⟨M, hM⟩ := langerTau_deriv_bound_compact3 (a := xiStar / 2) (b := Y1) (by linarith)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (xiStar / 2) ⟨le_rfl, by linarith⟩).1
  set T : ℝ := M / (c0 * (xiStar / 4)) with hT
  have hT0 : 0 ≤ T := by positivity
  have hY1p : 0 < 1 + Y1 := by linarith
  refine ⟨2 * Cl + (2 * Cl) ^ 2 + T * (1 + Y1) ^ 2 + (T * (1 + Y1)) ^ 2, by positivity,
    fun x hx y hxy => ?_⟩
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith
  have hyp : 0 < 1 + y := by linarith
  have hCl0 : 0 ≤ Cl := hCl.le
  have hτ1p : 0 < deriv langerTau y := deriv_langerTau_pos hy0
  rcases le_total Y1 y with hy1 | hy1
  · -- tail `y ≥ Y₁`
    have hτy : 2 * langerTau (xiStar + r0) ≤ langerTau y := hY y (hY1a.trans hy1)
    have hτx : langerTau x ≤ langerTau (xiStar + r0) :=
      langerTau_strictMonoOn.monotoneOn (Set.mem_Ioi.2 hx0) (Set.mem_Ioi.2 (by linarith)) hx.2
    have hτyp : 0 < langerTau y := by linarith
    have hSτ : langerTau y / 2 ≤ langerTau y - langerTau x := by linarith
    have hS : 0 < langerTau y - langerTau x := by linarith
    obtain ⟨_, h1, h2⟩ := hl y (by linarith)
    have r1 : |deriv langerTau y| / (langerTau y - langerTau x) ≤ 2 * Cl / (1 + y) := by
      rw [abs_of_pos hτ1p, div_le_div_iff₀ hS hyp]
      rw [le_div_iff₀ hyp] at h1
      nlinarith [mul_le_mul_of_nonneg_left hSτ hCl0]
    have r2 : |deriv (deriv langerTau) y| / (langerTau y - langerTau x) ≤ 2 * Cl / (1 + y) ^ 2 := by
      rw [div_le_div_iff₀ hS (by positivity)]
      rw [le_div_iff₀ (by positivity)] at h2
      nlinarith [mul_le_mul_of_nonneg_left hSτ hCl0]
    have r3 : (|deriv langerTau y| / (langerTau y - langerTau x)) ^ 2 ≤ (2 * Cl) ^ 2 / (1 + y) ^ 2 := by
      rw [← div_pow]
      exact pow_le_pow_left₀ (div_nonneg (abs_nonneg _) hS.le) r1 2
    have c1 : 2 * Cl ≤ 2 * Cl + (2 * Cl) ^ 2 + T * (1 + Y1) ^ 2 + (T * (1 + Y1)) ^ 2 := by
      have : 0 ≤ T * (1 + Y1) ^ 2 := by positivity
      nlinarith [sq_nonneg (2 * Cl), sq_nonneg (T * (1 + Y1))]
    have c2 : (2 * Cl) ^ 2 ≤ 2 * Cl + (2 * Cl) ^ 2 + T * (1 + Y1) ^ 2 + (T * (1 + Y1)) ^ 2 := by
      have : 0 ≤ T * (1 + Y1) ^ 2 := by positivity
      nlinarith [sq_nonneg (2 * Cl), sq_nonneg (T * (1 + Y1))]
    refine ⟨hS, r1.trans (div_le_div_of_nonneg_right c1 hyp.le), ?_, ?_⟩
    · exact r2.trans (div_le_div_of_nonneg_right c1 (by positivity))
    · exact r3.trans (div_le_div_of_nonneg_right c2 (by positivity))
  · -- compact `x + δ ≤ y ≤ Y₁`
    have hxm : xiStar / 2 ≤ x := hx.1
    have hI : y ∈ Icc (xiStar / 2) Y1 := ⟨by linarith, hy1⟩
    have hS' : c0 * (xiStar / 4) ≤ langerTau y - langerTau x := by
      have := langerTau_sub_ge (a := xiStar / 2) (c := c0) (by linarith) hc0le hxm (by linarith : x ≤ y)
      have h2 : c0 * (xiStar / 4) ≤ c0 * (y - x) := mul_le_mul_of_nonneg_left (by linarith) hc0.le
      linarith
    have hS : 0 < langerTau y - langerTau x := lt_of_lt_of_le (by positivity) hS'
    have q1 : |deriv langerTau y| / (langerTau y - langerTau x) ≤ T :=
      (div_le_div_of_nonneg_right (hM y hI).1 hS.le).trans
        (div_le_div_of_nonneg_left hM0 (by positivity) hS')
    have q2 : |deriv (deriv langerTau) y| / (langerTau y - langerTau x) ≤ T :=
      (div_le_div_of_nonneg_right (hM y hI).2.1 hS.le).trans
        (div_le_div_of_nonneg_left hM0 (by positivity) hS')
    have hyY : 1 + y ≤ 1 + Y1 := by linarith
    have t1 : T ≤ T * (1 + Y1) / (1 + y) := by
      rw [le_div_iff₀ hyp]; exact mul_le_mul_of_nonneg_left hyY hT0
    have t2 : T ≤ T * (1 + Y1) ^ 2 / (1 + y) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : (1 + y) ^ 2 ≤ (1 + Y1) ^ 2 := pow_le_pow_left₀ hyp.le hyY 2
      exact mul_le_mul_of_nonneg_left this hT0
    have t3 : T ^ 2 ≤ (T * (1 + Y1)) ^ 2 / (1 + y) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : (1 + y) ^ 2 ≤ (1 + Y1) ^ 2 := pow_le_pow_left₀ hyp.le hyY 2
      calc T ^ 2 * (1 + y) ^ 2 ≤ T ^ 2 * (1 + Y1) ^ 2 := mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = (T * (1 + Y1)) ^ 2 := by ring
    have c1 : T * (1 + Y1) ≤ 2 * Cl + (2 * Cl) ^ 2 + T * (1 + Y1) ^ 2 + (T * (1 + Y1)) ^ 2 := by
      have h0 : T * (1 + Y1) ≤ T * (1 + Y1) ^ 2 := by
        have : (1 : ℝ) ≤ 1 + Y1 := by linarith
        nlinarith [mul_nonneg hT0 (by linarith : (0 : ℝ) ≤ Y1)]
      nlinarith [sq_nonneg (2 * Cl), sq_nonneg (T * (1 + Y1))]
    have c2 : T * (1 + Y1) ^ 2 ≤ 2 * Cl + (2 * Cl) ^ 2 + T * (1 + Y1) ^ 2 + (T * (1 + Y1)) ^ 2 := by
      have h2 : 0 ≤ 2 * Cl := by linarith
      have h3 : 0 ≤ (2 * Cl) ^ 2 := sq_nonneg _
      have h4 : 0 ≤ (T * (1 + Y1)) ^ 2 := sq_nonneg _
      linarith
    have c3 : (T * (1 + Y1)) ^ 2 ≤ 2 * Cl + (2 * Cl) ^ 2 + T * (1 + Y1) ^ 2 + (T * (1 + Y1)) ^ 2 := by
      have h1 : 0 ≤ T * (1 + Y1) ^ 2 := by positivity
      have h2 : 0 ≤ 2 * Cl := by linarith
      have h3 : 0 ≤ (2 * Cl) ^ 2 := sq_nonneg _
      linarith
    have q3 : (|deriv langerTau y| / (langerTau y - langerTau x)) ^ 2 ≤ T ^ 2 :=
      pow_le_pow_left₀ (div_nonneg (abs_nonneg _) hS.le) q1 2
    refine ⟨hS, q1.trans (t1.trans (div_le_div_of_nonneg_right c1 hyp.le)), ?_, ?_⟩
    · exact q2.trans (t2.trans (div_le_div_of_nonneg_right c2 (by positivity)))
    · exact q3.trans (t3.trans (div_le_div_of_nonneg_right c3 (by positivity)))

/-- Above the diagonal: `y ≥ x + δ`. -/
theorem langerK_deriv_bounds_up (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ C : ℝ, ∀ x ∈ langerX r0, ∀ y : ℝ, x + xiStar / 4 ≤ y →
      |deriv (langerK x) y| ≤ C / (1 + y) ∧ |deriv (deriv (langerK x)) y| ≤ C / (1 + y) ^ 2 := by
  have hxs := xiStar_pos
  obtain ⟨CT, hCT, hR⟩ := langerTau_ratio_bounds r0 hr0
  obtain ⟨CH, hCH, hHb, _⟩ := combH_bounds
  set A0 : ℝ := 1 + (1 + xiStar + r0) / (xiStar / 4) with hA0
  have hA0p : 0 < A0 := by positivity
  refine ⟨2 * A0 + CT + 2 * (CH * A0 ^ 2) + 2 * CT, fun x hx y hxy => ?_⟩
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith
  have hyp : 0 < 1 + y := by linarith
  have hxy' : x < y := by linarith
  obtain ⟨hS, r1, r2, r3⟩ := hR x hx y hxy
  have hz1 : 0 < y - x := by linarith
  have hz2 : 0 < x + y := by linarith
  -- 1/(y-x) ≤ A0/(1+y)
  have hinv : 1 / (y - x) ≤ A0 / (1 + y) := by
    refine (inv_le_of_ge (by positivity) hx0 hxy).trans ?_
    apply div_le_div_of_nonneg_right _ hyp.le
    rw [hA0]
    have : (1 + x) / (xiStar / 4) ≤ (1 + xiStar + r0) / (xiStar / 4) :=
      div_le_div_of_nonneg_right (by linarith [hx.2]) (by positivity)
    linarith
  have hinv2 : 1 / (x + y) ≤ A0 / (1 + y) := by
    refine le_trans ?_ hinv
    rw [div_le_div_iff₀ hz2 hz1]; linarith
  have hH1a : combHDeriv (y - x) ≤ A0 / (1 + y) := ((hHb _ hz1).2.1).trans (by rwa [inv_eq_one_div])
  have hH1b : combHDeriv (x + y) ≤ A0 / (1 + y) := ((hHb _ hz2).2.1).trans (by rwa [inv_eq_one_div])
  have hH1ap := (hHb _ hz1).1
  have hH1bp := (hHb _ hz2).1
  have hH2a : |combHSecond (y - x)| ≤ CH * A0 ^ 2 / (1 + y) ^ 2 := by
    refine ((hHb _ hz1).2.2.2.2).trans ?_
    have h5 : (1 / (y - x)) ^ 2 ≤ (A0 / (1 + y)) ^ 2 := pow_le_pow_left₀ (by positivity) hinv 2
    have : CH / (y - x) ^ 2 = CH * (1 / (y - x)) ^ 2 := by field_simp
    rw [this]
    calc CH * (1 / (y - x)) ^ 2 ≤ CH * (A0 / (1 + y)) ^ 2 := mul_le_mul_of_nonneg_left h5 hCH.le
      _ = CH * A0 ^ 2 / (1 + y) ^ 2 := by rw [div_pow]; ring
  have hH2b : |combHSecond (x + y)| ≤ CH * A0 ^ 2 / (1 + y) ^ 2 := by
    refine ((hHb _ hz2).2.2.2.2).trans ?_
    have h5 : (1 / (x + y)) ^ 2 ≤ (A0 / (1 + y)) ^ 2 := pow_le_pow_left₀ (by positivity) hinv2 2
    have : CH / (x + y) ^ 2 = CH * (1 / (x + y)) ^ 2 := by field_simp
    rw [this]
    calc CH * (1 / (x + y)) ^ 2 ≤ CH * (A0 / (1 + y)) ^ 2 := mul_le_mul_of_nonneg_left h5 hCH.le
      _ = CH * A0 ^ 2 / (1 + y) ^ 2 := by rw [div_pow]; ring
  have hyp2 : 0 < (1 + y) ^ 2 := by positivity
  constructor
  · rw [deriv_langerK_gt hx0 hxy']
    have e1 : |deriv langerTau y / (langerTau y - langerTau x)| ≤ CT / (1 + y) := by
      rwa [abs_div, abs_of_pos hS]
    have a1 := abs_le.1 e1
    have b1 : 0 ≤ A0 / (1 + y) := by positivity
    have hsum : 2 * A0 / (1 + y) + CT / (1 + y) ≤
        (2 * A0 + CT + 2 * (CH * A0 ^ 2) + 2 * CT) / (1 + y) := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hyp.le
      have : 0 ≤ 2 * (CH * A0 ^ 2) + 2 * CT := by positivity
      linarith
    have e2 : 2 * A0 / (1 + y) = A0 / (1 + y) + A0 / (1 + y) := by ring
    rw [abs_le]
    constructor <;> linarith
  · rw [deriv2_langerK_gt hx0 hxy']
    have e : (deriv (deriv langerTau) y * (langerTau y - langerTau x) - deriv langerTau y ^ 2) /
        (langerTau y - langerTau x) ^ 2 =
        deriv (deriv langerTau) y / (langerTau y - langerTau x) -
          (deriv langerTau y / (langerTau y - langerTau x)) ^ 2 := by
      field_simp
    rw [e]
    have e2 : |deriv (deriv langerTau) y / (langerTau y - langerTau x)| ≤ CT / (1 + y) ^ 2 := by
      rwa [abs_div, abs_of_pos hS]
    have e3 : |(deriv langerTau y / (langerTau y - langerTau x)) ^ 2| ≤ CT / (1 + y) ^ 2 := by
      rw [abs_pow, abs_div, abs_of_pos hS]; exact r3
    have a2 := abs_le.1 e2
    have a3 := abs_le.1 e3
    have a4 := abs_le.1 hH2a
    have a5 := abs_le.1 hH2b
    have hsum : 2 * (CH * A0 ^ 2) / (1 + y) ^ 2 + CT / (1 + y) ^ 2 + CT / (1 + y) ^ 2 ≤
        (2 * A0 + CT + 2 * (CH * A0 ^ 2) + 2 * CT) / (1 + y) ^ 2 := by
      rw [← add_div, ← add_div]
      apply div_le_div_of_nonneg_right _ hyp2.le
      have : 0 ≤ 2 * A0 := by positivity
      linarith
    have e4 : 2 * (CH * A0 ^ 2) / (1 + y) ^ 2 =
        CH * A0 ^ 2 / (1 + y) ^ 2 + CH * A0 ^ 2 / (1 + y) ^ 2 := by ring
    rw [abs_le]
    constructor <;> linarith

/-- **`(F2)`**: for every `r₀ > 0` there is `C` such that for `x ∈ X = [ξ_*/2, ξ_* + r₀]` and `y ≥ ξ_*`,
`|∂_y K(x,y)| ≤ C/(1+y)` and `|∂_y² K(x,y)| ≤ C/(1+y)²`. -/
theorem langerK_deriv_bounds (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ langerX r0, ∀ y : ℝ, xiStar ≤ y →
      |deriv (langerK x) y| ≤ C / (1 + y) ∧ |deriv (deriv (langerK x)) y| ≤ C / (1 + y) ^ 2 := by
  have hxs := xiStar_pos
  obtain ⟨Cn, hn⟩ := langerK_deriv_bounds_near r0 hr0
  obtain ⟨Cd, hd⟩ := langerK_deriv_bounds_down r0 hr0
  obtain ⟨Cu, hu⟩ := langerK_deriv_bounds_up r0 hr0
  set Ym : ℝ := 1 + xiStar + r0 + xiStar / 4 with hYm
  have hYm1 : 1 ≤ Ym := by linarith
  set B : ℝ := |Cn| + |Cd| with hB
  refine ⟨B * Ym ^ 2 + |Cu| + 1, by positivity, fun x hx y hy => ?_⟩
  have hyp : 0 < 1 + y := by linarith
  have hx0 : 0 < x := by linarith [hx.1]
  have hB0 : 0 ≤ B := by positivity
  -- conversion of a bounded quantity to the `(1+y)^{-j}` scale when `1 + y ≤ Ym`
  have conv : ∀ {v : ℝ} {b : ℝ}, 0 ≤ b → |v| ≤ b → 1 + y ≤ Ym →
      |v| ≤ (b * Ym) / (1 + y) ∧ |v| ≤ (b * Ym ^ 2) / (1 + y) ^ 2 := by
    intro v b hb hv hYy
    constructor
    · rw [le_div_iff₀ hyp]
      exact mul_le_mul hv hYy hyp.le hb
    · rw [le_div_iff₀ (pow_pos hyp 2)]
      exact mul_le_mul hv (pow_le_pow_left₀ hyp.le hYy 2) (pow_pos hyp 2).le hb
  have hbig : B * Ym ^ 2 + |Cu| + 1 ≥ 0 := by positivity
  have aux : ∀ a : ℝ, 0 ≤ a → a ≤ B → a * Ym ≤ B * Ym ^ 2 := by
    intro a ha haB
    have h1 : a * Ym ≤ B * Ym := mul_le_mul_of_nonneg_right haB (by linarith)
    have h2 : B * Ym ≤ B * Ym ^ 2 := by
      have : Ym ≤ Ym ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this hB0
    linarith
  by_cases hnear : |y - x| < xiStar / 4
  · obtain ⟨h1, h2⟩ := hn x hx y hnear
    have hYy : 1 + y ≤ Ym := by
      have := abs_lt.1 hnear; linarith [hx.2]
    have hb : 0 ≤ |Cn| := abs_nonneg _
    obtain ⟨c1, _⟩ := conv hb (h1.trans (le_abs_self _)) hYy
    obtain ⟨_, c2⟩ := conv hb (h2.trans (le_abs_self _)) hYy
    constructor
    · refine c1.trans ?_
      apply div_le_div_of_nonneg_right _ hyp.le
      have : |Cn| * Ym ≤ B * Ym ^ 2 :=
        aux _ (abs_nonneg _) (by rw [hB]; linarith [abs_nonneg Cd])
      linarith [abs_nonneg Cu]
    · refine c2.trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : |Cn| ≤ B := by rw [hB]; linarith [abs_nonneg Cd]
      have := mul_le_mul_of_nonneg_right this (by positivity : 0 ≤ Ym ^ 2)
      linarith [abs_nonneg Cu]
  · push Not at hnear
    rcases le_abs'.1 hnear with hle | hge
    · -- y ≤ x - δ
      obtain ⟨h1, h2⟩ := hd x hx y hy (by linarith)
      have hYy : 1 + y ≤ Ym := by linarith [hx.2]
      have hb : 0 ≤ |Cd| := abs_nonneg _
      obtain ⟨c1, _⟩ := conv hb (h1.trans (le_abs_self _)) hYy
      obtain ⟨_, c2⟩ := conv hb (h2.trans (le_abs_self _)) hYy
      constructor
      · refine c1.trans ?_
        apply div_le_div_of_nonneg_right _ hyp.le
        have : |Cd| * Ym ≤ B * Ym ^ 2 :=
          aux _ (abs_nonneg _) (by rw [hB]; linarith [abs_nonneg Cn])
        linarith [abs_nonneg Cu]
      · refine c2.trans ?_
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : |Cd| ≤ B := by rw [hB]; linarith [abs_nonneg Cn]
        have := mul_le_mul_of_nonneg_right this (by positivity : 0 ≤ Ym ^ 2)
        linarith [abs_nonneg Cu]
    · -- y ≥ x + δ
      obtain ⟨h1, h2⟩ := hu x hx y (by linarith)
      constructor
      · refine h1.trans (div_le_div_of_nonneg_right ?_ hyp.le)
        have := le_abs_self Cu
        have : 0 ≤ B * Ym ^ 2 := by positivity
        linarith
      · refine h2.trans (div_le_div_of_nonneg_right ?_ (by positivity))
        have := le_abs_self Cu
        have : 0 ≤ B * Ym ^ 2 := by positivity
        linarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.langerK_deriv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerK_deriv_bounds

end FormalResearch.ModularBootstrap.Upper.Ramped
