module

public import FormalResearch.ModularBootstrap.FiveTerm.CombFunctional

/-!
# The exact minimum of the comb functional `𝒥` (FIVE-0; `cts:main`, `ctu:common-functional`)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Theorem C4 (`cts:main`):
`c_0^* = min_{F ∈ H_adm(Ω)} 𝒥[F] = α_tip g₁`, attained by `F_* = (1 + z²)/G_outer`.

Over an outer-function datum `G` (`OuterDatum W K g₁ G`; `g₁ = G'(0)` free), with `fStar G z = (1+z²)/G z`:

* `fStar_hAdm`: `fStar G ∈ HAdm` with `F'(0) = -g₁` (jet algebra, `|1/G| ≤ 2` near `0`, the lower bounds on `|G|`
  at `1` and `±i`);
* `comb_attained`: `𝒥[fStar G] = α_tip g₁` (the defect of `H = 1+z²` vanishes: `B_H = (1-y²)(1+q) ≥ H(iy) > 0`);
* `comb_minimum`: `α_tip g₁` is the least value of `𝒥` over `H_adm` (`IsLeast`), so `c_0^* = c0StarOf g₁`.

The existence of the outer function (`OuterDatum` for the Virasoro weights) is not in this file.  All results are
proved unconditionally.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- The minimiser `F_* = (1+z²)/G_outer` (`cts:main`). -/
noncomputable def fStar (G : ℂ → ℂ) (z : ℂ) : ℂ := (1 + z ^ 2) / G z

section

variable {G : ℂ → ℂ} {g1 : ℝ} {W : ℝ → ℝ} {K : ℝ → ℂ}

lemma fStar_jet (hG : OuterDatum W K g1 G) :
    ∃ C r : ℝ, 0 < r ∧ ∀ z ∈ closure halfDisc, ‖z‖ < r →
      ‖fStar G z - 1 - ((-g1 : ℝ) : ℂ) * z‖ ≤ C * ‖z‖ ^ 2 := by
  obtain ⟨C, r, hr, hj⟩ := hG.jet
  have hpos : 0 < 1 + |g1| + |C| := by positivity
  set δ : ℝ := 1 / (2 * (1 + |g1| + |C|)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]
    nlinarith only [abs_nonneg g1, abs_nonneg C]
  have hδm : (|g1| + |C|) * δ ≤ 1 / 2 := by
    rw [hδ, mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith only [abs_nonneg g1, abs_nonneg C]
  refine ⟨2 * (1 + g1 ^ 2 + |C| + |g1| * |C|), min r δ, lt_min hr hδ0, fun z hz hzr => ?_⟩
  have hzr' : ‖z‖ < r := lt_of_lt_of_le hzr (min_le_left _ _)
  have hzδ : ‖z‖ < δ := lt_of_lt_of_le hzr (min_le_right _ _)
  set a := ‖z‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg z
  have ha1 : a ≤ 1 := by linarith
  set e := G z - 1 - g1 * z with he
  have he_le : ‖e‖ ≤ |C| * a ^ 2 :=
    le_trans (hj z hz hzr') (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg a))
  have hGlb : 1 / 2 ≤ ‖G z‖ := by
    have h1 : ‖(1 : ℂ)‖ ≤ ‖G z‖ + ‖(g1 : ℂ) * z + e‖ := by
      have : (1 : ℂ) = G z - ((g1 : ℂ) * z + e) := by rw [he]; ring
      calc ‖(1 : ℂ)‖ = ‖G z - ((g1 : ℂ) * z + e)‖ := by rw [← this]
        _ ≤ ‖G z‖ + ‖(g1 : ℂ) * z + e‖ := norm_sub_le _ _
    have h2 : ‖(g1 : ℂ) * z + e‖ ≤ |g1| * a + |C| * a ^ 2 := by
      calc ‖(g1 : ℂ) * z + e‖ ≤ ‖(g1 : ℂ) * z‖ + ‖e‖ := norm_add_le _ _
        _ ≤ |g1| * a + |C| * a ^ 2 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; gcongr
    have h3 : |g1| * a + |C| * a ^ 2 ≤ (|g1| + |C|) * δ := by
      have : a ^ 2 ≤ a := by nlinarith only [ha0, ha1]
      nlinarith only [this, hzδ, abs_nonneg g1, abs_nonneg C, ha0]
    rw [norm_one] at h1
    linarith only [h1, h2, h3, hδm]
  have hGne : G z ≠ 0 := by
    intro h; rw [h, norm_zero] at hGlb; linarith
  have hid : fStar G z - 1 - ((-g1 : ℝ) : ℂ) * z =
      (z ^ 2 * (1 + (g1 : ℂ) ^ 2) - e + g1 * z * e) / G z := by
    unfold fStar
    rw [eq_div_iff hGne, he]
    field_simp
    push_cast
    ring
  have hN : ‖z ^ 2 * (1 + (g1 : ℂ) ^ 2) - e + g1 * z * e‖ ≤
      (1 + g1 ^ 2 + |C| + |g1| * |C|) * a ^ 2 := by
    have h1 : ‖z ^ 2 * (1 + (g1 : ℂ) ^ 2)‖ = a ^ 2 * (1 + g1 ^ 2) := by
      have : (1 + (g1 : ℂ) ^ 2) = ((1 + g1 ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : ‖(g1 : ℂ) * z * e‖ ≤ |g1| * a * (|C| * a ^ 2) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
    calc ‖z ^ 2 * (1 + (g1 : ℂ) ^ 2) - e + g1 * z * e‖
        ≤ ‖z ^ 2 * (1 + (g1 : ℂ) ^ 2) - e‖ + ‖(g1 : ℂ) * z * e‖ := norm_add_le _ _
      _ ≤ (‖z ^ 2 * (1 + (g1 : ℂ) ^ 2)‖ + ‖e‖) + ‖(g1 : ℂ) * z * e‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ (a ^ 2 * (1 + g1 ^ 2) + |C| * a ^ 2) + |g1| * a * (|C| * a ^ 2) := by
          rw [h1]; gcongr
      _ ≤ (1 + g1 ^ 2 + |C| + |g1| * |C|) * a ^ 2 := by
          have h3 : |g1| * |C| * a ^ 3 ≤ |g1| * |C| * a ^ 2 := by
            have : a ^ 3 ≤ a ^ 2 := by nlinarith only [ha0, ha1, sq_nonneg a]
            exact mul_le_mul_of_nonneg_left this (by positivity)
          nlinarith only [h3]
  rw [hid, norm_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hGlb)]
  have hN0 : 0 ≤ (1 + g1 ^ 2 + |C| + |g1| * |C|) * a ^ 2 := by positivity
  nlinarith only [hN, hGlb, hN0]

/-- `fStar G ∈ H_adm(Ω)` with `F_*'(0) = -g₁`. -/
theorem fStar_hAdm (hG : OuterDatum W K g1 G) : HAdm (fStar G) (-g1) where
  diff := by
    refine DifferentiableOn.div (by fun_prop) hG.diff (fun z hz => ?_)
    exact hG.ne_zero z ⟨subset_closure hz, not_mem_singPts_of_halfDisc hz⟩
  cont := ContinuousOn.div (by fun_prop) hG.cont (fun z hz => hG.ne_zero z hz)
  conj z hz := by simp only [fStar, map_div₀, hG.conj z hz, map_add, map_one, map_pow]
  jet := fStar_jet hG
  near_one := by
    obtain ⟨C, c, r, hc, hr, h⟩ := hG.near_one
    refine ⟨2 / c, r, hr, fun z hz hz1 hzr => ?_⟩
    have hs : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz1)
    have hlb := (h z hz hz1 hzr).1
    have hGpos : 0 < ‖G z‖ := lt_of_lt_of_le (by positivity) hlb
    unfold fStar
    rw [norm_div, div_mul_eq_mul_div, div_le_iff₀ hGpos]
    have h2 := norm_one_add_sq_le_two hz
    have hsp : 0 < ‖z - 1‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
    calc ‖1 + z ^ 2‖ * ‖z - 1‖ ^ (1 / 2 : ℝ) ≤ 2 * ‖z - 1‖ ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right h2 hsp.le
      _ = 2 / c * (c * ‖z - 1‖ ^ (1 / 2 : ℝ)) := by field_simp
      _ ≤ 2 / c * ‖G z‖ := by gcongr
  near_I := by
    obtain ⟨C, c, r, hc, hr, h⟩ := hG.near_I
    refine ⟨1 / c, r, 1, hr, by norm_num, fun z hz h1 h2 hzr => ?_⟩
    have hlb := (h z hz h1 h2 hzr).1
    unfold fStar
    rw [norm_div, Real.rpow_one, one_div, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hc hlb

/-- `edgeSum` of `1 + z²`: `B = (1 - y²) + 2 Re(e^{iψ}) · 2y²/(1+y²)`. -/
lemma edgeSum_one_add_sq (y : ℝ) :
    edgeSum (fun z => 1 + z ^ 2) y =
      (((1 - y ^ 2) + 2 * ((1 - y ^ 2) / (1 + y ^ 2)) * (2 * y ^ 2 / (1 + y ^ 2)) : ℝ) : ℂ) := by
  unfold edgeSum
  beta_reduce
  have h1 := wPt_mul_conj y
  have h2 := Complex.add_conj (wPt y)
  rw [re_wPt] at h2
  have hI : (1 : ℂ) + (Complex.I * (y : ℂ)) ^ 2 = ((1 - y ^ 2 : ℝ) : ℂ) := by
    push_cast; rw [mul_pow, Complex.I_sq]; ring
  rw [hI]
  push_cast at h2 ⊢
  linear_combination (2 * (y : ℂ) ^ 2 / (1 + (y : ℂ) ^ 2) * starRingEnd ℂ (wPt y)) * h1 +
    (2 * (y : ℂ) ^ 2 / (1 + (y : ℂ) ^ 2)) * h2

lemma defectNum_one_add_sq {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    defectNum (fun z => 1 + z ^ 2) y = 0 := by
  unfold defectNum
  rw [edgeSum_one_add_sq]
  have hy2 : y ^ 2 < 1 := by nlinarith only [hy0, hy1]
  have hpos : 0 < 1 + y ^ 2 := by positivity
  set B : ℝ := (1 - y ^ 2) + 2 * ((1 - y ^ 2) / (1 + y ^ 2)) * (2 * y ^ 2 / (1 + y ^ 2)) with hB
  have hB1 : 1 - y ^ 2 ≤ B := by
    have : 0 ≤ 2 * ((1 - y ^ 2) / (1 + y ^ 2)) * (2 * y ^ 2 / (1 + y ^ 2)) := by
      have : 0 ≤ (1 - y ^ 2) / (1 + y ^ 2) := div_nonneg (by linarith) hpos.le
      positivity
    rw [hB]; linarith only [this]
  have hB0 : 0 ≤ B := le_trans (by linarith) hB1
  have hH : ‖(fun z : ℂ => 1 + z ^ 2) (Complex.I * (y : ℂ))‖ = 1 - y ^ 2 := by
    have : (1 : ℂ) + (Complex.I * (y : ℂ)) ^ 2 = ((1 - y ^ 2 : ℝ) : ℂ) := by
      push_cast; rw [mul_pow, Complex.I_sq]; ring
    simp only [this, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by linarith)
  rw [hH, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB0, Complex.ofReal_re,
    max_eq_right hB1, sub_self]

/-- `defectInt` of `F·G` with `F = fStar G` vanishes on the slit/arc. -/
lemma defectInt_fStar_mul (hG : OuterDatum W K g1 G) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    defectInt (fun z => fStar G z * G z) y = 0 := by
  obtain ⟨hy0, hy1⟩ := hy
  have hfG : ∀ z ∈ closure halfDisc \ singPts, fStar G z * G z = 1 + z ^ 2 := by
    intro z hz
    unfold fStar
    exact div_mul_cancel₀ _ (hG.ne_zero z hz)
  have h1 := hfG _ (I_mul_mem_cont hy0 hy1)
  have h2 := hfG _ (wbar_mem_cont hy0 hy1)
  have hes : edgeSum (fun z => fStar G z * G z) y = edgeSum (fun z => 1 + z ^ 2) y := by
    unfold edgeSum
    beta_reduce
    rw [h1, h2]
  have := defectNum_one_add_sq hy0 hy1
  unfold defectNum at this
  unfold defectInt defectNum
  beta_reduce at this ⊢
  rw [hes, h1]
  rw [this, zero_div]

/-- **Attainment** (`cts:main`): `𝒥[F_*] = α_tip g₁`. -/
theorem comb_attained (hG : OuterDatum W K g1 G) : combJ W K (fStar G) = alphaTip * g1 := by
  obtain ⟨_, h⟩ := comb_defect_identity (fStar_hAdm hG) hG
  rw [h, setIntegral_congr_fun measurableSet_Ioo (fun y hy => defectInt_fStar_mul hG hy)]
  simp

/-- **`cts:main`**: over an outer-function datum `G` with `G'(0) = g₁`, the minimum of the comb functional `𝒥` over
`H_adm(Ω)` is `α_tip g₁`, attained at `F_* = (1+z²)/G`. -/
theorem comb_minimum (hG : OuterDatum W K g1 G) :
    IsLeast {x : ℝ | ∃ (F : ℂ → ℂ) (c1 : ℝ), HAdm F c1 ∧ combJ W K F = x} (alphaTip * g1) :=
  ⟨⟨fStar G, -g1, fStar_hAdm hG, comb_attained hG⟩, by
    rintro x ⟨F, c1, hF, rfl⟩
    exact comb_lower_bound hF hG⟩

/-- In the jet-parametrised constant: the minimum is `c0StarOf g₁`. -/
theorem comb_minimum_c0StarOf (hG : OuterDatum W K g1 G) :
    IsLeast {x : ℝ | ∃ (F : ℂ → ℂ) (c1 : ℝ), HAdm F c1 ∧ combJ W K F = x} (c0StarOf g1) :=
  comb_minimum hG

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.comb_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.comb_minimum

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.fStar_hAdm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.fStar_hAdm
