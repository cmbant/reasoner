module

public import FormalResearch.ModularBootstrap.FixedWeightBand.TruncationWDp

/-!
# Lemma Z at weight `w` (`vlo:Z`): decomposition and the inner-scale witness

Lemma Z (`lower_o1_two_edge.tex`, `vlo:Z`) at every fixed-weight problem `prob`: an interior bound on the
strip multiplier `tildeWW prob.w c' g` on the saddle sector implies the Airy envelope
`YVEnvBound (psiTilde prob c' g) c' R (C_B * Λ)` (`YVEnvBound` is weight-free).

## Decomposition into modules (all in `FixedWeightBand/`)
* `TruncationWDefs`: `dpThr`, `mellinDensityIntegrandW`, `truncatedMellinPW`, `cardyVC_inner_bound`
  (complex weight bound on the chart disc `|b - ξ_*| <= r_1`), the Stirling^(w) prefactor bound
  `norm_stirlingPrefW_le`, the pointwise factorisations `mellinDensityIntegrandW_strip_eq` /
  `mellinDensityIntegrandW_crude_eq`, the Stirling threshold `stirThr`.
* `TruncationWAnalytic`, `TruncationWMidline`, `TruncationWReal`, `TruncationWContour`, `TruncationWHalfPlane`,
  `TruncationWDp`: Lemma D' (`vlo:Dp`, `lemma_Dp_W`) with its inputs (holomorphy, conjugation symmetry,
  midline tail, real-diameter bound, saddle-contour deformation, inner-disc bound).
* `TruncationWZWitness` (this file): elementary Gaussian and exponential helpers, the packaged witness
  `ZWitnessW D` (Lemma D', saddle data of Lemma S6, `tildeWW` and Mellin bounds of Lemmas S4/S2 at weight `w`,
  `cardyVC` bound) and the scale cap `zScaleCapW D`.
* `TruncationWZSeg`: per-segment bound along the saddle contour (windowed strip multiplier near the saddle,
  uniform tails elsewhere); new at weight `w` are the Stirling^(w) prefactor bound on the segment and `mellinMGW`.
* `TruncationWZCombine`: assembly of the segment bound and Lemma D' into the envelope inequality.
* `TruncationWZ`: `lemma_Z_W`.

New relative to the Virasoro Lemma Z: the prefactor `(3 ω / (2π b²))^{(w-1)/2}` (bounded on the contour by
`C_Γ` and `|b| ≥ ξ_*/2`), the Stirling threshold `stirThr w / c_Γ` replacing `48 / c_Γ`, the Mellin line
`Re z = w/2`, and the use of `cardyVC` and `psiTilde prob`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special
open FormalResearch.ModularBootstrap.Chart
open FormalResearch.ModularBootstrap.ChartGeometry
open FormalResearch.ModularBootstrap.ComplexBessel
open FormalResearch.ModularBootstrap.StripMultiplier
open FormalResearch.ModularBootstrap.Mellin
open FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Contour
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.WeightAxioms

/-! ### 1. Elementary polar, Gaussian-window, and exponential helpers -/

lemma cpow_half_re_eq_sqrt_mul_sinW {u : ℂ} (hu : u ≠ 0) :
    (u ^ (1 / 2 : ℂ)).re = Real.sqrt ‖u‖ * Real.sin ((Real.pi - u.arg) / 2) := by
  have hn_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  rw [Complex.cpow_def_of_ne_zero hu, Complex.exp_re]
  have hre : (Complex.log u * (1 / 2 : ℂ)).re = Real.log ‖u‖ / 2 := by
    rw [Complex.mul_re, Complex.log_re, Complex.log_im]
    norm_num; ring
  have him : (Complex.log u * (1 / 2 : ℂ)).im = u.arg / 2 := by
    rw [Complex.mul_im, Complex.log_re, Complex.log_im]
    norm_num; ring
  have hexp_sqrt : Real.exp (Real.log ‖u‖ / 2) = Real.sqrt ‖u‖ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn_pos]
    congr 1; ring
  have hcos_sin : Real.cos (u.arg / 2) = Real.sin ((Real.pi - u.arg) / 2) := by
    have heq : u.arg / 2 = Real.pi / 2 - (Real.pi - u.arg) / 2 := by ring
    rw [heq, Real.cos_pi_div_two_sub]
  rw [hre, him, hexp_sqrt, hcos_sin]

lemma exp_neg_le_inv_one_addW {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ (1 + x)⁻¹ := by
  have h1 : 1 + x ≤ Real.exp x := by
    have h := Real.add_one_le_exp x
    linarith only [h]
  rw [Real.exp_neg]
  exact inv_anti₀ (by linarith only [hx]) h1

lemma integral_exp_neg_mul_sq_leW {α L : ℝ} (hα : 0 < α) (hL : 0 ≤ L) :
    ∫ t in (0 : ℝ)..L, Real.exp (-α * t ^ 2) ≤ (Real.pi / 2) / Real.sqrt α := by
  set s : ℝ := Real.sqrt α
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hα
  have hs_sq : s ^ 2 = α := Real.sq_sqrt hα.le
  set F : ℝ → ℝ := fun t => s⁻¹ * Real.arctan (s * t)
  have hF_deriv : ∀ t ∈ uIcc 0 L, HasDerivAt F ((1 + α * t ^ 2)⁻¹) t := fun t _ => by
    have h1 : HasDerivAt (fun x : ℝ => s * x) s t := by
      simpa using (hasDerivAt_id t).const_mul s
    have h2 := (Real.hasDerivAt_arctan (s * t)).comp t h1
    refine (h2.const_mul s⁻¹).congr_deriv ?_
    have hden : 1 + (s * t) ^ 2 = 1 + α * t ^ 2 := by rw [mul_pow, hs_sq]
    rw [hden]
    field_simp [hs_pos.ne']
  have hcont_r : ContinuousOn (fun t : ℝ => (1 + α * t ^ 2)⁻¹) (Icc 0 L) :=
    (continuousOn_const.add (continuousOn_const.mul (continuousOn_id.pow 2))).inv₀
      fun t _ => (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hα.le (sq_nonneg t))).ne'
  have hcont_l : ContinuousOn (fun t : ℝ => Real.exp (-α * t ^ 2)) (Icc 0 L) := by fun_prop
  have hmono : ∫ t in (0 : ℝ)..L, Real.exp (-α * t ^ 2) ≤
      ∫ t in (0 : ℝ)..L, (1 + α * t ^ 2)⁻¹ := by
    refine intervalIntegral.integral_mono_on hL (hcont_l.intervalIntegrable_of_Icc hL)
      (hcont_r.intervalIntegrable_of_Icc hL) fun t _ => ?_
    rw [show -α * t ^ 2 = -(α * t ^ 2) by ring]
    exact exp_neg_le_inv_one_addW (by positivity)
  have hftc : ∫ t in (0 : ℝ)..L, (1 + α * t ^ 2)⁻¹ = F L - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv (hcont_r.intervalIntegrable_of_Icc hL)
  have hF0 : F 0 = 0 := by simp [F]
  have hFL : F L ≤ (Real.pi / 2) / s := by
    dsimp [F]
    have harc : Real.arctan (s * L) ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two _).le
    calc s⁻¹ * Real.arctan (s * L) ≤ s⁻¹ * (Real.pi / 2) :=
          mul_le_mul_of_nonneg_left harc (inv_nonneg.mpr hs_pos.le)
      _ = (Real.pi / 2) / s := by ring
  linarith only [hmono, hftc, hF0, hFL]

lemma integral_exp_neg_mul_sub_sq_leW {α L : ℝ} (hα : 0 < α) (hL : 0 ≤ L) :
    ∫ t in (0 : ℝ)..L, Real.exp (-α * (L - t) ^ 2) ≤ (Real.pi / 2) / Real.sqrt α := by
  have hsub := intervalIntegral.integral_comp_sub_left (fun u : ℝ => Real.exp (-α * u ^ 2)) L
    (a := 0) (b := L)
  rw [sub_zero, sub_self] at hsub
  rw [hsub]
  exact integral_exp_neg_mul_sq_leW hα hL

lemma rpow_four_thirds_mul_exp_neg_leW {κ c' : ℝ} (hκ : 0 < κ) (hc' : 1 ≤ c') :
    c' ^ (4 / 3 : ℝ) * Real.exp (-κ * c' ^ (5 / 6 : ℝ)) ≤ 4 / κ ^ 2 := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le zero_lt_one hc'
  set x : ℝ := κ * c' ^ (5 / 6 : ℝ)
  have hx_pos : 0 < x := by positivity
  have hexp_half : 1 + x / 2 ≤ Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 2)
    linarith only [h]
  have hsq_exp : x ^ 2 / 4 ≤ Real.exp x := by
    have h1 : (x / 2) ^ 2 ≤ (1 + x / 2) ^ 2 := by nlinarith only [hx_pos]
    have h2 : (1 + x / 2) ^ 2 ≤ Real.exp (x / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hexp_half 2
    have h3 : Real.exp (x / 2) ^ 2 = Real.exp x := by
      rw [sq, ← Real.exp_add, add_halves]
    calc x ^ 2 / 4 = (x / 2) ^ 2 := by ring
      _ ≤ (1 + x / 2) ^ 2 := h1
      _ ≤ Real.exp (x / 2) ^ 2 := h2
      _ = Real.exp x := h3
  have hexp_inv : Real.exp (-x) ≤ 4 / x ^ 2 := by
    rw [Real.exp_neg]
    calc (Real.exp x)⁻¹ ≤ (x ^ 2 / 4)⁻¹ := inv_anti₀ (by positivity) hsq_exp
      _ = 4 / x ^ 2 := by field_simp [hx_pos.ne']
  have hx_sq : x ^ 2 = κ ^ 2 * c' ^ (5 / 3 : ℝ) := by
    dsimp [x]
    rw [mul_pow, ← Real.rpow_natCast (c' ^ (5 / 6 : ℝ)) 2, ← Real.rpow_mul hc'_pos.le]
    norm_num
  have hc_le : c' ^ (4 / 3 : ℝ) ≤ c' ^ (5 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hc' (by norm_num)
  have hneg_eq : -κ * c' ^ (5 / 6 : ℝ) = -x := by dsimp [x]; ring
  rw [hneg_eq]
  have hc53_pos : 0 < c' ^ (5 / 3 : ℝ) := Real.rpow_pos_of_pos hc'_pos _
  calc c' ^ (4 / 3 : ℝ) * Real.exp (-x)
      ≤ c' ^ (5 / 3 : ℝ) * (4 / x ^ 2) :=
        mul_le_mul hc_le hexp_inv (Real.exp_pos _).le hc53_pos.le
    _ = c' ^ (5 / 3 : ℝ) * (4 / (κ ^ 2 * c' ^ (5 / 3 : ℝ))) := by rw [hx_sq]
    _ = 4 / κ ^ 2 := by field_simp [hκ.ne', hc53_pos.ne']

lemma norm_contourIntegral_le_of_seg_boundW (f : ℂ → ℂ) (segs : List ContourSeg)
    {B : ℝ} (_hB : 0 ≤ B)
    (hseg : ∀ S ∈ segs, ‖∫ t in S.a..S.b, f (S.ω t) * S.ω' t‖ ≤ B) :
    ‖contourIntegral f segs‖ ≤ (segs.length : ℝ) * B := by
  induction segs with
  | nil => simp [contourIntegral]
  | cons S rest ih =>
    have hS : ‖∫ t in S.a..S.b, f (S.ω t) * S.ω' t‖ ≤ B := hseg S List.mem_cons_self
    have hrest := ih (fun S' hS' => hseg S' (List.mem_cons_of_mem _ hS'))
    change ‖(∫ t in S.a..S.b, f (S.ω t) * S.ω' t) + contourIntegral f rest‖ ≤
      (((rest.length + 1 : ℕ) : ℝ)) * B
    calc ‖(∫ t in S.a..S.b, f (S.ω t) * S.ω' t) + contourIntegral f rest‖
        ≤ ‖∫ t in S.a..S.b, f (S.ω t) * S.ω' t‖ + ‖contourIntegral f rest‖ := norm_add_le _ _
      _ ≤ B + (rest.length : ℝ) * B := add_le_add hS hrest
      _ = (((rest.length + 1 : ℕ) : ℝ)) * B := by push_cast; ring


/-! ### Packaged inner-scale witness and `zScaleCapW` -/

/-- Inner-scale witness for Lemma Z at weight `w`. -/
structure ZWitnessW {prob : FixedWeightProblem} (D : UniformPropositionPData prob) where
  c_D : ℝ
  C_D : ℝ
  d_D : ℝ
  c₀_D : ℝ
  hc_D : dpThr prob ≤ c_D
  hC_D : 0 < C_D
  hd_D : 0 < d_D
  hc₀_D : 0 < c₀_D
  hc₀_D_le4 : c₀_D ≤ innerChartRadius / 4
  hc₀_D_leV : c₀_D ≤ chartBV D.r_1 ^ 2
  hDp : ∀ {c' : ℝ}, c_D ≤ c' → ∀ {g : ℝ → ℝ},
    TestClass prob (c' / 12) g →
    0 < prob.cardyNorm (c' / 12) g →
    ∀ {u : ℂ}, u ∈ closedBall (0 : ℂ) (c₀_D * c' ^ (2 / 3 : ℝ)) →
      ‖truncatedMellinPW prob c' dpT0 g u - psiTilde prob c' g u‖ ≤
        C_D * Real.exp (-d_D * c') * airyEnv u
  q_V : ℂ → ℂ
  c₀_use : ℝ
  C₁ : ℝ
  C₂ : ℝ
  r_φ : ℝ
  c₀_Z : ℝ
  hc₀_Z_pos : 0 < c₀_Z
  hc₀_Z_le_D : c₀_Z ≤ c₀_D
  hc₀_Z_le_use : c₀_Z ≤ c₀_use
  hC₁_nn : 0 ≤ C₁
  hC₂_nn : 0 ≤ C₂
  hC₁_small : C₁ * c₀_use ≤ 1 / 10
  h_saddle : ∀ {c' a' φ : ℝ}, 0 < c' → 0 ≤ a' → 0 ≤ φ → φ ≤ Real.pi / 2 →
    a' ^ 2 * c' ^ (-(2 / 3 : ℝ)) ≤ c₀_Z →
    let u : ℂ := ((a' ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((Real.pi - 2 * φ : ℝ) : ℂ))
    let z : ℂ := u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
    let ζp : ℂ := (kappaV : ℂ) * ((c' ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * u ^ (1 / 2 : ℂ) * q_V z
    let ρ : ℝ := ‖ζp‖
    chartB ζp = virasoroBChart c' u ∧
    0 ≤ ζp.re ∧ 0 ≤ ζp.im ∧
    ρ ≤ dpConfig.ρ₀ ∧ ρ < r_φ ∧ C₂ * ρ ^ 2 ≤ 1 / 6 ∧
    (9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') ≤ ρ ∧
    ρ ≤ (11 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') ∧
    (5 / 6 : ℝ) * (ρ * Real.sin φ) ≤ ζp.re
  hφ_pot : ∀ ζ ∈ ball (0 : ℂ) r_φ, 0 < ζ.re →
    (chartPhiV ζ (chartB ζ)).re = (tipL (chartB ζ)).re + majorant2D (chartB ζ)
  C_S4 : ℝ
  c_S4 : ℝ
  hCS4 : 0 < C_S4
  hcS4 : max 1 (24 * prob.totalShift) ≤ c_S4
  hS4 : ∀ {c' : ℝ}, c_S4 ≤ c' → ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
    ∀ ζ ∈ stripClosed, ‖tildeWW prob.w c' g ζ‖ ≤ C_S4 * prob.cardyNorm (c' / 12) g
  C_S2 : ℝ
  c_S2 : ℝ
  hCS2 : 0 < C_S2
  hcS2 : max 1 (24 * prob.totalShift) ≤ c_S2
  hS2 : ∀ {c' : ℝ}, c_S2 ≤ c' → ∀ {ω : ℂ}, dpConfig.μ₀ ≤ ω.re →
    ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
      ‖mellinMGW g ((prob.w : ℂ) / 2 + (c' : ℂ) * ω)‖ ≤
        C_S2 * Real.exp (c' * ComplexBessel.crudeExponentB ω) *
          prob.cardyNorm (c' / 12) g
  c_V : ℝ
  C_V : ℝ
  hc_V : 39 ≤ c_V
  hC_V : 0 < C_V
  hV_bd : ∀ {c' : ℝ}, c_V ≤ c' → ∀ {u : ℂ},
    u ∈ closedBall (0 : ℂ) (chartAC D.r_1 c' ^ 2) →
    ‖cardyVC prob (c' / 12) (virasoroDeltaChartC c' u)‖ ≤
      C_V * c' ^ (-(1 / 2 : ℝ)) * Real.exp (c' * (tipL (virasoroBChart c' u)).re)

lemma zWitnessW_exists {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    Nonempty (ZWitnessW D) := by
  obtain ⟨c_D, C_D, d_D, c₀_D, hc_D, hC_D, hd_D, hc₀_D, hc₀_D_le4, hc₀_D_leV, hDp⟩ := lemma_Dp_W D
  obtain ⟨_, q_V, c₀_max, hc₀_max_pos, C₁, hC₁, C₂, hC₂, _, _, _, _, _, _, hS6_main, _⟩ :=
    lemma_S6 langerChartSpec_virasoro
  obtain ⟨r_φ, hr_φ_pos, _, hφ_pot⟩ := chartPhiV_saddle_eq_potential
  obtain ⟨C_S4, c_S4, hCS4, hcS4, hS4⟩ := lemma_S4_W prob
  obtain ⟨C_S2, c_S2, hCS2, hcS2, hS2⟩ := lemma_S2_W prob dpConfig.hμ₀_gt
  obtain ⟨c_V, C_V, _, hc_V, hC_V, hV_bd⟩ := cardyVC_inner_bound D
  let c₀_use : ℝ := min (c₀_max / 2) (1 / (10 * (C₁ + 1)))
  have hc₀_use_pos : 0 < c₀_use := by positivity
  have hc₀_use_mem : c₀_use ∈ Ioo 0 c₀_max :=
    ⟨hc₀_use_pos, (min_le_left _ _).trans_lt (half_lt_self hc₀_max_pos)⟩
  have hC₁_small : C₁ * c₀_use ≤ 1 / 10 := by
    have h1 : c₀_use ≤ 1 / (10 * (C₁ + 1)) := min_le_right _ _
    have hne : C₁ + 1 ≠ 0 := by linarith only [hC₁]
    calc C₁ * c₀_use ≤ C₁ * (1 / (10 * (C₁ + 1))) := mul_le_mul_of_nonneg_left h1 hC₁
      _ = (C₁ / (C₁ + 1)) * (1 / 10) := by field_simp [hne]
      _ ≤ 1 * (1 / 10) := by
          gcongr; exact (div_le_one (by linarith only [hC₁])).mpr (by linarith only [])
      _ = 1 / 10 := one_mul _
  let ρ_cap : ℝ := min dpConfig.ρ₀ (min r_φ (min 1 (1 / (6 * (C₂ + 1)))))
  have hρ_cap_pos : 0 < ρ_cap :=
    lt_min dpConfig.hρ₀_pos (lt_min hr_φ_pos (lt_min zero_lt_one (by positivity)))
  let c₀_Z : ℝ := min c₀_D (min c₀_use ((ρ_cap / (2 * kappaV * (1 + C₁ * c₀_use) + 1)) ^ 2))
  have hc₀_Z_pos : 0 < c₀_Z :=
    lt_min hc₀_D (lt_min hc₀_use_pos
      (sq_pos_of_pos (div_pos hρ_cap_pos (by have := kappaV_pos; positivity))))
  refine ⟨{
    c_D := c_D, C_D := C_D, d_D := d_D, c₀_D := c₀_D,
    hc_D := hc_D, hC_D := hC_D, hd_D := hd_D, hc₀_D := hc₀_D, hc₀_D_le4 := hc₀_D_le4, hc₀_D_leV := hc₀_D_leV,
    hDp := hDp, q_V := q_V, c₀_use := c₀_use, C₁ := C₁, C₂ := C₂, r_φ := r_φ, c₀_Z := c₀_Z,
    hc₀_Z_pos := hc₀_Z_pos,
    hc₀_Z_le_D := min_le_left _ _,
    hc₀_Z_le_use := (min_le_right _ _).trans (min_le_left _ _),
    hC₁_nn := hC₁, hC₂_nn := hC₂, hC₁_small := hC₁_small,
    h_saddle := fun {c' a' φ} hc' ha' hφ0 hφpi ha_le => by
      have ha_use : a' ^ 2 * c' ^ (-(2 / 3 : ℝ)) ≤ c₀_use :=
        ha_le.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hS6 := hS6_main c₀_use hc₀_use_mem c' a' φ hc' ha' hφ0 hφpi ha_use
      dsimp only at hS6 ⊢
      set u : ℂ := ((a' ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((Real.pi - 2 * φ : ℝ) : ℂ))
      set z : ℂ := u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
      set ζp : ℂ := (kappaV : ℂ) * ((c' ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * u ^ (1 / 2 : ℂ) * q_V z
      set ρ : ℝ := ‖ζp‖
      obtain ⟨_, hchartB, hσp_nn, hτp_nn, hρ_rel, hσp_rel, _, _⟩ := hS6
      have hb_eq : chartB ζp = virasoroBChart c' u :=
        hchartB.trans (langerChartSpec_virasoro_bL_eq c' u)
      have hρ_lo : (9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') ≤ ρ := by
        have h1 := (abs_le.mp hρ_rel).1
        have hkn : 0 ≤ kappaV * c' ^ (-(1 / 3 : ℝ)) * a' := by have := kappaV_pos; positivity
        nlinarith only [h1, hC₁_small, hkn]
      have hρ_hi : ρ ≤ (11 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') := by
        have h1 := (abs_le.mp hρ_rel).2
        have hkn : 0 ≤ kappaV * c' ^ (-(1 / 3 : ℝ)) * a' := by have := kappaV_pos; positivity
        nlinarith only [h1, hC₁_small, hkn]
      have hsqrt_Z : Real.sqrt c₀_Z ≤ ρ_cap / (2 * kappaV * (1 + C₁ * c₀_use) + 1) := by
        have hsq : c₀_Z ≤ (ρ_cap / (2 * kappaV * (1 + C₁ * c₀_use) + 1)) ^ 2 :=
          (min_le_right _ _).trans (min_le_right _ _)
        exact (Real.sqrt_le_sqrt hsq).trans_eq
          (Real.sqrt_sq (div_nonneg hρ_cap_pos.le (by have := kappaV_pos; positivity)))
      have ha_rt : c' ^ (-(1 / 3 : ℝ)) * a' ≤ Real.sqrt c₀_Z := by
        refine Real.le_sqrt_of_sq_le ?_
        rw [mul_pow, ← Real.rpow_natCast (c' ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hc'.le]
        calc c' ^ (-(1 / 3 : ℝ) * (2 : ℕ)) * a' ^ 2 = a' ^ 2 * c' ^ (-(2 / 3 : ℝ)) := by
              push_cast; rw [show -(1 / 3 : ℝ) * 2 = -(2 / 3 : ℝ) by norm_num, mul_comm]
          _ ≤ c₀_Z := ha_le
      have hρ_half : ρ ≤ ρ_cap / 2 := by
        have h1 : ρ ≤ (1 + C₁ * c₀_use) * kappaV * (c' ^ (-(1 / 3 : ℝ)) * a') := by
          have h2 := (abs_le.mp hρ_rel).2
          linarith only [h2]
        have hden2 : (1 + C₁ * c₀_use) * kappaV ≤ (2 * kappaV * (1 + C₁ * c₀_use) + 1) / 2 := by
          linarith only []
        calc ρ ≤ (1 + C₁ * c₀_use) * kappaV * (c' ^ (-(1 / 3 : ℝ)) * a') := h1
          _ ≤ (1 + C₁ * c₀_use) * kappaV * (ρ_cap / (2 * kappaV * (1 + C₁ * c₀_use) + 1)) := by
              gcongr; · have := kappaV_pos; positivity
              · exact ha_rt.trans hsqrt_Z
          _ ≤ ((2 * kappaV * (1 + C₁ * c₀_use) + 1) / 2) *
                (ρ_cap / (2 * kappaV * (1 + C₁ * c₀_use) + 1)) :=
              mul_le_mul_of_nonneg_right hden2
                (div_nonneg hρ_cap_pos.le (by have := kappaV_pos; positivity))
          _ = ρ_cap / 2 := by
              have hne : 2 * kappaV * (1 + C₁ * c₀_use) + 1 ≠ 0 := by
                have := kappaV_pos; positivity
              field_simp [hne]
      have hρ_cap : ρ ≤ ρ_cap := hρ_half.trans (half_le_self hρ_cap_pos.le)
      have hρ_ρ₀ : ρ ≤ dpConfig.ρ₀ := hρ_cap.trans (min_le_left _ _)
      have hρ_rφ : ρ < r_φ :=
        hρ_half.trans_lt ((div_two_lt_of_pos hρ_cap_pos).trans_le
          ((min_le_right _ _).trans (min_le_left _ _)))
      have hC₂_sq : C₂ * ρ ^ 2 ≤ 1 / 6 := by
        have hρ_nn : 0 ≤ ρ := norm_nonneg _
        have hρ1 : ρ ≤ 1 :=
          hρ_cap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
        have hρ6 : ρ ≤ 1 / (6 * (C₂ + 1)) :=
          hρ_cap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
        have hsq_le : ρ ^ 2 ≤ ρ := by nlinarith only [hρ_nn, hρ1]
        have hne2 : C₂ + 1 ≠ 0 := by linarith only [hC₂]
        calc C₂ * ρ ^ 2 ≤ C₂ * ρ := mul_le_mul_of_nonneg_left hsq_le hC₂
          _ ≤ C₂ * (1 / (6 * (C₂ + 1))) := mul_le_mul_of_nonneg_left hρ6 hC₂
          _ = (C₂ / (C₂ + 1)) * (1 / 6) := by field_simp [hne2]
          _ ≤ 1 * (1 / 6) := by
              gcongr; exact (div_le_one (by linarith only [hC₂])).mpr (by linarith only [])
          _ = 1 / 6 := one_mul _
      have hσ_lb : (5 / 6 : ℝ) * (ρ * Real.sin φ) ≤ ζp.re := by
        have h1 := (abs_le.mp hσp_rel).1
        have hsin_nn : 0 ≤ Real.sin φ :=
          Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith only [hφpi, Real.pi_pos])
        have hprod_nn : 0 ≤ ρ * Real.sin φ := mul_nonneg (norm_nonneg _) hsin_nn
        nlinarith only [h1, hC₂_sq, hprod_nn]
      exact ⟨hb_eq, hσp_nn, hτp_nn, hρ_ρ₀, hρ_rφ, hC₂_sq, hρ_lo, hρ_hi, hσ_lb⟩,
    hφ_pot := fun ζ hζ hre => (hφ_pot ζ hζ hre).2,
    C_S4 := C_S4, c_S4 := c_S4, hCS4 := hCS4, hcS4 := hcS4,
    hS4 := fun {c'} hc' {g} hg => (hS4 hc' hg).2.2.2,
    C_S2 := C_S2, c_S2 := c_S2, hCS2 := hCS2, hcS2 := hcS2,
    hS2 := fun {c'} hc' {ω} hω {g} hg => (hS2 hc' hω hg).2,
    c_V := c_V, C_V := C_V, hc_V := hc_V, hC_V := hC_V,
    hV_bd := fun {c'} hc' {u} hu => hV_bd hc' hu }⟩

noncomputable def zWitnessW {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    ZWitnessW D := Classical.choice (zWitnessW_exists D)

/-- Inner Langer chart scale cap `c₀_Z > 0` within which `lemma_Dp`, `lemma_S6`, and `lemma_Zp`
simultaneously apply for Lemma Z (`vlo:Z`). -/
noncomputable def zScaleCapW {prob : FixedWeightProblem} (D : UniformPropositionPData prob) : ℝ :=
  (zWitnessW D).c₀_Z

lemma zScaleCapW_pos {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    0 < zScaleCapW D := (zWitnessW D).hc₀_Z_pos

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.zWitnessW_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zWitnessW_exists

end FormalResearch.ModularBootstrap.FixedWeightBand
