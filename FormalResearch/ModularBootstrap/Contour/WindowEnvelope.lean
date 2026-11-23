module

public import FormalResearch.ModularBootstrap.Contour.TruncationError
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuadratureBounds

/-!
# Window Lemma and Improved Envelope (`lower_o1_two_edge.tex`, Lemma Z `vlo:Z`)

Formalizes **Lemma Z** (`vlo:Z`, `lower_o1_two_edge.tex`, lines 825–836):
an interior multiplier bound
`‖tildeWV c' g ζ‖ ≤ M[g] * (Λ * c'^{-5/6} * ‖ζ‖ / ζ.re)`
on the saddle sector `S = {ζ ∈ stripClosed | ρ_R / 3 ≤ ‖ζ‖ ≤ 2 ρ_R, c'^{-1/12} ‖ζ‖ ≤ ζ.re}`
for `Λ ≥ 1` implies the Airy envelope `YVEnvBound (virasoroPsiTilde c' g) c' R (C_B * Λ)`
on `R - 1 ≤ ‖u‖ ≤ R + 1`, `0 ≤ u.im`, `2 c'^{-1/12} √‖u‖ ≤ (u^{1/2}).re`.

## Proof architecture
1. `cpow_half_re_eq_sqrt_mul_sin`: exact polar identity
   `(u ^ (1 / 2 : ℂ)).re = √‖u‖ * Real.sin ((Real.pi - u.arg) / 2)` for `u ≠ 0`.
2. `integral_exp_neg_mul_sq_le` and `integral_exp_neg_mul_sub_sq_le`: elementary `arctan`
   comparisons `exp(-α t^2) ≤ (1 + α t^2)⁻¹` bounding the Gaussian ray integrals by
   `(π / 2) / √α`.
3. `rpow_four_thirds_mul_exp_neg_le`: algebraic inequality `x^2 / 4 ≤ exp x` yielding
   `c'^{4/3} exp(-κ c'^{5/6}) ≤ 4 / κ^2` for all `c' ≥ 1`.
4. `zScaleCap` and `lemma_Z`: combines `lemma_Dp` with `dpConfig_spec`,
   `truncatedMellinP_eq_contourIntegral`, `lemma_S6 langerChartSpec_virasoro`, `lemma_S4`, and
   `lemma_S2` across all contour pieces (`.upperRay`, `.lowerRay`, `.arcRadial`, `.fixedStrip`,
   and `isStrip = false`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Contour

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

/-! ### 1. Elementary polar, Gaussian-window, and exponential helpers -/

private lemma cpow_half_re_eq_sqrt_mul_sin {u : ℂ} (hu : u ≠ 0) :
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

private lemma exp_neg_le_inv_one_add {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ (1 + x)⁻¹ := by
  have h1 : 1 + x ≤ Real.exp x := by
    have h := Real.add_one_le_exp x
    linarith only [h]
  rw [Real.exp_neg]
  exact inv_anti₀ (by linarith only [hx]) h1

private lemma integral_exp_neg_mul_sq_le {α L : ℝ} (hα : 0 < α) (hL : 0 ≤ L) :
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
    exact exp_neg_le_inv_one_add (by positivity)
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

private lemma integral_exp_neg_mul_sub_sq_le {α L : ℝ} (hα : 0 < α) (hL : 0 ≤ L) :
    ∫ t in (0 : ℝ)..L, Real.exp (-α * (L - t) ^ 2) ≤ (Real.pi / 2) / Real.sqrt α := by
  have hsub := intervalIntegral.integral_comp_sub_left (fun u : ℝ => Real.exp (-α * u ^ 2)) L
    (a := 0) (b := L)
  rw [sub_zero, sub_self] at hsub
  rw [hsub]
  exact integral_exp_neg_mul_sq_le hα hL

private lemma rpow_four_thirds_mul_exp_neg_le {κ c' : ℝ} (hκ : 0 < κ) (hc' : 1 ≤ c') :
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

private lemma norm_contourIntegral_le_of_seg_bound (f : ℂ → ℂ) (segs : List ContourSeg)
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

/-! ### 2. Packaged inner-scale witness and `zScaleCap` -/

structure ZWitness where
  c_D : ℝ
  C_D : ℝ
  d_D : ℝ
  c₀_D : ℝ
  hc_D : 10000 ≤ c_D
  hC_D : 0 < C_D
  hd_D : 0 < d_D
  hc₀_D : 0 < c₀_D
  hc₀_D_le4 : c₀_D ≤ innerChartRadius / 4
  hDp : ∀ {c' : ℝ}, c_D ≤ c' → ∀ {g : ℝ → ℝ},
    TestClass virasoroProblem (c' / 12) g →
    0 < virasoroProblem.cardyNorm (c' / 12) g →
    ∀ {u : ℂ}, u ∈ closedBall (0 : ℂ) (c₀_D * c' ^ (2 / 3 : ℝ)) →
      ‖truncatedMellinP c' dpT0 g u - virasoroPsiTilde c' g u‖ ≤
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
  hcS4 : 10000 ≤ c_S4
  hS4 : ∀ {c' : ℝ}, c_S4 ≤ c' → ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
    ∀ ζ ∈ stripClosed, ‖tildeWV c' g ζ‖ ≤ C_S4 * virasoroProblem.cardyNorm (c' / 12) g
  C_S2 : ℝ
  c_S2 : ℝ
  hCS2 : 0 < C_S2
  hcS2 : 10000 ≤ c_S2
  hS2 : ∀ {c' : ℝ}, c_S2 ≤ c' → ∀ {ω : ℂ}, dpConfig.μ₀ ≤ ω.re →
    ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
      ‖mellinMG g (1 / 2 + (c' : ℂ) * ω)‖ ≤
        C_S2 * Real.exp (c' * ComplexBessel.crudeExponentB ω) *
          virasoroProblem.cardyNorm (c' / 12) g
  c_V : ℝ
  C_V : ℝ
  hc_V : 39 ≤ c_V
  hC_V : 0 < C_V
  hV_bd : ∀ {c' : ℝ}, c_V ≤ c' → ∀ {u : ℂ},
    u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) →
    ‖V_C (c' : ℂ) (virasoroDeltaChartC c' u)‖ ≤
      C_V * c' ^ (-(1 / 2 : ℝ)) * Real.exp (c' * (tipL (virasoroBChart c' u)).re)

lemma zWitness_exists : Nonempty ZWitness := by
  obtain ⟨c_D, C_D, d_D, c₀_D, hc_D, hC_D, hd_D, hc₀_D, hc₀_D_le4, hDp⟩ := lemma_Dp
  obtain ⟨_, q_V, c₀_max, hc₀_max_pos, C₁, hC₁, C₂, hC₂, _, _, _, _, _, _, hS6_main, _⟩ :=
    lemma_S6 langerChartSpec_virasoro
  obtain ⟨r_φ, hr_φ_pos, _, hφ_pot⟩ := chartPhiV_saddle_eq_potential
  obtain ⟨C_S4, c_S4, hCS4, hcS4, hS4⟩ := lemma_S4
  obtain ⟨C_S2, c_S2, hCS2, hcS2, hS2⟩ := lemma_S2 dpConfig.hμ₀_gt
  obtain ⟨c_V, C_V, hc_V, hC_V, hV_bd⟩ := virasoroV_C_inner_bound
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
    hc_D := hc_D, hC_D := hC_D, hd_D := hd_D, hc₀_D := hc₀_D, hc₀_D_le4 := hc₀_D_le4,
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

noncomputable def zWitness : ZWitness := Classical.choice zWitness_exists

/-- Inner Langer chart scale cap `c₀_Z > 0` within which `lemma_Dp`, `lemma_S6`, and `lemma_Zp`
simultaneously apply for Lemma Z (`vlo:Z`). -/
noncomputable def zScaleCap : ℝ := zWitness.c₀_Z

lemma zScaleCap_pos : 0 < zScaleCap := zWitness.hc₀_Z_pos

/-! ### 3. Per-segment and envelope assembly helpers for Lemma Z -/

private lemma const_seg_integral_le {f : ℝ → ℂ} {a b K C_tail B_unit : ℝ}
    (hab : a ≤ b) (hba : b - a ≤ 1) (hK_nn : 0 ≤ K) (hC_nn : 0 ≤ C_tail)
    (hC_le : C_tail ≤ B_unit)
    (hf_cont : ContinuousOn (fun τ => ‖f τ‖) (Icc a b))
    (hpt : ∀ τ ∈ Icc a b, ‖f τ‖ ≤ K * C_tail) :
    ‖∫ τ in a..b, f τ‖ ≤ K * B_unit := by
  have hKC_nn : 0 ≤ K * C_tail := mul_nonneg hK_nn hC_nn
  have h1 : ‖∫ τ in a..b, f τ‖ ≤ ∫ τ in a..b, K * C_tail :=
    (intervalIntegral.norm_integral_le_integral_norm hab).trans
      (intervalIntegral.integral_mono_on hab (hf_cont.intervalIntegrable_of_Icc hab)
        intervalIntegrable_const hpt)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  calc ‖∫ τ in a..b, f τ‖
      ≤ (b - a) * (K * C_tail) := h1
    _ ≤ 1 * (K * C_tail) := mul_le_mul_of_nonneg_right hba hKC_nn
    _ = K * C_tail := one_mul _
    _ ≤ K * B_unit := mul_le_mul_of_nonneg_left hC_le hK_nn

private lemma ray_seg_integral_le {f : ℝ → ℂ} {d : ℝ → ℝ} {a b t_max α_g K W_pt C_tail : ℝ}
    (ha : a = 0) (hb : b = t_max) (ht_nn : 0 ≤ t_max) (ht_le1 : t_max ≤ 1)
    (_hα : 0 < α_g) (hK_nn : 0 ≤ K) (hW_nn : 0 ≤ W_pt) (hC_nn : 0 ≤ C_tail)
    (hd_cont : Continuous d)
    (hf_cont : ContinuousOn (fun τ => ‖f τ‖) (Icc 0 t_max))
    (hgauss : ∫ τ in (0 : ℝ)..t_max, Real.exp (-α_g * d τ ^ 2) ≤
      (Real.pi / 2) / Real.sqrt α_g)
    (hpt : ∀ τ ∈ Icc (0 : ℝ) t_max,
      ‖f τ‖ ≤ (K * W_pt) * Real.exp (-α_g * d τ ^ 2) + K * C_tail) :
    ‖∫ τ in a..b, f τ‖ ≤
      K * (W_pt * ((Real.pi / 2) / Real.sqrt α_g) + C_tail) := by
  rw [ha, hb]
  have hg_cont : ContinuousOn (fun τ : ℝ => (K * W_pt) * Real.exp (-α_g * d τ ^ 2))
      (Icc 0 t_max) := by fun_prop
  have hrhs_cont : ContinuousOn
      (fun τ : ℝ => (K * W_pt) * Real.exp (-α_g * d τ ^ 2) + K * C_tail)
      (Icc 0 t_max) := hg_cont.add continuousOn_const
  have hint_le : ‖∫ τ in (0 : ℝ)..t_max, f τ‖ ≤
      ∫ τ in (0 : ℝ)..t_max,
        ((K * W_pt) * Real.exp (-α_g * d τ ^ 2) + K * C_tail) :=
    (intervalIntegral.norm_integral_le_integral_norm ht_nn).trans
      (intervalIntegral.integral_mono_on ht_nn
        (hf_cont.intervalIntegrable_of_Icc ht_nn)
        (hrhs_cont.intervalIntegrable_of_Icc ht_nn) hpt)
  have hint_split : ∫ τ in (0 : ℝ)..t_max,
        ((K * W_pt) * Real.exp (-α_g * d τ ^ 2) + K * C_tail) =
      (K * W_pt) * (∫ τ in (0 : ℝ)..t_max, Real.exp (-α_g * d τ ^ 2)) +
        t_max * (K * C_tail) := by
    rw [intervalIntegral.integral_add (hg_cont.intervalIntegrable_of_Icc ht_nn)
        intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
      sub_zero]
  calc ‖∫ τ in (0 : ℝ)..t_max, f τ‖
      ≤ (K * W_pt) * (∫ τ in (0 : ℝ)..t_max, Real.exp (-α_g * d τ ^ 2)) +
          t_max * (K * C_tail) := hint_le.trans_eq hint_split
    _ ≤ (K * W_pt) * ((Real.pi / 2) / Real.sqrt α_g) + 1 * (K * C_tail) :=
        add_le_add (mul_le_mul_of_nonneg_left hgauss (mul_nonneg hK_nn hW_nn))
          (mul_le_mul_of_nonneg_right ht_le1 (mul_nonneg hK_nn hC_nn))
    _ = K * (W_pt * ((Real.pi / 2) / Real.sqrt α_g) + C_tail) := by ring

private lemma lemma_Z_seg_bound (W : ZWitness) (P : ZPConfig)
    {c' Λ φ ρ κ_all ρ_min_Z M_g K_seg B_seg_unit : ℝ}
    {g : ℝ → ℝ} {s b t u : ℂ} (S : ContourSeg)
    (hc'_pos : 0 < c') (hc'_ge1 : 1 ≤ c') (hc'_24 : 24 ≤ c')
    (hc'_48 : 48 / P.c_Γ ≤ c') (hc'_S4 : W.c_S4 ≤ c')
    (hΛ_nn : 0 ≤ Λ) (hsin_pos : 0 < Real.sin φ) (hρ_pos : 0 < ρ) (hs_re_pos : 0 < s.re)
    (hρ_min_pos : 0 < ρ_min_Z) (hρ_ge_min : ρ_min_Z ≤ ρ)
    (hc_ρ_sre_sq : (25 / 9 : ℝ) * ρ_min_Z ^ 3 * c' ^ (5 / 6 : ℝ) ≤ c' * ρ * s.re ^ 2)
    (_hκ_all_pos : 0 < κ_all)
    (hκ_ray : κ_all ≤ (P.c_γ / 16) * (25 / 9 : ℝ) * ρ_min_Z ^ 3)
    (hκ_arc : κ_all ≤ P.κ_arc * ρ_min_Z ^ 3)
    (hκ_strip : κ_all ≤ P.κ_strip)
    (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < M_g) (hM_eq : M_g = virasoroProblem.cardyNorm (c' / 12) g)
    (hb_re_pos : 0 < b.re) (ht_re_pos : 0 < t.re) (ht_eq : t = (c' : ℂ) * b ^ 2 / 3)
    (ht_half_ub : ‖t ^ (-(1 / 2 : ℂ))‖ ≤ (2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ)))
    (hair_eq : Real.exp (c' * (chartPhiV s b).re) = airyEnv u)
    (hK_seg_eq : K_seg = (4 * Real.sqrt 3 / xiStar) * P.C_d * M_g *
      c' ^ (-(1 / 2 : ℝ)) * Real.exp (-(c' * (tipL b).re)) * airyEnv u)
    (hB_seg_eq : B_seg_unit =
      (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
        ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)) +
      max W.C_S4 W.C_S2 * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)))
    (hwin_wv : ∀ ζ ∈ stripClosed, ‖ζ - s‖ ≤ s.re / 4 →
      ‖tildeWV c' g ζ‖ ≤ M_g * (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ))
    (hS2_P : ∀ {ω : ℂ}, P.μ₀ ≤ ω.re →
      ‖mellinMG g (1 / 2 + (c' : ℂ) * ω)‖ ≤
        W.C_S2 * Real.exp (c' * ComplexBessel.crudeExponentB ω) * M_g)
    (hba : S.b - S.a ≤ 1)
    (hω_bd : ∀ τ ∈ Icc S.a S.b,
      0 ≤ (S.ω τ).re ∧ P.c_Γ ≤ ‖S.ω τ‖ ∧ ‖S.ω τ‖ ≤ P.C_Γ ∧ ‖S.ω' τ‖ ≤ P.C_d)
    (h_ur : S.isStrip = true → S.kind = .upperRay →
      ∃ t_max ≥ (0 : ℝ), S.a = 0 ∧ S.b = t_max ∧ t_max ≤ 11 * ρ ∧
        ∀ τ ∈ Icc 0 t_max, ‖S.ζ τ - s‖ = t_max - τ ∧ ‖S.ζ' τ‖ = 1 ∧
          (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re - P.c_γ * ρ * (t_max - τ) ^ 2)
    (h_lr : S.isStrip = true → S.kind = .lowerRay →
      ∃ t_max ≥ (0 : ℝ), S.a = 0 ∧ S.b = t_max ∧ t_max ≤ 11 * ρ ∧
        ∀ τ ∈ Icc 0 t_max, ‖S.ζ τ - s‖ = τ ∧ ‖S.ζ' τ‖ = 1 ∧
          (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re - P.c_γ * ρ * τ ^ 2)
    (h_ar : S.isStrip = true → S.kind = .arcRadial →
      ∀ τ ∈ Icc S.a S.b, (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re - P.κ_arc * ρ ^ 3)
    (h_fs : S.isStrip = true → S.kind = .fixedStrip →
      ∀ τ ∈ Icc S.a S.b, (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re - P.κ_strip)
    (hnonstrip : S.isStrip = false → ∀ τ ∈ Icc S.a S.b,
      P.μ₀ ≤ (S.ω τ).re ∧ crudeExponentEc (S.ω τ) b ≤ (chartPhiV s b).re - P.c_γ * ρ * s.re ^ 2)
    (h_no_crude : S.isStrip = true → S.kind ≠ .crudeEdge) :
    ‖∫ τ in S.a..S.b, mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖ ≤
      K_seg * B_seg_unit := by
  have hK_seg_pos : 0 < K_seg := by
    rw [hK_seg_eq]
    have := xiStar_pos; have := P.hC_d_pos; have := airyEnv_pos u; positivity
  have hKM_nn : 0 ≤ K_seg / M_g := div_nonneg hK_seg_pos.le hM_pos.le
  have hCS_max_pos : 0 < max W.C_S4 W.C_S2 := lt_of_lt_of_le W.hCS4 (le_max_left _ _)
  set C_tail_u : ℝ := max W.C_S4 W.C_S2 * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))
  have hC_tail_nn : 0 ≤ C_tail_u := mul_nonneg hCS_max_pos.le (Real.exp_pos _).le
  set W_pt : ℝ := 2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ
  have hW_pt_nn : 0 ≤ W_pt := by dsimp [W_pt]; positivity
  have hwin_term_nn : 0 ≤ W_pt * ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)) := by
    have := P.hc_γ_pos; positivity
  have hC_tail_le_B : C_tail_u ≤ B_seg_unit := by
    rw [hB_seg_eq]; dsimp [W_pt, C_tail_u]; linarith only [hwin_term_nn]
  have hc56_le_c : c' ^ (5 / 6 : ℝ) ≤ c' :=
    (Real.rpow_le_rpow_of_exponent_le hc'_ge1 (by norm_num)).trans_eq (Real.rpow_one c')
  have hstrip_mul_le : ∀ {A B E₁ E₂ : ℝ}, 0 ≤ B → A ≤ B → 0 ≤ E₁ → E₁ ≤ E₂ →
      (K_seg / M_g) * A * E₁ ≤ (K_seg / M_g) * B * E₂ := fun hB hAB hE1 hE =>
    mul_le_mul (mul_le_mul_of_nonneg_left hAB hKM_nn) hE hE1 (mul_nonneg hKM_nn hB)
  have hcont_seg : ContinuousOn (fun τ => mellinDensityIntegrand c' g t (S.ω τ)) (Icc S.a S.b) := by
    intro τ hτ
    have hω_re_nn := (hω_bd τ hτ).1
    have hz_re : 0 < (1 / 2 + (c' : ℂ) * S.ω τ).re := by
      have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
      simp only [Complex.add_re, h12, Complex.re_ofReal_mul]
      have hcw := mul_nonneg hc'_pos.le hω_re_nn
      linarith only [hcw]
    have hGam_d : DifferentiableAt ℂ Complex.Gamma (1 / 2 + (c' : ℂ) * S.ω τ) :=
      Complex.differentiableAt_Gamma _ (fun m hm => by
        have hrm := congrArg Complex.re hm
        simp only [Complex.neg_re, Complex.natCast_re] at hrm
        linarith only [hz_re, hrm, Nat.cast_nonneg (α := ℝ) m])
    have h_an_w : DifferentiableAt ℂ (mellinDensityIntegrand c' g t) (S.ω τ) := by
      have hm_d := (differentiable_mellinMGEntire (by linarith only [hc'_24] : 2 ≤ c' / 12) hg).differentiableAt
        (x := 1 / 2 + (c' : ℂ) * S.ω τ)
      have ht_ne : (2 * (Real.pi : ℂ) * t) ≠ 0 := by
        have ht0 : t ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at ht_re_pos; exact lt_irrefl 0 ht_re_pos
        exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) ht0
      have hlin : DifferentiableAt ℂ (fun ω : ℂ => 1 / 2 + (c' : ℂ) * ω) (S.ω τ) := by fun_prop
      have hp_d : DifferentiableAt ℂ (fun ω : ℂ =>
          (2 * (Real.pi : ℂ) * t) ^ (-(1 / 2 + (c' : ℂ) * ω))) (S.ω τ) := by
        have hex : (fun ω : ℂ => (2 * (Real.pi : ℂ) * t) ^ (-(1 / 2 + (c' : ℂ) * ω))) =
            fun ω => Complex.exp (Complex.log (2 * (Real.pi : ℂ) * t) * (-(1 / 2 + (c' : ℂ) * ω))) := by
          ext ω; rw [Complex.cpow_def_of_ne_zero ht_ne]
        rw [hex]; fun_prop
      have h1 := DifferentiableAt.comp (g := Complex.Gamma) (S.ω τ) hGam_d hlin
      have h2 := DifferentiableAt.comp (g := mellinMGEntire g) (S.ω τ) hm_d hlin
      exact (h1.mul hp_d).mul h2
    exact h_an_w.continuousAt.comp_continuousWithinAt (S.hω_cont τ hτ)
  have hf_cont : ContinuousOn
      (fun τ => ‖mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖) (Icc S.a S.b) :=
    (hcont_seg.mul S.hω'_cont).norm
  have hpt_stirling : ∀ τ ∈ Icc S.a S.b,
      let ω := S.ω τ
      0 < (1 / 2 + (c' : ℂ) * ω).re ∧
      ‖stirlingS c' ω‖ ≤ 2 ∧
      mellinDensityIntegrand c' g t ω =
        t ^ (-(1 / 2 : ℂ)) * stirlingS c' ω *
          Complex.exp ((c' : ℂ) * ComplexBessel.stirlingJ ω b) *
          mellinMG g (1 / 2 + (c' : ℂ) * ω) := fun τ hτ => by
    obtain ⟨hω_re, hω_lb, _, _⟩ := hω_bd τ hτ
    have hcω_48 : 48 ≤ c' * ‖S.ω τ‖ :=
      ((div_le_iff₀ P.hc_Γ_pos).mp hc'_48).trans (mul_le_mul_of_nonneg_left hω_lb hc'_pos.le)
    have hω_ne : S.ω τ ≠ 0 := by intro h0; rw [h0, norm_zero, mul_zero] at hcω_48; linarith only [hcω_48]
    have hS_bd : ‖stirlingS c' (S.ω τ)‖ ≤ 2 := by
      have h1 : 1 ≤ c' * ‖S.ω τ‖ := by linarith only [hcω_48]
      have hsub := norm_stirlingS_sub_one_le hc'_pos hω_re h1
      have hle : 24 / (c' * ‖S.ω τ‖) ≤ 1 / 2 := by
        calc 24 / (c' * ‖S.ω τ‖) ≤ 24 / 48 := by gcongr
          _ = 1 / 2 := by norm_num
      have htr : ‖stirlingS c' (S.ω τ)‖ ≤ ‖stirlingS c' (S.ω τ) - 1‖ + ‖(1 : ℂ)‖ := by
        calc ‖stirlingS c' (S.ω τ)‖ = ‖(stirlingS c' (S.ω τ) - 1) + 1‖ := by ring_nf
          _ ≤ ‖stirlingS c' (S.ω τ) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      rw [norm_one] at htr; linarith only [htr, hsub, hle]
    have hz_re : 0 < (1 / 2 + (c' : ℂ) * S.ω τ).re := by
      have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
      simp only [Complex.add_re, h12, Complex.re_ofReal_mul]
      have hcw := mul_nonneg hc'_pos.le hω_re
      linarith only [hcw]
    have h_st := gamma_mul_two_pi_t_cpow_neg hc'_pos (ω := S.ω τ) (b := b) hω_re hω_ne hb_re_pos
    rw [← ht_eq] at h_st
    refine ⟨hz_re, hS_bd, ?_⟩
    unfold mellinDensityIntegrand
    dsimp only
    rw [mellinMGEntire_of_re_pos g hz_re]
    calc Complex.Gamma (1 / 2 + (c' : ℂ) * S.ω τ) *
          (2 * (Real.pi : ℂ) * t) ^ (-(1 / 2 + (c' : ℂ) * S.ω τ)) *
          mellinMG g (1 / 2 + (c' : ℂ) * S.ω τ)
        = (Complex.Gamma (1 / 2 + (c' : ℂ) * S.ω τ) *
            (2 * (Real.pi : ℂ) * t) ^ (-(1 / 2 + (c' : ℂ) * S.ω τ))) *
            mellinMG g (1 / 2 + (c' : ℂ) * S.ω τ) := rfl
      _ = _ := by rw [h_st]; ring
  have hpt_strip_prod : ∀ (hstr : S.isStrip = true), ∀ τ ∈ Icc S.a S.b,
      ‖mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖ ≤
        (K_seg / M_g) * ‖tildeWV c' g (S.ζ τ)‖ *
          Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) := by
    intro hstr τ hτ
    obtain ⟨hz_re, hS_bd, hmel_eq⟩ := hpt_stirling τ hτ
    have hω'_bd := (hω_bd τ hτ).2.2.2
    have hω_ζ := (S.hζ_strip hstr τ hτ).2.2.1
    have hstrip_id : mellinDensityIntegrand c' g t (S.ω τ) =
        t ^ (-(1 / 2 : ℂ)) * stirlingS c' (S.ω τ) *
          Complex.exp ((c' : ℂ) * chartPhiV (S.ζ τ) b - (c' : ℂ) * tipL b) *
          tildeWV c' g (S.ζ τ) := by
      rw [hmel_eq, ← mellinMGEntire_of_re_pos g hz_re]
      unfold tildeWV chartPhiV
      rw [← hω_ζ]
      have hex : Complex.exp ((c' : ℂ) * ComplexBessel.stirlingJ (S.ω τ) b) =
          Complex.exp ((c' : ℂ) * (chartUpsilon (S.ζ τ) +
              ComplexBessel.stirlingJ (S.ω τ) b + tipL b) - (c' : ℂ) * tipL b) *
            Complex.exp (-(c' : ℂ) * chartUpsilon (S.ζ τ)) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [hex]; ring
    rw [norm_mul, hstrip_id, norm_mul, norm_mul, norm_mul, Complex.norm_exp]
    have hexp_eq : Real.exp (((c' : ℂ) * chartPhiV (S.ζ τ) b - (c' : ℂ) * tipL b).re) =
        Real.exp (-(c' * (tipL b).re)) * airyEnv u *
          Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) := by
      rw [← hair_eq, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [Complex.sub_re, Complex.re_ofReal_mul]
      ring
    rw [hexp_eq]
    calc ‖t ^ (-(1 / 2 : ℂ))‖ * ‖stirlingS c' (S.ω τ)‖ *
            (Real.exp (-(c' * (tipL b).re)) * airyEnv u *
              Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re))) *
            ‖tildeWV c' g (S.ζ τ)‖ * ‖S.ω' τ‖
        ≤ ((2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ))) * 2 *
            (Real.exp (-(c' * (tipL b).re)) * airyEnv u *
              Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re))) *
            ‖tildeWV c' g (S.ζ τ)‖ * P.C_d := by
          have := xiStar_pos; have := airyEnv_pos u; gcongr
      _ = (K_seg / M_g) * ‖tildeWV c' g (S.ζ τ)‖ *
            Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) := by
          rw [hK_seg_eq]; field_simp [hM_pos.ne']; ring
  -- Unified ray case handler for `.upperRay` (`d τ = t_max - τ`) and `.lowerRay` (`d τ = τ`)
  have hray_unified : ∀ (hstr : S.isStrip = true) (t_max : ℝ) (ht_nn : 0 ≤ t_max)
      (ha_eq : S.a = 0) (hb_eq_t : S.b = t_max) (d : ℝ → ℝ),
      Continuous d →
      (∫ τ in (0 : ℝ)..t_max, Real.exp (-(c' * P.c_γ * ρ) * d τ ^ 2) ≤
        (Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)) →
      (∀ τ ∈ Icc (0 : ℝ) t_max, ‖S.ζ τ - s‖ = d τ ∧
        (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re - P.c_γ * ρ * d τ ^ 2) →
      ‖∫ τ in S.a..S.b, mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖ ≤
        K_seg * B_seg_unit := by
    intro hstr t_max ht_nn ha_eq hb_eq_t d hd_cont hgauss hray_d
    set α_g : ℝ := c' * P.c_γ * ρ
    have hα_g_pos : 0 < α_g := mul_pos (mul_pos hc'_pos P.hc_γ_pos) hρ_pos
    have hpt_ray : ∀ τ ∈ Icc (0 : ℝ) t_max,
        ‖mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖ ≤
          (K_seg * W_pt) * Real.exp (-α_g * d τ ^ 2) + K_seg * C_tail_u := by
      intro τ hτ
      have hτ' : τ ∈ Icc S.a S.b := by rwa [ha_eq, hb_eq_t]
      have hbase := hpt_strip_prod hstr τ hτ'
      obtain ⟨hdist_eq, hphi_bd⟩ := hray_d τ hτ
      have hζ_d := S.hζ_strip hstr τ hτ'
      have hζ_cl : S.ζ τ ∈ stripClosed := ⟨hζ_d.1, hζ_d.2.1.trans (by norm_num)⟩
      have hexp_gauss : Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
          Real.exp (-α_g * d τ ^ 2) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : (chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re ≤
            -P.c_γ * ρ * d τ ^ 2 := by linarith only [hphi_bd]
        have hm := mul_le_mul_of_nonneg_left h1 hc'_pos.le
        dsimp [α_g]; linarith only [hm]
      by_cases hwin : d τ ≤ s.re / 4
      · have hdist_win : ‖S.ζ τ - s‖ ≤ s.re / 4 := hdist_eq.trans_le hwin
        have hwv := hwin_wv (S.ζ τ) hζ_cl hdist_win
        have h1 : (K_seg / M_g) * ‖tildeWV c' g (S.ζ τ)‖ *
              Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
            (K_seg * W_pt) * Real.exp (-α_g * d τ ^ 2) := by
          calc (K_seg / M_g) * ‖tildeWV c' g (S.ζ τ)‖ *
                  Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re))
              ≤ (K_seg / M_g) * (M_g * W_pt) * Real.exp (-α_g * d τ ^ 2) :=
                hstrip_mul_le (mul_nonneg hM_pos.le hW_pt_nn) hwv (Real.exp_pos _).le hexp_gauss
            _ = (K_seg * W_pt) * Real.exp (-α_g * d τ ^ 2) := by
                field_simp [hM_pos.ne']
        have hct_nn : 0 ≤ K_seg * C_tail_u := mul_nonneg hK_seg_pos.le hC_tail_nn
        linarith only [hbase, h1, hct_nn]
      · have hgt : s.re / 4 ≤ d τ := le_of_not_ge hwin
        have hsq_ge : (s.re / 4) ^ 2 ≤ d τ ^ 2 :=
          pow_le_pow_left₀ (div_nonneg hs_re_pos.le (by norm_num)) hgt 2
        have hexp_tail : Real.exp (-α_g * d τ ^ 2) ≤
            Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : κ_all * c' ^ (5 / 6 : ℝ) ≤ α_g * (s.re / 4) ^ 2 := by
            have hcγ_nn := (div_pos P.hc_γ_pos (by norm_num : (0 : ℝ) < 16)).le
            calc κ_all * c' ^ (5 / 6 : ℝ)
                ≤ ((P.c_γ / 16) * (25 / 9 : ℝ) * ρ_min_Z ^ 3) * c' ^ (5 / 6 : ℝ) :=
                  mul_le_mul_of_nonneg_right hκ_ray (Real.rpow_nonneg hc'_pos.le _)
              _ = (P.c_γ / 16) * ((25 / 9 : ℝ) * ρ_min_Z ^ 3 * c' ^ (5 / 6 : ℝ)) := by ring
              _ ≤ (P.c_γ / 16) * (c' * ρ * s.re ^ 2) :=
                  mul_le_mul_of_nonneg_left hc_ρ_sre_sq hcγ_nn
              _ = α_g * (s.re / 4) ^ 2 := by dsimp [α_g]; ring
          have h2 : α_g * (s.re / 4) ^ 2 ≤ α_g * d τ ^ 2 :=
            mul_le_mul_of_nonneg_left hsq_ge hα_g_pos.le
          linarith only [h1, h2]
        have hwv_s4 : ‖tildeWV c' g (S.ζ τ)‖ ≤ max W.C_S4 W.C_S2 * M_g := by
          have h0 := W.hS4 hc'_S4 hg (S.ζ τ) hζ_cl
          rw [← hM_eq] at h0
          exact h0.trans (mul_le_mul_of_nonneg_right (le_max_left W.C_S4 W.C_S2) hM_pos.le)
        have h1 : (K_seg / M_g) * ‖tildeWV c' g (S.ζ τ)‖ *
              Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
            K_seg * C_tail_u := by
          calc (K_seg / M_g) * ‖tildeWV c' g (S.ζ τ)‖ *
                  Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re))
              ≤ (K_seg / M_g) * (max W.C_S4 W.C_S2 * M_g) *
                  Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) :=
                hstrip_mul_le (mul_nonneg hCS_max_pos.le hM_pos.le) hwv_s4
                  (Real.exp_pos _).le (hexp_gauss.trans hexp_tail)
            _ = K_seg * C_tail_u := by dsimp [C_tail_u]; field_simp [hM_pos.ne']
        have hcw_nn : 0 ≤ (K_seg * W_pt) * Real.exp (-α_g * d τ ^ 2) :=
          mul_nonneg (mul_nonneg hK_seg_pos.le hW_pt_nn) (Real.exp_pos _).le
        linarith only [hbase, h1, hcw_nn]
    have hf_cont0 : ContinuousOn
        (fun τ => ‖mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖) (Icc 0 t_max) := by
      rwa [← ha_eq, ← hb_eq_t]
    have ht_le1 : t_max ≤ 1 := by
      have h1 := hba; rw [ha_eq, hb_eq_t, sub_zero] at h1; exact h1
    have hres := ray_seg_integral_le ha_eq hb_eq_t ht_nn ht_le1 hα_g_pos
      hK_seg_pos.le hW_pt_nn hC_tail_nn hd_cont hf_cont0 hgauss hpt_ray
    rwa [← hB_seg_eq] at hres
  cases hstr : S.isStrip
  · -- `S.isStrip = false`: crude left-edge piece (`lemma_S2`)
    refine const_seg_integral_le S.hab hba hK_seg_pos.le hC_tail_nn hC_tail_le_B hf_cont ?_
    intro τ hτ
    obtain ⟨_, hS_bd, hmel_eq⟩ := hpt_stirling τ hτ
    have hω'_bd := (hω_bd τ hτ).2.2.2
    obtain ⟨hμ₀_le, hEc_le⟩ := hnonstrip hstr τ hτ
    have hS2_bd := hS2_P hμ₀_le
    rw [norm_mul, hmel_eq, norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
    have hexp_ec : Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
        Real.exp (c' * ComplexBessel.crudeExponentB (S.ω τ)) ≤
        Real.exp (-(c' * (tipL b).re)) * airyEnv u * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) := by
      rw [← hair_eq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hEc_def : crudeExponentEc (S.ω τ) b =
          ComplexBessel.crudeExponentB (S.ω τ) + (ComplexBessel.stirlingJ (S.ω τ) b).re +
            (tipL b).re := rfl
      have h1 : c' * crudeExponentEc (S.ω τ) b ≤
          c' * (chartPhiV s b).re - c' * P.c_γ * ρ * s.re ^ 2 := by
        have hm := mul_le_mul_of_nonneg_left hEc_le hc'_pos.le
        linarith only [hm]
      have h2 : κ_all * c' ^ (5 / 6 : ℝ) ≤ c' * P.c_γ * ρ * s.re ^ 2 := by
        have hcγ_nn := (div_pos P.hc_γ_pos (by norm_num : (0 : ℝ) < 16)).le
        have hkr : ((P.c_γ / 16) * (25 / 9 : ℝ) * ρ_min_Z ^ 3) * c' ^ (5 / 6 : ℝ) ≤
            (P.c_γ / 16) * (c' * ρ * s.re ^ 2) := by
          calc ((P.c_γ / 16) * (25 / 9 : ℝ) * ρ_min_Z ^ 3) * c' ^ (5 / 6 : ℝ)
              = (P.c_γ / 16) * ((25 / 9 : ℝ) * ρ_min_Z ^ 3 * c' ^ (5 / 6 : ℝ)) := by ring
            _ ≤ (P.c_γ / 16) * (c' * ρ * s.re ^ 2) :=
                mul_le_mul_of_nonneg_left hc_ρ_sre_sq hcγ_nn
        have h16 : (P.c_γ / 16) * (c' * ρ * s.re ^ 2) ≤ c' * P.c_γ * ρ * s.re ^ 2 := by
          have hnn : 0 ≤ P.c_γ * (c' * ρ * s.re ^ 2) :=
            mul_nonneg P.hc_γ_pos.le (mul_nonneg (mul_nonneg hc'_pos.le hρ_pos.le) (sq_nonneg _))
          linarith only [hnn]
        exact (mul_le_mul_of_nonneg_right hκ_ray (Real.rpow_nonneg hc'_pos.le _)).trans
          (hkr.trans h16)
      rw [hEc_def, mul_add, mul_add] at h1
      linarith only [h1, h2]
    have hCS2_max : W.C_S2 ≤ max W.C_S4 W.C_S2 := le_max_right _ _
    have hK_pref_nn : 0 ≤ (4 * Real.sqrt 3 / xiStar) * P.C_d * M_g * c' ^ (-(1 / 2 : ℝ)) := by
      have := xiStar_pos; have := P.hC_d_pos; positivity
    calc ‖t ^ (-(1 / 2 : ℂ))‖ * ‖stirlingS c' (S.ω τ)‖ *
            Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
            ‖mellinMG g (1 / 2 + (c' : ℂ) * S.ω τ)‖ * ‖S.ω' τ‖
        ≤ ((2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ))) * 2 *
            Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
            (W.C_S2 * Real.exp (c' * ComplexBessel.crudeExponentB (S.ω τ)) * M_g) *
            P.C_d := by
          have := xiStar_pos; have := W.hCS2; gcongr
      _ = ((4 * Real.sqrt 3 / xiStar) * P.C_d * M_g * c' ^ (-(1 / 2 : ℝ)) * W.C_S2) *
            (Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
              Real.exp (c' * ComplexBessel.crudeExponentB (S.ω τ))) := by ring
      _ ≤ ((4 * Real.sqrt 3 / xiStar) * P.C_d * M_g * c' ^ (-(1 / 2 : ℝ)) * max W.C_S4 W.C_S2) *
            (Real.exp (-(c' * (tipL b).re)) * airyEnv u * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hCS2_max hK_pref_nn) hexp_ec
            (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
            (mul_nonneg hK_pref_nn hCS_max_pos.le)
      _ = K_seg * C_tail_u := by rw [hK_seg_eq]; dsimp [C_tail_u]; ring
  · -- `S.isStrip = true`: case split on `S.kind`
    cases hkind : S.kind
    · -- `.upperRay`
      obtain ⟨t_max, ht_max_nn, ha_eq, hb_eq_t, _, hray⟩ := h_ur hstr hkind
      exact hray_unified hstr t_max ht_max_nn ha_eq hb_eq_t (fun τ => t_max - τ)
        (continuous_const.sub continuous_id)
        (integral_exp_neg_mul_sub_sq_le (mul_pos (mul_pos hc'_pos P.hc_γ_pos) hρ_pos) ht_max_nn)
        (fun τ hτ => ⟨(hray τ hτ).1, (hray τ hτ).2.2⟩)
    · -- `.lowerRay`
      obtain ⟨t_max, ht_max_nn, ha_eq, hb_eq_t, _, hray⟩ := h_lr hstr hkind
      exact hray_unified hstr t_max ht_max_nn ha_eq hb_eq_t (fun τ => τ)
        continuous_id
        (integral_exp_neg_mul_sq_le (mul_pos (mul_pos hc'_pos P.hc_γ_pos) hρ_pos) ht_max_nn)
        (fun τ hτ => ⟨(hray τ hτ).1, (hray τ hτ).2.2⟩)
    · -- `.arcRadial`
      refine const_seg_integral_le S.hab hba hK_seg_pos.le hC_tail_nn hC_tail_le_B hf_cont ?_
      intro τ hτ
      have hbase := hpt_strip_prod hstr τ hτ
      have hphi_bd := h_ar hstr hkind τ hτ
      have hζ_d := S.hζ_strip hstr τ hτ
      have hζ_cl : S.ζ τ ∈ stripClosed := ⟨hζ_d.1, hζ_d.2.1.trans (by norm_num)⟩
      have hwv_s4 : ‖tildeWV c' g (S.ζ τ)‖ ≤ max W.C_S4 W.C_S2 * M_g := by
        have h0 := W.hS4 hc'_S4 hg (S.ζ τ) hζ_cl
        rw [← hM_eq] at h0
        exact h0.trans (mul_le_mul_of_nonneg_right (le_max_left W.C_S4 W.C_S2) hM_pos.le)
      have hexp_arc : Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
          Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : (chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re ≤ -P.κ_arc * ρ ^ 3 := by
          linarith only [hphi_bd]
        have hm := mul_le_mul_of_nonneg_left h1 hc'_pos.le
        have hρ_cube : ρ_min_Z ^ 3 ≤ ρ ^ 3 := pow_le_pow_left₀ hρ_min_pos.le hρ_ge_min 3
        have h2 : κ_all * c' ^ (5 / 6 : ℝ) ≤ c' * (P.κ_arc * ρ ^ 3) := by
          calc κ_all * c' ^ (5 / 6 : ℝ) ≤ (P.κ_arc * ρ_min_Z ^ 3) * c' :=
                mul_le_mul hκ_arc hc56_le_c (Real.rpow_nonneg hc'_pos.le _)
                  (mul_nonneg P.hκ_arc_pos.le (pow_nonneg hρ_min_pos.le 3))
            _ = c' * (P.κ_arc * ρ_min_Z ^ 3) := mul_comm _ _
            _ ≤ c' * (P.κ_arc * ρ ^ 3) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hρ_cube P.hκ_arc_pos.le) hc'_pos.le
        linarith only [hm, h2]
      calc ‖mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖
          ≤ (K_seg / M_g) * (max W.C_S4 W.C_S2 * M_g) *
              Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) :=
            hbase.trans (hstrip_mul_le (mul_nonneg hCS_max_pos.le hM_pos.le) hwv_s4
              (Real.exp_pos _).le hexp_arc)
        _ = K_seg * C_tail_u := by dsimp [C_tail_u]; field_simp [hM_pos.ne']
    · -- `.crudeEdge`: impossible when `S.isStrip = true`
      exact absurd hkind (h_no_crude hstr)
    · -- `.fixedStrip`
      refine const_seg_integral_le S.hab hba hK_seg_pos.le hC_tail_nn hC_tail_le_B hf_cont ?_
      intro τ hτ
      have hbase := hpt_strip_prod hstr τ hτ
      have hphi_bd := h_fs hstr hkind τ hτ
      have hζ_d := S.hζ_strip hstr τ hτ
      have hζ_cl : S.ζ τ ∈ stripClosed := ⟨hζ_d.1, hζ_d.2.1.trans (by norm_num)⟩
      have hwv_s4 : ‖tildeWV c' g (S.ζ τ)‖ ≤ max W.C_S4 W.C_S2 * M_g := by
        have h0 := W.hS4 hc'_S4 hg (S.ζ τ) hζ_cl
        rw [← hM_eq] at h0
        exact h0.trans (mul_le_mul_of_nonneg_right (le_max_left W.C_S4 W.C_S2) hM_pos.le)
      have hexp_fs : Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
          Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : (chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re ≤ -P.κ_strip := by
          linarith only [hphi_bd]
        have hm := mul_le_mul_of_nonneg_left h1 hc'_pos.le
        have h2 : κ_all * c' ^ (5 / 6 : ℝ) ≤ c' * P.κ_strip := by
          calc κ_all * c' ^ (5 / 6 : ℝ) ≤ P.κ_strip * c' :=
                mul_le_mul hκ_strip hc56_le_c (Real.rpow_nonneg hc'_pos.le _) P.hκ_strip_pos.le
            _ = c' * P.κ_strip := mul_comm _ _
        linarith only [hm, h2]
      calc ‖mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖
          ≤ (K_seg / M_g) * (max W.C_S4 W.C_S2 * M_g) *
              Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) :=
            hbase.trans (hstrip_mul_le (mul_nonneg hCS_max_pos.le hM_pos.le) hwv_s4
              (Real.exp_pos _).le hexp_fs)
        _ = K_seg * C_tail_u := by dsimp [C_tail_u]; field_simp [hM_pos.ne']

private lemma lemma_Z_combine_envelope (W : ZWitness) (P : ZPConfig)
    {b_hi c' Λ φ ρ κ_all C_pref B_seg_unit C_B : ℝ}
    {g : ℝ → ℝ} {u : ℂ}
    (hb_hi_pos : 0 < b_hi) (hc'_pos : 0 < c') (hc'_ge1 : 1 ≤ c')
    (hΛ : 1 ≤ Λ) (hκ_all_pos : 0 < κ_all) (hκ_le_D : κ_all ≤ W.d_D)
    (hC_pref_pos : 0 < C_pref)
    (hu_pos : 0 < ‖u‖) (hu_bhi : ‖u‖ ≤ b_hi ^ 2 * c' ^ (2 / 3 : ℝ))
    (hu_re_pos : 0 < (u ^ (1 / 2 : ℂ)).re)
    (hu_re_eq : (u ^ (1 / 2 : ℂ)).re = Real.sqrt ‖u‖ * Real.sin φ)
    (hsin_pos : 0 < Real.sin φ) (hsin_le1 : Real.sin φ ≤ 1)
    (_hρ_pos : 0 < ρ)
    (hρ_lo : (9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt ‖u‖) ≤ ρ)
    (hB_seg_eq : B_seg_unit =
      (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
        ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)) +
      max W.C_S4 W.C_S2 * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)))
    (hCB_ge : 12 * C_pref * Real.pi / Real.sqrt ((9 / 10 : ℝ) * P.c_γ * kappaV) *
        b_hi ^ (5 / 2 : ℝ) +
      (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * b_hi ^ 3 * (4 / κ_all ^ 2) ≤ C_B)
    (hP_norm : ‖truncatedMellinP c' dpT0 g u‖ ≤
      12 * C_pref * c' ^ (1 / 3 : ℝ) * B_seg_unit * airyEnv u)
    (hDp_u : ‖truncatedMellinP c' dpT0 g u - virasoroPsiTilde c' g u‖ ≤
      W.C_D * Real.exp (-W.d_D * c') * airyEnv u) :
    ‖virasoroPsiTilde c' g u‖ ≤
      C_B * Λ * airyEnv u *
        (u ^ (1 / 2 : ℂ)).re ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ)) := by
  set a' : ℝ := Real.sqrt ‖u‖
  have ha'_pos : 0 < a' := Real.sqrt_pos.mpr hu_pos
  set c_γ_kap : ℝ := (9 / 10 : ℝ) * P.c_γ * kappaV
  have hc_γ_kap_pos : 0 < c_γ_kap := by
    have := P.hc_γ_pos; have := kappaV_pos; positivity
  set C_win_tot : ℝ := 12 * C_pref * Real.pi / Real.sqrt c_γ_kap * b_hi ^ (5 / 2 : ℝ)
  set C_tail_tot : ℝ := (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * b_hi ^ 3 * (4 / κ_all ^ 2)
  have hDp_exp_le : Real.exp (-W.d_D * c') ≤ Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) := by
    refine Real.exp_le_exp.mpr ?_
    have hc56_le : c' ^ (5 / 6 : ℝ) ≤ c' :=
      (Real.rpow_le_rpow_of_exponent_le hc'_ge1 (by norm_num)).trans_eq (Real.rpow_one c')
    have hprod := mul_le_mul hκ_le_D hc56_le (Real.rpow_nonneg hc'_pos.le _) W.hd_D.le
    linarith only [hprod]
  have hDp_c13 : W.C_D * Real.exp (-W.d_D * c') * airyEnv u ≤
      W.C_D * c' ^ (1 / 3 : ℝ) * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) * airyEnv u := by
    have hc13_ge1 : 1 ≤ c' ^ (1 / 3 : ℝ) := Real.one_le_rpow hc'_ge1 (by norm_num)
    have hair_nn : 0 ≤ airyEnv u := (airyEnv_pos u).le
    calc W.C_D * Real.exp (-W.d_D * c') * airyEnv u
        ≤ W.C_D * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) * airyEnv u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDp_exp_le W.hC_D.le) hair_nn
      _ = W.C_D * 1 * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) * airyEnv u := by ring
      _ ≤ W.C_D * c' ^ (1 / 3 : ℝ) * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) * airyEnv u :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hc13_ge1 W.hC_D.le) (Real.exp_pos _).le) hair_nn
  set u_re : ℝ := (u ^ (1 / 2 : ℂ)).re
  set u_n : ℝ := ‖u‖
  have hu_re_ub : u_re ≤ u_n ^ (1 / 2 : ℝ) := by
    rw [hu_re_eq, ← Real.sqrt_eq_rpow]
    exact mul_le_of_le_one_right ha'_pos.le hsin_le1
  have hfac_pos : 0 < u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ) := by positivity
  have hwin_prod_le :
      (12 * C_pref * c' ^ (1 / 3 : ℝ) *
          ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
            ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)))) *
        (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) ≤ C_win_tot * Λ := by
    have hsqrt_ρ_lb : Real.sqrt c_γ_kap * c' ^ (1 / 3 : ℝ) * u_n ^ (1 / 4 : ℝ) ≤
        Real.sqrt (c' * P.c_γ * ρ) := by
      have h1 : c_γ_kap * c' ^ (2 / 3 : ℝ) * u_n ^ (1 / 2 : ℝ) ≤ c' * P.c_γ * ρ := by
        have hc23 : c' * c' ^ (-(1 / 3 : ℝ)) = c' ^ (2 / 3 : ℝ) := by
          rw [← Real.rpow_one_add' hc'_pos.le (by norm_num : (1 : ℝ) + -(1 / 3 : ℝ) ≠ 0)]
          norm_num
        have ha_rpow : a' = u_n ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow u_n
        calc c_γ_kap * c' ^ (2 / 3 : ℝ) * u_n ^ (1 / 2 : ℝ)
            = c' * P.c_γ * ((9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a')) := by
              rw [← hc23, ← ha_rpow]; dsimp [c_γ_kap]; ring
          _ ≤ c' * P.c_γ * ρ :=
              mul_le_mul_of_nonneg_left hρ_lo (mul_nonneg hc'_pos.le P.hc_γ_pos.le)
      have hrt := Real.sqrt_le_sqrt h1
      have hlhs : Real.sqrt (c_γ_kap * c' ^ (2 / 3 : ℝ) * u_n ^ (1 / 2 : ℝ)) =
          Real.sqrt c_γ_kap * c' ^ (1 / 3 : ℝ) * u_n ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hc_γ_kap_pos.le,
          Real.sqrt_eq_rpow (c' ^ (2 / 3 : ℝ)), Real.sqrt_eq_rpow (u_n ^ (1 / 2 : ℝ)),
          ← Real.rpow_mul hc'_pos.le, ← Real.rpow_mul hu_pos.le]
        norm_num
      rwa [hlhs] at hrt
    have hinv_sqrt : (Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ) ≤
        (Real.pi / (2 * Real.sqrt c_γ_kap)) * c' ^ (-(1 / 3 : ℝ)) * u_n ^ (-(1 / 4 : ℝ)) := by
      have h1 : (Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ) ≤
          (Real.pi / 2) / (Real.sqrt c_γ_kap * c' ^ (1 / 3 : ℝ) * u_n ^ (1 / 4 : ℝ)) := by
        gcongr
      refine h1.trans_eq ?_
      rw [Real.rpow_neg hc'_pos.le, Real.rpow_neg hu_pos.le]
      field_simp [hc_γ_kap_pos.ne']
    have hure_sin : (u_re ^ (3 / 2 : ℝ) / Real.sin φ) * u_n ^ (3 / 4 : ℝ) ≤ u_n ^ (3 / 2 : ℝ) := by
      have hsplit : u_re ^ (3 / 2 : ℝ) = u_re * u_re ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_one_add' hu_re_pos.le (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0)]
        norm_num
      have hdiv_sin : u_re / Real.sin φ = u_n ^ (1 / 2 : ℝ) := by
        rw [show u_re = a' * Real.sin φ from hu_re_eq, mul_div_cancel_right₀ _ hsin_pos.ne']
        exact Real.sqrt_eq_rpow u_n
      have hure_14 : u_re ^ (1 / 2 : ℝ) ≤ u_n ^ (1 / 4 : ℝ) := by
        calc u_re ^ (1 / 2 : ℝ) ≤ (u_n ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow hu_re_pos.le hu_re_ub (by norm_num)
          _ = u_n ^ (1 / 4 : ℝ) := by rw [← Real.rpow_mul hu_pos.le]; norm_num
      calc (u_re ^ (3 / 2 : ℝ) / Real.sin φ) * u_n ^ (3 / 4 : ℝ)
          = (u_re / Real.sin φ) * u_re ^ (1 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ) := by
            rw [hsplit]; ring
        _ = u_n ^ (1 / 2 : ℝ) * u_re ^ (1 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ) := by rw [hdiv_sin]
        _ ≤ u_n ^ (1 / 2 : ℝ) * u_n ^ (1 / 4 : ℝ) * u_n ^ (3 / 4 : ℝ) := by gcongr
        _ = u_n ^ (3 / 2 : ℝ) := by
            rw [← Real.rpow_add hu_pos, ← Real.rpow_add hu_pos]; norm_num
    have hun_54 : c' ^ (-(5 / 6 : ℝ)) * (u_n ^ (-(1 / 4 : ℝ)) * u_n ^ (3 / 2 : ℝ)) ≤
        b_hi ^ (5 / 2 : ℝ) := by
      have hsum : u_n ^ (-(1 / 4 : ℝ)) * u_n ^ (3 / 2 : ℝ) = u_n ^ (5 / 4 : ℝ) := by
        rw [← Real.rpow_add hu_pos]; norm_num
      have hub : u_n ^ (5 / 4 : ℝ) ≤ b_hi ^ (5 / 2 : ℝ) * c' ^ (5 / 6 : ℝ) := by
        calc u_n ^ (5 / 4 : ℝ) ≤ (b_hi ^ 2 * c' ^ (2 / 3 : ℝ)) ^ (5 / 4 : ℝ) :=
              Real.rpow_le_rpow hu_pos.le hu_bhi (by norm_num)
          _ = b_hi ^ (5 / 2 : ℝ) * c' ^ (5 / 6 : ℝ) := by
              rw [Real.mul_rpow (sq_nonneg _) (Real.rpow_nonneg hc'_pos.le _),
                ← Real.rpow_natCast b_hi 2, ← Real.rpow_mul hb_hi_pos.le,
                ← Real.rpow_mul hc'_pos.le]
              norm_num
      rw [hsum]
      calc c' ^ (-(5 / 6 : ℝ)) * u_n ^ (5 / 4 : ℝ)
          ≤ c' ^ (-(5 / 6 : ℝ)) * (b_hi ^ (5 / 2 : ℝ) * c' ^ (5 / 6 : ℝ)) := by gcongr
        _ = b_hi ^ (5 / 2 : ℝ) * (c' ^ (-(5 / 6 : ℝ)) * c' ^ (5 / 6 : ℝ)) := by ring
        _ = b_hi ^ (5 / 2 : ℝ) := by
            rw [← Real.rpow_add hc'_pos, neg_add_cancel, Real.rpow_zero, mul_one]
    have hc13_cancel : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero]
    calc (12 * C_pref * c' ^ (1 / 3 : ℝ) *
            ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
              ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)))) *
          (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ))
        ≤ (12 * C_pref * c' ^ (1 / 3 : ℝ) *
            ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
              ((Real.pi / (2 * Real.sqrt c_γ_kap)) * c' ^ (-(1 / 3 : ℝ)) * u_n ^ (-(1 / 4 : ℝ))))) *
          (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) := by
          gcongr
      _ = (12 * C_pref * Real.pi / Real.sqrt c_γ_kap) * Λ *
            (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ))) *
            (c' ^ (-(5 / 6 : ℝ)) * (u_n ^ (-(1 / 4 : ℝ)) *
              ((u_re ^ (3 / 2 : ℝ) / Real.sin φ) * u_n ^ (3 / 4 : ℝ)))) := by ring
      _ ≤ (12 * C_pref * Real.pi / Real.sqrt c_γ_kap) * Λ * 1 *
            (c' ^ (-(5 / 6 : ℝ)) * (u_n ^ (-(1 / 4 : ℝ)) * u_n ^ (3 / 2 : ℝ))) := by
          rw [hc13_cancel]; gcongr
      _ ≤ (12 * C_pref * Real.pi / Real.sqrt c_γ_kap) * Λ * 1 * b_hi ^ (5 / 2 : ℝ) := by
          gcongr
      _ = C_win_tot * Λ := by dsimp [C_win_tot]; ring
  have htail_prod_le :
      ((W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) *
          Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) *
        (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) ≤ C_tail_tot * Λ := by
    have hfac_ub : u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ) ≤ b_hi ^ 3 * c' := by
      have h1 : u_re ^ (3 / 2 : ℝ) ≤ u_n ^ (3 / 4 : ℝ) := by
        calc u_re ^ (3 / 2 : ℝ) ≤ (u_n ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) :=
              Real.rpow_le_rpow hu_re_pos.le hu_re_ub (by norm_num)
          _ = u_n ^ (3 / 4 : ℝ) := by rw [← Real.rpow_mul hu_pos.le]; norm_num
      have h2 : u_n ^ (3 / 2 : ℝ) ≤ b_hi ^ 3 * c' := by
        calc u_n ^ (3 / 2 : ℝ) ≤ (b_hi ^ 2 * c' ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) :=
              Real.rpow_le_rpow hu_pos.le hu_bhi (by norm_num)
          _ = b_hi ^ 3 * c' := by
              rw [Real.mul_rpow (sq_nonneg _) (Real.rpow_nonneg hc'_pos.le _),
                ← Real.rpow_natCast b_hi 2, ← Real.rpow_mul hb_hi_pos.le,
                ← Real.rpow_mul hc'_pos.le]
              norm_num
      calc u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)
          ≤ u_n ^ (3 / 4 : ℝ) * u_n ^ (3 / 4 : ℝ) := by gcongr
        _ = u_n ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hu_pos]; norm_num
        _ ≤ b_hi ^ 3 * c' := h2
    have hc43 : c' ^ (1 / 3 : ℝ) * c' = c' ^ (4 / 3 : ℝ) := by
      rw [← Real.rpow_add_one hc'_pos.ne']; norm_num
    have hexp_dom := rpow_four_thirds_mul_exp_neg_le hκ_all_pos hc'_ge1
    have hC_pos : 0 < W.C_D + 12 * C_pref * max W.C_S4 W.C_S2 := by
      have := W.hC_D; have := W.hCS4; positivity
    calc ((W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) *
            Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) *
          (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ))
        ≤ ((W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) *
            Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) * (b_hi ^ 3 * c') :=
          mul_le_mul_of_nonneg_left hfac_ub
            (mul_nonneg (mul_nonneg hC_pos.le (Real.rpow_nonneg hc'_pos.le _)) (Real.exp_pos _).le)
      _ = (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * b_hi ^ 3 *
            ((c' ^ (1 / 3 : ℝ) * c') * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) := by ring
      _ ≤ (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * b_hi ^ 3 * (4 / κ_all ^ 2) := by
          rw [hc43]; gcongr
      _ = C_tail_tot * 1 := by dsimp [C_tail_tot]; ring
      _ ≤ C_tail_tot * Λ := by dsimp [C_tail_tot]; gcongr
  have hPsi_tri : ‖virasoroPsiTilde c' g u‖ ≤
      ‖truncatedMellinP c' dpT0 g u‖ + ‖truncatedMellinP c' dpT0 g u - virasoroPsiTilde c' g u‖ := by
    calc ‖virasoroPsiTilde c' g u‖
        = ‖truncatedMellinP c' dpT0 g u - (truncatedMellinP c' dpT0 g u - virasoroPsiTilde c' g u)‖ := by
          ring_nf
      _ ≤ _ := norm_sub_le _ _
  have hPsi_prod_le :
      ‖virasoroPsiTilde c' g u‖ * (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) ≤
        (C_B * Λ) * airyEnv u := by
    have hsum_bd : ‖virasoroPsiTilde c' g u‖ ≤
        (12 * C_pref * c' ^ (1 / 3 : ℝ) *
            ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
              ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ))) +
          (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) *
            Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) * airyEnv u := by
      have hp1 := hP_norm
      have hp2 := hDp_u.trans hDp_c13
      have hcomb : 12 * C_pref * c' ^ (1 / 3 : ℝ) * B_seg_unit * airyEnv u +
            W.C_D * c' ^ (1 / 3 : ℝ) * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) * airyEnv u =
          (12 * C_pref * c' ^ (1 / 3 : ℝ) *
              ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
                ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ))) +
            (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) *
              Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) * airyEnv u := by
        rw [hB_seg_eq]; ring
      linarith only [hPsi_tri, hp1, hp2, hcomb]
    have hair_pos := airyEnv_pos u
    calc ‖virasoroPsiTilde c' g u‖ * (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ))
        ≤ ((12 * C_pref * c' ^ (1 / 3 : ℝ) *
              ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
                ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ))) *
            (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) +
            ((W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) *
              Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) *
            (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)))) * airyEnv u := by
          have hm := mul_le_mul_of_nonneg_right hsum_bd hfac_pos.le
          linarith only [hm]
      _ ≤ (C_win_tot * Λ + C_tail_tot * Λ) * airyEnv u := by gcongr
      _ = (C_win_tot + C_tail_tot) * Λ * airyEnv u := by ring
      _ ≤ (C_B * Λ) * airyEnv u := by gcongr
  have hinv_cancel : (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) *
      (u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ))) = 1 := by
    calc (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) *
          (u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ)))
        = (u_re ^ (3 / 2 : ℝ) * u_re ^ (-(3 / 2 : ℝ))) *
            (u_n ^ (3 / 4 : ℝ) * u_n ^ (-(3 / 4 : ℝ))) := by ring
      _ = 1 := by
          rw [← Real.rpow_add hu_re_pos, ← Real.rpow_add hu_pos,
            add_neg_cancel, add_neg_cancel, Real.rpow_zero, Real.rpow_zero, mul_one]
  have hinv_nn : 0 ≤ u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ)) := by positivity
  calc ‖virasoroPsiTilde c' g u‖
      = ‖virasoroPsiTilde c' g u‖ *
          ((u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) *
            (u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ)))) := by
        rw [hinv_cancel, mul_one]
    _ = (‖virasoroPsiTilde c' g u‖ * (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ))) *
          (u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ))) := by ring
    _ ≤ ((C_B * Λ) * airyEnv u) * (u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_right hPsi_prod_le hinv_nn
    _ = C_B * Λ * airyEnv u * u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ)) := by ring

/-! ### 4. Lemma Z (`lower_o1_two_edge.tex`, `vlo:Z`) -/

/-- **Lemma Z (interior multiplier bound implies the Airy envelope)** (`lower_o1_two_edge.tex`,
§J8, `vlo:Z`, lines 825–836):
for any compact scale band `0 < b_lo ≤ b_hi` with `b_hi ^ 2 ≤ zScaleCap`, there exist
`c_Z ≥ 10000` and `C_B ≥ 1` such that for all `c' ≥ c_Z`, `R` in `[b_lo^2 c'^{2/3}, b_hi^2 c'^{2/3} - 1]`,
`g ∈ TestClass virasoroProblem (c' / 12)` with `0 < M[g]`, and `Λ ≥ 1`:
if on the strip sector `S = {ζ ∈ stripClosed | ρ_R / 3 ≤ ‖ζ‖ ≤ 2 ρ_R, c'^{-1/12} ‖ζ‖ ≤ ζ.re}`
(with `ρ_R = kappaV * c'^{-1/3} * √R`) the strip multiplier satisfies
`‖tildeWV c' g ζ‖ ≤ M[g] * (Λ * c'^{-5/6} * ‖ζ‖ / ζ.re)`,
then `YVEnvBound (virasoroPsiTilde c' g) c' R (C_B * Λ)` holds. -/
theorem lemma_Z {b_lo b_hi : ℝ} (hb_lo : 0 < b_lo) (hb_le : b_lo ≤ b_hi)
    (hb_cap : b_hi ^ 2 ≤ zScaleCap) :
    ∃ c_Z C_B : ℝ, 10000 ≤ c_Z ∧ 1 ≤ C_B ∧
      ∀ {c' R Λ : ℝ}, c_Z ≤ c' → 1 ≤ Λ →
        b_lo ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R →
        R + 1 ≤ b_hi ^ 2 * c' ^ (2 / 3 : ℝ) →
        ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
          0 < virasoroProblem.cardyNorm (c' / 12) g →
          (∀ ζ ∈ stripClosed,
            kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R / 3 ≤ ‖ζ‖ →
            ‖ζ‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R) →
            c' ^ (-(1 / 12 : ℝ)) * ‖ζ‖ ≤ ζ.re →
            ‖tildeWV c' g ζ‖ ≤
              virasoroProblem.cardyNorm (c' / 12) g *
                (Λ * c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re)) →
          YVEnvBound (virasoroPsiTilde c' g) c' R (C_B * Λ) := by
  obtain ⟨W, hW_eq⟩ : ∃ x : ZWitness, x = zWitness := ⟨_, rfl⟩
  have hb_cap' : b_hi ^ 2 ≤ W.c₀_Z := by rw [hW_eq]; exact hb_cap
  have hb_hi_pos : 0 < b_hi := lt_of_lt_of_le hb_lo hb_le
  set ρ_min_Z : ℝ := (18 / 25 : ℝ) * kappaV * b_lo
  have hρ_min_pos : 0 < ρ_min_Z := mul_pos (mul_pos (by norm_num) kappaV_pos) hb_lo
  set κ_ray : ℝ := (dpConfig.c_γ / 16) * (25 / 9 : ℝ) * ρ_min_Z ^ 3
  have hκ_ray_pos : 0 < κ_ray :=
    mul_pos (mul_pos (div_pos dpConfig.hc_γ_pos (by norm_num)) (by norm_num)) (pow_pos hρ_min_pos 3)
  set κ_arc_Z : ℝ := dpConfig.κ_arc * ρ_min_Z ^ 3
  have hκ_arc_pos : 0 < κ_arc_Z := mul_pos dpConfig.hκ_arc_pos (pow_pos hρ_min_pos 3)
  set κ_all : ℝ := min (min κ_ray κ_arc_Z) (min dpConfig.κ_strip W.d_D)
  have hκ_all_pos : 0 < κ_all :=
    lt_min (lt_min hκ_ray_pos hκ_arc_pos) (lt_min dpConfig.hκ_strip_pos W.hd_D)
  set C_pref : ℝ := (innerCDxi * W.C_V / (2 * Real.pi)) * (4 * Real.sqrt 3 / xiStar) * dpConfig.C_d
  have hC_pref_pos : 0 < C_pref :=
    mul_pos (mul_pos (div_pos (mul_pos innerCDxi_pos W.hC_V)
      (mul_pos two_pos Real.pi_pos))
      (div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))) xiStar_pos))
      dpConfig.hC_d_pos
  set c_γ_kap : ℝ := (9 / 10 : ℝ) * dpConfig.c_γ * kappaV
  set C_win_tot : ℝ := 12 * C_pref * Real.pi / Real.sqrt c_γ_kap * b_hi ^ (5 / 2 : ℝ)
  set C_tail_tot : ℝ := (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * b_hi ^ 3 * (4 / κ_all ^ 2)
  obtain ⟨c_Z, hc_Z_eq⟩ : ∃ x : ℝ, x = max (max W.c_D (max W.c_S4 W.c_S2))
      (max W.c_V (max 10000 (max (48 / dpConfig.c_Γ) ((9 / b_lo ^ 2) ^ (3 / 2 : ℝ))))) := ⟨_, rfl⟩
  obtain ⟨C_B, hC_B_eq⟩ : ∃ x : ℝ, x = max 1 (C_win_tot + C_tail_tot) := ⟨_, rfl⟩
  refine ⟨c_Z, C_B, ?_, hC_B_eq ▸ le_max_left _ _, ?_⟩
  · rw [hc_Z_eq]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  intro c' R Λ hc' hΛ hR_lo hR_hi g hg hM_pos hsec u hu_im hu_lo hu_hi hsin_hyp
  have hc'_D : W.c_D ≤ c' :=
    (hc_Z_eq ▸ (le_max_left _ _).trans (le_max_left _ _)).trans hc'
  have hc'_S4 : W.c_S4 ≤ c' :=
    (hc_Z_eq ▸ (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc'
  have hc'_S2 : W.c_S2 ≤ c' :=
    (hc_Z_eq ▸ (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc'
  have hc'_V : W.c_V ≤ c' :=
    (hc_Z_eq ▸ (le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hc'_10000 : 10000 ≤ c' :=
    (hc_Z_eq ▸ (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc'
  have hc'_48 : 48 / dpConfig.c_Γ ≤ c' :=
    (hc_Z_eq ▸ (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc'
  have hc'_R9 : (9 / b_lo ^ 2) ^ (3 / 2 : ℝ) ≤ c' :=
    (hc_Z_eq ▸ (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc'
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have hc'_ge1 : 1 ≤ c' := by linarith only [hc'_10000]
  have hc'_24 : 24 ≤ c' := by linarith only [hc'_10000]
  -- Step 1: R ≥ 9 and comparability between ‖u‖, R, and c'^{2/3}
  have hR_ge9 : 9 ≤ R := by
    have h1 : 9 / b_lo ^ 2 ≤ c' ^ (2 / 3 : ℝ) := by
      calc 9 / b_lo ^ 2 = ((9 / b_lo ^ 2) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
            rw [← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ c' ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hc'_R9 (by norm_num)
    have h2 : 9 ≤ b_lo ^ 2 * c' ^ (2 / 3 : ℝ) := (div_le_iff₀' (sq_pos_of_pos hb_lo)).mp h1
    exact h2.trans hR_lo
  have hR_pos : 0 < R := by linarith only [hR_ge9]
  have hu_ge8 : 8 ≤ ‖u‖ := by linarith only [hR_ge9, hu_lo]
  have hu_pos : 0 < ‖u‖ := by linarith only [hu_ge8]
  have hu_ne : u ≠ 0 := norm_pos_iff.mp hu_pos
  have hu_bhi : ‖u‖ ≤ b_hi ^ 2 * c' ^ (2 / 3 : ℝ) := hu_hi.trans hR_hi
  have hu_Z : ‖u‖ ≤ W.c₀_Z * c' ^ (2 / 3 : ℝ) :=
    hu_bhi.trans (mul_le_mul_of_nonneg_right hb_cap' (Real.rpow_nonneg hc'_pos.le _))
  have hu_cb_D : u ∈ closedBall (0 : ℂ) (W.c₀_D * c' ^ (2 / 3 : ℝ)) :=
    mem_closedBall_zero_iff.mpr
      (hu_Z.trans (mul_le_mul_of_nonneg_right W.hc₀_Z_le_D (Real.rpow_nonneg hc'_pos.le _)))
  have hu_cb_in : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
    have hin_pos := innerChartRadius_pos
    have hle_in : W.c₀_D ≤ innerChartRadius := W.hc₀_D_le4.trans (by linarith only [hin_pos])
    exact closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right hle_in (Real.rpow_nonneg hc'_pos.le _)) hu_cb_D
  have hsqrt_u_lo : (4 / 5 : ℝ) * Real.sqrt R ≤ Real.sqrt ‖u‖ := by
    have h89 : (8 / 9 : ℝ) * R ≤ ‖u‖ := by linarith only [hR_ge9, hu_lo]
    have hsq : ((4 / 5 : ℝ) * Real.sqrt R) ^ 2 ≤ ‖u‖ := by
      rw [mul_pow, Real.sq_sqrt hR_pos.le]
      linarith only [h89, hR_pos]
    exact Real.le_sqrt_of_sq_le hsq
  have hsqrt_u_hi : Real.sqrt ‖u‖ ≤ (6 / 5 : ℝ) * Real.sqrt R := by
    have h109 : ‖u‖ ≤ (10 / 9 : ℝ) * R := by linarith only [hR_ge9, hu_hi]
    have hsq : ‖u‖ ≤ ((6 / 5 : ℝ) * Real.sqrt R) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hR_pos.le]
      linarith only [h109, hR_pos]
    exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by positivity))
  -- Step 2: Polar angle φ = (π - u.arg) / 2 and sin φ ≥ 2 c'^{-1/12}
  set a' : ℝ := Real.sqrt ‖u‖
  have ha'_pos : 0 < a' := Real.sqrt_pos.mpr hu_pos
  have ha'_sq : a' ^ 2 = ‖u‖ := Real.sq_sqrt hu_pos.le
  set φ : ℝ := (Real.pi - u.arg) / 2
  have hu_re_eq : (u ^ (1 / 2 : ℂ)).re = a' * Real.sin φ := cpow_half_re_eq_sqrt_mul_sin hu_ne
  have hu_re_pos : 0 < (u ^ (1 / 2 : ℂ)).re := by
    have h1 : 0 < 2 * c' ^ (-(1 / 12 : ℝ)) * a' := by positivity
    linarith only [h1, hsin_hyp]
  have hsin_lb : 2 * c' ^ (-(1 / 12 : ℝ)) ≤ Real.sin φ := by
    have h1 : a' * (2 * c' ^ (-(1 / 12 : ℝ))) ≤ a' * Real.sin φ := by
      linarith only [hsin_hyp, hu_re_eq]
    exact le_of_mul_le_mul_left h1 ha'_pos
  have hsin_pos : 0 < Real.sin φ := lt_of_lt_of_le (by positivity) hsin_lb
  have hsin_le1 : Real.sin φ ≤ 1 := Real.sin_le_one φ
  have hu_arg_nn : 0 ≤ u.arg := Complex.arg_nonneg_iff.mpr hu_im
  have hu_arg_lt : u.arg < Real.pi := by
    rcases lt_or_ge u.arg Real.pi with hlt | hge
    · exact hlt
    · exfalso
      have hpi : u.arg = Real.pi := le_antisymm (Complex.arg_le_pi u) hge
      have hφ0 : φ = 0 := by dsimp [φ]; rw [hpi, sub_self, zero_div]
      rw [hφ0, Real.sin_zero] at hsin_pos
      exact lt_irrefl 0 hsin_pos
  have hu_cut : ¬ (u.im = 0 ∧ u.re ≤ 0) := by
    rintro ⟨him0, hre_np⟩
    rcases eq_or_lt_of_le hre_np with hre0 | hre_neg
    · exact hu_ne (Complex.ext hre0 him0)
    · exact hu_arg_lt.ne (Complex.arg_eq_pi_iff.mpr ⟨hre_neg, him0⟩)
  have hφ_pos : 0 < φ := by dsimp [φ]; linarith only [hu_arg_lt]
  have hφ_le : φ ≤ Real.pi / 2 := by dsimp [φ]; linarith only [hu_arg_nn]
  have hu_polar : u = ((a' ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((Real.pi - 2 * φ : ℝ) : ℂ)) := by
    have hp := (Complex.norm_mul_exp_arg_mul_I u).symm
    rw [← ha'_sq] at hp
    conv_lhs => rw [hp]
    congr 1; congr 1
    dsimp [φ]; push_cast; ring
  -- Step 3: Saddle point s = ζp from W.h_saddle and exact potential airyEnv u
  have ha'_Z : a' ^ 2 * c' ^ (-(2 / 3 : ℝ)) ≤ W.c₀_Z := by
    rw [ha'_sq]
    calc ‖u‖ * c' ^ (-(2 / 3 : ℝ))
        ≤ (W.c₀_Z * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) := by gcongr
      _ = W.c₀_Z := by
          rw [mul_assoc, ← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero, mul_one]
  have hsad := W.h_saddle hc'_pos ha'_pos.le hφ_pos.le hφ_le ha'_Z
  dsimp only at hsad
  rw [← hu_polar] at hsad
  set z_u : ℂ := u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
  set s : ℂ := (kappaV : ℂ) * ((c' ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * u ^ (1 / 2 : ℂ) * W.q_V z_u
  set ρ : ℝ := ‖s‖
  obtain ⟨hb_eq_chartB, _hs_re_nn, hs_im_nn, hρ_ρ₀, hρ_rφ, _, hρ_lo, hρ_hi, hs_re_lb⟩ := hsad
  have hρ_pos : 0 < ρ :=
    lt_of_lt_of_le (by have := kappaV_pos; positivity) hρ_lo
  have hs_re_pos : 0 < s.re := lt_of_lt_of_le (by positivity) hs_re_lb
  set ρ_R : ℝ := kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R
  have hρ_lo_R : (18 / 25 : ℝ) * ρ_R ≤ ρ := by
    have h1 : (9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * ((4 / 5 : ℝ) * Real.sqrt R)) ≤
        (9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') := by
      gcongr; have := kappaV_pos; positivity
    calc (18 / 25 : ℝ) * ρ_R
        = (9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * ((4 / 5 : ℝ) * Real.sqrt R)) := by
          dsimp [ρ_R]; ring
      _ ≤ ρ := h1.trans hρ_lo
  have hρ_hi_R : ρ ≤ (33 / 25 : ℝ) * ρ_R := by
    have h1 : (11 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') ≤
        (11 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * ((6 / 5 : ℝ) * Real.sqrt R)) := by
      gcongr; have := kappaV_pos; positivity
    calc ρ ≤ (11 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * ((6 / 5 : ℝ) * Real.sqrt R)) :=
          hρ_hi.trans h1
      _ = (33 / 25 : ℝ) * ρ_R := by dsimp [ρ_R]; ring
  have hρ_ge_min : ρ_min_Z ≤ ρ := by
    have hsqrt_R_lb : b_lo * c' ^ (1 / 3 : ℝ) ≤ Real.sqrt R := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [mul_pow, ← Real.rpow_natCast (c' ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc'_pos.le]
      calc b_lo ^ 2 * c' ^ ((1 / 3 : ℝ) * (2 : ℕ)) = b_lo ^ 2 * c' ^ (2 / 3 : ℝ) := by
            push_cast; rw [show (1 / 3 : ℝ) * 2 = (2 / 3 : ℝ) by norm_num]
        _ ≤ R := hR_lo
    have hρR_lb : kappaV * b_lo ≤ ρ_R := by
      dsimp [ρ_R]
      calc kappaV * b_lo
          = kappaV * (c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ)) * b_lo := by
            rw [← Real.rpow_add hc'_pos, neg_add_cancel, Real.rpow_zero, mul_one]
        _ = kappaV * c' ^ (-(1 / 3 : ℝ)) * (b_lo * c' ^ (1 / 3 : ℝ)) := by ring
        _ ≤ kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R := by
            gcongr; have := kappaV_pos; positivity
    calc ρ_min_Z = (18 / 25 : ℝ) * (kappaV * b_lo) := by dsimp [ρ_min_Z]; ring
      _ ≤ (18 / 25 : ℝ) * ρ_R := by gcongr
      _ ≤ ρ := hρ_lo_R
  have hs_re_c12 : (5 / 3 : ℝ) * ρ * c' ^ (-(1 / 12 : ℝ)) ≤ s.re := by
    have h1 : (5 / 6 : ℝ) * (ρ * (2 * c' ^ (-(1 / 12 : ℝ)))) ≤ (5 / 6 : ℝ) * (ρ * Real.sin φ) := by
      gcongr
    calc (5 / 3 : ℝ) * ρ * c' ^ (-(1 / 12 : ℝ))
        = (5 / 6 : ℝ) * (ρ * (2 * c' ^ (-(1 / 12 : ℝ)))) := by ring
      _ ≤ s.re := h1.trans hs_re_lb
  have hc_ρ_sre_sq : (25 / 9 : ℝ) * ρ_min_Z ^ 3 * c' ^ (5 / 6 : ℝ) ≤ c' * ρ * s.re ^ 2 := by
    have hsq : ((5 / 3 : ℝ) * ρ * c' ^ (-(1 / 12 : ℝ))) ^ 2 ≤ s.re ^ 2 :=
      pow_le_pow_left₀ (by positivity) hs_re_c12 2
    have hpow_c : c' * (c' ^ (-(1 / 12 : ℝ))) ^ 2 = c' ^ (5 / 6 : ℝ) := by
      rw [← Real.rpow_natCast (c' ^ (-(1 / 12 : ℝ))) 2, ← Real.rpow_mul hc'_pos.le,
        ← Real.rpow_one_add' hc'_pos.le (by norm_num : (1 : ℝ) + -(1 / 12 : ℝ) * (2 : ℕ) ≠ 0)]
      push_cast; norm_num
    have hρ_cube : ρ_min_Z ^ 3 ≤ ρ ^ 3 := pow_le_pow_left₀ hρ_min_pos.le hρ_ge_min 3
    calc (25 / 9 : ℝ) * ρ_min_Z ^ 3 * c' ^ (5 / 6 : ℝ)
        ≤ (25 / 9 : ℝ) * ρ ^ 3 * c' ^ (5 / 6 : ℝ) := by gcongr
      _ = c' * ρ * (((5 / 3 : ℝ) * ρ * c' ^ (-(1 / 12 : ℝ))) ^ 2) := by
          rw [mul_pow, mul_pow, ← hpow_c]; ring
      _ ≤ c' * ρ * s.re ^ 2 := by gcongr
  set φ' : ℝ := Real.pi / 2 - s.arg
  have hs_arg_nn : 0 ≤ s.arg := Complex.arg_nonneg_iff.mpr hs_im_nn
  have hs_arg_le : s.arg ≤ Real.pi / 2 := by
    rcases eq_or_lt_of_le hs_im_nn with him0 | him_pos
    · rw [Complex.arg_eq_zero_iff.mpr ⟨hs_re_pos.le, him0.symm⟩]; positivity [Real.pi_pos]
    · exact (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hs_re_pos)).le
  have hφ'_nn : 0 ≤ φ' := by dsimp [φ']; linarith only [hs_arg_le]
  have hφ'_le : φ' ≤ Real.pi / 2 := by dsimp [φ']; linarith only [hs_arg_nn]
  have hs_polar : s = (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 - φ' : ℝ) : ℂ)) := by
    have hp := (Complex.norm_mul_exp_arg_mul_I s).symm
    have harg_eq : Real.pi / 2 - φ' = s.arg := by dsimp [φ']; ring
    rw [harg_eq]
    simpa [ρ, mul_comm (s.arg : ℂ) Complex.I] using hp
  -- Step 4: Deformation onto the `dpConfig_spec` saddle contour
  obtain ⟨_, _, _, segs, hchain, _, hω_bd, hstrip_gen, h_ur, h_lr, h_ar, h_fs, hnonstrip,
      hcnt_segs, hba_segs, h_no_crude⟩ :=
    dpConfig_spec hρ_pos.le hρ_ρ₀ hφ'_nn hφ'_le
  rw [← hs_polar, hb_eq_chartB] at hstrip_gen h_ur h_lr h_ar h_fs hnonstrip
  have hP_deform := truncatedMellinP_eq_contourIntegral hc'_24 hg hu_cb_in hchain hω_bd
  set b : ℂ := virasoroBChart c' u
  set t : ℂ := virasoroDeltaChartC c' u
  have hair_eq : Real.exp (c' * (chartPhiV s b).re) = airyEnv u := by
    have hs_ball : s ∈ ball (0 : ℂ) W.r_φ := by rwa [mem_ball_zero_iff]
    have hpot1 := W.hφ_pot s hs_ball hs_re_pos
    rw [hb_eq_chartB] at hpot1
    have hpot2 := virasoro_inner_potential_eq hc'_pos hu_cb_in hu_cut
    have hc_phi : c' * (chartPhiV s b).re = -(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re := by
      rw [hpot1]; simpa [add_comm] using hpot2
    rw [hc_phi]; rfl
  -- Step 5: Prefactor & window sector hypotheses for `lemma_Z_seg_bound`
  set M_g : ℝ := virasoroProblem.cardyNorm (c' / 12) g
  have hbd_in := virasoroBChart_inner_bounds hc'_pos hu_cb_in
  have hb_re_pos : 0 < b.re := lt_of_lt_of_le (half_pos xiStar_pos) hbd_in.2.2.1
  have ht_eq : t = (c' : ℂ) * b ^ 2 / 3 := virasoroDeltaChartC_eq_bChart_sq u
  have ht_half_ub : ‖t ^ (-(1 / 2 : ℂ))‖ ≤ (2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ)) := by
    have ht_lb : c' * (xiStar / 2) ^ 2 / 3 ≤ ‖t‖ := by
      rw [ht_eq, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc'_pos.le,
        Complex.norm_ofNat]
      have h1 : xiStar / 2 ≤ ‖b‖ := hbd_in.2.2.1.trans (Complex.re_le_norm _)
      have h2 : (xiStar / 2) ^ 2 ≤ ‖b‖ ^ 2 :=
        pow_le_pow_left₀ (by have := xiStar_pos; positivity) h1 2
      gcongr
    have ht_pos : 0 < ‖t‖ := lt_of_lt_of_le (by have := xiStar_pos; positivity) ht_lb
    have ht_ne : t ≠ 0 := norm_pos_iff.mp ht_pos
    have hnorm_cp : ‖t ^ (-(1 / 2 : ℂ))‖ = ‖t‖ ^ (-(1 / 2 : ℝ)) := by
      rw [Complex.cpow_def_of_ne_zero ht_ne, Complex.norm_exp]
      have hre : (Complex.log t * (-(1 / 2 : ℂ))).re = -(1 / 2 : ℝ) * Real.log ‖t‖ := by
        rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring,
          mul_comm, Complex.re_ofReal_mul, Complex.log_re]
      rw [hre, Real.rpow_def_of_pos ht_pos]
      congr 1; ring
    rw [hnorm_cp]
    have hpow_le : ‖t‖ ^ (-(1 / 2 : ℝ)) ≤ (c' * (xiStar / 2) ^ 2 / 3) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by have := xiStar_pos; positivity) ht_lb (by norm_num)
    have hrhs_eq : (c' * (xiStar / 2) ^ 2 / 3) ^ (-(1 / 2 : ℝ)) =
        (2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ)) := by
      have hxi := xiStar_pos
      have hsub : ((xiStar / 2) ^ 2 / 3) ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt 3 / xiStar := by
        rw [Real.rpow_neg (by positivity),
          Real.div_rpow (by positivity) (by norm_num),
          ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
          Real.sqrt_sq (by positivity)]
        field_simp [hxi.ne']
      rw [show c' * (xiStar / 2) ^ 2 / 3 = ((xiStar / 2) ^ 2 / 3) * c' by ring,
        Real.mul_rpow (by positivity) hc'_pos.le, hsub]
    exact hpow_le.trans_eq hrhs_eq
  have hwin_wv : ∀ ζ ∈ stripClosed, ‖ζ - s‖ ≤ s.re / 4 →
      ‖tildeWV c' g ζ‖ ≤ M_g * (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) := by
    intro ζ hζ_cl hdist
    have hdist_ρ : ‖ζ - s‖ ≤ ρ / 4 := by
      have hs_re_le : s.re ≤ ρ := Complex.re_le_norm s
      linarith only [hdist, hs_re_le]
    have hζ_lo : ρ_R / 3 ≤ ‖ζ‖ := by
      have htri := norm_sub_norm_le s (s - ζ)
      rw [sub_sub_cancel, norm_sub_rev] at htri
      have htri' : ρ - ‖ζ - s‖ ≤ ‖ζ‖ := htri
      have h34 : (3 / 4 : ℝ) * ρ ≤ ‖ζ‖ := by linarith only [htri', hdist_ρ]
      have hR_nn : 0 ≤ ρ_R := by dsimp [ρ_R]; have := kappaV_pos; positivity
      calc ρ_R / 3 ≤ (27 / 50 : ℝ) * ρ_R := by linarith only [hR_nn]
        _ = (3 / 4 : ℝ) * ((18 / 25 : ℝ) * ρ_R) := by ring
        _ ≤ (3 / 4 : ℝ) * ρ := by gcongr
        _ ≤ ‖ζ‖ := h34
    have hζ_hi : ‖ζ‖ ≤ 2 * ρ_R := by
      have htri : ‖ζ‖ ≤ ρ + ‖ζ - s‖ := by
        calc ‖ζ‖ = ‖s + (ζ - s)‖ := by ring_nf
          _ ≤ ‖s‖ + ‖ζ - s‖ := norm_add_le _ _
      have h54 : ‖ζ‖ ≤ (5 / 4 : ℝ) * ρ := by linarith only [htri, hdist_ρ]
      have hR_nn : 0 ≤ ρ_R := by dsimp [ρ_R]; have := kappaV_pos; positivity
      calc ‖ζ‖ ≤ (5 / 4 : ℝ) * ρ := h54
        _ ≤ (5 / 4 : ℝ) * ((33 / 25 : ℝ) * ρ_R) := by gcongr
        _ = (33 / 20 : ℝ) * ρ_R := by ring
        _ ≤ 2 * ρ_R := by linarith only [hR_nn]
    have hζ_re_lb : (3 / 4 : ℝ) * s.re ≤ ζ.re := by
      have hre_sub := (abs_le.mp ((Complex.abs_re_le_norm (ζ - s)).trans hdist)).1
      rw [Complex.sub_re] at hre_sub
      linarith only [hre_sub]
    have hζ_re_pos : 0 < ζ.re := lt_of_lt_of_le (by positivity) hζ_re_lb
    have hζ_ang : (1 / 2 : ℝ) * Real.sin φ * ‖ζ‖ ≤ ζ.re := by
      have h54 : ‖ζ‖ ≤ (5 / 4 : ℝ) * ρ := by
        have htri : ‖ζ‖ ≤ ρ + ‖ζ - s‖ := by
          calc ‖ζ‖ = ‖s + (ζ - s)‖ := by ring_nf
            _ ≤ ‖s‖ + ‖ζ - s‖ := norm_add_le _ _
        linarith only [htri, hdist_ρ]
      calc (1 / 2 : ℝ) * Real.sin φ * ‖ζ‖
          ≤ (1 / 2 : ℝ) * Real.sin φ * ((5 / 4 : ℝ) * ρ) := by gcongr
        _ = (3 / 4 : ℝ) * ((5 / 6 : ℝ) * (ρ * Real.sin φ)) := by ring
        _ ≤ (3 / 4 : ℝ) * s.re := by gcongr
        _ ≤ ζ.re := hζ_re_lb
    have hζ_c12 : c' ^ (-(1 / 12 : ℝ)) * ‖ζ‖ ≤ ζ.re := by
      have hc_half : c' ^ (-(1 / 12 : ℝ)) ≤ (1 / 2 : ℝ) * Real.sin φ := by linarith only [hsin_lb]
      exact (mul_le_mul_of_nonneg_right hc_half (norm_nonneg ζ)).trans hζ_ang
    have h_wv := hsec ζ hζ_cl hζ_lo hζ_hi hζ_c12
    have h_rat : ‖ζ‖ / ζ.re ≤ 2 / Real.sin φ := by
      rw [div_le_div_iff₀ hζ_re_pos hsin_pos]
      linarith only [hζ_ang]
    calc ‖tildeWV c' g ζ‖
        ≤ M_g * (Λ * c' ^ (-(5 / 6 : ℝ)) * (‖ζ‖ / ζ.re)) := by
          simpa only [mul_div_assoc] using h_wv
      _ ≤ M_g * (Λ * c' ^ (-(5 / 6 : ℝ)) * (2 / Real.sin φ)) := by gcongr
      _ = M_g * (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) := by ring
  set K_seg : ℝ := (4 * Real.sqrt 3 / xiStar) * dpConfig.C_d * M_g *
    c' ^ (-(1 / 2 : ℝ)) * Real.exp (-(c' * (tipL b).re)) * airyEnv u
  have hK_seg_pos : 0 < K_seg :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos
      (div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))) xiStar_pos)
      dpConfig.hC_d_pos) hM_pos) (Real.rpow_pos_of_pos hc'_pos _)) (Real.exp_pos _))
      (airyEnv_pos u)
  set B_seg_unit : ℝ :=
    (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
      ((Real.pi / 2) / Real.sqrt (c' * dpConfig.c_γ * ρ)) +
    max W.C_S4 W.C_S2 * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))
  have hB_seg_nn : 0 ≤ K_seg * B_seg_unit := by
    refine mul_nonneg hK_seg_pos.le (add_nonneg ?_ ?_)
    · exact mul_nonneg (div_nonneg (by positivity) hsin_pos.le)
        (div_nonneg (by positivity) (Real.sqrt_nonneg _))
    · exact mul_nonneg (lt_of_lt_of_le W.hCS4 (le_max_left _ _)).le (Real.exp_pos _).le
  have hseg_bound : ∀ S ∈ segs,
      ‖∫ τ in S.a..S.b, mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖ ≤
        K_seg * B_seg_unit := fun S hS =>
    lemma_Z_seg_bound W dpConfig S hc'_pos hc'_ge1 hc'_24 hc'_48 hc'_S4
      (by linarith only [hΛ]) hsin_pos hρ_pos hs_re_pos hρ_min_pos hρ_ge_min hc_ρ_sre_sq
      hκ_all_pos ((min_le_left _ _).trans (min_le_left _ _))
      ((min_le_left _ _).trans (min_le_right _ _))
      ((min_le_right _ _).trans (min_le_left _ _))
      hg hM_pos rfl hb_re_pos hbd_in.2.2.2.2.2 ht_eq ht_half_ub hair_eq rfl rfl
      hwin_wv (fun hμ => W.hS2 hc'_S2 hμ hg)
      (hba_segs S hS) (hω_bd S hS) (h_ur S hS) (h_lr S hS) (h_ar S hS) (h_fs S hS)
      (hnonstrip S hS) (h_no_crude S hS)
  -- Step 6: Sum over `segs` (`segs.length ≤ 12`) to bound `‖truncatedMellinP c' dpT0 g u‖`
  have hcont_tot : ‖contourIntegral (mellinDensityIntegrand c' g t) segs‖ ≤
      12 * (K_seg * B_seg_unit) :=
    (norm_contourIntegral_le_of_seg_bound _ segs hB_seg_nn hseg_bound).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcnt_segs) hB_seg_nn)
  have hP_norm : ‖truncatedMellinP c' dpT0 g u‖ ≤
      12 * C_pref * c' ^ (1 / 3 : ℝ) * B_seg_unit * airyEnv u := by
    have hV_u := W.hV_bd hc'_V hu_cb_in
    have hd_u := virasoroDeltaChartC_inner_deriv_bound hc'_pos hu_cb_in
    rw [hP_deform, norm_mul, norm_mul, norm_mul, norm_neg, norm_div, norm_div]
    have hM_norm : ‖(M_g : ℂ)‖ = M_g := by
      rw [Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
    have hc_2pi : ‖(c' : ℂ)‖ / ‖2 * (Real.pi : ℂ) * Complex.I‖ = c' / (2 * Real.pi) := by
      rw [Complex.norm_real, Real.norm_of_nonneg hc'_pos.le, norm_mul, norm_mul,
        Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
        Complex.norm_I, mul_one]
    change (‖deriv (virasoroDeltaChartC c') u‖ / ‖(M_g : ℂ)‖) *
        ‖V_C (c' : ℂ) t‖ * (‖(c' : ℂ)‖ / ‖2 * (Real.pi : ℂ) * Complex.I‖) *
        ‖contourIntegral (mellinDensityIntegrand c' g t) segs‖ ≤ _
    rw [hM_norm, hc_2pi]
    have hexp_cancel : Real.exp (c' * (tipL b).re) * Real.exp (-(c' * (tipL b).re)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hc_pow_eq : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ)) * c' * c' ^ (-(1 / 2 : ℝ)) =
        c' ^ (1 / 3 : ℝ) := by
      calc c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ)) * c' * c' ^ (-(1 / 2 : ℝ))
          = c' ^ (1 / 3 : ℝ) * (c' * (c' ^ (-(1 / 2 : ℝ)) * c' ^ (-(1 / 2 : ℝ)))) := by ring
        _ = c' ^ (1 / 3 : ℝ) * (c' * c' ^ (-1 : ℝ)) := by
            rw [← Real.rpow_add hc'_pos]; norm_num
        _ = c' ^ (1 / 3 : ℝ) * 1 := by rw [Real.rpow_neg_one, mul_inv_cancel₀ hc'_pos.ne']
        _ = c' ^ (1 / 3 : ℝ) := mul_one _
    calc (‖deriv (virasoroDeltaChartC c') u‖ / M_g) * ‖V_C (c' : ℂ) t‖ *
            (c' / (2 * Real.pi)) * ‖contourIntegral (mellinDensityIntegrand c' g t) segs‖
        ≤ ((innerCDxi * c' ^ (1 / 3 : ℝ)) / M_g) *
            (W.C_V * c' ^ (-(1 / 2 : ℝ)) * Real.exp (c' * (tipL b).re)) *
            (c' / (2 * Real.pi)) * (12 * (K_seg * B_seg_unit)) := by
          have := innerCDxi_pos; have := W.hC_V
          gcongr
      _ = 12 * C_pref * (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ)) * c' * c' ^ (-(1 / 2 : ℝ))) *
            (Real.exp (c' * (tipL b).re) * Real.exp (-(c' * (tipL b).re))) *
            B_seg_unit * airyEnv u := by
          dsimp [C_pref, K_seg]
          field_simp [hM_pos.ne', Real.pi_pos.ne']
      _ = 12 * C_pref * c' ^ (1 / 3 : ℝ) * B_seg_unit * airyEnv u := by
          rw [hc_pow_eq, hexp_cancel, mul_one]
  -- Step 7: Combine with `lemma_Dp` via `lemma_Z_combine_envelope`
  exact lemma_Z_combine_envelope W dpConfig hb_hi_pos hc'_pos hc'_ge1 hΛ
    hκ_all_pos ((min_le_right _ _).trans (min_le_right _ _)) hC_pref_pos
    hu_pos hu_bhi hu_re_pos hu_re_eq hsin_pos hsin_le1 hρ_pos hρ_lo rfl
    (hC_B_eq ▸ le_max_right _ _) hP_norm (W.hDp hc'_D hg hM_pos hu_cb_D)

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.Contour.lemma_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Z

end FormalResearch.ModularBootstrap.Contour
