module

public import FormalResearch.SignUncertainty.CtSdBounds

/-!
# Steepest-descent moment bounds (`ct:sd-moments`) (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3, display `ct:sd-moments`.  **Proved.**
The moments `∫_Γ |w|^α e^{-Im(2^{2/3} U w + w³/3)} |dw|` over the polygonal contour `Γ` (the ray `e^{iπ/6}ℝ₊` for `U ≥ -1`;
for `U = -W < -1` the segment `w_*(1-i)t`, then the line through the saddle `w_*` in direction `1+i` up to the ray `e^{iπ/6}ℝ₊`,
then the ray; `w_* = 2^{1/3}√W`) are `O((1+|U|)^{(α-1/2)/2})` for `α ∈ {1/2, 3/2}` and `O((1+|U|)^{-1/2})` for `α = -1/2`.
The line through `w_*` meets the ray at `(1+√3) w_*`, which simplifies the paper's exit analysis.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Real

namespace FormalResearch.SignUncertainty.CtSd

/-- `ν = 2^{-1/3}`, so that `Im(2^{2/3} U r e^{iπ/6}) = ν U r`. -/
noncomputable def nu : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 3)

lemma nu_pos : 0 < nu := by unfold nu; positivity

lemma nu_le_one : nu ≤ 1 := by
  unfold nu
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)

/-- exponent bound: `ν r - r³/3 ≤ 1 - r³/6` for `r ≥ 0`. -/
lemma exp_exponent_bd {r : ℝ} (hr : 0 ≤ r) : nu * r - r ^ 3 / 3 ≤ 1 - r ^ 3 / 6 := by
  have h1 := nu_le_one
  have : nu * r ≤ r := by nlinarith [nu_pos]
  nlinarith [mul_nonneg hr (sq_nonneg (r - 3 / 2)), sq_nonneg (r - 3 / 2), hr]

lemma aesm_rpow_mul {α : ℝ} {g : ℝ → ℝ} (hg : Measurable g) (S : Measure ℝ) :
    AEStronglyMeasurable (fun r : ℝ => r ^ α * g r) S :=
  ((measurable_id.pow_const α).mul hg).aestronglyMeasurable

/-- Case A (`U ≥ -1`): the moment along the ray is bounded by a constant. -/
lemma momA_const {α : ℝ} (hα : -1 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U R : ℝ, -1 ≤ U → 0 ≤ R →
      ∫ r in (0 : ℝ)..R, r ^ α * Real.exp (-(nu * U * r + r ^ 3 / 3)) ≤ C := by
  refine ⟨Real.exp 1 * ((1 / 6 : ℝ) ^ (-(α + 1) / 3) * (1 / 3) * Real.Gamma ((α + 1) / 3)), ?_, ?_⟩
  · have : 0 ≤ Real.Gamma ((α + 1) / 3) := (Real.Gamma_pos_of_pos (by linarith)).le
    positivity
  intro U R hU hR
  have hg := integrableOn_cube (α := α) (b := 1 / 6) hα (by norm_num)
  have hint := intervalIntegral_le_Ioi (f := fun r : ℝ => r ^ α * Real.exp (-(nu * U * r + r ^ 3 / 3)))
    (g := fun r : ℝ => Real.exp 1 * (r ^ α * Real.exp (-((1 / 6) * r ^ 3)))) le_rfl hR
    (fun t ht => by positivity)
    (fun t ht => by
      have h1 : -(nu * U * t + t ^ 3 / 3) ≤ 1 + -((1 / 6) * t ^ 3) := by
        have := exp_exponent_bd ht.le
        nlinarith [nu_pos, mul_nonneg nu_pos.le ht.le, mul_le_mul_of_nonneg_right hU (mul_nonneg nu_pos.le ht.le)]
      calc t ^ α * Real.exp (-(nu * U * t + t ^ 3 / 3)) ≤ t ^ α * Real.exp (1 + -((1 / 6) * t ^ 3)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) (by positivity)
        _ = Real.exp 1 * (t ^ α * Real.exp (-((1 / 6) * t ^ 3))) := by
            rw [Real.exp_add]; ring)
    (hg.const_mul _)
    (aesm_rpow_mul (by fun_prop) _)
  refine hint.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_cube hα (by norm_num)]

lemma one_add_abs_rpow_le {U : ℝ} (hU : 1 ≤ U) : U ^ (-(1 : ℝ) / 2) ≤ Real.sqrt 2 * (1 + |U|) ^ (-(1 : ℝ) / 2) := by
  have hU0 : 0 < U := by linarith
  have h1 : (1 + |U|) ≤ 2 * U := by rw [abs_of_pos hU0]; linarith
  have h2 : (2 * U) ^ (-(1 : ℝ) / 2) ≤ (1 + |U|) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
  rw [Real.mul_rpow (by norm_num) hU0.le] at h2
  have h3 : (2 : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt 2)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num)]; norm_num
  rw [h3] at h2
  have hs : 0 < Real.sqrt 2 := by positivity
  calc U ^ (-(1 : ℝ) / 2) = Real.sqrt 2 * ((Real.sqrt 2)⁻¹ * U ^ (-(1 : ℝ) / 2)) := by field_simp
    _ ≤ Real.sqrt 2 * (1 + |U|) ^ (-(1 : ℝ) / 2) := mul_le_mul_of_nonneg_left h2 hs.le

/-- Case A for `α = -1/2`: decay in `U`. -/
lemma momA_inv :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U R : ℝ, -1 ≤ U → 0 ≤ R →
      ∫ r in (0 : ℝ)..R, r ^ (-(1 : ℝ) / 2) * Real.exp (-(nu * U * r + r ^ 3 / 3)) ≤ C * (1 + |U|) ^ (-(1 : ℝ) / 2) := by
  obtain ⟨C0, hC0, h0⟩ := momA_const (α := -(1 : ℝ) / 2) (by norm_num)
  refine ⟨Real.sqrt 2 * (C0 + nu ^ (-(1 : ℝ) / 2) * Real.Gamma (1 / 2)), ?_, ?_⟩
  · have : 0 ≤ Real.Gamma (1 / 2) := (Real.Gamma_pos_of_pos (by norm_num)).le
    have := nu_pos
    positivity
  intro U R hU hR
  have hs : 0 < Real.sqrt 2 := by positivity
  by_cases hU1 : U ≤ 1
  · have hb := h0 U R hU hR
    have habs : 1 + |U| ≤ 2 := by
      have := abs_le.mpr (⟨by linarith, hU1⟩ : -1 ≤ U ∧ U ≤ 1); linarith
    have h2 : (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ (1 + |U|) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) habs (by norm_num)
    have h3 : (2 : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt 2)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num)]; norm_num
    rw [h3] at h2
    have hGam : 0 ≤ nu ^ (-(1 : ℝ) / 2) * Real.Gamma (1 / 2) := by
      have : 0 ≤ Real.Gamma (1 / 2) := (Real.Gamma_pos_of_pos (by norm_num)).le
      have := nu_pos
      positivity
    have hp : 0 ≤ (1 + |U|) ^ (-(1 : ℝ) / 2) := by positivity
    calc _ ≤ C0 := hb
      _ = Real.sqrt 2 * C0 * (Real.sqrt 2)⁻¹ := by field_simp
      _ ≤ Real.sqrt 2 * C0 * (1 + |U|) ^ (-(1 : ℝ) / 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hs.le hGam, mul_nonneg (mul_nonneg hs.le hGam) hp]
  · have hU1 : 1 < U := not_le.mp hU1
    have hnuU : 0 < nu * U := mul_pos nu_pos (by linarith)
    have hg := integrableOn_lin (α := -(1 : ℝ) / 2) (lam := nu * U) (by norm_num) hnuU
    have hint := intervalIntegral_le_Ioi (f := fun r : ℝ => r ^ (-(1 : ℝ) / 2) * Real.exp (-(nu * U * r + r ^ 3 / 3)))
      (g := fun r : ℝ => r ^ (-(1 : ℝ) / 2) * Real.exp (-((nu * U) * r))) le_rfl hR
      (fun t ht => by positivity)
      (fun t ht => by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        have : 0 ≤ t ^ 3 / 3 := by positivity
        linarith)
      hg (aesm_rpow_mul (by fun_prop) _)
    have hval := integral_lin (α := -(1 : ℝ) / 2) (lam := nu * U) (by norm_num) hnuU
    have e1 : -(-(1 : ℝ) / 2 + 1) = -(1 : ℝ) / 2 := by norm_num
    have e2 : (-(1 : ℝ) / 2 + 1) = 1 / 2 := by norm_num
    rw [e1, e2] at hval
    have hU0 : 0 < U := by linarith
    have hmul : (nu * U) ^ (-(1 : ℝ) / 2) = nu ^ (-(1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 2) :=
      Real.mul_rpow nu_pos.le hU0.le
    have hU' := one_add_abs_rpow_le hU1.le
    have hG : 0 ≤ nu ^ (-(1 : ℝ) / 2) * Real.Gamma (1 / 2) := by
      have : 0 ≤ Real.Gamma (1 / 2) := (Real.Gamma_pos_of_pos (by norm_num)).le
      have := nu_pos
      positivity
    calc _ ≤ ∫ r in Ioi (0 : ℝ), r ^ (-(1 : ℝ) / 2) * Real.exp (-((nu * U) * r)) := hint
      _ = nu ^ (-(1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 2) * Real.Gamma (1 / 2) := by rw [hval, hmul]
      _ = (nu ^ (-(1 : ℝ) / 2) * Real.Gamma (1 / 2)) * U ^ (-(1 : ℝ) / 2) := by ring
      _ ≤ (nu ^ (-(1 : ℝ) / 2) * Real.Gamma (1 / 2)) * (Real.sqrt 2 * (1 + |U|) ^ (-(1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hU' hG
      _ ≤ _ := by
          have hp : 0 ≤ (1 + |U|) ^ (-(1 : ℝ) / 2) := by positivity
          nlinarith [mul_nonneg hs.le (mul_nonneg hG hp), mul_nonneg (mul_nonneg hs.le hC0) hp]

lemma rpow_cube_eq {x : ℝ} (hx : 0 < x) (s : ℝ) : (x ^ 3) ^ s = x ^ (3 * s) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num

/-- Case B, first segment `w = w_* t (1-i)`, `t ∈ [0,1/2]`. -/
lemma momB1 {α : ℝ} (hα : -1 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, 1 ≤ w →
      ∫ t in (0 : ℝ)..(1 / 2), (Real.sqrt 2 * w * t) ^ α * Real.exp (-(w ^ 3 * (t - 2 / 3 * t ^ 3))) *
        (Real.sqrt 2 * w) ≤ C * w ^ (-2 * (α + 1)) := by
  refine ⟨(Real.sqrt 2) ^ (α + 1) * ((5 / 6 : ℝ) ^ (-(α + 1)) * Real.Gamma (α + 1)), ?_, ?_⟩
  · have : 0 ≤ Real.Gamma (α + 1) := (Real.Gamma_pos_of_pos (by linarith)).le
    positivity
  intro w hw
  have hw0 : 0 < w := by linarith
  have hs : 0 < Real.sqrt 2 := by positivity
  have hlam : 0 < 5 / 6 * w ^ 3 := by positivity
  have hg := integrableOn_lin (α := α) (lam := 5 / 6 * w ^ 3) hα hlam
  have hint := intervalIntegral_le_Ioi' (a := 0) (b := 1 / 2) (f := fun t : ℝ => (Real.sqrt 2 * w * t) ^ α * Real.exp (-(w ^ 3 * (t - 2 / 3 * t ^ 3))) *
        (Real.sqrt 2 * w))
    (g := fun t : ℝ => (Real.sqrt 2 * w) ^ (α + 1) * (t ^ α * Real.exp (-((5 / 6 * w ^ 3) * t)))) le_rfl (by norm_num)
    (fun t ht => by have := ht.1; positivity)
    (fun t ht => by
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 / 2 := ht.2
      have h1 : -(w ^ 3 * (t - 2 / 3 * t ^ 3)) ≤ -((5 / 6 * w ^ 3) * t) := by
        have : 5 / 6 * t ≤ t - 2 / 3 * t ^ 3 := by nlinarith [sq_nonneg t, mul_nonneg ht0.le (sq_nonneg t)]
        nlinarith [pow_pos hw0 3]
      calc (Real.sqrt 2 * w * t) ^ α * Real.exp (-(w ^ 3 * (t - 2 / 3 * t ^ 3))) * (Real.sqrt 2 * w)
          ≤ (Real.sqrt 2 * w * t) ^ α * Real.exp (-((5 / 6 * w ^ 3) * t)) * (Real.sqrt 2 * w) := by
            gcongr
        _ = (Real.sqrt 2 * w) ^ (α + 1) * (t ^ α * Real.exp (-((5 / 6 * w ^ 3) * t))) := by
            rw [Real.mul_rpow (by positivity) ht0.le, Real.rpow_add (by positivity), Real.rpow_one]; ring)
    (fun t ht => by positivity) (hg.const_mul _)
    ((((measurable_const.mul measurable_id).pow_const α).mul
      (Real.measurable_exp.comp (by fun_prop : Measurable fun t : ℝ => -(w ^ 3 * (t - 2 / 3 * t ^ 3))))).mul_const _
        |>.aestronglyMeasurable)
  refine hint.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_lin hα hlam]
  rw [Real.mul_rpow hs.le hw0.le, Real.mul_rpow (by norm_num) (pow_pos hw0 3).le, rpow_cube_eq hw0]
  have e1 : w ^ (α + 1) * w ^ (3 * -(α + 1)) = w ^ (-2 * (α + 1)) := by
    rw [← Real.rpow_add hw0]; congr 1; ring
  calc Real.sqrt 2 ^ (α + 1) * w ^ (α + 1) * ((5 / 6) ^ (-(α + 1)) * w ^ (3 * -(α + 1)) * Real.Gamma (α + 1))
      = Real.sqrt 2 ^ (α + 1) * ((5 / 6) ^ (-(α + 1)) * Real.Gamma (α + 1)) * (w ^ (α + 1) * w ^ (3 * -(α + 1))) := by ring
    _ = _ := by rw [e1]

lemma rho_bounds {u : ℝ} (hu : -(1 / 2 : ℝ) ≤ u) :
    (Real.sqrt 2)⁻¹ ≤ Real.sqrt ((1 + u) ^ 2 + u ^ 2) ∧ Real.sqrt ((1 + u) ^ 2 + u ^ 2) ≤ 1 + 2 * |u| := by
  constructor
  · rw [Real.le_sqrt (by positivity), inv_pow, Real.sq_sqrt (by norm_num)]
    nlinarith [sq_nonneg (u + 1 / 2)]
    positivity
  · rw [Real.sqrt_le_left (by positivity)]
    have : u ≤ |u| := le_abs_self u
    nlinarith [abs_nonneg u, sq_abs u]

/-- `ρ^α ≤ 2 e^{4|u|}` for `α ∈ [-1/2, 2]`. -/
lemma rho_rpow_le {α u : ℝ} (hα1 : -(1 / 2 : ℝ) ≤ α) (hα2 : α ≤ 2) (hu : -(1 / 2 : ℝ) ≤ u) :
    Real.sqrt ((1 + u) ^ 2 + u ^ 2) ^ α ≤ 2 * Real.exp (4 * |u|) := by
  obtain ⟨h1, h2⟩ := rho_bounds hu
  have hρ : 0 < Real.sqrt ((1 + u) ^ 2 + u ^ 2) := lt_of_lt_of_le (by positivity) h1
  have hexp : 1 + 2 * |u| ≤ Real.exp (2 * |u|) := by
    have := Real.add_one_le_exp (2 * |u|); linarith
  have hexp1 : 1 ≤ Real.exp (4 * |u|) := Real.one_le_exp (by positivity)
  rcases le_or_gt 0 α with hα | hα
  · calc Real.sqrt ((1 + u) ^ 2 + u ^ 2) ^ α ≤ (1 + 2 * |u|) ^ α := Real.rpow_le_rpow hρ.le h2 hα
      _ ≤ (1 + 2 * |u|) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg u]) hα2
      _ = (1 + 2 * |u|) ^ 2 := by rw [Real.rpow_two]
      _ ≤ Real.exp (2 * |u|) ^ 2 := pow_le_pow_left₀ (by positivity) hexp 2
      _ = Real.exp (4 * |u|) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ ≤ 2 * Real.exp (4 * |u|) := by linarith
  · have hs : 1 ≤ Real.sqrt 2 := by
      rw [Real.one_le_sqrt]; norm_num
    have hs2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    calc Real.sqrt ((1 + u) ^ 2 + u ^ 2) ^ α ≤ ((Real.sqrt 2)⁻¹) ^ α := Real.rpow_le_rpow_of_nonpos (by positivity) h1 hα.le
      _ = Real.sqrt 2 ^ (-α) := by rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
      _ ≤ Real.sqrt 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hs (by linarith)
      _ = Real.sqrt 2 := Real.rpow_one _
      _ ≤ 2 * Real.exp (4 * |u|) := by nlinarith

lemma gauss_exp_bound {b u : ℝ} (hb : 5 / 3 ≤ b) :
    Real.exp (4 * |u|) * Real.exp (-(b * u ^ 2)) ≤ Real.exp (24 / 5) * Real.exp (-((b / 2) * u ^ 2)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : (5 / 6) * u ^ 2 ≤ (b / 2) * u ^ 2 := by nlinarith [sq_nonneg u]
  have h2 : 0 ≤ (5 / 6) * (|u| - 12 / 5) ^ 2 := by positivity
  have h3 : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  nlinarith [h1, h2, h3]

/-- Case B, second segment `w = w_*(1 + u(1+i))`, `u ∈ [-1/2, u_J]`. -/
lemma momB2 {α : ℝ} (hα1 : -(1 / 2 : ℝ) ≤ α) (hα2 : α ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w uJ : ℝ, 1 ≤ w → -(1 / 2 : ℝ) ≤ uJ →
      ∫ u in (-(1 / 2 : ℝ))..uJ, (w * Real.sqrt ((1 + u) ^ 2 + u ^ 2)) ^ α *
        Real.exp (-(w ^ 3 * (u ^ 2 * (2 + 2 / 3 * u)))) * (Real.sqrt 2 * w) ≤ C * w ^ (α - 1 / 2) := by
  refine ⟨2 * Real.exp (24 / 5) * Real.sqrt 2 * Real.sqrt (π / (5 / 6)), ?_⟩
  refine ⟨by positivity, ?_⟩
  intro w uJ hw huJ
  have hw0 : 0 < w := by linarith
  have hb : (5 / 3 : ℝ) ≤ 5 / 3 * w ^ 3 := by
    have : 1 ≤ w ^ 3 := one_le_pow₀ hw
    nlinarith
  set b : ℝ := 5 / 3 * w ^ 3 with hbdef
  have hb0 : 0 < b := by linarith
  set K : ℝ := 2 * Real.exp (24 / 5) * w ^ α * (Real.sqrt 2 * w) with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ u ∈ Icc (-(1 / 2 : ℝ)) uJ, (w * Real.sqrt ((1 + u) ^ 2 + u ^ 2)) ^ α *
        Real.exp (-(w ^ 3 * (u ^ 2 * (2 + 2 / 3 * u)))) * (Real.sqrt 2 * w) ≤ K * Real.exp (-((b / 2) * u ^ 2)) := by
    intro u hu
    have hρ0 : 0 < Real.sqrt ((1 + u) ^ 2 + u ^ 2) := lt_of_lt_of_le (by positivity) (rho_bounds hu.1).1
    have hq : (5 / 3) * u ^ 2 ≤ u ^ 2 * (2 + 2 / 3 * u) := by nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) (by linarith [hu.1] : (0 : ℝ) ≤ 1 + 2 * u)]
    have h1 : Real.exp (-(w ^ 3 * (u ^ 2 * (2 + 2 / 3 * u)))) ≤ Real.exp (-(b * u ^ 2)) := by
      apply Real.exp_le_exp.mpr
      rw [hbdef]
      nlinarith [pow_pos hw0 3, mul_le_mul_of_nonneg_left hq (pow_pos hw0 3).le]
    have h2 := rho_rpow_le hα1 hα2 hu.1
    have h3 := gauss_exp_bound (b := b) (u := u) hb
    rw [Real.mul_rpow hw0.le hρ0.le]
    calc w ^ α * Real.sqrt ((1 + u) ^ 2 + u ^ 2) ^ α * Real.exp (-(w ^ 3 * (u ^ 2 * (2 + 2 / 3 * u)))) * (Real.sqrt 2 * w)
        ≤ w ^ α * (2 * Real.exp (4 * |u|)) * Real.exp (-(b * u ^ 2)) * (Real.sqrt 2 * w) := by
          gcongr
      _ = 2 * w ^ α * (Real.sqrt 2 * w) * (Real.exp (4 * |u|) * Real.exp (-(b * u ^ 2))) := by ring
      _ ≤ 2 * w ^ α * (Real.sqrt 2 * w) * (Real.exp (24 / 5) * Real.exp (-((b / 2) * u ^ 2))) := by
          gcongr
      _ = K * Real.exp (-((b / 2) * u ^ 2)) := by rw [hK]; ring
  have hfc : Continuous fun u : ℝ => (w * Real.sqrt ((1 + u) ^ 2 + u ^ 2)) ^ α *
        Real.exp (-(w ^ 3 * (u ^ 2 * (2 + 2 / 3 * u)))) * (Real.sqrt 2 * w) := by
    refine ((Continuous.rpow_const ?_ ?_).mul (by fun_prop)).mul continuous_const
    · fun_prop
    · intro u
      left
      have : 0 < Real.sqrt ((1 + u) ^ 2 + u ^ 2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (u + 1 / 2)])
      positivity
  have hGi : Integrable fun u : ℝ => K * Real.exp (-((b / 2) * u ^ 2)) := by
    have := integrable_exp_neg_mul_sq (b := b / 2) (by positivity)
    have h2 : Integrable fun u : ℝ => K * Real.exp (-(b / 2) * u ^ 2) := this.const_mul K
    refine h2.congr (ae_of_all _ fun u => ?_)
    simp only []; ring_nf
  have hle : -(1 / 2 : ℝ) ≤ uJ := huJ
  calc ∫ u in (-(1 / 2 : ℝ))..uJ, (w * Real.sqrt ((1 + u) ^ 2 + u ^ 2)) ^ α *
        Real.exp (-(w ^ 3 * (u ^ 2 * (2 + 2 / 3 * u)))) * (Real.sqrt 2 * w)
      ≤ ∫ u in (-(1 / 2 : ℝ))..uJ, K * Real.exp (-((b / 2) * u ^ 2)) :=
        intervalIntegral.integral_mono_on hle (hfc.intervalIntegrable _ _) (hGi.intervalIntegrable) hpt
    _ ≤ ∫ u : ℝ, K * Real.exp (-((b / 2) * u ^ 2)) := by
        rw [intervalIntegral.integral_of_le hle]
        exact setIntegral_le_integral hGi (ae_of_all _ fun u => by positivity)
    _ = K * Real.sqrt (π / (b / 2)) := by
        rw [integral_const_mul]
        congr 1
        have := integral_gaussian (b / 2)
        rw [← this]; congr 1; ext u; ring_nf
    _ = _ := by
        have e1 : b / 2 = 5 / 6 * w ^ 3 := by rw [hbdef]; ring
        have e2 : Real.sqrt (π / (b / 2)) = Real.sqrt (π / (5 / 6)) * w ^ (-(3 / 2 : ℝ)) := by
          rw [e1, show π / (5 / 6 * w ^ 3) = π / (5 / 6) * (w ^ 3)⁻¹ by field_simp,
            Real.sqrt_mul (by positivity), Real.sqrt_inv, Real.sqrt_eq_rpow (w ^ 3), rpow_cube_eq hw0,
            Real.rpow_neg hw0.le]
          congr 2
          norm_num
        have e3 : w ^ α * w = w ^ (α + 1) := by rw [Real.rpow_add hw0, Real.rpow_one]
        have e4 : w ^ (α + 1) * w ^ (-(3 / 2 : ℝ)) = w ^ (α - 1 / 2) := by
          rw [← Real.rpow_add hw0]; congr 1; ring
        rw [e2, hK, ← e4, ← e3]
        ring

/-- Case B, third segment: the ray `r e^{iπ/6}` beyond the junction `r_J = (1+√3) w_*`. -/
lemma momB3 {α : ℝ} (hα1 : -(1 / 2 : ℝ) ≤ α) (hα2 : α ≤ 3 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w R : ℝ, 1 ≤ w → (1 + Real.sqrt 3) * w ≤ R →
      ∫ r in ((1 + Real.sqrt 3) * w)..R, r ^ α * Real.exp (-(r ^ 3 / 3 - w ^ 2 / 2 * r)) ≤ C * w ^ (-(1 : ℝ)) := by
  have h5 : 0 < 5 - α := by linarith
  refine ⟨32 / (5 - α), by positivity, ?_⟩
  intro w R hw hR
  have hw0 : 0 < w := by linarith
  have h3 : 1 ≤ Real.sqrt 3 := by rw [Real.one_le_sqrt]; norm_num
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set rJ : ℝ := (1 + Real.sqrt 3) * w with hrJ
  have hrJw : 2 * w ≤ rJ := by rw [hrJ]; nlinarith
  have hrJ0 : 0 < rJ := by linarith
  have hsq : 6 * w ^ 2 ≤ rJ ^ 2 := by
    rw [hrJ]; nlinarith [sq_nonneg w, sq_nonneg (Real.sqrt 3), mul_nonneg (sq_nonneg w) (by linarith : (0 : ℝ) ≤ Real.sqrt 3 - 1)]
  have hg := integrableOn_Ioi_rpow_of_lt (a := α - 6) (c := rJ) (by linarith) hrJ0
  have hint := intervalIntegral_le_IoiFrom (a₀ := rJ) (a := rJ) (b := R) le_rfl hR
    (f := fun r : ℝ => r ^ α * Real.exp (-(r ^ 3 / 3 - w ^ 2 / 2 * r)))
    (g := fun r : ℝ => 32 * r ^ (α - 6))
    (fun t ht => by have := lt_of_lt_of_le hrJ0 ht.1.le; positivity)
    (fun t ht => by
      have ht0 : 0 < t := lt_of_lt_of_le hrJ0 ht.1.le
      have htJ : rJ ≤ t := ht.1.le
      have ht2 : 6 * w ^ 2 ≤ t ^ 2 := by nlinarith
      have hx : 0 ≤ t ^ 3 / 4 := by positivity
      have hexp : -(t ^ 3 / 3 - w ^ 2 / 2 * t) ≤ -(t ^ 3 / 4) := by nlinarith [mul_le_mul_of_nonneg_right ht2 ht0.le]
      have hq := Real.quadratic_le_exp_of_nonneg hx
      have hE : Real.exp (-(t ^ 3 / 4)) ≤ 32 / t ^ 6 := by
        have h6 : t ^ 6 / 32 ≤ Real.exp (t ^ 3 / 4) := by
          have : t ^ 6 / 32 = (t ^ 3 / 4) ^ 2 / 2 := by ring
          rw [this]; nlinarith [hq, sq_nonneg (t ^ 3 / 4)]
        calc Real.exp (-(t ^ 3 / 4)) = (Real.exp (t ^ 3 / 4))⁻¹ := Real.exp_neg _
          _ ≤ (t ^ 6 / 32)⁻¹ := inv_anti₀ (by positivity) h6
          _ = 32 / t ^ 6 := by field_simp
      calc t ^ α * Real.exp (-(t ^ 3 / 3 - w ^ 2 / 2 * t)) ≤ t ^ α * (32 / t ^ 6) :=
            mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr hexp).trans hE) (by positivity)
        _ = 32 * t ^ (α - 6) := by
            rw [Real.rpow_sub ht0, show (t : ℝ) ^ (6 : ℝ) = t ^ 6 by norm_cast]; field_simp)
    (fun t ht => by have := lt_trans hrJ0 ht; positivity) (hg.const_mul _)
    (aesm_rpow_mul (by fun_prop) _)
  refine hint.trans ?_
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hrJ0]
  have e1 : -rJ ^ (α - 6 + 1) / (α - 6 + 1) = rJ ^ (α - 5) / (5 - α) := by
    rw [show α - 6 + 1 = α - 5 by ring, neg_div, ← div_neg, neg_sub]
  rw [e1]
  have h1 : rJ ^ (α - 5) ≤ w ^ (α - 5) :=
    Real.rpow_le_rpow_of_nonpos hw0 (by linarith) (by linarith)
  have h2 : w ^ (α - 5) ≤ w ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hw (by linarith)
  calc 32 * (rJ ^ (α - 5) / (5 - α)) = 32 / (5 - α) * rJ ^ (α - 5) := by ring
    _ ≤ 32 / (5 - α) * w ^ (-(1 : ℝ)) := mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)

end FormalResearch.SignUncertainty.CtSd
