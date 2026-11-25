module

public import FormalResearch.ModularBootstrap.Contour.RayAndArcBounds
public import FormalResearch.ModularBootstrap.ChartGeometry.MidlineAndJunction

/-!
# Uniform Saddle Contour `Γ` Through the Tip Saddle (Lemma Z')

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J6–J7, **Lemma Z'** (`vlo:Zp`,
lines 572–720).

Constructs for every saddle point `s = ρ e^{i (π/2 - φ')}` (`0 ≤ ρ ≤ ρ₀`, `0 ≤ φ' ≤ π/2`,
`b = chartB s`) a piecewise-`C^1` contour `Γ` (`segs : List ContourSeg`) from
`ω(1/2 + i T₀)` to `ω(1/2 - i T₀)` lying in `{Re ω ≥ 0}`, uniformly bounded away from `ω = 0`
(`0 < c_Γ ≤ ‖ω‖ ≤ C_Γ`) with bounded length and velocity, such that relative to
`F_+ = Re Φ_V(s; b)`:
* on the saddle rays (`upperRay`, `lowerRay`): `Re Φ_V(ζ; b) ≤ F_+ - c_γ ρ ‖ζ - s‖^2`;
* on the connecting arcs and radial segments (`arcRadial`): `Re Φ_V(ζ; b) ≤ F_+ - κ_arc ρ^3`;
* on the fixed-scale compact-escape and junction strip segments (`fixedStrip`):
  `Re Φ_V(ζ; b) ≤ F_+ - κ_strip`;
* on the crude left-edge segments (`crudeEdge`, `φ' < π/4`): `μ₀ ≤ Re ω` (`μ₀ > π ξ_* / 6`)
  and `E_c(ω; b) ≤ F_+ - c_γ ρ (Re s)^2`.

Also records the J7 midline tail decay parameters `(d₀, d₁)` at the same `T₀`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Contour

open Chart ChartGeometry ComplexBessel

/-! ### Section 1: Segment constructors and geometric helpers -/

private lemma exp_ofReal_mul_I_norm' (α : ℝ) :
    ‖Complex.exp (Complex.I * (α : ℂ))‖ = 1 := by
  rw [show Complex.I * (α : ℂ) = (α : ℂ) * Complex.I by ring, Complex.norm_exp_ofReal_mul_I]

private lemma exp_ofReal_mul_I_re'' (α : ℝ) :
    (Complex.exp (Complex.I * (α : ℂ))).re = Real.cos α := by
  rw [show Complex.I * (α : ℂ) = (α : ℂ) * Complex.I by ring, Complex.exp_ofReal_mul_I_re]

private lemma exp_ofReal_mul_I_im'' (α : ℝ) :
    (Complex.exp (Complex.I * (α : ℂ))).im = Real.sin α := by
  rw [show Complex.I * (α : ℂ) = (α : ℂ) * Complex.I by ring, Complex.exp_ofReal_mul_I_im]

private lemma arg_in_first_quad {w : ℂ} (hre : 0 < w.re) (him : 0 < w.im) :
    w.arg ∈ Ioo 0 (Real.pi / 2) := by
  have habs := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hlt : w.arg < Real.pi / 2 := (abs_lt.mp habs).2
  have hgt : 0 < w.arg := by
    by_contra hle
    have h0 : w.arg ≤ 0 := not_lt.mp hle
    have h0' : 0 ≤ -w.arg := neg_nonneg.mpr h0
    have hlt' : -w.arg < Real.pi / 2 := by linarith [(abs_lt.mp habs).1]
    have hsin_nn : 0 ≤ Real.sin (-w.arg) :=
      Real.sin_nonneg_of_nonneg_of_le_pi h0' (by linarith [Real.pi_pos])
    rw [Real.sin_neg] at hsin_nn
    have hw_ne : w ≠ 0 := fun hz => by rw [hz, Complex.zero_re] at hre; exact lt_irrefl 0 hre
    have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
    have hsin_eq : Real.sin w.arg = w.im / ‖w‖ := Complex.sin_arg w
    have hpos_sin : 0 < Real.sin w.arg := by rw [hsin_eq]; exact div_pos him hnorm
    linarith
  exact ⟨hgt, hlt⟩

private lemma arg_in_fourth_quad {w : ℂ} (hre : 0 < w.re) (him : w.im < 0) :
    w.arg ∈ Ioo (-(Real.pi / 2)) 0 := by
  have habs := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  exact ⟨(abs_lt.mp habs).1, Complex.arg_neg_iff.mpr him⟩

private lemma arg_nonpos_of_re_pos_im_nonpos {b : ℂ} (hre : 0 < b.re) (him : b.im ≤ 0) :
    b.arg ≤ 0 := by
  by_contra hgt
  have hpos : 0 < b.arg := not_le.mp hgt
  have habs := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hlt : b.arg < Real.pi := by linarith [(abs_lt.mp habs).2, Real.pi_pos]
  have hsin_pos : 0 < Real.sin b.arg := Real.sin_pos_of_pos_of_lt_pi hpos hlt
  have hsin_le : Real.sin b.arg ≤ 0 := by
    rw [Complex.sin_arg]
    exact div_nonpos_of_nonpos_of_nonneg him (norm_nonneg b)
  linarith

private noncomputable def mkStripSeg (kind : ContourPieceKind) (a b : ℝ) (hab : a ≤ b)
    (ζ ζ' : ℝ → ℂ)
    (hζ_cont : ContinuousOn ζ (Icc a b))
    (hζ_deriv : ∀ t ∈ Icc a b, HasDerivAt ζ (ζ' t) t)
    (hζ'_cont : ContinuousOn ζ' (Icc a b))
    (hstrip : ∀ t ∈ Icc a b, 0 ≤ (ζ t).re ∧ (ζ t).re ≤ 1 / 2) :
    ContourSeg where
  kind := kind
  a := a
  b := b
  hab := hab
  ω := fun t => chartOmega (ζ t)
  ω' := fun t => deriv chartOmega (ζ t) * ζ' t
  hω_cont := fun t ht => by
    have hs := hstrip t ht
    have han := (analyticAt_chartOmega hs.1 (hs.2.trans (by norm_num))).continuousAt
    exact han.continuousWithinAt.comp (hζ_cont t ht) (mapsTo_univ _ _)
  hω_deriv := fun t ht => by
    have hs := hstrip t ht
    have hd_om : HasDerivAt chartOmega (deriv chartOmega (ζ t)) (ζ t) :=
      (analyticAt_chartOmega hs.1 (hs.2.trans (by norm_num))).differentiableAt.hasDerivAt
    exact (hd_om.scomp t (hζ_deriv t ht)).congr_deriv (by rw [smul_eq_mul, mul_comm])
  hω'_cont := by
    have hd_cont : ContinuousOn (fun t => deriv chartOmega (ζ t)) (Icc a b) := fun t ht => by
      have hs := hstrip t ht
      have han := (analyticAt_chartOmega hs.1 (hs.2.trans (by norm_num))).deriv.continuousAt
      exact han.continuousWithinAt.comp (hζ_cont t ht) (mapsTo_univ _ _)
    exact hd_cont.mul hζ'_cont
  isStrip := true
  ζ := ζ
  ζ' := ζ'
  hζ_strip := fun _ t ht =>
    ⟨(hstrip t ht).1, (hstrip t ht).2, rfl, hζ_deriv t ht, hζ'_cont, rfl⟩

private noncomputable def mkStripAffineSeg (kind : ContourPieceKind) (z₀ z₁ : ℂ)
    (hz₀ : 0 ≤ z₀.re ∧ z₀.re ≤ 1 / 2) (hz₁ : 0 ≤ z₁.re ∧ z₁.re ≤ 1 / 2) : ContourSeg :=
  mkStripSeg kind 0 1 zero_le_one
    (fun t => z₀ + (t : ℂ) * (z₁ - z₀)) (fun _ => z₁ - z₀)
    (by fun_prop)
    (fun t _ => by
      have hd0 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := by
        simpa [Complex.real_smul] using (hasDerivAt_id t).smul_const (1 : ℂ)
      exact ((hd0.mul_const (z₁ - z₀)).const_add z₀).congr_deriv (by ring))
    continuousOn_const
    (fun t ht => by
      rw [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re]
      constructor <;> nlinarith [ht.1, ht.2, hz₀.1, hz₀.2, hz₁.1, hz₁.2])

private noncomputable def mkCrudeAffineSeg (w₀ w₁ : ℂ) : ContourSeg where
  kind := .crudeEdge
  a := 0
  b := 1
  hab := zero_le_one
  ω := fun t => w₀ + (t : ℂ) * (w₁ - w₀)
  ω' := fun _ => w₁ - w₀
  hω_cont := by fun_prop
  hω_deriv := fun t _ => by
    have hd0 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := by
      simpa [Complex.real_smul] using (hasDerivAt_id t).smul_const (1 : ℂ)
    exact ((hd0.mul_const (w₁ - w₀)).const_add w₀).congr_deriv (by ring)
  hω'_cont := continuousOn_const
  isStrip := false
  ζ := fun _ => 0
  ζ' := fun _ => 0
  hζ_strip := fun h => by simp at h

private noncomputable def mkStripArcSeg (r θ₀ θ₁ : ℝ)
    (hstrip : ∀ α ∈ uIcc θ₀ θ₁,
      0 ≤ ((r : ℂ) * Complex.exp (Complex.I * (α : ℂ))).re ∧
      ((r : ℂ) * Complex.exp (Complex.I * (α : ℂ))).re ≤ 1 / 2) : ContourSeg :=
  mkStripSeg .arcRadial 0 1 zero_le_one
    (fun t => (r : ℂ) * Complex.exp (Complex.I * (((1 - t) * θ₀ + t * θ₁ : ℝ) : ℂ)))
    (fun t => Complex.I * ((θ₁ - θ₀ : ℝ) : ℂ) *
      ((r : ℂ) * Complex.exp (Complex.I * (((1 - t) * θ₀ + t * θ₁ : ℝ) : ℂ))))
    (by fun_prop)
    (fun t _ => by
      have hd_r : HasDerivAt (fun x : ℝ => (1 - x) * θ₀ + x * θ₁) (θ₁ - θ₀) t := by
        have hlin : (fun x : ℝ => (1 - x) * θ₀ + x * θ₁) = fun x : ℝ => θ₀ + x * (θ₁ - θ₀) := by
          ext x; ring
        rw [hlin]
        simpa using (((hasDerivAt_id t).mul_const (θ₁ - θ₀)).const_add θ₀)
      have hd_c : HasDerivAt (fun x : ℝ => Complex.I * (((1 - x) * θ₀ + x * θ₁ : ℝ) : ℂ))
          (Complex.I * ((θ₁ - θ₀ : ℝ) : ℂ)) t := by
        have h0 : HasDerivAt (fun x : ℝ => (((1 - x) * θ₀ + x * θ₁ : ℝ) : ℂ))
            ((θ₁ - θ₀ : ℝ) : ℂ) t := by
          simpa [Complex.real_smul] using hd_r.smul_const (1 : ℂ)
        exact h0.const_mul Complex.I
      exact (hd_c.cexp.const_mul (r : ℂ)).congr_deriv (by ring))
    (by fun_prop)
    (fun t ht => by
      refine hstrip ((1 - t) * θ₀ + t * θ₁) ?_
      rw [Set.mem_uIcc]
      rcases le_total θ₀ θ₁ with hle | hge
      · left; exact ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩
      · right; exact ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩)

private noncomputable def mkStripRaySeg (kind : ContourPieceKind) (s dir : ℂ)
    (t_max : ℝ) (ht : 0 ≤ t_max)
    (hstrip : ∀ v ∈ Icc (0 : ℝ) t_max,
      0 ≤ (s + (v : ℂ) * dir).re ∧ (s + (v : ℂ) * dir).re ≤ 1 / 2) : ContourSeg :=
  mkStripSeg kind 0 t_max ht
    (fun v => s + (v : ℂ) * dir) (fun _ => dir)
    (by fun_prop)
    (fun v _ => by
      have hd0 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 v := by
        simpa [Complex.real_smul] using (hasDerivAt_id v).smul_const (1 : ℂ)
      exact ((hd0.mul_const dir).const_add s).congr_deriv (by ring))
    continuousOn_const
    hstrip

private noncomputable def mkStripRevRaySeg (kind : ContourPieceKind) (s dir : ℂ)
    (t_max : ℝ) (ht : 0 ≤ t_max)
    (hstrip : ∀ v ∈ Icc (0 : ℝ) t_max,
      0 ≤ (s + (v : ℂ) * dir).re ∧ (s + (v : ℂ) * dir).re ≤ 1 / 2) : ContourSeg :=
  mkStripSeg kind 0 t_max ht
    (fun t => s + ((t_max - t : ℝ) : ℂ) * dir) (fun _ => -dir)
    (by fun_prop)
    (fun t _ => by
      have hd0 : HasDerivAt (fun x : ℝ => ((t_max - x : ℝ) : ℂ)) (-1) t := by
        simpa [Complex.real_smul] using ((hasDerivAt_id t).const_sub t_max).smul_const (1 : ℂ)
      exact ((hd0.mul_const dir).const_add s).congr_deriv (by ring))
    continuousOn_const
    (fun t ht_mem => hstrip (t_max - t) ⟨by linarith [ht_mem.2], by linarith [ht_mem.1]⟩)

private lemma exists_ray_circle_hit {s dir : ℂ} {ρ A₀ : ℝ} (hρ_pos : 0 < ρ)
    (hA₀ : 1 < A₀) (hs_norm : ‖s‖ = ρ) (hdir_norm : ‖dir‖ = 1) :
    ∃ t_hit ∈ Icc ((A₀ - 1) * ρ) ((A₀ + 1) * ρ), ‖s + (t_hit : ℂ) * dir‖ = A₀ * ρ := by
  let f : ℝ → ℝ := fun t => ‖s + (t : ℂ) * dir‖
  have hf_cont : ContinuousOn f (Icc ((A₀ - 1) * ρ) ((A₀ + 1) * ρ)) := by fun_prop
  have hlo : f ((A₀ - 1) * ρ) ≤ A₀ * ρ := by
    have hnn : 0 ≤ (A₀ - 1) * ρ := mul_nonneg (by linarith) hρ_pos.le
    calc ‖s + (((A₀ - 1) * ρ : ℝ) : ℂ) * dir‖
        ≤ ‖s‖ + ‖(((A₀ - 1) * ρ : ℝ) : ℂ) * dir‖ := norm_add_le _ _
      _ = ρ + (A₀ - 1) * ρ := by
          rw [hs_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn, hdir_norm, mul_one]
      _ = A₀ * ρ := by ring
  have hhi : A₀ * ρ ≤ f ((A₀ + 1) * ρ) := by
    have hnn : 0 ≤ (A₀ + 1) * ρ := mul_nonneg (by linarith) hρ_pos.le
    have hsub := norm_sub_norm_le ((((A₀ + 1) * ρ : ℝ) : ℂ) * dir) (-s)
    rw [norm_neg, hs_norm, sub_neg_eq_add, add_comm ((((A₀ + 1) * ρ : ℝ) : ℂ) * dir) s,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn, hdir_norm, mul_one] at hsub
    linarith
  exact intermediate_value_Icc (by nlinarith) hf_cont ⟨hlo, hhi⟩

private lemma chartOmega_strip_sub_zero_le {C_om' : ℝ}
    (hC_om' : ∀ ζ ∈ stripClosed, ‖deriv chartOmega ζ‖ ≤ C_om' * (1 + |ζ.im|))
    {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hnorm : ‖ζ‖ ≤ 1 / 2) :
    ‖chartOmega ζ - (muStar : ℂ)‖ ≤ (3 / 2 : ℝ) * C_om' * ‖ζ‖ := by
  let g : ℝ → ℂ := chartOmega ∘ fun t => (t : ℂ) * ζ
  let g' : ℝ → ℂ := fun t => deriv chartOmega ((t : ℂ) * ζ) * ζ
  have hstrip_t : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ((t : ℂ) * ζ).re ∧ ((t : ℂ) * ζ).re ≤ 1 / 2 :=
    fun t ht => by
      rw [Complex.re_ofReal_mul]
      exact ⟨mul_nonneg ht.1 h0, (mul_le_of_le_one_left h0 ht.2).trans h1⟩
  have hg_cont : ContinuousOn g (Icc 0 1) := fun t ht => by
    have hs := hstrip_t t ht
    have han := (analyticAt_chartOmega hs.1 (hs.2.trans (by norm_num))).continuousAt
    have hc : ContinuousWithinAt (fun x : ℝ => (x : ℂ) * ζ) (Icc 0 1) t := by fun_prop
    exact ContinuousWithinAt.comp (g := chartOmega) han.continuousWithinAt hc (mapsTo_univ _ _)
  have hg_deriv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (g' t) t := fun t ht => by
    have hs := hstrip_t t (Ioo_subset_Icc_self ht)
    have hd_om : HasDerivAt chartOmega (deriv chartOmega ((t : ℂ) * ζ)) ((t : ℂ) * ζ) :=
      (analyticAt_chartOmega hs.1 (hs.2.trans (by norm_num))).differentiableAt.hasDerivAt
    have hd0 : HasDerivAt (fun x : ℝ => (x : ℂ) * ζ) ζ t := by
      simpa [Complex.real_smul] using (hasDerivAt_id t).smul_const ζ
    exact (hd_om.scomp t hd0).congr_deriv (by rw [smul_eq_mul, mul_comm])
  have hg'_cont : ContinuousOn g' (Icc 0 1) := by
    have hd_cont : ContinuousOn (fun t : ℝ => deriv chartOmega ((t : ℂ) * ζ)) (Icc 0 1) :=
      fun t ht => by
        have hs := hstrip_t t ht
        have han := (analyticAt_chartOmega hs.1 (hs.2.trans (by norm_num))).deriv.continuousAt
        have hc : ContinuousWithinAt (fun x : ℝ => (x : ℂ) * ζ) (Icc 0 1) t := by fun_prop
        exact ContinuousWithinAt.comp (g := deriv chartOmega) han.continuousWithinAt hc (mapsTo_univ _ _)
    exact hd_cont.mul continuousOn_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hg_cont hg_deriv
    (hg'_cont.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
  have hsub : g 1 - g 0 = chartOmega ζ - (muStar : ℂ) := by
    simp [g, chartOmega_zero]
  rw [← hsub, ← hftc]
  have hbd : ∀ t ∈ Icc (0 : ℝ) 1, ‖g' t‖ ≤ (3 / 2 : ℝ) * C_om' * ‖ζ‖ := fun t ht => by
    have hs := hstrip_t t ht
    have hm : (t : ℂ) * ζ ∈ stripClosed := ⟨hs.1, hs.2.trans (by norm_num)⟩
    have him : |((t : ℂ) * ζ).im| ≤ 1 / 2 := by
      have htn : ‖(t : ℂ) * ζ‖ ≤ ‖ζ‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2
      exact (Complex.abs_im_le_norm _).trans (htn.trans hnorm)
    have h1 := hC_om' _ hm
    have hC_nn : 0 ≤ C_om' := by
      have h0' := hC_om' 0 ⟨le_rfl, zero_le_one⟩
      have : (0 : ℝ) ≤ C_om' * 1 := by simpa using (norm_nonneg _).trans h0'
      linarith
    have h2 : ‖deriv chartOmega ((t : ℂ) * ζ)‖ ≤ (3 / 2 : ℝ) * C_om' := by
      calc ‖deriv chartOmega ((t : ℂ) * ζ)‖ ≤ C_om' * (1 + |((t : ℂ) * ζ).im|) := h1
        _ ≤ C_om' * (1 + 1 / 2) := mul_le_mul_of_nonneg_left (by linarith) hC_nn
        _ = (3 / 2 : ℝ) * C_om' := by ring
    dsimp [g']; rw [norm_mul]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  calc ‖∫ t in (0 : ℝ)..1, g' t‖
      ≤ ∫ t in (0 : ℝ)..1, ‖g' t‖ := intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ _t in (0 : ℝ)..1, (3 / 2 : ℝ) * C_om' * ‖ζ‖ :=
        intervalIntegral.integral_mono_on zero_le_one
          (hg'_cont.norm.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
          intervalIntegrable_const hbd
    _ = (3 / 2 : ℝ) * C_om' * ‖ζ‖ := by simp

private lemma chartOmega_horiz_diff_le {C_om' : ℝ}
    (hC_om' : ∀ ζ ∈ stripClosed, ‖deriv chartOmega ζ‖ ≤ C_om' * (1 + |ζ.im|))
    {x₀ T₀ : ℝ} (hx₀ : 0 ≤ x₀) (hx₁ : x₀ ≤ 1 / 2) :
    ‖chartOmega ((x₀ : ℂ) - Complex.I * (T₀ : ℂ)) -
        chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ))‖ ≤
      C_om' * (1 + |T₀|) * (1 / 2 - x₀) := by
  let g : ℝ → ℂ := chartOmega ∘ fun x => (x : ℂ) - Complex.I * (T₀ : ℂ)
  let g' : ℝ → ℂ := fun x => deriv chartOmega ((x : ℂ) - Complex.I * (T₀ : ℂ))
  have hre_x : ∀ x ∈ Icc x₀ (1 / 2 : ℝ),
      0 ≤ ((x : ℂ) - Complex.I * (T₀ : ℂ)).re ∧
      ((x : ℂ) - Complex.I * (T₀ : ℂ)).re ≤ 1 / 2 := fun x hx => by
    have hre : ((x : ℂ) - Complex.I * (T₀ : ℂ)).re = x := by
      simp [Complex.sub_re, Complex.mul_re]
    rw [hre]
    exact ⟨hx₀.trans hx.1, hx.2⟩
  have hg_cont : ContinuousOn g (Icc x₀ (1 / 2)) := fun x hx => by
    have hs := hre_x x hx
    have han := (analyticAt_chartOmega hs.1 (hs.2.trans (by norm_num))).continuousAt
    have hc : ContinuousWithinAt (fun y : ℝ => (y : ℂ) - Complex.I * (T₀ : ℂ)) (Icc x₀ (1 / 2)) x := by
      fun_prop
    exact ContinuousWithinAt.comp (g := chartOmega) han.continuousWithinAt hc (mapsTo_univ _ _)
  have hg_deriv : ∀ x ∈ Ioo x₀ (1 / 2 : ℝ), HasDerivAt g (g' x) x := fun x hx => by
    have hs := hre_x x (Ioo_subset_Icc_self hx)
    have hd_om : HasDerivAt chartOmega (g' x) ((x : ℂ) - Complex.I * (T₀ : ℂ)) :=
      (analyticAt_chartOmega hs.1 (hs.2.trans (by norm_num))).differentiableAt.hasDerivAt
    have hd0 : HasDerivAt (fun y : ℝ => (y : ℂ) - Complex.I * (T₀ : ℂ)) 1 x := by
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
        simpa [Complex.real_smul] using (hasDerivAt_id x).smul_const (1 : ℂ)
      exact h1.sub_const _
    exact (hd_om.scomp x hd0).congr_deriv (by simp [smul_eq_mul])
  have hg'_cont : ContinuousOn g' (Icc x₀ (1 / 2)) := fun x hx => by
    have hs := hre_x x hx
    have han := (analyticAt_chartOmega hs.1 (hs.2.trans (by norm_num))).deriv.continuousAt
    have hc : ContinuousWithinAt (fun y : ℝ => (y : ℂ) - Complex.I * (T₀ : ℂ)) (Icc x₀ (1 / 2)) x := by
      fun_prop
    exact ContinuousWithinAt.comp (g := deriv chartOmega) han.continuousWithinAt hc (mapsTo_univ _ _)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx₁ hg_cont hg_deriv
    (hg'_cont.mono (by rw [Set.uIcc_of_le hx₁])).intervalIntegrable
  have hsub : chartOmega ((x₀ : ℂ) - Complex.I * (T₀ : ℂ)) -
      chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)) = -(∫ x in x₀..(1 / 2 : ℝ), g' x) := by
    rw [hftc]; dsimp [g]; push_cast; ring_nf
  rw [hsub, norm_neg]
  have hbd : ∀ x ∈ Icc x₀ (1 / 2 : ℝ), ‖g' x‖ ≤ C_om' * (1 + |T₀|) := fun x hx => by
    have hs := hre_x x hx
    have hm : (x : ℂ) - Complex.I * (T₀ : ℂ) ∈ stripClosed := ⟨hs.1, hs.2.trans (by norm_num)⟩
    have him : |((x : ℂ) - Complex.I * (T₀ : ℂ)).im| = |T₀| := by
      simp [Complex.sub_im, abs_neg]
    have h1 := hC_om' _ hm
    rwa [him] at h1
  calc ‖∫ x in x₀..(1 / 2 : ℝ), g' x‖
      ≤ ∫ x in x₀..(1 / 2 : ℝ), ‖g' x‖ := intervalIntegral.norm_integral_le_integral_norm hx₁
    _ ≤ ∫ _x in x₀..(1 / 2 : ℝ), C_om' * (1 + |T₀|) :=
        intervalIntegral.integral_mono_on hx₁
          (hg'_cont.norm.mono (by rw [Set.uIcc_of_le hx₁])).intervalIntegrable
          intervalIntegrable_const hbd
    _ = C_om' * (1 + |T₀|) * (1 / 2 - x₀) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring

private lemma radial_H_le_zero_limit {η : ℂ → ℂ → ℂ} {ρ_F C_F : ℝ}
    (hCF_nn : 0 ≤ C_F) (hη_an : AnalyticOnNhd ℂ (Function.uncurry η) (ball (0 : ℂ × ℂ) ρ_F))
    (hF_id : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      2 * Complex.log (chartB w / chartB s) * deriv chartOmega w =
        ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (w ^ 2 - s ^ 2) * (1 + η w s))
    (hη_bd : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F, ‖η w s‖ ≤ C_F * (‖w‖ + ‖s‖))
    {σ δ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hδ_pos : 0 < δ) (hδ_lt : δ < min ρ_F (1 / 2))
    (h_eta_small : C_F * (5 / 4 * δ) * (1 + 1 / 16) ≤ 1 / 4) :
    ∀ r ∈ Icc (0 : ℝ) δ,
      (chartPhiV ((r : ℂ) * Complex.exp (Complex.I * ((σ * Real.pi / 3 : ℝ) : ℂ))) (xiStar : ℂ)).re ≤
        (chartPhiV 0 (xiStar : ℂ)).re := by
  intro r hr
  rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
  · simp
  · let dir : ℂ := Complex.exp (Complex.I * ((σ * Real.pi / 3 : ℝ) : ℂ))
    let f : ℝ → ℝ := fun x => (chartPhiV ((x : ℂ) * dir) (xiStar : ℂ)).re
    have hdir_re : dir.re = 1 / 2 := by
      dsimp [dir]; rw [exp_ofReal_mul_I_re'']
      rcases hσ with rfl | rfl
      · simp [Real.cos_pi_div_three]
      · rw [show (-1 * Real.pi / 3 : ℝ) = -(Real.pi / 3) by ring, Real.cos_neg, Real.cos_pi_div_three]
    have hle_eps : ∀ x ∈ Ioo (0 : ℝ) r, f r ≤ f x := fun x hx => by
      have hanti := radial_H_antitone hCF_nn hη_an hF_id hη_bd (s := (0 : ℂ)) (b := (xiStar : ℂ))
        xiStar_pos chartB_zero.symm (mem_ball_self (lt_of_lt_of_le hδ_pos (hδ_lt.le.trans (min_le_left _ _))))
        hσ hx.1 (hx.2.le.trans hr.2) hδ_lt (by simpa using (div_pos hx.1 (by norm_num)).le) h_eta_small
      exact hanti ⟨le_rfl, hx.2.le.trans hr.2⟩ ⟨hx.2.le, hr.2⟩ hx.2.le
    have hf_cont : ContinuousWithinAt f (Icc 0 δ) 0 := by
      have hm : MapsTo (fun x : ℝ => (x : ℂ) * dir) (Icc 0 δ) {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 / 2} :=
        fun x hx => by
          change 0 ≤ ((x : ℂ) * dir).re ∧ ((x : ℂ) * dir).re ≤ 1 / 2
          rw [Complex.re_ofReal_mul, hdir_re]
          have hδ12 : δ ≤ 1 / 2 := hδ_lt.le.trans (min_le_right _ _)
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hc_strip : ContinuousWithinAt (fun w : ℂ => chartPhiV w (xiStar : ℂ))
          {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 / 2} 0 :=
        ((lemma_S5_deriv xiStar_pos).2.2 0 le_rfl (by norm_num) (by norm_num)).continuousWithinAt
      have hc_line : ContinuousWithinAt (fun x : ℝ => (x : ℂ) * dir) (Icc 0 δ) 0 := by fun_prop
      have hc_c : ContinuousWithinAt (fun x : ℝ => chartPhiV ((x : ℂ) * dir) (xiStar : ℂ)) (Icc 0 δ) 0 :=
        hc_strip.comp_of_eq hc_line hm (by simp)
      exact Complex.continuous_re.continuousAt.comp_continuousWithinAt hc_c
    have hsub : Ioo (0 : ℝ) r ⊆ Icc 0 δ := fun x hx => ⟨hx.1.le, hx.2.le.trans hr.2⟩
    have htend : Tendsto f (𝓝[Ioo 0 r] 0) (𝓝 (f 0)) := hf_cont.mono hsub
    have hnb : (𝓝[Ioo (0 : ℝ) r] 0).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hr_pos.ne]
      exact ⟨le_rfl, hr_pos.le⟩
    have hgoal : f r ≤ f 0 := ge_of_tendsto htend (eventually_nhdsWithin_of_forall hle_eps)
    dsimp only [f, dir] at hgoal
    rw [Complex.ofReal_zero, zero_mul] at hgoal
    exact hgoal

private lemma mul_div_add_one_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * (b / (a + 1)) ≤ b := by
  have ha1 : 0 < a + 1 := by linarith
  calc a * (b / (a + 1)) ≤ (a + 1) * (b / (a + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hb ha1.le)
    _ = b := mul_div_cancel₀ b ha1.ne'

/-! ### Section 2: Uniform contour parameters and Lemma Z' (`vlo:Zp`) -/

/-- Uniform geometric and analytic parameters for the saddle contour `Γ` of Lemma Z' (`vlo:Zp`). -/
structure ZPConfig where
  δ : ℝ
  ρ₀ : ℝ
  c_γ : ℝ
  T₀ : ℝ
  μ₀ : ℝ
  c_Γ : ℝ
  C_Γ : ℝ
  C_len : ℝ
  C_d : ℝ
  κ_arc : ℝ
  κ_strip : ℝ
  d₀ : ℝ
  d₁ : ℝ
  hδ_pos : 0 < δ
  hδ_j10 : δ ≤ j10Delta0
  hρ₀_pos : 0 < ρ₀
  hc_γ_pos : 0 < c_γ
  hT₀_ge : 4 ≤ T₀
  hμ₀_gt : Real.pi * xiStar / 6 < μ₀
  hc_Γ_pos : 0 < c_Γ
  hc_Γ_le : c_Γ ≤ C_Γ
  hC_len_pos : 0 < C_len
  hC_d_pos : 0 < C_d
  hκ_arc_pos : 0 < κ_arc
  hκ_strip_pos : 0 < κ_strip
  hd₀_pos : 0 < d₀
  hd₁_pos : 0 < d₁
  hmid_tail : ∀ τ ≥ T₀, (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (xiStar : ℂ)).re ≤
    -d₀ - d₁ * (τ - T₀)

private lemma zp_upper_ray_arc {η : ℂ → ℂ → ℂ} {ρ_F C_F : ℝ}
    (hCF_nn : 0 ≤ C_F)
    (hη_an : AnalyticOnNhd ℂ (Function.uncurry η) (ball (0 : ℂ × ℂ) ρ_F))
    (hF_id : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      2 * Complex.log (chartB w / chartB s) * deriv chartOmega w =
        ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (w ^ 2 - s ^ 2) * (1 + η w s))
    (hη_bd : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      ‖η w s‖ ≤ C_F * (‖w‖ + ‖s‖))
    (_hρF_pos : 0 < ρ_F)
    {δ ρ₀ ρ φ' c_γ κ_arc : ℝ}
    (_hδ_pos : 0 < δ) (hδ_14 : δ ≤ 1 / 4) (hδ_rhoF : δ < min ρ_F (1 / 2))
    (hCF_delta : C_F * δ ≤ 1 / 80)
    (hρ₀_pos : 0 < ρ₀) (hρ₀_delta : 12 * ρ₀ ≤ δ) (hρ₀_arc : 4000 * C_F * ρ₀ ≤ 1)
    (hρ_nn : 0 ≤ ρ) (hρ_le : ρ ≤ ρ₀) (hφ_nn : 0 ≤ φ') (hφ_le : φ' ≤ Real.pi / 2)
    (hcγ_le_pi4 : c_γ ≤ Real.pi ^ 2 / 24) (hκ_arc_eq : κ_arc = 10 * Real.pi ^ 2)
    {s b : ℂ}
    (hs_eq : s = (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 - φ' : ℝ) : ℂ)))
    (hb_eq : b = chartB s) (hb_re_pos : 0 < b.re) :
    let dir_plus : ℂ := Complex.exp (Complex.I * ((Real.pi / 3 : ℝ) : ℂ))
    ∃ (t_plus θ_plus : ℝ),
      t_plus ∈ Icc (9 * ρ) (11 * ρ) ∧
      θ_plus ∈ Icc (0 : ℝ) (Real.pi / 2) ∧
      s + (t_plus : ℂ) * dir_plus = ((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (θ_plus : ℂ)) ∧
      (∀ v ∈ Icc (0 : ℝ) t_plus,
        (chartPhiV (s + (v : ℂ) * dir_plus) b).re ≤ (chartPhiV s b).re - c_γ * ρ * v ^ 2) ∧
      (∀ α ∈ uIcc (Real.pi / 3) θ_plus,
        (chartPhiV (((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (α : ℂ))) b).re ≤
          (chartPhiV s b).re - κ_arc * ρ ^ 3) := by
  intro dir_plus
  have hs_norm : ‖s‖ = ρ := by
    rw [hs_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ_nn, exp_ofReal_mul_I_norm', mul_one]
  have hs_re_nn : 0 ≤ s.re := by
    rw [hs_eq, Complex.re_ofReal_mul, exp_ofReal_mul_I_re'']
    exact mul_nonneg hρ_nn (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩)
  have hs_im_nn : 0 ≤ s.im := by
    rw [hs_eq, Complex.im_ofReal_mul, exp_ofReal_mul_I_im'']
    exact mul_nonneg hρ_nn (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]))
  have h11ρ_δ : 11 * ρ ≤ δ := by linarith only [hρ_nn, hρ_le, hρ₀_delta]
  have hs_F : s ∈ ball (0 : ℂ) ρ_F := by
    rw [mem_ball_zero_iff, hs_norm]
    exact lt_trans (by linarith only [hρ_le, hρ₀_delta, hρ₀_pos] : ρ < δ) (lt_of_lt_of_le hδ_rhoF (min_le_left _ _))
  have hdir_plus_re : dir_plus.re = 1 / 2 := by
    dsimp [dir_plus]; rw [exp_ofReal_mul_I_re'', Real.cos_pi_div_three]
  have hdir_plus_im : dir_plus.im = √3 / 2 := by
    dsimp [dir_plus]; rw [exp_ofReal_mul_I_im'', Real.sin_pi_div_three]
  have hdir_plus_norm : ‖dir_plus‖ = 1 := exp_ofReal_mul_I_norm' _
  rcases eq_or_lt_of_le hρ_nn with rfl | hρ_pos
  · refine ⟨0, Real.pi / 3, by simp, ⟨by positivity, by linarith only [Real.pi_pos]⟩, ?_, ?_, ?_⟩
    · have hs0 : s = 0 := by simp [hs_eq]
      simp [hs0]
    · intro v hv; have hv0 : v = 0 := le_antisymm hv.2 hv.1; subst hv0; simp
    · intro α _
      have hs0 : s = 0 := by simp [hs_eq]
      simp [hs0]
  · obtain ⟨t_plus, ht_mem, hnorm_eq⟩ := exists_ray_circle_hit hρ_pos (A₀ := 10) (by norm_num) hs_norm hdir_plus_norm
    have ht_range : t_plus ∈ Icc (9 * ρ) (11 * ρ) := by
      have h1 : (10 - 1 : ℝ) * ρ = 9 * ρ := by ring
      have h2 : (10 + 1 : ℝ) * ρ = 11 * ρ := by ring
      rwa [h1, h2] at ht_mem
    let w_plus := s + (t_plus : ℂ) * dir_plus
    have hw_re_pos : 0 < w_plus.re := by
      have htd : ((t_plus : ℂ) * dir_plus).re = t_plus / 2 := by
        rw [Complex.re_ofReal_mul, hdir_plus_re]; ring
      have htp : 0 < t_plus := by linarith only [ht_range.1, hρ_pos]
      dsimp [w_plus]; rw [htd]; linarith only [hs_re_nn, htp]
    have hw_im_pos : 0 < w_plus.im := by
      have htd : ((t_plus : ℂ) * dir_plus).im = t_plus * √3 / 2 := by
        rw [Complex.im_ofReal_mul, hdir_plus_im]; ring
      have htp : 0 < t_plus := by linarith only [ht_range.1, hρ_pos]
      have hsq3 : 0 < √3 := by positivity
      dsimp [w_plus]; rw [htd]; nlinarith only [hs_im_nn, htp, hsq3]
    have harg_mem := arg_in_first_quad hw_re_pos hw_im_pos
    let θ_plus := w_plus.arg
    have hw_polar : w_plus = ((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (θ_plus : ℂ)) := by
      have h := Complex.norm_mul_exp_arg_mul_I w_plus
      rw [hnorm_eq] at h
      rw [← h, mul_comm Complex.I (θ_plus : ℂ)]
    have h_ray_strip : ∀ v ∈ Icc (0 : ℝ) t_plus,
        s + (v : ℂ) * dir_plus ∈ ball (0 : ℂ) ρ_F ∧
        0 ≤ (s + (v : ℂ) * dir_plus).re ∧ (s + (v : ℂ) * dir_plus).re ≤ 1 / 4 := fun v hv => by
      have hvn : ‖s + (v : ℂ) * dir_plus‖ ≤ 12 * ρ := by
        calc ‖s + (v : ℂ) * dir_plus‖ ≤ ‖s‖ + ‖(v : ℂ) * dir_plus‖ := norm_add_le _ _
          _ = ρ + v := by rw [hs_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hv.1, hdir_plus_norm, mul_one]
          _ ≤ 12 * ρ := by linarith only [hv.2, ht_range.2]
      have hltF : ‖s + (v : ℂ) * dir_plus‖ < ρ_F :=
        (hvn.trans (mul_le_mul_of_nonneg_left hρ_le (by norm_num))).trans_lt (hρ₀_delta.trans_lt (hδ_rhoF.trans_le (min_le_left _ _)))
      have hre0 : 0 ≤ (s + (v : ℂ) * dir_plus).re := by
        have hvd : ((v : ℂ) * dir_plus).re = v / 2 := by
          rw [Complex.re_ofReal_mul, hdir_plus_re]; ring
        change 0 ≤ s.re + ((v : ℂ) * dir_plus).re
        rw [hvd]; linarith only [hs_re_nn, hv.1]
      have hre14 : (s + (v : ℂ) * dir_plus).re ≤ 1 / 4 :=
        (Complex.re_le_norm _).trans (hvn.trans ((mul_le_mul_of_nonneg_left hρ_le (by norm_num)).trans (hρ₀_delta.trans hδ_14)))
      exact ⟨mem_ball_zero_iff.mpr hltF, hre0, hre14⟩
    have h_ray_bd : ∀ v ∈ Icc (0 : ℝ) t_plus,
        (chartPhiV (s + (v : ℂ) * dir_plus) b).re ≤ (chartPhiV s b).re - c_γ * ρ * v ^ 2 := fun v hv => by
      have hsr := saddle_ray_H_le hCF_nn hη_an hF_id hη_bd hρ_nn (by linarith only [ht_range.1, hρ_pos])
        s b hs_eq hb_re_pos hb_eq hs_F h_ray_strip v hv
      have hcos1 := upper_ray_cos_le hφ_nn hφ_le
      have hcos3 : Real.cos (3 * (Real.pi / 3)) = -1 := by
        rw [show 3 * (Real.pi / 3) = Real.pi by ring, Real.cos_pi]
      have hsq_split : (ρ + v) ^ 2 ≤ 2 * ρ ^ 2 + 2 * v ^ 2 := by nlinarith only [sq_nonneg (ρ - v)]
      have hv_ub : v ≤ 11 * ρ := hv.2.trans ht_range.2
      have hCF_r : 4 * C_F * ρ ≤ 1 / 4 := by
        have hρδ : ρ ≤ δ := by linarith only [hρ_le, hρ₀_delta, hρ₀_pos]
        have h4 : 4 * C_F * ρ ≤ 4 * C_F * δ := mul_le_mul_of_nonneg_left hρδ (by positivity)
        linarith only [h4, hCF_delta]
      have hCF_v : 4 * C_F * v ≤ 1 / 6 := by
        have hv_del : v ≤ δ := by linarith only [hv_ub, h11ρ_δ]
        have h4v : 4 * C_F * v ≤ 4 * C_F * δ := mul_le_mul_of_nonneg_left hv_del (by positivity)
        linarith only [h4v, hCF_delta]
      have hrem_sq : 2 * C_F * v ^ 2 * (ρ + v) ^ 2 ≤ (1 / 4 : ℝ) * ρ * v ^ 2 + (1 / 6 : ℝ) * v ^ 3 := by
        have hv2_nn : 0 ≤ v ^ 2 := sq_nonneg v
        have hv3_nn : 0 ≤ v ^ 3 := pow_nonneg hv.1 3
        calc 2 * C_F * v ^ 2 * (ρ + v) ^ 2
            ≤ 2 * C_F * v ^ 2 * (2 * ρ ^ 2 + 2 * v ^ 2) :=
              mul_le_mul_of_nonneg_left hsq_split (by positivity)
          _ = (4 * C_F * ρ) * (ρ * v ^ 2) + (4 * C_F * v) * v ^ 3 := by ring
          _ ≤ (1 / 4 : ℝ) * (ρ * v ^ 2) + (1 / 6 : ℝ) * v ^ 3 :=
              add_le_add (mul_le_mul_of_nonneg_right hCF_r (mul_nonneg hρ_nn hv2_nn))
                (mul_le_mul_of_nonneg_right hCF_v hv3_nn)
          _ = (1 / 4 : ℝ) * ρ * v ^ 2 + (1 / 6 : ℝ) * v ^ 3 := by ring
      have hcos1_mul : ρ * v ^ 2 * Real.cos (2 * (Real.pi / 3) + Real.pi / 2 - φ') ≤ -(1 / 2) * ρ * v ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left hcos1 (mul_nonneg hρ_nn (sq_nonneg v))
        linarith only [hmul]
      have hinner_neg : ρ * v ^ 2 * Real.cos (2 * (Real.pi / 3) + Real.pi / 2 - φ') +
          (1 / 3 : ℝ) * v ^ 3 * Real.cos (3 * (Real.pi / 3)) + 2 * C_F * v ^ 2 * (ρ + v) ^ 2 ≤
          -(1 / 4 : ℝ) * ρ * v ^ 2 - (1 / 6 : ℝ) * v ^ 3 := by
        rw [hcos3]; linarith only [hcos1_mul, hrem_sq]
      have hmain_pi : (chartPhiV (s + (v : ℂ) * dir_plus) b).re - (chartPhiV s b).re ≤
          -(Real.pi ^ 2 / 24) * ρ * v ^ 2 - (Real.pi ^ 2 / 36) * v ^ 3 := by
        have hmul := mul_le_mul_of_nonneg_left hinner_neg (by positivity : 0 ≤ Real.pi ^ 2 / 6)
        linarith only [hsr, hmul]
      have hv3_nn : 0 ≤ (Real.pi ^ 2 / 36) * v ^ 3 := by have := hv.1; positivity
      have hc_mul : c_γ * ρ * v ^ 2 ≤ (Real.pi ^ 2 / 24) * ρ * v ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcγ_le_pi4 hρ_nn) (sq_nonneg v)
      linarith only [hmain_pi, hv3_nn, hc_mul]
    have hw_gain : (chartPhiV w_plus b).re ≤ (chartPhiV s b).re - 20 * Real.pi ^ 2 * ρ ^ 3 := by
      have hsr := saddle_ray_H_le hCF_nn hη_an hF_id hη_bd hρ_nn (by linarith only [ht_range.1, hρ_pos])
        s b hs_eq hb_re_pos hb_eq hs_F h_ray_strip t_plus ⟨by linarith only [ht_range.1, hρ_pos], le_rfl⟩
      have hcos1 := upper_ray_cos_le hφ_nn hφ_le
      have hcos3 : Real.cos (3 * (Real.pi / 3)) = -1 := by
        rw [show 3 * (Real.pi / 3) = Real.pi by ring, Real.cos_pi]
      have hsq_split : (ρ + t_plus) ^ 2 ≤ 2 * ρ ^ 2 + 2 * t_plus ^ 2 := by nlinarith only [sq_nonneg (ρ - t_plus)]
      have ht_nn : 0 ≤ t_plus := by linarith only [ht_range.1, hρ_pos]
      have hCF_r : 4 * C_F * ρ ≤ 1 / 4 := by
        have hρδ : ρ ≤ δ := by linarith only [hρ_le, hρ₀_delta, hρ₀_pos]
        have h4 : 4 * C_F * ρ ≤ 4 * C_F * δ := mul_le_mul_of_nonneg_left hρδ (by positivity)
        linarith only [h4, hCF_delta]
      have hCF_v : 4 * C_F * t_plus ≤ 1 / 6 := by
        have hv_del : t_plus ≤ δ := by linarith only [ht_range.2, h11ρ_δ]
        have h4v : 4 * C_F * t_plus ≤ 4 * C_F * δ := mul_le_mul_of_nonneg_left hv_del (by positivity)
        linarith only [h4v, hCF_delta]
      have hrem_sq : 2 * C_F * t_plus ^ 2 * (ρ + t_plus) ^ 2 ≤ (1 / 4 : ℝ) * ρ * t_plus ^ 2 + (1 / 6 : ℝ) * t_plus ^ 3 := by
        have ht2_nn : 0 ≤ t_plus ^ 2 := sq_nonneg t_plus
        have ht3_nn : 0 ≤ t_plus ^ 3 := pow_nonneg ht_nn 3
        calc 2 * C_F * t_plus ^ 2 * (ρ + t_plus) ^ 2
            ≤ 2 * C_F * t_plus ^ 2 * (2 * ρ ^ 2 + 2 * t_plus ^ 2) :=
              mul_le_mul_of_nonneg_left hsq_split (by positivity)
          _ = (4 * C_F * ρ) * (ρ * t_plus ^ 2) + (4 * C_F * t_plus) * t_plus ^ 3 := by ring
          _ ≤ (1 / 4 : ℝ) * (ρ * t_plus ^ 2) + (1 / 6 : ℝ) * t_plus ^ 3 :=
              add_le_add (mul_le_mul_of_nonneg_right hCF_r (mul_nonneg hρ_nn ht2_nn))
                (mul_le_mul_of_nonneg_right hCF_v ht3_nn)
          _ = (1 / 4 : ℝ) * ρ * t_plus ^ 2 + (1 / 6 : ℝ) * t_plus ^ 3 := by ring
      have hcos1_mul : ρ * t_plus ^ 2 * Real.cos (2 * (Real.pi / 3) + Real.pi / 2 - φ') ≤ -(1 / 2) * ρ * t_plus ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left hcos1 (mul_nonneg hρ_nn (sq_nonneg t_plus))
        linarith only [hmul]
      have hinner_neg : ρ * t_plus ^ 2 * Real.cos (2 * (Real.pi / 3) + Real.pi / 2 - φ') +
          (1 / 3 : ℝ) * t_plus ^ 3 * Real.cos (3 * (Real.pi / 3)) + 2 * C_F * t_plus ^ 2 * (ρ + t_plus) ^ 2 ≤
          -(1 / 4 : ℝ) * ρ * t_plus ^ 2 - (1 / 6 : ℝ) * t_plus ^ 3 := by
        rw [hcos3]; linarith only [hcos1_mul, hrem_sq]
      have hmain_pi : (chartPhiV w_plus b).re - (chartPhiV s b).re ≤ -(Real.pi ^ 2 / 36) * t_plus ^ 3 := by
        have hmul := mul_le_mul_of_nonneg_left hinner_neg (by positivity : 0 ≤ Real.pi ^ 2 / 6)
        have hr_nn : 0 ≤ (Real.pi ^ 2 / 24) * ρ * t_plus ^ 2 := by positivity
        linarith only [hsr, hmul, hr_nn]
      have hcube_lb : 729 * ρ ^ 3 ≤ t_plus ^ 3 := by
        have h1 := pow_le_pow_left₀ (by linarith only [hρ_pos] : 0 ≤ 9 * ρ) ht_range.1 3
        linarith only [h1]
      have h20 : 20 * Real.pi ^ 2 * ρ ^ 3 ≤ (Real.pi ^ 2 / 36) * t_plus ^ 3 := by
        have hpi2 := sq_nonneg Real.pi
        have hr3 := pow_nonneg hρ_pos.le 3
        have h1 : 20 * Real.pi ^ 2 * ρ ^ 3 ≤ (Real.pi ^ 2 / 36) * (729 * ρ ^ 3) := by
          nlinarith only [hpi2, hr3]
        exact h1.trans (mul_le_mul_of_nonneg_left hcube_lb (by positivity))
      linarith only [hmain_pi, h20]
    refine ⟨t_plus, θ_plus, ht_range, ⟨harg_mem.1.le, harg_mem.2.le⟩, hw_polar, h_ray_bd, ?_⟩
    intro α hα
    have harc_mem : ∀ β ∈ uIcc θ_plus (Real.pi / 3),
        let w := ((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (β : ℂ))
        0 ≤ w.re ∧ w.re ≤ 1 / 4 := fun β hβ => by
      dsimp
      have hβ_mem : β ∈ Icc 0 (Real.pi / 2) := by
        rw [Set.mem_uIcc] at hβ
        rcases hβ with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨harg_mem.1.le.trans h1, h2.trans (by linarith only [Real.pi_pos])⟩
        · exact ⟨(by positivity : (0 : ℝ) ≤ Real.pi / 3).trans h1, h2.trans harg_mem.2.le⟩
      rw [Complex.re_ofReal_mul, exp_ofReal_mul_I_re'']
      refine ⟨mul_nonneg (by positivity) (Real.cos_nonneg_of_mem_Icc ⟨by linarith only [hβ_mem.1, Real.pi_pos], hβ_mem.2⟩), ?_⟩
      calc 10 * ρ * Real.cos β ≤ 10 * ρ * 1 :=
            mul_le_mul_of_nonneg_left (Real.cos_le_one β) (by positivity)
        _ ≤ 10 * ρ₀ := by linarith only [hρ_le]
        _ ≤ 1 / 4 := by linarith only [hρ₀_delta, hδ_14]
    have harc_step := arc_H_step_le hCF_nn hη_an hF_id hη_bd hb_re_pos hb_eq hs_F
      (r := 10 * ρ) (θ₀ := θ_plus) (θ₁ := Real.pi / 3) (by positivity)
      (by calc 10 * ρ ≤ 10 * ρ₀ := by linarith only [hρ_le]
        _ < δ := by linarith only [hρ₀_delta, hρ₀_pos]
        _ < ρ_F := hδ_rhoF.trans_le (min_le_left _ _))
      (by rw [hs_norm]; linarith only [hρ_pos])
      (by rw [abs_le]; constructor <;> linarith only [harg_mem.1, harg_mem.2, Real.pi_pos])
      harc_mem (fun β hβ => cos_three_le_of_upper_arc harg_mem.1.le harg_mem.2.le hβ)
    have hstep_bd : (Real.pi ^ 2 / 6) * (Real.pi / 2) * (10 * ρ) * (‖s‖ ^ 2 + 4 * C_F * (10 * ρ) ^ 3) ≤
        7 * Real.pi ^ 2 * ρ ^ 3 := by
      rw [hs_norm]
      have hcf4 : 4 * C_F * (10 * ρ) ^ 3 ≤ ρ ^ 2 := by
        have h4000 : 4000 * C_F * ρ ≤ 1 := by
          calc 4000 * C_F * ρ ≤ 4000 * C_F * ρ₀ :=
                mul_le_mul_of_nonneg_left hρ_le (by positivity)
            _ ≤ 1 := hρ₀_arc
        calc 4 * C_F * (10 * ρ) ^ 3 = (4000 * C_F * ρ) * ρ ^ 2 := by ring
          _ ≤ 1 * ρ ^ 2 := mul_le_mul_of_nonneg_right h4000 (sq_nonneg ρ)
          _ = ρ ^ 2 := one_mul _
      have hsum : ρ ^ 2 + 4 * C_F * (10 * ρ) ^ 3 ≤ 2 * ρ ^ 2 := by
        rw [two_mul]; exact add_le_add_right hcf4 _
      have h1 : (Real.pi ^ 2 / 6) * (Real.pi / 2) * (10 * ρ) * (ρ ^ 2 + 4 * C_F * (10 * ρ) ^ 3) ≤
          (Real.pi ^ 2 / 6) * (Real.pi / 2) * (10 * ρ) * (2 * ρ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      have h2 : (Real.pi ^ 2 / 6) * (Real.pi / 2) * (10 * ρ) * (2 * ρ ^ 2) =
          (5 * Real.pi / 3) * Real.pi ^ 2 * ρ ^ 3 := by ring
      have hpi4 : 5 * Real.pi / 3 ≤ 7 := by linarith only [Real.pi_lt_four]
      exact h1.trans (h2.symm ▸ mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpi4 (sq_nonneg Real.pi)) (pow_nonneg hρ_pos.le 3))
    have hw0_eq : ((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (θ_plus : ℂ)) = w_plus := hw_polar.symm
    rw [hw0_eq] at harc_step
    have hα_step := harc_step α (by rw [Set.uIcc_comm]; exact hα)
    rw [hκ_arc_eq]
    have h13 : 10 * Real.pi ^ 2 * ρ ^ 3 ≤ 13 * Real.pi ^ 2 * ρ ^ 3 := by
      have hpi2 := sq_nonneg Real.pi; have hr3 := pow_nonneg hρ_pos.le 3; nlinarith only [hpi2, hr3]
    linarith only [hα_step, hstep_bd, hw_gain, h13]

private lemma zp_lower_arcA_gain {C_F δ ρ c_neg t_m φ' : ℝ} {s w_m b : ℂ}
    (hCF_nn : 0 ≤ C_F) (hCF_delta : C_F * δ ≤ 1 / 80) (hCF_delta_cneg : C_F * δ ≤ c_neg / (16 * 44))
    (hc_neg_pos : 0 < c_neg) (hc_neg_ub : c_neg ≤ -Real.cos (7 * Real.pi / 12))
    (hρ_pos : 0 < ρ) (hρ_le_δ : ρ ≤ δ) (ht_range : t_m ∈ Icc (9 * ρ) (11 * ρ)) (h11ρ_δ : 11 * ρ ≤ δ)
    (h_inv_sq2 : 1 / √2 = √2 / 2)
    (hcos3_m : Real.cos (3 * (-(5 * Real.pi / 12))) = -(1 / √2))
    (hcos2_m : Real.cos (2 * (-(5 * Real.pi / 12)) + Real.pi / 2 - φ') ≤ Real.cos (7 * Real.pi / 12))
    (hsr : (chartPhiV w_m b).re - (chartPhiV s b).re ≤ (Real.pi ^ 2 / 6) *
      (ρ * t_m ^ 2 * Real.cos (2 * (-(5 * Real.pi / 12)) + Real.pi / 2 - φ') +
       (1 / 3 : ℝ) * t_m ^ 3 * Real.cos (3 * (-(5 * Real.pi / 12))) +
       2 * C_F * t_m ^ 2 * (ρ + t_m) ^ 2)) :
    (chartPhiV w_m b).re ≤ (chartPhiV s b).re - 20 * Real.pi ^ 2 * ρ ^ 3 := by
  have ht_nn : 0 ≤ t_m := by linarith only [ht_range.1, hρ_pos]
  have hsq_split : (ρ + t_m) ^ 2 ≤ 2 * ρ ^ 2 + 2 * t_m ^ 2 := by nlinarith only [sq_nonneg (ρ - t_m)]
  have hCF_r : 4 * C_F * ρ ≤ c_neg / 2 := by
    have h4 : 4 * C_F * ρ ≤ 4 * C_F * δ := mul_le_mul_of_nonneg_left hρ_le_δ (by positivity)
    linarith only [h4, hCF_delta_cneg, hc_neg_pos]
  have hcos_neg_le : Real.cos (2 * (-(5 * Real.pi / 12)) + Real.pi / 2 - φ') ≤ -c_neg := by
    linarith only [hcos2_m, hc_neg_ub]
  have hcos1_mul : ρ * t_m ^ 2 * Real.cos (2 * (-(5 * Real.pi / 12)) + Real.pi / 2 - φ') ≤ -c_neg * ρ * t_m ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hcos_neg_le (mul_nonneg hρ_pos.le (sq_nonneg t_m))
    linarith only [hmul]
  have hcube_lb : 729 * ρ ^ 3 ≤ t_m ^ 3 := by
    have h1 := pow_le_pow_left₀ (by linarith only [hρ_pos] : 0 ≤ 9 * ρ) ht_range.1 3
    linarith only [h1]
  have hsq2_lb : (1.4 : ℝ) ≤ √2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.4)]; exact Real.sqrt_le_sqrt (by norm_num)
  have h13_sq2 : (0.23 : ℝ) ≤ (1 / 3 : ℝ) * (1 / √2) := by
    rw [h_inv_sq2]; linarith only [hsq2_lb]
  have hCF_v' : 4 * C_F * t_m ≤ 0.05 := by
    have hv_del : t_m ≤ δ := by linarith only [ht_range.2, h11ρ_δ]
    have h4 : 4 * C_F * t_m ≤ 4 * C_F * δ := mul_le_mul_of_nonneg_left hv_del (by positivity)
    linarith only [h4, hCF_delta]
  have hcos3_ub' : (1 / 3 : ℝ) * t_m ^ 3 * Real.cos (3 * (-(5 * Real.pi / 12))) ≤ -(0.23) * t_m ^ 3 := by
    rw [hcos3_m]; have ht3 := pow_nonneg ht_nn 3; nlinarith only [h13_sq2, ht3]
  have hrem_sq' : 2 * C_F * t_m ^ 2 * (ρ + t_m) ^ 2 ≤ (c_neg / 2) * ρ * t_m ^ 2 + (0.05 : ℝ) * t_m ^ 3 := by
    have ht2_nn : 0 ≤ t_m ^ 2 := sq_nonneg t_m
    have ht3_nn : 0 ≤ t_m ^ 3 := pow_nonneg ht_nn 3
    calc 2 * C_F * t_m ^ 2 * (ρ + t_m) ^ 2
        ≤ 2 * C_F * t_m ^ 2 * (2 * ρ ^ 2 + 2 * t_m ^ 2) := mul_le_mul_of_nonneg_left hsq_split (by positivity)
      _ = (4 * C_F * ρ) * (ρ * t_m ^ 2) + (4 * C_F * t_m) * t_m ^ 3 := by ring
      _ ≤ (c_neg / 2) * (ρ * t_m ^ 2) + (0.05 : ℝ) * t_m ^ 3 :=
          add_le_add (mul_le_mul_of_nonneg_right hCF_r (mul_nonneg hρ_pos.le ht2_nn))
            (mul_le_mul_of_nonneg_right hCF_v' ht3_nn)
      _ = (c_neg / 2) * ρ * t_m ^ 2 + (0.05 : ℝ) * t_m ^ 3 := by ring
  have hinner_neg' : ρ * t_m ^ 2 * Real.cos (2 * (-(5 * Real.pi / 12)) + Real.pi / 2 - φ') +
      (1 / 3 : ℝ) * t_m ^ 3 * Real.cos (3 * (-(5 * Real.pi / 12))) + 2 * C_F * t_m ^ 2 * (ρ + t_m) ^ 2 ≤
      -(1 / 6 : ℝ) * t_m ^ 3 := by
    have hcn_nn : 0 ≤ (c_neg / 2) * ρ * t_m ^ 2 := by positivity
    have ht3_nn : (0 : ℝ) ≤ t_m ^ 3 := pow_nonneg ht_nn 3
    linarith only [hcos1_mul, hcos3_ub', hrem_sq', hcn_nn, ht3_nn]
  have hmain_pi' : (chartPhiV w_m b).re ≤ (chartPhiV s b).re - (Real.pi ^ 2 / 36) * t_m ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hinner_neg' (by positivity [Real.pi_pos] : 0 ≤ Real.pi ^ 2 / 6)
    linarith only [hsr, hmul]
  have h20 : 20 * Real.pi ^ 2 * ρ ^ 3 ≤ (Real.pi ^ 2 / 36) * t_m ^ 3 := by
    have h1 : 20 * Real.pi ^ 2 * ρ ^ 3 ≤ (Real.pi ^ 2 / 36) * (729 * ρ ^ 3) := by
      have hpi2 := sq_nonneg Real.pi; have hr3 := pow_nonneg hρ_pos.le 3; nlinarith only [hpi2, hr3]
    exact h1.trans (mul_le_mul_of_nonneg_left hcube_lb (by positivity [Real.pi_pos]))
  linarith only [hmain_pi', h20]

private lemma zp_lower_rayA_bd {C_F δ ρ c_neg c_γ v φ' : ℝ} {s dir_mA b : ℂ}
    (hCF_nn : 0 ≤ C_F) (hCF_delta_cneg : C_F * δ ≤ c_neg / (16 * 44))
    (hc_neg_pos : 0 < c_neg) (hc_neg_le_half : c_neg ≤ 1 / 2) (hc_neg_ub : c_neg ≤ -Real.cos (7 * Real.pi / 12))
    (hρ_nn : 0 ≤ ρ) (hρ_le_δ : ρ ≤ δ) (h11ρ_δ : 11 * ρ ≤ δ) (hcγ_le : c_γ ≤ (Real.pi ^ 2 / 6) * (c_neg / 2))
    (h_one_sixth : 1 / (6 : ℝ) ≤ (1 / 3 : ℝ) * (1 / √2))
    (hcos3_m : Real.cos (3 * (-(5 * Real.pi / 12))) = -(1 / √2))
    (hcos2_m : Real.cos (2 * (-(5 * Real.pi / 12)) + Real.pi / 2 - φ') ≤ Real.cos (7 * Real.pi / 12))
    (hv_nn : 0 ≤ v) (hv_ub : v ≤ 11 * ρ)
    (hsr : (chartPhiV (s + (v : ℂ) * dir_mA) b).re - (chartPhiV s b).re ≤ (Real.pi ^ 2 / 6) *
      (ρ * v ^ 2 * Real.cos (2 * (-(5 * Real.pi / 12)) + Real.pi / 2 - φ') +
       (1 / 3 : ℝ) * v ^ 3 * Real.cos (3 * (-(5 * Real.pi / 12))) +
       2 * C_F * v ^ 2 * (ρ + v) ^ 2)) :
    (chartPhiV (s + (v : ℂ) * dir_mA) b).re ≤ (chartPhiV s b).re - c_γ * ρ * v ^ 2 := by
  have hsq_split : (ρ + v) ^ 2 ≤ 2 * ρ ^ 2 + 2 * v ^ 2 := by
    have hsq : 0 ≤ (ρ - v) ^ 2 := sq_nonneg (ρ - v)
    linarith only [hsq]
  have hCF_r : 4 * C_F * ρ ≤ c_neg / 2 := by
    have h4 : 4 * C_F * ρ ≤ 4 * C_F * δ := mul_le_mul_of_nonneg_left hρ_le_δ (by positivity)
    linarith only [h4, hCF_delta_cneg, hc_neg_pos]
  have hCF_v : 4 * C_F * v ≤ 1 / 12 := by
    have hv_del : v ≤ δ := by linarith only [hv_ub, h11ρ_δ]
    have h4 : 4 * C_F * v ≤ 4 * C_F * δ := mul_le_mul_of_nonneg_left hv_del (by positivity)
    linarith only [h4, hCF_delta_cneg, hc_neg_le_half]
  have hrem_sq : 2 * C_F * v ^ 2 * (ρ + v) ^ 2 ≤ (c_neg / 2) * ρ * v ^ 2 + (1 / 12 : ℝ) * v ^ 3 := by
    have hv2_nn : 0 ≤ v ^ 2 := sq_nonneg v
    have hv3_nn : 0 ≤ v ^ 3 := pow_nonneg hv_nn 3
    calc 2 * C_F * v ^ 2 * (ρ + v) ^ 2
        ≤ 2 * C_F * v ^ 2 * (2 * ρ ^ 2 + 2 * v ^ 2) := mul_le_mul_of_nonneg_left hsq_split (by positivity)
      _ = (4 * C_F * ρ) * (ρ * v ^ 2) + (4 * C_F * v) * v ^ 3 := by ring
      _ ≤ (c_neg / 2) * (ρ * v ^ 2) + (1 / 12 : ℝ) * v ^ 3 :=
          add_le_add (mul_le_mul_of_nonneg_right hCF_r (mul_nonneg hρ_nn hv2_nn))
            (mul_le_mul_of_nonneg_right hCF_v hv3_nn)
      _ = (c_neg / 2) * ρ * v ^ 2 + (1 / 12 : ℝ) * v ^ 3 := by ring
  have hcos_neg_le : Real.cos (2 * (-(5 * Real.pi / 12)) + Real.pi / 2 - φ') ≤ -c_neg := by
    linarith only [hcos2_m, hc_neg_ub]
  have hcos1_mul : ρ * v ^ 2 * Real.cos (2 * (-(5 * Real.pi / 12)) + Real.pi / 2 - φ') ≤ -c_neg * ρ * v ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hcos_neg_le (mul_nonneg hρ_nn (sq_nonneg v))
    linarith only [hmul]
  have hcos3_ub : (1 / 3 : ℝ) * v ^ 3 * Real.cos (3 * (-(5 * Real.pi / 12))) ≤ -(1 / 6) * v ^ 3 := by
    rw [hcos3_m]
    have hv3 : 0 ≤ v ^ 3 := pow_nonneg hv_nn 3
    have h1 := mul_le_mul_of_nonneg_right h_one_sixth hv3
    linarith only [h1]
  have hinner_neg : ρ * v ^ 2 * Real.cos (2 * (-(5 * Real.pi / 12)) + Real.pi / 2 - φ') +
      (1 / 3 : ℝ) * v ^ 3 * Real.cos (3 * (-(5 * Real.pi / 12))) + 2 * C_F * v ^ 2 * (ρ + v) ^ 2 ≤
      -(c_neg / 2) * ρ * v ^ 2 - (1 / 12 : ℝ) * v ^ 3 := by
    linarith only [hcos1_mul, hcos3_ub, hrem_sq]
  have hmul := mul_le_mul_of_nonneg_left hinner_neg (by positivity [Real.pi_pos] : 0 ≤ Real.pi ^ 2 / 6)
  have hv3_nn : 0 ≤ (Real.pi ^ 2 / 6) * (1 / 12 : ℝ) * v ^ 3 :=
    mul_nonneg (mul_nonneg (by positivity [Real.pi_pos]) (by norm_num)) (pow_nonneg hv_nn 3)
  have hc_mul : c_γ * ρ * v ^ 2 ≤ (Real.pi ^ 2 / 6) * (c_neg / 2) * ρ * v ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcγ_le hρ_nn) (sq_nonneg v)
  linarith only [hsr, hmul, hv3_nn, hc_mul]

private lemma zp_lower_ray_arcA {η : ℂ → ℂ → ℂ} {ρ_F C_F : ℝ}
    (hCF_nn : 0 ≤ C_F)
    (hη_an : AnalyticOnNhd ℂ (Function.uncurry η) (ball (0 : ℂ × ℂ) ρ_F))
    (hF_id : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      2 * Complex.log (chartB w / chartB s) * deriv chartOmega w =
        ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (w ^ 2 - s ^ 2) * (1 + η w s))
    (hη_bd : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      ‖η w s‖ ≤ C_F * (‖w‖ + ‖s‖))
    (_hρF_pos : 0 < ρ_F)
    {δ ρ₀ ρ φ' c_neg c_γ κ_arc : ℝ}
    (_hδ_pos : 0 < δ) (hδ_14 : δ ≤ 1 / 4) (hδ_rhoF : δ < min ρ_F (1 / 2))
    (hCF_delta : C_F * δ ≤ 1 / 80) (hCF_delta_cneg : C_F * δ ≤ c_neg / (16 * 44))
    (hc_neg_pos : 0 < c_neg) (hc_neg_le_half : c_neg ≤ 1 / 2)
    (hc_neg_ub : c_neg ≤ -Real.cos (7 * Real.pi / 12))
    (hρ₀_pos : 0 < ρ₀) (hρ₀_delta : 12 * ρ₀ ≤ δ) (hρ₀_arc : 4000 * C_F * ρ₀ ≤ 1)
    (hρ_nn : 0 ≤ ρ) (hρ_le : ρ ≤ ρ₀) (hφ_ge : Real.pi / 4 ≤ φ') (hφ_le : φ' ≤ Real.pi / 2)
    (hcγ_le : c_γ ≤ (Real.pi ^ 2 / 6) * (c_neg / 2)) (hκ_arc_eq : κ_arc = 10 * Real.pi ^ 2)
    {s b : ℂ}
    (hs_eq : s = (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 - φ' : ℝ) : ℂ)))
    (hb_eq : b = chartB s) (hb_re_pos : 0 < b.re) :
    let dir_mA : ℂ := Complex.exp (Complex.I * ((-(5 * Real.pi / 12) : ℝ) : ℂ))
    ∃ (t_m θ_m : ℝ),
      t_m ∈ Icc (9 * ρ) (11 * ρ) ∧ θ_m ∈ Icc (-(Real.pi / 2)) 0 ∧
      s + (t_m : ℂ) * dir_mA = ((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (θ_m : ℂ)) ∧
      (∀ v ∈ Icc (0 : ℝ) t_m,
        (chartPhiV (s + (v : ℂ) * dir_mA) b).re ≤ (chartPhiV s b).re - c_γ * ρ * v ^ 2) ∧
      (∀ α ∈ uIcc θ_m (-(Real.pi / 3)),
        (chartPhiV (((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (α : ℂ))) b).re ≤
          (chartPhiV s b).re - κ_arc * ρ ^ 3) := by
  intro dir_mA
  have hs_norm : ‖s‖ = ρ := by
    rw [hs_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ_nn, exp_ofReal_mul_I_norm', mul_one]
  have hs_re_nn : 0 ≤ s.re := by
    rw [hs_eq, Complex.re_ofReal_mul, exp_ofReal_mul_I_re'']
    exact mul_nonneg hρ_nn (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩)
  have h11ρ_δ : 11 * ρ ≤ δ := by linarith only [hρ_nn, hρ_le, hρ₀_delta]
  have hs_F : s ∈ ball (0 : ℂ) ρ_F := by
    rw [mem_ball_zero_iff, hs_norm]
    exact lt_trans (by linarith only [hρ_le, hρ₀_delta, hρ₀_pos] : ρ < δ) (lt_of_lt_of_le hδ_rhoF (min_le_left _ _))
  have h_inv_sq2 : 1 / √2 = √2 / 2 := by
    have hsq2 : √2 ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
    rw [div_eq_div_iff hsq2 two_ne_zero]; ring_nf; rw [Real.sq_sqrt (by norm_num)]
  have h_one_sixth : 1 / (6 : ℝ) ≤ (1 / 3 : ℝ) * (1 / √2) := by
    have hsq2_lt : √2 < 2 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [one_div_mul_one_div, one_div_le_one_div (by norm_num) (by positivity)]; linarith only [hsq2_lt]
  have hdirA_re : dir_mA.re = Real.cos (5 * Real.pi / 12) := by
    dsimp [dir_mA]; rw [exp_ofReal_mul_I_re'', Real.cos_neg]
  have hdirA_im : dir_mA.im = -Real.sin (5 * Real.pi / 12) := by
    dsimp [dir_mA]; rw [exp_ofReal_mul_I_im'', Real.sin_neg]
  have hdirA_norm : ‖dir_mA‖ = 1 := exp_ofReal_mul_I_norm' _
  have hdirA_re_pos : 0 < dir_mA.re := by
    rw [hdirA_re]; exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsin512 : √2 / 2 ≤ Real.sin (5 * Real.pi / 12) := by
    rw [← Real.cos_pi_div_four, ← Real.cos_pi_div_two_sub]
    have h1 : Real.pi / 2 - 5 * Real.pi / 12 ∈ Icc 0 Real.pi := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have h2 : Real.pi / 4 ∈ Icc 0 Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩
    exact Real.strictAntiOn_cos.antitoneOn h1 h2 (by linarith [Real.pi_pos])
  rcases eq_or_lt_of_le hρ_nn with rfl | hρ_pos
  · refine ⟨0, -(Real.pi / 3), by simp, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, ?_, ?_, ?_⟩
    · have hs0 : s = 0 := by simp [hs_eq]
      simp [hs0]
    · intro v hv; have hv0 : v = 0 := le_antisymm hv.2 hv.1; subst hv0; simp
    · intro α _
      have hs0 : s = 0 := by simp [hs_eq]
      simp [hs0]
  · obtain ⟨t_m, ht_mem, hnorm_eq⟩ := exists_ray_circle_hit hρ_pos (A₀ := 10) (by norm_num) hs_norm hdirA_norm
    have ht_range : t_m ∈ Icc (9 * ρ) (11 * ρ) := by
      simpa [show (10 - 1 : ℝ) = 9 by norm_num, show (10 + 1 : ℝ) = 11 by norm_num] using ht_mem
    let w_m := s + (t_m : ℂ) * dir_mA
    have hw_re_pos : 0 < w_m.re := by
      simp only [w_m, Complex.add_re, Complex.re_ofReal_mul]
      have : 0 < t_m := by linarith [ht_range.1, hρ_pos]
      nlinarith only [hs_re_nn, hdirA_re_pos, this]
    have hw_im_neg : w_m.im < 0 := by
      simp only [w_m, Complex.add_im, Complex.im_ofReal_mul, hdirA_im]
      have hs_im_ub : s.im ≤ ρ := (le_abs_self s.im).trans ((Complex.abs_im_le_norm s).trans (by rw [hs_norm]))
      have hsq2_gt : 1 < √2 := by
        rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have hsin_pos : 0 < Real.sin (5 * Real.pi / 12) := lt_of_lt_of_le (by positivity) hsin512
      nlinarith only [hs_im_ub, ht_range.1, hρ_pos, hsin512, hsq2_gt, hsin_pos]
    have harg_mem := arg_in_fourth_quad hw_re_pos hw_im_neg
    let θ_m := w_m.arg
    have hw_polar : w_m = ((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (θ_m : ℂ)) := by
      have h := Complex.norm_mul_exp_arg_mul_I w_m
      rw [hnorm_eq] at h
      rw [← h, mul_comm Complex.I (θ_m : ℂ)]
    have h_ray_strip : ∀ v ∈ Icc (0 : ℝ) t_m,
        s + (v : ℂ) * dir_mA ∈ ball (0 : ℂ) ρ_F ∧
        0 ≤ (s + (v : ℂ) * dir_mA).re ∧ (s + (v : ℂ) * dir_mA).re ≤ 1 / 4 := fun v hv => by
      have hvn : ‖s + (v : ℂ) * dir_mA‖ ≤ 12 * ρ := by
        calc ‖s + (v : ℂ) * dir_mA‖ ≤ ‖s‖ + ‖(v : ℂ) * dir_mA‖ := norm_add_le _ _
          _ = ρ + v := by rw [hs_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hv.1, hdirA_norm, mul_one]
          _ ≤ 12 * ρ := by linarith [hv.2, ht_range.2]
      have hltF : ‖s + (v : ℂ) * dir_mA‖ < ρ_F :=
        (hvn.trans (mul_le_mul_of_nonneg_left hρ_le (by norm_num))).trans_lt (hρ₀_delta.trans_lt (hδ_rhoF.trans_le (min_le_left _ _)))
      have hre0 : 0 ≤ (s + (v : ℂ) * dir_mA).re := by
        rw [Complex.add_re, Complex.re_ofReal_mul]; nlinarith only [hs_re_nn, hv.1, hdirA_re_pos]
      have hre14 : (s + (v : ℂ) * dir_mA).re ≤ 1 / 4 :=
        (Complex.re_le_norm _).trans (hvn.trans ((mul_le_mul_of_nonneg_left hρ_le (by norm_num)).trans (hρ₀_delta.trans hδ_14)))
      exact ⟨mem_ball_zero_iff.mpr hltF, hre0, hre14⟩
    have hcos3_m : Real.cos (3 * (-(5 * Real.pi / 12))) = -(1 / √2) := by
      rw [show 3 * (-(5 * Real.pi / 12)) = -(5 * Real.pi / 4) by ring, Real.cos_neg,
        show 5 * Real.pi / 4 = Real.pi / 4 + Real.pi by ring, Real.cos_add_pi,
        Real.cos_pi_div_four, h_inv_sq2]
    have hcos2_m := (lower_ray_ge_pi4_cos_le hφ_ge hφ_le).1
    have h_ray_bd : ∀ v ∈ Icc (0 : ℝ) t_m,
        (chartPhiV (s + (v : ℂ) * dir_mA) b).re ≤ (chartPhiV s b).re - c_γ * ρ * v ^ 2 := fun v hv =>
      zp_lower_rayA_bd hCF_nn hCF_delta_cneg hc_neg_pos hc_neg_le_half hc_neg_ub hρ_nn
        (by linarith only [hρ_le, hρ₀_delta, hρ₀_pos]) h11ρ_δ hcγ_le h_one_sixth hcos3_m hcos2_m
        hv.1 (hv.2.trans ht_range.2)
        (saddle_ray_H_le hCF_nn hη_an hF_id hη_bd hρ_nn (by linarith only [ht_range.1, hρ_pos])
          s b hs_eq hb_re_pos hb_eq hs_F h_ray_strip v hv)
    have hw_gain : (chartPhiV w_m b).re ≤ (chartPhiV s b).re - 20 * Real.pi ^ 2 * ρ ^ 3 :=
      zp_lower_arcA_gain hCF_nn hCF_delta hCF_delta_cneg hc_neg_pos hc_neg_ub hρ_pos
        (by linarith only [hρ_le, hρ₀_delta, hρ₀_pos]) ht_range h11ρ_δ h_inv_sq2 hcos3_m hcos2_m
        (saddle_ray_H_le hCF_nn hη_an hF_id hη_bd hρ_nn (by linarith only [ht_range.1, hρ_pos])
          s b hs_eq hb_re_pos hb_eq hs_F h_ray_strip t_m ⟨by linarith only [ht_range.1, hρ_pos], le_rfl⟩)
    refine ⟨t_m, θ_m, ht_range, ⟨harg_mem.1.le, harg_mem.2.le⟩, hw_polar, h_ray_bd, ?_⟩
    intro α hα
    have harc_mem : ∀ β ∈ uIcc θ_m (-(Real.pi / 3)),
        let w := ((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (β : ℂ))
        0 ≤ w.re ∧ w.re ≤ 1 / 4 := fun β hβ => by
      dsimp
      have hβ_mem : β ∈ Icc (-(Real.pi / 2)) 0 := by
        rw [Set.mem_uIcc] at hβ
        rcases hβ with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨harg_mem.1.le.trans h1, h2.trans (by linarith only [Real.pi_pos])⟩
        · exact ⟨(by linarith only [Real.pi_pos] : -(Real.pi / 2) ≤ -(Real.pi / 3)).trans h1, h2.trans harg_mem.2.le⟩
      rw [Complex.re_ofReal_mul, exp_ofReal_mul_I_re'']
      refine ⟨mul_nonneg (by positivity) (Real.cos_nonneg_of_mem_Icc ⟨hβ_mem.1, by linarith only [hβ_mem.2, Real.pi_pos]⟩), ?_⟩
      calc 10 * ρ * Real.cos β ≤ 10 * ρ * 1 :=
            mul_le_mul_of_nonneg_left (Real.cos_le_one β) (by positivity)
        _ ≤ 10 * ρ₀ := by linarith only [hρ_le]
        _ ≤ 1 / 4 := by linarith only [hρ₀_delta, hδ_14]
    have harc_step := arc_H_step_le hCF_nn hη_an hF_id hη_bd hb_re_pos hb_eq hs_F
      (r := 10 * ρ) (θ₀ := θ_m) (θ₁ := -(Real.pi / 3)) (by positivity)
      (by calc 10 * ρ ≤ 10 * ρ₀ := by linarith only [hρ_le]
        _ < δ := by linarith only [hρ₀_delta, hρ₀_pos]
        _ < ρ_F := hδ_rhoF.trans_le (min_le_left _ _))
      (by rw [hs_norm]; linarith only [hρ_pos])
      (by rw [abs_le]; constructor <;> linarith only [harg_mem.1, harg_mem.2, Real.pi_pos])
      harc_mem (fun β hβ => cos_three_le_of_lower_arc harg_mem.1.le harg_mem.2.le hβ)
    have hstep_bd : (Real.pi ^ 2 / 6) * (Real.pi / 2) * (10 * ρ) * (‖s‖ ^ 2 + 4 * C_F * (10 * ρ) ^ 3) ≤
        7 * Real.pi ^ 2 * ρ ^ 3 := by
      rw [hs_norm]
      have hcf4 : 4 * C_F * (10 * ρ) ^ 3 ≤ ρ ^ 2 := by
        have h4000 : 4000 * C_F * ρ ≤ 1 := by
          calc 4000 * C_F * ρ ≤ 4000 * C_F * ρ₀ :=
                mul_le_mul_of_nonneg_left hρ_le (by positivity)
            _ ≤ 1 := hρ₀_arc
        calc 4 * C_F * (10 * ρ) ^ 3 = (4000 * C_F * ρ) * ρ ^ 2 := by ring
          _ ≤ 1 * ρ ^ 2 := mul_le_mul_of_nonneg_right h4000 (sq_nonneg ρ)
          _ = ρ ^ 2 := one_mul _
      have hsum : ρ ^ 2 + 4 * C_F * (10 * ρ) ^ 3 ≤ 2 * ρ ^ 2 := by
        rw [two_mul]; exact add_le_add_right hcf4 _
      have h1 : (Real.pi ^ 2 / 6) * (Real.pi / 2) * (10 * ρ) * (ρ ^ 2 + 4 * C_F * (10 * ρ) ^ 3) ≤
          (Real.pi ^ 2 / 6) * (Real.pi / 2) * (10 * ρ) * (2 * ρ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      have h2 : (Real.pi ^ 2 / 6) * (Real.pi / 2) * (10 * ρ) * (2 * ρ ^ 2) =
          (5 * Real.pi / 3) * Real.pi ^ 2 * ρ ^ 3 := by ring
      have hpi4 : 5 * Real.pi / 3 ≤ 7 := by linarith only [Real.pi_lt_four]
      exact h1.trans (h2.symm ▸ mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpi4 (sq_nonneg Real.pi)) (pow_nonneg hρ_pos.le 3))
    have hw0_eq : ((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (θ_m : ℂ)) = w_m := hw_polar.symm
    rw [hw0_eq] at harc_step
    have hα_step := harc_step α hα
    rw [hκ_arc_eq]
    have h13 : 10 * Real.pi ^ 2 * ρ ^ 3 ≤ 13 * Real.pi ^ 2 * ρ ^ 3 := by
      have hpi2 := sq_nonneg Real.pi; have hr3 := pow_nonneg hρ_pos.le 3; nlinarith only [hpi2, hr3]
    linarith only [hα_step, hstep_bd, hw_gain, h13]

private lemma j10GammaPlus_seg_0 (δ T₀ t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    j10GammaPlus δ T₀ t =
      j10P δ + (t : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I) - j10P δ) := by
  simp only [j10GammaPlus, ht.2, ↓reduceIte]
  push_cast; ring

private lemma j10GammaPlus_seg_1 (δ T₀ t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    j10GammaPlus δ T₀ (1 + t) =
      (j10YDelta δ : ℂ) * (1 + Complex.I) +
        (t : ℂ) * ((1 / 2 : ℂ) * (1 + Complex.I) - (j10YDelta δ : ℂ) * (1 + Complex.I)) := by
  by_cases ht0 : t = 0
  · subst ht0
    simp only [j10GammaPlus, add_zero, le_rfl, ↓reduceIte, sub_self, zero_mul, zero_add,
      Complex.ofReal_zero, Complex.ofReal_one, one_mul]
  · have hgt1 : ¬ (1 + t ≤ 1) := by linarith only [lt_of_le_of_ne ht.1 (Ne.symm ht0)]
    have hle2 : 1 + t ≤ 2 := by linarith only [ht.2]
    simp only [j10GammaPlus, hgt1, hle2, ↓reduceIte]
    push_cast; ring

private lemma j10GammaPlus_seg_2 (δ T₀ t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    j10GammaPlus δ T₀ (2 + t) =
      (1 / 2 : ℂ) * (1 + Complex.I) +
        (t : ℂ) * ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ) - (1 / 2 : ℂ) * (1 + Complex.I)) := by
  by_cases ht0 : t = 0
  · subst ht0
    simp only [j10GammaPlus, add_zero, show ¬((2 : ℝ) ≤ 1) by norm_num,
      show (2 : ℝ) ≤ 2 by norm_num, ↓reduceIte, sub_self, zero_mul, zero_add,
      Complex.ofReal_zero]
    push_cast; norm_num
  · have hgt2 : ¬ (2 + t ≤ 2) := by linarith only [lt_of_le_of_ne ht.1 (Ne.symm ht0)]
    have hgt1 : ¬ (2 + t ≤ 1) := by linarith only [ht.1]
    simp only [j10GammaPlus, hgt1, hgt2, ↓reduceIte]
    push_cast; ring

private lemma j10GammaMinus_seg_0 (δ T₀ t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    j10GammaMinus δ T₀ t =
      starRingEnd ℂ (j10P δ) +
        (t : ℂ) * (starRingEnd ℂ ((j10YDelta δ : ℂ) * (1 + Complex.I)) - starRingEnd ℂ (j10P δ)) := by
  rw [j10GammaMinus, j10GammaPlus_seg_0 δ T₀ t ht, map_add, map_mul, map_sub, Complex.conj_ofReal]

private lemma j10GammaMinus_seg_1 (δ T₀ t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    j10GammaMinus δ T₀ (1 + t) =
      starRingEnd ℂ ((j10YDelta δ : ℂ) * (1 + Complex.I)) +
        (t : ℂ) * (starRingEnd ℂ ((1 / 2 : ℂ) * (1 + Complex.I)) -
          starRingEnd ℂ ((j10YDelta δ : ℂ) * (1 + Complex.I))) := by
  simp only [j10GammaMinus, j10GammaPlus_seg_1 δ T₀ t ht, map_add, map_mul, map_sub, Complex.conj_ofReal]

private lemma j10GammaMinus_seg_2 (δ T₀ t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    j10GammaMinus δ T₀ (2 + t) =
      starRingEnd ℂ ((1 / 2 : ℂ) * (1 + Complex.I)) +
        (t : ℂ) * (starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ)) -
          starRingEnd ℂ ((1 / 2 : ℂ) * (1 + Complex.I))) := by
  simp only [j10GammaMinus, j10GammaPlus_seg_2 δ T₀ t ht, map_add, map_mul, map_sub, Complex.conj_ofReal]

private lemma zp_j10_dn_dz {δ T₀ : ℝ} (hδ_pos : 0 < δ) (hδ_14 : δ ≤ 1 / 4) (hT₀_ge4 : 4 ≤ T₀) :
    let P₀ : ℂ := j10P δ
    let P₁ : ℂ := (j10YDelta δ : ℂ) * (1 + Complex.I)
    let P₂ : ℂ := (1 / 2 : ℂ) * (1 + Complex.I)
    let P₃ : ℂ := (1 / 2 : ℂ) + Complex.I * (T₀ : ℂ)
    ‖P₁ - P₀‖ ≤ T₀ + 2 ∧ ‖P₂ - P₁‖ ≤ T₀ + 2 ∧ ‖P₃ - P₂‖ ≤ T₀ + 2 ∧
      |P₀.im| ≤ T₀ ∧ |P₁.im| ≤ T₀ ∧ |P₂.im| ≤ T₀ ∧ |P₃.im| ≤ T₀ := by
  intro P₀ P₁ P₂ P₃
  have hsq3 : √3 ≤ 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]; exact Real.sqrt_le_sqrt (by norm_num)
  have hyd_ub : j10YDelta δ ≤ δ := by
    unfold j10YDelta; nlinarith only [hsq3, hδ_pos]
  have hyd_nn : 0 ≤ j10YDelta δ := by unfold j10YDelta; positivity
  have hP0_n : ‖P₀‖ = δ := by
    dsimp [P₀, j10P]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ_pos.le, exp_ofReal_mul_I_norm', mul_one]
  have hnorm1I : ‖(1 : ℂ) + Complex.I‖ ≤ 2 := by
    calc ‖(1 : ℂ) + Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
      _ = 2 := by simp; norm_num
  have hP1_n : ‖P₁‖ ≤ 2 * δ := by
    dsimp [P₁]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hyd_nn]
    exact (mul_le_mul hyd_ub hnorm1I (norm_nonneg _) hδ_pos.le).trans (by ring_nf; rfl)
  have hP10 : ‖P₁ - P₀‖ ≤ T₀ + 2 := by
    calc ‖P₁ - P₀‖ ≤ ‖P₁‖ + ‖P₀‖ := norm_sub_le _ _
      _ ≤ 2 * δ + δ := add_le_add hP1_n hP0_n.le
      _ ≤ T₀ + 2 := by linarith only [hδ_14, hT₀_ge4]
  have hP21 : ‖P₂ - P₁‖ ≤ T₀ + 2 := by
    have hP12 : P₂ - P₁ = ((1 / 2 - j10YDelta δ : ℝ) : ℂ) * (1 + Complex.I) := by
      dsimp [P₁, P₂]; push_cast; ring
    have hyd : |1 / 2 - j10YDelta δ| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith only [hyd_nn, hyd_ub, hδ_14]
    rw [hP12, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |1 / 2 - j10YDelta δ| * ‖(1 : ℂ) + Complex.I‖ ≤ (1 / 2) * 2 :=
          mul_le_mul hyd hnorm1I (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
      _ ≤ T₀ + 2 := by linarith only [hT₀_ge4]
  have hP32 : ‖P₃ - P₂‖ ≤ T₀ + 2 := by
    have hP32_eq : P₃ - P₂ = Complex.I * ((T₀ - 1 / 2 : ℝ) : ℂ) := by
      dsimp [P₂, P₃]; push_cast; ring
    rw [hP32_eq, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (by linarith only [hT₀_ge4])]
    linarith only [hT₀_ge4]
  have hP0_im : |P₀.im| ≤ T₀ :=
    (Complex.abs_im_le_norm P₀).trans (by rw [hP0_n]; linarith only [hδ_14, hT₀_ge4])
  have hP1_im : |P₁.im| ≤ T₀ := by
    have heq : P₁.im = j10YDelta δ := by simp [P₁]
    rw [heq, abs_of_nonneg hyd_nn]; linarith only [hyd_ub, hδ_14, hT₀_ge4]
  have hP2_im : |P₂.im| ≤ T₀ := by
    have heq : P₂.im = 1 / 2 := by simp [P₂]
    rw [heq, abs_of_nonneg (by norm_num)]; linarith only [hT₀_ge4]
  have hP3_im : |P₃.im| ≤ T₀ := by
    have heq : P₃.im = T₀ := by simp [P₃]
    rw [heq, abs_of_nonneg (by linarith only [hT₀_ge4])]
  exact ⟨hP10, hP21, hP32, hP0_im, hP1_im, hP2_im, hP3_im⟩

private lemma zp_affine_im_bd {A B : ℂ} {T₀ t : ℝ}
    (_hT₀ : 0 ≤ T₀) (hA : |A.im| ≤ T₀) (hB : |B.im| ≤ T₀) (ht : t ∈ Icc (0 : ℝ) 1) :
    |(A + (t : ℂ) * (B - A)).im| ≤ T₀ := by
  have heq : (A + (t : ℂ) * (B - A)).im = (1 - t) * A.im + t * B.im := by simp; ring
  rw [heq]
  calc |(1 - t) * A.im + t * B.im|
      ≤ (1 - t) * |A.im| + t * |B.im| := (abs_add_le _ _).trans
        (by rw [abs_mul, abs_mul, abs_of_nonneg (by linarith only [ht.2]), abs_of_nonneg ht.1])
    _ ≤ (1 - t) * T₀ + t * T₀ := by gcongr <;> linarith only [ht.1, ht.2]
    _ = T₀ := by ring

private lemma mem_convex_uIcc {a b t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t) * a + t * b ∈ uIcc a b := by
  rw [Set.mem_uIcc]
  rcases le_total a b with hle | hge
  · left; exact ⟨by nlinarith only [ht.1, ht.2, hle], by nlinarith only [ht.1, ht.2, hle]⟩
  · right; exact ⟨by nlinarith only [ht.1, ht.2, hge], by nlinarith only [ht.1, ht.2, hge]⟩

private lemma zp_lower_caseA
    {η : ℂ → ℂ → ℂ} {ρ_F C_F C_om C_om' c_J10 : ℝ}
    (hCF_nn : 0 ≤ C_F)
    (hη_an : AnalyticOnNhd ℂ (Function.uncurry η) (ball (0 : ℂ × ℂ) ρ_F))
    (hF_id : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      2 * Complex.log (chartB w / chartB s) * deriv chartOmega w =
        ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (w ^ 2 - s ^ 2) * (1 + η w s))
    (hη_bd : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      ‖η w s‖ ≤ C_F * (‖w‖ + ‖s‖))
    (hρF_pos : 0 < ρ_F)
    (hC_om_pos : 0 < C_om)
    (hC_om : ∀ ζ ∈ stripClosed, ‖chartOmega ζ‖ ≤ C_om * (1 + ζ.im ^ 2))
    (hC_om'_pos : 0 < C_om')
    (hC_om' : ∀ ζ ∈ stripClosed, ‖deriv chartOmega ζ‖ ≤ C_om' * (1 + |ζ.im|))
    {δ T₀ ε_J10 κ_strip c_neg c_γ κ_arc μ₀ c_Γ C_Γ C_d C_om_max C_om'_max ρ₀ ρ φ' : ℝ}
    (hδ_pos : 0 < δ) (hδ_14 : δ ≤ 1 / 4) (hδ_rhoF : δ < min ρ_F (1 / 2))
    (hCF_delta : C_F * δ ≤ 1 / 80) (hCF_delta_cneg : C_F * δ ≤ c_neg / (16 * 44))
    (hc_neg_pos : 0 < c_neg) (hc_neg_le_half : c_neg ≤ 1 / 2)
    (hc_neg_ub : c_neg ≤ -Real.cos (7 * Real.pi / 12))
    (hT₀_ge4 : 4 ≤ T₀) (hκ_strip_pos : 0 < κ_strip)
    (hρ₀_pos : 0 < ρ₀) (hρ₀_delta : 12 * ρ₀ ≤ δ) (hρ₀_arc : 4000 * C_F * ρ₀ ≤ 1)
    (hC_om_max_eq : C_om_max = C_om * (1 + T₀ ^ 2))
    (hC_om'_max_eq : C_om'_max = C_om' * (1 + T₀))
    (hCom'_max_nn : 0 ≤ C_om'_max)
    (hC_Γ_ge_om : C_om_max ≤ C_Γ) (hc_Γ_le_j10 : c_Γ ≤ c_J10)
    (hC_d_ge_om : C_om'_max * (T₀ + 2 + 2 * Real.pi) ≤ C_d)
    (hC_d_ge_T0 : T₀ + 2 * Real.pi + 2 ≤ C_d) (hT0_pi_gt1 : (1 : ℝ) ≤ T₀ + 2 * Real.pi + 2)
    (hCom_pi_le_Cd : (3 / 2 : ℝ) * C_om' * (2 * Real.pi) ≤ C_d)
    (hCom_le_Cd : (3 / 2 : ℝ) * C_om' ≤ C_d) (hκ_strip_j10 : -ε_J10 ≤ -4 * κ_strip)
    (hc_γ_pos : 0 < c_γ) (hcγ_le : c_γ ≤ (Real.pi ^ 2 / 6) * (c_neg / 2)) (hκ_arc_eq : κ_arc = 10 * Real.pi ^ 2)
    (hρ_nn : 0 ≤ ρ) (hρ_le : ρ ≤ ρ₀) (hφ_ge : Real.pi / 4 ≤ φ') (hφ_le : φ' ≤ Real.pi / 2)
    {s b : ℂ}
    (hs_eq : s = (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 - φ' : ℝ) : ℂ)))
    (hb_eq : b = chartB s) (hb_re_pos : 0 < b.re)
    (hradial_eta : C_F * (5 / 4 * δ) * (1 + 1 / 16) ≤ 1 / 4)
    (h_inner_om : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 / 2 → ‖w‖ ≤ δ →
      0 ≤ (chartOmega w).re ∧ c_Γ ≤ ‖chartOmega w‖ ∧ ‖chartOmega w‖ ≤ C_Γ ∧
        ‖deriv chartOmega w‖ ≤ (3 / 2 : ℝ) * C_om')
    (h_fixed_strip_H : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 / 2 → |ζ.im| ≤ T₀ →
      j10H ζ ≤ -4 * κ_strip →
      (chartPhiV ζ b).re ≤ (chartPhiV s b).re - κ_strip)
    (hJ10_pts : ∀ t ∈ Icc (0 : ℝ) 3,
      0 ≤ (j10GammaPlus δ T₀ t).re ∧ (j10GammaPlus δ T₀ t).re ≤ 1 / 2 ∧
        0 ≤ (j10GammaPlus δ T₀ t).im ∧
      0 ≤ (j10GammaMinus δ T₀ t).re ∧ (j10GammaMinus δ T₀ t).re ≤ 1 / 2 ∧
        (j10GammaMinus δ T₀ t).im ≤ 0 ∧
      j10H (j10GammaPlus δ T₀ t) ≤ j10H (j10P δ) ∧
      j10H (j10GammaPlus δ T₀ t) ≤ -ε_J10 ∧
      j10H (j10GammaMinus δ T₀ t) ≤ j10H (j10P δ) ∧
      j10H (j10GammaMinus δ T₀ t) ≤ -ε_J10 ∧
      0 ≤ (chartOmega (j10GammaPlus δ T₀ t)).re ∧
      0 ≤ (chartOmega (j10GammaMinus δ T₀ t)).re)
    (hJ10_om_lb : ∀ t ∈ Icc (0 : ℝ) 3,
      c_J10 ≤ ‖chartOmega (j10GammaPlus δ T₀ t)‖ ∧
      c_J10 ≤ ‖chartOmega (j10GammaMinus δ T₀ t)‖)
    {P₀ P₁ P₂ P₃ : ℂ}
    (hP0_def : P₀ = j10P δ) (hP1_def : P₁ = (j10YDelta δ : ℂ) * (1 + Complex.I))
    (hP2_def : P₂ = (1 / 2 : ℂ) * (1 + Complex.I))
    (hP3_def : P₃ = (1 / 2 : ℂ) + Complex.I * (T₀ : ℂ))
    (hP0m_re : 0 ≤ (starRingEnd ℂ P₀).re ∧ (starRingEnd ℂ P₀).re ≤ 1 / 2)
    (hP1m_re : 0 ≤ (starRingEnd ℂ P₁).re ∧ (starRingEnd ℂ P₁).re ≤ 1 / 2)
    (hP2m_re : 0 ≤ (starRingEnd ℂ P₂).re ∧ (starRingEnd ℂ P₂).re ≤ 1 / 2)
    (hP3m_re : 0 ≤ (starRingEnd ℂ P₃).re ∧ (starRingEnd ℂ P₃).re ≤ 1 / 2) :
    ∃ lower_segs : List ContourSeg,
      ContourChained (chartOmega s) (chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ))) lower_segs ∧
      lower_segs.length ≤ 6 ∧
      (∀ S ∈ lower_segs, S.b - S.a ≤ 1) ∧
      (∀ S ∈ lower_segs, ∀ t ∈ Icc S.a S.b,
        0 ≤ (S.ω t).re ∧ c_Γ ≤ ‖S.ω t‖ ∧ ‖S.ω t‖ ≤ C_Γ ∧ ‖S.ω' t‖ ≤ C_d) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → ∀ t ∈ Icc S.a S.b,
        ‖S.ζ' t‖ ≤ C_d ∧ (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → S.kind ≠ .upperRay) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → S.kind = .lowerRay →
        ∃ t_max ≥ (0 : ℝ), S.a = 0 ∧ S.b = t_max ∧ t_max ≤ 11 * ρ ∧
          ∀ t ∈ Icc 0 t_max, ‖S.ζ t - s‖ = t ∧ ‖S.ζ' t‖ = 1 ∧
            (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - c_γ * ρ * t ^ 2) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → S.kind = .arcRadial →
        ∀ t ∈ Icc S.a S.b, (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - κ_arc * ρ ^ 3) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → S.kind = .fixedStrip →
        ∀ t ∈ Icc S.a S.b, (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - κ_strip) ∧
      (∀ S ∈ lower_segs, S.isStrip = false →
        ∀ t ∈ Icc S.a S.b,
          μ₀ ≤ (S.ω t).re ∧ crudeExponentEc (S.ω t) b ≤ (chartPhiV s b).re - c_γ * ρ * s.re ^ 2) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → S.kind ≠ .crudeEdge) := by
  have hs_norm : ‖s‖ = ρ := by
    rw [hs_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ_nn, exp_ofReal_mul_I_norm', mul_one]
  have hs_re_nn : 0 ≤ s.re := by
    rw [hs_eq, Complex.re_ofReal_mul, exp_ofReal_mul_I_re'']
    exact mul_nonneg hρ_nn (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩)
  have h12ρ_δ : 12 * ρ ≤ δ := by linarith only [hρ_le, hρ₀_delta]
  have h11ρ_δ : 11 * ρ ≤ δ := by linarith only [hρ_nn, h12ρ_δ]
  have hs_F : s ∈ ball (0 : ℂ) ρ_F := by
    rw [mem_ball_zero_iff, hs_norm]
    exact lt_trans (by linarith only [hρ_le, hρ₀_delta, hρ₀_pos] : ρ < δ) (lt_of_lt_of_le hδ_rhoF (min_le_left _ _))
  obtain ⟨hP10, hP21, hP32, hP0_im, hP1_im, hP2_im, hP3_im⟩ :=
    zp_j10_dn_dz hδ_pos hδ_14 hT₀_ge4
  simp only [← hP0_def, ← hP1_def, ← hP2_def, ← hP3_def] at hP10 hP21 hP32 hP0_im hP1_im hP2_im hP3_im
  let seg_dn01 := mkStripAffineSeg .fixedStrip (starRingEnd ℂ P₀) (starRingEnd ℂ P₁) hP0m_re hP1m_re
  let seg_dn12 := mkStripAffineSeg .fixedStrip (starRingEnd ℂ P₁) (starRingEnd ℂ P₂) hP1m_re hP2m_re
  let seg_dn23 := mkStripAffineSeg .fixedStrip (starRingEnd ℂ P₂) (starRingEnd ℂ P₃) hP2m_re hP3m_re
  have hj10m_mem : ∀ S ∈ [seg_dn01, seg_dn12, seg_dn23], ∀ t ∈ Icc S.a S.b,
      ∃ u ∈ Icc (0 : ℝ) 3, S.ζ t = j10GammaMinus δ T₀ u := fun S hS t ht => by
    rcases List.mem_cons.mp hS with rfl | hS
    · have ht01 : 0 ≤ t ∧ t ≤ 1 := ht
      refine ⟨t, ⟨ht01.1, ht01.2.trans (by norm_num)⟩, ?_⟩
      change starRingEnd ℂ P₀ + (t : ℂ) * (starRingEnd ℂ P₁ - starRingEnd ℂ P₀) = j10GammaMinus δ T₀ t
      rw [j10GammaMinus_seg_0 δ T₀ t ht01, hP0_def, hP1_def]
    · rcases List.mem_cons.mp hS with rfl | hS
      · have ht01 : 0 ≤ t ∧ t ≤ 1 := ht
        refine ⟨1 + t, ⟨by linarith only [ht01.1], by linarith only [ht01.2]⟩, ?_⟩
        change starRingEnd ℂ P₁ + (t : ℂ) * (starRingEnd ℂ P₂ - starRingEnd ℂ P₁) =
          j10GammaMinus δ T₀ (1 + t)
        rw [j10GammaMinus_seg_1 δ T₀ t ht01, hP1_def, hP2_def]
      · rw [List.mem_singleton] at hS; subst hS
        have ht01 : 0 ≤ t ∧ t ≤ 1 := ht
        refine ⟨2 + t, ⟨by linarith only [ht01.1], by linarith only [ht01.2]⟩, ?_⟩
        change starRingEnd ℂ P₂ + (t : ℂ) * (starRingEnd ℂ P₃ - starRingEnd ℂ P₂) =
          j10GammaMinus δ T₀ (2 + t)
        rw [j10GammaMinus_seg_2 δ T₀ t ht01, hP2_def, hP3_def]
  have hj10m_strip : ∀ S ∈ [seg_dn01, seg_dn12, seg_dn23], S.isStrip = true := fun S hS => by
    rcases List.mem_cons.mp hS with rfl | hS; · rfl
    rcases List.mem_cons.mp hS with rfl | hS; · rfl
    rw [List.mem_singleton] at hS; subst hS; rfl
  have hj10m_im : ∀ S ∈ [seg_dn01, seg_dn12, seg_dn23], ∀ t ∈ Icc S.a S.b,
      |(S.ζ t).im| ≤ T₀ := fun S hS t ht => by
    have hT0_nn : (0 : ℝ) ≤ T₀ := by linarith only [hT₀_ge4]
    have hc_im : ∀ z : ℂ, |z.im| ≤ T₀ → |(starRingEnd ℂ z).im| ≤ T₀ := fun z hz => by
      simpa [Complex.conj_im] using hz
    rcases List.mem_cons.mp hS with rfl | hS
    · exact zp_affine_im_bd hT0_nn (hc_im _ hP0_im) (hc_im _ hP1_im) ht
    · rcases List.mem_cons.mp hS with rfl | hS
      · exact zp_affine_im_bd hT0_nn (hc_im _ hP1_im) (hc_im _ hP2_im) ht
      · rw [List.mem_singleton] at hS; subst hS
        exact zp_affine_im_bd hT0_nn (hc_im _ hP2_im) (hc_im _ hP3_im) ht
  have h_dn_dz : ∀ S ∈ [seg_dn01, seg_dn12, seg_dn23], ∀ t ∈ Icc S.a S.b,
      ‖S.ζ' t‖ ≤ T₀ + 2 := fun S hS _ _ => by
    rcases List.mem_cons.mp hS with rfl | hS
    · change ‖starRingEnd ℂ P₁ - starRingEnd ℂ P₀‖ ≤ T₀ + 2
      rw [← map_sub, Complex.norm_conj]; exact hP10
    · rcases List.mem_cons.mp hS with rfl | hS
      · change ‖starRingEnd ℂ P₂ - starRingEnd ℂ P₁‖ ≤ T₀ + 2
        rw [← map_sub, Complex.norm_conj]; exact hP21
      · rw [List.mem_singleton] at hS; subst hS
        change ‖starRingEnd ℂ P₃ - starRingEnd ℂ P₂‖ ≤ T₀ + 2
        rw [← map_sub, Complex.norm_conj]; exact hP32
  let dir_mA : ℂ := Complex.exp (Complex.I * ((-(5 * Real.pi / 12) : ℝ) : ℂ))
  have hdirA_re : dir_mA.re = Real.cos (5 * Real.pi / 12) := by
    dsimp [dir_mA]; rw [exp_ofReal_mul_I_re'', Real.cos_neg]
  have hdirA_norm : ‖dir_mA‖ = 1 := exp_ofReal_mul_I_norm' _
  have hdirA_re_pos : 0 < dir_mA.re := by
    rw [hdirA_re]; exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hex_minus := zp_lower_ray_arcA hCF_nn hη_an hF_id hη_bd hρF_pos hδ_pos hδ_14 hδ_rhoF hCF_delta
    hCF_delta_cneg hc_neg_pos hc_neg_le_half hc_neg_ub hρ₀_pos hρ₀_delta hρ₀_arc
    hρ_nn hρ_le hφ_ge hφ_le hcγ_le hκ_arc_eq hs_eq hb_eq hb_re_pos
  rcases hex_minus with ⟨t_m, θ_m, ht_m_mem, hθ_m_mem, hw_m_polar, h_dn_ray_bd, h_dn_arc_bd⟩
  have h_dn_ray_strip : ∀ v ∈ Icc (0 : ℝ) t_m,
      0 ≤ (s + (v : ℂ) * dir_mA).re ∧ (s + (v : ℂ) * dir_mA).re ≤ 1 / 2 := fun v hv => by
    have hvd : ((v : ℂ) * dir_mA).re = v * dir_mA.re := by rw [Complex.re_ofReal_mul]
    have hnorm_v : ‖s + (v : ℂ) * dir_mA‖ ≤ δ := by
      calc ‖s + (v : ℂ) * dir_mA‖ ≤ ‖s‖ + ‖(v : ℂ) * dir_mA‖ := norm_add_le _ _
        _ = ρ + v := by rw [hs_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hv.1, hdirA_norm, mul_one]
        _ ≤ 12 * ρ := by linarith only [hv.2, ht_m_mem.2]
        _ ≤ δ := h12ρ_δ
    exact ⟨by rw [Complex.add_re, hvd]; nlinarith only [hs_re_nn, hv.1, hdirA_re_pos],
      (Complex.re_le_norm _).trans (hnorm_v.trans (hδ_14.trans (by norm_num)))⟩
  have h_dn_arc_strip : ∀ α ∈ uIcc θ_m (-(Real.pi / 3)),
      0 ≤ (((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (α : ℂ))).re ∧
      (((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (α : ℂ))).re ≤ 1 / 2 := fun α hα => by
    have hα_mem : α ∈ Icc (-(Real.pi / 2)) 0 := by
      rw [Set.mem_uIcc] at hα
      rcases hα with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨hθ_m_mem.1.trans h1, h2.trans (by linarith only [Real.pi_pos])⟩
      · exact ⟨(by linarith only [Real.pi_pos] : -(Real.pi / 2) ≤ -(Real.pi / 3)).trans h1, h2.trans hθ_m_mem.2⟩
    rw [Complex.re_ofReal_mul, exp_ofReal_mul_I_re'']
    refine ⟨mul_nonneg (by positivity) (Real.cos_nonneg_of_mem_Icc ⟨hα_mem.1, by linarith only [hα_mem.2, Real.pi_pos]⟩), ?_⟩
    calc 10 * ρ * Real.cos α ≤ 10 * ρ * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one α) (by positivity)
      _ ≤ 12 * ρ₀ := by linarith only [hρ_nn, hρ_le]
      _ ≤ 1 / 2 := hρ₀_delta.trans (hδ_14.trans (by norm_num))
  let dir_plus : ℂ := Complex.exp (Complex.I * ((Real.pi / 3 : ℝ) : ℂ))
  let dir_minus : ℂ := Complex.exp (Complex.I * ((-(Real.pi / 3) : ℝ) : ℂ))
  have hdir_m_eq : dir_minus = starRingEnd ℂ dir_plus := by
    dsimp only [dir_minus, dir_plus]; rw [← Complex.exp_conj]; congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
  have hP0m_eq : starRingEnd ℂ P₀ = (δ : ℂ) * dir_minus := by
    rw [hP0_def, j10P, hdir_m_eq, map_mul, Complex.conj_ofReal]
  have hdir_m_re : dir_minus.re = 1 / 2 := by
    dsimp [dir_minus]; rw [exp_ofReal_mul_I_re'', Real.cos_neg, Real.cos_pi_div_three]
  have hrad_m_re : 0 ≤ (((10 * ρ : ℝ) : ℂ) * dir_minus).re ∧ (((10 * ρ : ℝ) : ℂ) * dir_minus).re ≤ 1 / 2 := by
    rw [Complex.re_ofReal_mul, hdir_m_re]
    exact ⟨by linarith only [hρ_nn], by nlinarith only [h12ρ_δ, hδ_14, hρ_nn]⟩
  let seg_dn_ray := mkStripRaySeg .lowerRay s dir_mA t_m (by linarith only [ht_m_mem.1, hρ_nn]) h_dn_ray_strip
  let seg_dn_arc := mkStripArcSeg (10 * ρ) θ_m (-(Real.pi / 3)) h_dn_arc_strip
  let seg_dn_rad := mkStripAffineSeg .arcRadial (((10 * ρ : ℝ) : ℂ) * dir_minus) (starRingEnd ℂ P₀) hrad_m_re hP0m_re
  have h_dn_rad_bd : ∀ t ∈ Icc (0 : ℝ) 1,
      (chartPhiV (seg_dn_rad.ζ t) b).re ≤ (chartPhiV s b).re - κ_arc * ρ ^ 3 := fun t ht => by
    let r_t : ℝ := (1 - t) * (10 * ρ) + t * δ
    have hζ_eq : seg_dn_rad.ζ t = (r_t : ℂ) * dir_minus := by
      dsimp [seg_dn_rad, mkStripAffineSeg, mkStripSeg, r_t]; rw [hP0m_eq]; push_cast; ring
    rw [hζ_eq]
    have h10ρ_δ : 10 * ρ ≤ δ := by linarith only [hρ_nn, h12ρ_δ]
    have hr_mem : r_t ∈ Icc (10 * ρ) δ :=
      ⟨by nlinarith only [ht.1, ht.2, h10ρ_δ], by nlinarith only [ht.1, ht.2, h10ρ_δ]⟩
    rcases eq_or_lt_of_le hρ_nn with rfl | hρ_pos
    · have hs0 : s = 0 := by simp [hs_eq]
      have hb0 : b = (xiStar : ℂ) := by rw [hb_eq, hs0, chartB_zero]
      rw [hs0, hb0]
      have hr0 : r_t ∈ Icc (0 : ℝ) δ := ⟨by nlinarith only [ht.1, ht.2, hδ_pos], hr_mem.2⟩
      have h0 := radial_H_le_zero_limit (δ := δ) hCF_nn hη_an hF_id hη_bd (Or.inr rfl) hδ_pos hδ_rhoF
        hradial_eta r_t hr0
      rw [show (-1 * Real.pi / 3 : ℝ) = -(Real.pi / 3) by ring] at h0
      simpa [dir_minus] using h0
    · have hanti := radial_H_antitone hCF_nn hη_an hF_id hη_bd hb_re_pos hb_eq hs_F
        (Or.inr rfl) (by positivity) h10ρ_δ hδ_rhoF
        (by rw [hs_norm]; linarith only [hρ_pos]) hradial_eta
      have hle_end := hanti ⟨le_rfl, h10ρ_δ⟩ hr_mem hr_mem.1
      have harc_end := h_dn_arc_bd (-(Real.pi / 3)) Set.right_mem_uIcc
      have heq1 : (((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * ((-1 * Real.pi / 3 : ℝ) : ℂ))) =
          ((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * ((-(Real.pi / 3) : ℝ) : ℂ)) := by
        congr 2; push_cast; ring
      have heq2 : (r_t : ℂ) * Complex.exp (Complex.I * ((-1 * Real.pi / 3 : ℝ) : ℂ)) = (r_t : ℂ) * dir_minus := by
        dsimp [dir_minus]; congr 2; push_cast; ring
      dsimp only at hle_end
      rw [heq2, heq1] at hle_end
      exact hle_end.trans harc_end
  let lower_segs := [seg_dn_ray, seg_dn_arc, seg_dn_rad, seg_dn01, seg_dn12, seg_dn23]
  have hchain_dn : ContourChained (chartOmega s)
      (chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ))) lower_segs := by
    have hw0 : seg_dn_ray.ω 0 = chartOmega s := by
      dsimp [seg_dn_ray, mkStripRaySeg, mkStripSeg]; simp
    have hw1 : seg_dn_arc.ω 0 = seg_dn_ray.ω seg_dn_ray.b := by
      dsimp [seg_dn_arc, mkStripArcSeg, seg_dn_ray, mkStripRaySeg, mkStripSeg]
      simp only [sub_zero, one_mul, zero_mul, add_zero]
      exact congrArg chartOmega hw_m_polar.symm
    have hw2 : seg_dn_rad.ω 0 = seg_dn_arc.ω 1 := by
      dsimp [seg_dn_rad, mkStripAffineSeg, seg_dn_arc, mkStripArcSeg, mkStripSeg, dir_minus]
      simp
    have hw3 : seg_dn01.ω 0 = seg_dn_rad.ω 1 := by
      dsimp [seg_dn01, seg_dn_rad, mkStripAffineSeg, mkStripSeg]; simp
    have hw4 : seg_dn12.ω 0 = seg_dn01.ω 1 := by
      dsimp [seg_dn12, seg_dn01, mkStripAffineSeg, mkStripSeg]; simp
    have hw5 : seg_dn23.ω 0 = seg_dn12.ω 1 := by
      dsimp [seg_dn23, seg_dn12, mkStripAffineSeg, mkStripSeg]; simp
    have hw6 : seg_dn23.ω 1 = chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)) := by
      dsimp [seg_dn23, mkStripAffineSeg, mkStripSeg]
      rw [hP3_def]; congr 1; apply Complex.ext <;> simp
    exact ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6⟩
  refine ⟨lower_segs, hchain_dn, by simp [lower_segs], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    rcases List.mem_cons.mp hS with rfl | hS
    · dsimp [seg_dn_ray, mkStripRaySeg, mkStripSeg]; linarith only [ht_m_mem.2, h12ρ_δ, hδ_14, hρ_nn]
    rcases List.mem_cons.mp hS with rfl | hS; · dsimp [seg_dn_arc, mkStripArcSeg, mkStripSeg]; norm_num
    rcases List.mem_cons.mp hS with rfl | hS; · dsimp [seg_dn_rad, mkStripAffineSeg, mkStripSeg]; norm_num
    rcases List.mem_cons.mp hS with rfl | hS; · dsimp [seg_dn01, mkStripAffineSeg, mkStripSeg]; norm_num
    rcases List.mem_cons.mp hS with rfl | hS; · dsimp [seg_dn12, mkStripAffineSeg, mkStripSeg]; norm_num
    rw [List.mem_singleton] at hS; subst hS; dsimp [seg_dn23, mkStripAffineSeg, mkStripSeg]; norm_num
  · intro S hS t ht
    rcases List.mem_cons.mp hS with rfl | hS
    · have hvn : ‖s + (t : ℂ) * dir_mA‖ ≤ δ := by
        dsimp [seg_dn_ray, mkStripRaySeg, mkStripSeg] at ht
        calc ‖s + (t : ℂ) * dir_mA‖ ≤ ‖s‖ + ‖(t : ℂ) * dir_mA‖ := norm_add_le _ _
          _ = ρ + t := by rw [hs_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1, hdirA_norm, mul_one]
          _ ≤ 12 * ρ := by linarith only [ht.2, ht_m_mem.2]
          _ ≤ δ := h12ρ_δ
      have him := h_inner_om _ (h_dn_ray_strip t ht).1 (h_dn_ray_strip t ht).2 hvn
      refine ⟨him.1, him.2.1, him.2.2.1, ?_⟩
      change ‖deriv chartOmega (seg_dn_ray.ζ t) * dir_mA‖ ≤ C_d
      rw [norm_mul, hdirA_norm, mul_one]
      exact him.2.2.2.trans hCom_le_Cd
    · rcases List.mem_cons.mp hS with rfl | hS
      · have hvn : ‖seg_dn_arc.ζ t‖ ≤ δ := by
          change ‖((10 * ρ : ℝ) : ℂ) * Complex.exp _‖ ≤ δ
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), exp_ofReal_mul_I_norm', mul_one]
          linarith only [hρ_le, hρ₀_delta, hρ₀_pos]
        have hstrip_t := seg_dn_arc.hζ_strip rfl t ht
        have him := h_inner_om _ hstrip_t.1 hstrip_t.2.1 hvn
        refine ⟨him.1, him.2.1, him.2.2.1, ?_⟩
        have hdz_bd : ‖seg_dn_arc.ζ' t‖ ≤ 2 * Real.pi := by
          change ‖Complex.I * (((-(Real.pi / 3) - θ_m : ℝ) : ℂ)) * _‖ ≤ 2 * Real.pi
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
            norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), exp_ofReal_mul_I_norm', mul_one]
          have habs_th : |-(Real.pi / 3) - θ_m| ≤ Real.pi / 2 := by
            rw [abs_le]; constructor <;> linarith only [hθ_m_mem.1, hθ_m_mem.2, Real.pi_pos]
          have h10rho : 10 * ρ ≤ 1 := by linarith only [hρ_le, hρ₀_delta, hδ_14, hρ₀_pos]
          calc |-(Real.pi / 3) - θ_m| * (10 * ρ) ≤ (Real.pi / 2) * 1 :=
                mul_le_mul habs_th h10rho (by positivity) (by positivity)
            _ ≤ 2 * Real.pi := by linarith only [Real.pi_pos]
        rw [hstrip_t.2.2.2.2.2, norm_mul]
        have h1 : ‖deriv chartOmega (seg_dn_arc.ζ t)‖ * ‖seg_dn_arc.ζ' t‖ ≤ (3 / 2 * C_om') * (2 * Real.pi) :=
          mul_le_mul him.2.2.2 hdz_bd (norm_nonneg _) (by positivity)
        exact h1.trans hCom_pi_le_Cd
      · rcases List.mem_cons.mp hS with rfl | hS
        · have hvn : ‖seg_dn_rad.ζ t‖ ≤ δ := by
            dsimp [seg_dn_rad, mkStripAffineSeg, mkStripSeg] at ht
            let r_t : ℝ := (1 - t) * (10 * ρ) + t * δ
            have hζ_eq : seg_dn_rad.ζ t = (r_t : ℂ) * dir_minus := by
              dsimp [seg_dn_rad, mkStripAffineSeg, mkStripSeg, r_t]; rw [hP0m_eq]; push_cast; ring
            rw [hζ_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by nlinarith only [ht.1, ht.2, hρ_nn, hδ_pos]),
              exp_ofReal_mul_I_norm', mul_one]
            nlinarith only [ht.1, ht.2, h12ρ_δ, hρ_nn]
          have hstrip_t := seg_dn_rad.hζ_strip rfl t ht
          have him := h_inner_om _ hstrip_t.1 hstrip_t.2.1 hvn
          refine ⟨him.1, him.2.1, him.2.2.1, ?_⟩
          have hdz_bd : ‖seg_dn_rad.ζ' t‖ ≤ 1 := by
            change ‖starRingEnd ℂ P₀ - ((10 * ρ : ℝ) : ℂ) * dir_minus‖ ≤ 1
            rw [hP0m_eq, show (δ : ℂ) * dir_minus - ((10 * ρ : ℝ) : ℂ) * dir_minus =
              ((δ - 10 * ρ : ℝ) : ℂ) * dir_minus by push_cast; ring,
              norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith only [h12ρ_δ, hρ_nn]),
              exp_ofReal_mul_I_norm', mul_one]
            linarith only [hδ_14, hρ_nn]
          rw [hstrip_t.2.2.2.2.2, norm_mul]
          have h1 : ‖deriv chartOmega (seg_dn_rad.ζ t)‖ * ‖seg_dn_rad.ζ' t‖ ≤ (3 / 2 * C_om') * 1 :=
            mul_le_mul him.2.2.2 hdz_bd (norm_nonneg _) (by positivity)
          exact (h1.trans_eq (mul_one _)).trans hCom_le_Cd
        · obtain ⟨u, hu, hζ_u⟩ := hj10m_mem S hS t ht
          have hpt := hJ10_pts u hu
          have hstrip_t := S.hζ_strip (hj10m_strip S hS) t ht
          have him_ub : |(S.ζ t).im| ≤ T₀ := hj10m_im S hS t ht
          have hcl : S.ζ t ∈ stripClosed := ⟨hstrip_t.1, hstrip_t.2.1.trans (by norm_num)⟩
          have hom_ub : ‖S.ω t‖ ≤ C_Γ := by
            rw [hstrip_t.2.2.1]
            calc ‖chartOmega (S.ζ t)‖ ≤ C_om * (1 + (S.ζ t).im ^ 2) := hC_om _ hcl
              _ ≤ C_om * (1 + T₀ ^ 2) :=
                  mul_le_mul_of_nonneg_left (add_le_add_right (by rw [← sq_abs (S.ζ t).im]; exact pow_le_pow_left₀ (abs_nonneg _) him_ub 2) 1) hC_om_pos.le
              _ = C_om_max := hC_om_max_eq.symm
              _ ≤ C_Γ := hC_Γ_ge_om
          have hom_lb : c_Γ ≤ ‖S.ω t‖ := by
            rw [hstrip_t.2.2.1, hζ_u]
            exact hc_Γ_le_j10.trans (hJ10_om_lb u hu).2
          have hom_deriv : ‖deriv chartOmega (S.ζ t)‖ ≤ C_om'_max := by
            rw [hC_om'_max_eq]
            exact (hC_om' _ hcl).trans (mul_le_mul_of_nonneg_left (add_le_add_right him_ub 1) hC_om'_pos.le)
          have hdz_ub := h_dn_dz S hS t ht
          have hω'_ub : ‖S.ω' t‖ ≤ C_d := by
            rw [hstrip_t.2.2.2.2.2, norm_mul]
            have h1 : ‖deriv chartOmega (S.ζ t)‖ * ‖S.ζ' t‖ ≤ C_om'_max * (T₀ + 2) :=
              mul_le_mul hom_deriv hdz_ub (norm_nonneg _) hCom'_max_nn
            have h2 : C_om'_max * (T₀ + 2) ≤ C_om'_max * (T₀ + 2 + 2 * Real.pi) :=
              mul_le_mul_of_nonneg_left (by linarith only [Real.pi_pos]) hCom'_max_nn
            exact h1.trans (h2.trans hC_d_ge_om)
          exact ⟨by rw [hstrip_t.2.2.1, hζ_u]; exact hpt.2.2.2.2.2.2.2.2.2.2.2, hom_lb, hom_ub, hω'_ub⟩
  · intro S hS _ t ht
    rcases List.mem_cons.mp hS with rfl | hS
    · refine ⟨?_, ?_⟩
      · change ‖dir_mA‖ ≤ C_d; rw [hdirA_norm]; exact hT0_pi_gt1.trans hC_d_ge_T0
      · exact (h_dn_ray_bd t ht).trans (sub_le_self _
          (mul_nonneg (mul_nonneg hc_γ_pos.le hρ_nn) (sq_nonneg t)))
    · have hκ_arc_pos : 0 < κ_arc := by rw [hκ_arc_eq]; positivity [Real.pi_pos]
      rcases List.mem_cons.mp hS with rfl | hS
      · refine ⟨?_, ?_⟩
        · change ‖Complex.I * (((-(Real.pi / 3) - θ_m : ℝ) : ℂ)) * _‖ ≤ C_d
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
            norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), exp_ofReal_mul_I_norm', mul_one]
          have habs_th : |-(Real.pi / 3) - θ_m| ≤ Real.pi / 2 := by
            rw [abs_le]; constructor <;> linarith only [hθ_m_mem.1, hθ_m_mem.2, Real.pi_pos]
          have h10rho : 10 * ρ ≤ 1 := by linarith only [hρ_le, hρ₀_delta, hδ_14, hρ₀_pos]
          calc |-(Real.pi / 3) - θ_m| * (10 * ρ) ≤ (Real.pi / 2) * 1 := mul_le_mul habs_th h10rho (by positivity) (by positivity)
            _ ≤ T₀ + 2 * Real.pi + 2 := by linarith only [Real.pi_pos, hT₀_ge4]
            _ ≤ C_d := hC_d_ge_T0
        · let α_t : ℝ := (1 - t) * θ_m + t * -(Real.pi / 3)
          exact (h_dn_arc_bd α_t (mem_convex_uIcc ht)).trans
            (sub_le_self _ (mul_nonneg hκ_arc_pos.le (pow_nonneg hρ_nn 3)))
      · rcases List.mem_cons.mp hS with rfl | hS
        · refine ⟨?_, ?_⟩
          · change ‖starRingEnd ℂ P₀ - ((10 * ρ : ℝ) : ℂ) * dir_minus‖ ≤ C_d
            rw [hP0m_eq, show (δ : ℂ) * dir_minus - ((10 * ρ : ℝ) : ℂ) * dir_minus =
              ((δ - 10 * ρ : ℝ) : ℂ) * dir_minus by push_cast; ring,
              norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith only [h12ρ_δ, hρ_nn]),
              exp_ofReal_mul_I_norm', mul_one]
            exact (by linarith only [hδ_14, hρ_nn, Real.pi_pos, hT₀_ge4] : δ - 10 * ρ ≤ T₀ + 2 * Real.pi + 2).trans hC_d_ge_T0
          · exact (h_dn_rad_bd t ht).trans
              (sub_le_self _ (mul_nonneg hκ_arc_pos.le (pow_nonneg hρ_nn 3)))
        · refine ⟨(h_dn_dz S hS t ht).trans ((by linarith only [Real.pi_pos] : T₀ + 2 ≤ T₀ + 2 * Real.pi + 2).trans hC_d_ge_T0), ?_⟩
          obtain ⟨u, hu, hζ_u⟩ := hj10m_mem S hS t ht
          have hpt := hJ10_pts u hu
          have him_ub : |(S.ζ t).im| ≤ T₀ := hj10m_im S hS t ht
          have hJ10_m : j10H (S.ζ t) ≤ -4 * κ_strip := by
            rw [hζ_u]; exact hpt.2.2.2.2.2.2.2.2.2.1.trans hκ_strip_j10
          have hstrip_t := S.hζ_strip (hj10m_strip S hS) t ht
          exact (h_fixed_strip_H _ hstrip_t.1 hstrip_t.2.1 him_ub hJ10_m).trans (by linarith only [hκ_strip_pos])
  · intro S hS _ hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_ray, mkStripRaySeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_arc, mkStripArcSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_rad, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn01, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn12, mkStripAffineSeg, mkStripSeg] at hkind
    rw [List.mem_singleton] at hS; subst hS; simp [seg_dn23, mkStripAffineSeg, mkStripSeg] at hkind
  · intro S hS _ hkind
    rcases List.mem_cons.mp hS with rfl | hS
    · refine ⟨t_m, by linarith only [ht_m_mem.1, hρ_nn], rfl, rfl, ht_m_mem.2, fun t ht => ?_⟩
      refine ⟨?_, ?_, h_dn_ray_bd t ht⟩
      · change ‖s + (t : ℂ) * dir_mA - s‖ = t
        rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1, hdirA_norm, mul_one]
      · change ‖dir_mA‖ = 1; exact hdirA_norm
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_arc, mkStripArcSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_rad, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn01, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn12, mkStripAffineSeg, mkStripSeg] at hkind
    rw [List.mem_singleton] at hS; subst hS; simp [seg_dn23, mkStripAffineSeg, mkStripSeg] at hkind
  · intro S hS _ hkind t ht
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_ray, mkStripRaySeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS
    · let α_t : ℝ := (1 - t) * θ_m + t * -(Real.pi / 3)
      exact h_dn_arc_bd α_t (mem_convex_uIcc ht)
    rcases List.mem_cons.mp hS with rfl | hS
    · exact h_dn_rad_bd t ht
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn01, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn12, mkStripAffineSeg, mkStripSeg] at hkind
    rw [List.mem_singleton] at hS; subst hS; simp [seg_dn23, mkStripAffineSeg, mkStripSeg] at hkind
  · intro S hS _ hkind t ht
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_ray, mkStripRaySeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_arc, mkStripArcSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_rad, mkStripAffineSeg, mkStripSeg] at hkind
    obtain ⟨u, hu, hζ_u⟩ := hj10m_mem S hS t ht
    have hpt := hJ10_pts u hu
    have hstrip_t := S.hζ_strip (hj10m_strip S hS) t ht
    have him_ub : |(S.ζ t).im| ≤ T₀ := hj10m_im S hS t ht
    have hJ10_m : j10H (S.ζ t) ≤ -4 * κ_strip := by
      rw [hζ_u]; exact hpt.2.2.2.2.2.2.2.2.2.1.trans hκ_strip_j10
    exact h_fixed_strip_H _ hstrip_t.1 hstrip_t.2.1 him_ub hJ10_m
  · intro S hS hfalse
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_ray, mkStripRaySeg, mkStripSeg] at hfalse
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_arc, mkStripArcSeg, mkStripSeg] at hfalse
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_rad, mkStripAffineSeg, mkStripSeg] at hfalse
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn01, mkStripAffineSeg, mkStripSeg] at hfalse
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn12, mkStripAffineSeg, mkStripSeg] at hfalse
    rw [List.mem_singleton] at hS; subst hS; simp [seg_dn23, mkStripAffineSeg, mkStripSeg] at hfalse
  · intro S hS _ hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_ray, mkStripRaySeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_arc, mkStripArcSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_rad, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn01, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn12, mkStripAffineSeg, mkStripSeg] at hkind
    rw [List.mem_singleton] at hS; subst hS; simp [seg_dn23, mkStripAffineSeg, mkStripSeg] at hkind

private lemma zp_lower_rayB_bd {C_F δ ρ c_γ v φ' : ℝ} {s dir_mB b : ℂ}
    (hCF_nn : 0 ≤ C_F) (hCF_delta : C_F * δ ≤ 1 / 80)
    (hρ_nn : 0 ≤ ρ) (hρ_le_δ : ρ ≤ δ) (hcγ_le : c_γ ≤ (Real.pi ^ 2 / 6) * (1 / (3 * √2)))
    (hcos : Real.cos (2 * (5 * Real.pi / 4) + Real.pi / 2 - φ') ≤ -(1 / √2) ∧
      Real.cos (3 * (5 * Real.pi / 4)) = 1 / √2)
    (hv_nn : 0 ≤ v) (hv_le_rho : v ≤ ρ)
    (hsr : (chartPhiV (s + (v : ℂ) * dir_mB) b).re - (chartPhiV s b).re ≤ (Real.pi ^ 2 / 6) *
      (ρ * v ^ 2 * Real.cos (2 * (5 * Real.pi / 4) + Real.pi / 2 - φ') +
       (1 / 3 : ℝ) * v ^ 3 * Real.cos (3 * (5 * Real.pi / 4)) +
       2 * C_F * v ^ 2 * (ρ + v) ^ 2)) :
    (chartPhiV (s + (v : ℂ) * dir_mB) b).re ≤ (chartPhiV s b).re - c_γ * ρ * v ^ 2 := by
  have hsq_rho : (ρ + v) ^ 2 ≤ 4 * ρ ^ 2 := by nlinarith only [hv_nn, hv_le_rho]
  have h8CF : 8 * C_F * ρ ≤ 1 / (3 * √2) := by
    have h8 : 8 * C_F * ρ ≤ 8 * C_F * δ := mul_le_mul_of_nonneg_left hρ_le_δ (by positivity)
    have hsq2_lt : √2 < 2 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hinv6 : (1 / 10 : ℝ) ≤ 1 / (3 * √2) := by
      rw [one_div_le_one_div (by positivity) (by positivity)]; linarith only [hsq2_lt]
    linarith only [h8, hCF_delta, hinv6]
  have hrem_bd : 2 * C_F * v ^ 2 * (ρ + v) ^ 2 ≤ (1 / (3 * √2)) * ρ * v ^ 2 := by
    have hv2_nn : 0 ≤ v ^ 2 := sq_nonneg v
    calc 2 * C_F * v ^ 2 * (ρ + v) ^ 2 ≤ 2 * C_F * v ^ 2 * (4 * ρ ^ 2) := mul_le_mul_of_nonneg_left hsq_rho (by positivity)
      _ = (8 * C_F * ρ) * (ρ * v ^ 2) := by ring
      _ ≤ (1 / (3 * √2)) * (ρ * v ^ 2) := mul_le_mul_of_nonneg_right h8CF (mul_nonneg hρ_nn hv2_nn)
      _ = (1 / (3 * √2)) * ρ * v ^ 2 := by ring
  have hv3_ub : (1 / 3 : ℝ) * v ^ 3 * Real.cos (3 * (5 * Real.pi / 4)) ≤ (1 / 3 : ℝ) * ρ * v ^ 2 * (1 / √2) := by
    rw [hcos.2]
    have hv2_nn := sq_nonneg v
    calc (1 / 3 : ℝ) * v ^ 3 * (1 / √2)
        = (1 / 3 : ℝ) * (v * v ^ 2) * (1 / √2) := by ring
      _ ≤ (1 / 3 : ℝ) * (ρ * v ^ 2) * (1 / √2) := by
          gcongr
      _ = (1 / 3 : ℝ) * ρ * v ^ 2 * (1 / √2) := by ring
  have hcos1_mul : ρ * v ^ 2 * Real.cos (2 * (5 * Real.pi / 4) + Real.pi / 2 - φ') ≤ -(1 / √2) * ρ * v ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hcos.1 (mul_nonneg hρ_nn (sq_nonneg v))
    linarith only [hmul]
  have hinner_neg : ρ * v ^ 2 * Real.cos (2 * (5 * Real.pi / 4) + Real.pi / 2 - φ') +
      (1 / 3 : ℝ) * v ^ 3 * Real.cos (3 * (5 * Real.pi / 4)) + 2 * C_F * v ^ 2 * (ρ + v) ^ 2 ≤
      -(1 / (3 * √2)) * ρ * v ^ 2 := by
    calc ρ * v ^ 2 * Real.cos (2 * (5 * Real.pi / 4) + Real.pi / 2 - φ') +
          (1 / 3 : ℝ) * v ^ 3 * Real.cos (3 * (5 * Real.pi / 4)) + 2 * C_F * v ^ 2 * (ρ + v) ^ 2
        ≤ -(1 / √2) * ρ * v ^ 2 + (1 / 3 : ℝ) * ρ * v ^ 2 * (1 / √2) + (1 / (3 * √2)) * ρ * v ^ 2 :=
            add_le_add (add_le_add hcos1_mul hv3_ub) hrem_bd
      _ = -(1 / (3 * √2)) * ρ * v ^ 2 := by ring
  have hmul := mul_le_mul_of_nonneg_left hinner_neg (by positivity [Real.pi_pos] : 0 ≤ Real.pi ^ 2 / 6)
  have hc_mul : c_γ * ρ * v ^ 2 ≤ (Real.pi ^ 2 / 6) * (1 / (3 * √2)) * ρ * v ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcγ_le hρ_nn) (sq_nonneg v)
  linarith only [hsr, hmul, hc_mul]

private lemma zp_lower_caseB
    {η : ℂ → ℂ → ℂ} {ρ_F C_F C_om C_om' c_mid T_junc C_L c_L κ_J7 : ℝ}
    (hCF_nn : 0 ≤ C_F)
    (hη_an : AnalyticOnNhd ℂ (Function.uncurry η) (ball (0 : ℂ × ℂ) ρ_F))
    (hF_id : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      2 * Complex.log (chartB w / chartB s) * deriv chartOmega w =
        ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (w ^ 2 - s ^ 2) * (1 + η w s))
    (hη_bd : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      ‖η w s‖ ≤ C_F * (‖w‖ + ‖s‖))
    (_hρF_pos : 0 < ρ_F)
    (hC_om_pos : 0 < C_om)
    (hC_om : ∀ ζ ∈ stripClosed, ‖chartOmega ζ‖ ≤ C_om * (1 + ζ.im ^ 2))
    (hC_om'_pos : 0 < C_om')
    (hC_om' : ∀ ζ ∈ stripClosed, ‖deriv chartOmega ζ‖ ≤ C_om' * (1 + |ζ.im|))
    (_hc_mid_pos : 0 < c_mid)
    (h_mid_lb : ∀ τ : ℝ, c_mid * τ ^ 2 ≤ ‖chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖)
    (h_junc : ∀ {T₀ : ℝ}, T_junc ≤ T₀ → ∀ μ ∈ Icc (muStar / 2) (2 * muStar),
      ∃! x_L : ℝ, x_L ∈ Ioo (0 : ℝ) (1 / 2) ∧
        (chartOmega ((x_L : ℂ) - Complex.I * (T₀ : ℂ))).re = μ ∧
        1 / 2 - x_L ≤ C_L / T₀ ∧
        c_L * T₀ ^ 2 ≤ (chartOmega ((x_L : ℂ) - Complex.I * (T₀ : ℂ))).im ∧
        (∀ x ∈ Icc x_L (1 / 2), j10H ((x : ℂ) - Complex.I * (T₀ : ℂ)) ≤ -κ_J7 * T₀))
    {δ T₀ κ_strip c_γ κ_arc μ₀ c_Γ C_Γ C_d C_om_max C_om'_max ρ₀ ρ φ' : ℝ}
    (h_inv_sq2 : 1 / √2 = √2 / 2)
    (_hδ_pos : 0 < δ) (hδ_14 : δ ≤ 1 / 4) (hδ_rhoF : δ < min ρ_F (1 / 2))
    (hδ_om : δ ≤ muStar / (6 * (C_om' + 1))) (hCF_delta : C_F * δ ≤ 1 / 80)
    (hT₀_ge4 : 4 ≤ T₀) (hT₀_Tjunc : T_junc ≤ T₀)
    (hT₀_mid_sq : 2 * C_om' * C_L + 1 ≤ c_mid * T₀ ^ 2)
    (hT₀_yL_sq : muStar / 4 + 1 ≤ c_L * T₀ ^ 2)
    (hκ_strip_pos : 0 < κ_strip) (hκ_strip_j7 : -κ_J7 * T₀ ≤ -4 * κ_strip)
    (hρ₀_pos : 0 < ρ₀) (hρ₀_delta : 12 * ρ₀ ≤ δ)
    (hC_om_max_eq : C_om_max = C_om * (1 + T₀ ^ 2))
    (hC_om'_max_eq : C_om'_max = C_om' * (1 + T₀))
    (hCom'_max_nn : 0 ≤ C_om'_max) (hCom_max_nn : 0 ≤ C_om_max)
    (hC_Γ_ge_om : C_om_max ≤ C_Γ) (hC_Γ_ge_2om : 2 * muStar + C_om_max ≤ C_Γ)
    (hC_Γ_ge_32 : 3 / 2 * muStar ≤ C_Γ)
    (hc_Γ_le_mu0 : c_Γ ≤ μ₀) (hc_Γ_le_1 : c_Γ ≤ 1)
    (hC_d_ge_om : C_om'_max * (T₀ + 2 + 2 * Real.pi) ≤ C_d)
    (hC_d_ge_2mu : C_om_max + 2 * muStar ≤ C_d)
    (hC_d_ge_T0 : T₀ + 2 * Real.pi + 2 ≤ C_d) (hT0_pi_gt1 : (1 : ℝ) ≤ T₀ + 2 * Real.pi + 2)
    (hCom_le_Cd : (3 / 2 : ℝ) * C_om' ≤ C_d)
    (hc_γ_pos : 0 < c_γ)
    (hcγ_le : c_γ ≤ (Real.pi ^ 2 / 6) * (1 / (3 * √2)))
    (hμ₀_eq : μ₀ = (3 / 4 : ℝ) * muStar) (hμ₀_pos : 0 < μ₀)
    (hρ_nn : 0 ≤ ρ) (hρ_le : ρ ≤ ρ₀) (hφ_nn : 0 ≤ φ') (hφ_lt : φ' < Real.pi / 4)
    {s b : ℂ}
    (hs_eq : s = (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 - φ' : ℝ) : ℂ)))
    (hb_eq : b = chartB s) (hb_im : b.im ≤ 0) (hb_re_pos : 0 < b.re) (hb_ne : b ≠ 0)
    (hb_norm_range : ‖b‖ ∈ Icc (3 / 4 * xiStar) (5 / 4 * xiStar))
    (h_inner_om : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 / 2 → ‖w‖ ≤ δ →
      0 ≤ (chartOmega w).re ∧ c_Γ ≤ ‖chartOmega w‖ ∧ ‖chartOmega w‖ ≤ C_Γ ∧
        ‖deriv chartOmega w‖ ≤ (3 / 2 : ℝ) * C_om')
    (h_fixed_strip_H : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 / 2 → |ζ.im| ≤ T₀ →
      j10H ζ ≤ -4 * κ_strip →
      (chartPhiV ζ b).re ≤ (chartPhiV s b).re - κ_strip) :
    ∃ lower_segs : List ContourSeg,
      ContourChained (chartOmega s) (chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ))) lower_segs ∧
      lower_segs.length ≤ 6 ∧
      (∀ S ∈ lower_segs, S.b - S.a ≤ 1) ∧
      (∀ S ∈ lower_segs, ∀ t ∈ Icc S.a S.b,
        0 ≤ (S.ω t).re ∧ c_Γ ≤ ‖S.ω t‖ ∧ ‖S.ω t‖ ≤ C_Γ ∧ ‖S.ω' t‖ ≤ C_d) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → ∀ t ∈ Icc S.a S.b,
        ‖S.ζ' t‖ ≤ C_d ∧ (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → S.kind ≠ .upperRay) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → S.kind = .lowerRay →
        ∃ t_max ≥ (0 : ℝ), S.a = 0 ∧ S.b = t_max ∧ t_max ≤ 11 * ρ ∧
          ∀ t ∈ Icc 0 t_max, ‖S.ζ t - s‖ = t ∧ ‖S.ζ' t‖ = 1 ∧
            (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - c_γ * ρ * t ^ 2) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → S.kind = .arcRadial →
        ∀ t ∈ Icc S.a S.b, (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - κ_arc * ρ ^ 3) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → S.kind = .fixedStrip →
        ∀ t ∈ Icc S.a S.b, (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - κ_strip) ∧
      (∀ S ∈ lower_segs, S.isStrip = false →
        ∀ t ∈ Icc S.a S.b,
          μ₀ ≤ (S.ω t).re ∧ crudeExponentEc (S.ω t) b ≤ (chartPhiV s b).re - c_γ * ρ * s.re ^ 2) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → S.kind ≠ .crudeEdge) := by
  have hs_norm : ‖s‖ = ρ := by
    rw [hs_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ_nn, exp_ofReal_mul_I_norm', mul_one]
  have hs_re_nn : 0 ≤ s.re := by
    rw [hs_eq, Complex.re_ofReal_mul, exp_ofReal_mul_I_re'']
    exact mul_nonneg hρ_nn (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [hφ_lt]⟩)
  have hρ_lt_δ : ρ < δ := by linarith only [hρ_le, hρ₀_delta, hρ₀_pos]
  have hs_F : s ∈ ball (0 : ℂ) ρ_F :=
    mem_ball_zero_iff.mpr (hs_norm.symm ▸ lt_trans hρ_lt_δ (lt_of_lt_of_le hδ_rhoF (min_le_left _ _)))
  let dir_mB : ℂ := Complex.exp (Complex.I * ((5 * Real.pi / 4 : ℝ) : ℂ))
  have hdirB_norm : ‖dir_mB‖ = 1 := exp_ofReal_mul_I_norm' _
  have hdirB_re : dir_mB.re = -(1 / √2) := by
    dsimp [dir_mB]; rw [exp_ofReal_mul_I_re'', show 5 * Real.pi / 4 = Real.pi / 4 + Real.pi by ring,
      Real.cos_add_pi, Real.cos_pi_div_four, h_inv_sq2]
  have hdirB_im : dir_mB.im = -(1 / √2) := by
    dsimp [dir_mB]; rw [exp_ofReal_mul_I_im'', show 5 * Real.pi / 4 = Real.pi / 4 + Real.pi by ring,
      Real.sin_add_pi, Real.sin_pi_div_four, h_inv_sq2]
  have hs_re_eq : s.re = ρ * Real.sin φ' := by
    rw [hs_eq, Complex.re_ofReal_mul, exp_ofReal_mul_I_re'', Real.cos_pi_div_two_sub]
  have hs_im_eq : s.im = ρ * Real.cos φ' := by
    rw [hs_eq, Complex.im_ofReal_mul, exp_ofReal_mul_I_im'', Real.sin_pi_div_two_sub]
  have hsin_le_cos : Real.sin φ' ≤ 1 / √2 ∧ 1 / √2 ≤ Real.cos φ' := by
    have h1 : Real.cos φ' ≥ √2 / 2 := by
      have ha := Real.strictAntiOn_cos.antitoneOn (a := φ') (b := Real.pi / 4)
        ⟨hφ_nn, hφ_lt.le.trans (by linarith only [Real.pi_pos])⟩
        ⟨by positivity [Real.pi_pos], by linarith only [Real.pi_pos]⟩ hφ_lt.le
      rwa [Real.cos_pi_div_four] at ha
    have h2 : Real.sin φ' ≤ √2 / 2 := by
      rw [← Real.cos_pi_div_two_sub]
      have ha := Real.strictAntiOn_cos.antitoneOn (a := Real.pi / 4) (b := Real.pi / 2 - φ')
        ⟨by positivity [Real.pi_pos], by linarith only [Real.pi_pos]⟩
        ⟨by linarith only [Real.pi_pos, hφ_lt], by linarith only [Real.pi_pos, hφ_nn]⟩ (by linarith only [hφ_lt])
      rwa [Real.cos_pi_div_four] at ha
    exact ⟨h2.trans h_inv_sq2.symm.le, h_inv_sq2.le.trans h1⟩
  let t_hit : ℝ := √2 * s.re
  have ht_hit_nn : 0 ≤ t_hit := mul_nonneg (Real.sqrt_nonneg 2) hs_re_nn
  have ht_hit_le_rho : t_hit ≤ ρ := by
    dsimp [t_hit]; rw [hs_re_eq]
    have h1 : Real.sin φ' ≤ 1 / √2 := hsin_le_cos.1
    have hsq2 : (0 : ℝ) < √2 := by positivity
    calc √2 * (ρ * Real.sin φ') ≤ √2 * (ρ * (1 / √2)) := by gcongr
      _ = ρ := by field_simp [hsq2.ne']
  let τ_e : ℝ := s.im - s.re
  have hτ_e_mem : τ_e ∈ Icc 0 ρ := by
    dsimp [τ_e]; rw [hs_im_eq, hs_re_eq]
    have h1 : Real.sin φ' ≤ Real.cos φ' := hsin_le_cos.1.trans hsin_le_cos.2
    have h2 : Real.cos φ' - Real.sin φ' ≤ 1 := by
      linarith only [Real.cos_le_one φ', Real.sin_nonneg_of_nonneg_of_le_pi hφ_nn (by linarith only [Real.pi_pos, hφ_lt])]
    have h1' := mul_nonneg hρ_nn (sub_nonneg.mpr h1)
    have h2' := mul_le_of_le_one_right hρ_nn h2
    exact ⟨by linarith only [h1'], by linarith only [h2']⟩
  have hhit_eq : s + (t_hit : ℂ) * dir_mB = Complex.I * (τ_e : ℂ) := by
    apply Complex.ext
    · rw [Complex.add_re, Complex.re_ofReal_mul, hdirB_re]; dsimp [t_hit]
      rw [mul_neg, mul_one_div, mul_comm √2 s.re, mul_div_cancel_right₀ _ (Real.sqrt_ne_zero'.mpr two_pos)]
      simp
    · rw [Complex.add_im, Complex.im_ofReal_mul, hdirB_im]; dsimp [t_hit, τ_e]
      rw [mul_neg, mul_one_div, mul_comm √2 s.re, mul_div_cancel_right₀ _ (Real.sqrt_ne_zero'.mpr two_pos)]
      simp; ring
  have h_dn_rayB_strip : ∀ v ∈ Icc (0 : ℝ) t_hit,
      0 ≤ (s + (v : ℂ) * dir_mB).re ∧ (s + (v : ℂ) * dir_mB).re ≤ 1 / 2 := fun v hv => by
    rw [Complex.add_re, Complex.re_ofReal_mul, hdirB_re]
    have hsq2 : (0 : ℝ) < √2 := by positivity
    have hge0 : 0 ≤ s.re + v * -(1 / √2) := by
      have hdiv : v / √2 ≤ s.re := (div_le_iff₀ hsq2).mpr (by linarith only [hv.2])
      rw [show v * -(1 / √2) = -(v / √2) by ring]; linarith only [hdiv]
    have hle12 : s.re + v * -(1 / √2) ≤ 1 / 2 := by
      have hsre_le : s.re ≤ ρ := (le_abs_self s.re).trans ((Complex.abs_re_le_norm s).trans (by rw [hs_norm]))
      have hvn_le : v * -(1 / √2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv.1 (neg_nonpos.mpr (by positivity))
      linarith only [hsre_le, hvn_le, hρ_le, hρ₀_delta, hδ_14, hρ₀_pos]
    exact ⟨hge0, hle12⟩
  have h_dn_rayB_F : ∀ v ∈ Icc (0 : ℝ) t_hit,
      s + (v : ℂ) * dir_mB ∈ ball (0 : ℂ) ρ_F ∧
      0 ≤ (s + (v : ℂ) * dir_mB).re ∧ (s + (v : ℂ) * dir_mB).re ≤ 1 / 4 := fun v hv => by
    have hvn : ‖s + (v : ℂ) * dir_mB‖ ≤ 2 * ρ := by
      calc ‖s + (v : ℂ) * dir_mB‖ ≤ ‖s‖ + ‖(v : ℂ) * dir_mB‖ := norm_add_le _ _
        _ = ρ + v := by rw [hs_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hv.1, hdirB_norm, mul_one]
        _ ≤ 2 * ρ := by linarith [hv.2, ht_hit_le_rho]
    have hltF : ‖s + (v : ℂ) * dir_mB‖ < ρ_F :=
      (hvn.trans (mul_le_mul_of_nonneg_left hρ_le (by norm_num))).trans_lt
        (by linarith [hρ₀_delta, hδ_rhoF.trans_le (min_le_left _ _)])
    have hre14 : (s + (v : ℂ) * dir_mB).re ≤ 1 / 4 :=
      (Complex.re_le_norm _).trans (hvn.trans (by linarith [hρ_le, hρ₀_delta, hδ_14]))
    exact ⟨mem_ball_zero_iff.mpr hltF, (h_dn_rayB_strip v hv).1, hre14⟩
  have h_dn_rayB_bd : ∀ v ∈ Icc (0 : ℝ) t_hit,
      (chartPhiV (s + (v : ℂ) * dir_mB) b).re ≤ (chartPhiV s b).re - c_γ * ρ * v ^ 2 := fun v hv =>
    zp_lower_rayB_bd hCF_nn hCF_delta hρ_nn (by linarith only [hρ_le, hρ₀_delta, hρ₀_pos]) hcγ_le
      (lower_ray_le_pi4_cos_le hφ_nn hφ_lt.le) hv.1 (hv.2.trans ht_hit_le_rho)
      (saddle_ray_H_le hCF_nn hη_an hF_id hη_bd hρ_nn ht_hit_nn
        s b hs_eq hb_re_pos hb_eq hs_F h_dn_rayB_F v hv)
  let ζ_e : ℂ := Complex.I * (τ_e : ℂ)
  let ω_e : ℂ := chartOmega ζ_e
  let μ_e : ℝ := ω_e.re
  let ν_e : ℝ := ω_e.im
  have hζ_e_norm : ‖ζ_e‖ ≤ δ := by
    dsimp [ζ_e]; rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hτ_e_mem.1]
    exact hτ_e_mem.2.trans hρ_lt_δ.le
  have hω_e_sub : ‖ω_e - (muStar : ℂ)‖ ≤ muStar / 4 := by
    have hdiff := chartOmega_strip_sub_zero_le hC_om' (by simp [ζ_e]) (by simp [ζ_e]) (hζ_e_norm.trans (hδ_14.trans (by norm_num)))
    have hC_nn : 0 ≤ C_om' := by
      have h0' := hC_om' 0 ⟨le_rfl, zero_le_one⟩
      have hle0 : (0 : ℝ) ≤ C_om' * 1 := by simpa using (norm_nonneg _).trans h0'
      linarith only [hle0]
    have hCδ : (3 / 2 : ℝ) * C_om' * δ ≤ muStar / 4 := by
      calc (3 / 2 : ℝ) * C_om' * δ ≤ (3 / 2 : ℝ) * C_om' * (muStar / (6 * (C_om' + 1))) :=
            mul_le_mul_of_nonneg_left hδ_om (by positivity)
        _ = C_om' * ((muStar / 4) / (C_om' + 1)) := by
            rw [div_eq_mul_inv muStar (6 * (C_om' + 1)), mul_inv,
              div_eq_mul_inv (muStar / 4), div_eq_mul_inv muStar 4]; ring
        _ ≤ muStar / 4 := mul_div_add_one_le hC_nn (by positivity [muStar_pos])
    exact hdiff.trans ((mul_le_mul_of_nonneg_left hζ_e_norm (by positivity)).trans hCδ)
  have hμ_e_mem : μ_e ∈ Icc μ₀ (5 / 4 * muStar) := by
    have h1 := abs_le.mp ((Complex.abs_re_le_norm _).trans hω_e_sub)
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    exact ⟨by rw [hμ₀_eq]; dsimp [μ_e]; linarith only [h1.1, muStar_pos],
      by dsimp [μ_e]; linarith only [h1.2, muStar_pos]⟩
  have hν_e_abs : |ν_e| ≤ muStar / 4 := by
    have h1 := (Complex.abs_im_le_norm _).trans hω_e_sub
    simpa [ν_e] using h1
  have hEc_ωe : crudeExponentEc ω_e b ≤ (chartPhiV s b).re - c_γ * ρ * s.re ^ 2 := by
    have hE3 := (lemma_E2_E3.2.2.2.2 τ_e b).symm
    change crudeExponentEc ω_e b = (chartPhiV ζ_e b).re at hE3
    rw [hE3]; dsimp [ζ_e]; rw [← hhit_eq]
    have hhit_bd := h_dn_rayB_bd t_hit ⟨ht_hit_nn, le_rfl⟩
    have htsq : t_hit ^ 2 = 2 * s.re ^ 2 := by
      dsimp [t_hit]; rw [mul_pow, Real.sq_sqrt (by norm_num)]
    rw [htsq] at hhit_bd
    have hnn : 0 ≤ c_γ * ρ * s.re ^ 2 := by positivity
    linarith
  let μ_b : ℝ := Real.pi * ‖b‖ / 3
  have hμ_b_mem : μ_b ∈ Icc μ₀ (5 / 4 * muStar) := by
    dsimp [μ_b]; rw [hμ₀_eq]; unfold muStar
    exact ⟨by nlinarith only [Real.pi_pos, hb_norm_range.1], by nlinarith only [Real.pi_pos, hb_norm_range.2]⟩
  have hμ_b_junc : μ_b ∈ Icc (muStar / 2) (2 * muStar) :=
    ⟨(by rw [hμ₀_eq]; linarith only [muStar_pos] : muStar / 2 ≤ μ₀).trans hμ_b_mem.1,
     hμ_b_mem.2.trans (by linarith only [muStar_pos])⟩
  obtain ⟨x_L, hxL_props, _⟩ := h_junc hT₀_Tjunc μ_b hμ_b_junc
  rcases hxL_props with ⟨hxL_Ioo, hOm_L_re, hxL_diff, hOm_L_im, hxL_H⟩
  let ζ_L : ℂ := (x_L : ℂ) - Complex.I * (T₀ : ℂ)
  let ω_L : ℂ := chartOmega ζ_L
  let Y_L : ℝ := ω_L.im
  have hν_lt_YL : ν_e < Y_L := by
    have h1 : ν_e ≤ muStar / 4 := (abs_le.mp hν_e_abs).2
    linarith only [h1, hT₀_yL_sq, hOm_L_im]
  let ω_mid : ℂ := (μ_b : ℂ) + Complex.I * (ν_e : ℂ)
  let seg_dn_rayB := mkStripRaySeg .lowerRay s dir_mB t_hit ht_hit_nn h_dn_rayB_strip
  let seg_cr1 := mkCrudeAffineSeg ω_e ω_mid
  let seg_cr2 := mkCrudeAffineSeg ω_mid ω_L
  have hxL_re : 0 ≤ ζ_L.re ∧ ζ_L.re ≤ 1 / 2 := by
    refine ⟨by simpa [ζ_L] using hxL_Ioo.1.le, by simpa [ζ_L] using hxL_Ioo.2.le⟩
  have hhalf_re : 0 ≤ ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)).re ∧
      ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)).re ≤ 1 / 2 := by simp
  let seg_junc := mkStripAffineSeg .fixedStrip ζ_L ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)) hxL_re hhalf_re
  let lower_segs := [seg_dn_rayB, seg_cr1, seg_cr2, seg_junc]
  have hchainB : ContourChained (chartOmega s)
      (chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ))) lower_segs := by
    have hw0 : seg_dn_rayB.ω 0 = chartOmega s := by
      change chartOmega (s + ((0 : ℝ) : ℂ) * dir_mB) = chartOmega s; simp
    have hw1 : seg_cr1.ω 0 = seg_dn_rayB.ω seg_dn_rayB.b := by
      change ω_e + (0 : ℂ) * (ω_mid - ω_e) = chartOmega (s + (t_hit : ℂ) * dir_mB)
      rw [hhit_eq]; simp [ω_e, ζ_e]
    have hw2 : seg_cr2.ω 0 = seg_cr1.ω 1 := by
      change ω_mid + (0 : ℂ) * (ω_L - ω_mid) = ω_e + (1 : ℂ) * (ω_mid - ω_e)
      simp
    have hw3 : seg_junc.ω 0 = seg_cr2.ω 1 := by
      dsimp [seg_junc, mkStripAffineSeg, mkStripSeg, seg_cr2, mkCrudeAffineSeg]; simp [ω_L]
    have hw4 : seg_junc.ω 1 = chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)) := by
      dsimp [seg_junc, mkStripAffineSeg, mkStripSeg]; simp
    exact ⟨hw0, hw1, hw2, hw3, hw4⟩
  have hEc_mid : crudeExponentEc ω_mid b ≤ crudeExponentEc ω_e b := by
    have h1 := (lemma_E2_E3.2.2.1 hb_ne ν_e μ_e (lt_of_lt_of_le hμ₀_pos hμ_e_mem.1)).1
    have hω_e_eq : ω_e = (μ_e : ℂ) + (ν_e : ℂ) * Complex.I := by apply Complex.ext <;> simp [μ_e, ν_e]
    have hω_mid_eq : ω_mid = (μ_b : ℂ) + (ν_e : ℂ) * Complex.I := by
      dsimp [ω_mid]; apply Complex.ext <;> simp
    rw [show (Real.pi : ℂ) * ↑‖b‖ / 3 + (ν_e : ℂ) * Complex.I = ω_mid by dsimp [ω_mid, μ_b]; push_cast; ring] at h1
    rwa [← hω_e_eq] at h1
  have hcr1_bd : ∀ t ∈ Icc (0 : ℝ) 1,
      μ₀ ≤ (seg_cr1.ω t).re ∧ crudeExponentEc (seg_cr1.ω t) b ≤ (chartPhiV s b).re - c_γ * ρ * s.re ^ 2 := by
    intro t ht
    let μ_t : ℝ := (1 - t) * μ_e + t * μ_b
    have hω_eq : seg_cr1.ω t = (μ_t : ℂ) + (ν_e : ℂ) * Complex.I := by
      change ω_e + (t : ℂ) * (ω_mid - ω_e) = (μ_t : ℂ) + (ν_e : ℂ) * Complex.I
      apply Complex.ext
      · simp [ω_mid, μ_e, μ_t]; ring
      · simp [ω_mid, ν_e]
    rw [hω_eq]
    have hre : ((μ_t : ℂ) + (ν_e : ℂ) * Complex.I).re = μ_t := by simp
    have hμt_lb : μ₀ ≤ μ_t := by
      dsimp [μ_t]; nlinarith only [ht.1, ht.2, hμ_e_mem.1, hμ_b_mem.1]
    refine ⟨by simpa using hμt_lb, ?_⟩
    have hEc_le : crudeExponentEc ((μ_t : ℂ) + (ν_e : ℂ) * Complex.I) b ≤
        max (crudeExponentEc ω_e b) (crudeExponentEc ω_mid b) := by
      have hconv := (lemma_E2_E3.2.1 hb_ne ν_e).convexOn
      have hconv_pt := hconv.2 (lt_of_lt_of_le hμ₀_pos hμ_e_mem.1) (lt_of_lt_of_le hμ₀_pos hμ_b_mem.1)
        (by linarith only [ht.2] : 0 ≤ 1 - t) ht.1 (by ring)
      have hω_e_eq : ω_e = (μ_e : ℂ) + (ν_e : ℂ) * Complex.I := by apply Complex.ext <;> simp [μ_e, ν_e]
      have hω_mid_eq : ω_mid = (μ_b : ℂ) + (ν_e : ℂ) * Complex.I := by
        dsimp [ω_mid]; apply Complex.ext <;> simp
      have hle1 : (1 - t) * crudeExponentEc ((μ_e : ℂ) + (ν_e : ℂ) * Complex.I) b +
          t * crudeExponentEc ((μ_b : ℂ) + (ν_e : ℂ) * Complex.I) b ≤
          max (crudeExponentEc ((μ_e : ℂ) + (ν_e : ℂ) * Complex.I) b)
              (crudeExponentEc ((μ_b : ℂ) + (ν_e : ℂ) * Complex.I) b) := by
        have h1m := le_max_left (crudeExponentEc ((μ_e : ℂ) + (ν_e : ℂ) * Complex.I) b)
          (crudeExponentEc ((μ_b : ℂ) + (ν_e : ℂ) * Complex.I) b)
        have h2m := le_max_right (crudeExponentEc ((μ_e : ℂ) + (ν_e : ℂ) * Complex.I) b)
          (crudeExponentEc ((μ_b : ℂ) + (ν_e : ℂ) * Complex.I) b)
        nlinarith only [ht.1, ht.2, h1m, h2m]
      have h_eq1 : ((1 - t) * μ_e + t * μ_b : ℂ) + (ν_e : ℂ) * Complex.I = (μ_t : ℂ) + (ν_e : ℂ) * Complex.I := by
        dsimp [μ_t]; push_cast; ring
      have hconv_pt' : crudeExponentEc ((μ_t : ℂ) + (ν_e : ℂ) * Complex.I) b ≤
          (1 - t) * crudeExponentEc ((μ_e : ℂ) + (ν_e : ℂ) * Complex.I) b +
            t * crudeExponentEc ((μ_b : ℂ) + (ν_e : ℂ) * Complex.I) b := by
        simpa [h_eq1] using hconv_pt
      simpa [← hω_e_eq, ← hω_mid_eq] using hconv_pt'.trans hle1
    have hmax_bd : max (crudeExponentEc ω_e b) (crudeExponentEc ω_mid b) ≤
        crudeExponentEc ω_e b := max_le le_rfl hEc_mid
    exact hEc_le.trans (hmax_bd.trans hEc_ωe)
  have hb_arg_nonpos : b.arg ≤ 0 := arg_nonpos_of_re_pos_im_nonpos hb_re_pos hb_im
  have hcr2_bd : ∀ t ∈ Icc (0 : ℝ) 1,
      μ₀ ≤ (seg_cr2.ω t).re ∧ crudeExponentEc (seg_cr2.ω t) b ≤ (chartPhiV s b).re - c_γ * ρ * s.re ^ 2 := by
    intro t ht
    let ν_t : ℝ := (1 - t) * ν_e + t * Y_L
    have hω_eq : seg_cr2.ω t = (μ_b : ℂ) + (ν_t : ℂ) * Complex.I := by
      change ω_mid + (t : ℂ) * (ω_L - ω_mid) = (μ_b : ℂ) + (ν_t : ℂ) * Complex.I
      apply Complex.ext
      · simp [ω_mid, ω_L, ζ_L, hOm_L_re]
      · simp [ω_mid, Y_L, ν_t]; ring
    rw [hω_eq]
    have hν_ge : ν_e ≤ ν_t := by dsimp [ν_t]; nlinarith only [ht.1, ht.2, hν_lt_YL]
    have hline_t := lemma_E2_E3.2.2.2.1 hb_ne ν_t
    have hline_e := lemma_E2_E3.2.2.2.1 hb_ne ν_e
    change crudeExponentEc ((Real.pi * ‖b‖ / 3 : ℂ) + (ν_t : ℂ) * Complex.I) b = _ at hline_t
    change crudeExponentEc ((Real.pi * ‖b‖ / 3 : ℂ) + (ν_e : ℂ) * Complex.I) b = _ at hline_e
    have hslope : 2 * b.arg * ν_t - (2 * Real.pi / 3) * (‖b‖ - b.re) ≤
        2 * b.arg * ν_e - (2 * Real.pi / 3) * (‖b‖ - b.re) := by nlinarith only [hb_arg_nonpos, hν_ge]
    have hω_mid_eq : ω_mid = (μ_b : ℂ) + (ν_e : ℂ) * Complex.I := by
      dsimp [ω_mid]; apply Complex.ext <;> simp
    refine ⟨by simpa using hμ_b_mem.1, ?_⟩
    have hmb_c : (μ_b : ℂ) = (Real.pi : ℂ) * ↑‖b‖ / 3 := by dsimp [μ_b]; push_cast; ring
    calc crudeExponentEc ((μ_b : ℂ) + (ν_t : ℂ) * Complex.I) b
        = crudeExponentEc ((Real.pi : ℂ) * ↑‖b‖ / 3 + (ν_t : ℂ) * Complex.I) b := by rw [hmb_c]
      _ = 2 * b.arg * ν_t - (2 * Real.pi / 3) * (‖b‖ - b.re) := hline_t
      _ ≤ 2 * b.arg * ν_e - (2 * Real.pi / 3) * (‖b‖ - b.re) := hslope
      _ = crudeExponentEc ((Real.pi : ℂ) * ↑‖b‖ / 3 + (ν_e : ℂ) * Complex.I) b := hline_e.symm
      _ = crudeExponentEc ω_mid b := by rw [hω_mid_eq, hmb_c]
      _ ≤ crudeExponentEc ω_e b := hEc_mid
      _ ≤ (chartPhiV s b).re - c_γ * ρ * s.re ^ 2 := hEc_ωe
  refine ⟨lower_segs, hchainB, by simp [lower_segs], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    rcases List.mem_cons.mp hS with rfl | hS
    · dsimp [seg_dn_rayB, mkStripRaySeg, mkStripSeg]; linarith only [ht_hit_le_rho, hρ_le, hρ₀_delta, hδ_14, hρ₀_pos]
    rcases List.mem_cons.mp hS with rfl | hS; · dsimp [seg_cr1, mkCrudeAffineSeg]; norm_num
    rcases List.mem_cons.mp hS with rfl | hS; · dsimp [seg_cr2, mkCrudeAffineSeg]; norm_num
    rw [List.mem_singleton] at hS; subst hS; dsimp [seg_junc, mkStripAffineSeg, mkStripSeg]; norm_num
  · intro S hS t ht
    rcases List.mem_cons.mp hS with rfl | hS
    · have hvn : ‖s + (t : ℂ) * dir_mB‖ ≤ δ := by
        dsimp [seg_dn_rayB, mkStripRaySeg, mkStripSeg] at ht
        calc ‖s + (t : ℂ) * dir_mB‖ ≤ ‖s‖ + ‖(t : ℂ) * dir_mB‖ := norm_add_le _ _
          _ = ρ + t := by rw [hs_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1, hdirB_norm, mul_one]
          _ ≤ 2 * ρ := by linarith only [ht.2, ht_hit_le_rho]
          _ ≤ δ := by linarith only [hρ_le, hρ₀_delta, hρ₀_pos]
      have him := h_inner_om _ (h_dn_rayB_strip t ht).1 (h_dn_rayB_strip t ht).2 hvn
      refine ⟨him.1, him.2.1, him.2.2.1, ?_⟩
      change ‖deriv chartOmega (seg_dn_rayB.ζ t) * dir_mB‖ ≤ C_d
      rw [norm_mul, hdirB_norm, mul_one]
      exact him.2.2.2.trans hCom_le_Cd
    · rcases List.mem_cons.mp hS with rfl | hS
      · dsimp [seg_cr1, mkCrudeAffineSeg] at ht
        obtain ⟨hre_lb, _⟩ := hcr1_bd t ht
        have hre_nn : 0 ≤ (seg_cr1.ω t).re := hμ₀_pos.le.trans hre_lb
        have hcl_lb : c_Γ ≤ ‖seg_cr1.ω t‖ :=
          hc_Γ_le_mu0.trans (hre_lb.trans (Complex.re_le_norm _))
        have hre_ub : (seg_cr1.ω t).re ≤ 5 / 4 * muStar := by
          change (ω_e + (t : ℂ) * (ω_mid - ω_e)).re ≤ 5 / 4 * muStar
          simp [ω_mid]; nlinarith only [ht.1, ht.2, hμ_e_mem.2, hμ_b_mem.2]
        have him_ub : |(seg_cr1.ω t).im| ≤ muStar / 4 := by
          change |(ω_e + (t : ℂ) * (ω_mid - ω_e)).im| ≤ muStar / 4
          simp [ω_mid, ν_e]; exact hν_e_abs
        have hnorm_ub : ‖seg_cr1.ω t‖ ≤ C_Γ := by
          calc ‖seg_cr1.ω t‖ ≤ |(seg_cr1.ω t).re| + |(seg_cr1.ω t).im| := Complex.norm_le_abs_re_add_abs_im _
            _ ≤ 5 / 4 * muStar + muStar / 4 := add_le_add (by rw [abs_of_nonneg hre_nn]; exact hre_ub) him_ub
            _ = 3 / 2 * muStar := by ring
            _ ≤ C_Γ := hC_Γ_ge_32
        have hd_ub : ‖seg_cr1.ω' t‖ ≤ C_d := by
          change ‖ω_mid - ω_e‖ ≤ C_d
          have heq : ω_mid - ω_e = ((μ_b - μ_e : ℝ) : ℂ) := by
            apply Complex.ext
            · simp [ω_mid, μ_e]
            · simp [ω_mid, ν_e]
          rw [heq, Complex.norm_real, Real.norm_eq_abs]
          have hdiff_mu : |μ_b - μ_e| ≤ 2 * muStar := by
            rw [abs_le]; constructor <;> linarith only [hμ_e_mem.1, hμ_e_mem.2, hμ_b_mem.1, hμ_b_mem.2, hμ₀_pos]
          exact hdiff_mu.trans ((by linarith only [hCom_max_nn] : 2 * muStar ≤ C_om_max + 2 * muStar).trans hC_d_ge_2mu)
        exact ⟨hre_nn, hcl_lb, hnorm_ub, hd_ub⟩
      · rcases List.mem_cons.mp hS with rfl | hS
        · dsimp [seg_cr2, mkCrudeAffineSeg] at ht
          obtain ⟨hre_lb, _⟩ := hcr2_bd t ht
          have hre_nn : 0 ≤ (seg_cr2.ω t).re := hμ₀_pos.le.trans hre_lb
          have hcl_lb : c_Γ ≤ ‖seg_cr2.ω t‖ :=
            hc_Γ_le_mu0.trans (hre_lb.trans (Complex.re_le_norm _))
          have hωL_norm : ‖ω_L‖ ≤ C_om_max := by
            have hclL : ζ_L ∈ stripClosed := ⟨hxL_re.1, hxL_re.2.trans (by norm_num)⟩
            have himL : |ζ_L.im| ≤ T₀ := by simp [ζ_L, abs_of_nonneg (by linarith only [hT₀_ge4] : 0 ≤ T₀)]
            rw [hC_om_max_eq]
            calc ‖ω_L‖ ≤ C_om * (1 + ζ_L.im ^ 2) := hC_om ζ_L hclL
              _ ≤ C_om * (1 + T₀ ^ 2) :=
                  mul_le_mul_of_nonneg_left (add_le_add_right (by rw [← sq_abs ζ_L.im]; exact pow_le_pow_left₀ (abs_nonneg _) himL 2) 1) hC_om_pos.le
          have hYL_ub : |Y_L| ≤ C_om_max := (Complex.abs_im_le_norm ω_L).trans hωL_norm
          have hre_ub : (seg_cr2.ω t).re = μ_b := by
            change (ω_mid + (t : ℂ) * (ω_L - ω_mid)).re = μ_b; simp [ω_mid, ω_L, ζ_L, hOm_L_re]
          have him_ub : |(seg_cr2.ω t).im| ≤ C_om_max + muStar / 4 := by
            change |(ω_mid + (t : ℂ) * (ω_L - ω_mid)).im| ≤ C_om_max + muStar / 4
            have him_eq : (ω_mid + (t : ℂ) * (ω_L - ω_mid)).im = (1 - t) * ν_e + t * Y_L := by
              simp [ω_mid, Y_L]; ring
            rw [him_eq]
            calc |(1 - t) * ν_e + t * Y_L| ≤ (1 - t) * |ν_e| + t * |Y_L| := by
                  refine (abs_add_le _ _).trans ?_
                  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith only [ht.2]), abs_of_nonneg ht.1]
              _ ≤ (1 - t) * (muStar / 4) + t * C_om_max :=
                  add_le_add (mul_le_mul_of_nonneg_left hν_e_abs (by linarith only [ht.2]))
                    (mul_le_mul_of_nonneg_left hYL_ub ht.1)
              _ ≤ C_om_max + muStar / 4 := by nlinarith only [ht.1, ht.2, muStar_pos, hCom_max_nn]
          have hnorm_ub : ‖seg_cr2.ω t‖ ≤ C_Γ := by
            calc ‖seg_cr2.ω t‖ ≤ |(seg_cr2.ω t).re| + |(seg_cr2.ω t).im| := Complex.norm_le_abs_re_add_abs_im _
              _ ≤ 5 / 4 * muStar + (C_om_max + muStar / 4) := add_le_add (by rw [hre_ub, abs_of_nonneg (by linarith only [hμ_b_mem.1, hμ₀_pos])]; exact hμ_b_mem.2) him_ub
              _ ≤ 2 * muStar + C_om_max := by linarith only [muStar_pos]
              _ ≤ C_Γ := hC_Γ_ge_2om
          have hd_ub : ‖seg_cr2.ω' t‖ ≤ C_d := by
            change ‖ω_L - ω_mid‖ ≤ C_d
            have heq : ω_L - ω_mid = Complex.I * ((Y_L - ν_e : ℝ) : ℂ) := by
              apply Complex.ext <;> simp [ω_mid, ω_L, ζ_L, Y_L, hOm_L_re]
            rw [heq, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
            calc |Y_L - ν_e| ≤ |Y_L| + |ν_e| := abs_sub _ _
              _ ≤ C_om_max + muStar / 4 := add_le_add hYL_ub hν_e_abs
              _ ≤ C_om_max + 2 * muStar := by linarith only [muStar_pos]
              _ ≤ C_d := hC_d_ge_2mu
          exact ⟨hre_nn, hcl_lb, hnorm_ub, hd_ub⟩
        · rw [List.mem_singleton] at hS; subst hS
          have hstrip_t := seg_junc.hζ_strip rfl t ht
          dsimp [seg_junc, mkStripAffineSeg, mkStripSeg] at ht
          have hζ_eq : ∃ x ∈ Icc x_L (1 / 2), seg_junc.ζ t = (x : ℂ) - Complex.I * (T₀ : ℂ) := by
            refine ⟨x_L + t * (1 / 2 - x_L), ⟨by nlinarith only [ht.1, hxL_Ioo.2], by nlinarith only [ht.2, hxL_Ioo.2]⟩, ?_⟩
            change ζ_L + (t : ℂ) * (((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)) - ζ_L) = _
            dsimp [ζ_L]; push_cast; ring
          rcases hζ_eq with ⟨x, hx_Icc, hζx⟩
          have hx_012 : 0 ≤ x ∧ x ≤ 1 / 2 := ⟨hxL_Ioo.1.le.trans hx_Icc.1, hx_Icc.2⟩
          have hcl : seg_junc.ζ t ∈ stripClosed := ⟨hstrip_t.1, hstrip_t.2.1.trans (by norm_num)⟩
          have hre_nn : 0 ≤ (seg_junc.ω t).re := by
            rw [hstrip_t.2.2.1]; exact lemma_J7Q.2 _ hstrip_t.1 hstrip_t.2.1
          have hDiff : ‖chartOmega ((x : ℂ) - Complex.I * (T₀ : ℂ)) -
              chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ))‖ ≤ 2 * C_om' * C_L := by
            have hd := chartOmega_horiz_diff_le hC_om' (T₀ := T₀) hx_012.1 hx_012.2
            rw [abs_of_nonneg (by linarith only [hT₀_ge4])] at hd
            have hx_w : 1 / 2 - x ≤ C_L / T₀ := by linarith only [hx_Icc.1, hxL_diff]
            have hC_nn : 0 ≤ C_om' := hC_om'_pos.le
            have hCL_nn : 0 ≤ C_L := by
              have hmul := mul_le_mul_of_nonneg_right hxL_diff (by linarith only [hT₀_ge4] : 0 ≤ T₀)
              rw [div_mul_cancel₀ _ (by linarith only [hT₀_ge4])] at hmul
              nlinarith only [hmul, hxL_Ioo.2, hT₀_ge4]
            have hT_2 : (1 + T₀) / T₀ ≤ 2 := by
              rw [div_le_iff₀ (by linarith only [hT₀_ge4])]; linarith only [hT₀_ge4]
            calc ‖chartOmega ((x : ℂ) - Complex.I * (T₀ : ℂ)) -
                  chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ))‖
                ≤ C_om' * (1 + T₀) * (1 / 2 - x) := hd
              _ ≤ C_om' * (1 + T₀) * (C_L / T₀) := mul_le_mul_of_nonneg_left hx_w (by positivity)
              _ = C_om' * C_L * ((1 + T₀) / T₀) := by ring
              _ ≤ C_om' * C_L * 2 := mul_le_mul_of_nonneg_left hT_2 (mul_nonneg hC_nn hCL_nn)
              _ = 2 * C_om' * C_L := by ring
          have hmid_T0 : c_mid * T₀ ^ 2 ≤ ‖chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ))‖ := by
            have hconj := chartOmega_conj (ζ := (1 / 2 : ℂ) + Complex.I * (T₀ : ℂ))
              (by norm_num) (by norm_num)
            have heq : starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ)) = (1 / 2 : ℂ) - Complex.I * (T₀ : ℂ) := by
              apply Complex.ext <;> simp
            rw [heq] at hconj
            have hnorm_eq : ‖chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ))‖ =
                ‖chartOmega ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ))‖ := by
              rw [hconj, Complex.norm_conj]
            exact (h_mid_lb T₀).trans_eq hnorm_eq.symm
          have hnorm_lb : c_Γ ≤ ‖seg_junc.ω t‖ := by
            have htri := norm_sub_norm_le (chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)))
              (chartOmega ((x : ℂ) - Complex.I * (T₀ : ℂ)))
            rw [norm_sub_rev] at htri
            have h1 : 1 ≤ ‖chartOmega ((x : ℂ) - Complex.I * (T₀ : ℂ))‖ := by linarith only [htri, hmid_T0, hDiff, hT₀_mid_sq]
            rw [hstrip_t.2.2.1, hζx]
            exact hc_Γ_le_1.trans h1
          have hnorm_ub : ‖seg_junc.ω t‖ ≤ C_Γ := by
            rw [hstrip_t.2.2.1, hζx]
            have himL : |((x : ℂ) - Complex.I * (T₀ : ℂ)).im| = T₀ := by
              simp [abs_of_nonneg (by linarith only [hT₀_ge4] : 0 ≤ T₀)]
            calc ‖chartOmega ((x : ℂ) - Complex.I * (T₀ : ℂ))‖
                ≤ C_om * (1 + ((x : ℂ) - Complex.I * (T₀ : ℂ)).im ^ 2) := hC_om _ (hζx ▸ hcl)
              _ = C_om * (1 + T₀ ^ 2) := by simp
              _ = C_om_max := hC_om_max_eq.symm
              _ ≤ C_Γ := hC_Γ_ge_om
          have hω'_ub : ‖seg_junc.ω' t‖ ≤ C_d := by
            rw [hstrip_t.2.2.2.2.2, norm_mul]
            have hd1 : ‖deriv chartOmega (seg_junc.ζ t)‖ ≤ C_om'_max := by
              rw [hζx, hC_om'_max_eq]
              have hcl' : (x : ℂ) - Complex.I * (T₀ : ℂ) ∈ stripClosed := hζx ▸ hcl
              have h_im : |((x : ℂ) - Complex.I * (T₀ : ℂ)).im| = T₀ := by
                simp [abs_of_nonneg (by linarith only [hT₀_ge4] : 0 ≤ T₀)]
              calc ‖deriv chartOmega ((x : ℂ) - Complex.I * (T₀ : ℂ))‖
                  ≤ C_om' * (1 + |((x : ℂ) - Complex.I * (T₀ : ℂ)).im|) := hC_om' _ hcl'
                _ = C_om' * (1 + T₀) := by rw [h_im]
            have hd2 : ‖seg_junc.ζ' t‖ ≤ 1 := by
              change ‖((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)) - ζ_L‖ ≤ 1
              have : ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)) - ζ_L = ((1 / 2 - x_L : ℝ) : ℂ) := by
                dsimp [ζ_L]; push_cast; ring
              rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith only [hxL_Ioo.2])]
              linarith only [hxL_Ioo.1]
            calc ‖deriv chartOmega (seg_junc.ζ t)‖ * ‖seg_junc.ζ' t‖
                ≤ C_om'_max * 1 := mul_le_mul hd1 hd2 (norm_nonneg _) hCom'_max_nn
              _ ≤ C_om'_max * (T₀ + 2 + 2 * Real.pi) :=
                  mul_le_mul_of_nonneg_left (by linarith only [Real.pi_pos, hT₀_ge4]) hCom'_max_nn
              _ ≤ C_d := hC_d_ge_om
          exact ⟨hre_nn, hnorm_lb, hnorm_ub, hω'_ub⟩
  · intro S hS hstr t ht
    rcases List.mem_cons.mp hS with rfl | hS
    · refine ⟨?_, (h_dn_rayB_bd t ht).trans (sub_le_self _ (by positivity))⟩
      change ‖dir_mB‖ ≤ C_d; rw [hdirB_norm]
      exact hT0_pi_gt1.trans hC_d_ge_T0
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_cr1, mkCrudeAffineSeg] at hstr
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_cr2, mkCrudeAffineSeg] at hstr
    rw [List.mem_singleton] at hS; subst hS
    dsimp [seg_junc, mkStripAffineSeg, mkStripSeg] at ht
    have hζ_eq : ∃ x ∈ Icc x_L (1 / 2), seg_junc.ζ t = (x : ℂ) - Complex.I * (T₀ : ℂ) := by
      refine ⟨x_L + t * (1 / 2 - x_L), ⟨by nlinarith only [ht.1, hxL_Ioo.2], by nlinarith only [ht.2, hxL_Ioo.2]⟩, ?_⟩
      change ζ_L + (t : ℂ) * (((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)) - ζ_L) = _
      dsimp [ζ_L]; push_cast; ring
    rcases hζ_eq with ⟨x, hx_Icc, hζx⟩
    have hJ_x : j10H (seg_junc.ζ t) ≤ -4 * κ_strip := by
      rw [hζx]; exact (hxL_H x hx_Icc).trans hκ_strip_j7
    have hstrip_t := seg_junc.hζ_strip rfl t ht
    have him_ub : |(seg_junc.ζ t).im| ≤ T₀ := by
      rw [hζx]; simp [abs_of_nonneg (by linarith only [hT₀_ge4] : 0 ≤ T₀)]
    have hdz_ub : ‖seg_junc.ζ' t‖ ≤ C_d := by
      change ‖((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)) - ζ_L‖ ≤ C_d
      have : ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)) - ζ_L = ((1 / 2 - x_L : ℝ) : ℂ) := by
        dsimp [ζ_L]; push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith only [hxL_Ioo.2])]
      exact (by linarith only [hxL_Ioo.1, Real.pi_pos, hT₀_ge4] : 1 / 2 - x_L ≤ T₀ + 2 * Real.pi + 2).trans hC_d_ge_T0
    exact ⟨hdz_ub, (h_fixed_strip_H _ hstrip_t.1 hstrip_t.2.1 him_ub hJ_x).trans (by linarith only [hκ_strip_pos])⟩
  · intro S hS hstr hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_rayB, mkStripRaySeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_cr1, mkCrudeAffineSeg] at hstr
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_cr2, mkCrudeAffineSeg] at hstr
    rw [List.mem_singleton] at hS; subst hS; simp [seg_junc, mkStripAffineSeg, mkStripSeg] at hkind
  · intro S hS _ hkind
    rcases List.mem_cons.mp hS with rfl | hS
    · refine ⟨t_hit, ht_hit_nn, rfl, rfl, ht_hit_le_rho.trans (by linarith only [hρ_nn]), fun t ht => ?_⟩
      refine ⟨?_, ?_, h_dn_rayB_bd t ht⟩
      · change ‖s + (t : ℂ) * dir_mB - s‖ = t
        rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1, hdirB_norm, mul_one]
      · change ‖dir_mB‖ = 1; exact hdirB_norm
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_cr1, mkCrudeAffineSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_cr2, mkCrudeAffineSeg] at hkind
    rw [List.mem_singleton] at hS; subst hS; simp [seg_junc, mkStripAffineSeg, mkStripSeg] at hkind
  · intro S hS hstr hkind t ht
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_rayB, mkStripRaySeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_cr1, mkCrudeAffineSeg] at hstr
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_cr2, mkCrudeAffineSeg] at hstr
    rw [List.mem_singleton] at hS; subst hS; simp [seg_junc, mkStripAffineSeg, mkStripSeg] at hkind
  · intro S hS hstr hkind t ht
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_rayB, mkStripRaySeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_cr1, mkCrudeAffineSeg] at hstr
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_cr2, mkCrudeAffineSeg] at hstr
    rw [List.mem_singleton] at hS; subst hS
    dsimp [seg_junc, mkStripAffineSeg, mkStripSeg] at ht
    have hζ_eq : ∃ x ∈ Icc x_L (1 / 2), seg_junc.ζ t = (x : ℂ) - Complex.I * (T₀ : ℂ) := by
      refine ⟨x_L + t * (1 / 2 - x_L), ⟨by nlinarith only [ht.1, hxL_Ioo.2], by nlinarith only [ht.2, hxL_Ioo.2]⟩, ?_⟩
      change ζ_L + (t : ℂ) * (((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)) - ζ_L) = _
      dsimp [ζ_L]; push_cast; ring
    rcases hζ_eq with ⟨x, hx_Icc, hζx⟩
    have hJ_x : j10H (seg_junc.ζ t) ≤ -4 * κ_strip := by
      rw [hζx]; exact (hxL_H x hx_Icc).trans hκ_strip_j7
    have hstrip_t := seg_junc.hζ_strip rfl t ht
    have him_ub : |(seg_junc.ζ t).im| ≤ T₀ := by
      rw [hζx]; simp [abs_of_nonneg (by linarith only [hT₀_ge4] : 0 ≤ T₀)]
    exact h_fixed_strip_H _ hstrip_t.1 hstrip_t.2.1 him_ub hJ_x
  · intro S hS hfalse t ht
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_rayB, mkStripRaySeg, mkStripSeg] at hfalse
    rcases List.mem_cons.mp hS with rfl | hS; · exact hcr1_bd t ht
    rcases List.mem_cons.mp hS with rfl | hS; · exact hcr2_bd t ht
    rw [List.mem_singleton] at hS; subst hS; simp [seg_junc, mkStripAffineSeg, mkStripSeg] at hfalse
  · intro S hS hstr hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_dn_rayB, mkStripRaySeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_cr1, mkCrudeAffineSeg] at hstr
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_cr2, mkCrudeAffineSeg] at hstr
    rw [List.mem_singleton] at hS; subst hS; simp [seg_junc, mkStripAffineSeg, mkStripSeg] at hkind

private lemma zp_upper_case {η : ℂ → ℂ → ℂ} {ρ_F C_F C_om C_om' : ℝ}
    (hCF_nn : 0 ≤ C_F)
    (hη_an : AnalyticOnNhd ℂ (Function.uncurry η) (ball (0 : ℂ × ℂ) ρ_F))
    (hF_id : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      2 * Complex.log (chartB w / chartB s) * deriv chartOmega w =
        ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (w ^ 2 - s ^ 2) * (1 + η w s))
    (hη_bd : ∀ w ∈ ball (0 : ℂ) ρ_F, ∀ s ∈ ball (0 : ℂ) ρ_F,
      ‖η w s‖ ≤ C_F * (‖w‖ + ‖s‖))
    (hρF_pos : 0 < ρ_F)
    (hC_om_pos : 0 < C_om)
    (hC_om : ∀ ζ ∈ stripClosed, ‖chartOmega ζ‖ ≤ C_om * (1 + ζ.im ^ 2))
    (hC_om'_pos : 0 < C_om')
    (hC_om' : ∀ ζ ∈ stripClosed, ‖deriv chartOmega ζ‖ ≤ C_om' * (1 + |ζ.im|))
    {δ T₀ κ_strip ρ₀ c_Γ C_Γ C_d c_γ κ_arc C_om_max C_om'_max ε_J10 c_J10 ρ φ' : ℝ}
    (hδ_pos : 0 < δ) (hδ_14 : δ ≤ 1 / 4) (hδ_rhoF : δ < min ρ_F (1 / 2))
    (hCF_delta : C_F * δ ≤ 1 / 80)
    (hT₀_ge4 : 4 ≤ T₀) (hκ_strip_pos : 0 < κ_strip)
    (hρ₀_pos : 0 < ρ₀) (hρ₀_delta : 12 * ρ₀ ≤ δ) (hρ₀_arc : 4000 * C_F * ρ₀ ≤ 1)
    (hC_om_max_eq : C_om_max = C_om * (1 + T₀ ^ 2))
    (hC_om'_max_eq : C_om'_max = C_om' * (1 + T₀))
    (hCom'_max_nn : 0 ≤ C_om'_max)
    (hC_Γ_ge_om : C_om_max ≤ C_Γ) (hc_Γ_le_j10 : c_Γ ≤ c_J10)
    (hC_d_ge_om : C_om'_max * (T₀ + 2 + 2 * Real.pi) ≤ C_d)
    (hC_d_ge_T0 : T₀ + 2 * Real.pi + 2 ≤ C_d)
    (hT0_pi_gt1 : (1 : ℝ) ≤ T₀ + 2 * Real.pi + 2)
    (hCom_pi_le_Cd : (3 / 2 : ℝ) * C_om' * (2 * Real.pi) ≤ C_d)
    (hCom_le_Cd : (3 / 2 : ℝ) * C_om' ≤ C_d)
    (hκ_strip_j10 : -ε_J10 ≤ -4 * κ_strip)
    (hc_γ_pos : 0 < c_γ)
    (hcγ_le_pi4 : c_γ ≤ Real.pi ^ 2 / 24)
    (hκ_arc_eq : κ_arc = 10 * Real.pi ^ 2)
    (hρ_nn : 0 ≤ ρ) (hρ_le : ρ ≤ ρ₀) (hφ_nn : 0 ≤ φ') (hφ_le : φ' ≤ Real.pi / 2)
    {s b : ℂ}
    (hs_eq : s = (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 - φ' : ℝ) : ℂ)))
    (hb_eq : b = chartB s) (hb_re_pos : 0 < b.re)
    (hradial_eta : C_F * (5 / 4 * δ) * (1 + 1 / 16) ≤ 1 / 4)
    (h_inner_om : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 / 2 → ‖w‖ ≤ δ →
      0 ≤ (chartOmega w).re ∧ c_Γ ≤ ‖chartOmega w‖ ∧ ‖chartOmega w‖ ≤ C_Γ ∧
      ‖deriv chartOmega w‖ ≤ (3 / 2 : ℝ) * C_om')
    (h_fixed_strip_H : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 / 2 → |ζ.im| ≤ T₀ →
      j10H ζ ≤ -4 * κ_strip →
      (chartPhiV ζ b).re ≤ (chartPhiV s b).re - κ_strip)
    (hJ10_pts : ∀ u ∈ Icc (0 : ℝ) 3,
      let z := j10GammaPlus δ T₀ u
      let zm := j10GammaMinus δ T₀ u
      0 ≤ z.re ∧ z.re ≤ 1 / 2 ∧ 0 ≤ z.im ∧
      0 ≤ zm.re ∧ zm.re ≤ 1 / 2 ∧ zm.im ≤ 0 ∧
      j10H z ≤ j10H (j10P δ) ∧ j10H z ≤ -ε_J10 ∧
      j10H zm ≤ j10H (j10P δ) ∧ j10H zm ≤ -ε_J10 ∧
      0 ≤ (chartOmega z).re ∧ 0 ≤ (chartOmega zm).re)
    (hJ10_om_lb : ∀ u ∈ Icc (0 : ℝ) 3,
      c_J10 ≤ ‖chartOmega (j10GammaPlus δ T₀ u)‖ ∧
      c_J10 ≤ ‖chartOmega (j10GammaMinus δ T₀ u)‖)
    {P₀ P₁ P₂ P₃ : ℂ}
    (hP0_def : P₀ = j10P δ)
    (hP1_def : P₁ = (j10YDelta δ : ℂ) * (1 + Complex.I))
    (hP2_def : P₂ = (1 / 2 : ℂ) * (1 + Complex.I))
    (hP3_def : P₃ = (1 / 2 : ℂ) + Complex.I * (T₀ : ℂ))
    (hP0_re : 0 ≤ P₀.re ∧ P₀.re ≤ 1 / 2)
    (hP1_re : 0 ≤ P₁.re ∧ P₁.re ≤ 1 / 2)
    (hP2_re : 0 ≤ P₂.re ∧ P₂.re ≤ 1 / 2)
    (hP3_re : 0 ≤ P₃.re ∧ P₃.re ≤ 1 / 2) :
    ∃ upper_segs : List ContourSeg,
      ContourChained (chartOmega P₃) (chartOmega s) upper_segs ∧
      upper_segs.length ≤ 6 ∧
      (∀ S ∈ upper_segs, S.b - S.a ≤ 1) ∧
      (∀ S ∈ upper_segs, ∀ t ∈ Icc S.a S.b,
        0 ≤ (S.ω t).re ∧ c_Γ ≤ ‖S.ω t‖ ∧ ‖S.ω t‖ ≤ C_Γ ∧ ‖S.ω' t‖ ≤ C_d) ∧
      (∀ S ∈ upper_segs, S.isStrip = true → ∀ t ∈ Icc S.a S.b,
        ‖S.ζ' t‖ ≤ C_d ∧ (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re) ∧
      (∀ S ∈ upper_segs, S.isStrip = true → S.kind = .upperRay →
        ∃ t_max ≥ (0 : ℝ), S.a = 0 ∧ S.b = t_max ∧ t_max ≤ 11 * ρ ∧
          ∀ t ∈ Icc 0 t_max, ‖S.ζ t - s‖ = t_max - t ∧ ‖S.ζ' t‖ = 1 ∧
            (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - c_γ * ρ * (t_max - t) ^ 2) ∧
      (∀ S ∈ upper_segs, S.isStrip = true → S.kind ≠ .lowerRay) ∧
      (∀ S ∈ upper_segs, S.isStrip = true → S.kind = .arcRadial →
        ∀ t ∈ Icc S.a S.b, (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - κ_arc * ρ ^ 3) ∧
      (∀ S ∈ upper_segs, S.isStrip = true → S.kind = .fixedStrip →
        ∀ t ∈ Icc S.a S.b, (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - κ_strip) ∧
      (∀ S ∈ upper_segs, S.isStrip ≠ false) ∧
      (∀ S ∈ upper_segs, S.isStrip = true → S.kind ≠ .crudeEdge) := by
  subst hP0_def hP1_def hP2_def hP3_def
  have hs_norm : ‖s‖ = ρ := by
    rw [hs_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ_nn, exp_ofReal_mul_I_norm', mul_one]
  have hs_re_nn : 0 ≤ s.re := by
    rw [hs_eq, Complex.re_ofReal_mul, exp_ofReal_mul_I_re'']
    exact mul_nonneg hρ_nn (Real.cos_nonneg_of_mem_Icc ⟨by linarith only [Real.pi_pos, hφ_le], by linarith only [Real.pi_pos, hφ_nn]⟩)
  have h12ρ_δ : 12 * ρ ≤ δ := by linarith only [hρ_le, hρ₀_delta]
  have hρ_lt_δ : ρ < δ := by linarith only [hρ_le, hρ₀_delta, hρ₀_pos]
  have hs_F : s ∈ ball (0 : ℂ) ρ_F :=
    mem_ball_zero_iff.mpr (hs_norm.symm ▸ lt_trans hρ_lt_δ (lt_of_lt_of_le hδ_rhoF (min_le_left _ _)))
  let P₀ : ℂ := j10P δ
  let P₁ : ℂ := (j10YDelta δ : ℂ) * (1 + Complex.I)
  let P₂ : ℂ := (1 / 2 : ℂ) * (1 + Complex.I)
  let P₃ : ℂ := (1 / 2 : ℂ) + Complex.I * (T₀ : ℂ)
  let seg_up32 := mkStripAffineSeg .fixedStrip P₃ P₂ hP3_re hP2_re
  let seg_up21 := mkStripAffineSeg .fixedStrip P₂ P₁ hP2_re hP1_re
  let seg_up10 := mkStripAffineSeg .fixedStrip P₁ P₀ hP1_re hP0_re
  have hj10_seg_mem : ∀ S ∈ [seg_up32, seg_up21, seg_up10], ∀ t ∈ Icc S.a S.b,
      ∃ u ∈ Icc (0 : ℝ) 3, S.ζ t = j10GammaPlus δ T₀ u := fun S hS t ht => by
    rcases List.mem_cons.mp hS with rfl | hS
    · have ht01 : 0 ≤ t ∧ t ≤ 1 := ht
      refine ⟨3 - t, ⟨by linarith only [ht01.2], by linarith only [ht01.1]⟩, ?_⟩
      change P₃ + (t : ℂ) * (P₂ - P₃) = j10GammaPlus δ T₀ (3 - t)
      by_cases ht1 : t = 1
      · subst ht1; norm_num [P₂, P₃, j10GammaPlus]
      · have hgt2 : ¬ (3 - t ≤ 2) := by
          have : t < 1 := lt_of_le_of_ne ht01.2 ht1; linarith only [this]
        have hgt1 : ¬ (3 - t ≤ 1) := by linarith only [ht01.2]
        simp only [j10GammaPlus, hgt1, hgt2, ↓reduceIte, P₂, P₃]; push_cast; ring
    · rcases List.mem_cons.mp hS with rfl | hS
      · have ht01 : 0 ≤ t ∧ t ≤ 1 := ht
        refine ⟨2 - t, ⟨by linarith only [ht01.2], by linarith only [ht01.1]⟩, ?_⟩
        change P₂ + (t : ℂ) * (P₁ - P₂) = j10GammaPlus δ T₀ (2 - t)
        by_cases ht1 : t = 1
        · subst ht1; norm_num [P₁, P₂, j10GammaPlus]
        · have hgt1 : ¬ (2 - t ≤ 1) := by
            have : t < 1 := lt_of_le_of_ne ht01.2 ht1; linarith only [this]
          have hle2 : 2 - t ≤ 2 := by linarith only [ht01.1]
          simp only [j10GammaPlus, hgt1, hle2, ↓reduceIte, P₁, P₂]; push_cast; ring
      · rw [List.mem_singleton] at hS; subst hS
        have ht01 : 0 ≤ t ∧ t ≤ 1 := ht
        refine ⟨1 - t, ⟨by linarith only [ht01.2], by linarith only [ht01.1]⟩, ?_⟩
        change P₁ + (t : ℂ) * (P₀ - P₁) = j10GammaPlus δ T₀ (1 - t)
        have hle1 : 1 - t ≤ 1 := by linarith only [ht01.1]
        simp only [j10GammaPlus, hle1, ↓reduceIte, P₀, P₁]; push_cast; ring
  have hP0_im : |P₀.im| ≤ T₀ := by
    have : ‖P₀‖ = δ := by
      dsimp [P₀, j10P]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ_pos.le,
        exp_ofReal_mul_I_norm', mul_one]
    exact (Complex.abs_im_le_norm P₀).trans (by rw [this]; linarith only [hδ_14, hT₀_ge4])
  have hP1_im : |P₁.im| ≤ T₀ := by
    have hP1_im_eq : P₁.im = j10YDelta δ := by simp [P₁]
    have h1 : j10YDelta δ ≤ δ := by
      unfold j10YDelta
      have hsq3 : √3 ≤ 2 := by rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]; exact Real.sqrt_le_sqrt (by norm_num)
      nlinarith only [hsq3, hδ_pos]
    rw [hP1_im_eq, abs_of_nonneg (by unfold j10YDelta; positivity [hδ_pos])]
    linarith only [h1, hδ_14, hT₀_ge4]
  have hP2_im : |P₂.im| ≤ T₀ := by
    have : P₂.im = 1 / 2 := by simp [P₂]
    rw [this, abs_of_nonneg (by norm_num)]; linarith only [hT₀_ge4]
  have hP3_im : |P₃.im| ≤ T₀ := by
    have : P₃.im = T₀ := by simp [P₃]
    rw [this, abs_of_nonneg (by linarith only [hT₀_ge4])]
  have h_up_dz : ∀ S ∈ [seg_up32, seg_up21, seg_up10], ∀ t ∈ Icc S.a S.b, ‖S.ζ' t‖ ≤ T₀ + 2 := by
    intro S hS t _
    rcases List.mem_cons.mp hS with rfl | hS
    · change ‖P₂ - P₃‖ ≤ T₀ + 2
      have hP23 : P₂ - P₃ = -Complex.I * ((T₀ - 1 / 2 : ℝ) : ℂ) := by dsimp [P₂, P₃]; push_cast; ring
      rw [hP23, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (by linarith only [hT₀_ge4])]
      linarith only [hT₀_ge4]
    · rcases List.mem_cons.mp hS with rfl | hS
      · change ‖P₁ - P₂‖ ≤ T₀ + 2
        have hP12 : P₁ - P₂ = ((j10YDelta δ - 1 / 2 : ℝ) : ℂ) * (1 + Complex.I) := by
          dsimp [P₁, P₂]; push_cast; ring
        have hnorm1I : ‖(1 : ℂ) + Complex.I‖ ≤ 2 := by
          calc ‖(1 : ℂ) + Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
            _ = 2 := by simp; norm_num
        have hyd : |j10YDelta δ - 1 / 2| ≤ 1 / 2 := by
          unfold j10YDelta
          have hsq3 : √3 ≤ 2 := by rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]; exact Real.sqrt_le_sqrt (by norm_num)
          have h0 : 0 ≤ √3 * δ / 2 := by positivity
          have h1 : √3 * δ / 2 ≤ δ := by nlinarith only [hsq3, hδ_pos]
          rw [abs_le]; constructor <;> linarith only [h0, h1, hδ_14]
        rw [hP12, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc |j10YDelta δ - 1 / 2| * ‖(1 : ℂ) + Complex.I‖ ≤ (1 / 2) * 2 :=
              mul_le_mul hyd hnorm1I (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
          _ ≤ T₀ + 2 := by linarith only [hT₀_ge4]
      · rw [List.mem_singleton] at hS; subst hS
        change ‖P₀ - P₁‖ ≤ T₀ + 2
        have hP0_n : ‖P₀‖ = δ := by
          dsimp [P₀, j10P]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ_pos.le, exp_ofReal_mul_I_norm', mul_one]
        have hP1_n : ‖P₁‖ ≤ 2 * δ := by
          dsimp [P₁]; rw [norm_mul, Complex.norm_real]
          have hsq3 : √3 ≤ 2 := by rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]; exact Real.sqrt_le_sqrt (by norm_num)
          have hyd : |j10YDelta δ| ≤ δ := by
            unfold j10YDelta; rw [abs_of_nonneg (by positivity [hδ_pos])]
            nlinarith only [hsq3, hδ_pos]
          have h1I : ‖(1 : ℂ) + Complex.I‖ ≤ 2 := by
            calc ‖(1 : ℂ) + Complex.I‖ ≤ 1 + 1 := (norm_add_le 1 Complex.I).trans_eq (by simp)
              _ = 2 := by norm_num
          exact (mul_le_mul hyd h1I (norm_nonneg _) hδ_pos.le).trans (by ring_nf; rfl)
        calc ‖P₀ - P₁‖ ≤ ‖P₀‖ + ‖P₁‖ := norm_sub_le _ _
          _ ≤ δ + 2 * δ := add_le_add hP0_n.le hP1_n
          _ ≤ T₀ + 2 := by linarith only [hδ_14, hT₀_ge4]
  let dir_plus : ℂ := Complex.exp (Complex.I * ((Real.pi / 3 : ℝ) : ℂ))
  have hdir_plus_re : dir_plus.re = 1 / 2 := by
    dsimp [dir_plus]; rw [exp_ofReal_mul_I_re'', Real.cos_pi_div_three]
  have hdir_plus_norm : ‖dir_plus‖ = 1 := exp_ofReal_mul_I_norm' _
  have hrad_re : 0 ≤ ((10 * ρ : ℂ) * dir_plus).re ∧ ((10 * ρ : ℂ) * dir_plus).re ≤ 1 / 2 := by
    rw [show (10 * (ρ : ℂ)) * dir_plus = ((10 * ρ : ℝ) : ℂ) * dir_plus by push_cast; ring,
      Complex.re_ofReal_mul, hdir_plus_re]
    exact ⟨by linarith only [hρ_nn], by nlinarith only [hρ_le, hρ₀_delta, hδ_14]⟩
  let seg_up_rad := mkStripAffineSeg .arcRadial P₀ ((10 * ρ : ℂ) * dir_plus) hP0_re hrad_re
  have hex_plus := zp_upper_ray_arc hCF_nn hη_an hF_id hη_bd hρF_pos hδ_pos hδ_14 hδ_rhoF hCF_delta
    hρ₀_pos hρ₀_delta hρ₀_arc hρ_nn hρ_le hφ_nn hφ_le hcγ_le_pi4 hκ_arc_eq hs_eq hb_eq hb_re_pos
  rcases hex_plus with ⟨t_plus, θ_plus, ht_plus_mem, hθ_plus_mem, hw_plus_polar, h_up_ray_bd, h_up_arc_bd⟩
  have h_up_ray_strip : ∀ v ∈ Icc (0 : ℝ) t_plus,
      0 ≤ (s + (v : ℂ) * dir_plus).re ∧ (s + (v : ℂ) * dir_plus).re ≤ 1 / 2 := fun v hv => by
    have hvd : ((v : ℂ) * dir_plus).re = v / 2 := by rw [Complex.re_ofReal_mul, hdir_plus_re]; ring
    have hnorm_v : ‖s + (v : ℂ) * dir_plus‖ ≤ δ := by
      calc ‖s + (v : ℂ) * dir_plus‖ ≤ ‖s‖ + ‖(v : ℂ) * dir_plus‖ := norm_add_le _ _
        _ = ρ + v := by rw [hs_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hv.1, hdir_plus_norm, mul_one]
        _ ≤ 12 * ρ := by linarith only [hv.2, ht_plus_mem.2]
        _ ≤ δ := h12ρ_δ
    exact ⟨by rw [Complex.add_re, hvd]; linarith only [hs_re_nn, hv.1],
      (Complex.re_le_norm _).trans (hnorm_v.trans (hδ_14.trans (by norm_num)))⟩
  have h_up_arc_strip : ∀ α ∈ uIcc (Real.pi / 3) θ_plus,
      0 ≤ (((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (α : ℂ))).re ∧
      (((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (α : ℂ))).re ≤ 1 / 2 := fun α hα => by
    have hα_mem : α ∈ Icc 0 (Real.pi / 2) := by
      rw [Set.mem_uIcc] at hα
      rcases hα with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨(by positivity [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 3).trans h1, h2.trans hθ_plus_mem.2⟩
      · exact ⟨hθ_plus_mem.1.trans h1, h2.trans (by linarith only [Real.pi_pos])⟩
    rw [Complex.re_ofReal_mul, exp_ofReal_mul_I_re'']
    refine ⟨mul_nonneg (by positivity [hρ_nn]) (Real.cos_nonneg_of_mem_Icc ⟨by linarith only [hα_mem.1, Real.pi_pos], hα_mem.2⟩), ?_⟩
    calc 10 * ρ * Real.cos α ≤ 10 * ρ * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one α) (by positivity [hρ_nn])
      _ ≤ 12 * ρ₀ := by linarith only [hρ_nn, hρ_le]
      _ ≤ 1 / 2 := hρ₀_delta.trans (hδ_14.trans (by norm_num))
  let seg_up_arc := mkStripArcSeg (10 * ρ) (Real.pi / 3) θ_plus h_up_arc_strip
  let seg_up_ray := mkStripRevRaySeg .upperRay s dir_plus t_plus (by linarith only [ht_plus_mem.1, hρ_nn]) h_up_ray_strip
  have h_up_rad_bd : ∀ t ∈ Icc (0 : ℝ) 1,
      (chartPhiV (seg_up_rad.ζ t) b).re ≤ (chartPhiV s b).re - κ_arc * ρ ^ 3 := fun t ht => by
    let r_t : ℝ := (1 - t) * δ + t * (10 * ρ)
    have hζ_eq : seg_up_rad.ζ t = (r_t : ℂ) * dir_plus := by
      dsimp [seg_up_rad, mkStripAffineSeg, mkStripSeg, P₀, j10P, dir_plus, r_t]; push_cast; ring
    rw [hζ_eq]
    have h10ρ_δ : 10 * ρ ≤ δ := by linarith only [hρ_nn, h12ρ_δ]
    have hr_mem : r_t ∈ Icc (10 * ρ) δ :=
      ⟨by nlinarith only [ht.1, ht.2, h10ρ_δ], by nlinarith only [ht.1, ht.2, h10ρ_δ]⟩
    rcases eq_or_lt_of_le hρ_nn with rfl | hρ_pos
    · have hs0 : s = 0 := by simp [hs_eq]
      have hb0 : b = (xiStar : ℂ) := by rw [hb_eq, hs0, chartB_zero]
      have hr0 : r_t ∈ Icc (0 : ℝ) δ := ⟨by nlinarith only [ht.1, ht.2, hδ_pos], hr_mem.2⟩
      have hrad := radial_H_le_zero_limit (δ := δ) hCF_nn hη_an hF_id hη_bd (Or.inl rfl)
        hδ_pos hδ_rhoF hradial_eta r_t hr0
      rw [hs0, hb0]
      simpa [dir_plus] using hrad
    · have hanti := radial_H_antitone hCF_nn hη_an hF_id hη_bd hb_re_pos hb_eq hs_F
        (Or.inl rfl) (by positivity) h10ρ_δ hδ_rhoF
        (by rw [hs_norm]; linarith only [hρ_pos]) hradial_eta
      have hle_end := hanti ⟨le_rfl, h10ρ_δ⟩ hr_mem hr_mem.1
      have harc_end := h_up_arc_bd (Real.pi / 3) Set.left_mem_uIcc
      have heq1 : (((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * ((1 * Real.pi / 3 : ℝ) : ℂ))) =
          ((10 * ρ : ℝ) : ℂ) * Complex.exp (Complex.I * ((Real.pi / 3 : ℝ) : ℂ)) := by
        congr 2; push_cast; ring
      have heq2 : (r_t : ℂ) * Complex.exp (Complex.I * ((1 * Real.pi / 3 : ℝ) : ℂ)) = (r_t : ℂ) * dir_plus := by
        dsimp [dir_plus]; congr 2; push_cast; ring
      dsimp only at hle_end
      rw [heq2, heq1] at hle_end
      exact hle_end.trans harc_end
  let upper_segs : List ContourSeg := [seg_up32, seg_up21, seg_up10, seg_up_rad, seg_up_arc, seg_up_ray]
  have hchain_up : ContourChained (chartOmega P₃) (chartOmega s) upper_segs := by
    have hw0 : seg_up32.ω 0 = chartOmega P₃ := by
      dsimp [seg_up32, mkStripAffineSeg, mkStripSeg, P₃]; simp
    have hw1 : seg_up21.ω 0 = seg_up32.ω 1 := by
      dsimp [seg_up21, seg_up32, mkStripAffineSeg, mkStripSeg, P₂, P₃]; simp
    have hw2 : seg_up10.ω 0 = seg_up21.ω 1 := by
      dsimp [seg_up10, seg_up21, mkStripAffineSeg, mkStripSeg, P₁, P₂]; simp
    have hw3 : seg_up_rad.ω 0 = seg_up10.ω 1 := by
      dsimp [seg_up_rad, seg_up10, mkStripAffineSeg, mkStripSeg, P₀, P₁]; simp
    have hw4 : seg_up_arc.ω 0 = seg_up_rad.ω 1 := by
      dsimp [seg_up_arc, seg_up_rad, mkStripArcSeg, mkStripAffineSeg, mkStripSeg, dir_plus]; simp
    have hw5 : seg_up_ray.ω 0 = seg_up_arc.ω 1 := by
      dsimp [seg_up_ray, seg_up_arc, mkStripRevRaySeg, mkStripArcSeg, mkStripSeg, dir_plus]
      simp only [sub_zero, sub_self, zero_mul, zero_add, one_mul]
      exact congrArg chartOmega hw_plus_polar
    have hw6 : seg_up_ray.ω seg_up_ray.b = chartOmega s := by
      dsimp [seg_up_ray, mkStripRevRaySeg, mkStripSeg]; simp
    exact ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6⟩
  have hup_strip : ∀ S ∈ [seg_up32, seg_up21, seg_up10], S.isStrip = true := fun S hS => by
    rcases List.mem_cons.mp hS with rfl | hS; · rfl
    rcases List.mem_cons.mp hS with rfl | hS; · rfl
    rw [List.mem_singleton] at hS; subst hS; rfl
  have hup_j10_ω : ∀ S ∈ [seg_up32, seg_up21, seg_up10], ∀ him : ∀ t ∈ Icc S.a S.b, |(S.ζ t).im| ≤ T₀,
      ∀ t ∈ Icc S.a S.b, 0 ≤ (S.ω t).re ∧ c_Γ ≤ ‖S.ω t‖ ∧ ‖S.ω t‖ ≤ C_Γ ∧ ‖S.ω' t‖ ≤ C_d := fun S hS him t ht => by
    obtain ⟨u, hu, hζ_u⟩ := hj10_seg_mem S hS t ht
    have hpt := hJ10_pts u hu
    have hstrip_t := S.hζ_strip (hup_strip S hS) t ht
    have him_ub := him t ht
    have hcl : S.ζ t ∈ stripClosed := ⟨hstrip_t.1, hstrip_t.2.1.trans (by norm_num)⟩
    have hom_ub : ‖S.ω t‖ ≤ C_Γ := by
      rw [hstrip_t.2.2.1]
      calc ‖chartOmega (S.ζ t)‖ ≤ C_om * (1 + (S.ζ t).im ^ 2) := hC_om _ hcl
        _ ≤ C_om * (1 + T₀ ^ 2) :=
            mul_le_mul_of_nonneg_left (add_le_add_right (by rw [← sq_abs (S.ζ t).im]; exact pow_le_pow_left₀ (abs_nonneg _) him_ub 2) 1) hC_om_pos.le
        _ = C_om_max := hC_om_max_eq.symm
        _ ≤ C_Γ := hC_Γ_ge_om
    have hom_lb : c_Γ ≤ ‖S.ω t‖ := by
      rw [hstrip_t.2.2.1, hζ_u]
      exact hc_Γ_le_j10.trans (hJ10_om_lb u hu).1
    have hω'_ub : ‖S.ω' t‖ ≤ C_d := by
      rw [hstrip_t.2.2.2.2.2, norm_mul]
      have hd1 : ‖deriv chartOmega (S.ζ t)‖ ≤ C_om'_max := by
        rw [hC_om'_max_eq]
        exact (hC_om' _ hcl).trans (mul_le_mul_of_nonneg_left (add_le_add_right him_ub 1) hC_om'_pos.le)
      exact (mul_le_mul hd1 (h_up_dz S hS t ht) (norm_nonneg _) hCom'_max_nn).trans
        ((mul_le_mul_of_nonneg_left (by linarith only [Real.pi_pos] : T₀ + 2 ≤ T₀ + 2 + 2 * Real.pi)
          hCom'_max_nn).trans hC_d_ge_om)
    exact ⟨by rw [hstrip_t.2.2.1, hζ_u]; exact hpt.2.2.2.2.2.2.2.2.2.2.1, hom_lb, hom_ub, hω'_ub⟩
  have hup_fs_bd : ∀ S ∈ [seg_up32, seg_up21, seg_up10], ∀ him : ∀ t ∈ Icc S.a S.b, |(S.ζ t).im| ≤ T₀,
      ∀ t ∈ Icc S.a S.b, (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - κ_strip := fun S hS him t ht => by
    obtain ⟨u, hu, hζ_u⟩ := hj10_seg_mem S hS t ht
    have hpt := hJ10_pts u hu
    have hstrip_t := S.hζ_strip (hup_strip S hS) t ht
    have hJ10_m : j10H (S.ζ t) ≤ -4 * κ_strip := by
      rw [hζ_u]; exact hpt.2.2.2.2.2.2.2.1.trans hκ_strip_j10
    exact h_fixed_strip_H _ hstrip_t.1 hstrip_t.2.1 (him t ht) hJ10_m
  have hT02_Cd : T₀ + 2 ≤ C_d :=
    (by linarith only [Real.pi_pos, hT₀_ge4] : T₀ + 2 ≤ T₀ + 2 * Real.pi + 2).trans hC_d_ge_T0
  have hsub_ks : (chartPhiV s b).re - κ_strip ≤ (chartPhiV s b).re :=
    sub_le_self _ hκ_strip_pos.le
  have hsub_arc : (chartPhiV s b).re - κ_arc * ρ ^ 3 ≤ (chartPhiV s b).re := by
    refine sub_le_self _ (mul_nonneg ?_ (pow_nonneg hρ_nn 3))
    rw [hκ_arc_eq]; positivity [Real.pi_pos]
  refine ⟨upper_segs, hchain_up, by simp [upper_segs], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    rcases List.mem_cons.mp hS with rfl | hS; · dsimp [seg_up32, mkStripAffineSeg, mkStripSeg]; norm_num
    rcases List.mem_cons.mp hS with rfl | hS; · dsimp [seg_up21, mkStripAffineSeg, mkStripSeg]; norm_num
    rcases List.mem_cons.mp hS with rfl | hS; · dsimp [seg_up10, mkStripAffineSeg, mkStripSeg]; norm_num
    rcases List.mem_cons.mp hS with rfl | hS; · dsimp [seg_up_rad, mkStripAffineSeg, mkStripSeg]; norm_num
    rcases List.mem_cons.mp hS with rfl | hS; · dsimp [seg_up_arc, mkStripArcSeg, mkStripSeg]; norm_num
    rw [List.mem_singleton] at hS; subst hS
    change t_plus - 0 ≤ 1; linarith only [ht_plus_mem.2, hρ_le, hρ₀_delta, hδ_14]
  · intro S hS t ht
    rcases List.mem_cons.mp hS with rfl | hS
    · exact hup_j10_ω seg_up32 List.mem_cons_self
        (fun s hs => zp_affine_im_bd (by linarith only [hT₀_ge4]) hP3_im hP2_im hs) t ht
    rcases List.mem_cons.mp hS with rfl | hS
    · exact hup_j10_ω seg_up21 (List.mem_cons_of_mem _ List.mem_cons_self)
        (fun s hs => zp_affine_im_bd (by linarith only [hT₀_ge4]) hP2_im hP1_im hs) t ht
    rcases List.mem_cons.mp hS with rfl | hS
    · exact hup_j10_ω seg_up10 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (fun s hs => zp_affine_im_bd (by linarith only [hT₀_ge4]) hP1_im hP0_im hs) t ht
    rcases List.mem_cons.mp hS with rfl | hS
    · have hvn : ‖seg_up_rad.ζ t‖ ≤ δ := by
        let r_t : ℝ := (1 - t) * δ + t * (10 * ρ)
        have hζ_eq : seg_up_rad.ζ t = (r_t : ℂ) * dir_plus := by
          dsimp [seg_up_rad, mkStripAffineSeg, mkStripSeg, P₀, j10P, dir_plus, r_t]; push_cast; ring
        change t ∈ Icc (0 : ℝ) 1 at ht
        rw [hζ_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by nlinarith only [ht.1, ht.2, hρ_nn, hδ_pos]),
          hdir_plus_norm, mul_one]
        nlinarith only [ht.1, ht.2, h12ρ_δ, hρ_nn]
      have hstrip_t := seg_up_rad.hζ_strip rfl t ht
      have him := h_inner_om _ hstrip_t.1 hstrip_t.2.1 hvn
      refine ⟨him.1, him.2.1, him.2.2.1, ?_⟩
      have hdz_bd : ‖seg_up_rad.ζ' t‖ ≤ 1 := by
        change ‖(10 * (ρ : ℂ)) * dir_plus - P₀‖ ≤ 1
        have heq : (10 * (ρ : ℂ)) * dir_plus - P₀ = ((10 * ρ - δ : ℝ) : ℂ) * dir_plus := by
          dsimp [P₀, j10P, dir_plus]; push_cast; ring
        rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, hdir_plus_norm, mul_one, abs_le]
        constructor <;> linarith only [hδ_14, hρ_nn, h12ρ_δ]
      rw [hstrip_t.2.2.2.2.2, norm_mul]
      exact ((mul_le_mul him.2.2.2 hdz_bd (norm_nonneg _) (by positivity)).trans_eq (mul_one _)).trans hCom_le_Cd
    rcases List.mem_cons.mp hS with rfl | hS
    · have hvn : ‖seg_up_arc.ζ t‖ ≤ δ := by
        change ‖((10 * ρ : ℝ) : ℂ) * Complex.exp _‖ ≤ δ
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity [hρ_nn]), exp_ofReal_mul_I_norm', mul_one]
        linarith only [h12ρ_δ, hρ_nn]
      have hstrip_t := seg_up_arc.hζ_strip rfl t ht
      have him := h_inner_om _ hstrip_t.1 hstrip_t.2.1 hvn
      refine ⟨him.1, him.2.1, him.2.2.1, ?_⟩
      have hdz_bd : ‖seg_up_arc.ζ' t‖ ≤ 2 * Real.pi := by
        change ‖Complex.I * ((θ_plus - Real.pi / 3 : ℝ) : ℂ) * _‖ ≤ 2 * Real.pi
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity [hρ_nn]), exp_ofReal_mul_I_norm', mul_one]
        have habs_th : |θ_plus - Real.pi / 3| ≤ Real.pi / 2 := by
          rw [abs_le]; constructor <;> linarith only [hθ_plus_mem.1, hθ_plus_mem.2, Real.pi_pos]
        have h10rho : 10 * ρ ≤ 1 := by linarith only [hρ_le, hρ₀_delta, hδ_14]
        exact (mul_le_mul habs_th h10rho (by positivity) (by positivity [Real.pi_pos])).trans
          (by linarith only [Real.pi_pos])
      rw [hstrip_t.2.2.2.2.2, norm_mul]
      exact (mul_le_mul him.2.2.2 hdz_bd (norm_nonneg _) (by positivity)).trans hCom_pi_le_Cd
    rw [List.mem_singleton] at hS; subst hS
    have hvn : ‖seg_up_ray.ζ t‖ ≤ δ := by
      change t ∈ Icc (0 : ℝ) t_plus at ht
      change ‖s + ((t_plus - t : ℝ) : ℂ) * dir_plus‖ ≤ δ
      calc ‖s + ((t_plus - t : ℝ) : ℂ) * dir_plus‖
          ≤ ‖s‖ + ‖((t_plus - t : ℝ) : ℂ) * dir_plus‖ := norm_add_le _ _
        _ = ρ + (t_plus - t) := by
            rw [hs_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith only [ht.2]),
              hdir_plus_norm, mul_one]
        _ ≤ 12 * ρ := by linarith only [ht.1, ht_plus_mem.2]
        _ ≤ δ := h12ρ_δ
    have hstrip_t := seg_up_ray.hζ_strip rfl t ht
    have him := h_inner_om _ hstrip_t.1 hstrip_t.2.1 hvn
    refine ⟨him.1, him.2.1, him.2.2.1, ?_⟩
    rw [hstrip_t.2.2.2.2.2, norm_mul]
    have hdz : ‖seg_up_ray.ζ' t‖ = 1 := by change ‖-dir_plus‖ = 1; rw [norm_neg, hdir_plus_norm]
    rw [hdz, mul_one]
    exact him.2.2.2.trans hCom_le_Cd
  · intro S hS _ t ht
    rcases List.mem_cons.mp hS with rfl | hS
    · have hS' : seg_up32 ∈ [seg_up32, seg_up21, seg_up10] := List.mem_cons_self
      exact ⟨(h_up_dz seg_up32 hS' t ht).trans hT02_Cd,
        (hup_fs_bd seg_up32 hS' (fun s hs => zp_affine_im_bd (by linarith only [hT₀_ge4]) hP3_im hP2_im hs) t ht).trans hsub_ks⟩
    rcases List.mem_cons.mp hS with rfl | hS
    · have hS' : seg_up21 ∈ [seg_up32, seg_up21, seg_up10] := List.mem_cons_of_mem _ List.mem_cons_self
      exact ⟨(h_up_dz seg_up21 hS' t ht).trans hT02_Cd,
        (hup_fs_bd seg_up21 hS' (fun s hs => zp_affine_im_bd (by linarith only [hT₀_ge4]) hP2_im hP1_im hs) t ht).trans hsub_ks⟩
    rcases List.mem_cons.mp hS with rfl | hS
    · have hS' : seg_up10 ∈ [seg_up32, seg_up21, seg_up10] := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      exact ⟨(h_up_dz seg_up10 hS' t ht).trans hT02_Cd,
        (hup_fs_bd seg_up10 hS' (fun s hs => zp_affine_im_bd (by linarith only [hT₀_ge4]) hP1_im hP0_im hs) t ht).trans hsub_ks⟩
    rcases List.mem_cons.mp hS with rfl | hS
    · refine ⟨?_, (h_up_rad_bd t ht).trans hsub_arc⟩
      change ‖(10 * (ρ : ℂ)) * dir_plus - P₀‖ ≤ C_d
      have heq : (10 * (ρ : ℂ)) * dir_plus - P₀ = ((10 * ρ - δ : ℝ) : ℂ) * dir_plus := by
        dsimp [P₀, j10P, dir_plus]; push_cast; ring
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, hdir_plus_norm, mul_one]
      have h1 : |10 * ρ - δ| ≤ 1 := abs_le.mpr ⟨by linarith only [hδ_14, hρ_nn], by linarith only [hδ_14, hρ_nn, h12ρ_δ]⟩
      exact h1.trans (hT0_pi_gt1.trans hC_d_ge_T0)
    rcases List.mem_cons.mp hS with rfl | hS
    · refine ⟨?_, ?_⟩
      · change ‖Complex.I * ((θ_plus - Real.pi / 3 : ℝ) : ℂ) * _‖ ≤ C_d
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity [hρ_nn]), exp_ofReal_mul_I_norm', mul_one]
        have habs_th : |θ_plus - Real.pi / 3| ≤ Real.pi / 2 := by
          rw [abs_le]; constructor <;> linarith only [hθ_plus_mem.1, hθ_plus_mem.2, Real.pi_pos]
        have h10rho : 10 * ρ ≤ 1 := by linarith only [hρ_le, hρ₀_delta, hδ_14]
        calc |θ_plus - Real.pi / 3| * (10 * ρ) ≤ (Real.pi / 2) * 1 :=
              mul_le_mul habs_th h10rho (by positivity) (by positivity [Real.pi_pos])
          _ ≤ T₀ + 2 * Real.pi + 2 := by linarith only [Real.pi_pos, hT₀_ge4]
          _ ≤ C_d := hC_d_ge_T0
      · exact (h_up_arc_bd _ (mem_convex_uIcc ht)).trans hsub_arc
    rw [List.mem_singleton] at hS; subst hS
    refine ⟨?_, ?_⟩
    · change ‖-dir_plus‖ ≤ C_d; rw [norm_neg, hdir_plus_norm]; exact hT0_pi_gt1.trans hC_d_ge_T0
    · change t ∈ Icc (0 : ℝ) t_plus at ht
      change (chartPhiV (s + ((t_plus - t : ℝ) : ℂ) * dir_plus) b).re ≤ (chartPhiV s b).re
      exact (h_up_ray_bd (t_plus - t) ⟨by linarith only [ht.2], by linarith only [ht.1]⟩).trans
        (sub_le_self _ (mul_nonneg (mul_nonneg hc_γ_pos.le hρ_nn) (sq_nonneg _)))
  · intro S hS _ hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up32, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up21, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up10, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up_rad, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up_arc, mkStripArcSeg, mkStripSeg] at hkind
    rw [List.mem_singleton] at hS; subst hS
    refine ⟨t_plus, by linarith only [ht_plus_mem.1, hρ_nn], rfl, rfl, ht_plus_mem.2, fun t ht => ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · change ‖s + ((t_plus - t : ℝ) : ℂ) * dir_plus - s‖ = t_plus - t
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith only [ht.2]),
        hdir_plus_norm, mul_one]
    · change ‖-dir_plus‖ = 1; rw [norm_neg, hdir_plus_norm]
    · exact h_up_ray_bd (t_plus - t) ⟨by linarith only [ht.2], by linarith only [ht.1]⟩
  · intro S hS _ hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up32, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up21, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up10, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up_rad, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up_arc, mkStripArcSeg, mkStripSeg] at hkind
    rw [List.mem_singleton] at hS; subst hS; simp [seg_up_ray, mkStripRevRaySeg, mkStripSeg] at hkind
  · intro S hS _ hkind t ht
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up32, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up21, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up10, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · exact h_up_rad_bd t ht
    rcases List.mem_cons.mp hS with rfl | hS; · exact h_up_arc_bd _ (mem_convex_uIcc ht)
    rw [List.mem_singleton] at hS; subst hS; simp [seg_up_ray, mkStripRevRaySeg, mkStripSeg] at hkind
  · intro S hS _ hkind t ht
    rcases List.mem_cons.mp hS with rfl | hS
    · exact hup_fs_bd seg_up32 List.mem_cons_self
        (fun s hs => zp_affine_im_bd (by linarith only [hT₀_ge4]) hP3_im hP2_im hs) t ht
    rcases List.mem_cons.mp hS with rfl | hS
    · exact hup_fs_bd seg_up21 (List.mem_cons_of_mem _ List.mem_cons_self)
        (fun s hs => zp_affine_im_bd (by linarith only [hT₀_ge4]) hP2_im hP1_im hs) t ht
    rcases List.mem_cons.mp hS with rfl | hS
    · exact hup_fs_bd seg_up10 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (fun s hs => zp_affine_im_bd (by linarith only [hT₀_ge4]) hP1_im hP0_im hs) t ht
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up_rad, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up_arc, mkStripArcSeg, mkStripSeg] at hkind
    rw [List.mem_singleton] at hS; subst hS; simp [seg_up_ray, mkStripRevRaySeg, mkStripSeg] at hkind
  · intro S hS hfalse
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up32, mkStripAffineSeg, mkStripSeg] at hfalse
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up21, mkStripAffineSeg, mkStripSeg] at hfalse
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up10, mkStripAffineSeg, mkStripSeg] at hfalse
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up_rad, mkStripAffineSeg, mkStripSeg] at hfalse
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up_arc, mkStripArcSeg, mkStripSeg] at hfalse
    rw [List.mem_singleton] at hS; subst hS; simp [seg_up_ray, mkStripRevRaySeg, mkStripSeg] at hfalse
  · intro S hS _ hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up32, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up21, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up10, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up_rad, mkStripAffineSeg, mkStripSeg] at hkind
    rcases List.mem_cons.mp hS with rfl | hS; · simp [seg_up_arc, mkStripArcSeg, mkStripSeg] at hkind
    rw [List.mem_singleton] at hS; subst hS; simp [seg_up_ray, mkStripRevRaySeg, mkStripSeg] at hkind

/-- **Lemma Z' (uniform contour through the saddle)** (`lower_o1_two_edge.tex`, §J6–J7, `vlo:Zp`,
lines 572–720): there exists a uniform configuration `cfg : ZPConfig` such that for every
`s = ρ e^{i(π/2 - φ')}` with `0 ≤ ρ ≤ cfg.ρ₀` and `0 ≤ φ' ≤ π/2`, putting `b = chartB s`, one has
`Im b ≤ 0`, `Re b ≥ ξ_*/2`, and a piecewise-`C^1` chained contour `segs` from `ω(1/2 + i T₀)` to
`ω(1/2 - i T₀)` satisfying all `Re ω ≥ 0`, velocity, length, strip, ray, arc/radial, fixed-strip,
and crude left-edge bounds relative to `F_+ = Re Φ_V(s; b)`. -/
theorem lemma_Zp :
    ∃ cfg : ZPConfig,
      ∀ {ρ φ' : ℝ}, 0 ≤ ρ → ρ ≤ cfg.ρ₀ → 0 ≤ φ' → φ' ≤ Real.pi / 2 →
        let s : ℂ := (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 - φ' : ℝ) : ℂ))
        let b : ℂ := chartB s
        b.im ≤ 0 ∧ xiStar / 2 ≤ b.re ∧ ‖b‖ ≤ 2 * xiStar ∧
        ∃ segs : List ContourSeg,
          ContourChained (chartOmega ((1 / 2 : ℂ) + Complex.I * (cfg.T₀ : ℂ)))
            (chartOmega ((1 / 2 : ℂ) - Complex.I * (cfg.T₀ : ℂ))) segs ∧
          contourLength segs ≤ cfg.C_len ∧
          (∀ S ∈ segs, ∀ t ∈ Icc S.a S.b,
            0 ≤ (S.ω t).re ∧ cfg.c_Γ ≤ ‖S.ω t‖ ∧ ‖S.ω t‖ ≤ cfg.C_Γ ∧ ‖S.ω' t‖ ≤ cfg.C_d) ∧
          (∀ S ∈ segs, S.isStrip = true → ∀ t ∈ Icc S.a S.b,
            ‖S.ζ' t‖ ≤ cfg.C_d ∧ (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re) ∧
          (∀ S ∈ segs, S.isStrip = true → S.kind = .upperRay →
            ∃ t_max ≥ (0 : ℝ), S.a = 0 ∧ S.b = t_max ∧ t_max ≤ 11 * ρ ∧
              ∀ t ∈ Icc 0 t_max, ‖S.ζ t - s‖ = t_max - t ∧ ‖S.ζ' t‖ = 1 ∧
                (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - cfg.c_γ * ρ * (t_max - t) ^ 2) ∧
          (∀ S ∈ segs, S.isStrip = true → S.kind = .lowerRay →
            ∃ t_max ≥ (0 : ℝ), S.a = 0 ∧ S.b = t_max ∧ t_max ≤ 11 * ρ ∧
              ∀ t ∈ Icc 0 t_max, ‖S.ζ t - s‖ = t ∧ ‖S.ζ' t‖ = 1 ∧
                (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - cfg.c_γ * ρ * t ^ 2) ∧
          (∀ S ∈ segs, S.isStrip = true → S.kind = .arcRadial →
            ∀ t ∈ Icc S.a S.b,
              (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - cfg.κ_arc * ρ ^ 3) ∧
          (∀ S ∈ segs, S.isStrip = true → S.kind = .fixedStrip →
            ∀ t ∈ Icc S.a S.b,
              (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - cfg.κ_strip) ∧
          (∀ S ∈ segs, S.isStrip = false →
            ∀ t ∈ Icc S.a S.b,
              cfg.μ₀ ≤ (S.ω t).re ∧
              crudeExponentEc (S.ω t) b ≤ (chartPhiV s b).re - cfg.c_γ * ρ * s.re ^ 2) ∧
          segs.length ≤ 12 ∧
          (∀ S ∈ segs, S.b - S.a ≤ 1) ∧
          (∀ S ∈ segs, S.isStrip = true → S.kind ≠ .crudeEdge) := by
  classical
  obtain ⟨η, ρ_F, hρF_pos, C_F, hCF_nn, hη_an, _, hF_id, hη_bd⟩ := lemma_F
  obtain ⟨r_q, hr_q_pos, C_q, hCq_nn, hq_props⟩ := im_chartB_nonpos_firstQuadrant
  obtain ⟨r_sad, hr_sad_pos, C_sad, hCsad_nn, hsad_bd⟩ := chartPhiV_saddle_le
  obtain ⟨_, _, _, ⟨C_om, hC_om_pos, hC_om⟩, ⟨C_om', hC_om'_pos, hC_om'⟩, _, _⟩ := lemma_J7_asymptotics
  obtain ⟨_, _, _, ⟨c_mid, hc_mid_pos, h_mid_lb⟩, _, T_mid_tail, hT_mid_ge, h_mid_tail⟩ := lemma_J7_midline
  obtain ⟨T_junc, hT_junc_ge, C_L, hC_L_pos, c_L, hc_L_pos, κ_J7, hκ_J7_pos, h_junc⟩ :=
    existsUnique_junction_xL
  have hcos7 : Real.cos (7 * Real.pi / 12) < 0 :=
    (lower_ray_ge_pi4_cos_le le_rfl (by linarith [Real.pi_pos])).2
  have hneg7 : 0 < -Real.cos (7 * Real.pi / 12) := neg_pos.mpr hcos7
  obtain ⟨c_neg, hc_neg_eq⟩ : ∃ x : ℝ, x = min (-Real.cos (7 * Real.pi / 12)) (1 / 2) := ⟨_, rfl⟩
  have hc_neg_pos : 0 < c_neg := hc_neg_eq ▸ lt_min hneg7 (by norm_num)
  have hc_neg_le_half : c_neg ≤ 1 / 2 := hc_neg_eq ▸ min_le_right _ _
  have h_inv_sq2 : 1 / √2 = √2 / 2 := by
    have hsq2 : √2 ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
    rw [div_eq_div_iff hsq2 two_ne_zero]; ring_nf; rw [Real.sq_sqrt (by norm_num)]
  have h_one_sixth : 1 / (6 : ℝ) ≤ (1 / 3 : ℝ) * (1 / √2) := by
    have hsq2_lt : √2 < 2 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [one_div_mul_one_div, one_div_le_one_div (by norm_num) (by positivity)]
    linarith only [hsq2_lt]
  obtain ⟨δ, hδ_eq⟩ : ∃ x : ℝ, x = min
    (min (min (min r_q r_sad) (min (ρ_F / 2) j10Delta0)) (1 / 4))
    (min (muStar / (6 * (C_om' + 1))) (min (1 / (80 * (C_F + 1))) (c_neg / (16 * 44 * (C_F + 1))))) := ⟨_, rfl⟩
  have hj10_pos : 0 < j10Delta0 := by unfold j10Delta0; norm_num
  have hδ_pos : 0 < δ := by
    rw [hδ_eq]; have := xiStar_pos; have := muStar_pos; positivity
  have hδ_j10 : δ ≤ j10Delta0 := hδ_eq ▸
    (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδ_rq : δ ≤ r_q := hδ_eq ▸
    (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hδ_rsad : δ ≤ r_sad := hδ_eq ▸
    (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hδ_rhoF2 : δ ≤ ρ_F / 2 := hδ_eq ▸
    (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ_rhoF : δ < min ρ_F (1 / 2) := by
    refine lt_min (hδ_rhoF2.trans_lt (half_lt_self hρF_pos)) ?_
    exact (hδ_eq ▸ (min_le_left _ _).trans (min_le_right _ _)).trans_lt (by norm_num)
  have hδ_14 : δ ≤ 1 / 4 := hδ_eq ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hδ_om : δ ≤ muStar / (6 * (C_om' + 1)) := hδ_eq ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hδ_cf1 : δ ≤ 1 / (80 * (C_F + 1)) := hδ_eq ▸
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ_cf2 : δ ≤ c_neg / (16 * 44 * (C_F + 1)) := hδ_eq ▸
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨T₀, hT₀_eq⟩ : ∃ x : ℝ, x = max (max 4 (max T_mid_tail T_junc))
    (max (√((2 * C_om' * C_L + 1) / c_mid) + 1) (√((muStar / 4 + 1) / c_L) + 1)) := ⟨_, rfl⟩
  have hT₀_ge4 : 4 ≤ T₀ := hT₀_eq ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hT₀_half : 1 / 2 ≤ T₀ := by linarith only [hT₀_ge4]
  have hT₀_Tmid : T_mid_tail ≤ T₀ := hT₀_eq ▸
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hT₀_Tjunc : T_junc ≤ T₀ := hT₀_eq ▸
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hT₀_mid_sq : 2 * C_om' * C_L + 1 ≤ c_mid * T₀ ^ 2 := by
    have h1 : √((2 * C_om' * C_L + 1) / c_mid) ≤ T₀ := by
      have hmax : √((2 * C_om' * C_L + 1) / c_mid) + 1 ≤ T₀ := hT₀_eq ▸
        (le_max_left _ (√((muStar / 4 + 1) / c_L) + 1)).trans (le_max_right _ _)
      linarith only [hmax]
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rw [Real.sq_sqrt (by positivity)] at hsq
    calc 2 * C_om' * C_L + 1 = c_mid * ((2 * C_om' * C_L + 1) / c_mid) := by
          field_simp [hc_mid_pos.ne']
      _ ≤ c_mid * T₀ ^ 2 := mul_le_mul_of_nonneg_left hsq hc_mid_pos.le
  have hT₀_yL_sq : muStar / 4 + 1 ≤ c_L * T₀ ^ 2 := by
    have hmax : √((muStar / 4 + 1) / c_L) + 1 ≤ T₀ := hT₀_eq ▸
      (le_max_right (√((2 * C_om' * C_L + 1) / c_mid) + 1) _).trans (le_max_right _ _)
    have h1 : √((muStar / 4 + 1) / c_L) ≤ T₀ := by linarith only [hmax]
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rw [Real.sq_sqrt (by positivity [muStar_pos])] at hsq
    calc muStar / 4 + 1 = c_L * ((muStar / 4 + 1) / c_L) := by
          field_simp [hc_L_pos.ne']
      _ ≤ c_L * T₀ ^ 2 := mul_le_mul_of_nonneg_left hsq hc_L_pos.le
  obtain ⟨d₀, d₁, hd₀_pos, hd₁_pos, hmid_decay⟩ := h_mid_tail T₀ hT₀_Tmid
  obtain ⟨_, _, _, _, hJ10_P_le, hJ10_eps_ge, hε_pos, hJ10_pts, _, _,
    _, _, ⟨M_J10, hMJ10_pos, hJ10_dOm⟩, _, _, ⟨c_J10, hcJ10_pos, hJ10_om_lb⟩⟩ :=
    lemma_J10_compact_escape hδ_pos hδ_j10 hT₀_half
  obtain ⟨ε_J10, hε_J10_eq⟩ : ∃ x : ℝ, x = -j10H (j10P δ) / 2 := ⟨_, rfl⟩
  obtain ⟨κ_strip, hκ_strip_eq⟩ : ∃ x : ℝ, x = min ε_J10 (κ_J7 * T₀) / 4 := ⟨_, rfl⟩
  have hκ_strip_pos : 0 < κ_strip := by
    rw [hκ_strip_eq, hε_J10_eq]
    have : 0 < κ_J7 * T₀ := mul_pos hκ_J7_pos (by linarith only [hT₀_ge4])
    positivity
  obtain ⟨C_strip_om, hC_strip_om_eq⟩ : ∃ x : ℝ, x = max (C_om * (1 + 1)) (C_om * (1 + T₀ ^ 2)) := ⟨_, rfl⟩
  obtain ⟨C_pert, hC_pert_eq⟩ : ∃ x : ℝ, x = (2 * Real.pi / 3 + 4 / xiStar * C_strip_om) * C_q := ⟨_, rfl⟩
  have hC_pert_nn : 0 ≤ C_pert := by
    rw [hC_pert_eq, hC_strip_om_eq]; have := xiStar_pos; have := Real.pi_pos; positivity
  obtain ⟨ρ₀, hρ₀_eq⟩ : ∃ x : ℝ, x = min (min (δ / 12) (1 / (4000 * (C_F + 1))))
    (min (√(xiStar / (4 * (C_q + 1))))
      (min (√(κ_strip / (C_pert + 1))) (min 1 (κ_strip / (C_sad + 1))))) := ⟨_, rfl⟩
  have hρ₀_pos : 0 < ρ₀ := by
    rw [hρ₀_eq]; have := xiStar_pos; positivity
  have hρ₀_delta : 12 * ρ₀ ≤ δ := by
    have h1 : ρ₀ ≤ δ / 12 := hρ₀_eq ▸ (min_le_left _ _).trans (min_le_left _ _)
    linarith only [h1]
  have hρ₀_arc : 4000 * C_F * ρ₀ ≤ 1 := by
    have h1 : ρ₀ ≤ 1 / (4000 * (C_F + 1)) := hρ₀_eq ▸ (min_le_left _ _).trans (min_le_right _ _)
    have h2 : 4000 * C_F * ρ₀ ≤ 4000 * C_F * (1 / (4000 * (C_F + 1))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 4000 * C_F * (1 / (4000 * (C_F + 1))) = C_F * (1 / (C_F + 1)) := by
      rw [one_div (4000 * (C_F + 1)), mul_inv, one_div (C_F + 1)]; ring
    exact (h2.trans_eq h3).trans (mul_div_add_one_le hCF_nn zero_le_one)
  have hρ₀_cq : C_q * ρ₀ ^ 2 ≤ xiStar / 4 := by
    have h1 : ρ₀ ≤ √(xiStar / (4 * (C_q + 1))) := hρ₀_eq ▸
      (min_le_right _ _).trans (min_le_left _ _)
    have hsq := pow_le_pow_left₀ hρ₀_pos.le h1 2
    rw [Real.sq_sqrt (by positivity [xiStar_pos])] at hsq
    calc C_q * ρ₀ ^ 2 ≤ C_q * (xiStar / (4 * (C_q + 1))) := mul_le_mul_of_nonneg_left hsq hCq_nn
      _ = C_q * ((xiStar / 4) / (C_q + 1)) := by
          rw [div_eq_mul_inv xiStar (4 * (C_q + 1)), mul_inv, div_eq_mul_inv (xiStar / 4),
            div_eq_mul_inv xiStar 4]; ring
      _ ≤ xiStar / 4 := mul_div_add_one_le hCq_nn (by linarith only [xiStar_pos])
  have hρ₀_pert : C_pert * ρ₀ ^ 2 ≤ κ_strip := by
    have h1 : ρ₀ ≤ √(κ_strip / (C_pert + 1)) := hρ₀_eq ▸
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hsq := pow_le_pow_left₀ hρ₀_pos.le h1 2
    rw [Real.sq_sqrt (by positivity)] at hsq
    calc C_pert * ρ₀ ^ 2 ≤ C_pert * (κ_strip / (C_pert + 1)) := mul_le_mul_of_nonneg_left hsq hC_pert_nn
      _ ≤ κ_strip := mul_div_add_one_le hC_pert_nn hκ_strip_pos.le
  have hρ₀_sad : C_sad * ρ₀ ^ 3 ≤ κ_strip := by
    have h1 : ρ₀ ≤ 1 := hρ₀_eq ▸
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have h2 : ρ₀ ≤ κ_strip / (C_sad + 1) := hρ₀_eq ▸
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hcube : ρ₀ ^ 3 ≤ ρ₀ := by nlinarith only [sq_nonneg ρ₀, hρ₀_pos, h1]
    calc C_sad * ρ₀ ^ 3 ≤ C_sad * ρ₀ := mul_le_mul_of_nonneg_left hcube hCsad_nn
      _ ≤ C_sad * (κ_strip / (C_sad + 1)) := mul_le_mul_of_nonneg_left h2 hCsad_nn
      _ ≤ κ_strip := mul_div_add_one_le hCsad_nn hκ_strip_pos.le
  have hCF_delta : C_F * δ ≤ 1 / 80 := by
    calc C_F * δ ≤ C_F * (1 / (80 * (C_F + 1))) := mul_le_mul_of_nonneg_left hδ_cf1 hCF_nn
      _ = C_F * ((1 / 80 : ℝ) / (C_F + 1)) := by
          rw [one_div (80 * (C_F + 1)), mul_inv, div_eq_mul_inv (1 / 80 : ℝ)]; ring
      _ ≤ 1 / 80 := mul_div_add_one_le hCF_nn (by norm_num)
  have hCF_delta_cneg : C_F * δ ≤ c_neg / (16 * 44) := by
    calc C_F * δ ≤ C_F * (c_neg / (16 * 44 * (C_F + 1))) := mul_le_mul_of_nonneg_left hδ_cf2 hCF_nn
      _ = C_F * ((c_neg / (16 * 44)) / (C_F + 1)) := by
          rw [div_eq_mul_inv c_neg (16 * 44 * (C_F + 1)), mul_inv,
            div_eq_mul_inv (c_neg / (16 * 44)), div_eq_mul_inv c_neg (16 * 44)]; ring
      _ ≤ c_neg / (16 * 44) := mul_div_add_one_le hCF_nn (by positivity)
  have hradial_eta : C_F * (5 / 4 * δ) * (1 + 1 / 16) ≤ 1 / 4 := by
    linarith only [hCF_delta]
  obtain ⟨c_γ, hc_γ_eq⟩ : ∃ x : ℝ, x = (Real.pi ^ 2 / 6) * min (c_neg / 2) (1 / (3 * √2)) := ⟨_, rfl⟩
  have hc_γ_pos : 0 < c_γ := by rw [hc_γ_eq]; positivity [Real.pi_pos]
  obtain ⟨κ_arc, hκ_arc_eq⟩ : ∃ x : ℝ, x = 10 * Real.pi ^ 2 := ⟨_, rfl⟩
  have hκ_arc_pos : 0 < κ_arc := by rw [hκ_arc_eq]; positivity [Real.pi_pos]
  obtain ⟨μ₀, hμ₀_eq⟩ : ∃ x : ℝ, x = (3 / 4 : ℝ) * muStar := ⟨_, rfl⟩
  have hμ₀_pos : 0 < μ₀ := by rw [hμ₀_eq]; positivity [muStar_pos]
  have hμ₀_gt : Real.pi * xiStar / 6 < μ₀ := by
    rw [hμ₀_eq]; unfold muStar; have := mul_pos Real.pi_pos xiStar_pos; linarith only [this]
  obtain ⟨c_Γ, hc_Γ_eq⟩ : ∃ x : ℝ, x = min (muStar / 2) (min c_J10 (min μ₀ 1)) := ⟨_, rfl⟩
  have hc_Γ_pos : 0 < c_Γ := by rw [hc_Γ_eq]; have := muStar_pos; positivity
  obtain ⟨C_om_max, hC_om_max_eq⟩ : ∃ x : ℝ, x = C_om * (1 + T₀ ^ 2) := ⟨_, rfl⟩
  obtain ⟨C_om'_max, hC_om'_max_eq⟩ : ∃ x : ℝ, x = C_om' * (1 + T₀) := ⟨_, rfl⟩
  obtain ⟨C_Γ, hC_Γ_eq⟩ : ∃ x : ℝ, x = max (3 / 2 * muStar) (max C_om_max (2 * muStar + C_om_max)) := ⟨_, rfl⟩
  have hc_Γ_le : c_Γ ≤ C_Γ := by
    have hmu := muStar_pos
    calc c_Γ ≤ muStar / 2 := hc_Γ_eq ▸ min_le_left _ _
      _ ≤ 3 / 2 * muStar := by linarith only [hmu]
      _ ≤ C_Γ := hC_Γ_eq ▸ le_max_left _ _
  obtain ⟨C_d, hC_d_eq⟩ : ∃ x : ℝ, x = max (C_om'_max * (T₀ + 2 + 2 * Real.pi))
    (max (C_om_max + 2 * muStar) (T₀ + 2 * Real.pi + 2)) := ⟨_, rfl⟩
  have hC_d_pos : 0 < C_d := by
    rw [hC_d_eq, hC_om'_max_eq, hC_om_max_eq]; positivity [Real.pi_pos, hT₀_ge4]
  obtain ⟨C_len, hC_len_eq⟩ : ∃ x : ℝ, x = 12 * C_d := ⟨_, rfl⟩
  have hC_len_pos : 0 < C_len := by rw [hC_len_eq]; positivity
  have hCom'_max_nn : 0 ≤ C_om'_max := by rw [hC_om'_max_eq]; positivity [hT₀_ge4]
  have hCom_max_nn : 0 ≤ C_om_max := by rw [hC_om_max_eq]; positivity
  have hC_Γ_ge_32 : 3 / 2 * muStar ≤ C_Γ := hC_Γ_eq ▸ le_max_left _ _
  have hC_Γ_ge_om : C_om_max ≤ C_Γ := hC_Γ_eq ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hC_Γ_ge_2om : 2 * muStar + C_om_max ≤ C_Γ := hC_Γ_eq ▸ (le_max_right _ _).trans (le_max_right _ _)
  have hc_Γ_le_j10 : c_Γ ≤ c_J10 := hc_Γ_eq ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hc_Γ_le_mu0 : c_Γ ≤ μ₀ := hc_Γ_eq ▸ (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc_Γ_le_1 : c_Γ ≤ 1 := hc_Γ_eq ▸ (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hC_d_ge_om : C_om'_max * (T₀ + 2 + 2 * Real.pi) ≤ C_d := hC_d_eq ▸ le_max_left _ _
  have hC_d_ge_2mu : C_om_max + 2 * muStar ≤ C_d := hC_d_eq ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hC_d_ge_T0 : T₀ + 2 * Real.pi + 2 ≤ C_d := hC_d_eq ▸ (le_max_right _ _).trans (le_max_right _ _)
  have hT0_pi_gt1 : (1 : ℝ) ≤ T₀ + 2 * Real.pi + 2 := by linarith only [Real.pi_pos, hT₀_ge4]
  have hCom_pi_le_Cd : (3 / 2 : ℝ) * C_om' * (2 * Real.pi) ≤ C_d := by
    have h3 : (3 / 2 : ℝ) * (2 * Real.pi) ≤ (1 + T₀) * (T₀ + 2 + 2 * Real.pi) := by
      nlinarith only [Real.pi_pos, hT₀_ge4]
    have hmul : (3 / 2 : ℝ) * C_om' * (2 * Real.pi) ≤ C_om'_max * (T₀ + 2 + 2 * Real.pi) := by
      rw [hC_om'_max_eq]
      calc (3 / 2 : ℝ) * C_om' * (2 * Real.pi) = C_om' * ((3 / 2 : ℝ) * (2 * Real.pi)) := by ring
        _ ≤ C_om' * ((1 + T₀) * (T₀ + 2 + 2 * Real.pi)) := mul_le_mul_of_nonneg_left h3 hC_om'_pos.le
        _ = C_om' * (1 + T₀) * (T₀ + 2 + 2 * Real.pi) := by ring
    exact hmul.trans hC_d_ge_om
  have hCom_le_Cd : (3 / 2 : ℝ) * C_om' ≤ C_d := by
    have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith only [Real.two_le_pi]
    calc (3 / 2 : ℝ) * C_om' = (3 / 2 : ℝ) * C_om' * 1 := (mul_one _).symm
      _ ≤ (3 / 2 : ℝ) * C_om' * (2 * Real.pi) := mul_le_mul_of_nonneg_left h2pi (by positivity [hC_om'_pos])
      _ ≤ C_d := hCom_pi_le_Cd
  have hκ_strip_j10 : -ε_J10 ≤ -4 * κ_strip := by
    have h2 : κ_strip ≤ ε_J10 / 4 := by rw [hκ_strip_eq]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith only [h2]
  have hκ_strip_j7 : -κ_J7 * T₀ ≤ -4 * κ_strip := by
    have h2 : κ_strip ≤ (κ_J7 * T₀) / 4 := by rw [hκ_strip_eq]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    linarith only [h2]
  let cfg : ZPConfig := {
    δ := δ, ρ₀ := ρ₀, c_γ := c_γ, T₀ := T₀, μ₀ := μ₀,
    c_Γ := c_Γ, C_Γ := C_Γ, C_len := C_len, C_d := C_d,
    κ_arc := κ_arc, κ_strip := κ_strip, d₀ := d₀, d₁ := d₁,
    hδ_pos := hδ_pos, hδ_j10 := hδ_j10, hρ₀_pos := hρ₀_pos, hc_γ_pos := hc_γ_pos,
    hT₀_ge := hT₀_ge4, hμ₀_gt := hμ₀_gt, hc_Γ_pos := hc_Γ_pos, hc_Γ_le := hc_Γ_le,
    hC_len_pos := hC_len_pos, hC_d_pos := hC_d_pos, hκ_arc_pos := hκ_arc_pos,
    hκ_strip_pos := hκ_strip_pos, hd₀_pos := hd₀_pos, hd₁_pos := hd₁_pos,
    hmid_tail := hmid_decay }
  refine ⟨cfg, fun {ρ φ'} hρ_nn hρ_le_cfg hφ_nn hφ_le => ?_⟩
  have hρ_le : ρ ≤ ρ₀ := hρ_le_cfg
  have h12ρ_δ : 12 * ρ ≤ δ := by linarith only [hρ_le, hρ₀_delta]
  have h11ρ_δ : 11 * ρ ≤ δ := by linarith only [hρ_nn, h12ρ_δ]
  let s : ℂ := (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 - φ' : ℝ) : ℂ))
  let b : ℂ := chartB s
  have hs_norm : ‖s‖ = ρ := by
    dsimp [s]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ_nn,
      exp_ofReal_mul_I_norm', mul_one]
  have hs_re_nn : 0 ≤ s.re := by
    dsimp [s]; rw [Complex.re_ofReal_mul, exp_ofReal_mul_I_re'']
    exact mul_nonneg hρ_nn (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩)
  have hs_im_nn : 0 ≤ s.im := by
    dsimp [s]; rw [Complex.im_ofReal_mul, exp_ofReal_mul_I_im'']
    exact mul_nonneg hρ_nn (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]))
  have hρ_lt_δ : ρ < δ := by linarith [hρ_le, hρ₀_delta, hρ₀_pos]
  have hs_rq : s ∈ ball (0 : ℂ) r_q :=
    mem_ball_zero_iff.mpr (hs_norm.symm ▸ (hρ_lt_δ.trans_le hδ_rq))
  have hs_rsad : s ∈ ball (0 : ℂ) r_sad :=
    mem_ball_zero_iff.mpr (hs_norm.symm ▸ (hρ_lt_δ.trans_le hδ_rsad))
  have hs_F : s ∈ ball (0 : ℂ) ρ_F :=
    mem_ball_zero_iff.mpr (hs_norm.symm ▸ (hρ_lt_δ.trans_le (hδ_rhoF2.trans (half_lt_self hρF_pos).le)))
  obtain ⟨hb_im, hb_re, hb_ub, hb_sub⟩ := hq_props s hs_rq hs_re_nn hs_im_nn
  have hb_re_pos : 0 < b.re := lt_of_lt_of_le (half_pos xiStar_pos) hb_re
  have hb_ne : b ≠ 0 := fun hz => by rw [hz, Complex.zero_re] at hb_re_pos; exact lt_irrefl 0 hb_re_pos
  have hb_sub_xi : ‖b - (xiStar : ℂ)‖ ≤ xiStar / 4 :=
    hb_sub.trans (by rw [hs_norm]; exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ_nn hρ_le 2) hCq_nn).trans hρ₀_cq)
  have hb_norm_range : ‖b‖ ∈ Icc (3 / 4 * xiStar) (5 / 4 * xiStar) := by
    have h1 := abs_norm_sub_norm_le b (xiStar : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg xiStar_pos.le] at h1
    have h2 := abs_le.mp (h1.trans hb_sub_xi)
    exact ⟨by linarith, by linarith⟩
  have hsad_abs : |(chartPhiV s b).re| ≤ κ_strip := by
    have h1 := hsad_bd s hs_rsad hs_re_nn hs_im_nn
    rw [Real.norm_eq_abs, hs_norm] at h1
    exact h1.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ_nn hρ_le 3) hCsad_nn).trans hρ₀_sad)
  refine ⟨hb_im, hb_re, hb_ub, ?_⟩
  -- Common inner strip bounds for w with ‖w‖ ≤ δ
  have h_inner_om : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 / 2 → ‖w‖ ≤ δ →
      0 ≤ (chartOmega w).re ∧ c_Γ ≤ ‖chartOmega w‖ ∧ ‖chartOmega w‖ ≤ C_Γ ∧
      ‖deriv chartOmega w‖ ≤ (3 / 2 : ℝ) * C_om' := fun w hw0 hw1 hwn => by
    have hw12 : ‖w‖ ≤ 1 / 2 := hwn.trans (hδ_14.trans (by norm_num))
    have hdiff := chartOmega_strip_sub_zero_le hC_om' hw0 hw1 hw12
    have hCδ : (3 / 2 : ℝ) * C_om' * δ ≤ muStar / 4 := by
      have hC_nn : 0 ≤ C_om' := by
        have h0' := hC_om' 0 ⟨le_rfl, zero_le_one⟩
        have : (0 : ℝ) ≤ C_om' * 1 := by simpa using (norm_nonneg _).trans h0'
        linarith
      calc (3 / 2 : ℝ) * C_om' * δ ≤ (3 / 2 : ℝ) * C_om' * (muStar / (6 * (C_om' + 1))) :=
            mul_le_mul_of_nonneg_left hδ_om (by positivity)
        _ = C_om' * ((muStar / 4) / (C_om' + 1)) := by
            rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring
        _ ≤ muStar / 4 := mul_div_add_one_le hC_nn (by positivity [muStar_pos])
    have hC_nn : 0 ≤ C_om' := by
      have h0' := hC_om' 0 ⟨le_rfl, zero_le_one⟩
      have : (0 : ℝ) ≤ C_om' * 1 := by simpa using (norm_nonneg _).trans h0'
      linarith
    have hdiff' : ‖chartOmega w - (muStar : ℂ)‖ ≤ muStar / 4 :=
      hdiff.trans ((mul_le_mul_of_nonneg_left hwn (by positivity)).trans hCδ)
    have hre_ge : 3 / 4 * muStar ≤ (chartOmega w).re := by
      have hre1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hdiff')).1
      rw [Complex.sub_re, Complex.ofReal_re] at hre1; linarith only [hre1]
    have hnorm_le : ‖chartOmega w‖ ≤ 3 / 2 * muStar := by
      have hsub_n : ‖chartOmega w‖ - ‖(muStar : ℂ)‖ ≤ ‖chartOmega w - (muStar : ℂ)‖ :=
        norm_sub_norm_le _ _
      rw [Complex.norm_real, Real.norm_of_nonneg muStar_pos.le] at hsub_n
      linarith only [hsub_n, hdiff', muStar_pos]
    have hderiv : ‖deriv chartOmega w‖ ≤ (3 / 2 : ℝ) * C_om' := by
      have hw_cl : w ∈ stripClosed := ⟨hw0, hw1.trans (by norm_num)⟩
      have him : |w.im| ≤ 1 / 2 := (Complex.abs_im_le_norm w).trans hw12
      calc ‖deriv chartOmega w‖ ≤ C_om' * (1 + |w.im|) := hC_om' w hw_cl
        _ ≤ C_om' * (1 + 1 / 2) := mul_le_mul_of_nonneg_left (by linarith only [him]) hC_nn
        _ = (3 / 2 : ℝ) * C_om' := by ring
    exact ⟨by linarith only [hre_ge, muStar_pos],
      (hc_Γ_eq ▸ min_le_left _ _).trans (by
        have hre_norm := Complex.re_le_norm (chartOmega w)
        linarith only [hre_ge, muStar_pos, hre_norm]),
      hnorm_le.trans (hC_Γ_eq ▸ le_max_left _ _), hderiv⟩
  -- Helper: comparing fixed-strip points against j10H and s
  have h_fixed_strip_H : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 / 2 → |ζ.im| ≤ T₀ →
      j10H ζ ≤ -4 * κ_strip →
      (chartPhiV ζ b).re ≤ (chartPhiV s b).re - κ_strip := fun ζ h0 h1 him hJ10 => by
    have hm : ζ ∈ stripClosed := ⟨h0, h1.trans (by norm_num)⟩
    have hOm_bd : ‖chartOmega ζ‖ ≤ C_strip_om := by
      have hsq : ζ.im ^ 2 ≤ T₀ ^ 2 := by
        rw [← sq_abs ζ.im]; exact pow_le_pow_left₀ (abs_nonneg _) him 2
      calc ‖chartOmega ζ‖ ≤ C_om * (1 + ζ.im ^ 2) := hC_om ζ hm
        _ ≤ C_om * (1 + T₀ ^ 2) := mul_le_mul_of_nonneg_left (add_le_add_right hsq 1) hC_om_pos.le
        _ ≤ C_strip_om := hC_strip_om_eq ▸ le_max_right _ _
    have hsub := chartPhiV_sub_ref_le (b := b) h0 (h1.trans (by norm_num)) hb_re hb_ub
    have hpert : |(chartPhiV ζ b).re - j10H ζ| ≤ κ_strip := by
      have hnorm : |(chartPhiV ζ b).re - j10H ζ| ≤ ‖chartPhiV ζ b - chartPhiV ζ (xiStar : ℂ)‖ := by
        unfold j10H; rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have hb_d : ‖b - (xiStar : ℂ)‖ ≤ C_q * ρ₀ ^ 2 :=
        hb_sub.trans (by rw [hs_norm]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ_nn hρ_le 2) hCq_nn)
      have hOm_nn : 0 ≤ (2 * Real.pi / 3 + 4 / xiStar * C_strip_om) := by
        have := hC_strip_om_eq; subst this; positivity [Real.pi_pos, xiStar_pos, hC_om_pos]
      have hxi4_nn : (0 : ℝ) ≤ 4 / xiStar := by positivity [xiStar_pos]
      have hfac : 2 * Real.pi / 3 + 4 / xiStar * ‖chartOmega ζ‖ ≤ 2 * Real.pi / 3 + 4 / xiStar * C_strip_om :=
        add_le_add_right (mul_le_mul_of_nonneg_left hOm_bd hxi4_nn) (2 * Real.pi / 3)
      calc |(chartPhiV ζ b).re - j10H ζ|
          ≤ (2 * Real.pi / 3 + 4 / xiStar * ‖chartOmega ζ‖) * ‖b - (xiStar : ℂ)‖ := hnorm.trans hsub
        _ ≤ (2 * Real.pi / 3 + 4 / xiStar * C_strip_om) * (C_q * ρ₀ ^ 2) :=
            mul_le_mul hfac hb_d (norm_nonneg _) hOm_nn
        _ = C_pert * ρ₀ ^ 2 := by rw [hC_pert_eq]; ring
        _ ≤ κ_strip := hρ₀_pert
    have hs_lb : -κ_strip ≤ (chartPhiV s b).re := (abs_le.mp hsad_abs).1
    have hζ_ub : (chartPhiV ζ b).re - j10H ζ ≤ κ_strip := (abs_le.mp hpert).2
    linarith only [hs_lb, hζ_ub, hJ10, hκ_strip_pos]
  -- Upper fixed segments P₃ -> P₂ -> P₁ -> P₀ (reversed j10GammaPlus)
  let P₀ : ℂ := j10P δ
  let P₁ : ℂ := (j10YDelta δ : ℂ) * (1 + Complex.I)
  let P₂ : ℂ := (1 / 2 : ℂ) * (1 + Complex.I)
  let P₃ : ℂ := (1 / 2 : ℂ) + Complex.I * (T₀ : ℂ)
  have hj10_0 := hJ10_pts 0 ⟨le_rfl, by norm_num⟩
  have hj10_1 := hJ10_pts 1 ⟨by norm_num, by norm_num⟩
  have hj10_2 := hJ10_pts 2 ⟨by norm_num, by norm_num⟩
  have hj10_3 := hJ10_pts 3 ⟨by norm_num, by norm_num⟩
  have hP0_eq : j10GammaPlus δ T₀ 0 = P₀ := by simp [j10GammaPlus, P₀]
  have hP1_eq : j10GammaPlus δ T₀ 1 = P₁ := by simp [j10GammaPlus, P₁]
  have hP2_eq : j10GammaPlus δ T₀ 2 = P₂ := by
    simp only [j10GammaPlus, P₂, show ¬((2 : ℝ) ≤ 1) by norm_num, show (2 : ℝ) ≤ 2 by norm_num, ↓reduceIte]
    push_cast; ring
  have hP3_eq : j10GammaPlus δ T₀ 3 = P₃ := by
    simp only [j10GammaPlus, P₃, show ¬((3 : ℝ) ≤ 1) by norm_num, show ¬((3 : ℝ) ≤ 2) by norm_num, ↓reduceIte]
    push_cast; ring
  have hP0_re : 0 ≤ P₀.re ∧ P₀.re ≤ 1 / 2 := ⟨hP0_eq ▸ hj10_0.1, hP0_eq ▸ hj10_0.2.1⟩
  have hP1_re : 0 ≤ P₁.re ∧ P₁.re ≤ 1 / 2 := ⟨hP1_eq ▸ hj10_1.1, hP1_eq ▸ hj10_1.2.1⟩
  have hP2_re : 0 ≤ P₂.re ∧ P₂.re ≤ 1 / 2 := ⟨hP2_eq ▸ hj10_2.1, hP2_eq ▸ hj10_2.2.1⟩
  have hP3_re : 0 ≤ P₃.re ∧ P₃.re ≤ 1 / 2 := ⟨hP3_eq ▸ hj10_3.1, hP3_eq ▸ hj10_3.2.1⟩
  have hcγ_le_pi4 : c_γ ≤ Real.pi ^ 2 / 24 := by
    rw [hc_γ_eq]
    have hmin : min (c_neg / 2) (1 / (3 * √2)) ≤ 1 / 4 :=
      (min_le_left _ _).trans (by linarith only [hc_neg_le_half])
    nlinarith only [hmin, sq_nonneg Real.pi]
  have hJ10_pts_eps : ∀ u ∈ Icc (0 : ℝ) 3,
      let z := j10GammaPlus δ T₀ u
      let zm := j10GammaMinus δ T₀ u
      0 ≤ z.re ∧ z.re ≤ 1 / 2 ∧ 0 ≤ z.im ∧
      0 ≤ zm.re ∧ zm.re ≤ 1 / 2 ∧ zm.im ≤ 0 ∧
      j10H z ≤ j10H (j10P δ) ∧ j10H z ≤ -ε_J10 ∧
      j10H zm ≤ j10H (j10P δ) ∧ j10H zm ≤ -ε_J10 ∧
      0 ≤ (chartOmega z).re ∧ 0 ≤ (chartOmega zm).re := by
    simpa only [← hε_J10_eq] using hJ10_pts
  obtain ⟨upper_segs, hchain_up, hlen_up, hup_ba, hup_ω, hup_str, hup_ur, hup_nolr, hup_ar,
      hup_fs, hup_nocr, hup_kind⟩ :=
    zp_upper_case hCF_nn hη_an hF_id hη_bd hρF_pos hC_om_pos hC_om hC_om'_pos hC_om'
      hδ_pos hδ_14 hδ_rhoF hCF_delta hT₀_ge4 hκ_strip_pos hρ₀_pos hρ₀_delta hρ₀_arc
      hC_om_max_eq hC_om'_max_eq hCom'_max_nn hC_Γ_ge_om hc_Γ_le_j10 hC_d_ge_om hC_d_ge_T0
      hT0_pi_gt1 hCom_pi_le_Cd hCom_le_Cd hκ_strip_j10 hc_γ_pos hcγ_le_pi4 hκ_arc_eq
      hρ_nn hρ_le hφ_nn hφ_le rfl rfl hb_re_pos hradial_eta h_inner_om h_fixed_strip_H
      hJ10_pts_eps hJ10_om_lb rfl rfl rfl rfl hP0_re hP1_re hP2_re hP3_re
  -- Build lower half by cases on φ' ≥ π/4 vs φ' < π/4
  have hlower : ∃ lower_segs : List ContourSeg,
      ContourChained (chartOmega s) (chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ))) lower_segs ∧
      lower_segs.length ≤ 6 ∧
      (∀ S ∈ lower_segs, S.b - S.a ≤ 1) ∧
      (∀ S ∈ lower_segs, ∀ t ∈ Icc S.a S.b,
        0 ≤ (S.ω t).re ∧ c_Γ ≤ ‖S.ω t‖ ∧ ‖S.ω t‖ ≤ C_Γ ∧ ‖S.ω' t‖ ≤ C_d) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → ∀ t ∈ Icc S.a S.b,
        ‖S.ζ' t‖ ≤ C_d ∧ (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → S.kind ≠ .upperRay) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → S.kind = .lowerRay →
        ∃ t_max ≥ (0 : ℝ), S.a = 0 ∧ S.b = t_max ∧ t_max ≤ 11 * ρ ∧
          ∀ t ∈ Icc 0 t_max, ‖S.ζ t - s‖ = t ∧ ‖S.ζ' t‖ = 1 ∧
            (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - c_γ * ρ * t ^ 2) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → S.kind = .arcRadial →
        ∀ t ∈ Icc S.a S.b, (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - κ_arc * ρ ^ 3) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → S.kind = .fixedStrip →
        ∀ t ∈ Icc S.a S.b, (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - κ_strip) ∧
      (∀ S ∈ lower_segs, S.isStrip = false →
        ∀ t ∈ Icc S.a S.b,
          μ₀ ≤ (S.ω t).re ∧ crudeExponentEc (S.ω t) b ≤ (chartPhiV s b).re - c_γ * ρ * s.re ^ 2) ∧
      (∀ S ∈ lower_segs, S.isStrip = true → S.kind ≠ .crudeEdge) := by
    by_cases hφ_ge : Real.pi / 4 ≤ φ'
    · have hcγ_le : c_γ ≤ (Real.pi ^ 2 / 6) * (c_neg / 2) := by
        rw [hc_γ_eq]; exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
      have hc_neg_ub : c_neg ≤ -Real.cos (7 * Real.pi / 12) := hc_neg_eq ▸ min_le_left _ _
      have hP0m_re : 0 ≤ (starRingEnd ℂ P₀).re ∧ (starRingEnd ℂ P₀).re ≤ 1 / 2 := by simpa using hP0_re
      have hP1m_re : 0 ≤ (starRingEnd ℂ P₁).re ∧ (starRingEnd ℂ P₁).re ≤ 1 / 2 := by simpa using hP1_re
      have hP2m_re : 0 ≤ (starRingEnd ℂ P₂).re ∧ (starRingEnd ℂ P₂).re ≤ 1 / 2 := by simpa using hP2_re
      have hP3m_re : 0 ≤ (starRingEnd ℂ P₃).re ∧ (starRingEnd ℂ P₃).re ≤ 1 / 2 := by simpa using hP3_re
      exact zp_lower_caseA hCF_nn hη_an hF_id hη_bd hρF_pos hC_om_pos hC_om hC_om'_pos hC_om'
        hδ_pos hδ_14 hδ_rhoF hCF_delta hCF_delta_cneg hc_neg_pos hc_neg_le_half hc_neg_ub
        hT₀_ge4 hκ_strip_pos hρ₀_pos hρ₀_delta hρ₀_arc hC_om_max_eq hC_om'_max_eq hCom'_max_nn
        hC_Γ_ge_om hc_Γ_le_j10 hC_d_ge_om hC_d_ge_T0 hT0_pi_gt1 hCom_pi_le_Cd hCom_le_Cd
        hκ_strip_j10 hc_γ_pos hcγ_le hκ_arc_eq hρ_nn hρ_le hφ_ge hφ_le rfl rfl hb_re_pos
        hradial_eta h_inner_om h_fixed_strip_H hJ10_pts_eps hJ10_om_lb rfl rfl rfl rfl
        hP0m_re hP1m_re hP2m_re hP3m_re
    · have hφ_lt : φ' < Real.pi / 4 := not_le.mp hφ_ge
      have hcγ_leB : c_γ ≤ (Real.pi ^ 2 / 6) * (1 / (3 * √2)) := by
        rw [hc_γ_eq]; exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      have h_junc_H : ∀ {T₀' : ℝ}, T_junc ≤ T₀' → ∀ μ ∈ Icc (muStar / 2) (2 * muStar), ∃! x_L : ℝ,
          x_L ∈ Ioo 0 (1 / 2) ∧ (chartOmega ((x_L : ℂ) - Complex.I * (T₀' : ℂ))).re = μ ∧
          1 / 2 - x_L ≤ C_L / T₀' ∧ c_L * T₀' ^ 2 ≤ (chartOmega ((x_L : ℂ) - Complex.I * (T₀' : ℂ))).im ∧
          ∀ x ∈ Icc x_L (1 / 2), j10H ((x : ℂ) - Complex.I * (T₀' : ℂ)) ≤ -κ_J7 * T₀' := by
        intro T₀' hT₀'
        unfold j10H
        exact h_junc T₀' hT₀'
      exact zp_lower_caseB (T₀ := T₀) (κ_arc := κ_arc) hCF_nn hη_an hF_id hη_bd hρF_pos hC_om_pos hC_om hC_om'_pos hC_om'
        hc_mid_pos h_mid_lb h_junc_H h_inv_sq2 hδ_pos hδ_14 hδ_rhoF hδ_om hCF_delta
        hT₀_ge4 hT₀_Tjunc hT₀_mid_sq hT₀_yL_sq hκ_strip_pos hκ_strip_j7 hρ₀_pos hρ₀_delta
        hC_om_max_eq hC_om'_max_eq hCom'_max_nn hCom_max_nn hC_Γ_ge_om hC_Γ_ge_2om hC_Γ_ge_32
        hc_Γ_le_mu0 hc_Γ_le_1 hC_d_ge_om hC_d_ge_2mu hC_d_ge_T0 hT0_pi_gt1 hCom_le_Cd
        hc_γ_pos hcγ_leB hμ₀_eq hμ₀_pos hρ_nn hρ_le hφ_nn hφ_lt rfl rfl hb_im hb_re_pos hb_ne
        hb_norm_range h_inner_om h_fixed_strip_H
  rcases hlower with ⟨lower_segs, hchain_lo, hlen_lo, hlo_ba, hlo_ω, hlo_str, hlo_nour, hlo_lr,
    hlo_ar, hlo_fs, hlo_cr, hlo_kind⟩
  let segs : List ContourSeg := upper_segs ++ lower_segs
  have hcnt_segs : segs.length ≤ 12 := by
    dsimp [segs]; rw [List.length_append]
    linarith only [hlen_up, hlen_lo]
  have hba_segs : ∀ S ∈ segs, S.b - S.a ≤ 1 := fun S hS => by
    rw [List.mem_append] at hS
    rcases hS with hS | hS
    · exact hup_ba S hS
    · exact hlo_ba S hS
  have hlen_segs : contourLength segs ≤ C_len := by
    have h_seg_len : ∀ S ∈ segs, ∫ t in S.a..S.b, ‖S.ω' t‖ ≤ C_d := fun S hS => by
      have hω' : ∀ t ∈ Icc S.a S.b, ‖S.ω' t‖ ≤ C_d := fun t ht => by
        rw [List.mem_append] at hS
        rcases hS with hS | hS
        · exact (hup_ω S hS t ht).2.2.2
        · exact (hlo_ω S hS t ht).2.2.2
      have hba : S.b - S.a ≤ 1 := hba_segs S hS
      calc ∫ t in S.a..S.b, ‖S.ω' t‖ ≤ ∫ _t in S.a..S.b, C_d :=
            intervalIntegral.integral_mono_on S.hab
              ((S.hω'_cont.norm.mono (by rw [Set.uIcc_of_le S.hab])).intervalIntegrable)
              intervalIntegrable_const hω'
        _ = C_d * (S.b - S.a) := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
        _ ≤ C_d * 1 := mul_le_mul_of_nonneg_left hba hC_d_pos.le
        _ = C_d := mul_one _
    unfold contourLength
    have hmap_bd : (segs.map fun S => ∫ t in S.a..S.b, ‖S.ω' t‖).sum ≤
        (segs.map fun _ => C_d).sum :=
      List.sum_le_sum fun S hS => h_seg_len S hS
    have hconst : (segs.map fun _ => C_d).sum = (segs.length : ℝ) * C_d := by
      simp [List.sum_replicate, nsmul_eq_mul]
    calc (segs.map fun S => ∫ t in S.a..S.b, ‖S.ω' t‖).sum
        ≤ (segs.length : ℝ) * C_d := hmap_bd.trans_eq hconst
      _ ≤ 12 * C_d := mul_le_mul_of_nonneg_right (by exact_mod_cast hcnt_segs) hC_d_pos.le
      _ = C_len := hC_len_eq.symm
  refine ⟨segs, contourChained_append hchain_up hchain_lo, hlen_segs, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hcnt_segs, hba_segs, ?_⟩
  · intro S hS t ht
    rw [List.mem_append] at hS
    rcases hS with hS | hS
    · exact hup_ω S hS t ht
    · exact hlo_ω S hS t ht
  · intro S hS hstr t ht
    rw [List.mem_append] at hS
    rcases hS with hS | hS
    · exact hup_str S hS hstr t ht
    · exact hlo_str S hS hstr t ht
  · intro S hS hstr hkind
    rw [List.mem_append] at hS
    rcases hS with hS | hS
    · exact hup_ur S hS hstr hkind
    · exact absurd hkind (hlo_nour S hS hstr)
  · intro S hS hstr hkind
    rw [List.mem_append] at hS
    rcases hS with hS | hS
    · exact absurd hkind (hup_nolr S hS hstr)
    · exact hlo_lr S hS hstr hkind
  · intro S hS hstr hkind t ht
    rw [List.mem_append] at hS
    rcases hS with hS | hS
    · exact hup_ar S hS hstr hkind t ht
    · exact hlo_ar S hS hstr hkind t ht
  · intro S hS hstr hkind t ht
    rw [List.mem_append] at hS
    rcases hS with hS | hS
    · exact hup_fs S hS hstr hkind t ht
    · exact hlo_fs S hS hstr hkind t ht
  · intro S hS hfalse t ht
    rw [List.mem_append] at hS
    rcases hS with hS | hS
    · exact absurd hfalse (hup_nocr S hS)
    · exact hlo_cr S hS hfalse t ht
  · intro S hS hstr
    rw [List.mem_append] at hS
    rcases hS with hS | hS
    · exact hup_kind S hS hstr
    · exact hlo_kind S hS hstr

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.Contour.lemma_Zp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Zp

end FormalResearch.ModularBootstrap.Contour
