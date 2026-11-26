/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingHol
public import FormalResearch.SignUncertainty.FctDescentIbp

/-!
# Ray functions for the descent bound `(fct:F-38-bnd)`

Paper I (`constant_terms_five.tex`), proof of Lemma FCT.6 (1), steps (a)-(e): the ray functions `e^{cΦ_Mel}`, `Φ' = g_tan + L₁`, `W = K₀A_ε/(e^{cΦ}Φ')`, `N = K₀ D H_*/G_ε`, and the proved pieces `im_stripG_nonneg` ((a): `Im g_tan ≥ 0`), `norm_deriv_stripG_le` (`|Φ''| ≤ C`), `fctRayE_norm_le` ((c): monotone phase), `fctPhiC_ray_bound` ((b)-(e) assembly via `fctRay_ibp_bound`).

Class: proved.
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

/-- `e^{cΦ_Mel(t; ξ₁)}`. -/
noncomputable def fctRayE (c L1 : ℝ) (t : ℂ) : ℂ := Complex.exp (c * mellinPhi t (fctXi1 L1))

/-- `Φ'_Mel(t; ξ₁) = g_tan(t) + L₁`. -/
noncomputable def fctRayP (L1 : ℝ) (t : ℂ) : ℂ := stripG t + L1

lemma hasDerivAt_ray {f : ℂ → ℂ} {f' ζ : ℂ} {s : ℝ} (hf : HasDerivAt f f' (ζ + (s : ℂ) * Complex.I)) :
    HasDerivAt (fun s : ℝ => f (ζ + (s : ℂ) * Complex.I)) (Complex.I * f') s := by
  have h1 : HasDerivAt (fun s : ℝ => ζ + (s : ℂ) * Complex.I) (1 * Complex.I) s :=
    ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const Complex.I).const_add ζ
  have := HasDerivAt.scomp s hf h1
  rw [one_mul, smul_eq_mul] at this
  exact this

lemma log_pi_sq_fctXi1 (L1 : ℝ) : Complex.log (↑π ^ 2 * ↑(fctXi1 L1)) = L1 := by
  have h : (↑π ^ 2 * ↑(fctXi1 L1) : ℂ) = ((Real.exp L1 : ℝ) : ℂ) := by
    unfold fctXi1
    have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    push_cast
    field_simp
  rw [h, ← Complex.ofReal_log (Real.exp_pos L1).le, Real.log_exp]

lemma hasDerivAt_mellinPhi_fct (L1 : ℝ) {t : ℂ} (ht : |t.re| < 1) :
    HasDerivAt (fun t => mellinPhi t (fctXi1 L1)) (fctRayP L1 t) t := by
  have h := (hasDerivAt_stripS0Tilde ht).add ((hasDerivAt_id t).mul_const (Complex.log (↑π ^ 2 * ↑(fctXi1 L1))))
  rw [log_pi_sq_fctXi1] at h
  unfold mellinPhi fctRayP
  rw [log_pi_sq_fctXi1]
  rw [one_mul] at h
  exact h

lemma hasDerivAt_fctRayE (c L1 : ℝ) {t : ℂ} (ht : |t.re| < 1) :
    HasDerivAt (fctRayE c L1) ((c : ℂ) * fctRayP L1 t * fctRayE c L1 t) t := by
  have := ((hasDerivAt_mellinPhi_fct L1 ht).const_mul (c : ℂ)).cexp
  unfold fctRayE
  refine this.congr_deriv ?_
  ring

/-- **Monotone phase along the ray** (`fct:splitting` (1), `(c)`): if `Im g_tan(ζ + is) ≥ 0` for `s ≥ 0` then `‖e^{cΦ_Mel(ζ+is)}‖` is non-increasing in `s`. -/
lemma fctRayE_norm_le {c L1 : ℝ} (hc : 0 < c) {ζ : ℂ} (hre : |ζ.re| < 1)
    (him : ∀ s : ℝ, 0 ≤ s → 0 ≤ (stripG (ζ + (s : ℂ) * Complex.I)).im) (s : ℝ) (hs : 0 ≤ s) :
    ‖fctRayE c L1 (ζ + (s : ℂ) * Complex.I)‖ ≤ ‖fctRayE c L1 ζ‖ := by
  have hre' : ∀ s : ℝ, |(ζ + (s : ℂ) * Complex.I).re| < 1 := fun s => by simpa using hre
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ((c : ℂ) * mellinPhi (ζ + (s : ℂ) * Complex.I) (fctXi1 L1)).re)
      (-(c * (stripG (ζ + (s : ℂ) * Complex.I)).im)) s := fun s => by
    have h1 := hasDerivAt_ray (ζ := ζ) (s := s) (hasDerivAt_mellinPhi_fct L1 (hre' s))
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (h1.const_mul (c : ℂ))
    refine h2.congr_deriv ?_
    simp [fctRayP]
  have hanti : AntitoneOn (fun s : ℝ => ((c : ℂ) * mellinPhi (ζ + (s : ℂ) * Complex.I) (fctXi1 L1)).re) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (fun s _ => (hd s).continuousAt.continuousWithinAt)
      (fun s _ => (hd s).differentiableAt.differentiableWithinAt) fun s hs => ?_
    rw [(hd s).deriv]
    have := him s (le_of_lt (by simpa using hs))
    nlinarith
  unfold fctRayE
  rw [Complex.norm_exp, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
  simpa using this

/-- `Im (tan z / z) ≥ 0` for `z = x + iy`, `0 < x < π/2`, `y ≥ 0` (`x sinh y cosh y ≥ y sin x cos x`). -/
lemma im_tan_div_nonneg {x y : ℝ} (hx0 : 0 < x) (hx1 : x < π / 2) (hy : 0 ≤ y) :
    0 ≤ (Complex.tan ((x : ℂ) + (y : ℂ) * Complex.I) / ((x : ℂ) + (y : ℂ) * Complex.I)).im := by
  set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hz
  have hzre : z.re = x := by simp [hz]
  have hzim : z.im = y := by simp [hz]
  have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx1⟩
  have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_pos])
  have hcosh : 1 ≤ Real.cosh y := Real.one_le_cosh y
  have hsinh : y ≤ Real.sinh y := Real.self_le_sinh_iff.mpr hy
  have hs : Complex.sin z = ((Real.sin x * Real.cosh y : ℝ) : ℂ) + ((Real.cos x * Real.sinh y : ℝ) : ℂ) * Complex.I := by
    rw [hz, Complex.sin_add_mul_I]
    push_cast
    simp
  have hc : Complex.cos z = ((Real.cos x * Real.cosh y : ℝ) : ℂ) + (-(Real.sin x * Real.sinh y) : ℝ) * Complex.I := by
    rw [hz, Complex.cos_add_mul_I]
    push_cast
    simp
    ring
  have hcz : Complex.cos z ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    rw [hc] at h1 h2
    simp only [Complex.zero_re, Complex.zero_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at h1 h2
    have h2 : Real.sin x * Real.sinh y = 0 := by linarith
    have h1 : Real.cos x * Real.cosh y = 0 := by linarith
    have : 0 < Real.cos x * Real.cosh y := mul_pos hcx (by linarith)
    linarith
  have hz0 : z ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hzre] at this; simp at this; linarith
  rw [Complex.tan_eq_sin_div_cos, div_div, Complex.div_im]
  have hn : 0 < Complex.normSq (Complex.cos z * z) :=
    Complex.normSq_pos.mpr (mul_ne_zero hcz hz0)
  rw [← sub_div]
  refine div_nonneg ?_ hn.le
  rw [hs, hc, hz]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  have h3 : Real.cosh y ^ 2 - Real.sinh y ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq y
  have e : (Real.cos x * Real.sinh y) * (Real.cos x * Real.cosh y * x - -(Real.sin x * Real.sinh y) * y) -
      Real.sin x * Real.cosh y * (Real.cos x * Real.cosh y * y + -(Real.sin x * Real.sinh y) * x) =
      x * Real.sinh y * Real.cosh y - y * Real.sin x * Real.cos x := by
    have hs : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    linear_combination (x * Real.sinh y * Real.cosh y) * hs + (-(y * Real.sin x * Real.cos x)) * h3
  have hsc : Real.sin x * Real.cos x ≤ x := by
    have := Real.sin_le hx0.le
    nlinarith [mul_le_mul_of_nonneg_left (Real.cos_le_one x) hsx.le]
  have hsh : y ≤ Real.sinh y * Real.cosh y := by nlinarith
  have key : 0 ≤ x * Real.sinh y * Real.cosh y - y * Real.sin x * Real.cos x := by
    nlinarith [mul_le_mul_of_nonneg_left hsh hx0.le, mul_le_mul_of_nonneg_left hsc hy]
  linarith


/-- **`(a)` of `fct:splitting` (1)**: `Im g_tan(t) ≥ 0` for `0 < Re t < 1`, `Im t ≥ 0` (`arg tan(πt/2) ≥ arg(πt/2)`; the paper's strict inequality is not needed). -/
lemma im_stripG_nonneg {t : ℂ} (h0 : 0 < t.re) (h1 : t.re < 1) (hi : 0 ≤ t.im) : 0 ≤ (stripG t).im := by
  have ht : t ≠ 0 := fun h => by rw [h] at h0; simp at h0
  unfold stripG
  simp only [ht, ↓reduceIte]
  rw [Complex.log_im, Complex.arg_nonneg_iff]
  have hz : (π : ℂ) * t / 2 = ((π * t.re / 2 : ℝ) : ℂ) + ((π * t.im / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hz]
  exact im_tan_div_nonneg (by positivity) (by nlinarith [Real.pi_pos]) (by positivity)


/-- `‖sin w‖ ≥ sin(Re w)` for `0 ≤ Re w ≤ π` (`|sin(x+iy)|² = sin²x cosh²y + cos²x sinh²y ≥ sin²x`). -/
lemma sin_re_le_norm_sin {w : ℂ} (h0 : 0 ≤ w.re) (h1 : w.re ≤ π) : Real.sin w.re ≤ ‖Complex.sin w‖ := by
  have hw : w = ((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I := by apply Complex.ext <;> simp
  have hs : Complex.sin w = ((Real.sin w.re * Real.cosh w.im : ℝ) : ℂ) +
      ((Real.cos w.re * Real.sinh w.im : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [hw]
    rw [Complex.sin_add_mul_I]
    push_cast
    simp
  have hsx : 0 ≤ Real.sin w.re := Real.sin_nonneg_of_nonneg_of_le_pi h0 h1
  have hn : ‖Complex.sin w‖ ^ 2 = (Real.sin w.re * Real.cosh w.im) ^ 2 + (Real.cos w.re * Real.sinh w.im) ^ 2 := by
    rw [hs, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  have hc : 1 ≤ Real.cosh w.im := Real.one_le_cosh _
  have : Real.sin w.re ^ 2 ≤ ‖Complex.sin w‖ ^ 2 := by
    rw [hn]
    nlinarith [sq_nonneg (Real.cos w.re * Real.sinh w.im), mul_nonneg hsx (sub_nonneg.mpr hc),
      mul_nonneg (mul_nonneg hsx hsx) (sub_nonneg.mpr (one_le_pow₀ hc : 1 ≤ Real.cosh w.im ^ 2)) ]
  exact abs_le_of_sq_le_sq' this (norm_nonneg _) |>.2

/-- **`|Φ''| ≤ D₀`** (`fct:splitting` (1), `(e)`): `|g_tan'(t)| ≤ π/sin(5π/16) + 16/5` for `5/16 ≤ Re t ≤ 7/16`
(`g_tan' = π/sin(πt) - 1/t`). -/
lemma norm_deriv_stripG_le {t : ℂ} (h0 : 5 / 16 ≤ t.re) (h1 : t.re ≤ 7 / 16) :
    ‖deriv stripG t‖ ≤ π / Real.sin (5 * π / 16) + 16 / 5 := by
  rw [(hasDerivAt_stripG (by linarith) (by linarith)).deriv]
  have hpi := Real.pi_pos
  have hs5 : 0 < Real.sin (5 * π / 16) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hre : ((π : ℂ) * t).re = π * t.re := by simp
  have hsin : Real.sin (5 * π / 16) ≤ ‖Complex.sin ((π : ℂ) * t)‖ := by
    have := sin_re_le_norm_sin (w := (π : ℂ) * t) (by rw [hre]; positivity) (by rw [hre]; nlinarith)
    rw [hre] at this
    refine le_trans ?_ this
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by nlinarith) (by nlinarith)
  have ht : 5 / 16 ≤ ‖t‖ := (h0.trans (le_abs_self _)).trans (Complex.abs_re_le_norm t)
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    exact div_le_div_of_nonneg_left hpi.le hs5 hsin
  · rw [norm_div, norm_one]
    rw [div_le_iff₀ (by linarith)]
    nlinarith

/-- `W = K₀A_ε / (e^{cΦ} Φ')`, so that `K₀A_ε = c⁻¹ ∂_t(e^{cΦ}) W` (`fct:splitting` (1)): the paper's
`W(t) = (1-t)^{-1/2} e^{B_c(t)} D_{τ₁} (H_*/G_ε) (1 - L₁(1-φ_kill)/(g_tan + L₁))`. -/
noncomputable def fctRayW (K4 ε c L1 α : ℝ) (t : ℂ) : ℂ :=
  fctWarpKA K4 ε c L1 α t / (fctRayE c L1 t * fctRayP L1 t)

/-- `N(ζ) = K₀(ζ, ξ₁) D_{τ₁}(ζ) (H_*/G_ε)(ζ) = e^{cΦ(ζ)} A₀(ζ)` of the paper (`A₀ = (1-ζ)^{-1/2} e^{B_c} D H_*/G_ε`); `Φ_c = -i c ∫_0^∞ K₀A_ε(ζ+is) ds / N(ζ)`. -/
noncomputable def fctRayN (K4 ε c L1 α : ℝ) (ζ : ℂ) : ℂ :=
  mellinK0 c ζ (fctXi1 L1) * fctDcompAt K4 c α ζ * ctHG ε ζ

lemma isOpen_edgeStrip : IsOpen edgeStrip :=
  isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const

lemma strip_subset_edgeStrip' : strip ⊆ edgeStrip := fun t ht => by
  show |t.re| < 1
  rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]

lemma continuousOn_fctRayP (L1 : ℝ) : ContinuousOn (fctRayP L1) strip :=
  (differentiableOn_stripG.mono strip_subset_edgeStrip').continuousOn.add continuousOn_const

lemma differentiableOn_fctRayE (c L1 : ℝ) : DifferentiableOn ℂ (fctRayE c L1) strip := fun t ht =>
  (hasDerivAt_fctRayE c L1 (by
    have := strip_subset_edgeStrip' ht
    exact this)).differentiableAt.differentiableWithinAt

lemma fctRayE_ne_zero (c L1 : ℝ) (t : ℂ) : fctRayE c L1 t ≠ 0 := Complex.exp_ne_zero _

/-- `W` is holomorphic where `Φ' ≠ 0`. -/
lemma differentiableOn_fctRayW {K4 ε c L1 α : ℝ} (hc : 0 < c) (hD : DifferentiableOn ℂ (fctDcompAt K4 c α) strip) :
    DifferentiableOn ℂ (fctRayW K4 ε c L1 α) (strip ∩ fctRayP L1 ⁻¹' {0}ᶜ) := by
  unfold fctRayW
  have hs : strip ∩ fctRayP L1 ⁻¹' {0}ᶜ ⊆ strip := inter_subset_left
  exact ((fctWarpKA_differentiableOn hc hD).mono hs).div
    (((differentiableOn_fctRayE c L1).mono hs).mul
      ((differentiableOn_stripG.mono strip_subset_edgeStrip').add_const _ |>.mono hs))
    fun t ht => mul_ne_zero (fctRayE_ne_zero c L1 t) ht.2

lemma isOpen_stripP (L1 : ℝ) : IsOpen (strip ∩ fctRayP L1 ⁻¹' {0}ᶜ) :=
  (continuousOn_fctRayP L1).isOpen_inter_preimage isOpen_strip isOpen_compl_singleton

/-- **The ray bound** (`fct:splitting` (1), `(b)`-`(e)`): from the ray representation `ζ ∫₀¹ K₀A_ε(sζ) ds = -i ∫₀^∞ K₀A_ε(ζ + is) ds`, the monotone phase
`Im g_tan ≥ 0` (`im_stripG_nonneg`), `Im ζ ≥ 0`, `|Φ'| ≥ q`, `|Φ''| ≤ D` and the bounds `|W^{(j)}(ζ+is)| ≤ B₀ (‖N(ζ)‖/‖e^{cΦ(ζ)}‖) e^{-3s}`, `j = 0, 1, 2`:
`‖Φ_c(ζ) - e^{cΦ(ζ)} W(ζ)/N(ζ)‖ ≤ B₀ (1/q + (1/q + D/q²)/3)/c`. -/
theorem fctPhiC_ray_bound {K4 ε c L1 α B0 q D : ℝ} (hc : 0 < c) (hq : 0 < q) (hD0 : 0 ≤ D)
    (hD : DifferentiableOn ℂ (fctDcompAt K4 c α) strip) {ζ : ℂ} (hζ : ζ ∈ strip)
    (hN : fctRayN K4 ε c L1 α ζ ≠ 0)
    (hshift : ζ * ∫ s in (0 : ℝ)..1, mellinK0 c ((s : ℂ) * ζ) (fctXi1 L1) * fctWarpA K4 ε c L1 α ((s : ℂ) * ζ) =
      -(Complex.I * ∫ s in Ioi (0 : ℝ), fctWarpKA K4 ε c L1 α (ζ + (s : ℂ) * Complex.I)))
    (hy : 0 ≤ ζ.im)
    (hP : ∀ s : ℝ, 0 ≤ s → q ≤ ‖fctRayP L1 (ζ + (s : ℂ) * Complex.I)‖)
    (hP1 : ∀ s : ℝ, 0 ≤ s → ‖deriv stripG (ζ + (s : ℂ) * Complex.I)‖ ≤ D)
    (hW0 : ∀ s : ℝ, 0 ≤ s → ‖fctRayW K4 ε c L1 α (ζ + (s : ℂ) * Complex.I)‖ ≤
      B0 * (‖fctRayN K4 ε c L1 α ζ‖ / ‖fctRayE c L1 ζ‖) * Real.exp (-3 * s))
    (hW1 : ∀ s : ℝ, 0 ≤ s → ‖deriv (fctRayW K4 ε c L1 α) (ζ + (s : ℂ) * Complex.I)‖ ≤
      B0 * (‖fctRayN K4 ε c L1 α ζ‖ / ‖fctRayE c L1 ζ‖) * Real.exp (-3 * s))
    (hW2 : ∀ s : ℝ, 0 ≤ s → ‖deriv (deriv (fctRayW K4 ε c L1 α)) (ζ + (s : ℂ) * Complex.I)‖ ≤
      B0 * (‖fctRayN K4 ε c L1 α ζ‖ / ‖fctRayE c L1 ζ‖) * Real.exp (-3 * s)) :
    ‖fctPhiC K4 ε c L1 α ζ - fctRayE c L1 ζ * fctRayW K4 ε c L1 α ζ / fctRayN K4 ε c L1 α ζ‖ ≤
      B0 * (1 / q + (1 / q + D / q ^ 2) / 3) / c := by
  set W := fctRayW K4 ε c L1 α with hWdef
  set N := fctRayN K4 ε c L1 α ζ with hNdef
  set E0 := fctRayE c L1 ζ with hE0def
  have hζre : |ζ.re| < 1 := strip_subset_edgeStrip' hζ
  have him : ∀ s : ℝ, 0 ≤ s → 0 ≤ (stripG (ζ + (s : ℂ) * Complex.I)).im := fun s hs =>
    im_stripG_nonneg (by simpa using hζ.1) (by simpa using hζ.2) (by simpa using add_nonneg hy hs)
  have hray : ∀ s : ℝ, (ζ + (s : ℂ) * Complex.I) ∈ strip := fun s => by simpa [strip] using hζ
  have hrayU : ∀ s : ℝ, 0 ≤ s → (ζ + (s : ℂ) * Complex.I) ∈ strip ∩ fctRayP L1 ⁻¹' {0}ᶜ := fun s hs => by
    refine ⟨hray s, ?_⟩
    intro h
    have := hP s hs
    have h0 : fctRayP L1 (ζ + (s : ℂ) * Complex.I) = 0 := h
    rw [h0, norm_zero] at this; linarith
  have hU := isOpen_stripP L1
  have hWd := differentiableOn_fctRayW (ε := ε) (L1 := L1) (α := α) hc hD
  have hWan := hWd.analyticOnNhd hU
  have hW1an := hWan.deriv
  have hW2an := hW1an.deriv
  have hE0n : 0 < ‖E0‖ := norm_pos_iff.mpr (fctRayE_ne_zero c L1 ζ)
  -- the ray functions
  set e : ℝ → ℂ := fun s => fctRayE c L1 (ζ + (s : ℂ) * Complex.I) with he
  set w : ℝ → ℂ := fun s => W (ζ + (s : ℂ) * Complex.I) with hw
  set w1 : ℝ → ℂ := fun s => Complex.I * deriv W (ζ + (s : ℂ) * Complex.I) with hw1
  set w2 : ℝ → ℂ := fun s => Complex.I * (Complex.I * deriv (deriv W) (ζ + (s : ℂ) * Complex.I)) with hw2
  set p : ℝ → ℂ := fun s => fctRayP L1 (ζ + (s : ℂ) * Complex.I) with hp
  set p1 : ℝ → ℂ := fun s => Complex.I * deriv stripG (ζ + (s : ℂ) * Complex.I) with hp1
  have hed : ∀ s, 0 ≤ s → HasDerivAt e (Complex.I * (c : ℂ) * p s * e s) s := fun s _ => by
    have := hasDerivAt_ray (ζ := ζ) (s := s) (hasDerivAt_fctRayE c L1 (by simpa using hζre))
    refine this.congr_deriv ?_
    simp only [hp, he]; ring
  have hwd : ∀ s, 0 ≤ s → HasDerivAt w (w1 s) s := fun s hs =>
    hasDerivAt_ray (hWan _ (hrayU s hs)).differentiableAt.hasDerivAt
  have hw1d : ∀ s, 0 ≤ s → HasDerivAt w1 (w2 s) s := fun s hs => by
    have := hasDerivAt_ray (ζ := ζ) (s := s) (hW1an _ (hrayU s hs)).differentiableAt.hasDerivAt
    exact this.const_mul Complex.I
  have hpd : ∀ s, 0 ≤ s → HasDerivAt p (p1 s) s := fun s hs => by
    have hg : HasDerivAt stripG (deriv stripG (ζ + (s : ℂ) * Complex.I)) (ζ + (s : ℂ) * Complex.I) :=
      (differentiableOn_stripG.differentiableAt (isOpen_edgeStrip.mem_nhds (strip_subset_edgeStrip' (hray s)))).hasDerivAt
    exact hasDerivAt_ray (hg.add_const (L1 : ℂ))
  have hcw2 : ContinuousOn w2 (Ioi 0) := by
    have hm : MapsTo (fun s : ℝ => ζ + (s : ℂ) * Complex.I) (Ioi 0) (strip ∩ fctRayP L1 ⁻¹' {0}ᶜ) :=
      fun s hs => hrayU s (le_of_lt hs)
    exact (continuousOn_const.mul (continuousOn_const.mul (hW2an.continuousOn.comp (by fun_prop) hm)))
  have hcp1 : ContinuousOn p1 (Ioi 0) := by
    have han := (differentiableOn_stripG.analyticOnNhd isOpen_edgeStrip).deriv
    have hm : MapsTo (fun s : ℝ => ζ + (s : ℂ) * Complex.I) (Ioi 0) edgeStrip :=
      fun s hs => strip_subset_edgeStrip' (hray s)
    exact continuousOn_const.mul (han.continuousOn.comp (by fun_prop) hm)
  have hb : ∀ s, 0 ≤ s → ‖w s‖ ≤ (B0 * (‖N‖ / ‖E0‖)) * Real.exp (-3 * s) := hW0
  have hb1 : ∀ s, 0 ≤ s → ‖w1 s‖ ≤ (B0 * (‖N‖ / ‖E0‖)) * Real.exp (-3 * s) := fun s hs => by
    simp only [hw1, norm_mul, Complex.norm_I, one_mul]; exact hW1 s hs
  have hb2 : ∀ s, 0 ≤ s → ‖w2 s‖ ≤ (B0 * (‖N‖ / ‖E0‖)) * Real.exp (-3 * s) := fun s hs => by
    simp only [hw2, norm_mul, Complex.norm_I, one_mul]; exact hW2 s hs
  have hibp := fctRay_ibp_bound (c := c) (B := B0 * (‖N‖ / ‖E0‖)) (q := q) (D := D) hc hq hD0 hed hwd hw1d hpd hP
    (fun s hs => by simp only [hp1, norm_mul, Complex.norm_I, one_mul]; exact hP1 s hs)
    (fun s hs => by
      have h0 : e 0 = E0 := by simp [he, hE0def]
      rw [h0]; exact fctRayE_norm_le (L1 := L1) hc hζre him s hs) hb hb1 hb2 hcw2 hcp1
  have he0 : e 0 = E0 := by simp [he, hE0def]
  have hw0 : w 0 = W ζ := by simp [hw]
  rw [he0, hw0] at hibp
  have hJ : (∫ s in Ioi (0 : ℝ), p s * e s * w s) =
      ∫ s in Ioi (0 : ℝ), fctWarpKA K4 ε c L1 α (ζ + (s : ℂ) * Complex.I) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hPne : p s ≠ 0 := fun h => by
      have := hP s (le_of_lt hs)
      have h' : fctRayP L1 (ζ + (s : ℂ) * Complex.I) = 0 := h
      rw [h', norm_zero] at this; linarith
    have hEne : e s ≠ 0 := fctRayE_ne_zero c L1 _
    simp only [hw, hWdef, fctRayW]
    change p s * e s * (fctWarpKA K4 ε c L1 α (ζ + (s : ℂ) * Complex.I) / (e s * p s)) = _
    field_simp
  have hN' : mellinK0 c ζ (fctXi1 L1) ≠ 0 ∧ fctDcompAt K4 c α ζ ≠ 0 ∧ ctHG ε ζ ≠ 0 := by
    have := hN
    simp only [hNdef, fctRayN] at this
    exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul this), right_ne_zero_of_mul (left_ne_zero_of_mul this),
      right_ne_zero_of_mul this⟩
  have hΦ : fctPhiC K4 ε c L1 α ζ = -((c : ℂ) * Complex.I * ∫ s in Ioi (0 : ℝ), p s * e s * w s) / N := by
    rw [hJ]
    unfold fctPhiC fctPsi
    rw [hshift]
    simp only [hNdef, fctRayN]
    obtain ⟨h1, h2, h3⟩ := hN'
    field_simp
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hN0 : 0 < ‖N‖ := norm_pos_iff.mpr hN
  have hid : fctPhiC K4 ε c L1 α ζ - E0 * W ζ / N =
      -(((c : ℂ) * Complex.I / N) * ((∫ s in Ioi (0 : ℝ), p s * e s * w s) - Complex.I / c * E0 * W ζ)) := by
    rw [hΦ]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hid, norm_neg, norm_mul]
  have hnorm : ‖(c : ℂ) * Complex.I / N‖ = c / ‖N‖ := by
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hc]
  rw [hnorm]
  calc c / ‖N‖ * ‖(∫ s in Ioi (0 : ℝ), p s * e s * w s) - Complex.I / c * E0 * W ζ‖
      ≤ c / ‖N‖ * (‖E0‖ * (B0 * (‖N‖ / ‖E0‖)) * (1 / q + (1 / q + D / q ^ 2) / 3) / c ^ 2) := by
        gcongr
    _ = B0 * (1 / q + (1 / q + D / q ^ 2) / 3) / c := by
        field_simp

/-- info: 'FormalResearch.SignUncertainty.im_stripG_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms im_stripG_nonneg

/-- info: 'FormalResearch.SignUncertainty.norm_deriv_stripG_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_deriv_stripG_le

/-- info: 'FormalResearch.SignUncertainty.fctRayE_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctRayE_norm_le

/-- info: 'FormalResearch.SignUncertainty.fctPhiC_ray_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPhiC_ray_bound

end FormalResearch.SignUncertainty
