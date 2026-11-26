module

public import Mathlib
public import FormalResearch.SignUncertainty.CtRoscAssembly

/-!
# `ct:dyadic` (4), `(ct:rosc)`: the complex chart `φ_c` on the real axis (piece `T0` of `CtRoscBook`)

`constant_terms_lower.tex`, `ct:dyadic` (3)-(4).  The complex chart `φ_c = ctPhiC ctChartC1 ε c` is real on `[-R_max, R_max]`; its restriction
`ctPhiR` is a `C¹` increasing diffeomorphism with `φ' ∈ [1/2, 3/2]`, `|φ(u) - u| ≤ C c^{-1/3}` (`CtChartBody`), and `f_c = Ψ̃(φ)φ'` is real
there: `f_c(u) = hankelPsiR c f (φ u) · φ'(u)`.  The change of variables `x = φ(u)` on `(a, b) ⊂ (-R_max, R_max)`
(`ctPhiR_subst`) turns the `u`-integrals of `(ct:rosc)` into integrals of the Langer density `Re Ψ̃` over `x`.

All proved.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

/-- The real restriction `φ_c(u) = Re φ_c(u)` of the complex chart `φ_c` (`ctChartC1`). -/
noncomputable def ctPhiR (ε c u : ℝ) : ℝ := (ctPhiC ctChartC1 ε c (u : ℂ)).re

/-- The derivative `φ_c'(u) = Re φ_c'(u)` on the real axis. -/
noncomputable def ctPhiRD (ε c u : ℝ) : ℝ := (deriv (ctPhiC ctChartC1 ε c) (u : ℂ)).re

/-- `f_c(u) = Ψ̃(φ_c(u)) φ_c'(u)` for real `u` (real part, `ctFcC`). -/
noncomputable def ctFr (ε c : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ := hankelPsiR c f (ctPhiR ε c u) * ctPhiRD ε c u

/-- **The chart hypotheses of `(ct:rosc)` on the real axis**: `CtChartBody` for `ctChartC1` with a nonnegative constant `C`, `c ≥ 3·10⁶`
and `C c^{-1/3} ≤ 1/2`. -/
structure CtRealChartHyp (ε c C : ℝ) : Prop where
  body : CtChartBody ctChartC1 ε c C
  C_nn : 0 ≤ C
  hc : 3e6 ≤ c
  small : C * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2

namespace CtRealChartHyp

variable {ε c C : ℝ}

lemma c_pos (H : CtRealChartHyp ε c C) : 0 < c := by linarith [H.hc]

lemma Rm_pos (H : CtRealChartHyp ε c C) : 0 < ctRmax ctChartC1 c := ctRmax_pos ctChartC1_pos H.c_pos

lemma small' (H : CtRealChartHyp ε c C) : C * c ^ (-1 : ℝ) ≤ 1 / 2 := by
  have h1 : c ^ (-1 : ℝ) ≤ c ^ (-(1 / 3) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [H.hc]) (by norm_num)
  exact (mul_le_mul_of_nonneg_left h1 H.C_nn).trans H.small

/-- `R_max + C c^{-1/3} < A`: the chart maps the real window into the Langer disc. -/
lemma Rm_add_lt (H : CtRealChartHyp ε c C) : ctRmax ctChartC1 c + C * c ^ (-(1 / 3 : ℝ)) < langerRadius c := by
  have hc0 := H.c_pos
  have h1 := hankelBand_radius_ge_one H.hc
  have hp : 0 ≤ c ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
  have h2 : ctRmax ctChartC1 c ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
    unfold ctRmax
    have : 4 * ctChartC1 ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
      have := ctChartC1_le
      have := ctChartC1_pos
      nlinarith
    nlinarith
  linarith [H.small]

lemma ctPhiC_ofReal (H : CtRealChartHyp ε c C) {u : ℝ} (hu : |u| ≤ ctRmax ctChartC1 c) :
    ctPhiC ctChartC1 ε c (u : ℂ) = ((ctPhiR ε c u : ℝ) : ℂ) :=
  Complex.ext (by simp [ctPhiR]) (by simpa [ctPhiR] using H.body.2.2.1 u hu)

lemma abs_ctPhiR_sub_le (H : CtRealChartHyp ε c C) {u : ℝ} (hu : |u| ≤ ctRmax ctChartC1 c) :
    |ctPhiR ε c u - u| ≤ C * c ^ (-(1 / 3 : ℝ)) := by
  have h := (H.body.2.2.2 (u : ℂ) (by simpa [Complex.norm_real] using hu)).1
  have e : ctPhiC ctChartC1 ε c (u : ℂ) - u = ((ctPhiR ε c u - u : ℝ) : ℂ) := by
    rw [H.ctPhiC_ofReal hu]; push_cast; ring
  rwa [e, Complex.norm_real, Real.norm_eq_abs] at h

lemma abs_ctPhiR_lt (H : CtRealChartHyp ε c C) {u : ℝ} (hu : |u| ≤ ctRmax ctChartC1 c) :
    |ctPhiR ε c u| < langerRadius c := by
  have h := H.abs_ctPhiR_sub_le hu
  have := H.Rm_add_lt
  have h2 : |ctPhiR ε c u| ≤ |u| + |ctPhiR ε c u - u| := by
    calc |ctPhiR ε c u| = |u + (ctPhiR ε c u - u)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  linarith

lemma ctPhiR_hasDerivAt (H : CtRealChartHyp ε c C) {u : ℝ} (hu : |u| < ctRmax ctChartC1 c) :
    HasDerivAt (ctPhiR ε c) (ctPhiRD ε c u) u := by
  obtain ⟨⟨ρ0, hρ0, hd0⟩, -⟩ := ctPhiC_spec H.body.1
  have hmem : (u : ℂ) ∈ ball (0 : ℂ) ρ0 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith
  have hda := ((hd0 _ hmem).differentiableAt (isOpen_ball.mem_nhds hmem)).hasDerivAt
  exact hda.real_of_complex

lemma ctPhiRD_bounds (H : CtRealChartHyp ε c C) {u : ℝ} (hu : |u| ≤ ctRmax ctChartC1 c) :
    1 / 2 ≤ ctPhiRD ε c u ∧ ctPhiRD ε c u ≤ 3 / 2 := by
  have h := (H.body.2.2.2 (u : ℂ) (by simpa [Complex.norm_real] using hu)).2
  have h2 : |ctPhiRD ε c u - 1| ≤ 1 / 2 := by
    have := Complex.abs_re_le_norm (deriv (ctPhiC ctChartC1 ε c) (u : ℂ) - 1)
    have e : (deriv (ctPhiC ctChartC1 ε c) (u : ℂ) - 1).re = ctPhiRD ε c u - 1 := by simp [ctPhiRD]
    rw [e] at this
    linarith [H.small']
  have := abs_le.1 h2
  constructor <;> linarith [this.1, this.2]

lemma continuousOn_ctPhiR (H : CtRealChartHyp ε c C) :
    ContinuousOn (ctPhiR ε c) (Icc (-ctRmax ctChartC1 c) (ctRmax ctChartC1 c)) := by
  obtain ⟨⟨ρ0, hρ0, hd0⟩, -⟩ := ctPhiC_spec H.body.1
  intro u hu
  have hmem : (u : ℂ) ∈ ball (0 : ℂ) ρ0 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith [hu.1, hu.2]
  have hcc : ContinuousAt (ctPhiC ctChartC1 ε c) (u : ℂ) :=
    (hd0 _ hmem).continuousWithinAt.continuousAt (isOpen_ball.mem_nhds hmem)
  exact (Complex.continuous_re.continuousAt.comp (hcc.comp (Complex.continuous_ofReal.continuousAt))).continuousWithinAt

lemma ctPhiR_strictMonoOn (H : CtRealChartHyp ε c C) :
    StrictMonoOn (ctPhiR ε c) (Icc (-ctRmax ctChartC1 c) (ctRmax ctChartC1 c)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) H.continuousOn_ctPhiR fun x hx => ?_
  rw [interior_Icc] at hx
  have hx' : |x| < ctRmax ctChartC1 c := abs_lt.2 ⟨hx.1, hx.2⟩
  rw [(H.ctPhiR_hasDerivAt hx').deriv]
  linarith [(H.ctPhiRD_bounds hx'.le).1]

/-- **`f_c` is real on the real axis** (`ctFcC ↑u = ↑(Ψ̃(φ u) φ'(u))`, `|u| < R_max`). -/
lemma ctFcC_ofReal (H : CtRealChartHyp ε c C) {f : ℝ → ℝ} {u : ℝ} (hu : |u| < ctRmax ctChartC1 c) :
    ctFcC ctChartC1 ε c f (u : ℂ) = ((ctFr ε c f u : ℝ) : ℂ) := by
  have hc0 := H.c_pos
  obtain ⟨⟨ρ0, hρ0, hd0⟩, -⟩ := ctPhiC_spec H.body.1
  have hdim : (deriv (ctPhiC ctChartC1 ε c) (u : ℂ)).im = 0 :=
    deriv_im_eq_zero_of_real (r := ctRmax ctChartC1 c) (hd0.mono (ball_subset_ball hρ0.le))
      (fun y hy => H.body.2.2.1 y hy.le) hu
  have hD : deriv (ctPhiC ctChartC1 ε c) (u : ℂ) = ((ctPhiRD ε c u : ℝ) : ℂ) :=
    Complex.ext (by simp [ctPhiRD]) (by simpa using hdim)
  have hΨim : (hankelPsi c f (((ctPhiR ε c u : ℝ)) : ℂ)).im = 0 := by
    refine hankelPsi_real hc0 f (x := ctPhiR ε c u) (H.abs_ctPhiR_lt hu.le).le
  have hΨ : hankelPsi c f (((ctPhiR ε c u : ℝ)) : ℂ) = ((hankelPsiR c f (ctPhiR ε c u) : ℝ) : ℂ) :=
    Complex.ext (by simp [hankelPsiR]) (by simpa using hΨim)
  unfold ctFcC ctFr
  rw [H.ctPhiC_ofReal hu.le, hΨ, hD]
  push_cast; ring

lemma ctFcC_re (H : CtRealChartHyp ε c C) {f : ℝ → ℝ} {u : ℝ} (hu : |u| < ctRmax ctChartC1 c) :
    (ctFcC ctChartC1 ε c f (u : ℂ)).re = ctFr ε c f u := by
  rw [H.ctFcC_ofReal hu]; simp

/-- **Change of variables `x = φ_c(u)`** on `(a, b) ⊂ [-R_max, R_max]`:
`∫_{φ(a)}^{φ(b)} g(x) dx = ∫_a^b φ'(u) g(φ(u)) du` (set integrals over open intervals). -/
lemma ctPhiR_subst (H : CtRealChartHyp ε c C) {a b : ℝ} (ha : -ctRmax ctChartC1 c ≤ a)
    (hb : b ≤ ctRmax ctChartC1 c) (hab : a ≤ b) (g : ℝ → ℝ) :
    ∫ x in Ioo (ctPhiR ε c a) (ctPhiR ε c b), g x = ∫ u in Ioo a b, ctPhiRD ε c u * g (ctPhiR ε c u) := by
  have hsub : Icc a b ⊆ Icc (-ctRmax ctChartC1 c) (ctRmax ctChartC1 c) := Icc_subset_Icc ha hb
  have himg : ctPhiR ε c '' Ioo a b = Ioo (ctPhiR ε c a) (ctPhiR ε c b) := by
    apply Subset.antisymm
    · rintro _ ⟨u, hu, rfl⟩
      have hm := H.ctPhiR_strictMonoOn
      exact ⟨hm (hsub ⟨le_rfl, hab⟩) (hsub ⟨hu.1.le, hu.2.le⟩) hu.1,
        hm (hsub ⟨hu.1.le, hu.2.le⟩) (hsub ⟨hab, le_rfl⟩) hu.2⟩
    · exact intermediate_value_Ioo hab (H.continuousOn_ctPhiR.mono hsub)
  have hlt : ∀ u ∈ Ioo a b, |u| < ctRmax ctChartC1 c := fun u hu =>
    abs_lt.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hd : ∀ u ∈ Ioo a b, HasDerivWithinAt (ctPhiR ε c) (ctPhiRD ε c u) (Ioo a b) u := fun u hu =>
    (H.ctPhiR_hasDerivAt (hlt u hu)).hasDerivWithinAt
  have hinj : InjOn (ctPhiR ε c) (Ioo a b) :=
    H.ctPhiR_strictMonoOn.injOn.mono (fun u hu => hsub ⟨hu.1.le, hu.2.le⟩)
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj g
  rw [himg] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have hpos := (H.ctPhiRD_bounds (hlt u hu).le).1
  simp only [smul_eq_mul]
  rw [abs_of_pos (by linarith)]

end CtRealChartHyp

/-- info: 'FormalResearch.SignUncertainty.CtRealChartHyp.ctPhiR_subst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CtRealChartHyp.ctPhiR_subst

end FormalResearch.SignUncertainty
