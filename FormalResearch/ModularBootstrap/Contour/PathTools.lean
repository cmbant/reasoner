module

public import FormalResearch.ModularBootstrap.ChartGeometry.CompactEscape
public import FormalResearch.ModularBootstrap.Chart.ExponentAndSaddle
public import FormalResearch.ModularBootstrap.Chart.EvenAndFactorization
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Piecewise-Smooth Contours and Saddle Perturbation Helpers

Shared contour-segment representation (`ContourPieceKind`, `ContourSeg`, `contourIntegral`,
`contourLength`, `ContourChained`), primitive-based contour deformation on open balls
(`contourIntegral_eq_vertical_of_ball`), and elementary tip/perturbation bounds for `chartB` and
`chartPhiV` used in **Lemma Z'** (`SaddleContour.lean`), **Lemma D'** (`TruncationError.lean`),
and **Lemma Z** (`WindowEnvelope.lean`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Contour

open Chart ChartGeometry ComplexBessel

/-! ### Section 1: Piecewise-`C^1` contour segments and deformation -/

/-- Role of a segment in the Lemma Z' saddle contour (`vlo:Zp`). -/
inductive ContourPieceKind
  | upperRay
  | lowerRay
  | arcRadial
  | crudeEdge
  | fixedStrip
  deriving DecidableEq, Repr

/-- A `C^1` contour segment `[a, b] → ℂ` in the `ω`-plane (optionally pulled back from `stripClosed`). -/
structure ContourSeg where
  kind : ContourPieceKind
  a : ℝ
  b : ℝ
  hab : a ≤ b
  ω : ℝ → ℂ
  ω' : ℝ → ℂ
  hω_cont : ContinuousOn ω (Icc a b)
  hω_deriv : ∀ t ∈ Icc a b, HasDerivAt ω (ω' t) t
  hω'_cont : ContinuousOn ω' (Icc a b)
  isStrip : Bool
  ζ : ℝ → ℂ
  ζ' : ℝ → ℂ
  hζ_strip : isStrip = true → ∀ t ∈ Icc a b,
    0 ≤ (ζ t).re ∧ (ζ t).re ≤ 1 / 2 ∧ ω t = chartOmega (ζ t) ∧
    HasDerivAt ζ (ζ' t) t ∧ ContinuousOn ζ' (Icc a b) ∧
    ω' t = deriv chartOmega (ζ t) * ζ' t

/-- Line integral `∫_Γ f(ω) dω` along a list of contour segments. -/
noncomputable def contourIntegral (f : ℂ → ℂ) (segs : List ContourSeg) : ℂ :=
  (segs.map fun S => ∫ t in S.a..S.b, f (S.ω t) * S.ω' t).sum

/-- Total Euclidean length `∑ ∫ ‖ω'(t)‖ dt` in the `ω`-plane. -/
noncomputable def contourLength (segs : List ContourSeg) : ℝ :=
  (segs.map fun S => ∫ t in S.a..S.b, ‖S.ω' t‖).sum

/-- Predicate asserting that `segs` forms a continuous chained path from `ω₀` to `ω₁`. -/
def ContourChained : ℂ → ℂ → List ContourSeg → Prop
  | ω₀, ω₁, [] => ω₀ = ω₁
  | ω₀, ω₁, S :: rest => S.ω S.a = ω₀ ∧ ContourChained (S.ω S.b) ω₁ rest

lemma contourLength_nonneg (segs : List ContourSeg) : 0 ≤ contourLength segs := by
  unfold contourLength
  refine List.sum_nonneg ?_
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨S, _, rfl⟩ := hx
  exact intervalIntegral.integral_nonneg S.hab fun _ _ => norm_nonneg _

lemma contourIntegral_append (f : ℂ → ℂ) (s₁ s₂ : List ContourSeg) :
    contourIntegral f (s₁ ++ s₂) = contourIntegral f s₁ + contourIntegral f s₂ := by
  unfold contourIntegral
  rw [List.map_append, List.sum_append]

lemma contourChained_append {ω₀ ω₁ ω₂ : ℂ} {s₁ s₂ : List ContourSeg}
    (h₁ : ContourChained ω₀ ω₁ s₁) (h₂ : ContourChained ω₁ ω₂ s₂) :
    ContourChained ω₀ ω₂ (s₁ ++ s₂) := by
  induction s₁ generalizing ω₀ with
  | nil =>
    simp only [ContourChained] at h₁
    subst h₁
    exact h₂
  | cons S rest ih =>
    exact ⟨h₁.1, ih h₁.2⟩

/-- Reverses a single `ContourSeg` via `t ↦ S.a + S.b - t`. -/
noncomputable def reverseContourSeg (S : ContourSeg) (kind' : ContourPieceKind := S.kind) :
    ContourSeg where
  kind := kind'
  a := S.a
  b := S.b
  hab := S.hab
  ω := fun t => S.ω (S.a + S.b - t)
  ω' := fun t => -S.ω' (S.a + S.b - t)
  hω_cont := by
    refine S.hω_cont.comp (by fun_prop : Continuous (fun x : ℝ => S.a + S.b - x)).continuousOn
      fun t ht => ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
  hω_deriv := fun t ht => by
    have hsub : S.a + S.b - t ∈ Icc S.a S.b := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hd_lin : HasDerivAt (fun x : ℝ => S.a + S.b - x) (-1) t :=
      (hasDerivAt_id t).const_sub (S.a + S.b)
    exact ((S.hω_deriv _ hsub).scomp t hd_lin).congr_deriv (by simp)
  hω'_cont := (S.hω'_cont.comp (by fun_prop : Continuous (fun x : ℝ => S.a + S.b - x)).continuousOn
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩).neg
  isStrip := S.isStrip
  ζ := fun t => S.ζ (S.a + S.b - t)
  ζ' := fun t => -S.ζ' (S.a + S.b - t)
  hζ_strip := fun hs t ht => by
    have hsub : S.a + S.b - t ∈ Icc S.a S.b := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    obtain ⟨h0, h1, hω, hdz, hcz, hω'⟩ := S.hζ_strip hs _ hsub
    have hd_lin : HasDerivAt (fun x : ℝ => S.a + S.b - x) (-1) t :=
      (hasDerivAt_id t).const_sub (S.a + S.b)
    have hdz_comp : HasDerivAt (fun x : ℝ => S.ζ (S.a + S.b - x)) (-S.ζ' (S.a + S.b - t)) t :=
      (hdz.scomp t hd_lin).congr_deriv (by simp)
    refine ⟨h0, h1, hω, hdz_comp, ?_, ?_⟩
    · exact (hcz.comp (by fun_prop : Continuous (fun x : ℝ => S.a + S.b - x)).continuousOn
        fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩).neg
    · rw [hω']; ring

/-- Primitive evaluation on a chained contour `segs` inside an open set `U`. -/
lemma contourIntegral_eq_sub_of_primitive {U : Set ℂ} {f F : ℂ → ℂ} {ω₀ ω₁ : ℂ}
    (hf_cont : ContinuousOn f U) (hF : ∀ ω ∈ U, HasDerivAt F (f ω) ω)
    (segs : List ContourSeg) (hchain : ContourChained ω₀ ω₁ segs)
    (hmem : ∀ S ∈ segs, ∀ t ∈ Icc S.a S.b, S.ω t ∈ U) :
    contourIntegral f segs = F ω₁ - F ω₀ := by
  induction segs generalizing ω₀ with
  | nil =>
    simp only [ContourChained] at hchain
    subst hchain
    simp [contourIntegral]
  | cons S rest ih =>
    have hS_mem : ∀ t ∈ Icc S.a S.b, S.ω t ∈ U := hmem S (by simp)
    have hrest_mem : ∀ S' ∈ rest, ∀ t ∈ Icc S'.a S'.b, S'.ω t ∈ U :=
      fun S' hS' => hmem S' (by simp [hS'])
    have hih := ih hchain.2 hrest_mem
    have hF_seg : ∫ t in S.a..S.b, f (S.ω t) * S.ω' t = F (S.ω S.b) - F (S.ω S.a) := by
      have hcont_comp : ContinuousOn (fun t => F (S.ω t)) (Icc S.a S.b) :=
        fun t ht => ((hF _ (hS_mem t ht)).continuousAt.comp_continuousWithinAt
          (S.hω_cont t ht))
      have hderiv_comp : ∀ t ∈ Ioo S.a S.b,
          HasDerivAt (fun x => F (S.ω x)) (f (S.ω t) * S.ω' t) t := fun t ht =>
        (hF _ (hS_mem t (Ioo_subset_Icc_self ht))).comp t (S.hω_deriv t (Ioo_subset_Icc_self ht))
      have hint_cont : ContinuousOn (fun t => f (S.ω t) * S.ω' t) (Icc S.a S.b) :=
        (hf_cont.comp S.hω_cont hS_mem).mul S.hω'_cont
      have hint : IntervalIntegrable (fun t => f (S.ω t) * S.ω' t) volume S.a S.b :=
        (hint_cont.mono (by rw [Set.uIcc_of_le S.hab])).intervalIntegrable
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le S.hab hcont_comp hderiv_comp hint
    unfold contourIntegral at hih ⊢
    simp only [List.map_cons, List.sum_cons, hF_seg, hchain.1] at hih ⊢
    rw [hih]
    ring

/-- Deforms `contourIntegral f segs` onto the straight segment `[ω₀, ω₁]` when both lie in a
common ball `ball B R` on which `f` is `DifferentiableOn`. -/
lemma contourIntegral_eq_segment_of_ball {B : ℂ} {R : ℝ} {f : ℂ → ℂ} {ω₀ ω₁ : ℂ}
    (hf : DifferentiableOn ℂ f (ball B R)) (segs : List ContourSeg)
    (hchain : ContourChained ω₀ ω₁ segs)
    (hmem_segs : ∀ S ∈ segs, ∀ t ∈ Icc S.a S.b, S.ω t ∈ ball B R)
    (hω₀ : ω₀ ∈ ball B R) (hω₁ : ω₁ ∈ ball B R) :
    contourIntegral f segs =
      ∫ t in (0 : ℝ)..1, f ((1 - (t : ℂ)) * ω₀ + (t : ℂ) * ω₁) * (ω₁ - ω₀) := by
  obtain ⟨F, hF⟩ := hf.isExactOn_ball
  have hL := contourIntegral_eq_sub_of_primitive hf.continuousOn hF segs hchain hmem_segs
  let γ : ℝ → ℂ := fun t => (1 - (t : ℂ)) * ω₀ + (t : ℂ) * ω₁
  have hγ_mem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ ball B R := fun t ht => by
    have hcv := (convex_ball B R).add_smul_sub_mem hω₀ hω₁ ht
    have heq : γ t = ω₀ + t • (ω₁ - ω₀) := by
      simp only [γ, Complex.real_smul]; ring
    rwa [heq]
  have hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1) := by
    dsimp [γ]; fun_prop
  have hγ_deriv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt γ (ω₁ - ω₀) t := fun t _ => by
    dsimp [γ]
    have h1 : HasDerivAt (fun x : ℝ => (1 - (x : ℂ)) * ω₀) (-ω₀) t := by
      have hc := ((hasDerivAt_const t (1 : ℂ)).sub Complex.ofRealCLM.hasDerivAt).mul_const ω₀
      simpa using hc
    have h2 : HasDerivAt (fun x : ℝ => (x : ℂ) * ω₁) ω₁ t := by
      simpa using Complex.ofRealCLM.hasDerivAt.mul_const ω₁
    exact (h1.add h2).congr_deriv (by ring)
  have hF_seg : ∫ t in (0 : ℝ)..1, f (γ t) * (ω₁ - ω₀) = F ω₁ - F ω₀ := by
    have hcont_F : ContinuousOn (fun t => F (γ t)) (Icc (0 : ℝ) 1) :=
      fun t ht => (hF _ (hγ_mem t ht)).continuousAt.comp_continuousWithinAt (hγ_cont t ht)
    have hderiv_F : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun x => F (γ x)) (f (γ t) * (ω₁ - ω₀)) t :=
      fun t ht => (hF _ (hγ_mem t (Ioo_subset_Icc_self ht))).comp t (hγ_deriv t ht)
    have hint_F : IntervalIntegrable (fun t => f (γ t) * (ω₁ - ω₀)) volume 0 1 :=
      ((hf.continuousOn.comp hγ_cont hγ_mem).mul continuousOn_const).mono
        (by rw [Set.uIcc_of_le zero_le_one]) |>.intervalIntegrable
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont_F hderiv_F hint_F
    simpa [γ] using heq
  exact hL.trans hF_seg.symm

/-! ### Section 2: Tip bounds for `chartB` and `chartPhiV` near `ζ = 0` -/

lemma re_deriv_bEven_neg_near_zero :
    ∃ r > 0, r ≤ rBEven / 2 ∧
      ∀ w ∈ ball (0 : ℂ) r, (deriv bEven w).re ≤ -(Real.pi / (8 * √2)) := by
  have hcont : ContinuousAt (fun w : ℂ => (deriv bEven w).re) 0 :=
    Complex.continuous_re.continuousAt.comp
      (analyticOnNhd_bEven.deriv 0 (mem_ball_self rBEven_pos)).continuousAt
  have h0 : (deriv bEven 0).re = -(Real.pi / (4 * √2)) := by
    rw [deriv_bEven_zero, Complex.neg_re, Complex.ofReal_re]
  have hlt : (deriv bEven 0).re < -(Real.pi / (8 * √2)) := by
    rw [h0]
    have hpi := Real.pi_pos
    have hs2 : 0 < √2 := Real.sqrt_pos.mpr zero_lt_two
    exact neg_lt_neg (div_lt_div_of_pos_left hpi (by positivity) (by linarith))
  obtain ⟨r₁, hr₁_pos, hr₁⟩ := Metric.eventually_nhds_iff_ball.mp
    (hcont.eventually (Iic_mem_nhds hlt))
  refine ⟨min r₁ (rBEven / 2), lt_min hr₁_pos (half_pos rBEven_pos), min_le_right _ _,
    fun w hw => hr₁ w (ball_subset_ball (min_le_left _ _) hw)⟩

lemma im_chartB_nonpos_firstQuadrant :
    ∃ r > 0, ∃ C ≥ 0,
      ∀ ζ ∈ ball (0 : ℂ) r, 0 ≤ ζ.re → 0 ≤ ζ.im →
        (chartB ζ).im ≤ 0 ∧
        xiStar / 2 ≤ (chartB ζ).re ∧
        ‖chartB ζ‖ ≤ 2 * xiStar ∧
        ‖chartB ζ - (xiStar : ℂ)‖ ≤ C * ‖ζ‖ ^ 2 := by
  obtain ⟨r_b, hr_b_pos, C_b, hCb_nn, hr_b_half, hr_b_ev, _, h_exp⟩ := chartB_even_expansion
  obtain ⟨r_ev, hr_ev_pos, hr_ev_half, h_deriv_neg⟩ := re_deriv_bEven_neg_near_zero
  let r₁ : ℝ := min (min r_b (1 / 2)) (min (√r_ev) (√(xiStar / (2 * (C_b + Real.pi / (4 * √2) + 1)))))
  have hr₁_pos : 0 < r₁ := by
    have := xiStar_pos
    exact lt_min (lt_min hr_b_pos (by norm_num))
      (lt_min (Real.sqrt_pos.mpr hr_ev_pos) (Real.sqrt_pos.mpr (by positivity)))
  let C : ℝ := C_b + Real.pi / (4 * √2)
  refine ⟨r₁, hr₁_pos, C, by positivity, fun ζ hζ hre him => ?_⟩
  have hζ_norm : ‖ζ‖ < r₁ := mem_ball_zero_iff.mp hζ
  have hζ_rb : ζ ∈ ball (0 : ℂ) r_b :=
    mem_ball_zero_iff.mpr (hζ_norm.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have hζ_sq_lt_rev : ‖ζ ^ 2‖ < r_ev := by
    rw [norm_pow]
    have hlt : ‖ζ‖ < √r_ev := hζ_norm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hsq := mul_self_lt_mul_self (norm_nonneg ζ) hlt
    rwa [← sq, Real.mul_self_sqrt hr_ev_pos.le] at hsq
  obtain ⟨hb_eq, h_quad⟩ := h_exp ζ hζ_rb
  have hnorm_sub : ‖chartB ζ - (xiStar : ℂ)‖ ≤ C * ‖ζ‖ ^ 2 := by
    have h1 : ‖(-(((Real.pi / (4 * √2) : ℝ) : ℂ))) * ζ ^ 2‖ = (Real.pi / (4 * √2)) * ‖ζ‖ ^ 2 := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_pow]
    have h2 := norm_add_le (chartB ζ - (xiStar : ℂ) - (-(((Real.pi / (4 * √2) : ℝ) : ℂ))) * ζ ^ 2)
      ((-(((Real.pi / (4 * √2) : ℝ) : ℂ))) * ζ ^ 2)
    rw [sub_add_cancel] at h2
    calc ‖chartB ζ - (xiStar : ℂ)‖ ≤ C_b * ‖ζ‖ ^ 4 + (Real.pi / (4 * √2)) * ‖ζ‖ ^ 2 := by
          linarith [h_quad, h1]
      _ ≤ C_b * ‖ζ‖ ^ 2 + (Real.pi / (4 * √2)) * ‖ζ‖ ^ 2 := by
          have hζ_lt1 : ‖ζ‖ ≤ 1 :=
            hζ_norm.le.trans ((min_le_left _ _).trans (min_le_right _ _)) |>.trans (by norm_num)
          have hsq_le1 : ‖ζ‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ζ]
          have h42 : ‖ζ‖ ^ 4 ≤ ‖ζ‖ ^ 2 := by
            calc ‖ζ‖ ^ 4 = ‖ζ‖ ^ 2 * ‖ζ‖ ^ 2 := by ring
              _ ≤ 1 * ‖ζ‖ ^ 2 := mul_le_mul_of_nonneg_right hsq_le1 (sq_nonneg _)
              _ = ‖ζ‖ ^ 2 := one_mul _
          gcongr
      _ = C * ‖ζ‖ ^ 2 := by dsimp [C]; ring
  have h_C_lt : C * ‖ζ‖ ^ 2 ≤ xiStar / 2 := by
    have hlt : ‖ζ‖ < √(xiStar / (2 * (C + 1))) :=
      hζ_norm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hsq : ‖ζ‖ ^ 2 < xiStar / (2 * (C + 1)) := by
      have hm := mul_self_lt_mul_self (norm_nonneg ζ) hlt
      rwa [← sq, Real.mul_self_sqrt (by positivity [xiStar_pos])] at hm
    have hC_pos : 0 < C + 1 := by positivity
    calc C * ‖ζ‖ ^ 2 ≤ (C + 1) * ‖ζ‖ ^ 2 := by nlinarith [sq_nonneg ‖ζ‖]
      _ ≤ (C + 1) * (xiStar / (2 * (C + 1))) := by gcongr
      _ = xiStar / 2 := by field_simp [hC_pos.ne']
  have hre_ge : xiStar / 2 ≤ (chartB ζ).re := by
    have h1 := (Complex.abs_re_le_norm (chartB ζ - (xiStar : ℂ))).trans hnorm_sub
    rw [Complex.sub_re, Complex.ofReal_re, abs_sub_le_iff] at h1
    linarith [h1.2]
  have hnorm_ub : ‖chartB ζ‖ ≤ 2 * xiStar := by
    calc ‖chartB ζ‖ ≤ ‖(xiStar : ℂ)‖ + ‖chartB ζ - (xiStar : ℂ)‖ := by
          simpa using norm_add_le (xiStar : ℂ) (chartB ζ - (xiStar : ℂ))
      _ ≤ xiStar + xiStar / 2 := by
          rw [Complex.norm_real, Real.norm_of_nonneg xiStar_pos.le]; linarith
      _ ≤ 2 * xiStar := by linarith [xiStar_pos]
  have him_nonpos : (chartB ζ).im ≤ 0 := by
    let w : ℂ := ζ ^ 2
    have hw_norm : ‖w‖ < r_ev := hζ_sq_lt_rev
    have hw_im_nn : 0 ≤ w.im := by
      dsimp [w]; rw [sq, Complex.mul_im]; nlinarith
    let γ : ℝ → ℂ := fun t => (w.re : ℂ) + Complex.I * ((t * w.im : ℝ) : ℂ)
    have hγ_ball : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ ball (0 : ℂ) r_ev := fun t ht => by
      rw [mem_ball_zero_iff]
      have hsq_norm : ‖γ t‖ ^ 2 ≤ ‖w‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
          Complex.normSq_apply]
        have hre_γ : (γ t).re = w.re := by simp [γ]
        have him_γ : (γ t).im = t * w.im := by simp [γ]
        rw [hre_γ, him_γ]
        have ht2 : (t * w.im) ^ 2 ≤ w.im ^ 2 := by
          calc (t * w.im) ^ 2 = t ^ 2 * w.im ^ 2 := by ring
            _ ≤ 1 * w.im ^ 2 := mul_le_mul_of_nonneg_right (by nlinarith [ht.1, ht.2]) (sq_nonneg _)
            _ = w.im ^ 2 := one_mul _
        linarith
      have hsqrt_le : √(‖γ t‖ ^ 2) ≤ √(‖w‖ ^ 2) := Real.sqrt_le_sqrt hsq_norm
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt_le
      exact hsqrt_le.trans_lt hw_norm
    have hγ_rBE : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ ball (0 : ℂ) rBEven := fun t ht =>
      ball_subset_ball (hr_ev_half.trans (half_le_self rBEven_pos.le)) (hγ_ball t ht)
    have hγ_deriv : ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => bEven (γ s)) (deriv bEven (γ t) * (Complex.I * (w.im : ℂ))) t :=
      fun t ht => by
        have hb_d := (analyticOnNhd_bEven _ (hγ_rBE t ht)).differentiableAt.hasDerivAt
        have hlin : HasDerivAt γ (Complex.I * (w.im : ℂ)) t := by
          have h1 : HasDerivAt (fun s : ℝ => ((s * w.im : ℝ) : ℂ)) (w.im : ℂ) t := by
            simpa using (hasDerivAt_id t |>.mul_const w.im).ofReal_comp
          exact (h1.const_mul Complex.I).const_add (w.re : ℂ) |>.congr_deriv (by ring)
        exact hb_d.comp t hlin
    have hftc : bEven (γ 1) - bEven (γ 0) =
        ∫ t in (0 : ℝ)..1, deriv bEven (γ t) * (Complex.I * (w.im : ℂ)) := by
      have hint_cont : ContinuousOn (fun t => deriv bEven (γ t) * (Complex.I * (w.im : ℂ))) (Icc 0 1) :=
        ((analyticOnNhd_bEven.deriv.continuousOn.comp
          (by dsimp [γ]; fun_prop) hγ_rBE)).mul continuousOn_const
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
        (fun t ht => (hγ_deriv t ht).continuousAt.continuousWithinAt)
        (fun t ht => hγ_deriv t (Ioo_subset_Icc_self ht))
        (hint_cont.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable).symm
    have hγ1 : γ 1 = w := by apply Complex.ext <;> simp [γ]
    have hγ0_im : (bEven (γ 0)).im = 0 := by
      have hre_lt : |w.re| < rBEven :=
        (Complex.abs_re_le_norm w).trans_lt (hw_norm.trans_le
          (hr_ev_half.trans (half_le_self rBEven_pos.le)))
      simpa [γ] using bEven_ofReal_im_zero hre_lt
    have him_eq : (chartB ζ).im =
        ∫ t in (0 : ℝ)..1, (deriv bEven (γ t) * (Complex.I * (w.im : ℂ))).im := by
      rw [hb_eq]
      have hsub_im : (bEven w).im = (bEven (γ 1) - bEven (γ 0)).im := by
        rw [hγ1, Complex.sub_im, hγ0_im, sub_zero]
      rw [hsub_im, hftc]
      have hint_c : IntervalIntegrable
          (fun t => deriv bEven (γ t) * (Complex.I * (w.im : ℂ))) volume 0 1 :=
        ((((analyticOnNhd_bEven.deriv.continuousOn.comp
          (by dsimp [γ]; fun_prop) hγ_rBE)).mul continuousOn_const).mono
          (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
      have hcomm := Complex.imCLM.intervalIntegral_comp_comm hint_c
      change (∫ t in (0 : ℝ)..1, (deriv bEven (γ t) * (Complex.I * (w.im : ℂ))).im) =
        (∫ t in (0 : ℝ)..1, deriv bEven (γ t) * (Complex.I * (w.im : ℂ))).im at hcomm
      exact hcomm.symm
    rw [him_eq]
    have h_int_nonpos : ∫ t in (0 : ℝ)..1, (deriv bEven (γ t) * (Complex.I * (w.im : ℂ))).im ≤
        ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
      have hint_re : IntervalIntegrable
          (fun t => (deriv bEven (γ t) * (Complex.I * (w.im : ℂ))).im) volume 0 1 := by
        have hcont_c : ContinuousOn (fun t => deriv bEven (γ t) * (Complex.I * (w.im : ℂ)))
            (Icc 0 1) :=
          ((analyticOnNhd_bEven.deriv.continuousOn.comp
            (by dsimp [γ]; fun_prop) hγ_rBE)).mul continuousOn_const
        exact ((Complex.continuous_im.continuousOn.comp hcont_c (Set.mapsTo_univ _ _)).mono
          (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
      refine intervalIntegral.integral_mono_on zero_le_one hint_re intervalIntegrable_const
        fun t ht => ?_
      · have him_d : (deriv bEven (γ t) * (Complex.I * (w.im : ℂ))).im =
            w.im * (deriv bEven (γ t)).re := by
          simp [Complex.mul_im, Complex.mul_re]; ring
        rw [him_d]
        have hd_neg := h_deriv_neg (γ t) (hγ_ball t ht)
        have hpi_neg : -(Real.pi / (8 * √2)) ≤ 0 := neg_nonpos.mpr (by positivity [Real.pi_pos])
        exact mul_nonpos_of_nonneg_of_nonpos hw_im_nn (hd_neg.trans hpi_neg)
    simpa using h_int_nonpos
  exact ⟨him_nonpos, hre_ge, hnorm_ub, hnorm_sub⟩

/-- Perturbation identity and bound comparing `Φ_V(ζ; b)` to `Φ_V(ζ; ξ_*)`. -/
lemma chartPhiV_sub_ref_le {ζ b : ℂ} (_h0 : 0 ≤ ζ.re) (_h1 : ζ.re ≤ 1)
    (hb_lb : xiStar / 2 ≤ b.re) (_hb_ub : ‖b‖ ≤ 2 * xiStar) :
    ‖chartPhiV ζ b - chartPhiV ζ (xiStar : ℂ)‖ ≤
      (2 * Real.pi / 3 + 4 / xiStar * ‖chartOmega ζ‖) * ‖b - (xiStar : ℂ)‖ := by
  have hb_ne : b ≠ 0 := fun h0' => by rw [h0', Complex.zero_re] at hb_lb; linarith [xiStar_pos]
  have hxi_ne : (xiStar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr xiStar_pos.ne'
  have heq : chartPhiV ζ b - chartPhiV ζ (xiStar : ℂ) =
      ((2 * Real.pi / 3 : ℝ) : ℂ) * (b - (xiStar : ℂ)) -
        2 * chartOmega ζ * (Complex.log b - Complex.log (xiStar : ℂ)) := by
    unfold chartPhiV stirlingJ tipL
    ring
  rw [heq]
  have hlog_bd : ‖Complex.log b - Complex.log (xiStar : ℂ)‖ ≤ (2 / xiStar) * ‖b - (xiStar : ℂ)‖ := by
    let seg : ℝ → ℂ := fun t => (1 - (t : ℂ)) * (xiStar : ℂ) + (t : ℂ) * b
    have hseg_re : ∀ t ∈ Icc (0 : ℝ) 1, xiStar / 2 ≤ (seg t).re := fun t ht => by
      dsimp [seg]
      simp only [Complex.mul_re, Complex.sub_re, Complex.one_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.one_im, zero_mul, sub_zero]
      nlinarith [ht.1, ht.2, xiStar_pos]
    have hseg_slit : ∀ t ∈ Icc (0 : ℝ) 1, seg t ∈ Complex.slitPlane := fun t ht =>
      Complex.mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le (half_pos xiStar_pos) (hseg_re t ht)))
    have hder : ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt (fun x : ℝ => Complex.log (seg x)) ((seg t)⁻¹ * (b - (xiStar : ℂ))) t :=
      fun t ht => by
        have hlin : HasDerivAt seg (b - (xiStar : ℂ)) t := by
          have h1' : HasDerivAt (fun x : ℝ => (1 - (x : ℂ)) * (xiStar : ℂ)) (-(xiStar : ℂ)) t := by
            simpa using (((hasDerivAt_const t (1 : ℂ)).sub Complex.ofRealCLM.hasDerivAt).mul_const _)
          have h2' : HasDerivAt (fun x : ℝ => (x : ℂ) * b) b t := by
            simpa using Complex.ofRealCLM.hasDerivAt.mul_const b
          exact (h1'.add h2').congr_deriv (by ring)
        exact (Complex.hasDerivAt_log (hseg_slit t ht)).comp t hlin
    have hcont_d : ContinuousOn (fun t => (seg t)⁻¹ * (b - (xiStar : ℂ))) (Icc (0 : ℝ) 1) :=
      ((continuousOn_inv₀.comp (by dsimp [seg]; fun_prop) fun t ht =>
        Complex.slitPlane_ne_zero (hseg_slit t ht))).mul continuousOn_const
    have hftc : Complex.log b - Complex.log (xiStar : ℂ) =
        ∫ t in (0 : ℝ)..1, (seg t)⁻¹ * (b - (xiStar : ℂ)) := by
      have heq' := (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
        (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
        (fun t ht => hder t (Ioo_subset_Icc_self ht))
        (hcont_d.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable).symm
      simpa [seg] using heq'
    rw [hftc]
    have hbd_integrand : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖(seg t)⁻¹ * (b - (xiStar : ℂ))‖ ≤ (2 / xiStar) * ‖b - (xiStar : ℂ)‖ := fun t ht => by
      rw [norm_mul, norm_inv]
      have hnorm_ge : xiStar / 2 ≤ ‖seg t‖ := (hseg_re t ht).trans (Complex.re_le_norm _)
      have hinv : ‖seg t‖⁻¹ ≤ 2 / xiStar := by
        rw [inv_eq_one_div, div_le_div_iff₀ (lt_of_lt_of_le (half_pos xiStar_pos) hnorm_ge) xiStar_pos]
        linarith
      exact mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
    calc ‖∫ t in (0 : ℝ)..1, (seg t)⁻¹ * (b - (xiStar : ℂ))‖
        ≤ ∫ t in (0 : ℝ)..1, ‖(seg t)⁻¹ * (b - (xiStar : ℂ))‖ :=
          intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ _t in (0 : ℝ)..1, (2 / xiStar) * ‖b - (xiStar : ℂ)‖ :=
          intervalIntegral.integral_mono_on zero_le_one
            (hcont_d.norm.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
            intervalIntegrable_const (fun t ht => hbd_integrand t ht)
      _ = (2 / xiStar) * ‖b - (xiStar : ℂ)‖ := by simp
  calc ‖((2 * Real.pi / 3 : ℝ) : ℂ) * (b - (xiStar : ℂ)) -
          2 * chartOmega ζ * (Complex.log b - Complex.log (xiStar : ℂ))‖
      ≤ ‖((2 * Real.pi / 3 : ℝ) : ℂ) * (b - (xiStar : ℂ))‖ +
          ‖2 * chartOmega ζ * (Complex.log b - Complex.log (xiStar : ℂ))‖ := norm_sub_le _ _
    _ = (2 * Real.pi / 3) * ‖b - (xiStar : ℂ)‖ +
          2 * ‖chartOmega ζ‖ * ‖Complex.log b - Complex.log (xiStar : ℂ)‖ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_of_nonneg (by positivity [Real.pi_pos])]
    _ ≤ (2 * Real.pi / 3) * ‖b - (xiStar : ℂ)‖ +
          2 * ‖chartOmega ζ‖ * ((2 / xiStar) * ‖b - (xiStar : ℂ)‖) := by gcongr
    _ = (2 * Real.pi / 3 + 4 / xiStar * ‖chartOmega ζ‖) * ‖b - (xiStar : ℂ)‖ := by ring

/-- Saddle-value bound `|(chartPhiV s (chartB s)).re| ≤ C_F * ‖s‖^3` for small `s` in the closed
first quadrant. -/
lemma chartPhiV_saddle_le :
    ∃ r > 0, ∃ C ≥ 0,
      ∀ s ∈ ball (0 : ℂ) r, 0 ≤ s.re → 0 ≤ s.im →
        ‖(chartPhiV s (chartB s)).re‖ ≤ C * ‖s‖ ^ 3 := by
  obtain ⟨r_q, hr_q_pos, C_q, hCq_nn, hq_props⟩ := im_chartB_nonpos_firstQuadrant
  obtain ⟨η, ρ_F, hρF_pos, C_F, hCF_nn, hη_an, _, hF_id, hη_bd⟩ := lemma_F
  let r₀ : ℝ := min (min r_q (ρ_F / 2)) (1 / 4)
  have hr₀_pos : 0 < r₀ := lt_min (lt_min hr_q_pos (half_pos hρF_pos)) (by norm_num)
  let C : ℝ := (Real.pi ^ 2 / 6) * (1 + 2 * C_F) + (8 * Real.pi / (3 * xiStar)) * C_q ^ 2
  refine ⟨r₀, hr₀_pos, C, by positivity [xiStar_pos], fun s hs hs_re hs_im => ?_⟩
  have hs_norm : ‖s‖ < r₀ := mem_ball_zero_iff.mp hs
  have hs_rq : s ∈ ball (0 : ℂ) r_q :=
    mem_ball_zero_iff.mpr (hs_norm.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have hs_F : s ∈ ball (0 : ℂ) ρ_F :=
    mem_ball_zero_iff.mpr ((hs_norm.trans_le ((min_le_left _ _).trans (min_le_right _ _))).trans
      (half_lt_self hρF_pos))
  have hs_14 : ‖s‖ < 1 / 4 := hs_norm.trans_le (min_le_right _ _)
  obtain ⟨_, hb_re, hb_ub, hb_sub⟩ := hq_props s hs_rq hs_re hs_im
  have hb_re_pos : 0 < (chartB s).re := lt_of_lt_of_le (half_pos xiStar_pos) hb_re
  have hb_ne : chartB s ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hb_re_pos; exact lt_irrefl 0 hb_re_pos
  -- Part 1: Φ_V(0; b) via E_c
  have hPhi0_re : |(chartPhiV 0 (chartB s)).re| ≤ (8 * Real.pi / (3 * xiStar)) * C_q ^ 2 * ‖s‖ ^ 4 := by
    have h0_eq : (0 : ℂ) = Complex.I * ((0 : ℝ) : ℂ) := by simp
    rw [h0_eq, re_chartPhiV_edge_eq_Ec, show Complex.I * ((0 : ℝ) : ℂ) = 0 by simp, chartOmega_zero]
    have hEc := crudeExponentEc_eq (ω := (muStar : ℂ)) (b := chartB s) (by simpa using muStar_pos) hb_ne
    have hmu : (3 * (muStar : ℂ).re / Real.pi) = xiStar := by
      unfold muStar; simp only [Complex.ofReal_re]; field_simp [Real.pi_pos.ne']
    have him0 : (muStar : ℂ).im = 0 := Complex.ofReal_im _
    rw [hmu, him0, mul_zero, add_zero] at hEc
    rw [hEc]
    have hnorm_b : 0 < ‖chartB s‖ := norm_pos_iff.mpr hb_ne
    have hD_nn : 0 ≤ crudeDivergenceD xiStar ‖chartB s‖ :=
      crudeDivergenceD_nonneg xiStar_pos hnorm_b
    have hD_ub : crudeDivergenceD xiStar ‖chartB s‖ ≤ (4 * Real.pi / (3 * xiStar)) * (‖chartB s‖ - xiStar) ^ 2 := by
      unfold crudeDivergenceD
      have hlog_lb := Real.one_sub_inv_le_log_of_pos (div_pos hnorm_b xiStar_pos)
      rw [inv_div] at hlog_lb
      have h1 : ‖chartB s‖ - xiStar - xiStar * Real.log (‖chartB s‖ / xiStar) ≤
          ‖chartB s‖ - xiStar - xiStar * (1 - xiStar / ‖chartB s‖) := by
        nlinarith [xiStar_pos]
      have h2 : ‖chartB s‖ - xiStar - xiStar * (1 - xiStar / ‖chartB s‖) =
          (‖chartB s‖ - xiStar) ^ 2 / ‖chartB s‖ := by
        field_simp [hnorm_b.ne']
      have hnorm_ge : xiStar / 2 ≤ ‖chartB s‖ := hb_re.trans (Complex.re_le_norm _)
      have hinv : 1 / ‖chartB s‖ ≤ 2 / xiStar := by
        rw [div_le_div_iff₀ hnorm_b xiStar_pos]; linarith
      have h2pi3_nn : 0 ≤ 2 * Real.pi / 3 := by positivity [Real.pi_pos]
      calc (2 * Real.pi / 3) * (‖chartB s‖ - xiStar - xiStar * Real.log (‖chartB s‖ / xiStar))
          ≤ (2 * Real.pi / 3) * ((‖chartB s‖ - xiStar) ^ 2 / ‖chartB s‖) :=
            mul_le_mul_of_nonneg_left (by linarith) h2pi3_nn
        _ = (2 * Real.pi / 3) * (‖chartB s‖ - xiStar) ^ 2 * (1 / ‖chartB s‖) := by ring
        _ ≤ (2 * Real.pi / 3) * (‖chartB s‖ - xiStar) ^ 2 * (2 / xiStar) :=
            mul_le_mul_of_nonneg_left hinv (mul_nonneg h2pi3_nn (sq_nonneg _))
        _ = (4 * Real.pi / (3 * xiStar)) * (‖chartB s‖ - xiStar) ^ 2 := by ring
    have hdiff_norm : |‖chartB s‖ - xiStar| ≤ C_q * ‖s‖ ^ 2 := by
      have h1 : |‖chartB s‖ - ‖(xiStar : ℂ)‖| ≤ ‖chartB s - (xiStar : ℂ)‖ := abs_norm_sub_norm_le _ _
      rw [Complex.norm_real, Real.norm_of_nonneg xiStar_pos.le] at h1
      exact h1.trans hb_sub
    have hgap_nn : 0 ≤ ‖chartB s‖ - (chartB s).re := sub_nonneg.mpr (Complex.re_le_norm _)
    have hgap_ub : ‖chartB s‖ - (chartB s).re ≤ (1 / xiStar) * (chartB s).im ^ 2 := by
      have hpos_sum : 0 < ‖chartB s‖ + (chartB s).re := add_pos hnorm_b hb_re_pos
      have hmul : (‖chartB s‖ - (chartB s).re) * (‖chartB s‖ + (chartB s).re) = (chartB s).im ^ 2 := by
        have := Complex.normSq_eq_norm_sq (chartB s)
        rw [Complex.normSq_apply] at this
        linarith
      have hge_sum : xiStar ≤ ‖chartB s‖ + (chartB s).re := by
        linarith [hb_re.trans (Complex.re_le_norm (chartB s))]
      rw [← eq_div_iff hpos_sum.ne'] at hmul
      rw [hmul, div_eq_mul_one_div, mul_comm ((chartB s).im ^ 2) _]
      exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le xiStar_pos hge_sum) (sq_nonneg _)
    have him_ub : |(chartB s).im| ≤ C_q * ‖s‖ ^ 2 := by
      have h1 := Complex.abs_im_le_norm (chartB s - (xiStar : ℂ))
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
      exact h1.trans hb_sub
    have habs_Ec : |crudeDivergenceD xiStar ‖chartB s‖ - (2 * Real.pi / 3) * (‖chartB s‖ - (chartB s).re)| ≤
        crudeDivergenceD xiStar ‖chartB s‖ + (2 * Real.pi / 3) * (‖chartB s‖ - (chartB s).re) := by
      calc |crudeDivergenceD xiStar ‖chartB s‖ - (2 * Real.pi / 3) * (‖chartB s‖ - (chartB s).re)|
          ≤ |crudeDivergenceD xiStar ‖chartB s‖| + |(2 * Real.pi / 3) * (‖chartB s‖ - (chartB s).re)| :=
            abs_sub _ _
        _ = crudeDivergenceD xiStar ‖chartB s‖ + (2 * Real.pi / 3) * (‖chartB s‖ - (chartB s).re) := by
            rw [abs_of_nonneg hD_nn, abs_of_nonneg (mul_nonneg (by positivity [Real.pi_pos]) hgap_nn)]
    have hsq1 : (‖chartB s‖ - xiStar) ^ 2 ≤ (C_q * ‖s‖ ^ 2) ^ 2 := by
      rw [← sq_abs (‖chartB s‖ - xiStar)]
      exact pow_le_pow_left₀ (abs_nonneg _) hdiff_norm 2
    have hsq2 : (chartB s).im ^ 2 ≤ (C_q * ‖s‖ ^ 2) ^ 2 := by
      rw [← sq_abs (chartB s).im]
      exact pow_le_pow_left₀ (abs_nonneg _) him_ub 2
    have h4pi : 0 ≤ 4 * Real.pi / (3 * xiStar) := by positivity [Real.pi_pos, xiStar_pos]
    have h1xi : 0 ≤ 1 / xiStar := by positivity [xiStar_pos]
    have h2pi3 : 0 ≤ 2 * Real.pi / 3 := by positivity [Real.pi_pos]
    calc |crudeDivergenceD xiStar ‖chartB s‖ - (2 * Real.pi / 3) * (‖chartB s‖ - (chartB s).re)|
        ≤ crudeDivergenceD xiStar ‖chartB s‖ + (2 * Real.pi / 3) * (‖chartB s‖ - (chartB s).re) := habs_Ec
      _ ≤ (4 * Real.pi / (3 * xiStar)) * (‖chartB s‖ - xiStar) ^ 2 +
            (2 * Real.pi / 3) * ((1 / xiStar) * (chartB s).im ^ 2) := by
          gcongr
      _ ≤ (4 * Real.pi / (3 * xiStar)) * (C_q * ‖s‖ ^ 2) ^ 2 +
            (2 * Real.pi / 3) * ((1 / xiStar) * (C_q * ‖s‖ ^ 2) ^ 2) := by
          gcongr
      _ = (2 * Real.pi / xiStar) * C_q ^ 2 * ‖s‖ ^ 4 := by ring
      _ ≤ (8 * Real.pi / (3 * xiStar)) * C_q ^ 2 * ‖s‖ ^ 4 := by
          have h28 : 2 * Real.pi / xiStar ≤ 8 * Real.pi / (3 * xiStar) := by
            rw [div_le_div_iff₀ xiStar_pos (by positivity [xiStar_pos])]
            nlinarith [Real.pi_pos, xiStar_pos]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h28 (sq_nonneg C_q)) (pow_nonneg (norm_nonneg s) 4)
  -- Part 2: ∫_0^1 (d/dt) Φ_V(t s; b) dt
  have hseg_deriv : ∀ t ∈ Icc (0 : ℝ) 1,
      ((t : ℂ) * s) ∈ ball (0 : ℂ) ρ_F ∧
      0 ≤ ((t : ℂ) * s).re ∧ ((t : ℂ) * s).re ≤ 1 / 4 := fun t ht => by
    have hts_norm : ‖(t : ℂ) * s‖ ≤ ‖s‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg s) ht.2
    refine ⟨mem_ball_zero_iff.mpr (hts_norm.trans_lt (mem_ball_zero_iff.mp hs_F)), ?_, ?_⟩
    · simp only [Complex.re_ofReal_mul]; exact mul_nonneg ht.1 hs_re
    · exact (Complex.re_le_norm _).trans_lt (hts_norm.trans_lt hs_14) |>.le
  let g : ℝ → ℂ := fun t => chartPhiV ((t : ℂ) * s) (chartB s)
  let g' : ℝ → ℂ := fun t => (2 * Complex.log (chartB ((t : ℂ) * s) / chartB s) *
    deriv chartOmega ((t : ℂ) * s)) * s
  have hg_cont : ContinuousOn g (Icc (0 : ℝ) 1) := fun t ht => by
    have h0 : 0 ≤ ((t : ℂ) * s).re := (hseg_deriv t ht).2.1
    have h1 : ((t : ℂ) * s).re ≤ 1 / 2 := (hseg_deriv t ht).2.2.trans (by norm_num)
    have hne : (t : ℂ) * s ≠ 1 / 2 := fun h0' => by
      have hre_le := (hseg_deriv t ht).2.2
      have := congrArg Complex.re h0'
      simp only [Complex.one_re, Complex.div_ofNat_re] at this
      linarith
    have hd := (lemma_S5_deriv hb_re_pos).2.2 _ h0 h1 hne
    have hm : MapsTo (fun x : ℝ => (x : ℂ) * s) (Icc 0 1) {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 / 2} :=
      fun x hx => ⟨(hseg_deriv x hx).2.1, (hseg_deriv x hx).2.2.trans (by norm_num)⟩
    have hc_in : ContinuousWithinAt (fun x : ℝ => (x : ℂ) * s) (Icc 0 1) t :=
      (Complex.continuous_ofReal.mul continuous_const).continuousWithinAt
    exact hd.continuousWithinAt.comp_of_eq hc_in hm rfl
  have hg_deriv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (g' t) t := fun t ht => by
    have ht_icc := Ioo_subset_Icc_self ht
    have h0 : 0 ≤ ((t : ℂ) * s).re := (hseg_deriv t ht_icc).2.1
    have h1 : ((t : ℂ) * s).re ≤ 1 / 2 := (hseg_deriv t ht_icc).2.2.trans (by norm_num)
    have hne : (t : ℂ) * s ≠ 1 / 2 := fun h0' => by
      have hre_le := (hseg_deriv t ht_icc).2.2
      have := congrArg Complex.re h0'
      simp only [Complex.one_re, Complex.div_ofNat_re] at this
      linarith
    have hd := (lemma_S5_deriv hb_re_pos).2.2 _ h0 h1 hne
    have hlin : HasDerivWithinAt (fun x : ℝ => (x : ℂ) * s) s (Ioo 0 1) t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const s).hasDerivWithinAt
    have hm : MapsTo (fun x : ℝ => (x : ℂ) * s) (Ioo 0 1) {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 / 2} :=
      fun x hx => ⟨(hseg_deriv x (Ioo_subset_Icc_self hx)).2.1,
        (hseg_deriv x (Ioo_subset_Icc_self hx)).2.2.trans (by norm_num)⟩
    exact (hd.comp t hlin hm).hasDerivAt (isOpen_Ioo.mem_nhds ht)
  have hg'_eq : EqOn g' (fun t =>
      (((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (((t : ℂ) * s) ^ 2 - s ^ 2) * (1 + η ((t : ℂ) * s) s)) * s)
      (Icc 0 1) := fun t ht => by
    dsimp [g']
    rw [hF_id ((t : ℂ) * s) (hseg_deriv t ht).1 s hs_F]
  have hg'_cont : ContinuousOn g' (Icc (0 : ℝ) 1) := by
    refine ContinuousOn.congr ?_ hg'_eq
    have hη_comp : ContinuousOn (fun t : ℝ => η ((t : ℂ) * s) s) (Icc (0 : ℝ) 1) := fun t ht => by
      have hpair : (((t : ℂ) * s, s) : ℂ × ℂ) ∈ ball (0 : ℂ × ℂ) ρ_F := by
        rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
        exact ⟨mem_ball_zero_iff.mp (hseg_deriv t ht).1, mem_ball_zero_iff.mp hs_F⟩
      have hc_map : Continuous (fun x : ℝ => ((x : ℂ) * s, s)) := by fun_prop
      have hc_at : ContinuousAt (Function.uncurry η) (((t : ℂ) * s, s)) :=
        (hη_an _ hpair).continuousAt
      exact (hc_at.comp_of_eq hc_map.continuousAt rfl).continuousWithinAt
    have hpoly : ContinuousOn (fun t : ℝ =>
        ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (((t : ℂ) * s) ^ 2 - s ^ 2)) (Icc (0 : ℝ) 1) := by fun_prop
    exact (hpoly.mul (continuousOn_const.add hη_comp)).mul continuousOn_const
  have hftc : chartPhiV s (chartB s) - chartPhiV 0 (chartB s) = ∫ t in (0 : ℝ)..1, g' t := by
    have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hg_cont hg_deriv
      (hg'_cont.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
    simpa [g] using h1.symm
  have hg'_bd : ∀ t ∈ Icc (0 : ℝ) 1, ‖g' t‖ ≤ (Real.pi ^ 2 / 6) * (1 + 2 * C_F) * ‖s‖ ^ 3 := by
    intro t ht
    rw [hg'_eq ht]
    have hη_b : ‖η ((t : ℂ) * s) s‖ ≤ C_F * (‖(t : ℂ) * s‖ + ‖s‖) :=
      hη_bd _ (hseg_deriv t ht).1 s hs_F
    have h1η : ‖1 + η ((t : ℂ) * s) s‖ ≤ 1 + 2 * C_F := by
      have hts_le : ‖(t : ℂ) * s‖ ≤ ‖s‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
        exact mul_le_of_le_one_left (norm_nonneg s) ht.2
      have hlt1 : ‖s‖ ≤ 1 := hs_14.le.trans (by norm_num)
      calc ‖1 + η ((t : ℂ) * s) s‖ ≤ 1 + ‖η ((t : ℂ) * s) s‖ := by
            simpa using norm_add_le 1 (η ((t : ℂ) * s) s)
        _ ≤ 1 + C_F * (‖(t : ℂ) * s‖ + ‖s‖) := by gcongr
        _ ≤ 1 + C_F * (1 + 1) := by
            have hsum_le : ‖(t : ℂ) * s‖ + ‖s‖ ≤ 1 + 1 := by linarith
            gcongr
        _ = 1 + 2 * C_F := by ring
    have hdiff_s : ‖((t : ℂ) * s) ^ 2 - s ^ 2‖ ≤ ‖s‖ ^ 2 := by
      have heq' : ((t : ℂ) * s) ^ 2 - s ^ 2 = (((t ^ 2 - 1 : ℝ) : ℂ)) * s ^ 2 := by
        push_cast; ring
      rw [heq', norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
      have habs : |t ^ 2 - 1| ≤ 1 := abs_le.mpr ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩
      calc |t ^ 2 - 1| * ‖s‖ ^ 2 ≤ 1 * ‖s‖ ^ 2 := by gcongr
        _ = ‖s‖ ^ 2 := one_mul _
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity [Real.pi_pos])]
    calc (Real.pi ^ 2 / 6) * ‖((t : ℂ) * s) ^ 2 - s ^ 2‖ * ‖1 + η ((t : ℂ) * s) s‖ * ‖s‖
        ≤ (Real.pi ^ 2 / 6) * ‖s‖ ^ 2 * (1 + 2 * C_F) * ‖s‖ := by gcongr
      _ = (Real.pi ^ 2 / 6) * (1 + 2 * C_F) * ‖s‖ ^ 3 := by ring
  have hdiff_re : |(chartPhiV s (chartB s)).re - (chartPhiV 0 (chartB s)).re| ≤
      (Real.pi ^ 2 / 6) * (1 + 2 * C_F) * ‖s‖ ^ 3 := by
    have h1 : |(chartPhiV s (chartB s)).re - (chartPhiV 0 (chartB s)).re| ≤
        ‖chartPhiV s (chartB s) - chartPhiV 0 (chartB s)‖ := by
      rw [← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    rw [hftc] at h1
    calc |(chartPhiV s (chartB s)).re - (chartPhiV 0 (chartB s)).re|
        ≤ ∫ t in (0 : ℝ)..1, ‖g' t‖ :=
          h1.trans (intervalIntegral.norm_integral_le_integral_norm zero_le_one)
      _ ≤ ∫ _t in (0 : ℝ)..1, (Real.pi ^ 2 / 6) * (1 + 2 * C_F) * ‖s‖ ^ 3 :=
          intervalIntegral.integral_mono_on zero_le_one
            (hg'_cont.norm.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
            intervalIntegrable_const (fun t ht => hg'_bd t ht)
      _ = (Real.pi ^ 2 / 6) * (1 + 2 * C_F) * ‖s‖ ^ 3 := by simp
  have hs43 : ‖s‖ ^ 4 ≤ ‖s‖ ^ 3 := by
    have hlt1 : ‖s‖ ≤ 1 := hs_14.le.trans (by norm_num)
    calc ‖s‖ ^ 4 = ‖s‖ * ‖s‖ ^ 3 := by ring
      _ ≤ 1 * ‖s‖ ^ 3 := mul_le_mul_of_nonneg_right hlt1 (pow_nonneg (norm_nonneg s) 3)
      _ = ‖s‖ ^ 3 := one_mul _
  calc ‖(chartPhiV s (chartB s)).re‖ = |(chartPhiV s (chartB s)).re| := Real.norm_eq_abs _
    _ ≤ |(chartPhiV s (chartB s)).re - (chartPhiV 0 (chartB s)).re| + |(chartPhiV 0 (chartB s)).re| := by
        simpa using abs_add_le ((chartPhiV s (chartB s)).re - (chartPhiV 0 (chartB s)).re)
          (chartPhiV 0 (chartB s)).re
    _ ≤ (Real.pi ^ 2 / 6) * (1 + 2 * C_F) * ‖s‖ ^ 3 +
          (8 * Real.pi / (3 * xiStar)) * C_q ^ 2 * ‖s‖ ^ 4 := add_le_add hdiff_re hPhi0_re
    _ ≤ (Real.pi ^ 2 / 6) * (1 + 2 * C_F) * ‖s‖ ^ 3 +
          (8 * Real.pi / (3 * xiStar)) * C_q ^ 2 * ‖s‖ ^ 3 := by
        gcongr; positivity [xiStar_pos]
    _ = C * ‖s‖ ^ 3 := by dsimp [C]; ring

end FormalResearch.ModularBootstrap.Contour
