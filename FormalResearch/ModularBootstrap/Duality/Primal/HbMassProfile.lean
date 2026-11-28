module

public import FormalResearch.ModularBootstrap.Duality.Primal.HbClustersExtras
public import FormalResearch.ModularBootstrap.Duality.Primal.HbClustersTheorem
public import FormalResearch.Complex.HadamardCauchy

/-!
# Profile sign lemmas and elementary MVT Taylor bounds (`dsl:hb-mass`)

Helper module for `HbMassMoments.lean`:
* `deriv_normProfile_tm_neg`: strictly negative derivative of `normProfile H.G` at `H.tm`;
* `iteratedDeriv2_normProfile_pos`: strictly positive second derivative at double zeros `z k ∉ H.S`;
* `lin_lower_bound_of_holo` and `quad_lower_bound_of_holo`: MVT linear/quadratic Taylor lower bounds.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.WeightAxioms FormalResearch.ModularBootstrap.ConcreteBootstrap
  FormalResearch.ModularBootstrap.FixedWeightTip FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Bessel
  FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.Hadamard
  FormalResearch.ArgPrinciple

lemma hasDerivAt_re_of_complex {f : ℂ → ℂ} {x : ℝ} {d : ℂ}
    (h : HasDerivAt f d (x : ℂ)) : HasDerivAt (fun t : ℝ => (f (t : ℂ)).re) d.re x :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h.comp_ofReal

private lemma hasDerivAt_ofReal_comp {g : ℝ → ℝ} {x d : ℝ}
    (h : HasDerivAt g d x) : HasDerivAt (fun t : ℝ => (g t : ℂ)) (d : ℂ) x :=
  Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x h

private lemma normProfile_real_im (H : HermiteBiehlerData) (x : ℝ) :
    (normProfile H.G (x : ℂ)).im = 0 := by
  unfold normProfile
  have h1 : H.G (x : ℂ) = ((H.G (x : ℂ)).re : ℂ) := Complex.ext rfl (H.G_real x)
  rw [h1]; simp

private lemma normProfile_nonneg_left (H : HermiteBiehlerData) {x : ℝ} (hx : x ≤ H.tm) :
    0 ≤ (normProfile H.G (x : ℂ)).re := by
  unfold normProfile
  have h1 : H.G (x : ℂ) = ((H.G (x : ℂ)).re : ℂ) := Complex.ext rfl (H.G_real x)
  rw [h1]; simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (inv_nonneg.mpr (hbExtremalProfile H).mass_pos.le) (H.G_nonneg_left x hx)

private lemma deriv_normProfile_real_im (H : HermiteBiehlerData) (x : ℝ) :
    (deriv (normProfile H.G) (x : ℂ)).im = 0 := by
  have hd : HasDerivAt (fun t : ℝ => normProfile H.G (t : ℂ)) (deriv (normProfile H.G) (x : ℂ)) x :=
    ((normProfile_differentiable (hbExtremalProfile H) (x : ℂ)).hasDerivAt).comp_ofReal
  have hd_re : HasDerivAt (fun t : ℝ => (normProfile H.G (t : ℂ)).re)
      (deriv (normProfile H.G) (x : ℂ)).re x :=
    hasDerivAt_re_of_complex (normProfile_differentiable (hbExtremalProfile H) (x : ℂ)).hasDerivAt
  have h_eq : (fun t : ℝ => normProfile H.G (t : ℂ)) =
      fun t : ℝ => ((normProfile H.G (t : ℂ)).re : ℂ) := funext fun t =>
    Complex.ext rfl (normProfile_real_im H t)
  have hd2 : HasDerivAt (fun t : ℝ => normProfile H.G (t : ℂ))
      (((deriv (normProfile H.G) (x : ℂ)).re : ℝ) : ℂ) x := by
    rw [h_eq]; exact hasDerivAt_ofReal_comp hd_re
  exact congrArg Complex.im (hd.unique hd2)

lemma normProfile_deriv_differentiable (H : HermiteBiehlerData) :
    Differentiable ℂ (deriv (normProfile H.G)) := by
  have han : AnalyticOnNhd ℂ (normProfile H.G) univ :=
    ((normProfile_differentiable (hbExtremalProfile H)).differentiableOn.analyticOnNhd isOpen_univ)
  exact differentiableOn_univ.mp (han.deriv.differentiableOn)

private lemma iteratedDeriv2_normProfile_real_im (H : HermiteBiehlerData) (x : ℝ) :
    (iteratedDeriv 2 (normProfile H.G) (x : ℂ)).im = 0 := by
  have hdiff : Differentiable ℂ (deriv (normProfile H.G)) := normProfile_deriv_differentiable H
  have hd : HasDerivAt (fun t : ℝ => deriv (normProfile H.G) (t : ℂ))
      (deriv (deriv (normProfile H.G)) (x : ℂ)) x :=
    (hdiff (x : ℂ)).hasDerivAt.comp_ofReal
  have hd_re : HasDerivAt (fun t : ℝ => (deriv (normProfile H.G) (t : ℂ)).re)
      (deriv (deriv (normProfile H.G)) (x : ℂ)).re x :=
    hasDerivAt_re_of_complex (hdiff (x : ℂ)).hasDerivAt
  have h_eq : (fun t : ℝ => deriv (normProfile H.G) (t : ℂ)) =
      fun t : ℝ => ((deriv (normProfile H.G) (t : ℂ)).re : ℂ) := funext fun t =>
    Complex.ext rfl (deriv_normProfile_real_im H t)
  have hd2 : HasDerivAt (fun t : ℝ => deriv (normProfile H.G) (t : ℂ))
      (((deriv (deriv (normProfile H.G)) (x : ℂ)).re : ℝ) : ℂ) x := by
    rw [h_eq]; exact hasDerivAt_ofReal_comp hd_re
  rw [iteratedDeriv_succ', iteratedDeriv_one]
  exact congrArg Complex.im (hd.unique hd2)

lemma deriv_normProfile_tm_neg (H : HermiteBiehlerData) :
    (deriv (normProfile H.G) (H.tm : ℂ)).re < 0 := by
  have hdiff := normProfile_differentiable (hbExtremalProfile H)
  have h0 : normProfile H.G (H.tm : ℂ) = 0 := by
    unfold normProfile; rw [H.G_eq_zero_on_S H.tm H.tm_mem, mul_zero]
  have hne : deriv (normProfile H.G) (H.tm : ℂ) ≠ 0 := by
    have hm : (((profileMass H.G)⁻¹ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (inv_ne_zero (hbExtremalProfile H).mass_pos.ne')
    have heq : normProfile H.G = fun z => (((profileMass H.G)⁻¹ : ℝ) : ℂ) * H.G z := rfl
    rw [heq, deriv_const_mul _ (H.G_diff (H.tm : ℂ))]
    exact mul_ne_zero hm (H.G_deriv_ne_zero H.tm H.tm_mem)
  have him : (deriv (normProfile H.G) (H.tm : ℂ)).im = 0 := deriv_normProfile_real_im H H.tm
  have hre_ne : (deriv (normProfile H.G) (H.tm : ℂ)).re ≠ 0 := fun h => hne (Complex.ext h him)
  have hd : HasDerivAt (fun t : ℝ => (normProfile H.G (t : ℂ)).re)
      (deriv (normProfile H.G) (H.tm : ℂ)).re H.tm :=
    hasDerivAt_re_of_complex (hdiff (H.tm : ℂ)).hasDerivAt
  have hslope : Tendsto (fun n : ℕ => ((normProfile H.G ((H.tm + -(((n : ℝ) + 1)⁻¹) : ℝ) : ℂ)).re -
      (normProfile H.G (H.tm : ℂ)).re) / (-(((n : ℝ) + 1)⁻¹)))
      atTop (𝓝 (deriv (normProfile H.G) (H.tm : ℂ)).re) := by
    have hs := hd.tendsto_slope_zero
    have hinv : Tendsto (fun n : ℕ => -(((n : ℝ) + 1)⁻¹)) atTop (𝓝[≠] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
        (Eventually.of_forall fun n => neg_ne_zero.mpr (by positivity))
      have h0 : Tendsto (fun n : ℕ => (-1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      exact h0.congr fun n => by ring
    refine (hs.comp hinv).congr fun n => ?_
    rw [Function.comp_apply, smul_eq_mul, ← div_eq_inv_mul]
  have hle0 : (deriv (normProfile H.G) (H.tm : ℂ)).re ≤ 0 := by
    refine le_of_tendsto hslope (Eventually.of_forall fun n => ?_)
    have hinv_pos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have hnn : 0 ≤ (normProfile H.G ((H.tm + -(((n : ℝ) + 1)⁻¹) : ℝ) : ℂ)).re :=
      normProfile_nonneg_left H (by linarith)
    rw [h0, Complex.zero_re, sub_zero]
    exact div_nonpos_of_nonneg_of_nonpos hnn (by linarith)
  exact lt_of_le_of_ne hle0 hre_ne

lemma iteratedDeriv2_normProfile_pos (H : HermiteBiehlerData) (CD : HbClusterData H)
    {k : Fin CD.K} (hkS : CD.z k ∉ H.S) :
    0 < (iteratedDeriv 2 (normProfile H.G) (CD.z k : ℂ)).re := by
  have hdiff := normProfile_differentiable (hbExtremalProfile H)
  have hord2 : analyticOrderNatAt (normProfile H.G) (CD.z k : ℂ) = 2 := by
    simpa [hkS] using CD.hord k
  have hzk_lt : CD.z k < H.tm := lt_of_not_ge fun h => hkS ((CD.hS_top k).mpr h)
  have han : AnalyticAt ℂ (normProfile H.G) (CD.z k : ℂ) := hdiff.analyticAt _
  have h_ord_eq : analyticOrderAt (normProfile H.G) (CD.z k : ℂ) = (2 : ℕ∞) := by
    have hne : analyticOrderAt (normProfile H.G) (CD.z k : ℂ) ≠ ⊤ := by
      intro htop
      have : analyticOrderNatAt (normProfile H.G) (CD.z k : ℂ) = 0 := by
        unfold analyticOrderNatAt; rw [htop]; rfl
      omega
    have h1 := ENat.natCast_toNat hne
    change (analyticOrderNatAt (normProfile H.G) (CD.z k : ℂ) : ℕ∞) = _ at h1
    rw [← h1, hord2]; rfl
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := han.analyticOrderAt_eq_natCast.mp h_ord_eq
  have hmul : normProfile H.G =ᶠ[𝓝 (CD.z k : ℂ)] fun z => (z - (CD.z k : ℂ)) ^ 2 * g z := by
    filter_upwards [hg_eq] with z hz; simpa [pow_two] using hz
  have hderiv_ev : deriv (normProfile H.G) =ᶠ[𝓝 (CD.z k : ℂ)]
      fun z => 2 * (z - (CD.z k : ℂ)) * g z + (z - (CD.z k : ℂ)) ^ 2 * deriv g z := by
    have h1 : deriv (normProfile H.G) =ᶠ[𝓝 (CD.z k : ℂ)]
        deriv (fun z => (z - (CD.z k : ℂ)) ^ 2 * g z) := hmul.deriv
    refine h1.trans ?_
    filter_upwards [hg_an.eventually_analyticAt] with z hga
    have ha : HasDerivAt (fun w : ℂ => (w - (CD.z k : ℂ)) ^ 2) (2 * (z - (CD.z k : ℂ))) z := by
      convert (((hasDerivAt_id z).sub_const (CD.z k : ℂ)).fun_pow 2) using 1
      simp only [id_eq]; norm_num
    have hmul_d : HasDerivAt (fun w : ℂ => (w - (CD.z k : ℂ)) ^ 2 * g w)
        (2 * (z - (CD.z k : ℂ)) * g z + (z - (CD.z k : ℂ)) ^ 2 * deriv g z) z :=
      ha.fun_mul hga.differentiableAt.hasDerivAt
    exact hmul_d.deriv
  have hd2_eq : iteratedDeriv 2 (normProfile H.G) (CD.z k : ℂ) = 2 * g (CD.z k : ℂ) := by
    rw [iteratedDeriv_succ', iteratedDeriv_one, hderiv_ev.deriv_eq]
    have h1 : HasDerivAt (fun z : ℂ => 2 * (z - (CD.z k : ℂ)) * g z) (2 * g (CD.z k : ℂ)) (CD.z k : ℂ) := by
      have ha : HasDerivAt (fun z : ℂ => 2 * (z - (CD.z k : ℂ))) 2 (CD.z k : ℂ) := by
        simpa using ((hasDerivAt_id (CD.z k : ℂ)).sub_const (CD.z k : ℂ)).const_mul 2
      simpa using ha.fun_mul hg_an.differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ => (z - (CD.z k : ℂ)) ^ 2 * deriv g z) 0 (CD.z k : ℂ) := by
      have ha : HasDerivAt (fun z : ℂ => (z - (CD.z k : ℂ)) ^ 2) 0 (CD.z k : ℂ) := by
        convert (((hasDerivAt_id (CD.z k : ℂ)).sub_const (CD.z k : ℂ)).fun_pow 2) using 1
        dsimp [id]; simp
      simpa using ha.fun_mul hg_an.deriv.differentiableAt.hasDerivAt
    simpa using (h1.fun_add h2).deriv
  have hg_re_nn : 0 ≤ (g (CD.z k : ℂ)).re := by
    let seq : ℕ → ℂ := fun n => ((CD.z k + (H.tm - CD.z k) / ((n : ℝ) + 2) : ℝ) : ℂ)
    have hseq : Tendsto seq atTop (𝓝 (CD.z k : ℂ)) := by
      have h0 : Tendsto (fun n : ℕ => CD.z k + (H.tm - CD.z k) / ((n : ℝ) + 2)) atTop (𝓝 (CD.z k)) := by
        have hdiv : Tendsto (fun n : ℕ => (H.tm - CD.z k) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa using tendsto_const_nhds.add hdiv
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp h0
    have hgre_tend : Tendsto (fun n : ℕ => (g (seq n)).re) atTop (𝓝 (g (CD.z k : ℂ)).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp (hg_an.continuousAt.tendsto.comp hseq)
    refine ge_of_tendsto hgre_tend ?_
    filter_upwards [hseq.eventually hmul] with n hn
    let t := (H.tm - CD.z k) / ((n : ℝ) + 2)
    have ht_pos : 0 < t := div_pos (sub_pos.mpr hzk_lt) (by positivity)
    have hle_tm : CD.z k + t ≤ H.tm := by
      have h1 : t ≤ H.tm - CD.z k := div_le_self (sub_pos.mpr hzk_lt).le (by linarith)
      linarith
    have hfn : normProfile H.G (seq n) = (t : ℂ) ^ 2 * g (seq n) := by
      rw [hn]; simp [seq, t]
    have hf_re : (normProfile H.G (seq n)).re = t ^ 2 * (g (seq n)).re := by
      rw [hfn, show (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) from by push_cast; rfl, Complex.re_ofReal_mul]
    have hf_nn : 0 ≤ (normProfile H.G (seq n)).re := normProfile_nonneg_left H hle_tm
    rw [hf_re] at hf_nn
    exact nonneg_of_mul_nonneg_right hf_nn (sq_pos_of_pos ht_pos)
  have h2g_ne : (2 * g (CD.z k : ℂ)).re ≠ 0 := by
    intro h0
    have him : (2 * g (CD.z k : ℂ)).im = 0 := by
      rw [← hd2_eq]; exact iteratedDeriv2_normProfile_real_im H (CD.z k)
    exact mul_ne_zero two_ne_zero hg_ne (Complex.ext h0 him)
  rw [hd2_eq]
  have hnn : 0 ≤ (2 * g (CD.z k : ℂ)).re := by
    simpa [Complex.mul_re] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hg_re_nn
  exact lt_of_le_of_ne hnn h2g_ne.symm

lemma lin_lower_bound_of_holo {F : ℂ → ℂ} {c0 R a u0 c1 : ℝ}
    (hF : DifferentiableOn ℂ F (ball (c0 : ℂ) R))
    (ha_le : a ≤ u0) (hsub : ∀ u ∈ Icc a u0, (u : ℂ) ∈ ball (c0 : ℂ) R)
    (h0 : (F (u0 : ℂ)).re = 0)
    (hd : ∀ u ∈ Icc a u0, (deriv F (u : ℂ)).re ≤ -c1) :
    ∀ u ∈ Icc a u0, c1 * (u0 - u) ≤ (F (u : ℂ)).re := by
  intro u hu
  let h : ℝ → ℝ := fun x => (F (x : ℂ)).re - c1 * (u0 - x)
  have hderiv : ∀ x ∈ Icc a u0, HasDerivAt h ((deriv F (x : ℂ)).re + c1) x := fun x hx => by
    have hFx : DifferentiableAt ℂ F (x : ℂ) := hF.differentiableAt (isOpen_ball.mem_nhds (hsub x hx))
    have hf_re : HasDerivAt (fun y : ℝ => (F (y : ℂ)).re) (deriv F (x : ℂ)).re x :=
      hasDerivAt_re_of_complex hFx.hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => c1 * (u0 - y)) (-c1) x := by
      simpa using ((hasDerivAt_const x u0).fun_sub (hasDerivAt_id x)).const_mul c1
    simpa [h, sub_eq_add_neg] using hf_re.fun_sub hlin
  have h_anti : AntitoneOn h (Icc a u0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a u0) ?_ ?_ fun x hx => ?_
    · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · have hx_sub := interior_subset hx
      rw [(hderiv x hx_sub).deriv]
      linarith [hd x hx_sub]
  have hle := h_anti hu ⟨ha_le, le_rfl⟩ hu.2
  dsimp [h] at hle
  rw [h0, sub_self, mul_zero, sub_zero] at hle
  linarith

lemma quad_lower_bound_of_holo {F : ℂ → ℂ} {c0 R a b u0 m0 : ℝ}
    (hF : DifferentiableOn ℂ F (ball (c0 : ℂ) R))
    (hu0 : u0 ∈ Icc a b) (hsub : ∀ u ∈ Icc a b, (u : ℂ) ∈ ball (c0 : ℂ) R)
    (h0 : (F (u0 : ℂ)).re = 0) (h1 : (deriv F (u0 : ℂ)).re = 0)
    (h2 : ∀ u ∈ Icc a b, m0 ≤ (iteratedDeriv 2 F (u : ℂ)).re) :
    ∀ u ∈ Icc a b, (m0 / 2) * (u - u0) ^ 2 ≤ (F (u : ℂ)).re := by
  have hdF : DifferentiableOn ℂ (deriv F) (ball (c0 : ℂ) R) := hF.deriv isOpen_ball
  let g : ℝ → ℝ := fun x => (F (x : ℂ)).re - (m0 / 2) * (x - u0) ^ 2
  let g' : ℝ → ℝ := fun x => (deriv F (x : ℂ)).re - m0 * (x - u0)
  have hg_d : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x := fun x hx => by
    have hFx : DifferentiableAt ℂ F (x : ℂ) := hF.differentiableAt (isOpen_ball.mem_nhds (hsub x hx))
    have hf_re : HasDerivAt (fun y : ℝ => (F (y : ℂ)).re) (deriv F (x : ℂ)).re x :=
      hasDerivAt_re_of_complex hFx.hasDerivAt
    have hsq : HasDerivAt (fun y : ℝ => (m0 / 2) * (y - u0) ^ 2) (m0 * (x - u0)) x := by
      convert (((hasDerivAt_id x).sub_const u0).fun_pow 2).const_mul (m0 / 2) using 1
      dsimp [id]; norm_num; ring
    exact hf_re.fun_sub hsq
  have hg'_d : ∀ x ∈ Icc a b, HasDerivAt g' ((iteratedDeriv 2 F (x : ℂ)).re - m0) x := fun x hx => by
    have hFx' : DifferentiableAt ℂ (deriv F) (x : ℂ) := hdF.differentiableAt (isOpen_ball.mem_nhds (hsub x hx))
    have hf'_re : HasDerivAt (fun y : ℝ => (deriv F (y : ℂ)).re) (iteratedDeriv 2 F (x : ℂ)).re x := by
      rw [iteratedDeriv_succ', iteratedDeriv_one]
      exact hasDerivAt_re_of_complex hFx'.hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => m0 * (y - u0)) m0 x := by
      simpa using ((hasDerivAt_id x).sub_const u0).const_mul m0
    exact hf'_re.fun_sub hlin
  have hg'_mono : MonotoneOn g' (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ fun x hx => ?_
    · exact fun x hx => (hg'_d x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hg'_d x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · have hx_sub := interior_subset hx
      rw [(hg'_d x hx_sub).deriv]
      linarith [h2 x hx_sub]
  have hg'0 : g' u0 = 0 := by dsimp [g']; rw [h1, sub_self, mul_zero, sub_zero]
  intro u hu
  rcases le_total u0 u with hle | hge
  · have hg_mono : MonotoneOn g (Icc u0 b) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc u0 b) ?_ ?_ fun x hx => ?_
      · exact fun x hx => (hg_d x ⟨hu0.1.trans hx.1, hx.2⟩).continuousAt.continuousWithinAt
      · exact fun x hx => (hg_d x ⟨hu0.1.trans (interior_subset hx).1, (interior_subset hx).2⟩).differentiableAt.differentiableWithinAt
      · have hx_sub : x ∈ Icc a b := ⟨hu0.1.trans (interior_subset hx).1, (interior_subset hx).2⟩
        rw [(hg_d x hx_sub).deriv, ← hg'0]
        exact hg'_mono hu0 hx_sub (interior_subset hx).1
    have hres := hg_mono ⟨le_rfl, hu0.2⟩ ⟨hle, hu.2⟩ hle
    dsimp [g] at hres
    rw [h0, sub_self, sq, mul_zero, mul_zero, sub_zero] at hres
    linarith
  · have hg_anti : AntitoneOn g (Icc a u0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc a u0) ?_ ?_ fun x hx => ?_
      · exact fun x hx => (hg_d x ⟨hx.1, hx.2.trans hu0.2⟩).continuousAt.continuousWithinAt
      · exact fun x hx => (hg_d x ⟨(interior_subset hx).1, (interior_subset hx).2.trans hu0.2⟩).differentiableAt.differentiableWithinAt
      · have hx_sub : x ∈ Icc a b := ⟨(interior_subset hx).1, (interior_subset hx).2.trans hu0.2⟩
        rw [(hg_d x hx_sub).deriv, ← hg'0]
        exact hg'_mono hx_sub hu0 (interior_subset hx).2
    have hres := hg_anti ⟨hu.1, hge⟩ ⟨hu0.1, le_rfl⟩ hge
    dsimp [g] at hres
    rw [h0, sub_self, sq, mul_zero, mul_zero, sub_zero] at hres
    linarith

end FormalResearch.ModularBootstrap.FixedWeight
