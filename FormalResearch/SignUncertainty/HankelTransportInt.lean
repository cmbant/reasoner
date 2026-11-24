module

public import FormalResearch.SignUncertainty.HankelTransport
public import FormalResearch.SignUncertainty.DeepLobeMass

/-!
# Integrated transport `(c)` of `gt:7.7p` and the mass hypotheses `(Q2)`

`ũ ↦ Δ = c ξ(ũ)` is a decreasing `C¹` bijection of the Langer disc onto a subinterval of `(0, ∞)`
(`hasDerivAt_hankelXi`, `hankelXiD_neg`).  Substituting in `hankel_transport_pointwise`:
`∫_a^b Re Ψ̃ = ∫_{cξ(b)}^{cξ(a)} ρ₀ f + O((b-a) r_∞)` (`hankel_transport_integral`).
-/

@[expose] public section

open Complex Set Filter Topology Metric MeasureTheory
open scoped Real Interval

namespace FormalResearch.SignUncertainty

/-- The disc radius `A = c^{2/3} κ · 4.94·10⁻⁴` (`R_dom(c)`). -/
noncomputable def langerRadius (c : ℝ) : ℝ := langerScale c * 4.94e-4

lemma langerRadius_pos {c : ℝ} (hc : 0 < c) : 0 < langerRadius c :=
  mul_pos (langerScale_pos hc) (by norm_num)

lemma hasDerivAt_hankelXi {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : |x| ≤ langerRadius c) :
    HasDerivAt (hankelXi c) (hankelXiD c x) x := by
  have hK0 := langerScale_pos hc
  set yr : ℝ := x / langerScale c with hyr
  have hyr_le : |yr| ≤ 4.94e-4 := by
    rw [hyr, abs_div, abs_of_pos hK0, div_le_iff₀ hK0]; unfold langerRadius at hx; linarith
  have hyn : ‖(yr : ℂ)‖ ≤ 4.94e-4 := by simpa using hyr_le
  obtain ⟨hw, hY⟩ := chartYinv_spec etaC (exists_chartY_small langerEta_etaC hyn)
  have hG : AnalyticAt ℂ (chartYinv etaC) (yr : ℂ) := by
    have := (analyticAt_chartYinv langerEta_etaC (mem_ball_zero_iff.1 hw)).1
    rwa [hY] at this
  have hd := hG.differentiableAt.hasDerivAt
  have hcast : (x : ℂ) / (langerScale c : ℂ) = (yr : ℂ) := by rw [hyr]; push_cast; rfl
  have hd' : HasDerivAt (chartYinv etaC) (deriv (chartYinv etaC) (yr : ℂ)) ((x : ℂ) / (langerScale c : ℂ)) := by
    rw [hcast]; exact hd
  have hlin : HasDerivAt (fun z : ℂ => z / (langerScale c : ℂ)) (1 / (langerScale c : ℂ)) (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).div_const (langerScale c : ℂ)
  have hcomp := hd'.comp (x : ℂ) hlin
  have hre := hcomp.real_of_complex
  have hfun : (fun x : ℝ => (((chartYinv etaC) ∘ fun z : ℂ => z / (langerScale c : ℂ)) (x : ℂ)).re) =
      fun x : ℝ => (chartYinv etaC (((x / langerScale c : ℝ)) : ℂ)).re := by
    funext x; simp only [Function.comp]; push_cast; rfl
  rw [hfun] at hre
  have hDc : starRingEnd ℂ (deriv (chartYinv etaC) (yr : ℂ)) = deriv (chartYinv etaC) (yr : ℂ) :=
    deriv_chartYinv_real hyr_le
  have hval : (deriv (chartYinv etaC) (yr : ℂ) * (1 / (langerScale c : ℂ))).re =
      (deriv (chartYinv etaC) (yr : ℂ)).re / langerScale c := by
    rw [show (1 / (langerScale c : ℂ)) = ((1 / langerScale c : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_mul_ofReal]
    ring
  rw [hval] at hre
  have := (hre.const_add 1).div_const (π ^ 2)
  unfold hankelXi hankelXiD
  convert this using 1
  field_simp
  rfl

lemma hankelXi_pos {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : |x| ≤ langerRadius c) : 0 < hankelXi c x := by
  obtain ⟨_, hwre⟩ := chartYinv_real_point hc (x := x) hx
  unfold hankelXi
  have := abs_le.1 hwre
  have : 0 < 1 + (chartYinv etaC (((x / langerScale c : ℝ)) : ℂ)).re := by linarith
  positivity

lemma hankelXiD_neg {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : |x| ≤ langerRadius c) : hankelXiD c x < 0 := by
  have hK0 := langerScale_pos hc
  set yr : ℝ := x / langerScale c with hyr
  have hyr_le : |yr| ≤ 4.94e-4 := by
    rw [hyr, abs_div, abs_of_pos hK0, div_le_iff₀ hK0]; unfold langerRadius at hx; linarith
  have hyn : ‖(yr : ℂ)‖ ≤ 4.94e-4 := by simpa using hyr_le
  obtain ⟨hw, hY⟩ := chartYinv_spec etaC (exists_chartY_small langerEta_etaC hyn)
  have hd := (analyticAt_chartYinv langerEta_etaC (mem_ball_zero_iff.1 hw)).2
  rw [hY] at hd
  have hneg := re_neg_chartYD_pos langerEta_etaC (mem_ball_zero_iff.1 hw).le
  unfold hankelXiD
  rw [← hyr, hd.deriv, Complex.inv_re]
  have hpos : 0 < Complex.normSq (chartYD etaC (chartYinv etaC (yr : ℂ))) := by
    apply Complex.normSq_pos.2
    intro h0; rw [h0] at hneg; simp at hneg
  have hre : (chartYD etaC (chartYinv etaC (yr : ℂ))).re < 0 := by
    simpa using hneg
  have : (chartYD etaC (chartYinv etaC (yr : ℂ))).re / Complex.normSq (chartYD etaC (chartYinv etaC (yr : ℂ))) < 0 :=
    div_neg_of_neg_of_pos hre hpos
  have hπ : 0 < π ^ 2 * langerScale c := by positivity
  exact div_neg_of_neg_of_pos this hπ

lemma continuousOn_hankelXiD {c : ℝ} (hc : 0 < c) :
    ContinuousOn (hankelXiD c) (Icc (-(langerRadius c)) (langerRadius c)) := by
  have hK0 := langerScale_pos hc
  intro x hx
  have hxa : |x| ≤ langerRadius c := abs_le.2 hx
  refine ContinuousAt.continuousWithinAt ?_
  set yr : ℝ := x / langerScale c with hyr
  have hyr_le : |yr| ≤ 4.94e-4 := by
    rw [hyr, abs_div, abs_of_pos hK0, div_le_iff₀ hK0]; unfold langerRadius at hxa; linarith
  have hyn : ‖(yr : ℂ)‖ ≤ 4.94e-4 := by simpa using hyr_le
  obtain ⟨hw, hY⟩ := chartYinv_spec etaC (exists_chartY_small langerEta_etaC hyn)
  have hG : AnalyticAt ℂ (chartYinv etaC) (yr : ℂ) := by
    have := (analyticAt_chartYinv langerEta_etaC (mem_ball_zero_iff.1 hw)).1
    rwa [hY] at this
  have hDc : ContinuousAt (deriv (chartYinv etaC)) (yr : ℂ) := hG.deriv.continuousAt
  have hlin : ContinuousAt (fun x : ℝ => (((x / langerScale c : ℝ)) : ℂ)) x := by fun_prop
  have := (hDc.comp (f := fun x : ℝ => (((x / langerScale c : ℝ)) : ℂ)) (x := x) (by simpa [hyr] using hlin))
  unfold hankelXiD
  exact (Complex.continuous_re.continuousAt.comp this).div_const _

lemma hankel_subst {c : ℝ} (hc : 0 < c) {a b : ℝ} (ha : |a| ≤ langerRadius c) (hb : |b| ≤ langerRadius c)
    (hab : a ≤ b) (g : ℝ → ℝ) :
    ∫ x in a..b, g (c * hankelXi c x) * (c * hankelXiD c x) =
      ∫ u in (c * hankelXi c a)..(c * hankelXi c b), g u := by
  have hmem : ∀ x ∈ Icc a b, |x| ≤ langerRadius c := fun x hx =>
    abs_le.2 ⟨by linarith [abs_le.1 ha |>.1, hx.1], by linarith [abs_le.1 hb |>.2, hx.2]⟩
  have hder : ∀ x ∈ Icc a b, HasDerivAt (fun x => c * hankelXi c x) (c * hankelXiD c x) x := fun x hx =>
    (hasDerivAt_hankelXi hc (hmem x hx)).const_mul c
  have hcont : ContinuousOn (fun x => c * hankelXi c x) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact fun x hx => (hder x hx).continuousAt.continuousWithinAt
  have := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (a := a) (b := b)
    (f := fun x => c * hankelXi c x) (f' := fun x => c * hankelXiD c x) (g := g) hcont
    (fun x hx => by
      rw [min_eq_left hab, max_eq_right hab] at hx
      exact hder x ⟨hx.1.le, hx.2.le⟩)
    (fun x hx => by
      rw [min_eq_left hab, max_eq_right hab] at hx
      exact mul_nonpos_of_nonneg_of_nonpos hc.le (hankelXiD_neg hc (hmem x ⟨hx.1.le, hx.2.le⟩)).le)
  simpa using this

/-- `Re Ψ̃` on the real axis of the Langer disc. -/
noncomputable def hankelPsiR (c : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := (hankelPsi c f (x : ℂ)).re

/-- The transport error `r_∞ = 2 I₀ c^{1/3} e^{-c/40000}`. -/
noncomputable def hankelRinf (c : ℝ) : ℝ := 2 * hankelTailI0 * c ^ (1 / 3 : ℝ) * Real.exp (-(c / 40000))

lemma continuousOn_hankelPsiR {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    ContinuousOn (hankelPsiR c f) (Icc (-(langerRadius c)) (langerRadius c)) := by
  have han := (analyticOnNhd_hankelPsi hc hf).continuousOn
  have h2 : ContinuousOn (fun x : ℝ => hankelPsi c f (x : ℂ)) (Icc (-(langerRadius c)) (langerRadius c)) :=
    han.comp Complex.continuous_ofReal.continuousOn (fun x hx => by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.2 hx)
  exact Complex.continuous_re.comp_continuousOn h2

lemma continuousOn_hankel_term {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    ContinuousOn (fun x => hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x) * (c * hankelXiD c x))
      (Icc (-(langerRadius c)) (langerRadius c)) := by
  intro x hx
  have hxa : |x| ≤ langerRadius c := abs_le.2 hx
  have hxi : 0 < c * hankelXi c x := mul_pos hc (hankelXi_pos hc hxa)
  have hXi : ContinuousAt (fun x => c * hankelXi c x) x :=
    ((hasDerivAt_hankelXi hc hxa).const_mul c).continuousAt
  have hrho : ContinuousAt (hankelRho0 c) (c * hankelXi c x) := by
    unfold hankelRho0
    exact continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl hxi.ne'))
  have hfc : ContinuousAt f (c * hankelXi c x) := hf.cont.continuousAt (Ici_mem_nhds hxi)
  have hD : ContinuousWithinAt (hankelXiD c) (Icc (-(langerRadius c)) (langerRadius c)) x :=
    continuousOn_hankelXiD hc x hx
  refine ContinuousWithinAt.mul ?_ (hD.const_smul c |>.congr (fun y _ => by simp) (by simp))
  exact (((ContinuousAt.comp (g := hankelRho0 c) (f := fun x => c * hankelXi c x) hrho hXi)).mul
    (ContinuousAt.comp (g := f) (f := fun x => c * hankelXi c x) hfc hXi)).continuousWithinAt

/-- **Integrated transport `(c)`**: `∫_a^b Re Ψ̃ = ∫_{cξ(b)}^{cξ(a)} ρ₀ f + O((b-a) r_∞)`. -/
theorem hankel_transport_integral {c ε : ℝ} (hc : 5000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {a b : ℝ} (ha : |a| ≤ langerRadius c)
    (hb : |b| ≤ langerRadius c) (hab : a ≤ b) :
    |(∫ x in a..b, hankelPsiR c f x) -
        ∫ u in (c * hankelXi c b)..(c * hankelXi c a), hankelRho0 c u * f u| ≤ (b - a) * hankelRinf c := by
  have hc0 : 0 < c := by linarith
  have hmem : ∀ x ∈ Icc a b, |x| ≤ langerRadius c := fun x hx =>
    abs_le.2 ⟨by linarith [abs_le.1 ha |>.1, hx.1], by linarith [abs_le.1 hb |>.2, hx.2]⟩
  have hsub : Icc a b ⊆ Icc (-(langerRadius c)) (langerRadius c) := fun x hx => abs_le.1 (hmem x hx)
  have hψc : IntervalIntegrable (hankelPsiR c f) volume a b :=
    ((continuousOn_hankelPsiR hc0 hf).mono hsub |>.intervalIntegrable_of_Icc hab)
  have htc : IntervalIntegrable
      (fun x => hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x) * (c * hankelXiD c x)) volume a b :=
    ((continuousOn_hankel_term hc0 hf).mono hsub |>.intervalIntegrable_of_Icc hab)
  have hE : ‖∫ x in a..b, (hankelPsiR c f x +
      hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x) * (c * hankelXiD c x))‖ ≤ hankelRinf c * |b - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
    rw [uIoc_of_le hab] at hx
    have := hankel_transport_pointwise hc hf hε hM (hmem x ⟨hx.1.le, hx.2⟩)
    rw [Real.norm_eq_abs]
    unfold hankelPsiR hankelRinf
    refine le_trans (le_of_eq ?_) this
    congr 1; ring
  rw [intervalIntegral.integral_add hψc htc] at hE
  have hs := hankel_subst hc0 ha hb hab (fun u => hankelRho0 c u * f u)
  beta_reduce at hs
  rw [hs, intervalIntegral.integral_symm (c * hankelXi c b) (c * hankelXi c a)] at hE
  rw [abs_of_nonneg (by linarith : 0 ≤ b - a)] at hE
  rw [Real.norm_eq_abs] at hE
  rw [sub_eq_add_neg]
  linarith [hE]

/-- info: 'FormalResearch.SignUncertainty.hankel_transport_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_transport_integral

end FormalResearch.SignUncertainty
