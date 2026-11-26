module

public import Mathlib
public import FormalResearch.SignUncertainty.CtRoscUhat
public import FormalResearch.SignUncertainty.CtRoscLobe

/-!
# `ct:dyadic` (4), `(ct:rosc)`: the `u`-integrals of `f_c` against the Langer density (pieces `T2`, `T6` of `CtRoscBook`)

Context `CtRoscCtx` (chart, window, Hankel eigenfunction of mass one, continuity of `f_c` on `[-R_max, R_max]`) and the three substitutions:

* `ctFr_abs_subst`: `∫_{(a,b)} |f_c| du = ∫_{(φ(a), φ(b))} |Re Ψ̃| dx` (`x = φ_c(u)`) and `psi_abs_Ioo_le`: `∫_{(x₁, x₂)} |Re Ψ̃| ≤ 1 + 2 A r_∞`;
* `neg_decomp`: for the negative half-line, `∫_{(-R, 0)} g = ∫_{-R'}^0 û'(x) g(û x) dx + (edge strip)`, the strip being `∫_{(-λM, 0)} |g|`:
  the substitution `v = -û(x)` of `ct:dyadic` (4) and the edge strip `0 < v < -û(0⁻) ≤ λ M = O(c^{-1/3})`;
* the Landau constants of the strip (`edge_strip_le`): `|g| ≤ 2 (λM/R)^{12} |f_c|`.

All proved.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

/-- **Context of the bookkeeping `CtRoscBook`**: the real chart, the `ψ_ε`-window, a Hankel eigenfunction of mass one, and continuity of the complex
`f_c` on `[-R_max, R_max]`. -/
structure CtRoscCtx (ε c C ρ M : ℝ) (f : ℝ → ℝ) : Prop where
  H : CtRealChartHyp ε c C
  W : CtWinHyp ε c ρ M
  hf : IsHankelEigenfn c ε f
  hε : ε = 1 ∨ ε = -1
  hM : hankelMass c f = 1
  cont : ContinuousOn (fun u : ℝ => ctFcC ctChartC1 ε c f (u : ℂ)) (Icc (-ctRmax ctChartC1 c) (ctRmax ctChartC1 c))

namespace CtRoscCtx

variable {ε c C ρ M R : ℝ} {f : ℝ → ℝ}

lemma c_pos (X : CtRoscCtx ε c C ρ M f) : 0 < c := X.H.c_pos

lemma integrableOn_ctFr (X : CtRoscCtx ε c C ρ M f) {a b : ℝ} (ha : -ctRmax ctChartC1 c ≤ a)
    (hb : b ≤ ctRmax ctChartC1 c) : IntegrableOn (ctFr ε c f) (Ioo a b) := by
  have hc : ContinuousOn (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re) (Icc a b) :=
    Complex.continuous_re.comp_continuousOn (X.cont.mono (Icc_subset_Icc ha hb))
  have hi := (hc.integrableOn_Icc (μ := volume)).mono_set (Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b)
  refine hi.congr_fun (fun u hu => ?_) measurableSet_Ioo
  exact X.H.ctFcC_re (abs_lt.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩ |>.trans_le le_rfl)

/-- `∫_{(a,b)} |f_c(u)| du = ∫_{(φ(a), φ(b))} |Re Ψ̃(x)| dx`. -/
lemma ctFr_abs_subst (X : CtRoscCtx ε c C ρ M f) {a b : ℝ} (ha : -ctRmax ctChartC1 c ≤ a)
    (hb : b ≤ ctRmax ctChartC1 c) (hab : a ≤ b) :
    ∫ u in Ioo a b, |ctFr ε c f u| = ∫ x in Ioo (ctPhiR ε c a) (ctPhiR ε c b), |hankelPsiR c f x| := by
  rw [X.H.ctPhiR_subst ha hb hab (fun x => |hankelPsiR c f x|)]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have hlt : |u| < ctRmax ctChartC1 c := abs_lt.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hpos := (X.H.ctPhiRD_bounds hlt.le).1
  unfold ctFr
  rw [abs_mul, abs_of_pos (by linarith : 0 < ctPhiRD ε c u), mul_comm]

/-- **Total mass of `|Re Ψ̃|` on a sub-interval of the Langer disc**: `≤ 1 + 2 A r_∞`. -/
lemma psi_abs_Ioo_le (X : CtRoscCtx ε c C ρ M f) {x₁ x₂ : ℝ} (h1 : |x₁| ≤ langerRadius c) (h2 : |x₂| ≤ langerRadius c) :
    ∫ x in Ioo x₁ x₂, |hankelPsiR c f x| ≤ 1 + 2 * langerRadius c * hankelRinf c := by
  have hc0 := X.c_pos
  have hA := langerRadius_pos hc0
  have hmass := hankel_psi_abs_mass (by linarith [X.H.hc]) X.hf X.hε X.hM
  rw [intervalIntegral.integral_of_le (by linarith)] at hmass
  have hcont : ContinuousOn (fun x => |hankelPsiR c f x|) (Icc (-(langerRadius c)) (langerRadius c)) :=
    continuous_abs.comp_continuousOn (continuousOn_hankelPsiR hc0 X.hf)
  refine le_trans ?_ hmass
  rw [← integral_Ioc_eq_integral_Ioo]
  refine setIntegral_mono_set (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self) ?_ ?_
  · exact Eventually.of_forall fun x => abs_nonneg _
  · exact Eventually.of_forall fun x hx =>
      ⟨by linarith [(abs_le.1 h1).1, hx.1], by linarith [(abs_le.1 h2).2, hx.2]⟩

/-- **Mass of `|f_c|` on a sub-interval of the real window**: `∫_{(a,b)} |f_c| ≤ 1 + 2 A r_∞`. -/
lemma ctFr_abs_le (X : CtRoscCtx ε c C ρ M f) {a b : ℝ} (ha : -ctRmax ctChartC1 c ≤ a)
    (hb : b ≤ ctRmax ctChartC1 c) (hab : a ≤ b) :
    ∫ u in Ioo a b, |ctFr ε c f u| ≤ 1 + 2 * langerRadius c * hankelRinf c := by
  rw [X.ctFr_abs_subst ha hb hab]
  exact X.psi_abs_Ioo_le (X.H.abs_ctPhiR_lt (by rw [abs_le]; constructor <;> linarith [X.H.Rm_pos])).le
    (X.H.abs_ctPhiR_lt (by rw [abs_le]; constructor <;> linarith [X.H.Rm_pos])).le


/-- **Decomposition of the negative half-window** (`v = -û(x)`, edge strip): for `g` integrable on `(-R, 0)`,
`|∫_{(-R,0)} g - ∫_{(-R',0)} û'(x) g(û x) dx| ≤ ∫_{(-λM, 0)} |g|`. -/
lemma neg_decomp (X : CtRoscCtx ε c C ρ M f) (hR1 : 1 < R) (hRm : R ≤ ctRmax ctChartC1 c) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioo (-R) 0)) :
    |(∫ u in Ioo (-R) 0, g u) - ∫ x in Ioo (-ctRprime ε c R) 0, ctUhatD ε c x * g (ctUhat ε c x)| ≤
      ∫ u in Ioo (-(ctLam c * M)) 0, |g u| := by
  have hc0 := X.c_pos
  set δ := ctLam c * M with hδ
  have hδ1 : δ ≤ 1 / 2 := X.W.lam
  have hRp := ctRprime_bounds X.H X.W hR1 hRm
  set S := ctUhat ε c '' Ioo (-ctRprime ε c R) 0 with hS
  have hSsub : S ⊆ Ioo (-R) 0 := by
    rintro _ ⟨x, hx, rfl⟩
    exact ctUhat_mem X.H X.W hR1 hRm hx
  have hcontS : ContinuousOn (ctUhat ε c) (Ioo (-ctRprime ε c R) 0) := fun x hx =>
    (ctUhat_hasDerivAt X.W.win hc0 hx.2 (X.W.mu_mul_lt hc0 (by linarith [hx.1, hRp.2.1]))).continuousAt.continuousWithinAt
  have hSmeas : MeasurableSet S :=
    (isPreconnected_Ioo.image _ hcontS).ordConnected.measurableSet
  have hsplit := integral_inter_add_sdiff (μ := volume) (f := g) hSmeas hg (s := Ioo (-R) 0)
  rw [inter_eq_right.2 hSsub] at hsplit
  have hE : (∫ u in Ioo (-R) 0 \ S, g u) = (∫ u in Ioo (-R) 0, g u) - ∫ u in S, g u := by linarith
  have hSint : (∫ u in S, g u) = ∫ x in Ioo (-ctRprime ε c R) 0, ctUhatD ε c x * g (ctUhat ε c x) :=
    ctUhat_subst X.H X.W hR1 hRm g
  rw [← hSint, ← hE]
  have hEsub : Ioo (-R) 0 \ S ⊆ Ico (-δ) 0 := by
    intro u hu
    refine ⟨?_, hu.1.2⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨x, hx, hxv⟩ := ctUhat_image_cover X.H X.W hR1 hRm hu.1.1 hlt
    exact hu.2 ⟨x, hx, hxv⟩
  have hIco : Ico (-δ) 0 ⊆ Ioo (-R) 0 := fun u hu => ⟨by linarith [hu.1], hu.2⟩
  have hgabs : IntegrableOn (fun u => |g u|) (Ico (-δ) 0) := (hg.mono_set hIco).abs
  refine (abs_integral_le_integral_abs).trans ?_
  refine (setIntegral_mono_set hgabs (Eventually.of_forall fun u => abs_nonneg _)
    (Eventually.of_forall hEsub)).trans (le_of_eq ?_)
  exact integral_Ico_eq_integral_Ioo

/-- **Size of the edge strip**: if `|g| ≤ K |f_c|` on `(-λM, 0)`, `K ≥ 0`, then `∫_{(-λM, 0)} |g| ≤ K (1 + 2 A r_∞)`. -/
lemma strip_le (X : CtRoscCtx ε c C ρ M f) (hR1 : 1 < R) (hRm : R ≤ ctRmax ctChartC1 c) {g : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hgb : ∀ u ∈ Ioo (-(ctLam c * M)) 0, |g u| ≤ K * |ctFr ε c f u|) :
    ∫ u in Ioo (-(ctLam c * M)) 0, |g u| ≤ K * (1 + 2 * langerRadius c * hankelRinf c) := by
  have hδ1 : ctLam c * M ≤ 1 / 2 := X.W.lam
  have hRmR : -ctRmax ctChartC1 c ≤ -(ctLam c * M) := by linarith
  have hint := X.integrableOn_ctFr hRmR (by linarith [X.H.Rm_pos] : (0 : ℝ) ≤ ctRmax ctChartC1 c)
  have hmass := X.ctFr_abs_le hRmR (by linarith [X.H.Rm_pos] : (0 : ℝ) ≤ ctRmax ctChartC1 c)
    (by
      have : 0 ≤ ctLam c * M := by
        have h0 := X.W.win.2.1
        exact mul_nonneg (ctLam_pos X.c_pos).le h0
      linarith)
  calc ∫ u in Ioo (-(ctLam c * M)) 0, |g u| ≤ ∫ u in Ioo (-(ctLam c * M)) 0, K * |ctFr ε c f u| :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => abs_nonneg _)
          (hint.abs.const_mul K)
          (ae_restrict_of_forall_mem measurableSet_Ioo hgb)
    _ = K * ∫ u in Ioo (-(ctLam c * M)) 0, |ctFr ε c f u| := integral_const_mul _ _
    _ ≤ K * (1 + 2 * langerRadius c * hankelRinf c) := mul_le_mul_of_nonneg_left hmass hK

end CtRoscCtx

/-- info: 'FormalResearch.SignUncertainty.CtRoscCtx.neg_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CtRoscCtx.neg_decomp

end FormalResearch.SignUncertainty
