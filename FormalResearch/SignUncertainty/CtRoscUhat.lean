module

public import Mathlib
public import FormalResearch.SignUncertainty.CtRoscBudget

/-!
# `ct:dyadic` (4), `(ct:rosc)`: the substitution `u = û(x)` on `x ∈ (-R', 0)` (pieces `T4`, `T6` of `CtRoscBook`)

`constant_terms_lower.tex`, `ct:dyadic` (4): "substituting `v = -û(-v')` ... `f_c(-v) dv = Ψ̃(x) dx`".  For `x ∈ (-R', 0)` (`R' = -φ_c(-R)`) the real chart `û` maps
`(-R', 0)` onto `S ⊂ (-R, 0)`, and `(-R, 0) \ S ⊂ [-λM, 0)` is the *edge strip* `ũ ∈ (0, ũ₀)` of width `λ M = O(c^{-1/3})` (`ψ_ε(0⁻) < 0`).  On `S`,
`f_c(û(x)) û'(x) = Re Ψ̃(x)` (since `φ_c(û(x)) = x`, `ctPhiR_ctUhat`), so `∫_S g = ∫_{-R'}^0 û'(x) g(û(x)) dx` (`ctUhat_subst`).

* `ctUhat_neg_Rprime`: `û(-R') = -R`;  `ctUhat_image_cover`: every `u ∈ (-R, -λM)` is `û(x)` with `x ∈ (-R', 0)`;
* `ctUhat_subst`: the change of variables;  `ctFr_ctUhat`: `ctFr (û x) · û'(x) = Re Ψ̃(x)`.

All proved.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `û'(x) = 1 + c⁻¹ ψ_ε'(μx)`. -/
noncomputable def ctUhatD (ε c x : ℝ) : ℝ := 1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * x)

section Uhat

variable {ε c C ρ M R : ℝ}

/-- `û(-R') = -R`: `-R' = ctPhi(-R)` is the preimage of `-R`. -/
lemma ctUhat_neg_Rprime (H : CtRealChartHyp ε c C) (W : CtWinHyp ε c ρ M) (hR1 : 1 < R)
    (hRm : R ≤ ctRmax ctChartC1 c) : ctUhat ε c (-ctRprime ε c R) = -R := by
  have haw : -ρ < ctMu c * (-R) := W.mu_mul_lt H.c_pos (by linarith)
  obtain ⟨u, hu, huv, huφ⟩ := ctPhi_pre W.win H.c_pos W.cM W.lam (a := -R) (by linarith) haw
  unfold ctRprime
  rw [huφ, neg_neg, huv]

lemma ctRprime_bounds (H : CtRealChartHyp ε c C) (W : CtWinHyp ε c ρ M) (hR1 : 1 < R)
    (hRm : R ≤ ctRmax ctChartC1 c) :
    1 / 2 ≤ ctRprime ε c R ∧ ctRprime ε c R ≤ R ∧ R - 1 / 2 ≤ ctRprime ε c R := by
  have haw : -ρ < ctMu c * (-R) := W.mu_mul_lt H.c_pos (by linarith)
  obtain ⟨u, hu, huv, huφ⟩ := ctPhi_pre W.win H.c_pos W.cM W.lam (a := -R) (by linarith) haw
  have hu0 : u < 0 := by linarith [hu.2]
  have huw : -ρ < ctMu c * u := by
    have := mul_le_mul_of_nonneg_left hu.1 (ctMu_pos H.c_pos).le
    linarith
  have h2 := abs_ctUhat_sub_le W.win H.c_pos hu0 huw
  rw [huv] at h2
  have h3 := (abs_le.1 h2).1
  unfold ctRprime
  rw [huφ]
  refine ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2], ?_⟩
  linarith [W.lam]

lemma ctUhat_strictMonoOn (H : CtRealChartHyp ε c C) (W : CtWinHyp ε c ρ M) (hR1 : 1 < R)
    (hRm : R ≤ ctRmax ctChartC1 c) :
    StrictMonoOn (ctUhat ε c) (Icc (-ctRprime ε c R) 0) := by
  intro x hx y hy hxy
  exact ctUhat_lt_of_window W.win H.c_pos W.cM hxy hy.2
    (W.mu_mul_lt H.c_pos (by linarith [hx.1, (ctRprime_bounds H W hR1 hRm).2.1]))

/-- `û` maps `(-R', 0)` into `(-R, 0)`. -/
lemma ctUhat_mem (H : CtRealChartHyp ε c C) (W : CtWinHyp ε c ρ M) (hR1 : 1 < R)
    (hRm : R ≤ ctRmax ctChartC1 c) {x : ℝ} (hx : x ∈ Ioo (-ctRprime ε c R) 0) :
    ctUhat ε c x ∈ Ioo (-R) 0 := by
  have hmono := ctUhat_strictMonoOn H W hR1 hRm
  have hRp := ctRprime_bounds H W hR1 hRm
  have hlow : ctUhat ε c (-ctRprime ε c R) < ctUhat ε c x :=
    hmono ⟨le_rfl, by linarith [hRp.1]⟩ ⟨hx.1.le, hx.2.le⟩ hx.1
  rw [ctUhat_neg_Rprime H W hR1 hRm] at hlow
  have h2 := ctUhat_lt W.win H.c_pos hx.2 (W.mu_mul_lt H.c_pos (by linarith [hx.1, hRp.2.1]))
  exact ⟨hlow, by linarith [hx.2]⟩

/-- **The edge strip**: every `u ∈ (-R, -λM)` is `û(x)` for some `x ∈ (-R', 0)`. -/
lemma ctUhat_image_cover (H : CtRealChartHyp ε c C) (W : CtWinHyp ε c ρ M) (hR1 : 1 < R)
    (hRm : R ≤ ctRmax ctChartC1 c) {u : ℝ} (huR : -R < u) (hu : u < -(ctLam c * M)) :
    ∃ x ∈ Ioo (-ctRprime ε c R) 0, ctUhat ε c x = u := by
  have hRp := ctRprime_bounds H W hR1 hRm
  have hlam0 : 0 ≤ ctLam c * M := by
    have := W.lam
    by_contra h
    push Not at h
    have hM : M < 0 := by
      by_contra hM; push Not at hM; exact absurd (mul_nonneg (ctLam_pos H.c_pos).le hM) (not_le.2 h)
    have := W.win.2.1
    linarith
  set δ := ctLam c * M with hδ
  set x₂ : ℝ := (u + δ) / 2 with hx₂
  have hx₂0 : x₂ < 0 := by rw [hx₂]; linarith
  have hx₂gt : u + δ < x₂ := by rw [hx₂]; linarith
  have hx₂R : -ctRprime ε c R ≤ x₂ := by
    have : -R / 2 ≤ x₂ := by rw [hx₂]; linarith
    linarith [hRp.2.2]
  have hcont : ContinuousOn (ctUhat ε c) (Icc (-ctRprime ε c R) x₂) :=
    continuousOn_ctUhat W.win H.c_pos hx₂0 (W.mu_mul_lt H.c_pos (by linarith [hRp.2.1]))
  have h2 := abs_ctUhat_sub_le W.win H.c_pos hx₂0
    (W.mu_mul_lt H.c_pos (by linarith [hRp.2.1, hx₂R]))
  have hup : u < ctUhat ε c x₂ := by
    have := (abs_le.1 h2).1
    linarith
  have hlow : ctUhat ε c (-ctRprime ε c R) < u := by rw [ctUhat_neg_Rprime H W hR1 hRm]; exact huR
  obtain ⟨x, hx, hxv⟩ := intermediate_value_Icc hx₂R hcont ⟨hlow.le, hup.le⟩
  have hx1 : -ctRprime ε c R < x := by
    rcases hx.1.eq_or_lt with h | h
    · rw [← h] at hxv; linarith
    · exact h
  exact ⟨x, ⟨hx1, lt_of_le_of_lt hx.2 hx₂0⟩, hxv⟩

/-- `φ'(û(x)) û'(x) = 1` and `ctFr (û x) · û'(x) = Re Ψ̃(x)` for `x ∈ (-R', 0)`. -/
lemma ctFr_ctUhat (H : CtRealChartHyp ε c C) (W : CtWinHyp ε c ρ M) (f : ℝ → ℝ) (hR1 : 1 < R)
    (hRm : R ≤ ctRmax ctChartC1 c) {x : ℝ} (hx : x ∈ Ioo (-ctRprime ε c R) 0) :
    ctFr ε c f (ctUhat ε c x) * ctUhatD ε c x = hankelPsiR c f x := by
  have hRp := ctRprime_bounds H W hR1 hRm
  have hxw : -ρ < ctMu c * x := W.mu_mul_lt H.c_pos (by linarith [hx.1, hRp.2.1])
  have hu := ctUhat_mem H W hR1 hRm hx
  have habs : |ctUhat ε c x| < ctRmax ctChartC1 c := abs_lt.2 ⟨by linarith [hu.1], by linarith [hu.2, H.Rm_pos]⟩
  have hD1 := ctUhat_hasDerivAt W.win H.c_pos hx.2 hxw
  have hD2 := H.ctPhiR_hasDerivAt habs
  have hcomp := hD2.comp x hD1
  have hid : (ctPhiR ε c ∘ ctUhat ε c) =ᶠ[𝓝 x] id := by
    have hopen : IsOpen (Ioo (-ctRmax ctChartC1 c) (0 : ℝ)) := isOpen_Ioo
    have hmem : x ∈ Ioo (-ctRmax ctChartC1 c) (0 : ℝ) := ⟨by linarith [hx.1, hRp.2.1], hx.2⟩
    filter_upwards [hopen.mem_nhds hmem] with y hy
    exact H.ctPhiR_ctUhat hy.2 hy.1.le
  have hone : HasDerivAt (ctPhiR ε c ∘ ctUhat ε c) 1 x := (hasDerivAt_id x).congr_of_eventuallyEq hid
  have hprod : ctPhiRD ε c (ctUhat ε c x) * ctUhatD ε c x = 1 := hcomp.unique hone
  unfold ctFr
  rw [H.ctPhiR_ctUhat hx.2 (by linarith [hx.1, hRp.2.1])]
  calc hankelPsiR c f x * ctPhiRD ε c (ctUhat ε c x) * ctUhatD ε c x
      = hankelPsiR c f x * (ctPhiRD ε c (ctUhat ε c x) * ctUhatD ε c x) := by ring
    _ = _ := by rw [hprod, mul_one]

/-- **Change of variables `u = û(x)`** on `x ∈ (-R', 0)`: `∫_{û((-R',0))} g = ∫_{-R'}^0 û'(x) g(û x) dx`. -/
lemma ctUhat_subst (H : CtRealChartHyp ε c C) (W : CtWinHyp ε c ρ M) (hR1 : 1 < R)
    (hRm : R ≤ ctRmax ctChartC1 c) (g : ℝ → ℝ) :
    ∫ u in ctUhat ε c '' Ioo (-ctRprime ε c R) 0, g u =
      ∫ x in Ioo (-ctRprime ε c R) 0, ctUhatD ε c x * g (ctUhat ε c x) := by
  have hRp := ctRprime_bounds H W hR1 hRm
  have hd : ∀ x ∈ Ioo (-ctRprime ε c R) 0, HasDerivWithinAt (ctUhat ε c) (ctUhatD ε c x) (Ioo (-ctRprime ε c R) 0) x :=
    fun x hx => (ctUhat_hasDerivAt W.win H.c_pos hx.2
      (W.mu_mul_lt H.c_pos (by linarith [hx.1, hRp.2.1]))).hasDerivWithinAt
  have hinj : InjOn (ctUhat ε c) (Ioo (-ctRprime ε c R) 0) :=
    (ctUhat_strictMonoOn H W hR1 hRm).injOn.mono (fun x (hx : x ∈ Ioo (-ctRprime ε c R) 0) => (⟨hx.1.le, hx.2.le⟩ : x ∈ Icc (-ctRprime ε c R) 0))
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj g
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have hxw : -ρ < ctMu c * x := W.mu_mul_lt H.c_pos (by linarith [hx.1, hRp.2.1])
  have hb := (ctUhat_deriv_bounds W.win H.c_pos W.cM hx.2 hxw).1
  simp only [smul_eq_mul, ctUhatD]
  rw [abs_of_pos (by linarith)]

end Uhat

end FormalResearch.SignUncertainty
