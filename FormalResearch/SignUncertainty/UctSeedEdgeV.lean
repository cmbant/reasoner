module

public import FormalResearch.SignUncertainty.UctSeedWHolder

/-!
# `W^seed` edge trace, the Airy factor: `v(q) = F̃_{*,δ}(i·(iq))` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, `(uct:Wseed-def)` ("Combining with `uct:airy-trans` (2)-(3) verifies
(M1)-(M3)").  The edge trace of `W^seed` at `ζ = iτ` is `Y(τ) v(aτ)` with `v(q) = T(iq)`, `T(w) = F̃_{*,δ}(iw)`.  **Proved.**

* `seedV_contDiffOn`: `v` is `C^n` on `q ≠ 0` (it is `-F₁ - δ G₁` of the closed-form extensions, holomorphic on the slit plane);
* `seedV_near`: `|v(q) - v(0)| ≤ C|q|^{1/2}`, `|v'(q)| ≤ C|q|^{-1/2}`, `|v''(q)| ≤ C|q|^{-3/2}` for `0 < |q| ≤ 2` (`uct_airy_trans_small`,
  `uct_airy_trans_small_deriv_F`);
* `seedV_far`: `v, v', v''` are bounded on `|q| ≥ q₀` (any `q₀ > 0`): `ImagAxisBounds` for `|q| > 1`, compactness for `q₀ ≤ |q| ≤ 1`.
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

/-- `T(i q)` for real `q`: `F̃_{*,δ}(i·(iq))`. -/
noncomputable def seedV (δ : ℝ) (q : ℝ) : ℂ := seedT δ ((q : ℂ) * Complex.I)

/-- The closed-form extension `-F₁ - δ G₁` of `T`. -/
noncomputable def seedText (δ : ℝ) (w : ℂ) : ℂ := -uctF1Ext w - (δ : ℂ) * uctG1Ext w

lemma seedT_eq_text (δ : ℝ) {w : ℂ} (hw : 0 ≤ w.re) : seedT δ w = seedText δ w :=
  airyTwistedLaplaceC_uctFstarDelta δ hw

lemma differentiableOn_uctF1Ext : DifferentiableOn ℂ uctF1Ext Complex.slitPlane := by
  intro w hw
  have h1 : DifferentiableAt ℂ (fun z : ℂ => z ^ (1 / 2 : ℂ)) w := differentiableAt_id.cpow_const hw
  have h2 : DifferentiableAt ℂ uctE w := (uctE_differentiable w)
  exact ((h1.const_mul uctC).mul h2).differentiableWithinAt

lemma differentiableOn_seedText (δ : ℝ) : DifferentiableOn ℂ (seedText δ) Complex.slitPlane := by
  unfold seedText
  exact (differentiableOn_uctF1Ext.neg).sub (differentiableOn_uctG1Ext.const_mul _)

lemma seedV_eq_text (δ : ℝ) : seedV δ = fun q : ℝ => seedText δ ((q : ℂ) * Complex.I) := by
  funext q
  unfold seedV
  exact seedT_eq_text δ (by simp)

lemma mul_I_mem_slit {q : ℝ} (hq : q ≠ 0) : ((q : ℂ) * Complex.I) ∈ Complex.slitPlane := by
  right
  simpa using hq

theorem seedV_contDiffOn (δ : ℝ) (n : ℕ) : ContDiffOn ℝ n (seedV δ) {q : ℝ | q ≠ 0} := by
  intro q hq
  have hq' : q ≠ 0 := hq
  have h1 : ContDiffAt ℂ n (seedText δ) ((q : ℂ) * Complex.I) :=
    contDiffAt_of_slit (differentiableOn_seedText δ) (mul_I_mem_slit hq') n
  have h2 : ContDiffAt ℝ n (fun q : ℝ => (q : ℂ) * Complex.I) q := by
    exact (Complex.ofRealCLM.contDiff.mul contDiff_const).contDiffAt
  rw [seedV_eq_text]
  exact ((h1.restrict_scalars ℝ).comp q h2).contDiffWithinAt


lemma seedV_eq_swap (δ : ℝ) : (fun t : ℝ => airyTwistedLaplaceC (uctFstarDelta δ) (Complex.I * (t : ℂ))) = seedV δ := by
  funext t; simp [seedV, seedT, mul_comm]

theorem seedV_near {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, q ≠ 0 → |q| ≤ 2 →
      ‖seedV δ q - seedV δ 0‖ ≤ C * |q| ^ (1 / 2 : ℝ) ∧ ‖deriv (seedV δ) q‖ ≤ C * |q| ^ ((1 / 2 : ℝ) - 1) ∧
        ‖deriv (deriv (seedV δ)) q‖ ≤ C * |q| ^ ((1 / 2 : ℝ) - 2) := by
  obtain ⟨C0, hC00, hC0⟩ := seedT_holder hδ0 hδ1
  obtain ⟨C1, hC10, hC1⟩ := uct_airy_trans_small_deriv_F 1 le_rfl
  obtain ⟨C2, hC20, hC2⟩ := uct_airy_trans_small_deriv_F 2 (by norm_num)
  refine ⟨max C0 (max C1 C2), by positivity, fun q hq hq2 => ⟨?_, ?_, ?_⟩⟩
  · have h := hC0 ((q : ℂ) * Complex.I) (by simp)
    have hn : ‖(q : ℂ) * Complex.I‖ = |q| := by simp
    rw [hn] at h
    have : seedV δ 0 = seedT δ 0 := by simp [seedV]
    rw [this]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have h := hC1 δ hδ0 hδ1 q hq hq2
    rw [seedV_eq_swap, iteratedDeriv_one] at h
    simpa using h.trans (mul_le_mul_of_nonneg_right ((le_max_left C1 C2).trans (le_max_right C0 (max C1 C2))) (by positivity))
  · have h := hC2 δ hδ0 hδ1 q hq hq2
    rw [seedV_eq_swap, iteratedDeriv_succ, iteratedDeriv_one] at h
    have := h.trans (mul_le_mul_of_nonneg_right ((le_max_right C1 C2).trans (le_max_right C0 (max C1 C2))) (by positivity))
    norm_num at this ⊢
    exact this

lemma imagAxisBounds_seedT (δ : ℝ) : ImagAxisBounds (seedT δ) := by
  obtain ⟨gF1, gF2, hF1, hF2, CF, hCF, hF⟩ := ceF1_imagAxisBounds
  obtain ⟨gG1, gG2, hG1, hG2, CG, hCG, hG⟩ := ceG1_imagAxisBounds
  have hfun : (fun ω : ℝ => seedT δ ((ω : ℂ) * Complex.I)) = fun ω : ℝ =>
      -airyTwistedLaplaceC ceF1 ((ω : ℂ) * Complex.I) - (δ : ℂ) * airyTwistedLaplaceC (ceG1 (Special.airyZero 1)) ((ω : ℂ) * Complex.I) := by
    funext ω
    have h0 : 0 ≤ ((ω : ℂ) * Complex.I).re := by simp
    rw [seedT_eq_text δ h0, uctF1Ext_eq h0, uctG1Ext_eq h0]
    unfold seedText
    ring
  have hCF' : 0 ≤ CF := hCF.le
  refine ⟨fun ω => -gF1 ω - (δ : ℂ) * gG1 ω, fun ω => -gF2 ω - (δ : ℂ) * gG2 ω, fun ω hω => ?_, fun ω hω => ?_,
    CF + |δ| * CG, by positivity, fun ω hω => ?_⟩
  · rw [hfun]; exact (hF1 ω hω).neg.sub ((hG1 ω hω).const_mul (δ : ℂ))
  · exact (hF2 ω hω).neg.sub ((hG2 ω hω).const_mul (δ : ℂ))
  · have a1 := hF ω hω
    have a2 := hG ω hω
    have key : ∀ (a b : ℂ) (p : ℝ), 0 ≤ p → ‖a‖ ≤ CF * p → ‖b‖ ≤ CG * p →
        ‖-a - (δ : ℂ) * b‖ ≤ (CF + |δ| * CG) * p := by
      intro a b p hp ha hb
      have hδn : ‖(δ : ℂ)‖ = |δ| := by simp
      calc ‖-a - (δ : ℂ) * b‖ ≤ ‖a‖ + |δ| * ‖b‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_neg, norm_mul, hδn]
        _ ≤ CF * p + |δ| * (CG * p) := by gcongr
        _ = _ := by ring
    have e : seedT δ ((ω : ℂ) * Complex.I) = -airyTwistedLaplaceC ceF1 ((ω : ℂ) * Complex.I) -
        (δ : ℂ) * airyTwistedLaplaceC (ceG1 (Special.airyZero 1)) ((ω : ℂ) * Complex.I) := congrFun hfun ω
    refine ⟨?_, key _ _ _ (by positivity) a1.2.1 a2.2.1, key _ _ _ (by positivity) a1.2.2 a2.2.2⟩
    rw [e]
    exact key _ _ _ (by positivity) a1.1 a2.1


lemma rpow_neg_le_one {x p : ℝ} (hx : 1 ≤ x) (hp : 0 ≤ p) : x ^ (-p) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)

theorem seedV_far (δ : ℝ) {q₀ : ℝ} (hq₀ : 0 < q₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, q₀ ≤ |q| →
      ‖seedV δ q‖ ≤ C ∧ ‖deriv (seedV δ) q‖ ≤ C ∧ ‖deriv (deriv (seedV δ)) q‖ ≤ C := by
  obtain ⟨g1, g2, h1, h2, C, hC, hb⟩ := imagAxisBounds_seedT δ
  have hopen : IsOpen {q : ℝ | q ≠ 0} := isOpen_ne
  have hcd : ContDiffOn ℝ 3 (seedV δ) {q : ℝ | q ≠ 0} := seedV_contDiffOn δ 3
  have hc0 : ContinuousOn (seedV δ) {q : ℝ | q ≠ 0} := hcd.continuousOn
  have hc1 : ContinuousOn (deriv (seedV δ)) {q : ℝ | q ≠ 0} :=
    hcd.continuousOn_deriv_of_isOpen hopen (by norm_num)
  have hcd1 : ContDiffOn ℝ 2 (deriv (seedV δ)) {q : ℝ | q ≠ 0} := hcd.deriv_of_isOpen hopen (by norm_num)
  have hc2 : ContinuousOn (deriv (deriv (seedV δ))) {q : ℝ | q ≠ 0} :=
    hcd1.continuousOn_deriv_of_isOpen hopen (by norm_num)
  set K : Set ℝ := Icc q₀ 1 ∪ Icc (-1) (-q₀) with hK
  have hKc : IsCompact K := isCompact_Icc.union isCompact_Icc
  have hKsub : K ⊆ {q : ℝ | q ≠ 0} := by
    intro q hq
    rcases hq with hq | hq
    · exact ne_of_gt (lt_of_lt_of_le hq₀ hq.1)
    · exact ne_of_lt (lt_of_le_of_lt hq.2 (by linarith))
  obtain ⟨B0, hB0⟩ := hKc.exists_bound_of_continuousOn (hc0.mono hKsub)
  obtain ⟨B1, hB1⟩ := hKc.exists_bound_of_continuousOn (hc1.mono hKsub)
  obtain ⟨B2, hB2⟩ := hKc.exists_bound_of_continuousOn (hc2.mono hKsub)
  refine ⟨max C (max B0 (max B1 B2)), by positivity, fun q hq => ?_⟩
  by_cases hq1 : 1 < |q|
  · have hb' := hb q hq1
    have hd1 : deriv (seedV δ) q = g1 q := (h1 q hq1 : HasDerivAt (seedV δ) (g1 q) q).deriv
    have hev : deriv (seedV δ) =ᶠ[𝓝 q] g1 := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hq1] with y hy
      exact (h1 y hy : HasDerivAt (seedV δ) (g1 y) y).deriv
    have hd2 : deriv (deriv (seedV δ)) q = g2 q := by
      rw [hev.deriv_eq]; exact (h2 q hq1).deriv
    have p1 : |q| ^ (-(5 / 2 : ℝ)) ≤ 1 := rpow_neg_le_one hq1.le (by norm_num)
    have p2 : |q| ^ (-(7 / 2 : ℝ)) ≤ 1 := rpow_neg_le_one hq1.le (by norm_num)
    have p3 : |q| ^ (-(9 / 2 : ℝ)) ≤ 1 := rpow_neg_le_one hq1.le (by norm_num)
    have hmax : C ≤ max C (max B0 (max B1 B2)) := le_max_left _ _
    refine ⟨?_, ?_, ?_⟩
    · have : ‖seedV δ q‖ ≤ C * |q| ^ (-(5 / 2 : ℝ)) := hb'.1
      nlinarith
    · rw [hd1]; nlinarith [hb'.2.1]
    · rw [hd2]; nlinarith [hb'.2.2]
  · have hqK : q ∈ K := by
      rcases le_or_gt 0 q with h0 | h0
      · left; rw [abs_of_nonneg h0] at hq hq1; exact ⟨hq, not_lt.mp hq1⟩
      · right; rw [abs_of_neg h0] at hq hq1; exact ⟨by linarith [not_lt.mp hq1], by linarith⟩
    refine ⟨?_, ?_, ?_⟩
    · have := hB0 q hqK
      exact this.trans ((le_max_left B0 _).trans (le_max_right _ _))
    · have := hB1 q hqK
      exact this.trans (((le_max_left B1 B2).trans (le_max_right B0 _)).trans (le_max_right _ _))
    · have := hB2 q hqK
      exact this.trans (((le_max_right B1 B2).trans (le_max_right B0 _)).trans (le_max_right _ _))

/-- info: 'FormalResearch.SignUncertainty.seedV_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedV_contDiffOn

/-- info: 'FormalResearch.SignUncertainty.seedV_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedV_near

/-- info: 'FormalResearch.SignUncertainty.seedV_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedV_far

end FormalResearch.SignUncertainty
