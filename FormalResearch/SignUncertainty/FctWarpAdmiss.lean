module

public import FormalResearch.SignUncertainty.FctDcomp
public import FormalResearch.SignUncertainty.FctCompDPart2a
public import FormalResearch.SignUncertainty.FctWarpEdge

/-!
# Step 1 of `fct:s4-proof` for the warp summand (`fct:main-hankel`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, `fct:s4-proof` ("Every summand obeys `uct:admiss` with `α = 1/2`: in
`W̃^warp`, `Φ̂_c = O(|ζ|³)` cancels the `ζ^{-5/2}` singularity of `H_*/G_ε`, `|Φ̂_c| ≤ C log log(4+|τ|)` (`fct:splitting` (2)),
`|H_*/G_ε| = O((1+|τ|)² e^{-π|τ|})`", `uct:outer-growth`) and `fct:comp-D`.

* `fctWarp_admissible`: for `c ≥ c₀`, `ε = ±1`, `ctWwarp Φ̂ (fctDcomp K4 alpha) ε c` satisfies `StripAdmissFullData (1/2)` and
  `W(1-ζ) = εW(ζ)` on `S̄`.  This was the field `warp_admissible` of `FctMainHankelInputs`.
* Proved parts: `D_{τ₁}` (`fctDcomp_compData`: holomorphy, continuity, bound, `D(1-ζ) = D(ζ)`, real symmetry, `C²` left edge trace from `fct_comp_D_part1`);
  `H_*/G_ε` (`ctHG_oneSub`, `ctHG_conj`, `ctHG_differentiableOn`, `ctHG_continuousOn`, `ctHG_near`, `ctHG_far`); the assembly
  `warpMul_admissible` for abstract `SplittingData Φ`, `CompData D`, with the edge calculus `EJ` of `FctWarpEdge`.
* Named input: `FctSplittingStmt` (`fct:splitting` (1)-(2) for `Φ̂_c`); its holomorphy and real-symmetry clauses are proved from the descent bound (`FctSplittingWarp`, `FctSplittingConj`), the rest is the field `splitting_rest` of `FctMainHankelInputs`.

Class: proved under the explicit hypothesis `FctSplittingStmt`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctMoment

namespace FormalResearch.SignUncertainty

/-! ### `Env2` of `exp` -/

lemma Env2.neg {G : ℝ → ℂ} {P : ℝ → ℝ} (h : Env2 G P) : Env2 (fun τ => -G τ) P := by
  refine ⟨h.1.neg, fun τ => ?_⟩
  have h1 : deriv (fun τ => -G τ) = fun τ => -deriv G τ := funext fun τ => deriv.neg
  have h2 : deriv (deriv (fun τ => -G τ)) = fun τ => -deriv (deriv G) τ := by
    rw [h1]; funext τ; exact deriv.neg
  rw [h2, h1]; simp only [norm_neg]; exact h.2 τ

lemma Env2.cexp {G : ℝ → ℂ} {B b : ℝ} (h : Env2 G (fun _ => B)) (hb : ∀ τ, ‖Complex.exp (G τ)‖ ≤ b) :
    Env2 (fun τ => Complex.exp (G τ)) (fun _ => b * (1 + 2 * B + B ^ 2)) := by
  have := (h.neg).exp_neg (fun _ => b) (fun τ => by simpa using hb τ)
  simpa using this

/-! ### The compensator `exp (g_D[v])` -/

section CompD

variable {v : ℝ → ℝ}

lemma stripCompD_hol (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hs : HasCompactSupport v) :
    DifferentiableOn ℂ (fun ζ => Complex.exp (stripCompGExt v ζ)) strip :=
  ((differentiableOn_stripCompG hv.continuous hs).congr fun _ hz => stripCompGExt_eq_of_mem_strip hz).cexp

lemma stripCompD_cont (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hs : HasCompactSupport v) :
    ContinuousOn (fun ζ => Complex.exp (stripCompGExt v ζ)) closedStrip :=
  (continuousOn_stripCompGExt hv hs).cexp

lemma stripCompGExt_conj (he : ∀ t, v (-t) = v t) (ζ : ℂ) :
    stripCompGExt v (starRingEnd ℂ ζ) = starRingEnd ℂ (stripCompGExt v ζ) := by
  have hθ := fctThetaD_odd he
  by_cases hin : ζ ∈ strip
  · have hin' : starRingEnd ℂ ζ ∈ strip := ⟨by simpa using hin.1, by simpa using hin.2⟩
    rw [stripCompGExt_eq_of_mem_strip hin', stripCompGExt_eq_of_mem_strip hin]
    exact stripCompG_conj he ζ
  · unfold stripCompGExt
    simp only [Complex.conj_re, Complex.conj_im]
    rcases le_or_gt ζ.re 0 with h0 | h0
    · simp only [h0, ite_true, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, he, hθ]
      push_cast; ring
    · have h1 : 1 ≤ ζ.re := by
        by_contra h
        exact hin ⟨h0, not_le.mp h⟩
      have h0' : ¬ ζ.re ≤ 0 := not_le.mpr h0
      simp only [h0', h1, ite_false, ite_true, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, he, hθ]
      push_cast; ring

lemma stripCompD_edge_env2 (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hs : HasCompactSupport v) (B : ℕ → ℝ)
    (hB : ∀ r : ℕ, r ≤ 2 → ∀ ζ ∈ closedStrip, ‖stripCompGExt (iteratedDeriv r v) ζ‖ ≤ B r) :
    ∃ P : ℝ, 0 ≤ P ∧ Env2 (fun τ : ℝ => Complex.exp (stripCompGExt v ((τ : ℂ) * Complex.I))) (fun _ => P) := by
  have hθ : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD v) := contDiff_fctThetaD hv hs
  set G : ℕ → ℝ → ℂ := fun r τ => ((iteratedDeriv r v τ : ℝ) : ℂ) + Complex.I * ((iteratedDeriv r (fctThetaD v) τ : ℝ) : ℂ)
    with hGdef
  have hB0 : ∀ r, r ≤ 2 → 0 ≤ B r := fun r hr =>
    (norm_nonneg _).trans (hB r hr 0 ⟨by simp, by simp⟩)
  have hGn : ∀ r, r ≤ 2 → ∀ τ : ℝ, ‖G r τ‖ ≤ B r := fun r hr τ => by
    have := hB r hr ((τ : ℂ) * Complex.I) ⟨by simp, by simp⟩
    rw [stripCompGExt_left, ← iteratedDeriv_fctThetaD hv hs r] at this
    exact this
  have hGd : ∀ r τ, HasDerivAt (G r) (G (r + 1) τ) τ := fun r τ => by
    have h1 : HasDerivAt (iteratedDeriv r v) (iteratedDeriv (r + 1) v τ) τ := by
      rw [iteratedDeriv_succ]
      exact (((contDiff_iteratedDeriv_infty hv r).differentiable (by simp)) τ).hasDerivAt
    have h2 : HasDerivAt (iteratedDeriv r (fctThetaD v)) (iteratedDeriv (r + 1) (fctThetaD v) τ) τ := by
      rw [iteratedDeriv_succ]
      exact (((contDiff_iteratedDeriv_infty hθ r).differentiable (by simp)) τ).hasDerivAt
    exact h1.ofReal_comp.add (h2.ofReal_comp.const_mul Complex.I)
  have hd0 : deriv (G 0) = G 1 := funext fun τ => (hGd 0 τ).deriv
  have hd1 : deriv (G 1) = G 2 := funext fun τ => (hGd 1 τ).deriv
  have hc : ContDiff ℝ 2 (G 0) := by
    have h1 : ContDiff ℝ 2 (fun τ : ℝ => ((v τ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hv.of_le (by simp))
    have h2 : ContDiff ℝ 2 (fun τ : ℝ => ((fctThetaD v τ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hθ.of_le (by simp))
    simpa [hGdef] using h1.add (contDiff_const.mul h2)
  have hE : Env2 (G 0) (fun _ => B 0 + B 1 + B 2) := by
    refine ⟨hc, fun τ => ?_⟩
    have b0 := hB0 0 (by norm_num); have b1 := hB0 1 (by norm_num); have b2 := hB0 2 (by norm_num)
    refine ⟨?_, ?_, ?_⟩
    · linarith [hGn 0 (by norm_num) τ]
    · rw [hd0]; linarith [hGn 1 (by norm_num) τ]
    · rw [hd0, hd1]; linarith [hGn 2 (by norm_num) τ]
  have hb : ∀ τ, ‖Complex.exp (G 0 τ)‖ ≤ Real.exp (B 0) := fun τ => by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (hGn 0 (by norm_num) τ))
  have hX := hE.cexp hb
  have hfun : (fun τ : ℝ => Complex.exp (stripCompGExt v ((τ : ℂ) * Complex.I))) = fun τ => Complex.exp (G 0 τ) := by
    funext τ
    rw [stripCompGExt_left]
    simp [hGdef]
  rw [hfun]
  have b0 := hB0 0 (by norm_num); have b1 := hB0 1 (by norm_num); have b2 := hB0 2 (by norm_num)
  exact ⟨_, by positivity, hX⟩

end CompD

/-! ### The fixed factor `H_*/G_ε` (`ctHG`) -/

lemma ctHG_zero (ε : ℝ) : ctHG ε 0 = 0 := by
  unfold ctHG; simp

lemma ctHG_one (ε : ℝ) : ctHG ε 1 = 0 := by
  unfold ctHG; simp

lemma ctHG_oneSub {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    ctHG ε (1 - ζ) = (ε : ℂ) * ctHG ε ζ := by
  unfold ctHG
  rw [uctSeedZ_oneSub hε, outerHbar_oneSub hζ, sub_sub_cancel]
  ring

lemma arg_ne_pi_of_re_nonneg {z : ℂ} (h : 0 ≤ z.re) : z.arg ≠ π := by
  intro hz
  have := Complex.arg_eq_pi_iff.mp hz
  linarith [this.1]

lemma ctHG_conj (ε : ℝ) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    ctHG ε (starRingEnd ℂ ζ) = starRingEnd ℂ (ctHG ε ζ) := by
  have h1 : (1 - ζ) ∈ closedStrip := ⟨by simp [hζ.2], by simp [hζ.1]⟩
  have e : starRingEnd ℂ (5 / 2 : ℂ) = 5 / 2 := by rw [map_div₀, map_ofNat (starRingEnd ℂ) 5, map_ofNat (starRingEnd ℂ) 2]
  have c1 : starRingEnd ℂ ζ ^ (5 / 2 : ℂ) = starRingEnd ℂ (ζ ^ (5 / 2 : ℂ)) := by
    have := Complex.conj_cpow ζ (5 / 2 : ℂ) (arg_ne_pi_of_re_nonneg hζ.1)
    rw [e] at this; exact this
  have c2 : (1 - starRingEnd ℂ ζ) ^ (5 / 2 : ℂ) = starRingEnd ℂ ((1 - ζ) ^ (5 / 2 : ℂ)) := by
    have := Complex.conj_cpow (1 - ζ) (5 / 2 : ℂ) (arg_ne_pi_of_re_nonneg h1.1)
    rw [e] at this; simpa using this
  unfold ctHG
  rw [uctSeedZ_conj, outerHbar_conj hζ, ← map_neg, Complex.exp_conj, c1, c2]
  simp only [map_mul, map_div₀]

lemma mem_slit_of_closedStrip {ζ : ℂ} (hζ : ζ ∈ closedStrip) (h0 : ζ ≠ 0) : ζ ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rcases hζ.1.lt_or_eq with h | h
  · exact Or.inl h
  · right; intro him; apply h0; apply Complex.ext <;> simp [← h, him]

lemma ctHG_differentiableOn (ε : ℝ) : DifferentiableOn ℂ (ctHG ε) strip := by
  have hZ : DifferentiableOn ℂ (uctSeedZ ε) strip :=
    (differentiableOn_uctSeedZ ε).mono fun ζ hζ => ⟨by linarith [hζ.1], by linarith [hζ.2]⟩
  have hH : DifferentiableOn ℂ outerHbar strip := differentiableOn_outerH.congr fun z hz => outerHbar_of_mem_strip hz
  have hslit : ∀ ζ ∈ strip, ζ ∈ Complex.slitPlane := fun ζ hζ => Or.inl hζ.1
  have hslit1 : ∀ ζ ∈ strip, 1 - ζ ∈ Complex.slitPlane := fun ζ hζ => Or.inl (by simp; linarith [hζ.2])
  have hp : DifferentiableOn ℂ (fun ζ : ℂ => ζ ^ (5 / 2 : ℂ)) strip :=
    DifferentiableOn.cpow differentiableOn_id (differentiableOn_const _) hslit
  have hq : DifferentiableOn ℂ (fun ζ : ℂ => (1 - ζ) ^ (5 / 2 : ℂ)) strip :=
    DifferentiableOn.cpow (differentiableOn_const _ |>.sub differentiableOn_id) (differentiableOn_const _) hslit1
  unfold ctHG
  refine (hZ.mul hH.neg.cexp).div (hp.mul hq) fun ζ hζ => ?_
  have h1 : ζ ^ (5 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨h, -⟩
    have := hζ.1; rw [h] at this; simp at this
  have h2 : (1 - ζ) ^ (5 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨h, -⟩
    have := hζ.2; have h' : ζ = 1 := by linear_combination -h
    rw [h'] at this; simp at this
  exact mul_ne_zero h1 h2

lemma ctHG_continuousOn (ε : ℝ) :
    ContinuousOn (ctHG ε) {ζ : ℂ | ζ ∈ closedStrip ∧ ζ ≠ 0 ∧ ζ ≠ 1} := by
  have hZ : ContinuousOn (uctSeedZ ε) closedStrip :=
    (differentiableOn_uctSeedZ ε).continuousOn.mono fun ζ (hζ : ζ ∈ closedStrip) =>
      (⟨by linarith [hζ.1], by linarith [hζ.2]⟩ : -1 < ζ.re ∧ ζ.re < 2)
  have hH : ContinuousOn outerHbar closedStrip := continuousOn_outerHbar
  have hmem1 : ∀ ζ : ℂ, ζ ∈ {ζ : ℂ | ζ ∈ closedStrip ∧ ζ ≠ 0 ∧ ζ ≠ 1} → 1 - ζ ∈ closedStrip := fun ζ hζ =>
    ⟨by simp [hζ.1.2], by simp [hζ.1.1]⟩
  have hslit : ∀ ζ ∈ {ζ : ℂ | ζ ∈ closedStrip ∧ ζ ≠ 0 ∧ ζ ≠ 1}, ζ ∈ Complex.slitPlane := fun ζ hζ =>
    mem_slit_of_closedStrip hζ.1 hζ.2.1
  have hslit1 : ∀ ζ ∈ {ζ : ℂ | ζ ∈ closedStrip ∧ ζ ≠ 0 ∧ ζ ≠ 1}, 1 - ζ ∈ Complex.slitPlane := fun ζ hζ =>
    mem_slit_of_closedStrip (hmem1 ζ hζ) (fun h => hζ.2.2 (by linear_combination -h))
  have hp : DifferentiableOn ℂ (fun ζ : ℂ => ζ ^ (5 / 2 : ℂ)) {ζ : ℂ | ζ ∈ closedStrip ∧ ζ ≠ 0 ∧ ζ ≠ 1} :=
    DifferentiableOn.cpow differentiableOn_id (differentiableOn_const _) hslit
  have hq : DifferentiableOn ℂ (fun ζ : ℂ => (1 - ζ) ^ (5 / 2 : ℂ)) {ζ : ℂ | ζ ∈ closedStrip ∧ ζ ≠ 0 ∧ ζ ≠ 1} :=
    DifferentiableOn.cpow (differentiableOn_const _ |>.sub differentiableOn_id) (differentiableOn_const _) hslit1
  unfold ctHG
  have hsub : {ζ : ℂ | ζ ∈ closedStrip ∧ ζ ≠ 0 ∧ ζ ≠ 1} ⊆ closedStrip := fun ζ hζ => hζ.1
  refine ((hZ.mono hsub).mul (hH.mono hsub).neg.cexp).div (hp.continuousOn.mul hq.continuousOn) fun ζ hζ => ?_
  have h1 : ζ ^ (5 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨h, -⟩; exact hζ.2.1 h
  have h2 : (1 - ζ) ^ (5 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨h, -⟩; exact hζ.2.2 (by linear_combination -h)
  exact mul_ne_zero h1 h2

lemma ctHG_norm_cpow {z : ℂ} (hz : z ≠ 0) : ‖z ^ (5 / 2 : ℂ)‖ = ‖z‖ ^ (5 / 2 : ℝ) := by
  rw [Complex.norm_cpow_of_ne_zero hz]; simp

lemma ctHG_norm_eq (ε : ℝ) {ζ : ℂ} (h0 : ζ ≠ 0) (h1 : 1 - ζ ≠ 0) :
    ‖ctHG ε ζ‖ = ‖uctSeedZ ε ζ * Complex.exp (-outerHbar ζ)‖ / (‖ζ‖ ^ (5 / 2 : ℝ) * ‖1 - ζ‖ ^ (5 / 2 : ℝ)) := by
  unfold ctHG
  rw [norm_div, norm_mul (ζ ^ (5 / 2 : ℂ)), ctHG_norm_cpow h0, ctHG_norm_cpow h1]

lemma ctHG_near (ε : ℝ) : ∃ MH : ℝ, 0 ≤ MH ∧ ∀ ζ ∈ closedStrip, ζ ≠ 0 → ‖ζ‖ ≤ 1 / 2 →
    ‖ctHG ε ζ‖ ≤ MH * ‖ζ‖ ^ (-(5 / 2 : ℝ)) := by
  have hZ : ContinuousOn (uctSeedZ ε) closedStrip :=
    (differentiableOn_uctSeedZ ε).continuousOn.mono fun ζ (hζ : ζ ∈ closedStrip) =>
      (⟨by linarith [hζ.1], by linarith [hζ.2]⟩ : -1 < ζ.re ∧ ζ.re < 2)
  have hH : ContinuousOn outerHbar closedStrip := continuousOn_outerHbar
  have hcl : IsClosed closedStrip :=
    (isClosed_le continuous_const Complex.continuous_re).inter (isClosed_le Complex.continuous_re continuous_const)
  have hK : IsCompact (closedStrip ∩ Metric.closedBall (0 : ℂ) (1 / 2)) :=
    (isCompact_closedBall (0 : ℂ) (1 / 2)).inter_left hcl
  have hf : ContinuousOn (fun ζ => uctSeedZ ε ζ * Complex.exp (-outerHbar ζ)) (closedStrip ∩ Metric.closedBall (0 : ℂ) (1 / 2)) :=
    ((hZ.mul hH.neg.cexp).mono Set.inter_subset_left)
  obtain ⟨MZ, hMZ⟩ := hK.exists_bound_of_continuousOn hf
  have hq : (0 : ℝ) < (1 / 2 : ℝ) ^ (5 / 2 : ℝ) := by positivity
  refine ⟨|MZ| / (1 / 2 : ℝ) ^ (5 / 2 : ℝ), by positivity, fun ζ hζ hζ0 hb => ?_⟩
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  have h1ζ : (1 / 2 : ℝ) ≤ ‖1 - ζ‖ := by
    have := norm_sub_norm_le (1 : ℂ) ζ
    simp at this; linarith
  have h1ne : (1 - ζ) ≠ 0 := by intro h; rw [h] at h1ζ; simp at h1ζ; linarith
  rw [ctHG_norm_eq ε hζ0 h1ne]
  have hf' : ‖uctSeedZ ε ζ * Complex.exp (-outerHbar ζ)‖ ≤ |MZ| :=
    (hMZ ζ ⟨hζ, by simpa using hb⟩).trans (le_abs_self _)
  have e3 : (1 / 2 : ℝ) ^ (5 / 2 : ℝ) ≤ ‖1 - ζ‖ ^ (5 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) h1ζ (by norm_num)
  have hp1 : 0 < ‖ζ‖ ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
  rw [Real.rpow_neg hn.le, div_le_iff₀ (mul_pos hp1 (lt_of_lt_of_le hq e3))]
  calc ‖uctSeedZ ε ζ * Complex.exp (-outerHbar ζ)‖ ≤ |MZ| := hf'
    _ = |MZ| / (1 / 2 : ℝ) ^ (5 / 2 : ℝ) * (‖ζ‖ ^ (5 / 2 : ℝ))⁻¹ * ((1 / 2 : ℝ) ^ (5 / 2 : ℝ) * ‖ζ‖ ^ (5 / 2 : ℝ)) := by
        field_simp
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [hp1]

lemma ctHG_far (ε : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ ζ ∈ closedStrip, 1 / 2 ≤ |ζ.im| →
    ‖ctHG ε ζ‖ ≤ K * ((1 + |ζ.im|) ^ 6 * Real.exp (-(π * |ζ.im|))) := by
  obtain ⟨Ce, hCe⟩ := norm_exp_neg_outerHbar_le
  have hCe0 : 0 ≤ max Ce 0 := le_max_right _ _
  have hq : (0 : ℝ) < (1 / 2 : ℝ) ^ (5 / 2 : ℝ) := by positivity
  refine ⟨32 * π ^ 2 * max Ce 0 / ((1 / 2 : ℝ) ^ (5 / 2 : ℝ) * (1 / 2 : ℝ) ^ (5 / 2 : ℝ)), by positivity, fun ζ hζ hτ => ?_⟩
  have hZ := uctSeedZ_bound ε hζ hτ
  have hE := hCe ζ hζ
  set x : ℝ := |ζ.im| with hx
  have hx0 : 0 ≤ x := abs_nonneg _
  have hE' : ‖Complex.exp (-outerHbar ζ)‖ ≤ max Ce 0 * (1 + x) ^ 2 := by
    refine hE.trans ?_
    have h1 : 1 + ζ.im ^ 2 ≤ (1 + x) ^ 2 := by
      have := sq_abs ζ.im
      nlinarith
    calc Ce * (1 + ζ.im ^ 2) ≤ max Ce 0 * (1 + ζ.im ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max Ce 0 * (1 + x) ^ 2 := mul_le_mul_of_nonneg_left h1 hCe0
  have hnζ : (1 / 2 : ℝ) ≤ ‖ζ‖ := hτ.trans (Complex.abs_im_le_norm ζ)
  have hn1 : (1 / 2 : ℝ) ≤ ‖1 - ζ‖ := by
    have := Complex.abs_im_le_norm (1 - ζ)
    simp at this; exact hτ.trans this
  have hζ0 : ζ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hnζ)
  have h1ne : 1 - ζ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hn1)
  have e2 : (1 / 2 : ℝ) ^ (5 / 2 : ℝ) ≤ ‖ζ‖ ^ (5 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hnζ (by norm_num)
  have e3 : (1 / 2 : ℝ) ^ (5 / 2 : ℝ) ≤ ‖1 - ζ‖ ^ (5 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hn1 (by norm_num)
  rw [ctHG_norm_eq ε hζ0 h1ne, norm_mul]
  rw [div_le_iff₀ (mul_pos (lt_of_lt_of_le hq e2) (lt_of_lt_of_le hq e3))]
  have hnum : ‖uctSeedZ ε ζ‖ * ‖Complex.exp (-outerHbar ζ)‖ ≤
      (32 * π ^ 2 * (1 + x) ^ 4 * Real.exp (-(π * x))) * (max Ce 0 * (1 + x) ^ 2) := by gcongr
  have hden : (1 / 2 : ℝ) ^ (5 / 2 : ℝ) * (1 / 2 : ℝ) ^ (5 / 2 : ℝ) ≤ ‖ζ‖ ^ (5 / 2 : ℝ) * ‖1 - ζ‖ ^ (5 / 2 : ℝ) :=
    mul_le_mul e2 e3 hq.le (lt_of_lt_of_le hq e2).le
  have hpos : 0 ≤ (32 * π ^ 2 * (1 + x) ^ 4 * Real.exp (-(π * x))) * (max Ce 0 * (1 + x) ^ 2) := by positivity
  calc ‖uctSeedZ ε ζ‖ * ‖Complex.exp (-outerHbar ζ)‖ ≤ (32 * π ^ 2 * (1 + x) ^ 4 * Real.exp (-(π * x))) * (max Ce 0 * (1 + x) ^ 2) := hnum
    _ = 32 * π ^ 2 * max Ce 0 / ((1 / 2 : ℝ) ^ (5 / 2 : ℝ) * (1 / 2 : ℝ) ^ (5 / 2 : ℝ)) * ((1 + x) ^ 6 * Real.exp (-(π * x))) *
          ((1 / 2 : ℝ) ^ (5 / 2 : ℝ) * (1 / 2 : ℝ) ^ (5 / 2 : ℝ)) := by field_simp
    _ ≤ _ := by gcongr

/-! ### The data about `Φ̂_c` and `D_{τ₁}` used for one `(ε, c)` -/

lemma one_le_log_four : (1 : ℝ) ≤ Real.log 4 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

lemma loglog_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.log (Real.log (4 + x)) := by
  apply Real.log_nonneg
  calc (1 : ℝ) ≤ Real.log 4 := one_le_log_four
    _ ≤ Real.log (4 + x) := Real.log_le_log (by norm_num) (by linarith)

lemma loglog_le {x : ℝ} (hx : 0 ≤ x) : Real.log (Real.log (4 + x)) ≤ 4 + x := by
  have h1 : 0 ≤ Real.log (4 + x) := le_trans (by linarith [one_le_log_four]) (Real.log_le_log (by norm_num) (by linarith) : Real.log 4 ≤ Real.log (4 + x))
  calc Real.log (Real.log (4 + x)) ≤ Real.log (4 + x) := Real.log_le_self h1
    _ ≤ 4 + x := Real.log_le_self (by linarith)

/-- **`fct:splitting` (1)-(2) for one `Φ̂_c`** (`Φ : ℂ → ℂ`, the data of `FctSplittingStmt`). -/
structure SplittingData (Φ : ℂ → ℂ) : Prop where
  /-- holomorphic on `Re ζ > 0` (`fct:splitting` (2)) -/
  hol : DifferentiableOn ℂ Φ {ζ : ℂ | 0 < ζ.re}
  /-- continuous up to the left edge `Re ζ = 0` -/
  cont : ContinuousOn Φ closedStrip
  /-- real-symmetric -/
  conj : ∀ ζ ∈ closedStrip, Φ (starRingEnd ℂ ζ) = starRingEnd ℂ (Φ ζ)
  /-- left edge trace is `C²` off `0` -/
  left_c2 : ContDiffOn ℝ 2 (fun t : ℝ => Φ ((t : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0}
  bounds : ∃ M : ℝ, 0 ≤ M ∧
    -- `|Φ̂_c| ≤ M log log (4 + |τ|)` on `S̄`
    (∀ ζ ∈ closedStrip, ‖Φ ζ‖ ≤ M * Real.log (Real.log (4 + |ζ.im|))) ∧
    -- `Φ̂_c = O(ζ³)` at `ζ = 0` (`fct:splitting` (1))
    (∀ ζ ∈ closedStrip, ‖ζ‖ ≤ 1 → ‖Φ ζ‖ ≤ M * ‖ζ‖ ^ 3) ∧
    -- left edge derivative bounds (`(fct:Fminus-edge)`, `j = 1, 2`)
    (∀ τ : ℝ, τ ≠ 0 →
      ‖deriv (fun t : ℝ => Φ ((t : ℂ) * Complex.I)) τ‖ ≤ M * min 1 (|τ| ^ 2) ∧
      ‖deriv (deriv (fun t : ℝ => Φ ((t : ℂ) * Complex.I))) τ‖ ≤ M * min 1 |τ|) ∧
    -- right edge derivative bounds (`(fct:Eminus-edge)`, `j = 1, 2`)
    (∀ τ : ℝ, ‖deriv (fun t : ℝ => Φ (1 - (t : ℂ) * Complex.I)) τ‖ ≤ M ∧
      ‖deriv (deriv (fun t : ℝ => Φ (1 - (t : ℂ) * Complex.I))) τ‖ ≤ M)

/-- `D_{τ₁}` for one `(ε, c)`: holomorphic on `S`, continuous and bounded on `S̄`, real-symmetric, `D(1-ζ) = D(ζ)`, and a `C²` left edge
trace with bounded derivatives. -/
structure CompData (Dd : ℂ → ℂ) : Prop where
  hol : DifferentiableOn ℂ Dd strip
  cont : ContinuousOn Dd closedStrip
  conj : ∀ ζ ∈ closedStrip, Dd (starRingEnd ℂ ζ) = starRingEnd ℂ (Dd ζ)
  sym : ∀ ζ ∈ closedStrip, Dd (1 - ζ) = Dd ζ
  bd : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖Dd ζ‖ ≤ B
  env : ∃ P : ℝ, 0 ≤ P ∧ Env2 (fun τ : ℝ => Dd ((τ : ℂ) * Complex.I)) (fun _ => P)

/-- The warp multiplier for fixed `(ε, c)`. -/
noncomputable def warpMul (Cc : ℝ) (ε : ℝ) (Φ Dd : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  (Cc : ℂ) * (Φ ζ * Φ (1 - ζ) * Dd ζ * ctHG ε ζ)

lemma ctWwarp_eq_warpMul (PhiHat D : ℝ → ℝ → ℂ → ℂ) (ε c : ℝ) :
    ctWwarp PhiHat D ε c = warpMul (uctCAi * c ^ (-(5 / 6 : ℝ))) ε (PhiHat ε c) (D ε c) := rfl

section Warp

variable {Cc ε : ℝ} {Φ Dd : ℂ → ℂ}

lemma warpMul_zero : warpMul Cc ε Φ Dd 0 = 0 := by
  unfold warpMul; rw [ctHG_zero]; simp

lemma warpMul_oneSub (hε : ε = 1 ∨ ε = -1) (hD : CompData Dd) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    warpMul Cc ε Φ Dd (1 - ζ) = (ε : ℂ) * warpMul Cc ε Φ Dd ζ := by
  unfold warpMul
  rw [sub_sub_cancel, hD.sym ζ hζ, ctHG_oneSub hε hζ]
  ring

lemma warpMul_one (hε : ε = 1 ∨ ε = -1) (hD : CompData Dd) : warpMul Cc ε Φ Dd 1 = 0 := by
  have := warpMul_oneSub (Cc := Cc) (Φ := Φ) hε hD (ζ := 0) ⟨by simp, by simp⟩
  rw [sub_zero, warpMul_zero, mul_zero] at this
  exact this

lemma warpMul_conj (hΦ : SplittingData Φ) (hD : CompData Dd) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    warpMul Cc ε Φ Dd (starRingEnd ℂ ζ) = starRingEnd ℂ (warpMul Cc ε Φ Dd ζ) := by
  have h1 : (1 - ζ) ∈ closedStrip := ⟨by simp [hζ.2], by simp [hζ.1]⟩
  unfold warpMul
  have e : (1 : ℂ) - starRingEnd ℂ ζ = starRingEnd ℂ (1 - ζ) := by simp
  rw [e, hΦ.conj ζ hζ, hΦ.conj (1 - ζ) h1, hD.conj ζ hζ, ctHG_conj ε hζ]
  simp only [map_mul, Complex.conj_ofReal]

lemma warpMul_differentiableOn (hΦ : SplittingData Φ) (hD : CompData Dd) :
    DifferentiableOn ℂ (warpMul Cc ε Φ Dd) strip := by
  have h1 : DifferentiableOn ℂ Φ strip := hΦ.hol.mono fun ζ hζ => hζ.1
  have h2 : DifferentiableOn ℂ (fun ζ => Φ (1 - ζ)) strip :=
    hΦ.hol.comp ((differentiableOn_const 1).sub differentiableOn_id) fun ζ hζ => by
      show 0 < (1 - ζ).re
      simp; linarith [hζ.2]
  unfold warpMul
  exact ((h1.mul h2).mul hD.hol |>.mul (ctHG_differentiableOn ε)).const_mul _

lemma warpMul_continuousOn (hε : ε = 1 ∨ ε = -1) (hΦ : SplittingData Φ) (hD : CompData Dd)
    (htend : Tendsto (warpMul Cc ε Φ Dd) (𝓝[closedStrip \ {0}] 0) (𝓝 0)) :
    ContinuousOn (warpMul Cc ε Φ Dd) closedStrip := by
  intro ζ hζ
  by_cases h0 : ζ = 0
  · subst h0
    have : ContinuousWithinAt (warpMul Cc ε Φ Dd) (closedStrip \ {0}) 0 := by
      rw [ContinuousWithinAt, warpMul_zero]; exact htend
    exact continuousWithinAt_sdiff_singleton.mp this
  by_cases h1 : ζ = 1
  · subst h1
    have hc0 : ContinuousWithinAt (warpMul Cc ε Φ Dd) closedStrip ((fun z : ℂ => 1 - z) 1) := by
      have : ContinuousWithinAt (warpMul Cc ε Φ Dd) (closedStrip \ {0}) 0 := by
        rw [ContinuousWithinAt, warpMul_zero]; exact htend
      simpa using continuousWithinAt_sdiff_singleton.mp this
    have hcomp : ContinuousWithinAt (fun z : ℂ => (ε : ℂ) * warpMul Cc ε Φ Dd (1 - z)) closedStrip 1 :=
      (hc0.comp (f := fun z : ℂ => 1 - z) (continuousWithinAt_const.sub continuousWithinAt_id)
        (fun z hz => (⟨by simp [hz.2], by simp [hz.1]⟩ : (1 - z) ∈ closedStrip))).const_mul _
    have hεε : (ε : ℂ) * ε = 1 := by rcases hε with h | h <;> simp [h]
    refine hcomp.congr (fun z hz => ?_) ?_
    · rw [warpMul_oneSub hε hD hz]; linear_combination (-(warpMul Cc ε Φ Dd z)) * hεε
    · rw [warpMul_oneSub hε hD (⟨by simp, by simp⟩ : (1 : ℂ) ∈ closedStrip)]
      linear_combination (-(warpMul Cc ε Φ Dd 1)) * hεε
  · set T : Set ℂ := {ζ : ℂ | ζ ∈ closedStrip ∧ ζ ≠ 0 ∧ ζ ≠ 1} with hT
    have hΦc : ContinuousOn Φ T := hΦ.cont.mono fun z hz => hz.1
    have hΦ1 : ContinuousOn (fun z => Φ (1 - z)) T :=
      hΦ.cont.comp (continuousOn_const.sub continuousOn_id) fun z hz => (⟨by simp [hz.1.2], by simp [hz.1.1]⟩ : (1 - z) ∈ closedStrip)
    have hDc : ContinuousOn Dd T := hD.cont.mono fun z hz => hz.1
    have hW : ContinuousOn (warpMul Cc ε Φ Dd) T := by
      unfold warpMul
      exact (((hΦc.mul hΦ1).mul hDc).mul (ctHG_continuousOn ε)).const_mul _
    have hnh : T ∈ 𝓝[closedStrip] ζ := by
      have : {z : ℂ | z ≠ 0 ∧ z ≠ 1} ∈ 𝓝 ζ := (isOpen_ne.inter isOpen_ne).mem_nhds ⟨h0, h1⟩
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds this] with z hz hz'
      exact ⟨hz, hz'.1, hz'.2⟩
    exact (hW.continuousWithinAt ⟨hζ, h0, h1⟩).mono_of_mem_nhdsWithin hnh

lemma splitting_norm_le {M : ℝ} {Φ : ℂ → ℂ} (hM : 0 ≤ M)
    (h : ∀ ζ ∈ closedStrip, ‖Φ ζ‖ ≤ M * Real.log (Real.log (4 + |ζ.im|))) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    ‖Φ ζ‖ ≤ 4 * M * (1 + |ζ.im|) := by
  have := h ζ hζ
  have h2 := loglog_le (abs_nonneg ζ.im)
  have h3 : M * Real.log (Real.log (4 + |ζ.im|)) ≤ M * (4 + |ζ.im|) := mul_le_mul_of_nonneg_left h2 hM
  nlinarith [abs_nonneg ζ.im]

lemma warpMul_holder0 (hΦ : SplittingData Φ) (hD : CompData Dd) :
    ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖ζ‖ ≤ 1 / 2 →
      ‖warpMul Cc ε Φ Dd ζ - warpMul Cc ε Φ Dd 0‖ ≤ CH * ‖ζ‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨M, hM, hll, hcube, -, -⟩ := hΦ.bounds
  obtain ⟨BD, hBD⟩ := hD.bd
  obtain ⟨MH, hMH0, hMH⟩ := ctHG_near ε
  refine ⟨|Cc| * (M * (5 * M) * |BD|) * MH, fun ζ h0 h1 hb => ?_⟩
  rw [warpMul_zero, sub_zero]
  have hcl : ζ ∈ closedStrip := ⟨h0, h1⟩
  by_cases hz : ζ = 0
  · subst hz; rw [warpMul_zero]; simp
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hz
  have h1cl : (1 - ζ) ∈ closedStrip := ⟨by simp [h1], by simp [h0]⟩
  have hA : ‖Φ ζ‖ ≤ M * ‖ζ‖ ^ 3 := hcube ζ hcl (by linarith)
  have hB : ‖Φ (1 - ζ)‖ ≤ 5 * M := by
    have := hll (1 - ζ) h1cl
    have h2 : |(1 - ζ).im| ≤ 1 / 2 := by
      simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      exact (Complex.abs_im_le_norm ζ).trans hb
    have h3 := loglog_le (abs_nonneg (1 - ζ).im)
    have h4 : M * Real.log (Real.log (4 + |(1 - ζ).im|)) ≤ M * (4 + |(1 - ζ).im|) := mul_le_mul_of_nonneg_left h3 hM
    nlinarith
  have hC : ‖Dd ζ‖ ≤ |BD| := (hBD ζ hcl).trans (le_abs_self _)
  have hH : ‖ctHG ε ζ‖ ≤ MH * ‖ζ‖ ^ (-(5 / 2 : ℝ)) := hMH ζ hcl hz hb
  unfold warpMul
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul, norm_mul]
  have e : ‖ζ‖ ^ 3 * ‖ζ‖ ^ (-(5 / 2 : ℝ)) = ‖ζ‖ ^ (1 / 2 : ℝ) := by
    rw [show ‖ζ‖ ^ 3 = ‖ζ‖ ^ ((3 : ℕ) : ℝ) from (Real.rpow_natCast _ 3).symm, ← Real.rpow_add hn]; norm_num
  have hA' : ‖Φ ζ‖ * ‖Φ (1 - ζ)‖ * ‖Dd ζ‖ ≤ M * ‖ζ‖ ^ 3 * (5 * M) * |BD| :=
    mul_le_mul (mul_le_mul hA hB (norm_nonneg _) (by positivity)) hC (norm_nonneg _) (by positivity)
  calc |Cc| * (‖Φ ζ‖ * ‖Φ (1 - ζ)‖ * ‖Dd ζ‖ * ‖ctHG ε ζ‖)
      ≤ |Cc| * ((M * ‖ζ‖ ^ 3 * (5 * M) * |BD|) * (MH * ‖ζ‖ ^ (-(5 / 2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hA' hH (norm_nonneg _) (by positivity)) (abs_nonneg _)
    _ = |Cc| * (M * (5 * M) * |BD|) * MH * (‖ζ‖ ^ 3 * ‖ζ‖ ^ (-(5 / 2 : ℝ))) := by ring
    _ = _ := by rw [e]

lemma warpMul_holder1 (hε : ε = 1 ∨ ε = -1) (hΦ : SplittingData Φ) (hD : CompData Dd) :
    ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 →
      ‖warpMul Cc ε Φ Dd ζ - warpMul Cc ε Φ Dd 1‖ ≤ CH * ‖1 - ζ‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨CH, hCH⟩ := warpMul_holder0 (Cc := Cc) (ε := ε) hΦ hD
  refine ⟨CH, fun ζ h0 h1 hb => ?_⟩
  have h1cl : (1 - ζ) ∈ closedStrip := ⟨by simp [h1], by simp [h0]⟩
  have hs := warpMul_oneSub (Cc := Cc) (Φ := Φ) hε hD h1cl
  rw [sub_sub_cancel] at hs
  rw [warpMul_one hε hD, sub_zero, hs, norm_mul]
  have hεn : ‖(ε : ℂ)‖ = 1 := by rcases hε with h | h <;> simp [h]
  rw [hεn, one_mul]
  have := hCH (1 - ζ) (by simp [h1]) (by simp [h0]) hb
  rwa [warpMul_zero, sub_zero] at this

lemma warpMul_bound (hΦ : SplittingData Φ) (hD : CompData Dd)
    (hcont : ContinuousOn (warpMul Cc ε Φ Dd) closedStrip) :
    ∃ C : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖warpMul Cc ε Φ Dd ζ‖ ≤ C * (1 + |ζ.im|) ^ (-(2 : ℝ)) := by
  obtain ⟨M, hM, hll, -, -, -⟩ := hΦ.bounds
  obtain ⟨BD, hBD⟩ := hD.bd
  obtain ⟨K, hK0, hK⟩ := ctHG_far ε
  obtain ⟨M10, hM100, hM10⟩ := poly_exp_le_n 10
  have hcomp : IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc (-(1 / 2 : ℝ)) (1 / 2)) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨C0, hC0⟩ := hcomp.exists_bound_of_continuousOn (hcont.mono (fun ζ hζ => ⟨hζ.1.1, hζ.1.2⟩))
  have hC0' : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → |ζ.im| ≤ 1 / 2 → ‖warpMul Cc ε Φ Dd ζ‖ ≤ C0 := fun ζ h0 h1 h2 =>
    hC0 ζ ⟨⟨h0, h1⟩, abs_le.mp h2⟩
  have hC00 : 0 ≤ C0 := le_trans (norm_nonneg _) (hC0' 0 (by simp) (by simp) (by simp))
  set Kf : ℝ := |Cc| * (4 * M) * (4 * M) * |BD| * K with hKf
  have hKf0 : 0 ≤ Kf := by positivity
  refine ⟨max (C0 * (9 / 4)) (Kf * M10), fun ζ h0 h1 => ?_⟩
  set x : ℝ := |ζ.im| with hx
  have hx0 : 0 ≤ x := abs_nonneg _
  have hp : 0 < (1 + x) ^ 2 := by positivity
  rw [rpow_neg_two_eq (by linarith)]
  rw [← div_eq_mul_one_div, le_div_iff₀ hp]
  rcases lt_or_ge x (1 / 2) with hlt | hge
  · have := hC0' ζ h0 h1 hlt.le
    have h2 : (1 + x) ^ 2 ≤ 9 / 4 := by nlinarith
    calc ‖warpMul Cc ε Φ Dd ζ‖ * (1 + x) ^ 2 ≤ C0 * (9 / 4) := mul_le_mul this h2 hp.le hC00
      _ ≤ _ := le_max_left _ _
  · have hcl : ζ ∈ closedStrip := ⟨h0, h1⟩
    have h1cl : (1 - ζ) ∈ closedStrip := ⟨by simp [h1], by simp [h0]⟩
    have hA := splitting_norm_le hM hll hcl
    have hB := splitting_norm_le hM hll h1cl
    have him : |(1 - ζ).im| = x := by simp [hx]
    rw [him] at hB
    have hC : ‖Dd ζ‖ ≤ |BD| := (hBD ζ hcl).trans (le_abs_self _)
    have hH := hK ζ hcl hge
    have h3 := hM10 x hx0
    unfold warpMul
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul, norm_mul]
    have hprod : ‖Φ ζ‖ * ‖Φ (1 - ζ)‖ * ‖Dd ζ‖ * ‖ctHG ε ζ‖ ≤
        (4 * M * (1 + x)) * (4 * M * (1 + x)) * |BD| * (K * ((1 + x) ^ 6 * Real.exp (-(π * x)))) := by
      gcongr
    calc |Cc| * (‖Φ ζ‖ * ‖Φ (1 - ζ)‖ * ‖Dd ζ‖ * ‖ctHG ε ζ‖) * (1 + x) ^ 2
        ≤ |Cc| * ((4 * M * (1 + x)) * (4 * M * (1 + x)) * |BD| * (K * ((1 + x) ^ 6 * Real.exp (-(π * x))))) * (1 + x) ^ 2 := by
          gcongr
      _ = Kf * ((1 + x) ^ 10 * Real.exp (-(π * x))) := by rw [hKf]; ring
      _ ≤ Kf * M10 := mul_le_mul_of_nonneg_left h3 hKf0
      _ ≤ _ := le_max_right _ _

/-! ### The edge traces -/

lemma ejW_three_zero (τ : ℝ) : ejW 3 1 0 0 τ = |τ| ^ 3 * (1 + |τ|) := by
  unfold ejW
  rw [show (3 : ℝ) - ((0 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp

lemma ejW_three_one (τ : ℝ) : ejW 3 1 0 1 τ = |τ| ^ 2 * (1 + |τ|) ^ 2 := by
  unfold ejW
  rw [show (3 : ℝ) - ((1 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp

lemma ejW_three_two (τ : ℝ) : ejW 3 1 0 2 τ = |τ| * (1 + |τ|) ^ 3 := by
  unfold ejW
  rw [show (3 : ℝ) - ((2 : ℕ) : ℝ) = ((1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp

lemma ejW_zero_zero (τ : ℝ) : ejW 0 1 0 0 τ = 1 + |τ| := by
  unfold ejW; simp

lemma splitting_left_EJ (hΦ : SplittingData Φ) :
    ∃ M' : ℝ, EJ (fun t : ℝ => Φ ((t : ℂ) * Complex.I)) 3 1 0 M' := by
  obtain ⟨M, hM, hll, hcube, hL, -⟩ := hΦ.bounds
  refine ⟨4 * M, ⟨by positivity, hΦ.left_c2, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_⟩⟩
  · rw [ejW_three_zero]
    have hcl : ((τ : ℂ) * Complex.I) ∈ closedStrip := ⟨by simp, by simp⟩
    have hn : ‖(τ : ℂ) * Complex.I‖ = |τ| := by simp
    have h0 : 0 ≤ |τ| := abs_nonneg _
    rcases le_or_gt |τ| 1 with h | h
    · have := hcube _ hcl (by rw [hn]; exact h)
      rw [hn] at this
      have h3 : 0 ≤ M * |τ| ^ 3 := by positivity
      nlinarith [mul_nonneg h3 h0]
    · have := splitting_norm_le hM hll hcl
      have him : |((τ : ℂ) * Complex.I).im| = |τ| := by simp
      rw [him] at this
      have h3 : 1 ≤ |τ| ^ 3 := one_le_pow₀ h.le
      have : 0 ≤ M * (1 + |τ|) := by positivity
      nlinarith [mul_nonneg this (sub_nonneg.mpr h3)]
  · rw [ejW_three_one]
    have h0 : 0 ≤ |τ| := abs_nonneg _
    have := (hL τ hτ).1
    have h3 : M * min 1 (|τ| ^ 2) ≤ M * |τ| ^ 2 := mul_le_mul_of_nonneg_left (min_le_right _ _) hM
    have h4 : 1 ≤ (1 + |τ|) ^ 2 := one_le_pow₀ (by linarith)
    have h5 : 0 ≤ M * |τ| ^ 2 := by positivity
    nlinarith [mul_nonneg h5 (sub_nonneg.mpr h4)]
  · rw [ejW_three_two]
    have h0 : 0 ≤ |τ| := abs_nonneg _
    have := (hL τ hτ).2
    have h3 : M * min 1 |τ| ≤ M * |τ| := mul_le_mul_of_nonneg_left (min_le_right _ _) hM
    have h4 : 1 ≤ (1 + |τ|) ^ 3 := one_le_pow₀ (by linarith)
    have h5 : 0 ≤ M * |τ| := by positivity
    nlinarith [mul_nonneg h5 (sub_nonneg.mpr h4)]

lemma splitting_right_c2 (hΦ : SplittingData Φ) :
    ContDiffOn ℝ 2 (fun t : ℝ => Φ (1 - (t : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0} := by
  have hopen : IsOpen {ζ : ℂ | 0 < ζ.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : ContDiffOn ℂ 2 Φ {ζ : ℂ | 0 < ζ.re} := hΦ.hol.contDiffOn hopen
  have h2 : ContDiffOn ℝ 2 Φ {ζ : ℂ | 0 < ζ.re} := h1.restrict_scalars ℝ
  have hg : ContDiff ℝ 2 (fun t : ℝ => (1 : ℂ) - (t : ℂ) * Complex.I) :=
    contDiff_const.sub (Complex.ofRealCLM.contDiff.mul contDiff_const)
  exact h2.comp hg.contDiffOn (fun t _ => by simp)

lemma splitting_right_EJ (hΦ : SplittingData Φ) :
    ∃ M' : ℝ, EJ (fun t : ℝ => Φ (1 - (t : ℂ) * Complex.I)) 0 1 0 M' := by
  obtain ⟨M, hM, hll, -, -, hR⟩ := hΦ.bounds
  refine ⟨4 * M, ⟨by positivity, splitting_right_c2 hΦ, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_⟩⟩
  · rw [ejW_zero_zero]
    have hcl : (1 - (τ : ℂ) * Complex.I) ∈ closedStrip := ⟨by simp, by simp⟩
    have := splitting_norm_le hM hll hcl
    have him : |(1 - (τ : ℂ) * Complex.I).im| = |τ| := by simp
    rw [him] at this
    exact this
  · have hge := ejW_ge (b := 0) (N := 1) 1 hτ
    simp only [mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one, pow_one] at hge
    have h1 : 1 ≤ ejW 0 1 0 1 τ := by linarith [abs_nonneg τ]
    nlinarith [(hR τ).1]
  · have hge := ejW_ge (b := 0) (N := 1) 2 hτ
    simp only [mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one, pow_one] at hge
    have h1 : 1 ≤ ejW 0 1 0 2 τ := by linarith [abs_nonneg τ]
    nlinarith [(hR τ).2]

lemma edgeR_eq (τ : ℝ) : edgeR τ = ((1 - (τ : ℂ) * Complex.I) ^ (5 / 2 : ℂ))⁻¹ := by
  unfold edgeR
  rw [show (1 : ℂ) + (-Complex.I) * (τ : ℂ) = 1 - (τ : ℂ) * Complex.I by ring,
    show (((-(5 / 2) : ℝ)) : ℂ) = -(5 / 2 : ℂ) by push_cast; ring, Complex.cpow_neg]

lemma edgeS_eq (τ : ℝ) : edgeS τ = (((τ : ℂ) * Complex.I) ^ (5 / 2 : ℂ))⁻¹ := by
  unfold edgeS
  rw [show (0 : ℂ) + Complex.I * (τ : ℂ) = (τ : ℂ) * Complex.I by ring,
    show (((-(5 / 2) : ℝ)) : ℂ) = -(5 / 2 : ℂ) by push_cast; ring, Complex.cpow_neg]

lemma ctHG_edge (ε : ℝ) (τ : ℝ) :
    ctHG ε ((τ : ℂ) * Complex.I) = (uctSeedZ ε ((τ : ℂ) * Complex.I) * Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))) *
      edgeR τ * edgeS τ := by
  rw [edgeR_eq, edgeS_eq]; unfold ctHG; ring

lemma ejZE (ε : ℝ) : ∃ M : ℝ, EJ (fun τ : ℝ => uctSeedZ ε ((τ : ℂ) * Complex.I) * Complex.exp (-outerHbar ((τ : ℂ) * Complex.I)))
    0 (4 + 6) 1 M := by
  obtain ⟨CZ, hCZ0, hZ⟩ := env2_seedZi ε
  obtain ⟨aE, haE0, hE⟩ := env2_outerE
  have e1 : (fun τ : ℝ => uctSeedZ ε ((τ : ℂ) * Complex.I)) = fun τ : ℝ => uctSeedZ ε (0 + Complex.I * (τ : ℂ)) := by
    funext τ; congr 1; ring
  have e2 : (fun τ : ℝ => Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))) =
      fun τ : ℝ => Complex.exp (-outerHbar (Complex.I * (τ : ℂ))) := by
    funext τ; rw [mul_comm]
  have h1 : EJ (fun τ : ℝ => uctSeedZ ε ((τ : ℂ) * Complex.I)) 0 4 1 CZ := by
    rw [e1]
    refine EJ.of_env2 hZ hCZ0 4 (fun τ => le_of_eq ?_)
    ring_nf
  have h2 : EJ (fun τ : ℝ => Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))) 0 6 0 aE := by
    rw [e2]
    refine EJ.of_env2 hE haE0 6 (fun τ => le_of_eq ?_)
    simp
  exact ⟨_, (h1.mul h2).cast (by norm_num) (by norm_num)⟩

theorem warpMul_stripEdge0 (hΦ : SplittingData Φ) (hD : CompData Dd) :
    StripEdge0 (1 / 2 : ℝ) (warpMul Cc ε Φ Dd) := by
  obtain ⟨MA, hA⟩ := splitting_left_EJ hΦ
  obtain ⟨MB, hB⟩ := splitting_right_EJ hΦ
  obtain ⟨P, hP0, hE⟩ := hD.env
  obtain ⟨MZ, hZE⟩ := ejZE ε
  have hDe : EJ (fun τ : ℝ => Dd ((τ : ℂ) * Complex.I)) 0 0 0 P :=
    EJ.of_env2 hE hP0 0 (fun τ => by simp)
  have hbig := ((((hA.mul hB).mul hDe).mul hZE).mul edgeR_EJ).const_mul (Cc : ℂ) |>.mul edgeS_EJ
  have hcast := hbig.cast (a' := 1 / 2) (b' := 1) (by norm_num) (by norm_num)
  refine edge0_of_EJ hcast (fun τ hτ => ?_) warpMul_zero
  show warpMul Cc ε Φ Dd ((τ : ℂ) * Complex.I) = _
  unfold warpMul
  rw [ctHG_edge]
  ring

theorem warpMul_stripEdge1 (hε : ε = 1 ∨ ε = -1) (hΦ : SplittingData Φ) (hD : CompData Dd) :
    StripEdge1 (1 / 2 : ℝ) (warpMul Cc ε Φ Dd) := by
  have h0 := (warpMul_stripEdge0 (Cc := Cc) (ε := ε) hΦ hD).const_mul (ε : ℂ)
  unfold StripEdge1
  have hfun : stripEdge0 (fun ζ : ℂ => warpMul Cc ε Φ Dd (1 - ζ)) =
      stripEdge0 (fun ζ : ℂ => (ε : ℂ) * warpMul Cc ε Φ Dd ζ) := by
    funext τ
    unfold stripEdge0
    exact warpMul_oneSub hε hD (⟨by simp, by simp⟩ : ((τ : ℂ) * Complex.I) ∈ closedStrip)
  obtain ⟨a, b, d⟩ := h0
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]; exact a
  · rw [hfun]; exact b
  · rw [hfun]; exact d

/-- **The warp summand is admissible** (Step 1 of `fct:s4-proof`, for fixed `(ε, c)`): from `SplittingData Φ̂_c` and `CompData D_{τ₁}`,
`(M1)`-`(M3)` at `α = 1/2` and `W(1 - ζ) = ε W(ζ)`. -/
theorem warpMul_admissible (hε : ε = 1 ∨ ε = -1) (hΦ : SplittingData Φ) (hD : CompData Dd)
    (htend : Tendsto (warpMul Cc ε Φ Dd) (𝓝[closedStrip \ {0}] 0) (𝓝 0)) :
    StripAdmissFullData (1 / 2 : ℝ) (warpMul Cc ε Φ Dd) ∧
      ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → warpMul Cc ε Φ Dd (1 - ζ) = (ε : ℂ) * warpMul Cc ε Φ Dd ζ := by
  have hcont := warpMul_continuousOn hε hΦ hD htend
  refine ⟨?_, fun ζ h0 h1 => warpMul_oneSub hε hD ⟨h0, h1⟩⟩
  exact
    { hol := warpMul_differentiableOn hΦ hD
      cont := hcont
      real := fun ζ h0 h1 => warpMul_conj hΦ hD ⟨h0, h1⟩
      bound := warpMul_bound hΦ hD hcont
      holder1 := warpMul_holder1 hε hΦ hD
      edge0 := warpMul_stripEdge0 hΦ hD
      holder0 := warpMul_holder0 hΦ hD
      edge1 := warpMul_stripEdge1 hε hΦ hD }

end Warp

/-! ### The inputs and the field `warp_admissible` as a theorem -/

/-- **`fct:splitting` (1)-(2) for the splitting function `Φ̂_c`** (`constant_terms_five.tex`, Lemma FCT.6), as consumed by Step 1 of `fct:s4-proof`
(for large `c` and `ε = ±1`; `Φ̂_c` is the abstract datum `FctMainHankelInputs.PhiHat`): `Φ̂_c` is holomorphic on `Re ζ > 0`,
real-symmetric (on `S̄`, the edge values being the continuous extension), continuous on `S̄`, `Φ̂_c = O(ζ³)` at `ζ = 0`, `|Φ̂_c| ≤ M log log (4 + |τ|)`
on `S̄`, and the edge traces `τ ↦ Φ̂_c(iτ)` (`C²` off `0`) and `τ ↦ Φ̂_c(1 - iτ)` have first and second derivatives bounded as in
`(fct:Fminus-edge)`/`(fct:Eminus-edge)` (`≤ M min(1, |τ|²)`, `≤ M min(1, |τ|)` at the left edge, `≤ M` at the right edge).  The constants may depend on `(ε, c)`
(the paper's are uniform in `c`).  `Φ̂_c` carries no `ε`-symmetry of its own: `Φ̂_c(ζ) Φ̂_c(1 - ζ)` is symmetric, and the `ε` in
`W(1 - ζ) = ε W(ζ)` comes from `H_*/G_ε`.  This is the only part of the former field `warp_admissible` that is not proved. -/
def FctSplittingStmt (PhiHat : ℝ → ℝ → ℂ → ℂ) : Prop :=
  ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → SplittingData (PhiHat ε c)

/-- The corner bounds `Φ̂_c = O(ζ³)`, `Φ̂_c(1 - ζ) = O(1)` near `ζ = 0` that make `ctWwarp → 0` at the corner. -/
lemma SplittingData.corner {Φ : ℂ → ℂ} (hΦ : SplittingData Φ) :
    ∃ C : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖ζ‖ ≤ 1 → ‖Φ ζ‖ ≤ C * ‖ζ‖ ^ 3 ∧ ‖Φ (1 - ζ)‖ ≤ C := by
  obtain ⟨M, hM, hll, hcube, -, -⟩ := hΦ.bounds
  refine ⟨5 * M, fun ζ h0 h1 hb => ⟨?_, ?_⟩⟩
  · have := hcube ζ ⟨h0, h1⟩ hb
    have : 0 ≤ M * ‖ζ‖ ^ 3 := by positivity
    nlinarith [hcube ζ ⟨h0, h1⟩ hb]
  · have h1cl : (1 - ζ) ∈ closedStrip := ⟨by simp [h1], by simp [h0]⟩
    have := hll (1 - ζ) h1cl
    have h2 : |(1 - ζ).im| ≤ 1 := by
      simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      exact (Complex.abs_im_le_norm ζ).trans hb
    have h3 := loglog_le (abs_nonneg (1 - ζ).im)
    have h4 : M * Real.log (Real.log (4 + |(1 - ζ).im|)) ≤ M * (4 + |(1 - ζ).im|) := mul_le_mul_of_nonneg_left h3 hM
    nlinarith

/-- `D_{τ₁}` satisfies `CompData` for large `c` (`fct:comp-D`: `differentiableOn_stripCompG`, `continuousOn_stripCompGExt`,
`stripCompGExt_one_sub`, `fct_comp_D_part1`). -/
theorem fctDcomp_compData {K4 : ℝ} (hK4 : 1 ≤ K4) {alpha : ℝ → ℝ → ℝ}
    (hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |alpha ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ))) :
    ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → CompData (fctDcomp K4 alpha ε c) := by
  obtain ⟨B, c₀, h⟩ := fctDcomp_vdata hK4 hα
  refine ⟨c₀, fun ε c hε hc => ?_⟩
  obtain ⟨v, hv, hs, he, hb, hD⟩ := h ε c hε hc
  have hfun : fctDcomp K4 alpha ε c = fun ζ => Complex.exp (stripCompGExt v ζ) := funext hD
  rw [hfun]
  refine ⟨stripCompD_hol hv hs, stripCompD_cont hv hs, fun ζ _ => ?_, fun ζ hζ => ?_, ⟨Real.exp (B 0), fun ζ hζ => ?_⟩,
    stripCompD_edge_env2 hv hs B hb⟩
  · simp only [stripCompGExt_conj he ζ, Complex.exp_conj]
  · simp only [stripCompGExt_one_sub he hζ]
  · rw [Complex.norm_exp]
    have := hb 0 (by norm_num) ζ hζ
    simp only [iteratedDeriv_zero] at this
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans this)

/-- **Step 1 of `fct:s4-proof` for the warp summand** (the former field `warp_admissible` of `FctMainHankelInputs`): for `c ≥ c₀` and `ε = ±1`,
`ctWwarp Φ̂ D_{τ₁}` satisfies `uct:admiss` (M1)-(M3) at `α = 1/2` and `W(1 - ζ) = ε W(ζ)` on `S̄`.  Proved from `fct:comp-D`
(`fct_comp_D_part1`, through `fctDcomp_compData`), the fixed factor `H_*/G_ε` (`ctHG`; `uct:outer-growth`, `uctSeedZ`) and the splitting input
`FctSplittingStmt` (`fct:splitting` (1)-(2)). -/
theorem fctWarp_admissible {K4 : ℝ} (hK4 : 1 ≤ K4) {alpha : ℝ → ℝ → ℝ}
    (hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |alpha ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)))
    {PhiHat : ℝ → ℝ → ℂ → ℂ} (hS : FctSplittingStmt PhiHat) :
    ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      StripAdmissFullData (1 / 2) (ctWwarp PhiHat (fctDcomp K4 alpha) ε c) ∧
        ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 →
          ctWwarp PhiHat (fctDcomp K4 alpha) ε c (1 - ζ) = (ε : ℂ) * ctWwarp PhiHat (fctDcomp K4 alpha) ε c ζ := by
  obtain ⟨cD, hcD⟩ := fctDcomp_compData hK4 hα
  obtain ⟨cS, hcS⟩ := hS
  refine ⟨max cD cS, fun ε c hε hc => ?_⟩
  have hD := hcD ε c hε ((le_max_left _ _).trans hc)
  have hΦ := hcS ε c hε ((le_max_right _ _).trans hc)
  obtain ⟨C, hC⟩ := hΦ.corner
  obtain ⟨BD, hBD⟩ := hD.bd
  have htend : Tendsto (ctWwarp PhiHat (fctDcomp K4 alpha) ε c) (𝓝[closedStrip \ {0}] 0) (𝓝 0) :=
    ctWwarp_tendsto_zero PhiHat (fctDcomp K4 alpha) ε c
      ⟨max C BD, 1, one_pos, fun ζ h0 h1 hb =>
        ⟨(hC ζ h0 h1 hb).1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),
          (hC ζ h0 h1 hb).2.trans (le_max_left _ _), (hBD ζ ⟨h0, h1⟩).trans (le_max_right _ _)⟩⟩
  exact warpMul_admissible hε hΦ hD htend

/-- info: 'FormalResearch.SignUncertainty.fctWarp_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarp_admissible

/-- info: 'FormalResearch.SignUncertainty.fctDcomp_compData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctDcomp_compData

/-- info: 'FormalResearch.SignUncertainty.warpMul_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms warpMul_admissible

end FormalResearch.SignUncertainty
