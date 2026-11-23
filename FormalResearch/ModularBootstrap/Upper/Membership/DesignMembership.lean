module

public import FormalResearch.ModularBootstrap.Upper.Membership.SaddleTail
public import FormalResearch.ModularBootstrap.Upper.Membership.RefComb
public import FormalResearch.ModularBootstrap.Upper.Design.CombTransform

/-!
# Lemma `K7` for the finite-modification design combs (`cmb:K7`, `ut:Phi`, `upper_transfer.tex` §4)

Source: `comb_estimates.tex` Lemma `K7` (`cmb:K7`) and `upper_transfer.tex` Lemma `Φ` (`ut:Phi`) and the
membership paragraph of §4: "By `K1(a)`, `Φ`, `P` and `K6(a)` the design comb satisfies the hypotheses
of `K7` at `w = 1`".  For the finite modification `designComb c' f N η₀ σ ε` of the index-`f` reference
comb, in the compact family of `lemma_P_b` (`|σ_k| ≤ M`, `0 ≤ ε'_k ≤ E λ`), uniformly in the family and
for all large `c'`:

* `designComb_innerCombHyp`: hypotheses (i) and (iii) of `K7` (`InnerCombHyp`).  (i) is `K1(a)` and
  `designComb_neg_conj`.  For (iii), `lemma_P_b` bounds `|B_D| ≤ e^{K/(4s)} |B_ref|` on
  `x ≥ ξ_* + 4 s λ` (the finite factors of `B_ref` do not vanish there, `norm_designComb_le_exp_mul_ref`),
  the reference bound `band_upper_K6a_bdd` gives `sup |B_ref| e^{c' L} < ∞`, and on `[0, ξ_* + 4 s λ]`
  `|B_D| ≤ 1` and `e^{c' L}` is bounded.
* `designComb_combPhaseData`: hypothesis (ii) (`CombPhaseData`), `log B_D = c' Φ₀ + Φ₁^{(f)} + Δ_D` on
  `𝒩`, `Re = 0` on `E₊`, `sup_𝒩 |(Φ₁^{(f)} + Δ_D)^{(i)}| ≤ M_φ` for `i = 0, 1, 2`.
* `design_sdvAmplitudeInput`: the named hypothesis `SDVAmplitudeInput` of `SaddleTail.lean` is
  `designProfile_sdvHypotheses` (stated for all `x ≥ ξ_*`, hence for all `x ≥ x_I`).
* `design_k7_membership_vacuum`: for every fixed-weight problem with `w = 1`, for all large `c'`
  (no side condition on the shift: `a = c'/12 ≥ S` holds eventually) and every member of the family,
  `g = ½(h₀ - ĥ₀) ∈ Ā` with `|h₀| + |ĥ₀| ≤ C(c') e^{-c' L - πx}`, the vacuum identity
  `g_vac = ½ h_{0,vac} - π ∫ h₀ V` and `|½ h_{0,vac}| ≤ 2^m` (`|h_{0,vac}| ≤ 8` for `m = 2`).
* `design1_k7_membership_vacuum`: the same for the `f = 1` designs `D(N, η_*, d)`
  (`designSigma1`, `designWidth1`, `η₀ = 1/4`) of `lemma_P_a_fixedN`.

All results are proved unconditionally (no named hypothesis remains: the amplitude input is supplied by
`Design.CombTransform`).  The explicit `N`-dependence of `ut:P`(a) for growing `N` is not covered.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Membership

open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.WeightAxioms
  FormalResearch.ModularBootstrap.Upper.Hankel FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Holes

/-! ### 1. The conclusion of Lemma `K7` -/

/-- The conclusion of Lemma `K7` at weight `1` for the comb `B` (as in `k7_membership_vacuum_of_sdv`):
the decay of `h₀` and `ĥ₀` with a common constant, membership of `g = ½(h₀ - ĥ₀)` in the test class, the
vacuum identity and the bound `|½ h_{0,vac}| ≤ 2^m`. -/
def K7Conclusion (prob : FixedWeightProblem) (c' : ℝ) (B : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ DecayBound c' C (combProfile c' B) ∧
    DecayBound c' C (hankelTransform 1 (combProfile c' B)) ∧
    TestClass prob (c' / 12) (pairOdd (combProfile c' B) (hankelTransform 1 (combProfile c' B))) ∧
    ((prob.gVac (c' / 12) (pairOdd (combProfile c' B) (hankelTransform 1 (combProfile c' B))) : ℝ) :
        ℂ) =
      (1 / 2 : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
          combH0 B (bAlpha c' (c' / 12 - prob.shiftSum s)) -
        (π : ℂ) * ((∫ t in Ioi (0 : ℝ), combProfile c' B t * prob.cardyV (c' / 12) t : ℝ) : ℂ) ∧
    ‖(1 / 2 : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
        combH0 B (bAlpha c' (c' / 12 - prob.shiftSum s))‖ ≤ 2 ^ prob.m

/-- For `m = 2` (`Q = (1-q)²`) the conclusion gives `|h_{0,vac}| ≤ 8`, where
`h_{0,vac} = ∑_s (-1)^{|s|} h₀(b_{a-r_s})`. -/
lemma K7Conclusion.norm_vac_le_eight {prob : FixedWeightProblem} {c' : ℝ} {B : ℂ → ℂ}
    (h : K7Conclusion prob c' B) (hm : prob.m = 2) :
    ‖∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
        combH0 B (bAlpha c' (c' / 12 - prob.shiftSum s))‖ ≤ 8 := by
  obtain ⟨-, -, -, -, -, -, hv⟩ := h
  rw [norm_mul] at hv
  have h4 : (2 : ℝ) ^ prob.m = 4 := by rw [hm]; norm_num
  rw [h4] at hv
  norm_num at hv
  linarith

/-- `h₀ = sech²(πb/2) B_D` is `designProfile`. -/
lemma combH0_designComb (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) :
    combH0 (designComb c' f N η₀ σ ε) = designProfile c' f N η₀ σ ε := rfl

/-! ### 2. Hypothesis (iii): comparison with the reference comb -/

/-- Where the finite factors of `B_ref` do not vanish (`x` to the right of the reference sites, widths in
`[0, 1/2]`), a bound `|log(|B_D|/|B_ref|)| ≤ K` gives `|B_D| ≤ e^K |B_ref|`.  (The logarithm is `0` at a
zero of the denominator, so non-vanishing of `B_ref` is needed: it follows from `|B_D| ≠ 0`.) -/
lemma norm_designComb_le_exp_mul_ref {c' : ℝ} {f N : ℕ} {η₀ x K : ℝ} {σ ε : ℕ → ℝ} (hx0 : 0 ≤ x)
    (hsp : refComb c' f η₀ (x : ℂ) =
      blaschkeT (chiQuantile c' (f : ℝ) : ℂ) (x : ℂ) *
        (∏ i ∈ Finset.range (N - f),
          pairT (chiQuantile c' ((f + 1 + i : ℕ) : ℝ)) (η₀ * siteGap c' (f + 1 + i)) (x : ℂ)) *
        combTail c' N η₀ (x : ℂ))
    (hf0 : 0 ≤ chiQuantile c' (f : ℝ)) (hxf : chiQuantile c' (f : ℝ) < x)
    (hxs : ∀ i < N - f, 0 ≤ chiQuantile c' ((f + 1 + i : ℕ) : ℝ) ∧
      chiQuantile c' ((f + 1 + i : ℕ) : ℝ) < x ∧ 0 ≤ η₀ * siteGap c' (f + 1 + i) ∧
      η₀ * siteGap c' (f + 1 + i) ≤ 1 / 2)
    (hlog : |Real.log (‖designComb c' f N η₀ σ ε (x : ℂ)‖ / ‖refComb c' f η₀ (x : ℂ)‖)| ≤ K) :
    ‖designComb c' f N η₀ σ ε (x : ℂ)‖ ≤ Real.exp K * ‖refComb c' f η₀ (x : ℂ)‖ := by
  by_cases hD : ‖designComb c' f N η₀ σ ε (x : ℂ)‖ = 0
  · rw [hD]; exact mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hDpos : 0 < ‖designComb c' f N η₀ σ ε (x : ℂ)‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hD)
  have htail : 0 < ‖combTail c' N η₀ (x : ℂ)‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) (Ne.symm fun h => hD ?_)
    unfold designComb
    rw [norm_mul, h, mul_zero]
  have hRpos : 0 < ‖refComb c' f η₀ (x : ℂ)‖ := by
    rw [hsp, norm_mul, norm_mul, norm_prod]
    refine mul_pos (mul_pos (norm_blaschkeT_ofReal_pos hx0 hf0 hxf.ne') ?_) htail
    refine Finset.prod_pos fun i hi => ?_
    obtain ⟨h1, h2, h3, h4⟩ := hxs i (Finset.mem_range.mp hi)
    rw [norm_pairT_ofReal]
    exact blaschkePairQ_pos h1 hx0 h2.ne' h3 h4
  have h1 := (abs_le.mp hlog).2
  rw [Real.log_le_iff_le_exp (div_pos hDpos hRpos), div_le_iff₀ hRpos] at h1
  exact h1

lemma lambdaComb_pos_of_pos {c' : ℝ} (hc' : 0 < c') : 0 < lambdaComb c' :=
  Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _

lemma phiQuantile_succ_succ_pos (N : ℕ) : 0 < phiQuantile ((N : ℝ) + 2) := by
  unfold phiQuantile
  apply Real.rpow_pos_of_pos
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

private lemma tanh_strictMono' : StrictMono Real.tanh := by
  refine strictMono_of_deriv_pos fun x => ?_
  have hd : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
    rw [show Real.tanh = fun t => Real.sinh t / Real.cosh t from funext Real.tanh_eq_sinh_div_cosh]
    refine ((Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne').congr_deriv ?_
    field_simp [(Real.cosh_pos x).ne']
    linarith [Real.cosh_sq_sub_sinh_sq x]
  rw [hd.deriv]
  exact one_div_pos.mpr (sq_pos_of_pos (Real.cosh_pos x))

lemma tanh_half_pi_pos : 0 < Real.tanh (π / 2) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)

/-- A real Blaschke factor is bounded below by `tanh(π/2)²` at distance `≥ 1` from its zero. -/
lemma tanh_sq_le_norm_blaschkeT {x y : ℝ} (hy : 0 ≤ y) (hxy : y + 1 ≤ x) :
    Real.tanh (π / 2) ^ 2 ≤ ‖blaschkeT (y : ℂ) (x : ℂ)‖ := by
  rw [norm_blaschkeT_ofReal]
  have hpi := Real.pi_pos
  have h1 : Real.tanh (π / 2) ≤ Real.tanh (π * (x - y) / 2) :=
    tanh_strictMono'.monotone (by nlinarith)
  have h2 : Real.tanh (π / 2) ≤ Real.tanh (π * (x + y) / 2) :=
    tanh_strictMono'.monotone (by nlinarith)
  have hτ := tanh_half_pi_pos
  rw [abs_of_nonneg (mul_nonneg (hτ.le.trans h1) (hτ.le.trans h2))]
  nlinarith

/-- A conjugate-pair modulus is bounded below by `tanh(π/2)⁴` at distance `≥ 1` from its centre. -/
lemma tanh_pow_four_le_blaschkePairQ {χ ε x : ℝ} (hχ : 0 ≤ χ) (hxχ : χ + 1 ≤ x) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) : Real.tanh (π / 2) ^ 4 ≤ blaschkePairQ χ ε x := by
  have h := blaschkePairQ_ge_sq χ ε x hε0 hε
  refine le_trans ?_ h
  have h1 := tanh_sq_le_norm_blaschkeT hχ hxχ
  rw [norm_blaschkeT_ofReal] at h1
  have hτ := tanh_half_pi_pos
  have hpos : 0 ≤ Real.tanh (π * (x - χ) / 2) * Real.tanh (π * (x + χ) / 2) := by
    have hpi := Real.pi_pos
    have e1 : Real.tanh (π / 2) ≤ Real.tanh (π * (x - χ) / 2) :=
      tanh_strictMono'.monotone (by nlinarith)
    have e2 : Real.tanh (π / 2) ≤ Real.tanh (π * (x + χ) / 2) :=
      tanh_strictMono'.monotone (by nlinarith)
    exact mul_nonneg (hτ.le.trans e1) (hτ.le.trans e2)
  rw [abs_of_nonneg hpos] at h1
  calc Real.tanh (π / 2) ^ 4 = (Real.tanh (π / 2) ^ 2) ^ 2 := by ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) h1 2

/-- At a point `x ≥ 0` at distance `≥ 1` to the right of all zeros of the finite factors of both
`B_D^{(f)}` and `B_ref^{(f)}`, `B_D` is bounded by a finite multiple of `B_ref`: the constant
`tanh(π/2)^{-(2 + 4(N-f))}` depends on the cut `N` only, through the number of changed factors. -/
lemma tanh_pow_mul_norm_designComb_le {c' : ℝ} {f N : ℕ} {η₀ x : ℝ} {σ ε : ℕ → ℝ}
    (hA : DesignAdmissible c' f N η₀ σ ε) (hη₀0 : 0 ≤ η₀) (hgap : ∀ k, 1 ≤ k → 0 ≤ siteGap c' k)
    (hη₀1 : ∀ i < N - f, η₀ * siteGap c' (f + 1 + i) ≤ 1 / 2)
    (hsp : refComb c' f η₀ (x : ℂ) =
      blaschkeT (chiQuantile c' (f : ℝ) : ℂ) (x : ℂ) *
        (∏ i ∈ Finset.range (N - f),
          pairT (chiQuantile c' ((f + 1 + i : ℕ) : ℝ)) (η₀ * siteGap c' (f + 1 + i)) (x : ℂ)) *
        combTail c' N η₀ (x : ℂ))
    (hxf : chiQuantile c' (f : ℝ) + 1 ≤ x)
    (hxs : ∀ i < N - f, chiQuantile c' ((f + 1 + i : ℕ) : ℝ) + 1 ≤ x) :
    Real.tanh (π / 2) ^ (2 + 4 * (N - f)) * ‖designComb c' f N η₀ σ ε (x : ℂ)‖ ≤
      ‖refComb c' f η₀ (x : ℂ)‖ := by
  have hτ := tanh_half_pi_pos
  have hnorm_ref : ‖refComb c' f η₀ (x : ℂ)‖ =
      ((‖blaschkeT (chiQuantile c' (f : ℝ) : ℂ) (x : ℂ)‖) *
        ∏ i ∈ Finset.range (N - f), blaschkePairQ (chiQuantile c' ((f + 1 + i : ℕ) : ℝ))
          (η₀ * siteGap c' (f + 1 + i)) x) * ‖combTail c' N η₀ (x : ℂ)‖ := by
    rw [hsp, norm_mul, norm_mul, norm_prod]
    rfl
  have hnorm_D : ‖designComb c' f N η₀ σ ε (x : ℂ)‖ =
      ((‖blaschkeT (designSite c' σ f : ℂ) (x : ℂ)‖) *
        ∏ i ∈ Finset.range (N - f), blaschkePairQ (designSite c' σ (f + 1 + i))
          (ε (f + 1 + i)) x) * ‖combTail c' N η₀ (x : ℂ)‖ := by
    unfold designComb
    rw [norm_mul, norm_mul, norm_prod]
    rfl
  have hbim : |((x : ℂ)).im| ≤ 1 / 2 := by simp
  have hD1 : ‖blaschkeT (designSite c' σ f : ℂ) (x : ℂ)‖ *
      ∏ i ∈ Finset.range (N - f), blaschkePairQ (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) x
        ≤ 1 := by
    have h1 := norm_blaschkeT_real_le_one (designSite c' σ f) hbim
    have h2 : ∏ i ∈ Finset.range (N - f), blaschkePairQ (designSite c' σ (f + 1 + i))
        (ε (f + 1 + i)) x ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i hi =>
        norm_pair_blaschkeT_le_one _ _
          ((hA.width i (Finset.mem_range.mp hi)).trans (by norm_num)) hbim
    exact (mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one).trans
      (by norm_num)
  have hR0 : Real.tanh (π / 2) ^ 2 * (Real.tanh (π / 2) ^ 4) ^ (N - f) ≤
      ‖blaschkeT (chiQuantile c' (f : ℝ) : ℂ) (x : ℂ)‖ *
        ∏ i ∈ Finset.range (N - f), blaschkePairQ (chiQuantile c' ((f + 1 + i : ℕ) : ℝ))
          (η₀ * siteGap c' (f + 1 + i)) x := by
    refine mul_le_mul (tanh_sq_le_norm_blaschkeT hA.ref_first hxf) ?_ (by positivity) (norm_nonneg _)
    calc (Real.tanh (π / 2) ^ 4) ^ (N - f) = ∏ _i ∈ Finset.range (N - f), Real.tanh (π / 2) ^ 4 := by
          simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i hi => by
          have hi' := Finset.mem_range.mp hi
          exact tanh_pow_four_le_blaschkePairQ (hA.ref_site i hi') (hxs i hi')
            (mul_nonneg hη₀0 (hgap _ (by omega))) (hη₀1 i hi')
  have hpow : Real.tanh (π / 2) ^ (2 + 4 * (N - f)) =
      Real.tanh (π / 2) ^ 2 * (Real.tanh (π / 2) ^ 4) ^ (N - f) := by
    rw [pow_add, ← pow_mul]
  rw [hnorm_ref, hnorm_D, hpow]
  have ht := norm_nonneg (combTail c' N η₀ (x : ℂ))
  nlinarith [mul_le_mul_of_nonneg_right hR0 ht, mul_le_mul_of_nonneg_right hD1 ht,
    mul_nonneg (by positivity : (0 : ℝ) ≤ Real.tanh (π / 2) ^ 2 * (Real.tanh (π / 2) ^ 4) ^ (N - f))
      ht, hD1]

/-- **Hypotheses (i) and (iii) of Lemma `K7` for the design combs, for any admissible finite
modification** (`cmb:K7`, via `K1(a)`, `K6(a)`): for `c'` large, with a threshold independent of the cut `N` and
of the data, `B_D = designComb` is an `InnerCombHyp`.  The finiteness `sup_{x ≥ 0} |B_D(x)| e^{c' L(x)} < ∞`
(constant depending on `c'`, `N`, the data) comes from `|B_D| ≤ tanh(π/2)^{-(2+4(N-f))} |B_ref|` to the right of
the finitely many moved zeros; no quantitative estimate of `|B_D / B_ref|` is needed. -/
theorem designComb_innerCombHyp_of_admissible (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (h0 : 0 ≤ η₀)
    (h1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ), f ≤ N → DesignAdmissible c' f N η₀ σ ε →
      InnerCombHyp c' (designComb c' f N η₀ σ ε) := by
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  filter_upwards [refComb_eq_split_unif f h0 h1, combTail_K1a_unif h0 h1,
    band_upper_K6a_bdd hf h0 h1, eventually_gt_atTop (0 : ℝ), h_ev]
    with c' hsp hTd ⟨Mref, hMref0, hMref⟩ hc' ⟨hgap_k, _, _, hgap_1⟩ N σ ε hfN hA
  obtain ⟨hT1, hT2, hT3, hT4⟩ := hTd N
  obtain ⟨hK1, hK2, hK3⟩ := designComb_K1a hA hT1 hT2 hT3
  have hbim : ∀ r : ℝ, |((r : ℂ)).im| < 7 / 8 := fun r => by simp
  refine ⟨fun r => ?_, fun r => ?_, hK3, fun {b} hb => hK1 hb, fun v => ?_, ?_⟩
  · simpa using designComb_neg c' f N η₀ σ ε (r : ℂ)
  · have h := designComb_neg_conj c' f N η₀ σ ε (r : ℂ) (hT4 (hbim r))
    rw [Complex.conj_ofReal, designComb_neg] at h
    exact Complex.conj_eq_iff_im.mp h.symm
  · exact hK2 (by simp [abs_of_pos])
  · have hgap_nn : ∀ k, 1 ≤ k → 0 ≤ siteGap c' k := fun k hk => siteGap_nonneg hc' hk
    have hη₀h : ∀ i < N - f, η₀ * siteGap c' (f + 1 + i) ≤ 1 / 2 := fun i hi => by
      have := (abs_le.mp (hA.ref_width i hi)).2
      linarith
    set τ : ℝ := Real.tanh (π / 2) with hτdef
    have hτ : 0 < τ := tanh_half_pi_pos
    set P : ℝ := τ ^ (2 + 4 * (N - f)) with hP
    have hPpos : 0 < P := by positivity
    set Sx : ℝ := ∑ i ∈ Finset.range (N - f),
      (designSite c' σ (f + 1 + i) + chiQuantile c' ((f + 1 + i : ℕ) : ℝ)) with hSx
    have hSx0 : 0 ≤ Sx := Finset.sum_nonneg fun i hi => by
      have hi' := Finset.mem_range.mp hi
      exact add_nonneg (hA.site i hi') (hA.ref_site i hi')
    set X₀ : ℝ := 1 + designSite c' σ f + chiQuantile c' (f : ℝ) + Sx with hX₀
    have hX₀1 : 1 ≤ X₀ := by linarith [hA.first, hA.ref_first]
    have hsx : ∀ i < N - f, chiQuantile c' ((f + 1 + i : ℕ) : ℝ) + 1 ≤ X₀ := fun i hi => by
      have hle : designSite c' σ (f + 1 + i) + chiQuantile c' ((f + 1 + i : ℕ) : ℝ) ≤ Sx :=
        Finset.single_le_sum (f := fun i => designSite c' σ (f + 1 + i) +
          chiQuantile c' ((f + 1 + i : ℕ) : ℝ))
          (fun i hi => add_nonneg (hA.site i (Finset.mem_range.mp hi))
            (hA.ref_site i (Finset.mem_range.mp hi))) (Finset.mem_range.mpr hi)
      linarith [hA.site i hi, hA.first, hA.ref_first]
    refine ⟨max (Mref / P) (Real.exp (c' * (2 * π * X₀ / 3))), fun x hx => ?_⟩
    have hexp_pos := Real.exp_pos (c' * (2 * π * x / 3))
    by_cases hxR : X₀ ≤ x
    · have hnorm := tanh_pow_mul_norm_designComb_le (σ := σ) (ε := ε) hA h0 hgap_nn hη₀h
        (hsp N hfN (hbim x)) (by linarith [hA.first, hSx0])
        (fun i hi => (hsx i hi).trans hxR)
      have hM := hMref x hx
      unfold slitL at hM
      rw [abs_of_nonneg hx] at hM
      refine le_max_of_le_left ?_
      rw [le_div_iff₀ hPpos]
      calc ‖designComb c' f N η₀ σ ε (x : ℂ)‖ * Real.exp (c' * (2 * π * x / 3)) * P
          = (P * ‖designComb c' f N η₀ σ ε (x : ℂ)‖) * Real.exp (c' * (2 * π * x / 3)) := by ring
        _ ≤ ‖refComb c' f η₀ (x : ℂ)‖ * Real.exp (c' * (2 * π * x / 3)) :=
            mul_le_mul_of_nonneg_right hnorm hexp_pos.le
        _ ≤ Mref := hM
    · have hxR' : x ≤ X₀ := (not_le.mp hxR).le
      have hD1 : ‖designComb c' f N η₀ σ ε (x : ℂ)‖ ≤ 1 := hK1 (by simp)
      refine le_max_of_le_right ?_
      calc ‖designComb c' f N η₀ σ ε (x : ℂ)‖ * Real.exp (c' * (2 * π * x / 3))
          ≤ 1 * Real.exp (c' * (2 * π * X₀ / 3)) :=
            mul_le_mul hD1 (Real.exp_le_exp.mpr (by
              have := Real.pi_pos
              nlinarith [mul_nonneg hc'.le (mul_nonneg this.le (sub_nonneg.mpr hxR'))]))
              hexp_pos.le zero_le_one
        _ = Real.exp (c' * (2 * π * X₀ / 3)) := one_mul _

/-- **Hypotheses (i) and (iii) of Lemma `K7` for the design combs** (`cmb:K7`, via `K1(a)`, `P`, `K6(a)`):
for `c'` large and every member of the compact family of `lemma_P_b`, `B_D = designComb` is an
`InnerCombHyp`. -/
theorem designComb_innerCombHyp (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) {η₀ : ℝ}
    (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      InnerCombHyp c' (designComb c' f N η₀ σ ε) := by
  filter_upwards [designComb_innerCombHyp_of_admissible f hf h0 h1,
    designAdmissible_eventually f N hf hfN M E h0 h1] with c' h hAd σ ε hσ hε
  exact h N σ ε hfN (hAd σ ε hσ hε)

/-! ### 3. Hypothesis (ii): the phase data -/

/-- **Hypothesis (ii) of Lemma `K7` for an abstract finite modification** (`ut:Phi`, `cmb:K3`): there is
`A ≥ 0` (depending on `f` only) such that for `c'` large (threshold independent of the cut `N`), every
admissible finite modification with `DesignPhiDecomp c' f N η₀ σ ε B` has `CombPhaseData c' (A + B)`:
`B_D = exp (c' Φ₀ + Φ₁)` on `𝒩` with `Φ₁ = Φ₁^{(f)} + Δ_D = designPhi1` holomorphic, `Re Φ₁ = 0` on `E₊` and
`‖Φ₁^{(i)}‖ ≤ A + B` on `𝒩` for `i = 0, 1, 2`. -/
theorem designComb_combPhaseData_of_decomp (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (h0 : 0 ≤ η₀)
    (h1 : η₀ ≤ 1 / 4) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ) (B : ℝ),
      DesignAdmissible c' f N η₀ σ ε → DesignPhiDecomp c' f N η₀ σ ε B →
      CombPhaseData c' (A + B) (designComb c' f N η₀ σ ε) (designPhi1 c' f N η₀ σ ε) := by
  obtain ⟨C₁, hC₁, hK3⟩ := edgePhase_bounds
  obtain ⟨Cg, -, h_ev⟩ := siteGap_eventually_le
  have hn1 : 0 ≤ n1Comb f := by
    unfold n1Comb
    have : (1 : ℝ) ≤ f := by exact_mod_cast hf
    linarith
  refine ⟨C₁ * n1Comb f, by positivity, ?_⟩
  filter_upwards [hK3, h_ev, eventually_gt_atTop (0 : ℝ)]
    with c' hK ⟨hgap_k, hgap_1_bd, hcd1_bd, hgap_1⟩ hc' N σ ε B hA hDec
  have hphi := differentiableOn_phi1Comb hc' f hf h0 h1 hgap_1 hgap_k
  have hdelta := differentiableOn_designDelta hA
  have hΦ1 : DifferentiableOn ℂ (designPhi1 c' f N η₀ σ ε) combNMid := fun b hb =>
    (hphi b hb).add ((hdelta.mono combNMid_subset_combNOpen) b hb)
  refine ⟨?_, fun b hb => (exp_designPhi1_eq hDec (show b ∈ combN from hb)).symm, fun v => ?_,
    fun i hi b hb => ?_⟩
  · exact (hΦ1.analyticOnNhd isOpen_combNMid).mono (fun b hb => combN_subset_combNMid hb)
  · exact re_designPhi1_edge hDec (by simp)
  · have hb' : b ∈ combN := hb
    have hbm := combN_subset_combNMid hb'
    have hcd1 : ContDiffAt ℂ 2 (phi1Comb c' f η₀) b :=
      ((hphi.analyticOnNhd isOpen_combNMid) b hbm).contDiffAt
    have hcd2 : ContDiffAt ℂ 2 (designDelta c' f N η₀ σ ε) b :=
      ((hdelta.analyticOnNhd isOpen_combNOpen) b (combNMid_subset_combNOpen hbm)).contDiffAt
    have hsum : iteratedDeriv i (designPhi1 c' f N η₀ σ ε) b =
        iteratedDeriv i (phi1Comb c' f η₀) b + iteratedDeriv i (designDelta c' f N η₀ σ ε) b :=
      iteratedDeriv_fun_add (hcd1.of_le (by exact_mod_cast hi)) (hcd2.of_le (by exact_mod_cast hi))
    rw [hsum]
    refine (norm_add_le _ _).trans ?_
    have e1 := (hK f hf h0 h1 i hi hb').2.1
    have e2 := hDec.2.2.2 i hi b hb'
    linarith

/-- **Hypothesis (ii) of Lemma `K7` for the design combs** (`ut:Phi`, `cmb:K3`): there is `M_φ ≥ 0` such
that for `c'` large and every member of the family, `B_D = exp (c' Φ₀ + Φ₁)` on `𝒩` with
`Φ₁ = Φ₁^{(f)} + Δ_D = designPhi1` holomorphic, `Re Φ₁ = 0` on `E₊` and `‖Φ₁^{(i)}‖ ≤ M_φ` on `𝒩` for
`i = 0, 1, 2` (`designPhi1_bounds` only exports `i = 1, 2`). -/
theorem designComb_combPhaseData (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) (hE : 0 ≤ E)
    {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1 / 4) :
    ∃ Mφ : ℝ, 0 ≤ Mφ ∧ ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      CombPhaseData c' Mφ (designComb c' f N η₀ σ ε) (designPhi1 c' f N η₀ σ ε) := by
  obtain ⟨A, hA0, hAev⟩ := designComb_combPhaseData_of_decomp f hf h0 h1
  obtain ⟨CΦ, hCΦ, hΦ⟩ := lemma_Phi_b f N hf hfN M E hE h0 h1
  refine ⟨A + CΦ, by positivity, ?_⟩
  filter_upwards [hAev, hΦ, designAdmissible_eventually f N hf hfN M E h0 h1,
    tendsto_lambdaComb_atTop.eventually_le_const (zero_lt_one : (0 : ℝ) < 1)]
    with c' hP hD hAd hlam1 σ ε hσ hε
  exact hP N σ ε CΦ (hAd σ ε hσ hε) ((hD σ ε hσ hε).mono (by nlinarith))

/-! ### 4. Hypothesis `SDVAmplitudeInput` -/

/-- The named amplitude input `SDVAmplitudeInput` of `saddleTailBound_of_sdv` for an abstract finite
modification with `DesignPhiDecomp c' f N η₀ σ ε B` (`δ = 1/8`, constants `𝒜₀ + A + B` and `𝒜₀' + A + B`,
`A = A(f)`): this is `designProfile_sdvHypotheses_of_decomp`, stated there for all `x ≥ ξ_*` and used here
on `x ≥ x_I = ξ_* + c'^{-3/5} ≥ ξ_*`; the threshold is independent of the cut `N`. -/
theorem design_sdvAmplitudeInput_of_decomp (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (h0 : 0 ≤ η₀)
    (h1 : η₀ ≤ 1 / 4) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ) (B : ℝ),
      DesignAdmissible c' f N η₀ σ ε → DesignPhiDecomp c' f N η₀ σ ε B →
      SDVAmplitudeInput c' (designPhi1 c' f N η₀ σ ε) (1 / 8) (ampM0 + (A + B)) (ampM0' + (A + B)) := by
  obtain ⟨A, hA0, h⟩ := designProfile_sdvHypotheses_of_decomp f hf h0 h1
  refine ⟨A, hA0, ?_⟩
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with c' hc hpos N σ ε B hA hDec x hx
  refine hc N σ ε B hA hDec x (le_trans ?_ hx)
  unfold xI
  have := Real.rpow_pos_of_pos hpos (-(3 / 5 : ℝ))
  linarith

/-- The named amplitude input `SDVAmplitudeInput` of `saddleTailBound_of_sdv` holds for the design combs
(`δ = 1/8`, constants `M₁, M₂` uniform in `c'` and the family): this is `designProfile_sdvHypotheses`,
stated there for all `x ≥ ξ_*` and used here on `x ≥ x_I = ξ_* + c'^{-3/5} ≥ ξ_*`. -/
theorem design_sdvAmplitudeInput (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) (hE : 0 ≤ E)
    {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1 / 4) :
    ∃ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ,
      (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      SDVAmplitudeInput c' (designPhi1 c' f N η₀ σ ε) (1 / 8) M₁ M₂ := by
  obtain ⟨M₁, M₂, hM₁, hM₂, h⟩ := designProfile_sdvHypotheses f N hf hfN M E hE h0 h1
  refine ⟨M₁, M₂, hM₁, hM₂, ?_⟩
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with c' hc hpos σ ε hσ hε x hx
  refine hc σ ε hσ hε x (le_trans ?_ hx)
  unfold xI
  have := Real.rpow_pos_of_pos hpos (-(3 / 5 : ℝ))
  linarith

/-! ### 5. Lemma `K7` for the design combs -/

/-- **Lemma `K7` for an abstract finite modification, uniform in the cut `N`** (`cmb:K7` at `w = 1`;
`ut:Phi`).  Fix `f ≥ 1`, `η₀ ∈ [0, 1/4]`, a fixed-weight problem with `w = 1` and `B ≥ 0`.  There is `c₀` such
that for every `c' ≥ c₀` (threshold independent of `N`), every cut `N ≥ f` and every admissible finite
modification `designComb c' f N η₀ σ ε` with `DesignPhiDecomp c' f N η₀ σ ε B` (the derivative bound `B` is
independent of `c'` and `N`): `h₀ = sech²(πb/2) B_D` and `ĥ₀` decay like `C e^{-c' L(x) - πx}` (`C` depends on
`c'` and the data), `g = ½(h₀ - ĥ₀)` is in the test class (membership in `Ā` at `w = 1`, `a = c'/12`), the
vacuum identity `g_vac = ½ h_{0,vac} - π ∫ h₀ V` holds and `|½ h_{0,vac}| ≤ 2^m` (`|h_{0,vac}| ≤ 8` for
`Q = (1-q)²`).  Hypotheses (i), (iii): `designComb_innerCombHyp_of_admissible`; (ii):
`designComb_combPhaseData_of_decomp`; `SD_V`: `design_sdvAmplitudeInput_of_decomp`. -/
theorem design_k7_of_decomp {prob : FixedWeightProblem} (hw : prob.w = 1) (f : ℕ) (hf : 1 ≤ f)
    {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1 / 4) {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ), f ≤ N → DesignAdmissible c' f N η₀ σ ε →
      DesignPhiDecomp c' f N η₀ σ ε B → K7Conclusion prob c' (designComb c' f N η₀ σ ε) := by
  obtain ⟨A, hA0, hAmp⟩ := design_sdvAmplitudeInput_of_decomp f hf h0 h1
  have hc1 := cosC_pos
  have hM₁ : 0 ≤ ampM0 + (A + B) := by unfold ampM0; positivity
  have hM₂ : 0 ≤ ampM0' + (A + B) := by unfold ampM0'; positivity
  obtain ⟨c₀, hc₀, hK7⟩ := k7_membership_vacuum_of_sdv (prob := prob) hw hM₁ hM₂
  obtain ⟨A', -, hPh⟩ := designComb_combPhaseData_of_decomp f hf h0 h1
  filter_upwards [hAmp, hPh, designComb_innerCombHyp_of_admissible f hf h0 h1,
    eventually_ge_atTop c₀, eventually_ge_atTop (12 * prob.totalShift)]
    with c' ha hp hi hc hS N σ ε hfN hA hDec
  exact hK7 hc (by linarith) (hi N σ ε hfN hA) (hp N σ ε B hA hDec) (ha N σ ε B hA hDec)

/-- **Lemma `K7` for the finite-modification design combs** (`cmb:K7` at `w = 1`; `ut:Phi`, `ut:P`).
Fix `f ≥ 1`, `N ≥ f`, `M, E ≥ 0`, `η₀ ∈ [0, 1/4]` and a fixed-weight problem with `w = 1`.  For all large
`c'` and every `designComb c' f N η₀ σ ε` with `|σ_k| ≤ M` and `0 ≤ ε'_k ≤ E λ` (uniformly in the family):
`h₀ = sech²(πb/2) B_D` and `ĥ₀` decay like `C(c') e^{-c' L(x) - πx}`, `g = ½(h₀ - ĥ₀)` is in the test class
(membership in `Ā` at `w = 1`, `a = c'/12`), the vacuum identity `g_vac = ½ h_{0,vac} - π ∫ h₀ V` holds and
`|½ h_{0,vac}| ≤ 2^m` (so `|h_{0,vac}| ≤ 8` for `Q = (1-q)²`).  Hypotheses (i), (iii): `K1(a)`, `P`, `K6(a)`
(`designComb_innerCombHyp`); (ii): `Φ` (`designComb_combPhaseData`); `SD_V`: `design_sdvAmplitudeInput`. -/
theorem design_k7_membership_vacuum {prob : FixedWeightProblem} (hw : prob.w = 1) (f N : ℕ)
    (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) (hE : 0 ≤ E) {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      K7Conclusion prob c' (designComb c' f N η₀ σ ε) := by
  obtain ⟨CΦ, hCΦ, hΦ⟩ := lemma_Phi_b f N hf hfN M E hE h0 h1
  filter_upwards [design_k7_of_decomp hw f hf h0 h1 hCΦ, hΦ,
    designAdmissible_eventually f N hf hfN M E h0 h1,
    tendsto_lambdaComb_atTop.eventually_le_const (zero_lt_one : (0 : ℝ) < 1)]
    with c' hK hD hAd hlam1 σ ε hσ hε
  exact hK N σ ε hfN (hAd σ ε hσ hε) ((hD σ ε hσ hε).mono (by nlinarith))

/-- Non-vacuity of the family: the zero modification (`σ = 0`, `ε = 0`) belongs to it for `M, E ≥ 0`, so
`design_k7_membership_vacuum` has instances for every `c' > 0`. -/
theorem design_family_nonempty (f N : ℕ) {M E : ℝ} (hM : 0 ≤ M) (hE : 0 ≤ E) {c' : ℝ} (hc' : 0 < c') :
    ∃ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) ∧
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') :=
  ⟨fun _ => 0, fun _ => 0, fun k _ _ => by simpa using hM, fun k _ _ =>
    ⟨le_rfl, mul_nonneg hE (lambdaComb_pos_of_pos hc').le⟩⟩

/-- **Lemma `K7` for the designs `D(N, η_*, d)`** (`f = 1`, `η₀ = 1/4`, `σ = designSigma1 d`,
`ε = designWidth1 c' η_*` of `lemma_P_a_fixedN`), with `M` a bound for the finitely many offsets
`σ_1, …, σ_N`: for all large `c'` the conclusion of Lemma `K7` holds. -/
theorem design1_k7_membership_vacuum {prob : FixedWeightProblem} (hw : prob.w = 1) (N : ℕ)
    (hN : 1 ≤ N) {etaStar : ℝ} (hη0 : 0 ≤ etaStar) (hη1 : etaStar ≤ 1 / 4) (d M : ℝ)
    (hM : ∀ k, 1 ≤ k → k ≤ N → |designSigma1 d k| ≤ M) :
    ∀ᶠ c' in atTop,
      K7Conclusion prob c' (designComb c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' etaStar)) := by
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  filter_upwards [design_k7_membership_vacuum hw 1 N le_rfl hN M Cg hCg.le
    (by norm_num : (0 : ℝ) ≤ 1 / 4) le_rfl, h_ev, eventually_gt_atTop (0 : ℝ)]
    with c' hc' ⟨hgap_k, hgap_1_bd, hcd1_bd, _⟩ hpos
  refine hc' (designSigma1 d) (designWidth1 c' etaStar) (fun k hk hkN => hM k hk hkN)
    (fun k hk hkN => ⟨mul_nonneg hη0 (siteGap_nonneg hpos (by omega)), ?_⟩)
  have hgk := (hgap_k k (by omega)).trans (hgap_1_bd.trans hcd1_bd)
  unfold designWidth1
  calc etaStar * siteGap c' k ≤ 1 * (Cg * lambdaComb c') :=
        mul_le_mul (hη1.trans (by norm_num)) hgk (siteGap_nonneg hpos (by omega)) (by norm_num)
    _ = Cg * lambdaComb c' := one_mul _

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.designComb_innerCombHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designComb_innerCombHyp

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.designComb_combPhaseData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designComb_combPhaseData

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.design_sdvAmplitudeInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms design_sdvAmplitudeInput

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.design_k7_membership_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms design_k7_membership_vacuum

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.design1_k7_membership_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms design1_k7_membership_vacuum

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.K7Conclusion.norm_vac_le_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms K7Conclusion.norm_vac_le_eight

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.design_family_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms design_family_nonempty

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.designComb_innerCombHyp_of_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designComb_innerCombHyp_of_admissible

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.designComb_combPhaseData_of_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designComb_combPhaseData_of_decomp

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.design_sdvAmplitudeInput_of_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms design_sdvAmplitudeInput_of_decomp

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.design_k7_of_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms design_k7_of_decomp

end FormalResearch.ModularBootstrap.Upper.Membership
