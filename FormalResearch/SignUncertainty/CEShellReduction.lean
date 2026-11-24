module

public import FormalResearch.SignUncertainty.HeadlineDefs
public import FormalResearch.SignUncertainty.HankelThresholds
public import FormalResearch.SignUncertainty.EuclidRadialProjection

/-!
# The Cohn--Elkies shell reduction at `m = 1` from `hb_thresholds_lower` (M7)

A normalised continuous `L¹` Cohn--Elkies pair `(h, r)` on `ℝ^d` gives the anti-self-dual sign-uncertainty
competitor `g(x) = ĥ(x) - h(-x)` (`g(0) = 0`, `ĝ = -g`, `g ≥ 0` on `‖x‖ ≥ r`, `g ≠ 0` by the compact-support
uncertainty principle `fourier_compact_support_eq_zero`), and its `O(d)`-average is a Hankel-feasible profile at
`T = r²/2` for `c = d/2`, `ε = -1` (`radialProjection`).  With `hb_thresholds_lower`:

* `ce_admissible_signWitness`, `ce_admissible_hankelFeasible`: the competitor and the feasible profile;
* `ce_admissible_radius_lower`: `airyOrderModel d - C ≤ r²/2` for every admissible `(h, r)`, `d ≥ d₀`;
* `shell_reduction_m1_proved`: `∃ C d₀, ∀ d ≥ d₀, airyOrderModel d - C ≤ optimalL1CERadius d ^ 2 / 2`
  (the field `shell_reduction_m1` of `RadiiInputs`);
* `shell_reduction_airy`: `ShellReduction ShellHBData.airy` (no shells, so the shell constraints play no role).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform RealInnerProductSpace

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- `𝓕 (f ∘ neg) = conj (𝓕 f)` for a real integrable `f`. -/
lemma fourier_comp_neg_real {d : ℕ} {f : Euc d → ℝ} (hf : Integrable f) (y : Euc d) :
    𝓕 (fun x : Euc d => (f (-x) : ℂ)) y = star (𝓕 (fun x : Euc d => (f x : ℂ)) y) := by
  have hC : Integrable (fun x : Euc d => (f x : ℂ)) := Complex.ofRealCLM.integrable_comp hf
  have hconj : star (∫ x : Euc d, 𝐞 (-⟪x, y⟫) • (f x : ℂ)) =
      ∫ x : Euc d, star (𝐞 (-⟪x, y⟫) • (f x : ℂ)) :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integral_comp_comm
      ((Real.fourierIntegral_convergent_iff y).mpr hC)).symm
  rw [Real.fourier_eq, Real.fourier_eq, hconj, ← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [neg_neg, inner_neg_left, neg_neg, Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul,
    star_mul, Complex.star_def, Complex.conj_ofReal, ← Circle.coe_inv_eq_conj,
    ← AddChar.map_neg_eq_inv, neg_neg, mul_comm (f x : ℂ)]

/-- A normalised continuous `L¹` Cohn--Elkies pair gives an anti-self-dual sign-uncertainty competitor with
`g(0) = 0` at the same radius. -/
theorem ce_admissible_signWitness {d : ℕ} (hd : 1 ≤ d) {r : ℝ} {h : Euc d → ℝ}
    (hadm : IsContinuousL1CEAdmissible d r h) :
    ∃ g : Euc d → ℝ, IsSignWitness (-1) d r g ∧ g 0 = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  set F : Euc (n + 1) → ℂ := 𝓕 (fun x : Euc (n + 1) => (h x : ℂ)) with hFdef
  have hI : Integrable (fun x : Euc (n + 1) => (h x : ℂ)) := Complex.ofRealCLM.integrable_comp hadm.integrable
  have hC : Continuous (fun x : Euc (n + 1) => (h x : ℂ)) := Complex.continuous_ofReal.comp hadm.continuous
  have hFint : Integrable F := hadm.fourier_integrable
  have hFre : ∀ y, F y = ((F y).re : ℂ) := fun y => Complex.ext rfl (by simpa using (hadm.fourier_nonneg y).1)
  have hFcont : Continuous F := continuous_fourier_of_integrable hI
  have hFF : ∀ y, 𝓕 F y = (h (-y) : ℂ) := by
    intro y
    have := congrFun (hC.fourierInv_fourier_eq hI hFint) (-y)
    rw [Real.fourierInv_eq_fourier_neg, neg_neg] at this
    exact this
  have hneg : ∀ y, 𝓕 (fun x : Euc (n + 1) => (h (-x) : ℂ)) y = F y := by
    intro y
    rw [fourier_comp_neg_real hadm.integrable, ← hFdef]
    calc star (F y) = star ((F y).re : ℂ) := by rw [← hFre y]
      _ = ((F y).re : ℂ) := by simp
      _ = F y := (hFre y).symm
  have hhI : Integrable (fun x : Euc (n + 1) => h (-x)) := hadm.integrable.comp_neg
  have hhIC : Integrable (fun x : Euc (n + 1) => (h (-x) : ℂ)) := Complex.ofRealCLM.integrable_comp hhI
  set g : Euc (n + 1) → ℝ := fun x => (F x).re - h (-x) with hg
  have hgC : (fun x : Euc (n + 1) => (g x : ℂ)) = fun x => F x - (h (-x) : ℂ) := by
    funext x; simp only [hg]; push_cast; rw [← hFre x]
  have hgI : Integrable g := (hFint.re).sub hhI
  refine ⟨g, ⟨hgI, ?_, ?_, ?_⟩, ?_⟩
  · intro y
    rw [hgC]
    have h1 : 𝓕 (fun x => F x - (h (-x) : ℂ)) y = 𝓕 F y - 𝓕 (fun x => (h (-x) : ℂ)) y := by
      rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq, ← integral_sub]
      · congr 1; funext x; rw [smul_sub]
      · exact (Real.fourierIntegral_convergent_iff y).mpr hFint
      · exact (Real.fourierIntegral_convergent_iff y).mpr hhIC
    rw [h1, hFF, hneg]
    have : (g y : ℂ) = F y - (h (-y) : ℂ) := congrFun hgC y
    rw [this]
    push_cast; ring
  · by_contra hall
    push Not at hall
    have hz : ∀ x, g x = 0 := hall
    have hzero : ∀ y : Euc (n + 1), r ≤ ‖y‖ → F y = 0 := by
      intro y hy
      have h1 := hz y
      have h2 := hadm.nonpos_outside (-y) (by rw [norm_neg]; exact hy)
      have h3 := (hadm.fourier_nonneg y).2
      simp only [hg] at h1
      have : (F y).re = 0 := by linarith
      rw [hFre y, this]; simp
    have hsupp : HasCompactSupport F := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc (n + 1)) r) fun x hx => ?_
      rw [mem_closedBall_zero_iff, not_le] at hx
      exact hzero x hx.le
    have hR : ∀ y : Euc (n + 1), r ≤ ‖y‖ → 𝓕 F y = 0 := by
      intro y hy
      rw [hFF]
      have h1 := hz (-y)
      have h2 := hzero (-y) (by rw [norm_neg]; exact hy)
      simp only [hg, neg_neg] at h1
      rw [h2] at h1
      have : h y = 0 := by simpa using h1.symm
      have h4 : h (-y) = 0 := by
        have h5 := hz y
        simp only [hg] at h5
        have := hzero y hy
        rw [this] at h5; simpa using h5.symm
      simp [h4]
    have hF0 := fourier_compact_support_eq_zero (n := n) hFcont hsupp r hR
    have := hadm.fourier_origin_pos
    have h00 : F 0 = 0 := congrFun hF0 0
    rw [hFdef] at h00
    rw [h00] at this
    simp at this
  · intro x hx
    have h1 := (hadm.fourier_nonneg x).2
    have h2 := hadm.nonpos_outside (-x) (by rw [norm_neg]; exact hx)
    simp only [hg]; linarith
  · simp only [hg, neg_zero]
    have := hadm.origin_eq
    linarith

/-- A normalised continuous `L¹` Cohn--Elkies pair of radius `r` gives a Hankel-feasible profile for `c = d/2`,
`ε = -1` at the threshold `r²/2`. -/
theorem ce_admissible_hankelFeasible {d : ℕ} (hd : 2 ≤ d) {r : ℝ} {h : Euc d → ℝ}
    (hadm : IsContinuousL1CEAdmissible d r h) :
    ∃ G : ℝ → ℝ, IsHankelFeasible ((d : ℝ) / 2) (-1) (r ^ 2 / 2) G := by
  obtain ⟨g, hg, hg0⟩ := ce_admissible_signWitness (by omega) hadm
  obtain ⟨G, hG, -⟩ := radialProjection d hd (-1) (Or.inr rfl) r g hg (by simp [hg0])
  exact ⟨G, hG⟩

/-- Every admissible pair has `airyOrderModel d - C ≤ r²/2`, for `d ≥ d₀` (from `hb_thresholds_lower`). -/
theorem ce_admissible_radius_lower :
    ∃ (C : ℝ) (d₀ : ℕ), 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∀ (r : ℝ) (h : Euc d → ℝ),
      IsContinuousL1CEAdmissible d r h → airyOrderModel d - C ≤ r ^ 2 / 2 := by
  obtain ⟨C, c₀, hC⟩ := hb_thresholds_lower
  refine ⟨C, max 2 ⌈2 * c₀⌉₊, le_max_left _ _, fun d hd r h hadm => ?_⟩
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  have hc : c₀ ≤ (d : ℝ) / 2 := by
    have h1 : ⌈2 * c₀⌉₊ ≤ d := (le_max_right _ _).trans hd
    have h2 : 2 * c₀ ≤ (d : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h1)
    linarith
  obtain ⟨G, hG⟩ := ce_admissible_hankelFeasible hd2 hadm
  have := hC ((d : ℝ) / 2) hc (-1) (Or.inr rfl) (r ^ 2 / 2) G hG
  unfold airyOrderModel
  have e : (d : ℝ) / 2 / π ^ 2 = (d : ℝ) / (2 * π ^ 2) := by rw [div_div]
  linarith

/-- **`shell_reduction_m1`** (`thm:ce-shell-reduction` at `m = 1`; proved): for `d ≥ d₀`,
`r_CE(d)²/2 ≥ airyOrderModel d - C`, with `optimalL1CERadius` the infimum over normalised continuous `L¹` pairs.
The `O(d)` averaging of the paper is not needed: `radialProjection` averages the anti-self-dual competitor.
`C` and `d₀` are the non-sharp Lean constants inherited from `hb_thresholds_lower` (`d₀ = max 2 ⌈2c₀⌉`);
the statement covers every `d ≥ d₀`, even or odd. -/
theorem shell_reduction_m1_proved :
    ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d →
      airyOrderModel d - C ≤ optimalL1CERadius d ^ 2 / 2 := by
  obtain ⟨C, d₀, hd₀, hbound⟩ := ce_admissible_radius_lower
  refine ⟨C, d₀, fun d hd => ?_⟩
  have hd2 : 2 ≤ d := hd₀.trans hd
  have hpos := (optimalCERadius_pos_and_bound_ge (by omega : 1 ≤ d)).2.1
  set M := airyOrderModel d - C with hM
  by_cases hM0 : M ≤ 0
  · have : 0 ≤ optimalL1CERadius d ^ 2 / 2 := by positivity
    linarith
  · push Not at hM0
    obtain ⟨⟨r₀, h₀, hsw₀⟩, -⟩ := schwartzCE_nonempty_and_lower_bound (by omega : 1 ≤ d)
    have hge : Real.sqrt (2 * M) ≤ optimalL1CERadius d := by
      refine le_csInf ⟨r₀, h₀, hsw₀.toIsContinuousL1CEAdmissible⟩ fun r ⟨h, hadm⟩ => ?_
      have h1 := hbound d hd r h hadm
      have hr := hadm.r_pos
      apply Real.sqrt_le_iff.2 ⟨hr.le, ?_⟩
      nlinarith
    have h2 : (Real.sqrt (2 * M)) ^ 2 = 2 * M := Real.sq_sqrt (by linarith)
    have h3 : (Real.sqrt (2 * M)) ^ 2 ≤ optimalL1CERadius d ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hge 2
    linarith

/-- **`ShellReduction` for the Airy configuration** (`thm:ce-shell-reduction`, `m = 1`; proved). -/
theorem shell_reduction_airy : ShellReduction ShellHBData.airy := by
  intro R_off _
  obtain ⟨C, d₀, hd₀, hbound⟩ := ce_admissible_radius_lower
  refine ⟨C, d₀, fun d hd r _ R ⟨h, hadm⟩ => ?_⟩
  have h1 := hbound d hd R h hadm.toIsContinuousL1CEAdmissible
  have hA : -(ShellHBData.airy.tm / hankelBeta1) = airyOrderCoeff := by
    unfold airyOrderCoeff
    rw [abs_of_neg (airyZero_neg 1)]
    show -(airyZero 1 / hankelBeta1) = -airyZero 1 / hankelBeta1
    ring
  unfold airyOrderModel at h1
  have e : (d : ℝ) / (2 * π ^ 2) - (ShellHBData.airy.tm / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) =
      (d : ℝ) / (2 * π ^ 2) + airyOrderCoeff * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) := by
    rw [← hA]; ring
  rw [e]
  exact h1

/-- info: 'FormalResearch.SignUncertainty.fourier_comp_neg_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourier_comp_neg_real

/-- info: 'FormalResearch.SignUncertainty.ce_admissible_hankelFeasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_admissible_hankelFeasible

/-- info: 'FormalResearch.SignUncertainty.ce_admissible_radius_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_admissible_radius_lower

/-- info: 'FormalResearch.SignUncertainty.ce_admissible_signWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_admissible_signWitness

/-- info: 'FormalResearch.SignUncertainty.shell_reduction_m1_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shell_reduction_m1_proved

/-- info: 'FormalResearch.SignUncertainty.shell_reduction_airy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shell_reduction_airy

end FormalResearch.SignUncertainty
