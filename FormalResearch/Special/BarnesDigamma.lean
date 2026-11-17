module

public import FormalResearch.Special.BarnesDigammaReal

/-!
# Gauss' series for the digamma function on the right half-plane

`Complex.digamma z = -γ + ∑_{k ≥ 0} (1/(k+1) - 1/(k+z))` for `0 < Re z` (DLMF 5.7.6, in the form
`ψ(1+z) + γ = ∑_{k≥1} z/(k(k+z))`).  The real-axis case is `BarnesDigammaReal`; here both sides are
holomorphic on `Re z > 0` (the series by the Weierstrass M-test on `{δ < Re z, |z| < R}`) and the
identity theorem on the connected half-plane extends it.

Not formalised: the series on `Re z ≤ 0` (not needed), Gauss' integral representation.
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set Complex

local notation "γ" => Real.eulerMascheroniConstant

/-- The open right half-plane. -/
def rhp : Set ℂ := {z | 0 < z.re}

lemma isOpen_rhp : IsOpen rhp := isOpen_lt continuous_const Complex.continuous_re

lemma isPreconnected_rhp : IsPreconnected rhp :=
  (convex_halfSpace_re_gt 0).isPreconnected

lemma mem_rhp_ne_neg_nat {z : ℂ} (hz : z ∈ rhp) (m : ℕ) : z ≠ -(m : ℂ) := by
  intro h
  have := congrArg Complex.re h
  simp at this
  have h0 : 0 < z.re := hz
  linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]

lemma differentiableOn_Gamma_rhp : DifferentiableOn ℂ Gamma rhp :=
  fun z hz => (differentiableAt_Gamma z (mem_rhp_ne_neg_nat hz)).differentiableWithinAt

lemma differentiableOn_digamma_rhp : DifferentiableOn ℂ digamma rhp := by
  have h1 : DifferentiableOn ℂ (deriv Gamma) rhp := differentiableOn_Gamma_rhp.deriv isOpen_rhp
  intro z hz
  have := (h1 z hz).div (differentiableOn_Gamma_rhp z hz) (Gamma_ne_zero (mem_rhp_ne_neg_nat hz))
  exact this

lemma digamma_ofReal {x : ℝ} (hx : 0 < x) : digamma (x : ℂ) = ((deriv logGammaR x : ℝ) : ℂ) := by
  have hxr : (x : ℂ) ∈ rhp := by simpa [rhp] using hx
  have hdG : HasDerivAt Gamma (deriv Gamma (x : ℂ)) (x : ℂ) :=
    (differentiableAt_Gamma _ (mem_rhp_ne_neg_nat hxr)).hasDerivAt
  have hdR : HasDerivAt Real.Gamma (deriv Real.Gamma x) x :=
    (Real.differentiableAt_Gamma (fun m => ne_of_gt (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]))).hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => Gamma (y : ℂ)) (deriv Gamma (x : ℂ)) x := hdG.comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => ((Real.Gamma y : ℝ) : ℂ)) ((deriv Real.Gamma x : ℝ) : ℂ) x :=
    hdR.ofReal_comp
  have h3 : deriv Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ) := by
    refine h1.unique ?_
    simpa [Complex.Gamma_ofReal] using h2
  have hlog : deriv logGammaR x = deriv Real.Gamma x / Real.Gamma x :=
    deriv.log (Real.differentiableAt_Gamma (fun m => ne_of_gt (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])))
      (Real.Gamma_ne_zero (fun m => ne_of_gt (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])))
  rw [digamma_def, logDeriv_apply, h3, hlog, Complex.Gamma_ofReal]
  push_cast
  rfl

/-- The Gauss series. -/
noncomputable def psiSeries (z : ℂ) : ℂ := ∑' k : ℕ, psiTerm z k

lemma differentiableOn_psiTerm (k : ℕ) {U : Set ℂ} (hU : ∀ z ∈ U, 0 < z.re) :
    DifferentiableOn ℂ (psiTerm · k) U := by
  intro z hz
  have : ((k : ℂ) + z) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
    linarith [hU z hz, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold psiTerm
  fun_prop (disch := assumption)

lemma differentiableOn_psiSeries : DifferentiableOn ℂ psiSeries rhp := by
  intro z0 hz0
  have hz0' : 0 < z0.re := hz0
  set δ : ℝ := min 1 (z0.re / 2) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by linarith)
  set R : ℝ := ‖z0‖ + 1
  set U : Set ℂ := {z | δ < z.re ∧ ‖z‖ < R}
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_norm continuous_const)
  have hz0U : z0 ∈ U := ⟨lt_of_le_of_lt (min_le_right _ _) (by linarith), by simp [R]⟩
  have hUpos : ∀ z ∈ U, 0 < z.re := fun z hz => lt_trans hδpos hz.1
  have hsum : Summable (fun k : ℕ => (R + 1) * (1 / ((k : ℝ) + δ) ^ 2)) := by
    refine Summable.mul_left _ ?_
    have := (Real.summable_one_div_nat_add_rpow (δ) 2).mpr (by norm_num)
    refine this.congr fun k => ?_
    simp [abs_of_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) hδpos)]
  have hd : DifferentiableOn ℂ (fun w => ∑' k : ℕ, psiTerm w k) U := by
    refine differentiableOn_tsum_of_summable_norm hsum (fun k => differentiableOn_psiTerm k hUpos)
      hUo (fun k w hw => ?_)
    have hre : δ < w.re := hw.1
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have h1 : (k : ℝ) + δ ≤ ‖(k : ℂ) + 1‖ := by
      refine le_trans ?_ (Complex.re_le_norm _); simp; linarith
    have h2 : (k : ℝ) + δ ≤ ‖(k : ℂ) + w‖ := by
      refine le_trans ?_ (Complex.re_le_norm _); simp; linarith
    have hkd : (0 : ℝ) < (k : ℝ) + δ := by linarith
    have hne1 : (k : ℂ) + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hne2 : (k : ℂ) + w ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have heq : psiTerm w k = (w - 1) / (((k : ℂ) + 1) * ((k : ℂ) + w)) := by
      unfold psiTerm; field_simp; ring
    rw [heq, norm_div, norm_mul]
    have hw1 : ‖w - 1‖ ≤ R + 1 := by
      calc ‖w - 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ R + 1 := by simp; exact hw.2.le
    calc ‖w - 1‖ / (‖(k : ℂ) + 1‖ * ‖(k : ℂ) + w‖)
        ≤ (R + 1) / (((k : ℝ) + δ) * ((k : ℝ) + δ)) :=
          div_le_div₀ (by positivity) hw1 (by positivity)
            (mul_le_mul h1 h2 hkd.le (by linarith))
      _ = (R + 1) * (1 / ((k : ℝ) + δ) ^ 2) := by field_simp
  exact (hd.differentiableAt (hUo.mem_nhds hz0U)).differentiableWithinAt

lemma psiSeries_ofReal {x : ℝ} (hx : 0 < x) :
    psiSeries (x : ℂ) = ((deriv logGammaR x + γ : ℝ) : ℂ) := by
  have h := (hasSum_psiTerm_real hx).mapL (Complex.ofRealCLM)
  have h2 : HasSum (fun k : ℕ => psiTerm (x : ℂ) k) ((deriv logGammaR x + γ : ℝ) : ℂ) := by
    convert h using 1
    · ext k; simp [psiTerm]
    · simp
  exact h2.tsum_eq

/-- **Gauss' series for the digamma function** on `Re z > 0` (DLMF 5.7.6). -/
theorem digamma_eq_series {z : ℂ} (hz : 0 < z.re) :
    digamma z = -(γ : ℂ) + ∑' k : ℕ, ((1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)) := by
  have hz' : z ∈ rhp := hz
  have hA : AnalyticOnNhd ℂ (fun z => digamma z + γ) rhp :=
    (differentiableOn_digamma_rhp.add_const _).analyticOnNhd isOpen_rhp
  have hB : AnalyticOnNhd ℂ psiSeries rhp := differentiableOn_psiSeries.analyticOnNhd isOpen_rhp
  have h1 : (1 : ℂ) ∈ rhp := by simp [rhp]
  have hfreq : ∃ᶠ w : ℂ in 𝓝[≠] 1, digamma w + γ = psiSeries w := by
    have hev : ∀ᶠ x : ℝ in 𝓝[≠] (1 : ℝ), digamma (x : ℂ) + γ = psiSeries (x : ℂ) := by
      filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds (zero_lt_one' ℝ))] with x hx
      rw [digamma_ofReal hx, psiSeries_ofReal hx]; push_cast; ring
    have htend : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' _ _ (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using hx
    exact htend.frequently hev.frequently
  have := hA.eqOn_of_preconnected_of_frequently_eq hB isPreconnected_rhp h1 hfreq hz'
  simp only at this
  have h3 : digamma z + γ = psiSeries z := this
  rw [show digamma z = psiSeries z - γ by linear_combination h3]
  unfold psiSeries psiTerm
  ring


/-- info: 'FormalResearch.Special.Barnes.digamma_eq_series' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms digamma_eq_series

end FormalResearch.Special.Barnes
