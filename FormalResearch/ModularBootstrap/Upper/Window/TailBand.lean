module

public import FormalResearch.ModularBootstrap.Upper.Window.TailGeometry
public import FormalResearch.ModularBootstrap.Upper.Membership.DesignMembership

/-!
# Pointwise comb bounds on the bands of Lemma `T` (`ut:T`, `upper_transfer.tex` §5)

* `refComb_band_bound`: **`K6`(a) + `K4` + `K0`(c) on the intermediate band** (first step of the proof of
  `ut:T`): for `f ≥ 1`, `η₀ ∈ [0, 1/4]`, `r₀ > 0`, a constant `C = e^{C_+}` independent of `N₁` such that for
  every `N₁ ≥ 4f` and large `c'`, every `x ∈ [χ_{N₁+1}, ξ_* + r₀]` has
  `|B_ref^{(f)}(x)| e^{c' L(x)} ≤ C (4√2 cosh(πr₀/2)/(π (x - ξ_*)))^{2 n₁}`.  With `x - ξ_* = λσ` this is
  `C (2 cosh(πr₀/2))^{2n₁} (2√2/(πλ))^{2n₁} σ^{-2n₁}`.
* `refComb_far_bound`: `K6`(a) on `x ≥ ξ_* + r₀`: `|B_ref^{(f)}(x)| e^{c'L(x)} ≤ C(f, r₀)` for large `c'`.
* `designComb_norm_le_exp_ref`: `Lemma P`(b) in multiplicative form: for the compact family
  `|σ_k| ≤ M`, `0 ≤ ε'_k ≤ E λ`, large `c'`, all `x ≥ ξ_* + 4 max(Φ_{N+2}, M) λ`,
  `|B_D^{(f)}(x)| ≤ e^{K λ/(x - ξ_*)} |B_ref^{(f)}(x)|`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Window.Tail

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Holes FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Membership

lemma slitL_eq_besselL {x : ℝ} (hx : 0 ≤ x) : slitL x = Bessel.besselL x := by
  unfold slitL Bessel.besselL
  rw [abs_of_nonneg hx]

/-- `r_{a} ≤ 1` for large `c'` (fixed `a`): `r_a ≤ λ Φ_a → 0`. -/
lemma eventually_siteRadius_le_one (a : ℝ) :
    ∀ᶠ c' in atTop, 1 / 4 ≤ a → siteRadius c' a ≤ 1 := by
  have h := (tendsto_lambdaComb_atTop.const_mul (phiQuantile a))
  rw [mul_zero] at h
  filter_upwards [h.eventually_le_const (zero_lt_one : (0 : ℝ) < 1), eventually_gt_atTop (0 : ℝ)]
    with c' h1 hc' ha
  have := (siteRadius_bounds hc' ha).2
  linarith [mul_comm (phiQuantile a) (lambdaComb c')]

/-- **`K6`(a), `K4`, `K0`(c) on the intermediate band** (`ut:T`): see the module docstring. -/
theorem refComb_band_bound {f : ℕ} (hf : 1 ≤ f) {η₀ r₀ : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ N₁ : ℕ, 4 * f ≤ N₁ → ∀ᶠ c' in atTop, ∀ x : ℝ,
      chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) ≤ x → x ≤ xiStar + r₀ →
        ‖refComb c' f η₀ (x : ℂ)‖ * Real.exp (c' * Bessel.besselL x) ≤
          C * (4 * √2 * cosh (π * r₀ / 2) / (π * (x - xiStar))) ^ (2 * ((f : ℝ) - 1 / 4)) := by
  obtain ⟨Cp, hCp, hev⟩ := band_upper_K6a_mul
  refine ⟨Real.exp Cp, Real.exp_pos _, fun N₁ hN₁ => ?_⟩
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ),
    eventually_siteRadius_le_one (((N₁ + 1 : ℕ) : ℝ))] with c' hmul hc' hr1
  intro x hx hxr
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hf14 : (1 / 4 : ℝ) < f := by linarith
  have hN14s : (1 / 4 : ℝ) < ((N₁ + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((N₁ + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N₁ + 1)
    linarith
  have hN14 := hN14s.le
  have hr1' := hr1 hN14
  have hhalf := siteRadius_f_le_half hc' hf hN₁ hr1'
  have hξN : xiStar < chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) := xiStar_lt_chiQuantile hc' hN14s
  have hξf : xiStar ≤ chiQuantile c' (f : ℝ) := (chiQuantile_spec hc' hf14.le).1
  unfold siteRadius at hhalf
  have hxξ : 0 < x - xiStar := by linarith
  have hfx : chiQuantile c' (f : ℝ) < x := by linarith
  -- the cell of `x`
  have hχ2 : chiQuantile c' ((f + 2 : ℕ) : ℝ) ≤ chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) :=
    (chiQuantile_strictMonoOn hc').monotoneOn
      (Set.mem_Ici.mpr (by have : (1 : ℝ) ≤ ((f + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
                           linarith))
      (Set.mem_Ici.mpr hN14) (by exact_mod_cast (by omega : f + 2 ≤ N₁ + 1))
  obtain ⟨n, hn, hcell⟩ := exists_inCell_of_ge' hc' (k := f + 2) (by omega) (hχ2.trans hx)
  have h1 := hmul f n η₀ x hf hn hη₀0 hη₀1 hcell
  rw [slitL_eq_besselL (by linarith [xiStar_pos])] at h1
  have h2 := (combPf_bounds_K4 hc' hf hfx).2.1
  have hd : (x - xiStar) / 2 ≤ x - chiQuantile c' (f : ℝ) := by linarith
  have hlog := neg_realLogT_le (x := x) (y := chiQuantile c' (f : ℝ)) (d := (x - xiStar) / 2)
    (r₀ := r₀) hξf (by positivity) hd (by linarith)
  have hn1 : 0 ≤ 2 * n1Comb f := by unfold n1Comb; linarith
  have hA : 0 < 4 * √2 * cosh (π * r₀ / 2) / (π * (x - xiStar)) := by
    have := Real.pi_pos
    have : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
    have := Real.cosh_pos (π * r₀ / 2)
    positivity
  have hA' : 2 * √2 * cosh (π * r₀ / 2) / (π * ((x - xiStar) / 2)) =
      4 * √2 * cosh (π * r₀ / 2) / (π * (x - xiStar)) := by
    have := Real.pi_pos
    field_simp; ring
  rw [hA'] at hlog
  refine h1.trans ?_
  rw [Real.rpow_def_of_pos hA, ← Real.exp_add, add_comm]
  apply Real.exp_le_exp.mpr
  unfold n1Comb at h2 hn1
  nlinarith [mul_le_mul_of_nonneg_left hlog hn1]

/-- **`K6`(a) on the far band**: `|B_ref^{(f)}(x)| e^{c'L(x)} ≤ C(f, r₀)` on `x ≥ ξ_* + r₀`. -/
theorem refComb_far_bound {f : ℕ} (hf : 1 ≤ f) {η₀ r₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hr₀ : 0 < r₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' in atTop, ∀ x : ℝ, xiStar + r₀ ≤ x →
      ‖refComb c' f η₀ (x : ℂ)‖ * Real.exp (c' * Bessel.besselL x) ≤ C := by
  obtain ⟨C, hC, h⟩ := band_upper_K6a_r0 hf hη₀0 hη₀1 hr₀
  refine ⟨C, hC, h.mono fun c' hc' x hx => ?_⟩
  have := hc' x hx
  rwa [slitL_eq_besselL (by linarith [xiStar_pos])] at this

/-- **`Lemma P`(b), multiplicative form**: see the module docstring. -/
theorem designComb_norm_le_exp_ref (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) {η₀ : ℝ}
    (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      ∀ x : ℝ, xiStar + 4 * max (phiQuantile ((N : ℝ) + 2)) M * lambdaComb c' ≤ x →
        ‖designComb c' f N η₀ σ ε (x : ℂ)‖ ≤
          Real.exp (K * (lambdaComb c' / (x - xiStar))) * ‖refComb c' f η₀ (x : ℂ)‖ := by
  obtain ⟨K, hK0, hP⟩ := lemma_P_b f N hf hfN M E
  set s : ℝ := max (phiQuantile ((N : ℝ) + 2)) M with hs_def
  have hs : 0 < s := lt_of_lt_of_le (phiQuantile_succ_succ_pos N) (le_max_left _ _)
  have hΦs : phiQuantile ((N : ℝ) + 2) ≤ s := le_max_left _ _
  refine ⟨K, hK0, ?_⟩
  filter_upwards [hP h0 h1, designAdmissible_eventually f N hf hfN M E h0 h1,
    refComb_eq_split f N hfN h0 h1, eventually_gt_atTop (0 : ℝ)]
    with c' hP' hAd hsp hc' σ ε hσ hε x hxR
  have hA := hAd σ ε hσ hε
  have hlam := lambdaComb_pos_of_pos hc'
  have hbim : ∀ r : ℝ, |((r : ℂ)).im| < 7 / 8 := fun r => by simp
  have hXs : 4 * s * lambdaComb c' ≤ x - xiStar := by linarith
  have hX : 0 < x - xiStar := lt_of_lt_of_le (by positivity) hXs
  have hx : 0 ≤ x := by linarith [xiStar_pos]
  have hlog := hP' σ ε hσ hε x hxR
  have hsite : ∀ k : ℕ, 1 ≤ k → k ≤ N → chiQuantile c' (k : ℝ) < x := fun k hk hkN => by
    have hb := (refSite_bounds hc' hk hkN).2
    have : lambdaComb c' * phiQuantile ((N : ℝ) + 2) ≤ lambdaComb c' * s := by gcongr
    nlinarith [mul_pos hs hlam]
  exact norm_designComb_le_exp_mul_ref (σ := σ) (ε := ε) hx
    (hsp (hbim x)) (xiStar_pos.le.trans (refSite_bounds hc' hf hfN).1) (hsite f hf hfN)
    (fun i hi => ⟨xiStar_pos.le.trans (refSite_bounds (k := f + 1 + i) (N := N) hc' (by omega)
        (by omega)).1, hsite _ (by omega) (by omega),
      mul_nonneg h0 (siteGap_nonneg hc' (by omega)),
      by have := (abs_le.mp (hA.ref_width i hi)).2; linarith⟩) hlog

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.refComb_band_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refComb_band_bound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.designComb_norm_le_exp_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designComb_norm_le_exp_ref

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.refComb_far_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refComb_far_bound

end FormalResearch.ModularBootstrap.Upper.Window.Tail
