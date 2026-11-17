module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Two generic Liouville-type facts for entire functions

Generic complex analysis (no Airy function here), used for the equality case of the Airy sign-uncertainty theorem
(`FormalResearch.Special.AiryCftSignEqualityMain`).

* `entire_exists_div_sq` (**proved**): let `φ, ψ` be entire, and suppose that at every zero `z` of `ψ` the function `φ`
  vanishes to second order (`φ z = 0 = φ'(z)`) while the zero of `ψ` is simple (`ψ'(z) ≠ 0`).  Then `φ = H · ψ²` for an
  entire function `H`.  Proof: locally `φ = (w - z)² φ₂`, `ψ = (w - z) ψ₁` with `φ₂ = dslope (dslope φ z) z`, `ψ₁ = dslope ψ z`,
  `ψ₁(z) = ψ'(z) ≠ 0`, so `H = φ₂/ψ₁²` near `z`; the global `H` is `w ↦ limUnder (𝓝[≠] w) (φ/ψ²)`, which agrees with
  these local quotients on a neighbourhood of every point (the zeros of `ψ` are isolated).
* `entire_affine_of_circle_bound` (**proved**): an entire `Q` with `‖Q(u)‖ ≤ C (1 + r)` on circles `|u| = r` of arbitrarily large
  radii is affine, `Q(u) = q₀ + q₁ u`.  Proof: `Q₁ = dslope Q 0` is bounded on those circles, hence (maximum modulus) on
  every disc, hence constant (Liouville).

Nothing is assumed beyond the stated hypotheses.
-/

@[expose] public section

open Complex Filter Topology Set Metric
open scoped Real

namespace FormalResearch.EntireDiv

lemma differentiable_dslope_entire {g : ℂ → ℂ} (hg : Differentiable ℂ g) (c : ℂ) :
    Differentiable ℂ (dslope g c) := by
  intro z
  have := (Complex.differentiableOn_dslope (s := univ) (f := g) (c := c) Filter.univ_mem).2
    hg.differentiableOn
  exact (this z (mem_univ z)).differentiableAt Filter.univ_mem

/-- The local statement at one point: a function `G`, differentiable near `z₀`, with `φ = G ψ²` near `z₀`, and `ψ ≠ 0` on a
punctured neighbourhood of `z₀`. -/
lemma entire_div_sq_local {φ ψ : ℂ → ℂ} (hφ : Differentiable ℂ φ) (hψ : Differentiable ℂ ψ)
    (hz : ∀ z, ψ z = 0 → φ z = 0 ∧ deriv φ z = 0 ∧ deriv ψ z ≠ 0) (z₀ : ℂ) :
    ∃ G : ℂ → ℂ, (∀ᶠ w in 𝓝 z₀, DifferentiableAt ℂ G w) ∧ (∀ᶠ w in 𝓝 z₀, φ w = G w * ψ w ^ 2) ∧
      ∀ᶠ w in 𝓝[≠] z₀, ψ w ≠ 0 := by
  by_cases h0 : ψ z₀ = 0
  · obtain ⟨hφ0, hφ1, hψ1⟩ := hz z₀ h0
    set φ₁ := dslope φ z₀ with hφ₁
    set φ₂ := dslope φ₁ z₀ with hφ₂
    set ψ₁ := dslope ψ z₀ with hψ₁
    have dφ₁ : Differentiable ℂ φ₁ := differentiable_dslope_entire hφ z₀
    have dφ₂ : Differentiable ℂ φ₂ := differentiable_dslope_entire dφ₁ z₀
    have dψ₁ : Differentiable ℂ ψ₁ := differentiable_dslope_entire hψ z₀
    have hψ₁z : ψ₁ z₀ ≠ 0 := by
      rw [hψ₁, dslope_same]; exact hψ1
    have hφ₁z : φ₁ z₀ = 0 := by rw [hφ₁, dslope_same]; exact hφ1
    have eφ : ∀ w, φ w = (w - z₀) ^ 2 * φ₂ w := by
      intro w
      have e1 : (w - z₀) • φ₁ w = φ w - φ z₀ := sub_smul_dslope φ z₀ w
      have e2 : (w - z₀) • φ₂ w = φ₁ w - φ₁ z₀ := sub_smul_dslope φ₁ z₀ w
      simp only [smul_eq_mul] at e1 e2
      rw [hφ0] at e1
      rw [hφ₁z] at e2
      have : φ₁ w = (w - z₀) * φ₂ w := by linear_combination -e2
      rw [this] at e1
      linear_combination -e1
    have eψ : ∀ w, ψ w = (w - z₀) * ψ₁ w := by
      intro w
      have e1 : (w - z₀) • ψ₁ w = ψ w - ψ z₀ := sub_smul_dslope ψ z₀ w
      simp only [smul_eq_mul] at e1
      rw [h0] at e1
      linear_combination -e1
    have hnz : ∀ᶠ w in 𝓝 z₀, ψ₁ w ≠ 0 := dψ₁.continuous.continuousAt.eventually_ne hψ₁z
    refine ⟨fun w => φ₂ w / ψ₁ w ^ 2, ?_, ?_, ?_⟩
    · filter_upwards [hnz] with w hw
      exact (dφ₂ w).div ((dψ₁ w).pow 2) (pow_ne_zero 2 hw)
    · filter_upwards [hnz] with w hw
      rw [eφ w, eψ w]
      field_simp
    · filter_upwards [nhdsWithin_le_nhds hnz, self_mem_nhdsWithin] with w hw hw'
      rw [eψ w]
      exact mul_ne_zero (sub_ne_zero.2 hw') hw
  · have hnz : ∀ᶠ w in 𝓝 z₀, ψ w ≠ 0 := hψ.continuous.continuousAt.eventually_ne h0
    refine ⟨fun w => φ w / ψ w ^ 2, ?_, ?_, nhdsWithin_le_nhds hnz⟩
    · filter_upwards [hnz] with w hw
      exact (hφ w).div ((hψ w).pow 2) (pow_ne_zero 2 hw)
    · filter_upwards [hnz] with w hw
      field_simp

/-- **Division by a squared simple-zero function.**  `φ = H ψ²` with `H` entire, provided `φ` vanishes to second order at every
(simple) zero of `ψ`. -/
theorem entire_exists_div_sq {φ ψ : ℂ → ℂ} (hφ : Differentiable ℂ φ) (hψ : Differentiable ℂ ψ)
    (hz : ∀ z, ψ z = 0 → φ z = 0 ∧ deriv φ z = 0 ∧ deriv ψ z ≠ 0) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ z, φ z = H z * ψ z ^ 2 := by
  classical
  set H : ℂ → ℂ := fun w => limUnder (𝓝[≠] w) (fun x => φ x / ψ x ^ 2) with hH
  -- value of `H` at `w`, given a local quotient
  have key : ∀ (G : ℂ → ℂ) (w : ℂ), ContinuousAt G w → (∀ᶠ x in 𝓝 w, φ x = G x * ψ x ^ 2) →
      (∀ᶠ x in 𝓝[≠] w, ψ x ≠ 0) → H w = G w := by
    intro G w hG he hn
    have h1 : Tendsto (fun x => φ x / ψ x ^ 2) (𝓝[≠] w) (𝓝 (G w)) := by
      have : ∀ᶠ x in 𝓝[≠] w, φ x / ψ x ^ 2 = G x := by
        filter_upwards [nhdsWithin_le_nhds he, hn] with x hx hx'
        rw [hx]; field_simp
      exact (hG.tendsto.mono_left nhdsWithin_le_nhds).congr' (this.mono fun x hx => hx.symm)
    exact h1.limUnder_eq
  have hiso : ∀ w, ∀ᶠ x in 𝓝[≠] w, ψ x ≠ 0 := fun w => by
    obtain ⟨_, _, _, h⟩ := entire_div_sq_local hφ hψ hz w
    exact h
  have hloc : ∀ z₀, ∃ G : ℂ → ℂ, (∀ᶠ w in 𝓝 z₀, DifferentiableAt ℂ G w) ∧ (∀ᶠ w in 𝓝 z₀, H w = G w) ∧
      (∀ᶠ w in 𝓝 z₀, φ w = G w * ψ w ^ 2) := by
    intro z₀
    obtain ⟨G, hd, he, -⟩ := entire_div_sq_local hφ hψ hz z₀
    refine ⟨G, hd, ?_, he⟩
    have he' := he.eventually_nhds
    filter_upwards [hd, he'] with w hw hew
    exact key G w hw.continuousAt hew (hiso w)
  refine ⟨H, fun z₀ => ?_, fun z => ?_⟩
  · obtain ⟨G, hd, hHG, -⟩ := hloc z₀
    exact (hd.self_of_nhds).congr_of_eventuallyEq hHG
  · obtain ⟨G, hd, hHG, he⟩ := hloc z
    rw [hHG.self_of_nhds]; exact he.self_of_nhds

/-- info: 'FormalResearch.EntireDiv.entire_exists_div_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.EntireDiv.entire_exists_div_sq

/-- **Entire functions of linear growth on circles are affine.**  If `‖Q u‖ ≤ C (1 + r)` on the circle `|u| = r` for
arbitrarily large `r`, then `Q u = q₀ + q₁ u`. -/
theorem entire_affine_of_circle_bound {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q) {C : ℝ} (hC : 0 ≤ C)
    (hr : ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧ ∀ u : ℂ, ‖u‖ = r → ‖Q u‖ ≤ C * (1 + r)) :
    ∃ q₀ q₁ : ℂ, ∀ u, Q u = q₀ + q₁ * u := by
  set Q₁ := dslope Q 0 with hQ₁
  have dQ₁ : Differentiable ℂ Q₁ := differentiable_dslope_entire hQ 0
  set M : ℝ := 2 * C + ‖Q 0‖ with hM
  -- bound on large circles
  have hcirc : ∀ r : ℝ, 1 ≤ r → (∀ u : ℂ, ‖u‖ = r → ‖Q u‖ ≤ C * (1 + r)) → ∀ u : ℂ, ‖u‖ = r → ‖Q₁ u‖ ≤ M := by
    intro r hr1 hb u hu
    have hu0 : u ≠ 0 := by
      intro h; rw [h, norm_zero] at hu; linarith
    rw [hQ₁, dslope_of_ne _ hu0, slope_def_field, sub_zero, norm_div, hu]
    have hrpos : 0 < r := by linarith
    rw [div_le_iff₀ hrpos]
    have h1 : ‖Q u - Q 0‖ ≤ C * (1 + r) + ‖Q 0‖ := by
      calc ‖Q u - Q 0‖ ≤ ‖Q u‖ + ‖Q 0‖ := norm_sub_le _ _
        _ ≤ _ := by linarith [hb u hu]
    have h2 : C * (1 + r) ≤ 2 * C * r := by nlinarith
    have h3 : ‖Q 0‖ ≤ ‖Q 0‖ * r := by nlinarith [norm_nonneg (Q 0)]
    calc ‖Q u - Q 0‖ ≤ C * (1 + r) + ‖Q 0‖ := h1
      _ ≤ 2 * C * r + ‖Q 0‖ * r := by linarith
      _ = M * r := by rw [hM]; ring
  -- bound on all of `ℂ` by the maximum modulus principle
  have hbdd : ∀ u : ℂ, ‖Q₁ u‖ ≤ M := by
    intro u
    obtain ⟨r, hr1, hb⟩ := hr (max 1 (‖u‖ + 1))
    have hr1' : 1 ≤ r := (le_max_left _ _).trans hr1
    have hur : ‖u‖ < r := by
      have := (le_max_right _ _).trans hr1; linarith
    have := Complex.norm_le_of_forall_mem_frontier_norm_le (f := Q₁) (U := Metric.ball (0 : ℂ) r)
      Metric.isBounded_ball dQ₁.diffContOnCl (C := M) (fun z hz => by
        have hz' : ‖z‖ = r := by
          have hrpos : 0 < r := by linarith
          rw [frontier_ball (0 : ℂ) hrpos.ne'] at hz
          simpa using hz
        exact hcirc r hr1' hb z hz') (z := u) (by
          rw [closure_ball (0 : ℂ) (by linarith : r ≠ 0)]
          simpa using hur.le)
    exact this
  have hconst : ∀ u, Q₁ u = Q₁ 0 :=
    fun u => dQ₁.apply_eq_apply_of_bounded (isBounded_iff_forall_norm_le.2 ⟨M, by
      rintro _ ⟨z, rfl⟩; exact hbdd z⟩) u 0
  refine ⟨Q 0, Q₁ 0, fun u => ?_⟩
  have e1 : (u - 0) • Q₁ u = Q u - Q 0 := sub_smul_dslope Q 0 u
  simp only [smul_eq_mul, sub_zero] at e1
  rw [hconst u] at e1
  linear_combination -e1

/-- info: 'FormalResearch.EntireDiv.entire_affine_of_circle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.EntireDiv.entire_affine_of_circle_bound

end FormalResearch.EntireDiv
