module

public import FormalResearch.ModularBootstrap.Upper.Holes.HoleLimit
public import FormalResearch.ModularBootstrap.Upper.Holes.HoleComparison

/-!
# The floor of a finite modification of the reference comb (`rem:thmU`, Steps (3)-(4))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (3), the displayed bound
`h_0^D/Lev ≥ μ_4 [1 - C_4(1/n + ℓ_n)] e^{-2 e_L - S} ∏_{k ∈ H} ρ_k`.

* `designComb_floor`: for `x ∈ [χ_n, χ_{n+1})` and a finite modification `B_D = designComb c' f N η₀ σ ε`,
  `μ_j (1 - C(1/n + ℓ_n)) e^{-2𝓔_left + Σ_mod} ≤ (sech²(πx/2) ‖B_D(x)‖) / Lev^{(f)}(x)`
  with `Σ_mod = modLogRatio ≥ -S + Σ_{k∈H} log ρ_k` (`Upper.Holes.modLogRatio_ge`).  Here
  `μ_j = muHole j η₀`, the constants `N_j, C` are those of `hole_floor_general` (they do not depend on the
  modification), and `Lev^{(f)} = levComb c' f` is the level of the reference comb.
* `designComb_floor_pos`: the same in the form used by Region II, with `e^{-S} ∏ρ` explicit.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Holes

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design

/-- `sech²(πx/2) · r / Lev^{(f)}(x) = ¼ r e^{c' L(x)} e^{-(c' P^{(f)}(x) + J_end^{(f)}(x))}`. -/
lemma sech_mul_div_levComb (c' : ℝ) (f : ℕ) (x r : ℝ) :
    (1 / Real.cosh (π * x / 2) ^ 2 * r) / levComb c' f x =
      (1 / 4 : ℝ) * (r * Real.exp (c' * slitL x) *
        Real.exp (-(c' * combPf c' f x + jEndComb c' x f))) := by
  unfold levComb
  have hch_ne : Real.cosh (π * x / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hexp_mul : Real.exp (-c' * slitL x + c' * combPf c' f x + jEndComb c' x f) =
      Real.exp (-(c' * slitL x)) * Real.exp (c' * combPf c' f x + jEndComb c' x f) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp_mul, Real.exp_neg, Real.exp_neg]
  field_simp [hch_ne, (Real.exp_pos _).ne']

/-- **Floor of a finite modification** (`rem:thmU` Step (3), "Comparison"): for large `c'`, every
`n ≥ max(N_j, f + j)` and every `x ∈ [χ_n, χ_{n+1})`, every finite modification `B_D` of the
`η₀`-reference comb satisfies
`μ_j (1 - C(1/n + ℓ_n)) e^{-2𝓔_left + Σ_mod} ≤ sech²(πx/2) ‖B_D(x)‖ / Lev^{(f)}(x)`,
`Σ_mod = modLogRatio ≥ -S + Σ_{k∈H} log ρ_k`. -/
theorem designComb_floor {j : ℕ} {η₀ : ℝ} (hj : 1 ≤ j) (hη₀0 : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ (N_j : ℕ) (C : ℝ), 1 ≤ N_j ∧ 0 < C ∧
      ∀ᶠ c' in atTop, ∀ (f N n : ℕ) (x : ℝ) (σ ε : ℕ → ℝ),
        1 ≤ f → f ≤ N → max N_j (f + j) ≤ n → inCell c' n x →
        (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ 1 / 2) →
        (∀ k, f ≤ k → k ≤ N → 0 ≤ designSite c' σ k) →
        designSite c' σ f ≠ x →
        (∀ k, f < k → k ≤ N → k ∉ holeSet n j → designSite c' σ k ≠ x) →
        (∀ k, f < k → k ≤ N → k ∈ holeSet n j →
          0 < blaschkePairQ (designSite c' σ k) (ε k) x) →
        muHole j η₀ * (1 - C * (1 / (n : ℝ) + siteGap c' n)) *
            Real.exp (-2 * eLeftComb c' f n j x + modLogRatio c' η₀ x σ ε f N n j) ≤
          (1 / Real.cosh (π * x / 2) ^ 2 * ‖designComb c' f N η₀ σ ε (x : ℂ)‖) /
            levComb c' f x := by
  obtain ⟨N_j, C, hNj, hC_pos, h_ev⟩ := hole_floor_general hj hη₀0 hη₀1
  obtain ⟨_, _, hgap_ev⟩ := siteGap_eventually_le
  refine ⟨N_j, C, hNj, hC_pos, ?_⟩
  filter_upwards [h_ev, hgap_ev, eventually_gt_atTop (0 : ℝ)] with c' h_gen hgap_c hc'
  have hgap1 : siteGap c' 1 ≤ 1 / 2 := hgap_c.2.2.2
  intro f N n x σ ε hf hfN hn_max hx hε hsite hf_ne hout hhole
  have hfnj : f + j ≤ n := (le_max_right _ _).trans hn_max
  have hlow := designComb_lower_hole hc' hη₀0 hη₀1 hgap1 hf hfN hj hfnj hx σ ε hε hsite hf_ne hout
    hhole
  rw [sech_mul_div_levComb]
  refine h_gen f n x hf hn_max hx _ (modLogRatio c' η₀ x σ ε f N n j) (norm_nonneg _) ?_
  have h1 : Real.exp (holeH c' η₀ n j x - 2 * eLeftComb c' f n j x +
        modLogRatio c' η₀ x σ ε f N n j) =
      Real.exp (holeH c' η₀ n j x + jEndComb c' x f - 2 * eLeftComb c' f n j x +
        modLogRatio c' η₀ x σ ε f N n j) * Real.exp (-(jEndComb c' x f)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : ‖designComb c' f N η₀ σ ε (x : ℂ)‖ * Real.exp (c' * slitL x) *
        Real.exp (-(c' * combPf c' f x + jEndComb c' x f)) =
      (‖designComb c' f N η₀ σ ε (x : ℂ)‖ * Real.exp (c' * slitL x - c' * combPf c' f x)) *
        Real.exp (-(jEndComb c' x f)) := by
    rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_right hlow (Real.exp_pos _).le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.designComb_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.designComb_floor
