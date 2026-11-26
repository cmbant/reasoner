module

public import FormalResearch.ModularBootstrap.Upper.Ramped.PUnif

/-!
# `pmix:punif`: uniform Airy profile bounds (Lemma PM.4)

`positive_mixtures.tex`, Lemma PM.4.  The statement does not involve the Cardy weight, so it is the source-free
`lemma_P_unif` / `pUnif_V_ramped` of the W-P6 stack (`Upper/Ramped/PUnif`), packaged here as one theorem under the paper's label.
For the ramped profile (`u_f = a_1 - d`, `u_k = a_k` for `2 ≤ k ≤ N`, `u_k = u_k^W` beyond, heights `0 ≤ η_k ≤ 1/4`) there are
absolute `C, N₀` such that, for `N ≥ N₀` and `d ∈ [0, 1]`, uniformly in `N, d, η`:

* `‖W_D(u; d)‖ ≤ C (1 + ‖u‖)^{-3/2} e(u)` on `ℂ` (`e` is `airyEnv`);
* `1/2 ≤ R_1 ≤ C`;
* `E_0 ≤ C [∑_{2 ≤ k ≤ N} η_k² k^{-4/3} + ∑_{k > N} (η_k² k^{-4/3} + k^{-10/3})]`;
* `∫ Re W_D = -d R_1 + ∑_{n ≥ 2} Π_n(d) ≤ -d R_1 + E_0 ≤ -d/2 + E_0` (the vacuum inequality the proof of `pmix:smooth` uses).

Differences from the paper (all proved unconditionally): the paper's separate bound `|G(u)| ≤ C (1 + |u|)^{-5/2} e(u)` for
`G := W_0 - W_D(·; 1)` is not stated in Lean: it is not used by `pmix:smooth` or `pmix:o1` (only the `-3/2` bound for `W_D` and the
integral identity are), and `lemma_G_bound_unif` records the `-3/2` bound uniformly over the fixed designs.  The inequality
`∫ G ≥ R_1` is the equality `∫ W = -d R_1 + ∑ Π_n(d)` with `Π_n(d) ≥ 0`, rearranged (`profV_identity`).
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Mixtures

open MeasureTheory
open FormalResearch.ModularBootstrap.Upper.Ramped FormalResearch.ModularBootstrap.Upper.Window FormalResearch.Special

/-- **`pmix:punif`** (Lemma PM.4), source-free packaging: absolute constants `C, N₀` such that for all `N ≥ N₀`,
`d ∈ [0, 1]` and admissible heights `0 ≤ η_k ≤ 1/4`, the bounds listed in the module docstring hold uniformly. -/
theorem pmix_punif :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
      ∀ η : ℕ → ℝ, AdmHeights η →
      (∀ u : ℂ, ‖profW (designSiteU N) (rampedWidthU η) d u‖ ≤
        C * (1 + ‖u‖) ^ (-(3 / 2 : ℝ)) * airyEnv u) ∧
      (1 / 2 ≤ profR1 (designSiteU N) (rampedWidthU η) ∧
        profR1 (designSiteU N) (rampedWidthU η) ≤ C) ∧
      profE0 (designSiteU N) (rampedWidthU η) ≤ C *
        (∑ n ∈ Finset.Icc 2 N, η n ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) +
          ∑' m : ℕ, (η (N + 1 + m) ^ 2 * ((N + 1 + m : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) +
            ((N + 1 + m : ℕ) : ℝ) ^ (-(10 / 3 : ℝ)))) ∧
      (∫ x : ℝ, (profW (designSiteU N) (rampedWidthU η) d (x : ℂ)).re) =
        -d * profR1 (designSiteU N) (rampedWidthU η) +
          ∑' n : ℕ, profPi (designSiteU N) (rampedWidthU η) d (n + 2) ∧
      (∫ x : ℝ, (profW (designSiteU N) (rampedWidthU η) d (x : ℂ)).re) ≤
        -d * profR1 (designSiteU N) (rampedWidthU η) + profE0 (designSiteU N) (rampedWidthU η) ∧
      (∫ x : ℝ, (profW (designSiteU N) (rampedWidthU η) d (x : ℂ)).re) ≤
        -d / 2 + profE0 (designSiteU N) (rampedWidthU η) := by
  obtain ⟨C, hC, N0, hN0, hPU⟩ := lemma_P_unif
  obtain ⟨N1, hint⟩ := pUnif_integral_le
  refine ⟨C, hC, max N0 N1, hN0.trans (le_max_left _ _), fun N hN d hd0 hd1 η hη => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hPU N ((le_max_left _ _).trans hN) d hd0 hd1 η hη
  have hV := (pUnif_V_ramped N η hη d hd0 hd1).2.2
  exact ⟨h1, h2, h3, hV.1, hV.2, hint N ((le_max_right _ _).trans hN) d hd0 hd1 η hη⟩

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_punif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_punif

end FormalResearch.ModularBootstrap.Mixtures
