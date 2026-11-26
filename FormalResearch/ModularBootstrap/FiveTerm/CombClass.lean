module

public import FormalResearch.ModularBootstrap.FiveTerm.DefectIdentity

/-!
# The admissible class `H_adm(Ω)` and the outer-function datum (FIVE-0; `cts:s4`, `ctu:jets`)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, the class `H_adm(Ω)` before Theorem C4
(`cts:main`), and Lemma C3 (`cts:involution`) / Lemma ctu.2 (`ctu:jets`) for the outer function.

* `HAdm F c₁`: `F` holomorphic on `Ω`, real-symmetric, continuous on `closure Ω ∖ {i, -i, 1}`,
  `F = 1 + c₁ z + O(|z|²)` at `0`, `|F| = O(|1-z|^{-1/2})` near `1`, `|F| = O(|1+z²|^{a})` near `±i` with
  `a > 1/2`.
* `OuterDatum W K g₁ G`: what `cts:involution` / `ctu:jets` give for the outer function `G = G_outer`
  of the slit weight `W` and edge kernel `K`: holomorphic, zero-free, real-symmetric, `G = 1 + g₁ z + O(z²)`
  at `0`, `|G| ≍ |1-z|^{1/2}` near `1`, `|G| ≳ 1` and `|G| = O(|1+z²|^{-5/4})` near `±i` (a weakening of the
  paper's `|G| ≍ |1+z²|^{-1}(1+|log|1+z²||)^{w-1/2}`, in which every log power is absorbed), the boundary
  modulus `|G(iy)| = W(y)` and the coupling `G(iy) K(y) = G(e^{-iψ}) e^{iψ} 2y²/(1+y²)`
  (`cts:Gmod`, `cts:coupling`).

`OuterDatum` is the interface to the construction of `G_outer` (not in this file): it records exactly the
properties of `G_outer` that the minimisation of `𝒥` uses, with `g₁ = G_outer'(0)` free.
This file proves only elementary lemmas on these classes (compactness packaging).  All proved unconditionally.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- The three singular boundary points of `Ω` for the comb functional. -/
def singPts : Set ℂ := {Complex.I, -Complex.I, 1}

/-- The admissible class `H_adm(Ω)` of slit-strip envelopes (`cts:s4`), with `c₁ = F'(0)`. -/
structure HAdm (F : ℂ → ℂ) (c1 : ℝ) : Prop where
  diff : DifferentiableOn ℂ F halfDisc
  cont : ContinuousOn F (closure halfDisc \ singPts)
  conj : ∀ z ∈ halfDisc, F (starRingEnd ℂ z) = starRingEnd ℂ (F z)
  jet : ∃ C r : ℝ, 0 < r ∧ ∀ z ∈ closure halfDisc, ‖z‖ < r → ‖F z - 1 - c1 * z‖ ≤ C * ‖z‖ ^ 2
  near_one : ∃ C r : ℝ, 0 < r ∧ ∀ z ∈ closure halfDisc, z ≠ 1 → ‖z - 1‖ < r →
    ‖F z‖ * ‖z - 1‖ ^ (1 / 2 : ℝ) ≤ C
  near_I : ∃ C r a : ℝ, 0 < r ∧ 1 / 2 < a ∧ ∀ z ∈ closure halfDisc, z ≠ Complex.I → z ≠ -Complex.I →
    (‖z - Complex.I‖ < r ∨ ‖z + Complex.I‖ < r) → ‖F z‖ ≤ C * ‖1 + z ^ 2‖ ^ a

/-- The properties of the outer function `G_outer` of weight `W` and kernel `K` used by `cts:main`. -/
structure OuterDatum (W : ℝ → ℝ) (K : ℝ → ℂ) (g1 : ℝ) (G : ℂ → ℂ) : Prop where
  diff : DifferentiableOn ℂ G halfDisc
  cont : ContinuousOn G (closure halfDisc \ singPts)
  conj : ∀ z ∈ halfDisc, G (starRingEnd ℂ z) = starRingEnd ℂ (G z)
  ne_zero : ∀ z ∈ closure halfDisc \ singPts, G z ≠ 0
  jet : ∃ C r : ℝ, 0 < r ∧ ∀ z ∈ closure halfDisc, ‖z‖ < r → ‖G z - 1 - g1 * z‖ ≤ C * ‖z‖ ^ 2
  near_one : ∃ C c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ z ∈ closure halfDisc, z ≠ 1 → ‖z - 1‖ < r →
    c * ‖z - 1‖ ^ (1 / 2 : ℝ) ≤ ‖G z‖ ∧ ‖G z‖ ≤ C * ‖z - 1‖ ^ (1 / 2 : ℝ)
  near_I : ∃ C c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ z ∈ closure halfDisc, z ≠ Complex.I → z ≠ -Complex.I →
    (‖z - Complex.I‖ < r ∨ ‖z + Complex.I‖ < r) →
    c ≤ ‖G z‖ ∧ ‖G z‖ ≤ C * ‖1 + z ^ 2‖ ^ (-(5 / 4 : ℝ))
  modulus : ∀ y ∈ Ioo (0 : ℝ) 1, ‖G (Complex.I * (y : ℂ))‖ = W y
  coupling : ∀ y ∈ Ioo (0 : ℝ) 1, G (Complex.I * (y : ℂ)) * K y =
    G (starRingEnd ℂ (wPt y)) * wPt y * ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ)

lemma mem_singPts_iff {z : ℂ} : z ∈ singPts ↔ z = Complex.I ∨ z = -Complex.I ∨ z = 1 := Iff.rfl

lemma not_mem_singPts_of_halfDisc {z : ℂ} (hz : z ∈ halfDisc) : z ∉ singPts := by
  rw [mem_singPts_iff]
  have := halfDisc_ne_special hz
  tauto

lemma isCompact_closure_halfDisc : IsCompact (closure halfDisc) := by
  refine (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_closure ?_
  refine closure_minimal ?_ (isClosed_closedBall)
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  exact hz.1.le

/-- A function continuous on `closure Ω ∖ {i,-i,1}` which is bounded above near the three points is
bounded above on `closure Ω ∖ {i,-i,1}`. -/
lemma bounded_of_local {f : ℂ → ℝ} (hf : ContinuousOn f (closure halfDisc \ singPts)) {r : ℝ}
    (hr : 0 < r) {M : ℝ}
    (hloc : ∀ z ∈ closure halfDisc \ singPts,
      (dist z Complex.I < r ∨ dist z (-Complex.I) < r ∨ dist z 1 < r) → f z ≤ M) :
    ∃ M' : ℝ, ∀ z ∈ closure halfDisc \ singPts, f z ≤ M' := by
  set T : Set ℂ := closure halfDisc ∩ {z | r ≤ dist z Complex.I} ∩ {z | r ≤ dist z (-Complex.I)} ∩
    {z | r ≤ dist z 1} with hT
  have hTc : IsCompact T := by
    refine isCompact_closure_halfDisc.of_isClosed_subset ?_ (fun z hz => hz.1.1.1)
    refine (((isClosed_closure).inter ?_).inter ?_).inter ?_
    · exact isClosed_le continuous_const (continuous_id.dist continuous_const)
    · exact isClosed_le continuous_const (continuous_id.dist continuous_const)
    · exact isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hTsub : T ⊆ closure halfDisc \ singPts := by
    intro z hz
    refine ⟨hz.1.1.1, ?_⟩
    rw [mem_singPts_iff]
    rintro (h | h | h)
    · have : r ≤ dist z Complex.I := hz.1.1.2
      rw [h, dist_self] at this; linarith
    · have : r ≤ dist z (-Complex.I) := hz.1.2
      rw [h, dist_self] at this; linarith
    · have : r ≤ dist z 1 := hz.2
      rw [h, dist_self] at this; linarith
  obtain ⟨M₂, hM₂⟩ := hTc.exists_bound_of_continuousOn (hf.mono hTsub)
  refine ⟨max M M₂, fun z hz => ?_⟩
  by_cases hnear : dist z Complex.I < r ∨ dist z (-Complex.I) < r ∨ dist z 1 < r
  · exact le_trans (hloc z hz hnear) (le_max_left _ _)
  · push Not at hnear
    obtain ⟨h1, h2, h3⟩ := hnear
    have hzT : z ∈ T := ⟨⟨⟨hz.1, h1⟩, h2⟩, h3⟩
    exact le_trans (le_trans (le_abs_self _) (by simpa using hM₂ z hzT)) (le_max_right _ _)

end FormalResearch.ModularBootstrap.FiveTerm
