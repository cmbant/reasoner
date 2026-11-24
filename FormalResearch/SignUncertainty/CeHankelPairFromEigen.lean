module

public import FormalResearch.SignUncertainty.CeHbLiftAssembly

/-!
# The Cohn--Elkies Hankel pair from two eigenfunctions (M6, packaging step of `thm:ce-hb-lift`)

A pair `(h, ĥ)` with `ĥ = 𝓗_c h` is the sum and difference of the `σ = ±1` eigencomponents: `h = (f₊ + f₋)/2`, `ĥ = (f₊ - f₋)/2` for
`f_σ ∈ 𝒜_c^σ`.  `ceHankelPair_of_eigenfns` records the algebra: if `f₋(0) = 0 < f₊(0)` (the tuning of `η_c` in `thm:ce-hb-lift`),
`f₊ ≥ f₋` on `[0, ∞)` (`ĥ ≥ 0`) and `f₊ + f₋ ≤ 0` on `[T, ∞)` (`h ≤ 0`), then `G = (f₊ + f₋)/2` has every property required in
`CeHankelPair` for the dimension `d = 2c` except the bound on `T`.  The signs `f₊ ≥ f₋` and `f₊ + f₋ ≤ 0` are the Fourier and physical sign
theorems (pre-edge, window, post-edge; `O.6`) of the paper, not proved here.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

theorem besselHankelTransform_half_sum {c : ℝ} (hc : 1 / 2 < c) {f g : ℝ → ℝ}
    (hf : IntegrableOn (fun s => f s * hankelRho0 c s) (Ioi 0))
    (hg : IntegrableOn (fun s => g s * hankelRho0 c s) (Ioi 0)) (Δ : ℝ) :
    besselHankelTransform c (fun s => (f s + g s) / 2) Δ =
      (besselHankelTransform c f Δ + besselHankelTransform c g Δ) / 2 := by
  unfold besselHankelTransform
  have h1 := integrableOn_mul_hankelKernel hc hf Δ
  have h2 := integrableOn_mul_hankelKernel hc hg Δ
  rw [← integral_add h1 h2, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only
  ring

/-- **The pair `(G, 𝓗 G)` from two eigenfunctions** (see the module docstring). -/
theorem ceHankelPair_of_eigenfns {c T : ℝ} (hc : 1 / 2 < c) {fp fm : ℝ → ℝ} (hP : IsHankelEigenfn c 1 fp)
    (hM : IsHankelEigenfn c (-1) fm) (h0 : fm 0 = 0) (hpos : 0 < fp 0)
    (hnn : ∀ Δ : ℝ, 0 ≤ Δ → fm Δ ≤ fp Δ) (htail : ∀ Δ : ℝ, T ≤ Δ → fp Δ + fm Δ ≤ 0) :
    ContinuousOn (fun s => (fp s + fm s) / 2) (Ici 0) ∧
      IntegrableOn (fun Δ => (fun s => (fp s + fm s) / 2) Δ * hankelRho0 c Δ) (Ioi 0) ∧
      (∀ Δ : ℝ, 0 ≤ Δ → 0 ≤ besselHankelTransform c (fun s => (fp s + fm s) / 2) Δ) ∧
      IntegrableOn (fun Δ => besselHankelTransform c (fun s => (fp s + fm s) / 2) Δ * hankelRho0 c Δ) (Ioi 0) ∧
      0 < (fun s => (fp s + fm s) / 2) 0 ∧
      (fun s => (fp s + fm s) / 2) 0 = besselHankelTransform c (fun s => (fp s + fm s) / 2) 0 ∧
      (∀ Δ : ℝ, T ≤ Δ → (fun s => (fp s + fm s) / 2) Δ ≤ 0) := by
  have hH : ∀ Δ : ℝ, 0 ≤ Δ → besselHankelTransform c (fun s => (fp s + fm s) / 2) Δ = (fp Δ - fm Δ) / 2 := by
    intro Δ hΔ
    rw [besselHankelTransform_half_sum hc hP.int hM.int, hP.eigen Δ hΔ, hM.eigen Δ hΔ]
    ring
  refine ⟨(hP.cont.add hM.cont).div_const 2, ?_, fun Δ hΔ => ?_, ?_, ?_, ?_, fun Δ hΔ => ?_⟩
  · refine ((hP.int.add hM.int).div_const 2).congr (ae_restrict_of_forall_mem measurableSet_Ioi fun s _ => ?_)
    simp only [Pi.add_apply]; ring
  · rw [hH Δ hΔ]; linarith [hnn Δ hΔ]
  · refine ((hP.int.sub hM.int).div_const 2).congr (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
    simp only [Pi.sub_apply]
    rw [hH s (le_of_lt hs)]; ring
  · simp only [h0]; linarith
  · rw [hH 0 le_rfl]; simp only [h0]; ring
  · simp only; linarith [htail Δ hΔ]

/-- info: 'FormalResearch.SignUncertainty.ceHankelPair_of_eigenfns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceHankelPair_of_eigenfns

end FormalResearch.SignUncertainty
