module

public import FormalResearch.ModularBootstrap.Upper.Assembly.DesignWindow
public import FormalResearch.ModularBootstrap.Upper.Assembly.ProfileWindow

/-!
# Property `sr:P` for the displaced and far-first-site designs: `DesignPropertyP S.μS displacedClassX`

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` (Property `sr:P`, (P1)-(P4); its proof: the designs
are finite modifications `B_D` of the reference comb with threshold `R(𝔇) = 4 max{Φ_{N+2}, σ_f, max σ_k}`,
`σ_k = |u_k|/κ`, the sites `u_k = a_k + e_k` displaced), `upper_transfer.tex` (`ut:P`, `ut:Phi`, `ut:II`, `ut:R`,
`ut:I`, `ut:W`, `ut:ID`, `ut:T`, `ut:III`, `ut:Vac`).

The comb chain of `Assembly.DesignWindow` (membership `sig1_k7_membership_vacuum`, positivity
`proposition_I_sig_t`, window limit `sig_psi_uniform`, vacuum `sig_psi_limsup`) is stated for every `f = 1`
finite modification `designComb c 1 N (1/4) σs (designWidth1 c η)` with arbitrary offsets `σs`: the offsets
enter only through the bound `|σs k| ≤ M` on `1 ≤ k ≤ N`.  Nothing in the chain restricts the first site
(`σ_1` arbitrary: `d ∈ ℝ`) or the position of the sites `2..N` relative to it, because the pairs
`T_{χ+iε} T_{χ-iε}` are positive on the real axis wherever they sit, so the only sign change of `B_D` is the
simple zero at `χ'_1`, and Regions I (Lemma `R`, `lemma_R_lower`) and II only see `x ≥ χ'_1 + Cλ c^{-1/2}`.

* `dispSigma d e`: the offsets of the design with first site `a_1 - d` and sites `u_k = a_k + e_k`.
* `sigWindowW_dispSite`, `profWin_W_eq_sig`: the Airy window of `dispSigma d e` is the profile window
  `profWin (dispSite N e) (designWidthU N η)`.
* **`displacedClassX`**: the class `𝒟x` of the displaced designs with every first-site shift `d ∈ ℝ`, finitely
  many displaced sites `u_k = a_k + e_k` (`2 ≤ k ≤ N`, `e_k` arbitrary: no band or separation restriction is
  needed), `N ≥ 1`, `0 < η_* ≤ 1/4`.  `displacedClass_subset` : `displacedClass ⊆ displacedClassX`; the
  far-first-site windows of `Assembly.FarFirstSite` lie in it.
* **`displacedPropertyP_virasoro`**: `DesignPropertyP S.μS displacedClassX` for every Virasoro crossing
  sequence `S`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Ramped
  FormalResearch.ModularBootstrap.Upper.Positivity

/-- The offsets `σ_k` of the design with first site `a_1 - d` and sites `u_k = a_k + e_k` (`k ≥ 2`):
`σ_1 = (|a_1| + d)/κ`, `σ_k = |a_k|/κ - e_k/κ`, so that `-κ σ_k = u_k`. -/
noncomputable def dispSigma (d : ℝ) (e : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 1 then (|airyZero 1| + d) / kappaAiry else sNodeAiry k - e k / kappaAiry

lemma dispSigma_one (d : ℝ) (e : ℕ → ℝ) :
    -(kappaAiry * dispSigma d e 1) = airyZero 1 - d := by
  have hκ := kappaAiry_pos
  unfold dispSigma
  simp only [↓reduceIte]
  rw [abs_of_neg (airyZero_neg 1)]
  field_simp
  ring

lemma dispSigma_of_two_le {d : ℝ} (e : ℕ → ℝ) {k : ℕ} (hk : 2 ≤ k) :
    -(kappaAiry * dispSigma d e k) = airyZero k + e k := by
  have hκ := kappaAiry_pos
  unfold dispSigma sNodeAiry
  simp only [show k ≠ 1 by omega, ↓reduceIte]
  rw [abs_of_neg (airyZero_neg k)]
  field_simp
  ring

/-- The Airy window of the offsets `dispSigma d e` is the profile window of the displaced sites. -/
lemma sigWindowW_dispSite (N : ℕ) (η : ℝ) (d : ℝ) (e : ℕ → ℝ)
    (he : ∀ k, (k < 2 ∨ N < k) → e k = 0) (u : ℂ) :
    sigWindowW N η (dispSigma d e) u =
      profW (dispSite N e) (designWidthU N η) d u := by
  have hκ := kappaAiry_pos
  have hκ_ne : kappaAiry ≠ 0 := hκ.ne'
  unfold sigWindowW profW
  have huF : -kappaAiry * (sigMod N η (dispSigma d e)).sigmaFLim = airyZero 1 - d := by
    rw [← dispSigma_one d e]; show -kappaAiry * dispSigma d e 1 = _; ring
  rw [huF]
  refine airyWindowProd_congr (fun k hk => ?_) (fun k hk => ?_) u
  · unfold ModifiedCombData.allSigmaLim sigMod dispSite designSiteU
    by_cases hkN : k ≤ N
    · simp only [hkN, ↓reduceIte]
      have := dispSigma_of_two_le (d := d) e (k := k) (by omega)
      show -kappaAiry * dispSigma d e k = airyZero k + e k
      linarith
    · simp only [hkN, ↓reduceIte]
      rw [he k (Or.inr (by omega)), add_zero]
      rfl
  · unfold designWidthU ModifiedCombData.allEpsLim sigMod gapWKB uWKB phiWKB
    by_cases hkN : k ≤ N
    · simp only [hkN, ↓reduceIte]
      ring
    · simp only [hkN, ↓reduceIte]
      ring

/-- The class `𝒟x` of the displaced designs, all first-site shifts `d ∈ ℝ`: `D(N, η_*, d)` with finitely many
displaced sites `u_k = a_k + e_k` (`2 ≤ k ≤ N`, `e_k = 0` elsewhere), `N ≥ 1`, `0 < η_* ≤ 1/4`.  Unlike
`displacedClass`, there is no restriction `|d| < d₀` and no band condition `u_k < 0`. -/
def displacedClassX : Set Window :=
  {D | ∃ (N : ℕ) (η : ℝ) (e : ℕ → ℝ) (d : ℝ) (hη : 0 < η)
      (hH : AiryProdTailHypothesis 1 (dispSite N e) (designWidthU N η)),
      1 ≤ N ∧ η ≤ 1 / 4 ∧ (∀ k, (k < 2 ∨ N < k) → e k = 0) ∧
      D = profWin (dispSite N e) (designWidthU N η) hH
        (fun _ hk => designWidthU_ne_zero N hη hk) d}

lemma displacedClass_subset : displacedClass ⊆ displacedClassX := by
  rintro D ⟨N, η, e, d, hη, hH, hN, hη1, he, -, -, rfl⟩
  exact ⟨N, η, e, d, hη, hH, hN, hη1, he, rfl⟩

lemma profWin_mem_displacedClassX {N : ℕ} {η : ℝ} (hη : 0 < η) {e : ℕ → ℝ}
    (hH : AiryProdTailHypothesis 1 (dispSite N e) (designWidthU N η)) {d : ℝ} (hN : 1 ≤ N)
    (hη1 : η ≤ 1 / 4) (he : ∀ k, (k < 2 ∨ N < k) → e k = 0) :
    profWin (dispSite N e) (designWidthU N η) hH
      (fun _ hk => designWidthU_ne_zero N hη hk) d ∈ displacedClassX :=
  ⟨N, η, e, d, hη, hH, hN, hη1, he, rfl⟩

/-- **Property `sr:P` for the displaced and far-first-site designs**, every weight-one problem: every window
of `displacedClassX` carries a design test for the spectral measures `μ_S` of every crossing sequence `S` of
`prob` (`prob.w = 1`). -/
theorem displacedPropertyP_prob (prob : FixedWeightProblem) (hw : prob.w = 1) (S : CrossingSequence prob) :
    DesignPropertyP S.μS displacedClassX := by
  refine designPropertyP_of_comb S fun D hD => ?_
  obtain ⟨N, η, e, d, hη, hH, hN, hη1, he, rfl⟩ := hD
  refine ⟨(sigEventual prob hw N hN hη hη1 (dispSigma d e) _ ?_ ?_).toComb S⟩
  · funext u
    rw [profWin_W]
    show (profW (dispSite N e) (designWidthU N η) d (u : ℂ)).re = (sigWindowW N η (dispSigma d e) (u : ℂ)).re
    rw [sigWindowW_dispSite N η d e he]
  · rw [profWin_uF, dispSigma_one]

/-- **Property `sr:P` for the displaced and far-first-site designs**: every window of `displacedClassX`
carries a design test for the spectral measures `μ_S` of every Virasoro crossing sequence `S`. -/
theorem displacedPropertyP_virasoro (S : CrossingSequence virasoroProblem) :
    DesignPropertyP S.μS displacedClassX :=
  displacedPropertyP_prob virasoroProblem rfl S

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.displacedPropertyP_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms displacedPropertyP_prob

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.displacedPropertyP_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms displacedPropertyP_virasoro

end FormalResearch.ModularBootstrap.Upper.Assembly
