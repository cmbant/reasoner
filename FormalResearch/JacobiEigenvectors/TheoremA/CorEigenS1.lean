module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssembly
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssemblyBulk
public import FormalResearch.JacobiEigenvectors.TheoremA.ActionDerivativeDt

/-!
# `CorEigenS1` from the phase windows (paper: `thmA.tex`, proof of `cor:eigen` (a))

Proved, with no placeholder proofs and no added axiom (pins at the end):

* `thmAi_of_windows_spec`: `thmAi_of_windows` together with the identification `S_l = Scoef (Sigma)` of the glued coefficients on every window.
* `corEigenS1_of_trunc_windows`: the same for `S` of `G` itself from windows of the truncation `truncSM G 1` (the windows that the assembly produces), through `thmAi_of_trunc` and `eigDensity_of_trunc`; the chart-level premises are discharged in `Assembly/ThmAi.lean`
  (`layer4_windows`: bulk by `BulkPhaseInputs.Sigma_one/Sigma_zero`, soft by `CorEigenZero.lean`) and `CorEigen.lean`.
* `corEigenS1_of_windows`: if the windows have `Sigma_1(X, 0) = 0` and `Sigma_0(X, t) = S_0^{(t)}(X)` for small `t` on the open band, then every `S` with `SmoothExt`, the
  rule and the action formula (`M = 1`) has `S_1(mu, X) = d_t S_0^{(t)}(X)|_{t=0} = int_{u_-}^{u_+} (B_1 + (X - B_0) G_1 / (2 G_0)) T^{-1/2} du`.
  Route: `thmSmoSpec_unique` against the glued `Scoef`, `Scoef_one` (`S_1 = Sigma_1(., 0) + d_t Sigma_0(., 0)`) and `actionS0_frozen_hasDerivAt` (`eq:cp-dt`).

Differences from the paper: the chart-level facts (parity freezing `Sigma_1 = 0` at `t = 0`, `Sigma_0 = S_0^{(t)}` near `t = 0`) enter as the window premises `hone`/`hzero`
rather than being read off the bulk, soft-upper and soft-lower chart structures.

Not formalised: nothing at this level.  The discharge of `hone`/`hzero` for the chart-built windows (bulk: `BulkPhaseInputs.Sigma_one`/`Sigma_zero`; soft-upper: `softSigma` with `mu0_S0`; soft-lower: `softLoSigma` through the mirror family, `actionS0_neg`)
is `layer4_windows` (`Assembly/ThmAi.lean`, using `CorEigenZero.lean`) and the whole-band `CorEigenS1` is part of `corEigen_proved` (`Assembly/CorEigen.lean`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set Filter Topology FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

section Assembly

variable {ι : Type*} [Fintype ι] {F : SymbolFamily Par} {K : Set Par} {t0 : ℝ} {M : ℕ} {a b : ι → Par → ℝ} {δ : ℝ}

/-- `thmAi_of_windows` with the identification of the glued `S_l` with `Scoef` of the window phase on every window. -/
theorem thmAi_of_windows_spec (W : ∀ i, WindowPhase F K t0 M (a i) (b i)) (ht0 : 0 < t0) (hδ : 0 < δ) (hcov : WindowCover F K a b δ)
    (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K M) :
    ∃ (δ' Cn C hM : ℝ) (S : ℕ → Par → ℝ → ℝ), 0 < δ' ∧ SmoothExt F K M S δ' Cn ∧ ActionFormula F K S ∧ EigenRule F K M S hM C ∧
      ∀ i, ∀ μ ∈ K, ∀ l ≤ M, ∀ x ∈ Icc (a i μ) (b i μ), S l μ x = Scoef ((W i).Sigma μ) l x := by
  classical
  have hD0 : DM F K 0 := dm_zero_of_dm F K M hK hD
  obtain ⟨Cn, Cr, ε, hCn, hCr, hε, hreg, hrule⟩ := windows_local_all W ht0 (fun μ hμ i => (hcov.sub μ hμ i).2.1)
  have hden := density_of_windows W ht0 hδ hcov hK hH hD0
  obtain ⟨Cz, hz0, hzp, hzero⟩ := stepZeroD0 F K hK hH hD0
  have hglue : ∀ μ ∈ K, ∀ l ≤ M, ∃ g : ℝ → ℝ, (∀ i, ∀ x ∈ Icc (a i μ) (b i μ), g x = Scoef ((W i).Sigma μ) l x) ∧
      ContDiffOn ℝ ((M + 1 : ℕ) : WithTop ℕ∞) g (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) ∧
      ∀ n : ℕ, ∀ x ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ), ∃ i, x ∈ Icc (a i μ) (b i μ) ∧
        iteratedDerivWithin n g (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) x
          = iteratedDerivWithin n (Scoef ((W i).Sigma μ) l) (Icc (a i μ) (b i μ)) x :=
    fun μ hμ l hl => glue_contDiffOn (M + 1) _ _ (fun i => a i μ) (fun i => b i μ) (fun i => Scoef ((W i).Sigma μ) l)
      (hcov.sub μ hμ) (fun i => (hreg i μ hμ l hl).1) (agree_of_windows W ht0 hδ hcov hK hH hD0 hden hμ l hl) (hcov.cov μ hμ)
  let S : ℕ → Par → ℝ → ℝ := fun l μ => if h : μ ∈ K ∧ l ≤ M then Classical.choose (hglue μ h.1 l h.2) else fun _ => 0
  have hS : ∀ μ ∈ K, ∀ l ≤ M, (∀ i, ∀ x ∈ Icc (a i μ) (b i μ), S l μ x = Scoef ((W i).Sigma μ) l x) ∧
      ContDiffOn ℝ ((M + 1 : ℕ) : WithTop ℕ∞) (S l μ) (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) ∧
      ∀ n : ℕ, ∀ x ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ), ∃ i, x ∈ Icc (a i μ) (b i μ) ∧
        iteratedDerivWithin n (S l μ) (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) x
          = iteratedDerivWithin n (Scoef ((W i).Sigma μ) l) (Icc (a i μ) (b i μ)) x := by
    intro μ hμ l hl
    have h := Classical.choose_spec (hglue μ hμ l hl)
    have e : S l μ = Classical.choose (hglue μ hμ l hl) := by simp [S, hμ, hl]
    rw [e]
    exact h
  refine ⟨δ, Cn, Cr, min (min ε 1) (min hz0 (δ / (|Cz| + 1))), S, hδ, ?_, ?_, ?_, ?_⟩
  · intro μ hμ j hj
    obtain ⟨-, hc, hd⟩ := hS μ hμ j hj
    refine ⟨hc, fun n hn x hx => ?_⟩
    obtain ⟨i, hxi, heq⟩ := hd n x hx
    rw [heq]
    exact (hreg i μ hμ j hj).2 n hn x hxi
  · intro μ hμ X hX
    have hXU : X ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ) := ⟨by linarith [hX.1], by linarith [hX.2]⟩
    obtain ⟨i, hi1, hi2, -, -⟩ := hcov.cov μ hμ X hXU
    obtain ⟨hg, -, -⟩ := hS μ hμ 0 (Nat.zero_le _)
    rw [hg i X ⟨hi1, hi2⟩, Scoef_zero]
    exact (W i).Sigma_zero μ hμ X ⟨hi1, hi2⟩ hX
  · refine ⟨lt_min (lt_min hε one_pos) (lt_min hzp (div_pos hδ (by positivity))), ?_⟩
    intro μ hμ N hN Xs Um hE k
    have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have hN1 : F.step N ≤ ε := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hN3 : F.step N ≤ hz0 := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hN4 : F.step N ≤ δ / (|Cz| + 1) := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hCzh : |Cz| * F.step N < δ := by
      rw [le_div_iff₀ (by positivity)] at hN4
      nlinarith [abs_nonneg Cz]
    obtain ⟨h1, h2⟩ := hzero μ hμ N hN3 Xs Um hE k
    have hle : Cz * F.step N ≤ |Cz| * F.step N := mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le
    have hle2 : -(Cz * F.step N) ≤ |Cz| * F.step N := by
      have := mul_le_mul_of_nonneg_right (neg_le_abs Cz) hpos.le
      linarith
    have hxU : Xs k ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ) := ⟨by linarith, by linarith⟩
    obtain ⟨i, hi1, hi2, -, -⟩ := hcov.cov μ hμ (Xs k) hxU
    have hr := hrule i μ hμ N hN1 Xs Um hE k ⟨hi1, hi2⟩
    have e : ∑ j ∈ range (M + 1), F.step N ^ j * S j μ (Xs k) = ∑ j ∈ range (M + 1), F.step N ^ j * Scoef ((W i).Sigma μ) j (Xs k) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjM : j ≤ M := by have := Finset.mem_range.mp hj; omega
      rw [(hS μ hμ j hjM).1 i (Xs k) ⟨hi1, hi2⟩]
    rw [e]
    exact hr
  · intro i μ hμ l hl x hx
    exact (hS μ hμ l hl).1 i x hx

/-- **`CorEigenS1` from the windows** (the paper's proof of `cor:eigen` (a)): if the phase windows `W i` of `thm:smo-BSr` (with cover `hcov`) have, at every energy `X` of the open band in the window,
`Sigma_1(X, 0) = 0` (parity freezing: the frozen matrices have no odd jets) and `Sigma_0(X, t) = S_0^{(t)}(X)` for small `t`, then *every* `S` with `SmoothExt`, the rule and the action formula (at `M = 1`, `0 < delta'`)
has `S_1 = d_t S_0^{(t)}|_{t=0} = int_{u_-}^{u_+} (B_1 + (X - B_0) G_1/(2 G_0)) T^{-1/2} du` on the open band.  Proof: `thmSmoSpec_unique` against the glued `S* = Scoef (Sigma)` (`thmAi_of_windows_spec`), `Scoef_one`
(`S_1 = Sigma_1(., 0) + d_t Sigma_0(., 0)`), and `actionS0_frozen_hasDerivAt` (`eq:cp-dt`). -/
theorem corEigenS1_of_windows {ι : Type*} [Fintype ι] {F : SymbolFamily Par} {K : Set Par} {t0 : ℝ} {a b : ι → Par → ℝ} {δ : ℝ}
    (W : ∀ i, WindowPhase F K t0 1 (a i) (b i)) (ht0 : 0 < t0) (hδ : 0 < δ) (hcov : WindowCover F K a b δ)
    (hone : ∀ i, ∀ μ ∈ K, ∀ X ∈ Icc (a i μ) (b i μ), X ∈ Ioo (F.bandLo μ) (F.bandHi μ) → (W i).Sigma μ 1 X 0 = 0)
    (hzero : ∀ i, ∀ μ ∈ K, ∀ X ∈ Icc (a i μ) (b i μ), X ∈ Ioo (F.bandLo μ) (F.bandHi μ) →
      ∀ᶠ t in 𝓝 (0 : ℝ), (W i).Sigma μ 0 X t = actionS0 (frozenFamily F 0) (μ, t) X) :
    IsCompact K → HypOn F K → DM F K 1 →
    ∀ (S : ℕ → Par → ℝ → ℝ) (δ' Cn hM C : ℝ), 0 < δ' → SmoothExt F K 1 S δ' Cn → EigenRule F K 1 S hM C → ActionFormula F K S →
      ∀ μ ∈ K, ∀ X ∈ Ioo (F.bandLo μ) (F.bandHi μ),
        HasDerivAt (fun t : ℝ => actionS0 (frozenFamily F 0) (μ, t) X) (S 1 μ X) 0 ∧
        IntervalIntegrable (fun u => (F.B 1 μ u + (X - F.B 0 μ u) * F.G 1 μ u / (2 * F.G 0 μ u)) /
          Real.sqrt (Tfun F.L (F.G 0 μ) (F.B 0 μ) X u)) MeasureTheory.volume (F.uMinus μ X) (F.uPlus μ X) ∧
        S 1 μ X = ∫ u in (F.uMinus μ X)..(F.uPlus μ X), (F.B 1 μ u + (X - F.B 0 μ u) * F.G 1 μ u / (2 * F.G 0 μ u)) /
          Real.sqrt (Tfun F.L (F.G 0 μ) (F.B 0 μ) X u) := by
  intro hK hH hD S δ' Cn hM C hδ' hsm hrule _hact μ hμ X hX
  have hD0 : DM F K 0 := dm_zero_of_dm F K 1 hK hD
  obtain ⟨δ2, Cn2, C2, hM2, Sg, hδ2, hsm2, -, hrule2, hspec⟩ := thmAi_of_windows_spec W ht0 hδ hcov hK hH hD
  have hden : EigDensity F K := fun hK' hH' hD0' => density_of_windows W ht0 hδ hcov hK' hH' hD0'
  have huniq := thmSmoSpec_unique F K 1 hden (stepZeroD0 F K) hK hH hD S Sg δ' δ2 Cn Cn2 hM hM2 C C2 hδ' hδ2
    hsm hrule hsm2 hrule2 μ hμ 1 le_rfl X ⟨hX.1.le, hX.2.le⟩
  -- a window containing `X`
  have hXU : X ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ) := ⟨by linarith [hX.1], by linarith [hX.2]⟩
  obtain ⟨i, hi1, hi2, -, -⟩ := hcov.cov μ hμ X hXU
  have hSg : Sg 1 μ X = Scoef ((W i).Sigma μ) 1 X := hspec i μ hμ 1 le_rfl X ⟨hi1, hi2⟩
  have hev := hzero i μ hμ X ⟨hi1, hi2⟩ hX
  obtain ⟨hd, hint⟩ := actionS0_frozen_hasDerivAt F K hH hD hμ hX
  have hderiv : iteratedDeriv 1 (fun t => (W i).Sigma μ 0 X t) 0 = deriv (fun t : ℝ => actionS0 (frozenFamily F 0) (μ, t) X) 0 := by
    rw [iteratedDeriv_one]
    exact Filter.EventuallyEq.deriv_eq hev
  have hS1 : S 1 μ X = ∫ u in (F.uMinus μ X)..(F.uPlus μ X), (F.B 1 μ u + (X - F.B 0 μ u) * F.G 1 μ u / (2 * F.G 0 μ u)) /
      Real.sqrt (Tfun F.L (F.G 0 μ) (F.B 0 μ) X u) := by
    rw [huniq, hSg, Scoef_one, hone i μ hμ X ⟨hi1, hi2⟩ hX, hderiv, hd.deriv, zero_add]
  exact ⟨hS1 ▸ hd, hint, hS1⟩

/-- **`CorEigenS1` for `G` from windows of the truncation `truncSM G 1`** (the form in which the assembly of `thmSmoSpec_core` produces the windows): the same as `corEigenS1_of_windows`, with `S` an `S` for `G` itself.  The glued
`S* = Scoef (Sigma)` is an `S` for `truncSM G 1` (`thmAi_of_windows_spec`), hence for `G` (`thmAi_of_trunc`); `thmSmoSpec_unique` for `G` (with `EigDensity` from `eigDensity_of_trunc`) identifies `S` with `S*` on the band.  The chart-level
premises `hone`, `hzero` are stated for the frozen family of `G` at index `0` (`G_0 + t G_1`, `B_0 + t B_1`), which is the one `eq:cp-dt` differentiates. -/
theorem corEigenS1_of_trunc_windows {ι : Type*} [Fintype ι] {G : SymbolFamily Par} {K : Set Par} {t0 : ℝ} {a b : ι → Par → ℝ} {δ : ℝ}
    (W : ∀ i, WindowPhase (truncSM G 1) K t0 1 (a i) (b i)) (ht0 : 0 < t0) (hδ : 0 < δ) (hcov : WindowCover (truncSM G 1) K a b δ)
    (hone : ∀ i, ∀ μ ∈ K, ∀ X ∈ Icc (a i μ) (b i μ), X ∈ Ioo (G.bandLo μ) (G.bandHi μ) → (W i).Sigma μ 1 X 0 = 0)
    (hzero : ∀ i, ∀ μ ∈ K, ∀ X ∈ Icc (a i μ) (b i μ), X ∈ Ioo (G.bandLo μ) (G.bandHi μ) →
      ∀ᶠ t in 𝓝 (0 : ℝ), (W i).Sigma μ 0 X t = actionS0 (frozenFamily G 0) (μ, t) X) :
    IsCompact K → HypOn G K → DM G K 1 →
    ∀ (S : ℕ → Par → ℝ → ℝ) (δ' Cn hM C : ℝ), 0 < δ' → SmoothExt G K 1 S δ' Cn → EigenRule G K 1 S hM C → ActionFormula G K S →
      ∀ μ ∈ K, ∀ X ∈ Ioo (G.bandLo μ) (G.bandHi μ),
        HasDerivAt (fun t : ℝ => actionS0 (frozenFamily G 0) (μ, t) X) (S 1 μ X) 0 ∧
        IntervalIntegrable (fun u => (G.B 1 μ u + (X - G.B 0 μ u) * G.G 1 μ u / (2 * G.G 0 μ u)) /
          Real.sqrt (Tfun G.L (G.G 0 μ) (G.B 0 μ) X u)) MeasureTheory.volume (G.uMinus μ X) (G.uPlus μ X) ∧
        S 1 μ X = ∫ u in (G.uMinus μ X)..(G.uPlus μ X), (G.B 1 μ u + (X - G.B 0 μ u) * G.G 1 μ u / (2 * G.G 0 μ u)) /
          Real.sqrt (Tfun G.L (G.G 0 μ) (G.B 0 μ) X u) := by
  intro hK hH hD S δ' Cn hM C hδ' hsm hrule _hact μ hμ X hX
  have hHT := hypOn_truncSM G K 1 hH
  have hDT := dm_truncSM G K 1 hD
  have hD0T : DM (truncSM G 1) K 0 := dm_zero_of_dm _ K 1 hK hDT
  have hb : (truncSM G 1).bandLo μ = G.bandLo μ ∧ (truncSM G 1).bandHi μ = G.bandHi μ := band_truncSM G 1 μ
  obtain ⟨δ2, Cn2, C2, hM2, Sg, hδ2, hsm2, hact2, hrule2, hspec⟩ := thmAi_of_windows_spec W ht0 hδ hcov hK hHT hDT
  obtain ⟨hM2', C2', hsm2', -, hrule2'⟩ := thmAi_of_trunc G K 1 hK hH hD Sg δ2 Cn2 hM2 C2 hδ2 hsm2 hact2 hrule2
  have hden : EigDensity G K := eigDensity_of_trunc G K 1 hK hH hD (density_of_windows W ht0 hδ hcov hK hHT hD0T)
  have huniq := thmSmoSpec_unique G K 1 hden (stepZeroD0 G K) hK hH hD S Sg δ' δ2 Cn Cn2 hM hM2' C C2' hδ' hδ2
    hsm hrule hsm2' hrule2' μ hμ 1 le_rfl X ⟨hX.1.le, hX.2.le⟩
  have hXU : X ∈ Icc ((truncSM G 1).bandLo μ - δ) ((truncSM G 1).bandHi μ + δ) :=
    ⟨by rw [hb.1]; linarith [hX.1], by rw [hb.2]; linarith [hX.2]⟩
  obtain ⟨i, hi1, hi2, -, -⟩ := hcov.cov μ hμ X hXU
  have hSg : Sg 1 μ X = Scoef ((W i).Sigma μ) 1 X := hspec i μ hμ 1 le_rfl X ⟨hi1, hi2⟩
  have hev := hzero i μ hμ X ⟨hi1, hi2⟩ hX
  obtain ⟨hd, hint⟩ := actionS0_frozen_hasDerivAt G K hH hD hμ hX
  have hderiv : iteratedDeriv 1 (fun t => (W i).Sigma μ 0 X t) 0 = deriv (fun t : ℝ => actionS0 (frozenFamily G 0) (μ, t) X) 0 := by
    rw [iteratedDeriv_one]
    exact Filter.EventuallyEq.deriv_eq hev
  have hS1 : S 1 μ X = ∫ u in (G.uMinus μ X)..(G.uPlus μ X), (G.B 1 μ u + (X - G.B 0 μ u) * G.G 1 μ u / (2 * G.G 0 μ u)) /
      Real.sqrt (Tfun G.L (G.G 0 μ) (G.B 0 μ) X u) := by
    rw [huniq, hSg, Scoef_one, hone i μ hμ X ⟨hi1, hi2⟩ hX, hderiv, hd.deriv, zero_add]
  exact ⟨hS1 ▸ hd, hint, hS1⟩

end Assembly

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmAi_of_windows_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmAi_of_windows_spec

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.corEigenS1_of_trunc_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.corEigenS1_of_trunc_windows

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.corEigenS1_of_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.corEigenS1_of_windows

end FormalResearch.JacobiEigenvectors.TheoremA
