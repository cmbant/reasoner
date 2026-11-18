module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssembly
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkWindows
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZeroCovered
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkSlope
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumRestrict

/-!
# Paper J, Layer 2: the bulk windows and the final assembly of `thm:smo-spec` / `thm:A (i)` (L2.S6), modulo the labels and the soft windows

Source: Paper J `app_thmA.tex`, `thm:smo-BSr` ("Bulk phases": `Sigma_nu(X_k(t), t, h) = pi h (k + 1/2) + O(h^{M+1})`, "the labels give `k' = k`"), proof of `thm:smo-spec`.
Frozen statements: `ThmSmoSpec`, `ThmAi` (`TheoremA/Statements.lean`); the chain is in the docstring of `SpectrumAssembly.lean`.

## Proved here (axiom-pinned)

* `bulkPhaseWindow`: a bulk block `[lo nu, hi nu]` of `BulkPhaseInputs` for the frozen family of `T` gives a `WindowPhase` for `T` (the labelled rule `eq:smo-BSr2` at `t = h` is `bulk_BSr2`, with `frozenFamily_jacobiMat_at_step`).
  Premises (named, the paper's own): `hlab` = `BulkWindowLabels` (`lem:smo-bulkphase` (3), the labels `k' = k`: **this is where the soft-edge window `0` / `PropThaW2` (3) enters**),
  `hstd` = `StdAssump` of the frozen family, positive bonds of `T` for small `h`, and the slope `hslope` (**proved**: `bulk_slope`, `TheoremA/BulkSlope.lean`).
* `dm_truncSM`, `hypOn_truncSM`, `thmAi_of_trunc`, `eigDensity_of_trunc`: passage between `tilde J_h = truncSM G M` and `J_h`.
* `frozenReg_trunc`, `stdAssump_trunc` (**F-S6-7 discharged**): `(D_M)`, `Kidx = (M+1)/2` give `FrozenReg` of `truncSM G M`, hence (`HypMorse.frozenStandard_of_reg`) the standing assumptions of its frozen family on `paramSet K t0'`
  for every `0 < t0' <= t1`, at the index `max M 1 / 2` that `bulk_BSr2` takes (`EK_lower_zero_tail`, the dropped even jet vanishes).
* `thmSmoSpec_core`: the conclusion `SmoSpecConcl` (`ThmAi`, uniqueness (b), extension independence (c)) from explicit bulk data at a given `t0`, modulo `hstd`, `hlab`, `WS`, `hcov`.
* **`thmSmoSpec`: the frozen `ThmSmoSpec`** (charts of `truncFamily G M`) modulo exactly `hlabels` (`BulkWindowLabels` of every block), `WS` (the two soft `WindowPhase`s) and `hcov` (the cover `WindowCover`):
  the chart data are restricted to `t0' = min t0 t1` (F-t0; `TheoremA/SpectrumRestrict.lean`), so no premise on the size of `t0` is needed.

## Differences from the paper / what remains (findings F-S6-4..7 are in `SpectrumAssembly.lean`)

* Remaining premises of `thmSmoSpec`: `hlabels` (labels `k' = k`, from `PropThaW2` (3)/(4), L2.C7, for the bulk blocks), `WS` (soft windows: the upper one is `softUpWindow`, `TheoremA/SpectrumAssemblySoft.lean`, from
  `SoftPhaseInputs` and the labels `SoftLabels`; the lower one needs the reversal of eigen-systems of `negFamily`), `hcov` (the window cover with positive-length overlaps, as a relation between the chart fields
  `ChartInputs.cover_bulk`, `cover` (now with the F-S6-4 form) and the soft window radii; not derived).
* `C^infty` jets (`smo_jets` at every `M'`) are not assembled.

## Not formalised

The items listed as remaining premises.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

/-! ### The truncated family and the frozen family at `t = h` -/

/-- The frozen bonds at `t = h` are those of the family. -/
lemma frozen_bondA_at_step (G : SymbolFamily Par) (Kidx : ℕ) (μ : Par) (N : ℕ) (n : ℤ) :
    (frozenFamily G Kidx).bondA (μ, G.step N) N n = G.bondA μ N n := by
  have hE : ∀ n : ℤ, (frozenFamily G Kidx).entryE (μ, G.step N) N n = G.entryE μ N n := by
    intro n
    simp [SymbolFamily.entryE, SymbolFamily.step, frozenFamily]
  simp only [SymbolFamily.bondA, hE]

/-- The action of the frozen family at `t = 0` is that of the family. -/
lemma actionS0_frozen_zero (G : SymbolFamily Par) (Kidx : ℕ) (μ : Par) (X : ℝ) :
    actionS0 (frozenFamily G Kidx) (μ, 0) X = actionS0 G μ X := by
  unfold actionS0
  simp [frozenFamily]

/-- The action of the truncated family is that of the family. -/
lemma actionS0_truncSM (G : SymbolFamily Par) (M : ℕ) (μ : Par) (X : ℝ) :
    actionS0 (truncSM G M) μ X = actionS0 G μ X := by
  unfold actionS0
  simp [truncSM]

/-- `(D_M)` passes to the truncation `tilde J_h = truncSM G M` (jets `<= M` unchanged, remainder exactly zero). -/
theorem dm_truncSM (G : SymbolFamily Par) (K : Set Par) (M : ℕ) (hD : DM G K M) : DM (truncSM G M) K M := by
  refine ⟨fun j hj => ?_, ⟨0, fun μ hμ N s hs => ?_⟩⟩
  · have e1 : (truncSM G M).G j = G.G j := by funext μ s; simp [truncSM, hj]
    have e2 : (truncSM G M).B j = G.B j := by funext μ s; simp [truncSM, hj]
    rw [e1, e2]
    exact hD.reg j hj
  · refine ⟨?_, ?_⟩
    · have e : ∑ j ∈ range (M + 1), (truncSM G M).step N ^ j * (truncSM G M).G j μ s
          = ∑ j ∈ range (M + 1), (truncSM G M).step N ^ j * G.G j μ s :=
        Finset.sum_congr rfl (fun j hj => by simp [truncSM, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)])
      rw [e]; simp [truncSM]
    · have e : ∑ j ∈ range (M + 1), (truncSM G M).step N ^ j * (truncSM G M).B j μ s
          = ∑ j ∈ range (M + 1), (truncSM G M).step N ^ j * G.B j μ s :=
        Finset.sum_congr rfl (fun j hj => by simp [truncSM, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)])
      rw [e]; simp [truncSM]

/-- `(H1)--(H3)` passes to the truncation (same principal symbols). -/
theorem hypOn_truncSM (G : SymbolFamily Par) (K : Set Par) (M : ℕ) (hH : HypOn G K) : HypOn (truncSM G M) K := by
  obtain ⟨g, hg⟩ := hH
  refine ⟨g, fun μ hμ => ?_⟩
  have e1 : (truncSM G M).G 0 μ = G.G 0 μ := by funext s; simp [truncSM]
  have e2 : (truncSM G M).B 0 μ = G.B 0 μ := by funext s; simp [truncSM]
  rw [e1, e2]
  exact hg μ hμ

/-- The band of the truncation is the band of the family. -/
lemma band_truncSM (G : SymbolFamily Par) (M : ℕ) (μ : Par) :
    (truncSM G M).bandLo μ = G.bandLo μ ∧ (truncSM G M).bandHi μ = G.bandHi μ :=
  band_eq_of_symbols G (truncSM G M) μ rfl (fun s _ => by simp [truncSM]) (fun s _ => by simp [truncSM])

/-! ### From `tilde J_h` back to `J_h` -/

/-- **Back to `J_h`** (paragraph "Back to `J_h`"): the conclusion of `ThmAi` for `G` from that for the truncation (`smo_SM` through `eigClose_of_jets`, `rule_transfer`). -/
theorem thmAi_of_trunc (G : SymbolFamily Par) (K : Set Par) (M : ℕ) (hK : IsCompact K) (hH : HypOn G K) (hD : DM G K M)
    (S : ℕ → Par → ℝ → ℝ) (δ Cn hM C : ℝ) (hδ : 0 < δ) (h1 : SmoothExt (truncSM G M) K M S δ Cn)
    (h2 : ActionFormula (truncSM G M) K S) (h3 : EigenRule (truncSM G M) K M S hM C) :
    ∃ hM' C' : ℝ, SmoothExt G K M S δ Cn ∧ ActionFormula G K S ∧ EigenRule G K M S hM' C' := by
  have hDT := dm_truncSM G K M hD
  have hHT := hypOn_truncSM G K M hH
  have hbe : ∀ μ ∈ K, G.bandLo μ = (truncSM G M).bandLo μ ∧ G.bandHi μ = (truncSM G M).bandHi μ :=
    fun μ _ => ⟨(band_truncSM G M μ).1.symm, (band_truncSM G M μ).2.symm⟩
  have hband : ∀ μ ∈ K, (truncSM G M).bandLo μ < (truncSM G M).bandHi μ := bandLo_lt_bandHi _ K M hHT hDT
  have hcl : EigClose (truncSM G M) G K M := eigClose_of_jets (truncSM G M) G K M hK hHT hH hDT hD rfl
    (fun μ _ i hi s _ => by simp [truncSM, hi])
  obtain ⟨hM', C', hr⟩ := rule_transfer (truncSM G M) G K M hcl (stepZeroD0 _ K) (stepZeroD0 G K) hband hbe hK hHT hH
    (dm_zero_of_dm _ K M hK hDT) (dm_zero_of_dm G K M hK hD) S δ Cn hM C hδ h1 h3
  refine ⟨hM', C', ?_, ?_, hr⟩
  · intro μ hμ j hj
    have := h1 μ hμ j hj
    rw [(band_truncSM G M μ).1, (band_truncSM G M μ).2] at this
    exact this
  · intro μ hμ X hX
    have hX' : X ∈ Icc ((truncSM G M).bandLo μ) ((truncSM G M).bandHi μ) := by
      rw [(band_truncSM G M μ).1, (band_truncSM G M μ).2]; exact hX
    have := h2 μ hμ X hX'
    rw [actionS0_truncSM] at this
    exact this

/-- **`EigDensity` for `J_h`** from the density of the eigenvalues of `tilde J_h` (`eigClose_of_jets`). -/
theorem eigDensity_of_trunc (G : SymbolFamily Par) (K : Set Par) (M : ℕ) (hK : IsCompact K) (hH : HypOn G K) (hD : DM G K M)
    (hden : ∃ CD hD : ℝ, 0 < hD ∧ ∀ μ ∈ K, ∀ N : ℕ, (truncSM G M).step N ≤ hD →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem ((truncSM G M).jacobiMat μ N) Xs Um →
        ∀ Y ∈ Icc ((truncSM G M).bandLo μ) ((truncSM G M).bandHi μ), ∃ k : Fin (N + 1), |Xs k - Y| ≤ CD * (truncSM G M).step N) :
    EigDensity G K := by
  intro _ _ _
  have hDT := dm_truncSM G K M hD
  have hHT := hypOn_truncSM G K M hH
  obtain ⟨CD, hDd, hDpos, hdens⟩ := hden
  obtain ⟨he0, hep, hex⟩ := exists_eig_small (truncSM G M) K hHT (dm_zero_of_dm _ K M hK hDT)
  obtain ⟨Ccl, hcl0, hclp, hclose⟩ := (eigClose_of_jets (truncSM G M) G K M hK hHT hH hDT hD rfl
    (fun μ _ i hi s _ => by simp [truncSM, hi])).2
  refine ⟨|CD| + |Ccl|, min (min hDd he0) (min hcl0 1), lt_min (lt_min hDpos hep) (lt_min hclp one_pos), ?_⟩
  intro μ hμ N hN Xs' Um' hE' Y hY
  have hpos : 0 < G.step N := FormalResearch.JB.stepSize_pos G.L_pos N
  have hst : (truncSM G M).step N = G.step N := rfl
  have h1 : (truncSM G M).step N ≤ hDd := by rw [hst]; exact hN.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : (truncSM G M).step N ≤ he0 := by rw [hst]; exact hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : (truncSM G M).step N ≤ hcl0 := by rw [hst]; exact hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : G.step N ≤ 1 := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Xs, Um, hE⟩ := hex μ hμ N h2
  obtain ⟨k, hk⟩ := hdens μ hμ N h1 Xs Um hE Y (by rw [(band_truncSM G M μ).1, (band_truncSM G M μ).2]; exact hY)
  refine ⟨k, ?_⟩
  have hc := hclose μ hμ N h3 Xs Um hE Xs' Um' hE' k
  rw [hst] at hk
  have hpow : G.step N ^ (M + 1) ≤ G.step N := pow_le_of_le_one hpos.le h4 (Nat.succ_ne_zero M)
  have hc2 : |Xs k - Xs' k| ≤ |Ccl| * G.step N :=
    hc.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hpos.le _)).trans (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)))
  have hk2 : |Xs k - Y| ≤ |CD| * G.step N := hk.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le)
  calc |Xs' k - Y| = |(Xs' k - Xs k) + (Xs k - Y)| := by ring_nf
    _ ≤ |Xs' k - Xs k| + |Xs k - Y| := abs_add_le _ _
    _ ≤ |Ccl| * G.step N + |CD| * G.step N := by
        refine add_le_add ?_ hk2
        rw [abs_sub_comm]; exact hc2
    _ = (|CD| + |Ccl|) * G.step N := by ring

/-! ### The bulk window -/

/-- **A bulk block is a `WindowPhase`** (`eq:smo-BSr2` on `J_nu`, at `t = h`): `bulk_BSr2` for the frozen family of `T` (whose matrix at `t = h` is that of `T`), under the labels
`hlab = BulkWindowLabels`, the standing assumptions `hstd` of the frozen family, positive bonds of `T`, and the slope `hslope`. -/
def bulkPhaseWindow {T : SymbolFamily Par} {K : Set Par} {t0 : ℝ} {M Kidx : ℕ} {U V : ℝ → ℝ → ℝ} {Jlo Jhi : ℝ}
    {CL : BulkWeberChart (frozenFamily T Kidx) (paramSet K t0) Jlo Jhi (max M 1) U V}
    {CR : BulkWeberChart (mirrorFamily (frozenFamily T Kidx)) (paramSet K t0) Jlo Jhi (max M 1) U V}
    (PI : BulkPhaseInputs (frozenFamily T Kidx) (paramSet K t0) K t0 Jlo Jhi M U V CL CR) (ht0 : 0 < t0)
    (hcoup : CR.c = (frozenFamily T Kidx).L - CL.c' ∧ CR.c' = (frozenFamily T Kidx).L - CL.c)
    (hstd : ∃ r, StdAssump (frozenFamily T Kidx) (paramSet K t0) (max M 1 / 2) r)
    (hlab : BulkWindowLabels (frozenFamily T Kidx) K t0 Jlo Jhi)
    (hpos : ∃ h1 : ℝ, 0 < h1 ∧ ∀ μ ∈ K, ∀ N : ℕ, T.step N ≤ h1 → ∀ n : ℤ, 0 ≤ n → n < N → 0 < T.bondA μ N n)
    (hslope : ∃ c : ℝ, 0 < c ∧ ∀ μ ∈ K, ∀ X ∈ Ioo Jlo Jhi, deriv (fun X' => PI.Sigma μ 0 X' 0) X ≤ -c) :
    WindowPhase T K t0 M (fun _ => Jlo) (fun _ => Jhi) where
  Sigma := PI.Sigma
  Sigma_reg := fun μ hμ j hj => PI.Sigma_reg μ hμ j hj
  Sigma_bdd := PI.Sigma_bdd
  Sigma_zero := fun μ hμ X hX _ => by
    have h := PI.Sigma_zero μ hμ X hX 0 ⟨by linarith, ht0.le⟩
    rw [h]
    have := actionS0_frozen_zero T Kidx μ X
    unfold actionS0 at this ⊢
    exact this
  slope := hslope
  rule := by
    obtain ⟨r, hr⟩ := hstd
    obtain ⟨C, h0, hh0, N1, hmain⟩ := bulk_BSr2 PI (fun μ hμ t ht => ⟨hμ, ht⟩) hcoup r hr hlab
    obtain ⟨h1, hh1, hposT⟩ := hpos
    refine ⟨C, min (min h0 t0) (min h1 (T.L / ((N1 : ℝ) + 1))), lt_min (lt_min hh0 ht0) (lt_min hh1 (div_pos T.L_pos (by positivity))), ?_⟩
    intro μ hμ N hN Xs Um hE k hk
    have hst : 0 < T.step N := FormalResearch.JB.stepSize_pos T.L_pos N
    have hNt : T.step N ≤ t0 := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hN0 : T.step N ≤ h0 := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hN1' : T.step N ≤ h1 := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hNN : T.step N ≤ T.L / ((N1 : ℝ) + 1) := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hN1N : N1 ≤ N := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 : ((N : ℝ) + 1) < (N1 : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hcon
      have h2 : T.L / ((N1 : ℝ) + 1) < T.L / ((N : ℝ) + 1) := div_lt_div_of_pos_left T.L_pos (by positivity) h1
      have h3 : T.step N = T.L / ((N : ℝ) + 1) := rfl
      linarith
    have hE' : IsEigenSystem ((frozenFamily T Kidx).jacobiMat (μ, T.step N) N) Xs Um := by
      rw [frozenFamily_jacobiMat_at_step]; exact hE
    exact hmain μ hμ (T.step N) ⟨by linarith, hNt⟩ N hN1N hN0 (fun n hn1 hn2 => by
      rw [frozen_bondA_at_step]; exact hposT μ hμ N hN1' n hn1 hn2) Xs Um hE' k hk

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmAi_of_trunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmAi_of_trunc

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.eigDensity_of_trunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.eigDensity_of_trunc

/-! ### The standing assumptions of the frozen truncated family (findings F-S6-7, F-t0) -/

/-- The zero family of jets is regular of every order. -/
lemma jetReg_zero {K : Set Par} (L : ℝ) (n : ℕ) : JetReg (fun (_ : Par) (_ : ℝ) => (0 : ℝ)) K L n := by
  refine ⟨fun μ _ => contDiffOn_const, fun i hi => ?_⟩
  have : ∀ x : ℝ, iteratedDerivWithin i (fun _ : ℝ => (0 : ℝ)) (Icc 0 L) x = 0 := by
    intro x
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin]
    simp
  simp only [this]
  exact continuousOn_const

/-- **`FrozenReg` of the truncated family** (finding F-S6-7): `(D_M)` and `Kidx = (M+1)/2` give the part of `(D_{2 Kidx+1})` that `sec:tha-standing` uses, for `tilde J_h = truncSM G M`
(jets `0` beyond `M`, no remainder), with `r = regBudget M`. -/
theorem frozenReg_trunc (G : SymbolFamily Par) (K : Set Par) (M Kidx : ℕ) (hKidx : Kidx = (M + 1) / 2) (hD : DM G K M) :
    HypMorse.FrozenReg (truncSM G M) K Kidx (regBudget M) := by
  have hbud : regBudget (max (2 * Kidx - 1) 0) ≤ regBudget M := by unfold regBudget; omega
  have hjet : ∀ i j : ℕ, i / 2 = j → j ≤ Kidx →
      JetReg ((truncSM G M).G i) K G.L (regBudget M - 10 * j) ∧ JetReg ((truncSM G M).B i) K G.L (regBudget M - 10 * j) := by
    intro i j hij hj
    by_cases hi : i ≤ M
    · have e1 : (truncSM G M).G i = G.G i := by funext μ s; simp [truncSM, hi]
      have e2 : (truncSM G M).B i = G.B i := by funext μ s; simp [truncSM, hi]
      rw [e1, e2, ← hij]
      exact hD.reg i hi
    · have e1 : (truncSM G M).G i = fun (_ : Par) (_ : ℝ) => (0 : ℝ) := by funext μ s; simp [truncSM, hi]
      have e2 : (truncSM G M).B i = fun (_ : Par) (_ : ℝ) => (0 : ℝ) := by funext μ s; simp [truncSM, hi]
      rw [e1, e2]
      exact ⟨jetReg_zero G.L _, jetReg_zero G.L _⟩
  refine ⟨hbud, fun j hj => ?_, ⟨0, fun μ hμ N s hs => ?_⟩⟩
  · have a := hjet (2 * j) j (by omega) hj
    have b := hjet (2 * j + 1) j (by omega) hj
    exact ⟨a.1, a.2, b.1, b.2⟩
  · have hsum : ∀ f : ℕ → ℝ, ∑ i ∈ Finset.range (2 * Kidx + 1 + 1), (truncSM G M).step N ^ i * (if i ≤ M then f i else 0)
        = ∑ i ∈ Finset.range (M + 1), (truncSM G M).step N ^ i * f i := by
      intro f
      have h1 : ∑ i ∈ Finset.range (2 * Kidx + 1 + 1), (truncSM G M).step N ^ i * (if i ≤ M then f i else 0)
          = ∑ i ∈ Finset.range (M + 1), (truncSM G M).step N ^ i * (if i ≤ M then f i else 0) := by
        symm
        refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) (fun i hi hni => ?_)
        have : ¬ i ≤ M := by
          intro h'; exact hni (Finset.mem_range.mpr (by omega))
        simp [this]
      rw [h1]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have : i ≤ M := by have := Finset.mem_range.mp hi; omega
      simp [this]
    have e1 : ∑ i ∈ Finset.range (2 * Kidx + 1 + 1), (truncSM G M).step N ^ i * (truncSM G M).G i μ s
        = ∑ i ∈ Finset.range (M + 1), (truncSM G M).step N ^ i * G.G i μ s := by
      have := hsum (fun i => G.G i μ s)
      simpa [truncSM] using this
    have e2 : ∑ i ∈ Finset.range (2 * Kidx + 1 + 1), (truncSM G M).step N ^ i * (truncSM G M).B i μ s
        = ∑ i ∈ Finset.range (M + 1), (truncSM G M).step N ^ i * G.B i μ s := by
      have := hsum (fun i => G.B i μ s)
      simpa [truncSM] using this
    rw [e1, e2]
    simp only [truncSM, sub_self, abs_zero, zero_mul]
    exact ⟨le_rfl, le_rfl⟩

/-- **Standing assumptions of the frozen truncated family on `paramSet K t0'`, for every `0 < t0' <= t1`, at the index `max M 1 / 2` that `bulk_BSr2` takes** (findings F-S6-7, F-t0):
`frozenStandard_of_reg` for `frozenReg_trunc`, restriction to `t0' <= t1` (`stdAssump_restrict`), and lowering the index from `Kidx = (M+1)/2` to `max M 1 / 2` (they differ for odd `M`, where
the dropped even jet `G_{2 Kidx} = G_{M+1}` vanishes: `EK_lower_zero_tail`). -/
theorem stdAssump_trunc (G : SymbolFamily Par) (K : Set Par) (M Kidx : ℕ) (hKidx : Kidx = (M + 1) / 2) (hK : IsCompact K) (hH : HypOn G K) (hD : DM G K M) :
    ∃ t1 : ℝ, 0 < t1 ∧ ∀ t0' : ℝ, 0 < t0' → t0' ≤ t1 →
      ∃ r : ℕ, StdAssump (frozenFamily (truncSM G M) Kidx) (paramSet K t0') (max M 1 / 2) r := by
  obtain ⟨t1, ht1, hs⟩ := HypMorse.frozenStandard_of_reg (truncSM G M) K Kidx (regBudget M) hK (hypOn_truncSM G K M hH)
    (frozenReg_trunc G K M Kidx hKidx hD)
  refine ⟨t1, ht1, fun t0' ht0' ht01 => ⟨regBudget M, ?_⟩⟩
  have hsub : paramSet K t0' ⊆ paramSet K t1 := Set.prod_mono subset_rfl (Set.Icc_subset_Icc (by linarith) ht01)
  obtain ⟨hPc, hEK, hHyp⟩ := stdAssump_restrict hs hsub (hK.prod isCompact_Icc)
  refine ⟨hPc, EK_lower_zero_tail hEK (by omega) (fun j hj1 hj2 μ hμ => ?_), hHyp⟩
  have h2j : ¬ 2 * j ≤ M := by omega
  have h2j1 : ¬ 2 * j + 1 ≤ M := by omega
  have hG : (frozenFamily (truncSM G M) Kidx).G (2 * j) μ = 0 := by
    have := HypMorse.frozen_G_eq (truncSM G M) Kidx j hj2 μ
    rw [this]; funext s; simp [truncSM, h2j, h2j1]
  have hB : (frozenFamily (truncSM G M) Kidx).B (2 * j) μ = 0 := by
    have := HypMorse.frozen_B_eq (truncSM G M) Kidx j hj2 μ
    rw [this]; funext s; simp [truncSM, h2j, h2j1]
  exact ⟨hG, hB⟩

/-! ### The assembly -/

/-- The conclusion of `ThmSmoSpec` (existence `ThmAi`, uniqueness (b), extension independence (c)); it does not depend on the charts. -/
def SmoSpecConcl (G : SymbolFamily Par) (K : Set Par) (M : ℕ) : Prop :=
  ThmAi G K M ∧
  (IsCompact K → HypOn G K → DM G K M →
    ∀ (S S' : ℕ → Par → ℝ → ℝ) (δ δ' Cn Cn' hM hM' C C' : ℝ), 0 < δ → 0 < δ' →
      SmoothExt G K M S δ Cn → EigenRule G K M S hM C → SmoothExt G K M S' δ' Cn' → EigenRule G K M S' hM' C' →
        ∀ μ ∈ K, ∀ j ≤ M, ∀ X ∈ Set.Icc (G.bandLo μ) (G.bandHi μ), S j μ X = S' j μ X) ∧
  (IsCompact K → HypOn G K → DM G K M →
    ∀ (S S' : ℕ → Par → ℝ → ℝ) (δ δ' Cn Cn' hM C : ℝ), 0 < δ → 0 < δ' →
      SmoothExt G K M S δ Cn → EigenRule G K M S hM C → SmoothExt G K M S' δ' Cn' →
        (∀ μ ∈ K, ∀ j ≤ M, ∀ X ∈ Set.Icc (G.bandLo μ) (G.bandHi μ), S' j μ X = S j μ X) →
          ∃ hM' C' : ℝ, EigenRule G K M S' hM' C')

/-- **Assembly of `thm:smo-spec` / `thm:A (i)`, on the charts of `tilde J_h` at a given `t0`** (explicit bulk data, no `ChartInputs`), modulo the named premises: `hstd` (`StdAssump` of the frozen
family on the chart's parameter set), `hlabels` (`BulkWindowLabels` of every block: the labels `k' = k`, from `PropThaW2` (3)/(4)), the soft windows `WS` (`WindowPhase` of the two soft edges) and the cover
`hcov`.  The slope of `S_0` on the blocks is **proved** (`bulk_slope`). -/
theorem thmSmoSpec_core (G : SymbolFamily Par) (K : Set Par) (M Kidx : ℕ) (t0 : ℝ) (U V : ℝ → ℝ → ℝ)
    {nb : ℕ} {lo hi : Fin nb → ℝ}
    {CL : ∀ ν, BulkWeberChart (frozenFamily (truncSM G M) Kidx) (paramSet K t0) (lo ν) (hi ν) (max M 1) U V}
    {CR : ∀ ν, BulkWeberChart (mirrorFamily (frozenFamily (truncSM G M) Kidx)) (paramSet K t0) (lo ν) (hi ν) (max M 1) U V}
    (PI : ∀ ν, BulkPhaseInputs (frozenFamily (truncSM G M) Kidx) (paramSet K t0) K t0 (lo ν) (hi ν) M U V (CL ν) (CR ν))
    (hcoup : ∀ ν, (CR ν).c = (frozenFamily (truncSM G M) Kidx).L - (CL ν).c' ∧ (CR ν).c' = (frozenFamily (truncSM G M) Kidx).L - (CL ν).c)
    (ht0 : 0 < t0)
    (hstd : ∃ r, StdAssump (frozenFamily (truncSM G M) Kidx) (paramSet K t0) (max M 1 / 2) r)
    (hlabels : ∀ ν, BulkWindowLabels (frozenFamily (truncSM G M) Kidx) K t0 (lo ν) (hi ν))
    (aS bS : Bool → Par → ℝ) (WS : ∀ s : Bool, WindowPhase (truncSM G M) K t0 M (aS s) (bS s))
    (δ : ℝ) (hδ : 0 < δ)
    (hcov : WindowCover (truncSM G M) K (Sum.elim (fun ν _ => lo ν) aS) (Sum.elim (fun ν _ => hi ν) bS) δ)
    (hK : IsCompact K) (hH : HypOn G K) (hD : DM G K M) :
    SmoSpecConcl G K M := by
  have hDT := dm_truncSM G K M hD
  have hHT := hypOn_truncSM G K M hH
  obtain ⟨C1, h1, hC1, hh1, hpos1⟩ := smoSM_of_DM G K M hK hH hD
  have hposT : ∃ h1 : ℝ, 0 < h1 ∧ ∀ μ ∈ K, ∀ N : ℕ, (truncSM G M).step N ≤ h1 → ∀ n : ℤ, 0 ≤ n → n < N → 0 < (truncSM G M).bondA μ N n :=
    ⟨h1, hh1, fun μ hμ N hN n hn1 hn2 => ((hpos1 μ hμ N hN).1 n hn1 hn2).2⟩
  have hslope : ∀ ν, ∃ c : ℝ, 0 < c ∧ ∀ μ ∈ K, ∀ X ∈ Ioo (lo ν) (hi ν), deriv (fun X' => (PI ν).Sigma μ 0 X' 0) X ≤ -c := by
    intro ν
    obtain ⟨r, hr⟩ := hstd
    exact bulk_slope (PI ν) ht0 (fun μ hμ => ⟨hμ, ⟨by linarith, ht0.le⟩⟩) hr
  let W : ∀ i : Fin nb ⊕ Bool, WindowPhase (truncSM G M) K t0 M (Sum.elim (fun ν _ => lo ν) aS i) (Sum.elim (fun ν _ => hi ν) bS i) :=
    fun i => match i with
      | Sum.inl ν => bulkPhaseWindow (PI ν) ht0 (hcoup ν) hstd (hlabels ν) hposT (hslope ν)
      | Sum.inr s => WS s
  obtain ⟨δ', Cn, C, hM, S, hδ', hsm, hact, hrule⟩ := thmAi_of_windows W ht0 hδ hcov hK hHT hDT
  obtain ⟨hM', C', hsm', hact', hrule'⟩ := thmAi_of_trunc G K M hK hH hD S δ' Cn hM C hδ' hsm hact hrule
  have hden := eigDensity_of_trunc G K M hK hH hD (density_of_windows W ht0 hδ hcov hK hHT (dm_zero_of_dm _ K M hK hDT))
  refine ⟨fun _ _ _ => ⟨δ', Cn, C', hM', S, hδ', hsm', hact', hrule'⟩, ?_, ?_⟩
  · exact thmSmoSpec_unique G K M hden (stepZeroD0 G K)
  · exact thmSmoSpec_extend G K M (stepZeroD0 G K)

/-- **`thm:smo-spec`** (the frozen statement `ThmSmoSpec`, for the charts of `tilde J_h`, F-S6-5), assembled from the bulk blocks and the soft windows modulo the named premises
`hlabels`, `WS`, `hcov` (see `thmSmoSpec_core`).  The standing assumptions of the frozen family (`hstd`, F-S6-7) and the slope on the blocks are **proved**: the chart data are restricted to `t0' = min t0 t1`
(`t1` of `frozenStandard_of_reg`, finding F-t0; `SpectrumRestrict.lean`). -/
theorem thmSmoSpec (G : SymbolFamily Par) (K : Set Par) (M Kidx : ℕ) (t0 : ℝ) (U V : ℝ → ℝ → ℝ) (cPC CPC : ℝ)
    (CI : ChartInputs (truncFamily G M) K Kidx t0 (max M 1) (2 * Kidx) U V cPC CPC)
    (PI : ∀ ν, BulkPhaseInputs (frozenFamily (truncFamily G M) Kidx) (paramSet K t0) K t0 (CI.lo ν) (CI.hi ν) M U V (CI.bulkL ν) (CI.bulkR ν))
    (ht0 : 0 < t0)
    (hlabels : ∀ ν, BulkWindowLabels (frozenFamily (truncSM G M) Kidx) K t0 (CI.lo ν) (CI.hi ν))
    (aS bS : Bool → Par → ℝ) (WS : ∀ s : Bool, WindowPhase (truncSM G M) K t0 M (aS s) (bS s))
    (δ : ℝ) (hδ : 0 < δ)
    (hcov : WindowCover (truncSM G M) K (Sum.elim (fun ν _ => CI.lo ν) aS) (Sum.elim (fun ν _ => CI.hi ν) bS) δ)
    (hK : IsCompact K) (hH : HypOn G K) (hD : DM G K M) :
    ThmSmoSpec G K M Kidx t0 U V cPC CPC CI PI := by
  intro hKidx
  obtain ⟨t1, ht1, hstd⟩ := stdAssump_trunc G K M Kidx hKidx hK hH hD
  set t0' : ℝ := min t0 t1 with ht0'def
  have ht0' : 0 < t0' := lt_min ht0 ht1
  have hle0 : t0' ≤ t0 := min_le_left _ _
  have hle1 : t0' ≤ t1 := min_le_right _ _
  have hP : paramSet K t0' ⊆ paramSet K t0 := Set.prod_mono subset_rfl (Set.Icc_subset_Icc (by linarith) hle0)
  have hlt : ∀ ν, K.Nonempty → CI.lo ν < CI.hi ν := fun ν ⟨μ, hμ⟩ => (hcov.sub μ hμ (Sum.inl ν)).2.1
  refine thmSmoSpec_core G K M Kidx t0' U V (CL := fun ν => (CI.bulkL ν).restrictSub hP) (CR := fun ν => (CI.bulkR ν).restrictSub hP)
    (fun ν => (PI ν).restrictSub (hlt ν) hP ht0' hle0) (fun ν => CI.overlap_match ν) ht0' (hstd t0' ht0' hle1) ?_
    aS bS (fun s => (WS s).restrictT0 (fun μ hμ => (hcov.sub μ hμ (Sum.inr s)).2.1) ht0' hle0) δ hδ hcov hK hH hD
  intro ν
  obtain ⟨Cl, h0, hh0, hl⟩ := hlabels ν
  exact ⟨Cl, h0, hh0, fun μ hμ t ht => hl μ hμ t ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulkPhaseWindow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulkPhaseWindow

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmSmoSpec_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmSmoSpec_core

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmSmoSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmSmoSpec

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.stdAssump_trunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.stdAssump_trunc

end FormalResearch.JacobiEigenvectors.TheoremA
