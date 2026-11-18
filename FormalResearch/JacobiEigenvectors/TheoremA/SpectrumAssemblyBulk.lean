module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssembly
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkWindows
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZeroCovered

/-!
# Paper J, Layer 2: the bulk windows and the final assembly of `thm:smo-spec` / `thm:A (i)` (L2.S6), modulo the labels and the soft windows

Source: Paper J `app_thmA.tex`, `thm:smo-BSr` ("Bulk phases": `Sigma_nu(X_k(t), t, h) = pi h (k + 1/2) + O(h^{M+1})`, "the labels give `k' = k`"), proof of `thm:smo-spec`.
Frozen statements: `ThmSmoSpec`, `ThmAi` (`TheoremA/Statements.lean`); the chain is in the docstring of `SpectrumAssembly.lean`.

## Proved here (axiom-pinned)

* `bulkPhaseWindow`: a bulk block `[lo nu, hi nu]` of `BulkPhaseInputs` for the frozen family of `T` gives a `WindowPhase` for `T` (the labelled rule `eq:smo-BSr2` at `t = h` is `bulk_BSr2`, with `frozenFamily_jacobiMat_at_step`).
  Premises (named, the paper's own): `hlab` = `BulkWindowLabels` (`lem:smo-bulkphase` (3), the labels `k' = k`: **this is where the soft-edge window `0` / `PropThaW2` (3) enters**),
  `hstd` = `StdAssump` of the frozen family (`sec:tha-standing`, finding F-S6-7), positive bonds of `T` for small `h`, and `hslope` (`|S_0'| >= c` on the block).
* `dm_truncSM`, `hypOn_truncSM`, `thmAi_of_trunc`, `eigDensity_of_trunc`: passage between `tilde J_h = truncSM G M` and `J_h`.
* `thmSmoSpecTrunc` (**`ThmSmoSpec` assembled, for the charts of `tilde J_h`**): `ThmAi G K M`, uniqueness (b) and extension independence (c), from the bulk windows and the soft windows
  (premise `WS`: `WindowPhase`s of the two soft edges, i.e. `PropThaW2` (3)/(4) with the regularity of `thm:smo-MPS/TPC/WT2`).

## Differences from the paper / what remains (findings F-S6-4..7 are in `SpectrumAssembly.lean`)

* The statement proved is `ThmSmoSpecTrunc` (the frozen `ThmSmoSpec` with `CI`, `_PI` taken for `truncSM F M`, F-S6-5): `Statements.lean` should replace `F` by `truncSM F M` in the types of `CI` and `_PI`.
* Remaining premises: `hlab` (labels `k' = k`, needs `PropThaW2` (3)/(4), L2.C7), `WS` (soft windows), `hslope` (bulk slope), `hstd` (F-S6-7), the cover `hcov` (F-S6-4), `hpos` (positive bonds, from `smoSM_of_DM`, derived below).
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

/-! ### The assembly -/

/-- **`ThmSmoSpec` for the charts of `tilde J_h`** (finding F-S6-5): the frozen statement with `CI`, `_PI` for `truncSM G M`; the conclusion (`ThmAi`, uniqueness (b), extension (c)) is about `G`. -/
def ThmSmoSpecTrunc (G : SymbolFamily Par) (K : Set Par) (M Kidx : ℕ) (t0 : ℝ) (U V : ℝ → ℝ → ℝ) (cPC CPC : ℝ)
    (CI : ChartInputs (truncSM G M) K Kidx t0 (max M 1) (2 * Kidx) U V cPC CPC)
    (_PI : ∀ ν, BulkPhaseInputs (frozenFamily (truncSM G M) Kidx) (paramSet K t0) K t0 (CI.lo ν) (CI.hi ν) M U V (CI.bulkL ν) (CI.bulkR ν)) : Prop :=
  Kidx = (M + 1) / 2 → ThmAi G K M ∧
  (IsCompact K → HypOn G K → DM G K M →
    ∀ (S S' : ℕ → Par → ℝ → ℝ) (δ δ' Cn Cn' hM hM' C C' : ℝ), 0 < δ → 0 < δ' →
      SmoothExt G K M S δ Cn → EigenRule G K M S hM C → SmoothExt G K M S' δ' Cn' → EigenRule G K M S' hM' C' →
        ∀ μ ∈ K, ∀ j ≤ M, ∀ X ∈ Set.Icc (G.bandLo μ) (G.bandHi μ), S j μ X = S' j μ X) ∧
  (IsCompact K → HypOn G K → DM G K M →
    ∀ (S S' : ℕ → Par → ℝ → ℝ) (δ δ' Cn Cn' hM C : ℝ), 0 < δ → 0 < δ' →
      SmoothExt G K M S δ Cn → EigenRule G K M S hM C → SmoothExt G K M S' δ' Cn' →
        (∀ μ ∈ K, ∀ j ≤ M, ∀ X ∈ Set.Icc (G.bandLo μ) (G.bandHi μ), S' j μ X = S j μ X) →
          ∃ hM' C' : ℝ, EigenRule G K M S' hM' C')

/-- **Assembly of `thm:smo-spec` / `thm:A (i)`**, for the charts of `tilde J_h`, modulo the named premises: `hstd` (`StdAssump` of the frozen family, F-S6-7), `hlabels`
(`BulkWindowLabels` of every block: the labels `k' = k`, from `PropThaW2` (3)/(4)), `hslope` (the slope of `S_0` on the blocks), the soft windows `WS` (`WindowPhase` of the two soft edges) and the cover
`hcov` of `[X_s^- - delta, X_s^+ + delta]` by blocks and soft windows with positive-length overlaps (F-S6-4). -/
theorem thmSmoSpecTrunc (G : SymbolFamily Par) (K : Set Par) (M Kidx : ℕ) (t0 : ℝ) (U V : ℝ → ℝ → ℝ) (cPC CPC : ℝ)
    (CI : ChartInputs (truncSM G M) K Kidx t0 (max M 1) (2 * Kidx) U V cPC CPC)
    (PI : ∀ ν, BulkPhaseInputs (frozenFamily (truncSM G M) Kidx) (paramSet K t0) K t0 (CI.lo ν) (CI.hi ν) M U V (CI.bulkL ν) (CI.bulkR ν))
    (ht0 : 0 < t0)
    (hstd : ∃ r, StdAssump (frozenFamily (truncSM G M) Kidx) (paramSet K t0) (max M 1 / 2) r)
    (hlabels : ∀ ν, BulkWindowLabels (frozenFamily (truncSM G M) Kidx) K t0 (CI.lo ν) (CI.hi ν))
    (hslope : ∀ ν, ∃ c : ℝ, 0 < c ∧ ∀ μ ∈ K, ∀ X ∈ Ioo (CI.lo ν) (CI.hi ν), deriv (fun X' => (PI ν).Sigma μ 0 X' 0) X ≤ -c)
    (aS bS : Bool → Par → ℝ) (WS : ∀ s : Bool, WindowPhase (truncSM G M) K t0 M (aS s) (bS s))
    (δ : ℝ) (hδ : 0 < δ)
    (hcov : WindowCover (truncSM G M) K (Sum.elim (fun ν _ => CI.lo ν) aS) (Sum.elim (fun ν _ => CI.hi ν) bS) δ)
    (hK : IsCompact K) (hH : HypOn G K) (hD : DM G K M) :
    ThmSmoSpecTrunc G K M Kidx t0 U V cPC CPC CI PI := by
  intro _
  have hDT := dm_truncSM G K M hD
  have hHT := hypOn_truncSM G K M hH
  obtain ⟨C1, h1, hC1, hh1, hpos1⟩ := smoSM_of_DM G K M hK hH hD
  have hposT : ∃ h1 : ℝ, 0 < h1 ∧ ∀ μ ∈ K, ∀ N : ℕ, (truncSM G M).step N ≤ h1 → ∀ n : ℤ, 0 ≤ n → n < N → 0 < (truncSM G M).bondA μ N n :=
    ⟨h1, hh1, fun μ hμ N hN n hn1 hn2 => ((hpos1 μ hμ N hN).1 n hn1 hn2).2⟩
  let W : ∀ i : Fin CI.nb ⊕ Bool, WindowPhase (truncSM G M) K t0 M (Sum.elim (fun ν _ => CI.lo ν) aS i) (Sum.elim (fun ν _ => CI.hi ν) bS i) :=
    fun i => match i with
      | Sum.inl ν => bulkPhaseWindow (PI ν) ht0 (CI.overlap_match ν) hstd (hlabels ν) hposT (hslope ν)
      | Sum.inr s => WS s
  obtain ⟨δ', Cn, C, hM, S, hδ', hsm, hact, hrule⟩ := thmAi_of_windows W ht0 hδ hcov hK hHT hDT
  obtain ⟨hM', C', hsm', hact', hrule'⟩ := thmAi_of_trunc G K M hK hH hD S δ' Cn hM C hδ' hsm hact hrule
  have hden := eigDensity_of_trunc G K M hK hH hD (density_of_windows W ht0 hδ hcov hK hHT (dm_zero_of_dm _ K M hK hDT))
  refine ⟨fun _ _ _ => ⟨δ', Cn, C', hM', S, hδ', hsm', hact', hrule'⟩, ?_, ?_⟩
  · exact thmSmoSpec_unique G K M hden (stepZeroD0 G K)
  · exact thmSmoSpec_extend G K M (stepZeroD0 G K)

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulkPhaseWindow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulkPhaseWindow

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmSmoSpecTrunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmSmoSpecTrunc

end FormalResearch.JacobiEigenvectors.TheoremA
