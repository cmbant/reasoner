module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Assembly.ThmA
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssemblyLower
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbFinal
public import FormalResearch.JacobiEigenvectors.Assembly.HeadlinesOfCore

/-!
# Paper J, assembly: gluing local charts over a finite cover of the parameter set

The charts of a family live on a parameter neighbourhood `K'` of a point (`local_cover_of_geom`, `Charts/LocalGeometry.lean`, gives one with its own
`t0, Jlo, Jhi`; the overlap `(c', c)` of a bulk block exists per energy and per neighbourhood, F-geom2).  This file turns charts on finitely many
compact pieces `K_i` of a compact `K` into the statements on `K`.

**Order of choices** (non-circular).  A chart is constructed at a point `mu_0` in this order: the soft fold `u_c`, the collar width `eta` and the window `delta_0`
(properties of the principal symbols at `mu_0`); then `local_cover_of_geom` with `delta_up = delta_lo = delta_0` gives `K'`, `t0`, `Jlo`, `Jhi`
(`ChartInputs.cover`); then the bulk blocks and the soft charts are built on `paramSet K' t0` with these constants (every chart field is an open condition in
`(mu, t)`, so it holds on a smaller `K'`).  Nothing in the cover depends on the chart beyond `delta_0`.

## Here

* `ChartInputs.restrictSet`, `SoftPhaseInputs.restrict`: restriction of chart inputs and soft phase inputs to a subset of the parameters (and, for `SoftPhaseInputs`,
  a smaller `t0`: the `C^{2M+1}` norm of the phase coefficients on the smaller rectangle is the same by `iteratedFDerivWithin_subset`).  So a chart on a
  neighbourhood restricts to a compact piece, and `softPhase_bandHi_close` can shrink `t0`.
* `exists_finite_compact_cover`: a compact `K` in a regular space, with a hereditary property `Loc` that holds near every point of `K`, is covered by finitely many
  compact `K_i ⊆ K` with `Loc K_i`.
* `thmAi_of_cover`: `ThmAi` on `K` from `ThmAi` on the pieces (the rule has no regularity in `mu`: constants combine by `min`/`max`, and the smooth
  extensions are restricted to the narrowest window).
* `ThmAiiCover`, `thmAii_of_cover`: `ThmAii` on `K` from charts `CI_i` on the pieces: uniform constants `C`, `h_m`, and for every `mu in K` one chart `i` containing it
  that gives the bounds.  `ThmBCover`, `thmB_of_cover`: the same for `ThmB` (chart pairs).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Set FormalResearch.JacobiEigenvectors.Setting

end FormalResearch.JacobiEigenvectors.Charts

namespace FormalResearch.JacobiEigenvectors.Setting

section Monotone

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K K' : Set Par}

theorem JetReg.mono_set {f : Par → ℝ → ℝ} {L : ℝ} {r : ℕ} (h : JetReg f K L r) (hK : K' ⊆ K) : JetReg f K' L r :=
  ⟨fun μ hμ => h.1 μ (hK hμ), fun i hi => (h.2 i hi).mono (Set.prod_mono hK subset_rfl)⟩

theorem HypOn.mono_set (h : HypOn F K) (hK : K' ⊆ K) : HypOn F K' :=
  let ⟨g, hg⟩ := h
  ⟨g, fun μ hμ => hg μ (hK hμ)⟩

theorem DM.mono_set {M : ℕ} (h : DM F K M) (hK : K' ⊆ K) : DM F K' M :=
  ⟨fun j hj => ⟨JetReg.mono_set (h.reg j hj).1 hK, JetReg.mono_set (h.reg j hj).2 hK⟩,
    let ⟨C, hC⟩ := h.rem
    ⟨C, fun μ hμ => hC μ (hK hμ)⟩⟩

end Monotone

end FormalResearch.JacobiEigenvectors.Setting

namespace FormalResearch.JacobiEigenvectors.Charts

open Set FormalResearch.JacobiEigenvectors.Setting

/-! ### Restriction to a subset of the parameters -/

lemma paramSet_mono_set {Par : Type*} {K K' : Set Par} (h : K' ⊆ K) (t0 : ℝ) : paramSet K' t0 ⊆ paramSet K t0 :=
  Set.prod_mono h subset_rfl

/-- **`ChartInputs.restrictSet`**: chart inputs on `paramSet K t0` restrict to `paramSet K' t0` for `K' ⊆ K` (same blocks, same constants). -/
def ChartInputs.restrictSet {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K K' : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ}
    {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ} (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (h : K' ⊆ K) :
    ChartInputs F K' Kidx t0 m q U V cPC CPC where
  pc := CI.pc
  Jlo := CI.Jlo
  Jhi := CI.Jhi
  nb := CI.nb
  lo := CI.lo
  hi := CI.hi
  bulkL := fun ν => (CI.bulkL ν).restrictSub (paramSet_mono_set h t0)
  bulkR := fun ν => (CI.bulkR ν).restrictSub (paramSet_mono_set h t0)
  softUpL := CI.softUpL.restrictSub (paramSet_mono_set h t0)
  softUpR := CI.softUpR.restrictSub (paramSet_mono_set h t0)
  softLoL := CI.softLoL.restrictSub (paramSet_mono_set h t0)
  softLoR := CI.softLoR.restrictSub (paramSet_mono_set h t0)
  overlap_match := CI.overlap_match
  mirror_up := ⟨fun p hp => CI.mirror_up.1 p (paramSet_mono_set h t0 hp), fun p hp => CI.mirror_up.2.1 p (paramSet_mono_set h t0 hp),
    fun r p hp => CI.mirror_up.2.2.1 r p (paramSet_mono_set h t0 hp), CI.mirror_up.2.2.2.1, CI.mirror_up.2.2.2.2.1, CI.mirror_up.2.2.2.2.2⟩
  mirror_lo := ⟨fun p hp => CI.mirror_lo.1 p (paramSet_mono_set h t0 hp), fun p hp => CI.mirror_lo.2.1 p (paramSet_mono_set h t0 hp),
    fun r p hp => CI.mirror_lo.2.2.1 r p (paramSet_mono_set h t0 hp), CI.mirror_lo.2.2.2.1, CI.mirror_lo.2.2.2.2.1, CI.mirror_lo.2.2.2.2.2⟩
  cover_bulk := CI.cover_bulk
  blocks_in_J := CI.blocks_in_J
  cover := fun p hp => CI.cover p (paramSet_mono_set h t0 hp)

/-- **`SoftPhaseInputs.restrict`**: the soft phase inputs restrict to a subset `K' ⊆ K` of the parameters and a smaller `0 < t0' <= t0` (for the restricted chart).  The norm bound
`Sigma_bdd` is the same on the smaller rectangle because the derivatives within a subset of a rectangle agree with those within the rectangle (`iteratedFDerivWithin_subset`; the phase
coefficients are `C^{2M+1}` on the rectangle, `softSigmaG_reg`). -/
def SoftPhaseInputs.restrict {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P P' : Set (Par × ℝ)} {K K' : Set Par}
    {t0 t0' : ℝ} {M m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ} {C : SoftEdgeChart Fz P m q U V Lm}
    (SI : SoftPhaseInputs Fz P K t0 M C) (hP : P' ⊆ P) (hK : K' ⊆ K) (ht0' : 0 < t0') (ht : t0' ≤ t0) :
    SoftPhaseInputs Fz P' K' t0' M (C.restrictSub hP) where
  w := SI.w
  ρ := SI.ρ
  w_pos := SI.w_pos
  ρ_nonneg := SI.ρ_nonneg
  window_in_chart := SI.window_in_chart
  bandHi_close := fun μ hμ t htt => SI.bandHi_close μ (hK hμ) t ⟨by linarith [htt.1], by linarith [htt.2]⟩
  bandHi_reg := fun μ hμ => (SI.bandHi_reg μ (hK hμ)).mono (Icc_subset_Icc (by linarith) ht)
  muS_reg := fun μ hμ r hr => (SI.muS_reg μ (hK hμ) r hr).mono (Set.prod_mono subset_rfl (Icc_subset_Icc (by linarith) ht))
  Sigma_bdd := by
    obtain ⟨Cb, hCb⟩ := SI.Sigma_bdd
    refine ⟨Cb, fun μ hμ j hj i hi p hp => ?_⟩
    have hsub : Icc (Fz.bandHi (μ, 0) - SI.w) (Fz.bandHi (μ, 0) + SI.w) ×ˢ Icc (-t0') t0' ⊆
        Icc (Fz.bandHi (μ, 0) - SI.w) (Fz.bandHi (μ, 0) + SI.w) ×ˢ Icc (-t0) t0 :=
      Set.prod_mono subset_rfl (Icc_subset_Icc (by linarith) ht)
    have hw : Fz.bandHi (μ, 0) - SI.w < Fz.bandHi (μ, 0) + SI.w := by linarith [SI.w_pos]
    have hU' := (uniqueDiffOn_Icc hw).prod (uniqueDiffOn_Icc (by linarith : -t0' < t0'))
    have hU := (uniqueDiffOn_Icc hw).prod (uniqueDiffOn_Icc (by linarith : -t0 < t0))
    have hreg : ContDiffOn ℝ (i : WithTop ℕ∞) (fun q : ℝ × ℝ => softSigma C μ j q.1 q.2)
        (Icc (Fz.bandHi (μ, 0) - SI.w) (Fz.bandHi (μ, 0) + SI.w) ×ˢ Icc (-t0) t0) :=
      (TheoremA.softSigmaG_reg SI (hK hμ) hj).of_le (by exact_mod_cast hi)
    show ‖iteratedFDerivWithin ℝ i (fun q : ℝ × ℝ => softSigma C μ j q.1 q.2)
      (Icc (Fz.bandHi (μ, 0) - SI.w) (Fz.bandHi (μ, 0) + SI.w) ×ˢ Icc (-t0') t0') p‖ ≤ Cb
    rw [iteratedFDerivWithin_subset hsub hU' hU hreg hp]
    exact hCb μ (hK hμ) j hj i hi p (hsub hp)

/-! ### Finite compact cover -/

/-- **A finite cover by compact pieces with a hereditary local property.**  If `K` is compact in a regular space and every point of `K` has a neighbourhood `K'` in `K` with
`Loc K'`, where `Loc` passes to subsets, then finitely many compact `K_i ⊆ K` with `Loc K_i` cover `K`. -/
theorem exists_finite_compact_cover {Par : Type*} [TopologicalSpace Par] [RegularSpace Par] {K : Set Par} (hK : IsCompact K)
    (Loc : Set Par → Prop) (hmono : ∀ A B : Set Par, B ⊆ A → Loc A → Loc B)
    (hloc : ∀ μ ∈ K, ∃ K' ∈ nhdsWithin μ K, Loc K') :
    ∃ s : Finset Par, ∃ Kα : Par → Set Par, (∀ i ∈ s, IsCompact (Kα i) ∧ Kα i ⊆ K ∧ Loc (Kα i)) ∧ K ⊆ ⋃ i ∈ s, Kα i := by
  have hex : ∀ μ ∈ K, ∃ C : Set Par, C ∈ nhds μ ∧ IsClosed C ∧ Loc (K ∩ C) := by
    intro μ hμ
    obtain ⟨K', hK', hL⟩ := hloc μ hμ
    obtain ⟨V, hVo, hμV, hVK⟩ := mem_nhdsWithin.mp hK'
    obtain ⟨C, hCn, hCc, hCV⟩ := exists_mem_nhds_isClosed_subset (hVo.mem_nhds hμV)
    exact ⟨C, hCn, hCc, hmono K' _ (fun x hx => hVK ⟨hCV hx.2, hx.1⟩) hL⟩
  choose! C hCn hCc hLoc using hex
  obtain ⟨s, hsK, hcov⟩ := hK.elim_nhds_subcover C (fun x hx => hCn x hx)
  refine ⟨s, fun i => K ∩ C i, fun i hi => ⟨hK.inter_right (hCc i (hsK i hi)), inter_subset_left, hLoc i (hsK i hi)⟩, fun μ hμ => ?_⟩
  have := hcov hμ
  simp only [mem_iUnion] at this ⊢
  obtain ⟨i, hi, h⟩ := this
  exact ⟨i, hi, hμ, h⟩

theorem step_nonneg' {Par : Type*} (F : SymbolFamily Par) (N : ℕ) : 0 ≤ F.step N :=
  (FormalResearch.JB.stepSize_pos F.L_pos N).le

/-! ### Uniform constants over a finite index set -/

theorem exists_const_ge {ι : Type*} [Finite ι] (C : ι → ℝ) : ∃ M : ℝ, ∀ i, C i ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range C).bddAbove
  exact ⟨M, fun i => hM ⟨i, rfl⟩⟩

theorem exists_pos_le {ι : Type*} [Finite ι] (h : ι → ℝ) (hp : ∀ i, 0 < h i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ h i := by
  obtain ⟨M, hM⟩ := exists_const_ge (fun i => (h i)⁻¹)
  refine ⟨(max M 1)⁻¹, inv_pos.2 (lt_max_of_lt_right one_pos), fun i => ?_⟩
  have h1 : (h i)⁻¹ ≤ max M 1 := (hM i).trans (le_max_left _ _)
  calc (max M 1)⁻¹ ≤ ((h i)⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 (hp i)) h1
    _ = h i := inv_inv _

/-! ### `ThmAi` on a finite cover -/

open FormalResearch.JacobiEigenvectors.TheoremA in
/-- **`ThmAi` from `ThmAi` on a finite cover by compact pieces.**  The rule `EigenRule` is uniform in `mu` and `S` is not required to be regular in `mu`, so the pieces' families
`S_i` combine (`S mu := S_i mu` for a piece containing `mu`) with the constants `min`/`max` over the pieces; the smooth extensions are restricted to the narrowest window. -/
theorem thmAi_of_cover {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {M : ℕ} {ι : Type*} [Finite ι]
    {Kα : ι → Set Par} (hcov : K ⊆ ⋃ i, Kα i) (hsub : ∀ i, Kα i ⊆ K) (hcpt : ∀ i, IsCompact (Kα i))
    (h : ∀ i, ThmAi F (Kα i) M) : ThmAi F K M := by
  intro hK hH hD
  choose δ Cn C hM S hδ hSm hAct hEig using fun i => h i (hcpt i) (hH.mono_set (hsub i)) (hD.mono_set (hsub i))
  obtain ⟨δm, hδm, hδle⟩ := exists_pos_le δ hδ
  obtain ⟨Cnm, hCnm⟩ := exists_const_ge Cn
  obtain ⟨Cm, hCm⟩ := exists_const_ge C
  obtain ⟨hm, hhm, hhle⟩ := exists_pos_le hM (fun i => (hEig i).1)
  classical
  let S' : ℕ → Par → ℝ → ℝ := fun j μ =>
    if hex : ∃ i, μ ∈ Kα i then S (Classical.choose hex) j μ else fun _ => 0
  have hS' : ∀ μ ∈ K, ∃ i, μ ∈ Kα i ∧ ∀ j, S' j μ = S i j μ := by
    intro μ hμ
    have hex : ∃ i, μ ∈ Kα i := mem_iUnion.mp (hcov hμ)
    exact ⟨Classical.choose hex, Classical.choose_spec hex, fun j => by simp only [S', dif_pos hex]⟩
  refine ⟨δm, Cnm, Cm, hm, S', hδm, ?_, ?_, ?_⟩
  · intro μ hμ j hj
    obtain ⟨i, hi, hSi⟩ := hS' μ hμ
    obtain ⟨hd, hb⟩ := hSm i μ hi j hj
    rw [hSi j]
    have hsubI : Icc (F.bandLo μ - δm) (F.bandHi μ + δm) ⊆ Icc (F.bandLo μ - δ i) (F.bandHi μ + δ i) :=
      Icc_subset_Icc (by linarith [hδle i]) (by linarith [hδle i])
    refine ⟨hd.mono hsubI, fun n hn x hx => ?_⟩
    have hlt := bandLo_lt_bandHi F K M hH hD μ hμ
    have hU' := uniqueDiffOn_Icc (by linarith : F.bandLo μ - δm < F.bandHi μ + δm)
    have hU := uniqueDiffOn_Icc (by linarith [hδ i] : F.bandLo μ - δ i < F.bandHi μ + δ i)
    have hreg : ContDiffOn ℝ (n : WithTop ℕ∞) (S i j μ) (Icc (F.bandLo μ - δ i) (F.bandHi μ + δ i)) :=
      hd.of_le (by exact_mod_cast hn)
    have heq : iteratedDerivWithin n (S i j μ) (Icc (F.bandLo μ - δm) (F.bandHi μ + δm)) x =
        iteratedDerivWithin n (S i j μ) (Icc (F.bandLo μ - δ i) (F.bandHi μ + δ i)) x := by
      rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin,
        iteratedFDerivWithin_subset hsubI hU' hU hreg hx]
    rw [heq]
    exact (hb n hn x (hsubI hx)).trans (hCnm i)
  · intro μ hμ X hX
    obtain ⟨i, hi, hSi⟩ := hS' μ hμ
    rw [hSi 0]
    exact hAct i μ hi X hX
  · refine ⟨hhm, fun μ hμ N hN X Um hE k => ?_⟩
    obtain ⟨i, hi, hSi⟩ := hS' μ hμ
    simp only [hSi]
    exact ((hEig i).2 μ hi N (hN.trans (hhle i)) X Um hE k).trans
      (mul_le_mul_of_nonneg_right (hCm i) (pow_nonneg (step_nonneg' F N) _))

/-! ### `ThmAii`, `ThmB` on a finite cover -/

/-- A finite family of pairs `(C, h)` with a property monotone in `C` and (below `t i`) in `h` has a common pair. -/
theorem glue_pair {ι : Type*} [Finite ι] (R : ι → ℝ → ℝ → Prop) (t : ι → ℝ) (ht : ∀ i, 0 < t i)
    (hmono : ∀ i C C' h h', C ≤ C' → h' ≤ h → h' ≤ t i → R i C h → R i C' h')
    (h : ∀ i, ∃ C hm : ℝ, 0 < hm ∧ R i C hm) :
    ∃ C hm : ℝ, 0 < hm ∧ (∀ i, hm ≤ t i) ∧ ∀ i, R i C hm := by
  choose C hm hp hR using h
  obtain ⟨M, hM⟩ := exists_const_ge C
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le (fun i => min (hm i) (t i)) (fun i => lt_min (hp i) (ht i))
  exact ⟨M, δ, hδ, fun i => (hδle i).trans (min_le_right _ _), fun i =>
    hmono i (C i) M (hm i) δ (hM i) ((hδle i).trans (min_le_left _ _)) ((hδle i).trans (min_le_right _ _)) (hR i)⟩

open FormalResearch.JacobiEigenvectors.TheoremA in
/-- **`ThmAii` on a finite cover** (the statement): the constants `C`, `h_m` (and `C_eps`, `h_eps`) are uniform over `K`; every `mu in K` is assigned one piece `pick mu` containing it, and the *same*
chart `CI (pick mu)` (hence the same vector `psiHat`) gives both the `h^m` bound and the relative clause for every `eps`, as in the paper. -/
def ThmAiiCover {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) (m Kidx : ℕ) (U V : ℝ → ℝ → ℝ) (cPC CPC : ℝ)
    {ι : Type*} (Kα : ι → Set Par) (t0α : ι → ℝ) (CI : ∀ i, ChartInputs F (Kα i) Kidx (t0α i) m (2 * Kidx) U V cPC CPC) : Prop :=
  1 ≤ m → Kidx = (m + 1) / 2 → IsCompact K → HypOn F K → DM F K (2 * ((m + 1) / 2) + 1) →
    ∃ pick : (μ : Par) → μ ∈ K → ι, (∀ μ (hμ : μ ∈ K), μ ∈ Kα (pick μ hμ)) ∧
    (∃ C hm : ℝ, 0 < hm ∧ ∀ μ (hμ : μ ∈ K), ∀ N : ℕ, F.step N ≤ hm →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (∀ n ∈ rowsOf N, |eigVec Um k n - psiHatVec (CI (pick μ hμ)) μ N (X k) n| ≤
            C * F.step N ^ m * envVec (CI (pick μ hμ)) μ N (X k) n) ∧
          ∑ n ∈ rowsOf N, envVec (CI (pick μ hμ)) μ N (X k) n ^ 2 ≤ C) ∧
    (∀ ε : ℝ, 0 < ε → ∃ Cε hε : ℝ, 0 < hε ∧ ∀ μ (hμ : μ ∈ K), ∀ N : ℕ, F.step N ≤ hε →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), ∀ n ∈ rowsOf N,
          Tfun F.L (F.G 0 μ) (F.B 0 μ) (X k) (uNode (F.step N) n) ≤ -ε →
            envVec (CI (pick μ hμ)) μ N (X k) n ≤ Cε * |psiHatVec (CI (pick μ hμ)) μ N (X k) n|)

open FormalResearch.JacobiEigenvectors.TheoremA in
/-- **`ThmAii` from `ThmAii` on the pieces of a finite cover** (`thmAii_proved` on each piece: the charts `CI i` are those of the pieces, `0 < t0α i`). -/
theorem thmAii_of_cover {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {m Kidx : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    {ι : Type*} [Finite ι] {Kα : ι → Set Par} {t0α : ι → ℝ} (CI : ∀ i, ChartInputs F (Kα i) Kidx (t0α i) m (2 * Kidx) U V cPC CPC)
    (ht0 : ∀ i, 0 < t0α i) (hcov : K ⊆ ⋃ i, Kα i) (hsub : ∀ i, Kα i ⊆ K) (hcpt : ∀ i, IsCompact (Kα i))
    (h : ∀ i, ThmAii F (Kα i) m Kidx (t0α i) U V cPC CPC (CI i)) :
    ThmAiiCover F K m Kidx U V cPC CPC Kα t0α CI := by
  intro hm1 hK hKc hH hD
  have hloc := fun i => h i hm1 hK (hcpt i) (hH.mono_set (hsub i)) (hD.mono_set (hsub i))
  choose hn hnp hnnv using fun i => envVec_nonneg (CI i)
  choose pick hpick using fun μ (hμ : μ ∈ K) => mem_iUnion.mp (hcov hμ)
  refine ⟨pick, hpick, ?_, fun ε hε => ?_⟩
  · obtain ⟨C, hm, hmp, hmle, hR⟩ := glue_pair
      (fun i C hh => ∀ μ ∈ Kα i, ∀ N : ℕ, F.step N ≤ hh → F.step N ≤ t0α i →
        ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
          ∀ k : Fin (N + 1), (∀ n ∈ rowsOf N, |eigVec Um k n - psiHatVec (CI i) μ N (X k) n| ≤ C * F.step N ^ m * envVec (CI i) μ N (X k) n) ∧
            ∑ n ∈ rowsOf N, envVec (CI i) μ N (X k) n ^ 2 ≤ C)
      (fun i => min (t0α i) (hn i)) (fun i => lt_min (ht0 i) (hnp i))
      (fun i C C' hh hh' hCC hhh hht hR μ hμ N hN hN' X Um hE k => by
        obtain ⟨hb, hs⟩ := hR μ hμ N (hN.trans hhh) hN' X Um hE k
        refine ⟨fun n hn => (hb n hn).trans ?_, hs.trans hCC⟩
        have hen := hnnv i μ hμ N (hN.trans (hht.trans (min_le_right _ _))) hN' (X k) n hn
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC (pow_nonneg (step_nonneg' F N) m)) hen)
      (fun i => by
        obtain ⟨⟨C, hm, hmp, hh⟩, _⟩ := hloc i
        exact ⟨C, hm, hmp, hh⟩)
    refine ⟨C, hm, hmp, fun μ hμ N hN X Um hE k => ?_⟩
    exact hR (pick μ hμ) μ (hpick μ hμ) N hN (hN.trans ((hmle _).trans (min_le_left _ _))) X Um hE k
  · obtain ⟨C, hm, hmp, hmle, hR⟩ := glue_pair
      (fun i C hh => ∀ μ ∈ Kα i, ∀ N : ℕ, F.step N ≤ hh → F.step N ≤ t0α i →
        ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
          ∀ k : Fin (N + 1), ∀ n ∈ rowsOf N, Tfun F.L (F.G 0 μ) (F.B 0 μ) (X k) (uNode (F.step N) n) ≤ -ε →
            envVec (CI i) μ N (X k) n ≤ C * |psiHatVec (CI i) μ N (X k) n|)
      t0α ht0
      (fun i C C' hh hh' hCC hhh hht hR μ hμ N hN hN' X Um hE k n hn hT =>
        (hR μ hμ N (hN.trans hhh) hN' X Um hE k n hn hT).trans
          (mul_le_mul_of_nonneg_right hCC (abs_nonneg _)))
      (fun i => by
        obtain ⟨_, hB⟩ := hloc i
        exact hB ε hε)
    refine ⟨C, hm, hmp, fun μ hμ N hN X Um hE k n hn hT => ?_⟩
    exact hR (pick μ hμ) μ (hpick μ hμ) N hN (hN.trans (hmle _)) X Um hE k n hn hT

end FormalResearch.JacobiEigenvectors.Charts

namespace FormalResearch.JacobiEigenvectors.TheoremA.HypMorse

open FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

theorem FrozenReg.mono_set {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K K' : Set Par} {Kidx r : ℕ}
    (h : FrozenReg F K Kidx r) (hK : K' ⊆ K) : FrozenReg F K' Kidx r :=
  ⟨h.budget, fun j hj => ⟨JetReg.mono_set (h.reg j hj).1 hK, JetReg.mono_set (h.reg j hj).2.1 hK,
      JetReg.mono_set (h.reg j hj).2.2.1 hK, JetReg.mono_set (h.reg j hj).2.2.2 hK⟩,
    let ⟨C, hC⟩ := h.rem
    ⟨C, fun μ hμ => hC μ (hK hμ)⟩⟩

end FormalResearch.JacobiEigenvectors.TheoremA.HypMorse

namespace FormalResearch.JacobiEigenvectors.TheoremB

open FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

theorem StdDM.mono_set {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K K' : Set Par} {Kidx : ℕ}
    (h : StdDM F K Kidx) (hK : K' ⊆ K) : StdDM F K' Kidx :=
  ⟨h.d1.mono_set hK, let ⟨r, hr⟩ := h.frozen; ⟨r, hr.mono_set hK⟩⟩

end FormalResearch.JacobiEigenvectors.TheoremB

namespace FormalResearch.JacobiEigenvectors.Charts

open Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.TheoremA FormalResearch.JacobiEigenvectors.TheoremB
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix

/-- The conclusion of `ThmB` for the constants `C`, `hh` (the part of `ThmB` after the constants), on the parameter set `K` of the chart pair. -/
def ThmBBound {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) (C hh : ℝ) : Prop :=
  ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hh → F.step N ≤ t0 →
    ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
      ‖compMatrix CP.CI0 spl μ N Xs - Um‖ ≤ C * F.step N ^ m ∧
      (compMatrix CP.CI0 spl μ N Xs * (CFC.sqrt ((compMatrix CP.CI0 spl μ N Xs)ᵀ * compMatrix CP.CI0 spl μ N Xs))⁻¹)ᵀ *
          (compMatrix CP.CI0 spl μ N Xs * (CFC.sqrt ((compMatrix CP.CI0 spl μ N Xs)ᵀ * compMatrix CP.CI0 spl μ N Xs))⁻¹) = 1 ∧
      ‖compMatrix CP.CI0 spl μ N Xs * (CFC.sqrt ((compMatrix CP.CI0 spl μ N Xs)ᵀ * compMatrix CP.CI0 spl μ N Xs))⁻¹ - Um‖
        ≤ 2 * C * F.step N ^ m

theorem ThmBBound.mono {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    {CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC)}
    {spl : Fin CP.CI0.nb → ℝ} {C C' hh hh' : ℝ} (hCC : C ≤ C') (hhh : hh' ≤ hh) (h : ThmBBound CP spl C hh) : ThmBBound CP spl C' hh' := by
  intro μ hμ N hN hN' Xs Um hE
  obtain ⟨h1, h2, h3⟩ := h μ hμ N (hN.trans hhh) hN' Xs Um hE
  have hs := pow_nonneg (step_nonneg' F N) m
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right hCC hs), h2,
    h3.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCC two_pos.le) hs)⟩

/-- **`ThmB` on a finite cover** (the statement): constants `C`, `h_m` uniform over `K` with `C h_m^m < 1`; every `mu in K` lies in a piece `i` whose chart pair `CP i` gives the bounds. -/
def ThmBCover {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) (m q Kidx : ℕ) (U V : ℝ → ℝ → ℝ) (cPC CPC : ℝ)
    {ι : Type*} (Kα : ι → Set Par) (t0α : ι → ℝ)
    (CP : ∀ i, ChartPair (F := F) (K := Kα i) (Kidx := Kidx) (t0 := t0α i) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : ∀ i, Fin (CP i).CI0.nb → ℝ) : Prop :=
  1 ≤ m → Kidx = (m + 1) / 2 → q = 2 * Kidx → IsCompact K → HypOn F K → StdDM F K Kidx → (∀ i, (CP i).SplicesInWindow (spl i)) →
    ∃ C hm : ℝ, 0 < hm ∧ C * hm ^ m < 1 ∧ ∀ μ ∈ K, ∃ i, μ ∈ Kα i ∧ ∀ N : ℕ, F.step N ≤ hm →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ‖compMatrix (CP i).CI0 (spl i) μ N Xs - Um‖ ≤ C * F.step N ^ m ∧
        (compMatrix (CP i).CI0 (spl i) μ N Xs * (CFC.sqrt ((compMatrix (CP i).CI0 (spl i) μ N Xs)ᵀ * compMatrix (CP i).CI0 (spl i) μ N Xs))⁻¹)ᵀ *
            (compMatrix (CP i).CI0 (spl i) μ N Xs * (CFC.sqrt ((compMatrix (CP i).CI0 (spl i) μ N Xs)ᵀ * compMatrix (CP i).CI0 (spl i) μ N Xs))⁻¹) = 1 ∧
        ‖compMatrix (CP i).CI0 (spl i) μ N Xs * (CFC.sqrt ((compMatrix (CP i).CI0 (spl i) μ N Xs)ᵀ * compMatrix (CP i).CI0 (spl i) μ N Xs))⁻¹ - Um‖
          ≤ 2 * C * F.step N ^ m

/-- **`ThmB` from `ThmB` on the pieces of a finite cover** (`thmB_proved` on each piece, with its transfer bundle). -/
theorem thmB_of_cover {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {m q Kidx : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    {ι : Type*} [Finite ι] {Kα : ι → Set Par} {t0α : ι → ℝ}
    (CP : ∀ i, ChartPair (F := F) (K := Kα i) (Kidx := Kidx) (t0 := t0α i) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : ∀ i, Fin (CP i).CI0.nb → ℝ)
    (ht0 : ∀ i, 0 < t0α i) (hcov : K ⊆ ⋃ i, Kα i) (hsub : ∀ i, Kα i ⊆ K) (hcpt : ∀ i, IsCompact (Kα i))
    (h : ∀ i, ThmB (CP i) (spl i)) : ThmBCover F K m q Kidx U V cPC CPC Kα t0α CP spl := by
  intro hm1 hK hq hKc hH hD hspl
  have hloc := fun i => h i hm1 hK hq (hcpt i) (hH.mono_set (hsub i)) (hD.mono_set (hsub i)) (hspl i)
  obtain ⟨C, hm, hmp, hmle, hR⟩ := glue_pair (fun i C hh => ThmBBound (CP i) (spl i) C hh) t0α ht0
    (fun i C C' hh hh' hCC hhh _ hR => ThmBBound.mono hCC hhh hR)
    (fun i => by
      obtain ⟨C, hm, hmp, _, hh⟩ := hloc i
      exact ⟨C, hm, hmp, hh⟩)
  set C2 : ℝ := max C 0 with hC2
  have hC2n : 0 ≤ C2 := le_max_right _ _
  set hm2 : ℝ := min hm (min 1 (C2 + 1)⁻¹) with hhm2
  have hinv : 0 < (C2 + 1)⁻¹ := inv_pos.2 (by linarith)
  have hm2p : 0 < hm2 := lt_min hmp (lt_min one_pos hinv)
  have hm2le1 : hm2 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hm2le : hm2 ≤ (C2 + 1)⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C2, hm2, hm2p, ?_, fun μ hμ => ?_⟩
  · calc C2 * hm2 ^ m ≤ C2 * hm2 := mul_le_mul_of_nonneg_left (pow_le_of_le_one hm2p.le hm2le1 (by omega)) hC2n
      _ ≤ C2 * (C2 + 1)⁻¹ := mul_le_mul_of_nonneg_left hm2le hC2n
      _ < 1 := by rw [← div_eq_mul_inv]; exact (div_lt_one (by linarith)).2 (by linarith)
  · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hμ)
    have hb : ThmBBound (CP i) (spl i) C2 hm2 := ThmBBound.mono (le_max_left C 0) (min_le_left hm _) (hR i)
    exact ⟨i, hi, fun N hN Xs Um hE => hb μ hi N hN (hN.trans ((min_le_left hm _).trans (hmle i))) Xs Um hE⟩

/-! ### The headlines from local charts -/

open FormalResearch.JacobiEigenvectors.TheoremA in
/-- **thm:A (ii) from local charts**: if every point of the compact `K` has a neighbourhood `K'` in `K` carrying chart inputs on `paramSet K' t0` (some `t0 > 0`), then `ThmAii` holds on `K`
in the glued form `ThmAiiCover` for a finite cover by compact pieces with their charts.  No premise beyond the statement's own. -/
theorem thmAii_of_local_charts {Par : Type u_1} [TopologicalSpace Par] [RegularSpace Par] {F : SymbolFamily Par} {K : Set Par} {m Kidx : ℕ}
    {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ} (hK : IsCompact K)
    (hloc : ∀ μ ∈ K, ∃ K' ∈ nhdsWithin μ K, ∃ t0 : ℝ, 0 < t0 ∧ Nonempty (ChartInputs F K' Kidx t0 m (2 * Kidx) U V cPC CPC)) :
    ∃ (ι : Type u_1) (_ : Finite ι) (Kα : ι → Set Par) (t0α : ι → ℝ) (CI : ∀ i, ChartInputs F (Kα i) Kidx (t0α i) m (2 * Kidx) U V cPC CPC),
      ThmAiiCover F K m Kidx U V cPC CPC Kα t0α CI := by
  obtain ⟨s, Kα, hs, hcov⟩ := exists_finite_compact_cover hK
    (fun A => ∃ t0 : ℝ, 0 < t0 ∧ Nonempty (ChartInputs F A Kidx t0 m (2 * Kidx) U V cPC CPC))
    (fun A B hBA ⟨t0, ht0, ⟨CI⟩⟩ => ⟨t0, ht0, ⟨CI.restrictSet hBA⟩⟩) hloc
  choose t0α ht0 hCI using fun i : s => (hs i i.2).2.2
  refine ⟨s, inferInstance, fun i => Kα i, t0α, fun i => (hCI i).some, thmAii_of_cover _ ht0 ?_ (fun i => (hs i i.2).2.1)
    (fun i => (hs i i.2).1) (fun i => thmAii_proved _)⟩
  intro μ hμ
  have := hcov hμ
  simp only [mem_iUnion] at this ⊢
  obtain ⟨i, hi, h⟩ := this
  exact ⟨⟨i, hi⟩, h⟩

open FormalResearch.JacobiEigenvectors.TheoremA in
/-- **thm:A (ii) from local cores**: the same with chart cores `ChartCores` (the charts are `ChartInputs.ofCore`). -/
theorem thmAii_of_local_cores {Par : Type u_1} [TopologicalSpace Par] [RegularSpace Par] {F : SymbolFamily Par} {K : Set Par} {m Kidx : ℕ}
    (hK : IsCompact K)
    (hloc : ∀ μ ∈ K, ∃ K' ∈ nhdsWithin μ K, ∃ t0 : ℝ, 0 < t0 ∧ Nonempty (ChartCores F K' Kidx t0 m (2 * Kidx))) :
    ∃ (ι : Type u_1) (_ : Finite ι) (Kα : ι → Set Par) (t0α : ι → ℝ) (CI : ∀ i, ChartInputs F (Kα i) Kidx (t0α i) m (2 * Kidx) pcU pcV pcCs.1 pcCs.2),
      ThmAiiCover F K m Kidx pcU pcV pcCs.1 pcCs.2 Kα t0α CI :=
  thmAii_of_local_charts hK fun μ hμ => by
    obtain ⟨K', hK', t0, ht0, ⟨D⟩⟩ := hloc μ hμ
    exact ⟨K', hK', t0, ht0, ⟨ChartInputs.ofCore D⟩⟩

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.thmAi_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.thmAi_of_cover

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.thmAii_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.thmAii_of_cover

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.thmB_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.thmB_of_cover

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.thmAii_of_local_cores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.thmAii_of_local_cores

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.SoftPhaseInputs.restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.SoftPhaseInputs.restrict

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.exists_finite_compact_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.exists_finite_compact_cover

end FormalResearch.JacobiEigenvectors.Charts
