module

public import FormalResearch.JacobiEigenvectors.Setting.JacobiFamily
public import FormalResearch.JacobiEigenvectors.Charts.BulkWeber
public import FormalResearch.JacobiEigenvectors.Charts.SoftParabolicCylinder
public import FormalResearch.JacobiEigenvectors.Charts.SoftPhaseInputs
public import FormalResearch.JacobiEigenvectors.Charts.ChartInputs
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZeroCore
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZero
public import FormalResearch.JacobiEigenvectors.TheoremA.BandFacts
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometryStatements
public import FormalResearch.JacobiEigenvectors.TheoremA.Geometry

/-!
# Local parameter cover, bulk block cover, mirror symmetries, and cover constants (WP2)

Layer-4 proofs for the parameter-localisation and mirror-symmetry chart obligations:
* `local_cover_of_geom_strict` / `local_cover_of_geom`: local parameter neighbourhood `K' ∈ 𝓝[K] μ0`,
  freezing radius `t0 > 0`, and uniform compact bulk energy interval `[Jlo, Jhi] ⊂ (X_s^-, X_s^+)`
  covered by the soft windows `(Jhi + δup, Jlo - δlo)`.
* `local_bulk_cover_of_geom`: uniform finite cover of `[Jlo, Jhi]` by blocks `[lo ν, hi ν]` with
  strict overlaps `c' ν < c ν` inside `(u_-, u_+)` (`overlap_in_well`) and uniform phase margin
  `theta_margin`.
* `uMinus_mirror_ne`, `uPlus_mirror_ne`, `mirror_bulk_overlap_match`: mirror formulas
  `(mirrorFamily F).uMinus = L - F.uPlus` and `(mirrorFamily F).uPlus = L - F.uMinus` on
  nonempty allowed sets, and transfer of `overlap_in_well`, `theta_margin`, and `overlap_match`
  (`c_R = L - c'`, `c'_R = L - c`).
* `softMirror_geom_of_left`: geometric `SoftMirror` identities (`uc_spec`, `ucη_in`, `geom_far`,
  `zeta_deriv`, `zeta_zero`, `zeta_alpha`, `zeta_far`, `zeta_far_out`, `zeta_sign_out`, `zeta_T`)
  for `mirrorFamily F`.
* `softPhase_bandHi_close`: joint continuity of `(frozenFamily F Kidx).bandHi` giving `t0 > 0`
  for `SoftPhaseInputs.bandHi_close`.
* `layer4_cover_consts`: elementary construction of the uniform cover constants matching
  `Layer4Inputs` (`hw`, `hlt`, `hJhi`, `hJlo`, `hwb`, `hKidx`).

No placeholders and no non-standard axioms.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Set Filter Topology
open FormalResearch.JacobiEigenvectors.Setting
open FormalResearch.JacobiEigenvectors.TheoremA

/-! ### 1. Local cover (`local_cover_of_geom`) -/

lemma frozen_bandHi_eq {Par : Type*} (F : SymbolFamily Par) (Kidx : ℕ) :
    (frozenFamily F Kidx).bandHi = (frozenFamily F 0).bandHi := by
  funext p
  unfold SymbolFamily.bandHi
  have hG : (frozenFamily F Kidx).G 0 p = (frozenFamily F 0).G 0 p := by
    funext s; simp [frozenFamily]
  have hB : (frozenFamily F Kidx).B 0 p = (frozenFamily F 0).B 0 p := by
    funext s; simp [frozenFamily]
  rw [hG, hB]; rfl

lemma frozen_bandLo_eq {Par : Type*} (F : SymbolFamily Par) (Kidx : ℕ) :
    (frozenFamily F Kidx).bandLo = (frozenFamily F 0).bandLo := by
  funext p
  unfold SymbolFamily.bandLo
  have hG : (frozenFamily F Kidx).G 0 p = (frozenFamily F 0).G 0 p := by
    funext s; simp [frozenFamily]
  have hB : (frozenFamily F Kidx).B 0 p = (frozenFamily F 0).B 0 p := by
    funext s; simp [frozenFamily]
  rw [hG, hB]; rfl

lemma frozen_bandHi_zero {Par : Type*} (F : SymbolFamily Par) (Kidx : ℕ) (μ : Par) :
    (frozenFamily F Kidx).bandHi (μ, 0) = F.bandHi μ := by
  unfold SymbolFamily.bandHi
  have hG : (frozenFamily F Kidx).G 0 (μ, 0) = F.G 0 μ := by
    funext s; simp [frozenFamily]
  have hB : (frozenFamily F Kidx).B 0 (μ, 0) = F.B 0 μ := by
    funext s; simp [frozenFamily]
  rw [hG, hB]; rfl

lemma frozen_bandLo_zero {Par : Type*} (F : SymbolFamily Par) (Kidx : ℕ) (μ : Par) :
    (frozenFamily F Kidx).bandLo (μ, 0) = F.bandLo μ := by
  unfold SymbolFamily.bandLo
  have hG : (frozenFamily F Kidx).G 0 (μ, 0) = F.G 0 μ := by
    funext s; simp [frozenFamily]
  have hB : (frozenFamily F Kidx).B 0 (μ, 0) = F.B 0 μ := by
    funext s; simp [frozenFamily]
  rw [hG, hB]; rfl

private lemma frozen_bandHi_contOn {Par : Type*} [TopologicalSpace Par]
    (F : SymbolFamily Par) {K : Set Par} (hK : IsCompact K) {Kidx : ℕ}
    (hD : DM F K (2 * Kidx + 1)) :
    ContinuousOn (frozenFamily F Kidx).bandHi (paramSet K 1) := by
  have hP1 : IsCompact (paramSet K 1) := hK.prod isCompact_Icc
  have hR : CoreReg (frozenFamily F Kidx) (paramSet K 1) 2 :=
    coreReg_of_EK hP1 (HypMorse.EK_frozen_of_reg 1 (HypMorse.frozenReg_of_dm hD))
  exact continuousOn_iff_continuous_restrict.mpr hR.contBandHi

private lemma frozen_bandLo_contOn {Par : Type*} [TopologicalSpace Par]
    (F : SymbolFamily Par) {K : Set Par} (hK : IsCompact K) {Kidx : ℕ}
    (hD : DM F K (2 * Kidx + 1)) :
    ContinuousOn (frozenFamily F Kidx).bandLo (paramSet K 1) := by
  have hP1 : IsCompact (paramSet K 1) := hK.prod isCompact_Icc
  have hR : CoreReg (frozenFamily F Kidx) (paramSet K 1) 2 :=
    coreReg_of_EK hP1 (HypMorse.EK_frozen_of_reg 1 (HypMorse.frozenReg_of_dm hD))
  have hNeg : ContinuousOn (fun p => -((negFamily (frozenFamily F Kidx)).bandHi p)) (paramSet K 1) :=
    (continuousOn_iff_continuous_restrict.mpr (hR.neg).contBandHi).neg
  have heq : (fun p : Par × ℝ => -((negFamily (frozenFamily F Kidx)).bandHi p)) =
      (frozenFamily F Kidx).bandLo := by
    funext p
    rw [negFamily_bandHi, neg_neg]
  simpa [heq] using hNeg

private lemma paramSet_nhd_of_prod {Par : Type*} [TopologicalSpace Par]
    {K : Set Par} {μ0 : Par} {W : Set (Par × ℝ)}
    (hW : W ∈ 𝓝[paramSet K 1] (μ0, (0 : ℝ))) :
    ∃ K' ∈ 𝓝[K] μ0, ∃ t0 : ℝ, 0 < t0 ∧ t0 ≤ 1 ∧ paramSet K' t0 ⊆ W := by
  unfold paramSet at hW ⊢
  rw [nhdsWithin_prod_eq, Filter.mem_prod_iff] at hW
  obtain ⟨K', hK', V, hV, hsub⟩ := hW
  rw [Metric.mem_nhdsWithin_iff] at hV
  obtain ⟨r, hr, hball⟩ := hV
  refine ⟨K', hK', min (r / 2) 1, lt_min (half_pos hr) zero_lt_one, min_le_right _ _, ?_⟩
  intro ⟨μ, t⟩ ⟨hμ, ht⟩
  apply hsub
  refine ⟨hμ, hball ⟨?_, ?_⟩⟩
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have ht_abs : |t| ≤ min (r / 2) 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    have : min (r / 2) 1 ≤ r / 2 := min_le_left _ _
    linarith
  · exact ⟨by linarith [ht.1, min_le_right (r / 2) 1], ht.2.trans (min_le_right _ _)⟩

/-- Strict-interval version of `local_cover_of_geom`: yields `Jlo < Jhi` as well as all 5 band inequalities. -/
theorem local_cover_of_geom_strict {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par)
    {K : Set Par} (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K 1) (μ0 : Par) (hμ0 : μ0 ∈ K)
    {δup δlo : ℝ} (hδup : 0 < δup) (hδlo : 0 < δlo) (Kidx : ℕ := 0) :
    ∃ K' ∈ 𝓝[K] μ0, ∃ t0 Jlo Jhi : ℝ, 0 < t0 ∧ t0 ≤ 1 ∧ Jlo < Jhi ∧
      ∀ p ∈ paramSet K' t0, (frozenFamily F Kidx).bandLo p < Jlo ∧ Jlo < Jhi ∧
        Jhi < (frozenFamily F Kidx).bandHi p ∧
        (frozenFamily F Kidx).bandHi p < Jhi + δup ∧ Jlo - δlo < (frozenFamily F Kidx).bandLo p := by
  have hband_lt : F.bandLo μ0 < F.bandHi μ0 := bandLo_lt_bandHi F K 1 hH hD μ0 hμ0
  let ε : ℝ := min ((F.bandHi μ0 - F.bandLo μ0) / 4) (min (δup / 2) (δlo / 2))
  have hε : 0 < ε := by
    dsimp [ε]
    refine lt_min (by linarith) (lt_min (half_pos hδup) (half_pos hδlo))
  let Jlo : ℝ := F.bandLo μ0 + ε
  let Jhi : ℝ := F.bandHi μ0 - ε
  have hJlt : Jlo < Jhi := by
    have : ε ≤ (F.bandHi μ0 - F.bandLo μ0) / 4 := min_le_left _ _
    dsimp [Jlo, Jhi]
    linarith
  have hε_up : ε ≤ δup / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε_lo : ε ≤ δlo / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hP0 : (μ0, (0 : ℝ)) ∈ paramSet K 1 := ⟨hμ0, by norm_num⟩
  have hContHi := frozen_bandHi_contOn F hK hD (Kidx := 0) (μ0, 0) hP0
  have hContLo := frozen_bandLo_contOn F hK hD (Kidx := 0) (μ0, 0) hP0
  have hW1 : {p : Par × ℝ | |(frozenFamily F 0).bandHi p - F.bandHi μ0| < ε} ∈
      𝓝[paramSet K 1] (μ0, (0 : ℝ)) := by
    have heq : (frozenFamily F 0).bandHi (μ0, 0) = F.bandHi μ0 := frozen_bandHi_zero F 0 μ0
    simpa [heq, Metric.ball, Real.dist_eq] using hContHi (Metric.ball_mem_nhds _ hε)
  have hW2 : {p : Par × ℝ | |(frozenFamily F 0).bandLo p - F.bandLo μ0| < ε} ∈
      𝓝[paramSet K 1] (μ0, (0 : ℝ)) := by
    have heq : (frozenFamily F 0).bandLo (μ0, 0) = F.bandLo μ0 := frozen_bandLo_zero F 0 μ0
    simpa [heq, Metric.ball, Real.dist_eq] using hContLo (Metric.ball_mem_nhds _ hε)
  obtain ⟨K', hK', t0, ht0, ht0_le, hsub⟩ := paramSet_nhd_of_prod (Filter.inter_mem hW1 hW2)
  refine ⟨K', hK', t0, Jlo, Jhi, ht0, ht0_le, hJlt, fun p hp => ?_⟩
  obtain ⟨h1, h2⟩ := hsub hp
  rw [Set.mem_ofPred_eq, abs_lt] at h1 h2
  rw [frozen_bandHi_eq F Kidx, frozen_bandLo_eq F Kidx]
  refine ⟨?_, hJlt, ?_, ?_, ?_⟩
  · dsimp [Jlo]; linarith [h2.2]
  · dsimp [Jhi]; linarith [h1.1]
  · dsimp [Jhi]; linarith [h1.2, hε_up]
  · dsimp [Jlo]; linarith [h2.1, hε_lo]

/-- **Local cover (`ChartInputs.cover`)**: from `HypOn F K` and `DM F K 1` on compact `K`. -/
theorem local_cover_of_geom {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par)
    {K : Set Par} (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K 1) (μ0 : Par) (hμ0 : μ0 ∈ K)
    {δup δlo : ℝ} (hδup : 0 < δup) (hδlo : 0 < δlo) (Kidx : ℕ := 0) :
    ∃ K' ∈ 𝓝[K] μ0, ∃ t0 Jlo Jhi : ℝ, 0 < t0 ∧
      ∀ p ∈ paramSet K' t0, (frozenFamily F Kidx).bandLo p < Jlo ∧ Jlo ≤ Jhi ∧
        Jhi < (frozenFamily F Kidx).bandHi p ∧
        (frozenFamily F Kidx).bandHi p < Jhi + δup ∧ Jlo - δlo < (frozenFamily F Kidx).bandLo p := by
  obtain ⟨K', hK', t0, Jlo, Jhi, ht0, _, hJlt, hcov⟩ :=
    local_cover_of_geom_strict F hK hH hD μ0 hμ0 hδup hδlo Kidx
  refine ⟨K', hK', t0, Jlo, Jhi, ht0, fun p hp => ?_⟩
  obtain ⟨h1, _, h3, h4, h5⟩ := hcov p hp
  exact ⟨h1, hJlt.le, h3, h4, h5⟩

/-! ### 2. Bulk block cover, `overlap_in_well`, and `theta_margin` -/

private lemma local_bulk_point_data {Par : Type*} [TopologicalSpace Par]
    (F : SymbolFamily Par) {P : Set Par} (hH : HypOn F P) (hReg : PrincipalReg F P 2)
    (μ0 : Par) (hμ0 : μ0 ∈ P) {Jlo Jhi : ℝ}
    (hJband : ∀ μ ∈ P, F.bandLo μ < Jlo ∧ Jhi < F.bandHi μ)
    (Emax : ℝ) (hEmax : 1 ≤ Emax ∧ ∀ μ ∈ P, ∀ u ∈ Icc 0 F.L, E0 F.L (F.G 0 μ) u ≤ Emax)
    (X0 : ℝ) (hX0 : X0 ∈ Icc Jlo Jhi) :
    ∃ N ∈ 𝓝[P] μ0, ∃ r c' c σ ε : ℝ, 0 < r ∧ c' < c ∧ 0 < σ ∧ 0 < ε ∧ ε < 1 ∧
      ∀ p ∈ N ∩ P, ∀ X ∈ Metric.ball X0 r ∩ Icc Jlo Jhi,
        F.uMinus p X + σ ≤ c' ∧ c ≤ F.uPlus p X - σ ∧
        ∀ u ∈ Icc c' c, |X - F.B 0 p u| ≤ (1 - ε) * (2 * Real.sqrt (E0 F.L (F.G 0 p) u)) := by
  obtain ⟨g, hHyp⟩ := hH
  have hyp0 := hHyp μ0 hμ0
  have hX0_band : F.bandLo μ0 < X0 ∧ X0 < F.bandHi μ0 :=
    ⟨(hJband μ0 hμ0).1.trans_le hX0.1, hX0.2.trans_lt (hJband μ0 hμ0).2⟩
  have hG2_0 : ContDiffOn ℝ 2 (F.G 0 μ0) (Icc 0 F.L) := hReg.1.1 μ0 hμ0
  have hB2_0 : ContDiffOn ℝ 2 (F.B 0 μ0) (Icc 0 F.L) := hReg.2.1 μ0 hμ0
  obtain ⟨hb_lt, hTpos, _⟩ :=
    HypMorse.geomBulk F.L (F.G 0 μ0) (F.B 0 μ0) g F.L_pos hyp0 hG2_0 hB2_0 X0 hX0_band.1 hX0_band.2
  obtain ⟨a, b, ha0, hab, hbL, hEqSet, _⟩ := hyp0.H2 X0 hX0_band.1 hX0_band.2
  have hum_eq : F.uMinus μ0 X0 = a := by
    rw [SymbolFamily.uMinus, hEqSet, csInf_Icc hab]
  have hup_eq : F.uPlus μ0 X0 = b := by
    rw [SymbolFamily.uPlus, hEqSet, csSup_Icc hab]
  have hum_lt : F.uMinus μ0 X0 < F.uPlus μ0 X0 := by
    simpa only [uMinus_eq_uMinusS, uPlus_eq_uPlusS] using hb_lt
  have h0_le_um : 0 ≤ F.uMinus μ0 X0 := by rw [hum_eq]; exact ha0
  have hup_le_L : F.uPlus μ0 X0 ≤ F.L := by rw [hup_eq]; exact hbL
  let um := F.uMinus μ0 X0
  let up := F.uPlus μ0 X0
  let c' := (2 * um + up) / 3
  let c := (um + 2 * up) / 3
  let σ := (up - um) / 6
  have hσ_pos : 0 < σ := by dsimp [σ]; linarith
  have hc'_lt_c : c' < c := by dsimp [c', c]; linarith
  let S : Set ℝ := Icc (c' - σ) (c + σ)
  have hS_sub_well : S ⊆ Ioo um up := by
    intro u hu
    dsimp [S, c', c, σ] at hu ⊢
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hS_sub_L : S ⊆ Icc 0 F.L := fun u hu =>
    ⟨h0_le_um.trans (hS_sub_well hu).1.le, (hS_sub_well hu).2.le.trans hup_le_L⟩
  have hS_ne : S.Nonempty := ⟨c' - σ, left_mem_Icc.mpr (by dsimp [c', c, σ]; linarith)⟩
  let Φ : Par × ℝ × ℝ → ℝ := fun q => Tfun F.L (F.G 0 q.1) (F.B 0 q.1) q.2.1 q.2.2
  have hG_cont_joint : ContinuousOn (fun x : Par × ℝ => F.G 0 x.1 x.2) (P ×ˢ Icc 0 F.L) := by
    simpa [iteratedDerivWithin_zero] using hReg.1.2 0 (by norm_num)
  have hB_cont_joint : ContinuousOn (fun x : Par × ℝ => F.B 0 x.1 x.2) (P ×ˢ Icc 0 F.L) := by
    simpa [iteratedDerivWithin_zero] using hReg.2.2 0 (by norm_num)
  let Qset : Set (Par × ℝ × ℝ) := P ×ˢ (univ ×ˢ Icc 0 F.L)
  have hΦ_cont : ContinuousOn Φ Qset := by
    have hmap : Continuous (fun q : Par × ℝ × ℝ => (q.1, q.2.2)) := by fun_prop
    have hG_q : ContinuousOn (fun q : Par × ℝ × ℝ => F.G 0 q.1 q.2.2) Qset :=
      hG_cont_joint.comp hmap.continuousOn fun q hq => ⟨hq.1, hq.2.2⟩
    have hB_q : ContinuousOn (fun q : Par × ℝ × ℝ => F.B 0 q.1 q.2.2) Qset :=
      hB_cont_joint.comp hmap.continuousOn fun q hq => ⟨hq.1, hq.2.2⟩
    have hE_q : ContinuousOn (fun q : Par × ℝ × ℝ => E0 F.L (F.G 0 q.1) q.2.2) Qset := by
      unfold E0
      exact (((continuous_snd.comp continuous_snd).mul
        (continuous_const.sub (continuous_snd.comp continuous_snd))).continuousOn).mul hG_q
    have hX_q : ContinuousOn (fun q : Par × ℝ × ℝ => q.2.1) Qset :=
      (continuous_fst.comp continuous_snd).continuousOn
    unfold Φ Tfun
    exact (continuousOn_const.mul hE_q).sub ((hX_q.sub hB_q).pow 2)
  have hφ_cont : ContinuousOn (fun u => Φ (μ0, X0, u)) S := by
    have hmap : Continuous (fun u : ℝ => (μ0, X0, u)) := by fun_prop
    exact hΦ_cont.comp hmap.continuousOn fun u hu => ⟨hμ0, mem_univ _, hS_sub_L hu⟩
  obtain ⟨umin, humin_mem, humin_min⟩ := isCompact_Icc.exists_isMinOn hS_ne hφ_cont
  let m := Φ (μ0, X0, umin)
  have hm_pos : 0 < m := by
    dsimp [m, Φ]
    exact (hTpos umin (hS_sub_L humin_mem)).mpr (hS_sub_well humin_mem)
  have hm_le_4E : m ≤ 4 * Emax := by
    have h1 : m ≤ 4 * E0 F.L (F.G 0 μ0) umin := by
      dsimp [m, Φ, Tfun]
      linarith [sq_nonneg (X0 - F.B 0 μ0 umin)]
    have h2 : E0 F.L (F.G 0 μ0) umin ≤ Emax := hEmax.2 μ0 hμ0 umin (hS_sub_L humin_mem)
    linarith
  have htube_pt : ∀ u : S, ∃ U ∈ 𝓝[P] μ0, ∃ ρ δ : ℝ, 0 < ρ ∧ 0 < δ ∧
      ∀ p ∈ U ∩ P, ∀ X ∈ Metric.ball X0 ρ, ∀ v ∈ Metric.ball u.1 δ ∩ Icc 0 F.L, m / 2 < Φ (p, X, v) := by
    intro ⟨u, hu⟩
    have huQ : (μ0, X0, u) ∈ Qset := ⟨hμ0, mem_univ _, hS_sub_L hu⟩
    have hm_u : m / 2 < Φ (μ0, X0, u) := by
      have : m ≤ Φ (μ0, X0, u) := humin_min hu
      linarith
    have hnhd : Φ ⁻¹' Ioi (m / 2) ∈ 𝓝[Qset] (μ0, X0, u) :=
      hΦ_cont (μ0, X0, u) huQ (isOpen_Ioi.mem_nhds hm_u)
    dsimp [Qset] at hnhd
    rw [nhdsWithin_prod_eq, Filter.mem_prod_iff] at hnhd
    obtain ⟨U, hU, V2, hV2, hsub⟩ := hnhd
    rw [nhdsWithin_prod_eq, nhdsWithin_univ, Filter.mem_prod_iff] at hV2
    obtain ⟨Vx, hVx, Vu, hVu, hsub2⟩ := hV2
    rw [Metric.mem_nhds_iff] at hVx
    rw [Metric.mem_nhdsWithin_iff] at hVu
    obtain ⟨ρ, hρ, hballx⟩ := hVx
    obtain ⟨δ, hδ, hballu⟩ := hVu
    refine ⟨U, hU, ρ, δ, hρ, hδ, fun p hp X hX v hv => ?_⟩
    exact hsub ⟨hp.1, hsub2 ⟨hballx hX, hballu hv⟩⟩
  choose Uf hUf ρf δf hρf hδf hball_pt using htube_pt
  have hcov : S ⊆ ⋃ u : S, Metric.ball u.1 (δf u) := fun u hu =>
    Set.mem_iUnion.mpr ⟨⟨u, hu⟩, Metric.mem_ball_self (hδf ⟨u, hu⟩)⟩
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover
    (fun u : S => Metric.ball u.1 (δf u)) (fun _ => Metric.isOpen_ball) hcov
  have ht_ne : t.Nonempty := by
    rcases hS_ne with ⟨u0, hu0⟩
    have := ht hu0
    simp only [Set.mem_iUnion] at this
    rcases this with ⟨u, hu_t, _⟩
    exact ⟨u, hu_t⟩
  let N : Set Par := ⋂ u ∈ t, Uf u
  have hN_mem : N ∈ 𝓝[P] μ0 := (biInter_finset_mem t).mpr fun u _ => hUf u
  let r : ℝ := t.inf' ht_ne ρf
  have hr_pos : 0 < r := (Finset.lt_inf'_iff ht_ne).mpr fun u _ => hρf u
  let ε : ℝ := m / (16 * Emax)
  have hEmax_pos : 0 < Emax := by linarith [hEmax.1]
  have hε_pos : 0 < ε := by positivity
  have hε_le_quart : ε ≤ 1 / 4 := by
    dsimp [ε]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hε_lt_one : ε < 1 := by linarith
  refine ⟨N, hN_mem, r, c', c, σ, ε, hr_pos, hc'_lt_c, hσ_pos, hε_pos, hε_lt_one, ?_⟩
  intro p hp X hX
  have hpP : p ∈ P := hp.2
  have hT_S : ∀ v ∈ S, m / 2 < Tfun F.L (F.G 0 p) (F.B 0 p) X v := by
    intro v hv
    have hv_cov := ht hv
    simp only [Set.mem_iUnion] at hv_cov
    rcases hv_cov with ⟨u0, hu0_t, hv_ball⟩
    have hp_u0 : p ∈ Uf u0 ∩ P := ⟨Set.iInter₂_subset u0 hu0_t hp.1, hpP⟩
    have hr_le : r ≤ ρf u0 := Finset.inf'_le _ hu0_t
    have hX_u0 : X ∈ Metric.ball X0 (ρf u0) := Metric.ball_subset_ball hr_le hX.1
    exact hball_pt u0 p hp_u0 X hX_u0 v ⟨hv_ball, hS_sub_L hv⟩
  have hX_band : F.bandLo p < X ∧ X < F.bandHi p :=
    ⟨(hJband p hpP).1.trans_le hX.2.1, hX.2.2.trans_lt (hJband p hpP).2⟩
  obtain ⟨_, hT_iff_p, _⟩ :=
    HypMorse.geomBulk F.L (F.G 0 p) (F.B 0 p) g F.L_pos (hHyp p hpP)
      (hReg.1.1 p hpP) (hReg.2.1 p hpP) X hX_band.1 hX_band.2
  have hwell_S : ∀ v ∈ S, F.uMinus p X < v ∧ v < F.uPlus p X := fun v hv => by
    have hv_pos : 0 < Tfun F.L (F.G 0 p) (F.B 0 p) X v := by linarith [hT_S v hv]
    simpa only [uMinus_eq_uMinusS, uPlus_eq_uPlusS] using (hT_iff_p v (hS_sub_L hv)).mp hv_pos
  have hL_pt := (hwell_S (c' - σ) (left_mem_Icc.mpr (by linarith))).1
  have hR_pt := (hwell_S (c + σ) (right_mem_Icc.mpr (by linarith))).2
  refine ⟨by linarith, by linarith, fun u hu => ?_⟩
  have huS : u ∈ S := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hm_u : m / 2 < Tfun F.L (F.G 0 p) (F.B 0 p) X u := hT_S u huS
  have hE0_pos : 0 < E0 F.L (F.G 0 p) u := by
    unfold Tfun at hm_u
    linarith [sq_nonneg (X - F.B 0 p u)]
  have hE0_le : E0 F.L (F.G 0 p) u ≤ Emax := hEmax.2 p hpP u (hS_sub_L huS)
  have hQ_sq : (X - F.B 0 p u) ^ 2 ≤ 4 * E0 F.L (F.G 0 p) u - m / 2 := by
    unfold Tfun at hm_u; linarith
  have h8_le : 8 * E0 F.L (F.G 0 p) u * ε ≤ m / 2 := by
    have hcalc : 8 * E0 F.L (F.G 0 p) u * ε = (E0 F.L (F.G 0 p) u / Emax) * (m / 2) := by
      dsimp [ε]; field_simp; ring
    rw [hcalc]
    have hratio : E0 F.L (F.G 0 p) u / Emax ≤ 1 := (div_le_one hEmax_pos).mpr hE0_le
    calc (E0 F.L (F.G 0 p) u / Emax) * (m / 2) ≤ 1 * (m / 2) :=
          mul_le_mul_of_nonneg_right hratio (by linarith)
      _ = m / 2 := one_mul _
  have hsq_bound : (X - F.B 0 p u) ^ 2 ≤ ((1 - ε) * (2 * Real.sqrt (E0 F.L (F.G 0 p) u))) ^ 2 := by
    have h1 : ((1 - ε) * (2 * Real.sqrt (E0 F.L (F.G 0 p) u))) ^ 2 =
        4 * E0 F.L (F.G 0 p) u * (1 - 2 * ε + ε ^ 2) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hE0_pos.le]; ring
    have h2 : 4 * E0 F.L (F.G 0 p) u - m / 2 ≤ 4 * E0 F.L (F.G 0 p) u * (1 - 2 * ε + ε ^ 2) := by
      nlinarith [hE0_pos.le, sq_nonneg ε, h8_le]
    exact hQ_sq.trans (h2.trans_eq h1.symm)
  have hrhs_nn : 0 ≤ (1 - ε) * (2 * Real.sqrt (E0 F.L (F.G 0 p) u)) :=
    mul_nonneg (by linarith) (by positivity)
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hrhs_nn]
  exact Real.sqrt_le_sqrt hsq_bound

/-- **Bulk block cover (`ChartInputs.cover_bulk`), `blocks_in_J`, `overlap_in_well`, and `theta_margin`**:
from `HypOn` and `PrincipalReg F P 2` on compact `P` with `Jlo < Jhi` strictly inside `(bandLo, bandHi)`.
Constructs `2 * m - 1` overlapping intervals of equal width `< δ_L` so every `X ∈ [Jlo, Jhi]` lies
in the relative interior of some block (`lo ν < X ∨ lo ν = Jlo` and `X < hi ν ∨ hi ν = Jhi`). -/
theorem local_bulk_cover_of_geom {Par : Type*} [TopologicalSpace Par]
    (F : SymbolFamily Par) {P : Set Par} (hP : IsCompact P) (hH : HypOn F P)
    (hReg : PrincipalReg F P 2) (μ0 : Par) (hμ0 : μ0 ∈ P) {Jlo Jhi : ℝ} (hJlt : Jlo < Jhi)
    (hJband : ∀ μ ∈ P, F.bandLo μ < Jlo ∧ Jhi < F.bandHi μ) :
    ∃ N ∈ 𝓝[P] μ0, ∃ (nb : ℕ) (lo hi c' c : Fin nb → ℝ) (σ ε : ℝ),
      0 < nb ∧ 0 < σ ∧ 0 < ε ∧ ε < 1 ∧
      (∀ ν, lo ν < hi ν ∧ Icc (lo ν) (hi ν) ⊆ Icc Jlo Jhi) ∧
      (∀ X ∈ Icc Jlo Jhi, ∃ ν, lo ν ≤ X ∧ X ≤ hi ν ∧
        (lo ν < X ∨ lo ν = Jlo) ∧ (X < hi ν ∨ hi ν = Jhi)) ∧
      (∀ ν, c' ν < c ν) ∧
      (∀ ν, ∀ p ∈ N ∩ P, ∀ X ∈ Icc (lo ν) (hi ν),
        F.uMinus p X + σ ≤ c' ν ∧ c ν ≤ F.uPlus p X - σ ∧
        ∀ u ∈ Icc (c' ν) (c ν), |X - F.B 0 p u| ≤ (1 - ε) * (2 * Real.sqrt (E0 F.L (F.G 0 p) u))) := by
  have hG_cont_joint : ContinuousOn (fun x : Par × ℝ => F.G 0 x.1 x.2) (P ×ˢ Icc 0 F.L) := by
    simpa [iteratedDerivWithin_zero] using hReg.1.2 0 (by norm_num)
  have hE_cont_joint : ContinuousOn (fun x : Par × ℝ => E0 F.L (F.G 0 x.1) x.2) (P ×ˢ Icc 0 F.L) := by
    unfold E0
    exact (((continuous_snd.mul (continuous_const.sub continuous_snd)).continuousOn)).mul hG_cont_joint
  have hPL_ne : (P ×ˢ Icc (0 : ℝ) F.L).Nonempty := ⟨(μ0, 0), hμ0, left_mem_Icc.mpr F.L_pos.le⟩
  obtain ⟨qmax, _, hqmax⟩ := (hP.prod isCompact_Icc).exists_isMaxOn hPL_ne hE_cont_joint
  let Emax : ℝ := max (E0 F.L (F.G 0 qmax.1) qmax.2) 1
  have hEmax : 1 ≤ Emax ∧ ∀ μ ∈ P, ∀ u ∈ Icc 0 F.L, E0 F.L (F.G 0 μ) u ≤ Emax :=
    ⟨le_max_right _ _, fun μ hμ u hu => (isMaxOn_iff.mp hqmax (μ, u) ⟨hμ, hu⟩).trans (le_max_left _ _)⟩
  have hpt : ∀ X0 : Icc Jlo Jhi, ∃ N ∈ 𝓝[P] μ0, ∃ r c' c σ ε : ℝ,
      0 < r ∧ c' < c ∧ 0 < σ ∧ 0 < ε ∧ ε < 1 ∧
      ∀ p ∈ N ∩ P, ∀ X ∈ Metric.ball X0.1 r ∩ Icc Jlo Jhi,
        F.uMinus p X + σ ≤ c' ∧ c ≤ F.uPlus p X - σ ∧
        ∀ u ∈ Icc c' c, |X - F.B 0 p u| ≤ (1 - ε) * (2 * Real.sqrt (E0 F.L (F.G 0 p) u)) :=
    fun ⟨X0, hX0⟩ => local_bulk_point_data F hH hReg μ0 hμ0 hJband Emax hEmax X0 hX0
  choose Nf hNf rf cf' cf σf εf hrf hcf hσf hεf_pos hεf_lt hball using hpt
  have hcov_J : Icc Jlo Jhi ⊆ ⋃ X0 : Icc Jlo Jhi, Metric.ball X0.1 (rf X0) := fun X hX =>
    Set.mem_iUnion.mpr ⟨⟨X, hX⟩, Metric.mem_ball_self (hrf ⟨X, hX⟩)⟩
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover
    (fun X0 : Icc Jlo Jhi => Metric.ball X0.1 (rf X0)) (fun _ => Metric.isOpen_ball) hcov_J
  have hs_ne : s.Nonempty := by
    have hJ := hs (left_mem_Icc.mpr hJlt.le)
    simp only [Set.mem_iUnion] at hJ
    rcases hJ with ⟨X0, hX0_s, _⟩
    exact ⟨X0, hX0_s⟩
  have hcov_s : Icc Jlo Jhi ⊆ ⋃ i : s, Metric.ball i.1.1 (rf i.1) := by
    intro X hX
    have := hs hX
    simp only [Set.mem_iUnion] at this ⊢
    rcases this with ⟨X0, hX0_s, hmem⟩
    exact ⟨⟨X0, hX0_s⟩, hmem⟩
  obtain ⟨δL, hδL_pos, hleb⟩ :=
    lebesgue_number_lemma_of_metric (ι := s) isCompact_Icc (fun _ => Metric.isOpen_ball) hcov_s
  let m : ℕ := Nat.floor ((Jhi - Jlo) / δL) + 1
  have hm_pos : 0 < m := Nat.succ_pos _
  let nb : ℕ := 2 * m - 1
  have hnb_pos : 0 < nb := by dsimp [nb]; omega
  let halfStep : ℝ := (Jhi - Jlo) / (2 * (m : ℝ))
  have hhalf_pos : 0 < halfStep := div_pos (sub_pos.mpr hJlt) (by positivity)
  have hstep_lt : 2 * halfStep < δL := by
    have hm_gt : (Jhi - Jlo) / δL < (m : ℝ) := by
      dsimp [m]; exact_mod_cast Nat.lt_floor_add_one ((Jhi - Jlo) / δL)
    have h2eq : 2 * halfStep = (Jhi - Jlo) / m := by dsimp [halfStep]; ring
    rw [h2eq, div_lt_iff₀ (Nat.cast_pos.mpr hm_pos)]
    exact (div_lt_iff₀ hδL_pos).mp hm_gt |>.trans_eq (mul_comm _ _)
  let lo : Fin nb → ℝ := fun ν => Jlo + (ν : ℝ) * halfStep
  let hi : Fin nb → ℝ := fun ν => Jlo + ((ν : ℝ) + 2) * halfStep
  let mid : Fin nb → ℝ := fun ν => (lo ν + hi ν) / 2
  have hhmul : 2 * (m : ℝ) * halfStep = Jhi - Jlo := by
    dsimp [halfStep]; field_simp
  have hblk_in : ∀ ν : Fin nb, lo ν < hi ν ∧ Icc (lo ν) (hi ν) ⊆ Icc Jlo Jhi := by
    intro ν
    have h0 : (0 : ℝ) ≤ ν := Nat.cast_nonneg _
    have h1 : ((ν : ℝ) + 2) ≤ 2 * (m : ℝ) := by
      have hν : ν.1 + 2 ≤ 2 * m := by have := ν.isLt; dsimp [nb] at this; omega
      exact_mod_cast hν
    refine ⟨by dsimp [lo, hi]; linarith, fun X hX => ⟨?_, ?_⟩⟩
    · dsimp [lo] at hX; nlinarith [hX.1]
    · have hhi_le : hi ν ≤ Jhi := by
        dsimp [hi]
        have : ((ν : ℝ) + 2) * halfStep ≤ (2 * (m : ℝ)) * halfStep :=
          mul_le_mul_of_nonneg_right h1 hhalf_pos.le
        linarith
      exact hX.2.trans hhi_le
  have hmid_in : ∀ ν : Fin nb, mid ν ∈ Icc Jlo Jhi := fun ν =>
    (hblk_in ν).2 ⟨by dsimp [mid]; linarith [(hblk_in ν).1],
      by dsimp [mid]; linarith [(hblk_in ν).1]⟩
  have hchoose : ∀ ν : Fin nb, ∃ i : s, Metric.ball (mid ν) δL ⊆ Metric.ball i.1.1 (rf i.1) :=
    fun ν => hleb (mid ν) (hmid_in ν)
  choose idxf hidxf using hchoose
  let N : Set Par := ⋂ x ∈ s, Nf x
  have hN_mem : N ∈ 𝓝[P] μ0 := (biInter_finset_mem s).mpr fun x _ => hNf x
  let σ : ℝ := s.inf' hs_ne σf
  let ε : ℝ := s.inf' hs_ne εf
  have hσ_pos : 0 < σ := (Finset.lt_inf'_iff hs_ne).mpr fun x _ => hσf x
  have hε_pos : 0 < ε := (Finset.lt_inf'_iff hs_ne).mpr fun x _ => hεf_pos x
  have hε_lt1 : ε < 1 := by
    rcases hs_ne with ⟨x0, hx0⟩
    exact (Finset.inf'_le _ hx0).trans_lt (hεf_lt x0)
  refine ⟨N, hN_mem, nb, lo, hi, fun ν => cf' (idxf ν).1, fun ν => cf (idxf ν).1, σ, ε,
    hnb_pos, hσ_pos, hε_pos, hε_lt1, hblk_in, ?_, fun ν => hcf (idxf ν).1, ?_⟩
  · intro X hX
    by_cases hm1 : m = 1
    · have hnb1 : nb = 1 := by dsimp [nb]; omega
      let ν0 : Fin nb := ⟨0, hnb_pos⟩
      have hlo0 : lo ν0 = Jlo := by dsimp [lo, ν0]; ring
      have hhi0 : hi ν0 = Jhi := by
        dsimp [hi, ν0]
        have hm1r : (m : ℝ) = 1 := by exact_mod_cast hm1
        have hstep1 : 2 * halfStep = Jhi - Jlo := by rw [hm1r, mul_one] at hhmul; exact hhmul
        linarith
      exact ⟨ν0, hlo0.symm ▸ hX.1, hhi0.symm ▸ hX.2, Or.inr hlo0, Or.inr hhi0⟩
    · have hm2 : 2 ≤ m := by omega
      by_cases hleft : X < Jlo + 2 * halfStep
      · let ν0 : Fin nb := ⟨0, hnb_pos⟩
        have hlo0 : lo ν0 = Jlo := by dsimp [lo, ν0]; ring
        have hhi0 : hi ν0 = Jlo + 2 * halfStep := by dsimp [hi, ν0]; ring
        exact ⟨ν0, hlo0.symm ▸ hX.1, (hhi0.symm ▸ hleft).le, Or.inr hlo0, Or.inl (hhi0.symm ▸ hleft)⟩
      · by_cases hright : Jhi - 2 * halfStep < X
        · let νlast : Fin nb := ⟨nb - 1, Nat.sub_lt hnb_pos Nat.one_pos⟩
          have hhi_last : hi νlast = Jhi := by
            dsimp [hi, νlast]
            have hnb_eq : ((nb - 1 : ℕ) : ℝ) + 2 = 2 * (m : ℝ) := by
              have : (nb - 1) + 2 = 2 * m := by dsimp [nb]; omega
              exact_mod_cast this
            rw [hnb_eq]; linarith [hhmul]
          have hlo_last : lo νlast = Jhi - 2 * halfStep := by
            have hdiff : hi νlast - lo νlast = 2 * halfStep := by dsimp [lo, hi]; ring
            linarith
          exact ⟨νlast, (hlo_last.symm ▸ hright).le, hhi_last.symm ▸ hX.2,
            Or.inl (hlo_last.symm ▸ hright), Or.inr hhi_last⟩
        · push Not at hleft hright
          let t : ℝ := (X - Jlo) / halfStep
          have ht_ge : 2 ≤ t := by
            dsimp [t]; rw [le_div_iff₀ hhalf_pos]; linarith
          have ht_le : t ≤ 2 * (m : ℝ) - 2 := by
            dsimp [t]; rw [div_le_iff₀ hhalf_pos]; linarith [hhmul]
          let k : ℕ := Nat.floor (t - 1 / 2)
          have hk_lt : k < nb := by
            have hk_leR : (k : ℝ) ≤ t - 1 / 2 := Nat.floor_le (by linarith)
            have hk_ltR : (k : ℝ) < (nb : ℝ) := by
              have hnb_cast : (nb : ℝ) = 2 * (m : ℝ) - 1 := by
                have h2m : 1 ≤ 2 * m := by omega
                dsimp [nb]; rw [Nat.cast_sub h2m]; push_cast; ring
              linarith
            exact_mod_cast hk_ltR
          refine ⟨⟨k, hk_lt⟩, ?_, ?_, Or.inl ?_, Or.inl ?_⟩
          · have hk_leR : (k : ℝ) ≤ t - 1 / 2 := Nat.floor_le (by linarith)
            have : (k : ℝ) < t := by linarith
            dsimp [lo]; rw [lt_div_iff₀ hhalf_pos] at this; linarith
          · have hk_gtR : t - 1 / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
            have : t < (k : ℝ) + 2 := by linarith
            dsimp [hi]; rw [div_lt_iff₀ hhalf_pos] at this; linarith
          · have hk_leR : (k : ℝ) ≤ t - 1 / 2 := Nat.floor_le (by linarith)
            have : (k : ℝ) < t := by linarith
            dsimp [lo]; rw [lt_div_iff₀ hhalf_pos] at this; linarith
          · have hk_gtR : t - 1 / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
            have : t < (k : ℝ) + 2 := by linarith
            dsimp [hi]; rw [div_lt_iff₀ hhalf_pos] at this; linarith
  · intro ν p hp X hX
    have hx_s := (idxf ν).2
    have hp_x : p ∈ Nf (idxf ν).1 ∩ P := ⟨Set.iInter₂_subset _ hx_s hp.1, hp.2⟩
    have hX_ball_mid : X ∈ Metric.ball (mid ν) δL := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hhalf : |X - mid ν| ≤ (hi ν - lo ν) / 2 := by
        rw [abs_le]; dsimp [mid]; constructor <;> linarith [hX.1, hX.2]
      have hdiff : hi ν - lo ν = 2 * halfStep := by dsimp [lo, hi]; ring
      linarith
    have hX_ball := hidxf ν hX_ball_mid
    have hX_J := (hblk_in ν).2 hX
    obtain ⟨hm, hp_u, hth⟩ := hball (idxf ν).1 p hp_x X ⟨hX_ball, hX_J⟩
    have hσ_le : σ ≤ σf (idxf ν).1 := Finset.inf'_le _ hx_s
    have hε_le : ε ≤ εf (idxf ν).1 := Finset.inf'_le _ hx_s
    refine ⟨by linarith, by linarith, fun u hu => ?_⟩
    have h1 := hth u hu
    have hsq_nn : 0 ≤ 2 * Real.sqrt (E0 F.L (F.G 0 p) u) := by positivity
    exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) hsq_nn)

/-! ### 3. Mirror symmetries (`Bulk` overlap + `SoftMirror` geometry) -/

private lemma allowedSet_mirror {Par : Type*} (F : SymbolFamily Par) (μ : Par) (X : ℝ) :
    Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L ((mirrorFamily F).G 0 μ) ((mirrorFamily F).B 0 μ) X u} =
      (fun u => F.L - u) '' (Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L (F.G 0 μ) (F.B 0 μ) X u}) := by
  ext u
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq, Set.mem_image, mirrorFamily]
  constructor
  · intro ⟨⟨hu0, huL⟩, hT⟩
    refine ⟨F.L - u, ⟨⟨by linarith, by linarith⟩, ?_⟩, by ring⟩
    unfold Tfun E0 at hT ⊢
    ring_nf at hT ⊢
    exact hT
  · rintro ⟨v, ⟨⟨hv0, hvL⟩, hT⟩, rfl⟩
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    unfold Tfun E0 at hT ⊢
    ring_nf at hT ⊢
    exact hT

theorem uMinus_mirror_ne {Par : Type*} (F : SymbolFamily Par) (μ : Par) (X : ℝ)
    (hne : (Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L (F.G 0 μ) (F.B 0 μ) X u}).Nonempty) :
    (mirrorFamily F).uMinus μ X = F.L - F.uPlus μ X := by
  let S := Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L (F.G 0 μ) (F.B 0 μ) X u}
  have hS_bdd_lo : BddBelow S := ⟨0, fun u hu => hu.1.1⟩
  have hS_bdd_hi : BddAbove S := ⟨F.L, fun u hu => hu.1.2⟩
  have hM_eq : Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L ((mirrorFamily F).G 0 μ) ((mirrorFamily F).B 0 μ) X u} =
      (fun u => F.L - u) '' S := allowedSet_mirror F μ X
  have hM_ne : ((fun u => F.L - u) '' S).Nonempty := hne.image _
  have hM_bdd_lo : BddBelow ((fun u => F.L - u) '' S) := ⟨0, by rintro _ ⟨v, hv, rfl⟩; linarith [hv.1.2]⟩
  unfold SymbolFamily.uMinus SymbolFamily.uPlus
  change sInf (Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L ((mirrorFamily F).G 0 μ) ((mirrorFamily F).B 0 μ) X u}) = F.L - sSup S
  rw [hM_eq]
  apply le_antisymm
  · have hsup : sSup S ≤ F.L - sInf ((fun u => F.L - u) '' S) := csSup_le hne fun u hu => by
      have := csInf_le hM_bdd_lo (mem_image_of_mem (fun u => F.L - u) hu)
      linarith
    linarith
  · refine le_csInf hM_ne ?_
    rintro _ ⟨v, hv, rfl⟩
    have := le_csSup hS_bdd_hi hv
    linarith

theorem uPlus_mirror_ne {Par : Type*} (F : SymbolFamily Par) (μ : Par) (X : ℝ)
    (hne : (Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L (F.G 0 μ) (F.B 0 μ) X u}).Nonempty) :
    (mirrorFamily F).uPlus μ X = F.L - F.uMinus μ X := by
  let S := Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L (F.G 0 μ) (F.B 0 μ) X u}
  have hS_bdd_lo : BddBelow S := ⟨0, fun u hu => hu.1.1⟩
  have hM_eq : Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L ((mirrorFamily F).G 0 μ) ((mirrorFamily F).B 0 μ) X u} =
      (fun u => F.L - u) '' S := allowedSet_mirror F μ X
  have hM_ne : ((fun u => F.L - u) '' S).Nonempty := hne.image _
  have hM_bdd_hi : BddAbove ((fun u => F.L - u) '' S) := ⟨F.L, by rintro _ ⟨v, hv, rfl⟩; linarith [hv.1.1]⟩
  unfold SymbolFamily.uPlus SymbolFamily.uMinus
  change sSup (Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L ((mirrorFamily F).G 0 μ) ((mirrorFamily F).B 0 μ) X u}) = F.L - sInf S
  rw [hM_eq]
  apply le_antisymm
  · refine csSup_le hM_ne ?_
    rintro _ ⟨v, hv, rfl⟩
    have := csInf_le hS_bdd_lo hv
    linarith
  · rw [sub_le_iff_le_add]
    have : F.L - sSup ((fun u => F.L - u) '' S) ≤ sInf S := by
      refine le_csInf hne fun v hv => ?_
      have := le_csSup hM_bdd_hi (mem_image_of_mem _ hv)
      linarith
    linarith

/-- **Mirror bulk overlap (`ChartInputs.overlap_match` + `overlap_in_well` + `theta_margin`)**:
with `c'_R = F.L - c`, `c_R = F.L - c'`, `σ_R = σ`. -/
theorem mirror_bulk_overlap_match {Par : Type*} (F : SymbolFamily Par)
    {P : Set Par} {Jlo Jhi c' c σ ε : ℝ} (hcc : c' < c)
    (hne : ∀ p ∈ P, ∀ X ∈ Icc Jlo Jhi,
      (Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L (F.G 0 p) (F.B 0 p) X u}).Nonempty)
    (hov : ∀ p ∈ P, ∀ X ∈ Icc Jlo Jhi, F.uMinus p X + σ ≤ c' ∧ c ≤ F.uPlus p X - σ)
    (hth : ∀ p ∈ P, ∀ X ∈ Icc Jlo Jhi, ∀ u ∈ Icc c' c,
      |X - F.B 0 p u| ≤ (1 - ε) * (2 * Real.sqrt (E0 F.L (F.G 0 p) u))) :
    let c'R := F.L - c
    let cR := F.L - c'
    c'R < cR ∧ cR = F.L - c' ∧ c'R = F.L - c ∧
      (∀ p ∈ P, ∀ X ∈ Icc Jlo Jhi,
        (mirrorFamily F).uMinus p X + σ ≤ c'R ∧ cR ≤ (mirrorFamily F).uPlus p X - σ) ∧
      (∀ p ∈ P, ∀ X ∈ Icc Jlo Jhi, ∀ u ∈ Icc c'R cR,
        |X - (mirrorFamily F).B 0 p u| ≤ (1 - ε) * (2 * Real.sqrt (E0 F.L ((mirrorFamily F).G 0 p) u))) := by
  refine ⟨by linarith, rfl, rfl, fun p hp X hX => ?_, fun p hp X hX u hu => ?_⟩
  · obtain ⟨h1, h2⟩ := hov p hp X hX
    rw [uMinus_mirror_ne F p X (hne p hp X hX), uPlus_mirror_ne F p X (hne p hp X hX)]
    constructor <;> linarith
  · have hLu : F.L - u ∈ Icc c' c := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have hE_eq : E0 F.L ((mirrorFamily F).G 0 p) u = E0 F.L (F.G 0 p) (F.L - u) := by
      unfold E0 mirrorFamily; ring
    have hB_eq : (mirrorFamily F).B 0 p u = F.B 0 p (F.L - u) := rfl
    rw [hE_eq, hB_eq]
    exact hth p hp X hX (F.L - u) hLu

/-- **`SoftMirror` geometric obligations for `mirrorFamily F`**:
given left-edge coordinate data `(ucL, zetaL, μL)` satisfying `uc_spec`, `ucη_in`, `geom_far`,
`zeta_deriv`, `zeta_zero`, `zeta_alpha`, `zeta_far`, `zeta_far_out`, `zeta_sign_out`, `zeta_T`,
the mirrored data `ucR := L - ucL`, `zetaR(p, α, x) := -zetaL(p, α, -x)`, `μR := μL` satisfies all
matching fields for `mirrorFamily F`. -/
theorem softMirror_geom_of_left {Par : Type*} (F : SymbolFamily Par) (P : Set Par)
    (ucL : Par → ℝ) (zetaL : Par → ℝ → ℝ → ℝ) (muS : ℕ → Par → ℝ → ℝ)
    (η δ0 dm dp cZ cz1 cT : ℝ) (q : ℕ)
    (h_uc_spec : ∀ p ∈ P, 0 < ucL p ∧ ucL p < F.L ∧ fPlus F.L (F.G 0 p) (F.B 0 p) (ucL p) = F.bandHi p)
    (h_ucη_in : ∀ p ∈ P, 0 < ucL p - 2 * η ∧ ucL p + 2 * η < F.L)
    (h_geom_far : ∀ p ∈ P, ∀ X, |X - F.bandHi p| ≤ δ0 → ∀ u ∈ Icc 0 F.L, η / 4 ≤ |u - ucL p| →
      Tfun F.L (F.G 0 p) (F.B 0 p) X u < 0 ∧ 0 < X - F.B 0 p u)
    (h_zeta_deriv : ∀ p ∈ P, ∀ α, |α| ≤ δ0 → ∀ x, |x| ≤ 2 * η → dm ≤ deriv (zetaL p α) x ∧ deriv (zetaL p α) x ≤ dp)
    (h_zeta_zero : ∀ p ∈ P, zetaL p 0 0 = 0)
    (h_zeta_alpha : ∀ p ∈ P, ∀ α, |α| ≤ δ0 → |zetaL p α 0| ≤ cZ * |α|)
    (h_zeta_far : ∀ p ∈ P, ∀ α, |α| ≤ δ0 → ∀ x, |x| ≤ 2 * η → η / 4 ≤ |x| →
      4 * max (muS 0 p α) 0 + cz1 ≤ zetaL p α x ^ 2)
    (h_zeta_far_out : ∀ p ∈ P, ∀ α, |α| ≤ δ0 → ∀ x, 2 * η ≤ |x| → 0 ≤ ucL p + x → ucL p + x ≤ F.L →
      4 * max (muS 0 p α) 0 + cz1 ≤ zetaL p α x ^ 2)
    (h_zeta_sign_out : ∀ p ∈ P, ∀ α, |α| ≤ δ0 → ∀ x, η / 4 ≤ |x| → 0 ≤ ucL p + x → ucL p + x ≤ F.L →
      (x < 0 → zetaL p α x ≤ 0) ∧ (0 < x → 0 ≤ zetaL p α x))
    (h_zeta_T : ∀ p ∈ P, ∀ α, |α| ≤ δ0 → ∀ x, |x| ≤ 2 * η → 0 ≤ ucL p + x → ucL p + x ≤ F.L →
      Tfun F.L (F.G 0 p) (F.B 0 p) (F.bandHi p - α) (ucL p + x) ≤ 0 →
      cT * (-Tfun F.L (F.G 0 p) (F.B 0 p) (F.bandHi p - α) (ucL p + x)) ≤ zetaL p α x ^ 2 / 4 - muS 0 p α) :
    let ucR : Par → ℝ := fun p => F.L - ucL p
    let zetaR : Par → ℝ → ℝ → ℝ := fun p α x => -zetaL p α (-x)
    (∀ p ∈ P, (mirrorFamily F).bandHi p = F.bandHi p) ∧
    (∀ p ∈ P, 0 < ucR p ∧ ucR p < F.L ∧
      fPlus F.L ((mirrorFamily F).G 0 p) ((mirrorFamily F).B 0 p) (ucR p) = (mirrorFamily F).bandHi p) ∧
    (∀ p ∈ P, 0 < ucR p - 2 * η ∧ ucR p + 2 * η < F.L) ∧
    (∀ p ∈ P, ∀ X, |X - (mirrorFamily F).bandHi p| ≤ δ0 → ∀ u ∈ Icc 0 F.L, η / 4 ≤ |u - ucR p| →
      Tfun F.L ((mirrorFamily F).G 0 p) ((mirrorFamily F).B 0 p) X u < 0 ∧ 0 < X - (mirrorFamily F).B 0 p u) ∧
    (∀ p ∈ P, ∀ α, |α| ≤ δ0 → ∀ x, |x| ≤ 2 * η → dm ≤ deriv (zetaR p α) x ∧ deriv (zetaR p α) x ≤ dp) ∧
    (∀ p ∈ P, zetaR p 0 0 = 0) ∧
    (∀ p ∈ P, ∀ α, |α| ≤ δ0 → |zetaR p α 0| ≤ cZ * |α|) ∧
    (∀ p ∈ P, ∀ α, |α| ≤ δ0 → ∀ x, |x| ≤ 2 * η → η / 4 ≤ |x| →
      4 * max (muS 0 p α) 0 + cz1 ≤ zetaR p α x ^ 2) ∧
    (∀ p ∈ P, ∀ α, |α| ≤ δ0 → ∀ x, 2 * η ≤ |x| → 0 ≤ ucR p + x → ucR p + x ≤ F.L →
      4 * max (muS 0 p α) 0 + cz1 ≤ zetaR p α x ^ 2) ∧
    (∀ p ∈ P, ∀ α, |α| ≤ δ0 → ∀ x, η / 4 ≤ |x| → 0 ≤ ucR p + x → ucR p + x ≤ F.L →
      (x < 0 → zetaR p α x ≤ 0) ∧ (0 < x → 0 ≤ zetaR p α x)) ∧
    (∀ p ∈ P, ∀ α, |α| ≤ δ0 → ∀ x, |x| ≤ 2 * η → 0 ≤ ucR p + x → ucR p + x ≤ F.L →
      Tfun F.L ((mirrorFamily F).G 0 p) ((mirrorFamily F).B 0 p) ((mirrorFamily F).bandHi p - α) (ucR p + x) ≤ 0 →
      cT * (-Tfun F.L ((mirrorFamily F).G 0 p) ((mirrorFamily F).B 0 p) ((mirrorFamily F).bandHi p - α) (ucR p + x)) ≤
        zetaR p α x ^ 2 / 4 - muS 0 p α) := by
  have _ := q
  have hf_mir : ∀ p u, fPlus F.L ((mirrorFamily F).G 0 p) ((mirrorFamily F).B 0 p) u =
      fPlus F.L (F.G 0 p) (F.B 0 p) (F.L - u) := by
    intro p u; unfold fPlus E0 mirrorFamily; ring_nf
  have hT_mir : ∀ p X u, Tfun F.L ((mirrorFamily F).G 0 p) ((mirrorFamily F).B 0 p) X u =
      Tfun F.L (F.G 0 p) (F.B 0 p) X (F.L - u) := by
    intro p X u; unfold Tfun E0 mirrorFamily; ring_nf
  have hband_eq : ∀ p, (mirrorFamily F).bandHi p = F.bandHi p := by
    intro p
    unfold SymbolFamily.bandHi Xsp
    change sSup (fPlus F.L ((mirrorFamily F).G 0 p) ((mirrorFamily F).B 0 p) '' Icc 0 F.L) =
      sSup (fPlus F.L (F.G 0 p) (F.B 0 p) '' Icc 0 F.L)
    have himg : fPlus F.L ((mirrorFamily F).G 0 p) ((mirrorFamily F).B 0 p) '' Icc 0 F.L =
        fPlus F.L (F.G 0 p) (F.B 0 p) '' Icc 0 F.L := by
      ext y; simp only [Set.mem_image, Set.mem_Icc, hf_mir]
      constructor
      · rintro ⟨u, ⟨hu0, huL⟩, rfl⟩; exact ⟨F.L - u, ⟨by linarith, by linarith⟩, rfl⟩
      · rintro ⟨v, ⟨hv0, hvL⟩, rfl⟩; exact ⟨F.L - v, ⟨by linarith, by linarith⟩, by ring_nf⟩
    rw [himg]
  refine ⟨fun p _ => hband_eq p, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := h_uc_spec p hp
    refine ⟨by linarith, by linarith, ?_⟩
    rw [hf_mir, hband_eq]
    simpa [sub_sub_cancel] using h3
  · intro p hp
    obtain ⟨h1, h2⟩ := h_ucη_in p hp
    constructor <;> linarith
  · intro p hp X hX u hu hgap
    rw [hband_eq] at hX
    have hgap' : η / 4 ≤ |(F.L - u) - ucL p| := by
      have : (F.L - u) - ucL p = -(u - (F.L - ucL p)) := by ring
      rw [this, abs_neg]
      exact hgap
    have hu' : F.L - u ∈ Icc 0 F.L := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    rw [hT_mir]
    exact h_geom_far p hp X hX (F.L - u) hu' hgap'
  · intro p hp α hα x hx
    have hderiv : deriv (fun y => -zetaL p α (-y)) x = deriv (zetaL p α) (-x) := by
      change deriv (-(fun y => zetaL p α (-y))) x = deriv (zetaL p α) (-x)
      rw [deriv.neg, deriv_comp_neg (f := zetaL p α), neg_neg]
    rw [hderiv]
    exact h_zeta_deriv p hp α hα (-x) (by simpa [abs_neg] using hx)
  · intro p hp; simp [h_zeta_zero p hp]
  · intro p hp α hα; simp [h_zeta_alpha p hp α hα]
  · intro p hp α hα x hx hgap
    simpa [neg_sq] using h_zeta_far p hp α hα (-x) (by simpa [abs_neg] using hx) (by simpa [abs_neg] using hgap)
  · intro p hp α hα x hgap h0 hL
    have h1 : 0 ≤ ucL p + (-x) := by linarith
    have h2 : ucL p + (-x) ≤ F.L := by linarith
    simpa [neg_sq] using h_zeta_far_out p hp α hα (-x) (by simpa [abs_neg] using hgap) h1 h2
  · intro p hp α hα x hgap h0 hL
    have h1 : 0 ≤ ucL p + (-x) := by linarith
    have h2 : ucL p + (-x) ≤ F.L := by linarith
    obtain ⟨hn, hp_pos⟩ := h_zeta_sign_out p hp α hα (-x) (by simpa [abs_neg] using hgap) h1 h2
    refine ⟨fun hx_neg => ?_, fun hx_pos => ?_⟩
    · have : 0 ≤ zetaL p α (-x) := hp_pos (by linarith)
      linarith
    · have : zetaL p α (-x) ≤ 0 := hn (by linarith)
      linarith
  · intro p hp α hα x hx h0 hL hT
    have h1 : 0 ≤ ucL p + (-x) := by linarith
    have h2 : ucL p + (-x) ≤ F.L := by linarith
    rw [hband_eq, hT_mir] at hT ⊢
    have hu_eq : F.L - (F.L - ucL p + x) = ucL p + (-x) := by ring
    rw [hu_eq] at hT ⊢
    simpa [neg_sq] using h_zeta_T p hp α hα (-x) (by simpa [abs_neg] using hx) h1 h2 hT

/-! ### 4. `SoftPhaseInputs.bandHi_close` and `Layer4Inputs` cover constants -/

/-- **`SoftPhaseInputs.bandHi_close`**: joint continuity of `(frozenFamily F Kidx).bandHi`
on compact `K × [-1, 1]` yields `t0 ∈ (0, 1]` with `|bandHi (μ, t) - bandHi (μ, 0)| ≤ ρ`. -/
theorem softPhase_bandHi_close {Par : Type*} [TopologicalSpace Par]
    (F : SymbolFamily Par) {K : Set Par} (hK : IsCompact K) (Kidx : ℕ)
    (hD : DM F K (2 * Kidx + 1)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ t0 : ℝ, 0 < t0 ∧ t0 ≤ 1 ∧ ∀ μ ∈ K, ∀ t ∈ Icc (-t0) t0,
      |(frozenFamily F Kidx).bandHi (μ, t) - (frozenFamily F Kidx).bandHi (μ, 0)| ≤ ρ := by
  rcases K.eq_empty_or_nonempty with rfl | hK_ne
  · exact ⟨1, zero_lt_one, le_rfl, fun _ h => False.elim h⟩
  have hCont := frozen_bandHi_contOn F hK hD (Kidx := Kidx)
  have hpt : ∀ μ0 : K, ∃ U ∈ 𝓝[K] μ0.1, ∃ t0 : ℝ, 0 < t0 ∧ t0 ≤ 1 ∧
      ∀ p ∈ paramSet U t0, |(frozenFamily F Kidx).bandHi p - (frozenFamily F Kidx).bandHi (μ0.1, 0)| < ρ / 2 := by
    intro ⟨μ0, hμ0⟩
    have hW : {p : Par × ℝ | |(frozenFamily F Kidx).bandHi p - (frozenFamily F Kidx).bandHi (μ0, 0)| < ρ / 2} ∈
        𝓝[paramSet K 1] (μ0, (0 : ℝ)) := by
      simpa [Metric.ball, Real.dist_eq] using
        hCont (μ0, 0) ⟨hμ0, by norm_num⟩ (Metric.ball_mem_nhds _ (half_pos hρ))
    obtain ⟨U, hU, t0, ht0, ht0_le, hsub⟩ := paramSet_nhd_of_prod hW
    exact ⟨U, hU, t0, ht0, ht0_le, fun p hp => hsub hp⟩
  choose Uf hUf tf htf_pos htf_le hUsub using hpt
  have hopen : ∀ μ0 : K, ∃ V : Set Par, IsOpen V ∧ μ0.1 ∈ V ∧ V ∩ K ⊆ Uf μ0 := by
    intro μ0
    obtain ⟨V, hV_open, hμ0_V, hsub⟩ := mem_nhdsWithin.mp (hUf μ0)
    exact ⟨V, hV_open, hμ0_V, fun x hx => hsub ⟨hx.1, hx.2⟩⟩
  choose Vf hVf_open hVf_mem hVf_sub using hopen
  have hcov_K : K ⊆ ⋃ μ0 : K, Vf μ0 := fun μ hμ =>
    Set.mem_iUnion.mpr ⟨⟨μ, hμ⟩, hVf_mem ⟨μ, hμ⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover Vf hVf_open hcov_K
  have hs_ne : s.Nonempty := by
    rcases hK_ne with ⟨μ0, hμ0⟩
    have := hs hμ0
    simp only [Set.mem_iUnion] at this
    rcases this with ⟨x, hx, _⟩
    exact ⟨x, hx⟩
  let t0 : ℝ := s.inf' hs_ne tf
  have ht0_pos : 0 < t0 := (Finset.lt_inf'_iff hs_ne).mpr fun x _ => htf_pos x
  have ht0_le : t0 ≤ 1 := by
    rcases hs_ne with ⟨x0, hx0⟩
    exact (Finset.inf'_le _ hx0).trans (htf_le x0)
  refine ⟨t0, ht0_pos, ht0_le, fun μ hμ t ht => ?_⟩
  have hμ_cov := hs hμ
  simp only [Set.mem_iUnion] at hμ_cov
  rcases hμ_cov with ⟨x0, hx0_s, hμ_V⟩
  have hμ_U : μ ∈ Uf x0 := hVf_sub x0 ⟨hμ_V, hμ⟩
  have ht_x0 : t ∈ Icc (-tf x0) (tf x0) := by
    have htle : t0 ≤ tf x0 := Finset.inf'_le _ hx0_s
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h0_x0 : (0 : ℝ) ∈ Icc (-tf x0) (tf x0) := ⟨by linarith [htf_pos x0], (htf_pos x0).le⟩
  have h1 := hUsub x0 (μ, t) ⟨hμ_U, ht_x0⟩
  have h2 := hUsub x0 (μ, 0) ⟨hμ_U, h0_x0⟩
  calc |(frozenFamily F Kidx).bandHi (μ, t) - (frozenFamily F Kidx).bandHi (μ, 0)|
      ≤ |(frozenFamily F Kidx).bandHi (μ, t) - (frozenFamily F Kidx).bandHi (x0.1, 0)| +
        |(frozenFamily F Kidx).bandHi (μ, 0) - (frozenFamily F Kidx).bandHi (x0.1, 0)| := by
          have := abs_sub_le ((frozenFamily F Kidx).bandHi (μ, t))
            ((frozenFamily F Kidx).bandHi (x0.1, 0)) ((frozenFamily F Kidx).bandHi (μ, 0))
          simpa only [abs_sub_comm ((frozenFamily F Kidx).bandHi (x0.1, 0))] using this
    _ ≤ ρ / 2 + ρ / 2 := by linarith
    _ = ρ := add_halves ρ

/-- **`Layer4Inputs` cover constants (`hw`, `hlt`, `hJhi`, `hJlo`, `hwb`, `hKidx`)**:
elementary packaging from a common soft window width `w` satisfying `bandHi < Jhi + w`,
`Jlo - w < bandLo`, and `w ≤ bandHi - bandLo`, with `Kidx := (M + 1) / 2`. -/
theorem layer4_cover_consts {Par : Type*} (T : SymbolFamily Par) (K : Set Par) (M : ℕ)
    {w wu wl Jlo Jhi : ℝ} (hw_u : wu = w) (hw_l : wl = w)
    {nb : ℕ} {lo hi : Fin nb → ℝ} (hblk : ∀ ν, lo ν < hi ν)
    (hcov : ∀ μ ∈ K, T.bandLo μ < Jlo ∧ Jlo ≤ Jhi ∧ Jhi < T.bandHi μ ∧
      T.bandHi μ < Jhi + w ∧ Jlo - w < T.bandLo μ)
    (hwidth : ∀ μ ∈ K, w ≤ T.bandHi μ - T.bandLo μ) :
    let Kidx : ℕ := (M + 1) / 2
    wl = wu ∧ (∀ ν, lo ν < hi ν) ∧
      (∀ μ ∈ K, T.bandHi μ - wu < Jhi) ∧
      (∀ μ ∈ K, Jlo < T.bandLo μ + wu) ∧
      (∀ μ ∈ K, wu ≤ T.bandHi μ - T.bandLo μ) ∧
      Kidx = (M + 1) / 2 := by
  refine ⟨by rw [hw_l, hw_u], hblk, ?_, ?_, ?_, rfl⟩
  · intro μ hμ; rw [hw_u]; linarith [(hcov μ hμ).2.2.2.1]
  · intro μ hμ; rw [hw_u]; linarith [(hcov μ hμ).2.2.2.2]
  · intro μ hμ; rw [hw_u]; exact hwidth μ hμ

/-! ### Axiom verification guards -/

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.local_cover_of_geom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.local_cover_of_geom

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.local_bulk_cover_of_geom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.local_bulk_cover_of_geom

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.uPlus_mirror_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.uPlus_mirror_ne

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.mirror_bulk_overlap_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.mirror_bulk_overlap_match

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.softMirror_geom_of_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.softMirror_geom_of_left

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.softPhase_bandHi_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.softPhase_bandHi_close

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.layer4_cover_consts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.layer4_cover_consts

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.local_cover_of_geom_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.local_cover_of_geom_strict

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.uMinus_mirror_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.uMinus_mirror_ne

end FormalResearch.JacobiEigenvectors.Charts
