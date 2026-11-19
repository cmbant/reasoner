module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Assembly.LabelsAbstract
public import FormalResearch.JacobiEigenvectors.Assembly.LabelsSlope
public import FormalResearch.JacobiEigenvectors.Assembly.LabelsSoft
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssemblyBulk
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkSlope
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftCountLink

/-!
# Paper J: the bulk labels `BulkWindowLabels` (thm:A (i), "Location and labels"; item 2)

Source: Paper J `thmA.tex`, proof of `thm:A (i)`, paragraph "Location and labels" and `lem:smo-bulkphase` (3).

## The chain (paper) and where each step is

1. *Windows* (`bulk_count`, conjunct (i)): every eigenvalue in a bulk block `J_nu` is in a window `|S_0(X) - pi h (j + 1/2)| <= C h^2`; the window integer is `floor (S_0 / (pi h))`, independent of the block.
2. *Count* (`bulk_count`, uniqueness and existence): at most one eigenvalue per window inside a block, exactly one in each window whose bracketing interval lies in `S_0(J_nu)` (`bulk_kappa_sign`, `bulk_actionS0_strictAnti`).
3. *Consecutive windows* (`ScaleFacts.consec`, `Assembly/LabelsAbstract.lean`): two consecutive eigenvalues of the bulk range have consecutive windows.  A skipped window would contain an eigenvalue strictly between them (existence
   on a block that contains the whole window, by a Lebesgue number of the cover `cover_bulk`, `leb_blocks`); two eigenvalues of the same window lie in a common block (the Lebesgue number again), contradicting uniqueness.
   The quantitative slope `S_0(x, h) - S_0(y, h) >= c (y - x) - C1 h` (`block_slope_quant`, `Assembly/LabelsSlope.lean`: `bulk_slope` at `t = 0` plus the `t`-Lipschitz bound from `Sigma_bdd`) makes "close" quantitative.
4. *Anchor at the soft window `0`* (`ScaleFacts.anchor_exists`, `soft_anchor_window`): the last block contains an eigenvalue within `e` of `J_hi`, i.e. within `delta_0` of `X_s^+(mu, h)`; there `PropThaW2` (3) (`SoftLabels`, label = index)
   and `pi mu_0 = S_0` (`mu0_S0`) give `|S_0(X_a) - pi h (a + 1/2)| <= Cs h^2`: its window is its index.
5. *Induction along the eigenvalues* (`labels_of_anchor`): the eigenvalues of the bulk range are consecutive in the index, so window = index for all of them.

## Proved here (axiom-pinned)

* `bulkLabels_core`: `BulkWindowLabels (frozenFamily T Kidx) K t0 (lo nu) (hi nu)` for every block of the chart data, for a general symbol family `T`, from `PI`, the soft labels `SoftLabels` (exponent `max M 1 + 1`),
  the standing assumption `hstd`, positive bonds `hpos`, and the geometric relations `hlt` (blocks of positive length) and `hzone` (the last block reaches within `delta_0 - e` of the soft band end, uniformly).

## Differences from the paper

* `BulkWindowLabels` is stated at `t = h` only (`t = F.step N`), which is all `bulk_BSr2` uses; the paper's labels are for the matrices at `t = h`.
* The paper inducts block by block from the soft window; here the induction runs along the eigenvalue index over all of `[J_lo, J_hi]` and blocks enter only through the Lebesgue number.
* The uniform margin `e` in `hzone` is the (uniform in `mu`) form of the strict `J_hi + delta_0 > X_s^+(p)` of the chart field `cover`.

## Not formalised

Nothing beyond the named premises.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Set Filter FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

lemma exists_unif_le {nb : ℕ} (f : Fin nb → ℝ) : ∃ B, ∀ ν, f ν ≤ B :=
  ⟨∑ ν, |f ν|, fun ν => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |f i|) (fun i _ => abs_nonneg (f i)) (Finset.mem_univ ν))⟩

lemma exists_unif_pos {nb : ℕ} (f : Fin nb → ℝ) (hf : ∀ ν, 0 < f ν) : ∃ m, 0 < m ∧ ∀ ν, m ≤ f ν := by
  obtain ⟨B, hB⟩ := exists_unif_le (fun ν => (f ν)⁻¹)
  have hB' : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(max B 1)⁻¹, inv_pos.mpr hB', fun ν => ?_⟩
  rw [inv_le_comm₀ hB' (hf ν)]
  exact (hB ν).trans (le_max_left _ _)

lemma ev_mul_lt (a : ℝ) {b : ℝ} (hb : 0 < b) : ∀ᶠ h in nhds (0 : ℝ), a * h < b := by
  have : Tendsto (fun h : ℝ => a * h) (nhds 0) (nhds (a * 0)) := (continuous_const.mul continuous_id).tendsto 0
  exact this.eventually (gt_mem_nhds (by simpa using hb))

theorem bulkLabels_core {T : SymbolFamily Par} {K : Set Par} {M Kidx : ℕ} {t0 : ℝ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CI : ChartInputs T K Kidx t0 (max M 1) (2 * Kidx) U V cPC CPC)
    (PI : ∀ ν, BulkPhaseInputs (frozenFamily T Kidx) (paramSet K t0) K t0 (CI.lo ν) (CI.hi ν) M U V (CI.bulkL ν) (CI.bulkR ν))
    (ht0 : 0 < t0)
    (hstd : ∃ r, StdAssump (frozenFamily T Kidx) (paramSet K t0) (max M 1 / 2) r)
    (hlab : SoftLabels T Kidx K (max M 1) CI.softUpL)
    (hpos : ∃ h1 : ℝ, 0 < h1 ∧ ∀ μ ∈ K, ∀ N : ℕ, T.step N ≤ h1 → ∀ n : ℤ, 0 ≤ n → n < N → 0 < T.bondA μ N n)
    (hlt : ∀ ν, CI.lo ν < CI.hi ν)
    (hzone : ∃ e : ℝ, 0 < e ∧ ∀ μ ∈ K, ∀ t ∈ Icc (-t0) t0,
      (frozenFamily T Kidx).bandHi (μ, t) - CI.softUpL.δ0 + e ≤ CI.Jhi) :
    ∀ ν, BulkWindowLabels (frozenFamily T Kidx) K t0 (CI.lo ν) (CI.hi ν) := by
  obtain ⟨r, hr⟩ := hstd
  have hP : ∀ μ ∈ K, ∀ t ∈ Icc (-t0) t0, (μ, t) ∈ paramSet K t0 := fun μ hμ t ht => ⟨hμ, ht⟩
  have hP0 : ∀ μ ∈ K, (μ, (0 : ℝ)) ∈ paramSet K t0 := fun μ hμ => ⟨hμ, ⟨by linarith, ht0.le⟩⟩
  -- the global statement, uniform over the blocks
  have hcnt := fun ν => bulk_count (PI ν) CI.pc hP (CI.overlap_match ν) r hr
  choose C h0 hC hh0 N1 hN1 hbc using hcnt
  have G : ∃ η : ℝ, 0 < η ∧ ∀ μ ∈ K, ∀ N : ℕ, (frozenFamily T Kidx).step N ≤ η → (frozenFamily T Kidx).step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        IsEigenSystem ((frozenFamily T Kidx).jacobiMat (μ, (frozenFamily T Kidx).step N) N) Xs Um →
        ∀ k : Fin (N + 1), ∀ ν, Xs k ∈ Icc (CI.lo ν) (CI.hi ν) →
          |actionS0 (frozenFamily T Kidx) (μ, (frozenFamily T Kidx).step N) (Xs k)
            - Real.pi * (frozenFamily T Kidx).step N * (((k : ℕ) : ℝ) + 1 / 2)| ≤ C ν * (frozenFamily T Kidx).step N ^ 2 := by
    by_cases hKne : K.Nonempty
    swap
    · exact ⟨1, one_pos, fun μ hμ => absurd ⟨μ, hμ⟩ hKne⟩
    obtain ⟨μ0, hμ0⟩ := hKne
    have hJ : CI.Jlo ≤ CI.Jhi := (CI.cover (μ0, 0) (hP0 μ0 hμ0)).2.1
    have hq := fun ν => block_slope_quant (PI ν) ht0 (hlt ν) (bulk_slope (PI ν) ht0 hP0 hr)
    choose c C1 hc hC1 hqs using hq
    obtain ⟨c', hc', hcc'⟩ := exists_unif_pos c hc
    obtain ⟨C1m, hC1m⟩ := exists_unif_le C1
    set C1' : ℝ := max C1m 0 with hC1'
    obtain ⟨δ, hδ, hleb⟩ := leb_blocks CI.lo CI.hi CI.Jlo CI.Jhi CI.cover_bulk CI.blocks_in_J
    obtain ⟨ν1, -, -, -, hν1⟩ := CI.cover_bulk CI.Jhi hJ le_rfl
    have hνtop : CI.hi ν1 = CI.Jhi := by
      rcases hν1 with h | h
      · exact absurd h (not_lt.mpr (CI.blocks_in_J ν1).2.2)
      · exact h
    have hνlt : CI.lo ν1 < CI.Jhi := hνtop ▸ hlt ν1
    obtain ⟨e, he, hze⟩ := hzone
    obtain ⟨Cs, h0s, hh0s, hsoft⟩ := soft_anchor_window CI (M' := max M 1) (le_max_right _ _) hlab
    obtain ⟨h1p, hh1p, hposT⟩ := hpos
    have hpi := Real.pi_pos
    have hC1'0 : 0 ≤ C1' := le_max_right _ _
    have hev : ∀ᶠ h in nhds (0 : ℝ), h < 1 ∧ h < h1p ∧ h < h0s ∧ Cs * h < Real.pi / 8 ∧ (Real.pi + C1') * h < c' * (δ / 2) ∧
        (2 * Real.pi + C1') * h < c' * min (CI.Jhi - CI.lo ν1) e ∧
        ∀ ν, (h < h0 ν ∧ h < T.L / ((N1 ν : ℝ) + 1) ∧ C ν * h < Real.pi / 8) := by
      filter_upwards [ev_mul_lt 1 one_pos, ev_mul_lt 1 hh1p, ev_mul_lt 1 hh0s, ev_mul_lt Cs (by positivity : 0 < Real.pi / 8),
        ev_mul_lt (Real.pi + C1') (by positivity : 0 < c' * (δ / 2)),
        ev_mul_lt (2 * Real.pi + C1') (mul_pos hc' (lt_min (sub_pos.mpr hνlt) he)),
        Filter.eventually_all.mpr (fun ν => (ev_mul_lt 1 (hh0 ν)).and ((ev_mul_lt 1 (div_pos T.L_pos (by positivity : (0 : ℝ) < (N1 ν : ℝ) + 1))).and
          (ev_mul_lt (C ν) (by positivity : 0 < Real.pi / 8))))] with h a1 a2 a3 a4 a5 a6 a7
      simp only [one_mul] at a1 a2 a3
      refine ⟨a1, a2, a3, a4, a5, a6, fun ν => ?_⟩
      obtain ⟨b1, b2, b3⟩ := a7 ν
      simp only [one_mul] at b1 b2
      exact ⟨b1, b2, b3⟩
    obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨ε / 2, by positivity, ?_⟩
    intro μ hμ N hN ht Xs Um hE k ν hk
    have hst : 0 < (frozenFamily T Kidx).step N := FormalResearch.JB.stepSize_pos T.L_pos N
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hεs (y := (frozenFamily T Kidx).step N)
      (by rw [Real.dist_eq, sub_zero, abs_of_pos hst]; linarith)
    have ht' : (frozenFamily T Kidx).step N ∈ Icc (-t0) t0 := ⟨by linarith, ht⟩
    have hp : (μ, (frozenFamily T Kidx).step N) ∈ paramSet K t0 := hP μ hμ _ ht'
    have hNN : ∀ ν, N1 ν ≤ N := by
      intro ν
      by_contra hcon
      rw [not_le] at hcon
      have h1 : ((N : ℝ) + 1) < (N1 ν : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hcon
      have h2 : T.L / ((N1 ν : ℝ) + 1) < T.L / ((N : ℝ) + 1) := div_lt_div_of_pos_left T.L_pos (by positivity) h1
      have h3 : (frozenFamily T Kidx).step N = T.L / ((N : ℝ) + 1) := rfl
      linarith [(a7 ν).2.1]
    have h1N : 1 ≤ N := (hN1 ν1).trans (hNN ν1)
    have hpos' : ∀ n : ℤ, 0 ≤ n → n < N → 0 < (frozenFamily T Kidx).bondA (μ, (frozenFamily T Kidx).step N) N n := by
      intro n hn1 hn2
      rw [show (frozenFamily T Kidx).step N = T.step N from rfl, frozen_bondA_at_step]
      exact hposT μ hμ N a2.le n hn1 hn2
    have hF : ScaleFacts (fun X => actionS0 (frozenFamily T Kidx) (μ, (frozenFamily T Kidx).step N) X) (Set.range Xs) CI.Jlo CI.Jhi
        CI.lo CI.hi ((frozenFamily T Kidx).step N) (fun ν => C ν * (frozenFamily T Kidx).step N ^ 2) c' C1' δ := by
      refine ⟨hst, hc', hδ, ?_, a5, ?_, ?_, ?_, CI.blocks_in_J, hleb, ?_, ?_, ?_, ?_⟩
      · intro ν
        have h3 := mul_le_mul_of_nonneg_right (a7 ν).2.2.le hst.le
        nlinarith
      · exact strictAntiOn_of_blocks hδ _ hleb (fun ν => bulk_actionS0_strictAnti (CI.bulkL ν) hP hr μ hμ _ ht')
      · exact continuousOn_of_blocks hδ _ hleb (fun ν => actionS0_continuousOn (PI ν) hμ ht')
      · exact fun x _ => actionS0_nonneg _ _ x
      · intro ν x hx y hy hxy
        have hSx := (PI ν).Sigma_zero μ hμ x hx _ ht'
        have hSy := (PI ν).Sigma_zero μ hμ y hy _ ht'
        have h3 := hqs ν μ hμ _ ⟨hst.le, ht⟩ x hx y hy hxy
        have e1 : actionS0 (frozenFamily T Kidx) (μ, (frozenFamily T Kidx).step N) x = (PI ν).Sigma μ 0 x ((frozenFamily T Kidx).step N) := hSx.symm
        have e2 : actionS0 (frozenFamily T Kidx) (μ, (frozenFamily T Kidx).step N) y = (PI ν).Sigma μ 0 y ((frozenFamily T Kidx).step N) := hSy.symm
        have h4 := mul_le_mul_of_nonneg_right (hcc' ν) (sub_nonneg.2 hxy)
        have h5 := mul_le_mul_of_nonneg_right ((hC1m ν).trans (le_max_left C1m 0)) hst.le
        show c' * (y - x) - C1' * (frozenFamily T Kidx).step N ≤ actionS0 _ _ x - actionS0 _ _ y
        rw [e1, e2]
        have h6 : C1 ν * (frozenFamily T Kidx).step N ≤ C1m * (frozenFamily T Kidx).step N :=
          mul_le_mul_of_nonneg_right (hC1m ν) hst.le
        nlinarith [le_max_left C1m 0]
      · intro ν x hx hxν
        obtain ⟨i, rfl⟩ := hx
        exact (hbc ν μ hμ _ ht' N (hNN ν) (a7 ν).1.le hpos').1 (Xs i) hxν (casD_eig_zero hpos' h1N Xs Um hE i)
      · intro ν j x hx hxν x' hx' hx'ν hw hw'
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨i', rfl⟩ := hx'
        exact (hbc ν μ hμ _ ht' N (hNN ν) (a7 ν).1.le hpos').2.1 j (Xs i) hxν (Xs i') hx'ν
          (casD_eig_zero hpos' h1N Xs Um hE i) (casD_eig_zero hpos' h1N Xs Um hE i') hw hw'
      · intro ν j hbr
        obtain ⟨X, hX, hD, hw⟩ := (hbc ν μ hμ _ ht' N (hNN ν) (a7 ν).1.le hpos').2.2 j hbr
        obtain ⟨i, hi⟩ := casD_zero_exists_eig hpos' h1N hD Xs Um hE
        exact ⟨X, ⟨i, hi⟩, hX, hw⟩
    -- the anchor
    have hbig : (2 * Real.pi + C1') * (frozenFamily T Kidx).step N ≤ c' * min (CI.Jhi - CI.lo ν1) e := a6.le
    obtain ⟨y, ⟨a, rfl⟩, hy1, hy2, hyB⟩ := hF.anchor_exists ν1 hνtop hνlt e he hbig
    have hE' : IsEigenSystem (T.jacobiMat μ N) Xs Um := by
      rw [← frozenFamily_jacobiMat_at_step T Kidx μ N]; exact hE
    have hbandlt : CI.Jhi < (frozenFamily T Kidx).bandHi (μ, (frozenFamily T Kidx).step N) := (CI.cover _ hp).2.2.1
    have hz := hze μ hμ _ ht'
    have hq1 : (frozenFamily T Kidx).bandHi (μ, (frozenFamily T Kidx).step N) - Xs a ≤ CI.softUpL.δ0 := by linarith
    have hq2 : Xs a ≤ (frozenFamily T Kidx).bandHi (μ, (frozenFamily T Kidx).step N) := by linarith
    have hsa := hsoft μ hμ N a3.le ht Xs Um hE' a hq1 hq2
    have hal : ScaleFacts.lab (fun X => actionS0 (frozenFamily T Kidx) (μ, (frozenFamily T Kidx).step N) X)
        ((frozenFamily T Kidx).step N) (Xs a) = (a : ℕ) := by
      unfold ScaleFacts.lab
      refine floor_lab_eq hF.pih_pos ?_
      have h3 : Cs * (frozenFamily T Kidx).step N ^ 2 ≤ Real.pi * (frozenFamily T Kidx).step N / 8 := by
        have := mul_le_mul_of_nonneg_right a4.le hst.le
        nlinarith
      exact hsa.trans h3
    have hkB : Xs k ∈ Icc CI.Jlo CI.Jhi := ⟨(CI.blocks_in_J ν).1.trans hk.1, hk.2.trans (CI.blocks_in_J ν).2.2⟩
    have hlk := labels_of_anchor Xs hE.anti hF a hyB hal k hkB
    have hw := hF.win_lab (x := Xs k) ⟨k, rfl⟩ hk
    rw [hlk] at hw
    exact hw
  intro ν0
  obtain ⟨η, hη, hG⟩ := G
  refine ⟨C ν0, η, hη, ?_⟩
  intro μ hμ t ht N hN htN Xs Um hE k hk
  subst htN
  exact hG μ hμ N hN ht.2 Xs Um hE k ν0 hk

/-- `BulkWindowLabels` for a smaller `t0'` gives it for `t0` (the labels are at `t = h` only). -/
theorem bulkWindowLabels_of_le {F : SymbolFamily (Par × ℝ)} {K : Set Par} {t0 t0' Jlo Jhi : ℝ} (hle : t0' ≤ t0) (h0 : 0 < t0')
    (H : BulkWindowLabels F K t0' Jlo Jhi) : BulkWindowLabels F K t0 Jlo Jhi := by
  obtain ⟨Cl, h0l, hh0, hl⟩ := H
  refine ⟨Cl, min h0l t0', lt_min hh0 h0, fun μ hμ t ht N hN htN => ?_⟩
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hNt : F.step N ≤ t0' := hN.trans (min_le_right _ _)
  exact hl μ hμ t ⟨by rw [htN]; linarith, by rw [htN]; exact hNt⟩ N (hN.trans (min_le_left _ _)) htN

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulkLabels_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulkLabels_core

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulkWindowLabels_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulkWindowLabels_of_le

end FormalResearch.JacobiEigenvectors.TheoremA

end
