module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbConstants
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbSoftDiff
public import FormalResearch.JacobiEigenvectors.TheoremB.SoftOneStep
public import FormalResearch.JacobiEigenvectors.TheoremB.SoftExtChart
public import FormalResearch.JacobiEigenvectors.TheoremB.BulkSchur

/-!
# Paper J, Theorem B, L3.5c, part 11: the left half chart of a soft block (generic over the soft chart pair)

Source: Paper J `app_thmB.tex`, proof of `prop:thb-inputs`, the soft charts: (I1)--(I4) for the left half collar `rows a + 1 .. n_c` of the upper soft edge.

For a soft chart pair `(CL, CR)` of a family `Fz` (orders `m` and `m + 1`: `(CL1, CR1)`), a parameter `p`, an eigen-system and host matrices `G0, G1` whose columns on `cols` are the sewn columns of the two orders (`compMatrix` on the upper
edge), `softLeftChart` is the `JB.Chart` with the rows `lo .. n_c` (`lo = floor((u_c - eta/2)/h - 1/2) + 1`), `used = univ`, the half-window `P_k = softPk`, and `sigma^{[r]}_k = lambda_L^{[r]}/(kappa_bal hat N^{[r]})`.

## Proved here

* `soft_left_ok`: constants `cs, N_0, h_0` (depending on `Ch`, the host bound of `G0, G1`) such that for every `p in P`, `N >= N_0`, `h <= h_0`, every eigen-system and every column set in the window, the left chart is `Chart.Ok`, `G0, G1` match it on all rows, and
  it covers the rows `lo .. n_c`.

## Differences from the paper

The hosts are the final matrices `G0, G1` themselves (as for the bulk blocks).  The generic form (any family `Fz`, abstract `G0, G1` with the sewn-column entries as a hypothesis) is what the lower edge needs (`negFamily`).

## Not formalised

The right half (`ThbSoftRight.lean`), the cover bound (`ThbSoftUp.lean`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine FormalResearch.JB

open scoped Classical

theorem chartSchurK_congr {a b c d a' b' c' d' : ℝ} (S cT cα H : ℝ) (h1 : b - a = b' - a') (h2 : d - c = d' - c') :
    chartSchurK a b c d S cT cα H = chartSchurK a' b' c' d' S cT cα H := by
  simp only [chartSchurK, schurInvK, schurDivK, schurC2K, h1, h2]

section Defs

variable {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}

/-- First row of the left chart: the row after the last row below the collar. -/
def softLo (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (p : Par × ℝ) (N : ℕ) : ℕ :=
  (⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋ + 1).toNat

/-- Number of rows `lo .. n_c` of the left chart. -/
def softRL (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (p : Par × ℝ) (N : ℕ) : ℕ :=
  (nearestRow (Fz.step N) (CL.uc p)).toNat + 1 - softLo CL p N

/-- The left half chart of the soft block. -/
def softLeftChart {Jlo Jhi ulo uhi : (Par × ℝ) → ℝ}
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1))
    (CL1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1)) (CR1 : SoftEdgeChart (mirrorFamily Fz) P (m + 1) q U V (fun _ => 1))
    (TIL : TransferInputsDn Fz P Jlo Jhi m CL.chain CL1.chain 2 ulo uhi)
    (p : Par × ℝ) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1)))
    (G0 G1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hlo : softLo CL p N + softRL CL p N ≤ N + 1) :
    Chart (N + 1) (softRL CL p N) cols :=
  softJBChart CL CL1 TIL p N Xs cols (softLo CL p N) (softRL CL p N) hlo false Finset.univ
    (fun k => softPk N (softLo CL p N) (softRL CL p N) false
      ((softWindow CL p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p))))
    (fun k => CL.lamL p (Xs k) N / (kappaBal (CL.aOf p (Xs k) N) * softNorm CL CR p (Xs k) N))
    (fun k => CL1.lamL p (Xs k) N / (kappaBal (CL1.aOf p (Xs k) N) * softNorm CL1 CR1 p (Xs k) N)) G0 G1

end Defs

section Left

variable {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

theorem soft_left_ok (hf : ParabolicCylinderFacts U V cPC CPC)
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1))
    (CL1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1)) (CR1 : SoftEdgeChart (mirrorFamily Fz) P (m + 1) q U V (fun _ => 1))
    (hM : SoftMirror CL CR) (hM1 : SoftMirror CL1 CR1)
    (hz : CL1.zeta = CL.zeta) (hmu : CL1.muS = CL.muS) (huc : CL1.uc = CL.uc) (hδ1 : CL1.δ0 = CL.δ0) (hη1 : CL1.η = CL.η)
    (hm : 1 ≤ m) (r : ℕ) (hr : StdAssump Fz P (q / 2) r)
    (TIL : TransferInputsDn Fz P (fun p => Fz.bandHi p - CL.δ0) (fun p => Fz.bandHi p + CL.δ0) m CL.chain CL1.chain 2
      (fun p => CL.uc p - CL.η / 2) (fun p => CL.uc p + CL.η / 2))
    (Ch : ℝ) (hCh : 0 ≤ Ch) :
    ∃ (cs : OneStepConsts) (N0 : ℕ) (h0 : ℝ), 0 < h0 ∧ h0 ≤ 1 ∧ ∀ p ∈ P, ∀ N : ℕ, N0 ≤ N → Fz.step N ≤ h0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
      ∀ cols : Finset (Fin (N + 1)), (∀ k ∈ cols, |Xs k - Fz.bandHi p| ≤ CL.δ0) →
      ∀ G0 G1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
        (∀ k ∈ cols, ∀ i : Fin (N + 1), G0 i k =
          if ((i : ℕ) : ℤ) ≤ nearestRow (Fz.step N) (CL.uc p) then CL.psiHatL p (Xs k) N ((i : ℕ) : ℤ) / softNorm CL CR p (Xs k) N
          else softKappa CL CR p (Xs k) N * CR.psiHatL p (Xs k) N ((N : ℤ) - ((i : ℕ) : ℤ)) / softNorm CL CR p (Xs k) N) →
        (∀ k ∈ cols, ∀ i : Fin (N + 1), G1 i k =
          if ((i : ℕ) : ℤ) ≤ nearestRow (Fz.step N) (CL1.uc p) then CL1.psiHatL p (Xs k) N ((i : ℕ) : ℤ) / softNorm CL1 CR1 p (Xs k) N
          else softKappa CL1 CR1 p (Xs k) N * CR1.psiHatL p (Xs k) N ((N : ℤ) - ((i : ℕ) : ℤ)) / softNorm CL1 CR1 p (Xs k) N) →
        (∀ j : Fin (N + 1), jbL2 Finset.univ (fun i => G0 i j - Um i j) ≤ Ch * Fz.step N ^ m) →
        (∀ j : Fin (N + 1), jbL2 Finset.univ (fun i => G1 i j - Um i j) ≤ Ch * Fz.step N ^ (m + 1) * Real.log (1 / Fz.step N)) →
        ∃ hlo : softLo CL p N + softRL CL p N ≤ N + 1,
          (softLeftChart CL CR CL1 CR1 TIL p N Xs cols G0 G1 hlo).Ok cs m (Fz.step N) Um ∧
          (∀ (n) (k : cols), G0 ((softLeftChart CL CR CL1 CR1 TIL p N Xs cols G0 G1 hlo).row n) k =
            (softLeftChart CL CR CL1 CR1 TIL p N Xs cols G0 G1 hlo).H0 (Fz.step N) n k) ∧
          (∀ (n) (k : cols), G1 ((softLeftChart CL CR CL1 CR1 TIL p N Xs cols G0 G1 hlo).row n) k =
            (softLeftChart CL CR CL1 CR1 TIL p N Xs cols G0 G1 hlo).H1 (Fz.step N) n k) ∧
          (∀ i : Fin (N + 1), (softLo CL p N : ℤ) ≤ ((i : ℕ) : ℤ) → ((i : ℕ) : ℤ) ≤ nearestRow (Fz.step N) (CL.uc p) →
            ∃ n : Fin (softRL CL p N), (softLeftChart CL CR CL1 CR1 TIL p N Xs cols G0 G1 hlo).row n = i) := by
  obtain ⟨Cs, hs0, hs0p, hsp⟩ := stepZero Fz P (q / 2) r hr
  obtain ⟨hE1, hhE1, HEXT⟩ := softJBChart_ext_row (Jlo := fun p => Fz.bandHi p - CL.δ0) (Jhi := fun p => Fz.bandHi p + CL.δ0)
    (ulo := fun p => CL.uc p - CL.η / 2) (uhi := fun p => CL.uc p + CL.η / 2) hf CL CR CL1 CR1 hM hM1 hδ1 r hr
  obtain ⟨C4, hu1, hC40, hupos, HUB⟩ := softJBChart_overlap_ub_P (Jlo := fun p => Fz.bandHi p - CL.δ0) (Jhi := fun p => Fz.bandHi p + CL.δ0)
    (ulo := fun p => CL.uc p - CL.η / 2) (uhi := fun p => CL.uc p + CL.η / 2) hf CL CL1 hδ1
  obtain ⟨c0, hl1, hc0pos, hlpos, HLB⟩ := softJBChart_overlap_lb_left (Jlo := fun p => Fz.bandHi p - CL.δ0) (Jhi := fun p => Fz.bandHi p + CL.δ0)
    (ulo := fun p => CL.uc p - CL.η / 2) (uhi := fun p => CL.uc p + CL.η / 2) hf CL CR CL1 hM hm Cs
  obtain ⟨hA, hhA, HA⟩ := soft_a_data hf CL CR hm hM r hr
  have hηpos : 0 < CL.η := CL.consts_pos.2.1
  have hδpos : 0 < CL.δ0 := CL.consts_pos.1
  obtain ⟨hrect, hcTp, hcαp, hS0, hωp⟩ := TIL.consts_pos
  obtain ⟨h0, hh0pos, hle⟩ : ∃ h0 : ℝ, 0 < h0 ∧ ∀ x : ℝ, x ≤ h0 → x ≤ 1 ∧ x ≤ CL.η / 4 ∧ x ≤ hE1 ∧ x ≤ hu1 ∧ x ≤ hl1 ∧ x ≤ hs0 ∧ x ≤ hA ∧
      x ≤ asmH0 CL := by
    refine ⟨min 1 (min (CL.η / 4) (min hE1 (min hu1 (min hl1 (min hs0 (min hA (asmH0 CL))))))), ?_, fun x hx => ?_⟩
    · simp only [lt_min_iff]
      exact ⟨one_pos, by linarith, hhE1, hupos, hlpos, hs0p, hhA, asmH0_pos CL⟩
    · simp only [le_min_iff] at hx
      exact hx
  set cs : OneStepConsts :=
    ⟨0, Ch, max (chartSchurK 0 CL.η 0 (2 * CL.δ0) TIL.S TIL.cT TIL.cα 1) 0, TIL.ωmax, TIL.cT, TIL.cα, c0, C4, 1,
      hCh, le_max_right _ _, hωp, hcTp, hcαp, hc0pos, hC40, zero_le_one⟩ with hcs
  refine ⟨cs, max CL.N0 (max CR.N0 (max CL1.N0 TIL.N0)), h0, hh0pos, (hle h0 le_rfl).1, ?_⟩
  intro p hp N hN hstep Xs Um hE cols hwin G0 G1 hG0 hG1 hc0 hc1
  simp only [max_le_iff] at hN
  obtain ⟨hN0L, hN0R, hN1L, hNT⟩ := hN
  have hst : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L := step_mul_succ Fz N
  obtain ⟨hh1, hsη, hsE, hsu, hsl, hss0, hsA, hsasm⟩ := hle _ hstep
  obtain ⟨hu1', hu2'⟩ := CL.ucη_in p hp
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ :=
    soft_geom (N := N) hst hηpos hsη hLs hu1' hu2'
  set a : ℤ := ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋ with hadef
  set nc : ℤ := nearestRow (Fz.step N) (CL.uc p) with hncdef
  have hlo_int : (softLo CL p N : ℤ) = a + 1 := by unfold softLo; omega
  have hRL_int : (softRL CL p N : ℤ) = nc - a := by
    unfold softRL
    rw [show (softLo CL p N : ℤ) = a + 1 from hlo_int] at *
    have : (nc.toNat : ℤ) = nc := by omega
    unfold softLo at *
    omega
  have hlo : softLo CL p N + softRL CL p N ≤ N + 1 := by
    have : ((softLo CL p N + softRL CL p N : ℕ) : ℤ) ≤ ((N + 1 : ℕ) : ℤ) := by push_cast; omega
    exact_mod_cast this
  have hX : ∀ k : cols, Xs k ∈ Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0) := fun k => by
    have := hwin k k.2
    rw [abs_le] at this
    exact ⟨by linarith, by linarith⟩
  have hX' : ∀ k : cols, |Xs k - Fz.bandHi p| ≤ CL.δ0 := fun k => hwin k k.2
  have hsame : ∀ k : cols, (CL.chain p (Xs k) N).wf 2 = (CL1.chain p (Xs k) N).wf 2 :=
    fun k => (TIL.same_ladder p hp (Xs k) (hX k) N hNT).2.1
  have haL1 : ∀ k : cols, CL.aOf p (Xs k) N ≤ 1 := fun k =>
    ((HA p hp N (max_le hN0L hN0R) hsA Xs Um hE k (hX' k)).trans zero_le_one)
  have haL1' : ∀ k : cols, CL1.aOf p (Xs k) N ≤ 1 := fun k => by
    rw [(softChart_data_eq_P CL CL1 (fun α x => by rw [hz]) (fun r α => by rw [hmu]) (by rw [huc]) (Xs k) N).1]
    exact haL1 k
  have hrows : ∀ n : Fin (softRL CL p N), 1 ≤ chartRowDn N (softLo CL p N) (softRL CL p N) false n ∧
      CL.uc p - CL.η / 2 ≤ uNode (Fz.step N) (chartRowDn N (softLo CL p N) (softRL CL p N) false n) ∧
      uNode (Fz.step N) (chartRowDn N (softLo CL p N) (softRL CL p N) false n) ≤ CL.uc p + CL.η / 2 := by
    intro n
    have hn : n.val < softRL CL p N := n.isLt
    have hnz : (n.val : ℤ) < nc - a := by rw [← hRL_int]; exact_mod_cast hn
    have hr' : chartRowDn N (softLo CL p N) (softRL CL p N) false n = (softLo CL p N : ℤ) + n.val := by simp [chartRowDn]
    rw [hr']
    refine ⟨by omega, (g10 _ (by omega)).le, ?_⟩
    have := g14 ((softLo CL p N : ℤ) + n.val) (by omega)
    linarith
  -- window rows are chart rows
  have hcov : ∀ k : cols, ∀ j ∈ (softWindow CL p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)),
      ∃ n : Fin (softRL CL p N), chartRowDn N (softLo CL p N) (softRL CL p N) false n = j := by
    intro k j hj
    have hj' := Finset.mem_filter.mp hj
    have hloc := soft_win_loc CL hp (hX' k) (hsasm.trans le_rfl) hj'.1
    have hj0 : 0 ≤ j := by
      have := (Finset.mem_filter.mp hj'.1).1
      unfold rowsOf at this
      exact (Finset.mem_Icc.mp this).1
    have hja : a + 1 ≤ j := by
      by_contra hcon
      have h1 := g11 j (by omega)
      have h2 := (abs_lt.mp hloc).1
      linarith
    refine ⟨⟨(j - (softLo CL p N : ℤ)).toNat, ?_⟩, ?_⟩
    · have : ((j - (softLo CL p N : ℤ)).toNat : ℤ) < (softRL CL p N : ℤ) := by omega
      exact_mod_cast this
    · simp only [chartRowDn, Bool.false_eq_true, ite_false]
      omega
  have hzP : ∀ α x, CL1.zeta p α x = CL.zeta p α x := fun α x => by rw [hz]
  have hmuP : ∀ r α, CL1.muS r p α = CL.muS r p α := fun r α => by rw [hmu]
  have hucP : CL1.uc p = CL.uc p := by rw [huc]
  have hcoeff := softJBChart_coeff CL CL1 TIL cs hp N (max_le hN0L hN1L) hNT Xs cols (softLo CL p N) (softRL CL p N) hlo false Finset.univ
    (fun k => softPk N (softLo CL p N) (softRL CL p N) false
      ((softWindow CL p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p))))
    (fun k => CL.lamL p (Xs k) N / (kappaBal (CL.aOf p (Xs k) N) * softNorm CL CR p (Xs k) N))
    (fun k => CL1.lamL p (Xs k) N / (kappaBal (CL1.aOf p (Xs k) N) * softNorm CL1 CR1 p (Xs k) N)) G0 G1
    hX (fun X hX0 => by
      obtain ⟨h1, h2⟩ := hX0
      exact abs_le.mpr ⟨by linarith, by linarith⟩) hrows 1
    (by show |Fz.step N| ≤ 1; rw [abs_of_pos hst]; exact hh1) le_rfl le_rfl le_rfl
    (by
      show chartSchurK (CL.uc p - CL.η / 2) (CL.uc p + CL.η / 2) (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0) TIL.S TIL.cT TIL.cα 1 ≤
        max (chartSchurK 0 CL.η 0 (2 * CL.δ0) TIL.S TIL.cT TIL.cα 1) 0
      rw [chartSchurK_congr (a' := 0) (b' := CL.η) (c' := 0) (d' := 2 * CL.δ0) _ _ _ _ (by ring) (by ring)]
      exact le_max_left _ _)
  have hnc1 : nearestRow (Fz.step N) (CL1.uc p) = nc := by rw [hucP]
  have hH0 : ∀ (n : Fin (softRL CL p N)) (k : cols),
      (softLeftChart CL CR CL1 CR1 TIL p N Xs cols G0 G1 hlo).H0 (Fz.step N) n k =
        G0 ((softLeftChart CL CR CL1 CR1 TIL p N Xs cols G0 G1 hlo).row n) k := by
    intro n k
    unfold softLeftChart
    erw [softJBChart_H0]
    simp only [FormalResearch.JB.Chart.row, softJBChart]
    rw [hG0 k k.2]
    have hn : n.val < softRL CL p N := n.isLt
    have hnz : (n.val : ℤ) < nc - a := by rw [← hRL_int]; exact_mod_cast hn
    have hn' : (((softLo CL p N + n.val : ℕ)) : ℤ) ≤ nc := by push_cast; omega
    simp only [Fin.val_mk]
    rw [if_pos hn']
    have hcr : chartRowDn N (softLo CL p N) (softRL CL p N) false n = (((softLo CL p N + n.val : ℕ) : ℤ)) := by simp [chartRowDn]
    rw [hcr]
    have hg : CL.uc p - CL.η / 2 < uNode (Fz.step N) (((softLo CL p N + n.val : ℕ) : ℤ)) := by
      push_cast; exact g10 _ (by omega)
    rw [psiHatL_of_gt _ _ _ _ hg]
    ring
  have hH1 : ∀ (n : Fin (softRL CL p N)) (k : cols),
      (softLeftChart CL CR CL1 CR1 TIL p N Xs cols G0 G1 hlo).H1 (Fz.step N) n k =
        G1 ((softLeftChart CL CR CL1 CR1 TIL p N Xs cols G0 G1 hlo).row n) k := by
    intro n k
    unfold softLeftChart
    rw [softJBChart_H1 CL CL1 TIL p hp N hNT Xs cols (softLo CL p N) (softRL CL p N) hlo false _ _ _ _ G0 G1 hX n k]
    simp only [FormalResearch.JB.Chart.row, softJBChart]
    rw [hG1 k k.2]
    have hn : n.val < softRL CL p N := n.isLt
    have hnz : (n.val : ℤ) < nc - a := by rw [← hRL_int]; exact_mod_cast hn
    have hn' : (((softLo CL p N + n.val : ℕ)) : ℤ) ≤ nearestRow (Fz.step N) (CL1.uc p) := by rw [hnc1]; push_cast; omega
    simp only [Fin.val_mk]
    rw [if_pos hn']
    have hcr : chartRowDn N (softLo CL p N) (softRL CL p N) false n = (((softLo CL p N + n.val : ℕ) : ℤ)) := by simp [chartRowDn]
    rw [hcr]
    have hg : CL1.uc p - CL1.η / 2 < uNode (Fz.step N) (((softLo CL p N + n.val : ℕ) : ℤ)) := by
      rw [hucP, hη1]; push_cast; exact g10 _ (by omega)
    rw [psiHatL_of_gt _ _ _ _ hg]
    ring
  refine ⟨hlo, ?_, fun n k => (hH0 n k).symm, fun n k => (hH1 n k).symm, ?_⟩
  · refine ChartOkCoeff.ok (c := softLeftChart CL CR CL1 CR1 TIL p N Xs cols G0 G1 hlo) hcoeff (fun n k => hH0 n k) (fun n k => hH1 n k)
      (fun j => hc0 j) (fun j => hc1 j) ?_ ?_ ?_
    · intro n _ hn0'
      have hn0 : n.val = 0 := hn0' rfl
      have := (HEXT p hp N (max_le hN0L hN1L) hsE Xs cols hX' haL1').1 TIL (softLo CL p N) (softRL CL p N) hlo Finset.univ
        (fun k => softPk N (softLo CL p N) (softRL CL p N) false
          ((softWindow CL p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p))))
        (fun k => CL.lamL p (Xs k) N / (kappaBal (CL.aOf p (Xs k) N) * softNorm CL CR p (Xs k) N))
        (fun k => CL1.lamL p (Xs k) N / (kappaBal (CL1.aOf p (Xs k) N) * softNorm CL1 CR1 p (Xs k) N)) G0 G1
        (by rw [hlo_int]) (fun k => rfl) n hn0
      exact this
    · intro k
      exact HLB p hp N (max_le hN0L hN0R) hsl Xs Um hE (fun i => (hsp p hp N hss0 Xs Um hE i).2) TIL cols (softLo CL p N) (softRL CL p N) hlo
        Finset.univ
        (fun k => CL.lamL p (Xs k) N / (kappaBal (CL.aOf p (Xs k) N) * softNorm CL CR p (Xs k) N))
        (fun k => CL1.lamL p (Xs k) N / (kappaBal (CL1.aOf p (Xs k) N) * softNorm CL1 CR1 p (Xs k) N)) G0 G1
        Xs id Um (fun k => rfl) (fun n k => rfl) hX' haL1 hcov k
    · intro k
      exact HUB p hp hzP hmuP hucP N (max_le hN0L hN1L) hsu TIL Xs cols (softLo CL p N) (softRL CL p N) hlo false Finset.univ
        (fun k => CL.lamL p (Xs k) N / (kappaBal (CL.aOf p (Xs k) N) * softNorm CL CR p (Xs k) N))
        (fun k => CL1.lamL p (Xs k) N / (kappaBal (CL1.aOf p (Xs k) N) * softNorm CL1 CR1 p (Xs k) N)) G0 G1
        hX' haL1 hsame hcov k
  · intro i hi1 hi2
    have hi' : (((i : ℕ) : ℤ) - (softLo CL p N : ℤ)).toNat < softRL CL p N := by
      have : (((((i : ℕ) : ℤ) - (softLo CL p N : ℤ)).toNat : ℕ) : ℤ) < (softRL CL p N : ℤ) := by omega
      exact_mod_cast this
    refine ⟨⟨(((i : ℕ) : ℤ) - (softLo CL p N : ℤ)).toNat, hi'⟩, ?_⟩
    apply Fin.ext
    simp only [FormalResearch.JB.Chart.row, softLeftChart, softJBChart]
    omega

end Left

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_left_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.soft_left_ok

end FormalResearch.JacobiEigenvectors.TheoremB

end
