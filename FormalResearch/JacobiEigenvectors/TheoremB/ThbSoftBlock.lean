module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbSoftRight
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbConstants
public import FormalResearch.JacobiEigenvectors.TheoremB.Collar

/-!
# Paper J, Theorem B, L3.5c, part 13: the soft block as a `ThbBlock` (generic over the soft chart pair)

Source: Paper J `app_thmB.tex`, proof of `prop:thb-inputs`, the soft blocks: the left and right half charts of the soft collar (`soft_left_ok`, `soft_right_ok`) glued into one `ThbBlock`, and the exterior bound (the entries of `hat G^{[m]}`, `hat G^{[m+1]}` and `U` on the rows
outside the collar are `<= C e^{-c/h}`: `lem:tha-collar (1)`).

## Proved here

* `soft_block_gen`: for a soft chart pair `(CL, CR)` of orders `m`, `m + 1` with the transfer inputs of both halves, host bound `C_h` and the eigenvalue columns in the window `|X - bandHi| <= delta_0`: uniform constants `cs, C_eps, c_eps, N_0, h_0`
  and a `ThbBlock` for any matrices `G0, G1` that are the glued columns (`softVec` form) with `||G0 col - U col|| <= C_h h^m`, `||G1 col - U col|| <= C_h h^{m+1} log(1/h)`.  The rows not used by either chart are the rows with
  `|u_n - u_c| >= eta/2`, where `G0, G1` are `softVec` of the two orders and `U` the eigenvector, bounded by `propThaCollar_proved`.

## Differences from the paper

None.  **Not formalised**: nothing.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine FormalResearch.JB

open scoped Classical

theorem cexp_le {C C' c c' h : ℝ} (hC : 0 ≤ C) (hCC : C ≤ C') (hc : c' ≤ c) (hh : 0 < h) :
    C * Real.exp (-c / h) ≤ C' * Real.exp (-c' / h) := by
  have hexp : Real.exp (-c / h) ≤ Real.exp (-c' / h) := by
    apply Real.exp_le_exp.mpr
    have : c' / h ≤ c / h := div_le_div_of_nonneg_right hc hh.le
    linarith [neg_div h c, neg_div h c']
  exact mul_le_mul hCC hexp (Real.exp_pos _).le (hC.trans hCC)

theorem softLo_eq {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (p : Par × ℝ) (N : ℕ)
    (h0 : 0 ≤ ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋) :
    (softLo CL p N : ℤ) = ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋ + 1 := by
  unfold softLo; omega

section Generic

variable {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **The soft block** for a soft chart pair: uniform constants and a `ThbBlock` (see the module docstring). -/
theorem soft_block_gen (hf : ParabolicCylinderFacts U V cPC CPC)
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1))
    (CL1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1)) (CR1 : SoftEdgeChart (mirrorFamily Fz) P (m + 1) q U V (fun _ => 1))
    (hM : SoftMirror CL CR) (hM1 : SoftMirror CL1 CR1)
    (hz : CL1.zeta = CL.zeta) (hmu : CL1.muS = CL.muS) (huc : CL1.uc = CL.uc) (hδ1 : CL1.δ0 = CL.δ0) (hη1 : CL1.η = CL.η)
    (hm : 1 ≤ m) (r : ℕ) (hr : StdAssump Fz P (q / 2) r)
    (TIL : TransferInputsDn Fz P (fun p => Fz.bandHi p - CL.δ0) (fun p => Fz.bandHi p + CL.δ0) m CL.chain CL1.chain 2
      (fun p => CL.uc p - CL.η / 2) (fun p => CL.uc p + CL.η / 2))
    (TIR : TransferInputsDn (mirrorFamily Fz) P (fun p => Fz.bandHi p - CL.δ0) (fun p => Fz.bandHi p + CL.δ0) m CR.chain CR1.chain 2
      (fun p => CR.uc p - CR.η / 2) (fun p => CR.uc p + CR.η / 2))
    (Ch : ℝ) (hCh : 0 ≤ Ch) :
    ∃ (cs : OneStepConsts) (Cε cε : ℝ) (N0 : ℕ) (h0 : ℝ), 0 ≤ Cε ∧ 0 < cε ∧ 0 < h0 ∧ h0 ≤ 1 ∧
      ∀ p ∈ P, ∀ N : ℕ, N0 ≤ N → Fz.step N ≤ h0 →
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
        Nonempty (ThbBlock cs N m (Fz.step N) Um G0 G1 cols Cε cε) := by
  obtain ⟨csL, NL, hL, hL0, hL1, HL⟩ := soft_left_ok hf CL CR CL1 CR1 hM hM1 hz hmu huc hδ1 hη1 hm r hr TIL Ch hCh
  obtain ⟨csR, NR, hR, hR0, hR1, HR⟩ := soft_right_ok hf CL CR CL1 CR1 hM hM1 hz hmu huc hδ1 hη1 hm r hr TIR Ch hCh
  obtain ⟨cs, hcs⟩ := exists_consts_join (ι := Bool) (fun b => if b then csL else csR)
  obtain ⟨C0, c0, h00, hC0pos, hc0pos, hh00, HC0⟩ := propThaCollar_proved (cPC := cPC) (CPC := CPC) CL CR hf hm hM r hr
  obtain ⟨C1, c1, h01, hC1pos, hc1pos, hh01, HC1⟩ := propThaCollar_proved (cPC := cPC) (CPC := CPC) CL1 CR1 hf (by omega) hM1 r hr
  obtain ⟨hA, hhA, HA⟩ := soft_a_data hf CL CR hm hM r hr
  have hηpos : 0 < CL.η := CL.consts_pos.2.1
  obtain ⟨h0, hh0pos, hle⟩ : ∃ h0 : ℝ, 0 < h0 ∧ ∀ x : ℝ, x ≤ h0 → x ≤ 1 ∧ x ≤ hL ∧ x ≤ hR ∧ x ≤ CL.η / 4 ∧ x ≤ h00 ∧ x ≤ h01 ∧ x ≤ hA := by
    refine ⟨min 1 (min hL (min hR (min (CL.η / 4) (min h00 (min h01 hA))))), ?_, fun x hx => ?_⟩
    · simp only [lt_min_iff]
      exact ⟨one_pos, hL0, hR0, by linarith, hh00, hh01, hhA⟩
    · simp only [le_min_iff] at hx
      exact hx
  refine ⟨cs, max C0 C1, min c0 c1, max NL (max NR (max CL.N0 (max CR.N0 (max CL1.N0 CR1.N0)))), h0,
    (le_max_of_le_left hC0pos.le), lt_min hc0pos hc1pos, hh0pos, (hle h0 le_rfl).1, ?_⟩
  intro p hp N hN hst Xs Um hE cols hwin G0 G1 hG0 hG1 hc0 hc1
  simp only [max_le_iff] at hN
  obtain ⟨hNL, hNR, hN0L, hN0R, hN1L, hN1R⟩ := hN
  obtain ⟨hh1, hsL, hsR, hsη, hs0, hs1, hsA⟩ := hle _ hst
  have hstp : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L := step_mul_succ Fz N
  obtain ⟨hu1', hu2'⟩ := CL.ucη_in p hp
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ :=
    soft_geom (N := N) hstp hηpos hsη hLs hu1' hu2'
  set a : ℤ := ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋ with hadef
  set b : ℤ := ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉ with hbdef
  set nc : ℤ := nearestRow (Fz.step N) (CL.uc p) with hncdef
  have hucP : CL1.uc p = CL.uc p := by rw [huc]
  have hnc1 : nearestRow (Fz.step N) (CL1.uc p) = nc := by rw [hucP]
  have hzP : ∀ α x, CL1.zeta p α x = CL.zeta p α x := fun α x => by rw [hz]
  have hmuP : ∀ r α, CL1.muS r p α = CL.muS r p α := fun r α => by rw [hmu]
  have haL1 : ∀ k ∈ cols, CL.aOf p (Xs k) N ≤ 1 := fun k hk =>
    ((HA p hp N (max_le hN0L hN0R) hsA Xs Um hE k (hwin k hk)).trans zero_le_one)
  have haL1' : ∀ k ∈ cols, CL1.aOf p (Xs k) N ≤ 1 := fun k hk => by
    rw [(softChart_data_eq_P CL CL1 hzP hmuP hucP (Xs k) N).1]
    exact haL1 k hk
  have hwin1 : ∀ k ∈ cols, |Xs k - Fz.bandHi p| ≤ CL1.δ0 := fun k hk => by rw [hδ1]; exact hwin k hk
  obtain ⟨hloL, okL, m0L, m1L, covL⟩ := HL p hp N hNL hsL Xs Um hE cols hwin G0 G1 hG0 hG1 hc0 hc1
  obtain ⟨hloR, okR, m0R, m1R, covR⟩ := HR p hp N hNR hsR Xs Um hE cols hwin G0 G1 hG0 hG1 hc0 hc1
  have hlo_int : (softLo CL p N : ℤ) = a + 1 := softLo_eq CL p N g1
  have hccle : ∀ y : ℝ, y ≤ C0 * Real.exp (-c0 / Fz.step N) → y ≤ max C0 C1 * Real.exp (-min c0 c1 / Fz.step N) := fun y hy =>
    hy.trans (cexp_le hC0pos.le (le_max_left _ _) (min_le_left _ _) hstp)
  have hccle1 : ∀ y : ℝ, y ≤ C1 * Real.exp (-c1 / Fz.step N) → y ≤ max C0 C1 * Real.exp (-min c0 c1 / Fz.step N) := fun y hy =>
    hy.trans (cexp_le hC1pos.le (le_max_right _ _) (min_le_right _ _) hstp)
  refine ⟨{
    RL := softRL CL p N
    RR := softRR CL CR p N
    chL := softLeftChart CL CR CL1 CR1 TIL p N Xs cols G0 G1 hloL
    chR := softRightChart CL CR CL1 CR1 TIR p N Xs cols G0 G1 hloR
    okL := okL.mono (by simpa using hcs true) hstp hh1
    okR := okR.mono (by simpa using hcs false) hstp hh1
    match0L := fun n _ k => m0L n k
    match0R := fun n hn k => m0R n hn k
    match1L := fun n _ k => m1L n k
    match1R := fun n hn k => m1R n hn k
    cover := ?_ }⟩
  intro k hk i hi1 hi2
  have hrow : ((i : ℕ) : ℤ) ∈ rowsOf N := Finset.mem_Icc.mpr ⟨by positivity, by have := i.isLt; omega⟩
  have hfar : ((i : ℕ) : ℤ) ≤ a ∨ b ≤ ((i : ℕ) : ℤ) := by
    by_contra hcon
    push_neg at hcon
    by_cases hle : ((i : ℕ) : ℤ) ≤ nc
    · obtain ⟨n, hn⟩ := covL i (by omega) hle
      exact hi1 ⟨n, Finset.mem_univ _, hn⟩
    · obtain ⟨n, hn, hn'⟩ := covR i (by omega) hcon.2
      exact hi2 ⟨n, hn, hn'⟩
  have hX := hwin k hk
  have hXe : eigVec Um k ((i : ℕ) : ℤ) = Um i k := eigVec_row Um k i
  rcases hfar with hfa | hfb
  · -- below the collar
    have hu : uNode (Fz.step N) ((i : ℕ) : ℤ) ≤ CL.uc p - CL.η / 2 := g11 _ hfa
    have hlenc : ((i : ℕ) : ℤ) ≤ nc := by omega
    have hZ : CL.Zof p (Xs k) N ((i : ℕ) : ℤ) ≤ 0 := Zof_nonpos_of_near CL hp hX hrow (by linarith)
    have hZ1 : CL1.Zof p (Xs k) N ((i : ℕ) : ℤ) ≤ 0 := by
      refine Zof_nonpos_of_near CL1 hp (hwin1 k hk) hrow ?_
      rw [hucP, hη1]; linarith
    have hv0 := (HC0 p hp (Xs k) hX N (max_le hN0L hN0R) hs0 (haL1 k hk)).1 Xs Um hE k rfl _ hrow (by
      rw [abs_of_nonpos (by linarith)]; linarith)
    have hv1 := (HC1 p hp (Xs k) (hwin1 k hk) N (max_le hN1L hN1R) hs1 (haL1' k hk)).1 Xs Um hE k rfl _ hrow (by
      rw [hucP, hη1, abs_of_nonpos (by linarith)]; linarith)
    have e0 : G0 i k = softVec CL CR p (Xs k) N ((i : ℕ) : ℤ) := by
      rw [hG0 k hk i, if_pos hlenc, softVec_eq]
      unfold softNum
      rw [if_pos hZ]
    have e1 : G1 i k = softVec CL1 CR1 p (Xs k) N ((i : ℕ) : ℤ) := by
      rw [hG1 k hk i, if_pos (by rw [hnc1]; exact hlenc), softVec_eq]
      unfold softNum
      rw [if_pos hZ1]
    rw [e0, e1, ← hXe]
    exact ⟨hccle _ ((le_add_of_nonneg_left (abs_nonneg _)).trans hv0),
      hccle1 _ ((le_add_of_nonneg_left (abs_nonneg _)).trans hv1),
      hccle _ ((le_add_of_nonneg_right (abs_nonneg _)).trans hv0)⟩
  · -- above the collar
    have hu : CL.uc p + CL.η / 2 ≤ uNode (Fz.step N) ((i : ℕ) : ℤ) := g13 _ hfb
    have hgtnc : ¬ ((i : ℕ) : ℤ) ≤ nc := fun h => by
      have := g14 _ h
      linarith
    have hZ : 0 < CL.Zof p (Xs k) N ((i : ℕ) : ℤ) := Zof_pos_of_far CL hp hX hrow (by linarith)
    have hZ1 : 0 < CL1.Zof p (Xs k) N ((i : ℕ) : ℤ) := by
      refine Zof_pos_of_far CL1 hp (hwin1 k hk) hrow ?_
      rw [hucP, hη1]; linarith
    have hv0 := (HC0 p hp (Xs k) hX N (max_le hN0L hN0R) hs0 (haL1 k hk)).1 Xs Um hE k rfl _ hrow (by
      rw [abs_of_nonneg (by linarith)]; linarith)
    have hv1 := (HC1 p hp (Xs k) (hwin1 k hk) N (max_le hN1L hN1R) hs1 (haL1' k hk)).1 Xs Um hE k rfl _ hrow (by
      rw [hucP, hη1, abs_of_nonneg (by linarith)]; linarith)
    have e0 : G0 i k = softVec CL CR p (Xs k) N ((i : ℕ) : ℤ) := by
      rw [hG0 k hk i, if_neg hgtnc, softVec_eq]
      unfold softNum softSeqR
      rw [if_neg (not_le.mpr hZ)]
    have e1 : G1 i k = softVec CL1 CR1 p (Xs k) N ((i : ℕ) : ℤ) := by
      rw [hG1 k hk i, if_neg (by rw [hnc1]; exact hgtnc), softVec_eq]
      unfold softNum softSeqR
      rw [if_neg (not_le.mpr hZ1)]
    rw [e0, e1, ← hXe]
    exact ⟨hccle _ ((le_add_of_nonneg_left (abs_nonneg _)).trans hv0),
      hccle1 _ ((le_add_of_nonneg_left (abs_nonneg _)).trans hv1),
      hccle _ ((le_add_of_nonneg_right (abs_nonneg _)).trans hv0)⟩

end Generic

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_block_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.soft_block_gen

end FormalResearch.JacobiEigenvectors.TheoremB

end
