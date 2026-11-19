module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.CollarPC
public import FormalResearch.JacobiEigenvectors.TheoremB.CollarGlue
public import FormalResearch.JacobiEigenvectors.TheoremB.SpliceSoftFacts
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAssembly6
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZero
public import FormalResearch.JacobiEigenvectors.TheoremB.Statements

/-!
# Paper J, Theorem B, L3.4: `lem:tha-collar` (1) (`PropThaCollar`)

Source: Paper J `app_thmB.tex`, proof of `lem:tha-collar` (1).  Statement: `PropThaCollar CL CR cPC CPC` (`TheoremB/Statements.lean`; F-B15 applied in round 10).

## Chain of lemmas (checked against the paper)

1. *Forbidden margin and discrete maximum principle* (paper: `f_+` has a unique strict maximum, `T < 0`, `Q_0 - 2 sqrt(E_0) >= c nu` off the collar; `0 < psi^L_n <= psi^L_{n_1+1}`, eq:tha-S4grow): these are the chart fields `geom_far`, `grow_gap`
   and their consequences already proved for the soft charts: `weber_tail` (`SoftTails.lean`, `sum_{n <= n_1} E_Web^2 M_Web^2 <= C_w (|lam_L|/kappa_b)^2 e^{-c_w/h}`: it contains the growth bound, the envelope `V_n <= C psi^L_n` and `E(a,Z_{n_1+1}) <= e^{-c_E/h}`
   (`Eminus_left_small`)) and its mirror `weber_tail_right`.  Nothing of the paper's argument is re-proved; a single term of a sum of squares is bounded by the sum.
2. *First conjunct.* `|Psi_n| + |hat Psi_n| <= C V_n / hat N`: `soft_eigen_main` (`|eigVec - softVec| <= C h^m softEnv`) and `soft_splice_facts` (`|softNum| <= C_env softEnvNum`), so `<= C softEnv_n`; on `u_n <= u_c - eta/2` (resp. `>= u_c + eta/2`) `softEnv_n^2 <= (C_w/c_n) e^{-c_w/h}` (resp. `(C_w' C_k^2/c_n) e^{-c_r/h}`)
   from step 1 and `hat N^2 >= c_n T^2` (`soft_norm_lb`), `T = |lam_L|/kappa_b`; the right side uses `|hat kappa lam_R| <= C_k |lam_L|` (`soft_kappa_bound`).
3. *Conjuncts 2-4.* `ext_left_row`: the last row `n_1` below the collar is a row of patch 2 with `-2 eta <= x <= -5 eta/16`; `pc_ext_row` (`CollarPC.lean`): `|phi^{(1)}_{2,n_1}|` and `|wf 2 0 .. 1|` are `<= B e^{-c_Q/h}`; with `hat N >= sqrt(c_n) T` the quotient
   `(|lam_L|/hat N) |phi/kappa_b| = (T/hat N) |phi|` is `<= (B/sqrt c_n) e^{-c_Q/h}`.  The right exterior neighbour is the same statement for the mirror chart (`floor_mirror`: `N - ceil(.) = floor(.)` at `u_c^R = L - u_c`), with `|hat kappa lam_R| <= C_k |lam_L|`.

## Proved here

`propThaCollar_proved : PropThaCollar CL CR cPC CPC`, no premise beyond the statement's own (`ParabolicCylinderFacts`, `1 <= m`, `SoftMirror`).  No `SoftFoldSmall`, no `SoftCountHyps`.

## Differences from the paper

* **F-B15 (applied).**  `PropThaCollar` lacked the premises `ParabolicCylinderFacts U V cPC CPC`, `1 <= m`, `SoftMirror CL CR`; the first conjunct compares the eigenvector with `softVec CL CR` (built from the mirror chart `CR`), whose
  comparison (`soft_eigen_main`) needs the engine smallness `h^m Theta <= c_*` (false for `m = 0`) and the facts on `U, V` (the chart fields constrain `U, V` only at chain rows); for an unrelated `CR` conjuncts 1 and 4 are false.  Same pattern as F-B9, F-B14.
  The statement now starts `ParabolicCylinderFacts U V cPC CPC -> 1 <= m -> SoftMirror CL CR ->`.
* **Conjuncts 2-4 hold at every `X` near the edge (no eigenvalue).**  The frozen statement quantifies them over all `X` with `|X - bandHi| <= delta_0`, `a <= 1` (not only eigenvalues, as in the paper); the proof is chart-level (`soft_norm_lb`, `soft_kappa_bound`).

## Not formalised

Item (2) of `lem:tha-collar` (`TransferInputs.t12_lb`, `reg_*`), which the frozen statement leaves to chart fields.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section Helpers

lemma ratio_le (T S c : ℝ) (hc : 0 < c) (hT : 0 ≤ T) (hS : 0 ≤ S) (h : c * T ^ 2 ≤ S ^ 2) : T / S ≤ 1 / Real.sqrt c := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  by_cases hS0 : S = 0
  · rw [hS0, div_zero]; positivity
  · have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
    rw [div_le_div_iff₀ hSp hsc, one_mul]
    have h1 : (T * Real.sqrt c) ^ 2 ≤ S ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le]; linarith
    exact abs_le_of_sq_le_sq' h1 hS |>.2

lemma le_of_sq_exp (x D c h : ℝ) (hD : 0 ≤ D) (hx0 : 0 ≤ x) (hx : x ^ 2 ≤ D * Real.exp (-c / h)) :
    x ≤ Real.sqrt D * Real.exp (-(c / 2) / h) := by
  have hb : 0 ≤ Real.sqrt D * Real.exp (-(c / 2) / h) := by positivity
  have h2 : (Real.sqrt D * Real.exp (-(c / 2) / h)) ^ 2 = D * Real.exp (-c / h) := by
    rw [mul_pow, Real.sq_sqrt hD, pow_two, ← Real.exp_add]
    congr 2
    ring
  exact abs_le_of_sq_le_sq' (by rw [h2]; exact hx) hb |>.2

lemma exp_mono_c (c1 c h : ℝ) (hh : 0 < h) (hc : c ≤ c1) : Real.exp (-c1 / h) ≤ Real.exp (-c / h) := by
  apply Real.exp_le_exp.mpr
  have : c / h ≤ c1 / h := div_le_div_of_nonneg_right hc hh.le
  have e1 : -c1 / h = -(c1 / h) := by ring
  have e2 : -c / h = -(c / h) := by ring
  rw [e1, e2]; linarith

lemma floor_mirror (N : ℕ) (h uc η L : ℝ) (hh : 0 < h) (hL : h * ((N : ℝ) + 1) = L) :
    (N : ℤ) - ⌈(uc + η / 2) / h - 1 / 2⌉ = ⌊((L - uc) - η / 2) / h - 1 / 2⌋ := by
  have e : ((L - uc) - η / 2) / h - 1 / 2 = -((uc + η / 2) / h - 1 / 2) + ((N : ℤ) : ℝ) := by
    rw [← hL]; push_cast; field_simp; ring
  rw [e, Int.floor_add_intCast, Int.floor_neg]
  ring

end Helpers

section Row

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}

/-- **the last row below the collar is a row of patch 2** with `-2 eta <= x <= -5 eta/16`. -/
lemma ext_left_row (C : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ}
    (hN : C.N0 ≤ N) (hh : Fz.step N ≤ C.η / 2) {j : ℤ} (hj : j = ⌊(C.uc p - C.η / 2) / Fz.step N - 1 / 2⌋) :
    0 ≤ j ∧ j ≤ (N : ℤ) ∧ (C.chain p X N).jj 1 ≤ j ∧ j ≤ (C.chain p X N).NR ∧
      -(2 * C.η) ≤ uNode (Fz.step N) j - C.uc p ∧ uNode (Fz.step N) j - C.uc p ≤ -(5 * C.η / 16) := by
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hη := C.consts_pos.2.1
  obtain ⟨hc1, hc2⟩ := C.ucη_in p hp
  have hL := step_mul_succ Fz N
  set h := Fz.step N with hhd
  set y : ℝ := (C.uc p - C.η / 2) / h - 1 / 2 with hy
  have f1 : (j : ℝ) ≤ y := by rw [hj]; exact Int.floor_le y
  have f2 : y < (j : ℝ) + 1 := by rw [hj]; exact Int.lt_floor_add_one y
  have hyh : (y + 1 / 2) * h = C.uc p - C.η / 2 := by rw [hy]; field_simp; ring
  have e1 : uNode h j ≤ C.uc p - C.η / 2 := by
    unfold uNode
    rw [← hyh]
    exact mul_le_mul_of_nonneg_right (by linarith) hh0.le
  have e2 : C.uc p - C.η / 2 < uNode h (j + 1) := by
    unfold uNode
    rw [← hyh]
    push_cast
    exact mul_lt_mul_of_pos_right (by linarith) hh0
  have e3 : C.uc p - C.η / 2 - h < uNode h j := by
    have : uNode h (j + 1) = uNode h j + h := by unfold uNode; push_cast; ring
    linarith
  have hpos : 0 < uNode h j := by linarith
  refine ⟨?_, ?_, ?_, ?_, by linarith, by linarith⟩
  · by_contra hcon
    have : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
    have : uNode h j ≤ 0 := by
      unfold uNode
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hh0.le
    linarith
  · by_contra hcon
    have h1 : ((N : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast (show (N : ℤ) + 1 ≤ j by omega)
    have h2 : uNode h j ≥ ((N : ℝ) + 1 + 1 / 2) * h := by
      unfold uNode
      exact mul_le_mul_of_nonneg_right (by linarith) hh0.le
    nlinarith
  · by_contra hcon
    obtain ⟨-, -, hjj1, -⟩ := C.shape p hp X hX N hN
    have hle : j + 1 ≤ (C.chain p X N).jj 1 := by omega
    have := SoftEdgeChart.uNode_mono_le hh0.le hle
    linarith
  · exact row_le_chainNR C hp hX hN (k := j) (by linarith)

end Row

section Main

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}

set_option maxHeartbeats 8000000 in
/-- **`lem:tha-collar` (1)** (`PropThaCollar CL CR cPC CPC`; the premises `ParabolicCylinderFacts`, `1 <= m`, `SoftMirror CL CR` are part of the statement since round 10: finding F-B15 applied). -/
theorem propThaCollar_proved {cPC CPC : ℝ} (CL : SoftEdgeChart Fz P m q U V (fun _ => 1))
    (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1)) : PropThaCollar CL CR cPC CPC := by
  unfold PropThaCollar
  intro hf hm hM r hr
  have hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ (fun _ : ℝ => (1 : ℝ)) h := fun _ _ _ => le_rfl
  obtain ⟨cn, hn0, hcn, hn0p, Hn⟩ := soft_norm_lb CL CR hf r hr
  obtain ⟨Ck, hk0, hCk, hk0p, Hk⟩ := soft_kappa_bound CL CR hM hf
  obtain ⟨Cw, cw, hw0, hw0p, hcw, Hw⟩ := weber_tail CL hf hm hLm
  obtain ⟨Cr, cr, hr0, hr0p, hcr, Hr⟩ := weber_tail_right hM hf hm hLm
  obtain ⟨Cenv, Cm, K, CM, cn2, clb, hs0, hCenv, hCm, hK, hCM, hcn2, hclb, hs0p, Hs⟩ := soft_splice_facts CL CR hM hf hm hLm
  obtain ⟨Cz, hz0, hz0p, Hz⟩ := stepZero Fz P (q / 2) r hr
  obtain ⟨Cc, he0, he0p, He⟩ := soft_eigen_main CL CR hM hf hm hLm Cz
  have hN0 : CR.N0 = CL.N0 := hM.2.2.2.2.2
  have hδ : CR.δ0 = CL.δ0 := hM.2.2.2.2.1
  have hηe : CR.η = CL.η := hM.2.2.2.1
  have hη := CL.consts_pos.2.1
  have hCPC : 0 ≤ CPC := le_trans hf.cPC_pos.le hf.cPC_le
  have hBL := extB_nonneg CL hf
  have hBR := extB_nonneg CR hf
  have hcQL := softCQ_pos CL
  have hcQR := softCQ_pos CR
  set c0 : ℝ := min (min (softCQ CL) (softCQ CR)) (min (cw / 2) (cr / 2)) with hc0
  have hc0p : 0 < c0 := lt_min (lt_min hcQL hcQR) (lt_min (by linarith) (by linarith))
  have hc0a : c0 ≤ softCQ CL := (min_le_left _ _).trans (min_le_left _ _)
  have hc0b : c0 ≤ softCQ CR := (min_le_left _ _).trans (min_le_right _ _)
  have hc0c : c0 ≤ cw / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc0d : c0 ≤ cr / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set Cw' : ℝ := max Cw 0 with hCw'
  set Cr' : ℝ := max Cr 0 with hCr'
  have hCw0 : 0 ≤ Cw' := le_max_right _ _
  have hCr0 : 0 ≤ Cr' := le_max_right _ _
  set D1L : ℝ := (|Cc| + 2 * Cenv) * Real.sqrt (Cw' / cn) with hD1L
  set D1R : ℝ := (|Cc| + 2 * Cenv) * Real.sqrt (Cr' * Ck ^ 2 / cn) with hD1R
  set D2 : ℝ := extB CL CPC / Real.sqrt cn with hD2
  set D4 : ℝ := Ck * extB CR CPC / Real.sqrt cn with hD4
  have hsqcn : 0 < Real.sqrt cn := Real.sqrt_pos.mpr hcn
  have hD1L0 : 0 ≤ D1L := by
    have : 0 ≤ Real.sqrt (Cw' / cn) := Real.sqrt_nonneg _
    positivity
  have hD1R0 : 0 ≤ D1R := by
    have : 0 ≤ Real.sqrt (Cr' * Ck ^ 2 / cn) := Real.sqrt_nonneg _
    positivity
  have hD20 : 0 ≤ D2 := by positivity
  have hD40 : 0 ≤ D4 := by positivity
  set h0fin : ℝ := min hn0 (min hk0 (min hw0 (min hr0 (min hs0 (min hz0 (min he0
      (min CL.softH1 (min CR.softH1 (min (CL.η / 2) (min (winH1 CL) (min (winH1 CR) (min CL.softH2 (min CR.softH2 1))))))))))))) with hh0fin
  have hh0finp : 0 < h0fin := by
    refine lt_min hn0p (lt_min hk0p (lt_min hw0p (lt_min hr0p (lt_min hs0p (lt_min hz0p (lt_min he0p
      (lt_min CL.softH1_pos (lt_min CR.softH1_pos (lt_min (by linarith) (lt_min (winH1_pos CL) (lt_min (winH1_pos CR)
        (lt_min CL.softH2_pos (lt_min CR.softH2_pos one_pos)))))))))))))
  refine ⟨1 + D1L + D1R + D2 + D4, c0, h0fin, by positivity, hc0p, hh0finp, ?_⟩
  intro p hp X hX N hN hstep ha
  rw [hh0fin] at hstep
  simp only [le_min_iff] at hstep
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15⟩ := hstep
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hN2 : CR.N0 ≤ N := (le_max_right _ _).trans hN
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have sη : Fz.step N ≤ CL.η := by linarith
  have sηR : Fz.step N ≤ CR.η := by rw [hηe]; exact sη
  have hκ := kappaBal_pos (CL.aOf p X N)
  have hSnn : 0 ≤ softNorm CL CR p X N := by unfold softNorm glueNorm; exact Real.sqrt_nonneg _
  have hT0 : 0 ≤ |CL.lamL p X N| / kappaBal (CL.aOf p X N) := by positivity
  have hone : 1 ≤ Fz.step N ^ (-(1 : ℝ) / 2) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh0 s15 (by norm_num)
  have hnorm : cn * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 ≤ softNorm CL CR p X N ^ 2 := by
    have h1 := Hn p hp N hN1 s1 X hX ha
    have hT2 := sq_nonneg (|CL.lamL p X N| / kappaBal (CL.aOf p X N))
    calc cn * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2
        = cn * ((|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * 1) := by ring
      _ ≤ cn * ((|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hone hT2) hcn.le
      _ ≤ _ := h1
  have hratio := ratio_le _ _ cn hcn hT0 hSnn hnorm
  have hkb := Hk p hp N hN1 s2 X hX ha
  -- the exterior rows of the two charts
  have hhL : Fz.step N ≤ min (winH1 CL) (min CL.softH2 1) := le_min s11 (le_min s13 s15)
  have hhR : Fz.step N ≤ min (winH1 CR) (min CR.softH2 1) := le_min s12 (le_min s14 s15)
  have hX' : |X - (mirrorFamily Fz).bandHi p| ≤ CR.δ0 := by rw [bandHi_mirror, hδ]; exact hX
  have hexpL : Real.exp (-(softCQ CL / Fz.step N)) ≤ Real.exp (-c0 / Fz.step N) := by
    have := exp_mono_c (softCQ CL) c0 (Fz.step N) hh0 hc0a
    rwa [show -(softCQ CL / Fz.step N) = -softCQ CL / Fz.step N by ring]
  have hexpR : Real.exp (-(softCQ CR / Fz.step N)) ≤ Real.exp (-c0 / Fz.step N) := by
    have := exp_mono_c (softCQ CR) c0 (Fz.step N) hh0 hc0b
    rwa [show -(softCQ CR / Fz.step N) = -softCQ CR / Fz.step N by ring]
  have hex0 := Real.exp_pos (-c0 / Fz.step N)
  have hCfin : ∀ D : ℝ, 0 ≤ D → D ≤ 1 + D1L + D1R + D2 + D4 → D * Real.exp (-c0 / Fz.step N) ≤ (1 + D1L + D1R + D2 + D4) * Real.exp (-c0 / Fz.step N) :=
    fun D _ hD => mul_le_mul_of_nonneg_right hD hex0.le
  -- left neighbour
  obtain ⟨jL0, jLN, jL1, jLR, jLlo, jLhi⟩ := ext_left_row CL hp hX hN1 (by linarith) (j := ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋) rfl
  obtain ⟨pL1, pL2⟩ := pc_ext_row CL hf hp hX hN1 hhL jL0 jLN jL1 jLR jLlo jLhi
  -- right neighbour (mirror chart)
  have hL := step_mul_succ Fz N
  have huc : CR.uc p = Fz.L - CL.uc p := hM.1 p hp
  have hjR : (N : ℤ) - ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉ =
      ⌊(CR.uc p - CR.η / 2) / (mirrorFamily Fz).step N - 1 / 2⌋ := by
    rw [floor_mirror N (Fz.step N) (CL.uc p) CL.η Fz.L hh0 hL, huc, hηe]
    rfl
  obtain ⟨jR0, jRN, jR1, jRR, jRlo, jRhi⟩ := ext_left_row CR hp hX' hN2 (by show Fz.step N ≤ CR.η / 2; rw [hηe]; exact s10)
    (j := (N : ℤ) - ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉) hjR
  obtain ⟨pR1, pR2⟩ := pc_ext_row CR hf hp hX' hN2 hhR jR0 jRN jR1 jRR jRlo jRhi
  have hκR : kappaBal (CR.aOf p X N) = kappaBal (CL.aOf p X N) := by rw [aOf_mirror hM hp X N]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- conjunct 1
    intro Xs Um hE k hk n hn hfar
    subst hk
    have hX0 : |Xs k - Fz.bandHi p| ≤ CL.δ0 := hX
    obtain ⟨ψL, ψ', κ, hJL, hsL, hJR, hsR, hrel⟩ := eig_exact_data CL CR hM hp hN1 hN2 s8 s9 sη sηR Xs Um hE k hX0
    obtain ⟨hTpos, hnum, -⟩ := Hs p hp N hN s5 (Xs k) hX0 ha ψL ψ' κ hJL hsL hJR hsR hrel
    have hst0 : ∀ i, Xs i ≤ Fz.bandHi p + Cz * Fz.step N ^ 2 := fun i => (Hz p hp N s6 Xs Um hE i).2
    obtain ⟨hclose, -⟩ := He p hp N hN s7 Xs Um hE hst0 k hX0
    have hSpos : 0 < softNorm CL CR p (Xs k) N := by
      by_contra hcon
      have h0 : softNorm CL CR p (Xs k) N = 0 := le_antisymm (not_lt.mp hcon) hSnn
      rw [h0] at hnorm
      have : 0 < cn * (|CL.lamL p (Xs k) N| / kappaBal (CL.aOf p (Xs k) N)) ^ 2 := by positivity
      linarith
    have hn' := hclose n hn
    -- |softVec| <= Cenv softEnv
    have hvec : |softVec CL CR p (Xs k) N n| ≤ Cenv * softEnv CL CR p (Xs k) N n := by
      rw [softVec_eq, softEnv_eq, abs_div, abs_of_pos hSpos, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (hnum n hn) hSpos.le
    have hh1 : Fz.step N ^ m ≤ 1 := pow_le_one₀ hh0.le s15
    have hEnv0 : 0 ≤ softEnv CL CR p (Xs k) N n := by
      rw [softEnv_eq]
      exact div_nonneg (softEnvNum_nonneg hf CL CR p (Xs k) N n) hSnn
    have hsum : |eigVec Um k n| + |softVec CL CR p (Xs k) N n| ≤ (|Cc| + 2 * Cenv) * softEnv CL CR p (Xs k) N n := by
      have h1 : |eigVec Um k n| ≤ |eigVec Um k n - softVec CL CR p (Xs k) N n| + |softVec CL CR p (Xs k) N n| := by
        have := abs_add_le (eigVec Um k n - softVec CL CR p (Xs k) N n) (softVec CL CR p (Xs k) N n)
        simpa using this
      have h2 : |eigVec Um k n - softVec CL CR p (Xs k) N n| ≤ |Cc| * softEnv CL CR p (Xs k) N n := by
        refine hn'.trans ?_
        simp only [mul_one]
        calc Cc * Fz.step N ^ m * softEnv CL CR p (Xs k) N n ≤ |Cc| * 1 * softEnv CL CR p (Xs k) N n := by
              apply mul_le_mul_of_nonneg_right _ hEnv0
              exact mul_le_mul (le_abs_self _) hh1 (by positivity) (abs_nonneg _)
          _ = _ := by ring
      nlinarith [hvec, h1, h2]
    have hnum2 : cn * (|CL.lamL p (Xs k) N| / kappaBal (CL.aOf p (Xs k) N)) ^ 2 ≤ softNorm CL CR p (Xs k) N ^ 2 := hnorm
    set T := |CL.lamL p (Xs k) N| / kappaBal (CL.aOf p (Xs k) N) with hTdef
    have hT2 : 0 < T ^ 2 := by positivity
    -- the envelope at an exterior row
    have henv : softEnv CL CR p (Xs k) N n ≤ (max (Real.sqrt (Cw' / cn)) (Real.sqrt (Cr' * Ck ^ 2 / cn))) * Real.exp (-c0 / Fz.step N) := by
      have hn1 := mem_Icc.mp (show n ∈ rowsOf N from hn)
      rcases le_abs'.mp hfar with hl | hr'
      · -- left
        have hb1 : uNode (Fz.step N) n ≤ CL.uc p - CL.η / 2 := by linarith
        have hmem : n ∈ Finset.Icc (0 : ℤ) (CL.chainW p (Xs k) N).NR := by
          refine mem_Icc.mpr ⟨hn1.1, ?_⟩
          obtain ⟨-, -, -, -, hB⟩ := CL.shapeW p hp (Xs k) hX0 N hN1
          by_contra hcon
          have := SoftEdgeChart.uNode_mono_le hh0.le (show (CL.chainW p (Xs k) N).NR + 1 ≤ n by omega)
          linarith
        have hsumw : ∑ i ∈ Finset.Icc (0 : ℤ) (CL.chainW p (Xs k) N).NR, softEnvWeb CL p (Xs k) N i ^ 2 ≤
            Cw' * T ^ 2 * Real.exp (-(cw / Fz.step N)) :=
          (Hw p hp N hN1 s3 (Xs k) hX0 ψL hJL hsL).trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)) (Real.exp_pos _).le)
        have hsingle : softEnvWeb CL p (Xs k) N n ^ 2 ≤ ∑ i ∈ Finset.Icc (0 : ℤ) (CL.chainW p (Xs k) N).NR, softEnvWeb CL p (Xs k) N i ^ 2 :=
          Finset.single_le_sum (f := fun i => softEnvWeb CL p (Xs k) N i ^ 2) (fun i _ => sq_nonneg _) hmem
        have hse : softEnv CL CR p (Xs k) N n = softEnvWeb CL p (Xs k) N n / softNorm CL CR p (Xs k) N := by
          unfold softEnv; rw [if_pos hb1]
        have hD : 0 ≤ Cw' / cn := by positivity
        have hsq : softEnv CL CR p (Xs k) N n ^ 2 ≤ (Cw' / cn) * Real.exp (-cw / Fz.step N) := by
          rw [hse, div_pow, div_le_iff₀ (by positivity)]
          have e1 : -cw / Fz.step N = -(cw / Fz.step N) := by ring
          rw [e1]
          calc softEnvWeb CL p (Xs k) N n ^ 2 ≤ Cw' * T ^ 2 * Real.exp (-(cw / Fz.step N)) := hsingle.trans hsumw
            _ = Cw' / cn * Real.exp (-(cw / Fz.step N)) * (cn * T ^ 2) := by field_simp
            _ ≤ Cw' / cn * Real.exp (-(cw / Fz.step N)) * softNorm CL CR p (Xs k) N ^ 2 :=
                mul_le_mul_of_nonneg_left hnum2 (by positivity)
        have := le_of_sq_exp _ _ cw (Fz.step N) hD hEnv0 hsq
        refine this.trans ?_
        calc Real.sqrt (Cw' / cn) * Real.exp (-(cw / 2) / Fz.step N) ≤ Real.sqrt (Cw' / cn) * Real.exp (-c0 / Fz.step N) :=
              mul_le_mul_of_nonneg_left (exp_mono_c (cw / 2) c0 _ hh0 hc0c) (Real.sqrt_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hex0.le
      · -- right
        have hxn : CL.η / 4 ≤ uNode (Fz.step N) n - CL.uc p := by linarith
        have hZ : 0 < CL.Zof p (Xs k) N n := Zof_pos_of_far CL hp hX0 hn hxn
        have hmem : n ∈ (rowsOf N).filter (fun n => CL.uc p + CL.η / 2 ≤ uNode (Fz.step N) n) :=
          Finset.mem_filter.mpr ⟨hn, by linarith⟩
        have hsumr : ∑ i ∈ (rowsOf N).filter (fun n => CL.uc p + CL.η / 2 ≤ uNode (Fz.step N) n),
            (|softKappa CL CR p (Xs k) N| * softEnvWeb CR p (Xs k) N ((N : ℤ) - i)) ^ 2 ≤
            Cr' * Ck ^ 2 * T ^ 2 * Real.exp (-(cr / Fz.step N)) := by
          refine (Hr p hp N hN1 s4 (Xs k) hX0 Ck ψ' hJR hsR (Hk p hp N hN1 s2 (Xs k) hX0 ha)).trans ?_
          have : Cr * Ck ^ 2 * T ^ 2 ≤ Cr' * Ck ^ 2 * T ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)) (sq_nonneg _)
          exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
        have hsingle : (|softKappa CL CR p (Xs k) N| * softEnvWeb CR p (Xs k) N ((N : ℤ) - n)) ^ 2 ≤
            ∑ i ∈ (rowsOf N).filter (fun n => CL.uc p + CL.η / 2 ≤ uNode (Fz.step N) n),
              (|softKappa CL CR p (Xs k) N| * softEnvWeb CR p (Xs k) N ((N : ℤ) - i)) ^ 2 :=
          Finset.single_le_sum (f := fun i => (|softKappa CL CR p (Xs k) N| * softEnvWeb CR p (Xs k) N ((N : ℤ) - i)) ^ 2)
            (fun i _ => sq_nonneg _) hmem
        have hse : softEnv CL CR p (Xs k) N n = |softKappa CL CR p (Xs k) N| * softEnvWeb CR p (Xs k) N ((N : ℤ) - n) / softNorm CL CR p (Xs k) N := by
          unfold softEnv
          rw [if_neg (by linarith), if_neg (not_le.mpr hZ), if_neg (by linarith)]
        have hD : 0 ≤ Cr' * Ck ^ 2 / cn := by positivity
        have hsq : softEnv CL CR p (Xs k) N n ^ 2 ≤ (Cr' * Ck ^ 2 / cn) * Real.exp (-cr / Fz.step N) := by
          rw [hse, div_pow, div_le_iff₀ (by positivity)]
          have e1 : -cr / Fz.step N = -(cr / Fz.step N) := by ring
          rw [e1]
          calc (|softKappa CL CR p (Xs k) N| * softEnvWeb CR p (Xs k) N ((N : ℤ) - n)) ^ 2
              ≤ Cr' * Ck ^ 2 * T ^ 2 * Real.exp (-(cr / Fz.step N)) := hsingle.trans hsumr
            _ = Cr' * Ck ^ 2 / cn * Real.exp (-(cr / Fz.step N)) * (cn * T ^ 2) := by field_simp
            _ ≤ Cr' * Ck ^ 2 / cn * Real.exp (-(cr / Fz.step N)) * softNorm CL CR p (Xs k) N ^ 2 :=
                mul_le_mul_of_nonneg_left hnum2 (by positivity)
        have := le_of_sq_exp _ _ cr (Fz.step N) hD hEnv0 hsq
        refine this.trans ?_
        calc Real.sqrt (Cr' * Ck ^ 2 / cn) * Real.exp (-(cr / 2) / Fz.step N) ≤ Real.sqrt (Cr' * Ck ^ 2 / cn) * Real.exp (-c0 / Fz.step N) :=
              mul_le_mul_of_nonneg_left (exp_mono_c (cr / 2) c0 _ hh0 hc0d) (Real.sqrt_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hex0.le
    calc |eigVec Um k n| + |softVec CL CR p (Xs k) N n| ≤ (|Cc| + 2 * Cenv) * softEnv CL CR p (Xs k) N n := hsum
      _ ≤ (|Cc| + 2 * Cenv) * ((max (Real.sqrt (Cw' / cn)) (Real.sqrt (Cr' * Ck ^ 2 / cn))) * Real.exp (-c0 / Fz.step N)) :=
          mul_le_mul_of_nonneg_left henv (by positivity)
      _ ≤ (1 + D1L + D1R + D2 + D4) * Real.exp (-c0 / Fz.step N) := by
          have hmx : (|Cc| + 2 * Cenv) * max (Real.sqrt (Cw' / cn)) (Real.sqrt (Cr' * Ck ^ 2 / cn)) ≤ D1L + D1R := by
            rcases max_choice (Real.sqrt (Cw' / cn)) (Real.sqrt (Cr' * Ck ^ 2 / cn)) with h | h
            · rw [h]; linarith
            · rw [h]; linarith
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ hex0.le
          linarith
  · -- conjunct 2
    have hq := hratio
    have e : |CL.lamL p X N| / softNorm CL CR p X N * |(CL.chain p X N).phi (Fz.step N) 0 2 ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋ / kappaBal (CL.aOf p X N)|
        = (|CL.lamL p X N| / kappaBal (CL.aOf p X N) / softNorm CL CR p X N) *
          |(CL.chain p X N).phi (Fz.step N) 0 2 ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋| := by
      rw [abs_div, abs_of_pos hκ]; ring
    rw [e]
    calc _ ≤ (1 / Real.sqrt cn) * (extB CL CPC * Real.exp (-(softCQ CL / Fz.step N))) :=
          mul_le_mul hq pL1 (abs_nonneg _) (by positivity)
      _ ≤ (1 / Real.sqrt cn) * (extB CL CPC * Real.exp (-c0 / Fz.step N)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpL hBL) (by positivity)
      _ = D2 * Real.exp (-c0 / Fz.step N) := by rw [hD2]; ring
      _ ≤ _ := hCfin _ hD20 (by linarith)
  · -- conjunct 3
    have hq := hratio
    have e : |CL.lamL p X N| / softNorm CL CR p X N * |(CL.chain p X N).wf 2 0 (uNode (Fz.step N) ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋) (Fz.step N) 1| / kappaBal (CL.aOf p X N)
        = (|CL.lamL p X N| / kappaBal (CL.aOf p X N) / softNorm CL CR p X N) *
          |(CL.chain p X N).wf 2 0 (uNode (Fz.step N) ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋) (Fz.step N) 1| := by ring
    rw [e]
    calc _ ≤ (1 / Real.sqrt cn) * (extB CL CPC * Real.exp (-(softCQ CL / Fz.step N))) :=
          mul_le_mul hq pL2 (abs_nonneg _) (by positivity)
      _ ≤ (1 / Real.sqrt cn) * (extB CL CPC * Real.exp (-c0 / Fz.step N)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpL hBL) (by positivity)
      _ = D2 * Real.exp (-c0 / Fz.step N) := by rw [hD2]; ring
      _ ≤ _ := hCfin _ hD20 (by linarith)
  · -- conjunct 4
    have hq := hratio
    have hrow : (N : ℤ) - ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉ =
        ⌊(CR.uc p - CR.η / 2) / (mirrorFamily Fz).step N - 1 / 2⌋ := hjR
    have pR1' : |(CR.chain p X N).phi (Fz.step N) 0 2 ((N : ℤ) - ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉)| ≤
        extB CR CPC * Real.exp (-(softCQ CR / Fz.step N)) := pR1
    rw [← hκR]
    have hk' : |softKappa CL CR p X N * CR.lamL p X N| ≤ Ck * |CL.lamL p X N| := hkb
    have hSn := hSnn
    have e : |softKappa CL CR p X N * CR.lamL p X N| / softNorm CL CR p X N *
          |(CR.chain p X N).phi (Fz.step N) 0 2 ((N : ℤ) - ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉) / kappaBal (CR.aOf p X N)| =
        (|softKappa CL CR p X N * CR.lamL p X N| / softNorm CL CR p X N / kappaBal (CR.aOf p X N)) *
          |(CR.chain p X N).phi (Fz.step N) 0 2 ((N : ℤ) - ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉)| := by
      rw [abs_div, abs_of_pos (kappaBal_pos _)]; ring
    rw [e, hκR]
    have h1 : |softKappa CL CR p X N * CR.lamL p X N| / softNorm CL CR p X N / kappaBal (CL.aOf p X N) ≤
        Ck * (1 / Real.sqrt cn) := by
      calc |softKappa CL CR p X N * CR.lamL p X N| / softNorm CL CR p X N / kappaBal (CL.aOf p X N)
          ≤ (Ck * |CL.lamL p X N|) / softNorm CL CR p X N / kappaBal (CL.aOf p X N) := by
            apply div_le_div_of_nonneg_right _ hκ.le
            exact div_le_div_of_nonneg_right hk' hSn
        _ = Ck * (|CL.lamL p X N| / kappaBal (CL.aOf p X N) / softNorm CL CR p X N) := by ring
        _ ≤ Ck * (1 / Real.sqrt cn) := mul_le_mul_of_nonneg_left hq hCk
    calc _ ≤ (Ck * (1 / Real.sqrt cn)) * (extB CR CPC * Real.exp (-(softCQ CR / Fz.step N))) :=
          mul_le_mul h1 pR1' (abs_nonneg _) (by positivity)
      _ ≤ (Ck * (1 / Real.sqrt cn)) * (extB CR CPC * Real.exp (-c0 / Fz.step N)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpR hBR) (by positivity)
      _ = D4 * Real.exp (-c0 / Fz.step N) := by rw [hD4]; ring
      _ ≤ _ := hCfin _ hD40 (by linarith)

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.propThaCollar_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms propThaCollar_proved

end Main

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.ext_left_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ext_left_row

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.floor_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floor_mirror

end FormalResearch.JacobiEigenvectors.TheoremB

end
