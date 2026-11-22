module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAssembly4

/-!
# Soft-edge assembly, part E: the off-window relative form (R2) for `PropThaW2` (2)

Source: app_thmA, proof of prop:tha-W2, Step 4 (f).

Proved here (all axiom-pinned):
* `left_lb`: for one chart, off the window, `V_k <= C |psi-hat^L_k|` on the Weber rows and on the left PC rows with `Z_k < -rho(a)` (from the chart fields `lb_weber`, `lb_pc`, F-W2-18).
* `soft_row_lb`: the four-branch version for the glued numerator.
* `soft_rel`: for `X <= bandHi + Cs0 h^2`, `softEnv_n <= Cc |softVec_n|` for `n` off the window; `soft_eigen_clause`: the whole eigen-system clause of `PropThaW2` (2) with one constant.

Differences from the paper: the lower bounds on the rows are the chart fields `lb_weber`, `lb_pc` (paper: lem:cha-W0 and `corr_PC`, `beyond`, Step 4 (f)).

Not formalised: the derivation of those two fields from the corrector and the PC envelopes.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section LeftLb

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}

/-- lower facts of one chart off the window. -/
def LeftLower {F : SymbolFamily (Par × ℝ)} (C : SoftEdgeChart F P m q U V Lm) (p : Par × ℝ) (X : ℝ) (N : ℕ) (Clb : ℝ) : Prop :=
  ∀ k ∈ rowsOf N,
    (uNode (F.step N) k ≤ C.uc p - C.η / 2 → softEnvWeb C p X N k ≤ Clb * |C.psiHatL p X N k|) ∧
    (C.uc p - C.η / 2 < uNode (F.step N) k → C.Zof p X N k < -rhoWin (C.aOf p X N) →
      |C.lamL p X N| * Molv U V (C.aOf p X N) (-(C.Zof p X N k)) ≤ Clb * |C.psiHatL p X N k|)

variable (C : SoftEdgeChart Fz P m q U V Lm)

theorem left_lb {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) :
    ∃ Clb h0 : ℝ, 0 < h0 ∧ 0 ≤ Clb ∧ ∀ p ∈ P, ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ C.δ0 →
      C.aOf p X N ≤ asmAplus C → LeftLower C p X N Clb := by
  have hCPC : 0 ≤ CPC := le_trans hf.cPC_pos.le hf.cPC_le
  have hclb := C.clb_pos
  refine ⟨(1 + CPC) / C.clb, C.softH2, C.softH2_pos, by positivity, ?_⟩
  intro p hp N hN hh X hX ha k hk
  have hk' := mem_Icc.mp hk
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hη := C.consts_pos.2.1
  constructor
  · intro hku
    have hsh := C.shapeW p hp X hX N hN
    obtain ⟨-, -, hNR0, hA, hB⟩ := hsh
    have hkW : k ≤ (C.chainW p X N).NR := by
      by_contra hcon
      have := SoftEdgeChart.uNode_mono_le hh0.le (show (C.chainW p X N).NR + 1 ≤ k by omega)
      linarith
    have hkk : k ∈ Finset.Icc (0 : ℤ) (C.chainW p X N).NR := mem_Icc.mpr ⟨hk'.1, hkW⟩
    have hl := C.lb_weber p hp X hX N hN k hkk
    have hW := C.W_defW p hp X hX N hN k hkk
    have hM := C.M_defW p hp X hX N hN k hkk
    rw [hW, hM] at hl
    rw [psiHatL_of_le C p X N hku]
    have e : softEnvWeb C p X N k = Ewell (-((k : ℝ) + 1 / 2)) |C.Y p X (uNode (Fz.step N) k) / Real.sqrt (Fz.step N)| *
        Mbal (-((k : ℝ) + 1 / 2)) (C.Y p X (uNode (Fz.step N) k) / Real.sqrt (Fz.step N)) := rfl
    rw [e]
    have h1 : Ewell (-((k : ℝ) + 1 / 2)) |C.Y p X (uNode (Fz.step N) k) / Real.sqrt (Fz.step N)| *
        Mbal (-((k : ℝ) + 1 / 2)) (C.Y p X (uNode (Fz.step N) k) / Real.sqrt (Fz.step N)) ≤ |(C.chainW p X N).phi (Fz.step N) 0 1 k| / C.clb := by
      rw [le_div_iff₀ hclb]; linarith [hl]
    refine h1.trans ?_
    have : |(C.chainW p X N).phi (Fz.step N) 0 1 k| / C.clb = (1 / C.clb) * |(C.chainW p X N).phi (Fz.step N) 0 1 k| := by ring
    rw [this]
    have h2 : (1 / C.clb) ≤ (1 + CPC) / C.clb := div_le_div_of_nonneg_right (by linarith) hclb.le
    exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  · intro hku hZ
    have hZ0 : C.Zof p X N k ≤ 0 := by
      have := rhoWin_margin (C.aOf p X N)
      linarith [this.2]
    have hu4 := lt_of_Zof_nonpos C hp hX hk hZ0
    have hhH1 : Fz.step N ≤ C.softH1 := hh.trans C.softH2_le_H1
    have hVpre : ((C.chain p X N).rescale1 (softLam C p X N)).PreValid C.cs (Fz.step N) m := C.valid p hp X hX N hN
    obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hp hX hN hhH1 hVpre
    obtain ⟨-, -, -, -, -, -, hNRu, hNRv⟩ := C.shape p hp X hX N hN
    obtain ⟨hshape1, -⟩ : (C.chain p X N).P = 3 ∧ True := ⟨hP3, trivial⟩
    have hk1 : (C.chain p X N).jj 1 < k := by
      by_contra hcon
      have := SoftEdgeChart.uNode_mono_le hh0.le (not_lt.mp hcon)
      obtain ⟨-, -, hj1, -, -, -, -, -⟩ := C.shape p hp X hX N hN
      linarith
    have hkNR : k ≤ (C.chain p X N).NR := row_le_chainNR C hp hX hN (by linarith)
    have hk2 : k ≤ (C.chain p X N).jj 2 := by
      by_contra hcon
      have hpos := Zof_pos_of_gt C hp hX hN hhH1 hVpre (k := k) (mem_Icc.mpr ⟨by omega, hkNR⟩) (by linarith)
      linarith
    have hkw : k ∈ Finset.Icc ((C.chain p X N).jj 1 + 1) ((C.chain p X N).jj 2) := mem_Icc.mpr ⟨by omega, hk2⟩
    have hl := C.lb_pc p hp X hX N hN ha k hkw (by unfold SoftEdgeChart.Zof SoftEdgeChart.aOf at hZ; exact hZ)
    have hW : (C.chain p X N).W k = Eminus (C.aOf p X N) (C.Zof p X N k) := C.W2_def p hp X hX N hN k hkw
    have hM : (C.chain p X N).M k = Mbal (C.aOf p X N) (C.Zof p X N k) :=
      C.M2_def p hp X hX N hN k (mem_Icc.mpr ⟨by omega, hkNR⟩)
    rw [hW, hM] at hl
    rw [psiHatL_of_gt C p X N hku, abs_mul, abs_div, abs_of_pos (kappaBal_pos _)]
    have hmu := molv_upper hf (C.aOf p X N) (-(C.Zof p X N k))
    rw [Wmol_neg_of_nonpos _ hZ0, Mbal_neg] at hmu
    have hκ := kappaBal_pos (C.aOf p X N)
    have hl0 := abs_nonneg (C.lamL p X N)
    set ph := |(C.chain p X N).phi (Fz.step N) 0 2 k| with hph
    set Em := Eminus (C.aOf p X N) (C.Zof p X N k) with hEm
    set Mb := Mbal (C.aOf p X N) (C.Zof p X N k) with hMb
    have h1 : Em * Mb ≤ ph / C.clb := by rw [le_div_iff₀ hclb]; linarith [hl]
    calc |C.lamL p X N| * Molv U V (C.aOf p X N) (-(C.Zof p X N k))
        ≤ |C.lamL p X N| * (CPC * (kappaBal (C.aOf p X N))⁻¹ * Em * Mb) := mul_le_mul_of_nonneg_left hmu hl0
      _ = (CPC * |C.lamL p X N| / kappaBal (C.aOf p X N)) * (Em * Mb) := by field_simp
      _ ≤ (CPC * |C.lamL p X N| / kappaBal (C.aOf p X N)) * (ph / C.clb) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (CPC / C.clb) * (|C.lamL p X N| * (ph / kappaBal (C.aOf p X N))) := by field_simp
      _ ≤ ((1 + CPC) / C.clb) * (|C.lamL p X N| * (ph / kappaBal (C.aOf p X N))) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) hclb.le) (by positivity)

end LeftLb

section RowLb

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- **R2 per row**: off the window, `V_n <= C |numerator_n|`. -/
theorem soft_row_lb (hM : SoftMirror CL CR) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ}
    (ClbL ClbR Cl : ℝ) (LL : LeftLower CL p X N ClbL) (LR : LeftLower CR p X N ClbR) (hL : ClbL ≤ Cl) (hR : ClbR ≤ Cl)
    {n : ℤ} (hn : n ∈ rowsOf N) (hΩ : n ∉ softWindow CL p X N) :
    softEnvNum CL CR p X N n ≤ Cl * |softNum CL CR p X N n| := by
  have hη := CL.consts_pos.2.1
  have hmem : ¬ |CL.Zof p X N n| ≤ rhoWin (CL.aOf p X N) := by
    intro h; exact hΩ (by unfold softWindow; simp [hn, h])
  push_neg at hmem
  unfold softNum softEnvNum
  by_cases hZ : CL.Zof p X N n ≤ 0
  · rw [show (if CL.Zof p X N n ≤ 0 then CL.psiHatL p X N n else softKappa CL CR p X N * softSeqR CR p X N n) = CL.psiHatL p X N n from if_pos hZ]
    have hZlt : CL.Zof p X N n < -rhoWin (CL.aOf p X N) := by
      rw [abs_of_nonpos hZ] at hmem; linarith
    by_cases b1 : uNode (Fz.step N) n ≤ CL.uc p - CL.η / 2
    · rw [if_pos b1]
      exact ((LL n hn).1 b1).trans (mul_le_mul_of_nonneg_right hL (abs_nonneg _))
    · rw [if_neg b1, if_pos hZ]
      exact ((LL n hn).2 (not_le.mp b1) hZlt).trans (mul_le_mul_of_nonneg_right hL (abs_nonneg _))
  · rw [if_neg hZ]
    push_neg at hZ
    have hZgt : rhoWin (CL.aOf p X N) < CL.Zof p X N n := by
      rw [abs_of_pos hZ] at hmem; exact hmem
    have hnear : CL.uc p - CL.η / 4 < uNode (Fz.step N) n := by
      by_contra h
      have := Zof_nonpos_of_near CL hp hX hn (by linarith [not_lt.mp h])
      linarith
    have b1 : ¬ uNode (Fz.step N) n ≤ CL.uc p - CL.η / 2 := by intro h; linarith
    rw [if_neg b1, if_neg (not_le.mpr hZ)]
    have hstepR : (mirrorFamily Fz).step N = Fz.step N := rfl
    have hL' := step_mul_succ Fz N
    have hrefl : uNode (Fz.step N) ((N : ℤ) - n) = Fz.L - uNode (Fz.step N) n := uNode_mirror Fz.L (Fz.step N) N n hL'
    have huc : CR.uc p = Fz.L - CL.uc p := hM.1 p hp
    have hηe : CR.η = CL.η := hM.2.2.2.1
    have hkR : (N : ℤ) - n ∈ rowsOf N := by
      simp only [rowsOf, Finset.mem_Icc] at hn ⊢; omega
    have hZR : CR.Zof p X N ((N : ℤ) - n) = -CL.Zof p X N n := Zof_mirror hM hp X N n
    have haR : CR.aOf p X N = CL.aOf p X N := aOf_mirror hM hp X N
    have hsr : softSeqR CR p X N n = CR.psiHatL p X N ((N : ℤ) - n) := rfl
    rw [hsr, abs_mul (softKappa CL CR p X N) (CR.psiHatL p X N ((N : ℤ) - n))]
    have hκ0 := abs_nonneg (softKappa CL CR p X N)
    by_cases b3 : uNode (Fz.step N) n < CL.uc p + CL.η / 2
    · rw [if_pos b3]
      have hc1 : CR.uc p - CR.η / 2 < uNode (Fz.step N) ((N : ℤ) - n) := by
        rw [hrefl, huc, hηe]; linarith
      have hc2 : CR.Zof p X N ((N : ℤ) - n) < -rhoWin (CR.aOf p X N) := by
        rw [hZR, haR]; linarith
      have h1 := (LR ((N : ℤ) - n) hkR).2 (by rw [hstepR]; exact hc1) hc2
      rw [haR, hZR, neg_neg] at h1
      have eV : |softKappa CL CR p X N * CR.lamL p X N| * Molv U V (CL.aOf p X N) (CL.Zof p X N n) =
          |softKappa CL CR p X N| * (|CR.lamL p X N| * Molv U V (CL.aOf p X N) (CL.Zof p X N n)) := by rw [abs_mul]; ring
      rw [eV]
      calc |softKappa CL CR p X N| * (|CR.lamL p X N| * Molv U V (CL.aOf p X N) (CL.Zof p X N n))
          ≤ |softKappa CL CR p X N| * (ClbR * |CR.psiHatL p X N ((N : ℤ) - n)|) := mul_le_mul_of_nonneg_left h1 hκ0
        _ ≤ |softKappa CL CR p X N| * (Cl * |CR.psiHatL p X N ((N : ℤ) - n)|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR (abs_nonneg _)) hκ0
        _ = Cl * (|softKappa CL CR p X N| * |CR.psiHatL p X N ((N : ℤ) - n)|) := by ring
    · rw [if_neg b3]
      have hc1 : uNode (Fz.step N) ((N : ℤ) - n) ≤ CR.uc p - CR.η / 2 := by
        rw [hrefl, huc, hηe]; linarith [not_lt.mp b3]
      have h1 := (LR ((N : ℤ) - n) hkR).1 (by rw [hstepR]; exact hc1)
      calc |softKappa CL CR p X N| * softEnvWeb CR p X N ((N : ℤ) - n)
          ≤ |softKappa CL CR p X N| * (ClbR * |CR.psiHatL p X N ((N : ℤ) - n)|) := mul_le_mul_of_nonneg_left h1 hκ0
        _ ≤ |softKappa CL CR p X N| * (Cl * |CR.psiHatL p X N ((N : ℤ) - n)|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR (abs_nonneg _)) hκ0
        _ = Cl * (|softKappa CL CR p X N| * |CR.psiHatL p X N ((N : ℤ) - n)|) := by ring

end RowLb

section Rel

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- **`prop:tha-W2` (2), the off-window relative clause (R2)**: for `X <= bandHi + Cs0 h^2`, `softEnv_n <= C |softVec_n|` for `n` off the window. -/
theorem soft_rel (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (Cs0 : ℝ) :
    ∃ Cc h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      X ≤ Fz.bandHi p + Cs0 * Fz.step N ^ 2 → ∀ n ∈ rowsOf N, n ∉ softWindow CL p X N →
        softEnv CL CR p X N n ≤ Cc * |softVec CL CR p X N n| := by
  obtain ⟨ClbL, h0L, h0Lp, hClL, HL⟩ := left_lb CL hf
  obtain ⟨ClbR, h0R, h0Rp, hClR, HR⟩ := left_lb CR hf
  obtain ⟨h0a, h0ap, Ha⟩ := aOf_le_of_step0 CL Cs0
  obtain ⟨h0b, h0bp, Hb⟩ := aOf_le_of_step0 CR Cs0
  refine ⟨max ClbL ClbR, min (min h0L h0R) (min h0a h0b), lt_min (lt_min h0Lp h0Rp) (lt_min h0ap h0bp), ?_⟩
  intro p hp N hN hstep X hX hX0 n hn hΩ
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hN2 : CR.N0 ≤ N := (le_max_right _ _).trans hN
  have hsL : Fz.step N ≤ h0L := (hstep.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hsR : Fz.step N ≤ h0R := (hstep.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hsa : Fz.step N ≤ h0a := (hstep.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hsb : Fz.step N ≤ h0b := (hstep.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨-, hXR⟩ := mirror_ctx hM hp hX hN1
  have haL := Ha p hp N hsa X hX hX0
  have haR := Hb p hp N hsb X (by rw [bandHi_mirror]; exact (hM.2.2.2.2.1 ▸ hX)) (by rw [bandHi_mirror]; exact hX0)
  have LL := HL p hp N hN1 hsL X hX haL
  have LR := HR p hp N hN2 hsR X hXR haR
  have hrow := soft_row_lb CL CR hM hp hX ClbL ClbR (max ClbL ClbR) LL LR (le_max_left _ _) (le_max_right _ _) hn hΩ
  have hnn : 0 ≤ softNorm CL CR p X N := Real.sqrt_nonneg _
  rw [softEnv_eq, softVec_eq, abs_div, abs_of_nonneg hnn, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hrow hnn

end Rel

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.left_lb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms left_lb

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_row_lb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_row_lb

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_rel

section Clause

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- **the eigen-system clause of `PropThaW2` (2), complete**: the three conjuncts of the frozen statement (row-wise error, `l^2` bound, off-window relative form) with one constant. -/
theorem soft_eigen_clause (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) (Cs0 : ℝ) :
    ∃ Cc h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        (∀ i, Xs i ≤ Fz.bandHi p + Cs0 * Fz.step N ^ 2) → ∀ k : Fin (N + 1), |Xs k - Fz.bandHi p| ≤ CL.δ0 →
          (∀ n ∈ rowsOf N, |eigVec Um k n - softVec CL CR p (Xs k) N n| ≤ Cc * Fz.step N ^ m * Lm (Fz.step N) * softEnv CL CR p (Xs k) N n) ∧
          ∑ n ∈ rowsOf N, softEnv CL CR p (Xs k) N n ^ 2 ≤ Cc ∧
          (∀ n ∈ rowsOf N, n ∉ softWindow CL p (Xs k) N → softEnv CL CR p (Xs k) N n ≤ Cc * |softVec CL CR p (Xs k) N n|) := by
  obtain ⟨C1, h1, h1p, H1⟩ := soft_eigen_main CL CR hM hf hm hLm Cs0
  obtain ⟨C2, h2, h2p, H2⟩ := soft_rel CL CR hM hf Cs0
  refine ⟨max C1 (max C2 0), min (min h1 h2) CL.softH2, lt_min (lt_min h1p h2p) CL.softH2_pos, ?_⟩
  intro p hp N hN hstep Xs Um hE hs0 k hX
  have hs1 : Fz.step N ≤ h1 := (hstep.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hs2 : Fz.step N ≤ h2 := (hstep.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hs3 : Fz.step N ≤ CL.softH2 := hstep.trans (min_le_right _ _)
  obtain ⟨ha, hb⟩ := H1 p hp N hN hs1 Xs Um hE hs0 k hX
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hh1 : Fz.step N ≤ 1 := hs3.trans (CL.softH2_le_H1.trans CL.softH1_le_one)
  have hε : 0 ≤ Fz.step N ^ m * Lm (Fz.step N) := powLm_nonneg CL hh0 hh1
  have hC1 : C1 ≤ max C1 (max C2 0) := le_max_left _ _
  have hC2 : C2 ≤ max C1 (max C2 0) := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨?_, hb.trans hC1, ?_⟩
  · intro n hn
    have e : max C1 (max C2 0) * Fz.step N ^ m * Lm (Fz.step N) * softEnv CL CR p (Xs k) N n =
        max C1 (max C2 0) * (Fz.step N ^ m * Lm (Fz.step N)) * softEnv CL CR p (Xs k) N n := by ring
    rw [e]
    refine (ha n hn).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hε) (softEnv_nonneg CL CR hf p (Xs k) N n)
  · intro n hn hΩ
    have := H2 p hp N hN hs2 (Xs k) hX (hs0 k) n hn hΩ
    exact this.trans (mul_le_mul_of_nonneg_right hC2 (abs_nonneg _))

end Clause

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_eigen_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_eigen_clause

end FormalResearch.JacobiEigenvectors.TheoremA

end
