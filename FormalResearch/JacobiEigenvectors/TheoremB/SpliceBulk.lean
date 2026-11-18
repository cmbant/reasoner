module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.BulkEigen
public import FormalResearch.JacobiEigenvectors.TheoremB.Statements

/-!
# Paper J, Theorem B, L3.1 bulk: independence of the splice (`prop:tha-splice` (a), bulk)

Source: Paper J `thmB.tex` `prop:tha-splice` (a) and `app_thmB.tex`, proof of `prop:tha-splice`, the normaliser estimate
`eq:tha-spl3`.  Inputs: `bulk_matching_eig` (BulkEigen.lean, clause (ii) at eigenvalues), `propThaW` norm bounds (`bulk_conj1`).

## Proved here (abstract core)

* `glueNorm_sq`: the squared normaliser of a glued vector is a sum over all rows of the switch-dependent term.
* `norm_ratio_bound`: `|x/y - 1| <= A/B` from `|x^2 - y^2| <= A` and `B <= y^2`.
* `sq_diff_window`: on the window, `|psihat^L^2 - kappa^2 psihat^R^2| <= C h^m M^2` from the matching bound and an envelope bound.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA

open scoped Classical

/-- The squared normaliser of a glued vector: `hat N^2 = sum over the rows of (psi^L_n^2 if left, kappa^2 psi^R_n^2 otherwise)`. -/
theorem glueNorm_sq (ψL ψR : ℤ → ℝ) (Ω rows : Finset ℤ) (isLeft : ℤ → Prop) :
    glueNorm ψL ψR Ω rows isLeft ^ 2 =
      ∑ n ∈ rows, (if isLeft n then ψL n ^ 2 else glueKappa ψL ψR Ω ^ 2 * ψR n ^ 2) := by
  unfold glueNorm
  have hnn : 0 ≤ (∑ n ∈ rows.filter isLeft, ψL n ^ 2) +
      glueKappa ψL ψR Ω ^ 2 * ∑ n ∈ rows.filter (fun n => ¬ isLeft n), ψR n ^ 2 := by
    have h1 : 0 ≤ ∑ n ∈ rows.filter isLeft, ψL n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
    have h2 : 0 ≤ ∑ n ∈ rows.filter (fun n => ¬ isLeft n), ψR n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
    have h3 : 0 ≤ glueKappa ψL ψR Ω ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg h3 h2]
  rw [Real.sq_sqrt hnn, Finset.sum_ite, Finset.mul_sum]

/-- **Ratio of two normalisers**: `|x/y - 1| <= |x^2 - y^2| / y^2`, and `<= A / B` when `B <= y^2`. -/
theorem norm_ratio_bound (x y A B : ℝ) (hx : 0 ≤ x) (hy : 0 < y) (hxy : |x ^ 2 - y ^ 2| ≤ A)
    (hB : 0 < B) (hBy : B ≤ y ^ 2) : |x / y - 1| ≤ A / B := by
  have hA : 0 ≤ A := (abs_nonneg _).trans hxy
  have hy2 : 0 < y ^ 2 := by positivity
  have key : |x / y - 1| * y ^ 2 ≤ |x ^ 2 - y ^ 2| := by
    have e : |x / y - 1| * y ^ 2 = |x - y| * y := by
      rw [show x / y - 1 = (x - y) / y by field_simp, abs_div, abs_of_pos hy]
      field_simp
    have e2 : |x ^ 2 - y ^ 2| = |x - y| * (x + y) := by
      rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x + y)]
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have h1 : |x / y - 1| ≤ A / y ^ 2 := by
    rw [le_div_iff₀ hy2]
    exact key.trans hxy
  exact h1.trans (div_le_div_of_nonneg_left hA hB hBy)

/-- **Two splits of a glued vector differ only on the window** (`eq:tha-spl3`): if two split predicates agree on the rows outside
`Ω`, the squared normalisers differ by at most the sum of `|psi^L^2 - kappa^2 psi^R^2|` over `Ω`. -/
theorem glue_norm_sq_diff (ψL ψR : ℤ → ℝ) (Ω rows : Finset ℤ) (isA isB : ℤ → Prop)
    (hAB : ∀ n ∈ rows, n ∉ Ω → (isA n ↔ isB n)) :
    |glueNorm ψL ψR Ω rows isA ^ 2 - glueNorm ψL ψR Ω rows isB ^ 2| ≤
      ∑ n ∈ rows, (if n ∈ Ω then |ψL n ^ 2 - glueKappa ψL ψR Ω ^ 2 * ψR n ^ 2| else 0) := by
  rw [glueNorm_sq, glueNorm_sq, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  by_cases hΩ : n ∈ Ω
  · rw [if_pos hΩ]
    by_cases ha : isA n <;> by_cases hb : isB n <;> simp [ha, hb, abs_sub_comm]
  · rw [if_neg hΩ]
    have hiff := hAB n hn hΩ
    by_cases ha : isA n
    · have hb : isB n := hiff.mp ha
      simp [ha, hb]
    · have hb : ¬ isB n := fun hb => ha (hiff.mpr hb)
      simp [ha, hb]

/-- **The split of the normaliser outside the window**: for `ns` in the window `Ω = {c' <= u_n <= c}`, the splice predicate
`n <= ns` and the standard predicate `u_n <= c` agree on the rows outside `Ω`. -/
theorem split_agree_outside (h c c' : ℝ) (hh : 0 ≤ h) (Ω rows : Finset ℤ) (hΩ : ∀ n, n ∈ Ω ↔ n ∈ rows ∧ c' ≤ uNode h n ∧ uNode h n ≤ c)
    (ns : ℤ) (hns : ns ∈ Ω) (n : ℤ) (hn : n ∈ rows) (hnΩ : n ∉ Ω) :
    (n ≤ ns ↔ uNode h n ≤ c) := by
  have hns' := (hΩ ns).mp hns
  constructor
  · intro hle
    exact (uNode_le_of_le hh hle).trans hns'.2.2
  · intro hu
    by_contra hcon
    push_neg at hcon
    have h1 := uNode_le_of_le hh hcon.le
    have hnot : ¬ (c' ≤ uNode h n ∧ uNode h n ≤ c) := fun h2 => hnΩ ((hΩ n).mpr ⟨hn, h2⟩)
    have hlt : uNode h n < c' := by
      by_contra hc
      push_neg at hc
      exact hnot ⟨hc, hu⟩
    linarith [hns'.2.1]

/-- **Pointwise window bound**: `|psi^L^2 - kappa^2 psi^R^2| <= Cm K eta M^2` from the matching bound `|psi^L - kappa psi^R| <= Cm eta M`
and the envelope bound `|psi^L| + |kappa||psi^R| <= K M`. -/
theorem sq_diff_window (pL pR κ M Cm K η : ℝ) (hM0 : 0 ≤ M) (hCm : 0 ≤ Cm) (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hmatch : |pL - κ * pR| ≤ Cm * η * M) (henv : |pL| + |κ| * |pR| ≤ K * M) :
    |pL ^ 2 - κ ^ 2 * pR ^ 2| ≤ Cm * K * η * M ^ 2 := by
  have e : pL ^ 2 - κ ^ 2 * pR ^ 2 = (pL - κ * pR) * (pL + κ * pR) := by ring
  rw [e, abs_mul]
  have hsum : |pL + κ * pR| ≤ K * M := by
    have := abs_add_le pL (κ * pR)
    rw [abs_mul] at this
    linarith
  have hCM : 0 ≤ Cm * η * M := mul_nonneg (mul_nonneg hCm hη) hM0
  calc |pL - κ * pR| * |pL + κ * pR| ≤ (Cm * η * M) * (K * M) :=
        mul_le_mul hmatch hsum (abs_nonneg _) hCM
    _ = Cm * K * η * M ^ 2 := by ring

/-- **Window sum**: a sum over the rows of the window-indicator of a bound by `C M^2` is at most `C` times the row sum of `M^2`. -/
theorem window_indicator_sum_le (Ω rows : Finset ℤ) (f : ℤ → ℝ) (hΩ : Ω ⊆ rows) (hf : ∀ n ∈ Ω, 0 ≤ f n) :
    ∑ n ∈ rows, (if n ∈ Ω then f n else 0) = ∑ n ∈ Ω, f n := by
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hΩ]

/-- `(h^(-1/4))^2 = (sqrt h)^{-1}`. -/
theorem rpow_quarter_neg_sq (h : ℝ) (hh : 0 < h) : (h ^ (-(1 : ℝ) / 4)) ^ 2 = (Real.sqrt h)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le, Real.sqrt_eq_rpow, ← Real.rpow_neg hh.le]
  norm_num

set_option maxHeartbeats 2000000 in
/-- **Clause (i) of `prop:tha-splice` (a), bulk, at an eigenvalue** (normaliser ratio): the glued normaliser of the splice `ns`
over the bulk window differs from the standard normaliser by `C h^m` relatively, uniformly in `ns`, `X`, `N`, the eigenvector. -/
theorem bulk_norm_clause {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V)
    (hm : 1 ≤ m) (hcoup : CR.c = Fz.L - CL.c' ∧ CR.c' = Fz.L - CL.c) (r : ℕ) (hr : StdAssump Fz P (m / 2) r) :
    ∃ Cn h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ ns ∈ bulkWindow CL N, ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        IsEigenSystem (Fz.jacobiMat p N) Xs Um → ∀ k : Fin (N + 1), Xs k = X →
          |glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns /
              bulkNorm CL CR p X N - 1| ≤ Cn * Fz.step N ^ m := by
  obtain ⟨Cm, h1m, hh1m, hmatch⟩ := bulk_matching_eig CL CR hm hcoup r hr
  have hr' := hr
  obtain ⟨hPc, hEK, -⟩ := hr'
  obtain ⟨Cc0, h0k, cN, CN, cκ, Cκ, hh0k, hcN, hcκ, hκall⟩ := bulk_conj1 CL CR hm hcoup r hr
  have hcM : 0 < CL.cM := CL.consts_pos.2.2.2.2.2.1
  obtain ⟨KgL, hKgL⟩ : ∃ x : ℝ, x = (CL.cs.KA + CL.cs.KB) * CL.cs.Kw + 1 := ⟨_, rfl⟩
  obtain ⟨KgR, hKgR⟩ : ∃ x : ℝ, x = (CR.cs.KA + CR.cs.KB) * CR.cs.Kw + 1 := ⟨_, rfl⟩
  obtain ⟨CML, hCML⟩ : ∃ x : ℝ, x = CL.CM + 1 := ⟨_, rfl⟩
  obtain ⟨CMR, hCMR⟩ : ∃ x : ℝ, x = CR.CM + 1 := ⟨_, rfl⟩
  obtain ⟨CsL, hCsL⟩ : ∃ x : ℝ, x = CL.Csum + 1 := ⟨_, rfl⟩
  have hKgL0 : 0 < KgL := by
    have := mul_nonneg (add_nonneg CL.cs.KA_nonneg CL.cs.KB_nonneg) CL.cs.Kw_nonneg
    rw [hKgL]; linarith
  have hKgR0 : 0 < KgR := by
    have := mul_nonneg (add_nonneg CR.cs.KA_nonneg CR.cs.KB_nonneg) CR.cs.Kw_nonneg
    rw [hKgR]; linarith
  have hCML0 : 0 < CML := by rw [hCML]; linarith [CL.consts_pos.2.2.2.2.2.2.1, hcM]
  have hCMR0 : 0 < CMR := by rw [hCMR]; linarith [CR.consts_pos.2.2.2.2.2.2.1, CR.consts_pos.2.2.2.2.2.1]
  have hCsL0 : 0 ≤ CsL := by rw [hCsL]; linarith [CL.consts_pos.2.2.2.2.2.2.2.2.1]
  obtain ⟨CA, hCA0, hCA⟩ := bondA_bound_of_EK Fz P (m / 2) r hPc hEK
  obtain ⟨CEL, hCEL⟩ : ∃ x : ℝ, x = |CL.cs.CE| + 1 := ⟨_, rfl⟩
  obtain ⟨CER, hCER⟩ : ∃ x : ℝ, x = |CR.cs.CE| + 1 := ⟨_, rfl⟩
  obtain ⟨CsR, hCsR⟩ : ∃ x : ℝ, x = CR.Csum + 1 := ⟨_, rfl⟩
  obtain ⟨CAg, hCAg⟩ : ∃ x : ℝ, x = CA + 1 := ⟨_, rfl⟩
  have hCEL0 : 0 < CEL := by rw [hCEL]; linarith [abs_nonneg CL.cs.CE]
  have hCER0 : 0 < CER := by rw [hCER]; linarith [abs_nonneg CR.cs.CE]
  have hCsR0 : 0 < CsR := by rw [hCsR]; linarith [CR.consts_pos.2.2.2.2.2.2.2.2.1]
  have hCAg0 : 0 < CAg := by rw [hCAg]; linarith
  have hKgCL : (CL.cs.KA + CL.cs.KB) * CL.cs.Kw ≤ KgL := by rw [hKgL]; linarith
  have hKgCR : (CR.cs.KA + CR.cs.KB) * CR.cs.Kw ≤ KgR := by rw [hKgR]; linarith
  have hCEgCL : CL.cs.CE ≤ CEL := by rw [hCEL]; linarith [le_abs_self CL.cs.CE]
  have hCEgCR : CR.cs.CE ≤ CER := by rw [hCER]; linarith [le_abs_self CR.cs.CE]
  have hCMgCL : CL.CM ≤ CML := by rw [hCML]; linarith
  have hCMgCR : CR.CM ≤ CMR := by rw [hCMR]; linarith
  have hCsgCL : CL.Csum ≤ CsL := by rw [hCsL]; linarith
  have hCsgCR : CR.Csum ≤ CsR := by rw [hCsR]; linarith
  have hCAgCA : CA ≤ CAg := by rw [hCAg]; linarith
  -- the constants of the statement
  have hcLD : 0 < CL.c - CL.c' := by linarith [CL.consts_pos.2.1]
  obtain ⟨K4, hK4⟩ : ∃ x : ℝ, x = (KgL * CML + |Cκ| * KgR * CMR) / CL.cM := ⟨_, rfl⟩
  have hK40 : 0 ≤ K4 := by
    rw [hK4]
    apply div_nonneg _ hcM.le
    have h1 := mul_nonneg hKgL0.le hCML0.le
    have h2 := mul_nonneg (mul_nonneg (abs_nonneg Cκ) hKgR0.le) hCMR0.le
    linarith
  obtain ⟨SM, hSM⟩ : ∃ x : ℝ, x = CL.Csum + CL.CM ^ 2 := ⟨_, rfl⟩
  have hSM0 : 0 ≤ SM := by
    rw [hSM]
    have := CL.consts_pos.2.2.2.2.2.2.2.2.1
    have := sq_nonneg CL.CM
    linarith
  obtain ⟨Cn, hCn⟩ : ∃ x : ℝ, x = |Cm| * K4 * SM / cN ^ 2 := ⟨_, rfl⟩
  have hCn0 : 0 ≤ Cn := by rw [hCn]; have := abs_nonneg Cm; positivity
  refine ⟨Cn, min (min h1m h0k) (min 1 (CL.c - CL.c')), lt_min (lt_min hh1m hh0k) (lt_min one_pos hcLD), ?_⟩
  intro p hp X hX N hN hstep ns hns Xs Um hE k hk
  have hN1 : CL.N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : CR.N0 ≤ N := le_trans (le_max_right _ _) hN
  have hst : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L := step_mul_succ Fz N
  have hsm : Fz.step N ≤ h1m := hstep.trans (min_le_left _ _ |>.trans (min_le_left _ _))
  have hsk : Fz.step N ≤ h0k := hstep.trans (min_le_left _ _ |>.trans (min_le_right _ _))
  have hs1 : Fz.step N ≤ 1 := hstep.trans (min_le_right _ _ |>.trans (min_le_left _ _))
  have hsw : Fz.step N ≤ CL.c - CL.c' := hstep.trans (min_le_right _ _ |>.trans (min_le_right _ _))
  have hhcL : Fz.step N ≤ CL.c - CL.c' := hsw
  have hhcR : Fz.step N ≤ CR.c - CR.c' := by
    have hCRD : CR.c - CR.c' = CL.c - CL.c' := by rw [hcoup.1, hcoup.2]; ring
    rw [hCRD]; exact hsw
  -- the clause (ii) matching at this eigenvalue, with the constant |Cm|
  have hcl2 : ∀ n ∈ bulkWindow CL N, |CL.psiHatL p X N n - bulkKappa CL CR p X N * bulkSeqR CR p X N n| ≤
      |Cm| * Fz.step N ^ m * (CL.chain p X N).M n := by
    intro n hn
    refine (hmatch p hp X hX N hN hsm Xs Um hE k hk n hn).trans ?_
    have hη : 0 ≤ Fz.step N ^ m := pow_nonneg hst.le _
    have hM : 0 ≤ (CL.chain p X N).M n := by
      have hn' := window_sub_rows CL p hp X hX N hN1 hst n hn
      have hcn : CL.c' ≤ uNode (Fz.step N) n := by
        have h := hn
        unfold bulkWindow at h
        exact (Finset.mem_filter.mp h).2.1
      exact le_trans (mul_nonneg hcM.le (Real.rpow_nonneg hst.le _)) (CL.M_osc p hp X hX N hN1 n hn' hcn).1
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hη) hM
  -- the chart facts of the two charts on the rows
  have hAL0 : ∀ j : ℤ, 0 ≤ j → j ≤ (CL.chain p X N).NR - 1 → |(CL.chain p X N).A j| ≤ CA := by
    intro j h0 h1
    rw [CL.A_bond p hp X hX N hN1 j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
    exact hCA p hp N j
  have hAR0 : ∀ j : ℤ, 0 ≤ j → j ≤ (CR.chain p X N).NR - 1 → |(CR.chain p X N).A j| ≤ CA := by
    intro j h0 h1
    rw [CR.A_bond p hp X hX N hN2 j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), bondA_mirror]
    exact hCA p hp N _
  have hAL : ∀ j : ℤ, 0 ≤ j → j ≤ (CL.chain p X N).NR - 1 → |(CL.chain p X N).A j| ≤ CAg :=
    fun j h0 h1 => (hAL0 j h0 h1).trans hCAgCA
  have hAR : ∀ j : ℤ, 0 ≤ j → j ≤ (CR.chain p X N).NR - 1 → |(CR.chain p X N).A j| ≤ CAg :=
    fun j h0 h1 => (hAR0 j h0 h1).trans hCAgCA
  obtain ⟨LA, LB, LC, LD, -⟩ := chart_side_facts CL p hp X hX N hN1 hhcL KgL CEL CML CL.cs.cm CsL CAg hKgL0 hCEL0
    hCML0 CL.cs.cm_pos hCAg0 hKgCL hCEgCL hCMgCL le_rfl hCsgCL hAL
  obtain ⟨RA, RB, RC, RD, -⟩ := chart_side_facts CR p hp X hX N hN2 hhcR KgR CER CMR CR.cs.cm CsR CAg hKgR0 hCER0
    hCMR0 CR.cs.cm_pos hCAg0 hKgCR hCEgCR hCMgCR le_rfl hCsgCR hAR
  -- the envelope bound on the window
  have hM4 : ∀ n ∈ bulkWindow CL N, |CL.psiHatL p X N n| + |bulkKappa CL CR p X N| * |bulkSeqR CR p X N n| ≤
      K4 * (CL.chain p X N).M n := by
    intro n hn
    have hnL := Finset.mem_Icc.mp (window_sub_rows CL p hp X hX N hN1 hst n hn)
    have hjR := Finset.mem_Icc.mp (window_sub_rows CR p hp X hX N hN2 hst ((N : ℤ) - n)
      (mirror_mem_window CL CR hcoup N hLs n hn))
    have hcn : CL.c' ≤ uNode (Fz.step N) n := by
      have h := hn
      unfold bulkWindow at h
      exact (Finset.mem_filter.mp h).2.1
    have hcjR : CR.c' ≤ uNode (Fz.step N) ((N : ℤ) - n) := by
      have h := mirror_mem_window CL CR hcoup N hLs n hn
      unfold bulkWindow at h
      exact (Finset.mem_filter.mp h).2.1
    have hMlow := (CL.M_osc p hp X hX N hN1 n (Finset.mem_Icc.mpr hnL) hcn).1
    have hLa := LA n hnL.1 hnL.2
    have hLd := LD n hnL.1 hnL.2 hcn
    have hRa := RA ((N : ℤ) - n) hjR.1 hjR.2
    have hRd := RD ((N : ℤ) - n) hjR.1 hjR.2 hcjR
    have hκb : |bulkKappa CL CR p X N| ≤ |Cκ| :=
      ((hκall p hp X hX N hN hsk).2.2.2.1).trans (le_abs_self _)
    set q := Fz.step N ^ ((1 : ℝ) / 4) with hq
    have hq0 : 0 ≤ q := Real.rpow_nonneg hst.le _
    have hS0 : 0 ≤ KgL * CML + |Cκ| * KgR * CMR := by
      have := mul_nonneg hKgL0.le hCML0.le
      have := mul_nonneg (mul_nonneg (abs_nonneg Cκ) hKgR0.le) hCMR0.le
      linarith
    have hpsiR : |bulkSeqR CR p X N n| ≤ KgR * CMR * q := by
      have hRe : KgR * CR.envL p X N ((N : ℤ) - n) ≤ KgR * (CMR * q) :=
        mul_le_mul_of_nonneg_left hRd hKgR0.le
      exact hRa.trans (hRe.trans (le_of_eq (by ring)))
    have hpsiL : |CL.psiHatL p X N n| ≤ KgL * CML * q := by
      have hLe : KgL * CL.envL p X N n ≤ KgL * (CML * q) := mul_le_mul_of_nonneg_left hLd hKgL0.le
      exact hLa.trans (hLe.trans (le_of_eq (by ring)))
    have hsum : |CL.psiHatL p X N n| + |bulkKappa CL CR p X N| * |bulkSeqR CR p X N n| ≤
        (KgL * CML + |Cκ| * KgR * CMR) * q := by
      have h1 : |bulkKappa CL CR p X N| * |bulkSeqR CR p X N n| ≤ |Cκ| * (KgR * CMR * q) :=
        mul_le_mul hκb hpsiR (abs_nonneg _) (abs_nonneg _)
      calc _ ≤ KgL * CML * q + |Cκ| * (KgR * CMR * q) := add_le_add hpsiL h1
        _ = (KgL * CML + |Cκ| * KgR * CMR) * q := by ring
    have hqM : q ≤ (CL.chain p X N).M n / CL.cM := by
      rw [le_div_iff₀ hcM, mul_comm]
      exact hMlow
    calc _ ≤ (KgL * CML + |Cκ| * KgR * CMR) * q := hsum
      _ ≤ (KgL * CML + |Cκ| * KgR * CMR) * ((CL.chain p X N).M n / CL.cM) :=
          mul_le_mul_of_nonneg_left hqM hS0
      _ = K4 * (CL.chain p X N).M n := by rw [hK4]; ring
  -- the sum of the squared overlap moduli
  have hWsub : bulkWindow CL N ⊆ rowsOf N := fun n hn => by
    have h := hn
    unfold bulkWindow at h
    exact (Finset.mem_filter.mp h).1
  have hsumM : ∑ n ∈ bulkWindow CL N, (CL.chain p X N).M n ^ 2 ≤ SM / Real.sqrt (Fz.step N) := by
    have hrow := chart_row_facts CL p hp X hX N hN1 hst hhcL
    have hsub : ∑ n ∈ bulkWindow CL N, (CL.chain p X N).M n ^ 2 ≤
        ∑ j ∈ Finset.Icc (0 : ℤ) (CL.chain p X N).NR, (CL.chain p X N).M j ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => window_sub_rows CL p hp X hX N hN1 hst n hn)
        (fun j _ _ => sq_nonneg _)
    have hs : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hst
    have hsq : Real.sqrt (Fz.step N) ≤ 1 / Real.sqrt (Fz.step N) := by
      rw [le_div_iff₀ hs]
      nlinarith [Real.sq_sqrt hst.le]
    have hrow' := hrow.2
    have e : SM / Real.sqrt (Fz.step N) = CL.Csum / Real.sqrt (Fz.step N) +
        CL.CM ^ 2 * (1 / Real.sqrt (Fz.step N)) := by
      rw [hSM]; ring
    have hCM2 : CL.CM ^ 2 * Real.sqrt (Fz.step N) ≤ CL.CM ^ 2 * (1 / Real.sqrt (Fz.step N)) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    rw [e]
    have hrow'' : ∑ j ∈ Finset.Icc (0 : ℤ) (CL.chain p X N).NR, (CL.chain p X N).M j ^ 2 ≤
        CL.Csum / Real.sqrt (Fz.step N) + CL.CM ^ 2 * Real.sqrt (Fz.step N) := hrow'
    linarith
  -- the normaliser difference: the two splits differ only on the window
  have hΩ : ∀ n, n ∈ bulkWindow CL N ↔ n ∈ rowsOf N ∧ CL.c' ≤ uNode (Fz.step N) n ∧ uNode (Fz.step N) n ≤ CL.c :=
    fun n => by unfold bulkWindow; exact Finset.mem_filter
  have hAB : ∀ n ∈ rowsOf N, n ∉ bulkWindow CL N → (n ≤ ns ↔ uNode (Fz.step N) n ≤ CL.c) :=
    fun n hn hnW => split_agree_outside (Fz.step N) CL.c CL.c' hst.le (bulkWindow CL N) (rowsOf N) hΩ ns hns n hn hnW
  have hdiff := glue_norm_sq_diff (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N)
    (fun n => n ≤ ns) (fun n => uNode (Fz.step N) n ≤ CL.c) hAB
  have hMnn : ∀ n ∈ bulkWindow CL N, 0 ≤ (CL.chain p X N).M n := by
    intro n hn
    have hn' := window_sub_rows CL p hp X hX N hN1 hst n hn
    have hcn : CL.c' ≤ uNode (Fz.step N) n := by
      have h := hn
      unfold bulkWindow at h
      exact (Finset.mem_filter.mp h).2.1
    exact le_trans (mul_nonneg hcM.le (Real.rpow_nonneg hst.le _)) (CL.M_osc p hp X hX N hN1 n hn' hcn).1
  have hpt : ∀ n ∈ bulkWindow CL N, |CL.psiHatL p X N n ^ 2 - bulkKappa CL CR p X N ^ 2 * bulkSeqR CR p X N n ^ 2| ≤
      |Cm| * K4 * Fz.step N ^ m * (CL.chain p X N).M n ^ 2 :=
    fun n hn => sq_diff_window _ _ _ _ _ _ _ (hMnn n hn) (abs_nonneg Cm) (pow_nonneg hst.le _) hK40
      (hcl2 n hn) (hM4 n hn)
  have hnn : ∀ n ∈ bulkWindow CL N, 0 ≤ |Cm| * K4 * Fz.step N ^ m * (CL.chain p X N).M n ^ 2 := fun n _ =>
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hK40) (pow_nonneg hst.le _)) (sq_nonneg _)
  have hsumD : ∑ n ∈ rowsOf N, (if n ∈ bulkWindow CL N then
      |CL.psiHatL p X N n ^ 2 - bulkKappa CL CR p X N ^ 2 * bulkSeqR CR p X N n ^ 2| else 0) ≤
      |Cm| * K4 * Fz.step N ^ m * (SM / Real.sqrt (Fz.step N)) := by
    calc _ ≤ ∑ n ∈ rowsOf N, (if n ∈ bulkWindow CL N then
          |Cm| * K4 * Fz.step N ^ m * (CL.chain p X N).M n ^ 2 else 0) := by
          refine Finset.sum_le_sum fun n _ => ?_
          by_cases hnW : n ∈ bulkWindow CL N
          · simp only [hnW, if_true]
            exact hpt n hnW
          · simp only [hnW, if_false, le_refl]
      _ = ∑ n ∈ bulkWindow CL N, |Cm| * K4 * Fz.step N ^ m * (CL.chain p X N).M n ^ 2 :=
          window_indicator_sum_le (bulkWindow CL N) (rowsOf N)
            (fun n => |Cm| * K4 * Fz.step N ^ m * (CL.chain p X N).M n ^ 2) hWsub hnn
      _ = |Cm| * K4 * Fz.step N ^ m * ∑ n ∈ bulkWindow CL N, (CL.chain p X N).M n ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ |Cm| * K4 * Fz.step N ^ m * (SM / Real.sqrt (Fz.step N)) :=
          mul_le_mul_of_nonneg_left hsumM (mul_nonneg (mul_nonneg (abs_nonneg _) hK40) (pow_nonneg hst.le _))
  -- the standard normaliser is bounded below by `cN h^(-1/4)`
  obtain ⟨hyPos, hyLow, -, -, -⟩ := hκall p hp X hX N hN hsk
  have hB : cN ^ 2 / Real.sqrt (Fz.step N) ≤ bulkNorm CL CR p X N ^ 2 := by
    have hcn0 : 0 ≤ cN * Fz.step N ^ (-(1 : ℝ) / 4) := mul_nonneg hcN.le (Real.rpow_nonneg hst.le _)
    have h2 := pow_le_pow_left₀ hcn0 hyLow 2
    have e : (cN * Fz.step N ^ (-(1 : ℝ) / 4)) ^ 2 = cN ^ 2 / Real.sqrt (Fz.step N) := by
      rw [mul_pow, rpow_quarter_neg_sq _ hst]
      ring
    rw [e] at h2
    exact h2
  have hBpos : 0 < cN ^ 2 / Real.sqrt (Fz.step N) := div_pos (by positivity) (Real.sqrt_pos.mpr hst)
  have hx2 : |glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns ^ 2 -
      bulkNorm CL CR p X N ^ 2| ≤ |Cm| * K4 * Fz.step N ^ m * (SM / Real.sqrt (Fz.step N)) :=
    hdiff.trans hsumD
  have hratio := norm_ratio_bound _ _ _ _ (Real.sqrt_nonneg _) hyPos hx2 hBpos hB
  refine hratio.trans (le_of_eq ?_)
  have hs : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hst
  rw [hCn]
  field_simp
/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.glueNorm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.glueNorm_sq

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.norm_ratio_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.norm_ratio_bound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.glue_norm_sq_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.glue_norm_sq_diff

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.split_agree_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.split_agree_outside

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.sq_diff_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.sq_diff_window

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.window_indicator_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.window_indicator_sum_le

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.rpow_quarter_neg_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.rpow_quarter_neg_sq

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulk_norm_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulk_norm_clause

/-- **Two normalisations of one value**: `|v/N1 - v/N0| <= 2 e |v| / N0` when `|N1/N0 - 1| <= e <= 1/2`. -/
theorem div_pair_bound (v N0 N1 e : ℝ) (hN0 : 0 < N0) (hN1 : 0 < N1) (hr : |N1 / N0 - 1| ≤ e) (he : e ≤ 1 / 2) :
    |v / N1 - v / N0| ≤ 2 * e * |v| / N0 := by
  have hrel : |N1 - N0| ≤ e * N0 := by
    have e1 : N1 - N0 = (N1 / N0 - 1) * N0 := by field_simp
    rw [e1, abs_mul, abs_of_pos hN0]
    exact mul_le_mul_of_nonneg_right hr hN0.le
  have hlow : N0 / 2 ≤ N1 := by
    have h := (abs_le.mp hr).1
    have h2 : 1 / 2 ≤ N1 / N0 := by linarith
    rw [le_div_iff₀ hN0] at h2
    linarith
  have e2 : v / N1 - v / N0 = v * (N0 - N1) / (N1 * N0) := by field_simp
  rw [e2, abs_div, abs_mul, abs_of_pos (mul_pos hN1 hN0)]
  have hd : |N0 - N1| ≤ e * N0 := by rw [abs_sub_comm]; exact hrel
  have hnum : |v| * |N0 - N1| ≤ |v| * (e * N0) := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
  rw [div_le_div_iff₀ (mul_pos hN1 hN0) hN0]
  have : |v| * |N0 - N1| * N0 ≤ |v| * (e * N0) * N0 := mul_le_mul_of_nonneg_right hnum hN0.le
  have he0 : 0 ≤ e := (abs_nonneg _).trans hr
  have hN0le : N0 ≤ 2 * N1 := by linarith [hlow]
  have hen : e * N0 ≤ 2 * N1 * e := by
    calc e * N0 ≤ e * (2 * N1) := mul_le_mul_of_nonneg_left hN0le he0
      _ = 2 * N1 * e := by ring
  have h3 : |v| * (e * N0) * N0 ≤ 2 * e * |v| * N1 * N0 := by
    have h4 := mul_le_mul_of_nonneg_left hen (abs_nonneg v)
    have h5 := mul_le_mul_of_nonneg_right h4 hN0.le
    calc |v| * (e * N0) * N0 = |v| * (e * N0) * N0 := rfl
      _ ≤ |v| * (2 * N1 * e) * N0 := h5
      _ = 2 * e * |v| * N1 * N0 := by ring
  calc |v| * |N0 - N1| * N0 ≤ |v| * (e * N0) * N0 := this
    _ ≤ 2 * e * |v| * N1 * N0 := h3
    _ = 2 * e * |v| * (N1 * N0) := by ring

set_option maxHeartbeats 4000000 in
/-- **Clause (iii) of `prop:tha-splice` (a), bulk, at an eigenvalue**: the eigenvector is compared with the spliced vector
`splicedVec ns` within `C h^m bulkEnv`, uniformly in `ns` (the splice-independence of the comparison vector). -/
theorem bulk_vec_clause {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V)
    (hm : 1 ≤ m) (hcoup : CR.c = Fz.L - CL.c' ∧ CR.c' = Fz.L - CL.c) (r : ℕ) (hr : StdAssump Fz P (m / 2) r) :
    ∃ C3 h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ ns ∈ bulkWindow CL N, ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        IsEigenSystem (Fz.jacobiMat p N) Xs Um → ∀ k : Fin (N + 1), Xs k = X → ∀ n ∈ rowsOf N,
          |eigVec Um k n - splicedVec (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns n| ≤
            C3 * Fz.step N ^ m * bulkEnv CL CR p X N n := by
  obtain ⟨Cn, h1n, hh1n, hnorm⟩ := bulk_norm_clause CL CR hm hcoup r hr
  obtain ⟨Cm, h1m, hh1m, hmatch⟩ := bulk_matching_eig CL CR hm hcoup r hr
  obtain ⟨Cc0, h0k, cN, CN, cκ, Cκ, hh0k, hcN, hcκ, hκall⟩ := bulk_conj1 CL CR hm hcoup r hr
  have hr' := hr
  obtain ⟨hPc, hEK, hH⟩ := hr'
  obtain ⟨CA, hCA0, hCA⟩ := bondA_bound_of_EK Fz P (m / 2) r hPc hEK
  have hcM : 0 < CL.cM := CL.consts_pos.2.2.2.2.2.1
  obtain ⟨KgL, hKgL⟩ : ∃ x : ℝ, x = (CL.cs.KA + CL.cs.KB) * CL.cs.Kw + 1 := ⟨_, rfl⟩
  obtain ⟨KgR, hKgR⟩ : ∃ x : ℝ, x = (CR.cs.KA + CR.cs.KB) * CR.cs.Kw + 1 := ⟨_, rfl⟩
  have hKgL0 : 0 < KgL := by
    have := mul_nonneg (add_nonneg CL.cs.KA_nonneg CL.cs.KB_nonneg) CL.cs.Kw_nonneg
    rw [hKgL]; linarith
  have hKgR0 : 0 < KgR := by
    have := mul_nonneg (add_nonneg CR.cs.KA_nonneg CR.cs.KB_nonneg) CR.cs.Kw_nonneg
    rw [hKgR]; linarith
  have hKgCL : (CL.cs.KA + CL.cs.KB) * CL.cs.Kw ≤ KgL := by rw [hKgL]; linarith
  have hKgCR : (CR.cs.KA + CR.cs.KB) * CR.cs.Kw ≤ KgR := by rw [hKgR]; linarith
  obtain ⟨CML, hCML⟩ : ∃ x : ℝ, x = CL.CM + 1 := ⟨_, rfl⟩
  obtain ⟨CMR, hCMR⟩ : ∃ x : ℝ, x = CR.CM + 1 := ⟨_, rfl⟩
  obtain ⟨CsL, hCsL⟩ : ∃ x : ℝ, x = CL.Csum + 1 := ⟨_, rfl⟩
  obtain ⟨CsR, hCsR⟩ : ∃ x : ℝ, x = CR.Csum + 1 := ⟨_, rfl⟩
  obtain ⟨CEL, hCEL⟩ : ∃ x : ℝ, x = |CL.cs.CE| + 1 := ⟨_, rfl⟩
  obtain ⟨CER, hCER⟩ : ∃ x : ℝ, x = |CR.cs.CE| + 1 := ⟨_, rfl⟩
  obtain ⟨CAg, hCAg⟩ : ∃ x : ℝ, x = CA + 1 := ⟨_, rfl⟩
  have hCML0 : 0 < CML := by rw [hCML]; linarith [CL.consts_pos.2.2.2.2.2.2.1, hcM]
  have hCMR0 : 0 < CMR := by rw [hCMR]; linarith [CR.consts_pos.2.2.2.2.2.2.1, CR.consts_pos.2.2.2.2.2.1]
  have hCsL0 : 0 < CsL := by rw [hCsL]; linarith [CL.consts_pos.2.2.2.2.2.2.2.2.1]
  have hCsR0 : 0 < CsR := by rw [hCsR]; linarith [CR.consts_pos.2.2.2.2.2.2.2.2.1]
  have hCEL0 : 0 < CEL := by rw [hCEL]; linarith [abs_nonneg CL.cs.CE]
  have hCER0 : 0 < CER := by rw [hCER]; linarith [abs_nonneg CR.cs.CE]
  have hCAg0 : 0 < CAg := by rw [hCAg]; linarith
  have hCEgCL : CL.cs.CE ≤ CEL := by rw [hCEL]; linarith [le_abs_self CL.cs.CE]
  have hCEgCR : CR.cs.CE ≤ CER := by rw [hCER]; linarith [le_abs_self CR.cs.CE]
  have hCMgCL : CL.CM ≤ CML := by rw [hCML]; linarith
  have hCMgCR : CR.CM ≤ CMR := by rw [hCMR]; linarith
  have hCsgCL : CL.Csum ≤ CsL := by rw [hCsL]; linarith
  have hCsgCR : CR.Csum ≤ CsR := by rw [hCsR]; linarith
  have hCAgCA : CA ≤ CAg := by rw [hCAg]; linarith
  -- the constant of the statement
  obtain ⟨C3, hC3⟩ : ∃ x : ℝ, x = |Cc0| + (2 * |Cn| * (KgL + KgR) + 2 * |Cm| + 2 * |Cn| * |Cm|) := ⟨_, rfl⟩
  have hC30 : 0 ≤ C3 := by rw [hC3]; positivity
  have hCn0 : 0 ≤ |Cn| := abs_nonneg _
  have hcLD : 0 < CL.c - CL.c' := by linarith [CL.consts_pos.2.1]
  refine ⟨C3, min (min h1n h1m) (min (min h0k (min 1 (1 / (2 * (|Cn| + 1))))) ((CL.c - CL.c') / 6)),
    lt_min (lt_min hh1n hh1m) (lt_min (lt_min hh0k (lt_min one_pos (div_pos one_pos (by positivity))))
      (div_pos hcLD (by norm_num))), ?_⟩
  intro p hp X hX N hN hstep ns hns Xs Um hE k hk n hn
  have hN1 : CL.N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : CR.N0 ≤ N := le_trans (le_max_right _ _) hN
  have hst : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L := step_mul_succ Fz N
  have hs1n : Fz.step N ≤ h1n := hstep.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hs1m : Fz.step N ≤ h1m := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hsk : Fz.step N ≤ h0k := hstep.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hs1 : Fz.step N ≤ 1 := hstep.trans ((min_le_right _ _).trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hsC : Fz.step N ≤ 1 / (2 * (|Cn| + 1)) :=
    hstep.trans ((min_le_right _ _).trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hsW : Fz.step N ≤ (CL.c - CL.c') / 6 := hstep.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hη : Fz.step N ^ m ≤ Fz.step N := pow_le_of_le_one hst.le hs1 (by omega)
  have hη0 : 0 ≤ Fz.step N ^ m := pow_nonneg hst.le _
  have hη1 : Fz.step N ^ m ≤ 1 := pow_le_one₀ hst.le hs1
  have hsn' : Fz.step N * (2 * (|Cn| + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hsC
  have hCnη : |Cn| * Fz.step N ^ m ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hη hCn0
    linarith
  -- the normaliser ratio and the standard normaliser
  have hr1 := hnorm p hp X hX N hN hs1n ns hns Xs Um hE k hk
  have hr1' : |glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns /
      bulkNorm CL CR p X N - 1| ≤ |Cn| * Fz.step N ^ m :=
    hr1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hη0)
  obtain ⟨hyPos, -, -, -, -⟩ := hκall p hp X hX N hN hsk
  have hN1pos : 0 < glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns := by
    have h2 : 0 < glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns /
        bulkNorm CL CR p X N := by
      have := (abs_le.mp hr1').1
      linarith
    exact (div_pos_iff_of_pos_right hyPos).mp h2
  -- the eigenvector comparison of `bulk_conj1`
  have heig := ((hκall p hp X hX N hN hsk).2.2.2.2 Xs Um hE k hk).2 n hn
  -- the window point ns and the fold
  have hnsF : CL.c' ≤ uNode (Fz.step N) ns ∧ uNode (Fz.step N) ns ≤ CL.c := by
    have h := hns
    unfold bulkWindow at h
    exact (Finset.mem_filter.mp h).2
  obtain ⟨hl_ns, hu_ns⟩ := hnsF
  -- the chart facts (envelope bounds on the rows)
  have hAL0 : ∀ j : ℤ, 0 ≤ j → j ≤ (CL.chain p X N).NR - 1 → |(CL.chain p X N).A j| ≤ CA := by
    intro j h0 h1
    rw [CL.A_bond p hp X hX N hN1 j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
    exact hCA p hp N j
  have hAR0 : ∀ j : ℤ, 0 ≤ j → j ≤ (CR.chain p X N).NR - 1 → |(CR.chain p X N).A j| ≤ CA := by
    intro j h0 h1
    rw [CR.A_bond p hp X hX N hN2 j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), bondA_mirror]
    exact hCA p hp N _
  have hAL : ∀ j : ℤ, 0 ≤ j → j ≤ (CL.chain p X N).NR - 1 → |(CL.chain p X N).A j| ≤ CAg :=
    fun j h0 h1 => (hAL0 j h0 h1).trans hCAgCA
  have hAR : ∀ j : ℤ, 0 ≤ j → j ≤ (CR.chain p X N).NR - 1 → |(CR.chain p X N).A j| ≤ CAg :=
    fun j h0 h1 => (hAR0 j h0 h1).trans hCAgCA
  have hhcL' : Fz.step N ≤ CL.c - CL.c' := by linarith [hsW, hcLD]
  have hhcR' : (mirrorFamily Fz).step N ≤ CR.c - CR.c' := by
    have hCRD : CR.c - CR.c' = CL.c - CL.c' := by rw [hcoup.1, hcoup.2]; ring
    show Fz.step N ≤ CR.c - CR.c'
    rw [hCRD]
    exact hhcL'
  obtain ⟨LA, LB, -, -, -⟩ := chart_side_facts CL p hp X hX N hN1 hhcL' KgL CEL CML CL.cs.cm CsL CAg hKgL0 hCEL0
    hCML0 CL.cs.cm_pos hCAg0 hKgCL hCEgCL hCMgCL le_rfl hCsgCL hAL
  obtain ⟨RA, RB, -, -, -⟩ := chart_side_facts CR p hp X hX N hN2 hhcR' KgR CER CMR CR.cs.cm CsR CAg hKgR0 hCER0
    hCMR0 CR.cs.cm_pos hCAg0 hKgCR hCEgCR hCMgCR le_rfl hCsgCR hAR
  obtain ⟨Csp, hCsp⟩ : ∃ x : ℝ, x = 2 * |Cn| * (KgL + KgR) + 2 * |Cm| + 2 * |Cn| * |Cm| := ⟨_, rfl⟩
  have hCsp0 : 0 ≤ Csp := by rw [hCsp]; positivity
  have hn0 : 0 ≤ n := by unfold rowsOf at hn; exact (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ (N : ℤ) := by unfold rowsOf at hn; exact (Finset.mem_Icc.mp hn).2
  have hMn0 : ∀ n ∈ bulkWindow CL N, 0 ≤ (CL.chain p X N).M n := by
    intro n hn
    have hn' := window_sub_rows CL p hp X hX N hN1 hst n hn
    have hcn : CL.c' ≤ uNode (Fz.step N) n := by
      have h := hn
      unfold bulkWindow at h
      exact (Finset.mem_filter.mp h).2.1
    exact le_trans (mul_nonneg hcM.le (Real.rpow_nonneg hst.le _)) (CL.M_osc p hp X hX N hN1 n hn' hcn).1
  have hu_mir : uNode (Fz.step N) ((N : ℤ) - n) = Fz.L - uNode (Fz.step N) n := uNode_mirror Fz.L (Fz.step N) N n hLs
  -- the splice-versus-standard vector on the row `n`
  have hcLD' : CL.c' < CL.c := CL.consts_pos.2.1
  have hsplice : |bulkVec CL CR p X N n - splicedVec (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N)
      (rowsOf N) ns n| ≤ Csp * Fz.step N ^ m * bulkEnv CL CR p X N n ∧ 0 ≤ bulkEnv CL CR p X N n := by
    by_cases hnsn : n ≤ ns
    · by_cases hcn : uNode (Fz.step N) n ≤ CL.c
      · -- case 1: both left
        have hnr := Finset.mem_Icc.mpr ⟨hn0, le_NR_of CL p hp X hX N hN1 hst n hcn⟩
        have hLA := LA n (Finset.mem_Icc.mp hnr).1 (Finset.mem_Icc.mp hnr).2
        have hLB0 := (LB n (Finset.mem_Icc.mp hnr).1 (Finset.mem_Icc.mp hnr).2).1
        have eV : bulkVec CL CR p X N n = CL.psiHatL p X N n / bulkNorm CL CR p X N := by
          unfold bulkVec glueVec; rw [if_pos hcn]; rfl
        have eS : splicedVec (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns n =
            CL.psiHatL p X N n / glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns := by
          unfold splicedVec; rw [if_pos hnsn]
        have eE : bulkEnv CL CR p X N n = CL.envL p X N n / bulkNorm CL CR p X N := by
          unfold bulkEnv; rw [if_pos hcn]
        rw [eV, eS, eE, abs_sub_comm]
        have hX0 : 0 ≤ CL.envL p X N n / bulkNorm CL CR p X N := div_nonneg hLB0 hyPos.le
        refine ⟨?_, hX0⟩
        have hd := div_pair_bound (CL.psiHatL p X N n) (bulkNorm CL CR p X N)
          (glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns)
          (|Cn| * Fz.step N ^ m) hyPos hN1pos hr1' hCnη
        calc _ ≤ 2 * (|Cn| * Fz.step N ^ m) * |CL.psiHatL p X N n| / bulkNorm CL CR p X N := hd
          _ ≤ 2 * (|Cn| * Fz.step N ^ m) * (KgL * CL.envL p X N n) / bulkNorm CL CR p X N :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLA (by positivity)) hyPos.le
          _ = (2 * |Cn| * KgL) * Fz.step N ^ m * (CL.envL p X N n / bulkNorm CL CR p X N) := by ring
          _ ≤ Csp * Fz.step N ^ m * (CL.envL p X N n / bulkNorm CL CR p X N) := by
              apply mul_le_mul_of_nonneg_right _ hX0
              apply mul_le_mul_of_nonneg_right _ hη0
              rw [hCsp]
              have h1 := mul_nonneg (abs_nonneg Cn) hKgR0.le
              have h2 := mul_nonneg (abs_nonneg Cn) (abs_nonneg Cm)
              have h3 := abs_nonneg Cm
              linarith
      · exfalso
        exact hcn ((uNode_le_of_le hst.le hnsn).trans hu_ns)
    · by_cases hcn : uNode (Fz.step N) n ≤ CL.c
      · -- case 3: the splice is right, the standard split is left (a window point)
        have hlow : CL.c' ≤ uNode (Fz.step N) n := hl_ns.trans (uNode_le_of_le hst.le (not_le.mp hnsn).le)
        have hnW : n ∈ bulkWindow CL N := by
          unfold bulkWindow
          exact Finset.mem_filter.mpr ⟨hn, hlow, hcn⟩
        have hnr := window_sub_rows CL p hp X hX N hN1 hst n hnW
        have hLA := LA n (Finset.mem_Icc.mp hnr).1 (Finset.mem_Icc.mp hnr).2
        have hLB0 := (LB n (Finset.mem_Icc.mp hnr).1 (Finset.mem_Icc.mp hnr).2).1
        have hWe : CL.envL p X N n = (CL.chain p X N).M n := by
          unfold BulkWeberChart.envL
          rw [CL.W_osc p hp X hX N hN1 n hnr hlow, one_mul]
        have hmt := hmatch p hp X hX N hN hs1m Xs Um hE k hk n hnW
        have hmt' : |CL.psiHatL p X N n - bulkKappa CL CR p X N * bulkSeqR CR p X N n| ≤
            |Cm| * Fz.step N ^ m * CL.envL p X N n := by
          rw [hWe]
          exact hmt.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hη0)
            (hMn0 n hnW))
        have eV : bulkVec CL CR p X N n = CL.psiHatL p X N n / bulkNorm CL CR p X N := by
          unfold bulkVec glueVec; rw [if_pos hcn]; rfl
        have eS : splicedVec (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns n =
            bulkKappa CL CR p X N * bulkSeqR CR p X N n /
              glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns := by
          unfold splicedVec; rw [if_neg hnsn]; rfl
        have eE : bulkEnv CL CR p X N n = CL.envL p X N n / bulkNorm CL CR p X N := by
          unfold bulkEnv; rw [if_pos hcn]
        rw [eV, eS, eE]
        have hX0 : 0 ≤ CL.envL p X N n / bulkNorm CL CR p X N := div_nonneg hLB0 hyPos.le
        refine ⟨?_, hX0⟩
        have hdec : CL.psiHatL p X N n / bulkNorm CL CR p X N -
            bulkKappa CL CR p X N * bulkSeqR CR p X N n / glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N)
              (bulkWindow CL N) (rowsOf N) ns =
            (CL.psiHatL p X N n - bulkKappa CL CR p X N * bulkSeqR CR p X N n) / bulkNorm CL CR p X N +
            (bulkKappa CL CR p X N * bulkSeqR CR p X N n / bulkNorm CL CR p X N -
              bulkKappa CL CR p X N * bulkSeqR CR p X N n /
                glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns) := by ring
        rw [hdec]
        have h1 : |(CL.psiHatL p X N n - bulkKappa CL CR p X N * bulkSeqR CR p X N n) / bulkNorm CL CR p X N| ≤
            |Cm| * Fz.step N ^ m * CL.envL p X N n / bulkNorm CL CR p X N := by
          rw [abs_div, abs_of_pos hyPos]
          exact div_le_div_of_nonneg_right hmt' hyPos.le
        have hκψ : |bulkKappa CL CR p X N * bulkSeqR CR p X N n| ≤ (KgL + |Cm|) * CL.envL p X N n := by
          have hA1 : |CL.psiHatL p X N n| ≤ KgL * CL.envL p X N n := hLA
          have e2 : CL.psiHatL p X N n - (CL.psiHatL p X N n - bulkKappa CL CR p X N * bulkSeqR CR p X N n) =
              bulkKappa CL CR p X N * bulkSeqR CR p X N n := by ring
          have hA2 := abs_sub (CL.psiHatL p X N n) (CL.psiHatL p X N n - bulkKappa CL CR p X N * bulkSeqR CR p X N n)
          rw [e2] at hA2
          have hη1' : |Cm| * Fz.step N ^ m * CL.envL p X N n ≤ |Cm| * CL.envL p X N n := by
            have hEn : 0 ≤ CL.envL p X N n := hLB0
            have := mul_le_mul_of_nonneg_left hη1 (abs_nonneg Cm)
            have := mul_le_mul_of_nonneg_right this hEn
            linarith
          have hsub : |CL.psiHatL p X N n - bulkKappa CL CR p X N * bulkSeqR CR p X N n| ≤
              |Cm| * CL.envL p X N n := hmt'.trans hη1'
          nlinarith [hA2, hA1, hsub]
        have h2 := div_pair_bound (bulkKappa CL CR p X N * bulkSeqR CR p X N n) (bulkNorm CL CR p X N)
          (glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns)
          (|Cn| * Fz.step N ^ m) hyPos hN1pos hr1' hCnη
        rw [abs_sub_comm] at h2
        have hX0' : 0 ≤ CL.envL p X N n / bulkNorm CL CR p X N := hX0
        calc _ ≤ |(CL.psiHatL p X N n - bulkKappa CL CR p X N * bulkSeqR CR p X N n) / bulkNorm CL CR p X N| +
              |bulkKappa CL CR p X N * bulkSeqR CR p X N n / bulkNorm CL CR p X N -
                bulkKappa CL CR p X N * bulkSeqR CR p X N n /
                  glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns| :=
              abs_add_le _ _
          _ ≤ |Cm| * Fz.step N ^ m * CL.envL p X N n / bulkNorm CL CR p X N +
              2 * (|Cn| * Fz.step N ^ m) * ((KgL + |Cm|) * CL.envL p X N n) / bulkNorm CL CR p X N :=
              add_le_add h1 (h2.trans (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hκψ (by positivity)) hyPos.le))
          _ = (|Cm| + 2 * |Cn| * (KgL + |Cm|)) * Fz.step N ^ m * (CL.envL p X N n / bulkNorm CL CR p X N) := by ring
          _ ≤ Csp * Fz.step N ^ m * (CL.envL p X N n / bulkNorm CL CR p X N) := by
              apply mul_le_mul_of_nonneg_right _ hX0'
              apply mul_le_mul_of_nonneg_right _ hη0
              rw [hCsp]
              have h1' := mul_nonneg (abs_nonneg Cn) hKgR0.le
              have h3 := abs_nonneg Cm
              have h4 := mul_nonneg (abs_nonneg Cn) (abs_nonneg Cm)
              nlinarith
      · -- case 4: the splice is right and the standard split is right (outside the window)
        have hcn_up : CL.c < uNode (Fz.step N) n := not_le.mp hcn
        have hjn0 : 0 ≤ (N : ℤ) - n := by omega
        have hjle : uNode (Fz.step N) ((N : ℤ) - n) ≤ CR.c := by
          rw [hu_mir, hcoup.1]
          linarith [hcLD', hcn_up]
        have hjR := le_NR_of CR p hp X hX N hN2 hst ((N : ℤ) - n) hjle
        have hjm := Finset.mem_Icc.mpr ⟨hjn0, hjR⟩
        have hRA := RA ((N : ℤ) - n) (Finset.mem_Icc.mp hjm).1 (Finset.mem_Icc.mp hjm).2
        have hRB0 := (RB ((N : ℤ) - n) (Finset.mem_Icc.mp hjm).1 (Finset.mem_Icc.mp hjm).2).1
        have eV : bulkVec CL CR p X N n = bulkKappa CL CR p X N * bulkSeqR CR p X N n / bulkNorm CL CR p X N := by
          unfold bulkVec glueVec; rw [if_neg hcn]; rfl
        have eS : splicedVec (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns n =
            bulkKappa CL CR p X N * bulkSeqR CR p X N n /
              glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns := by
          unfold splicedVec; rw [if_neg hnsn]; rfl
        have eE : bulkEnv CL CR p X N n = |bulkKappa CL CR p X N| * CR.envL p X N ((N : ℤ) - n) /
            bulkNorm CL CR p X N := by
          unfold bulkEnv; rw [if_neg hcn]
        rw [eV, eS, eE]
        have hX0 : 0 ≤ |bulkKappa CL CR p X N| * CR.envL p X N ((N : ℤ) - n) / bulkNorm CL CR p X N :=
          div_nonneg (mul_nonneg (abs_nonneg _) hRB0) hyPos.le
        refine ⟨?_, hX0⟩
        have h2 := div_pair_bound (bulkKappa CL CR p X N * bulkSeqR CR p X N n) (bulkNorm CL CR p X N)
          (glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns)
          (|Cn| * Fz.step N ^ m) hyPos hN1pos hr1' hCnη
        have h2' : |bulkKappa CL CR p X N * bulkSeqR CR p X N n / bulkNorm CL CR p X N -
            bulkKappa CL CR p X N * bulkSeqR CR p X N n /
              glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns| ≤
            2 * (|Cn| * Fz.step N ^ m) * |bulkKappa CL CR p X N * bulkSeqR CR p X N n| / bulkNorm CL CR p X N := by
          rw [abs_sub_comm]; exact h2
        have hκR : |bulkKappa CL CR p X N * bulkSeqR CR p X N n| ≤
            |bulkKappa CL CR p X N| * (KgR * CR.envL p X N ((N : ℤ) - n)) := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hRA : |CR.psiHatL p X N ((N : ℤ) - n)| ≤ _) (abs_nonneg _)
        calc _ ≤ 2 * (|Cn| * Fz.step N ^ m) * |bulkKappa CL CR p X N * bulkSeqR CR p X N n| / bulkNorm CL CR p X N :=
              h2'
          _ ≤ 2 * (|Cn| * Fz.step N ^ m) * (|bulkKappa CL CR p X N| * (KgR * CR.envL p X N ((N : ℤ) - n))) /
              bulkNorm CL CR p X N :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hκR (by positivity)) hyPos.le
          _ = (2 * |Cn| * KgR) * Fz.step N ^ m * (|bulkKappa CL CR p X N| * CR.envL p X N ((N : ℤ) - n) /
              bulkNorm CL CR p X N) := by ring
          _ ≤ Csp * Fz.step N ^ m * (|bulkKappa CL CR p X N| * CR.envL p X N ((N : ℤ) - n) /
              bulkNorm CL CR p X N) := by
              apply mul_le_mul_of_nonneg_right _ hX0
              apply mul_le_mul_of_nonneg_right _ hη0
              rw [hCsp]
              have h1' := mul_nonneg (abs_nonneg Cn) (abs_nonneg Cm)
              have h3 := mul_nonneg (abs_nonneg Cn) hKgL0.le
              have h4 := abs_nonneg Cm
              nlinarith
  -- the eigenvector comparison: the bulk part and the splice part
  have heig := ((hκall p hp X hX N hN hsk).2.2.2.2 Xs Um hE k hk).2 n hn
  have hB0 := hsplice.2
  have htri := abs_add_le (eigVec Um k n - bulkVec CL CR p X N n) (bulkVec CL CR p X N n -
    splicedVec (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns n)
  rw [show eigVec Um k n - bulkVec CL CR p X N n + (bulkVec CL CR p X N n -
    splicedVec (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns n) =
    eigVec Um k n - splicedVec (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns n by ring] at htri
  have hCc0 : Cc0 * Fz.step N ^ m * bulkEnv CL CR p X N n ≤ |Cc0| * Fz.step N ^ m * bulkEnv CL CR p X N n :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hη0) hB0
  calc _ ≤ _ := htri
    _ ≤ (Cc0 * Fz.step N ^ m * bulkEnv CL CR p X N n) + Csp * Fz.step N ^ m * bulkEnv CL CR p X N n :=
        add_le_add heig hsplice.1
    _ ≤ |Cc0| * Fz.step N ^ m * bulkEnv CL CR p X N n + Csp * Fz.step N ^ m * bulkEnv CL CR p X N n :=
        add_le_add hCc0 le_rfl
    _ = C3 * Fz.step N ^ m * bulkEnv CL CR p X N n := by rw [hC3, hCsp]; ring

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.div_pair_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.div_pair_bound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulk_vec_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulk_vec_clause

/-- **The bulk envelope is nonnegative on the rows** (from the nonnegativity of the chart envelopes `envL`, `envR` on their rows). -/
theorem bulkEnv_nonneg_rows {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V)
    (hcoup : CR.c = Fz.L - CL.c' ∧ CR.c' = Fz.L - CL.c) (p : Par × ℝ) (hp : p ∈ P) (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi)
    (N : ℕ) (hN1 : CL.N0 ≤ N) (hN2 : CR.N0 ≤ N) (hst : 0 < Fz.step N)
    (hLB : ∀ j : ℤ, 0 ≤ j → j ≤ (CL.chain p X N).NR → 0 ≤ CL.envL p X N j)
    (hRB : ∀ j : ℤ, 0 ≤ j → j ≤ (CR.chain p X N).NR → 0 ≤ CR.envL p X N j) (n : ℤ) (hn : n ∈ rowsOf N) :
    0 ≤ bulkEnv CL CR p X N n := by
  have hn0 : 0 ≤ n := by unfold rowsOf at hn; exact (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ (N : ℤ) := by unfold rowsOf at hn; exact (Finset.mem_Icc.mp hn).2
  have hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L := step_mul_succ Fz N
  by_cases hcn : uNode (Fz.step N) n ≤ CL.c
  · unfold bulkEnv
    rw [if_pos hcn]
    exact div_nonneg (hLB n hn0 (le_NR_of CL p hp X hX N hN1 hst n hcn)) (Real.sqrt_nonneg _)
  · unfold bulkEnv
    rw [if_neg hcn]
    have hcn_up : CL.c < uNode (Fz.step N) n := not_le.mp hcn
    have hjle : uNode (Fz.step N) ((N : ℤ) - n) ≤ CR.c := by
      rw [uNode_mirror Fz.L (Fz.step N) N n hLs, hcoup.1]
      linarith [CL.consts_pos.2.1]
    exact div_nonneg (mul_nonneg (abs_nonneg _) (hRB ((N : ℤ) - n) (by omega)
      (le_NR_of CR p hp X hX N hN2 hst ((N : ℤ) - n) hjle))) (Real.sqrt_nonneg _)

/-- The bulk chart's `M` is nonnegative on the window (from `M_osc`, with `cM > 0`). -/
theorem bulk_M_nonneg {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (p : Par × ℝ) (hp : p ∈ P) (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi)
    (N : ℕ) (hN1 : CL.N0 ≤ N) (hst : 0 < Fz.step N) (n : ℤ) (hn : n ∈ bulkWindow CL N) :
    0 ≤ (CL.chain p X N).M n := by
  have hcM : 0 < CL.cM := CL.consts_pos.2.2.2.2.2.1
  have hn' := window_sub_rows CL p hp X hX N hN1 hst n hn
  have hcn : CL.c' ≤ uNode (Fz.step N) n := by
    have h := hn
    unfold bulkWindow at h
    exact (Finset.mem_filter.mp h).2.1
  exact le_trans (mul_nonneg hcM.le (Real.rpow_nonneg hst.le _)) (CL.M_osc p hp X hX N hN1 n hn' hcn).1

/-- The chart envelope `envL = W * M` is nonnegative on its rows (from the chart's `W_pos`, `M_pos`). -/
theorem chart_envL_nonneg {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (p : Par × ℝ) (hp : p ∈ P)
    (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi) (N : ℕ) (hN : C.N0 ≤ N) (j : ℤ) (hj0 : 0 ≤ j) (hjN : j ≤ (C.chain p X N).NR) :
    0 ≤ C.envL p X N j := by
  have hW := (C.valid p hp X hX N hN).W_pos j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩)
  have hM := (C.valid p hp X hX N hN).M_pos j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩)
  unfold BulkWeberChart.envL
  exact (mul_pos hW hM).le

set_option maxHeartbeats 4000000 in
/-- **`PropThaSpliceBulk` for `eta(h) = h^m`** (prop:tha-splice (a), bulk), assembled from the three clauses: the normaliser
ratio (`bulk_norm_clause`), the window matching (`bulk_matching_eig`) and the eigenvector comparison (`bulk_vec_clause`), with
the one constant `C = |Cn| + |Cm| + |C3|`.  The hypotheses `1 <= m` and the mirror overlap `hcoup` are now part of the statement
`PropThaSpliceBulk` (finding F-B9, applied: same pattern as `PropThaW`), so the theorem has no further premise. -/
theorem propThaSpliceBulk_proved {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V) :
    PropThaSpliceBulk CL CR (fun h => h ^ m) := by
  unfold PropThaSpliceBulk
  intro hm hcoup r hr
  obtain ⟨Cn, h1n, hh1n, hnorm⟩ := bulk_norm_clause CL CR hm hcoup r hr
  obtain ⟨Cm, h1m, hh1m, hmatch⟩ := bulk_matching_eig CL CR hm hcoup r hr
  obtain ⟨C3, h1v, hh1v, hvec⟩ := bulk_vec_clause CL CR hm hcoup r hr
  obtain ⟨C, hCdef⟩ : ∃ x : ℝ, x = |Cn| + |Cm| + |C3| := ⟨_, rfl⟩
  have hCn : Cn ≤ C := by rw [hCdef]; linarith [le_abs_self Cn, abs_nonneg Cm, abs_nonneg C3]
  have hCm : Cm ≤ C := by rw [hCdef]; linarith [le_abs_self Cm, abs_nonneg Cn, abs_nonneg C3]
  have hC3 : C3 ≤ C := by rw [hCdef]; linarith [le_abs_self C3, abs_nonneg Cn, abs_nonneg Cm]
  refine ⟨C, min (min h1n h1m) h1v, lt_min (lt_min hh1n hh1m) hh1v, ?_⟩
  intro p hp X hX N hN hstep ns hns Xs Um hEig k hk
  have hst : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hN1 : CL.N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : CR.N0 ≤ N := le_trans (le_max_right _ _) hN
  have hs1n : Fz.step N ≤ h1n := hstep.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hs1m : Fz.step N ≤ h1m := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hs1v : Fz.step N ≤ h1v := hstep.trans (min_le_right _ _)
  have hη0 : 0 ≤ Fz.step N ^ m := pow_nonneg hst.le _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (hnorm p hp X hX N hN hs1n ns hns Xs Um hEig k hk).trans (mul_le_mul_of_nonneg_right hCn hη0)
  · intro n hn
    have hmM := bulk_M_nonneg CL p hp X hX N hN1 hst n hn
    exact (hmatch p hp X hX N hN hs1m Xs Um hEig k hk n hn).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCm hη0) hmM)
  · intro n hn
    have hE := bulkEnv_nonneg_rows CL CR hcoup p hp X hX N hN1 hN2 hst
      (fun j hj0 hjN => chart_envL_nonneg CL p hp X hX N hN1 j hj0 hjN)
      (fun j hj0 hjN => chart_envL_nonneg CR p hp X hX N hN2 j hj0 hjN) n hn
    exact (hvec p hp X hX N hN hs1v ns hns Xs Um hEig k hk n hn).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 hη0) hE)

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulkEnv_nonneg_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulkEnv_nonneg_rows

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulk_M_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulk_M_nonneg

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.chart_envL_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.chart_envL_nonneg

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.propThaSpliceBulk_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.propThaSpliceBulk_proved

end FormalResearch.JacobiEigenvectors.TheoremB
