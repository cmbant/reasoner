module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.SpliceBulk
public import FormalResearch.JacobiEigenvectors.TheoremA.Geometry

/-!
# Paper J, Theorem B, L3.2 (bulk columns): `prop:tha-splice` (c), the bulk columns of `PropThaSpliceTwoOrders`

Source: Paper J `thmB.tex` `prop:tha-splice` (c) and `app_thmB.tex`, proof of `prop:tha-splice` and of `prop:thb-inputs` (I1): the bulk columns of `hat G^{[r]}` are `hat Psi^{(n_nu)}` times
`hat N(n_nu)/hat N`, the scalars being those of the standard splice and fixed when the splice moves.

## Proved here

* `bulk_env_sq_sum`: `sum_{n=0}^N bulkEnv_n^2 <= C` (the bulk `sum V_n^2/hat N^2 <= C`), from the chart envelope sums (`chart_side_facts`), `hat N >= c h^{-1/4}` and `|hat kappa| <= C` of `PropThaW (2)`.
* `bulk_col_clause`: for a pair of bulk charts with `StdAssump Fz P (m/2) r`, `1 <= m` and the mirror overlap, the column `bulkColAt .. n_s` of `hat G^{[m]}` (standard normaliser and `hat kappa`, splice row `n_s`
  **any row of the window**) satisfies `||bulkColAt - Psi_k||_2 <= C h^m` at every eigenvalue `X = X_k` in the block, uniformly in `n_s`.  Route: the column differs from `bulkVec` only on the rows between `n_s` and the
  standard split, where `|psi^L - hat kappa psi^R| <= Cm h^m M = Cm h^m envL` (`bulk_matching_eig`, `W = 1` on the window), and `|Psi - bulkVec| <= Cc h^m bulkEnv` (`bulk_conj1`).  The normaliser ratio
  `hat N(n_s)/hat N` of `prop:tha-splice` (a) is **not** needed for the matrix columns (they use the standard normaliser), so bridge item (b) (`glueVecAt` versus `splicedVec`) is not used.
* Bridge (a) `StdAssump` of the frozen family: `EK_mono_set`, `EK_mono_idx` (lowering the index of `(E_K)` on a compact set), `stdAssump_frozen_all` (from `frozenStandard`, `TheoremA/Geometry.lean`:
  `StdAssump (frozenFamily F Kidx) (paramSet K t') Kd r` for all `0 < t' <= t1`, `Kd <= Kidx`), and `BulkWeberChart.restrict` (restriction of a chart to a smaller parameter set; **it lists every `P`-dependent field of `BulkWeberChart`,
  a new such field must be added there**): this is the `ChartInputs.restrict` step of finding F-t0, for bulk charts.
* Bridge (d): `(frozenFamily F Kidx).jacobiMat (mu, h) N = F.jacobiMat mu N` (`frozenFamily_jacobiMat_at_step`) transports the eigen-system.
* `nearestRow_mem_window`: for `c' < s < c`, `nearestRow h s` lies in the window `{c' <= u_n <= c}` once `h <= min (2(s-c'), 2(c-s), c')`.
* `bulk_block_columns`, `compMatrix_bulk_col`: the above for one block and, uniformly over the finitely many blocks, for every column `j` of `compMatrix CI spl` whose energy lies in a block (`compColumn` unfolds to `bulkColAt` of the chosen block).
* `twoOrders_bulk_columns`: both conjuncts of `PropThaSpliceTwoOrders` for the bulk columns, with `etaR` (`h^m`, and `h^{m+1} <= etaR m (m+1) h` for `h <= e^{-1}`), from `CP : ChartPair` with `SplicesInWindow`.

## Differences from the paper

* The splices are the fixed positions `spl nu` in the **open** overlap `(c', c)` (`ChartPair.SplicesInWindow`, finding F-B10), because the Lean splice row is `nearestRow h (spl nu)`.
* The constants are uniform over the blocks (finitely many) by summing the block constants; `N >= N0` is encoded in `h <= L/(N0 + 1)`, `h <= t1` (the `t0` of `frozenStandard`) in `h0`.
* The order-`(m+1)` bound is the sharper `h^{m+1}` (no logarithm in the bulk, as in the paper: "in the bulk nothing depends on `q`").

## Not formalised (the soft columns of `PropThaSpliceTwoOrders`)

The conjunct for the columns outside all blocks (`X_j` in the soft windows) needs, **from the soft half (agents S, T)**: (i) `PropThaSpliceSoft` proved (it also gives `nearestRow u_c in softWindow`) for the upper edge, for
`CI.softUpL/softUpR` and for `negFamily (frozenFamily F Kidx)` at `-X` (lower edge), at `m` and `m+1` with the common shift `q`, with `StdAssump` for the soft families (bridge (a) for `negFamily`, `mirrorFamily`; `q/2 = Kidx`, and the
`log(1/h)` of `prop:tha-W2 (4)` for even `m` at order `m+1`); (ii) `sum_n softEnv_n^2 <= C` (this is the second clause of `PropThaW2 (2)`); (iii) the sign factor `(-1)^n` and the identification of the eigenvector of
`negFamily (frozenFamily F Kidx)` at `-X_k` with `D_- Psi_k` (`negFamily_JacSol`, a lemma not yet in the tree); (iv) the soft analogue of `bulk_col_clause`: `softColAt` has the standard soft normaliser and `hat kappa`, so it differs
from `softVec` only between the fold row and the standard split `Z <= 0`, by the matching bound of `PropThaSpliceSoft` (second clause).  The final `propThaSpliceTwoOrders` is the combination of `twoOrders_bulk_columns` and that soft half
(a column is bulk or not: `compColumn` splits on `exists nu, lo nu <= X <= hi nu`, then `Jhi < X`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA

open scoped Classical

set_option maxHeartbeats 4000000 in
/-- **The envelope is bounded in `l^2`**: `sum_{n=0}^{N} bulkEnv_n^2 <= C`, uniformly in `p`, `X`, `N` (small `h`).  This is `sum V_n^2/hat N^2 <= C` of eq:tha-G14 for the bulk. -/
theorem bulk_env_sq_sum {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V)
    (hm : 1 ≤ m) (hcoup : CR.c = Fz.L - CL.c' ∧ CR.c' = Fz.L - CL.c) (r : ℕ) (hr : StdAssump Fz P (m / 2) r) :
    ∃ CS h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∑ n ∈ rowsOf N, bulkEnv CL CR p X N n ^ 2 ≤ CS := by
  obtain ⟨Cc0, h0k, cN, CN, cκ, Cκ, hh0k, hcN, hcκ, hκall⟩ := bulk_conj1 CL CR hm hcoup r hr
  have hr' := hr
  obtain ⟨hPc, hEK, -⟩ := hr'
  obtain ⟨CA, hCA0, hCA⟩ := bondA_bound_of_EK Fz P (m / 2) r hPc hEK
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
  have hCML0 : 0 < CML := by rw [hCML]; linarith [CL.consts_pos.2.2.2.2.2.2.1, CL.consts_pos.2.2.2.2.2.1]
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
  have hcLD : 0 < CL.c - CL.c' := by linarith [CL.consts_pos.2.1]
  have hcRD : CR.c - CR.c' = CL.c - CL.c' := by rw [hcoup.1, hcoup.2]; ring
  refine ⟨(CEL ^ 2 * (CsL + CML ^ 2) + Cκ ^ 2 * (CER ^ 2 * (CsR + CMR ^ 2))) / cN ^ 2,
    min (min h0k 1) (CL.c - CL.c'), lt_min (lt_min hh0k one_pos) hcLD, ?_⟩
  intro p hp X hX N hN hstep
  have hN1 : CL.N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : CR.N0 ≤ N := le_trans (le_max_right _ _) hN
  have hst : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L := step_mul_succ Fz N
  have hsk : Fz.step N ≤ h0k := hstep.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hs1 : Fz.step N ≤ 1 := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhcL' : Fz.step N ≤ CL.c - CL.c' := hstep.trans (min_le_right _ _)
  have hhcR' : (mirrorFamily Fz).step N ≤ CR.c - CR.c' := by
    show Fz.step N ≤ CR.c - CR.c'
    rw [hcRD]
    exact hhcL'
  obtain ⟨hnnpos, hnnlo, -, hκ, -⟩ := hκall p hp X hX N hN hsk
  have hAL : ∀ j : ℤ, 0 ≤ j → j ≤ (CL.chain p X N).NR - 1 → |(CL.chain p X N).A j| ≤ CAg := by
    intro j h0 h1
    rw [CL.A_bond p hp X hX N hN1 j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
    exact (hCA p hp N j).trans (by rw [hCAg]; linarith)
  have hAR : ∀ j : ℤ, 0 ≤ j → j ≤ (CR.chain p X N).NR - 1 → |(CR.chain p X N).A j| ≤ CAg := by
    intro j h0 h1
    rw [CR.A_bond p hp X hX N hN2 j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), bondA_mirror]
    exact (hCA p hp N _).trans (by rw [hCAg]; linarith)
  obtain ⟨-, -, LS, -, -⟩ := chart_side_facts CL p hp X hX N hN1 hhcL' KgL CEL CML CL.cs.cm CsL CAg hKgL0 hCEL0
    hCML0 CL.cs.cm_pos hCAg0 hKgCL hCEgCL hCMgCL le_rfl hCsgCL hAL
  obtain ⟨-, -, RS, -, -⟩ := chart_side_facts CR p hp X hX N hN2 hhcR' KgR CER CMR CR.cs.cm CsR CAg hKgR0 hCER0
    hCMR0 CR.cs.cm_pos hCAg0 hKgCR hCEgCR hCMgCR le_rfl hCsgCR hAR
  have hLS' := env_sum_inv _ (CEL ^ 2) CsL CML (Fz.step N) LS (sq_nonneg _) hCML0.le hst hs1
  have hRS' := env_sum_inv _ (CER ^ 2) CsR CMR (Fz.step N) RS (sq_nonneg _) hCMR0.le hst hs1
  set nn := bulkNorm CL CR p X N with hnn
  set κ := bulkKappa CL CR p X N with hκdef
  have hsq : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hst
  -- the row sum splits into the left and the right part
  have hdecomp : ∑ n ∈ rowsOf N, bulkEnv CL CR p X N n ^ 2 =
      ((∑ n ∈ (rowsOf N).filter (fun n => uNode (Fz.step N) n ≤ CL.c), CL.envL p X N n ^ 2) +
        (∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode (Fz.step N) n ≤ CL.c),
          κ ^ 2 * CR.envL p X N ((N : ℤ) - n) ^ 2)) / nn ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (rowsOf N) (fun n => uNode (Fz.step N) n ≤ CL.c), add_div,
      Finset.sum_div, Finset.sum_div]
    congr 1
    · refine Finset.sum_congr rfl fun n hn => ?_
      have h := (Finset.mem_filter.mp hn).2
      simp only [bulkEnv, if_pos h, div_pow] <;> rfl
    · refine Finset.sum_congr rfl fun n hn => ?_
      have h := (Finset.mem_filter.mp hn).2
      simp only [bulkEnv, if_neg h, div_pow, mul_pow, sq_abs] <;> rfl
  have hSL : ∑ n ∈ (rowsOf N).filter (fun n => uNode (Fz.step N) n ≤ CL.c), CL.envL p X N n ^ 2 ≤
      CEL ^ 2 * (CsL + CML ^ 2) / Real.sqrt (Fz.step N) := by
    refine le_trans ?_ hLS'
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun j _ _ => sq_nonneg _)
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.mp hn
    have hn3 : 0 ≤ n := (Finset.mem_Icc.mp hn1).1
    exact Finset.mem_Icc.mpr ⟨hn3, le_NR_of CL p hp X hX N hN1 hst n hn2⟩
  have hSR : ∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode (Fz.step N) n ≤ CL.c),
      κ ^ 2 * CR.envL p X N ((N : ℤ) - n) ^ 2 ≤ Cκ ^ 2 * (CER ^ 2 * (CsR + CMR ^ 2) / Real.sqrt (Fz.step N)) := by
    rw [← Finset.mul_sum]
    have hrefl : ∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode (Fz.step N) n ≤ CL.c), CR.envL p X N ((N : ℤ) - n) ^ 2 ≤
        ∑ k ∈ Finset.Icc (0 : ℤ) (CR.chain p X N).NR, CR.envL p X N k ^ 2 := by
      refine sum_reflect_le N _ _ (fun k => CR.envL p X N k ^ 2) (fun k => sq_nonneg _) ?_ ?_
      · intro n hn
        obtain ⟨hn1, hn2⟩ := Finset.mem_filter.mp hn
        have hnN : n ≤ (N : ℤ) := (Finset.mem_Icc.mp hn1).2
        have hmir : uNode (Fz.step N) ((N : ℤ) - n) = Fz.L - uNode (Fz.step N) n := uNode_mirror Fz.L (Fz.step N) N n hLs
        have hk : uNode ((mirrorFamily Fz).step N) ((N : ℤ) - n) ≤ CR.c := by
          show uNode (Fz.step N) ((N : ℤ) - n) ≤ CR.c
          rw [hmir]
          linarith [hcoup.1, hcoup.2, not_le.mp hn2, CR.consts_pos.2.1]
        exact Finset.mem_Icc.mpr ⟨by omega, le_NR_of CR p hp X hX N hN2 hst _ hk⟩
      · intro a _ b _ hab
        simp only at hab
        omega
    have h2 := hrefl.trans (hRS'.trans (le_refl _))
    have hκ2 : κ ^ 2 ≤ Cκ ^ 2 := by
      rw [← sq_abs κ]
      exact pow_le_pow_left₀ (abs_nonneg _) hκ 2
    calc κ ^ 2 * ∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode (Fz.step N) n ≤ CL.c), CR.envL p X N ((N : ℤ) - n) ^ 2
        ≤ Cκ ^ 2 * (CER ^ 2 * (CsR + CMR ^ 2) / Real.sqrt (Fz.step N)) := by
          apply mul_le_mul hκ2 h2 (Finset.sum_nonneg fun n _ => sq_nonneg _) (sq_nonneg _)
      _ = _ := rfl
  have hnn2 : cN ^ 2 / Real.sqrt (Fz.step N) ≤ nn ^ 2 := by
    have h1 : cN * Fz.step N ^ (-(1 : ℝ) / 4) ≤ nn := hnnlo
    have h0 : 0 ≤ cN * Fz.step N ^ (-(1 : ℝ) / 4) := by positivity
    have h2 := pow_le_pow_left₀ h0 h1 2
    have e : (cN * Fz.step N ^ (-(1 : ℝ) / 4)) ^ 2 = cN ^ 2 / Real.sqrt (Fz.step N) := by
      rw [mul_pow, rpow_quarter_neg_sq _ hst]
      field_simp
    rwa [e] at h2
  rw [hdecomp]
  have hnum : (∑ n ∈ (rowsOf N).filter (fun n => uNode (Fz.step N) n ≤ CL.c), CL.envL p X N n ^ 2) +
      (∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode (Fz.step N) n ≤ CL.c), κ ^ 2 * CR.envL p X N ((N : ℤ) - n) ^ 2) ≤
      (CEL ^ 2 * (CsL + CML ^ 2) + Cκ ^ 2 * (CER ^ 2 * (CsR + CMR ^ 2))) / Real.sqrt (Fz.step N) := by
    have e : (CEL ^ 2 * (CsL + CML ^ 2) + Cκ ^ 2 * (CER ^ 2 * (CsR + CMR ^ 2))) / Real.sqrt (Fz.step N) =
        CEL ^ 2 * (CsL + CML ^ 2) / Real.sqrt (Fz.step N) +
          Cκ ^ 2 * (CER ^ 2 * (CsR + CMR ^ 2) / Real.sqrt (Fz.step N)) := by ring
    rw [e]
    linarith
  have hnum0 : 0 ≤ (CEL ^ 2 * (CsL + CML ^ 2) + Cκ ^ 2 * (CER ^ 2 * (CsR + CMR ^ 2))) / Real.sqrt (Fz.step N) := by positivity
  have hD : 0 < cN ^ 2 / Real.sqrt (Fz.step N) := by positivity
  calc _ ≤ ((CEL ^ 2 * (CsL + CML ^ 2) + Cκ ^ 2 * (CER ^ 2 * (CsR + CMR ^ 2))) / Real.sqrt (Fz.step N)) / nn ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ ≤ ((CEL ^ 2 * (CsL + CML ^ 2) + Cκ ^ 2 * (CER ^ 2 * (CsR + CMR ^ 2))) / Real.sqrt (Fz.step N)) /
          (cN ^ 2 / Real.sqrt (Fz.step N)) := div_le_div_of_nonneg_left hnum0 hD hnn2
    _ = _ := by field_simp

set_option maxHeartbeats 4000000 in
/-- **The bulk column of `hat G^{[m]}`, for any splice row in the window, is within `C h^m` of the eigenvector in `l^2`** (`prop:tha-splice` (c) for one bulk block and one order).
`bulkColAt .. ns` is the column of `compMatrix` for a bulk energy with the splice row `ns` (standard normaliser and standard `hat kappa`, eq:thb-bulkcol). -/
theorem bulk_col_clause {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V)
    (hm : 1 ≤ m) (hcoup : CR.c = Fz.L - CL.c' ∧ CR.c' = Fz.L - CL.c) (r : ℕ) (hr : StdAssump Fz P (m / 2) r) :
    ∃ C h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ ns ∈ bulkWindow CL N, ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        IsEigenSystem (Fz.jacobiMat p N) Xs Um → ∀ k : Fin (N + 1), Xs k = X →
          FormalResearch.JB.jbL2 Finset.univ (fun i : Fin (N + 1) => bulkColAt CL CR p X N ns ((i : ℕ) : ℤ) - Um i k) ≤
            C * Fz.step N ^ m := by
  obtain ⟨Cc0, h0k, cN, CN, cκ, Cκ, hh0k, hcN, hcκ, hκall⟩ := bulk_conj1 CL CR hm hcoup r hr
  obtain ⟨Cm, h1m, hh1m, hmatch⟩ := bulk_matching_eig CL CR hm hcoup r hr
  obtain ⟨CS, h1S, hh1S, hSum⟩ := bulk_env_sq_sum CL CR hm hcoup r hr
  refine ⟨(|Cc0| + |Cm|) * Real.sqrt CS, min (min h0k h1m) h1S, lt_min (lt_min hh0k hh1m) hh1S, ?_⟩
  intro p hp X hX N hN hstep ns hns Xs Um hE k hk
  have hN1 : CL.N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : CR.N0 ≤ N := le_trans (le_max_right _ _) hN
  have hst : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hsk : Fz.step N ≤ h0k := hstep.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hsm : Fz.step N ≤ h1m := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hsS : Fz.step N ≤ h1S := hstep.trans (min_le_right _ _)
  have hη0 : 0 ≤ Fz.step N ^ m := pow_nonneg hst.le _
  obtain ⟨hnnpos, -, -, -, hrest⟩ := hκall p hp X hX N hN hsk
  have heig := (hrest Xs Um hE k hk).2
  have hnsF : CL.c' ≤ uNode (Fz.step N) ns ∧ uNode (Fz.step N) ns ≤ CL.c := by
    have h := hns
    unfold bulkWindow at h
    exact (Finset.mem_filter.mp h).2
  obtain ⟨hl_ns, hu_ns⟩ := hnsF
  have hMn0 : ∀ n ∈ bulkWindow CL N, 0 ≤ (CL.chain p X N).M n := by
    intro n hn
    have hn' := window_sub_rows CL p hp X hX N hN1 hst n hn
    have hcn : CL.c' ≤ uNode (Fz.step N) n := by
      have h := hn
      unfold bulkWindow at h
      exact (Finset.mem_filter.mp h).2.1
    have hcM : 0 < CL.cM := CL.consts_pos.2.2.2.2.2.1
    exact le_trans (mul_nonneg hcM.le (Real.rpow_nonneg hst.le _)) (CL.M_osc p hp X hX N hN1 n hn' hcn).1
  -- the row bound
  have hrow : ∀ n ∈ rowsOf N, |bulkColAt CL CR p X N ns n - eigVec Um k n| ≤
      (|Cc0| + |Cm|) * Fz.step N ^ m * bulkEnv CL CR p X N n := by
    intro n hn
    have hEn := bulkEnv_nonneg_rows CL CR hcoup p hp X hX N hN1 hN2 hst
      (fun j hj0 hjN => chart_envL_nonneg CL p hp X hX N hN1 j hj0 hjN)
      (fun j hj0 hjN => chart_envL_nonneg CR p hp X hX N hN2 j hj0 hjN) n hn
    have hev := heig n hn
    have hcc : Cc0 * Fz.step N ^ m * bulkEnv CL CR p X N n ≤ |Cc0| * Fz.step N ^ m * bulkEnv CL CR p X N n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hη0) hEn
    have hdiff : |bulkColAt CL CR p X N ns n - bulkVec CL CR p X N n| ≤ |Cm| * Fz.step N ^ m * bulkEnv CL CR p X N n := by
      by_cases hnsn : n ≤ ns
      · have hcn : uNode (Fz.step N) n ≤ CL.c := (uNode_le_of_le hst.le hnsn).trans hu_ns
        have e : bulkColAt CL CR p X N ns n = bulkVec CL CR p X N n := by
          unfold bulkColAt glueVecAt bulkVec glueVec
          rw [if_pos hnsn, if_pos hcn]
        rw [e, sub_self, abs_zero]
        positivity
      · by_cases hcn : uNode (Fz.step N) n ≤ CL.c
        · have hlow : CL.c' ≤ uNode (Fz.step N) n := hl_ns.trans (uNode_le_of_le hst.le (not_le.mp hnsn).le)
          have hnW : n ∈ bulkWindow CL N := by
            unfold bulkWindow
            exact Finset.mem_filter.mpr ⟨hn, hlow, hcn⟩
          have hnr := window_sub_rows CL p hp X hX N hN1 hst n hnW
          have hWe : CL.envL p X N n = (CL.chain p X N).M n := by
            unfold BulkWeberChart.envL
            rw [CL.W_osc p hp X hX N hN1 n hnr hlow, one_mul]
          have hmt := hmatch p hp X hX N hN hsm Xs Um hE k hk n hnW
          have hmt' : |CL.psiHatL p X N n - bulkKappa CL CR p X N * bulkSeqR CR p X N n| ≤
              |Cm| * Fz.step N ^ m * CL.envL p X N n := by
            rw [hWe]
            exact hmt.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hη0) (hMn0 n hnW))
          have e : bulkColAt CL CR p X N ns n - bulkVec CL CR p X N n =
              -((CL.psiHatL p X N n - bulkKappa CL CR p X N * bulkSeqR CR p X N n) / bulkNorm CL CR p X N) := by
            unfold bulkColAt glueVecAt bulkVec glueVec
            rw [if_neg hnsn, if_pos hcn]
            show _ = -((CL.psiHatL p X N n - bulkKappa CL CR p X N * bulkSeqR CR p X N n) / bulkNorm CL CR p X N)
            unfold bulkKappa bulkNorm
            ring
          have eE : bulkEnv CL CR p X N n = CL.envL p X N n / bulkNorm CL CR p X N := by
            unfold bulkEnv; rw [if_pos hcn]
          rw [e, abs_neg, abs_div, abs_of_pos hnnpos, eE, ← mul_div_assoc]
          exact div_le_div_of_nonneg_right hmt' hnnpos.le
        · have e : bulkColAt CL CR p X N ns n = bulkVec CL CR p X N n := by
            unfold bulkColAt glueVecAt bulkVec glueVec
            rw [if_neg hnsn, if_neg hcn]
          rw [e, sub_self, abs_zero]
          positivity
    calc |bulkColAt CL CR p X N ns n - eigVec Um k n|
        ≤ |bulkColAt CL CR p X N ns n - bulkVec CL CR p X N n| + |eigVec Um k n - bulkVec CL CR p X N n| := by
          rw [abs_sub_comm (eigVec Um k n)]
          exact abs_sub_le _ _ _
      _ ≤ |Cm| * Fz.step N ^ m * bulkEnv CL CR p X N n + Cc0 * Fz.step N ^ m * bulkEnv CL CR p X N n := add_le_add hdiff hev
      _ ≤ |Cm| * Fz.step N ^ m * bulkEnv CL CR p X N n + |Cc0| * Fz.step N ^ m * bulkEnv CL CR p X N n := by linarith
      _ = (|Cc0| + |Cm|) * Fz.step N ^ m * bulkEnv CL CR p X N n := by ring
  -- from rows to the `l^2` norm over `Fin (N+1)`
  unfold FormalResearch.JB.jbL2
  have hconv : ∑ i : Fin (N + 1), (bulkColAt CL CR p X N ns ((i : ℕ) : ℤ) - Um i k) ^ 2 =
      ∑ n ∈ rowsOf N, (bulkColAt CL CR p X N ns n - eigVec Um k n) ^ 2 := by
    rw [sum_rowsOf_eq_fin N (fun n => (bulkColAt CL CR p X N ns n - eigVec Um k n) ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hev : eigVec Um k (i.val : ℤ) = Um i k := extV_fin (fun j => Um j k) i
    rw [hev]
  rw [hconv]
  have hsq : ∑ n ∈ rowsOf N, (bulkColAt CL CR p X N ns n - eigVec Um k n) ^ 2 ≤
      ((|Cc0| + |Cm|) * Fz.step N ^ m) ^ 2 * CS := by
    calc _ ≤ ∑ n ∈ rowsOf N, ((|Cc0| + |Cm|) * Fz.step N ^ m * bulkEnv CL CR p X N n) ^ 2 := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hrow n hn) 2
      _ = ((|Cc0| + |Cm|) * Fz.step N ^ m) ^ 2 * ∑ n ∈ rowsOf N, bulkEnv CL CR p X N n ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
      _ ≤ ((|Cc0| + |Cm|) * Fz.step N ^ m) ^ 2 * CS :=
          mul_le_mul_of_nonneg_left (hSum p hp X hX N hN hsS) (sq_nonneg _)
  calc Real.sqrt _ ≤ Real.sqrt (((|Cc0| + |Cm|) * Fz.step N ^ m) ^ 2 * CS) := Real.sqrt_le_sqrt hsq
    _ = (|Cc0| + |Cm|) * Fz.step N ^ m * Real.sqrt CS := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    _ = (|Cc0| + |Cm|) * Real.sqrt CS * Fz.step N ^ m := by ring

/-! ### Bridge (a): `StdAssump` of the frozen family at the orders `m` and `m + 1` -/

/-- `(E_K)` on a smaller parameter set. -/
theorem EK_mono_set {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P P' : Set Par} {Kd r : ℕ}
    (h : EK F P Kd r) (hsub : P' ⊆ P) : EK F P' Kd r := by
  refine EK.mk h.budget ?_ ?_
  · intro j hj
    obtain ⟨⟨g1, g2⟩, ⟨b1, b2⟩⟩ := h.reg j hj
    exact ⟨⟨fun μ hμ => g1 μ (hsub hμ), fun i hi => (g2 i hi).mono (Set.prod_mono hsub subset_rfl)⟩,
      ⟨fun μ hμ => b1 μ (hsub hμ), fun i hi => (b2 i hi).mono (Set.prod_mono hsub subset_rfl)⟩⟩
  · obtain ⟨C, hC⟩ := h.rem
    exact ⟨C, fun μ hμ N s hs => hC μ (hsub hμ) N s hs⟩

/-- `StdAssump` on a smaller compact parameter set. -/
theorem stdAssump_mono_set {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P P' : Set Par} {Kd r : ℕ}
    (h : StdAssump F P Kd r) (hsub : P' ⊆ P) (hP' : IsCompact P') : StdAssump F P' Kd r := by
  obtain ⟨-, hE, ⟨g, hg⟩⟩ := h
  exact ⟨hP', EK_mono_set hE hsub, ⟨g, fun μ hμ => hg μ (hsub hμ)⟩⟩

/-- `h <= L` for the step `h = L/(N+1)`. -/
theorem step_le_L {Par : Type*} (F : SymbolFamily Par) (N : ℕ) : F.step N ≤ F.L := by
  unfold SymbolFamily.step FormalResearch.JB.stepSize
  exact div_le_self F.L_pos.le (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])

/-- **Lowering the index of `(E_K)`**: `(E_Kd)` with the same regularity `r` follows from `(E_K)` for `Kd <= K` on a compact `P`
(the extra even jets are bounded, and `h^{2j} <= C h^{2 Kd + 2}` for `2 Kd + 2 <= 2j <= 2K` since `h <= L`). -/
theorem EK_mono_idx {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} (hP : IsCompact P)
    {Kd Kd' r : ℕ} (h : EK F P Kd r) (hle : Kd' ≤ Kd) : EK F P Kd' r := by
  -- bounded jets
  have hbd : ∀ j : ℕ, ∃ Cj : ℝ, j ≤ Kd → ∀ μ ∈ P, ∀ s ∈ Set.Icc 0 F.L, |F.G (2 * j) μ s| ≤ Cj ∧ |F.B (2 * j) μ s| ≤ Cj := by
    intro j
    by_cases hj : j ≤ Kd
    · obtain ⟨⟨g1, g2⟩, ⟨b1, b2⟩⟩ := h.reg j hj
      have hcG := g2 0 (Nat.zero_le _)
      have hcB := b2 0 (Nat.zero_le _)
      simp only [iteratedDerivWithin_zero] at hcG hcB
      obtain ⟨CG, hCG⟩ := (hP.prod isCompact_Icc).exists_bound_of_continuousOn hcG
      obtain ⟨CB, hCB⟩ := (hP.prod isCompact_Icc).exists_bound_of_continuousOn hcB
      refine ⟨max CG CB, fun _ μ hμ s hs => ⟨?_, ?_⟩⟩
      · exact (hCG (μ, s) ⟨hμ, hs⟩).trans (le_max_left _ _)
      · exact (hCB (μ, s) ⟨hμ, hs⟩).trans (le_max_right _ _)
    · exact ⟨0, fun h' => absurd h' hj⟩
  choose Cj hCj using hbd
  obtain ⟨C, hC⟩ := h.rem
  obtain ⟨Λ, hΛ⟩ : ∃ x : ℝ, x = max 1 F.L := ⟨_, rfl⟩
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; exact le_max_left _ _
  have hΛL : F.L ≤ Λ := by rw [hΛ]; exact le_max_right _ _
  obtain ⟨CJ, hCJ⟩ : ∃ x : ℝ, x = ∑ j ∈ Finset.range (Kd + 1), |Cj j| := ⟨_, rfl⟩
  have hCJj : ∀ j ≤ Kd, |Cj j| ≤ CJ := by
    intro j hj
    rw [hCJ]
    exact Finset.single_le_sum (f := fun j => |Cj j|) (fun i _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
  refine EK.mk (le_trans ?_ h.budget) (fun j hj => h.reg j (hj.trans hle)) ?_
  · unfold regBudget
    omega
  · refine ⟨(|C| + CJ * ((Kd : ℝ) + 1)) * Λ ^ (2 * Kd + 2), fun μ hμ N s hs => ?_⟩
    have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have hsL : F.step N ≤ Λ := (step_le_L F N).trans hΛL
    set hh := F.step N with hhh
    have hpow : ∀ k : ℕ, k ≤ 2 * Kd + 2 → hh ^ k ≤ Λ ^ (2 * Kd + 2) := by
      intro k hk
      calc hh ^ k ≤ Λ ^ k := pow_le_pow_left₀ hst.le hsL k
        _ ≤ Λ ^ (2 * Kd + 2) := pow_le_pow_right₀ hΛ1 hk
    have hΛ0 : 0 ≤ Λ ^ (2 * Kd + 2) := by positivity
    have hsplit : ∀ f : ℕ → ℝ, ∑ j ∈ Finset.range (Kd + 1), hh ^ (2 * j) * f j =
        ∑ j ∈ Finset.range (Kd' + 1), hh ^ (2 * j) * f j + ∑ j ∈ Finset.Ico (Kd' + 1) (Kd + 1), hh ^ (2 * j) * f j := by
      intro f
      rw [Finset.sum_range_add_sum_Ico _ (by omega)]
    have htail : ∀ f : ℕ → ℝ, (∀ j ≤ Kd, |f j| ≤ CJ) →
        |∑ j ∈ Finset.Ico (Kd' + 1) (Kd + 1), hh ^ (2 * j) * f j| ≤
          CJ * ((Kd : ℝ) + 1) * Λ ^ (2 * Kd + 2) * hh ^ (2 * Kd' + 2) := by
      intro f hf
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ j ∈ Finset.Ico (Kd' + 1) (Kd + 1), |hh ^ (2 * j) * f j| ≤
          CJ * Λ ^ (2 * Kd + 2) * hh ^ (2 * Kd' + 2) := by
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
        have e : hh ^ (2 * j) = hh ^ (2 * Kd' + 2) * hh ^ (2 * j - (2 * Kd' + 2)) := by
          rw [← pow_add]; congr 1; omega
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ hh ^ (2 * j)), e]
        have h1 := hpow (2 * j - (2 * Kd' + 2)) (by omega)
        have hfj := hf j (by omega)
        calc hh ^ (2 * Kd' + 2) * hh ^ (2 * j - (2 * Kd' + 2)) * |f j|
            ≤ hh ^ (2 * Kd' + 2) * Λ ^ (2 * Kd + 2) * CJ := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) hfj (abs_nonneg _) (by positivity)
          _ = CJ * Λ ^ (2 * Kd + 2) * hh ^ (2 * Kd' + 2) := by ring
      calc ∑ j ∈ Finset.Ico (Kd' + 1) (Kd + 1), |hh ^ (2 * j) * f j|
          ≤ ∑ j ∈ Finset.Ico (Kd' + 1) (Kd + 1), CJ * Λ ^ (2 * Kd + 2) * hh ^ (2 * Kd' + 2) := Finset.sum_le_sum hterm
        _ = ((Kd + 1 - (Kd' + 1) : ℕ) : ℝ) * (CJ * Λ ^ (2 * Kd + 2) * hh ^ (2 * Kd' + 2)) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ ((Kd : ℝ) + 1) * (CJ * Λ ^ (2 * Kd + 2) * hh ^ (2 * Kd' + 2)) := by
            have hCJ0 : 0 ≤ CJ := (abs_nonneg _).trans (hCJj 0 (Nat.zero_le _))
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have : ((Kd + 1 - (Kd' + 1) : ℕ) : ℝ) ≤ (Kd : ℝ) + 1 := by
              have : (Kd + 1 - (Kd' + 1) : ℕ) ≤ Kd + 1 := by omega
              exact_mod_cast this
            exact this
        _ = CJ * ((Kd : ℝ) + 1) * Λ ^ (2 * Kd + 2) * hh ^ (2 * Kd' + 2) := by ring
    have hmain : ∀ (a : ℝ) (f : ℕ → ℝ), (∀ j ≤ Kd, |f j| ≤ CJ) →
        |a - ∑ j ∈ Finset.range (Kd + 1), hh ^ (2 * j) * f j| ≤ C * hh ^ (2 * Kd + 2) →
        |a - ∑ j ∈ Finset.range (Kd' + 1), hh ^ (2 * j) * f j| ≤
          (|C| + CJ * ((Kd : ℝ) + 1)) * Λ ^ (2 * Kd + 2) * hh ^ (2 * Kd' + 2) := by
      intro a f hf hrem
      have e : a - ∑ j ∈ Finset.range (Kd' + 1), hh ^ (2 * j) * f j =
          (a - ∑ j ∈ Finset.range (Kd + 1), hh ^ (2 * j) * f j) +
            ∑ j ∈ Finset.Ico (Kd' + 1) (Kd + 1), hh ^ (2 * j) * f j := by
        rw [hsplit f]; ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      have h1 : C * hh ^ (2 * Kd + 2) ≤ |C| * Λ ^ (2 * Kd + 2) * hh ^ (2 * Kd' + 2) := by
        have e2 : hh ^ (2 * Kd + 2) = hh ^ (2 * Kd' + 2) * hh ^ (2 * Kd - 2 * Kd') := by
          rw [← pow_add]; congr 1; omega
        have h3 := hpow (2 * Kd - 2 * Kd') (by omega)
        calc C * hh ^ (2 * Kd + 2) ≤ |C| * hh ^ (2 * Kd + 2) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
          _ = |C| * (hh ^ (2 * Kd' + 2) * hh ^ (2 * Kd - 2 * Kd')) := by rw [e2]
          _ ≤ |C| * (hh ^ (2 * Kd' + 2) * Λ ^ (2 * Kd + 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) (abs_nonneg _)
          _ = |C| * Λ ^ (2 * Kd + 2) * hh ^ (2 * Kd' + 2) := by ring
      have h2 := htail f hf
      calc _ ≤ |C| * Λ ^ (2 * Kd + 2) * hh ^ (2 * Kd' + 2) + CJ * ((Kd : ℝ) + 1) * Λ ^ (2 * Kd + 2) * hh ^ (2 * Kd' + 2) :=
            add_le_add (hrem.trans h1) h2
        _ = _ := by ring
    obtain ⟨hG, hB⟩ := hC μ hμ N s hs
    exact ⟨hmain _ (fun j => F.G (2 * j) μ s) (fun j hj => ((hCj j hj μ hμ s hs).1).trans ((le_abs_self _).trans (hCJj j hj))) hG,
      hmain _ (fun j => F.B (2 * j) μ s) (fun j hj => ((hCj j hj μ hμ s hs).2).trans ((le_abs_self _).trans (hCJj j hj))) hB⟩

/-- **Bridge (a)**: from `DM F K (2 Kidx + 1)`, `IsCompact K`, `HypOn F K` (the hypotheses of `PropThaSpliceTwoOrders`), the frozen family satisfies the standing
assumptions `StdAssump (frozenFamily F Kidx) (paramSet K t0') Kd r` for every `t0' <= t1` and every `Kd <= Kidx` (with one `r`): `frozenStandard` (`TheoremA/Geometry.lean`), then monotonicity in `t0` and in the index. -/
theorem stdAssump_frozen_all {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) (Kidx : ℕ)
    (hK : IsCompact K) (hH : HypOn F K) (hDM : DM F K (2 * Kidx + 1)) :
    ∃ t1 : ℝ, 0 < t1 ∧ ∃ r : ℕ, ∀ t' : ℝ, 0 < t' → t' ≤ t1 → ∀ Kd : ℕ, Kd ≤ Kidx →
      StdAssump (frozenFamily F Kidx) (paramSet K t') Kd r := by
  obtain ⟨t1, ht1, r, hr⟩ := HypMorse.frozenStandard F K Kidx hK hH hDM
  refine ⟨t1, ht1, r, fun t' ht' ht'1 Kd hKd => ?_⟩
  obtain ⟨hPc, hEK, hHyp⟩ := hr
  have hsub : paramSet K t' ⊆ paramSet K t1 :=
    Set.prod_mono subset_rfl (Set.Icc_subset_Icc (by linarith) ht'1)
  refine ⟨hK.prod isCompact_Icc, EK_mono_set (EK_mono_idx hPc hEK hKd) hsub, ?_⟩
  obtain ⟨g, hg⟩ := hHyp
  exact ⟨g, fun μ hμ => hg μ (hsub hμ)⟩

/-! ### Restriction of a bulk chart to a smaller parameter set -/

/-- Every field of a bulk Weber chart is a statement for all parameters in `P`: restriction to `P' <= P`. -/
def _root_.FormalResearch.JacobiEigenvectors.Charts.BulkWeberChart.restrict {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par}
    {P P' : Set Par} {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart F P Jlo Jhi m U V) (h : P' ⊆ P) :
    BulkWeberChart F P' Jlo Jhi m U V :=
  { C with
    overlap_in_well := fun μ hμ => C.overlap_in_well μ (h hμ)
    turn_eq := fun μ hμ => C.turn_eq μ (h hμ)
    Hz_lb := fun μ hμ => C.Hz_lb μ (h hμ)
    matchF := fun μ hμ => C.matchF μ (h hμ)
    matchO := fun μ hμ => C.matchO μ (h hμ)
    Y_bound := by
      obtain ⟨S, hS⟩ := C.Y_bound
      exact ⟨S, fun μ hμ => hS μ (h hμ)⟩
    shape := fun μ hμ => C.shape μ (h hμ)
    valid := fun μ hμ => C.valid μ (h hμ)
    A_bond := fun μ hμ => C.A_bond μ (h hμ)
    Q_diag := fun μ hμ => C.Q_diag μ (h hμ)
    dd_sqrt := fun μ hμ => C.dd_sqrt μ (h hμ)
    omega_sqrt := fun μ hμ => C.omega_sqrt μ (h hμ)
    wf_eq := fun μ hμ => C.wf_eq μ (h hμ)
    rho_one := fun μ hμ => C.rho_one μ (h hμ)
    theta_le := fun μ hμ => C.theta_le μ (h hμ)
    W_def := fun μ hμ => C.W_def μ (h hμ)
    M_def := fun μ hμ => C.M_def μ (h hμ)
    W_osc := fun μ hμ => C.W_osc μ (h hμ)
    M_osc := fun μ hμ => C.M_osc μ (h hμ)
    seed_pos := fun μ hμ => C.seed_pos μ (h hμ)
    collar_lb := fun μ hμ => C.collar_lb μ (h hμ)
    corr_lead := by
      obtain ⟨cg, Cg, hcg, g0, hg⟩ := C.corr_lead
      exact ⟨cg, Cg, hcg, g0, fun μ hμ => hg μ (h hμ)⟩
    theta_margin := by
      obtain ⟨ε, hε, hε1, hm⟩ := C.theta_margin
      exact ⟨ε, hε, hε1, fun μ hμ => hm μ (h hμ)⟩ }

/-! ### The splice row `nearestRow h (spl)` lies in the window -/

/-- If `c' < s < c`, the row nearest `s` lies in the window `{c' <= u_n <= c}` for `h` small (`|u_row - s| <= h/2`). -/
theorem nearestRow_mem_window {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart Fz P Jlo Jhi m U V) (s : ℝ) (hs : C.c' < s ∧ s < C.c) :
    ∃ hw : ℝ, 0 < hw ∧ ∀ N : ℕ, Fz.step N ≤ hw → nearestRow (Fz.step N) s ∈ bulkWindow C N := by
  obtain ⟨hc'0, hc'c, hσ, hcσ, -⟩ := C.consts_pos
  refine ⟨min (min (2 * (s - C.c')) (2 * (C.c - s))) C.c', lt_min (lt_min (by linarith) (by linarith)) hc'0, ?_⟩
  intro N hN
  have hst : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L := step_mul_succ Fz N
  have h1 : Fz.step N ≤ 2 * (s - C.c') := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : Fz.step N ≤ 2 * (C.c - s) := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : Fz.step N ≤ C.c' := hN.trans (min_le_right _ _)
  set h := Fz.step N with hh
  set row := nearestRow h s with hrow
  have hr : |s / h - 1 / 2 - (row : ℝ)| ≤ 1 / 2 := abs_sub_round (s / h - 1 / 2)
  obtain ⟨hr1, hr2⟩ := abs_le.mp hr
  have hsh : s / h * h = s := div_mul_cancel₀ s hst.ne'
  -- bounds on `u_row = (row + 1/2) h`
  have hu_hi : uNode h row ≤ s + h / 2 := by
    unfold uNode
    nlinarith [mul_le_mul_of_nonneg_right (show (row : ℝ) ≤ s / h from by linarith) hst.le]
  have hu_lo : s - h / 2 ≤ uNode h row := by
    unfold uNode
    nlinarith [mul_le_mul_of_nonneg_right (show s / h - 1 ≤ (row : ℝ) from by linarith) hst.le]
  have hrow0 : (0 : ℤ) ≤ row := by
    have : (0 : ℝ) ≤ row := by
      have : 1 ≤ s / h := by
        rw [le_div_iff₀ hst]; linarith
      linarith
    exact_mod_cast this
  have hrowN : row ≤ (N : ℤ) := by
    have hu : uNode h row < Fz.L := by linarith
    unfold uNode at hu
    rw [← hLs] at hu
    have : (row : ℝ) + 1 / 2 < (N : ℝ) + 1 := by
      by_contra hcon
      push_neg at hcon
      nlinarith [mul_le_mul_of_nonneg_right hcon hst.le]
    have : (row : ℝ) < (N : ℝ) + 1 := by linarith
    have : row < (N : ℤ) + 1 := by exact_mod_cast this
    omega
  unfold bulkWindow
  refine Finset.mem_filter.mpr ⟨?_, by linarith, by linarith⟩
  unfold rowsOf
  exact Finset.mem_Icc.mpr ⟨hrow0, hrowN⟩

/-! ### One bulk block at one order, for the frozen family on `K` -/

set_option maxHeartbeats 4000000 in
/-- **A bulk block (left chart `CL`, mirror chart `CR` on `paramSet K t0`) at order `M`, `1 <= M`, `M/2 <= Kidx`**: for the splice row `nearestRow h s` with `c' < s < c`, the column of `hat G^{[M]}` for
an eigenvalue `X` of the block is within `C h^M` of the eigenvector in `l^2`, uniformly in `mu in K`, `N` (with `h` small and `h <= t0`), the eigen-system.
The standing assumptions of the frozen family come from `stdAssump_frozen_all`, the passage from the chart's `t0` to the smaller `t0'` of `frozenStandard` by `BulkWeberChart.restrict`
(finding F-t0), and the frozen matrix at `t = h` is `J_h` (`frozenFamily_jacobiMat_at_step`). -/
theorem bulk_block_columns {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) (Kidx : ℕ) (t0 : ℝ)
    (hK : IsCompact K) (hH : HypOn F K) (hDM : DM F K (2 * Kidx + 1)) {Jlo Jhi : ℝ} {M : ℕ} {U V : ℝ → ℝ → ℝ}
    (hM : 1 ≤ M) (hMK : M / 2 ≤ Kidx)
    (CL : BulkWeberChart (frozenFamily F Kidx) (paramSet K t0) Jlo Jhi M U V)
    (CR : BulkWeberChart (mirrorFamily (frozenFamily F Kidx)) (paramSet K t0) Jlo Jhi M U V)
    (hcoup : CR.c = F.L - CL.c' ∧ CR.c' = F.L - CL.c) (s : ℝ) (hs : CL.c' < s ∧ s < CL.c) :
    ∃ C h1 : ℝ, 0 < h1 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h1 → F.step N ≤ t0 →
      ∀ X ∈ Set.Icc Jlo Jhi, ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        IsEigenSystem (F.jacobiMat μ N) Xs Um → ∀ k : Fin (N + 1), Xs k = X →
          FormalResearch.JB.jbL2 Finset.univ
            (fun i : Fin (N + 1) => bulkColAt CL CR (atStep F μ N) X N (nearestRow (F.step N) s) ((i : ℕ) : ℤ) - Um i k) ≤
              C * F.step N ^ M := by
  by_cases ht0 : 0 < t0
  swap
  · refine ⟨0, 1, one_pos, ?_⟩
    intro μ hμ N _ hle
    exfalso
    have := FormalResearch.JB.stepSize_pos F.L_pos N
    exact absurd (this.trans_le hle) (not_lt.mpr (not_lt.mp ht0))
  obtain ⟨t1, ht1, r, hstd⟩ := stdAssump_frozen_all F K Kidx hK hH hDM
  have ht2 : 0 < min t0 t1 := lt_min ht0 ht1
  have hsub : paramSet K (min t0 t1) ⊆ paramSet K t0 :=
    Set.prod_mono subset_rfl (Set.Icc_subset_Icc (by linarith [min_le_left t0 t1]) (min_le_left _ _))
  have hr := hstd (min t0 t1) ht2 (min_le_right _ _) (M / 2) hMK
  obtain ⟨C, h1, hh1, hcl⟩ := bulk_col_clause (CL.restrict hsub) (CR.restrict hsub) hM hcoup r hr
  obtain ⟨hw, hhw, hwin⟩ := nearestRow_mem_window (CL.restrict hsub) s hs
  obtain ⟨N0, hN0⟩ : ∃ n : ℕ, n = max CL.N0 CR.N0 := ⟨_, rfl⟩
  refine ⟨C, min (min h1 (min t0 t1)) (min hw (F.L / ((N0 : ℝ) + 1))), ?_, ?_⟩
  · exact lt_min (lt_min hh1 ht2) (lt_min hhw (by have := F.L_pos; positivity))
  intro μ hμ N hN1 hNt X hX Xs Um hE k hk
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hs1 : F.step N ≤ h1 := hN1.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 : F.step N ≤ min t0 t1 := hN1.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : F.step N ≤ hw := hN1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs4 : F.step N ≤ F.L / ((N0 : ℝ) + 1) := hN1.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hNN : N0 ≤ N := by
    by_contra hcon
    push_neg at hcon
    have h5 : (N : ℝ) + 1 < (N0 : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hcon
    have h6 : F.L / ((N0 : ℝ) + 1) < F.L / ((N : ℝ) + 1) :=
      div_lt_div_of_pos_left F.L_pos (by positivity) h5
    exact absurd hs4 (not_le.mpr h6)
  have hNmax : max (CL.restrict hsub).N0 (CR.restrict hsub).N0 ≤ N := by
    show max CL.N0 CR.N0 ≤ N
    rw [← hN0]
    exact hNN
  have hp : atStep F μ N ∈ paramSet K (min t0 t1) :=
    ⟨hμ, ⟨by show -(min t0 t1) ≤ F.step N; linarith, hs2⟩⟩
  have hE' : IsEigenSystem ((frozenFamily F Kidx).jacobiMat (atStep F μ N) N) Xs Um := by
    unfold atStep
    rw [frozenFamily_jacobiMat_at_step]
    exact hE
  exact hcl (atStep F μ N) hp X hX N hNmax hs1 _ (hwin N hs3) Xs Um hE' k hk

/-! ### The columns of `compMatrix` for bulk energies -/

set_option maxHeartbeats 4000000 in
/-- **Bulk columns of `hat G^{[M]}` (one order)**: for every column `j` whose energy lies in a bulk block, `||(hat G^{[M]} - U) e_j||_2 <= C h^M`, uniformly in `mu in K`, `N` and the eigen-system,
for splices `spl nu` in the open overlap of the block. -/
theorem compMatrix_bulk_col {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {M q : ℕ}
    {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ} (CI : ChartInputs F K Kidx t0 M q U V cPC CPC) (spl : Fin CI.nb → ℝ)
    (hK : IsCompact K) (hH : HypOn F K) (hDM : DM F K (2 * Kidx + 1)) (hM : 1 ≤ M) (hMK : M / 2 ≤ Kidx)
    (hspl : ∀ ν, (CI.bulkL ν).c' < spl ν ∧ spl ν < (CI.bulkL ν).c) :
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∀ j : Fin (N + 1), (∃ ν, CI.lo ν ≤ Xs j ∧ Xs j ≤ CI.hi ν) →
          FormalResearch.JB.jbL2 Finset.univ (fun i : Fin (N + 1) => compMatrix CI spl μ N Xs i j - Um i j) ≤ C * F.step N ^ M := by
  have hblk : ∀ ν : Fin CI.nb, ∃ C h1 : ℝ, 0 < h1 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h1 → F.step N ≤ t0 →
      ∀ X ∈ Set.Icc (CI.lo ν) (CI.hi ν), ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        IsEigenSystem (F.jacobiMat μ N) Xs Um → ∀ k : Fin (N + 1), Xs k = X →
          FormalResearch.JB.jbL2 Finset.univ
            (fun i : Fin (N + 1) => bulkColAt (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) X N (nearestRow (F.step N) (spl ν)) ((i : ℕ) : ℤ) - Um i k) ≤
              C * F.step N ^ M :=
    fun ν => bulk_block_columns F K Kidx t0 hK hH hDM hM hMK (CI.bulkL ν) (CI.bulkR ν) (CI.overlap_match ν) (spl ν) (hspl ν)
  choose Cf hf hfpos hfprop using hblk
  refine ⟨∑ ν, |Cf ν|, 1 / (1 + ∑ ν, 1 / hf ν), ?_, ?_⟩
  · have : 0 ≤ ∑ ν, 1 / hf ν := Finset.sum_nonneg fun ν _ => by have := hfpos ν; positivity
    positivity
  intro μ hμ N hN hNt Xs Um hE j hj
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  set ν := Classical.choose hj with hνdef
  obtain ⟨hν1, hν2⟩ := Classical.choose_spec hj
  have hcol : ∀ i : Fin (N + 1), compMatrix CI spl μ N Xs i j =
      bulkColAt (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) (Xs j) N (nearestRow (F.step N) (spl ν)) ((i : ℕ) : ℤ) := by
    intro i
    simp only [compMatrix, Matrix.of_apply, compColumn, dif_pos hj] <;> rfl
  have hhν : F.step N ≤ hf ν := by
    refine hN.trans ?_
    have h1 : 1 / hf ν ≤ ∑ ν', 1 / hf ν' :=
      Finset.single_le_sum (f := fun ν' => 1 / hf ν') (fun ν' _ => by have := hfpos ν'; positivity) (Finset.mem_univ ν)
    have h2 : 1 / hf ν ≤ 1 + ∑ ν', 1 / hf ν' := by linarith
    rw [div_le_iff₀ (by have : 0 ≤ ∑ ν', 1 / hf ν' := Finset.sum_nonneg fun ν' _ => by have := hfpos ν'; positivity
                        positivity)]
    rw [div_le_iff₀ (hfpos ν)] at h2
    linarith
  have hb := hfprop ν μ hμ N hhν hNt (Xs j) ⟨hν1, hν2⟩ Xs Um hE j rfl
  have e : (fun i : Fin (N + 1) => compMatrix CI spl μ N Xs i j - Um i j) =
      (fun i : Fin (N + 1) => bulkColAt (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) (Xs j) N (nearestRow (F.step N) (spl ν)) ((i : ℕ) : ℤ) - Um i j) := by
    funext i
    rw [hcol i]
  rw [e]
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hst.le _))
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun ν' => |Cf ν'|) (fun ν' _ => abs_nonneg _) (Finset.mem_univ ν))

/-! ### `prop:tha-splice` (c), bulk columns, two orders -/

/-- `h^{m+1} <= eta_{m+1}` for `h <= e^{-1}`: the logarithm only helps. -/
theorem etaR_succ_ge (m : ℕ) (h : ℝ) (hh : 0 < h) (he : h ≤ Real.exp (-1)) : h ^ (m + 1) ≤ etaR m (m + 1) h := by
  have hlog : 1 ≤ Real.log (1 / h) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    rw [one_div, le_inv_comm₀ (Real.exp_pos 1) hh, ← Real.exp_neg]
    exact he
  have hp : 0 < h ^ (m + 1) := by positivity
  unfold etaR
  rw [if_neg (by omega)]
  split_ifs
  · nlinarith
  · exact le_refl _

/-- `eta_m = h^m` at order `m`. -/
theorem etaR_self (m : ℕ) (h : ℝ) : etaR m m h = h ^ m := by
  unfold etaR
  rw [if_pos rfl]

set_option maxHeartbeats 4000000 in
/-- **`PropThaSpliceTwoOrders`, bulk columns** (`prop:tha-splice` (c) for the columns whose energy lies in a bulk block): with the hypotheses of the frozen statement (`1 <= m`, `Kidx = (m+1)/2`,
`q = 2 Kidx`, `IsCompact K`, `HypOn F K`, `DM F K (2 Kidx + 1)`, `SplicesInWindow`), there are `C`, `h0` such that for every `mu in K`, `N` with `h <= h0`, `h <= t0`, every eigen-system and every column `j` with `X_j` in a block,
`||(hat G^{[m]} - U) e_j||_2 <= C eta_m` and `||(hat G^{[m+1]} - U) e_j||_2 <= C eta_{m+1}`.  The soft columns (`X_j` outside all blocks) are the soft half (`PropThaSpliceSoft`). -/
theorem twoOrders_bulk_columns {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ}
    {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) (hm : 1 ≤ m) (hK : Kidx = (m + 1) / 2) (hKc : IsCompact K) (hH : HypOn F K)
    (hDM : DM F K (2 * Kidx + 1)) (hspl : CP.SplicesInWindow spl) :
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∀ j : Fin (N + 1), (∃ ν, CP.CI0.lo ν ≤ Xs j ∧ Xs j ≤ CP.CI0.hi ν) →
          FormalResearch.JB.jbL2 Finset.univ (fun i => compMatrix CP.CI0 spl μ N Xs i j - Um i j) ≤ C * etaR m m (F.step N) ∧
          FormalResearch.JB.jbL2 Finset.univ (fun i => compMatrix CP.CI1 (CP.spl1 spl) μ N Xs i j - Um i j) ≤ C * etaR m (m + 1) (F.step N) := by
  obtain ⟨C0, h00, hh00, hb0⟩ := compMatrix_bulk_col CP.CI0 spl hKc hH hDM hm (by omega) hspl.1
  obtain ⟨C1, h01, hh01, hb1⟩ := compMatrix_bulk_col CP.CI1 (CP.spl1 spl) hKc hH hDM (by omega) (by omega) hspl.2
  refine ⟨|C0| + |C1|, min (min h00 h01) (Real.exp (-1)), lt_min (lt_min hh00 hh01) (Real.exp_pos _), ?_⟩
  intro μ hμ N hN hNt Xs Um hE j hj
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hs0 : F.step N ≤ h00 := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hs1 : F.step N ≤ h01 := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hse : F.step N ≤ Real.exp (-1) := hN.trans (min_le_right _ _)
  have hj1 : ∃ ν, CP.CI1.lo ν ≤ Xs j ∧ Xs j ≤ CP.CI1.hi ν := by
    obtain ⟨ν, hν1, hν2⟩ := hj
    refine ⟨Fin.cast CP.nb_eq.symm ν, ?_, ?_⟩
    · rw [CP.lo_eq]; simpa using hν1
    · rw [CP.hi_eq]; simpa using hν2
  have e0 := hb0 μ hμ N hs0 hNt Xs Um hE j hj
  have e1 := hb1 μ hμ N hs1 hNt Xs Um hE j hj1
  have a0 : |C0| + |C1| ≥ C0 := by linarith [le_abs_self C0, abs_nonneg C1]
  have a1 : |C0| + |C1| ≥ C1 := by linarith [le_abs_self C1, abs_nonneg C0]
  constructor
  · rw [etaR_self]
    exact e0.trans (mul_le_mul_of_nonneg_right a0 (pow_nonneg hst.le _))
  · refine e1.trans ?_
    calc C1 * F.step N ^ (m + 1) ≤ (|C0| + |C1|) * F.step N ^ (m + 1) :=
          mul_le_mul_of_nonneg_right a1 (pow_nonneg hst.le _)
      _ ≤ (|C0| + |C1|) * etaR m (m + 1) (F.step N) :=
          mul_le_mul_of_nonneg_left (etaR_succ_ge m _ hst hse) (by positivity)

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulk_env_sq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulk_env_sq_sum

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulk_col_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulk_col_clause

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.EK_mono_idx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.EK_mono_idx

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.stdAssump_frozen_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.stdAssump_frozen_all

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulk_block_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulk_block_columns

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.compMatrix_bulk_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.compMatrix_bulk_col

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.twoOrders_bulk_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.twoOrders_bulk_columns

end FormalResearch.JacobiEigenvectors.TheoremB
