module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.SpliceSoftFacts
public import FormalResearch.JacobiEigenvectors.TheoremB.SpliceBulk
public import FormalResearch.JacobiEigenvectors.TheoremB.Statements

/-!
# Paper J, Theorem B, L3.1 soft: independence of the splice at a soft edge (`prop:tha-splice` (b))

Source: Paper J `thmB.tex` `prop:tha-splice` (b) and `app_thmB.tex`, proof of `prop:tha-splice` (`eq:tha-spl1`--`eq:tha-spl3`, "The fixed row `n_c` is a splice for every column").
Statement: `PropThaSpliceSoft CL CR eta cPC CPC` (`TheoremB/Statements.lean`; the premise `ParabolicCylinderFacts` was added in round 10, as in `PropThaW2`).

## Proved here

`propThaSpliceSoft_proved : PropThaSpliceSoft CL CR (fun h => h ^ m) cPC CPC`, for every soft chart pair; no premise beyond the statement's own (`ParabolicCylinderFacts U V cPC CPC`, `1 <= m`, `SoftMirror CL CR`).  The smallness `SoftFoldSmall CL` is the chart field `delta0_small`.
Chain (as in the paper, with the three clauses of the statement):
1. `n_c = nearestRow u_c` lies in the window (`fold_in_window`, flat0 of `lem:tha-Mflat`);
2. window matching `|psi-hat^L - hat kappa psi-hat^R| <= C h^m |lambda_L| kappa_bal^{-1} M_bal` (`soft_splice_facts`: `soft_win_err` for both charts and the mirror window, `right_alg`, `soft_match`);
3. normaliser ratio `|hat N(n_s)/hat N - 1| <= C h^m` (`soft_split_agree`: the splits `n <= n_s` and `Z_n <= 0` agree off the window; `glue_norm_sq_diff`, `sq_diff_window`, `norm_ratio_bound`, `c_n T^2 h^{-1/2} <= hat N^2` of `soft_match`, `m_Omega <= C h^{-1/2}`);
4. the eigenvector comparison `|Psi - hat Psi^{(n_s)}| <= C h^m softEnv`: `soft_eigen_clause` (at eigenvalues obeying Step 0, from `stepZero` under `StdAssump`) plus the splice-versus-standard difference
   (`splice_pt`: rows where the splits differ are in the window; there the matching bound against `softEnvNum >= c_lb T M_bal`).

## Differences from the paper

* None.  The statement carries `ParabolicCylinderFacts` (finding F-B14/F-B15 pattern, applied to the definition); the chart-constant smallness (`delta_0` against `c_Z, cmu0, Cmu0`, the paper's "choose `delta_0` small") is the chart field `delta0_small` (without it `n_c` is not in the window).
* The window membership of `n_c` is the first conjunct of the statement and is independent of the eigen-system.

## Not formalised

Nothing of the statement; `eta = h^m` (the order `m + 1` columns use `etaR` through `PropThaSpliceTwoOrders`, not here).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

/-- **Pointwise splice-versus-standard** (abstract): `|x/N_0 - s/N_1| <= (M + 2 e (K + M)) (E/N_0)` when `|N_1/N_0 - 1| <= e <= 1/2`, `|x| <= K E`, and `s = x` or `|x - s| <= M E`. -/
theorem splice_pt (x s N0 N1 e K M E : ℝ) (hN0 : 0 < N0) (hN1 : 0 < N1) (hr : |N1 / N0 - 1| ≤ e) (he : e ≤ 1 / 2)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hE : 0 ≤ E) (hx : |x| ≤ K * E) (hs : s = x ∨ |x - s| ≤ M * E) :
    |x / N0 - s / N1| ≤ (M + 2 * e * (K + M)) * (E / N0) := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans hr
  have hEN : 0 ≤ E / N0 := div_nonneg hE hN0.le
  rcases hs with rfl | hs
  · have h := div_pair_bound s N0 N1 e hN0 hN1 hr he
    rw [abs_sub_comm]
    refine h.trans ?_
    have h1 : 2 * e * |s| / N0 ≤ 2 * e * (K * E) / N0 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by positivity)) hN0.le
    refine h1.trans ?_
    have : 2 * e * (K * E) / N0 = (2 * e * K) * (E / N0) := by ring
    rw [this]
    have : 0 ≤ M * (E / N0) := mul_nonneg hM hEN
    nlinarith [mul_nonneg (mul_nonneg he0 hM) hEN]
  · have hsx : |s| ≤ (K + M) * E := by
      have := abs_sub_abs_le_abs_sub s x
      rw [abs_sub_comm] at this
      nlinarith [hx, hs]
    have h2 := div_pair_bound s N0 N1 e hN0 hN1 hr he
    have e1 : x / N0 - s / N1 = (x - s) / N0 + (s / N0 - s / N1) := by ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    have h3 : |(x - s) / N0| ≤ M * (E / N0) := by
      rw [abs_div, abs_of_pos hN0]
      calc |x - s| / N0 ≤ (M * E) / N0 := div_le_div_of_nonneg_right hs hN0.le
        _ = M * (E / N0) := by ring
    have h4 : |s / N0 - s / N1| ≤ 2 * e * (K + M) * (E / N0) := by
      rw [abs_sub_comm]
      refine h2.trans ?_
      have : 2 * e * |s| / N0 ≤ 2 * e * ((K + M) * E) / N0 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsx (by positivity)) hN0.le
      refine this.trans (le_of_eq ?_)
      ring
    linarith

/-- `|u_{nearestRow h x} - x| <= h/2`. -/
theorem nearestRow_close (h x : ℝ) (hh : 0 < h) : |uNode h (nearestRow h x) - x| ≤ h / 2 := by
  have hr := abs_sub_round (x / h - 1 / 2)
  unfold nearestRow uNode
  have e : ((round (x / h - 1 / 2) : ℤ) + 1 / 2 : ℝ) * h - x = (((round (x / h - 1 / 2) : ℤ) : ℝ) - (x / h - 1 / 2)) * h := by
    field_simp; ring
  rw [e, abs_mul, abs_of_pos hh, abs_sub_comm]
  nlinarith

section Split

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- **The splits `n <= n_s` and `Z_n <= 0` agree off the window** (for `n_s` in the window): rows below `n_s` have `Z_n <= rho` (`Zof_le` on the collar, `zeta_sign_out` beyond), rows above have `Z_n >= -rho`. -/
theorem soft_split_agree {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ} (hs : Fz.step N ≤ asmH0 C)
    {ns n : ℤ} (hns : ns ∈ softWindow C p X N) (hn : n ∈ rowsOf N) (hnΩ : n ∉ softWindow C p X N) :
    (n ≤ ns ↔ C.Zof p X N n ≤ 0) := by
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hη := C.consts_pos.2.1
  have hα := C.abs_alpha_le hX
  have hcol := soft_win_loc C hp hX hs hns
  obtain ⟨hcl, hcu⟩ := abs_lt.mp hcol
  have hnsZ : |C.Zof p X N ns| ≤ rhoWin (C.aOf p X N) := (Finset.mem_filter.mp hns).2
  have hρ0 : 0 ≤ rhoWin (C.aOf p X N) := by unfold rhoWin; positivity
  have hnZ : rhoWin (C.aOf p X N) < |C.Zof p X N n| := by
    by_contra hcon
    push Not at hcon
    exact hnΩ (Finset.mem_filter.mpr ⟨hn, hcon⟩)
  obtain ⟨hu0, huL⟩ := uNode_row_mem (Fz := Fz) hn
  have hsgn := fun hx : C.η / 4 ≤ |uNode (Fz.step N) n - C.uc p| =>
    C.zeta_sign_out p hp (Fz.bandHi p - X) hα _ hx (by linarith) (by linarith)
  have hZn : C.Zof p X N n = C.zeta p (Fz.bandHi p - X) (uNode (Fz.step N) n - C.uc p) / Real.sqrt (Fz.step N) := rfl
  have hsq := Real.sqrt_pos.mpr hh0
  have hnsZ' := abs_le.mp hnsZ
  -- rows below `n_s` have `Z_n <= rho`
  have hlow : n ≤ ns → C.Zof p X N n ≤ rhoWin (C.aOf p X N) := by
    intro hle
    have hxle := uNode_le_of_le hh0.le hle
    by_cases hx : -(C.η / 2) ≤ uNode (Fz.step N) n - C.uc p
    · have := Zof_le C hp hX N hle (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
      linarith
    · push Not at hx
      have hxa : C.η / 4 ≤ |uNode (Fz.step N) n - C.uc p| := by rw [abs_of_neg (by linarith)]; linarith
      have := (hsgn hxa).1 (by linarith)
      rw [hZn]
      have : C.zeta p (Fz.bandHi p - X) (uNode (Fz.step N) n - C.uc p) / Real.sqrt (Fz.step N) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg this hsq.le
      linarith
  have hup : ns < n → -rhoWin (C.aOf p X N) ≤ C.Zof p X N n := by
    intro hlt
    have hxle := uNode_le_of_le hh0.le hlt.le
    by_cases hx : uNode (Fz.step N) n - C.uc p ≤ C.η / 2
    · have := Zof_le C hp hX N hlt.le (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
      linarith
    · push Not at hx
      have hxa : C.η / 4 ≤ |uNode (Fz.step N) n - C.uc p| := by rw [abs_of_pos (by linarith)]; linarith
      have := (hsgn hxa).2 (by linarith)
      rw [hZn]
      have : 0 ≤ C.zeta p (Fz.bandHi p - X) (uNode (Fz.step N) n - C.uc p) / Real.sqrt (Fz.step N) :=
        div_nonneg this hsq.le
      linarith
  constructor
  · intro hle
    have h1 := hlow hle
    by_contra hcon
    push Not at hcon
    rw [abs_of_pos hcon] at hnZ
    linarith
  · intro hZ
    by_contra hcon
    push Not at hcon
    have h1 := hup hcon
    rw [abs_of_nonpos hZ] at hnZ
    linarith

end Split

section Main

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}

/-- **`prop:tha-splice` (b)** (`PropThaSpliceSoft`) with `eta(h) = h^m`, (the statement carries the premises `ParabolicCylinderFacts`, `1 <= m`, `SoftMirror`; the chart-constant smallness is the chart field `delta0_small`). -/
theorem propThaSpliceSoft_proved {cPC CPC : ℝ} (CL : SoftEdgeChart Fz P m q U V (fun _ => 1))
    (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1)) :
    PropThaSpliceSoft CL CR (fun h => h ^ m) cPC CPC := by
  unfold PropThaSpliceSoft
  intro hf hm hM r hr
  have hfold : SoftFoldSmall CL := CL.delta0_small
  have hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ (fun _ : ℝ => (1 : ℝ)) h := fun _ _ _ => le_rfl
  obtain ⟨Cenv, Cm, K, CM, cn, clb, hF0, hCenv, hCm, hK, hCM, hcn, hclb, hF0p, Hf⟩ := soft_splice_facts CL CR hM hf hm hLm
  obtain ⟨Cz, hz0, hz0p, Hz⟩ := stepZero Fz P (q / 2) r hr
  obtain ⟨Cc, hc0, hc0p, Hc⟩ := soft_eigen_clause CL CR hM hf hm hLm Cz
  obtain ⟨hw0, hw0p, Hw⟩ := fold_in_window CL hfold
  set Cn : ℝ := Cm * K * CM / cn with hCn
  have hCn0 : 0 ≤ Cn := by rw [hCn]; positivity
  set Mc : ℝ := Cm / clb with hMc
  have hMc0 : 0 ≤ Mc := by rw [hMc]; positivity
  set Cv : ℝ := |Cc| + (Mc + 2 * Cn * (Cenv + Mc)) with hCv
  have hCv0 : 0 ≤ Cv := by rw [hCv]; positivity
  refine ⟨max (max Cn Cm) Cv,
    min (min (min hF0 hc0) (min hw0 hz0)) (min (min (min CL.softH1 CR.softH1) (min CL.η CR.η)) (min (asmH0 CL) (1 / (2 * (Cn + 1))))),
    lt_min (lt_min (lt_min hF0p hc0p) (lt_min hw0p hz0p))
      (lt_min (lt_min (lt_min CL.softH1_pos CR.softH1_pos) (lt_min CL.consts_pos.2.1 CR.consts_pos.2.1)) (lt_min (asmH0_pos CL) (by positivity))), ?_⟩
  intro p hp X hX N hN hstep ha
  have hA1 := hstep.trans (min_le_left _ _)
  have hA2 := hstep.trans (min_le_right _ _)
  have sF : Fz.step N ≤ hF0 := hA1.trans ((min_le_left _ _).trans (min_le_left _ _))
  have sc : Fz.step N ≤ hc0 := hA1.trans ((min_le_left _ _).trans (min_le_right _ _))
  have sw : Fz.step N ≤ hw0 := hA1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have sz : Fz.step N ≤ hz0 := hA1.trans ((min_le_right _ _).trans (min_le_right _ _))
  have sH1 : Fz.step N ≤ CL.softH1 := hA2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have sH1R : Fz.step N ≤ CR.softH1 := hA2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have sη : Fz.step N ≤ CL.η := hA2.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have sηR : Fz.step N ≤ CR.η := hA2.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have sAs : Fz.step N ≤ asmH0 CL := hA2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have sCn : Fz.step N ≤ 1 / (2 * (Cn + 1)) := hA2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hN2 : CR.N0 ≤ N := (le_max_right _ _).trans hN
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hh1 : Fz.step N ≤ 1 := sAs.trans (asmH0_le_one CL)
  have hnc := Hw p hp X hX N hN1 sw ha (nearestRow (Fz.step N) (CL.uc p)) (nearestRow_close _ _ hh0)
  refine ⟨hnc.1, ?_⟩
  intro ns hns Xs Um hE k hk
  subst hk
  set ε : ℝ := Fz.step N ^ m with hε
  have hε0 : 0 ≤ ε := pow_nonneg hh0.le _
  have hε1 : ε ≤ 1 := pow_le_one₀ hh0.le hh1
  have hεh : ε ≤ Fz.step N := pow_le_of_le_one hh0.le hh1 (by omega)
  have hCnε : Cn * ε ≤ 1 / 2 := by
    have h1 : Cn * ε ≤ Cn * (1 / (2 * (Cn + 1))) := mul_le_mul_of_nonneg_left (hεh.trans sCn) hCn0
    have h2 : Cn * (1 / (2 * (Cn + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    exact h1.trans h2
  obtain ⟨ψL, ψ', κ, hJL, hsL, hJR, hsR, hrel⟩ := eig_exact_data CL CR hM hp hN1 hN2 sH1 sH1R sη sηR Xs Um hE k hX
  obtain ⟨hT, E1, E2, E3, E4, E5, E7⟩ := Hf p hp N hN sF (Xs k) hX ha ψL ψ' κ hJL hsL hJR hsR hrel
  have hst0 : ∀ i, Xs i ≤ Fz.bandHi p + Cz * Fz.step N ^ 2 := fun i => (Hz p hp N sz Xs Um hE i).2
  obtain ⟨hrow, -, -⟩ := Hc p hp N hN sc Xs Um hE hst0 k hX
  simp only [mul_one] at E2 hrow
  set a := CL.aOf p (Xs k) N with hadef
  set T := |CL.lamL p (Xs k) N| / kappaBal a with hTdef
  have hΩrows : softWindow CL p (Xs k) N ⊆ rowsOf N := fun n hn => (Finset.mem_filter.mp hn).1
  have hMn0 : ∀ n, 0 ≤ Mbal a (CL.Zof p (Xs k) N n) := fun n => Mbal_nonneg' _ _
  -- the normaliser ratio
  have hnorm : |glueNormAt (CL.psiHatL p (Xs k) N) (softSeqR CR p (Xs k) N) (softWindow CL p (Xs k) N) (rowsOf N) ns /
      softNorm CL CR p (Xs k) N - 1| ≤ Cn * ε := by
    have hAB : ∀ n ∈ rowsOf N, n ∉ softWindow CL p (Xs k) N → ((n ≤ ns) ↔ CL.Zof p (Xs k) N n ≤ 0) :=
      fun n hn hnΩ => soft_split_agree CL hp hX sAs hns hn hnΩ
    have hdiff := glue_norm_sq_diff (CL.psiHatL p (Xs k) N) (softSeqR CR p (Xs k) N) (softWindow CL p (Xs k) N) (rowsOf N)
      (fun n => n ≤ ns) (fun n => CL.Zof p (Xs k) N n ≤ 0) hAB
    have hpt : ∀ n ∈ softWindow CL p (Xs k) N, |CL.psiHatL p (Xs k) N n ^ 2 - softKappa CL CR p (Xs k) N ^ 2 * softSeqR CR p (Xs k) N n ^ 2| ≤
        Cm * K * ε * (T * Mbal a (CL.Zof p (Xs k) N n)) ^ 2 := fun n hn =>
      sq_diff_window _ _ _ _ _ _ _ (mul_nonneg hT.le (hMn0 n)) hCm hε0 hK (E2 n hn) (E3 n hn)
    have hnn : ∀ n ∈ softWindow CL p (Xs k) N, 0 ≤ Cm * K * ε * (T * Mbal a (CL.Zof p (Xs k) N n)) ^ 2 := fun n _ =>
      mul_nonneg (mul_nonneg (mul_nonneg hCm hK) hε0) (sq_nonneg _)
    have hsum : ∑ n ∈ rowsOf N, (if n ∈ softWindow CL p (Xs k) N then
        |CL.psiHatL p (Xs k) N n ^ 2 - softKappa CL CR p (Xs k) N ^ 2 * softSeqR CR p (Xs k) N n ^ 2| else 0) ≤
        Cm * K * ε * T ^ 2 * (CM * Fz.step N ^ (-(1 : ℝ) / 2)) := by
      calc _ ≤ ∑ n ∈ rowsOf N, (if n ∈ softWindow CL p (Xs k) N then Cm * K * ε * (T * Mbal a (CL.Zof p (Xs k) N n)) ^ 2 else 0) := by
            refine Finset.sum_le_sum fun n _ => ?_
            by_cases hnW : n ∈ softWindow CL p (Xs k) N
            · simp only [hnW, if_true]; exact hpt n hnW
            · simp only [hnW, ite_false, le_refl]
        _ = ∑ n ∈ softWindow CL p (Xs k) N, Cm * K * ε * (T * Mbal a (CL.Zof p (Xs k) N n)) ^ 2 :=
            window_indicator_sum_le _ _ _ hΩrows hnn
        _ = Cm * K * ε * T ^ 2 * wmMass CL p (Xs k) N := by
            unfold wmMass; rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun n _ => by ring
        _ ≤ Cm * K * ε * T ^ 2 * (CM * Fz.step N ^ (-(1 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left E4 (mul_nonneg (mul_nonneg (mul_nonneg hCm hK) hε0) (sq_nonneg _))
    have hx2 : |glueNormAt (CL.psiHatL p (Xs k) N) (softSeqR CR p (Xs k) N) (softWindow CL p (Xs k) N) (rowsOf N) ns ^ 2 -
        softNorm CL CR p (Xs k) N ^ 2| ≤ Cm * K * ε * T ^ 2 * (CM * Fz.step N ^ (-(1 : ℝ) / 2)) := hdiff.trans hsum
    have hE0 : 0 < Fz.step N ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hh0 _
    have hBpos : 0 < cn * (T ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2)) := by positivity
    have hypos : 0 < softNorm CL CR p (Xs k) N := by
      have hnn : 0 ≤ softNorm CL CR p (Xs k) N := Real.sqrt_nonneg _
      refine lt_of_le_of_ne hnn (fun h => ?_)
      rw [← h] at E5; simp at E5; linarith
    have hratio := norm_ratio_bound _ _ _ _ (Real.sqrt_nonneg _) hypos hx2 hBpos E5
    refine hratio.trans (le_of_eq ?_)
    rw [hCn]; field_simp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · beta_reduce
    have hmax : Cn ≤ max (max Cn Cm) Cv := (le_max_left _ _).trans (le_max_left _ _)
    exact hnorm.trans (mul_le_mul_of_nonneg_right hmax hε0)
  · intro n hn
    beta_reduce
    have hmax : Cm ≤ max (max Cn Cm) Cv := (le_max_right _ _).trans (le_max_left _ _)
    refine (E2 n hn).trans ?_
    have hM0 := hMn0 n
    have hκ := kappaBal_pos a
    have e : Cm * ε * (T * Mbal a (CL.Zof p (Xs k) N n)) = Cm * ε * |CL.lamL p (Xs k) N| * (kappaBal a)⁻¹ * Mbal a (CL.Zof p (Xs k) N n) := by
      rw [hTdef]; ring
    rw [e]
    have : 0 ≤ ε * |CL.lamL p (Xs k) N| * (kappaBal a)⁻¹ * Mbal a (CL.Zof p (Xs k) N n) := by
      have := inv_nonneg.mpr hκ.le
      positivity
    calc Cm * ε * |CL.lamL p (Xs k) N| * (kappaBal a)⁻¹ * Mbal a (CL.Zof p (Xs k) N n)
        = Cm * (ε * |CL.lamL p (Xs k) N| * (kappaBal a)⁻¹ * Mbal a (CL.Zof p (Xs k) N n)) := by ring
      _ ≤ max (max Cn Cm) Cv * (ε * |CL.lamL p (Xs k) N| * (kappaBal a)⁻¹ * Mbal a (CL.Zof p (Xs k) N n)) :=
          mul_le_mul_of_nonneg_right hmax this
      _ = _ := by ring
  · intro n hn
    beta_reduce
    have hEn0 : 0 ≤ softEnv CL CR p (Xs k) N n := softEnv_nonneg CL CR hf p (Xs k) N n
    have hEnum0 : 0 ≤ softEnvNum CL CR p (Xs k) N n := softEnvNum_nonneg hf CL CR p (Xs k) N n
    have hypos : 0 < softNorm CL CR p (Xs k) N := by
      have hE0 : 0 < Fz.step N ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hh0 _
      have hBpos : 0 < cn * (T ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2)) := by positivity
      have hnn : 0 ≤ softNorm CL CR p (Xs k) N := Real.sqrt_nonneg _
      refine lt_of_le_of_ne hnn (fun h => ?_)
      rw [← h] at E5; simp at E5; linarith
    have hr1 := hnorm
    have hN1pos : 0 < glueNormAt (CL.psiHatL p (Xs k) N) (softSeqR CR p (Xs k) N) (softWindow CL p (Xs k) N) (rowsOf N) ns := by
      have h2 : 0 < glueNormAt (CL.psiHatL p (Xs k) N) (softSeqR CR p (Xs k) N) (softWindow CL p (Xs k) N) (rowsOf N) ns /
          softNorm CL CR p (Xs k) N := by
        have := (abs_le.mp hr1).1
        linarith
      exact (div_pos_iff_of_pos_right hypos).mp h2
    have hs : (softNum CL CR p (Xs k) N n = (if n ≤ ns then CL.psiHatL p (Xs k) N n else softKappa CL CR p (Xs k) N * softSeqR CR p (Xs k) N n)) ∨
        |softNum CL CR p (Xs k) N n - (if n ≤ ns then CL.psiHatL p (Xs k) N n else softKappa CL CR p (Xs k) N * softSeqR CR p (Xs k) N n)| ≤
          (Mc * ε) * softEnvNum CL CR p (Xs k) N n := by
      by_cases hiff : (n ≤ ns ↔ CL.Zof p (Xs k) N n ≤ 0)
      · left
        unfold softNum
        by_cases hz : CL.Zof p (Xs k) N n ≤ 0
        · rw [ite_eq_left hz, ite_eq_left (hiff.mpr hz)]
        · rw [ite_eq_right hz, ite_eq_right (fun h => hz (hiff.mp h))]
      · right
        have hnΩ : n ∈ softWindow CL p (Xs k) N := by
          by_contra hnΩ
          exact hiff (soft_split_agree CL hp hX sAs hns hn hnΩ)
        have hm2 := E2 n hnΩ
        have h7 := E7 n hnΩ
        have hbd : Cm * ε * (T * Mbal a (CL.Zof p (Xs k) N n)) ≤ (Mc * ε) * softEnvNum CL CR p (Xs k) N n := by
          have h8 : T * Mbal a (CL.Zof p (Xs k) N n) ≤ softEnvNum CL CR p (Xs k) N n / clb := by
            rw [le_div_iff₀ hclb]; linarith
          calc Cm * ε * (T * Mbal a (CL.Zof p (Xs k) N n)) ≤ Cm * ε * (softEnvNum CL CR p (Xs k) N n / clb) :=
                mul_le_mul_of_nonneg_left h8 (mul_nonneg hCm hε0)
            _ = (Mc * ε) * softEnvNum CL CR p (Xs k) N n := by rw [hMc]; field_simp
        have habs : |softNum CL CR p (Xs k) N n - (if n ≤ ns then CL.psiHatL p (Xs k) N n else softKappa CL CR p (Xs k) N * softSeqR CR p (Xs k) N n)| =
            |CL.psiHatL p (Xs k) N n - softKappa CL CR p (Xs k) N * softSeqR CR p (Xs k) N n| := by
          unfold softNum
          by_cases hz : CL.Zof p (Xs k) N n ≤ 0
          · have hn' : ¬ n ≤ ns := fun h => hiff ⟨fun _ => hz, fun _ => h⟩
            rw [ite_eq_left hz, ite_eq_right hn']
          · have hn' : n ≤ ns := by
              by_contra h; exact hiff ⟨fun h' => absurd h' h, fun h' => absurd h' hz⟩
            rw [ite_eq_right hz, ite_eq_left hn', abs_sub_comm]
        rw [habs]
        exact hm2.trans hbd
    have hpt := splice_pt (softNum CL CR p (Xs k) N n)
      (if n ≤ ns then CL.psiHatL p (Xs k) N n else softKappa CL CR p (Xs k) N * softSeqR CR p (Xs k) N n)
      (softNorm CL CR p (Xs k) N)
      (glueNormAt (CL.psiHatL p (Xs k) N) (softSeqR CR p (Xs k) N) (softWindow CL p (Xs k) N) (rowsOf N) ns)
      (Cn * ε) Cenv (Mc * ε) (softEnvNum CL CR p (Xs k) N n) hypos hN1pos hr1 hCnε hCenv (mul_nonneg hMc0 hε0) hEnum0 (E1 n hn) (hs.imp_left Eq.symm)
    have hvec : softVec CL CR p (Xs k) N n = softNum CL CR p (Xs k) N n / softNorm CL CR p (Xs k) N := softVec_eq CL CR _ _ _ _
    have hspl : splicedVec (CL.psiHatL p (Xs k) N) (softSeqR CR p (Xs k) N) (softWindow CL p (Xs k) N) (rowsOf N) ns n =
        (if n ≤ ns then CL.psiHatL p (Xs k) N n else softKappa CL CR p (Xs k) N * softSeqR CR p (Xs k) N n) /
          glueNormAt (CL.psiHatL p (Xs k) N) (softSeqR CR p (Xs k) N) (softWindow CL p (Xs k) N) (rowsOf N) ns := rfl
    have hse : softEnv CL CR p (Xs k) N n = softEnvNum CL CR p (Xs k) N n / softNorm CL CR p (Xs k) N := rfl
    rw [← hvec, ← hspl, ← hse] at hpt
    have hmid : (Mc * ε + 2 * (Cn * ε) * (Cenv + Mc * ε)) * softEnv CL CR p (Xs k) N n ≤
        (Mc + 2 * Cn * (Cenv + Mc)) * ε * softEnv CL CR p (Xs k) N n := by
      apply mul_le_mul_of_nonneg_right _ hEn0
      have hee : ε * ε ≤ ε := mul_le_of_le_one_left hε0 hε1
      have h2 : 0 ≤ 2 * Cn * Mc := by positivity
      have e1 : Mc * ε + 2 * (Cn * ε) * (Cenv + Mc * ε) = Mc * ε + 2 * Cn * Cenv * ε + 2 * Cn * Mc * (ε * ε) := by ring
      have e2 : (Mc + 2 * Cn * (Cenv + Mc)) * ε = Mc * ε + 2 * Cn * Cenv * ε + 2 * Cn * Mc * ε := by ring
      rw [e1, e2]
      linarith [mul_le_mul_of_nonneg_left hee h2]
    have hCc' : Cc * ε * softEnv CL CR p (Xs k) N n ≤ |Cc| * ε * softEnv CL CR p (Xs k) N n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hε0) hEn0
    have htri := abs_add_le (eigVec Um k n - softVec CL CR p (Xs k) N n)
      (softVec CL CR p (Xs k) N n - splicedVec (CL.psiHatL p (Xs k) N) (softSeqR CR p (Xs k) N) (softWindow CL p (Xs k) N) (rowsOf N) ns n)
    rw [show eigVec Um k n - softVec CL CR p (Xs k) N n + (softVec CL CR p (Xs k) N n -
      splicedVec (CL.psiHatL p (Xs k) N) (softSeqR CR p (Xs k) N) (softWindow CL p (Xs k) N) (rowsOf N) ns n) =
      eigVec Um k n - splicedVec (CL.psiHatL p (Xs k) N) (softSeqR CR p (Xs k) N) (softWindow CL p (Xs k) N) (rowsOf N) ns n by ring] at htri
    have hmax : Cv ≤ max (max Cn Cm) Cv := le_max_right _ _
    have hfin : Cv * ε * softEnv CL CR p (Xs k) N n ≤ max (max Cn Cm) Cv * ε * softEnv CL CR p (Xs k) N n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmax hε0) hEn0
    have hev : |Cc| * ε * softEnv CL CR p (Xs k) N n + (Mc + 2 * Cn * (Cenv + Mc)) * ε * softEnv CL CR p (Xs k) N n =
        Cv * ε * softEnv CL CR p (Xs k) N n := by rw [hCv]; ring
    have h1 := hrow n hn
    linarith [htri, hpt, hmid, hCc', hfin, hev, h1]

end Main

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.splice_pt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splice_pt

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.nearestRow_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nearestRow_close

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_split_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_split_agree

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.propThaSpliceSoft_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms propThaSpliceSoft_proved


end FormalResearch.JacobiEigenvectors.TheoremB

end
