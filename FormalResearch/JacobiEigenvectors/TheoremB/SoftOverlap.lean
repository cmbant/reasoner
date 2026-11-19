module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.SoftExtRow
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftMflat2

/-!
# Paper J, Theorem B, L3.5b (soft halves), part 6: the overlap bound `overlap_ub` (I4, upper) of the soft charts

Source: Paper J `app_thmB.tex`, (I4) for the soft half-collars: `||P y|| + ||P y~|| <= C ||P phi^{[m+1]}||` on the half-window `P = Omega cap {n <= n_c}`.

## Proved here

* `softChart_data_eq`: two soft charts with the same `zeta`, `muS`, `u_c` (orders `m`, `m+1`, `ChartPair.soft_up_eq`) have the same `a`, `Z_n`, window and fold row.
* `softPk`, `sum_chart_rows`, `softJBChart_phi1`, `softJBChart_overlap_ub`: the same for the chart rows `P_k = softPk` (the chart rows whose chain row lies in the half-window; the chart must cover it).
* `eigVec_row`, `softJBChart_overlap_lb_left`: `overlap_lb` of the left half at the chart rows `P_k` (`Xc = Xs`).
* `soft_window_eig_lower` (`overlap_lb`, chain level, left half): at an eigenvalue near the edge with `a <= 1` and Step 0, `c_0 <= sqrt(sum_{S} Psi_{k,j}^2)`, `S = Omega cap {n <= n_c}` (route in its docstring).
* `soft_overlap_ub`: at chain level (any soft chart, so also the mirror and negated ones): with `S = Omega cap {n <= n_c}`,
  `sqrt(sum_S y^2) + sqrt(sum_S y~^2) <= C_4 sqrt(sum_S (phi^{[m+1]})^2)`.  Upper: `|y| <= C_B M_bal`, `|y~| <= C_B C_Lambda M_bal` on the window (`wm_env_two`, `wm_rowfacts`), so `<= C_B (1 + C_Lambda) sqrt(m_Omega)`;
  lower: `sum_S phi^2 >= c m_Omega` (`lem:tha-Mflat` flat1 for the order-`(m+1)` chart, `propThaMflat_proved`).

## Differences from the paper

None of substance (`P_k` is the half-window `Omega_-`, the same for every column).

## Not formalised here

`overlap_lb` for the **right** half (the same with the mirror chart: needs `|hat kappa lambda_R| >= c |lambda_L|`, the identification of the global half-window `{i > n_c}` with the mirror half-window `{j <= n_c^R}` (`Zof_mirror`; `n_c^R = N - n_c` or `N - n_c + 1`), and flat1 for the mirror chart), the lower soft edge.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section Eq

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}

theorem softChart_data_eq (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CL1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1))
    (hz : CL1.zeta = CL.zeta) (hmu : CL1.muS = CL.muS) (huc : CL1.uc = CL.uc) (p : Par × ℝ) (X : ℝ) (N : ℕ) :
    CL1.aOf p X N = CL.aOf p X N ∧ (∀ n, CL1.Zof p X N n = CL.Zof p X N n) ∧ softWindow CL1 p X N = softWindow CL p X N := by
  have ha : CL1.aOf p X N = CL.aOf p X N := by
    unfold SoftEdgeChart.aOf
    rw [hmu]
  have hZ : ∀ n, CL1.Zof p X N n = CL.Zof p X N n := by
    intro n
    unfold SoftEdgeChart.Zof
    rw [hz, huc]
  refine ⟨ha, hZ, ?_⟩
  unfold softWindow
  simp only [ha, hZ]

end Eq

section UB

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}

theorem soft_overlap_ub {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC)
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CL1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1))
    (CR1 : SoftEdgeChart (mirrorFamily Fz) P (m + 1) q U V (fun _ => 1)) (hM1 : SoftMirror CL1 CR1)
    (hz : CL1.zeta = CL.zeta) (hmu : CL1.muS = CL.muS) (huc : CL1.uc = CL.uc) (hδ1 : CL1.δ0 = CL.δ0)
    (r : ℕ) (hr : StdAssump Fz P (q / 2) r) :
    ∃ C4 h1 : ℝ, 0 ≤ C4 ∧ 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max (max CL.N0 CL1.N0) CR1.N0 ≤ N → Fz.step N ≤ h1 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      CL.aOf p X N ≤ 1 →
      Real.sqrt (∑ j ∈ (softWindow CL p X N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)),
          ((CL.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 0) ^ 2) +
        Real.sqrt (∑ j ∈ (softWindow CL p X N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)),
          ((CL.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 1) ^ 2) ≤
      C4 * Real.sqrt (∑ j ∈ (softWindow CL p X N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)),
          ((CL1.chain p X N).phi (Fz.step N) 0 2 j) ^ 2) := by
  obtain ⟨c, C, h0, hc, hh0, Hf⟩ := propThaMflat_proved (cPC := cPC) (CPC := CPC) CL1 CR1 hf (by omega) hM1 r hr
  have hCPC : 0 < CPC := lt_of_lt_of_le hf.cPC_pos hf.cPC_le
  have hB : 0 < winCB CPC 1 := by unfold winCB; positivity
  have hΛ := winCLam_nonneg CL
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  refine ⟨winCB CPC 1 * (1 + winCLam CL) / Real.sqrt c, min h0 (asmH0 CL), by positivity, lt_min hh0 (by
    unfold asmH0; exact lt_min (winH1_pos CL) (farThr_pos CL)), ?_⟩
  intro p hp N hN hstep X hX ha
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN1' : CL1.N0 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : CR1.N0 ≤ N := (le_max_right _ _).trans hN
  have s0 : Fz.step N ≤ h0 := hstep.trans (min_le_left _ _)
  have sA : Fz.step N ≤ asmH0 CL := hstep.trans (min_le_right _ _)
  have hs1 : Fz.step N ≤ winH1 CL := sA.trans (min_le_left _ _)
  obtain ⟨hA1, hZ1, hW1⟩ := softChart_data_eq CL CL1 hz hmu huc p X N
  have hX1 : |X - Fz.bandHi p| ≤ CL1.δ0 := by rw [hδ1]; exact hX
  have hN12 : max CL1.N0 CR1.N0 ≤ N := max_le hN1' hN2
  -- lower bound for the `phi^{[m+1]}` mass
  have hflat := (Hf p hp X hX1 N hN12 s0 (by rw [hA1]; exact ha)).2.2.2.1
  set S := (softWindow CL p X N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)) with hS
  have hκ := kappaBal_pos (CL.aOf p X N)
  have hi : 0 < (kappaBal (CL.aOf p X N))⁻¹ ^ 2 := by positivity
  have hlow : c * wmMass CL p X N ≤ ∑ j ∈ S, ((CL1.chain p X N).phi (Fz.step N) 0 2 j) ^ 2 := by
    have e : (softWindow CL1 p X N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL1.uc p)) = S := by
      rw [hW1, huc]
    have e2 : ∑ n ∈ S, ((CL1.chain p X N).phi (Fz.step N) 0 2 n / kappaBal (CL.aOf p X N)) ^ 2 =
        (kappaBal (CL.aOf p X N))⁻¹ ^ 2 * ∑ n ∈ S, ((CL1.chain p X N).phi (Fz.step N) 0 2 n) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [div_eq_inv_mul, mul_pow]
    have hW : ∑ n ∈ softWindow CL1 p X N, Mbal (CL1.aOf p X N) (CL1.Zof p X N n) ^ 2 = wmMass CL p X N := by
      unfold wmMass
      rw [hW1, hA1]
      exact Finset.sum_congr rfl (fun n _ => by rw [hZ1])
    rw [e, hW, hA1, e2] at hflat
    have key : c * (kappaBal (CL.aOf p X N))⁻¹ ^ 2 * wmMass CL p X N = (kappaBal (CL.aOf p X N))⁻¹ ^ 2 * (c * wmMass CL p X N) := by ring
    rw [key] at hflat
    exact le_of_mul_le_mul_left hflat hi
  -- upper bounds
  have hrow : ∀ j ∈ S, |(CL.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 0| ≤ winCB CPC 1 * Mbal (CL.aOf p X N) (CL.Zof p X N j) ∧
      |(CL.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 1| ≤ winCB CPC 1 * winCLam CL * Mbal (CL.aOf p X N) (CL.Zof p X N j) := by
    intro j hj
    have hjΩ := (Finset.mem_filter.mp hj).1
    have hcol := soft_win_loc CL hp hX sA hjΩ
    obtain ⟨hj0, hjN, hZ, hj1, hNR, hc2, hkz⟩ := wm_rowfacts CL hp hX hN1 hs1 hjΩ hcol
    have hj2' : j ≤ (CL.chain p X N).NR + 1 := by omega
    have hw := CL.wf2_eq p hp X hX N hN1 j (Finset.mem_Icc.mpr ⟨hj1.le, hj2'⟩)
    obtain ⟨-, ⟨e1, e2⟩⟩ := wm_env_two hf 1 (CL.aOf p X N) ha (CL.Zof p X N j) hZ
    have hh0' : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
    have hM0 := Mbal_nonneg' (CL.aOf p X N) (CL.Zof p X N j)
    constructor
    · have h0 : (CL.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 0 =
          kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-(CL.Zof p X N j)) := by
        rw [hw 0]
        simp [wm_pcMinus0, SoftEdgeChart.aOf, SoftEdgeChart.Zof]
      rw [h0]; exact e1
    · have h1 : (CL.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 1 =
          Real.sqrt (Fz.step N) * deriv (fun w => kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-w)) (CL.Zof p X N j) := by
        rw [hw 0]
        simp [wm_pcMinus0, SoftEdgeChart.aOf, SoftEdgeChart.Zof]
      rw [h1, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hsk : Real.sqrt (Fz.step N) * Real.sqrt (k2 (CL.aOf p X N) (CL.Zof p X N j)) ≤ winCLam CL := by
        rw [← Real.sqrt_mul hh0'.le]
        exact Real.sqrt_le_iff.mpr ⟨hΛ, hkz⟩
      calc Real.sqrt (Fz.step N) * |deriv (fun w => kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-w)) (CL.Zof p X N j)|
          ≤ Real.sqrt (Fz.step N) * (winCB CPC 1 * Real.sqrt (k2 (CL.aOf p X N) (CL.Zof p X N j)) * Mbal (CL.aOf p X N) (CL.Zof p X N j)) :=
            mul_le_mul_of_nonneg_left e2 (Real.sqrt_nonneg _)
        _ = (Real.sqrt (Fz.step N) * Real.sqrt (k2 (CL.aOf p X N) (CL.Zof p X N j))) * (winCB CPC 1 * Mbal (CL.aOf p X N) (CL.Zof p X N j)) := by ring
        _ ≤ winCLam CL * (winCB CPC 1 * Mbal (CL.aOf p X N) (CL.Zof p X N j)) :=
            mul_le_mul_of_nonneg_right hsk (by positivity)
        _ = winCB CPC 1 * winCLam CL * Mbal (CL.aOf p X N) (CL.Zof p X N j) := by ring
  have hsub : ∑ j ∈ S, Mbal (CL.aOf p X N) (CL.Zof p X N j) ^ 2 ≤ wmMass CL p X N := by
    unfold wmMass
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  have hy : Real.sqrt (∑ j ∈ S, ((CL.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 0) ^ 2) ≤
      winCB CPC 1 * Real.sqrt (wmMass CL p X N) := by
    rw [← Real.sqrt_sq hB.le, ← Real.sqrt_mul (sq_nonneg _)]
    apply Real.sqrt_le_sqrt
    calc ∑ j ∈ S, ((CL.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 0) ^ 2
        ≤ ∑ j ∈ S, (winCB CPC 1) ^ 2 * Mbal (CL.aOf p X N) (CL.Zof p X N j) ^ 2 := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          have := (hrow j hj).1
          rw [← mul_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2 |>.trans' (by rw [sq_abs])
      _ = (winCB CPC 1) ^ 2 * ∑ j ∈ S, Mbal (CL.aOf p X N) (CL.Zof p X N j) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (winCB CPC 1) ^ 2 * wmMass CL p X N := mul_le_mul_of_nonneg_left hsub (sq_nonneg _)
  have hyt : Real.sqrt (∑ j ∈ S, ((CL.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 1) ^ 2) ≤
      winCB CPC 1 * winCLam CL * Real.sqrt (wmMass CL p X N) := by
    have hBL : 0 ≤ winCB CPC 1 * winCLam CL := by positivity
    rw [← Real.sqrt_sq hBL, ← Real.sqrt_mul (sq_nonneg _)]
    apply Real.sqrt_le_sqrt
    calc ∑ j ∈ S, ((CL.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 1) ^ 2
        ≤ ∑ j ∈ S, (winCB CPC 1 * winCLam CL) ^ 2 * Mbal (CL.aOf p X N) (CL.Zof p X N j) ^ 2 := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          have := (hrow j hj).2
          rw [← mul_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2 |>.trans' (by rw [sq_abs])
      _ = (winCB CPC 1 * winCLam CL) ^ 2 * ∑ j ∈ S, Mbal (CL.aOf p X N) (CL.Zof p X N j) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (winCB CPC 1 * winCLam CL) ^ 2 * wmMass CL p X N := mul_le_mul_of_nonneg_left hsub (sq_nonneg _)
  have hΦ : Real.sqrt c * Real.sqrt (wmMass CL p X N) ≤ Real.sqrt (∑ j ∈ S, ((CL1.chain p X N).phi (Fz.step N) 0 2 j) ^ 2) := by
    rw [← Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt hlow
  have hM0 : 0 ≤ Real.sqrt (wmMass CL p X N) := Real.sqrt_nonneg _
  calc _ ≤ winCB CPC 1 * Real.sqrt (wmMass CL p X N) + winCB CPC 1 * winCLam CL * Real.sqrt (wmMass CL p X N) := add_le_add hy hyt
    _ = winCB CPC 1 * (1 + winCLam CL) / Real.sqrt c * (Real.sqrt c * Real.sqrt (wmMass CL p X N)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hΦ (by positivity)

end UB

section Chart

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Jlo Jhi : (Par × ℝ) → ℝ} {ulo uhi : (Par × ℝ) → ℝ}

theorem chartRowDn_injective (N lo R : ℕ) (τ : Bool) : Function.Injective (chartRowDn N lo R τ) := by
  intro n n' h
  apply Fin.ext
  cases τ <;> simp only [chartRowDn, Bool.false_eq_true, ite_false, ite_true] at h <;> omega

/-- The chart rows whose chain row lies in the set `S` of chain rows (the half-window): the overlap window `P_k` of a soft chart. -/
def softPk (N lo R : ℕ) (τ : Bool) (S : Finset ℤ) : Finset (Fin R) :=
  Finset.univ.filter fun n => chartRowDn N lo R τ n ∈ S

theorem sum_chart_rows {R : ℕ} (rowf : Fin R → ℤ) (hinj : Function.Injective rowf) (S : Finset ℤ) (hcov : ∀ j ∈ S, ∃ n, rowf n = j)
    (f : ℤ → ℝ) :
    ∑ n ∈ (Finset.univ : Finset (Fin R)).filter (fun n => rowf n ∈ S), f (rowf n) = ∑ j ∈ S, f j := by
  have himg : ((Finset.univ : Finset (Fin R)).filter (fun n => rowf n ∈ S)).image rowf = S := by
    ext j
    constructor
    · intro hj
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj
      exact (Finset.mem_filter.mp hn).2
    · intro hj
      obtain ⟨n, hn⟩ := hcov j hj
      exact Finset.mem_image.mpr ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hn]; exact hj⟩, hn⟩
  rw [← himg, Finset.sum_image (fun a _ b _ h => hinj h)]
  rw [himg]

/-- The chart profile of order `m + 1` is the corrected comparison sequence of the order-`(m+1)` chart (the model pair is the one of `C`: `same_ladder`). -/
theorem softJBChart_phi1 (C : SoftEdgeChart Fz P m q U V (fun _ => 1)) (C1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1))
    (TI : TransferInputsDn Fz P Jlo Jhi m C.chain C1.chain 2 ulo uhi)
    (p : Par × ℝ) (N : ℕ) (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (lo R : ℕ) (hlo : lo + R ≤ N + 1) (τ : Bool)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 σ1 : cols → ℝ)
    (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (n : Fin R) (k : cols)
    (hw : (C.chain p (Xc k) N).wf 2 = (C1.chain p (Xc k) N).wf 2) :
    (softJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).phi1 (Fz.step N) n k =
      (C1.chain p (Xc k) N).phi (Fz.step N) 0 2 (chartRowDn N lo R τ n) := by
  simp only [FormalResearch.JB.Chart.phi1_apply, softJBChart, Matrix.of_apply]
  unfold LadderData.phi ladderSeq vrow dot uNode
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hw' := congrFun hw 0
  rw [← hw']
  ring

/-- **`overlap_ub` of the soft charts** (chart rows, `P_k` the rows over the half-window `S_k`; needs the chart to cover `S_k`): see `soft_overlap_ub`. -/
theorem softJBChart_overlap_ub {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC)
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CL1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1))
    (CR1 : SoftEdgeChart (mirrorFamily Fz) P (m + 1) q U V (fun _ => 1)) (hM1 : SoftMirror CL1 CR1)
    (hz : CL1.zeta = CL.zeta) (hmu : CL1.muS = CL.muS) (huc : CL1.uc = CL.uc) (hδ1 : CL1.δ0 = CL.δ0)
    (r : ℕ) (hr : StdAssump Fz P (q / 2) r) :
    ∃ C4 h1 : ℝ, 0 ≤ C4 ∧ 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max (max CL.N0 CL1.N0) CR1.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ (TI : TransferInputsDn Fz P Jlo Jhi m CL.chain CL1.chain 2 ulo uhi) (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (lo R : ℕ)
        (hlo : lo + R ≤ N + 1) (τ : Bool) (used : Finset (Fin R)) (σ0 σ1 : cols → ℝ) (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
      (∀ k : cols, |Xc k - Fz.bandHi p| ≤ CL.δ0) → (∀ k : cols, CL.aOf p (Xc k) N ≤ 1) →
      (∀ k : cols, (CL.chain p (Xc k) N).wf 2 = (CL1.chain p (Xc k) N).wf 2) →
      (∀ k : cols, ∀ j ∈ (softWindow CL p (Xc k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)),
        ∃ n : Fin R, chartRowDn N lo R τ n = j) →
      ∀ k : cols,
        FormalResearch.JB.jbL2 (softPk N lo R τ ((softWindow CL p (Xc k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p))))
            (fun n => (softJBChart CL CL1 TI p N Xc cols lo R hlo τ used
              (fun k => softPk N lo R τ ((softWindow CL p (Xc k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)))) σ0 σ1 host0 host1).y n k) +
          FormalResearch.JB.jbL2 (softPk N lo R τ ((softWindow CL p (Xc k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p))))
            (fun n => (softJBChart CL CL1 TI p N Xc cols lo R hlo τ used
              (fun k => softPk N lo R τ ((softWindow CL p (Xc k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)))) σ0 σ1 host0 host1).yt n k) ≤
          C4 * FormalResearch.JB.jbL2 (softPk N lo R τ ((softWindow CL p (Xc k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p))))
            (fun n => (softJBChart CL CL1 TI p N Xc cols lo R hlo τ used
              (fun k => softPk N lo R τ ((softWindow CL p (Xc k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)))) σ0 σ1 host0 host1).phi1 (Fz.step N) n k) := by
  obtain ⟨C4, h1, hC4, hh1, H⟩ := soft_overlap_ub hf CL CL1 CR1 hM1 hz hmu huc hδ1 r hr
  refine ⟨C4, h1, hC4, hh1, ?_⟩
  intro p hp N hN hstep TI Xc cols lo R hlo τ used σ0 σ1 host0 host1 hX ha hsame hcov k
  have h := H p hp N hN hstep (Xc k) (hX k) (ha k)
  set S := (softWindow CL p (Xc k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)) with hS
  have hcs := hcov k
  have hph : ∀ n : Fin R, (softJBChart CL CL1 TI p N Xc cols lo R hlo τ used
      (fun k => softPk N lo R τ ((softWindow CL p (Xc k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)))) σ0 σ1 host0 host1).phi1
        (Fz.step N) n k = (CL1.chain p (Xc k) N).phi (Fz.step N) 0 2 (chartRowDn N lo R τ n) :=
    fun n => softJBChart_phi1 CL CL1 TI p N Xc cols lo R hlo τ used _ σ0 σ1 host0 host1 n k (hsame k)
  unfold FormalResearch.JB.jbL2
  simp only [hph]
  simp only [softJBChart, Matrix.of_apply]
  have e1 := sum_chart_rows (chartRowDn N lo R τ) (chartRowDn_injective N lo R τ) S hcs
    (fun j => ((CL.chain p (Xc k) N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 0) ^ 2)
  have e2 := sum_chart_rows (chartRowDn N lo R τ) (chartRowDn_injective N lo R τ) S hcs
    (fun j => ((CL.chain p (Xc k) N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 1) ^ 2)
  have e3 := sum_chart_rows (chartRowDn N lo R τ) (chartRowDn_injective N lo R τ) S hcs
    (fun j => ((CL1.chain p (Xc k) N).phi (Fz.step N) 0 2 j) ^ 2)
  beta_reduce at e1 e2 e3
  unfold softPk
  rw [e1, e2, e3]
  exact h

end Chart

section LB

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}

lemma sqrt_sum_le_env (S Ω : Finset ℤ) (hSΩ : S ⊆ Ω) (f M : ℤ → ℝ) {B : ℝ} (hB : 0 ≤ B) (h : ∀ j ∈ S, |f j| ≤ B * M j) :
    Real.sqrt (∑ j ∈ S, f j ^ 2) ≤ B * Real.sqrt (∑ j ∈ Ω, M j ^ 2) := by
  rw [← Real.sqrt_sq hB, ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  calc ∑ j ∈ S, f j ^ 2 ≤ ∑ j ∈ S, B ^ 2 * M j ^ 2 := Finset.sum_le_sum (fun j hj => by
          have := h j hj
          calc f j ^ 2 = |f j| ^ 2 := (sq_abs _).symm
            _ ≤ (B * M j) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
            _ = B ^ 2 * M j ^ 2 := by ring)
    _ = B ^ 2 * ∑ j ∈ S, M j ^ 2 := by rw [Finset.mul_sum]
    _ ≤ B ^ 2 * ∑ j ∈ Ω, M j ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hSΩ (fun _ _ _ => sq_nonneg _)) (sq_nonneg _)

set_option maxHeartbeats 4000000 in
/-- **The eigenvector mass on the left half-window** (`overlap_lb`, (I4) lower, chain level): at an eigenvalue `X_k` near the edge with `a <= 1` (and Step 0),
`c_0 <= sqrt(sum_{S} Psi_{k,j}^2)` for `S = Omega cap {n <= n_c}`.  Route: `Psi = hat Psi + O(h^m env)` (`soft_eigen_main`), `hat Psi = hat psi^L/hat N` on `S` up to `C_m h^m T M_bal / hat N` (window matching of `soft_splice_facts`),
`sum_S (psi-hat^L)^2 = T^2 sum_S phi^2 >= c T^2 m_Omega` (flat1), `c_n T^2 h^{-1/2} <= hat N^2 <= D T^2 h^{-1/2}` (`soft_splice_facts`, `softNorm_sq`, `soft_env_sum`), `c_M h^{-1/2} <= m_Omega` (`soft_win_massw`). -/
theorem soft_window_eig_lower {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC)
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1))
    (hM : SoftMirror CL CR) (hm : 1 ≤ m) (r : ℕ) (hr : StdAssump Fz P (q / 2) r) (Cs0 : ℝ) :
    ∃ c0 h1 : ℝ, 0 < c0 ∧ 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        (∀ i, Xs i ≤ Fz.bandHi p + Cs0 * Fz.step N ^ 2) → ∀ k : Fin (N + 1), |Xs k - Fz.bandHi p| ≤ CL.δ0 → CL.aOf p (Xs k) N ≤ 1 →
          c0 ≤ Real.sqrt (∑ j ∈ (softWindow CL p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)), (eigVec Um k j) ^ 2) := by
  have hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ (fun _ : ℝ => (1 : ℝ)) h := fun _ _ _ => le_rfl
  obtain ⟨Cc, he0, he0p, He⟩ := soft_eigen_main CL CR hM hf hm hLm Cs0
  obtain ⟨Cenv, Cm, K, CM, cn, clb, hs0, hCenv, hCm, hK, hCM, hcn, hclb, hs0p, Hs⟩ := soft_splice_facts CL CR hM hf hm hLm
  obtain ⟨Ck, hk0, hCk, hk0p, Hk⟩ := soft_kappa_bound CL CR hM hf
  obtain ⟨C0, C1, he1, he1p, hC0, hC1, Hv⟩ := soft_env_sum CL CR hM hf hm hLm 1
  obtain ⟨cM, CM', hw0, hcM, hw0p, HW⟩ := soft_win_massw CL hf 1
  obtain ⟨cf, Cf, hf0, hcf, hf0p, Hf⟩ := propThaMflat_proved (cPC := cPC) (CPC := CPC) CL CR hf hm hM r hr
  have hηe : CR.η = CL.η := hM.2.2.2.1
  have hN0 : CR.N0 = CL.N0 := hM.2.2.2.2.2
  have hη := CL.consts_pos.2.1
  set D1 : ℝ := Cenv ^ 2 * (C0 + C1 * Ck ^ 2) + 1 with hD1
  have hD1p : 0 < D1 := by positivity
  set c1 : ℝ := Real.sqrt (cf * cM / D1) with hc1
  have hc1p : 0 < c1 := Real.sqrt_pos.mpr (by positivity)
  set Cc' : ℝ := max Cc 0 with hCc'
  have hCc'0 : 0 ≤ Cc' := le_max_right _ _
  set CM'' : ℝ := max CM' 0 with hCM''
  have hCM''0 : 0 ≤ CM'' := le_max_right _ _
  set E : ℝ := Cm * Real.sqrt (CM'' / cn) + Cc' * Real.sqrt Cc' with hE
  have hE0 : 0 ≤ E := by positivity
  refine ⟨c1 / 2, min (min (min (min he0 hs0) (min he1 (min hw0 hk0))) (min hf0 (min CL.softH1 (min CR.softH1 (min (CL.η / 2) (min (winH1 CL) (min (asmH0 CL) (min CR.η 1)))))))) (c1 / (2 * (E + 1))),
    by positivity, ?_, ?_⟩
  · refine lt_min (lt_min (lt_min (lt_min he0p hs0p) (lt_min he1p (lt_min hw0p hk0p))) (lt_min hf0p (lt_min CL.softH1_pos (lt_min CR.softH1_pos
      (lt_min (by linarith) (lt_min (winH1_pos CL) (lt_min (by unfold asmH0; exact lt_min (winH1_pos CL) (farThr_pos CL))
        (lt_min CR.consts_pos.2.1 one_pos)))))))) (by positivity)
  intro p hp N hN hstep Xs Um hE' hs0' k hX ha
  simp only [le_min_iff] at hstep
  obtain ⟨⟨⟨⟨sE, sS⟩, ⟨sV, sW, sK⟩⟩, ⟨sF, sH1, sH1R, sη2, sWin, sA, sηR, s1⟩⟩, sc⟩ := hstep
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hN2 : CR.N0 ≤ N := (le_max_right _ _).trans hN
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hsη : Fz.step N ≤ CL.η := by linarith
  obtain ⟨ψL, ψ', κ, hJL, hsL, hJR, hsR, hrel⟩ := eig_exact_data CL CR hM hp hN1 hN2 sH1 sH1R hsη sηR Xs Um hE' k hX
  obtain ⟨hTpos, hnum, hwc, -, -, hnorm, -⟩ := Hs p hp N hN sS (Xs k) hX ha ψL ψ' κ hJL hsL hJR hsR hrel
  obtain ⟨hEclose, hEsum⟩ := He p hp N hN sE Xs Um hE' hs0' k hX
  have hkb := Hk p hp N hN1 sK (Xs k) hX ha
  have hvs := Hv p hp N hN1 sV (Xs k) hX ha Ck hCk ψL ψ' hJL hsL hJR hsR hkb
  obtain ⟨hmL, hmU⟩ := HW p hp N hN1 sW (Xs k) hX ha
  have hflat := (Hf p hp (Xs k) hX N hN sF ha).2.2.2.1
  -- notation
  set w : ℝ := Fz.step N ^ (-(1 : ℝ) / 2) with hw
  have hwp : 0 < w := Real.rpow_pos_of_pos hh0 _
  set T : ℝ := |CL.lamL p (Xs k) N| / kappaBal (CL.aOf p (Xs k) N) with hT
  set Nh : ℝ := softNorm CL CR p (Xs k) N with hNh
  set S := (softWindow CL p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)) with hS
  set wm : ℝ := wmMass CL p (Xs k) N with hwm
  have hκ := kappaBal_pos (CL.aOf p (Xs k) N)
  have hNnn : 0 ≤ Nh := by rw [hNh]; unfold softNorm glueNorm; exact Real.sqrt_nonneg _
  have hT2p : 0 < T ^ 2 := pow_pos hTpos 2
  have hNlow : cn * (T ^ 2 * w) ≤ Nh ^ 2 := hnorm
  have hNpos : 0 < Nh := by
    by_contra hcon
    have h0 : Nh = 0 := le_antisymm (not_lt.mp hcon) hNnn
    rw [h0] at hNlow
    have : 0 < cn * (T ^ 2 * w) := mul_pos hcn (mul_pos hT2p hwp)
    linarith
  have hNup : Nh ^ 2 ≤ D1 * (T ^ 2 * w) := by
    rw [hNh, softNorm_sq]
    calc ∑ n ∈ rowsOf N, softNum CL CR p (Xs k) N n ^ 2
        ≤ ∑ n ∈ rowsOf N, (Cenv * softEnvNum CL CR p (Xs k) N n) ^ 2 := Finset.sum_le_sum (fun n hn => by
          have := hnum n hn
          calc softNum CL CR p (Xs k) N n ^ 2 = |softNum CL CR p (Xs k) N n| ^ 2 := (sq_abs _).symm
            _ ≤ (Cenv * softEnvNum CL CR p (Xs k) N n) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2)
      _ = Cenv ^ 2 * ∑ n ∈ rowsOf N, softEnvNum CL CR p (Xs k) N n ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
      _ ≤ Cenv ^ 2 * ((C0 + C1 * Ck ^ 2) * T ^ 2 * w) := mul_le_mul_of_nonneg_left hvs (sq_nonneg _)
      _ ≤ D1 * (T ^ 2 * w) := by
          have : 0 ≤ T ^ 2 * w := mul_nonneg (sq_nonneg _) hwp.le
          have h2 : 0 ≤ Cenv ^ 2 * (C0 + C1 * Ck ^ 2) := mul_nonneg (sq_nonneg _) (add_nonneg hC0 (mul_nonneg hC1 (sq_nonneg _)))
          nlinarith [mul_nonneg h2 this]
  -- the window rows are above `u_c - eta/2`
  have hSΩ : S ⊆ softWindow CL p (Xs k) N := Finset.filter_subset _ _
  have hSrows : S ⊆ rowsOf N := hSΩ.trans (Finset.filter_subset _ _)
  have hgt : ∀ j ∈ S, CL.uc p - CL.η / 2 < uNode (Fz.step N) j := by
    intro j hj
    have hcol := soft_win_loc CL hp hX sA (hSΩ hj)
    obtain ⟨hcl, -⟩ := abs_lt.mp hcol
    linarith
  -- (1) the profile mass
  have hpsiS : ∀ j ∈ S, CL.psiHatL p (Xs k) N j = CL.lamL p (Xs k) N * ((CL.chain p (Xs k) N).phi (Fz.step N) 0 2 j / kappaBal (CL.aOf p (Xs k) N)) :=
    fun j hj => psiHatL_of_gt CL p (Xs k) N (hgt j hj)
  have hmassψ : cf * T ^ 2 * wm ≤ ∑ j ∈ S, (CL.psiHatL p (Xs k) N j) ^ 2 := by
    have e : ∑ j ∈ S, (CL.psiHatL p (Xs k) N j) ^ 2 =
        |CL.lamL p (Xs k) N| ^ 2 * ∑ j ∈ S, ((CL.chain p (Xs k) N).phi (Fz.step N) 0 2 j / kappaBal (CL.aOf p (Xs k) N)) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [hpsiS j hj, mul_pow, sq_abs]
    rw [e]
    have hT' : T ^ 2 = |CL.lamL p (Xs k) N| ^ 2 * (kappaBal (CL.aOf p (Xs k) N))⁻¹ ^ 2 := by
      rw [hT, div_eq_mul_inv, mul_pow]
    calc cf * T ^ 2 * wm = |CL.lamL p (Xs k) N| ^ 2 * (cf * (kappaBal (CL.aOf p (Xs k) N))⁻¹ ^ 2 * wm) := by rw [hT']; ring
      _ ≤ |CL.lamL p (Xs k) N| ^ 2 * ∑ j ∈ S, ((CL.chain p (Xs k) N).phi (Fz.step N) 0 2 j / kappaBal (CL.aOf p (Xs k) N)) ^ 2 :=
          mul_le_mul_of_nonneg_left hflat (sq_nonneg _)
  -- (2) lower bound of the normalised profile
  have hA : c1 ≤ Real.sqrt (∑ j ∈ S, (CL.psiHatL p (Xs k) N j / Nh) ^ 2) := by
    rw [hc1]
    apply Real.sqrt_le_sqrt
    have e : ∑ j ∈ S, (CL.psiHatL p (Xs k) N j / Nh) ^ 2 = (∑ j ∈ S, (CL.psiHatL p (Xs k) N j) ^ 2) / Nh ^ 2 := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun j _ => by rw [div_pow])
    rw [e, div_le_div_iff₀ hD1p (pow_pos hNpos 2)]
    -- cf * cM * Nh^2 ≤ ... : use Nh^2 ≥ ? we need  cf*cM*Nh^2 ≤ D1 * (sum)  i.e.  (cf cM) (Nh^2) ≤ D1 * Σ ; Σ ≥ cf T^2 wm and Nh^2 ≤ D1 T^2 w
    have h5 : cf * cM * Nh ^ 2 ≤ D1 * (cf * T ^ 2 * wm) := by
      have hup := mul_le_mul_of_nonneg_left hNup (show 0 ≤ cf * cM from mul_nonneg hcf.le hcM.le)
      have hh : 0 ≤ cf * T ^ 2 := mul_nonneg hcf.le (sq_nonneg _)
      calc cf * cM * Nh ^ 2 ≤ cf * cM * (D1 * (T ^ 2 * w)) := hup
        _ = D1 * (cf * T ^ 2 * (cM * w)) := by ring
        _ ≤ D1 * (cf * T ^ 2 * wm) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmL hh) hD1p.le
    calc cf * cM * Nh ^ 2 ≤ D1 * (cf * T ^ 2 * wm) := h5
      _ ≤ D1 * (∑ j ∈ S, (CL.psiHatL p (Xs k) N j) ^ 2) := mul_le_mul_of_nonneg_left hmassψ hD1p.le
      _ = _ := by ring
  -- (3) window matching: `softVec ≈ ψ̂_L / N̂` on `S`
  have hwm0 : 0 ≤ wm := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh1 : Fz.step N ^ m ≤ Fz.step N := pow_le_of_le_one hh0.le s1 (by omega)
  have hhm0 : 0 ≤ Fz.step N ^ m := pow_nonneg hh0.le _
  have hB : Real.sqrt (∑ j ∈ S, (softVec CL CR p (Xs k) N j - CL.psiHatL p (Xs k) N j / Nh) ^ 2) ≤
      Cm * Fz.step N ^ m * Real.sqrt (CM'' / cn) := by
    have hrow : ∀ j ∈ S, |softVec CL CR p (Xs k) N j - CL.psiHatL p (Xs k) N j / Nh| ≤
        (Cm * Fz.step N ^ m * T / Nh) * Mbal (CL.aOf p (Xs k) N) (CL.Zof p (Xs k) N j) := by
      intro j hj
      have hd : |softNum CL CR p (Xs k) N j - CL.psiHatL p (Xs k) N j| ≤
          Cm * Fz.step N ^ m * T * Mbal (CL.aOf p (Xs k) N) (CL.Zof p (Xs k) N j) := by
        have hMb := Mbal_nonneg' (CL.aOf p (Xs k) N) (CL.Zof p (Xs k) N j)
        unfold softNum
        by_cases hz : CL.Zof p (Xs k) N j ≤ 0
        · simp only [hz, if_true, sub_self, abs_zero]
          have : 0 ≤ Cm * Fz.step N ^ m * T * Mbal (CL.aOf p (Xs k) N) (CL.Zof p (Xs k) N j) := by
            have := hTpos.le
            positivity
          exact this
        · simp only [hz, if_false]
          have h1 := hwc j (hSΩ hj)
          rw [abs_sub_comm]
          calc _ ≤ Cm * (Fz.step N ^ m * 1) * (T * Mbal (CL.aOf p (Xs k) N) (CL.Zof p (Xs k) N j)) := h1
            _ = _ := by ring
      rw [softVec_eq, ← sub_div, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
      calc _ ≤ Cm * Fz.step N ^ m * T * Mbal (CL.aOf p (Xs k) N) (CL.Zof p (Xs k) N j) := by
            have e : softNum CL CR p (Xs k) N j - CL.psiHatL p (Xs k) N j / Nh * Nh = softNum CL CR p (Xs k) N j - CL.psiHatL p (Xs k) N j := by
              rw [div_mul_cancel₀ _ hNpos.ne']
            rw [← hNh] at *
            exact hd
        _ = _ := by field_simp
    have hBnn : 0 ≤ Cm * Fz.step N ^ m * T / Nh := by
      have := hTpos.le
      positivity
    have h1 := sqrt_sum_le_env S (softWindow CL p (Xs k) N) hSΩ _ _ hBnn hrow
    refine h1.trans ?_
    have hwmdef : ∑ j ∈ softWindow CL p (Xs k) N, Mbal (CL.aOf p (Xs k) N) (CL.Zof p (Xs k) N j) ^ 2 = wm := rfl
    rw [hwmdef]
    have hx : T / Nh * Real.sqrt wm ≤ Real.sqrt (CM'' / cn) := by
      have hx0 : 0 ≤ T / Nh * Real.sqrt wm := by
        have := hTpos.le
        positivity
      rw [← Real.sqrt_sq hx0]
      apply Real.sqrt_le_sqrt
      rw [mul_pow, div_pow, Real.sq_sqrt hwm0, div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos hNpos 2) hcn]
      have hm1 : wm ≤ CM'' * w := hmU.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hwp.le)
      calc T ^ 2 * wm * cn ≤ T ^ 2 * (CM'' * w) * cn := by
            have := mul_le_mul_of_nonneg_left hm1 hT2p.le
            nlinarith [this, hcn]
        _ = CM'' * (cn * (T ^ 2 * w)) := by ring
        _ ≤ CM'' * Nh ^ 2 := mul_le_mul_of_nonneg_left hNlow hCM''0
    calc Cm * Fz.step N ^ m * T / Nh * Real.sqrt wm = Cm * Fz.step N ^ m * (T / Nh * Real.sqrt wm) := by ring
      _ ≤ Cm * Fz.step N ^ m * Real.sqrt (CM'' / cn) := mul_le_mul_of_nonneg_left hx (by positivity)
  -- (4) the eigenvector against `softVec`
  have hC : Real.sqrt (∑ j ∈ S, (eigVec Um k j - softVec CL CR p (Xs k) N j) ^ 2) ≤ Cc' * Fz.step N ^ m * Real.sqrt Cc' := by
    have hrow : ∀ j ∈ S, |eigVec Um k j - softVec CL CR p (Xs k) N j| ≤ (Cc' * Fz.step N ^ m) * softEnv CL CR p (Xs k) N j := by
      intro j hj
      have h1 := hEclose j (hSrows hj)
      have hen : 0 ≤ softEnv CL CR p (Xs k) N j := by
        rw [softEnv_eq]
        exact div_nonneg (softEnvNum_nonneg hf CL CR p (Xs k) N j) hNnn
      calc _ ≤ Cc * (Fz.step N ^ m * 1) * softEnv CL CR p (Xs k) N j := h1
        _ ≤ Cc' * Fz.step N ^ m * softEnv CL CR p (Xs k) N j := by
            have : Cc ≤ Cc' := le_max_left _ _
            have h2 : 0 ≤ Fz.step N ^ m * softEnv CL CR p (Xs k) N j := mul_nonneg hhm0 hen
            nlinarith [mul_le_mul_of_nonneg_right this h2]
    have h1 := sqrt_sum_le_env S (rowsOf N) hSrows _ _ (mul_nonneg hCc'0 hhm0) hrow
    refine h1.trans ?_
    have : Real.sqrt (∑ j ∈ rowsOf N, softEnv CL CR p (Xs k) N j ^ 2) ≤ Real.sqrt Cc' :=
      Real.sqrt_le_sqrt (hEsum.trans (le_max_left _ _))
    exact mul_le_mul_of_nonneg_left this (mul_nonneg hCc'0 hhm0)
  -- (5) conclusion
  have hmink := abs_sqrt_sub_le S (fun j => eigVec Um k j) (fun j => CL.psiHatL p (Xs k) N j / Nh)
  have hadd := sqrt_sum_add_le S (fun j => eigVec Um k j - softVec CL CR p (Xs k) N j)
    (fun j => softVec CL CR p (Xs k) N j - CL.psiHatL p (Xs k) N j / Nh)
  have e : ∀ j, (eigVec Um k j - softVec CL CR p (Xs k) N j) + (softVec CL CR p (Xs k) N j - CL.psiHatL p (Xs k) N j / Nh) =
      eigVec Um k j - CL.psiHatL p (Xs k) N j / Nh := fun j => by ring
  simp only [e] at hadd
  have hEtot : Cc' * Fz.step N ^ m * Real.sqrt Cc' + Cm * Fz.step N ^ m * Real.sqrt (CM'' / cn) ≤ Fz.step N ^ m * E := by
    rw [hE]; ring_nf; exact le_refl _
  have hmE : Fz.step N ^ m * E ≤ c1 / 2 := by
    calc Fz.step N ^ m * E ≤ Fz.step N * E := mul_le_mul_of_nonneg_right hh1 hE0
      _ ≤ c1 / (2 * (E + 1)) * E := mul_le_mul_of_nonneg_right sc hE0
      _ ≤ c1 / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [hc1p]
  have habs := (abs_le.mp hmink).1
  have hupper := hadd
  linarith [hA, hB, hC, hEtot, hmE]

end LB

section LBChart

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Jlo Jhi : (Par × ℝ) → ℝ} {ulo uhi : (Par × ℝ) → ℝ}

theorem eigVec_row {N : ℕ} (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (k : Fin (N + 1)) (i : Fin (N + 1)) :
    eigVec Um k (i : ℤ) = Um i k := by
  unfold eigVec
  have : 0 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (N : ℤ) := ⟨by positivity, by have := i.isLt; omega⟩
  rw [dif_pos this]
  congr 1

set_option maxHeartbeats 1000000 in
/-- **`overlap_lb` of the left soft half, chart rows**: `||P_k Psi_k|| >= c_0` for `P_k = softPk` over the left half-window (chain rows = global rows, `tau = false`), at the eigenvalue columns `k` of the chart
(`Xc = Xs`); see `soft_window_eig_lower`. -/
theorem softJBChart_overlap_lb_left {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC)
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1))
    (CL1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1))
    (hM : SoftMirror CL CR) (hm : 1 ≤ m) (r : ℕ) (hr : StdAssump Fz P (q / 2) r) (Cs0 : ℝ) :
    ∃ c0 h1 : ℝ, 0 < c0 ∧ 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
      (∀ i, Xs i ≤ Fz.bandHi p + Cs0 * Fz.step N ^ 2) →
      ∀ (TI : TransferInputsDn Fz P Jlo Jhi m CL.chain CL1.chain 2 ulo uhi) (cols : Finset (Fin (N + 1))) (lo R : ℕ)
        (hlo : lo + R ≤ N + 1) (used : Finset (Fin R)) (σ0 σ1 : cols → ℝ) (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
      (∀ k : cols, |Xs k - Fz.bandHi p| ≤ CL.δ0) → (∀ k : cols, CL.aOf p (Xs k) N ≤ 1) →
      (∀ k : cols, ∀ j ∈ (softWindow CL p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)),
        ∃ n : Fin R, chartRowDn N lo R false n = j) →
      ∀ k : cols,
        c0 ≤ FormalResearch.JB.jbL2 (softPk N lo R false ((softWindow CL p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p))))
            (fun n => Um ((softJBChart CL CL1 TI p N Xs cols lo R hlo false used
              (fun k => softPk N lo R false ((softWindow CL p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)))) σ0 σ1 host0 host1).row n) k) := by
  obtain ⟨c0, h1, hc0, hh1, H⟩ := soft_window_eig_lower hf CL CR hM hm r hr Cs0
  refine ⟨c0, h1, hc0, hh1, ?_⟩
  intro p hp N hN hstep Xs Um hE hs0 TI cols lo R hlo used σ0 σ1 host0 host1 hX ha hcov k
  have h := H p hp N hN hstep Xs Um hE hs0 k (hX k) (ha k)
  refine h.trans (le_of_eq ?_)
  unfold FormalResearch.JB.jbL2
  congr 1
  set S := (softWindow CL p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)) with hS
  have e := sum_chart_rows (chartRowDn N lo R false) (chartRowDn_injective N lo R false) S (hcov k)
    (fun j => (eigVec Um k j) ^ 2)
  beta_reduce at e
  unfold softPk
  rw [← e]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hr1 : chartRowDn N lo R false n = ((FormalResearch.JB.Chart.row (softJBChart CL CL1 TI p N Xs cols lo R hlo false used
      (fun k => softPk N lo R false ((softWindow CL p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)))) σ0 σ1 host0 host1) n : Fin (N + 1)) : ℤ) := by
    simp [chartRowDn, FormalResearch.JB.Chart.row, softJBChart]
  simp only [hr1, eigVec_row]
  rfl

end LBChart

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.softJBChart_overlap_lb_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms softJBChart_overlap_lb_left

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_window_eig_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_window_eig_lower

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.softJBChart_overlap_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms softJBChart_overlap_ub

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_overlap_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_overlap_ub

end FormalResearch.JacobiEigenvectors.TheoremB

end
