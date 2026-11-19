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
* `soft_overlap_ub`: at chain level (any soft chart, so also the mirror and negated ones): with `S = Omega cap {n <= n_c}`,
  `sqrt(sum_S y^2) + sqrt(sum_S y~^2) <= C_4 sqrt(sum_S (phi^{[m+1]})^2)`.  Upper: `|y| <= C_B M_bal`, `|y~| <= C_B C_Lambda M_bal` on the window (`wm_env_two`, `wm_rowfacts`), so `<= C_B (1 + C_Lambda) sqrt(m_Omega)`;
  lower: `sum_S phi^2 >= c m_Omega` (`lem:tha-Mflat` flat1 for the order-`(m+1)` chart, `propThaMflat_proved`).

## Differences from the paper

None of substance (`P_k` is the half-window `Omega_-`, the same for every column).

## Not formalised here

`overlap_lb` (the eigenvector half-window mass: needs `N^2 <= C T^2 h^{-1/2}` from `softNorm_sq`, `soft_env_sum`, then `soft_eigen_main` and flat1 for `phi^{[m]}`; for the right half also `|hat kappa lambda_R| >= c |lambda_L|`), the lower soft edge.
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

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.softJBChart_overlap_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms softJBChart_overlap_ub

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_overlap_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_overlap_ub

end FormalResearch.JacobiEigenvectors.TheoremB

end
