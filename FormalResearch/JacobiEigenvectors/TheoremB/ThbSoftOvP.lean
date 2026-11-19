module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.SoftOverlap
public import FormalResearch.JacobiEigenvectors.TheoremB.SoftOverlapRight

/-!
# Paper J, Theorem B, L3.5c, part 8: `overlap_ub` of the soft charts with the equalities of the two orders only at the parameter `p`

Source: Paper J `app_thmB.tex`, (I4) for the soft half-collars.  `soft_overlap_ub` and `softJBChart_overlap_ub` (`SoftOverlap.lean`) take the equalities `zeta^{[m+1]} = zeta`, `mu^{[m+1]} = mu`, `u_c^{[m+1]} = u_c` as equalities of functions on all parameters;
`ChartPair` provides them for the left charts (`soft_up_eq`) but for the *mirror* charts only on `P` (from `SoftMirror` of both orders).  The proofs of `SoftOverlap.lean` only use them at the parameter `p`, so they are repeated here with pointwise hypotheses.

## Proved here

* `softChart_data_eq_P`, `soft_overlap_ub_P`, `softJBChart_overlap_ub_P`: the statements of `SoftOverlap.lean` with `(forall alpha x, zeta^{[m+1]} p alpha x = zeta p alpha x)`, etc. after `p in P`.

## Differences from the paper

None.  **Not formalised**: nothing.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section Eq

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}

theorem softChart_data_eq_P (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CL1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1))
    {p : Par × ℝ} (hz : ∀ α x, CL1.zeta p α x = CL.zeta p α x) (hmu : ∀ r α, CL1.muS r p α = CL.muS r p α) (huc : CL1.uc p = CL.uc p)
    (X : ℝ) (N : ℕ) :
    CL1.aOf p X N = CL.aOf p X N ∧ (∀ n, CL1.Zof p X N n = CL.Zof p X N n) ∧ softWindow CL1 p X N = softWindow CL p X N := by
  have ha : CL1.aOf p X N = CL.aOf p X N := by
    unfold SoftEdgeChart.aOf
    simp only [hmu]
  have hZ : ∀ n, CL1.Zof p X N n = CL.Zof p X N n := by
    intro n
    unfold SoftEdgeChart.Zof
    simp only [hz, huc]
  refine ⟨ha, hZ, ?_⟩
  unfold softWindow
  simp only [ha, hZ]

end Eq

section UB

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}

theorem soft_overlap_ub_P {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC)
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CL1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1))
    (hδ1 : CL1.δ0 = CL.δ0) :
    ∃ C4 h1 : ℝ, 0 ≤ C4 ∧ 0 < h1 ∧ ∀ p ∈ P, (∀ α x, CL1.zeta p α x = CL.zeta p α x) → (∀ r α, CL1.muS r p α = CL.muS r p α) →
      CL1.uc p = CL.uc p → ∀ N : ℕ, max CL.N0 CL1.N0 ≤ N → Fz.step N ≤ h1 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      CL.aOf p X N ≤ 1 →
      Real.sqrt (∑ j ∈ (softWindow CL p X N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)),
          ((CL.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 0) ^ 2) +
        Real.sqrt (∑ j ∈ (softWindow CL p X N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)),
          ((CL.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 1) ^ 2) ≤
      C4 * Real.sqrt (∑ j ∈ (softWindow CL p X N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)),
          ((CL1.chain p X N).phi (Fz.step N) 0 2 j) ^ 2) := by
  obtain ⟨c, h0, hc, hh0, Hf⟩ := soft_flat1_phi hf CL1
  have hCPC : 0 < CPC := lt_of_lt_of_le hf.cPC_pos hf.cPC_le
  have hB : 0 < winCB CPC 1 := by unfold winCB; positivity
  have hΛ := winCLam_nonneg CL
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  refine ⟨winCB CPC 1 * (1 + winCLam CL) / Real.sqrt c, min h0 (asmH0 CL), by positivity, lt_min hh0 (by
    unfold asmH0; exact lt_min (winH1_pos CL) (farThr_pos CL)), ?_⟩
  intro p hp hz hmu huc N hN hstep X hX ha
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hN1' : CL1.N0 ≤ N := (le_max_right _ _).trans hN
  have s0 : Fz.step N ≤ h0 := hstep.trans (min_le_left _ _)
  have sA : Fz.step N ≤ asmH0 CL := hstep.trans (min_le_right _ _)
  have hs1 : Fz.step N ≤ winH1 CL := sA.trans (min_le_left _ _)
  obtain ⟨hA1, hZ1, hW1⟩ := softChart_data_eq_P CL CL1 hz hmu huc X N
  have hX1 : |X - Fz.bandHi p| ≤ CL1.δ0 := by rw [hδ1]; exact hX
  -- lower bound for the `phi^{[m+1]}` mass
  have hflat := Hf p hp X hX1 N hN1' s0 (by rw [hA1]; exact ha)
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

/-- **`overlap_ub` of the soft charts** (chart rows, `P_k` the rows over the half-window `S_k`; needs the chart to cover `S_k`): see `soft_overlap_ub`. -/
theorem softJBChart_overlap_ub_P {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC)
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CL1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1))
    (hδ1 : CL1.δ0 = CL.δ0) :
    ∃ C4 h1 : ℝ, 0 ≤ C4 ∧ 0 < h1 ∧ ∀ p ∈ P, (∀ α x, CL1.zeta p α x = CL.zeta p α x) → (∀ r α, CL1.muS r p α = CL.muS r p α) →
      CL1.uc p = CL.uc p → ∀ N : ℕ, max CL.N0 CL1.N0 ≤ N → Fz.step N ≤ h1 →
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
  obtain ⟨C4, h1, hC4, hh1, H⟩ := soft_overlap_ub_P hf CL CL1 hδ1
  refine ⟨C4, h1, hC4, hh1, ?_⟩
  intro p hp hz hmu huc N hN hstep TI Xc cols lo R hlo τ used σ0 σ1 host0 host1 hX ha hsame hcov k
  have h := H p hp hz hmu huc N hN hstep (Xc k) (hX k) (ha k)
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

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.softJBChart_overlap_ub_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.softJBChart_overlap_ub_P

end FormalResearch.JacobiEigenvectors.TheoremB

end
