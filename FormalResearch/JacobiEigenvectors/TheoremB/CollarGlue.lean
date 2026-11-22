module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftMflat
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAssembly4
public import FormalResearch.JacobiEigenvectors.TheoremA.WindowMass2
public import FormalResearch.JacobiEigenvectors.TheoremB.Statements

/-!
# Paper J, Theorem B, L3.4 (part 2): chart-level normalisation facts (no eigenvalue needed)

Source: Paper J `app_thmB.tex`, proof of `lem:tha-collar` (1), "`widehat N >= c |lambda_L| kappa_bal^{-1} h^{-1/4}`" and "`|hat kappa lambda_R| asymp |lambda_L|` (Step 4 (b))".

## Proved here

Both facts are statements about the comparison sequences of the two charts only, so they hold at every `X` with `|X - bandHi| <= delta_0`, `a <= 1` (the frozen `PropThaCollar` quantifies over such `X` without an eigen-system in its second to fourth conjuncts):
* `soft_norm_lb`: `c (|lam_L|/kappa_bal)^2 h^{-1/2} <= softNorm^2` (left half of the window: `PropThaM` third conjunct at the cut `s = 0`, `wmMass >= c h^{-1/2}`).
* `soft_kappa_bound`: `|hat kappa lam_R| <= C_k |lam_L|` (Cauchy-Schwarz for `hat kappa = <psi^L, psi^R>_Omega / ||psi^R||_Omega^2`, the upper bound `soft_win_psihat` for `psi-hat^L`, the lower bound `soft_win_mass` for the mirror chart, and the window reflection).

## Differences from the paper

The paper proves `|hat kappa lambda_R| asymp |lambda_L|` at an eigenvalue from the matching `psi^L = kappa psi^R`; only the upper bound (all that the collar estimate uses) is needed here, and it holds without an eigenvalue.

## Not formalised

The assembly of `PropThaCollar` (`Collar.lean`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section Glue

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1))

/-- **`hat N^2 >= c (|lam_L|/kappa_b)^2 h^{-1/2}`** at every `X` near the edge with `a <= 1` (left half of the window). -/
theorem soft_norm_lb {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (r : ℕ) (hr : StdAssump Fz P (q / 2) r) :
    ∃ c h0 : ℝ, 0 < c ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → CL.aOf p X N ≤ 1 →
      c * ((|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2)) ≤ softNorm CL CR p X N ^ 2 := by
  obtain ⟨cM, hM0, hcM, hM0p, HM⟩ := propThaM_of_facts (cPC := cPC) (CPC := CPC) CL 1 hf r hr
  obtain ⟨cW, CW, hW0, hcW, hW0p, HW⟩ := soft_win_massw CL hf 1
  refine ⟨cM * cW, min (min hM0 hW0) (asmH0 CL), mul_pos hcM hcW, lt_min (lt_min hM0p hW0p) (asmH0_pos CL), ?_⟩
  intro p hp N hN hstep X hX ha
  have sM : Fz.step N ≤ hM0 := (hstep.trans (min_le_left _ _)).trans (min_le_left _ _)
  have sW : Fz.step N ≤ hW0 := (hstep.trans (min_le_left _ _)).trans (min_le_right _ _)
  have sA : Fz.step N ≤ asmH0 CL := hstep.trans (min_le_right _ _)
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  obtain ⟨-, -, M3⟩ := HM p hp X hX N hN sM ha 0 (by
    rw [abs_zero]; exact add_nonneg (Real.sqrt_nonneg _) (div_nonneg (ell_nonneg' _) (by norm_num)))
  have hmass := (HW p hp N hN sW X hX ha).1
  have hκ := kappaBal_pos (CL.aOf p X N)
  set Ω := softWindow CL p X N with hΩ
  have hsub : Ω.filter (fun n => CL.Zof p X N n ≤ 0) ⊆ rowsOf N :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have h1 : ∑ n ∈ Ω.filter (fun n => CL.Zof p X N n ≤ 0), softNum CL CR p X N n ^ 2 ≤ softNorm CL CR p X N ^ 2 := by
    rw [softNorm_sq CL CR p X N]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => sq_nonneg _)
  have hrew : ∑ n ∈ Ω.filter (fun n => CL.Zof p X N n ≤ 0), softNum CL CR p X N n ^ 2 =
      CL.lamL p X N ^ 2 * ∑ n ∈ Ω.filter (fun n => CL.Zof p X N n ≤ 0),
        ((CL.chain p X N).phi (Fz.step N) 0 2 n / kappaBal (CL.aOf p X N)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    obtain ⟨hnΩ, hZ⟩ := Finset.mem_filter.mp hn
    have hcol := soft_win_loc CL hp hX sA hnΩ
    have hgt : CL.uc p - CL.η / 2 < uNode (Fz.step N) n := by
      have := (abs_lt.mp hcol).1
      have := CL.consts_pos.2.1
      linarith
    unfold softNum
    rw [if_pos hZ, psiHatL_of_gt CL p X N hgt]; ring
  rw [hrew] at h1
  have hl2 : (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 = CL.lamL p X N ^ 2 * (kappaBal (CL.aOf p X N))⁻¹ ^ 2 := by
    rw [div_pow, sq_abs]; field_simp
  have hmass' : cW * Fz.step N ^ (-(1 : ℝ) / 2) ≤ ∑ n ∈ Ω, Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2 := hmass
  have hl0 : 0 ≤ CL.lamL p X N ^ 2 := sq_nonneg _
  have hk0 : 0 ≤ (kappaBal (CL.aOf p X N))⁻¹ ^ 2 := sq_nonneg _
  calc cM * cW * ((|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2))
      = CL.lamL p X N ^ 2 * (cM * (kappaBal (CL.aOf p X N))⁻¹ ^ 2 * (cW * Fz.step N ^ (-(1 : ℝ) / 2))) := by rw [hl2]; ring
    _ ≤ CL.lamL p X N ^ 2 * (cM * (kappaBal (CL.aOf p X N))⁻¹ ^ 2 * ∑ n ∈ Ω, Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hl0
        exact mul_le_mul_of_nonneg_left hmass' (by positivity)
    _ ≤ CL.lamL p X N ^ 2 * ∑ n ∈ Ω.filter (fun n => CL.Zof p X N n ≤ 0),
          ((CL.chain p X N).phi (Fz.step N) 0 2 n / kappaBal (CL.aOf p X N)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hl0
        exact M3
    _ ≤ _ := h1

/-- **`|hat kappa lam_R| <= C_k |lam_L|`** at every `X` near the edge with `a <= 1`. -/
theorem soft_kappa_bound (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) :
    ∃ Ck h0 : ℝ, 0 ≤ Ck ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → CL.aOf p X N ≤ 1 →
      |softKappa CL CR p X N * CR.lamL p X N| ≤ Ck * |CL.lamL p X N| := by
  obtain ⟨K, hK0, HK⟩ := soft_win_psihat CL hf 1
  obtain ⟨c0, h0a, hc0, hh0a, H0⟩ := soft_win_mass CR hf 1
  obtain ⟨cW, CW, hW0, hcW, hW0p, HW⟩ := soft_win_massw CL hf 1
  refine ⟨K / Real.sqrt c0, min (min (min h0a hW0) (asmH0 CL)) (asmH0 CR),
    div_nonneg hK0 (Real.sqrt_nonneg _), lt_min (lt_min (lt_min hh0a hW0p) (asmH0_pos CL)) (asmH0_pos CR), ?_⟩
  intro p hp N hN hstep X hX ha
  have sa : Fz.step N ≤ h0a := ((hstep.trans (min_le_left _ _)).trans (min_le_left _ _)).trans (min_le_left _ _)
  have sW : Fz.step N ≤ hW0 := ((hstep.trans (min_le_left _ _)).trans (min_le_left _ _)).trans (min_le_right _ _)
  have sAL : Fz.step N ≤ asmH0 CL := (hstep.trans (min_le_left _ _)).trans (min_le_right _ _)
  have sAR : Fz.step N ≤ asmH0 CR := hstep.trans (min_le_right _ _)
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hN0 : CR.N0 = CL.N0 := hM.2.2.2.2.2
  have hδ : CR.δ0 = CL.δ0 := hM.2.2.2.2.1
  have hX' : |X - (mirrorFamily Fz).bandHi p| ≤ CR.δ0 := by rw [bandHi_mirror, hδ]; exact hX
  have haR : CR.aOf p X N ≤ 1 := by rw [aOf_mirror hM hp X N]; exact ha
  have hκ := kappaBal_pos (CL.aOf p X N)
  have hκR : kappaBal (CR.aOf p X N) = kappaBal (CL.aOf p X N) := by rw [aOf_mirror hM hp X N]
  set Ω := softWindow CL p X N with hΩ
  set ψL : ℤ → ℝ := CL.psiHatL p X N with hψL
  set ψR : ℤ → ℝ := softSeqR CR p X N with hψR
  set A : ℝ := ∑ n ∈ Ω, ψL n * ψR n with hA
  set B : ℝ := ∑ n ∈ Ω, ψR n ^ 2 with hB
  set S : ℝ := ∑ n ∈ Ω, ψL n ^ 2 with hS
  have hkap : softKappa CL CR p X N = A / B := rfl
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hCS : A ^ 2 ≤ S * B := Finset.sum_mul_sq_le_sq_mul_sq Ω ψL ψR
  have hk2B : (A / B) ^ 2 * B ≤ S := by
    by_cases hb : B = 0
    · rw [hb]; simpa using hS0
    · have hbp : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hb)
      have e : (A / B) ^ 2 * B = A ^ 2 / B := by field_simp
      rw [e, div_le_iff₀ hbp]
      linarith [hCS]
  -- lower bound for B (mirror window)
  have hBlow : c0 * (|CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * wmMass CL p X N ≤ B := by
    have h1 := H0 p hp N (by rw [hN0]; exact hN) (le_min sa sAR) X hX' haR
    rw [hκR, wmMass_mirror hM hp X N] at h1
    have hrefl : B = ∑ k ∈ softWindow CR p X N, (CR.psiHatL p X N k) ^ 2 :=
      sum_window_reflect hM hp X N (fun k => CR.psiHatL p X N k ^ 2)
    rw [hrefl]; exact h1
  -- upper bound for S
  have hSup : S ≤ K ^ 2 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * wmMass CL p X N := by
    have hpt : ∀ n ∈ Ω, ψL n ^ 2 ≤ K ^ 2 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2 := by
      intro n hn
      have h1 := HK p hp N hN sAL X hX ha n hn
      have hM0 := Mbal_nonneg' (CL.aOf p X N) (CL.Zof p X N n)
      rw [← sq_abs (ψL n)]
      calc |ψL n| ^ 2 ≤ (K * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) * Mbal (CL.aOf p X N) (CL.Zof p X N n)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = _ := by ring
    calc S ≤ ∑ n ∈ Ω, K ^ 2 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2 :=
          Finset.sum_le_sum hpt
      _ = K ^ 2 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * wmMass CL p X N := by
          unfold wmMass; rw [Finset.mul_sum]
  have hwm : 0 < wmMass CL p X N := by
    have := (HW p hp N hN sW X hX ha).1
    have hp0 : 0 < cW * Fz.step N ^ (-(1 : ℝ) / 2) := mul_pos hcW (Real.rpow_pos_of_pos hh0 _)
    linarith
  -- combine
  have hmain : (A / B) ^ 2 * (c0 * (|CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * wmMass CL p X N) ≤
      K ^ 2 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * wmMass CL p X N :=
    calc _ ≤ (A / B) ^ 2 * B := mul_le_mul_of_nonneg_left hBlow (sq_nonneg _)
      _ ≤ S := hk2B
      _ ≤ _ := hSup
  have hκ2 : 0 < (kappaBal (CL.aOf p X N))⁻¹ ^ 2 := by positivity
  have hmain2 : (A / B) ^ 2 * (c0 * CR.lamL p X N ^ 2) ≤ K ^ 2 * CL.lamL p X N ^ 2 := by
    have e1 : (|CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 = CR.lamL p X N ^ 2 * (kappaBal (CL.aOf p X N))⁻¹ ^ 2 := by
      rw [div_pow, sq_abs]; field_simp
    have e2 : (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 = CL.lamL p X N ^ 2 * (kappaBal (CL.aOf p X N))⁻¹ ^ 2 := by
      rw [div_pow, sq_abs]; field_simp
    rw [e1, e2] at hmain
    have hpos : 0 < (kappaBal (CL.aOf p X N))⁻¹ ^ 2 * wmMass CL p X N := mul_pos hκ2 hwm
    have : ((A / B) ^ 2 * (c0 * CR.lamL p X N ^ 2)) * ((kappaBal (CL.aOf p X N))⁻¹ ^ 2 * wmMass CL p X N) ≤
        (K ^ 2 * CL.lamL p X N ^ 2) * ((kappaBal (CL.aOf p X N))⁻¹ ^ 2 * wmMass CL p X N) := by
      nlinarith [hmain]
    exact le_of_mul_le_mul_right this hpos
  rw [hkap]
  have hsq : (A / B * CR.lamL p X N) ^ 2 ≤ (K / Real.sqrt c0 * |CL.lamL p X N|) ^ 2 := by
    have hc0s : Real.sqrt c0 ^ 2 = c0 := Real.sq_sqrt hc0.le
    have hc0p : 0 < Real.sqrt c0 := Real.sqrt_pos.mpr hc0
    have e : (K / Real.sqrt c0 * |CL.lamL p X N|) ^ 2 = K ^ 2 * CL.lamL p X N ^ 2 / c0 := by
      rw [mul_pow, div_pow, sq_abs, hc0s]; ring
    rw [e, mul_pow, le_div_iff₀ hc0]
    calc (A / B) ^ 2 * CR.lamL p X N ^ 2 * c0 = (A / B) ^ 2 * (c0 * CR.lamL p X N ^ 2) := by ring
      _ ≤ _ := hmain2
  have hnn : 0 ≤ K / Real.sqrt c0 * |CL.lamL p X N| := by positivity
  exact abs_le.mpr (abs_le_of_sq_le_sq' hsq hnn)

end Glue

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_norm_lb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_norm_lb

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_kappa_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_kappa_bound

end FormalResearch.JacobiEigenvectors.TheoremB

end
