module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.SoftExtRow

/-!
# Paper J, Theorem B, L3.5b (soft halves), part 12: the field `ext_row` of `JB.Chart.Ok` at `softJBChart`

`softJBChart_ext_row`: `soft_ext_row_l2` instantiated at the charts `softJBChart CL CL1 TI ...` (left half, `tau = false`) and `softJBChart CR CR1 TI' ...` (right half, `tau = true`, mirror family) when the rows are
chosen as `lo = floor((u_c - eta/2)/h - 1/2) + 1` (left) resp. `lo + R = ceil((u_c + eta/2)/h - 1/2)` (right), so that `chartExtRowDn` is the exterior row `j` of `soft_ext_row_l2`, and the scalars are
`sigma^{[m+1]} = lambda_L/(kappa_b hat N)` (left), `hat kappa lambda_R/(kappa_b hat N)` (right), both for the order-`(m+1)` pair.  Then `jbL2 univ (omega_n sigma^{[m+1]}_k y_ext,k) <= 1`, `C_E >= 1` covers `Chart.Ok.ext_row`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
  {Jlo Jhi : (Par × ℝ) → ℝ} {ulo uhi : (Par × ℝ) → ℝ}

/-- **`ext_row` of the soft charts** (both halves). -/
theorem softJBChart_ext_row {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC)
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1))
    (CL1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1)) (CR1 : SoftEdgeChart (mirrorFamily Fz) P (m + 1) q U V (fun _ => 1))
    (hM : SoftMirror CL CR) (hM1 : SoftMirror CL1 CR1) (hδ1 : CL1.δ0 = CL.δ0)
    (r : ℕ) (hr : StdAssump Fz P (q / 2) r) :
    ∃ h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CL1.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))), (∀ k : cols, |Xc k - Fz.bandHi p| ≤ CL.δ0) → (∀ k : cols, CL1.aOf p (Xc k) N ≤ 1) →
      (∀ (TI : TransferInputsDn Fz P Jlo Jhi m CL.chain CL1.chain 2 ulo uhi) (lo R : ℕ) (hlo : lo + R ≤ N + 1)
        (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 σ1 : cols → ℝ) (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        (lo : ℤ) = ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋ + 1 →
        (∀ k : cols, σ1 k = CL1.lamL p (Xc k) N / (kappaBal (CL1.aOf p (Xc k) N) * softNorm CL1 CR1 p (Xc k) N)) →
        ∀ n : Fin R, n.val = 0 →
          FormalResearch.JB.jbL2 Finset.univ (fun k : cols =>
            (softJBChart CL CL1 TI p N Xc cols lo R hlo false used Pk σ0 σ1 host0 host1).ω n * σ1 k *
              (softJBChart CL CL1 TI p N Xc cols lo R hlo false used Pk σ0 σ1 host0 host1).yext k) ≤ 1) ∧
      (∀ (TI : TransferInputsDn (mirrorFamily Fz) P Jlo Jhi m CR.chain CR1.chain 2 ulo uhi) (lo R : ℕ) (hlo : lo + R ≤ N + 1)
        (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 σ1 : cols → ℝ) (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        ((lo + R : ℕ) : ℤ) = ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉ →
        (∀ k : cols, σ1 k = softKappa CL1 CR1 p (Xc k) N * CR1.lamL p (Xc k) N / (kappaBal (CR1.aOf p (Xc k) N) * softNorm CL1 CR1 p (Xc k) N)) →
        ∀ n : Fin R, n.val + 1 = R →
          FormalResearch.JB.jbL2 Finset.univ (fun k : cols =>
            (softJBChart CR CR1 TI p N Xc cols lo R hlo true used Pk σ0 σ1 host0 host1).ω n * σ1 k *
              (softJBChart CR CR1 TI p N Xc cols lo R hlo true used Pk σ0 σ1 host0 host1).yext k) ≤ 1) := by
  obtain ⟨h1, hh1, H⟩ := soft_ext_row_l2 hf CL CR CL1 CR1 hM hM1 hδ1 r hr
  refine ⟨h1, hh1, ?_⟩
  intro p hp N hN hstep Xc cols hX ha
  obtain ⟨HL, HR⟩ := H p hp N hN hstep Xc cols hX ha
  constructor
  · intro TI lo R hlo used Pk σ0 σ1 host0 host1 hlo' hσ n hn
    have hj : (lo : ℤ) - 1 = ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋ := by omega
    have h := HL _ hj
    refine le_trans (le_of_eq ?_) h
    unfold FormalResearch.JB.jbL2
    congr 2
    funext k
    simp only [softJBChart, chartExtRowDn, Bool.false_eq_true, ite_false, hσ k, hj]
  · intro TI lo R hlo used Pk σ0 σ1 host0 host1 hlo' hσ n hn
    have hj : (N : ℤ) - lo - R = (N : ℤ) - ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉ := by
      rw [← hlo']; push_cast; ring
    have h := HR _ hj
    refine le_trans (le_of_eq ?_) h
    unfold FormalResearch.JB.jbL2
    congr 2
    funext k
    simp only [softJBChart, chartExtRowDn, ite_true, hσ k]
    rw [hj]
    rfl

end FormalResearch.JacobiEigenvectors.TheoremB

end
