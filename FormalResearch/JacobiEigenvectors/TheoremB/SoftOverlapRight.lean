module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.SoftOverlap
public import FormalResearch.JacobiEigenvectors.TheoremB.SoftMirrorEig

/-!
# Paper J, Theorem B, L3.5b (soft halves), part 11: `overlap_lb` of the right half, by mirror transport

The right half of a soft edge is the left half of the mirror chart `CR` (a soft chart of `mirrorFamily Fz`), read at the chain rows `j <-> N - j`: the chart rows of the right half are `chartRowDn N lo R true`, whose chain row is `N - j`
with `j` in the mirror half-window `(softWindow CR p X N).filter (j <= nearestRow h (CR.uc p))` (this is the set `P_k` of the right chart, which is the mirror image of `Omega cap {n >= N - n_c^R}`).  Hence the lower bound is
`soft_window_eig_lower` for the *mirror* matrix and the reflected eigen-system `(X, mirrorU U)` of `SoftMirrorEig.lean`; no new estimate is needed.

* `castChart`, `castChart_fields`: transport of a soft chart along `F = G` (used with `mirror_mirror`, to see `CL` as a chart of `mirrorFamily (mirrorFamily Fz)`).
* `soft_window_eig_lower_right`: `c_0 <= sqrt(sum_{j in S^R} Psi_{k, N-j}^2)`, `S^R = Omega_R cap {j <= n_c^R}`, at eigenvalues near the edge with `a <= 1` and Step 0.
* `softJBChart_overlap_lb_right`: the same at the chart rows (`tau = true`).

Needs only `SoftMirror CL CR`, no `StdAssump` (flat1 of the mirror chart is `soft_flat1_phi`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section Cast

variable {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}

/-- transport of a soft chart along an equality of families. -/
def castChart {F G : SymbolFamily (Par × ℝ)} (h : F = G) (C : SoftEdgeChart F P m q U V Lm) : SoftEdgeChart G P m q U V Lm := h ▸ C

theorem castChart_fields {F G : SymbolFamily (Par × ℝ)} (h : F = G) (C : SoftEdgeChart F P m q U V Lm) :
    (∀ p, (castChart h C).uc p = C.uc p) ∧ (∀ p α x, (castChart h C).zeta p α x = C.zeta p α x) ∧
      (∀ r p α, (castChart h C).muS r p α = C.muS r p α) ∧ (castChart h C).η = C.η ∧ (castChart h C).δ0 = C.δ0 ∧
      (castChart h C).N0 = C.N0 := by
  subst h
  exact ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩

end Cast

section Right

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}

theorem softMirror_symm (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1))
    (hM : SoftMirror CL CR) : SoftMirror CR (castChart (mirror_mirror Fz).symm CL) := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := castChart_fields (mirror_mirror Fz).symm CL
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hM
  refine ⟨fun p hp => ?_, fun p hp α x => ?_, fun r p hp α => ?_, ?_, ?_, ?_⟩
  · rw [c1, h1 p hp]; show CL.uc p = Fz.L - (Fz.L - CL.uc p); ring
  · have := h2 p hp α (-x)
    rw [neg_neg] at this
    rw [c2]; linarith
  · rw [c3, h3 r p hp α]
  · rw [c4, h4]
  · rw [c5, h5]
  · rw [c6, h6]

set_option maxHeartbeats 1000000 in
theorem soft_window_eig_lower_right {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC)
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1))
    (hM : SoftMirror CL CR) (hm : 1 ≤ m) (Cs0 : ℝ) :
    ∃ c0 h1 : ℝ, 0 < c0 ∧ 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        (∀ i, Xs i ≤ Fz.bandHi p + Cs0 * Fz.step N ^ 2) → ∀ k : Fin (N + 1), |Xs k - Fz.bandHi p| ≤ CL.δ0 → CL.aOf p (Xs k) N ≤ 1 →
          c0 ≤ Real.sqrt (∑ j ∈ (softWindow CR p (Xs k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CR.uc p)),
            (eigVec Um k ((N : ℤ) - j)) ^ 2) := by
  have hM' := softMirror_symm CL CR hM
  obtain ⟨-, -, -, -, -, c6⟩ := castChart_fields (mirror_mirror Fz).symm CL
  obtain ⟨c0, h1, hc0, hh1, H⟩ := soft_window_eig_lower (Fz := mirrorFamily Fz) hf CR (castChart (mirror_mirror Fz).symm CL) hM' hm Cs0
  refine ⟨c0, min h1 (min CL.softH1 CR.softH1), hc0, lt_min hh1 (lt_min CL.softH1_pos CR.softH1_pos), ?_⟩
  intro p hp N hN hstep Xs Um hE hs0 k hX ha
  have hs1 : (mirrorFamily Fz).step N ≤ h1 := hstep.trans (min_le_left _ _)
  have hsL : Fz.step N ≤ CL.softH1 := hstep.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsR : Fz.step N ≤ CR.softH1 := hstep.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hpos := bondA_pos_all CL CR hM hp hX hN1 hsL hsR
  have hne : ∀ k', Um (Fin.last N) k' ≠ 0 := fun k' => by
    have := eigen_last_ne_zero Fz p N (Xs k') Xs Um hE k' rfl hpos
    have e : eigVec Um k' (N : ℤ) = Um (Fin.last N) k' := by
      unfold eigVec
      rw [dif_pos ⟨by positivity, le_rfl⟩]
      congr 1
    rwa [e] at this
  have hE' := isEigenSystem_mirror hE hne
  have hcR : (mirrorFamily Fz).bandHi p = Fz.bandHi p := bandHi_mirror Fz p
  have hδ : CR.δ0 = CL.δ0 := hM.2.2.2.2.1
  have h := H p hp N (by rw [c6]; exact max_comm CL.N0 CR.N0 ▸ hN) hs1 Xs (mirrorU Um) hE'
    (fun i => by rw [hcR]; exact hs0 i) k (by rw [hcR, hδ]; exact hX) (by rw [aOf_mirror hM hp]; exact ha)
  refine h.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [eigVec_mirrorU]
  split_ifs <;> ring

end Right

section RightChart

variable {Jlo Jhi : (Par × ℝ) → ℝ} {ulo uhi : (Par × ℝ) → ℝ}

set_option maxHeartbeats 1000000 in
/-- **`overlap_lb` of the right soft half, chart rows** (`tau = true`, the chart `softJBChart CR CR1 ...` of the mirror family): `||P_k Psi_k|| >= c_0` for `P_k = softPk` over the mirror half-window
`Omega_R cap {j <= n_c^R}` (the chain row `j` of the chart row `n` is `N - (lo + n)`, i.e. the global row `lo + n`); see `soft_window_eig_lower_right`.  Columns and gauge as in `softJBChart_overlap_lb_left`
(`Xc k = Xs (kc k)`, `(Wm n k)^2 = (Um n (kc k))^2`). -/
theorem softJBChart_overlap_lb_right {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC)
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1))
    (CR1 : SoftEdgeChart (mirrorFamily Fz) P (m + 1) q U V (fun _ => 1))
    (hM : SoftMirror CL CR) (hm : 1 ≤ m) (Cs0 : ℝ) :
    ∃ c0 h1 : ℝ, 0 < c0 ∧ 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
      (∀ i, Xs i ≤ Fz.bandHi p + Cs0 * Fz.step N ^ 2) →
      ∀ (TI : TransferInputsDn (mirrorFamily Fz) P Jlo Jhi m CR.chain CR1.chain 2 ulo uhi) (cols : Finset (Fin (N + 1))) (lo R : ℕ)
        (hlo : lo + R ≤ N + 1) (used : Finset (Fin R)) (σ0 σ1 : cols → ℝ) (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
        (Xc : Fin (N + 1) → ℝ) (kc : Fin (N + 1) → Fin (N + 1)) (Wm : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
      (∀ k : cols, Xc k = Xs (kc k)) → (∀ n k : Fin (N + 1), (Wm n k) ^ 2 = (Um n (kc k)) ^ 2) →
      (∀ k : cols, |Xc k - Fz.bandHi p| ≤ CL.δ0) → (∀ k : cols, CL.aOf p (Xc k) N ≤ 1) →
      (∀ k : cols, ∀ j ∈ (softWindow CR p (Xc k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CR.uc p)),
        ∃ n : Fin R, chartRowDn N lo R true n = j) →
      ∀ k : cols,
        c0 ≤ FormalResearch.JB.jbL2 (softPk N lo R true ((softWindow CR p (Xc k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CR.uc p))))
            (fun n => Wm ((softJBChart CR CR1 TI p N Xc cols lo R hlo true used
              (fun k => softPk N lo R true ((softWindow CR p (Xc k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CR.uc p)))) σ0 σ1 host0 host1).row n) k) := by
  obtain ⟨c0, h1, hc0, hh1, H⟩ := soft_window_eig_lower_right hf CL CR hM hm Cs0
  refine ⟨c0, h1, hc0, hh1, ?_⟩
  intro p hp N hN hstep Xs Um hE hs0 TI cols lo R hlo used σ0 σ1 host0 host1 Xc kc Wm hXc hW hX ha hcov k
  have hXk := hXc k
  have h := H p hp N hN hstep Xs Um hE hs0 (kc k) (by rw [← hXk]; exact hX k) (by rw [← hXk]; exact ha k)
  rw [← hXk] at h
  refine h.trans (le_of_eq ?_)
  unfold FormalResearch.JB.jbL2
  congr 1
  set S := (softWindow CR p (Xc k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CR.uc p)) with hS
  have e := sum_chart_rows (chartRowDn N lo R true) (chartRowDn_injective N lo R true) S (hcov k)
    (fun j => (eigVec Um (kc k) ((N : ℤ) - j)) ^ 2)
  beta_reduce at e
  unfold softPk
  rw [← e]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hr1 : (N : ℤ) - chartRowDn N lo R true n = ((FormalResearch.JB.Chart.row (softJBChart CR CR1 TI p N Xc cols lo R hlo true used
      (fun k => softPk N lo R true ((softWindow CR p (Xc k) N).filter (fun n => n ≤ nearestRow (Fz.step N) (CR.uc p)))) σ0 σ1 host0 host1) n : Fin (N + 1)) : ℤ) := by
    simp [chartRowDn, FormalResearch.JB.Chart.row, softJBChart]
  simp only [hr1, eigVec_row]
  exact (hW _ k).symm

end RightChart

end FormalResearch.JacobiEigenvectors.TheoremB

end
