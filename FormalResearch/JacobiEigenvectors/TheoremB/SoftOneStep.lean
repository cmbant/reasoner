module

public import Mathlib
public import FormalResearch.JB.JBOneStepDef
public import FormalResearch.JacobiEigenvectors.TheoremB.BulkOneStep
public import FormalResearch.JacobiEigenvectors.TheoremB.Collar
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftRescale
public import FormalResearch.JacobiEigenvectors.TheoremA.WindowMass2

/-!
# Paper J, Theorem B, L3.5b (soft halves to `JB.Chart`), part 1: the coefficient fields of `JB.Chart.Ok` and the host entries

Source: Paper J `app_thmB.tex`, "(I2): soft charts" (the exact transfer of the parabolic-cylinder ladder of the collar, `omega = 1`, `|t_12| >= c_T`, `alpha >= c_alpha`, the five Schur multipliers) and
the soft columns of `eq:thb-bulkcol`.  Model: `BulkOneStep.lean` (the bulk analogue).

## Proved here

* `softJBChart`: the `JB.Chart` of a soft chart pair `(C, C1)` (orders `m`, `m + 1` of the collar ladder, `TransferInputs` `TI` of patch `2`), sampled at the energies `Xc k`, `k in cols`, with the chart rows `chartRowDn` (`tau = false`, the left half, direction `-1`: the
  rows `lo + n` of the chain; `tau = true`, the right half, direction `+1`: the rows `N - (lo + n)` of the mirror family; in the index of the chain of the half both **step down**, finding F-B16), the model pair `(y, y~) = wf 2 0` of the order-`m` chain, `omega = 1` (`D_+ = 1` on the shared PC patches, `shared_PC`),
  `t_11, t_12 = Pi_{-,00}, Pi_{-,01}` of patch 2 (`TransferInputsDn`), the corrector rows `A^{[r]}, B^{[r]}` and `kappa` of `TI`, the exterior row `y_ext` and the design data as parameters.
* `soft_transfer_row_dn`: the exact downward model transfer `omega y_{r-1} = Pi_{-,00} y_r + Pi_{-,01} y~_r` on every lattice row `r >= 1` for the rescaled chain (`rescale1` does not touch patch 2; `shift_dn`).
* `softJBChart_coeff`: **all of `ChartOkCoeff` for `softJBChart`** (every design data), from `TransferInputs`, `soft_transfer_row`, `chart_schur_five`.
* `softJBChart_H0`, `softJBChart_H1`: `H^{[r]}_c = sigma phi^{[r]}_2` on the chart rows.
* `compMatrix_softUp_entry`: the entry of `compMatrix` in a column of an upper soft energy (`blockOf = none`, `Jhi < X`) is `psi-hat^L_n/hat N` for rows `n <= n_c` and `hat kappa psi-hat^R_n/hat N` beyond, `n_c = nearestRow u_c`.
* `softUp_host1_eq_left`, `softUp_host1_eq_right`: `host1_eq` of the two halves (order `m+1` chart `C1`, `softJBChart_H1`, host `compMatrix CI1 spl1`).
* `softUp_host0_eq_left`, `softUp_host0_eq_right`: `host0_eq` of the two halves of the upper soft edge, with `sigma = lambda_L/(kappa_bal hat N)` (left, rows `<= n_c`, `psi-hat^L = lambda_L phi_2/kappa_bal` on the collar)
  and `sigma = hat kappa lambda_R/(kappa_bal hat N)` (right).

## Differences from the paper

None of substance.  The soft chart uses the **whole collar ladder** (patch 2 for all collar rows: patches 2 and 3 share `dd, PiP, AA, BB`, and `wf2_eq` holds on every row of the collar), as the paper's "comparison sequence `psi-hat^{PC,-}` lives on the whole collar".

## Not formalised here

The lower soft edge (the gauge `D_-`: `y, y~ -> (-1)^n (y, y~)`, `(t_11, t_12) -> (-t_11, -t_12)`), `host*_col`, `match0/1`, `ext_row`, `overlap_lb/ub` (see the report), and the choice of `lo, R, used, P_k`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

open scoped Classical

/-- The chain row of the chart row `n` of a **down** soft chart with global rows `lo .. lo + R - 1`: left half (`tau = false`, direction `-1`): the row itself; right half (`tau = true`, direction `+1`, in the mirror chain):
the mirror row `N - (lo + n)`. -/
def chartRowDn (N lo R : ℕ) (τ : Bool) (n : Fin R) : ℤ := if τ then (N : ℤ) - ((lo : ℤ) + n) else (lo : ℤ) + n

/-- The chain row of the exterior row of a down soft chart: `lo - 1` (left, before the first row) resp. `N - lo - R` (right half, mirror chain, after the last global row); both in the forbidden region. -/
def chartExtRowDn (N lo R : ℕ) (τ : Bool) : ℤ := if τ then (N : ℤ) - lo - R else (lo : ℤ) - 1

section Chart

variable {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
  {Jlo Jhi : (Par × ℝ) → ℝ} {ulo uhi : (Par × ℝ) → ℝ}

/-- **The `JB.Chart` of a soft chart pair** `(C, C1)` (orders `m`, `m+1`, the collar ladder = patch 2, `TransferInputs` `TI`), sampled at the energies `Xc k`, `k in cols`; see the module docstring. -/
def softJBChart (C : SoftEdgeChart G P m q U V (fun _ => 1)) (C1 : SoftEdgeChart G P (m + 1) q U V (fun _ => 1))
    (TI : TransferInputsDn G P Jlo Jhi m C.chain C1.chain 2 ulo uhi)
    (p : Par × ℝ) (N : ℕ) (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (lo R : ℕ) (hlo : lo + R ≤ N + 1) (τ : Bool)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 σ1 : cols → ℝ)
    (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : FormalResearch.JB.Chart (N + 1) R cols where
  lo := lo
  lo_add := hlo
  τ := τ
  used := used
  y := Matrix.of fun n k => (C.chain p (Xc k) N).wf 2 0 (uNode (G.step N) (chartRowDn N lo R τ n)) (G.step N) 0
  yt := Matrix.of fun n k => (C.chain p (Xc k) N).wf 2 0 (uNode (G.step N) (chartRowDn N lo R τ n)) (G.step N) 1
  yext := fun k => (C.chain p (Xc k) N).wf 2 0 (uNode (G.step N) (chartExtRowDn N lo R τ)) (G.step N) 0
  ω := fun _ => 1
  t11 := Matrix.of fun n k => (C1.chain p (Xc k) N).PiM 2 (uNode (G.step N) (chartRowDn N lo R τ n)) (G.step N) 0 0
  t12 := Matrix.of fun n k => (C1.chain p (Xc k) N).PiM 2 (uNode (G.step N) (chartRowDn N lo R τ n)) (G.step N) 0 1
  A0 := Matrix.of fun n k => (C.chain p (Xc k) N).AA 2 (uNode (G.step N) (chartRowDn N lo R τ n)) (G.step N)
  A1 := Matrix.of fun n k => (C1.chain p (Xc k) N).AA 2 (uNode (G.step N) (chartRowDn N lo R τ n)) (G.step N)
  B0 := Matrix.of fun n k => (C.chain p (Xc k) N).BB 2 (uNode (G.step N) (chartRowDn N lo R τ n)) (G.step N)
  B1 := Matrix.of fun n k => (C1.chain p (Xc k) N).BB 2 (uNode (G.step N) (chartRowDn N lo R τ n)) (G.step N)
  κ := Matrix.of fun n k => TI.κ p (Xc k) N (uNode (G.step N) (chartRowDn N lo R τ n))
  σ0 := σ0
  σ1 := σ1
  P := Pk
  host0 := host0
  host1 := host1

/-- **The exact one-step model transfer of the collar ladder, downward** (`SymplecticLadder.shift_dn`, first component; `omega = D_- = 1`): at a lattice row `r >= 1`,
`y_{r-1} = Pi_{-,00}(u_r) y_r + Pi_{-,01}(u_r) y~_r` for the model pair `(y, y~) = wf 2 0` of the chain (every row of the collar, by the shared PC ladder). -/
theorem soft_transfer_row_dn (C : SoftEdgeChart G P m q U V (fun _ => 1)) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - G.bandHi p| ≤ C.δ0)
    {N : ℕ} (hN : C.N0 ≤ N) (r : ℤ) (hr : 1 ≤ r) :
    (C.chain p X N).wf 2 0 (uNode (G.step N) (r - 1)) (G.step N) 0 =
      (C.chain p X N).PiM 2 (uNode (G.step N) r) (G.step N) 0 0 * (C.chain p X N).wf 2 0 (uNode (G.step N) r) (G.step N) 0 +
        (C.chain p X N).PiM 2 (uNode (G.step N) r) (G.step N) 0 1 * (C.chain p X N).wf 2 0 (uNode (G.step N) r) (G.step N) 1 := by
  have hst : 0 < G.step N := SoftEdgeChart.step_pos (F := G) N
  obtain ⟨lam, hV⟩ : ∃ lam, ((C.chain p X N).rescale1 lam).PreValid C.cs (G.step N) m := ⟨_, C.valid p hp X hX N hN⟩
  have hP3 : ((C.chain p X N).rescale1 lam).P = 3 := (C.shape p hp X hX N hN).1
  have hL := hV.ladder 2 (Finset.mem_Icc.mpr ⟨by norm_num, by rw [hP3]; norm_num⟩)
  have hwf : ((C.chain p X N).rescale1 lam).wf 2 = (C.chain p X N).wf 2 := by
    funext α u h
    simp [LadderData.rescale1, LadderData.rescaleFactor]
  have hsite : IsSitePos (1 / 2) (G.step N) (uNode (G.step N) r) := by
    refine ⟨r.toNat, by omega, ?_⟩
    unfold uNode
    have h2 : ((r.toNat : ℕ) : ℝ) = (r : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
    rw [h2]
  have h1 := (shift_dn_comp hL 0 (uNode (G.step N) r) (G.step N) hst hsite).1
  have e : uNode (G.step N) r - G.step N = uNode (G.step N) (r - 1) := by
    unfold uNode; push_cast; ring
  rw [e] at h1
  have hd : Dm ((C.chain p X N).dd 2) (uNode (G.step N) r) (G.step N) = 1 := by
    unfold Dm
    exact (C.shared_PC p hp X hX N hN).1 _ _
  have hd' : Dm (((C.chain p X N).rescale1 lam).dd 2) (uNode (G.step N) r) (G.step N) = 1 := hd
  rw [hd', hwf] at h1
  simpa using h1.trans (by simp [LadderData.rescale1])

/-- The shifted carrier of the sampled down soft chart: `y_{n + tau}` is the model pair at the chain row **below** `chartRowDn n` (in the index of the chain of the half). -/
theorem softJBChart_shifted (C : SoftEdgeChart G P m q U V (fun _ => 1)) (C1 : SoftEdgeChart G P (m + 1) q U V (fun _ => 1))
    (TI : TransferInputsDn G P Jlo Jhi m C.chain C1.chain 2 ulo uhi)
    (p : Par × ℝ) (N : ℕ) (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (lo R : ℕ) (hlo : lo + R ≤ N + 1) (τ : Bool)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 σ1 : cols → ℝ)
    (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (n : Fin R) (k : cols) :
    (softJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).shifted
        (softJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).y n k =
      (C.chain p (Xc k) N).wf 2 0 (uNode (G.step N) (chartRowDn N lo R τ n - 1)) (G.step N) 0 := by
  have key : ∀ A B : ℤ, A = B → (C.chain p (Xc k) N).wf 2 0 (uNode (G.step N) A) (G.step N) 0 =
      (C.chain p (Xc k) N).wf 2 0 (uNode (G.step N) B) (G.step N) 0 := fun A B h => by rw [h]
  cases τ
  · simp only [FormalResearch.JB.Chart.shifted, softJBChart, Bool.false_eq_true, ite_false, Matrix.of_apply]
    unfold FormalResearch.JB.YshRev
    by_cases hn : 0 < n.val
    · rw [dite_eq_left hn]
      simp only [Matrix.of_apply, chartRowDn, Bool.false_eq_true, ite_false]
      refine key _ _ ?_
      omega
    · rw [dite_eq_right hn]
      simp only [chartExtRowDn, chartRowDn, Bool.false_eq_true, ite_false]
      refine key _ _ ?_
      omega
  · simp only [FormalResearch.JB.Chart.shifted, softJBChart, ite_true, Matrix.of_apply]
    unfold FormalResearch.JB.Ysh
    by_cases hn : n.val + 1 < R
    · rw [dite_eq_left hn]
      simp only [Matrix.of_apply, chartRowDn, ite_true]
      refine key _ _ ?_
      omega
    · rw [dite_eq_right hn]
      simp only [chartExtRowDn, chartRowDn, ite_true]
      refine key _ _ ?_
      omega

/-- **The coefficient fields of `JB.Chart.Ok` for a soft chart** (all design data arbitrary): `omega_pos`, the exact model `transfer`, `t12_lb`, `alpha_lb`, the five Schur bounds and the parity identities, from `TransferInputs`
(the primitive `C^2`, lower-bound and parity inputs), `soft_transfer_row` and `chart_schur_five`.  The chart rows must be rows of the chain on the collar rectangle (`0 <= row`, `ulo <= u_row <= uhi`); `cs` dominates the chart
constants (`c_T`, `c_alpha`, `omega_max`, and the Schur constant `chartSchurK ..` for `|h| <= H`). -/
theorem softJBChart_coeff (C : SoftEdgeChart G P m q U V (fun _ => 1)) (C1 : SoftEdgeChart G P (m + 1) q U V (fun _ => 1))
    (TI : TransferInputsDn G P Jlo Jhi m C.chain C1.chain 2 ulo uhi)
    (cs : FormalResearch.JB.OneStepConsts) {p : Par × ℝ} (hp : p ∈ P) (N : ℕ) (hN : max C.N0 C1.N0 ≤ N) (hNT : TI.N0 ≤ N)
    (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (lo R : ℕ) (hlo : lo + R ≤ N + 1) (τ : Bool)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 σ1 : cols → ℝ)
    (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hX : ∀ k : cols, Xc k ∈ Set.Icc (Jlo p) (Jhi p)) (hJ : ∀ X ∈ Set.Icc (Jlo p) (Jhi p), |X - G.bandHi p| ≤ C.δ0)
    (hrows : ∀ n : Fin R, 1 ≤ chartRowDn N lo R τ n ∧ ulo p ≤ uNode (G.step N) (chartRowDn N lo R τ n) ∧ uNode (G.step N) (chartRowDn N lo R τ n) ≤ uhi p)
    (H : ℝ) (hH : |G.step N| ≤ H) (hcT : cs.cT ≤ TI.cT) (hcα : cs.cα ≤ TI.cα) (hω : TI.ωmax ≤ cs.ωmax)
    (hK : chartSchurK (ulo p) (uhi p) (Jlo p) (Jhi p) TI.S TI.cT TI.cα H ≤ cs.K) :
    ChartOkCoeff cs m (G.step N) (softJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1) := by
  have hN0 : C.N0 ≤ N := le_trans (le_max_left _ _) hN
  have hst : 0 < G.step N := SoftEdgeChart.step_pos (F := G) N
  obtain ⟨hrect, hcTp, hcαp, hS0, hωp⟩ := TI.consts_pos
  have hab := (hrect p hp).1
  have hcd := (hrect p hp).2
  have hu : ∀ n : Fin R, uNode (G.step N) (chartRowDn N lo R τ n) ∈ Set.Icc (ulo p) (uhi p) := fun n => ⟨(hrows n).2.1, (hrows n).2.2⟩
  have hsame := fun k : cols => TI.same_ladder p hp (Xc k) (hX k) N hNT
  have hfive := chart_schur_five (a := ulo p) (b := uhi p) (c := Jlo p) (d := Jhi p) (S := TI.S) (cT := TI.cT) (cα := TI.cα) (H := H)
    hab hcd hcTp hcαp
    (fun u X => (C1.chain p X N).AA 2 u (G.step N)) (fun u X => (C1.chain p X N).BB 2 u (G.step N))
    (fun u X => (C1.chain p X N).PiM 2 u (G.step N) 0 0) (fun u X => (C1.chain p X N).PiM 2 u (G.step N) 0 1)
    (fun u X => TI.κ p X N u) (G.step N) hH
    (TI.reg_A1 p hp N hNT) (TI.reg_B1 p hp N hNT) (TI.reg_t11 p hp N hNT) (TI.reg_t12 p hp N hNT) (TI.reg_κ p hp N hNT)
    (fun t ht X hXm => TI.t12_lb p hp X hXm N hNT t ht) (fun t ht X hXm => TI.alpha_lb p hp X hXm N hNT t ht)
  obtain ⟨-, hS⟩ := hfive
  obtain ⟨b1, b2, b3, b4, b5⟩ := hS (Fin R) cols (fun n => uNode (G.step N) (chartRowDn N lo R τ n)) (fun k => Xc k) (fun n => hu n) (fun k => hX k)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n k
    exact TI.parity_A p hp (Xc k) (hX k) N hNT _ (hu n)
  · intro n k
    exact TI.parity_B p hp (Xc k) (hX k) N hNT _ (hu n)
  · intro n
    refine ⟨one_pos, ?_⟩
    have hXn : ∀ k : cols, Xc k ∈ Set.Icc (Jlo p) (Jhi p) := hX
    -- a sampled energy: any point of the rectangle works (the column set may be empty; `Jlo p` is in the rectangle)
    have hJlo : Jlo p ∈ Set.Icc (Jlo p) (Jhi p) := ⟨le_rfl, hcd⟩
    have h2 := (TI.omega_pos_le p hp (Jlo p) hJlo N hNT (chartRowDn N lo R τ n) (hu n).1 (hu n).2).2
    have hd : Dm ((C1.chain p (Jlo p) N).dd 2) (uNode (G.step N) (chartRowDn N lo R τ n)) (G.step N) = 1 := by
      have e : (C1.chain p (Jlo p) N).dd 2 = (C.chain p (Jlo p) N).dd 2 := ((TI.same_ladder p hp (Jlo p) hJlo N hNT).2.2).symm
      rw [e]
      unfold Dm
      exact (C.shared_PC p hp (Jlo p) (hJ _ hJlo) N hN0).1 _ _
    rw [hd] at h2
    exact h2.trans hω
  · intro n k
    show 1 * _ = _ * _ + _ * _
    rw [softJBChart_shifted]
    obtain ⟨hnn, -⟩ := hrows n
    have h1 := soft_transfer_row_dn C hp (hJ _ (hX k)) hN0 (chartRowDn N lo R τ n) hnn
    have hP := congrFun (congrFun (hsame k).1 (uNode (G.step N) (chartRowDn N lo R τ n))) (G.step N)
    simp only [softJBChart, Matrix.of_apply]
    rw [← hP, one_mul]
    exact h1
  · intro n k
    exact hcT.trans (TI.t12_lb p hp (Xc k) (hX k) N hNT _ (hu n))
  · intro n k
    exact hcα.trans (TI.alpha_lb p hp (Xc k) (hX k) N hNT _ (hu n))
  exacts [b4.mono hK, b5.mono hK, b1.mono hK, b2.mono hK, b3.mono hK]

/-- **The model-profile identity**: `H^{[m]}_c = sigma_k phi^{[m]}_{2, row n}` for the chart of a soft chart `C` (any `sigma`): the profile `A y + h B y~` is the corrected comparison sequence `phi^{(1)}_2` (`phi = v . w`). -/
theorem softJBChart_H0 (C : SoftEdgeChart G P m q U V (fun _ => 1)) (C1 : SoftEdgeChart G P (m + 1) q U V (fun _ => 1))
    (TI : TransferInputsDn G P Jlo Jhi m C.chain C1.chain 2 ulo uhi)
    (p : Par × ℝ) (N : ℕ) (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (lo R : ℕ) (hlo : lo + R ≤ N + 1) (τ : Bool)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 σ1 : cols → ℝ)
    (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (n : Fin R) (k : cols) :
    (softJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).H0 (G.step N) n k =
      σ0 k * (C.chain p (Xc k) N).phi (G.step N) 0 2 (chartRowDn N lo R τ n) := by
  simp only [FormalResearch.JB.Chart.H0_apply, FormalResearch.JB.Chart.phi0_apply, softJBChart, Matrix.of_apply]
  congr 1
  unfold LadderData.phi ladderSeq vrow dot uNode
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Same for order `m + 1`, with the chart `C1` (the model pair is the one of `C`: `same_ladder`). -/
theorem softJBChart_H1 (C : SoftEdgeChart G P m q U V (fun _ => 1)) (C1 : SoftEdgeChart G P (m + 1) q U V (fun _ => 1))
    (TI : TransferInputsDn G P Jlo Jhi m C.chain C1.chain 2 ulo uhi)
    (p : Par × ℝ) (hp : p ∈ P) (N : ℕ) (hNT : TI.N0 ≤ N) (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (lo R : ℕ)
    (hlo : lo + R ≤ N + 1) (τ : Bool)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 σ1 : cols → ℝ)
    (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hX : ∀ k : cols, Xc k ∈ Set.Icc (Jlo p) (Jhi p)) (n : Fin R) (k : cols) :
    (softJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).H1 (G.step N) n k =
      σ1 k * (C1.chain p (Xc k) N).phi (G.step N) 0 2 (chartRowDn N lo R τ n) := by
  simp only [FormalResearch.JB.Chart.H1_apply, FormalResearch.JB.Chart.phi1_apply, softJBChart, Matrix.of_apply]
  congr 1
  unfold LadderData.phi ladderSeq vrow dot uNode
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hw : (C.chain p (Xc k) N).wf 2 = (C1.chain p (Xc k) N).wf 2 := (TI.same_ladder p hp (Xc k) (hX k) N hNT).2.1
  have hw := congrFun hw 0
  rw [← hw]
  ring

end Chart

section HostEntries

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **The entries of `compMatrix` on an upper soft column**: for an energy outside all blocks and above `J_hi`, the entry in row `i` is `psi-hat^L_i / hat N` if `i <= n_c` and
`hat kappa psi-hat^R_i / hat N` otherwise (`n_c = nearestRow u_c`, `psi-hat^R_i = psi-hat^{L,mirror}_{N - i}`). -/
theorem compMatrix_softUp_entry (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (spl : Fin CI.nb → ℝ) (μ : Par) (N : ℕ)
    (Xs : Fin (N + 1) → ℝ) (k : Fin (N + 1)) (hk1 : ¬ ∃ ν : Fin CI.nb, CI.lo ν ≤ Xs k ∧ Xs k ≤ CI.hi ν) (hk2 : CI.Jhi < Xs k) (i : Fin (N + 1)) :
    compMatrix CI spl μ N Xs i k =
      if ((i : ℕ) : ℤ) ≤ nearestRow (F.step N) (CI.softUpL.uc (atStep F μ N)) then
        CI.softUpL.psiHatL (atStep F μ N) (Xs k) N i / softNorm CI.softUpL CI.softUpR (atStep F μ N) (Xs k) N
      else softKappa CI.softUpL CI.softUpR (atStep F μ N) (Xs k) N *
        CI.softUpR.psiHatL (atStep F μ N) (Xs k) N ((N : ℤ) - ((i : ℕ) : ℤ)) / softNorm CI.softUpL CI.softUpR (atStep F μ N) (Xs k) N := by
  simp only [compMatrix, Matrix.of_apply, compColumn, dite_eq_right hk1, ite_eq_left hk2]
  unfold softColAt glueVecAt
  split_ifs <;> rfl

/-- **`host0_eq` for the left half of the upper soft edge** (chart rows `lo .. lo + R - 1`, all `<= n_c` and above `u_c - eta/2`; direction `-1`, exterior row `lo - 1`; `sigma_k = lambda_L / (kappa_bal hat N)`): `H^{[m]}_c = sigma phi_2` is the entry of the host `compMatrix CI spl`. -/
theorem softUp_host0_eq_left (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (CI1 : ChartInputs F K Kidx t0 (m + 1) q U V cPC CPC)
    {Jlo Jhi ulo uhi : (Par × ℝ) → ℝ}
    (TI : TransferInputsDn (frozenFamily F Kidx) (paramSet K t0) Jlo Jhi m CI.softUpL.chain CI1.softUpL.chain 2 ulo uhi)
    (spl : Fin CI.nb → ℝ) (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ)
    (cols : Finset (Fin (N + 1))) (hcols : ∀ k ∈ cols, (¬ ∃ ν : Fin CI.nb, CI.lo ν ≤ Xs k ∧ Xs k ≤ CI.hi ν) ∧ CI.Jhi < Xs k)
    (lo R : ℕ) (hlo : lo + R ≤ N + 1)
    (hle : ∀ n : Fin R, ((lo : ℤ) + n) ≤ nearestRow (F.step N) (CI.softUpL.uc (atStep F μ N)))
    (hgt : ∀ n : Fin R, CI.softUpL.uc (atStep F μ N) - CI.softUpL.η / 2 < uNode (F.step N) ((lo : ℤ) + n))
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ1 : cols → ℝ) (host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∀ n k, (softJBChart CI.softUpL CI1.softUpL TI (atStep F μ N) N Xs cols lo R hlo false used Pk
        (fun k => CI.softUpL.lamL (atStep F μ N) (Xs k) N /
          (kappaBal (CI.softUpL.aOf (atStep F μ N) (Xs k) N) * softNorm CI.softUpL CI.softUpR (atStep F μ N) (Xs k) N)) σ1
        (compMatrix CI spl μ N Xs) host1).H0 (F.step N) n k =
      (softJBChart CI.softUpL CI1.softUpL TI (atStep F μ N) N Xs cols lo R hlo false used Pk
        (fun k => CI.softUpL.lamL (atStep F μ N) (Xs k) N /
          (kappaBal (CI.softUpL.aOf (atStep F μ N) (Xs k) N) * softNorm CI.softUpL CI.softUpR (atStep F μ N) (Xs k) N)) σ1
        (compMatrix CI spl μ N Xs) host1).host0
        ((softJBChart CI.softUpL CI1.softUpL TI (atStep F μ N) N Xs cols lo R hlo false used Pk
          (fun k => CI.softUpL.lamL (atStep F μ N) (Xs k) N /
            (kappaBal (CI.softUpL.aOf (atStep F μ N) (Xs k) N) * softNorm CI.softUpL CI.softUpR (atStep F μ N) (Xs k) N)) σ1
          (compMatrix CI spl μ N Xs) host1).row n) k := by
  intro n k
  erw [softJBChart_H0]
  have hk := hcols k k.2
  simp only [softJBChart, FormalResearch.JB.Chart.row]
  rw [compMatrix_softUp_entry CI spl μ N Xs k hk.1 hk.2]
  have hn : ((((lo + n.val : ℕ)) : ℤ) ≤ nearestRow (F.step N) (CI.softUpL.uc (atStep F μ N))) := by
    have := hle n
    push_cast; exact this
  rw [ite_eq_left hn]
  have hcr : chartRowDn N lo R false n = (((lo + n.val : ℕ) : ℤ)) := by simp [chartRowDn]
  rw [hcr]
  have hg := hgt n
  have hg' : CI.softUpL.uc (atStep F μ N) - CI.softUpL.η / 2 < uNode (F.step N) (((lo + n.val : ℕ) : ℤ)) := by
    push_cast; exact hg
  rw [psiHatL_of_gt _ _ _ _ hg']
  ring

/-- **`host0_eq` for the right half of the upper soft edge** (mirror chart, direction `+1`, rows `lo .. lo + R - 1`, all `> n_c`, mirror rows above `u_c^R - eta/2`; `sigma_k = hat kappa lambda_R / (kappa_bal hat N)`). -/
theorem softUp_host0_eq_right (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (CI1 : ChartInputs F K Kidx t0 (m + 1) q U V cPC CPC)
    {Jlo Jhi ulo uhi : (Par × ℝ) → ℝ}
    (TI : TransferInputsDn (mirrorFamily (frozenFamily F Kidx)) (paramSet K t0) Jlo Jhi m CI.softUpR.chain CI1.softUpR.chain 2 ulo uhi)
    (spl : Fin CI.nb → ℝ) (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ)
    (cols : Finset (Fin (N + 1))) (hcols : ∀ k ∈ cols, (¬ ∃ ν : Fin CI.nb, CI.lo ν ≤ Xs k ∧ Xs k ≤ CI.hi ν) ∧ CI.Jhi < Xs k)
    (lo R : ℕ) (hlo : lo + R ≤ N + 1)
    (hgtn : ∀ n : Fin R, nearestRow (F.step N) (CI.softUpL.uc (atStep F μ N)) < (lo : ℤ) + n)
    (hgt : ∀ n : Fin R, CI.softUpR.uc (atStep F μ N) - CI.softUpR.η / 2 < uNode (F.step N) ((N : ℤ) - ((lo : ℤ) + n)))
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ1 : cols → ℝ) (host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∀ n k, (softJBChart CI.softUpR CI1.softUpR TI (atStep F μ N) N Xs cols lo R hlo true used Pk
        (fun k => softKappa CI.softUpL CI.softUpR (atStep F μ N) (Xs k) N * CI.softUpR.lamL (atStep F μ N) (Xs k) N /
          (kappaBal (CI.softUpR.aOf (atStep F μ N) (Xs k) N) * softNorm CI.softUpL CI.softUpR (atStep F μ N) (Xs k) N)) σ1
        (compMatrix CI spl μ N Xs) host1).H0 (F.step N) n k =
      (softJBChart CI.softUpR CI1.softUpR TI (atStep F μ N) N Xs cols lo R hlo true used Pk
        (fun k => softKappa CI.softUpL CI.softUpR (atStep F μ N) (Xs k) N * CI.softUpR.lamL (atStep F μ N) (Xs k) N /
          (kappaBal (CI.softUpR.aOf (atStep F μ N) (Xs k) N) * softNorm CI.softUpL CI.softUpR (atStep F μ N) (Xs k) N)) σ1
        (compMatrix CI spl μ N Xs) host1).host0
        ((softJBChart CI.softUpR CI1.softUpR TI (atStep F μ N) N Xs cols lo R hlo true used Pk
          (fun k => softKappa CI.softUpL CI.softUpR (atStep F μ N) (Xs k) N * CI.softUpR.lamL (atStep F μ N) (Xs k) N /
            (kappaBal (CI.softUpR.aOf (atStep F μ N) (Xs k) N) * softNorm CI.softUpL CI.softUpR (atStep F μ N) (Xs k) N)) σ1
          (compMatrix CI spl μ N Xs) host1).row n) k := by
  intro n k
  erw [softJBChart_H0]
  have hk := hcols k k.2
  simp only [softJBChart, FormalResearch.JB.Chart.row]
  rw [compMatrix_softUp_entry CI spl μ N Xs k hk.1 hk.2]
  have hn : ¬ ((((lo + n.val : ℕ)) : ℤ) ≤ nearestRow (F.step N) (CI.softUpL.uc (atStep F μ N))) := by
    have := hgtn n
    push_cast; omega
  rw [ite_eq_right hn]
  have hcr : chartRowDn N lo R true n = (N : ℤ) - (((lo + n.val : ℕ) : ℤ)) := by simp [chartRowDn]
  rw [hcr]
  have hg' : CI.softUpR.uc (atStep F μ N) - CI.softUpR.η / 2 < uNode (F.step N) ((N : ℤ) - (((lo + n.val : ℕ) : ℤ))) := by
    push_cast; exact hgt n
  have e := psiHatL_of_gt CI.softUpR (atStep F μ N) (Xs k) N hg'
  simp only [Fin.val_mk]
  rw [e]
  ring

/-- **`host1_eq` for the left half of the upper soft edge**: `H^{[m+1]}_c = sigma^{[m+1]} phi^{[m+1]}_2` is the entry of the order-`(m+1)` host `compMatrix CI1 spl1` (`sigma^{[m+1]}_k = lambda_L^{[m+1]}/(kappa_bal^{[m+1]} hat N^{[m+1]})`);
the row conditions are those of the order-`(m+1)` chart (`n_c, u_c, eta` of `CI1`). -/
theorem softUp_host1_eq_left (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (CI1 : ChartInputs F K Kidx t0 (m + 1) q U V cPC CPC)
    {Jlo Jhi ulo uhi : (Par × ℝ) → ℝ}
    (TI : TransferInputsDn (frozenFamily F Kidx) (paramSet K t0) Jlo Jhi m CI.softUpL.chain CI1.softUpL.chain 2 ulo uhi)
    (spl1 : Fin CI1.nb → ℝ) (μ : Par) (N : ℕ) (hp : atStep F μ N ∈ paramSet K t0) (hNT : TI.N0 ≤ N) (Xs : Fin (N + 1) → ℝ)
    (cols : Finset (Fin (N + 1))) (hcols : ∀ k ∈ cols, (¬ ∃ ν : Fin CI1.nb, CI1.lo ν ≤ Xs k ∧ Xs k ≤ CI1.hi ν) ∧ CI1.Jhi < Xs k)
    (hX : ∀ k : cols, Xs k ∈ Set.Icc (Jlo (atStep F μ N)) (Jhi (atStep F μ N)))
    (lo R : ℕ) (hlo : lo + R ≤ N + 1)
    (hle : ∀ n : Fin R, ((lo : ℤ) + n) ≤ nearestRow (F.step N) (CI1.softUpL.uc (atStep F μ N)))
    (hgt : ∀ n : Fin R, CI1.softUpL.uc (atStep F μ N) - CI1.softUpL.η / 2 < uNode (F.step N) ((lo : ℤ) + n))
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 : cols → ℝ) (host0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∀ n k, (softJBChart CI.softUpL CI1.softUpL TI (atStep F μ N) N Xs cols lo R hlo false used Pk σ0
        (fun k => CI1.softUpL.lamL (atStep F μ N) (Xs k) N /
          (kappaBal (CI1.softUpL.aOf (atStep F μ N) (Xs k) N) * softNorm CI1.softUpL CI1.softUpR (atStep F μ N) (Xs k) N))
        host0 (compMatrix CI1 spl1 μ N Xs)).H1 (F.step N) n k =
      (softJBChart CI.softUpL CI1.softUpL TI (atStep F μ N) N Xs cols lo R hlo false used Pk σ0
        (fun k => CI1.softUpL.lamL (atStep F μ N) (Xs k) N /
          (kappaBal (CI1.softUpL.aOf (atStep F μ N) (Xs k) N) * softNorm CI1.softUpL CI1.softUpR (atStep F μ N) (Xs k) N))
        host0 (compMatrix CI1 spl1 μ N Xs)).host1
        ((softJBChart CI.softUpL CI1.softUpL TI (atStep F μ N) N Xs cols lo R hlo false used Pk σ0
          (fun k => CI1.softUpL.lamL (atStep F μ N) (Xs k) N /
            (kappaBal (CI1.softUpL.aOf (atStep F μ N) (Xs k) N) * softNorm CI1.softUpL CI1.softUpR (atStep F μ N) (Xs k) N))
          host0 (compMatrix CI1 spl1 μ N Xs)).row n) k := by
  intro n k
  erw [softJBChart_H1 CI.softUpL CI1.softUpL TI (atStep F μ N) hp N hNT Xs cols lo R hlo false used Pk _ _ _ _ hX]
  have hk := hcols k k.2
  simp only [softJBChart, FormalResearch.JB.Chart.row]
  rw [compMatrix_softUp_entry CI1 spl1 μ N Xs k hk.1 hk.2]
  have hn : ((((lo + n.val : ℕ)) : ℤ) ≤ nearestRow (F.step N) (CI1.softUpL.uc (atStep F μ N))) := by
    have := hle n
    push_cast; exact this
  rw [ite_eq_left hn]
  have hcr : chartRowDn N lo R false n = (((lo + n.val : ℕ) : ℤ)) := by simp [chartRowDn]
  rw [hcr]
  have hg := hgt n
  have hg' : CI1.softUpL.uc (atStep F μ N) - CI1.softUpL.η / 2 < uNode (F.step N) (((lo + n.val : ℕ) : ℤ)) := by
    push_cast; exact hg
  rw [psiHatL_of_gt _ _ _ _ hg']
  ring

/-- **`host1_eq` for the right half of the upper soft edge** (mirror chart; `sigma^{[m+1]}_k = hat kappa^{[m+1]} lambda_R^{[m+1]}/(kappa_bal^{[m+1]} hat N^{[m+1]})`). -/
theorem softUp_host1_eq_right (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (CI1 : ChartInputs F K Kidx t0 (m + 1) q U V cPC CPC)
    {Jlo Jhi ulo uhi : (Par × ℝ) → ℝ}
    (TI : TransferInputsDn (mirrorFamily (frozenFamily F Kidx)) (paramSet K t0) Jlo Jhi m CI.softUpR.chain CI1.softUpR.chain 2 ulo uhi)
    (spl1 : Fin CI1.nb → ℝ) (μ : Par) (N : ℕ) (hp : atStep F μ N ∈ paramSet K t0) (hNT : TI.N0 ≤ N) (Xs : Fin (N + 1) → ℝ)
    (cols : Finset (Fin (N + 1))) (hcols : ∀ k ∈ cols, (¬ ∃ ν : Fin CI1.nb, CI1.lo ν ≤ Xs k ∧ Xs k ≤ CI1.hi ν) ∧ CI1.Jhi < Xs k)
    (hX : ∀ k : cols, Xs k ∈ Set.Icc (Jlo (atStep F μ N)) (Jhi (atStep F μ N)))
    (lo R : ℕ) (hlo : lo + R ≤ N + 1)
    (hgtn : ∀ n : Fin R, nearestRow (F.step N) (CI1.softUpL.uc (atStep F μ N)) < (lo : ℤ) + n)
    (hgt : ∀ n : Fin R, CI1.softUpR.uc (atStep F μ N) - CI1.softUpR.η / 2 < uNode (F.step N) ((N : ℤ) - ((lo : ℤ) + n)))
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 : cols → ℝ) (host0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∀ n k, (softJBChart CI.softUpR CI1.softUpR TI (atStep F μ N) N Xs cols lo R hlo true used Pk σ0
        (fun k => softKappa CI1.softUpL CI1.softUpR (atStep F μ N) (Xs k) N * CI1.softUpR.lamL (atStep F μ N) (Xs k) N /
          (kappaBal (CI1.softUpR.aOf (atStep F μ N) (Xs k) N) * softNorm CI1.softUpL CI1.softUpR (atStep F μ N) (Xs k) N))
        host0 (compMatrix CI1 spl1 μ N Xs)).H1 (F.step N) n k =
      (softJBChart CI.softUpR CI1.softUpR TI (atStep F μ N) N Xs cols lo R hlo true used Pk σ0
        (fun k => softKappa CI1.softUpL CI1.softUpR (atStep F μ N) (Xs k) N * CI1.softUpR.lamL (atStep F μ N) (Xs k) N /
          (kappaBal (CI1.softUpR.aOf (atStep F μ N) (Xs k) N) * softNorm CI1.softUpL CI1.softUpR (atStep F μ N) (Xs k) N))
        host0 (compMatrix CI1 spl1 μ N Xs)).host1
        ((softJBChart CI.softUpR CI1.softUpR TI (atStep F μ N) N Xs cols lo R hlo true used Pk σ0
          (fun k => softKappa CI1.softUpL CI1.softUpR (atStep F μ N) (Xs k) N * CI1.softUpR.lamL (atStep F μ N) (Xs k) N /
            (kappaBal (CI1.softUpR.aOf (atStep F μ N) (Xs k) N) * softNorm CI1.softUpL CI1.softUpR (atStep F μ N) (Xs k) N))
          host0 (compMatrix CI1 spl1 μ N Xs)).row n) k := by
  intro n k
  erw [softJBChart_H1 CI.softUpR CI1.softUpR TI (atStep F μ N) hp N hNT Xs cols lo R hlo true used Pk _ _ _ _ hX]
  have hk := hcols k k.2
  simp only [softJBChart, FormalResearch.JB.Chart.row]
  rw [compMatrix_softUp_entry CI1 spl1 μ N Xs k hk.1 hk.2]
  have hn : ¬ ((((lo + n.val : ℕ)) : ℤ) ≤ nearestRow (F.step N) (CI1.softUpL.uc (atStep F μ N))) := by
    have := hgtn n
    push_cast; omega
  rw [ite_eq_right hn]
  have hcr : chartRowDn N lo R true n = (N : ℤ) - (((lo + n.val : ℕ) : ℤ)) := by simp [chartRowDn]
  rw [hcr]
  have hg' : CI1.softUpR.uc (atStep F μ N) - CI1.softUpR.η / 2 < uNode (F.step N) ((N : ℤ) - (((lo + n.val : ℕ) : ℤ))) := by
    push_cast; exact hgt n
  have e := psiHatL_of_gt CI1.softUpR (atStep F μ N) (Xs k) N hg'
  simp only [Fin.val_mk]
  rw [e]
  ring

end HostEntries

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_transfer_row_dn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_transfer_row_dn

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.softJBChart_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms softJBChart_shifted

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.softJBChart_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms softJBChart_coeff

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.softJBChart_H0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms softJBChart_H0

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.softJBChart_H1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms softJBChart_H1

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.compMatrix_softUp_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compMatrix_softUp_entry

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.softUp_host0_eq_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms softUp_host0_eq_left

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.softUp_host0_eq_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms softUp_host0_eq_right

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.softUp_host1_eq_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms softUp_host1_eq_left

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.softUp_host1_eq_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms softUp_host1_eq_right

end FormalResearch.JacobiEigenvectors.TheoremB

end
