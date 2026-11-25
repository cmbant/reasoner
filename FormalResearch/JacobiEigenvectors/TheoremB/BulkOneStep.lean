module

public import Mathlib
public import FormalResearch.JB.JBOneStepDef
public import FormalResearch.JacobiEigenvectors.TheoremB.BulkSchur
public import FormalResearch.JacobiEigenvectors.TheoremB.BulkWindow
public import FormalResearch.JacobiEigenvectors.TheoremB.Statements

/-!
# Paper J, Theorem B, L3.5a (bulk charts to `JB.Chart`): the coefficient fields of `JB.Chart.Ok`, host entries

Source: Paper J `app_thmB.tex`, "(I2) and the changed coefficient: bulk charts" (the exact model transfer, `omega_n = sqrt(s_n)`, `|t_12| >= c_T`, `alpha >= c_alpha`, the five Schur multipliers),
`thmB.tex` `eq:thb-parity`, `eq:thb-bulkcol`, `def:thb-inputs` (I2).

## Proved here

* `bulkJBChart`: the `JB.Chart` of a bulk Weber chart pair `(C, C1)` (orders `m`, `m + 1` on the same ladder, `TransferInputs` `TI`), sampled at the energies `Xc k`, `k in cols`, with the rows `chartRow` (`tau = true`: the chain
  rows `lo + n`; `tau = false`, the mirror chart: the chain rows `N - (lo + n)` of the mirror family), the model pair `y, y~ = wf` of the order-`m` chain, `omega_n = sqrt(u_n + h/2)` (`= D_+(u_n)`, `dd_sqrt`),
  `t_11, t_12 = Pi_{+,00}, Pi_{+,01}`, the corrector rows `A^{[r]}, B^{[r]}` of the two chains and `kappa` of `TI`, the exterior row `y_ext` at the chain row next to the chart (`chartExtRow`), and the
  *design data* (`used`, `P_k`, `sigma^{[r]}`, hosts) as parameters.
* `chart_transfer_row`, `bulkJBChart_shifted`: the exact model transfer `omega_n y_{n+tau} = t_11 y_n + t_12 y~_n` (`SymplecticLadder.shift_up`, first component), including the exterior row, for both directions.
* `ChartOkCoeff`: the fields of `JB.Chart.Ok` that depend only on the coefficients: `omega_pos`, `transfer`, `t12_lb`, `alpha_lb`, the five `schur_*`, `parity_A`, `parity_B`.
* `bulkJBChart_coeff`: **all of `ChartOkCoeff` for `bulkJBChart`**, for every design data, from `TransferInputs` (`reg_*`, `t12_lb`, `alpha_lb`, `parity_*`, `omega_pos_le`, `same_ladder`), `shift_up` and `chart_schur_five` (BulkSchur).
* `ChartOkCoeff.ok`: `JB.Chart.Ok` from `ChartOkCoeff` and the seven design fields (`host0_eq`, `host1_eq`, `host0_col`, `host1_col`, `ext_row`, `overlap_lb`, `overlap_ub`).
* Host entries: `bulkJBChart_H0`, `bulkJBChart_H1` (`H^{[r]}_c = sigma psi-hat` on the chart rows), `blockCols`, `blockCols_disjoint` (**`cols_disjoint`**), `compMatrix_bulk_entry` (the entry of `compMatrix` on a bulk column is
  `psi-hat^L/hat N` for rows `<= n_nu`, `hat kappa psi-hat^R/hat N` beyond: eq:thb-bulkcol), and **`host0_eq`** for the left chart (`bulk_host0_eq_left`, `sigma = 1/hat N`, rows `<= n_nu`) and the right chart
  (`bulk_host0_eq_right`, mirror, `sigma = hat kappa/hat N`, rows `> n_nu`), with the host `compMatrix CI0 spl`.

## Differences from the paper

* `omega_n` is `sqrt(u_n + h/2)` (the Weber ladder has `D(s,h) = sqrt s`), the same for both orders and every column.
* The Schur constant `cs.K` must dominate `chartSchurK 0 (c + sigma/2) Jlo Jhi S c_T c_alpha H` (`|h| <= H`); `c_T`, `c_alpha`, `omega_max` of `cs` are below/above those of `TransferInputs` (hypotheses of `bulkJBChart_coeff`).
* The chart `C1` of order `m + 1` has its own energy interval `[Jlo1, Jhi1]`, assumed equal to the one of `C` (`ChartPair.lo_eq`, `hi_eq`).

## FINDING F-B11 (block choice for the second order; **applied**: `blockIdx` in `ComparisonMatrix.lean`)

`compColumn CI spl mu N X` used to pick the bulk block of the energy `X` by `Classical.choose` of `exists nu, lo nu <= X <= hi nu`, separately for `CI0` and `CI1`.  When blocks overlap the two choices need not correspond under `Fin.cast CP.nb_eq`,
and then the column of `compMatrix CI1` of a block-`nu` column of `compMatrix CI0` is built from a different block (its profile is `psi-hat` of another overlap window, equal only up to `O(h^m)`), so `host1_eq` / `match1`
of `OneStepInputs` (`H^{[m+1]}_c` of the block-`nu` chart is a submatrix of `compMatrix CI1`) fails for such columns.  **Applied correction**: `compColumn` and `blockOf` take the *least* block index (`blockIdx`, `blockIdx_spec`, `blockIdx_min`);
`lo_eq`, `hi_eq` of `ChartPair` then make the choices for the two orders correspond (`blockIdx_cast`, `blockOf_cast` in `BulkOneStep2.lean`).  `TwoOrdersBulk` (`compMatrix_bulk_col`) was changed only to use `blockIdx_spec` in place of `Classical.choose_spec`;
its headline theorems and axiom pins are unchanged.  `host0_eq` (one order) needed no change; `host1_eq` is in `BulkOneStep2.lean`.

## Not formalised here

`host1_eq`, `match0/1`, `ext_row`, `overlap_lb`, `overlap_ub` for the bulk charts are in `BulkOneStep2.lean` (with the exact remaining assembly items listed there).  Still open: `host0_col`, `host1_col` for the soft columns (the soft half),
`OneStepInputs.outside`, `G1_col`, `eps5`, the choice of `lo`, `R`, `used`, `P_k`, the extreme splices `n^pm_nu` and the existence of the constants `cs`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

open scoped Classical

/-- The chain row of the chart row `n` of a chart with global rows `lo .. lo + R - 1`: the row itself (`tau = true`), or its mirror `N - (lo + n)` (`tau = false`, the mirror chart). -/
def chartRow (N lo R : ℕ) (τ : Bool) (n : Fin R) : ℤ := if τ then (lo : ℤ) + n else (N : ℤ) - ((lo : ℤ) + n)

/-- The chain row of the exterior row of the chart (the row next to the chart in direction `tau`). -/
def chartExtRow (N lo R : ℕ) (τ : Bool) : ℤ := if τ then (lo : ℤ) + R else (N : ℤ) - lo + 1

/-- **The `JB.Chart` of a bulk chart pair** `(C, C1)` (orders `m`, `m+1` on the same ladder, with `TransferInputs` `TI`), sampled at the energies `Xc k`, `k in cols`; see the module docstring.
The design data (`used`, `Pk`, `sigma0`, `sigma1`, `host0`, `host1`) are parameters. -/
def bulkJBChart {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi Jlo1 Jhi1 : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (C : BulkWeberChart G P Jlo Jhi m U V) (C1 : BulkWeberChart G P Jlo1 Jhi1 (m + 1) U V)
    (TI : TransferInputs G P (fun _ => Jlo) (fun _ => Jhi) m C.chain C1.chain 1 (fun _ => 0) (fun _ => C.c + C.σ / 2))
    (p : Par × ℝ) (N : ℕ) (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (lo R : ℕ) (hlo : lo + R ≤ N + 1) (τ : Bool)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 σ1 : cols → ℝ)
    (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : FormalResearch.JB.Chart (N + 1) R cols where
  lo := lo
  lo_add := hlo
  τ := τ
  used := used
  y := Matrix.of fun n k => (C.chain p (Xc k) N).wf 1 0 (uNode (G.step N) (chartRow N lo R τ n)) (G.step N) 0
  yt := Matrix.of fun n k => (C.chain p (Xc k) N).wf 1 0 (uNode (G.step N) (chartRow N lo R τ n)) (G.step N) 1
  yext := fun k => (C.chain p (Xc k) N).wf 1 0 (uNode (G.step N) (chartExtRow N lo R τ)) (G.step N) 0
  ω := fun n => Real.sqrt (uNode (G.step N) (chartRow N lo R τ n) + G.step N / 2)
  t11 := Matrix.of fun n k => (C1.chain p (Xc k) N).PiP 1 (uNode (G.step N) (chartRow N lo R τ n)) (G.step N) 0 0
  t12 := Matrix.of fun n k => (C1.chain p (Xc k) N).PiP 1 (uNode (G.step N) (chartRow N lo R τ n)) (G.step N) 0 1
  A0 := Matrix.of fun n k => (C.chain p (Xc k) N).AA 1 (uNode (G.step N) (chartRow N lo R τ n)) (G.step N)
  A1 := Matrix.of fun n k => (C1.chain p (Xc k) N).AA 1 (uNode (G.step N) (chartRow N lo R τ n)) (G.step N)
  B0 := Matrix.of fun n k => (C.chain p (Xc k) N).BB 1 (uNode (G.step N) (chartRow N lo R τ n)) (G.step N)
  B1 := Matrix.of fun n k => (C1.chain p (Xc k) N).BB 1 (uNode (G.step N) (chartRow N lo R τ n)) (G.step N)
  κ := Matrix.of fun n k => TI.κ p (Xc k) N (uNode (G.step N) (chartRow N lo R τ n))
  σ0 := σ0
  σ1 := σ1
  P := Pk
  host0 := host0
  host1 := host1

/-- The fields of `JB.Chart.Ok` that depend only on the coefficients of the chart (not on the design data `used`, `P_k`, `sigma`, hosts). -/
structure ChartOkCoeff {D R : ℕ} {cols : Finset (Fin D)} (cs : FormalResearch.JB.OneStepConsts) (m : ℕ) (h : ℝ)
    (c : FormalResearch.JB.Chart D R cols) : Prop where
  parity_A : ∀ n k, c.A1 n k - c.A0 n k = (1 - ((m % 2 : ℕ) : ℝ)) * h ^ m * c.κ n k
  parity_B : ∀ n k, h * (c.B1 n k - c.B0 n k) = ((m % 2 : ℕ) : ℝ) * h ^ m * c.κ n k
  ω_pos : ∀ n, 0 < c.ω n ∧ c.ω n ≤ cs.ωmax
  transfer : ∀ n k, c.ω n * c.shifted c.y n k = c.t11 n k * c.y n k + c.t12 n k * c.yt n k
  t12_lb : ∀ n k, cs.cT ≤ |c.t12 n k|
  α_lb : ∀ n k, cs.cα ≤ FormalResearch.JB.jbAlpha c.A1 c.B1 c.t11 c.t12 h n k
  schur_inv_α : FormalResearch.JB.IsSchurBdd
    (Matrix.of fun n k => 1 / FormalResearch.JB.jbAlpha c.A1 c.B1 c.t11 c.t12 h n k) cs.K
  schur_B : FormalResearch.JB.IsSchurBdd
    (Matrix.of fun n k => c.B1 n k / (c.t12 n k * FormalResearch.JB.jbAlpha c.A1 c.B1 c.t11 c.t12 h n k)) cs.K
  schur_inv_t12 : FormalResearch.JB.IsSchurBdd (Matrix.of fun n k => 1 / c.t12 n k) cs.K
  schur_t11 : FormalResearch.JB.IsSchurBdd (Matrix.of fun n k => c.t11 n k / c.t12 n k) cs.K
  schur_κ : FormalResearch.JB.IsSchurBdd c.κ cs.K

/-- `JB.Chart.Ok` from the coefficient fields and the seven design fields. -/
theorem ChartOkCoeff.ok {D R : ℕ} {cols : Finset (Fin D)} {cs : FormalResearch.JB.OneStepConsts} {m : ℕ} {h : ℝ}
    {U : Matrix (Fin D) (Fin D) ℝ} {c : FormalResearch.JB.Chart D R cols} (hc : ChartOkCoeff cs m h c)
    (host0_eq : ∀ n k, c.H0 h n k = c.host0 (c.row n) k) (host1_eq : ∀ n k, c.H1 h n k = c.host1 (c.row n) k)
    (host0_col : ∀ j : Fin D, FormalResearch.JB.jbL2 Finset.univ (fun i => c.host0 i j - U i j) ≤ cs.C * h ^ m)
    (host1_col : ∀ j : Fin D, FormalResearch.JB.jbL2 Finset.univ (fun i => c.host1 i j - U i j) ≤ cs.C * h ^ (m + 1) * Real.log (1 / h))
    (ext_row : ∀ n : Fin R, (c.τ = true → n.val + 1 = R) → (c.τ = false → n.val = 0) →
      FormalResearch.JB.jbL2 Finset.univ (fun k => c.ω n * c.σ1 k * c.yext k) ≤ cs.CE)
    (overlap_lb : ∀ k : cols, cs.c0 ≤ FormalResearch.JB.jbL2 (c.P k) (fun n => U (c.row n) k))
    (overlap_ub : ∀ k : cols, FormalResearch.JB.jbL2 (c.P k) (fun n => c.y n k) + FormalResearch.JB.jbL2 (c.P k) (fun n => c.yt n k) ≤
      cs.C4 * FormalResearch.JB.jbL2 (c.P k) (fun n => c.phi1 h n k)) :
    c.Ok cs m h U where
  host0_eq := host0_eq
  host1_eq := host1_eq
  host0_col := host0_col
  host1_col := host1_col
  parity_A := hc.parity_A
  parity_B := hc.parity_B
  ω_pos := hc.ω_pos
  transfer := hc.transfer
  t12_lb := hc.t12_lb
  α_lb := hc.α_lb
  schur_inv_α := hc.schur_inv_α
  schur_B := hc.schur_B
  schur_inv_t12 := hc.schur_inv_t12
  schur_t11 := hc.schur_t11
  schur_κ := hc.schur_κ
  ext_row := ext_row
  overlap_lb := overlap_lb
  overlap_ub := overlap_ub

/-! ### The exact model transfer along the chain -/

/-- **The exact one-step model transfer of a bulk chart** (`SymplecticLadder.shift_up`, first component): at a lattice row `r >= 0`,
`sqrt(u_r + h/2) y_{r+1} = Pi_{+,00}(u_r) y_r + Pi_{+,01}(u_r) y~_r` for the model pair `(y, y~) = wf` of the chain. -/
theorem chart_transfer_row {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi : ℝ} {m : ℕ}
    {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : X ∈ Set.Icc Jlo Jhi)
    {N : ℕ} (hN : C.N0 ≤ N) (r : ℤ) (hr : 0 ≤ r) :
    Real.sqrt (uNode (G.step N) r + G.step N / 2) * (C.chain p X N).wf 1 0 (uNode (G.step N) (r + 1)) (G.step N) 0 =
      (C.chain p X N).PiP 1 (uNode (G.step N) r) (G.step N) 0 0 * (C.chain p X N).wf 1 0 (uNode (G.step N) r) (G.step N) 0 +
        (C.chain p X N).PiP 1 (uNode (G.step N) r) (G.step N) 0 1 * (C.chain p X N).wf 1 0 (uNode (G.step N) r) (G.step N) 1 := by
  have hst : 0 < G.step N := FormalResearch.JB.stepSize_pos G.L_pos N
  have hV := C.valid p hp X hX N hN
  obtain ⟨hP1, -, -, -, -⟩ := C.shape p hp X hX N hN
  have hL := hV.ladder 1 (Finset.mem_Icc.mpr ⟨le_rfl, by rw [hP1]⟩)
  have hsite : IsSite (1 / 2) (G.step N) (uNode (G.step N) r) := by
    refine ⟨r.toNat, ?_⟩
    unfold uNode
    have h2 : ((r.toNat : ℕ) : ℝ) = (r : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hr
    rw [h2]
  have h1 := (shift_up_comp hL 0 (uNode (G.step N) r) (G.step N) hst hsite).1
  have e : uNode (G.step N) r + G.step N = uNode (G.step N) (r + 1) := by
    unfold uNode; push_cast; ring
  rw [e] at h1
  have hd : Dp ((C.chain p X N).dd 1) (uNode (G.step N) r) (G.step N) = Real.sqrt (uNode (G.step N) r + G.step N / 2) := by
    unfold Dp
    exact (C.dd_sqrt p hp X hX N hN _ _).1
  rw [hd] at h1
  exact h1

/-- The shifted carrier of the sampled chart: `y_{n + tau}` is the model pair at the chain row next to `chartRow n`. -/
theorem bulkJBChart_shifted {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi Jlo1 Jhi1 : ℝ} {m : ℕ}
    {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (C1 : BulkWeberChart G P Jlo1 Jhi1 (m + 1) U V)
    (TI : TransferInputs G P (fun _ => Jlo) (fun _ => Jhi) m C.chain C1.chain 1 (fun _ => 0) (fun _ => C.c + C.σ / 2))
    (p : Par × ℝ) (N : ℕ) (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (lo R : ℕ) (hlo : lo + R ≤ N + 1) (τ : Bool)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 σ1 : cols → ℝ)
    (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (n : Fin R) (k : cols) :
    (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).shifted
        (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).y n k =
      (C.chain p (Xc k) N).wf 1 0 (uNode (G.step N) (chartRow N lo R τ n + 1)) (G.step N) 0 := by
  have key : ∀ A B : ℤ, A = B → (C.chain p (Xc k) N).wf 1 0 (uNode (G.step N) A) (G.step N) 0 =
      (C.chain p (Xc k) N).wf 1 0 (uNode (G.step N) B) (G.step N) 0 := fun A B h => by rw [h]
  cases τ
  · simp only [FormalResearch.JB.Chart.shifted, bulkJBChart, Bool.false_eq_true, ite_false, Matrix.of_apply]
    unfold FormalResearch.JB.YshRev
    by_cases hn : 0 < n.val
    · rw [dite_eq_left hn]
      simp only [Matrix.of_apply, chartRow, Bool.false_eq_true, ite_false]
      refine key _ _ ?_
      omega
    · rw [dite_eq_right hn]
      simp only [chartExtRow, chartRow, Bool.false_eq_true, ite_false]
      refine key _ _ ?_
      omega
  · simp only [FormalResearch.JB.Chart.shifted, bulkJBChart, ite_true, Matrix.of_apply]
    unfold FormalResearch.JB.Ysh
    by_cases hn : n.val + 1 < R
    · rw [dite_eq_left hn]
      simp only [Matrix.of_apply, chartRow, ite_true]
      refine key _ _ ?_
      omega
    · rw [dite_eq_right hn]
      simp only [chartExtRow, chartRow, ite_true]
      refine key _ _ ?_
      omega

/-- **The coefficient fields of `JB.Chart.Ok` for a bulk chart** (all design data arbitrary): `omega_pos`, the exact model `transfer`, `t12_lb`, `alpha_lb`, the five Schur bounds and the parity identities,
from `TransferInputs` (the primitive `C^2`, lower-bound and parity inputs), `shift_up` (`chart_transfer_row`) and `chart_schur_five`.  The chart rows must be rows of the chain (`0 <= row`, `u_row <= c`);
`cs` dominates the chart constants (`c_T`, `c_alpha`, `omega_max`, and the Schur constant `chartSchurK ..` for `|h| <= H`). -/
theorem bulkJBChart_coeff {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi Jlo1 Jhi1 : ℝ} {m : ℕ}
    {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (C1 : BulkWeberChart G P Jlo1 Jhi1 (m + 1) U V)
    (TI : TransferInputs G P (fun _ => Jlo) (fun _ => Jhi) m C.chain C1.chain 1 (fun _ => 0) (fun _ => C.c + C.σ / 2))
    (cs : FormalResearch.JB.OneStepConsts) {p : Par × ℝ} (hp : p ∈ P) (N : ℕ) (hN : max C.N0 C1.N0 ≤ N) (hNT : TI.N0 ≤ N)
    (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (lo R : ℕ) (hlo : lo + R ≤ N + 1) (τ : Bool)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 σ1 : cols → ℝ)
    (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hX : ∀ k : cols, Xc k ∈ Set.Icc Jlo Jhi) (hJ1 : Jlo = Jlo1) (hJ2 : Jhi = Jhi1)
    (hrows : ∀ n : Fin R, 0 ≤ chartRow N lo R τ n ∧ uNode (G.step N) (chartRow N lo R τ n) ≤ C.c)
    (H : ℝ) (hH : |G.step N| ≤ H) (hcT : cs.cT ≤ TI.cT) (hcα : cs.cα ≤ TI.cα) (hω : TI.ωmax ≤ cs.ωmax)
    (hK : chartSchurK 0 (C.c + C.σ / 2) Jlo Jhi TI.S TI.cT TI.cα H ≤ cs.K) :
    ChartOkCoeff cs m (G.step N) (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1) := by
  subst hJ1 hJ2
  have hN0 : C.N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : C1.N0 ≤ N := le_trans (le_max_right _ _) hN
  have hst : 0 < G.step N := FormalResearch.JB.stepSize_pos G.L_pos N
  obtain ⟨hc'0, hc'c, hσ, hcσ, hcH, hcM, hcMCM, hc3, hCs, hJ⟩ := C.consts_pos
  have hJlo : Jlo ∈ Set.Icc Jlo Jhi := ⟨le_rfl, hJ⟩
  -- the sampled rows lie on the rectangle
  have hu : ∀ n : Fin R, uNode (G.step N) (chartRow N lo R τ n) ∈ Set.Icc ((fun _ : Par × ℝ => (0 : ℝ)) p) ((fun _ : Par × ℝ => C.c + C.σ / 2) p) := by
    intro n
    obtain ⟨h0, h1⟩ := hrows n
    refine ⟨?_, by simp only; linarith⟩
    unfold uNode
    have : (0 : ℝ) ≤ ((chartRow N lo R τ n : ℤ) : ℝ) := by exact_mod_cast h0
    simp only
    positivity
  have hsame := fun k : cols => TI.same_ladder p hp (Xc k) (hX k) N hNT
  -- the five Schur bounds
  have hab : (0 : ℝ) ≤ C.c + C.σ / 2 := by linarith
  have hcTp : 0 < TI.cT := TI.consts_pos.2.1
  have hcαp : 0 < TI.cα := TI.consts_pos.2.2.1
  have hfive := chart_schur_five (a := 0) (b := C.c + C.σ / 2) (c := Jlo) (d := Jhi) (S := TI.S) (cT := TI.cT) (cα := TI.cα) (H := H)
    hab hJ hcTp hcαp
    (fun u X => (C1.chain p X N).AA 1 u (G.step N)) (fun u X => (C1.chain p X N).BB 1 u (G.step N))
    (fun u X => (C1.chain p X N).PiP 1 u (G.step N) 0 0) (fun u X => (C1.chain p X N).PiP 1 u (G.step N) 0 1)
    (fun u X => TI.κ p X N u) (G.step N) hH
    (TI.reg_A1 p hp N hNT) (TI.reg_B1 p hp N hNT) (TI.reg_t11 p hp N hNT) (TI.reg_t12 p hp N hNT) (TI.reg_κ p hp N hNT)
    (fun t ht X hXm => TI.t12_lb p hp X hXm N hNT t ht) (fun t ht X hXm => TI.alpha_lb p hp X hXm N hNT t ht)
  obtain ⟨-, hS⟩ := hfive
  obtain ⟨b1, b2, b3, b4, b5⟩ := hS (Fin R) cols (fun n => uNode (G.step N) (chartRow N lo R τ n)) (fun k => Xc k) (fun n => hu n) (fun k => hX k)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n k
    exact TI.parity_A p hp (Xc k) (hX k) N hNT _ (hu n)
  · intro n k
    exact TI.parity_B p hp (Xc k) (hX k) N hNT _ (hu n)
  · intro n
    obtain ⟨hnn, hlow⟩ := hrows n
    have hupos : 0 < uNode (G.step N) (chartRow N lo R τ n) := by
      unfold uNode
      have : (0 : ℝ) ≤ ((chartRow N lo R τ n : ℤ) : ℝ) := by exact_mod_cast hnn
      positivity
    refine ⟨?_, ?_⟩
    · show 0 < Real.sqrt _
      exact Real.sqrt_pos.mpr (by linarith)
    · have h2 := (TI.omega_pos_le p hp Jlo hJlo N hNT (chartRow N lo R τ n) (hu n).1 (hu n).2).2
      have hd : Dp ((C1.chain p Jlo N).dd 1) (uNode (G.step N) (chartRow N lo R τ n)) (G.step N) =
          Real.sqrt (uNode (G.step N) (chartRow N lo R τ n) + G.step N / 2) := by
        unfold Dp
        exact (C1.dd_sqrt p hp Jlo hJlo N hN1 _ _).1
      rw [hd] at h2
      exact h2.trans hω
  · intro n k
    rw [bulkJBChart_shifted]
    obtain ⟨hnn, -⟩ := hrows n
    have h1 := chart_transfer_row C hp (hX k) hN0 (chartRow N lo R τ n) hnn
    have hP := congrFun (congrFun (hsame k).1 (uNode (G.step N) (chartRow N lo R τ n))) (G.step N)
    show Real.sqrt _ * _ = _ * _ + _ * _
    simp only [bulkJBChart, Matrix.of_apply]
    rw [← hP]
    exact h1
  · intro n k
    exact hcT.trans (TI.t12_lb p hp (Xc k) (hX k) N hNT _ (hu n))
  · intro n k
    exact hcα.trans (TI.alpha_lb p hp (Xc k) (hX k) N hNT _ (hu n))
  exacts [b4.mono hK, b5.mono hK, b1.mono hK, b2.mono hK, b3.mono hK]

/-! ### Host entries: `H^{[m]}_c` is a submatrix of `compMatrix` -/

/-- **The model-profile identity**: `H^{[m]}_c = sigma_k psi-hat^L_{row n}` for the chart of a bulk chart `C` (any `sigma`): the profile `A y + h B y~` is the comparison sequence `psi-hat` (`phi = v . w`). -/
theorem bulkJBChart_H0 {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi Jlo1 Jhi1 : ℝ} {m : ℕ}
    {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (C1 : BulkWeberChart G P Jlo1 Jhi1 (m + 1) U V)
    (TI : TransferInputs G P (fun _ => Jlo) (fun _ => Jhi) m C.chain C1.chain 1 (fun _ => 0) (fun _ => C.c + C.σ / 2))
    (p : Par × ℝ) (N : ℕ) (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (lo R : ℕ) (hlo : lo + R ≤ N + 1) (τ : Bool)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 σ1 : cols → ℝ)
    (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (n : Fin R) (k : cols) :
    (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).H0 (G.step N) n k =
      σ0 k * C.psiHatL p (Xc k) N (chartRow N lo R τ n) := by
  simp only [FormalResearch.JB.Chart.H0_apply, FormalResearch.JB.Chart.phi0_apply, bulkJBChart, Matrix.of_apply]
  congr 1
  unfold BulkWeberChart.psiHatL
  rw [psiHat_one_eq]
  unfold LadderData.phi ladderSeq vrow dot uNode
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Same for order `m + 1`, with the chart `C1`. -/
theorem bulkJBChart_H1 {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi Jlo1 Jhi1 : ℝ} {m : ℕ}
    {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (C1 : BulkWeberChart G P Jlo1 Jhi1 (m + 1) U V)
    (TI : TransferInputs G P (fun _ => Jlo) (fun _ => Jhi) m C.chain C1.chain 1 (fun _ => 0) (fun _ => C.c + C.σ / 2))
    (p : Par × ℝ) (hp : p ∈ P) (N : ℕ) (hNT : TI.N0 ≤ N) (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (lo R : ℕ)
    (hlo : lo + R ≤ N + 1) (τ : Bool)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 σ1 : cols → ℝ)
    (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hX : ∀ k : cols, Xc k ∈ Set.Icc Jlo Jhi) (n : Fin R) (k : cols) :
    (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).H1 (G.step N) n k =
      σ1 k * C1.psiHatL p (Xc k) N (chartRow N lo R τ n) := by
  simp only [FormalResearch.JB.Chart.H1_apply, FormalResearch.JB.Chart.phi1_apply, bulkJBChart, Matrix.of_apply]
  congr 1
  unfold BulkWeberChart.psiHatL
  rw [psiHat_one_eq]
  unfold LadderData.phi ladderSeq vrow dot uNode
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hw : (C.chain p (Xc k) N).wf 1 = (C1.chain p (Xc k) N).wf 1 := (TI.same_ladder p hp (Xc k) (hX k) N hNT).2.1
  have hw := congrFun hw 0
  rw [← hw]
  ring


section HostEntries

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- The columns of the block `nu` (disjoint for different blocks: `blockOf` is a function). -/
def blockCols (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν : Fin CI.nb) : Finset (Fin (N + 1)) :=
  Finset.univ.filter fun k => blockOf CI (Xs k) = some ν

theorem blockCols_disjoint (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν ν' : Fin CI.nb) (h : ν ≠ ν') :
    Disjoint (blockCols CI N Xs ν) (blockCols CI N Xs ν') := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  simp only [blockCols, Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
  exact h (Option.some.inj (hk.symm.trans hk'))

/-- **The entries of `compMatrix` on a bulk column** (`eq:thb-bulkcol`): for `blockOf CI (Xs k) = some nu`, the entry in row `i` is `psi-hat^L_i / hat N` if `i <= n_nu` and `hat kappa psi-hat^R_i / hat N` otherwise
(`n_nu = nearestRow h (spl nu)`, `psi-hat^R_i = psi-hat^{L,mirror}_{N - i}`). -/
theorem compMatrix_bulk_entry (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (spl : Fin CI.nb → ℝ) (μ : Par) (N : ℕ)
    (Xs : Fin (N + 1) → ℝ) (ν : Fin CI.nb) (k : Fin (N + 1)) (hk : blockOf CI (Xs k) = some ν) (i : Fin (N + 1)) :
    compMatrix CI spl μ N Xs i k =
      if ((i : ℕ) : ℤ) ≤ nearestRow (F.step N) (spl ν) then
        (CI.bulkL ν).psiHatL (atStep F μ N) (Xs k) N i / bulkNorm (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) (Xs k) N
      else bulkKappa (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) (Xs k) N *
        (CI.bulkR ν).psiHatL (atStep F μ N) (Xs k) N ((N : ℤ) - ((i : ℕ) : ℤ)) / bulkNorm (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) (Xs k) N := by
  unfold blockOf at hk
  by_cases hex : ∃ ν', CI.lo ν' ≤ Xs k ∧ Xs k ≤ CI.hi ν'
  · rw [dite_eq_left hex] at hk
    have hν : blockIdx CI (Xs k) hex = ν := Option.some.inj hk
    simp only [compMatrix, Matrix.of_apply, compColumn, dite_eq_left hex]
    rw [hν]
    unfold bulkColAt glueVecAt
    split_ifs <;> rfl
  · rw [dite_eq_right hex] at hk
    exact absurd hk (by simp)

end HostEntries

section HostEq

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **`host0_eq` for the left chart of a block** (rows `0 .. R-1` of the left chart, all `<= n_nu`; direction `+`; `sigma_k = 1/hat N`): `H^{[m]}_c = sigma psi-hat^L` is the entry of the host
`compMatrix CI0 spl` (the host at the fixed splice `spl`; for the extreme splices `n^+_nu` take `spl` there).  The columns are those of the block (`blockOf`). -/
theorem bulk_host0_eq_left (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν : Fin CP.CI0.nb)
    (cols : Finset (Fin (N + 1))) (hcols : ∀ k ∈ cols, blockOf CP.CI0 (Xs k) = some ν) (R : ℕ) (hlo : 0 + R ≤ N + 1)
    (hR : ((R : ℤ) - 1) ≤ nearestRow (F.step N) (spl ν)) (used : Finset (Fin R)) (Pk : cols → Finset (Fin R))
    (σ1 : cols → ℝ) (host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∀ n k, (bulkJBChart (CP.CI0.bulkL ν) (CP.CI1.bulkL (Fin.cast CP.nb_eq.symm ν)) (TB.bulkL ν) (atStep F μ N) N Xs cols 0 R hlo true used Pk
        (fun k => 1 / bulkNorm (CP.CI0.bulkL ν) (CP.CI0.bulkR ν) (atStep F μ N) (Xs k) N) σ1 (compMatrix CP.CI0 spl μ N Xs) host1).H0
          (F.step N) n k =
      (bulkJBChart (CP.CI0.bulkL ν) (CP.CI1.bulkL (Fin.cast CP.nb_eq.symm ν)) (TB.bulkL ν) (atStep F μ N) N Xs cols 0 R hlo true used Pk
        (fun k => 1 / bulkNorm (CP.CI0.bulkL ν) (CP.CI0.bulkR ν) (atStep F μ N) (Xs k) N) σ1 (compMatrix CP.CI0 spl μ N Xs) host1).host0
        ((bulkJBChart (CP.CI0.bulkL ν) (CP.CI1.bulkL (Fin.cast CP.nb_eq.symm ν)) (TB.bulkL ν) (atStep F μ N) N Xs cols 0 R hlo true used Pk
        (fun k => 1 / bulkNorm (CP.CI0.bulkL ν) (CP.CI0.bulkR ν) (atStep F μ N) (Xs k) N) σ1 (compMatrix CP.CI0 spl μ N Xs) host1).row n) k := by
  intro n k
  erw [bulkJBChart_H0]
  have hk := hcols k k.2
  simp only [bulkJBChart, FormalResearch.JB.Chart.row]
  rw [compMatrix_bulk_entry CP.CI0 spl μ N Xs ν k hk]
  have hn : ((((0 : ℕ) + n.val : ℕ)) : ℤ) ≤ nearestRow (F.step N) (spl ν) := by
    have := n.isLt
    omega
  rw [ite_eq_left hn]
  have hcr : chartRow N 0 R true n = (((0 : ℕ) + n.val : ℕ) : ℤ) := by simp [chartRow]
  rw [hcr]
  ring

/-- **`host0_eq` for the right chart of a block** (mirror chart, direction `-`, rows `lo .. lo + R - 1`, all `> n_nu`; `sigma_k = hat kappa/hat N`). -/
theorem bulk_host0_eq_right (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν : Fin CP.CI0.nb)
    (cols : Finset (Fin (N + 1))) (hcols : ∀ k ∈ cols, blockOf CP.CI0 (Xs k) = some ν) (lo R : ℕ) (hlo : lo + R ≤ N + 1)
    (hR : nearestRow (F.step N) (spl ν) < (lo : ℤ)) (used : Finset (Fin R)) (Pk : cols → Finset (Fin R))
    (σ1 : cols → ℝ) (host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∀ n k, (bulkJBChart (CP.CI0.bulkR ν) (CP.CI1.bulkR (Fin.cast CP.nb_eq.symm ν)) (TB.bulkR ν) (atStep F μ N) N Xs cols lo R hlo false used Pk
        (fun k => bulkKappa (CP.CI0.bulkL ν) (CP.CI0.bulkR ν) (atStep F μ N) (Xs k) N /
          bulkNorm (CP.CI0.bulkL ν) (CP.CI0.bulkR ν) (atStep F μ N) (Xs k) N) σ1 (compMatrix CP.CI0 spl μ N Xs) host1).H0
          (F.step N) n k =
      (bulkJBChart (CP.CI0.bulkR ν) (CP.CI1.bulkR (Fin.cast CP.nb_eq.symm ν)) (TB.bulkR ν) (atStep F μ N) N Xs cols lo R hlo false used Pk
        (fun k => bulkKappa (CP.CI0.bulkL ν) (CP.CI0.bulkR ν) (atStep F μ N) (Xs k) N /
          bulkNorm (CP.CI0.bulkL ν) (CP.CI0.bulkR ν) (atStep F μ N) (Xs k) N) σ1 (compMatrix CP.CI0 spl μ N Xs) host1).host0
        ((bulkJBChart (CP.CI0.bulkR ν) (CP.CI1.bulkR (Fin.cast CP.nb_eq.symm ν)) (TB.bulkR ν) (atStep F μ N) N Xs cols lo R hlo false used Pk
        (fun k => bulkKappa (CP.CI0.bulkL ν) (CP.CI0.bulkR ν) (atStep F μ N) (Xs k) N /
          bulkNorm (CP.CI0.bulkL ν) (CP.CI0.bulkR ν) (atStep F μ N) (Xs k) N) σ1 (compMatrix CP.CI0 spl μ N Xs) host1).row n) k := by
  intro n k
  erw [bulkJBChart_H0]
  have hk := hcols k k.2
  simp only [bulkJBChart, FormalResearch.JB.Chart.row]
  rw [compMatrix_bulk_entry CP.CI0 spl μ N Xs ν k hk]
  have hn : ¬ ((((lo + n.val : ℕ)) : ℤ) ≤ nearestRow (F.step N) (spl ν)) := by
    omega
  rw [ite_eq_right hn]
  have hcr : chartRow N lo R false n = (N : ℤ) - (((lo + n.val : ℕ) : ℤ)) := by simp [chartRow]
  rw [hcr]
  ring

end HostEq

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.chart_transfer_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.chart_transfer_row

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChart_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChart_shifted

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChart_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChart_coeff

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.ChartOkCoeff.ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.ChartOkCoeff.ok

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChart_H0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChart_H0

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChart_H1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChart_H1

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.compMatrix_bulk_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.compMatrix_bulk_entry

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.blockCols_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.blockCols_disjoint

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulk_host0_eq_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulk_host0_eq_left

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulk_host0_eq_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulk_host0_eq_right

end FormalResearch.JacobiEigenvectors.TheoremB
