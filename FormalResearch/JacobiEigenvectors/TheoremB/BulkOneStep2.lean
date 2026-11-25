module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.BulkOneStep
public import FormalResearch.JacobiEigenvectors.TheoremB.TwoOrdersBulk

/-!
# Paper J, Theorem B, L3.5a (bulk charts to `JB.Chart`), part 2: the two-order block correspondence, `host1_eq`, `match*`, and the bulk design fields

Source: Paper J `thmB.tex` `eq:thb-bulkcol`, `def:thb-inputs` (I3), (I4), `app_thmB.tex` "Charts, bootstrap blocks and directions", "(I3)", "(I4)" (bulk), `app_thmA.tex` Step 2 of the bulk (window sums).

## Proved here

* `blockIdx_cast`, `blockOf_cast` (**finding F-B11, applied**): with `compColumn` choosing the *least* bulk block (`blockIdx`, `ComparisonMatrix.lean`), the blocks that the two orders `CI0` (order `m`) and `CI1` (order `m + 1`)
  of a `ChartPair` assign to the same energy correspond under `Fin.cast CP.nb_eq`.
* `blockChartL`, `blockChartR`: the `JB.Chart` of the left / right bulk chart of the block `nu` (`bulkJBChart` with the scalars and hosts of the paper: left `sigma = 1/hat N`, right `sigma = hat kappa/hat N`, each at its own order,
  hosts `compMatrix CI0 spl`, `compMatrix CI1 (spl1 spl)`); design data `used`, `P_k`, `lo`, `R` are parameters.
* `blockChartL_host0_eq`, `blockChartR_host0_eq`, **`blockChartL_host1_eq`, `blockChartR_host1_eq`**: the fields `host0_eq`, `host1_eq` of `JB.Chart.Ok`, both orders, both directions.
* `blockChartL_match0/1`, `blockChartR_match0/1`: `OneStepInputs.match0`, `match1` for the bulk charts: `hat G^{[r]}` at the *final* splice `splF` equals `H^{[r]}_c` on the used rows (chart rows `<= n_nu`, resp. `> n_nu`, of `splF`),
  although the chart's host may be built at an extreme splice (the scalars do not depend on the splice).
* `window_sum_lower_sub` (`subWin`, `subWindowConst`): `window_sum_lower` on a sub-window `[a, b]` of the oscillatory overlap, `c' <= a < b <= c`.
* `bulk_wf_bound`: `|y|, |y~| <= K_w C_M h^{1/4}` on the oscillatory part (chain `env`, `W_osc`, `M_osc`, `rho = rho~ = 1`).
* `bulkJBChart_phi1`: `phi^{[m+1]} = psi-hat^{L,[m+1]}` on the chart rows.
* **`bulkJBChart_overlap_ub`** (`overlap_ub`): `||P y|| + ||P y~|| <= C_4 ||P phi^{[m+1]}||` for `P_k = bulkPk` (chart rows with node in `[a, b]`, a sub-window of both orders' overlaps, covered by the chart rows).
* **`bulk_sigma_bound`**, **`bulkJBChart_ext_row`** (`ext_row`, (I3)): `|sigma^{[r]}| <= C_sigma h^{1/4}` (`PropThaW (2)`: `hat N >= c_N h^{-1/4}`, `|hat kappa| <= C_kappa`) and `||(omega sigma y_ext)|| <= C_E`
  (`sqrt(c+1) C_sigma K_w C_M sqrt L`) when the exterior row is a row of the oscillatory region.
* **`bulk_window_eig_lower`**, **`bulkJBChartL_overlap_lb`**, **`bulkJBChartR_overlap_lb`** (`overlap_lb`, (I4)): the eigenvector window mass `sum_{a <= u_i <= b} Psi_{k,i}^2 >= c_0^2` (from `bulk_conj1`, `bulk_env_sq_sum`,
  `window_sum_lower_sub`), transported to `||P_k Psi_k||` of the chart (`pk_sum_ge`; the right chart's window `[a, b]` is the global window `[L - b, L - a]`).
* `U_orth` of `OneStepInputs` is `IsEigenSystem.orth` (a field of the eigen-system hypothesis): nothing to prove.

## Differences from the paper

* `P_k` is the set of chart rows with node in a **fixed sub-window** `[a, b]` of the oscillatory overlaps, `max(c'_0, c'_1) <= a < b <= min(c_0, c_1)` (the paper takes the window `Omega_nu`; the chart rows end at the splice `n^+_nu`, strictly inside the window,
  so the part of `Omega_nu` that the chart covers is what is used, and it contains such a `[a, b]` with `b < spl^+`).  The chart rows must cover the global window (hypothesis `hcov`).
* The constants `c_0`, `C_4`, `C_E` depend on the chart pair, the bond bound `CA`, `[a, b]` and `C_sigma` only (not on `p`, `N`, the columns or the eigen-system); the threshold `h_1` likewise.
* `ext_row` is for any `n` with `chartRow n + 1 = ` the exterior row, which must be a row of the oscillatory region (`c' <= u <= c`): for the left chart `R - 1 = n^+_nu`, `R` in the window.

## Not formalised (exactly what is missing for the bulk charts of `OneStepInputs`)

* `host0_col`, `host1_col` (columns `j` of the host `compMatrix .. (extreme splice)`, for **every** `j`): bulk `j` is `twoOrders_bulk_columns` with `spl :=` the extreme splices (needs `SplicesInWindow` for them);
  soft `j` needs the soft half (`PropThaSpliceSoft`, `sum softEnv^2 <= C`, the lower-edge eigenvector `D_- Psi`).
* Assembly (L3.5c): the choice of `lo`, `R`, `used`, `[a, b]` (with the covering and exterior-row hypotheses above), the extreme splices `n^pm_nu`, passing from `StdAssump (frozenFamily F Kidx) (paramSet K t0)` to `t <= t1`
  (`BulkWeberChart.restrict`, F-t0) and from `ChartPair` to `StdAssump` of order `m + 1` (`(m+1)/2 = Kidx`) for `bulk_sigma_bound` of the order-`(m+1)` pair, the bond bound `CA` (`bondA_bound_of_EK`), the common constants `cs` (finitely many blocks),
  and `OneStepInputs.outside`, `G1_col`, `eps5` (the soft halves and `lem:tha-collar (1)`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

open scoped Classical

section Cast

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **Finding F-B11 (applied)**: the least blocks of the two orders correspond under `Fin.cast CP.nb_eq`. -/
theorem blockIdx_cast (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (X : ℝ) (h0 : ∃ ν : Fin CP.CI0.nb, CP.CI0.lo ν ≤ X ∧ X ≤ CP.CI0.hi ν) (h1 : ∃ ν : Fin CP.CI1.nb, CP.CI1.lo ν ≤ X ∧ X ≤ CP.CI1.hi ν) :
    Fin.cast CP.nb_eq (blockIdx CP.CI1 X h1) = blockIdx CP.CI0 X h0 := by
  apply le_antisymm
  · have hb0 := blockIdx_spec CP.CI0 X h0
    have hh : CP.CI1.lo (Fin.cast CP.nb_eq.symm (blockIdx CP.CI0 X h0)) ≤ X ∧ X ≤ CP.CI1.hi (Fin.cast CP.nb_eq.symm (blockIdx CP.CI0 X h0)) := by
      rw [CP.lo_eq, CP.hi_eq]
      simpa using hb0
    have := blockIdx_min CP.CI1 X h1 hh
    simpa [Fin.le_def] using this
  · have hb1 := blockIdx_spec CP.CI1 X h1
    have hh : CP.CI0.lo (Fin.cast CP.nb_eq (blockIdx CP.CI1 X h1)) ≤ X ∧ X ≤ CP.CI0.hi (Fin.cast CP.nb_eq (blockIdx CP.CI1 X h1)) := by
      rw [← CP.lo_eq, ← CP.hi_eq]
      exact hb1
    exact blockIdx_min CP.CI0 X h0 hh

/-- The block of order `m + 1` of an energy whose block of order `m` is `nu` is `Fin.cast CP.nb_eq.symm nu`. -/
theorem blockOf_cast (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (X : ℝ) (ν : Fin CP.CI0.nb) (h : blockOf CP.CI0 X = some ν) : blockOf CP.CI1 X = some (Fin.cast CP.nb_eq.symm ν) := by
  unfold blockOf at h ⊢
  by_cases h0 : ∃ ν' : Fin CP.CI0.nb, CP.CI0.lo ν' ≤ X ∧ X ≤ CP.CI0.hi ν'
  · rw [dite_eq_left h0] at h
    have hν : blockIdx CP.CI0 X h0 = ν := Option.some.inj h
    have h1 : ∃ ν' : Fin CP.CI1.nb, CP.CI1.lo ν' ≤ X ∧ X ≤ CP.CI1.hi ν' := by
      refine ⟨Fin.cast CP.nb_eq.symm ν, ?_, ?_⟩
      · rw [CP.lo_eq]; simpa using (hν ▸ (blockIdx_spec CP.CI0 X h0).1)
      · rw [CP.hi_eq]; simpa using (hν ▸ (blockIdx_spec CP.CI0 X h0).2)
    rw [dite_eq_left h1]
    congr 1
    apply Fin.ext
    have := congrArg Fin.val (blockIdx_cast CP X h0 h1)
    simp only [Fin.coe_cast] at this ⊢
    rw [this, hν]
  · rw [dite_eq_right h0] at h
    exact absurd h (by simp)

end Cast

section Charts

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

theorem blockOf_spec (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (X : ℝ) (ν : Fin CI.nb) (h : blockOf CI X = some ν) :
    CI.lo ν ≤ X ∧ X ≤ CI.hi ν := by
  unfold blockOf at h
  by_cases hex : ∃ ν' : Fin CI.nb, CI.lo ν' ≤ X ∧ X ≤ CI.hi ν'
  · rw [dite_eq_left hex] at h
    have := Option.some.inj h
    rw [← this]
    exact blockIdx_spec CI X hex
  · rw [dite_eq_right hex] at h
    exact absurd h (by simp)

/-- **The `JB.Chart` of the left bulk chart of the block `nu`** (direction `+`, rows `0 .. R-1`, columns `cols`): the scalars `sigma^{[m]} = 1/hat N`, `sigma^{[m+1]} = 1/hat N^{[m+1]}` and the hosts
`compMatrix CI0 spl`, `compMatrix CI1 (spl1 spl)` are those of the paper (eq:thb-bulkcol); the design data are `used` and `P_k`. -/
def blockChartL (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν : Fin CP.CI0.nb)
    (cols : Finset (Fin (N + 1))) (R : ℕ) (hlo : 0 + R ≤ N + 1) (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) :
    FormalResearch.JB.Chart (N + 1) R cols :=
  bulkJBChart (CP.CI0.bulkL ν) (CP.CI1.bulkL (Fin.cast CP.nb_eq.symm ν)) (TB.bulkL ν) (atStep F μ N) N Xs cols 0 R hlo true used Pk
    (fun k : cols => 1 / bulkNorm (CP.CI0.bulkL ν) (CP.CI0.bulkR ν) (atStep F μ N) (Xs k) N)
    (fun k : cols => 1 / bulkNorm (CP.CI1.bulkL (Fin.cast CP.nb_eq.symm ν)) (CP.CI1.bulkR (Fin.cast CP.nb_eq.symm ν)) (atStep F μ N) (Xs k) N)
    (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs)

/-- **The `JB.Chart` of the right (mirror) bulk chart of the block `nu`** (direction `-`, chain rows `N - (lo + n)` of the mirror family, `sigma^{[r]} = hat kappa^{[r]}/hat N^{[r]}`). -/
def blockChartR (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν : Fin CP.CI0.nb)
    (cols : Finset (Fin (N + 1))) (lo R : ℕ) (hlo : lo + R ≤ N + 1) (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) :
    FormalResearch.JB.Chart (N + 1) R cols :=
  bulkJBChart (CP.CI0.bulkR ν) (CP.CI1.bulkR (Fin.cast CP.nb_eq.symm ν)) (TB.bulkR ν) (atStep F μ N) N Xs cols lo R hlo false used Pk
    (fun k : cols => bulkKappa (CP.CI0.bulkL ν) (CP.CI0.bulkR ν) (atStep F μ N) (Xs k) N /
      bulkNorm (CP.CI0.bulkL ν) (CP.CI0.bulkR ν) (atStep F μ N) (Xs k) N)
    (fun k : cols => bulkKappa (CP.CI1.bulkL (Fin.cast CP.nb_eq.symm ν)) (CP.CI1.bulkR (Fin.cast CP.nb_eq.symm ν)) (atStep F μ N) (Xs k) N /
      bulkNorm (CP.CI1.bulkL (Fin.cast CP.nb_eq.symm ν)) (CP.CI1.bulkR (Fin.cast CP.nb_eq.symm ν)) (atStep F μ N) (Xs k) N)
    (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs)

theorem blockChartL_host0_eq (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν : Fin CP.CI0.nb)
    (cols : Finset (Fin (N + 1))) (hcols : ∀ k ∈ cols, blockOf CP.CI0 (Xs k) = some ν) (R : ℕ) (hlo : 0 + R ≤ N + 1)
    (hR : ((R : ℤ) - 1) ≤ nearestRow (F.step N) (spl ν)) (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) :
    ∀ n k, (blockChartL CP TB spl μ N Xs ν cols R hlo used Pk).H0 (F.step N) n k =
      (blockChartL CP TB spl μ N Xs ν cols R hlo used Pk).host0 ((blockChartL CP TB spl μ N Xs ν cols R hlo used Pk).row n) k := by
  unfold blockChartL
  exact bulk_host0_eq_left CP TB spl μ N Xs ν cols hcols R hlo hR used Pk _ _

theorem blockChartR_host0_eq (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν : Fin CP.CI0.nb)
    (cols : Finset (Fin (N + 1))) (hcols : ∀ k ∈ cols, blockOf CP.CI0 (Xs k) = some ν) (lo R : ℕ) (hlo : lo + R ≤ N + 1)
    (hR : nearestRow (F.step N) (spl ν) < (lo : ℤ)) (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) :
    ∀ n k, (blockChartR CP TB spl μ N Xs ν cols lo R hlo used Pk).H0 (F.step N) n k =
      (blockChartR CP TB spl μ N Xs ν cols lo R hlo used Pk).host0 ((blockChartR CP TB spl μ N Xs ν cols lo R hlo used Pk).row n) k := by
  unfold blockChartR
  exact bulk_host0_eq_right CP TB spl μ N Xs ν cols hcols lo R hlo hR used Pk _ _

/-- **`host1_eq` for the left chart** (the order-`(m+1)` host `compMatrix CI1 (spl1 spl)`; uses the block correspondence `blockOf_cast`, finding F-B11). -/
theorem blockChartL_host1_eq (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν : Fin CP.CI0.nb)
    (cols : Finset (Fin (N + 1))) (hcols : ∀ k ∈ cols, blockOf CP.CI0 (Xs k) = some ν) (R : ℕ) (hlo : 0 + R ≤ N + 1)
    (hR : ((R : ℤ) - 1) ≤ nearestRow (F.step N) (spl ν)) (used : Finset (Fin R)) (Pk : cols → Finset (Fin R))
    (hp : atStep F μ N ∈ paramSet K t0) (hNT : (TB.bulkL ν).N0 ≤ N) :
    ∀ n k, (blockChartL CP TB spl μ N Xs ν cols R hlo used Pk).H1 (F.step N) n k =
      (blockChartL CP TB spl μ N Xs ν cols R hlo used Pk).host1 ((blockChartL CP TB spl μ N Xs ν cols R hlo used Pk).row n) k := by
  intro n k
  have hk := hcols k k.2
  have hk1 := blockOf_cast CP (Xs k) ν hk
  have hX : ∀ k : cols, Xs k ∈ Set.Icc (CP.CI0.lo ν) (CP.CI0.hi ν) := fun k => blockOf_spec CP.CI0 (Xs k) ν (hcols k k.2)
  unfold blockChartL
  erw [bulkJBChart_H1 (CP.CI0.bulkL ν) (CP.CI1.bulkL (Fin.cast CP.nb_eq.symm ν)) (TB.bulkL ν) (atStep F μ N) hp N hNT Xs cols 0 R hlo true used Pk _ _ _ _ hX n k]
  simp only [bulkJBChart, FormalResearch.JB.Chart.row]
  rw [compMatrix_bulk_entry CP.CI1 (CP.spl1 spl) μ N Xs (Fin.cast CP.nb_eq.symm ν) k hk1]
  have hs : CP.spl1 spl (Fin.cast CP.nb_eq.symm ν) = spl ν := by simp [ChartPair.spl1]
  rw [hs]
  have hn : ((((0 : ℕ) + n.val : ℕ)) : ℤ) ≤ nearestRow (F.step N) (spl ν) := by
    have := n.isLt
    omega
  rw [ite_eq_left hn]
  have hcr : chartRow N 0 R true n = (((0 : ℕ) + n.val : ℕ) : ℤ) := by simp [chartRow]
  rw [hcr]
  ring

/-- **`host1_eq` for the right chart.** -/
theorem blockChartR_host1_eq (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν : Fin CP.CI0.nb)
    (cols : Finset (Fin (N + 1))) (hcols : ∀ k ∈ cols, blockOf CP.CI0 (Xs k) = some ν) (lo R : ℕ) (hlo : lo + R ≤ N + 1)
    (hR : nearestRow (F.step N) (spl ν) < (lo : ℤ)) (used : Finset (Fin R)) (Pk : cols → Finset (Fin R))
    (hp : atStep F μ N ∈ paramSet K t0) (hNT : (TB.bulkR ν).N0 ≤ N) :
    ∀ n k, (blockChartR CP TB spl μ N Xs ν cols lo R hlo used Pk).H1 (F.step N) n k =
      (blockChartR CP TB spl μ N Xs ν cols lo R hlo used Pk).host1 ((blockChartR CP TB spl μ N Xs ν cols lo R hlo used Pk).row n) k := by
  intro n k
  have hk := hcols k k.2
  have hk1 := blockOf_cast CP (Xs k) ν hk
  have hX : ∀ k : cols, Xs k ∈ Set.Icc (CP.CI0.lo ν) (CP.CI0.hi ν) := fun k => blockOf_spec CP.CI0 (Xs k) ν (hcols k k.2)
  unfold blockChartR
  erw [bulkJBChart_H1 (CP.CI0.bulkR ν) (CP.CI1.bulkR (Fin.cast CP.nb_eq.symm ν)) (TB.bulkR ν) (atStep F μ N) hp N hNT Xs cols lo R hlo false used Pk _ _ _ _ hX n k]
  simp only [bulkJBChart, FormalResearch.JB.Chart.row]
  rw [compMatrix_bulk_entry CP.CI1 (CP.spl1 spl) μ N Xs (Fin.cast CP.nb_eq.symm ν) k hk1]
  have hs : CP.spl1 spl (Fin.cast CP.nb_eq.symm ν) = spl ν := by simp [ChartPair.spl1]
  rw [hs]
  have hn : ¬ ((((lo + n.val : ℕ)) : ℤ) ≤ nearestRow (F.step N) (spl ν)) := by
    omega
  rw [ite_eq_right hn]
  have hcr : chartRow N lo R false n = (N : ℤ) - (((lo + n.val : ℕ) : ℤ)) := by simp [chartRow]
  rw [hcr]
  ring

end Charts


/-! ### Window lower bound on a sub-window `[a, b]` of the oscillatory overlap -/

section SubWindow

/-- The rows of `rowsOf N` whose node lies in `[a, b]`. -/
def subWin (h a b : ℝ) (N : ℕ) : Finset ℤ := (rowsOf N).filter (fun n => a ≤ uNode h n ∧ uNode h n ≤ b)

/-- The window constant of a sub-window `[a, b]` of the overlap of a bulk chart (`windowConst` with `[c', c]` replaced by `[a, b]`). -/
def subWindowConst {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi : ℝ}
    {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (CA a b : ℝ) : ℝ :=
  (b - a) * C.cs.cm ^ 2 / (8 * ((CA + 1) * ((C.cs.KA + C.cs.KB) * C.cs.Kw + 1) * (C.CM + 1)) ^ 2)

/-- **Window lower bound on a sub-window** (`window_sum_lower` for `[a, b]` with `c' <= a < b <= c`): `c_{[a,b]} / sqrt h <= sum_{n in [a,b]} (psihat^L_n)^2`. -/
theorem window_sum_lower_sub {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (CA : ℝ) (hCA0 : 0 ≤ CA) (a b : ℝ)
    (hca : C.c' ≤ a) (hab : a < b) (hbc : b ≤ C.c)
    (p : Par × ℝ) (hp : p ∈ P) (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi) (N : ℕ) (hN : C.N0 ≤ N)
    (hhd : G.step N ≤ (b - a) / 6) (hhσ : G.step N ≤ C.σ)
    (hA : ∀ j : ℤ, 0 ≤ j → j ≤ (C.chain p X N).NR - 1 → |(C.chain p X N).A j| ≤ CA) :
    subWindowConst C CA a b / Real.sqrt (G.step N) ≤ ∑ n ∈ subWin (G.step N) a b N, (C.psiHatL p X N n) ^ 2 := by
  obtain ⟨hc'L, hcc'L, -, hcσL, -, hcM, hcMCM, -, hCsumL, -⟩ := C.consts_pos
  have hst : 0 < G.step N := FormalResearch.JB.stepSize_pos G.L_pos N
  have hLs : G.step N * ((N : ℝ) + 1) = G.L := step_mul_succ G N
  have hD0 : 0 < b - a := by linarith
  have hhc : G.step N ≤ C.c - C.c' := by linarith [hhd]
  have hcL : b + G.step N ≤ G.L := by linarith
  have hKg0 : 0 < (C.cs.KA + C.cs.KB) * C.cs.Kw + 1 := by
    have := mul_nonneg (add_nonneg C.cs.KA_nonneg C.cs.KB_nonneg) C.cs.Kw_nonneg
    linarith
  have hCEg0 : 0 < |C.cs.CE| + 1 := by linarith [abs_nonneg C.cs.CE]
  have hCMg0 : 0 < C.CM + 1 := by linarith
  have hCAg0 : 0 < CA + 1 := by linarith
  have hCsg0 : 0 < C.Csum + 1 := by linarith
  have hA' : ∀ j : ℤ, 0 ≤ j → j ≤ (C.chain p X N).NR - 1 → |(C.chain p X N).A j| ≤ CA + 1 :=
    fun j h1 h2 => (hA j h1 h2).trans (by linarith)
  obtain ⟨-, -, -, -, hpair⟩ := chart_side_facts C p hp X hX N hN hhc ((C.cs.KA + C.cs.KB) * C.cs.Kw + 1)
    (|C.cs.CE| + 1) (C.CM + 1) C.cs.cm (C.Csum + 1) (CA + 1) hKg0 hCEg0 hCMg0 C.cs.cm_pos hCAg0
    (by linarith) (by linarith [le_abs_self C.cs.CE]) (by linarith) le_rfl (by linarith) hA'
  set K3 : ℝ := (CA + 1) * ((C.cs.KA + C.cs.KB) * C.cs.Kw + 1) * (C.CM + 1) with hK3
  have hK3pos : 0 < K3 := by rw [hK3]; positivity
  set q : ℝ := G.step N ^ ((1 : ℝ) / 4) with hq
  obtain ⟨hq2, hq0⟩ := fourth_root_sq (G.step N) hst
  rw [← hq] at hq2
  set c1 : ℝ := C.cs.cm * q / K3 with hc1
  have hc10 : 0 ≤ c1 := by rw [hc1]; exact div_nonneg (mul_nonneg C.cs.cm_pos.le hq0.le) hK3pos.le
  have ha0 : 0 < a := by linarith
  obtain ⟨S, hSprop, hScard⟩ := count_pairs (G.step N) G.L a b N hst hLs ha0 hab hcL
  have hPpair : ∀ n ∈ S, c1 ≤ |C.psiHatL p X N n| + |C.psiHatL p X N (n + 1)| := by
    intro n hn
    obtain ⟨hn0, hn1, hc1', hc2'⟩ := hSprop n hn
    have hk := hpair n hn0 (le_NR_of C p hp X hX N hN hst (n + 1) (hc2'.trans hbc)) (hca.trans hc1') (hc2'.trans hbc)
    rw [hc1, div_le_iff₀ hK3pos]
    have e : K3 = (CA + 1) * ((C.cs.KA + C.cs.KB) * C.cs.Kw + 1) * (C.CM + 1) := hK3
    rw [e]
    linarith [hk]
  have hmem : ∀ n : ℤ, n ∈ subWin (G.step N) a b N ↔ (n ∈ rowsOf N ∧ a ≤ uNode (G.step N) n ∧ uNode (G.step N) n ≤ b) := by
    intro n
    unfold subWin
    exact Finset.mem_filter
  have hS : ∀ n ∈ S, n ∈ subWin (G.step N) a b N ∧ n + 1 ∈ subWin (G.step N) a b N := by
    intro n hn
    obtain ⟨hn0, hn1, hc1', hc2'⟩ := hSprop n hn
    have hle : uNode (G.step N) n ≤ uNode (G.step N) (n + 1) := uNode_le_of_le hst.le (by omega)
    refine ⟨(hmem n).mpr ⟨?_, hc1', by linarith⟩, (hmem (n + 1)).mpr ⟨?_, by linarith, hc2'⟩⟩
    · unfold rowsOf; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · unfold rowsOf; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hov := overlap_sum_lower (fun n => C.psiHatL p X N n) (subWin (G.step N) a b N) S c1 hc10 hS hPpair
  have hov' : (S.card : ℝ) * c1 ^ 2 ≤ 4 * ∑ n ∈ subWin (G.step N) a b N, C.psiHatL p X N n ^ 2 := hov
  have h6 : 6 ≤ (b - a) / G.step N := by
    rw [le_div_iff₀ hst]; linarith [hhd]
  have hSmall : (b - a) / (2 * G.step N) ≤ (S.card : ℝ) := by
    have e : (b - a) / (2 * G.step N) = ((b - a) / G.step N) / 2 := by rw [div_div, mul_comm]
    rw [e]; linarith
  have hk1 : (b - a) / (2 * G.step N) * c1 ^ 2 ≤ (S.card : ℝ) * c1 ^ 2 :=
    mul_le_mul_of_nonneg_right hSmall (sq_nonneg _)
  have hsq : Real.sqrt (G.step N) ^ 2 = G.step N := Real.sq_sqrt hst.le
  have hs0 : 0 < Real.sqrt (G.step N) := Real.sqrt_pos.mpr hst
  have hc1sq : c1 ^ 2 = C.cs.cm ^ 2 * Real.sqrt (G.step N) / K3 ^ 2 := by
    rw [hc1, div_pow, mul_pow, hq2]
  have hw : subWindowConst C CA a b = (b - a) * C.cs.cm ^ 2 / (8 * K3 ^ 2) := rfl
  have heq : subWindowConst C CA a b / Real.sqrt (G.step N) =
      (b - a) / (2 * G.step N) * c1 ^ 2 / 4 := by
    obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (G.step N) := ⟨_, rfl⟩
    have hG : G.step N = s ^ 2 := by rw [hs, Real.sq_sqrt hst.le]
    have hs0' : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hst
    rw [hc1sq, hw, ← hs, hG]
    field_simp
    ring
  rw [heq]
  linarith [hk1, hov']

end SubWindow


/-! ### Design data of a bulk chart: the overlap windows `P_k`, the model pair bound, `overlap_ub` -/

section Design

/-- The chart rows whose chain row has its node in `[a, b]`: the overlap window `P_k` of a bulk chart (the same for every column). -/
def bulkPk (N lo R : ℕ) (τ : Bool) (h a b : ℝ) : Finset (Fin R) :=
  Finset.univ.filter fun n => a ≤ uNode h (chartRow N lo R τ n) ∧ uNode h (chartRow N lo R τ n) ≤ b

theorem chartRow_nonneg (N lo R : ℕ) (hlo : lo + R ≤ N + 1) (τ : Bool) (n : Fin R) : 0 ≤ chartRow N lo R τ n := by
  have := n.isLt
  cases τ <;> simp only [chartRow, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem chartRow_injective (N lo R : ℕ) (τ : Bool) : Function.Injective (chartRow N lo R τ) := by
  intro n n' h
  apply Fin.ext
  cases τ <;> simp only [chartRow, Bool.false_eq_true, ite_false, ite_true] at h <;> omega

theorem jbL2_le_sqrt_card_mul {ι : Type*} (S : Finset ι) (v : ι → ℝ) {B : ℝ} (hB : 0 ≤ B) (h : ∀ n ∈ S, |v n| ≤ B) :
    FormalResearch.JB.jbL2 S v ≤ Real.sqrt (S.card : ℝ) * B := by
  unfold FormalResearch.JB.jbL2
  have e : Real.sqrt (S.card : ℝ) * B = Real.sqrt ((S.card : ℝ) * B ^ 2) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB]
  rw [e]
  apply Real.sqrt_le_sqrt
  calc ∑ n ∈ S, v n ^ 2 ≤ ∑ _n ∈ S, B ^ 2 := Finset.sum_le_sum fun n hn => by
        have := h n hn
        calc v n ^ 2 = |v n| ^ 2 := (sq_abs _).symm
          _ ≤ B ^ 2 := by gcongr
    _ = (S.card : ℝ) * B ^ 2 := by simp

/-- **The model pair is bounded by the Weber modulus on the oscillatory part**: `|y_j|, |y~_j| <= K_w C_M h^{1/4}` for chain rows `j <= NR` with `c' <= u_j`
(`env` of the chain, `W = 1` by `W_osc`, `rho = rho~ = 1`, `M <= C_M h^{1/4}` by `M_osc`). -/
theorem bulk_wf_bound {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi : ℝ} {m : ℕ}
    {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : X ∈ Set.Icc Jlo Jhi) {N : ℕ} (hN : C.N0 ≤ N)
    (j : ℤ) (hj0 : 0 ≤ j) (hjN : j ≤ (C.chain p X N).NR) (hcj : C.c' ≤ uNode (G.step N) j) :
    |(C.chain p X N).wf 1 0 (uNode (G.step N) j) (G.step N) 0| ≤ C.cs.Kw * (C.CM * (G.step N) ^ ((1 : ℝ) / 4)) ∧
    |(C.chain p X N).wf 1 0 (uNode (G.step N) j) (G.step N) 1| ≤ C.cs.Kw * (C.CM * (G.step N) ^ ((1 : ℝ) / 4)) := by
  have hV := C.valid p hp X hX N hN
  obtain ⟨hP1, -, -, -, -⟩ := C.shape p hp X hX N hN
  have hjm : j ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR := Finset.mem_Icc.mpr ⟨hj0, hjN⟩
  obtain ⟨hp1, hjj0, hjj1⟩ := window_one (C.chain p X N) C.cs (G.step N) m hV hP1
  have hw : j ∈ Finset.Icc (max ((C.chain p X N).jj (1 - 1)) 0) ((C.chain p X N).jj 1 + 1) := by
    rw [hjj0, hjj1, max_self]
    exact Finset.mem_Icc.mpr ⟨hj0, by omega⟩
  obtain ⟨e0, -, e2, -⟩ := hV.env 1 hp1 j hw
  obtain ⟨hρ, hρt⟩ := C.rho_one p hp X hX N hN j hjm
  have hW := C.W_osc p hp X hX N hN j hjm hcj
  have hM := (C.M_osc p hp X hX N hN j hjm hcj).2
  simp only [hρt, hρ, hW, one_mul, mul_one] at e2 e0
  have hKw := C.cs.Kw_nonneg
  have hMb : C.cs.Kw * (C.chain p X N).M j ≤ C.cs.Kw * (C.CM * (G.step N) ^ ((1 : ℝ) / 4)) := mul_le_mul_of_nonneg_left hM hKw
  have e0' : |(C.chain p X N).wf 1 0 (uNode (G.step N) j) (G.step N) 0| ≤ C.cs.Kw * (C.chain p X N).M j := by
    unfold uNode; exact e0
  have e2' : |(C.chain p X N).wf 1 0 (uNode (G.step N) j) (G.step N) 1| ≤ C.cs.Kw * (C.chain p X N).M j := by
    unfold uNode; exact e2
  exact ⟨e0'.trans hMb, e2'.trans hMb⟩

/-- `phi^{[m+1]} = psi-hat^{L}` of the order-`(m+1)` chart on the chart rows (profile identity, `bulkJBChart_H1` without the scalar). -/
theorem bulkJBChart_phi1 {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi Jlo1 Jhi1 : ℝ} {m : ℕ}
    {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (C1 : BulkWeberChart G P Jlo1 Jhi1 (m + 1) U V)
    (TI : TransferInputs G P (fun _ => Jlo) (fun _ => Jhi) m C.chain C1.chain 1 (fun _ => 0) (fun _ => C.c + C.σ / 2))
    (p : Par × ℝ) (hp : p ∈ P) (N : ℕ) (hNT : TI.N0 ≤ N) (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (lo R : ℕ)
    (hlo : lo + R ≤ N + 1) (τ : Bool)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 σ1 : cols → ℝ)
    (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hX : ∀ k : cols, Xc k ∈ Set.Icc Jlo Jhi) (n : Fin R) (k : cols) :
    (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).phi1 (G.step N) n k =
      C1.psiHatL p (Xc k) N (chartRow N lo R τ n) := by
  simp only [FormalResearch.JB.Chart.phi1_apply, bulkJBChart, Matrix.of_apply]
  unfold BulkWeberChart.psiHatL
  rw [psiHat_one_eq]
  unfold LadderData.phi ladderSeq vrow dot uNode
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hw : (C.chain p (Xc k) N).wf 1 = (C1.chain p (Xc k) N).wf 1 := (TI.same_ladder p hp (Xc k) (hX k) N hNT).2.1
  have hw := congrFun hw 0
  rw [← hw]
  ring


theorem ub_arith (n L Ky wc s : ℝ) (hn : 0 ≤ n) (hKy : 0 ≤ Ky) (hwc : 0 < wc) (hs : 0 < s) (hN : n * s ^ 4 = L) :
    2 * (Real.sqrt n * (Ky * s)) ≤ (2 * (Ky * Real.sqrt L) / Real.sqrt wc) * Real.sqrt (wc / s ^ 2) := by
  have h1 : Real.sqrt L = Real.sqrt n * s ^ 2 := by
    rw [← hN, Real.sqrt_mul hn, show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have h2 : Real.sqrt (wc / s ^ 2) = Real.sqrt wc / s := by
    rw [Real.sqrt_div hwc.le, Real.sqrt_sq hs.le]
  have h3 : 0 < Real.sqrt wc := Real.sqrt_pos.mpr hwc
  rw [h1, h2]
  apply le_of_eq
  field_simp

/-- **`overlap_ub` for a bulk chart** (`||P_k y|| + ||P_k y~|| <= C_4 ||P_k phi^{[m+1]}||`), with `P_k` the chart rows whose node lies in a fixed sub-window `[a, b]` of the oscillatory overlaps of both orders
(`c' <= a < b <= c` for `C` and `C1`).  Route: `|y|, |y~| <= K_w C_M h^{1/4}` on the window (`bulk_wf_bound`), at most `N + 1 = L/h` rows, so `||P y|| <= K_w C_M sqrt(L) h^{-1/4}`; the window mass of the order-`(m+1)` comparison sequence
is `>= c_{[a,b]} h^{-1/2}` (`window_sum_lower_sub`), and `phi^{[m+1]} = psi-hat^{L,[m+1]}` on the chart rows (`bulkJBChart_phi1`).  The constant `C_4` and the threshold `h_1` depend on the chart pair, the bond bound `CA` and `[a, b]` only. -/
theorem bulkJBChart_overlap_ub {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi Jlo1 Jhi1 : ℝ} {m : ℕ}
    {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (C1 : BulkWeberChart G P Jlo1 Jhi1 (m + 1) U V)
    (TI : TransferInputs G P (fun _ => Jlo) (fun _ => Jhi) m C.chain C1.chain 1 (fun _ => 0) (fun _ => C.c + C.σ / 2))
    (CA : ℝ) (hCA0 : 0 ≤ CA) (hCA : ∀ μ ∈ P, ∀ N : ℕ, ∀ n : ℤ, |G.bondA μ N n| ≤ CA)
    (a b : ℝ) (hab : a < b) (hca : C.c' ≤ a) (hbc : b ≤ C.c) (hca1 : C1.c' ≤ a) (hbc1 : b ≤ C1.c) :
    ∃ C4 h1 : ℝ, 0 ≤ C4 ∧ 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max C.N0 C1.N0 ≤ N → TI.N0 ≤ N → G.step N ≤ h1 →
      ∀ (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (lo R : ℕ) (hlo : lo + R ≤ N + 1) (τ : Bool)
        (used : Finset (Fin R)) (σ0 σ1 : cols → ℝ) (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        (∀ k : cols, Xc k ∈ Set.Icc Jlo Jhi) → (∀ k : cols, Xc k ∈ Set.Icc Jlo1 Jhi1) →
        (∀ j ∈ subWin (G.step N) a b N, ∃ n : Fin R, chartRow N lo R τ n = j) →
        ∀ k : cols,
          FormalResearch.JB.jbL2 (bulkPk N lo R τ (G.step N) a b)
              (fun n => (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used (fun _ => bulkPk N lo R τ (G.step N) a b) σ0 σ1 host0 host1).y n k) +
            FormalResearch.JB.jbL2 (bulkPk N lo R τ (G.step N) a b)
              (fun n => (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used (fun _ => bulkPk N lo R τ (G.step N) a b) σ0 σ1 host0 host1).yt n k) ≤
          C4 * FormalResearch.JB.jbL2 (bulkPk N lo R τ (G.step N) a b)
              (fun n => (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used (fun _ => bulkPk N lo R τ (G.step N) a b) σ0 σ1 host0 host1).phi1 (G.step N) n k) := by
  obtain ⟨hc'L, hcc'L, hσL, hcσL, -, hcM, hcMCM, -, hCsumL, -⟩ := C.consts_pos
  have hCM0 : 0 ≤ C.CM := hcM.le.trans hcMCM
  have hKy : 0 ≤ C.cs.Kw * C.CM := mul_nonneg C.cs.Kw_nonneg hCM0
  have hwc : 0 < subWindowConst C1 CA a b := by
    unfold subWindowConst
    obtain ⟨-, -, -, -, -, hcM1, hcMCM1, -, -, -⟩ := C1.consts_pos
    have := C1.cs.cm_pos
    have hK : 0 < (CA + 1) * ((C1.cs.KA + C1.cs.KB) * C1.cs.Kw + 1) * (C1.CM + 1) := by
      have h1 := mul_nonneg (add_nonneg C1.cs.KA_nonneg C1.cs.KB_nonneg) C1.cs.Kw_nonneg
      have : 0 < C1.CM + 1 := by linarith
      positivity
    have : 0 < b - a := by linarith
    positivity
  refine ⟨2 * ((C.cs.Kw * C.CM) * Real.sqrt G.L) / Real.sqrt (subWindowConst C1 CA a b), min (min 1 ((b - a) / 6)) C1.σ,
    div_nonneg (mul_nonneg (by norm_num) (mul_nonneg hKy (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _),
    lt_min (lt_min one_pos (by linarith)) (by obtain ⟨-, -, h, -⟩ := C1.consts_pos; exact h), ?_⟩
  intro p hp N hN hNT hstep Xc cols lo R hlo τ used σ0 σ1 host0 host1 hX hX1 hcov k
  have hN0 : C.N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : C1.N0 ≤ N := le_trans (le_max_right _ _) hN
  have hst : 0 < G.step N := FormalResearch.JB.stepSize_pos G.L_pos N
  have hLs : G.step N * ((N : ℝ) + 1) = G.L := step_mul_succ G N
  have hhd : G.step N ≤ (b - a) / 6 := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhσ : G.step N ≤ C1.σ := hstep.trans (min_le_right _ _)
  obtain ⟨hs2, hs0⟩ := fourth_root_sq (G.step N) hst
  set s : ℝ := G.step N ^ ((1 : ℝ) / 4) with hsdef
  have hs4 : G.step N = s ^ 4 := by
    have h2 : s ^ 2 = Real.sqrt (G.step N) := hs2
    have h3 : Real.sqrt (G.step N) ^ 2 = G.step N := Real.sq_sqrt hst.le
    calc G.step N = Real.sqrt (G.step N) ^ 2 := h3.symm
      _ = (s ^ 2) ^ 2 := by rw [h2]
      _ = s ^ 4 := by ring
  set c := bulkJBChart C C1 TI p N Xc cols lo R hlo τ used (fun _ => bulkPk N lo R τ (G.step N) a b) σ0 σ1 host0 host1 with hc
  set Pw := bulkPk N lo R τ (G.step N) a b with hPw
  -- the model pair on the window
  have hyb : ∀ n ∈ Pw, |c.y n k| ≤ C.cs.Kw * (C.CM * s) ∧ |c.yt n k| ≤ C.cs.Kw * (C.CM * s) := by
    intro n hn
    have hn' := (Finset.mem_filter.mp hn).2
    have hb' := bulk_wf_bound C hp (hX k) hN0 (chartRow N lo R τ n) (chartRow_nonneg N lo R hlo τ n)
      (le_NR_of C p hp (Xc k) (hX k) N hN0 hst _ (hn'.2.trans hbc)) (hca.trans hn'.1)
    exact hb'
  have hcard : (Pw.card : ℝ) ≤ (N : ℝ) + 1 := by
    have h1 : Pw.card ≤ R := by
      calc Pw.card ≤ (Finset.univ : Finset (Fin R)).card := Finset.card_le_univ _
        _ = R := by simp
    have h2 : R ≤ N + 1 := by omega
    exact_mod_cast h1.trans h2
  have hsq : Real.sqrt (Pw.card : ℝ) ≤ Real.sqrt ((N : ℝ) + 1) := Real.sqrt_le_sqrt hcard
  have hB : 0 ≤ C.cs.Kw * (C.CM * s) := mul_nonneg C.cs.Kw_nonneg (mul_nonneg hCM0 hs0.le)
  have hy1 := jbL2_le_sqrt_card_mul Pw (fun n => c.y n k) hB (fun n hn => (hyb n hn).1)
  have hy2 := jbL2_le_sqrt_card_mul Pw (fun n => c.yt n k) hB (fun n hn => (hyb n hn).2)
  have hup : FormalResearch.JB.jbL2 Pw (fun n => c.y n k) + FormalResearch.JB.jbL2 Pw (fun n => c.yt n k) ≤
      2 * (Real.sqrt ((N : ℝ) + 1) * ((C.cs.Kw * C.CM) * s)) := by
    have e : C.cs.Kw * (C.CM * s) = (C.cs.Kw * C.CM) * s := by ring
    rw [e] at hy1 hy2
    have h3 : Real.sqrt (Pw.card : ℝ) * ((C.cs.Kw * C.CM) * s) ≤ Real.sqrt ((N : ℝ) + 1) * ((C.cs.Kw * C.CM) * s) :=
      mul_le_mul_of_nonneg_right hsq (mul_nonneg hKy hs0.le)
    linarith
  -- the window mass of the order (m+1) comparison sequence
  have hA1 : ∀ j : ℤ, 0 ≤ j → j ≤ (C1.chain p (Xc k) N).NR - 1 → |(C1.chain p (Xc k) N).A j| ≤ CA := by
    intro j h0 h1
    rw [C1.A_bond p hp (Xc k) (hX1 k) N hN1 j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
    exact hCA p hp N j
  have hwin := window_sum_lower_sub C1 CA hCA0 a b hca1 hab hbc1 p hp (Xc k) (hX1 k) N hN1 hhd hhσ hA1
  have hmass : subWindowConst C1 CA a b / Real.sqrt (G.step N) ≤ ∑ n ∈ Pw, (c.phi1 (G.step N) n k) ^ 2 := by
    refine hwin.trans ?_
    have hsub : subWin (G.step N) a b N ⊆ Pw.image (chartRow N lo R τ) := by
      intro j hj
      obtain ⟨n, hn⟩ := hcov j hj
      have hj' := (Finset.mem_filter.mp hj).2
      refine Finset.mem_image.mpr ⟨n, ?_, hn⟩
      rw [hPw]
      unfold bulkPk
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hn]
      exact hj'
    calc ∑ n ∈ subWin (G.step N) a b N, (C1.psiHatL p (Xc k) N n) ^ 2
        ≤ ∑ n ∈ Pw.image (chartRow N lo R τ), (C1.psiHatL p (Xc k) N n) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ = ∑ n ∈ Pw, (C1.psiHatL p (Xc k) N (chartRow N lo R τ n)) ^ 2 :=
          Finset.sum_image (fun x _ y _ hxy => chartRow_injective N lo R τ hxy)
      _ = ∑ n ∈ Pw, (c.phi1 (G.step N) n k) ^ 2 := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [hc, bulkJBChart_phi1 C C1 TI p hp N hNT Xc cols lo R hlo τ used _ σ0 σ1 host0 host1 hX n k]
  have hΦ : Real.sqrt (subWindowConst C1 CA a b / s ^ 2) ≤ FormalResearch.JB.jbL2 Pw (fun n => c.phi1 (G.step N) n k) := by
    unfold FormalResearch.JB.jbL2
    apply Real.sqrt_le_sqrt
    rw [hs2]
    exact hmass
  have hari := ub_arith ((N : ℝ) + 1) G.L (C.cs.Kw * C.CM) (subWindowConst C1 CA a b) s (by positivity) hKy hwc hs0
    (by rw [← hLs, hs4]; ring)
  have hC4 : 0 ≤ 2 * ((C.cs.Kw * C.CM) * Real.sqrt G.L) / Real.sqrt (subWindowConst C1 CA a b) :=
    div_nonneg (mul_nonneg (by norm_num) (mul_nonneg hKy (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _)
  calc _ ≤ 2 * (Real.sqrt ((N : ℝ) + 1) * ((C.cs.Kw * C.CM) * s)) := hup
    _ ≤ _ := hari
    _ ≤ _ := mul_le_mul_of_nonneg_left hΦ hC4


/-- **The scalars `sigma^{[r]}` of the bulk charts are `O(h^{1/4})`** (`hat N >= c_N h^{-1/4}`, `|hat kappa| <= C_kappa`: `PropThaW (2)`): `|1/hat N| <= C_sigma h^{1/4}` (left chart) and
`|hat kappa/hat N| <= C_sigma h^{1/4}` (right chart). -/
theorem bulk_sigma_bound {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V)
    (hm : 1 ≤ m) (hcoup : CR.c = Fz.L - CL.c' ∧ CR.c' = Fz.L - CL.c) (r : ℕ) (hr : StdAssump Fz P (m / 2) r) :
    ∃ Cσ h1 : ℝ, 0 ≤ Cσ ∧ 0 < h1 ∧ ∀ p ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      |1 / bulkNorm CL CR p X N| ≤ Cσ * Fz.step N ^ ((1 : ℝ) / 4) ∧
      |bulkKappa CL CR p X N / bulkNorm CL CR p X N| ≤ Cσ * Fz.step N ^ ((1 : ℝ) / 4) := by
  obtain ⟨Cc, h0, cN, CN, cκ, Cκ, hh0, hcN, hcκ, hall⟩ := bulk_conj1 CL CR hm hcoup r hr
  refine ⟨(1 + |Cκ|) / cN, h0, by positivity, hh0, ?_⟩
  intro p hp X hX N hN hstep
  have hst : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  obtain ⟨hpos, hlow, -, hκ, -⟩ := hall p hp X hX N hN hstep
  obtain ⟨-, hs0⟩ := fourth_root_sq (Fz.step N) hst
  set s : ℝ := Fz.step N ^ ((1 : ℝ) / 4) with hsdef
  have hneg : Fz.step N ^ (-(1 : ℝ) / 4) = s⁻¹ := by
    rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring, Real.rpow_neg hst.le]
  rw [hneg] at hlow
  have hinv : |1 / bulkNorm CL CR p X N| ≤ s / cN := by
    rw [abs_of_pos (by positivity), div_le_div_iff₀ hpos hcN]
    have : cN * s⁻¹ ≤ bulkNorm CL CR p X N := hlow
    have h2 : cN ≤ bulkNorm CL CR p X N * s := by
      calc cN = cN * s⁻¹ * s := by field_simp
        _ ≤ bulkNorm CL CR p X N * s := mul_le_mul_of_nonneg_right this hs0.le
    linarith
  have hcσ : 0 < (1 + |Cκ|) / cN := by positivity
  refine ⟨hinv.trans ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hcN]
    nlinarith [abs_nonneg Cκ, hs0]
  · calc |bulkKappa CL CR p X N / bulkNorm CL CR p X N| = |bulkKappa CL CR p X N| * |1 / bulkNorm CL CR p X N| := by
          rw [← abs_mul]; congr 1; ring
      _ ≤ |Cκ| * (s / cN) := mul_le_mul (hκ.trans (le_abs_self _)) hinv (abs_nonneg _) (abs_nonneg _)
      _ ≤ (1 + |Cκ|) / cN * s := by
          rw [mul_div_assoc', div_mul_eq_mul_div]
          apply div_le_div_of_nonneg_right _ hcN.le
          nlinarith [abs_nonneg Cκ, hs0]

/-- **`ext_row` for a bulk chart** (`||(omega_n sigma^{[m+1]}_k y_{ext,k})_k|| <= C_E`, `(I3)`): if the exterior row is a row of the oscillatory region (`0 <= row`, `c' <= u_row <= c`) and
`|sigma^{[m+1]}_k| <= C_sigma h^{1/4}` on the columns (`bulk_sigma_bound`), then `|omega sigma y_ext| <= sqrt(c + 1) C_sigma K_w C_M h^{1/2}` and the `l^2` norm over at most `N + 1 = L/h` columns is `<= sqrt(c+1) C_sigma K_w C_M sqrt L`. -/
theorem bulkJBChart_ext_row {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi Jlo1 Jhi1 : ℝ} {m : ℕ}
    {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (C1 : BulkWeberChart G P Jlo1 Jhi1 (m + 1) U V)
    (TI : TransferInputs G P (fun _ => Jlo) (fun _ => Jhi) m C.chain C1.chain 1 (fun _ => 0) (fun _ => C.c + C.σ / 2))
    (Cσ : ℝ) (hCσ : 0 ≤ Cσ) :
    ∃ CE h1 : ℝ, 0 ≤ CE ∧ 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, C.N0 ≤ N → G.step N ≤ h1 →
      ∀ (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))) (lo R : ℕ) (hlo : lo + R ≤ N + 1) (τ : Bool)
        (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (σ0 σ1 : cols → ℝ) (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        (∀ k : cols, Xc k ∈ Set.Icc Jlo Jhi) → (∀ k : cols, |σ1 k| ≤ Cσ * G.step N ^ ((1 : ℝ) / 4)) →
        0 ≤ chartExtRow N lo R τ → C.c' ≤ uNode (G.step N) (chartExtRow N lo R τ) → uNode (G.step N) (chartExtRow N lo R τ) ≤ C.c →
        ∀ n : Fin R, (τ = true → n.val + 1 = R) → (τ = false → n.val = 0) →
          FormalResearch.JB.jbL2 Finset.univ
            (fun k : cols => (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).ω n *
              (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).σ1 k *
              (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).yext k) ≤ CE := by
  obtain ⟨hc'L, hcc'L, hσL, hcσL, -, hcM, hcMCM, -, hCsumL, -⟩ := C.consts_pos
  have hCM0 : 0 ≤ C.CM := hcM.le.trans hcMCM
  have hKy : 0 ≤ C.cs.Kw * C.CM := mul_nonneg C.cs.Kw_nonneg hCM0
  refine ⟨Real.sqrt (C.c + 1) * Cσ * (C.cs.Kw * C.CM) * Real.sqrt G.L, 1, by positivity, one_pos, ?_⟩
  intro p hp N hN hstep Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1 hX hσ hext0 hext1 hext2 n hnτ hnf
  have hst : 0 < G.step N := FormalResearch.JB.stepSize_pos G.L_pos N
  have hLs : G.step N * ((N : ℝ) + 1) = G.L := step_mul_succ G N
  obtain ⟨hs2, hs0⟩ := fourth_root_sq (G.step N) hst
  set s : ℝ := G.step N ^ ((1 : ℝ) / 4) with hsdef
  have hs4 : G.step N = s ^ 4 := by
    have h2 : s ^ 2 = Real.sqrt (G.step N) := hs2
    have h3 : Real.sqrt (G.step N) ^ 2 = G.step N := Real.sq_sqrt hst.le
    calc G.step N = Real.sqrt (G.step N) ^ 2 := h3.symm
      _ = (s ^ 2) ^ 2 := by rw [h2]
      _ = s ^ 4 := by ring
  -- the row of `n` is just below the exterior row
  have hrow1 : chartRow N lo R τ n + 1 = chartExtRow N lo R τ := by
    cases τ
    · have := hnf rfl
      simp only [chartRow, chartExtRow, Bool.false_eq_true, ite_false]
      have : n.val = 0 := this
      omega
    · have := hnτ rfl
      simp only [chartRow, chartExtRow, ite_true]
      omega
  have hu1 : uNode (G.step N) (chartRow N lo R τ n) ≤ C.c := by
    have : uNode (G.step N) (chartRow N lo R τ n) ≤ uNode (G.step N) (chartExtRow N lo R τ) :=
      uNode_le_of_le hst.le (by omega)
    linarith
  have hωb : ∀ k : cols, |(bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).ω n| ≤ Real.sqrt (C.c + 1) := by
    intro k
    show |Real.sqrt _| ≤ _
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    have : 0 ≤ uNode (G.step N) (chartRow N lo R τ n) := by
      have h0 := chartRow_nonneg N lo R hlo τ n
      unfold uNode
      have : (0 : ℝ) ≤ ((chartRow N lo R τ n : ℤ) : ℝ) := by exact_mod_cast h0
      positivity
    linarith [hstep]
  have hbound : ∀ k : cols, |(bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).ω n *
      (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).σ1 k *
      (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).yext k| ≤
      Real.sqrt (C.c + 1) * Cσ * (C.cs.Kw * C.CM) * s ^ 2 := by
    intro k
    have hy := (bulk_wf_bound C hp (hX k) hN (chartExtRow N lo R τ) hext0
      (le_NR_of C p hp (Xc k) (hX k) N hN hst _ hext2) hext1).1
    have hσk : |σ1 k| ≤ Cσ * s := hσ k
    show |(bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).ω n * σ1 k *
      (C.chain p (Xc k) N).wf 1 0 (uNode (G.step N) (chartExtRow N lo R τ)) (G.step N) 0| ≤ _
    rw [abs_mul, abs_mul]
    have h1 := hωb k
    have e : Real.sqrt (C.c + 1) * Cσ * (C.cs.Kw * C.CM) * s ^ 2 =
        Real.sqrt (C.c + 1) * (Cσ * s) * (C.cs.Kw * (C.CM * s)) := by ring
    rw [e]
    exact mul_le_mul (mul_le_mul h1 hσk (abs_nonneg _) (Real.sqrt_nonneg _)) hy (abs_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCσ hs0.le))
  have hBnn : 0 ≤ Real.sqrt (C.c + 1) * Cσ * (C.cs.Kw * C.CM) * s ^ 2 := by positivity
  have hl2 := jbL2_le_sqrt_card_mul (Finset.univ : Finset cols) (fun k : cols => (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).ω n *
      (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).σ1 k *
      (bulkJBChart C C1 TI p N Xc cols lo R hlo τ used Pk σ0 σ1 host0 host1).yext k) hBnn (fun k _ => hbound k)
  refine hl2.trans ?_
  have hcard : ((Finset.univ : Finset cols).card : ℝ) ≤ (N : ℝ) + 1 := by
    have : (Finset.univ : Finset cols).card ≤ N + 1 := by
      rw [Finset.card_univ, Fintype.card_coe]
      calc cols.card ≤ (Finset.univ : Finset (Fin (N + 1))).card := Finset.card_le_univ _
        _ = N + 1 := by simp
    exact_mod_cast this
  have hsq := Real.sqrt_le_sqrt hcard
  have hL : Real.sqrt ((N : ℝ) + 1) * s ^ 2 = Real.sqrt G.L := by
    rw [← hLs, hs4, show ((N : ℝ) + 1) = ((N : ℝ) + 1) from rfl]
    rw [mul_comm, show s ^ 4 * ((N : ℝ) + 1) = (s ^ 2) ^ 2 * ((N : ℝ) + 1) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  calc Real.sqrt ((Finset.univ : Finset cols).card : ℝ) * (Real.sqrt (C.c + 1) * Cσ * (C.cs.Kw * C.CM) * s ^ 2)
      ≤ Real.sqrt ((N : ℝ) + 1) * (Real.sqrt (C.c + 1) * Cσ * (C.cs.Kw * C.CM) * s ^ 2) :=
        mul_le_mul_of_nonneg_right hsq hBnn
    _ = Real.sqrt (C.c + 1) * Cσ * (C.cs.Kw * C.CM) * (Real.sqrt ((N : ℝ) + 1) * s ^ 2) := by ring
    _ = _ := by rw [hL]


theorem sq_aux (x y : ℝ) : y ^ 2 / 2 - (x - y) ^ 2 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - y / 2)]

theorem mul_aux {e h K : ℝ} (hh : h * (4 * e) ≤ K) : e * h ≤ K / 4 := by
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
  nlinarith

theorem subWindowConst_pos {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi : ℝ}
    {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) {CA : ℝ} (hCA0 : 0 ≤ CA) {a b : ℝ} (hab : a < b) :
    0 < subWindowConst C CA a b := by
  unfold subWindowConst
  obtain ⟨-, -, -, -, -, hcM1, hcMCM1, -, -, -⟩ := C.consts_pos
  have := C.cs.cm_pos
  have hK : 0 < (CA + 1) * ((C.cs.KA + C.cs.KB) * C.cs.Kw + 1) * (C.CM + 1) := by
    have h1 := mul_nonneg (add_nonneg C.cs.KA_nonneg C.cs.KB_nonneg) C.cs.Kw_nonneg
    have : 0 < C.CM + 1 := by linarith
    positivity
  have : 0 < b - a := by linarith
  positivity

/-- **Window mass of the eigenvector on a sub-window** (`||P_k Psi_k|| >= c_0`, `(I4)` lower bound, in global coordinates): for `c' <= a < b <= c` there are `c_0, h_1 > 0` with
`sum_{i : a <= u_i <= b} (Psi_k)_i^2 >= c_0^2` at every eigenvalue `X = X_k` in the block.  Route: `Psi = hat Psi + O(h^m env)` (`bulk_conj1`), `hat Psi = psi-hat^L/hat N` on `u <= c`,
`hat N <= C_N h^{-1/4}`, the window mass of `psi-hat^L` is `>= c_{[a,b]} h^{-1/2}` (`window_sum_lower_sub`), and `sum env^2 <= C` (`bulk_env_sq_sum`); `(x + e)^2 >= x^2/2 - e^2`. -/
theorem bulk_window_eig_lower {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V)
    (hm : 1 ≤ m) (hcoup : CR.c = Fz.L - CL.c' ∧ CR.c' = Fz.L - CL.c) (r : ℕ) (hr : StdAssump Fz P (m / 2) r)
    (a b : ℝ) (hab : a < b) (hca : CL.c' ≤ a) (hbc : b ≤ CL.c) :
    ∃ c0 h1 : ℝ, 0 < c0 ∧ 0 < h1 ∧ ∀ p ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        ∀ k : Fin (N + 1), Xs k = X →
          c0 ≤ Real.sqrt (∑ i ∈ subWin (Fz.step N) a b N, (eigVec Um k i) ^ 2) := by
  obtain ⟨Cc, h0, cN, CN, cκ, Cκ, hh0, hcN, hcκ, hall⟩ := bulk_conj1 CL CR hm hcoup r hr
  obtain ⟨CS, h1s, hh1s, hCS⟩ := bulk_env_sq_sum CL CR hm hcoup r hr
  obtain ⟨hPc, hEK, -⟩ := hr
  obtain ⟨CA, hCA0, hCA⟩ := bondA_bound_of_EK Fz P (m / 2) r hPc hEK
  obtain ⟨hc'L, hcc'L, hσL, hcσL, -, -, -, -, -, -⟩ := CL.consts_pos
  have hwcpos := subWindowConst_pos CL hCA0 hab
  set wc := subWindowConst CL CA a b with hwc
  set CN' : ℝ := |CN| + 1 with hCN'
  have hCN'0 : 0 < CN' := by positivity
  set Kc : ℝ := wc / CN' ^ 2 with hKc
  have hKc0 : 0 < Kc := by positivity
  set Ee : ℝ := Cc ^ 2 * |CS| + 1 with hEe
  have hEe0 : 0 < Ee := by positivity
  refine ⟨Real.sqrt (Kc / 4), min (min (min h0 h1s) (min 1 ((b - a) / 6))) (min CL.σ (Kc / (4 * Ee))), Real.sqrt_pos.mpr (by positivity),
    lt_min (lt_min (lt_min hh0 hh1s) (lt_min one_pos (by linarith))) (lt_min hσL (by positivity)), ?_⟩
  intro p hp X hX N hN hstep Xs Um hE k hk
  have hN1 : CL.N0 ≤ N := le_trans (le_max_left _ _) hN
  have hst : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hh0' : Fz.step N ≤ h0 := hstep.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hh1' : Fz.step N ≤ h1s := hstep.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hh1 : Fz.step N ≤ 1 := hstep.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hhd : Fz.step N ≤ (b - a) / 6 := hstep.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hhσ : Fz.step N ≤ CL.σ := hstep.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhE : Fz.step N ≤ Kc / (4 * Ee) := hstep.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hpos, hlow, hup, hκ, hev⟩ := hall p hp X hX N hN hh0'
  obtain ⟨-, hcmp⟩ := hev Xs Um hE k hk
  have hsumenv := hCS p hp X hX N hN hh1'
  obtain ⟨hs2, hs0⟩ := fourth_root_sq (Fz.step N) hst
  set s : ℝ := Fz.step N ^ ((1 : ℝ) / 4) with hsdef
  have hneg : Fz.step N ^ (-(1 : ℝ) / 4) = s⁻¹ := by
    rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring, Real.rpow_neg hst.le]
  rw [hneg] at hup
  have hsqrt : Real.sqrt (Fz.step N) = s ^ 2 := hs2.symm
  have hA : ∀ j : ℤ, 0 ≤ j → j ≤ (CL.chain p X N).NR - 1 → |(CL.chain p X N).A j| ≤ CA := by
    intro j h0' h1'
    rw [CL.A_bond p hp X hX N hN1 j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
    exact hCA p hp N j
  have hwin := window_sum_lower_sub CL CA hCA0 a b hca hab hbc p hp X hX N hN1 hhd hhσ hA
  -- on the window the glued vector is the left profile over the normaliser
  have hvec : ∀ i ∈ subWin (Fz.step N) a b N, bulkVec CL CR p X N i = CL.psiHatL p X N i / bulkNorm CL CR p X N := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    unfold bulkVec glueVec bulkNorm
    rw [ite_eq_left (hi'.2.trans hbc)]
  have hNle : bulkNorm CL CR p X N ≤ CN' * s⁻¹ := by
    refine hup.trans ?_
    exact mul_le_mul_of_nonneg_right (by rw [hCN']; linarith [le_abs_self CN]) (inv_nonneg.mpr hs0.le)
  have hN2 : bulkNorm CL CR p X N ^ 2 ≤ CN' ^ 2 / s ^ 2 := by
    calc bulkNorm CL CR p X N ^ 2 ≤ (CN' * s⁻¹) ^ 2 := pow_le_pow_left₀ hpos.le hNle 2
      _ = CN' ^ 2 / s ^ 2 := by field_simp
  -- mass of the normalised profile
  have hmass : Kc ≤ ∑ i ∈ subWin (Fz.step N) a b N, (bulkVec CL CR p X N i) ^ 2 := by
    have e : ∑ i ∈ subWin (Fz.step N) a b N, (bulkVec CL CR p X N i) ^ 2 =
        (∑ i ∈ subWin (Fz.step N) a b N, (CL.psiHatL p X N i) ^ 2) / bulkNorm CL CR p X N ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [hvec i hi, div_pow]
    rw [e, le_div_iff₀ (by positivity)]
    have h1 : wc / s ^ 2 ≤ ∑ i ∈ subWin (Fz.step N) a b N, (CL.psiHatL p X N i) ^ 2 := by
      rw [← hsqrt]; exact hwin
    calc Kc * bulkNorm CL CR p X N ^ 2 ≤ Kc * (CN' ^ 2 / s ^ 2) := mul_le_mul_of_nonneg_left hN2 hKc0.le
      _ = wc / s ^ 2 := by rw [hKc]; field_simp
      _ ≤ _ := h1
  -- the error
  have herr : ∑ i ∈ subWin (Fz.step N) a b N, (eigVec Um k i - bulkVec CL CR p X N i) ^ 2 ≤ Kc / 4 := by
    have hsub : subWin (Fz.step N) a b N ⊆ rowsOf N := Finset.filter_subset _ _
    calc ∑ i ∈ subWin (Fz.step N) a b N, (eigVec Um k i - bulkVec CL CR p X N i) ^ 2
        ≤ ∑ i ∈ subWin (Fz.step N) a b N, (Cc * Fz.step N ^ m) ^ 2 * (bulkEnv CL CR p X N i) ^ 2 := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          have h2 := hcmp i (hsub hi)
          calc (eigVec Um k i - bulkVec CL CR p X N i) ^ 2 = |eigVec Um k i - bulkVec CL CR p X N i| ^ 2 := (sq_abs _).symm
            _ ≤ (Cc * Fz.step N ^ m * bulkEnv CL CR p X N i) ^ 2 := by
                gcongr
            _ = _ := by ring
      _ = (Cc * Fz.step N ^ m) ^ 2 * ∑ i ∈ subWin (Fz.step N) a b N, (bulkEnv CL CR p X N i) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (Cc * Fz.step N ^ m) ^ 2 * CS := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          refine le_trans ?_ hsumenv
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ ≤ Cc ^ 2 * |CS| * Fz.step N := by
          have hpow : Fz.step N ^ (2 * m) ≤ Fz.step N := by
            calc Fz.step N ^ (2 * m) ≤ Fz.step N ^ 1 := pow_le_pow_of_le_one hst.le hh1 (by omega)
              _ = Fz.step N := pow_one _
          calc (Cc * Fz.step N ^ m) ^ 2 * CS = Cc ^ 2 * Fz.step N ^ (2 * m) * CS := by ring
            _ ≤ Cc ^ 2 * Fz.step N ^ (2 * m) * |CS| := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
            _ ≤ Cc ^ 2 * Fz.step N * |CS| := by gcongr
            _ = Cc ^ 2 * |CS| * Fz.step N := by ring
      _ ≤ Kc / 4 := by
          have h3 : Cc ^ 2 * |CS| * Fz.step N ≤ Ee * Fz.step N := by
            apply mul_le_mul_of_nonneg_right _ hst.le
            rw [hEe]; linarith
          have h4 : Ee * Fz.step N ≤ Kc / 4 := by
            have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Ee)).mp hhE
            exact mul_aux this
          linarith
  -- combine
  have hcomb : Kc / 4 ≤ ∑ i ∈ subWin (Fz.step N) a b N, (eigVec Um k i) ^ 2 := by
    have hpt : ∀ i ∈ subWin (Fz.step N) a b N, (bulkVec CL CR p X N i) ^ 2 / 2 - (eigVec Um k i - bulkVec CL CR p X N i) ^ 2 ≤ (eigVec Um k i) ^ 2 := by
      intro i _
      exact sq_aux _ _
    have := Finset.sum_le_sum hpt
    rw [Finset.sum_sub_distrib, ← Finset.sum_div] at this
    linarith
  exact Real.sqrt_le_sqrt hcomb


theorem eigVec_nat {N : ℕ} (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (k : Fin (N + 1)) (j : ℕ) (hj : j < N + 1) :
    eigVec Um k (j : ℤ) = Um ⟨j, hj⟩ k := by
  unfold eigVec
  rw [dite_eq_left ⟨by omega, by omega⟩]
  congr 2

/-- The window mass of the eigenvector on the global rows `[ga, gb]` is at most the mass on the chart rows `P_k = bulkPk` (global rows `lo + n`), provided the chart covers the global window; `[ga, gb] = [a, b]` for the
direction `+` and the mirror `[L - b, L - a]` for the direction `-` (chain row `N - i`, `uNode_mirror`). -/
theorem pk_sum_ge (N lo R : ℕ) (hlo : lo + R ≤ N + 1) (τ : Bool) (h L a b ga gb : ℝ) (hLs : h * ((N : ℝ) + 1) = L)
    (hg : (τ = true → ga = a ∧ gb = b) ∧ (τ = false → ga = L - b ∧ gb = L - a))
    (hcov : ∀ i ∈ subWin h ga gb N, (lo : ℤ) ≤ i ∧ i < lo + R)
    (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (k : Fin (N + 1)) :
    ∑ i ∈ subWin h ga gb N, (eigVec Um k i) ^ 2 ≤
      ∑ n ∈ bulkPk N lo R τ h a b, (Um ⟨lo + n.val, by have := n.isLt; omega⟩ k) ^ 2 := by
  have hsub : subWin h ga gb N ⊆ (bulkPk N lo R τ h a b).image (fun n : Fin R => ((lo + n.val : ℕ) : ℤ)) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := hcov i hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hi0 : 0 ≤ i - lo := by omega
    refine Finset.mem_image.mpr ⟨⟨(i - lo).toNat, by omega⟩, ?_, ?_⟩
    · unfold bulkPk
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hrow : (lo : ℤ) + ((i - lo).toNat : ℕ) = i := by omega
      cases τ
      · have e : chartRow N lo R false ⟨(i - lo).toNat, by omega⟩ = (N : ℤ) - i := by
          simp only [chartRow, Bool.false_eq_true, ite_false]
          push_cast
          omega
        rw [e, uNode_mirror L h N i hLs]
        obtain ⟨e1, e2⟩ := hg.2 rfl
        rw [e1, e2] at hi'
        constructor <;> linarith [hi'.1, hi'.2]
      · have e : chartRow N lo R true ⟨(i - lo).toNat, by omega⟩ = i := by
          simp only [chartRow, ite_true]
          omega
        rw [e]
        obtain ⟨e1, e2⟩ := hg.1 rfl
        rw [e1, e2] at hi'
        exact hi'
    · push_cast
      omega
  calc ∑ i ∈ subWin h ga gb N, (eigVec Um k i) ^ 2
      ≤ ∑ i ∈ (bulkPk N lo R τ h a b).image (fun n : Fin R => ((lo + n.val : ℕ) : ℤ)), (eigVec Um k i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ = ∑ n ∈ bulkPk N lo R τ h a b, (eigVec Um k ((lo + n.val : ℕ) : ℤ)) ^ 2 := by
        rw [Finset.sum_image]
        intro x _ y _ hxy
        apply Fin.ext
        have := hxy
        push_cast at this
        omega
    _ = _ := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [eigVec_nat Um k (lo + n.val) (by have := n.isLt; omega)]


/-- **`overlap_lb` for the left bulk chart**: `c_0 <= ||P_k Psi_k||` with `P_k` the chart rows (direction `+`, global rows `lo + n`) whose node lies in `[a, b]`, `c' <= a < b <= c`, provided the chart rows cover the global window
`{i : a <= u_i <= b}`.  From `bulk_window_eig_lower` and `pk_sum_ge`. -/
theorem bulkJBChartL_overlap_lb {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi Jlo1 Jhi1 : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V)
    (C1 : BulkWeberChart Fz P Jlo1 Jhi1 (m + 1) U V)
    (TI : TransferInputs Fz P (fun _ => Jlo) (fun _ => Jhi) m CL.chain C1.chain 1 (fun _ => 0) (fun _ => CL.c + CL.σ / 2))
    (hm : 1 ≤ m) (hcoup : CR.c = Fz.L - CL.c' ∧ CR.c' = Fz.L - CL.c) (r : ℕ) (hr : StdAssump Fz P (m / 2) r)
    (a b : ℝ) (hab : a < b) (hca : CL.c' ≤ a) (hbc : b ≤ CL.c) :
    ∃ c0 h1 : ℝ, 0 < c0 ∧ 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
      ∀ (cols : Finset (Fin (N + 1))) (lo R : ℕ) (hlo : lo + R ≤ N + 1) (used : Finset (Fin R)) (σ0 σ1 : cols → ℝ)
        (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        (∀ k : cols, Xs k ∈ Set.Icc Jlo Jhi) → (∀ i ∈ subWin (Fz.step N) a b N, (lo : ℤ) ≤ i ∧ i < lo + R) →
        ∀ k : cols, c0 ≤ FormalResearch.JB.jbL2 (bulkPk N lo R true (Fz.step N) a b)
          (fun n => Um ((bulkJBChart CL C1 TI p N Xs cols lo R hlo true used (fun _ => bulkPk N lo R true (Fz.step N) a b) σ0 σ1 host0 host1).row n) k) := by
  obtain ⟨c0, h1, hc0, hh1, hwin⟩ := bulk_window_eig_lower CL CR hm hcoup r hr a b hab hca hbc
  refine ⟨c0, h1, hc0, hh1, ?_⟩
  intro p hp N hN hstep Xs Um hE cols lo R hlo used σ0 σ1 host0 host1 hX hcov k
  have h := hwin p hp (Xs k) (hX k) N hN hstep Xs Um hE k rfl
  have hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L := step_mul_succ Fz N
  have hpk := pk_sum_ge N lo R hlo true (Fz.step N) Fz.L a b a b hLs ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by simp)⟩ hcov Um k
  refine h.trans ?_
  unfold FormalResearch.JB.jbL2
  exact Real.sqrt_le_sqrt hpk

/-- **`overlap_lb` for the right (mirror) bulk chart**: the window `[a, b]` of the mirror chart (`c'_R <= a < b <= c_R`) corresponds to the global rows `[L - b, L - a]`, which lie in the window of the left chart by the mirror overlap. -/
theorem bulkJBChartR_overlap_lb {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi Jlo1 Jhi1 : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V)
    (C1 : BulkWeberChart (mirrorFamily Fz) P Jlo1 Jhi1 (m + 1) U V)
    (TI : TransferInputs (mirrorFamily Fz) P (fun _ => Jlo) (fun _ => Jhi) m CR.chain C1.chain 1 (fun _ => 0) (fun _ => CR.c + CR.σ / 2))
    (hm : 1 ≤ m) (hcoup : CR.c = Fz.L - CL.c' ∧ CR.c' = Fz.L - CL.c) (r : ℕ) (hr : StdAssump Fz P (m / 2) r)
    (a b : ℝ) (hab : a < b) (hca : CR.c' ≤ a) (hbc : b ≤ CR.c) :
    ∃ c0 h1 : ℝ, 0 < c0 ∧ 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
      ∀ (cols : Finset (Fin (N + 1))) (lo R : ℕ) (hlo : lo + R ≤ N + 1) (used : Finset (Fin R)) (σ0 σ1 : cols → ℝ)
        (host0 host1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        (∀ k : cols, Xs k ∈ Set.Icc Jlo Jhi) → (∀ i ∈ subWin (Fz.step N) (Fz.L - b) (Fz.L - a) N, (lo : ℤ) ≤ i ∧ i < lo + R) →
        ∀ k : cols, c0 ≤ FormalResearch.JB.jbL2 (bulkPk N lo R false ((mirrorFamily Fz).step N) a b)
          (fun n => Um ((bulkJBChart CR C1 TI p N Xs cols lo R hlo false used (fun _ => bulkPk N lo R false ((mirrorFamily Fz).step N) a b) σ0 σ1 host0 host1).row n) k) := by
  have hab' : Fz.L - b < Fz.L - a := by linarith
  have hca' : CL.c' ≤ Fz.L - b := by linarith [hcoup.1]
  have hbc' : Fz.L - a ≤ CL.c := by linarith [hcoup.2]
  obtain ⟨c0, h1, hc0, hh1, hwin⟩ := bulk_window_eig_lower CL CR hm hcoup r hr (Fz.L - b) (Fz.L - a) hab' hca' hbc'
  refine ⟨c0, h1, hc0, hh1, ?_⟩
  intro p hp N hN hstep Xs Um hE cols lo R hlo used σ0 σ1 host0 host1 hX hcov k
  have h := hwin p hp (Xs k) (hX k) N hN hstep Xs Um hE k rfl
  have hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L := step_mul_succ Fz N
  have hpk := pk_sum_ge N lo R hlo false (Fz.step N) Fz.L a b (Fz.L - b) (Fz.L - a) hLs
    ⟨fun h => absurd h (by simp), fun _ => ⟨rfl, rfl⟩⟩ hcov Um k
  refine h.trans ?_
  unfold FormalResearch.JB.jbL2
  exact Real.sqrt_le_sqrt hpk

end Design


section Match

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **`match0` for the left chart** (`OneStepInputs.match0`): `hat G^{[m]}` at the *final* splice `splF` agrees with `H^{[m]}_c` of the left chart on the used rows (the chart rows `<= n_nu = nearestRow (splF nu)`), although the chart's host
may be built at another (extreme) splice `spl`: the scalars `1/hat N` do not depend on the splice. -/
theorem blockChartL_match0 (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl splF : Fin CP.CI0.nb → ℝ) (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν : Fin CP.CI0.nb)
    (cols : Finset (Fin (N + 1))) (hcols : ∀ k ∈ cols, blockOf CP.CI0 (Xs k) = some ν) (R : ℕ) (hlo : 0 + R ≤ N + 1)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (hused : ∀ n ∈ used, ((n.val : ℕ) : ℤ) ≤ nearestRow (F.step N) (splF ν)) :
    ∀ n ∈ used, ∀ k : cols, compMatrix CP.CI0 splF μ N Xs ((blockChartL CP TB spl μ N Xs ν cols R hlo used Pk).row n) k =
      (blockChartL CP TB spl μ N Xs ν cols R hlo used Pk).H0 (F.step N) n k := by
  intro n hn k
  have hk := hcols k k.2
  unfold blockChartL
  symm
  erw [bulkJBChart_H0]
  simp only [bulkJBChart, FormalResearch.JB.Chart.row]
  rw [compMatrix_bulk_entry CP.CI0 splF μ N Xs ν k hk]
  have hn' : ((((0 : ℕ) + n.val : ℕ)) : ℤ) ≤ nearestRow (F.step N) (splF ν) := by
    have := hused n hn
    omega
  rw [ite_eq_left hn']
  have hcr : chartRow N 0 R true n = (((0 : ℕ) + n.val : ℕ) : ℤ) := by simp [chartRow]
  rw [hcr]
  ring

/-- **`match0` for the right chart** (used rows: chart rows with global row `lo + n > n_nu`). -/
theorem blockChartR_match0 (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl splF : Fin CP.CI0.nb → ℝ) (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν : Fin CP.CI0.nb)
    (cols : Finset (Fin (N + 1))) (hcols : ∀ k ∈ cols, blockOf CP.CI0 (Xs k) = some ν) (lo R : ℕ) (hlo : lo + R ≤ N + 1)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (hused : ∀ n ∈ used, nearestRow (F.step N) (splF ν) < ((lo + n.val : ℕ) : ℤ)) :
    ∀ n ∈ used, ∀ k : cols, compMatrix CP.CI0 splF μ N Xs ((blockChartR CP TB spl μ N Xs ν cols lo R hlo used Pk).row n) k =
      (blockChartR CP TB spl μ N Xs ν cols lo R hlo used Pk).H0 (F.step N) n k := by
  intro n hn k
  have hk := hcols k k.2
  unfold blockChartR
  symm
  erw [bulkJBChart_H0]
  simp only [bulkJBChart, FormalResearch.JB.Chart.row]
  rw [compMatrix_bulk_entry CP.CI0 splF μ N Xs ν k hk]
  have hn' : ¬ ((((lo + n.val : ℕ)) : ℤ) ≤ nearestRow (F.step N) (splF ν)) := by
    have := hused n hn
    omega
  rw [ite_eq_right hn']
  have hcr : chartRow N lo R false n = (N : ℤ) - (((lo + n.val : ℕ) : ℤ)) := by simp [chartRow]
  rw [hcr]
  ring

/-- **`match1` for the left chart** (order `m + 1`, final splice `spl1 splF`; uses `blockOf_cast`). -/
theorem blockChartL_match1 (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl splF : Fin CP.CI0.nb → ℝ) (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν : Fin CP.CI0.nb)
    (cols : Finset (Fin (N + 1))) (hcols : ∀ k ∈ cols, blockOf CP.CI0 (Xs k) = some ν) (R : ℕ) (hlo : 0 + R ≤ N + 1)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (hused : ∀ n ∈ used, ((n.val : ℕ) : ℤ) ≤ nearestRow (F.step N) (splF ν))
    (hp : atStep F μ N ∈ paramSet K t0) (hNT : (TB.bulkL ν).N0 ≤ N) :
    ∀ n ∈ used, ∀ k : cols, compMatrix CP.CI1 (CP.spl1 splF) μ N Xs ((blockChartL CP TB spl μ N Xs ν cols R hlo used Pk).row n) k =
      (blockChartL CP TB spl μ N Xs ν cols R hlo used Pk).H1 (F.step N) n k := by
  intro n hn k
  have hk := hcols k k.2
  have hk1 := blockOf_cast CP (Xs k) ν hk
  have hX : ∀ k : cols, Xs k ∈ Set.Icc (CP.CI0.lo ν) (CP.CI0.hi ν) := fun k => blockOf_spec CP.CI0 (Xs k) ν (hcols k k.2)
  unfold blockChartL
  symm
  erw [bulkJBChart_H1 (CP.CI0.bulkL ν) (CP.CI1.bulkL (Fin.cast CP.nb_eq.symm ν)) (TB.bulkL ν) (atStep F μ N) hp N hNT Xs cols 0 R hlo true used Pk _ _ _ _ hX n k]
  simp only [bulkJBChart, FormalResearch.JB.Chart.row]
  rw [compMatrix_bulk_entry CP.CI1 (CP.spl1 splF) μ N Xs (Fin.cast CP.nb_eq.symm ν) k hk1]
  have hs : CP.spl1 splF (Fin.cast CP.nb_eq.symm ν) = splF ν := by simp [ChartPair.spl1]
  rw [hs]
  have hn' : ((((0 : ℕ) + n.val : ℕ)) : ℤ) ≤ nearestRow (F.step N) (splF ν) := by
    have := hused n hn
    omega
  rw [ite_eq_left hn']
  have hcr : chartRow N 0 R true n = (((0 : ℕ) + n.val : ℕ) : ℤ) := by simp [chartRow]
  rw [hcr]
  ring

/-- **`match1` for the right chart.** -/
theorem blockChartR_match1 (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl splF : Fin CP.CI0.nb → ℝ) (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν : Fin CP.CI0.nb)
    (cols : Finset (Fin (N + 1))) (hcols : ∀ k ∈ cols, blockOf CP.CI0 (Xs k) = some ν) (lo R : ℕ) (hlo : lo + R ≤ N + 1)
    (used : Finset (Fin R)) (Pk : cols → Finset (Fin R)) (hused : ∀ n ∈ used, nearestRow (F.step N) (splF ν) < ((lo + n.val : ℕ) : ℤ))
    (hp : atStep F μ N ∈ paramSet K t0) (hNT : (TB.bulkR ν).N0 ≤ N) :
    ∀ n ∈ used, ∀ k : cols, compMatrix CP.CI1 (CP.spl1 splF) μ N Xs ((blockChartR CP TB spl μ N Xs ν cols lo R hlo used Pk).row n) k =
      (blockChartR CP TB spl μ N Xs ν cols lo R hlo used Pk).H1 (F.step N) n k := by
  intro n hn k
  have hk := hcols k k.2
  have hk1 := blockOf_cast CP (Xs k) ν hk
  have hX : ∀ k : cols, Xs k ∈ Set.Icc (CP.CI0.lo ν) (CP.CI0.hi ν) := fun k => blockOf_spec CP.CI0 (Xs k) ν (hcols k k.2)
  unfold blockChartR
  symm
  erw [bulkJBChart_H1 (CP.CI0.bulkR ν) (CP.CI1.bulkR (Fin.cast CP.nb_eq.symm ν)) (TB.bulkR ν) (atStep F μ N) hp N hNT Xs cols lo R hlo false used Pk _ _ _ _ hX n k]
  simp only [bulkJBChart, FormalResearch.JB.Chart.row]
  rw [compMatrix_bulk_entry CP.CI1 (CP.spl1 splF) μ N Xs (Fin.cast CP.nb_eq.symm ν) k hk1]
  have hs : CP.spl1 splF (Fin.cast CP.nb_eq.symm ν) = splF ν := by simp [ChartPair.spl1]
  rw [hs]
  have hn' : ¬ ((((lo + n.val : ℕ)) : ℤ) ≤ nearestRow (F.step N) (splF ν)) := by
    have := hused n hn
    omega
  rw [ite_eq_right hn']
  have hcr : chartRow N lo R false n = (N : ℤ) - (((lo + n.val : ℕ) : ℤ)) := by simp [chartRow]
  rw [hcr]
  ring

end Match

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.blockIdx_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.blockIdx_cast

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.blockOf_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.blockOf_cast

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.blockOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.blockOf_spec

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.blockChartL_host0_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.blockChartL_host0_eq

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.blockChartR_host0_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.blockChartR_host0_eq

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.blockChartL_host1_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.blockChartL_host1_eq

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.blockChartR_host1_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.blockChartR_host1_eq

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.window_sum_lower_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.window_sum_lower_sub

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulk_wf_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulk_wf_bound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChart_phi1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChart_phi1

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.jbL2_le_sqrt_card_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.jbL2_le_sqrt_card_mul

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChart_overlap_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChart_overlap_ub

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulk_sigma_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulk_sigma_bound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChart_ext_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChart_ext_row

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulk_window_eig_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulk_window_eig_lower

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.pk_sum_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.pk_sum_ge

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChartL_overlap_lb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChartL_overlap_lb

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChartR_overlap_lb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulkJBChartR_overlap_lb

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.blockChartL_match0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.blockChartL_match0

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.blockChartR_match0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.blockChartR_match0

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.blockChartL_match1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.blockChartL_match1

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.blockChartR_match1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.blockChartR_match1

end FormalResearch.JacobiEigenvectors.TheoremB
