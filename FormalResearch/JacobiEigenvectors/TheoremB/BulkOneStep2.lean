module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.BulkOneStep

/-!
# Paper J, Theorem B, L3.5a (bulk charts to `JB.Chart`), part 2: the two-order block correspondence, `host1_eq`, and the bulk design fields

Source: Paper J `thmB.tex` `eq:thb-bulkcol`, `def:thb-inputs`, `app_thmB.tex` "Charts, bootstrap blocks and directions".

## Proved here

* `blockIdx_cast`, `blockOf_cast` (**finding F-B11, applied**): with `compColumn` choosing the *least* bulk block (`blockIdx`, `ComparisonMatrix.lean`), the blocks that the two orders
  `CI0` (order `m`) and `CI1` (order `m + 1`) of a `ChartPair` assign to the same energy correspond under `Fin.cast CP.nb_eq`.
* `blockChartL`, `blockChartR`: the `JB.Chart` of the left / right bulk chart of the block `nu`, with the scalars `sigma^{[r]}` and the hosts `compMatrix CI0 spl`, `compMatrix CI1 (spl1 spl)` fixed by the paper
  (left: `sigma = 1/hat N`, right: `sigma = hat kappa/hat N`, each at its own order); only `used`, `P_k`, `lo`, `R` are design data.
* `blockChartL_host0_eq`, `blockChartR_host0_eq`, **`blockChartL_host1_eq`, `blockChartR_host1_eq`** (the `host0_eq`, `host1_eq` fields of `JB.Chart.Ok` for these charts, both orders).
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
  · rw [dif_pos h0] at h
    have hν : blockIdx CP.CI0 X h0 = ν := Option.some.inj h
    have h1 : ∃ ν' : Fin CP.CI1.nb, CP.CI1.lo ν' ≤ X ∧ X ≤ CP.CI1.hi ν' := by
      refine ⟨Fin.cast CP.nb_eq.symm ν, ?_, ?_⟩
      · rw [CP.lo_eq]; simpa using (hν ▸ (blockIdx_spec CP.CI0 X h0).1)
      · rw [CP.hi_eq]; simpa using (hν ▸ (blockIdx_spec CP.CI0 X h0).2)
    rw [dif_pos h1]
    congr 1
    apply Fin.ext
    have := congrArg Fin.val (blockIdx_cast CP X h0 h1)
    simp only [Fin.coe_cast] at this ⊢
    rw [this, hν]
  · rw [dif_neg h0] at h
    exact absurd h (by simp)

end Cast

section Charts

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

theorem blockOf_spec (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (X : ℝ) (ν : Fin CI.nb) (h : blockOf CI X = some ν) :
    CI.lo ν ≤ X ∧ X ≤ CI.hi ν := by
  unfold blockOf at h
  by_cases hex : ∃ ν' : Fin CI.nb, CI.lo ν' ≤ X ∧ X ≤ CI.hi ν'
  · rw [dif_pos hex] at h
    have := Option.some.inj h
    rw [← this]
    exact blockIdx_spec CI X hex
  · rw [dif_neg hex] at h
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
  rw [if_pos hn]
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
  rw [if_neg hn]
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

end Design

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

end FormalResearch.JacobiEigenvectors.TheoremB
