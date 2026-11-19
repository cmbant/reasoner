module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.BulkOneStep2
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbGeom
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbBlocks
public import FormalResearch.JacobiEigenvectors.TheoremB.HostCols

/-!
# Paper J, Theorem B, L3.5c, part 5: the bulk blocks (`OneStepInputs` charts of a bulk block)

Source: Paper J `app_thmB.tex`, proof of `prop:thb-inputs`: the two Weber charts of a bulk block, (I1)--(I5) for them.

For the fixed splice `spl nu` (in the open overlap of both orders) the two charts of the bulk block `nu` are `blockChartL` (rows `0 .. n_s`, direction `+`) and `blockChartR` (rows `n_s + 1 .. N`, direction `-`),
`n_s = nearestRow h (spl nu)`, with `used = univ` (the hosts are the final comparison matrices themselves, `compMatrix CI0 spl`, `compMatrix CI1 (spl1 spl)`, so `match0/1` is `host0_eq/host1_eq`);
the overlap windows `P_k` are the chart rows whose node lies in the sub-windows `[a_L, b_L]` (left; `b_L < spl`) and `[a_R, b_R]` (right; `a_R > spl`) of the common overlap `[max c', min c]` of the two orders.
The two charts together cover all rows, so the block contributes nothing to `outside`.

## Proved here

* `bulk_block_left`, `bulk_block_right`: constants `cs`, `N_0`, `h_0` such that for every `mu in K`, `N >= N_0`, `h <= h_0`, every eigen-system and every column set of the block, the chart is `Chart.Ok`, matches `G^{[m]}`, `G^{[m+1]}` on all
  its rows, and covers the rows `<= n_s` resp. `> n_s`.
* `bulk_block`: both charts as a `ThbBlock`, uniform constants.

## Differences from the paper

* The hosts are at the fixed splice itself (not at the extreme splices): the statement `PropThbInputs` fixes `spl`, so the splice-moved hosts of the paper are not needed.
* The standing assumptions `StdAssump (frozenFamily F Kidx) (paramSet K t0) ..` are hypotheses here (F-t0, restricted in `ThbInputs`); the host bound (`PropThaSpliceTwoOrders`) is a hypothesis `hhost`.

## Not formalised

Nothing of the bulk charts.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine FormalResearch.JB

open scoped Classical

/-- The number of rows `n_s + 1` of the left bulk chart (rows `0 .. n_s`). -/
def bulkRL (h s : ℝ) : ℕ := (nearestRow h s).toNat + 1

/-- The number of rows `N - n_s` of the right bulk chart (rows `n_s + 1 .. N`). -/
def bulkRR (N : ℕ) (h s : ℝ) : ℕ := N - (nearestRow h s).toNat

section Bulk

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
  (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
  (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ)

/-- The common overlap `[max c', min c]` of the two orders of the block `nu`. -/
def bulkWinLo (ν : Fin CP.CI0.nb) : ℝ := max (CP.CI0.bulkL ν).c' (CP.CI1.bulkL (Fin.cast CP.nb_eq.symm ν)).c'
def bulkWinHi (ν : Fin CP.CI0.nb) : ℝ := min (CP.CI0.bulkL ν).c (CP.CI1.bulkL (Fin.cast CP.nb_eq.symm ν)).c

/-- The sub-window of the left chart: `[max c', (max c' + spl)/2]`. -/
def bulkLa (ν : Fin CP.CI0.nb) : ℝ := bulkWinLo CP ν
def bulkLb (ν : Fin CP.CI0.nb) : ℝ := (bulkWinLo CP ν + spl ν) / 2
/-- The sub-window of the right chart in global coordinates: `[(spl + min c)/2, min c]`. -/
def bulkRga (ν : Fin CP.CI0.nb) : ℝ := (spl ν + bulkWinHi CP ν) / 2
def bulkRgb (ν : Fin CP.CI0.nb) : ℝ := bulkWinHi CP ν

/-- The left chart of the bulk block `nu` with the design data of the assembly. -/
def bulkLeftChart (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν : Fin CP.CI0.nb) (cols : Finset (Fin (N + 1)))
    (hlo : 0 + bulkRL (F.step N) (spl ν) ≤ N + 1) : Chart (N + 1) (bulkRL (F.step N) (spl ν)) cols :=
  blockChartL CP TB spl μ N Xs ν cols (bulkRL (F.step N) (spl ν)) hlo Finset.univ
    (fun _ => bulkPk N 0 (bulkRL (F.step N) (spl ν)) true (F.step N) (bulkLa CP ν) (bulkLb CP spl ν))

/-- The right chart of the bulk block `nu`: mirror windows `[L - b_R, L - a_R]`. -/
def bulkRightChart (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ) (ν : Fin CP.CI0.nb) (cols : Finset (Fin (N + 1)))
    (hlo : (nearestRow (F.step N) (spl ν)).toNat + 1 + bulkRR N (F.step N) (spl ν) ≤ N + 1) :
    Chart (N + 1) (bulkRR N (F.step N) (spl ν)) cols :=
  blockChartR CP TB spl μ N Xs ν cols ((nearestRow (F.step N) (spl ν)).toNat + 1) (bulkRR N (F.step N) (spl ν)) hlo Finset.univ
    (fun _ => bulkPk N ((nearestRow (F.step N) (spl ν)).toNat + 1) (bulkRR N (F.step N) (spl ν)) false (F.step N)
      (F.L - bulkRgb CP ν) (F.L - bulkRga CP spl ν))


/-- Hypothesis `hhost` of the block lemmas: the columns of the two hosts (the matrices `G^{[m]}`, `G^{[m+1]}` themselves) are close to those of `U` (`PropThaSpliceTwoOrders` in the form of `hostCols_of_twoOrders`). -/
def HostBound (K : Set Par) (CI0 : ChartInputs F K Kidx t0 m q U V cPC CPC) (CI1 : ChartInputs F K Kidx t0 (m + 1) q U V cPC CPC)
    (spl0 : Fin CI0.nb → ℝ) (spl1 : Fin CI1.nb → ℝ) : Prop :=
  ∃ Ch h0 : ℝ, 0 ≤ Ch ∧ 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 → F.step N ≤ t0 →
    ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
      ∀ j : Fin (N + 1),
        jbL2 Finset.univ (fun i => compMatrix CI0 spl0 μ N Xs i j - Um i j) ≤ Ch * F.step N ^ m ∧
        jbL2 Finset.univ (fun i => compMatrix CI1 spl1 μ N Xs i j - Um i j) ≤ Ch * F.step N ^ (m + 1) * Real.log (1 / F.step N)

theorem eig_frozen {μ : Par} {N : ℕ} {Xs : Fin (N + 1) → ℝ} {Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hE : IsEigenSystem (F.jacobiMat μ N) Xs Um) :
    IsEigenSystem ((frozenFamily F Kidx).jacobiMat (atStep F μ N) N) Xs Um := by
  unfold atStep
  rw [frozenFamily_jacobiMat_at_step]
  exact hE

theorem atStep_mem {μ : Par} (hμ : μ ∈ K) (N : ℕ) (ht : F.step N ≤ t0) : atStep F μ N ∈ paramSet K t0 := by
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  exact ⟨hμ, ⟨by show -t0 ≤ F.step N; linarith, ht⟩⟩

theorem bulk_block_left (hs : CP.SplicesInWindow spl) (hm : 1 ≤ m) (ht0 : 0 < t0)
    (hstd0 : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) (m / 2) r)
    (hstd1 : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) ((m + 1) / 2) r)
    (hhost : HostBound K CP.CI0 CP.CI1 spl (CP.spl1 spl)) (ν : Fin CP.CI0.nb) :
    ∃ (cs : OneStepConsts) (N0 : ℕ) (h0 : ℝ), 0 < h0 ∧ h0 ≤ 1 ∧ ∀ μ ∈ K, ∀ N : ℕ, N0 ≤ N → F.step N ≤ h0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
      ∀ cols : Finset (Fin (N + 1)), (∀ k ∈ cols, blockOf CP.CI0 (Xs k) = some ν) →
        ∃ hlo : 0 + bulkRL (F.step N) (spl ν) ≤ N + 1,
          (bulkLeftChart CP TB spl μ N Xs ν cols hlo).Ok cs m (F.step N) Um ∧
          (∀ (n) (k : cols), compMatrix CP.CI0 spl μ N Xs ((bulkLeftChart CP TB spl μ N Xs ν cols hlo).row n) k =
            (bulkLeftChart CP TB spl μ N Xs ν cols hlo).H0 (F.step N) n k) ∧
          (∀ (n) (k : cols), compMatrix CP.CI1 (CP.spl1 spl) μ N Xs ((bulkLeftChart CP TB spl μ N Xs ν cols hlo).row n) k =
            (bulkLeftChart CP TB spl μ N Xs ν cols hlo).H1 (F.step N) n k) ∧
          (∀ i : Fin (N + 1), ((i : ℕ) : ℤ) ≤ nearestRow (F.step N) (spl ν) →
            ∃ n : Fin (bulkRL (F.step N) (spl ν)), (bulkLeftChart CP TB spl μ N Xs ν cols hlo).row n = i) := by
  obtain ⟨r0, hr0⟩ := hstd0
  obtain ⟨r1, hr1⟩ := hstd1
  obtain ⟨Ch, hHr, hCh0, hHpos, Hhost⟩ := hhost
  set ν' : Fin CP.CI1.nb := Fin.cast CP.nb_eq.symm ν with hν'
  have hcoup0 := CP.CI0.overlap_match ν
  have hcoup1 := CP.CI1.overlap_match ν'
  have hs0 : (CP.CI0.bulkL ν).c' < spl ν ∧ spl ν < (CP.CI0.bulkL ν).c := hs.1 ν
  have hs1 : (CP.CI1.bulkL ν').c' < spl ν ∧ spl ν < (CP.CI1.bulkL ν').c := by
    have := hs.2 ν'
    simpa [ChartPair.spl1, hν'] using this
  have hJ1 : CP.CI0.lo ν = CP.CI1.lo ν' := by rw [CP.lo_eq]; rfl
  have hJ2 : CP.CI0.hi ν = CP.CI1.hi ν' := by rw [CP.hi_eq]; rfl
  obtain ⟨Cσ, hσh, hCσ0, hσpos, Hσ⟩ := bulk_sigma_bound (CP.CI1.bulkL ν') (CP.CI1.bulkR ν') (by omega) hcoup1 r1 hr1
  obtain ⟨CE, hEr, hCE0, hEpos, HE⟩ := bulkJBChart_ext_row (CP.CI0.bulkL ν) (CP.CI1.bulkL ν') (TB.bulkL ν) Cσ hCσ0
  have hr0' := hr0
  obtain ⟨hPc, hEK, -⟩ := hr0'
  obtain ⟨CA, hCA0, hCA⟩ := bondA_bound_of_EK (frozenFamily F Kidx) (paramSet K t0) (m / 2) r0 hPc hEK
  set CL0 := CP.CI0.bulkL ν with hCL0
  set CR0 := CP.CI0.bulkR ν with hCR0
  set CL1 := CP.CI1.bulkL ν' with hCL1
  set aL := bulkLa CP ν with haL
  set bL := bulkLb CP spl ν with hbL
  have hA_lt_s : aL < spl ν := max_lt hs0.1 hs1.1
  have hab : aL < bL := by simp only [hbL, bulkLb, haL, bulkLa] at *; linarith
  have hbs : bL < spl ν := by simp only [hbL, bulkLb, haL, bulkLa] at *; linarith
  have hca : CL0.c' ≤ aL := le_max_left _ _
  have hca1 : CL1.c' ≤ aL := le_max_right _ _
  have hbc : bL ≤ CL0.c := by linarith [hs0.2]
  have hbc1 : bL ≤ CL1.c := by linarith [hs1.2]
  obtain ⟨C4, hu1, hC40, hupos, HU⟩ := bulkJBChart_overlap_ub CL0 CL1 (TB.bulkL ν) CA hCA0 hCA aL bL hab hca hbc hca1 hbc1
  obtain ⟨c0, hl1, hc0pos, hlpos, HL⟩ := bulkJBChartL_overlap_lb CL0 CR0 CL1 (TB.bulkL ν) hm hcoup0 r0 hr0 aL bL hab hca hbc
  set TI := TB.bulkL ν with hTI
  obtain ⟨hrect, hcTp, hcαp, hS0, hωp⟩ := TI.consts_pos
  have hc'pos : 0 < CL0.c' := CL0.consts_pos.1
  have hσpos' : 0 < CL0.σ := CL0.consts_pos.2.2.1
  have hcL : CL0.c + CL0.σ < F.L := CL0.consts_pos.2.2.2.1
  obtain ⟨h0, hh0pos, hle⟩ : ∃ h0 : ℝ, 0 < h0 ∧ ∀ x : ℝ, x ≤ h0 → x ≤ 1 ∧ x ≤ t0 ∧ x ≤ hσh ∧ x ≤ hEr ∧ x ≤ hu1 ∧ x ≤ hl1 ∧ x ≤ hHr ∧
      x ≤ CL0.σ ∧ x ≤ 2 * (CL0.c - spl ν) / 3 ∧ x ≤ 2 * (spl ν - CL0.c') := by
    refine ⟨min 1 (min t0 (min hσh (min hEr (min hu1 (min hl1 (min hHr (min CL0.σ (min (2 * (CL0.c - spl ν) / 3) (2 * (spl ν - CL0.c')))))))))), ?_, fun x hx => ?_⟩
    · simp only [lt_min_iff]
      refine ⟨one_pos, ht0, hσpos, hEpos, hupos, hlpos, hHpos, hσpos', by linarith [hs0.2], by linarith [hs0.1]⟩
    · simp only [le_min_iff] at hx
      exact hx
  set cs : OneStepConsts :=
    ⟨0, Ch, max (chartSchurK 0 (CL0.c + CL0.σ / 2) (CP.CI0.lo ν) (CP.CI0.hi ν) TI.S TI.cT TI.cα 1) 0, TI.ωmax, TI.cT, TI.cα, c0, C4, CE,
      hCh0, le_max_right _ _, hωp, hcTp, hcαp, hc0pos, hC40, hCE0⟩ with hcs
  refine ⟨cs, max CL0.N0 (max CR0.N0 (max CL1.N0 (max (CP.CI1.bulkR ν').N0 TI.N0))), h0, hh0pos, (hle h0 le_rfl).1, ?_⟩
  intro μ hμ N hN hstep Xs Um hE cols hcols
  simp only [max_le_iff] at hN
  obtain ⟨hN0L, hN0R, hN1L, hN1R, hNT⟩ := hN
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hLs : F.step N * ((N : ℝ) + 1) = F.L := step_mul_succ F N
  obtain ⟨hh1, ht, hsσh, hsEr, hsu1, hsl1, hsHr, hsσ, hs2, hs3⟩ := hle _ hstep
  have hp := atStep_mem hμ N ht
  have hE' := eig_frozen (Kidx := Kidx) hE
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := bulk_geom hst hLs hc'pos hs0.1 hs0.2 hσpos' hcL hsσ hs2 hs3
  set ns := nearestRow (F.step N) (spl ν) with hns
  have hRL : bulkRL (F.step N) (spl ν) = ns.toNat + 1 := rfl
  have hlo : 0 + bulkRL (F.step N) (spl ν) ≤ N + 1 := by rw [hRL]; omega
  have hX : ∀ k : cols, Xs k ∈ Set.Icc (CP.CI0.lo ν) (CP.CI0.hi ν) := fun k => blockOf_spec CP.CI0 (Xs k) ν (hcols k k.2)
  have hX1 : ∀ k : cols, Xs k ∈ Set.Icc (CP.CI1.lo ν') (CP.CI1.hi ν') := fun k => by rw [← hJ1, ← hJ2]; exact hX k
  have hrow : ∀ n : Fin (bulkRL (F.step N) (spl ν)), chartRow N 0 (bulkRL (F.step N) (spl ν)) true n = (n.val : ℤ) := by
    intro n; simp [chartRow]
  have hRn : ∀ n : Fin (bulkRL (F.step N) (spl ν)), (n.val : ℤ) ≤ ns := by
    intro n; have h1 : n.val < ns.toNat + 1 := n.isLt; omega
  have hrows : ∀ n : Fin (bulkRL (F.step N) (spl ν)), 0 ≤ chartRow N 0 (bulkRL (F.step N) (spl ν)) true n ∧
      uNode ((frozenFamily F Kidx).step N) (chartRow N 0 (bulkRL (F.step N) (spl ν)) true n) ≤ CL0.c := by
    intro n
    rw [hrow n]
    refine ⟨by positivity, ?_⟩
    exact ((uNode_le_iff hst _ _).mpr (hRn n)).trans g6
  have hext : chartExtRow N 0 (bulkRL (F.step N) (spl ν)) true = ns + 1 := by
    simp only [chartExtRow, if_true, hRL]; omega
  have hcov : ∀ i ∈ subWin (F.step N) aL bL N, ((0 : ℕ) : ℤ) ≤ i ∧ i < ((0 : ℕ) : ℤ) + (bulkRL (F.step N) (spl ν) : ℤ) := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hi0 : (0 : ℤ) ≤ i := (Finset.mem_Icc.mp hi'.1).1
    refine ⟨by simpa using hi0, ?_⟩
    by_contra hcon
    push Not at hcon
    have hge : ns + 1 ≤ i := by rw [hRL] at hcon; push_cast at hcon; omega
    have h1 := (uNode_le_iff hst _ _).mpr hge
    have h2 := hi'.2.2
    linarith
  have hcov' : ∀ j ∈ subWin (F.step N) aL bL N, ∃ n : Fin (bulkRL (F.step N) (spl ν)), chartRow N 0 (bulkRL (F.step N) (spl ν)) true n = j := by
    intro j hj
    have := hcov j hj
    refine ⟨⟨j.toNat, by simp at this; omega⟩, ?_⟩
    simp only [chartRow, if_true]
    simp at this
    omega
  refine ⟨hlo, ?_, ?_, ?_, ?_⟩
  · have hcoeff := bulkJBChart_coeff CL0 CL1 TI cs hp N (max_le hN0L hN1L) hNT Xs cols 0 (bulkRL (F.step N) (spl ν)) hlo true Finset.univ
      (fun _ => bulkPk N 0 (bulkRL (F.step N) (spl ν)) true (F.step N) aL bL)
      (fun k : cols => 1 / bulkNorm CL0 (CP.CI0.bulkR ν) (atStep F μ N) (Xs k) N)
      (fun k : cols => 1 / bulkNorm CL1 (CP.CI1.bulkR ν') (atStep F μ N) (Xs k) N)
      (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs) hX hJ1 hJ2 hrows 1 (by show |F.step N| ≤ 1; rw [abs_of_pos hst]; exact hh1) le_rfl le_rfl le_rfl
      (le_max_left _ _)
    have hR1 : ((bulkRL (F.step N) (spl ν) : ℕ) : ℤ) - 1 ≤ ns := by rw [hRL]; omega
    refine ChartOkCoeff.ok (c := bulkLeftChart CP TB spl μ N Xs ν cols hlo) hcoeff
      (blockChartL_host0_eq CP TB spl μ N Xs ν cols hcols _ hlo hR1 _ _)
      (blockChartL_host1_eq CP TB spl μ N Xs ν cols hcols _ hlo hR1 _ _ hp hNT)
      (fun j => (Hhost μ hμ N hsHr ht Xs Um hE j).1)
      (fun j => (Hhost μ hμ N hsHr ht Xs Um hE j).2) ?_ ?_ ?_
    · intro n hτ hn0
      refine HE (atStep F μ N) hp N hN0L hsEr Xs cols 0 (bulkRL (F.step N) (spl ν)) hlo true Finset.univ
        (fun _ => bulkPk N 0 (bulkRL (F.step N) (spl ν)) true (F.step N) aL bL)
        (fun k : cols => 1 / bulkNorm CL0 CR0 (atStep F μ N) (Xs k) N)
        (fun k : cols => 1 / bulkNorm CL1 (CP.CI1.bulkR ν') (atStep F μ N) (Xs k) N)
        (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs) hX ?_ ?_ ?_ ?_ n hτ hn0
      · intro k
        exact (Hσ (atStep F μ N) hp (Xs k) (hX1 k) N (max_le hN1L hN1R) hsσh).1
      · show (0 : ℤ) ≤ chartExtRow N 0 (bulkRL (F.step N) (spl ν)) true
        rw [hext]; omega
      · show CL0.c' ≤ uNode (F.step N) (chartExtRow N 0 (bulkRL (F.step N) (spl ν)) true)
        rw [hext]; exact g4
      · show uNode (F.step N) (chartExtRow N 0 (bulkRL (F.step N) (spl ν)) true) ≤ CL0.c
        rw [hext]; exact g3
    · intro k
      exact HL (atStep F μ N) hp N (max_le hN0L hN0R) hsl1 Xs Um hE' cols 0 (bulkRL (F.step N) (spl ν)) hlo Finset.univ
        (fun k : cols => 1 / bulkNorm CL0 CR0 (atStep F μ N) (Xs k) N)
        (fun k : cols => 1 / bulkNorm CL1 (CP.CI1.bulkR ν') (atStep F μ N) (Xs k) N)
        (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs) hX hcov k
    · intro k
      exact HU (atStep F μ N) hp N (max_le hN0L hN1L) hNT hsu1 Xs cols 0 (bulkRL (F.step N) (spl ν)) hlo true Finset.univ
        (fun k : cols => 1 / bulkNorm CL0 CR0 (atStep F μ N) (Xs k) N)
        (fun k : cols => 1 / bulkNorm CL1 (CP.CI1.bulkR ν') (atStep F μ N) (Xs k) N)
        (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs) hX hX1 hcov' k
  · intro n k
    exact (blockChartL_host0_eq CP TB spl μ N Xs ν cols hcols _ hlo (by rw [hRL]; omega) _ _ n k).symm
  · intro n k
    exact (blockChartL_host1_eq CP TB spl μ N Xs ν cols hcols _ hlo (by rw [hRL]; omega) _ _ hp hNT n k).symm
  · intro i hi
    have hi' : i.val < ns.toNat + 1 := by omega
    refine ⟨⟨i.val, hi'⟩, ?_⟩
    apply Fin.ext
    simp [FormalResearch.JB.Chart.row, bulkLeftChart, blockChartL, bulkJBChart]

theorem bulk_block_right (hs : CP.SplicesInWindow spl) (hm : 1 ≤ m) (ht0 : 0 < t0)
    (hstd0 : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) (m / 2) r)
    (hstd1 : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) ((m + 1) / 2) r)
    (hhost : HostBound K CP.CI0 CP.CI1 spl (CP.spl1 spl)) (ν : Fin CP.CI0.nb) :
    ∃ (cs : OneStepConsts) (N0 : ℕ) (h0 : ℝ), 0 < h0 ∧ h0 ≤ 1 ∧ ∀ μ ∈ K, ∀ N : ℕ, N0 ≤ N → F.step N ≤ h0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
      ∀ cols : Finset (Fin (N + 1)), (∀ k ∈ cols, blockOf CP.CI0 (Xs k) = some ν) →
        ∃ hlo : (nearestRow (F.step N) (spl ν)).toNat + 1 + bulkRR N (F.step N) (spl ν) ≤ N + 1,
          (bulkRightChart CP TB spl μ N Xs ν cols hlo).Ok cs m (F.step N) Um ∧
          (∀ (n) (k : cols), compMatrix CP.CI0 spl μ N Xs ((bulkRightChart CP TB spl μ N Xs ν cols hlo).row n) k =
            (bulkRightChart CP TB spl μ N Xs ν cols hlo).H0 (F.step N) n k) ∧
          (∀ (n) (k : cols), compMatrix CP.CI1 (CP.spl1 spl) μ N Xs ((bulkRightChart CP TB spl μ N Xs ν cols hlo).row n) k =
            (bulkRightChart CP TB spl μ N Xs ν cols hlo).H1 (F.step N) n k) ∧
          (∀ i : Fin (N + 1), nearestRow (F.step N) (spl ν) < ((i : ℕ) : ℤ) →
            ∃ n : Fin (bulkRR N (F.step N) (spl ν)), (bulkRightChart CP TB spl μ N Xs ν cols hlo).row n = i) := by
  obtain ⟨r0, hr0⟩ := hstd0
  obtain ⟨r1, hr1⟩ := hstd1
  obtain ⟨Ch, hHr, hCh0, hHpos, Hhost⟩ := hhost
  set ν' : Fin CP.CI1.nb := Fin.cast CP.nb_eq.symm ν with hν'
  have hcoup0 := CP.CI0.overlap_match ν
  have hcoup1 := CP.CI1.overlap_match ν'
  have hs0 : (CP.CI0.bulkL ν).c' < spl ν ∧ spl ν < (CP.CI0.bulkL ν).c := hs.1 ν
  have hs1 : (CP.CI1.bulkL ν').c' < spl ν ∧ spl ν < (CP.CI1.bulkL ν').c := by
    have := hs.2 ν'
    simpa [ChartPair.spl1, hν'] using this
  have hJ1 : CP.CI0.lo ν = CP.CI1.lo ν' := by rw [CP.lo_eq]; rfl
  have hJ2 : CP.CI0.hi ν = CP.CI1.hi ν' := by rw [CP.hi_eq]; rfl
  obtain ⟨Cσ, hσh, hCσ0, hσpos, Hσ⟩ := bulk_sigma_bound (CP.CI1.bulkL ν') (CP.CI1.bulkR ν') (by omega) hcoup1 r1 hr1
  obtain ⟨CE, hEr, hCE0, hEpos, HE⟩ := bulkJBChart_ext_row (CP.CI0.bulkR ν) (CP.CI1.bulkR ν') (TB.bulkR ν) Cσ hCσ0
  have hr0' := hr0
  obtain ⟨hPc, hEK, -⟩ := hr0'
  obtain ⟨CA, hCA0, hCA⟩ := bondA_bound_of_EK (frozenFamily F Kidx) (paramSet K t0) (m / 2) r0 hPc hEK
  have hCA' : ∀ μ ∈ paramSet K t0, ∀ N : ℕ, ∀ n : ℤ, |(mirrorFamily (frozenFamily F Kidx)).bondA μ N n| ≤ CA := by
    intro μ hμ N n
    rw [bondA_mirror]
    exact hCA μ hμ N _
  set CL0 := CP.CI0.bulkL ν with hCL0
  set CR0 := CP.CI0.bulkR ν with hCR0
  set CL1 := CP.CI1.bulkL ν' with hCL1
  set CR1 := CP.CI1.bulkR ν' with hCR1
  set cmx := bulkWinHi CP ν with hcmx
  have hcmx_s : spl ν < cmx := lt_min hs0.2 hs1.2
  have hcmx0 : cmx ≤ CL0.c := min_le_left _ _
  have hcmx1 : cmx ≤ CL1.c := min_le_right _ _
  set aRg := bulkRga CP spl ν with haRg
  set bRg := bulkRgb CP ν with hbRg
  have haRg' : aRg = (spl ν + cmx) / 2 := rfl
  have hbRg' : bRg = cmx := rfl
  set a : ℝ := F.L - bRg with ha
  set b : ℝ := F.L - aRg with hb
  have hab : a < b := by rw [ha, hb, haRg', hbRg']; linarith
  have hca : CR0.c' ≤ a := by rw [ha, hbRg', hcoup0.2]; linarith
  have hbc : b ≤ CR0.c := by rw [hb, haRg', hcoup0.1]; linarith [hs0.1]
  have hca1 : CR1.c' ≤ a := by rw [ha, hbRg', hcoup1.2]; linarith
  have hbc1 : b ≤ CR1.c := by rw [hb, haRg', hcoup1.1]; linarith [hs1.1]
  obtain ⟨C4, hu1, hC40, hupos, HU⟩ := bulkJBChart_overlap_ub CR0 CR1 (TB.bulkR ν) CA hCA0 hCA' a b hab hca hbc hca1 hbc1
  obtain ⟨c0, hl1, hc0pos, hlpos, HL⟩ := bulkJBChartR_overlap_lb CL0 CR0 CR1 (TB.bulkR ν) hm hcoup0 r0 hr0 a b hab hca hbc
  set TI := TB.bulkR ν with hTI
  obtain ⟨hrect, hcTp, hcαp, hS0, hωp⟩ := TI.consts_pos
  have hc'pos : 0 < CL0.c' := CL0.consts_pos.1
  have hσpos' : 0 < CL0.σ := CL0.consts_pos.2.2.1
  have hcL : CL0.c + CL0.σ < F.L := CL0.consts_pos.2.2.2.1
  obtain ⟨h0, hh0pos, hle⟩ : ∃ h0 : ℝ, 0 < h0 ∧ ∀ x : ℝ, x ≤ h0 → x ≤ 1 ∧ x ≤ t0 ∧ x ≤ hσh ∧ x ≤ hEr ∧ x ≤ hu1 ∧ x ≤ hl1 ∧ x ≤ hHr ∧
      x ≤ CL0.σ ∧ x ≤ 2 * (CL0.c - spl ν) / 3 ∧ x ≤ 2 * (spl ν - CL0.c') ∧ x ≤ (cmx - spl ν) / 2 := by
    refine ⟨min 1 (min t0 (min hσh (min hEr (min hu1 (min hl1 (min hHr (min CL0.σ (min (2 * (CL0.c - spl ν) / 3) (min (2 * (spl ν - CL0.c')) ((cmx - spl ν) / 2)))))))))), ?_, fun x hx => ?_⟩
    · simp only [lt_min_iff]
      refine ⟨one_pos, ht0, hσpos, hEpos, hupos, hlpos, hHpos, hσpos', by linarith [hs0.2], by linarith [hs0.1], by linarith⟩
    · simp only [le_min_iff] at hx
      exact hx
  set cs : OneStepConsts :=
    ⟨0, Ch, max (chartSchurK 0 (CR0.c + CR0.σ / 2) (CP.CI0.lo ν) (CP.CI0.hi ν) TI.S TI.cT TI.cα 1) 0, TI.ωmax, TI.cT, TI.cα, c0, C4, CE,
      hCh0, le_max_right _ _, hωp, hcTp, hcαp, hc0pos, hC40, hCE0⟩ with hcs
  refine ⟨cs, max CL0.N0 (max CR0.N0 (max CL1.N0 (max CR1.N0 TI.N0))), h0, hh0pos, (hle h0 le_rfl).1, ?_⟩
  intro μ hμ N hN hstep Xs Um hE cols hcols
  simp only [max_le_iff] at hN
  obtain ⟨hN0L, hN0R, hN1L, hN1R, hNT⟩ := hN
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hLs : F.step N * ((N : ℝ) + 1) = F.L := step_mul_succ F N
  obtain ⟨hh1, ht, hsσh, hsEr, hsu1, hsl1, hsHr, hsσ, hs2, hs3, hs4⟩ := hle _ hstep
  have hp := atStep_mem hμ N ht
  have hE' := eig_frozen (Kidx := Kidx) hE
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := bulk_geom hst hLs hc'pos hs0.1 hs0.2 hσpos' hcL hsσ hs2 hs3
  set ns := nearestRow (F.step N) (spl ν) with hns
  have hRR : bulkRR N (F.step N) (spl ν) = N - ns.toNat := rfl
  have hlo : ns.toNat + 1 + bulkRR N (F.step N) (spl ν) ≤ N + 1 := by rw [hRR]; omega
  have hX : ∀ k : cols, Xs k ∈ Set.Icc (CP.CI0.lo ν) (CP.CI0.hi ν) := fun k => blockOf_spec CP.CI0 (Xs k) ν (hcols k k.2)
  have hX1 : ∀ k : cols, Xs k ∈ Set.Icc (CP.CI1.lo ν') (CP.CI1.hi ν') := fun k => by rw [← hJ1, ← hJ2]; exact hX k
  have hmir : ∀ n : ℤ, uNode (F.step N) ((N : ℤ) - n) = F.L - uNode (F.step N) n := fun n => uNode_mirror F.L (F.step N) N n hLs
  set lo : ℕ := ns.toNat + 1 with hlodef
  set R : ℕ := bulkRR N (F.step N) (spl ν) with hRdef
  have hlo_int : (lo : ℤ) = ns + 1 := by simp only [hlodef]; omega
  have hlowR : ∀ i : ℤ, aRg ≤ uNode (F.step N) i → ns + 1 ≤ i := by
    intro i hi
    by_contra hcon
    push Not at hcon
    have h1 := (uNode_le_iff hst _ _).mpr (show i ≤ ns by omega)
    rw [haRg'] at hi
    linarith
  have hrow : ∀ n : Fin R, chartRow N lo R false n = (N : ℤ) - ((lo : ℤ) + n.val) := by
    intro n; simp [chartRow]
  have hRn : ∀ n : Fin R, (lo : ℤ) + n.val ≤ N := by
    intro n; have h1 : n.val < N - ns.toNat := n.isLt; simp only [hlodef]; omega
  have hrows : ∀ n : Fin R, 0 ≤ chartRow N lo R false n ∧
      uNode ((mirrorFamily (frozenFamily F Kidx)).step N) (chartRow N lo R false n) ≤ CR0.c := by
    intro n
    rw [hrow n]
    refine ⟨by have := hRn n; omega, ?_⟩
    show uNode (F.step N) ((N : ℤ) - ((lo : ℤ) + n.val)) ≤ CR0.c
    rw [hmir, hcoup0.1]
    have h1 := (uNode_le_iff hst _ _).mpr (show ns + 1 ≤ (lo : ℤ) + n.val by omega)
    linarith
  have hext : chartExtRow N lo R false = (N : ℤ) - ns := by
    simp only [chartExtRow, Bool.false_eq_true, ite_false]; omega
  have hcov : ∀ i ∈ subWin (F.step N) (F.L - b) (F.L - a) N, (lo : ℤ) ≤ i ∧ i < (lo : ℤ) + (R : ℤ) := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hi0 := Finset.mem_Icc.mp hi'.1
    have h1 : F.L - b = aRg := by rw [hb]; ring
    have h2 := hi'.2.1
    rw [h1] at h2
    refine ⟨by rw [hlo_int]; exact hlowR i h2, ?_⟩
    have : (R : ℤ) = N - ns.toNat := by simp only [hRdef, bulkRR]; omega
    omega
  have hcov' : ∀ j ∈ subWin (F.step N) a b N, ∃ n : Fin R, chartRow N lo R false n = j := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have hj0 := Finset.mem_Icc.mp hj'.1
    have h2 : aRg ≤ uNode (F.step N) ((N : ℤ) - j) := by
      rw [hmir j]
      have := hj'.2.2
      rw [hb] at this
      linarith
    have h3 := hlowR _ h2
    have hRz : (R : ℤ) = N - ns.toNat := by simp only [hRdef, bulkRR]; omega
    refine ⟨⟨((N : ℤ) - j - lo).toNat, by omega⟩, ?_⟩
    rw [hrow]
    simp only [hlo_int]
    omega
  refine ⟨hlo, ?_, ?_, ?_, ?_⟩
  · have hcoeff := bulkJBChart_coeff CR0 CR1 TI cs hp N (max_le hN0R hN1R) hNT Xs cols lo R hlo false Finset.univ
      (fun _ => bulkPk N lo R false (F.step N) (F.L - bRg) (F.L - aRg))
      (fun k : cols => bulkKappa CL0 CR0 (atStep F μ N) (Xs k) N / bulkNorm CL0 CR0 (atStep F μ N) (Xs k) N)
      (fun k : cols => bulkKappa CL1 CR1 (atStep F μ N) (Xs k) N / bulkNorm CL1 CR1 (atStep F μ N) (Xs k) N)
      (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs) hX hJ1 hJ2 hrows 1
      (by show |F.step N| ≤ 1; rw [abs_of_pos hst]; exact hh1) le_rfl le_rfl le_rfl (le_max_left _ _)
    refine ChartOkCoeff.ok (c := bulkRightChart CP TB spl μ N Xs ν cols hlo) hcoeff
      (blockChartR_host0_eq CP TB spl μ N Xs ν cols hcols _ _ hlo (by simp only [hlodef]; omega) _ _)
      (blockChartR_host1_eq CP TB spl μ N Xs ν cols hcols _ _ hlo (by simp only [hlodef]; omega) _ _ hp hNT)
      (fun j => (Hhost μ hμ N hsHr ht Xs Um hE j).1)
      (fun j => (Hhost μ hμ N hsHr ht Xs Um hE j).2) ?_ ?_ ?_
    · intro n hτ hn0
      refine HE (atStep F μ N) hp N hN0R hsEr Xs cols lo R hlo false Finset.univ
        (fun _ => bulkPk N lo R false (F.step N) (F.L - bRg) (F.L - aRg))
        (fun k : cols => bulkKappa CL0 CR0 (atStep F μ N) (Xs k) N / bulkNorm CL0 CR0 (atStep F μ N) (Xs k) N)
        (fun k : cols => bulkKappa CL1 CR1 (atStep F μ N) (Xs k) N / bulkNorm CL1 CR1 (atStep F μ N) (Xs k) N)
        (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs) hX ?_ ?_ ?_ ?_ n hτ hn0
      · intro k
        exact (Hσ (atStep F μ N) hp (Xs k) (hX1 k) N (max_le hN1L hN1R) hsσh).2
      · show (0 : ℤ) ≤ chartExtRow N lo R false
        rw [hext]; omega
      · show CR0.c' ≤ uNode (F.step N) (chartExtRow N lo R false)
        rw [hext, hmir, hcoup0.2]; linarith
      · show uNode (F.step N) (chartExtRow N lo R false) ≤ CR0.c
        rw [hext, hmir, hcoup0.1]; linarith
    · intro k
      exact HL (atStep F μ N) hp N (max_le hN0L hN0R) hsl1 Xs Um hE' cols lo R hlo Finset.univ
        (fun k : cols => bulkKappa CL0 CR0 (atStep F μ N) (Xs k) N / bulkNorm CL0 CR0 (atStep F μ N) (Xs k) N)
        (fun k : cols => bulkKappa CL1 CR1 (atStep F μ N) (Xs k) N / bulkNorm CL1 CR1 (atStep F μ N) (Xs k) N)
        (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs) hX hcov k
    · intro k
      exact HU (atStep F μ N) hp N (max_le hN0R hN1R) hNT hsu1 Xs cols lo R hlo false Finset.univ
        (fun k : cols => bulkKappa CL0 CR0 (atStep F μ N) (Xs k) N / bulkNorm CL0 CR0 (atStep F μ N) (Xs k) N)
        (fun k : cols => bulkKappa CL1 CR1 (atStep F μ N) (Xs k) N / bulkNorm CL1 CR1 (atStep F μ N) (Xs k) N)
        (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs) hX hX1 hcov' k
  · intro n k
    exact (blockChartR_host0_eq CP TB spl μ N Xs ν cols hcols _ _ hlo (by simp only [hlodef]; omega) _ _ n k).symm
  · intro n k
    exact (blockChartR_host1_eq CP TB spl μ N Xs ν cols hcols _ _ hlo (by simp only [hlodef]; omega) _ _ hp hNT n k).symm
  · intro i hi
    have hRz : (R : ℤ) = N - ns.toNat := by simp only [hRdef, bulkRR]; omega
    have hi2 : i.val - lo < R := by have := i.isLt; omega
    refine ⟨⟨i.val - lo, hi2⟩, ?_⟩
    apply Fin.ext
    have : lo ≤ i.val := by simp only [hlodef]; omega
    simp [FormalResearch.JB.Chart.row, bulkRightChart, blockChartR, bulkJBChart]
    omega

include TB in
/-- **The bulk block as a `ThbBlock`** (both charts of the block `nu`, uniform constants): the entries outside the used rows are bounded trivially (`C_eps = 0`: there are none, the two charts cover all rows). -/
theorem bulk_block (hs : CP.SplicesInWindow spl) (hm : 1 ≤ m) (ht0 : 0 < t0)
    (hstd0 : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) (m / 2) r)
    (hstd1 : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) ((m + 1) / 2) r)
    (hhost : HostBound K CP.CI0 CP.CI1 spl (CP.spl1 spl)) (ν : Fin CP.CI0.nb) :
    ∃ (cs : OneStepConsts) (N0 : ℕ) (h0 : ℝ), 0 < h0 ∧ h0 ≤ 1 ∧ ∀ μ ∈ K, ∀ N : ℕ, N0 ≤ N → F.step N ≤ h0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
      ∀ cols : Finset (Fin (N + 1)), (∀ k ∈ cols, blockOf CP.CI0 (Xs k) = some ν) →
        Nonempty (ThbBlock cs N m (F.step N) Um (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs) cols 0 1) := by
  obtain ⟨csL, NL, hL, hL0, hL1, HL⟩ := bulk_block_left CP TB spl hs hm ht0 hstd0 hstd1 hhost ν
  obtain ⟨csR, NR, hR, hR0, hR1, HR⟩ := bulk_block_right CP TB spl hs hm ht0 hstd0 hstd1 hhost ν
  obtain ⟨cs, hcs⟩ := exists_consts_join (ι := Bool) (fun b => if b then csL else csR)
  refine ⟨cs, max NL NR, min hL hR, lt_min hL0 hR0, (min_le_left _ _).trans hL1, ?_⟩
  intro μ hμ N hN hst Xs Um hE cols hcols
  have hst1 : F.step N ≤ hL := hst.trans (min_le_left _ _)
  have hst2 : F.step N ≤ hR := hst.trans (min_le_right _ _)
  have hh0 : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hh1 : F.step N ≤ 1 := hst.trans ((min_le_left _ _).trans hL1)
  obtain ⟨hloL, okL, m0L, m1L, covL⟩ := HL μ hμ N ((le_max_left _ _).trans hN) hst1 Xs Um hE cols hcols
  obtain ⟨hloR, okR, m0R, m1R, covR⟩ := HR μ hμ N ((le_max_right _ _).trans hN) hst2 Xs Um hE cols hcols
  refine ⟨{
    RL := bulkRL (F.step N) (spl ν)
    RR := bulkRR N (F.step N) (spl ν)
    chL := bulkLeftChart CP TB spl μ N Xs ν cols hloL
    chR := bulkRightChart CP TB spl μ N Xs ν cols hloR
    okL := okL.mono (by simpa using hcs true) hh0 hh1
    okR := okR.mono (by simpa using hcs false) hh0 hh1
    match0L := fun n _ k => m0L n k
    match0R := fun n _ k => m0R n k
    match1L := fun n _ k => m1L n k
    match1R := fun n _ k => m1R n k
    cover := ?_ }⟩
  intro k hk i hi1 hi2
  exfalso
  by_cases hle : ((i : ℕ) : ℤ) ≤ nearestRow (F.step N) (spl ν)
  · obtain ⟨n, hn⟩ := covL i hle
    exact hi1 ⟨n, Finset.mem_univ _, hn⟩
  · obtain ⟨n, hn⟩ := covR i (by omega)
    exact hi2 ⟨n, Finset.mem_univ _, hn⟩

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulk_block_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulk_block_left

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulk_block_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulk_block_right

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulk_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulk_block

end Bulk

end FormalResearch.JacobiEigenvectors.TheoremB

end
