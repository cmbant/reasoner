module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbBulk
public import FormalResearch.JacobiEigenvectors.TheoremB.TwoOrdersSoft
public import FormalResearch.JacobiEigenvectors.TheoremB.ThmBProof

/-!
# Paper J, Theorem B, L3.5c, part 7: assembly of `PropThbInputs` from the blocks

Source: Paper J `app_thmB.tex`, proof of `prop:thb-inputs`: (S1) the blocks, the charts of each block, (I1)--(I5), and the uniformity of the constants.

## Proved here

* `thbBlock_eq_up_iff`, `thbBlock_eq_lo_iff`: the column sets of the two soft blocks (`blockOf = none`, above / not above `Jhi`).
* `SoftBlockUp`, `SoftBlockLo`: **the statements of the two soft blocks** (the soft analogue of `bulk_block`): for the columns of the upper (lower) soft edge, a `ThbBlock` with uniform constants, under `1 <= m`, `q = 2 Kidx`,
  the standing assumptions at `Kidx` and the host bound.
* **`propThbInputs_of_soft`: `PropThbInputs CP TB spl` from `SoftBlockUp`, `SoftBlockLo` (for every restriction `t0' <= t0` of the chart data)**.  Everything else is proved: the bulk blocks (`bulk_block`, with the host bound from `propThaSpliceTwoOrders_proved`
  and `hostCols_of_twoOrders`), the F-t0 restriction (`ChartPair.restrict`, `TransferBundle.restrict`, `stdAssump_frozen_all`), the uniform constants (`exists_uniform_blocks`), the assembly (`oneStepInputs_of_blocks`), `U_orth` (`IsEigenSystem.orth`), and `G1_col`
  (from the host bound, constant `C` enlarged).
* `thmB_of_soft`: `ThmB CP spl` from the same premises (`thmB_of_propThbInputs`).

## Differences from the paper

`N_0` replaces `h <= h_0` (F-B3).  The two soft blocks are stated here (`SoftBlockUp`, `SoftBlockLo`) and proved in `ThbSoftUp.lean` (`softBlockUp_proved`) and `ThbSoftLo.lean` (`softBlockLo_proved`); `ThbFinal.lean` discharges the premises of
`propThbInputs_of_soft` and `thmB_of_soft` (`propThbInputs_proved`, `thmB_proved`).

## Not formalised

Nothing in this module beyond its statements (the soft blocks are proved in `ThbSoftUp.lean`, `ThbSoftLo.lean`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JB

open scoped Classical

section Cols

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

theorem thbBlock_eq_up_iff (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (X : ℝ) :
    thbBlock CI X = ⟨CI.nb, by omega⟩ ↔ blockOf CI X = none ∧ CI.Jhi < X := by
  unfold thbBlock
  cases hb : blockOf CI X with
  | some ν =>
    have := ν.isLt
    simp [Fin.ext_iff]
    omega
  | none =>
    by_cases hX : CI.Jhi < X <;> simp [hX, Fin.ext_iff]

theorem thbBlock_eq_lo_iff (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (X : ℝ) :
    thbBlock CI X = ⟨CI.nb + 1, by omega⟩ ↔ blockOf CI X = none ∧ ¬ CI.Jhi < X := by
  unfold thbBlock
  cases hb : blockOf CI X with
  | some ν =>
    have := ν.isLt
    simp [Fin.ext_iff]
    omega
  | none =>
    by_cases hX : CI.Jhi < X <;> simp [hX, Fin.ext_iff]

variable (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))

/-- **The upper soft block** (statement; the analogue of `bulk_block` for the columns of the upper soft edge, `blockOf = none`, `Jhi < X`): uniform constants and a `ThbBlock` with the exterior bound `C_eps e^{-c_eps/h}`. -/
def SoftBlockUp (_TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) : Prop :=
  1 ≤ m → q = 2 * Kidx → 0 < t0 → (∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) Kidx r) →
    HostBound K CP.CI0 CP.CI1 spl (CP.spl1 spl) →
    ∃ (cs : OneStepConsts) (Cε cε : ℝ) (N0 : ℕ) (h0 : ℝ), 0 ≤ Cε ∧ 0 < cε ∧ 0 < h0 ∧ h0 ≤ 1 ∧
      ∀ μ ∈ K, ∀ N : ℕ, N0 ≤ N → F.step N ≤ h0 →
        ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
          ∀ cols : Finset (Fin (N + 1)), (∀ k ∈ cols, blockOf CP.CI0 (Xs k) = none ∧ CP.CI0.Jhi < Xs k) →
            Nonempty (ThbBlock cs N m (F.step N) Um (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs) cols Cε cε)

/-- **The lower soft block** (statement; columns with `blockOf = none`, `not (Jhi < X)`). -/
def SoftBlockLo (_TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) : Prop :=
  1 ≤ m → q = 2 * Kidx → 0 < t0 → (∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) Kidx r) →
    HostBound K CP.CI0 CP.CI1 spl (CP.spl1 spl) →
    ∃ (cs : OneStepConsts) (Cε cε : ℝ) (N0 : ℕ) (h0 : ℝ), 0 ≤ Cε ∧ 0 < cε ∧ 0 < h0 ∧ h0 ≤ 1 ∧
      ∀ μ ∈ K, ∀ N : ℕ, N0 ≤ N → F.step N ≤ h0 →
        ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
          ∀ cols : Finset (Fin (N + 1)), (∀ k ∈ cols, blockOf CP.CI0 (Xs k) = none ∧ ¬ CP.CI0.Jhi < Xs k) →
            Nonempty (ThbBlock cs N m (F.step N) Um (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs) cols Cε cε)

end Cols

section Main

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
  (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
  (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ)

/-- **`PropThbInputs` from the two soft blocks** (the soft blocks for every restriction of the chart data to `t0' <= t0`; see the module docstring). -/
theorem propThbInputs_of_soft
    (hUp : ∀ {t0' : ℝ} (h : t0' ≤ t0), SoftBlockUp (CP.restrict h) (TB.restrict h) spl)
    (hLo : ∀ {t0' : ℝ} (h : t0' ≤ t0), SoftBlockLo (CP.restrict h) (TB.restrict h) spl) :
    PropThbInputs CP TB spl := by
  intro hm hK hq hKc hH hDM hs
  obtain ⟨t1, ht1, r, hr⟩ := stdAssump_frozen_all_of_stdDM F K Kidx hKc hH hDM
  by_cases ht0 : 0 < t0
  swap
  · refine ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, le_rfl, le_rfl, one_pos, one_pos, one_pos, one_pos, le_rfl, le_rfl⟩, 0, 0, 1, one_pos, ?_⟩
    intro μ hμ N _ hNt
    have := FormalResearch.JB.stepSize_pos F.L_pos N
    exact absurd (this.trans_le hNt) ht0
  have ht' : 0 < min t0 t1 := lt_min ht0 ht1
  have hle : min t0 t1 ≤ t0 := min_le_left _ _
  set CP' := CP.restrict hle with hCP'
  set TB' := TB.restrict hle with hTB'
  have hs' : CP'.SplicesInWindow spl := CP.restrict_splicesInWindow hle spl hs
  have hstdK : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K (min t0 t1)) Kidx r := ⟨r, hr _ ht' (min_le_right _ _) Kidx le_rfl⟩
  have hstd0 : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K (min t0 t1)) (m / 2) r :=
    ⟨r, hr _ ht' (min_le_right _ _) (m / 2) (by omega)⟩
  have hstd1 : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K (min t0 t1)) ((m + 1) / 2) r :=
    ⟨r, hr _ ht' (min_le_right _ _) ((m + 1) / 2) (by omega)⟩
  obtain ⟨Ch, hh0, hCh0, hhpos, Hhost⟩ := hostCols_of_twoOrders CP' spl (propThaSpliceTwoOrders_proved CP' spl) hm hK hq hKc hH hDM hs'
  have hhost : HostBound K CP'.CI0 CP'.CI1 spl (CP'.spl1 spl) := ⟨Ch, hh0, hCh0, hhpos, Hhost⟩
  have hUp' := hUp hle hm hq ht' hstdK hhost
  have hLo' := hLo hle hm hq ht' hstdK hhost
  -- uniform blocks over the index set `Fin (nb + 2)`
  have hblocks : ∀ i : Fin (CP.CI0.nb + 2), ∃ (cs : OneStepConsts) (Cε cε : ℝ) (N0 : ℕ) (h0 : ℝ), 0 ≤ Cε ∧ 0 < cε ∧ 0 < h0 ∧ h0 ≤ 1 ∧
      ∀ μ ∈ K, ∀ N : ℕ, N0 ≤ N → F.step N ≤ h0 → ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        IsEigenSystem (F.jacobiMat μ N) Xs Um →
        Nonempty (ThbBlock cs N m (F.step N) Um (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs)
          (thbCols CP.CI0 Xs i) Cε cε) := by
    intro i
    by_cases hb : i.val < CP.CI0.nb
    · obtain ⟨cs, N0, h0, hh0p, hh01, H⟩ := bulk_block CP' TB' spl hs' hm ht' hstd0 hstd1 hhost ⟨i.val, hb⟩
      refine ⟨cs, 0, 1, N0, h0, le_rfl, one_pos, hh0p, hh01, fun μ hμ N hN hst Xs Um hE => ?_⟩
      refine H μ hμ N hN hst Xs Um hE _ (fun k hk => ?_)
      rw [mem_thbCols_iff] at hk
      have := (thbBlock_eq_bulk_iff CP.CI0 (Xs k) ⟨i.val, hb⟩).mp (by rw [hk])
      exact this
    · by_cases hb1 : i.val = CP.CI0.nb
      · obtain ⟨cs, Cε, cε, N0, h0, hC, hc, hh0p, hh01, H⟩ := hUp'
        refine ⟨cs, Cε, cε, N0, h0, hC, hc, hh0p, hh01, fun μ hμ N hN hst Xs Um hE => ?_⟩
        refine H μ hμ N hN hst Xs Um hE _ (fun k hk => ?_)
        rw [mem_thbCols_iff] at hk
        have hi : i = ⟨CP.CI0.nb, by omega⟩ := Fin.ext hb1
        rw [hi] at hk
        exact (thbBlock_eq_up_iff CP.CI0 (Xs k)).mp hk
      · have hb2 : i.val = CP.CI0.nb + 1 := by have := i.isLt; omega
        obtain ⟨cs, Cε, cε, N0, h0, hC, hc, hh0p, hh01, H⟩ := hLo'
        refine ⟨cs, Cε, cε, N0, h0, hC, hc, hh0p, hh01, fun μ hμ N hN hst Xs Um hE => ?_⟩
        refine H μ hμ N hN hst Xs Um hE _ (fun k hk => ?_)
        rw [mem_thbCols_iff] at hk
        have hi : i = ⟨CP.CI0.nb + 1, by omega⟩ := Fin.ext hb2
        rw [hi] at hk
        exact (thbBlock_eq_lo_iff CP.CI0 (Xs k)).mp hk
  obtain ⟨csJ, Cε, cε, N0, h0, hC0, hc0, hh0p, hh01, HJ⟩ := exists_uniform_blocks (ι := Fin (CP.CI0.nb + 2)) K F.step m
    (fun μ N Xs Um => IsEigenSystem (F.jacobiMat μ N) Xs Um)
    (fun μ N Xs => compMatrix CP.CI0 spl μ N Xs) (fun μ N Xs => compMatrix CP.CI1 (CP.spl1 spl) μ N Xs)
    (fun i N Xs => thbCols CP.CI0 Xs i) hblocks (fun N => FormalResearch.JB.stepSize_pos F.L_pos N)
  -- final constants
  set cs : OneStepConsts := { csJ with nb := CP.CI0.nb + 2, C := max csJ.C Ch, C_nonneg := le_max_of_le_left csJ.C_nonneg } with hcs
  have hcle : csJ.Le cs := ⟨le_max_left _ _, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  obtain ⟨N1, hN1⟩ := exists_N_step_le F (lt_min (lt_min hh0p ht') hhpos)
  refine ⟨cs, max N0 N1, Cε, cε, hc0, ?_⟩
  intro μ hμ N hN hNt Xs Um hE
  have hN0 : N0 ≤ N := (le_max_left _ _).trans hN
  have hstN : F.step N ≤ min (min h0 (min t0 t1)) hh0 := hN1 N ((le_max_right _ _).trans hN)
  have hsh : F.step N ≤ h0 := (hstN.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hsm : F.step N ≤ min t0 t1 := (hstN.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hsH : F.step N ≤ hh0 := hstN.trans (min_le_right _ _)
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hB : ∀ i : Fin (CP.CI0.nb + 2), ThbBlock cs N m (F.step N) Um (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs)
      (thbCols CP.CI0 Xs i) Cε cε := by
    intro i
    exact (Classical.choice (HJ i μ hμ N hN0 hsh Xs Um hE)).mono hcle hst (hsh.trans hh01) hC0 le_rfl le_rfl
  have hG1 : ∀ j : Fin (N + 1), jbL2 Finset.univ (fun i => compMatrix CP.CI1 (CP.spl1 spl) μ N Xs i j - Um i j) ≤
      cs.C * F.step N ^ (m + 1) * Real.log (1 / F.step N) := by
    intro j
    have h := (Hhost μ hμ N hsH hsm Xs Um hE j).2
    have hl : 0 ≤ F.step N ^ (m + 1) * Real.log (1 / F.step N) := by
      refine mul_nonneg (pow_nonneg hst.le _) (Real.log_nonneg ?_)
      rw [le_div_iff₀ hst]
      linarith [hsh.trans hh01]
    refine h.trans ?_
    calc Ch * F.step N ^ (m + 1) * Real.log (1 / F.step N) = Ch * (F.step N ^ (m + 1) * Real.log (1 / F.step N)) := by ring
      _ ≤ cs.C * (F.step N ^ (m + 1) * Real.log (1 / F.step N)) := mul_le_mul_of_nonneg_right (le_max_right _ _) hl
      _ = _ := by ring
  refine ⟨oneStepInputs_of_blocks cs Um (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs)
    (thbCols CP.CI0 Xs) (fun ν ν' h => thbCols_disjoint CP.CI0 Xs ν ν' h) (exists_mem_thbCols CP.CI0 Xs) Cε cε hC0 hB hst hm hE.orth hG1,
    rfl, rfl, rfl, le_rfl⟩

/-- **Theorem B from the two soft blocks.** -/
theorem thmB_of_soft
    (hUp : ∀ {t0' : ℝ} (h : t0' ≤ t0), SoftBlockUp (CP.restrict h) (TB.restrict h) spl)
    (hLo : ∀ {t0' : ℝ} (h : t0' ≤ t0), SoftBlockLo (CP.restrict h) (TB.restrict h) spl) : ThmB CP spl :=
  thmB_of_propThbInputs CP TB spl (propThbInputs_of_soft CP TB spl hUp hLo)

end Main

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.propThbInputs_of_soft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.propThbInputs_of_soft

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thmB_of_soft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thmB_of_soft


end FormalResearch.JacobiEigenvectors.TheoremB

end
