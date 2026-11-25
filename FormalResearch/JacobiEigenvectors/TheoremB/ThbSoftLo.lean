module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbSoftUp
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbGauge
public import FormalResearch.JacobiEigenvectors.TheoremB.NegColumns

/-!
# Paper J, Theorem B, L3.5c, part 16: the lower soft block (`SoftBlockLo`)

Source: Paper J `app_thmB.tex`, proof of `prop:thb-inputs` (I1): "a column in `Sigma^-` is `D_-` times such a vector for `-D_- J_h D_-`, and `D_- Psi_k` is the eigenvector of `-D_- J_h D_-` in the gauge `(.)_0 > 0`".

## Proved here

* **`softBlockLo_proved : SoftBlockLo CP TB spl`** (the frozen statement of `ThbInputs.lean`): the upper-edge soft block (`soft_block_gen`) for the chart family `negFamily (frozenFamily F Kidx)` (`softLoL, softLoR`, `mirror_lo`, `soft_lo_eq`, `TB.softLoL`, `TB.softLoR`,
  `stdAssump_neg`), applied to the eigen-system `(negX X, negU U)` (`IsEigenSystem.neg_frozen`) and the matrices `G' = D G R` (`D = diag((-1)^i)`, `R` the column reversal), then transported back by `ThbBlock.gauge`.  The columns of the lower block are those
  with `blockOf = none`, `not (Jhi < X)`, i.e. `X < Jlo` (`cover_bulk`), whose window `|-X - bandHi(neg)| <= delta_0` follows from `cover` (`Jlo - delta_0 < bandLo`) and `stepZero`.

## Differences from the paper

The gauge is applied to the blocks (`ThbBlock.gauge`: signed charts) instead of to the sampled energies.  **Not formalised**: nothing.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine FormalResearch.JB

open scoped Classical

section Lo

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **The entries of `compMatrix` on a lower soft column** (`blockOf = none`, `not (Jhi < X)`), in the gauge frame: `(-1)^i` times the entry is the upper-edge entry of `softLoL, softLoR` at `-X`. -/
theorem compMatrix_softLo_entry (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (spl : Fin CI.nb → ℝ) (μ : Par) (N : ℕ)
    (Xs : Fin (N + 1) → ℝ) (k : Fin (N + 1)) (hk1 : ¬ ∃ ν : Fin CI.nb, CI.lo ν ≤ Xs k ∧ Xs k ≤ CI.hi ν) (hk2 : ¬ CI.Jhi < Xs k) (i : Fin (N + 1)) :
    gsg i.val * compMatrix CI spl μ N Xs i k =
      if ((i : ℕ) : ℤ) ≤ nearestRow (F.step N) (CI.softLoL.uc (atStep F μ N)) then
        CI.softLoL.psiHatL (atStep F μ N) (-Xs k) N i / softNorm CI.softLoL CI.softLoR (atStep F μ N) (-Xs k) N
      else softKappa CI.softLoL CI.softLoR (atStep F μ N) (-Xs k) N *
        CI.softLoR.psiHatL (atStep F μ N) (-Xs k) N ((N : ℤ) - ((i : ℕ) : ℤ)) / softNorm CI.softLoL CI.softLoR (atStep F μ N) (-Xs k) N := by
  have h1 : compMatrix CI spl μ N Xs i k = (-1 : ℝ) ^ ((i : ℕ) : ℤ) *
      softColAt CI.softLoL CI.softLoR (atStep F μ N) (-Xs k) N (nearestRow (F.step N) (CI.softLoL.uc (atStep F μ N))) ((i : ℕ) : ℤ) := by
    simp only [compMatrix, Matrix.of_apply]
    exact compColumn_lower CI spl μ N (Xs k) hk1 hk2 _
  rw [h1, ← mul_assoc]
  have h2 : gsg i.val * (-1 : ℝ) ^ ((i : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast]; exact gsg_sq _
  rw [h2, one_mul]
  unfold softColAt glueVecAt
  split_ifs <;> rfl

theorem softBlockLo_proved (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) : SoftBlockLo CP TB spl := by
  intro hm hq ht0 hstd hhost
  obtain ⟨r, hr0⟩ := hstd
  obtain ⟨Ch, hH0, hCh0, hHpos, Hhost⟩ := hhost
  have hrq : StdAssump (frozenFamily F Kidx) (paramSet K t0) (q / 2) r := by
    have : q / 2 = Kidx := by omega
    rw [this]; exact hr0
  have hrn : StdAssump (negFamily (frozenFamily F Kidx)) (paramSet K t0) (q / 2) r := stdAssump_neg hrq
  obtain ⟨hUc, hUδ, hUη, hUz, hUmu⟩ := CP.soft_lo_eq
  obtain ⟨cs, Cε, cε, N0, h0, hCε, hcε, hh0, hh01, H⟩ := soft_block_gen CP.CI0.pc CP.CI0.softLoL CP.CI0.softLoR CP.CI1.softLoL CP.CI1.softLoR
    CP.CI0.mirror_lo CP.CI1.mirror_lo hUz hUmu hUc hUδ hUη hm r hrn TB.softLoL TB.softLoR Ch hCh0
  obtain ⟨Cs, hs0, hs0p, hsp⟩ := stepZero (frozenFamily F Kidx) (paramSet K t0) (q / 2) r hrq
  have hδpos : 0 < CP.CI0.softLoL.δ0 := CP.CI0.softLoL.consts_pos.1
  have hM : 0 < |Cs| + 1 := by positivity
  refine ⟨cs, Cε, cε, N0, min (min h0 hH0) (min t0 (min hs0 (CP.CI0.softLoL.δ0 / (|Cs| + 1)))), hCε, hcε,
    lt_min (lt_min hh0 hHpos) (lt_min ht0 (lt_min hs0p (div_pos hδpos hM))),
    (min_le_left _ _).trans ((min_le_left _ _).trans hh01), ?_⟩
  intro μ hμ N hN hst Xs Um hE cols hcols
  have hst1 : F.step N ≤ h0 := hst.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hst2 : F.step N ≤ hH0 := hst.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hst3 : F.step N ≤ t0 := hst.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hst4 : F.step N ≤ hs0 := hst.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hst5 : F.step N ≤ CP.CI0.softLoL.δ0 / (|Cs| + 1) :=
    hst.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hp := atStep_mem hμ N hst3
  have hEf := eig_frozen (Kidx := Kidx) hE
  have hEn : IsEigenSystem ((negFamily (frozenFamily F Kidx)).jacobiMat (atStep F μ N) N) (negX Xs) (negU Um) :=
    IsEigenSystem.neg_frozen hE
  have h1 : F.step N ≤ 1 := hst1.trans hh01
  have hsm : Cs * F.step N ^ 2 ≤ CP.CI0.softLoL.δ0 := by
    have e1 : Cs * F.step N ^ 2 ≤ |Cs| * F.step N := by
      calc Cs * F.step N ^ 2 ≤ |Cs| * F.step N ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
        _ ≤ |Cs| * F.step N := mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
    have e2 : |Cs| * F.step N ≤ |Cs| * (CP.CI0.softLoL.δ0 / (|Cs| + 1)) := mul_le_mul_of_nonneg_left hst5 (abs_nonneg _)
    have e3 : |Cs| * (CP.CI0.softLoL.δ0 / (|Cs| + 1)) ≤ CP.CI0.softLoL.δ0 := by
      rw [← mul_div_assoc, div_le_iff₀ hM]
      nlinarith [mul_nonneg hδpos.le (abs_nonneg Cs)]
    linarith
  have hcolsJ : ∀ k ∈ cols, Xs k < CP.CI0.Jlo := by
    intro k hk
    by_contra hcon
    push Not at hcon
    obtain ⟨ν, hν1, hν2, -⟩ := CP.CI0.cover_bulk (Xs k) hcon (not_lt.mp (hcols k hk).2)
    exact blockOf_none CP.CI0 (hcols k hk).1 ν ⟨hν1, hν2⟩
  have hmem : ∀ k : Fin (N + 1), Fin.rev k ∈ cols.image Fin.rev ↔ k ∈ cols := fun k => by
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, hax⟩
      have : a = k := Fin.rev_injective hax
      rw [this] at ha; exact ha
    · intro hk; exact ⟨k, hk, rfl⟩
  have hwin : ∀ k' ∈ cols.image Fin.rev, |negX Xs k' - (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N)| ≤ CP.CI0.softLoL.δ0 := by
    intro k' hk'
    have hk : Fin.rev k' ∈ cols := by
      obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hk'
      rw [← hax, Fin.rev_rev]; exact ha
    have hlow : (frozenFamily F Kidx).bandLo (atStep F μ N) - Cs * F.step N ^ 2 ≤ Xs (Fin.rev k') :=
      (hsp _ hp N hst4 Xs Um hEf (Fin.rev k')).1
    have hcov := (CP.CI0.cover _ hp).2.2.2.2
    have hJ := hcolsJ _ hk
    rw [negFrozen_bandHi]
    show |-Xs (Fin.rev k') - -(frozenFamily F Kidx).bandLo (atStep F μ N)| ≤ _
    rw [abs_le]
    constructor <;> linarith
  have hbl : ∀ k ∈ cols, ¬ ∃ ν : Fin CP.CI1.nb, CP.CI1.lo ν ≤ Xs k ∧ Xs k ≤ CP.CI1.hi ν := fun k hk ⟨ν, h1, h2⟩ =>
    blockOf_none CP.CI0 (hcols k hk).1 (Fin.cast CP.nb_eq ν) ⟨by rw [← CP.lo_eq]; exact h1, by rw [← CP.hi_eq]; exact h2⟩
  have hJ1 : ∀ k ∈ cols, ¬ CP.CI1.Jhi < Xs k := fun k hk => by rw [CP.J_eq.2]; exact (hcols k hk).2
  set G0' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := Matrix.of fun i k' => gsg i.val * compMatrix CP.CI0 spl μ N Xs i (Fin.rev k') with hG0'
  set G1' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := Matrix.of fun i k' => gsg i.val * compMatrix CP.CI1 (CP.spl1 spl) μ N Xs i (Fin.rev k') with hG1'
  have hf0 : ∀ k' ∈ cols.image Fin.rev, ∀ i : Fin (N + 1), G0' i k' =
      if ((i : ℕ) : ℤ) ≤ nearestRow (F.step N) (CP.CI0.softLoL.uc (atStep F μ N)) then
        CP.CI0.softLoL.psiHatL (atStep F μ N) (negX Xs k') N ((i : ℕ) : ℤ) / softNorm CP.CI0.softLoL CP.CI0.softLoR (atStep F μ N) (negX Xs k') N
      else softKappa CP.CI0.softLoL CP.CI0.softLoR (atStep F μ N) (negX Xs k') N *
        CP.CI0.softLoR.psiHatL (atStep F μ N) (negX Xs k') N ((N : ℤ) - ((i : ℕ) : ℤ)) / softNorm CP.CI0.softLoL CP.CI0.softLoR (atStep F μ N) (negX Xs k') N := by
    intro k' hk' i
    have hk : Fin.rev k' ∈ cols := (hmem _).mp (by simpa using hk')
    have := compMatrix_softLo_entry CP.CI0 spl μ N Xs (Fin.rev k') (fun ⟨ν, h⟩ => blockOf_none CP.CI0 (hcols _ hk).1 ν h) (hcols _ hk).2 i
    simp only [hG0', Matrix.of_apply]
    rw [this]
    rfl
  have hf1 : ∀ k' ∈ cols.image Fin.rev, ∀ i : Fin (N + 1), G1' i k' =
      if ((i : ℕ) : ℤ) ≤ nearestRow (F.step N) (CP.CI1.softLoL.uc (atStep F μ N)) then
        CP.CI1.softLoL.psiHatL (atStep F μ N) (negX Xs k') N ((i : ℕ) : ℤ) / softNorm CP.CI1.softLoL CP.CI1.softLoR (atStep F μ N) (negX Xs k') N
      else softKappa CP.CI1.softLoL CP.CI1.softLoR (atStep F μ N) (negX Xs k') N *
        CP.CI1.softLoR.psiHatL (atStep F μ N) (negX Xs k') N ((N : ℤ) - ((i : ℕ) : ℤ)) / softNorm CP.CI1.softLoL CP.CI1.softLoR (atStep F μ N) (negX Xs k') N := by
    intro k' hk' i
    have hk : Fin.rev k' ∈ cols := (hmem _).mp (by simpa using hk')
    have := compMatrix_softLo_entry CP.CI1 (CP.spl1 spl) μ N Xs (Fin.rev k') (hbl _ hk) (hJ1 _ hk) i
    simp only [hG1', Matrix.of_apply]
    rw [this]
    rfl
  have hc0 : ∀ j' : Fin (N + 1), jbL2 Finset.univ (fun i => G0' i j' - negU Um i j') ≤ Ch * F.step N ^ m := by
    intro j'
    have h2 := (Hhost μ hμ N hst2 hst3 Xs Um hE (Fin.rev j')).1
    refine le_of_eq_of_le ?_ h2
    have : (fun i => G0' i j' - negU Um i j') = fun i => gsg i.val * (compMatrix CP.CI0 spl μ N Xs i (Fin.rev j') - Um i (Fin.rev j')) := by
      funext i
      simp only [hG0', negU, Matrix.of_apply]
      ring
    rw [this]
    exact jbL2_gsg _ _ _ (fun i => gsg_sq _)
  have hc1 : ∀ j' : Fin (N + 1), jbL2 Finset.univ (fun i => G1' i j' - negU Um i j') ≤ Ch * F.step N ^ (m + 1) * Real.log (1 / F.step N) := by
    intro j'
    have h2 := (Hhost μ hμ N hst2 hst3 Xs Um hE (Fin.rev j')).2
    refine le_of_eq_of_le ?_ h2
    have : (fun i => G1' i j' - negU Um i j') = fun i => gsg i.val * (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs i (Fin.rev j') - Um i (Fin.rev j')) := by
      funext i
      simp only [hG1', negU, Matrix.of_apply]
      ring
    rw [this]
    exact jbL2_gsg _ _ _ (fun i => gsg_sq _)
  obtain ⟨B⟩ := H (atStep F μ N) hp N hN hst1 (negX Xs) (negU Um) hEn (cols.image Fin.rev) hwin G0' G1' hf0 hf1 hc0 hc1
  refine ⟨ThbBlock.gauge (cols := cols) (cols' := cols.image Fin.rev) (fun k => (hmem k).symm) (fun i k => negU_rev Um i k)
    (fun i k => ?_) (fun i k => ?_) B⟩
  · simp only [hG0', Matrix.of_apply, Fin.rev_rev]
  · simp only [hG1', Matrix.of_apply, Fin.rev_rev]

end Lo

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.softBlockLo_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.softBlockLo_proved

end FormalResearch.JacobiEigenvectors.TheoremB

end
