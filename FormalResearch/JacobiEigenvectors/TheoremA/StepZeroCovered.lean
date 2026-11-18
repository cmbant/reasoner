module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZero

/-!
# Paper J, Layer 2: the three cases exhaust the spectrum (`SpectrumCovered`)

Source: Paper J `thmA.tex`, proof of thm:A (ii) ("Step 0 ... so the three cases exhaust `0 <= k <= N`"); plan item L2.C8.  Frozen statement: `SpectrumCovered` of `TheoremA/EigenvalueStatements.lean` (unchanged).

## Proved

* `spectrumCovered : SpectrumCovered CI` for every `CI : ChartInputs F K Kidx t0 m q U V cPC CPC`.
* `fPlus_close`, `Xsp_le_add`, `bddAbove_fPlus`, `frozen_bandHi`, `frozen_bandLo`: the frozen band at `t = h` is `O(h)` from the plain band, in the one-sided form used.

Chain: `eigen_loc` with `e = 1` (the `O(h)` location of the eigenvalues, from `(D_{2 Kidx+1})`; `coreReg_of_DM`) gives `X_k in [bandLo - C h, bandHi + C h]`; `fPlus_close` (for
`G_0 + h G_1`, `B_0 + h B_1`, `h` small: the factor `s (L-s)` cancels in the square root) and `Xsp_le_add` give `bandHi <= bandHi^{frozen}(mu,h) + c h`, `bandLo^{frozen}(mu,h) <= bandLo + c h`;
the chart field `CI.cover` (`bandHi^{frozen} <= Jhi + delta_0`, `Jlo - delta_0 <= bandLo^{frozen}`, `Jlo <= Jhi`) and `CI.cover_bulk` then place every `X_k` in a block, or above `Jhi`
within the upper window, or below `Jlo` within the lower window (`negFamily_bandHi`).

## Differences from the paper

The paper applies Step 0 to the frozen matrix `tilde J_h^{(t)}` (`O(h^2)` from the frozen band); here the `O(h)` location from `(D_0)` relative to the plain band, plus the `O(h)` shift of the band from
`G_0 -> G_0 + h G_1`, is enough because the windows `delta_0` are fixed.  This avoids the (unproved) `FrozenStandard` premise `StdAssump (frozenFamily ..) (paramSet K t0)`.  The hypothesis `Kidx = (m+1)/2` is not used.

## Not formalised

Nothing beyond the statement.  The `O(h^2)` relation to the frozen band (`StepZero` for the frozen family) holds under `FrozenStandard` and is not needed here.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

/-! ### Perturbation of the band under `G_0 -> G_0 + h G_1`, `B_0 -> B_0 + h B_1` -/

/-- Pointwise `O(h)` closeness of `f_+` for `G_0 + h G_1`, `B_0 + h B_1` (the hard-edge factor cancels in the square root). -/
lemma fPlus_close {L g Mg Mb h : ℝ} (hL : 0 < L) (hg : 0 < g) (G0 G1 B0 B1 : ℝ → ℝ)
    (hG0 : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hMg : ∀ u ∈ Icc 0 L, |G1 u| ≤ Mg) (hMb : ∀ u ∈ Icc 0 L, |B1 u| ≤ Mb)
    (hh : 0 ≤ h) (hhg : h * Mg ≤ g / 2) {u : ℝ} (hu : u ∈ Icc 0 L) :
    |fPlus L (fun s => G0 s + h * G1 s) (fun s => B0 s + h * B1 s) u - fPlus L G0 B0 u| ≤
      h * (Mb + L * Mg / (2 * Real.sqrt (g / 2))) := by
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg u hu)
  have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans (hMb u hu)
  have hsg2 : 0 < Real.sqrt (g / 2) := Real.sqrt_pos.mpr (by positivity)
  have hdB : |B0 u + h * B1 u - B0 u| ≤ h * Mb := by
    rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left (hMb u hu) hh
  have hextra : 0 ≤ h * (L * Mg / (2 * Real.sqrt (g / 2))) := by positivity
  have hsq : |Real.sqrt (E0 L (fun s => G0 s + h * G1 s) u) - Real.sqrt (E0 L G0 u)| ≤
      L * (h * Mg) / (4 * Real.sqrt (g / 2)) := by
    rcases hu.1.eq_or_lt with h0 | h0
    · simp [E0, ← h0]; positivity
    rcases hu.2.eq_or_lt with hL' | hL'
    · simp [E0, hL']; positivity
    have hq : 0 < u * (L - u) := mul_pos h0 (by linarith)
    have hqL : u * (L - u) ≤ L ^ 2 / 4 := by nlinarith [sq_nonneg (u - L / 2)]
    have hδ : 0 ≤ h * Mg := by positivity
    have hd : |(G0 u + h * G1 u) - G0 u| ≤ h * Mg := by
      rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hh]
      exact mul_le_mul_of_nonneg_left (hMg u hu) hh
    have hd' : |G0 u - (G0 u + h * G1 u)| ≤ h * Mg := by rw [abs_sub_comm]; exact hd
    have hGt : g / 2 ≤ G0 u + h * G1 u := by
      have := (abs_le.mp (hMg u hu)).1
      nlinarith [hG0 u hu, mul_le_mul_of_nonneg_left (hMg u hu) hh, neg_abs_le (G1 u), mul_nonneg hh (abs_nonneg (G1 u))]
    have e1 := sqrt_perturb_le hL.le hq hqL hg hδ (hG0 u hu) hd
    have e2 := sqrt_perturb_le hL.le hq hqL (by positivity : 0 < g / 2) hδ hGt hd'
    have hsg : 0 < Real.sqrt g := Real.sqrt_pos.mpr hg
    have hle : Real.sqrt (g / 2) ≤ Real.sqrt g := Real.sqrt_le_sqrt (by linarith)
    have hc : L * (h * Mg) / (4 * Real.sqrt g) ≤ L * (h * Mg) / (4 * Real.sqrt (g / 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    simp only [E0]
    rw [abs_le]
    constructor <;> linarith
  have hfd : fPlus L (fun s => G0 s + h * G1 s) (fun s => B0 s + h * B1 s) u - fPlus L G0 B0 u =
      (B0 u + h * B1 u - B0 u) + 2 * (Real.sqrt (E0 L (fun s => G0 s + h * G1 s) u) - Real.sqrt (E0 L G0 u)) := by
    unfold fPlus; ring
  rw [hfd]
  calc _ ≤ |B0 u + h * B1 u - B0 u| + |2 * (Real.sqrt (E0 L (fun s => G0 s + h * G1 s) u) - Real.sqrt (E0 L G0 u))| :=
        abs_add_le _ _
    _ ≤ h * Mb + 2 * (L * (h * Mg) / (4 * Real.sqrt (g / 2))) := by
        rw [abs_mul, abs_two]
        linarith
    _ = h * (Mb + L * Mg / (2 * Real.sqrt (g / 2))) := by field_simp; ring

/-- Boundedness above of `f_+` for continuous symbols. -/
lemma bddAbove_fPlus {L : ℝ} {G B : ℝ → ℝ} (hG : ContinuousOn G (Icc 0 L)) (hB : ContinuousOn B (Icc 0 L)) :
    BddAbove (fPlus L G B '' Icc 0 L) := by
  have hc : ContinuousOn (fPlus L G B) (Icc 0 L) := by
    unfold fPlus E0
    exact hB.add (continuousOn_const.mul ((((continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).mul hG)).sqrt))
  exact isCompact_Icc.bddAbove_image hc

/-- If `f_+(G_0,B_0) <= f_+(G_1,B_1) + c` pointwise on `[0,L]`, then `X_s^+(G_0,B_0) <= X_s^+(G_1,B_1) + c`. -/
lemma Xsp_le_add {L c : ℝ} (hL : 0 ≤ L) {G0 B0 G1 B1 : ℝ → ℝ} (hG : ContinuousOn G1 (Icc 0 L)) (hB : ContinuousOn B1 (Icc 0 L))
    (h : ∀ u ∈ Icc 0 L, fPlus L G0 B0 u ≤ fPlus L G1 B1 u + c) : Xsp L G0 B0 ≤ Xsp L G1 B1 + c := by
  unfold Xsp
  apply csSup_le ((Set.nonempty_Icc.mpr hL).image _)
  rintro _ ⟨u, hu, rfl⟩
  exact (h u hu).trans (add_le_add_left (le_csSup (bddAbove_fPlus hG hB) ⟨u, hu, rfl⟩) c)

/-! ### The frozen band at `t = h` -/

section Frozen

variable {Par : Type*} [TopologicalSpace Par]

omit [TopologicalSpace Par] in
lemma frozen_G0 (F : SymbolFamily Par) (Kd : ℕ) (μ : Par) (t : ℝ) :
    (frozenFamily F Kd).G 0 (μ, t) = fun s => F.G 0 μ s + t * F.G 1 μ s := by
  funext s; simp [frozenFamily]

omit [TopologicalSpace Par] in
lemma frozen_B0 (F : SymbolFamily Par) (Kd : ℕ) (μ : Par) (t : ℝ) :
    (frozenFamily F Kd).B 0 (μ, t) = fun s => F.B 0 μ s + t * F.B 1 μ s := by
  funext s; simp [frozenFamily]

omit [TopologicalSpace Par] in
lemma frozen_bandHi (F : SymbolFamily Par) (Kd : ℕ) (μ : Par) (t : ℝ) :
    (frozenFamily F Kd).bandHi (μ, t) = Xsp F.L (fun s => F.G 0 μ s + t * F.G 1 μ s) (fun s => F.B 0 μ s + t * F.B 1 μ s) := by
  unfold SymbolFamily.bandHi
  rw [frozen_G0, frozen_B0]; rfl

omit [TopologicalSpace Par] in
lemma frozen_bandLo (F : SymbolFamily Par) (Kd : ℕ) (μ : Par) (t : ℝ) :
    (frozenFamily F Kd).bandLo (μ, t) = Xsm F.L (fun s => F.G 0 μ s + t * F.G 1 μ s) (fun s => F.B 0 μ s + t * F.B 1 μ s) := by
  unfold SymbolFamily.bandLo
  rw [frozen_G0, frozen_B0]; rfl

end Frozen

/-- **The three cases of `def:tha-Psihat` exhaust the spectrum** (frozen statement `SpectrumCovered`): proved from the `O(h)` location of the eigenvalues
(`eigen_loc` with `e = 1`, i.e. `StepZeroD0`) and the `O(h)` distance between the plain band and the frozen band at `t = h` (`Xsp_le_add`, `fPlus_close`); the
cover property `CI.cover` of the chart data does the rest. -/
theorem spectrumCovered {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ}
    {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ} (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) : SpectrumCovered CI := by
  intro _ hK hH hD
  rcases K.eq_empty_or_nonempty with hKe | ⟨μ0, hμ0⟩
  · exact ⟨1, one_pos, fun μ hμ => by simp [hKe] at hμ⟩
  obtain ⟨g, hg⟩ := hH
  have hgpos : 0 < g := (hg μ0 hμ0).gstar_pos
  obtain ⟨C1, h1, hh1, H1⟩ := eigen_loc (coreReg_of_DM hK hD) (by norm_num) (upHyp_of_hypOn ⟨g, hg⟩)
    (upHyp_neg_of_hypOn ⟨g, hg⟩)
  obtain ⟨Mg, hMg⟩ := jets_bound_choose hK (n := 2 * Kidx + 1) (fun j => F.G j)
    (fun j => regBudget (2 * Kidx + 1) - 10 * (j / 2)) (fun j hj => (hD.reg j hj).1)
  obtain ⟨Mb, hMb⟩ := jets_bound_choose hK (n := 2 * Kidx + 1) (fun j => F.B j)
    (fun j => regBudget (2 * Kidx + 1) - 10 * (j / 2)) (fun j hj => (hD.reg j hj).2)
  have hL := F.L_pos
  have hsg : 0 < Real.sqrt (g / 2) := Real.sqrt_pos.mpr (by positivity)
  set c2 : ℝ := |Mb 1| + F.L * |Mg 1| / (2 * Real.sqrt (g / 2)) with hc2
  have hδ : 0 < min CI.softUpL.δ0 CI.softLoL.δ0 :=
    lt_min CI.softUpL.consts_pos.1 CI.softLoL.consts_pos.1
  have hc2' : 0 ≤ c2 := by positivity
  refine ⟨min h1 (min (g / (2 * (|Mg 1| + 1))) (min CI.softUpL.δ0 CI.softLoL.δ0 / (|C1| + c2 + 1))), ?_, ?_⟩
  · refine lt_min hh1 (lt_min (by positivity) (by positivity))
  intro μ hμ N hN ht0 X Um hE k
  have hh := step_pos F N
  have hNh1 : F.step N ≤ h1 := hN.trans (min_le_left _ _)
  have hNg : F.step N ≤ g / (2 * (|Mg 1| + 1)) := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hNδ : F.step N ≤ min CI.softUpL.δ0 CI.softLoL.δ0 / (|C1| + c2 + 1) :=
    hN.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCh : (|C1| + c2) * F.step N ≤ min CI.softUpL.δ0 CI.softLoL.δ0 := by
    have hpos : 0 < |C1| + c2 + 1 := by positivity
    have := (le_div_iff₀ hpos).mp hNδ
    nlinarith [abs_nonneg C1]
  have hδup : min CI.softUpL.δ0 CI.softLoL.δ0 ≤ CI.softUpL.δ0 := min_le_left _ _
  have hδlo : min CI.softUpL.δ0 CI.softLoL.δ0 ≤ CI.softLoL.δ0 := min_le_right _ _
  have hhg : F.step N * |Mg 1| ≤ g / 2 := by
    have hpos : 0 < 2 * (|Mg 1| + 1) := by positivity
    have := (le_div_iff₀ hpos).mp hNg
    nlinarith [abs_nonneg (Mg 1)]
  -- eigenvalue location (O(h))
  obtain ⟨hXlo, hXhi⟩ := H1 μ hμ N hNh1 X Um hE k
  rw [pow_one] at hXlo hXhi
  -- frozen band
  have hp : (μ, F.step N) ∈ paramSet K t0 := ⟨hμ, by constructor <;> linarith⟩
  obtain ⟨-, -, -, hcHi, hcLo⟩ := CI.cover _ hp
  have hG1 : ∀ u ∈ Icc 0 F.L, |F.G 1 μ u| ≤ |Mg 1| := fun u hu =>
    (hMg 1 (by omega) μ hμ u hu).trans (le_abs_self _)
  have hB1 : ∀ u ∈ Icc 0 F.L, |F.B 1 μ u| ≤ |Mb 1| := fun u hu =>
    (hMb 1 (by omega) μ hμ u hu).trans (le_abs_self _)
  have hcG : ContinuousOn (fun s => F.G 0 μ s + F.step N * F.G 1 μ s) (Icc 0 F.L) :=
    ((hD.reg 0 (Nat.zero_le _)).1.1 μ hμ).continuousOn.add
      (continuousOn_const.mul ((hD.reg 1 (by omega)).1.1 μ hμ).continuousOn)
  have hcB : ContinuousOn (fun s => F.B 0 μ s + F.step N * F.B 1 μ s) (Icc 0 F.L) :=
    ((hD.reg 0 (Nat.zero_le _)).2.1 μ hμ).continuousOn.add
      (continuousOn_const.mul ((hD.reg 1 (by omega)).2.1 μ hμ).continuousOn)
  have hcB' : ContinuousOn (fun s => -(F.B 0 μ s + F.step N * F.B 1 μ s)) (Icc 0 F.L) := hcB.neg
  have hA : F.bandHi μ ≤ (frozenFamily F Kidx).bandHi (μ, F.step N) + c2 * F.step N := by
    rw [frozen_bandHi]
    refine Xsp_le_add hL.le hcG hcB fun u hu => ?_
    have := fPlus_close hL hgpos (F.G 0 μ) (F.G 1 μ) (F.B 0 μ) (F.B 1 μ) (hg μ hμ).G0_lb hG1 hB1 hh.le
      (by linarith) hu
    have h2 := (abs_le.mp this).1
    have : c2 * F.step N = F.step N * (|Mb 1| + F.L * |Mg 1| / (2 * Real.sqrt (g / 2))) := by rw [hc2]; ring
    linarith
  have hB : (frozenFamily F Kidx).bandLo (μ, F.step N) ≤ F.bandLo μ + c2 * F.step N := by
    rw [frozen_bandLo]
    have hx := Xsp_le_add (L := F.L) (c := c2 * F.step N) hL.le (G0 := F.G 0 μ) (B0 := fun s => -F.B 0 μ s)
      (G1 := fun s => F.G 0 μ s + F.step N * F.G 1 μ s) (B1 := fun s => -(F.B 0 μ s + F.step N * F.B 1 μ s)) hcG hcB' (by
        intro u hu
        have := fPlus_close hL hgpos (F.G 0 μ) (F.G 1 μ) (fun s => -F.B 0 μ s) (fun s => -F.B 1 μ s)
          (hg μ hμ).G0_lb hG1 (fun u hu => by simpa using hB1 u hu) hh.le (by linarith) hu
        have h2 := (abs_le.mp this).1
        have e : (fun s => -F.B 0 μ s + F.step N * -F.B 1 μ s) = fun s => -(F.B 0 μ s + F.step N * F.B 1 μ s) := by
          funext s; ring
        rw [e] at h2
        have : c2 * F.step N = F.step N * (|Mb 1| + F.L * |Mg 1| / (2 * Real.sqrt (g / 2))) := by rw [hc2]; ring
        linarith)
    rw [Xsp_neg, Xsp_neg] at hx
    have hbl : F.bandLo μ = Xsm F.L (F.G 0 μ) (F.B 0 μ) := rfl
    rw [hbl]
    linarith
  have hC1a : C1 * F.step N ≤ |C1| * F.step N := mul_le_mul_of_nonneg_right (le_abs_self C1) hh.le
  have hC1b : -(C1 * F.step N) ≤ |C1| * F.step N := by
    have := mul_le_mul_of_nonneg_right (neg_le_abs C1) hh.le
    linarith
  -- the three cases
  simp only [atStep]
  by_cases hb : ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν
  · exact Or.inl hb
  · by_cases hJ : CI.Jhi < X k
    · refine Or.inr (Or.inl ⟨hb, hJ, abs_le.mpr ⟨by linarith, ?_⟩⟩)
      linarith
    · refine Or.inr (Or.inr ⟨hb, hJ, ?_⟩)
      have hXJ : X k ≤ CI.Jhi := not_lt.mp hJ
      have hXlt : X k < CI.Jlo := by
        by_contra hcon
        exact hb (CI.cover_bulk _ (not_lt.mp hcon) hXJ)
      rw [negFamily_bandHi, abs_le]
      constructor
      · linarith
      · linarith

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.spectrumCovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.spectrumCovered

end FormalResearch.JacobiEigenvectors.TheoremA
