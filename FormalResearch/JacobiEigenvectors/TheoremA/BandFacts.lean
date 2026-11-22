module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Setting.JacobiFamily

/-!
# Paper J, Layer 2: two elementary consequences of the standing hypotheses (findings F-S6-2, F-S6-3)

Source: Paper J `main_results.tex` (def:symbols, (D_M), (H1)--(H3)), used by `thm:smo-spec` (`TheoremA/SmoothSpectrum.lean`).

## Proved here (axiom-pinned)

* `bandLo_lt_bandHi` (**F-S6-2**, agent M's proposed premise `X_s^- < X_s^+` of `ThmSmoSpec` (b), (c)): under (H1), (H3) for `mu` and continuity of the principal symbols `G_0, B_0` on `[0,L]`
  (part of `(D_0)`), `X_s^-(mu) < X_s^+(mu)`.  Proof: `X_s^- <= f_-(u_c^+) < f_+(u_c^+) <= X_s^+` (`E_0(u_c^+) > 0`, so `f_+ - f_- = 4 sqrt(E_0) > 0` at the interior point `u_c^+`;
  `X_s^+ = sup f_+`, `X_s^- = inf f_-` of continuous functions on a compact interval).  **Confirmed, and no premise is needed**: `ThmSmoSpec` is not changed for it.
* `jet_bdd`: `JetReg` on a compact `K` bounds the jets on `K x [0,L]`.
* `jetReg_mono`: `JetReg f K L r` implies `JetReg f K L r'` for `r' <= r`.
* `dm_mono`, `dm_zero_of_dm` (**F-S6-3**): for compact `K`, `DM F K M` implies `DM F K j` (`j <= M`), in particular `DM F K 0` (the jets `G_j, B_j` are bounded on the compact set `K x [0,L]` by the joint continuity in `JetReg`, so
  `|G_h - G_0| <= C h` for `h <= L`).  **Confirmed**: `StepZeroD0`, `EigDensity` (stated for `DM F K 0`) apply under the hypothesis `DM F K M` of `ThmSmoSpec`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Set Finset FormalResearch.JacobiEigenvectors.Setting

variable {Par : Type*} [TopologicalSpace Par]

/-- `h (N + 1) = L`. -/
lemma step_mul_succ_aux (F : SymbolFamily Par) (N : ℕ) : F.step N * ((N : ℝ) + 1) = F.L := by
  unfold SymbolFamily.step FormalResearch.JB.stepSize
  exact div_mul_cancel₀ F.L (by positivity)

/-- `E_0` is continuous on `[0,L]` when `G_0` is. -/
lemma E0_continuousOn {L : ℝ} {G0 : ℝ → ℝ} (hG : ContinuousOn G0 (Icc 0 L)) : ContinuousOn (E0 L G0) (Icc 0 L) := by
  unfold E0
  exact (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).mul hG

/-- **F-S6-2**: `X_s^- < X_s^+` from (H1), (H3) and continuity of `G_0, B_0` on `[0,L]`. -/
theorem bandLo_lt_bandHi_of {L : ℝ} {G0 B0 : ℝ → ℝ} {g : ℝ} (h : Hyp L G0 B0 g)
    (hG : ContinuousOn G0 (Icc 0 L)) (hB : ContinuousOn B0 (Icc 0 L)) : Xsm L G0 B0 < Xsp L G0 B0 := by
  obtain ⟨uc, huc0, hucL, hucE, -⟩ := h.H3p
  have hE : ContinuousOn (E0 L G0) (Icc 0 L) := E0_continuousOn hG
  have hsq : ContinuousOn (fun u => Real.sqrt (E0 L G0 u)) (Icc 0 L) := hE.sqrt
  have hfp : ContinuousOn (fPlus L G0 B0) (Icc 0 L) := hB.add (continuousOn_const.mul hsq)
  have hfm : ContinuousOn (fMinus L G0 B0) (Icc 0 L) := hB.sub (continuousOn_const.mul hsq)
  have hmem : uc ∈ Icc 0 L := ⟨huc0.le, hucL.le⟩
  have h1 : fPlus L G0 B0 uc ≤ Xsp L G0 B0 :=
    le_csSup (isCompact_Icc.image_of_continuousOn hfp).bddAbove ⟨uc, hmem, rfl⟩
  have h2 : Xsm L G0 B0 ≤ fMinus L G0 B0 uc :=
    csInf_le (isCompact_Icc.image_of_continuousOn hfm).bddBelow ⟨uc, hmem, rfl⟩
  have hEpos : 0 < E0 L G0 uc := by
    unfold E0
    exact mul_pos (mul_pos huc0 (by linarith)) (lt_of_lt_of_le h.gstar_pos (h.G0_lb uc hmem))
  have h3 : fMinus L G0 B0 uc < fPlus L G0 B0 uc := by
    unfold fMinus fPlus
    have := Real.sqrt_pos.mpr hEpos
    linarith
  linarith

theorem bandLo_lt_bandHi (F : SymbolFamily Par) (K : Set Par) (M : ℕ) (hH : HypOn F K) (hD : DM F K M) :
    ∀ μ ∈ K, F.bandLo μ < F.bandHi μ := by
  obtain ⟨g, hg⟩ := hH
  intro μ hμ
  have hG : ContinuousOn (F.G 0 μ) (Icc 0 F.L) := ((hD.reg 0 (Nat.zero_le _)).1.1 μ hμ).continuousOn
  have hB : ContinuousOn (F.B 0 μ) (Icc 0 F.L) := ((hD.reg 0 (Nat.zero_le _)).2.1 μ hμ).continuousOn
  exact bandLo_lt_bandHi_of (hg μ hμ) hG hB

lemma jetReg_mono {f : Par → ℝ → ℝ} {K : Set Par} {L : ℝ} {r r' : ℕ} (hr : r' ≤ r) (h : JetReg f K L r) : JetReg f K L r' :=
  ⟨fun μ hμ => (h.1 μ hμ).of_le (by exact_mod_cast hr), fun i hi => h.2 i (hi.trans hr)⟩

/-- Pure algebra: truncating a remainder estimate `O(h^{M+1})` at order `M` to one at order `j <= M`, for `0 < h <= Lam`, with bounded jets. -/
lemma rem_trunc_aux (fh : ℝ) (fj : ℕ → ℝ) (j M : ℕ) (hjM : j ≤ M) (h Lam C0 : ℝ) (Kb : ℕ → ℝ) (hh : 0 < h) (hhL : h ≤ Lam)
    (hrem : |fh - ∑ i ∈ range (M + 1), h ^ i * fj i| ≤ C0 * h ^ (M + 1)) (hb : ∀ i ≤ M, |fj i| ≤ Kb i) :
    |fh - ∑ i ∈ range (j + 1), h ^ i * fj i|
      ≤ (|C0| * Lam ^ (M - j) + ∑ i ∈ Ico (j + 1) (M + 1), Lam ^ (i - (j + 1)) * |Kb i|) * h ^ (j + 1) := by
  have hLam : 0 ≤ Lam := hh.le.trans hhL
  have hsplit := Finset.sum_range_add_sum_Ico (fun i => h ^ i * fj i) (show j + 1 ≤ M + 1 by omega)
  have e : fh - ∑ i ∈ range (j + 1), h ^ i * fj i
      = (fh - ∑ i ∈ range (M + 1), h ^ i * fj i) + ∑ i ∈ Ico (j + 1) (M + 1), h ^ i * fj i := by
    linarith [hsplit]
  rw [e]
  have hpow : ∀ n : ℕ, h ^ (j + 1 + n) ≤ Lam ^ n * h ^ (j + 1) := by
    intro n
    rw [pow_add, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh.le hhL n) (pow_nonneg hh.le _)
  have h1 : C0 * h ^ (M + 1) ≤ |C0| * Lam ^ (M - j) * h ^ (j + 1) := by
    have hM1 : h ^ (M + 1) ≤ Lam ^ (M - j) * h ^ (j + 1) := by
      have := hpow (M - j)
      rwa [show j + 1 + (M - j) = M + 1 by omega] at this
    calc C0 * h ^ (M + 1) ≤ |C0| * h ^ (M + 1) := mul_le_mul_of_nonneg_right (le_abs_self C0) (pow_nonneg hh.le _)
      _ ≤ |C0| * (Lam ^ (M - j) * h ^ (j + 1)) := mul_le_mul_of_nonneg_left hM1 (abs_nonneg _)
      _ = _ := by ring
  have h2 : |∑ i ∈ Ico (j + 1) (M + 1), h ^ i * fj i|
      ≤ (∑ i ∈ Ico (j + 1) (M + 1), Lam ^ (i - (j + 1)) * |Kb i|) * h ^ (j + 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    rw [abs_mul, abs_of_pos (pow_pos hh _)]
    have hp := hpow (i - (j + 1))
    rw [show j + 1 + (i - (j + 1)) = i by omega] at hp
    calc h ^ i * |fj i| ≤ (Lam ^ (i - (j + 1)) * h ^ (j + 1)) * |Kb i| :=
          mul_le_mul hp ((hb i (by omega)).trans (le_abs_self _)) (abs_nonneg _) (by positivity)
      _ = Lam ^ (i - (j + 1)) * |Kb i| * h ^ (j + 1) := by ring
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ |C0| * Lam ^ (M - j) * h ^ (j + 1) + (∑ i ∈ Ico (j + 1) (M + 1), Lam ^ (i - (j + 1)) * |Kb i|) * h ^ (j + 1) :=
        add_le_add (hrem.trans h1) h2
    _ = _ := by ring

/-- Jets of a family with `JetReg` on a compact `K` are bounded on `K x [0,L]` (joint continuity, compactness). -/
lemma jet_bdd (K : Set Par) (hK : IsCompact K) (L : ℝ) (M : ℕ) (r : ℕ → ℕ) (f : ℕ → Par → ℝ → ℝ)
    (hf : ∀ j ≤ M, JetReg (f j) K L (r j)) :
    ∃ Kb : ℕ → ℝ, ∀ j ≤ M, ∀ μ ∈ K, ∀ s ∈ Icc 0 L, |f j μ s| ≤ Kb j := by
  have : ∀ j ≤ M, ∃ Kj : ℝ, ∀ μ ∈ K, ∀ s ∈ Icc 0 L, |f j μ s| ≤ Kj := by
    intro j hj
    have hc : ContinuousOn (fun p : Par × ℝ => f j p.1 p.2) (K ×ˢ Icc 0 L) := by
      have := (hf j hj).2 0 (Nat.zero_le _)
      simpa [iteratedDerivWithin_zero] using this
    obtain ⟨Kj, hKj⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hc
    exact ⟨Kj, fun μ hμ s hs => by simpa [Real.norm_eq_abs] using hKj (μ, s) ⟨hμ, hs⟩⟩
  choose! Kb hKb using this
  exact ⟨Kb, fun j hj μ hμ s hs => hKb j hj μ hμ s hs⟩

/-- `DM F K M` implies `DM F K j` for `j <= M` and compact `K` (the jets are bounded on `K x [0,L]`). -/
theorem dm_mono (F : SymbolFamily Par) (K : Set Par) {j M : ℕ} (hjM : j ≤ M) (hK : IsCompact K) (hD : DM F K M) : DM F K j := by
  obtain ⟨KG, hKG⟩ := jet_bdd K hK F.L M _ F.G (fun i hi => (hD.reg i hi).1)
  obtain ⟨KB, hKB⟩ := jet_bdd K hK F.L M _ F.B (fun i hi => (hD.reg i hi).2)
  obtain ⟨C0, hC0⟩ := hD.rem
  refine ⟨?_, ?_⟩
  · intro i hi
    have hb : regBudget j - 10 * (i / 2) ≤ regBudget M - 10 * (i / 2) := by unfold regBudget; omega
    exact ⟨jetReg_mono hb (hD.reg i (hi.trans hjM)).1, jetReg_mono hb (hD.reg i (hi.trans hjM)).2⟩
  · refine ⟨max (|C0| * F.L ^ (M - j) + ∑ i ∈ Ico (j + 1) (M + 1), F.L ^ (i - (j + 1)) * |KG i|)
      (|C0| * F.L ^ (M - j) + ∑ i ∈ Ico (j + 1) (M + 1), F.L ^ (i - (j + 1)) * |KB i|), ?_⟩
    intro μ hμ N s hs
    have hh : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have hhL : F.step N ≤ F.L := by
      unfold SymbolFamily.step FormalResearch.JB.stepSize
      exact div_le_self F.L_pos.le (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)
    obtain ⟨hG1, hB1⟩ := hC0 μ hμ N s hs
    have hh1 : 0 ≤ F.step N ^ (j + 1) := pow_nonneg hh.le _
    constructor
    · exact (rem_trunc_aux _ _ j M hjM (F.step N) F.L C0 KG hh hhL hG1 (fun i hi => hKG i hi μ hμ s hs)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hh1)
    · exact (rem_trunc_aux _ _ j M hjM (F.step N) F.L C0 KB hh hhL hB1 (fun i hi => hKB i hi μ hμ s hs)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hh1)

/-- **F-S6-3**: `DM F K M` implies `DM F K 0` for compact `K`. -/
theorem dm_zero_of_dm (F : SymbolFamily Par) (K : Set Par) (M : ℕ) (hK : IsCompact K) (hD : DM F K M) : DM F K 0 :=
  dm_mono F K (Nat.zero_le M) hK hD

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bandLo_lt_bandHi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bandLo_lt_bandHi

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.dm_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.dm_mono

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.dm_zero_of_dm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.dm_zero_of_dm

end FormalResearch.JacobiEigenvectors.TheoremA
