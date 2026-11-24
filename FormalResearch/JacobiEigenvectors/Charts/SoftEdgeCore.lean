module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.BulkWeberCore

/-!
# Paper J, charts: the soft-edge chart from its core

`SoftEdgeChart F P m q U V Lm` extends `SoftEdgeCore` (`Charts/SoftParabolicCylinder.lean`) by the fields `bondA_le`, `grow_gap`,
`seed_posW`, `collar_lbW`, `ratio2`, `ratioM`, `lb_weber`, `lb_pc`, `grow3` and their constants.  For the model pair `pcU, pcV` these
follow from the core and the standing assumptions on the family: `SoftEdgeChart.ofCore` builds the chart, with `N0` raised so that
`h = L/(N+1)` is below the thresholds of the derivations.  The inputs are the Layer-4 lemmas of `Charts/SoftBounds.lean`.

The derivations: `exists_weber` (`seed_posW`, `collar_lbW`, the Weber half of `lb_weber`), `exists_ratioM`, `exists_pc` (`lb_pc`, `ratio2`,
`grow3`), `exists_bonds` (`bondA_le`, `grow_gap`, from the standing assumptions `FamilyInputs`); `exists_chart` assembles them.
`lamL_cont`, `theta_leW`, `theta_le` stay core fields (they need regularity in `X` and the modulus sums, Phase II).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Engine
open FormalResearch.JacobiEigenvectors.TheoremA

namespace SoftEdgeCore

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {m q : ℕ} {Lm : ℝ → ℝ}
  (C : SoftEdgeCore F P m q pcU pcV Lm)

/-- The Weber chart `chainW`: the rows `0 <= k <= N_W` lie in `[0, u_c - eta/2]`. -/
lemma uNodeW_mem {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : |X - F.bandHi μ| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N) {k : ℤ}
    (hk : k ∈ Finset.Icc (0 : ℤ) (C.chainW μ X N).NR) :
    0 ≤ uNode (F.step N) k ∧ uNode (F.step N) k ≤ C.uc μ - C.η / 2 := by
  obtain ⟨hk0, hkN⟩ := Finset.mem_Icc.mp hk
  have hh := step_pos F N
  have hshape := (C.shapeW μ hμ X hX N hN).2.2.2.1
  have hk0' : (0 : ℝ) ≤ k := by exact_mod_cast hk0
  have hkN' : (k : ℝ) ≤ (C.chainW μ X N).NR := by exact_mod_cast hkN
  unfold uNode at hshape ⊢
  constructor
  · positivity
  · nlinarith

/-- The shape of the three-patch chain: `0 < j_1 < j_2`, `j_2 + 2 <= N_R` (`PreValid` with `P = 3`). -/
lemma jj_order {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : |X - F.bandHi μ| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N) :
    0 < (C.chain μ X N).jj 1 ∧ (C.chain μ X N).jj 1 < (C.chain μ X N).jj 2 ∧
      (C.chain μ X N).jj 2 + 2 ≤ (C.chain μ X N).NR := by
  have hv := C.valid μ hμ X hX N hN
  have hP : (C.chain μ X N).P = 3 := (C.shape μ hμ X hX N hN).1
  have h0 := hv.jj0
  have h01 := hv.jj_mono 0 (by simp [LadderData.rescale1, hP])
  have h12 := hv.jj_mono 1 (by simp [LadderData.rescale1, hP])
  have h23 := hv.jj_mono 2 (by simp [LadderData.rescale1, hP])
  have hl := hv.jj_last
  simp only [LadderData.rescale1_jj] at h0 h01 h12 h23 hl
  simp only [LadderData.rescale1, hP] at hl
  norm_num at h01 h12 h23
  exact ⟨by omega, by omega, by omega⟩

/-- **The Weber part of the soft chart** (`seed_posW`, `collar_lbW`, `lb_weber` on `chainW`): from `corr_leadW`, `Y_forb`, `Y_le` by
`weber_seed_pos_of_corr`, `weber_collar_lb_of_corr`. -/
theorem exists_weber : ∃ N1 : ℕ, ∃ c3 : ℝ, 0 < c3 ∧
    (∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ C.δ0 → ∀ N, max C.N0 N1 ≤ N → 0 < (C.chainW μ X N).phi (F.step N) 0 1 0) ∧
    (∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ C.δ0 → ∀ N, max C.N0 N1 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (C.chainW μ X N).NR,
      c3 * (C.chainW μ X N).W k * (C.chainW μ X N).M k ≤ |(C.chainW μ X N).phi (F.step N) 0 1 k|) := by
  obtain ⟨CY0, hYle⟩ := C.Y_le
  set CY := max CY0 0
  have hCY : 0 ≤ CY := le_max_right _ _
  obtain ⟨cg, Cg0, hcg, g0, hcorr⟩ := C.corr_leadW
  set Cg := max Cg0 0
  have hCg : 0 ≤ Cg := le_max_right _ _
  obtain ⟨hs, hs_pos, hseed⟩ := weber_seed_pos_of_corr (half_pos hcg) hCg hCY
  obtain ⟨c3c, hcl, hc3, hcl_pos, hcoll⟩ := weber_collar_lb_of_corr (half_pos hcg) hCg F.L_pos.le hCY
  set hA := cg / (2 * (Cg + 1))
  have hA_pos : 0 < hA := by positivity
  obtain ⟨N1, hN1⟩ := exists_N_step_le F (lt_min (lt_min one_pos hA_pos) (lt_min hs_pos hcl_pos))
  refine ⟨N1, c3c, hc3, ?_⟩
  have hstep : ∀ N, max C.N0 N1 ≤ N →
      C.N0 ≤ N ∧ 0 < F.step N ∧ F.step N ≤ 1 ∧ F.step N ≤ hA ∧ F.step N ≤ hs ∧ F.step N ≤ hcl := by
    intro N hN
    have h := hN1 N ((le_max_right _ _).trans hN)
    simp only [le_min_iff] at h
    exact ⟨(le_max_left _ _).trans hN, step_pos F N, h.1.1, h.1.2, h.2.1, h.2.2⟩
  have hrow : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ C.δ0 → ∀ N, max C.N0 N1 ≤ N →
      ∀ k ∈ Finset.Icc (0 : ℤ) (C.chainW μ X N).NR,
      cg / 2 ≤ (C.chainW μ X N).AA 1 (uNode (F.step N) k) (F.step N) ∧
      |(C.chainW μ X N).BB 1 (uNode (F.step N) k) (F.step N)| ≤ Cg ∧
      |C.Y μ X (uNode (F.step N) k)| ≤ CY ∧
      4 * uNode (F.step N) k ≤ C.Y μ X (uNode (F.step N) k) ^ 2 := by
    intro μ hμ X hX N hN k hk
    obtain ⟨hN0, hh, hh1, hhA, -, -⟩ := hstep N hN
    obtain ⟨hg, hAg, hB⟩ := hcorr μ hμ X hX N hN0 k hk
    have hu := C.uNodeW_mem hμ hX hN0 hk
    obtain ⟨hF, hYpos⟩ := C.Y_forb μ hμ X hX _ hu
    have hcF := C.consts_pos.2.2.2.2.2.1
    refine ⟨BulkWeberCore.A_lb_of_corr hCg hh hh1 hhA hg (hAg.trans (by gcongr; exact le_max_left _ _)),
      hB.trans (le_max_left _ _), ?_, by linarith⟩
    rw [abs_of_pos hYpos]
    exact (hYle μ hμ X hX _ hu).trans (le_max_left _ _)
  refine ⟨?_, ?_⟩
  · intro μ hμ X hX N hN
    obtain ⟨hN0, hh, -, -, hhs, -⟩ := hstep N hN
    have hNR0 := (C.shapeW μ hμ X hX N hN0).2.2.1
    have hk : (0 : ℤ) ∈ Finset.Icc (0 : ℤ) (C.chainW μ X N).NR := Finset.mem_Icc.mpr ⟨le_rfl, hNR0⟩
    have he := LadderData.phi_eq_weberModelPhi (C.chainW μ X N) (j := 0)
      (C.wfW_eq μ hμ X hX N hN0 ((0 : ℕ) : ℤ) (by simp only [Nat.cast_zero, Finset.mem_Icc]; omega)).1
    simp only [Nat.cast_zero] at he
    rw [he]
    obtain ⟨hA', hB, hY, -⟩ := hrow μ hμ X hX N hN 0 hk
    exact hseed hh hhs hY hA' hB
  · intro μ hμ X hX N hN k hk
    obtain ⟨hN0, hh, -, -, -, hhc⟩ := hstep N hN
    obtain ⟨hA', hB, hY, h4⟩ := hrow μ hμ X hX N hN k hk
    have hu := C.uNodeW_mem hμ hX hN0 hk
    rw [C.W_defW μ hμ X hX N hN0 k hk, C.M_defW μ hμ X hX N hN0 k hk]
    obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (Finset.mem_Icc.mp hk).1
    rw [LadderData.phi_eq_weberModelPhi (C.chainW μ X N) (j := j)
      (C.wfW_eq μ hμ X hX N hN0 (j : ℤ) (by simp only [Finset.mem_Icc] at hk ⊢; omega)).1]
    have ej : ((j : ℤ) : ℝ) = (j : ℝ) := Int.cast_natCast j
    have hU : uNode (F.step N) (j : ℤ) = ((j : ℝ) + 1 / 2) * F.step N := by unfold uNode; rw [ej]
    have h4' : 4 * (((j : ℝ) + 1 / 2) * F.step N) ≤ C.Y μ X (uNode (F.step N) j) ^ 2 := by rw [← hU]; exact h4
    have hL : ((j : ℝ) + 1 / 2) * F.step N ≤ F.L := by
      rw [← hU]; linarith [hu.2, (C.ucη_in μ hμ).2, C.consts_pos.2.1]
    rw [ej]
    exact hcoll hh hhc hL hY (BulkWeberCore.two_sqrt_le_abs hh (by positivity) h4') hA' hB

/-- **`ratioM`**: `M_{j_1+1} <= C_M M_{j_1}` (`soft_ratioM`, with `Y_le` and the margin `Zq_lb` of `zeta` at the row after the overlap). -/
theorem exists_ratioM : ∃ N1 : ℕ, ∃ CM : ℝ, 0 < CM ∧
    ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ C.δ0 → ∀ N, max C.N0 N1 ≤ N →
      (C.chain μ X N).M ((C.chain μ X N).jj 1 + 1) ≤ CM * (C.chain μ X N).M ((C.chain μ X N).jj 1) := by
  obtain ⟨CY0, hYle⟩ := C.Y_le
  set CY := max CY0 0
  have hCY : 0 ≤ CY := le_max_right _ _
  have hcz1 := C.consts_pos2.2
  have hη := C.consts_pos.2.1
  have hrat := soft_ratioM F.L_pos hCY hcz1
  dsimp only at hrat
  obtain ⟨hCM, hrat⟩ := hrat
  obtain ⟨N1, hN1⟩ := exists_N_step_le F C.softH1_pos
  refine ⟨N1, (8 * max (CY ^ 2 / 4 + F.L) (F.L + 1) / C.cz1) ^ ((1 : ℝ) / 4), hCM, ?_⟩
  intro μ hμ X hX N hN
  have hN0 : C.N0 ≤ N := (le_max_left _ _).trans hN
  have hh := step_pos F N
  have hhH : F.step N ≤ C.softH1 := hN1 N ((le_max_right _ _).trans hN)
  have hh1 : F.step N ≤ 1 := hhH.trans C.softH1_le_one
  have hhη : F.step N ≤ C.η / 2 := hhH.trans C.softH1_le_eta
  obtain ⟨hj1, hj12, hj2N⟩ := C.jj_order hμ hX hN0
  obtain ⟨-, -, hu1, hu1', -⟩ := C.shape μ hμ X hX N hN0
  set j1 := (C.chain μ X N).jj 1
  have hmem1 : j1 ∈ Finset.Icc (0 : ℤ) j1 := Finset.mem_Icc.mpr ⟨hj1.le, le_rfl⟩
  have hmem2 : j1 + 1 ∈ Finset.Icc (j1 + 1) (C.chain μ X N).NR := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  rw [C.M1_def μ hμ X hX N hN0 j1 hmem1, C.M2_def μ hμ X hX N hN0 (j1 + 1) hmem2]
  have hj1' : (0 : ℝ) ≤ (j1 : ℝ) := by exact_mod_cast hj1.le
  have hu0 : 0 ≤ uNode (F.step N) j1 := by unfold uNode; positivity
  have hYm : uNode (F.step N) j1 ∈ Set.Icc 0 (C.uc μ - C.η / 2) := ⟨hu0, by linarith⟩
  have hY : |C.Y μ X (uNode (F.step N) j1)| ≤ CY := by
    rw [abs_of_pos (C.Y_forb μ hμ X hX _ hYm).2]
    exact (hYle μ hμ X hX _ hYm).trans (le_max_left _ _)
  have hL : ((j1 : ℝ) + 1 / 2) * F.step N ≤ F.L := by
    have := (C.ucη_in μ hμ).2; unfold uNode at hu1; linarith
  -- the row after the overlap: `x = u_{j_1+1} - u_c` with `eta/4 <= |x| <= 2 eta`
  have hx : uNode (F.step N) (j1 + 1) = uNode (F.step N) j1 + F.step N := by unfold uNode; push_cast; ring
  have hxlo : C.η / 4 ≤ |uNode (F.step N) (j1 + 1) - C.uc μ| := by
    rw [abs_of_neg (by linarith)]; linarith
  have hxhi : |uNode (F.step N) (j1 + 1) - C.uc μ| ≤ 2 * C.η := by
    rw [abs_of_neg (by linarith)]; linarith
  have hZ := C.Zq_lb hμ hX hhH hxlo hxhi
  have hZa := C.Z2_add_a μ X N (j1 + 1)
  have hZb : C.cz1 / (8 * F.step N) ≤ C.Zof μ X N (j1 + 1) ^ 2 / 4 + C.aOf μ X N := by
    rw [hZa, div_le_div_iff₀ (by positivity) hh]
    nlinarith
  exact hrat hh hh1 hj1.le hL hY hZb

/-- `phi^{(alpha)}_p(k) = A w_0 + h B w_1` when the model pair at row `k` is `(w_0, w_1)`. -/
lemma _root_.FormalResearch.JacobiEigenvectors.Charts.LadderData.phi_of_wf (D : LadderData) {h w0 w1 : ℝ} {α : Fin 2} {p : ℕ}
    {k : ℤ} (hw : D.wf p α (uNode h k) h = ![w0, w1]) :
    D.phi h α p k = D.AA p (uNode h k) h * w0 + h * D.BB p (uNode h k) h * w1 := by
  unfold LadderData.phi ladderSeq
  change dot (vrow (D.AA p) (D.BB p) (uNode h k) h) (D.wf p α (uNode h k) h) = _
  rw [hw]
  simp only [dot, vrow, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `|zeta(x; alpha)| <= c_Z delta_0 + 2 eta d_+` on the collar `|x| <= 2 eta` (`zeta_alpha`, `zeta_deriv`). -/
lemma zeta_abs_le {μ : Par} (hμ : μ ∈ P) {α : ℝ} (hα : |α| ≤ C.δ0) {x : ℝ} (hx : |x| ≤ 2 * C.η) :
    |C.zeta μ α x| ≤ C.cZ * C.δ0 + 2 * C.η * C.dp := by
  obtain ⟨-, hη, hdm, hdmp, -, -, -, hcZ⟩ := C.consts_pos
  have h0 : |C.zeta μ α 0| ≤ C.cZ * C.δ0 := (C.zeta_alpha μ hμ α hα).trans (mul_le_mul_of_nonneg_left hα hcZ.le)
  have hx' := abs_le.mp hx
  have hdp : 0 < C.dp := hdm.trans_le hdmp
  rcases le_total 0 x with hx0 | hx0
  · obtain ⟨h1, h2⟩ := C.zeta_mvt hμ hα (x1 := 0) (x2 := x) (by linarith) hx0 hx'.2
    have : |C.zeta μ α x - C.zeta μ α 0| ≤ 2 * C.η * C.dp := by
      rw [abs_le]; constructor <;> nlinarith
    calc |C.zeta μ α x| = |(C.zeta μ α x - C.zeta μ α 0) + C.zeta μ α 0| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by linarith)
  · obtain ⟨h1, h2⟩ := C.zeta_mvt hμ hα (x1 := x) (x2 := 0) hx'.1 hx0 (by linarith)
    have : |C.zeta μ α 0 - C.zeta μ α x| ≤ 2 * C.η * C.dp := by
      rw [abs_le]; constructor <;> nlinarith
    calc |C.zeta μ α x| = |C.zeta μ α 0 - (C.zeta μ α 0 - C.zeta μ α x)| := by ring_nf
      _ ≤ _ := (abs_sub _ _).trans (by linarith)

/-- `|a| <= C_a / h` with `C_a = C_mu (1 + q/2)` (`a = -mu~/h`, `muTilde_abs_le`). -/
lemma aOf_abs_le {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : |X - F.bandHi μ| ≤ C.δ0) {N : ℕ} (hh1 : F.step N ≤ 1) :
    |C.aOf μ X N| ≤ C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)) / F.step N := by
  have hh := step_pos F N
  rw [C.aOf_eq, abs_mul, abs_neg, abs_of_pos (one_div_pos.mpr hh), one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right (C.muTilde_abs_le hμ hX hh1) hh.le

/-- `zeta` does not vanish away from the fold core: `zeta(x)^2 >= c_{z1}` for `eta/4 <= |x|` on the lattice interval. -/
lemma zeta_ne_zero {μ : Par} (hμ : μ ∈ P) {α : ℝ} (hα : |α| ≤ C.δ0) {x : ℝ} (hx1 : C.η / 4 ≤ |x|)
    (h0 : 0 ≤ C.uc μ + x) (hL : C.uc μ + x ≤ F.L) : C.zeta μ α x ≠ 0 := by
  have hz : 4 * max (C.muS 0 μ α) 0 + C.cz1 ≤ C.zeta μ α x ^ 2 := by
    rcases le_total |x| (2 * C.η) with hx2 | hx2
    · exact C.zeta_far μ hμ α hα x hx2 hx1
    · exact C.zeta_far_out μ hμ α hα x hx2 h0 hL
  have := C.consts_pos2.2
  have : 0 ≤ max (C.muS 0 μ α) 0 := le_max_right _ _
  intro he; rw [he] at hz; nlinarith

/-- The rows of the chain lie on the lattice: `N_R <= N`. -/
lemma NR_le {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : |X - F.bandHi μ| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N) :
    (C.chain μ X N).NR ≤ (N : ℤ) := by
  have hu := (C.shape μ hμ X hX N hN).2.2.2.2.2.2.1
  have hL := (C.ucη_in μ hμ).2
  have hm := step_mul F N
  have hh := step_pos F N
  have : ((C.chain μ X N).NR : ℝ) < (N : ℝ) + 1 := by
    unfold uNode at hu
    by_contra! hc
    nlinarith
  have : (C.chain μ X N).NR < (N : ℤ) + 1 := by exact_mod_cast this
  omega

/-- **The PC-row fields `lb_pc`, `ratio2`, `grow3`** of the soft chart, from `corr_PC`, `AA2_ratio`, the coordinate fields of `zeta` and
the PC parameter bounds, by `soft_lb_pc_of_corr`, `soft_ratio2_of_corr`, `soft_grow3_of_corr`. -/
theorem exists_pc : ∃ N1 : ℕ, ∃ clb C2 cgr Cgr : ℝ, 0 < clb ∧ 0 ≤ C2 ∧ 0 < cgr ∧ 0 ≤ Cgr ∧
    (∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ C.δ0 → ∀ N, max C.N0 N1 ≤ N →
      aPC (fun r α' => C.muS r μ α') q (F.step N) (F.bandHi μ - X) ≤ ((q / 2 : ℕ) : ℝ) * C.Cmu + 1 →
      ∀ k ∈ Finset.Icc ((C.chain μ X N).jj 1 + 1) ((C.chain μ X N).jj 2),
        C.zeta μ (F.bandHi μ - X) (uNode (F.step N) k - C.uc μ) / Real.sqrt (F.step N) <
          -(2 * Real.sqrt (max (-(aPC (fun r α' => C.muS r μ α') q (F.step N) (F.bandHi μ - X))) 0) +
            (1 + max (-(aPC (fun r α' => C.muS r μ α') q (F.step N) (F.bandHi μ - X))) 0) ^ (-(1 : ℝ) / 6)) →
        clb * ((C.chain μ X N).W k * (C.chain μ X N).M k) ≤ |(C.chain μ X N).phi (F.step N) 0 2 k|) ∧
    (∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ C.δ0 → ∀ N, max C.N0 N1 ≤ N →
      |(C.chain μ X N).phi (F.step N) 1 2 ((C.chain μ X N).jj 1 + 1)| ≤
        (1 + C2 * F.step N) * |(C.chain μ X N).phi (F.step N) 1 2 ((C.chain μ X N).jj 1)|) ∧
    (∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ C.δ0 → ∀ N, max C.N0 N1 ≤ N →
      aPC (fun r α' => C.muS r μ α') q (F.step N) (F.bandHi μ - X) ≤ ((q / 2 : ℕ) : ℝ) * C.Cmu + 1 →
      ∀ k : ℤ, (C.chain μ X N).jj 2 + 1 ≤ k → k + 1 ≤ (C.chain μ X N).NR → C.uc μ + C.η / 4 ≤ uNode (F.step N) k →
        cgr * ((C.chain μ X N).W k * (C.chain μ X N).M k) ≤ (C.chain μ X N).phi (F.step N) 0 3 k ∧
        cgr * ((C.chain μ X N).W (k + 1) * (C.chain μ X N).M (k + 1)) ≤ (C.chain μ X N).phi (F.step N) 0 3 (k + 1) ∧
        (C.chain μ X N).phi (F.step N) 0 3 k ≤ (1 + Cgr * F.step N) * (C.chain μ X N).phi (F.step N) 0 3 (k + 1)) := by
  obtain ⟨hδ0, hη, hdm, hdmp, -, -, -, hcZ⟩ := C.consts_pos
  obtain ⟨hCmu, hcz1⟩ := C.consts_pos2
  obtain ⟨hgm, hCBc⟩ := C.consts_pos4
  obtain ⟨CAl, hCAl, hAr⟩ := C.AA2_ratio
  have hdp : 0 < C.dp := hdm.trans_le hdmp
  set CZ := C.cZ * C.δ0 + 2 * C.η * C.dp
  have hCZ : 0 < CZ := by positivity
  set Ca := C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)) with hCadef
  have hCa : 0 ≤ Ca := by positivity
  set aHi := ((q / 2 : ℕ) : ℝ) * C.Cmu + 1
  have haHi : 0 ≤ aHi := by positivity
  obtain ⟨clb, h0a, hclb, h0a_pos, hlb⟩ := soft_lb_pc_of_corr hgm hCBc hCZ.le hCa haHi
  obtain ⟨C2, h0b, hC2, h0b_pos, hr2⟩ := soft_ratio2_of_corr hgm hCBc hCAl hcz1 hCZ hCa
  obtain ⟨cgr, Cgr, h0c, hcgr, hCgr, h0c_pos, hg3⟩ := soft_grow3_of_corr hgm hCBc hCAl hcz1 hCZ hCa haHi
  obtain ⟨N1, hN1⟩ := exists_N_step_le F (lt_min C.softH1_pos (lt_min h0a_pos (lt_min h0b_pos h0c_pos)))
  refine ⟨N1, clb, C2, cgr, Cgr, hclb, hC2, hcgr, hCgr, ?_⟩
  -- common facts
  have hstep : ∀ N, max C.N0 N1 ≤ N → C.N0 ≤ N ∧ 0 < F.step N ∧ F.step N ≤ C.softH1 ∧ F.step N ≤ 1 ∧
      F.step N ≤ C.η / 2 ∧ F.step N ≤ h0a ∧ F.step N ≤ h0b ∧ F.step N ≤ h0c := by
    intro N hN
    have h := hN1 N ((le_max_right _ _).trans hN)
    simp only [le_min_iff] at h
    exact ⟨(le_max_left _ _).trans hN, step_pos F N, h.1, h.1.trans C.softH1_le_one,
      h.1.trans C.softH1_le_eta, h.2.1, h.2.2.1, h.2.2.2⟩
  have hZlo : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ C.δ0 → ∀ N, 0 < F.step N → ∀ x, |x| ≤ 2 * C.η →
      -(CZ / Real.sqrt (F.step N)) ≤ C.zeta μ (F.bandHi μ - X) x / Real.sqrt (F.step N) ∧
      C.zeta μ (F.bandHi μ - X) x / Real.sqrt (F.step N) ≤ CZ / Real.sqrt (F.step N) := by
    intro μ hμ X hX N hh x hx
    have := abs_le.mp (C.zeta_abs_le hμ (C.abs_alpha_le hX) hx)
    have hs := Real.sqrt_pos.mpr hh
    rw [← neg_div]
    exact ⟨div_le_div_of_nonneg_right this.1 hs.le, div_le_div_of_nonneg_right this.2 hs.le⟩
  have hmono : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ C.δ0 → ∀ N, 0 < F.step N → ∀ x1 x2, -(2 * C.η) ≤ x1 → x1 ≤ x2 →
      x2 ≤ 2 * C.η → C.zeta μ (F.bandHi μ - X) x1 / Real.sqrt (F.step N) ≤
        C.zeta μ (F.bandHi μ - X) x2 / Real.sqrt (F.step N) := by
    intro μ hμ X hX N hh x1 x2 h1 h12 h2
    have := (C.zeta_mvt hμ (C.abs_alpha_le hX) h1 h12 h2).1
    exact div_le_div_of_nonneg_right (by nlinarith) (Real.sqrt_nonneg _)
  have haC : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ C.δ0 → ∀ N, F.step N ≤ 1 →
      (C.aOf μ X N ≤ 0 → -C.aOf μ X N ≤ Ca / F.step N) ∧ (0 < C.aOf μ X N → C.aOf μ X N ≤ Ca / F.step N) := by
    intro μ hμ X hX N hh1
    have hab := C.aOf_abs_le hμ hX hh1
    rw [← hCadef] at hab
    exact ⟨fun _ => neg_le.mpr (abs_le.mp hab).1, fun _ => (abs_le.mp hab).2⟩
  have hrowu : ∀ (N : ℕ) (k : ℤ), uNode (F.step N) (k + 1) = uNode (F.step N) k + F.step N := by
    intro N k; unfold uNode; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · -- lb_pc
    intro μ hμ X hX N hN ha k hk hZk
    obtain ⟨hN0, hh, hhH, hh1, hhη, hha, -, -⟩ := hstep N hN
    obtain ⟨hj1, hj12, hj2N⟩ := C.jj_order hμ hX hN0
    obtain ⟨-, -, hu1, hu1', -⟩ := C.shape μ hμ X hX N hN0
    obtain ⟨-, hj2le, hsw, -⟩ := C.switch_in μ hμ X hX N hN0
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hlo : uNode (F.step N) ((C.chain μ X N).jj 1 + 1) ≤ uNode (F.step N) k :=
      SoftEdgeChart.uNode_mono_le hh.le hk1
    have hhi : uNode (F.step N) k ≤ uNode (F.step N) ((C.chain μ X N).jj 2) :=
      SoftEdgeChart.uNode_mono_le hh.le hk2
    have hx : |uNode (F.step N) k - C.uc μ| ≤ 2 * C.η := by
      have := abs_le.mp hsw; rw [abs_le]; constructor <;> linarith
    obtain ⟨hgA, hgB⟩ := C.corr_PC μ hμ X hX N hN0 k (by omega) (by omega) hx
    have hmem2 : k ∈ Finset.Icc ((C.chain μ X N).jj 1) ((C.chain μ X N).NR + 1) :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [LadderData.phi_of_wf _ (C.wf2_eq μ hμ X hX N hN0 k hmem2 0),
      C.W2_def μ hμ X hX N hN0 k hk, C.M2_def μ hμ X hX N hN0 k (Finset.mem_Icc.mpr ⟨hk1, by omega⟩)]
    have hl := hlb (h := F.step N) (A := (C.chain μ X N).AA 2 (uNode (F.step N) k) (F.step N))
      (B := (C.chain μ X N).BB 2 (uNode (F.step N) k) (F.step N)) hh hha ha
      (haC μ hμ X hX N hh1).1
      (hZlo μ hμ X hX N hh _ hx).1 hZk hgA hgB
    simp only [minusModelPhi0] at hl ⊢
    exact hl
  · -- ratio2
    intro μ hμ X hX N hN
    obtain ⟨hN0, hh, hhH, hh1, hhη, -, hhb, -⟩ := hstep N hN
    obtain ⟨hj1, hj12, hj2N⟩ := C.jj_order hμ hX hN0
    obtain ⟨-, -, hu1, hu1', -⟩ := C.shape μ hμ X hX N hN0
    obtain ⟨-, hj2le, -, -⟩ := C.switch_in μ hμ X hX N hN0
    have hNR := C.NR_le hμ hX hN0
    set j1 := (C.chain μ X N).jj 1
    have hr := hrowu N j1
    have hx1 : |uNode (F.step N) j1 - C.uc μ| ≤ 2 * C.η := by rw [abs_le]; constructor <;> linarith
    have hx2 : |uNode (F.step N) (j1 + 1) - C.uc μ| ≤ 2 * C.η := by rw [abs_le]; constructor <;> linarith
    have hx2' : C.η / 4 ≤ |uNode (F.step N) (j1 + 1) - C.uc μ| := by
      rw [abs_of_neg (by linarith)]; linarith
    obtain ⟨hgA1, hgB1⟩ := C.corr_PC μ hμ X hX N hN0 j1 hj1.le (by omega) hx1
    obtain ⟨hgA2, hgB2⟩ := C.corr_PC μ hμ X hX N hN0 (j1 + 1) (by omega) (by omega) hx2
    have hA21 := (hAr μ hμ X hX N hN0 j1 hj1.le (by omega) hx1 hx2).1
    have hm1 : j1 ∈ Finset.Icc j1 ((C.chain μ X N).NR + 1) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have hm2 : j1 + 1 ∈ Finset.Icc j1 ((C.chain μ X N).NR + 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [LadderData.phi_of_wf _ (C.wf2_eq μ hμ X hX N hN0 j1 hm1 1),
      LadderData.phi_of_wf _ (C.wf2_eq μ hμ X hX N hN0 (j1 + 1) hm2 1)]
    have hlu := (C.ucη_in μ hμ)
    have hZ2neg : C.zeta μ (F.bandHi μ - X) (uNode (F.step N) (j1 + 1) - C.uc μ) / Real.sqrt (F.step N) < 0 := by
      have hs := (C.zeta_sign_out μ hμ _ (C.abs_alpha_le hX) _ hx2' (by linarith) (by linarith)).1 (by linarith)
      have hne := C.zeta_ne_zero hμ (C.abs_alpha_le hX) hx2' (by linarith) (by linarith)
      exact div_neg_of_neg_of_pos (lt_of_le_of_ne hs hne) (Real.sqrt_pos.mpr hh)
    have hZb : C.cz1 / (8 * F.step N) ≤ C.Zof μ X N (j1 + 1) ^ 2 / 4 + C.aOf μ X N := by
      rw [C.Z2_add_a μ X N (j1 + 1), div_le_div_iff₀ (by positivity) hh]
      have := C.Zq_lb hμ hX hhH hx2' hx2
      nlinarith
    have hl := hr2 (h := F.step N) hh hhb (haC μ hμ X hX N hh1).1
      (haC μ hμ X hX N hh1).2 (hZlo μ hμ X hX N hh _ hx1).1
      (hmono μ hμ X hX N hh _ _ (abs_le.mp hx1).1 (by linarith) (abs_le.mp hx2).2) hZ2neg hZb
      hgA1 hgA2 hgB1 hgB2 hA21
    simp only [minusModelPhi1, SoftEdgeCore.aOf] at hl ⊢
    exact hl
  · -- grow3
    intro μ hμ X hX N hN ha k hk2 hkNR hku
    obtain ⟨hN0, hh, hhH, hh1, hhη, -, -, hhc⟩ := hstep N hN
    obtain ⟨hj1, hj12, hj2N⟩ := C.jj_order hμ hX hN0
    obtain ⟨-, -, -, -, -, -, huNR, -⟩ := C.shape μ hμ X hX N hN0
    have hNR := C.NR_le hμ hX hN0
    have hr := hrowu N k
    have hk1u : uNode (F.step N) (k + 1) ≤ uNode (F.step N) (C.chain μ X N).NR :=
      SoftEdgeChart.uNode_mono_le hh.le hkNR
    have hx1 : |uNode (F.step N) k - C.uc μ| ≤ 2 * C.η := by rw [abs_le]; constructor <;> linarith
    have hx2 : |uNode (F.step N) (k + 1) - C.uc μ| ≤ 2 * C.η := by rw [abs_le]; constructor <;> linarith
    have hx1' : C.η / 4 ≤ |uNode (F.step N) k - C.uc μ| := by rw [abs_of_pos (by linarith)]; linarith
    have hlu := C.ucη_in μ hμ
    obtain ⟨hgA1, hgB1⟩ := C.corr_PC μ hμ X hX N hN0 k (by omega) (by omega) hx1
    obtain ⟨hgA2, hgB2⟩ := C.corr_PC μ hμ X hX N hN0 (k + 1) (by omega) (by omega) hx2
    have hA12 := (hAr μ hμ X hX N hN0 k (by omega) (by omega) hx1 hx2).2
    have hm1 : k ∈ Finset.Icc ((C.chain μ X N).jj 2) ((C.chain μ X N).NR + 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hm2 : k + 1 ∈ Finset.Icc ((C.chain μ X N).jj 2) ((C.chain μ X N).NR + 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [LadderData.phi_of_wf _ (C.wf3_eq μ hμ X hX N hN0 k hm1 0),
      LadderData.phi_of_wf _ (C.wf3_eq μ hμ X hX N hN0 (k + 1) hm2 0),
      C.W3_def μ hμ X hX N hN0 k (Finset.mem_Icc.mpr ⟨hk2, by omega⟩),
      C.W3_def μ hμ X hX N hN0 (k + 1) (Finset.mem_Icc.mpr ⟨by omega, hkNR⟩),
      C.M2_def μ hμ X hX N hN0 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩),
      C.M2_def μ hμ X hX N hN0 (k + 1) (Finset.mem_Icc.mpr ⟨by omega, hkNR⟩)]
    obtain ⟨-, -, -, -, -, -, -, -, hAA3, hBB3⟩ := C.shared_PC μ hμ X hX N hN0
    rw [hAA3, hBB3]
    have hZ1pos : 0 < C.zeta μ (F.bandHi μ - X) (uNode (F.step N) k - C.uc μ) / Real.sqrt (F.step N) := by
      have hs := (C.zeta_sign_out μ hμ _ (C.abs_alpha_le hX) _ hx1' (by linarith) (by linarith)).2 (by linarith)
      have hne := C.zeta_ne_zero hμ (C.abs_alpha_le hX) hx1' (by linarith) (by linarith)
      exact div_pos (lt_of_le_of_ne hs (Ne.symm hne)) (Real.sqrt_pos.mpr hh)
    have hZb : C.cz1 / (8 * F.step N) ≤ C.Zof μ X N k ^ 2 / 4 + C.aOf μ X N := by
      rw [C.Z2_add_a μ X N k, div_le_div_iff₀ (by positivity) hh]
      have := C.Zq_lb hμ hX hhH hx1' hx1
      nlinarith
    obtain ⟨g1, g2, g3⟩ := hg3 (h := F.step N) hh hhc ha (haC μ hμ X hX N hh1).1 hZ1pos
      (hmono μ hμ X hX N hh _ _ (abs_le.mp hx1).1 (by linarith) (abs_le.mp hx2).2) (hZlo μ hμ X hX N hh _ hx2).2 hZb
      hgA1 hgA2 hgB1 hgB2 hA12
    simp only [softModelPhi] at g1 g2 g3
    refine ⟨?_, ?_, g3⟩
    · rw [← mul_assoc]; exact g1
    · rw [← mul_assoc]; exact g2

/-- The core with `N0` raised to `max N0 N1` (every field holds for the larger threshold). -/
def raiseN0 {U V : ℝ → ℝ → ℝ} (C : SoftEdgeCore F P m q U V Lm) (N1 : ℕ) : SoftEdgeCore F P m q U V Lm :=
  have hN : ∀ N, max C.N0 N1 ≤ N → C.N0 ≤ N := fun _ h => (le_max_left _ _).trans h
  { C with
    N0 := max C.N0 N1
    shapeW := fun μ hμ X hX N h => C.shapeW μ hμ X hX N (hN N h)
    validW := fun μ hμ X hX N h => C.validW μ hμ X hX N (hN N h)
    A_bondW := fun μ hμ X hX N h => C.A_bondW μ hμ X hX N (hN N h)
    Q_diagW := fun μ hμ X hX N h => C.Q_diagW μ hμ X hX N (hN N h)
    dd_sqrtW := fun μ hμ X hX N h => C.dd_sqrtW μ hμ X hX N (hN N h)
    omega_sqrtW := fun μ hμ X hX N h => C.omega_sqrtW μ hμ X hX N (hN N h)
    wfW_eq := fun μ hμ X hX N h => C.wfW_eq μ hμ X hX N (hN N h)
    theta_leW := fun μ hμ X hX N h => C.theta_leW μ hμ X hX N (hN N h)
    W_defW := fun μ hμ X hX N h => C.W_defW μ hμ X hX N (hN N h)
    M_defW := fun μ hμ X hX N h => C.M_defW μ hμ X hX N (hN N h)
    patch1_eq := fun μ hμ X hX N h => C.patch1_eq μ hμ X hX N (hN N h)
    shape := fun μ hμ X hX N h => C.shape μ hμ X hX N (hN N h)
    switch_in := fun μ hμ X hX N h => C.switch_in μ hμ X hX N (hN N h)
    valid := fun μ hμ X hX N h => C.valid μ hμ X hX N (hN N h)
    A_bond := fun μ hμ X hX N h => C.A_bond μ hμ X hX N (hN N h)
    Q_diag := fun μ hμ X hX N h => C.Q_diag μ hμ X hX N (hN N h)
    shared_PC := fun μ hμ X hX N h => C.shared_PC μ hμ X hX N (hN N h)
    d2_PC := fun μ hμ X hX N h => C.d2_PC μ hμ X hX N (hN N h)
    wf2_eq := fun μ hμ X hX N h => C.wf2_eq μ hμ X hX N (hN N h)
    wf3_eq := fun μ hμ X hX N h => C.wf3_eq μ hμ X hX N (hN N h)
    W1_def := fun μ hμ X hX N h => C.W1_def μ hμ X hX N (hN N h)
    M1_def := fun μ hμ X hX N h => C.M1_def μ hμ X hX N (hN N h)
    W2_def := fun μ hμ X hX N h => C.W2_def μ hμ X hX N (hN N h)
    W3_def := fun μ hμ X hX N h => C.W3_def μ hμ X hX N (hN N h)
    M2_def := fun μ hμ X hX N h => C.M2_def μ hμ X hX N (hN N h)
    theta_le := fun μ hμ X hX N h => C.theta_le μ hμ X hX N (hN N h)
    corr_PC := fun μ hμ X hX N h => C.corr_PC μ hμ X hX N (hN N h)
    lamL_cont := fun μ hμ N h => C.lamL_cont μ hμ N (hN N h)
    corr_leadW := by
      obtain ⟨cg, Cg, hcg, g0, h⟩ := C.corr_leadW
      exact ⟨cg, Cg, hcg, g0, fun μ hμ X hX N hN' => h μ hμ X hX N (hN N hN')⟩
    AA2_ratio := by
      obtain ⟨CAl, hCAl, h⟩ := C.AA2_ratio
      exact ⟨CAl, hCAl, fun μ hμ X hX N hN' => h μ hμ X hX N (hN N hN')⟩ }

/-- The standing assumptions on the family that the bond fields `bondA_le`, `grow_gap` of the soft chart need: the regularity
`CoreReg` (`e >= 1`), a uniform lower bound `g` of `G_0` (H1), and the geometry of `lem:tha-geom` (d) for the chart's fold `u_c` and collar
width `eta` on a window `delta_s >= 2 delta_0` (the paper fixes `eta`, then `delta_0`). -/
structure FamilyInputs {U V : ℝ → ℝ → ℝ} (C : SoftEdgeCore F P m q U V Lm) : Prop where
  reg : ∃ e : ℕ, 1 ≤ e ∧ CoreReg F P e
  G_lb : ∃ g : ℝ, 0 < g ∧ ∀ μ ∈ P, ∀ u ∈ Set.Icc 0 F.L, g ≤ F.G 0 μ u
  geom : ∃ δs : ℝ, 0 < δs ∧ C.δ0 ≤ δs / 2 ∧ ∀ μ ∈ P, ∀ δ0' : ℝ, 0 < δ0' → δ0' ≤ δs → ∀ X : ℝ, |X - F.bandHi μ| ≤ δ0' →
    ∀ u ∈ Set.Icc 0 F.L, C.η / 4 ≤ |u - C.uc μ| →
      Tfun F.L (F.G 0 μ) (F.B 0 μ) X u < 0 ∧ 0 < X - F.B 0 μ u

/-- **`bondA_le`, `grow_gap`** from the standing assumptions (`soft_bondA_le`, `soft_grow_gap`). -/
theorem exists_bonds {U V : ℝ → ℝ → ℝ} (C : SoftEdgeCore F P m q U V Lm) (hF : C.FamilyInputs) :
    ∃ N1 : ℕ, ∃ CA nu1 : ℝ, 0 ≤ CA ∧ 0 < nu1 ∧
      (∀ μ ∈ P, ∀ N, max C.N0 N1 ≤ N → ∀ k : ℤ, F.bondA μ N k ≤ CA) ∧
      (∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ C.δ0 → ∀ N, max C.N0 N1 ≤ N → ∀ n : ℤ, 0 ≤ n →
        uNode (F.step N) n ≤ C.uc μ - C.η / 4 → F.bondA μ N n + F.bondA μ N (n - 1) + nu1 ≤ F.diagQ μ N X n) := by
  obtain ⟨e, he, hR⟩ := hF.reg
  obtain ⟨g, hg, hG⟩ := hF.G_lb
  obtain ⟨δs, hδs, hδ0, hgeom⟩ := hF.geom
  obtain ⟨CA, NA, hCA, hA⟩ := soft_bondA_le F hR
  obtain ⟨nu1, NG, hnu, hG'⟩ := soft_grow_gap F hR he subset_rfl hg hG C.consts_pos.2.1 hδs C.consts_pos.1 hδ0
    (fun μ hμ => C.ucη_in μ hμ) hgeom
  refine ⟨max NA NG, CA, nu1, hCA.le, hnu, ?_, ?_⟩
  · intro μ hμ N hN k
    exact hA μ hμ N ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) k
  · intro μ hμ X hX N hN n hn hu
    exact hG' μ hμ X hX N ((le_max_right _ _).trans ((le_max_right _ _).trans hN)) n hn hu

/-- **Every soft-edge chart field is derived from the core** (model pair `pcU, pcV`, standing assumptions `FamilyInputs`): a chart whose
core is `C` with `N0` raised. -/
theorem exists_chart (hF : C.FamilyInputs) :
    ∃ N1 : ℕ, ∀ N2 : ℕ, N1 ≤ N2 → ∃ Ch : SoftEdgeChart F P m q pcU pcV Lm, Ch.toSoftEdgeCore = C.raiseN0 N2 := by
  obtain ⟨Na, c3, hc3, hseed, hcoll⟩ := C.exists_weber
  obtain ⟨Nb, CM, hCM, hratM⟩ := C.exists_ratioM
  obtain ⟨Nc, clb, C2, cgr, Cgr, hclb, hC2, hcgr, hCgr, hlb, hr2, hg3⟩ := C.exists_pc
  obtain ⟨Nd, CA, nu1, hCA, hnu, hbA, hgg⟩ := C.exists_bonds hF
  refine ⟨max (max Na Nb) (max Nc Nd), fun N2 hN2 => ?_⟩
  have hle : ∀ {N : ℕ} {Nx : ℕ}, Nx ≤ N2 → max C.N0 N2 ≤ N → max C.N0 Nx ≤ N :=
    fun hx hN => (max_le_max le_rfl hx).trans hN
  have ha : Na ≤ N2 := ((le_max_left _ _).trans (le_max_left _ _)).trans hN2
  have hb : Nb ≤ N2 := ((le_max_right _ _).trans (le_max_left _ _)).trans hN2
  have hc : Nc ≤ N2 := ((le_max_left _ _).trans (le_max_right _ _)).trans hN2
  have hd : Nd ≤ N2 := ((le_max_right _ _).trans (le_max_right _ _)).trans hN2
  have hN0 : ∀ {N : ℕ}, max C.N0 N2 ≤ N → C.N0 ≤ N := fun hN => (le_max_left _ _).trans hN
  -- `W M >= 0` on the Weber rows (engine positivity of `chainW`)
  have hWM : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ C.δ0 → ∀ N, C.N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (C.chainW μ X N).NR,
      0 ≤ (C.chainW μ X N).W k * (C.chainW μ X N).M k := fun μ hμ X hX N hN k hk =>
    mul_nonneg ((C.validW μ hμ X hX N hN).W_pos k hk).le ((C.validW μ hμ X hX N hN).M_pos k hk).le
  refine ⟨{ toSoftEdgeCore := C.raiseN0 N2
            CA := CA, nu1 := nu1, c3W := c3, C2 := C2, CM := CM
            consts_pos3 := ⟨hCA, hnu, hc3, hC2, hCM⟩
            bondA_le := fun μ hμ N hN => hbA μ hμ N (hle hd hN)
            grow_gap := fun μ hμ X hX N hN => hgg μ hμ X hX N (hle hd hN)
            seed_posW := fun μ hμ X hX N hN => hseed μ hμ X hX N (hle ha hN)
            collar_lbW := fun μ hμ X hX N hN k hk _ => hcoll μ hμ X hX N (hle ha hN) k hk
            ratio2 := fun μ hμ X hX N hN => hr2 μ hμ X hX N (hle hc hN)
            ratioM := fun μ hμ X hX N hN => hratM μ hμ X hX N (hle hb hN)
            clb := min c3 clb
            clb_pos := lt_min hc3 hclb
            lb_weber := fun μ hμ X hX N hN k hk => by
              have h1 := hcoll μ hμ X hX N (hle ha hN) k hk
              have h2 := hWM μ hμ X hX N (hN0 hN) k hk
              calc min c3 clb * ((C.chainW μ X N).W k * (C.chainW μ X N).M k)
                  ≤ c3 * ((C.chainW μ X N).W k * (C.chainW μ X N).M k) :=
                    mul_le_mul_of_nonneg_right (min_le_left _ _) h2
                _ ≤ _ := by rw [← mul_assoc]; exact h1
            lb_pc := fun μ hμ X hX N hN ha' k hk hZ => by
              have h1 := hlb μ hμ X hX N (hle hc hN) ha' k hk hZ
              have hv := C.valid μ hμ X hX N (hN0 hN)
              obtain ⟨hj1, hj12, hj2N⟩ := C.jj_order hμ hX (hN0 hN)
              change k ∈ Finset.Icc ((C.chain μ X N).jj 1 + 1) ((C.chain μ X N).jj 2) at hk
              have hk' : k ∈ Finset.Icc (0 : ℤ) (C.chain μ X N).NR := by
                simp only [Finset.mem_Icc] at hk ⊢; omega
              have h2 : 0 ≤ (C.chain μ X N).W k * (C.chain μ X N).M k :=
                mul_nonneg (hv.W_pos k hk').le (hv.M_pos k hk').le
              exact (mul_le_mul_of_nonneg_right (min_le_right _ _) h2).trans h1
            cgr := cgr, Cgr := Cgr
            consts_pos6 := ⟨hcgr, hCgr⟩
            grow3 := fun μ hμ X hX N hN => hg3 μ hμ X hX N (hle hc hN) }, rfl⟩

end SoftEdgeCore

/-- The threshold from which the soft-edge chart of a core exists: for every `N2` above it, `SoftEdgeChart.ofCore C hF N2` is the chart
whose core is `C` with `N0` raised to `max C.N0 N2`. -/
def SoftEdgeCore.chartN0 {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {m q : ℕ} {Lm : ℝ → ℝ}
    (C : SoftEdgeCore F P m q pcU pcV Lm) (hF : C.FamilyInputs) : ℕ :=
  Classical.choose (C.exists_chart hF)

/-- **The soft-edge chart of a core** (model pair `pcU, pcV`), given the standing assumptions `FamilyInputs`, at the threshold `N2 >= chartN0`:
its core is the given core with `N0` raised to `max N0 N2` (`SoftEdgeChart.ofCore_core`).  The explicit `N2` lets a mirror pair of charts
be built with the same `N0`. -/
def SoftEdgeChart.ofCore {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {m q : ℕ} {Lm : ℝ → ℝ}
    (C : SoftEdgeCore F P m q pcU pcV Lm) (hF : C.FamilyInputs) (N2 : ℕ) (hN2 : C.chartN0 hF ≤ N2) :
    SoftEdgeChart F P m q pcU pcV Lm :=
  Classical.choose (Classical.choose_spec (C.exists_chart hF) N2 hN2)

/-- The chart of a core has the core's coordinates, ladders and corrector rows; only `N0` is raised. -/
lemma SoftEdgeChart.ofCore_core {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {m q : ℕ}
    {Lm : ℝ → ℝ} (C : SoftEdgeCore F P m q pcU pcV Lm) (hF : C.FamilyInputs) (N2 : ℕ) (hN2 : C.chartN0 hF ≤ N2) :
    (SoftEdgeChart.ofCore C hF N2 hN2).toSoftEdgeCore = C.raiseN0 N2 :=
  Classical.choose_spec (Classical.choose_spec (C.exists_chart hF) N2 hN2)

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.SoftEdgeCore.exists_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.SoftEdgeCore.exists_chart

end FormalResearch.JacobiEigenvectors.Charts
