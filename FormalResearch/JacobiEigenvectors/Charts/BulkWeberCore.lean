module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.SoftBounds

/-!
# Paper J, charts: the core of the bulk Weber chart

`BulkWeberChart F P Jlo Jhi m U V` extends `BulkWeberCore` (`Charts/BulkWeber.lean`) by the constants `cM, CM, c3, Csum` and the
bounds `W_osc`, `M_osc` (`lem:cha-weber-env` (2)), `theta_le` (`lem:cha-weber-env` (3)), `seed_pos` and `collar_lb` (`lem:cha-W0` plus
the smallness of the corrector term).  For the model pair `pcU, pcV` these follow from the core: `BulkWeberChart.ofCore` builds the
chart from a core, with `N0` raised so that `h = L/(N+1)` is below the thresholds of the derivations.  The inputs are the Layer-4
lemmas of `Charts/SoftBounds.lean`: `bulk_W_osc_M_osc`, `bulk_theta_le`, `weber_seed_pos_of_corr`, `weber_collar_lb_of_corr`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Engine
open FormalResearch.JacobiEigenvectors.TheoremA

namespace BulkWeberCore

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {Jlo Jhi : ℝ} {m : ℕ}
  (C : BulkWeberCore F P Jlo Jhi m pcU pcV)

/-- The core with `N0` raised to `max N0 N1` (every field holds for the larger threshold). -/
def raiseN0 {U V : ℝ → ℝ → ℝ} (C : BulkWeberCore F P Jlo Jhi m U V) (N1 : ℕ) : BulkWeberCore F P Jlo Jhi m U V :=
  have hN : ∀ N, max C.N0 N1 ≤ N → C.N0 ≤ N := fun _ h => (le_max_left _ _).trans h
  { C with
    N0 := max C.N0 N1
    shape := fun μ hμ X hX N h => C.shape μ hμ X hX N (hN N h)
    valid := fun μ hμ X hX N h => C.valid μ hμ X hX N (hN N h)
    A_bond := fun μ hμ X hX N h => C.A_bond μ hμ X hX N (hN N h)
    Q_diag := fun μ hμ X hX N h => C.Q_diag μ hμ X hX N (hN N h)
    dd_sqrt := fun μ hμ X hX N h => C.dd_sqrt μ hμ X hX N (hN N h)
    omega_sqrt := fun μ hμ X hX N h => C.omega_sqrt μ hμ X hX N (hN N h)
    wf_eq := fun μ hμ X hX N h => C.wf_eq μ hμ X hX N (hN N h)
    rho_one := fun μ hμ X hX N h => C.rho_one μ hμ X hX N (hN N h)
    W_def := fun μ hμ X hX N h => C.W_def μ hμ X hX N (hN N h)
    M_def := fun μ hμ X hX N h => C.M_def μ hμ X hX N (hN N h)
    corr_lead := by
      obtain ⟨cg, Cg, hcg, g0, h⟩ := C.corr_lead
      exact ⟨cg, Cg, hcg, g0, fun μ hμ X hX N hN' => h μ hμ X hX N (hN N hN')⟩ }

/-- On a row whose first model function is the Weber pair at `a = -(j + 1/2)`, `Z = Y/sqrt h` (the form of `wf_eq`), the comparison
sequence `phi^{(1)}` of patch `1` is the Weber model `weberModelPhi` of the corrector row. -/
lemma _root_.FormalResearch.JacobiEigenvectors.Charts.LadderData.phi_eq_weberModelPhi (D : LadderData) {h Yv : ℝ} {j : ℕ}
    (hw : D.wf 1 0 (uNode h (j : ℤ)) h =
      ![ut pcU (-(((j : ℤ) : ℝ) + 1 / 2)) (Yv / Real.sqrt h),
        Real.sqrt h * (kappaBal (-(((j : ℤ) : ℝ) + 1 / 2)) * deriv (pcU (-(((j : ℤ) : ℝ) + 1 / 2))) (Yv / Real.sqrt h))]) :
    D.phi h 0 1 j = weberModelPhi pcU (D.AA 1 (uNode h j) h) (D.BB 1 (uNode h j) h) h j (Yv / Real.sqrt h) := by
  have hd : ∀ a z : ℝ, deriv (ut pcU a) z = kappaBal a * deriv (pcU a) z := fun a z => by
    change deriv (fun w => kappaBal a * pcU a w) z = _
    rw [deriv_const_mul_field']
  unfold LadderData.phi ladderSeq
  unfold uNode at hw
  rw [hw]
  simp only [dot, vrow, weberModelPhi, hd, uNode, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_natCast]

/-- On the chart rows the comparison sequence `phi^{(1)}` is the Weber model `weberModelPhi` of the corrector row. -/
lemma phi_eq {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : X ∈ Set.Icc Jlo Jhi) {N : ℕ} (hN : C.N0 ≤ N) {j : ℕ}
    (hj : (j : ℤ) ∈ Finset.Icc (0 : ℤ) ((C.chain μ X N).NR + 1)) :
    (C.chain μ X N).phi (F.step N) 0 1 j =
      weberModelPhi pcU ((C.chain μ X N).AA 1 (uNode (F.step N) j) (F.step N))
        ((C.chain μ X N).BB 1 (uNode (F.step N) j) (F.step N)) (F.step N) j
        (C.Y μ X (uNode (F.step N) j) / Real.sqrt (F.step N)) :=
  LadderData.phi_eq_weberModelPhi _ (C.wf_eq μ hμ X hX N hN (j : ℤ) hj).1

/-- The nodes `u_k`, `0 <= k <= N_R`, lie in `[0, c]`. -/
lemma uNode_mem {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : X ∈ Set.Icc Jlo Jhi) {N : ℕ} (hN : C.N0 ≤ N) {k : ℤ}
    (hk : k ∈ Finset.Icc (0 : ℤ) (C.chain μ X N).NR) :
    0 ≤ uNode (F.step N) k ∧ uNode (F.step N) k ≤ C.c := by
  obtain ⟨hk0, hkN⟩ := Finset.mem_Icc.mp hk
  have hh := step_pos F N
  have hshape := (C.shape μ hμ X hX N hN).2.2.2.1
  have hk0' : (0 : ℝ) ≤ k := by exact_mod_cast hk0
  have hkN' : (k : ℝ) ≤ (C.chain μ X N).NR := by exact_mod_cast hkN
  unfold uNode at hshape ⊢
  constructor
  · positivity
  · nlinarith


/-- The corrector row is bounded below once `C_g h^2 <= c_g/2` (the leading term `g_0 >= c_g` of `corr_lead`). -/
lemma A_lb_of_corr {cg Cg g A h : ℝ} (hCg : 0 ≤ Cg) (hh : 0 < h) (hh1 : h ≤ 1)
    (hhA : h ≤ cg / (2 * (Cg + 1))) (hg : cg ≤ g) (hA : |A - g| ≤ Cg * h ^ 2) : cg / 2 ≤ A := by
  have h1 : (Cg + 1) * h ≤ cg / 2 := by
    rw [le_div_iff₀ (by positivity)] at hhA; nlinarith
  have h2 : Cg * h ^ 2 ≤ Cg * h := mul_le_mul_of_nonneg_left (by nlinarith) hCg
  have := (abs_le.mp hA).1
  nlinarith

/-- `k_2(-(k + 1/2), Z_k) >= c_k max(|k + 1/2 - u_- / h|, 1)`, `c_k = min(c_H/4, 1)`: on the chart
`Z_k^2/4 - (k + 1/2) = -(u_k - u_-) H_Z/(4h)` (`turn_eq`). -/
lemma k2_lb {h um Hz Y cH : ℝ} {k : ℤ} (hh : 0 < h) (hcH : 0 < cH) (hHz : cH ≤ Hz)
    (hturn : 4 * (((k : ℝ) + 1 / 2) * h) - Y ^ 2 = (((k : ℝ) + 1 / 2) * h - um) * Hz) :
    min (cH / 4) 1 * max |(k : ℝ) + 1 / 2 - um / h| 1 ≤ k2 (-((k : ℝ) + 1 / 2)) (Y / Real.sqrt h) := by
  set x := |(k : ℝ) + 1 / 2 - um / h|
  have hz : (Y / Real.sqrt h) ^ 2 / 4 + -((k : ℝ) + 1 / 2) = -(((k : ℝ) + 1 / 2 - um / h) * Hz) / 4 := by
    rw [div_pow, Real.sq_sqrt hh.le]
    field_simp
    linear_combination (-(2 : ℝ)) * hturn
  have habs : |(Y / Real.sqrt h) ^ 2 / 4 + -((k : ℝ) + 1 / 2)| = x * Hz / 4 := by
    rw [hz, abs_div, abs_neg, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Hz), abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h1 : (1 : ℝ) ≤ (max |-((k : ℝ) + 1 / 2)| 1) ^ ((1 : ℝ) / 3) :=
    Real.one_le_rpow (le_max_right _ _) (by norm_num)
  unfold k2
  rcases le_total x 1 with hx | hx
  · rw [max_eq_right hx, mul_one]
    exact (min_le_right _ _).trans (le_max_of_le_right h1)
  · rw [max_eq_left hx]
    refine le_max_of_le_left ?_
    rw [habs]
    have hx0 : 0 ≤ x := abs_nonneg _
    calc min (cH / 4) 1 * x ≤ cH / 4 * x := mul_le_mul_of_nonneg_right (min_le_left _ _) hx0
      _ ≤ x * Hz / 4 := by nlinarith

/-- On a forbidden collar `4 x h <= Y^2`: `|Y/sqrt h| >= 2 sqrt x`. -/
lemma two_sqrt_le_abs {h Y x : ℝ} (hh : 0 < h) (hx : 0 ≤ x) (h4 : 4 * (x * h) ≤ Y ^ 2) :
    2 * Real.sqrt x ≤ |Y / Real.sqrt h| := by
  have hs := Real.sqrt_pos.mpr hh
  rw [abs_div, abs_of_pos hs, le_div_iff₀ hs]
  have e4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have : 2 * Real.sqrt x * Real.sqrt h = Real.sqrt (4 * (x * h)) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul hx, e4]; ring
  rw [this, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h4

/-- The derived chart data of a core: the threshold `N1`, the constants `cM, CM, c3, Csum` and the derived fields of
`BulkWeberChart`, for `N >= max N0 N1`. -/
structure Derived (N1 : ℕ) (cM CM c3 Csum : ℝ) : Prop where
  cM_pos : 0 < cM
  cM_le : cM ≤ CM
  c3_pos : 0 < c3
  Csum_nonneg : 0 ≤ Csum
  theta_le : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, max C.N0 N1 ≤ N → (C.chain μ X N).theta (F.step N) ≤ Csum
  W_osc : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, max C.N0 N1 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (C.chain μ X N).NR,
    C.c' ≤ uNode (F.step N) k → (C.chain μ X N).W k = 1
  M_osc : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, max C.N0 N1 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (C.chain μ X N).NR,
    C.c' ≤ uNode (F.step N) k →
      cM * (F.step N) ^ ((1 : ℝ) / 4) ≤ (C.chain μ X N).M k ∧ (C.chain μ X N).M k ≤ CM * (F.step N) ^ ((1 : ℝ) / 4)
  seed_pos : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, max C.N0 N1 ≤ N → 0 < (C.chain μ X N).phi (F.step N) 0 1 0
  collar_lb : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, max C.N0 N1 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (C.chain μ X N).NR,
    uNode (F.step N) k ≤ F.uMinus μ X →
      c3 * (C.chain μ X N).W k * (C.chain μ X N).M k ≤ |(C.chain μ X N).phi (F.step N) 0 1 k|

/-- **The derived fields hold** (`lem:cha-weber-env` (2), (3), `lem:cha-W0`) for `N >= max N0 N1`, from `bulk_W_osc_M_osc`, `bulk_theta_le`,
`weber_seed_pos_of_corr`, `weber_collar_lb_of_corr`. -/
theorem exists_derived : ∃ d : ℕ × ℝ × ℝ × ℝ × ℝ, C.Derived d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2 := by
  obtain ⟨hc'0, hc'c, hσ, hcL, hcH, -⟩ := C.geom_pos
  have hc0 : 0 ≤ C.c := by linarith
  obtain ⟨S, hS⟩ := C.Y_bound
  set CY := max S 0 with hCYdef
  have hCY : 0 ≤ CY := le_max_right _ _
  have hYb : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ u ∈ Set.Icc 0 (C.c + C.σ), |C.Y μ X u| ≤ CY := by
    intro μ hμ X hX u hu
    obtain ⟨_, _, _, _, hb⟩ := hS μ hμ
    exact (hb u hu X hX).1.trans (le_max_left _ _)
  obtain ⟨cg, Cg0, hcg, g0, hcorr⟩ := C.corr_lead
  set Cg := max Cg0 0
  have hCg : 0 ≤ Cg := le_max_right _ _
  obtain ⟨hs, hs_pos, hseed⟩ := weber_seed_pos_of_corr (half_pos hcg) hCg hCY
  obtain ⟨c3c, hcl, hc3, hcl_pos, hcoll⟩ := weber_collar_lb_of_corr (half_pos hcg) hCg hc0 hCY
  have hWM := bulk_W_osc_M_osc hcH hσ hc0 hCY
  dsimp only at hWM
  obtain ⟨hcM, hCM, hWM⟩ := hWM
  have hck : 0 < min (C.cH / 4) 1 := lt_min (by positivity) one_pos
  have hth := bulk_theta_le hck F.L_pos
  dsimp only at hth
  obtain ⟨hCs, hth⟩ := hth
  set hA := cg / (2 * (Cg + 1))
  have hA_pos : 0 < hA := by positivity
  obtain ⟨N1, hN1⟩ := exists_N_step_le F (lt_min (lt_min one_pos hA_pos) (lt_min hs_pos hcl_pos))
  refine ⟨(N1, (CY ^ 2 / 4 + C.c + 0 + 1) ^ (-(1 : ℝ) / 4),
    max ((C.cH * C.σ / 4) ^ (-(1 : ℝ) / 4)) ((CY ^ 2 / 4 + C.c + 0 + 1) ^ (-(1 : ℝ) / 4)), c3c,
    8 / Real.sqrt (min (C.cH / 4) 1) * Real.sqrt (2 * F.L + 1)), ?_⟩
  -- common facts for `N >= max N0 N1`
  have hstep : ∀ N, max C.N0 N1 ≤ N →
      C.N0 ≤ N ∧ 0 < F.step N ∧ F.step N ≤ 1 ∧ F.step N ≤ hA ∧ F.step N ≤ hs ∧ F.step N ≤ hcl := by
    intro N hN
    have h := hN1 N ((le_max_right _ _).trans hN)
    simp only [le_min_iff] at h
    exact ⟨(le_max_left _ _).trans hN, step_pos F N, h.1.1, h.1.2, h.2.1, h.2.2⟩
  have hrow : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, max C.N0 N1 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (C.chain μ X N).NR,
      cg / 2 ≤ (C.chain μ X N).AA 1 (uNode (F.step N) k) (F.step N) ∧
      |(C.chain μ X N).BB 1 (uNode (F.step N) k) (F.step N)| ≤ Cg ∧
      |C.Y μ X (uNode (F.step N) k)| ≤ CY := by
    intro μ hμ X hX N hN k hk
    obtain ⟨hN0, hh, hh1, hhA, -, -⟩ := hstep N hN
    obtain ⟨hg, hAg, hB⟩ := hcorr μ hμ X hX N hN0 k hk
    have hu := C.uNode_mem hμ hX hN0 hk
    exact ⟨A_lb_of_corr hCg hh hh1 hhA hg (hAg.trans (by gcongr; exact le_max_left _ _)),
      hB.trans (le_max_left _ _), hYb μ hμ X hX _ ⟨hu.1, by linarith⟩⟩
  refine ⟨hcM, le_max_right _ _, hc3, hCs, ?_, ?_, ?_, ?_, ?_⟩
  · -- theta_le
    intro μ hμ X hX N hN
    obtain ⟨hN0, hh, hh1, -, -, -⟩ := hstep N hN
    obtain ⟨hP, hs0, hNR0, hNRc, -⟩ := C.shape μ hμ X hX N hN0
    have hv := C.valid μ hμ X hX N hN0
    have hjj : (C.chain μ X N).jj 1 = (C.chain μ X N).NR - 1 := by
      have := hv.jj_last; rwa [hP] at this
    unfold LadderData.theta volTheta
    rw [C.omega_sqrt μ hμ X hX N hN0, hs0, hP, abs_of_nonneg (Real.sqrt_nonneg _), Real.div_sqrt,
      Finset.Icc_self, Finset.sum_singleton, hjj]
    simp only [eqLo, ite_true]
    have hsub : ∑ k ∈ Finset.Icc (0 : ℤ) ((C.chain μ X N).NR - 1), (C.chain μ X N).ρ k * (C.chain μ X N).M k ^ 2 ≤
        ∑ k ∈ Finset.Icc (0 : ℤ) (C.chain μ X N).NR,
          Mbal (-((k : ℝ) + 1 / 2)) (C.Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)) ^ 2 := by
      calc _ = ∑ k ∈ Finset.Icc (0 : ℤ) ((C.chain μ X N).NR - 1),
              Mbal (-((k : ℝ) + 1 / 2)) (C.Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)) ^ 2 := by
            refine Finset.sum_congr rfl fun k hk => ?_
            have hk' : k ∈ Finset.Icc (0 : ℤ) (C.chain μ X N).NR := by
              simp only [Finset.mem_Icc] at hk ⊢; omega
            rw [(C.rho_one μ hμ X hX N hN0 k hk').1, C.M_def μ hμ X hX N hN0 k hk', one_mul]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (by omega))
            (fun _ _ _ => sq_nonneg _)
    have hhL : F.step N ≤ F.L := by
      have := step_mul F N
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    have hNRL : (((C.chain μ X N).NR : ℝ) + 1) * F.step N ≤ 2 * F.L := by
      unfold uNode at hNRc; nlinarith
    have hk2 : ∀ k ∈ Finset.Icc (0 : ℤ) (C.chain μ X N).NR, min (C.cH / 4) 1 * max |(k : ℝ) + 1 / 2 - F.uMinus μ X / F.step N| 1 ≤
        k2 (-((k : ℝ) + 1 / 2)) (C.Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)) := by
      intro k hk
      have hu := C.uNode_mem hμ hX hN0 hk
      have hmem : uNode (F.step N) k ∈ Set.Icc 0 (C.c + C.σ) := ⟨hu.1, by linarith⟩
      exact k2_lb hh hcH (C.Hz_lb μ hμ X hX _ hmem) (C.turn_eq μ hμ X hX _ hmem)
    calc Real.sqrt (F.step N) * _ ≤ Real.sqrt (F.step N) * ∑ k ∈ Finset.Icc (0 : ℤ) (C.chain μ X N).NR,
          Mbal (-((k : ℝ) + 1 / 2)) (C.Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsub (Real.sqrt_nonneg _)
      _ ≤ _ := hth (Y := fun k => C.Y μ X (uNode (F.step N) k)) hh hh1 hNR0 hNRL hk2
  · -- W_osc
    intro μ hμ X hX N hN k hk hc'
    obtain ⟨hN0, hh, hh1, -, -, -⟩ := hstep N hN
    have hu := C.uNode_mem hμ hX hN0 hk
    have hmem : uNode (F.step N) k ∈ Set.Icc 0 (C.c + C.σ) := ⟨hu.1, by linarith⟩
    have hturn := C.turn_eq μ hμ X hX _ hmem
    have hHz := C.Hz_lb μ hμ X hX _ hmem
    have hwell := (C.overlap_in_well μ hμ X hX).1
    have hk0 : (0 : ℝ) ≤ (k : ℝ) + 1 / 2 := by
      have := (Finset.mem_Icc.mp hk).1; have : (0 : ℝ) ≤ k := by exact_mod_cast this
      linarith
    have hcs : C.cH * C.σ ≤ 4 * uNode (F.step N) k - C.Y μ X (uNode (F.step N) k) ^ 2 := by
      rw [hturn]; nlinarith
    rw [C.W_def μ hμ X hX N hN0 k hk]
    exact (hWM hh hh1 hk0 hu.2 hcs (hrow μ hμ X hX N hN k hk).2.2).1
  · -- M_osc
    intro μ hμ X hX N hN k hk hc'
    obtain ⟨hN0, hh, hh1, -, -, -⟩ := hstep N hN
    have hu := C.uNode_mem hμ hX hN0 hk
    have hmem : uNode (F.step N) k ∈ Set.Icc 0 (C.c + C.σ) := ⟨hu.1, by linarith⟩
    have hturn := C.turn_eq μ hμ X hX _ hmem
    have hHz := C.Hz_lb μ hμ X hX _ hmem
    have hwell := (C.overlap_in_well μ hμ X hX).1
    have hk0 : (0 : ℝ) ≤ (k : ℝ) + 1 / 2 := by
      have := (Finset.mem_Icc.mp hk).1; have : (0 : ℝ) ≤ k := by exact_mod_cast this
      linarith
    have hcs : C.cH * C.σ ≤ 4 * uNode (F.step N) k - C.Y μ X (uNode (F.step N) k) ^ 2 := by
      rw [hturn]; nlinarith
    rw [C.M_def μ hμ X hX N hN0 k hk]
    obtain ⟨-, h1, h2⟩ := hWM hh hh1 hk0 hu.2 hcs (hrow μ hμ X hX N hN k hk).2.2
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩
  · -- seed_pos
    intro μ hμ X hX N hN
    obtain ⟨hN0, hh, -, -, hhs, -⟩ := hstep N hN
    have hNR0 := (C.shape μ hμ X hX N hN0).2.2.1
    have hk : (0 : ℤ) ∈ Finset.Icc (0 : ℤ) (C.chain μ X N).NR := Finset.mem_Icc.mpr ⟨le_rfl, hNR0⟩
    have he := C.phi_eq hμ hX hN0 (j := 0) (by simp only [Nat.cast_zero, Finset.mem_Icc]; omega)
    simp only [Nat.cast_zero] at he
    rw [he]
    obtain ⟨hA, hB, hY⟩ := hrow μ hμ X hX N hN 0 hk
    exact hseed hh hhs hY hA hB
  · -- collar_lb
    intro μ hμ X hX N hN k hk hum
    obtain ⟨hN0, hh, -, -, -, hhc⟩ := hstep N hN
    obtain ⟨hA, hB, hY⟩ := hrow μ hμ X hX N hN k hk
    have hu := C.uNode_mem hμ hX hN0 hk
    have hmem : uNode (F.step N) k ∈ Set.Icc 0 (C.c + C.σ) := ⟨hu.1, by linarith⟩
    have hturn := C.turn_eq μ hμ X hX _ hmem
    have hHz := C.Hz_lb μ hμ X hX _ hmem
    rw [C.W_def μ hμ X hX N hN0 k hk, C.M_def μ hμ X hX N hN0 k hk]
    obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (Finset.mem_Icc.mp hk).1
    rw [C.phi_eq hμ hX hN0 (j := j) (by simp only [Finset.mem_Icc] at hk ⊢; omega)]
    have ej : ((j : ℤ) : ℝ) = (j : ℝ) := Int.cast_natCast j
    have hU : uNode (F.step N) (j : ℤ) = ((j : ℝ) + 1 / 2) * F.step N := by unfold uNode; rw [ej]
    have h4 : 4 * (((j : ℝ) + 1 / 2) * F.step N) ≤ C.Y μ X (uNode (F.step N) j) ^ 2 := by
      have : 4 * uNode (F.step N) j - C.Y μ X (uNode (F.step N) j) ^ 2 ≤ 0 := by
        rw [hturn]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      rw [← hU]; linarith
    have hL : ((j : ℝ) + 1 / 2) * F.step N ≤ C.c := by rw [← hU]; exact hu.2
    rw [ej]
    exact hcoll hh hhc hL hY (two_sqrt_le_abs hh (by positivity) h4) hA hB

end BulkWeberCore

/-- **The bulk Weber chart of a core** (model pair `pcU, pcV`): the core with `N0` raised (`raiseN0`) and the derived fields of
`BulkWeberCore.exists_derived`. -/
def BulkWeberChart.ofCore {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {Jlo Jhi : ℝ} {m : ℕ}
    (C : BulkWeberCore F P Jlo Jhi m pcU pcV) : BulkWeberChart F P Jlo Jhi m pcU pcV :=
  let d := Classical.choose C.exists_derived
  have hd : C.Derived d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2 := Classical.choose_spec C.exists_derived
  { toBulkWeberCore := C.raiseN0 d.1
    Csum := d.2.2.2.2, cM := d.2.1, CM := d.2.2.1, c3 := d.2.2.2.1
    env_pos := ⟨hd.cM_pos, hd.cM_le, hd.c3_pos, hd.Csum_nonneg⟩
    theta_le := hd.theta_le
    W_osc := hd.W_osc
    M_osc := hd.M_osc
    seed_pos := hd.seed_pos
    collar_lb := hd.collar_lb }

/-- The chart of a core has the core's ladder data. -/
@[simp] lemma BulkWeberChart.ofCore_chain {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par}
    {Jlo Jhi : ℝ} {m : ℕ} (C : BulkWeberCore F P Jlo Jhi m pcU pcV) : (BulkWeberChart.ofCore C).chain = C.chain := rfl

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.BulkWeberCore.exists_derived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.BulkWeberCore.exists_derived

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.BulkWeberChart.ofCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.BulkWeberChart.ofCore

end FormalResearch.JacobiEigenvectors.Charts
