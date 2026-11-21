module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.PCVFarGrowth
public import FormalResearch.JacobiEigenvectors.Charts.WeberLadder
public import FormalResearch.JacobiEigenvectors.Charts.SoftParabolicCylinder
public import FormalResearch.JacobiEigenvectors.Charts.BulkWeber
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftTransfer
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometrySoft
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZeroCore

/-!
# Paper J, Layer 4 (WP1b): Chart envelope/growth bounds & corrector-implied sign/lower bounds

Discharges the analytic chart bounds needed by `SoftEdgeChart` and `BulkWeberChart`:
* `soft_bondA_le` (`SoftEdgeChart.bondA_le`): uniform upper bound on tridiagonal bonds `a_n <= C_A`.
* `soft_grow_gap` (`SoftEdgeChart.grow_gap`): exact growth margin `a_n + a_{n-1} + nu_1 <= Q_n` on `[0, u_c - eta/4]`.
* `soft_ratioM` (`SoftEdgeChart.ratioM`): overlap amplitude ratio `M_{j_1+1} <= C_M M_{j_1}`.
* `actionWell_ge_of_zeta_lb`: far-zone lower bound `actionWell a Z >= SV` from `Z^2/4 + a >= c_{z1}/(8h)`.
* `soft_grow3_of_corr` (`SoftEdgeChart.grow3`): lower & growth bounds of the patch-3 growing comparison profile.
* `soft_ratio2_of_corr` (`SoftEdgeChart.ratio2`): forward decay ratio across `j_1` of the dominant PC pair.
* `soft_lb_pc_of_corr` (`SoftEdgeChart.lb_pc`): Liouville-Green lower bound on the left of the PC well.
* `weber_seed_pos_of_corr` (`BulkWeberChart.seed_pos`, `SoftEdgeChart.seed_posW`): positivity at row `0`.
* `weber_collar_lb_of_corr` (`BulkWeberChart.collar_lb`, `SoftEdgeChart.collar_lbW`, `SoftEdgeChart.lb_weber`):
  Weber collar lower bound for `|Z_k| >= 2 sqrt(k + 1/2)`.
* `bulk_W_osc_M_osc` (`BulkWeberChart.W_osc`, `BulkWeberChart.M_osc`): `W = 1`, `M ~ h^{1/4}` on `[c', c]`.
* `bulk_theta_le` (`BulkWeberChart.theta_le`): uniform modulus-sum bound `Theta_h <= C_sum`.
-/

@[expose] public section

noncomputable section

open Set Real
open scoped BigOperators

namespace FormalResearch.JacobiEigenvectors.Charts

open FormalResearch.JacobiEigenvectors
open FormalResearch.JacobiEigenvectors.Setting
open FormalResearch.JacobiEigenvectors.TheoremA

/-! ### Helper calculus and PC envelope bounds -/

private lemma deriv_comp_neg_of_diff {f : ℝ → ℝ} (hf : Differentiable ℝ f) (z : ℝ) :
    deriv (fun w => f (-w)) z = -deriv f (-z) := by
  have hc : HasDerivAt (fun w => f (-w)) (deriv f (-z) * (-1 : ℝ)) z :=
    (hf (-z)).hasDerivAt.comp z (hasDerivAt_neg z)
  linarith [hc.deriv]

private lemma deriv_neg_fun_of_diff {f : ℝ → ℝ} (hf : Differentiable ℝ f) (z : ℝ) :
    deriv (fun w => -f w) z = -deriv f z :=
  ((hf z).hasDerivAt.neg).deriv

private lemma vt_diff (a : ℝ) : Differentiable ℝ (vt pcV a) := by
  unfold vt
  exact ((pcSmoothFacts.slice_V a).differentiable (by simp)).const_mul _

private lemma ut_diff (a : ℝ) : Differentiable ℝ (ut pcU a) := by
  unfold ut
  exact ((pcSmoothFacts.slice_U a).differentiable (by simp)).const_mul _

private lemma kappaU_diff (a : ℝ) : Differentiable ℝ (fun w => kappaBal a * pcU a w) :=
  ((pcSmoothFacts.slice_U a).differentiable (by simp)).const_mul _

private lemma kappaU_neg_diff (a : ℝ) : Differentiable ℝ (fun w => kappaBal a * pcU a (-w)) :=
  (kappaU_diff a).comp differentiable_neg

private lemma Eswap_pos' (a z : ℝ) : 0 < Eswap a z := by
  unfold Eswap
  split_ifs
  · exact inv_pos.mpr (Ewell_pos _ _)
  · exact inv_pos.mpr (Ebar_pos _ _)

private lemma Ebar_neg_eq_inv (a z : ℝ) : (Ebar a z)⁻¹ = Ebar a (-z) := by
  unfold Ebar
  rw [← Real.exp_neg, neg_neg]
  congr 1
  have hcomp := intervalIntegral.integral_comp_neg
    (f := fun t : ℝ => Real.sqrt (t ^ 2 / 4 + a)) (a := (0 : ℝ)) (b := -z)
  simp only [neg_zero, neg_sq, neg_neg] at hcomp
  rw [hcomp, intervalIntegral.integral_symm]

private lemma Eminus_eq_Erec_neg (a z : ℝ) (hz : z < 0) :
    Eminus a z = Erec a (-z) := by
  unfold Eminus Erec
  by_cases ha : a ≤ 0
  · rw [if_pos ha, if_pos ha, abs_of_neg hz, abs_of_pos (neg_pos.mpr hz)]
  · rw [if_neg ha, if_neg ha, Ebar_neg_eq_inv]

private lemma Eswap_eq_Ewell_inv_of_nonpos {a z : ℝ} (ha : a ≤ 0) (hz : 0 ≤ z) :
    Eswap a z = (Ewell a z)⁻¹ := by
  unfold Eswap; rw [if_pos ha, abs_of_nonneg hz]

private lemma Eswap_eq_Ebar_inv_of_pos {a : ℝ} (ha : 0 < a) (z : ℝ) :
    Eswap a z = (Ebar a z)⁻¹ := by
  unfold Eswap; rw [if_neg ha.not_ge]

private lemma rpow_neg_half_eq_inv_sqrt {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 : ℝ) / 2) = (Real.sqrt x)⁻¹ := by
  have he : -(1 : ℝ) / 2 = -(1 / 2 : ℝ) := by norm_num
  rw [he, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]

private lemma rpow_div_neg_quarter {c h : ℝ} (hc : 0 < c) (hh : 0 < h) :
    (c / h) ^ (-(1 : ℝ) / 4) = c ^ (-(1 : ℝ) / 4) * h ^ ((1 : ℝ) / 4) := by
  rw [div_eq_mul_inv, Real.mul_rpow hc.le (inv_nonneg.mpr hh.le), Real.inv_rpow hh.le]
  congr 1
  have he : -(1 : ℝ) / 4 = -((1 : ℝ) / 4) := by norm_num
  rw [he, Real.rpow_neg hh.le, inv_inv]

private lemma step_le_one_of_large {Par : Type*} (F : SymbolFamily Par) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N → F.step N ≤ 1 := by
  obtain ⟨N0, hN0⟩ := exists_nat_one_div_lt (show (0 : ℝ) < 1 / max F.L 1 from
    div_pos zero_lt_one (lt_max_iff.mpr (Or.inr zero_lt_one)))
  refine ⟨N0, fun N hN => ?_⟩
  unfold SymbolFamily.step FormalResearch.JB.stepSize
  have hL : 0 < F.L := F.L_pos
  have hN' : (N0 : ℝ) ≤ N := by exact_mod_cast hN
  have hmax : (1 : ℝ) / max F.L 1 ≤ 1 / F.L := one_div_le_one_div_of_le hL (le_max_left _ _)
  have h1 : 1 / ((N0 : ℝ) + 1) < 1 / F.L := hN0.trans_le hmax
  rw [div_lt_div_iff₀ (by positivity) hL] at h1
  exact (div_le_one (by positivity : (0 : ℝ) < (N : ℝ) + 1)).mpr (by nlinarith)

private lemma abs_E0_sub_le {L M0 M1 : ℝ} (hL : 0 < L) {G : ℝ → ℝ}
    (hG_cont : ContinuousOn G (Icc 0 L))
    (hG_diff : ∀ s ∈ Ioo 0 L, HasDerivAt G (deriv G s) s)
    (hG0 : ∀ s ∈ Icc 0 L, |G s| ≤ M0)
    (hG1 : ∀ s ∈ Ioo 0 L, |deriv G s| ≤ M1)
    {u v : ℝ} (hu : u ∈ Icc 0 L) (hv : v ∈ Icc 0 L) :
    |E0 L G u - E0 L G v| ≤ (L * M0 + L ^ 2 / 4 * M1) * |u - v| := by
  wlog huv : u ≤ v generalizing u v
  · rw [abs_sub_comm (E0 L G u), abs_sub_comm u v]
    exact this hv hu (le_of_not_ge huv)
  rcases eq_or_lt_of_le huv with rfl | huv_lt
  · simp
  have hE_cont : ContinuousOn (E0 L G) (Icc u v) := by
    have hs : ContinuousOn (fun s : ℝ => s * (L - s)) (Icc u v) := by fun_prop
    exact hs.mul (hG_cont.mono (Icc_subset_Icc hu.1 hv.2))
  let f' : ℝ → ℝ := fun x => (L - 2 * x) * G x + x * (L - x) * deriv G x
  have hE_diff : ∀ x ∈ Ioo u v, HasDerivAt (E0 L G) (f' x) x := by
    intro x hx
    have hx0L : x ∈ Ioo 0 L := ⟨hu.1.trans_lt hx.1, hx.2.trans_le hv.2⟩
    have hp : HasDerivAt (fun s : ℝ => s * (L - s)) (L - 2 * x) x :=
      ((hasDerivAt_id' x).mul ((hasDerivAt_const x L).sub (hasDerivAt_id' x))).congr_deriv (by dsimp; ring)
    exact (hp.mul (hG_diff x hx0L)).congr_deriv (by ring)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (E0 L G) f' huv_lt hE_cont hE_diff
  have hcI : c ∈ Icc 0 L := ⟨hu.1.trans hc.1.le, hc.2.le.trans hv.2⟩
  have hc0L : c ∈ Ioo 0 L := ⟨hu.1.trans_lt hc.1, hc.2.trans_le hv.2⟩
  have h1 : |L - 2 * c| ≤ L := by rw [abs_le]; constructor <;> linarith [hcI.1, hcI.2]
  have h2 : |c * (L - c)| ≤ L ^ 2 / 4 := by
    rw [abs_of_nonneg (mul_nonneg hcI.1 (sub_nonneg.mpr hcI.2))]
    nlinarith [sq_nonneg (c - L / 2)]
  have hfc : |f' c| ≤ L * M0 + L ^ 2 / 4 * M1 := by
    calc |f' c|
        ≤ |(L - 2 * c) * G c| + |c * (L - c) * deriv G c| := abs_add_le _ _
      _ = |L - 2 * c| * |G c| + |c * (L - c)| * |deriv G c| := by rw [abs_mul, abs_mul]
      _ ≤ L * M0 + L ^ 2 / 4 * M1 := by
            gcongr
            · exact hG0 c hcI
            · exact hG1 c hc0L
  have hv_u : 0 < v - u := sub_pos.mpr huv_lt
  rw [eq_div_iff hv_u.ne'] at hslope
  have heq : |E0 L G u - E0 L G v| = |f' c| * |u - v| := by
    rw [abs_sub_comm (E0 L G u), abs_sub_comm u v, ← hslope, abs_mul]
  rw [heq]
  exact mul_le_mul_of_nonneg_right hfc (abs_nonneg _)

/-! ### 1. `soft_bondA_le` and `soft_grow_gap` -/

/-- **Tridiagonal bond upper bound (`SoftEdgeChart.bondA_le`)**: from `CoreReg F P e`. -/
theorem soft_bondA_le {Par : Type*} [TopologicalSpace Par]
    (F : SymbolFamily Par) {P : Set Par} {e : ℕ} (hR : CoreReg F P e) :
    ∃ CA : ℝ, ∃ N0 : ℕ, 0 < CA ∧
      ∀ μ ∈ P, ∀ N, N0 ≤ N → ∀ k : ℤ, F.bondA μ N k ≤ CA := by
  obtain ⟨M0, hM0⟩ := jet_bound hR.compact hR.regG (k := 0) (by omega)
  obtain ⟨C0, hC0⟩ := hR.rem
  obtain ⟨N0, hN0⟩ := step_le_one_of_large F
  refine ⟨Real.sqrt (max (F.L ^ 2 / 4 * (M0 + |C0|)) 0) + 1, N0, by positivity, ?_⟩
  intro μ hμ N hN k
  have hstep_le : F.step N ≤ 1 := hN0 N hN
  unfold SymbolFamily.bondA
  split_ifs with hk
  · have hpos : 0 < F.step N := step_pos F N
    have hmul : F.step N * ((N : ℝ) + 1) = F.L := step_mul F N
    have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hkN : (k : ℝ) + 1 ≤ N := by
      have : k + 1 ≤ (N : ℤ) := hk.2
      exact_mod_cast this
    have hs0 : 0 ≤ sNode (F.step N) k := by unfold sNode; positivity
    have hsL : sNode (F.step N) k ≤ F.L := by unfold sNode; nlinarith
    have hs_prod : sNode (F.step N) k * (F.L - sNode (F.step N) k) ≤ F.L ^ 2 / 4 := by
      nlinarith [sq_nonneg (sNode (F.step N) k - F.L / 2)]
    have hG_err := (hC0 μ hμ N hstep_le (sNode (F.step N) k) ⟨hs0, hsL⟩).1
    have hG0_bd : |F.G 0 μ (sNode (F.step N) k)| ≤ M0 := hM0 μ hμ _ ⟨hs0, hsL⟩
    have hGh_bd : F.Gh μ (F.step N) (sNode (F.step N) k) ≤ M0 + |C0| := by
      have h1 : F.Gh μ (F.step N) (sNode (F.step N) k) - F.G 0 μ (sNode (F.step N) k) ≤
          C0 * F.step N ^ e := (abs_le.mp hG_err).2
      have h2 : F.G 0 μ (sNode (F.step N) k) ≤ M0 := (le_abs_self _).trans hG0_bd
      have h3 : C0 * F.step N ^ e ≤ |C0| := (le_abs_self _).trans (by
        rw [abs_mul, abs_pow, abs_of_pos hpos]
        exact mul_le_of_le_one_right (abs_nonneg C0) (pow_le_one₀ hpos.le hstep_le))
      linarith
    have hE : F.entryE μ N k ≤ F.L ^ 2 / 4 * (M0 + |C0|) := by
      unfold SymbolFamily.entryE
      have hnn : 0 ≤ sNode (F.step N) k * (F.L - sNode (F.step N) k) := mul_nonneg hs0 (sub_nonneg.mpr hsL)
      have hMnn : 0 ≤ M0 + |C0| :=
        (abs_nonneg _).trans hG0_bd |>.trans (le_add_of_nonneg_right (abs_nonneg C0))
      nlinarith
    calc Real.sqrt (F.entryE μ N k)
        ≤ Real.sqrt (max (F.L ^ 2 / 4 * (M0 + |C0|)) 0) :=
            Real.sqrt_le_sqrt (hE.trans (le_max_left _ _))
      _ ≤ Real.sqrt (max (F.L ^ 2 / 4 * (M0 + |C0|)) 0) + 1 := by linarith
  · positivity

/-- **Forbidden-left growth margin (`SoftEdgeChart.grow_gap`)**: from `CoreReg` (`e >= 1`) and `GeomSoftConcl`
(using `X' = X - delta_*/2` to extract `Q_0 - 2 sqrt(E_0) > delta_*/2`). -/
theorem soft_grow_gap {Par : Type*} [TopologicalSpace Par]
    (F : SymbolFamily Par) {P K : Set Par} {e : ℕ} (hR : CoreReg F P e) (he : 1 ≤ e) (hKP : K ⊆ P)
    {g : ℝ} (hg : 0 < g) (hG_pos : ∀ μ ∈ P, ∀ u ∈ Icc 0 F.L, g ≤ F.G 0 μ u)
    {uc : Par → ℝ} {η δs δ0 : ℝ} (hη : 0 < η) (hδs : 0 < δs) (hδ0p : 0 < δ0) (hδ0 : δ0 ≤ δs / 2)
    (huc : ∀ μ ∈ K, 0 < uc μ - 2 * η ∧ uc μ + 2 * η < F.L)
    (hgeom : ∀ μ ∈ K, ∀ δ0' : ℝ, 0 < δ0' → δ0' ≤ δs → ∀ X : ℝ, |X - F.bandHi μ| ≤ δ0' →
      ∀ u ∈ Icc 0 F.L, η / 4 ≤ |u - uc μ| → Tfun F.L (F.G 0 μ) (F.B 0 μ) X u < 0 ∧ 0 < X - F.B 0 μ u) :
    ∃ nu1 : ℝ, ∃ N0 : ℕ, 0 < nu1 ∧
      ∀ μ ∈ K, ∀ X : ℝ, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ n : ℤ, 0 ≤ n →
        uNode (F.step N) n ≤ uc μ - η / 4 →
        F.bondA μ N n + F.bondA μ N (n - 1) + nu1 ≤ F.diagQ μ N X n := by
  obtain ⟨M0, hM0⟩ := jet_bound hR.compact hR.regG (k := 0) (by omega)
  obtain ⟨M1, hM1⟩ := jet_bound hR.compact hR.regG (k := 1) (by omega)
  obtain ⟨C0, hC0⟩ := hR.rem
  obtain ⟨N1, hN1⟩ := step_le_one_of_large F
  have hFL : 0 < F.L := F.L_pos
  let CE : ℝ := max (F.L * |M0| + F.L ^ 2 / 4 * |M1|) 0
  let C_tot : ℝ := |C0| + 2 * (F.L * |C0| / (4 * Real.sqrt g)) + 2 * Real.sqrt CE
  have hCE_nn : 0 ≤ CE := le_max_right _ _
  have hCtot_nn : 0 ≤ C_tot := by dsimp [C_tot]; positivity
  let hmax : ℝ := min 1 ((δs / (4 * (C_tot + 1))) ^ 2)
  have hhmax_pos : 0 < hmax := lt_min zero_lt_one (sq_pos_of_pos (div_pos hδs (by linarith)))
  obtain ⟨N2, hN2⟩ := exists_nat_one_div_lt (show (0 : ℝ) < hmax / max F.L 1 from
    div_pos hhmax_pos (lt_max_iff.mpr (Or.inr zero_lt_one)))
  refine ⟨δs / 4, max N1 N2, by positivity, ?_⟩
  intro μ hμK X hX N hN n hn0 hun
  have hμP : μ ∈ P := hKP hμK
  have hh_pos : 0 < F.step N := step_pos F N
  have hh1 : F.step N ≤ 1 := hN1 N (le_trans (le_max_left _ _) hN)
  have hh_le_hmax : F.step N ≤ hmax := by
    unfold SymbolFamily.step FormalResearch.JB.stepSize
    have hL : 0 < F.L := F.L_pos
    have hN' : (N2 : ℝ) ≤ N := by exact_mod_cast (le_trans (le_max_right _ _) hN)
    have hmaxL : 1 / max F.L 1 ≤ 1 / F.L := one_div_le_one_div_of_le hL (le_max_left _ _)
    have h1 : 1 / ((N2 : ℝ) + 1) < hmax / F.L := by
      calc 1 / ((N2 : ℝ) + 1) < hmax / max F.L 1 := hN2
        _ = hmax * (1 / max F.L 1) := by ring
        _ ≤ hmax * (1 / F.L) := mul_le_mul_of_nonneg_left hmaxL hhmax_pos.le
        _ = hmax / F.L := by ring
    rw [div_lt_div_iff₀ (by positivity) hL] at h1
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    nlinarith
  have hsq_le : Real.sqrt (F.step N) ≤ δs / (4 * (C_tot + 1)) := by
    calc Real.sqrt (F.step N) ≤ Real.sqrt ((δs / (4 * (C_tot + 1))) ^ 2) :=
            Real.sqrt_le_sqrt (hh_le_hmax.trans (min_le_right _ _))
      _ = δs / (4 * (C_tot + 1)) := Real.sqrt_sq (div_nonneg hδs.le (by linarith))
  have h_le_sqrt : F.step N ≤ Real.sqrt (F.step N) := by
    calc F.step N = Real.sqrt (F.step N) * Real.sqrt (F.step N) := (Real.mul_self_sqrt hh_pos.le).symm
      _ ≤ 1 * Real.sqrt (F.step N) := mul_le_mul_of_nonneg_right (Real.sqrt_le_one.mpr hh1) (Real.sqrt_nonneg _)
      _ = Real.sqrt (F.step N) := one_mul _
  have hpow_le : F.step N ^ e ≤ Real.sqrt (F.step N) :=
    (pow_le_pow_of_le_one hh_pos.le hh1 he).trans (by simpa using h_le_sqrt)
  have hun_nn : 0 ≤ uNode (F.step N) n := by
    unfold uNode
    have : (0 : ℝ) ≤ n := by exact_mod_cast hn0
    positivity
  have huc_bounds := huc μ hμK
  have hun_le_L : uNode (F.step N) n ≤ F.L := by linarith [huc_bounds.2]
  have hun_mem : uNode (F.step N) n ∈ Icc 0 F.L := ⟨hun_nn, hun_le_L⟩
  have hgap_eta : η / 4 ≤ |uNode (F.step N) n - uc μ| := by
    have : uNode (F.step N) n - uc μ ≤ -(η / 4) := by linarith
    exact (le_neg.mpr this).trans (neg_le_abs _)
  have hX' : |(X - δs / 2) - F.bandHi μ| ≤ δs := by
    calc |(X - δs / 2) - F.bandHi μ| = |(X - F.bandHi μ) - δs / 2| := by ring_nf
      _ ≤ |X - F.bandHi μ| + |δs / 2| := abs_sub _ _
      _ ≤ δ0 + δs / 2 := by rw [abs_of_pos (half_pos hδs)]; linarith
      _ ≤ δs := by linarith
  obtain ⟨hT_neg, hQ'_pos⟩ := hgeom μ hμK δs hδs le_rfl (X - δs / 2) hX' (uNode (F.step N) n) hun_mem hgap_eta
  have hE0_nn : 0 ≤ E0 F.L (F.G 0 μ) (uNode (F.step N) n) := by
    unfold E0
    exact mul_nonneg (mul_nonneg hun_nn (sub_nonneg.mpr hun_le_L))
      (le_trans hg.le (hG_pos μ hμP _ hun_mem))
  have hsq_strict : 4 * E0 F.L (F.G 0 μ) (uNode (F.step N) n) < (X - δs / 2 - F.B 0 μ (uNode (F.step N) n)) ^ 2 := by
    unfold Tfun at hT_neg; linarith
  have h2sqrt_lt : 2 * Real.sqrt (E0 F.L (F.G 0 μ) (uNode (F.step N) n)) <
      X - δs / 2 - F.B 0 μ (uNode (F.step N) n) := by
    nlinarith [Real.sq_sqrt hE0_nn, Real.sqrt_nonneg (E0 F.L (F.G 0 μ) (uNode (F.step N) n))]
  have hBn_err : F.entryB μ N n - F.B 0 μ (uNode (F.step N) n) ≤ |C0| * Real.sqrt (F.step N) := by
    have hb := (hC0 μ hμP N hh1 (uNode (F.step N) n) hun_mem).2
    have h1 : F.entryB μ N n - F.B 0 μ (uNode (F.step N) n) ≤ C0 * F.step N ^ e := by
      dsimp [SymbolFamily.entryB]
      exact (le_abs_self _).trans hb
    calc F.entryB μ N n - F.B 0 μ (uNode (F.step N) n)
        ≤ C0 * F.step N ^ e := h1
      _ ≤ |C0| * F.step N ^ e := mul_le_mul_of_nonneg_right (le_abs_self C0) (pow_pos hh_pos e).le
      _ ≤ |C0| * Real.sqrt (F.step N) := mul_le_mul_of_nonneg_left hpow_le (abs_nonneg _)
  have hG_cont : ContinuousOn (F.G 0 μ) (Icc 0 F.L) := (hR.regG.1 μ hμP).continuousOn
  have hG_diff : ∀ s ∈ Ioo 0 F.L, HasDerivAt (F.G 0 μ) (deriv (F.G 0 μ) s) s :=
    fun s hs => (interior_jet F.L_pos (hR.regG.1 μ hμP) hs).1
  have hG0_bd : ∀ s ∈ Icc 0 F.L, |F.G 0 μ s| ≤ |M0| := fun s hs => (hM0 μ hμP s hs).trans (le_abs_self M0)
  have hG1_bd : ∀ s ∈ Ioo 0 F.L, |deriv (F.G 0 μ) s| ≤ |M1| := fun s hs => by
    have heq := (interior_jet F.L_pos (hR.regG.1 μ hμP) hs).2.2.1
    rw [← heq]
    exact (hM1 μ hμP s (Ioo_subset_Icc_self hs)).trans (le_abs_self M1)
  have hbond_bound : ∀ k : ℤ, (k = n ∨ k = n - 1) →
      F.bondA μ N k ≤ Real.sqrt (E0 F.L (F.G 0 μ) (uNode (F.step N) n)) +
        (F.L * |C0| / (4 * Real.sqrt g) + Real.sqrt CE) * Real.sqrt (F.step N) := by
    intro k hk
    by_cases hk_in : 0 ≤ k ∧ k < N
    · have hmul : F.step N * ((N : ℝ) + 1) = F.L := step_mul F N
      have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast hk_in.1
      have hkN : (k : ℝ) + 1 ≤ N := by
        have : k + 1 ≤ (N : ℤ) := hk_in.2
        exact_mod_cast this
      have hs0 : 0 ≤ sNode (F.step N) k := by unfold sNode; positivity
      have hsL : sNode (F.step N) k ≤ F.L := by unfold sNode; nlinarith
      have hba := TheoremA.bondA_le F hg (abs_nonneg C0) μ N (hG_pos μ hμP) (e := e)
        (fun s hs => (hC0 μ hμP N hh1 s hs).1.trans
          (mul_le_mul_of_nonneg_right (le_abs_self C0) (pow_pos hh_pos e).le)) k
      have hE_diff := abs_E0_sub_le F.L_pos hG_cont hG_diff hG0_bd hG1_bd ⟨hs0, hsL⟩ hun_mem
      have hs_dist : |sNode (F.step N) k - uNode (F.step N) n| ≤ F.step N / 2 := by
        unfold sNode uNode
        rcases hk with hk_eq | hk_eq
        · rw [hk_eq]
          have : ((n : ℝ) + 1) * F.step N - ((n : ℝ) + 1 / 2) * F.step N = F.step N / 2 := by ring
          rw [this, abs_of_pos (half_pos hh_pos)]
        · rw [hk_eq]
          have : (((n - 1 : ℤ) : ℝ) + 1) * F.step N - ((n : ℝ) + 1 / 2) * F.step N = -(F.step N / 2) := by
            push_cast; ring
          rw [this, abs_neg, abs_of_pos (half_pos hh_pos)]
      set Es : ℝ := E0 F.L (F.G 0 μ) (sNode (F.step N) k)
      set Eu : ℝ := E0 F.L (F.G 0 μ) (uNode (F.step N) n)
      have hE_step : Es ≤ Eu + CE * F.step N := by
        have h1 : Es - Eu ≤ (F.L * |M0| + F.L ^ 2 / 4 * |M1|) * |sNode (F.step N) k - uNode (F.step N) n| :=
          (le_abs_self _).trans hE_diff
        have h2 : (F.L * |M0| + F.L ^ 2 / 4 * |M1|) * |sNode (F.step N) k - uNode (F.step N) n| ≤
            CE * (F.step N / 2) := by
          gcongr; exact le_max_left _ _
        have h3 : CE * (F.step N / 2) ≤ CE * F.step N :=
          mul_le_mul_of_nonneg_left (by linarith only [hh_pos]) hCE_nn
        have h4 : Es - Eu ≤ CE * F.step N := h1.trans (h2.trans h3)
        rwa [sub_le_iff_le_add'] at h4
      have hsq_E : Real.sqrt Es ≤ Real.sqrt Eu + Real.sqrt CE * Real.sqrt (F.step N) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        have hsq1 : Real.sqrt Eu ^ 2 = Eu := Real.sq_sqrt hE0_nn
        have hsq2 : (Real.sqrt CE * Real.sqrt (F.step N)) ^ 2 = CE * F.step N := by
          rw [mul_pow, Real.sq_sqrt hCE_nn, Real.sq_sqrt hh_pos.le]
        calc Es
            ≤ Eu + CE * F.step N := hE_step
          _ = Real.sqrt Eu ^ 2 + (Real.sqrt CE * Real.sqrt (F.step N)) ^ 2 := by rw [hsq1, hsq2]
          _ ≤ Real.sqrt Eu ^ 2 + (Real.sqrt CE * Real.sqrt (F.step N)) ^ 2 +
                2 * Real.sqrt Eu * (Real.sqrt CE * Real.sqrt (F.step N)) :=
              le_add_of_nonneg_right (by positivity)
          _ = (Real.sqrt Eu + Real.sqrt CE * Real.sqrt (F.step N)) ^ 2 := by ring
      have herr_pow : F.L * (|C0| * F.step N ^ e) / (4 * Real.sqrt g) ≤
          F.L * |C0| / (4 * Real.sqrt g) * Real.sqrt (F.step N) := by
        have : F.L * (|C0| * F.step N ^ e) / (4 * Real.sqrt g) =
            (F.L * |C0| / (4 * Real.sqrt g)) * F.step N ^ e := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
      calc F.bondA μ N k
          ≤ Real.sqrt Es + F.L * (|C0| * F.step N ^ e) / (4 * Real.sqrt g) := hba
        _ ≤ (Real.sqrt Eu + Real.sqrt CE * Real.sqrt (F.step N)) +
              F.L * |C0| / (4 * Real.sqrt g) * Real.sqrt (F.step N) := add_le_add hsq_E herr_pow
        _ = Real.sqrt Eu + (F.L * |C0| / (4 * Real.sqrt g) + Real.sqrt CE) * Real.sqrt (F.step N) := by ring
    · unfold SymbolFamily.bondA
      rw [if_neg hk_in]
      exact add_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (add_nonneg (div_nonneg (mul_nonneg hFL.le (abs_nonneg _)) (by positivity))
          (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hba_n := hbond_bound n (Or.inl rfl)
  have hba_m := hbond_bound (n - 1) (Or.inr rfl)
  have herr_sum : C_tot * Real.sqrt (F.step N) ≤ δs / 4 := by
    calc C_tot * Real.sqrt (F.step N)
        ≤ (C_tot + 1) * (δs / (4 * (C_tot + 1))) := by gcongr; linarith
      _ = δs / 4 := by field_simp
  have htot_eq : C_tot * Real.sqrt (F.step N) =
      |C0| * Real.sqrt (F.step N) + 2 * ((F.L * |C0| / (4 * Real.sqrt g) + Real.sqrt CE) * Real.sqrt (F.step N)) := by
    dsimp [C_tot]; ring
  unfold SymbolFamily.diagQ
  exact le_of_lt <| by
    calc F.bondA μ N n + F.bondA μ N (n - 1) + δs / 4
        ≤ (Real.sqrt (E0 F.L (F.G 0 μ) (uNode (F.step N) n)) +
              (F.L * |C0| / (4 * Real.sqrt g) + Real.sqrt CE) * Real.sqrt (F.step N)) +
            (Real.sqrt (E0 F.L (F.G 0 μ) (uNode (F.step N) n)) +
              (F.L * |C0| / (4 * Real.sqrt g) + Real.sqrt CE) * Real.sqrt (F.step N)) +
            δs / 4 := by linarith only [hba_n, hba_m]
      _ = 2 * Real.sqrt (E0 F.L (F.G 0 μ) (uNode (F.step N) n)) +
            (C_tot * Real.sqrt (F.step N) - |C0| * Real.sqrt (F.step N)) + δs / 4 := by
          rw [htot_eq]; ring
      _ ≤ 2 * Real.sqrt (E0 F.L (F.G 0 μ) (uNode (F.step N) n)) + δs / 2 - |C0| * Real.sqrt (F.step N) := by
          linarith only [herr_sum]
      _ < (X - δs / 2 - F.B 0 μ (uNode (F.step N) n)) + δs / 2 -
            (F.entryB μ N n - F.B 0 μ (uNode (F.step N) n)) := by
          linarith only [h2sqrt_lt, hBn_err]
      _ = X - F.entryB μ N n := by ring

/-! ### 2. `soft_ratioM` (`SoftEdgeChart.ratioM`) -/

/-- **Overlap amplitude ratio (`SoftEdgeChart.ratioM`)**: grid-level ratio `M_{j_1+1} ≤ C_M M_{j_1}`. -/
theorem soft_ratioM {L CY cz1 : ℝ} (hL : 0 < L) (hCY : 0 ≤ CY) (hcz1 : 0 < cz1) :
    let CM : ℝ := (8 * max (CY ^ 2 / 4 + L) (L + 1) / cz1) ^ ((1 : ℝ) / 4)
    0 < CM ∧ ∀ {h : ℝ} {j1 : ℤ} {Y a Z : ℝ},
      0 < h → h ≤ 1 → 0 ≤ j1 → ((j1 : ℝ) + 1 / 2) * h ≤ L → |Y| ≤ CY →
      cz1 / (8 * h) ≤ Z ^ 2 / 4 + a →
      Mbal a Z ≤ CM * Mbal (-((j1 : ℝ) + 1 / 2)) (Y / Real.sqrt h) := by
  intro CM
  have hmax_pos : 0 < max (CY ^ 2 / 4 + L) (L + 1) :=
    lt_of_lt_of_le (by linarith [hL]) (le_max_right _ _)
  have hc_pos : 0 < 8 * max (CY ^ 2 / 4 + L) (L + 1) / cz1 := div_pos (mul_pos (by norm_num) hmax_pos) hcz1
  refine ⟨Real.rpow_pos_of_pos hc_pos _, ?_⟩
  intro h j1 Y a Z hh hh1 hj1 hu_le hY hZa
  have hk_lo : cz1 / (8 * h) ≤ k2 a Z := by
    have : cz1 / (8 * h) ≤ |Z ^ 2 / 4 + a| := hZa.trans (le_abs_self _)
    exact this.trans (le_max_left _ _)
  have hnu_pos : 0 ≤ (j1 : ℝ) + 1 / 2 := by
    have : (0 : ℝ) ≤ j1 := by exact_mod_cast hj1
    linarith
  have hnu_le : (j1 : ℝ) + 1 / 2 ≤ L / h := (le_div_iff₀ hh).mpr hu_le
  have hZ_sq : (Y / Real.sqrt h) ^ 2 / 4 ≤ (CY ^ 2 / 4) / h := by
    rw [div_pow, Real.sq_sqrt hh.le]
    have hsq : Y ^ 2 ≤ CY ^ 2 := sq_le_sq.mpr (by simpa [abs_of_nonneg hCY] using hY)
    calc Y ^ 2 / h / 4 = (Y ^ 2 / 4) / h := by ring
      _ ≤ (CY ^ 2 / 4) / h := by gcongr
  have hterm1 : |(Y / Real.sqrt h) ^ 2 / 4 + (-((j1 : ℝ) + 1 / 2))| ≤ (CY ^ 2 / 4 + L) / h := by
    have hadd : (CY ^ 2 / 4 + L) / h = (CY ^ 2 / 4) / h + L / h := add_div _ _ _
    have hZ_nn : 0 ≤ (Y / Real.sqrt h) ^ 2 / 4 := by positivity
    have hCY_nn : 0 ≤ (CY ^ 2 / 4) / h := by positivity
    rw [abs_le]; constructor <;> linarith
  have hterm2 : max |-((j1 : ℝ) + 1 / 2)| 1 ^ ((1 : ℝ) / 3) ≤ (L + 1) / h := by
    have hm_ge1 : 1 ≤ max |-((j1 : ℝ) + 1 / 2)| 1 := le_max_right _ _
    have hm_le : max |-((j1 : ℝ) + 1 / 2)| 1 ≤ (L + 1) / h := by
      rw [abs_neg, abs_of_nonneg hnu_pos]
      exact max_le (hnu_le.trans (div_le_div_of_nonneg_right (by linarith) hh.le))
        ((one_le_div hh).mpr (by linarith))
    have hpow : max |-((j1 : ℝ) + 1 / 2)| 1 ^ ((1 : ℝ) / 3) ≤ max |-((j1 : ℝ) + 1 / 2)| 1 ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hm_ge1 (by norm_num)
    rw [Real.rpow_one] at hpow
    exact hpow.trans hm_le
  have hk_hi : k2 (-((j1 : ℝ) + 1 / 2)) (Y / Real.sqrt h) ≤ max (CY ^ 2 / 4 + L) (L + 1) / h := by
    unfold k2
    exact max_le (hterm1.trans (div_le_div_of_nonneg_right (le_max_left _ _) hh.le))
      (hterm2.trans (div_le_div_of_nonneg_right (le_max_right _ _) hh.le))
  have hratio_k : k2 (-((j1 : ℝ) + 1 / 2)) (Y / Real.sqrt h) ≤
      (8 * max (CY ^ 2 / 4 + L) (L + 1) / cz1) * k2 a Z := by
    calc k2 (-((j1 : ℝ) + 1 / 2)) (Y / Real.sqrt h)
        ≤ max (CY ^ 2 / 4 + L) (L + 1) / h := hk_hi
      _ = (8 * max (CY ^ 2 / 4 + L) (L + 1) / cz1) * (cz1 / (8 * h)) := by field_simp
      _ ≤ (8 * max (CY ^ 2 / 4 + L) (L + 1) / cz1) * k2 a Z := by gcongr
  have hM1 : Mbal a Z ≤ (k2 (-((j1 : ℝ) + 1 / 2)) (Y / Real.sqrt h) /
      (8 * max (CY ^ 2 / 4 + L) (L + 1) / cz1)) ^ (-(1 : ℝ) / 4) := by
    unfold Mbal
    apply Real.rpow_le_rpow_of_nonpos
    · exact div_pos (k2_pos _ _) hc_pos
    · rw [div_le_iff₀ hc_pos]
      linarith [mul_comm (8 * max (CY ^ 2 / 4 + L) (L + 1) / cz1) (k2 a Z)]
    · norm_num
  have hpow_div : (k2 (-((j1 : ℝ) + 1 / 2)) (Y / Real.sqrt h) /
      (8 * max (CY ^ 2 / 4 + L) (L + 1) / cz1)) ^ (-(1 : ℝ) / 4) =
      CM * Mbal (-((j1 : ℝ) + 1 / 2)) (Y / Real.sqrt h) := by
    unfold Mbal
    rw [div_eq_mul_inv, Real.mul_rpow (k2_pos _ _).le (inv_nonneg.mpr hc_pos.le),
      Real.inv_rpow hc_pos.le]
    have he : -(1 : ℝ) / 4 = -((1 : ℝ) / 4) := by norm_num
    rw [he, Real.rpow_neg hc_pos.le, inv_inv, mul_comm]
  exact hM1.trans_eq hpow_div

/-! ### 3. Far-zone action lower bound helper & `soft_grow3_of_corr`, `soft_ratio2_of_corr`, `soft_lb_pc_of_corr` -/

/-- When `a ≤ 0`, `0 < Z ≤ CZ / √h`, `-a ≤ Ca / h`, and `Z^2/4 + a ≥ cz1 / (8h)`,
smallness of `h` implies BOTH `max (z2Airy a) 10 ≤ Z` AND `SV ≤ actionWell a Z`. -/
lemma actionWell_ge_of_zeta_lb {cz1 CZ Ca SV : ℝ}
    (hcz1 : 0 < cz1) (hCZ : 0 < CZ) (hCa : 0 ≤ Ca) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ {a Z h : ℝ}, a ≤ 0 → 0 < h → h ≤ h0 → 0 < Z → Z ≤ CZ / Real.sqrt h →
      -a ≤ Ca / h → cz1 / (8 * h) ≤ Z ^ 2 / 4 + a →
      max (z2Airy a) 10 ≤ Z ∧ SV ≤ actionWell a Z := by
  let h1 : ℝ := min (min 1 (cz1 / 201))
    (min (Real.sqrt (cz1 ^ 3 / (4096 * (Ca + 1) + 1)) / 2)
      (cz1 * Real.sqrt cz1 / (32 * CZ * max SV 1 + 1)))
  refine ⟨h1, by positivity, ?_⟩
  intro a Z h ha hh_pos hh_le hZ_pos hZ_ub ha_ub hZa
  have hh_lt_201 : h ≤ cz1 / 201 := hh_le.trans (min_le_left _ _) |>.trans (min_le_right _ _)
  have hp_gt25 : 25 < cz1 / (8 * h) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [hh_lt_201]
  have hp_cube : 2 * (-a) ^ ((1 : ℝ) / 3) < cz1 / (8 * h) := by
    have hh_r : h ≤ Real.sqrt (cz1 ^ 3 / (4096 * (Ca + 1) + 1)) / 2 :=
      hh_le.trans (min_le_right _ _) |>.trans (min_le_left _ _)
    have hh_sq : h ^ 2 < cz1 ^ 3 / (4096 * (Ca + 1)) := by
      have hsq1 : h ^ 2 ≤ (Real.sqrt (cz1 ^ 3 / (4096 * (Ca + 1) + 1)) / 2) ^ 2 :=
        sq_le_sq.mpr (by rw [abs_of_pos hh_pos, abs_of_nonneg (by positivity)]; exact hh_r)
      rw [div_pow, Real.sq_sqrt (by positivity), show (2 : ℝ) ^ 2 = 4 by norm_num] at hsq1
      have hlt : cz1 ^ 3 / (4096 * (Ca + 1) + 1) / 4 < cz1 ^ 3 / (4096 * (Ca + 1)) := by
        rw [div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
        have : 0 < cz1 ^ 3 := pow_pos hcz1 3
        nlinarith
      exact hsq1.trans_lt hlt
    have hcube : (2 * (-a) ^ ((1 : ℝ) / 3)) ^ 3 < (cz1 / (8 * h)) ^ 3 := by
      have hLHS : (2 * (-a) ^ ((1 : ℝ) / 3)) ^ 3 = 8 * (-a) := by
        rw [mul_pow, ← Real.rpow_natCast ((-a) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul (neg_nonneg.mpr ha)]
        norm_num
      have hRHS : (cz1 / (8 * h)) ^ 3 = cz1 ^ 3 / (512 * h ^ 3) := by ring
      rw [hLHS, hRHS, lt_div_iff₀ (by positivity)]
      have h1' : 4096 * Ca * h ^ 2 < cz1 ^ 3 := by
        have h2 : 4096 * (Ca + 1) * h ^ 2 < cz1 ^ 3 := by
          have := (lt_div_iff₀ (by positivity)).mp hh_sq
          linarith
        nlinarith [sq_nonneg h]
      calc 8 * (-a) * (512 * h ^ 3) ≤ 8 * (Ca / h) * (512 * h ^ 3) := by gcongr
        _ = 4096 * Ca * h ^ 2 := by field_simp; ring
        _ < cz1 ^ 3 := h1'
    by_contra hbad
    push_neg at hbad
    have hneg : 0 ≤ cz1 / (8 * h) := by positivity
    exact not_lt_of_ge (pow_le_pow_left₀ hneg hbad 3) hcube
  have h10 : 10 ≤ Z := by
    have hZ2 : 100 < Z ^ 2 := by nlinarith [show 0 ≤ -a from neg_nonneg.mpr ha]
    by_contra hlt
    push_neg at hlt
    nlinarith [hZ_pos]
  have hz2 : z2Airy a ≤ Z := by
    unfold z2Airy
    have harg : -a + 2 * (-a) ^ ((1 : ℝ) / 3) < Z ^ 2 / 4 := by linarith
    have hz2_sq : (2 * Real.sqrt (-a + 2 * (-a) ^ ((1 : ℝ) / 3))) ^ 2 < Z ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by
        have : 0 ≤ (-a) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (neg_nonneg.mpr ha) _
        linarith [neg_nonneg.mpr ha])]
      linarith
    by_contra hlt
    push_neg at hlt
    nlinarith [show 0 ≤ 2 * Real.sqrt (-a + 2 * (-a) ^ ((1 : ℝ) / 3)) by positivity, hZ_pos]
  refine ⟨max_le hz2 h10, ?_⟩
  let z0 := 2 * Real.sqrt (-a)
  let tstar := Real.sqrt (4 * (-a) + cz1 / (4 * h))
  have h4h_pos : 0 < cz1 / (4 * h) := div_pos hcz1 (mul_pos (by norm_num) hh_pos)
  have hz0_le_tstar : z0 ≤ tstar := by
    have hsq : z0 ^ 2 ≤ tstar ^ 2 := by
      dsimp [z0, tstar]
      rw [mul_pow, Real.sq_sqrt (neg_nonneg.mpr ha), Real.sq_sqrt (add_nonneg (mul_nonneg (by norm_num) (neg_nonneg.mpr ha)) h4h_pos.le)]
      linarith
    have hz0_nn : 0 ≤ z0 := by dsimp [z0]; positivity
    have hts_nn : 0 ≤ tstar := Real.sqrt_nonneg _
    nlinarith
  have htstar_sq : tstar ^ 2 = 4 * (-a) + cz1 / (4 * h) :=
    Real.sq_sqrt (add_nonneg (mul_nonneg (by norm_num) (neg_nonneg.mpr ha)) h4h_pos.le)
  have htstar_le_Z : tstar ≤ Z := by
    have hZa4 : cz1 / (4 * h) ≤ 4 * (Z ^ 2 / 4 + a) - cz1 / (4 * h) := by
      have : 4 * (Z ^ 2 / 4 + a) ≥ 4 * (cz1 / (8 * h)) := by linarith
      have : 4 * (cz1 / (8 * h)) = 2 * (cz1 / (4 * h)) := by ring
      linarith
    have hdiff_sq : tstar ^ 2 ≤ Z ^ 2 := by rw [htstar_sq]; linarith
    have hts_nn : 0 ≤ tstar := Real.sqrt_nonneg _
    nlinarith
  have hZ_sub_tstar : cz1 / (8 * CZ) / Real.sqrt h ≤ Z - tstar := by
    have hsum_le : Z + tstar ≤ 2 * CZ / Real.sqrt h := by
      have : tstar ≤ CZ / Real.sqrt h := htstar_le_Z.trans hZ_ub
      have h2 : 2 * CZ / Real.sqrt h = CZ / Real.sqrt h + CZ / Real.sqrt h := by ring
      linarith
    have hsq_diff : cz1 / (4 * h) ≤ (Z - tstar) * (Z + tstar) := by
      have hZa4 : 4 * (Z ^ 2 / 4 + a) ≥ 4 * (cz1 / (8 * h)) := by linarith
      have hring1 : 4 * (Z ^ 2 / 4 + a) = Z ^ 2 - 4 * (-a) := by ring
      have hring2 : 4 * (cz1 / (8 * h)) = 2 * (cz1 / (4 * h)) := by ring
      calc cz1 / (4 * h) ≤ Z ^ 2 - 4 * (-a) - cz1 / (4 * h) := by linarith [hZa4, hring1, hring2]
        _ = Z ^ 2 - (4 * (-a) + cz1 / (4 * h)) := by ring
        _ = Z ^ 2 - tstar ^ 2 := by rw [htstar_sq]
        _ = (Z - tstar) * (Z + tstar) := by ring
    have hdiv1 : (cz1 / (4 * h)) / (2 * CZ / Real.sqrt h) ≤ Z - tstar :=
      (div_le_iff₀ (by positivity)).mpr
        (hsq_diff.trans (mul_le_mul_of_nonneg_left hsum_le (sub_nonneg.mpr htstar_le_Z)))
    have heq1 : (cz1 / (4 * h)) / (2 * CZ / Real.sqrt h) = cz1 / (8 * CZ) / Real.sqrt h := by
      have hsq : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hh_pos.le
      calc (cz1 / (4 * h)) / (2 * CZ / Real.sqrt h)
          = cz1 * Real.sqrt h / (8 * CZ * h) := by field_simp; ring
        _ = cz1 * Real.sqrt h / (8 * CZ * (Real.sqrt h * Real.sqrt h)) := by rw [hsq]
        _ = cz1 / (8 * CZ) / Real.sqrt h := by field_simp
    exact heq1 ▸ hdiv1
  have hc_int : Continuous (fun t : ℝ => Real.sqrt (t ^ 2 / 4 + a)) := by fun_prop
  have hI1 : IntervalIntegrable (fun t : ℝ => Real.sqrt (t ^ 2 / 4 + a))
      MeasureTheory.volume z0 tstar := hc_int.intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun t : ℝ => Real.sqrt (t ^ 2 / 4 + a))
      MeasureTheory.volume tstar Z := hc_int.intervalIntegrable _ _
  have hsplit : ∫ t in z0..Z, Real.sqrt (t ^ 2 / 4 + a) =
      (∫ t in z0..tstar, Real.sqrt (t ^ 2 / 4 + a)) + ∫ t in tstar..Z, Real.sqrt (t ^ 2 / 4 + a) :=
    (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
  have hnonneg1 : 0 ≤ ∫ t in z0..tstar, Real.sqrt (t ^ 2 / 4 + a) :=
    intervalIntegral.integral_nonneg hz0_le_tstar fun t _ => Real.sqrt_nonneg _
  have hlb_int : ∀ t ∈ Icc tstar Z, Real.sqrt (cz1 / (16 * h)) ≤ Real.sqrt (t ^ 2 / 4 + a) := by
    intro t ht
    apply Real.sqrt_le_sqrt
    have hts_nn : 0 ≤ tstar := Real.sqrt_nonneg _
    have htsq : tstar ^ 2 ≤ t ^ 2 := by nlinarith [ht.1]
    have hcz16 : cz1 / (16 * h) = tstar ^ 2 / 4 + a := by rw [htstar_sq]; ring
    linarith [htsq, hcz16]
  have hlow2 := intervalIntegral.integral_mono_on htstar_le_Z intervalIntegrable_const hI2 hlb_int
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlow2
  have hprod : (Z - tstar) * Real.sqrt (cz1 / (16 * h)) ≥ cz1 * Real.sqrt cz1 / (32 * CZ * h) := by
    have hsq_simp : Real.sqrt (cz1 / (16 * h)) = Real.sqrt cz1 / (4 * Real.sqrt h) := by
      rw [Real.sqrt_div hcz1.le, Real.sqrt_mul (by norm_num), show Real.sqrt 16 = 4 by norm_num]
    calc (Z - tstar) * Real.sqrt (cz1 / (16 * h))
        ≥ (cz1 / (8 * CZ) / Real.sqrt h) * (Real.sqrt cz1 / (4 * Real.sqrt h)) := by
            rw [← hsq_simp]; exact mul_le_mul_of_nonneg_right hZ_sub_tstar (Real.sqrt_nonneg _)
      _ = cz1 * Real.sqrt cz1 / (32 * CZ * (Real.sqrt h * Real.sqrt h)) := by ring
      _ = cz1 * Real.sqrt cz1 / (32 * CZ * h) := by rw [Real.mul_self_sqrt hh_pos.le]
  have hh_sv : h ≤ cz1 * Real.sqrt cz1 / (32 * CZ * max SV 1 + 1) :=
    hh_le.trans (min_le_right _ _) |>.trans (min_le_right _ _)
  have hsv_prod : SV ≤ cz1 * Real.sqrt cz1 / (32 * CZ * h) := by
    have hden_sv : 0 < 32 * CZ * max SV 1 + 1 := by positivity
    have h1' : (32 * CZ * max SV 1 + 1) * h ≤ cz1 * Real.sqrt cz1 :=
      (le_div_iff₀' hden_sv).mp hh_sv
    have h0' : max SV 1 * (32 * CZ * h) ≤ (32 * CZ * max SV 1 + 1) * h := by linarith [hh_pos.le]
    have h2' : SV * (32 * CZ * h) ≤ max SV 1 * (32 * CZ * h) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    rw [le_div_iff₀ (by positivity)]
    exact (h2'.trans h0').trans h1'
  have hact_eq : actionWell a Z = ∫ t in z0..Z, Real.sqrt (t ^ 2 / 4 + a) := rfl
  have htot : cz1 * Real.sqrt cz1 / (32 * CZ * h) ≤ ∫ t in z0..Z, Real.sqrt (t ^ 2 / 4 + a) := by
    rw [hsplit]; linarith [hnonneg1, hprod, hlow2]
  rw [hact_eq]
  exact hsv_prod.trans htot

/-! ### Helper: Model combinations -/

/-- Model combination at row `k` on patch 3 (`SoftEdgeChart.grow3`). -/
def softModelPhi (U V : ℝ → ℝ → ℝ) (A B a h Z : ℝ) : ℝ :=
  A * pcSwap U V a 0 Z + h * B * (Real.sqrt h * deriv (pcSwap U V a 0) Z)

/-- Model combination (`alpha = 1`, patch 2) at the overlap `j_1` (`SoftEdgeChart.ratio2`). -/
def minusModelPhi1 (U V : ℝ → ℝ → ℝ) (A B a h Z : ℝ) : ℝ :=
  A * pcMinus U V a 1 Z + h * B * (Real.sqrt h * deriv (pcMinus U V a 1) Z)

/-- Model combination (`alpha = 0`, patch 2) on the left of the PC well (`SoftEdgeChart.lb_pc`). -/
def minusModelPhi0 (U V : ℝ → ℝ → ℝ) (A B a h Z : ℝ) : ℝ :=
  A * pcMinus U V a 0 Z + h * B * (Real.sqrt h * deriv (pcMinus U V a 0) Z)

/-- Weber model combination (`alpha = 0`) (`BulkWeberChart.seed_pos`, `collar_lb`, `SoftEdgeChart.collar_lbW`). -/
def weberModelPhi (U : ℝ → ℝ → ℝ) (A B h : ℝ) (j : ℕ) (Z : ℝ) : ℝ :=
  A * ut U (-((j : ℝ) + 1 / 2)) Z + h * B * (Real.sqrt h * deriv (ut U (-((j : ℝ) + 1 / 2))) Z)

private lemma h_mul_k2_le {h a Z CZ Cneg Cpos : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hCZ : 0 ≤ CZ) (hCn : 0 ≤ Cneg) (hCp : 0 ≤ Cpos)
    (hZ : |Z| ≤ CZ / Real.sqrt h) (hlo : -Cneg / h ≤ a) (hhi : a ≤ Cpos / h) :
    h * k2 a Z ≤ CZ ^ 2 / 4 + Cneg + Cpos + 1 := by
  have hZ2 : Z ^ 2 / 4 ≤ (CZ ^ 2 / 4) / h := by
    have hZ_abs_sq : Z ^ 2 ≤ (CZ / Real.sqrt h) ^ 2 := by
      rw [← sq_abs Z]
      exact sq_le_sq.mpr (by rw [abs_of_nonneg (abs_nonneg Z), abs_of_nonneg (div_nonneg hCZ (Real.sqrt_nonneg h))]; exact hZ)
    calc Z ^ 2 / 4 ≤ (CZ / Real.sqrt h) ^ 2 / 4 := by gcongr
      _ = (CZ ^ 2 / 4) / h := by rw [div_pow, Real.sq_sqrt hh.le]; ring
  have habs_a : |a| ≤ (Cneg + Cpos) / h := by
    rw [abs_le]
    have h1 : -((Cneg + Cpos) / h) ≤ -Cneg / h := by
      calc -((Cneg + Cpos) / h) ≤ -(Cneg / h) := neg_le_neg (div_le_div_of_nonneg_right (by linarith) hh.le)
        _ = -Cneg / h := by ring
    have h2 : Cpos / h ≤ (Cneg + Cpos) / h := div_le_div_of_nonneg_right (by linarith) hh.le
    constructor <;> linarith
  have hp1 : |Z ^ 2 / 4 + a| ≤ (CZ ^ 2 / 4 + Cneg + Cpos + 1) / h := by
    have hnn : 0 ≤ Z ^ 2 / 4 := by positivity
    calc |Z ^ 2 / 4 + a| ≤ |Z ^ 2 / 4| + |a| := abs_add_le (Z ^ 2 / 4) a
      _ = Z ^ 2 / 4 + |a| := by rw [abs_of_nonneg hnn]
      _ ≤ (CZ ^ 2 / 4) / h + (Cneg + Cpos) / h := add_le_add hZ2 habs_a
      _ ≤ (CZ ^ 2 / 4 + Cneg + Cpos + 1) / h := by rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hh.le
  have hp2 : max |a| 1 ^ ((1 : ℝ) / 3) ≤ (CZ ^ 2 / 4 + Cneg + Cpos + 1) / h := by
    have hm1 : 1 ≤ max |a| 1 := le_max_right _ _
    have hm_pow : max |a| 1 ^ ((1 : ℝ) / 3) ≤ max |a| 1 :=
      (Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)).trans_eq (Real.rpow_one _)
    have h1h : 1 ≤ 1 / h := (one_le_div hh).mpr hh1
    have hma : max |a| 1 ≤ (Cneg + Cpos + 1) / h := by
      refine max_le (habs_a.trans (div_le_div_of_nonneg_right (by linarith) hh.le)) ?_
      exact h1h.trans (div_le_div_of_nonneg_right (by linarith) hh.le)
    have hfin : (Cneg + Cpos + 1) / h ≤ (CZ ^ 2 / 4 + Cneg + Cpos + 1) / h :=
      div_le_div_of_nonneg_right (by linarith [sq_nonneg CZ]) hh.le
    exact hm_pow.trans (hma.trans hfin)
  have hk : k2 a Z ≤ (CZ ^ 2 / 4 + Cneg + Cpos + 1) / h := max_le hp1 hp2
  calc h * k2 a Z ≤ h * ((CZ ^ 2 / 4 + Cneg + Cpos + 1) / h) := mul_le_mul_of_nonneg_left hk hh.le
    _ = CZ ^ 2 / 4 + Cneg + Cpos + 1 := by field_simp

/-- **Patch-3 growing-profile bounds (`SoftEdgeChart.grow3`)** modulo `corr_PC` and `A1 ≤ (1 + CAl h) A2`. -/
theorem soft_grow3_of_corr {gm CBc CAl cz1 CZ Ca aHi : ℝ}
    (hgm : 0 < gm) (hCBc : 0 ≤ CBc) (hCAl : 0 ≤ CAl) (hcz1 : 0 < cz1) (hCZ : 0 < CZ)
    (hCa : 0 ≤ Ca) (haHi_nn : 0 ≤ aHi) :
    ∃ cgr Cgr h0 : ℝ, 0 < cgr ∧ 0 ≤ Cgr ∧ 0 < h0 ∧
      ∀ {h A1 A2 B1 B2 a Z1 Z2 : ℝ},
        0 < h → h ≤ h0 → a ≤ aHi → (a ≤ 0 → -a ≤ Ca / h) →
        0 < Z1 → Z1 ≤ Z2 → Z2 ≤ CZ / Real.sqrt h →
        cz1 / (8 * h) ≤ Z1 ^ 2 / 4 + a →
        gm ≤ A1 → gm ≤ A2 → |B1| ≤ CBc → |B2| ≤ CBc → A1 ≤ (1 + CAl * h) * A2 →
        cgr * Eswap a Z1 * Mbal a Z1 ≤ softModelPhi pcU pcV A1 B1 a h Z1 ∧
        cgr * Eswap a Z2 * Mbal a Z2 ≤ softModelPhi pcU pcV A2 B2 a h Z2 ∧
        softModelPhi pcU pcV A1 B1 a h Z1 ≤ (1 + Cgr * h) * softModelPhi pcU pcV A2 B2 a h Z2 := by
  obtain ⟨cPC, CPC, env⟩ := pcEnvelopeFacts
  obtain ⟨cV, SV, hcV, hSV, hVfar⟩ := pcV_far_pos_and_growth
  obtain ⟨cU, hcU, hUfar⟩ := pcU_neg_pos_and_growth
  obtain ⟨hAct, hhAct, hact_far⟩ := actionWell_ge_of_zeta_lb hcz1 hCZ hCa
  set c0 : ℝ := min cV cU
  have hc0 : 0 < c0 := lt_min hcV hcU
  set Cd : ℝ := max (CPC / cV) 4
  have hCd : 0 < Cd := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  set Ck2 : ℝ := CZ ^ 2 / 4 + Ca + aHi + 1
  have hCk2 : 0 ≤ Ck2 := by positivity
  set Merr : ℝ := CBc * Cd * Real.sqrt Ck2
  have hMerr : 0 ≤ Merr := by positivity
  set cgr : ℝ := gm / 2 * c0
  set Cgr : ℝ := CAl + 6 * Merr / gm
  set h0 : ℝ := min 1 (min hAct (min (gm / (4 * (Merr + 1))) (1 / (Cgr + 1))))
  refine ⟨cgr, Cgr, h0, by positivity, by positivity, by positivity, ?_⟩
  intro h A1 A2 B1 B2 a Z1 Z2 hh hh0 haHi_le ha_neg hZ1 hZ12 hZ2 hZa1 hA1 hA2 hB1 hB2 hA12
  have hh1 : h ≤ 1 := hh0.trans (min_le_left _ _)
  have hha : h ≤ hAct := hh0.trans (min_le_right _ _) |>.trans (min_le_left _ _)
  have hhMerr : h * Merr ≤ gm / 4 := by
    have h1 : h ≤ gm / (4 * (Merr + 1)) :=
      hh0.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans (min_le_left _ _)
    have h2 : 4 * (Merr + 1) * h ≤ gm := (le_div_iff₀' (by positivity)).mp h1
    nlinarith [hh]
  have hhCgr : Cgr * h ≤ 1 := by
    have h1 : h ≤ 1 / (Cgr + 1) :=
      hh0.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans (min_le_right _ _)
    have h2 : (Cgr + 1) * h ≤ 1 := (le_div_iff₀' (by positivity)).mp h1
    nlinarith [hh]
  have h_a_lo : -Ca / h ≤ a := by
    by_cases ha0 : a ≤ 0
    · rw [neg_div]; linarith [ha_neg ha0]
    · have : -Ca / h ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hCa) hh.le
      linarith
  have h_a_hi : a ≤ aHi / h := haHi_le.trans ((le_div_iff₀ hh).mpr (by nlinarith [hh1]))
  have hw_pt : ∀ Z ∈ Icc Z1 Z2,
      c0 * Eswap a Z * Mbal a Z ≤ pcSwap pcU pcV a 0 Z ∧
      0 ≤ deriv (pcSwap pcU pcV a 0) Z ∧
      deriv (pcSwap pcU pcV a 0) Z ≤ Cd * Real.sqrt (k2 a Z) * pcSwap pcU pcV a 0 Z := by
    intro Z hZ
    have hZp : 0 < Z := hZ1.trans_le hZ.1
    have hZub : Z ≤ CZ / Real.sqrt h := hZ.2.trans hZ2
    have hZa : cz1 / (8 * h) ≤ Z ^ 2 / 4 + a := by nlinarith [hZ.1, hZ1]
    by_cases ha0 : a ≤ 0
    · obtain ⟨hz2_le, hact_ge⟩ := hact_far ha0 hh hha hZp hZub (ha_neg ha0) hZa
      obtain ⟨hvt_lo, hvt_gr⟩ := hVfar a ha0 Z hz2_le hact_ge
      have h_eq : pcSwap pcU pcV a 0 = vt pcV a := by
        ext w; change (if a ≤ 0 then vt pcV a w else kappaBal a * pcU a (-w)) = vt pcV a w
        rw [if_pos ha0]
      have hE_eq : Eswap a Z = (Ewell a Z)⁻¹ := Eswap_eq_Ewell_inv_of_nonpos ha0 hZp.le
      have hwell := (env.env_well a ha0 Z hZp.le).2
      have hk2p : 0 < k2 a Z := k2_pos a Z
      have hderiv_sq : deriv (vt pcV a) Z ≤ (CPC * (Ewell a Z)⁻¹ * Mbal a Z) * Real.sqrt (k2 a Z) := by
        have hv1 : Real.sqrt ((deriv (vt pcV a) Z) ^ 2 / k2 a Z) ≤
            Real.sqrt (vt pcV a Z ^ 2 + (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) Z) ^ 2 / k2 a Z) := by
          apply Real.sqrt_le_sqrt
          have hdeq : deriv (vt pcV a) Z = Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) Z := by
            unfold vt; exact deriv_const_mul _ ((pcSmoothFacts.slice_V a).differentiable (by simp) Z)
          rw [hdeq]; linarith [sq_nonneg (vt pcV a Z)]
        have hv2 : |deriv (vt pcV a) Z| / Real.sqrt (k2 a Z) ≤ CPC * (Ewell a Z)⁻¹ * Mbal a Z := by
          rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_div (sq_nonneg _)]
          exact hv1.trans hwell
        calc deriv (vt pcV a) Z ≤ |deriv (vt pcV a) Z| := le_abs_self _
          _ ≤ CPC * (Ewell a Z)⁻¹ * Mbal a Z * Real.sqrt (k2 a Z) := (div_le_iff₀ (Real.sqrt_pos.mpr hk2p)).mp hv2
      have hderiv_ub : deriv (vt pcV a) Z ≤ Cd * Real.sqrt (k2 a Z) * vt pcV a Z := by
        have hcdiv : (Ewell a Z)⁻¹ * Mbal a Z ≤ vt pcV a Z / cV := (le_div_iff₀ hcV).mpr (by linarith [hvt_lo])
        have hCPC_nn : 0 ≤ CPC := (lt_of_lt_of_le env.cPC_pos env.cPC_le).le
        have h1 : CPC * ((Ewell a Z)⁻¹ * Mbal a Z) * Real.sqrt (k2 a Z) ≤
            CPC * (vt pcV a Z / cV) * Real.sqrt (k2 a Z) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcdiv hCPC_nn) (Real.sqrt_nonneg _)
        have h2 : CPC * (vt pcV a Z / cV) * Real.sqrt (k2 a Z) = (CPC / cV) * Real.sqrt (k2 a Z) * vt pcV a Z := by ring
        have hv_pos : 0 < vt pcV a Z :=
          (mul_pos (mul_pos hcV (inv_pos.mpr (Ewell_pos a Z))) (Mbal_pos a Z)).trans_le hvt_lo
        have h3 : (CPC / cV) * Real.sqrt (k2 a Z) * vt pcV a Z ≤ Cd * Real.sqrt (k2 a Z) * vt pcV a Z :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) hv_pos.le
        linarith [hderiv_sq, h1, h2, h3]
      have hderiv_nn : 0 ≤ deriv (vt pcV a) Z := by
        have hvnn := (mul_pos (mul_pos hcV (inv_pos.mpr (Ewell_pos a Z))) (Mbal_pos a Z) |>.trans_le hvt_lo).le
        exact (by positivity : 0 ≤ (1 / 4 : ℝ) * Real.sqrt (k2 a Z) * vt pcV a Z).trans hvt_gr
      rw [h_eq, hE_eq]
      refine ⟨?_, hderiv_nn, hderiv_ub⟩
      have hc0V : c0 ≤ cV := min_le_left _ _
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc0V (inv_nonneg.mpr (Ewell_pos a Z).le))
        (Mbal_pos a Z).le).trans hvt_lo
    · have ha_pos : 0 < a := lt_of_not_ge ha0
      obtain ⟨hU_lo, hU_nn, hU_ub⟩ := hUfar a ha_pos Z hZp.le
      have h_eq : pcSwap pcU pcV a 0 = fun w => kappaBal a * pcU a (-w) := by
        ext w; change (if a ≤ 0 then vt pcV a w else kappaBal a * pcU a (-w)) = kappaBal a * pcU a (-w)
        rw [if_neg ha0]
      have hE_eq : Eswap a Z = (Ebar a Z)⁻¹ := Eswap_eq_Ebar_inv_of_pos ha_pos Z
      rw [h_eq, hE_eq]
      have hc0U : c0 ≤ cU := min_le_right _ _
      have hu_nn : 0 ≤ kappaBal a * pcU a (-Z) :=
        (mul_pos (mul_pos hcU (inv_pos.mpr (Ebar_pos a Z))) (Mbal_pos a Z)).le.trans hU_lo
      have h4Cd : (4 : ℝ) ≤ Cd := le_max_right _ _
      refine ⟨?_, hU_nn, ?_⟩
      · exact (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc0U (inv_nonneg.mpr (Ebar_pos a Z).le))
          (Mbal_pos a Z).le).trans hU_lo
      · exact hU_ub.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h4Cd (Real.sqrt_nonneg _)) hu_nn)
  have hw_mono : pcSwap pcU pcV a 0 Z1 ≤ pcSwap pcU pcV a 0 Z2 := by
    have hdiff : Differentiable ℝ (pcSwap pcU pcV a 0) := by
      by_cases ha0 : a ≤ 0
      · have h_eq : pcSwap pcU pcV a 0 = vt pcV a := by
          ext w; change (if a ≤ 0 then vt pcV a w else kappaBal a * pcU a (-w)) = vt pcV a w; rw [if_pos ha0]
        rw [h_eq]; exact vt_diff a
      · have h_eq : pcSwap pcU pcV a 0 = fun w => kappaBal a * pcU a (-w) := by
          ext w; change (if a ≤ 0 then vt pcV a w else kappaBal a * pcU a (-w)) = kappaBal a * pcU a (-w); rw [if_neg ha0]
        rw [h_eq]; exact kappaU_neg_diff a
    exact monotoneOn_of_deriv_nonneg (convex_Icc Z1 Z2) hdiff.continuous.continuousOn
      (fun Z _ => (hdiff Z).differentiableWithinAt) (fun Z hZ => (hw_pt Z (interior_subset hZ)).2.1)
      ⟨le_rfl, hZ12⟩ ⟨hZ12, le_rfl⟩ hZ12
  have hphi_bounds : ∀ {A B Z : ℝ}, Z ∈ Icc Z1 Z2 → gm ≤ A → |B| ≤ CBc →
      (A - h * Merr) * pcSwap pcU pcV a 0 Z ≤ softModelPhi pcU pcV A B a h Z ∧
      softModelPhi pcU pcV A B a h Z ≤ (A + h * Merr) * pcSwap pcU pcV a 0 Z := by
    intro A B Z hZ _ hB
    obtain ⟨hw_lo, hd_nn, hd_ub⟩ := hw_pt Z hZ
    have hZp : 0 < Z := hZ1.trans_le hZ.1
    have hhk2 : h * k2 a Z ≤ Ck2 :=
      h_mul_k2_le hh hh1 hCZ.le hCa haHi_nn (by rw [abs_of_pos hZp]; exact hZ.2.trans hZ2) h_a_lo h_a_hi
    have hsq_k2 : Real.sqrt h * Real.sqrt (k2 a Z) ≤ Real.sqrt Ck2 := by
      rw [← Real.sqrt_mul hh.le]; exact Real.sqrt_le_sqrt hhk2
    have hw_nn : 0 ≤ pcSwap pcU pcV a 0 Z :=
      ((mul_pos (mul_pos hc0 (Eswap_pos' a Z)) (Mbal_pos a Z)).trans_le hw_lo).le
    have hcorr_abs : |h * B * (Real.sqrt h * deriv (pcSwap pcU pcV a 0) Z)| ≤ h * Merr * pcSwap pcU pcV a 0 Z := by
      calc |h * B * (Real.sqrt h * deriv (pcSwap pcU pcV a 0) Z)|
          = h * |B| * (Real.sqrt h * |deriv (pcSwap pcU pcV a 0) Z|) := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_pos hh, abs_of_nonneg (Real.sqrt_nonneg h)]
        _ = h * |B| * (Real.sqrt h * deriv (pcSwap pcU pcV a 0) Z) := by rw [abs_of_nonneg hd_nn]
        _ ≤ h * CBc * (Real.sqrt h * (Cd * Real.sqrt (k2 a Z) * pcSwap pcU pcV a 0 Z)) := by gcongr
        _ = h * (CBc * Cd * (Real.sqrt h * Real.sqrt (k2 a Z))) * pcSwap pcU pcV a 0 Z := by ring
        _ ≤ h * (CBc * Cd * Real.sqrt Ck2) * pcSwap pcU pcV a 0 Z := by gcongr
    have habs := abs_le.mp hcorr_abs
    unfold softModelPhi
    constructor <;> linarith [habs.1, habs.2]
  obtain ⟨h1_lo, h1_hi⟩ := hphi_bounds ⟨le_rfl, hZ12⟩ hA1 hB1
  obtain ⟨h2_lo, _⟩ := hphi_bounds ⟨hZ12, le_rfl⟩ hA2 hB2
  have hw1_lo := (hw_pt Z1 ⟨le_rfl, hZ12⟩).1
  have hw2_lo := (hw_pt Z2 ⟨hZ12, le_rfl⟩).1
  have hw1_nn : 0 ≤ pcSwap pcU pcV a 0 Z1 :=
    (mul_pos (mul_pos hc0 (Eswap_pos' a Z1)) (Mbal_pos a Z1)).le.trans hw1_lo
  have hw2_nn : 0 ≤ pcSwap pcU pcV a 0 Z2 := hw1_nn.trans hw_mono
  refine ⟨?_, ?_, ?_⟩
  · have hA1' : gm / 2 ≤ A1 - h * Merr := by linarith
    calc cgr * Eswap a Z1 * Mbal a Z1 = gm / 2 * (c0 * Eswap a Z1 * Mbal a Z1) := by ring
      _ ≤ gm / 2 * pcSwap pcU pcV a 0 Z1 := by gcongr
      _ ≤ (A1 - h * Merr) * pcSwap pcU pcV a 0 Z1 := by gcongr
      _ ≤ softModelPhi pcU pcV A1 B1 a h Z1 := h1_lo
  · have hA2' : gm / 2 ≤ A2 - h * Merr := by linarith
    calc cgr * Eswap a Z2 * Mbal a Z2 = gm / 2 * (c0 * Eswap a Z2 * Mbal a Z2) := by ring
      _ ≤ gm / 2 * pcSwap pcU pcV a 0 Z2 := by gcongr
      _ ≤ (A2 - h * Merr) * pcSwap pcU pcV a 0 Z2 := by gcongr
      _ ≤ softModelPhi pcU pcV A2 B2 a h Z2 := h2_lo
  · have hCd_nn : 0 ≤ Cd := by dsimp [Cd]; positivity
    have hCk2_nn : 0 ≤ Ck2 := by dsimp [Ck2]; positivity
    have hMerr_nn' : 0 ≤ Merr := by dsimp [Merr]; positivity
    have hdif : 6 * Merr ≤ (Cgr - CAl) * A2 := by
      have h6 : 6 * Merr = (Cgr - CAl) * gm := by dsimp [Cgr]; field_simp; ring
      have hdiff_eq : Cgr - CAl = 6 * Merr / gm := by dsimp [Cgr]; ring
      rw [h6, hdiff_eq]
      exact mul_le_mul_of_nonneg_left hA2 (div_nonneg (mul_nonneg (by norm_num) hMerr_nn') hgm.le)
    have hdif_h : 6 * (h * Merr) ≤ (Cgr - CAl) * h * A2 := by
      calc 6 * (h * Merr) = h * (6 * Merr) := by ring
        _ ≤ h * ((Cgr - CAl) * A2) := mul_le_mul_of_nonneg_left hdif hh.le
        _ = (Cgr - CAl) * h * A2 := by ring
    have hMerr_nn : 0 ≤ h * Merr := mul_nonneg hh.le hMerr_nn'
    have hCgr_err : (1 + Cgr * h) * (h * Merr) ≤ 2 * (h * Merr) :=
      mul_le_mul_of_nonneg_right (by linarith) hMerr_nn
    have hcoef : A1 + h * Merr ≤ (1 + Cgr * h) * (A2 - h * Merr) := by
      have h1 : A1 + h * Merr ≤ (1 + CAl * h) * A2 + h * Merr := add_le_add hA12 le_rfl
      have h2 : (1 + CAl * h) * A2 + h * Merr = (1 + Cgr * h) * A2 - (Cgr - CAl) * h * A2 + h * Merr := by ring
      have h3 : (1 + Cgr * h) * A2 - 5 * (h * Merr) ≤ (1 + Cgr * h) * A2 - (1 + Cgr * h) * (h * Merr) := by
        linarith [hCgr_err, hMerr_nn]
      have h4 : (1 + Cgr * h) * A2 - (1 + Cgr * h) * (h * Merr) = (1 + Cgr * h) * (A2 - h * Merr) := by ring
      linarith
    have hCgr_nn : 0 ≤ Cgr := by
      dsimp [Cgr]
      exact add_nonneg hCAl (div_nonneg (mul_nonneg (by norm_num) hMerr_nn') hgm.le)
    have h1_lt : 0 ≤ 1 + Cgr * h := by linarith [mul_nonneg hCgr_nn hh.le]
    calc softModelPhi pcU pcV A1 B1 a h Z1
        ≤ (A1 + h * Merr) * pcSwap pcU pcV a 0 Z1 := h1_hi
      _ ≤ (A1 + h * Merr) * pcSwap pcU pcV a 0 Z2 := mul_le_mul_of_nonneg_left hw_mono (by linarith)
      _ ≤ (1 + Cgr * h) * (A2 - h * Merr) * pcSwap pcU pcV a 0 Z2 :=
            mul_le_mul_of_nonneg_right hcoef hw2_nn
      _ = (1 + Cgr * h) * ((A2 - h * Merr) * pcSwap pcU pcV a 0 Z2) := by ring
      _ ≤ (1 + Cgr * h) * softModelPhi pcU pcV A2 B2 a h Z2 :=
            mul_le_mul_of_nonneg_left h2_lo h1_lt

/-- **Forward overlap decay ratio (`SoftEdgeChart.ratio2`)** across `j_1` modulo `corr_PC` and `A2 ≤ (1 + CAl h) A1`. -/
theorem soft_ratio2_of_corr {gm CBc CAl cz1 CZ Ca : ℝ}
    (hgm : 0 < gm) (hCBc : 0 ≤ CBc) (hCAl : 0 ≤ CAl) (hcz1 : 0 < cz1) (hCZ : 0 < CZ)
    (hCa : 0 ≤ Ca) :
    ∃ C2 h0 : ℝ, 0 ≤ C2 ∧ 0 < h0 ∧
      ∀ {h A1 A2 B1 B2 a Z1 Z2 : ℝ},
        0 < h → h ≤ h0 → (a ≤ 0 → -a ≤ Ca / h) → (0 < a → a ≤ Ca / h) →
        -(CZ / Real.sqrt h) ≤ Z1 → Z1 ≤ Z2 → Z2 < 0 →
        cz1 / (8 * h) ≤ Z2 ^ 2 / 4 + a →
        gm ≤ A1 → gm ≤ A2 → |B1| ≤ CBc → |B2| ≤ CBc → A2 ≤ (1 + CAl * h) * A1 →
        |minusModelPhi1 pcU pcV A2 B2 a h Z2| ≤ (1 + C2 * h) * |minusModelPhi1 pcU pcV A1 B1 a h Z1| := by
  obtain ⟨cPC, CPC, env⟩ := pcEnvelopeFacts
  obtain ⟨cV, SV, hcV, hSV, hVfar⟩ := pcV_far_pos_and_growth
  obtain ⟨cU, hcU, hUfar⟩ := pcU_neg_pos_and_growth
  obtain ⟨hAct, hhAct, hact_far⟩ := actionWell_ge_of_zeta_lb hcz1 hCZ hCa
  set c0 : ℝ := min cV cU
  have hc0 : 0 < c0 := lt_min hcV hcU
  set Cd : ℝ := max (CPC / cV) 4
  set Ck2 : ℝ := CZ ^ 2 / 4 + Ca + Ca + 1
  set Merr : ℝ := CBc * Cd * Real.sqrt Ck2
  set C2 : ℝ := CAl + 6 * Merr / gm
  set h0 : ℝ := min 1 (min hAct (min (gm / (4 * (Merr + 1))) (1 / (C2 + 1))))
  refine ⟨C2, h0, by positivity, by positivity, ?_⟩
  intro h A1 A2 B1 B2 a Z1 Z2 hh hh0 ha_neg ha_pos hZ1_lb hZ12 hZ2_neg hZa2 hA1 hA2 hB1 hB2 hA21
  have hh1 : h ≤ 1 := hh0.trans (min_le_left _ _)
  have hha : h ≤ hAct := hh0.trans (min_le_right _ _) |>.trans (min_le_left _ _)
  have hhMerr : h * Merr ≤ gm / 4 := by
    have h1 : h ≤ gm / (4 * (Merr + 1)) :=
      hh0.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans (min_le_left _ _)
    have h2 : 4 * (Merr + 1) * h ≤ gm := (le_div_iff₀' (by positivity)).mp h1
    nlinarith [hh]
  have hhC2 : C2 * h ≤ 1 := by
    have h1 : h ≤ 1 / (C2 + 1) :=
      hh0.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans (min_le_right _ _)
    have h2 : (C2 + 1) * h ≤ 1 := (le_div_iff₀' (by positivity)).mp h1
    nlinarith [hh]
  have h_a_lo : -Ca / h ≤ a := by
    by_cases ha0 : a ≤ 0
    · rw [neg_div]; linarith [ha_neg ha0]
    · exact le_trans (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hCa) hh.le) (le_of_not_ge ha0)
  have h_a_hi : a ≤ Ca / h := by
    by_cases ha0 : 0 < a
    · exact ha_pos ha0
    · exact (not_lt.mp ha0).trans (div_nonneg hCa hh.le)
  let g : ℝ → ℝ := fun z => if a ≤ 0 then vt pcV a z else kappaBal a * pcU a (-z)
  have hg_pt : ∀ z ∈ Icc (-Z2) (-Z1),
      0 < g z ∧ 0 ≤ deriv g z ∧ deriv g z ≤ Cd * Real.sqrt (k2 a z) * g z := by
    intro z hz
    have hzp : 0 < z := (neg_pos.mpr hZ2_neg).trans_le hz.1
    have hzub : z ≤ CZ / Real.sqrt h := hz.2.trans (by linarith)
    have hZa : cz1 / (8 * h) ≤ z ^ 2 / 4 + a := by nlinarith [hz.1, hZ2_neg]
    by_cases ha0 : a ≤ 0
    · have hg_eq : g = vt pcV a := by ext w; simp [g, ha0]
      obtain ⟨hz2_le, hact_ge⟩ := hact_far ha0 hh hha hzp hzub (ha_neg ha0) hZa
      obtain ⟨hvt_lo, hvt_gr⟩ := hVfar a ha0 z hz2_le hact_ge
      have hv_pos : 0 < vt pcV a z :=
        (mul_pos (mul_pos hcV (inv_pos.mpr (Ewell_pos a z))) (Mbal_pos a z)).trans_le hvt_lo
      have hwell := (env.env_well a ha0 z hzp.le).2
      have hk2p : 0 < k2 a z := k2_pos a z
      have hderiv_sq : deriv (vt pcV a) z ≤ (CPC * (Ewell a z)⁻¹ * Mbal a z) * Real.sqrt (k2 a z) := by
        have hv1 : Real.sqrt ((deriv (vt pcV a) z) ^ 2 / k2 a z) ≤
            Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) := by
          apply Real.sqrt_le_sqrt
          have hdeq : deriv (vt pcV a) z = Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z := by
            unfold vt; exact deriv_const_mul _ ((pcSmoothFacts.slice_V a).differentiable (by simp) z)
          rw [hdeq]; linarith [sq_nonneg (vt pcV a z)]
        have hv2 : |deriv (vt pcV a) z| / Real.sqrt (k2 a z) ≤ CPC * (Ewell a z)⁻¹ * Mbal a z := by
          rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_div (sq_nonneg _)]
          exact hv1.trans hwell
        calc deriv (vt pcV a) z ≤ |deriv (vt pcV a) z| := le_abs_self _
          _ ≤ CPC * (Ewell a z)⁻¹ * Mbal a z * Real.sqrt (k2 a z) := (div_le_iff₀ (Real.sqrt_pos.mpr hk2p)).mp hv2
      have hderiv_ub : deriv (vt pcV a) z ≤ Cd * Real.sqrt (k2 a z) * vt pcV a z := by
        have hcdiv : (Ewell a z)⁻¹ * Mbal a z ≤ vt pcV a z / cV := (le_div_iff₀ hcV).mpr (by linarith [hvt_lo])
        have hCPC_nn : 0 ≤ CPC := (lt_of_lt_of_le env.cPC_pos env.cPC_le).le
        have h1 : CPC * ((Ewell a z)⁻¹ * Mbal a z) * Real.sqrt (k2 a z) ≤
            CPC * (vt pcV a z / cV) * Real.sqrt (k2 a z) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcdiv hCPC_nn) (Real.sqrt_nonneg _)
        have h2 : CPC * (vt pcV a z / cV) * Real.sqrt (k2 a z) = (CPC / cV) * Real.sqrt (k2 a z) * vt pcV a z := by ring
        have h3 : (CPC / cV) * Real.sqrt (k2 a z) * vt pcV a z ≤ Cd * Real.sqrt (k2 a z) * vt pcV a z := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) hv_pos.le
        linarith [hderiv_sq, h1, h2, h3]
      rw [hg_eq]
      exact ⟨hv_pos, (by positivity : 0 ≤ (1 / 4 : ℝ) * Real.sqrt (k2 a z) * vt pcV a z).trans hvt_gr, hderiv_ub⟩
    · have ha_pos : 0 < a := lt_of_not_ge ha0
      have hg_eq : g = fun w => kappaBal a * pcU a (-w) := by ext w; simp [g, ha0]
      obtain ⟨hU_lo, hU_nn, hU_ub⟩ := hUfar a ha_pos z hzp.le
      have hu_pos : 0 < kappaBal a * pcU a (-z) :=
        (mul_pos (mul_pos hcU (inv_pos.mpr (Ebar_pos a z))) (Mbal_pos a z)).trans_le hU_lo
      rw [hg_eq]
      refine ⟨hu_pos, hU_nn, ?_⟩
      calc deriv (fun w => kappaBal a * pcU a (-w)) z
          ≤ 4 * Real.sqrt (k2 a z) * (kappaBal a * pcU a (-z)) := hU_ub
        _ ≤ Cd * Real.sqrt (k2 a z) * (kappaBal a * pcU a (-z)) := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)) hu_pos.le
  have hg_mono : g (-Z2) ≤ g (-Z1) := by
    have hdiff : Differentiable ℝ g := by
      by_cases ha0 : a ≤ 0
      · have hg_eq : g = vt pcV a := by ext w; simp [g, ha0]
        rw [hg_eq]; exact vt_diff a
      · have hg_eq : g = fun w => kappaBal a * pcU a (-w) := by ext w; simp [g, ha0]
        rw [hg_eq]; exact kappaU_neg_diff a
    exact monotoneOn_of_deriv_nonneg (convex_Icc (-Z2) (-Z1)) hdiff.continuous.continuousOn
      (fun z _ => (hdiff z).differentiableWithinAt) (fun z hz => (hg_pt z (interior_subset hz)).2.1)
      ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  have hpc_eq : ∀ Z : ℝ, pcMinus pcU pcV a 1 Z = -g (-Z) ∧ deriv (pcMinus pcU pcV a 1) Z = deriv g (-Z) := by
    intro Z
    by_cases ha0 : a ≤ 0
    · have hp1 : pcMinus pcU pcV a 1 = fun w => -vt pcV a (-w) := by
        ext w; change (if a ≤ 0 then -vt pcV a (-w) else -(kappaBal a * pcU a w)) = -vt pcV a (-w); rw [if_pos ha0]
      have hg_eq : g = vt pcV a := by ext w; simp [g, ha0]
      rw [hp1, hg_eq]
      refine ⟨rfl, ?_⟩
      calc deriv (fun w => -vt pcV a (-w)) Z
          = -deriv (fun w => vt pcV a (-w)) Z :=
              deriv_neg_fun_of_diff ((vt_diff a).comp differentiable_neg) Z
        _ = -(-deriv (vt pcV a) (-Z)) := by rw [deriv_comp_neg_of_diff (vt_diff a)]
        _ = deriv (vt pcV a) (-Z) := neg_neg _
    · have hp1 : pcMinus pcU pcV a 1 = fun w => -(kappaBal a * pcU a w) := by
        ext w; change (if a ≤ 0 then -vt pcV a (-w) else -(kappaBal a * pcU a w)) = -(kappaBal a * pcU a w); rw [if_neg ha0]
      have hg_eq : g = fun w => kappaBal a * pcU a (-w) := by ext w; simp [g, ha0]
      rw [hp1, hg_eq]
      refine ⟨by dsimp; rw [neg_neg], ?_⟩
      calc deriv (fun w => -(kappaBal a * pcU a w)) Z
          = -deriv (fun w => kappaBal a * pcU a w) Z := deriv_neg_fun_of_diff (kappaU_diff a) Z
        _ = -deriv (fun w => kappaBal a * pcU a w) (-(-Z)) := by rw [neg_neg]
        _ = deriv (fun w => kappaBal a * pcU a (-w)) (-Z) := (deriv_comp_neg_of_diff (kappaU_diff a) (-Z)).symm
  have hphi_abs : ∀ {A B Z : ℝ}, -Z ∈ Icc (-Z2) (-Z1) → gm ≤ A → |B| ≤ CBc →
      (A - h * Merr) * g (-Z) ≤ |minusModelPhi1 pcU pcV A B a h Z| ∧
      |minusModelPhi1 pcU pcV A B a h Z| ≤ (A + h * Merr) * g (-Z) := by
    intro A B Z hz hAge hB
    obtain ⟨hg_p, hd_nn, hd_ub⟩ := hg_pt (-Z) hz
    have hzp : 0 < -Z := (neg_pos.mpr hZ2_neg).trans_le hz.1
    have hhk2 : h * k2 a (-Z) ≤ Ck2 :=
      h_mul_k2_le hh hh1 hCZ.le hCa hCa (by rw [abs_of_pos hzp]; exact hz.2.trans (by linarith)) h_a_lo h_a_hi
    have hsq_k2 : Real.sqrt h * Real.sqrt (k2 a (-Z)) ≤ Real.sqrt Ck2 := by
      rw [← Real.sqrt_mul hh.le]; exact Real.sqrt_le_sqrt hhk2
    have hcorr_abs : |h * B * (Real.sqrt h * deriv (pcMinus pcU pcV a 1) Z)| ≤ h * Merr * g (-Z) := by
      rw [(hpc_eq Z).2]
      calc |h * B * (Real.sqrt h * deriv g (-Z))|
          = h * |B| * (Real.sqrt h * deriv g (-Z)) := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_pos hh, abs_of_nonneg (Real.sqrt_nonneg h), abs_of_nonneg hd_nn]
        _ ≤ h * CBc * (Real.sqrt h * (Cd * Real.sqrt (k2 a (-Z)) * g (-Z))) := by gcongr
        _ = h * (CBc * Cd * (Real.sqrt h * Real.sqrt (k2 a (-Z)))) * g (-Z) := by ring
        _ ≤ h * (CBc * Cd * Real.sqrt Ck2) * g (-Z) := by gcongr
    unfold minusModelPhi1
    rw [(hpc_eq Z).1]
    have hA_p : 0 < A := hgm.trans_le hAge
    have hMain : |A * (-g (-Z))| = A * g (-Z) := by
      rw [abs_mul, abs_neg, abs_of_pos hA_p, abs_of_pos hg_p]
    constructor
    · have h1 : |A * (-g (-Z))| - |h * B * (Real.sqrt h * deriv (pcMinus pcU pcV a 1) Z)| ≤
          |A * (-g (-Z)) + h * B * (Real.sqrt h * deriv (pcMinus pcU pcV a 1) Z)| := by
        simpa [sub_neg_eq_add] using abs_sub_abs_le_abs_sub (A * (-g (-Z)))
          (-(h * B * (Real.sqrt h * deriv (pcMinus pcU pcV a 1) Z)))
      linarith
    · calc |A * (-g (-Z)) + h * B * (Real.sqrt h * deriv (pcMinus pcU pcV a 1) Z)|
          ≤ |A * (-g (-Z))| + |h * B * (Real.sqrt h * deriv (pcMinus pcU pcV a 1) Z)| := abs_add_le _ _
        _ ≤ A * g (-Z) + h * Merr * g (-Z) := add_le_add hMain.le hcorr_abs
        _ = (A + h * Merr) * g (-Z) := by ring
  obtain ⟨h1_lo, _⟩ := hphi_abs ⟨by linarith, le_rfl⟩ hA1 hB1
  obtain ⟨_, h2_hi⟩ := hphi_abs ⟨le_rfl, by linarith⟩ hA2 hB2
  have hg1_nn : 0 ≤ g (-Z1) := (hg_pt (-Z1) ⟨by linarith, le_rfl⟩).1.le
  have hCd_nn : 0 ≤ Cd := by dsimp [Cd]; positivity
  have hCk2_nn : 0 ≤ Ck2 := by dsimp [Ck2]; positivity
  have hMerr_nn' : 0 ≤ Merr := by dsimp [Merr]; positivity
  have hdif : 6 * Merr ≤ (C2 - CAl) * A1 := by
    have h6 : 6 * Merr = (C2 - CAl) * gm := by dsimp [C2]; field_simp; ring
    have hdiff_eq : C2 - CAl = 6 * Merr / gm := by dsimp [C2]; ring
    rw [h6, hdiff_eq]
    exact mul_le_mul_of_nonneg_left hA1 (div_nonneg (mul_nonneg (by norm_num) hMerr_nn') hgm.le)
  have hdif_h : 6 * (h * Merr) ≤ (C2 - CAl) * h * A1 := by
    calc 6 * (h * Merr) = h * (6 * Merr) := by ring
      _ ≤ h * ((C2 - CAl) * A1) := mul_le_mul_of_nonneg_left hdif hh.le
      _ = (C2 - CAl) * h * A1 := by ring
  have hMerr_nn : 0 ≤ h * Merr := mul_nonneg hh.le hMerr_nn'
  have hC2_err : (1 + C2 * h) * (h * Merr) ≤ 2 * (h * Merr) :=
    mul_le_mul_of_nonneg_right (by linarith) hMerr_nn
  have hcoef : A2 + h * Merr ≤ (1 + C2 * h) * (A1 - h * Merr) := by
    have h1 : A2 + h * Merr ≤ (1 + CAl * h) * A1 + h * Merr := add_le_add hA21 le_rfl
    have h2 : (1 + CAl * h) * A1 + h * Merr = (1 + C2 * h) * A1 - (C2 - CAl) * h * A1 + h * Merr := by ring
    have h3 : (1 + C2 * h) * A1 - 5 * (h * Merr) ≤ (1 + C2 * h) * A1 - (1 + C2 * h) * (h * Merr) := by
      linarith [hC2_err, hMerr_nn]
    have h4 : (1 + C2 * h) * A1 - (1 + C2 * h) * (h * Merr) = (1 + C2 * h) * (A1 - h * Merr) := by ring
    linarith
  have hC2_nn : 0 ≤ C2 := by
    dsimp [C2]
    exact add_nonneg hCAl (div_nonneg (mul_nonneg (by norm_num) hMerr_nn') hgm.le)
  have h1_lt : 0 ≤ 1 + C2 * h := by linarith [mul_nonneg hC2_nn hh.le]
  calc |minusModelPhi1 pcU pcV A2 B2 a h Z2|
      ≤ (A2 + h * Merr) * g (-Z2) := h2_hi
    _ ≤ (A2 + h * Merr) * g (-Z1) := mul_le_mul_of_nonneg_left hg_mono (by linarith)
    _ ≤ (1 + C2 * h) * (A1 - h * Merr) * g (-Z1) := mul_le_mul_of_nonneg_right hcoef hg1_nn
    _ = (1 + C2 * h) * ((A1 - h * Merr) * g (-Z1)) := by ring
    _ ≤ (1 + C2 * h) * |minusModelPhi1 pcU pcV A1 B1 a h Z1| :=
          mul_le_mul_of_nonneg_left h1_lo h1_lt

/-- **Liouville-Green lower bound (`SoftEdgeChart.lb_pc`)** on the left of the PC well modulo `corr_PC`. -/
theorem soft_lb_pc_of_corr {gm CBc CZ Ca aHi : ℝ}
    (hgm : 0 < gm) (hCBc : 0 ≤ CBc) (hCZ : 0 ≤ CZ) (hCa : 0 ≤ Ca) (haHi_nn : 0 ≤ aHi) :
    ∃ clb h0 : ℝ, 0 < clb ∧ 0 < h0 ∧
      ∀ {h A B a Z : ℝ},
        0 < h → h ≤ h0 → a ≤ aHi → (a ≤ 0 → -a ≤ Ca / h) →
        -(CZ / Real.sqrt h) ≤ Z →
        Z < -(2 * Real.sqrt (max (-a) 0) + (1 + max (-a) 0) ^ (-(1 : ℝ) / 6)) →
        gm ≤ A → |B| ≤ CBc →
        clb * (Eminus a Z * Mbal a Z) ≤ |minusModelPhi0 pcU pcV A B a h Z| := by
  obtain ⟨cPC, CPC, env⟩ := pcEnvelopeFacts
  have hcPC_pos : 0 < cPC := env.cPC_pos
  have hCPC_pos : 0 < CPC := lt_of_lt_of_le env.cPC_pos env.cPC_le
  set Ck2 : ℝ := CZ ^ 2 / 4 + Ca + aHi + 1
  set Cd : ℝ := CPC * Real.sqrt 17 / cPC
  have hCk2_nn : 0 ≤ Ck2 := by dsimp [Ck2]; positivity
  have hCd_nn : 0 ≤ Cd := by dsimp [Cd]; positivity
  set Merr : ℝ := CBc * Cd * Real.sqrt Ck2
  have hMerr_nn : 0 ≤ Merr := by dsimp [Merr]; positivity
  set clb : ℝ := gm / 2 * (cPC / Real.sqrt 17)
  set h0 : ℝ := min 1 (gm / (2 * (Merr + 1)))
  refine ⟨clb, h0, by dsimp [clb]; positivity, by dsimp [h0]; positivity, ?_⟩
  intro h A B a Z hh hh0 haHi_le ha_neg hZ_lb hZ_lt hA hB
  have hh1 : h ≤ 1 := hh0.trans (min_le_left _ _)
  have hhMerr : h * Merr ≤ gm / 2 := by
    have h1 : h ≤ gm / (2 * (Merr + 1)) := hh0.trans (min_le_right _ _)
    have h2 : 2 * (Merr + 1) * h ≤ gm := (le_div_iff₀' (by positivity)).mp h1
    nlinarith [hh]
  have hz_neg : Z < 0 := by
    have h1 : 0 ≤ 2 * Real.sqrt (max (-a) 0) := by positivity
    have h2 : 0 ≤ (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    linarith
  have hz_pos : 2 * Real.sqrt (max (-a) 0) ≤ -Z := by
    have : 0 ≤ (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by positivity) _
    linarith
  obtain ⟨_, hU_lb⟩ := env.beyond a (-Z) hz_pos
  have hE : Eminus a Z = Erec a (-Z) := Eminus_eq_Erec_neg a Z hz_neg
  have hM : Mbal a Z = Mbal a (-Z) := (Mbal_neg a Z).symm
  have hk2_eq : k2 a Z = k2 a (-Z) := (k2_neg a Z).symm
  have hpc_eq : pcMinus pcU pcV a 0 Z = kappaBal a * pcU a (-Z) := by
    change (if a ≤ 0 then ut pcU a (-Z) else kappaBal a * pcU a (-Z)) = kappaBal a * pcU a (-Z)
    split_ifs <;> rfl
  have hpc_fun : pcMinus pcU pcV a 0 = fun w => kappaBal a * pcU a (-w) := by
    ext w; change (if a ≤ 0 then ut pcU a (-w) else kappaBal a * pcU a (-w)) = kappaBal a * pcU a (-w)
    split_ifs <;> rfl
  have hderiv_eq : |deriv (pcMinus pcU pcV a 0) Z| = |kappaBal a * deriv (pcU a) (-Z)| := by
    rw [hpc_fun, deriv_comp_neg_of_diff (kappaU_diff a), abs_neg]
    have hdeq : deriv (fun w => kappaBal a * pcU a w) (-Z) = kappaBal a * deriv (pcU a) (-Z) :=
      deriv_const_mul _ ((pcSmoothFacts.slice_U a).differentiable (by simp) (-Z))
    rw [hdeq]
  have hE_ub : |kappaBal a * deriv (pcU a) (-Z)| / Real.sqrt (k2 a (-Z)) ≤ CPC * Erec a (-Z) * Mbal a (-Z) := by
    have hk2p : 0 < k2 a (-Z) := k2_pos a (-Z)
    have h_env : Real.sqrt ((kappaBal a * pcU a (-Z)) ^ 2 + (kappaBal a * deriv (pcU a) (-Z)) ^ 2 / k2 a (-Z)) ≤
        CPC * Erec a (-Z) * Mbal a (-Z) := by
      by_cases ha0 : a ≤ 0
      · have he := (env.env_well a ha0 (-Z) (neg_pos.mpr hz_neg).le).1
        unfold Erec; rw [if_pos ha0, abs_of_pos (neg_pos.mpr hz_neg)]; exact he
      · have he := (env.env_bar a (lt_of_not_ge ha0) (-Z)).1
        unfold Erec; rw [if_neg ha0]; exact he
    have h1 : |kappaBal a * deriv (pcU a) (-Z)| / Real.sqrt (k2 a (-Z)) ≤
        Real.sqrt ((kappaBal a * pcU a (-Z)) ^ 2 + (kappaBal a * deriv (pcU a) (-Z)) ^ 2 / k2 a (-Z)) := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_div (sq_nonneg _)]
      apply Real.sqrt_le_sqrt
      linarith [sq_nonneg (kappaBal a * pcU a (-Z))]
    exact h1.trans h_env
  have h_deriv_bd : |deriv (pcMinus pcU pcV a 0) Z| ≤ Cd * Real.sqrt (k2 a (-Z)) * |pcMinus pcU pcV a 0 Z| := by
    rw [hderiv_eq, hpc_eq]
    have h1 : |kappaBal a * deriv (pcU a) (-Z)| ≤ CPC * Erec a (-Z) * Mbal a (-Z) * Real.sqrt (k2 a (-Z)) :=
      (div_le_iff₀ (Real.sqrt_pos.mpr (k2_pos a (-Z)))).mp hE_ub
    have hU_lb' : cPC / Real.sqrt 17 * (Erec a (-Z) * Mbal a (-Z)) ≤ |kappaBal a * pcU a (-Z)| := by
      linarith [hU_lb]
    have h2 : Erec a (-Z) * Mbal a (-Z) ≤ |kappaBal a * pcU a (-Z)| / (cPC / Real.sqrt 17) :=
      (le_div_iff₀' (div_pos env.cPC_pos (Real.sqrt_pos.mpr (by norm_num)))).mpr hU_lb'
    have hCPC : 0 ≤ CPC := (lt_of_lt_of_le env.cPC_pos env.cPC_le).le
    have heq : CPC * (|kappaBal a * pcU a (-Z)| / (cPC / Real.sqrt 17)) * Real.sqrt (k2 a (-Z)) =
        Cd * Real.sqrt (k2 a (-Z)) * |kappaBal a * pcU a (-Z)| := by dsimp [Cd]; field_simp [env.cPC_pos.ne']
    calc |kappaBal a * deriv (pcU a) (-Z)|
        ≤ CPC * (Erec a (-Z) * Mbal a (-Z)) * Real.sqrt (k2 a (-Z)) := by linarith
      _ ≤ CPC * (|kappaBal a * pcU a (-Z)| / (cPC / Real.sqrt 17)) * Real.sqrt (k2 a (-Z)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hCPC) (Real.sqrt_nonneg _)
      _ = Cd * Real.sqrt (k2 a (-Z)) * |kappaBal a * pcU a (-Z)| := heq
  have h_a_lo : -Ca / h ≤ a := by
    by_cases ha0 : a ≤ 0
    · rw [neg_div]; linarith [ha_neg ha0]
    · exact le_trans (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hCa) hh.le) (le_of_not_ge ha0)
  have h_a_hi : a ≤ aHi / h := haHi_le.trans ((le_div_iff₀ hh).mpr (by nlinarith [hh1]))
  have hhk2 : h * k2 a (-Z) ≤ Ck2 := by
    rw [← hk2_eq]
    exact h_mul_k2_le hh hh1 hCZ hCa haHi_nn (by rw [abs_of_neg hz_neg]; linarith) h_a_lo h_a_hi
  have hsq_k2 : Real.sqrt h * Real.sqrt (k2 a (-Z)) ≤ Real.sqrt Ck2 := by
    rw [← Real.sqrt_mul hh.le]; exact Real.sqrt_le_sqrt hhk2
  have hcorr_abs : |h * B * (Real.sqrt h * deriv (pcMinus pcU pcV a 0) Z)| ≤ h * Merr * |pcMinus pcU pcV a 0 Z| := by
    have hCBcCd : 0 ≤ CBc * Cd := mul_nonneg hCBc hCd_nn
    calc |h * B * (Real.sqrt h * deriv (pcMinus pcU pcV a 0) Z)|
        = h * |B| * (Real.sqrt h * |deriv (pcMinus pcU pcV a 0) Z|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos hh, abs_of_nonneg (Real.sqrt_nonneg h)]
      _ ≤ h * CBc * (Real.sqrt h * (Cd * Real.sqrt (k2 a (-Z)) * |pcMinus pcU pcV a 0 Z|)) := by gcongr
      _ = h * (CBc * Cd * (Real.sqrt h * Real.sqrt (k2 a (-Z)))) * |pcMinus pcU pcV a 0 Z| := by ring
      _ ≤ h * (CBc * Cd * Real.sqrt Ck2) * |pcMinus pcU pcV a 0 Z| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq_k2 hCBcCd) hh.le) (abs_nonneg _)
  have hrev : (A - h * Merr) * |pcMinus pcU pcV a 0 Z| ≤ |minusModelPhi0 pcU pcV A B a h Z| := by
    unfold minusModelPhi0
    have hA_p : 0 < A := hgm.trans_le hA
    have h1 : |A * pcMinus pcU pcV a 0 Z| - |h * B * (Real.sqrt h * deriv (pcMinus pcU pcV a 0) Z)| ≤
        |A * pcMinus pcU pcV a 0 Z + h * B * (Real.sqrt h * deriv (pcMinus pcU pcV a 0) Z)| := by
      simpa [sub_neg_eq_add] using abs_sub_abs_le_abs_sub (A * pcMinus pcU pcV a 0 Z)
        (-(h * B * (Real.sqrt h * deriv (pcMinus pcU pcV a 0) Z)))
    rw [abs_mul, abs_of_pos hA_p] at h1
    linarith
  calc clb * (Eminus a Z * Mbal a Z)
      = gm / 2 * (cPC / Real.sqrt 17 * Erec a (-Z) * Mbal a (-Z)) := by rw [hE, hM]; ring
    _ ≤ gm / 2 * |pcMinus pcU pcV a 0 Z| := by rw [hpc_eq]; gcongr
    _ ≤ (A - h * Merr) * |pcMinus pcU pcV a 0 Z| := by gcongr; linarith
    _ ≤ |minusModelPhi0 pcU pcV A B a h Z| := hrev

/-! ### 4. Weber chart bounds (`seed_pos`, `collar_lb`, `W_osc`, `M_osc`, `theta_le`) -/

/-- **Weber seed positivity (`BulkWeberChart.seed_pos`, `SoftEdgeChart.seed_posW`)** at row `0` modulo `corr_lead`/`corr_PC`.
Uses `pcU (-1/2, Z) = exp(-Z^2/4) > 0` for all `Z : ℝ`, covering both `SoftEdgeChart.seed_posW` and
`BulkWeberChart.seed_pos` (including collision energies `X ≤ B_0(0)` where `Y(h/2)` may be small or negative). -/
theorem weber_seed_pos_of_corr {cg Cg CY : ℝ} (hcg : 0 < cg) (hCg : 0 ≤ Cg) (hCY : 0 ≤ CY) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ {h A B Y : ℝ},
      0 < h → h ≤ h0 → |Y| ≤ CY → cg ≤ A → |B| ≤ Cg →
      0 < weberModelPhi pcU A B h 0 (Y / Real.sqrt h) := by
  set h0 : ℝ := cg / (Cg * CY + 1)
  refine ⟨h0, by positivity, ?_⟩
  intro h A B Y hh hh0 hY hA hB
  let Z := Y / Real.sqrt h
  have hU_eq : pcU (-((0 : ℕ) + 1 / 2)) = fun x => Real.exp (-x ^ 2 / 4) := by
    ext x
    have h0' : -((0 : ℕ) + 1 / 2 : ℝ) = -(0 : ℕ) - 1 / 2 := by norm_num
    rw [h0', pcU_nat 0 x, FormalResearch.Special.heR_zero, Polynomial.eval_one, mul_one]
  have hdU : deriv (pcU (-((0 : ℕ) + 1 / 2))) Z = -(Z / 2) * Real.exp (-Z ^ 2 / 4) := by
    rw [hU_eq]
    have hd : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / 4)) (Real.exp (-Z ^ 2 / 4) * (-(2 * Z ^ (2 - 1)) / 4)) Z :=
      ((hasDerivAt_pow 2 Z).neg.div_const 4).exp
    convert hd.deriv using 1
    simp; ring
  have hk_pos : 0 < kappaBal (-((0 : ℕ) + 1 / 2)) := kappaBal_pos _
  have hexp_pos : 0 < Real.exp (-Z ^ 2 / 4) := Real.exp_pos _
  have hdut : deriv (ut pcU (-((0 : ℕ) + 1 / 2))) Z =
      kappaBal (-((0 : ℕ) + 1 / 2)) * (-(Z / 2) * Real.exp (-Z ^ 2 / 4)) := by
    have hdiff : DifferentiableAt ℝ (pcU (-((0 : ℕ) + 1 / 2))) Z :=
      (pcSmoothFacts.slice_U _).differentiable (by simp) Z
    change deriv (fun x => kappaBal (-((0 : ℕ) + 1 / 2)) * pcU (-((0 : ℕ) + 1 / 2)) x) Z = _
    rw [deriv_const_mul _ hdiff, hdU]
  have hut_eq : ut pcU (-((0 : ℕ) + 1 / 2)) Z = kappaBal (-((0 : ℕ) + 1 / 2)) * Real.exp (-Z ^ 2 / 4) := by
    unfold ut; rw [hU_eq]
  have hZ_sqrt : Real.sqrt h * Z = Y := by
    dsimp [Z]; field_simp [(Real.sqrt_pos.mpr hh).ne']
  have hphi_eq : weberModelPhi pcU A B h 0 Z =
      kappaBal (-((0 : ℕ) + 1 / 2)) * Real.exp (-Z ^ 2 / 4) * (A - h * B * Y / 2) := by
    unfold weberModelPhi
    rw [hut_eq, hdut]
    calc A * (kappaBal (-((0 : ℕ) + 1 / 2)) * Real.exp (-Z ^ 2 / 4)) +
          h * B * (Real.sqrt h * (kappaBal (-((0 : ℕ) + 1 / 2)) * (-(Z / 2) * Real.exp (-Z ^ 2 / 4))))
        = kappaBal (-((0 : ℕ) + 1 / 2)) * Real.exp (-Z ^ 2 / 4) * (A - h * B * (Real.sqrt h * Z) / 2) := by ring
      _ = kappaBal (-((0 : ℕ) + 1 / 2)) * Real.exp (-Z ^ 2 / 4) * (A - h * B * Y / 2) := by rw [hZ_sqrt]
  have hBY : |h * B * Y / 2| ≤ h * (Cg * CY) / 2 := by
    have h1 : |h * B * Y| ≤ h * (Cg * CY) := by
      rw [abs_mul, abs_mul, abs_of_pos hh, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hB hY (abs_nonneg Y) hCg) hh.le
    rw [abs_div, abs_two]
    linarith
  have hsmall : h * (Cg * CY) / 2 < cg := by
    have h1 : h * (Cg * CY + 1) ≤ cg := (le_div_iff₀ (by positivity)).mp hh0
    have h2 : h * (Cg * CY) < h * (Cg * CY + 1) := by linarith
    linarith
  have hfac : 0 < A - h * B * Y / 2 := by
    have := (abs_le.mp hBY).2
    linarith
  rw [hphi_eq]
  exact mul_pos (mul_pos hk_pos hexp_pos) hfac

/-- **Weber collar lower bound (`BulkWeberChart.collar_lb`, `SoftEdgeChart.collar_lbW`, `SoftEdgeChart.lb_weber`)**
modulo `corr_lead`/`corr_PC`. -/
theorem weber_collar_lb_of_corr {cg Cg L CY : ℝ} (hcg : 0 < cg) (hCg : 0 ≤ Cg) (hL : 0 ≤ L) (hCY : 0 ≤ CY) :
    ∃ c3c h0 : ℝ, 0 < c3c ∧ 0 < h0 ∧
      ∀ {h A B Y : ℝ} {j : ℕ},
        0 < h → h ≤ h0 → ((j : ℝ) + 1 / 2) * h ≤ L → |Y| ≤ CY →
        2 * Real.sqrt ((j : ℝ) + 1 / 2) ≤ |Y / Real.sqrt h| →
        cg ≤ A → |B| ≤ Cg →
        c3c * Ewell (-((j : ℝ) + 1 / 2)) |Y / Real.sqrt h| * Mbal (-((j : ℝ) + 1 / 2)) (Y / Real.sqrt h) ≤
          |weberModelPhi pcU A B h j (Y / Real.sqrt h)| := by
  obtain ⟨CW, hCW, hwell⟩ := weber_env_well
  obtain ⟨c3, hc3, hw0⟩ := weber_W0
  set Ck2 : ℝ := CY ^ 2 / 4 + L + 0 + 1
  set Cd : ℝ := 2 * CW / c3
  set Merr : ℝ := Cg * Cd * Real.sqrt Ck2
  set h0 : ℝ := min 1 (cg / (2 * (Merr + 1)))
  refine ⟨cg / 2 * c3, h0, by positivity, by positivity, ?_⟩
  intro h A B Y j hh hh0 hu_ub hY hZ_abs hA hB
  have hh1 : h ≤ 1 := hh0.trans (min_le_left _ _)
  have hhMerr : h * Merr ≤ cg / 2 := by
    have h1 : h ≤ cg / (2 * (Merr + 1)) := hh0.trans (min_le_right _ _)
    have h2 : 2 * (Merr + 1) * h ≤ cg := (le_div_iff₀' (by positivity)).mp h1
    nlinarith [hh]
  let Z := Y / Real.sqrt h
  have hwellj : |ut pcU (-((j : ℝ) + 1 / 2)) Z| +
      (k2 (-((j : ℝ) + 1 / 2)) Z) ^ (-(1 : ℝ) / 2) * |deriv (ut pcU (-((j : ℝ) + 1 / 2))) Z| ≤
      2 * CW * Ewell (-((j : ℝ) + 1 / 2)) |Z| * Mbal (-((j : ℝ) + 1 / 2)) Z := by
    simpa [neg_div] using (hwell j Z).1
  have hw0j := hw0 j Z hZ_abs
  have hk2_pos : 0 < k2 (-((j : ℝ) + 1 / 2)) Z := k2_pos _ _
  have hd_bd : |deriv (ut pcU (-((j : ℝ) + 1 / 2))) Z| ≤
      Cd * Real.sqrt (k2 (-((j : ℝ) + 1 / 2)) Z) * |ut pcU (-((j : ℝ) + 1 / 2)) Z| := by
    have h1 : (k2 (-((j : ℝ) + 1 / 2)) Z) ^ (-(1 : ℝ) / 2) * |deriv (ut pcU (-((j : ℝ) + 1 / 2))) Z| ≤
        2 * CW * Ewell (-((j : ℝ) + 1 / 2)) |Z| * Mbal (-((j : ℝ) + 1 / 2)) Z := by
      linarith [hwellj, abs_nonneg (ut pcU (-((j : ℝ) + 1 / 2)) Z)]
    have h2 : Ewell (-((j : ℝ) + 1 / 2)) |Z| * Mbal (-((j : ℝ) + 1 / 2)) Z ≤ |ut pcU (-((j : ℝ) + 1 / 2)) Z| / c3 :=
      (le_div_iff₀ hc3).mpr (by linarith [hw0j])
    rw [rpow_neg_half_eq_inv_sqrt hk2_pos, inv_mul_le_iff₀ (Real.sqrt_pos.mpr hk2_pos)] at h1
    calc |deriv (ut pcU (-((j : ℝ) + 1 / 2))) Z|
        ≤ 2 * CW * (Ewell (-((j : ℝ) + 1 / 2)) |Z| * Mbal (-((j : ℝ) + 1 / 2)) Z) *
            Real.sqrt (k2 (-((j : ℝ) + 1 / 2)) Z) := by linarith
      _ ≤ 2 * CW * (|ut pcU (-((j : ℝ) + 1 / 2)) Z| / c3) * Real.sqrt (k2 (-((j : ℝ) + 1 / 2)) Z) := by gcongr
      _ = Cd * Real.sqrt (k2 (-((j : ℝ) + 1 / 2)) Z) * |ut pcU (-((j : ℝ) + 1 / 2)) Z| := by dsimp [Cd]; ring
  have hhk2 : h * k2 (-((j : ℝ) + 1 / 2)) Z ≤ Ck2 := by
    have hZ_ub : |Z| ≤ CY / Real.sqrt h := by
      rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hh)]
      exact div_le_div_of_nonneg_right hY (Real.sqrt_nonneg h)
    have hlo : -L / h ≤ -((j : ℝ) + 1 / 2) := by
      have : ((j : ℝ) + 1 / 2) ≤ L / h := (le_div_iff₀ hh).mpr hu_ub
      rw [neg_div]
      linarith
    exact h_mul_k2_le hh hh1 hCY hL le_rfl hZ_ub hlo
      (by rw [zero_div]; exact neg_nonpos.mpr (by positivity))
  have hsq_k2 : Real.sqrt h * Real.sqrt (k2 (-((j : ℝ) + 1 / 2)) Z) ≤ Real.sqrt Ck2 := by
    rw [← Real.sqrt_mul hh.le]; exact Real.sqrt_le_sqrt hhk2
  have hcorr : |h * B * (Real.sqrt h * deriv (ut pcU (-((j : ℝ) + 1 / 2))) Z)| ≤
      h * Merr * |ut pcU (-((j : ℝ) + 1 / 2)) Z| := by
    have hCd_nn : 0 ≤ Cd := by dsimp [Cd]; positivity
    have hCgCd : 0 ≤ Cg * Cd := mul_nonneg hCg hCd_nn
    calc |h * B * (Real.sqrt h * deriv (ut pcU (-((j : ℝ) + 1 / 2))) Z)|
        = h * |B| * (Real.sqrt h * |deriv (ut pcU (-((j : ℝ) + 1 / 2))) Z|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos hh, abs_of_nonneg (Real.sqrt_nonneg h)]
      _ ≤ h * Cg * (Real.sqrt h * (Cd * Real.sqrt (k2 (-((j : ℝ) + 1 / 2)) Z) * |ut pcU (-((j : ℝ) + 1 / 2)) Z|)) := by gcongr
      _ = h * (Cg * Cd * (Real.sqrt h * Real.sqrt (k2 (-((j : ℝ) + 1 / 2)) Z))) * |ut pcU (-((j : ℝ) + 1 / 2)) Z| := by ring
      _ ≤ h * (Cg * Cd * Real.sqrt Ck2) * |ut pcU (-((j : ℝ) + 1 / 2)) Z| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq_k2 hCgCd) hh.le) (abs_nonneg _)
  have hrev : (A - h * Merr) * |ut pcU (-((j : ℝ) + 1 / 2)) Z| ≤ |weberModelPhi pcU A B h j Z| := by
    unfold weberModelPhi
    have hA_p : 0 < A := hcg.trans_le hA
    have h1 : |A * ut pcU (-((j : ℝ) + 1 / 2)) Z| - |h * B * (Real.sqrt h * deriv (ut pcU (-((j : ℝ) + 1 / 2))) Z)| ≤
        |A * ut pcU (-((j : ℝ) + 1 / 2)) Z + h * B * (Real.sqrt h * deriv (ut pcU (-((j : ℝ) + 1 / 2))) Z)| := by
      simpa [sub_neg_eq_add] using abs_sub_abs_le_abs_sub (A * ut pcU (-((j : ℝ) + 1 / 2)) Z)
        (-(h * B * (Real.sqrt h * deriv (ut pcU (-((j : ℝ) + 1 / 2))) Z)))
    rw [abs_mul, abs_of_pos hA_p] at h1
    linarith
  calc cg / 2 * c3 * Ewell (-((j : ℝ) + 1 / 2)) |Z| * Mbal (-((j : ℝ) + 1 / 2)) Z
      ≤ cg / 2 * |ut pcU (-((j : ℝ) + 1 / 2)) Z| := by nlinarith [hw0j, hcg]
    _ ≤ (A - h * Merr) * |ut pcU (-((j : ℝ) + 1 / 2)) Z| := by gcongr; linarith
    _ ≤ |weberModelPhi pcU A B h j Z| := hrev

/-- **Oscillatory overlap bounds (`BulkWeberChart.W_osc`, `BulkWeberChart.M_osc`)**:
on `[c', c + σ]` where `4 u - Y^2 ≥ cH * σ > 0` and `|Y| ≤ CY`, we have `Ewell = 1` and `cM h^{1/4} ≤ Mbal ≤ CM h^{1/4}`. -/
theorem bulk_W_osc_M_osc {cH σ cs_hi CY : ℝ} (hcH : 0 < cH) (hσ : 0 < σ) (hcs : 0 ≤ cs_hi) (hCY : 0 ≤ CY) :
    let Ck2 : ℝ := CY ^ 2 / 4 + cs_hi + 0 + 1
    let cM : ℝ := Ck2 ^ (-(1 : ℝ) / 4)
    let CM : ℝ := (cH * σ / 4) ^ (-(1 : ℝ) / 4)
    0 < cM ∧ 0 < CM ∧ ∀ {h Y : ℝ} {k : ℤ},
      0 < h → h ≤ 1 → 0 ≤ ((k : ℝ) + 1 / 2) → ((k : ℝ) + 1 / 2) * h ≤ cs_hi →
      cH * σ ≤ 4 * (((k : ℝ) + 1 / 2) * h) - Y ^ 2 → |Y| ≤ CY →
      Ewell (-((k : ℝ) + 1 / 2)) |Y / Real.sqrt h| = 1 ∧
      cM * h ^ ((1 : ℝ) / 4) ≤ Mbal (-((k : ℝ) + 1 / 2)) (Y / Real.sqrt h) ∧
      Mbal (-((k : ℝ) + 1 / 2)) (Y / Real.sqrt h) ≤ CM * h ^ ((1 : ℝ) / 4) := by
  intro Ck2 cM CM
  have hCk2_pos : 0 < Ck2 := by dsimp [Ck2]; positivity
  refine ⟨Real.rpow_pos_of_pos hCk2_pos _, Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro h Y k hh hh1 hk_nn hu_le hturn hY
  have hk_neg : |(-((k : ℝ) + 1 / 2))| = (k : ℝ) + 1 / 2 := by rw [abs_neg, abs_of_nonneg hk_nn]
  have hgap : (Y / Real.sqrt h) ^ 2 / 4 - ((k : ℝ) + 1 / 2) ≤ -(cH * σ / (4 * h)) := by
    rw [div_pow, Real.sq_sqrt hh.le]
    have h1 : Y ^ 2 - 4 * (((k : ℝ) + 1 / 2) * h) ≤ -(cH * σ) := by linarith
    calc Y ^ 2 / h / 4 - ((k : ℝ) + 1 / 2) = (Y ^ 2 - 4 * (((k : ℝ) + 1 / 2) * h)) / (4 * h) := by field_simp
      _ ≤ -(cH * σ) / (4 * h) := div_le_div_of_nonneg_right h1 (by positivity)
      _ = -(cH * σ / (4 * h)) := by ring
  have hlt_turn : |Y / Real.sqrt h| ≤ 2 * Real.sqrt |(-((k : ℝ) + 1 / 2))| := by
    rw [hk_neg]
    have hsq : |Y / Real.sqrt h| ^ 2 ≤ (2 * Real.sqrt ((k : ℝ) + 1 / 2)) ^ 2 := by
      rw [sq_abs, mul_pow, Real.sq_sqrt hk_nn]; linarith [show 0 < cH * σ / (4 * h) by positivity]
    by_contra hbad; push_neg at hbad
    nlinarith [abs_nonneg (Y / Real.sqrt h), Real.sqrt_nonneg ((k : ℝ) + 1 / 2)]
  have hW : Ewell (-((k : ℝ) + 1 / 2)) |Y / Real.sqrt h| = 1 := by
    unfold Ewell; rw [if_neg (not_lt.mpr hlt_turn)]
  have hk2_lo : (cH * σ / 4) / h ≤ k2 (-((k : ℝ) + 1 / 2)) (Y / Real.sqrt h) := by
    have h1 : cH * σ / (4 * h) ≤ |(Y / Real.sqrt h) ^ 2 / 4 + (-((k : ℝ) + 1 / 2))| := by
      have : -((Y / Real.sqrt h) ^ 2 / 4 + (-((k : ℝ) + 1 / 2))) ≥ cH * σ / (4 * h) := by linarith
      exact this.trans (neg_le_abs _)
    calc (cH * σ / 4) / h = cH * σ / (4 * h) := by ring
      _ ≤ |(Y / Real.sqrt h) ^ 2 / 4 + (-((k : ℝ) + 1 / 2))| := h1
      _ ≤ k2 (-((k : ℝ) + 1 / 2)) (Y / Real.sqrt h) := le_max_left _ _
  have hk2_hi : k2 (-((k : ℝ) + 1 / 2)) (Y / Real.sqrt h) ≤ Ck2 / h := by
    have hZ_ub : |Y / Real.sqrt h| ≤ CY / Real.sqrt h := by
      rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hh)]
      exact div_le_div_of_nonneg_right hY (Real.sqrt_nonneg h)
    have hlo : -cs_hi / h ≤ -((k : ℝ) + 1 / 2) := by
      have : (k : ℝ) + 1 / 2 ≤ cs_hi / h := (le_div_iff₀ hh).mpr hu_le
      rw [neg_div]
      linarith
    have hmul := h_mul_k2_le hh hh1 hCY hcs le_rfl hZ_ub hlo
      (by rw [zero_div]; exact neg_nonpos.mpr hk_nn)
    exact (le_div_iff₀' hh).mpr (by dsimp [Ck2]; exact hmul)
  have hM_lo : cM * h ^ ((1 : ℝ) / 4) ≤ Mbal (-((k : ℝ) + 1 / 2)) (Y / Real.sqrt h) := by
    unfold Mbal
    have h1 : (Ck2 / h) ^ (-(1 : ℝ) / 4) ≤ k2 (-((k : ℝ) + 1 / 2)) (Y / Real.sqrt h) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos (k2_pos _ _) hk2_hi (by norm_num)
    exact (rpow_div_neg_quarter hCk2_pos hh).symm ▸ h1
  have hM_hi : Mbal (-((k : ℝ) + 1 / 2)) (Y / Real.sqrt h) ≤ CM * h ^ ((1 : ℝ) / 4) := by
    unfold Mbal
    have h1 : k2 (-((k : ℝ) + 1 / 2)) (Y / Real.sqrt h) ^ (-(1 : ℝ) / 4) ≤ ((cH * σ / 4) / h) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hk2_lo (by norm_num)
    exact h1.trans_eq (rpow_div_neg_quarter (by positivity) hh)
  exact ⟨hW, hM_lo, hM_hi⟩

private lemma sum_inv_sqrt_le (M : ℕ) :
    (∑ m ∈ Finset.range M, 1 / Real.sqrt ((m : ℝ) + 1)) ≤ 2 * Real.sqrt (M : ℝ) := by
  induction M with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hm1 : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have hsq_diff : (Real.sqrt ((m : ℝ) + 1) - Real.sqrt (m : ℝ)) *
          (Real.sqrt ((m : ℝ) + 1) + Real.sqrt (m : ℝ)) = 1 := by
        rw [mul_comm, ← sq_sub_sq, Real.sq_sqrt (by positivity), Real.sq_sqrt (Nat.cast_nonneg m)]; ring
      have hstep : 1 / Real.sqrt ((m : ℝ) + 1) ≤ 2 * (Real.sqrt ((m : ℝ) + 1) - Real.sqrt (m : ℝ)) := by
        have hle : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
        rw [div_le_iff₀ hm1]
        have h1 : 1 ≤ 2 * (Real.sqrt ((m : ℝ) + 1) - Real.sqrt (m : ℝ)) * Real.sqrt ((m : ℝ) + 1) := by
          nlinarith [hsq_diff]
        linarith
      push_cast
      linarith

/-- **Uniform modulus-sum bound (`BulkWeberChart.theta_le`)**:
if `k_2 ≥ c_k max(|(k + 1/2) - u_- / h|, 1)` on `[0, N_R]` and `(N_R + 1) h ≤ 2 L`, then
`sqrt h * ∑_{k=0}^{N_R} M_k^2 ≤ C_sum` independently of `h` and `u_-`. -/
theorem bulk_theta_le {ck L : ℝ} (hck : 0 < ck) (hL : 0 < L) :
    let Csum : ℝ := 8 / Real.sqrt ck * Real.sqrt (2 * L + 1)
    0 ≤ Csum ∧ ∀ {h uMinus : ℝ} {NR : ℤ} {Y : ℤ → ℝ},
      0 < h → h ≤ 1 → 0 ≤ NR → ((NR : ℝ) + 1) * h ≤ 2 * L →
      (∀ k ∈ Finset.Icc (0 : ℤ) NR,
        ck * max |(k : ℝ) + 1 / 2 - uMinus / h| 1 ≤ k2 (-((k : ℝ) + 1 / 2)) (Y k / Real.sqrt h)) →
      Real.sqrt h * ∑ k ∈ Finset.Icc (0 : ℤ) NR, Mbal (-((k : ℝ) + 1 / 2)) (Y k / Real.sqrt h) ^ 2 ≤ Csum := by
  intro Csum
  refine ⟨by positivity, ?_⟩
  intro h uMinus NR Y hh hh1 hNR hu_le hk2_lb
  let k0 : ℤ := ⌊uMinus / h⌋
  have hk0_le : (k0 : ℝ) ≤ uMinus / h := Int.floor_le (uMinus / h)
  have hlt_k01 : uMinus / h < (k0 : ℝ) + 1 := Int.lt_floor_add_one (uMinus / h)
  have hterm : ∀ k ∈ Finset.Icc (0 : ℤ) NR,
      Mbal (-((k : ℝ) + 1 / 2)) (Y k / Real.sqrt h) ^ 2 ≤
        2 / Real.sqrt ck * (1 / Real.sqrt ((Int.natAbs (k - k0) : ℝ) + 1)) := by
    intro k hk
    have hk2p : 0 < k2 (-((k : ℝ) + 1 / 2)) (Y k / Real.sqrt h) := k2_pos _ _
    have hM2 : Mbal (-((k : ℝ) + 1 / 2)) (Y k / Real.sqrt h) ^ 2 =
        1 / Real.sqrt (k2 (-((k : ℝ) + 1 / 2)) (Y k / Real.sqrt h)) := by
      unfold Mbal
      rw [← Real.rpow_natCast (_ ^ _), ← Real.rpow_mul hk2p.le]
      have he : -(1 : ℝ) / 4 * (2 : ℕ) = -(1 / 2 : ℝ) := by norm_num
      rw [he, Real.rpow_neg hk2p.le, ← Real.sqrt_eq_rpow, ← one_div]
    have hmax_lb : ((Int.natAbs (k - k0) : ℝ) + 1) / 4 ≤ max |(k : ℝ) + 1 / 2 - uMinus / h| 1 := by
      by_cases hd : Int.natAbs (k - k0) ≤ 1
      · have : (Int.natAbs (k - k0) : ℝ) ≤ 1 := by exact_mod_cast hd
        exact (by linarith : ((Int.natAbs (k - k0) : ℝ) + 1) / 4 ≤ 1).trans (le_max_right _ _)
      · have hd2 : (2 : ℝ) ≤ Int.natAbs (k - k0) := by exact_mod_cast (by omega : 2 ≤ Int.natAbs (k - k0))
        have hdiff : (Int.natAbs (k - k0) : ℝ) = |(k : ℝ) - k0| := by
          rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
        have htri : |(k : ℝ) - k0| ≤ |(k : ℝ) + 1 / 2 - uMinus / h| + 1 / 2 := by
          have : |(k : ℝ) - k0| ≤ |(k : ℝ) + 1 / 2 - uMinus / h| + |uMinus / h - k0 - 1 / 2| := by
            have heq : (k : ℝ) - k0 = ((k : ℝ) + 1 / 2 - uMinus / h) + (uMinus / h - k0 - 1 / 2) := by ring
            rw [heq]; exact abs_add_le _ _
          have hb : |uMinus / h - k0 - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
          linarith
        have h1 : ((Int.natAbs (k - k0) : ℝ) + 1) / 4 ≤ |(k : ℝ) - k0| - 1 / 2 := by linarith
        exact (h1.trans (by linarith)).trans (le_max_left _ _)
    have hk_bound : ck / 4 * ((Int.natAbs (k - k0) : ℝ) + 1) ≤ k2 (-((k : ℝ) + 1 / 2)) (Y k / Real.sqrt h) := by
      calc ck / 4 * ((Int.natAbs (k - k0) : ℝ) + 1) = ck * (((Int.natAbs (k - k0) : ℝ) + 1) / 4) := by ring
        _ ≤ ck * max |(k : ℝ) + 1 / 2 - uMinus / h| 1 := mul_le_mul_of_nonneg_left hmax_lb hck.le
        _ ≤ k2 (-((k : ℝ) + 1 / 2)) (Y k / Real.sqrt h) := hk2_lb k hk
    have hsq_lb : Real.sqrt (ck / 4 * ((Int.natAbs (k - k0) : ℝ) + 1)) ≤
        Real.sqrt (k2 (-((k : ℝ) + 1 / 2)) (Y k / Real.sqrt h)) := Real.sqrt_le_sqrt hk_bound
    have hsq_fac : Real.sqrt (ck / 4 * ((Int.natAbs (k - k0) : ℝ) + 1)) =
        Real.sqrt ck / 2 * Real.sqrt ((Int.natAbs (k - k0) : ℝ) + 1) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_div hck.le, show Real.sqrt 4 = 2 by norm_num]
    rw [hsq_fac] at hsq_lb
    rw [hM2]
    calc 1 / Real.sqrt (k2 (-((k : ℝ) + 1 / 2)) (Y k / Real.sqrt h))
        ≤ 1 / (Real.sqrt ck / 2 * Real.sqrt ((Int.natAbs (k - k0) : ℝ) + 1)) :=
          one_div_le_one_div_of_le (by positivity) hsq_lb
      _ = 2 / Real.sqrt ck * (1 / Real.sqrt ((Int.natAbs (k - k0) : ℝ) + 1)) := by ring
  let M : ℕ := Int.toNat (NR + 1) + 1
  let a1 : ℤ := min k0 NR
  let a2 : ℤ := max k0 (-1)
  have ha1_le_NR : a1 ≤ NR := min_le_right _ _
  have ha1_le_k0 : a1 ≤ k0 := min_le_left _ _
  have hge_k0_a2 : k0 ≤ a2 := le_max_left _ _
  have hge_m1_a2 : (-1 : ℤ) ≤ a2 := le_max_right _ _
  have hsum_split : ∑ k ∈ Finset.Icc (0 : ℤ) NR, (1 / Real.sqrt ((Int.natAbs (k - k0) : ℝ) + 1)) ≤
      2 * (∑ m ∈ Finset.range M, 1 / Real.sqrt ((m : ℝ) + 1)) := by
    let S1 := (Finset.Icc (0 : ℤ) NR).filter (fun k => k ≤ k0)
    let S2 := (Finset.Icc (0 : ℤ) NR).filter (fun k => k0 < k)
    have hdisj : Disjoint S1 S2 := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hunion : Finset.Icc (0 : ℤ) NR = S1 ∪ S2 := by
      ext k; simp only [S1, S2, Finset.mem_union, Finset.mem_filter]; constructor
      · intro hk; rcases le_or_gt k k0 with hle | hgt <;> [exact Or.inl ⟨hk, hle⟩; exact Or.inr ⟨hk, hgt⟩]
      · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk
    rw [hunion, Finset.sum_union hdisj, two_mul]
    apply add_le_add
    · let e1 : ℤ → ℕ := fun k => Int.toNat (a1 - k)
      calc ∑ k ∈ S1, 1 / Real.sqrt ((Int.natAbs (k - k0) : ℝ) + 1)
          ≤ ∑ k ∈ S1, 1 / Real.sqrt ((e1 k : ℝ) + 1) := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [Finset.mem_filter, Finset.mem_Icc] at hk
            have hk_le_k0 : k ≤ k0 := hk.2
            have ha1_le : a1 ≤ k0 := ha1_le_k0
            have hk_le_a1 : k ≤ a1 := le_min hk.2 hk.1.2
            have hle : e1 k ≤ Int.natAbs (k - k0) := by dsimp [e1]; omega
            have hleR : (e1 k : ℝ) + 1 ≤ (Int.natAbs (k - k0) : ℝ) + 1 := by
              have : (e1 k : ℝ) ≤ Int.natAbs (k - k0) := by exact_mod_cast hle
              linarith
            exact one_div_le_one_div_of_le (by positivity) (Real.sqrt_le_sqrt hleR)
        _ = ∑ m ∈ S1.image e1, 1 / Real.sqrt ((m : ℝ) + 1) := by
            refine (Finset.sum_image (f := fun m : ℕ => 1 / Real.sqrt ((m : ℝ) + 1)) (g := e1) ?_).symm
            intro k1 hk1 k2 hk2 heq
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hk1 hk2
            have h1 : k1 ≤ a1 := le_min hk1.2 hk1.1.2
            have h2 : k2 ≤ a1 := le_min hk2.2 hk2.1.2
            dsimp [e1] at heq; omega
        _ ≤ ∑ m ∈ Finset.range M, 1 / Real.sqrt ((m : ℝ) + 1) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
            intro m hm
            rcases Finset.mem_image.mp hm with ⟨k, hk, rfl⟩
            rw [Finset.mem_filter, Finset.mem_Icc] at hk
            rw [Finset.mem_range]
            have hk_le_a1 : k ≤ a1 := le_min hk.2 hk.1.2
            have hk_nn : 0 ≤ k := hk.1.1
            have hNR_nn : 0 ≤ NR + 1 := by linarith [hk.1.1, hk.1.2]
            dsimp [e1, M]
            zify
            rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg hNR_nn]
            linarith [ha1_le_NR]
    · let e2 : ℤ → ℕ := fun k => Int.toNat (k - a2 - 1)
      calc ∑ k ∈ S2, 1 / Real.sqrt ((Int.natAbs (k - k0) : ℝ) + 1)
          ≤ ∑ k ∈ S2, 1 / Real.sqrt ((e2 k : ℝ) + 1) := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [Finset.mem_filter, Finset.mem_Icc] at hk
            have hk_gt_k0 : k0 < k := hk.2
            have hk_nn : 0 ≤ k := hk.1.1
            have ha2_lt : a2 < k := max_lt hk.2 (by omega)
            have hge_k0 : k0 ≤ a2 := hge_k0_a2
            have hle : e2 k ≤ Int.natAbs (k - k0) := by dsimp [e2]; omega
            have hleR : (e2 k : ℝ) + 1 ≤ (Int.natAbs (k - k0) : ℝ) + 1 := by
              have : (e2 k : ℝ) ≤ Int.natAbs (k - k0) := by exact_mod_cast hle
              linarith
            exact one_div_le_one_div_of_le (by positivity) (Real.sqrt_le_sqrt hleR)
        _ = ∑ m ∈ S2.image e2, 1 / Real.sqrt ((m : ℝ) + 1) := by
            refine (Finset.sum_image (f := fun m : ℕ => 1 / Real.sqrt ((m : ℝ) + 1)) (g := e2) ?_).symm
            intro k1 hk1 k2 hk2 heq
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hk1 hk2
            have h1 : a2 < k1 := max_lt hk1.2 (by omega)
            have h2 : a2 < k2 := max_lt hk2.2 (by omega)
            dsimp [e2] at heq; omega
        _ ≤ ∑ m ∈ Finset.range M, 1 / Real.sqrt ((m : ℝ) + 1) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
            intro m hm
            rcases Finset.mem_image.mp hm with ⟨k, hk, rfl⟩
            rw [Finset.mem_filter, Finset.mem_Icc] at hk
            rw [Finset.mem_range]
            have hk_nn : 0 ≤ k := hk.1.1
            have hk_le_NR : k ≤ NR := hk.1.2
            have ha2_lt : a2 < k := max_lt hk.2 (by omega)
            have hNR_nn : 0 ≤ NR + 1 := by linarith [hk_nn, hk_le_NR]
            dsimp [e2, M]
            zify
            rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg hNR_nn]
            linarith [hge_m1_a2]
  have hS_bound : ∑ k ∈ Finset.Icc (0 : ℤ) NR, Mbal (-((k : ℝ) + 1 / 2)) (Y k / Real.sqrt h) ^ 2 ≤
      8 / Real.sqrt ck * Real.sqrt (M : ℝ) := by
    calc ∑ k ∈ Finset.Icc (0 : ℤ) NR, Mbal (-((k : ℝ) + 1 / 2)) (Y k / Real.sqrt h) ^ 2
        ≤ ∑ k ∈ Finset.Icc (0 : ℤ) NR, 2 / Real.sqrt ck * (1 / Real.sqrt ((Int.natAbs (k - k0) : ℝ) + 1)) :=
            Finset.sum_le_sum hterm
      _ = 2 / Real.sqrt ck * ∑ k ∈ Finset.Icc (0 : ℤ) NR, (1 / Real.sqrt ((Int.natAbs (k - k0) : ℝ) + 1)) := by
            rw [Finset.mul_sum]
      _ ≤ 2 / Real.sqrt ck * (2 * (∑ m ∈ Finset.range M, 1 / Real.sqrt ((m : ℝ) + 1))) := by gcongr
      _ ≤ 2 / Real.sqrt ck * (2 * (2 * Real.sqrt (M : ℝ))) := by
            gcongr; exact sum_inv_sqrt_le M
      _ = 8 / Real.sqrt ck * Real.sqrt (M : ℝ) := by ring
  have hM_cast : (M : ℝ) = (NR : ℝ) + 2 := by
    have hM_int : (M : ℤ) = NR + 2 := by
      dsimp [M]
      have hnn : 0 ≤ NR + 1 := by omega
      omega
    exact_mod_cast hM_int
  have hhM : h * (M : ℝ) ≤ 2 * L + 1 := by
    rw [hM_cast]
    nlinarith [hu_le, hh, hh1]
  calc Real.sqrt h * ∑ k ∈ Finset.Icc (0 : ℤ) NR, Mbal (-((k : ℝ) + 1 / 2)) (Y k / Real.sqrt h) ^ 2
      ≤ Real.sqrt h * (8 / Real.sqrt ck * Real.sqrt (M : ℝ)) :=
          mul_le_mul_of_nonneg_left hS_bound (Real.sqrt_nonneg h)
    _ = 8 / Real.sqrt ck * (Real.sqrt h * Real.sqrt (M : ℝ)) := by ring
    _ = 8 / Real.sqrt ck * Real.sqrt (h * (M : ℝ)) := by rw [Real.sqrt_mul hh.le]
    _ ≤ 8 / Real.sqrt ck * Real.sqrt (2 * L + 1) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hhM) (by positivity)

/-! ### Axiom verification guards -/

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.soft_bondA_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.soft_bondA_le

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.soft_grow_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.soft_grow_gap

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.soft_ratioM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.soft_ratioM

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.actionWell_ge_of_zeta_lb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.actionWell_ge_of_zeta_lb

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.soft_grow3_of_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.soft_grow3_of_corr

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.soft_ratio2_of_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.soft_ratio2_of_corr

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.soft_lb_pc_of_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.soft_lb_pc_of_corr

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.weber_seed_pos_of_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.weber_seed_pos_of_corr

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.weber_collar_lb_of_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.weber_collar_lb_of_corr

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.bulk_W_osc_M_osc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.bulk_W_osc_M_osc

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.bulk_theta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.bulk_theta_le

end FormalResearch.JacobiEigenvectors.Charts
