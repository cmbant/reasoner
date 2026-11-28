/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpWinDiff

/-!
# Window `E`, `K`, `J`, `winMuMix`, and `chi` symbol & difference bounds (`fct:warp-win`)

Leaf module establishing the exact symbol bounds on `[0, fctUc c]` for `L_lo ≤ L_hi` in the
Airy window `0 ≤ concreteEll1 ε c L_lo`, `concreteEll1 ε c L_hi ≤ Sw_ell * c^{-1/6}`:
* `win_E_diff_and_bounds`: `exp(E_2) - exp(E_1) ∈ 𝒮^8_4 (C c^{-5/6} (L_hi - L_lo))`,
  `exp(E) ∈ 𝒮^8_0 C`, and (for `|α| ≤ Cα c^{-2/3}`) `exp(E) - 1 ∈ 𝒮^8_8 (C c^{-4/3})`;
* `win_K_diff_and_bounds`: `K_2 - K_1 ∈ 𝒮^8_7 (C c^{-4/3} (L_hi - L_lo))`, `K ∈ 𝒮^8_0 C`, `K - 1 ∈ 𝒮^8_6 (C c^{-4/3})`;
* `win_J_diff_and_bounds`: `J_2 - J_1 ∈ 𝒮^8_{10} (C c^{-2/3} (L_hi - L_lo))`, `J - 1 ∈ 𝒮^8_{10} (C c^{-4/3})`,
  and `J ∈ 𝒮^8_0 C`;
* `win_muMix_diff_and_bounds`: `winMuMix(L_hi) - winMuMix(L_lo) ∈ 𝒮^8_{10} (C c^{-2/3} (L_hi - L_lo))`,
  `winMuMix(L) ∈ 𝒮^8_0 C`, and (for `|α| ≤ Cα c^{-2/3}`) `winMuMix(L) - 1 ∈ 𝒮^8_{10} (C c^{-4/3})`;
* `win_chi_diff_sym`: `χ_2 - χ_1 ∈ 𝒮^8_1 (C c^{-1/12} (L_hi - L_lo))`, vanishing on `[0, fctUstar c]`.

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Finset
open scoped Real ContDiff BigOperators
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctMoment
open FormalResearch.SignUncertainty.FctPhiKill FormalResearch.SignUncertainty.FctSymA
open FormalResearch.SignUncertainty.CtCfu FormalResearch.Asymptotics

namespace FormalResearch.SignUncertainty

/-! ### 1. General `JC 8` helper and local smoothness helpers -/

private lemma win_jc_all_of_contDiffOn {R₀ R : ℝ} (_hR : 0 < R) (hRR₀ : R < R₀)
    {g : ℝ → ℂ} (hg : ContDiffOn ℝ 9 g (Ioo (-R₀) R₀)) :
    ∃ B : ℝ, 0 ≤ B ∧ JC 8 (Ioo (-R) R) g B := by
  have hsub : Ioo (-R) R ⊆ Ioo (-R₀) R₀ := fun x hx => ⟨by linarith only [hx.1, hRR₀], by linarith only [hx.2, hRR₀]⟩
  have hsubC : Icc (-R) R ⊆ Ioo (-R₀) R₀ := fun x hx => ⟨by linarith only [hx.1, hRR₀], by linarith only [hx.2, hRR₀]⟩
  have hbd : ∀ k : ℕ, ∃ Ck : ℝ, 0 ≤ Ck ∧ (k ≤ 8 → ∀ t ∈ Icc (-R) R, ‖iteratedDeriv k g t‖ ≤ Ck) := by
    intro k
    by_cases hk : k ≤ 8
    · have hcont : ContinuousOn (iteratedDeriv k g) (Ioo (-R₀) R₀) := by
        have hm : (k : WithTop ℕ∞) ≤ 9 := by
          rw [show (9 : WithTop ℕ∞) = (((9 : ℕ) : ℕ∞) : WithTop ℕ∞) by rfl]; exact_mod_cast (by omega : k ≤ 9)
        exact (hg.continuousOn_iteratedDerivWithin hm isOpen_Ioo.uniqueDiffOn).congr
          fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm
      obtain ⟨Ck, hCk⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont.mono hsubC)
      exact ⟨max Ck 0, le_max_right _ _, fun _ t ht => (hCk t ht).trans (le_max_left _ _)⟩
    · exact ⟨0, le_rfl, fun h => absurd h hk⟩
  choose Ck hCk0 hCk using hbd
  let B : ℝ := ∑ k ∈ range 9, Ck k
  refine ⟨B, sum_nonneg fun k _ => hCk0 _, (hg.mono hsub).of_le (by norm_num), fun k hk t ht => ?_⟩
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, iteratedDerivWithin_of_isOpen isOpen_Ioo ht]
  exact (hCk k hk t ⟨ht.1.le, ht.2.le⟩).trans (single_le_sum (fun m _ => hCk0 m) (mem_range.mpr (by omega)))

private lemma win_jc_deriv_of_contDiffOn {R₀ R : ℝ} (hR : 0 < R) (hRR₀ : R < R₀)
    {g : ℝ → ℂ} (hg : ContDiffOn ℝ 10 g (Ioo (-R₀) R₀)) :
    ∃ B : ℝ, 0 ≤ B ∧ JC 8 (Ioo (-R) R) (deriv g) B := by
  have hg' : ContDiffOn ℝ 9 (deriv g) (Ioo (-R₀) R₀) := by
    have h0 := hg.derivWithin isOpen_Ioo.uniqueDiffOn (by norm_num : ((9 : WithTop ℕ∞) + 1 ≤ 10))
    exact h0.congr fun x hx => (derivWithin_of_isOpen isOpen_Ioo hx).symm
  exact win_jc_all_of_contDiffOn hR hRR₀ hg'

private lemma binetDiff_differentiableOn_left' {c : ℝ} (hc : 0 < c) :
    DifferentiableOn ℂ (binetDiff c) {ζ : ℂ | ζ.re < 1} := by
  have h1 : DifferentiableOn ℂ (fun ζ : ℂ => binetRem ((c : ℂ) * (1 - ζ))) {ζ : ℂ | ζ.re < 1} := by
    refine binetRem_differentiableOn.comp ?_ ?_
    · exact (differentiable_const _ |>.mul (differentiable_const _ |>.sub differentiable_id)).differentiableOn
    · intro ζ hζ
      simp only [mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, zero_mul, sub_zero]
      have : 0 < 1 - ζ.re := sub_pos.mpr hζ
      positivity
  exact h1.sub (differentiableOn_const _)

private lemma contDiff_binetImag' {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ ⊤ (fun τ : ℝ => binetDiff c ((τ : ℂ) * Complex.I)) := by
  have hopen : IsOpen {ζ : ℂ | ζ.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have hcd_R : ContDiffOn ℝ ⊤ (binetDiff c) {ζ : ℂ | ζ.re < 1} :=
    ((binetDiff_differentiableOn_left' hc).contDiffOn hopen).restrict_scalars ℝ
  rw [contDiff_iff_contDiffAt]
  intro τ
  have hmem : ((τ : ℂ) * Complex.I) ∈ {ζ : ℂ | ζ.re < 1} := by simp
  exact (hcd_R.contDiffAt (hopen.mem_nhds hmem)).comp τ (Complex.ofRealCLM.contDiff.mul contDiff_const).contDiffAt

private lemma iteratedDeriv_binetImag' {c : ℝ} (hc : 0 < c) (k : ℕ) (τ : ℝ) :
    iteratedDeriv k (fun t : ℝ => binetDiff c ((t : ℂ) * Complex.I)) τ =
      Complex.I ^ k * iteratedDeriv k (binetDiff c) ((τ : ℂ) * Complex.I) := by
  have hopen : IsOpen {ζ : ℂ | ζ.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have hcd_C : ContDiffOn ℂ ⊤ (binetDiff c) {ζ : ℂ | ζ.re < 1} :=
    (binetDiff_differentiableOn_left' hc).contDiffOn hopen
  induction k generalizing τ with
  | zero => simp
  | succ k ih =>
    have hfun : iteratedDeriv k (fun t : ℝ => binetDiff c ((t : ℂ) * Complex.I)) =
        fun t : ℝ => Complex.I ^ k * iteratedDeriv k (binetDiff c) ((t : ℂ) * Complex.I) := funext ih
    rw [iteratedDeriv_succ, hfun]
    have hmem : ((τ : ℂ) * Complex.I) ∈ {ζ : ℂ | ζ.re < 1} := by simp
    have hcd_k : ContDiffOn ℂ ⊤ (iteratedDeriv k (binetDiff c)) {ζ : ℂ | ζ.re < 1} := by
      clear hmem ih hfun τ
      induction k with
      | zero => simpa using hcd_C
      | succ k ihk =>
        rw [show iteratedDeriv (k + 1) (binetDiff c) = deriv (iteratedDeriv k (binetDiff c)) by
          ext z; rw [iteratedDeriv_succ]]
        exact ihk.deriv_of_isOpen hopen (by simp)
    have hd_C : HasDerivAt (iteratedDeriv k (binetDiff c))
        (iteratedDeriv (k + 1) (binetDiff c) ((τ : ℂ) * Complex.I)) ((τ : ℂ) * Complex.I) := by
      rw [iteratedDeriv_succ]
      exact ((hcd_k.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hmem)).hasDerivAt
    have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I τ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I
    have hcomp := (hd_C.scomp τ hlin).const_mul (Complex.I ^ k)
    have hcomp_deriv : deriv (fun t : ℝ => Complex.I ^ k * iteratedDeriv k (binetDiff c) ((t : ℂ) * Complex.I)) τ =
        Complex.I ^ k * (Complex.I * iteratedDeriv (k + 1) (binetDiff c) ((τ : ℂ) * Complex.I)) := by
      simpa [Function.comp, smul_eq_mul] using hcomp.deriv
    rw [hcomp_deriv, pow_succ]
    ring

private lemma contDiff_phiKillR_imag10 :
    ContDiff ℝ 10 (fun s : ℝ => phiKillR ((s : ℂ) * Complex.I)) := by
  have h1s : ∀ s : ℝ, 1 + (s : ℂ) * Complex.I ≠ 0 := fun s h0 => by
    have hre := congrArg Complex.re h0; simp at hre
  have hdiff : DifferentiableOn ℂ phiKillR {z : ℂ | 1 + z ≠ 0} := by
    refine DifferentiableOn.fun_sum fun j _ => ?_
    refine (differentiableOn_const _ |>.mul (differentiableOn_id.pow j)).div
      ((differentiableOn_const 1 |>.add differentiableOn_id).pow 15) fun z hz => pow_ne_zero 15 hz
  have hopen : IsOpen {z : ℂ | 1 + z ≠ 0} := isOpen_ne.preimage (continuous_const.add continuous_id)
  have hcd_R : ContDiffOn ℝ 10 phiKillR {z : ℂ | 1 + z ≠ 0} :=
    ((hdiff.contDiffOn hopen).restrict_scalars ℝ).of_le le_top
  have hlin : ContDiff ℝ 10 (fun s : ℝ => (s : ℂ) * Complex.I) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  exact contDiffOn_univ.mp (hcd_R.comp hlin.contDiffOn fun s _ => h1s s)

private lemma win_nfun_inv_jc :
    ∃ (R_n C_n C_0 : ℝ), 0 < R_n ∧ 0 ≤ C_n ∧ 0 ≤ C_0 ∧ R_n ^ 2 < rr ∧
      ContDiffOn ℝ 10 (fun t : ℝ => ((nfun (t ^ 2) : ℝ) : ℂ)⁻¹) (Ioo (-R_n) R_n) ∧
      JC 8 (Ioo (-(R_n / 2)) (R_n / 2)) (deriv (fun t : ℝ => ((nfun (t ^ 2) : ℝ) : ℂ)⁻¹)) C_n ∧
      JC 8 (Ioo (-(R_n / 2)) (R_n / 2)) (fun t : ℝ => ((nfun (t ^ 2) : ℝ) : ℂ)⁻¹) C_0 := by
  have hnfun_ev : ∀ᶠ y in 𝓝 (0 : ℝ), 0 < nfun y := by
    have hcont : ContinuousAt nfun 0 :=
      (contDiffOn_nfun.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith [rr_pos], rr_pos⟩)).continuousAt
    exact hcont.eventually (lt_mem_nhds (by rw [nfun_zero]; positivity))
  obtain ⟨δ_raw, hδ_raw0, hδ_raw_pos⟩ := Metric.eventually_nhds_iff.mp hnfun_ev
  let δn : ℝ := min rr (δ_raw / 2)
  have hδn0 : 0 < δn := lt_min rr_pos (half_pos hδ_raw0)
  let R_n : ℝ := min (1 / 2) (Real.sqrt (δn / 2))
  have hRn0 : 0 < R_n := lt_min (by norm_num) (Real.sqrt_pos.mpr (half_pos hδn0))
  have hRn_sq : R_n ^ 2 < rr := by
    have hle : R_n ^ 2 ≤ δn / 2 := by
      calc R_n ^ 2 ≤ (Real.sqrt (δn / 2)) ^ 2 :=
            pow_le_pow_left₀ hRn0.le (min_le_right _ _) 2
        _ = δn / 2 := Real.sq_sqrt (half_pos hδn0).le
    have hle2 : δn ≤ rr := min_le_left _ _
    linarith only [hle, hle2, rr_pos]
  have hn_pos : ∀ t ∈ Icc (-R_n) R_n, nfun (t ^ 2) ≠ 0 := fun t ht => by
    have htsq : t ^ 2 ≤ R_n ^ 2 := by
      rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) (abs_le.mpr ht) 2
    have hle : R_n ^ 2 ≤ δn / 2 := by
      calc R_n ^ 2 ≤ (Real.sqrt (δn / 2)) ^ 2 :=
            pow_le_pow_left₀ hRn0.le (min_le_right _ _) 2
        _ = δn / 2 := Real.sq_sqrt (half_pos hδn0).le
    have hdist : dist (t ^ 2) 0 < δ_raw := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg t)]
      calc t ^ 2 ≤ δn / 2 := htsq.trans hle
        _ ≤ (δ_raw / 2) / 2 := by gcongr; exact min_le_right _ _
        _ < δ_raw := by linarith only [hδ_raw0]
    exact (hδ_raw_pos hdist).ne'
  have hcd : ContDiffOn ℝ 10 (fun t : ℝ => ((nfun (t ^ 2) : ℝ) : ℂ)⁻¹) (Ioo (-R_n) R_n) := by
    have hmap : MapsTo (fun t : ℝ => t ^ 2) (Ioo (-R_n) R_n) (Ioo (-rr) rr) := fun t ht => by
      have htsq : t ^ 2 < R_n ^ 2 := by
        rw [← sq_abs t]; exact pow_lt_pow_left₀ (abs_lt.mpr ht) (abs_nonneg t) (by norm_num)
      exact ⟨by linarith [sq_nonneg t, rr_pos], htsq.trans hRn_sq⟩
    have hn10 : ContDiffOn ℝ 10 nfun (Ioo (-rr) rr) := contDiffOn_nfun.of_le (by simp)
    have hcomp := (Complex.ofRealCLM.contDiff.comp_contDiffOn hn10).comp contDiff_pow.contDiffOn hmap
    exact hcomp.inv fun t ht => Complex.ofReal_ne_zero.mpr (hn_pos t ⟨ht.1.le, ht.2.le⟩)
  obtain ⟨C_n, hCn0, hJC⟩ := win_jc_deriv_of_contDiffOn (half_pos hRn0) (half_lt_self hRn0) hcd
  obtain ⟨C_0, hC00, hJC0⟩ := win_jc_all_of_contDiffOn (half_pos hRn0) (half_lt_self hRn0) (hcd.of_le (by norm_num))
  exact ⟨R_n, C_n, C_0, hRn0, hCn0, hC00, hRn_sq, hcd, hJC, hJC0⟩

lemma win_chi_deriv_jc :
    ∃ B_χ : ℝ, 0 ≤ B_χ ∧ JC 8 (Ioo (-3 : ℝ) 3) (deriv (fun y : ℝ => ((outerChiIn y : ℝ) : ℂ))) B_χ := by
  have hcd : ContDiffOn ℝ 10 (fun y : ℝ => ((outerChiIn y : ℝ) : ℂ)) (Ioo (-4 : ℝ) 4) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn (outerChiIn_cutoff.smooth.of_le (by simp)).contDiffOn)
  exact win_jc_deriv_of_contDiffOn (by norm_num) (by norm_num) hcd

/-! ### 2. `exp(E)` window difference and `𝒮^8_0` / `𝒮^8_8` bounds -/

theorem win_E_diff_and_bounds {K4 Sw_ell : ℝ} (hK4 : 1 ≤ K4) (hSw : 1 ≤ Sw_ell) :
    ∃ (C_E C_d c₀ : ℝ), 0 ≤ C_E ∧ 0 ≤ C_d ∧ 10000 ≤ c₀ ∧ ∀ {ε c α L_lo L_hi : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim → K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 →
      |α| ≤ c ^ (-(1 / 2 : ℝ)) →
      0 ≤ concreteEll1 ε c L_lo → L_lo ≤ L_hi →
      concreteEll1 ε c L_hi ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      let T1 := fctInnerT c (concreteInnerV K4 ε c L_lo α)
      let T2 := fctInnerT c (concreteInnerV K4 ε c L_hi α)
      let E := fun T : ℝ → ℝ => fun u : ℝ =>
        -((K4 * (T u) ^ 4 : ℝ) : ℂ) +
          ((v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ))) (T u) : ℝ) : ℂ) +
          ((α * (T u) ^ 2 : ℝ) : ℂ) +
          FormalResearch.Asymptotics.binetDiff c (Complex.I * ((T u : ℝ) : ℂ))
      FctSymClsOn (Icc 0 (fctUc c)) 8 4 (C_d * c ^ (-(5 / 6 : ℝ)) * (L_hi - L_lo))
        (fun u => Complex.exp (E T2 u) - Complex.exp (E T1 u)) ∧
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_E (fun u => Complex.exp (E T1 u)) ∧
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_E (fun u => Complex.exp (E T2 u)) := by
  obtain ⟨c_V, _, hV_props⟩ := winVProps_of_window hK4 hSw
  obtain ⟨C_V, c_Vd, hCV0, _, hV_diff⟩ := win_V_diff_sym hK4 hSw
  obtain ⟨B_T, hBT1, hBT⟩ := fctInnerT_sym_bounds pbKV_nonneg
  obtain ⟨C_sc, hCsc0, hsc⟩ := win_comp_scale_T_diff_jc pbKV_nonneg
  obtain ⟨τ_D, hτD0, _, _, _, _, C_v1b, C_v1m, _, _, _, _, _, _, _, _, _, _, _, _, hCv_nn, _, _, _, hDmain⟩ :=
    fct_comp_D_part1 StripKernelChoice.star
  obtain ⟨C_T4, hCT40, hT4⟩ := fctInner_T4_sym pbKV_nonneg
  obtain ⟨C_v1, c_v1, hCv10, _, hv1⟩ := fctInner_v1_sym pbKV_nonneg
  obtain ⟨C_bin, hCbin0, hbin⟩ := fctInner_binet_sym pbKV_nonneg
  let C_v1_jc : ℝ := ∑ k ∈ range 9, (C_v1b (k + 1) + C_v1m (k + 1))
  have hCv1jc0 : 0 ≤ C_v1_jc := sum_nonneg fun k _ => add_nonneg (hCv_nn (k + 1)).2.2.2.1 (hCv_nn (k + 1)).2.2.2.2
  let C_bin_jc : ℝ := (Nat.factorial 9 : ℝ) / 12
  let C_d4 : ℝ := 2 ^ 24 * C_V * B_T ^ 3 * 4
  let C_dv1 : ℝ := C_sc * C_v1_jc * K4 * C_V
  let C_dα : ℝ := 2 ^ 8 * C_V * B_T * 2
  let C_dbin : ℝ := C_sc * C_bin_jc * 1 * C_V
  let C_Ediff : ℝ := C_d4 * K4 + C_dv1 + C_dα + C_dbin
  let C_E0 : ℝ := 4 ^ 10 * (C_T4 * K4 + C_v1 + C_bin) + 4 ^ 2 * 2 ^ 8 * B_T ^ 2
  let c₀ : ℝ := max (max c_V c_Vd) (max (max c_v1 (τ_D ^ (-4 : ℝ))) (max (K4 ^ 2)
    (max ((4 ^ 4 * C_Ediff * Sw_ell + 1) ^ 2) ((C_E0 + 1) ^ 2))))
  let C_Efin : ℝ := 1 + 3 * (Nat.factorial 8 : ℝ)
  let C_dfin : ℝ := 2 ^ 8 * C_Efin * (3 * (Nat.factorial 8 : ℝ) * C_Ediff)
  refine ⟨C_Efin, C_dfin, max 10000 c₀, by positivity, by positivity, le_max_left _ _,
    fun {ε c α L_lo L_hi} hε hc hτ_lim hK4t hα hell1 h12 hell2 => ?_⟩
  have hcv : c_V ≤ c := (le_max_left _ _ |>.trans (le_max_left _ _)).trans ((le_max_right 10000 c₀).trans hc)
  have hcvd : c_Vd ≤ c := (le_max_right _ _ |>.trans (le_max_left _ _)).trans ((le_max_right 10000 c₀).trans hc)
  have hvp := hV_props hε hcv hτ_lim hK4t hα hell1 h12 hell2
  have hc0 := hvp.hc0
  have hc1 : 1 ≤ c := by linarith only [hvp.hc10000]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hdiff_V := hV_diff hε hcvd hτ_lim hK4t hα hell1 h12 hell2
  have hT_diff : FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C_V * c ^ (-(1 / 3 : ℝ)) * (L_hi - L_lo))
      (fun u => ((fctInnerT c (concreteInnerV K4 ε c L_hi α) u -
        fctInnerT c (concreteInnerV K4 ε c L_lo α) u : ℝ) : ℂ)) :=
    hdiff_V.2.congr hDu fun u hu => by
      dsimp only [fctInnerT]
      rw [hvp.heq_hi _ (fctInnerY_mem_35 hc1 hu), hvp.heq_lo _ (fctInnerY_mem_35 hc1 hu)]
  have hT_diff_c : FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C_V * (L_hi - L_lo) * c ^ (-(1 / 3 : ℝ)))
      (fun u => ((fctInnerT c (concreteInnerV K4 ε c L_hi α) u -
        fctInnerT c (concreteInnerV K4 ε c L_lo α) u : ℝ) : ℂ)) :=
    hT_diff.mono_B Icc_subset_Ici_self (le_of_eq (by ring))
  have hT1_sym := (hBT hc1 hvp.hKV_small hvp.hjets_lo).2.2.2
  have hT2_sym := (hBT hc1 hvp.hKV_small hvp.hjets_hi).2.2.2
  -- 1. `-(K4 * (T2^4 - T1^4))`
  have hd4 : FctSymClsOn (Icc 0 (fctUc c)) 8 4 (C_d4 * K4 * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo))
      (fun u => -((K4 * (fctInnerT c (concreteInnerV K4 ε c L_hi α) u) ^ 4 : ℝ) : ℂ) -
        -((K4 * (fctInnerT c (concreteInnerV K4 ε c L_lo α) u) ^ 4 : ℝ) : ℂ)) := by
    have hsum1 := hT2_sym.add hDu hT1_sym
    have hsq2 := hT2_sym.mul Icc_subset_Ici_self hDu hT2_sym
    have hsq1 := hT1_sym.mul Icc_subset_Ici_self hDu hT1_sym
    have hsum2 := hsq2.add hDu hsq1
    have h12_p := hT_diff.mul Icc_subset_Ici_self hDu hsum1
    have h1234 := (h12_p.mul Icc_subset_Ici_self hDu hsum2).const_mul hDu ((-K4 : ℝ) : ℂ)
    have hnormK : ‖((-K4 : ℝ) : ℂ)‖ = K4 := by
      rw [Complex.norm_real, Real.norm_neg, Real.norm_of_nonneg (by linarith)]
    refine ((h1234.mono_B Icc_subset_Ici_self ?_).mono_p Icc_subset_Ici_self (by positivity)
      (by norm_num : (1 + 1 + (1 + 1) : ℝ) ≤ 4)).congr hDu fun u _ => by push_cast; ring
    rw [hnormK]
    have hc_p : c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * (c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ))) =
        c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0, ← Real.rpow_add hc0]; congr 1; norm_num
    calc K4 * (2 ^ 8 * (2 ^ 8 * (C_V * c ^ (-(1 / 3 : ℝ)) * (L_hi - L_lo)) *
          (B_T * c ^ (-(1 / 3 : ℝ)) + B_T * c ^ (-(1 / 3 : ℝ)))) *
          (2 ^ 8 * (B_T * c ^ (-(1 / 3 : ℝ))) * (B_T * c ^ (-(1 / 3 : ℝ))) +
           2 ^ 8 * (B_T * c ^ (-(1 / 3 : ℝ))) * (B_T * c ^ (-(1 / 3 : ℝ)))))
        = 2 ^ 24 * C_V * B_T ^ 3 * 4 * K4 *
            (c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * (c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)))) * (L_hi - L_lo) := by ring
      _ = C_d4 * K4 * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo) := by dsimp only [C_d4]; rw [hc_p]
  -- 2. `v1(T2) - v1(T1)`
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ))
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hdv1 : FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C_dv1 * c ^ (-(5 / 6 : ℝ)) * (L_hi - L_lo))
      (fun u => ((v1 StripKernelChoice.star K4 c τ₁ (fctInnerT c (concreteInnerV K4 ε c L_hi α) u) : ℝ) : ℂ) -
        ((v1 StripKernelChoice.star K4 c τ₁ (fctInnerT c (concreteInnerV K4 ε c L_lo α) u) : ℝ) : ℂ)) := by
    have hτ₁_le : τ₁ ≤ τ_D := by
      have h1 : τ_D ^ (-4 : ℝ) ≤ c :=
        (le_max_right _ _ |>.trans (le_max_left _ _) |>.trans (le_max_right _ _)).trans ((le_max_right 10000 c₀).trans hc)
      calc τ₁ = c ^ (-(1 / 4 : ℝ)) := rfl
        _ ≤ (τ_D ^ (-4 : ℝ)) ^ (-(1 / 4 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hτD0 _) h1 (by norm_num)
        _ = τ_D := by rw [← Real.rpow_mul hτD0.le]; norm_num
    have hcτ : τ₁ ^ 4 * c = 1 := by
      have : τ₁ ^ 4 = c⁻¹ := by dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num [Real.rpow_neg_one]
      rw [this]; field_simp [hc0.ne']
    have hτ₁_sq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
      dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have hα_τ₁ : |α| ≤ τ₁ ^ 2 := by rw [hτ₁_sq]; exact hα
    obtain ⟨hcd_v, _, _, _, _, _, _, hderiv_all, _⟩ := hDmain hK4 hc0 hτ₁_pos hτ₁_le hcτ hα_τ₁
    let g_v1 : ℝ → ℂ := fun y => ((v1 StripKernelChoice.star K4 c τ₁ (τ₁ * y) : ℝ) : ℂ)
    have hv1_cd : ContDiff ℝ ⊤ (v1 StripKernelChoice.star K4 c τ₁) := by
      change ContDiff ℝ ⊤ (fun t => v1Base StripKernelChoice.star c τ₁ t + K4 * v1Marg c τ₁ t)
      exact hcd_v.2.2.2.1.add (contDiff_const.mul hcd_v.2.2.2.2.1)
    have hg_cd : ContDiffOn ℝ 10 g_v1 (Ioo (-3 : ℝ) 3) :=
      (Complex.ofRealCLM.contDiff.comp (hv1_cd.comp (contDiff_const.mul contDiff_id))).of_le le_top |>.contDiffOn
    have hdg_jc : JC 8 (Ioo (-3 : ℝ) 3) (deriv g_v1) (C_v1_jc * K4 * c ^ (-(3 / 4 : ℝ))) := by
      have hg' : ContDiffOn ℝ 9 (deriv g_v1) (Ioo (-3 : ℝ) 3) := by
        have h0 := hg_cd.derivWithin isOpen_Ioo.uniqueDiffOn (by norm_num : ((9 : WithTop ℕ∞) + 1 ≤ 10))
        exact h0.congr fun x hx => (derivWithin_of_isOpen isOpen_Ioo hx).symm
      refine ⟨hg', fun k hk y hy => ?_⟩
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, iteratedDerivWithin_of_isOpen isOpen_Ioo hy,
        ← iteratedDeriv_succ']
      have hreal : iteratedDeriv (k + 1) g_v1 y =
          ((iteratedDeriv (k + 1) (fun s => v1 StripKernelChoice.star K4 c τ₁ (τ₁ * s)) y : ℝ) : ℂ) := by
        dsimp only [g_v1]
        rw [← iteratedDerivWithin_univ, iteratedDerivWithin_ofReal_cast uniqueDiffOn_univ
          ((hv1_cd.comp (contDiff_const.mul contDiff_id)).of_le le_top).contDiffOn (by omega) y (mem_univ y),
          iteratedDerivWithin_univ]
      rw [hreal, Complex.norm_real, Real.norm_eq_abs]
      have hcomp_d : iteratedDeriv (k + 1) (fun s => v1 StripKernelChoice.star K4 c τ₁ (τ₁ * s)) y =
          τ₁ ^ (k + 1) * iteratedDeriv (k + 1) (v1 StripKernelChoice.star K4 c τ₁) (τ₁ * y) := by
        induction k generalizing y with
        | zero =>
          simp only [zero_add, pow_one, iteratedDeriv_one]
          have hd := ((hv1_cd.differentiable (by simp)).hasDerivAt (x := τ₁ * y)).comp y
            ((hasDerivAt_id y).const_mul τ₁)
          simpa [Function.comp] using hd.deriv
        | succ m ihm =>
          have hfn : iteratedDeriv (m + 1) (fun s => v1 StripKernelChoice.star K4 c τ₁ (τ₁ * s)) =
              fun s => τ₁ ^ (m + 1) * iteratedDeriv (m + 1) (v1 StripKernelChoice.star K4 c τ₁) (τ₁ * s) :=
            funext ihm
          rw [iteratedDeriv_succ, hfn]
          have hd := (((hv1_cd.contDiffAt.iteratedDeriv (by simp)).differentiableAt (by simp)).hasDerivAt
            (x := τ₁ * y)).comp y ((hasDerivAt_id y).const_mul τ₁)
          have hd2 := hd.const_mul (τ₁ ^ (m + 1))
          have hd3 : deriv (fun s => τ₁ ^ (m + 1) * iteratedDeriv (m + 1) (v1 StripKernelChoice.star K4 c τ₁) (τ₁ * s)) y =
              τ₁ ^ (m + 2) * iteratedDeriv (m + 2) (v1 StripKernelChoice.star K4 c τ₁) (τ₁ * y) := by
            rw [show deriv (fun s => τ₁ ^ (m + 1) * iteratedDeriv (m + 1) (v1 StripKernelChoice.star K4 c τ₁) (τ₁ * s)) y =
                τ₁ ^ (m + 1) * (iteratedDeriv (m + 2) (v1 StripKernelChoice.star K4 c τ₁) (τ₁ * y) * τ₁) by
              simpa [Function.comp, iteratedDeriv_succ] using hd2.deriv]
            rw [pow_succ]; ring
          exact hd3
      rw [hcomp_d, abs_mul, abs_of_pos (pow_pos hτ₁_pos (k + 1))]
      have hv_sum : iteratedDeriv (k + 1) (v1 StripKernelChoice.star K4 c τ₁) (τ₁ * y) =
          iteratedDeriv (k + 1) (v1Base StripKernelChoice.star c τ₁) (τ₁ * y) +
            K4 * iteratedDeriv (k + 1) (v1Marg c τ₁) (τ₁ * y) := by
        have hc1' : ContDiffAt ℝ (k + 1 : ℕ) (v1Base StripKernelChoice.star c τ₁) (τ₁ * y) :=
          hcd_v.2.2.2.1.contDiffAt.of_le le_top
        have hc2' : ContDiffAt ℝ (k + 1 : ℕ) (fun s => K4 * v1Marg c τ₁ s) (τ₁ * y) :=
          (contDiff_const.mul hcd_v.2.2.2.2.1).contDiffAt.of_le le_top
        have hfun : v1 StripKernelChoice.star K4 c τ₁ =
            v1Base StripKernelChoice.star c τ₁ + fun s => K4 * v1Marg c τ₁ s := funext fun s => rfl
        rw [hfun, iteratedDeriv_add hc1' hc2', iteratedDeriv_const_mul_field]
      have hbd_all := hderiv_all (k + 1) (τ₁ * y)
      have hτ₁_le1 : τ₁ ≤ 1 := by
        dsimp only [τ₁]; exact Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
      have hpow_neg1 : τ₁ ^ (k + 1) * τ₁ ^ ((-1 : ℤ) - (k + 1 : ℕ)) = c ^ (1 / 4 : ℝ) := by
        rw [← zpow_natCast, ← zpow_add₀ hτ₁_pos.ne', add_sub_cancel, zpow_neg_one]
        dsimp only [τ₁]; rw [← Real.rpow_neg hc0.le]; congr 1; norm_num
      have hpow_pos1 : τ₁ ^ (k + 1) * τ₁ ^ ((1 : ℤ) - (k + 1 : ℕ)) ≤ c ^ (1 / 4 : ℝ) := by
        rw [← zpow_natCast, ← zpow_add₀ hτ₁_pos.ne', add_sub_cancel, zpow_one]
        have h14 : (1 : ℝ) ≤ c ^ (1 / 4 : ℝ) := Real.one_le_rpow hc1 (by norm_num)
        linarith only [hτ₁_le1, h14]
      have hc34 : c⁻¹ * c ^ (1 / 4 : ℝ) = c ^ (-(3 / 4 : ℝ)) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; congr 1; norm_num
      have hsum_k : C_v1b (k + 1) + C_v1m (k + 1) ≤ C_v1_jc :=
        single_le_sum (fun m _ => add_nonneg (hCv_nn (m + 1)).2.2.2.1 (hCv_nn (m + 1)).2.2.2.2)
          (mem_range.mpr (by omega))
      calc τ₁ ^ (k + 1) * |iteratedDeriv (k + 1) (v1 StripKernelChoice.star K4 c τ₁) (τ₁ * y)|
          ≤ τ₁ ^ (k + 1) * (|iteratedDeriv (k + 1) (v1Base StripKernelChoice.star c τ₁) (τ₁ * y)| +
              K4 * |iteratedDeriv (k + 1) (v1Marg c τ₁) (τ₁ * y)|) := by
            gcongr; rw [hv_sum]
            simpa only [abs_mul, abs_of_pos (by linarith only [hK4] : 0 < K4)] using abs_add_le _ _
        _ ≤ τ₁ ^ (k + 1) * (C_v1b (k + 1) * c⁻¹ * τ₁ ^ ((-1 : ℤ) - (k + 1 : ℕ)) +
              K4 * (C_v1m (k + 1) * c⁻¹ * τ₁ ^ ((1 : ℤ) - (k + 1 : ℕ)))) := by
            gcongr; exact hbd_all.2.2.2.1; exact hbd_all.2.2.2.2
        _ = C_v1b (k + 1) * c⁻¹ * (τ₁ ^ (k + 1) * τ₁ ^ ((-1 : ℤ) - (k + 1 : ℕ))) +
              K4 * C_v1m (k + 1) * c⁻¹ * (τ₁ ^ (k + 1) * τ₁ ^ ((1 : ℤ) - (k + 1 : ℕ))) := by ring
        _ ≤ C_v1b (k + 1) * c⁻¹ * c ^ (1 / 4 : ℝ) + K4 * C_v1m (k + 1) * c⁻¹ * c ^ (1 / 4 : ℝ) := by
            have := (hCv_nn (k + 1)).2.2.2.2
            have := (hCv_nn (k + 1)).2.2.2.1
            rw [hpow_neg1]; gcongr
        _ ≤ (C_v1b (k + 1) + C_v1m (k + 1)) * K4 * (c⁻¹ * c ^ (1 / 4 : ℝ)) := by
            have h1c := (hCv_nn (k + 1)).2.2.2.1
            have h2c := (hCv_nn (k + 1)).2.2.2.2
            have h0 : 0 ≤ C_v1b (k + 1) * c⁻¹ * c ^ (1 / 4 : ℝ) := by positivity
            nlinarith only [hK4, h0, h1c, h2c, hc0]
        _ ≤ C_v1_jc * K4 * c ^ (-(3 / 4 : ℝ)) := by rw [hc34]; gcongr
    have hR3 : 3 * c ^ (1 / 4 : ℝ) * fctTau1 c ≤ 3 := by
      have hp : c ^ (1 / 4 : ℝ) * fctTau1 c = 1 := by
        unfold fctTau1; rw [← Real.rpow_add hc0]; norm_num
      linarith only [hp]
    have hcomp := hsc hvp.hc10000 hvp.hKV_small (Real.rpow_pos_of_pos hc0 _) le_rfl hR3
      (by positivity) (mul_nonneg (sub_nonneg.mpr h12) (by have := pbcV_nonneg; have := pbC0_nonneg; positivity))
      hvp.hcd_lo hvp.hcd_hi hvp.hjets_lo hvp.hjets_hi hvp.hbd_lo hvp.hbd_hi hT_diff_c hg_cd hdg_jc
    have hprod_c : c ^ (-(3 / 4 : ℝ)) * c ^ (1 / 4 : ℝ) * c ^ (-(1 / 3 : ℝ)) = c ^ (-(5 / 6 : ℝ)) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; congr 1; norm_num
    have hc_inv : τ₁ * c ^ (1 / 4 : ℝ) = 1 := by
      dsimp only [τ₁]; rw [← Real.rpow_add hc0]; norm_num
    refine (hcomp.mono_B Icc_subset_Ici_self (le_of_eq ?_)).congr hDu fun u _ => ?_
    · calc C_sc * (C_v1_jc * K4 * c ^ (-(3 / 4 : ℝ))) * c ^ (1 / 4 : ℝ) * (C_V * (L_hi - L_lo)) * c ^ (-(1 / 3 : ℝ))
          = (C_sc * C_v1_jc * K4 * C_V) * (c ^ (-(3 / 4 : ℝ)) * c ^ (1 / 4 : ℝ) * c ^ (-(1 / 3 : ℝ))) * (L_hi - L_lo) := by ring
        _ = C_dv1 * c ^ (-(5 / 6 : ℝ)) * (L_hi - L_lo) := by dsimp only [C_dv1]; rw [hprod_c]
    · dsimp only [g_v1]; rw [← mul_assoc, hc_inv, one_mul, ← mul_assoc, hc_inv, one_mul]
  -- 3. `α * (T2^2 - T1^2)`
  have hdα : FctSymClsOn (Icc 0 (fctUc c)) 8 2 (C_dα * c ^ (-(7 / 6 : ℝ)) * (L_hi - L_lo))
      (fun u => ((α * (fctInnerT c (concreteInnerV K4 ε c L_hi α) u) ^ 2 : ℝ) : ℂ) -
        ((α * (fctInnerT c (concreteInnerV K4 ε c L_lo α) u) ^ 2 : ℝ) : ℂ)) := by
    have h12 := ((hT_diff.mul Icc_subset_Ici_self hDu (hT2_sym.add hDu hT1_sym)).const_mul hDu (α : ℂ)).congr hDu
      fun u _ => by push_cast; ring
    have hc_p : c ^ (-(1 / 2 : ℝ)) * (c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ))) = c ^ (-(7 / 6 : ℝ)) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; congr 1; norm_num
    refine h12.mono_B Icc_subset_Ici_self ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hc13_nn : 0 ≤ c ^ (-(1 / 3 : ℝ)) := by positivity
    have hL0 : 0 ≤ L_hi - L_lo := sub_nonneg.mpr h12
    have hnn1 : 0 ≤ 2 ^ 8 * (C_V * c ^ (-(1 / 3 : ℝ)) * (L_hi - L_lo)) * (B_T * c ^ (-(1 / 3 : ℝ)) + B_T * c ^ (-(1 / 3 : ℝ))) := by
      have := pbcV_nonneg; have := pbC0_nonneg; positivity
    calc |α| * (2 ^ 8 * (C_V * c ^ (-(1 / 3 : ℝ)) * (L_hi - L_lo)) *
          (B_T * c ^ (-(1 / 3 : ℝ)) + B_T * c ^ (-(1 / 3 : ℝ))))
        ≤ c ^ (-(1 / 2 : ℝ)) * (2 ^ 8 * (C_V * c ^ (-(1 / 3 : ℝ)) * (L_hi - L_lo)) *
          (B_T * c ^ (-(1 / 3 : ℝ)) + B_T * c ^ (-(1 / 3 : ℝ)))) := by gcongr
      _ = 2 ^ 8 * C_V * B_T * 2 * (c ^ (-(1 / 2 : ℝ)) * (c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)))) * (L_hi - L_lo) := by ring
      _ = C_dα * c ^ (-(7 / 6 : ℝ)) * (L_hi - L_lo) := by dsimp only [C_dα]; rw [hc_p]
  -- 4. `binetDiff c (I * T2) - binetDiff c (I * T1)`
  have hdbin : FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C_dbin * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo))
      (fun u => FormalResearch.Asymptotics.binetDiff c (Complex.I * ((fctInnerT c (concreteInnerV K4 ε c L_hi α) u : ℝ) : ℂ)) -
        FormalResearch.Asymptotics.binetDiff c (Complex.I * ((fctInnerT c (concreteInnerV K4 ε c L_lo α) u : ℝ) : ℂ))) := by
    let g_bin : ℝ → ℂ := fun t => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I)
    have hgb_cd : ContDiffOn ℝ 10 g_bin (Ioo (-(3 * fctTau1 c)) (3 * fctTau1 c)) :=
      ((contDiff_binetImag' hc0).of_le le_top).contDiffOn
    have hgb_jc : JC 8 (Ioo (-(3 * fctTau1 c)) (3 * fctTau1 c)) (deriv g_bin) (C_bin_jc * c⁻¹) := by
      have hg' : ContDiffOn ℝ 9 (deriv g_bin) (Ioo (-(3 * fctTau1 c)) (3 * fctTau1 c)) := by
        have h0 := ((contDiff_binetImag' hc0).of_le le_top).contDiffOn.derivWithin
          isOpen_Ioo.uniqueDiffOn (by norm_num : ((9 : WithTop ℕ∞) + 1 ≤ 10))
        exact h0.congr fun x hx => (derivWithin_of_isOpen isOpen_Ioo hx).symm
      refine ⟨hg', fun k hk t ht => ?_⟩
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, iteratedDerivWithin_of_isOpen isOpen_Ioo ht,
        ← iteratedDeriv_succ', show iteratedDeriv (k + 1) g_bin t = _ from iteratedDeriv_binetImag' hc0 (k + 1) t,
        norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
      have hre : ((t : ℂ) * Complex.I).re ≤ 0 := by simp
      refine (Asymptotics.binetDiff_iteratedDeriv_norm_le hc0 hre (Nat.succ_pos k)).trans ?_
      have hfac : ((k + 1).factorial : ℝ) ≤ Nat.factorial 9 := by exact_mod_cast Nat.factorial_le (by omega : k + 1 ≤ 9)
      calc ((k + 1).factorial : ℝ) / (12 * c) ≤ (Nat.factorial 9 : ℝ) / (12 * c) := by gcongr
        _ = C_bin_jc * c⁻¹ := by dsimp only [C_bin_jc]; ring
    have hcomp := hsc hvp.hc10000 hvp.hKV_small one_pos (Real.one_le_rpow hc1 (by norm_num)) (by ring_nf; rfl)
      (by positivity) (mul_nonneg (sub_nonneg.mpr h12) (by have := pbcV_nonneg; have := pbC0_nonneg; positivity))
      hvp.hcd_lo hvp.hcd_hi hvp.hjets_lo hvp.hjets_hi hvp.hbd_lo hvp.hbd_hi hT_diff_c hgb_cd hgb_jc
    have hc43 : c⁻¹ * c ^ (-(1 / 3 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; congr 1; norm_num
    refine (hcomp.mono_B Icc_subset_Ici_self (le_of_eq ?_)).congr hDu fun u _ => by
      dsimp only [g_bin]; simp only [one_mul, mul_comm Complex.I]
    calc C_sc * (C_bin_jc * c⁻¹) * 1 * (C_V * (L_hi - L_lo)) * c ^ (-(1 / 3 : ℝ))
        = (C_sc * C_bin_jc * 1 * C_V) * (c⁻¹ * c ^ (-(1 / 3 : ℝ))) * (L_hi - L_lo) := by ring
      _ = C_dbin * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo) := by dsimp only [C_dbin]; rw [hc43]
  -- Combine all 4 terms of `E2 - E1`
  have hc43_56 : c ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(5 / 6 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hc76_56 : c ^ (-(7 / 6 : ℝ)) ≤ c ^ (-(5 / 6 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hdv1_4 := hdv1.mono_p Icc_subset_Ici_self
    (by have := pbcV_nonneg; have := pbC0_nonneg; have := sub_nonneg.mpr h12; positivity)
    (by norm_num : (1 : ℝ) ≤ 4)
  have hd4_56 := hd4.mono_B Icc_subset_Ici_self (by
    have := pbcV_nonneg; have := pbC0_nonneg; have := sub_nonneg.mpr h12
    calc C_d4 * K4 * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo)
        ≤ C_d4 * K4 * c ^ (-(5 / 6 : ℝ)) * (L_hi - L_lo) := by gcongr)
  have hdα_4 := (hdα.mono_p Icc_subset_Ici_self (by
    have := pbcV_nonneg; have := pbC0_nonneg; have := sub_nonneg.mpr h12; positivity)
    (by norm_num : (2 : ℝ) ≤ 4)).mono_B Icc_subset_Ici_self (by
      have := pbcV_nonneg; have := pbC0_nonneg; have := sub_nonneg.mpr h12
      calc C_dα * c ^ (-(7 / 6 : ℝ)) * (L_hi - L_lo)
          ≤ C_dα * c ^ (-(5 / 6 : ℝ)) * (L_hi - L_lo) := by gcongr)
  have hdbin_4 := (hdbin.mono_p Icc_subset_Ici_self (by
    have := pbcV_nonneg; have := pbC0_nonneg; have := sub_nonneg.mpr h12; positivity)
    (by norm_num : (1 : ℝ) ≤ 4)).mono_B Icc_subset_Ici_self (by
      have := pbcV_nonneg; have := pbC0_nonneg; have := sub_nonneg.mpr h12
      calc C_dbin * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo)
          ≤ C_dbin * c ^ (-(5 / 6 : ℝ)) * (L_hi - L_lo) := by gcongr)
  have hEdiff : FctSymClsOn (Icc 0 (fctUc c)) 8 4 (C_Ediff * c ^ (-(5 / 6 : ℝ)) * (L_hi - L_lo))
      (fun u => (-((K4 * (fctInnerT c (concreteInnerV K4 ε c L_hi α) u) ^ 4 : ℝ) : ℂ) +
          ((v1 StripKernelChoice.star K4 c τ₁ (fctInnerT c (concreteInnerV K4 ε c L_hi α) u) : ℝ) : ℂ) +
          ((α * (fctInnerT c (concreteInnerV K4 ε c L_hi α) u) ^ 2 : ℝ) : ℂ) +
          FormalResearch.Asymptotics.binetDiff c (Complex.I * ((fctInnerT c (concreteInnerV K4 ε c L_hi α) u : ℝ) : ℂ))) -
        (-((K4 * (fctInnerT c (concreteInnerV K4 ε c L_lo α) u) ^ 4 : ℝ) : ℂ) +
          ((v1 StripKernelChoice.star K4 c τ₁ (fctInnerT c (concreteInnerV K4 ε c L_lo α) u) : ℝ) : ℂ) +
          ((α * (fctInnerT c (concreteInnerV K4 ε c L_lo α) u) ^ 2 : ℝ) : ℂ) +
          FormalResearch.Asymptotics.binetDiff c (Complex.I * ((fctInnerT c (concreteInnerV K4 ε c L_lo α) u : ℝ) : ℂ)))) :=
    (((hd4_56.add hDu hdv1_4).add hDu hdα_4).add hDu hdbin_4).mono_B Icc_subset_Ici_self
      (le_of_eq (by dsimp only [C_Ediff]; ring)) |>.congr hDu fun u _ => by ring
  -- Bound `exp(E)` on `[0, U_c]` in `𝒮^8_0 C_Efin`
  have hexp_pt : ∀ {V : ℝ → ℝ}, FctVJets pbKV c V →
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_Efin (fun u => Complex.exp (
        -((K4 * (fctInnerT c V u) ^ 4 : ℝ) : ℂ) +
          ((v1 StripKernelChoice.star K4 c τ₁ (fctInnerT c V u) : ℝ) : ℂ) +
          ((α * (fctInnerT c V u) ^ 2 : ℝ) : ℂ) +
          FormalResearch.Asymptotics.binetDiff c (Complex.I * ((fctInnerT c V u : ℝ) : ℂ)))) := fun {V} hVj => by
    have hK4c : K4 * c ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      have : K4 ^ 2 ≤ c := (le_max_left _ _ |>.trans (le_max_right _ _) |>.trans (le_max_right _ _)).trans
        ((le_max_right 10000 c₀).trans hc)
      have h1 : K4 ≤ c ^ (1 / 2 : ℝ) := by rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le this
      rw [Real.rpow_neg hc0.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hc0 _)]; exact h1
    have hcv1' : c_v1 ≤ c := (le_max_left _ _ |>.trans (le_max_left _ _) |>.trans (le_max_right _ _)).trans
      ((le_max_right 10000 c₀).trans hc)
    have hTV := (hBT hc1 hvp.hKV_small hVj).2.2.2
    have h1 := (hT4 hK4 hc1 hvp.hKV_small hVj).mono_p Icc_subset_Ici_self (by positivity) (by norm_num : (4 : ℝ) ≤ 10)
    have h2 := ((hv1 hK4 hcv1' hK4c hvp.hKV_small hα hVj).mono_p Icc_subset_Ici_self (by positivity)
      (by norm_num : (8 : ℝ) ≤ 10)).mono_B Icc_subset_Ici_self
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)) hCv10)
    have h3 := (hbin hc1 hvp.hKV_small hVj).mono_p Icc_subset_Ici_self (by positivity) (by norm_num : (1 : ℝ) ≤ 10)
    have h123_0 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (4 ^ 10 * (C_T4 * K4 + C_v1 + C_bin) * c ^ (-(1 / 2 : ℝ)))
        (fun u => -((K4 * (fctInnerT c V u) ^ 4 : ℝ) : ℂ) +
          ((v1 StripKernelChoice.star K4 c τ₁ (fctInnerT c V u) : ℝ) : ℂ) +
          FormalResearch.Asymptotics.binetDiff c (Complex.I * ((fctInnerT c V u : ℝ) : ℂ))) := by
      have hsum10 := ((h1.add hDu h2).add hDu h3).mono_B Icc_subset_Ici_self (le_of_eq (by ring))
      have hsh := hsum10.shrink_p hUc0.le (by positivity) (by norm_num : (0 : ℝ) ≤ 10)
      have hUc10 := one_add_Uc_rpow_le hc1 10 (by norm_num)
      have hc_p : c ^ (-(4 / 3 : ℝ)) * c ^ ((10 : ℝ) / 12) = c ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      refine (hsh.mono_B Icc_subset_Ici_self ?_).congr hDu fun u _ => by ring
      calc (C_T4 * K4 + C_v1 + C_bin) * c ^ (-(4 / 3 : ℝ)) * (1 + fctUc c) ^ (10 - 0 : ℝ)
          = (C_T4 * K4 + C_v1 + C_bin) * c ^ (-(4 / 3 : ℝ)) * (1 + fctUc c) ^ (10 : ℝ) := by norm_num
        _ ≤ (C_T4 * K4 + C_v1 + C_bin) * c ^ (-(4 / 3 : ℝ)) * ((4 : ℝ) ^ (10 : ℝ) * c ^ ((10 : ℝ) / 12)) := by gcongr
        _ = 4 ^ 10 * (C_T4 * K4 + C_v1 + C_bin) * (c ^ (-(4 / 3 : ℝ)) * c ^ ((10 : ℝ) / 12)) := by norm_num; ring
        _ = 4 ^ 10 * (C_T4 * K4 + C_v1 + C_bin) * c ^ (-(1 / 2 : ℝ)) := by rw [hc_p]
    have hT2 := ((hTV.mul Icc_subset_Ici_self hDu hTV).const_mul hDu (α : ℂ)).congr hDu fun u _ => by push_cast; ring
    have hα_0 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (4 ^ 2 * 2 ^ 8 * B_T ^ 2 * c ^ (-(1 / 2 : ℝ)))
        (fun u => ((α * (fctInnerT c V u) ^ 2 : ℝ) : ℂ)) := by
      have hsh := (hT2.shrink_p hUc0.le (by positivity) (by norm_num : (0 : ℝ) ≤ 2))
      have hUc2 := one_add_Uc_rpow_le hc1 2 (by norm_num)
      have hc_p : c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * c ^ ((2 : ℝ) / 12) = c ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; congr 1; norm_num
      refine hsh.mono_B Icc_subset_Ici_self ?_
      rw [Complex.norm_real, Real.norm_eq_abs, show (2 : ℝ) - 0 = 2 by norm_num]
      calc |α| * (2 ^ 8 * (B_T * c ^ (-(1 / 3 : ℝ))) * (B_T * c ^ (-(1 / 3 : ℝ)))) * (1 + fctUc c) ^ (2 : ℝ)
          ≤ c ^ (-(1 / 2 : ℝ)) * (2 ^ 8 * (B_T * c ^ (-(1 / 3 : ℝ))) * (B_T * c ^ (-(1 / 3 : ℝ)))) *
              ((4 : ℝ) ^ (2 : ℝ) * c ^ ((2 : ℝ) / 12)) := by gcongr
        _ ≤ 1 * (2 ^ 8 * (B_T * c ^ (-(1 / 3 : ℝ))) * (B_T * c ^ (-(1 / 3 : ℝ)))) *
              ((4 : ℝ) ^ (2 : ℝ) * c ^ ((2 : ℝ) / 12)) := by
            gcongr; exact Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
        _ = 4 ^ 2 * 2 ^ 8 * B_T ^ 2 * (c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * c ^ ((2 : ℝ) / 12)) := by norm_num; ring
        _ = 4 ^ 2 * 2 ^ 8 * B_T ^ 2 * c ^ (-(1 / 2 : ℝ)) := by rw [hc_p]
    have hE0_sum : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (C_E0 * c ^ (-(1 / 2 : ℝ)))
        (fun u => -((K4 * (fctInnerT c V u) ^ 4 : ℝ) : ℂ) +
          ((v1 StripKernelChoice.star K4 c τ₁ (fctInnerT c V u) : ℝ) : ℂ) +
          ((α * (fctInnerT c V u) ^ 2 : ℝ) : ℂ) +
          FormalResearch.Asymptotics.binetDiff c (Complex.I * ((fctInnerT c V u : ℝ) : ℂ))) :=
      (h123_0.add hDu hα_0).mono_B Icc_subset_Ici_self (le_of_eq (by dsimp only [C_E0]; ring)) |>.congr hDu
        fun u _ => by ring
    have hBU0 : C_E0 * c ^ (-(1 / 2 : ℝ)) * (1 + fctUc c) ^ (0 : ℝ) ≤ 1 := by
      have hc_bd : (C_E0 + 1) ^ 2 ≤ c :=
        (le_max_right _ _ |>.trans (le_max_right _ _) |>.trans (le_max_right _ _) |>.trans (le_max_right _ _)).trans
          ((le_max_right 10000 c₀).trans hc)
      have h1 : C_E0 + 1 ≤ c ^ (1 / 2 : ℝ) := by rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_bd
      rw [Real.rpow_zero, mul_one, Real.rpow_neg hc0.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hc0 _)]
      linarith only [h1]
    have hexp_sub := (hE0_sum.cexp_sub_one hUc0 (by norm_num) (by positivity) hBU0).mono_B Icc_subset_Ici_self (by
      calc 3 * (Nat.factorial 8 : ℝ) * (C_E0 * c ^ (-(1 / 2 : ℝ)))
          ≤ 3 * (Nat.factorial 8 : ℝ) * 1 := by gcongr; simpa using hBU0
        _ = 3 * (Nat.factorial 8 : ℝ) := by ring)
    have hone := (one_symCls 8).mono_set Icc_subset_Ici_self hDu (uniqueDiffOn_Ici 0)
    exact ((hone.add hDu hexp_sub).mono_B Icc_subset_Ici_self (le_of_eq (by dsimp only [C_Efin]; ring))).congr hDu
      fun u _ => by ring
  have hexp1 := hexp_pt hvp.hjets_lo
  have hexp2 := hexp_pt hvp.hjets_hi
  -- Apply `cexp_sub_one` to `E2 - E1`
  have hL_diff_le : L_hi - L_lo ≤ Sw_ell * c ^ (-(2 / 3 : ℝ)) := by
    have hell2' : (L_hi - ctTheta1 ε / c) / (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) := hell2
    have hell1' : 0 ≤ (L_lo - ctTheta1 ε / c) / (c ^ (-(1 / 4 : ℝ))) ^ 2 := hell1
    have hτ2 : 0 < (c ^ (-(1 / 4 : ℝ))) ^ 2 := by positivity
    have hdiff_ell : (L_hi - L_lo) / (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) := by
      have : (L_hi - L_lo) / (c ^ (-(1 / 4 : ℝ))) ^ 2 =
          (L_hi - ctTheta1 ε / c) / (c ^ (-(1 / 4 : ℝ))) ^ 2 -
            (L_lo - ctTheta1 ε / c) / (c ^ (-(1 / 4 : ℝ))) ^ 2 := by ring
      linarith only [this, hell2', hell1']
    have h1 : L_hi - L_lo ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) * (c ^ (-(1 / 4 : ℝ))) ^ 2 :=
      (div_le_iff₀ hτ2).mp hdiff_ell
    have hp : c ^ (-(1 / 6 : ℝ)) * (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; congr 1; norm_num
    linarith only [h1, hp]
  have hBU_diff : C_Ediff * c ^ (-(5 / 6 : ℝ)) * (L_hi - L_lo) * (1 + fctUc c) ^ (4 : ℝ) ≤ 1 := by
    have hUc4 := one_add_Uc_rpow_le hc1 4 (by norm_num)
    have hc_p : c ^ (-(5 / 6 : ℝ)) * c ^ (-(2 / 3 : ℝ)) * c ^ ((4 : ℝ) / 12) = c ^ (-(7 / 6 : ℝ)) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; congr 1; norm_num
    have hc76_12 : c ^ (-(7 / 6 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hc_bd : (4 ^ 4 * C_Ediff * Sw_ell + 1) ^ 2 ≤ c :=
      (le_max_left _ _ |>.trans (le_max_right _ _) |>.trans (le_max_right _ _) |>.trans (le_max_right _ _)).trans
        ((le_max_right 10000 c₀).trans hc)
    have h1 : 4 ^ 4 * C_Ediff * Sw_ell + 1 ≤ c ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_bd
    have hL0 : 0 ≤ L_hi - L_lo := sub_nonneg.mpr h12
    calc C_Ediff * c ^ (-(5 / 6 : ℝ)) * (L_hi - L_lo) * (1 + fctUc c) ^ (4 : ℝ)
        ≤ C_Ediff * c ^ (-(5 / 6 : ℝ)) * (Sw_ell * c ^ (-(2 / 3 : ℝ))) * ((4 : ℝ) ^ (4 : ℝ) * c ^ ((4 : ℝ) / 12)) := by
          gcongr
      _ = 4 ^ 4 * C_Ediff * Sw_ell * (c ^ (-(5 / 6 : ℝ)) * c ^ (-(2 / 3 : ℝ)) * c ^ ((4 : ℝ) / 12)) := by norm_num; ring
      _ = 4 ^ 4 * C_Ediff * Sw_ell * c ^ (-(7 / 6 : ℝ)) := by rw [hc_p]
      _ ≤ 4 ^ 4 * C_Ediff * Sw_ell * c ^ (-(1 / 2 : ℝ)) := by gcongr
      _ ≤ 1 := by
          rw [Real.rpow_neg hc0.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hc0 _)]
          linarith only [h1]
  have hcexp_d := hEdiff.cexp_sub_one hUc0 (by norm_num)
    (by have := pbcV_nonneg; have := pbC0_nonneg; have := sub_nonneg.mpr h12; positivity) hBU_diff
  have hprod := (hexp1.mul Icc_subset_Ici_self hDu hcexp_d).mono_p Icc_subset_Ici_self
    (by have := pbcV_nonneg; have := pbC0_nonneg; have := sub_nonneg.mpr h12; positivity)
    (by norm_num : (0 : ℝ) + 4 ≤ 4)
  refine ⟨(hprod.mono_B Icc_subset_Ici_self (le_of_eq (by dsimp only [C_dfin]; ring))).congr hDu
    fun u _ => by rw [← Complex.exp_add]; ring_nf, hexp1, hexp2⟩

/-! ### 3. `K(L) = 1 - L1 * phiKillDivM(a, T_L)` window difference and bounds -/

lemma win_K_diff_and_bounds {K4 Sw_ell : ℝ} (hK4 : 1 ≤ K4) (hSw : 1 ≤ Sw_ell) :
    ∃ (C_K C_d c₀ : ℝ), 0 ≤ C_K ∧ 0 ≤ C_d ∧ 10000 ≤ c₀ ∧ ∀ {ε c α L1 L_lo L_hi : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim → K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 →
      |α| ≤ c ^ (-(1 / 2 : ℝ)) → |L1| ≤ 1 →
      0 ≤ concreteEll1 ε c L_lo → L_lo ≤ L_hi →
      concreteEll1 ε c L_hi ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      let T1 := fctInnerT c (concreteInnerV K4 ε c L_lo α)
      let T2 := fctInnerT c (concreteInnerV K4 ε c L_hi α)
      let a := c ^ (-(1 / 12 : ℝ))
      FctSymClsOn (Icc 0 (fctUc c)) 8 7 (C_d * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo))
        (fun u => (1 - (L1 : ℂ) * phiKillDivM a (T2 u)) - (1 - (L1 : ℂ) * phiKillDivM a (T1 u))) ∧
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_K (fun u => 1 - (L1 : ℂ) * phiKillDivM a (T1 u)) ∧
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_K (fun u => 1 - (L1 : ℂ) * phiKillDivM a (T2 u)) := by
  obtain ⟨c_V, _, hV_props⟩ := winVProps_of_window hK4 hSw
  obtain ⟨C_V, c_Vd, hCV0, _, hV_diff⟩ := win_V_diff_sym hK4 hSw
  obtain ⟨B_T, hBT1, hBT⟩ := fctInnerT_sym_bounds pbKV_nonneg
  obtain ⟨C_sc, hCsc0, hsc⟩ := win_comp_scale_T_diff_jc pbKV_nonneg
  obtain ⟨C_pk, c_pk, hCpk0, _, hpk⟩ := fctInner_phiKillDivM_sym pbKV_nonneg
  obtain ⟨CR, hCR0, hCR⟩ := win_jc_deriv_of_contDiffOn (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    contDiff_phiKillR_imag10.contDiffOn
  obtain ⟨CR0, hCR0_nn, hCR0_jc⟩ := win_jc_all_of_contDiffOn (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (contDiff_phiKillR_imag10.of_le (by norm_num)).contDiffOn
  obtain ⟨R_n, C_n, C_n0, hRn0, hCn0, hCn0_nn, hRn_sq, hn_cd, hn_jc, hn0_jc⟩ := win_nfun_inv_jc
  let M_m : ℝ := max 1 (4 * B_T)
  let C_g0 : ℝ := (Nat.factorial 8 : ℝ) * M_m ^ 8
  let C_B : ℝ := C_g0 * CR0
  let C_C : ℝ := C_g0 * C_n0
  let C_A1 : ℝ := B_T ^ 6 * 2 ^ 40
  let C_T6d : ℝ := 2 ^ 40 * 6 * C_V * B_T ^ 5
  let C_pkR : ℝ := C_sc * CR * C_V
  let C_ninv : ℝ := C_sc * C_n * 1 * C_V
  let C_dfin : ℝ := 2 ^ 8 * (2 ^ 8 * (C_T6d * C_B) * C_C + 2 ^ 8 * (C_A1 * C_pkR) * C_C) +
    2 ^ 8 * (2 ^ 8 * C_A1 * C_B) * C_ninv
  let C_Kfin : ℝ := 1 + 4 ^ 6 * C_pk
  let c₀ : ℝ := max (max c_V c_Vd) (max c_pk (max ((6 : ℝ) ^ 6) (((6 / R_n) ^ 4) + 1)))
  refine ⟨C_Kfin, C_dfin, max 10000 c₀, by positivity, by positivity, le_max_left _ _,
    fun {ε c α L1 L_lo L_hi} hε hc hτ_lim hK4t hα hL1 hell1 h12 hell2 => ?_⟩
  have hcv : c_V ≤ c := (le_max_left _ _ |>.trans (le_max_left _ _)).trans ((le_max_right 10000 c₀).trans hc)
  have hcvd : c_Vd ≤ c := (le_max_right _ _ |>.trans (le_max_left _ _)).trans ((le_max_right 10000 c₀).trans hc)
  have hcpk : c_pk ≤ c := (le_max_left _ _ |>.trans (le_max_right _ _)).trans ((le_max_right 10000 c₀).trans hc)
  have hc66 : (6 : ℝ) ^ 6 ≤ c := (le_max_left _ _ |>.trans (le_max_right _ _) |>.trans (le_max_right _ _)).trans
    ((le_max_right 10000 c₀).trans hc)
  have hcRn : (6 / R_n) ^ 4 ≤ c := by
    have h1 : (6 / R_n) ^ 4 ≤ ((6 / R_n) ^ 4) + 1 := by linarith
    exact h1.trans ((le_max_right _ _ |>.trans (le_max_right _ _) |>.trans (le_max_right _ _)).trans
      ((le_max_right 10000 c₀).trans hc))
  have hvp := hV_props hε hcv hτ_lim hK4t hα hell1 h12 hell2
  have hc0 := hvp.hc0
  have hc1 : 1 ≤ c := by linarith only [hvp.hc10000]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hT_diff : FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C_V * c ^ (-(1 / 3 : ℝ)) * (L_hi - L_lo))
      (fun u => ((fctInnerT c (concreteInnerV K4 ε c L_hi α) u -
        fctInnerT c (concreteInnerV K4 ε c L_lo α) u : ℝ) : ℂ)) :=
    (hV_diff hε hcvd hτ_lim hK4t hα hell1 h12 hell2).2.congr hDu fun u hu => by
      dsimp only [fctInnerT]
      rw [hvp.heq_hi _ (fctInnerY_mem_35 hc1 hu), hvp.heq_lo _ (fctInnerY_mem_35 hc1 hu)]
  have hT_diff_c : FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C_V * (L_hi - L_lo) * c ^ (-(1 / 3 : ℝ))) _ :=
    hT_diff.mono_B Icc_subset_Ici_self (le_of_eq (by ring))
  have hT1_sym := (hBT hc1 hvp.hKV_small hvp.hjets_lo).2.2.2
  have hT2_sym := (hBT hc1 hvp.hKV_small hvp.hjets_hi).2.2.2
  set a : ℝ := c ^ (-(1 / 12 : ℝ))
  have ha0 : 0 < a := Real.rpow_pos_of_pos hc0 _
  have hR_pk : 3 * c ^ (1 / 12 : ℝ) * fctTau1 c ≤ 1 / 2 := by
    have hp : c ^ (1 / 12 : ℝ) * fctTau1 c = c ^ (-(1 / 6 : ℝ)) := by
      unfold fctTau1; rw [← Real.rpow_add hc0]; congr 1; norm_num
    have hc16 : c ^ (-(1 / 6 : ℝ)) ≤ 1 / 6 := by
      have h1 : (6 : ℝ) ≤ c ^ ((1 : ℝ) / 6) := by
        calc (6 : ℝ) = ((6 : ℝ) ^ 6) ^ ((1 : ℝ) / 6) := by norm_num [← Real.rpow_natCast, ← Real.rpow_mul]
          _ ≤ c ^ ((1 : ℝ) / 6) := Real.rpow_le_rpow (by positivity) hc66 (by norm_num)
      rw [Real.rpow_neg hc0.le, ← one_div, div_le_div_iff₀ (Real.rpow_pos_of_pos hc0 _) (by norm_num)]
      linarith only [h1]
    linarith only [hp, hc16]
  have hR_n : 3 * 1 * fctTau1 c ≤ R_n / 2 := by
    have hτ_le : fctTau1 c ≤ R_n / 6 := by
      have h1 : 6 / R_n ≤ c ^ ((1 : ℝ) / 4) := by
        calc 6 / R_n = ((6 / R_n) ^ 4) ^ ((1 : ℝ) / 4) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
          _ ≤ c ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by positivity) hcRn (by norm_num)
      unfold fctTau1; rw [Real.rpow_neg hc0.le, ← one_div, div_le_div_iff₀ (Real.rpow_pos_of_pos hc0 _) (by norm_num)]
      rw [div_le_iff₀ hRn0] at h1; linarith only [h1]
    linarith only [hτ_le]
  have hT_small : ∀ {V : ℝ → ℝ}, FctVJets pbKV c V → ∀ u ∈ Icc 0 (fctUc c),
      0 ≤ fctInnerT c V u ∧ fctInnerT c V u < R_n / 2 ∧ fctInnerT c V u / a < 1 / 2 := by
    intro V hVj u hu
    have h0 := (hBT hc1 hvp.hKV_small hVj).2.1 u hu
    have h2tau : fctInnerT c V u ≤ 2 * fctTau1 c := fctInnerT_le_two_tau1 pbKV_nonneg hc1 hvp.hKV_small hVj hu
    have h1n : fctInnerT c V u < R_n / 2 := by
      have : 0 < fctTau1 c := Real.rpow_pos_of_pos hc0 _; linarith only [h2tau, hR_n, this]
    have h2a : fctInnerT c V u / a < 1 / 2 := by
      rw [div_eq_mul_inv, show a⁻¹ = c ^ (1 / 12 : ℝ) by dsimp only [a]; rw [Real.rpow_neg hc0.le, inv_inv]]
      have : 0 < c ^ (1 / 12 : ℝ) * fctTau1 c := by positivity
      nlinarith only [h2tau, hR_pk, this]
    exact ⟨h0.1, h1n, h2a⟩
  have hpk_eq : ∀ {V : ℝ → ℝ}, FctVJets pbKV c V → EqOn (fun u => phiKillDivM a (fctInnerT c V u))
      (fun u => ((fctInnerT c V u ^ 6 * a ^ (-8 : ℤ) : ℝ) : ℂ) *
        phiKillR (((c ^ (1 / 12 : ℝ) * fctInnerT c V u : ℝ) : ℂ) * Complex.I) *
        ((nfun (fctInnerT c V u ^ 2) : ℝ) : ℂ)⁻¹) (Icc 0 (fctUc c)) := fun {V} hVj u hu => by
    have hs := hT_small hVj u hu
    have hsq_rr : fctInnerT c V u ^ 2 < rr := by
      have h1 : fctInnerT c V u ^ 2 ≤ (R_n / 2) ^ 2 := pow_le_pow_left₀ hs.1 hs.2.1.le 2
      have h2 : (R_n / 2) ^ 2 < R_n ^ 2 := by nlinarith only [hRn0]
      exact (h1.trans_lt h2).trans hRn_sq
    rw [phiKillDivM_eq ha0 hs.1 hsq_rr, div_eq_mul_inv, div_eq_mul_inv]
    have ha_inv : a⁻¹ = c ^ (1 / 12 : ℝ) := by dsimp only [a]; rw [Real.rpow_neg hc0.le, inv_inv]
    rw [ha_inv]; push_cast; ring
  have ha8 : a ^ (-8 : ℤ) = c ^ (2 / 3 : ℝ) := by
    dsimp only [a]; rw [← Real.rpow_intCast, ← Real.rpow_mul hc0.le]; congr 1; norm_num
  have hA_of : ∀ {V : ℝ → ℝ},
      FctSymClsOn (Icc 0 (fctUc c)) 8 1 (B_T * c ^ (-(1 / 3 : ℝ))) (fun u => ((fctInnerT c V u : ℝ) : ℂ)) →
      FctSymClsOn (Icc 0 (fctUc c)) 8 6 (C_A1 * c ^ (-(4 / 3 : ℝ)))
        (fun u => ((fctInnerT c V u ^ 6 * a ^ (-8 : ℤ) : ℝ) : ℂ)) := fun hTs => by
    have hp1 := hTs.mul Icc_subset_Ici_self hDu hTs
    have hp3 := hp1.mul Icc_subset_Ici_self hDu hTs
    have hp6 := (hp3.mul Icc_subset_Ici_self hDu hp3).const_mul hDu ((a ^ (-8 : ℤ) : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zpow_pos ha0 _), ha8] at hp6
    have hc_p : c ^ (2 / 3 : ℝ) * (c ^ (-(1 / 3 : ℝ))) ^ 6 = c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; congr 1; norm_num
    refine (hp6.mono_B Icc_subset_Ici_self (le_of_eq ?_)).congr hDu fun u _ => by push_cast; ring
    have h6 : (c ^ (-(1 / 3 : ℝ))) ^ 6 = c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
        (c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ))) := by ring
    dsimp only [C_A1]; rw [← hc_p, h6]; ring
  have hA1 := hA_of hT1_sym
  have hA2 := hA_of hT2_sym
  have hdA : FctSymClsOn (Icc 0 (fctUc c)) 8 6 (C_T6d * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo))
      (fun u => ((fctInnerT c (concreteInnerV K4 ε c L_hi α) u ^ 6 * a ^ (-8 : ℤ) : ℝ) : ℂ) -
        ((fctInnerT c (concreteInnerV K4 ε c L_lo α) u ^ 6 * a ^ (-8 : ℤ) : ℝ) : ℂ)) := by
    have hsq2 := hT2_sym.mul Icc_subset_Ici_self hDu hT2_sym
    have hsq1 := hT1_sym.mul Icc_subset_Ici_self hDu hT1_sym
    have hp12 := hT2_sym.mul Icc_subset_Ici_self hDu hT1_sym
    have hq2 := (hsq2.add hDu hp12).add hDu hsq1
    have hc3_1 := hT1_sym.mul Icc_subset_Ici_self hDu hsq1
    have hc3_2 := hT2_sym.mul Icc_subset_Ici_self hDu hsq2
    have hprod := (((hT_diff.mul Icc_subset_Ici_self hDu hq2).mul Icc_subset_Ici_self hDu
      (hc3_2.add hDu hc3_1)).const_mul hDu ((a ^ (-8 : ℤ) : ℝ) : ℂ))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zpow_pos ha0 _), ha8] at hprod
    have hc_p : c ^ (2 / 3 : ℝ) * (c ^ (-(1 / 3 : ℝ))) ^ 6 = c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; congr 1; norm_num
    refine (hprod.mono_B Icc_subset_Ici_self (le_of_eq ?_)).congr hDu fun u _ => by push_cast; ring
    have h6 : (c ^ (-(1 / 3 : ℝ))) ^ 6 = c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
        (c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ))) := by ring
    dsimp only [C_T6d]; rw [← hc_p, h6]; ring
  have hB1 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_B
      (fun u => phiKillR (((c ^ (1 / 12 : ℝ) * fctInnerT c (concreteInnerV K4 ε c L_lo α) u : ℝ) : ℂ) * Complex.I)) := by
    obtain ⟨hTcd, _, hTd, _⟩ := hBT hc1 hvp.hKV_small hvp.hjets_lo
    have hmaps : MapsTo (fun u => c ^ (1 / 12 : ℝ) * fctInnerT c (concreteInnerV K4 ε c L_lo α) u)
        (Icc 0 (fctUc c)) (Ioo (-1 / 2 : ℝ) (1 / 2)) := fun u hu => by
      have hs := hT_small hvp.hjets_lo u hu
      have hc120 : 0 ≤ c ^ (1 / 12 : ℝ) := by positivity
      have ha_inv : a⁻¹ = c ^ (1 / 12 : ℝ) := by dsimp only [a]; rw [Real.rpow_neg hc0.le, inv_inv]
      rw [div_eq_mul_inv, ha_inv, mul_comm] at hs
      exact ⟨by linarith only [mul_nonneg hc120 hs.1], by linarith only [hs.2.2]⟩
    have hBfM : c ^ (1 / 12 : ℝ) * B_T * c ^ (-(1 / 3 : ℝ)) * (1 + fctUc c) ≤ M_m := by
      have h1 := one_add_fctUc_le hc1
      have hc14 : c ^ (1 / 12 : ℝ) * c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12) = c ^ (-(1 / 6 : ℝ)) := by
        rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; congr 1; norm_num
      have hle1 : c ^ (-(1 / 6 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
      calc c ^ (1 / 12 : ℝ) * B_T * c ^ (-(1 / 3 : ℝ)) * (1 + fctUc c)
          ≤ c ^ (1 / 12 : ℝ) * B_T * c ^ (-(1 / 3 : ℝ)) * (4 * c ^ ((1 : ℝ) / 12)) := by gcongr
        _ = 4 * B_T * (c ^ (1 / 12 : ℝ) * c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
        _ ≤ 4 * B_T * 1 := by rw [hc14]; gcongr
        _ ≤ M_m := by rw [mul_one]; exact le_max_right _ _
    have hc12pos : 0 < c ^ (1 / 12 : ℝ) := Real.rpow_pos_of_pos hc0 _
    have hcomp := FctSymClsOn.comp_T_zero hUc0 (le_max_left _ _ : 1 ≤ M_m) isOpen_Ioo.uniqueDiffOn
      (hCR0_jc.1.of_le (by norm_num)) hCR0_nn
      (fun i hi t ht => by
        have := hCR0_jc.2 i hi t ht; rwa [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin] at this)
      (contDiffOn_const.mul hTcd) hmaps (by positivity) hBfM
      (fun j hj1 hj8 u hu => by
        have hTj := (hTcd.of_le (by exact_mod_cast hj8)).contDiffWithinAt hu
        rw [iteratedDerivWithin_const_mul (n := j) (c := c ^ (1 / 12 : ℝ)) hu hDu hTj,
          abs_mul, abs_of_pos hc12pos]
        exact (mul_le_mul_of_nonneg_left (hTd j hj1 hj8 u hu) hc12pos.le).trans_eq (by ring))
    exact (hcomp.mono_B Icc_subset_Ici_self (le_of_eq (by dsimp only [C_B, C_g0]; ring))).congr hDu
      fun u _ => rfl
  have hdB : FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C_pkR * c ^ (-(1 / 4 : ℝ)) * (L_hi - L_lo))
      (fun u => phiKillR (((c ^ (1 / 12 : ℝ) * fctInnerT c (concreteInnerV K4 ε c L_hi α) u : ℝ) : ℂ) * Complex.I) -
        phiKillR (((c ^ (1 / 12 : ℝ) * fctInnerT c (concreteInnerV K4 ε c L_lo α) u : ℝ) : ℂ) * Complex.I)) := by
    have hsc14 : c ^ (1 / 12 : ℝ) ≤ c ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hcomp := hsc hvp.hc10000 hvp.hKV_small (Real.rpow_pos_of_pos hc0 _) hsc14 hR_pk hCR0
      (mul_nonneg (sub_nonneg.mpr h12) (by have := pbcV_nonneg; have := pbC0_nonneg; positivity))
      hvp.hcd_lo hvp.hcd_hi hvp.hjets_lo hvp.hjets_hi hvp.hbd_lo hvp.hbd_hi hT_diff_c
      (contDiff_phiKillR_imag10.contDiffOn) hCR
    have hc14 : c ^ (1 / 12 : ℝ) * c ^ (-(1 / 3 : ℝ)) = c ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    refine (hcomp.mono_B Icc_subset_Ici_self (le_of_eq ?_)).congr hDu fun u _ => rfl
    calc C_sc * CR * c ^ (1 / 12 : ℝ) * (C_V * (L_hi - L_lo)) * c ^ (-(1 / 3 : ℝ))
        = (C_sc * CR * C_V) * (c ^ (1 / 12 : ℝ) * c ^ (-(1 / 3 : ℝ))) * (L_hi - L_lo) := by ring
      _ = C_pkR * c ^ (-(1 / 4 : ℝ)) * (L_hi - L_lo) := by dsimp only [C_pkR]; rw [hc14]
  have hC2 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_C
      (fun u => ((nfun (fctInnerT c (concreteInnerV K4 ε c L_hi α) u ^ 2) : ℝ) : ℂ)⁻¹) := by
    obtain ⟨hTcd, _, hTd, _⟩ := hBT hc1 hvp.hKV_small hvp.hjets_hi
    have hmaps : MapsTo (fctInnerT c (concreteInnerV K4 ε c L_hi α))
        (Icc 0 (fctUc c)) (Ioo (-R_n / 2) (R_n / 2)) := fun u hu => by
      have hs := hT_small hvp.hjets_hi u hu
      exact ⟨by linarith only [hs.1, hRn0], by linarith only [hs.2.1]⟩
    have hBfM : B_T * c ^ (-(1 / 3 : ℝ)) * (1 + fctUc c) ≤ M_m := by
      have h1 := one_add_fctUc_le hc1
      have hc14 : c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12) = c ^ (-(1 / 4 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      have hle1 : c ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
      calc B_T * c ^ (-(1 / 3 : ℝ)) * (1 + fctUc c)
          ≤ B_T * c ^ (-(1 / 3 : ℝ)) * (4 * c ^ ((1 : ℝ) / 12)) := by gcongr
        _ = 4 * B_T * (c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
        _ ≤ 4 * B_T * 1 := by rw [hc14]; gcongr
        _ ≤ M_m := by rw [mul_one]; exact le_max_right _ _
    have hcomp := FctSymClsOn.comp_T_zero hUc0 (le_max_left _ _ : 1 ≤ M_m) isOpen_Ioo.uniqueDiffOn
      (hn0_jc.1.of_le (by norm_num)) hCn0_nn
      (fun i hi t ht => by
        have := hn0_jc.2 i hi t ht; rwa [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin] at this)
      hTcd hmaps (by positivity) hBfM hTd
    exact (hcomp.mono_B Icc_subset_Ici_self (le_of_eq (by dsimp only [C_C, C_g0]; ring))).congr hDu
      fun u _ => rfl
  have hdC : FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C_ninv * c ^ (-(1 / 3 : ℝ)) * (L_hi - L_lo))
      (fun u => ((nfun (fctInnerT c (concreteInnerV K4 ε c L_hi α) u ^ 2) : ℝ) : ℂ)⁻¹ -
        ((nfun (fctInnerT c (concreteInnerV K4 ε c L_lo α) u ^ 2) : ℝ) : ℂ)⁻¹) := by
    have hcomp := hsc hvp.hc10000 hvp.hKV_small one_pos (Real.one_le_rpow hc1 (by norm_num)) hR_n hCn0
      (mul_nonneg (sub_nonneg.mpr h12) (by have := pbcV_nonneg; have := pbC0_nonneg; positivity))
      hvp.hcd_lo hvp.hcd_hi hvp.hjets_lo hvp.hjets_hi hvp.hbd_lo hvp.hbd_hi hT_diff_c
      (hn_cd.mono (Ioo_subset_Ioo (by linarith only [hRn0]) (by linarith only [hRn0]))) hn_jc
    refine (hcomp.mono_B Icc_subset_Ici_self (le_of_eq (by dsimp only [C_ninv]; ring))).congr hDu
      fun u _ => by simp only [one_mul]
  -- Combine `d(A*B*C) = (dA*B1 + A2*dB)*C2 + A1*B1*dC`
  have hdAB : FctSymClsOn (Icc 0 (fctUc c)) 8 7
      ((2 ^ 8 * (C_T6d * C_B) + 2 ^ 8 * (C_A1 * C_pkR)) * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo))
      (fun u => ((fctInnerT c (concreteInnerV K4 ε c L_hi α) u ^ 6 * a ^ (-8 : ℤ) : ℝ) : ℂ) *
          phiKillR (((c ^ (1 / 12 : ℝ) * fctInnerT c (concreteInnerV K4 ε c L_hi α) u : ℝ) : ℂ) * Complex.I) -
        ((fctInnerT c (concreteInnerV K4 ε c L_lo α) u ^ 6 * a ^ (-8 : ℤ) : ℝ) : ℂ) *
          phiKillR (((c ^ (1 / 12 : ℝ) * fctInnerT c (concreteInnerV K4 ε c L_lo α) u : ℝ) : ℂ) * Complex.I)) := by
    have hL0 : 0 ≤ L_hi - L_lo := sub_nonneg.mpr h12
    have h1 := ((hdA.mul Icc_subset_Ici_self hDu hB1).mono_p Icc_subset_Ici_self
      (by have := pbcV_nonneg; have := pbC0_nonneg; positivity) (by norm_num : (6 : ℝ) + 0 ≤ 7)).mono_B
      Icc_subset_Ici_self (le_of_eq (by ring))
    have h2 := (hA2.mul Icc_subset_Ici_self hDu hdB).mono_B Icc_subset_Ici_self (by
      have hc_le : c ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 4 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) := by
        calc c ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 4 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) * 1 := by
              gcongr; exact Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
          _ = c ^ (-(4 / 3 : ℝ)) := mul_one _
      have := pbcV_nonneg; have := pbC0_nonneg
      calc 2 ^ 8 * (C_A1 * c ^ (-(4 / 3 : ℝ))) * (C_pkR * c ^ (-(1 / 4 : ℝ)) * (L_hi - L_lo))
          = 2 ^ 8 * (C_A1 * C_pkR) * (c ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 4 : ℝ))) * (L_hi - L_lo) := by ring
        _ ≤ 2 ^ 8 * (C_A1 * C_pkR) * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo) := by gcongr)
    exact ((h1.add hDu h2).mono_B Icc_subset_Ici_self (le_of_eq (by ring))).congr hDu fun u _ => by ring
  have hd_pk : FctSymClsOn (Icc 0 (fctUc c)) 8 7 (C_dfin * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo))
      (fun u => phiKillDivM a (fctInnerT c (concreteInnerV K4 ε c L_hi α) u) -
        phiKillDivM a (fctInnerT c (concreteInnerV K4 ε c L_lo α) u)) := by
    have hL0 : 0 ≤ L_hi - L_lo := sub_nonneg.mpr h12
    have hpart1 := hdAB.mul Icc_subset_Ici_self hDu hC2
    have hAB1 := hA1.mul Icc_subset_Ici_self hDu hB1
    have hpart2 := (hAB1.mul Icc_subset_Ici_self hDu hdC).mono_B Icc_subset_Ici_self (by
      have hc_le : c ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) := by
        calc c ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) * 1 := by
              gcongr; exact Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
          _ = c ^ (-(4 / 3 : ℝ)) := mul_one _
      have := pbcV_nonneg; have := pbC0_nonneg
      calc 2 ^ 8 * (2 ^ 8 * (C_A1 * c ^ (-(4 / 3 : ℝ))) * C_B) * (C_ninv * c ^ (-(1 / 3 : ℝ)) * (L_hi - L_lo))
          = 2 ^ 8 * (2 ^ 8 * C_A1 * C_B) * C_ninv * (c ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ))) * (L_hi - L_lo) := by ring
        _ ≤ 2 ^ 8 * (2 ^ 8 * C_A1 * C_B) * C_ninv * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo) := by gcongr)
    have htot := ((hpart1.add hDu hpart2).mono_p Icc_subset_Ici_self
      (by have := pbcV_nonneg; have := pbC0_nonneg; positivity) (by norm_num : (7 : ℝ) + 0 ≤ 7)).mono_B
      Icc_subset_Ici_self (le_of_eq (by dsimp only [C_dfin]; ring))
    exact htot.congr hDu fun u hu => by
      rw [hpk_eq hvp.hjets_hi hu, hpk_eq hvp.hjets_lo hu]; ring
  have hK_diff : FctSymClsOn (Icc 0 (fctUc c)) 8 7 (C_dfin * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo))
      (fun u => (1 - (L1 : ℂ) * phiKillDivM a (fctInnerT c (concreteInnerV K4 ε c L_hi α) u)) -
        (1 - (L1 : ℂ) * phiKillDivM a (fctInnerT c (concreteInnerV K4 ε c L_lo α) u))) := by
    have hsm := hd_pk.const_mul hDu (-(L1 : ℂ))
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs] at hsm
    have hbd : |L1| * (C_dfin * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo)) ≤ C_dfin * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo) := by
      have := pbcV_nonneg; have := pbC0_nonneg; have := sub_nonneg.mpr h12
      calc |L1| * (C_dfin * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo))
          ≤ 1 * (C_dfin * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo)) := by gcongr
        _ = C_dfin * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo) := one_mul _
    exact (hsm.mono_B Icc_subset_Ici_self hbd).congr hDu fun u _ => by ring
  have hK_pt : ∀ {V : ℝ → ℝ}, FctVJets pbKV c V →
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_Kfin (fun u => 1 - (L1 : ℂ) * phiKillDivM a (fctInnerT c V u)) := fun {V} hVj => by
    have hs := (hpk hcpk hVj).shrink_p hUc0.le (by positivity) (by norm_num : (0 : ℝ) ≤ 6)
    have hUc6 := one_add_Uc_rpow_le hc1 6 (by norm_num)
    have h46 : (4 : ℝ) ^ (6 : ℝ) = 4 ^ 6 := by norm_num
    rw [h46] at hUc6
    have hc_le : c ^ (-(4 / 3 : ℝ)) * c ^ ((6 : ℝ) / 12) ≤ 1 := by
      rw [← Real.rpow_add hc0]; exact Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    have hs0 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (4 ^ 6 * C_pk) (fun u => -(L1 : ℂ) * phiKillDivM a (fctInnerT c V u)) := by
      have hm := hs.const_mul hDu (-(L1 : ℂ))
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs] at hm
      exact hm.mono_B Icc_subset_Ici_self (by
        calc |L1| * (C_pk * c ^ (-(4 / 3 : ℝ)) * (1 + fctUc c) ^ (6 - 0 : ℝ))
            ≤ 1 * (C_pk * c ^ (-(4 / 3 : ℝ)) * (4 ^ 6 * c ^ ((6 : ℝ) / 12))) := by
              rw [show (6 : ℝ) - 0 = 6 by norm_num]; gcongr
          _ = 4 ^ 6 * C_pk * (c ^ (-(4 / 3 : ℝ)) * c ^ ((6 : ℝ) / 12)) := by ring
          _ ≤ 4 ^ 6 * C_pk * 1 := by gcongr
          _ = 4 ^ 6 * C_pk := mul_one _)
    have hone := (one_symCls 8).mono_set Icc_subset_Ici_self hDu (uniqueDiffOn_Ici 0)
    exact ((hone.add hDu hs0).mono_B Icc_subset_Ici_self (le_of_eq (by dsimp only [C_Kfin]; ring))).congr hDu
      fun u _ => by ring
  exact ⟨hK_diff, hK_pt hvp.hjets_lo, hK_pt hvp.hjets_hi⟩

/-- info: 'FormalResearch.SignUncertainty.win_E_diff_and_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_E_diff_and_bounds

/-- info: 'FormalResearch.SignUncertainty.win_K_diff_and_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_K_diff_and_bounds

end FormalResearch.SignUncertainty