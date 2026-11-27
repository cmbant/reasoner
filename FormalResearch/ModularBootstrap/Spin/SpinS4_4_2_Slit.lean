/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_2_Strip
public import FormalResearch.ModularBootstrap.Spin.SpinS4_3_3_Cap
public import FormalResearch.ModularBootstrap.Spin.SpinS22bPartA
public import FormalResearch.ModularBootstrap.Spin.SpinS4Rc2Bound

/-!
# Section 4.2 (`s4:4.2`) Rescaled Strip & Slit Bounds

Supporting bounds for `SpinS4_4_2` (`Spin/SpinS4_4_2.lean`) in the rescaled variable `b = γ_N b'`:
1. `spinQSlice_rescaled_strip_bound`: polynomial boundary bound on `{|Im b'| ≤ 1/2}`.
2. `spinQSlice_rescaled_slit_bound`: uniform `L¹` bound on the real slits `{|b'| ≥ ξ_*}`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Spin

open Real Complex MeasureTheory Filter Topology Set Metric
open scoped Real ENNReal

/-- Polynomial boundary bound for the rescaled slice `b' ↦ Q_{c,N}(γ_N b')` on `{|Im b'| ≤ 1/2}`. -/
lemma spinQSlice_rescaled_strip_bound {c V C_V : ℝ} (hc : 49 ≤ c) (hV : 0 < V) (_hCV : 0 ≤ C_V)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    {χ : ℝ → ℝ} (hχ_meas : Measurable χ) (hχ_bd : ∀ v, 0 ≤ χ v ∧ χ v ≤ 1)
    (hχ_supp : ∀ v, V < |v| → χ v = 0)
    (h41_poly : ∀ (d : ℝ) (b : ℂ),
      |d| ≤ V * Real.sqrt ((c - 1) ^ (-(2 / 3 : ℝ))) →
      |b.im| ≤ (spinGamma ((c - 1) / 12) * (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹) / 2 →
      ‖spinTruncInvC ((c - 1) / 12) (Nat.ceil (Real.log (c - 1))) Φ (b + (d : ℂ)) (b - (d : ℂ))‖ ≤
        C_V * (Nat.ceil (Real.log (c - 1)) : ℝ) ^ 2 * (1 + |b.re| ^ 2) ^ 2)
    (hγN_le1 : spinGamma ((c - 1) / 12) * (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹ ≤ 1)
    {b' : ℂ} (hb' : |b'.im| ≤ 1 / 2) :
    let n := c - 1
    let a := n / 12
    let ε := n ^ (-(2 / 3 : ℝ))
    let N := Nat.ceil (Real.log n)
    let γN := spinGamma a * (spinLambda a ^ (N - 1))⁻¹
    ‖spinQSlice c N Φ χ ((γN : ℂ) * b')‖ ≤
      (2 * V * Real.sqrt ε * C_V * (N : ℝ) ^ 2) * (1 + |b'.re| ^ 2) ^ 2 := by
  intro n a ε N γN
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have hN_pos : 1 ≤ N := Nat.ceil_pos.mpr (Real.log_pos (by linarith))
  have hlam_gt1 : 1 < spinLambda a := spinLambda_gt_one_s4 ha2
  have hγN_pos : 0 < γN := mul_pos (spinGamma_pos ha2) (inv_pos.mpr (pow_pos (lt_trans zero_lt_one hlam_gt1) _))
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hn_pos _
  let V_bd : ℝ := V * Real.sqrt ε
  have hVbd0 : 0 ≤ V_bd := by positivity
  have hb_im : |((γN : ℂ) * b').im| ≤ γN / 2 := by
    rw [Complex.im_ofReal_mul, abs_mul, abs_of_pos hγN_pos]
    calc γN * |b'.im| ≤ γN * (1 / 2) := mul_le_mul_of_nonneg_left hb' hγN_pos.le
      _ = γN / 2 := by ring
  have hb_re : |((γN : ℂ) * b').re| ≤ |b'.re| := by
    rw [Complex.re_ofReal_mul, abs_mul, abs_of_pos hγN_pos]
    exact mul_le_of_le_one_left (abs_nonneg _) hγN_le1
  have hre_sq : (1 + |((γN : ℂ) * b').re| ^ 2) ^ 2 ≤ (1 + |b'.re| ^ 2) ^ 2 := by gcongr
  let M_b : ℝ := C_V * (N : ℝ) ^ 2 * (1 + |b'.re| ^ 2) ^ 2
  have hpt : ∀ d : ℝ, ‖(χ (d / Real.sqrt ε) : ℂ) *
      spinTruncInvC a N Φ ((γN : ℂ) * b' + (d : ℂ)) ((γN : ℂ) * b' - (d : ℂ))‖ ≤
      (Icc (-V_bd) V_bd).indicator (fun _ => M_b) d := fun d => by
    by_cases hd : d ∈ Icc (-V_bd) V_bd
    · rw [Set.indicator_of_mem hd, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hχ1 : |χ (d / Real.sqrt ε)| ≤ 1 := by
        have h := hχ_bd (d / Real.sqrt ε); exact abs_le.mpr ⟨by linarith, h.2⟩
      have h41 := h41_poly d ((γN : ℂ) * b') (abs_le.mpr hd) hb_im
      have h41' : ‖spinTruncInvC a N Φ ((γN : ℂ) * b' + (d : ℂ)) ((γN : ℂ) * b' - (d : ℂ))‖ ≤ M_b :=
        h41.trans (by dsimp [M_b]; gcongr)
      calc |χ (d / Real.sqrt ε)| * _ ≤ 1 * M_b := mul_le_mul hχ1 h41' (norm_nonneg _) zero_le_one
        _ = M_b := one_mul _
    · have hnot : V_bd < |d| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hd
        rcases hd with h1 | h2
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; linarith
      have hχ0 : χ (d / Real.sqrt ε) = 0 := by
        apply hχ_supp
        rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hε_pos), lt_div_iff₀ (Real.sqrt_pos.mpr hε_pos)]
        exact hnot
      rw [Set.indicator_of_notMem hd, hχ0, Complex.ofReal_zero, zero_mul, norm_zero]
  have hbd_int : Integrable ((Icc (-V_bd) V_bd).indicator (fun _ => M_b)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (hs := measure_Icc_lt_top.ne))
  have hmeas : AEStronglyMeasurable (fun d : ℝ => (χ (d / Real.sqrt ε) : ℂ) *
      spinTruncInvC a N Φ ((γN : ℂ) * b' + (d : ℂ)) ((γN : ℂ) * b' - (d : ℂ))) volume := by
    have hm1 : Measurable (fun d : ℝ => (χ (d / Real.sqrt ε) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (hχ_meas.comp (measurable_id.div_const _))
    have hm2 : Continuous (fun d : ℝ =>
        spinTruncInvC a N Φ ((γN : ℂ) * b' + (d : ℂ)) ((γN : ℂ) * b' - (d : ℂ))) :=
      continuous_spinTruncInvC_d hc hΦ hb_im
    exact (hm1.mul hm2.measurable).aestronglyMeasurable
  have hint_norm : Integrable (fun d : ℝ => ‖(χ (d / Real.sqrt ε) : ℂ) *
      spinTruncInvC a N Φ ((γN : ℂ) * b' + (d : ℂ)) ((γN : ℂ) * b' - (d : ℂ))‖) volume :=
    (hbd_int.mono' hmeas (Eventually.of_forall hpt)).norm
  unfold spinQSlice
  calc ‖∫ d : ℝ, (χ (d / Real.sqrt ε) : ℂ) *
          spinTruncInvC a N Φ ((γN : ℂ) * b' + (d : ℂ)) ((γN : ℂ) * b' - (d : ℂ))‖
      ≤ ∫ d : ℝ, ‖(χ (d / Real.sqrt ε) : ℂ) *
          spinTruncInvC a N Φ ((γN : ℂ) * b' + (d : ℂ)) ((γN : ℂ) * b' - (d : ℂ))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ d : ℝ, (Icc (-V_bd) V_bd).indicator (fun _ => M_b) d :=
        integral_mono hint_norm hbd_int hpt
    _ = (2 * V * Real.sqrt ε * C_V * (N : ℝ) ^ 2) * (1 + |b'.re| ^ 2) ^ 2 := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, Measure.real,
          Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
        dsimp [V_bd, M_b]; ring

private lemma spinTruncInvC_ofReal {a : ℝ} (ha : 2 ≤ a) (N : ℕ) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (xL xR : ℝ) :
    spinTruncInvC a N Φ (xL : ℂ) (xR : ℂ) = (spinTruncInv a N Φ xL xR : ℂ) := by
  unfold spinTruncInvC spinTruncInv spinDeltaAC spinDeltaA
  simp only [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ℓ _ => ?_
  have h1 : (spinLambda a : ℂ) * ((spinLambda a ^ j : ℝ) : ℂ) * (xL : ℂ) =
      (((spinLambda a * (spinLambda a ^ j * xL) : ℝ)) : ℂ) := by push_cast; ring
  have h2 : (spinLambda a : ℂ) * ((spinLambda a ^ ℓ : ℝ) : ℂ) * (xR : ℂ) =
      (((spinLambda a * (spinLambda a ^ ℓ * xR) : ℝ)) : ℂ) := by push_cast; ring
  rw [← mul_assoc, ← mul_assoc, h1, h2]
  exact spinDaC_eq_spinDa ha hΦ _ _

private lemma spinTruncInv_d4_neg_left {a : ℝ} (ha : 2 < a) (N : ℕ) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (xL xR : ℝ) :
    spinTruncInv a N Φ (-xL) xR = spinTruncInv a N Φ xL xR := by
  have h1 := spinG_sub_spinTruncInv ha Φ (-xL) xR N
  have h2 := spinG_sub_spinTruncInv ha Φ xL xR N
  simp only [mul_neg, spinG_d4_neg_left hΦ] at h1
  linarith

private lemma spinTruncInv_d4_neg_right {a : ℝ} (ha : 2 < a) (N : ℕ) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (xL xR : ℝ) :
    spinTruncInv a N Φ xL (-xR) = spinTruncInv a N Φ xL xR := by
  have h1 := spinG_sub_spinTruncInv ha Φ xL (-xR) N
  have h2 := spinG_sub_spinTruncInv ha Φ xL xR N
  simp only [mul_neg, spinG_d4_neg_right hΦ] at h1
  linarith

private lemma spinWc_mul_ge_exp_slit_half {c : ℝ} (hc : 49 ≤ c) {γN : ℝ} (hγN : 1 / 2 ≤ γN)
    {b' d : ℝ} (hb' : xiStar ≤ |b'|) (hd : |d| ≤ xiStar / 4) :
    let n := c - 1
    let a := n / 12
    spinSlitConst0 * (a * Real.exp ((n * γN) * slitL b')) ≤
      spinWc a (γN * b' + d) * spinWc a (γN * b' - d) := by
  intro n a
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have ha0 : 0 < a := by linarith
  have hxi005 : (0.05 : ℝ) < xiStar := xiStar_gt_005
  have hsd1 : (0.0075 : ℝ) ≤ |γN * b' + d| := by
    have h1 : |γN * b'| - |d| ≤ |γN * b' + d| := by
      simpa [sub_neg_eq_add, abs_neg] using abs_sub_abs_le_abs_sub (γN * b') (-d)
    have h2 : xiStar / 2 ≤ |γN * b'| := by
      rw [abs_mul, abs_of_pos (by linarith : 0 < γN)]; nlinarith [abs_nonneg b']
    linarith
  have hsd2 : (0.0075 : ℝ) ≤ |γN * b' - d| := by
    have h1 : |γN * b'| - |d| ≤ |γN * b' - d| := abs_sub_abs_le_abs_sub (γN * b') d
    have h2 : xiStar / 2 ≤ |γN * b'| := by
      rw [abs_mul, abs_of_pos (by linarith : 0 < γN)]; nlinarith [abs_nonneg b']
    linarith
  have hsum_abs : |γN * b' + d| + |γN * b' - d| = 2 * (γN * |b'|) := by
    have hd_le_b : |d| ≤ |γN * b'| := by
      have h2 : xiStar / 2 ≤ |γN * b'| := by
        rw [abs_mul, abs_of_pos (by linarith : 0 < γN)]; nlinarith [abs_nonneg b']
      linarith
    have hgb_eq : |γN * b'| = γN * |b'| := by rw [abs_mul, abs_of_pos (by linarith)]
    rcases le_total 0 (γN * b') with hs0 | hs0
    · rw [abs_of_nonneg hs0] at hd_le_b hgb_eq
      have h1 : 0 ≤ γN * b' + d := by linarith [(abs_le.mp hd_le_b).1]
      have h2 : 0 ≤ γN * b' - d := by linarith [(abs_le.mp hd_le_b).2]
      rw [abs_of_nonneg h1, abs_of_nonneg h2, ← hgb_eq]; ring
    · rw [abs_of_nonpos hs0] at hd_le_b hgb_eq
      have h1 : γN * b' + d ≤ 0 := by linarith [(abs_le.mp hd_le_b).2]
      have h2 : γN * b' - d ≤ 0 := by linarith [(abs_le.mp hd_le_b).1]
      rw [abs_of_nonpos h1, abs_of_nonpos h2, ← hgb_eq]; ring
  have hFc_ge : ∀ x : ℝ, (0.0075 : ℝ) ≤ x → (1 - Real.exp (-4 * π * 0.0075)) ^ 2 ≤ spinCalFc a x := by
    intro x hx
    have hγ_pos : 0 < spinGamma a := spinGamma_pos ha2
    have hγ_lt1 : spinGamma a < 1 := spinGamma_lt_one ha2
    have hγ_sq : spinGamma a ^ 2 = 1 - 2 / a := spinGamma_sq ha2.le
    have h1m : a * (1 - spinGamma a) ≥ 1 := by
      have hprod : (1 - spinGamma a) * (1 + spinGamma a) = 2 / a := by linarith [hγ_sq]
      have hsum_pos : 0 < 1 + spinGamma a := by linarith
      have h1 : a * (1 - spinGamma a) = 2 / (1 + spinGamma a) := by
        have h2 : a * (1 - spinGamma a) * (1 + spinGamma a) = 2 := by
          rw [mul_assoc, hprod]; field_simp [ha0.ne']
        exact eq_div_of_mul_eq hsum_pos.ne' h2
      rw [h1, ge_iff_le, one_le_div hsum_pos]; linarith
    have h1p : a * (1 + spinGamma a) ≥ 1 := by nlinarith
    have hexp_m : Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) ≤ Real.exp (-4 * π * 0.0075) := by
      refine Real.exp_le_exp.mpr ?_
      rw [show -π * (12 * a) * (1 - spinGamma a) * x / 3 = -(4 * π * (a * (1 - spinGamma a)) * x) by ring]
      have : 1 * (0.0075 : ℝ) ≤ (a * (1 - spinGamma a)) * x :=
        mul_le_mul h1m hx (by norm_num) (by linarith)
      nlinarith [Real.pi_pos]
    have hexp_p : Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) ≤ Real.exp (-4 * π * 0.0075) := by
      refine Real.exp_le_exp.mpr ?_
      rw [show -π * (12 * a) * (1 + spinGamma a) * x / 3 = -(4 * π * (a * (1 + spinGamma a)) * x) by ring]
      have : 1 * (0.0075 : ℝ) ≤ (a * (1 + spinGamma a)) * x :=
        mul_le_mul h1p hx (by norm_num) (by linarith)
      nlinarith [Real.pi_pos]
    have hnn : 0 ≤ 1 - Real.exp (-4 * π * 0.0075) :=
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos]))
    unfold spinCalFc; rw [sq]; exact mul_le_mul (by linarith) (by linarith) hnn (by linarith)
  rw [spinWc_factorization ha2.le (γN * b' + d), spinWc_factorization ha2.le (γN * b' - d)]
  have hF1 := hFc_ge _ hsd1
  have hF2 := hFc_ge _ hsd2
  have hnn : 0 ≤ (1 - Real.exp (-4 * π * 0.0075)) ^ 2 := sq_nonneg _
  have hFprod : spinSlitConst0 ≤ spinCalFc a |γN * b' + d| * spinCalFc a |γN * b' - d| := by
    unfold spinSlitConst0
    rw [show (1 - Real.exp (-4 * π * 0.0075)) ^ 4 =
        (1 - Real.exp (-4 * π * 0.0075)) ^ 2 * (1 - Real.exp (-4 * π * 0.0075)) ^ 2 by ring]
    exact mul_le_mul hF1 hF2 hnn (hnn.trans hF1)
  have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
  have hexp : Real.exp (4 * π * a * |γN * b' + d|) * Real.exp (4 * π * a * |γN * b' - d|) =
      Real.exp ((n * γN) * slitL b') := by
    rw [← Real.exp_add]; congr 1
    unfold slitL
    calc 4 * π * a * |γN * b' + d| + 4 * π * a * |γN * b' - d|
        = 4 * π * a * (|γN * b' + d| + |γN * b' - d|) := by ring
      _ = 4 * π * a * (2 * (γN * |b'|)) := by rw [hsum_abs]
      _ = ((12 * a) * γN) * (2 * π / 3 * |b'|) := by ring
      _ = (n * γN) * slitL b' := by dsimp [a, slitL]; ring
  calc spinSlitConst0 * (a * Real.exp ((n * γN) * slitL b'))
      ≤ (spinCalFc a |γN * b' + d| * spinCalFc a |γN * b' - d|) *
          (a * Real.exp ((n * γN) * slitL b')) := mul_le_mul_of_nonneg_right hFprod (by positivity)
    _ = (spinCalFc a |γN * b' + d| * spinCalFc a |γN * b' - d|) *
          ((Real.sqrt a * Real.sqrt a) *
            (Real.exp (4 * π * a * |γN * b' + d|) * Real.exp (4 * π * a * |γN * b' - d|))) := by
        rw [hsq, hexp]
    _ = (Real.sqrt a * Real.exp (4 * π * a * |γN * b' + d|) * spinCalFc a |γN * b' + d|) *
          (Real.sqrt a * Real.exp (4 * π * a * |γN * b' - d|) * spinCalFc a |γN * b' - d|) := by ring

private lemma lintegral_quads_spinTruncInv_wc {a C_r r₀ : ℝ} (ha2 : 2 < a) (hr₀ : 0 < r₀) (N : ℕ)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ)
    (hL1 : ∫ p in {q : ℝ × ℝ | r₀ ≤ q.1 ∧ r₀ ≤ q.2},
      |spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 ≤ C_r) :
    ∫⁻ q in {q : ℝ × ℝ | r₀ ≤ |q.1| ∧ r₀ ≤ |q.2|},
      ENNReal.ofReal (|spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) ≤
      ENNReal.ofReal (4 * C_r) := by
  let g : ℝ × ℝ → ℝ := fun q => |spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2
  let Qpp : Set (ℝ × ℝ) := {q : ℝ × ℝ | r₀ ≤ q.1 ∧ r₀ ≤ q.2}
  have hQpp_m : MeasurableSet Qpp :=
    (isClosed_le continuous_const continuous_fst).measurableSet.inter
      (isClosed_le continuous_const continuous_snd).measurableSet
  have hg_cont : Continuous g := by
    have hG : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
      unfold spinG; exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
    have hT : Continuous (fun p : ℝ × ℝ => spinTruncInv a N Φ p.1 p.2) := by
      have heq : (fun p : ℝ × ℝ => spinTruncInv a N Φ p.1 p.2) = fun p =>
          spinG a Φ p.1 p.2 - spinG a Φ p.1 (spinLambda a ^ N * p.2) -
            spinG a Φ (spinLambda a ^ N * p.1) p.2 +
            spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2) := by
        ext p; linarith [spinG_sub_spinTruncInv ha2 Φ p.1 p.2 N]
      rw [heq]
      exact (((hG.sub (hG.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd)))).sub
        (hG.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd))).add
        (hG.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))))
    have hW : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
    exact (hT.abs.mul (hW.comp continuous_fst)).mul (hW.comp continuous_snd)
  have hg_int : Integrable g volume := by
    obtain ⟨h00, _⟩ := integrable_dilate_and_bound_s4 ha2 hr₀ hΦ 0 0
    obtain ⟨h0N, _⟩ := integrable_dilate_and_bound_s4 ha2 hr₀ hΦ 0 N
    obtain ⟨hN0, _⟩ := integrable_dilate_and_bound_s4 ha2 hr₀ hΦ N 0
    obtain ⟨hNN, _⟩ := integrable_dilate_and_bound_s4 ha2 hr₀ hΦ N N
    have he00 : (fun p : ℝ × ℝ => |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) =
        fun p => |spinG a Φ (spinLambda a ^ 0 * p.1) (spinLambda a ^ 0 * p.2)| * spinWc a p.1 * spinWc a p.2 := by
      ext p; simp
    have he0N : (fun p : ℝ × ℝ => |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2) =
        fun p => |spinG a Φ (spinLambda a ^ 0 * p.1) (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 := by
      ext p; simp
    have heN0 : (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2) =
        fun p => |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ 0 * p.2)| * spinWc a p.1 * spinWc a p.2 := by
      ext p; simp
    rw [← he00] at h00; rw [← he0N] at h0N; rw [← heN0] at hN0
    refine (((h00.add h0N).add hN0).add hNN).mono' hg_cont.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    have hw1 := spinWc_nonneg ha2.le p.1
    have hw2 := spinWc_nonneg ha2.le p.2
    have hnn : 0 ≤ g p := mul_nonneg (mul_nonneg (abs_nonneg _) hw1) hw2
    rw [Real.norm_of_nonneg hnn]
    have hsub := spinG_sub_spinTruncInv ha2 Φ p.1 p.2 N
    have hab : |spinTruncInv a N Φ p.1 p.2| ≤
        |spinG a Φ p.1 p.2| + |spinG a Φ p.1 (spinLambda a ^ N * p.2)| +
        |spinG a Φ (spinLambda a ^ N * p.1) p.2| +
        |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| := by
      have h1 := abs_sub (spinG a Φ p.1 p.2) (spinG a Φ p.1 (spinLambda a ^ N * p.2))
      have h2 := abs_add_le (spinG a Φ p.1 p.2 - spinG a Φ p.1 (spinLambda a ^ N * p.2))
        (-spinG a Φ (spinLambda a ^ N * p.1) p.2)
      have h3 := abs_add_le (spinG a Φ p.1 p.2 - spinG a Φ p.1 (spinLambda a ^ N * p.2) -
        spinG a Φ (spinLambda a ^ N * p.1) p.2) (spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2))
      rw [← sub_eq_add_neg] at h2
      rw [abs_neg] at h2
      have heq : spinTruncInv a N Φ p.1 p.2 =
          spinG a Φ p.1 p.2 - spinG a Φ p.1 (spinLambda a ^ N * p.2) -
          spinG a Φ (spinLambda a ^ N * p.1) p.2 +
          spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2) := by linarith
      rw [heq]; linarith only [h1, h2, h3]
    dsimp [g]
    have hmul_b := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab hw1) hw2
    rw [add_mul, add_mul, add_mul, add_mul, add_mul, add_mul] at hmul_b
    exact hmul_b
  have hQpp_lin : ∫⁻ q in Qpp, ENNReal.ofReal (g q) ≤ ENNReal.ofReal C_r := by
    have heq := (ofReal_integral_eq_lintegral_ofReal (hg_int.integrableOn (s := Qpp))
      (Eventually.of_forall fun q => mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha2.le _))
        (spinWc_nonneg ha2.le _))).symm
    rw [heq]
    exact ENNReal.ofReal_le_ofReal hL1
  have hg_negL : ∀ q, g (-q.1, q.2) = g q := fun q => by
    dsimp [g]; rw [spinTruncInv_d4_neg_left ha2 N hΦ, spinWc_even]
  have hg_negR : ∀ q, g (q.1, -q.2) = g q := fun q => by
    dsimp [g]; rw [spinTruncInv_d4_neg_right ha2 N hΦ, spinWc_even]
  let mL : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toEquiv :=
        { toFun := fun q => (-q.1, q.2)
          invFun := fun q => (-q.1, q.2)
          left_inv := fun ⟨x, y⟩ => Prod.ext (neg_neg x) rfl
          right_inv := fun ⟨x, y⟩ => Prod.ext (neg_neg x) rfl }
      measurable_toFun := measurable_fst.neg.prodMk measurable_snd
      measurable_invFun := measurable_fst.neg.prodMk measurable_snd }
  let mR : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toEquiv :=
        { toFun := fun q => (q.1, -q.2)
          invFun := fun q => (q.1, -q.2)
          left_inv := fun ⟨x, y⟩ => Prod.ext rfl (neg_neg y)
          right_inv := fun ⟨x, y⟩ => Prod.ext rfl (neg_neg y) }
      measurable_toFun := measurable_fst.prodMk measurable_snd.neg
      measurable_invFun := measurable_fst.prodMk measurable_snd.neg }
  have hmL_vol : MeasurePreserving mL (volume : Measure (ℝ × ℝ)) volume := by
    have heq : (mL : ℝ × ℝ → ℝ × ℝ) = Prod.map Neg.neg id := rfl
    rw [heq, Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id (volume : Measure ℝ))
  have hmR_vol : MeasurePreserving mR (volume : Measure (ℝ × ℝ)) volume := by
    have heq : (mR : ℝ × ℝ → ℝ × ℝ) = Prod.map id Neg.neg := rfl
    rw [heq, Measure.volume_eq_prod]
    exact (MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg (volume : Measure ℝ))
  let Qnp : Set (ℝ × ℝ) := {q : ℝ × ℝ | r₀ ≤ -q.1 ∧ r₀ ≤ q.2}
  let Qpn : Set (ℝ × ℝ) := {q : ℝ × ℝ | r₀ ≤ q.1 ∧ r₀ ≤ -q.2}
  let Qnn : Set (ℝ × ℝ) := {q : ℝ × ℝ | r₀ ≤ -q.1 ∧ r₀ ≤ -q.2}
  have hsub : {q : ℝ × ℝ | r₀ ≤ |q.1| ∧ r₀ ≤ |q.2|} ⊆ Qpp ∪ Qnp ∪ Qpn ∪ Qnn := fun q ⟨h1, h2⟩ => by
    rcases le_or_gt 0 q.1 with hq1 | hq1 <;> rcases le_or_gt 0 q.2 with hq2 | hq2
    · exact Or.inl (Or.inl (Or.inl ⟨by rwa [abs_of_nonneg hq1] at h1, by rwa [abs_of_nonneg hq2] at h2⟩))
    · exact Or.inl (Or.inr ⟨by rwa [abs_of_nonneg hq1] at h1, by rwa [abs_of_neg hq2] at h2⟩)
    · exact Or.inl (Or.inl (Or.inr ⟨by rwa [abs_of_neg hq1] at h1, by rwa [abs_of_nonneg hq2] at h2⟩))
    · exact Or.inr ⟨by rwa [abs_of_neg hq1] at h1, by rwa [abs_of_neg hq2] at h2⟩
  have hQnp_m : MeasurableSet Qnp :=
    (isClosed_le continuous_const continuous_fst.neg).measurableSet.inter
      (isClosed_le continuous_const continuous_snd).measurableSet
  have hQpn_m : MeasurableSet Qpn :=
    (isClosed_le continuous_const continuous_fst).measurableSet.inter
      (isClosed_le continuous_const continuous_snd.neg).measurableSet
  have hQnn_m : MeasurableSet Qnn :=
    (isClosed_le continuous_const continuous_fst.neg).measurableSet.inter
      (isClosed_le continuous_const continuous_snd.neg).measurableSet
  have hlin_np : ∫⁻ q in Qnp, ENNReal.ofReal (g q) = ∫⁻ q in Qpp, ENNReal.ofReal (g q) := by
    have hind : Qnp.indicator (fun q => ENNReal.ofReal (g q)) =
        fun q => Qpp.indicator (fun y => ENNReal.ofReal (g y)) (mL q) := by
      ext q; by_cases hq : q ∈ Qnp
      · have hmq : mL q ∈ Qpp := hq
        rw [Set.indicator_of_mem hq, Set.indicator_of_mem hmq, show g (mL q) = g q from hg_negL q]
      · have hmq : mL q ∉ Qpp := hq
        rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hmq]
    rw [← lintegral_indicator hQnp_m, hind, ← lintegral_map (hg_cont.measurable.ennreal_ofReal.indicator hQpp_m)
      hmL_vol.measurable, hmL_vol.map_eq, lintegral_indicator hQpp_m]
  have hlin_pn : ∫⁻ q in Qpn, ENNReal.ofReal (g q) = ∫⁻ q in Qpp, ENNReal.ofReal (g q) := by
    have hind : Qpn.indicator (fun q => ENNReal.ofReal (g q)) =
        fun q => Qpp.indicator (fun y => ENNReal.ofReal (g y)) (mR q) := by
      ext q; by_cases hq : q ∈ Qpn
      · have hmq : mR q ∈ Qpp := hq
        rw [Set.indicator_of_mem hq, Set.indicator_of_mem hmq, show g (mR q) = g q from hg_negR q]
      · have hmq : mR q ∉ Qpp := hq
        rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hmq]
    rw [← lintegral_indicator hQpn_m, hind, ← lintegral_map (hg_cont.measurable.ennreal_ofReal.indicator hQpp_m)
      hmR_vol.measurable, hmR_vol.map_eq, lintegral_indicator hQpp_m]
  have hlin_nn : ∫⁻ q in Qnn, ENNReal.ofReal (g q) = ∫⁻ q in Qpp, ENNReal.ofReal (g q) := by
    have hind : Qnn.indicator (fun q => ENNReal.ofReal (g q)) =
        fun q => Qpn.indicator (fun y => ENNReal.ofReal (g y)) (mL q) := by
      ext q; by_cases hq : q ∈ Qnn
      · have hmq : mL q ∈ Qpn := hq
        rw [Set.indicator_of_mem hq, Set.indicator_of_mem hmq, show g (mL q) = g q from hg_negL q]
      · have hmq : mL q ∉ Qpn := hq
        rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hmq]
    rw [← lintegral_indicator hQnn_m, hind, ← lintegral_map (hg_cont.measurable.ennreal_ofReal.indicator hQpn_m)
      hmL_vol.measurable, hmL_vol.map_eq, lintegral_indicator hQpn_m, hlin_pn]
  have hU1 : ∫⁻ q in (Qpp ∪ Qnp), ENNReal.ofReal (g q) ≤
      (∫⁻ q in Qpp, ENNReal.ofReal (g q)) + (∫⁻ q in Qnp, ENNReal.ofReal (g q)) :=
    lintegral_union_le _ _ _
  have hU2 : ∫⁻ q in (Qpp ∪ Qnp ∪ Qpn), ENNReal.ofReal (g q) ≤
      (∫⁻ q in (Qpp ∪ Qnp), ENNReal.ofReal (g q)) + (∫⁻ q in Qpn, ENNReal.ofReal (g q)) :=
    lintegral_union_le _ _ _
  have hU3 : ∫⁻ q in (Qpp ∪ Qnp ∪ Qpn ∪ Qnn), ENNReal.ofReal (g q) ≤
      (∫⁻ q in (Qpp ∪ Qnp ∪ Qpn), ENNReal.ofReal (g q)) + (∫⁻ q in Qnn, ENNReal.ofReal (g q)) :=
    lintegral_union_le _ _ _
  calc ∫⁻ q in {q : ℝ × ℝ | r₀ ≤ |q.1| ∧ r₀ ≤ |q.2|}, ENNReal.ofReal (g q)
      ≤ ∫⁻ q in (Qpp ∪ Qnp ∪ Qpn ∪ Qnn), ENNReal.ofReal (g q) := lintegral_mono_set hsub
    _ ≤ (((∫⁻ q in Qpp, ENNReal.ofReal (g q)) + (∫⁻ q in Qnp, ENNReal.ofReal (g q))) +
          (∫⁻ q in Qpn, ENNReal.ofReal (g q))) + (∫⁻ q in Qnn, ENNReal.ofReal (g q)) := by
        have h12 : ∫⁻ q in (Qpp ∪ Qnp ∪ Qpn), ENNReal.ofReal (g q) ≤
            ((∫⁻ q in Qpp, ENNReal.ofReal (g q)) + (∫⁻ q in Qnp, ENNReal.ofReal (g q))) +
              (∫⁻ q in Qpn, ENNReal.ofReal (g q)) :=
          hU2.trans (add_le_add_left hU1 _)
        exact hU3.trans (add_le_add_left h12 _)
    _ = 4 * ∫⁻ q in Qpp, ENNReal.ofReal (g q) := by
        rw [hlin_np, hlin_pn, hlin_nn]
        symm
        calc 4 * ∫⁻ q in Qpp, ENNReal.ofReal (g q)
            = (1 + 1 + 1 + 1) * ∫⁻ q in Qpp, ENNReal.ofReal (g q) := by norm_num
          _ = (((∫⁻ q in Qpp, ENNReal.ofReal (g q)) + (∫⁻ q in Qpp, ENNReal.ofReal (g q))) +
                (∫⁻ q in Qpp, ENNReal.ofReal (g q))) + (∫⁻ q in Qpp, ENNReal.ofReal (g q)) := by
              simp only [add_mul, one_mul]
    _ ≤ 4 * ENNReal.ofReal C_r := by gcongr
    _ = ENNReal.ofReal (4 * C_r) := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]

/-- Uniform `L¹` slit bound for the rescaled slice `b' ↦ Q_{c,N}(γ_N b')` on `{|b'| ≥ ξ_*}`. -/
lemma spinQSlice_rescaled_slit_bound {c V C_r : ℝ} (hc : 49 ≤ c) (hV : 0 < V) (hCr : 0 ≤ C_r)
    (hV_eps : V * Real.sqrt ((c - 1) ^ (-(2 / 3 : ℝ))) ≤ xiStar / 4)
    (hγN_lo : 1 / 2 ≤ spinGamma ((c - 1) / 12) *
      (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    {χ : ℝ → ℝ} (hχ_meas : Measurable χ) (hχ_bd : ∀ v, 0 ≤ χ v ∧ χ v ≤ 1)
    (hχ_supp : ∀ v, V < |v| → χ v = 0)
    (h41_L1 : ∫ p in {q : ℝ × ℝ | xiStar / 4 ≤ q.1 ∧ xiStar / 4 ≤ q.2},
      |spinTruncInv ((c - 1) / 12) (Nat.ceil (Real.log (c - 1))) Φ p.1 p.2| *
        spinWc ((c - 1) / 12) p.1 * spinWc ((c - 1) / 12) p.2 ≤ C_r) :
    let n := c - 1
    let a := n / 12
    let N := Nat.ceil (Real.log n)
    let γN := spinGamma a * (spinLambda a ^ (N - 1))⁻¹
    IntegrableOn (fun b' : ℝ =>
        a * Real.exp ((n * γN) * slitL b') * ‖spinQSlice c N Φ χ ((γN : ℂ) * (b' : ℂ))‖)
      {t : ℝ | xiStar ≤ |t|} ∧
    ∫ b' in {t : ℝ | xiStar ≤ |t|},
        a * Real.exp ((n * γN) * slitL b') * ‖spinQSlice c N Φ χ ((γN : ℂ) * (b' : ℂ))‖ ≤
      4 * C_r / spinSlitConst0 := by
  intro n a N γN
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have ha0 : 0 < a := by linarith
  have hε_pos : 0 < n ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hn_pos _
  have hγN_pos : 0 < γN := by dsimp [γN]; linarith only [hγN_lo]
  let V_bd : ℝ := V * Real.sqrt (n ^ (-(2 / 3 : ℝ)))
  let S' : Set ℝ := {t : ℝ | xiStar ≤ |t|}
  let D_set : Set ℝ := Icc (-V_bd) V_bd
  have hS'_m : MeasurableSet S' := (isClosed_le continuous_const continuous_abs).measurableSet
  have hD_m : MeasurableSet D_set := measurableSet_Icc
  have hq_diff := spinQSlice_differentiableOn hc hV hΦ hχ_meas hχ_bd hχ_supp
  have hq_cont : Continuous (fun b' : ℝ => spinQSlice c N Φ χ ((γN : ℂ) * (b' : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro b'
    have him : |((γN : ℂ) * (b' : ℂ)).im| < γN / 2 := by
      rw [show ((γN : ℂ) * (b' : ℂ)).im = 0 by simp [Complex.mul_im]]
      rw [abs_zero]; exact half_pos hγN_pos
    have hopen : IsOpen {b : ℂ | |b.im| < γN / 2} := isOpen_lt Complex.continuous_im.abs continuous_const
    have hc_at : ContinuousAt (spinQSlice c N Φ χ) ((γN : ℂ) * (b' : ℂ)) :=
      ((hq_diff _ him).differentiableAt (hopen.mem_nhds him)).continuousAt
    have hlin : Continuous (fun t : ℝ => (γN : ℂ) * (t : ℂ)) :=
      continuous_const.mul Complex.continuous_ofReal
    exact (hc_at.comp (hlin.continuousAt (x := b')) :
      ContinuousAt (spinQSlice c N Φ χ ∘ fun t : ℝ => (γN : ℂ) * (t : ℂ)) b')
  let h_slit : ℝ → ℝ := fun b' =>
    a * Real.exp ((n * γN) * slitL b') * ‖spinQSlice c N Φ χ ((γN : ℂ) * (b' : ℂ))‖
  have hh_cont : Continuous h_slit := by
    have hL : Continuous slitL := by unfold slitL; fun_prop
    exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hL))).mul hq_cont.norm
  have hh_nn : ∀ b', 0 ≤ h_slit b' := fun b' => by dsimp [h_slit]; positivity
  -- Step 1: pointwise norm bound on `spinQSlice` by integral over `D_set`
  have hpt_slice : ∀ b' : ℝ,
      h_slit b' ≤ ∫ d in D_set, a * Real.exp ((n * γN) * slitL b') *
        |spinTruncInv a N Φ (γN * b' + d) (γN * b' - d)| := by
    intro b'
    have him_zero : |((γN : ℂ) * (b' : ℂ)).im| ≤ γN / 2 := by
      rw [show ((γN : ℂ) * (b' : ℂ)).im = 0 by simp [Complex.mul_im], abs_zero]
      exact (half_pos hγN_pos).le
    have hcont_d : Continuous (fun d : ℝ =>
        spinTruncInvC a N Φ ((γN : ℂ) * (b' : ℂ) + (d : ℂ)) ((γN : ℂ) * (b' : ℂ) - (d : ℂ))) :=
      continuous_spinTruncInvC_d hc hΦ him_zero
    have hdom_d : ∀ d : ℝ, ‖(χ (d / Real.sqrt (n ^ (-(2 / 3 : ℝ)))) : ℂ) *
        spinTruncInvC a N Φ ((γN : ℂ) * (b' : ℂ) + (d : ℂ)) ((γN : ℂ) * (b' : ℂ) - (d : ℂ))‖ ≤
        D_set.indicator (fun d => |spinTruncInv a N Φ (γN * b' + d) (γN * b' - d)|) d := fun d => by
      have heq_c : spinTruncInvC a N Φ ((γN : ℂ) * (b' : ℂ) + (d : ℂ)) ((γN : ℂ) * (b' : ℂ) - (d : ℂ)) =
          (spinTruncInv a N Φ (γN * b' + d) (γN * b' - d) : ℂ) := by
        rw [show (γN : ℂ) * (b' : ℂ) + (d : ℂ) = ((γN * b' + d : ℝ) : ℂ) by push_cast; ring,
          show (γN : ℂ) * (b' : ℂ) - (d : ℂ) = ((γN * b' - d : ℝ) : ℂ) by push_cast; ring]
        exact spinTruncInvC_ofReal ha2.le N hΦ _ _
      by_cases hd : d ∈ D_set
      · rw [Set.indicator_of_mem hd, norm_mul, Complex.norm_real, Real.norm_eq_abs, heq_c,
          Complex.norm_real, Real.norm_eq_abs]
        have hχ1 : |χ (d / Real.sqrt (n ^ (-(2 / 3 : ℝ))))| ≤ 1 := by
          have h := hχ_bd (d / Real.sqrt (n ^ (-(2 / 3 : ℝ)))); exact abs_le.mpr ⟨by linarith, h.2⟩
        exact mul_le_of_le_one_left (abs_nonneg _) hχ1
      · have hVbd0 : 0 ≤ V_bd := by dsimp [V_bd]; positivity
        have hnot : V_bd < |d| := by
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at hd
          rcases hd with h1 | h2
          · rw [abs_of_neg (by linarith only [h1, hVbd0])]; linarith only [h1]
          · rw [abs_of_nonneg (by linarith only [h2, hVbd0])]; linarith only [h2]
        have hχ0 : χ (d / Real.sqrt (n ^ (-(2 / 3 : ℝ)))) = 0 := by
          apply hχ_supp
          rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hε_pos), lt_div_iff₀ (Real.sqrt_pos.mpr hε_pos)]
          exact hnot
        rw [Set.indicator_of_notMem hd, hχ0, Complex.ofReal_zero, zero_mul, norm_zero]
    have hcont_abs : Continuous (fun d : ℝ => |spinTruncInv a N Φ (γN * b' + d) (γN * b' - d)|) := by
      have heq_f : (fun d : ℝ => |spinTruncInv a N Φ (γN * b' + d) (γN * b' - d)|) = fun d : ℝ =>
          |(spinTruncInvC a N Φ ((γN : ℂ) * (b' : ℂ) + (d : ℂ)) ((γN : ℂ) * (b' : ℂ) - (d : ℂ))).re| := by
        ext d
        rw [show (γN : ℂ) * (b' : ℂ) + (d : ℂ) = ((γN * b' + d : ℝ) : ℂ) by push_cast; ring,
          show (γN : ℂ) * (b' : ℂ) - (d : ℂ) = ((γN * b' - d : ℝ) : ℂ) by push_cast; ring,
          spinTruncInvC_ofReal ha2.le N hΦ _ _, Complex.ofReal_re]
      rw [heq_f]; exact (Complex.continuous_re.comp hcont_d).abs
    have hbd_int : Integrable (D_set.indicator (fun d => |spinTruncInv a N Φ (γN * b' + d) (γN * b' - d)|)) volume :=
      (integrable_indicator_iff hD_m).mpr hcont_abs.continuousOn.integrableOn_Icc
    have hm_int : AEStronglyMeasurable (fun d : ℝ => (χ (d / Real.sqrt (n ^ (-(2 / 3 : ℝ)))) : ℂ) *
        spinTruncInvC a N Φ ((γN : ℂ) * (b' : ℂ) + (d : ℂ)) ((γN : ℂ) * (b' : ℂ) - (d : ℂ))) volume :=
      ((Complex.continuous_ofReal.measurable.comp (hχ_meas.comp (measurable_id.div_const _))).mul
        hcont_d.measurable).aestronglyMeasurable
    have hnorm_int : Integrable (fun d : ℝ => ‖(χ (d / Real.sqrt (n ^ (-(2 / 3 : ℝ)))) : ℂ) *
        spinTruncInvC a N Φ ((γN : ℂ) * (b' : ℂ) + (d : ℂ)) ((γN : ℂ) * (b' : ℂ) - (d : ℂ))‖) volume :=
      (hbd_int.mono' hm_int (Eventually.of_forall hdom_d)).norm
    have hq_bd : ‖spinQSlice c N Φ χ ((γN : ℂ) * (b' : ℂ))‖ ≤
        ∫ d in D_set, |spinTruncInv a N Φ (γN * b' + d) (γN * b' - d)| := by
      unfold spinQSlice
      calc ‖∫ d : ℝ, _‖ ≤ ∫ d : ℝ, ‖_‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ d : ℝ, D_set.indicator (fun d => |spinTruncInv a N Φ (γN * b' + d) (γN * b' - d)|) d :=
            integral_mono hnorm_int hbd_int hdom_d
        _ = ∫ d in D_set, _ := integral_indicator hD_m
    calc h_slit b'
        ≤ (a * Real.exp ((n * γN) * slitL b')) *
            ∫ d in D_set, |spinTruncInv a N Φ (γN * b' + d) (γN * b' - d)| :=
          mul_le_mul_of_nonneg_left hq_bd (by positivity)
      _ = ∫ d in D_set, a * Real.exp ((n * γN) * slitL b') *
            |spinTruncInv a N Φ (γN * b' + d) (γN * b' - d)| := by
          rw [integral_const_mul]
  -- Step 2: bound `lintegral` via Tonelli + `γN * b'` scaling + `lintegral_xi_d_s4_3` + 4 quadrants
  let F : ℝ × ℝ → ℝ := fun p =>
    a * Real.exp ((n * γN) * slitL p.1) * |spinTruncInv a N Φ (γN * p.1 + p.2) (γN * p.1 - p.2)|
  have hF_meas : Measurable F := by
    have hg : Measurable Φ := hΦ.cont.measurable
    have hmG : ∀ c1 c2 : ℝ, Measurable (fun p : ℝ × ℝ =>
        spinG a Φ (c1 * (γN * p.1 + p.2)) (c2 * (γN * p.1 - p.2))) := fun c1 c2 => by
      unfold spinG
      exact hg.comp ((measurable_const.mul (measurable_const.mul ((measurable_const.mul measurable_fst).add measurable_snd))).prodMk
        (measurable_const.mul (measurable_const.mul ((measurable_const.mul measurable_fst).sub measurable_snd))))
    have hT : Measurable (fun p : ℝ × ℝ => spinTruncInv a N Φ (γN * p.1 + p.2) (γN * p.1 - p.2)) := by
      have heq : (fun p : ℝ × ℝ => spinTruncInv a N Φ (γN * p.1 + p.2) (γN * p.1 - p.2)) = fun p =>
          spinG a Φ (1 * (γN * p.1 + p.2)) (1 * (γN * p.1 - p.2)) -
          spinG a Φ (1 * (γN * p.1 + p.2)) (spinLambda a ^ N * (γN * p.1 - p.2)) -
          spinG a Φ (spinLambda a ^ N * (γN * p.1 + p.2)) (1 * (γN * p.1 - p.2)) +
          spinG a Φ (spinLambda a ^ N * (γN * p.1 + p.2)) (spinLambda a ^ N * (γN * p.1 - p.2)) := by
        ext p; simp only [one_mul]; linarith [spinG_sub_spinTruncInv ha2 Φ (γN * p.1 + p.2) (γN * p.1 - p.2) N]
      rw [heq]
      exact (((hmG _ _).sub (hmG _ _)).sub (hmG _ _)).add (hmG _ _)
    have hL : Continuous slitL := by unfold slitL; fun_prop
    exact (measurable_const.mul (Real.continuous_exp.measurable.comp
      (measurable_const.mul (hL.measurable.comp measurable_fst)))).mul hT.abs
  have hF_dom_quads : ∫⁻ p in (S' ×ˢ D_set), ENNReal.ofReal (F p) ≤
      ENNReal.ofReal (4 * C_r / spinSlitConst0) := by
    let g_wc : ℝ × ℝ → ℝ := fun q => |spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2
    have hg_wc_m : Measurable g_wc := by
      have hg : Measurable Φ := hΦ.cont.measurable
      have hmG : ∀ c1 c2 : ℝ, Measurable (fun q : ℝ × ℝ => spinG a Φ (c1 * q.1) (c2 * q.2)) :=
        fun c1 c2 => by
          unfold spinG
          exact hg.comp ((measurable_const.mul (measurable_const.mul measurable_fst)).prodMk
            (measurable_const.mul (measurable_const.mul measurable_snd)))
      have hT : Measurable (fun q : ℝ × ℝ => spinTruncInv a N Φ q.1 q.2) := by
        have heq : (fun q : ℝ × ℝ => spinTruncInv a N Φ q.1 q.2) = fun q =>
            spinG a Φ (1 * q.1) (1 * q.2) -
            spinG a Φ (1 * q.1) (spinLambda a ^ N * q.2) -
            spinG a Φ (spinLambda a ^ N * q.1) (1 * q.2) +
            spinG a Φ (spinLambda a ^ N * q.1) (spinLambda a ^ N * q.2) := by
          ext q; simp only [one_mul]; linarith [spinG_sub_spinTruncInv ha2 Φ q.1 q.2 N]
        rw [heq]
        exact (((hmG _ _).sub (hmG _ _)).sub (hmG _ _)).add (hmG _ _)
      have hW : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
      exact (hT.abs.mul (hW.measurable.comp measurable_fst)).mul (hW.measurable.comp measurable_snd)
    let Gq : ℝ × ℝ → ℝ := fun q => spinSlitConst0⁻¹ * g_wc q
    have hGq_meas : Measurable Gq := measurable_const.mul hg_wc_m
    let Q_all : Set (ℝ × ℝ) := {q : ℝ × ℝ | xiStar / 4 ≤ |q.1| ∧ xiStar / 4 ≤ |q.2|}
    have hQall_m : MeasurableSet Q_all :=
      (isClosed_le continuous_const continuous_fst.abs).measurableSet.inter
        (isClosed_le continuous_const continuous_snd.abs).measurableSet
    have hpt_F : ∀ p ∈ S' ×ˢ D_set,
        ENNReal.ofReal (F p) ≤ (Q_all.indicator (fun q => ENNReal.ofReal (Gq q))) (γN * p.1 + p.2, γN * p.1 - p.2) := by
      intro p ⟨hp1, hp2⟩
      have hp1' : xiStar ≤ |p.1| := hp1
      have hd_abs : |p.2| ≤ xiStar / 4 := (abs_le.mpr hp2).trans hV_eps
      have hgb_ge : xiStar / 2 ≤ |γN * p.1| := by
        rw [abs_mul, abs_of_pos hγN_pos]
        calc xiStar / 2 = (1 / 2) * xiStar := by ring
          _ ≤ γN * |p.1| := mul_le_mul hγN_lo hp1' xiStar_pos.le (by positivity)
      have hq1 : xiStar / 4 ≤ |γN * p.1 + p.2| := by
        have h1 : |γN * p.1| - |p.2| ≤ |γN * p.1 + p.2| := by
          simpa [sub_neg_eq_add, abs_neg] using abs_sub_abs_le_abs_sub (γN * p.1) (-p.2)
        linarith
      have hq2 : xiStar / 4 ≤ |γN * p.1 - p.2| := by
        have h1 : |γN * p.1| - |p.2| ≤ |γN * p.1 - p.2| := abs_sub_abs_le_abs_sub (γN * p.1) p.2
        linarith
      rw [Set.indicator_of_mem (⟨hq1, hq2⟩ : (γN * p.1 + p.2, γN * p.1 - p.2) ∈ Q_all)]
      apply ENNReal.ofReal_le_ofReal
      have hwc := spinWc_mul_ge_exp_slit_half hc hγN_lo hp1 hd_abs
      have hc0 := spinSlitConst0_pos
      have hmul := mul_le_mul_of_nonneg_right hwc (abs_nonneg (spinTruncInv a N Φ (γN * p.1 + p.2) (γN * p.1 - p.2)))
      have hle : spinSlitConst0 * F p ≤ g_wc (γN * p.1 + p.2, γN * p.1 - p.2) := by
        dsimp [F, g_wc]
        calc spinSlitConst0 * (a * Real.exp (n * γN * slitL p.1) *
                |spinTruncInv a N Φ (γN * p.1 + p.2) (γN * p.1 - p.2)|)
            = spinSlitConst0 * (a * Real.exp (n * γN * slitL p.1)) *
                |spinTruncInv a N Φ (γN * p.1 + p.2) (γN * p.1 - p.2)| := by ring
          _ ≤ spinWc a (γN * p.1 + p.2) * spinWc a (γN * p.1 - p.2) *
                |spinTruncInv a N Φ (γN * p.1 + p.2) (γN * p.1 - p.2)| := hmul
          _ = _ := by ring
      calc F p = spinSlitConst0⁻¹ * (spinSlitConst0 * F p) := by field_simp [hc0.ne']
        _ ≤ Gq (γN * p.1 + p.2, γN * p.1 - p.2) := by
            dsimp [Gq]; exact mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hc0.le)
    let ϕ : ℝ × ℝ → ℝ≥0∞ := Q_all.indicator (fun q => ENNReal.ofReal (Gq q))
    have hϕ_m : Measurable ϕ := (hGq_meas.ennreal_ofReal).indicator hQall_m
    let sc : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
      { toEquiv :=
          { toFun := fun p => (γN * p.1, p.2)
            invFun := fun b => (γN⁻¹ * b.1, b.2)
            left_inv := fun ⟨x, y⟩ => Prod.ext (by field_simp [hγN_pos.ne']) rfl
            right_inv := fun ⟨x, y⟩ => Prod.ext (by field_simp [hγN_pos.ne']) rfl }
        measurable_toFun := (measurable_const.mul measurable_fst).prodMk measurable_snd
        measurable_invFun := (measurable_const.mul measurable_fst).prodMk measurable_snd }
    have hsc_map : Measure.map sc (volume : Measure (ℝ × ℝ)) =
        ENNReal.ofReal γN⁻¹ • (volume : Measure (ℝ × ℝ)) := by
      have heq : (sc : ℝ × ℝ → ℝ × ℝ) = Prod.map (γN * ·) id := rfl
      rw [heq, Measure.volume_eq_prod,
        ← Measure.map_prod_map _ _ (measurable_const_mul γN) measurable_id,
        Measure.map_id, Real.map_volume_mul_left hγN_pos.ne', Measure.prod_smul_left]
      congr 2; rw [abs_inv, abs_of_pos hγN_pos]
    have hsc_int : ∫⁻ p : ℝ × ℝ, ϕ (γN * p.1 + p.2, γN * p.1 - p.2) =
        ENNReal.ofReal γN⁻¹ * ∫⁻ q : ℝ × ℝ, ϕ (q.1 + q.2, q.1 - q.2) := by
      have hm_comp : Measurable (fun q : ℝ × ℝ => ϕ (q.1 + q.2, q.1 - q.2)) :=
        hϕ_m.comp ((measurable_fst.add measurable_snd).prodMk (measurable_fst.sub measurable_snd))
      have h1 := lintegral_map (f := fun q : ℝ × ℝ => ϕ (q.1 + q.2, q.1 - q.2)) hm_comp sc.measurable
      rw [hsc_map, lintegral_smul_measure] at h1
      simpa [sc] using h1.symm
    have hsh_int : ∫⁻ y : ℝ × ℝ, ϕ y = ENNReal.ofReal 2 * ∫⁻ q : ℝ × ℝ, ϕ (q.1 + q.2, q.1 - q.2) :=
      lintegral_xi_d_s4_3 hϕ_m
    have hQ_lin := lintegral_quads_spinTruncInv_wc ha2 (by positivity [xiStar_pos] : 0 < xiStar / 4) N hΦ h41_L1
    have hϕ_tot : ∫⁻ y : ℝ × ℝ, ϕ y ≤ ENNReal.ofReal (4 * C_r / spinSlitConst0) := by
      dsimp [ϕ]
      rw [lintegral_indicator hQall_m]
      calc ∫⁻ q in Q_all, ENNReal.ofReal (Gq q)
          = ∫⁻ q in Q_all, ENNReal.ofReal spinSlitConst0⁻¹ * ENNReal.ofReal (g_wc q) := by
            refine setLIntegral_congr_fun hQall_m fun q _ => ?_
            dsimp [Gq]; exact ENNReal.ofReal_mul (inv_nonneg.mpr spinSlitConst0_pos.le)
        _ = ENNReal.ofReal spinSlitConst0⁻¹ * ∫⁻ q in Q_all, ENNReal.ofReal (g_wc q) :=
            lintegral_const_mul _ hg_wc_m.ennreal_ofReal
        _ ≤ ENNReal.ofReal spinSlitConst0⁻¹ * ENNReal.ofReal (4 * C_r) := by gcongr
        _ = ENNReal.ofReal (4 * C_r / spinSlitConst0) := by
            rw [← ENNReal.ofReal_mul (inv_nonneg.mpr spinSlitConst0_pos.le), inv_mul_eq_div]
    calc ∫⁻ p in S' ×ˢ D_set, ENNReal.ofReal (F p)
        ≤ ∫⁻ p in S' ×ˢ D_set, ϕ (γN * p.1 + p.2, γN * p.1 - p.2) :=
          setLIntegral_mono' (hS'_m.prod hD_m) hpt_F
      _ ≤ ∫⁻ p : ℝ × ℝ, ϕ (γN * p.1 + p.2, γN * p.1 - p.2) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal γN⁻¹ * ∫⁻ q : ℝ × ℝ, ϕ (q.1 + q.2, q.1 - q.2) := hsc_int
      _ ≤ ENNReal.ofReal 2 * ∫⁻ q : ℝ × ℝ, ϕ (q.1 + q.2, q.1 - q.2) := by
          gcongr; exact inv_le_of_inv_le₀ (by norm_num) (by linarith only [hγN_lo])
      _ = ∫⁻ y : ℝ × ℝ, ϕ y := hsh_int.symm
      _ ≤ ENNReal.ofReal (4 * C_r / spinSlitConst0) := hϕ_tot
  have hprod_m : (volume.restrict S').prod (volume.restrict D_set) =
      (volume : Measure (ℝ × ℝ)).restrict (S' ×ˢ D_set) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hlin_h : ∫⁻ b' in S', ENNReal.ofReal (h_slit b') ≤
      ENNReal.ofReal (4 * C_r / spinSlitConst0) := by
    have h1 : ∀ b' : ℝ, ENNReal.ofReal (h_slit b') ≤ ∫⁻ d in D_set, ENNReal.ofReal (F (b', d)) := by
      intro b'
      have hF_b'_m : Measurable (fun d : ℝ => F (b', d)) :=
        hF_meas.comp (measurable_const.prodMk measurable_id)
      have hF_b'_int : IntegrableOn (fun d : ℝ => F (b', d)) D_set volume := by
        have hF_b'_cont : Continuous (fun d : ℝ => F (b', d)) := by
          have hc_re : Continuous (fun d : ℝ => |spinTruncInv a N Φ (γN * b' + d) (γN * b' - d)|) := by
            have him_zero : |((γN : ℂ) * (b' : ℂ)).im| ≤ γN / 2 := by
              rw [show ((γN : ℂ) * (b' : ℂ)).im = 0 by simp [Complex.mul_im], abs_zero]
              exact (half_pos hγN_pos).le
            have hcont_d := continuous_spinTruncInvC_d hc hΦ him_zero
            have heq_f : (fun d : ℝ => |spinTruncInv a N Φ (γN * b' + d) (γN * b' - d)|) = fun d : ℝ =>
                |(spinTruncInvC a N Φ ((γN : ℂ) * (b' : ℂ) + (d : ℂ)) ((γN : ℂ) * (b' : ℂ) - (d : ℂ))).re| := by
              ext d
              rw [show (γN : ℂ) * (b' : ℂ) + (d : ℂ) = ((γN * b' + d : ℝ) : ℂ) by push_cast; ring,
                show (γN : ℂ) * (b' : ℂ) - (d : ℂ) = ((γN * b' - d : ℝ) : ℂ) by push_cast; ring,
                spinTruncInvC_ofReal ha2.le N hΦ _ _, Complex.ofReal_re]
            rw [heq_f]; exact (Complex.continuous_re.comp hcont_d).abs
          dsimp [F]; exact continuous_const.mul hc_re
        exact hF_b'_cont.continuousOn.integrableOn_Icc
      have heq_lin := ofReal_integral_eq_lintegral_ofReal hF_b'_int
        (Eventually.of_forall fun d => by dsimp [F]; positivity)
      calc ENNReal.ofReal (h_slit b')
          ≤ ENNReal.ofReal (∫ d in D_set, F (b', d)) := ENNReal.ofReal_le_ofReal (hpt_slice b')
        _ = ∫⁻ d in D_set, ENNReal.ofReal (F (b', d)) := heq_lin
    calc ∫⁻ b' in S', ENNReal.ofReal (h_slit b')
        ≤ ∫⁻ b' in S', ∫⁻ d in D_set, ENNReal.ofReal (F (b', d)) := lintegral_mono h1
      _ = ∫⁻ p in S' ×ˢ D_set, ENNReal.ofReal (F p) := by
          rw [← hprod_m, lintegral_prod _ (hF_meas.ennreal_ofReal).aemeasurable]
      _ ≤ ENNReal.ofReal (4 * C_r / spinSlitConst0) := hF_dom_quads
  have hh_int : IntegrableOn h_slit S' volume := by
    refine ⟨hh_cont.aestronglyMeasurable, hasFiniteIntegral_iff_eNorm.mpr ?_⟩
    have heq_n : ∫⁻ b' in S', ‖h_slit b'‖ₑ = ∫⁻ b' in S', ENNReal.ofReal (h_slit b') :=
      setLIntegral_congr_fun hS'_m fun b' _ => by
        rw [eNorm_eq_ofReal_abs, abs_of_nonneg (hh_nn b')]
    rw [heq_n]
    exact hlin_h.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hh_int, ?_⟩
  have heq_b : ENNReal.ofReal (∫ b' in S', h_slit b') = ∫⁻ b' in S', ENNReal.ofReal (h_slit b') :=
    ofReal_integral_eq_lintegral_ofReal hh_int (Eventually.of_forall hh_nn)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity [hCr, spinSlitConst0_pos.le])).mp (heq_b.symm ▸ hlin_h)

end FormalResearch.ModularBootstrap.Spin
