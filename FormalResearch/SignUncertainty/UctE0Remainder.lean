module

public import FormalResearch.SignUncertainty.UctE0Deriv
public import FormalResearch.SignUncertainty.UctEnv2

/-!
# The `C²` remainder of `E₀` after subtracting a polynomial in `τ` (F2a, `uct:bump-weighted` far band)

`E0_poly_remainder`: there are a weak weighted polynomial `P` and constants `C, p` such that for every `h ∈ (0, 1/4]` (`c = h⁻²`, `v = τ/h`) the function
`ε(τ) = E₀(τ) - (E₀'(0) τ + G_h(τ/h))` is `C²`, where `G_h'' (v) = P(h, v)` is the double `v`-antiderivative of `P(h, ·)` vanishing to order two at `0`
(so `E₀'(0) τ + G_h(τ/h)` is a polynomial in `τ`), and
`|ε| ≤ C h⁴ (1+|v|)^p`, `|ε'| ≤ C h³ (1+|v|)^p`, `|ε''| ≤ C h² (1+|v|)^p` for all real `τ`.
Inside `h(1+|v|)³ ≤ 1/2` this is `K2_wexpW` (`ε'' = h⁻² (K2 - P)`) integrated twice from `τ = 0` (where `ε = ε' = 0`); outside, the crude `Env2`
envelope of `kernel_amp_env2` and `1 < 2 h (1+|v|)³` suffice.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology
open FormalResearch.Asymptotics

namespace FormalResearch.SignUncertainty

/-- First antiderivative of `∑ coeff h^{d0} v^{d1}` vanishing at `0`. -/
noncomputable def gP1 (P : P2) (h v : ℝ) : ℂ :=
  ∑ d ∈ P.support, P.coeff d * (h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1 + 1) / (((d 1 + 1 : ℕ)) : ℂ)

/-- Second antiderivative of `∑ coeff h^{d0} v^{d1}` vanishing to order two at `0`. -/
noncomputable def gP0 (P : P2) (h v : ℝ) : ℂ :=
  ∑ d ∈ P.support, P.coeff d * (h : ℂ) ^ (d 0) / (((d 1 + 1 : ℕ)) : ℂ) * (v : ℂ) ^ (d 1 + 2) / (((d 1 + 2 : ℕ)) : ℂ)

lemma hasDerivAt_pow_div (a : ℂ) (k : ℕ) (hk : 1 ≤ k) (v : ℝ) :
    HasDerivAt (fun v : ℝ => a * (v : ℂ) ^ k / (k : ℂ)) (a * (v : ℂ) ^ (k - 1)) v := by
  have h1 := ((hasDerivAt_pow k (v : ℂ)).comp_ofReal).const_mul a |>.div_const (k : ℂ)
  refine h1.congr_deriv ?_
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  field_simp

lemma hasDerivAt_gP1 (P : P2) (h v : ℝ) : HasDerivAt (gP1 P h) (wev h v P) v := by
  rw [wev_eq]
  unfold gP1
  have := HasDerivAt.fun_sum (u := P.support) (A := fun d (v : ℝ) => P.coeff d * (h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1 + 1) / (((d 1 + 1 : ℕ)) : ℂ))
    (A' := fun d => P.coeff d * (h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1)) (x := v)
    (fun d _ => by simpa using hasDerivAt_pow_div (P.coeff d * (h : ℂ) ^ (d 0)) (d 1 + 1) (by omega) v)
  convert this using 1
  exact Finset.sum_congr rfl fun d _ => by ring

lemma hasDerivAt_gP0 (P : P2) (h v : ℝ) : HasDerivAt (gP0 P h) (gP1 P h v) v := by
  unfold gP0 gP1
  have := HasDerivAt.fun_sum (u := P.support) (A := fun d (v : ℝ) => P.coeff d * (h : ℂ) ^ (d 0) / (((d 1 + 1 : ℕ)) : ℂ) * (v : ℂ) ^ (d 1 + 2) / (((d 1 + 2 : ℕ)) : ℂ))
    (A' := fun d => P.coeff d * (h : ℂ) ^ (d 0) / (((d 1 + 1 : ℕ)) : ℂ) * (v : ℂ) ^ (d 1 + 1)) (x := v)
    (fun d _ => by simpa using hasDerivAt_pow_div (P.coeff d * (h : ℂ) ^ (d 0) / (((d 1 + 1 : ℕ)) : ℂ)) (d 1 + 2) (by omega) v)
  convert this using 1
  refine Finset.sum_congr rfl fun d _ => ?_
  have : (((d 1 + 1 : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast (by omega : d 1 + 1 ≠ 0)
  field_simp

lemma gP1_zero (P : P2) (h : ℝ) : gP1 P h 0 = 0 := by simp [gP1]
lemma gP0_zero (P : P2) (h : ℝ) : gP0 P h 0 = 0 := by simp [gP0]

lemma contDiff_gP0 (P : P2) (h : ℝ) : ContDiff ℝ 2 (gP0 P h) := by
  unfold gP0
  refine ContDiff.sum fun d _ => ?_
  exact ((contDiff_const.mul (Complex.ofRealCLM.contDiff.pow (d 1 + 2))).div_const _)

lemma kernelAmp_zero (c : ℝ) : kernelAmp c 0 = 1 := by
  unfold kernelAmp
  simp [cpowI_zero, ellN_zero, binetDiff]

lemma bumpE0_zero (c : ℝ) : bumpE0 c 0 = 0 := by simp [bumpE0, kernelAmp_zero]

lemma contDiff_bumpE0 {c : ℝ} (hc : 2 ≤ c) : ContDiff ℝ 2 (bumpE0 c) := by
  obtain ⟨Ca, hCa, haenv⟩ := kernel_amp_env2
  exact (haenv c hc).1.sub contDiff_const

lemma deriv_bumpE0 (c : ℝ) : deriv (bumpE0 c) = deriv (kernelAmp c) := by
  funext τ
  unfold bumpE0
  exact deriv_sub_const _

lemma deriv_deriv_bumpE0 (c : ℝ) : deriv (deriv (bumpE0 c)) = deriv (deriv (kernelAmp c)) := by
  rw [deriv_bumpE0]

/-- The remainder `ε = E₀ - (E₀'(0) τ + G_h(τ/h))`. -/
noncomputable def E0r (P : P2) (h τ : ℝ) : ℂ :=
  bumpE0 ((h ^ 2)⁻¹) τ - (deriv (bumpE0 ((h ^ 2)⁻¹)) 0 * (τ : ℂ) + gP0 P h (τ / h))

lemma hasDerivAt_polyPart (P : P2) {h : ℝ} (_hh : 0 < h) (a : ℂ) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => a * (τ : ℂ) + gP0 P h (τ / h)) (a + ((h⁻¹ : ℝ) : ℂ) * gP1 P h (τ / h)) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => a * (τ : ℂ)) a τ := by
    simpa using ((hasDerivAt_id τ).ofReal_comp).const_mul a
  have h2 : HasDerivAt (fun τ : ℝ => τ / h) h⁻¹ τ := by
    simpa using (hasDerivAt_id τ).div_const h
  have h3 := (hasDerivAt_gP0 P h (τ / h)).scomp τ h2
  have h4 : HasDerivAt (fun τ : ℝ => gP0 P h (τ / h)) (((h⁻¹ : ℝ) : ℂ) * gP1 P h (τ / h)) τ := by
    refine h3.congr_deriv ?_
    simp [Complex.real_smul]
  exact h1.add h4

lemma hasDerivAt_polyPart1 (P : P2) {h : ℝ} (_hh : 0 < h) (a : ℂ) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => a + ((h⁻¹ : ℝ) : ℂ) * gP1 P h (τ / h)) (((h⁻¹ : ℝ) : ℂ) ^ 2 * wev (h) (τ / h) P) τ := by
  have h2 : HasDerivAt (fun τ : ℝ => τ / h) h⁻¹ τ := by
    simpa using (hasDerivAt_id τ).div_const h
  have h3 := (hasDerivAt_gP1 P h (τ / h)).scomp τ h2
  have h4 := (h3.const_mul (((h⁻¹ : ℝ) : ℂ))).const_add a
  refine h4.congr_deriv ?_
  simp [Complex.real_smul]; ring

lemma deriv_E0r {P : P2} {h : ℝ} (hh : 0 < h) (hc : 2 ≤ (h ^ 2)⁻¹) (τ : ℝ) :
    deriv (E0r P h) τ = deriv (kernelAmp ((h ^ 2)⁻¹)) τ -
      (deriv (bumpE0 ((h ^ 2)⁻¹)) 0 + ((h⁻¹ : ℝ) : ℂ) * gP1 P h (τ / h)) := by
  have h1 : HasDerivAt (bumpE0 ((h ^ 2)⁻¹)) (deriv (kernelAmp ((h ^ 2)⁻¹)) τ) τ := by
    rw [← deriv_bumpE0]
    exact (((contDiff_bumpE0 hc).differentiable (by norm_num)) τ).hasDerivAt
  exact (h1.sub (hasDerivAt_polyPart P hh _ τ)).deriv

lemma deriv_deriv_E0r {P : P2} {h : ℝ} (hh : 0 < h) (hc : 2 ≤ (h ^ 2)⁻¹) (τ : ℝ) :
    deriv (deriv (E0r P h)) τ = deriv (deriv (kernelAmp ((h ^ 2)⁻¹))) τ -
      ((h⁻¹ : ℝ) : ℂ) ^ 2 * wev h (τ / h) P := by
  have hfun : deriv (E0r P h) = fun τ => deriv (kernelAmp ((h ^ 2)⁻¹)) τ -
      (deriv (bumpE0 ((h ^ 2)⁻¹)) 0 + ((h⁻¹ : ℝ) : ℂ) * gP1 P h (τ / h)) := funext (deriv_E0r hh hc)
  rw [hfun]
  have hk : ContDiff ℝ 2 (kernelAmp ((h ^ 2)⁻¹)) := by
    obtain ⟨Ca, hCa, haenv⟩ := kernel_amp_env2
    exact (haenv _ hc).1
  have h1 : HasDerivAt (deriv (kernelAmp ((h ^ 2)⁻¹))) (deriv (deriv (kernelAmp ((h ^ 2)⁻¹))) τ) τ :=
    (((cd1_of_cd2 hk).differentiable (by norm_num)) τ).hasDerivAt
  exact (h1.sub (hasDerivAt_polyPart1 P hh _ τ)).deriv

lemma contDiff_E0r (P : P2) {h : ℝ} (_hh : 0 < h) (hc : 2 ≤ (h ^ 2)⁻¹) : ContDiff ℝ 2 (E0r P h) := by
  unfold E0r
  refine (contDiff_bumpE0 hc).sub ?_
  refine (contDiff_const.mul Complex.ofRealCLM.contDiff).add ?_
  exact (contDiff_gP0 P h).comp (contDiff_id.div_const h)

lemma E0r_zero (P : P2) (h : ℝ) : E0r P h 0 = 0 := by simp [E0r, bumpE0_zero, gP0_zero]

lemma deriv_E0r_zero {P : P2} {h : ℝ} (hh : 0 < h) (hc : 2 ≤ (h ^ 2)⁻¹) : deriv (E0r P h) 0 = 0 := by
  rw [deriv_E0r hh hc, deriv_bumpE0]
  simp [gP1_zero]

/-- Two integrations from `0` of a pointwise bound on the second derivative (valid while `h(1+|t/h|)³ ≤ 1/2`). -/
lemma region_bounds {ε : ℝ → ℂ} (hε : ContDiff ℝ 2 ε) {h C : ℝ} (hh : 0 < h) (hC : 0 ≤ C)
    (h0 : ε 0 = 0) (h1 : deriv ε 0 = 0)
    (hd2 : ∀ t : ℝ, wx h (t / h) ≤ 1 / 2 → ‖deriv (deriv ε) t‖ ≤ C * h ^ 2 * (1 + |t / h|) ^ 12)
    {τ : ℝ} (hτ : wx h (τ / h) ≤ 1 / 2) :
    ‖ε τ‖ ≤ C * h ^ 4 * (1 + |τ / h|) ^ 14 ∧ ‖deriv ε τ‖ ≤ C * h ^ 3 * (1 + |τ / h|) ^ 13 ∧
      ‖deriv (deriv ε) τ‖ ≤ C * h ^ 2 * (1 + |τ / h|) ^ 12 := by
  set v : ℝ := τ / h with hv
  have hτabs : |τ| = h * |v| := by rw [hv, abs_div, abs_of_pos hh]; field_simp
  set M : ℝ := C * h ^ 2 * (1 + |v|) ^ 12 with hM
  have hM0 : 0 ≤ M := by positivity
  have hseg : ∀ t ∈ Set.uIcc 0 τ, |t| ≤ |τ| := by
    intro t ht
    rcases le_total 0 τ with h0τ | h0τ
    · rw [Set.uIcc_of_le h0τ] at ht
      rw [abs_of_nonneg ht.1, abs_of_nonneg h0τ]; exact ht.2
    · rw [Set.uIcc_of_ge h0τ] at ht
      rw [abs_of_nonpos ht.2, abs_of_nonpos h0τ]; linarith [ht.1]
  have hwx : ∀ t ∈ Set.uIcc 0 τ, wx h (t / h) ≤ 1 / 2 ∧ (1 + |t / h|) ^ 12 ≤ (1 + |v|) ^ 12 := by
    intro t ht
    have h1' : |t / h| ≤ |v| := by
      rw [hv, abs_div, abs_div, abs_of_pos hh]
      exact div_le_div_of_nonneg_right (hseg t ht) hh.le
    refine ⟨?_, pow_le_pow_left₀ (by positivity) (by linarith) 12⟩
    refine le_trans ?_ hτ
    unfold wx
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 3) hh.le
  have hd2M : ∀ t ∈ Set.uIcc 0 τ, ‖deriv (deriv ε) t‖ ≤ M := by
    intro t ht
    obtain ⟨a, b⟩ := hwx t ht
    exact (hd2 t a).trans (by rw [hM]; exact mul_le_mul_of_nonneg_left b (by positivity))
  have hdiff1 : Differentiable ℝ (deriv ε) := ((cd1_of_cd2 hε).differentiable (by norm_num))
  have hdiff0 : Differentiable ℝ ε := hε.differentiable (by norm_num)
  have hconv : Convex ℝ (Set.uIcc (0 : ℝ) τ) := convex_uIcc 0 τ
  have hmem0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) τ := Set.left_mem_uIcc
  have hmemτ : τ ∈ Set.uIcc (0 : ℝ) τ := Set.right_mem_uIcc
  -- first derivative bound
  have hd1 : ∀ t ∈ Set.uIcc 0 τ, ‖deriv ε t‖ ≤ M * |τ| := by
    intro t ht
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv ε) (s := Set.uIcc (0 : ℝ) τ) (C := M)
      (fun x _ => hdiff1 x) hd2M hconv hmem0 ht
    rw [h1, sub_zero, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hseg t ht) hM0)
  have e1 : ‖deriv ε τ‖ ≤ M * |τ| := hd1 τ hmemτ
  have e0 : ‖ε τ‖ ≤ M * |τ| * |τ| := by
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := ε) (s := Set.uIcc (0 : ℝ) τ) (C := M * |τ|)
      (fun x _ => hdiff0 x) hd1 hconv hmem0 hmemτ
    rw [h0, sub_zero, sub_zero] at this
    exact this
  refine ⟨?_, ?_, hd2M τ hmemτ |>.trans (le_of_eq rfl)⟩
  · refine e0.trans ?_
    rw [hτabs, hM]
    have hv1 : |v| ≤ 1 + |v| := by linarith
    have : (h * |v|) * (h * |v|) ≤ h ^ 2 * (1 + |v|) ^ 2 := by
      have := mul_le_mul hv1 hv1 (abs_nonneg v) (by positivity)
      nlinarith [sq_nonneg h, mul_pos hh hh]
    calc C * h ^ 2 * (1 + |v|) ^ 12 * (h * |v|) * (h * |v|)
        = C * h ^ 2 * (1 + |v|) ^ 12 * ((h * |v|) * (h * |v|)) := by ring
      _ ≤ C * h ^ 2 * (1 + |v|) ^ 12 * (h ^ 2 * (1 + |v|) ^ 2) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = C * h ^ 4 * (1 + |v|) ^ 14 := by ring
  · refine e1.trans ?_
    rw [hτabs, hM]
    have hv1 : |v| ≤ 1 + |v| := by linarith
    calc C * h ^ 2 * (1 + |v|) ^ 12 * (h * |v|) ≤ C * h ^ 2 * (1 + |v|) ^ 12 * (h * (1 + |v|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv1 hh.le) (by positivity)
      _ = C * h ^ 3 * (1 + |v|) ^ 13 := by ring

/-! ### Crude bounds outside the region -/

lemma norm_div_nat_le (z : ℂ) {n : ℕ} (hn : 1 ≤ n) : ‖z / (n : ℂ)‖ ≤ ‖z‖ := by
  rw [norm_div, Complex.norm_natCast]
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_le_self (norm_nonneg _) this

lemma norm_hpow_le {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) (n : ℕ) : ‖(h : ℂ) ^ n‖ ≤ 1 := by
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg h0.le]
  exact pow_le_one₀ h0.le h1

lemma norm_vpow_le (v : ℝ) (n m : ℕ) (hnm : n ≤ m) : ‖(v : ℂ) ^ n‖ ≤ (1 + |v|) ^ m := by
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc |v| ^ n ≤ (1 + |v|) ^ n := pow_le_pow_left₀ (abs_nonneg v) (by linarith) n
    _ ≤ (1 + |v|) ^ m := pow_le_pow_right₀ (by linarith [abs_nonneg v]) hnm

lemma norm_gP0_le (P : P2) {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) (v : ℝ) :
    ‖gP0 P h v‖ ≤ cnorm P * (1 + |v|) ^ (P.support.sup (fun d => d 1) + 2) := by
  unfold gP0 cnorm
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  have hD : d 1 ≤ P.support.sup (fun d => d 1) := Finset.le_sup (f := fun d => d 1) hd
  refine (norm_div_nat_le _ (by omega)).trans ?_
  rw [norm_mul]
  have hv := norm_vpow_le v (d 1 + 2) (P.support.sup (fun d => d 1) + 2) (by omega)
  have h3 := norm_hpow_le h0 h1 (d 0)
  have hpos : 0 ≤ (1 + |v|) ^ (P.support.sup (fun d => d 1) + 2) := by positivity
  calc ‖(P.coeff d * (h : ℂ) ^ (d 0)) / (((d 1 + 1 : ℕ)) : ℂ)‖ * ‖(v : ℂ) ^ (d 1 + 2)‖
      ≤ ‖P.coeff d * (h : ℂ) ^ (d 0)‖ * (1 + |v|) ^ (P.support.sup (fun d => d 1) + 2) :=
        mul_le_mul (norm_div_nat_le _ (by omega)) hv (norm_nonneg _) (norm_nonneg _)
    _ ≤ ‖P.coeff d‖ * 1 * (1 + |v|) ^ (P.support.sup (fun d => d 1) + 2) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) hpos
    _ = _ := by ring

lemma norm_gP1_le (P : P2) {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) (v : ℝ) :
    ‖gP1 P h v‖ ≤ cnorm P * (1 + |v|) ^ (P.support.sup (fun d => d 1) + 1) := by
  unfold gP1 cnorm
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  have hD : d 1 ≤ P.support.sup (fun d => d 1) := Finset.le_sup (f := fun d => d 1) hd
  refine (norm_div_nat_le _ (by omega)).trans ?_
  rw [norm_mul, norm_mul]
  have := norm_hpow_le h0 h1 (d 0)
  have hv := norm_vpow_le v (d 1 + 1) (P.support.sup (fun d => d 1) + 1) (by omega)
  have hp : 0 ≤ (1 + |v|) ^ (P.support.sup (fun d => d 1) + 1) := by positivity
  calc ‖P.coeff d‖ * ‖(h : ℂ) ^ (d 0)‖ * ‖(v : ℂ) ^ (d 1 + 1)‖
      ≤ ‖P.coeff d‖ * 1 * (1 + |v|) ^ (P.support.sup (fun d => d 1) + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left this (norm_nonneg _)) hv (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma norm_wev_le_crude (P : P2) {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) (v : ℝ) :
    ‖wev h v P‖ ≤ cnorm P * (1 + |v|) ^ (P.support.sup (fun d => d 1)) := by
  rw [wev_eq]
  unfold cnorm
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  have hD : d 1 ≤ P.support.sup (fun d => d 1) := Finset.le_sup (f := fun d => d 1) hd
  rw [norm_mul, norm_mul]
  have := norm_hpow_le h0 h1 (d 0)
  have hv := norm_vpow_le v (d 1) (P.support.sup (fun d => d 1)) hD
  calc ‖P.coeff d‖ * (‖(h : ℂ) ^ (d 0)‖ * ‖(v : ℂ) ^ (d 1)‖)
      ≤ ‖P.coeff d‖ * (1 * (1 + |v|) ^ (P.support.sup (fun d => d 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul this hv (norm_nonneg _) (by norm_num)) (norm_nonneg _)
    _ = _ := by ring

lemma E0r_crude (P : P2) : ∃ (A : ℝ) (q : ℕ), 0 ≤ A ∧ ∀ h : ℝ, 0 < h → h ≤ 1 / 4 → ∀ τ : ℝ,
    ‖E0r P h τ‖ ≤ A * (h ^ 4)⁻¹ * (1 + |τ / h|) ^ q ∧ ‖deriv (E0r P h) τ‖ ≤ A * (h ^ 4)⁻¹ * (1 + |τ / h|) ^ q ∧
      ‖deriv (deriv (E0r P h)) τ‖ ≤ A * (h ^ 4)⁻¹ * (1 + |τ / h|) ^ q := by
  obtain ⟨Ca, hCa, haenv⟩ := kernel_amp_env2
  have hN0 := cnorm_nonneg P
  refine ⟨8 * Ca + 1 + cnorm P, P.support.sup (fun d => d 1) + 4, by positivity, fun h hh hh4 τ => ?_⟩
  set D0 := P.support.sup (fun d => d 1) with hD0
  have hh1 : h ≤ 1 := by linarith
  have hc : 2 ≤ (h ^ 2)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (by positivity)]; nlinarith
  set c : ℝ := (h ^ 2)⁻¹ with hcdef
  have hEnv := haenv c hc
  set v : ℝ := τ / h with hv
  have hτv : |τ| ≤ |v| := by
    rw [hv, abs_div, abs_of_pos hh, le_div_iff₀ hh]
    nlinarith [abs_nonneg τ]
  set H : ℝ := (h ^ 4)⁻¹ with hH
  have hH1 : 1 ≤ H := by
    rw [hH, one_le_inv₀ (by positivity)]; exact pow_le_one₀ hh.le hh1
  set X : ℝ := 1 + |v| with hX
  have hX1 : 1 ≤ X := by linarith [abs_nonneg v]
  have hc2 : (1 + c) ^ 2 ≤ 4 * H := by
    have h1 : 1 ≤ c := by linarith
    have : c ^ 2 = H := by rw [hcdef, hH]; field_simp
    nlinarith
  have hbK : ∀ t : ℝ, ‖kernelAmp c t‖ ≤ Ca * (1 + c) ^ 2 * (1 + |t|) ^ 4 ∧
      ‖deriv (kernelAmp c) t‖ ≤ Ca * (1 + c) ^ 2 * (1 + |t|) ^ 4 ∧
      ‖deriv (deriv (kernelAmp c)) t‖ ≤ Ca * (1 + c) ^ 2 * (1 + |t|) ^ 4 := fun t => hEnv.2 t
  have hY : ∀ t : ℝ, |t| ≤ |v| → Ca * (1 + c) ^ 2 * (1 + |t|) ^ 4 ≤ 4 * Ca * H * X ^ 4 := by
    intro t ht
    have h1 : (1 + |t|) ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ (by positivity) (by rw [hX]; linarith) 4
    calc Ca * (1 + c) ^ 2 * (1 + |t|) ^ 4 ≤ Ca * (4 * H) * X ^ 4 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hc2 hCa) h1 (by positivity) (by positivity)
      _ = 4 * Ca * H * X ^ 4 := by ring
  have hXq : X ^ 4 ≤ X ^ (D0 + 4) := pow_le_pow_right₀ hX1 (by omega)
  have hXq1 : ∀ k : ℕ, k ≤ D0 + 4 → X ^ k ≤ X ^ (D0 + 4) := fun k hk => pow_le_pow_right₀ hX1 hk
  set Y : ℝ := H * X ^ (D0 + 4) with hYdef
  have hY1 : 1 ≤ Y := by
    have : 1 ≤ X ^ (D0 + 4) := one_le_pow₀ hX1
    nlinarith
  have hHY : ∀ k : ℕ, k ≤ D0 + 4 → H * X ^ k ≤ Y := fun k hk =>
    mul_le_mul_of_nonneg_left (hXq1 k hk) (by positivity)
  have hHinv : ∀ m : ℕ, m ≤ 4 → (h ^ m)⁻¹ ≤ H := by
    intro m hm
    rw [hH]
    exact inv_anti₀ (by positivity) (pow_le_pow_of_le_one hh.le hh1 hm)
  have hKY : ‖deriv (bumpE0 c) 0‖ ≤ 4 * Ca * H := by
    rw [deriv_bumpE0]
    refine (hbK 0).2.1.trans ?_
    simp only [abs_zero, add_zero, one_pow, mul_one]
    nlinarith [mul_le_mul_of_nonneg_left hc2 hCa]
  have hKtY : ∀ t : ℝ, |t| ≤ |v| → ‖kernelAmp c t‖ ≤ 4 * Ca * Y ∧ ‖deriv (kernelAmp c) t‖ ≤ 4 * Ca * Y ∧
      ‖deriv (deriv (kernelAmp c)) t‖ ≤ 4 * Ca * Y := by
    intro t ht
    obtain ⟨a, b, d⟩ := hbK t
    have := (hY t ht).trans (by
      have : 4 * Ca * H * X ^ 4 ≤ 4 * Ca * (H * X ^ (D0 + 4)) := by
        have := mul_le_mul_of_nonneg_left hXq (by positivity : 0 ≤ 4 * Ca * H)
        linarith
      exact this)
    exact ⟨a.trans this, b.trans this, d.trans this⟩
  have hG0 := norm_gP0_le P hh hh1 v
  have hG1 := norm_gP1_le P hh hh1 v
  have hW := norm_wev_le_crude P hh hh1 v
  have hG0Y : ‖gP0 P h v‖ ≤ cnorm P * Y := by
    refine hG0.trans (mul_le_mul_of_nonneg_left ?_ hN0)
    calc (1 + |v|) ^ (D0 + 2) ≤ X ^ (D0 + 4) := hXq1 _ (by omega)
      _ ≤ H * X ^ (D0 + 4) := le_mul_of_one_le_left (by positivity) hH1
  have hG1Y : ‖((h⁻¹ : ℝ) : ℂ) * gP1 P h v‖ ≤ cnorm P * Y := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc h⁻¹ * ‖gP1 P h v‖ ≤ H * (cnorm P * X ^ (D0 + 1)) := by
          refine mul_le_mul ?_ (hG1.trans (le_of_eq rfl)) (norm_nonneg _) (by positivity)
          have := hHinv 1 (by norm_num); simpa using this
      _ = cnorm P * (H * X ^ (D0 + 1)) := by ring
      _ ≤ cnorm P * Y := mul_le_mul_of_nonneg_left (hHY _ (by omega)) hN0
  have hWY : ‖((h⁻¹ : ℝ) : ℂ) ^ 2 * wev h v P‖ ≤ cnorm P * Y := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc (h⁻¹) ^ 2 * ‖wev h v P‖ ≤ H * (cnorm P * X ^ D0) := by
          refine mul_le_mul ?_ hW (norm_nonneg _) (by positivity)
          have := hHinv 2 (by norm_num); simpa [inv_pow] using this
      _ = cnorm P * (H * X ^ D0) := by ring
      _ ≤ cnorm P * Y := mul_le_mul_of_nonneg_left (hHY _ (by omega)) hN0
  have hτ0 := hKtY τ hτv
  have hHleY : H ≤ Y := by
    have : 1 ≤ X ^ (D0 + 4) := one_le_pow₀ hX1
    exact le_mul_of_one_le_right (by positivity) this
  have hKY' : ‖deriv (bumpE0 c) 0‖ ≤ 4 * Ca * Y :=
    hKY.trans (mul_le_mul_of_nonneg_left hHleY (by positivity))
  have hAY : (8 * Ca + 1 + cnorm P) * (h ^ 4)⁻¹ * (1 + |τ / h|) ^ (D0 + 4) = (8 * Ca + 1 + cnorm P) * Y := by
    rw [hYdef, hH, hX, hv]; ring
  refine ⟨?_, ?_, ?_⟩
  · -- ε
    unfold E0r
    have e1 : ‖bumpE0 c τ‖ ≤ 4 * Ca * Y + 1 := by
      unfold bumpE0
      exact (norm_sub_le _ _).trans (by simp; linarith [hτ0.1])
    have e2 : ‖deriv (bumpE0 c) 0 * (τ : ℂ)‖ ≤ 4 * Ca * Y := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖deriv (bumpE0 c) 0‖ * |τ| ≤ (4 * Ca * H) * X := by
            refine mul_le_mul hKY ?_ (abs_nonneg _) (by positivity)
            rw [hX]; linarith
        _ ≤ 4 * Ca * Y := by
            have : H * X ≤ Y := hHY 1 (by omega) |> fun h => by simpa using h
            nlinarith [mul_le_mul_of_nonneg_left this hCa]
    have e3 := hG0Y
    have : ‖bumpE0 c τ - (deriv (bumpE0 c) 0 * (τ : ℂ) + gP0 P h (τ / h))‖ ≤
        ‖bumpE0 c τ‖ + (‖deriv (bumpE0 c) 0 * (τ : ℂ)‖ + ‖gP0 P h v‖) :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _) |>.trans (le_of_eq rfl)
    refine this.trans ?_
    rw [hAY]
    linarith
  · rw [deriv_E0r hh hc]
    have : ‖deriv (kernelAmp c) τ - (deriv (bumpE0 c) 0 + ((h⁻¹ : ℝ) : ℂ) * gP1 P h v)‖ ≤
        ‖deriv (kernelAmp c) τ‖ + (‖deriv (bumpE0 c) 0‖ + ‖((h⁻¹ : ℝ) : ℂ) * gP1 P h v‖) :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    refine this.trans ?_
    rw [hAY]
    nlinarith [hτ0.2.1, hKY', hG1Y]
  · rw [deriv_deriv_E0r hh hc]
    have : ‖deriv (deriv (kernelAmp c)) τ - ((h⁻¹ : ℝ) : ℂ) ^ 2 * wev h v P‖ ≤
        ‖deriv (deriv (kernelAmp c)) τ‖ + ‖((h⁻¹ : ℝ) : ℂ) ^ 2 * wev h v P‖ := norm_sub_le _ _
    refine this.trans ?_
    rw [hAY]
    nlinarith [hτ0.2.2, hWY]

lemma outside_amplify {A h X : ℝ} {q : ℕ} (m : ℕ) (hA : 0 ≤ A) (hh : 0 < h) (hX : 1 ≤ X)
    (hx : 1 ≤ 2 * (h * X ^ 3)) {y : ℝ} (hy : y ≤ A * (h ^ 4)⁻¹ * X ^ q) :
    y ≤ 2 ^ m * A * (h ^ m * (h ^ 4)⁻¹) * X ^ (q + 3 * m) := by
  have h1 : 1 ≤ (2 * (h * X ^ 3)) ^ m := one_le_pow₀ hx
  have hX0 : 0 < X := by linarith
  calc y ≤ A * (h ^ 4)⁻¹ * X ^ q := hy
    _ ≤ A * (h ^ 4)⁻¹ * X ^ q * (2 * (h * X ^ 3)) ^ m := le_mul_of_one_le_right (by positivity) h1
    _ = 2 ^ m * A * (h ^ m * (h ^ 4)⁻¹) * X ^ (q + 3 * m) := by
        rw [mul_pow, mul_pow, ← pow_mul]; ring

/-- **The `C²` remainder of `E₀`.**  For `0 < h ≤ 1/4` (`c = h⁻²`, `v = τ/h`) the function `E0r P h = E₀ - (E₀'(0) τ + G_h(τ/h))` is `C²` and
`|ε| ≤ C h⁴ (1+|v|)^p`, `|ε'| ≤ C h³ (1+|v|)^p`, `|ε''| ≤ C h² (1+|v|)^p`; `E₀'(0) τ + G_h(τ/h)` is a polynomial in `τ`. -/
theorem E0_poly_remainder :
    ∃ (P : P2) (C : ℝ) (p : ℕ), WPolyW P ∧ MvPolynomial.constantCoeff P = 0 ∧ 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 / 4 →
      ContDiff ℝ 2 (E0r P h) ∧ ∀ τ : ℝ,
        ‖E0r P h τ‖ ≤ C * h ^ 4 * (1 + |τ / h|) ^ p ∧
        ‖deriv (E0r P h) τ‖ ≤ C * h ^ 3 * (1 + |τ / h|) ^ p ∧
        ‖deriv (deriv (E0r P h)) τ‖ ≤ C * h ^ 2 * (1 + |τ / h|) ^ p := by
  obtain ⟨P, C, hP, hc0, hC, hb⟩ := K2_wexpW
  obtain ⟨A, q, hA, hcr⟩ := E0r_crude P
  refine ⟨P, max C (256 * A), q + 24, hP, hc0, le_max_of_le_left hC, fun h hh hh4 => ?_⟩
  have hc : 2 ≤ (h ^ 2)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (by positivity)]; nlinarith
  refine ⟨contDiff_E0r P hh hc, fun τ => ?_⟩
  set X : ℝ := 1 + |τ / h| with hX
  have hX1 : 1 ≤ X := by linarith [abs_nonneg (τ / h)]
  have hCm : C ≤ max C (256 * A) := le_max_left _ _
  have hAm : 256 * A ≤ max C (256 * A) := le_max_right _ _
  have hXp : ∀ k : ℕ, k ≤ q + 24 → X ^ k ≤ X ^ (q + 24) := fun k hk => pow_le_pow_right₀ hX1 hk
  by_cases hreg : wx h (τ / h) ≤ 1 / 2
  · have hd2 : ∀ t : ℝ, wx h (t / h) ≤ 1 / 2 →
        ‖deriv (deriv (E0r P h)) t‖ ≤ C * h ^ 2 * (1 + |t / h|) ^ 12 := by
      intro t ht
      have hr : WReg (1 / 2) h (t / h) := ⟨hh, ht⟩
      have key : deriv (deriv (E0r P h)) t = ((h⁻¹ : ℝ) : ℂ) ^ 2 * (K2 h (t / h) - wev h (t / h) P) := by
        rw [deriv_deriv_E0r hh hc]
        unfold K2
        rw [show h * (t / h) = t by field_simp]
        have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
        push_cast
        field_simp
      rw [key, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have := hb h (t / h) hr
      calc h⁻¹ ^ 2 * ‖K2 h (t / h) - wev h (t / h) P‖ ≤ h⁻¹ ^ 2 * (C * wx h (t / h) ^ 4) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = C * h ^ 2 * (1 + |t / h|) ^ 12 := by
            unfold wx
            field_simp
    obtain ⟨b0, b1, b2⟩ := region_bounds (contDiff_E0r P hh hc) hh hC (E0r_zero P h) (deriv_E0r_zero hh hc) hd2 hreg
    have hX4 : 0 ≤ X := by linarith
    refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
    · exact mul_le_mul (mul_le_mul_of_nonneg_right hCm (by positivity)) (hXp 14 (by omega)) (by positivity) (by positivity)
    · exact mul_le_mul (mul_le_mul_of_nonneg_right hCm (by positivity)) (hXp 13 (by omega)) (by positivity) (by positivity)
    · exact mul_le_mul (mul_le_mul_of_nonneg_right hCm (by positivity)) (hXp 12 (by omega)) (by positivity) (by positivity)
  · obtain ⟨c0, c1, c2⟩ := hcr h hh hh4 τ
    have hx : 1 ≤ 2 * (h * X ^ 3) := by
      have : 1 / 2 < wx h (τ / h) := not_le.mp hreg
      unfold wx at this
      linarith
    have hm : ∀ m : ℕ, 2 ^ m * A * (h ^ m * (h ^ 4)⁻¹) = 2 ^ m * A * h ^ m * (h ^ 4)⁻¹ := fun m => by ring
    have e8 : h ^ 8 * (h ^ 4)⁻¹ = h ^ 4 := by
      rw [← div_eq_mul_inv, div_eq_iff (by positivity)]; ring
    have e7 : h ^ 7 * (h ^ 4)⁻¹ = h ^ 3 := by
      rw [← div_eq_mul_inv, div_eq_iff (by positivity)]; ring
    have e6 : h ^ 6 * (h ^ 4)⁻¹ = h ^ 2 := by
      rw [← div_eq_mul_inv, div_eq_iff (by positivity)]; ring
    have fin : ∀ (a : ℝ) (k e : ℕ), a ≤ max C (256 * A) → 0 ≤ a → e ≤ q + 24 →
        a * h ^ k * X ^ e ≤ max C (256 * A) * h ^ k * X ^ (q + 24) := fun a k e ha ha0 he =>
      mul_le_mul (mul_le_mul_of_nonneg_right ha (by positivity)) (hXp e he) (by positivity) (by positivity)
    refine ⟨(outside_amplify 8 hA hh hX1 hx c0).trans ?_, (outside_amplify 7 hA hh hX1 hx c1).trans ?_,
      (outside_amplify 6 hA hh hX1 hx c2).trans ?_⟩
    · rw [e8]
      exact fin _ 4 _ (by linarith [hAm, hA]) (by positivity) (by omega)
    · rw [e7]
      exact fin _ 3 _ (by linarith [hAm, hA]) (by positivity) (by omega)
    · rw [e6]
      exact fin _ 2 _ (by linarith [hAm, hA]) (by positivity) (by omega)

/-- info: 'FormalResearch.SignUncertainty.E0_poly_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms E0_poly_remainder

end FormalResearch.SignUncertainty
