/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerConcreteSetup
public import FormalResearch.SignUncertainty.CtLowerChartGap

/-!
# Lemma FJ (`fj:lemma`) smooth fold bound in `z = τ²`

Paper I (`constant_terms_five.tex`, `fct:warp-asymp` (1); `CFT/common/fine_order_fold.tex`, `fj:lemma`):
proves the uniform quadratic fold cancellation `fj_fold_taylor`:
for `L = z₀ n(z₀)` with `0 < z₀ ≤ δz`, `0 ≤ s ≤ s₀`, and `s ≤ K_z z₀`, there is a unique
`z_s ∈ [z₀/4, 4 z₀]` solving `fjFcrit nfun (concreteThetaT ε) s z_s = L - s θ₁^ε`, and
`fjAfold fF (concreteThetaT ε) s z_s = z₀ d(z₀)² + s (-θ_ε(√z₀)/(√z₀ d(z₀))) + O(s²)`
with `C_fj` independent of `z₀, L, s`.

Class: proved, unconditional.
-/

@[expose] public section

open Set Filter Topology Metric MeasureTheory
open scoped Real ContDiff
open FormalResearch.CohnElkies
open FormalResearch.Special
open FormalResearch.SignUncertainty.CtCfu
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment

namespace FormalResearch.SignUncertainty

/-! ### 1. Smooth FJ(1) fold in `z = τ²` -/

section FoldFJ

noncomputable def fjH1 (θt : ℝ → ℝ) (z : ℝ) : ℝ :=
  3 * θt z + 2 * z * deriv θt z

noncomputable def fjFcrit (nfun θt : ℝ → ℝ) (s z : ℝ) : ℝ :=
  z * (nfun z + s * fjH1 θt z)

noncomputable def fjQ (fF θt : ℝ → ℝ) (s z : ℝ) : ℝ :=
  fF z + s * (2 * θt z + 2 * z * deriv θt z)

noncomputable def fjAfold (fF θt : ℝ → ℝ) (s z : ℝ) : ℝ :=
  z * ((3 / 2 : ℝ) * fjQ fF θt s z) ^ (2 / 3 : ℝ)

private lemma hasDerivAt_mul_cube {g : ℝ → ℝ} {g' τ : ℝ} (hg : HasDerivAt g g' τ) :
    HasDerivAt (fun t => t ^ 3 * g t) (3 * τ ^ 2 * g τ + τ ^ 3 * g') τ := by
  exact ((hasDerivAt_pow 3 τ).fun_mul hg).congr_deriv (by ring)

lemma outerTheta_deriv_sq {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ Mθ : ℝ, 0 ≤ Mθ ∧ JC 18 (Ioo (-1 : ℝ) 6) (concreteThetaT ε) Mθ ∧
      ∀ τ : ℝ, |τ| ≤ 2 →
        HasDerivAt (outerTheta ε) (ctTheta1 ε + τ ^ 2 * fjH1 (concreteThetaT ε) (τ ^ 2)) τ := by
  obtain ⟨hspec, Mθ, hMθ0, hMθ⟩ := concreteThetaT_spec hε
  refine ⟨Mθ, hMθ0, hMθ, fun τ hτ => ?_⟩
  have hz : τ ^ 2 ∈ Ioo (-1 : ℝ) 6 := ⟨by nlinarith [sq_nonneg τ], by
    have : τ ^ 2 ≤ 4 := by nlinarith [abs_le.mp hτ]
    linarith only [this]⟩
  have hθcd : ContDiffOn ℝ 18 (concreteThetaT ε) (Ioo (-1 : ℝ) 6) := hMθ.1
  have hd_t : HasDerivAt (concreteThetaT ε) (deriv (concreteThetaT ε) (τ ^ 2)) (τ ^ 2) :=
    ((hθcd.contDiffAt (isOpen_Ioo.mem_nhds hz)).differentiableAt (by norm_num)).hasDerivAt
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * τ) τ := by simpa using hasDerivAt_pow 2 τ
  have hc : HasDerivAt (fun t : ℝ => concreteThetaT ε (t ^ 2)) (deriv (concreteThetaT ε) (τ ^ 2) * (2 * τ)) τ :=
    HasDerivAt.comp τ hd_t hsq
  have htot := ((hasDerivAt_id τ).const_mul (ctTheta1 ε)).add (hasDerivAt_mul_cube hc)
  have hfn : outerTheta ε = fun t : ℝ => ctTheta1 ε * t + t ^ 3 * concreteThetaT ε (t ^ 2) :=
    funext hspec
  rw [hfn]
  refine htot.congr_deriv ?_
  unfold fjH1
  ring

private lemma deriv_z_mul_fn {f : ℝ → ℝ} {z : ℝ} (hf : DifferentiableAt ℝ f z) :
    HasDerivAt (fun w : ℝ => w * f w) (f z + z * deriv f z) z :=
  ((hasDerivAt_id' z).fun_mul hf.hasDerivAt).congr_deriv (by ring)

private lemma mvt_lip_on_Icc {f : ℝ → ℝ} {l u M : ℝ} (_hM : 0 ≤ M)
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀ w ∈ Icc l u, HasDerivAt f (deriv f w) w)
    (hbd : ∀ w ∈ Icc l u, |deriv f w| ≤ M)
    {x y : ℝ} (hx : x ∈ Icc l u) (hy : y ∈ Icc l u) :
    |f x - f y| ≤ M * |x - y| := by
  wlog hle : x ≤ y generalizing x y
  · rw [abs_sub_comm (f x), abs_sub_comm x]; exact this hy hx (le_of_not_ge hle)
  rcases hle.eq_or_lt with rfl | hlt
  · simp
  · have hsub : Icc x y ⊆ Icc l u := Icc_subset_Icc hx.1 hy.2
    obtain ⟨c, hcm, hce⟩ := exists_hasDerivAt_eq_slope f (deriv f) hlt (hc.mono hsub)
      fun w hw => hd w (hsub (Ioo_subset_Icc_self hw))
    have hpos : 0 < y - x := sub_pos.mpr hlt
    have hfe : f y - f x = deriv f c * (y - x) := by rw [hce, div_mul_cancel₀ _ hpos.ne']
    rw [abs_sub_comm (f x) (f y), abs_sub_comm x y, hfe, abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_right (hbd c (hsub (Ioo_subset_Icc_self hcm))) hpos.le

private lemma hasDerivAt_comp_sq {g : ℝ → ℝ} {g' x : ℝ} (hg : HasDerivAt g g' (x ^ 2)) :
    HasDerivAt (fun u : ℝ => g (u ^ 2)) (g' * (2 * x)) x := by
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  exact HasDerivAt.comp x (show HasDerivAt g g' ((fun u : ℝ => u ^ 2) x) from hg) hsq

private lemma hasDerivAt_comp_snd {g : ℝ → ℝ} {g' a b : ℝ} (hg : HasDerivAt g g' b) :
    HasFDerivAt (fun p : ℝ × ℝ => g p.2) (g' • ContinuousLinearMap.snd ℝ ℝ ℝ) (a, b) :=
  hg.comp_hasFDerivAt (a, b) hasFDerivAt_snd

private lemma three_ntil_add_two_z_deriv_ntil {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) rr) :
    3 * ntil z + 2 * z * deriv ntil z = nfun z := by
  set τ : ℝ := Real.sqrt z with hτ_def
  have hτ_pos : 0 < τ := Real.sqrt_pos.mpr hz.1
  have hτ_sq : τ ^ 2 = z := Real.sq_sqrt hz.1.le
  have hτ_lt : τ < Real.sqrt rr := Real.sqrt_lt_sqrt hz.1.le hz.2
  have hIoo_sub : ∀ u ∈ Ioo (0 : ℝ) (Real.sqrt rr), u ^ 2 < rr := fun u hu => by
    have hlt : u < Real.sqrt rr := hu.2
    have hsq : Real.sqrt rr ^ 2 = rr := Real.sq_sqrt rr_pos.le
    nlinarith [hu.1]
  have h1 : HasDerivAt (fun u : ℝ => ∫ v in (0 : ℝ)..u, hankelEdgeM v) (hankelEdgeM τ) τ := by
    have hint : IntervalIntegrable hankelEdgeM volume 0 τ :=
      (hankelEdgeM_continuousOn.mono fun x hx => by
        rw [Set.uIcc_of_le hτ_pos.le] at hx; exact hx.1).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter hankelEdgeM (𝓝 τ) :=
      (hankelEdgeM_continuousOn.mono Set.Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi τ hτ_pos
    exact intervalIntegral.integral_hasDerivAt_right hint hmeas (hankelEdgeM_hasDerivAt hτ_pos).continuousAt
  have hntil_cd : DifferentiableAt ℝ ntil z :=
    (contDiffOn_ntil.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith [hz.1, rr_pos], hz.2⟩)).differentiableAt (by simp)
  have h2 : HasDerivAt (fun u : ℝ => u ^ 3 * ntil (u ^ 2))
      (3 * τ ^ 2 * ntil z + τ ^ 3 * (deriv ntil z * (2 * τ))) τ := by
    have hnt_at : HasDerivAt ntil (deriv ntil (τ ^ 2)) (τ ^ 2) := by
      rw [hτ_sq]; exact hntil_cd.hasDerivAt
    have hc : HasDerivAt (fun u : ℝ => ntil (u ^ 2)) (deriv ntil z * (2 * τ)) τ := by
      simpa [hτ_sq] using hasDerivAt_comp_sq hnt_at
    exact ((hasDerivAt_pow 3 τ).fun_mul hc).congr_deriv (by rw [hτ_sq]; push_cast; ring)
  have heq : (fun u : ℝ => u ^ 3 * ntil (u ^ 2)) =ᶠ[𝓝 τ] fun u => ∫ v in (0 : ℝ)..u, hankelEdgeM v := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hτ_pos, hτ_lt⟩] with u hu
    exact (integral_hankelEdgeM_eq hu.1.le (hIoo_sub u hu)).symm
  have hderiv_eq := h1.unique (h2.congr_of_eventuallyEq heq.symm)
  rw [hankelEdgeM_eq hτ_pos.le (hτ_sq ▸ hz.2), hτ_sq] at hderiv_eq
  have hfac : z * nfun z = z * (3 * ntil z + 2 * z * deriv ntil z) := by
    rw [hderiv_eq]
    have hτ4 : τ ^ 3 * (deriv ntil z * (2 * τ)) = 2 * z ^ 2 * deriv ntil z := by
      calc τ ^ 3 * (deriv ntil z * (2 * τ)) = 2 * (τ ^ 2) ^ 2 * deriv ntil z := by ring
        _ = 2 * z ^ 2 * deriv ntil z := by rw [hτ_sq]
    rw [hτ4]; ring
  exact (mul_left_cancel₀ hz.1.ne' hfac).symm

private lemma three_halves_fF_add_z_deriv_fF {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) rr) :
    (3 / 2 : ℝ) * fF z + z * deriv fF z = nfun z + z * deriv nfun z := by
  have hIoo : z ∈ Ioo (-rr) rr := ⟨by linarith [hz.1, rr_pos], hz.2⟩
  have hnd : DifferentiableAt ℝ nfun z := (contDiffOn_nfun.contDiffAt (isOpen_Ioo.mem_nhds hIoo)).differentiableAt (by simp)
  have hntd : DifferentiableAt ℝ ntil z := (contDiffOn_ntil.contDiffAt (isOpen_Ioo.mem_nhds hIoo)).differentiableAt (by simp)
  have hdf : deriv fF z = deriv nfun z - deriv ntil z := by
    change deriv (fun w => nfun w - ntil w) z = _
    exact (hnd.hasDerivAt.sub hntd.hasDerivAt).deriv
  have hode := three_ntil_add_two_z_deriv_ntil hz
  rw [hdf]
  change (3 / 2 : ℝ) * (nfun z - ntil z) + z * (deriv nfun z - deriv ntil z) = nfun z + z * deriv nfun z
  linarith [hode]

set_option maxHeartbeats 800000 in
/-- **FJ(1) quantitative fold bound** (`fj:lemma` for `Φ_Ph(τ; L) - s θ_ε(τ)`):
for any `ε = ±1`, there exist `δz > 0`, `s₀ > 0`, `C_fj ≥ 0`, `K_z ≥ 0` (independent of `L`) such that
for any `z₀ ∈ (0, δz]` (`L := z₀ n(z₀)`) and any `s ∈ [0, s₀]` with `s ≤ K_z z₀`:
1. there is a unique `z_s ∈ [z₀/4, 4 z₀]` solving `z_s (n(z_s) + s H₁(z_s)) = L - s θ₁^ε`;
2. `|fjAfold fF θt s z_s - (z₀ dF(z₀)² + s (-θ_ε(√z₀)/(√z₀ dF(z₀))))| ≤ C_fj * s²`. -/
theorem fj_fold_taylor {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ δz s₀ C_fj K_z : ℝ, 0 < δz ∧ δz ≤ min (rr / 4) (1 / 16) ∧ 0 < s₀ ∧ 0 ≤ C_fj ∧ 0 < K_z ∧
      ∀ {z₀ s : ℝ}, 0 < z₀ → z₀ ≤ δz → 0 ≤ s → s ≤ s₀ → s ≤ K_z * z₀ →
        let L := z₀ * nfun z₀
        let θt := concreteThetaT ε
        ∃ z_s ∈ Icc (z₀ / 4) (4 * z₀),
          fjFcrit nfun θt s z_s = L - s * ctTheta1 ε ∧
          (∀ z' ∈ Icc (z₀ / 4) (4 * z₀), fjFcrit nfun θt s z' = L - s * ctTheta1 ε → z' = z_s) ∧
          |fjAfold fF θt s z_s - (z₀ * dF z₀ ^ 2 + s * (-(outerTheta ε (Real.sqrt z₀) / (Real.sqrt z₀ * dF z₀))))| ≤
            C_fj * s ^ 2 := by
  obtain ⟨hspecθ, Mθ, hMθ0, hθjc⟩ := concreteThetaT_spec hε
  set θt := concreteThetaT ε
  have hθcd : ContDiffOn ℝ 18 θt (Ioo (-1 : ℝ) 6) := hθjc.1
  have hn_cd : ContDiffOn ℝ (⊤ : ℕ∞) nfun (Ioo (-rr) rr) := contDiffOn_nfun
  have hf_cd : ContDiffOn ℝ (⊤ : ℕ∞) fF (Ioo (-rr) rr) := contDiffOn_fF
  set r₀ : ℝ := min (rr / 2) (1 / 4 : ℝ)
  have hr₀_pos : 0 < r₀ := lt_min (by linarith [rr_pos]) (by norm_num)
  have hr₀_rr : r₀ < rr := (min_le_left _ _).trans_lt (by linarith [rr_pos])
  have hK_Ioo : Icc (-r₀) r₀ ⊆ Ioo (-rr) rr := fun z hz => ⟨by linarith [hz.1, hr₀_rr], by linarith [hz.2, hr₀_rr]⟩
  have hK_Yint : Icc (-r₀) r₀ ⊆ Ioo (-1 : ℝ) 6 := fun z hz =>
    ⟨by have := (min_le_right (rr / 2) (1 / 4 : ℝ)); linarith [hz.1],
     by have := (min_le_right (rr / 2) (1 / 4 : ℝ)); linarith [hz.2]⟩
  have hKc : IsCompact (Icc (-r₀) r₀) := isCompact_Icc
  have hn_d1 : ContDiffOn ℝ (⊤ : ℕ∞) (deriv nfun) (Ioo (-rr) rr) := contDiffOn_deriv_nfun
  have hf_d1 : ContDiffOn ℝ (⊤ : ℕ∞) (deriv fF) (Ioo (-rr) rr) := contDiffOn_deriv_fF
  have hθ_d1 : ContDiffOn ℝ 17 (deriv θt) (Ioo (-1 : ℝ) 6) := hθcd.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hθ_d2 : ContDiffOn ℝ 16 (deriv (deriv θt)) (Ioo (-1 : ℝ) 6) := hθ_d1.deriv_of_isOpen isOpen_Ioo (by norm_num)
  obtain ⟨Bf1, hBf1⟩ := hKc.exists_bound_of_continuousOn (hf_d1.continuousOn.mono hK_Ioo)
  obtain ⟨Bθ0, hBθ0⟩ := hKc.exists_bound_of_continuousOn (hθjc.1.continuousOn.mono hK_Yint)
  obtain ⟨Bθ1, hBθ1⟩ := hKc.exists_bound_of_continuousOn (hθ_d1.continuousOn.mono hK_Yint)
  obtain ⟨Bθ2, hBθ2⟩ := hKc.exists_bound_of_continuousOn (hθ_d2.continuousOn.mono hK_Yint)
  have h0_mem : (0 : ℝ) ∈ Icc (-r₀) r₀ := ⟨by linarith, by linarith⟩
  have hBθ0_nn : 0 ≤ Bθ0 := (norm_nonneg _).trans (hBθ0 0 h0_mem)
  have hBθ1_nn : 0 ≤ Bθ1 := (norm_nonneg _).trans (hBθ1 0 h0_mem)
  have hBθ2_nn : 0 ≤ Bθ2 := (norm_nonneg _).trans (hBθ2 0 h0_mem)
  have hBf1_nn : 0 ≤ Bf1 := (norm_nonneg _).trans (hBf1 0 h0_mem)
  have hev_n : ∀ᶠ z in 𝓝 (0 : ℝ), Real.pi ^ 2 / 24 ≤ nfun z + z * deriv nfun z := by
    have hc : ContinuousAt (fun z : ℝ => nfun z + z * deriv nfun z) 0 :=
      (contDiffAt_nfun.continuousAt).add (continuousAt_id.mul
        ((hn_d1.contDiffAt (isOpen_Ioo.mem_nhds zero_mem_Ioo)).continuousAt))
    have hlt : Real.pi ^ 2 / 24 < (fun z : ℝ => nfun z + z * deriv nfun z) 0 := by
      dsimp only; rw [nfun_zero]; linarith [sq_pos_of_pos Real.pi_pos]
    exact (hc.eventually (lt_mem_nhds hlt)).mono fun z hz => hz.le
  have hev_nl : ∀ᶠ z in 𝓝 (0 : ℝ), Real.pi ^ 2 / 16 ≤ nfun z ∧ nfun z ≤ Real.pi ^ 2 / 10 := by
    have hlt1 : Real.pi ^ 2 / 16 < nfun 0 := by rw [nfun_zero]; linarith [sq_pos_of_pos Real.pi_pos]
    have hlt2 : nfun 0 < Real.pi ^ 2 / 10 := by rw [nfun_zero]; linarith [sq_pos_of_pos Real.pi_pos]
    exact ((contDiffAt_nfun.continuousAt.eventually (lt_mem_nhds hlt1)).and
      (contDiffAt_nfun.continuousAt.eventually (gt_mem_nhds hlt2))).mono
      fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hev_f : ∀ᶠ z in 𝓝 (0 : ℝ), Real.pi ^ 2 / 36 ≤ fF z := by
    have hlt : Real.pi ^ 2 / 36 < fF 0 := by rw [fF_zero]; linarith [sq_pos_of_pos Real.pi_pos]
    exact (contDiffAt_fF.continuousAt.eventually (lt_mem_nhds hlt)).mono fun z hz => hz.le
  obtain ⟨ρ1, hρ1, h1_ball⟩ := Metric.eventually_nhds_iff.mp (hev_n.and (hev_nl.and hev_f))
  set δz : ℝ := min (min (rr / 4) (1 / 16 : ℝ)) (min (r₀ / 4) (ρ1 / 8))
  have hδz_pos : 0 < δz := lt_min (lt_min (by linarith [rr_pos]) (by norm_num)) (lt_min (by linarith) (by linarith))
  have hδz_le : δz ≤ min (rr / 4) (1 / 16 : ℝ) := min_le_left _ _
  have hz_mem_r0 : ∀ {z : ℝ}, 0 ≤ z → z ≤ 4 * δz → z ∈ Icc (-r₀) r₀ := fun hz0 hz4 =>
    ⟨by linarith, by have := (min_le_right (min (rr / 4) (1 / 16 : ℝ)) (min (r₀ / 4) (ρ1 / 8))).trans (min_le_left _ _); linarith⟩
  have hz_mem_rho1 : ∀ {z : ℝ}, 0 ≤ z → z ≤ 4 * δz →
      (Real.pi ^ 2 / 24 ≤ nfun z + z * deriv nfun z) ∧
      (Real.pi ^ 2 / 16 ≤ nfun z ∧ nfun z ≤ Real.pi ^ 2 / 10) ∧
      (Real.pi ^ 2 / 36 ≤ fF z) := fun hz0 hz4 => by
    apply h1_ball
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hz0]
    have := (min_le_right (min (rr / 4) (1 / 16 : ℝ)) (min (r₀ / 4) (ρ1 / 8))).trans (min_le_right _ _)
    linarith [hρ1]
  set BH10 : ℝ := 3 * Bθ0 + 2 * r₀ * Bθ1 + 1
  set BH11 : ℝ := 5 * Bθ1 + 2 * r₀ * Bθ2 + 1
  set BQ10 : ℝ := 2 * Bθ0 + 2 * r₀ * Bθ1 + 1
  set BQ11 : ℝ := 4 * Bθ1 + 2 * r₀ * Bθ2 + 1
  have hBH10_pos : 0 < BH10 := by positivity
  have hBH11_pos : 0 < BH11 := by positivity
  have hBQ10_pos : 0 < BQ10 := by positivity
  have hBQ11_pos : 0 < BQ11 := by positivity
  have hH1_bd : ∀ {z : ℝ}, z ∈ Icc (-r₀) r₀ →
      |fjH1 θt z| ≤ BH10 ∧ |deriv (fjH1 θt) z| ≤ BH11 ∧
      |2 * θt z + 2 * z * deriv θt z| ≤ BQ10 := fun {z} hz => by
    have hz_y : z ∈ Ioo (-1 : ℝ) 6 := hK_Yint hz
    have h0 := hBθ0 z hz; rw [Real.norm_eq_abs] at h0
    have h1 := hBθ1 z hz; rw [Real.norm_eq_abs] at h1
    have h2 := hBθ2 z hz; rw [Real.norm_eq_abs] at h2
    have hzd : |z| ≤ r₀ := abs_le.mpr hz
    have hda : DifferentiableAt ℝ θt z := (hθcd.contDiffAt (isOpen_Ioo.mem_nhds hz_y)).differentiableAt (by norm_num)
    have hda1 : DifferentiableAt ℝ (deriv θt) z := (hθ_d1.contDiffAt (isOpen_Ioo.mem_nhds hz_y)).differentiableAt (by norm_num)
    have hd_H1 : HasDerivAt (fjH1 θt) (5 * deriv θt z + 2 * z * deriv (deriv θt) z) z := by
      change HasDerivAt (fun w => 3 * θt w + 2 * w * deriv θt w) _ z
      exact ((hda.hasDerivAt.const_mul 3).fun_add (((hasDerivAt_id' z).const_mul 2).fun_mul hda1.hasDerivAt)).congr_deriv (by ring)
    refine ⟨?_, ?_, ?_⟩
    · calc |fjH1 θt z| ≤ 3 * |θt z| + 2 * |z| * |deriv θt z| := (abs_add_le _ _).trans (by rw [abs_mul, abs_mul, abs_mul]; norm_num)
        _ ≤ 3 * Bθ0 + 2 * r₀ * Bθ1 := by gcongr
        _ ≤ BH10 := by linarith
    · rw [hd_H1.deriv]
      calc |5 * deriv θt z + 2 * z * deriv (deriv θt) z|
          ≤ 5 * |deriv θt z| + 2 * |z| * |deriv (deriv θt) z| := (abs_add_le _ _).trans (by rw [abs_mul, abs_mul, abs_mul]; norm_num)
        _ ≤ 5 * Bθ1 + 2 * r₀ * Bθ2 := by gcongr
        _ ≤ BH11 := by linarith
    · calc |2 * θt z + 2 * z * deriv θt z| ≤ 2 * |θt z| + 2 * |z| * |deriv θt z| := (abs_add_le _ _).trans (by rw [abs_mul, abs_mul, abs_mul]; norm_num)
        _ ≤ 2 * Bθ0 + 2 * r₀ * Bθ1 := by gcongr
        _ ≤ BQ10 := by linarith
  set s₀ : ℝ := min ((Real.pi ^ 2 / 48) / (BH10 + r₀ * BH11 + 1)) ((Real.pi ^ 2 / 72) / (BQ10 + 1))
  have hs₀_pos : 0 < s₀ := lt_min (div_pos (by positivity) (by positivity)) (div_pos (by positivity) (by positivity))
  set Dθ1 : ℝ := |ctTheta1 ε| + r₀ * BH10 + 1
  set K_z : ℝ := (Real.pi ^ 2 / 100) / Dθ1
  have hK_z_pos : 0 < K_z := div_pos (by positivity) (by positivity)
  set D_crit : ℝ := Real.pi ^ 2 / 48
  set Q_lo : ℝ := Real.pi ^ 2 / 72
  have hD_crit_pos : 0 < D_crit := by positivity
  have hQ_lo_pos : 0 < Q_lo := by positivity
  set M_zp : ℝ := Dθ1 / D_crit
  set M_Q3 : ℝ := ((3 / 2 : ℝ) * Q_lo) ^ (-(1 / 3 : ℝ))
  set M_Q4 : ℝ := ((3 / 2 : ℝ) * Q_lo) ^ (-(4 / 3 : ℝ))
  set M_Qp : ℝ := Bf1 * M_zp + BQ10
  set M_nump : ℝ := (Bθ0 + r₀ * Bθ1) * M_zp
  set C_sec : ℝ := M_nump * M_Q3 + (|ctTheta1 ε| + r₀ * Bθ0) * (1 / 2 : ℝ) * M_Qp * M_Q4
  have hC_sec_nn : 0 ≤ C_sec := by positivity
  refine ⟨δz, s₀, C_sec / 2 + 1, K_z, hδz_pos, hδz_le, hs₀_pos, by positivity, hK_z_pos,
    fun {z₀ s} hz₀_pos hz₀_le hs_nn hs_le hsz => ?_⟩
  intro L θt_def
  have hIcc_r0 : ∀ {z : ℝ}, z ∈ Icc (z₀ / 4) (4 * z₀) → z ∈ Icc (-r₀) r₀ := fun {z} hz =>
    hz_mem_r0 (by linarith [hz.1, hz₀_pos]) (by linarith [hz.2, hz₀_le])
  have hIcc_rho1 : ∀ {z : ℝ}, z ∈ Icc (z₀ / 4) (4 * z₀) →
      (Real.pi ^ 2 / 24 ≤ nfun z + z * deriv nfun z) ∧
      (Real.pi ^ 2 / 16 ≤ nfun z ∧ nfun z ≤ Real.pi ^ 2 / 10) ∧
      (Real.pi ^ 2 / 36 ≤ fF z) := fun {z} hz =>
    hz_mem_rho1 (by linarith [hz.1, hz₀_pos]) (by linarith [hz.2, hz₀_le])
  have hdiff_z : ∀ {z : ℝ}, z ∈ Icc (-r₀) r₀ →
      DifferentiableAt ℝ nfun z ∧ DifferentiableAt ℝ fF z ∧ DifferentiableAt ℝ θt z ∧
      DifferentiableAt ℝ (deriv θt) z ∧ DifferentiableAt ℝ (deriv (deriv θt)) z ∧ DifferentiableAt ℝ (fjH1 θt) z := fun hzm => by
    have hnd := (hn_cd.contDiffAt (isOpen_Ioo.mem_nhds (hK_Ioo hzm))).differentiableAt (by norm_num)
    have hfd := (hf_cd.contDiffAt (isOpen_Ioo.mem_nhds (hK_Ioo hzm))).differentiableAt (by norm_num)
    have hθd := (hθcd.contDiffAt (isOpen_Ioo.mem_nhds (hK_Yint hzm))).differentiableAt (by norm_num)
    have hθ1d := (hθ_d1.contDiffAt (isOpen_Ioo.mem_nhds (hK_Yint hzm))).differentiableAt (by norm_num)
    have hθ2d := (hθ_d2.contDiffAt (isOpen_Ioo.mem_nhds (hK_Yint hzm))).differentiableAt (by norm_num)
    exact ⟨hnd, hfd, hθd, hθ1d, hθ2d, (hθd.const_mul 3).add ((differentiableAt_id.const_mul 2).fun_mul hθ1d)⟩
  have hderiv_Fcrit_ge : ∀ t ∈ Icc (0 : ℝ) s, ∀ z ∈ Icc (z₀ / 4) (4 * z₀),
      D_crit ≤ deriv (fjFcrit nfun θt t) z := fun t ht z hz => by
    have hzm := hIcc_r0 hz
    have hzr := hIcc_rho1 hz
    obtain ⟨hnd, -, -, -, -, hH1d⟩ := hdiff_z hzm
    have hder := (deriv_z_mul_fn (hnd.fun_add (hH1d.const_mul t))).deriv
    have hds := (hnd.hasDerivAt.fun_add (hH1d.hasDerivAt.const_mul t)).deriv
    have hfc_eq : fjFcrit nfun θt t = fun w => w * (nfun w + t * fjH1 θt w) := rfl
    rw [hfc_eq, hder, hds]
    obtain ⟨hB0, hB1, _⟩ := hH1_bd hzm
    have ht_small : t * (BH10 + r₀ * BH11) ≤ Real.pi ^ 2 / 48 := by
      have h1 : t ≤ (Real.pi ^ 2 / 48) / (BH10 + r₀ * BH11 + 1) := (ht.2.trans hs_le).trans (min_le_left _ _)
      have hpos : 0 < BH10 + r₀ * BH11 + 1 := by positivity
      calc t * (BH10 + r₀ * BH11) ≤ ((Real.pi ^ 2 / 48) / (BH10 + r₀ * BH11 + 1)) * (BH10 + r₀ * BH11 + 1) :=
            mul_le_mul h1 (by linarith) (by positivity) (by positivity)
        _ = Real.pi ^ 2 / 48 := div_mul_cancel₀ _ hpos.ne'
    have hzt_bd : |t * (fjH1 θt z + z * deriv (fjH1 θt) z)| ≤ Real.pi ^ 2 / 48 := by
      rw [abs_mul, abs_of_nonneg ht.1]
      have hzr0 : |z| ≤ r₀ := abs_le.mpr hzm
      have hsum : |fjH1 θt z + z * deriv (fjH1 θt) z| ≤ BH10 + r₀ * BH11 :=
        (abs_add_le _ _).trans (by rw [abs_mul]; gcongr)
      exact (mul_le_mul_of_nonneg_left hsum ht.1).trans ht_small
    have := abs_le.mp hzt_bd
    change Real.pi ^ 2 / 48 ≤ _
    linarith [hzr.1, this.1]
  have hcont_Fcrit : ∀ t ∈ Icc (0 : ℝ) s, ContinuousOn (fjFcrit nfun θt t) (Icc (z₀ / 4) (4 * z₀)) := fun t _ z hz => by
    obtain ⟨hnd, -, -, -, -, hH1d⟩ := hdiff_z (hIcc_r0 hz)
    exact (differentiableAt_id.fun_mul (hnd.add (hH1d.const_mul t))).continuousAt.continuousWithinAt
  have hcrit_ex : ∀ t ∈ Icc (0 : ℝ) s, ∃! z ∈ Icc (z₀ / 4) (4 * z₀), fjFcrit nfun θt t z = L - t * ctTheta1 ε := fun t ht => by
    have hsm : StrictMonoOn (fjFcrit nfun θt t) (Icc (z₀ / 4) (4 * z₀)) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (hcont_Fcrit t ht) fun z hz => ?_
      rw [interior_Icc] at hz
      exact lt_of_lt_of_le hD_crit_pos (hderiv_Fcrit_ge t ht z (Ioo_subset_Icc_self hz))
    have hbr : ∀ z ∈ Icc (z₀ / 4) (4 * z₀), t * |ctTheta1 ε + z * fjH1 θt z| ≤ Real.pi ^ 2 / 100 * z₀ := fun z hz => by
      have hzr : |z| ≤ r₀ := abs_le.mpr (hIcc_r0 hz)
      have hH0 := (hH1_bd (hIcc_r0 hz)).1
      have hct : |ctTheta1 ε + z * fjH1 θt z| ≤ Dθ1 := by
        calc |ctTheta1 ε + z * fjH1 θt z| ≤ |ctTheta1 ε| + |z| * |fjH1 θt z| := (abs_add_le _ _).trans (by rw [abs_mul])
          _ ≤ |ctTheta1 ε| + r₀ * BH10 := by gcongr
          _ ≤ Dθ1 := by linarith
      calc t * |ctTheta1 ε + z * fjH1 θt z| ≤ (K_z * z₀) * Dθ1 := mul_le_mul (ht.2.trans hsz) hct (abs_nonneg _) (by positivity)
        _ = Real.pi ^ 2 / 100 * z₀ := by
            have hDpos : (0 : ℝ) < Dθ1 := by positivity
            rw [show K_z = (Real.pi ^ 2 / 100) / Dθ1 from rfl]; field_simp [hDpos.ne']
    have hlo : fjFcrit nfun θt t (z₀ / 4) ≤ L - t * ctTheta1 ε := by
      have hz1_mem : z₀ / 4 ∈ Icc (z₀ / 4) (4 * z₀) := ⟨le_rfl, by linarith⟩
      have hmr1 := hIcc_rho1 hz1_mem
      have hmr0 := hIcc_rho1 (⟨by linarith, by linarith⟩ : z₀ ∈ Icc (z₀ / 4) (4 * z₀))
      have hdiff : (L - t * ctTheta1 ε) - fjFcrit nfun θt t (z₀ / 4) =
          z₀ * nfun z₀ - (z₀ / 4) * nfun (z₀ / 4) - t * (ctTheta1 ε + (z₀ / 4) * fjH1 θt (z₀ / 4)) := by unfold fjFcrit; ring
      have ht_abs : t * (ctTheta1 ε + (z₀ / 4) * fjH1 θt (z₀ / 4)) ≤ Real.pi ^ 2 / 100 * z₀ :=
        (mul_le_mul_of_nonneg_left (le_abs_self _) ht.1).trans (hbr _ hz1_mem)
      have hgap : Real.pi ^ 2 / 48 * z₀ ≤ z₀ * nfun z₀ - (z₀ / 4) * nfun (z₀ / 4) := by
        have hnz0 : Real.pi ^ 2 / 16 * z₀ ≤ z₀ * nfun z₀ := (mul_le_mul_of_nonneg_right hmr0.2.1.1 hz₀_pos.le).trans_eq (by ring)
        have hnz1 : (z₀ / 4) * nfun (z₀ / 4) ≤ (z₀ / 4) * (Real.pi ^ 2 / 10) := mul_le_mul_of_nonneg_left hmr1.2.1.2 (by linarith)
        have := sq_nonneg Real.pi; nlinarith [hz₀_pos]
      have := sq_nonneg Real.pi; nlinarith [hz₀_pos, hdiff, hgap, ht_abs]
    have hhi : L - t * ctTheta1 ε ≤ fjFcrit nfun θt t (4 * z₀) := by
      have hz4_mem : 4 * z₀ ∈ Icc (z₀ / 4) (4 * z₀) := ⟨by linarith, le_rfl⟩
      have hmr4 := hIcc_rho1 hz4_mem
      have hmr0 := hIcc_rho1 (⟨by linarith, by linarith⟩ : z₀ ∈ Icc (z₀ / 4) (4 * z₀))
      have hdiff : fjFcrit nfun θt t (4 * z₀) - (L - t * ctTheta1 ε) =
          (4 * z₀) * nfun (4 * z₀) - z₀ * nfun z₀ + t * (ctTheta1 ε + (4 * z₀) * fjH1 θt (4 * z₀)) := by unfold fjFcrit; ring
      have ht_abs : -(Real.pi ^ 2 / 100 * z₀) ≤ t * (ctTheta1 ε + (4 * z₀) * fjH1 θt (4 * z₀)) := by
        have hle_neg : -(Real.pi ^ 2 / 100 * z₀) ≤ -(t * |ctTheta1 ε + (4 * z₀) * fjH1 θt (4 * z₀)|) := neg_le_neg (hbr _ hz4_mem)
        exact hle_neg.trans (by nlinarith [ht.1, neg_abs_le (ctTheta1 ε + (4 * z₀) * fjH1 θt (4 * z₀))])
      have hgap : Real.pi ^ 2 / 24 * z₀ ≤ (4 * z₀) * nfun (4 * z₀) - z₀ * nfun z₀ := by
        have hnz4 : (4 * z₀) * (Real.pi ^ 2 / 16) ≤ (4 * z₀) * nfun (4 * z₀) := mul_le_mul_of_nonneg_left hmr4.2.1.1 (by linarith)
        have hnz0 : z₀ * nfun z₀ ≤ z₀ * (Real.pi ^ 2 / 10) := mul_le_mul_of_nonneg_left hmr0.2.1.2 hz₀_pos.le
        have := sq_nonneg Real.pi; nlinarith [hz₀_pos]
      have := sq_nonneg Real.pi; nlinarith [hz₀_pos, hdiff, hgap, ht_abs]
    obtain ⟨zt, hzt_mem, hzt_eq⟩ := intermediate_value_Icc (by linarith : z₀ / 4 ≤ 4 * z₀) (hcont_Fcrit t ht) ⟨hlo, hhi⟩
    exact ⟨zt, ⟨hzt_mem, hzt_eq⟩, fun z' ⟨hz', hzeq⟩ => hsm.injOn hz' hzt_mem (hzeq.trans hzt_eq.symm)⟩
  obtain ⟨z_s, ⟨hz_s_mem, hz_s_eq⟩, hz_s_uniq⟩ := hcrit_ex s ⟨hs_nn, le_rfl⟩
  refine ⟨z_s, hz_s_mem, hz_s_eq, fun z' hz' hzeq => hz_s_uniq z' ⟨hz', hzeq⟩, ?_⟩
  rcases hs_nn.eq_or_lt with rfl | hs_pos
  · have hz_eq0 : z_s = z₀ :=
      (hz_s_uniq z₀ ⟨⟨by linarith, by linarith⟩, by dsimp only [L]; unfold fjFcrit; simp⟩).symm
    dsimp only [θt_def]
    rw [hz_eq0, zero_mul, add_zero]
    have ha0 : fjAfold fF θt 0 z₀ = z₀ * dF z₀ ^ 2 := by
      have hf_z0_le := (hz_mem_rho1 hz₀_pos.le (by linarith [hz₀_le])).2.2
      have hpi := sq_pos_of_pos Real.pi_pos
      have hf_pos : 0 < fF z₀ := by linarith
      unfold fjAfold fjQ dF
      simp only [zero_mul, add_zero]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [ha0, sub_self, abs_zero]; positivity
  -- `0 < s`: define `z_fn` on `[0, s]` via `Classical.epsilon`
  let z_fn : ℝ → ℝ := fun t => Classical.epsilon (fun z => z ∈ Icc (z₀ / 4) (4 * z₀) ∧ fjFcrit nfun θt t z = L - t * ctTheta1 ε)
  have hz_fn_spec : ∀ t ∈ Icc (0 : ℝ) s, z_fn t ∈ Icc (z₀ / 4) (4 * z₀) ∧ fjFcrit nfun θt t (z_fn t) = L - t * ctTheta1 ε :=
    fun t ht => Classical.epsilon_spec (ExistsUnique.exists (hcrit_ex t ht))
  have hz_fn_uniq : ∀ t ∈ Icc (0 : ℝ) s, ∀ z ∈ Icc (z₀ / 4) (4 * z₀),
      fjFcrit nfun θt t z = L - t * ctTheta1 ε → z = z_fn t := fun t ht z hz hze =>
    (hcrit_ex t ht).unique ⟨hz, hze⟩ (hz_fn_spec t ht)
  have hz_fn_0 : z_fn 0 = z₀ :=
    (hz_fn_uniq 0 ⟨le_rfl, hs_nn⟩ z₀ ⟨by linarith, by linarith⟩ (by dsimp only [L]; unfold fjFcrit; simp)).symm
  have hz_fn_s : z_fn s = z_s := (hz_fn_uniq s ⟨hs_nn, le_rfl⟩ z_s hz_s_mem hz_s_eq).symm
  have hz_fn_lip : ∀ t₁ ∈ Icc (0 : ℝ) s, ∀ t₂ ∈ Icc (0 : ℝ) s, |z_fn t₁ - z_fn t₂| ≤ M_zp * |t₁ - t₂| := by
    intro t₁ ht₁ t₂ ht₂
    obtain ⟨hz1, he1⟩ := hz_fn_spec t₁ ht₁
    obtain ⟨hz2, he2⟩ := hz_fn_spec t₂ ht₂
    have hdiff_F : |fjFcrit nfun θt t₁ (z_fn t₁) - fjFcrit nfun θt t₁ (z_fn t₂)| =
        |(t₁ - t₂) * (ctTheta1 ε + z_fn t₂ * fjH1 θt (z_fn t₂))| := by
      have h3 : fjFcrit nfun θt t₁ (z_fn t₂) - fjFcrit nfun θt t₂ (z_fn t₂) =
          (t₁ - t₂) * (z_fn t₂ * fjH1 θt (z_fn t₂)) := by unfold fjFcrit; ring
      have hd : fjFcrit nfun θt t₁ (z_fn t₁) - fjFcrit nfun θt t₁ (z_fn t₂) =
          -((t₁ - t₂) * (ctTheta1 ε + z_fn t₂ * fjH1 θt (z_fn t₂))) := by linarith [he1, he2, h3]
      rw [hd, abs_neg]
    have hzm2 := hIcc_r0 hz2
    have hH2 := (hH1_bd hzm2).1
    have hrhs : |(t₁ - t₂) * (ctTheta1 ε + z_fn t₂ * fjH1 θt (z_fn t₂))| ≤ Dθ1 * |t₁ - t₂| := by
      rw [abs_mul]
      have hct : |ctTheta1 ε + z_fn t₂ * fjH1 θt (z_fn t₂)| ≤ Dθ1 := by
        have hz2r : |z_fn t₂| ≤ r₀ := abs_le.mpr hzm2
        calc |ctTheta1 ε + z_fn t₂ * fjH1 θt (z_fn t₂)| ≤ |ctTheta1 ε| + |z_fn t₂ * fjH1 θt (z_fn t₂)| := abs_add_le _ _
          _ ≤ |ctTheta1 ε| + r₀ * BH10 := by rw [abs_mul]; gcongr
          _ ≤ Dθ1 := by linarith
      calc |t₁ - t₂| * |ctTheta1 ε + z_fn t₂ * fjH1 θt (z_fn t₂)| ≤ |t₁ - t₂| * Dθ1 := by gcongr
        _ = Dθ1 * |t₁ - t₂| := by ring
    have hlow_F : D_crit * |z_fn t₁ - z_fn t₂| ≤ |fjFcrit nfun θt t₁ (z_fn t₁) - fjFcrit nfun θt t₁ (z_fn t₂)| := by
      have hdiff_on : ∀ z ∈ Icc (z₀ / 4) (4 * z₀), HasDerivAt (fjFcrit nfun θt t₁) (deriv (fjFcrit nfun θt t₁) z) z := fun z hz => by
        obtain ⟨hnd, -, -, -, -, hH1d⟩ := hdiff_z (hIcc_r0 hz)
        exact (differentiableAt_id.fun_mul (hnd.add (hH1d.const_mul t₁))).hasDerivAt
      have hmono : ∀ a b, a ∈ Icc (z₀ / 4) (4 * z₀) → b ∈ Icc (z₀ / 4) (4 * z₀) → a ≤ b →
          D_crit * (b - a) ≤ fjFcrit nfun θt t₁ b - fjFcrit nfun θt t₁ a := fun a b ha hb hab => by
        rcases hab.eq_or_lt with rfl | hlt
        · simp
        · have hsub : Icc a b ⊆ Icc (z₀ / 4) (4 * z₀) := Icc_subset_Icc ha.1 hb.2
          obtain ⟨c, hcm, hce⟩ := exists_hasDerivAt_eq_slope (fjFcrit nfun θt t₁) (deriv (fjFcrit nfun θt t₁))
            hlt ((hcont_Fcrit t₁ ht₁).mono hsub) fun w hw => hdiff_on w (hsub (Ioo_subset_Icc_self hw))
          have hpos : 0 < b - a := sub_pos.mpr hlt
          rw [show fjFcrit nfun θt t₁ b - fjFcrit nfun θt t₁ a = deriv (fjFcrit nfun θt t₁) c * (b - a) by
            rw [hce, div_mul_cancel₀ _ hpos.ne']]
          exact mul_le_mul_of_nonneg_right (hderiv_Fcrit_ge t₁ ht₁ c (hsub (Ioo_subset_Icc_self hcm))) hpos.le
      rcases le_total (z_fn t₁) (z_fn t₂) with hle | hle
      · rw [abs_sub_comm (z_fn t₁), abs_sub_comm (fjFcrit _ _ _ (z_fn t₁)), abs_of_nonneg (sub_nonneg.mpr hle)]
        exact (hmono _ _ hz1 hz2 hle).trans (le_abs_self _)
      · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        exact (hmono _ _ hz2 hz1 hle).trans (le_abs_self _)
    have hmul_lip : D_crit * |z_fn t₁ - z_fn t₂| ≤ Dθ1 * |t₁ - t₂| :=
      hlow_F.trans (hdiff_F.le.trans hrhs)
    calc |z_fn t₁ - z_fn t₂| = (D_crit * |z_fn t₁ - z_fn t₂|) / D_crit := by field_simp [hD_crit_pos.ne']
      _ ≤ (Dθ1 * |t₁ - t₂|) / D_crit := div_le_div_of_nonneg_right hmul_lip hD_crit_pos.le
      _ = M_zp * |t₁ - t₂| := by dsimp only [M_zp]; ring
  -- Differentiate `z_fn` within `[0, s]`
  let z_fn_p : ℝ → ℝ := fun t =>
    -(ctTheta1 ε + z_fn t * fjH1 θt (z_fn t)) / deriv (fjFcrit nfun θt t) (z_fn t)
  have hz_fn_deriv : ∀ t ∈ Icc (0 : ℝ) s,
      D_crit ≤ deriv (fjFcrit nfun θt t) (z_fn t) ∧ HasDerivWithinAt z_fn (z_fn_p t) (Icc 0 s) t := by
    intro t ht
    obtain ⟨hz_mem, hz_eq⟩ := hz_fn_spec t ht
    set z := z_fn t
    have hFz_ge := hderiv_Fcrit_ge t ht z hz_mem
    refine ⟨hFz_ge, ?_⟩
    have hzm := hIcc_r0 hz_mem
    obtain ⟨hnd, -, -, -, -, hH1d⟩ := hdiff_z (hIcc_r0 hz_mem)
    set Fz : ℝ := deriv (fjFcrit nfun θt t) z
    set Ft : ℝ := ctTheta1 ε + z * fjH1 θt z
    have hFz_ne : Fz ≠ 0 := (lt_of_lt_of_le hD_crit_pos hFz_ge).ne'
    let G : ℝ × ℝ → ℝ := fun p => fjFcrit nfun θt p.1 p.2 + p.1 * ctTheta1 ε
    let F' : ℝ × ℝ →L[ℝ] ℝ := Ft • ContinuousLinearMap.fst ℝ ℝ ℝ + Fz • ContinuousLinearMap.snd ℝ ℝ ℝ
    have hd_u : HasFDerivAt (fun p : ℝ × ℝ => p.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (t, z) := hasFDerivAt_fst
    have hd_w : HasFDerivAt (fun p : ℝ × ℝ => p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (t, z) := hasFDerivAt_snd
    have hd_n : HasFDerivAt (fun p : ℝ × ℝ => nfun p.2) (deriv nfun z • ContinuousLinearMap.snd ℝ ℝ ℝ) (t, z) :=
      hasDerivAt_comp_snd hnd.hasDerivAt
    have hd_H : HasFDerivAt (fun p : ℝ × ℝ => fjH1 θt p.2) (deriv (fjH1 θt) z • ContinuousLinearMap.snd ℝ ℝ ℝ) (t, z) :=
      hasDerivAt_comp_snd hH1d.hasDerivAt
    have hd_G_raw := ((hd_w.fun_mul (hd_n.fun_add (hd_u.fun_mul hd_H))).fun_add (hd_u.mul_const (ctTheta1 ε)))
    have hd_G : HasFDerivAt G F' (t, z) := by
      refine hd_G_raw.congr_fderiv ?_
      have hder := (deriv_z_mul_fn (hnd.fun_add (hH1d.const_mul t))).deriv
      have hds := (hnd.hasDerivAt.fun_add (hH1d.hasDerivAt.const_mul t)).deriv
      have hFz_eq : Fz = (nfun z + t * fjH1 θt z) + z * (deriv nfun z + t * deriv (fjH1 θt) z) := by
        change deriv (fun w => w * (nfun w + t * fjH1 θt w)) z = _
        rw [hder, hds]
      ext <;> simp [F', Ft, hFz_eq] <;> ring
    have hγ_O : (fun u : ℝ => (u, z_fn u) - (t, z)) =O[𝓝[Icc 0 s] t] fun u => u - t := by
      refine Asymptotics.IsBigO.of_bound (max 1 M_zp) ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hlip := hz_fn_lip u hu t ht
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      refine max_le (le_mul_of_one_le_left (abs_nonneg _) (le_max_left 1 M_zp)) ?_
      exact hlip.trans (mul_le_mul_of_nonneg_right (le_max_right 1 M_zp) (abs_nonneg _))
    have hγ_tend : Tendsto (fun u : ℝ => (u, z_fn u)) (𝓝[Icc 0 s] t) (𝓝 (t, z)) := by
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro ε' hε'
      refine ⟨ε' / (max 1 M_zp + 1), by positivity, fun u hu hdist => ?_⟩
      have hlip := hz_fn_lip u hu t ht
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; rw [Real.dist_eq] at hdist
      have h1 : |u - t| < ε' := lt_of_lt_of_le hdist (div_le_self hε'.le (by linarith [le_max_left 1 M_zp]))
      have h2 : |z_fn u - z| < ε' := by
        calc |z_fn u - z| ≤ (max 1 M_zp + 1) * |u - t| :=
              hlip.trans (mul_le_mul_of_nonneg_right (by linarith [le_max_right 1 M_zp]) (abs_nonneg _))
          _ < (max 1 M_zp + 1) * (ε' / (max 1 M_zp + 1)) := mul_lt_mul_of_pos_left hdist (by positivity)
          _ = ε' := mul_div_cancel₀ _ (by positivity)
      exact max_lt h1 h2
    have hlo : (fun u : ℝ => -(Ft * (u - t) + Fz * (z_fn u - z))) =o[𝓝[Icc 0 s] t] fun u => u - t := by
      have h1 := (hd_G.isLittleO.comp_tendsto hγ_tend).trans_isBigO hγ_O
      refine h1.congr' ?_ (Eventually.of_forall fun _ => rfl)
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hGu : G (u, z_fn u) = L := by dsimp only [G]; rw [(hz_fn_spec u hu).2]; ring
      have hGt : G (t, z) = L := by dsimp only [G]; rw [hz_eq]; ring
      simp only [Function.comp_apply, hGu, hGt, sub_self, F', add_apply,
        smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul, zero_sub]
    have hlo2 : (fun u : ℝ => z_fn u - z - (u - t) • z_fn_p t) =o[𝓝[Icc 0 s] t] fun u => u - t := by
      have hFz_ne' : deriv (fjFcrit nfun θt t) (z_fn t) ≠ 0 := hFz_ne
      have h2 := hlo.const_mul_left (-Fz⁻¹)
      refine h2.congr' (Eventually.of_forall fun u => ?_) (Eventually.of_forall fun _ => rfl)
      dsimp only [z_fn_p, Ft, Fz, z]; rw [smul_eq_mul]; field_simp [hFz_ne']; ring
    exact hasDerivWithinAt_iff_isLittleO.mpr hlo2
  -- Compute `HasDerivWithinAt` for `a t = fjAfold fF θt t (z_fn t)`
  let Q_fn : ℝ → ℝ := fun t => fjQ fF θt t (z_fn t)
  have hQ_pos : ∀ t ∈ Icc (0 : ℝ) s, Q_lo ≤ Q_fn t := fun t ht => by
    obtain ⟨hz_mem, -⟩ := hz_fn_spec t ht
    have hzm := hIcc_r0 hz_mem
    have hzr := hIcc_rho1 hz_mem
    have hQ1 := (hH1_bd hzm).2.2
    have ht_bd : t * |2 * θt (z_fn t) + 2 * z_fn t * deriv θt (z_fn t)| ≤ Real.pi ^ 2 / 72 := by
      have h1 : t ≤ (Real.pi ^ 2 / 72) / (BQ10 + 1) := (ht.2.trans hs_le).trans (min_le_right _ _)
      have hpos : 0 < BQ10 + 1 := by positivity
      calc t * |2 * θt (z_fn t) + 2 * z_fn t * deriv θt (z_fn t)| ≤ t * BQ10 := mul_le_mul_of_nonneg_left hQ1 ht.1
        _ ≤ ((Real.pi ^ 2 / 72) / (BQ10 + 1)) * (BQ10 + 1) := mul_le_mul h1 (by linarith) (by positivity) (by positivity)
        _ = Real.pi ^ 2 / 72 := div_mul_cancel₀ _ hpos.ne'
    have h2 := abs_le.mp (show |t * (2 * θt (z_fn t) + 2 * z_fn t * deriv θt (z_fn t))| ≤ Real.pi ^ 2 / 72 by
      rwa [abs_mul, abs_of_nonneg ht.1])
    dsimp only [Q_fn, fjQ, Q_lo]
    linarith [hzr.2.2, h2.1]
  let a_fn : ℝ → ℝ := fun t => fjAfold fF θt t (z_fn t)
  let ap_fn : ℝ → ℝ := fun t => -(ctTheta1 ε + z_fn t * θt (z_fn t)) / ((3 / 2 : ℝ) * Q_fn t) ^ (1 / 3 : ℝ)
  have ha_deriv : ∀ t ∈ Icc (0 : ℝ) s, HasDerivWithinAt a_fn (ap_fn t) (Icc 0 s) t := fun t ht => by
    obtain ⟨hz_mem, -⟩ := hz_fn_spec t ht
    set z := z_fn t
    have hz_pos : 0 < z := by linarith [hz_mem.1, hz₀_pos]
    have hzm := hIcc_r0 hz_mem
    have hz_oo : z ∈ Ioo (0 : ℝ) rr := ⟨hz_pos, (hK_Ioo hzm).2⟩
    obtain ⟨hnd, hfd, hθd, hθ1d, hθ2d, hH1d⟩ := hdiff_z hzm
    obtain ⟨hFz_ge, hz_d⟩ := hz_fn_deriv t ht
    have hQ_t_pos : 0 < (3 / 2 : ℝ) * Q_fn t := by linarith [hQ_pos t ht]
    let gQ : ℝ → ℝ := fun w => 2 * θt w + 2 * w * deriv θt w
    have hgQ_d : HasDerivAt gQ (4 * deriv θt z + 2 * z * deriv (deriv θt) z) z := by
      have hA := hθd.hasDerivAt.const_mul 2
      have hB := ((hasDerivAt_id' z).const_mul 2).fun_mul hθ1d.hasDerivAt
      change HasDerivAt (fun w => 2 * θt w + 2 * w * deriv θt w) _ z
      exact (hA.fun_add hB).congr_deriv (by ring)
    have hQ_w : HasDerivWithinAt Q_fn
        (deriv fF z * z_fn_p t + (gQ z + t * ((4 * deriv θt z + 2 * z * deriv (deriv θt) z) * z_fn_p t)))
        (Icc 0 s) t := by
      have hf_w := hfd.hasDerivAt.comp_hasDerivWithinAt t hz_d
      have hgQ_w := hgQ_d.comp_hasDerivWithinAt t hz_d
      exact hf_w.fun_add (((hasDerivAt_id' t).hasDerivWithinAt.fun_mul hgQ_w).congr_deriv (by
        simp only [Function.comp_apply, z]; ring))
    have h32Q_w := hQ_w.const_mul (3 / 2 : ℝ)
    have hpow_w := h32Q_w.rpow_const (p := (2 / 3 : ℝ)) (Or.inl hQ_t_pos.ne')
    have ha_w := hz_d.fun_mul hpow_w
    refine ha_w.congr_deriv ?_
    set den : ℝ := ((3 / 2 : ℝ) * Q_fn t) ^ (1 / 3 : ℝ)
    have hden_ne : den ≠ 0 := (Real.rpow_pos_of_pos hQ_t_pos _).ne'
    have hpow_sub : ((3 / 2 : ℝ) * Q_fn t) ^ (2 / 3 : ℝ) = ((3 / 2 : ℝ) * Q_fn t) * den⁻¹ := by
      rw [show (2 / 3 : ℝ) = 1 + (-(1 / 3 : ℝ)) by norm_num, Real.rpow_add hQ_t_pos, Real.rpow_one,
        Real.rpow_neg hQ_t_pos.le]
    set Fz : ℝ := deriv (fjFcrit nfun θt t) z
    have hFz_ne : Fz ≠ 0 := (lt_of_lt_of_le hD_crit_pos hFz_ge).ne'
    have hFz_val : Fz = (nfun z + z * deriv nfun z) + t * (fjH1 θt z + z * (5 * deriv θt z + 2 * z * deriv (deriv θt) z)) := by
      have hder := (deriv_z_mul_fn (hnd.fun_add (hH1d.const_mul t))).deriv
      have hds := (hnd.hasDerivAt.fun_add (hH1d.hasDerivAt.const_mul t)).deriv
      have hH1_der : HasDerivAt (fjH1 θt) (5 * deriv θt z + 2 * z * deriv (deriv θt) z) z := by
        have hA := hθd.hasDerivAt.const_mul 3
        have hB := ((hasDerivAt_id' z).const_mul 2).fun_mul hθ1d.hasDerivAt
        change HasDerivAt (fun w => 3 * θt w + 2 * w * deriv θt w) _ z
        exact (hA.fun_add hB).congr_deriv (by ring)
      change deriv (fun w => w * (nfun w + t * fjH1 θt w)) z = _
      rw [hder, hds, hH1_der.deriv]; ring
    have hode := three_halves_fF_add_z_deriv_fF hz_oo
    have h23 : ((2 / 3 : ℝ) - 1) = -(1 / 3 : ℝ) := by norm_num
    rw [h23, hpow_sub, Real.rpow_neg hQ_t_pos.le]
    have hQ_id : (3 / 2 : ℝ) * Q_fn t + z * (deriv fF z + t * (4 * deriv θt z + 2 * z * deriv (deriv θt) z)) = Fz := by
      rw [hFz_val]; dsimp only [Q_fn, fjQ, fjH1]; linarith [hode]
    have h_diff_H : z * gQ z - z * fjH1 θt z = -(z * θt z) := by dsimp only [gQ, fjH1]; ring
    have hnum : (-(ctTheta1 ε + z * fjH1 θt z)) * ((3 / 2 : ℝ) * Q_fn t) +
        z * ((3 / 2 : ℝ) * (deriv fF z * (-(ctTheta1 ε + z * fjH1 θt z)) +
          (gQ z * Fz + t * ((4 * deriv θt z + 2 * z * deriv (deriv θt) z) * (-(ctTheta1 ε + z * fjH1 θt z))))) *
          (2 / 3 : ℝ)) = -(ctTheta1 ε + z * θt z) * Fz := by
      calc _ = -(ctTheta1 ε + z * fjH1 θt z) * ((3 / 2 : ℝ) * Q_fn t + z * (deriv fF z + t * (4 * deriv θt z + 2 * z * deriv (deriv θt) z))) + Fz * (z * gQ z) := by ring
        _ = -(ctTheta1 ε + z * fjH1 θt z) * Fz + Fz * (z * gQ z) := by rw [hQ_id]
        _ = -(ctTheta1 ε + z * θt z) * Fz + Fz * (z * gQ z - z * fjH1 θt z + z * θt z) := by ring
        _ = -(ctTheta1 ε + z * θt z) * Fz := by rw [h_diff_H]; ring
    dsimp only [ap_fn, z_fn_p]
    calc (-(ctTheta1 ε + z * fjH1 θt z) / Fz) * (((3 / 2 : ℝ) * Q_fn t) * den⁻¹) +
        z * ((3 / 2 : ℝ) * (deriv fF z * (-(ctTheta1 ε + z * fjH1 θt z) / Fz) +
          (gQ z + t * ((4 * deriv θt z + 2 * z * deriv (deriv θt) z) * (-(ctTheta1 ε + z * fjH1 θt z) / Fz)))) *
          (2 / 3 : ℝ) * den⁻¹)
        = ((-(ctTheta1 ε + z * fjH1 θt z)) * ((3 / 2 : ℝ) * Q_fn t) +
            z * ((3 / 2 : ℝ) * (deriv fF z * (-(ctTheta1 ε + z * fjH1 θt z)) +
              (gQ z * Fz + t * ((4 * deriv θt z + 2 * z * deriv (deriv θt) z) * (-(ctTheta1 ε + z * fjH1 θt z))))) *
              (2 / 3 : ℝ))) / (den * Fz) := by field_simp [hden_ne, hFz_ne]
      _ = (-(ctTheta1 ε + z * θt z) * Fz) / (den * Fz) := by rw [hnum]
      _ = -(ctTheta1 ε + z * θt z) / den := by field_simp [hden_ne, hFz_ne]
  -- Bound `|ap_fn t - ap_fn 0| ≤ C_sec * t` for `t ∈ [0, s]`
  have hap_lip : ∀ t ∈ Icc (0 : ℝ) s, |ap_fn t - ap_fn 0| ≤ C_sec * t := fun t ht => by
    obtain ⟨hz_t, -⟩ := hz_fn_spec t ht
    obtain ⟨hz_0, -⟩ := hz_fn_spec 0 ⟨le_rfl, hs_nn⟩
    have hlip_z : |z_fn t - z₀| ≤ M_zp * t := by
      have h1 := hz_fn_lip t ht 0 ⟨le_rfl, hs_nn⟩
      rwa [hz_fn_0, sub_zero, abs_of_nonneg ht.1] at h1
    let num : ℝ → ℝ := fun z => ctTheta1 ε + z * θt z
    have hnum_mv : |num (z_fn t) - num z₀| ≤ M_nump * t := by
      have hnum_lip : |num (z_fn t) - num z₀| ≤ (Bθ0 + r₀ * Bθ1) * |z_fn t - z₀| := by
        have hz_0' : z_fn 0 ∈ Icc (z₀ / 4) (4 * z₀) := hz_0
        have hlip0 := mvt_lip_on_Icc (f := num) (M := Bθ0 + r₀ * Bθ1) (by positivity)
          (fun z hz => by
            obtain ⟨-, -, hθd, -, -, -⟩ := hdiff_z (hIcc_r0 hz)
            exact ((differentiableAt_const _).add (differentiableAt_id.fun_mul hθd)).continuousAt.continuousWithinAt)
          (fun z hz => by
            obtain ⟨-, -, hθd, -, -, -⟩ := hdiff_z (hIcc_r0 hz)
            exact (((differentiableAt_const _).fun_add (differentiableAt_id.fun_mul hθd)) :
              DifferentiableAt ℝ num z).hasDerivAt)
          (fun z hz => by
            have hzm := hIcc_r0 hz
            obtain ⟨-, -, hθd, -, -, -⟩ := hdiff_z hzm
            have hder : deriv num z = θt z + z * deriv θt z :=
              ((hasDerivAt_const z (ctTheta1 ε)).add ((hasDerivAt_id' z).fun_mul hθd.hasDerivAt)).congr_deriv (by ring) |>.deriv
            have h0 := hBθ0 z hzm; rw [Real.norm_eq_abs] at h0
            have h1 := hBθ1 z hzm; rw [Real.norm_eq_abs] at h1
            have hzr : |z| ≤ r₀ := abs_le.mpr hzm
            rw [hder]
            calc |θt z + z * deriv θt z| ≤ |θt z| + |z| * |deriv θt z| := (abs_add_le _ _).trans (by rw [abs_mul])
              _ ≤ Bθ0 + r₀ * Bθ1 := add_le_add h0 (mul_le_mul hzr h1 (abs_nonneg _) hr₀_pos.le))
          hz_t hz_0'
        rwa [hz_fn_0] at hlip0
      calc |num (z_fn t) - num z₀| ≤ (Bθ0 + r₀ * Bθ1) * |z_fn t - z₀| := hnum_lip
        _ ≤ (Bθ0 + r₀ * Bθ1) * (M_zp * t) := mul_le_mul_of_nonneg_left hlip_z (by positivity)
        _ = M_nump * t := by ring
    have hQ_mv : |Q_fn t - Q_fn 0| ≤ M_Qp * t := by
      have hfF_lip : |fF (z_fn t) - fF z₀| ≤ Bf1 * |z_fn t - z₀| := by
        have hlip0 := mvt_lip_on_Icc (f := fF) (M := Bf1) hBf1_nn
          (fun z hz => (hdiff_z (hIcc_r0 hz)).2.1.continuousAt.continuousWithinAt)
          (fun z hz => (hdiff_z (hIcc_r0 hz)).2.1.hasDerivAt)
          (fun z hz => by simpa [Real.norm_eq_abs] using hBf1 z (hIcc_r0 hz))
          hz_t hz_0
        rwa [hz_fn_0] at hlip0
      have hQ0 : Q_fn 0 = fF z₀ := by dsimp only [Q_fn, fjQ]; rw [hz_fn_0]; ring
      have hQt_sub : Q_fn t - Q_fn 0 = (fF (z_fn t) - fF z₀) + t * (2 * θt (z_fn t) + 2 * z_fn t * deriv θt (z_fn t)) := by
        rw [hQ0]; dsimp only [Q_fn, fjQ]; ring
      have htQ := (hH1_bd (hIcc_r0 hz_t)).2.2
      rw [hQt_sub]
      calc |(fF (z_fn t) - fF z₀) + t * (2 * θt (z_fn t) + 2 * z_fn t * deriv θt (z_fn t))|
          ≤ |fF (z_fn t) - fF z₀| + t * |2 * θt (z_fn t) + 2 * z_fn t * deriv θt (z_fn t)| := by
            have := abs_add_le (fF (z_fn t) - fF z₀) (t * (2 * θt (z_fn t) + 2 * z_fn t * deriv θt (z_fn t)))
            rwa [abs_mul, abs_of_nonneg ht.1] at this
        _ ≤ Bf1 * (M_zp * t) + t * BQ10 :=
            add_le_add (hfF_lip.trans (mul_le_mul_of_nonneg_left hlip_z hBf1_nn)) (mul_le_mul_of_nonneg_left htQ ht.1)
        _ = M_Qp * t := by ring
    have hq3_t : ((3 / 2 : ℝ) * Q_fn t) ^ (-(1 / 3 : ℝ)) ≤ M_Q3 :=
      Real.rpow_le_rpow_of_nonpos (by dsimp only [Q_lo]; positivity) (mul_le_mul_of_nonneg_left (hQ_pos t ht) (by norm_num)) (by norm_num)
    have hq3_mv : |((3 / 2 : ℝ) * Q_fn t) ^ (-(1 / 3 : ℝ)) - ((3 / 2 : ℝ) * Q_fn 0) ^ (-(1 / 3 : ℝ))| ≤
        (1 / 2 : ℝ) * M_Qp * M_Q4 * t := by
      let qL : ℝ := (3 / 2 : ℝ) * Q_lo
      let qU : ℝ := max ((3 / 2 : ℝ) * Q_fn t) ((3 / 2 : ℝ) * Q_fn 0) + 1
      have hqt_mem : (3 / 2 : ℝ) * Q_fn t ∈ Icc qL qU :=
        ⟨mul_le_mul_of_nonneg_left (hQ_pos t ht) (by norm_num), by linarith [le_max_left ((3 / 2 : ℝ) * Q_fn t) ((3 / 2 : ℝ) * Q_fn 0)]⟩
      have hq0_mem : (3 / 2 : ℝ) * Q_fn 0 ∈ Icc qL qU :=
        ⟨mul_le_mul_of_nonneg_left (hQ_pos 0 ⟨le_rfl, hs_nn⟩) (by norm_num), by linarith [le_max_right ((3 / 2 : ℝ) * Q_fn t) ((3 / 2 : ℝ) * Q_fn 0)]⟩
      have hq_pos : ∀ {q : ℝ}, q ∈ Icc qL qU → 0 < q := fun {q} hq =>
        lt_of_lt_of_le (by dsimp only [qL, Q_lo]; positivity) hq.1
      have hlip_q := mvt_lip_on_Icc (f := fun q : ℝ => q ^ (-(1 / 3 : ℝ))) (l := qL) (u := qU) (M := (1 / 3 : ℝ) * M_Q4)
        (by positivity)
        (fun q hq => ((hasDerivAt_id' q).rpow_const (Or.inl (hq_pos hq).ne')).continuousAt.continuousWithinAt)
        (fun q hq => ((hasDerivAt_id' q).rpow_const (p := -(1 / 3 : ℝ)) (Or.inl (hq_pos hq).ne')).differentiableAt.hasDerivAt)
        (fun q hq => by
          have hd := ((hasDerivAt_id' q).rpow_const (p := -(1 / 3 : ℝ)) (Or.inl (hq_pos hq).ne')).deriv
          rw [hd, show (-(1 / 3 : ℝ) - 1) = -(4 / 3 : ℝ) by norm_num, one_mul, abs_mul,
            abs_of_neg (by norm_num : -(1 / 3 : ℝ) < 0), neg_neg, abs_of_pos (Real.rpow_pos_of_pos (hq_pos hq) _)]
          have hle : q ^ (-(4 / 3 : ℝ)) ≤ M_Q4 := by
            dsimp only [M_Q4]; exact Real.rpow_le_rpow_of_nonpos (by positivity) hq.1 (by norm_num)
          exact mul_le_mul_of_nonneg_left hle (by norm_num))
        hqt_mem hq0_mem
      calc |((3 / 2 : ℝ) * Q_fn t) ^ (-(1 / 3 : ℝ)) - ((3 / 2 : ℝ) * Q_fn 0) ^ (-(1 / 3 : ℝ))|
          ≤ (1 / 3 : ℝ) * M_Q4 * |(3 / 2 : ℝ) * Q_fn t - (3 / 2 : ℝ) * Q_fn 0| := hlip_q
        _ = (1 / 2 : ℝ) * M_Q4 * |Q_fn t - Q_fn 0| := by
            rw [show (3 / 2 : ℝ) * Q_fn t - (3 / 2 : ℝ) * Q_fn 0 = (3 / 2 : ℝ) * (Q_fn t - Q_fn 0) by ring,
              abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]; ring
        _ ≤ (1 / 2 : ℝ) * M_Q4 * (M_Qp * t) := by gcongr
        _ = (1 / 2 : ℝ) * M_Qp * M_Q4 * t := by ring
    have hnum0_bd : |num z₀| ≤ |ctTheta1 ε| + r₀ * Bθ0 := by
      have hzm0 := hIcc_r0 (hz_fn_0 ▸ hz_0)
      have h0 := hBθ0 z₀ hzm0; rw [Real.norm_eq_abs] at h0
      have hz0r : |z₀| ≤ r₀ := abs_le.mpr hzm0
      calc |num z₀| ≤ |ctTheta1 ε| + |z₀ * θt z₀| := abs_add_le _ _
        _ ≤ |ctTheta1 ε| + r₀ * Bθ0 := by rw [abs_mul]; gcongr
    have hap_eq : ∀ u ∈ Icc (0 : ℝ) s, ap_fn u = -num (z_fn u) * ((3 / 2 : ℝ) * Q_fn u) ^ (-(1 / 3 : ℝ)) := fun u hu => by
      have hQu : 0 < (3 / 2 : ℝ) * Q_fn u := by linarith [hQ_pos u hu]
      dsimp only [ap_fn, num]; rw [div_eq_mul_inv, ← Real.rpow_neg hQu.le]
    rw [hap_eq t ht, hap_eq 0 ⟨le_rfl, hs_nn⟩, hz_fn_0]
    have hsplit : -num (z_fn t) * ((3 / 2 : ℝ) * Q_fn t) ^ (-(1 / 3 : ℝ)) -
        (-num z₀ * ((3 / 2 : ℝ) * Q_fn 0) ^ (-(1 / 3 : ℝ))) =
        -(num (z_fn t) - num z₀) * ((3 / 2 : ℝ) * Q_fn t) ^ (-(1 / 3 : ℝ)) +
        (-num z₀) * (((3 / 2 : ℝ) * Q_fn t) ^ (-(1 / 3 : ℝ)) - ((3 / 2 : ℝ) * Q_fn 0) ^ (-(1 / 3 : ℝ))) := by ring
    rw [hsplit]
    calc |-(num (z_fn t) - num z₀) * ((3 / 2 : ℝ) * Q_fn t) ^ (-(1 / 3 : ℝ)) +
            (-num z₀) * (((3 / 2 : ℝ) * Q_fn t) ^ (-(1 / 3 : ℝ)) - ((3 / 2 : ℝ) * Q_fn 0) ^ (-(1 / 3 : ℝ)))|
        ≤ |-(num (z_fn t) - num z₀)| * |((3 / 2 : ℝ) * Q_fn t) ^ (-(1 / 3 : ℝ))| +
          |-num z₀| * |((3 / 2 : ℝ) * Q_fn t) ^ (-(1 / 3 : ℝ)) - ((3 / 2 : ℝ) * Q_fn 0) ^ (-(1 / 3 : ℝ))| :=
            (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
      _ = |num (z_fn t) - num z₀| * ((3 / 2 : ℝ) * Q_fn t) ^ (-(1 / 3 : ℝ)) +
          |num z₀| * |((3 / 2 : ℝ) * Q_fn t) ^ (-(1 / 3 : ℝ)) - ((3 / 2 : ℝ) * Q_fn 0) ^ (-(1 / 3 : ℝ))| := by
            rw [abs_neg, abs_neg, abs_of_pos (Real.rpow_pos_of_pos (by linarith [hQ_pos t ht]) _)]
      _ ≤ (M_nump * t) * M_Q3 + (|ctTheta1 ε| + r₀ * Bθ0) * ((1 / 2 : ℝ) * M_Qp * M_Q4 * t) := by
            have hM3_nn : 0 ≤ M_Q3 := by dsimp only [M_Q3]; positivity
            exact add_le_add
              (mul_le_mul hnum_mv hq3_t (Real.rpow_pos_of_pos (by linarith [hQ_pos t ht]) _).le (mul_nonneg (by positivity) ht.1))
              (mul_le_mul hnum0_bd hq3_mv (abs_nonneg _) (by positivity))
      _ = C_sec * t := by ring
  -- Integrate `|a'(t) - a'(0)| ≤ C_sec * t` over `[0, s]` via monotonicity
  let f_hi : ℝ → ℝ := fun t => a_fn t - a_fn 0 - t * ap_fn 0 - (C_sec / 2) * t ^ 2
  let f_lo : ℝ → ℝ := fun t => a_fn t - a_fn 0 - t * ap_fn 0 + (C_sec / 2) * t ^ 2
  have hf_hi_d : ∀ t ∈ Ioo (0 : ℝ) s, HasDerivWithinAt f_hi (ap_fn t - ap_fn 0 - C_sec * t) (Ioo 0 s) t := fun t ht =>
    (((((ha_deriv t ⟨ht.1.le, ht.2.le⟩).sub (hasDerivWithinAt_const t (Icc 0 s) (a_fn 0))).sub
      ((hasDerivWithinAt_id t (Icc 0 s)).mul_const (ap_fn 0))).sub
      (((hasDerivWithinAt_id t (Icc 0 s)).pow 2).const_mul (C_sec / 2))).congr_deriv (by simp [id]; ring)).mono Ioo_subset_Icc_self
  have hf_lo_d : ∀ t ∈ Ioo (0 : ℝ) s, HasDerivWithinAt f_lo (ap_fn t - ap_fn 0 + C_sec * t) (Ioo 0 s) t := fun t ht =>
    (((((ha_deriv t ⟨ht.1.le, ht.2.le⟩).sub (hasDerivWithinAt_const t (Icc 0 s) (a_fn 0))).sub
      ((hasDerivWithinAt_id t (Icc 0 s)).mul_const (ap_fn 0))).add
      (((hasDerivWithinAt_id t (Icc 0 s)).pow 2).const_mul (C_sec / 2))).congr_deriv (by simp [id]; ring)).mono Ioo_subset_Icc_self
  have hf_hi_anti : AntitoneOn f_hi (Icc 0 s) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => ap_fn t - ap_fn 0 - C_sec * t) (convex_Icc 0 s)
      (fun t ht => (ha_deriv t ht).continuousWithinAt.sub continuousWithinAt_const |>.sub
        (continuousWithinAt_id.mul continuousWithinAt_const) |>.sub (continuousWithinAt_const.mul (continuousWithinAt_id.pow 2)))
      (fun t ht => by rw [interior_Icc] at ht ⊢; exact hf_hi_d t ht) fun t ht => by
        rw [interior_Icc] at ht
        have hle : ap_fn t - ap_fn 0 ≤ C_sec * t := (abs_le.mp (hap_lip t ⟨ht.1.le, ht.2.le⟩)).2
        linarith
  have hf_lo_mono : MonotoneOn f_lo (Icc 0 s) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => ap_fn t - ap_fn 0 + C_sec * t) (convex_Icc 0 s)
      (fun t ht => (ha_deriv t ht).continuousWithinAt.sub continuousWithinAt_const |>.sub
        (continuousWithinAt_id.mul continuousWithinAt_const) |>.add (continuousWithinAt_const.mul (continuousWithinAt_id.pow 2)))
      (fun t ht => by rw [interior_Icc] at ht ⊢; exact hf_lo_d t ht) fun t ht => by
        rw [interior_Icc] at ht
        have hge : -(C_sec * t) ≤ ap_fn t - ap_fn 0 := (abs_le.mp (hap_lip t ⟨ht.1.le, ht.2.le⟩)).1
        linarith
  have hf_hi_s : f_hi s ≤ f_hi 0 := hf_hi_anti ⟨le_rfl, hs_nn⟩ ⟨hs_nn, le_rfl⟩ hs_nn
  have hf_lo_s : f_lo 0 ≤ f_lo s := hf_lo_mono ⟨le_rfl, hs_nn⟩ ⟨hs_nn, le_rfl⟩ hs_nn
  have hf_hi_0 : f_hi 0 = 0 := by simp [f_hi]
  have hf_lo_0 : f_lo 0 = 0 := by simp [f_lo]
  have ha_bd : |a_fn s - (a_fn 0 + s * ap_fn 0)| ≤ (C_sec / 2) * s ^ 2 := by
    rw [abs_le]
    constructor <;> dsimp only [f_hi, f_lo] at hf_hi_s hf_lo_s hf_hi_0 hf_lo_0 <;> linarith
  have hf_z0 : 0 < fF z₀ := by
    have hle := (hz_mem_rho1 hz₀_pos.le (by linarith [hz₀_le])).2.2
    have hpi := sq_pos_of_pos Real.pi_pos
    linarith
  have ha0_eq : a_fn 0 = z₀ * dF z₀ ^ 2 := by
    dsimp only [a_fn, fjAfold, fjQ]; unfold dF
    rw [hz_fn_0, zero_mul, add_zero, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    norm_num
  have hap0_eq : ap_fn 0 = -(outerTheta ε (Real.sqrt z₀) / (Real.sqrt z₀ * dF z₀)) := by
    dsimp only [ap_fn, Q_fn, fjQ]; unfold dF
    rw [hz_fn_0, zero_mul, add_zero, hspecθ (Real.sqrt z₀)]
    have hsqz : Real.sqrt z₀ ^ 2 = z₀ := Real.sq_sqrt hz₀_pos.le
    have hsq_pos : 0 < Real.sqrt z₀ := Real.sqrt_pos.mpr hz₀_pos
    have hcube : Real.sqrt z₀ ^ 3 = Real.sqrt z₀ * z₀ := by rw [pow_succ', hsqz]
    rw [hcube, hsqz]
    change -(ctTheta1 ε + z₀ * θt z₀) / ((3 / 2 : ℝ) * fF z₀) ^ (1 / 3 : ℝ) =
      -((ctTheta1 ε * Real.sqrt z₀ + Real.sqrt z₀ * z₀ * θt z₀) / (Real.sqrt z₀ * ((3 / 2 : ℝ) * fF z₀) ^ (1 / 3 : ℝ)))
    have hden_ne : ((3 / 2 : ℝ) * fF z₀) ^ (1 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
    field_simp [hsq_pos.ne', hden_ne]
  dsimp only [θt_def]
  rw [← hz_fn_s]
  change |a_fn s - (z₀ * dF z₀ ^ 2 + s * -(outerTheta ε √z₀ / (√z₀ * dF z₀)))| ≤ (C_sec / 2 + 1) * s ^ 2
  rw [← ha0_eq, ← hap0_eq]
  exact ha_bd.trans (by nlinarith [sq_nonneg s])

end FoldFJ

/-- info: 'FormalResearch.SignUncertainty.fj_fold_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fj_fold_taylor

end FormalResearch.SignUncertainty
