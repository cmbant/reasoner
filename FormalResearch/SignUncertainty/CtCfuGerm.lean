module

public import FormalResearch.SignUncertainty.CtCfuSeries
public import FormalResearch.SignUncertainty.HankelEdgePhase
public import FormalResearch.SignUncertainty.CtOuterDefs
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Smooth germs of the dispersion `m(τ) = τ² n(τ²)` and of `∫₀^τ m = τ³ ñ(τ²)`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 2 (`m(τ) = τ² n(τ²)`, `∫₀^τ m = τ³ ñ(τ²)`).
**Proved.**  With `m = hankelEdgeM`:

* `m'(u) = u k(u²)` where `k(y) = π² S_3(π²y)/S_1(π²y)` (smooth on `|y| < 1/π²`);
* `n(z) = ½ ∫₀¹ k(tz) dt`, `ñ(z) = ∫₀¹ s² n(zs²) ds` are `C^∞` on `|z| < 1/π²`;
* `m(τ) = τ² n(τ²)` and `∫₀^τ m = τ³ ñ(τ²)` for `0 ≤ τ² < 1/π²`;
* `n(0) = π²/12`, `n'(0) = -7π⁴/1440`, `ñ(0) = n(0)/3`, `ñ'(0) = n'(0)/5`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtCfu

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The radius `1/π²` of the germ domain. -/
noncomputable def rr : ℝ := 1 / π ^ 2

lemma rr_pos : 0 < rr := by unfold rr; positivity

/-- `k(y) = π² S_3(π² y) / S_1(π² y)`, so that `m'(u) = u k(u²)`. -/
noncomputable def kfun (y : ℝ) : ℝ := π ^ 2 * Sser 3 (π ^ 2 * y) / Sser 1 (π ^ 2 * y)

lemma abs_pi_sq_mul_le {y : ℝ} (hy : y ∈ Icc (-rr) rr) : |π ^ 2 * y| ≤ 1 := by
  have hp : 0 < π ^ 2 := by positivity
  rw [abs_mul, abs_of_pos hp]
  have : |y| ≤ rr := abs_le.mpr hy
  calc π ^ 2 * |y| ≤ π ^ 2 * rr := mul_le_mul_of_nonneg_left this hp.le
    _ = 1 := by unfold rr; field_simp

lemma Sser1_pos {y : ℝ} (hy : y ∈ Icc (-rr) rr) : 0 < Sser 1 (π ^ 2 * y) :=
  lt_of_lt_of_le (by norm_num) (Sser1_ge (abs_pi_sq_mul_le hy))

lemma contDiffOn_kfun : ContDiffOn ℝ ∞' kfun (Ioo (-rr) rr) := by
  unfold kfun
  have h3 : ContDiff ℝ ∞' (fun y : ℝ => Sser 3 (π ^ 2 * y)) :=
    ((contDiff_Sser 3).of_le (by exact_mod_cast le_top)).comp (contDiff_const.mul contDiff_id)
  have h1 : ContDiff ℝ ∞' (fun y : ℝ => Sser 1 (π ^ 2 * y)) :=
    ((contDiff_Sser 1).of_le (by exact_mod_cast le_top)).comp (contDiff_const.mul contDiff_id)
  refine (contDiff_const.mul h3).contDiffOn.div h1.contDiffOn (fun y hy => ?_)
  exact (Sser1_pos (Ioo_subset_Icc_self hy)).ne'

lemma kfun_zero : kfun 0 = π ^ 2 / 6 := by
  unfold kfun
  simp [Sser_zero, Nat.factorial]
  ring

lemma hasDerivAt_kfun_zero : HasDerivAt kfun (-(7 * π ^ 4 / 360)) 0 := by
  have hl : HasDerivAt (fun y : ℝ => π ^ 2 * y) (π ^ 2) 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_mul (π ^ 2)
  have hS : ∀ a : ℕ, HasDerivAt (fun y : ℝ => Sser a (π ^ 2 * y)) (π ^ 2 * (1 / ((a + 2).factorial : ℝ))) 0 := by
    intro a
    have hg : HasDerivAt (Sser a) (1 / ((a + 2).factorial : ℝ)) (π ^ 2 * 0) := by
      simpa using hasDerivAt_Sser_zero a
    have := hg.scomp 0 hl
    exact this.congr_deriv (by simp [mul_comm])
  have h3 := hS 3
  have h1 := hS 1
  have hq := ((h3.const_mul (π ^ 2))).div h1 (by simp [Sser_zero])
  exact hq.congr_deriv (by simp [Sser_zero, Nat.factorial]; ring)

/-- `n(z) = ½ ∫₀¹ k(tz) dt`. -/
noncomputable def nfun (z : ℝ) : ℝ := (1 / 2) * ∫ t in (0 : ℝ)..1, kfun (t * z)

/-- `ñ(z) = ∫₀¹ s² n(z s²) ds`. -/
noncomputable def ntil (z : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, s ^ 2 * nfun (z * s ^ 2)

lemma contDiffOn_nfun : ContDiffOn ℝ ∞' nfun (Ioo (-rr) rr) := by
  unfold nfun
  refine contDiffOn_const.mul (ContDiffOn.parametric_intervalIntegral (f := fun z t => kfun (t * z)) isOpen_Ioo ?_)
  have hmap : MapsTo (fun p : ℝ × ℝ => p.2 * p.1) (Ioo (-rr) rr ×ˢ [[(0 : ℝ), 1]]) (Ioo (-rr) rr) := by
    intro p hp
    have ht : p.2 ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using hp.2
    have hz := hp.1
    have h1 : |p.2 * p.1| ≤ |p.1| := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (abs_nonneg _) ht.2
    have : |p.1| < rr := abs_lt.mpr hz
    exact abs_lt.mp (lt_of_le_of_lt h1 this)
  exact contDiffOn_kfun.comp (by fun_prop : ContDiff ℝ ∞' fun p : ℝ × ℝ => p.2 * p.1).contDiffOn hmap

lemma contDiffOn_ntil : ContDiffOn ℝ ∞' ntil (Ioo (-rr) rr) := by
  unfold ntil
  refine ContDiffOn.parametric_intervalIntegral (f := fun z s => s ^ 2 * nfun (z * s ^ 2)) isOpen_Ioo ?_
  have hmap : MapsTo (fun p : ℝ × ℝ => p.1 * p.2 ^ 2) (Ioo (-rr) rr ×ˢ [[(0 : ℝ), 1]]) (Ioo (-rr) rr) := by
    intro p hp
    have ht : p.2 ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using hp.2
    have hz := hp.1
    have h1 : |p.1 * p.2 ^ 2| ≤ |p.1| := by
      rw [abs_mul, abs_pow, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ ht.1 ht.2)
    have : |p.1| < rr := abs_lt.mpr hz
    exact abs_lt.mp (lt_of_le_of_lt h1 this)
  exact (contDiff_snd.pow 2).contDiffOn.mul
    (contDiffOn_nfun.comp (by fun_prop : ContDiff ℝ ∞' fun p : ℝ × ℝ => p.1 * p.2 ^ 2).contDiffOn hmap)

/-- Differentiation at `0` of `z ↦ ∫₀¹ w(t) G(φ(t) z) dt`. -/
lemma hasDerivAt_param0 {G : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hG : ContDiffOn ℝ ∞' G (Ioo (-δ) δ))
    {w φ : ℝ → ℝ} (hw : Continuous w) (hφ : Continuous φ) (hφ01 : ∀ t ∈ Icc (0 : ℝ) 1, φ t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun z => ∫ t in (0 : ℝ)..1, w t * G (φ t * z)) ((∫ t in (0 : ℝ)..1, w t * φ t) * deriv G 0) 0 := by
  have hGc : ContinuousOn G (Ioo (-δ) δ) := hG.continuousOn
  have hG' : ContinuousOn (deriv G) (Ioo (-δ) δ) :=
    hG.continuousOn_deriv_of_isOpen isOpen_Ioo (by exact_mod_cast le_top)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -(δ / 2)) (b := δ / 2)).exists_bound_of_continuousOn
    (hG'.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  obtain ⟨W, hW⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hw.continuousOn
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Ioo (-(δ / 2)) (δ / 2), φ t * z ∈ Ioo (-δ) δ := by
    intro t ht z hz
    have h1 := hφ01 t ht
    have h2 : |φ t * z| ≤ |z| := by
      rw [abs_mul, abs_of_nonneg h1.1]; exact mul_le_of_le_one_left (abs_nonneg _) h1.2
    have : |z| < δ / 2 := abs_lt.mpr hz
    exact abs_lt.mp (by linarith)
  have hfin := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := (0 : ℝ)) (b := 1)
    (F := fun z t => w t * G (φ t * z)) (F' := fun z t => w t * (φ t * deriv G (φ t * z)))
    (x₀ := 0) (s := Ioo (-(δ / 2)) (δ / 2)) (bound := fun _ => W * M) (Ioo_mem_nhds (by linarith) (by linarith))
    ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · have := hfin.2
    convert this using 1
    simp only [mul_zero]
    have : ∫ t in (0 : ℝ)..1, w t * (φ t * deriv G 0) = (∫ t in (0 : ℝ)..1, w t * φ t) * deriv G 0 := by
      rw [← intervalIntegral.integral_mul_const]; refine intervalIntegral.integral_congr fun t _ => ?_; show _ = _; ring
    exact this.symm
  · filter_upwards [Ioo_mem_nhds (show -(δ / 2) < 0 by linarith) (show (0 : ℝ) < δ / 2 by linarith)] with z hz
    rw [uIoc_of_le zero_le_one]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact hw.continuousOn.mul (hGc.comp (hφ.mul continuous_const).continuousOn
      (fun t ht => hmem t (Ioc_subset_Icc_self ht) z hz))
  · exact (Continuous.intervalIntegrable (by
      have : Continuous fun t : ℝ => w t * G (φ t * 0) := by
        simp only [mul_zero]; exact hw.mul continuous_const
      exact this) 0 1)
  · rw [uIoc_of_le zero_le_one]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    simp only [mul_zero]
    exact (hw.mul (hφ.mul continuous_const)).continuousOn
  · refine Eventually.of_forall fun t ht z hz => ?_
    rw [uIoc_of_le zero_le_one] at ht
    have h1 := hφ01 t (Ioc_subset_Icc_self ht)
    have hz' := hmem t (Ioc_subset_Icc_self ht) z hz
    rw [norm_mul, norm_mul]
    have hb1 : ‖w t‖ ≤ W := hW t (Ioc_subset_Icc_self ht)
    have hb2 : ‖deriv G (φ t * z)‖ ≤ M := by
      refine hM _ ⟨?_, ?_⟩ <;> [skip; skip]
      · have h2 : |φ t * z| ≤ |z| := by
          rw [abs_mul, abs_of_nonneg h1.1]; exact mul_le_of_le_one_left (abs_nonneg _) h1.2
        have : |z| < δ / 2 := abs_lt.mpr hz
        linarith [(abs_le.mp h2).1]
      · have h2 : |φ t * z| ≤ |z| := by
          rw [abs_mul, abs_of_nonneg h1.1]; exact mul_le_of_le_one_left (abs_nonneg _) h1.2
        have : |z| < δ / 2 := abs_lt.mpr hz
        linarith [(abs_le.mp h2).2]
    have hφn : ‖φ t‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h1.1]; exact h1.2
    calc ‖w t‖ * (‖φ t‖ * ‖deriv G (φ t * z)‖) ≤ W * (1 * M) :=
          mul_le_mul hb1 (mul_le_mul hφn hb2 (norm_nonneg _) zero_le_one) (by positivity)
            ((norm_nonneg _).trans hb1)
      _ = W * M := by ring
  · refine Eventually.of_forall fun t ht z hz => ?_
    rw [uIoc_of_le zero_le_one] at ht
    have hz' := hmem t (Ioc_subset_Icc_self ht) z hz
    have hdiff : DifferentiableAt ℝ G (φ t * z) :=
      (hG.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hz')
    have h1 : HasDerivAt (fun z : ℝ => φ t * z) (φ t) z := by simpa using (hasDerivAt_id' z).const_mul (φ t)
    have h2 := hdiff.hasDerivAt.scomp z h1
    have h3 := h2.const_mul (w t)
    refine h3.congr_deriv ?_
    simp [mul_comm]

lemma nfun_zero : nfun 0 = π ^ 2 / 12 := by
  unfold nfun
  simp [kfun_zero]
  ring

lemma hasDerivAt_nfun_zero : HasDerivAt nfun (-(7 * π ^ 4 / 1440)) 0 := by
  have h := hasDerivAt_param0 rr_pos contDiffOn_kfun (w := fun _ => (1 : ℝ)) (φ := fun t => t) continuous_const
    continuous_id (fun t ht => ht)
  have h2 := h.const_mul (1 / 2 : ℝ)
  have e : nfun = fun z => 1 / 2 * ∫ t in (0 : ℝ)..1, 1 * kfun (t * z) := by
    funext z; unfold nfun; simp
  rw [e]
  refine h2.congr_deriv ?_
  rw [hasDerivAt_kfun_zero.deriv]
  simp
  ring

lemma ntil_zero : ntil 0 = π ^ 2 / 36 := by
  unfold ntil
  simp [nfun_zero]
  ring

lemma hasDerivAt_ntil_zero : HasDerivAt ntil (-(7 * π ^ 4 / 7200)) 0 := by
  have h := hasDerivAt_param0 rr_pos contDiffOn_nfun (w := fun s => s ^ 2) (φ := fun s => s ^ 2) (by fun_prop)
    (by fun_prop) (fun t ht => ⟨by positivity, pow_le_one₀ ht.1 ht.2⟩)
  have e : ntil = fun z => ∫ s in (0 : ℝ)..1, s ^ 2 * nfun (s ^ 2 * z) := by
    funext z; unfold ntil; refine intervalIntegral.integral_congr fun s _ => ?_; simp only [mul_comm]
  rw [e]
  refine h.congr_deriv ?_
  rw [hasDerivAt_nfun_zero.deriv]
  have : ∫ t in (0 : ℝ)..1, t ^ 2 * t ^ 2 = 1 / 5 := by
    simp only [← pow_add]; rw [integral_pow]; norm_num
  rw [this]; ring

lemma hankelEdgeM'_eq {u : ℝ} (hu : 0 < u) (hu2 : u ^ 2 < rr) : hankelEdgeM' u = u * kfun (u ^ 2) := by
  rw [← CtOuter.mPrime_eq_hankelEdgeM' hu]
  unfold CtOuter.mPrime kfun
  have hy : u ^ 2 ∈ Icc (-rr) rr := ⟨by nlinarith [rr_pos, sq_nonneg u], hu2.le⟩
  have hS1 : 0 < Sser 1 (π ^ 2 * u ^ 2) := Sser1_pos hy
  have hsinh := Sser1_sq (π * u)
  have hsq : (π * u) ^ 2 = π ^ 2 * u ^ 2 := by ring
  rw [hsq] at hsinh
  have hS : Sser 1 (π ^ 2 * u ^ 2) = 1 + π ^ 2 * u ^ 2 * Sser 3 (π ^ 2 * u ^ 2) := by
    have := Sser_succ 1 (π ^ 2 * u ^ 2)
    simpa using this
  have hπu : (π * u) ≠ 0 := by positivity
  have hsh : Real.sinh (π * u) = Sser 1 (π ^ 2 * u ^ 2) * (π * u) := hsinh.symm
  rw [hsh]
  generalize Sser 3 (π ^ 2 * u ^ 2) = S3 at hS ⊢
  generalize Sser 1 (π ^ 2 * u ^ 2) = S1 at hS hS1 ⊢
  subst hS
  have hu0 : u ≠ 0 := hu.ne'
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have hne := hS1.ne'
  have hne' : 1 + u ^ 2 * π ^ 2 * S3 ≠ 0 := by
    intro h; apply hne; linarith [h, (by ring : π ^ 2 * u ^ 2 * S3 = u ^ 2 * π ^ 2 * S3)]
  field_simp
  ring

lemma sq_mem_Ioo {τ : ℝ} (hτ2 : τ ^ 2 < rr) : τ ^ 2 ∈ Ioo (-rr) rr :=
  ⟨by nlinarith [rr_pos, sq_nonneg τ], hτ2⟩

lemma hankelEdgeM_eq {τ : ℝ} (hτ : 0 ≤ τ) (hτ2 : τ ^ 2 < rr) : hankelEdgeM τ = τ ^ 2 * nfun (τ ^ 2) := by
  rcases hτ.eq_or_lt with h | hτ'
  · subst h; simp [hankelEdgeM_zero]
  have hcont : ContinuousOn hankelEdgeM (Icc 0 τ) := hankelEdgeM_continuousOn.mono Icc_subset_Ici_self
  have hderiv : ∀ u ∈ Ioo 0 τ, HasDerivAt hankelEdgeM (u * kfun (u ^ 2)) u := by
    intro u hu
    refine (hankelEdgeM_hasDerivAt hu.1).congr_deriv (hankelEdgeM'_eq hu.1 ?_)
    nlinarith [hu.2, hu.1]
  have hkc : ContinuousOn kfun (Icc 0 (τ ^ 2)) :=
    contDiffOn_kfun.continuousOn.mono (fun y hy => ⟨by linarith [hy.1, rr_pos], lt_of_le_of_lt hy.2 hτ2⟩)
  have hint : IntervalIntegrable (fun u : ℝ => u * kfun (u ^ 2)) volume 0 τ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hτ]
    exact continuousOn_id.mul (hkc.comp (continuousOn_id.pow 2) (fun u hu => ⟨by positivity, by nlinarith [hu.2, hu.1]⟩))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ hcont hderiv hint
  rw [hankelEdgeM_zero, sub_zero] at hftc
  have hsub := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := τ) (f := fun u : ℝ => u ^ 2)
    (f' := fun u => 2 * u) (g := kfun) (fun x _ => by simpa using hasDerivAt_pow 2 x)
    (by fun_prop) (by
      rw [uIcc_of_le hτ]
      refine hkc.mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨by positivity, by nlinarith [hx.2, hx.1]⟩)
  simp only [Function.comp, zero_pow two_ne_zero] at hsub
  have hτsq : τ ^ 2 ≠ 0 := by positivity
  have hnf : nfun (τ ^ 2) = (1 / 2) * ((τ ^ 2)⁻¹ * ∫ x in (0 : ℝ)..τ ^ 2, kfun x) := by
    unfold nfun
    have := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) kfun (c := τ ^ 2) hτsq
    simp only [mul_zero, mul_one, smul_eq_mul] at this
    have hfun : (fun t : ℝ => kfun (t * τ ^ 2)) = fun t => kfun (τ ^ 2 * t) := by
      funext t; rw [mul_comm]
    rw [hfun, this]
  rw [← hftc, hnf]
  have : ∫ x in (0 : ℝ)..τ, kfun (x ^ 2) * (2 * x) = ∫ x in (0 : ℝ)..τ, 2 * (x * kfun (x ^ 2)) := by
    refine intervalIntegral.integral_congr fun x _ => ?_; show _ = _; ring
  rw [this, intervalIntegral.integral_const_mul] at hsub
  field_simp
  linarith

lemma integral_hankelEdgeM_eq {τ : ℝ} (hτ : 0 ≤ τ) (hτ2 : τ ^ 2 < rr) :
    ∫ u in (0 : ℝ)..τ, hankelEdgeM u = τ ^ 3 * ntil (τ ^ 2) := by
  rcases hτ.eq_or_lt with h | hτ'
  · subst h; simp
  have hcongr : ∫ u in (0 : ℝ)..τ, hankelEdgeM u = ∫ u in (0 : ℝ)..τ, u ^ 2 * nfun (u ^ 2) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hτ] at hu
    exact hankelEdgeM_eq hu.1 (by nlinarith [hu.2, hu.1])
  rw [hcongr]
  have := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (fun u : ℝ => u ^ 2 * nfun (u ^ 2)) (c := τ) hτ'.ne'
  simp only [mul_zero, mul_one, smul_eq_mul] at this
  have hτ0 : τ ≠ 0 := hτ'.ne'
  have h2 : ∫ u in (0 : ℝ)..τ, u ^ 2 * nfun (u ^ 2) =
      τ * ∫ x in (0 : ℝ)..1, (τ * x) ^ 2 * nfun ((τ * x) ^ 2) := by
    rw [this]; field_simp
  rw [h2]
  unfold ntil
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  show τ * ((τ * x) ^ 2 * nfun ((τ * x) ^ 2)) = τ ^ 3 * (x ^ 2 * nfun (τ ^ 2 * x ^ 2))
  rw [show (τ * x) ^ 2 = τ ^ 2 * x ^ 2 by ring]
  ring

end FormalResearch.SignUncertainty.CtCfu
