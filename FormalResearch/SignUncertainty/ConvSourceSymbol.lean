module

public import Mathlib
public import FormalResearch.SignUncertainty.ConvSourceLaplace
public import FormalResearch.SignUncertainty.ConvSourceWeight

/-!
# Laplace-transform moments of the weight `w_h` (M6, Lemma `O.12(4)`, `ceo:conv.5`)

For a weight `w` integrable on `(0, ∞)` and `Re z > 0`, the `k`-th moment transform
`convSD w k z = ∫₀^∞ w(y) (-y)^k e^{-zy} dy` is the `k`-th complex derivative of `lapW w`
(`convSD_zero`, `convSD_hasDerivAt`). On the line `z = δ + iq` this is `∂_q^k` of the transform up to
the unimodular factor `i^k`, which is the integral `∫ (-iy)^k w(y) e^{-(δ+iq)y} dy` of the TeX.

* `convSD_zero`, `convSD_hasDerivAt`: `convSD w 0 = lapW w` and
  `HasDerivAt (convSD w k) (convSD w (k+1) z) z` for `Re z > 0` and any `w` integrable on `(0, ∞)`
  (class: proved).
* `convWh_contDiff`: `w_h` is `C^∞` on `ℝ` for `h > 0` (class: proved).
* `convS_lapW_exp`: the Laplace transform of the exponential term `γ ε e^{-y}` (class: proved).
* `convS_lapW_norm_le`: `‖lapW w_h z‖ ≤ 2` for `Re z ≥ 0`, uniformly in `h > 0` (class: proved).
* `convS_lapW_sub_le`: `‖lapW w_h z - ∫ w_h‖ ≤ 6 ‖z‖^{1/2}` for `Re z > 0`, `‖z‖ ≤ 1`, uniformly in
  `h > 0` (class: proved).

The decay bounds for the moments `k ≥ 1` are in `ConvSourceSymbolIBP` (abstract integration by
parts) and `ConvSourceSymbolBounds` (the assembly `convS_bounds`, for `k = 1, 2, 3`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- The `k`-th moment transform `∫₀^∞ w(y) (-y)^k e^{-zy} dy`; for `Re z > 0` it is the `k`-th
complex derivative of `lapW w` (`convSD_hasDerivAt`). -/
noncomputable def convSD (w : ℝ → ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), (w y : ℂ) * (-(y : ℂ)) ^ k * Complex.exp (-(z * (y : ℂ)))

/-- The `0`-th moment transform is the Laplace transform `lapW`. -/
lemma convSD_zero (w : ℝ → ℝ) : convSD w 0 = lapW w := by
  funext z
  simp [convSD, lapW]

/-- `t^n e^{-δ t} ≤ n!/δ^n` for `δ > 0`, `t ≥ 0`. -/
lemma convS_pow_mul_exp_le {δ : ℝ} (hδ : 0 < δ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ n * Real.exp (-(δ * t)) ≤ (n.factorial : ℝ) / δ ^ n := by
  have hx : 0 ≤ δ * t := mul_nonneg hδ.le ht
  have h1 := Real.pow_div_factorial_le_exp _ hx n
  rw [div_le_iff₀ (by positivity)] at h1
  rw [le_div_iff₀ (pow_pos hδ n)]
  calc t ^ n * Real.exp (-(δ * t)) * δ ^ n = (δ * t) ^ n * Real.exp (-(δ * t)) := by
        rw [mul_pow]; ring
    _ ≤ Real.exp (δ * t) * n.factorial * Real.exp (-(δ * t)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ = n.factorial := by
        rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- The norm of the `k`-th moment integrand at a point `y > 0`. -/
lemma convS_norm_term (z : ℂ) (k : ℕ) (w : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖(w : ℂ) * (-(y : ℂ)) ^ k * Complex.exp (-(z * (y : ℂ)))‖
      = |w| * (y ^ k * Real.exp (-(z.re * y))) := by
  have hre : (-(z * (y : ℂ))).re = -(z.re * y) := by simp [Complex.mul_re]
  simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Complex.norm_exp, hre,
    Real.norm_eq_abs, abs_of_pos hy]
  ring

lemma convS_aesm {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) (k : ℕ) (z : ℂ) :
    AEStronglyMeasurable (fun y : ℝ => (w y : ℂ) * (-(y : ℂ)) ^ k * Complex.exp (-(z * (y : ℂ))))
      (volume.restrict (Ioi (0 : ℝ))) :=
  ((integrableOn_ofReal_weight hw).1.mul
    (by fun_prop : Continuous fun y : ℝ => (-(y : ℂ)) ^ k).aestronglyMeasurable).mul
    (by fun_prop : Continuous fun y : ℝ => Complex.exp (-(z * (y : ℂ)))).aestronglyMeasurable

lemma convS_integrableOn {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) (k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun y : ℝ => (w y : ℂ) * (-(y : ℂ)) ^ k * Complex.exp (-(z * (y : ℂ)))) (Ioi 0) := by
  refine (hw.norm.mul_const ((k.factorial : ℝ) / z.re ^ k)).mono' (convS_aesm hw k z) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
  have hy' : (0 : ℝ) < y := hy
  rw [convS_norm_term z k (w y) hy', Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (convS_pow_mul_exp_le hz k hy'.le) (abs_nonneg _)

/-- (i) The moment transforms are the successive derivatives of `lapW`: for `Re z₀ > 0`,
`∂_z convSD w k = convSD w (k+1)`. -/
theorem convSD_hasDerivAt {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) (k : ℕ) {z₀ : ℂ}
    (hz₀ : 0 < z₀.re) :
    HasDerivAt (convSD w k) (convSD w (k + 1) z₀) z₀ := by
  unfold convSD
  set δ : ℝ := z₀.re / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hs : {z : ℂ | δ < z.re} ∈ 𝓝 z₀ :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simp only [Set.mem_ofPred_eq, hδ]; linarith)
  refine (hasDerivAt_integral_Ioi
    (F := fun z y => (w y : ℂ) * (-(y : ℂ)) ^ k * Complex.exp (-(z * (y : ℂ))))
    (F' := fun z y => (w y : ℂ) * (-(y : ℂ)) ^ (k + 1) * Complex.exp (-(z * (y : ℂ))))
    hs (bound := fun y => ‖w y‖ * (((k + 1).factorial : ℝ) / δ ^ (k + 1)))
    (Eventually.of_forall fun z => convS_aesm hw k z) (convS_integrableOn hw k hz₀)
    (convS_aesm hw (k + 1) z₀) ?_ (hw.norm.mul_const _) ?_).2
  · intro t ht y hy
    have ht0 : (0 : ℝ) < t := ht
    have hy' : δ < y.re := hy
    have hexp : Real.exp (-(y.re * t)) ≤ Real.exp (-(δ * t)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hb := convS_pow_mul_exp_le hδ0 (k + 1) ht0.le
    rw [convS_norm_term y (k + 1) (w t) ht0, Real.norm_eq_abs]
    calc |w t| * (t ^ (k + 1) * Real.exp (-(y.re * t)))
        ≤ |w t| * (((k + 1).factorial : ℝ) / δ ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left
            ((mul_le_mul_of_nonneg_left hexp (pow_nonneg ht0.le _)).trans hb) (abs_nonneg _)
      _ = ‖w t‖ * (((k + 1).factorial : ℝ) / δ ^ (k + 1)) := by rw [Real.norm_eq_abs]
  · intro t ht z hz
    have h1 : HasDerivAt (fun y : ℂ => -(y * (t : ℂ))) (-(1 * (t : ℂ))) z :=
      ((hasDerivAt_id' z).mul_const (t : ℂ)).neg
    have h2 := (h1.cexp).const_mul ((w t : ℂ) * (-(t : ℂ)) ^ k)
    convert h2 using 1
    ring

/-- `w_h` is `C^∞` on `ℝ` for `h > 0`: it vanishes on `(-∞, 1)` and is a composition of smooth
maps on `[1, ∞)`. -/
lemma convWh_contDiff {p h : ℝ} (hh : 0 < h) : ContDiff ℝ (⊤ : ℕ∞) (convWh p h) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge x 1 with hx | hx
  · have hev : convWh p h =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (isOpen_Iio.mem_nhds hx) (fun y hy => convWh_eq_zero (le_of_lt hy))
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hpos : 0 < x := by linarith
    have hden : 0 < 1 + h * x := by have := mul_pos hh hpos; linarith
    have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => h * y / (1 + h * y)) x :=
      (contDiffAt_const.mul contDiffAt_id).div
        (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)) hden.ne'
    have hr : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => (h * y / (1 + h * y)) ^ p) x :=
      hg.rpow_const_of_ne (div_pos (mul_pos hh hpos) hden).ne'
    have hy : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => y ^ (3 / 2 : ℝ)) x :=
      Real.contDiffAt_rpow_const_of_ne hpos.ne'
    have he : ContDiffAt ℝ (⊤ : ℕ∞) convEta x := convEta_contDiff.contDiffAt
    unfold convWh convRho
    exact (he.mul hr).div hy (Real.rpow_pos_of_pos hpos _).ne'

/-- `Re w ≤ 0` gives `‖e^w - 1‖ ≤ ‖w‖` (mean value inequality along `s ↦ e^{sw}`). -/
lemma convS_exp_sub_one_le {ζ : ℂ} (hζ : ζ.re ≤ 0) : ‖Complex.exp ζ - 1‖ ≤ ‖ζ‖ := by
  have hd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => Complex.exp (s * ζ))
      (Complex.exp (s * ζ) * ζ) (Set.Icc (0 : ℝ) 1) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * ζ) ζ s := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const ζ)
    exact ((h1.cexp).hasDerivWithinAt)
  have hb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖Complex.exp (s * ζ) * ζ‖ ≤ ‖ζ‖ := by
    intro s hs
    have hre : (s * ζ).re ≤ 0 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      nlinarith [hs.1]
    rw [norm_mul]
    have : ‖Complex.exp (s * ζ)‖ ≤ 1 := by
      rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hre
    nlinarith [norm_nonneg ζ, norm_nonneg (Complex.exp (s * ζ))]
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc (0 : ℝ) 1)
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.ofReal_one, one_mul,
    sub_zero, Real.norm_eq_abs, abs_one, mul_one] at key
  exact key

/-- (iii) The Laplace transform of the exponential term: `lapW (γ ε e^{-y}) z = γ ε/(1+z)`. -/
lemma convS_lapW_exp (γ ε : ℝ) {z : ℂ} (hz : 0 < z.re) :
    lapW (fun y => γ * ε * Real.exp (-y)) z = ((γ * ε : ℝ) : ℂ) / (1 + z) := by
  have hne : (1 + z) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  have ha : (-(1 + z)).re < 0 := by simp; linarith
  have hint : ∀ y : ℝ, (((γ * ε * Real.exp (-y) : ℝ)) : ℂ) * Complex.exp (-(z * (y : ℂ)))
      = ((γ * ε : ℝ) : ℂ) * Complex.exp (-(1 + z) * (y : ℂ)) := by
    intro y
    have e : Complex.exp (-(1 + z) * (y : ℂ)) = Complex.exp (-(y : ℂ)) * Complex.exp (-(z * (y : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; ring
    push_cast
    rw [e]
    ring
  unfold lapW
  calc ∫ y in Ioi (0 : ℝ), (((γ * ε * Real.exp (-y) : ℝ)) : ℂ) * Complex.exp (-(z * (y : ℂ)))
      = ∫ y in Ioi (0 : ℝ), ((γ * ε : ℝ) : ℂ) * Complex.exp (-(1 + z) * (y : ℂ)) :=
        setIntegral_congr_fun measurableSet_Ioi (fun y _ => hint y)
    _ = ((γ * ε : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), Complex.exp (-(1 + z) * (y : ℂ)) :=
        integral_const_mul _ _
    _ = ((γ * ε : ℝ) : ℂ) / (1 + z) := by
        rw [integral_exp_mul_complex_Ioi ha 0]
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
        field_simp

/-- The `L¹` norm of `w_h` on `(0, ∞)` is at most `2`, uniformly in `h > 0`. -/
lemma convS_norm_integral_le {p h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h) :
    ∫ y in Ioi (0 : ℝ), ‖convWh p h y‖ ≤ 2 := by
  have hn : IntegrableOn (fun y : ℝ => ‖convWh p h y‖) (Ioi 0) := (convW_integrable hp hp1 hh).norm
  have hI : IntegrableOn (fun y : ℝ => y ^ (-(3 / 2 : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  have hsplit : ∫ y in Ioi (0 : ℝ), ‖convWh p h y‖
      = (∫ y in Ioc (0 : ℝ) 1, ‖convWh p h y‖) + ∫ y in Ioi (1 : ℝ), ‖convWh p h y‖ := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hn.mono_set Set.Ioc_subset_Ioi_self) (hn.mono_set (Ioi_subset_Ioi zero_le_one))]
  have hzero : ∫ y in Ioc (0 : ℝ) 1, ‖convWh p h y‖ = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero (fun y hy => ?_)
    rw [convWh_eq_zero hy.2, norm_zero]
  have htail : ∫ y in Ioi (1 : ℝ), ‖convWh p h y‖ ≤ ∫ y in Ioi (1 : ℝ), y ^ (-(3 / 2 : ℝ)) := by
    refine setIntegral_mono_on (hn.mono_set (Ioi_subset_Ioi zero_le_one)) hI measurableSet_Ioi
      (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := lt_trans zero_lt_one hy
    rw [Real.norm_of_nonneg (convWh_nonneg hh.le hy0)]
    exact convWh_le (by linarith) hh.le hy0
  have h2 : ∫ y in Ioi (1 : ℝ), y ^ (-(3 / 2 : ℝ)) = 2 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num [Real.one_rpow]
  rw [hsplit, hzero, zero_add]
  linarith

/-- (ii, `k`-independent part) `‖lapW w_h z‖ ≤ 2` for `Re z ≥ 0`, uniformly in `h > 0`. -/
theorem convS_lapW_norm_le {p h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h) {z : ℂ}
    (hz : 0 ≤ z.re) : ‖lapW (convWh p h) z‖ ≤ 2 :=
  (lapW_norm_le (convW_integrable hp hp1 hh) hz).trans (convS_norm_integral_le hp hp1 hh)

/-- Splitting `(0, ∞)` at `1` for an integrand vanishing on `(0, 1]`. -/
lemma convS_split_Ioi_one {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    (h0 : ∀ y : ℝ, 0 < y → y ≤ 1 → f y = 0) :
    ∫ y in Ioi (0 : ℝ), f y = ∫ y in Ioi (1 : ℝ), f y := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hf.mono_set Set.Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi zero_le_one))]
  rw [setIntegral_eq_zero_of_forall_eq_zero (fun y (hy : y ∈ Set.Ioc (0 : ℝ) 1) => h0 y hy.1 hy.2), zero_add]

/-- Integrability of the tail majorant `y^{-3/2} min(a y, 2)` on `(1, ∞)`. -/
lemma convS_tail_integrableOn {a : ℝ} (ha0 : 0 < a) :
    IntegrableOn (fun y : ℝ => y ^ (-(3 / 2 : ℝ)) * min (a * y) 2) (Ioi 1) := by
  have hI : IntegrableOn (fun y : ℝ => y ^ (-(3 / 2 : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  refine Integrable.mono' (Integrable.const_mul hI 2) ?_ ?_
  · exact (by fun_prop : Measurable fun y : ℝ => y ^ (-(3 / 2 : ℝ)) * min (a * y) 2).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := lt_trans zero_lt_one hy
    have hnn : 0 ≤ y ^ (-(3 / 2 : ℝ)) * min (a * y) 2 :=
      mul_nonneg (Real.rpow_nonneg hy0.le _) (le_min (mul_nonneg ha0.le hy0.le) (by norm_num))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    show _ ≤ 2 * y ^ (-(3 / 2 : ℝ))
    calc y ^ (-(3 / 2 : ℝ)) * min (a * y) 2 ≤ y ^ (-(3 / 2 : ℝ)) * 2 :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.rpow_nonneg hy0.le _)
      _ = 2 * y ^ (-(3 / 2 : ℝ)) := mul_comm _ _

/-- The tail estimate `∫_{(1,∞)} y^{-3/2} min(a y, 2) dy ≤ 6 √a` for `0 < a ≤ 1`
(the argument gives the constant `4√2 ≈ 5.66`). -/
lemma convS_tail_le {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∫ y in Ioi (1 : ℝ), y ^ (-(3 / 2 : ℝ)) * min (a * y) 2 ≤ 6 * a ^ (1 / 2 : ℝ) := by
  have hT2 : (2 : ℝ) ≤ 2 / a := by rw [le_div_iff₀ ha0]; linarith
  have hT1 : (1 : ℝ) ≤ 2 / a := by linarith
  have hT0 : (0 : ℝ) < 2 / a := by linarith
  have hf := convS_tail_integrableOn ha0
  have hI : IntegrableOn (fun y : ℝ => y ^ (-(3 / 2 : ℝ))) (Ioi (2 / a)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hT0
  have hsplit : ∫ y in Ioi (1 : ℝ), y ^ (-(3 / 2 : ℝ)) * min (a * y) 2
      = (∫ y in Ioc (1 : ℝ) (2 / a), y ^ (-(3 / 2 : ℝ)) * min (a * y) 2)
        + ∫ y in Ioi (2 / a), y ^ (-(3 / 2 : ℝ)) * min (a * y) 2 := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hT1,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hf.mono_set Set.Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hT1))]
  -- piece A: on (1, T], `min (a y, 2) ≤ a y`, so the integrand is at most `a y^{-1/2}`
  have hA1 : IntegrableOn (fun y : ℝ => a * y ^ (-(1 / 2 : ℝ))) (Ioc (1 : ℝ) (2 / a)) :=
    Integrable.const_mul
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT1).mp
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num))) a
  have hA : ∫ y in Ioc (1 : ℝ) (2 / a), y ^ (-(3 / 2 : ℝ)) * min (a * y) 2
      ≤ ∫ y in Ioc (1 : ℝ) (2 / a), a * y ^ (-(1 / 2 : ℝ)) := by
    refine setIntegral_mono_on (hf.mono_set (fun y hy => (show (1 : ℝ) < y from hy.1)))
      hA1 measurableSet_Ioc (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := lt_trans zero_lt_one hy.1
    have hpow : y ^ (-(1 / 2 : ℝ)) = y ^ (-(3 / 2 : ℝ)) * y := by
      rw [← Real.rpow_add_one hy0.ne']; norm_num
    calc y ^ (-(3 / 2 : ℝ)) * min (a * y) 2 ≤ y ^ (-(3 / 2 : ℝ)) * (a * y) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.rpow_nonneg hy0.le _)
      _ = a * y ^ (-(1 / 2 : ℝ)) := by rw [hpow]; ring
  -- piece B: on (T, ∞), `min (a y, 2) ≤ 2`
  have hB : ∫ y in Ioi (2 / a), y ^ (-(3 / 2 : ℝ)) * min (a * y) 2
      ≤ ∫ y in Ioi (2 / a), 2 * y ^ (-(3 / 2 : ℝ)) := by
    refine setIntegral_mono_on (hf.mono_set (Ioi_subset_Ioi hT1))
      (Integrable.const_mul hI 2) measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := lt_trans hT0 hy
    calc y ^ (-(3 / 2 : ℝ)) * min (a * y) 2 ≤ y ^ (-(3 / 2 : ℝ)) * 2 :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.rpow_nonneg hy0.le _)
      _ = 2 * y ^ (-(3 / 2 : ℝ)) := mul_comm _ _
  have hAval : ∫ y in Ioc (1 : ℝ) (2 / a), a * y ^ (-(1 / 2 : ℝ))
      = 2 * a * ((2 / a) ^ (1 / 2 : ℝ) - 1) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hT1,
      integral_rpow (Or.inl (by norm_num))]
    norm_num [Real.one_rpow]
    ring
  have hBval : ∫ y in Ioi (2 / a), 2 * y ^ (-(3 / 2 : ℝ)) = 4 * ((2 / a) ^ (1 / 2 : ℝ))⁻¹ := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT0]
    have e : (-(3 / 2 : ℝ) + 1) = -(1 / 2) := by norm_num
    rw [e, Real.rpow_neg hT0.le]
    ring
  rw [hsplit]
  rw [hAval] at hA
  rw [hBval] at hB
  -- algebra: with `s = √a`, `t = (2/a)^{1/2}`, `a t² = 2`, `(st)² = 2`
  set s : ℝ := a ^ (1 / 2 : ℝ) with hs
  set t : ℝ := (2 / a) ^ (1 / 2 : ℝ) with ht
  have hs0 : 0 < s := Real.rpow_pos_of_pos ha0 _
  have ht0 : 0 < t := Real.rpow_pos_of_pos hT0 _
  have hs2 : s ^ 2 = a := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]; norm_num
  have ht2 : t ^ 2 = 2 / a := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
  have key : a * t ^ 2 = 2 := by rw [ht2]; field_simp
  have hinv : t⁻¹ = a * t / 2 := by
    field_simp
    nlinarith [key]
  have hsq : (s * t) ^ 2 = 2 := by rw [mul_pow, hs2, ht2]; field_simp
  have hst : s * t ≤ 3 / 2 := by nlinarith [mul_pos hs0 ht0, hsq]
  have hat : a * t = s ^ 2 * t := by rw [hs2]
  nlinarith [mul_le_mul_of_nonneg_left hst hs0.le, hat, hinv, hA, hB, ha0]

/-- (ii, Hölder part) `‖lapW w_h z - ∫ w_h‖ ≤ 6 ‖z‖^{1/2}` for `Re z > 0`, `‖z‖ ≤ 1`, uniformly in
`h > 0`. -/
theorem convS_lapW_sub_le {p h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h) {z : ℂ}
    (hz : 0 < z.re) (hz1 : ‖z‖ ≤ 1) :
    ‖lapW (convWh p h) z - ∫ y in Ioi (0 : ℝ), convWh p h y‖ ≤ 6 * ‖z‖ ^ (1 / 2 : ℝ) := by
  have hw := convW_integrable hp hp1 hh
  have hwc := integrableOn_ofReal_weight hw
  have ha0 : 0 < ‖z‖ := lt_of_lt_of_le hz (Complex.re_le_norm z)
  have hc : lapW (convWh p h) z - ((∫ y in Ioi (0 : ℝ), convWh p h y : ℝ) : ℂ)
      = ∫ y in Ioi (0 : ℝ), (convWh p h y : ℂ) * (Complex.exp (-(z * (y : ℂ))) - 1) := by
    have hI : ∫ y in Ioi (0 : ℝ), (convWh p h y : ℂ)
        = ((∫ y in Ioi (0 : ℝ), convWh p h y : ℝ) : ℂ) := integral_ofReal
    unfold lapW
    rw [← hI, ← integral_sub (integrableOn_lapW hw hz.le) hwc]
    simp only [mul_sub, mul_one]
  have hg : IntegrableOn (fun y : ℝ => ‖convWh p h y‖ * min (‖z‖ * y) 2) (Ioi 0) := by
    refine Integrable.mono' (hw.norm.mul_const 2) ?_ ?_
    · exact hw.norm.aestronglyMeasurable.mul
        (by fun_prop : Continuous fun y : ℝ => min (‖z‖ * y) 2).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 : (0 : ℝ) < y := hy
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _)
        (le_min (mul_nonneg ha0.le hy0.le) (by norm_num)))]
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) (norm_nonneg _)
  have hpt : ∀ y ∈ Ioi (0 : ℝ), ‖(convWh p h y : ℂ) * (Complex.exp (-(z * (y : ℂ))) - 1)‖
      ≤ ‖convWh p h y‖ * min (‖z‖ * y) 2 := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    rw [norm_mul, Complex.norm_real]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    refine le_min ?_ ?_
    · have hre : (-(z * (y : ℂ))).re = -(z.re * y) := by simp [Complex.mul_re]
      have hle : (-(z * (y : ℂ))).re ≤ 0 := by rw [hre]; nlinarith
      calc ‖Complex.exp (-(z * (y : ℂ))) - 1‖ ≤ ‖-(z * (y : ℂ))‖ := convS_exp_sub_one_le hle
        _ = ‖z‖ * y := by rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hy0.le]
    · calc ‖Complex.exp (-(z * (y : ℂ))) - 1‖ ≤ ‖Complex.exp (-(z * (y : ℂ)))‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (norm_exp_neg_mul_le hz.le hy0.le) (by simp)
        _ = 2 := by norm_num
  have hJ := convS_tail_integrableOn ha0
  calc ‖lapW (convWh p h) z - ∫ y in Ioi (0 : ℝ), convWh p h y‖
      = ‖∫ y in Ioi (0 : ℝ), (convWh p h y : ℂ) * (Complex.exp (-(z * (y : ℂ))) - 1)‖ := by rw [hc]
    _ ≤ ∫ y in Ioi (0 : ℝ), ‖convWh p h y‖ * min (‖z‖ * y) 2 :=
        norm_integral_le_of_norm_le hg ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall fun y hy => hpt y hy))
    _ = ∫ y in Ioi (1 : ℝ), ‖convWh p h y‖ * min (‖z‖ * y) 2 :=
        convS_split_Ioi_one hg (fun y hy0 hy1 => by
          show ‖convWh p h y‖ * min (‖z‖ * y) 2 = 0
          rw [convWh_eq_zero hy1, norm_zero, zero_mul])
    _ ≤ ∫ y in Ioi (1 : ℝ), y ^ (-(3 / 2 : ℝ)) * min (‖z‖ * y) 2 := by
        refine setIntegral_mono_on (hg.mono_set (Ioi_subset_Ioi zero_le_one)) hJ measurableSet_Ioi
          (fun y hy => ?_)
        have hy0 : (0 : ℝ) < y := lt_trans zero_lt_one hy
        refine mul_le_mul_of_nonneg_right ?_ (le_min (mul_nonneg ha0.le hy0.le) (by norm_num))
        rw [Real.norm_of_nonneg (convWh_nonneg hh.le hy0)]
        exact convWh_le (by linarith) hh.le hy0
    _ ≤ 6 * ‖z‖ ^ (1 / 2 : ℝ) := convS_tail_le ha0 hz1

/-- info: 'FormalResearch.SignUncertainty.convSD_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convSD_hasDerivAt

/-- info: 'FormalResearch.SignUncertainty.convWh_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWh_contDiff

/-- info: 'FormalResearch.SignUncertainty.convS_exp_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_exp_sub_one_le

/-- info: 'FormalResearch.SignUncertainty.convS_lapW_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_lapW_exp

/-- info: 'FormalResearch.SignUncertainty.convS_lapW_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_lapW_norm_le

/-- info: 'FormalResearch.SignUncertainty.convS_lapW_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_lapW_sub_le

/-- info: 'FormalResearch.SignUncertainty.convS_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_tail_le

/-- info: 'FormalResearch.SignUncertainty.convSD_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convSD_zero

/-- info: 'FormalResearch.SignUncertainty.convS_pow_mul_exp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_pow_mul_exp_le

/-- info: 'FormalResearch.SignUncertainty.convS_norm_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_norm_term

/-- info: 'FormalResearch.SignUncertainty.convS_aesm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_aesm

/-- info: 'FormalResearch.SignUncertainty.convS_integrableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_integrableOn

/-- info: 'FormalResearch.SignUncertainty.convS_norm_integral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_norm_integral_le

/-- info: 'FormalResearch.SignUncertainty.convS_split_Ioi_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_split_Ioi_one

/-- info: 'FormalResearch.SignUncertainty.convS_tail_integrableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_tail_integrableOn

end FormalResearch.SignUncertainty
