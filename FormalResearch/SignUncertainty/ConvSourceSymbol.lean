module

public import Mathlib
public import FormalResearch.SignUncertainty.ConvSourceLaplace
public import FormalResearch.SignUncertainty.ConvSourceWeight

/-!
# Derivatives of the Laplace transform of the weight `w_h` (M6, Lemma `O.12(4)`, `ceo:conv.5`)

For a weight `w` integrable on `(0, ∞)` and `Re z > 0`, the `k`-th moment transform
`convSD w k z = ∫₀^∞ w(y) (-y)^k e^{-zy} dy` is the `k`-th complex derivative of `lapW w`.

* `convSD_hasDerivAt`: `HasDerivAt (convSD w k) (convSD w (k+1) z) z` for `Re z > 0` and any
  `w` integrable on `(0, ∞)` (class: proved).
* `convWh_contDiff`: `w_h` is `C^∞` on `ℝ` for `h > 0` (class: proved).
* `ConvWeightDerivBound p C`: the derivative bounds `(ceo:conv.4)` for `w_h` on `[1, ∞)`, as a
  hypothesis structure. Its `smooth` field is `convWh_contDiff`; its `deriv_le` field is the
  statement proved by `convW_deriv_bound` (another module). Non-vacuity: the bound is a true
  statement about `w_h` for a suitable `C` (the profile `(t/(1+t))^p` has `(t ∂_t)^r` bounded, and
  the cutoff derivatives are bounded on `[1, ∞)`), so the structure has the intended instance;
  this module does not construct that instance.
* `convS_lapW_exp`: the Laplace transform of the exponential term `γ ε e^{-y}` (class: proved).
* `convS_lapW_norm_le`: `‖lapW w_h z‖ ≤ 2` for `Re z ≥ 0`, uniformly in `h > 0` (class: proved).
* `convS_lapW_sub_le`: `‖lapW w_h z - ∫ w_h‖ ≤ 6 ‖z‖^{1/2}` for `Re z > 0`, `‖z‖ ≤ 1`, uniformly in
  `h > 0` (class: proved).
* `convS_k1_decay`: `‖∫ w_h(y) (-y) e^{-zy}‖ ≤ 2|C| ‖z‖^{-2}` for `Re z > 0`, uniformly in `h > 0`,
  from `ConvWeightDerivBound p C` by two integrations by parts (class: proved, conditional on the
  hypothesis structure).

Not in this module: the `k = 2, 3` bounds of `(ceo:conv.5)` and all `‖z‖ ≤ 1` bounds for `k ≥ 1`.
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
      (by simp only [mem_setOf_eq, hδ]; linarith)
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

/-- The derivative bounds of `w_h` on `[1, ∞)` (`ceo:conv.4`), uniform in `h > 0`, for the
derivative orders `r ≤ 4` used by the integration by parts. Instances are supplied by
`convW_deriv_bound`; the field `smooth` is `convWh_contDiff`. -/
structure ConvWeightDerivBound (p C : ℝ) : Prop where
  deriv_le : ∀ r : ℕ, r ≤ 4 → ∀ h : ℝ, 0 < h → ∀ y : ℝ, 1 ≤ y →
    |iteratedDeriv r (convWh p h) y| ≤ C * y ^ (-(3 / 2 : ℝ) - (r : ℝ))
  smooth : ∀ h : ℝ, 0 < h → ContDiff ℝ (⊤ : ℕ∞) (convWh p h)

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
  rw [setIntegral_eq_zero_of_forall_eq_zero (fun y hy => h0 y hy.1 hy.2), zero_add]

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
(the exact value of the bound is `4√2 √a`). -/
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

/-- (ii, `ζ`-Hölder part) `‖lapW w_h z - ∫ w_h‖ ≤ 6 ‖z‖^{1/2}` for `Re z > 0`, `‖z‖ ≤ 1`, uniformly in
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

/-- Decay of `G(y) e^{-zy}` at `∞` for a bounded `G` (`Re z > 0`). -/
lemma convS_tendsto_zero {G : ℝ → ℂ} {M : ℝ} {z : ℂ} (hz : 0 < z.re)
    (hG : ∀ y : ℝ, 1 ≤ y → ‖G y‖ ≤ M) :
    Tendsto (fun y : ℝ => G y * Complex.exp (-(z * (y : ℂ)))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => Real.exp (-(z.re * y))) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hz)
    simpa [Function.comp_def] using this
  have h2 : Tendsto (fun y : ℝ => M * Real.exp (-(z.re * y))) atTop (𝓝 0) := by
    simpa using h1.const_mul M
  refine squeeze_zero_norm' ?_ h2
  filter_upwards [eventually_ge_atTop 1] with y hy
  have hre : (-(z * (y : ℂ))).re = -(z.re * y) := by simp [Complex.mul_re]
  rw [norm_mul, Complex.norm_exp, hre]
  exact mul_le_mul_of_nonneg_right (hG y hy) (Real.exp_nonneg _)

/-- Integrability of `G(y) e^{-zy}` on `(0, ∞)` for a measurable, bounded `G`. -/
lemma convS_int_exp {G : ℝ → ℂ} {M : ℝ} {z : ℂ} (hz : 0 < z.re)
    (hGm : AEStronglyMeasurable G (volume.restrict (Ioi (0 : ℝ))))
    (hG : ∀ y : ℝ, 0 < y → ‖G y‖ ≤ M) :
    IntegrableOn (fun y : ℝ => G y * Complex.exp (-(z * (y : ℂ)))) (Ioi 0) := by
  have he : IntegrableOn (fun y : ℝ => Complex.exp (-(z * (y : ℂ)))) (Ioi 0) := by
    have := integrableOn_exp_mul_complex_Ioi (a := -z) (by simp; linarith) 0
    simpa [neg_mul] using this
  refine Integrable.mono' (Integrable.const_mul he.norm M) (hGm.mul
    (by fun_prop : Continuous fun y : ℝ => Complex.exp (-(z * (y : ℂ)))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : (0 : ℝ) < y := hy
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hG y hy0) (norm_nonneg _)

/-- A real integrand vanishing on `(0, 1)` is integrable on `(0, ∞)` once it is integrable on
`(1, ∞)`. -/
lemma convS_integrableOn_Ioi_of_vanish {G : ℝ → ℝ} (hG0 : ∀ y : ℝ, 0 < y → y < 1 → G y = 0)
    (hG : IntegrableOn G (Ioi 1)) : IntegrableOn G (Ioi 0) := by
  rw [← Set.Ioo_union_Ici_eq_Ioi zero_lt_one, integrableOn_union]
  exact ⟨integrableOn_zero.congr_fun (fun y hy => (hG0 y hy.1 hy.2).symm) measurableSet_Ioo,
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hG⟩

/-- Every iterated derivative of `w_h` vanishes on `(-∞, 1)`. -/
lemma convS_iteratedDeriv_zero_of_lt {p h y : ℝ} (hy : y < 1) (r : ℕ) :
    iteratedDeriv r (convWh p h) y = 0 := by
  have hev : convWh p h =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (isOpen_Iio.mem_nhds hy) (fun x hx => convWh_eq_zero (le_of_lt hx))
  rw [hev.iteratedDeriv_eq r, iteratedDeriv_const]
  simp

/-- Every iterated derivative of `w_h` vanishes on `(-∞, 1]` (by continuity from `(-∞, 1)`). -/
lemma convS_iteratedDeriv_zero_of_le {p h y : ℝ} (hh : 0 < h) (hy : y ≤ 1) (r : ℕ) :
    iteratedDeriv r (convWh p h) y = 0 := by
  have hW : ContDiff ℝ (⊤ : ℕ∞) (convWh p h) := convWh_contDiff hh
  have hcont : Continuous (iteratedDeriv r (convWh p h)) :=
    ContDiff.continuous_iteratedDeriv r hW (by simp)
  have hcl : Iic (1 : ℝ) ⊆ {x : ℝ | iteratedDeriv r (convWh p h) x = 0} := by
    rw [← closure_Iio (1 : ℝ)]
    exact closure_minimal (fun x hx => convS_iteratedDeriv_zero_of_lt hx r)
      (isClosed_eq hcont continuous_const)
  exact hcl hy

/-- One integration by parts on `(0, ∞)` against `e^{-zy}`: for `g` vanishing on `(0, 1)`, bounded
on `[1, ∞)` and with `g'` its derivative,
`∫ g e^{-zy} = (1/z) ∫ g' e^{-zy}`. -/
lemma convS_ibp {g g' : ℝ → ℝ} {M : ℝ} {z : ℂ} (hz : 0 < z.re)
    (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (g' y) y)
    (hg0 : ∀ y : ℝ, 0 < y → y < 1 → g y = 0)
    (hM : ∀ y : ℝ, 1 ≤ y → |g y| ≤ M)
    (hgi : IntegrableOn (fun y : ℝ => (g y : ℂ) * Complex.exp (-(z * (y : ℂ)))) (Ioi 0))
    (hg'i : IntegrableOn (fun y : ℝ => (g' y : ℂ) * Complex.exp (-(z * (y : ℂ)))) (Ioi 0)) :
    ∫ y in Ioi (0 : ℝ), (g y : ℂ) * Complex.exp (-(z * (y : ℂ)))
      = (1 / z) * ∫ y in Ioi (0 : ℝ), (g' y : ℂ) * Complex.exp (-(z * (y : ℂ))) := by
  have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
  have hE : ∀ y : ℝ, HasDerivAt (fun y : ℝ => -(Complex.exp (-(z * (y : ℂ)))) / z)
      (Complex.exp (-(z * (y : ℂ)))) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
    have h2 : HasDerivAt (fun y : ℝ => -(z * (y : ℂ))) (-(z * 1)) y := (h1.const_mul z).neg
    have h3 := ((h2.cexp).neg).div_const z
    convert h3 using 1
    field_simp
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => (g y : ℂ)) (g' x : ℂ) x :=
    fun x hx => (hg x hx).ofReal_comp
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => -(Complex.exp (-(z * (y : ℂ)))) / z)
      (Complex.exp (-(z * (x : ℂ)))) x := fun x _ => hE x
  have h_zero : Tendsto ((fun y : ℝ => (g y : ℂ)) * (fun y : ℝ => -(Complex.exp (-(z * (y : ℂ)))) / z))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with y hy
    simp only [Pi.mul_apply, hg0 y hy.1 hy.2, Complex.ofReal_zero, zero_mul]
  have hlim := convS_tendsto_zero (z := z) (M := M) hz (fun y hy => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hM y hy)
  have h_infty : Tendsto ((fun y : ℝ => (g y : ℂ)) * (fun y : ℝ => -(Complex.exp (-(z * (y : ℂ)))) / z))
      atTop (𝓝 0) := by
    have h3 := hlim.const_mul (-(1 / z))
    rw [mul_zero] at h3
    refine h3.congr (fun y => ?_)
    simp only [Pi.mul_apply]
    ring
  have huv : IntegrableOn ((fun y : ℝ => (g' y : ℂ)) * (fun y : ℝ => -(Complex.exp (-(z * (y : ℂ)))) / z)
      + (fun y : ℝ => (g y : ℂ)) * (fun y : ℝ => Complex.exp (-(z * (y : ℂ))))) (Ioi 0) := by
    refine IntegrableOn.congr_fun
      ((Integrable.const_mul hg'i (-(1 / z))).add hgi) (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  have key := integral_Ioi_deriv_mul_eq_sub (u := fun y : ℝ => (g y : ℂ))
    (v := fun y : ℝ => -(Complex.exp (-(z * (y : ℂ)))) / z)
    (u' := fun y : ℝ => (g' y : ℂ)) (v' := fun y : ℝ => Complex.exp (-(z * (y : ℂ))))
    (a := 0) (a' := 0) (b' := 0) hu hv huv h_zero h_infty
  have e2 : ∫ x in Ioi (0 : ℝ), (g' x : ℂ) * (-(Complex.exp (-(z * (x : ℂ)))) / z)
        + (g x : ℂ) * Complex.exp (-(z * (x : ℂ)))
      = ∫ x in Ioi (0 : ℝ), (-(1 / z)) * ((g' x : ℂ) * Complex.exp (-(z * (x : ℂ))))
        + (g x : ℂ) * Complex.exp (-(z * (x : ℂ))) := by
    congr 1
    funext x
    ring
  rw [integral_add ((Integrable.const_mul hg'i (-(1 / z)))) hgi, integral_const_mul] at e2
  simp only [sub_zero] at key
  linear_combination key - e2

/-- `y · y^s = y^{s+1}` for `y > 0`. -/
lemma convS_mul_rpow {y : ℝ} (hy : 0 < y) (s : ℝ) : y * y ^ s = y ^ (s + 1) := by
  rw [Real.rpow_add_one hy.ne', mul_comm]

/-- The `k = 1` moment `∫ w_h(y) (-y) e^{-zy}` decays like `‖z‖^{-2}`, uniformly in `h > 0`
(`ceo:conv.5` for `k = 1`). The bound holds for every `z` with `Re z > 0`; the constant is `2|C|`
from the derivative bounds of `ConvWeightDerivBound`. Two integrations by parts against `e^{-zy}`
turn `y w_h` into `(y w_h)''`, which is `O(y^{-5/2})` on `[1, ∞)` and vanishes on `(0, 1)`. -/
theorem convS_k1_decay {p C : ℝ} (hp : 0 ≤ p) (hD : ConvWeightDerivBound p C) {h : ℝ} (hh : 0 < h)
    {z : ℂ} (hz : 0 < z.re) :
    ‖convSD (convWh p h) 1 z‖ ≤ 2 * |C| * ‖z‖ ^ (-(1 : ℝ) - 1) := by
  have hW : ContDiff ℝ (⊤ : ℕ∞) (convWh p h) := convWh_contDiff hh
  have hWc : Continuous (convWh p h) := hW.continuous
  have hd1 : ∀ y : ℝ, HasDerivAt (convWh p h) (iteratedDeriv 1 (convWh p h) y) y := by
    intro y
    rw [iteratedDeriv_one]
    exact ((contDiff_infty_iff_deriv.mp hW).1 y).hasDerivAt
  have hW1 : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv 1 (convWh p h)) := by
    rw [iteratedDeriv_one]; exact (contDiff_infty_iff_deriv.mp hW).2
  have e2 : iteratedDeriv 2 (convWh p h) = deriv (iteratedDeriv 1 (convWh p h)) := iteratedDeriv_succ
  have hd2 : ∀ y : ℝ, HasDerivAt (iteratedDeriv 1 (convWh p h)) (iteratedDeriv 2 (convWh p h) y) y := by
    intro y
    rw [e2]
    exact ((contDiff_infty_iff_deriv.mp hW1).1 y).hasDerivAt
  have hi1 : Continuous (iteratedDeriv 1 (convWh p h)) := hW1.continuous
  have hi2 : Continuous (iteratedDeriv 2 (convWh p h)) := by
    rw [e2]; exact (contDiff_infty_iff_deriv.mp hW1).2.continuous
  have hg2c : Continuous (fun y : ℝ => iteratedDeriv 1 (convWh p h) y
      + (iteratedDeriv 1 (convWh p h) y + y * iteratedDeriv 2 (convWh p h) y)) :=
    hi1.add (hi1.add (continuous_id.mul hi2))
  -- derivatives of the three functions `y w`, `w + y w'`, and `w' + (w' + y w'')`
  have hG0 : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y * convWh p h y)
      (convWh p h y + y * iteratedDeriv 1 (convWh p h) y) y := by
    intro y
    have := (hasDerivAt_id' y).mul (hd1 y)
    convert this using 1
    ring
  have hG1 : ∀ y : ℝ, HasDerivAt (fun y : ℝ => convWh p h y + y * iteratedDeriv 1 (convWh p h) y)
      (iteratedDeriv 1 (convWh p h) y + (iteratedDeriv 1 (convWh p h) y
        + y * iteratedDeriv 2 (convWh p h) y)) y := by
    intro y
    have := (hd1 y).add ((hasDerivAt_id' y).mul (hd2 y))
    convert this using 1
    ring
  -- vanishing on `(0, 1)`
  have hV0 : ∀ y : ℝ, 0 < y → y < 1 → y * convWh p h y = 0 := fun y _ hy => by
    rw [convWh_eq_zero (p := p) (h := h) (le_of_lt hy), mul_zero]
  have hV1 : ∀ y : ℝ, 0 < y → y < 1 →
      convWh p h y + y * iteratedDeriv 1 (convWh p h) y = 0 := fun y _ hy => by
    rw [convWh_eq_zero (p := p) (h := h) (le_of_lt hy), convS_iteratedDeriv_zero_of_lt (p := p) (h := h) hy 1]
    ring
  have hV2le : ∀ y : ℝ, y ≤ 1 →
      iteratedDeriv 1 (convWh p h) y + (iteratedDeriv 1 (convWh p h) y
        + y * iteratedDeriv 2 (convWh p h) y) = 0 := fun y hy => by
    rw [convS_iteratedDeriv_zero_of_le (p := p) (h := h) hh hy 1,
      convS_iteratedDeriv_zero_of_le (p := p) (h := h) hh hy 2]
    ring
  have hV2 : ∀ y : ℝ, 0 < y → y < 1 →
      iteratedDeriv 1 (convWh p h) y + (iteratedDeriv 1 (convWh p h) y
        + y * iteratedDeriv 2 (convWh p h) y) = 0 := fun y _ hy => by
    rw [convS_iteratedDeriv_zero_of_lt (p := p) (h := h) hy 1,
      convS_iteratedDeriv_zero_of_lt (p := p) (h := h) hy 2]
    ring
  -- bounds on `[1, ∞)`
  have hK0 : 0 ≤ |C| := abs_nonneg C
  have hb1 : ∀ y : ℝ, 1 ≤ y → |iteratedDeriv 1 (convWh p h) y| ≤ |C| * y ^ (-(5 / 2 : ℝ)) := by
    intro y hy
    have h1 := hD.deriv_le 1 (by norm_num) h hh y hy
    have e : (-(3 / 2 : ℝ) - ((1 : ℕ) : ℝ)) = -(5 / 2 : ℝ) := by norm_num
    rw [e] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _))
  have hb2 : ∀ y : ℝ, 1 ≤ y → |iteratedDeriv 2 (convWh p h) y| ≤ |C| * y ^ (-(7 / 2 : ℝ)) := by
    intro y hy
    have h1 := hD.deriv_le 2 (by norm_num) h hh y hy
    have e : (-(3 / 2 : ℝ) - ((2 : ℕ) : ℝ)) = -(7 / 2 : ℝ) := by norm_num
    rw [e] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _))
  -- `y^s ≤ 1` and `y · y^s ≤ 1` on `[1, ∞)`
  have hle_mul : ∀ (y s : ℝ), 1 ≤ y → s + 1 ≤ 0 → y * y ^ s ≤ 1 := fun y s hy hs => by
    rw [convS_mul_rpow (by linarith) s]
    exact Real.rpow_le_one_of_one_le_of_nonpos hy hs
  have hyy : ∀ (y s : ℝ), 1 ≤ y → s ≤ 0 → y ^ s ≤ 1 := fun y s hy hs =>
    Real.rpow_le_one_of_one_le_of_nonpos hy hs
  have hA1 : ∀ y : ℝ, 1 ≤ y → |convWh p h y| ≤ 1 := fun y hy => by
    have y0 : (0 : ℝ) < y := by linarith
    rw [abs_of_nonneg (convWh_nonneg hh.le y0)]
    exact (convWh_le hp hh.le y0).trans (hyy y _ hy (by norm_num))
  have hbg0 : ∀ y : ℝ, 1 ≤ y → |y * convWh p h y| ≤ 1 := fun y hy => by
    have y0 : (0 : ℝ) < y := by linarith
    rw [abs_mul, abs_of_pos y0]
    calc y * |convWh p h y| ≤ y * y ^ (-(3 / 2 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ y0.le
          rw [abs_of_nonneg (convWh_nonneg hh.le y0)]
          exact convWh_le hp hh.le y0
      _ ≤ 1 := hle_mul y _ hy (by norm_num)
  have hA2 : ∀ y : ℝ, 1 ≤ y → y * |iteratedDeriv 1 (convWh p h) y| ≤ |C| := fun y hy => by
    have y0 : (0 : ℝ) < y := by linarith
    calc y * |iteratedDeriv 1 (convWh p h) y| ≤ y * (|C| * y ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hb1 y hy) y0.le
      _ = |C| * (y * y ^ (-(5 / 2 : ℝ))) := by ring
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left (hle_mul y _ hy (by norm_num)) hK0
      _ = |C| := mul_one _
  have hA3 : ∀ y : ℝ, 1 ≤ y → y * |iteratedDeriv 2 (convWh p h) y| ≤ |C| * y ^ (-(5 / 2 : ℝ)) :=
    fun y hy => by
    have y0 : (0 : ℝ) < y := by linarith
    calc y * |iteratedDeriv 2 (convWh p h) y| ≤ y * (|C| * y ^ (-(7 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hb2 y hy) y0.le
      _ = |C| * (y * y ^ (-(7 / 2 : ℝ))) := by ring
      _ = |C| * y ^ (-(5 / 2 : ℝ)) := by
          rw [convS_mul_rpow y0]; norm_num
  have hbg1 : ∀ y : ℝ, 1 ≤ y →
      |convWh p h y + y * iteratedDeriv 1 (convWh p h) y| ≤ 1 + |C| := fun y hy => by
    have y0 : (0 : ℝ) < y := by linarith
    calc |convWh p h y + y * iteratedDeriv 1 (convWh p h) y|
        ≤ |convWh p h y| + |y * iteratedDeriv 1 (convWh p h) y| := abs_add_le _ _
      _ = |convWh p h y| + y * |iteratedDeriv 1 (convWh p h) y| := by
          rw [abs_mul, abs_of_pos y0]
      _ ≤ 1 + |C| := add_le_add (hA1 y hy) (hA2 y hy)
  have hbg2 : ∀ y : ℝ, 1 ≤ y → |iteratedDeriv 1 (convWh p h) y
      + (iteratedDeriv 1 (convWh p h) y + y * iteratedDeriv 2 (convWh p h) y)|
        ≤ 3 * |C| * y ^ (-(5 / 2 : ℝ)) := fun y hy => by
    have y0 : (0 : ℝ) < y := by linarith
    have hy5 : (0 : ℝ) ≤ y ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg y0.le _
    have t1 := abs_add_le (iteratedDeriv 1 (convWh p h) y)
      (iteratedDeriv 1 (convWh p h) y + y * iteratedDeriv 2 (convWh p h) y)
    have t2 := abs_add_le (iteratedDeriv 1 (convWh p h) y) (y * iteratedDeriv 2 (convWh p h) y)
    rw [abs_mul, abs_of_pos y0] at t2
    have t3 := hb1 y hy
    have t4 := hA3 y hy
    linarith
  have hbg2' : ∀ y : ℝ, 1 ≤ y → |iteratedDeriv 1 (convWh p h) y
      + (iteratedDeriv 1 (convWh p h) y + y * iteratedDeriv 2 (convWh p h) y)| ≤ 3 * |C| := fun y hy =>
    (hbg2 y hy).trans (mul_le_of_le_one_right (by positivity) (hyy y _ hy (by norm_num)))
  -- global bounds on `(0, ∞)` (the functions vanish on `(0, 1)`)
  have hcn : ∀ x : ℝ, ‖(x : ℂ)‖ = |x| := fun x => by rw [Complex.norm_real, Real.norm_eq_abs]
  have glob : ∀ (G : ℝ → ℝ) (M : ℝ), 0 ≤ M → (∀ y : ℝ, 0 < y → y < 1 → G y = 0) →
      (∀ y : ℝ, 1 ≤ y → |G y| ≤ M) → ∀ y : ℝ, 0 < y → |G y| ≤ M := by
    intro G M hM0 hG0 hbig y hy
    by_cases h1 : y < 1
    · rw [hG0 y hy h1, abs_zero]; exact hM0
    · exact hbig y (not_lt.mp h1)
  have hsm : ∀ G : ℝ → ℝ, Continuous G → AEStronglyMeasurable (fun y : ℝ => (G y : ℂ))
      (volume.restrict (Ioi (0 : ℝ))) := fun G hG =>
    (Complex.continuous_ofReal.comp hG).aestronglyMeasurable
  have hgi0 : IntegrableOn (fun y : ℝ => ((y * convWh p h y : ℝ) : ℂ) * Complex.exp (-(z * (y : ℂ))))
      (Ioi 0) :=
    convS_int_exp (M := 1) hz (hsm _ (continuous_id.mul hWc)) (fun y hy => by
      rw [hcn]
      exact glob _ 1 zero_le_one (fun y _ hy1 => hV0 y ‹_› hy1) hbg0 y hy)
  have hgi1 : IntegrableOn (fun y : ℝ => ((convWh p h y + y * iteratedDeriv 1 (convWh p h) y : ℝ) : ℂ)
      * Complex.exp (-(z * (y : ℂ)))) (Ioi 0) :=
    convS_int_exp (M := 1 + |C|) hz (hsm _ (hWc.add (continuous_id.mul hi1))) (fun y hy => by
      rw [hcn]
      exact glob _ (1 + |C|) (by linarith) (fun y _ hy1 => hV1 y ‹_› hy1) hbg1 y hy)
  have hgi2 : IntegrableOn (fun y : ℝ => ((iteratedDeriv 1 (convWh p h) y
      + (iteratedDeriv 1 (convWh p h) y + y * iteratedDeriv 2 (convWh p h) y) : ℝ) : ℂ)
      * Complex.exp (-(z * (y : ℂ)))) (Ioi 0) :=
    convS_int_exp (M := 3 * |C|) hz (hsm _ hg2c) (fun y hy => by
      rw [hcn]
      exact glob _ (3 * |C|) (by linarith) (fun y _ hy1 => hV2 y ‹_› hy1) hbg2' y hy)
  -- the two integrations by parts
  have I1 : ∫ y in Ioi (0 : ℝ), ((y * convWh p h y : ℝ) : ℂ) * Complex.exp (-(z * (y : ℂ)))
      = (1 / z) * ∫ y in Ioi (0 : ℝ), ((convWh p h y + y * iteratedDeriv 1 (convWh p h) y : ℝ) : ℂ)
        * Complex.exp (-(z * (y : ℂ))) :=
    convS_ibp (M := 1) hz (fun y _ => hG0 y) (fun y _ hy1 => hV0 y ‹_› hy1) hbg0 hgi0 hgi1
  have I2 : ∫ y in Ioi (0 : ℝ), ((convWh p h y + y * iteratedDeriv 1 (convWh p h) y : ℝ) : ℂ)
        * Complex.exp (-(z * (y : ℂ)))
      = (1 / z) * ∫ y in Ioi (0 : ℝ), ((iteratedDeriv 1 (convWh p h) y
          + (iteratedDeriv 1 (convWh p h) y + y * iteratedDeriv 2 (convWh p h) y) : ℝ) : ℂ)
        * Complex.exp (-(z * (y : ℂ))) :=
    convS_ibp (M := 1 + |C|) hz (fun y _ => hG1 y) (fun y _ hy1 => hV1 y ‹_› hy1) hbg1 hgi1 hgi2
  -- the moment equals minus the first integral
  have hsd : convSD (convWh p h) 1 z
      = -∫ y in Ioi (0 : ℝ), ((y * convWh p h y : ℝ) : ℂ) * Complex.exp (-(z * (y : ℂ))) := by
    unfold convSD
    rw [← integral_neg]
    congr 1
    funext y
    push_cast
    ring
  -- the bound on the second derivative `(y w)''`
  have hI5 : IntegrableOn (fun y : ℝ => y ^ (-(5 / 2 : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  have hJ1 : IntegrableOn (fun y : ℝ => |iteratedDeriv 1 (convWh p h) y
      + (iteratedDeriv 1 (convWh p h) y + y * iteratedDeriv 2 (convWh p h) y)|) (Ioi 1) :=
    Integrable.mono' (Integrable.const_mul hI5 (3 * |C|))
      ((continuous_abs.comp hg2c).aestronglyMeasurable)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        rw [Real.norm_eq_abs, abs_abs]
        exact hbg2 y (le_of_lt hy))
  have hA2' : IntegrableOn (fun y : ℝ => |iteratedDeriv 1 (convWh p h) y
      + (iteratedDeriv 1 (convWh p h) y + y * iteratedDeriv 2 (convWh p h) y)|) (Ioi 0) :=
    convS_integrableOn_Ioi_of_vanish (fun y hy0 hy1 => by
      rw [hV2 y hy0 hy1, abs_zero]) hJ1
  have hIbound : ∫ y in Ioi (0 : ℝ), |iteratedDeriv 1 (convWh p h) y
      + (iteratedDeriv 1 (convWh p h) y + y * iteratedDeriv 2 (convWh p h) y)| ≤ 2 * |C| := by
    rw [convS_split_Ioi_one hA2' (fun y _ hy1 => by rw [hV2le y hy1, abs_zero])]
    calc ∫ y in Ioi (1 : ℝ), |iteratedDeriv 1 (convWh p h) y
          + (iteratedDeriv 1 (convWh p h) y + y * iteratedDeriv 2 (convWh p h) y)|
        ≤ ∫ y in Ioi (1 : ℝ), 3 * |C| * y ^ (-(5 / 2 : ℝ)) :=
          setIntegral_mono_on hJ1 (Integrable.const_mul hI5 (3 * |C|)) measurableSet_Ioi
            (fun y hy => hbg2 y (le_of_lt hy))
      _ = 2 * |C| := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
          norm_num [Real.one_rpow]
          ring
  -- the norm of the last integral
  have hJ : ‖∫ y in Ioi (0 : ℝ), ((iteratedDeriv 1 (convWh p h) y
          + (iteratedDeriv 1 (convWh p h) y + y * iteratedDeriv 2 (convWh p h) y) : ℝ) : ℂ)
        * Complex.exp (-(z * (y : ℂ)))‖ ≤ 2 * |C| := by
    refine (norm_integral_le_of_norm_le hA2' ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun y hy => ?_))).trans hIbound
    have hy0 : (0 : ℝ) < y := hy
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (norm_exp_neg_mul_le hz.le hy0.le)
  -- assemble
  have hr : ‖z‖ ^ (-(1 : ℝ) - 1) = (‖z‖ ^ 2)⁻¹ := by
    rw [show (-(1 : ℝ) - 1) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (norm_nonneg z),
      Real.rpow_natCast]
  rw [hsd, norm_neg, I1, I2, norm_mul, norm_mul, norm_div, norm_one, hr]
  calc 1 / ‖z‖ * (1 / ‖z‖ * ‖∫ y in Ioi (0 : ℝ), ((iteratedDeriv 1 (convWh p h) y
          + (iteratedDeriv 1 (convWh p h) y + y * iteratedDeriv 2 (convWh p h) y) : ℝ) : ℂ)
        * Complex.exp (-(z * (y : ℂ)))‖)
      ≤ 1 / ‖z‖ * (1 / ‖z‖ * (2 * |C|)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJ (by positivity)) (by positivity)
    _ = 2 * |C| * (‖z‖ ^ 2)⁻¹ := by ring

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

/-- info: 'FormalResearch.SignUncertainty.convS_k1_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_k1_decay


end FormalResearch.SignUncertainty
