module

public import Mathlib
public import FormalResearch.SignUncertainty.ConvSourceLaplace

/-!
# Integration by parts against `e^{-zy}`: the general moment bounds (M6, `ceo:conv.5`)

An abstract decay estimate for `I(z) = ∫₀^∞ F(y) e^{-zy} dy`, `Re z > 0`, where `F` is smooth,
vanishes on `(-∞, 1]` and satisfies `|F^{(j)}(y)| ≤ K y^{s-j}` on `[1, ∞)` for `j ≤ m`
(hypothesis structure `ConvMomentData F K s m`, with `-1 < s` and `s - m < -1`). For the moment
`F(y) = y^k w_h(y)` one has `s = k - 3/2` and `m = k + 1`.

* `convS_ibp_tail`: one integration by parts on `(T, ∞)`, with the boundary term at `T`.
* `convS_ibp_iter`: `m` integrations by parts (the boundary terms and the remaining integral).
* `convS_tail_norm_le`: the norm bound of the integral over `(T, ∞)` for `T ≥ 1`.
* `convS_moment_decay`: `‖I(z)‖ ≤ K/(m-s-1) ‖z‖^{-m}` for every `Re z > 0` (`T = 1`, where all the
  boundary terms vanish).
* `convS_moment_small`: `‖I(z)‖ ≤ K (1/(s+1) + m + 1/(m-s-1)) ‖z‖^{-(s+1)}` for `‖z‖ ≤ 1`
  (split at `T = 1/‖z‖`: the inner part is bounded in absolute value, the outer part by `m`
  integrations by parts with the boundary terms at `T`; no smooth cutoff is needed).

All statements are class: proved (no hypothesis beyond `ConvMomentData`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- The derivative data of a moment integrand `F`: smooth, vanishing on `(-∞, 1]`, with the
derivative bounds `|F^{(j)}(y)| ≤ K y^{s-j}` on `[1, ∞)` for `j ≤ m`; `-1 < s` and `s - m < -1`
make the integrals converge. -/
structure ConvMomentData (F : ℝ → ℝ) (K s : ℝ) (m : ℕ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) F
  vanish : ∀ y : ℝ, y ≤ 1 → F y = 0
  K_nonneg : 0 ≤ K
  s_gt : -1 < s
  s_lt : s - m < -1
  bound : ∀ j : ℕ, j ≤ m → ∀ y : ℝ, 1 ≤ y → |iteratedDeriv j F y| ≤ K * y ^ (s - j)

/-- The iterated derivatives of a smooth function are smooth. -/
lemma convS_contDiff_iteratedDeriv {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv m F) := by
  induction m with
  | zero => simpa using hF
  | succ m ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

/-- The derivative of `iteratedDeriv m F` is `iteratedDeriv (m+1) F`, everywhere. -/
lemma convS_hasDerivAt_iteratedDeriv {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (m : ℕ) (y : ℝ) :
    HasDerivAt (iteratedDeriv m F) (iteratedDeriv (m + 1) F y) y := by
  rw [iteratedDeriv_succ]
  exact ((contDiff_infty_iff_deriv.mp (convS_contDiff_iteratedDeriv hF m)).1 y).hasDerivAt

/-- All iterated derivatives of a smooth `F` vanishing on `(-∞, 1)` vanish on `(-∞, 1]`. -/
lemma convS_iteratedDeriv_zero_of_le_gen {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hF0 : ∀ y : ℝ, y < 1 → F y = 0) (r : ℕ) {y : ℝ} (hy : y ≤ 1) :
    iteratedDeriv r F y = 0 := by
  have hcont : Continuous (iteratedDeriv r F) := hF.continuous_iteratedDeriv r (by simp)
  have hlt : ∀ x : ℝ, x < 1 → iteratedDeriv r F x = 0 := fun x hx => by
    have hev : F =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (isOpen_Iio.mem_nhds hx) (fun t ht => hF0 t ht)
    rw [hev.iteratedDeriv_eq r, iteratedDeriv_const]
    simp
  have hcl : Iic (1 : ℝ) ⊆ {x : ℝ | iteratedDeriv r F x = 0} := by
    rw [← closure_Iio (1 : ℝ)]
    exact closure_minimal (fun x hx => hlt x hx) (isClosed_eq hcont continuous_const)
  exact hcl hy

/-- `y^s e^{-b y}` is integrable on `(T, ∞)` for `s > -1`, `b > 0`, `T ≥ 0`. -/
lemma convS_integrableOn_rpow_exp {s b : ℝ} (hs : -1 < s) (hb : 0 < b) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun y : ℝ => y ^ s * Real.exp (-(b * y))) (Ioi T) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hs one_pos hb
  refine (h.congr_fun (fun y _ => ?_) measurableSet_Ioi).mono_set (Ioi_subset_Ioi hT)
  simp only [Real.rpow_one, neg_mul]

/-- A continuous `G` with `|G y| ≤ M y^s` on `[T, ∞)` (`s > -1`) has `G e^{-zy}` integrable on
`(T, ∞)` for `Re z > 0`. -/
lemma convS_integrableOn_poly {G : ℝ → ℝ} {M s T : ℝ} {z : ℂ} (hz : 0 < z.re) (hs : -1 < s)
    (hT : 0 ≤ T) (hGc : Continuous G) (hG : ∀ y : ℝ, T ≤ y → |G y| ≤ M * y ^ s) :
    IntegrableOn (fun y : ℝ => (G y : ℂ) * Complex.exp (-(z * (y : ℂ)))) (Ioi T) := by
  refine Integrable.mono' ((convS_integrableOn_rpow_exp hs hz hT).const_mul M) ?_ ?_
  · exact ((Complex.continuous_ofReal.comp hGc).mul
      (by fun_prop : Continuous fun y : ℝ => Complex.exp (-(z * (y : ℂ))))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : T ≤ y := le_of_lt hy
    have hre : (-(z * (y : ℂ))).re = -(z.re * y) := by simp [Complex.mul_re]
    rw [norm_mul, Complex.norm_real, Complex.norm_exp, hre, Real.norm_eq_abs]
    calc |G y| * Real.exp (-(z.re * y)) ≤ (M * y ^ s) * Real.exp (-(z.re * y)) :=
          mul_le_mul_of_nonneg_right (hG y hy') (Real.exp_nonneg _)
      _ = M * (y ^ s * Real.exp (-(z.re * y))) := by ring

/-- A function with `|G y| ≤ M y^s` on `[T, ∞)` has `G e^{-zy} → 0` at `∞` for `Re z > 0`. -/
lemma convS_tendsto_poly {G : ℝ → ℝ} {M s T : ℝ} {z : ℂ} (hz : 0 < z.re)
    (hG : ∀ y : ℝ, T ≤ y → |G y| ≤ M * y ^ s) :
    Tendsto (fun y : ℝ => (G y : ℂ) * Complex.exp (-(z * (y : ℂ)))) atTop (𝓝 0) := by
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s z.re hz).const_mul M
  rw [mul_zero] at h1
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [eventually_ge_atTop T] with y hy
  have hre : (-(z * (y : ℂ))).re = -(z.re * y) := by simp [Complex.mul_re]
  rw [norm_mul, Complex.norm_real, Complex.norm_exp, hre, Real.norm_eq_abs, neg_mul]
  calc |G y| * Real.exp (-(z.re * y)) ≤ (M * y ^ s) * Real.exp (-(z.re * y)) :=
        mul_le_mul_of_nonneg_right (hG y hy) (Real.exp_nonneg _)
    _ = M * (y ^ s * Real.exp (-(z.re * y))) := by ring

/-- One integration by parts on `(T, ∞)` against `e^{-zy}`, with the boundary term at `T`:
`∫_T^∞ G e^{-zy} = G(T) e^{-zT}/z + (1/z) ∫_T^∞ G' e^{-zy}`, for `G`, `G'` continuous with
`|G|, |G'| ≤ M y^s` on `[T, ∞)` and `G' = G'` everywhere. -/
lemma convS_ibp_tail {G G' : ℝ → ℝ} {M s T : ℝ} {z : ℂ} (hz : 0 < z.re) (hs : -1 < s) (hT : 0 < T)
    (hg : ∀ y : ℝ, HasDerivAt G (G' y) y) (hGc : Continuous G) (hG'c : Continuous G')
    (hG : ∀ y : ℝ, T ≤ y → |G y| ≤ M * y ^ s) (hG' : ∀ y : ℝ, T ≤ y → |G' y| ≤ M * y ^ s) :
    ∫ y in Ioi T, (G y : ℂ) * Complex.exp (-(z * (y : ℂ)))
      = (G T : ℂ) * Complex.exp (-(z * (T : ℂ))) / z
        + (1 / z) * ∫ y in Ioi T, (G' y : ℂ) * Complex.exp (-(z * (y : ℂ))) := by
  have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
  have hE : ∀ y : ℝ, HasDerivAt (fun y : ℝ => -(Complex.exp (-(z * (y : ℂ)))) / z)
      (Complex.exp (-(z * (y : ℂ)))) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
    have h2 : HasDerivAt (fun y : ℝ => -(z * (y : ℂ))) (-(z * 1)) y := (h1.const_mul z).neg
    have h3 := ((h2.cexp).neg).div_const z
    convert h3 using 1
    field_simp
  have hu : ∀ x ∈ Ioi T, HasDerivAt (fun y : ℝ => (G y : ℂ)) (G' x : ℂ) x :=
    fun x _ => (hg x).ofReal_comp
  have hv : ∀ x ∈ Ioi T, HasDerivAt (fun y : ℝ => -(Complex.exp (-(z * (y : ℂ)))) / z)
      (Complex.exp (-(z * (x : ℂ)))) x := fun x _ => hE x
  have hGi := convS_integrableOn_poly hz hs hT.le hGc hG
  have hG'i := convS_integrableOn_poly hz hs hT.le hG'c hG'
  have hu'v : IntegrableOn ((fun y : ℝ => (G' y : ℂ)) *
      (fun y : ℝ => -(Complex.exp (-(z * (y : ℂ)))) / z)) (Ioi T) := by
    refine IntegrableOn.congr_fun (hG'i.const_mul (-(1 / z))) (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]
    ring
  have hcont : Continuous ((fun y : ℝ => (G y : ℂ)) *
      (fun y : ℝ => -(Complex.exp (-(z * (y : ℂ)))) / z)) :=
    (Complex.continuous_ofReal.comp hGc).mul (by fun_prop)
  have h_zero : Tendsto ((fun y : ℝ => (G y : ℂ)) *
      (fun y : ℝ => -(Complex.exp (-(z * (y : ℂ)))) / z)) (𝓝[>] T)
      (𝓝 ((G T : ℂ) * (-(Complex.exp (-(z * (T : ℂ)))) / z))) :=
    (hcont.tendsto T).mono_left nhdsWithin_le_nhds
  have h_infty : Tendsto ((fun y : ℝ => (G y : ℂ)) *
      (fun y : ℝ => -(Complex.exp (-(z * (y : ℂ)))) / z)) atTop (𝓝 0) := by
    have h3 := (convS_tendsto_poly (T := T) hz hG).const_mul (-(1 / z))
    rw [mul_zero] at h3
    refine h3.congr (fun y => ?_)
    simp only [Pi.mul_apply]
    ring
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (a := T)
    (u := fun y : ℝ => (G y : ℂ)) (v := fun y : ℝ => -(Complex.exp (-(z * (y : ℂ)))) / z)
    (u' := fun y : ℝ => (G' y : ℂ)) (v' := fun y : ℝ => Complex.exp (-(z * (y : ℂ))))
    (a' := (G T : ℂ) * (-(Complex.exp (-(z * (T : ℂ)))) / z)) (b' := 0)
    hu hv hGi hu'v h_zero h_infty
  have e2 : ∫ x in Ioi T, (G' x : ℂ) * (-(Complex.exp (-(z * (x : ℂ)))) / z)
      = -(1 / z) * ∫ x in Ioi T, (G' x : ℂ) * Complex.exp (-(z * (x : ℂ))) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [e2] at key
  rw [key]
  ring

/-- `m` integrations by parts on `(T, ∞)`: the boundary terms at `T` and the remaining integral. -/
lemma convS_ibp_iter {F : ℝ → ℝ} {M s T : ℝ} {z : ℂ} (hz : 0 < z.re) (hs : -1 < s) (hT : 0 < T)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (m : ℕ)
    (hD : ∀ j : ℕ, j ≤ m → ∀ y : ℝ, T ≤ y → |iteratedDeriv j F y| ≤ M * y ^ s) :
    ∫ y in Ioi T, (F y : ℂ) * Complex.exp (-(z * (y : ℂ)))
      = (∑ j ∈ Finset.range m,
          ((iteratedDeriv j F T : ℝ) : ℂ) * Complex.exp (-(z * (T : ℂ))) / z ^ (j + 1))
        + (1 / z) ^ m * ∫ y in Ioi T, ((iteratedDeriv m F y : ℝ) : ℂ) * Complex.exp (-(z * (y : ℂ))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih (fun j hj => hD j (by omega))]
    rw [convS_ibp_tail (G := iteratedDeriv m F) (G' := iteratedDeriv (m + 1) F) hz hs hT
      (convS_hasDerivAt_iteratedDeriv hF m)
      (convS_contDiff_iteratedDeriv hF m).continuous
      (convS_contDiff_iteratedDeriv hF (m + 1)).continuous
      (hD m (by omega)) (hD (m + 1) le_rfl)]
    rw [Finset.sum_range_succ]
    ring

/-- The `j`-th derivative bound `K y^{s-j}` implies the crude bound `K y^s` on `[1, ∞)`. -/
lemma ConvMomentData.crude {F : ℝ → ℝ} {K s : ℝ} {m : ℕ} (hd : ConvMomentData F K s m) {j : ℕ}
    (hj : j ≤ m) {y : ℝ} (hy : 1 ≤ y) : |iteratedDeriv j F y| ≤ K * y ^ s :=
  (hd.bound j hj y hy).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hy (by simp)) hd.K_nonneg)

/-- Norm bound for the integral over `(T, ∞)`, `T ≥ 1`: the boundary terms at `T` plus the
remaining integral of `F^{(m)}`. -/
lemma convS_tail_norm_le {F : ℝ → ℝ} {K s : ℝ} {m : ℕ} (hd : ConvMomentData F K s m) {z : ℂ}
    (hz : 0 < z.re) {T : ℝ} (hT : 1 ≤ T) :
    ‖∫ y in Ioi T, (F y : ℂ) * Complex.exp (-(z * (y : ℂ)))‖
      ≤ (∑ j ∈ Finset.range m, |iteratedDeriv j F T| / ‖z‖ ^ (j + 1))
        + K * (T ^ (s - m + 1) / ((m : ℝ) - s - 1)) / ‖z‖ ^ m := by
  have hT0 : 0 < T := by linarith
  have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [convS_ibp_iter hz hd.s_gt hT0 hd.smooth m
    (fun j hj y hy => hd.crude hj (le_trans hT hy))]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg _) (norm_exp_neg_mul_le hz.le hT0.le)) (by positivity)
  · have hI5 : IntegrableOn (fun y : ℝ => K * y ^ (s - m)) (Ioi T) :=
      (integrableOn_Ioi_rpow_of_lt hd.s_lt hT0).const_mul K
    have hint : ‖∫ y in Ioi T, ((iteratedDeriv m F y : ℝ) : ℂ) * Complex.exp (-(z * (y : ℂ)))‖
        ≤ ∫ y in Ioi T, K * y ^ (s - m) := by
      refine norm_integral_le_of_norm_le hI5 ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun y hy => ?_))
      have hy0 : 0 < y := lt_of_lt_of_le hT0 (le_of_lt hy)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _)
        (norm_exp_neg_mul_le hz.le hy0.le)).trans (hd.bound m le_rfl y (le_trans hT (le_of_lt hy)))
    have hval : ∫ y in Ioi T, K * y ^ (s - m) = K * (T ^ (s - m + 1) / ((m : ℝ) - s - 1)) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hd.s_lt hT0]
      congr 1
      rw [show s - (m : ℝ) + 1 = -((m : ℝ) - s - 1) by ring, div_neg]
      ring_nf
    rw [norm_mul, norm_pow, norm_div, norm_one]
    calc (1 / ‖z‖) ^ m * ‖∫ y in Ioi T, ((iteratedDeriv m F y : ℝ) : ℂ) * Complex.exp (-(z * (y : ℂ)))‖
        ≤ (1 / ‖z‖) ^ m * (K * (T ^ (s - m + 1) / ((m : ℝ) - s - 1))) := by
          rw [← hval]
          exact mul_le_mul_of_nonneg_left hint (by positivity)
      _ = K * (T ^ (s - m + 1) / ((m : ℝ) - s - 1)) / ‖z‖ ^ m := by ring

/-- Complex-valued form of the splitting of `(0, ∞)` at `1` for an integrand vanishing on
`(0, 1]`. -/
lemma convS_integral_Ioi_zero_eq {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 1))
    (h0 : ∀ y : ℝ, y ≤ 1 → f y = 0) :
    ∫ y in Ioi (0 : ℝ), f y = ∫ y in Ioi (1 : ℝ), f y := by
  have hIoc : IntegrableOn f (Ioc (0 : ℝ) 1) :=
    integrableOn_zero.congr_fun (fun y hy => (h0 y hy.2).symm) measurableSet_Ioc
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hIoc hf,
    setIntegral_eq_zero_of_forall_eq_zero (fun y (hy : y ∈ Set.Ioc (0 : ℝ) 1) => h0 y hy.2), zero_add]

/-- `F e^{-zy}` is integrable on `(1, ∞)`, under `ConvMomentData`. -/
lemma ConvMomentData.integrableOn {F : ℝ → ℝ} {K s : ℝ} {m : ℕ} (hd : ConvMomentData F K s m)
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun y : ℝ => (F y : ℂ) * Complex.exp (-(z * (y : ℂ)))) (Ioi 1) :=
  convS_integrableOn_poly hz hd.s_gt zero_le_one hd.smooth.continuous (fun y hy => by
    simpa using hd.crude (Nat.zero_le m) hy)

/-- The moment integral decays like `‖z‖^{-m}`, for every `Re z > 0`: `m` integrations by parts on
`(1, ∞)`, all the boundary terms at `1` vanish. -/
theorem convS_moment_decay {F : ℝ → ℝ} {K s : ℝ} {m : ℕ} (hd : ConvMomentData F K s m) {z : ℂ}
    (hz : 0 < z.re) :
    ‖∫ y in Ioi (0 : ℝ), (F y : ℂ) * Complex.exp (-(z * (y : ℂ)))‖
      ≤ K / ((m : ℝ) - s - 1) * ‖z‖ ^ (-(m : ℝ)) := by
  have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hs0 := convS_iteratedDeriv_zero_of_le_gen hd.smooth (fun y hy => hd.vanish y hy.le)
  rw [convS_integral_Ioi_zero_eq (hd.integrableOn hz) (fun y hy => by simp [hd.vanish y hy])]
  refine (convS_tail_norm_le hd hz le_rfl).trans ?_
  have hsum : (∑ j ∈ Finset.range m, |iteratedDeriv j F 1| / ‖z‖ ^ (j + 1)) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [hs0 j le_rfl, abs_zero, zero_div]
  rw [hsum, zero_add, Real.one_rpow, Real.rpow_neg hzn.le, Real.rpow_natCast]
  apply le_of_eq
  ring

/-- Small `‖z‖`: `‖I(z)‖ ≤ K (1/(s+1) + m + 1/(m-s-1)) ‖z‖^{-(s+1)}`. Split at `T = 1/‖z‖`; on
`(1, T]` the integrand is bounded by `K y^s`, on `(T, ∞)` use `m` integrations by parts. -/
theorem convS_moment_small {F : ℝ → ℝ} {K s : ℝ} {m : ℕ} (hd : ConvMomentData F K s m) {z : ℂ}
    (hz : 0 < z.re) (hz1 : ‖z‖ ≤ 1) :
    ‖∫ y in Ioi (0 : ℝ), (F y : ℂ) * Complex.exp (-(z * (y : ℂ)))‖
      ≤ K * (1 / (s + 1) + m + 1 / ((m : ℝ) - s - 1)) * ‖z‖ ^ (-(s + 1)) := by
  have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
  have ha0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = ‖z‖⁻¹ := ⟨_, rfl⟩
  have haT : ‖z‖ = T⁻¹ := by rw [hTdef, inv_inv]
  have hT1 : 1 ≤ T := by rw [hTdef]; exact (one_le_inv₀ ha0).mpr hz1
  have hT0 : 0 < T := by linarith
  have hs1 : 0 < s + 1 := by linarith [hd.s_gt]
  have hms : 0 < (m : ℝ) - s - 1 := by linarith [hd.s_lt]
  have hint := hd.integrableOn hz
  rw [convS_integral_Ioi_zero_eq hint (fun y hy => by simp [hd.vanish y hy]),
    ← Set.Ioc_union_Ioi_eq_Ioi hT1,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set (fun y hy => (show (1 : ℝ) < y from hy.1)))
      (hint.mono_set (Ioi_subset_Ioi hT1))]
  -- the inner piece
  have hI1 : IntegrableOn (fun y : ℝ => K * y ^ s) (Ioc (1 : ℝ) T) :=
    Integrable.const_mul
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT1).mp
        (intervalIntegral.intervalIntegrable_rpow' hd.s_gt)) K
  have hinner : ‖∫ y in Ioc (1 : ℝ) T, (F y : ℂ) * Complex.exp (-(z * (y : ℂ)))‖
      ≤ K * (T ^ (s + 1) / (s + 1)) := by
    have h1 : ‖∫ y in Ioc (1 : ℝ) T, (F y : ℂ) * Complex.exp (-(z * (y : ℂ)))‖
        ≤ ∫ y in Ioc (1 : ℝ) T, K * y ^ s := by
      refine norm_integral_le_of_norm_le hI1 ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Eventually.of_forall fun y hy => ?_))
      have hy0 : 0 < y := lt_trans zero_lt_one hy.1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _)
        (norm_exp_neg_mul_le hz.le hy0.le)).trans (by simpa using hd.crude (Nat.zero_le m) hy.1.le)
    have h2 : ∫ y in Ioc (1 : ℝ) T, K * y ^ s = K * ((T ^ (s + 1) - 1) / (s + 1)) := by
      rw [integral_const_mul, ← intervalIntegral.integral_of_le hT1,
        integral_rpow (Or.inl hd.s_gt), Real.one_rpow]
    refine h1.trans (h2.trans_le ?_)
    refine mul_le_mul_of_nonneg_left ?_ hd.K_nonneg
    exact div_le_div_of_nonneg_right (by linarith) hs1.le
  -- the outer piece
  have houter := convS_tail_norm_le hd hz hT1
  have hX : (0 : ℝ) < T ^ (s + 1) := Real.rpow_pos_of_pos hT0 _
  have hbd : ∀ j : ℕ, j ≤ m → |iteratedDeriv j F T| / ‖z‖ ^ (j + 1) ≤ K * T ^ (s + 1) := by
    intro j hj
    have hb := hd.bound j hj T hT1
    rw [haT, inv_pow, div_inv_eq_mul]
    calc |iteratedDeriv j F T| * T ^ (j + 1) ≤ K * T ^ (s - j) * T ^ (j + 1) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = K * T ^ (s + 1) := by
          rw [mul_assoc, ← Real.rpow_natCast T (j + 1), ← Real.rpow_add hT0]
          congr 2
          push_cast
          ring
  have hsum : (∑ j ∈ Finset.range m, |iteratedDeriv j F T| / ‖z‖ ^ (j + 1))
      ≤ m * (K * T ^ (s + 1)) := by
    calc (∑ j ∈ Finset.range m, |iteratedDeriv j F T| / ‖z‖ ^ (j + 1))
        ≤ ∑ j ∈ Finset.range m, K * T ^ (s + 1) :=
          Finset.sum_le_sum fun j hj => hbd j (Finset.mem_range.mp hj).le
      _ = m * (K * T ^ (s + 1)) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have htail : K * (T ^ (s - m + 1) / ((m : ℝ) - s - 1)) / ‖z‖ ^ m
      = K * (T ^ (s + 1) / ((m : ℝ) - s - 1)) := by
    rw [haT, inv_pow, div_inv_eq_mul]
    have : T ^ (s - (m : ℝ) + 1) * T ^ m = T ^ (s + 1) := by
      rw [← Real.rpow_natCast T m, ← Real.rpow_add hT0]
      congr 1
      ring
    rw [← this]
    ring
  have hfin : ‖z‖ ^ (-(s + 1)) = T ^ (s + 1) := by
    rw [haT, Real.rpow_neg (inv_nonneg.mpr hT0.le), Real.inv_rpow hT0.le, inv_inv]
  rw [htail] at houter
  refine (norm_add_le _ _).trans ?_
  rw [hfin]
  have e : K * (1 / (s + 1) + m + 1 / ((m : ℝ) - s - 1)) * T ^ (s + 1)
      = K * (T ^ (s + 1) / (s + 1)) + ((m : ℝ) * (K * T ^ (s + 1))
        + K * (T ^ (s + 1) / ((m : ℝ) - s - 1))) := by ring
  rw [e]
  exact add_le_add hinner (houter.trans (add_le_add hsum le_rfl))

/-- info: 'FormalResearch.SignUncertainty.convS_ibp_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_ibp_tail

/-- info: 'FormalResearch.SignUncertainty.convS_ibp_iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_ibp_iter

/-- info: 'FormalResearch.SignUncertainty.convS_tail_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_tail_norm_le

/-- info: 'FormalResearch.SignUncertainty.convS_moment_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_moment_decay

/-- info: 'FormalResearch.SignUncertainty.convS_moment_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_moment_small

/-- info: 'FormalResearch.SignUncertainty.convS_contDiff_iteratedDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_contDiff_iteratedDeriv

/-- info: 'FormalResearch.SignUncertainty.convS_hasDerivAt_iteratedDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_hasDerivAt_iteratedDeriv

/-- info: 'FormalResearch.SignUncertainty.convS_iteratedDeriv_zero_of_le_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_iteratedDeriv_zero_of_le_gen

/-- info: 'FormalResearch.SignUncertainty.convS_integrableOn_rpow_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_integrableOn_rpow_exp

/-- info: 'FormalResearch.SignUncertainty.convS_integrableOn_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_integrableOn_poly

/-- info: 'FormalResearch.SignUncertainty.convS_tendsto_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_tendsto_poly

/-- info: 'FormalResearch.SignUncertainty.ConvMomentData.crude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConvMomentData.crude

/-- info: 'FormalResearch.SignUncertainty.convS_integral_Ioi_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_integral_Ioi_zero_eq

/-- info: 'FormalResearch.SignUncertainty.ConvMomentData.integrableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConvMomentData.integrableOn

end FormalResearch.SignUncertainty
