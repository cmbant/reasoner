module

public import FormalResearch.SignUncertainty.ConvSourceLaplace
public import FormalResearch.SignUncertainty.ConvSourceG1
public import FormalResearch.SignUncertainty.ConvSourceWeight

/-!
# Positivity, mass and negative tail of the convolution source `S_c` (M6, Lemma `O.12`, `ceo:conv`)

With `g₁ = ceG1 (airyZero 1)`, `w_c = γ ε e^{-y} + θ w_h` (`ConvSourceDefs`) and
`S_c(u) = ∫₀^∞ w_c(y) g₁(u + y) dy = convR w_c g₁ (u)` (`convSource_eq_convR`, `ConvSourceLaplace`),
this module proves the items (1)-(2) of `ceo:conv` in the `convR` form:

* `convSource_pos`: `S_c > 0` on `ℝ`;
* `convSource_integral`: `S_c` is integrable and `∫ S_c = ∫₀^∞ w_c`;
* `convSource_compact_floor`: `S_c(u) ≥ b γ ε` on `|u| ≤ U`, with `b > 0` depending on `U` only;
* `convSource_mass`: `|∫ S_c - (γ + θ B_p √λ) ε| ≤ C ε^{2p}` for `h = λ ε²`;
* `convSource_neg_tail_upper`, `convSource_neg_tail_lower`: the two-sided negative tail.

Positivity and the floor come from `g₁ > 0` on `[a₁, ∞)` and compactness; the upper tail splits the
integral at `y = x/2` and uses `g₁ ≤ C(1+|u|)^{-5/2}` and `∫ g₁ = 1`; the lower tail uses the window
`y ∈ (x, x+1]` on which `η = 1`, `ϱ(hy) ≥ ϱ(hx)` and `g₁(y - x) ≥ m > 0`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-! ### Elementary bounds on `e^{-y}`, the weight and the profile -/

/-- `e^{-y} ≤ 2 (1+y)^{-3/2}` for `y ≥ 0`. -/
lemma convSg_exp_neg_le {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-y) ≤ 2 * (1 + y) ^ (-(3 / 2 : ℝ)) := by
  have hx : 0 < 1 + y := by linarith
  have hq : (1 + y) ^ 2 / 2 ≤ Real.exp y := by
    nlinarith [Real.quadratic_le_exp_of_nonneg hy]
  have hpos : 0 < (1 + y) ^ 2 / 2 := by positivity
  have h1 : Real.exp (-y) ≤ ((1 + y) ^ 2 / 2)⁻¹ := by
    rw [Real.exp_neg]; exact inv_anti₀ hpos hq
  have h2 : ((1 + y) ^ 2 / 2)⁻¹ = 2 * ((1 + y) ^ (2 : ℝ))⁻¹ := by
    rw [Real.rpow_two, inv_div, div_eq_mul_inv]
  have h3 : ((1 + y) ^ (2 : ℝ))⁻¹ ≤ (1 + y) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_neg hx.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  linarith [h1, h2, h3]

/-- `((1+s)/2)^{-3/2} = 2^{3/2} (1+s)^{-3/2}` for `s ≥ 0`. -/
lemma convSg_half_pow {s : ℝ} (hs : 0 ≤ s) :
    ((1 + s) / 2) ^ (-(3 / 2 : ℝ)) = 2 ^ (3 / 2 : ℝ) * (1 + s) ^ (-(3 / 2 : ℝ)) := by
  rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 + s), div_inv_eq_mul]
  ring

/-- `y^{-3/2} ≤ 2^{3/2} (1+y)^{-3/2}` for `y ≥ 1`. -/
lemma convSg_pow_le_shift {y : ℝ} (hy : 1 ≤ y) :
    y ^ (-(3 / 2 : ℝ)) ≤ 2 ^ (3 / 2 : ℝ) * (1 + y) ^ (-(3 / 2 : ℝ)) := by
  have h := Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < (1 + y) / 2)
    (by linarith : (1 + y) / 2 ≤ y) (by norm_num : -(3 / 2 : ℝ) ≤ 0)
  rw [convSg_half_pow (by linarith)] at h
  exact h

/-- Pointwise bound for the long-range weight: `w_h(y) ≤ 2^{3/2}(1+y)^{-3/2}` for `y > 0`. -/
lemma convSg_wh_le_shift {p h : ℝ} (hp : 0 ≤ p) (hh : 0 ≤ h) {y : ℝ} (hy : 0 < y) :
    convWh p h y ≤ 2 ^ (3 / 2 : ℝ) * (1 + y) ^ (-(3 / 2 : ℝ)) := by
  by_cases hy1 : y ≤ 1
  · rw [convWh_eq_zero hy1]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by linarith) _)
  · push_neg at hy1
    exact (convWh_le hp hh hy).trans (convSg_pow_le_shift hy1.le)

/-- Pointwise bound for the full weight: `w_c(y) ≤ (2γ + 2^{3/2}θ)(1+y)^{-3/2}` for `y > 0`, `ε ≤ 1`. -/
lemma convSg_wc_le {p γ θ ε h : ℝ} (hp : 0 ≤ p) (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (hε1 : ε ≤ 1) (hh : 0 ≤ h)
    {y : ℝ} (hy : 0 < y) :
    convWc p γ θ ε h y ≤ (2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (1 + y) ^ (-(3 / 2 : ℝ)) := by
  unfold convWc
  have hE := convSg_exp_neg_le hy.le
  have hW := convSg_wh_le_shift hp hh hy
  have hexp := Real.exp_pos (-y)
  have h0 : ε * Real.exp (-y) ≤ 2 * (1 + y) ^ (-(3 / 2 : ℝ)) :=
    (by nlinarith : ε * Real.exp (-y) ≤ Real.exp (-y)).trans hE
  have hA : γ * ε * Real.exp (-y) ≤ γ * (2 * (1 + y) ^ (-(3 / 2 : ℝ))) := by
    calc γ * ε * Real.exp (-y) = γ * (ε * Real.exp (-y)) := by ring
      _ ≤ γ * (2 * (1 + y) ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_left h0 hγ
  have hB : θ * convWh p h y ≤ θ * (2 ^ (3 / 2 : ℝ) * (1 + y) ^ (-(3 / 2 : ℝ))) :=
    mul_le_mul_of_nonneg_left hW hθ
  have e : (2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (1 + y) ^ (-(3 / 2 : ℝ))
      = γ * (2 * (1 + y) ^ (-(3 / 2 : ℝ))) + θ * (2 ^ (3 / 2 : ℝ) * (1 + y) ^ (-(3 / 2 : ℝ))) := by
    ring
  rw [e]
  linarith [hA, hB]

/-- The profile `ϱ` is monotone in `t ≥ 0`. -/
lemma convSg_rho_mono {p s t : ℝ} (hp : 0 ≤ p) (hs : 0 ≤ s) (hst : s ≤ t) :
    convRho p s ≤ convRho p t := by
  unfold convRho
  apply Real.rpow_le_rpow (div_nonneg hs (by linarith)) _ hp
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-! ### Integrability and the `g₁` bounds -/

lemma convSg_exp_integrableOn : IntegrableOn (fun y : ℝ => Real.exp (-y)) (Ioi 0) := by
  simpa using exp_neg_integrableOn_Ioi 0 one_pos

lemma convSg_wc_integrableOn {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h) :
    IntegrableOn (convWc p γ θ ε h) (Ioi 0) := by
  unfold convWc
  exact (convSg_exp_integrableOn.const_mul (γ * ε)).add ((convW_integrable hp hp1 hh).const_mul θ)

lemma convSg_g1_bdd : ∃ M : ℝ, ∀ u : ℝ, ceG1 (airyZero 1) u ≤ M := by
  obtain ⟨C, hC0, hC⟩ := convG1_le_poly
  refine ⟨C, fun u => (hC u).trans ?_⟩
  exact mul_le_of_le_one_right hC0.le
    (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg u]) (by norm_num))

lemma convSg_mul_g1_integrableOn {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h) (u : ℝ) :
    IntegrableOn (fun y => convWc p γ θ ε h y * ceG1 (airyZero 1) (u + y)) (Ioi 0) := by
  obtain ⟨M, hM⟩ := convSg_g1_bdd
  have hw := convSg_wc_integrableOn (γ := γ) (θ := θ) (ε := ε) hp hp1 hh
  have hc : Continuous (fun y : ℝ => ceG1 (airyZero 1) (u + y)) :=
    (continuous_ceG1 (airyZero 1)).comp (continuous_const.add continuous_id)
  refine Integrable.mono' (hw.norm.mul_const M) (hw.1.mul hc.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y _
  rw [norm_mul, Real.norm_of_nonneg (convG1_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)

/-- A positive floor for `g₁` on `[0, 2T+1]` (compact, inside `[a₁, ∞)`). -/
lemma convSg_g1_floor {T : ℝ} (hT : 0 ≤ T) :
    ∃ m : ℝ, 0 < m ∧ ∀ v : ℝ, 0 ≤ v → v ≤ 2 * T + 1 → m ≤ ceG1 (airyZero 1) v := by
  obtain ⟨x, hx, hmin⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * T + 1)).exists_isMinOn
    (Set.nonempty_Icc.mpr (by linarith)) (continuous_ceG1 (airyZero 1)).continuousOn
  exact ⟨ceG1 (airyZero 1) x, convG1_pos_of_ge (le_trans (airyZero_neg 1).le hx.1),
    fun v hv0 hv1 => isMinOn_iff.mp hmin v ⟨hv0, hv1⟩⟩

/-- `∫ w_c` over `(0, ∞)` splits into the exponential and the long-range part. -/
lemma convSg_integral_wc {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h) :
    ∫ y in Ioi 0, convWc p γ θ ε h y = γ * ε + θ * ∫ y in Ioi 0, convWh p h y := by
  unfold convWc
  rw [integral_add (convSg_exp_integrableOn.const_mul (γ * ε))
    ((convW_integrable hp hp1 hh).const_mul θ), integral_const_mul, integral_const_mul,
    integral_exp_neg_Ioi_zero]
  ring

/-! ### Lower bounds for `S_c` -/

/-- Lower bound by a pointwise floor on a window `(a, b]` inside `(0, ∞)`. -/
lemma convSg_source_ge {p γ θ ε h u a b c : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 ≤ γ) (hθ : 0 ≤ θ)
    (hε : 0 ≤ ε) (hh : 0 < h) (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : ∀ y ∈ Ioc a b, c ≤ convWc p γ θ ε h y * ceG1 (airyZero 1) (u + y)) :
    c * (b - a) ≤ convSource p γ θ ε h u := by
  have hI := convSg_mul_g1_integrableOn (γ := γ) (θ := θ) (ε := ε) hp hp1 hh u
  have hsub : Ioc a b ⊆ Ioi 0 := fun y hy => lt_of_le_of_lt ha hy.1
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun y => convWc p γ θ ε h y * ceG1 (airyZero 1) (u + y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg (convWc_nonneg hγ hθ hε hh.le hy) (convG1_nonneg _)
  have h1 : ∫ y in Ioc a b, convWc p γ θ ε h y * ceG1 (airyZero 1) (u + y)
      ≤ convSource p γ θ ε h u :=
    setIntegral_mono_set hI hnn hsub.eventuallyLE
  have h2 := setIntegral_ge_of_const_le (μ := volume) measurableSet_Ioc
    (measure_Ioc_lt_top).ne hc (hI.mono_set hsub)
  rw [Real.volume_real_Ioc_of_le hab, smul_eq_mul] at h2
  calc c * (b - a) = (b - a) * c := mul_comm _ _
    _ ≤ _ := h2
    _ ≤ _ := h1

/-- Floor on a window `(T, T+1]` for `|u| ≤ T`. -/
lemma convSg_window {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 < γ) (hθ : 0 ≤ θ)
    (hε : 0 < ε) (hh : 0 < h) {T m : ℝ} (hT : 0 ≤ T) (hm0 : 0 ≤ m)
    (hm : ∀ v : ℝ, 0 ≤ v → v ≤ 2 * T + 1 → m ≤ ceG1 (airyZero 1) v) {u : ℝ} (hu : |u| ≤ T) :
    γ * ε * Real.exp (-(T + 1)) * m ≤ convSource p γ θ ε h u := by
  have hu1 := abs_le.mp hu
  have h := convSg_source_ge (u := u) (a := T) (b := T + 1) (c := γ * ε * Real.exp (-(T + 1)) * m)
    hp hp1 hγ.le hθ hε.le hh hT (by linarith) ?_
  · have e : T + 1 - T = 1 := by ring
    rw [e, mul_one] at h
    exact h
  · intro y hy
    have hy0 : T < y := hy.1
    have hy1 : y ≤ T + 1 := hy.2
    have hw : γ * ε * Real.exp (-(T + 1)) ≤ convWc p γ θ ε h y := by
      unfold convWc
      have e : Real.exp (-(T + 1)) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
      have h1 : γ * ε * Real.exp (-(T + 1)) ≤ γ * ε * Real.exp (-y) :=
        mul_le_mul_of_nonneg_left e (by positivity)
      have h2 : 0 ≤ θ * convWh p h y := mul_nonneg hθ (convWh_nonneg hh.le (by linarith))
      linarith
    have hg : m ≤ ceG1 (airyZero 1) (u + y) := hm _ (by linarith) (by linarith)
    exact mul_le_mul hw hg hm0 (convWc_nonneg hγ.le hθ hε.le hh.le (by linarith))

/-! ### Positivity, integrability and mass -/

/-- **Positivity:** `S_c(u) > 0` for every `u`. -/
theorem convSource_pos {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 < γ) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hε : 0 < ε) (hh : 0 < h) (u : ℝ) :
    0 < convSource p γ θ ε h u := by
  obtain ⟨m, hm, hfl⟩ := convSg_g1_floor (T := |u|) (abs_nonneg u)
  have hpos : 0 < γ * ε * Real.exp (-(|u| + 1)) * m :=
    mul_pos (mul_pos (mul_pos hγ hε) (Real.exp_pos _)) hm
  exact lt_of_lt_of_le hpos (convSg_window hp hp1 hγ hθ.le hε hh (abs_nonneg u) hm.le hfl le_rfl)

/-- **Integrability and mass identity:** `S_c` is integrable and `∫ S_c = ∫₀^∞ w_c`. -/
theorem convSource_integral {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h) :
    Integrable (convSource p γ θ ε h) ∧
      ∫ u, convSource p γ θ ε h u = ∫ y in Ioi 0, convWc p γ θ ε h y := by
  have hw : IntegrableOn (convWc p γ θ ε h) (Ioi 0) := convSg_wc_integrableOn hp hp1 hh
  have hX : Continuous (ceG1 (airyZero 1)) := continuous_ceG1 (airyZero 1)
  have hXi : Integrable (fun u : ℝ => ((ceG1 (airyZero 1) u : ℝ) : ℂ) * Complex.exp ((0:ℂ) * (u : ℂ))) := by
    simp only [zero_mul, Complex.exp_zero, mul_one]
    exact ceG1_integrable.ofReal
  obtain ⟨hint, heq⟩ := convR_twisted hw hX (z := 0) (by simp) hXi
  have hfun : (fun u : ℝ => (convR (convWc p γ θ ε h) (ceG1 (airyZero 1)) u : ℂ) * Complex.exp ((0:ℂ) * (u : ℂ)))
      = fun u : ℝ => (convR (convWc p γ θ ε h) (ceG1 (airyZero 1)) u : ℂ) := by
    funext u; simp
  have hI1 : ∫ u : ℝ, (convR (convWc p γ θ ε h) (ceG1 (airyZero 1)) u : ℂ) * Complex.exp ((0:ℂ) * (u : ℂ))
      = ((∫ u, convR (convWc p γ θ ε h) (ceG1 (airyZero 1)) u : ℝ) : ℂ) := by
    rw [hfun]; exact integral_complex_ofReal
  have hI2 : lapW (convWc p γ θ ε h) 0 * ∫ v : ℝ, ((ceG1 (airyZero 1) v : ℝ) : ℂ) * Complex.exp ((0:ℂ) * (v : ℂ))
      = ((∫ y in Ioi 0, convWc p γ θ ε h y : ℝ) : ℂ) := by
    have e1 : ∫ v : ℝ, ((ceG1 (airyZero 1) v : ℝ) : ℂ) * Complex.exp ((0:ℂ) * (v : ℂ)) = 1 := by
      simp only [zero_mul, Complex.exp_zero, mul_one]
      rw [integral_complex_ofReal, ceG1_integral_eq_one]
      simp
    have e2 : lapW (convWc p γ θ ε h) 0 = ((∫ y in Ioi 0, convWc p γ θ ε h y : ℝ) : ℂ) := by
      unfold lapW
      simp only [zero_mul, neg_zero, Complex.exp_zero, mul_one]
      exact integral_complex_ofReal
    rw [e1, e2, mul_one]
  have key := heq
  rw [hI1, hI2] at key
  have key' : ∫ u, convR (convWc p γ θ ε h) (ceG1 (airyZero 1)) u = ∫ y in Ioi 0, convWc p γ θ ε h y := by
    exact_mod_cast key
  have hintR : Integrable (convR (convWc p γ θ ε h) (ceG1 (airyZero 1))) := by
    rw [hfun] at hint
    simpa using hint.re
  rw [convSource_eq_convR]
  exact ⟨hintR, key'⟩

/-- Compact floor: `S_c(u) ≥ b γ ε` on `|u| ≤ U`, with `b > 0` independent of `p, θ, ε, h`. -/
theorem convSource_compact_floor {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 < γ) (hθ : 0 < θ)
    (hε : 0 < ε) (hh : 0 < h) (U : ℝ) :
    ∃ b : ℝ, 0 < b ∧ ∀ u : ℝ, |u| ≤ U → b * γ * ε ≤ convSource p γ θ ε h u := by
  obtain ⟨m, hm, hfl⟩ := convSg_g1_floor (T := |U|) (abs_nonneg U)
  refine ⟨Real.exp (-(|U| + 1)) * m, mul_pos (Real.exp_pos _) hm, fun u hu => ?_⟩
  have := convSg_window hp hp1 hγ hθ.le hε hh (abs_nonneg U) hm.le hfl (u := u) (hu.trans (le_abs_self U))
  calc Real.exp (-(|U| + 1)) * m * γ * ε = γ * ε * Real.exp (-(|U| + 1)) * m := by ring
    _ ≤ _ := this

/-- Upper negative tail: `S_c(-x) ≤ C (1+x)^{-3/2}` for `x ≥ 0`, `0 < ε ≤ 1`, `0 < h ≤ 1`. -/
theorem convSource_neg_tail_upper {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 < γ) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1) :
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → convSource p γ θ ε h (-x) ≤ C * (1 + x) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C₁, hC₁, hC⟩ := convG1_le_poly
  have hK2 : 0 ≤ 2 * γ + 2 ^ (3 / 2 : ℝ) * θ := by positivity
  refine ⟨(2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (C₁ + 1) * 2 ^ (3 / 2 : ℝ), fun x hx => ?_⟩
  have hx1 : 0 < 1 + x / 2 := by linarith
  have hQ : 0 ≤ (1 + x / 2) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hx1.le _
  have hR : 0 ≤ (1 + x / 2) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hx1.le _
  have hI := convSg_mul_g1_integrableOn (γ := γ) (θ := θ) (ε := ε) hp hp1 hh (-x)
  have hsplit : Ioi (0:ℝ) = Ioc 0 (x / 2) ∪ Ioi (x / 2) := (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  have hsub1 : Ioc (0:ℝ) (x / 2) ⊆ Ioi 0 := Set.Ioc_subset_Ioi_self
  have hsub2 : Ioi (x / 2) ⊆ Ioi (0:ℝ) := Set.Ioi_subset_Ioi (by linarith)
  -- piece 1: `0 < y ≤ x/2`, where `|-x+y| ≥ x/2`
  have P1 : ∫ y in Ioc (0:ℝ) (x / 2), convWc p γ θ ε h y * ceG1 (airyZero 1) (-x + y)
      ≤ (x / 2) * ((2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (C₁ * (1 + x / 2) ^ (-(5 / 2 : ℝ)))) := by
    have hpt : ∀ y ∈ Ioc (0:ℝ) (x / 2), convWc p γ θ ε h y * ceG1 (airyZero 1) (-x + y)
        ≤ (2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (C₁ * (1 + x / 2) ^ (-(5 / 2 : ℝ))) := by
      intro y hy
      have hy0 : 0 < y := hy.1
      have hy2 : y ≤ x / 2 := hy.2
      have hw1 : convWc p γ θ ε h y ≤ 2 * γ + 2 ^ (3 / 2 : ℝ) * θ :=
        (convSg_wc_le (by linarith) hγ.le hθ.le hε1 hh.le hy0).trans
          (mul_le_of_le_one_right hK2 (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)))
      have hg1 : ceG1 (airyZero 1) (-x + y) ≤ C₁ * (1 + x / 2) ^ (-(5 / 2 : ℝ)) := by
        refine (hC (-x + y)).trans (mul_le_mul_of_nonneg_left ?_ hC₁.le)
        exact Real.rpow_le_rpow_of_nonpos hx1 (by rw [abs_of_nonpos (by linarith)]; linarith) (by norm_num)
      exact mul_le_mul hw1 hg1 (convG1_nonneg _) hK2
    calc ∫ y in Ioc (0:ℝ) (x / 2), convWc p γ θ ε h y * ceG1 (airyZero 1) (-x + y)
        ≤ ∫ _ in Ioc (0:ℝ) (x / 2), (2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (C₁ * (1 + x / 2) ^ (-(5 / 2 : ℝ))) :=
          setIntegral_mono_on (hI.mono_set hsub1) (integrableOn_const measure_Ioc_lt_top.ne)
            measurableSet_Ioc hpt
      _ = (x / 2) * ((2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (C₁ * (1 + x / 2) ^ (-(5 / 2 : ℝ)))) := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul]
          ring
  -- piece 2: `y > x/2`, where `(1+y)^{-3/2} ≤ (1+x/2)^{-3/2}`
  have P2 : ∫ y in Ioi (x / 2), convWc p γ θ ε h y * ceG1 (airyZero 1) (-x + y)
      ≤ (2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (1 + x / 2) ^ (-(3 / 2 : ℝ)) := by
    have hgi : Integrable (fun y : ℝ => ceG1 (airyZero 1) (-x + y)) :=
      ceG1_integrable.comp_add_left (-x)
    have hgint : ∫ y : ℝ, ceG1 (airyZero 1) (-x + y) = 1 := by
      rw [integral_add_left_eq_self (ceG1 (airyZero 1)) (-x)]
      exact ceG1_integral_eq_one
    have hpt2 : ∀ y ∈ Ioi (x / 2), convWc p γ θ ε h y * ceG1 (airyZero 1) (-x + y)
        ≤ ((2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (1 + x / 2) ^ (-(3 / 2 : ℝ))) * ceG1 (airyZero 1) (-x + y) := by
      intro y hy
      have hy' : x / 2 < y := hy
      have hy0 : 0 < y := by linarith
      have hpow : (1 + y) ^ (-(3 / 2 : ℝ)) ≤ (1 + x / 2) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hx1 (by linarith) (by norm_num)
      exact mul_le_mul_of_nonneg_right
        ((convSg_wc_le (by linarith) hγ.le hθ.le hε1 hh.le hy0).trans (mul_le_mul_of_nonneg_left hpow hK2))
        (convG1_nonneg _)
    calc ∫ y in Ioi (x / 2), convWc p γ θ ε h y * ceG1 (airyZero 1) (-x + y)
        ≤ ∫ y in Ioi (x / 2), ((2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (1 + x / 2) ^ (-(3 / 2 : ℝ)))
            * ceG1 (airyZero 1) (-x + y) :=
          setIntegral_mono_on (hI.mono_set hsub2) (hgi.const_mul _).integrableOn measurableSet_Ioi hpt2
      _ = ((2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (1 + x / 2) ^ (-(3 / 2 : ℝ)))
            * ∫ y in Ioi (x / 2), ceG1 (airyZero 1) (-x + y) := by
          rw [integral_const_mul]
      _ ≤ ((2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (1 + x / 2) ^ (-(3 / 2 : ℝ)))
            * ∫ y : ℝ, ceG1 (airyZero 1) (-x + y) :=
          mul_le_mul_of_nonneg_left (setIntegral_le_integral hgi (Eventually.of_forall fun y => convG1_nonneg _))
            (mul_nonneg hK2 hR)
      _ = (2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (1 + x / 2) ^ (-(3 / 2 : ℝ)) := by rw [hgint, mul_one]
  -- `(x/2) Q ≤ R` with `Q = (1+x/2)^{-5/2}`, `R = (1+x/2)^{-3/2}`
  have hQR : (x / 2) * (1 + x / 2) ^ (-(5 / 2 : ℝ)) ≤ (1 + x / 2) ^ (-(3 / 2 : ℝ)) := by
    have e : (1 + x / 2) ^ (-(3 / 2 : ℝ)) = (1 + x / 2) ^ (-(5 / 2 : ℝ)) * (1 + x / 2) := by
      rw [← Real.rpow_add_one hx1.ne']; norm_num
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right (show x / 2 ≤ 1 + x / 2 by linarith) hQ]
  have hR2 : (1 + x / 2) ^ (-(3 / 2 : ℝ)) ≤ 2 ^ (3 / 2 : ℝ) * (1 + x) ^ (-(3 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < (1 + x) / 2)
      (by linarith : (1 + x) / 2 ≤ 1 + x / 2) (by norm_num : -(3 / 2 : ℝ) ≤ 0)
    rw [convSg_half_pow hx] at h
    exact h
  have hKC : 0 ≤ (2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * C₁ := mul_nonneg hK2 hC₁.le
  have A1 : (x / 2) * ((2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (C₁ * (1 + x / 2) ^ (-(5 / 2 : ℝ))))
      ≤ (2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * C₁ * (1 + x / 2) ^ (-(3 / 2 : ℝ)) := by
    calc (x / 2) * ((2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (C₁ * (1 + x / 2) ^ (-(5 / 2 : ℝ))))
        = ((2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * C₁) * ((x / 2) * (1 + x / 2) ^ (-(5 / 2 : ℝ))) := by ring
      _ ≤ ((2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * C₁) * (1 + x / 2) ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hQR hKC
  have A3 : (2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (C₁ + 1) * (1 + x / 2) ^ (-(3 / 2 : ℝ))
      ≤ (2 * γ + 2 ^ (3 / 2 : ℝ) * θ) * (C₁ + 1) * (2 ^ (3 / 2 : ℝ) * (1 + x) ^ (-(3 / 2 : ℝ))) :=
    mul_le_mul_of_nonneg_left hR2 (mul_nonneg hK2 (by linarith))
  unfold convSource
  rw [hsplit, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi (hI.mono_set hsub1)
    (hI.mono_set hsub2)]
  nlinarith [P1, P2, A1, A3]

/-- Lower negative tail: `S_c(-x) ≥ b θ ϱ(hx) x^{-3/2}` for `x ≥ 4`. -/
theorem convSource_neg_tail_lower {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 < γ) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hε : 0 < ε) (hh : 0 < h) :
    ∃ b : ℝ, 0 < b ∧ ∀ x : ℝ, 4 ≤ x →
      b * θ * convRho p (h * x) * x ^ (-(3 / 2 : ℝ)) ≤ convSource p γ θ ε h (-x) := by
  obtain ⟨m, hm, hfl⟩ := convSg_g1_floor (T := 1) zero_le_one
  have hc5 : 0 < (5 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨(5 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * m, mul_pos hc5 hm, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  -- on the window `y ∈ (x, x+1]`: `w_h(y) ≥ c5 ϱ(hx) x^{-3/2}`
  have hwh : ∀ y ∈ Ioc x (x + 1), (5 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * convRho p (h * x) * x ^ (-(3 / 2 : ℝ))
      ≤ convWh p h y := by
    intro y hy
    have hy1 : x < y := hy.1
    have hy2 : y ≤ x + 1 := hy.2
    have hy0 : 0 < y := by linarith
    have hη : convEta y = 1 := convEta_eq_one (by linarith)
    have hρ : convRho p (h * x) ≤ convRho p (h * y) :=
      convSg_rho_mono (by linarith) (mul_nonneg hh.le hx0.le) (mul_le_mul_of_nonneg_left hy1.le hh.le)
    have hpow : (5 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ)) ≤ y ^ (-(3 / 2 : ℝ)) := by
      have h := Real.rpow_le_rpow_of_nonpos hy0 (by linarith : y ≤ 5 / 4 * x) (by norm_num : -(3 / 2 : ℝ) ≤ 0)
      rw [Real.mul_rpow (by norm_num) hx0.le] at h
      exact h
    have e2 : convRho p (h * y) / y ^ (3 / 2 : ℝ) = convRho p (h * y) * y ^ (-(3 / 2 : ℝ)) := by
      rw [Real.rpow_neg hy0.le, div_eq_mul_inv]
    unfold convWh
    rw [hη, one_mul, e2]
    calc (5 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * convRho p (h * x) * x ^ (-(3 / 2 : ℝ))
        = convRho p (h * x) * ((5 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ))) := by ring
      _ ≤ convRho p (h * y) * y ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul hρ hpow (mul_nonneg hc5.le (Real.rpow_nonneg hx0.le _))
            (convRho_nonneg p (mul_nonneg hh.le hy0.le))
  have hI := convSg_source_ge (u := -x) (a := x) (b := x + 1)
    (c := θ * ((5 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * convRho p (h * x) * x ^ (-(3 / 2 : ℝ))) * m)
    hp hp1 hγ.le hθ.le hε.le hh hx0.le (by linarith) ?_
  · have e : x + 1 - x = 1 := by ring
    rw [e, mul_one] at hI
    calc (5 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * m * θ * convRho p (h * x) * x ^ (-(3 / 2 : ℝ))
        = θ * ((5 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * convRho p (h * x) * x ^ (-(3 / 2 : ℝ))) * m := by ring
      _ ≤ _ := hI
  · intro y hy
    have hy1 : x < y := hy.1
    have hy2 : y ≤ x + 1 := hy.2
    have hw : θ * ((5 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * convRho p (h * x) * x ^ (-(3 / 2 : ℝ)))
        ≤ convWc p γ θ ε h y := by
      unfold convWc
      have h1 := mul_le_mul_of_nonneg_left (hwh y hy) hθ.le
      have h2 : 0 ≤ γ * ε * Real.exp (-y) := mul_nonneg (mul_nonneg hγ.le hε.le) (Real.exp_pos _).le
      linarith
    have hg : m ≤ ceG1 (airyZero 1) (-x + y) := hfl _ (by linarith) (by linarith)
    exact mul_le_mul hw hg hm.le (convWc_nonneg hγ.le hθ.le hε.le hh.le (by linarith))

/-- **Mass:** `|∫ S_c - (γ + θ B_p √λ) ε| ≤ C ε^{2p}` for `h = λ ε²`, `0 < ε ≤ ε₀`. -/
theorem convSource_mass {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 < γ) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hlam : 0 < lam) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      |(∫ u, convSource p γ θ ε (lam * ε ^ 2) u) - (γ + θ * convBp p * Real.sqrt lam) * ε|
        ≤ C * ε ^ (2 * p) := by
  obtain ⟨Cm, hCm⟩ := convW_mass hp hp1
  have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  refine ⟨|Cm| * lam ^ p, 1 / Real.sqrt lam, by positivity, fun ε hε hεε => ?_⟩
  have hh : 0 < lam * ε ^ 2 := mul_pos hlam (by positivity)
  have hh1 : lam * ε ^ 2 ≤ 1 := by
    have h1 : ε ^ 2 ≤ (1 / Real.sqrt lam) ^ 2 := pow_le_pow_left₀ hε.le hεε 2
    have e : (1 / Real.sqrt lam) ^ 2 = 1 / lam := by
      rw [div_pow, one_pow, Real.sq_sqrt hlam.le]
    have h2 := mul_le_mul_of_nonneg_left h1 hlam.le
    rw [e, mul_one_div_cancel hlam.ne'] at h2
    exact h2
  have hmass := (convSource_integral (p := p) (γ := γ) (θ := θ) (ε := ε) (h := lam * ε ^ 2) hp hp1 hh).2
  rw [hmass, convSg_integral_wc hp hp1 hh]
  have hC := hCm (lam * ε ^ 2) hh hh1
  have hsq : Real.sqrt (lam * ε ^ 2) = Real.sqrt lam * ε := by
    rw [Real.sqrt_mul hlam.le, Real.sqrt_sq hε.le]
  have e2 : ε ^ (2 * p) = (ε ^ 2) ^ p := by
    rw [Real.rpow_mul hε.le, Real.rpow_two]
  have hpow : (lam * ε ^ 2) ^ p = lam ^ p * ε ^ (2 * p) := by
    rw [Real.mul_rpow hlam.le (by positivity), e2]
  rw [hsq, hpow] at hC
  have hP : 0 ≤ lam ^ p * ε ^ (2 * p) := mul_nonneg (Real.rpow_nonneg hlam.le _) (Real.rpow_nonneg hε.le _)
  have key : γ * ε + θ * (∫ y in Ioi 0, convWh p (lam * ε ^ 2) y) - (γ + θ * convBp p * Real.sqrt lam) * ε
      = θ * ((∫ y in Ioi 0, convWh p (lam * ε ^ 2) y) - Real.sqrt lam * ε * convBp p) := by
    ring
  rw [key, abs_mul, abs_of_nonneg hθ.le]
  calc θ * |(∫ y in Ioi 0, convWh p (lam * ε ^ 2) y) - Real.sqrt lam * ε * convBp p|
      ≤ 1 * |(∫ y in Ioi 0, convWh p (lam * ε ^ 2) y) - Real.sqrt lam * ε * convBp p| :=
        mul_le_mul_of_nonneg_right hθ1 (abs_nonneg _)
    _ = |(∫ y in Ioi 0, convWh p (lam * ε ^ 2) y) - Real.sqrt lam * ε * convBp p| := one_mul _
    _ ≤ Cm * (lam ^ p * ε ^ (2 * p)) := hC
    _ ≤ |Cm| * (lam ^ p * ε ^ (2 * p)) := mul_le_mul_of_nonneg_right (le_abs_self Cm) hP
    _ = |Cm| * lam ^ p * ε ^ (2 * p) := by ring

/-- info: 'FormalResearch.SignUncertainty.convSource_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convSource_pos

/-- info: 'FormalResearch.SignUncertainty.convSource_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convSource_integral

/-- info: 'FormalResearch.SignUncertainty.convSource_compact_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convSource_compact_floor

/-- info: 'FormalResearch.SignUncertainty.convSource_neg_tail_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convSource_neg_tail_upper

/-- info: 'FormalResearch.SignUncertainty.convSource_neg_tail_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convSource_neg_tail_lower

/-- info: 'FormalResearch.SignUncertainty.convSource_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convSource_mass

end FormalResearch.SignUncertainty
