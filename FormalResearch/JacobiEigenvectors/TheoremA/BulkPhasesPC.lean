module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.ParabolicCylinder

/-!
# Paper J, Layer 2: special-function lemmas for the bulk phases (`lem:smo-bulkphase` (1), the model-function part)

Source: Paper J `app_thmA.tex`, proof of `lem:smo-bulkphase` (1): "the trigonometric expansion (DLMF 12.10.18) ... gives
`U(-mu^2/2, mu t sqrt 2) = 2g(mu)/(1-t^2)^{1/4} [cos(mu^2 eta(t) - pi/4) + O(mu^{-2})]`; ... since `2u eta(y/(2 sqrt u)) = int_y^{2 sqrt u} sqrt(u - s^2/4) ds`...;
the corrector term is `O(h)` times the same envelope since `|d_z U| <= C mu |U|_env` on compact `t`-sets".

## Proved here (all from `ParabolicCylinderFacts` and Mathlib; nothing is added to `ParabolicCylinderFacts`)

* `integral_sqrt_sub_sq` (**the calculus identity of the paper**): `int_{2 sqrt u t}^{2 sqrt u} sqrt(u - s^2/4) ds = u (arccos t - t sqrt(1-t^2))`, `u > 0`, `|t| <= 1`; i.e. `mu^2 eta(t) = Theta_L/h`.
* `landau_deriv`: a pure interpolation bound: `|f'(z)| <= 2B/s + s Lam B` from `|f| <= B` and `|f''| <= Lam B` on `[z, z+s]`.
* `phase_deriv_bound` (**finding F-S1-2, refined**): the derivative of `U` needs no new field.  From `phase_osc` alone (with `eps/2`) and the differential equation `U'' = (z^2/4 + a) U` (`ode_U`),
  `|U'(-mu^2/2, mu t sqrt 2)| <= C mu 2 g(mu)` for `|t| <= 1 - eps`, `mu >= mu_1` (Landau interpolation on a window of length `1/mu`).  The *envelope* bound is all that the
  corrector term `h B h^{1/2} U'` needs; the *phase* of `U'` (DLMF 12.10.19) is not used by the formalisation.
* `EU_lower` (**the lower bound for the envelope**): for `a <= 0` and `|z| <= 2 sqrt(-a)` (both signs of `z`), `kappa_bal(a) sqrt(U^2 + U'^2/k_2) >= M_bal(a,z)/((sqrt(pi/2) + 1) c_PC...)`,
  from the Wronskian `wronsk`, the envelope bound `env_well` for `U` and `V` on `z >= 0` and the connection formulae `reflect`, `reflect_V` for `z < 0`.  With `phase_deriv_bound` this gives
  `kappa_bal 2 g(mu) (1-t^2)^{-1/4} >= c M_bal` (the paper's `rho >~ h^{1/4}`; `phase_osc` has `g` existential).

## Not formalised

DLMF 12.10.19 (the phase of `U'`), the explicit `g(mu)`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Set Real intervalIntegral

/-! ### The calculus identity -/

/-- `d/dt [(t sqrt(1-t^2) + arcsin t)/2] = sqrt(1-t^2)` on `(-1,1)`. -/
lemma hasDerivAt_antideriv {t : ℝ} (h1 : -1 < t) (h2 : t < 1) :
    HasDerivAt (fun x : ℝ => (x * Real.sqrt (1 - x ^ 2) + Real.arcsin x) / 2) (Real.sqrt (1 - t ^ 2)) t := by
  have hpos : 0 < 1 - t ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr hpos
  have hsq := Real.sq_sqrt hpos.le
  have h1' : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * t)) t := by
    simpa using ((hasDerivAt_pow 2 t).const_sub 1)
  have h2' := h1'.sqrt hpos.ne'
  have h3 := ((hasDerivAt_id t).mul h2').add (Real.hasDerivAt_arcsin h1.ne' h2.ne)
  have h4 := h3.div_const 2
  have h5 : HasDerivAt (fun x : ℝ => (x * Real.sqrt (1 - x ^ 2) + Real.arcsin x) / 2)
      ((1 * Real.sqrt (1 - t ^ 2) + t * (-(2 * t) / (2 * Real.sqrt (1 - t ^ 2))) + 1 / Real.sqrt (1 - t ^ 2)) / 2) t := h4
  refine h5.congr_deriv ?_
  field_simp
  nlinarith [hsq]

/-- `int_t^1 sqrt(1 - x^2) dx = (arccos t - t sqrt(1-t^2))/2`, `-1 <= t <= 1`. -/
lemma integral_sqrt_one_sub_sq_Ioi {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    ∫ x in t..1, Real.sqrt (1 - x ^ 2) = (Real.arccos t - t * Real.sqrt (1 - t ^ 2)) / 2 := by
  rcases h2.eq_or_lt with rfl | hlt
  · simp
  have hcont : ContinuousOn (fun x : ℝ => (x * Real.sqrt (1 - x ^ 2) + Real.arcsin x) / 2) (Icc t 1) := by
    have : Continuous (fun x : ℝ => (x * Real.sqrt (1 - x ^ 2) + Real.arcsin x) / 2) := by fun_prop
    exact this.continuousOn
  have hd : ∀ x ∈ Ioo t 1, HasDerivAt (fun x : ℝ => (x * Real.sqrt (1 - x ^ 2) + Real.arcsin x) / 2) (Real.sqrt (1 - x ^ 2)) x :=
    fun x hx => hasDerivAt_antideriv (by linarith [hx.1]) hx.2
  have hint : IntervalIntegrable (fun x : ℝ => Real.sqrt (1 - x ^ 2)) MeasureTheory.volume t 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [integral_eq_sub_of_hasDerivAt_of_le hlt.le hcont hd hint]
  simp only [Real.sqrt_zero, mul_zero, zero_add, one_pow, sub_self, Real.arcsin_one]
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  ring

/-- **The calculus identity of `lem:smo-bulkphase` (1)**: `int_{2 sqrt u t}^{2 sqrt u} sqrt(u - s^2/4) ds = u (arccos t - t sqrt(1-t^2))`. -/
lemma integral_sqrt_sub_sq {u t : ℝ} (hu : 0 < u) (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    ∫ s in (2 * Real.sqrt u * t)..(2 * Real.sqrt u), Real.sqrt (u - s ^ 2 / 4)
      = u * (Real.arccos t - t * Real.sqrt (1 - t ^ 2)) := by
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hc : (2 * Real.sqrt u) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left (a := t) (b := 1)
    (fun s : ℝ => Real.sqrt (u - s ^ 2 / 4)) hc
  rw [mul_one, smul_eq_mul] at this
  have this' : ∫ s in (2 * Real.sqrt u * t)..(2 * Real.sqrt u), Real.sqrt (u - s ^ 2 / 4)
      = (2 * Real.sqrt u) * ∫ x in t..1, Real.sqrt (u - (2 * Real.sqrt u * x) ^ 2 / 4) := by
    rw [this]; field_simp
  rw [this']
  have hrw : ∀ x : ℝ, Real.sqrt (u - (2 * Real.sqrt u * x) ^ 2 / 4) = Real.sqrt u * Real.sqrt (1 - x ^ 2) := by
    intro x
    have hsq := Real.sq_sqrt hu.le
    rw [← Real.sqrt_mul hu.le]
    congr 1
    nlinarith [hsq]
  simp_rw [hrw]
  rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq_Ioi h1 h2]
  have hsq := Real.sq_sqrt hu.le
  field_simp
  rw [hsq]
  ring

/-! ### Landau interpolation -/

/-- `|f'(z)| <= 2B/s + s D` from `|f| <= B` and `|f''| <= D` on `[z, z+s]`. -/
lemma landau_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f)) {z s B D : ℝ} (hs : 0 < s)
    (hB : ∀ w ∈ Icc z (z + s), |f w| ≤ B) (hD : ∀ w ∈ Icc z (z + s), |deriv (deriv f) w| ≤ D) :
    |deriv f z| ≤ 2 * B / s + s * D := by
  have hzz : z < z + s := by linarith
  obtain ⟨ξ, hξ, hξe⟩ := exists_deriv_eq_slope f hzz hf.continuous.continuousOn
    (fun x _ => hf.differentiableAt.differentiableWithinAt)
  have hξ' : ξ ∈ Icc z (z + s) := ⟨hξ.1.le, hξ.2.le⟩
  have h1 : |deriv f ξ| ≤ 2 * B / s := by
    rw [hξe]
    have e : z + s - z = s := by ring
    rw [e, abs_div, abs_of_pos hs, div_le_div_iff_of_pos_right hs]
    calc |f (z + s) - f z| ≤ |f (z + s)| + |f z| := abs_sub _ _
      _ ≤ B + B := add_le_add (hB _ ⟨hzz.le, le_rfl⟩) (hB _ ⟨le_rfl, hzz.le⟩)
      _ = 2 * B := by ring
  have h2 : |deriv f z - deriv f ξ| ≤ D * |z - ξ| := by
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv f) (s := Icc z (z + s)) (C := D)
      (fun x _ => hf'.differentiableAt) (fun x hx => by simpa using hD x hx) (convex_Icc _ _)
      hξ' ⟨le_rfl, hzz.le⟩
    simpa [Real.norm_eq_abs, abs_sub_comm] using this
  have h3 : |z - ξ| ≤ s := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hξ.1])]
    linarith [hξ.2]
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD z ⟨le_rfl, hzz.le⟩)
  calc |deriv f z| = |deriv f ξ + (deriv f z - deriv f ξ)| := by ring_nf
    _ ≤ |deriv f ξ| + |deriv f z - deriv f ξ| := abs_add_le _ _
    _ ≤ 2 * B / s + D * s := add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left h3 hD0))
    _ = 2 * B / s + s * D := by ring

/-! ### The derivative of the Weber branch on the oscillatory range (finding F-S1-2, refined) -/

section Phase

variable {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

lemma U_differentiable (PC : ParabolicCylinderFacts U V cPC CPC) (a : ℝ) : ContDiff ℝ ⊤ (U a) := by
  have h : ContDiff ℝ ⊤ (fun z : ℝ => U a z) :=
    PC.smooth_U.comp (contDiff_const.prodMk contDiff_id)
  exact h

lemma U_deriv_differentiable (PC : ParabolicCylinderFacts U V cPC CPC) (a : ℝ) : Differentiable ℝ (deriv (U a)) := by
  have h2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (U a) := (U_differentiable PC a).of_le le_top
  exact ((contDiff_succ_iff_deriv (n := 1)).mp h2).2.2.differentiable (by norm_num)

/-- **Value and derivative bounds on the oscillatory range, from `phase_osc` and the differential equation.**  Suppose the expansion of `phase_osc` holds for `|t| <= 1 - eps/2`
and `mu >= mu0`, `mu >= 1`.  Then for `|t| <= 1 - eps`, `mu^2 >= 2/eps` and `mu >= 1`, with `G = 2 g(mu)`:
`|U(-mu^2/2, mu t sqrt 2)| <= B G` and `|U'(-mu^2/2, mu t sqrt 2)| <= 3 B mu G`, `B = (2/eps)^{1/4} (1 + C)`. -/
lemma phase_value_deriv_bound (PC : ParabolicCylinderFacts U V cPC CPC) {ε C μ0 : ℝ} {g : ℝ → ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hg : ∀ μ, 0 < g μ)
    (hph : ∀ μ : ℝ, μ0 ≤ μ → ∀ t : ℝ, |t| ≤ 1 - ε / 2 →
      |U (-(μ ^ 2) / 2) (μ * t * Real.sqrt 2) - 2 * g μ / (1 - t ^ 2) ^ ((1 : ℝ) / 4)
        * Real.cos (μ ^ 2 * ((Real.arccos t - t * Real.sqrt (1 - t ^ 2)) / 2) - Real.pi / 4)|
        ≤ C * μ⁻¹ ^ 2 * (2 * g μ / (1 - t ^ 2) ^ ((1 : ℝ) / 4)))
    (hC : 0 ≤ C) {μ t : ℝ} (hμ0 : μ0 ≤ μ) (hμ1 : 1 ≤ μ) (hμε : 2 / ε ≤ μ ^ 2) (ht : |t| ≤ 1 - ε) :
    |U (-(μ ^ 2) / 2) (μ * t * Real.sqrt 2)| ≤ (2 / ε) ^ ((1 : ℝ) / 4) * (1 + C) * (2 * g μ) ∧
    |deriv (U (-(μ ^ 2) / 2)) (μ * t * Real.sqrt 2)| ≤ 3 * ((2 / ε) ^ ((1 : ℝ) / 4) * (1 + C) * (2 * g μ)) * μ := by
  set B : ℝ := (2 / ε) ^ ((1 : ℝ) / 4) * (1 + C) * (2 * g μ) with hB
  have hμpos : 0 < μ := by linarith
  have hgpos := hg μ
  -- bound on the window `t' in [-(1-eps/2), 1-eps/2]`
  have hwin : ∀ t' : ℝ, |t'| ≤ 1 - ε / 2 → |U (-(μ ^ 2) / 2) (μ * t' * Real.sqrt 2)| ≤ B := by
    intro t' ht'
    have h := hph μ hμ0 t' ht'
    have h1t : 0 < 1 - t' ^ 2 := by nlinarith [abs_nonneg t', sq_abs t']
    have hlow : ε / 2 ≤ 1 - t' ^ 2 := by
      have : t' ^ 2 ≤ (1 - ε / 2) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ht' 2
      nlinarith
    set amp := 2 * g μ / (1 - t' ^ 2) ^ ((1 : ℝ) / 4) with hamp
    have hampB : amp ≤ (2 / ε) ^ ((1 : ℝ) / 4) * (2 * g μ) := by
      rw [hamp, div_eq_mul_inv]
      have hz : 0 < (1 - t' ^ 2) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos h1t _
      have hle : (2 / ε)⁻¹ ^ ((1 : ℝ) / 4) ≤ (1 - t' ^ 2) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by positivity) (by rw [inv_div]; linarith) (by norm_num)
      have : ((1 - t' ^ 2) ^ ((1 : ℝ) / 4))⁻¹ ≤ (2 / ε) ^ ((1 : ℝ) / 4) := by
        have h2 : ((2 / ε)⁻¹ ^ ((1 : ℝ) / 4))⁻¹ = (2 / ε) ^ ((1 : ℝ) / 4) := by
          rw [← Real.inv_rpow (by positivity), inv_inv]
        rw [← h2]
        exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) hle
      calc 2 * g μ * ((1 - t' ^ 2) ^ ((1 : ℝ) / 4))⁻¹ ≤ 2 * g μ * (2 / ε) ^ ((1 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = (2 / ε) ^ ((1 : ℝ) / 4) * (2 * g μ) := by ring
    have hamp0 : 0 ≤ amp := by positivity
    have hcos := Real.abs_cos_le_one (μ ^ 2 * ((Real.arccos t' - t' * Real.sqrt (1 - t' ^ 2)) / 2) - Real.pi / 4)
    have hinv : C * μ⁻¹ ^ 2 ≤ C := by
      have : μ⁻¹ ^ 2 ≤ 1 := by
        have : μ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hμ1
        have h0 : 0 ≤ μ⁻¹ := inv_nonneg.mpr hμpos.le
        nlinarith
      nlinarith
    calc |U (-(μ ^ 2) / 2) (μ * t' * Real.sqrt 2)|
        ≤ |amp * Real.cos (μ ^ 2 * ((Real.arccos t' - t' * Real.sqrt (1 - t' ^ 2)) / 2) - Real.pi / 4)|
          + C * μ⁻¹ ^ 2 * amp := by
          have := abs_sub_abs_le_abs_sub (U (-(μ ^ 2) / 2) (μ * t' * Real.sqrt 2))
            (amp * Real.cos (μ ^ 2 * ((Real.arccos t' - t' * Real.sqrt (1 - t' ^ 2)) / 2) - Real.pi / 4))
          linarith
      _ ≤ amp + C * amp := by
          rw [abs_mul, abs_of_nonneg hamp0]
          have := mul_le_mul_of_nonneg_left hcos hamp0
          nlinarith [mul_le_mul_of_nonneg_right hinv hamp0]
      _ = (1 + C) * amp := by ring
      _ ≤ (1 + C) * ((2 / ε) ^ ((1 : ℝ) / 4) * (2 * g μ)) := mul_le_mul_of_nonneg_left hampB (by linarith)
      _ = B := by rw [hB]; ring
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hεμ : 2 ≤ ε * μ ^ 2 := by
    have := (div_le_iff₀ hε0).mp hμε
    linarith
  have hsq2 : 1 ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hkey : 1 ≤ ε / 2 * (μ * Real.sqrt 2) * μ := by
    have h1 : ε * μ ^ 2 ≤ ε * μ ^ 2 * Real.sqrt 2 := le_mul_of_one_le_right (by positivity) hsq2
    have : ε / 2 * (μ * Real.sqrt 2) * μ = (ε * μ ^ 2 * Real.sqrt 2) / 2 := by ring
    rw [this]; linarith
  refine ⟨hwin t (by linarith), ?_⟩
  -- Landau on the window `[Z, Z + 1/mu]`
  set Z : ℝ := μ * t * Real.sqrt 2 with hZ
  set s : ℝ := 1 / μ with hs
  have hspos : 0 < s := by positivity
  have hwin2 : ∀ w ∈ Icc Z (Z + s), |U (-(μ ^ 2) / 2) w| ≤ B := by
    intro w hw
    set t' : ℝ := w / (μ * Real.sqrt 2) with ht'
    have hs2 : 0 < Real.sqrt 2 := by positivity
    have hw' : w = μ * t' * Real.sqrt 2 := by rw [ht']; field_simp
    have hdiff : t' - t = (w - Z) / (μ * Real.sqrt 2) := by rw [ht', hZ]; field_simp
    have hwZ : 0 ≤ w - Z := by linarith [hw.1]
    have hwZ2 : w - Z ≤ 1 / μ := by linarith [hw.2]
    have hd0 : 0 ≤ t' - t := by rw [hdiff]; positivity
    have hd1 : t' - t ≤ ε / 2 := by
      rw [hdiff, div_le_iff₀ (by positivity)]
      have : 1 / μ ≤ ε / 2 * (μ * Real.sqrt 2) := by
        rw [div_le_iff₀ hμpos]
        linarith [hkey]
      linarith
    have habs : |t'| ≤ 1 - ε / 2 := by
      rw [abs_le]
      have := abs_le.mp ht
      constructor <;> linarith
    rw [hw']
    exact hwin t' habs
  have hq : ∀ w ∈ Icc Z (Z + s), |deriv (deriv (U (-(μ ^ 2) / 2))) w| ≤ μ ^ 2 * B := by
    intro w hw
    rw [PC.ode_U, abs_mul]
    have hUw := hwin2 w hw
    have hwz : |w| ≤ μ * Real.sqrt 2 := by
      -- `|w| <= |Z| + s`, `|Z| <= (1 - eps) mu sqrt 2`
      have hs2 : 1 ≤ Real.sqrt 2 := hsq2
      have hZb : |Z| ≤ (1 - ε) * (μ * Real.sqrt 2) := by
        rw [hZ, show μ * t * Real.sqrt 2 = t * (μ * Real.sqrt 2) by ring, abs_mul, abs_of_pos (by positivity : 0 < μ * Real.sqrt 2)]
        exact mul_le_mul_of_nonneg_right ht (by positivity)
      have : s ≤ ε * (μ * Real.sqrt 2) := by
        rw [hs, div_le_iff₀ hμpos]
        linarith [hkey]
      rw [abs_le] at hZb ⊢
      constructor <;> nlinarith [hw.1, hw.2, hZb.1, hZb.2]
    have hwsq : w ^ 2 ≤ 2 * μ ^ 2 := by
      have : w ^ 2 ≤ (μ * Real.sqrt 2) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hwz 2
      rw [mul_pow, Real.sq_sqrt (by norm_num)] at this
      linarith
    have hcoef : |w ^ 2 / 4 + -(μ ^ 2) / 2| ≤ μ ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg w, sq_nonneg μ]
    exact mul_le_mul hcoef hUw (abs_nonneg _) (by positivity)
  have hl := landau_deriv ((U_differentiable PC _).differentiable (by norm_num)) (U_deriv_differentiable PC _) hspos hwin2 hq
  have hfin : 2 * B / s + s * (μ ^ 2 * B) = 3 * B * μ := by
    rw [hs]; field_simp; ring
  linarith [hl, hfin]

end Phase

/-! ### The lower bound for the envelope (Wronskian + `env_well` + connection formula) -/

/-- The Euclidean envelope `E_k(p, p') = sqrt(p^2 + p'^2/k)`. -/
def Env2 (k p p' : ℝ) : ℝ := Real.sqrt (p ^ 2 + p' ^ 2 / k)

lemma Env2_nonneg (k p p' : ℝ) : 0 ≤ Env2 k p p' := Real.sqrt_nonneg _

lemma Env2_sq {k : ℝ} (hk : 0 < k) (p p' : ℝ) : Env2 k p p' ^ 2 = p ^ 2 + p' ^ 2 / k :=
  Real.sq_sqrt (by positivity)

/-- Cauchy--Schwarz for the Wronskian: `|x y' - x' y| <= sqrt(k) E(x,x') E(y,y')`. -/
lemma wronsk_le_Env2 {k : ℝ} (hk : 0 < k) (x x' y y' : ℝ) :
    |x * y' - x' * y| ≤ Real.sqrt k * Env2 k x x' * Env2 k y y' := by
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hss := Real.sq_sqrt hk.le
  have hsq : (x * y' - x' * y) ^ 2 ≤ (Real.sqrt k * Env2 k x x' * Env2 k y y') ^ 2 := by
    have e1 := Env2_sq hk x x'
    have e2 := Env2_sq hk y y'
    rw [mul_pow, mul_pow, e1, e2, hss]
    have key : (x ^ 2 + x' ^ 2 / k) * (k * y ^ 2 + y' ^ 2) - (x * y' - x' * y) ^ 2
        = (x * (Real.sqrt k * y) + (x' / Real.sqrt k) * y') ^ 2 := by
      have ha : x' ^ 2 / k = (x' / Real.sqrt k) ^ 2 := by rw [div_pow, hss]
      have hb : k * y ^ 2 = (Real.sqrt k * y) ^ 2 := by rw [mul_pow, hss]
      have hab : x' * y = (x' / Real.sqrt k) * (Real.sqrt k * y) := by field_simp
      rw [ha, hb, hab]; ring
    have h1 : (x * y' - x' * y) ^ 2 ≤ (x ^ 2 + x' ^ 2 / k) * (k * y ^ 2 + y' ^ 2) := by
      nlinarith [sq_nonneg (x * (Real.sqrt k * y) + (x' / Real.sqrt k) * y')]
    calc (x * y' - x' * y) ^ 2 ≤ (x ^ 2 + x' ^ 2 / k) * (k * y ^ 2 + y' ^ 2) := h1
      _ = k * (x ^ 2 + x' ^ 2 / k) * (y ^ 2 + y' ^ 2 / k) := by field_simp
  exact abs_le_of_sq_le_sq hsq (by have := Env2_nonneg k x x'; have := Env2_nonneg k y y'; positivity)

/-- Triangle inequality for `Env2`. -/
lemma Env2_comb_le {k : ℝ} (hk : 0 < k) (α β p p' q q' : ℝ) :
    Env2 k (α * p + β * q) (α * p' + β * q') ≤ |α| * Env2 k p p' + |β| * Env2 k q q' := by
  have hA := Env2_sq hk p p'
  have hB := Env2_sq hk q q'
  have hA0 := Env2_nonneg k p p'
  have hB0 := Env2_nonneg k q q'
  have hcs : p * q + p' * q' / k ≤ Env2 k p p' * Env2 k q q' := by
    have h2 : (p * q + p' * q' / k) ^ 2 ≤ (Env2 k p p' * Env2 k q q') ^ 2 := by
      rw [mul_pow, hA, hB]
      have : (p ^ 2 + p' ^ 2 / k) * (q ^ 2 + q' ^ 2 / k) - (p * q + p' * q' / k) ^ 2 = (p * q' - p' * q) ^ 2 / k := by
        field_simp; ring
      have h3 : 0 ≤ (p * q' - p' * q) ^ 2 / k := by positivity
      linarith
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq h2 (by positivity))
  have hsq : (Env2 k (α * p + β * q) (α * p' + β * q')) ^ 2 ≤ (|α| * Env2 k p p' + |β| * Env2 k q q') ^ 2 := by
    rw [Env2_sq hk]
    have e : (α * p + β * q) ^ 2 + (α * p' + β * q') ^ 2 / k
        = α ^ 2 * (p ^ 2 + p' ^ 2 / k) + β ^ 2 * (q ^ 2 + q' ^ 2 / k) + 2 * α * β * (p * q + p' * q' / k) := by
      field_simp; ring
    rw [e]
    have e2 : (|α| * Env2 k p p' + |β| * Env2 k q q') ^ 2
        = α ^ 2 * (p ^ 2 + p' ^ 2 / k) + β ^ 2 * (q ^ 2 + q' ^ 2 / k) + 2 * (|α| * |β|) * (Env2 k p p' * Env2 k q q') := by
      have := sq_abs α; have := sq_abs β
      nlinarith [hA, hB]
    rw [e2]
    have : 2 * α * β * (p * q + p' * q' / k) ≤ 2 * (|α| * |β|) * (Env2 k p p' * Env2 k q q') := by
      have h1 : α * β ≤ |α| * |β| := by rw [← abs_mul]; exact le_abs_self _
      have h2 : -(α * β) ≤ |α| * |β| := by rw [← abs_mul]; exact neg_le_abs _
      have hp : -(Env2 k p p' * Env2 k q q') ≤ p * q + p' * q' / k := by
        have h2' : (p * q + p' * q' / k) ^ 2 ≤ (Env2 k p p' * Env2 k q q') ^ 2 := by
          rw [mul_pow, hA, hB]
          have : (p ^ 2 + p' ^ 2 / k) * (q ^ 2 + q' ^ 2 / k) - (p * q + p' * q' / k) ^ 2 = (p * q' - p' * q) ^ 2 / k := by
            field_simp; ring
          have h3 : 0 ≤ (p * q' - p' * q) ^ 2 / k := by positivity
          linarith
        exact neg_le_of_abs_le (abs_le_of_sq_le_sq h2' (by positivity))
      nlinarith [mul_nonneg hA0 hB0, mul_nonneg (abs_nonneg α) (abs_nonneg β)]
    linarith
  exact abs_le_of_sq_le_sq hsq (by positivity) |> fun h => by
    rwa [abs_of_nonneg (Env2_nonneg k _ _)] at h

section Lower

variable {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

lemma V_differentiable (PC : ParabolicCylinderFacts U V cPC CPC) (a : ℝ) : ContDiff ℝ ⊤ (V a) :=
  PC.smooth_V.comp (contDiff_const.prodMk contDiff_id)

lemma kappaBal_nonpos {a : ℝ} (ha : a ≤ 0) :
    0 < kappaBal a ∧ kappaBal a ^ 2 * Real.Gamma (1 / 2 - a) = 1 := by
  have hG : 0 < Real.Gamma (1 / 2 - a) := Real.Gamma_pos_of_pos (by linarith)
  have hk : kappaBal a = (Real.Gamma (1 / 2 - a)) ^ (-(1 : ℝ) / 2) := by
    unfold kappaBal; rw [if_pos ha]
  rw [hk]
  refine ⟨Real.rpow_pos_of_pos hG _, ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hG.le]
  have : (-(1 : ℝ) / 2 * ((2 : ℕ) : ℝ)) = -1 := by norm_num
  rw [this, Real.rpow_neg_one]
  exact inv_mul_cancel₀ hG.ne'

lemma deriv_V_reflect (PC : ParabolicCylinderFacts U V cPC CPC) {a : ℝ} (ha : a ≤ 0) (w : ℝ) :
    deriv (V a) (-w) = -((Real.cos (Real.pi * a) / Real.Gamma (1 / 2 - a)) * deriv (U a) w
      + Real.sin (Real.pi * a) * deriv (V a) w) := by
  have hfun : (fun w => V a (-w)) = fun w => (Real.cos (Real.pi * a) / Real.Gamma (1 / 2 - a)) * U a w
      + Real.sin (Real.pi * a) * V a w := funext (PC.reflect_V a ha)
  have h1 : deriv (fun w => V a (-w)) w = -deriv (V a) (-w) := deriv_comp_neg (V a) w
  have hUd : HasDerivAt (U a) (deriv (U a) w) w :=
    ((U_differentiable PC a).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hVd : HasDerivAt (V a) (deriv (V a) w) w :=
    ((V_differentiable PC a).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun w => (Real.cos (Real.pi * a) / Real.Gamma (1 / 2 - a)) * U a w
      + Real.sin (Real.pi * a) * V a w)
      ((Real.cos (Real.pi * a) / Real.Gamma (1 / 2 - a)) * deriv (U a) w + Real.sin (Real.pi * a) * deriv (V a) w) w :=
    (hUd.const_mul (Real.cos (Real.pi * a) / Real.Gamma (1 / 2 - a))).add (hVd.const_mul (Real.sin (Real.pi * a)))
  rw [hfun, h2.deriv] at h1
  linarith

lemma k2_pos (a z : ℝ) : 0 < k2 a z := by
  unfold k2
  exact lt_max_of_lt_right (Real.rpow_pos_of_pos (lt_max_of_lt_right one_pos) _)

lemma k2_neg (a z : ℝ) : k2 a (-z) = k2 a z := by simp [k2, neg_sq]

lemma Mbal_neg (a z : ℝ) : Mbal a (-z) = Mbal a z := by simp [Mbal, k2_neg]

lemma Ewell_one {a z : ℝ} (hz : z ≤ 2 * Real.sqrt |a|) : Ewell a z = 1 := by
  unfold Ewell; rw [if_neg (not_lt.mpr hz)]

lemma Mbal_sq_mul {k : ℝ} (hk : 0 < k) : Real.sqrt k * (k ^ (-(1 : ℝ) / 4)) ^ 2 = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hk.le, Real.sqrt_eq_rpow, ← Real.rpow_add hk]
  norm_num

/-- The envelope of the second solution `V` (normalised by `sqrt(pi/2) kappa^{-1}`) is at most `(sqrt(pi/2) + 1) C_PC M_bal`
on the whole well `|z| <= 2 sqrt(-a)` (`z >= 0` by `env_well`, `z < 0` through `reflect_V`). -/
lemma EV_upper (PC : ParabolicCylinderFacts U V cPC CPC) {a z : ℝ} (ha : a ≤ 0) (hz : |z| ≤ 2 * Real.sqrt (-a)) :
    Env2 (k2 a z) (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * V a z)
      (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (V a) z) ≤ (Real.sqrt (Real.pi / 2) + 1) * CPC * Mbal a z := by
  obtain ⟨hκ, hκ2⟩ := kappaBal_nonpos ha
  have hCPC : 0 < CPC := lt_of_lt_of_le PC.cPC_pos PC.cPC_le
  have hΓpos : 0 < Real.Gamma (1 / 2 - a) := Real.Gamma_pos_of_pos (by linarith)
  have hm0 : 0 < Mbal a z := Real.rpow_pos_of_pos (k2_pos a z) _
  have hsp : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  rcases le_total 0 z with hz0 | hz0
  · have hzle : z ≤ 2 * Real.sqrt |a| := by
      rw [abs_of_nonpos ha]; exact (le_abs_self z).trans hz
    have h := (PC.env_well a ha z hz0).2
    rw [Ewell_one hzle, inv_one, mul_one] at h
    have h' : Env2 (k2 a z) (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * V a z)
      (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (V a) z) ≤ CPC * Mbal a z := h
    have h1 : CPC * Mbal a z ≤ (Real.sqrt (Real.pi / 2) + 1) * CPC * Mbal a z := by
      have : 0 ≤ Real.sqrt (Real.pi / 2) * (CPC * Mbal a z) := by positivity
      nlinarith
    linarith
  · obtain ⟨w, rfl⟩ : ∃ w, z = -w := ⟨-z, by ring⟩
    have hw0 : 0 ≤ w := by linarith
    have hwle : w ≤ 2 * Real.sqrt |a| := by
      rw [abs_of_nonpos ha]
      have := hz; rw [abs_of_nonpos hz0] at this; simpa using this
    rw [k2_neg, Mbal_neg]
    have hEW := PC.env_well a ha w hw0
    rw [Ewell_one hwle, inv_one, mul_one] at hEW
    obtain ⟨h1, h2⟩ := hEW
    have hk := k2_pos a w
    set k := k2 a w with hkdef
    set κ := kappaBal a with hκdef
    set Γ := Real.Gamma (1 / 2 - a) with hΓ
    set m := Mbal a w with hmdef
    have hmpos : 0 < m := Real.rpow_pos_of_pos hk _
    set xw := κ * U a w with hxw
    set xw' := κ * deriv (U a) w with hxw'
    set yw := Real.sqrt (Real.pi / 2) * κ⁻¹ * V a w with hyw
    set yw' := Real.sqrt (Real.pi / 2) * κ⁻¹ * deriv (V a) w with hyw'
    have e1 : Env2 k xw xw' ≤ CPC * m := h1
    have e2 : Env2 k yw yw' ≤ CPC * m := h2
    have hVz : V a (-w) = (Real.cos (Real.pi * a) / Γ) * U a w + Real.sin (Real.pi * a) * V a w := PC.reflect_V a ha w
    have hVz' : deriv (V a) (-w) = -((Real.cos (Real.pi * a) / Γ) * deriv (U a) w + Real.sin (Real.pi * a) * deriv (V a) w) :=
      deriv_V_reflect PC ha w
    have hcomb : ∀ (P : ℝ), Real.sqrt (Real.pi / 2) * κ⁻¹ * ((Real.cos (Real.pi * a) / Γ) * P)
        = (Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * a)) * (κ * P) := by
      intro P
      have : κ⁻¹ * (Real.cos (Real.pi * a) / Γ) = Real.cos (Real.pi * a) * κ := by
        field_simp
        linear_combination (-Real.cos (Real.pi * a)) * hκ2
      calc Real.sqrt (Real.pi / 2) * κ⁻¹ * ((Real.cos (Real.pi * a) / Γ) * P)
          = Real.sqrt (Real.pi / 2) * (κ⁻¹ * (Real.cos (Real.pi * a) / Γ)) * P := by ring
        _ = _ := by rw [this]; ring
    have hyz : Real.sqrt (Real.pi / 2) * κ⁻¹ * V a (-w)
        = (Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * a)) * xw + Real.sin (Real.pi * a) * yw := by
      rw [hVz, mul_add, hcomb, hxw, hyw]; ring
    have hyz' : Real.sqrt (Real.pi / 2) * κ⁻¹ * deriv (V a) (-w)
        = -((Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * a)) * xw' + Real.sin (Real.pi * a) * yw') := by
      rw [hVz', mul_neg, mul_add, hcomb, hxw', hyw']; ring
    have hc := Env2_comb_le hk (Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * a)) (Real.sin (Real.pi * a)) xw xw' yw yw'
    have hEyeq : Env2 k (Real.sqrt (Real.pi / 2) * κ⁻¹ * V a (-w)) (Real.sqrt (Real.pi / 2) * κ⁻¹ * deriv (V a) (-w))
        = Env2 k ((Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * a)) * xw + Real.sin (Real.pi * a) * yw)
          ((Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * a)) * xw' + Real.sin (Real.pi * a) * yw') := by
      unfold Env2
      rw [hyz, hyz']
      congr 1
      ring
    rw [hEyeq]
    refine hc.trans ?_
    have hcos : |Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * a)| ≤ Real.sqrt (Real.pi / 2) := by
      rw [abs_mul, abs_of_nonneg hsp]
      exact mul_le_of_le_one_right hsp (Real.abs_cos_le_one _)
    have hsin : |Real.sin (Real.pi * a)| ≤ 1 := Real.abs_sin_le_one _
    have hE1 := Env2_nonneg k xw xw'
    have hE2 := Env2_nonneg k yw yw'
    calc _ ≤ Real.sqrt (Real.pi / 2) * (CPC * m) + 1 * (CPC * m) := by
          apply add_le_add
          · exact mul_le_mul hcos e1 hE1 hsp
          · exact mul_le_mul hsin e2 hE2 zero_le_one
      _ = (Real.sqrt (Real.pi / 2) + 1) * CPC * m := by ring

/-- **Lower bound for the envelope of `U` in the well** (both signs of `z`): for `a <= 0`, `|z| <= 2 sqrt(-a)`,
`M_bal(a, z) <= (sqrt(pi/2) + 1) C_PC kappa_bal(a) sqrt(U^2 + U'^2/k_2)`. -/
theorem EU_lower (PC : ParabolicCylinderFacts U V cPC CPC) {a z : ℝ} (ha : a ≤ 0) (hz : |z| ≤ 2 * Real.sqrt (-a)) :
    Mbal a z ≤ (Real.sqrt (Real.pi / 2) + 1) * CPC *
      (kappaBal a * Real.sqrt (U a z ^ 2 + deriv (U a) z ^ 2 / k2 a z)) := by
  obtain ⟨hκ, hκ2⟩ := kappaBal_nonpos ha
  have hCPC : 0 < CPC := lt_of_lt_of_le PC.cPC_pos PC.cPC_le
  have hk := k2_pos a z
  have hEy := EV_upper PC ha hz
  have hm := Mbal_sq_mul hk
  have hmpos : 0 < Mbal a z := Real.rpow_pos_of_pos hk _
  set k := k2 a z with hkdef
  set κ := kappaBal a with hκdef
  set m := Mbal a z with hmdef
  have hm2 : Real.sqrt k * m ^ 2 = 1 := hm
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  set x := κ * U a z with hx
  set x' := κ * deriv (U a) z with hx'
  set y := Real.sqrt (Real.pi / 2) * κ⁻¹ * V a z with hy
  set y' := Real.sqrt (Real.pi / 2) * κ⁻¹ * deriv (V a) z with hy'
  have hW : x * y' - x' * y = 1 := by
    have hw := PC.wronsk a z
    have hsp : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
      rw [← Real.sqrt_mul (by positivity)]
      have : Real.pi / 2 * (2 / Real.pi) = 1 := by field_simp
      rw [this, Real.sqrt_one]
    have : x * y' - x' * y = Real.sqrt (Real.pi / 2) * (κ * κ⁻¹) * (U a z * deriv (V a) z - deriv (U a) z * V a z) := by
      rw [hx, hx', hy, hy']; ring
    rw [this, mul_inv_cancel₀ hκ.ne', mul_one, hw, hsp]
  have hEx : Env2 k x x' = κ * Real.sqrt (U a z ^ 2 + deriv (U a) z ^ 2 / k) := by
    unfold Env2
    rw [show x ^ 2 + x' ^ 2 / k = κ ^ 2 * (U a z ^ 2 + deriv (U a) z ^ 2 / k) by rw [hx, hx']; ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ.le]
  have hcs := wronsk_le_Env2 hk x x' y y'
  rw [hW, abs_one, hEx] at hcs
  set EU := Real.sqrt (U a z ^ 2 + deriv (U a) z ^ 2 / k) with hEU
  have hEy0 := Env2_nonneg k y y'
  have hEU0 : 0 ≤ EU := Real.sqrt_nonneg _
  have h1 : 1 ≤ Real.sqrt k * (κ * EU) * ((Real.sqrt (Real.pi / 2) + 1) * CPC * m) := by
    calc (1 : ℝ) ≤ Real.sqrt k * (κ * EU) * Env2 k y y' := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_left hEy (by positivity)
  have h3 : m ≤ m * (Real.sqrt k * (κ * EU) * ((Real.sqrt (Real.pi / 2) + 1) * CPC * m)) := by
    nlinarith [hmpos]
  have h4 : m * (Real.sqrt k * (κ * EU) * ((Real.sqrt (Real.pi / 2) + 1) * CPC * m))
      = (Real.sqrt k * m ^ 2) * ((Real.sqrt (Real.pi / 2) + 1) * CPC * (κ * EU)) := by ring
  rw [h4, hm2, one_mul] at h3
  exact h3

end Lower

lemma mul_chain_aux (c κ E E' : ℝ) (hc : 0 ≤ c) (hκ : 0 ≤ κ) (h : E ≤ E') : c * (κ * E) ≤ c * (κ * E') := by
  gcongr

section Pack

variable {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- The Mbal bound of `phase_pack` for abstract bounds `|U| <= B`, `|U'| <= 3 B mu`. -/
lemma pack_Mbal (PC : ParabolicCylinderFacts U V cPC CPC) {ε μ t B : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hμ1 : 1 ≤ μ)
    (hμε : 2 / ε ≤ μ ^ 2) (ht : |t| ≤ 1 - ε) (hB : 0 ≤ B)
    (hv : |U (-(μ ^ 2) / 2) (μ * t * Real.sqrt 2)| ≤ B)
    (hd : |deriv (U (-(μ ^ 2) / 2)) (μ * t * Real.sqrt 2)| ≤ 3 * B * μ) :
    Mbal (-(μ ^ 2) / 2) (μ * t * Real.sqrt 2) ≤
      (Real.sqrt (Real.pi / 2) + 1) * CPC * Real.sqrt (1 + 18 / ε) * kappaBal (-(μ ^ 2) / 2) * B := by
  have hμpos : 0 < μ := by linarith
  have hCPC : 0 < CPC := lt_of_lt_of_le PC.cPC_pos PC.cPC_le
  have hc10 : 0 ≤ (Real.sqrt (Real.pi / 2) + 1) * CPC := by positivity
  set a : ℝ := -(μ ^ 2) / 2 with ha
  set Z : ℝ := μ * t * Real.sqrt 2 with hZ
  have ha0 : a ≤ 0 := by rw [ha]; nlinarith [sq_nonneg μ]
  have ht1 : t ^ 2 ≤ 1 := by have := abs_le.mp ht; nlinarith
  have hZw : |Z| ≤ 2 * Real.sqrt (-a) := by
    have h2 : 0 ≤ 2 * Real.sqrt (-a) := by positivity
    refine abs_le_of_sq_le_sq ?_ h2
    have : (2 * Real.sqrt (-a)) ^ 2 = 2 * μ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by rw [ha]; nlinarith [sq_nonneg μ])]; rw [ha]; ring
    rw [this, hZ, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith [sq_nonneg μ]
  have hlow := EU_lower PC ha0 hZw
  have hk2 : μ ^ 2 * ε / 2 ≤ k2 a Z := by
    unfold k2
    refine le_trans ?_ (le_max_left _ _)
    have e : Z ^ 2 / 4 + a = -(μ ^ 2 * (1 - t ^ 2) / 2) := by
      rw [hZ, ha, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
    rw [e, abs_neg, abs_of_nonneg (by positivity)]
    have h1t : ε ≤ 1 - t ^ 2 := by
      have h1 := abs_le.mp ht
      nlinarith
    nlinarith [sq_nonneg μ]
  have hkpos : 0 < k2 a Z := k2_pos a Z
  generalize k2 a Z = k at hlow hk2 hkpos
  have hU2 : U a Z ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hv 2
  have hD2 : deriv (U a) Z ^ 2 / k ≤ 9 * B ^ 2 * (2 / ε) := by
    have h1 : deriv (U a) Z ^ 2 ≤ (3 * B * μ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    rw [div_le_iff₀ hkpos]
    have h2 : (3 * B * μ) ^ 2 = 9 * B ^ 2 * μ ^ 2 := by ring
    have h3 : μ ^ 2 ≤ (2 / ε) * k := by
      calc μ ^ 2 = (2 / ε) * (μ ^ 2 * ε / 2) := by field_simp
        _ ≤ (2 / ε) * k := mul_le_mul_of_nonneg_left hk2 (by positivity)
    have h4 : 0 ≤ 9 * B ^ 2 := by positivity
    calc deriv (U a) Z ^ 2 ≤ 9 * B ^ 2 * μ ^ 2 := by rw [← h2]; exact h1
      _ ≤ 9 * B ^ 2 * ((2 / ε) * k) := mul_le_mul_of_nonneg_left h3 h4
      _ = 9 * B ^ 2 * (2 / ε) * k := by ring
  have hEU : Real.sqrt (U a Z ^ 2 + deriv (U a) Z ^ 2 / k) ≤ Real.sqrt (1 + 18 / ε) * B := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have e1 : (Real.sqrt (1 + 18 / ε) * B) ^ 2 = B ^ 2 * (1 + 18 / ε) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    rw [e1]
    have e2 : B ^ 2 * (1 + 18 / ε) = B ^ 2 + 9 * B ^ 2 * (2 / ε) := by ring
    rw [e2]
    exact add_le_add hU2 hD2
  have hκ : 0 < kappaBal a := (kappaBal_nonpos ha0).1
  refine hlow.trans ?_
  have hfin := mul_chain_aux _ _ _ _ hc10 hκ.le hEU
  have hring : (Real.sqrt (Real.pi / 2) + 1) * CPC * (kappaBal a * (Real.sqrt (1 + 18 / ε) * B))
      = (Real.sqrt (Real.pi / 2) + 1) * CPC * Real.sqrt (1 + 18 / ε) * kappaBal a * B := by ring
  exact hfin.trans hring.le

/-- **The packaged facts about the Weber branch on the oscillatory range** (`lem:smo-bulkphase` (1), model-function part).  For every margin `0 < eps < 1` there are constants `C, Cd, Cm >= 0`,
`mu1 >= 1` and a positive function `g` (the `g(mu)` of DLMF 12.10.18, existential in `phase_osc`) such that for `mu >= mu1`, `|t| <= 1 - eps`, with `a = -mu^2/2`, `Z = mu t sqrt 2`, `G = 2 g(mu)`:
(i) `|U(a, Z) - G (1-t^2)^{-1/4} cos(mu^2 eta(t) - pi/4)| <= C mu^{-2} G (1-t^2)^{-1/4}`;
(ii) `|U'(a, Z)| <= Cd mu G`;
(iii) `M_bal(a, Z) <= Cm kappa_bal(a) G`. -/
theorem phase_pack (PC : ParabolicCylinderFacts U V cPC CPC) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C Cd Cm μ1 : ℝ, ∃ g : ℝ → ℝ, 0 ≤ C ∧ 0 ≤ Cd ∧ 0 ≤ Cm ∧ 1 ≤ μ1 ∧ (∀ μ, 0 < g μ) ∧
      ∀ μ : ℝ, μ1 ≤ μ → ∀ t : ℝ, |t| ≤ 1 - ε →
        |U (-(μ ^ 2) / 2) (μ * t * Real.sqrt 2) - 2 * g μ / (1 - t ^ 2) ^ ((1 : ℝ) / 4)
          * Real.cos (μ ^ 2 * ((Real.arccos t - t * Real.sqrt (1 - t ^ 2)) / 2) - Real.pi / 4)|
          ≤ C * μ⁻¹ ^ 2 * (2 * g μ / (1 - t ^ 2) ^ ((1 : ℝ) / 4)) ∧
        |deriv (U (-(μ ^ 2) / 2)) (μ * t * Real.sqrt 2)| ≤ Cd * μ * (2 * g μ) ∧
        Mbal (-(μ ^ 2) / 2) (μ * t * Real.sqrt 2) ≤ Cm * kappaBal (-(μ ^ 2) / 2) * (2 * g μ) := by
  obtain ⟨C0, μ0, g, hg, hph⟩ := PC.phase_osc (ε / 2) (by positivity) (by linarith)
  set C := max C0 0 with hCdef
  have hC : 0 ≤ C := le_max_right _ _
  have hph' : ∀ μ : ℝ, μ0 ≤ μ → ∀ t : ℝ, |t| ≤ 1 - ε / 2 →
      |U (-(μ ^ 2) / 2) (μ * t * Real.sqrt 2) - 2 * g μ / (1 - t ^ 2) ^ ((1 : ℝ) / 4)
        * Real.cos (μ ^ 2 * ((Real.arccos t - t * Real.sqrt (1 - t ^ 2)) / 2) - Real.pi / 4)|
        ≤ C * μ⁻¹ ^ 2 * (2 * g μ / (1 - t ^ 2) ^ ((1 : ℝ) / 4)) := by
    intro μ hμ t ht
    refine (hph μ hμ t ht).trans ?_
    have hpos : 0 ≤ μ⁻¹ ^ 2 * (2 * g μ / (1 - t ^ 2) ^ ((1 : ℝ) / 4)) := by
      have h1t : 0 < 1 - t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
      have := hg μ
      have : 0 < (1 - t ^ 2) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos h1t _
      positivity
    have := mul_le_mul_of_nonneg_right (le_max_left C0 0) hpos
    linarith
  set B' : ℝ := (2 / ε) ^ ((1 : ℝ) / 4) * (1 + C) with hB'
  have hB'0 : 0 ≤ B' := by rw [hB']; positivity
  have hCPC : 0 < CPC := lt_of_lt_of_le PC.cPC_pos PC.cPC_le
  set c1 : ℝ := (Real.sqrt (Real.pi / 2) + 1) * CPC with hc1
  have hc10 : 0 ≤ c1 := by rw [hc1]; positivity
  refine ⟨C, 3 * B', c1 * B' * Real.sqrt (1 + 18 / ε), max (max μ0 1) (2 / ε), g, hC, by positivity,
    by positivity, le_trans (le_max_right _ _) (le_max_left _ _), hg, ?_⟩
  intro μ hμ t ht
  have hμ0 : μ0 ≤ μ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hμ
  have hμ1 : 1 ≤ μ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hμ
  have hμ2 : 2 / ε ≤ μ := le_trans (le_max_right _ _) hμ
  have hμpos : 0 < μ := by linarith
  have hμε : 2 / ε ≤ μ ^ 2 := by nlinarith
  have htε : |t| ≤ 1 - ε / 2 := by linarith
  obtain ⟨hv, hd⟩ := phase_value_deriv_bound PC hε0 hε1 hg hph' hC hμ0 hμ1 hμε ht
  have hgpos := hg μ
  refine ⟨hph' μ hμ0 t htε, ?_, ?_⟩
  · have : 3 * ((2 / ε) ^ ((1 : ℝ) / 4) * (1 + C) * (2 * g μ)) * μ = 3 * B' * μ * (2 * g μ) := by rw [hB']; ring
    rw [← this] at *
    simpa [hB'] using hd
  · have h := pack_Mbal PC hε0 hε1 hμ1 hμε ht (B := B' * (2 * g μ)) (by positivity)
      (by rw [hB']; exact hv) (by rw [hB']; exact hd)
    have e : (Real.sqrt (Real.pi / 2) + 1) * CPC * Real.sqrt (1 + 18 / ε) * kappaBal (-(μ ^ 2) / 2) * (B' * (2 * g μ))
        = c1 * B' * Real.sqrt (1 + 18 / ε) * kappaBal (-(μ ^ 2) / 2) * (2 * g μ) := by rw [hc1]; ring
    exact h.trans e.le

end Pack

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.integral_sqrt_sub_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.integral_sqrt_sub_sq

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.phase_value_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.phase_value_deriv_bound

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.EU_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.EU_lower

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.phase_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.phase_pack

end FormalResearch.JacobiEigenvectors.Charts
