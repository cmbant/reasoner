module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.PCOrigin

/-!
# Paper J, Layer 4 (phase B2, E2): modified-energy bound on `[0, z₁]` and `env_well`

For `a ≤ -4` (`A = -a ≥ 4`), put `q(a, z) = -a - z^2 / 4` and `z₁(a) = 2 * sqrt(-a - 2 * (-a)^{1/3})`.
On `[0, z₁(a)]`, `q(a, z) ≥ 2 * (-a)^{1/3} > 0`, `k₂(a, z) = q(a, z)`, and `E_well(a, z) = 1`.

For any real solution `y` of Weber's equation `y'' = (z^2/4 + a) * y = -q(a, z) * y` on `[0, z₁(a)]`,
the modified energy
`E₁(z) = sqrt(q(a, z)) * y(z)^2 + (sqrt(q(a, z)))⁻¹ * y'(z)^2`
satisfies `80 / 99 * E₁(0) ≤ E₁(z) ≤ 5 / 4 * E₁(0)` (and hence `7 / 10 * E₁(0) ≤ E₁(z) ≤ 7 / 5 * E₁(0)`,
and `0.86 * sqrt(E₁(0)) ≤ sqrt(E₁(z)) ≤ 1.17 * sqrt(E₁(0))`).

The proof uses the auxiliary energy `H(z) = E₁(z) + α(z) * y(z) * y'(z)` with
`α(z) = -z / (4 * q(a, z) * sqrt(q(a, z)))`, for which `H'(z) = α'(z) * y(z) * y'(z)` exactly,
`|α(z)| ≤ 1 / (4 * sqrt 2) ≤ 1 / 5`, `(9/10) * E₁ ≤ H ≤ (11/10) * E₁`, and
`H(z) * exp(±(5/9) * α(z))` are monotone/antitone on `[0, z₁(a)]`.

Combining with `PCOrigin.origin_env_well_U` and `PCOrigin.origin_env_well_V` yields `env_well`
on `[0, z₁(a)]` for `pcU` and `pcV` (with explicit constant `2 * sqrt(5 / 4) ≤ 9 / 4`, or `5 / 2`,
and lower bound `80 / 99` on `E₁` giving `0.44` on the envelope).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Real

/-! ### Geometry and `k₂`, `E_well` on `[0, z₁]` -/

/-- The oscillatory endpoint `z₁(a) = 2 * sqrt(-a - 2 * (-a)^{1/3})` for `a ≤ -4`. -/
def z1Well (a : ℝ) : ℝ := 2 * Real.sqrt (-a - 2 * (-a) ^ ((1 : ℝ) / 3))

/-- The oscillatory potential `q(a, z) = -a - z^2 / 4`. -/
def qWell (a z : ℝ) : ℝ := -a - z ^ 2 / 4

/-- For `A ≥ 4`, `2 * A^{1/3} < A`. -/
lemma two_mul_rpow_one_third_lt {A : ℝ} (hA : 4 ≤ A) : 2 * A ^ ((1 : ℝ) / 3) < A := by
  have hA0 : 0 < A := by linarith
  have hcube : (2 * A ^ ((1 : ℝ) / 3)) ^ 3 < A ^ 3 := by
    have h1 : (A ^ ((1 : ℝ) / 3)) ^ 3 = A := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hA0.le]
      norm_num
    have hA2 : 8 < A ^ 2 := by nlinarith
    calc (2 * A ^ ((1 : ℝ) / 3)) ^ 3 = 8 * (A ^ ((1 : ℝ) / 3)) ^ 3 := by ring
      _ = 8 * A := by rw [h1]
      _ < A ^ 2 * A := by gcongr
      _ = A ^ 3 := by ring
  exact lt_of_pow_lt_pow_left₀ 3 hA0.le hcube

lemma z1Well_nonneg (a : ℝ) : 0 ≤ z1Well a := by
  unfold z1Well; positivity

lemma z1Well_lt_turning {a : ℝ} (ha : a ≤ -4) : z1Well a < 2 * Real.sqrt |a| := by
  unfold z1Well
  have hA : 4 ≤ -a := by linarith
  have h2 : 0 < (-a) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by linarith) _
  have hsub : 0 ≤ -a - 2 * (-a) ^ ((1 : ℝ) / 3) := by
    linarith [two_mul_rpow_one_third_lt hA]
  rw [abs_of_nonpos (by linarith)]
  gcongr
  linarith

lemma qWell_ge_on_Icc {a z : ℝ} (ha : a ≤ -4) (hz0 : 0 ≤ z) (hz1 : z ≤ z1Well a) :
    2 * (-a) ^ ((1 : ℝ) / 3) ≤ qWell a z := by
  have hA : 4 ≤ -a := by linarith
  have hsub : 0 ≤ -a - 2 * (-a) ^ ((1 : ℝ) / 3) := by
    linarith [two_mul_rpow_one_third_lt hA]
  have hzsq : z ^ 2 ≤ 4 * (-a - 2 * (-a) ^ ((1 : ℝ) / 3)) := by
    calc z ^ 2 ≤ (z1Well a) ^ 2 := by nlinarith
      _ = 4 * (-a - 2 * (-a) ^ ((1 : ℝ) / 3)) := by
          unfold z1Well; rw [mul_pow, Real.sq_sqrt hsub]; ring
  unfold qWell
  linarith

lemma qWell_pos_on_Icc {a z : ℝ} (ha : a ≤ -4) (hz0 : 0 ≤ z) (hz1 : z ≤ z1Well a) :
    0 < qWell a z := by
  have h2 : 0 < (-a) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by linarith) _
  linarith [qWell_ge_on_Icc ha hz0 hz1]

lemma k2_eq_qWell {a z : ℝ} (ha : a ≤ -4) (hz0 : 0 ≤ z) (hz1 : z ≤ z1Well a) :
    k2 a z = qWell a z := by
  have hq := qWell_ge_on_Icc ha hz0 hz1
  have h2 : 0 < (-a) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by linarith) _
  have hqpos : 0 < qWell a z := by linarith
  have habs_a : max |a| 1 = -a := by
    rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
  have hz_eq : z ^ 2 / 4 + a = -qWell a z := by unfold qWell; ring
  unfold k2
  rw [hz_eq, abs_neg, abs_of_pos hqpos, habs_a]
  exact max_eq_left (by linarith)

lemma Ewell_eq_one_on_Icc {a z : ℝ} (ha : a ≤ -4) (hz1 : z ≤ z1Well a) :
    Ewell a z = 1 := by
  unfold Ewell
  rw [ite_eq_right]
  intro hlt
  linarith [z1Well_lt_turning ha]

/-! ### Modified energy `E₁` and auxiliary energy `H` on `[0, z₁]` -/

/-- The modified oscillatory energy `E₁(z) = sqrt(q(a, z)) * y(z)^2 + (sqrt(q(a, z)))⁻¹ * y'(z)^2`. -/
def E1Well (y : ℝ → ℝ) (a z : ℝ) : ℝ :=
  Real.sqrt (qWell a z) * y z ^ 2 + (Real.sqrt (qWell a z))⁻¹ * deriv y z ^ 2

/-- Auxiliary perturbation weight `α(a, z) = -z / (4 * q(a, z) * sqrt(q(a, z)))`. -/
def alphaWell (a z : ℝ) : ℝ :=
  -z / (4 * qWell a z * Real.sqrt (qWell a z))

/-- Auxiliary energy `H(z) = E₁(z) + α(a, z) * y(z) * y'(z)`. -/
def HWell (y : ℝ → ℝ) (a z : ℝ) : ℝ :=
  E1Well y a z + alphaWell a z * y z * deriv y z

lemma E1Well_nonneg (y : ℝ → ℝ) (a z : ℝ) : 0 ≤ E1Well y a z := by
  unfold E1Well; positivity

lemma two_mul_abs_mul_deriv_le_E1Well (y : ℝ → ℝ) {a z : ℝ} (hq : 0 < qWell a z) :
    2 * |y z * deriv y z| ≤ E1Well y a z := by
  set s := Real.sqrt (qWell a z)
  have hs : 0 < s := Real.sqrt_pos.mpr hq
  have hsq : 0 ≤ (s * |y z| - |deriv y z|) ^ 2 := sq_nonneg _
  have hmul : 2 * (s * |y z * deriv y z|) ≤ s ^ 2 * y z ^ 2 + deriv y z ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_abs (y z), sq_abs (deriv y z)]
  have hdiv : 2 * |y z * deriv y z| ≤ (s ^ 2 * y z ^ 2 + deriv y z ^ 2) / s := by
    rw [le_div_iff₀ hs]
    linarith
  have hE1 : E1Well y a z = (s ^ 2 * y z ^ 2 + deriv y z ^ 2) / s := by
    unfold E1Well
    change s * y z ^ 2 + s⁻¹ * deriv y z ^ 2 = (s ^ 2 * y z ^ 2 + deriv y z ^ 2) / s
    field_simp [hs.ne']
  linarith

lemma abs_alphaWell_le {a z : ℝ} (ha : a ≤ -4) (hz0 : 0 ≤ z) (hz1 : z ≤ z1Well a) :
    |alphaWell a z| ≤ 1 / 5 := by
  have hq := qWell_ge_on_Icc ha hz0 hz1
  have hA0 : 0 < -a := by linarith
  have hqpos : 0 < qWell a z := qWell_pos_on_Icc ha hz0 hz1
  have hspos : 0 < Real.sqrt (qWell a z) := Real.sqrt_pos.mpr hqpos
  have hz_le : z ≤ 2 * Real.sqrt (-a) := by
    have h2 : 0 ≤ (-a) ^ ((1 : ℝ) / 3) := by positivity
    calc z ≤ z1Well a := hz1
      _ = 2 * Real.sqrt (-a - 2 * (-a) ^ ((1 : ℝ) / 3)) := rfl
      _ ≤ 2 * Real.sqrt (-a) := by gcongr; linarith
  have hqs_ge : 2 * Real.sqrt 2 * Real.sqrt (-a) ≤ qWell a z * Real.sqrt (qWell a z) := by
    have hpow : (2 * (-a) ^ ((1 : ℝ) / 3)) * Real.sqrt (2 * (-a) ^ ((1 : ℝ) / 3)) =
        2 * Real.sqrt 2 * Real.sqrt (-a) := by
      have h1 : Real.sqrt (2 * (-a) ^ ((1 : ℝ) / 3)) =
          Real.sqrt 2 * (-a) ^ ((1 : ℝ) / 6) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow ((-a) ^ ((1 : ℝ) / 3)), ← Real.rpow_mul hA0.le]
        norm_num
      have h2 : (-a) ^ ((1 : ℝ) / 3) * (-a) ^ ((1 : ℝ) / 6) = Real.sqrt (-a) := by
        rw [← Real.rpow_add hA0, Real.sqrt_eq_rpow]
        norm_num
      rw [h1]
      calc 2 * (-a) ^ ((1 : ℝ) / 3) * (Real.sqrt 2 * (-a) ^ ((1 : ℝ) / 6))
          = 2 * Real.sqrt 2 * ((-a) ^ ((1 : ℝ) / 3) * (-a) ^ ((1 : ℝ) / 6)) := by ring
        _ = 2 * Real.sqrt 2 * Real.sqrt (-a) := by rw [h2]
    rw [← hpow]
    exact mul_le_mul hq (Real.sqrt_le_sqrt hq) (by positivity) hqpos.le
  have halpha_eq : |alphaWell a z| = z / (4 * qWell a z * Real.sqrt (qWell a z)) := by
    unfold alphaWell
    rw [abs_div, abs_neg, abs_of_nonneg hz0, abs_of_pos (by positivity)]
  rw [halpha_eq, div_le_iff₀ (by positivity)]
  have h5 : 5 ≤ 4 * Real.sqrt 2 := by
    have hsq : (5 : ℝ) ^ 2 ≤ (4 * Real.sqrt 2) ^ 2 := by
      calc (5 : ℝ) ^ 2 = 25 := by norm_num
        _ ≤ 16 * (Real.sqrt 2) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
        _ = (4 * Real.sqrt 2) ^ 2 := by ring
    exact le_of_sq_le_sq hsq (by positivity)
  calc z ≤ 2 * Real.sqrt (-a) := hz_le
    _ = 1 / 5 * (5 * (2 * Real.sqrt (-a))) := by ring
    _ ≤ 1 / 5 * (4 * Real.sqrt 2 * (2 * Real.sqrt (-a))) := by gcongr
    _ = 1 / 5 * (4 * (2 * Real.sqrt 2 * Real.sqrt (-a))) := by ring
    _ ≤ 1 / 5 * (4 * (qWell a z * Real.sqrt (qWell a z))) := by gcongr
    _ = 1 / 5 * (4 * qWell a z * Real.sqrt (qWell a z)) := by ring

lemma alphaWell_nonpos {a z : ℝ} (ha : a ≤ -4) (hz0 : 0 ≤ z) (hz1 : z ≤ z1Well a) :
    alphaWell a z ≤ 0 := by
  have hqpos := qWell_pos_on_Icc ha hz0 hz1
  unfold alphaWell
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

lemma HWell_bounds (y : ℝ → ℝ) {a z : ℝ} (ha : a ≤ -4) (hz0 : 0 ≤ z) (hz1 : z ≤ z1Well a) :
    9 / 10 * E1Well y a z ≤ HWell y a z ∧ HWell y a z ≤ 11 / 10 * E1Well y a z := by
  have hqpos := qWell_pos_on_Icc ha hz0 hz1
  have h1 := two_mul_abs_mul_deriv_le_E1Well y hqpos
  have h2 := abs_alphaWell_le ha hz0 hz1
  have h3 : |alphaWell a z * y z * deriv y z| ≤ 1 / 10 * E1Well y a z := by
    calc |alphaWell a z * y z * deriv y z|
        = |alphaWell a z| * |y z * deriv y z| := by rw [mul_assoc, abs_mul]
      _ ≤ (1 / 5) * (E1Well y a z / 2) := by gcongr; linarith
      _ = 1 / 10 * E1Well y a z := by ring
  obtain ⟨hl, hu⟩ := abs_le.mp h3
  unfold HWell
  constructor <;> linarith

lemma hasDerivAt_qWell (a z : ℝ) : HasDerivAt (qWell a) (-z / 2) z := by
  have h : HasDerivAt (fun w => -a - w ^ 2 / 4) (0 - (2 * z ^ 1) / 4) z :=
    (hasDerivAt_const z (-a)).sub ((hasDerivAt_pow 2 z).div_const 4)
  convert h using 1
  · ext w; rfl
  · ring

lemma hasDerivAt_alphaWell {a z : ℝ} (hq : 0 < qWell a z) :
    HasDerivAt (alphaWell a) (-(-a + z ^ 2 / 2) * Real.sqrt (qWell a z) / (4 * qWell a z ^ 3)) z := by
  set s := fun w => Real.sqrt (qWell a w)
  have hs_pos : 0 < s z := Real.sqrt_pos.mpr hq
  have hq_d : HasDerivAt (qWell a) (-z / 2) z := hasDerivAt_qWell a z
  have hs_d : HasDerivAt s ((-z / 2) / (2 * s z)) z := hq_d.sqrt hq.ne'
  have hden_d : HasDerivAt (fun w => 4 * qWell a w * s w) (-3 * z * s z) z := by
    have hmul := (hq_d.const_mul 4).mul hs_d
    convert hmul using 1
    have hsq : qWell a z = s z * s z := (Real.mul_self_sqrt hq.le).symm
    rw [hsq]
    field_simp [hs_pos.ne']
    ring
  have hnum_d : HasDerivAt (fun w : ℝ => -w) (-1) z := (hasDerivAt_id z).neg
  have hden_ne : 4 * qWell a z * s z ≠ 0 := by positivity
  have hdiv := hnum_d.div hden_d hden_ne
  convert hdiv using 1
  · ext w; unfold alphaWell; rfl
  · have hsq : qWell a z = s z * s z := (Real.mul_self_sqrt hq.le).symm
    have hq_eq : 4 * qWell a z + 3 * z ^ 2 = 4 * (-a + z ^ 2 / 2) := by
      unfold qWell; ring
    symm
    calc (-1 * (4 * qWell a z * s z) - -z * (-3 * z * s z)) / (4 * qWell a z * s z) ^ 2
        = -(4 * qWell a z + 3 * z ^ 2) * s z / (16 * qWell a z ^ 2 * (s z * s z)) := by ring
      _ = -(4 * (-a + z ^ 2 / 2)) * s z / (16 * qWell a z ^ 2 * qWell a z) := by rw [hq_eq, ← hsq]
      _ = -(-a + z ^ 2 / 2) * s z / (4 * qWell a z ^ 3) := by ring

lemma hasDerivAt_HWell {y : ℝ → ℝ} {a z : ℝ} (hq : 0 < qWell a z)
    (hy : DifferentiableAt ℝ y z) (hy' : DifferentiableAt ℝ (deriv y) z)
    (hode : deriv (deriv y) z = (z ^ 2 / 4 + a) * y z) :
    HasDerivAt (HWell y a)
      ((-(-a + z ^ 2 / 2) * Real.sqrt (qWell a z) / (4 * qWell a z ^ 3)) * y z * deriv y z) z := by
  set s := fun w => Real.sqrt (qWell a w)
  have hs_pos : 0 < s z := Real.sqrt_pos.mpr hq
  have hq_d : HasDerivAt (qWell a) (-z / 2) z := hasDerivAt_qWell a z
  have hs_d : HasDerivAt s ((-z / 2) / (2 * s z)) z := hq_d.sqrt hq.ne'
  have hsinv_d : HasDerivAt (fun w => (s w)⁻¹) (-((-z / 2) / (2 * s z)) / s z ^ 2) z :=
    hs_d.inv hs_pos.ne'
  have hy_d : HasDerivAt y (deriv y z) z := hy.hasDerivAt
  have hy'_d : HasDerivAt (deriv y) ((z ^ 2 / 4 + a) * y z) z := by
    rw [← hode]; exact hy'.hasDerivAt
  have hy2_d : HasDerivAt (fun w => y w ^ 2) (2 * y z * deriv y z) z := by
    convert hy_d.pow 2 using 1; ring
  have hy'2_d : HasDerivAt (fun w => deriv y w ^ 2) (2 * deriv y z * ((z ^ 2 / 4 + a) * y z)) z := by
    convert hy'_d.pow 2 using 1; ring
  have hE1_d := (hs_d.mul hy2_d).add (hsinv_d.mul hy'2_d)
  have ha_d := hasDerivAt_alphaWell hq
  have hpert_d := (ha_d.mul hy_d).mul hy'_d
  convert hE1_d.add hpert_d using 1
  · ext w; unfold HWell E1Well; rfl
  · have hsq : s z ^ 2 = qWell a z := Real.sq_sqrt hq.le
    have hq_def : z ^ 2 / 4 + a = -qWell a z := by unfold qWell; ring
    have hs_eq : Real.sqrt (qWell a z) = s z := rfl
    dsimp only [Pi.mul_apply, Pi.add_apply]
    rw [hs_eq]
    change _ = -z / 2 / (2 * s z) * y z ^ 2 + s z * (2 * y z * deriv y z) +
        (-(-z / 2 / (2 * s z)) / s z ^ 2 * deriv y z ^ 2 + (s z)⁻¹ * (2 * deriv y z * ((z ^ 2 / 4 + a) * y z))) +
      ((-(-a + z ^ 2 / 2) * s z / (4 * qWell a z ^ 3) * y z + alphaWell a z * deriv y z) * deriv y z +
        alphaWell a z * y z * ((z ^ 2 / 4 + a) * y z))
    rw [hq_def]
    unfold alphaWell
    change _ = -z / 2 / (2 * s z) * y z ^ 2 + s z * (2 * y z * deriv y z) +
        (-(-z / 2 / (2 * s z)) / s z ^ 2 * deriv y z ^ 2 + (s z)⁻¹ * (2 * deriv y z * (-qWell a z * y z))) +
      ((-(-a + z ^ 2 / 2) * s z / (4 * qWell a z ^ 3) * y z + -z / (4 * qWell a z * s z) * deriv y z) * deriv y z +
        -z / (4 * qWell a z * s z) * y z * (-qWell a z * y z))
    field_simp [hs_pos.ne', hq.ne']
    rw [show s z ^ 4 = (s z ^ 2) ^ 2 by ring, hsq]
    ring

/-- **E2 (general Weber solution on `[0, z₁]`)**: for any solution `y` of Weber's equation
`y'' = (z^2/4 + a) * y` on `[0, z₁(a)]` with `a ≤ -4`, the modified energy
`E₁(z) = sqrt(q(a, z)) * y(z)^2 + (sqrt(q(a, z)))⁻¹ * y'(z)^2` satisfies
`80 / 99 * E₁(0) ≤ E₁(z) ≤ 5 / 4 * E₁(0)` for all `z ∈ [0, z₁(a)]`. -/
theorem E1Well_bounds {a : ℝ} (ha : a ≤ -4) (y : ℝ → ℝ)
    (hy : ∀ z ∈ Set.Icc 0 (z1Well a), DifferentiableAt ℝ y z)
    (hy' : ∀ z ∈ Set.Icc 0 (z1Well a), DifferentiableAt ℝ (deriv y) z)
    (hode : ∀ z ∈ Set.Icc 0 (z1Well a), deriv (deriv y) z = (z ^ 2 / 4 + a) * y z) :
    ∀ z ∈ Set.Icc 0 (z1Well a),
      80 / 99 * E1Well y a 0 ≤ E1Well y a z ∧ E1Well y a z ≤ 5 / 4 * E1Well y a 0 := by
  let S := Set.Icc 0 (z1Well a)
  let fUp : ℝ → ℝ := fun w => HWell y a w * Real.exp (5 / 9 * alphaWell a w)
  let fDn : ℝ → ℝ := fun w => HWell y a w * Real.exp (-(5 / 9) * alphaWell a w)
  have hderiv : ∀ c : ℝ, ∀ w ∈ S,
      HasDerivAt (fun t => HWell y a t * Real.exp (c * alphaWell a t))
        (((-(-a + w ^ 2 / 2) * Real.sqrt (qWell a w) / (4 * qWell a w ^ 3)) *
          (y w * deriv y w + c * HWell y a w)) * Real.exp (c * alphaWell a w)) w := by
    intro c w hw
    have hq := qWell_pos_on_Icc ha hw.1 hw.2
    have hH := hasDerivAt_HWell hq (hy w hw) (hy' w hw) (hode w hw)
    have ha_d := hasDerivAt_alphaWell hq
    have hexp := (ha_d.const_mul c).exp
    convert hH.mul hexp using 1
    ring
  have hfUp_anti : AntitoneOn fUp S := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (z1Well a))
    · intro w hw
      exact (hderiv (5 / 9) w hw).continuousAt.continuousWithinAt
    · intro w hw
      have hwS : w ∈ S := interior_subset hw
      exact (hderiv (5 / 9) w hwS).hasDerivWithinAt
    · intro w hw
      have hwS : w ∈ S := interior_subset hw
      have hq := qWell_pos_on_Icc ha hwS.1 hwS.2
      have hH_ge : 9 / 10 * E1Well y a w ≤ HWell y a w := (HWell_bounds y ha hwS.1 hwS.2).1
      have h2 := abs_le.mp (show |y w * deriv y w| ≤ E1Well y a w / 2 by
        linarith [two_mul_abs_mul_deriv_le_E1Well y hq])
      have h_br : 0 ≤ y w * deriv y w + 5 / 9 * HWell y a w := by
        linarith [h2.1]
      have hα'_nonpos : -(-a + w ^ 2 / 2) * Real.sqrt (qWell a w) / (4 * qWell a w ^ 3) ≤ 0 := by
        have hA : 0 < -a := by linarith
        exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [Real.sqrt_nonneg (qWell a w)]) (by positivity)
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hα'_nonpos h_br) (Real.exp_pos _).le
  have hfDn_mono : MonotoneOn fDn S := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (z1Well a))
    · intro w hw
      exact (hderiv (-(5 / 9)) w hw).continuousAt.continuousWithinAt
    · intro w hw
      have hwS : w ∈ S := interior_subset hw
      exact (hderiv (-(5 / 9)) w hwS).hasDerivWithinAt
    · intro w hw
      have hwS : w ∈ S := interior_subset hw
      have hq := qWell_pos_on_Icc ha hwS.1 hwS.2
      have hH_ge : 9 / 10 * E1Well y a w ≤ HWell y a w := (HWell_bounds y ha hwS.1 hwS.2).1
      have h2 := abs_le.mp (show |y w * deriv y w| ≤ E1Well y a w / 2 by
        linarith [two_mul_abs_mul_deriv_le_E1Well y hq])
      have h_br : y w * deriv y w + -(5 / 9) * HWell y a w ≤ 0 := by
        linarith [h2.2]
      have hα'_nonpos : -(-a + w ^ 2 / 2) * Real.sqrt (qWell a w) / (4 * qWell a w ^ 3) ≤ 0 := by
        have hA : 0 < -a := by linarith
        exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [Real.sqrt_nonneg (qWell a w)]) (by positivity)
      exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hα'_nonpos h_br) (Real.exp_pos _).le
  have h0S : (0 : ℝ) ∈ S := ⟨le_rfl, z1Well_nonneg a⟩
  have hα0 : alphaWell a 0 = 0 := by unfold alphaWell; simp
  have hH0 : HWell y a 0 = E1Well y a 0 := by unfold HWell; rw [hα0, zero_mul, zero_mul, add_zero]
  have hexp_ub : Real.exp ((1 : ℝ) / 9) ≤ 9 / 8 := by
    have h1 : (8 : ℝ) / 9 ≤ Real.exp (-(1 / 9 : ℝ)) := by
      linarith [Real.add_one_le_exp (-(1 / 9 : ℝ))]
    calc Real.exp ((1 : ℝ) / 9) = (Real.exp (-(1 / 9 : ℝ)))⁻¹ := by rw [Real.exp_neg, inv_inv]
      _ ≤ (8 / 9)⁻¹ := inv_anti₀ (by norm_num) h1
      _ = 9 / 8 := by norm_num
  have hexp_lb : 8 / 9 ≤ Real.exp (-(1 / 9 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1 / 9 : ℝ))]
  intro z hz
  have hH_bds := HWell_bounds y ha hz.1 hz.2
  have hα_bds := abs_le.mp (abs_alphaWell_le ha hz.1 hz.2)
  have hUp : fUp z ≤ fUp 0 := hfUp_anti h0S hz hz.1
  have hDn : fDn 0 ≤ fDn z := hfDn_mono h0S hz hz.1
  have hfUp0 : fUp 0 = E1Well y a 0 := by simp [fUp, hα0, hH0]
  have hfDn0 : fDn 0 = E1Well y a 0 := by simp [fDn, hα0, hH0]
  rw [hfUp0] at hUp
  rw [hfDn0] at hDn
  have hHz_le : HWell y a z ≤ E1Well y a 0 * Real.exp (1 / 9) := by
    calc HWell y a z = fUp z * Real.exp (-(5 / 9 * alphaWell a z)) := by
          simp [fUp, mul_assoc, ← Real.exp_add]
      _ ≤ E1Well y a 0 * Real.exp (-(5 / 9 * alphaWell a z)) := by gcongr
      _ ≤ E1Well y a 0 * Real.exp (1 / 9) := by
          gcongr
          · exact E1Well_nonneg y a 0
          · linarith
  have hHz_ge : E1Well y a 0 * Real.exp (-(1 / 9 : ℝ)) ≤ HWell y a z := by
    calc E1Well y a 0 * Real.exp (-(1 / 9 : ℝ))
        ≤ E1Well y a 0 * Real.exp (5 / 9 * alphaWell a z) := by
          gcongr
          · exact E1Well_nonneg y a 0
          · linarith
      _ ≤ fDn z * Real.exp (5 / 9 * alphaWell a z) := by gcongr
      _ = HWell y a z := by simp [fDn, mul_assoc, ← Real.exp_add]
  constructor
  · calc 80 / 99 * E1Well y a 0 = 10 / 11 * (E1Well y a 0 * (8 / 9)) := by ring
      _ ≤ 10 / 11 * (E1Well y a 0 * Real.exp (-(1 / 9 : ℝ))) := by gcongr; exact E1Well_nonneg y a 0
      _ ≤ 10 / 11 * HWell y a z := by gcongr
      _ ≤ E1Well y a z := by linarith [hH_bds.2]
  · calc E1Well y a z ≤ 10 / 9 * HWell y a z := by linarith [hH_bds.1]
      _ ≤ 10 / 9 * (E1Well y a 0 * Real.exp (1 / 9)) := by gcongr
      _ ≤ 10 / 9 * (E1Well y a 0 * (9 / 8)) := by gcongr; exact E1Well_nonneg y a 0
      _ = 5 / 4 * E1Well y a 0 := by ring

/-- Corollary: `0.7 * E₁(0) ≤ E₁(z) ≤ 1.4 * E₁(0)` and `0.86 * sqrt(E₁(0)) ≤ sqrt(E₁(z)) ≤ 1.17 * sqrt(E₁(0))`. -/
theorem E1Well_bounds_std {a : ℝ} (ha : a ≤ -4) (y : ℝ → ℝ)
    (hy : ∀ z ∈ Set.Icc 0 (z1Well a), DifferentiableAt ℝ y z)
    (hy' : ∀ z ∈ Set.Icc 0 (z1Well a), DifferentiableAt ℝ (deriv y) z)
    (hode : ∀ z ∈ Set.Icc 0 (z1Well a), deriv (deriv y) z = (z ^ 2 / 4 + a) * y z) :
    ∀ z ∈ Set.Icc 0 (z1Well a),
      7 / 10 * E1Well y a 0 ≤ E1Well y a z ∧ E1Well y a z ≤ 7 / 5 * E1Well y a 0 ∧
      86 / 100 * Real.sqrt (E1Well y a 0) ≤ Real.sqrt (E1Well y a z) ∧
        Real.sqrt (E1Well y a z) ≤ 117 / 100 * Real.sqrt (E1Well y a 0) := by
  intro z hz
  obtain ⟨hl, hu⟩ := E1Well_bounds ha y hy hy' hode z hz
  have h0 : 0 ≤ E1Well y a 0 := E1Well_nonneg y a 0
  have hsq1 : (86 / 100 : ℝ) ^ 2 ≤ 80 / 99 := by norm_num
  have hsq2 : (5 / 4 : ℝ) ≤ (117 / 100 : ℝ) ^ 2 := by norm_num
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 86 / 100), ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    calc (86 / 100 : ℝ) ^ 2 * E1Well y a 0 ≤ 80 / 99 * E1Well y a 0 := by gcongr
      _ ≤ E1Well y a z := hl
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 117 / 100), ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    calc E1Well y a z ≤ 5 / 4 * E1Well y a 0 := hu
      _ ≤ (117 / 100 : ℝ) ^ 2 * E1Well y a 0 := by gcongr

/-! ### Link to `env_well` on `[0, z₁]` for `pcU` and `pcV` -/

lemma env_U_eq_Mbal_mul_sqrt_E1Well {a z : ℝ} (ha : a ≤ -4) (hz0 : 0 ≤ z) (hz1 : z ≤ z1Well a) :
    Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) =
      kappaBal a * Mbal a z * Real.sqrt (E1Well (pcU a) a z) := by
  have hκ := kappaBal_pos a
  have hM := Mbal_pos a z
  have hq := qWell_pos_on_Icc ha hz0 hz1
  have hk : k2 a z = qWell a z := k2_eq_qWell ha hz0 hz1
  have hs_pos : 0 < Real.sqrt (qWell a z) := Real.sqrt_pos.mpr hq
  rw [← Real.sqrt_sq (mul_nonneg hκ.le hM.le), ← Real.sqrt_mul (by positivity)]
  congr 1
  rw [mul_pow (kappaBal a) (Mbal a z) 2, Mbal_sq a z, hk]
  unfold ut E1Well
  field_simp [hs_pos.ne']
  rw [Real.sq_sqrt hq.le]
  ring

lemma env_V_eq_Mbal_mul_sqrt_E1Well {a z : ℝ} (ha : a ≤ -4) (hz0 : 0 ≤ z) (hz1 : z ≤ z1Well a) :
    Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) =
      Real.sqrt (π / 2) * (kappaBal a)⁻¹ * Mbal a z * Real.sqrt (E1Well (pcV a) a z) := by
  have hκ := kappaBal_pos a
  have hM := Mbal_pos a z
  have hq := qWell_pos_on_Icc ha hz0 hz1
  have hk : k2 a z = qWell a z := k2_eq_qWell ha hz0 hz1
  have hs_pos : 0 < Real.sqrt (qWell a z) := Real.sqrt_pos.mpr hq
  have hc : 0 ≤ Real.sqrt (π / 2) * (kappaBal a)⁻¹ * Mbal a z := by positivity
  rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (by positivity)]
  congr 1
  rw [mul_pow (Real.sqrt (π / 2) * (kappaBal a)⁻¹) (Mbal a z) 2, Mbal_sq a z, hk]
  unfold vt E1Well
  field_simp [hs_pos.ne']
  rw [Real.sq_sqrt hq.le]
  ring

/-- **E2 (`env_well` on `[0, z₁]` for `pcU` and `pcV`)**: for `a ≤ -4` and `0 ≤ z ≤ z₁(a)`,
both the `U`-envelope and `V`-envelope satisfy two-sided bounds with explicit absolute constants
`(43/100, 117/50)` (and hence `(2/5, 5/2)`), where `E_well(a, z) = 1`. -/
theorem env_well_on_Icc_U_V {a z : ℝ} (ha : a ≤ -4) (hz0 : 0 ≤ z) (hz1 : z ≤ z1Well a) :
    (43 / 100 * (Ewell a z * Mbal a z) ≤
        Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ∧
      Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ≤
        117 / 50 * (Ewell a z * Mbal a z)) ∧
    (43 / 100 * ((Ewell a z)⁻¹ * Mbal a z) ≤
        Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) ∧
      Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) ≤
        117 / 50 * ((Ewell a z)⁻¹ * Mbal a z)) := by
  have ha0 : a ≤ 0 := by linarith
  have h0 : (0 : ℝ) ≤ z1Well a := z1Well_nonneg a
  have hEwell_z : Ewell a z = 1 := Ewell_eq_one_on_Icc ha hz1
  have hEwell_0 : Ewell a 0 = 1 := Ewell_zero a
  have hM0 := Mbal_pos a 0
  have hMz := Mbal_pos a z
  have hκ := kappaBal_pos a
  have hU0 := origin_env_well_U ha0
  have hV0 := origin_env_well_V ha0
  rw [env_U_eq_Mbal_mul_sqrt_E1Well ha le_rfl h0, hEwell_0, one_mul] at hU0
  rw [env_V_eq_Mbal_mul_sqrt_E1Well ha le_rfl h0, hEwell_0, inv_one, one_mul] at hV0
  have hU0_lb : 1 / 2 ≤ kappaBal a * Real.sqrt (E1Well (pcU a) a 0) := by
    have : 1 / 2 * Mbal a 0 ≤ (kappaBal a * Real.sqrt (E1Well (pcU a) a 0)) * Mbal a 0 := by
      linarith [hU0.1]
    exact le_of_mul_le_mul_right this hM0
  have hU0_ub : kappaBal a * Real.sqrt (E1Well (pcU a) a 0) ≤ 2 := by
    have : (kappaBal a * Real.sqrt (E1Well (pcU a) a 0)) * Mbal a 0 ≤ 2 * Mbal a 0 := by
      linarith [hU0.2]
    exact le_of_mul_le_mul_right this hM0
  have hcV : 0 ≤ Real.sqrt (π / 2) * (kappaBal a)⁻¹ := by positivity
  have hV0_lb : 1 / 2 ≤ Real.sqrt (π / 2) * (kappaBal a)⁻¹ * Real.sqrt (E1Well (pcV a) a 0) := by
    have : 1 / 2 * Mbal a 0 ≤ (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * Real.sqrt (E1Well (pcV a) a 0)) * Mbal a 0 := by
      linarith [hV0.1]
    exact le_of_mul_le_mul_right this hM0
  have hV0_ub : Real.sqrt (π / 2) * (kappaBal a)⁻¹ * Real.sqrt (E1Well (pcV a) a 0) ≤ 2 := by
    have : (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * Real.sqrt (E1Well (pcV a) a 0)) * Mbal a 0 ≤ 2 * Mbal a 0 := by
      linarith [hV0.2]
    exact le_of_mul_le_mul_right this hM0
  have hU_E1 := (E1Well_bounds_std ha (pcU a)
    (fun w _ => (hasDerivAt_pcU a w).differentiableAt)
    (fun w _ => by rw [deriv_pcU]; exact (hasDerivAt_pcUD a w).differentiableAt)
    (fun w _ => pcU_ode a w) z ⟨hz0, hz1⟩).2.2
  have hV_E1 := (E1Well_bounds_std ha (pcV a)
    (fun w _ => (hasDerivAt_pcV a w).differentiableAt)
    (fun w _ => by rw [deriv_pcV]; exact (hasDerivAt_pcVD a w).differentiableAt)
    (fun w _ => pcV_ode a w) z ⟨hz0, hz1⟩).2.2
  rw [env_U_eq_Mbal_mul_sqrt_E1Well ha hz0 hz1, env_V_eq_Mbal_mul_sqrt_E1Well ha hz0 hz1,
    hEwell_z, inv_one, one_mul]
  constructor
  · constructor
    · calc 43 / 100 * Mbal a z = (86 / 100) * (1 / 2) * Mbal a z := by ring
        _ ≤ (86 / 100) * (kappaBal a * Real.sqrt (E1Well (pcU a) a 0)) * Mbal a z := by gcongr
        _ = kappaBal a * Mbal a z * (86 / 100 * Real.sqrt (E1Well (pcU a) a 0)) := by ring
        _ ≤ kappaBal a * Mbal a z * Real.sqrt (E1Well (pcU a) a z) := by gcongr; exact hU_E1.1
    · calc kappaBal a * Mbal a z * Real.sqrt (E1Well (pcU a) a z)
          ≤ kappaBal a * Mbal a z * (117 / 100 * Real.sqrt (E1Well (pcU a) a 0)) := by gcongr; exact hU_E1.2
        _ = (117 / 100) * (kappaBal a * Real.sqrt (E1Well (pcU a) a 0)) * Mbal a z := by ring
        _ ≤ (117 / 100) * 2 * Mbal a z := by gcongr
        _ = 117 / 50 * Mbal a z := by ring
  · constructor
    · calc 43 / 100 * Mbal a z = (86 / 100) * (1 / 2) * Mbal a z := by ring
        _ ≤ (86 / 100) * (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * Real.sqrt (E1Well (pcV a) a 0)) * Mbal a z := by gcongr
        _ = Real.sqrt (π / 2) * (kappaBal a)⁻¹ * Mbal a z * (86 / 100 * Real.sqrt (E1Well (pcV a) a 0)) := by ring
        _ ≤ Real.sqrt (π / 2) * (kappaBal a)⁻¹ * Mbal a z * Real.sqrt (E1Well (pcV a) a z) := by gcongr; exact hV_E1.1
    · calc Real.sqrt (π / 2) * (kappaBal a)⁻¹ * Mbal a z * Real.sqrt (E1Well (pcV a) a z)
          ≤ Real.sqrt (π / 2) * (kappaBal a)⁻¹ * Mbal a z * (117 / 100 * Real.sqrt (E1Well (pcV a) a 0)) := by gcongr; exact hV_E1.2
        _ = (117 / 100) * (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * Real.sqrt (E1Well (pcV a) a 0)) * Mbal a z := by ring
        _ ≤ (117 / 100) * 2 * Mbal a z := by gcongr
        _ = 117 / 50 * Mbal a z := by ring

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.E1Well_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms E1Well_bounds

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.E1Well_bounds_std' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms E1Well_bounds_std

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.env_well_on_Icc_U_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms env_well_on_Icc_U_V

end FormalResearch.JacobiEigenvectors.Charts
