module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.PCEnergyWell

/-!
# Paper J, Layer 4 (phase B2, E3): constant-scale energy bound on the Airy zone `[z₁, z₂]`

For `a ≤ -4` (`A = -a ≥ 4`), put `z₁(a) = 2 * sqrt(A - 2 * A^{1/3})` (`z1Well a`) and
`z₂(a) = 2 * sqrt(A + 2 * A^{1/3})` (`z2Airy a`).
On `[z₁(a), z₂(a)]`:
* `A^{1/6} * (z₂(a) - z₁(a)) ≤ 6` (`airy_length_bound`),
* `A^{1/3} ≤ k₂(a, z) ≤ 2 * A^{1/3}` (`k2_airy_bounds`),
* for any real solution `y` of Weber's equation `y'' = (z^2/4 + a) * y` on `[z₁(a), z₂(a)]`,
  the constant-scale energy `R₀(z) = y(z)^2 + y'(z)^2 / A^{1/3}` satisfies
  `|R₀'(z)| ≤ 3 * A^{1/6} * R₀(z)` and hence
  `exp(-18) * R₀(z₁) ≤ R₀(z) ≤ exp(18) * R₀(z₁)` (`R0Airy_bounds`).

Combining with `PCEnergyWell.env_well_on_Icc_U_V` at `z₁(a)` gives two-sided bounds on
`sqrt(u~^2 + u~'^2 / k₂)` and `sqrt(v~^2 + v~'^2 / k₂)` in terms of `Mbal a z` on `[z₁, z₂]`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Real

/-- The outer Airy endpoint `z₂(a) = 2 * sqrt(-a + 2 * (-a)^{1/3})` for `a ≤ -4`. -/
def z2Airy (a : ℝ) : ℝ := 2 * Real.sqrt (-a + 2 * (-a) ^ ((1 : ℝ) / 3))

lemma z1Well_le_z2Airy {a : ℝ} (ha : a ≤ -4) : z1Well a ≤ z2Airy a := by
  unfold z1Well z2Airy
  have hA0 : 0 ≤ -a := by linarith
  have h2 : 0 ≤ (-a) ^ ((1 : ℝ) / 3) := by positivity
  gcongr
  linarith

lemma airy_length_bound {a : ℝ} (ha : a ≤ -4) :
    (-a) ^ ((1 : ℝ) / 6) * (z2Airy a - z1Well a) ≤ 6 := by
  have hA : 4 ≤ -a := by linarith
  have hA0 : 0 < -a := by linarith
  have hsub : 0 ≤ -a - 2 * (-a) ^ ((1 : ℝ) / 3) := by
    linarith [two_mul_rpow_one_third_lt hA]
  set s1 := Real.sqrt (-a - 2 * (-a) ^ ((1 : ℝ) / 3))
  set s2 := Real.sqrt (-a + 2 * (-a) ^ ((1 : ℝ) / 3))
  have hs1_nonneg : 0 ≤ s1 := Real.sqrt_nonneg _
  have hs2_pos : 0 < s2 := Real.sqrt_pos.mpr (by positivity)
  have hs_diff : s2 ^ 2 - s1 ^ 2 = 4 * (-a) ^ ((1 : ℝ) / 3) := by
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt hsub]; ring
  have hs2_ge : Real.sqrt (-a) ≤ s2 := by
    apply Real.sqrt_le_sqrt
    linarith [Real.rpow_pos_of_pos hA0 ((1 : ℝ) / 3)]
  have hs1_ge : 1 / 3 * Real.sqrt (-a) ≤ s1 := by
    have hsq : (1 / 3 * Real.sqrt (-a)) ^ 2 ≤ -a - 2 * (-a) ^ ((1 : ℝ) / 3) := by
      have hcube : (18 * (-a) ^ ((1 : ℝ) / 3)) ^ 3 < (8 * (-a)) ^ 3 := by
        have h1 : ((-a) ^ ((1 : ℝ) / 3)) ^ 3 = -a := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num
        have hA2 : 16 ≤ (-a) ^ 2 := by nlinarith
        calc (18 * (-a) ^ ((1 : ℝ) / 3)) ^ 3 = 5832 * ((-a) ^ ((1 : ℝ) / 3)) ^ 3 := by ring
          _ = 5832 * (-a) := by rw [h1]
          _ < 512 * 16 * (-a) := by linarith
          _ ≤ 512 * (-a) ^ 2 * (-a) := by gcongr
          _ = (8 * (-a)) ^ 3 := by ring
      have hlin : 18 * (-a) ^ ((1 : ℝ) / 3) ≤ 8 * (-a) :=
        (lt_of_pow_lt_pow_left₀ 3 (by positivity) hcube).le
      rw [mul_pow, Real.sq_sqrt hA0.le]
      linarith
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 / 3 * Real.sqrt (-a))]
    exact Real.sqrt_le_sqrt hsq
  have hsum_pos : 0 < s2 + s1 := by linarith
  have hsum_ge : 4 / 3 * Real.sqrt (-a) ≤ s2 + s1 := by linarith
  have hdiff_eq : z2Airy a - z1Well a = 8 * (-a) ^ ((1 : ℝ) / 3) / (s2 + s1) := by
    unfold z2Airy z1Well
    change 2 * s2 - 2 * s1 = 8 * (-a) ^ ((1 : ℝ) / 3) / (s2 + s1)
    rw [eq_div_iff hsum_pos.ne']
    linarith [hs_diff]
  have hrpow : (-a) ^ ((1 : ℝ) / 6) * (-a) ^ ((1 : ℝ) / 3) = Real.sqrt (-a) := by
    rw [← Real.rpow_add hA0, Real.sqrt_eq_rpow]
    norm_num
  rw [hdiff_eq]
  calc (-a) ^ ((1 : ℝ) / 6) * (8 * (-a) ^ ((1 : ℝ) / 3) / (s2 + s1))
      = 8 * ((-a) ^ ((1 : ℝ) / 6) * (-a) ^ ((1 : ℝ) / 3)) / (s2 + s1) := by ring
    _ = 8 * Real.sqrt (-a) / (s2 + s1) := by rw [hrpow]
    _ ≤ 8 * Real.sqrt (-a) / (4 / 3 * Real.sqrt (-a)) := by gcongr
    _ = 6 := by
        have hsA : Real.sqrt (-a) ≠ 0 := (Real.sqrt_pos.mpr hA0).ne'
        field_simp [hsA]
        norm_num

lemma abs_p_le_on_airy {a z : ℝ} (ha : a ≤ -4) (hz1 : z1Well a ≤ z) (hz2 : z ≤ z2Airy a) :
    |z ^ 2 / 4 + a| ≤ 2 * (-a) ^ ((1 : ℝ) / 3) := by
  have hA : 4 ≤ -a := by linarith
  have hsub : 0 ≤ -a - 2 * (-a) ^ ((1 : ℝ) / 3) := by
    linarith [two_mul_rpow_one_third_lt hA]
  have hz0 : 0 ≤ z := le_trans (z1Well_nonneg a) hz1
  have hz_lb : 4 * (-a - 2 * (-a) ^ ((1 : ℝ) / 3)) ≤ z ^ 2 := by
    calc 4 * (-a - 2 * (-a) ^ ((1 : ℝ) / 3))
        = (z1Well a) ^ 2 := by unfold z1Well; rw [mul_pow, Real.sq_sqrt hsub]; ring
      _ ≤ z ^ 2 := by nlinarith [z1Well_nonneg a]
  have hz_ub : z ^ 2 ≤ 4 * (-a + 2 * (-a) ^ ((1 : ℝ) / 3)) := by
    have hA0 : 0 ≤ -a := by linarith
    have h2 : 0 ≤ (-a) ^ ((1 : ℝ) / 3) := by positivity
    calc z ^ 2 ≤ (z2Airy a) ^ 2 := by nlinarith
      _ = 4 * (-a + 2 * (-a) ^ ((1 : ℝ) / 3)) := by
          unfold z2Airy; rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [abs_le]
  constructor <;> linarith

lemma k2_airy_bounds {a z : ℝ} (ha : a ≤ -4) (hz1 : z1Well a ≤ z) (hz2 : z ≤ z2Airy a) :
    (-a) ^ ((1 : ℝ) / 3) ≤ k2 a z ∧ k2 a z ≤ 2 * (-a) ^ ((1 : ℝ) / 3) := by
  have habs_a : max |a| 1 = -a := by
    rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
  have hp := abs_p_le_on_airy ha hz1 hz2
  unfold k2
  rw [habs_a]
  exact ⟨le_max_right _ _, max_le hp (by linarith [Real.rpow_pos_of_pos (by linarith : 0 < -a) ((1 : ℝ) / 3)])⟩

/-- Constant-scale energy `R₀(z) = y(z)^2 + y'(z)^2 / (-a)^{1/3}` on `[z₁, z₂]`. -/
def R0Airy (y : ℝ → ℝ) (a z : ℝ) : ℝ :=
  y z ^ 2 + deriv y z ^ 2 / (-a) ^ ((1 : ℝ) / 3)

lemma R0Airy_nonneg (y : ℝ → ℝ) {a : ℝ} (ha : a ≤ -4) (z : ℝ) : 0 ≤ R0Airy y a z := by
  unfold R0Airy
  have hA0 : 0 ≤ -a := by linarith
  have : 0 ≤ (-a) ^ ((1 : ℝ) / 3) := by positivity
  positivity

/-- **E3 (general Weber solution on `[z₁, z₂]`)**: for any solution `y` of Weber's equation
`y'' = (z^2/4 + a) * y` on `[z₁(a), z₂(a)]` with `a ≤ -4`,
`exp(-18) * R₀(z₁) ≤ R₀(z) ≤ exp(18) * R₀(z₁)` for all `z ∈ [z₁(a), z₂(a)]`. -/
theorem R0Airy_bounds {a : ℝ} (ha : a ≤ -4) (y : ℝ → ℝ)
    (hy : ∀ z ∈ Set.Icc (z1Well a) (z2Airy a), DifferentiableAt ℝ y z)
    (hy' : ∀ z ∈ Set.Icc (z1Well a) (z2Airy a), DifferentiableAt ℝ (deriv y) z)
    (hode : ∀ z ∈ Set.Icc (z1Well a) (z2Airy a), deriv (deriv y) z = (z ^ 2 / 4 + a) * y z) :
    ∀ z ∈ Set.Icc (z1Well a) (z2Airy a),
      Real.exp (-18) * R0Airy y a (z1Well a) ≤ R0Airy y a z ∧
        R0Airy y a z ≤ Real.exp 18 * R0Airy y a (z1Well a) := by
  have hA0 : 0 < -a := by linarith
  have hA13 : 0 < (-a) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hA0 _
  have hA16 : 0 < (-a) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hA0 _
  have hA16_sq : ((-a) ^ ((1 : ℝ) / 6)) ^ 2 = (-a) ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num
  let S := Set.Icc (z1Well a) (z2Airy a)
  let c := 3 * (-a) ^ ((1 : ℝ) / 6)
  have hc_nonneg : 0 ≤ c := by positivity
  have hR0_deriv : ∀ w ∈ S, HasDerivAt (R0Airy y a)
      (2 * y w * deriv y w * (1 + (w ^ 2 / 4 + a) / (-a) ^ ((1 : ℝ) / 3))) w := by
    intro w hw
    have hy_d : HasDerivAt y (deriv y w) w := (hy w hw).hasDerivAt
    have hy'_d : HasDerivAt (deriv y) ((w ^ 2 / 4 + a) * y w) w := by
      rw [← hode w hw]; exact (hy' w hw).hasDerivAt
    have hy2_d : HasDerivAt (fun t => y t ^ 2) (2 * y w * deriv y w) w := by
      convert hy_d.pow 2 using 1; ring
    have hy'2_d : HasDerivAt (fun t => deriv y t ^ 2 / (-a) ^ ((1 : ℝ) / 3))
        (2 * deriv y w * ((w ^ 2 / 4 + a) * y w) / (-a) ^ ((1 : ℝ) / 3)) w := by
      convert (hy'_d.pow 2).div_const ((-a) ^ ((1 : ℝ) / 3)) using 1; ring
    convert hy2_d.add hy'2_d using 1
    · ext t; unfold R0Airy; rfl
    · ring
  have hR0'_bound : ∀ w ∈ S,
      |2 * y w * deriv y w * (1 + (w ^ 2 / 4 + a) / (-a) ^ ((1 : ℝ) / 3))| ≤ c * R0Airy y a w := by
    intro w hw
    have hp := abs_p_le_on_airy ha hw.1 hw.2
    have hfac : |1 + (w ^ 2 / 4 + a) / (-a) ^ ((1 : ℝ) / 3)| ≤ 3 := by
      have hdiv : |(w ^ 2 / 4 + a) / (-a) ^ ((1 : ℝ) / 3)| ≤ 2 := by
        rw [abs_div, abs_of_pos hA13, div_le_iff₀ hA13]
        exact hp
      calc |1 + (w ^ 2 / 4 + a) / (-a) ^ ((1 : ℝ) / 3)|
          ≤ |1| + |(w ^ 2 / 4 + a) / (-a) ^ ((1 : ℝ) / 3)| := abs_add_le _ _
        _ ≤ 1 + 2 := by norm_num; linarith
        _ = 3 := by norm_num
    have h2yy' : |2 * y w * deriv y w| ≤ (-a) ^ ((1 : ℝ) / 6) * R0Airy y a w := by
      have hsq : 0 ≤ ((-a) ^ ((1 : ℝ) / 6) * |y w| - |deriv y w|) ^ 2 := sq_nonneg _
      have hmul : 2 * ((-a) ^ ((1 : ℝ) / 6) * |y w * deriv y w|) ≤
          (-a) ^ ((1 : ℝ) / 3) * y w ^ 2 + deriv y w ^ 2 := by
        rw [abs_mul, ← hA16_sq]
        nlinarith [sq_abs (y w), sq_abs (deriv y w)]
      have hR0_eq : (-a) ^ ((1 : ℝ) / 3) * R0Airy y a w = (-a) ^ ((1 : ℝ) / 3) * y w ^ 2 + deriv y w ^ 2 := by
        unfold R0Airy; field_simp [hA13.ne']
      rw [← hR0_eq] at hmul
      have hmul2 : (-a) ^ ((1 : ℝ) / 6) * (2 * |y w * deriv y w|) ≤
          (-a) ^ ((1 : ℝ) / 6) * ((-a) ^ ((1 : ℝ) / 6) * R0Airy y a w) := by
        calc (-a) ^ ((1 : ℝ) / 6) * (2 * |y w * deriv y w|)
            = 2 * ((-a) ^ ((1 : ℝ) / 6) * |y w * deriv y w|) := by ring
          _ ≤ (-a) ^ ((1 : ℝ) / 3) * R0Airy y a w := hmul
          _ = (-a) ^ ((1 : ℝ) / 6) * ((-a) ^ ((1 : ℝ) / 6) * R0Airy y a w) := by
              rw [← mul_assoc, ← sq, hA16_sq]
      rw [mul_assoc, abs_mul, abs_of_nonneg (by norm_num)]
      exact le_of_mul_le_mul_left hmul2 hA16
    calc |2 * y w * deriv y w * (1 + (w ^ 2 / 4 + a) / (-a) ^ ((1 : ℝ) / 3))|
        = |2 * y w * deriv y w| * |1 + (w ^ 2 / 4 + a) / (-a) ^ ((1 : ℝ) / 3)| := abs_mul _ _
      _ ≤ ((-a) ^ ((1 : ℝ) / 6) * R0Airy y a w) * 3 := by
          gcongr; exact mul_nonneg hA16.le (R0Airy_nonneg y ha w)
      _ = c * R0Airy y a w := by ring
  let fUp : ℝ → ℝ := fun w => R0Airy y a w * Real.exp (-c * (w - z1Well a))
  let fDn : ℝ → ℝ := fun w => R0Airy y a w * Real.exp (c * (w - z1Well a))
  have hfUp_anti : AntitoneOn fUp S := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (z1Well a) (z2Airy a))
    · intro w hw
      exact ((hR0_deriv w hw).continuousAt.mul (by fun_prop)).continuousWithinAt
    · intro w hw
      have hwS : w ∈ S := interior_subset hw
      have hd1 := hR0_deriv w hwS
      have hd2 : HasDerivAt (fun t => Real.exp (-c * (t - z1Well a)))
          (-c * Real.exp (-c * (w - z1Well a))) w := by
        have hlin : HasDerivAt (fun t => -c * (t - z1Well a)) (-c) w := by
          simpa using ((hasDerivAt_id w).sub_const (z1Well a)).const_mul (-c)
        simpa [mul_comm] using hlin.exp
      exact (hd1.mul hd2).hasDerivWithinAt
    · intro w hw
      have hwS : w ∈ S := interior_subset hw
      have hb := (abs_le.mp (hR0'_bound w hwS)).2
      have hexp : 0 ≤ Real.exp (-c * (w - z1Well a)) := (Real.exp_pos _).le
      have hcomb : (2 * y w * deriv y w * (1 + (w ^ 2 / 4 + a) / (-a) ^ ((1 : ℝ) / 3)) -
          c * R0Airy y a w) * Real.exp (-c * (w - z1Well a)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hexp
      linarith
  have hfDn_mono : MonotoneOn fDn S := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (z1Well a) (z2Airy a))
    · intro w hw
      exact ((hR0_deriv w hw).continuousAt.mul (by fun_prop)).continuousWithinAt
    · intro w hw
      have hwS : w ∈ S := interior_subset hw
      have hd1 := hR0_deriv w hwS
      have hd2 : HasDerivAt (fun t => Real.exp (c * (t - z1Well a)))
          (c * Real.exp (c * (w - z1Well a))) w := by
        have hlin : HasDerivAt (fun t => c * (t - z1Well a)) c w := by
          simpa using ((hasDerivAt_id w).sub_const (z1Well a)).const_mul c
        simpa [mul_comm] using hlin.exp
      exact (hd1.mul hd2).hasDerivWithinAt
    · intro w hw
      have hwS : w ∈ S := interior_subset hw
      have hb := (abs_le.mp (hR0'_bound w hwS)).1
      have hexp : 0 ≤ Real.exp (c * (w - z1Well a)) := (Real.exp_pos _).le
      have hcomb : (2 * y w * deriv y w * (1 + (w ^ 2 / 4 + a) / (-a) ^ ((1 : ℝ) / 3)) +
          c * R0Airy y a w) * Real.exp (c * (w - z1Well a)) ≥ 0 :=
        mul_nonneg (by linarith) hexp
      linarith
  have hz1S : z1Well a ∈ S := ⟨le_rfl, z1Well_le_z2Airy ha⟩
  have hlen : c * (z2Airy a - z1Well a) ≤ 18 := by
    calc c * (z2Airy a - z1Well a) = 3 * ((-a) ^ ((1 : ℝ) / 6) * (z2Airy a - z1Well a)) := by ring
      _ ≤ 3 * 6 := by gcongr; exact airy_length_bound ha
      _ = 18 := by norm_num
  intro z hz
  have hR0_0 : 0 ≤ R0Airy y a (z1Well a) := R0Airy_nonneg y ha (z1Well a)
  have hUp : fUp z ≤ fUp (z1Well a) := hfUp_anti hz1S hz hz.1
  have hDn : fDn (z1Well a) ≤ fDn z := hfDn_mono hz1S hz hz.1
  have hfUp1 : fUp (z1Well a) = R0Airy y a (z1Well a) := by simp [fUp]
  have hfDn1 : fDn (z1Well a) = R0Airy y a (z1Well a) := by simp [fDn]
  rw [hfUp1] at hUp
  rw [hfDn1] at hDn
  have hcz : c * (z - z1Well a) ≤ 18 := by
    calc c * (z - z1Well a) ≤ c * (z2Airy a - z1Well a) := by gcongr; exact hz.2
      _ ≤ 18 := hlen
  constructor
  · calc Real.exp (-18) * R0Airy y a (z1Well a)
        ≤ Real.exp (-(c * (z - z1Well a))) * R0Airy y a (z1Well a) := by gcongr
      _ ≤ Real.exp (-(c * (z - z1Well a))) * fDn z := by gcongr
      _ = R0Airy y a z := by simp [fDn, mul_left_comm, ← Real.exp_add]
  · calc R0Airy y a z = fUp z * Real.exp (c * (z - z1Well a)) := by
          simp [fUp, mul_assoc, ← Real.exp_add]
      _ ≤ R0Airy y a (z1Well a) * Real.exp (c * (z - z1Well a)) := by gcongr
      _ ≤ R0Airy y a (z1Well a) * Real.exp 18 := by gcongr
      _ = Real.exp 18 * R0Airy y a (z1Well a) := by ring

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.R0Airy_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms R0Airy_bounds

end FormalResearch.JacobiEigenvectors.Charts