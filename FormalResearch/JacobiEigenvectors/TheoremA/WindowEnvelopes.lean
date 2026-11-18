module

public import FormalResearch.JacobiEigenvectors.TheoremA.Statements

/-!
# Paper J, Layer 2: the window envelopes, mass and counting (`lem:tha-win`, `PropThaWin`)

Source: Paper J `app_thmA.tex`, "The window: envelopes, mass and counting", lemma `lem:tha-win` (items (1), (2), (3), (5)), with the
setting of `Statements.lean` (`PropThaWin`, after the finding F-W1: the lattice facts at the chart edge are guarded by the neighbour rows
being on the chart).  Plan item L2.C3 (`PLAN.md`).  Namespace `FormalResearch.JacobiEigenvectors.TheoremA`.

Status:
* conjunct (1), the lattice facts and localisation (`win_conj1`): proved;
* conjunct (2), the weights (`weights_conj`): proved;
* conjunct (3), the envelopes (`envelope_conj3`): proved, for the `ParabolicCylinderFacts` premise of `PropThaWin`;
* conjunct (5), the window sums (`win_chart_sums`): proved; the far-field localisation (`farChart`, from the
  chart field `zeta_far_out`) supplies the outside-the-window bound the upper estimate needs.
* `propThaWin`: the frozen `PropThaWin` (with its `ParabolicCylinderFacts` premise, as stated), proved.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Real intervalIntegral
open FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.Setting



lemma ell_le_one (A : ℝ) (hA : 0 ≤ A) : (1 + A) ^ (-(1 : ℝ) / 6) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)

lemma ell_cube_mul_sqrt (A : ℝ) (hA : 0 ≤ A) :
    ((1 + A) ^ (-(1 : ℝ) / 6)) ^ 3 * Real.sqrt (1 + A) = 1 := by
  have hpos : (0 : ℝ) < 1 + A := by linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, Real.sqrt_eq_rpow, ← Real.rpow_add hpos]
  norm_num

lemma sqrt_half_le (A : ℝ) (hA : 0 ≤ A) : Real.sqrt A + 1 / 2 ≤ 3 / 2 * Real.sqrt (1 + A) := by
  have hs := Real.sq_sqrt hA
  have hr := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + A)
  have hs0 := Real.sqrt_nonneg A
  have hr0 := Real.sqrt_nonneg (1 + A)
  nlinarith [sq_nonneg (Real.sqrt A - 2 / 5), sq_nonneg (Real.sqrt A + Real.sqrt (1 + A))]

lemma well_integral_integrand (A : ℝ) (hA : 0 ≤ A) (t : ℝ) (hc : 2 * Real.sqrt A ≤ t) (hs2 : t - 2 * Real.sqrt A ≤ 2) :
    Real.sqrt (t ^ 2 / 4 - A) ≤ Real.sqrt (Real.sqrt A + 1 / 2) * Real.sqrt (t - 2 * Real.sqrt A) := by
  have hK : 0 ≤ Real.sqrt A + 1 / 2 := by positivity
  rw [← Real.sqrt_mul hK]
  apply Real.sqrt_le_sqrt
  have hsq : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  have hs0 : 0 ≤ t - 2 * Real.sqrt A := by linarith
  nlinarith [mul_nonneg hs0 (by linarith : (0:ℝ) ≤ 2 - (t - 2 * Real.sqrt A)), Real.sqrt_nonneg A,
    mul_nonneg hs0 (Real.sqrt_nonneg A)]

lemma well_integral_sq_le (A z : ℝ) (hA : 0 ≤ A) (hz : 2 * Real.sqrt A ≤ z) (hz2 : z ≤ 2 * Real.sqrt A + 2) :
    (∫ t in (2 * Real.sqrt A)..z, Real.sqrt (t ^ 2 / 4 - A)) ^ 2 ≤
      (4 / 9) * (Real.sqrt A + 1 / 2) * (z - 2 * Real.sqrt A) ^ 3 := by
  set c := 2 * Real.sqrt A with hc
  have hK : 0 ≤ Real.sqrt A + 1 / 2 := by positivity
  have hτ : 0 ≤ z - c := by linarith
  have hint : (∫ t in c..z, Real.sqrt (t ^ 2 / 4 - A)) ≤
      ∫ t in c..z, Real.sqrt (Real.sqrt A + 1 / 2) * Real.sqrt (t - c) := by
    apply intervalIntegral.integral_mono_on hz
    · apply Continuous.intervalIntegrable; fun_prop
    · apply Continuous.intervalIntegrable; fun_prop
    · intro t ht
      exact well_integral_integrand A hA t ht.1 (by linarith [ht.2])
  have h1 : ∫ t in c..z, Real.sqrt (t - c) = ∫ t in (0:ℝ)..(z - c), Real.sqrt t := by
    have := intervalIntegral.integral_comp_sub_right (fun t => Real.sqrt t) (a := c) (b := z) c
    simpa using this
  have hcomp : (∫ t in c..z, Real.sqrt (Real.sqrt A + 1 / 2) * Real.sqrt (t - c))
      = Real.sqrt (Real.sqrt A + 1 / 2) * ((2 / 3) * (z - c) ^ (3 / 2 : ℝ)) := by
    rw [intervalIntegral.integral_const_mul, h1]
    simp only [Real.sqrt_eq_rpow]
    rw [integral_rpow (Or.inl (by norm_num))]
    congr 1
    have e : (1 : ℝ) / 2 + 1 = 3 / 2 := by norm_num
    rw [e, Real.zero_rpow (by norm_num)]
    ring
  have hI0 : 0 ≤ ∫ t in c..z, Real.sqrt (t ^ 2 / 4 - A) :=
    intervalIntegral.integral_nonneg hz (fun t _ => Real.sqrt_nonneg _)
  have h2 := hint.trans_eq hcomp
  have h3 := pow_le_pow_left₀ hI0 h2 2
  have h4 : ((z - c) ^ (3 / 2 : ℝ)) ^ 2 = (z - c) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ]; norm_num
  have h5 : (Real.sqrt (Real.sqrt A + 1 / 2)) ^ 2 = Real.sqrt A + 1 / 2 := Real.sq_sqrt hK
  calc _ ≤ _ := h3
    _ = (4 / 9) * (Real.sqrt A + 1 / 2) * (z - c) ^ 3 := by
        rw [mul_pow, mul_pow, h5, h4]; ring

lemma ewell_integral_nonneg (A z : ℝ) (hA : 0 ≤ A) (hz : 2 * Real.sqrt A ≤ z) :
    0 ≤ ∫ t in (2 * Real.sqrt A)..z, Real.sqrt (t ^ 2 / 4 - A) :=
  intervalIntegral.integral_nonneg hz (fun t _ => Real.sqrt_nonneg _)

/-- Lower bound for the well weight (`a <= 0`): `e^{-5/2} <= Ewell a z` for `0 <= z <= 2 sqrt A + 2 l_A`, `A = -a`. -/
lemma ewell_lower (a z : ℝ) (ha : a ≤ 0) (hz : 0 ≤ z)
    (hzR : z ≤ 2 * Real.sqrt (max (-a) 0) + 2 * (1 + max (-a) 0) ^ (-(1 : ℝ) / 6)) :
    Real.exp (-(5 : ℝ) / 2) ≤ Ewell a z := by
  have hA : max (-a) 0 = -a := max_eq_left (by linarith)
  rw [hA] at hzR
  have hAnn : 0 ≤ -a := by linarith
  have hab : |a| = -a := abs_of_nonpos ha
  have hℓ1 := ell_le_one (-a) hAnn
  have hℓ0 : 0 ≤ (1 + -a) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by linarith) _
  unfold Ewell
  rw [hab]
  split_ifs with hcz
  · have hsq := well_integral_sq_le (-a) z hAnn hcz.le (by linarith)
    have hτ0 : 0 ≤ z - 2 * Real.sqrt (-a) := by linarith
    have hτ : z - 2 * Real.sqrt (-a) ≤ 2 * (1 + -a) ^ (-(1 : ℝ) / 6) := by linarith
    have hτ3 : (z - 2 * Real.sqrt (-a)) ^ 3 ≤ (2 * (1 + -a) ^ (-(1 : ℝ) / 6)) ^ 3 :=
      pow_le_pow_left₀ hτ0 hτ 3
    have hK := sqrt_half_le (-a) hAnn
    have hprod : (4 / 9) * (Real.sqrt (-a) + 1 / 2) * (z - 2 * Real.sqrt (-a)) ^ 3 ≤ 16 / 3 := by
      have h1 := mul_le_mul (mul_le_mul_of_nonneg_left hK (by norm_num : (0:ℝ) ≤ 4 / 9)) hτ3
        (pow_nonneg hτ0 3) (by positivity)
      have h2 : (4 / 9) * (3 / 2 * Real.sqrt (1 + -a)) * (2 * (1 + -a) ^ (-(1 : ℝ) / 6)) ^ 3 = 16 / 3 := by
        linear_combination (16 / 3) * ell_cube_mul_sqrt (-a) hAnn
      linarith [h1, h2]
    have hI0 := ewell_integral_nonneg (-a) z hAnn hcz.le
    have hI : (∫ t in (2 * Real.sqrt (-a))..z, Real.sqrt (t ^ 2 / 4 - -a)) ≤ 5 / 2 := by
      nlinarith [hsq, hprod, hI0]
    apply Real.exp_le_exp.mpr
    linarith
  · calc Real.exp (-(5 : ℝ) / 2) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num)
      _ = 1 := Real.exp_zero

/-- Upper bound for the well weight: `Ewell a z <= 1` for `z >= 0` and `a <= 0`. -/
lemma ewell_le_one (a z : ℝ) (ha : a ≤ 0) : Ewell a z ≤ 1 := by
  have hab : |a| = -a := abs_of_nonpos ha
  unfold Ewell
  rw [hab]
  split_ifs with hcz
  · have hI0 := ewell_integral_nonneg (-a) z (by linarith) hcz.le
    calc Real.exp (-∫ t in (2 * Real.sqrt (-a))..z, Real.sqrt (t ^ 2 / 4 - -a)) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  · exact le_refl _

/-- The barrier weight: `|int_0^z sqrt(t^2/4 + a)| <= 2 sqrt(1 + aplus)` for `|z| <= 2`, `0 <= a <= aplus`. -/
lemma ebar_exponent_bound (a aplus z : ℝ) (ha : 0 ≤ a) (haplus : a ≤ aplus) (hz : |z| ≤ 2) :
    |∫ t in (0:ℝ)..z, Real.sqrt (t ^ 2 / 4 + a)| ≤ 2 * Real.sqrt (1 + aplus) := by
  have hC : ∀ t ∈ Set.uIoc (0:ℝ) z, ‖Real.sqrt (t ^ 2 / 4 + a)‖ ≤ Real.sqrt (1 + a) := by
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    have htz : t ^ 2 ≤ 4 := by
      have h1 : |t| ≤ |z| := by
        rcases Set.mem_uIoc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_pos h1]; exact le_trans h2 (le_abs_self z)
        · rw [abs_of_nonpos h2]; linarith [neg_le_abs z]
      have h3 : |t| ^ 2 ≤ |z| ^ 2 := pow_le_pow_left₀ (abs_nonneg t) h1 2
      have h4 : |z| ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (abs_nonneg z) hz 2
      rw [sq_abs] at h3
      linarith
    linarith
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hC
  rw [Real.norm_eq_abs] at hb
  have hab : |z - 0| = |z| := by simp
  rw [hab] at hb
  have hs : Real.sqrt (1 + a) ≤ Real.sqrt (1 + aplus) := Real.sqrt_le_sqrt (by linarith)
  calc |∫ t in (0:ℝ)..z, Real.sqrt (t ^ 2 / 4 + a)| ≤ Real.sqrt (1 + a) * |z| := hb
    _ ≤ Real.sqrt (1 + aplus) * 2 := mul_le_mul hs hz (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (1 + aplus) := by ring

/-- Conjunct (2) of `lem:tha-win`, weight part: for `a <= 0` the well weight is in `[e^{-5/2}, 1]` on `|z| <= rho'`; for `a > 0` the barrier
weight is in `[e^{-2 sqrt(1+a_+)}, e^{2 sqrt(1+a_+)}]` on `|z| <= rho' = 2`. -/
lemma weights_conj (a aplus z : ℝ) (haplus : a ≤ aplus)
    (hz : |z| ≤ rhoWin a + (1 + max (-a) 0) ^ (-(1 : ℝ) / 6)) :
    (a ≤ 0 → Real.exp (-(5 : ℝ) / 2) ≤ Ewell a |z| ∧ Ewell a |z| ≤ 1) ∧
    (0 < a → Real.exp (-(2 * Real.sqrt (1 + aplus))) ≤ Ebar a z ∧
      Ebar a z ≤ Real.exp (2 * Real.sqrt (1 + aplus))) := by
  constructor
  · intro ha
    refine ⟨?_, ewell_le_one a |z| ha⟩
    apply ewell_lower a |z| ha (abs_nonneg z)
    unfold rhoWin at hz
    linarith
  · intro ha
    have hmax : max (-a) 0 = 0 := max_eq_right (by linarith)
    have hz2 : |z| ≤ 2 := by
      unfold rhoWin at hz
      rw [hmax] at hz
      norm_num at hz
      linarith
    have hI := ebar_exponent_bound a aplus z ha.le haplus hz2
    rw [abs_le] at hI
    unfold Ebar
    constructor
    · apply Real.exp_le_exp.mpr
      linarith [hI.2]
    · apply Real.exp_le_exp.mpr
      linarith [hI.1]



/-- Mean value bounds for a function whose derivative lies in `[dm, dp]` on a closed interval `[lo, hi]`. -/
lemma win_mvt (f : ℝ → ℝ) (lo hi dm dp : ℝ) (hdm : 0 < dm)
    (hd : ∀ x ∈ Set.Icc lo hi, dm ≤ deriv f x ∧ deriv f x ≤ dp)
    (x y : ℝ) (hx : x ∈ Set.Icc lo hi) (hy : y ∈ Set.Icc lo hi) (hxy : x ≤ y) :
    dm * (y - x) ≤ f y - f x ∧ f y - f x ≤ dp * (y - x) := by
  rcases hxy.lt_or_eq with hlt | heq
  · have hdiff : ∀ z ∈ Set.Icc lo hi, DifferentiableAt ℝ f z := fun z hz =>
      differentiableAt_of_deriv_ne_zero (by linarith [(hd z hz).1])
    have hcont : ContinuousOn f (Set.Icc x y) := fun z hz =>
      (hdiff z ⟨le_trans hx.1 hz.1, le_trans hz.2 hy.2⟩).continuousAt.continuousWithinAt
    have hdo : DifferentiableOn ℝ f (Set.Ioo x y) := fun z hz =>
      (hdiff z ⟨le_trans hx.1 hz.1.le, le_trans hz.2.le hy.2⟩).differentiableWithinAt
    obtain ⟨c, hc, hceq⟩ := exists_deriv_eq_slope f hlt hcont hdo
    have hcI : c ∈ Set.Icc lo hi := ⟨le_trans hx.1 hc.1.le, le_trans hc.2.le hy.2⟩
    have hsl : f y - f x = deriv f c * (y - x) := by
      rw [hceq]; field_simp [sub_ne_zero.mpr (ne_of_gt hlt)]
    have hyx : 0 ≤ y - x := by linarith
    rw [hsl]
    constructor
    · exact mul_le_mul_of_nonneg_right (hd c hcI).1 hyx
    · exact mul_le_mul_of_nonneg_right (hd c hcI).2 hyx
  · subst heq
    simp

/-- `|k2(a,Z') - k2(a,Z)| <= |Z'^2/4 - Z^2/4|`. -/
lemma win_k2_diff (a Z Z' : ℝ) :
    |k2 a Z' - k2 a Z| ≤ |Z' ^ 2 / 4 - Z ^ 2 / 4| := by
  unfold k2
  have h1 := abs_max_sub_max_le_abs |Z' ^ 2 / 4 + a| |Z ^ 2 / 4 + a| (max |a| 1 ^ ((1 : ℝ) / 3))
  have h2 := abs_abs_sub_abs_le_abs_sub (Z' ^ 2 / 4 + a) (Z ^ 2 / 4 + a)
  have h3 : Z' ^ 2 / 4 + a - (Z ^ 2 / 4 + a) = Z' ^ 2 / 4 - Z ^ 2 / 4 := by ring
  rw [h3] at h2
  exact le_trans h1 h2

lemma win_one_le_c (a : ℝ) : 1 ≤ max |a| 1 ^ ((1 : ℝ) / 3) :=
  Real.one_le_rpow (le_max_right _ _) (by norm_num)

lemma win_k2_ge_one (a z : ℝ) : 1 ≤ k2 a z :=
  le_trans (win_one_le_c a) (le_max_right _ _)

/-- Neighbour comparison: if `|Z'^2 - Z^2| <= 4 D0`, then `Mbal(a,Z') <= D1^{1/4} Mbal(a,Z)` with `D1 = max 2 (2 D0)`. -/
lemma win_mbal_neighbour (a Z Z' D0 : ℝ) (hD0 : 0 ≤ D0) (hZ : |Z' ^ 2 - Z ^ 2| ≤ 4 * D0) :
    Mbal a Z' ≤ (max 2 (2 * D0)) ^ ((1 : ℝ) / 4) * Mbal a Z := by
  set D1 := max 2 (2 * D0) with hD1
  have hD1pos : 0 < D1 := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hD1ge : 2 * D0 ≤ D1 := le_max_right _ _
  have hD12 : 2 ≤ D1 := le_max_left _ _
  have hdiff : |k2 a Z' - k2 a Z| ≤ D0 := by
    refine le_trans (win_k2_diff a Z Z') ?_
    have : Z' ^ 2 / 4 - Z ^ 2 / 4 = (Z' ^ 2 - Z ^ 2) / 4 := by ring
    rw [this, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    linarith [hZ]
  have hk1 := win_k2_ge_one a Z
  have hk1' := win_k2_ge_one a Z'
  have hcase : k2 a Z ≤ D1 * k2 a Z' := by
    by_cases hlarge : 2 * D0 ≤ k2 a Z
    · have h1 : k2 a Z - D0 ≤ k2 a Z' := by
        have := (abs_le.mp hdiff).1; linarith
      have h2 : k2 a Z ≤ 2 * k2 a Z' := by linarith
      nlinarith [mul_le_mul_of_nonneg_right hD12 (by linarith : (0:ℝ) ≤ k2 a Z')]
    · push_neg at hlarge
      have h1 : k2 a Z ≤ 2 * D0 * k2 a Z' := by nlinarith
      nlinarith
  -- Mbal comparison
  have hpos : 0 < k2 a Z / D1 := div_pos (by linarith) hD1pos
  have hle : k2 a Z / D1 ≤ k2 a Z' := by rw [div_le_iff₀ hD1pos]; linarith [hcase]
  unfold Mbal
  have hm : (k2 a Z' ) ^ (-(1 : ℝ) / 4) ≤ (k2 a Z / D1) ^ (-(1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)
  have hdiv : (k2 a Z / D1) ^ (-(1 : ℝ) / 4) = D1 ^ ((1 : ℝ) / 4) * (k2 a Z) ^ (-(1 : ℝ) / 4) := by
    rw [Real.div_rpow (by linarith) hD1pos.le]
    rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring, Real.rpow_neg hD1pos.le, div_inv_eq_mul, mul_comm]
  rw [hdiv] at hm
  exact hm



/-- The threshold for the localisation: `4 Kq Cmu h^2 + 8 sqrt(h K4) + 4 h < cz1` for `h <= h1`, `K4 = (1 + Kq) Cmu`, `Kq >= 0` (`Kq = floor(q/2)`). -/
lemma win_loc_threshold (Kq Cmu cz1 : ℝ) (hKq : 0 ≤ Kq) (hC : 0 ≤ Cmu) (hcz : 0 < cz1) (h : ℝ) (hh0 : 0 < h)
    (hh1 : h ≤ min (min 1 (cz1 / 16)) (min ((cz1 / 24) ^ 2 / ((1 + Kq) * Cmu + 1))
      (cz1 / (12 * (Kq * Cmu + 1))))) :
    4 * Kq * Cmu * h ^ 2 + 8 * Real.sqrt (h * ((1 + Kq) * Cmu)) + 4 * h < cz1 := by
  have hm1 : h ≤ 1 := le_trans hh1 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hm2 : h ≤ cz1 / 16 := le_trans hh1 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hm3 : h ≤ (cz1 / 24) ^ 2 / ((1 + Kq) * Cmu + 1) :=
    le_trans hh1 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hm4 : h ≤ cz1 / (12 * (Kq * Cmu + 1)) := le_trans hh1 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hKC : 0 ≤ Kq * Cmu := mul_nonneg hKq hC
  have t1 : 4 * Kq * Cmu * h ^ 2 ≤ cz1 / 3 := by
    have hh2 : h ^ 2 ≤ h := by nlinarith
    have hden : 0 < 12 * (Kq * Cmu + 1) := by positivity
    have : h * (12 * (Kq * Cmu + 1)) ≤ cz1 := (le_div_iff₀ hden).mp hm4
    have h3 : 4 * Kq * Cmu * h ^ 2 ≤ 4 * (Kq * Cmu) * h := by nlinarith
    nlinarith
  have t2 : 8 * Real.sqrt (h * ((1 + Kq) * Cmu)) ≤ cz1 / 3 := by
    have hK0 : 0 ≤ (1 + Kq) * Cmu := by positivity
    have hden : 0 < (1 + Kq) * Cmu + 1 := by linarith
    have hhK : h * ((1 + Kq) * Cmu) ≤ (cz1 / 24) ^ 2 := by
      have := (le_div_iff₀ hden).mp hm3
      nlinarith
    have hs : Real.sqrt (h * ((1 + Kq) * Cmu)) ≤ cz1 / 24 := by
      rw [show cz1 / 24 = Real.sqrt ((cz1 / 24) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
      exact Real.sqrt_le_sqrt hhK
    linarith
  have t3 : 4 * h ≤ cz1 / 4 := by linarith [hm2]
  linarith

/-- Localisation (conjunct (1), last part) for one row: if `|Z| <= 2 sqrt A + 2 l_A` with `Z = zeta_x / sqrt h`, `h A = max(-h a, 0)`,
`-h a = mu0 + E`, and the far-field bound `4 max(mu0,0) + cz1 <= zeta_x^2` for `eta/4 <= |x|`, then `|x| < eta/4`. -/
lemma win_loc_core (Kq Cmu cz1 η h x μ0 E a zx : ℝ) (hKq : 0 ≤ Kq) (hh0 : 0 < h) (hh1 : h ≤ 1) (hC : 0 ≤ Cmu)
    (hthr : 4 * Kq * Cmu * h ^ 2 + 8 * Real.sqrt (h * ((1 + Kq) * Cmu)) + 4 * h < cz1)
    (ha : h * a = -(μ0 + E)) (hμ : |μ0| ≤ Cmu) (hE : |E| ≤ Kq * Cmu * h ^ 2)
    (hfar : η / 4 ≤ |x| → 4 * max μ0 0 + cz1 ≤ zx ^ 2)
    (hZ : |zx / Real.sqrt h| ≤ 2 * Real.sqrt (max (-a) 0) + 2 * (1 + max (-a) 0) ^ (-(1 : ℝ) / 6)) :
    |x| < η / 4 := by
  by_contra hcon
  push_neg at hcon
  have hfar' := hfar hcon
  have hA0 : 0 ≤ max (-a) 0 := le_max_right _ _
  have hℓ1 : (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hℓ0 : 0 ≤ (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by linarith) _
  have hs := Real.sqrt_pos.mpr hh0
  have hzsq : h * (zx / Real.sqrt h) ^ 2 = zx ^ 2 := by
    rw [div_pow, Real.sq_sqrt hh0.le]; field_simp
  -- h * max(-a,0) = max(mu0 + E, 0)
  have hTA : h * max (-a) 0 = max (μ0 + E) 0 := by
    rw [mul_max_of_nonneg _ _ hh0.le]
    congr 1
    · linarith [ha]
    · simp
  have hM0 : max μ0 0 ≤ Cmu := max_le (le_trans (le_abs_self _) hμ) hC
  have hT1 : h * max (-a) 0 ≤ max μ0 0 + |E| := by
    rw [hTA]
    apply max_le
    · linarith [le_max_left μ0 0, le_abs_self E]
    · linarith [le_max_right μ0 0, abs_nonneg E]
  have hT2 : h * max (-a) 0 ≤ (1 + Kq) * Cmu := by
    have hq : (0:ℝ) ≤ Kq * Cmu := mul_nonneg hKq hC
    have hh2 : h ^ 2 ≤ 1 := by nlinarith
    have : Kq * Cmu * h ^ 2 ≤ Kq * Cmu := by nlinarith
    nlinarith
  have hsqA : h * Real.sqrt (max (-a) 0) ≤ Real.sqrt (h * ((1 + Kq) * Cmu)) := by
    have hsq2 : (h * Real.sqrt (max (-a) 0)) ^ 2 ≤ h * ((1 + Kq) * Cmu) := by
      rw [mul_pow, Real.sq_sqrt hA0]
      nlinarith
    calc h * Real.sqrt (max (-a) 0) = Real.sqrt ((h * Real.sqrt (max (-a) 0)) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hsq2
  have hsA := Real.sq_sqrt hA0
  have hbig : h * (2 * Real.sqrt (max (-a) 0) + 2 * (1 + max (-a) 0) ^ (-(1 : ℝ) / 6)) ^ 2 ≤
      4 * (h * max (-a) 0) + 8 * Real.sqrt (h * ((1 + Kq) * Cmu)) + 4 * h := by
    have e2 : h * (2 * Real.sqrt (max (-a) 0) + 2 * (1 + max (-a) 0) ^ (-(1 : ℝ) / 6)) ^ 2 =
        4 * (h * max (-a) 0) + 8 * (h * Real.sqrt (max (-a) 0)) * (1 + max (-a) 0) ^ (-(1 : ℝ) / 6)
          + 4 * h * ((1 + max (-a) 0) ^ (-(1 : ℝ) / 6)) ^ 2 := by
      linear_combination (4 * h) * hsA
    rw [e2]
    have hp0 : 0 ≤ h * Real.sqrt (max (-a) 0) := by positivity
    have h8 : 8 * (h * Real.sqrt (max (-a) 0)) * (1 + max (-a) 0) ^ (-(1 : ℝ) / 6)
        ≤ 8 * Real.sqrt (h * ((1 + Kq) * Cmu)) := by
      have := mul_le_mul_of_nonneg_left hℓ1 hp0
      nlinarith
    have h4 : 4 * h * ((1 + max (-a) 0) ^ (-(1 : ℝ) / 6)) ^ 2 ≤ 4 * h := by
      have : ((1 + max (-a) 0) ^ (-(1 : ℝ) / 6)) ^ 2 ≤ 1 := by nlinarith
      nlinarith
    linarith
  have hZ2 : (zx / Real.sqrt h) ^ 2 ≤ (2 * Real.sqrt (max (-a) 0) + 2 * (1 + max (-a) 0) ^ (-(1 : ℝ) / 6)) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hZ 2
    rwa [sq_abs] at this
  have hsq : 4 * max μ0 0 + cz1 ≤ h * (2 * Real.sqrt (max (-a) 0) + 2 * (1 + max (-a) 0) ^ (-(1 : ℝ) / 6)) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hZ2 hh0.le
    linarith [hzsq, hfar', this]
  linarith


/-! ### Chart constants and the row lemma of conjunct (1) -/

section Chart

variable {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
  {Lm : ℝ → ℝ}

/-- The bound `B` on `|zeta(x)|` for `|x| <= 2 eta`: `B = cZ delta_0 + d_+ 2 eta`. -/
def winB (CL : SoftEdgeChart Fz P m q U V Lm) : ℝ := CL.cZ * CL.δ0 + CL.dp * (2 * CL.η)

/-- The neighbour constant `Cnb = (max 2 (2 D0))^{1/4}` with `D0 = d_+ B / 2`. -/
def winCnb (CL : SoftEdgeChart Fz P m q U V Lm) : ℝ := (max 2 (2 * (CL.dp * winB CL / 2))) ^ ((1 : ℝ) / 4)

/-- `K_q = floor(q/2)` as a real number (the number of corrector shifts `r = 1..q/2`). -/
def winKq (q : ℕ) : ℝ := ((q / 2 : ℕ) : ℝ)

/-- The constant `CΛ` of the lattice bound `h k_2(Z_n) <= CΛ^2`. -/
def winCLam (CL : SoftEdgeChart Fz P m q U V Lm) : ℝ :=
  (winB CL) ^ 2 / 4 + 2 * ((winKq q + 1) * CL.Cmu) + 1

/-- The localisation threshold `h1` of the row lemma. -/
def winH1 (CL : SoftEdgeChart Fz P m q U V Lm) : ℝ :=
  min (min 1 (CL.cz1 / 16)) (min ((CL.cz1 / 24) ^ 2 / ((1 + winKq q) * CL.Cmu + 1))
    (CL.cz1 / (12 * (winKq q * CL.Cmu + 1))))

lemma winB_nonneg (CL : SoftEdgeChart Fz P m q U V Lm) : 0 ≤ winB CL := by
  obtain ⟨_, h2, _, _, _, _, _, h8⟩ := CL.consts_pos
  unfold winB
  have := CL.consts_pos2
  have h3 := CL.consts_pos
  have hdp : 0 ≤ CL.dp := le_trans h3.2.2.1.le h3.2.2.2.1
  nlinarith [mul_nonneg h8.le h2.le, mul_nonneg hdp h2.le]

/-- Lipschitz bound along the chart: `|f y - f x| <= dp |y - x|` for `x, y` in `[lo, hi]`. -/
lemma win_lip (f : ℝ → ℝ) (lo hi dm dp : ℝ) (hdm : 0 < dm) (hdp : dm ≤ dp)
    (hd : ∀ x ∈ Set.Icc lo hi, dm ≤ deriv f x ∧ deriv f x ≤ dp)
    (x y : ℝ) (hx : x ∈ Set.Icc lo hi) (hy : y ∈ Set.Icc lo hi) :
    |f y - f x| ≤ dp * |y - x| := by
  rcases le_total x y with hxy | hxy
  · obtain ⟨h1, h2⟩ := win_mvt f lo hi dm dp hdm hd x y hx hy hxy
    have hyx : 0 ≤ y - x := by linarith
    rw [abs_of_nonneg hyx, abs_le]
    constructor
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ dp) hyx]
    · exact h2
  · obtain ⟨h1, h2⟩ := win_mvt f lo hi dm dp hdm hd y x hy hx hxy
    have hxy' : 0 ≤ x - y := by linarith
    rw [abs_of_nonpos (by linarith : y - x ≤ 0), abs_le]
    constructor
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ dp) hxy']
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ dm + dp) hxy']

/-- `c = max(|a|,1)^{1/3} <= max(|a|,1)`. -/
lemma win_cube_le (a : ℝ) : max |a| 1 ^ ((1 : ℝ) / 3) ≤ max |a| 1 := by
  have h1 : (1 : ℝ) ≤ max |a| 1 := le_max_right _ _
  calc max |a| 1 ^ ((1 : ℝ) / 3) ≤ max |a| 1 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    _ = max |a| 1 := Real.rpow_one _

/-- The `k_2` bound in terms of the parabolic-cylinder data: `k2(a,Z) <= |Z^2/4 + a| + max(|a|,1)`. -/
lemma win_k2_le (a z : ℝ) : k2 a z ≤ |z ^ 2 / 4 + a| + max |a| 1 := by
  unfold k2
  apply max_le
  · have h0 : 0 ≤ max |a| 1 := le_trans zero_le_one (le_max_right _ _)
    linarith [abs_nonneg (z ^ 2 / 4 + a)]
  · have := win_cube_le a
    linarith [abs_nonneg (z ^ 2 / 4 + a)]

/-- The zeta function is Lipschitz on the chart and bounded there. -/
lemma win_zeta_bound (CL : SoftEdgeChart Fz P m q U V Lm) (p : Par × ℝ) (hp : p ∈ P) (α : ℝ) (hα : |α| ≤ CL.δ0)
    (x : ℝ) (hx : |x| ≤ 2 * CL.η) : |CL.zeta p α x| ≤ winB CL := by
  obtain ⟨_, h2, h3, h4, _, _, _, _⟩ := CL.consts_pos
  have hd : ∀ y ∈ Set.Icc (-(2 * CL.η)) (2 * CL.η),
      CL.dm ≤ deriv (CL.zeta p α) y ∧ deriv (CL.zeta p α) y ≤ CL.dp :=
    fun y hy => CL.zeta_deriv p hp α hα y (abs_le.mpr ⟨hy.1, hy.2⟩)
  have h0 : (0 : ℝ) ∈ Set.Icc (-(2 * CL.η)) (2 * CL.η) := ⟨by linarith, by linarith⟩
  have hxI : x ∈ Set.Icc (-(2 * CL.η)) (2 * CL.η) := abs_le.mp hx
  have hl := win_lip (CL.zeta p α) (-(2 * CL.η)) (2 * CL.η) CL.dm CL.dp h3 h4 hd 0 x h0 hxI
  have hz0 := CL.zeta_alpha p hp α hα
  have hz0' : |CL.zeta p α 0| ≤ CL.cZ * CL.δ0 := le_trans hz0
    (mul_le_mul_of_nonneg_left hα (le_of_lt (CL.consts_pos.2.2.2.2.2.2.2)))
  have hxabs : |x - 0| ≤ 2 * CL.η := by simpa using hx
  have hdp0 : 0 ≤ CL.dp := le_trans h3.le h4
  have hbd : CL.dp * |x - 0| ≤ CL.dp * (2 * CL.η) := mul_le_mul_of_nonneg_left hxabs hdp0
  have htri : |CL.zeta p α x| ≤ |CL.zeta p α 0| + |CL.zeta p α x - CL.zeta p α 0| := by
    have := abs_sub_le (CL.zeta p α x) (CL.zeta p α 0) 0
    simpa [abs_sub_comm] using (abs_add_le (CL.zeta p α x - CL.zeta p α 0) (CL.zeta p α 0))
      |>.trans (le_of_eq (by ring_nf))
  unfold winB
  linarith

/-- Division by `sqrt h`: `dm h <= d <= dp h` gives `dm sqrt h <= d/sqrt h <= dp sqrt h`. -/
lemma win_div_bounds (d h dm dp : ℝ) (hh : 0 < h) (hl : dm * h ≤ d) (hu : d ≤ dp * h) :
    dm * Real.sqrt h ≤ d / Real.sqrt h ∧ d / Real.sqrt h ≤ dp * Real.sqrt h := by
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hss : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hh.le
  constructor
  · rw [le_div_iff₀ hs, mul_assoc, hss]; linarith
  · rw [div_le_iff₀ hs, mul_assoc, hss]; linarith

/-- The squared-difference bound for neighbouring lattice coordinates `Z = s/sqrt h`, `Z' = t/sqrt h`. -/
lemma win_sq_diff (s t h B dp : ℝ) (hh : 0 < h) (hs : |s| ≤ B) (ht : |t| ≤ B) (hd : |t - s| ≤ dp * h)
    (hdp : 0 ≤ dp) (hB : 0 ≤ B) :
    |(t / Real.sqrt h) ^ 2 - (s / Real.sqrt h) ^ 2| ≤ 4 * (dp * B / 2) := by
  have hsq : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh.le
  have e : (t / Real.sqrt h) ^ 2 - (s / Real.sqrt h) ^ 2 = (t - s) * (t + s) / h := by
    rw [div_pow, div_pow, hsq]; field_simp; ring
  rw [e, abs_div, abs_of_pos hh, div_le_iff₀ hh, abs_mul]
  have h1 : |t + s| ≤ 2 * B := by
    have := abs_add_le t s; linarith
  have h2 : |t - s| * |t + s| ≤ (dp * h) * (2 * B) :=
    mul_le_mul hd h1 (abs_nonneg _) (by positivity)
  nlinarith

/-- The `a`-parameter identity and bounds: `h a = -(mu_0 + E)`, `|E| <= Kq Cmu h^2`, `|mu_0| <= Cmu`. -/
lemma win_aOf_facts (CL : SoftEdgeChart Fz P m q U V Lm) (p : Par × ℝ) (hp : p ∈ P) (X : ℝ) (hX : |X - Fz.bandHi p| ≤ CL.δ0)
    (N : ℕ) (hh0 : 0 < Fz.step N) (hh1 : Fz.step N ≤ 1) :
    ∃ E : ℝ, Fz.step N * CL.aOf p X N = -(CL.muS 0 p (Fz.bandHi p - X) + E) ∧
      |E| ≤ winKq q * CL.Cmu * Fz.step N ^ 2 ∧ |CL.muS 0 p (Fz.bandHi p - X)| ≤ CL.Cmu := by
  obtain ⟨hCmu, _⟩ := CL.consts_pos2
  have hα : |Fz.bandHi p - X| ≤ CL.δ0 := by rw [abs_sub_comm]; exact hX
  refine ⟨∑ r ∈ Finset.Icc 1 (q / 2), Fz.step N ^ (2 * r) * CL.muS r p (Fz.bandHi p - X), ?_, ?_, ?_⟩
  · unfold SoftEdgeChart.aOf aPC
    field_simp
  · unfold winKq
    have hsum : |∑ r ∈ Finset.Icc 1 (q / 2), Fz.step N ^ (2 * r) * CL.muS r p (Fz.bandHi p - X)|
        ≤ ∑ r ∈ Finset.Icc 1 (q / 2), Fz.step N ^ 2 * CL.Cmu := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun r hr => ?_)
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hrq : r ≤ q / 2 := (Finset.mem_Icc.mp hr).2
      rw [abs_mul, abs_of_pos (pow_pos hh0 _)]
      have hp2 : Fz.step N ^ (2 * r) ≤ Fz.step N ^ 2 :=
        pow_le_pow_of_le_one hh0.le hh1 (by omega)
      have hm : |CL.muS r p (Fz.bandHi p - X)| ≤ CL.Cmu :=
        CL.muS_bd r (Finset.mem_Icc.mpr ⟨by omega, hrq⟩) p hp _ hα
      exact mul_le_mul hp2 hm (abs_nonneg _) (pow_nonneg hh0.le 2)
    have hcard : (∑ r ∈ Finset.Icc 1 (q / 2), Fz.step N ^ 2 * CL.Cmu) = ((q / 2 : ℕ) : ℝ) * (Fz.step N ^ 2 * CL.Cmu) := by
      simp [Finset.sum_const, Nat.card_Icc]
    rw [hcard] at hsum
    calc _ ≤ _ := hsum
      _ = ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N ^ 2 := by ring
  · have hm : |CL.muS 0 p (Fz.bandHi p - X)| ≤ CL.Cmu :=
      CL.muS_bd 0 (Finset.mem_Icc.mpr ⟨le_refl _, Nat.zero_le _⟩) p hp _ hα
    exact hm

/-- Conjunct (1) of `lem:tha-win`, for one row `n` (with `|u_n - u_c| <= 2 eta`): the lattice spacing and neighbour bounds when the
neighbour is on the chart, the bound `h k_2(Z_n) <= CΛ^2`, and the localisation `|Z_n| <= rho' => |u_n - u_c| < eta/4`. -/
lemma win_row (CL : SoftEdgeChart Fz P m q U V Lm) (p : Par × ℝ) (hp : p ∈ P) (X : ℝ) (hX : |X - Fz.bandHi p| ≤ CL.δ0)
    (N : ℕ) (hh0 : 0 < Fz.step N) (hh1 : Fz.step N ≤ winH1 CL) (n : ℤ)
    (hn : |uNode (Fz.step N) n - CL.uc p| ≤ 2 * CL.η) :
    (|uNode (Fz.step N) (n + 1) - CL.uc p| ≤ 2 * CL.η →
      CL.dm * Real.sqrt (Fz.step N) ≤ CL.Zof p X N (n + 1) - CL.Zof p X N n ∧
      CL.Zof p X N (n + 1) - CL.Zof p X N n ≤ CL.dp * Real.sqrt (Fz.step N) ∧
      Mbal (CL.aOf p X N) (CL.Zof p X N (n + 1)) ≤ winCnb CL * Mbal (CL.aOf p X N) (CL.Zof p X N n)) ∧
    Fz.step N * k2 (CL.aOf p X N) (CL.Zof p X N n) ≤ winCLam CL ^ 2 ∧
    (|uNode (Fz.step N) (n - 1) - CL.uc p| ≤ 2 * CL.η →
      Mbal (CL.aOf p X N) (CL.Zof p X N (n - 1)) ≤ winCnb CL * Mbal (CL.aOf p X N) (CL.Zof p X N n)) ∧
    (|CL.Zof p X N n| ≤ rhoWin (CL.aOf p X N) + (1 + max (-CL.aOf p X N) 0) ^ (-(1 : ℝ) / 6) →
      |uNode (Fz.step N) n - CL.uc p| < CL.η / 4) := by
  obtain ⟨hδ0, hη, hdm, hdmp, -, -, -, hcZ⟩ := CL.consts_pos
  obtain ⟨hCmu, hcz1⟩ := CL.consts_pos2
  have hdp0 : 0 ≤ CL.dp := le_trans hdm.le hdmp
  have hB0 : 0 ≤ winB CL := winB_nonneg CL
  have hα : |Fz.bandHi p - X| ≤ CL.δ0 := by rw [abs_sub_comm]; exact hX
  have hwh : winH1 CL ≤ 1 := by
    unfold winH1
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hKq : 0 ≤ winKq q := by unfold winKq; positivity
  have hh1' : Fz.step N ≤ 1 := le_trans hh1 hwh
  have hthr := win_loc_threshold (winKq q) CL.Cmu CL.cz1 hKq hCmu hcz1 (Fz.step N) hh0 hh1
  set h := Fz.step N with hhdef
  have hsqh : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh0
  have hZdef : ∀ k : ℤ, CL.Zof p X N k = CL.zeta p (Fz.bandHi p - X) (uNode h k - CL.uc p) / Real.sqrt h :=
    fun k => rfl
  have hdI : ∀ y ∈ Set.Icc (-(2 * CL.η)) (2 * CL.η),
      CL.dm ≤ deriv (CL.zeta p (Fz.bandHi p - X)) y ∧ deriv (CL.zeta p (Fz.bandHi p - X)) y ≤ CL.dp :=
    fun y hy => CL.zeta_deriv p hp _ hα y (abs_le.mpr ⟨hy.1, hy.2⟩)
  have hstep : ∀ k : ℤ, uNode h (k + 1) - CL.uc p - (uNode h k - CL.uc p) = h := by
    intro k; unfold uNode; push_cast; ring
  have hstepb : ∀ k : ℤ, uNode h k - CL.uc p - (uNode h (k - 1) - CL.uc p) = h := by
    intro k; unfold uNode; push_cast; ring
  have hBn : ∀ k : ℤ, |uNode h k - CL.uc p| ≤ 2 * CL.η → |CL.zeta p (Fz.bandHi p - X) (uNode h k - CL.uc p)| ≤ winB CL :=
    fun k hk => win_zeta_bound CL p hp _ hα _ hk
  -- Lipschitz/spacing for a pair of chart points at distance h
  have hpair : ∀ k : ℤ, |uNode h k - CL.uc p| ≤ 2 * CL.η → |uNode h (k + 1) - CL.uc p| ≤ 2 * CL.η →
      CL.dm * h ≤ CL.zeta p (Fz.bandHi p - X) (uNode h (k + 1) - CL.uc p) - CL.zeta p (Fz.bandHi p - X) (uNode h k - CL.uc p) ∧
      CL.zeta p (Fz.bandHi p - X) (uNode h (k + 1) - CL.uc p) - CL.zeta p (Fz.bandHi p - X) (uNode h k - CL.uc p) ≤ CL.dp * h := by
    intro k hk hk1
    have hxk := abs_le.mp hk
    have hxk1 := abs_le.mp hk1
    have hle : uNode h k - CL.uc p ≤ uNode h (k + 1) - CL.uc p := by have := hstep k; linarith
    obtain ⟨h1, h2⟩ := win_mvt (CL.zeta p (Fz.bandHi p - X)) (-(2 * CL.η)) (2 * CL.η) CL.dm CL.dp hdm hdI _ _ hxk hxk1 hle
    have hd := hstep k
    rw [hd] at h1 h2
    exact ⟨h1, h2⟩
  have hsqdiff : ∀ k : ℤ, |uNode h k - CL.uc p| ≤ 2 * CL.η → |uNode h (k + 1) - CL.uc p| ≤ 2 * CL.η →
      |CL.Zof p X N (k + 1) ^ 2 - CL.Zof p X N k ^ 2| ≤ 4 * (CL.dp * winB CL / 2) := by
    intro k hk hk1
    obtain ⟨h1, h2⟩ := hpair k hk hk1
    have hd : |CL.zeta p (Fz.bandHi p - X) (uNode h (k + 1) - CL.uc p) - CL.zeta p (Fz.bandHi p - X) (uNode h k - CL.uc p)| ≤ CL.dp * h := by
      rw [abs_le]; constructor <;> nlinarith
    rw [hZdef, hZdef]
    exact win_sq_diff _ _ h (winB CL) CL.dp hh0 (hBn k hk) (hBn (k + 1) hk1) hd hdp0 hB0
  have hD0 : 0 ≤ CL.dp * winB CL / 2 := div_nonneg (mul_nonneg hdp0 hB0) (by norm_num)
  have hZstep : ∀ k : ℤ, |uNode h k - CL.uc p| ≤ 2 * CL.η → |uNode h (k + 1) - CL.uc p| ≤ 2 * CL.η →
      CL.dm * Real.sqrt h ≤ CL.Zof p X N (k + 1) - CL.Zof p X N k ∧
      CL.Zof p X N (k + 1) - CL.Zof p X N k ≤ CL.dp * Real.sqrt h := by
    intro k hk hk1
    obtain ⟨h1, h2⟩ := hpair k hk hk1
    simp only [hZdef]
    rw [← sub_div]
    exact win_div_bounds _ h CL.dm CL.dp hh0 h1 h2
  have hMnb : ∀ k : ℤ, |uNode h k - CL.uc p| ≤ 2 * CL.η → |uNode h (k + 1) - CL.uc p| ≤ 2 * CL.η →
      Mbal (CL.aOf p X N) (CL.Zof p X N (k + 1)) ≤ winCnb CL * Mbal (CL.aOf p X N) (CL.Zof p X N k) := by
    intro k hk hk1
    unfold winCnb
    exact win_mbal_neighbour _ _ _ _ hD0 (hsqdiff k hk hk1)
  -- the lower neighbour: pair (zeta at u_n, zeta at u_{n-1})
  have hprem1 : |uNode h (n - 1) - CL.uc p| ≤ 2 * CL.η → |CL.Zof p X N (n - 1) ^ 2 - CL.Zof p X N n ^ 2| ≤ 4 * (CL.dp * winB CL / 2) := by
    intro hm1
    have hpm := hpair (n - 1) hm1 (by simpa [sub_add_cancel] using hn)
    simp only [sub_add_cancel] at hpm
    have hd : |CL.zeta p (Fz.bandHi p - X) (uNode h (n - 1) - CL.uc p) - CL.zeta p (Fz.bandHi p - X) (uNode h n - CL.uc p)| ≤ CL.dp * h := by
      rw [abs_le]; constructor <;> nlinarith [hpm.1, hpm.2]
    rw [hZdef, hZdef]
    exact win_sq_diff (CL.zeta p (Fz.bandHi p - X) (uNode h n - CL.uc p))
      (CL.zeta p (Fz.bandHi p - X) (uNode h (n - 1) - CL.uc p)) h (winB CL) CL.dp hh0 (hBn n hn) (hBn (n - 1) hm1) hd hdp0 hB0
  have hMnbm : |uNode h (n - 1) - CL.uc p| ≤ 2 * CL.η →
      Mbal (CL.aOf p X N) (CL.Zof p X N (n - 1)) ≤ winCnb CL * Mbal (CL.aOf p X N) (CL.Zof p X N n) := by
    intro hm1
    unfold winCnb
    exact win_mbal_neighbour _ _ _ _ hD0 (hprem1 hm1)
  -- the k_2 bound
  obtain ⟨E, hEa, hEb, hEc⟩ := win_aOf_facts CL p hp X hX N hh0 hh1'
  rw [← hhdef] at hEa hEb
  have hKC : 0 ≤ winKq q * CL.Cmu := mul_nonneg hKq hCmu
  have hh2 : h ^ 2 ≤ 1 := by nlinarith
  have hE2 : winKq q * CL.Cmu * h ^ 2 ≤ winKq q * CL.Cmu := by
    calc winKq q * CL.Cmu * h ^ 2 ≤ winKq q * CL.Cmu * 1 := mul_le_mul_of_nonneg_left hh2 hKC
      _ = winKq q * CL.Cmu := mul_one _
  have hKu : (winKq q + 1) * CL.Cmu = CL.Cmu + winKq q * CL.Cmu := by ring
  have hha : |h * CL.aOf p X N| ≤ (winKq q + 1) * CL.Cmu := by
    rw [hEa, abs_neg]
    have h1 := abs_add_le (CL.muS 0 p (Fz.bandHi p - X)) E
    linarith [hEc, hE2, hKu]
  have hk2 : h * k2 (CL.aOf p X N) (CL.Zof p X N n) ≤ winCLam CL ^ 2 := by
    have hZ2 : h * CL.Zof p X N n ^ 2 = CL.zeta p (Fz.bandHi p - X) (uNode h n - CL.uc p) ^ 2 := by
      rw [hZdef, div_pow, Real.sq_sqrt hh0.le]; field_simp
    have hk := win_k2_le (CL.aOf p X N) (CL.Zof p X N n)
    have hw : h * |CL.Zof p X N n ^ 2 / 4 + CL.aOf p X N| =
        |CL.zeta p (Fz.bandHi p - X) (uNode h n - CL.uc p) ^ 2 / 4 + h * CL.aOf p X N| := by
      have habs : h * |CL.Zof p X N n ^ 2 / 4 + CL.aOf p X N| = |h * (CL.Zof p X N n ^ 2 / 4 + CL.aOf p X N)| := by
        rw [abs_mul, abs_of_pos hh0]
      rw [habs]
      congr 1
      linear_combination hZ2 / 4
    have hsq : CL.zeta p (Fz.bandHi p - X) (uNode h n - CL.uc p) ^ 2 ≤ winB CL ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) (hBn n hn) 2
      rwa [sq_abs] at this
    have habs1 : |CL.zeta p (Fz.bandHi p - X) (uNode h n - CL.uc p) ^ 2 / 4 + h * CL.aOf p X N| ≤
        winB CL ^ 2 / 4 + (winKq q + 1) * CL.Cmu := by
      have := abs_add_le (CL.zeta p (Fz.bandHi p - X) (uNode h n - CL.uc p) ^ 2 / 4) (h * CL.aOf p X N)
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ CL.zeta p (Fz.bandHi p - X) (uNode h n - CL.uc p) ^ 2 / 4)] at this
      have h4 : CL.zeta p (Fz.bandHi p - X) (uNode h n - CL.uc p) ^ 2 / 4 ≤ winB CL ^ 2 / 4 := by linarith
      linarith [hha]
    have hmax : h * max |CL.aOf p X N| 1 ≤ (winKq q + 1) * CL.Cmu + 1 := by
      rw [mul_max_of_nonneg _ _ hh0.le]
      apply max_le
      · have habs : h * |CL.aOf p X N| = |h * CL.aOf p X N| := by rw [abs_mul, abs_of_pos hh0]
        rw [habs]
        linarith [hha]
      · have hK1 : 0 ≤ (winKq q + 1) * CL.Cmu := by positivity
        rw [mul_one]
        linarith [hh1']
    have hkk : h * k2 (CL.aOf p X N) (CL.Zof p X N n) ≤
        h * (|CL.Zof p X N n ^ 2 / 4 + CL.aOf p X N| + max |CL.aOf p X N| 1) :=
      mul_le_mul_of_nonneg_left hk hh0.le
    have hfin : h * (|CL.Zof p X N n ^ 2 / 4 + CL.aOf p X N| + max |CL.aOf p X N| 1) ≤ winCLam CL := by
      rw [mul_add, hw]
      unfold winCLam
      linarith [habs1, hmax]
    have hK1 : 0 ≤ (winKq q + 1) * CL.Cmu := by positivity
    have hge1 : 1 ≤ winCLam CL := by
      unfold winCLam
      have := sq_nonneg (winB CL)
      linarith
    have hsqge : winCLam CL ≤ winCLam CL ^ 2 := by nlinarith [hge1]
    linarith [hkk, hfin, hsqge]
  -- localisation
  have hloc : |CL.Zof p X N n| ≤ rhoWin (CL.aOf p X N) + (1 + max (-CL.aOf p X N) 0) ^ (-(1 : ℝ) / 6) →
      |uNode h n - CL.uc p| < CL.η / 4 := by
    intro hZ
    have hZ' : |CL.zeta p (Fz.bandHi p - X) (uNode h n - CL.uc p) / Real.sqrt h| ≤
        2 * Real.sqrt (max (-CL.aOf p X N) 0) + 2 * (1 + max (-CL.aOf p X N) 0) ^ (-(1 : ℝ) / 6) := by
      have h' := hZ
      unfold rhoWin at h'
      rw [hZdef] at h'
      linarith
    exact win_loc_core (winKq q) CL.Cmu CL.cz1 CL.η h (uNode h n - CL.uc p) (CL.muS 0 p (Fz.bandHi p - X)) E
      (CL.aOf p X N) (CL.zeta p (Fz.bandHi p - X) (uNode h n - CL.uc p)) hKq hh0 hh1' hCmu hthr hEa
      (CL.muS_bd 0 (Finset.mem_Icc.mpr ⟨le_refl _, Nat.zero_le _⟩) p hp _ hα) hEb
      (fun hc => CL.zeta_far p hp _ hα _ hn hc) hZ'
  exact ⟨fun hn1 => ⟨hZstep n hn hn1 |>.1, hZstep n hn hn1 |>.2, hMnb n hn hn1⟩, hk2, hMnbm, hloc⟩

/-- **Conjunct (1) of `lem:tha-win`** (the lattice facts, with the F-W1 guards), for all rows `n` of `rowsOf N`, with the constants
`Cnb = winCnb CL`, `CΛ = winCLam CL` and the row threshold `Fz.step N <= winH1 CL`. -/
theorem win_conj1 (CL : SoftEdgeChart Fz P m q U V Lm) (p : Par × ℝ) (hp : p ∈ P) (X : ℝ)
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) (N : ℕ) (hh1 : Fz.step N ≤ winH1 CL) :
    ∀ n ∈ rowsOf N, |uNode (Fz.step N) n - CL.uc p| ≤ 2 * CL.η →
      (|uNode (Fz.step N) (n + 1) - CL.uc p| ≤ 2 * CL.η →
        CL.dm * Real.sqrt (Fz.step N) ≤ CL.Zof p X N (n + 1) - CL.Zof p X N n ∧
        CL.Zof p X N (n + 1) - CL.Zof p X N n ≤ CL.dp * Real.sqrt (Fz.step N) ∧
        Mbal (CL.aOf p X N) (CL.Zof p X N (n + 1)) ≤ winCnb CL * Mbal (CL.aOf p X N) (CL.Zof p X N n)) ∧
      Fz.step N * k2 (CL.aOf p X N) (CL.Zof p X N n) ≤ winCLam CL ^ 2 ∧
      (|uNode (Fz.step N) (n - 1) - CL.uc p| ≤ 2 * CL.η →
        Mbal (CL.aOf p X N) (CL.Zof p X N (n - 1)) ≤ winCnb CL * Mbal (CL.aOf p X N) (CL.Zof p X N n)) ∧
      (|CL.Zof p X N n| ≤ rhoWin (CL.aOf p X N) + (1 + max (-CL.aOf p X N) 0) ^ (-(1 : ℝ) / 6) →
        |uNode (Fz.step N) n - CL.uc p| < CL.η / 4) := by
  intro n _ hn
  exact win_row CL p hp X hX N (FormalResearch.JB.stepSize_pos Fz.L_pos N) hh1 n hn

end Chart


/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.win_conj1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.win_conj1

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.weights_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.weights_conj

/-! ### Conjunct (3): the envelopes of the window, from `ParabolicCylinderFacts` -/

section Envelopes

variable {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

lemma sqrt_split (x y k T : ℝ) (hk : 0 < k) (h : Real.sqrt (x ^ 2 + y ^ 2 / k) ≤ T) :
    |x| ≤ T ∧ |y| ≤ T * Real.sqrt k := by
  have hT : 0 ≤ T := le_trans (Real.sqrt_nonneg _) h
  have hsq : Real.sqrt (x ^ 2 + y ^ 2 / k) ^ 2 = x ^ 2 + y ^ 2 / k :=
    Real.sq_sqrt (by positivity)
  have hle : x ^ 2 + y ^ 2 / k ≤ T ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    linarith
  have hdiv : 0 ≤ y ^ 2 / k := div_nonneg (sq_nonneg y) hk.le
  have hx2 : x ^ 2 ≤ T ^ 2 := by linarith
  have hy2 : y ^ 2 / k ≤ T ^ 2 := by linarith [sq_nonneg x]
  have hy3 : y ^ 2 ≤ T ^ 2 * k := (div_le_iff₀ hk).mp hy2
  constructor
  · exact abs_le.mpr (abs_le_of_sq_le_sq' hx2 hT)
  · have hyT : y ^ 2 ≤ (T * Real.sqrt k) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hk.le]; exact hy3
    exact abs_le.mpr (abs_le_of_sq_le_sq' hyT (mul_nonneg hT (Real.sqrt_nonneg _)))

lemma kappa_sq_gamma (a : ℝ) (ha : a ≤ 0) :
    kappaBal a ≠ 0 ∧ kappaBal a ^ 2 * Real.Gamma (1 / 2 - a) = 1 := by
  have hG : 0 < Real.Gamma (1 / 2 - a) := Real.Gamma_pos_of_pos (by linarith)
  unfold kappaBal
  rw [if_pos ha]
  have hpow : (Real.Gamma (1 / 2 - a) ^ (-(1 : ℝ) / 2)) ^ 2 = (Real.Gamma (1 / 2 - a))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hG.le]
    norm_num
    exact Real.rpow_neg_one _
  constructor
  · apply ne_of_gt
    exact Real.rpow_pos_of_pos hG _
  · rw [hpow, inv_mul_cancel₀ hG.ne']

lemma inv_eq_mul_of (κ Γ : ℝ) (hκΓ : κ ^ 2 * Γ = 1) : κ⁻¹ = κ * Γ :=
  inv_eq_of_mul_eq_one_right (by linear_combination hκΓ)

lemma alg_gen (κ Γ r α γ u v : ℝ) (hκ : κ ≠ 0) (hκΓ : κ ^ 2 * Γ = 1) (hr : r ≠ 0) :
    κ * (α * u + γ * Γ * v) = α * (κ * u) + γ / r * (r * κ⁻¹ * v) := by
  have h1 : γ / r * (r * κ⁻¹ * v) = γ * κ⁻¹ * v := by field_simp
  rw [h1, inv_eq_mul_of κ Γ hκΓ]
  ring

lemma alg_two (κ Γ r α β u v : ℝ) (hκ : κ ≠ 0) (hΓ : Γ ≠ 0) (hκΓ : κ ^ 2 * Γ = 1) :
    r * κ⁻¹ * (α / Γ * u + β * v) = α * r * (κ * u) + β * (r * κ⁻¹ * v) := by
  rw [inv_eq_mul_of κ Γ hκΓ]
  field_simp

lemma pc_diffU (pc : ParabolicCylinderFacts U V cPC CPC) (a : ℝ) : Differentiable ℝ (U a) := by
  have h := pc.smooth_U.differentiable (by simp)
  have hpair : Differentiable ℝ (fun z : ℝ => ((a, z) : ℝ × ℝ)) :=
    (differentiable_const a).prodMk differentiable_id
  exact h.comp hpair

lemma pc_diffV (pc : ParabolicCylinderFacts U V cPC CPC) (a : ℝ) : Differentiable ℝ (V a) := by
  have h := pc.smooth_V.differentiable (by simp)
  have hpair : Differentiable ℝ (fun z : ℝ => ((a, z) : ℝ × ℝ)) :=
    (differentiable_const a).prodMk differentiable_id
  exact h.comp hpair

/-- The derivative of the connection formula `U(a,-z) = -sin U(a,z) + cos Gamma V(a,z)`, at `-w`. -/
lemma deriv_reflect_U (pc : ParabolicCylinderFacts U V cPC CPC) (a : ℝ) (ha : a ≤ 0) (w : ℝ) :
    deriv (U a) (-w) = Real.sin (Real.pi * a) * deriv (U a) w +
      (-Real.cos (Real.pi * a)) * Real.Gamma (1 / 2 - a) * deriv (V a) w := by
  have hfun : (fun x => U a (-x)) = fun x => -Real.sin (Real.pi * a) * U a x +
      Real.cos (Real.pi * a) * Real.Gamma (1 / 2 - a) * V a x :=
    funext fun x => pc.reflect a ha x
  have h1 : deriv (fun x => U a (-x)) w = deriv (fun x => -Real.sin (Real.pi * a) * U a x +
      Real.cos (Real.pi * a) * Real.Gamma (1 / 2 - a) * V a x) w := by rw [hfun]
  rw [deriv_comp_neg] at h1
  have hA : DifferentiableAt ℝ (fun x => -Real.sin (Real.pi * a) * U a x) w :=
    ((pc_diffU pc a) w).const_mul _
  have hB : DifferentiableAt ℝ (fun x => Real.cos (Real.pi * a) * Real.Gamma (1 / 2 - a) * V a x) w :=
    ((pc_diffV pc a) w).const_mul _
  rw [deriv_fun_add hA hB, deriv_const_mul _ ((pc_diffU pc a) w), deriv_const_mul _ ((pc_diffV pc a) w)] at h1
  linear_combination (-1 : ℝ) * h1

/-- The derivative of the companion formula `V(a,-z) = cos/Gamma U(a,z) + sin V(a,z)`, at `-w`. -/
lemma deriv_reflect_V (pc : ParabolicCylinderFacts U V cPC CPC) (a : ℝ) (ha : a ≤ 0) (w : ℝ) :
    deriv (V a) (-w) = (-Real.cos (Real.pi * a)) / Real.Gamma (1 / 2 - a) * deriv (U a) w +
      (-Real.sin (Real.pi * a)) * deriv (V a) w := by
  have hfun : (fun x => V a (-x)) = fun x => Real.cos (Real.pi * a) / Real.Gamma (1 / 2 - a) * U a x +
      Real.sin (Real.pi * a) * V a x :=
    funext fun x => pc.reflect_V a ha x
  have h1 : deriv (fun x => V a (-x)) w = deriv (fun x => Real.cos (Real.pi * a) / Real.Gamma (1 / 2 - a) * U a x +
      Real.sin (Real.pi * a) * V a x) w := by rw [hfun]
  rw [deriv_comp_neg] at h1
  have hA : DifferentiableAt ℝ (fun x => Real.cos (Real.pi * a) / Real.Gamma (1 / 2 - a) * U a x) w :=
    ((pc_diffU pc a) w).const_mul _
  have hB : DifferentiableAt ℝ (fun x => Real.sin (Real.pi * a) * V a x) w :=
    ((pc_diffV pc a) w).const_mul _
  rw [deriv_fun_add hA hB, deriv_const_mul _ ((pc_diffU pc a) w), deriv_const_mul _ ((pc_diffV pc a) w)] at h1
  linear_combination (-1 : ℝ) * h1

end Envelopes


/-! ### Conjunct (3), the bounds on `pcPlus`/`pcMinus` -/

section Envelopes2

variable {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- The radius `rho' = rho + l_A` of the window (the bound on `|Z|` in `lem:tha-win` (2), (3)). -/
def winR (a : ℝ) : ℝ := rhoWin a + (1 + max (-a) 0) ^ (-(1 : ℝ) / 6)

/-- The constant `C_1` of conjunct (3): uniform in `a <= a_+`, `|z| <= rho'`. -/
def winCB (CPC aplus : ℝ) : ℝ := CPC * (2 + Real.exp (5 / 2) + Real.exp (2 * Real.sqrt (1 + aplus)))

lemma ewell_bounds_nonneg (a aplus w : ℝ) (ha : a ≤ 0) (haplus : a ≤ aplus) (hw0 : 0 ≤ w) (hw : w ≤ winR a) :
    Real.exp (-(5 : ℝ) / 2) ≤ Ewell a w ∧ Ewell a w ≤ 1 := by
  have h := (weights_conj a aplus w haplus (by rw [abs_of_nonneg hw0]; exact hw)).1 ha
  rw [abs_of_nonneg hw0] at h
  exact h

lemma inv_le_exp_five_half (E : ℝ) (hE : Real.exp (-(5 : ℝ) / 2) ≤ E) : E⁻¹ ≤ Real.exp (5 / 2) := by
  have hpos : 0 < Real.exp (-(5 : ℝ) / 2) := Real.exp_pos _
  have h1 : E⁻¹ ≤ (Real.exp (-(5 : ℝ) / 2))⁻¹ := inv_anti₀ hpos hE
  rw [← Real.exp_neg] at h1
  norm_num at h1
  exact h1

lemma inv_le_exp_bar (E aplus : ℝ) (hE : Real.exp (-(2 * Real.sqrt (1 + aplus))) ≤ E) :
    E⁻¹ ≤ Real.exp (2 * Real.sqrt (1 + aplus)) := by
  have hpos : 0 < Real.exp (-(2 * Real.sqrt (1 + aplus))) := Real.exp_pos _
  have h1 : E⁻¹ ≤ (Real.exp (-(2 * Real.sqrt (1 + aplus))))⁻¹ := inv_anti₀ hpos hE
  rw [← Real.exp_neg, neg_neg] at h1
  exact h1

lemma pc_pair_well (pc : ParabolicCylinderFacts U V cPC CPC) (a : ℝ) (ha : a ≤ 0) (w : ℝ) (hw : 0 ≤ w) :
    |kappaBal a * U a w| ≤ CPC * Ewell a w * Mbal a w ∧
    |kappaBal a * deriv (U a) w| ≤ CPC * Ewell a w * Mbal a w * Real.sqrt (k2 a w) ∧
    |Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * V a w| ≤ CPC * (Ewell a w)⁻¹ * Mbal a w ∧
    |Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (V a) w| ≤
      CPC * (Ewell a w)⁻¹ * Mbal a w * Real.sqrt (k2 a w) := by
  have hk : 0 < k2 a w := lt_of_lt_of_le one_pos (win_k2_ge_one a w)
  obtain ⟨e1, e2⟩ := pc.env_well a ha w hw
  have s1 := sqrt_split _ _ _ _ hk e1
  have s2 := sqrt_split _ _ _ _ hk e2
  exact ⟨s1.1, s1.2, s2.1, s2.2⟩

lemma pcPlus_nonpos_eq (a : ℝ) (ha : a ≤ 0) :
    pcPlus U V a 0 = (fun z => kappaBal a * U a z) ∧
    pcPlus U V a 1 = (fun z => Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * V a z) := by
  constructor
  · funext z; simp [pcPlus, ha, ut]
  · funext z; simp [pcPlus, ha, vt]

lemma pcPlus_pos_eq (a : ℝ) (ha : ¬ a ≤ 0) :
    pcPlus U V a 0 = (fun z => kappaBal a * U a z) ∧ pcPlus U V a 1 = (fun z => kappaBal a * U a (-z)) := by
  constructor
  · funext z; simp [pcPlus, ha]
  · funext z; simp [pcPlus, ha]

end Envelopes2


/-! ### Conjunct (3): the bounds, case by case -/

section Envelopes3

variable {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

lemma k2_neg (a z : ℝ) : k2 a (-z) = k2 a z := by
  unfold k2; rw [neg_sq]

lemma Mbal_neg (a z : ℝ) : Mbal a (-z) = Mbal a z := by
  unfold Mbal; rw [k2_neg]

lemma Mbal_nonneg' (a z : ℝ) : 0 ≤ Mbal a z :=
  Real.rpow_nonneg (le_trans zero_le_one (win_k2_ge_one a z)) _

lemma abs_mul_le_of_le' {a b c : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ c) (hc : 0 ≤ c) : |a * b| ≤ c := by
  rw [abs_mul]
  calc |a| * |b| ≤ 1 * c := mul_le_mul ha hb (abs_nonneg _) zero_le_one
    _ = c := one_mul c

lemma cPC_pos_le (pc : ParabolicCylinderFacts U V cPC CPC) : 0 ≤ CPC :=
  le_trans (le_trans pc.cPC_pos.le pc.cPC_le) le_rfl

lemma winCB_ge (pc : ParabolicCylinderFacts U V cPC CPC) (aplus : ℝ) : CPC ≤ winCB CPC aplus := by
  unfold winCB
  have h1 := Real.exp_pos (5 / 2)
  have h2 := Real.exp_pos (2 * Real.sqrt (1 + aplus))
  have hC := cPC_pos_le pc
  nlinarith

lemma pcPlus_nonpos_value (pc : ParabolicCylinderFacts U V cPC CPC) (a : ℝ) (ha : a ≤ 0) (w : ℝ) :
    pcPlus U V a 0 (-w) = -Real.sin (Real.pi * a) * (kappaBal a * U a w) +
      Real.cos (Real.pi * a) / Real.sqrt (Real.pi / 2) *
        (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * V a w) ∧
    pcPlus U V a 1 (-w) = Real.cos (Real.pi * a) * Real.sqrt (Real.pi / 2) * (kappaBal a * U a w) +
      Real.sin (Real.pi * a) * (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * V a w) := by
  obtain ⟨hκ, hκΓ⟩ := kappa_sq_gamma a ha
  have hr : Real.sqrt (Real.pi / 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hΓ : Real.Gamma (1 / 2 - a) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  constructor
  · have e : pcPlus U V a 0 (-w) = kappaBal a * U a (-w) := by simp [pcPlus, ha, ut]
    rw [e, pc.reflect a ha w]
    exact alg_gen _ _ _ _ _ _ _ hκ hκΓ hr
  · have e : pcPlus U V a 1 (-w) = Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * V a (-w) := by
      simp [pcPlus, ha, vt]
    rw [e, pc.reflect_V a ha w]
    exact alg_two _ _ _ _ _ _ _ hκ hΓ hκΓ

lemma pcPlus_nonpos_deriv (pc : ParabolicCylinderFacts U V cPC CPC) (a : ℝ) (ha : a ≤ 0) (w : ℝ) :
    deriv (pcPlus U V a 0) (-w) = Real.sin (Real.pi * a) * (kappaBal a * deriv (U a) w) +
      (-Real.cos (Real.pi * a)) / Real.sqrt (Real.pi / 2) *
        (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (V a) w) ∧
    deriv (pcPlus U V a 1) (-w) = (-Real.cos (Real.pi * a)) * Real.sqrt (Real.pi / 2) * (kappaBal a * deriv (U a) w) +
      (-Real.sin (Real.pi * a)) * (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (V a) w) := by
  obtain ⟨hκ, hκΓ⟩ := kappa_sq_gamma a ha
  have hr : Real.sqrt (Real.pi / 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hΓ : Real.Gamma (1 / 2 - a) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  constructor
  · have e : pcPlus U V a 0 = fun z => kappaBal a * U a z := (pcPlus_nonpos_eq a ha).1
    rw [e, deriv_const_mul _ ((pc_diffU pc a) (-w)), deriv_reflect_U pc a ha w]
    exact alg_gen _ _ _ _ _ _ _ hκ hκΓ hr
  · have e : pcPlus U V a 1 = fun z => Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * V a z :=
      (pcPlus_nonpos_eq a ha).2
    rw [e, deriv_const_mul _ ((pc_diffV pc a) (-w)), deriv_reflect_V pc a ha w]
    exact alg_two _ _ _ _ _ _ _ hκ hΓ hκΓ

end Envelopes3


/-! ### Conjunct (3): the case analysis and the transfer to `pcMinus` -/

section Envelopes4

variable {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

lemma abs_add_mul_le' {α β X Y A B P Q : ℝ} (hα : |α| ≤ A) (hβ : |β| ≤ B) (hX : |X| ≤ P) (hY : |Y| ≤ Q)
    (hA : 0 ≤ A) (hP : 0 ≤ P) (hB : 0 ≤ B) (hQ : 0 ≤ Q) : |α * X + β * Y| ≤ A * P + B * Q := by
  have h1 : |α * X| ≤ A * P := by
    rw [abs_mul]; exact mul_le_mul hα hX (abs_nonneg _) hA
  have h2 : |β * Y| ≤ B * Q := by
    rw [abs_mul]; exact mul_le_mul hβ hY (abs_nonneg _) hB
  exact le_trans (abs_add_le _ _) (add_le_add h1 h2)

lemma pc_nonpos_pos_bounds (pc : ParabolicCylinderFacts U V cPC CPC) (aplus a z : ℝ) (ha : a ≤ 0)
    (haplus : a ≤ aplus) (hz0 : 0 ≤ z) (hz : z ≤ winR a) :
    |pcPlus U V a 0 z| ≤ winCB CPC aplus * Mbal a z ∧
    |deriv (pcPlus U V a 0) z| ≤ winCB CPC aplus * Real.sqrt (k2 a z) * Mbal a z ∧
    |pcPlus U V a 1 z| ≤ winCB CPC aplus * Mbal a z ∧
    |deriv (pcPlus U V a 1) z| ≤ winCB CPC aplus * Real.sqrt (k2 a z) * Mbal a z := by
  obtain ⟨hE1, hE2⟩ := ewell_bounds_nonneg a aplus z ha haplus hz0 hz
  have hinv := inv_le_exp_five_half _ hE1
  obtain ⟨b1, b2, b3, b4⟩ := pc_pair_well pc a ha z hz0
  have hM := Mbal_nonneg' a z
  have hk := Real.sqrt_nonneg (k2 a z)
  have hC := cPC_pos_le pc
  have hB : 0 ≤ Real.exp (5 / 2) := (Real.exp_pos _).le
  have hD : 0 ≤ Real.exp (2 * Real.sqrt (1 + aplus)) := (Real.exp_pos _).le
  have hCBdef : winCB CPC aplus = CPC * (2 + Real.exp (5 / 2) + Real.exp (2 * Real.sqrt (1 + aplus))) := rfl
  have k1 : CPC * Ewell a z ≤ winCB CPC aplus := by
    rw [hCBdef]
    apply mul_le_mul_of_nonneg_left _ hC
    linarith
  have k2' : CPC * (Ewell a z)⁻¹ ≤ winCB CPC aplus := by
    rw [hCBdef]
    apply mul_le_mul_of_nonneg_left _ hC
    linarith
  have e0 : pcPlus U V a 0 z = kappaBal a * U a z := by simp [pcPlus, ha, ut]
  have e1 : pcPlus U V a 1 z = Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * V a z := by
    simp [pcPlus, ha, vt]
  have d0 : deriv (pcPlus U V a 0) z = kappaBal a * deriv (U a) z := by
    rw [(pcPlus_nonpos_eq a ha).1, deriv_const_mul _ ((pc_diffU pc a) z)]
  have d1 : deriv (pcPlus U V a 1) z = Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (V a) z := by
    rw [(pcPlus_nonpos_eq a ha).2, deriv_const_mul _ ((pc_diffV pc a) z)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e0]
    calc |kappaBal a * U a z| ≤ CPC * Ewell a z * Mbal a z := b1
      _ ≤ winCB CPC aplus * Mbal a z := mul_le_mul_of_nonneg_right k1 hM
  · rw [d0]
    calc |kappaBal a * deriv (U a) z| ≤ CPC * Ewell a z * Mbal a z * Real.sqrt (k2 a z) := b2
      _ ≤ winCB CPC aplus * Mbal a z * Real.sqrt (k2 a z) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k1 hM) hk
      _ = winCB CPC aplus * Real.sqrt (k2 a z) * Mbal a z := by ring
  · rw [e1]
    calc _ ≤ CPC * (Ewell a z)⁻¹ * Mbal a z := b3
      _ ≤ winCB CPC aplus * Mbal a z := mul_le_mul_of_nonneg_right k2' hM
  · rw [d1]
    calc _ ≤ CPC * (Ewell a z)⁻¹ * Mbal a z * Real.sqrt (k2 a z) := b4
      _ ≤ winCB CPC aplus * Mbal a z * Real.sqrt (k2 a z) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k2' hM) hk
      _ = winCB CPC aplus * Real.sqrt (k2 a z) * Mbal a z := by ring

lemma pc_nonpos_neg_bounds (pc : ParabolicCylinderFacts U V cPC CPC) (aplus a w : ℝ) (ha : a ≤ 0)
    (haplus : a ≤ aplus) (hw0 : 0 ≤ w) (hw : w ≤ winR a) :
    |pcPlus U V a 0 (-w)| ≤ winCB CPC aplus * Mbal a w ∧
    |deriv (pcPlus U V a 0) (-w)| ≤ winCB CPC aplus * Real.sqrt (k2 a w) * Mbal a w ∧
    |pcPlus U V a 1 (-w)| ≤ winCB CPC aplus * Mbal a w ∧
    |deriv (pcPlus U V a 1) (-w)| ≤ winCB CPC aplus * Real.sqrt (k2 a w) * Mbal a w := by
  obtain ⟨hE1, hE2⟩ := ewell_bounds_nonneg a aplus w ha haplus hw0 hw
  have hinv := inv_le_exp_five_half _ hE1
  obtain ⟨b1, b2, b3, b4⟩ := pc_pair_well pc a ha w hw0
  have hM := Mbal_nonneg' a w
  have hk := Real.sqrt_nonneg (k2 a w)
  have hC := cPC_pos_le pc
  have hEwnn : 0 ≤ Ewell a w := le_trans (Real.exp_pos _).le hE1
  have hinvnn : 0 ≤ (Ewell a w)⁻¹ := inv_nonneg.mpr hEwnn
  have hB : 0 ≤ Real.exp (5 / 2) := (Real.exp_pos _).le
  have hD : 0 ≤ Real.exp (2 * Real.sqrt (1 + aplus)) := (Real.exp_pos _).le
  have hCBdef : winCB CPC aplus = CPC * (2 + Real.exp (5 / 2) + Real.exp (2 * Real.sqrt (1 + aplus))) := rfl
  have hr1 : 1 ≤ Real.sqrt (Real.pi / 2) := Real.one_le_sqrt.mpr (by linarith [Real.pi_gt_three])
  have hr2 : Real.sqrt (Real.pi / 2) ≤ 2 := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    calc Real.sqrt (Real.pi / 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith [Real.pi_le_four])
      _ = 2 := h4
  have hcos : |Real.cos (Real.pi * a)| ≤ 1 := Real.abs_cos_le_one _
  have hsin : |Real.sin (Real.pi * a)| ≤ 1 := Real.abs_sin_le_one _
  have hr0 : 0 < Real.sqrt (Real.pi / 2) := by linarith
  have hcosr : |Real.cos (Real.pi * a) / Real.sqrt (Real.pi / 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos hr0]
    exact (div_le_one hr0).mpr (le_trans hcos hr1)
  have hcosr2 : |Real.cos (Real.pi * a) * Real.sqrt (Real.pi / 2)| ≤ 2 := by
    rw [abs_mul, abs_of_pos hr0]
    calc |Real.cos (Real.pi * a)| * Real.sqrt (Real.pi / 2) ≤ 1 * 2 :=
          mul_le_mul hcos hr2 hr0.le zero_le_one
      _ = 2 := by ring
  have hsinneg : |-Real.sin (Real.pi * a)| ≤ 1 := by rw [abs_neg]; exact hsin
  have hnegcosr : |(-Real.cos (Real.pi * a)) / Real.sqrt (Real.pi / 2)| ≤ 1 := by
    rw [neg_div, abs_neg]; exact hcosr
  have hnegcosr2 : |(-Real.cos (Real.pi * a)) * Real.sqrt (Real.pi / 2)| ≤ 2 := by
    rw [neg_mul, abs_neg]; exact hcosr2
  have k3 : CPC * Ewell a w + CPC * (Ewell a w)⁻¹ ≤ winCB CPC aplus := by
    have h1 : CPC * Ewell a w ≤ CPC := mul_le_of_le_one_right hC hE2
    have h2 : CPC * (Ewell a w)⁻¹ ≤ CPC * Real.exp (5 / 2) := mul_le_mul_of_nonneg_left hinv hC
    have h3 : 0 ≤ CPC * Real.exp (2 * Real.sqrt (1 + aplus)) := mul_nonneg hC hD
    have h4 : winCB CPC aplus = 2 * CPC + CPC * Real.exp (5 / 2) + CPC * Real.exp (2 * Real.sqrt (1 + aplus)) := by
      rw [hCBdef]; ring
    rw [h4]
    linarith
  have k4 : 2 * (CPC * Ewell a w) + CPC * (Ewell a w)⁻¹ ≤ winCB CPC aplus := by
    have h1 : CPC * Ewell a w ≤ CPC := mul_le_of_le_one_right hC hE2
    have h2 : CPC * (Ewell a w)⁻¹ ≤ CPC * Real.exp (5 / 2) := mul_le_mul_of_nonneg_left hinv hC
    have h3 : 0 ≤ CPC * Real.exp (2 * Real.sqrt (1 + aplus)) := mul_nonneg hC hD
    have h4 : winCB CPC aplus = 2 * CPC + CPC * Real.exp (5 / 2) + CPC * Real.exp (2 * Real.sqrt (1 + aplus)) := by
      rw [hCBdef]; ring
    rw [h4]
    linarith
  have hP1 : 0 ≤ CPC * Ewell a w * Mbal a w := mul_nonneg (mul_nonneg hC hEwnn) hM
  have hQ1 : 0 ≤ CPC * (Ewell a w)⁻¹ * Mbal a w := mul_nonneg (mul_nonneg hC hinvnn) hM
  have hP2 : 0 ≤ CPC * Ewell a w * Mbal a w * Real.sqrt (k2 a w) := mul_nonneg hP1 hk
  have hQ2 : 0 ≤ CPC * (Ewell a w)⁻¹ * Mbal a w * Real.sqrt (k2 a w) := mul_nonneg hQ1 hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h0 := (pcPlus_nonpos_value pc a ha w).1
    have hb := abs_add_mul_le' hsinneg hcosr b1 b3 zero_le_one hP1 zero_le_one hQ1
    rw [h0]
    refine hb.trans ?_
    calc 1 * (CPC * Ewell a w * Mbal a w) + 1 * (CPC * (Ewell a w)⁻¹ * Mbal a w)
        = (CPC * Ewell a w + CPC * (Ewell a w)⁻¹) * Mbal a w := by ring
      _ ≤ winCB CPC aplus * Mbal a w := mul_le_mul_of_nonneg_right k3 hM
  · have h0 := (pcPlus_nonpos_deriv pc a ha w).1
    have hb := abs_add_mul_le' hsin hnegcosr b2 b4 zero_le_one hP2 zero_le_one hQ2
    rw [h0]
    refine hb.trans ?_
    calc 1 * (CPC * Ewell a w * Mbal a w * Real.sqrt (k2 a w)) +
          1 * (CPC * (Ewell a w)⁻¹ * Mbal a w * Real.sqrt (k2 a w))
        = (CPC * Ewell a w + CPC * (Ewell a w)⁻¹) * Mbal a w * Real.sqrt (k2 a w) := by ring
      _ ≤ winCB CPC aplus * Mbal a w * Real.sqrt (k2 a w) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k3 hM) hk
      _ = winCB CPC aplus * Real.sqrt (k2 a w) * Mbal a w := by ring
  · have h1 := (pcPlus_nonpos_value pc a ha w).2
    have hb := abs_add_mul_le' hcosr2 hsin b1 b3 (by norm_num) hP1 zero_le_one hQ1
    rw [h1]
    refine hb.trans ?_
    calc 2 * (CPC * Ewell a w * Mbal a w) + 1 * (CPC * (Ewell a w)⁻¹ * Mbal a w)
        = (2 * (CPC * Ewell a w) + CPC * (Ewell a w)⁻¹) * Mbal a w := by ring
      _ ≤ winCB CPC aplus * Mbal a w := mul_le_mul_of_nonneg_right k4 hM
  · have h1 := (pcPlus_nonpos_deriv pc a ha w).2
    have hb := abs_add_mul_le' hnegcosr2 hsinneg b2 b4 (by norm_num) hP2 zero_le_one hQ2
    rw [h1]
    refine hb.trans ?_
    calc 2 * (CPC * Ewell a w * Mbal a w * Real.sqrt (k2 a w)) +
          1 * (CPC * (Ewell a w)⁻¹ * Mbal a w * Real.sqrt (k2 a w))
        = (2 * (CPC * Ewell a w) + CPC * (Ewell a w)⁻¹) * Mbal a w * Real.sqrt (k2 a w) := by ring
      _ ≤ winCB CPC aplus * Mbal a w * Real.sqrt (k2 a w) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k4 hM) hk
      _ = winCB CPC aplus * Real.sqrt (k2 a w) * Mbal a w := by ring

end Envelopes4


/-! ### Conjunct (3): the case `a > 0` and the full bounds -/

section Envelopes5

variable {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

lemma pc_pos_bounds (pc : ParabolicCylinderFacts U V cPC CPC) (aplus a z : ℝ) (ha : 0 < a)
    (haplus : a ≤ aplus) (hz : |z| ≤ winR a) :
    |pcPlus U V a 0 z| ≤ winCB CPC aplus * Mbal a z ∧
    |deriv (pcPlus U V a 0) z| ≤ winCB CPC aplus * Real.sqrt (k2 a z) * Mbal a z ∧
    |pcPlus U V a 1 z| ≤ winCB CPC aplus * Mbal a z ∧
    |deriv (pcPlus U V a 1) z| ≤ winCB CPC aplus * Real.sqrt (k2 a z) * Mbal a z := by
  have hna : ¬ a ≤ 0 := not_le.mpr ha
  obtain ⟨eb1, eb2⟩ := (weights_conj a aplus z haplus hz).2 ha
  have hC := cPC_pos_le pc
  have hM := Mbal_nonneg' a z
  have hk1 : 0 < k2 a z := lt_of_lt_of_le one_pos (win_k2_ge_one a z)
  have hk := Real.sqrt_nonneg (k2 a z)
  have hEnn : 0 ≤ Ebar a z := le_trans (Real.exp_pos _).le eb1
  have hinv : (Ebar a z)⁻¹ ≤ Real.exp (2 * Real.sqrt (1 + aplus)) := inv_le_exp_bar _ aplus eb1
  have hB : 0 ≤ Real.exp (5 / 2) := (Real.exp_pos _).le
  have hD : 0 ≤ Real.exp (2 * Real.sqrt (1 + aplus)) := (Real.exp_pos _).le
  have hCBdef : winCB CPC aplus = CPC * (2 + Real.exp (5 / 2) + Real.exp (2 * Real.sqrt (1 + aplus))) := rfl
  have hpos : 0 ≤ CPC * (2 + Real.exp (5 / 2)) := mul_nonneg hC (by linarith)
  have hsplit : winCB CPC aplus = CPC * (2 + Real.exp (5 / 2)) + CPC * Real.exp (2 * Real.sqrt (1 + aplus)) := by
    rw [hCBdef]; ring
  have k5 : CPC * Ebar a z ≤ winCB CPC aplus := by
    have := mul_le_mul_of_nonneg_left eb2 hC
    linarith
  have k6 : CPC * (Ebar a z)⁻¹ ≤ winCB CPC aplus := by
    have := mul_le_mul_of_nonneg_left hinv hC
    linarith
  obtain ⟨e1, e2⟩ := pc.env_bar a ha z
  have s1 := sqrt_split _ _ _ _ hk1 e1
  have s2 := sqrt_split _ _ _ _ hk1 e2
  have e0 : pcPlus U V a 0 z = kappaBal a * U a z := by simp [pcPlus, hna, ut]
  have f1 : pcPlus U V a 1 z = kappaBal a * U a (-z) := by simp [pcPlus, hna]
  have hd : DifferentiableAt ℝ (fun w => U a (-w)) z :=
    ((pc_diffU pc a) (-z)).comp z (differentiableAt_id.neg)
  have d0 : deriv (pcPlus U V a 0) z = kappaBal a * deriv (U a) z := by
    have : pcPlus U V a 0 = fun y => kappaBal a * U a y := by
      funext y; simp [pcPlus, hna, ut]
    rw [this, deriv_const_mul _ ((pc_diffU pc a) z)]
  have d1 : deriv (pcPlus U V a 1) z = kappaBal a * deriv (fun w => U a (-w)) z := by
    have : pcPlus U V a 1 = fun y => kappaBal a * U a (-y) := by
      funext y; simp [pcPlus, hna]
    rw [this, deriv_const_mul _ hd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e0]
    calc |kappaBal a * U a z| ≤ CPC * Ebar a z * Mbal a z := s1.1
      _ ≤ winCB CPC aplus * Mbal a z := mul_le_mul_of_nonneg_right k5 hM
  · rw [d0]
    calc |kappaBal a * deriv (U a) z| ≤ CPC * Ebar a z * Mbal a z * Real.sqrt (k2 a z) := s1.2
      _ ≤ winCB CPC aplus * Mbal a z * Real.sqrt (k2 a z) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k5 hM) hk
      _ = winCB CPC aplus * Real.sqrt (k2 a z) * Mbal a z := by ring
  · rw [f1]
    calc |kappaBal a * U a (-z)| ≤ CPC * (Ebar a z)⁻¹ * Mbal a z := s2.1
      _ ≤ winCB CPC aplus * Mbal a z := mul_le_mul_of_nonneg_right k6 hM
  · rw [d1]
    calc |kappaBal a * deriv (fun w => U a (-w)) z| ≤ CPC * (Ebar a z)⁻¹ * Mbal a z * Real.sqrt (k2 a z) := s2.2
      _ ≤ winCB CPC aplus * Mbal a z * Real.sqrt (k2 a z) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k6 hM) hk
      _ = winCB CPC aplus * Real.sqrt (k2 a z) * Mbal a z := by ring

/-- The bounds on `pcPlus` for all `z` in the window `|z| <= rho'`, for `a <= a_+`. -/
lemma pcPlus_all (pc : ParabolicCylinderFacts U V cPC CPC) (aplus a z : ℝ) (haplus : a ≤ aplus)
    (hz : |z| ≤ winR a) :
    (|pcPlus U V a 0 z| ≤ winCB CPC aplus * Mbal a z ∧
      |deriv (pcPlus U V a 0) z| ≤ winCB CPC aplus * Real.sqrt (k2 a z) * Mbal a z) ∧
    (|pcPlus U V a 1 z| ≤ winCB CPC aplus * Mbal a z ∧
      |deriv (pcPlus U V a 1) z| ≤ winCB CPC aplus * Real.sqrt (k2 a z) * Mbal a z) := by
  by_cases ha : a ≤ 0
  · rcases le_or_gt 0 z with hz0 | hz0
    · have hz' : z ≤ winR a := by rw [abs_of_nonneg hz0] at hz; exact hz
      obtain ⟨p1, p2, p3, p4⟩ := pc_nonpos_pos_bounds pc aplus a z ha haplus hz0 hz'
      exact ⟨⟨p1, p2⟩, ⟨p3, p4⟩⟩
    · obtain ⟨w, rfl⟩ : ∃ w, z = -w := ⟨-z, (neg_neg z).symm⟩
      have hw0 : 0 ≤ w := by linarith
      have hw : w ≤ winR a := by rw [abs_neg, abs_of_nonneg hw0] at hz; exact hz
      obtain ⟨p1, p2, p3, p4⟩ := pc_nonpos_neg_bounds pc aplus a w ha haplus hw0 hw
      rw [Mbal_neg, k2_neg]
      exact ⟨⟨p1, p2⟩, ⟨p3, p4⟩⟩
  · obtain ⟨p1, p2, p3, p4⟩ := pc_pos_bounds pc aplus a z (not_le.mp ha) haplus hz
    exact ⟨⟨p1, p2⟩, ⟨p3, p4⟩⟩

end Envelopes5


/-! ### Conjunct (3): `pcMinus` and the frozen form -/

section Envelopes6

variable {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

lemma pcMinus_zero_eq (a : ℝ) : pcMinus U V a 0 = fun y => pcPlus U V a 0 (-y) := rfl

lemma pcMinus_one_eq (a : ℝ) : pcMinus U V a 1 = fun y => -pcPlus U V a 1 (-y) := by
  funext y
  by_cases h : a ≤ 0
  · simp [pcMinus, pcPlus, h]
  · simp [pcMinus, pcPlus, h]

lemma deriv_fun_neg_comp {g : ℝ → ℝ} {x : ℝ} : deriv (fun y => -g y) x = -deriv g x := by
  rw [show (fun y => -g y) = -g from rfl]
  exact deriv.neg

/-- Conjunct (3) of `lem:tha-win`: the envelope bounds of `pcPlus` and `pcMinus`, both pairs, all `i`, uniform in `a <= a_+`. -/
lemma envelope_conj3 (pc : ParabolicCylinderFacts U V cPC CPC) (aplus a z : ℝ) (haplus : a ≤ aplus)
    (hz : |z| ≤ winR a) :
    ∀ i : Fin 2,
      (|pcPlus U V a i z| ≤ winCB CPC aplus * Mbal a z ∧
        |deriv (pcPlus U V a i) z| ≤ winCB CPC aplus * Real.sqrt (k2 a z) * Mbal a z) ∧
      (|pcMinus U V a i z| ≤ winCB CPC aplus * Mbal a z ∧
        |deriv (pcMinus U V a i) z| ≤ winCB CPC aplus * Real.sqrt (k2 a z) * Mbal a z) := by
  have hmz : |-z| ≤ winR a := by rw [abs_neg]; exact hz
  obtain ⟨⟨p1, p2⟩, ⟨p3, p4⟩⟩ := pcPlus_all pc aplus a z haplus hz
  obtain ⟨⟨q1, q2⟩, ⟨q3, q4⟩⟩ := pcPlus_all pc aplus a (-z) haplus hmz
  rw [Mbal_neg] at q1 q3
  rw [Mbal_neg, k2_neg] at q2 q4
  rw [Fin.forall_fin_two]
  constructor
  · refine ⟨⟨p1, p2⟩, ⟨?_, ?_⟩⟩
    · show |pcPlus U V a 0 (-z)| ≤ _
      exact q1
    · rw [pcMinus_zero_eq, deriv_comp_neg, abs_neg]
      exact q2
  · refine ⟨⟨p3, p4⟩, ⟨?_, ?_⟩⟩
    · have hv : pcMinus U V a 1 z = -pcPlus U V a 1 (-z) := by rw [pcMinus_one_eq]
      rw [hv, abs_neg]
      exact q3
    · rw [pcMinus_one_eq, deriv_fun_neg_comp, deriv_comp_neg, neg_neg]
      exact q4

end Envelopes6


/-! ### Conjunct (5): lattice sums of monotone functions -/

section Lattice

lemma cell_bounds {g : ℝ → ℝ} (hg : Monotone g) {a b : ℝ} (hab : a ≤ b) :
    g a * (b - a) ≤ ∫ x in a..b, g x ∧ ∫ x in a..b, g x ≤ g b * (b - a) := by
  constructor
  · have h := intervalIntegral.integral_mono_on hab ((continuous_const.intervalIntegrable _ _))
      hg.intervalIntegrable (μ := MeasureTheory.volume) (fun x hx => hg hx.1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith [h]
  · have h := intervalIntegral.integral_mono_on hab hg.intervalIntegrable (μ := MeasureTheory.volume)
      ((continuous_const.intervalIntegrable _ _)) (fun x hx => hg hx.2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith [h]

/-- Left-endpoint sums of a monotone function over a chain of points with gaps at most `δ`:
the sum is between the integral minus a telescoping boundary term and the integral. -/
lemma riemann_lattice {g : ℝ → ℝ} (hg : Monotone g) (Z : ℕ → ℝ) (hZ : ∀ i, Z i ≤ Z (i + 1))
    (δ : ℝ) (hδ : 0 ≤ δ) (hstep : ∀ i, Z (i + 1) - Z i ≤ δ) (K : ℕ) :
    (∫ x in Z 0..Z K, g x) - δ * (g (Z K) - g (Z 0)) ≤
        ∑ i ∈ Finset.range K, g (Z i) * (Z (i + 1) - Z i) ∧
      ∑ i ∈ Finset.range K, g (Z i) * (Z (i + 1) - Z i) ≤ ∫ x in Z 0..Z K, g x := by
  have hmon : Monotone Z := monotone_nat_of_le_succ hZ
  induction K with
  | zero => simp
  | succ K ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hcell := cell_bounds hg (hZ K)
    have hint := intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (μ := MeasureTheory.volume) (a := Z 0) (b := Z K)) (hg.intervalIntegrable (μ := MeasureTheory.volume) (a := Z K) (b := Z (K + 1)))
    have hstepK := hstep K
    have hmonoK : g (Z K) ≤ g (Z (K + 1)) := hg (hZ K)
    have hup : g (Z K) * (Z (K + 1) - Z K) ≤ ∫ x in Z K..Z (K + 1), g x := hcell.1
    have hlow : (∫ x in Z K..Z (K + 1), g x) - δ * (g (Z (K + 1)) - g (Z K)) ≤ g (Z K) * (Z (K + 1) - Z K) := by
      have h1 : (∫ x in Z K..Z (K + 1), g x) ≤ g (Z (K + 1)) * (Z (K + 1) - Z K) := hcell.2
      have h2 : (g (Z (K + 1)) - g (Z K)) * (Z (K + 1) - Z K) ≤ (g (Z (K + 1)) - g (Z K)) * δ :=
        mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hmonoK)
      nlinarith [h1, h2]
    rw [Finset.sum_range_succ]
    have hd : δ * (g (Z (K + 1)) - g (Z 0)) = δ * (g (Z K) - g (Z 0)) + δ * (g (Z (K + 1)) - g (Z K)) := by ring
    constructor
    · linarith [ih1, hlow, hint, hd]
    · linarith [ih2, hup, hint]

end Lattice


/-! ### The monotone decomposition of an up-down-up-down function -/

section Decomp

/-- A function with the shape `up on (-∞,-s], down on [-s,0], up on [0,s], down on [s,∞)` (values in `[0,1]`) is the difference of two
nondecreasing functions with values in `[0,2]` and `[0,3]`. -/
lemma decomp_monotone (f : ℝ → ℝ) (s : ℝ) (hs : 0 ≤ s)
    (h1 : MonotoneOn f (Set.Iic (-s))) (h2 : AntitoneOn f (Set.Icc (-s) 0))
    (h3 : MonotoneOn f (Set.Icc 0 s)) (h4 : AntitoneOn f (Set.Ici s))
    (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1) :
    ∃ f1 f2 : ℝ → ℝ, Monotone f1 ∧ Monotone f2 ∧ (∀ z, f z = f1 z - f2 z) ∧
      (∀ z, 0 ≤ f2 z ∧ f2 z ≤ 2) ∧ (∀ z, 0 ≤ f1 z ∧ f1 z ≤ 3) := by
  let p : ℝ → ℝ := fun z => min (max z (-s)) 0
  let q : ℝ → ℝ := fun z => max z s
  have hpmono : Monotone p := (monotone_id.max monotone_const).min monotone_const
  have hqmono : Monotone q := monotone_id.max monotone_const
  have hpI : ∀ z, p z ∈ Set.Icc (-s) 0 := fun z =>
    ⟨le_min (le_max_right _ _) (by linarith), min_le_right _ _⟩
  have hqI : ∀ z, q z ∈ Set.Ici s := fun z => le_max_right _ _
  let f2 : ℝ → ℝ := fun z => (f (-s) - f (p z)) + (f s - f (q z))
  let f1 : ℝ → ℝ := fun z => f z + f2 z
  have hfp_le : ∀ z, f (p z) ≤ f (-s) := fun z =>
    h2 ⟨le_refl _, by linarith⟩ (hpI z) (hpI z).1
  have hfq_le : ∀ z, f (q z) ≤ f s := fun z =>
    h4 (Set.mem_Ici.mpr le_rfl) (hqI z) (Set.mem_Ici.mp (hqI z))
  -- f2 is nondecreasing and takes values in [0,2]
  have hF2 : Monotone f2 := by
    intro z z' hzz'
    have hpp : p z ≤ p z' := hpmono hzz'
    have hqq : q z ≤ q z' := hqmono hzz'
    have ha : f (p z') ≤ f (p z) := h2 (hpI z) (hpI z') hpp
    have hb : f (q z') ≤ f (q z) := h4 (hqI z) (hqI z') hqq
    show (f (-s) - f (p z)) + (f s - f (q z)) ≤ (f (-s) - f (p z')) + (f s - f (q z'))
    linarith
  have hf2b : ∀ z, 0 ≤ f2 z ∧ f2 z ≤ 2 := by
    intro z
    have e1 := hfp_le z
    have e2 := hfq_le z
    have a1 := hf0 (p z)
    have a2 := hf0 (q z)
    have b1 := hf1 (-s)
    have b2 := hf1 s
    show 0 ≤ (f (-s) - f (p z)) + (f s - f (q z)) ∧
      (f (-s) - f (p z)) + (f s - f (q z)) ≤ 2
    constructor <;> linarith
  -- the four regions of the decomposition
  have hR1 : ∀ z, z ≤ -s → f1 z = f z := by
    intro z hz
    have hp : p z = -s := by
      simp only [p]
      rw [max_eq_right (show z ≤ -s from hz), min_eq_left (show -s ≤ 0 by linarith)]
    have hq : q z = s := by
      simp only [q]
      rw [max_eq_right (show z ≤ s by linarith)]
    simp only [f1, f2, hp, hq]
    ring
  have hR2 : ∀ z, -s < z → z ≤ 0 → f1 z = f (-s) := by
    intro z hz hz0
    have hp : p z = z := by
      simp only [p]
      rw [max_eq_left (show -s ≤ z by linarith), min_eq_left (show z ≤ 0 from hz0)]
    have hq : q z = s := by
      simp only [q]
      rw [max_eq_right (show z ≤ s by linarith)]
    simp only [f1, f2, hp, hq]
    ring
  have hR3 : ∀ z, 0 < z → z ≤ s → f1 z = f z + f (-s) - f 0 := by
    intro z hz hzs
    have hp : p z = 0 := by
      simp only [p]
      rw [max_eq_left (show -s ≤ z by linarith), min_eq_right (show (0:ℝ) ≤ z from le_of_lt hz)]
    have hq : q z = s := by
      simp only [q]
      rw [max_eq_right hzs]
    simp only [f1, f2, hp, hq]
    ring
  have hR4 : ∀ z, s < z → f1 z = f (-s) - f 0 + f s := by
    intro z hz
    have hp : p z = 0 := by
      simp only [p]
      rw [max_eq_left (show -s ≤ z by linarith), min_eq_right (show (0:ℝ) ≤ z by linarith)]
    have hq : q z = z := by
      simp only [q]
      rw [max_eq_left (show s ≤ z from le_of_lt hz)]
    simp only [f1, f2, hp, hq]
    ring
  -- monotone facts for f on the four pieces
  have hF1 : ∀ x y, x ≤ y → y ≤ -s → f x ≤ f y := fun x y hxy hy =>
    h1 (show x ∈ Set.Iic (-s) from le_trans hxy hy) (show y ∈ Set.Iic (-s) from hy) hxy
  have hF1lo : ∀ x, x ≤ -s → f x ≤ f (-s) := fun x hx =>
    h1 (show x ∈ Set.Iic (-s) from hx) (show -s ∈ Set.Iic (-s) from le_refl _) hx
  have hF3 : ∀ x y, 0 ≤ x → x ≤ y → y ≤ s → f x ≤ f y := fun x y hx hxy hy =>
    h3 ⟨hx, le_trans hxy hy⟩ ⟨le_trans hx hxy, hy⟩ hxy
  have hF3lo : ∀ x, 0 ≤ x → x ≤ s → f 0 ≤ f x := fun x hx hxs =>
    h3 ⟨le_refl 0, hs⟩ ⟨hx, hxs⟩ hx
  have hF3hi : ∀ x, 0 ≤ x → x ≤ s → f x ≤ f s := fun x hx hxs =>
    h3 ⟨hx, hxs⟩ ⟨hs, le_refl s⟩ hxs
  -- f1 is nondecreasing: split z and z' into the four regions
  have hF1mono : Monotone f1 := by
    have key : ∀ x : ℝ, x ≤ -s ∨ (-s < x ∧ x ≤ 0) ∨ (0 < x ∧ x ≤ s) ∨ s < x := by
      intro x
      rcases le_or_gt x (-s) with k1 | k1
      · exact Or.inl k1
      rcases le_or_gt x 0 with k2 | k2
      · exact Or.inr (Or.inl ⟨k1, k2⟩)
      rcases le_or_gt x s with k3 | k3
      · exact Or.inr (Or.inr (Or.inl ⟨k2, k3⟩))
      · exact Or.inr (Or.inr (Or.inr k3))
    intro z z' hzz'
    rcases key z with hz | hz | hz | hz <;> rcases key z' with hz' | hz' | hz' | hz'
    · linarith [hR1 z hz, hR1 z' hz', hF1 z z' hzz' hz']
    · linarith [hR1 z hz, hR2 z' hz'.1 hz'.2, hF1lo z hz]
    · linarith [hR1 z hz, hR3 z' hz'.1 hz'.2, hF1lo z hz, hF3lo z' hz'.1.le hz'.2]
    · linarith [hR1 z hz, hR4 z' hz', hF1lo z hz, hF3lo s hs le_rfl]
    · linarith [hz.1]
    · linarith [hR2 z hz.1 hz.2, hR2 z' hz'.1 hz'.2]
    · linarith [hR2 z hz.1 hz.2, hR3 z' hz'.1 hz'.2, hF3lo z' hz'.1.le hz'.2]
    · linarith [hR2 z hz.1 hz.2, hR4 z' hz', hF3lo s hs le_rfl]
    · linarith [hz.1, hs]
    · linarith [hz.1, hz'.2]
    · linarith [hR3 z hz.1 hz.2, hR3 z' hz'.1 hz'.2, hF3 z z' hz.1.le hzz' hz'.2]
    · linarith [hR3 z hz.1 hz.2, hR4 z' hz', hF3hi z hz.1.le hz.2]
    · linarith [hz, hs]
    · linarith [hz, hz'.2]
    · linarith [hz, hz'.2]
    · linarith [hR4 z hz, hR4 z' hz']
  refine ⟨f1, f2, hF1mono, hF2, fun z => ?_, fun z => hf2b z, fun z => ?_⟩
  · show f z = (f z + f2 z) - f2 z
    ring
  · have b := hf2b z
    have a := hf0 z
    have c := hf1 z
    show 0 ≤ f z + f2 z ∧ f z + f2 z ≤ 3
    constructor <;> linarith [b.1, b.2]

end Decomp


/-! ### The window weight `Mbal^2`: shape, decomposition -/

section WinWeight

lemma sq_le_of_mem_Icc (s z : ℝ) (h1 : -s ≤ z) (h2 : z ≤ s) : z ^ 2 ≤ s ^ 2 := sq_le_sq' h1 h2

/-- the turning-point half-width `s0 = 2 sqrt(max(-a,0))` of the window weight. -/
def winS0 (a : ℝ) : ℝ := 2 * Real.sqrt (max (-a) 0)

lemma winS0_nonneg (a : ℝ) : 0 ≤ winS0 a := by unfold winS0; positivity

lemma winS0_sq (a : ℝ) : winS0 a ^ 2 = 4 * max (-a) 0 := by
  unfold winS0
  rw [mul_pow, Real.sq_sqrt (le_max_right _ _)]
  norm_num

lemma winS0_zero_of_pos {a : ℝ} (ha : 0 < a) : winS0 a = 0 := by
  unfold winS0
  rw [max_eq_right (by linarith : -a ≤ 0)]
  simp

lemma mbal_sq_eq (a z : ℝ) : Mbal a z ^ 2 = (k2 a z) ^ (-(1 : ℝ) / 2) := by
  have hk : 0 ≤ k2 a z := le_trans zero_le_one (win_k2_ge_one a z)
  unfold Mbal
  rw [← Real.rpow_natCast, ← Real.rpow_mul hk]
  norm_num

lemma mbal_sq_le_of_k2 (a x y : ℝ) (h : k2 a y ≤ k2 a x) : Mbal a x ^ 2 ≤ Mbal a y ^ 2 := by
  rw [mbal_sq_eq, mbal_sq_eq]
  exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (win_k2_ge_one a y)) h (by norm_num)

lemma mbal_sq_le_one (a z : ℝ) : Mbal a z ^ 2 ≤ 1 := by
  rw [mbal_sq_eq]
  exact Real.rpow_le_one_of_one_le_of_nonpos (win_k2_ge_one a z) (by norm_num)

lemma k2_le_of_phi (a x y : ℝ) (h : |y ^ 2 / 4 + a| ≤ |x ^ 2 / 4 + a|) : k2 a y ≤ k2 a x := by
  unfold k2
  exact max_le_max h le_rfl

lemma abs_phi_far (a z : ℝ) (hz : 4 * max (-a) 0 ≤ z ^ 2) : |z ^ 2 / 4 + a| = z ^ 2 / 4 + a := by
  have h1 := le_max_left (-a) 0
  apply abs_of_nonneg
  linarith

lemma abs_phi_near (a z : ℝ) (ha : a ≤ 0) (hz : z ^ 2 ≤ -4 * a) : |z ^ 2 / 4 + a| = -a - z ^ 2 / 4 := by
  rw [abs_of_nonpos (by linarith)]
  ring

lemma sq_anti_neg (x y : ℝ) (hxy : x ≤ y) (hy : y ≤ 0) : y ^ 2 ≤ x ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.2 hxy) (show (0:ℝ) ≤ -(x + y) by linarith)]

lemma sq_mono_pos (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) : x ^ 2 ≤ y ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.2 hxy) (show (0:ℝ) ≤ x + y by linarith)]

lemma far_sq (s z : ℝ) (hs : 0 ≤ s) (hz : z ≤ -s ∨ s ≤ z) : s ^ 2 ≤ z ^ 2 := by
  rcases hz with h | h
  · have h' := sq_mono_pos s (-z) hs (by linarith)
    rwa [neg_sq] at h'
  · exact sq_mono_pos s z hs h

/-- `Mbal^2` is nondecreasing on `(-∞, -s0]`. -/
lemma mbal_sq_mono_left (a : ℝ) : MonotoneOn (fun z => Mbal a z ^ 2) (Set.Iic (-winS0 a)) := by
  intro x hx y hy hxy
  have hx' : x ≤ -winS0 a := hx
  have hy' : y ≤ -winS0 a := hy
  have hs := winS0_nonneg a
  have e := winS0_sq a
  have fx := far_sq (winS0 a) x hs (Or.inl hx')
  have fy := far_sq (winS0 a) y hs (Or.inl hy')
  show Mbal a x ^ 2 ≤ Mbal a y ^ 2
  refine mbal_sq_le_of_k2 a x y ?_
  apply k2_le_of_phi
  rw [abs_phi_far a x (by linarith), abs_phi_far a y (by linarith)]
  have := sq_anti_neg x y hxy (by linarith)
  linarith

/-- `Mbal^2` is nonincreasing on `[-s0, 0]`. -/
lemma mbal_sq_anti_mid (a : ℝ) : AntitoneOn (fun z => Mbal a z ^ 2) (Set.Icc (-winS0 a) 0) := by
  intro x hx y hy hxy
  have hx1 : -winS0 a ≤ x := hx.1
  have hy0 : y ≤ 0 := hy.2
  show Mbal a y ^ 2 ≤ Mbal a x ^ 2
  refine mbal_sq_le_of_k2 a y x ?_
  rcases le_or_gt a 0 with ha | ha
  · apply k2_le_of_phi
    have e := winS0_sq a
    have hmax : max (-a) 0 = -a := max_eq_left (by linarith)
    have hsx : x ^ 2 ≤ -4 * a := by
      have := sq_le_of_mem_Icc (winS0 a) x hx1 (by linarith [winS0_nonneg a, hx.2])
      rw [e, hmax] at this
      linarith
    rw [abs_phi_near a x ha hsx, abs_phi_near a y ha (by nlinarith [sq_anti_neg x y hxy hy0])]
    have := sq_anti_neg x y hxy hy0
    linarith
  · have hs0 := winS0_zero_of_pos ha
    rw [hs0] at hx1 hx
    have hx0 : x = 0 := by linarith [hx.2]
    have hy0' : y = 0 := by linarith [hy.1]
    rw [hx0, hy0']

/-- `Mbal^2` is nondecreasing on `[0, s0]`. -/
lemma mbal_sq_mono_mid (a : ℝ) : MonotoneOn (fun z => Mbal a z ^ 2) (Set.Icc 0 (winS0 a)) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx.1
  have hyS : y ≤ winS0 a := hy.2
  show Mbal a x ^ 2 ≤ Mbal a y ^ 2
  rcases le_or_gt a 0 with ha | ha
  · refine mbal_sq_le_of_k2 a x y ?_
    apply k2_le_of_phi
    have e := winS0_sq a
    have hmax : max (-a) 0 = -a := max_eq_left (by linarith)
    have hsx : x ^ 2 ≤ -4 * a := by
      have := sq_le_of_mem_Icc (winS0 a) x (by linarith [winS0_nonneg a]) (by linarith [hx.2])
      rw [e, hmax] at this
      linarith
    have hsy : y ^ 2 ≤ -4 * a := by
      have := sq_le_of_mem_Icc (winS0 a) y (by linarith [winS0_nonneg a]) hyS
      rw [e, hmax] at this
      linarith
    rw [abs_phi_near a x ha hsx, abs_phi_near a y ha hsy]
    have := sq_mono_pos x y hx0 hxy
    linarith
  · have hs0 := winS0_zero_of_pos ha
    rw [hs0] at hyS
    have hx0' : x = 0 := by linarith [hx.2]
    have hy0' : y = 0 := by linarith
    rw [hx0', hy0']

/-- `Mbal^2` is nonincreasing on `[s0, ∞)`. -/
lemma mbal_sq_anti_right (a : ℝ) : AntitoneOn (fun z => Mbal a z ^ 2) (Set.Ici (winS0 a)) := by
  intro x hx y hy hxy
  have hxs : winS0 a ≤ x := hx
  have hs := winS0_nonneg a
  have e := winS0_sq a
  have fx := far_sq (winS0 a) x hs (Or.inr hxs)
  have fy := far_sq (winS0 a) y hs (Or.inr (by linarith))
  show Mbal a y ^ 2 ≤ Mbal a x ^ 2
  refine mbal_sq_le_of_k2 a y x ?_
  apply k2_le_of_phi
  rw [abs_phi_far a x (by linarith), abs_phi_far a y (by linarith)]
  have := sq_mono_pos x y (by linarith) hxy
  linarith

/-- `Mbal^2` is nonincreasing on `[0, ∞)`-side turning points; the four pieces give the shape of `decomp_monotone`. -/
lemma mbal_sq_mono_right (a : ℝ) : MonotoneOn (fun z => Mbal a z ^ 2) (Set.Icc 0 (winS0 a)) :=
  mbal_sq_mono_mid a

/-- The window weight `Mbal^2` is the difference of two monotone functions (`f1 ∈ [0,3]`, `f2 ∈ [0,2]`). -/
lemma mbal_sq_shape (a : ℝ) : ∃ f1 f2 : ℝ → ℝ, Monotone f1 ∧ Monotone f2 ∧
    (∀ z, Mbal a z ^ 2 = f1 z - f2 z) ∧ (∀ z, 0 ≤ f2 z ∧ f2 z ≤ 2) ∧ (∀ z, 0 ≤ f1 z ∧ f1 z ≤ 3) :=
  decomp_monotone (fun z => Mbal a z ^ 2) (winS0 a) (winS0_nonneg a)
    (mbal_sq_mono_left a) (mbal_sq_anti_mid a) (mbal_sq_mono_right a) (mbal_sq_anti_right a)
    (fun z => sq_nonneg _) (fun z => mbal_sq_le_one a z)

end WinWeight

/-! ### Integral bounds for the window weight -/

section WinIntegral

lemma mbal_sq_ii (a u v : ℝ) : IntervalIntegrable (fun z => Mbal a z ^ 2) MeasureTheory.volume u v := by
  obtain ⟨f1, f2, hf1, hf2, hs, -, -⟩ := mbal_sq_shape a
  have e : (fun z => Mbal a z ^ 2) = fun z => f1 z - f2 z := funext hs
  rw [e]
  exact (Monotone.intervalIntegrable hf1).sub (Monotone.intervalIntegrable hf2)

lemma mbal_sq_eq' (a z : ℝ) : Mbal a z ^ 2 = (Real.sqrt (k2 a z))⁻¹ := by
  have hk : 0 ≤ k2 a z := le_trans zero_le_one (win_k2_ge_one a z)
  rw [mbal_sq_eq, show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg hk, Real.sqrt_eq_rpow]

lemma rpow_third_le (x : ℝ) (hx : 1 ≤ x) : x ^ ((1 : ℝ) / 3) ≤ x := by
  have := Real.rpow_le_rpow_of_exponent_le hx (show (1 : ℝ) / 3 ≤ 1 by norm_num)
  rwa [Real.rpow_one] at this

/-- pointwise comparison with the singular majorant `2 / (sqrt s0 sqrt(s0 - z))` on `[0, s0)`, `a <= 0`. -/
lemma mbal_sq_le_psi (a z : ℝ) (ha : a ≤ 0) (hz0 : 0 ≤ z) (hzs : z < winS0 a) :
    Mbal a z ^ 2 ≤ 2 / (Real.sqrt (winS0 a) * Real.sqrt (winS0 a - z)) := by
  have hs0 : 0 ≤ winS0 a := winS0_nonneg a
  have e := winS0_sq a
  have hmax : max (-a) 0 = -a := max_eq_left (by linarith)
  have hsq : winS0 a ^ 2 = -4 * a := by rw [e, hmax]; ring
  have hspos : 0 < winS0 a := by linarith
  have ht : 0 < winS0 a - z := by linarith
  have hz2 : z ^ 2 ≤ -4 * a := by nlinarith
  have hphi := abs_phi_near a z ha hz2
  have hK1 : |z ^ 2 / 4 + a| ≤ k2 a z := by
    unfold k2; exact le_max_left _ _
  have hKge : -a - z ^ 2 / 4 ≤ k2 a z := by linarith [hK1, hphi]
  have hKpos : 0 < k2 a z := by nlinarith
  rw [mbal_sq_eq']
  have hsa : 0 < Real.sqrt (winS0 a) := Real.sqrt_pos.mpr hspos
  have hsb : 0 < Real.sqrt (winS0 a - z) := Real.sqrt_pos.mpr ht
  have hK0 : 0 < Real.sqrt (k2 a z) := Real.sqrt_pos.mpr hKpos
  have h1 : (Real.sqrt (winS0 a) * Real.sqrt (winS0 a - z)) ^ 2 = winS0 a * (winS0 a - z) := by
    rw [mul_pow, Real.sq_sqrt hs0, Real.sq_sqrt ht.le]
  have h2 : (2 * Real.sqrt (k2 a z)) ^ 2 = 4 * k2 a z := by
    rw [mul_pow, Real.sq_sqrt hKpos.le]; norm_num
  have key : Real.sqrt (winS0 a) * Real.sqrt (winS0 a - z) ≤ 2 * Real.sqrt (k2 a z) := by
    rw [← sq_le_sq₀ (by positivity) (by positivity), h1, h2]
    nlinarith [mul_nonneg ht.le hz0]
  rw [inv_eq_one_div, div_le_div_iff₀ hK0 (mul_pos hsa hsb)]
  linarith

/-- the singular integral: `∫_0^{s0} Mbal^2 <= 4` when `s0 >= 4` (`a <= 0`). -/
lemma mbal_sq_int_upper (a : ℝ) (ha : a ≤ 0) (hs4 : 4 ≤ winS0 a) :
    ∫ z in (0 : ℝ)..winS0 a, Mbal a z ^ 2 ≤ 4 := by
  have hs0pos : 0 < winS0 a := by linarith
  set s0 := winS0 a with hs0def
  set σ := Real.sqrt s0 with hσ
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hs0pos
  have hσsq : σ ^ 2 = s0 := Real.sq_sqrt hs0pos.le
  set θ := (4 / σ) ^ 2 with hθ
  have hθpos : 0 < θ := by positivity
  have hθs : θ * s0 = 16 := by
    rw [hθ, div_pow, ← hσsq]
    field_simp
    norm_num
  have hθle : θ ≤ s0 := by nlinarith
  set b := s0 - θ with hbdef
  have hb0 : 0 ≤ b := by linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (mbal_sq_ii a 0 b) (mbal_sq_ii a b s0)
  -- top piece
  have htop : ∫ z in b..s0, Mbal a z ^ 2 ≤ θ := by
    have h := intervalIntegral.integral_mono_on (show b ≤ s0 by linarith) (mbal_sq_ii a b s0)
      (intervalIntegrable_const (c := (1 : ℝ))) (fun x _ => mbal_sq_le_one a x)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
    linarith
  -- bottom piece: the singular majorant has the explicit primitive `-4 sqrt(s0 - z) / sigma`
  have hderiv : ∀ x ∈ Set.uIcc 0 b, HasDerivAt (fun z => -4 * Real.sqrt (s0 - z) / σ)
      (2 / (σ * Real.sqrt (s0 - x))) x := by
    intro x hx
    rw [Set.uIcc_of_le hb0] at hx
    have hpos : 0 < s0 - x := by linarith [hx.2]
    have h1 : HasDerivAt (fun z => s0 - z) (-1) x := by
      simpa using (hasDerivAt_id' x).const_sub s0
    have h2 := ((h1.sqrt hpos.ne').const_mul (-4)).div_const σ
    convert h2 using 1
    field_simp
    ring
  have hc : ContinuousOn (fun z => 2 / (σ * Real.sqrt (s0 - z))) (Set.uIcc 0 b) := by
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_const.mul (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousOn
    · intro x hx
      rw [Set.uIcc_of_le hb0] at hx
      have hpos : 0 < s0 - x := by linarith [hx.2]
      exact mul_ne_zero hσpos.ne' (Real.sqrt_pos.mpr hpos).ne'
  have hint := hc.intervalIntegrable (μ := MeasureTheory.volume)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hval : (-4 * Real.sqrt (s0 - b) / σ) - (-4 * Real.sqrt (s0 - 0) / σ) = 4 - θ := by
    have e1 : s0 - b = (4 / σ) ^ 2 := by rw [hbdef]; ring
    rw [e1, Real.sqrt_sq (by positivity), sub_zero, ← hσ, hθ]
    field_simp
    ring
  have hbot : ∫ z in (0 : ℝ)..b, Mbal a z ^ 2 ≤ 4 - θ := by
    have h := intervalIntegral.integral_mono_on hb0 (mbal_sq_ii a 0 b) hint
      (fun x hx => mbal_sq_le_psi a x ha hx.1 (by linarith [hx.2]))
    linarith
  linarith

end WinIntegral

/-! ### The total window mass: `∫_{-ρ}^{ρ} Mbal^2` is bounded above and below uniformly -/

section WinMass

lemma rhoWin_eq (a : ℝ) : rhoWin a = winS0 a + (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) := by
  unfold rhoWin winS0; ring

lemma ell_nonneg' (a : ℝ) : 0 ≤ (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) := by positivity

lemma ell_pow6 (A : ℝ) (hA : 0 ≤ A) : ((1 + A) ^ (-(1 : ℝ) / 6)) ^ 6 = (1 + A)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num [Real.rpow_neg_one]

lemma rhoWin_ge_half (a : ℝ) : 1 / 2 ≤ rhoWin a := by
  rw [rhoWin_eq]
  have hs0 := winS0_nonneg a
  rcases le_or_gt 1 (max (-a) 0) with hA | hA
  · have h1 : 1 ≤ Real.sqrt (max (-a) 0) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hA
    have : (2 : ℝ) ≤ winS0 a := by unfold winS0; linarith
    linarith [ell_nonneg' a]
  · have h6 := ell_pow6 (max (-a) 0) (le_max_right _ _)
    have hA2 : 1 + max (-a) 0 < 2 := by linarith
    have hinv : (1 / 2 : ℝ) < (1 + max (-a) 0)⁻¹ := by
      rw [← one_div]
      exact (one_div_lt_one_div (by norm_num) (by linarith [le_max_right (-a) 0])).mpr hA2
    by_contra hc
    push_neg at hc
    have hℓlt : (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) < 1 / 2 := by linarith
    have hpos := ell_nonneg' a
    have hpow : ((1 + max (-a) 0) ^ (-(1 : ℝ) / 6)) ^ 6 < (1 / 2) ^ 6 :=
      pow_lt_pow_left₀ hℓlt hpos (by norm_num)
    rw [h6] at hpow
    norm_num at hpow
    linarith

/-- the window mass is at most `10`, uniformly in `a`. -/
lemma mbal_sq_int_upper_all (a : ℝ) : ∫ z in (-rhoWin a)..(rhoWin a), Mbal a z ^ 2 ≤ 10 := by
  have hs0 := winS0_nonneg a
  have hℓ1 : (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) ≤ 1 := ell_le_one _ (le_max_right _ _)
  have hℓ0 := ell_nonneg' a
  have hρ := rhoWin_eq a
  have hI0 : ∫ z in (0 : ℝ)..winS0 a, Mbal a z ^ 2 ≤ 4 := by
    rcases le_or_gt (winS0 a) 4 with h4 | h4
    · have h := intervalIntegral.integral_mono_on hs0 (mbal_sq_ii a 0 (winS0 a))
        (intervalIntegrable_const (c := (1 : ℝ))) (fun x _ => mbal_sq_le_one a x)
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at h
      linarith
    · have ha : a ≤ 0 := by
        by_contra hc
        push_neg at hc
        have := winS0_zero_of_pos hc
        linarith
      exact mbal_sq_int_upper a ha h4.le
  have hI1 : ∫ z in winS0 a..rhoWin a, Mbal a z ^ 2 ≤ 1 := by
    have h := intervalIntegral.integral_mono_on (show winS0 a ≤ rhoWin a by linarith)
      (mbal_sq_ii a (winS0 a) (rhoWin a)) (intervalIntegrable_const (c := (1 : ℝ)))
      (fun x _ => mbal_sq_le_one a x)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
    linarith
  have hev : ∫ z in (-rhoWin a)..0, Mbal a z ^ 2 = ∫ z in (0 : ℝ)..rhoWin a, Mbal a z ^ 2 := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := rhoWin a)
      (f := fun z => Mbal a z ^ 2)
    simp only [Mbal_neg, neg_zero] at h
    exact h.symm
  have hsplitA := intervalIntegral.integral_add_adjacent_intervals
    (mbal_sq_ii a (-rhoWin a) 0) (mbal_sq_ii a 0 (rhoWin a))
  have hsplitB := intervalIntegral.integral_add_adjacent_intervals
    (mbal_sq_ii a 0 (winS0 a)) (mbal_sq_ii a (winS0 a) (rhoWin a))
  linarith

/-- the window mass is at least `1 / (2 max(1, aplus))`, uniformly for `a <= aplus`. -/
lemma mbal_sq_int_lower (a aplus : ℝ) (haplus : a ≤ aplus) :
    1 / (2 * max 1 aplus) ≤ ∫ z in (-rhoWin a)..(rhoWin a), Mbal a z ^ 2 := by
  have hM1 : 1 ≤ max 1 aplus := le_max_left _ _
  have hMa : aplus ≤ max 1 aplus := le_max_right _ _
  have hρh := rhoWin_ge_half a
  have hg0 : ∀ z, 0 ≤ Mbal a z ^ 2 := fun z => sq_nonneg _
  have hsub : ∀ r : ℝ, 0 ≤ r → r ≤ rhoWin a →
      ∫ z in (-r)..r, Mbal a z ^ 2 ≤ ∫ z in (-rhoWin a)..(rhoWin a), Mbal a z ^ 2 := by
    intro r hr hrρ
    exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall hg0) (mbal_sq_ii a _ _)
  rcases lt_or_ge (max (-a) 0) 1 with hA | hA
  · -- case A < 1: the window contains [-1/2, 1/2] and the weight is bounded below there
    have ha1 : -1 < a := by have := le_max_left (-a) 0; linarith
    have hpt : ∀ z ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), 1 / (2 * max 1 aplus) ≤ Mbal a z ^ 2 := by
      intro z hz
      have hz2 : z ^ 2 ≤ 1 / 4 := by nlinarith [hz.1, hz.2]
      have hz0 : 0 ≤ z ^ 2 := sq_nonneg z
      have habs : |a| ≤ max 1 aplus := abs_le.mpr ⟨by linarith, by linarith⟩
      have hk : k2 a z ≤ 4 * (max 1 aplus) ^ 2 := by
        unfold k2
        apply max_le
        · have hb : |z ^ 2 / 4 + a| ≤ max 1 aplus + 1 / 16 :=
            abs_le.mpr ⟨by linarith, by linarith⟩
          nlinarith
        · have h1 : max |a| 1 ≤ max 1 aplus := max_le habs hM1
          have h2 := rpow_third_le (max |a| 1) (le_max_right _ _)
          nlinarith
      have hkpos : 0 < k2 a z := lt_of_lt_of_le one_pos (win_k2_ge_one a z)
      have hsq : Real.sqrt (k2 a z) ≤ 2 * max 1 aplus := by
        rw [show 2 * max 1 aplus = Real.sqrt ((2 * max 1 aplus) ^ 2) from
          (Real.sqrt_sq (by positivity)).symm]
        exact Real.sqrt_le_sqrt (by nlinarith)
      have hspos : 0 < Real.sqrt (k2 a z) := Real.sqrt_pos.mpr hkpos
      rw [mbal_sq_eq']
      simp only [inv_eq_one_div]
      exact one_div_le_one_div_of_le hspos hsq
    have hI := intervalIntegral.integral_mono_on (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)
      (intervalIntegrable_const (c := 1 / (2 * max 1 aplus))) (mbal_sq_ii a _ _) hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at hI
    have hlen : (1 / 2 : ℝ) - -(1 / 2) = 1 := by norm_num
    rw [hlen, one_mul] at hI
    have := hsub (1 / 2) (by norm_num) (by linarith)
    linarith
  · -- case A >= 1: the weight is at least `r⁻¹` on `[-r, r]`, `r = sqrt A`
    have hna : 0 ≤ -a := by
      by_contra hc
      have h0 : max (-a) 0 = 0 := max_eq_right (le_of_lt (not_le.mp hc))
      linarith
    have hA' : max (-a) 0 = -a := max_eq_left hna
    have hr2 : Real.sqrt (max (-a) 0) ^ 2 = -a := by rw [Real.sq_sqrt (le_max_right _ _), hA']
    have hr1 : 1 ≤ Real.sqrt (max (-a) 0) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hA
    have hrρ : Real.sqrt (max (-a) 0) ≤ rhoWin a := by
      rw [rhoWin_eq]; unfold winS0; linarith [ell_nonneg' a, Real.sqrt_nonneg (max (-a) 0)]
    have hpt : ∀ z ∈ Set.Icc (-Real.sqrt (max (-a) 0)) (Real.sqrt (max (-a) 0)),
        (Real.sqrt (max (-a) 0))⁻¹ ≤ Mbal a z ^ 2 := by
      intro z hz
      have hz2 : z ^ 2 ≤ -a := by
        have := sq_le_sq' hz.1 hz.2
        linarith
      have hk : k2 a z ≤ Real.sqrt (max (-a) 0) ^ 2 := by
        rw [hr2]
        unfold k2
        apply max_le
        · have : |z ^ 2 / 4 + a| ≤ -a := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
          linarith
        · have habs : |a| = -a := abs_of_nonpos (by linarith)
          rw [habs, max_eq_left (by linarith : (1 : ℝ) ≤ -a)]
          have h2 := rpow_third_le (-a) (by linarith)
          linarith
      have hkpos : 0 < k2 a z := lt_of_lt_of_le one_pos (win_k2_ge_one a z)
      have hspos : 0 < Real.sqrt (k2 a z) := Real.sqrt_pos.mpr hkpos
      have hr0 : 0 < Real.sqrt (max (-a) 0) := by linarith
      have hsq : Real.sqrt (k2 a z) ≤ Real.sqrt (max (-a) 0) := by
        rw [← Real.sqrt_sq hr0.le]
        exact Real.sqrt_le_sqrt (by rw [Real.sq_sqrt (le_max_right _ _)]; linarith)
      rw [mbal_sq_eq']
      simp only [inv_eq_one_div]
      exact one_div_le_one_div_of_le hspos hsq
    have hr0 : 0 < Real.sqrt (max (-a) 0) := by linarith
    have hI := intervalIntegral.integral_mono_on (by linarith : -Real.sqrt (max (-a) 0) ≤ Real.sqrt (max (-a) 0))
      (intervalIntegrable_const (c := (Real.sqrt (max (-a) 0))⁻¹)) (mbal_sq_ii a _ _) hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at hI
    have hval : (Real.sqrt (max (-a) 0) - -Real.sqrt (max (-a) 0)) * (Real.sqrt (max (-a) 0))⁻¹ = 2 := by
      field_simp
      ring
    rw [hval] at hI
    have := hsub (Real.sqrt (max (-a) 0)) hr0.le hrρ
    have hc : 1 / (2 * max 1 aplus) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith

end WinMass

/-! ### Lattice sums over a block of rows -/

section WinBlock

lemma sum_cells_upper {g f1 f2 : ℝ → ℝ} (hf1 : Monotone f1) (hf2 : Monotone f2)
    (hsplit : ∀ z, g z = f1 z - f2 z) (hb2 : ∀ z, 0 ≤ f2 z ∧ f2 z ≤ 2)
    (Z : ℕ → ℝ) (hZ : ∀ i, Z i ≤ Z (i + 1)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hstep : ∀ i, Z (i + 1) - Z i ≤ δ) (K : ℕ) :
    ∑ i ∈ Finset.range K, g (Z i) * (Z (i + 1) - Z i) ≤ (∫ x in Z 0..Z K, g x) + 2 * δ := by
  have A := (riemann_lattice hf1 Z hZ δ hδ hstep K).2
  have B := (riemann_lattice hf2 Z hZ δ hδ hstep K).1
  have hsum : ∑ i ∈ Finset.range K, g (Z i) * (Z (i + 1) - Z i) =
      ∑ i ∈ Finset.range K, f1 (Z i) * (Z (i + 1) - Z i) -
        ∑ i ∈ Finset.range K, f2 (Z i) * (Z (i + 1) - Z i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hsplit]; ring)
  have hint : (∫ x in Z 0..Z K, g x) = (∫ x in Z 0..Z K, f1 x) - ∫ x in Z 0..Z K, f2 x := by
    rw [← intervalIntegral.integral_sub (Monotone.intervalIntegrable (μ := MeasureTheory.volume) hf1)
      (Monotone.intervalIntegrable (μ := MeasureTheory.volume) hf2)]
    exact intervalIntegral.integral_congr (fun x _ => hsplit x)
  have hδ2 : δ * (f2 (Z K) - f2 (Z 0)) ≤ 2 * δ := by
    nlinarith [hb2 (Z K), hb2 (Z 0)]
  nlinarith [A, B, hsum, hint, hδ2]

lemma sum_cells_lower {g f1 f2 : ℝ → ℝ} (hf1 : Monotone f1) (hf2 : Monotone f2)
    (hsplit : ∀ z, g z = f1 z - f2 z) (hb1 : ∀ z, 0 ≤ f1 z ∧ f1 z ≤ 3)
    (Z : ℕ → ℝ) (hZ : ∀ i, Z i ≤ Z (i + 1)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hstep : ∀ i, Z (i + 1) - Z i ≤ δ) (K : ℕ) :
    (∫ x in Z 0..Z K, g x) - 3 * δ ≤ ∑ i ∈ Finset.range K, g (Z i) * (Z (i + 1) - Z i) := by
  have A := (riemann_lattice hf1 Z hZ δ hδ hstep K).1
  have B := (riemann_lattice hf2 Z hZ δ hδ hstep K).2
  have hsum : ∑ i ∈ Finset.range K, g (Z i) * (Z (i + 1) - Z i) =
      ∑ i ∈ Finset.range K, f1 (Z i) * (Z (i + 1) - Z i) -
        ∑ i ∈ Finset.range K, f2 (Z i) * (Z (i + 1) - Z i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hsplit]; ring)
  have hint : (∫ x in Z 0..Z K, g x) = (∫ x in Z 0..Z K, f1 x) - ∫ x in Z 0..Z K, f2 x := by
    rw [← intervalIntegral.integral_sub (Monotone.intervalIntegrable (μ := MeasureTheory.volume) hf1)
      (Monotone.intervalIntegrable (μ := MeasureTheory.volume) hf2)]
    exact intervalIntegral.integral_congr (fun x _ => hsplit x)
  have hδ3 : δ * (f1 (Z K) - f1 (Z 0)) ≤ 3 * δ := by
    nlinarith [hb1 (Z K), hb1 (Z 0)]
  nlinarith [A, B, hsum, hint, hδ3]

/-- the window sum over a block of consecutive rows is a sum over `range` -/
lemma sum_Icc_range (F : ℤ → ℝ) (na : ℤ) (K : ℕ) :
    ∑ n ∈ Finset.Icc na (na + K), F n = ∑ i ∈ Finset.range (K + 1), F (na + i) := by
  rw [← Finset.sum_image (f := F) (g := fun i : ℕ => na + (i : ℤ))]
  · congr 1
    ext n
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      have h := Int.toNat_of_nonneg (show 0 ≤ n - na by omega)
      refine ⟨(n - na).toNat, ?_, ?_⟩
      · omega
      · omega
    · rintro ⟨i, hi, hin⟩
      omega
  · intro x _ y _ hxy
    simpa using hxy

/-- The window sums over a block of rows `na..nb` with spacing in `[dm s, dp s]` (`s = sqrt h`):
upper and lower bounds in terms of the window mass `J = ∫_{-rho}^{rho} g`. -/
lemma window_block_bounds {g : ℝ → ℝ} (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1)
    (f1 f2 : ℝ → ℝ) (hf1 : Monotone f1) (hf2 : Monotone f2) (hsplit : ∀ z, g z = f1 z - f2 z)
    (hb1 : ∀ z, 0 ≤ f1 z ∧ f1 z ≤ 3) (hb2 : ∀ z, 0 ≤ f2 z ∧ f2 z ≤ 2)
    (ρ dm dp s : ℝ) (hdm : 0 < dm) (hdp : dm ≤ dp) (hs : 0 < s)
    (Z : ℤ → ℝ) (na nb : ℤ) (hnb : na ≤ nb)
    (hsp : ∀ n, na ≤ n → n < nb → dm * s ≤ Z (n + 1) - Z n ∧ Z (n + 1) - Z n ≤ dp * s)
    (hblock : ∀ n, na ≤ n → n ≤ nb → -ρ ≤ Z n ∧ Z n ≤ ρ)
    (hna : Z na < -ρ + dp * s) (hnb' : ρ - dp * s < Z nb) :
    (∑ n ∈ Finset.Icc na nb, g (Z n)) ≤ ((∫ z in (-ρ)..ρ, g z) + 2 * (dp * s)) / (dm * s) + 1 ∧
    ((∫ z in (-ρ)..ρ, g z) - 5 * (dp * s)) / (dp * s) ≤ ∑ n ∈ Finset.Icc na nb, g (Z n) := by
  obtain ⟨K, hK⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ nb - na by omega)
  have hnb_eq : nb = na + K := by omega
  have hgi : ∀ u v : ℝ, IntervalIntegrable g MeasureTheory.volume u v := by
    intro u v
    have e : g = fun z => f1 z - f2 z := funext hsplit
    rw [e]
    exact (Monotone.intervalIntegrable (μ := MeasureTheory.volume) hf1).sub
      (Monotone.intervalIntegrable (μ := MeasureTheory.volume) hf2)
  have hdps : 0 < dp * s := by nlinarith
  have hdms : 0 < dm * s := by nlinarith
  -- the sum over the block, as a sum over `range K` plus the top row
  have hT : ∑ n ∈ Finset.Icc na nb, g (Z n) = ∑ i ∈ Finset.range K, g (Z (na + i)) + g (Z nb) := by
    rw [hnb_eq, sum_Icc_range (fun n => g (Z n)) na K, Finset.sum_range_succ]
  -- clamped row sequence, so that the lattice lemmas apply on all of `ℕ`
  set Zc : ℕ → ℝ := fun i => Z (na + ((min i K : ℕ) : ℤ)) with hZc
  have hZc_eq : ∀ i, i ≤ K → Zc i = Z (na + i) := by
    intro i hi; simp only [hZc]; rw [min_eq_left hi]
  have hZc_zero : Zc 0 = Z na := by simp [hZc]
  have hZc_K : Zc K = Z nb := by rw [hZc_eq K le_rfl, hnb_eq]
  have hZc_step_block : ∀ i, i < K → dm * s ≤ Zc (i + 1) - Zc i ∧ Zc (i + 1) - Zc i ≤ dp * s := by
    intro i hi
    rw [hZc_eq i hi.le, hZc_eq (i + 1) hi]
    have e : na + ((i + 1 : ℕ) : ℤ) = na + (i : ℤ) + 1 := by push_cast; ring
    rw [e]
    exact hsp (na + i) (by omega) (by omega)
  have hZc_mono : ∀ i, Zc i ≤ Zc (i + 1) := by
    intro i
    by_cases hi : i < K
    · have := (hZc_step_block i hi).1
      linarith
    · have h1 : Zc i = Z (na + K) := by
        simp only [hZc]; rw [min_eq_right (by omega)]
      have h2 : Zc (i + 1) = Z (na + K) := by
        simp only [hZc]; rw [min_eq_right (by omega)]
      rw [h1, h2]
  have hZc_step : ∀ i, Zc (i + 1) - Zc i ≤ dp * s := by
    intro i
    by_cases hi : i < K
    · exact (hZc_step_block i hi).2
    · have h1 : Zc i = Z (na + K) := by
        simp only [hZc]; rw [min_eq_right (by omega)]
      have h2 : Zc (i + 1) = Z (na + K) := by
        simp only [hZc]; rw [min_eq_right (by omega)]
      rw [h1, h2]; linarith
  have hZc_mono' : Monotone Zc := monotone_nat_of_le_succ hZc_mono
  have hZa : -ρ ≤ Zc 0 := by rw [hZc_zero]; exact (hblock na le_rfl (by omega)).1
  have hZb : Zc K ≤ ρ := by rw [hZc_K]; exact (hblock nb (by omega) le_rfl).2
  have hZab : Zc 0 ≤ Zc K := hZc_mono' (Nat.zero_le K)
  have hint_le : (∫ z in Zc 0..Zc K, g z) ≤ ∫ z in (-ρ)..ρ, g z :=
    intervalIntegral.integral_mono_interval hZa hZab hZb (Filter.Eventually.of_forall hg0) (hgi _ _)
  -- the two boundary pieces of the window mass
  have hbot : (∫ z in (-ρ)..Zc 0, g z) ≤ Zc 0 + ρ := by
    have h := intervalIntegral.integral_mono_on hZa (hgi _ _) (intervalIntegrable_const (c := (1 : ℝ)))
      (fun x _ => hg1 x)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
    linarith
  have htop : (∫ z in Zc K..ρ, g z) ≤ ρ - Zc K := by
    have h := intervalIntegral.integral_mono_on hZb (hgi _ _) (intervalIntegrable_const (c := (1 : ℝ)))
      (fun x _ => hg1 x)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
    linarith
  have hsplitL := intervalIntegral.integral_add_adjacent_intervals (hgi (-ρ) (Zc 0)) (hgi (Zc 0) (Zc K))
  have hsplitR := intervalIntegral.integral_add_adjacent_intervals (hgi (-ρ) (Zc K)) (hgi (Zc K) ρ)
  -- the Riemann sums over the cells
  have hU := sum_cells_upper hf1 hf2 hsplit hb2 Zc hZc_mono (dp * s) hdps.le hZc_step K
  have hL := sum_cells_lower hf1 hf2 hsplit hb1 Zc hZc_mono (dp * s) hdps.le hZc_step K
  have hTc : ∑ i ∈ Finset.range K, g (Z (na + i)) = ∑ i ∈ Finset.range K, g (Zc i) :=
    Finset.sum_congr rfl (fun i hi => by rw [hZc_eq i (Finset.mem_range.mp hi).le])
  have hup_term : ∑ i ∈ Finset.range K, g (Zc i) ≤
      (∑ i ∈ Finset.range K, g (Zc i) * (Zc (i + 1) - Zc i)) / (dm * s) := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    have hc := (hZc_step_block i (Finset.mem_range.mp hi)).1
    rw [le_div_iff₀ hdms]
    exact mul_le_mul_of_nonneg_left hc (hg0 _)
  have hlo_term : (∑ i ∈ Finset.range K, g (Zc i) * (Zc (i + 1) - Zc i)) / (dp * s) ≤
      ∑ i ∈ Finset.range K, g (Zc i) := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    have hc := (hZc_step_block i (Finset.mem_range.mp hi)).2
    rw [div_le_iff₀ hdps]
    exact mul_le_mul_of_nonneg_left hc (hg0 _)
  simp only [hZc_zero, hZc_K] at hbot hsplitL htop hsplitR hU hL hint_le
  constructor
  · -- upper bound
    have hT1 : ∑ i ∈ Finset.range K, g (Zc i) ≤ ((∫ z in (-ρ)..ρ, g z) + 2 * (dp * s)) / (dm * s) := by
      refine hup_term.trans ?_
      rw [div_le_div_iff_of_pos_right hdms]
      linarith
    rw [hT, hTc]
    linarith [hg1 (Z nb)]
  · -- lower bound
    have hJ : (∫ z in Z na..Z nb, g z) ≥ (∫ z in (-ρ)..ρ, g z) - 2 * (dp * s) := by
      linarith
    have hT2 : ((∫ z in (-ρ)..ρ, g z) - 5 * (dp * s)) / (dp * s) ≤
        ((∫ z in Z na..Z nb, g z) - 3 * (dp * s)) / (dp * s) := by
      rw [div_le_div_iff_of_pos_right hdps]
      linarith
    have hT3 : ((∫ z in Z na..Z nb, g z) - 3 * (dp * s)) / (dp * s) ≤
        ∑ i ∈ Finset.range K, g (Zc i) := by
      refine le_trans ?_ hlo_term
      rw [div_le_div_iff_of_pos_right hdps]
      linarith
    rw [hT, hTc]
    linarith [hg0 (Z nb)]

end WinBlock

/-! ### The collar window is a block of rows; the window sums (conjunct (5)) -/

section WinBlockChart

lemma int_chain_mono {Z : ℤ → ℝ} {a b : ℤ} (h : ∀ n, a ≤ n → n < b → Z n ≤ Z (n + 1)) (n : ℤ)
    (hn : a ≤ n) : ∀ m : ℤ, n ≤ m → m ≤ b → Z n ≤ Z m := by
  have key : ∀ k : ℕ, n + (k : ℤ) ≤ b → Z n ≤ Z (n + (k : ℤ)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by push_cast at hk; omega)
      have h2 := h (n + (k : ℤ)) (by omega) (by push_cast at hk; omega)
      have e : n + ((k + 1 : ℕ) : ℤ) = n + (k : ℤ) + 1 := by push_cast; ring
      rw [e]
      linarith
  intro m hnm hmb
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ m - n by omega)
  have e : m = n + (k : ℤ) := by omega
  rw [e]
  exact key k (by omega)

lemma rpow_neg_half (x : ℝ) (hx : 0 ≤ x) : x ^ (-(1 : ℝ) / 2) = (Real.sqrt x)⁻¹ := by
  rw [show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg hx, Real.sqrt_eq_rpow]

/-- The window sums from abstract row data: the window `{n in [0,N] : |Z_n| <= rho}` is the block
of rows in the collar whose `Z` lies in `[-rho, rho]`; its sum is bounded above (under the far-field
hypothesis `hfar`) and below. -/
lemma win_block_abstract (g : ℝ → ℝ) (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1)
    (f1 f2 : ℝ → ℝ) (hf1 : Monotone f1) (hf2 : Monotone f2) (hsplit : ∀ z, g z = f1 z - f2 z)
    (hb1 : ∀ z, 0 ≤ f1 z ∧ f1 z ≤ 3) (hb2 : ∀ z, 0 ≤ f2 z ∧ f2 z ≤ 2)
    (N : ℕ) (h η uc L ρ dm dp : ℝ) (hh : 0 < h) (hηpos : 0 < η) (hdm : 0 < dm) (hdmp : dm ≤ dp)
    (hLh : h * ((N : ℝ) + 1) = L) (huc1 : 2 * η < uc) (huc2 : uc + 2 * η < L) (hηh : h ≤ η)
    (hsm : dp * Real.sqrt h ≤ 1 / 20) (hρ : 1 / 2 ≤ ρ)
    (Z u : ℤ → ℝ) (hu : ∀ n : ℤ, u n = ((n : ℝ) + 1 / 2) * h)
    (hspc : ∀ n : ℤ, |u n - uc| ≤ 2 * η → |u (n + 1) - uc| ≤ 2 * η →
      dm * Real.sqrt h ≤ Z (n + 1) - Z n ∧ Z (n + 1) - Z n ≤ dp * Real.sqrt h)
    (hcol : ∀ n : ℤ, |u n - uc| ≤ 2 * η → |Z n| ≤ ρ → |u n - uc| < η / 4)
    (J2 : ℤ) (hJ2a : 0 ≤ J2) (hJ2b : J2 + 1 ≤ (N : ℤ)) (hJ2c : |u J2 - uc| ≤ 2 * η)
    (hJ2d : |u (J2 + 1) - uc| ≤ 2 * η) (hJ2e : Z J2 ≤ 0) (hJ2f : 0 < Z (J2 + 1))
    (hfar : ∀ n : ℤ, 0 ≤ n → n ≤ (N : ℤ) → 2 * η < |u n - uc| → ρ < |Z n|) :
    (∑ n ∈ (Finset.Icc 0 (N : ℤ)).filter (fun n => |Z n| ≤ ρ), g (Z n)) ≤
        ((∫ z in (-ρ)..ρ, g z) + 2 * (dp * Real.sqrt h)) / (dm * Real.sqrt h) + 1 ∧
      ((∫ z in (-ρ)..ρ, g z) - 5 * (dp * Real.sqrt h)) / (dp * Real.sqrt h) ≤
        ∑ n ∈ (Finset.Icc 0 (N : ℤ)).filter (fun n => |Z n| ≤ ρ), g (Z n) := by
  have hs0 : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hdp : 0 < dp := lt_of_lt_of_le hdm hdmp
  have hdps : 0 < dp * Real.sqrt h := mul_pos hdp hs0
  have hdms : 0 < dm * Real.sqrt h := mul_pos hdm hs0
  -- the collar rows of the window
  let Wc : Finset ℤ := (Finset.Icc 0 (N : ℤ)).filter (fun n => |u n - uc| ≤ 2 * η ∧ |Z n| ≤ ρ)
  have hmemWc : ∀ n, n ∈ Wc ↔ (0 ≤ n ∧ n ≤ (N : ℤ)) ∧ |u n - uc| ≤ 2 * η ∧ |Z n| ≤ ρ := by
    intro n; simp only [Wc, Finset.mem_filter, Finset.mem_Icc]
  have hJ2mem : J2 ∈ Wc := by
    rw [hmemWc]
    refine ⟨⟨hJ2a, by omega⟩, hJ2c, ?_⟩
    have hsp := (hspc J2 hJ2c hJ2d).2
    rw [abs_le]
    constructor <;> linarith
  have hne : Wc.Nonempty := ⟨J2, hJ2mem⟩
  obtain ⟨na, hna⟩ : ∃ n, n = Wc.min' hne := ⟨_, rfl⟩
  obtain ⟨nb, hnb⟩ : ∃ n, n = Wc.max' hne := ⟨_, rfl⟩
  have hna_mem : na ∈ Wc := by rw [hna]; exact Finset.min'_mem Wc hne
  have hnb_mem : nb ∈ Wc := by rw [hnb]; exact Finset.max'_mem Wc hne
  have hna_le : ∀ n ∈ Wc, na ≤ n := fun n hn => by rw [hna]; exact Finset.min'_le Wc n hn
  have hnb_ge : ∀ n ∈ Wc, n ≤ nb := fun n hn => by rw [hnb]; exact Finset.le_max' Wc n hn
  have hnab : na ≤ nb := le_trans (hna_le J2 hJ2mem) (hnb_ge J2 hJ2mem)
  rw [hmemWc] at hna_mem hnb_mem
  obtain ⟨⟨hna0, hnaN⟩, hnacol, hnaZ⟩ := hna_mem
  obtain ⟨⟨hnb0, hnbN⟩, hnbcol, hnbZ⟩ := hnb_mem
  have hna_str : |u na - uc| < η / 4 := hcol na hnacol hnaZ
  have hnb_str : |u nb - uc| < η / 4 := hcol nb hnbcol hnbZ
  -- the block lies in the collar
  have hblk : ∀ n : ℤ, na ≤ n → n ≤ nb → |u n - uc| < η / 4 := by
    intro n h1 h2
    have c1 : (na : ℝ) ≤ n := by exact_mod_cast h1
    have c2 : (n : ℝ) ≤ nb := by exact_mod_cast h2
    have e1 : u na ≤ u n := by rw [hu, hu]; nlinarith
    have e2 : u n ≤ u nb := by rw [hu, hu]; nlinarith
    obtain ⟨l1, l2⟩ := abs_lt.mp hna_str
    obtain ⟨r1, r2⟩ := abs_lt.mp hnb_str
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hblk2 : ∀ n : ℤ, na ≤ n → n ≤ nb → |u n - uc| ≤ 2 * η := fun n h1 h2 =>
    le_trans (hblk n h1 h2).le (by linarith)
  have hsp_blk : ∀ n : ℤ, na ≤ n → n < nb →
      dm * Real.sqrt h ≤ Z (n + 1) - Z n ∧ Z (n + 1) - Z n ≤ dp * Real.sqrt h :=
    fun n h1 h2 => hspc n (hblk2 n h1 (by omega)) (hblk2 (n + 1) (by omega) (by omega))
  have hZmono : ∀ n : ℤ, na ≤ n → n < nb → Z n ≤ Z (n + 1) := fun n h1 h2 => by
    linarith [(hsp_blk n h1 h2).1]
  have hZblk : ∀ n : ℤ, na ≤ n → n ≤ nb → -ρ ≤ Z n ∧ Z n ≤ ρ := fun n h1 h2 => by
    have l1 := int_chain_mono hZmono na le_rfl n h1 h2
    have l2 := int_chain_mono hZmono n h1 nb h2 le_rfl
    have za := abs_le.mp hnaZ
    have zb := abs_le.mp hnbZ
    exact ⟨by linarith [za.1], by linarith [zb.2]⟩
  -- boundary rows: the row below the block is left of the window, the row above is right of it
  have hna1 : 1 ≤ na := by
    by_contra hc
    have h0 : na = 0 := by omega
    have hu0 : u na = h / 2 := by rw [h0, hu]; push_cast; ring
    rw [hu0] at hna_str
    have := abs_lt.mp hna_str
    linarith [this.1, this.2]
  have hnb1N : nb + 1 ≤ (N : ℤ) := by
    by_contra hc
    have h0 : nb = (N : ℤ) := by omega
    have hunb : u nb = L - h / 2 := by
      rw [hu, h0]; push_cast; linear_combination hLh
    rw [hunb] at hnb_str
    have := abs_lt.mp hnb_str
    linarith [this.1, this.2]
  have hnt_col : |u (nb + 1) - uc| ≤ 2 * η := by
    have e : u (nb + 1) = u nb + h := by rw [hu, hu]; push_cast; ring
    rw [e]
    have := abs_lt.mp hnb_str
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]
  have hZt : ρ < |Z (nb + 1)| := by
    by_contra hc
    have hmem : nb + 1 ∈ Wc := (hmemWc _).2 ⟨⟨by omega, hnb1N⟩, hnt_col, not_lt.mp hc⟩
    have := hnb_ge (nb + 1) hmem
    omega
  have hsp_t := hspc nb (hblk2 nb hnab le_rfl) hnt_col
  have hZt' : ρ < Z (nb + 1) := by
    rcases lt_abs.mp hZt with h1 | h1
    · exact h1
    · linarith [(hZblk nb hnab le_rfl).1, hsp_t.1]
  have hnb' : ρ - dp * Real.sqrt h < Z nb := by linarith [hsp_t.2]
  have hna_col' : |u (na - 1) - uc| ≤ 2 * η := by
    have e : u (na - 1) = u na - h := by rw [hu, hu]; push_cast; ring
    rw [e]
    have := abs_lt.mp hna_str
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]
  have hZb : ρ < |Z (na - 1)| := by
    by_contra hc
    have hmem : na - 1 ∈ Wc := (hmemWc _).2 ⟨⟨by omega, by omega⟩, hna_col', not_lt.mp hc⟩
    have := hna_le (na - 1) hmem
    omega
  have hna_nb : na - 1 + 1 = na := by ring
  have hsp_b := hspc (na - 1) hna_col' (by rw [hna_nb]; exact hnacol)
  rw [hna_nb] at hsp_b
  have hZb' : Z (na - 1) < -ρ := by
    rcases lt_abs.mp hZb with h1 | h1
    · linarith [(hZblk na le_rfl hnab).2, hsp_b.1]
    · linarith
  have hna' : Z na < -ρ + dp * Real.sqrt h := by linarith [hsp_b.2]
  -- the window is exactly the block
  have hW : (Finset.Icc 0 (N : ℤ)).filter (fun n => |Z n| ≤ ρ) = Finset.Icc na nb := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h0, hN⟩, hZn⟩
      by_cases hc : |u n - uc| ≤ 2 * η
      · have hmem : n ∈ Wc := (hmemWc n).2 ⟨⟨h0, hN⟩, hc, hZn⟩
        exact ⟨hna_le n hmem, hnb_ge n hmem⟩
      · exfalso
        have := hfar n h0 hN (not_le.mp hc)
        exact absurd hZn (not_le.mpr this)
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by omega, by omega⟩, abs_le.mpr (hZblk n h1 h2)⟩
  rw [hW]
  exact window_block_bounds hg0 hg1 f1 f2 hf1 hf2 hsplit hb1 hb2 ρ dm dp (Real.sqrt h) hdm hdmp hs0
    Z na nb hnab hsp_blk hZblk hna' hnb'

end WinBlockChart

/-! ### The chart-level window sums and the assembly of `PropThaWin` -/

section WinAssembly

variable {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ}
  {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}

lemma winH1_pos (CL : SoftEdgeChart Fz P m q U V Lm) : 0 < winH1 CL := by
  unfold winH1
  have hcz : 0 < CL.cz1 := CL.consts_pos2.2
  have hC : 0 ≤ CL.Cmu := CL.consts_pos2.1
  have hK : 0 ≤ winKq q := by unfold winKq; positivity
  have h1 : 0 < (1 + winKq q) * CL.Cmu + 1 := by nlinarith
  have h2 : 0 < winKq q * CL.Cmu + 1 := by nlinarith
  refine lt_min (lt_min one_pos (div_pos hcz (by norm_num))) (lt_min ?_ ?_)
  · exact div_pos (pow_pos (div_pos hcz (by norm_num)) 2) h1
  · exact div_pos hcz (mul_pos (by norm_num) h2)

lemma win_chart_sums (CL : SoftEdgeChart Fz P m q U V Lm) (p : Par × ℝ) (hp : p ∈ P) (X : ℝ)
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) (N : ℕ) (hN : CL.N0 ≤ N) (aplus : ℝ)
    (hh1 : Fz.step N ≤ winH1 CL) (hηh : Fz.step N ≤ CL.η)
    (hsm : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / (2 * max 1 aplus) / 10) (haplus : CL.aOf p X N ≤ aplus)
    (hfar : ∀ n : ℤ, 0 ≤ n → n ≤ (N : ℤ) → 2 * CL.η < |uNode (Fz.step N) n - CL.uc p| →
      rhoWin (CL.aOf p X N) < |CL.Zof p X N n|) :
    (∑ n ∈ softWindow CL p X N, Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2 ≤
        11 / CL.dm * Fz.step N ^ (-(1 : ℝ) / 2)) ∧
      1 / (2 * max 1 aplus) / (2 * CL.dp) * Fz.step N ^ (-(1 : ℝ) / 2) ≤
        ∑ n ∈ softWindow CL p X N, Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2 := by
  obtain ⟨-, hη, hdm, hdmp, -, -, -, -⟩ := CL.consts_pos
  have hdp : 0 < CL.dp := lt_of_lt_of_le hdm hdmp
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hM1 : 1 ≤ max 1 aplus := le_max_left _ _
  have hc0half : 1 / (2 * max 1 aplus) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hsm' : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / 20 := by linarith
  have hρ := rhoWin_ge_half (CL.aOf p X N)
  have hLh : Fz.step N * ((N : ℝ) + 1) = Fz.L := by
    unfold SymbolFamily.step FormalResearch.JB.stepSize
    field_simp
  have hspc : ∀ n : ℤ, |uNode (Fz.step N) n - CL.uc p| ≤ 2 * CL.η →
      |uNode (Fz.step N) (n + 1) - CL.uc p| ≤ 2 * CL.η →
      CL.dm * Real.sqrt (Fz.step N) ≤ CL.Zof p X N (n + 1) - CL.Zof p X N n ∧
        CL.Zof p X N (n + 1) - CL.Zof p X N n ≤ CL.dp * Real.sqrt (Fz.step N) :=
    fun n h1 h2 => ⟨((win_row CL p hp X hX N hh0 hh1 n h1).1 h2).1,
      ((win_row CL p hp X hX N hh0 hh1 n h1).1 h2).2.1⟩
  have hcol : ∀ n : ℤ, |uNode (Fz.step N) n - CL.uc p| ≤ 2 * CL.η →
      |CL.Zof p X N n| ≤ rhoWin (CL.aOf p X N) →
      |uNode (Fz.step N) n - CL.uc p| < CL.η / 4 := fun n h1 h2 =>
    (win_row CL p hp X hX N hh0 hh1 n h1).2.2.2 (le_trans h2 (by linarith [ell_nonneg' (CL.aOf p X N)]))
  obtain ⟨-, -, -, -, hz1, hz2, -, -⟩ := CL.shape p hp X hX N hN
  obtain ⟨hj0, hjN, hc1, hc2⟩ := CL.switch_in p hp X hX N hN
  obtain ⟨-, hr⟩ := CL.ucη_in p hp
  obtain ⟨f1, f2, hf1, hf2, hsplit, hb2, hb1⟩ := mbal_sq_shape (CL.aOf p X N)
  have hmain := win_block_abstract (fun z => Mbal (CL.aOf p X N) z ^ 2) (fun z => sq_nonneg _)
    (fun z => mbal_sq_le_one _ z) f1 f2 hf1 hf2 (fun z => hsplit z) hb1 hb2 N (Fz.step N) CL.η
    (CL.uc p) Fz.L (rhoWin (CL.aOf p X N)) CL.dm CL.dp hh0 hη hdm hdmp hLh
    (by linarith [(CL.ucη_in p hp).1]) hr hηh hsm' hρ
    (fun n => CL.Zof p X N n) (fun n => uNode (Fz.step N) n) (fun n => rfl) hspc hcol
    ((CL.chain p X N).jj 2) hj0 hjN hc1 hc2 hz1 hz2 hfar
  have hJup := mbal_sq_int_upper_all (CL.aOf p X N)
  have hJlow := mbal_sq_int_lower (CL.aOf p X N) aplus haplus
  have hs0 : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hdps : 0 < CL.dp * Real.sqrt (Fz.step N) := mul_pos hdp hs0
  have hdms : 0 < CL.dm * Real.sqrt (Fz.step N) := mul_pos hdm hs0
  have hsmall : CL.dm * Real.sqrt (Fz.step N) + 2 * (CL.dp * Real.sqrt (Fz.step N)) ≤ 1 := by
    have : CL.dm * Real.sqrt (Fz.step N) ≤ CL.dp * Real.sqrt (Fz.step N) :=
      mul_le_mul_of_nonneg_right hdmp hs0.le
    linarith
  have hup' := hmain.1
  have hlow' := hmain.2
  have e1 : 11 / CL.dm * Fz.step N ^ (-(1 : ℝ) / 2) = 11 / (CL.dm * Real.sqrt (Fz.step N)) := by
    rw [rpow_neg_half _ hh0.le]; field_simp
  have e2 : 1 / (2 * max 1 aplus) / (2 * CL.dp) * Fz.step N ^ (-(1 : ℝ) / 2) =
      (1 / (2 * max 1 aplus) / 2) / (CL.dp * Real.sqrt (Fz.step N)) := by
    rw [rpow_neg_half _ hh0.le]; field_simp
  constructor
  · rw [e1]
    have hb : ((∫ z in (-rhoWin (CL.aOf p X N))..rhoWin (CL.aOf p X N),
        Mbal (CL.aOf p X N) z ^ 2) + 2 * (CL.dp * Real.sqrt (Fz.step N))) /
          (CL.dm * Real.sqrt (Fz.step N)) + 1 ≤ 11 / (CL.dm * Real.sqrt (Fz.step N)) := by
      rw [div_add_one hdms.ne', div_le_div_iff_of_pos_right hdms]
      linarith
    exact hup'.trans hb
  · rw [e2]
    have hc : (1 / (2 * max 1 aplus) / 2) / (CL.dp * Real.sqrt (Fz.step N)) ≤
        ((∫ z in (-rhoWin (CL.aOf p X N))..rhoWin (CL.aOf p X N), Mbal (CL.aOf p X N) z ^ 2) -
          5 * (CL.dp * Real.sqrt (Fz.step N))) / (CL.dp * Real.sqrt (Fz.step N)) := by
      rw [div_le_div_iff_of_pos_right hdps]
      linarith
    exact hc.trans hlow'

end WinAssembly


/-! ### The far-field localisation of `Z` (from `zeta_far_out`); `PropThaWin` without a premise -/

section FarField

variable {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ}
  {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}

/-- the cut-off comparison: `2 sqrt(max(mu~,0)) + l sqrt h < |zeta|` from the far margin of `zeta`. -/
lemma far_real (cz1 Cmu K h s ℓ P Pt muS0 μt zz : ℝ) (hcz : 0 < cz1) (hC : 0 ≤ Cmu) (hK : 0 ≤ K)
    (hh : 0 < h) (hs : s = Real.sqrt h) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) (hP : P = max muS0 0)
    (hmu0 : |muS0| ≤ Cmu) (hPt : Pt = max μt 0) (hd : |μt - muS0| ≤ K * h ^ 2)
    (hzz : 4 * P + cz1 ≤ zz ^ 2) (hzz0 : 0 ≤ zz)
    (hsmall : 2 * Real.sqrt K * h + s < cz1 / (2 * Real.sqrt (4 * Cmu + cz1))) :
    2 * Real.sqrt Pt + ℓ * s < zz := by
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg h
  have hP0 : 0 ≤ P := by rw [hP]; exact le_max_right _ _
  have hPC : P ≤ Cmu := by
    rw [hP]; exact max_le (le_trans (le_abs_self _) hmu0) hC
  -- `Pt <= P + K h^2`: the positive part is 1-Lipschitz
  have hPt_le : Pt ≤ P + K * h ^ 2 := by
    rw [hPt, hP]
    have h1 : max μt 0 ≤ max muS0 0 + |μt - muS0| := by
      apply max_le
      · have a1 := le_max_left muS0 0
        have a2 := le_abs_self (μt - muS0)
        linarith
      · have a1 := le_max_right muS0 0
        have a2 := abs_nonneg (μt - muS0)
        linarith
    linarith
  -- `sqrt Pt <= sqrt P + sqrt K * h`
  have hsqPt : Real.sqrt Pt ≤ Real.sqrt P + Real.sqrt K * h := by
    rw [Real.sqrt_le_iff]
    refine ⟨add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hh.le), ?_⟩
    have e : (Real.sqrt P + Real.sqrt K * h) ^ 2 =
        P + 2 * Real.sqrt P * Real.sqrt K * h + K * h ^ 2 := by
      rw [add_sq, mul_pow, Real.sq_sqrt hP0, Real.sq_sqrt hK]; ring
    have : 0 ≤ 2 * Real.sqrt P * Real.sqrt K * h := by
      have := Real.sqrt_nonneg P; have := Real.sqrt_nonneg K
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg P)) (Real.sqrt_nonneg K)) hh.le
    rw [e]
    linarith
  -- the margin: with R = sqrt(4P + cz1), `2 sqrt P + cz1/(2T) <= R`, T = sqrt(4 Cmu + cz1)
  set R := Real.sqrt (4 * P + cz1) with hR
  set T := Real.sqrt (4 * Cmu + cz1) with hT
  have hTpos : 0 < T := Real.sqrt_pos.mpr (by linarith)
  have hRsq : R ^ 2 = 4 * P + cz1 := Real.sq_sqrt (by linarith)
  have hPsq : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP0
  have hR2 : 2 * Real.sqrt P ≤ R := by
    refine (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp ?_
    rw [mul_pow, hPsq, hRsq]; linarith
  have hRT : R ≤ T := Real.sqrt_le_sqrt (by linarith)
  have hmargin : cz1 / (2 * T) ≤ R - 2 * Real.sqrt P := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.2 hR2) (show (0 : ℝ) ≤ 2 * T - R - 2 * Real.sqrt P by linarith),
      hRsq, hPsq]
  have hRzz : R ≤ zz := by
    rw [hR]
    calc Real.sqrt (4 * P + cz1) ≤ Real.sqrt (zz ^ 2) := Real.sqrt_le_sqrt hzz
      _ = zz := Real.sqrt_sq hzz0
  have hℓs : ℓ * s ≤ s := mul_le_of_le_one_left hs0 hℓ1
  have hsmall' : cz1 / (2 * Real.sqrt (4 * Cmu + cz1)) = cz1 / (2 * T) := by rw [hT]
  rw [hsmall'] at hsmall
  nlinarith

/-- the far-field smallness `2 sqrt K h + sqrt h < delta1` for `h <= (delta1/(2(2 sqrt K+1)))^2`. -/
lemma far_small (K δ1 h : ℝ) (hK : 0 ≤ K) (hδ : 0 < δ1) (hh : 0 < h) (h1 : h ≤ 1)
    (ht : h ≤ (δ1 / (2 * (2 * Real.sqrt K + 1))) ^ 2) :
    2 * Real.sqrt K * h + Real.sqrt h < δ1 := by
  set t := δ1 / (2 * (2 * Real.sqrt K + 1)) with htdef
  have htpos : 0 < t := by
    rw [htdef]; apply div_pos hδ; have := Real.sqrt_nonneg K; linarith
  have hsh : Real.sqrt h ≤ t := by
    calc Real.sqrt h ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt ht
      _ = t := Real.sqrt_sq htpos.le
  have hsq : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh.le
  have hs1 : Real.sqrt h ≤ 1 := by nlinarith [Real.sqrt_nonneg h]
  have hhs : h ≤ Real.sqrt h := by nlinarith [Real.sqrt_nonneg h]
  have hK1 := Real.sqrt_nonneg K
  have hA : 2 * Real.sqrt K * h ≤ 2 * Real.sqrt K * Real.sqrt h :=
    mul_le_mul_of_nonneg_left hhs (by linarith)
  have hB : (2 * Real.sqrt K + 1) * Real.sqrt h ≤ (2 * Real.sqrt K + 1) * t :=
    mul_le_mul_of_nonneg_left hsh (by linarith)
  have hC : (2 * Real.sqrt K + 1) * t = δ1 / 2 := by
    rw [htdef]; field_simp
  nlinarith

/-- the sum `sum_{r=1}^{q/2} h^{2r} muS_r` is `O(h^2)` by the uniform bound `Cmu` on `muS_r`. -/
lemma far_sum_bound (q : ℕ) (f : ℕ → ℝ) (C h : ℝ) (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hf : ∀ r ∈ Finset.Icc 1 (q / 2), |f r| ≤ C) :
    |∑ r ∈ Finset.Icc 1 (q / 2), h ^ (2 * r) * f r| ≤ ((q / 2 : ℕ) : ℝ) * C * h ^ 2 := by
  have step1 : |∑ r ∈ Finset.Icc 1 (q / 2), h ^ (2 * r) * f r| ≤
      ∑ r ∈ Finset.Icc 1 (q / 2), C * h ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
    rw [abs_mul, abs_of_nonneg (pow_nonneg hh0 _)]
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hp : h ^ (2 * r) ≤ h ^ 2 := pow_le_pow_of_le_one hh0 hh1 (by omega)
    have := mul_le_mul hp (hf r hr) (abs_nonneg _) (pow_nonneg hh0 2)
    linarith [mul_comm C (h ^ 2)]
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at step1
  have hcard : ((q / 2 + 1 - 1 : ℕ) : ℝ) = ((q / 2 : ℕ) : ℝ) := by
    rw [Nat.add_sub_cancel]
  rw [hcard] at step1
  linarith [step1]

/-- the positive part of the far threshold `h` for which the chart lemma holds. -/
def farThr (CL : SoftEdgeChart Fz P m q U V Lm) : ℝ :=
  min 1 ((CL.cz1 / (2 * Real.sqrt (4 * CL.Cmu + CL.cz1)) /
    (2 * (2 * Real.sqrt (((q / 2 : ℕ) : ℝ) * CL.Cmu) + 1))) ^ 2)

lemma farThr_pos (CL : SoftEdgeChart Fz P m q U V Lm) : 0 < farThr CL := by
  have hcz : 0 < CL.cz1 := CL.consts_pos2.2
  have hC : 0 ≤ CL.Cmu := CL.consts_pos2.1
  have hT : 0 < Real.sqrt (4 * CL.Cmu + CL.cz1) := Real.sqrt_pos.mpr (by linarith)
  have hK : 0 ≤ Real.sqrt (((q / 2 : ℕ) : ℝ) * CL.Cmu) := Real.sqrt_nonneg _
  unfold farThr
  refine lt_min one_pos (pow_pos (div_pos (div_pos hcz (by linarith)) (by linarith)) 2)

/-- **the far-field localisation**: rows beyond the collar lie outside the window,
`rho(a) < |Z_n|`, for `step N <= farThr CL`. -/
lemma farChart (CL : SoftEdgeChart Fz P m q U V Lm) (p : Par × ℝ) (hp : p ∈ P) (X : ℝ)
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) (N : ℕ) (hstep : Fz.step N ≤ farThr CL) (n : ℤ)
    (hn0 : 0 ≤ n) (hnN : n ≤ (N : ℤ)) (hfn : 2 * CL.η < |uNode (Fz.step N) n - CL.uc p|) :
    rhoWin (CL.aOf p X N) < |CL.Zof p X N n| := by
  have hcz : 0 < CL.cz1 := CL.consts_pos2.2
  have hC : 0 ≤ CL.Cmu := CL.consts_pos2.1
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hLh : Fz.step N * ((N : ℝ) + 1) = Fz.L := by
    unfold SymbolFamily.step FormalResearch.JB.stepSize
    field_simp
  have hh1 : Fz.step N ≤ 1 := le_trans hstep (min_le_left _ _)
  have hthr : Fz.step N ≤ (CL.cz1 / (2 * Real.sqrt (4 * CL.Cmu + CL.cz1)) /
      (2 * (2 * Real.sqrt (((q / 2 : ℕ) : ℝ) * CL.Cmu) + 1))) ^ 2 :=
    le_trans hstep (min_le_right _ _)
  have hδ1 : 0 < CL.cz1 / (2 * Real.sqrt (4 * CL.Cmu + CL.cz1)) := by
    apply div_pos hcz
    have : 0 < Real.sqrt (4 * CL.Cmu + CL.cz1) := Real.sqrt_pos.mpr (by linarith)
    linarith
  have hsmall : 2 * Real.sqrt (((q / 2 : ℕ) : ℝ) * CL.Cmu) * Fz.step N + Real.sqrt (Fz.step N) <
      CL.cz1 / (2 * Real.sqrt (4 * CL.Cmu + CL.cz1)) :=
    far_small _ _ _ (mul_nonneg (Nat.cast_nonneg _) hC) hδ1 hh0 hh1 hthr
  set α := Fz.bandHi p - X with hα
  have hαδ : |α| ≤ CL.δ0 := by rw [hα, abs_sub_comm]; exact hX
  set μt : ℝ := CL.muS 0 p α + ∑ r ∈ Finset.Icc 1 (q / 2), Fz.step N ^ (2 * r) * CL.muS r p α with hμt
  have haO : CL.aOf p X N = -(1 / Fz.step N) * μt := rfl
  -- the bound on the sum and on the zeroth moment
  have hmu0 : |CL.muS 0 p α| ≤ CL.Cmu :=
    CL.muS_bd 0 (Finset.mem_Icc.mpr ⟨le_refl 0, Nat.zero_le _⟩) p hp α hαδ
  have hsum := far_sum_bound q (fun r => CL.muS r p α) CL.Cmu (Fz.step N) hC hh0.le hh1
    (fun r hr => CL.muS_bd r (Finset.mem_Icc.mpr ⟨by linarith [(Finset.mem_Icc.mp hr).1],
      (Finset.mem_Icc.mp hr).2⟩) p hp α hαδ)
  have hd : |μt - CL.muS 0 p α| ≤ ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N ^ 2 := by
    have e : μt - CL.muS 0 p α = ∑ r ∈ Finset.Icc 1 (q / 2), Fz.step N ^ (2 * r) * CL.muS r p α := by
      rw [hμt]; ring
    rw [e]; exact hsum
  -- the zeta margin beyond the collar
  have hx0 : 0 ≤ uNode (Fz.step N) n := by
    unfold uNode
    have : (0 : ℝ) ≤ n := by exact_mod_cast hn0
    nlinarith
  have hxL : CL.uc p + (uNode (Fz.step N) n - CL.uc p) ≤ Fz.L := by
    unfold uNode at *
    have : (n : ℝ) ≤ N := by exact_mod_cast hnN
    nlinarith
  have hz := CL.zeta_far_out p hp α hαδ (uNode (Fz.step N) n - CL.uc p)
    (le_trans (by linarith) hfn.le) (by linarith) hxL
  -- the algebra of `aOf`
  set A' : ℝ := max (-CL.aOf p X N) 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hneg : -CL.aOf p X N * Fz.step N = μt := by
    rw [haO]; field_simp
  have hAh : A' * Fz.step N = max μt 0 := by
    rw [hA', max_mul_of_nonneg _ _ hh0.le, hneg, zero_mul]
  have hℓ0 : 0 ≤ (1 + A') ^ (-(1 : ℝ) / 6) := by positivity
  have hℓ1 : (1 + A') ^ (-(1 : ℝ) / 6) ≤ 1 := ell_le_one A' hA'0
  have hrho : rhoWin (CL.aOf p X N) = 2 * Real.sqrt A' + (1 + A') ^ (-(1 : ℝ) / 6) := rfl
  have hsq : Real.sqrt (max μt 0) = Real.sqrt A' * Real.sqrt (Fz.step N) := by
    rw [← hAh, Real.sqrt_mul hA'0]
  -- the real comparison
  have key := far_real CL.cz1 CL.Cmu (((q / 2 : ℕ) : ℝ) * CL.Cmu) (Fz.step N) (Real.sqrt (Fz.step N))
    ((1 + A') ^ (-(1 : ℝ) / 6)) (max (CL.muS 0 p α) 0) (max μt 0) (CL.muS 0 p α) μt
    (|CL.zeta p α (uNode (Fz.step N) n - CL.uc p)|) hcz hC (mul_nonneg (Nat.cast_nonneg _) hC) hh0 rfl
    hℓ0 hℓ1 rfl hmu0 rfl hd (by rw [sq_abs]; exact hz) (abs_nonneg _) hsmall
  have hzpos : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  unfold SoftEdgeChart.Zof
  rw [abs_div, abs_of_pos hzpos, lt_div_iff₀ hzpos, hrho]
  have e2 : (2 * Real.sqrt A' + (1 + A') ^ (-(1 : ℝ) / 6)) * Real.sqrt (Fz.step N) =
      2 * Real.sqrt (max μt 0) + (1 + A') ^ (-(1 : ℝ) / 6) * Real.sqrt (Fz.step N) := by
    rw [hsq]; ring
  rw [e2]
  exact key

end FarField

section FinalTheorem

variable {Par : Type*} [TopologicalSpace Par]

/-- **lem:tha-win** (items (1), (2), (3), (5)): the frozen `PropThaWin`, with no premise. -/
theorem propThaWin (Fz : SymbolFamily (Par × ℝ)) (P : Set (Par × ℝ)) (m q : ℕ) (U V : ℝ → ℝ → ℝ)
    {Lm : ℝ → ℝ} (CL : SoftEdgeChart Fz P m q U V Lm) (aplus cPC CPC : ℝ) :
    PropThaWin Fz P m q U V CL aplus cPC CPC := by
  unfold PropThaWin
  intro pc r _
  obtain ⟨-, hη, hdm, hdmp, -, -, -, -⟩ := CL.consts_pos
  have hdp : 0 < CL.dp := lt_of_lt_of_le hdm hdmp
  have hM1 : 1 ≤ max 1 aplus := le_max_left _ _
  have hc0pos : 0 < 1 / (2 * max 1 aplus) := by apply div_pos one_pos; linarith
  have hfpos := farThr_pos CL
  have hh0pos : 0 < min (winH1 CL) (min CL.η (farThr CL)) :=
    lt_min (winH1_pos CL) (lt_min hη hfpos)
  have hsq : 0 < (1 / (2 * max 1 aplus) / (10 * CL.dp)) ^ 2 :=
    pow_pos (div_pos hc0pos (by linarith)) 2
  refine ⟨min (min (winH1 CL) (min CL.η (farThr CL))) ((1 / (2 * max 1 aplus) / (10 * CL.dp)) ^ 2),
    winCLam CL, winCnb CL, winCB CPC aplus, 1 / (2 * max 1 aplus), lt_min hh0pos hsq, hc0pos, ?_⟩
  intro p hp X hX N hN hstep haplus
  have hstep1 : Fz.step N ≤ winH1 CL :=
    le_trans hstep (le_trans (min_le_left _ _) (min_le_left _ _))
  have hstep2 : Fz.step N ≤ CL.η :=
    le_trans hstep (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hstep3 : Fz.step N ≤ farThr CL :=
    le_trans hstep (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hstep4 : Fz.step N ≤ (1 / (2 * max 1 aplus) / (10 * CL.dp)) ^ 2 :=
    le_trans hstep (min_le_right _ _)
  have hsm : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / (2 * max 1 aplus) / 10 := by
    have hq : Real.sqrt (Fz.step N) ≤ 1 / (2 * max 1 aplus) / (10 * CL.dp) := by
      have hpos : 0 ≤ 1 / (2 * max 1 aplus) / (10 * CL.dp) := by
        apply div_nonneg hc0pos.le; linarith
      rw [← Real.sqrt_sq hpos]
      exact Real.sqrt_le_sqrt hstep4
    calc CL.dp * Real.sqrt (Fz.step N) ≤ CL.dp * (1 / (2 * max 1 aplus) / (10 * CL.dp)) :=
          mul_le_mul_of_nonneg_left hq hdp.le
      _ = 1 / (2 * max 1 aplus) / 10 := by field_simp
  have hfarN : ∀ n : ℤ, 0 ≤ n → n ≤ (N : ℤ) → 2 * CL.η < |uNode (Fz.step N) n - CL.uc p| →
      rhoWin (CL.aOf p X N) < |CL.Zof p X N n| :=
    fun n h0 hN' hfn => farChart CL p hp X hX N hstep3 n h0 hN' hfn
  obtain ⟨hup, hlow⟩ := win_chart_sums CL p hp X hX N hN aplus hstep1 hstep2 hsm haplus hfarN
  refine ⟨win_conj1 CL p hp X hX N hstep1, ?_, hlow, hup⟩
  intro z hz
  exact ⟨(weights_conj (CL.aOf p X N) aplus z haplus hz).1,
    (weights_conj (CL.aOf p X N) aplus z haplus hz).2,
    envelope_conj3 pc aplus (CL.aOf p X N) z haplus hz⟩

end FinalTheorem

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.mbal_sq_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.mbal_sq_shape

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.mbal_sq_int_upper_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.mbal_sq_int_upper_all

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.mbal_sq_int_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.mbal_sq_int_lower

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.window_block_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.window_block_bounds

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.win_block_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.win_block_abstract

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.win_chart_sums' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.win_chart_sums

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.farChart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.farChart

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.propThaWin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.propThaWin

end FormalResearch.JacobiEigenvectors.TheoremA

end

end
