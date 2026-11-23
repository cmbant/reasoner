module

public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerTau
public import FormalResearch.ModularBootstrap.SlitStrip.Majorant

/-!
# Closed forms of `ψ`, `H` and `J` (`remainder.tex`, Proposition 1.2(1), proof)

* `langerPsi_eq_arccosh` (`u > 0`): `∫₀¹ 2 dt/(2 + u t²)^{1/2} = arccosh(1 + u)/√u`;
  `langerPsi_eq_arccos` (`-2 < u < 0`): `= arccos(1 + u)/√(-u)`.
* `langerH_eq_of_pos`: `H(r) = ρ_U(ξ_* + r)/√r` for `r > 0`;
  `langerH_eq_of_neg`: `H(r) = (4/(3π)) arccos(sinh(π(ξ_* + r)))/√(-r)` for `-ξ_* < r < 0`.
* `langerJ_mul_rpow_of_pos`: `J(r) r^{3/2} = ∫₀^r ρ_U(ξ_* + s) ds = 2 N(ξ_* + r)` for `r > 0`;
  `langerJ_mul_rpow_of_neg`: `J(r)|r|^{3/2} = slitDeficit(|r|)/π` for `-ξ_* < r < 0`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb

/-! ### `ψ` in closed form -/

lemma arccoshR_one_add_eq {u : ℝ} (hu : 0 < u) : arccoshR (1 + u) = 2 * Real.arsinh (√(u / 2)) := by
  set z := √(u / 2) with hz
  have hz2 : z ^ 2 = u / 2 := Real.sq_sqrt (by positivity)
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hsh : Real.sinh (Real.arsinh z) = z := Real.sinh_arsinh z
  have hcs : Real.cosh (Real.arsinh z) ^ 2 = 1 + z ^ 2 := by
    have := Real.cosh_sq (Real.arsinh z); rw [hsh] at this; rw [this]; ring
  have hnn : 0 ≤ 2 * Real.arsinh z := by
    have := Real.arsinh_nonneg_iff.2 hz0; linarith
  have : Real.cosh (2 * Real.arsinh z) = 1 + u := by
    rw [Real.cosh_two_mul, hcs, hsh]; nlinarith
  rw [← this, arccoshR_cosh hnn]

lemma arccos_one_sub_eq {w : ℝ} (hw : 0 < w) (hw2 : w < 2) :
    Real.arccos (1 - w) = 2 * Real.arcsin (√(w / 2)) := by
  set z := √(w / 2) with hz
  have hz2 : z ^ 2 = w / 2 := Real.sq_sqrt (by positivity)
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hz1 : z ≤ 1 := by
    rw [hz, Real.sqrt_le_one]; linarith
  have hs : Real.sin (Real.arcsin z) = z := Real.sin_arcsin (by linarith) hz1
  have h1 : 0 ≤ Real.arcsin z := Real.arcsin_nonneg.2 hz0
  have h2 : Real.arcsin z ≤ π / 2 := Real.arcsin_le_pi_div_two z
  have : Real.cos (2 * Real.arcsin z) = 1 - w := by
    rw [Real.cos_two_mul, Real.cos_sq', hs]; nlinarith
  rw [← this, Real.arccos_cos (by linarith) (by linarith)]

/-- `ψ(u) = arccosh(1+u)/√u` for `u > 0`. -/
lemma langerPsi_eq_arccosh {u : ℝ} (hu : 0 < u) : langerPsi u = arccoshR (1 + u) / √u := by
  have hs : 0 < √u := Real.sqrt_pos.2 hu
  set c := √(u / 2) with hc
  have hc2 : c ^ 2 = u / 2 := Real.sq_sqrt (by positivity)
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hcs : c = √u / √2 := by
    rw [hc, Real.sqrt_div hu.le]
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
  have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hder : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => (2 / √u) * Real.arsinh (t * c)) (2 / √(2 + u * t ^ 2)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => t * c) c t := by simpa using (hasDerivAt_id t).mul_const c
    have h3 := ((Real.hasDerivAt_arsinh (t * c)).comp t h1).const_mul (2 / √u)
    refine h3.congr_deriv ?_
    have hpos : 0 < 2 + u * t ^ 2 := by nlinarith [sq_nonneg t]
    have hw : 0 < √(2 + u * t ^ 2) := Real.sqrt_pos.2 hpos
    have e : 1 + (t * c) ^ 2 = (2 + u * t ^ 2) / 2 := by rw [mul_pow, hc2]; ring
    rw [e, Real.sqrt_div hpos.le, hcs]
    field_simp
  have hcont : ContinuousOn (fun t : ℝ => 2 / √(2 + u * t ^ 2)) (uIcc 0 1) := by
    refine continuousOn_const.div (by fun_prop) fun t _ => ?_
    exact (Real.sqrt_pos.2 (by nlinarith [sq_nonneg t])).ne'
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.intervalIntegrable)
  unfold langerPsi
  rw [this, arccoshR_one_add_eq hu]
  simp only [one_mul, zero_mul, Real.arsinh_zero, mul_zero, sub_zero]
  field_simp
  rfl

/-- `ψ(u) = arccos(1+u)/√(-u)` for `-2 < u < 0`. -/
lemma langerPsi_eq_arccos {u : ℝ} (hu : -2 < u) (hu0 : u < 0) :
    langerPsi u = Real.arccos (1 + u) / √(-u) := by
  set w := -u with hw
  have hw0 : 0 < w := by linarith
  have hw2 : w < 2 := by linarith
  have hs : 0 < √w := Real.sqrt_pos.2 hw0
  set c := √(w / 2) with hc
  have hc2 : c ^ 2 = w / 2 := Real.sq_sqrt (by positivity)
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc1 : c < 1 := by rw [hc, Real.sqrt_lt' one_pos]; linarith
  have hcs : c = √w / √2 := by rw [hc, Real.sqrt_div hw0.le]
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
  have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hder : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => (2 / √w) * Real.arcsin (t * c)) (2 / √(2 + u * t ^ 2)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h1 : HasDerivAt (fun t : ℝ => t * c) c t := by simpa using (hasDerivAt_id t).mul_const c
    have htc : t * c < 1 := by nlinarith [ht.1, ht.2]
    have htc' : t * c ≠ -1 := by nlinarith [ht.1, ht.2]
    have htc'' : t * c ≠ 1 := htc.ne
    have h3 := ((Real.hasDerivAt_arcsin htc' htc'').comp t h1).const_mul (2 / √w)
    refine h3.congr_deriv ?_
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have hpos : 0 < 2 + u * t ^ 2 := by nlinarith [mul_nonneg (neg_nonneg.2 hu0.le) (sub_nonneg.2 ht2)]
    have hw' : 0 < √(2 + u * t ^ 2) := Real.sqrt_pos.2 hpos
    have e : 1 - (t * c) ^ 2 = (2 + u * t ^ 2) / 2 := by rw [mul_pow, hc2, hw]; ring
    rw [e, Real.sqrt_div hpos.le, hcs]
    field_simp
  have hcont : ContinuousOn (fun t : ℝ => 2 / √(2 + u * t ^ 2)) (uIcc 0 1) := by
    refine continuousOn_const.div (by fun_prop) fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    exact (Real.sqrt_pos.2 (by nlinarith [mul_nonneg (neg_nonneg.2 hu0.le) (sub_nonneg.2 ht2)])).ne'
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.intervalIntegrable)
  unfold langerPsi
  rw [this, show 1 + u = 1 - w by rw [hw]; ring, arccos_one_sub_eq hw0 hw2]
  simp only [one_mul, zero_mul, Real.arcsin_zero, mul_zero, sub_zero]
  field_simp
  rfl

/-! ### `H` in closed form -/

lemma langerQ_eq {r : ℝ} (hr : r ≠ 0) : langerQ r = langerU r / r := by
  rw [eq_div_iff hr]; exact langerQ_mul r

lemma langerU_pos {r : ℝ} (hr : 0 < r) : 0 < langerU r := by
  have := langerU_strictMono hr; rwa [langerU_zero] at this

lemma langerU_neg {r : ℝ} (hr : r < 0) : langerU r < 0 := by
  have := langerU_strictMono hr; rwa [langerU_zero] at this

lemma one_add_langerU (r : ℝ) : 1 + langerU r = Real.sinh (π * (xiStar + r)) := by
  unfold langerU; ring

/-- `H(r) = ρ_U(ξ_* + r)/√r` for `r > 0`. -/
lemma langerH_eq_of_pos {r : ℝ} (hr : 0 < r) : langerH r = rhoU (xiStar + r) / √r := by
  have hu := langerU_pos hr
  unfold langerH
  rw [langerPsi_eq_arccosh hu, one_add_langerU, langerQ_eq hr.ne',
    rhoU_eq_of_ge (by linarith), Real.sqrt_div hu.le]
  have h1 : 0 < √(langerU r) := Real.sqrt_pos.2 hu
  have h2 : 0 < √r := Real.sqrt_pos.2 hr
  have := Real.pi_pos
  field_simp

/-- `H(r) = (4/(3π)) arccos(sinh(π(ξ_* + r)))/√(-r)` for `-ξ_* < r < 0`. -/
lemma langerH_eq_of_neg {r : ℝ} (hr : -xiStar < r) (hr0 : r < 0) :
    langerH r = (4 / (3 * π)) * Real.arccos (Real.sinh (π * (xiStar + r))) / √(-r) := by
  have hu := langerU_neg hr0
  have hu1 := neg_one_lt_langerU hr
  unfold langerH
  rw [langerPsi_eq_arccos (by linarith) hu, one_add_langerU, langerQ_eq hr0.ne]
  have e : langerU r / r = (-langerU r) / (-r) := by rw [neg_div_neg_eq]
  rw [e, Real.sqrt_div (by linarith)]
  have h1 : 0 < √(-langerU r) := Real.sqrt_pos.2 (by linarith)
  have h2 : 0 < √(-r) := Real.sqrt_pos.2 (by linarith)
  have := Real.pi_pos
  field_simp

/-! ### Change of variables `s = R t²` -/

lemma integral_sq_subst {g : ℝ → ℝ} {R : ℝ} (hR : 0 < R) (hg : ContinuousOn g (Icc 0 R)) :
    ∫ t in (0 : ℝ)..1, t * g (R * t ^ 2) = (1 / (2 * R)) * ∫ s in (0 : ℝ)..R, g s := by
  have himg : (fun t : ℝ => R * t ^ 2) '' [[0, 1]] ⊆ Icc 0 R := by
    rintro _ ⟨t, ht, rfl⟩
    rw [uIcc_of_le zero_le_one] at ht
    refine ⟨by have := ht.1; positivity, ?_⟩
    have : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    nlinarith
  have h := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := 1)
    (f := fun t : ℝ => R * t ^ 2) (f' := fun t : ℝ => 2 * R * t) (g := g)
    (fun t _ => by simpa [mul_assoc, mul_comm, mul_left_comm] using
      ((hasDerivAt_pow 2 t).const_mul R))
    (by fun_prop) (hg.mono himg)
  simp only [Function.comp_apply] at h
  have e : ∀ t : ℝ, g (R * t ^ 2) * (2 * R * t) = (2 * R) * (t * g (R * t ^ 2)) := fun t => by ring
  simp_rw [e] at h
  rw [intervalIntegral.integral_const_mul] at h
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, one_pow, mul_one] at h
  rw [h.symm, ← mul_assoc, one_div_mul_cancel (by positivity), one_mul]

lemma rpow_three_halves {r : ℝ} (hr : 0 ≤ r) : r ^ (3 / 2 : ℝ) = r * √r := by
  rcases hr.eq_or_lt with h | h
  · rw [← h]; simp
  · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add h, Real.rpow_one,
      ← Real.sqrt_eq_rpow]

/-- `J(r) r^{3/2} = ∫₀^r ρ_U(ξ_* + s) ds` for `r > 0`. -/
lemma langerJ_mul_rpow_of_pos {r : ℝ} (hr : 0 < r) :
    langerJ r * r ^ (3 / 2 : ℝ) = ∫ s in (0 : ℝ)..r, rhoU (xiStar + s) := by
  have hcont : ContinuousOn (fun s => rhoU (xiStar + s)) (Icc 0 r) :=
    continuousOn_rhoU.comp (by fun_prop) (fun s hs => by
      simp only [mem_Ici]; linarith [hs.1])
  have hs : 0 < √r := Real.sqrt_pos.2 hr
  have hJ : langerJ r = (2 / √r) * ∫ t in (0 : ℝ)..1, t * rhoU (xiStar + r * t ^ 2) := by
    unfold langerJ
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    rcases ht.1.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · rw [langerH_eq_of_pos (by positivity)]
      have : √(r * t ^ 2) = √r * t := by rw [Real.sqrt_mul hr.le, Real.sqrt_sq ht.1]
      rw [this]
      have : 0 < t := hpos
      field_simp
  rw [hJ, integral_sq_subst hr hcont, rpow_three_halves hr.le]
  field_simp

/-- `π J(r) |r|^{3/2} = slitDeficit(|r|)` for `-ξ_* < r < 0`. -/
lemma langerJ_mul_rpow_of_neg {r : ℝ} (hr : -xiStar < r) (hr0 : r < 0) :
    π * (langerJ r * (-r) ^ (3 / 2 : ℝ)) = slitDeficit (-r) := by
  set R := -r with hR
  have hR0 : 0 < R := by linarith
  have hRlt : R < xiStar := by linarith
  have hcont : ContinuousOn (fun s => Real.arccos (Real.sinh (π * (xiStar - s)))) (Icc 0 R) := by
    exact (Real.continuous_arccos.comp (Real.continuous_sinh.comp
      (continuous_const.mul (continuous_const.sub continuous_id)))).continuousOn
  have hs : 0 < √R := Real.sqrt_pos.2 hR0
  have hJ : langerJ r = (2 / √R) * ((4 / (3 * π)) * ∫ t in (0 : ℝ)..1,
      t * Real.arccos (Real.sinh (π * (xiStar - R * t ^ 2)))) := by
    unfold langerJ
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    rcases ht.1.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      have hlo : -xiStar < r * t ^ 2 := by nlinarith [sq_nonneg t]
      have hhi : r * t ^ 2 < 0 := by have : 0 < t ^ 2 := by positivity
                                     nlinarith
      rw [langerH_eq_of_neg hlo hhi]
      have e1 : -(r * t ^ 2) = R * t ^ 2 := by rw [hR]; ring
      have e2 : xiStar + r * t ^ 2 = xiStar - R * t ^ 2 := by rw [hR]; ring
      rw [e1, e2, Real.sqrt_mul hR0.le, Real.sqrt_sq ht.1]
      have : 0 < t := hpos
      have := Real.pi_pos
      field_simp
  rw [hJ, integral_sq_subst hR0 hcont, rpow_three_halves hR0.le]
  have h2 : ∫ s in (0 : ℝ)..R, Real.arccos (Real.sinh (π * (xiStar - s))) =
      ∫ y in (xiStar - R)..xiStar, Real.arccos (Real.sinh (π * y)) := by
    have := intervalIntegral.integral_comp_sub_left
      (fun y : ℝ => Real.arccos (Real.sinh (π * y))) (a := 0) (b := R) xiStar
    rw [sub_zero] at this
    exact this
  rw [h2]
  unfold slitDeficit
  have := Real.pi_pos
  field_simp

end FormalResearch.ModularBootstrap.Upper.Ramped
