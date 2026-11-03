module

public import FormalResearch.FourQubitEntropy.RenyiFullSHNodes
public import FormalResearch.FourQubitEntropy.RenyiFullNU

/-!
# Small-head dual: the small-tail deficit (SHD)

Paper E, `lem:fqe-small-head-dual`, equation (SHD): for `0 < u ≤ 1/4`, `0 ≤ δ ≤ u`,
`H_q(λ) ≤ 1 + h(u) - (11/10)(1+2u) δ²` on `λ = ((1-u+δ)/2, (1-u-δ)/2, u/2, u/2)`.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

theorem bqD_third_ge : 249 / 2000 ≤ bqD qBQ (1 / 9) := by
  have h := binH_third_le
  have e := bqD_binary (u := 1 / 3) (by norm_num) (by norm_num)
  have e2 : (1 - 2 * (1 / 3 : ℝ)) ^ 2 = 1 / 9 := by norm_num
  rw [e2] at e
  linarith

theorem bqD_ge {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 9) : 2241 / 2000 * z ≤ bqD qBQ z := by
  have h := bqD_chord hz0 hz1
  have := bqD_third_ge
  nlinarith

theorem t_poly {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 3 / 5) :
    55 * (1 + 3 * t ^ 2) * (1 + t ^ 3) ≤ 56 * (1 + t ^ 2) ^ 3 := by
  nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), sq_nonneg (t ^ 2 - t / 2), sq_nonneg (t - 1 / 3),
    sq_nonneg (t ^ 2 - 1 / 4), mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.2 h1),
    sq_nonneg (t ^ 3 - t ^ 2), sq_nonneg (t ^ 2 - 2 * t / 5)]

/-- The weight `1 - w = (1-u)^q/((1-u)^q+u^q)` is at least `(55/56)(1+2u)(1-u)²` for `u ≤ 1/4`. -/
theorem omega_lower {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 4) :
    55 / 56 * (1 + 2 * u) * (1 - u) ^ 2 ≤ (1 - u) ^ qS / ((1 - u) ^ qS + u ^ qS) := by
  have h1u : 0 < 1 - u := by linarith
  set ρ := u / (1 - u) with hρ
  have hρ0 : 0 < ρ := div_pos hu0 h1u
  have hρ1 : ρ ≤ 1 / 3 := by rw [hρ, div_le_iff₀ h1u]; linarith
  have huρ : u = (1 - u) * ρ := by rw [hρ]; field_simp
  have hT0 : 0 < (1 - u) ^ qS := Real.rpow_pos_of_pos h1u _
  have hupow : u ^ qS = (1 - u) ^ qS * ρ ^ qS := by
    conv_lhs => rw [huρ]
    exact Real.mul_rpow h1u.le hρ0.le
  have hω : (1 - u) ^ qS / ((1 - u) ^ qS + u ^ qS) = 1 / (1 + ρ ^ qS) := by
    rw [hupow]; field_simp
  rw [hω]
  have hq32 : ρ ^ qS ≤ ρ ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hρ0 (by linarith) (by unfold qS; norm_num)
  rw [rpow_three_halves_eq_nu hρ0.le] at hq32
  set t := Real.sqrt ρ with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htt : t ^ 2 = ρ := Real.sq_sqrt hρ0.le
  have ht1 : t ≤ 3 / 5 := by nlinarith
  have hρt : ρ * t = t ^ 3 := by rw [← htt]; ring
  have hu_t : u = t ^ 2 / (1 + t ^ 2) := by
    rw [htt]; rw [hρ]; field_simp; ring
  have hpoly := t_poly ht0 ht1
  have hden : 0 < 1 + ρ ^ qS := by positivity
  have hstep : 1 / (1 + ρ * t) ≤ 1 / (1 + ρ ^ qS) := by
    apply one_div_le_one_div_of_le hden; linarith
  refine le_trans ?_ hstep
  rw [hρt, hu_t, le_div_iff₀ (by positivity)]
  have e : 55 / 56 * (1 + 2 * (t ^ 2 / (1 + t ^ 2))) * (1 - t ^ 2 / (1 + t ^ 2)) ^ 2 * (1 + t ^ 3) =
      55 * (1 + 3 * t ^ 2) * (1 + t ^ 3) / (56 * (1 + t ^ 2) ^ 3) := by field_simp; ring
  rw [e, div_le_one (by positivity)]
  exact hpoly

/-- **(SHD)**. -/
theorem sh_deficit {u δ : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 4) (hδ0 : 0 ≤ δ) (hδu : δ ≤ u) :
    renyiSpec qS ![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2] ≤
      1 + binH qBQ u - 11 / 10 * (1 + 2 * u) * δ ^ 2 := by
  have h1u : 0 < 1 - u := by linarith
  have hJ := sh_jensen hu0 (by linarith) hδ0 (by linarith)
  set s := δ / (1 - u) with hs
  have hs0 : 0 ≤ s := div_nonneg hδ0 h1u.le
  have hs3 : s ≤ 1 / 3 := by rw [hs, div_le_iff₀ h1u]; linarith
  have hz1 : s ^ 2 ≤ 1 / 9 := by nlinarith
  have hD := bqD_ge (sq_nonneg s) hz1
  have hω := omega_lower hu0 hu1
  have hω0 : 0 ≤ (1 - u) ^ qS / ((1 - u) ^ qS + u ^ qS) := by positivity
  have hδs : δ = s * (1 - u) := by rw [hs]; field_simp
  have key : 11 / 10 * (1 + 2 * u) * δ ^ 2 ≤
      (1 - u) ^ qS / ((1 - u) ^ qS + u ^ qS) * bqD qBQ (s ^ 2) := by
    have h2 := mul_le_mul_of_nonneg_left hD hω0
    have h3 : 0 ≤ 2241 / 2000 * s ^ 2 := by positivity
    have h4 := mul_le_mul_of_nonneg_right hω h3
    have e : δ ^ 2 = s ^ 2 * (1 - u) ^ 2 := by rw [hδs]; ring
    rw [e]
    have hpos : 0 ≤ (1 + 2 * u) * (1 - u) ^ 2 * s ^ 2 := by positivity
    nlinarith [hpos]
  linarith

end FormalResearch.FourQubitEntropy.RenyiFull
