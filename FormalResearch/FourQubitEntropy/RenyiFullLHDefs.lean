module

public import FormalResearch.FourQubitEntropy.RenyiFullLHKfun

/-!
# Large-head chart: the polynomials `B, C`, the cubic minorant `K_*` and the range of `K`

Paper E, `lem:fqe-large-head-curvature`: `B = (1+2z²)/3`, `C = (1+6z²+2z³)/9`, `K = kfun q_s z`.
`K_*(z) = k + (3-3k-2q/3) z² + (2q/3-2+2k) z³`, `k = 5247/10000 < K(0)`, is the cubic Hermite
minorant of `K` at `0, 1`; the chord of the convex `K` gives `K ≤ 61/80` for `z ≤ 1/2`.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

noncomputable def Bz (z : ℝ) : ℝ := (1 + 2 * z ^ 2) / 3
noncomputable def Cz (z : ℝ) : ℝ := (1 + 6 * z ^ 2 + 2 * z ^ 3) / 9

/-- The cubic Hermite minorant of `K` at `0, 1` (with `k = 5247/10000`). -/
noncomputable def Kstar (z : ℝ) : ℝ :=
  5247 / 10000 + (3 - 3 * (5247 / 10000) - 2 * qS / 3) * z ^ 2 + (2 * qS / 3 - 2 + 2 * (5247 / 10000)) * z ^ 3

theorem three_rpow_qS_lt : (3 : ℝ) ^ qS ≤ 28587 / 5000 := by
  have := rpow_qS_le_Q (x := 3) (b := 28587 / 5000) (by norm_num) (by norm_num) (by decide +kernel)
  simpa using this

theorem three_rpow_qS_gt : (11433 / 2000 : ℝ) ≤ 3 ^ qS := by
  have := le_rpow_qS_Q (x := 3) (b := 11433 / 2000) (by norm_num) (by norm_num) (by decide +kernel)
  simpa using this

theorem K0_bounds : 5247 / 10000 ≤ kfun qS 0 ∧ kfun qS 0 ≤ 5248 / 10000 := by
  rw [kfun_zero]
  have h3 := three_rpow_qS_lt
  have h4 := three_rpow_qS_gt
  have hp : (0 : ℝ) < 3 ^ qS := by linarith
  constructor
  · rw [le_div_iff₀ hp]; linarith
  · rw [div_le_iff₀ hp]; linarith

theorem Kstar_le_kfun {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : Kstar z ≤ kfun qS z := by
  have hq1 : 1 < qS := by unfold qS; norm_num
  have hq2 : qS < 2 := by unfold qS; norm_num
  have h := kfun_ge_Hh hq1 hq2 z ⟨hz0, hz1⟩
  have hK := K0_bounds
  unfold Hh at h
  unfold Kstar
  have e : 0 ≤ (kfun qS 0 - 5247 / 10000) * ((1 - z) ^ 2 * (1 + 2 * z)) := by
    apply mul_nonneg (by linarith [hK.1]) (by positivity)
  nlinarith

theorem Kstar_ge_k {z : ℝ} (hz0 : 0 ≤ z) (_hz1 : z ≤ 1) : 5247 / 10000 ≤ Kstar z := by
  unfold Kstar qS
  nlinarith [pow_nonneg hz0 2, pow_nonneg hz0 3]

/-- Chord of the convex `K`: `K(z) ≤ K(0) + (1-K(0)) z` on `[0,1]`. -/
theorem kfun_le_chord {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    kfun qS z ≤ kfun qS 0 + (1 - kfun qS 0) * z := by
  have hq1 : (1 : ℝ) ≤ qS := by unfold qS; norm_num
  have hc := convexOn_rpow hq1
  have h3 : (0 : ℝ) < 3 ^ qS := Real.rpow_pos_of_pos (by norm_num) _
  -- 1 + 2z = (1-z)*1 + z*3,  1 - z = (1-z)*1 + z*0
  have e1 : (1 + 2 * z) ^ qS ≤ (1 - z) * 1 + z * 3 ^ qS := by
    have := hc.2 (show (1 : ℝ) ∈ Ici 0 by simp) (show (3 : ℝ) ∈ Ici 0 by simp)
      (show 0 ≤ 1 - z by linarith) hz0 (by ring)
    simp only [smul_eq_mul, Real.one_rpow, mul_one] at this
    have e : 1 - z + z * 3 = 1 + 2 * z := by ring
    rw [e] at this
    linarith
  have e2 : (1 - z) ^ qS ≤ (1 - z) * 1 + z * 0 := by
    have := hc.2 (show (1 : ℝ) ∈ Ici 0 by simp) (show (0 : ℝ) ∈ Ici 0 by simp)
      (show 0 ≤ 1 - z by linarith) hz0 (by ring)
    have hq0 : (0 : ℝ) ^ qS = 0 := Real.zero_rpow (by linarith)
    simp only [smul_eq_mul, Real.one_rpow, mul_one, mul_zero, add_zero, hq0] at this
    linarith
  rw [kfun_zero]
  unfold kfun
  rw [div_le_iff₀ h3]
  have : (3 / 3 ^ qS + (1 - 3 / 3 ^ qS) * z) * 3 ^ qS = 3 + (3 ^ qS - 3) * z := by
    field_simp
  rw [this]
  nlinarith

theorem kfun_le_one {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : kfun qS z ≤ 1 := by
  have h := kfun_le_chord hz0 hz1
  have := K0_bounds
  nlinarith

theorem kfun_le_A {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) : kfun qS z ≤ 61 / 80 := by
  have h := kfun_le_chord hz0 (by linarith)
  have := K0_bounds
  nlinarith

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.Kstar_le_kfun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kstar_le_kfun

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.kfun_le_chord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kfun_le_chord

end FormalResearch.FourQubitEntropy.RenyiFull
