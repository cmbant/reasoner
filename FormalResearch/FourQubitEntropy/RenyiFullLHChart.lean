import FormalResearch.FourQubitEntropy.RenyiFullLHHalfCells

/-!
# Large-head chart: the third derivative of `f` is nonpositive

Paper E, `lem:fqe-large-head-curvature`.  `f(a,z) = h(a, K(z)) + P(a; B(z), C(z))` on
`1/2 ≤ a ≤ 4/5`, `0 ≤ z ≤ 1`.  `f_aaaa < 0` (`f4_neg_A`, `f4_neg_B`) and `f_aaa(1/2) ≤ 0`
(`f3_half_nonpos`) give `f_aaa ≤ 0`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

theorem lhY_half (q K : ℝ) (hK : 0 < K) : lhY q K (1 / 2) = (1 - K) / (1 + K) := by
  unfold lhY lhZ
  have h : (0 : ℝ) < (1 / 2) ^ q := Real.rpow_pos_of_pos (by norm_num) q
  have e : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  rw [e]
  field_simp

theorem hd3_half (K : ℝ) (hK : 0 < K) :
    hd3 qS K (1 / 2) = 16 * qS * ((1 - K) / (1 + K)) *
      ((qS ^ 2 - 1) - qS ^ 2 * ((1 - K) / (1 + K)) ^ 2) / ((qS - 1) * Real.log 2) := by
  unfold hd3 lhm3
  rw [lhY_half _ _ hK]
  have e : 2 * (1 / 2 : ℝ) - 1 = 0 := by norm_num
  rw [e]
  have : (1 - (0 : ℝ) ^ 2) = 1 := by norm_num
  simp only [this]
  ring

theorem Pg3_half (B C : ℝ) :
    Pg3 aL bL gL B C (1 / 2) = -(72 * (3 / 20 : ℝ) * (1 - C) + 12 * (159 / 100 : ℝ) * (1 - B ^ 2)) := by
  unfold Pg3 bL gL
  ring

/-- **`f_aaa(1/2) ≤ 0`.** -/
theorem f3_half_nonpos {z K : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hKs : Kstar z ≤ K) (hK1 : K ≤ 1) :
    hd3 qS K (1 / 2) + Pg3 aL bL gL (Bz z) (Cz z) (1 / 2) ≤ 0 := by
  have hk := Kstar_ge_k hz0 hz1
  have hq : qS = 1587 / 1000 := rfl
  have hL := log2_bounds
  have hK0 : 0 < K := by linarith
  have hKs0 : 0 < 1 + Kstar z := by linarith
  have hK10 : 0 < 1 + K := by linarith
  set Ks := Kstar z with hKs_def
  set y := (1 - K) / (1 + K) with hy
  set ys := (1 - Ks) / (1 + Ks) with hys
  have hy0 : 0 ≤ y := div_nonneg (by linarith) hK10.le
  have hyys : y ≤ ys := by
    rw [hy, hys, div_le_div_iff₀ hK10 hKs0]; nlinarith
  have hys3 : ys ≤ 1 / 3 := by
    rw [hys, div_le_iff₀ hKs0]; nlinarith
  -- monotonicity of φ
  have hφ : 16 * qS * y * ((qS ^ 2 - 1) - qS ^ 2 * y ^ 2) ≤ 16 * qS * ys * ((qS ^ 2 - 1) - qS ^ 2 * ys ^ 2) := by
    rw [hq]
    nlinarith [mul_nonneg (sub_nonneg.2 hyys) hy0, mul_nonneg (sub_nonneg.2 hyys) (sub_nonneg.2 hys3),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hyys) hy0) hy0, mul_nonneg (sub_nonneg.2 hyys) (mul_nonneg hy0 (sub_nonneg.2 hys3)),
      mul_nonneg (sub_nonneg.2 hyys) (mul_nonneg (sub_nonneg.2 hys3) (sub_nonneg.2 hys3))]
  have hφ0 : 0 ≤ 16 * qS * ys * ((qS ^ 2 - 1) - qS ^ 2 * ys ^ 2) := by
    rw [hq]
    have : 0 ≤ ys := hy0.trans hyys
    nlinarith [mul_nonneg this (sub_nonneg.2 hys3)]
  -- clear denominators in φ(ys)
  have hid : 16 * qS * ys * ((qS ^ 2 - 1) - qS ^ 2 * ys ^ 2) * (1 + Ks) ^ 3 =
      16 * qS * (qS ^ 2 - 1) * (1 - Ks) * (1 + Ks) ^ 2 - 16 * qS ^ 3 * (1 - Ks) ^ 3 := by
    rw [hys]
    field_simp
  have hpoly := lh_half_poly hz0 hz1
  rw [← hKs_def] at hpoly
  set rhs := 72 * (3 / 20 : ℝ) * (1 - Cz z) + 12 * (159 / 100 : ℝ) * (1 - Bz z ^ 2) with hrhs
  have hrhs0 : 0 ≤ rhs := by
    have hB : Bz z ≤ 1 := by
      unfold Bz
      nlinarith
    have hB0 : 0 ≤ Bz z := by
      unfold Bz
      positivity
    have hC : Cz z ≤ 1 := by
      unfold Cz
      nlinarith [pow_nonneg hz0 2, pow_nonneg hz0 3, mul_nonneg hz0 hz0,
        mul_nonneg (pow_nonneg hz0 2) (sub_nonneg.2 hz1)]
    rw [hrhs]
    nlinarith
  have hφle : 16 * qS * ys * ((qS ^ 2 - 1) - qS ^ 2 * ys ^ 2) ≤ rhs * (587 / 1000) * (693147 / 1000000) := by
    have h3 : 0 < (1 + Ks) ^ 3 := by positivity
    refine le_of_mul_le_mul_right ?_ h3
    linarith [hid, hpoly]
  rw [hd3_half K hK0, Pg3_half]
  have hc : 0 < (qS - 1) * Real.log 2 := mul_pos (by rw [hq]; norm_num) (by linarith [hL.1])
  rw [← hy]
  have : 16 * qS * y * ((qS ^ 2 - 1) - qS ^ 2 * y ^ 2) / ((qS - 1) * Real.log 2) ≤ rhs := by
    rw [div_le_iff₀ hc]
    have hr : qS - 1 = 587 / 1000 := by rw [hq]; norm_num
    rw [hr]
    have := mul_le_mul_of_nonneg_left hL.1.le (mul_nonneg hrhs0 (by norm_num : (0:ℝ) ≤ 587 / 1000))
    linarith [hφ, hφle]
  linarith


/-! ### The chart function and its derivatives -/

noncomputable def fS (z a : ℝ) : ℝ := hfun qS (kfun qS z) a + Pgen aL bL gL (Bz z) (Cz z) a
noncomputable def fS1 (z a : ℝ) : ℝ := hd1 qS (kfun qS z) a + Pg1 aL bL gL (Bz z) (Cz z) a
noncomputable def fS2 (z a : ℝ) : ℝ := hd2 qS (kfun qS z) a + Pg2 aL bL gL (Bz z) (Cz z) a
noncomputable def fS3 (z a : ℝ) : ℝ := hd3 qS (kfun qS z) a + Pg3 aL bL gL (Bz z) (Cz z) a
noncomputable def fS4 (z a : ℝ) : ℝ := hd4 qS (kfun qS z) a + Pg4 gL (Bz z)

theorem kfun_pos {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 < kfun qS z := by
  have := Kstar_le_kfun hz0 hz1
  have := Kstar_ge_k hz0 hz1
  linarith

section FChain
variable {z a : ℝ}

theorem hasDerivAt_fS (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (ha : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fS z) (fS1 z a) a :=
  (hasDerivAt_hfun (kfun_pos hz0 hz1) ha ha1).add (hasDerivAt_Pgen a)

theorem hasDerivAt_fS1 (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (ha : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fS1 z) (fS2 z a) a :=
  (hasDerivAt_hd1 (kfun_pos hz0 hz1) ha ha1).add (hasDerivAt_Pg1 a)

theorem hasDerivAt_fS2 (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (ha : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fS2 z) (fS3 z a) a :=
  (hasDerivAt_hd2 (kfun_pos hz0 hz1) ha ha1).add (hasDerivAt_Pg2 a)

theorem hasDerivAt_fS3 (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (ha : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fS3 z) (fS4 z a) a :=
  (hasDerivAt_hd3 (kfun_pos hz0 hz1) ha ha1).add (hasDerivAt_Pg3 a)

end FChain

/-- `f_aaaa < 0` on the large-head chart. -/
theorem fS4_neg {z a : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (ha : 1 / 2 ≤ a) (ha' : a ≤ 4 / 5) : fS4 z a < 0 := by
  have hKs := Kstar_le_kfun hz0 hz1
  have hk := Kstar_ge_k hz0 hz1
  unfold fS4
  rcases le_total z (1 / 2) with h | h
  · exact f4_neg_A ha ha' (by linarith) (kfun_le_A hz0 h) (by unfold Bz; nlinarith [sq_nonneg z])
  · exact f4_neg_B ha ha' (by linarith) (kfun_le_one hz0 hz1) (by unfold Bz; nlinarith)

/-- **`lem:fqe-large-head-curvature`: `f_aaa ≤ 0`** on `1/2 ≤ a ≤ 4/5`, `0 ≤ z ≤ 1`. -/
theorem fS3_nonpos {z a : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (ha : 1 / 2 ≤ a) (ha' : a ≤ 4 / 5) : fS3 z a ≤ 0 := by
  have h0 : fS3 z (1 / 2) ≤ 0 := by
    unfold fS3
    exact f3_half_nonpos hz0 hz1 (Kstar_le_kfun hz0 hz1) (kfun_le_one hz0 hz1)
  have := ge_of_deriv_nonpos_hd (f := fS3 z) (f' := fS4 z) ha
    (fun w hw => hasDerivAt_fS3 hz0 hz1 (by linarith [hw.1]) (by linarith [hw.2]))
    (fun w hw => (fS4_neg hz0 hz1 (by linarith [hw.1]) (by linarith [hw.2])).le)
  linarith


/-! ### The quadratic Hermite upper bound -/

/-- The quadratic Hermite interpolant of `f(·, z)` at the single node `1/2` and the double node `127/200`. -/
noncomputable def Qh (z a : ℝ) : ℝ :=
  fS z (127 / 200) + fS1 z (127 / 200) * (a - 127 / 200) +
    (fS z (1 / 2) - fS z (127 / 200) + 27 / 200 * fS1 z (127 / 200)) / (27 / 200) ^ 2 * (a - 127 / 200) ^ 2

theorem fS_le_Qh {z a : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (ha : 1 / 2 ≤ a) (ha' : a ≤ 4 / 5) :
    fS z a ≤ Qh z a := by
  set f0 := fS z (127 / 200) with hf0
  set D := fS1 z (127 / 200) with hD
  set A := (fS z (1 / 2) - f0 + 27 / 200 * D) / (27 / 200) ^ 2 with hA
  have hI : ∀ w ∈ Icc (1 / 2 : ℝ) (4 / 5), 0 < w ∧ w < 1 := fun w hw =>
    ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have key := hermite3_nonpos (A := 1 / 2) (B := 4 / 5) (m := 127 / 200) (by norm_num) (by norm_num)
    (R := fun w => fS z w - (f0 + D * (w - 127 / 200) + A * (w - 127 / 200) ^ 2))
    (R1 := fun w => fS1 z w - (D + 2 * A * (w - 127 / 200)))
    (R2 := fun w => fS2 z w - 2 * A) (R3 := fun w => fS3 z w)
    (fun w hw => by
      have h1 := hasDerivAt_fS hz0 hz1 (hI w hw).1 (hI w hw).2
      have h2 : HasDerivAt (fun w : ℝ => f0 + D * (w - 127 / 200) + A * (w - 127 / 200) ^ 2)
          (D + 2 * A * (w - 127 / 200)) w := by
        have := (((hasDerivAt_id w).sub_const (127 / 200 : ℝ)).const_mul D).const_add f0 |>.add
          ((((hasDerivAt_id w).sub_const (127 / 200 : ℝ)).pow 2).const_mul A)
        refine this.congr_deriv ?_
        simp
        ring
      exact h1.sub h2)
    (fun w hw => by
      have h1 := hasDerivAt_fS1 hz0 hz1 (hI w hw).1 (hI w hw).2
      have h2 : HasDerivAt (fun w : ℝ => D + 2 * A * (w - 127 / 200)) (2 * A) w := by
        have := ((hasDerivAt_id w).sub_const (127 / 200 : ℝ)).const_mul (2 * A) |>.const_add D
        refine this.congr_deriv ?_
        simp
      exact h1.sub h2)
    (fun w hw => by
      have h1 := hasDerivAt_fS2 hz0 hz1 (hI w hw).1 (hI w hw).2
      have h2 : HasDerivAt (fun w : ℝ => 2 * A) 0 w := hasDerivAt_const w (2 * A)
      exact (h1.sub h2).congr_deriv (by simp))
    (fun w hw => fS3_nonpos hz0 hz1 hw.1 hw.2)
    (by
      show fS z (1 / 2) - (f0 + D * (1 / 2 - 127 / 200) + A * (1 / 2 - 127 / 200) ^ 2) = 0
      have : f0 + D * (1 / 2 - 127 / 200) + A * (1 / 2 - 127 / 200) ^ 2 = fS z (1 / 2) := by
        rw [hA]; field_simp; ring
      rw [this]; ring)
    (by
      show fS z (127 / 200) - (f0 + D * (127 / 200 - 127 / 200) + A * (127 / 200 - 127 / 200) ^ 2) = 0
      rw [← hf0]; ring)
    (by
      show fS1 z (127 / 200) - (D + 2 * A * (127 / 200 - 127 / 200)) = 0
      rw [← hD]; ring)
  have := key a ⟨ha, ha'⟩
  show fS z a ≤ f0 + D * (a - 127 / 200) + A * (a - 127 / 200) ^ 2
  linarith

end FormalResearch.FourQubitEntropy.RenyiFull
