module

public import FormalResearch.Special.DiscreteAiryKappaSharpParam

/-!
# Sharp `κ`: the explicit error bounds at a node (plan K1, sharp constant, step 14)

Pure real lemmas turning the lattice facts `A² ≤ k₀ δ³` (`k₀ = ⌈A²/δ³⌉`) and `δ ≤ 1` into the linear-in-`δ` bounds
`S ≤ K_S δ`, `E ≤ K_E δ`, `a ≤ (2A + 3δ)/q_*`, `l ≤ 8C_l(A + δ/A)`, `ζ ≤ K_Z A + K_3 δ` (`ksfin_S`, `ksfin_E`, `ksfin_a`, `ksfin_l`, `ksfin_z`)
used by `ksfin_node`.

**Claim class: proved.**
-/

@[expose] public section

namespace FormalResearch.Special

/-- The band error scale: `S ≤ K_S δ`. -/
lemma ksfin_S {x A δ β mσ k0 : ℝ} (hx : 0 < x) (hA : 0 < A) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : A ^ 2 ≤ k0 * δ ^ 3) (hk0 : 0 < k0)
    (hβ : 0 ≤ β) (hmσ : 0 ≤ mσ) :
    200 / (x * A ^ 9) * (δ ^ 3 + 2 * (3 * β + mσ) / k0) ≤ 200 * (1 + 2 * (3 * β + mσ) / A ^ 2) / (x * A ^ 9) * δ := by
  have hδ3 : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  have h1 : 1 / k0 ≤ δ ^ 3 / A ^ 2 := by
    rw [div_le_div_iff₀ hk0 (by positivity)]
    linarith
  have h2 : 2 * (3 * β + mσ) / k0 ≤ 2 * (3 * β + mσ) / A ^ 2 * δ := by
    have e : 2 * (3 * β + mσ) / k0 = 2 * (3 * β + mσ) * (1 / k0) := by ring
    rw [e]
    have : 2 * (3 * β + mσ) * (1 / k0) ≤ 2 * (3 * β + mσ) * (δ ^ 3 / A ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    refine this.trans ?_
    have e2 : 2 * (3 * β + mσ) * (δ ^ 3 / A ^ 2) = 2 * (3 * β + mσ) / A ^ 2 * δ ^ 3 := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left hδ3 (by positivity)
  have e3 : 200 * (1 + 2 * (3 * β + mσ) / A ^ 2) / (x * A ^ 9) * δ =
      200 / (x * A ^ 9) * (δ + 2 * (3 * β + mσ) / A ^ 2 * δ) := by ring
  rw [e3]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The bond-match error: `E ≤ K_E δ`. -/
lemma ksfin_E {x A δ β Cr qs c1s k0 : ℝ} (hx : 0 < x) (hA : 0 < A) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : A ^ 2 ≤ k0 * δ ^ 3) (hk0 : 0 < k0)
    (hβ : 0 ≤ β) (hCr : 0 ≤ Cr) (hqs : 0 < qs) (hc1s : 0 < c1s) :
    ksfE x A δ (3 * β / k0 ^ 2) Cr ((2 * qs / (c1s * A ^ 2)) ^ (3 / 2 : ℝ) * δ ^ 3) ≤
      (6 * ((3 / (A * x ^ 2) + 2 * (1 + 3 * β / A ^ 4) / x ^ 4) / x) / A ^ 2 + 8 * (Cr + (2 * qs / (c1s * A ^ 2)) ^ (3 / 2 : ℝ) / 8) / A) * δ := by
  have hδ3 : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  have hδ2 : δ ^ 2 * √δ ≤ δ := by
    have h0 : √δ ≤ 1 := by rw [Real.sqrt_le_one]; exact hδ1
    have h1 : δ ^ 2 ≤ δ := by nlinarith
    have : δ ^ 2 * √δ ≤ δ * 1 := mul_le_mul h1 h0 (Real.sqrt_nonneg _) hδ.le
    linarith
  set KY : ℝ := (2 * qs / (c1s * A ^ 2)) ^ (3 / 2 : ℝ) with hKY
  have hKY0 : 0 ≤ KY := by rw [hKY]; positivity
  have hη : 3 * β / k0 ^ 2 ≤ 3 * β / A ^ 4 * δ := by
    have h1 : A ^ 4 ≤ k0 ^ 2 * δ ^ 6 := by
      have := pow_le_pow_left₀ (by positivity) hk 2
      nlinarith [this]
    rw [div_le_iff₀ (by positivity)]
    have e : 3 * β / A ^ 4 * δ * k0 ^ 2 = 3 * β * (δ * k0 ^ 2) / A ^ 4 := by ring
    rw [e, le_div_iff₀ (by positivity)]
    have h2 : δ ^ 6 ≤ δ := by nlinarith [pow_pos hδ 5, pow_pos hδ 4, pow_pos hδ 2]
    nlinarith [mul_nonneg hβ (sq_nonneg k0), mul_le_mul_of_nonneg_left h2 (mul_nonneg hβ (sq_nonneg k0)), h1,
      mul_le_mul_of_nonneg_left h1 hβ]
  unfold ksfE
  have hη0 : 0 ≤ 3 * β / A ^ 4 := by positivity
  have t1 : 2 * (δ ^ 3 + 3 * β / k0 ^ 2) / x ^ 4 ≤ 2 * (1 + 3 * β / A ^ 4) / x ^ 4 * δ := by
    have : 2 * (δ ^ 3 + 3 * β / k0 ^ 2) ≤ 2 * (1 + 3 * β / A ^ 4) * δ := by nlinarith
    calc 2 * (δ ^ 3 + 3 * β / k0 ^ 2) / x ^ 4 ≤ 2 * (1 + 3 * β / A ^ 4) * δ / x ^ 4 :=
          div_le_div_of_nonneg_right this (by positivity)
      _ = _ := by ring
  have t2 : 3 * δ ^ 3 / (A * x ^ 2) ≤ 3 / (A * x ^ 2) * δ := by
    have : 3 * δ ^ 3 ≤ 3 * δ := by linarith
    calc 3 * δ ^ 3 / (A * x ^ 2) ≤ 3 * δ / (A * x ^ 2) := div_le_div_of_nonneg_right this (by positivity)
      _ = _ := by ring
  have t3 : (3 * δ ^ 3 / (A * x ^ 2) + 2 * (δ ^ 3 + 3 * β / k0 ^ 2) / x ^ 4) / x ≤
      (3 / (A * x ^ 2) + 2 * (1 + 3 * β / A ^ 4) / x ^ 4) / x * δ := by
    have : 3 * δ ^ 3 / (A * x ^ 2) + 2 * (δ ^ 3 + 3 * β / k0 ^ 2) / x ^ 4 ≤
        (3 / (A * x ^ 2) + 2 * (1 + 3 * β / A ^ 4) / x ^ 4) * δ := by linarith
    calc _ ≤ (3 / (A * x ^ 2) + 2 * (1 + 3 * β / A ^ 4) / x ^ 4) * δ / x := div_le_div_of_nonneg_right this hx.le
      _ = _ := by ring
  have t4 : 6 * ((3 * δ ^ 3 / (A * x ^ 2) + 2 * (δ ^ 3 + 3 * β / k0 ^ 2) / x ^ 4) / x) / A ^ 2 ≤
      6 * ((3 / (A * x ^ 2) + 2 * (1 + 3 * β / A ^ 4) / x ^ 4) / x) / A ^ 2 * δ := by
    calc _ ≤ 6 * ((3 / (A * x ^ 2) + 2 * (1 + 3 * β / A ^ 4) / x ^ 4) / x * δ) / A ^ 2 :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  have t5 : 4 * (2 * (Cr * (δ ^ 2 * √δ) + KY * δ ^ 3 / 8)) / A ≤ 8 * (Cr + KY / 8) / A * δ := by
    have : 4 * (2 * (Cr * (δ ^ 2 * √δ) + KY * δ ^ 3 / 8)) ≤ 8 * (Cr + KY / 8) * δ := by
      have h1 : Cr * (δ ^ 2 * √δ) ≤ Cr * δ := mul_le_mul_of_nonneg_left hδ2 hCr
      have h2 : KY * δ ^ 3 ≤ KY * δ := mul_le_mul_of_nonneg_left hδ3 hKY0
      nlinarith
    calc _ ≤ 8 * (Cr + KY / 8) * δ / A := div_le_div_of_nonneg_right this hA.le
      _ = _ := by ring
  linarith

/-- The profile-sum defect: `q_{k₀-1}/q_* + √(1 - (q_{b-1}/q_*)²) ≤ (2A + 3δ)/q_*`. -/
lemma ksfin_a {qs A δ q1 q2 qA : ℝ} (hqs : 0 < qs) (hqs1 : qs ≤ 1) (hA : 0 < A) (hAq : A ≤ qs / 2) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδq : δ ≤ qs / 8)
    (hq1 : q1 ≤ A ^ 2 + δ ^ 3) (hqA : qA ^ 2 = qs ^ 2 - A ^ 2) (hqA0 : 0 ≤ qA) (hq2 : qA - 2 * δ ^ 3 ≤ q2) (hq2q : q2 ≤ qA) :
    q1 / qs + √(1 - (q2 / qs) ^ 2) ≤ (2 * A + 3 * δ) / qs := by
  have hδ3 : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  have hqsq : qs ^ 2 - q2 ^ 2 ≤ A ^ 2 + 4 * δ ^ 3 := by
    have h1 : (qA - 2 * δ ^ 3) ^ 2 ≤ q2 ^ 2 := by
      have : 0 ≤ qA - 2 * δ ^ 3 := by
        have : qs * (4 / 5) ≤ qA := by
          rw [← Real.sqrt_sq hqA0]
          apply Real.le_sqrt_of_sq_le
          nlinarith [mul_self_le_mul_self hA.le hAq, sq_nonneg qs]
        linarith
      exact pow_le_pow_left₀ this hq2 2
    have hqA1 : qA ≤ 1 := by nlinarith [sq_nonneg A]
    have h5 : δ ^ 3 * qA ≤ δ ^ 3 := by nlinarith [pow_pos hδ 3]
    nlinarith [pow_pos hδ 6]
  have h2 : 1 - (q2 / qs) ^ 2 = (qs ^ 2 - q2 ^ 2) / qs ^ 2 := by field_simp
  have h3 : √(1 - (q2 / qs) ^ 2) ≤ (A + 2 * δ) / qs := by
    rw [h2, Real.sqrt_le_left (by positivity)]
    rw [div_pow, div_le_div_iff_of_pos_right (by positivity)]
    have h32 : δ ^ 3 ≤ δ ^ 2 := by nlinarith [pow_pos hδ 2]
    have : A ^ 2 + 4 * δ ^ 3 ≤ (A + 2 * δ) ^ 2 := by nlinarith [mul_pos hA hδ]
    linarith
  have h4 : q1 / qs ≤ (A + δ) / qs := by
    apply div_le_div_of_nonneg_right _ hqs.le
    nlinarith
  have : (2 * A + 3 * δ) / qs = (A + δ) / qs + (A + 2 * δ) / qs := by ring
  linarith

/-- The left coefficient: `k₀ C_l (8/A)/N ≤ 8 C_l (A + δ/A)` for `k₀ δ³ < A² + δ³`. -/
lemma ksfin_l {A δ CL k0 : ℝ} (hA : 0 < A) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hCL : 0 ≤ CL) (hk : k0 * δ ^ 3 < A ^ 2 + δ ^ 3) :
    k0 * (CL * (8 / A)) / (1 / δ ^ 3) ≤ 8 * CL * (A + δ / A) := by
  have hδ3 : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  have e : k0 * (CL * (8 / A)) / (1 / δ ^ 3) = (k0 * δ ^ 3) * (8 * CL / A) := by field_simp
  rw [e]
  have h1 : (k0 * δ ^ 3) * (8 * CL / A) ≤ (A ^ 2 + δ ^ 3) * (8 * CL / A) :=
    mul_le_mul_of_nonneg_right hk.le (by positivity)
  refine h1.trans ?_
  have e2 : (A ^ 2 + δ ^ 3) * (8 * CL / A) = 8 * CL * (A + δ ^ 3 / A) := by field_simp
  rw [e2]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have : δ ^ 3 / A ≤ δ / A := div_le_div_of_nonneg_right hδ3 hA.le
  linarith

/-- `kszK3` is monotone in `R_c`. -/
lemma kszK3_mono {c1 G C Rc Rc' : ℝ} (h : Rc ≤ Rc') : kszK3 c1 G C Rc ≤ kszK3 c1 G C Rc' := by
  unfold kszK3
  have : 2 * (C + 1) ^ 2 * Rc ≤ 2 * (C + 1) ^ 2 * Rc' := mul_le_mul_of_nonneg_left h (by positivity)
  linarith

/-- The zone coefficient `ζ ≤ K_Z A + K_3 δ`. -/
lemma ksfin_z {K : KsfConst} (P : K.Pos) {A δ : ℝ} (hA : 0 < A) (hA1 : A ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδA : δ ≤ A ^ 2) :
    2 * K.gmax ^ 2 * (√(K.c2s * (A ^ 2 / K.qs + δ ^ 3)) / Real.pi + 2 * K.c2 * (K.c2s * (A ^ 2 / K.qs + δ ^ 3))) / K.c1 +
      kszK3 K.c1 K.gmax K.C (A ^ 2 / K.qs + 4 * δ ^ 3) * δ ≤ kfKZ K * A + kfK3 K * δ := by
  have hqs := P.hqs
  have hc1 := P.hc1
  have hδ3 : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  have hA2 : A ^ 2 ≤ A := by nlinarith
  set R0 : ℝ := K.c2s * (A ^ 2 / K.qs + δ ^ 3) with hR0
  have hR0b : R0 ≤ kfρ0 K ^ 2 * A ^ 2 := by
    have hρ : kfρ0 K ^ 2 = K.c2s * (1 / K.qs + 1) := by
      unfold kfρ0; rw [Real.sq_sqrt (by have := P.hc2s; positivity)]
    rw [hρ, hR0]
    have : A ^ 2 / K.qs + δ ^ 3 ≤ (1 / K.qs + 1) * A ^ 2 := by
      have e : (1 / K.qs + 1) * A ^ 2 = A ^ 2 / K.qs + A ^ 2 := by ring
      rw [e]; linarith
    calc K.c2s * (A ^ 2 / K.qs + δ ^ 3) ≤ K.c2s * ((1 / K.qs + 1) * A ^ 2) := mul_le_mul_of_nonneg_left this P.hc2s.le
      _ = _ := by ring
  have hR00 : 0 ≤ R0 := by have := P.hc2s; rw [hR0]; positivity
  have hsq : √R0 ≤ kfρ0 K * A := by
    rw [Real.sqrt_le_left (by unfold kfρ0; positivity)]
    nlinarith
  have hs : √R0 / Real.pi + 2 * K.c2 * R0 ≤ (kfρ0 K / Real.pi + 2 * K.c2 * kfρ0 K ^ 2) * A := by
    have h1 : √R0 / Real.pi ≤ kfρ0 K * A / Real.pi := div_le_div_of_nonneg_right hsq Real.pi_pos.le
    have h2 : 2 * K.c2 * R0 ≤ 2 * K.c2 * (kfρ0 K ^ 2 * A) := by
      apply mul_le_mul_of_nonneg_left _ (by have := P.hc2; positivity)
      nlinarith [sq_nonneg (kfρ0 K)]
    have e : (kfρ0 K / Real.pi + 2 * K.c2 * kfρ0 K ^ 2) * A = kfρ0 K * A / Real.pi + 2 * K.c2 * (kfρ0 K ^ 2 * A) := by ring
    rw [e]; linarith
  have hz1 : 2 * K.gmax ^ 2 * (√R0 / Real.pi + 2 * K.c2 * R0) / K.c1 ≤ kfKZ K * A := by
    unfold kfKZ
    have : 2 * K.gmax ^ 2 * (√R0 / Real.pi + 2 * K.c2 * R0) ≤ 2 * K.gmax ^ 2 * ((kfρ0 K / Real.pi + 2 * K.c2 * kfρ0 K ^ 2) * A) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    calc _ ≤ 2 * K.gmax ^ 2 * ((kfρ0 K / Real.pi + 2 * K.c2 * kfρ0 K ^ 2) * A) / K.c1 := div_le_div_of_nonneg_right this hc1.le
      _ = _ := by ring
  have hz2 : kszK3 K.c1 K.gmax K.C (A ^ 2 / K.qs + 4 * δ ^ 3) ≤ kfK3 K := by
    unfold kfK3
    apply kszK3_mono
    have h1 : A ^ 2 / K.qs ≤ 1 / K.qs := div_le_div_of_nonneg_right (by nlinarith) hqs.le
    linarith
  have := mul_le_mul_of_nonneg_right hz2 hδ.le
  linarith

end FormalResearch.Special
