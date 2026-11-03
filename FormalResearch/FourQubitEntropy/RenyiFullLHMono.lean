module

public import FormalResearch.FourQubitEntropy.RenyiFullLHChart

/-!
# Large-head dual: the Hermite quadratic is decreasing in `K`

Paper E, `lem:fqe-large-head-dual`: with `Q = f_0(1-t²) + f_l t² + d(t + t²) D`, `t = (a-a_0)/d`, the
three `K`-dependent pieces are `h(a_0,K)`, `h(1/2,K)` and `h_a(a_0,K)`; their `K`-derivatives are
`-v_0/(Z_0 c)`, `-1/((1+K) c)` and `q u_0 v_0/(a_0 S c Z_0²)`, and `∂_K Q ≤ 0` on `K ∈ [13/25, 1]`,
`-d ≤ a - a_0 ≤ 33/200`, because `R = (a_0/S)^q ∈ [12/5, 5/2]`.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

section KDeriv
variable {q a : ℝ}

theorem hasDerivAt_hfun_K {K : ℝ} (hK : 0 < K) (ha : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fun K => hfun q K a) (-((1 - a) ^ q) / (lhZ q K a * ((q - 1) * Real.log 2))) K := by
  have hZ := lhZ_pos (q := q) hK ha ha1
  have hz : HasDerivAt (fun K : ℝ => lhZ q K a) ((1 - a) ^ q) K := by
    have := ((hasDerivAt_id K).mul_const ((1 - a) ^ q)).const_add (a ^ q)
    simpa [lhZ] using this
  have := (hz.log hZ.ne').neg.div_const ((q - 1) * Real.log 2)
  refine this.congr_deriv ?_
  field_simp

theorem hasDerivAt_hd1_K {K : ℝ} (hq : q ≠ 1) (hK : 0 < K) (ha : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fun K => hd1 q K a)
      (q * a ^ q * (1 - a) ^ q / (a * (1 - a) * ((q - 1) * Real.log 2) * lhZ q K a ^ 2)) K := by
  have hZ := lhZ_pos (q := q) hK ha ha1
  have h1a : 0 < 1 - a := by linarith
  have hu := Real.rpow_pos_of_pos ha q
  have hv := Real.rpow_pos_of_pos h1a q
  have hn : HasDerivAt (fun K : ℝ => a ^ q - K * (1 - a) ^ q) (-((1 - a) ^ q)) K := by
    have := ((hasDerivAt_id K).mul_const ((1 - a) ^ q)).const_sub (a ^ q)
    simpa using this
  have hd : HasDerivAt (fun K : ℝ => lhZ q K a) ((1 - a) ^ q) K := by
    have := ((hasDerivAt_id K).mul_const ((1 - a) ^ q)).const_add (a ^ q)
    simpa [lhZ] using this
  have hy := hn.div hd hZ.ne'
  have h2 := ((hy.sub_const (2 * a - 1)).const_mul (2 * q / (1 - (2 * a - 1) ^ 2))).neg.div_const
    ((q - 1) * Real.log 2)
  have e : (fun K => hd1 q K a) = fun K => -(2 * q / (1 - (2 * a - 1) ^ 2) *
      ((a ^ q - K * (1 - a) ^ q) / lhZ q K a - (2 * a - 1))) / ((q - 1) * Real.log 2) := by
    funext K'
    unfold hd1 lhm1 lhY
    ring
  rw [e]
  refine h2.congr_deriv ?_
  have hx : (1 - (2 * a - 1) ^ 2) = 4 * a * (1 - a) := by ring
  rw [hx]
  have hZ' := hZ.ne'
  unfold lhZ at hZ' ⊢
  have ha' := ha.ne'
  have h1a' := h1a.ne'
  have hc : (q - 1) * Real.log 2 ≠ 0 := by
    have : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have : q - 1 ≠ 0 := sub_ne_zero.2 hq
    positivity
  field_simp
  ring

end KDeriv


/-! ### The sign of `∂_K Q` -/

/-- Algebra: `E · (R+K)² (1+K) ≥ 0`. -/
theorem Ecleared {R K t : ℝ} (hR1 : 12 / 5 ≤ R) (hR2 : R ≤ 5 / 2) (hK1 : 13 / 25 ≤ K) (hK2 : K ≤ 1)
    (ht : t ≤ 11 / 9) :
    0 ≤ (1 + K) * (R + K - 42849 / 46355 * R * t) +
      t ^ 2 * ((R + K) * (R - 1) - 42849 / 46355 * R * (1 + K)) := by
  have hB1 : 0 ≤ (R + K) * (R - 1) - 42849 / 46355 * R * (1 + K) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hR1) (sub_nonneg.2 hK2), mul_nonneg (sub_nonneg.2 hR1) (sub_nonneg.2 hK1),
      mul_nonneg (sub_nonneg.2 hR2) (sub_nonneg.2 hK2), mul_nonneg (sub_nonneg.2 hR2) (sub_nonneg.2 hK1)]
  have hB2 : 0 ≤ R + K - 42849 / 46355 * R * t := by
    nlinarith [mul_nonneg (sub_nonneg.2 ht) (by linarith : (0 : ℝ) ≤ R)]
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + K) hB2
  have := mul_nonneg (sq_nonneg t) hB1
  linarith

theorem R_bounds : (12 / 5 : ℝ) ≤ (127 / 200 : ℝ) ^ qS / (1 - 127 / 200 : ℝ) ^ qS ∧
    (127 / 200 : ℝ) ^ qS / (1 - 127 / 200 : ℝ) ^ qS ≤ 5 / 2 := by
  have e : (127 / 200 : ℝ) ^ qS / (1 - 127 / 200 : ℝ) ^ qS = (127 / 73 : ℝ) ^ qS := by
    rw [← Real.div_rpow (by norm_num) (by norm_num)]
    norm_num
  rw [e]
  constructor
  · have := le_rpow_qS_Q (x := 127 / 73) (b := 12 / 5) (by norm_num) (by norm_num) (by decide +kernel)
    simpa using this
  · have := rpow_qS_le_Q (x := 127 / 73) (b := 5 / 2) (by norm_num) (by norm_num) (by decide +kernel)
    simpa using this


/-- The quadratic Hermite bound as a function of `K` (with the polynomial parts `p0, pl, pa`
at the nodes) and `x = a - 127/200`. -/
noncomputable def Qfun (p0 pl pa x K : ℝ) : ℝ :=
  (hfun qS K (127 / 200) + p0) * (1 - x ^ 2 / (27 / 200) ^ 2) +
    (hfun qS K (1 / 2) + pl) * (x ^ 2 / (27 / 200) ^ 2) +
    (hd1 qS K (127 / 200) + pa) * (x + x ^ 2 / (27 / 200))

theorem Qfun_deriv_nonpos {p0 pl pa x K : ℝ} (hK1 : 13 / 25 ≤ K) (hK2 : K ≤ 1)
    (hx1 : -(27 / 200) ≤ x) (hx2 : x ≤ 33 / 200) :
    HasDerivAt (Qfun p0 pl pa x)
      ((1 - x ^ 2 / (27 / 200) ^ 2) * (-((1 - 127 / 200 : ℝ) ^ qS) / (lhZ qS K (127 / 200) * ((qS - 1) * Real.log 2))) +
        x ^ 2 / (27 / 200) ^ 2 * (-((1 - 1 / 2 : ℝ) ^ qS) / (lhZ qS K (1 / 2) * ((qS - 1) * Real.log 2))) +
        (x + x ^ 2 / (27 / 200)) * (qS * (127 / 200 : ℝ) ^ qS * (1 - 127 / 200 : ℝ) ^ qS /
          ((127 / 200) * (1 - 127 / 200) * ((qS - 1) * Real.log 2) * lhZ qS K (127 / 200) ^ 2))) K := by
  have hK : 0 < K := by linarith
  have hq : qS ≠ 1 := by unfold qS; norm_num
  have h0 := hasDerivAt_hfun_K (q := qS) (a := 127 / 200) hK (by norm_num) (by norm_num)
  have hl := hasDerivAt_hfun_K (q := qS) (a := 1 / 2) hK (by norm_num) (by norm_num)
  have ha := hasDerivAt_hd1_K (q := qS) (a := 127 / 200) hq hK (by norm_num) (by norm_num)
  have := ((((h0.add_const p0).mul_const (1 - x ^ 2 / (27 / 200) ^ 2)).add
    ((hl.add_const pl).mul_const (x ^ 2 / (27 / 200) ^ 2))).add
    ((ha.add_const pa).mul_const (x + x ^ 2 / (27 / 200))))
  exact this.congr_deriv (by ring)


/-- Pure algebra: the `K`-derivative of `Q` as `-E/c`. -/
theorem Dexpr_eq {v0 vl R K t c : ℝ} (hv0 : v0 ≠ 0) (hvl : vl ≠ 0) (hc : c ≠ 0) (hRK : R + K ≠ 0)
    (hK1 : 1 + K ≠ 0) :
    (1 - t ^ 2) * (-v0 / ((R * v0 + K * v0) * c)) + t ^ 2 * (-vl / ((vl + K * vl) * c)) +
      (27 / 200) * (t + t ^ 2) * ((1587 / 1000) * (R * v0) * v0 /
        ((127 / 200) * (73 / 200) * c * (R * v0 + K * v0) ^ 2)) =
    -((1 + K) * (R + K - 42849 / 46355 * R * t) +
      t ^ 2 * ((R + K) * (R - 1) - 42849 / 46355 * R * (1 + K))) / (c * (R + K) ^ 2 * (1 + K)) := by
  field_simp
  ring


theorem QD_nonpos_abs {q u0 v0 vl K x c : ℝ} (hq : q = 1587 / 1000) (hv0 : 0 < v0) (hu1 : 12 / 5 * v0 ≤ u0) (hu2 : u0 ≤ 5 / 2 * v0)
    (hvl : 0 < vl) (hc : 0 < c) (hK1 : 13 / 25 ≤ K) (hK2 : K ≤ 1) (hx2 : x ≤ 33 / 200) :
    (1 - x ^ 2 / (27 / 200) ^ 2) * (-v0 / ((u0 + K * v0) * c)) +
        x ^ 2 / (27 / 200) ^ 2 * (-vl / ((vl + K * vl) * c)) +
        (x + x ^ 2 / (27 / 200)) * (q * u0 * v0 / ((127 / 200) * (73 / 200) * c * (u0 + K * v0) ^ 2)) ≤ 0 := by
  subst hq
  set R : ℝ := u0 / v0 with hR
  have hRu : u0 = R * v0 := by rw [hR]; exact (div_mul_cancel₀ _ hv0.ne').symm
  have hR1 : 12 / 5 ≤ R := by rw [hR, le_div_iff₀ hv0]; linarith
  have hR2 : R ≤ 5 / 2 := by rw [hR, div_le_iff₀ hv0]; linarith
  have e2 : x ^ 2 / (27 / 200) ^ 2 = (x / (27 / 200)) ^ 2 := by ring
  have e3 : x + x ^ 2 / (27 / 200) = (27 / 200) * (x / (27 / 200) + (x / (27 / 200)) ^ 2) := by
    field_simp
  rw [e2, e3, hRu]
  have key := Dexpr_eq (v0 := v0) (vl := vl) (R := R) (K := K) (t := x / (27 / 200)) (c := c) hv0.ne' hvl.ne'
    hc.ne' (by linarith) (by linarith)
  rw [mul_assoc (27 / 200 : ℝ) _ _] at key
  have key2 : (1 - (x / (27 / 200)) ^ 2) * (-v0 / ((R * v0 + K * v0) * c)) +
      (x / (27 / 200)) ^ 2 * (-vl / ((vl + K * vl) * c)) +
      (27 / 200 * (x / (27 / 200) + (x / (27 / 200)) ^ 2)) * (1587 / 1000 * (R * v0) * v0 /
        (127 / 200 * (73 / 200) * c * (R * v0 + K * v0) ^ 2)) =
      -((1 + K) * (R + K - 42849 / 46355 * R * (x / (27 / 200))) +
        (x / (27 / 200)) ^ 2 * ((R + K) * (R - 1) - 42849 / 46355 * R * (1 + K))) / (c * (R + K) ^ 2 * (1 + K)) := by
    rw [← key]
    ring
  rw [key2]
  have hE := Ecleared hR1 hR2 hK1 hK2 (t := x / (27 / 200)) (by rw [div_le_iff₀ (by norm_num)]; linarith)
  have hden : 0 < c * (R + K) ^ 2 * (1 + K) := by
    have : 0 < R + K := by linarith
    positivity
  rw [neg_div]
  exact neg_nonpos.2 (div_nonneg hE hden.le)

theorem QD_nonpos {x K : ℝ} (hK1 : 13 / 25 ≤ K) (hK2 : K ≤ 1) (hx1 : -(27 / 200) ≤ x) (hx2 : x ≤ 33 / 200) :
    (1 - x ^ 2 / (27 / 200) ^ 2) * (-((1 - 127 / 200 : ℝ) ^ qS) / (lhZ qS K (127 / 200) * ((qS - 1) * Real.log 2))) +
        x ^ 2 / (27 / 200) ^ 2 * (-((1 - 1 / 2 : ℝ) ^ qS) / (lhZ qS K (1 / 2) * ((qS - 1) * Real.log 2))) +
        (x + x ^ 2 / (27 / 200)) * (qS * (127 / 200 : ℝ) ^ qS * (1 - 127 / 200 : ℝ) ^ qS /
          ((127 / 200) * (1 - 127 / 200) * ((qS - 1) * Real.log 2) * lhZ qS K (127 / 200) ^ 2)) ≤ 0 := by
  have hRb := R_bounds
  have hL := log2_bounds
  have hv0p : 0 < (1 - 127 / 200 : ℝ) ^ qS := Real.rpow_pos_of_pos (by norm_num) _
  have hvlp : 0 < (1 / 2 : ℝ) ^ qS := Real.rpow_pos_of_pos (by norm_num) _
  have hc : 0 < (qS - 1) * Real.log 2 := mul_pos (by unfold qS; norm_num) (by linarith [hL.1])
  have hu1 : 12 / 5 * (1 - 127 / 200 : ℝ) ^ qS ≤ (127 / 200 : ℝ) ^ qS := by
    have := hRb.1
    rwa [le_div_iff₀ hv0p] at this
  have hu2 : (127 / 200 : ℝ) ^ qS ≤ 5 / 2 * (1 - 127 / 200 : ℝ) ^ qS := by
    have := hRb.2
    rwa [div_le_iff₀ hv0p] at this
  have hvl : (1 - 1 / 2 : ℝ) ^ qS = (1 / 2 : ℝ) ^ qS := by norm_num
  have hZ0 : lhZ qS K (127 / 200) = (127 / 200 : ℝ) ^ qS + K * (1 - 127 / 200 : ℝ) ^ qS := rfl
  have hZl : lhZ qS K (1 / 2) = (1 / 2 : ℝ) ^ qS + K * (1 / 2 : ℝ) ^ qS := by
    unfold lhZ; rw [hvl]
  have hh := QD_nonpos_abs (u0 := (127 / 200 : ℝ) ^ qS) (v0 := (1 - 127 / 200 : ℝ) ^ qS) (vl := (1 / 2 : ℝ) ^ qS)
    (K := K) (x := x) (c := (qS - 1) * Real.log 2) (q := qS) rfl hv0p hu1 hu2 hvlp hc hK1 hK2 hx2
  rw [hZ0, hZl, hvl]
  have e1 : (1 - 127 / 200 : ℝ) = 73 / 200 := by norm_num
  have hq : qS = 1587 / 1000 := rfl
  rw [e1] at hh ⊢
  exact hh


/-- **`Q` is decreasing in `K` on `[13/25, 1]`.** -/
theorem Qfun_anti {p0 pl pa x K1 K2 : ℝ} (h1 : 13 / 25 ≤ K1) (h12 : K1 ≤ K2) (h2 : K2 ≤ 1)
    (hx1 : -(27 / 200) ≤ x) (hx2 : x ≤ 33 / 200) :
    Qfun p0 pl pa x K2 ≤ Qfun p0 pl pa x K1 :=
  ge_of_deriv_nonpos_hd h12
    (fun K hK => Qfun_deriv_nonpos (by linarith [hK.1]) (by linarith [hK.2]) hx1 hx2)
    (fun K hK => QD_nonpos (by linarith [hK.1]) (by linarith [hK.2]) hx1 hx2)

theorem Qh_eq_Qfun (z a : ℝ) :
    Qh z a = Qfun (Pgen aL bL gL (Bz z) (Cz z) (127 / 200)) (Pgen aL bL gL (Bz z) (Cz z) (1 / 2))
      (Pg1 aL bL gL (Bz z) (Cz z) (127 / 200)) (a - 127 / 200) (kfun qS z) := by
  unfold Qh Qfun fS fS1
  ring

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.Qfun_anti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qfun_anti

end FormalResearch.FourQubitEntropy.RenyiFull
