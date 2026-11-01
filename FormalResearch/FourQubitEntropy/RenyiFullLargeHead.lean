import FormalResearch.FourQubitEntropy.RenyiFullLHFinalCells
import FormalResearch.FourQubitEntropy.RenyiFullRD

/-!
# `lem:fqe-large-head-dual`: `LargeHeadDual`

Paper E, `renyi_large_head_dual.tex`.  For `z ∈ [0,1]`, `1/2 ≤ a ≤ 4/5`:

1. `f(a,z) ≤ Q_h(a,z)` (quadratic Hermite interpolation at `1/2` and the double node `127/200`;
   `f_aaa ≤ 0`, `lem:fqe-large-head-curvature`, `fS3_nonpos`);
2. `Q_h` is decreasing in `K` on `[13/25, 1]` (`Qfun_anti`), and `K ≥ κ(z)` (`kap_le_kfun`);
3. at `K = κ(z)` the three entropy terms are replaced by rational functions with explicit error bounds
   (`H0_approx`, `Hl_approx`, `Ha_approx`), and the resulting quadratic in `t = (a-a_0)/d` is positive by the exact
   rational certificate of `RenyiFullLHFinalCells`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

theorem kap_bounds {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 13 / 25 ≤ kap z ∧ kap z ≤ 1 := by
  unfold kap
  have z2 : z ^ 2 ≤ 1 := by nlinarith
  have z3 : z ^ 3 ≤ 1 := by nlinarith [sq_nonneg z, pow_nonneg hz0 3]
  have z2' := pow_nonneg hz0 2
  have z3' := pow_nonneg hz0 3
  constructor <;> nlinarith

/-- `Q ≤ F` for `v ∈ [13/25, 1]`, `x ∈ [-d, 33/200]` (the rational approximations `(LH2)`). -/
theorem Qfun_le_lhF {p0 pl pa x v : ℝ} (hv1 : 13 / 25 ≤ v) (hv2 : v ≤ 1) (hx1 : -(27 / 200) ≤ x)
    (hx2 : x ≤ 33 / 200) : Qfun p0 pl pa x v ≤ lhF v p0 pl pa (x / (27 / 200)) := by
  set t := x / (27 / 200) with ht
  have hx : x = 27 / 200 * t := by rw [ht]; field_simp
  have ht1 : -1 ≤ t := by rw [ht, le_div_iff₀ (by norm_num)]; linarith
  have ht2 : t ≤ 11 / 9 := by rw [ht, div_le_iff₀ (by norm_num)]; linarith
  have e1 : x ^ 2 / (27 / 200) ^ 2 = t ^ 2 := by rw [ht]; ring
  have e2 : x + x ^ 2 / (27 / 200) = 27 / 200 * (t + t ^ 2) := by rw [hx]; ring
  have a0 := H0_approx hv1 hv2
  have al := Hl_approx hv1 hv2
  have aa := Ha_approx hv1 hv2
  unfold Qfun lhF
  rw [e1, e2]
  have t2 : 0 ≤ t ^ 2 := sq_nonneg t
  have t2b : t ^ 2 ≤ 121 / 81 := by nlinarith
  have b0 : |1 - t ^ 2| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
  have bl : |t ^ 2| ≤ 121 / 81 := by rw [abs_of_nonneg t2]; exact t2b
  have ba : |27 / 200 * (t + t ^ 2)| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have c0 : |(hfun qS v (127 / 200) - hh0 v) * (1 - t ^ 2)| ≤ 1 / 10000 := by
    rw [abs_mul]
    calc |hfun qS v (127 / 200) - hh0 v| * |1 - t ^ 2| ≤ 1 / 10000 * 1 :=
          mul_le_mul a0 b0 (abs_nonneg _) (by norm_num)
      _ = 1 / 10000 := by norm_num
  have cl : (hfun qS v (1 / 2) - hhl v) * t ^ 2 ≤ 6 / 10000 * t ^ 2 :=
    mul_le_mul_of_nonneg_right (abs_le.1 al).2 t2
  have ca : |(hd1 qS v (127 / 200) - hha v) * (27 / 200 * (t + t ^ 2))| ≤ 1 / 10 ^ 6 := by
    rw [abs_mul]
    calc |hd1 qS v (127 / 200) - hha v| * |27 / 200 * (t + t ^ 2)| ≤ 1 / 10 ^ 6 * 1 :=
          mul_le_mul aa ba (abs_nonneg _) (by norm_num)
      _ = 1 / 10 ^ 6 := by norm_num
  have c0' := (abs_le.1 c0).2
  have ca' := (abs_le.1 ca).2
  nlinarith [c0', ca', cl]

/-- The final positivity: `F < T` for every real `t`, on the whole `z`-range. -/
theorem lhF_lt {z t : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    lhF (kap z) (P0z z) (Plz z) (Paz z) t < 2507333 / 1500000 := by
  have hk := kap_bounds hz0 hz1
  have hk0 : 0 < kap z := by linarith [hk.1]
  have h1 : 2 * (240792594 / 10 ^ 8 : ℝ) + kap z + 3 / 4 ≠ 0 := by
    apply ne_of_gt; linarith
  have h2 : kap z + 11 / 4 ≠ 0 := by apply ne_of_gt; linarith
  have h3 : 240792594 / 10 ^ 8 + kap z ≠ 0 := by apply ne_of_gt; linarith
  have hid := lh_identity (v := kap z) (p0 := P0z z) (pl := Plz z) (pa := Paz z) (t := t) h1 h2 h3
  have hE : 0 < lhE (kap z) := by
    unfold lhE
    have : 0 < kap z + 2 * (240792594 / 10 ^ 8 : ℝ) + 3 / 4 := by linarith
    have : 0 < kap z + 11 / 4 := by linarith
    have : 0 < kap z + 240792594 / 10 ^ 8 := by linarith
    positivity
  have hc2 := lhc2_ge hz0 hz1
  have hdet := lh_det_ge hz0 hz1
  set c0 := lhc0 (kap z) (P0z z)
  set c1 := lhc1 (kap z) (Paz z)
  set c2 := lhc2 (kap z) (P0z z) (Plz z) (Paz z)
  have hq : 0 < c0 + c1 * t + c2 * t ^ 2 := by
    have h4 : 0 < 4 * c2 * (c0 + c1 * t + c2 * t ^ 2) := by
      nlinarith [sq_nonneg (2 * c2 * t + c1)]
    have : 0 < c2 := by linarith
    by_contra hcon
    push Not at hcon
    nlinarith
  have : 0 < lhE (kap z) * (2507333 / 1500000 - lhF (kap z) (P0z z) (Plz z) (Paz z) t) := by
    rw [hid]; exact hq
  have := (mul_pos_iff_of_pos_left hE).1 this
  linarith


/-- The chart parametrisation: `(a, b, c, c)` with `b = (1-a)(1+2z)/3`, `c = (1-a)(1-z)/3`. -/
theorem lam_chart_eq {a z : ℝ} (ha : a < 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Lam qS aL bL gL ![a, (1 - a) * (1 + 2 * z) / 3, (1 - a) * (1 - z) / 3, (1 - a) * (1 - z) / 3] =
      fS z a := by
  have h1a : 0 < 1 - a := by linarith
  have hq0 : (0 : ℝ) < qS := by unfold qS; norm_num
  -- the power sum
  have hsum : ∑ i, (![a, (1 - a) * (1 + 2 * z) / 3, (1 - a) * (1 - z) / 3, (1 - a) * (1 - z) / 3] :
      Fin 4 → ℝ) i ^ qS = lhZ qS (kfun qS z) a := by
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    unfold lhZ kfun
    have h3 : (0 : ℝ) < 3 ^ qS := Real.rpow_pos_of_pos (by norm_num) _
    rw [Real.div_rpow (by positivity) (by norm_num), Real.div_rpow (by positivity) (by norm_num),
      Real.mul_rpow h1a.le (by linarith), Real.mul_rpow h1a.le (by linarith)]
    field_simp
    ring
  have hent : renyiSpec qS ![a, (1 - a) * (1 + 2 * z) / 3, (1 - a) * (1 - z) / 3, (1 - a) * (1 - z) / 3] =
      hfun qS (kfun qS z) a := by
    unfold renyiSpec hfun
    rw [hsum]
    unfold Real.logb
    have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hq1 : (1 - qS) ≠ 0 := by unfold qS; norm_num
    have hq2 : (qS - 1) ≠ 0 := by unfold qS; norm_num
    field_simp
    ring
  unfold Lam
  rw [hent, pur_abcc, cub_abcc]
  unfold fS Pgen Bz Cz
  ring


/-- **`f(a,z) < T`** on the large-head chart. -/
theorem fS_lt {z a : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (ha : 1 / 2 ≤ a) (ha' : a ≤ 4 / 5) :
    fS z a < 2507333 / 1500000 := by
  have h1 := fS_le_Qh hz0 hz1 ha ha'
  rw [Qh_eq_Qfun] at h1
  have hk := kap_bounds hz0 hz1
  have hkK := kap_le_kfun hz0 hz1
  have hK1 := kfun_le_one hz0 hz1
  have hx1 : -(27 / 200 : ℝ) ≤ a - 127 / 200 := by linarith
  have hx2 : a - 127 / 200 ≤ 33 / 200 := by linarith
  have h2 := Qfun_anti (p0 := P0z z) (pl := Plz z) (pa := Paz z) hk.1 hkK hK1 hx1 hx2
  have h3 := Qfun_le_lhF (p0 := P0z z) (pl := Plz z) (pa := Paz z) hk.1 hk.2 hx1 hx2
  have h4 := lhF_lt (z := z) (t := (a - 127 / 200) / (27 / 200)) hz0 hz1
  unfold P0z Plz Paz at h2 h3 h4
  linarith

/-- **`lem:fqe-large-head-dual`.** -/
theorem largeHeadDual : LargeHeadDual := by
  intro a b c hc hcb hba ha1 ha2 hs
  have h1a : 0 < 1 - a := by linarith
  set z := (b - c) / (1 - a) with hz
  have hb : b = (1 - a) * (1 + 2 * z) / 3 := by
    rw [hz]; field_simp; linarith
  have hc' : c = (1 - a) * (1 - z) / 3 := by
    rw [hz]; field_simp; linarith
  have hz0 : 0 ≤ z := div_nonneg (by linarith) h1a.le
  have hz1 : z ≤ 1 := by
    rw [hz, div_le_one h1a]; linarith
  have hv : (![a, b, c, c] : Fin 4 → ℝ) = ![a, (1 - a) * (1 + 2 * z) / 3, (1 - a) * (1 - z) / 3, (1 - a) * (1 - z) / 3] := by
    rw [← hb, ← hc']
  rw [hv, lam_chart_eq (by linarith) hz0 hz1]
  exact fS_lt hz0 hz1 ha1 ha2

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.fS_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fS_lt

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.largeHeadDual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms largeHeadDual

end FormalResearch.FourQubitEntropy.RenyiFull
