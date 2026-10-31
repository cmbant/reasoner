import Mathlib

/-!
# The second divided difference of `x ^ r`, `0 < r < 1`

Paper E, `lem:fqe-low-tilt-reduction` and `lem:fqe-hs-tilt` (the Hermite--Genocchi/Jensen step).

For `0 < c < b < a` and `0 < r < 1` put
`dd2 r a b c = a^r/((a-b)(a-c)) + b^r/((b-a)(b-c)) + c^r/((c-a)(c-b))`, the second divided
difference `[a,b,c] x^r`.  The paper bounds `-[a,b,c] x^r` below by the Hermite--Genocchi average of
the convex function `(r(1-r)/2) x^{r-2}` and Jensen's inequality.  Here the same bound
`neg_dd2_ge` is proved without integrals: `h = x^r - g`, with `g` the degree-three Taylor polynomial
of `x^r - (affine)` at the mean `m = (a+b+c)/3`, is concave because `x^{r-2}` is convex (tangent
inequality), while `[a,b,c] g = (x^r)''(m)/2` exactly (the cubic term has `[a,b,c](x-m)^3 = 0`).

* `dd2_quadratic`, `dd2_cubic`: `[a,b,c] (x-m)^2 = 1`, `[a,b,c] (x-m)^3 = 0`.
* `rpow_neg_tangent`: `y^{r-2} ≥ m^{r-2} + (r-2) m^{r-3} (y-m)`.
* `neg_dd2_ge`: `-[a,b,c] x^r ≥ (r(1-r)/2) ((a+b+c)/3)^{r-2}`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

/-- The second divided difference `[a,b,c] x^r`, as an explicit sum. -/
noncomputable def dd2 (r a b c : ℝ) : ℝ :=
  a ^ r / ((a - b) * (a - c)) + b ^ r / ((b - a) * (b - c)) + c ^ r / ((c - a) * (c - b))

/-- The weights of the divided difference. -/
theorem dd2_weights {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (g : ℝ → ℝ) :
    g a / ((a - b) * (a - c)) + g b / ((b - a) * (b - c)) + g c / ((c - a) * (c - b)) =
      g a * (1 / ((a - b) * (a - c))) + g b * (-(1 / ((a - b) * (b - c)))) +
        g c * (1 / ((a - c) * (b - c))) := by
  have h1 : a - b ≠ 0 := sub_ne_zero.2 hab
  have h2 : a - c ≠ 0 := sub_ne_zero.2 hac
  have h3 : b - c ≠ 0 := sub_ne_zero.2 hbc
  field_simp
  ring

theorem dd2_quadratic {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a - (a + b + c) / 3) ^ 2 / ((a - b) * (a - c)) + (b - (a + b + c) / 3) ^ 2 / ((b - a) * (b - c))
      + (c - (a + b + c) / 3) ^ 2 / ((c - a) * (c - b)) = 1 := by
  have h1 : a - b ≠ 0 := sub_ne_zero.2 hab
  have h2 : a - c ≠ 0 := sub_ne_zero.2 hac
  have h3 : b - c ≠ 0 := sub_ne_zero.2 hbc
  field_simp
  ring

theorem dd2_cubic {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a - (a + b + c) / 3) ^ 3 / ((a - b) * (a - c)) + (b - (a + b + c) / 3) ^ 3 / ((b - a) * (b - c))
      + (c - (a + b + c) / 3) ^ 3 / ((c - a) * (c - b)) = 0 := by
  have h1 : a - b ≠ 0 := sub_ne_zero.2 hab
  have h2 : a - c ≠ 0 := sub_ne_zero.2 hac
  have h3 : b - c ≠ 0 := sub_ne_zero.2 hbc
  field_simp
  ring

/-- Tangent inequality for the convex function `y ↦ y^{r-2}` (`r < 2`). -/
theorem rpow_neg_tangent {r m y : ℝ} (hr : r ≤ 2) (hm : 0 < m) (hy : 0 < y) :
    m ^ (r - 2) + (r - 2) * m ^ (r - 3) * (y - m) ≤ y ^ (r - 2) := by
  have hc : r - 2 ≤ 0 := by linarith
  have e3 : m ^ (r - 3) = m ^ (r - 2) / m := by
    rw [show r - 3 = (r - 2) - 1 by ring, Real.rpow_sub hm, Real.rpow_one]
  have e1 : y ^ (r - 2) = m ^ (r - 2) * Real.exp ((r - 2) * Real.log (y / m)) := by
    have hym : 0 < y / m := div_pos hy hm
    rw [mul_comm (r - 2), ← Real.rpow_def_of_pos hym, ← Real.mul_rpow hm.le hym.le]
    congr 1
    field_simp
  have hmp : 0 < m ^ (r - 2) := Real.rpow_pos_of_pos hm _
  have hl : Real.log (y / m) ≤ y / m - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hexp := Real.add_one_le_exp ((r - 2) * Real.log (y / m))
  have hlin : (r - 2) * (y / m - 1) ≤ (r - 2) * Real.log (y / m) :=
    mul_le_mul_of_nonpos_left hl hc
  have hfin : 1 + (r - 2) * (y / m - 1) ≤ Real.exp ((r - 2) * Real.log (y / m)) := by linarith
  rw [e1, e3]
  have : m ^ (r - 2) + (r - 2) * (m ^ (r - 2) / m) * (y - m) =
      m ^ (r - 2) * (1 + (r - 2) * (y / m - 1)) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hfin hmp.le

/-- The auxiliary concave function `h = x^r - g`. -/
noncomputable def hAux (r m : ℝ) (y : ℝ) : ℝ :=
  y ^ r - (-(r * (1 - r)) * m ^ (r - 2) * (y - m) ^ 2 / 2 +
    r * (1 - r) * (2 - r) * m ^ (r - 3) * (y - m) ^ 3 / 6)

theorem hAux_concave {r m : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hm : 0 < m) :
    ConcaveOn ℝ (Ici 0) (hAux r m) := by
  have hint : interior (Ici (0 : ℝ)) = Ioi 0 := interior_Ici
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici 0)
    (f' := fun y => r * y ^ (r - 1) - (-(r * (1 - r)) * m ^ (r - 2) * (y - m) +
      r * (1 - r) * (2 - r) * m ^ (r - 3) * (y - m) ^ 2 / 2))
    (f'' := fun y => -(r * (1 - r)) * y ^ (r - 2) - (-(r * (1 - r)) * m ^ (r - 2) +
      r * (1 - r) * (2 - r) * m ^ (r - 3) * (y - m)))
    ?_ ?_ ?_ ?_
  · intro y hy
    have hy : (0 : ℝ) ≤ y := hy
    unfold hAux
    have hc : ContinuousAt (fun y : ℝ => y ^ r) y := Real.continuousAt_rpow_const _ _ (Or.inr hr0.le)
    exact (hc.sub (by fun_prop)).continuousWithinAt
  · intro y hy
    rw [hint] at hy ⊢
    have hy : (0 : ℝ) < y := hy
    have h1 : HasDerivAt (fun y : ℝ => y ^ r) (r * y ^ (r - 1)) y := Real.hasDerivAt_rpow_const (Or.inl hy.ne')
    have h2 : HasDerivAt (fun y : ℝ => (y - m) ^ 2) (2 * (y - m)) y := by
      convert ((hasDerivAt_id y).sub_const m).fun_pow 2 using 1 <;> simp [id]
    have h3 : HasDerivAt (fun y : ℝ => (y - m) ^ 3) (3 * (y - m) ^ 2) y := by
      convert ((hasDerivAt_id y).sub_const m).fun_pow 3 using 1 <;> simp [id]
    have := h1.sub (((h2.const_mul (-(r * (1 - r)) * m ^ (r - 2))).div_const 2).add
      ((h3.const_mul (r * (1 - r) * (2 - r) * m ^ (r - 3))).div_const 6))
    unfold hAux
    refine (this.congr_deriv ?_).hasDerivWithinAt
    ring
  · intro y hy
    rw [hint] at hy ⊢
    have hy : (0 : ℝ) < y := hy
    have h1 : HasDerivAt (fun y : ℝ => y ^ (r - 1)) ((r - 1) * y ^ (r - 1 - 1)) y :=
      Real.hasDerivAt_rpow_const (Or.inl hy.ne')
    have h2 : HasDerivAt (fun y : ℝ => y - m) 1 y := (hasDerivAt_id y).sub_const m
    have h3 : HasDerivAt (fun y : ℝ => (y - m) ^ 2) (2 * (y - m)) y := by
      convert ((hasDerivAt_id y).sub_const m).fun_pow 2 using 1 <;> simp [id]
    have := (h1.const_mul r).sub (((h2.const_mul (-(r * (1 - r)) * m ^ (r - 2)))).add
      ((h3.const_mul (r * (1 - r) * (2 - r) * m ^ (r - 3))).div_const 2))
    refine (this.congr_deriv ?_).hasDerivWithinAt
    have e : y ^ (r - 1 - 1) = y ^ (r - 2) := by ring_nf
    rw [e]
    ring
  · intro y hy
    rw [hint] at hy
    have hy : (0 : ℝ) < y := hy
    have := rpow_neg_tangent (r := r) (m := m) (y := y) (by linarith) hm hy
    have hp : 0 ≤ r * (1 - r) := by nlinarith
    nlinarith [mul_nonneg hp (sub_nonneg.2 this)]

/-- **Slope bound** (Hermite--Genocchi/Jensen step of `lem:fqe-low-tilt-reduction`):
for `0 ≤ c < b < a` and `0 < r < 1`,
`-[a,b,c] x^r ≥ (r(1-r)/2) ((a+b+c)/3)^{r-2}`. -/
theorem neg_dd2_ge {r a b c : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hc : 0 ≤ c) (hcb : c < b)
    (hba : b < a) :
    r * (1 - r) / 2 * ((a + b + c) / 3) ^ (r - 2) ≤ -dd2 r a b c := by
  set m := (a + b + c) / 3 with hm_def
  have hm : 0 < m := by rw [hm_def]; linarith
  have hab : a ≠ b := hba.ne'
  have hac : a ≠ c := (hcb.trans hba).ne'
  have hbc : b ≠ c := hcb.ne'
  have hab' : 0 < a - b := sub_pos.2 hba
  have hac' : 0 < a - c := sub_pos.2 (hcb.trans hba)
  have hbc' : 0 < b - c := sub_pos.2 hcb
  have hconc := hAux_concave (r := r) hr0 hr1 hm
  -- three-point concavity: h b ≥ λ h c + (1-λ) h a
  set lam := (a - b) / (a - c) with hlam
  have hl0 : 0 ≤ lam := div_nonneg hab'.le hac'.le
  have hl1 : lam ≤ 1 := by rw [hlam, div_le_one hac']; linarith
  have hbeq : lam • c + (1 - lam) • a = b := by
    simp only [smul_eq_mul, hlam]; field_simp; ring
  have hcm : c ∈ Ici (0 : ℝ) := hc
  have ham : a ∈ Ici (0 : ℝ) := hc.trans (hcb.trans hba).le
  have key := hconc.2 hcm ham hl0 (by linarith : 0 ≤ 1 - lam) (by ring)
  rw [hbeq] at key
  simp only [smul_eq_mul] at key
  -- identity: dd2 of the polynomial part
  have e2 := dd2_quadratic hab hac hbc
  have e3 := dd2_cubic hab hac hbc
  rw [← hm_def] at e2 e3
  set α := -(r * (1 - r)) * m ^ (r - 2) with hα
  set β := r * (1 - r) * (2 - r) * m ^ (r - 3) with hβ
  have hpoly : (α * (a - m) ^ 2 / 2 + β * (a - m) ^ 3 / 6) / ((a - b) * (a - c)) +
      (α * (b - m) ^ 2 / 2 + β * (b - m) ^ 3 / 6) / ((b - a) * (b - c)) +
      (α * (c - m) ^ 2 / 2 + β * (c - m) ^ 3 / 6) / ((c - a) * (c - b)) = α / 2 := by
    have : (α * (a - m) ^ 2 / 2 + β * (a - m) ^ 3 / 6) / ((a - b) * (a - c)) +
      (α * (b - m) ^ 2 / 2 + β * (b - m) ^ 3 / 6) / ((b - a) * (b - c)) +
      (α * (c - m) ^ 2 / 2 + β * (c - m) ^ 3 / 6) / ((c - a) * (c - b)) =
      α / 2 * ((a - m) ^ 2 / ((a - b) * (a - c)) + (b - m) ^ 2 / ((b - a) * (b - c)) +
        (c - m) ^ 2 / ((c - a) * (c - b))) +
      β / 6 * ((a - m) ^ 3 / ((a - b) * (a - c)) + (b - m) ^ 3 / ((b - a) * (b - c)) +
        (c - m) ^ 3 / ((c - a) * (c - b))) := by
      ring
    rw [this, e2, e3]; ring
  -- decomposition dd2 = (dd2 of h) + α/2
  have hdec : dd2 r a b c = (hAux r m a / ((a - b) * (a - c)) + hAux r m b / ((b - a) * (b - c)) +
      hAux r m c / ((c - a) * (c - b))) + α / 2 := by
    rw [← hpoly]
    unfold hAux dd2
    simp only [← hα, ← hβ]
    ring
  -- sign of the h-part
  have hsign : hAux r m a / ((a - b) * (a - c)) + hAux r m b / ((b - a) * (b - c)) +
      hAux r m c / ((c - a) * (c - b)) ≤ 0 := by
    have hw : hAux r m a / ((a - b) * (a - c)) + hAux r m b / ((b - a) * (b - c)) +
        hAux r m c / ((c - a) * (c - b)) =
        -(1 / ((a - b) * (b - c))) * (hAux r m b - (lam * hAux r m c + (1 - lam) * hAux r m a)) := by
      simp only [hlam]
      field_simp
      ring
    rw [hw]
    have : 0 ≤ 1 / ((a - b) * (b - c)) := by positivity
    nlinarith [mul_nonneg this (sub_nonneg.2 key)]
  have hα2 : α / 2 = -(r * (1 - r) / 2 * m ^ (r - 2)) := by rw [hα]; ring
  linarith

end FormalResearch.FourQubitEntropy.RenyiFull
