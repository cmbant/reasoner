import FormalResearch.FourQubitEntropy.RenyiFullSlope
import FormalResearch.FourQubitEntropy.RenyiFullProps

/-!
# `lem:fqe-low-tilt-reduction`: the repeated-largest chart `(a,a,b,c)`

Paper E, `renyi_low_tilt_reduction.tex`.  For `3/2 ≤ q ≤ 8/5` and `0 ≤ ω ≤ 9/5`, among spectra
`(a,a,b,c)`, `a ≥ b ≥ c ≥ 0`, of a fixed purity, `H_q - ω t` is maximised only by two equal pairs.

The path of the paper is
`(1/4+u, 1/4+u, 1/4-u+d, 1/4-u-d)`, `d = √((x-4u²)/2)`, `u ∈ [u₁, √x/2]`, `x = p - 1/4`;
`dt/du = 36u² - 3x ≥ 0`, and `d(H_q - ωt)/du = (η - ω) dt/du` with `η > 64/35 > 9/5`
(`path_strictMonoOn` with `lowTilt_slope_numeric`).

* `sqrtPath_hasDerivAt`: derivative of `u ↦ √((x-4u²)/2)`.
* `lowTilt_chart`: the statement, in terms of the real numbers `a, b, c` (strict if `c < b`).
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

theorem sqrtPath_hasDerivAt {x u : ℝ} (h : 4 * u ^ 2 < x) :
    HasDerivAt (fun u : ℝ => Real.sqrt ((x - 4 * u ^ 2) / 2))
      (-2 * u / Real.sqrt ((x - 4 * u ^ 2) / 2)) u := by
  have hg : HasDerivAt (fun u : ℝ => (x - 4 * u ^ 2) / 2) (-4 * u) u := by
    have h1 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have := ((h1.const_mul 4).const_sub x).div_const 2
    convert this using 1
    ring
  have hpos : (x - 4 * u ^ 2) / 2 ≠ 0 := by
    have : 0 < x - 4 * u ^ 2 := by linarith
    positivity
  have := hg.sqrt hpos
  convert this using 1
  have hs : 0 < Real.sqrt ((x - 4 * u ^ 2) / 2) :=
    Real.sqrt_pos.2 (by have : 0 < x - 4 * u ^ 2 := by linarith
                        positivity)
  field_simp
  ring

noncomputable def ddF (x u : ℝ) : ℝ := Real.sqrt ((x - 4 * u ^ 2) / 2)
noncomputable def lE1 (u : ℝ) : ℝ := 1 / 4 + u
noncomputable def lE2 (x u : ℝ) : ℝ := 1 / 4 - u + ddF x u
noncomputable def lE3 (x u : ℝ) : ℝ := 1 / 4 - u - ddF x u
noncomputable def lT (x u : ℝ) : ℝ := 2 * lE1 u ^ 3 + 1 * lE2 x u ^ 3 + 1 * lE3 x u ^ 3

/-- The context of the lower-chart path: `u₁ = a - 1/4`, `d₁ = (b-c)/2 > 0`, `x = 4u₁²+2d₁²`,
`u_* = √x/2`. -/
structure LowCtx (u1 d1 x us : ℝ) : Prop where
  hu1 : 0 ≤ u1
  hd1 : 0 < d1
  hd1u : d1 ≤ 2 * u1
  hx : x = 4 * u1 ^ 2 + 2 * d1 ^ 2
  hus2 : 4 * us ^ 2 = x
  hus0 : 0 ≤ us

theorem LowCtx.x_pos {u1 d1 x us : ℝ} (C : LowCtx u1 d1 x us) : 0 < x := by
  rw [C.hx]; have := C.hd1; positivity

theorem LowCtx.lt {u1 d1 x us : ℝ} (C : LowCtx u1 d1 x us) : u1 < us := by
  by_contra hle
  push Not at hle
  have := C.hx; have := C.hus2; have := C.hd1; have := C.hu1
  nlinarith [C.hus0]

theorem LowCtx.x_le {u1 d1 x us : ℝ} (C : LowCtx u1 d1 x us) : x ≤ 12 * u1 ^ 2 := by
  have := C.hd1u; have := C.hd1; have := C.hx
  nlinarith

theorem LowCtx.x_le_u {u1 d1 x us : ℝ} (C : LowCtx u1 d1 x us) {u : ℝ} (hu : u1 ≤ u) :
    x ≤ 12 * u ^ 2 := by
  have := C.x_le; have := C.hu1
  nlinarith

theorem LowCtx.mem {u1 d1 x us : ℝ} (C : LowCtx u1 d1 x us) {u : ℝ} (hu : u ∈ Icc u1 us) :
    4 * u ^ 2 ≤ x := by
  have h1 := hu.2
  have h0 : 0 ≤ u := C.hu1.trans hu.1
  have := C.hus2
  nlinarith

theorem ddF_sq {x u : ℝ} (hu : 4 * u ^ 2 ≤ x) : ddF x u ^ 2 = (x - 4 * u ^ 2) / 2 :=
  Real.sq_sqrt (by linarith)

theorem ddF_nonneg (x u : ℝ) : 0 ≤ ddF x u := Real.sqrt_nonneg _

theorem LowCtx.dd_u1 {u1 d1 x us : ℝ} (C : LowCtx u1 d1 x us) : ddF x u1 = d1 := by
  unfold ddF
  rw [show (x - 4 * u1 ^ 2) / 2 = d1 ^ 2 by rw [C.hx]; ring, Real.sqrt_sq C.hd1.le]

theorem LowCtx.dd_us {u1 d1 x us : ℝ} (C : LowCtx u1 d1 x us) : ddF x us = 0 := by
  unfold ddF
  rw [C.hus2]; simp

theorem LowCtx.dd_le {u1 d1 x us : ℝ} (C : LowCtx u1 d1 x us) {u : ℝ} (hu : u ∈ Icc u1 us) :
    ddF x u ≤ d1 := by
  have h2 := ddF_sq (C.mem hu)
  have h3 : ddF x u ^ 2 ≤ d1 ^ 2 := by
    rw [h2]
    have := hu.1
    have := C.hx
    have := C.hu1
    nlinarith
  exact (abs_le_of_sq_le_sq' h3 C.hd1.le).2

theorem LowCtx.E3_nonneg {u1 d1 x us : ℝ} (C : LowCtx u1 d1 x us) {u : ℝ} (hu : u ∈ Icc u1 us)
    (hc : 0 ≤ 1 / 4 - u1 - d1) : 0 ≤ lE3 x u := by
  have h2 := ddF_sq (C.mem hu)
  have hdl := C.dd_le hu
  have hd0 := ddF_nonneg x u
  have hd1 := C.hd1
  unfold lE3
  by_contra hneg
  push Not at hneg
  have e1 : (d1 - ddF x u) * (d1 + ddF x u) = 2 * ((u - u1) * (u + u1)) := by
    have : d1 ^ 2 = (x - 4 * u1 ^ 2) / 2 := by rw [C.hx]; ring
    nlinarith
  have hs0 : 0 < d1 + ddF x u := by linarith
  have hs1 : d1 + ddF x u ≤ 2 * (u + u1) := by
    have := C.hd1u
    have := hu.1
    have := C.hu1
    linarith
  have e : 0 ≤ ((d1 - ddF x u) - (u - u1)) * (d1 + ddF x u) := by
    have h : (u - u1) * (d1 + ddF x u) ≤ (u - u1) * (2 * (u + u1)) :=
      mul_le_mul_of_nonneg_left hs1 (by linarith [hu.1])
    nlinarith
  have : 0 ≤ (d1 - ddF x u) - (u - u1) := nonneg_of_mul_nonneg_left e hs0
  linarith

theorem LowCtx.E3_le_E2 {u1 d1 x us : ℝ} (_C : LowCtx u1 d1 x us) (u : ℝ) :
    lE3 x u ≤ lE2 x u := by
  unfold lE3 lE2
  linarith [ddF_nonneg x u]

theorem LowCtx.E2_le_E1 {u1 d1 x us : ℝ} (C : LowCtx u1 d1 x us) {u : ℝ} (hu : u ∈ Icc u1 us) :
    lE2 x u ≤ lE1 u := by
  have h2 := ddF_sq (C.mem hu)
  have hd0 := ddF_nonneg x u
  have h0 : 0 ≤ u := C.hu1.trans hu.1
  have : ddF x u ≤ 2 * u := by
    have h3 : ddF x u ^ 2 ≤ (2 * u) ^ 2 := by
      rw [h2]
      have := C.x_le_u hu.1
      nlinarith
    exact (abs_le_of_sq_le_sq' h3 (by linarith)).2
  unfold lE2 lE1
  linarith

theorem LowCtx.interior {u1 d1 x us : ℝ} (C : LowCtx u1 d1 x us) {u : ℝ} (hu : u ∈ Ioo u1 us) :
    4 * u ^ 2 < x ∧ 0 < ddF x u ∧ ddF x u < 2 * u := by
  have h0 : 0 ≤ u := C.hu1.trans hu.1.le
  have hus2 := C.hus2
  have h1 : 4 * u ^ 2 < x := by nlinarith [hu.2]
  have h2 := ddF_sq h1.le
  have hp : 0 < ddF x u := Real.sqrt_pos.2 (by linarith)
  refine ⟨h1, hp, ?_⟩
  have h3 : ddF x u ^ 2 < (2 * u) ^ 2 := by
    rw [h2]
    have h4 := C.x_le
    have h5 := C.hu1
    have h6 := hu.1
    nlinarith
  exact (abs_lt_of_sq_lt_sq' h3 (by linarith [hu.1])).2

theorem lE1_deriv (u : ℝ) : HasDerivAt lE1 1 u := by
  unfold lE1
  simpa using (hasDerivAt_id u).const_add (1 / 4 : ℝ)

theorem lE2_deriv {x u : ℝ} (h : 4 * u ^ 2 < x) :
    HasDerivAt (lE2 x) (-1 + (-2 * u / ddF x u)) u := by
  have h1 := sqrtPath_hasDerivAt h
  have := ((hasDerivAt_id u).const_sub (1 / 4 : ℝ)).add h1
  unfold lE2 ddF
  exact this

theorem lE3_deriv {x u : ℝ} (h : 4 * u ^ 2 < x) :
    HasDerivAt (lE3 x) (-1 - (-2 * u / ddF x u)) u := by
  have h1 := sqrtPath_hasDerivAt h
  have := ((hasDerivAt_id u).const_sub (1 / 4 : ℝ)).sub h1
  unfold lE3 ddF
  exact this

theorem lT_deriv {x u : ℝ} (h : 4 * u ^ 2 < x) :
    HasDerivAt (lT x) (3 * (2 * 1 * lE1 u ^ 2 + 1 * (-1 + (-2 * u / ddF x u)) * lE2 x u ^ 2 +
      1 * (-1 - (-2 * u / ddF x u)) * lE3 x u ^ 2)) u := by
  have h1 := (lE1_deriv u).pow 3
  have h2 := (lE2_deriv h).pow 3
  have h3 := (lE3_deriv h).pow 3
  have := ((h1.const_mul 2).add (h2.const_mul 1)).add (h3.const_mul 1)
  unfold lT
  convert this using 1
  simp
  ring

theorem lowKappa {x u : ℝ} (h : 4 * u ^ 2 < x) :
    2 * 1 * lE1 u ^ 2 + 1 * (-1 + (-2 * u / ddF x u)) * lE2 x u ^ 2 +
      1 * (-1 - (-2 * u / ddF x u)) * lE3 x u ^ 2 = 12 * u ^ 2 - x := by
  have h2 := ddF_sq h.le
  have hp : 0 < ddF x u := Real.sqrt_pos.2 (by linarith)
  unfold lE1 lE2 lE3
  field_simp
  nlinarith [h2]

theorem lE1_cont : Continuous lE1 := by unfold lE1; fun_prop
theorem ddF_cont (x : ℝ) : Continuous (ddF x) := by unfold ddF; fun_prop
theorem lE2_cont (x : ℝ) : Continuous (lE2 x) := by unfold lE2; have := ddF_cont x; fun_prop
theorem lE3_cont (x : ℝ) : Continuous (lE3 x) := by unfold lE3; have := ddF_cont x; fun_prop
theorem lT_cont (x : ℝ) : Continuous (lT x) := by
  unfold lT; have := lE1_cont; have := lE2_cont x; have := lE3_cont x; fun_prop

/-- The functional on the lower chart, `H_q - ω t` of `(a,a,b,c)`. -/
noncomputable def lowF (q ω a b c : ℝ) : ℝ :=
  Real.logb 2 (2 * a ^ q + b ^ q + c ^ q) / (1 - q) - ω * (2 * a ^ 3 + b ^ 3 + c ^ 3)

/-- The functional on two equal pairs `(a,a,b,b)`. -/
noncomputable def pairF (q ω a b : ℝ) : ℝ :=
  Real.logb 2 (2 * a ^ q + 2 * b ^ q) / (1 - q) - ω * (2 * a ^ 3 + 2 * b ^ 3)

/-- **`lem:fqe-low-tilt-reduction`, strict form.**  For `3/2 ≤ q ≤ 8/5`, `0 ≤ ω ≤ 9/5` and a
spectrum `(a,a,b,c)` with `a ≥ b > c ≥ 0`, there is a two-pair spectrum `(a',a',b',b')` of the same
purity with strictly larger `H_q - ω t`. -/
theorem lowTilt_chart_strict {q ω a b c : ℝ} (hq1 : 3 / 2 ≤ q) (hq2 : q ≤ 8 / 5) (hω0 : 0 ≤ ω)
    (hω1 : ω ≤ 9 / 5) (hc : 0 ≤ c) (hcb : c < b) (hba : b ≤ a) (hs : 2 * a + b + c = 1) :
    ∃ a' b' : ℝ, 0 ≤ b' ∧ b' ≤ a' ∧ 2 * a' + 2 * b' = 1 ∧
      2 * a' ^ 2 + 2 * b' ^ 2 = 2 * a ^ 2 + b ^ 2 + c ^ 2 ∧
      lowF q ω a b c < pairF q ω a' b' := by
  have hq : 1 < q := by linarith
  obtain ⟨u1, hu1⟩ : ∃ u1 : ℝ, u1 = a - 1 / 4 := ⟨_, rfl⟩
  obtain ⟨d1, hd1⟩ : ∃ d1 : ℝ, d1 = (b - c) / 2 := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 4 * u1 ^ 2 + 2 * d1 ^ 2 := ⟨_, rfl⟩
  have hd1pos : 0 < d1 := by rw [hd1]; linarith
  have hxpos : 0 < x := by rw [hx]; positivity
  obtain ⟨us, hus⟩ : ∃ us : ℝ, us = Real.sqrt x / 2 := ⟨_, rfl⟩
  have hus2 : 4 * us ^ 2 = x := by
    rw [hus, div_pow, Real.sq_sqrt hxpos.le]; ring
  have hus0 : 0 ≤ us := by rw [hus]; positivity
  have hbd : b = 1 / 4 - u1 + d1 := by rw [hu1, hd1]; linarith
  have hcd : c = 1 / 4 - u1 - d1 := by rw [hu1, hd1]; linarith
  have C : LowCtx u1 d1 x us :=
    ⟨by rw [hu1]; linarith, hd1pos, by rw [hd1, hu1]; linarith, hx, hus2, hus0⟩
  have hcc : 0 ≤ 1 / 4 - u1 - d1 := by rw [← hcd]; exact hc
  have hlt := C.lt
  have E3nn := fun u (hu : u ∈ Icc u1 us) => C.E3_nonneg hu hcc
  have E1pos : ∀ u ∈ Icc u1 us, 0 < lE1 u := fun u hu => by
    unfold lE1; linarith [C.hu1, hu.1]
  have hZpos : ∀ u ∈ Icc u1 us, 0 < Zp q 2 1 1 lE1 (lE2 x) (lE3 x) u := fun u hu => by
    unfold Zp
    have a1 : 0 < lE1 u ^ q := Real.rpow_pos_of_pos (E1pos u hu) _
    have a2 : 0 ≤ lE2 x u ^ q := Real.rpow_nonneg ((E3nn u hu).trans (C.E3_le_E2 u)) _
    have a3 : 0 ≤ lE3 x u ^ q := Real.rpow_nonneg (E3nn u hu) _
    linarith
  have hmono := path_strictMonoOn (q := q) (ω := ω) (n1 := 2) (n2 := 1) (n3 := 1)
    (E1 := lE1) (E2 := lE2 x) (E3 := lE3 x) (T := lT x) (u0 := u1) (u1 := us) hq
    lE1_cont.continuousOn (lE2_cont x).continuousOn (lE3_cont x).continuousOn
    (lT_cont x).continuousOn hZpos
    (w1 := fun _ => 1) (w2 := fun u => -1 + (-2 * u / ddF x u))
    (w3 := fun u => -1 - (-2 * u / ddF x u))
    (fun u _ => lE1_deriv u) (fun u hu => lE2_deriv (C.interior hu).1)
    (fun u hu => lE3_deriv (C.interior hu).1) (fun u hu => lT_deriv (C.interior hu).1)
    (fun u hu => by ring)
    (fun u hu => by
      obtain ⟨-, hp, -⟩ := C.interior hu
      unfold lE1 lE2 lE3
      field_simp
      ring)
    (fun u hu => by
      obtain ⟨-, hp, hlt2⟩ := C.interior hu
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [lE1, lE2, lE3] at h <;> linarith)
    (fun u hu => by
      have := lowKappa (C.interior hu).1
      show 0 < 2 * 1 * lE1 u ^ 2 + 1 * (-1 + (-2 * u / ddF x u)) * lE2 x u ^ 2 +
        1 * (-1 - (-2 * u / ddF x u)) * lE3 x u ^ 2
      rw [this]
      have := C.x_le_u hu.1.le
      have h1 := C.x_le_u hu.1.le
      nlinarith [hu.1, C.hu1])
    (fun u hu => by
      obtain ⟨h4, hp, hlt2⟩ := C.interior hu
      have hume : u ∈ Icc u1 us := Ioo_subset_Icc_self hu
      have hE3 := C.E3_nonneg hume hcc
      have e32 : lE3 x u < lE2 x u := by unfold lE3 lE2; linarith
      have e21 : lE2 x u < lE1 u := by unfold lE2 lE1; linarith
      have hD := neg_dd2_ge (r := q - 1) (a := lE1 u) (b := lE2 x u) (c := lE3 x u)
        (by linarith) (by linarith) hE3 e32 e21
      have hmean : (lE1 u + lE2 x u + lE3 x u) / 3 = (1 - lE1 u) / 3 := by
        unfold lE1 lE2 lE3; ring
      rw [hmean] at hD
      have hZ := hZpos u hume
      have hsum : 2 * lE1 u + 1 * lE2 x u + 1 * lE3 x u = 1 := by
        unfold lE1 lE2 lE3; ring
      have hZa : Zp q 2 1 1 lE1 (lE2 x) (lE3 x) u ≤ lE1 u ^ (q - 1) := by
        unfold Zp
        exact Z_le_E1 hq (by norm_num) (by norm_num) (by norm_num) hE3 (C.E3_le_E2 u)
          (C.E2_le_E1 hume) hsum
      have ha1 : 1 / 4 ≤ lE1 u := by unfold lE1; linarith [C.hu1, hu.1]
      have ha2 : lE1 u ≤ 1 / 2 := by
        have := C.E3_le_E2 u
        linarith
      have hnum := lowTilt_slope_numeric hq1 hq2 hω0 hω1 ha1 ha2 hZ hZa
      unfold slope3
      refine slope_of_bound hq (Real.log_pos (by norm_num)) hZ hD ?_
      have hpos : 0 < (q - 1) / 2 := by linarith
      calc 3 * ω * ((q - 1) * Real.log 2 * Zp q 2 1 1 lE1 (lE2 x) (lE3 x) u)
          = (q - 1) / 2 * (6 * ω * Real.log 2 * Zp q 2 1 1 lE1 (lE2 x) (lE3 x) u) := by ring
        _ < (q - 1) / 2 * (q * (1 - (q - 1)) * ((1 - lE1 u) / 3) ^ (q - 1 - 2)) :=
            mul_lt_mul_of_pos_left hnum hpos
        _ = q * ((q - 1) * (1 - (q - 1)) / 2 * ((1 - lE1 u) / 3) ^ (q - 1 - 2)) := by ring)
  -- endpoint values
  have e1 : lE1 u1 = a := by unfold lE1; rw [hu1]; ring
  have e2 : lE2 x u1 = b := by unfold lE2; rw [C.dd_u1]; linarith
  have e3 : lE3 x u1 = c := by unfold lE3; rw [C.dd_u1]; linarith
  have f1 : lE1 us = 1 / 4 + us := rfl
  have f2 : lE2 x us = 1 / 4 - us := by unfold lE2; rw [C.dd_us]; ring
  have f3 : lE3 x us = 1 / 4 - us := by unfold lE3; rw [C.dd_us]; ring
  have hlt' := hmono ⟨le_refl _, hlt.le⟩ ⟨hlt.le, le_refl _⟩ hlt
  have g1 : pathF q ω 2 1 1 lE1 (lE2 x) (lE3 x) (lT x) u1 = lowF q ω a b c := by
    unfold pathF Zp lT lowF
    rw [e1, e2, e3]
    simp only [one_mul]
  have g2 : pathF q ω 2 1 1 lE1 (lE2 x) (lE3 x) (lT x) us = pairF q ω (1 / 4 + us) (1 / 4 - us) := by
    unfold pathF Zp lT pairF
    rw [f1, f2, f3]
    have h2 : 2 * (1 / 4 + us) ^ q + 1 * (1 / 4 - us) ^ q + 1 * (1 / 4 - us) ^ q =
        2 * (1 / 4 + us) ^ q + 2 * (1 / 4 - us) ^ q := by ring
    rw [h2]
    ring
  rw [g1, g2] at hlt'
  have hb' : 0 ≤ 1 / 4 - us := by
    have := C.E3_nonneg ⟨hlt.le, le_refl _⟩ hcc
    unfold lE3 at this
    rw [C.dd_us] at this
    linarith
  refine ⟨1 / 4 + us, 1 / 4 - us, hb', by linarith, by ring, ?_, hlt'⟩
  have ha' : a = 1 / 4 + u1 := by rw [hu1]; ring
  rw [ha', hbd, hcd]
  linear_combination hus2 + hx

/-! ### Back to four-point spectra -/

theorem renyi_aabc (q ω a b c : ℝ) :
    renyiSpec q ![a, a, b, c] - ω * cub ![a, a, b, c] = lowF q ω a b c := by
  unfold renyiSpec cub lowF
  simp only [Fin.sum_univ_four]
  simp
  ring_nf

theorem renyi_aabb (q ω a b : ℝ) :
    renyiSpec q ![a, a, b, b] - ω * cub ![a, a, b, b] = pairF q ω a b := by
  unfold renyiSpec cub pairF
  simp only [Fin.sum_univ_four]
  simp
  ring_nf

theorem pur_aabc (a b c : ℝ) : pur ![a, a, b, c] = 2 * a ^ 2 + b ^ 2 + c ^ 2 := by
  unfold pur; simp [Fin.sum_univ_four]; ring

theorem pur_abcc (a b c : ℝ) : pur ![a, b, c, c] = a ^ 2 + b ^ 2 + 2 * c ^ 2 := by
  unfold pur; simp [Fin.sum_univ_four]; ring

theorem cub_abcc (a b c : ℝ) : cub ![a, b, c, c] = a ^ 3 + b ^ 3 + 2 * c ^ 3 := by
  unfold cub; simp [Fin.sum_univ_four]; ring

theorem pur_aabb (a b : ℝ) : pur ![a, a, b, b] = 2 * a ^ 2 + 2 * b ^ 2 := by
  unfold pur; simp [Fin.sum_univ_four]; ring

theorem cub_aabb (a b : ℝ) : cub ![a, a, b, b] = 2 * a ^ 3 + 2 * b ^ 3 := by
  unfold cub; simp [Fin.sum_univ_four]; ring

theorem Lam_diff (q α β γ : ℝ) {μ ν : Fin 4 → ℝ} (hp : pur ν = pur μ) :
    Lam q α β γ ν - Lam q α β γ μ =
      (renyiSpec q ν - 12 * β * cub ν) - (renyiSpec q μ - 12 * β * cub μ) := by
  unfold Lam
  rw [hp]
  ring

/-- **`lem:fqe-low-tilt-reduction`** (supporting-function form): for `3/2 ≤ q ≤ 8/5` and
`0 ≤ β ≤ 3/20`, every chart spectrum has an `(a,b,c,c)` spectrum of the same purity with at least
as large `Λ_{(α,β,γ)}`, equal only if it is the spectrum itself. -/
theorem lowTilt_reduce {q β : ℝ} (α γ : ℝ) (hq1 : 3 / 2 ≤ q) (hq2 : q ≤ 8 / 5) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 3 / 20) {μ : Fin 4 → ℝ} (hμ : IsChart μ) :
    ∃ ν : Fin 4 → ℝ, IsProb4 ν ∧ (∃ a b c : ℝ, 0 ≤ c ∧ c ≤ b ∧ b ≤ a ∧ ν = ![a, b, c, c]) ∧
      pur ν = pur μ ∧ Lam q α β γ μ ≤ Lam q α β γ ν ∧
      (ν = μ ∨ Lam q α β γ μ < Lam q α β γ ν) := by
  obtain ⟨hpμ, a, b, c, hc, hcb, hba, hμe⟩ := hμ
  have hω0 : 0 ≤ 12 * β := by linarith
  have hω1 : 12 * β ≤ 9 / 5 := by linarith
  rcases hμe with rfl | rfl
  · exact ⟨_, hpμ, ⟨a, b, c, hc, hcb, hba, rfl⟩, rfl, le_refl _, Or.inl rfl⟩
  · have hs : 2 * a + b + c = 1 := by
      obtain ⟨-, h⟩ := hpμ
      simp [Fin.sum_univ_four] at h
      linarith
    rcases hcb.eq_or_lt with hbc | hbc
    · subst hbc
      exact ⟨![a, a, c, c], hpμ, ⟨a, a, c, hc, hba, le_rfl, rfl⟩, rfl, le_refl _, Or.inl rfl⟩
    · obtain ⟨a', b', hb', hab', hs', hpur, hlt⟩ :=
        lowTilt_chart_strict hq1 hq2 hω0 hω1 hc hbc hba hs
      have hνprob : IsProb4 ![a', a', b', b'] := by
        refine ⟨fun i => ?_, ?_⟩
        · fin_cases i <;> simp <;> linarith
        · simp [Fin.sum_univ_four]; linarith
      have hp : pur ![a', a', b', b'] = pur ![a, a, b, c] := by
        rw [pur_aabb, pur_aabc]; exact hpur
      have hd := Lam_diff q α β γ hp
      rw [renyi_aabb, renyi_aabc] at hd
      have hlt' : lowF q (12 * β) a b c < pairF q (12 * β) a' b' := hlt
      refine ⟨![a', a', b', b'], hνprob, ⟨a', a', b', hb', hab', le_rfl, rfl⟩, hp, ?_, ?_⟩
      · linarith
      · right; linarith

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.lowTilt_chart_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowTilt_chart_strict

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.lowTilt_reduce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowTilt_reduce

end FormalResearch.FourQubitEntropy.RenyiFull
