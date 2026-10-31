import Mathlib

/-!
# Single crossing of the Rényi entropies: the one-large-family lemma

Paper: `lem:fqe-renyi-single-crossing` (renyi_single_crossing.tex), the paragraph "The one-large
family" of its proof.

For `q > 1` write `s = q - 1`, `L = ln 3`, `κ = 1/q + L/sinh(sL)`, `β = qκ - 1 = qL/sinh(sL) > 0`
and `φ = v_q - κ u_q`, where for a four-point vector `l` (with `0^q ln 0 = 0`)
`u_q(l) = ln Σ lᵢ^q`, `v_q(l) = Σ lᵢ^q ln lᵢ / Σ lᵢ^q`.
On the one-large family `(a, b, b, b)`, `a = (1 + 3e^{-z})⁻¹`, `b = a e^{-z}`, one has the closed form
`Φ(z) = β ln(1 + 3e^{-z}) - κ ln(1 + 3e^{-qz}) - z w`, `w = 3e^{-qz}/(1 + 3e^{-qz})`.
This file proves: `φ(a,b,b,b) = Φ(ln(a/b))` (`sxPhiVec_family`), the derivative formula
`Φ' = zw(1-w)(q - βR(z))` with the hyperbolic identity (SR) for `R`, and that `Φ` strictly increases on
`[0, L]` and strictly decreases on `[L, ∞)` (`sxPhi_le`, `sxPhi_eq_iff`), so
`φ(a,b,b,b) ≤ φ(σ)`, `σ = (1/2, 1/6, 1/6, 1/6)`, with equality only for `a/b = 3` (`sxFamily_le`).
Not in this file: the reduction of an arbitrary maximiser of `φ` on the simplex to the family
(`RenyiSingleCrossing.lean`).
-/

namespace FormalResearch.FourQubitEntropy

open Real

/-- `κ_q = 1/q + ln 3 / sinh((q-1) ln 3)`. -/
noncomputable def sxKappa (q : ℝ) : ℝ := 1 / q + Real.log 3 / Real.sinh ((q - 1) * Real.log 3)

/-- `β_q = q L / sinh((q-1) L) = q κ_q - 1`. -/
noncomputable def sxBeta (q : ℝ) : ℝ := q * Real.log 3 / Real.sinh ((q - 1) * Real.log 3)

/-- `Σ lᵢ^q` over four points. -/
noncomputable def sxZ (q : ℝ) (l : Fin 4 → ℝ) : ℝ := ∑ i, l i ^ q

/-- `u_q(l) = ln Σ lᵢ^q`. -/
noncomputable def sxU (q : ℝ) (l : Fin 4 → ℝ) : ℝ := Real.log (sxZ q l)

/-- `v_q(l) = Σ lᵢ^q ln lᵢ / Σ lᵢ^q`. -/
noncomputable def sxV (q : ℝ) (l : Fin 4 → ℝ) : ℝ :=
  (∑ i, l i ^ q * Real.log (l i)) / sxZ q l

/-- `φ = v_q - κ_q u_q`. -/
noncomputable def sxPhiVec (q : ℝ) (l : Fin 4 → ℝ) : ℝ := sxV q l - sxKappa q * sxU q l

/-- The HS spectrum `σ = (1/2, 1/6, 1/6, 1/6)`. -/
noncomputable def hsSpec : Fin 4 → ℝ := ![1 / 2, 1 / 6, 1 / 6, 1 / 6]

/-- A four-point probability vector. -/
def IsProb4 (l : Fin 4 → ℝ) : Prop := (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1

/-- `l` is a permutation of the HS spectrum `σ`. -/
def IsHsPerm (l : Fin 4 → ℝ) : Prop := ∃ e : Equiv.Perm (Fin 4), ∀ i, l i = hsSpec (e i)

/-! ### Elementary facts on `κ`, `β` -/

theorem sx_log3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

theorem sx_sinh_pos {q : ℝ} (hq : 1 < q) : 0 < Real.sinh ((q - 1) * Real.log 3) :=
  Real.sinh_pos_iff.mpr (mul_pos (by linarith) sx_log3_pos)

theorem sxBeta_pos {q : ℝ} (hq : 1 < q) : 0 < sxBeta q :=
  div_pos (mul_pos (by linarith) sx_log3_pos) (sx_sinh_pos hq)

theorem q_mul_sxKappa {q : ℝ} (hq : 1 < q) : q * sxKappa q = 1 + sxBeta q := by
  have hq0 : q ≠ 0 := by linarith
  unfold sxKappa sxBeta
  field_simp

/-! ### The closed form `Φ` and its derivative -/

/-- `Φ(z) = β ln(1 + 3e^{-z}) - κ ln(1 + 3e^{-qz}) - z w`, `w = 3e^{-qz}/(1 + 3e^{-qz})`. -/
noncomputable def sxPhi (q z : ℝ) : ℝ :=
  sxBeta q * Real.log (1 + 3 * Real.exp (-z))
    - sxKappa q * Real.log (1 + 3 * Real.exp (-(q * z)))
    - z * (3 * Real.exp (-(q * z)) / (1 + 3 * Real.exp (-(q * z))))

/-- `R(z) = (e^{sz} - 1)(1 + 3e^{-qz}) / (z (1 + 3e^{-z}))`, `s = q - 1`. -/
noncomputable def sxR (q z : ℝ) : ℝ :=
  (Real.exp ((q - 1) * z) - 1) * (1 + 3 * Real.exp (-(q * z))) / (z * (1 + 3 * Real.exp (-z)))

theorem sx_hasDerivAt_Phi {q : ℝ} (hq : 1 < q) (z : ℝ) :
    HasDerivAt (sxPhi q)
      (sxBeta q * (3 * Real.exp (-(q * z)) / (1 + 3 * Real.exp (-(q * z)))
          - 3 * Real.exp (-z) / (1 + 3 * Real.exp (-z)))
        + q * z * (3 * Real.exp (-(q * z)) / (1 + 3 * Real.exp (-(q * z))))
          * (1 - 3 * Real.exp (-(q * z)) / (1 + 3 * Real.exp (-(q * z))))) z := by
  have h1 : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-z)) z := by
    have := (hasDerivAt_neg z).exp
    simpa using this
  have h2 : HasDerivAt (fun z : ℝ => Real.exp (-(q * z))) (-(q * Real.exp (-(q * z)))) z := by
    have hl : HasDerivAt (fun z : ℝ => -(q * z)) (-q) z := by
      have h := ((hasDerivAt_id' z).const_mul q).neg
      convert h using 1
      ring
    have := hl.exp
    convert this using 1
    ring
  have hp1 : 0 < 1 + 3 * Real.exp (-z) := by positivity
  have hp2 : 0 < 1 + 3 * Real.exp (-(q * z)) := by positivity
  have h3 := ((h1.const_mul 3).const_add 1).log hp1.ne'
  have h4 := ((h2.const_mul 3).const_add 1).log hp2.ne'
  have h5 := (h2.const_mul 3).div ((h2.const_mul 3).const_add 1) hp2.ne'
  have h6 := (hasDerivAt_id z).mul h5
  have h := ((h3.const_mul (sxBeta q)).sub (h4.const_mul (sxKappa q))).sub h6
  have hk : sxKappa q * q = 1 + sxBeta q := by rw [mul_comm]; exact q_mul_sxKappa hq
  unfold sxPhi
  refine h.congr_deriv ?_
  have hk' : sxKappa q = (1 + sxBeta q) / q := by
    rw [eq_div_iff (by linarith)]; exact hk
  simp only [id, Pi.div_apply]
  rw [hk']
  have hq0 : q ≠ 0 := by linarith
  field_simp
  ring

/-- The derivative of `Φ`, `β(w - p) + q z w (1 - w)`. -/
noncomputable def sxD (q z : ℝ) : ℝ :=
  sxBeta q * (3 * Real.exp (-(q * z)) / (1 + 3 * Real.exp (-(q * z)))
          - 3 * Real.exp (-z) / (1 + 3 * Real.exp (-z)))
        + q * z * (3 * Real.exp (-(q * z)) / (1 + 3 * Real.exp (-(q * z))))
          * (1 - 3 * Real.exp (-(q * z)) / (1 + 3 * Real.exp (-(q * z))))

theorem sxD_eq (q : ℝ) {z : ℝ} (hz : z ≠ 0) :
    sxD q z = z * (3 * Real.exp (-(q * z)) / (1 + 3 * Real.exp (-(q * z)))
        * (1 - 3 * Real.exp (-(q * z)) / (1 + 3 * Real.exp (-(q * z))))) * (q - sxBeta q * sxR q z) := by
  have hE1 : Real.exp (-z) = Real.exp (-(q * z)) * Real.exp ((q - 1) * z) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold sxD sxR
  rw [hE1]
  have h1 : 0 < Real.exp (-(q * z)) := Real.exp_pos _
  have h2 : 0 < Real.exp ((q - 1) * z) := Real.exp_pos _
  have h3 : 0 < 1 + 3 * Real.exp (-(q * z)) := by positivity
  have h4 : 0 < 1 + 3 * (Real.exp (-(q * z)) * Real.exp ((q - 1) * z)) := by positivity
  field_simp
  ring

/-- The hyperbolic identity (SR):
`R(z) = sinh(sz)/z + ((e^z - 3)/(e^z + 3)) (cosh(sz) - 1)/z`, equivalently with
`tanh((z - L)/2) = (e^z - 3)/(e^z + 3)`. -/
theorem sxR_eq (q : ℝ) {z : ℝ} (hz : z ≠ 0) :
    sxR q z = Real.sinh ((q - 1) * z) / z
      + (Real.exp z - 3) * (Real.cosh ((q - 1) * z) - 1) / ((Real.exp z + 3) * z) := by
  have hE1 : Real.exp (-z) = (Real.exp z)⁻¹ := Real.exp_neg z
  have hE2 : Real.exp (-(q * z)) = (Real.exp z)⁻¹ * (Real.exp ((q - 1) * z))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  have hs : Real.sinh ((q - 1) * z) = (Real.exp ((q - 1) * z) - (Real.exp ((q - 1) * z))⁻¹) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg]
  have hc : Real.cosh ((q - 1) * z) = (Real.exp ((q - 1) * z) + (Real.exp ((q - 1) * z))⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg]
  unfold sxR
  rw [hE1, hE2, hs, hc]
  have h1 : 0 < Real.exp z := Real.exp_pos _
  have h2 : 0 < Real.exp ((q - 1) * z) := Real.exp_pos _
  generalize Real.exp z = A at *
  generalize Real.exp ((q - 1) * z) = X at *
  have h3 : 0 < A + 3 := by positivity
  have h4 : 0 < 1 + 3 * A⁻¹ := by positivity
  have h5 : 0 < A * X + 3 := by positivity
  field_simp
  ring

/-! ### Monotonicity of `sinh y / y` -/

theorem cosh_mul_sub_sinh_pos {y : ℝ} (hy : 0 < y) : 0 < y * Real.cosh y - Real.sinh y := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => x * Real.cosh x - Real.sinh x) (x * Real.sinh x) x := by
    intro x
    have := ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub (Real.hasDerivAt_sinh x)
    refine this.congr_deriv ?_
    simp only [id]; ring
  have hm : StrictMonoOn (fun x => x * Real.cosh x - Real.sinh x) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      exact mul_pos hx (Real.sinh_pos_iff.mpr hx)
  have := hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy.le) hy
  simpa using this

theorem sinh_div_strictMonoOn : StrictMonoOn (fun y : ℝ => Real.sinh y / y) (Set.Ioi 0) := by
  have hd : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => Real.sinh x / x)
      ((Real.cosh x * x - Real.sinh x * 1) / x ^ 2) x := by
    intro x hx
    exact (Real.hasDerivAt_sinh x).div (hasDerivAt_id x) hx
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx
    exact (hd x (ne_of_gt hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hd x (ne_of_gt hx)).deriv]
    have := cosh_mul_sub_sinh_pos hx
    apply div_pos _ (pow_pos hx 2)
    nlinarith

/-! ### The sign of `q - β R` -/

theorem sx_beta_mul {q : ℝ} (hq : 1 < q) :
    sxBeta q * (Real.sinh ((q - 1) * Real.log 3) / Real.log 3) = q := by
  have hS := (sx_sinh_pos hq).ne'
  have hL := sx_log3_pos.ne'
  unfold sxBeta
  generalize Real.sinh ((q - 1) * Real.log 3) = S at *
  field_simp

theorem sxR_lt {q z : ℝ} (hq : 1 < q) (hz0 : 0 < z) (hzL : z < Real.log 3) :
    sxR q z < Real.sinh ((q - 1) * Real.log 3) / Real.log 3 := by
  rw [sxR_eq q hz0.ne']
  have hs : 0 < q - 1 := by linarith
  have hmono := sinh_div_strictMonoOn (Set.mem_Ioi.mpr (mul_pos hs hz0))
    (Set.mem_Ioi.mpr (mul_pos hs sx_log3_pos)) (by nlinarith)
  simp only at hmono
  have e1 : Real.sinh ((q - 1) * z) / z = (q - 1) * (Real.sinh ((q - 1) * z) / ((q - 1) * z)) := by
    field_simp
  have e2 : Real.sinh ((q - 1) * Real.log 3) / Real.log 3
      = (q - 1) * (Real.sinh ((q - 1) * Real.log 3) / ((q - 1) * Real.log 3)) := by
    have := sx_log3_pos.ne'; field_simp
  have h3 : Real.exp z < 3 := by
    have := Real.exp_lt_exp.mpr hzL
    rwa [Real.exp_log (by norm_num)] at this
  have h4 : 1 < Real.cosh ((q - 1) * z) := Real.one_lt_cosh.mpr (mul_pos hs hz0).ne'
  have h5 : (Real.exp z - 3) * (Real.cosh ((q - 1) * z) - 1) / ((Real.exp z + 3) * z) < 0 := by
    apply div_neg_of_neg_of_pos
    · exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    · positivity
  rw [e2]
  nlinarith [mul_lt_mul_of_pos_left hmono hs]

theorem sxR_gt {q z : ℝ} (hq : 1 < q) (hzL : Real.log 3 < z) :
    Real.sinh ((q - 1) * Real.log 3) / Real.log 3 < sxR q z := by
  have hz0 : 0 < z := lt_trans sx_log3_pos hzL
  rw [sxR_eq q hz0.ne']
  have hs : 0 < q - 1 := by linarith
  have hmono := sinh_div_strictMonoOn (Set.mem_Ioi.mpr (mul_pos hs sx_log3_pos))
    (Set.mem_Ioi.mpr (mul_pos hs hz0)) (by nlinarith)
  simp only at hmono
  have e1 : Real.sinh ((q - 1) * z) / z = (q - 1) * (Real.sinh ((q - 1) * z) / ((q - 1) * z)) := by
    field_simp
  have e2 : Real.sinh ((q - 1) * Real.log 3) / Real.log 3
      = (q - 1) * (Real.sinh ((q - 1) * Real.log 3) / ((q - 1) * Real.log 3)) := by
    have := sx_log3_pos.ne'; field_simp
  have h3 : 3 < Real.exp z := by
    have := Real.exp_lt_exp.mpr hzL
    rwa [Real.exp_log (by norm_num)] at this
  have h4 : 1 < Real.cosh ((q - 1) * z) := Real.one_lt_cosh.mpr (mul_pos hs hz0).ne'
  have h5 : 0 < (Real.exp z - 3) * (Real.cosh ((q - 1) * z) - 1) / ((Real.exp z + 3) * z) := by
    apply div_pos
    · exact mul_pos (by linarith) (by linarith)
    · positivity
  rw [e2]
  nlinarith [mul_lt_mul_of_pos_left hmono hs]

/-! ### `Φ` increases up to `L = ln 3` and decreases afterwards -/

theorem sx_w_factor_pos (q z : ℝ) :
    0 < 3 * Real.exp (-(q * z)) / (1 + 3 * Real.exp (-(q * z)))
        * (1 - 3 * Real.exp (-(q * z)) / (1 + 3 * Real.exp (-(q * z)))) := by
  have h1 : 0 < Real.exp (-(q * z)) := Real.exp_pos _
  have h3 : 0 < 1 + 3 * Real.exp (-(q * z)) := by positivity
  have : 1 - 3 * Real.exp (-(q * z)) / (1 + 3 * Real.exp (-(q * z)))
      = 1 / (1 + 3 * Real.exp (-(q * z))) := by field_simp; ring
  rw [this]; positivity

theorem sxPhi_hasDerivAt_D {q : ℝ} (hq : 1 < q) (z : ℝ) : HasDerivAt (sxPhi q) (sxD q z) z :=
  sx_hasDerivAt_Phi hq z

theorem sxPhi_continuous {q : ℝ} (hq : 1 < q) : Continuous (sxPhi q) :=
  continuous_iff_continuousAt.mpr fun z => (sxPhi_hasDerivAt_D hq z).continuousAt

theorem sxPhi_strictMonoOn {q : ℝ} (hq : 1 < q) :
    StrictMonoOn (sxPhi q) (Set.Icc 0 (Real.log 3)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (sxPhi_continuous hq).continuousOn
  intro z hz
  rw [interior_Icc] at hz
  rw [(sxPhi_hasDerivAt_D hq z).deriv, sxD_eq q hz.1.ne']
  have h1 := sx_w_factor_pos q z
  have h2 : 0 < q - sxBeta q * sxR q z := by
    have := sxR_lt hq hz.1 hz.2
    have h3 := sx_beta_mul hq
    nlinarith [sxBeta_pos hq]
  exact mul_pos (mul_pos hz.1 h1) h2

theorem sxPhi_strictAntiOn {q : ℝ} (hq : 1 < q) :
    StrictAntiOn (sxPhi q) (Set.Ici (Real.log 3)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (sxPhi_continuous hq).continuousOn
  intro z hz
  rw [interior_Ici] at hz
  have hz0 : 0 < z := lt_trans sx_log3_pos hz
  rw [(sxPhi_hasDerivAt_D hq z).deriv, sxD_eq q hz0.ne']
  have h1 := sx_w_factor_pos q z
  have h2 : q - sxBeta q * sxR q z < 0 := by
    have := sxR_gt hq hz
    have h3 := sx_beta_mul hq
    nlinarith [sxBeta_pos hq]
  exact mul_neg_of_pos_of_neg (mul_pos hz0 h1) h2

/-- `Φ(z) < Φ(ln 3)` for `z ≥ 0`, `z ≠ ln 3`. -/
theorem sxPhi_lt {q : ℝ} (hq : 1 < q) {z : ℝ} (hz : 0 ≤ z) (hne : z ≠ Real.log 3) :
    sxPhi q z < sxPhi q (Real.log 3) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact sxPhi_strictMonoOn hq ⟨hz, h.le⟩ ⟨sx_log3_pos.le, le_rfl⟩ h
  · exact sxPhi_strictAntiOn hq (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h.le) h

theorem sxPhi_le {q : ℝ} (hq : 1 < q) {z : ℝ} (hz : 0 ≤ z) :
    sxPhi q z ≤ sxPhi q (Real.log 3) := by
  by_cases h : z = Real.log 3
  · rw [h]
  · exact (sxPhi_lt hq hz h).le

/-! ### From the one-large vector to `Φ` -/

theorem sx_sum_family (q a b : ℝ) :
    ∑ i, (![a, b, b, b] : Fin 4 → ℝ) i ^ q = a ^ q + 3 * b ^ q := by
  simp [Fin.sum_univ_four]; ring

theorem sx_sumlog_family (q a b : ℝ) :
    ∑ i, (![a, b, b, b] : Fin 4 → ℝ) i ^ q * Real.log ((![a, b, b, b] : Fin 4 → ℝ) i)
      = a ^ q * Real.log a + 3 * (b ^ q * Real.log b) := by
  simp [Fin.sum_univ_four]; ring

/-- `φ(a,b,b,b) = Φ(ln(a/b))` for `a, b > 0`, `a + 3b = 1`. -/
theorem sxPhiVec_family {q : ℝ} (hq : 1 < q) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + 3 * b = 1) :
    sxPhiVec q ![a, b, b, b] = sxPhi q (Real.log (a / b)) := by
  set z := Real.log (a / b) with hz
  have hbz : b = a * Real.exp (-z) := by
    rw [hz, Real.exp_neg, Real.exp_log (div_pos ha hb), inv_div]; field_simp
  have hbq : b ^ q = a ^ q * Real.exp (-(q * z)) := by
    rw [hbz, Real.mul_rpow ha.le (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2; ring
  have hlb : Real.log b = Real.log a - z := by
    rw [hbz, Real.log_mul ha.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
  have hA : 0 < a ^ q := Real.rpow_pos_of_pos ha q
  have hE : 0 < Real.exp (-(q * z)) := Real.exp_pos _
  have hE1 : 0 < Real.exp (-z) := Real.exp_pos _
  have hla : Real.log a = - Real.log (1 + 3 * Real.exp (-z)) := by
    have : a * (1 + 3 * Real.exp (-z)) = 1 := by
      calc a * (1 + 3 * Real.exp (-z)) = a + 3 * (a * Real.exp (-z)) := by ring
        _ = a + 3 * b := by rw [← hbz]
        _ = 1 := hab
    have h2 : a = (1 + 3 * Real.exp (-z))⁻¹ := eq_inv_of_mul_eq_one_left this
    rw [h2, Real.log_inv]
  have hZ : sxZ q ![a, b, b, b] = a ^ q * (1 + 3 * Real.exp (-(q * z))) := by
    unfold sxZ; rw [sx_sum_family, hbq]; ring
  have hlogZ : Real.log (a ^ q * (1 + 3 * Real.exp (-(q * z))))
      = q * Real.log a + Real.log (1 + 3 * Real.exp (-(q * z))) := by
    rw [Real.log_mul hA.ne' (by positivity), Real.log_rpow ha]
  have hk := q_mul_sxKappa hq
  unfold sxPhiVec sxV sxU
  rw [hZ, hlogZ]
  unfold sxPhi
  rw [sx_sumlog_family, hbq, hlb]
  have h3 : 0 < 1 + 3 * Real.exp (-(q * z)) := by positivity
  have e : (a ^ q * Real.log a + 3 * (a ^ q * Real.exp (-(q * z)) * (Real.log a - z)))
        / (a ^ q * (1 + 3 * Real.exp (-(q * z))))
      = Real.log a - z * (3 * Real.exp (-(q * z)) / (1 + 3 * Real.exp (-(q * z)))) := by
    field_simp; ring
  rw [e, hla]
  linear_combination (Real.log (1 + 3 * Real.exp (-z))) * hk

theorem sxPhiVec_hsSpec {q : ℝ} (hq : 1 < q) : sxPhiVec q hsSpec = sxPhi q (Real.log 3) := by
  have := sxPhiVec_family hq (a := 1 / 2) (b := 1 / 6) (by norm_num) (by norm_num) (by norm_num)
  have h3 : ((1 : ℝ) / 2) / (1 / 6) = 3 := by norm_num
  rw [h3] at this
  exact this

/-- **One-large family, `lem:fqe-renyi-single-crossing`.** For `q > 1` and `a ≥ b > 0`, `a + 3b = 1`:
`φ_q(a,b,b,b) ≤ φ_q(σ)`, `σ = (1/2,1/6,1/6,1/6)`, with `φ = v_q - κ_q u_q`. -/
theorem sxFamily_le {q : ℝ} (hq : 1 < q) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + 3 * b = 1) (hba : b ≤ a) : sxPhiVec q ![a, b, b, b] ≤ sxPhiVec q hsSpec := by
  rw [sxPhiVec_family hq ha hb hab, sxPhiVec_hsSpec hq]
  apply sxPhi_le hq
  exact Real.log_nonneg ((one_le_div hb).mpr hba)

/-- Equality case of the one-large family: only `(a,b) = (1/2, 1/6)`. -/
theorem sxFamily_eq {q : ℝ} (hq : 1 < q) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + 3 * b = 1) (hba : b ≤ a) (h : sxPhiVec q ![a, b, b, b] = sxPhiVec q hsSpec) :
    a = 1 / 2 ∧ b = 1 / 6 := by
  rw [sxPhiVec_family hq ha hb hab, sxPhiVec_hsSpec hq] at h
  have hz : Real.log (a / b) = Real.log 3 := by
    by_contra hne
    exact (sxPhi_lt hq (Real.log_nonneg ((one_le_div hb).mpr hba)) hne).ne h
  have h2 : a / b = 3 := Real.log_injOn_pos (Set.mem_Ioi.mpr (div_pos ha hb))
    (Set.mem_Ioi.mpr (by norm_num)) hz
  have h3 : a = 3 * b := by field_simp at h2; linarith
  constructor <;> linarith

end FormalResearch.FourQubitEntropy
