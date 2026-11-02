import FormalResearch.FourQubitEntropy.EntropyPurityEnvelope

/-!
# `lem:seven-entropy-linear-purity`: the sharp entropy–purity slope in every dimension `d ≥ 3`

Source: `ResearchNotes/QI/seven_qubit_entanglement/seven_qubit_entropy_compatibility.tex`,
`lem:seven-entropy-linear-purity` (SP7-5), eq. `eq:entropy-purity-general-slope`.

For every probability vector `λ` on `d ≥ 3` points (entropy `S` in bits),

  `log₂ d - S(λ) ≥ c_d (d ∑ λ² - 1)`,   `c_d = (d-1) log₂(d-1) / (d(d-2))`,

with equality exactly at the uniform spectrum and at `((d-1)/d, (1/[d(d-1)])^{d-1})`
(`entropy_purity_slope_nats`, `entropy_purity_slope_bits`, `entropy_purity_slope_eq_iff`).

Proof (as in the paper).  Put `m = d - 1 ≥ 2`.  By `lem:seven-fixed-purity-envelope`
(`entropy_le_gEnv`) it suffices to treat the one-spike spectrum `((1+mr)/d, ((1-r)/d)^m)`,
`0 ≤ r ≤ 1`, whose purity excess is `d ∑ λ² - 1 = m r²` and whose entropy loss is `F_m(r)/d` (nats) with
`F_m(r) = (1+mr) ln(1+mr) + m(1-r) ln(1-r)` (`Fm`, `spikeEnt_eq`).  The derivative of `F_m/r²` has
numerator `N = r F_m' - 2 F_m` with `N(0) = N'(0) = 0` and `N'' = r F_m'''`, where `F_m'''` has the sign
of `2mr - (m-1)`.  So `N < 0` on `(0, r_*)` and `N > 0` on `(r_*, 1)`, `r_* = (m-1)/m` (where `N(r_*) = 0`),
and `F_m/r²` has its strict minimum `m² ln m/(m-1)` exactly at `r_*` (`Fm_ge_sharp`, `Fm_eq_iff`).
Equality in the slope forces equality in the envelope (`entropy_eq_gEnv_iff`) and `r ∈ {0, r_*}`.

Everything is proved (no hypotheses).  The `d = 8` instances are
`SevenQubitConseq.LinPur.entropy_linear_purity_*`.
-/

open Real Finset

namespace FormalResearch.FourQubitEntropy.EntropyPurity

/-! ### The function `F_m` and its derivatives -/

/-- `F_m(r) = (1+mr) ln(1+mr) + m(1-r) ln(1-r)`, written with `negMulLog` (so `F_m(1)` is defined). -/
noncomputable def Fm (m r : ℝ) : ℝ := -(negMulLog (1 + m * r) + m * negMulLog (1 - r))

/-- `F_m'(r)`. -/
noncomputable def F1m (m r : ℝ) : ℝ := m * (log (1 + m * r) - log (1 - r))

/-- `F_m''(r)`. -/
noncomputable def F2m (m r : ℝ) : ℝ := m * (m + 1) / ((1 + m * r) * (1 - r))

/-- `F_m'''(r)`. -/
noncomputable def F3m (m r : ℝ) : ℝ :=
  m * (m + 1) * (2 * m * r - (m - 1)) / ((1 + m * r) * (1 - r)) ^ 2

/-- `N(r) = r F_m'(r) - 2 F_m(r)`. -/
noncomputable def Nm (m r : ℝ) : ℝ := r * F1m m r - 2 * Fm m r

/-- `N'(r) = r F_m''(r) - F_m'(r)`. -/
noncomputable def N1m (m r : ℝ) : ℝ := r * F2m m r - F1m m r

/-- `F_m(r)/r²`. -/
noncomputable def phiM (m r : ℝ) : ℝ := Fm m r / r ^ 2

section deriv

variable {m r : ℝ}

theorem Fm_continuous (m : ℝ) : Continuous (Fm m) := by
  unfold Fm; fun_prop

theorem Fm_zero (m : ℝ) : Fm m 0 = 0 := by simp [Fm]

theorem lin_hasDerivAt (m r : ℝ) : HasDerivAt (fun r : ℝ => 1 + m * r) m r := by
  simpa using ((hasDerivAt_id r).const_mul m).const_add 1

theorem one_sub_hasDerivAt (r : ℝ) : HasDerivAt (fun r : ℝ => 1 - r) (-1) r := by
  simpa using (hasDerivAt_id r).const_sub 1

theorem Fm_hasDerivAt (hm : 0 < m) (h0 : 0 ≤ r) (h1 : r < 1) :
    HasDerivAt (Fm m) (F1m m r) r := by
  have p1 : 0 < 1 + m * r := by positivity
  have p2 : 0 < 1 - r := by linarith
  have ha := (Real.hasDerivAt_negMulLog p1.ne').comp r (lin_hasDerivAt m r)
  have hb := (Real.hasDerivAt_negMulLog p2.ne').comp r (one_sub_hasDerivAt r)
  have h := (ha.add (hb.const_mul m)).neg
  have hF : Fm m = fun x => -((negMulLog ∘ fun r => 1 + m * r) x +
      m * (negMulLog ∘ fun r => 1 - r) x) := by
    funext x; simp [Fm]
  rw [hF]
  refine h.congr_deriv ?_
  unfold F1m; ring

theorem F1m_hasDerivAt (hm : 0 < m) (h0 : 0 ≤ r) (h1 : r < 1) :
    HasDerivAt (F1m m) (F2m m r) r := by
  have p1 : 0 < 1 + m * r := by positivity
  have p2 : 0 < 1 - r := by linarith
  have h := (((lin_hasDerivAt m r).log p1.ne').sub ((one_sub_hasDerivAt r).log p2.ne')).const_mul m
  refine h.congr_deriv ?_
  unfold F2m; field_simp; ring

theorem F2m_hasDerivAt (hm : 0 < m) (h0 : 0 ≤ r) (h1 : r < 1) :
    HasDerivAt (F2m m) (F3m m r) r := by
  have p1 : 0 < 1 + m * r := by positivity
  have p2 : 0 < 1 - r := by linarith
  have hd := (lin_hasDerivAt m r).mul (one_sub_hasDerivAt r)
  have hc : HasDerivAt (fun _ : ℝ => m * (m + 1)) 0 r := hasDerivAt_const r _
  have h := hc.div hd (by show (1 + m * r) * (1 - r) ≠ 0; positivity)
  have hF : F2m m = (fun _ : ℝ => m * (m + 1)) / ((fun r : ℝ => 1 + m * r) * fun r : ℝ => 1 - r) := by
    funext x; simp [F2m]
  rw [hF]
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  unfold F3m; field_simp; ring

theorem Nm_hasDerivAt (hm : 0 < m) (h0 : 0 ≤ r) (h1 : r < 1) :
    HasDerivAt (Nm m) (N1m m r) r := by
  have h := ((hasDerivAt_id r).mul (F1m_hasDerivAt hm h0 h1)).sub
    ((Fm_hasDerivAt hm h0 h1).const_mul 2)
  have hF : Nm m = fun x => id x * F1m m x - 2 * Fm m x := by funext x; simp [Nm]
  rw [hF]
  refine h.congr_deriv ?_
  unfold N1m; simp only [id]; ring

theorem N1m_hasDerivAt (hm : 0 < m) (h0 : 0 ≤ r) (h1 : r < 1) :
    HasDerivAt (N1m m) (r * F3m m r) r := by
  have h := ((hasDerivAt_id r).mul (F2m_hasDerivAt hm h0 h1)).sub (F1m_hasDerivAt hm h0 h1)
  have hF : N1m m = fun x => id x * F2m m x - F1m m x := by funext x; simp [N1m]
  rw [hF]
  refine h.congr_deriv ?_
  simp only [id]; ring

theorem F3m_neg (hm : 1 < m) (h0 : 0 ≤ r) (h1 : r < (m - 1) / (2 * m)) : F3m m r < 0 := by
  have hm0 : 0 < m := by linarith
  have p1 : 0 < 1 + m * r := by positivity
  have hr1 : r < 1 := by
    have : (m - 1) / (2 * m) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  have p2 : 0 < 1 - r := by linarith
  have hnum : 2 * m * r - (m - 1) < 0 := by
    rw [lt_div_iff₀ (by positivity)] at h1; linarith
  unfold F3m
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hnum) (by positivity)

theorem F3m_nonneg (hm : 1 < m) (h0 : (m - 1) / (2 * m) ≤ r) (h1 : r < 1) : 0 ≤ F3m m r := by
  have hm0 : 0 < m := by linarith
  have hr0 : 0 ≤ r := le_trans (div_nonneg (by linarith) (by positivity)) h0
  have p1 : 0 < 1 + m * r := by positivity
  have p2 : 0 < 1 - r := by linarith
  have hnum : 0 ≤ 2 * m * r - (m - 1) := by
    rw [div_le_iff₀ (by positivity)] at h0; linarith
  unfold F3m
  exact div_nonneg (mul_nonneg (by positivity) hnum) (by positivity)

end deriv

/-! ### Sign of `N` -/

section sign

variable {m : ℝ}

/-- A convex function lies below its chord. -/
theorem convex_chord {D : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ D f) {x y z : ℝ} (hx : x ∈ D)
    (hz : z ∈ D) (hxy : x < y) (hyz : y < z) :
    f y ≤ (z - y) / (z - x) * f x + (y - x) / (z - x) * f z := by
  have hzx : 0 < z - x := by linarith
  have hA : 0 ≤ (z - y) / (z - x) := div_nonneg (by linarith) hzx.le
  have hB : 0 ≤ (y - x) / (z - x) := div_nonneg (by linarith) hzx.le
  have hab : (z - y) / (z - x) + (y - x) / (z - x) = 1 := by field_simp; ring
  have h := hf.2 hx hz hA hB hab
  have e : ((z - y) / (z - x)) • x + ((y - x) / (z - x)) • z = y := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [e, smul_eq_mul, smul_eq_mul] at h
  exact h

/-- `N < 0` on `(0, r₀]`, `r₀ = (m-1)/(2m)`. -/
theorem Nm_neg_low (hm : 1 < m) {r : ℝ} (h0 : 0 < r) (h1 : r ≤ (m - 1) / (2 * m)) : Nm m r < 0 := by
  have hm0 : 0 < m := by linarith
  set r0 := (m - 1) / (2 * m) with hr0
  have hr01 : r0 < 1 := by rw [hr0, div_lt_one (by positivity)]; linarith
  have hN1 : StrictAntiOn (N1m m) (Set.Icc 0 r0) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
    · intro x hx
      exact (N1m_hasDerivAt hm0 hx.1 (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(N1m_hasDerivAt hm0 hx.1.le (by linarith [hx.2])).deriv]
      exact mul_neg_of_pos_of_neg hx.1 (F3m_neg hm hx.1.le hx.2)
  have e0 : N1m m 0 = 0 := by simp [N1m, F2m, F1m]
  have hneg : ∀ x ∈ Set.Ioc 0 r0, N1m m x < 0 := by
    intro x hx
    have := hN1 (a := 0) (b := x) ⟨le_rfl, by linarith [hx.1, hx.2]⟩ ⟨hx.1.le, hx.2⟩ hx.1
    rwa [e0] at this
  have hN : StrictAntiOn (Nm m) (Set.Icc 0 r0) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
    · intro x hx
      exact (Nm_hasDerivAt hm0 hx.1 (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(Nm_hasDerivAt hm0 hx.1.le (by linarith [hx.2])).deriv]
      exact hneg x ⟨hx.1, hx.2.le⟩
  have e1 : Nm m 0 = 0 := by simp [Nm, F1m, Fm]
  have := hN (a := 0) (b := r) ⟨le_rfl, by linarith⟩ ⟨h0.le, h1⟩ h0
  rwa [e1] at this

/-- `N` is convex on `[r₀, 1)`. -/
theorem Nm_convexOn (hm : 1 < m) : ConvexOn ℝ (Set.Ico ((m - 1) / (2 * m)) 1) (Nm m) := by
  have hm0 : 0 < m := by linarith
  have hr00 : 0 ≤ (m - 1) / (2 * m) := div_nonneg (by linarith) (by positivity)
  have hmono : MonotoneOn (N1m m) (Set.Ioo ((m - 1) / (2 * m)) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo _ _) ?_ ?_ ?_
    · intro x hx
      exact (N1m_hasDerivAt hm0 (by linarith [hx.1]) hx.2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      exact (N1m_hasDerivAt hm0 (by linarith [hx.1]) hx.2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      rw [(N1m_hasDerivAt hm0 (by linarith [hx.1]) hx.2).deriv]
      exact mul_nonneg (by linarith [hx.1]) (F3m_nonneg hm hx.1.le hx.2)
  refine MonotoneOn.convexOn_of_deriv (convex_Ico _ _) ?_ ?_ ?_
  · intro x hx
    exact (Nm_hasDerivAt hm0 (by linarith [hx.1]) hx.2).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    exact (Nm_hasDerivAt hm0 (by linarith [hx.1]) hx.2).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [interior_Ico] at hx hy
    rw [(Nm_hasDerivAt hm0 (by linarith [hx.1]) hx.2).deriv,
      (Nm_hasDerivAt hm0 (by linarith [hy.1]) hy.2).deriv]
    exact hmono hx hy hxy

/-- Values at `r_* = (m-1)/m`: `1 + m r_* = m`, `1 - r_* = 1/m`, `F_m(r_*) = (m-1) ln m`,
`F_m'(r_*) = 2m ln m`. -/
theorem Fm_rs (hm : 1 < m) : Fm m ((m - 1) / m) = (m - 1) * log m ∧
    F1m m ((m - 1) / m) = 2 * m * log m := by
  have hm0 : 0 < m := by linarith
  have e1 : 1 + m * ((m - 1) / m) = m := by field_simp; ring
  have e2 : 1 - (m - 1) / m = m⁻¹ := by field_simp; ring
  unfold Fm F1m
  rw [e1, e2]
  simp only [negMulLog, Real.log_inv]
  constructor
  · field_simp; ring
  · ring

theorem Nm_rs (hm : 1 < m) : Nm m ((m - 1) / m) = 0 := by
  obtain ⟨hF, h1⟩ := Fm_rs hm
  have hm0 : 0 < m := by linarith
  unfold Nm; rw [hF, h1]; field_simp; ring

theorem r0_lt_rs (hm : 1 < m) : (m - 1) / (2 * m) < (m - 1) / m := by
  have hm0 : 0 < m := by linarith
  rw [div_lt_div_iff₀ (by positivity) hm0]; nlinarith

theorem rs_lt_one (hm : 1 < m) : (m - 1) / m < 1 := by
  have hm0 : 0 < m := by linarith
  rw [div_lt_one hm0]; linarith

/-- `N < 0` on `(0, r_*)`. -/
theorem Nm_neg (hm : 1 < m) {r : ℝ} (h0 : 0 < r) (h1 : r < (m - 1) / m) : Nm m r < 0 := by
  have hm0 : 0 < m := by linarith
  set r0 := (m - 1) / (2 * m)
  have hr0 : 0 < r0 := div_pos (by linarith) (by positivity)
  rcases le_or_gt r r0 with h | h
  · exact Nm_neg_low hm h0 h
  · have ha := Nm_neg_low hm hr0 le_rfl
    have hc := convex_chord (Nm_convexOn hm) ⟨le_rfl, by linarith [r0_lt_rs hm, rs_lt_one hm]⟩
      ⟨(r0_lt_rs hm).le, rs_lt_one hm⟩ h h1
    rw [Nm_rs hm, mul_zero, add_zero] at hc
    have hp : 0 < ((m - 1) / m - r) / ((m - 1) / m - r0) :=
      div_pos (by linarith) (by linarith [r0_lt_rs hm])
    exact lt_of_le_of_lt hc (mul_neg_of_pos_of_neg hp ha)

/-- `N > 0` on `(r_*, 1)`. -/
theorem Nm_pos (hm : 1 < m) {r : ℝ} (h0 : (m - 1) / m < r) (h1 : r < 1) : 0 < Nm m r := by
  have hm0 : 0 < m := by linarith
  set r0 := (m - 1) / (2 * m)
  have hr0 : 0 < r0 := div_pos (by linarith) (by positivity)
  have ha := Nm_neg_low hm hr0 le_rfl
  have hc := convex_chord (Nm_convexOn hm) ⟨le_rfl, by linarith [r0_lt_rs hm, rs_lt_one hm]⟩
    ⟨by linarith [r0_lt_rs hm], h1⟩ (r0_lt_rs hm) h0
  rw [Nm_rs hm] at hc
  have hp : 0 < (r - (m - 1) / m) / (r - r0) := div_pos (by linarith) (by linarith [r0_lt_rs hm])
  have hq : 0 < ((m - 1) / m - r0) / (r - r0) :=
    div_pos (by linarith [r0_lt_rs hm]) (by linarith [r0_lt_rs hm])
  by_contra hneg
  have h3 := mul_nonpos_of_nonneg_of_nonpos hq.le (not_lt.1 hneg)
  have h4 : 0 < (r - (m - 1) / m) / (r - r0) * (-Nm m r0) := mul_pos hp (by linarith)
  nlinarith

end sign

/-! ### The sharp constant: `F_m(r) ≥ m² ln m/(m-1) · r²`, equality only at `r ∈ {0, r_*}` -/

section sharp

variable {m : ℝ}

theorem phiM_hasDerivAt (hm : 0 < m) {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    HasDerivAt (phiM m) (Nm m r / r ^ 3) r := by
  have h := (Fm_hasDerivAt hm h0.le h1).div (hasDerivAt_pow 2 r) (by positivity)
  have hF : phiM m = fun x => Fm m x / x ^ 2 := by funext x; simp [phiM]
  rw [hF]
  refine h.congr_deriv ?_
  unfold Nm; push_cast; field_simp

theorem phiM_rs (hm : 1 < m) : phiM m ((m - 1) / m) = m ^ 2 * log m / (m - 1) := by
  obtain ⟨hF, -⟩ := Fm_rs hm
  have hm0 : 0 < m := by linarith
  have hm1 : m - 1 ≠ 0 := by linarith
  unfold phiM; rw [hF]; field_simp

theorem phiM_strictAntiOn (hm : 1 < m) : StrictAntiOn (phiM m) (Set.Ioc 0 ((m - 1) / m)) := by
  have hm0 : 0 < m := by linarith
  refine strictAntiOn_of_deriv_neg (convex_Ioc _ _) ?_ ?_
  · intro x hx
    exact (phiM_hasDerivAt hm0 hx.1 (by linarith [hx.2, rs_lt_one hm])).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    rw [(phiM_hasDerivAt hm0 hx.1 (by linarith [hx.2, rs_lt_one hm])).deriv]
    exact div_neg_of_neg_of_pos (Nm_neg hm hx.1 hx.2) (by have := hx.1; positivity)

theorem phiM_strictMonoOn (hm : 1 < m) : StrictMonoOn (phiM m) (Set.Icc ((m - 1) / m) 1) := by
  have hm0 : 0 < m := by linarith
  have hrs0 : 0 < (m - 1) / m := div_pos (by linarith) hm0
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
  · intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have : ContinuousAt (fun x => Fm m x / x ^ 2) x :=
      (Fm_continuous m).continuousAt.div (continuous_pow 2).continuousAt (pow_ne_zero 2 hx0.ne')
    exact this.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [(phiM_hasDerivAt hm0 hx0 hx.2).deriv]
    exact div_pos (Nm_pos hm hx.1 hx.2) (by positivity)

/-- **Sharp constant** (proof of `lem:seven-entropy-linear-purity`): for `m > 1` and `0 ≤ r ≤ 1`,
`m² ln m/(m-1) · r² ≤ F_m(r)`. -/
theorem Fm_ge_sharp (hm : 1 < m) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    m ^ 2 * log m / (m - 1) * r ^ 2 ≤ Fm m r := by
  rcases h0.eq_or_lt with hr | hr
  · subst hr; simp [Fm_zero]
  have hphi : m ^ 2 * log m / (m - 1) ≤ phiM m r := by
    rcases le_total r ((m - 1) / m) with h | h
    · have := (phiM_strictAntiOn hm).antitoneOn ⟨hr, h⟩ ⟨div_pos (by linarith) (by linarith), le_rfl⟩ h
      rwa [phiM_rs hm] at this
    · have := (phiM_strictMonoOn hm).monotoneOn ⟨le_rfl, (rs_lt_one hm).le⟩ ⟨h, h1⟩ h
      rwa [phiM_rs hm] at this
  unfold phiM at hphi
  rwa [le_div_iff₀ (by positivity)] at hphi

/-- **Equality in the sharp constant**: for `m > 1` and `0 ≤ r ≤ 1`,
`F_m(r) = m² ln m/(m-1) · r²` iff `r = 0` or `r = (m-1)/m`. -/
theorem Fm_eq_iff (hm : 1 < m) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    Fm m r = m ^ 2 * log m / (m - 1) * r ^ 2 ↔ r = 0 ∨ r = (m - 1) / m := by
  have hrs0 : 0 < (m - 1) / m := div_pos (by linarith) (by linarith)
  constructor
  · intro heq
    rcases h0.eq_or_lt with hr | hr
    · exact Or.inl hr.symm
    right
    by_contra hne
    have hphi : m ^ 2 * log m / (m - 1) < phiM m r := by
      rcases lt_or_gt_of_ne hne with h | h
      · have := (phiM_strictAntiOn hm) ⟨hr, h.le⟩ ⟨hrs0, le_rfl⟩ h
        rwa [phiM_rs hm] at this
      · have := (phiM_strictMonoOn hm) ⟨le_rfl, (rs_lt_one hm).le⟩ ⟨h.le, h1⟩ h
        rwa [phiM_rs hm] at this
    unfold phiM at hphi
    rw [lt_div_iff₀ (by positivity)] at hphi
    linarith
  · rintro (h | h)
    · subst h; simp [Fm_zero]
    · have := phiM_rs hm
      rw [← h] at this
      unfold phiM at this
      rw [div_eq_iff (by rw [h]; exact pow_ne_zero 2 hrs0.ne')] at this
      exact this

end sharp

/-! ### The spike spectrum in terms of `F_m` -/

/-- With `m = d - 1`: the spike `((1+mr)/d, ((1-r)/d)^m)` has entropy `ln d - F_m(r)/d`. -/
theorem spikeEnt_eq {d r : ℝ} (hd : 1 < d) :
    spikeEnt d ((1 + (d - 1) * r) / d) = log d - Fm (d - 1) r / d := by
  have hd0 : 0 < d := by linarith
  have hm : d - 1 ≠ 0 := by linarith
  have e : (1 - (1 + (d - 1) * r) / d) / (d - 1) = (1 - r) * d⁻¹ := by field_simp; ring
  have e2 : (1 + (d - 1) * r) / d = (1 + (d - 1) * r) * d⁻¹ := div_eq_mul_inv _ _
  have hinv : negMulLog d⁻¹ = d⁻¹ * log d := by simp [negMulLog, Real.log_inv]
  unfold spikeEnt Fm
  rw [e, e2, negMulLog_mul, negMulLog_mul, hinv]
  field_simp
  ring

/-! ### The slope -/

/-- The sharp slope `c_d = (d-1) log₂(d-1)/(d(d-2))` (`eq:entropy-purity-general-slope`), in bits. -/
noncomputable def slopeBits (d : ℝ) : ℝ := (d - 1) * Real.logb 2 (d - 1) / (d * (d - 2))

/-- The common reduction: with `m = d - 1`, `s = √(m(dp-1))`, `r = s/m`, one has
`d p - 1 = m r²`, `g_d(p) = ln d - F_m(r)/d` and `0 ≤ r ≤ 1`. -/
theorem slope_reduction {d p : ℝ} (hd : 2 < d) (hp1 : 1 / d ≤ p) (hp2 : p ≤ 1) :
    ∃ r, 0 ≤ r ∧ r ≤ 1 ∧ d * p - 1 = (d - 1) * r ^ 2 ∧ gEnv d p = log d - Fm (d - 1) r / d ∧
      spikeWt d p = (1 + (d - 1) * r) / d := by
  obtain ⟨hs0, hsm, hs2, -, -, -, ht⟩ := spike_data (by linarith : (1 : ℝ) < d) hp1 hp2
  set s := Real.sqrt ((d - 1) * (d * p - 1))
  have hm : 0 < d - 1 := by linarith
  have ht' : spikeWt d p = (1 + (d - 1) * (s / (d - 1))) / d := by rw [ht]; field_simp
  refine ⟨s / (d - 1), div_nonneg hs0 hm.le, (div_le_one hm).2 hsm, ?_, ?_, ht'⟩
  · field_simp; nlinarith
  · unfold gEnv; rw [ht']; exact spikeEnt_eq (by linarith)

/-- **`lem:seven-entropy-linear-purity`, `eq:entropy-purity-general-slope`, in nats.**  For every
probability vector `λ` on a `d`-point set, `d ≥ 3`:
`(d-1) ln(d-1)/(d(d-2)) · (d ∑ λ² - 1) ≤ ln d - ∑ -λ ln λ`. -/
theorem entropy_purity_slope_nats {ι : Type*} [Fintype ι] {d : ℕ} (hd : 3 ≤ d)
    (hcard : Fintype.card ι = d) (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    ((d : ℝ) - 1) * log ((d : ℝ) - 1) / ((d : ℝ) * ((d : ℝ) - 2)) * ((d : ℝ) * ∑ i, lam i ^ 2 - 1) ≤
      log d - ∑ i, negMulLog (lam i) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : 1 / (d : ℝ) ≤ ∑ i, lam i ^ 2 := sum_sq_ge_inv hcard (by omega) lam h1
  have hp2 := sum_sq_le_one lam h0 h1
  obtain ⟨r, hr0, hr1, hp, hg, -⟩ := slope_reduction (by linarith) hp1 hp2
  have hS := entropy_le_gEnv (by omega) hcard lam h0 h1
  have hF := Fm_ge_sharp (m := (d : ℝ) - 1) (by linarith) hr0 hr1
  rw [hp]
  have e : ((d : ℝ) - 1) * log ((d : ℝ) - 1) / ((d : ℝ) * ((d : ℝ) - 2)) * (((d : ℝ) - 1) * r ^ 2) =
      (((d : ℝ) - 1) ^ 2 * log ((d : ℝ) - 1) / ((d : ℝ) - 1 - 1) * r ^ 2) / d := by
    have : (d : ℝ) - 2 ≠ 0 := by linarith
    have : (d : ℝ) - 1 - 1 ≠ 0 := by linarith
    have : (d : ℝ) ≠ 0 := by linarith
    field_simp; ring
  rw [e]
  have hd0 : (0 : ℝ) < d := by linarith
  have : (((d : ℝ) - 1) ^ 2 * log ((d : ℝ) - 1) / ((d : ℝ) - 1 - 1) * r ^ 2) / d ≤
      Fm ((d : ℝ) - 1) r / d := div_le_div_of_nonneg_right hF hd0.le
  linarith

/-- **`lem:seven-entropy-linear-purity`, `eq:entropy-purity-general-slope`, in bits.**  For every
probability vector `λ` on a `d`-point set, `d ≥ 3`, with `S(λ) = (∑ -λ ln λ)/ln 2`:
`c_d (d ∑ λ² - 1) ≤ log₂ d - S(λ)`, `c_d = (d-1) log₂(d-1)/(d(d-2))`. -/
theorem entropy_purity_slope_bits {ι : Type*} [Fintype ι] {d : ℕ} (hd : 3 ≤ d)
    (hcard : Fintype.card ι = d) (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    slopeBits d * ((d : ℝ) * ∑ i, lam i ^ 2 - 1) ≤
      Real.logb 2 d - (∑ i, negMulLog (lam i)) / log 2 := by
  have l2 : 0 < log 2 := Real.log_pos (by norm_num)
  have h := entropy_purity_slope_nats hd hcard lam h0 h1
  have e1 : slopeBits d * ((d : ℝ) * ∑ i, lam i ^ 2 - 1) =
      (((d : ℝ) - 1) * log ((d : ℝ) - 1) / ((d : ℝ) * ((d : ℝ) - 2)) *
        ((d : ℝ) * ∑ i, lam i ^ 2 - 1)) / log 2 := by
    unfold slopeBits Real.logb; ring
  have e2 : Real.logb 2 d - (∑ i, negMulLog (lam i)) / log 2 =
      (log d - ∑ i, negMulLog (lam i)) / log 2 := by
    unfold Real.logb; ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right h l2.le

/-- **`lem:seven-entropy-linear-purity`, equality case.**  For a probability vector `λ` on a `d`-point
set, `d ≥ 3`, equality holds in `eq:entropy-purity-general-slope` iff `λ` is uniform or is the spectrum
`((d-1)/d, (1/[d(d-1)])^{d-1})` (one entry `(d-1)/d`, all others `1/(d(d-1))`). -/
theorem entropy_purity_slope_eq_iff {ι : Type*} [Fintype ι] {d : ℕ} (hd : 3 ≤ d)
    (hcard : Fintype.card ι = d) (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    ((d : ℝ) - 1) * log ((d : ℝ) - 1) / ((d : ℝ) * ((d : ℝ) - 2)) * ((d : ℝ) * ∑ i, lam i ^ 2 - 1) =
      log d - ∑ i, negMulLog (lam i) ↔
    (∀ i, lam i = 1 / (d : ℝ)) ∨
      ∃ i0, lam i0 = ((d : ℝ) - 1) / d ∧ ∀ i, i ≠ i0 → lam i = 1 / ((d : ℝ) * ((d : ℝ) - 1)) := by
  classical
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hm1 : (d : ℝ) - 1 - 1 ≠ 0 := by linarith
  have hd2 : (d : ℝ) - 2 ≠ 0 := by linarith
  have hm0 : (d : ℝ) - 1 ≠ 0 := by linarith
  set p := ∑ i, lam i ^ 2 with hpdef
  have hp1 : 1 / (d : ℝ) ≤ p := sum_sq_ge_inv hcard (by omega) lam h1
  have hp2 := sum_sq_le_one lam h0 h1
  obtain ⟨r, hr0, hr1, hp, hg, ht⟩ := slope_reduction (by linarith) hp1 hp2
  have hS := entropy_le_gEnv (by omega) hcard lam h0 h1
  have hF := Fm_ge_sharp (m := (d : ℝ) - 1) (by linarith) hr0 hr1
  have e : ((d : ℝ) - 1) * log ((d : ℝ) - 1) / ((d : ℝ) * ((d : ℝ) - 2)) * (((d : ℝ) - 1) * r ^ 2) =
      (((d : ℝ) - 1) ^ 2 * log ((d : ℝ) - 1) / ((d : ℝ) - 1 - 1) * r ^ 2) / d := by
    field_simp; ring
  constructor
  · intro heq
    rw [hp, e] at heq
    rw [← hpdef] at hS
    -- both inequalities in the chain are equalities
    have hFd : Fm ((d : ℝ) - 1) r / d =
        (((d : ℝ) - 1) ^ 2 * log ((d : ℝ) - 1) / ((d : ℝ) - 1 - 1) * r ^ 2) / d := by
      have : (((d : ℝ) - 1) ^ 2 * log ((d : ℝ) - 1) / ((d : ℝ) - 1 - 1) * r ^ 2) / d ≤
          Fm ((d : ℝ) - 1) r / d := div_le_div_of_nonneg_right hF hd0.le
      linarith
    have hSe : ∑ i, negMulLog (lam i) = gEnv d p := by
      have : (((d : ℝ) - 1) ^ 2 * log ((d : ℝ) - 1) / ((d : ℝ) - 1 - 1) * r ^ 2) / d ≤
          Fm ((d : ℝ) - 1) r / d := div_le_div_of_nonneg_right hF hd0.le
      linarith
    have hFe : Fm ((d : ℝ) - 1) r =
        ((d : ℝ) - 1) ^ 2 * log ((d : ℝ) - 1) / ((d : ℝ) - 1 - 1) * r ^ 2 := by
      field_simp at hFd
      rw [div_mul_eq_mul_div, eq_div_iff hm1]
      linear_combination hFd
    obtain ⟨i0, ha, hb⟩ := (entropy_eq_gEnv_iff (by omega) hcard lam h0 h1).1 hSe
    rw [← hpdef, ht] at ha hb
    rcases (Fm_eq_iff (m := (d : ℝ) - 1) (by linarith) hr0 hr1).1 hFe with hr | hr
    · left
      subst hr
      intro i
      by_cases hi : i = i0
      · rw [hi, ha]; ring
      · rw [hb i hi]; field_simp; ring
    · right
      refine ⟨i0, ?_, fun i hi => ?_⟩
      · rw [ha, hr]; field_simp; ring
      · rw [hb i hi, hr]; field_simp; ring
  · have l1 : negMulLog (1 / (d : ℝ)) = log d / d := by
      simp [negMulLog, Real.log_inv]; ring
    rintro (hu | ⟨i0, ha, hb⟩)
    · have hsq : ∑ i, lam i ^ 2 = 1 / d := by
        simp only [hu, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]; field_simp
      have hS' : ∑ i, negMulLog (lam i) = log d := by
        simp only [hu, l1, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]; field_simp
      rw [hpdef, hsq, hS']; field_simp; ring
    · rw [hpdef, sum_spike hcard lam negMulLog ha hb, sum_spike hcard lam (fun x => x ^ 2) ha hb]
      have hm : (0 : ℝ) < (d : ℝ) - 1 := by linarith
      have e1 : negMulLog (((d : ℝ) - 1) / d) = -(((d : ℝ) - 1) / d) * (log ((d : ℝ) - 1) - log d) := by
        simp only [negMulLog]; rw [Real.log_div hm.ne' hd0.ne']
      have e2 : negMulLog (1 / ((d : ℝ) * ((d : ℝ) - 1))) =
          (1 / ((d : ℝ) * ((d : ℝ) - 1))) * (log d + log ((d : ℝ) - 1)) := by
        simp only [negMulLog, one_div, Real.log_inv]
        rw [Real.log_mul hd0.ne' hm.ne']; ring
      rw [e1, e2]
      field_simp
      ring

/-- info: 'FormalResearch.FourQubitEntropy.EntropyPurity.Fm_ge_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Fm_ge_sharp

/-- info: 'FormalResearch.FourQubitEntropy.EntropyPurity.Fm_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Fm_eq_iff

/-- info: 'FormalResearch.FourQubitEntropy.EntropyPurity.entropy_purity_slope_nats' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropy_purity_slope_nats

/-- info: 'FormalResearch.FourQubitEntropy.EntropyPurity.entropy_purity_slope_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropy_purity_slope_bits

/-- info: 'FormalResearch.FourQubitEntropy.EntropyPurity.entropy_purity_slope_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropy_purity_slope_eq_iff

end FormalResearch.FourQubitEntropy.EntropyPurity
