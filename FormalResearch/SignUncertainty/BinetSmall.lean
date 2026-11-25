module

public import FormalResearch.SignUncertainty.BinetFract
public import FormalResearch.SignUncertainty.BinetDecay

/-!
# Small-`τ` expansion of the Binet remainder (`ct:binet-small`)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:dual-id` (1), `(ct:binet-small)`.

**Proved**: for `Re w > 0`, `B_Bin(w) - 1/(12 w) = 6 ∫₀^∞ P₄(s) (s+w)^{-4} ds`, where `P₄ = g₄ ∘ fract`
is the periodic Bernoulli function with `P₄' = P₃`, `P₃' = P₂ - 1/12`.  This gives
`|B_c(iτ) - iτ/(12c(1-iτ))| ≤ 8|τ|/c³`.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open FormalResearch.Asymptotics

namespace FormalResearch.SignUncertainty.BinetDecay

/-- `g₃(u) = u²/4 - u³/6 - u/12`. -/
noncomputable def g3 (u : ℝ) : ℝ := u ^ 2 / 4 - u ^ 3 / 6 - u / 12
/-- `g₄(u) = u³/12 - u⁴/24 - u²/24`. -/
noncomputable def g4 (u : ℝ) : ℝ := u ^ 3 / 12 - u ^ 4 / 24 - u ^ 2 / 24
/-- `g₂(u) - 1/12 = u(1-u)/2 - 1/12`. -/
noncomputable def g2m (u : ℝ) : ℝ := u / 2 - u ^ 2 / 2 - 1 / 12

/-- `P₃ = g₃ ∘ fract`. -/
noncomputable def binP3 (s : ℝ) : ℝ := g3 (Int.fract s)
/-- `P₄ = g₄ ∘ fract`. -/
noncomputable def binP4 (s : ℝ) : ℝ := g4 (Int.fract s)

lemma hasDerivAt_g3 (x : ℝ) : HasDerivAt g3 (g2m x) x := by
  have h := (((hasDerivAt_pow 2 x).div_const 4).sub ((hasDerivAt_pow 3 x).div_const 6)).sub
    ((hasDerivAt_id x).div_const 12)
  refine h.congr_deriv ?_
  unfold g2m; simp; ring

lemma hasDerivAt_g4 (x : ℝ) : HasDerivAt g4 (g3 x) x := by
  have h := ((((hasDerivAt_pow 3 x).div_const 12).sub ((hasDerivAt_pow 4 x).div_const 24)).sub
    ((hasDerivAt_pow 2 x).div_const 24))
  refine h.congr_deriv ?_
  unfold g3; simp; ring

lemma hasDerivAt_binP3 (x : ℝ) : HasDerivAt binP3 (binP2 x - 1 / 12) x := by
  have h := hasDerivAt_comp_fract (g := g3) (g' := g2m) hasDerivAt_g3
    (by norm_num [g3]) (by norm_num [g2m]) x
  have e : g2m (Int.fract x) = binP2 x - 1 / 12 := by unfold g2m binP2; ring
  rw [e] at h
  exact h

lemma hasDerivAt_binP4 (x : ℝ) : HasDerivAt binP4 (binP3 x) x :=
  hasDerivAt_comp_fract (g := g4) (g' := g3) hasDerivAt_g4
    (by norm_num [g4]) (by norm_num [g3]) x

lemma abs_binP3_le (s : ℝ) : |binP3 s| ≤ 1 / 12 := by
  unfold binP3 g3
  have h0 := Int.fract_nonneg s
  have h1 := Int.fract_lt_one s
  set u := Int.fract s
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg h0 (by linarith : 0 ≤ 1 - u), mul_nonneg (mul_nonneg h0 (by linarith : 0 ≤ 1 - u)) h0,
    mul_nonneg (mul_nonneg h0 (by linarith : 0 ≤ 1 - u)) (by linarith : 0 ≤ 1 - u), sq_nonneg (u - 1 / 2)]

lemma abs_binP4_le (s : ℝ) : |binP4 s| ≤ 1 / 24 := by
  unfold binP4 g4
  have h0 := Int.fract_nonneg s
  have h1 := Int.fract_lt_one s
  set u := Int.fract s
  have e : u ^ 3 / 12 - u ^ 4 / 24 - u ^ 2 / 24 = -((u * (1 - u)) ^ 2) / 24 := by ring
  rw [e, abs_le]
  have hu : 0 ≤ u * (1 - u) := mul_nonneg h0 (by linarith)
  have hu2 : u * (1 - u) ≤ 1 := by nlinarith
  constructor <;> nlinarith [sq_nonneg (u * (1 - u)), mul_le_mul hu2 hu2 hu (by norm_num)]

lemma abs_binP2m_le (s : ℝ) : |binP2 s - 1 / 12| ≤ 1 / 8 := by
  have h0 := binP2_nonneg s
  have h1 := binP2_le s
  rw [abs_le]; constructor <;> linarith

lemma continuous_binP3 : Continuous binP3 :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_binP3 x).continuousAt

lemma continuous_binP4 : Continuous binP4 :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_binP4 x).continuousAt

lemma measurable_binP3 : Measurable binP3 := continuous_binP3.measurable

lemma binP3_zero : binP3 0 = 0 := by simp [binP3, g3]
lemma binP4_zero : binP4 0 = 0 := by simp [binP4, g4]


lemma norm_inv_pow_le {w : ℂ} (hw : 0 < w.re) {s : ℝ} (hs : 0 ≤ s) (m : ℕ) :
    ‖(((s : ℂ) + w) ^ m)⁻¹‖ ≤ 2 ^ m * ((s + ‖w‖) ^ m)⁻¹ := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by simp [h] at hw)
  have hlow := half_le_norm_add hw.le hs
  have hpos : 0 < (s + ‖w‖) / 2 := by positivity
  rw [norm_inv, norm_pow]
  calc (‖(s : ℂ) + w‖ ^ m)⁻¹ ≤ (((s + ‖w‖) / 2) ^ m)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hlow _)
    _ = 2 ^ m * ((s + ‖w‖) ^ m)⁻¹ := by rw [div_pow]; field_simp

lemma integrableOn_bdd_mul_inv_pow {P : ℝ → ℝ} {M : ℝ} (hP : Measurable P) (hM : ∀ s, |P s| ≤ M)
    {w : ℂ} (hw : 0 < w.re) {m : ℕ} (hm : 2 ≤ m) :
    IntegrableOn (fun s : ℝ => (P s : ℂ) * (((s : ℂ) + w) ^ m)⁻¹) (Ioi 0) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by simp [h] at hw)
  have hI := (integral_inv_pow_shift hwn k).1.const_mul (M * 2 ^ (k + 2))
  refine Integrable.mono' hI ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    exact (Complex.measurable_ofReal.comp hP).mul (by fun_prop)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have hs' : (0 : ℝ) ≤ s := le_of_lt hs
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |P s| * ‖(((s : ℂ) + w) ^ (k + 2))⁻¹‖ ≤ M * (2 ^ (k + 2) * ((s + ‖w‖) ^ (k + 2))⁻¹) :=
          mul_le_mul (hM s) (norm_inv_pow_le hw hs' _) (norm_nonneg _) ((abs_nonneg _).trans (hM s))
      _ = M * 2 ^ (k + 2) * ((s + ‖w‖) ^ (k + 2))⁻¹ := by ring

/-- Integration by parts for the periodic Bernoulli functions. -/
lemma ibp_step {Pk Pk1 : ℝ → ℝ} {M : ℝ} (hd : ∀ s, HasDerivAt Pk1 (Pk s) s)
    (hmeas : Measurable Pk) (hM : ∀ s, |Pk s| ≤ M) (hM1 : ∀ s, |Pk1 s| ≤ M) (h0 : Pk1 0 = 0)
    {w : ℂ} (hw : 0 < w.re) {m : ℕ} (hm : 2 ≤ m) :
    ∫ s in Ioi (0 : ℝ), (Pk s : ℂ) * (((s : ℂ) + w) ^ m)⁻¹ =
      (m : ℂ) * ∫ s in Ioi (0 : ℝ), (Pk1 s : ℂ) * (((s : ℂ) + w) ^ (m + 1))⁻¹ := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by simp [h] at hw)
  have hcont : Continuous Pk1 := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hspos : ∀ s : ℝ, 0 < s → (s : ℂ) + w ≠ 0 := by
    intro s hs h
    have := congrArg Complex.re h
    simp at this; linarith
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun s : ℝ => (Pk1 s : ℂ)) (Pk x : ℂ) x :=
    fun x _ => (hd x).ofReal_comp
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun s : ℝ => (((s : ℂ) + w) ^ m)⁻¹)
      (-((m : ℂ) * (((x : ℂ) + w) ^ (m + 1))⁻¹)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have h1 : HasDerivAt (fun y : ℂ => ((y + w) ^ m)⁻¹) (-((m : ℂ) * (((x : ℂ) + w) ^ (m + 1))⁻¹)) (x : ℂ) := by
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have := (((hasDerivAt_id (x : ℂ)).add_const w).fun_pow (j + 1)).inv (pow_ne_zero _ (hspos x hx0))
      refine this.congr_deriv ?_
      have hne := hspos x hx0
      simp only [id]
      push_cast
      field_simp
      simp
      ring
    exact h1.comp_ofReal
  have hI1 : IntegrableOn (fun s : ℝ => (Pk1 s : ℂ) * (-((m : ℂ) * (((s : ℂ) + w) ^ (m + 1))⁻¹))) (Ioi 0) := by
    have := (integrableOn_bdd_mul_inv_pow hcont.measurable hM1 hw (by omega : 2 ≤ m + 1)).const_mul (-(m : ℂ))
    refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
    ring
  have hI2 : IntegrableOn (fun s : ℝ => (Pk s : ℂ) * (((s : ℂ) + w) ^ m)⁻¹) (Ioi 0) :=
    integrableOn_bdd_mul_inv_pow hmeas hM hw hm
  have hlim : ∀ {j : ℕ}, 1 ≤ j →
      Tendsto (fun s : ℝ => (Pk1 s : ℂ) * (((s : ℂ) + w) ^ j)⁻¹) atTop (𝓝 0) := by
    intro j hj
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : ∀ᶠ s : ℝ in atTop, ‖(Pk1 s : ℂ) * (((s : ℂ) + w) ^ j)⁻¹‖ ≤ M * 2 ^ j * ((s + ‖w‖) ^ j)⁻¹ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |Pk1 s| * ‖(((s : ℂ) + w) ^ j)⁻¹‖ ≤ M * (2 ^ j * ((s + ‖w‖) ^ j)⁻¹) :=
            mul_le_mul (hM1 s) (norm_inv_pow_le hw hs _) (norm_nonneg _) ((abs_nonneg _).trans (hM1 s))
        _ = _ := by ring
    have hz : Tendsto (fun s : ℝ => M * 2 ^ j * ((s + ‖w‖) ^ j)⁻¹) atTop (𝓝 0) := by
      have h : Tendsto (fun s : ℝ => (s + ‖w‖) ^ j) atTop atTop :=
        (tendsto_pow_atTop (by omega)).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
      simpa using h.inv_tendsto_atTop.const_mul (M * 2 ^ j)
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb hz
  have h0' : Tendsto (fun s : ℝ => (Pk1 s : ℂ) * (((s : ℂ) + w) ^ m)⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun s : ℝ => (Pk1 s : ℂ) * (((s : ℂ) + w) ^ m)⁻¹) 0 := by
      refine ContinuousAt.mul (Complex.continuous_ofReal.comp hcont).continuousAt ?_
      refine ContinuousAt.inv₀ (by fun_prop) ?_
      have : ((0 : ℝ) : ℂ) + w ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      exact pow_ne_zero _ this
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [h0] using this
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hI1 hI2 h0' (hlim (by omega : 1 ≤ m))
  have hI1' : ∫ s in Ioi (0 : ℝ), (Pk1 s : ℂ) * (-((m : ℂ) * (((s : ℂ) + w) ^ (m + 1))⁻¹)) =
      -((m : ℂ) * ∫ s in Ioi (0 : ℝ), (Pk1 s : ℂ) * (((s : ℂ) + w) ^ (m + 1))⁻¹) := by
    rw [← integral_const_mul, ← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioi (fun s _ => by ring)
  simp only [hI1'] at hibp
  linear_combination hibp


lemma integral_inv_sq_shift {w : ℂ} (hw : 0 < w.re) :
    ∫ s in Ioi (0 : ℝ), (((s : ℂ) + w) ^ 2)⁻¹ = 1 / w := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by simp [h] at hw)
  have hspos : ∀ s : ℝ, 0 ≤ s → (s : ℂ) + w ≠ 0 := by
    intro s hs h
    have := congrArg Complex.re h
    simp at this; linarith
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun s : ℝ => -(((s : ℂ) + w)⁻¹)) ((((x : ℂ) + w) ^ 2)⁻¹) x := by
    intro x hx
    have hne := hspos x hx
    have h1 : HasDerivAt (fun y : ℂ => -((y + w)⁻¹)) ((((x : ℂ) + w) ^ 2)⁻¹) (x : ℂ) := by
      have := (((hasDerivAt_id (x : ℂ)).add_const w).inv hne).neg
      refine this.congr_deriv ?_
      simp only [id]
      field_simp
    exact h1.comp_ofReal
  have hint : IntegrableOn (fun s : ℝ => (((s : ℂ) + w) ^ 2)⁻¹) (Ioi 0) := by
    have := integrableOn_bdd_mul_inv_pow (P := fun _ => (1 : ℝ)) (M := 1) measurable_const
      (fun s => by simp) hw (le_refl 2)
    simpa using this
  have hlim : Tendsto (fun s : ℝ => -(((s : ℂ) + w)⁻¹)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : ∀ᶠ s : ℝ in atTop, ‖-(((s : ℂ) + w)⁻¹)‖ ≤ 2 * (s + ‖w‖)⁻¹ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      have := norm_inv_pow_le hw hs 1
      simpa using this
    have hz : Tendsto (fun s : ℝ => 2 * (s + ‖w‖)⁻¹) atTop (𝓝 0) := by
      have h : Tendsto (fun s : ℝ => s + ‖w‖) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
      simpa using h.inv_tendsto_atTop.const_mul 2
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb hz
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim]
  simp

/-- `B_Bin(w) - 1/(12w) = 6 ∫₀^∞ P₄(s) (s+w)^{-4} ds` for `Re w > 0`. -/
theorem binetRem_sub_eq {w : ℂ} (hw : 0 < w.re) :
    binetRem w - 1 / (12 * w) =
      6 * ∫ s in Ioi (0 : ℝ), (binP4 s : ℂ) * (((s : ℂ) + w) ^ 4)⁻¹ := by
  have h0 := iteratedDeriv_binetRem_P2 0 hw
  rw [iteratedDeriv_zero] at h0
  simp only [pow_zero, one_mul, zero_add, Nat.factorial_one, Nat.cast_one, one_div] at h0
  have hP2 : ∫ s in Ioi (0 : ℝ), (binP2 s : ℂ) * (((s : ℂ) + w) ^ 2)⁻¹ =
      (∫ s in Ioi (0 : ℝ), ((binP2 s - 1 / 12 : ℝ) : ℂ) * (((s : ℂ) + w) ^ 2)⁻¹) +
        (1 / 12 : ℂ) * ∫ s in Ioi (0 : ℝ), (((s : ℂ) + w) ^ 2)⁻¹ := by
    have i1 := integrableOn_bdd_mul_inv_pow (P := fun s => binP2 s - 1 / 12) (M := 1 / 8)
      (measurable_binP2.sub measurable_const) abs_binP2m_le hw (le_refl 2)
    have i2 : IntegrableOn (fun s : ℝ => (((s : ℂ) + w) ^ 2)⁻¹) (Ioi 0) := by
      have := integrableOn_bdd_mul_inv_pow (P := fun _ => (1 : ℝ)) (M := 1) measurable_const
        (fun s => by simp) hw (le_refl 2)
      simpa using this
    rw [← integral_const_mul, ← integral_add i1 (i2.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    push_cast
    ring
  have hs1 := ibp_step (Pk := fun s => binP2 s - 1 / 12) (Pk1 := binP3) (M := 1 / 8)
    (fun s => hasDerivAt_binP3 s) (measurable_binP2.sub measurable_const) abs_binP2m_le
    (fun s => (abs_binP3_le s).trans (by norm_num)) binP3_zero hw (le_refl 2)
  have hs2 := ibp_step (Pk := binP3) (Pk1 := binP4) (M := 1 / 12)
    (fun s => hasDerivAt_binP4 s) measurable_binP3 abs_binP3_le
    (fun s => (abs_binP4_le s).trans (by norm_num)) binP4_zero hw (by norm_num : 2 ≤ 3)
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  rw [h0, hP2, integral_inv_sq_shift hw]
  simp only [Nat.cast_ofNat] at hs1 hs2
  rw [hs1, hs2]
  field_simp
  ring


lemma inv_pow4_sub_le {a b : ℂ} {m : ℝ} (hm : 0 < m) (ha : m ≤ ‖a‖) (hb : m ≤ ‖b‖) :
    ‖(a ^ 4)⁻¹ - (b ^ 4)⁻¹‖ ≤ 4 * ‖a - b‖ / m ^ 5 := by
  have ha0 : a ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hm ha)
  have hb0 : b ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hm hb)
  have hx : ‖a⁻¹‖ ≤ m⁻¹ := by rw [norm_inv]; exact inv_anti₀ hm ha
  have hy : ‖b⁻¹‖ ≤ m⁻¹ := by rw [norm_inv]; exact inv_anti₀ hm hb
  have hxy : ‖a⁻¹ - b⁻¹‖ ≤ ‖a - b‖ / m ^ 2 := by
    rw [inv_sub_inv ha0 hb0, norm_div, norm_mul, norm_sub_rev]
    have hab : m * m ≤ ‖a‖ * ‖b‖ := mul_le_mul ha hb hm.le (norm_nonneg _)
    rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hab) (by positivity)]
    nlinarith [norm_nonneg (a - b), mul_le_mul_of_nonneg_left hab (norm_nonneg (a - b))]
  have hfac : (a ^ 4)⁻¹ - (b ^ 4)⁻¹ =
      (a⁻¹ - b⁻¹) * (a⁻¹ ^ 3 + a⁻¹ ^ 2 * b⁻¹ + a⁻¹ * b⁻¹ ^ 2 + b⁻¹ ^ 3) := by
    rw [inv_pow, inv_pow]; ring
  have hs : ‖a⁻¹ ^ 3 + a⁻¹ ^ 2 * b⁻¹ + a⁻¹ * b⁻¹ ^ 2 + b⁻¹ ^ 3‖ ≤ 4 * (m⁻¹) ^ 3 := by
    have h1 : ‖a⁻¹ ^ 3‖ ≤ (m⁻¹) ^ 3 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hx 3
    have h2 : ‖a⁻¹ ^ 2 * b⁻¹‖ ≤ (m⁻¹) ^ 3 := by
      rw [norm_mul, norm_pow]
      calc ‖a⁻¹‖ ^ 2 * ‖b⁻¹‖ ≤ (m⁻¹) ^ 2 * m⁻¹ :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx 2) hy (norm_nonneg _) (by positivity)
        _ = (m⁻¹) ^ 3 := by ring
    have h3 : ‖a⁻¹ * b⁻¹ ^ 2‖ ≤ (m⁻¹) ^ 3 := by
      rw [norm_mul, norm_pow]
      calc ‖a⁻¹‖ * ‖b⁻¹‖ ^ 2 ≤ m⁻¹ * (m⁻¹) ^ 2 :=
            mul_le_mul hx (pow_le_pow_left₀ (norm_nonneg _) hy 2) (by positivity) (by positivity)
        _ = (m⁻¹) ^ 3 := by ring
    have h4 : ‖b⁻¹ ^ 3‖ ≤ (m⁻¹) ^ 3 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hy 3
    calc _ ≤ ‖a⁻¹ ^ 3‖ + ‖a⁻¹ ^ 2 * b⁻¹‖ + ‖a⁻¹ * b⁻¹ ^ 2‖ + ‖b⁻¹ ^ 3‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ 4 * (m⁻¹) ^ 3 := by linarith
  rw [hfac, norm_mul]
  calc ‖a⁻¹ - b⁻¹‖ * ‖a⁻¹ ^ 3 + a⁻¹ ^ 2 * b⁻¹ + a⁻¹ * b⁻¹ ^ 2 + b⁻¹ ^ 3‖
      ≤ (‖a - b‖ / m ^ 2) * (4 * (m⁻¹) ^ 3) :=
        mul_le_mul hxy hs (norm_nonneg _) (by positivity)
    _ = 4 * ‖a - b‖ / m ^ 5 := by field_simp


/-- **Small-`τ` expansion** (`(ct:binet-small)`): for `c > 0` and all real `τ`,
`|B_c(iτ) - iτ/(12 c (1-iτ))| ≤ 8|τ|/c³`. -/
theorem binetDiff_small {c : ℝ} (hc : 0 < c) (τ : ℝ) :
    ‖binetDiff c (Complex.I * (τ : ℂ)) - Complex.I * (τ : ℂ) / (12 * (c : ℂ) * (1 - Complex.I * (τ : ℂ)))‖ ≤
      8 * |τ| / c ^ 3 := by
  set w1 : ℂ := (c : ℂ) * (1 - Complex.I * (τ : ℂ)) with hw1
  have hw1re : 0 < w1.re := by simpa [hw1] using hc
  have hw2re : 0 < (c : ℂ).re := by simpa using hc
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hw10 : w1 ≠ 0 := fun h => by simp [h] at hw1re
  have h1τ : (1 - Complex.I * (τ : ℂ)) ≠ 0 := fun h => by
    apply hw10; rw [hw1, h, mul_zero]
  have hid : binetDiff c (Complex.I * (τ : ℂ)) - Complex.I * (τ : ℂ) / (12 * (c : ℂ) * (1 - Complex.I * (τ : ℂ))) =
      (binetRem w1 - 1 / (12 * w1)) - (binetRem (c : ℂ) - 1 / (12 * (c : ℂ))) := by
    unfold binetDiff
    rw [← hw1]
    field_simp [hw1]
    ring
  rw [hid, binetRem_sub_eq hw1re, binetRem_sub_eq hw2re]
  have i1 := integrableOn_bdd_mul_inv_pow (P := binP4) (M := 1 / 24) continuous_binP4.measurable
    abs_binP4_le hw1re (by norm_num : 2 ≤ 4)
  have i2 := integrableOn_bdd_mul_inv_pow (P := binP4) (M := 1 / 24) continuous_binP4.measurable
    abs_binP4_le hw2re (by norm_num : 2 ≤ 4)
  rw [← mul_sub, ← integral_sub i1 i2, norm_mul]
  have hmaj := (integral_inv_pow_shift hc 3)
  have hg : Integrable (fun s : ℝ => (16 / 3 * (c * |τ|)) * ((s + c) ^ (3 + 2))⁻¹) (volume.restrict (Ioi (0 : ℝ))) :=
    hmaj.1.const_mul _
  have hbound : ‖∫ s in Ioi (0 : ℝ), ((binP4 s : ℂ) * (((s : ℂ) + w1) ^ 4)⁻¹ -
      (binP4 s : ℂ) * (((s : ℂ) + (c : ℂ)) ^ 4)⁻¹)‖ ≤ ∫ s in Ioi (0 : ℝ), (16 / 3 * (c * |τ|)) * ((s + c) ^ (3 + 2))⁻¹ := by
    refine norm_integral_le_of_norm_le hg ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have hs' : (0 : ℝ) ≤ s := le_of_lt hs
    have hm : 0 < (s + c) / 2 := by positivity
    have ha : (s + c) / 2 ≤ ‖(s : ℂ) + w1‖ := by
      have := half_le_norm_add hw1re.le hs'
      have hc1 : c ≤ ‖w1‖ := by
        have hre : w1.re = c := by simp [hw1]
        have := Complex.re_le_norm w1
        linarith
      linarith
    have hb : (s + c) / 2 ≤ ‖(s : ℂ) + (c : ℂ)‖ := by
      have : ‖(s : ℂ) + (c : ℂ)‖ = s + c := by
        rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [this]; linarith
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hd := inv_pow4_sub_le hm ha hb
    have hab : ‖((s : ℂ) + w1) - ((s : ℂ) + (c : ℂ))‖ = c * |τ| := by
      rw [add_sub_add_left_eq_sub, hw1]
      have : (c : ℂ) * (1 - Complex.I * (τ : ℂ)) - (c : ℂ) = ((-(c * τ) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul,
        abs_of_pos hc]
    rw [hab] at hd
    calc |binP4 s| * ‖(((s : ℂ) + w1) ^ 4)⁻¹ - (((s : ℂ) + (c : ℂ)) ^ 4)⁻¹‖
        ≤ (1 / 24) * (4 * (c * |τ|) / ((s + c) / 2) ^ 5) :=
          mul_le_mul (abs_binP4_le s) hd (norm_nonneg _) (by norm_num)
      _ = (16 / 3 * (c * |τ|)) * ((s + c) ^ (3 + 2))⁻¹ := by
          have : (s + c) ≠ 0 := by positivity
          rw [div_pow]
          field_simp
          ring
  rw [integral_const_mul, hmaj.2] at hbound
  have h6 : ‖(6 : ℂ)‖ = 6 := by simp
  rw [h6]
  calc 6 * _ ≤ 6 * ((16 / 3 * (c * |τ|)) * (1 / ((3 : ℕ) + 1 : ℝ) * (c ^ (3 + 1))⁻¹)) :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = 8 * |τ| / c ^ 3 := by
        have : c ≠ 0 := hc.ne'
        push_cast
        field_simp
        ring

/-- info: 'FormalResearch.SignUncertainty.BinetDecay.binetRem_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binetRem_sub_eq

/-- info: 'FormalResearch.SignUncertainty.BinetDecay.binetDiff_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binetDiff_small

end FormalResearch.SignUncertainty.BinetDecay
