module

public import FormalResearch.SignUncertainty.ConvSourceEdgeBoundary
public import FormalResearch.SignUncertainty.ConvSourceHasU2
public import FormalResearch.SignUncertainty.Gt1NegTail

/-!
# `GT.1` for the symbol of the convolution source (M6, `ceo:conv` (4), the main trace of `ceo:O11ak`)

`ceo:conv` (4): `W_{S_c}` satisfies the `GT.1` bounds `(cegt:eqGT1)`.  Proof of the paper (Leibniz): `W_{S_c}(iv) = W_{g_1}(iv) ŵ_c(c_s v)` (`ceo:conv` (3)), the
bounds of `W_{g_1}` (`GT.1` for the fixed seed `g_1`) and `(ceo:conv.5)` for `ŵ_c`.  Here:

* `convInterior_convWh`: the interior estimates `ConvInterior` of `w_h` (`1/2 < p < 1`, uniformly in `h > 0`), from `convS_moment_bounds`, `convS_lapW_norm_le`, `convS_lapW_sub_le`;
* `convInterior_exp`: those of the exponential term `γ ε e^{-y}`, from the explicit moment transforms `convSD_exp` (`(-1)^k k! γ ε (1+z)^{-k-1}`);
* `lapBounds_convWc`: `LapBounds` of `v ↦ ŵ_c(a v)`, `a ≥ 1`, with a constant independent of `h` (the boundary passage `lapBounds_of_interior`);
* `liftW_convSource_eq`: `W_{S_c}(iv) = W_{g_1}(iv) · ŵ_c(c_s v)` (`ceo:conv` (3));
* `gt1Bounds_convSource` (**`ceo:conv` (4)**, fixed `c`): `Gt1Bounds A (liftW (convSource p γ θ ε h) δ₀ m)` for `1/2 < p < 1`, `h > 0`, `m ≥ 3`, `δ₀ ∈ [0, 2]`, with `A` independent of `h`
  and `δ₀` (class: proved).  The constants depend on `γ ε` and `θ`; no uniformity in `c` is claimed beyond that of the paper's `|γ ε|, |θ| ≲ 1`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

lemma lapW_zero (w : ℝ → ℝ) : lapW w 0 = ((∫ y in Ioi (0 : ℝ), w y : ℝ) : ℂ) := by
  unfold lapW
  simp only [zero_mul, neg_zero, Complex.exp_zero, mul_one]
  exact integral_ofReal

/-! ### The weight `w_h` -/

/-- Interior estimates of `(ceo:conv.5)` for `w_h`, `1/2 < p < 1`, with a constant independent of `h > 0`. -/
theorem convInterior_convWh {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) :
    ∃ C : ℝ, ∀ h : ℝ, 0 < h → ConvInterior (convWh p h) C := by
  obtain ⟨C1, hC1, h1⟩ := convS_moment_bounds hp 1 le_rfl
  obtain ⟨C2, hC2, h2⟩ := convS_moment_bounds hp 2 (by norm_num)
  obtain ⟨C3, hC3, h3⟩ := convS_moment_bounds hp 3 (by norm_num)
  obtain ⟨C4, hC4, h4⟩ := convS_moment_bounds hp 4 (by norm_num)
  refine ⟨C1 + C2 + C3 + C4 + 6, fun h hh => ⟨convW_integrable hp hp1 hh, by positivity, ?_, ?_, ?_, ?_⟩⟩
  · intro k hk1 hk4 z hz
    have hp0 : 0 ≤ ‖z‖ ^ (-(k : ℝ) - 1) := Real.rpow_nonneg (norm_nonneg _) _
    interval_cases k
    · exact ((h1 h hh z hz).1).trans (by nlinarith)
    · exact ((h2 h hh z hz).1).trans (by nlinarith)
    · exact ((h3 h hh z hz).1).trans (by nlinarith)
    · exact ((h4 h hh z hz).1).trans (by nlinarith)
  · intro k hk1 hk3 z hz hz1
    have hp0 : 0 ≤ ‖z‖ ^ (1 / 2 - (k : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    interval_cases k
    · exact ((h1 h hh z hz).2 hz1).trans (by nlinarith)
    · exact ((h2 h hh z hz).2 hz1).trans (by nlinarith)
    · exact ((h3 h hh z hz).2 hz1).trans (by nlinarith)
  · intro z hz
    exact (convS_lapW_norm_le hp hp1 hh hz).trans (by linarith)
  · intro z hz hz1
    have hp0 : 0 ≤ ‖z‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    have := convS_lapW_sub_le hp hp1 hh hz hz1
    rw [lapW_zero]
    refine this.trans ?_
    nlinarith

/-! ### The exponential term `γ ε e^{-y}` -/

/-- The weight `γ ε e^{-y}`. -/
noncomputable def convWe (γ ε : ℝ) (y : ℝ) : ℝ := γ * ε * Real.exp (-y)

lemma convWe_integrableOn (γ ε : ℝ) : IntegrableOn (convWe γ ε) (Ioi 0) :=
  ((exp_neg_integrableOn_Ioi 0 one_pos).congr_fun (fun y _ => by simp) measurableSet_Ioi).const_mul (γ * ε)

lemma one_add_re_ne {z : ℂ} (hz : 0 ≤ z.re) : (1 + z) ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp at this
  linarith

/-- `ℒ(γ ε e^{-y})(z) = γ ε / (1 + z)` for `Re z ≥ 0`. -/
lemma lapW_convWe {γ ε : ℝ} {z : ℂ} (hz : 0 ≤ z.re) : lapW (convWe γ ε) z = ((γ * ε : ℝ) : ℂ) / (1 + z) := by
  have hne := one_add_re_ne hz
  have ha : (-(1 + z)).re < 0 := by simp; linarith
  have hint : ∀ y : ℝ, (((convWe γ ε y : ℝ)) : ℂ) * Complex.exp (-(z * (y : ℂ)))
      = ((γ * ε : ℝ) : ℂ) * Complex.exp (-(1 + z) * (y : ℂ)) := by
    intro y
    have e : Complex.exp (-(1 + z) * (y : ℂ)) = Complex.exp (-(y : ℂ)) * Complex.exp (-(z * (y : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; ring
    unfold convWe
    push_cast
    rw [e]
    ring
  unfold lapW
  calc ∫ y in Ioi (0 : ℝ), (((convWe γ ε y : ℝ)) : ℂ) * Complex.exp (-(z * (y : ℂ)))
      = ∫ y in Ioi (0 : ℝ), ((γ * ε : ℝ) : ℂ) * Complex.exp (-(1 + z) * (y : ℂ)) :=
        setIntegral_congr_fun measurableSet_Ioi (fun y _ => hint y)
    _ = ((γ * ε : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), Complex.exp (-(1 + z) * (y : ℂ)) :=
        integral_const_mul _ _
    _ = ((γ * ε : ℝ) : ℂ) / (1 + z) := by
        rw [integral_exp_mul_complex_Ioi ha 0]
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
        field_simp

/-- The explicit moment transforms of the exponential weight, `Re z > 0`. -/
lemma convSD_exp (γ ε : ℝ) (k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    convSD (convWe γ ε) k z = ((γ * ε : ℝ) : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) / (1 + z) ^ (k + 1) := by
  induction k generalizing z with
  | zero => simp [convSD_zero, lapW_convWe hz.le]
  | succ k ih =>
    have hne := one_add_re_ne hz.le
    have hderiv : HasDerivAt (convSD (convWe γ ε) k) (convSD (convWe γ ε) (k + 1) z) z :=
      convSD_hasDerivAt (convWe_integrableOn γ ε) k hz
    have hc := (hasDerivAt_pow (k + 1) (1 + z)).comp z ((hasDerivAt_id z).const_add (1 : ℂ))
    have hq := (hasDerivAt_const z (((γ * ε : ℝ) : ℂ) * ((-1) ^ k * (k.factorial : ℂ)))).div hc (pow_ne_zero _ hne)
    have hev : convSD (convWe γ ε) k =ᶠ[𝓝 z]
        fun z : ℂ => ((γ * ε : ℝ) : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) / (1 + z) ^ (k + 1) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with y hy
      exact ih hy
    have h2 := hderiv.unique (hq.congr_of_eventuallyEq hev)
    rw [h2]
    have hk : ((k + 1).factorial : ℂ) = ((k : ℂ) + 1) * (k.factorial : ℂ) := by
      push_cast [Nat.factorial_succ]; ring
    rw [hk]
    simp only [Function.comp_apply, Nat.add_sub_cancel, mul_one]
    push_cast
    field_simp
    ring

lemma convEdge_norm_one_add_ge {z : ℂ} (hz : 0 ≤ z.re) : 1 ≤ ‖1 + z‖ ∧ ‖z‖ ≤ ‖1 + z‖ := by
  have h1 : (1 : ℝ) ≤ (1 + z).re := by simpa using hz
  refine ⟨h1.trans (Complex.re_le_norm _), ?_⟩
  have h2 : ‖z‖ ^ 2 ≤ ‖1 + z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zero_add]
    nlinarith
  exact le_of_sq_le_sq h2 (norm_nonneg _)

/-- Interior estimates of the exponential weight. -/
theorem convInterior_exp (γ ε : ℝ) : ConvInterior (convWe γ ε) (24 * |γ * ε|) := by
  have hg : 0 ≤ |γ * ε| := abs_nonneg _
  refine ⟨convWe_integrableOn γ ε, by positivity, ?_, ?_, ?_, ?_⟩
  · intro k hk1 hk4 z hz
    obtain ⟨h1, h2⟩ := convEdge_norm_one_add_ge hz.le
    have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
    have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hne : ‖convSD (convWe γ ε) k z‖ = |γ * ε| * (k.factorial : ℝ) / ‖1 + z‖ ^ (k + 1) := by
      rw [convSD_exp γ ε k hz]
      simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_natCast, one_mul, abs_mul]
    rw [hne]
    have hfac : (k.factorial : ℝ) ≤ 24 := by
      have : k.factorial ≤ (4 : ℕ).factorial := Nat.factorial_le hk4
      exact_mod_cast this
    have hpow : ‖z‖ ^ (-(k : ℝ) - 1) = (‖z‖ ^ (k + 1))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hzn.le]; congr 1; push_cast; ring
    rw [hpow, div_eq_mul_inv]
    have hle : (‖z‖ ^ (k + 1))⁻¹ ≥ (‖1 + z‖ ^ (k + 1))⁻¹ :=
      inv_anti₀ (pow_pos hzn _) (pow_le_pow_left₀ hzn.le h2 _)
    calc |γ * ε| * (k.factorial : ℝ) * (‖1 + z‖ ^ (k + 1))⁻¹ ≤ |γ * ε| * 24 * (‖z‖ ^ (k + 1))⁻¹ := by
          gcongr
      _ = 24 * |γ * ε| * (‖z‖ ^ (k + 1))⁻¹ := by ring
  · intro k hk1 hk3 z hz hz1
    obtain ⟨h1, h2⟩ := convEdge_norm_one_add_ge hz.le
    have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
    have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hne : ‖convSD (convWe γ ε) k z‖ = |γ * ε| * (k.factorial : ℝ) / ‖1 + z‖ ^ (k + 1) := by
      rw [convSD_exp γ ε k hz]
      simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_natCast, one_mul, abs_mul]
    rw [hne]
    have hk1' : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk1
    have hfac : (k.factorial : ℝ) ≤ 24 := by
      have : k.factorial ≤ (4 : ℕ).factorial := Nat.factorial_le (by omega)
      exact_mod_cast this
    have hpz1 : 1 ≤ ‖z‖ ^ (1 / 2 - (k : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hzn hz1 (by linarith)
    have hinv : (‖1 + z‖ ^ (k + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1)
    calc |γ * ε| * (k.factorial : ℝ) * (‖1 + z‖ ^ (k + 1))⁻¹ ≤ |γ * ε| * 24 * 1 := by gcongr
      _ ≤ 24 * |γ * ε| * ‖z‖ ^ (1 / 2 - (k : ℝ)) := by nlinarith [mul_nonneg hg (by norm_num : (0 : ℝ) ≤ 24)]
  · intro z hz
    rw [lapW_convWe hz, norm_div, Complex.norm_real, Real.norm_eq_abs]
    obtain ⟨h1, _⟩ := convEdge_norm_one_add_ge hz
    calc |γ * ε| / ‖1 + z‖ ≤ |γ * ε| / 1 := by gcongr
      _ ≤ 24 * |γ * ε| := by linarith
  · intro z hz hz1
    rw [lapW_convWe hz.le, lapW_convWe (by simp : 0 ≤ (0 : ℂ).re)]
    obtain ⟨h1, h2⟩ := convEdge_norm_one_add_ge hz.le
    have hne := one_add_re_ne hz.le
    have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
    have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have e : ((γ * ε : ℝ) : ℂ) / (1 + z) - ((γ * ε : ℝ) : ℂ) / (1 + 0) = -(((γ * ε : ℝ) : ℂ) * z / (1 + z)) := by
      field_simp
      ring
    rw [e, norm_neg, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hsq : ‖z‖ ≤ ‖z‖ ^ (1 / 2 : ℝ) := by
      calc ‖z‖ = ‖z‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ‖z‖ ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hzn hz1 (by norm_num)
    calc |γ * ε| * ‖z‖ / ‖1 + z‖ ≤ |γ * ε| * ‖z‖ / 1 := by gcongr
      _ = |γ * ε| * ‖z‖ := by ring
      _ ≤ |γ * ε| * ‖z‖ ^ (1 / 2 : ℝ) := by gcongr
      _ ≤ 24 * |γ * ε| * ‖z‖ ^ (1 / 2 : ℝ) := by
          have := mul_nonneg hg (Real.rpow_nonneg (norm_nonneg z) (1 / 2 : ℝ))
          nlinarith

/-! ### The full weight `w_c = γ ε e^{-y} + θ w_h` and the symbol of the source -/

lemma lapW_convWc {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h) {z : ℂ} (hz : 0 ≤ z.re) :
    lapW (convWc p γ θ ε h) z = lapW (convWe γ ε) z + (θ : ℂ) * lapW (convWh p h) z := by
  have hE := integrableOn_lapW (convWe_integrableOn γ ε) hz
  have hH := integrableOn_lapW (convW_integrable hp hp1 hh) hz
  have hpt : ∀ y : ℝ, (((convWc p γ θ ε h y : ℝ)) : ℂ) * Complex.exp (-(z * (y : ℂ))) =
      (((convWe γ ε y : ℝ)) : ℂ) * Complex.exp (-(z * (y : ℂ))) +
        (θ : ℂ) * ((((convWh p h y : ℝ)) : ℂ) * Complex.exp (-(z * (y : ℂ)))) := by
    intro y; unfold convWc convWe; push_cast; ring
  unfold lapW
  rw [← integral_const_mul, ← integral_add hE (hH.const_mul _)]
  exact setIntegral_congr_fun measurableSet_Ioi (fun y _ => hpt y)

lemma convEdge_one_le_ceCs : 1 ≤ ceCs := by
  unfold ceCs
  refine Real.one_le_rpow ?_ (by norm_num)
  have := Real.pi_gt_three
  nlinarith

/-- **`(ceo:conv.5)` for the full weight on the real line**: `v ↦ ŵ_c(a v) = ℒ w_c (i a v)` satisfies `LapBounds B` for `a ≥ 1`, with `B` independent of `h > 0`
(it depends on `p`, `a` and `γ ε`, `θ`). -/
theorem lapBounds_convWc {p γ θ ε : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) {a : ℝ} (ha : 1 ≤ a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ h : ℝ, 0 < h →
      LapBounds B (fun v : ℝ => lapW (convWc p γ θ ε h) ((((a * v : ℝ)) : ℂ) * Complex.I)) := by
  obtain ⟨C, hC⟩ := convInterior_convWh hp hp1
  have hC0 : 0 ≤ C := (hC 1 one_pos).nonneg
  have ha3 : 0 ≤ a ^ 3 := by positivity
  refine ⟨2 * (24 * |γ * ε|) * a ^ 3 + |θ| * (2 * C * a ^ 3), by positivity, fun h hh => ?_⟩
  have hE := lapBounds_of_interior ha (convInterior_exp γ ε)
  have hW := (lapBounds_of_interior ha (hC h hh)).smul (θ : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs] at hW
  have hsum := hE.add hW
  have hfun : (fun v : ℝ => lapW (convWc p γ θ ε h) ((((a * v : ℝ)) : ℂ) * Complex.I)) =
      fun s => lapW (convWe γ ε) ((((a * s : ℝ)) : ℂ) * Complex.I) +
        (θ : ℂ) * lapW (convWh p h) ((((a * s : ℝ)) : ℂ) * Complex.I) := by
    funext v
    exact lapW_convWc hp hp1 hh (by simp)
  rw [hfun]
  exact hsum

/-- **`ceo:conv` (3)** on the imaginary axis: `W_{S_c}(iv) = W_{g_1}(iv) · ŵ_c(c_s v)`. -/
theorem liftW_convSource_eq {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h) (δ₀ : ℝ) (m : ℕ) (v : ℝ) :
    liftW (convSource p γ θ ε h) δ₀ m v = liftW (ceG1 (airyZero 1)) δ₀ m v *
      lapW (convWc p γ θ ε h) ((((ceCs * v : ℝ)) : ℂ) * Complex.I) := by
  unfold liftW liftSymbol
  have hz : 0 ≤ ((ceCs : ℂ) * ((v : ℂ) * Complex.I)).re := by simp [Complex.mul_re]
  rw [airyTwistedLaplaceC_convSource hp hp1 hh hz]
  have e : (((ceCs * v : ℝ)) : ℂ) * Complex.I = (ceCs : ℂ) * ((v : ℂ) * Complex.I) := by push_cast; ring
  rw [e]
  ring

lemma airySeedU2_zero_one_zero' : airySeedU2 0 1 0 = ceG1 (airyZero 1) := by
  funext u; simp [airySeedU2]

/-- **`ceo:conv` (4)** (the `GT.1` bounds for the symbol of the convolution source), at fixed parameters: for `1/2 < p < 1`, `m ≥ 3` there is `A` such that for every `h > 0` and
`δ₀ ∈ [0, 2]` the symbol `W_{S_c}(v) = M_ψ(iv) S̃_c(i c_s v)` of `S_c = convSource p γ θ ε h` satisfies `Gt1Bounds A`: three derivatives off `0`, `|W^{(j)}| ≲ |v|^{1/2-j}` for `|v| ≤ 1`,
`|W^{(j)}| ≲ |v|^{-5/2-j}` for `|v| ≥ 1`, `W` bounded and `1/2`-Hölder at `0`.  `A` is independent of `h` and `δ₀`.  Class: proved (Leibniz product of `gt1BasisInput` for `g_1` with
`lapBounds_convWc`); the paper's uniformity in `c` is not asserted. -/
theorem gt1Bounds_convSource {p γ θ ε : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 3 ≤ m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ h : ℝ, 0 < h → ∀ δ₀ : ℝ, δ₀ ∈ Icc (0 : ℝ) 2 →
      Gt1Bounds A (liftW (convSource p γ θ ε h) δ₀ m) := by
  obtain ⟨A1, hA1, hb⟩ := gt1BasisInput m hm
  obtain ⟨B, hB, hLB⟩ := lapBounds_convWc (p := p) (γ := γ) (θ := θ) (ε := ε) hp hp1 convEdge_one_le_ceCs
  refine ⟨9 * A1 * B, by positivity, fun h hh δ₀ hδ => ?_⟩
  have hU : Gt1Bounds A1 (liftW (ceG1 (airyZero 1)) δ₀ m) := by
    have := (hb δ₀ hδ).2.1
    rwa [airySeedU2_zero_one_zero'] at this
  have hmul := hU.mul_lap (hLB h hh)
  have hfun : liftW (convSource p γ θ ε h) δ₀ m = fun v => liftW (ceG1 (airyZero 1)) δ₀ m v *
      lapW (convWc p γ θ ε h) ((((ceCs * v : ℝ)) : ℂ) * Complex.I) := by
    funext v; exact liftW_convSource_eq hp hp1 hh δ₀ m v
  rw [hfun]
  exact hmul

/-- info: 'FormalResearch.SignUncertainty.convInterior_convWh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convInterior_convWh

/-- info: 'FormalResearch.SignUncertainty.convInterior_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convInterior_exp

/-- info: 'FormalResearch.SignUncertainty.lapBounds_convWc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lapBounds_convWc

/-- info: 'FormalResearch.SignUncertainty.liftW_convSource_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftW_convSource_eq

/-- info: 'FormalResearch.SignUncertainty.gt1Bounds_convSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gt1Bounds_convSource

end FormalResearch.SignUncertainty
