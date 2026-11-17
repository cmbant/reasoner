module

public import FormalResearch.Special.HermiteNorm
public import FormalResearch.Special.HermiteKappaWeber

/-!
# Hermite functions: the Weber equation and the energy identity

For the orthonormal Hermite functions `φ_n = hermitePhi n` (`HermiteFunction`, `HermiteNorm`), with `λ = 2n + 1`:

* `hkDer n` is the derivative of `φ_n` in the symmetric ladder form `√(n/2) φ_{n-1} - √((n+1)/2) φ_{n+1}`
  (`hasDerivAt_hermitePhi'`);
* **Weber equation** `φ_n'' = (x² - (2n+1)) φ_n` (`hasDerivAt_hkDer`), derived from the ladder relations and the exact recurrence
  (`hermitePsi_rec`) only;
* decay at `+∞`: `φ_n(x) → 0` and `φ_n'(x) → 0` (`tendsto_hermitePhi_atTop`, `tendsto_hkDer_atTop`);
* **energy identity** `E = φ'² + (λ - x²) φ²` has `E' = -2x φ²` (`hasDerivAt_hkE`), so `E` is nonincreasing on `[0, ∞)`
  and, since `E → 0`, `E ≥ 0` there (`hkE_nonneg`).

These are the inputs of the Sonin-type envelope bound `HermiteKappaEnvelope` (W1 `lem:PR(b)`).

**Claim class: proved.**  Not formalised: orthogonality, completeness, the second solution of the Weber equation.
-/

@[expose] public section

open Real Filter Topology MeasureTheory

namespace FormalResearch.Special

/-- The derivative of `φ_n` in ladder form: `√(n/2) φ_{n-1} - √((n+1)/2) φ_{n+1}` (`φ_{-1} = 0`). -/
noncomputable def hkDer (n : ℕ) (x : ℝ) : ℝ :=
  √((n : ℝ) / 2) * hermitePsi ((n : ℤ) - 1) x - √(((n : ℝ) + 1) / 2) * hermitePsi ((n : ℤ) + 1) x

lemma hasDerivAt_hermitePhi' (n : ℕ) (x : ℝ) : HasDerivAt (hermitePhi n) (hkDer n x) x := by
  have h := hasDerivAt_hermitePsi (n : ℤ) (Int.natCast_nonneg n) x
  have hm : hermitePsi (n : ℤ) = hermitePhi n := funext (hermitePsi_natCast n)
  rw [hm] at h
  simpa [hkDer] using h

/-- The ladder relation for all integer indices (for `m < 0` both sides vanish). -/
lemma hasDerivAt_hermitePsi_all (m : ℤ) (x : ℝ) :
    HasDerivAt (hermitePsi m)
      (√((m : ℝ) / 2) * hermitePsi (m - 1) x - √(((m : ℝ) + 1) / 2) * hermitePsi (m + 1) x) x := by
  by_cases hm : 0 ≤ m
  · exact hasDerivAt_hermitePsi m hm x
  · have hz : hermitePsi m = fun _ => 0 := funext fun y => hermitePsi_neg (not_le.1 hm) y
    rw [hz]
    have hm1 : m - 1 < 0 := by omega
    rw [hermitePsi_neg hm1]
    have hmr : (m : ℝ) < 0 := by exact_mod_cast not_le.1 hm
    have : √((m : ℝ) / 2) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    rw [this, zero_mul, zero_sub]
    by_cases h2 : m + 1 < 0
    · rw [hermitePsi_neg h2, mul_zero, neg_zero]; exact hasDerivAt_const x 0
    · have : m = -1 := by omega
      subst this
      norm_num
      exact hasDerivAt_const x 0

/-- The exact recurrence for all integer indices. -/
lemma hermitePsi_rec_all (m : ℤ) (x : ℝ) :
    √(((m : ℝ) + 1) / 2) * hermitePsi (m + 1) x + √((m : ℝ) / 2) * hermitePsi (m - 1) x =
      x * hermitePsi m x := by
  by_cases hm : 0 ≤ m
  · exact hermitePsi_rec m hm x
  · have hmr : (m : ℝ) < 0 := by exact_mod_cast not_le.1 hm
    rw [hermitePsi_neg (not_le.1 hm), hermitePsi_neg (show m - 1 < 0 by omega)]
    by_cases h2 : m + 1 < 0
    · rw [hermitePsi_neg h2]; ring
    · have : m = -1 := by omega
      subst this
      norm_num

/-- **Weber equation** `φ_n'' = (x² - (2n+1)) φ_n`, in the form `(hkDer n)' = (x² - (2n+1)) φ_n`. -/
theorem hasDerivAt_hkDer (n : ℕ) (x : ℝ) :
    HasDerivAt (hkDer n) ((x ^ 2 - (2 * (n : ℝ) + 1)) * hermitePhi n x) x := by
  have h1 := (hasDerivAt_hermitePsi_all ((n : ℤ) - 1) x).const_mul (√((n : ℝ) / 2))
  have h2 := (hasDerivAt_hermitePsi_all ((n : ℤ) + 1) x).const_mul (√(((n : ℝ) + 1) / 2))
  have h := h1.sub h2
  have hfun : hkDer n = fun y => √((n : ℝ) / 2) * hermitePsi ((n : ℤ) - 1) y -
      √(((n : ℝ) + 1) / 2) * hermitePsi ((n : ℤ) + 1) y := funext fun y => rfl
  rw [hfun]
  refine h.congr_deriv ?_
  have hm : hermitePsi (n : ℤ) x = hermitePhi n x := hermitePsi_natCast n x
  have r0 := hermitePsi_rec_all (n : ℤ) x
  have r1 := hermitePsi_rec_all ((n : ℤ) + 1) x
  have r2 := hermitePsi_rec_all ((n : ℤ) - 1) x
  have s0 : √((n : ℝ) / 2) ^ 2 = (n : ℝ) / 2 := Real.sq_sqrt (by positivity)
  have s1 : √(((n : ℝ) + 1) / 2) ^ 2 = ((n : ℝ) + 1) / 2 := Real.sq_sqrt (by positivity)
  push_cast at r0 r1 r2 ⊢
  simp only [add_sub_cancel_right, sub_add_cancel, hm] at r0 r1 r2 ⊢
  linear_combination (√(((n : ℝ) + 1) / 2)) * r1 + (√((n : ℝ) / 2)) * r2 + x * r0 +
    (-2 * hermitePhi n x) * s0 + (-2 * hermitePhi n x) * s1

lemma tendsto_hermitePhi_sq_atTop (n : ℕ) :
    Tendsto (fun x => hermitePhi n x ^ 2) atTop (𝓝 0) := by
  have := (pg_tendsto_atTop (hq n * hq n)).const_mul (hermiteK n * hermiteK n)
  simp only [mul_zero] at this
  refine this.congr (fun y => ?_)
  rw [← hermitePhi_mul, sq]

lemma tendsto_hermitePhi_atTop (n : ℕ) : Tendsto (hermitePhi n) atTop (𝓝 0) := by
  have h := ((Real.continuous_sqrt.tendsto 0).comp (tendsto_hermitePhi_sq_atTop n))
  simp only [Real.sqrt_zero] at h
  have h2 : Tendsto (fun x => |hermitePhi n x|) atTop (𝓝 0) :=
    h.congr (fun x => Real.sqrt_sq_eq_abs _)
  exact tendsto_zero_iff_abs_tendsto_zero _ |>.2 h2

lemma tendsto_hermitePsi_atTop (m : ℤ) : Tendsto (hermitePsi m) atTop (𝓝 0) := by
  by_cases hm : 0 ≤ m
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    have : hermitePsi (k : ℤ) = hermitePhi k := funext (hermitePsi_natCast k)
    rw [this]; exact tendsto_hermitePhi_atTop k
  · have : hermitePsi m = fun _ => 0 := funext fun y => hermitePsi_neg (not_le.1 hm) y
    rw [this]; exact tendsto_const_nhds

lemma tendsto_hkDer_atTop (n : ℕ) : Tendsto (hkDer n) atTop (𝓝 0) := by
  have h1 := (tendsto_hermitePsi_atTop ((n : ℤ) - 1)).const_mul (√((n : ℝ) / 2))
  have h2 := (tendsto_hermitePsi_atTop ((n : ℤ) + 1)).const_mul (√(((n : ℝ) + 1) / 2))
  have := h1.sub h2
  simp only [mul_zero, sub_zero] at this
  exact this

lemma tendsto_sq_mul_hermitePhi_sq (n : ℕ) :
    Tendsto (fun x => x ^ 2 * hermitePhi n x ^ 2) atTop (𝓝 0) := by
  have := (pg_tendsto_atTop (Polynomial.X ^ 2 * (hq n * hq n))).const_mul (hermiteK n * hermiteK n)
  simp only [mul_zero] at this
  refine this.congr (fun y => ?_)
  have := hermitePhi_mul n n y
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at this ⊢
  rw [sq (hermitePhi n y), this]; ring

lemma continuous_hermitePhi (n : ℕ) : Continuous (hermitePhi n) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_hermitePhi' n x).continuousAt

/-- **The Hermite function `φ_n` is `WeberData` with `L = 2n + 1`** (mass function `V(x) = ∫_0^x φ_n²`). -/
theorem hermite_weberData (n : ℕ) :
    WeberData (2 * (n : ℝ) + 1) (hermitePhi n) (hkDer n) (fun x => ∫ t in (0 : ℝ)..x, hermitePhi n t ^ 2) where
  hf := hasDerivAt_hermitePhi' n
  hg := hasDerivAt_hkDer n
  tf := tendsto_hermitePhi_atTop n
  tg := tendsto_hkDer_atTop n
  tE := tendsto_sq_mul_hermitePhi_sq n
  hV := fun x => ((continuous_hermitePhi n).pow 2).integral_hasStrictDerivAt 0 x |>.hasDerivAt
  V0 := by simp
  Vle := by
    intro x hx
    rw [intervalIntegral.integral_of_le hx]
    have hint : Integrable (fun t => hermitePhi n t ^ 2) := by
      simpa [sq] using integrable_hermitePhi_mul n n
    calc ∫ t in Set.Ioc 0 x, hermitePhi n t ^ 2 ≤ ∫ t, hermitePhi n t ^ 2 :=
          setIntegral_le_integral hint (Filter.Eventually.of_forall fun t => sq_nonneg _)
      _ = 1 := integral_hermitePhi_sq n

end FormalResearch.Special
