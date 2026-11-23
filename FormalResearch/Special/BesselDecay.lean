module

public import FormalResearch.Special.BesselSeries
public import FormalResearch.Special.BesselPoisson
public import FormalResearch.Special.BesselEnergy

/-!
# Decay of the normalised Bessel function

For `ν > -1/2`: `|besselNorm (ν+1) x| ≤ C x^{-(ν+3/2)}` for `x ≥ 1`, i.e. `J_{ν+1}(x) = O(x^{-1/2})`.
Proof: the pair `a = (x/2)^ν besselNorm ν x / Γ(ν+1)` (`= J_ν`), `b = (x/2)^{ν+1} besselNorm (ν+1) x / Γ(ν+2)`
(`= J_{ν+1}`) satisfies `a' = (ν/x) a - b`, `b' = a - ((ν+1)/x) b`
(`hasDerivAt_besselNorm`, `besselNorm_recurrence`), and `bessel_energy_bound` applies.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

lemma hasDerivAt_half_rpow (p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (x / 2) ^ p) (p / x * (x / 2) ^ p) x := by
  have h := (Real.hasDerivAt_rpow_const (x := x / 2) (p := p) (Or.inl (by positivity))).comp x
    ((hasDerivAt_id x).div_const 2)
  refine h.congr_deriv ?_
  rw [Real.rpow_sub_one (by positivity)]
  field_simp

/-- The pair `J_ν, J_{ν+1}` in terms of `besselNorm`. -/
noncomputable def besselJPairA (ν x : ℝ) : ℝ := (x / 2) ^ ν * besselNorm ν x / Real.Gamma (ν + 1)

/-- `J_{ν+1}`. -/
noncomputable def besselJPairB (ν x : ℝ) : ℝ :=
  (x / 2) ^ (ν + 1) * besselNorm (ν + 1) x / Real.Gamma (ν + 2)

theorem hasDerivAt_besselJPairA {ν : ℝ} (hν : -1 < ν) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (besselJPairA ν) (ν / x * besselJPairA ν x - besselJPairB ν x) x := by
  have h := ((hasDerivAt_half_rpow ν hx).mul (hasDerivAt_besselNorm hν x)).div_const
    (Real.Gamma (ν + 1))
  unfold besselJPairA besselJPairB
  refine h.congr_deriv ?_
  have hG : Real.Gamma (ν + 2) = (ν + 1) * Real.Gamma (ν + 1) := by
    rw [show ν + 2 = ν + 1 + 1 by ring]; exact Real.Gamma_add_one (by linarith)
  have hQ : (x / 2) ^ (ν + 1) = (x / 2) ^ ν * (x / 2) := by
    rw [Real.rpow_add_one (by positivity)]
  rw [hG, hQ]
  have h1 : (ν + 1) ≠ 0 := by linarith
  have h2 : Real.Gamma (ν + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have h3 : x ≠ 0 := hx.ne'
  field_simp
  ring

theorem hasDerivAt_besselJPairB {ν : ℝ} (hν : -1 < ν) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (besselJPairB ν) (besselJPairA ν x - (ν + 1) / x * besselJPairB ν x) x := by
  have h := ((hasDerivAt_half_rpow (ν + 1) hx).mul
    (hasDerivAt_besselNorm (by linarith : -1 < ν + 1) x)).div_const (Real.Gamma (ν + 2))
  unfold besselJPairA besselJPairB
  refine h.congr_deriv ?_
  have hG : Real.Gamma (ν + 2) = (ν + 1) * Real.Gamma (ν + 1) := by
    rw [show ν + 2 = ν + 1 + 1 by ring]; exact Real.Gamma_add_one (by linarith)
  have hQ : (x / 2) ^ (ν + 1) = (x / 2) ^ ν * (x / 2) := by
    rw [Real.rpow_add_one (by positivity)]
  have hrec := besselNorm_recurrence hν x
  rw [show ν + 1 + 1 = ν + 2 by ring]
  rw [hG, hQ]
  have h1 : (ν + 1) ≠ 0 := by linarith
  have h1' : (ν + 2) ≠ 0 := by linarith
  have h2 : Real.Gamma (ν + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have h3 : x ≠ 0 := hx.ne'
  have hy2 : besselNorm (ν + 2) x =
      4 * (ν + 1) * (ν + 2) / x ^ 2 * (besselNorm (ν + 1) x - besselNorm ν x) := by
    have e : besselNorm (ν + 1) x - besselNorm ν x =
        x ^ 2 / (4 * (ν + 1) * (ν + 2)) * besselNorm (ν + 2) x := by linarith
    rw [e]
    field_simp
  rw [hy2]
  generalize (x / 2) ^ ν = P
  generalize besselNorm ν x = y0
  generalize besselNorm (ν + 1) x = y1
  generalize Real.Gamma (ν + 1) = G at *
  field_simp
  ring

/-- **Decay**: for `ν > -1/2` there is `C` with `|besselNorm (ν+1) x| x^{ν+3/2} ≤ C` for `x ≥ 1`. -/
theorem besselNorm_decay {ν : ℝ} (hν : -1 / 2 < ν) :
    ∃ C : ℝ, ∀ x ≥ (1 : ℝ), |besselNorm (ν + 1) x| * x ^ (ν + 3 / 2) ≤ C := by
  obtain ⟨K, hK⟩ := bessel_energy_bound (ν := ν) hν.le (a := besselJPairA ν) (b := besselJPairB ν)
    (x₀ := 1) one_pos (fun x hx => hasDerivAt_besselJPairA (by linarith) (by linarith))
    (fun x hx => hasDerivAt_besselJPairB (by linarith) (by linarith))
  set x₁ : ℝ := max 1 (2 * ν + 1) with hx₁
  have hx₁1 : 1 ≤ x₁ := le_max_left _ _
  have hG : 0 < Real.Gamma (ν + 2) := Real.Gamma_pos_of_pos (by linarith)
  -- the bound on `[x₁, ∞)`
  have hbig : ∀ x ≥ x₁, (|besselNorm (ν + 1) x| * x ^ (ν + 3 / 2)) ^ 2 ≤
      4 ^ (ν + 1) * Real.Gamma (ν + 2) ^ 2 * K := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have h1 := hK x hx
    have hb2 : besselJPairB ν x ^ 2 * x ≤ K := by
      have : 0 ≤ besselJPairA ν x ^ 2 := sq_nonneg _
      nlinarith
    have e1 : (|besselNorm (ν + 1) x| * x ^ (ν + 3 / 2)) ^ 2 =
        (besselNorm (ν + 1) x) ^ 2 * x ^ (2 * ν + 3) := by
      rw [mul_pow, sq_abs, ← Real.rpow_natCast (x ^ (ν + 3 / 2)) 2, ← Real.rpow_mul hx0.le]
      congr 2
      push_cast; ring
    have e2 : besselJPairB ν x ^ 2 = (x / 2) ^ (2 * ν + 2) * besselNorm (ν + 1) x ^ 2 /
        Real.Gamma (ν + 2) ^ 2 := by
      unfold besselJPairB
      rw [div_pow, mul_pow, ← Real.rpow_natCast ((x / 2) ^ (ν + 1)) 2,
        ← Real.rpow_mul (by positivity)]
      congr 3
      push_cast; ring
    have e3 : (x / 2) ^ (2 * ν + 2) = x ^ (2 * ν + 2) / 4 ^ (ν + 1) := by
      rw [Real.div_rpow hx0.le (by norm_num), show (2 : ℝ) ^ (2 * ν + 2) = 4 ^ (ν + 1) by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        congr 1; ring]
    have e4 : x ^ (2 * ν + 3) = x ^ (2 * ν + 2) * x := by
      rw [show 2 * ν + 3 = (2 * ν + 2) + 1 by ring, Real.rpow_add_one hx0.ne']
    have h4 : (0 : ℝ) < 4 ^ (ν + 1) := Real.rpow_pos_of_pos (by norm_num) _
    rw [e1, e4]
    rw [e2, e3] at hb2
    have : x ^ (2 * ν + 2) * besselNorm (ν + 1) x ^ 2 * x ≤ 4 ^ (ν + 1) * Real.Gamma (ν + 2) ^ 2 * K := by
      have hA : (x ^ (2 * ν + 2) * besselNorm (ν + 1) x ^ 2 * x) /
          (4 ^ (ν + 1) * Real.Gamma (ν + 2) ^ 2) ≤ K := by
        refine le_trans (le_of_eq ?_) hb2
        field_simp
      rw [div_le_iff₀ (by positivity)] at hA
      linarith
    nlinarith
  refine ⟨max (Real.sqrt (4 ^ (ν + 1) * Real.Gamma (ν + 2) ^ 2 * K)) (x₁ ^ (ν + 3 / 2)), fun x hx => ?_⟩
  rcases le_or_gt x₁ x with hxx | hxx
  · refine le_trans ?_ (le_max_left _ _)
    exact Real.le_sqrt_of_sq_le (hbig x hxx)
  · refine le_trans ?_ (le_max_right _ _)
    have hx0 : 0 < x := by linarith
    have hy := abs_besselNorm_le_one (by linarith : -1 / 2 < ν + 1) x
    calc |besselNorm (ν + 1) x| * x ^ (ν + 3 / 2) ≤ 1 * x ^ (ν + 3 / 2) :=
          mul_le_mul_of_nonneg_right hy (Real.rpow_nonneg hx0.le _)
      _ ≤ x₁ ^ (ν + 3 / 2) := by
          rw [one_mul]
          exact Real.rpow_le_rpow hx0.le hxx.le (by linarith)

/-- info: 'FormalResearch.Special.besselNorm_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselNorm_decay

end FormalResearch.Special
