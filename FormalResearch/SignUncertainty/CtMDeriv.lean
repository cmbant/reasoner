module

public import FormalResearch.SignUncertainty.CtCfuGerm
public import FormalResearch.SignUncertainty.CtOuterPart3Plus

/-!
# Derivative bounds for the dispersion `m = hankelEdgeM`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4 (`|m^{(r)}(τ)| ≤ C_r τ^{-r}` for large `τ`,
bounded for small `τ`; used for the phase derivatives `Φ^{(k)} = -m^{(k-1)}`).  **Proved.**

For every `j`: `|(m')^{(j)}(τ)| ≤ C_j (1+τ)^{-(j+1)}` for all `τ > 0` (`mPrime_iter_bound`), i.e. `|m^{(k)}(τ)| ≤ C_k (1+τ)^{-k}`, `k ≥ 1`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped Real

namespace FormalResearch.SignUncertainty.CtMDeriv

open CtOuter

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Cauchy estimate: `|(π/sinh(π·))^{(j)}(x)| ≤ K_j e^{-πx}` for `x ≥ 2`. -/
theorem csch_deriv_bound (j : ℕ) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → |iteratedDeriv j (fun y : ℝ => π / Real.sinh (π * y)) x| ≤ K * Real.exp (-π * x) := by
  refine ⟨j.factorial * (4 * π * Real.exp (π / 2)) / (1 / 2) ^ j, fun x hx => ?_⟩
  have hU : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hne : ∀ z : ℂ, 0 < z.re → Complex.sinh (π * z) ≠ 0 := by
    intro z hz h0
    have := norm_sinh_ge ((π : ℂ) * z)
    have hre : ((π : ℂ) * z).re = π * z.re := by simp [Complex.mul_re]
    rw [hre, abs_of_nonneg (mul_nonneg Real.pi_pos.le hz.le), h0, norm_zero] at this
    have : 0 < Real.sinh (π * z.re) := Real.sinh_pos_iff.mpr (by positivity)
    linarith
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => (π : ℂ) / Complex.sinh (π * z)) {z : ℂ | 1 < z.re} := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (differentiableAt_const _).div (by fun_prop) (hne z (by have : 1 < z.re := hz; linarith))
  have hsub : closedBall (x : ℂ) (1 / 2) ⊆ {z : ℂ | 1 < z.re} := by
    intro z hz
    have hd : ‖z - x‖ ≤ 1 / 2 := by simpa [mem_closedBall, dist_eq_norm] using hz
    have := Complex.abs_re_le_norm (z - x)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    show 1 < z.re
    linarith [(abs_le.mp (this.trans hd)).1]
  have hM : ∀ z ∈ sphere (x : ℂ) (1 / 2), ‖(π : ℂ) / Complex.sinh (π * z)‖ ≤
      4 * π * Real.exp (π / 2) * Real.exp (-π * x) := by
    intro z hz
    have hd : ‖z - x‖ = 1 / 2 := by simpa [dist_eq_norm] using hz
    have := Complex.abs_re_le_norm (z - x)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    have hre : x - 1 / 2 ≤ z.re := by linarith [(abs_le.mp (this.trans hd.le)).1]
    have h := norm_sinh_ge ((π : ℂ) * z)
    have hre' : ((π : ℂ) * z).re = π * z.re := by simp [Complex.mul_re]
    have hzpos : 0 ≤ π * z.re := mul_nonneg Real.pi_pos.le (by linarith)
    rw [hre', abs_of_nonneg hzpos] at h
    have h1 : 1 ≤ π * z.re := by nlinarith only [Real.pi_gt_three, hre, hx]
    have h2 := exp_div_four_le_sinh h1
    have hpos : 0 < Real.exp (π * z.re) / 4 := by positivity
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hc : Real.exp (π * z.re) / 4 ≤ ‖Complex.sinh (π * z)‖ := h2.trans h
    rw [div_le_iff₀ (hpos.trans_le hc)]
    have e1 : Real.exp (-π * z.re) ≤ Real.exp (π / 2) * Real.exp (-π * x) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith only [Real.pi_pos, hre]
    have e2 : Real.exp (-π * z.re) * Real.exp (π * z.re) = 1 := by rw [← Real.exp_add]; simp
    calc π = π * (Real.exp (-π * z.re) * Real.exp (π * z.re)) := by rw [e2, mul_one]
      _ = 4 * π * Real.exp (-π * z.re) * (Real.exp (π * z.re) / 4) := by ring
      _ ≤ 4 * π * (Real.exp (π / 2) * Real.exp (-π * x)) * ‖Complex.sinh (π * z)‖ := by
          have : 0 ≤ 4 * π * Real.exp (-π * z.re) := by positivity
          calc 4 * π * Real.exp (-π * z.re) * (Real.exp (π * z.re) / 4) ≤ 4 * π * Real.exp (-π * z.re) * ‖Complex.sinh (π * z)‖ :=
                mul_le_mul_of_nonneg_left hc this
            _ ≤ 4 * π * (Real.exp (π / 2) * Real.exp (-π * x)) * ‖Complex.sinh (π * z)‖ := by
                apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                gcongr
      _ = _ := by ring
  have h := cauchy_real (f := fun y : ℝ => π / Real.sinh (π * y)) hU hdiff
    (fun t _ => by
      simp only [Complex.ofReal_div, Complex.ofReal_sinh, Complex.ofReal_mul])
    (by norm_num : (0 : ℝ) < 1 / 2) (by simpa using hsub) hM j
  refine h.trans (le_of_eq ?_)
  ring

/-- Iterated derivatives of a `C^∞` function on an open set are bounded on compact subsets. -/
lemma bdd_iter_on_compact {f : ℝ → ℝ} {U K : Set ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞' f U) (hK : IsCompact K)
    (hKU : K ⊆ U) (j : ℕ) : ∃ B : ℝ, ∀ x ∈ K, |iteratedDeriv j f x| ≤ B := by
  have hc : ContinuousOn (iteratedDeriv j f) U := by
    have := hf.continuousOn_iteratedDerivWithin (m := j) (by exact_mod_cast le_top) hU.uniqueDiffOn
    exact this.congr (fun x hx => (iteratedDerivWithin_of_isOpen hU hx).symm)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hc.mono hKU)
  exact ⟨B, fun x hx => by simpa [Real.norm_eq_abs] using hB x hx⟩

lemma contDiffOn_mPrime : ContDiffOn ℝ ∞' mPrime (Ioi 0) := by
  unfold mPrime
  have h1 : ContDiffOn ℝ ∞' (fun t : ℝ => 1 / t) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun t ht => (ne_of_gt ht))
  have h2 : ContDiffOn ℝ ∞' (fun t : ℝ => π / Real.sinh (π * t)) (Ioi 0) := by
    refine contDiffOn_const.div ?_ (fun t ht => ?_)
    · exact (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)).contDiffOn
    · have : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by have : 0 < t := ht; positivity)
      exact this.ne'
  exact h1.sub h2

/-- Near `0`: `m'(u) = u k(u²)`. -/
noncomputable def g0 (u : ℝ) : ℝ := u * CtCfu.kfun (u ^ 2)

lemma contDiffOn_g0 : ContDiffOn ℝ ∞' g0 (Ioo (-(1 / 4 : ℝ)) (1 / 4)) := by
  unfold g0
  have hmap : MapsTo (fun u : ℝ => u ^ 2) (Ioo (-(1 / 4 : ℝ)) (1 / 4)) (Ioo (-CtCfu.rr) CtCfu.rr) := by
    intro u hu
    have h1 : u ^ 2 < 1 / 16 := by nlinarith [hu.1, hu.2]
    have h2 : (1 / 16 : ℝ) < CtCfu.rr := by
      unfold CtCfu.rr
      rw [lt_div_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three, Real.pi_lt_d2]
    exact ⟨by nlinarith [CtCfu.rr_pos, sq_nonneg u], lt_trans h1 h2⟩
  exact contDiffOn_id.mul (CtCfu.contDiffOn_kfun.comp (contDiffOn_id.pow 2) hmap)

lemma mPrime_eq_g0 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) (1 / 4)) : mPrime u = g0 u := by
  have hr : u ^ 2 < CtCfu.rr := by
    have h1 : u ^ 2 < 1 / 16 := by nlinarith [hu.1, hu.2]
    have h2 : (1 / 16 : ℝ) < CtCfu.rr := by
      unfold CtCfu.rr
      rw [lt_div_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three, Real.pi_lt_d2]
    exact lt_trans h1 h2
  rw [mPrime_eq_hankelEdgeM' hu.1, CtCfu.hankelEdgeM'_eq hu.1 hr]; rfl

/-- **Derivative bounds for `m'`**: `|(m')^{(j)}(τ)| ≤ C_j (1+τ)^{-(j+1)}` for all `τ > 0`. -/
theorem mPrime_iter_bound (j : ℕ) : ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → |iteratedDeriv j mPrime τ| ≤ C / (1 + τ) ^ (j + 1) := by
  obtain ⟨B1, hB1⟩ := bdd_iter_on_compact (isOpen_Ioo (a := -(1 / 4 : ℝ)) (b := 1 / 4)) contDiffOn_g0
    (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 5)) (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) j
  obtain ⟨B2, hB2⟩ := bdd_iter_on_compact (isOpen_Ioi (a := (0 : ℝ))) contDiffOn_mPrime
    (isCompact_Icc (a := (1 / 5 : ℝ)) (b := 2)) (fun x hx => by simp only [mem_Ioi]; linarith [hx.1]) j
  obtain ⟨K, hK⟩ := csch_deriv_bound j
  obtain ⟨P, hP⟩ := poly_exp_bdd (j + 1)
  refine ⟨|B1| * (6 / 5) ^ (j + 1) + |B2| * 3 ^ (j + 1) + (j.factorial * (3 / 2) ^ (j + 1) + |K| * P), fun τ hτ => ?_⟩
  have hpos : 0 < (1 + τ) ^ (j + 1) := by positivity
  rw [le_div_iff₀ hpos]
  have h1 : 0 ≤ |B1| * (6 / 5) ^ (j + 1) := by positivity
  have h2 : 0 ≤ |B2| * 3 ^ (j + 1) := by positivity
  have h3 : 0 ≤ (j.factorial : ℝ) * (3 / 2) ^ (j + 1) + |K| * P := by
    have hP0 : 0 ≤ P := by
      have := hP 0 le_rfl
      simp at this
      exact le_trans (by positivity) this
    positivity
  rcases le_or_gt τ (1 / 5) with hs | hs
  · -- small `τ`
    have hev : mPrime =ᶠ[𝓝 τ] g0 := by
      filter_upwards [isOpen_Ioo.mem_nhds (show τ ∈ Ioo (0 : ℝ) (1 / 4) from ⟨hτ, by linarith⟩)] with u hu using mPrime_eq_g0 hu
    rw [hev.iteratedDeriv_eq j]
    have := hB1 τ ⟨hτ.le, hs⟩
    have hle : (1 + τ) ^ (j + 1) ≤ (6 / 5) ^ (j + 1) := pow_le_pow_left₀ (by linarith) (by linarith) _
    calc |iteratedDeriv j g0 τ| * (1 + τ) ^ (j + 1) ≤ |B1| * (6 / 5) ^ (j + 1) :=
          mul_le_mul (this.trans (le_abs_self _)) hle hpos.le (abs_nonneg _)
      _ ≤ _ := by linarith
  rcases le_or_gt τ 2 with hm | hl
  · have := hB2 τ ⟨hs.le, hm⟩
    have hle : (1 + τ) ^ (j + 1) ≤ 3 ^ (j + 1) := pow_le_pow_left₀ (by linarith) (by linarith) _
    calc |iteratedDeriv j mPrime τ| * (1 + τ) ^ (j + 1) ≤ |B2| * 3 ^ (j + 1) :=
          mul_le_mul (this.trans (le_abs_self _)) hle hpos.le (abs_nonneg _)
      _ ≤ _ := by linarith
  · -- large `τ`
    have hmp : mPrime = fun t : ℝ => (fun y : ℝ => 1 / y) t - (fun y : ℝ => π / Real.sinh (π * y)) t := by
      funext t; rfl
    have hc1 : ContDiffAt ℝ ∞' (fun y : ℝ => 1 / y) τ :=
      (contDiffOn_const.div contDiffOn_id (fun t ht => (ne_of_gt ht)) : ContDiffOn ℝ ∞' (fun y : ℝ => 1 / y) (Ioi 0)).contDiffAt
        (isOpen_Ioi.mem_nhds hτ)
    have hc2 : ContDiffAt ℝ ∞' (fun y : ℝ => π / Real.sinh (π * y)) τ := by
      have : ContDiffOn ℝ ∞' (fun t : ℝ => π / Real.sinh (π * t)) (Ioi 0) := by
        refine contDiffOn_const.div ?_ (fun t ht => ?_)
        · exact (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)).contDiffOn
        · have : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by have : 0 < t := ht; positivity)
          exact this.ne'
      exact this.contDiffAt (isOpen_Ioi.mem_nhds hτ)
    have hsub := iteratedDeriv_sub (n := j) (hc1.of_le (by exact_mod_cast le_top)) (hc2.of_le (by exact_mod_cast le_top))
    rw [hmp]
    simp only [Pi.sub_apply] at hsub ⊢
    rw [show (fun t : ℝ => 1 / t - π / Real.sinh (π * t)) = (fun y : ℝ => 1 / y) - (fun y : ℝ => π / Real.sinh (π * y)) from rfl,
      hsub]
    have hone : iteratedDeriv j (fun y : ℝ => 1 / y) τ = (-1) ^ j * (j.factorial : ℝ) * τ ^ (-1 - j : ℤ) := by
      have := iteratedDerivWithin_one_div (𝕜 := ℝ) j (isOpen_Ioi (a := (0 : ℝ))) (mem_Ioi.mpr hτ)
      rw [iteratedDerivWithin_of_isOpen isOpen_Ioi (mem_Ioi.mpr hτ)] at this
      exact this
    have hK' := hK τ hl.le
    have hP' := hP τ hτ.le
    have e1 : |iteratedDeriv j (fun y : ℝ => 1 / y) τ| ≤ (j.factorial : ℝ) * (3 / 2) ^ (j + 1) / (1 + τ) ^ (j + 1) := by
      rw [hone, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
      have : |τ ^ (-1 - j : ℤ)| = (τ ^ (j + 1))⁻¹ := by
        rw [abs_of_pos (by positivity), show (-1 - j : ℤ) = -((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
      rw [this]
      have hτ1 : (1 + τ) ≤ 3 / 2 * τ := by linarith
      have hpw : (1 + τ) ^ (j + 1) ≤ (3 / 2) ^ (j + 1) * τ ^ (j + 1) := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hτ1 _
      calc (j.factorial : ℝ) * (τ ^ (j + 1))⁻¹ ≤ (j.factorial : ℝ) * ((3 / 2) ^ (j + 1) / (1 + τ) ^ (j + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
            linarith
        _ = _ := by ring
    have e2 : |iteratedDeriv j (fun y : ℝ => π / Real.sinh (π * y)) τ| * (1 + τ) ^ (j + 1) ≤ |K| * P := by
      calc _ ≤ (K * Real.exp (-π * τ)) * (1 + τ) ^ (j + 1) := mul_le_mul_of_nonneg_right hK' hpos.le
        _ = K * ((1 + τ) ^ (j + 1) * Real.exp (-π * τ)) := by ring
        _ ≤ |K| * P := by
            calc _ ≤ |K| * ((1 + τ) ^ (j + 1) * Real.exp (-π * τ)) :=
                  mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
              _ ≤ |K| * P := mul_le_mul_of_nonneg_left hP' (abs_nonneg K)
    have e1' : |iteratedDeriv j (fun y : ℝ => 1 / y) τ| * (1 + τ) ^ (j + 1) ≤ (j.factorial : ℝ) * (3 / 2) ^ (j + 1) := by
      calc _ ≤ ((j.factorial : ℝ) * (3 / 2) ^ (j + 1) / (1 + τ) ^ (j + 1)) * (1 + τ) ^ (j + 1) :=
            mul_le_mul_of_nonneg_right e1 hpos.le
        _ = _ := by field_simp
    calc |iteratedDeriv j (fun y : ℝ => 1 / y) τ - iteratedDeriv j (fun y : ℝ => π / Real.sinh (π * y)) τ| * (1 + τ) ^ (j + 1)
        ≤ (|iteratedDeriv j (fun y : ℝ => 1 / y) τ| + |iteratedDeriv j (fun y : ℝ => π / Real.sinh (π * y)) τ|) * (1 + τ) ^ (j + 1) :=
          mul_le_mul_of_nonneg_right (abs_sub _ _) hpos.le
      _ = |iteratedDeriv j (fun y : ℝ => 1 / y) τ| * (1 + τ) ^ (j + 1) +
          |iteratedDeriv j (fun y : ℝ => π / Real.sinh (π * y)) τ| * (1 + τ) ^ (j + 1) := by ring
      _ ≤ _ := by linarith

lemma deriv_hankelEdgeM_eventually {τ : ℝ} (hτ : 0 < τ) : deriv hankelEdgeM =ᶠ[𝓝 τ] mPrime := by
  filter_upwards [isOpen_Ioi.mem_nhds (mem_Ioi.mpr hτ)] with u hu
  rw [(hankelEdgeM_hasDerivAt hu).deriv, mPrime_eq_hankelEdgeM' hu]

lemma contDiffOn_hankelEdgeM : ContDiffOn ℝ ∞' hankelEdgeM (Ioi 0) := by
  have hd : DifferentiableOn ℝ hankelEdgeM (Ioi 0) := fun u hu => (hankelEdgeM_hasDerivAt hu).differentiableAt.differentiableWithinAt
  have hder : ContDiffOn ℝ ∞' (deriv hankelEdgeM) (Ioi 0) :=
    contDiffOn_mPrime.congr (fun u hu => by rw [(hankelEdgeM_hasDerivAt hu).deriv, mPrime_eq_hankelEdgeM' hu])
  exact (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr ⟨hd, hder⟩

/-- **`ct:cfu` Step 4, phase derivative bounds**: `|m^{(k)}(τ)| ≤ C_k (1+τ)^{-k}` for `k ≥ 1`, `τ > 0`. -/
theorem m_iter_bound (k : ℕ) (hk : 1 ≤ k) : ∃ C : ℝ, ∀ τ : ℝ, 0 < τ →
    |iteratedDeriv k hankelEdgeM τ| ≤ C / (1 + τ) ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨C, hC⟩ := mPrime_iter_bound j
  refine ⟨C, fun τ hτ => ?_⟩
  rw [iteratedDeriv_succ', (deriv_hankelEdgeM_eventually hτ).iteratedDeriv_eq j]
  exact hC τ hτ

/-- `HasDerivAt` chain for `m^{(k)}` on `(0, ∞)`. -/
lemma hasDerivAt_m_iter (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (iteratedDeriv k hankelEdgeM) (iteratedDeriv (k + 1) hankelEdgeM τ) τ := by
  have hd : DifferentiableAt ℝ (iteratedDeriv k hankelEdgeM) τ := by
    have : DifferentiableOn ℝ (iteratedDerivWithin k hankelEdgeM (Ioi 0)) (Ioi 0) :=
      contDiffOn_hankelEdgeM.differentiableOn_iteratedDerivWithin (m := k) (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top k))
        isOpen_Ioi.uniqueDiffOn
    have h2 := (this τ (mem_Ioi.mpr hτ)).differentiableAt (isOpen_Ioi.mem_nhds hτ)
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hτ] with u hu
    exact (iteratedDerivWithin_of_isOpen isOpen_Ioi hu).symm
  have := hd.hasDerivAt
  rwa [← iteratedDeriv_succ] at this

/-- info: 'FormalResearch.SignUncertainty.CtMDeriv.m_iter_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms m_iter_bound

/-- info: 'FormalResearch.SignUncertainty.CtMDeriv.hasDerivAt_m_iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_m_iter

end FormalResearch.SignUncertainty.CtMDeriv
