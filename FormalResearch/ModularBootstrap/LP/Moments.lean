module

public import FormalResearch.ModularBootstrap.LP.Laguerre
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.Exponential

/-!
# Lemma LP-M (`ds:mom`): moment bounds from the odd equations

`CFT/modular_bootstrap/paper/dual_spectrum_limit.tex`, Lemma LP-M (line 33).  For `w > 0` and a
positive reference measure `μ₀` on `[0, ∞)` with `∫ e^{π t} dμ₀ < ∞`, and `M ≥ 0`, there is a constant
`C₁` depending only on `(w, μ₀, M)` such that every positive measure `μ` on `[0, ∞)` of mass `≤ M` with
finite moments up to order `K` and `∫ P_k dμ = ∫ P_k dμ₀` for odd `k ≤ K` has
`∫ t^k dμ ≤ (C₁ k)^k` for `1 ≤ k ≤ K - 1`; if this holds for all `K` then `∫ e^{ε t} dμ ≤ M + 1` with
`ε = 1/(2 e C₁)`.

The paper's proof localises the zeros of `P_k` by Gershgorin's theorem on the Jacobi matrix.  Here the
two consequences used (`P_k(t) ≥ (t/2)^k` for `t ≥ D k`, and `|P_k(t)| ≤ (t + a k)^k`) are proved
directly from the three-term recurrence in `LP.Laguerre` (`lagP_lower`, `abs_lagP_le`).  The proof of
the moment bound is also slightly simpler: the pointwise inequality
`(t/2)^k ≤ P_k(t) + 2((D + a)k)^k` is integrated against `μ`, and the even moments are controlled by
`t^k ≤ s^k + t^{k+1}/s` instead of Hölder's inequality.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology

namespace FormalResearch.ModularBootstrap.LP

/-- `a = (3 + w)/(4π)`: the constant of `abs_lagP_le`. -/
noncomputable def momA (w : ℝ) : ℝ := (3 + w) / (4 * π)

/-- `D = 2(1 + w)/π`: `P_k(t) ≥ (t/2)^k` for `t ≥ D k`. -/
noncomputable def momD (w : ℝ) : ℝ := 2 * (1 + w) / π

lemma momA_pos {w : ℝ} (hw : 0 < w) : 0 < momA w := by unfold momA; positivity

lemma momD_pos {w : ℝ} (hw : 0 < w) : 0 < momD w := by unfold momD; positivity

lemma abs_lagP_le_mom {w : ℝ} (hw : 0 < w) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |lagP w k t| ≤ (t + momA w * k) ^ k := by
  have := abs_lagP_le hw k ht
  have e : (3 + w) * (k : ℝ) / (4 * π) = momA w * k := by unfold momA; ring
  rwa [e] at this

/-- The pointwise inequality integrated against `μ`: `(t/2)^k ≤ P_k(t) + 2 ((D + a) k)^k`, `t ≥ 0`. -/
lemma half_pow_le_lagP_add {w : ℝ} (hw : 0 < w) {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    (t / 2) ^ k ≤ lagP w k t + 2 * ((momD w + momA w) * k) ^ k := by
  have hD := momD_pos hw
  have hA := momA_pos hw
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hB : 0 ≤ ((momD w + momA w) * k) ^ k := by positivity
  by_cases h : momD w * k ≤ t
  · have : 2 * ((k : ℝ) + w) / π ≤ t := by
      refine le_trans ?_ h
      unfold momD
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by nlinarith) Real.pi_pos.le
    have := lagP_lower hw k this
    linarith
  · push Not at h
    have h1 : |lagP w k t| ≤ ((momD w + momA w) * k) ^ k := by
      refine (abs_lagP_le_mom hw k ht).trans ?_
      gcongr
      nlinarith
    have h2 : (t / 2) ^ k ≤ ((momD w + momA w) * k) ^ k := by
      gcongr
      nlinarith
    have := neg_abs_le (lagP w k t)
    linarith [abs_nonneg (lagP w k t)]


/-- `m = max (1/π) a`. -/
noncomputable def momM (w : ℝ) : ℝ := max (1 / π) (momA w)

lemma momM_pos {w : ℝ} (_hw : 0 < w) : 0 < momM w :=
  lt_max_of_lt_left (by positivity)

lemma one_div_pi_le_momM (w : ℝ) : 1 / π ≤ momM w := le_max_left _ _

lemma momA_le_momM (w : ℝ) : momA w ≤ momM w := le_max_right _ _

/-- Domination by the exponential moment: `|P_k(t)| ≤ (2 m k)^k e^{πt}` for `t ≥ 0`. -/
lemma abs_lagP_le_exp {w : ℝ} (hw : 0 < w) {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    |lagP w k t| ≤ (2 * momM w * k) ^ k * Real.exp (π * t) := by
  have hm := momM_pos hw
  have hπ := Real.pi_pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := abs_lagP_le_mom hw k ht
  have h2 : (t + momA w * k) ^ k ≤ 2 ^ (k - 1) * (t ^ k + (momA w * k) ^ k) :=
    add_pow_le ht (by have := momA_pos hw; positivity) k
  -- `t^k ≤ (k/π)^k e^{πt}`
  have h3 : t ^ k ≤ (k / π) ^ k * Real.exp (π * t) := by
    have := Real.pow_div_factorial_le_exp (x := π * t) (by positivity) k
    have hf : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
    have hfpos : (0 : ℝ) < k.factorial := by positivity
    rw [div_le_iff₀ hfpos] at this
    calc t ^ k = (π * t) ^ k / π ^ k := by rw [mul_pow]; field_simp
      _ ≤ (Real.exp (π * t) * k.factorial) / π ^ k := by gcongr
      _ ≤ (Real.exp (π * t) * (k : ℝ) ^ k) / π ^ k := by gcongr
      _ = (k / π) ^ k * Real.exp (π * t) := by rw [div_pow]; ring
  have he : (1 : ℝ) ≤ Real.exp (π * t) := Real.one_le_exp (by positivity)
  have h4 : (k / π) ^ k ≤ (momM w * k) ^ k := by
    gcongr
    calc (k : ℝ) / π = 1 / π * k := by ring
      _ ≤ momM w * k := by gcongr; exact one_div_pi_le_momM w
  have h5 : (momA w * k) ^ k ≤ (momM w * k) ^ k := by
    exact pow_le_pow_left₀ (by have := momA_pos hw; positivity)
      (mul_le_mul_of_nonneg_right (momA_le_momM w) hk0.le) k
  have h2pos : (0 : ℝ) ≤ 2 ^ (k - 1) := by positivity
  have h6 : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  calc |lagP w k t| ≤ (t + momA w * k) ^ k := h1
    _ ≤ 2 ^ (k - 1) * (t ^ k + (momA w * k) ^ k) := h2
    _ ≤ 2 ^ (k - 1) * ((momM w * k) ^ k * Real.exp (π * t) + (momM w * k) ^ k * Real.exp (π * t)) := by
        gcongr
        · exact h3.trans (by gcongr)
        · calc (momA w * k) ^ k ≤ (momM w * k) ^ k := h5
            _ = (momM w * k) ^ k * 1 := (mul_one _).symm
            _ ≤ _ := by gcongr
    _ = (2 * momM w * k) ^ k * Real.exp (π * t) := by
        have e : (2 * momM w * k) ^ k = 2 ^ k * (momM w * k) ^ k := by rw [mul_assoc, mul_pow]
        rw [e, h6]; ring


/-- `C₂`, the bound of `∫ |P_k| dμ₀`. -/
noncomputable def momC2 (w : ℝ) (μ₀ : Measure ℝ) : ℝ :=
  2 * momM w * max 1 (∫ t, Real.exp (π * t) ∂μ₀)

/-- `C₃`, the odd-moment constant. -/
noncomputable def momC3 (w : ℝ) (μ₀ : Measure ℝ) (M : ℝ) : ℝ :=
  2 * max (2 * momC2 w μ₀) (2 * (momD w + momA w) * (2 * M + 1))

/-- The constant `C₁` of `ds:mom`. -/
noncomputable def momC1 (w : ℝ) (μ₀ : Measure ℝ) (M : ℝ) : ℝ :=
  2 * momC3 w μ₀ M * (M + 1)

section Mom

variable {w : ℝ} {μ₀ μ : Measure ℝ}

private lemma ae_nonneg_of_Iio (h : μ (Iio 0) = 0) : ∀ᵐ t ∂μ, 0 ≤ t := by
  rw [ae_iff]
  simpa using h

private lemma isFiniteMeasure_of_mass {M : ℝ} (h : μ univ ≤ ENNReal.ofReal M) : IsFiniteMeasure μ :=
  ⟨lt_of_le_of_lt h ENNReal.ofReal_lt_top⟩

private lemma integrable_lagP_of_moment (hw : 0 < w) {M : ℝ} (hμ : μ (Iio 0) = 0)
    (hmass : μ univ ≤ ENNReal.ofReal M) {k : ℕ} (hmom : Integrable (fun t : ℝ => t ^ k) μ) :
    Integrable (lagP w k) μ := by
  haveI := isFiniteMeasure_of_mass hmass
  have hint : Integrable (fun t : ℝ => 2 ^ (k - 1) * (t ^ k + (momA w * k) ^ k)) μ :=
    (hmom.add (integrable_const _)).const_mul _
  refine hint.mono' (continuous_lagP w k).aestronglyMeasurable ?_
  filter_upwards [ae_nonneg_of_Iio hμ] with t ht
  rw [Real.norm_eq_abs]
  exact (abs_lagP_le_mom hw k ht).trans
    (add_pow_le ht (by have := momA_pos hw; positivity) k)

private lemma integral_lagP_mu0_le (hw : 0 < w) (hμ₀ : μ₀ (Iio 0) = 0)
    (hint : Integrable (fun t => Real.exp (π * t)) μ₀) {k : ℕ} (hk : 1 ≤ k) :
    ∫ t, lagP w k t ∂μ₀ ≤ (momC2 w μ₀ * k) ^ k := by
  set E₀ : ℝ := ∫ t, Real.exp (π * t) ∂μ₀ with hE₀
  have hE0nn : 0 ≤ E₀ := integral_nonneg fun t => (Real.exp_pos _).le
  have hbound : ∫ t, |lagP w k t| ∂μ₀ ≤ (2 * momM w * k) ^ k * E₀ := by
    have h1 : ∫ t, |lagP w k t| ∂μ₀ ≤ ∫ t, (2 * momM w * k) ^ k * Real.exp (π * t) ∂μ₀ := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _)
        (hint.const_mul _) ?_
      filter_upwards [ae_nonneg_of_Iio hμ₀] with t ht
      exact abs_lagP_le_exp hw hk ht
    rwa [integral_const_mul] at h1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hE : E₀ ≤ max 1 E₀ ^ k := by
    calc E₀ ≤ max 1 E₀ := le_max_right _ _
      _ = max 1 E₀ ^ 1 := (pow_one _).symm
      _ ≤ max 1 E₀ ^ k := pow_le_pow_right₀ (le_max_left _ _) hk
  calc ∫ t, lagP w k t ∂μ₀ ≤ ∫ t, |lagP w k t| ∂μ₀ :=
        (le_abs_self _).trans (abs_integral_le_integral_abs)
    _ ≤ (2 * momM w * k) ^ k * E₀ := hbound
    _ ≤ (2 * momM w * k) ^ k * max 1 E₀ ^ k := by gcongr
    _ = (momC2 w μ₀ * k) ^ k := by
        unfold momC2
        rw [← hE₀, ← mul_pow]
        congr 1; ring

/-- The odd-moment bound `∫ t^k dμ ≤ (C₃ k)^k` for odd `k ≥ 1`. -/
private lemma odd_moment_bound (hw : 0 < w) (hμ₀ : μ₀ (Iio 0) = 0)
    (hint : Integrable (fun t => Real.exp (π * t)) μ₀) (hμ : μ (Iio 0) = 0) {M : ℝ} (hM : 0 ≤ M)
    (hmass : μ univ ≤ ENNReal.ofReal M) {k : ℕ} (hk : 1 ≤ k)
    (hmom : Integrable (fun t : ℝ => t ^ k) μ)
    (heq : ∫ t, lagP w k t ∂μ = ∫ t, lagP w k t ∂μ₀) :
    ∫ t, t ^ k ∂μ ≤ (momC3 w μ₀ M * k) ^ k := by
  haveI := isFiniteMeasure_of_mass hmass
  have hPint := integrable_lagP_of_moment hw hμ hmass hmom
  set B : ℝ := ((momD w + momA w) * k) ^ k with hB
  have hBnn : 0 ≤ B := by
    have := momD_pos hw; have := momA_pos hw; positivity
  have hmu : μ.real univ ≤ M := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
    rwa [ENNReal.toReal_ofReal hM] at this
  have hmu0 : 0 ≤ μ.real univ := measureReal_nonneg
  -- integrate the pointwise inequality
  have h1 : ∫ t, (1 / 2 : ℝ) ^ k * t ^ k ∂μ ≤ ∫ t, (lagP w k t + 2 * B) ∂μ := by
    refine integral_mono_ae (hmom.const_mul _) (hPint.add (integrable_const _)) ?_
    filter_upwards [ae_nonneg_of_Iio hμ] with t ht
    have := half_pow_le_lagP_add hw hk ht
    rw [div_pow, one_div, inv_pow, inv_mul_eq_div, ← div_pow]
    simpa [div_pow] using this
  rw [integral_const_mul, integral_add hPint (integrable_const _), integral_const, heq] at h1
  have h2 : ∫ t, lagP w k t ∂μ₀ ≤ (momC2 w μ₀ * k) ^ k := integral_lagP_mu0_le hw hμ₀ hint hk
  have h3 : (1 / 2 : ℝ) ^ k * ∫ t, t ^ k ∂μ ≤ (momC2 w μ₀ * k) ^ k + 2 * B * M := by
    have : μ.real univ • (2 * B) ≤ M * (2 * B) := by
      rw [smul_eq_mul]; exact mul_le_mul_of_nonneg_right hmu (by positivity)
    nlinarith
  have h4 : ∫ t, t ^ k ∂μ ≤ (2 * momC2 w μ₀ * k) ^ k + 2 * M * (2 * (momD w + momA w) * k) ^ k := by
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    have : ∫ t, t ^ k ∂μ = 2 ^ k * ((1 / 2 : ℝ) ^ k * ∫ t, t ^ k ∂μ) := by
      rw [← mul_assoc, ← mul_pow]; norm_num
    rw [this]
    calc 2 ^ k * ((1 / 2 : ℝ) ^ k * ∫ t, t ^ k ∂μ) ≤ 2 ^ k * ((momC2 w μ₀ * k) ^ k + 2 * B * M) := by
          gcongr
      _ = (2 * momC2 w μ₀ * k) ^ k + 2 * M * (2 * (momD w + momA w) * k) ^ k := by
          rw [hB, mul_add, mul_assoc 2 (momC2 w μ₀), ← mul_pow]
          have : (2 * (momD w + momA w) * (k : ℝ)) ^ k = 2 ^ k * ((momD w + momA w) * k) ^ k := by
            rw [mul_assoc, mul_pow]
          rw [this]; ring
  -- combine into `(C₃ k)^k`
  set c₁ : ℝ := 2 * momC2 w μ₀ with hc₁
  set c₂ : ℝ := 2 * (momD w + momA w) * (2 * M + 1) with hc₂
  have hc₁nn : 0 ≤ c₁ := by
    have : 0 ≤ momC2 w μ₀ := by
      unfold momC2
      have := momM_pos hw
      have : (0 : ℝ) ≤ max 1 (∫ t, Real.exp (π * t) ∂μ₀) := le_trans zero_le_one (le_max_left _ _)
      positivity
    positivity
  have hc₂nn : 0 ≤ c₂ := by
    have := momD_pos hw; have := momA_pos hw; positivity
  have hmx : 0 ≤ max c₁ c₂ := le_trans hc₁nn (le_max_left _ _)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hMk : 2 * M ≤ (2 * M + 1) ^ k := by
    calc 2 * M ≤ 2 * M + 1 := by linarith
      _ = (2 * M + 1) ^ 1 := (pow_one _).symm
      _ ≤ (2 * M + 1) ^ k := pow_le_pow_right₀ (by linarith) hk
  have hterm1 : (c₁ * k) ^ k ≤ (max c₁ c₂ * k) ^ k := by
    gcongr; exact le_max_left _ _
  have hterm2 : 2 * M * (2 * (momD w + momA w) * k) ^ k ≤ (max c₁ c₂ * k) ^ k := by
    calc 2 * M * (2 * (momD w + momA w) * k) ^ k
        ≤ (2 * M + 1) ^ k * (2 * (momD w + momA w) * k) ^ k := by
          gcongr
      _ = (c₂ * k) ^ k := by
          rw [hc₂, ← mul_pow]; congr 1; ring
      _ ≤ (max c₁ c₂ * k) ^ k := by gcongr; exact le_max_right _ _
  have h2le : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one _).symm
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  calc ∫ t, t ^ k ∂μ ≤ (c₁ * k) ^ k + 2 * M * (2 * (momD w + momA w) * k) ^ k := h4
    _ ≤ (max c₁ c₂ * k) ^ k + (max c₁ c₂ * k) ^ k := add_le_add hterm1 hterm2
    _ = 2 * (max c₁ c₂ * k) ^ k := by ring
    _ ≤ 2 ^ k * (max c₁ c₂ * k) ^ k := by gcongr
    _ = (momC3 w μ₀ M * k) ^ k := by
        unfold momC3
        rw [← hc₁, ← hc₂, ← mul_pow]; congr 1; ring

end Mom

end FormalResearch.ModularBootstrap.LP
