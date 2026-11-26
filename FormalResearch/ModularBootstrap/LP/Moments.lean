module

public import FormalResearch.ModularBootstrap.LP.Laguerre
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.Exponential

/-!
# Lemma LP-M (`ds:mom`): moment bounds from the odd equations

`CFT/modular_bootstrap/paper/dual_spectrum_limit.tex`, Lemma LP-M (line 33), for an abstract family.
Let `p_k` (`k` odd) be continuous with `|p_k(t)| ≤ (t + C k)^k` for `t ≥ 0` and `p_k(t) ≥ (t/2)^k` for
`t ≥ 2 C k` (`OddFam C p`).  For a positive reference measure `μ₀` on `[0, ∞)` with
`∫ e^{π t} dμ₀ < ∞` and `M ≥ 0` there is `C₁`, depending only on `(C, μ₀, M)`, such that every positive
measure `μ` on `[0, ∞)` of mass `≤ M` with finite moments up to order `K` and `∫ p_k dμ = ∫ p_k dμ₀` for
odd `k ≤ K` has `∫ t^k dμ ≤ (C₁ k)^k` for `1 ≤ k ≤ K - 1`; if this holds for all `K` then
`∫ e^{ε t} dμ ≤ M + 1` with `ε = 1/(2 e C₁)` (`ds_mom`).

The monic Laguerre family `P_k` at weight `w > 0` is such a family (`lagP_oddFam`, with `C = (1+w)/π`,
from the three-term recurrence of `LP.Laguerre` rather than Gershgorin's theorem; the hypotheses are
monotone in `C`), giving the Laguerre statement `ds_mom_laguerre` and the mass bound `ds_mom_mass`.

The pointwise inequality used is `(t/2)^k ≤ p_k(t) + 2(3Ck)^k` (`t ≥ 0`), integrated against `μ`; the
even moments are controlled by `t^k ≤ s^k + t^{k+1}/s` instead of Hölder's inequality.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology

namespace FormalResearch.ModularBootstrap.LP

/-- The hypotheses of `ds:mom` on a family `p_k` (`k` odd): continuity, `|p_k(t)| ≤ (t + Ck)^k` for
`t ≥ 0` and `p_k(t) ≥ (t/2)^k` for `t ≥ 2Ck`. -/
structure OddFam (C : ℝ) (p : ℕ → C(ℝ, ℝ)) : Prop where
  C_pos : 0 < C
  upper : ∀ k : ℕ, Odd k → ∀ t : ℝ, 0 ≤ t → |p k t| ≤ (t + C * k) ^ k
  lower : ∀ k : ℕ, Odd k → ∀ t : ℝ, 2 * C * k ≤ t → (t / 2) ^ k ≤ p k t

namespace OddFam

variable {C : ℝ} {p : ℕ → C(ℝ, ℝ)}

/-- The pointwise inequality integrated against `μ`: `(t/2)^k ≤ p_k(t) + 2 (3Ck)^k`, `t ≥ 0`. -/
lemma half_pow_le_add (hF : OddFam C p) {k : ℕ} (hk : Odd k) {t : ℝ} (ht : 0 ≤ t) :
    (t / 2) ^ k ≤ p k t + 2 * ((3 * C) * k) ^ k := by
  have hC := hF.C_pos
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.pos
  have hB : 0 ≤ ((3 * C) * k) ^ k := by positivity
  by_cases h : 2 * C * k ≤ t
  · have := hF.lower k hk t h
    linarith
  · push Not at h
    have h1 : |p k t| ≤ ((3 * C) * k) ^ k := by
      refine (hF.upper k hk t ht).trans ?_
      gcongr
      nlinarith
    have h2 : (t / 2) ^ k ≤ ((3 * C) * k) ^ k := by
      gcongr
      nlinarith
    have := neg_abs_le (p k t)
    linarith [abs_nonneg (p k t)]

end OddFam

/-- `m = max (1/π) a`. -/
noncomputable def momM (C : ℝ) : ℝ := max (1 / π) C

lemma momM_pos {C : ℝ} (_hC : 0 < C) : 0 < momM C :=
  lt_max_of_lt_left (by positivity)

lemma one_div_pi_le_momM (C : ℝ) : 1 / π ≤ momM C := le_max_left _ _

lemma le_momM (C : ℝ) : C ≤ momM C := le_max_right _ _

/-- Domination by the exponential moment: `|P_k(t)| ≤ (2 m k)^k e^{πt}` for `t ≥ 0`. -/
lemma OddFam.abs_le_exp {C : ℝ} {p : ℕ → C(ℝ, ℝ)} (hF : OddFam C p) {k : ℕ} (hk : Odd k) {t : ℝ} (ht : 0 ≤ t) :
    |p k t| ≤ (2 * momM C * k) ^ k * Real.exp (π * t) := by
  have hC := hF.C_pos
  have hm := momM_pos hC
  have hπ := Real.pi_pos
  have hk' : 1 ≤ k := hk.pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk'
  have h1 := hF.upper k hk t ht
  have h2 : (t + C * k) ^ k ≤ 2 ^ (k - 1) * (t ^ k + (C * k) ^ k) :=
    add_pow_le ht (by have := hF.C_pos; positivity) k
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
  have h4 : (k / π) ^ k ≤ (momM C * k) ^ k := by
    gcongr
    calc (k : ℝ) / π = 1 / π * k := by ring
      _ ≤ momM C * k := by gcongr; exact one_div_pi_le_momM C
  have h5 : (C * k) ^ k ≤ (momM C * k) ^ k := by
    exact pow_le_pow_left₀ (by have := hF.C_pos; positivity)
      (mul_le_mul_of_nonneg_right (le_momM C) hk0.le) k
  have h2pos : (0 : ℝ) ≤ 2 ^ (k - 1) := by positivity
  have h6 : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  calc |p k t| ≤ (t + C * k) ^ k := h1
    _ ≤ 2 ^ (k - 1) * (t ^ k + (C * k) ^ k) := h2
    _ ≤ 2 ^ (k - 1) * ((momM C * k) ^ k * Real.exp (π * t) + (momM C * k) ^ k * Real.exp (π * t)) := by
        gcongr
        · exact h3.trans (by gcongr)
        · calc (C * k) ^ k ≤ (momM C * k) ^ k := h5
            _ = (momM C * k) ^ k * 1 := (mul_one _).symm
            _ ≤ _ := by gcongr
    _ = (2 * momM C * k) ^ k * Real.exp (π * t) := by
        have e : (2 * momM C * k) ^ k = 2 ^ k * (momM C * k) ^ k := by rw [mul_assoc, mul_pow]
        rw [e, h6]; ring


/-- `C₂`, the bound of `∫ |P_k| dμ₀`. -/
noncomputable def momC2 (C : ℝ) (μ₀ : Measure ℝ) : ℝ :=
  2 * momM C * max 1 (∫ t, Real.exp (π * t) ∂μ₀)

/-- `C₃`, the odd-moment constant. -/
noncomputable def momC3 (C : ℝ) (μ₀ : Measure ℝ) (M : ℝ) : ℝ :=
  2 * max (2 * momC2 C μ₀) (2 * (3 * C) * (2 * M + 1))

/-- The constant `C₁` of `ds:mom`. -/
noncomputable def momC1 (C : ℝ) (μ₀ : Measure ℝ) (M : ℝ) : ℝ :=
  2 * momC3 C μ₀ M * (M + 1)

section Mom

variable {C : ℝ} {p : ℕ → C(ℝ, ℝ)} {μ₀ μ : Measure ℝ}

private lemma ae_nonneg_of_Iio (h : μ (Iio 0) = 0) : ∀ᵐ t ∂μ, 0 ≤ t := by
  have e : {t : ℝ | ¬ 0 ≤ t} = Iio 0 := by ext t; simp
  rw [ae_iff, e]
  exact h

private lemma isFiniteMeasure_of_mass {M : ℝ} (h : μ univ ≤ ENNReal.ofReal M) : IsFiniteMeasure μ :=
  ⟨lt_of_le_of_lt h ENNReal.ofReal_lt_top⟩

private lemma integrable_p_of_moment (hF : OddFam C p) {M : ℝ} (hμ : μ (Iio 0) = 0)
    (hmass : μ univ ≤ ENNReal.ofReal M) {k : ℕ} (hk : Odd k) (hmom : Integrable (fun t : ℝ => t ^ k) μ) :
    Integrable (p k) μ := by
  have := isFiniteMeasure_of_mass hmass
  have hint : Integrable (fun t : ℝ => 2 ^ (k - 1) * (t ^ k + (C * k) ^ k)) μ :=
    (hmom.add (integrable_const _)).const_mul _
  refine hint.mono' (p k).continuous.aestronglyMeasurable ?_
  filter_upwards [ae_nonneg_of_Iio hμ] with t ht
  rw [Real.norm_eq_abs]
  exact (hF.upper k hk t ht).trans
    (add_pow_le ht (by have := hF.C_pos; positivity) k)

private lemma integral_p_mu0_le (hF : OddFam C p) (hμ₀ : μ₀ (Iio 0) = 0)
    (hint : Integrable (fun t => Real.exp (π * t)) μ₀) {k : ℕ} (hk : Odd k) :
    ∫ t, p k t ∂μ₀ ≤ (momC2 C μ₀ * k) ^ k := by
  set E₀ : ℝ := ∫ t, Real.exp (π * t) ∂μ₀ with hE₀
  have hE0nn : 0 ≤ E₀ := integral_nonneg fun t => (Real.exp_pos _).le
  have hbound : ∫ t, |p k t| ∂μ₀ ≤ (2 * momM C * k) ^ k * E₀ := by
    have h1 : ∫ t, |p k t| ∂μ₀ ≤ ∫ t, (2 * momM C * k) ^ k * Real.exp (π * t) ∂μ₀ := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _)
        (hint.const_mul _) ?_
      filter_upwards [ae_nonneg_of_Iio hμ₀] with t ht
      exact hF.abs_le_exp hk ht
    rwa [integral_const_mul] at h1
  have hk1 : 1 ≤ k := hk.pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hE : E₀ ≤ max 1 E₀ ^ k := by
    calc E₀ ≤ max 1 E₀ := le_max_right _ _
      _ = max 1 E₀ ^ 1 := (pow_one _).symm
      _ ≤ max 1 E₀ ^ k := pow_le_pow_right₀ (le_max_left _ _) hk1
  calc ∫ t, p k t ∂μ₀ ≤ ∫ t, |p k t| ∂μ₀ :=
        (le_abs_self _).trans (abs_integral_le_integral_abs)
    _ ≤ (2 * momM C * k) ^ k * E₀ := hbound
    _ ≤ (2 * momM C * k) ^ k * max 1 E₀ ^ k :=
        mul_le_mul_of_nonneg_left hE (by have := momM_pos hF.C_pos; positivity)
    _ = (momC2 C μ₀ * k) ^ k := by
        unfold momC2
        rw [← hE₀, ← mul_pow]
        congr 1; ring

/-- The odd-moment bound `∫ t^k dμ ≤ (C₃ k)^k` for odd `k ≥ 1`. -/
private lemma odd_moment_bound (hF : OddFam C p) (hμ₀ : μ₀ (Iio 0) = 0)
    (hint : Integrable (fun t => Real.exp (π * t)) μ₀) (hμ : μ (Iio 0) = 0) {M : ℝ} (hM : 0 ≤ M)
    (hmass : μ univ ≤ ENNReal.ofReal M) {k : ℕ} (hk : Odd k)
    (hmom : Integrable (fun t : ℝ => t ^ k) μ)
    (heq : ∫ t, p k t ∂μ = ∫ t, p k t ∂μ₀) :
    ∫ t, t ^ k ∂μ ≤ (momC3 C μ₀ M * k) ^ k := by
  have hk1 : 1 ≤ k := hk.pos
  have := isFiniteMeasure_of_mass hmass
  have hPint := integrable_p_of_moment hF hμ hmass hk hmom
  set B : ℝ := ((3 * C) * k) ^ k with hB
  have hBnn : 0 ≤ B := by
    have := hF.C_pos; have := hF.C_pos; positivity
  have hmu : μ.real univ ≤ M := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
    rwa [ENNReal.toReal_ofReal hM] at this
  have hmu0 : 0 ≤ μ.real univ := measureReal_nonneg
  -- integrate the pointwise inequality
  have h1 : ∫ t, (1 / 2 : ℝ) ^ k * t ^ k ∂μ ≤ ∫ t, (p k t + 2 * B) ∂μ := by
    refine integral_mono_ae (hmom.const_mul _) (hPint.add (integrable_const _)) ?_
    filter_upwards [ae_nonneg_of_Iio hμ] with t ht
    have := hF.half_pow_le_add hk ht
    have e : (1 / 2 : ℝ) ^ k * t ^ k = (t / 2) ^ k := by rw [← mul_pow]; congr 1; ring
    rw [e]; exact this
  rw [integral_const_mul, integral_add hPint (integrable_const _), integral_const, heq] at h1
  have h2 : ∫ t, p k t ∂μ₀ ≤ (momC2 C μ₀ * k) ^ k := integral_p_mu0_le hF hμ₀ hint hk
  have h3 : (1 / 2 : ℝ) ^ k * ∫ t, t ^ k ∂μ ≤ (momC2 C μ₀ * k) ^ k + 2 * B * M := by
    have : μ.real univ • (2 * B) ≤ M * (2 * B) := by
      rw [smul_eq_mul]; exact mul_le_mul_of_nonneg_right hmu (by positivity)
    nlinarith
  have h4 : ∫ t, t ^ k ∂μ ≤ (2 * momC2 C μ₀ * k) ^ k + 2 * M * (2 * (3 * C) * k) ^ k := by
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    have : ∫ t, t ^ k ∂μ = 2 ^ k * ((1 / 2 : ℝ) ^ k * ∫ t, t ^ k ∂μ) := by
      rw [← mul_assoc, ← mul_pow]; norm_num
    rw [this]
    calc 2 ^ k * ((1 / 2 : ℝ) ^ k * ∫ t, t ^ k ∂μ) ≤ 2 ^ k * ((momC2 C μ₀ * k) ^ k + 2 * B * M) := by
          gcongr
      _ = (2 * momC2 C μ₀ * k) ^ k + 2 * M * (2 * (3 * C) * k) ^ k := by
          rw [hB, mul_add, mul_assoc 2 (momC2 C μ₀), ← mul_pow]
          have : (2 * (3 * C) * (k : ℝ)) ^ k = 2 ^ k * ((3 * C) * k) ^ k := by
            rw [mul_assoc, mul_pow]
          rw [this]; ring
  -- combine into `(C₃ k)^k`
  set c₁ : ℝ := 2 * momC2 C μ₀ with hc₁
  set c₂ : ℝ := 2 * (3 * C) * (2 * M + 1) with hc₂
  have hc₁nn : 0 ≤ c₁ := by
    have : 0 ≤ momC2 C μ₀ := by
      unfold momC2
      have := momM_pos hF.C_pos
      have : (0 : ℝ) ≤ max 1 (∫ t, Real.exp (π * t) ∂μ₀) := le_trans zero_le_one (le_max_left _ _)
      positivity
    positivity
  have hc₂nn : 0 ≤ c₂ := by
    have := hF.C_pos; have := hF.C_pos; positivity
  have hmx : 0 ≤ max c₁ c₂ := le_trans hc₁nn (le_max_left _ _)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hMk : 2 * M ≤ (2 * M + 1) ^ k := by
    calc 2 * M ≤ 2 * M + 1 := by linarith
      _ = (2 * M + 1) ^ 1 := (pow_one _).symm
      _ ≤ (2 * M + 1) ^ k := pow_le_pow_right₀ (by linarith) hk1
  have hterm1 : (c₁ * k) ^ k ≤ (max c₁ c₂ * k) ^ k := by
    gcongr; exact le_max_left _ _
  have hterm2 : 2 * M * (2 * (3 * C) * k) ^ k ≤ (max c₁ c₂ * k) ^ k := by
    calc 2 * M * (2 * (3 * C) * k) ^ k
        ≤ (2 * M + 1) ^ k * (2 * (3 * C) * k) ^ k := by
          have := hF.C_pos; have := hF.C_pos
          exact mul_le_mul_of_nonneg_right hMk (by positivity)
      _ = (c₂ * k) ^ k := by
          rw [hc₂, ← mul_pow]; congr 1; ring
      _ ≤ (max c₁ c₂ * k) ^ k := by gcongr; exact le_max_right _ _
  have h2le : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one _).symm
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk1
  calc ∫ t, t ^ k ∂μ ≤ (c₁ * k) ^ k + 2 * M * (2 * (3 * C) * k) ^ k := h4
    _ ≤ (max c₁ c₂ * k) ^ k + (max c₁ c₂ * k) ^ k := add_le_add hterm1 hterm2
    _ = 2 * (max c₁ c₂ * k) ^ k := by ring
    _ ≤ 2 ^ k * (max c₁ c₂ * k) ^ k := by gcongr
    _ = (momC3 C μ₀ M * k) ^ k := by
        unfold momC3
        rw [← hc₁, ← hc₂, ← mul_pow]; congr 1; ring


private lemma momC3_pos (hC : 0 < C) (μ₀ : Measure ℝ) (M : ℝ) : 0 < momC3 C μ₀ M := by
  unfold momC3 momC2
  have := momM_pos hC
  have h1 : (0 : ℝ) < max 1 (∫ t, Real.exp (π * t) ∂μ₀) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have : 0 < 2 * momM C * max 1 (∫ t, Real.exp (π * t) ∂μ₀) := by positivity
  have h2 : 0 < 2 * (2 * momM C * max 1 (∫ t, Real.exp (π * t) ∂μ₀)) := by positivity
  exact mul_pos two_pos (lt_of_lt_of_le h2 (le_max_left _ _))

/-- **Lemma LP-M, moment bound** (`ds:mom`, first part): the interpolation
`t^k ≤ s^k + t^{k+1}/s` controls the even moments by the odd ones. -/
theorem ds_mom_bound (hF : OddFam C p) (hμ₀ : μ₀ (Iio 0) = 0)
    (hint : Integrable (fun t => Real.exp (π * t)) μ₀) {M : ℝ} (hM : 0 ≤ M)
    (hμ : μ (Iio 0) = 0) (hmass : μ univ ≤ ENNReal.ofReal M) {K : ℕ}
    (hmom : ∀ k ≤ K, Integrable (fun t : ℝ => t ^ k) μ)
    (hodd : ∀ k ≤ K, Odd k → ∫ t, p k t ∂μ = ∫ t, p k t ∂μ₀)
    {k : ℕ} (hk : 1 ≤ k) (hkK : k + 1 ≤ K) :
    ∫ t, t ^ k ∂μ ≤ (momC1 C μ₀ M * k) ^ k := by
  have have_fin := isFiniteMeasure_of_mass hmass
  set C₃ := momC3 C μ₀ M with hC₃
  have hC₃pos : 0 < C₃ := momC3_pos hF.C_pos μ₀ M
  have hMp : (1 : ℝ) ≤ M + 1 := by linarith
  have hC₁ : momC1 C μ₀ M = 2 * C₃ * (M + 1) := rfl
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rcases Nat.even_or_odd k with he | ho
  · -- even `k`: interpolate with the odd moment of order `k + 1`
    have hodd1 : Odd (k + 1) := he.add_one
    have hb := odd_moment_bound hF hμ₀ hint hμ hM hmass (k := k + 1) hodd1 (hmom _ hkK)
      (hodd _ hkK hodd1)
    rw [← hC₃] at hb
    set s : ℝ := C₃ * ((k : ℝ) + 1) with hs
    have hspos : 0 < s := by positivity
    have hmu : μ.real univ ≤ M := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
      rwa [ENNReal.toReal_ofReal hM] at this
    have hpt : ∀ t : ℝ, 0 ≤ t → t ^ k ≤ s ^ k + t ^ (k + 1) / s := by
      intro t ht
      by_cases hts : t ≤ s
      · have : t ^ k ≤ s ^ k := pow_le_pow_left₀ ht hts k
        have : 0 ≤ t ^ (k + 1) / s := by positivity
        linarith
      · push Not at hts
        have : t ^ k ≤ t ^ (k + 1) / s := by
          rw [le_div_iff₀ hspos, pow_succ]
          exact mul_le_mul_of_nonneg_left hts.le (by positivity)
        have : 0 ≤ s ^ k := by positivity
        linarith
    have h1 : ∫ t, t ^ k ∂μ ≤ ∫ t, (s ^ k + t ^ (k + 1) / s) ∂μ := by
      refine integral_mono_ae (hmom k (by omega)) ((integrable_const _).add
        ((hmom (k + 1) hkK).div_const s)) ?_
      filter_upwards [ae_nonneg_of_Iio hμ] with t ht using hpt t ht
    rw [integral_add (integrable_const _) ((hmom (k + 1) hkK).div_const s), integral_const,
      integral_div, smul_eq_mul] at h1
    have h2 : ∫ t, t ^ (k + 1) ∂μ ≤ s ^ (k + 1) := by
      refine hb.trans (le_of_eq ?_)
      rw [hs]; push_cast; ring
    have h3 : (∫ t, t ^ (k + 1) ∂μ) / s ≤ s ^ k := by
      rw [div_le_iff₀ hspos, ← pow_succ]; exact h2
    have h4 : ∫ t, t ^ k ∂μ ≤ s ^ k * (M + 1) := by
      have : μ.real univ * s ^ k ≤ M * s ^ k := mul_le_mul_of_nonneg_right hmu (by positivity)
      nlinarith
    have h5 : s ≤ 2 * C₃ * k := by
      rw [hs]; have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    calc ∫ t, t ^ k ∂μ ≤ s ^ k * (M + 1) := h4
      _ ≤ (2 * C₃ * k) ^ k * (M + 1) ^ k := by
          gcongr
          calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
            _ ≤ (M + 1) ^ k := pow_le_pow_right₀ hMp hk
      _ = (momC1 C μ₀ M * k) ^ k := by rw [hC₁, ← mul_pow]; congr 1; ring
  · have hb := odd_moment_bound hF hμ₀ hint hμ hM hmass ho (hmom k (by omega)) (hodd k (by omega) ho)
    refine hb.trans ?_
    have : C₃ ≤ momC1 C μ₀ M := by
      rw [hC₁]; nlinarith
    gcongr


/-- **Lemma LP-M, exponential moment** (`ds:mom`, second part): if the bound holds for all `K`,
`∫ e^{ε t} dμ ≤ M + 1` with `ε = 1/(2 e C₁)`. -/
theorem ds_mom_exp (hF : OddFam C p) (hμ₀ : μ₀ (Iio 0) = 0)
    (hint : Integrable (fun t => Real.exp (π * t)) μ₀) {M : ℝ} (hM : 0 ≤ M)
    (hμ : μ (Iio 0) = 0) (hmass : μ univ ≤ ENNReal.ofReal M)
    (hmom : ∀ k : ℕ, Integrable (fun t : ℝ => t ^ k) μ)
    (hodd : ∀ k : ℕ, Odd k → ∫ t, p k t ∂μ = ∫ t, p k t ∂μ₀) :
    Integrable (fun t => Real.exp (t / (2 * Real.exp 1 * momC1 C μ₀ M))) μ ∧
      ∫ t, Real.exp (t / (2 * Real.exp 1 * momC1 C μ₀ M)) ∂μ ≤ M + 1 := by
  have have_fin := isFiniteMeasure_of_mass hmass
  set C₁ := momC1 C μ₀ M with hC₁
  have hC₁pos : 0 < C₁ := by
    have := momC3_pos hF.C_pos μ₀ M
    rw [hC₁]; unfold momC1; positivity
  set ε : ℝ := 1 / (2 * Real.exp 1 * C₁) with hε
  have hεpos : 0 < ε := by positivity
  have hεe : Real.exp 1 * C₁ * ε = 1 / 2 := by
    rw [hε]; field_simp
  have hmu : μ.real univ ≤ M := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
    rwa [ENNReal.toReal_ofReal hM] at this
  have hmoment : ∀ k : ℕ, 1 ≤ k → ∫ t, t ^ k ∂μ ≤ (C₁ * k) ^ k := fun k hk =>
    ds_mom_bound hF hμ₀ hint hM hμ hmass (K := k + 1) (fun j _ => hmom j) (fun j _ hj => hodd j hj)
      hk le_rfl
  -- the series coefficients
  set b : ℕ → ℝ := fun k => ε ^ k / k.factorial * ∫ t, t ^ k ∂μ with hb
  have hbnn : ∀ k, 0 ≤ b k := fun k =>
    mul_nonneg (by positivity) (integral_nonneg_of_ae ((ae_nonneg_of_Iio hμ).mono fun t ht => by positivity))
  have hb0 : b 0 ≤ M := by
    simp only [hb, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, integral_const,
      smul_eq_mul, mul_one]
    exact hmu
  have hbk : ∀ k, 1 ≤ k → b k ≤ (1 / 2) ^ k := by
    intro k hk
    have hf : (0 : ℝ) < k.factorial := by positivity
    have hexp : (k : ℝ) ^ k / k.factorial ≤ Real.exp 1 ^ k := by
      have := Real.pow_div_factorial_le_exp (x := (k : ℝ)) (Nat.cast_nonneg k) k
      calc (k : ℝ) ^ k / k.factorial ≤ Real.exp k := this
        _ = Real.exp 1 ^ k := by rw [← Real.exp_nat_mul, mul_one]
    have hεk : 0 ≤ ε ^ k / k.factorial := by positivity
    calc b k = ε ^ k / k.factorial * ∫ t, t ^ k ∂μ := rfl
      _ ≤ ε ^ k / k.factorial * (C₁ * k) ^ k := by gcongr; exact hmoment k hk
      _ = (ε * C₁) ^ k * ((k : ℝ) ^ k / k.factorial) := by rw [mul_pow, mul_pow]; ring
      _ ≤ (ε * C₁) ^ k * Real.exp 1 ^ k := by gcongr
      _ = (1 / 2) ^ k := by rw [← mul_pow]; congr 1; linarith [hεe]
  -- the exponential as a series
  have hfun : (fun t : ℝ => Real.exp (t / (2 * Real.exp 1 * C₁))) = fun t => Real.exp (ε * t) := by
    funext t; rw [hε]; ring_nf
  rw [hfun]
  have hmeas : ∀ k : ℕ, AEMeasurable (fun t : ℝ => ENNReal.ofReal ((ε * t) ^ k / k.factorial)) μ :=
    fun k => (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun t : ℝ => (ε * t) ^ k / k.factorial)).aemeasurable
  have hterm : ∀ k : ℕ, ∫⁻ t, ENNReal.ofReal ((ε * t) ^ k / k.factorial) ∂μ = ENNReal.ofReal (b k) := by
    intro k
    have hI : Integrable (fun t : ℝ => ε ^ k / k.factorial * t ^ k) μ := (hmom k).const_mul _
    have := ofReal_integral_eq_lintegral_ofReal hI (by
      filter_upwards [ae_nonneg_of_Iio hμ] with t ht
      positivity)
    rw [integral_const_mul] at this
    rw [show b k = ε ^ k / k.factorial * ∫ t, t ^ k ∂μ from rfl, this]
    refine lintegral_congr fun t => ?_
    congr 1; rw [mul_pow]; ring
  have hexpser : ∫⁻ t, ENNReal.ofReal (Real.exp (ε * t)) ∂μ = ∑' k, ENNReal.ofReal (b k) := by
    rw [← tsum_congr hterm, ← lintegral_tsum hmeas]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_nonneg_of_Iio hμ] with t ht
    have hsum : Summable (fun k : ℕ => (ε * t) ^ k / k.factorial) := Real.summable_pow_div_factorial _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum]
    congr 1
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hbound : ∑' k, ENNReal.ofReal (b k) ≤ ENNReal.ofReal (M + 1) := by
    rw [tsum_eq_zero_add' CompleteLattice.summable]
    have h1 : ∑' k : ℕ, ENNReal.ofReal (b (k + 1)) ≤ ∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) :=
      tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (hbk (k + 1) (by omega))
    have h2 : ∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) = ENNReal.ofReal 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
        ((summable_geometric_two).mul_left (1 / 2) |>.congr fun k => by ring)]
      congr 1
      have : ∑' k : ℕ, (1 / 2 : ℝ) ^ (k + 1) = 1 / 2 * ∑' k : ℕ, (1 / 2 : ℝ) ^ k := by
        rw [← tsum_mul_left]; exact tsum_congr fun k => by ring
      rw [this, tsum_geometric_two]; norm_num
    calc ENNReal.ofReal (b 0) + ∑' k : ℕ, ENNReal.ofReal (b (k + 1))
        ≤ ENNReal.ofReal M + ENNReal.ofReal 1 := add_le_add (ENNReal.ofReal_le_ofReal hb0) (h1.trans h2.le)
      _ = ENNReal.ofReal (M + 1) := by rw [ENNReal.ofReal_add hM zero_le_one]
  have hlint : ∫⁻ t, ENNReal.ofReal (Real.exp (ε * t)) ∂μ ≤ ENNReal.ofReal (M + 1) := hexpser ▸ hbound
  have hI : Integrable (fun t : ℝ => Real.exp (ε * t)) μ := by
    refine ⟨(by fun_prop : Continuous fun t : ℝ => Real.exp (ε * t)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun t => (Real.exp_pos _).le)]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  refine ⟨hI, ?_⟩
  have := ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun t => (Real.exp_pos _).le)
  rw [← this] at hlint
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 hlint


end Mom

/-- **Lemma LP-M** (`ds:mom`, `dual_spectrum_limit.tex` line 33), for an abstract family.
Let `p_k` (`k` odd) be continuous with `|p_k(t)| ≤ (t + Ck)^k` for `t ≥ 0` and `p_k(t) ≥ (t/2)^k` for
`t ≥ 2Ck` (`OddFam C p`), `μ₀` a positive reference measure on `[0, ∞)` with `∫ e^{π t} dμ₀ < ∞`, and
`M ≥ 0`.  There is `C₁ > 0`, depending only on `(C, μ₀, M)`, such that for every positive measure `μ`
on `[0, ∞)` of total mass `≤ M` (the paper's `[T₀, ∞)`, `T₀ ≥ 0`, is covered):

* if `μ` has finite moments of all orders `≤ K` and `∫ p_k dμ = ∫ p_k dμ₀` for odd `k ≤ K`, then
  `∫ t^k dμ ≤ (C₁ k)^k` for `1 ≤ k ≤ K - 1`;
* if this holds for every `K`, then `∫ e^{ε t} dμ ≤ M + 1` for `ε = 1/(2 e C₁)`.

The Laguerre case is `ds_mom_laguerre`, its mass bound `ds_mom_mass`. -/
theorem ds_mom {C : ℝ} {p : ℕ → C(ℝ, ℝ)} (hF : OddFam C p) (μ₀ : Measure ℝ)
    (hμ₀ : μ₀ (Iio 0) = 0) (hint : Integrable (fun t => Real.exp (π * t)) μ₀) {M : ℝ}
    (hM : 0 ≤ M) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      (∀ μ : Measure ℝ, μ (Iio 0) = 0 → μ univ ≤ ENNReal.ofReal M → ∀ K : ℕ,
        (∀ k ≤ K, Integrable (fun t : ℝ => t ^ k) μ) →
        (∀ k ≤ K, Odd k → ∫ t, p k t ∂μ = ∫ t, p k t ∂μ₀) →
        ∀ k : ℕ, 1 ≤ k → k + 1 ≤ K → ∫ t, t ^ k ∂μ ≤ (C₁ * k) ^ k) ∧
      (∀ μ : Measure ℝ, μ (Iio 0) = 0 → μ univ ≤ ENNReal.ofReal M →
        (∀ k : ℕ, Integrable (fun t : ℝ => t ^ k) μ) →
        (∀ k : ℕ, Odd k → ∫ t, p k t ∂μ = ∫ t, p k t ∂μ₀) →
        Integrable (fun t => Real.exp (t / (2 * Real.exp 1 * C₁))) μ ∧
          ∫ t, Real.exp (t / (2 * Real.exp 1 * C₁)) ∂μ ≤ M + 1) := by
  refine ⟨momC1 C μ₀ M, ?_, ?_, ?_⟩
  · have := momC3_pos hF.C_pos μ₀ M
    unfold momC1; positivity
  · intro μ hμ hmass K hmom hodd k hk hkK
    exact ds_mom_bound hF hμ₀ hint hM hμ hmass hmom hodd hk hkK
  · intro μ hμ hmass hmom hodd
    exact ds_mom_exp hF hμ₀ hint hM hμ hmass hmom hodd

/-! ### The monic Laguerre family -/

/-- The monic Laguerre polynomial `P_k` at weight `w` as a continuous function. -/
noncomputable def lagPC (w : ℝ) (k : ℕ) : C(ℝ, ℝ) := ⟨lagP w k, continuous_lagP w k⟩

@[simp] lemma lagPC_apply (w : ℝ) (k : ℕ) (t : ℝ) : lagPC w k t = lagP w k t := rfl

/-- The monic Laguerre polynomials at weight `w > 0` satisfy the hypotheses of `ds:mom` with
`C = (1 + w)/π` (every larger `C` works as well): `|P_k(t)| ≤ (t + (3+w)k/(4π))^k` and
`P_k(t) ≥ (t/2)^k` for `t ≥ 2(k+w)/π`, from the three-term recurrence (`LP.Laguerre`). -/
theorem lagP_oddFam {w : ℝ} (hw : 0 < w) : OddFam ((1 + w) / π) (lagPC w) where
  C_pos := by positivity
  upper k _ t ht := by
    have h := abs_lagP_le hw k ht
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have e : (3 + w) * (k : ℝ) / (4 * π) ≤ (1 + w) / π * k := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) Real.pi_pos]
      nlinarith [Real.pi_pos, mul_nonneg hk0 hw.le]
    simp only [lagPC_apply]
    exact h.trans (pow_le_pow_left₀ (by positivity) (by linarith) k)
  lower k hk t ht := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.pos
    simp only [lagPC_apply]
    refine lagP_lower hw k (le_trans ?_ ht)
    rw [mul_assoc, show 2 * ((1 + w) / π * (k : ℝ)) = 2 * ((1 + w) * k) / π by ring]
    exact div_le_div_of_nonneg_right (by nlinarith) Real.pi_pos.le

/-- **Lemma LP-M for the Laguerre family**: `ds_mom` for `p_k = P_k` at weight `w > 0`; `C₁` depends
only on `(w, μ₀, M)`. -/
theorem ds_mom_laguerre {w : ℝ} (hw : 0 < w) (μ₀ : Measure ℝ) (hμ₀ : μ₀ (Iio 0) = 0)
    (hint : Integrable (fun t => Real.exp (π * t)) μ₀) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      (∀ μ : Measure ℝ, μ (Iio 0) = 0 → μ univ ≤ ENNReal.ofReal M → ∀ K : ℕ,
        (∀ k ≤ K, Integrable (fun t : ℝ => t ^ k) μ) →
        (∀ k ≤ K, Odd k → ∫ t, lagP w k t ∂μ = ∫ t, lagP w k t ∂μ₀) →
        ∀ k : ℕ, 1 ≤ k → k + 1 ≤ K → ∫ t, t ^ k ∂μ ≤ (C₁ * k) ^ k) ∧
      (∀ μ : Measure ℝ, μ (Iio 0) = 0 → μ univ ≤ ENNReal.ofReal M →
        (∀ k : ℕ, Integrable (fun t : ℝ => t ^ k) μ) →
        (∀ k : ℕ, Odd k → ∫ t, lagP w k t ∂μ = ∫ t, lagP w k t ∂μ₀) →
        Integrable (fun t => Real.exp (t / (2 * Real.exp 1 * C₁))) μ ∧
          ∫ t, Real.exp (t / (2 * Real.exp 1 * C₁)) ∂μ ≤ M + 1) :=
  ds_mom (lagP_oddFam hw) μ₀ hμ₀ hint hM

section Mass

variable {w : ℝ} {μ₀ μ : Measure ℝ}

/-- **Lemma LP-M, mass bound** (`ds:mom`, last sentence): if `T₀ > w/(4π)` and
`∫ P_1 dμ = ∫ P_1 dμ₀` for a measure on `[T₀, ∞)`, then
`μ ≤ ∫ P_1 dμ₀ / (T₀ - w/(4π))`. -/
theorem ds_mom_mass {T₀ : ℝ} (hT₀ : w / (4 * π) < T₀) (hμ : μ (Iio T₀) = 0)
    (hP : Integrable (lagP w 1) μ) (hL : ∫ t, lagP w 1 t ∂μ = ∫ t, lagP w 1 t ∂μ₀) :
    μ univ ≤ ENNReal.ofReal ((∫ t, lagP w 1 t ∂μ₀) / (T₀ - w / (4 * π))) := by
  set δ : ℝ := T₀ - w / (4 * π) with hδ
  have hδpos : 0 < δ := by linarith
  have hae : ∀ᵐ t ∂μ, δ ≤ lagP w 1 t := by
    have e : {t : ℝ | ¬ T₀ ≤ t} = Iio T₀ := by ext t; simp
    have : ∀ᵐ t ∂μ, T₀ ≤ t := by rw [ae_iff, e]; exact hμ
    filter_upwards [this] with t ht
    rw [lagP_one]; linarith
  have h1 : ENNReal.ofReal δ * μ univ ≤ ENNReal.ofReal (∫ t, lagP w 1 t ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hP (hae.mono fun t ht => by simp only [Pi.zero_apply]; linarith)]
    calc ENNReal.ofReal δ * μ univ = ∫⁻ _, ENNReal.ofReal δ ∂μ := by rw [lintegral_const]
      _ ≤ ∫⁻ t, ENNReal.ofReal (lagP w 1 t) ∂μ :=
          lintegral_mono_ae (hae.mono fun t ht => ENNReal.ofReal_le_ofReal ht)
  rw [hL] at h1
  rw [ENNReal.ofReal_div_of_pos hδpos, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hδpos))
    (Or.inl ENNReal.ofReal_ne_top)]
  rwa [mul_comm]

end Mass

/-- info: 'FormalResearch.ModularBootstrap.LP.ds_mom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.LP.ds_mom

/-- info: 'FormalResearch.ModularBootstrap.LP.lagP_oddFam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.LP.lagP_oddFam

/-- info: 'FormalResearch.ModularBootstrap.LP.ds_mom_laguerre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.LP.ds_mom_laguerre

/-- info: 'FormalResearch.ModularBootstrap.LP.ds_mom_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.LP.ds_mom_mass

end FormalResearch.ModularBootstrap.LP
