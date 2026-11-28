module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Measurable Good Boas Window Width `L_0(z)` and Gaussian Kernel `Γ_W` (`ctl:freeze`)

Establishes:
* `dist_int_ge_one_eighth_iff`: `Int.fract x ∈ [1/8, 7/8] ↔ ∀ n : ℤ, 1/8 ≤ |x - n|`.
* `goodL0`: measurable choice of `L₀(z) ∈ [8 log c', 8 log c' + 1/2]` avoiding `φ₀(z) + ℤ` by `≥ 1/8`
  at both endpoints `z ± L₀(z)`.
* `gaussW`: normalized Gaussian `Γ_W(q) = exp(-q^2 / (4 log c')) / (√(2π) √(2 log c'))`, with
  `integral_gaussW = 1`, `gaussW_odd_integral = 0`, `gaussW_sq_integral_le`, and `gaussW_tail_le`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

noncomputable section

/-! ### 1. Finite 3-point selection of pole-avoiding window width `L_0` -/

lemma dist_int_ge_one_eighth_iff (x : ℝ) :
    Int.fract x ∈ Icc (1 / 8 : ℝ) (7 / 8) ↔ ∀ n : ℤ, (1 / 8 : ℝ) ≤ |x - n| := by
  constructor
  · intro ⟨hlo, hhi⟩ n
    have hx : x = (⌊x⌋ : ℝ) + Int.fract x := by rw [Int.fract]; ring
    rcases lt_trichotomy n ⌊x⌋ with hn | rfl | hn
    · have hn1 : (n : ℝ) ≤ (⌊x⌋ : ℝ) - 1 := by exact_mod_cast Int.le_sub_one_of_lt hn
      have hsub : 1 + 1 / 8 ≤ x - n := by linarith only [hx, hn1, hlo]
      rw [abs_of_nonneg (by linarith only [hsub])]
      linarith only [hsub]
    · rw [← show x - (⌊x⌋ : ℝ) = Int.fract x from rfl] at hlo
      have hx_eq : x - (⌊x⌋ : ℝ) = Int.fract x := rfl
      rw [hx_eq, abs_of_nonneg (Int.fract_nonneg x)]
      exact hlo
    · have hn1 : (⌊x⌋ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hn
      have hsub : 1 / 8 ≤ (n : ℝ) - x := by linarith only [hx, hn1, hhi]
      rw [abs_sub_comm, abs_of_nonneg (by linarith only [hsub])]
      exact hsub
  · intro h
    have h0 := h ⌊x⌋
    have h1 := h (⌊x⌋ + 1)
    have hf0 : 0 ≤ Int.fract x := Int.fract_nonneg x
    have hf1 : Int.fract x < 1 := Int.fract_lt_one x
    have heq0 : x - (⌊x⌋ : ℝ) = Int.fract x := rfl
    rw [heq0, abs_of_nonneg hf0] at h0
    have heq1 : x - ((⌊x⌋ + 1 : ℤ) : ℝ) = Int.fract x - 1 := by
      push_cast; rw [← heq0]; ring
    rw [heq1, abs_of_nonpos (by linarith only [hf1])] at h1
    exact ⟨h0, by linarith only [h1]⟩

private lemma fract_bad_unique_pos {a t₁ t₂ : ℝ}
    (ht : (t₁ = 0 ∧ t₂ = 1 / 4) ∨ (t₁ = 0 ∧ t₂ = 1 / 2) ∨ (t₁ = 1 / 4 ∧ t₂ = 1 / 2))
    (h1 : Int.fract (a + t₁) ∉ Icc (1 / 8 : ℝ) (7 / 8))
    (h2 : Int.fract (a + t₂) ∉ Icc (1 / 8 : ℝ) (7 / 8)) : False := by
  rw [dist_int_ge_one_eighth_iff] at h1 h2
  push Not at h1 h2
  obtain ⟨n₁, hn₁⟩ := h1
  obtain ⟨n₂, hn₂⟩ := h2
  have hdiff : |(t₂ - t₁) - ((n₂ - n₁ : ℤ) : ℝ)| < 1 / 4 := by
    have heq : (t₂ - t₁) - ((n₂ - n₁ : ℤ) : ℝ) = ((a + t₂ - n₂) - (a + t₁ - n₁)) := by
      push_cast; ring
    rw [heq]
    exact (abs_sub _ _).trans_lt ((add_lt_add hn₂ hn₁).trans_eq (by norm_num))
  set m : ℤ := n₂ - n₁
  rcases abs_lt.mp hdiff with ⟨hl, hr⟩
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hm_lt : m < 1 := by exact_mod_cast (by linarith only [hl] : (m : ℝ) < 1)
    have hm_gt : -1 < m := by exact_mod_cast (by linarith only [hr] : (-1 : ℝ) < m)
    have hm0 : m = 0 := by omega
    rw [hm0] at hr; norm_num at hr
  · have hm_lt : m < 1 := by exact_mod_cast (by linarith only [hl] : (m : ℝ) < 1)
    have hm_gt : 0 < m := by exact_mod_cast (by linarith only [hr] : (0 : ℝ) < m)
    omega
  · have hm_lt : m < 1 := by exact_mod_cast (by linarith only [hl] : (m : ℝ) < 1)
    have hm_gt : -1 < m := by exact_mod_cast (by linarith only [hr] : (-1 : ℝ) < m)
    have hm0 : m = 0 := by omega
    rw [hm0] at hr; norm_num at hr

private lemma fract_bad_unique_neg {b t₁ t₂ : ℝ}
    (ht : (t₁ = 0 ∧ t₂ = 1 / 4) ∨ (t₁ = 0 ∧ t₂ = 1 / 2) ∨ (t₁ = 1 / 4 ∧ t₂ = 1 / 2))
    (h1 : Int.fract (b - t₁) ∉ Icc (1 / 8 : ℝ) (7 / 8))
    (h2 : Int.fract (b - t₂) ∉ Icc (1 / 8 : ℝ) (7 / 8)) : False := by
  have heq1 : b - t₁ = (b - 1 / 2) + (1 / 2 - t₁) := by ring
  have heq2 : b - t₂ = (b - 1 / 2) + (1 / 2 - t₂) := by ring
  rw [heq1] at h1; rw [heq2] at h2
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact fract_bad_unique_pos (t₁ := 1 / 4) (t₂ := 1 / 2) (Or.inr (Or.inr ⟨rfl, rfl⟩))
      (by norm_num at h2 ⊢; exact h2) (by norm_num at h1 ⊢; exact h1)
  · exact fract_bad_unique_pos (t₁ := 0) (t₂ := 1 / 2) (Or.inr (Or.inl ⟨rfl, rfl⟩))
      (by norm_num at h2 ⊢; exact h2) (by norm_num at h1 ⊢; exact h1)
  · exact fract_bad_unique_pos (t₁ := 0) (t₂ := 1 / 4) (Or.inl ⟨rfl, rfl⟩)
      (by norm_num at h2 ⊢; exact h2) (by norm_num at h1 ⊢; exact h1)

/-- Measurable choice of good half-width `L_0(z) ∈ [8 log c', 8 log c' + 1/2]` avoiding `φ₀(z) + ℤ` by `≥ 1/8`. -/
def goodL0 (c' : ℝ) (φ₀ : ℝ → ℝ) (z : ℝ) : ℝ :=
  let B := 8 * Real.log c'
  B + if Int.fract (z + B - φ₀ z) ∈ Icc (1 / 8 : ℝ) (7 / 8) ∧
        Int.fract (z - B - φ₀ z) ∈ Icc (1 / 8 : ℝ) (7 / 8) then 0
      else if Int.fract (z + (B + 1 / 4) - φ₀ z) ∈ Icc (1 / 8 : ℝ) (7 / 8) ∧
        Int.fract (z - (B + 1 / 4) - φ₀ z) ∈ Icc (1 / 8 : ℝ) (7 / 8) then 1 / 4
      else 1 / 2

lemma goodL0_bounds_and_poles (c' : ℝ) (φ₀ : ℝ → ℝ) (z : ℝ) :
    8 * Real.log c' ≤ goodL0 c' φ₀ z ∧
    goodL0 c' φ₀ z ≤ 8 * Real.log c' + 1 / 2 ∧
    (∀ n : ℤ, (1 / 8 : ℝ) ≤ |z + goodL0 c' φ₀ z - φ₀ z - n|) ∧
    (∀ n : ℤ, (1 / 8 : ℝ) ≤ |z - goodL0 c' φ₀ z - φ₀ z - n|) := by
  set B := 8 * Real.log c'
  set a := z + B - φ₀ z
  set b := z - B - φ₀ z
  have ha0 : z + B - φ₀ z = a + 0 := by ring
  have hb0 : z - B - φ₀ z = b - 0 := by ring
  have ha1 : z + (B + 1 / 4) - φ₀ z = a + 1 / 4 := by ring
  have hb1 : z - (B + 1 / 4) - φ₀ z = b - 1 / 4 := by ring
  have ha2 : z + (B + 1 / 2) - φ₀ z = a + 1 / 2 := by ring
  have hb2 : z - (B + 1 / 2) - φ₀ z = b - 1 / 2 := by ring
  have hok : ∀ t : ℝ, Int.fract (a + t) ∈ Icc (1 / 8 : ℝ) (7 / 8) →
      Int.fract (b - t) ∈ Icc (1 / 8 : ℝ) (7 / 8) →
      (∀ n : ℤ, 1 / 8 ≤ |z + (B + t) - φ₀ z - n|) ∧
      (∀ n : ℤ, 1 / 8 ≤ |z - (B + t) - φ₀ z - n|) := by
    intro t ht1 ht2
    rw [dist_int_ge_one_eighth_iff] at ht1 ht2
    refine ⟨fun n => ?_, fun n => ?_⟩
    · have h := ht1 n
      rwa [show a + t - n = z + (B + t) - φ₀ z - n by dsimp [a]; ring] at h
    · have h := ht2 n
      rwa [show b - t - n = z - (B + t) - φ₀ z - n by dsimp [b]; ring] at h
  unfold goodL0
  dsimp only
  split_ifs with h0 h1
  · simp only [add_zero]
    exact ⟨le_rfl, by linarith, by simpa using (dist_int_ge_one_eighth_iff _).mp h0.1,
      by simpa using (dist_int_ge_one_eighth_iff _).mp h0.2⟩
  · have hp := hok (1 / 4) (by rw [← ha1]; exact h1.1) (by rw [← hb1]; exact h1.2)
    exact ⟨by linarith, by linarith, hp.1, hp.2⟩
  · have h2a : Int.fract (a + 1 / 2) ∈ Icc (1 / 8 : ℝ) (7 / 8) := by
      by_contra h2a'
      by_cases h0a : Int.fract (a + 0) ∈ Icc (1 / 8 : ℝ) (7 / 8)
      · by_cases h1a : Int.fract (a + 1 / 4) ∈ Icc (1 / 8 : ℝ) (7 / 8)
        · have h0b : Int.fract (b - 0) ∉ Icc (1 / 8 : ℝ) (7 / 8) := fun hb =>
            h0 ⟨by rwa [ha0], by rwa [hb0]⟩
          have h1b : Int.fract (b - 1 / 4) ∉ Icc (1 / 8 : ℝ) (7 / 8) := fun hb =>
            h1 ⟨by rwa [ha1], by rwa [hb1]⟩
          exact fract_bad_unique_neg (Or.inl ⟨rfl, rfl⟩) h0b h1b
        · exact fract_bad_unique_pos (Or.inr (Or.inr ⟨rfl, rfl⟩)) h1a h2a'
      · exact fract_bad_unique_pos (Or.inr (Or.inl ⟨rfl, rfl⟩)) h0a h2a'
    have h2b : Int.fract (b - 1 / 2) ∈ Icc (1 / 8 : ℝ) (7 / 8) := by
      by_contra h2b'
      by_cases h0b : Int.fract (b - 0) ∈ Icc (1 / 8 : ℝ) (7 / 8)
      · by_cases h1b : Int.fract (b - 1 / 4) ∈ Icc (1 / 8 : ℝ) (7 / 8)
        · have h0a : Int.fract (a + 0) ∉ Icc (1 / 8 : ℝ) (7 / 8) := fun ha =>
            h0 ⟨by rwa [ha0], by rwa [hb0]⟩
          have h1a : Int.fract (a + 1 / 4) ∉ Icc (1 / 8 : ℝ) (7 / 8) := fun ha =>
            h1 ⟨by rwa [ha1], by rwa [hb1]⟩
          exact fract_bad_unique_pos (Or.inl ⟨rfl, rfl⟩) h0a h1a
        · exact fract_bad_unique_neg (Or.inr (Or.inr ⟨rfl, rfl⟩)) h1b h2b'
      · exact fract_bad_unique_neg (Or.inr (Or.inl ⟨rfl, rfl⟩)) h0b h2b'
    have hp := hok (1 / 2) h2a h2b
    exact ⟨by linarith, by linarith, hp.1, hp.2⟩

lemma measurable_goodL0 (c' : ℝ) {φ₀ : ℝ → ℝ} (hφ : Measurable φ₀) :
    Measurable (goodL0 c' φ₀) := by
  unfold goodL0
  dsimp only
  have hmono : Monotone (Int.floor : ℝ → ℤ) := fun _ _ hab => Int.floor_mono hab
  have hfloor : Measurable (Int.floor : ℝ → ℤ) := hmono.measurable
  have hfract : Measurable (Int.fract : ℝ → ℝ) := by
    have heq : (Int.fract : ℝ → ℝ) = fun x : ℝ => x - (Int.floor x : ℝ) := rfl
    rw [heq]
    exact measurable_id.sub (measurable_from_top.comp hfloor)
  have hf_add : ∀ t : ℝ, Measurable fun z : ℝ => Int.fract (z + t - φ₀ z) := fun t =>
    hfract.comp ((measurable_id.add_const t).sub hφ)
  have hf_sub : ∀ t : ℝ, Measurable fun z : ℝ => Int.fract (z - t - φ₀ z) := fun t =>
    hfract.comp ((measurable_id.sub_const t).sub hφ)
  have hmset : ∀ t : ℝ, MeasurableSet {z : ℝ |
      Int.fract (z + t - φ₀ z) ∈ Icc (1 / 8 : ℝ) (7 / 8) ∧
      Int.fract (z - t - φ₀ z) ∈ Icc (1 / 8 : ℝ) (7 / 8)} := fun t =>
    (hf_add t measurableSet_Icc).inter (hf_sub t measurableSet_Icc)
  refine measurable_const.add ?_
  exact Measurable.ite (hmset (8 * Real.log c')) measurable_const
    (Measurable.ite (hmset (8 * Real.log c' + 1 / 4)) measurable_const measurable_const)

/-! ### 2. Normalized Gaussian window `gaussW` (`Γ_W`) -/

/-- Normalized Gaussian density `Γ_W(q) = exp(-q² / (4 log c')) / (√(2π) √(2 log c'))`. -/
def gaussW (c' q : ℝ) : ℝ :=
  Real.exp (-q ^ 2 / (2 * (2 * Real.log c'))) / (Real.sqrt (2 * π) * Real.sqrt (2 * Real.log c'))

lemma gaussW_nonneg (c' q : ℝ) : 0 ≤ gaussW c' q := by
  unfold gaussW; positivity

lemma gaussW_symm (c' q : ℝ) : gaussW c' (-q) = gaussW c' q := by
  unfold gaussW; simp only [neg_sq]

lemma integrable_gaussW {c' : ℝ} (hc' : 1 < c') : Integrable (gaussW c') := by
  have hl : 0 < Real.log c' := Real.log_pos hc'
  have hb : 0 < (2 * (2 * Real.log c'))⁻¹ := by positivity
  have h1 := (integrable_exp_neg_mul_sq hb).div_const (Real.sqrt (2 * π) * Real.sqrt (2 * Real.log c'))
  refine h1.congr (Eventually.of_forall fun q => ?_)
  unfold gaussW; ring_nf

lemma integral_gaussW {c' : ℝ} (hc' : 1 < c') : ∫ q : ℝ, gaussW c' q = 1 := by
  have hl : 0 < Real.log c' := Real.log_pos hc'
  have hpi := Real.pi_pos
  have heq : (fun q => gaussW c' q) =
      fun q => Real.exp (-(2 * (2 * Real.log c'))⁻¹ * q ^ 2) / (Real.sqrt (2 * π) * Real.sqrt (2 * Real.log c')) := by
    ext q; unfold gaussW; ring_nf
  rw [heq, integral_div, integral_gaussian, div_eq_one_iff_eq (by positivity)]
  rw [div_inv_eq_mul,
    show π * (2 * (2 * Real.log c')) = (2 * π) * (2 * Real.log c') by ring,
    Real.sqrt_mul (by positivity)]

lemma gaussW_odd_integral (c' L : ℝ) : ∫ q in (-L)..L, q * gaussW c' q = 0 := by
  have hodd : ∀ q, (-q) * gaussW c' (-q) = -(q * gaussW c' q) := fun q => by
    rw [gaussW_symm]; ring
  have hcomp := intervalIntegral.integral_comp_neg (a := -L) (b := L) (f := fun q => q * gaussW c' q)
  simp only [neg_neg] at hcomp
  have hneg : ∫ q in (-L)..L, (-q) * gaussW c' (-q) = -∫ q in (-L)..L, q * gaussW c' q := by
    simp_rw [hodd, intervalIntegral.integral_neg]
  linarith only [hcomp, hneg]

private lemma gaussW_sq_pt {W2 : ℝ} (hW2 : 0 < W2) (q : ℝ) :
    q ^ 2 * Real.exp (-q ^ 2 / (2 * W2)) ≤ 4 * W2 * Real.exp (-q ^ 2 / (4 * W2)) := by
  have h1 := Real.add_one_le_exp (q ^ 2 / (4 * W2))
  have hpos : 0 < Real.exp (q ^ 2 / (4 * W2)) := Real.exp_pos _
  have h2 : q ^ 2 / (4 * W2) ≤ Real.exp (q ^ 2 / (4 * W2)) := by linarith
  have h3 : q ^ 2 / (4 * W2) * Real.exp (-(q ^ 2 / (4 * W2))) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hpos]
    exact h2
  have h4 : q ^ 2 * Real.exp (-q ^ 2 / (4 * W2)) ≤ 4 * W2 := by
    have he : -q ^ 2 / (4 * W2) = -(q ^ 2 / (4 * W2)) := by ring
    rw [he]
    have hmul := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 4 * W2)
    calc q ^ 2 * Real.exp (-(q ^ 2 / (4 * W2)))
        = (4 * W2) * (q ^ 2 / (4 * W2) * Real.exp (-(q ^ 2 / (4 * W2)))) := by
          field_simp [hW2.ne']
      _ ≤ (4 * W2) * 1 := hmul
      _ = 4 * W2 := mul_one _
  have he2 : -q ^ 2 / (2 * W2) = -(q ^ 2 / (4 * W2)) + (-q ^ 2 / (4 * W2)) := by ring
  rw [he2, Real.exp_add, ← mul_assoc]
  have hex_nn : 0 ≤ Real.exp (-(q ^ 2 / (4 * W2))) := (Real.exp_pos _).le
  rw [show -q ^ 2 / (4 * W2) = -(q ^ 2 / (4 * W2)) by ring] at h4 ⊢
  exact mul_le_mul_of_nonneg_right h4 hex_nn

lemma gaussW_sq_integral_le {c' : ℝ} (hc' : 1 < c') :
    ∫ q : ℝ, q ^ 2 * gaussW c' q ≤ 8 * Real.sqrt 2 * Real.log c' := by
  have hl : 0 < Real.log c' := Real.log_pos hc'
  have hpi := Real.pi_pos
  let W2 : ℝ := 2 * Real.log c'
  have hW2 : 0 < W2 := by positivity
  let g : ℝ → ℝ := fun q => (4 * W2 * Real.exp (-(4 * W2)⁻¹ * q ^ 2)) / (Real.sqrt (2 * π) * Real.sqrt W2)
  have hb4 : 0 < (4 * W2)⁻¹ := by positivity
  have hg_int : Integrable g :=
    (((integrable_exp_neg_mul_sq hb4).const_mul (4 * W2)).div_const _).congr (Eventually.of_forall fun _ => rfl)
  have hle_pt : ∀ q : ℝ, q ^ 2 * gaussW c' q ≤ g q := fun q => by
    unfold gaussW; dsimp [g, W2]
    have hden_pos : 0 < Real.sqrt (2 * π) * Real.sqrt (2 * Real.log c') := by positivity
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hden_pos]
    have hpt_q := gaussW_sq_pt hW2 q
    dsimp [W2] at hpt_q
    simpa [mul_comm, div_eq_mul_inv] using hpt_q
  have hcont_f : Continuous (fun q : ℝ => q ^ 2 * gaussW c' q) := by unfold gaussW; fun_prop
  have hf_int : Integrable (fun q : ℝ => q ^ 2 * gaussW c' q) :=
    hg_int.mono hcont_f.aestronglyMeasurable (Eventually.of_forall fun q => by
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (gaussW_nonneg c' q)),
        Real.norm_of_nonneg (by dsimp [g]; positivity)]
      exact hle_pt q)
  have hg_val : ∫ q : ℝ, g q = 8 * Real.sqrt 2 * Real.log c' := by
    dsimp [g]
    rw [integral_div, integral_const_mul, integral_gaussian, div_inv_eq_mul,
      show π * (4 * W2) = 2 * ((2 * π) * W2) by ring,
      Real.sqrt_mul zero_le_two, Real.sqrt_mul (by positivity)]
    have hs1 : Real.sqrt (2 * π) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hs2 : Real.sqrt W2 ≠ 0 := (Real.sqrt_pos.mpr hW2).ne'
    dsimp [W2] at hs2 ⊢
    field_simp [hs1, hs2]; ring
  exact (integral_mono hf_int hg_int hle_pt).trans_eq hg_val

lemma gaussW_tail_le {c' : ℝ} (hc' : 1 < c') :
    ∫ q in {q : ℝ | 8 * Real.log c' < |q|}, gaussW c' q ≤ 2 * c' ^ (-8 : ℝ) := by
  have hl : 0 < Real.log c' := Real.log_pos hc'
  have hc0 : 0 < c' := by linarith
  have hpi := Real.pi_pos
  set L := 8 * Real.log c'
  set W2 := 2 * Real.log c'
  have hW2 : 0 < W2 := by positivity
  let g : ℝ → ℝ := fun q => (c' ^ (-8 : ℝ)) * (Real.exp (-(4 * W2)⁻¹ * q ^ 2) / (Real.sqrt (2 * π) * Real.sqrt W2))
  have hb4 : 0 < (4 * W2)⁻¹ := by positivity
  have hg_int : Integrable g :=
    (((integrable_exp_neg_mul_sq hb4).div_const _).const_mul (c' ^ (-8 : ℝ))).congr
      (Eventually.of_forall fun _ => rfl)
  have hpt : ∀ q ∈ {q : ℝ | L < |q|}, gaussW c' q ≤ g q := by
    intro q hq
    have hq_sq : L ^ 2 ≤ q ^ 2 := by
      have h1 : L ^ 2 < |q| ^ 2 := pow_lt_pow_left₀ hq (by positivity) two_ne_zero
      rw [sq_abs] at h1
      exact h1.le
    have hexp_le : Real.exp (-q ^ 2 / (2 * W2)) ≤ c' ^ (-8 : ℝ) * Real.exp (-(4 * W2)⁻¹ * q ^ 2) := by
      have he_c : c' ^ (-8 : ℝ) = Real.exp (-(8 * Real.log c')) := by
        rw [Real.rpow_def_of_pos hc0]; congr 1; ring
      rw [he_c, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hL2 : L ^ 2 / (4 * W2) = 8 * Real.log c' := by
        dsimp [L, W2]; field_simp [hl.ne']; ring
      rw [← hL2]
      have hdiv : q ^ 2 / (2 * W2) = q ^ 2 / (4 * W2) + q ^ 2 / (4 * W2) := by ring
      have hle_div : L ^ 2 / (4 * W2) ≤ q ^ 2 / (4 * W2) := by gcongr
      linarith only [hle_div, show -q ^ 2 / (2 * W2) = -(q ^ 2 / (4 * W2) + q ^ 2 / (4 * W2)) by ring,
        show -(L ^ 2 / (4 * W2)) + -(4 * W2)⁻¹ * q ^ 2 = -(L ^ 2 / (4 * W2) + q ^ 2 / (4 * W2)) by ring]
    unfold gaussW; dsimp [g, W2]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hexp_le (by positivity)
  have hset_int : IntegrableOn (gaussW c') {q : ℝ | L < |q|} := (integrable_gaussW hc').integrableOn
  have hg_sub : IntegrableOn g {q : ℝ | L < |q|} := hg_int.integrableOn
  have hg_val : ∫ q : ℝ, g q = Real.sqrt 2 * c' ^ (-8 : ℝ) := by
    dsimp [g]
    rw [integral_const_mul, integral_div, integral_gaussian, div_inv_eq_mul,
      show π * (4 * W2) = 2 * ((2 * π) * W2) by ring,
      Real.sqrt_mul zero_le_two, Real.sqrt_mul (by positivity)]
    have hs1 : Real.sqrt (2 * π) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hs2 : Real.sqrt W2 ≠ 0 := (Real.sqrt_pos.mpr hW2).ne'
    dsimp [W2] at hs2 ⊢
    field_simp [hs1, hs2]
  calc ∫ q in {q : ℝ | L < |q|}, gaussW c' q
      ≤ ∫ q in {q : ℝ | L < |q|}, g q :=
        setIntegral_mono_on hset_int hg_sub (measurableSet_lt measurable_const continuous_abs.measurable) hpt
    _ ≤ ∫ q : ℝ, g q := setIntegral_le_integral hg_int (Eventually.of_forall fun q => by dsimp [g]; positivity)
    _ = Real.sqrt 2 * c' ^ (-8 : ℝ) := hg_val
    _ ≤ 2 * c' ^ (-8 : ℝ) := by
        gcongr
        calc Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
          _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]

end

end FormalResearch.ModularBootstrap.FiveTerm
