/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctBumpProfileField

/-!
# `fct:physical-budget`: the `K₁`-dependence of the physical bump budget and the field `physical_budget` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:physical-budget` (`(fct:B-physical)`):
`∫_0^∞ B = C_fl(H₀) + (M₁(c) K₁ + O_{K₄}(1)) c^{-3/4}`, `C_fl(H_*) = 0`, constants independent of `K₁` and of the later `K_d`.

`FctMainHankelInputs.physical_budget` asks (`Re W̃^bump(0) = c^{-1/3}∫B + O(e^{-c' c^{1/2}})`):
`∃ C₀ b₂, ∀ K₁ > 0, ∃ c₀, ∀ c ≥ c₀, Re ctWbump(B_c^ε)(0) ≤ (C₀ + b₂ K₁) c^{-13/12}`.

**Proved here** (`physBump_integral_le`, `physical_budget_field`):

* the margin of the lemma, part (e): `B = n(B₀ + p₂ + p₃)` with `B₀` the `K₁ = 0` bump and `p₂, p₃` the two margin pieces of
  `physBump_pieces`; their `L¹` norms are `≤ C K₁ c^{-2}δ^{-5/2}` and `C K₁ c^{-1}δ^{-1/2}` (symbol classes `(7/2, 7/2)`, `(3/2, 3/2)`),
  hence `≤ C' K₁ c^{-3/4}` for `δ ≍ c^{-1/2}`;
* the reflected term `c^{-1/3} B̂(c)` is `O(e^{-c' c^{1/2}})` (`bump_laplace_decay`) and is absorbed for large `c`;
* the passage `Re ctWbump(0) = c^{-1/3} ∫B + ε c^{-1/3} B̂(c)` and the quantifier order `C₀, b₂` before `K₁`, `c₀` after.

**Not proved here (hypothesis `hvac`, named after the paper).**  The `K₁`-free vacuum budget `∫ B|_{K₁ = 0} ≤ A c^{-3/4}`: this is
`fct:physical-budget` at `K₁ = 0`, i.e. parts (a)-(d) of its proof (the paired decomposition `(fct:vac-paired)`, the cosine penalty
`(fct:cos-pen)`, `(fct:bump-1L)`, `(fct:bump-2L)` of `fct:comp-D` (2), the finite-part cancellation of `fct:phikill` (3) and the
`B_tr` mass), for `H₀ = H_*` (`C_fl(H_*) = 0`).  It does not involve `K₁`; the `K₁`-linear part of the lemma and the
assembly are proved.

Class: proved under the explicit hypotheses `hsize`, `hR`, `hT`, `hvac`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped ContDiff Real
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty.FctSym

open SymW

/-- A two-regime profile with `α = β > 1` is integrable with `∫|p| ≤ 2 K₀ M (3δ/2)^{1-α}/(α-1)`. -/
lemma l1_pw_eq {δ M α : ℝ} {K : ℕ → ℝ} {p : ℝ → ℝ} (h : SymW (Ici (3 / 2 * δ)) (pw M α α) K p)
    (hsup : ∀ x : ℝ, x < 3 / 2 * δ → p x = 0) (hM : 0 ≤ M) (hδ : 0 < δ) (hδ1 : 3 / 2 * δ ≤ 1) (hα : 1 < α) :
    Integrable p ∧ ∫ x, ‖p x‖ ≤ 2 * K 0 * M * (3 / 2 * δ) ^ (1 - α) / (α - 1) := by
  have hp := h.toBumpProfile hM hsup
  have hb : 0 < (3 / 2 : ℝ) * δ := by positivity
  refine ⟨by simpa using hp.integrable_iteratedDeriv hδ1 hα 0, ?_⟩
  have hl := hp.l1_le hb hδ1 hα 0
  simp only [iteratedDeriv_zero, Nat.cast_zero, add_zero] at hl
  have hI := (integral_rpow_neg_bounds (a := α) hb hδ1).1 hα
  have hX : 1 ≤ (3 / 2 * δ) ^ (1 - α) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hb hδ1 (by linarith)
  have hK : 0 ≤ K 0 := h.K_nonneg 0
  have h1 : (∫ x in (3 / 2 * δ)..1, x ^ (-α)) + 1 / (α - 1) ≤ 2 * (3 / 2 * δ) ^ (1 - α) / (α - 1) := by
    have : 1 / (α - 1) ≤ (3 / 2 * δ) ^ (1 - α) / (α - 1) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    have e : 2 * (3 / 2 * δ) ^ (1 - α) / (α - 1) = (3 / 2 * δ) ^ (1 - α) / (α - 1) + (3 / 2 * δ) ^ (1 - α) / (α - 1) := by ring
    linarith
  calc ∫ x, ‖p x‖ ≤ K 0 * M * ((∫ x in (3 / 2 * δ)..1, x ^ (-α)) + 1 / (α - 1)) := hl
    _ ≤ K 0 * M * (2 * (3 / 2 * δ) ^ (1 - α) / (α - 1)) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hK hM)
    _ = _ := by ring

/-- The bump is integrable, and its integral exceeds the `K₁ = 0` integral by at most the `L¹` norms of the two margin pieces
(Lemma `fct:physical-budget` (e)): `B_{K₁} = B₀ + n (p₂ + p₃)`, `p₂ ∈ (|K₁c^{-2}| M_Φ (M_R + 2), 7/2, 7/2)`,
`p₃ ∈ (|K₁c^{-1}| M_Φ (M_R + 2), 3/2, 3/2)`. -/
theorem physBump_integral_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {Kχ : ℕ → ℝ}
    (hKχ : ∀ (r : ℕ) (s : ℝ), |iteratedDeriv r χ s| ≤ Kχ r)
    {KΦ KR KT : ℕ → ℝ} {n c δ s K1 K4 MΦ MR MT : ℝ} {F R T4 : ℝ → ℝ}
    (hδ : 0 < δ) (hδ1 : 3 / 2 * δ ≤ 1) (hs : |s| ≤ 3 / 2 * δ / 2)
    (hsmall : (5 * π ^ 2 / 96) * c⁻¹ ^ 2 * (3 / 2 * δ) ^ (-3 : ℝ) ≤ 1)
    (hMΦ : 0 ≤ MΦ) (hMR : 0 ≤ MR) (hMT : 0 ≤ MT)
    (hF : SymW (Ici (3 / 2 * δ)) (pw MΦ (3 / 2) (3 / 2)) KΦ F)
    (hR : SymW (Ici (3 / 2 * δ)) (pw MR (-1) 0) KR (fun x => R x - 1))
    (hT : SymW (Icc (3 / 2 * δ) (6 * δ)) (pw MT (-(1 / 2)) (3 / 2)) KT T4) :
    Integrable (physBump χ n c δ s K1 K4 (fun x => F x * R x) F T4) ∧
      Integrable (physBump χ n c δ s 0 K4 (fun x => F x * R x) F T4) ∧
      ∫ x, physBump χ n c δ s K1 K4 (fun x => F x * R x) F T4 x ≤
        (∫ x, physBump χ n c δ s 0 K4 (fun x => F x * R x) F T4 x) +
          |n| * (2 * KpMar1 Kχ KΦ KR 0 * (|K1 * c⁻¹ ^ 2| * (MΦ * (MR + 2))) * (3 / 2 * δ) ^ (-(5 / 2 : ℝ)) / (5 / 2) +
              2 * KpMar2 Kχ KΦ KR 0 * (|K1 * c⁻¹| * (MΦ * (MR + 2))) * (3 / 2 * δ) ^ (-(1 / 2 : ℝ)) / (1 / 2)) := by
  have hprof := physBump_profile hχ hKχ (n := n) (c := c) (δ := δ) (s := s) (K1 := K1) (K4 := K4) (MΦ := MΦ) (MR := MR)
    (MT := MT) (F := F) (R := R) (T4 := T4) hδ hs hsmall hMΦ hMR hMT hF hR hT
  have hprof0 := physBump_profile hχ hKχ (n := n) (c := c) (δ := δ) (s := s) (K1 := 0) (K4 := K4) (MΦ := MΦ) (MR := MR)
    (MT := MT) (F := F) (R := R) (T4 := T4) hδ hs hsmall hMΦ hMR hMT hF hR hT
  obtain ⟨p1, p2, p3, p4⟩ := physBump_pieces hχ hKχ (K1 := K1) (K4 := K4) (c := c) (s := s) (MΦ := MΦ) (αΦ := 3 / 2)
    (βΦ := 3 / 2) (MR := MR) (MT := MT) hδ hs hsmall hMR hMT hF hR hT
  have hint : Integrable (physBump χ n c δ s K1 K4 (fun x => F x * R x) F T4) := by
    simpa using hprof.integrable_iteratedDeriv hδ1 (by norm_num : (1 : ℝ) < 3 / 2) 0
  have hint0 : Integrable (physBump χ n c δ s 0 K4 (fun x => F x * R x) F T4) := by
    simpa using hprof0.integrable_iteratedDeriv hδ1 (by norm_num : (1 : ℝ) < 3 / 2) 0
  have hz : ∀ x : ℝ, x < 3 / 2 * δ → χ (x / (3 * δ)) = 0 := fun x hx =>
    hχ.zero _ (by rw [div_le_iff₀ (by positivity)]; linarith)
  have hm2 : 0 ≤ |K1 * c⁻¹ ^ 2| * (MΦ * (MR + 2)) := mul_nonneg (abs_nonneg _) (mul_nonneg hMΦ (by linarith))
  have hm3 : 0 ≤ |K1 * c⁻¹| * (MΦ * (MR + 2)) := mul_nonneg (abs_nonneg _) (mul_nonneg hMΦ (by linarith))
  have e52 : (1 - (3 / 2 + 2 : ℝ)) = -(5 / 2) := by norm_num
  have e52' : ((3 / 2 + 2 : ℝ) - 1) = 5 / 2 := by norm_num
  have e12 : (1 - (3 / 2 : ℝ)) = -(1 / 2) := by norm_num
  have e12' : ((3 / 2 : ℝ) - 1) = 1 / 2 := by norm_num
  obtain ⟨i2, l2⟩ := l1_pw_eq p2 (fun x hx => by simp [hz x hx]) hm2 hδ hδ1 (by norm_num : (1 : ℝ) < 3 / 2 + 2)
  obtain ⟨i3, l3⟩ := l1_pw_eq p3 (fun x hx => by simp [hz x hx]) hm3 hδ hδ1 (by norm_num : (1 : ℝ) < 3 / 2)
  rw [e52, e52'] at l2
  rw [e12, e12'] at l3
  -- the pointwise identity `B_{K₁} = B₀ + n (p₂ + p₃)`
  have hid : physBump χ n c δ s K1 K4 (fun x => F x * R x) F T4 = fun x =>
      physBump χ n c δ s 0 K4 (fun x => F x * R x) F T4 x +
        n * (χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ ^ 2 * x ^ (-2 : ℝ) * (F x * R x + F x)) +
          χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ * (F x * R x + F x))) := by
    funext x
    simp only [physBump, physEta]; ring
  rw [hid] at hint ⊢
  refine ⟨hint, hint0, ?_⟩
  have hg : Integrable (fun x => n * (χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ ^ 2 * x ^ (-2 : ℝ) * (F x * R x + F x))) +
      n * (χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ * (F x * R x + F x)))) := (i2.const_mul n).add (i3.const_mul n)
  have hsplit : ∫ x, (physBump χ n c δ s 0 K4 (fun x => F x * R x) F T4 x +
      n * (χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ ^ 2 * x ^ (-2 : ℝ) * (F x * R x + F x)) +
        χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ * (F x * R x + F x)))) =
      (∫ x, physBump χ n c δ s 0 K4 (fun x => F x * R x) F T4 x) +
        n * (∫ x, χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ ^ 2 * x ^ (-2 : ℝ) * (F x * R x + F x))) +
        n * (∫ x, χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ * (F x * R x + F x))) := by
    have e : ∀ x : ℝ, physBump χ n c δ s 0 K4 (fun x => F x * R x) F T4 x +
        n * (χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ ^ 2 * x ^ (-2 : ℝ) * (F x * R x + F x)) +
          χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ * (F x * R x + F x))) =
        physBump χ n c δ s 0 K4 (fun x => F x * R x) F T4 x +
        (n * (χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ ^ 2 * x ^ (-2 : ℝ) * (F x * R x + F x))) +
          n * (χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ * (F x * R x + F x)))) := fun x => by ring
    simp_rw [e]
    have h1 := integral_add hint0 hg
    have h2 := integral_add (i2.const_mul n) (i3.const_mul n)
    simp only [integral_const_mul] at h2
    rw [h1, h2]
    ring
  rw [hsplit]
  have b2 : n * ∫ x, χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ ^ 2 * x ^ (-2 : ℝ) * (F x * R x + F x)) ≤
      |n| * (2 * KpMar1 Kχ KΦ KR 0 * (|K1 * c⁻¹ ^ 2| * (MΦ * (MR + 2))) * (3 / 2 * δ) ^ (-(5 / 2 : ℝ)) / (5 / 2)) := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans l2) (abs_nonneg n)
  have b3 : n * ∫ x, χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ * (F x * R x + F x)) ≤
      |n| * (2 * KpMar2 Kχ KΦ KR 0 * (|K1 * c⁻¹| * (MΦ * (MR + 2))) * (3 / 2 * δ) ^ (-(1 / 2 : ℝ)) / (1 / 2)) := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans l3) (abs_nonneg n)
  linarith

/-! ### The field `physical_budget` -/

lemma exp_absorb {κ : ℝ} (hκ : 0 < κ) (q : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ c : ℝ in atTop, c ^ q * Real.exp (-κ * Real.sqrt c) ≤ η := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * q) κ hκ
  have h2 := h1.comp Real.tendsto_sqrt_atTop
  have h3 : ∀ᶠ c : ℝ in atTop, (Real.sqrt c) ^ (2 * q) * Real.exp (-κ * Real.sqrt c) < η :=
    h2.eventually (gt_mem_nhds hη)
  filter_upwards [h3, eventually_gt_atTop 0] with c hc hc0
  have e : c ^ q = (Real.sqrt c) ^ (2 * q) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc0.le]; congr 1; ring
  rw [e]; exact hc.le

lemma rpow_neg_le_of_le {a y p : ℝ} (ha : 0 < a) (hay : a ≤ y) (hp : 0 ≤ p) : y ^ (-p) ≤ a ^ (-p) :=
  Real.rpow_le_rpow_of_nonpos ha hay (by linarith)

/-- `O = F (O/F)` on the support of the cutoff: the bump built from `O` is the bump built from `F R`, `R = O/F`
(`F > 0` on `[3δ/2, ∞)`; below `3δ/2` both vanish with `χ`). -/
lemma physBump_eq_ratio {χ : ℝ → ℝ} (hχ : IsCutoff χ) {n c δ s L1 K1 K4 : ℝ} {O T4 : ℝ → ℝ}
    (hδ : 0 < δ) (hs : |s| ≤ 3 / 2 * δ / 2) (hL1 : |L1| ≤ 3 / 2 * δ / 2) :
    physBump χ n c δ s K1 K4 O (physF s L1) T4 =
      physBump χ n c δ s K1 K4 (fun x => physF s L1 x * (O x / physF s L1 x)) (physF s L1) T4 := by
  have hx0 : 0 < 3 / 2 * δ := by positivity
  funext x
  by_cases hx : 3 / 2 * δ ≤ x
  · have hpos : physF s L1 x ≠ 0 := (physF_pos hx0 hs hL1 hx).ne'
    simp only [physBump]
    rw [mul_div_cancel₀ _ hpos]
  · have hx3 : x / (3 * δ) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith [not_le.mp hx]
    simp only [physBump, hχ.zero _ hx3]; ring

/-- `Re W̃^bump(0) = c^{-1/3} ∫B + ε Re(c^{-1/3} B̂(c))`: the real part of the bump multiplier at the corner `0`. -/
lemma ctWbump_zero_re_le {B : ℝ → ℝ} {c ε : ℝ} (hc : 0 < c) (hε : ε = 1 ∨ ε = -1) :
    (ctWbump B ε c 0).re ≤ c ^ (-(1 / 3 : ℝ)) * (∫ x, B x) + c ^ (-(1 / 3 : ℝ)) * ‖bumpLaplace B (c : ℂ)‖ := by
  have h0 : bumpDW c B 0 = (((c ^ (-(1 / 3 : ℝ)) * ∫ x, B x : ℝ)) : ℂ) := by
    unfold bumpDW bumpLaplace
    simp only [mul_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul]
    rw [show (∫ x : ℝ, (B x : ℂ)) = ((∫ x : ℝ, B x : ℝ) : ℂ) from integral_ofReal]; push_cast; ring
  have h1 : ‖bumpDW c B 1‖ = c ^ (-(1 / 3 : ℝ)) * ‖bumpLaplace B (c : ℂ)‖ := by
    unfold bumpDW
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hc.le _), mul_one]
  have hεn : ‖(ε : ℂ)‖ = 1 := by
    rcases hε with rfl | rfl <;> simp
  unfold ctWbump
  rw [sub_zero, Complex.add_re, h0, Complex.ofReal_re]
  have : ((ε : ℂ) * bumpDW c B 1).re ≤ ‖bumpDW c B 1‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, hεn, one_mul]
  linarith

/-- The reflected term: `c^{-1/3} ‖B̂(c)‖ ≤ c^{-13/12}` for large `c` (uniformly in the profile data, with constants `Cl, P`). -/
lemma reflected_small {P a₀ : ℝ} (hP : 0 ≤ P) (ha₀ : 0 < a₀) :
    ∀ᶠ c : ℝ in atTop, P * (c ^ (3 / 4 : ℝ) + a₀ ^ (-(5 / 2 : ℝ)) * c ^ (2 : ℝ)) * Real.exp (-(3 * a₀ / 2) * Real.sqrt c) ≤ 1 := by
  have hκ : 0 < 3 * a₀ / 2 := by positivity
  have hA : 0 ≤ a₀ ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg ha₀.le _
  set η : ℝ := 1 / (P * (1 + a₀ ^ (-(5 / 2 : ℝ))) + 1) with hη
  have hη0 : 0 < η := by positivity
  filter_upwards [exp_absorb hκ (3 / 4) hη0, exp_absorb hκ 2 hη0, eventually_gt_atTop 0] with c h1 h2 hc
  have e : P * (c ^ (3 / 4 : ℝ) + a₀ ^ (-(5 / 2 : ℝ)) * c ^ (2 : ℝ)) * Real.exp (-(3 * a₀ / 2) * Real.sqrt c) =
      P * (c ^ (3 / 4 : ℝ) * Real.exp (-(3 * a₀ / 2) * Real.sqrt c) +
        a₀ ^ (-(5 / 2 : ℝ)) * (c ^ (2 : ℝ) * Real.exp (-(3 * a₀ / 2) * Real.sqrt c))) := by ring
  rw [e]
  have h3 : P * (c ^ (3 / 4 : ℝ) * Real.exp (-(3 * a₀ / 2) * Real.sqrt c) +
        a₀ ^ (-(5 / 2 : ℝ)) * (c ^ (2 : ℝ) * Real.exp (-(3 * a₀ / 2) * Real.sqrt c))) ≤ P * (η + a₀ ^ (-(5 / 2 : ℝ)) * η) :=
    mul_le_mul_of_nonneg_left (add_le_add h1 (mul_le_mul_of_nonneg_left h2 hA)) hP
  refine h3.trans ?_
  have : P * (η + a₀ ^ (-(5 / 2 : ℝ)) * η) = P * (1 + a₀ ^ (-(5 / 2 : ℝ))) * η := by ring
  rw [this, hη, mul_one_div, div_le_one (by positivity)]
  linarith

lemma rpow_scale_half {a c p : ℝ} (ha : 0 < a) (hc : 0 < c) :
    (a * c ^ (-(1 / 2 : ℝ))) ^ (-p) = a ^ (-p) * c ^ (p / 2) := by
  rw [Real.mul_rpow ha.le (Real.rpow_nonneg hc.le _), ← Real.rpow_mul hc.le]
  congr 2; ring

lemma KpMar_nonneg {Kχ KΦ KR : ℕ → ℝ} (h1 : ∀ r, 0 ≤ Kχ r) (h2 : ∀ r, 0 ≤ KΦ r) (h3 : ∀ r, 0 ≤ KR r) (r : ℕ) :
    0 ≤ KpMar1 Kχ KΦ KR r ∧ 0 ≤ KpMar2 Kχ KΦ KR r := by
  have hg : ∀ r, 0 ≤ Kgam r := fun r => add_nonneg (Kone_nonneg r) (Kpow_nonneg _ r)
  have hG := Kmul_nonneg h1 hg
  have hR1 : ∀ r, 0 ≤ KR r + Kone r := fun r => add_nonneg (h3 r) (Kone_nonneg r)
  have hF := Kmul_nonneg h2 hR1
  exact ⟨Kmul_nonneg hG (Kmul_nonneg (Kpow_nonneg _) hF) r, Kmul_nonneg hG (Kmul_nonneg Kone_nonneg hF) r⟩

/-- The constants of the budget: `K₁`-slope `Cm` of the margin (`(e)` of the lemma). -/
noncomputable def budgetSlope (K0a K0b X a₀ : ℝ) : ℝ :=
  2 * K0a * X * (3 * a₀ / 2) ^ (-(5 / 2 : ℝ)) / (5 / 2) + 2 * K0b * X * (3 * a₀ / 2) ^ (-(1 / 2 : ℝ)) / (1 / 2)

lemma Mbound {n nmax c K1 A0 B0 X : ℝ} (hc : 1 ≤ c) (hK1 : 0 ≤ K1) (hX : 0 ≤ X) (hn : |n| ≤ nmax) (hA0 : 0 ≤ A0)
    (hB0 : 0 ≤ B0) :
    |n| * (A0 + |K1 * c⁻¹ ^ 2| * X + |K1 * c⁻¹| * X + B0) ≤ nmax * ((A0 + B0) + 2 * K1 * X) := by
  have h1 : |K1 * c⁻¹ ^ 2| ≤ K1 := by
    rw [abs_of_nonneg (by positivity)]
    have : c⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hc)
    nlinarith
  have h2 : |K1 * c⁻¹| ≤ K1 := by
    rw [abs_of_nonneg (by positivity)]
    have : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
    nlinarith
  have h3 : A0 + |K1 * c⁻¹ ^ 2| * X + |K1 * c⁻¹| * X + B0 ≤ (A0 + B0) + 2 * K1 * X := by
    have := mul_le_mul_of_nonneg_right h1 hX
    have := mul_le_mul_of_nonneg_right h2 hX
    linarith
  have hnn : 0 ≤ nmax := (abs_nonneg _).trans hn
  calc |n| * (A0 + |K1 * c⁻¹ ^ 2| * X + |K1 * c⁻¹| * X + B0) ≤ nmax * (A0 + |K1 * c⁻¹ ^ 2| * X + |K1 * c⁻¹| * X + B0) :=
        mul_le_mul_of_nonneg_right hn (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 hnn

lemma exp_le_of_delta {a₀ c δ : ℝ} (hc : 0 < c) (hδa : a₀ * c ^ (-(1 / 2 : ℝ)) ≤ δ) :
    Real.exp (-(3 / 2 * c * 1 * δ)) ≤ Real.exp (-(3 * a₀ / 2) * Real.sqrt c) := by
  refine Real.exp_le_exp.mpr ?_
  have h2 : c * (a₀ * c ^ (-(1 / 2 : ℝ))) ≤ c * δ := mul_le_mul_of_nonneg_left hδa hc.le
  have h3 : c * (a₀ * c ^ (-(1 / 2 : ℝ))) = a₀ * Real.sqrt c := by
    rw [Real.sqrt_eq_rpow, mul_left_comm, ← Real.rpow_one_add' hc.le (by norm_num)]
    norm_num
  linarith

lemma lambda_le {a₀ c δ : ℝ} (ha₀ : 0 < a₀) (hc : 0 < c) (hδa : a₀ * c ^ (-(1 / 2 : ℝ)) ≤ δ) :
    bumpLambda (7 / 2) δ ≤ 1 + a₀ ^ (-(5 / 2 : ℝ)) * c ^ (5 / 4 : ℝ) := by
  unfold bumpLambda
  simp only [show ((7 / 2 : ℝ) = 1) = False by norm_num, ite_false]
  have h1 : δ ^ (1 - 7 / 2 : ℝ) ≤ (a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-(5 / 2 : ℝ)) := by
    have := rpow_neg_le_of_le (by positivity : 0 < a₀ * c ^ (-(1 / 2 : ℝ))) hδa (by norm_num : (0 : ℝ) ≤ 5 / 2)
    convert this using 2; norm_num
  rw [rpow_scale_half ha₀ hc] at h1
  have : a₀ ^ (-(5 / 2 : ℝ)) * c ^ ((5 / 2 : ℝ) / 2) = a₀ ^ (-(5 / 2 : ℝ)) * c ^ (5 / 4 : ℝ) := by norm_num
  linarith

/-- **`physical_budget` of `FctMainHankelInputs`** from Lemma `fct:physical-budget` (`H₀ = H_*`, `C_fl = 0`):
`∃ C₀ b₂, ∀ K₁ > 0, ∃ c₀, ∀ c ≥ c₀, Re ctWbump(B_c^ε)(0) ≤ (C₀ + b₂ K₁) c^{-13/12}` for the bump `B_c^ε = physBump` of `(fct:B-physical)`.

Inputs (module docstring): `hsize` (the scales and `δ_L ≥ a₀ c^{-1/2}`, `|n_c| ≤ n_max`), `hR`, `hT` (the symbol-class facts of
Lemma 7b (b), with constants uniform in `(ε, c)`) and `hvac` (the `K₁ = 0` vacuum budget `∫B|_{K₁=0} ≤ A c^{-3/4}`: parts (a)-(d)
of `fct:physical-budget`, from `fct:comp-D` (2) and `fct:phikill` (3)).  Proved: the margin (e), the reflected term, the assembly. -/
theorem physical_budget_field {χ : ℝ → ℝ} (hχ : IsCutoff χ) {Bphys : ℝ → ℝ → ℝ → ℝ → ℝ}
    (δf sf L1f nf : ℝ → ℝ → ℝ) (K4 : ℝ) (Of : ℝ → ℝ → ℝ → ℝ)
    (hdef : ∀ ε c K1 : ℝ, Bphys ε c K1 = physBump χ (nf ε c) c (δf ε c) (sf ε c) K1 K4 (Of ε c)
      (physF (sf ε c) (L1f ε c)) (fun L => tau0 L ^ 4 * uctIfl L))
    (hsize : ∃ c₀ a₀ nmax : ℝ, 1 ≤ c₀ ∧ 0 < a₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      0 < δf ε c ∧ 3 / 2 * δf ε c ≤ 1 ∧ |sf ε c| ≤ 3 / 2 * δf ε c / 2 ∧ |L1f ε c| ≤ 3 / 2 * δf ε c / 2 ∧
        |L1f ε c - sf ε c| ≤ 3 / 2 * δf ε c ∧ (5 * π ^ 2 / 96) * c⁻¹ ^ 2 * (3 / 2 * δf ε c) ^ (-3 : ℝ) ≤ 1 ∧
        a₀ * c ^ (-(1 / 2 : ℝ)) ≤ δf ε c ∧ |nf ε c| ≤ nmax)
    (hR : ∃ (c₀ MR : ℝ) (KR : ℕ → ℝ), 0 ≤ MR ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      SymW (Ici (3 / 2 * δf ε c)) (pw MR (-1) 0) KR (fun x => Of ε c x / physF (sf ε c) (L1f ε c) x - 1))
    (hT : ∃ (c₀ MT : ℝ) (KT : ℕ → ℝ), 0 ≤ MT ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      SymW (Icc (3 / 2 * δf ε c) (6 * δf ε c)) (pw MT (-(1 / 2)) (3 / 2)) KT (fun L => tau0 L ^ 4 * uctIfl L))
    (hvac : ∃ A c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → (∫ x, Bphys ε c 0 x) ≤ A * c ^ (-(3 / 4 : ℝ))) :
    ∃ C0 b2 : ℝ, ∀ K1 : ℝ, 0 < K1 → ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      (ctWbump (Bphys ε c K1) ε c 0).re ≤ (C0 + b2 * K1) * c ^ (-(13 / 12 : ℝ)) := by
  obtain ⟨c₁, a₀, nmax, hc₁, ha₀, hsz⟩ := hsize
  obtain ⟨c₂, MR, KR, hMR, hRu⟩ := hR
  obtain ⟨c₃, MT, KT, hMT, hTu⟩ := hT
  obtain ⟨A, c₄, hvac'⟩ := hvac
  obtain ⟨Kχ, hKχ⟩ := hχ.exists_bound
  have hKχ0 : ∀ r, 0 ≤ Kχ r := fun r => (abs_nonneg _).trans (hKχ r 0)
  set KΦ : ℕ → ℝ := Kmul (fun r => Kone r + Kpow (-1) r) (Kpow (-(3 / 2))) with hKΦ
  have hKΦ0 : ∀ r, 0 ≤ KΦ r := Kmul_nonneg (fun r => add_nonneg (Kone_nonneg r) (Kpow_nonneg _ r)) (Kpow_nonneg _)
  have hKR0 : ∀ r, 0 ≤ KR r := fun r => (hRu 1 (max c₂ 1) (Or.inl rfl) (le_max_left _ _)).K_nonneg r
  set MΦ : ℝ := |uctAlphaFl| with hMΦ
  set X : ℝ := MΦ * (MR + 2) with hX
  have hX0 : 0 ≤ X := mul_nonneg (abs_nonneg _) (by linarith)
  set K0a := KpMar1 Kχ KΦ KR 0 with hK0a
  set K0b := KpMar2 Kχ KΦ KR 0 with hK0b
  obtain ⟨hK0a0, hK0b0⟩ := KpMar_nonneg hKχ0 hKΦ0 hKR0 0
  set Cm := budgetSlope K0a K0b X a₀ with hCm
  obtain ⟨Cl, hCl0, hCl⟩ := bump_laplace_decay (b := 3 / 2) (α := 7 / 2) (β := 3 / 2) (by norm_num) (by norm_num)
    (KpTot Kχ KΦ KR KT) 0
  have hn0 : 0 ≤ nmax := by
    obtain ⟨_, _, _, _, _, _, _, hn⟩ := hsz 1 (max c₁ 1) (Or.inl rfl) (le_max_left _ _)
    exact (abs_nonneg _).trans hn
  refine ⟨A + 1, nmax * Cm, fun K1 hK1 => ?_⟩
  set M0 : ℝ := MΦ * MR + |2 * K4| * MT with hM0
  have hM00 : 0 ≤ M0 := add_nonneg (mul_nonneg (abs_nonneg _) hMR) (mul_nonneg (abs_nonneg _) hMT)
  set P : ℝ := Cl * nmax * (M0 + 2 * K1 * X) with hP
  have hP0 : 0 ≤ P := mul_nonneg (mul_nonneg hCl0 hn0) (by positivity)
  obtain ⟨c₅, hc₅⟩ := Filter.eventually_atTop.mp (reflected_small hP0 ha₀)
  refine ⟨max (max (max c₁ c₂) (max c₃ c₄)) c₅, fun ε c hε hc => ?_⟩
  have hc5 : c₅ ≤ c := (le_max_right _ _).trans hc
  have hcB : max (max c₁ c₂) (max c₃ c₄) ≤ c := (le_max_left _ _).trans hc
  have hc1 : c₁ ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hcB)
  have hc2 : c₂ ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hcB)
  have hc3 : c₃ ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hcB)
  have hc4 : c₄ ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hcB)
  have hc1' : 1 ≤ c := hc₁.trans hc1
  have hc0 : 0 < c := by linarith
  obtain ⟨hδ, hδ1, hs, hL1, hLs, hsmall, hδa, hn⟩ := hsz ε c hε hc1
  have hRε := hRu ε c hε hc2
  have hTε := hTu ε c hε hc3
  have hx0 : 0 < 3 / 2 * δf ε c := by positivity
  have hFsym := physF_sym hx0 hs hL1 hLs
  have hBeq : ∀ K1' : ℝ, Bphys ε c K1' = physBump χ (nf ε c) c (δf ε c) (sf ε c) K1' K4
      (fun x => physF (sf ε c) (L1f ε c) x * (Of ε c x / physF (sf ε c) (L1f ε c) x))
      (physF (sf ε c) (L1f ε c)) (fun L => tau0 L ^ 4 * uctIfl L) := fun K1' => by
    rw [hdef, physBump_eq_ratio hχ hδ hs hL1]
  obtain ⟨hint, hint0, hbound⟩ := physBump_integral_le hχ hKχ (n := nf ε c) (c := c) (K1 := K1) (K4 := K4)
    (MΦ := MΦ) (MR := MR) (MT := MT) (R := fun x => Of ε c x / physF (sf ε c) (L1f ε c) x)
    hδ hδ1 hs hsmall (abs_nonneg _) hMR hMT hFsym hRε hTε
  have hprof := physBump_profile hχ hKχ (n := nf ε c) (c := c) (K1 := K1) (K4 := K4)
    (MΦ := MΦ) (MR := MR) (MT := MT) (R := fun x => Of ε c x / physF (sf ε c) (L1f ε c) x)
    hδ hs hsmall (abs_nonneg _) hMR hMT hFsym hRε hTε
  have hv : (∫ x, physBump χ (nf ε c) c (δf ε c) (sf ε c) 0 K4
      (fun x => physF (sf ε c) (L1f ε c) x * (Of ε c x / physF (sf ε c) (L1f ε c) x))
      (physF (sf ε c) (L1f ε c)) (fun L => tau0 L ^ 4 * uctIfl L) x) ≤ A * c ^ (-(3 / 4 : ℝ)) := by
    have := hvac' ε c hε hc4
    rwa [hBeq 0] at this
  -- the scale bounds
  have hδlow : (3 * a₀ / 2) * c ^ (-(1 / 2 : ℝ)) ≤ 3 / 2 * δf ε c := by
    have := mul_le_mul_of_nonneg_left hδa (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  have hylow : 0 < (3 * a₀ / 2) * c ^ (-(1 / 2 : ℝ)) := by positivity
  have hY1 : (3 / 2 * δf ε c) ^ (-(5 / 2 : ℝ)) ≤ (3 * a₀ / 2) ^ (-(5 / 2 : ℝ)) * c ^ (5 / 4 : ℝ) := by
    refine (rpow_neg_le_of_le hylow hδlow (by norm_num)).trans (le_of_eq ?_)
    rw [rpow_scale_half (by positivity) hc0]; norm_num
  have hY2 : (3 / 2 * δf ε c) ^ (-(1 / 2 : ℝ)) ≤ (3 * a₀ / 2) ^ (-(1 / 2 : ℝ)) * c ^ (1 / 4 : ℝ) := by
    refine (rpow_neg_le_of_le hylow hδlow (by norm_num)).trans (le_of_eq ?_)
    rw [rpow_scale_half (by positivity) hc0]; norm_num
  have hcc1 : c⁻¹ ^ 2 * c ^ (5 / 4 : ℝ) = c ^ (-(3 / 4 : ℝ)) := by
    rw [show c⁻¹ ^ 2 = c ^ (-(2 : ℝ)) by rw [Real.rpow_neg hc0.le, Real.rpow_two]; simp, ← Real.rpow_add hc0]; norm_num
  have hcc2 : c⁻¹ * c ^ (1 / 4 : ℝ) = c ^ (-(3 / 4 : ℝ)) := by
    rw [show c⁻¹ = c ^ (-(1 : ℝ)) by rw [Real.rpow_neg hc0.le, Real.rpow_one], ← Real.rpow_add hc0]; norm_num
  have hZ1 : 0 ≤ (3 * a₀ / 2) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hZ2 : 0 ≤ (3 * a₀ / 2) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hcp : 0 ≤ c ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hc0.le _
  -- margin: `∫ B_{K₁} ≤ (A + n_max C_m K₁) c^{-3/4}`
  have hmar : (∫ x, physBump χ (nf ε c) c (δf ε c) (sf ε c) K1 K4
      (fun x => physF (sf ε c) (L1f ε c) x * (Of ε c x / physF (sf ε c) (L1f ε c) x))
      (physF (sf ε c) (L1f ε c)) (fun L => tau0 L ^ 4 * uctIfl L) x) ≤
        A * c ^ (-(3 / 4 : ℝ)) + nmax * Cm * K1 * c ^ (-(3 / 4 : ℝ)) := by
    refine hbound.trans ?_
    have habs1 : |K1 * c⁻¹ ^ 2| = K1 * c⁻¹ ^ 2 := abs_of_nonneg (by positivity)
    have habs2 : |K1 * c⁻¹| = K1 * c⁻¹ := abs_of_nonneg (by positivity)
    rw [habs1, habs2]
    have t1 : 2 * K0a * (K1 * c⁻¹ ^ 2 * X) * (3 / 2 * δf ε c) ^ (-(5 / 2 : ℝ)) / (5 / 2) ≤
        2 * K0a * (K1 * c⁻¹ ^ 2 * X) * ((3 * a₀ / 2) ^ (-(5 / 2 : ℝ)) * c ^ (5 / 4 : ℝ)) / (5 / 2) := by
      gcongr
    have t2 : 2 * K0b * (K1 * c⁻¹ * X) * (3 / 2 * δf ε c) ^ (-(1 / 2 : ℝ)) / (1 / 2) ≤
        2 * K0b * (K1 * c⁻¹ * X) * ((3 * a₀ / 2) ^ (-(1 / 2 : ℝ)) * c ^ (1 / 4 : ℝ)) / (1 / 2) := by
      gcongr
    have e : 2 * K0a * (K1 * c⁻¹ ^ 2 * X) * ((3 * a₀ / 2) ^ (-(5 / 2 : ℝ)) * c ^ (5 / 4 : ℝ)) / (5 / 2) +
        2 * K0b * (K1 * c⁻¹ * X) * ((3 * a₀ / 2) ^ (-(1 / 2 : ℝ)) * c ^ (1 / 4 : ℝ)) / (1 / 2) =
        Cm * K1 * c ^ (-(3 / 4 : ℝ)) := by
      rw [hCm, budgetSlope]
      linear_combination (2 * K0a * X * K1 * (3 * a₀ / 2) ^ (-(5 / 2 : ℝ)) / (5 / 2)) * hcc1 +
        (2 * K0b * X * K1 * (3 * a₀ / 2) ^ (-(1 / 2 : ℝ)) / (1 / 2)) * hcc2
    have hnn : |nf ε c| ≤ nmax := hn
    have hsum : 2 * K0a * (K1 * c⁻¹ ^ 2 * X) * (3 / 2 * δf ε c) ^ (-(5 / 2 : ℝ)) / (5 / 2) +
        2 * K0b * (K1 * c⁻¹ * X) * (3 / 2 * δf ε c) ^ (-(1 / 2 : ℝ)) / (1 / 2) ≤ Cm * K1 * c ^ (-(3 / 4 : ℝ)) := by
      linarith
    have hCm0 : 0 ≤ Cm * K1 * c ^ (-(3 / 4 : ℝ)) := by
      have : 0 ≤ Cm := by
        rw [hCm, budgetSlope]; positivity
      positivity
    calc _ ≤ A * c ^ (-(3 / 4 : ℝ)) + |nf ε c| * (Cm * K1 * c ^ (-(3 / 4 : ℝ))) := by
          have := mul_le_mul_of_nonneg_left hsum (abs_nonneg (nf ε c))
          linarith
      _ ≤ A * c ^ (-(3 / 4 : ℝ)) + nmax * (Cm * K1 * c ^ (-(3 / 4 : ℝ))) := by
          have := mul_le_mul_of_nonneg_right hnn hCm0
          linarith
      _ = _ := by ring
  -- the reflected term
  have hLap : ‖bumpLaplace (physBump χ (nf ε c) c (δf ε c) (sf ε c) K1 K4
      (fun x => physF (sf ε c) (L1f ε c) x * (Of ε c x / physF (sf ε c) (L1f ε c) x))
      (physF (sf ε c) (L1f ε c)) (fun L => tau0 L ^ 4 * uctIfl L)) (c : ℂ)‖ ≤ c ^ (-(3 / 4 : ℝ)) := by
    have hM0' : 0 ≤ |nf ε c| * (MΦ * MR + |K1 * c⁻¹ ^ 2| * (MΦ * (MR + 2)) + |K1 * c⁻¹| * (MΦ * (MR + 2)) + |2 * K4| * MT) :=
      mul_nonneg (abs_nonneg _) (by positivity)
    have h := hCl _ (δf ε c) _ c 1 0 hδ (by linarith) (by linarith) hM0' hc0 zero_le_one hprof
    have ec : ((c : ℂ) * (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) = (c : ℂ) := by simp
    rw [ec] at h
    simp only [abs_zero, mul_zero, add_zero, pow_zero, div_one] at h
    refine h.trans ?_
    -- `C M Λ e^{-3cδ/2} ≤ c^{-3/4}`
    have hΛ := lambda_le ha₀ hc0 hδa
    have hexp := exp_le_of_delta hc0 hδa
    have hMle := Mbound (n := nf ε c) (nmax := nmax) (c := c) (K1 := K1) (A0 := MΦ * MR) (B0 := |2 * K4| * MT) (X := MΦ * (MR + 2))
      hc1' hK1.le hX0 hn (mul_nonneg (abs_nonneg _) hMR) (mul_nonneg (abs_nonneg _) hMT)
    have hΛ0 : 0 ≤ bumpLambda (7 / 2) (δf ε c) :=
      (zero_le_one).trans (one_le_bumpLambda hδ (by linarith))
    have hcs := hc₅ c hc5
    have key : Cl * (|nf ε c| * (MΦ * MR + |K1 * c⁻¹ ^ 2| * (MΦ * (MR + 2)) + |K1 * c⁻¹| * (MΦ * (MR + 2)) + |2 * K4| * MT)) *
        bumpLambda (7 / 2) (δf ε c) * Real.exp (-(3 / 2 * c * 1 * δf ε c)) ≤
        P * (1 + a₀ ^ (-(5 / 2 : ℝ)) * c ^ (5 / 4 : ℝ)) * Real.exp (-(3 * a₀ / 2) * Real.sqrt c) := by
      have hMP : Cl * (|nf ε c| * (MΦ * MR + |K1 * c⁻¹ ^ 2| * (MΦ * (MR + 2)) + |K1 * c⁻¹| * (MΦ * (MR + 2)) + |2 * K4| * MT)) ≤ P :=
        by have := mul_le_mul_of_nonneg_left hMle hCl0; rw [hP]; linarith
      calc _ ≤ P * bumpLambda (7 / 2) (δf ε c) * Real.exp (-(3 / 2 * c * 1 * δf ε c)) := by
            gcongr
        _ ≤ P * (1 + a₀ ^ (-(5 / 2 : ℝ)) * c ^ (5 / 4 : ℝ)) * Real.exp (-(3 / 2 * c * 1 * δf ε c)) := by
            gcongr
        _ ≤ _ := by gcongr
    refine key.trans ?_
    -- `c^{3/4}` times the left side is `≤ 1`
    have e3 : c ^ (3 / 4 : ℝ) * (P * (1 + a₀ ^ (-(5 / 2 : ℝ)) * c ^ (5 / 4 : ℝ)) * Real.exp (-(3 * a₀ / 2) * Real.sqrt c)) =
        P * (c ^ (3 / 4 : ℝ) + a₀ ^ (-(5 / 2 : ℝ)) * c ^ (2 : ℝ)) * Real.exp (-(3 * a₀ / 2) * Real.sqrt c) := by
      have : c ^ (3 / 4 : ℝ) * c ^ (5 / 4 : ℝ) = c ^ (2 : ℝ) := by
        rw [← Real.rpow_add hc0]; norm_num
      linear_combination (P * a₀ ^ (-(5 / 2 : ℝ)) * Real.exp (-(3 * a₀ / 2) * Real.sqrt c)) * this
    have hcc : c ^ (-(3 / 4 : ℝ)) * c ^ (3 / 4 : ℝ) = 1 := by
      rw [← Real.rpow_add hc0]; norm_num
    have hpos : 0 < c ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos hc0 _
    calc _ = c ^ (-(3 / 4 : ℝ)) * (c ^ (3 / 4 : ℝ) * (P * (1 + a₀ ^ (-(5 / 2 : ℝ)) * c ^ (5 / 4 : ℝ)) *
            Real.exp (-(3 * a₀ / 2) * Real.sqrt c))) := by rw [← mul_assoc, hcc, one_mul]
      _ ≤ c ^ (-(3 / 4 : ℝ)) * 1 := by
          rw [e3]; exact mul_le_mul_of_nonneg_left hcs hpos.le
      _ = _ := mul_one _
  -- assembly
  have hre := ctWbump_zero_re_le (B := Bphys ε c K1) (c := c) (ε := ε) hc0 hε
  rw [hBeq K1] at hre ⊢
  have hcm : c ^ (-(1 / 3 : ℝ)) * c ^ (-(3 / 4 : ℝ)) = c ^ (-(13 / 12 : ℝ)) := by
    rw [← Real.rpow_add hc0]; norm_num
  have hc13 : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
  calc _ ≤ _ := hre
    _ ≤ c ^ (-(1 / 3 : ℝ)) * (A * c ^ (-(3 / 4 : ℝ)) + nmax * Cm * K1 * c ^ (-(3 / 4 : ℝ))) +
          c ^ (-(1 / 3 : ℝ)) * c ^ (-(3 / 4 : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hmar hc13
        have := mul_le_mul_of_nonneg_left hLap hc13
        linarith
    _ = _ := by rw [hcm.symm]; ring

/-- **The fields `bump_profile` and `physical_budget` of `FctMainHankelInputs`**, for an `I.Bphys` that is the bump `(fct:B-physical)`
(`hdef`), from `fct:bump-sym-check` and `fct:physical-budget`; the conclusions are literally the types of the two fields.
Inputs: `hsize`, `hR`, `hT` (the instantiated `fct:comp-D` / warp datum, uniform in `(ε, c)`) and `hvac` (the `K₁ = 0` vacuum budget,
`fct:physical-budget` (a)-(d)). -/
theorem fctMainHankel_bump_fields {χ : ℝ → ℝ} (hχ : IsCutoff χ) (I : FctMainHankelInputs)
    (δf sf L1f nf : ℝ → ℝ → ℝ) (K4 : ℝ) (Of : ℝ → ℝ → ℝ → ℝ)
    (hdef : ∀ ε c K1 : ℝ, I.Bphys ε c K1 = physBump χ (nf ε c) c (δf ε c) (sf ε c) K1 K4 (Of ε c)
      (physF (sf ε c) (L1f ε c)) (fun L => tau0 L ^ 4 * uctIfl L))
    (hsize : ∃ c₀ a₀ nmax : ℝ, 1 ≤ c₀ ∧ 0 < a₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      0 < δf ε c ∧ 3 / 2 * δf ε c ≤ 1 ∧ |sf ε c| ≤ 3 / 2 * δf ε c / 2 ∧ |L1f ε c| ≤ 3 / 2 * δf ε c / 2 ∧
        |L1f ε c - sf ε c| ≤ 3 / 2 * δf ε c ∧ (5 * π ^ 2 / 96) * c⁻¹ ^ 2 * (3 / 2 * δf ε c) ^ (-3 : ℝ) ≤ 1 ∧
        a₀ * c ^ (-(1 / 2 : ℝ)) ≤ δf ε c ∧ |nf ε c| ≤ nmax)
    (hR : ∃ (c₀ MR : ℝ) (KR : ℕ → ℝ), 0 ≤ MR ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      SymW (Ici (3 / 2 * δf ε c)) (pw MR (-1) 0) KR (fun x => Of ε c x / physF (sf ε c) (L1f ε c) x - 1))
    (hT : ∃ (c₀ MT : ℝ) (KT : ℕ → ℝ), 0 ≤ MT ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      SymW (Icc (3 / 2 * δf ε c) (6 * δf ε c)) (pw MT (-(1 / 2)) (3 / 2)) KT (fun L => tau0 L ^ 4 * uctIfl L))
    (hvac : ∃ A c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → (∫ x, I.Bphys ε c 0 x) ≤ A * c ^ (-(3 / 4 : ℝ))) :
    type_of% I.bump_profile ∧ type_of% I.physical_budget := by
  refine ⟨?_, physical_budget_field hχ δf sf L1f nf K4 Of hdef hsize hR hT hvac⟩
  obtain ⟨c₁, a₀, nmax, _, _, hsz⟩ := hsize
  obtain ⟨c₂, MR, KR, hMR, hRu⟩ := hR
  obtain ⟨c₃, MT, KT, hMT, hTu⟩ := hT
  refine bump_profile_field hχ δf sf L1f nf K4 Of hdef ⟨c₁, fun ε c hε hc => ?_⟩ ⟨c₂, fun ε c hε hc => ⟨MR, KR, hMR, hRu ε c hε hc⟩⟩
    ⟨c₃, fun ε c hε hc => ⟨MT, KT, hMT, hTu ε c hε hc⟩⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, _, _⟩ := hsz ε c hε hc
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- info: 'FormalResearch.SignUncertainty.FctSym.bump_profile_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_profile_field

/-- info: 'FormalResearch.SignUncertainty.FctSym.physical_budget_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physical_budget_field

/-- info: 'FormalResearch.SignUncertainty.FctSym.fctMainHankel_bump_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctMainHankel_bump_fields

end FormalResearch.SignUncertainty.FctSym
