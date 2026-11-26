/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctPhiKill
public import FormalResearch.SignUncertainty.FctSymChain
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# `φ_kill(it; a)` as a `t`-symbol (`fct:phikill` (1) in the form needed by `fct:bump-sym-check`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.4 (`fct:phikill`) (1) and Lemma FCT.7b (a), fourth item:
`|∂_t^r φ_kill(it; a)| ≤ C_r t^{8-r} a^{-8}`, `|φ_kill| ≤ C (t/a)^8` for `t ≤ a`, and `|φ_kill| ≤ C`,
`|∂_t^r φ_kill| ≤ C_r a^8 t^{-8-r}` (`r ≥ 1`) for `t ≥ a`.

For `Ψ(t) = φ_kill(it; a)` and `E = 1 - Ψ` this file proves, for the real and imaginary parts `L ∈ {Re, Im}`, with constants
`C_j` independent of `a > 0`, `t > 0`:

* `|t^j ∂_t^j L(Ψ)(t)| ≤ C_j min(1, (t/a)^8)`  (small-`t` form);
* `|t^j ∂_t^j L(E)(t)| ≤ C_j min(1, (a/t)^8)`   (large-`t` form: `φ_kill → 1`).

These are the base bounds `|f^j g^{(j)}(f)| ≤ P_j om` of `comp_scale_bound` for `f = τ₀`.

Class: proved, no hypotheses (from `fct_phikill`).
-/

@[expose] public section

open Set Filter Topology Complex
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctPhiKill

/-- Iterated derivatives of a smooth function on an open set are smooth there (any scalar field and codomain). -/
lemma contDiffOn_iteratedDeriv_gen {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : 𝕜 → F} {V : Set 𝕜} (hV : IsOpen V) (hf : ContDiffOn 𝕜 ∞ f V) (j : ℕ) :
    ContDiffOn 𝕜 ∞ (iteratedDeriv j f) V := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    have : iteratedDeriv (j + 1) f = deriv (iteratedDeriv j f) := iteratedDeriv_succ
    rw [this]
    exact ih.deriv_of_isOpen hV (by simp)

/-- A continuous `ℝ`-linear map commutes with iterated derivatives of a `ℂ`-valued smooth function. -/
lemma iteratedDeriv_clm_comp {V : Set ℝ} (hV : IsOpen V) {Ψ : ℝ → ℂ} (hΨ : ContDiffOn ℝ ∞ Ψ V) (L : ℂ →L[ℝ] ℝ)
    (j : ℕ) : ∀ t ∈ V, iteratedDeriv j (fun s => L (Ψ s)) t = L (iteratedDeriv j Ψ t) := by
  induction j with
  | zero => intro t ht; simp
  | succ j ih =>
    intro t ht
    have hev : iteratedDeriv j (fun s => L (Ψ s)) =ᶠ[nhds t] fun s => L (iteratedDeriv j Ψ s) :=
      Filter.eventually_of_mem (hV.mem_nhds ht) ih
    rw [iteratedDeriv_succ, iteratedDeriv_succ, hev.deriv_eq]
    have hd : DifferentiableAt ℝ (iteratedDeriv j Ψ) t :=
      ((contDiffOn_iteratedDeriv_gen hV hΨ j).differentiableOn (by simp)).differentiableAt (hV.mem_nhds ht)
    exact (L.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).deriv

lemma phiKill_ne {a : ℝ} (ha : 0 < a) : ∀ t : ℝ, (t : ℂ) * Complex.I ∈ {z : ℂ | z ≠ -(a : ℂ)} := by
  intro t h
  have := congrArg Complex.re h
  simp at this
  linarith

lemma contDiff_phiKill_imag {a : ℝ} (ha : 0 < a) : ContDiff ℝ ∞ (fun s : ℝ => phiKill a ((s : ℂ) * Complex.I)) := by
  have hΩ : IsOpen {z : ℂ | z ≠ -(a : ℂ)} := isOpen_ne
  have hC : ContDiffOn ℂ ∞ (phiKill a) {z : ℂ | z ≠ -(a : ℂ)} := (differentiableOn_phiPQ 8 8 a).contDiffOn hΩ
  have hh : ContDiff ℝ ∞ (fun s : ℝ => (s : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.mul contDiff_const)
  rw [contDiff_iff_contDiffAt]
  intro s
  have hat : ContDiffAt ℂ ∞ (phiKill a) ((s : ℂ) * Complex.I) :=
    hC.contDiffAt (hΩ.mem_nhds (phiKill_ne ha s))
  exact (hat.restrict_scalars ℝ).comp s hh.contDiffAt

/-- `∂_t^j φ_kill(it; a) = i^j φ_kill^{(j)}(it; a)`. -/
lemma iteratedDeriv_phiKill_imag {a : ℝ} (ha : 0 < a) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun s : ℝ => phiKill a ((s : ℂ) * Complex.I)) t =
      Complex.I ^ j * iteratedDeriv j (phiKill a) ((t : ℂ) * Complex.I) := by
  have hΩ : IsOpen {z : ℂ | z ≠ -(a : ℂ)} := isOpen_ne
  have hC : ContDiffOn ℂ ∞ (phiKill a) {z : ℂ | z ≠ -(a : ℂ)} := (differentiableOn_phiPQ 8 8 a).contDiffOn hΩ
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    have hfun : iteratedDeriv j (fun s : ℝ => phiKill a ((s : ℂ) * Complex.I)) =
        fun s : ℝ => Complex.I ^ j * iteratedDeriv j (phiKill a) ((s : ℂ) * Complex.I) := funext ih
    rw [iteratedDeriv_succ, hfun]
    have hG : HasDerivAt (iteratedDeriv j (phiKill a)) (iteratedDeriv (j + 1) (phiKill a) ((t : ℂ) * Complex.I))
        ((t : ℂ) * Complex.I) := by
      have hd := ((contDiffOn_iteratedDeriv_gen hΩ hC j).differentiableOn (by simp)).differentiableAt
        (hΩ.mem_nhds (phiKill_ne ha t))
      rw [iteratedDeriv_succ]; exact hd.hasDerivAt
    have hh : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
    have h2 := (hG.scomp t hh).const_mul (Complex.I ^ j)
    have := h2.deriv
    simp only [Function.comp_def, smul_eq_mul] at this
    rw [this]
    ring

/-- The large-`t` bound `t^j · t^{-8-j} a^8 = (a/t)^8` and the small-`t` bound `t^j · t^{8-j} a^{-8} = (t/a)^8`
for the derivatives `j ≥ 1` of `φ_kill` on the imaginary axis. -/
lemma phiKill_deriv_ge_one (j : ℕ) (hj : 1 ≤ j) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a t : ℝ), 0 < a → 0 < t →
    t ^ j * ‖iteratedDeriv j (phiKill a) ((t : ℂ) * Complex.I)‖ ≤ C * min ((t / a) ^ 8) ((a / t) ^ 8) := by
  obtain ⟨C, hC0, hC⟩ := norm_iteratedDeriv_phiPQ_le 8 8 j (by norm_num) (by norm_num) hj
  refine ⟨C, hC0, fun a t ha ht => ?_⟩
  have hz : (t : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast ht.ne') Complex.I_ne_zero
  have hre : 0 ≤ ((t : ℂ) * Complex.I).re := by simp
  have h : ‖iteratedDeriv j (phiKill a) ((t : ℂ) * Complex.I)‖ ≤ C * min (‖(t : ℂ) * Complex.I‖ ^ (((8 : ℕ) : ℤ) - (j : ℤ)) *
      a ^ (-((8 : ℕ) : ℤ))) (a ^ 8 * ‖(t : ℂ) * Complex.I‖ ^ (-(((8 + j : ℕ)) : ℤ))) := hC ha hre hz
  have hn : ‖(t : ℂ) * Complex.I‖ = t := by simp [abs_of_pos ht]
  have z1 : t ^ (((8 : ℕ) : ℤ) - (j : ℤ)) = t ^ 8 / t ^ j := by rw [zpow_sub₀ ht.ne', zpow_natCast, zpow_natCast]
  have z2 : a ^ (-((8 : ℕ) : ℤ)) = (a ^ 8)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have z3 : t ^ (-(((8 + j : ℕ)) : ℤ)) = (t ^ (8 + j))⁻¹ := by rw [zpow_neg, zpow_natCast]
  rw [hn, z1, z2, z3] at h
  have e1 : t ^ j * (t ^ 8 / t ^ j * (a ^ 8)⁻¹) = (t / a) ^ 8 := by
    have := pow_pos ht j
    rw [div_pow]; field_simp
  have e2 : t ^ j * (a ^ 8 * (t ^ (8 + j))⁻¹) = (a / t) ^ 8 := by
    have := pow_pos ht j
    rw [div_pow, pow_add]; field_simp
  calc t ^ j * ‖iteratedDeriv j (phiKill a) ((t : ℂ) * Complex.I)‖
      ≤ t ^ j * (C * min (t ^ 8 / t ^ j * (a ^ 8)⁻¹) (a ^ 8 * (t ^ (8 + j))⁻¹)) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg ht.le _)
    _ = C * min (t ^ j * (t ^ 8 / t ^ j * (a ^ 8)⁻¹)) (t ^ j * (a ^ 8 * (t ^ (8 + j))⁻¹)) := by
        rw [← mul_min_of_nonneg _ _ (pow_nonneg ht.le j)]; ring
    _ = _ := by rw [e1, e2]

lemma min_pair_le_left (x y : ℝ) (hxy : x * y = 1) : min x y ≤ min 1 x := by
  rcases le_total x 1 with h | h
  · rw [min_eq_right h]; exact min_le_left _ _
  · have hy : y ≤ 1 := by
      by_contra hy; push Not at hy; nlinarith
    rw [min_eq_left (show 1 ≤ x from h)]
    exact (min_le_right _ _).trans hy

lemma min_pair_le_right (x y : ℝ) (hxy : x * y = 1) : min x y ≤ min 1 y := by
  rw [min_comm x y]; exact min_pair_le_left y x (by rw [mul_comm]; exact hxy)

/-- **`φ_kill(it; a)` as a `t`-symbol**, for the real and imaginary parts `L` of `Ψ(t) = φ_kill(it; a)` and of `1 - Ψ`. -/
theorem phiKill_tsymbol : ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ (a t : ℝ), 0 < a → 0 < t → ∀ (L : ℂ →L[ℝ] ℝ),
    (∀ z, |L z| ≤ ‖z‖) → ∀ j : ℕ,
    |t ^ j * iteratedDeriv j (fun s : ℝ => L (phiKill a ((s : ℂ) * Complex.I))) t| ≤ C j * min 1 ((t / a) ^ 8) ∧
    |t ^ j * iteratedDeriv j (fun s : ℝ => L (1 - phiKill a ((s : ℂ) * Complex.I))) t| ≤ C j * min 1 ((a / t) ^ 8) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ : ∃ C ≥ (0 : ℝ), ∀ {a : ℝ} {z : ℂ}, 0 < a → 0 ≤ z.re →
      ‖phiKill a z‖ ≤ C * min ((‖z‖ / a) ^ 8) 1 := (fct_phikill).2.2.2.2.2.1
  obtain ⟨C₂, hC₂0, hC₂⟩ : ∃ C ≥ (0 : ℝ), ∀ {a : ℝ} {z : ℂ}, 0 < a → 0 ≤ z.re →
      ‖1 - phiKill a z‖ ≤ C ∧ (z ≠ 0 → ‖1 - phiKill a z‖ ≤ C * (a / ‖z‖) ^ 8) :=
    (fct_phikill).2.2.2.2.2.2.1
  have hD : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (a t : ℝ), 0 < a → 0 < t → 1 ≤ j →
      t ^ j * ‖iteratedDeriv j (phiKill a) ((t : ℂ) * Complex.I)‖ ≤ C * min ((t / a) ^ 8) ((a / t) ^ 8) := by
    intro j
    by_cases hj : 1 ≤ j
    · obtain ⟨C, hC0, hC⟩ := phiKill_deriv_ge_one j hj
      exact ⟨C, hC0, fun a t ha ht _ => hC a t ha ht⟩
    · exact ⟨0, le_rfl, fun _ _ _ _ h => absurd h hj⟩
  choose D hD0 hD using hD
  refine ⟨fun j => max (D j) (max C₁ C₂), fun j => (hD0 j).trans (le_max_left _ _), ?_⟩
  intro a t ha ht L hL j
  have hz0 : (0 : ℂ).re = 0 := rfl
  have hre : 0 ≤ ((t : ℂ) * Complex.I).re := by simp
  have hn : ‖(t : ℂ) * Complex.I‖ = t := by simp [abs_of_pos ht]
  have hcd := contDiff_phiKill_imag ha
  have hV : IsOpen (univ : Set ℝ) := isOpen_univ
  have hcdE : ContDiffOn ℝ ∞ (fun s : ℝ => 1 - phiKill a ((s : ℂ) * Complex.I)) univ :=
    (contDiffOn_const.sub hcd.contDiffOn)
  have hinv1 : (t / a) ^ 8 * (a / t) ^ 8 = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm t a, div_self (by positivity)]; simp
  have hm1 : min ((t / a) ^ 8) ((a / t) ^ 8) ≤ min 1 ((t / a) ^ 8) := min_pair_le_left _ _ hinv1
  have hm2 : min ((t / a) ^ 8) ((a / t) ^ 8) ≤ min 1 ((a / t) ^ 8) := min_pair_le_right _ _ hinv1
  have hCj : 0 ≤ max (D j) (max C₁ C₂) := (hD0 j).trans (le_max_left _ _)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- order zero
    simp only [pow_zero, one_mul, iteratedDeriv_zero]
    constructor
    · have h1 := hC₁ ha hre
      rw [hn] at h1
      refine (hL _).trans (h1.trans ?_)
      rw [min_comm]
      exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (le_min zero_le_one (by positivity))
    · obtain ⟨h2a, h2b⟩ := hC₂ ha hre
      have h3 := h2b (mul_ne_zero (by exact_mod_cast ht.ne') Complex.I_ne_zero)
      rw [hn] at h3
      refine (hL _).trans ?_
      calc ‖1 - phiKill a ((t : ℂ) * Complex.I)‖ ≤ C₂ * min 1 ((a / t) ^ 8) := by
            rcases le_total 1 ((a / t) ^ 8) with h | h
            · rw [min_eq_left h, mul_one]; exact h2a
            · rw [min_eq_right h]; exact h3
        _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (le_min zero_le_one (by positivity))
  · have hj1 : 1 ≤ j := hj
    have hDj := hD j a t ha ht hj1
    have hG : ‖iteratedDeriv j (fun s : ℝ => phiKill a ((s : ℂ) * Complex.I)) t‖ =
        ‖iteratedDeriv j (phiKill a) ((t : ℂ) * Complex.I)‖ := by
      rw [iteratedDeriv_phiKill_imag ha j t, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
    have key : ∀ (G : ℝ → ℂ) (hG : ContDiffOn ℝ ∞ G univ),
        ‖iteratedDeriv j G t‖ = ‖iteratedDeriv j (fun s : ℝ => phiKill a ((s : ℂ) * Complex.I)) t‖ →
        |t ^ j * iteratedDeriv j (fun s => L (G s)) t| ≤ D j * min ((t / a) ^ 8) ((a / t) ^ 8) := by
      intro G hGs hGn
      rw [iteratedDeriv_clm_comp hV hGs L j t (mem_univ _), abs_mul, abs_of_pos (pow_pos ht j)]
      calc t ^ j * |L (iteratedDeriv j G t)| ≤ t ^ j * ‖iteratedDeriv j G t‖ :=
            mul_le_mul_of_nonneg_left (hL _) (pow_nonneg ht.le _)
        _ = t ^ j * ‖iteratedDeriv j (phiKill a) ((t : ℂ) * Complex.I)‖ := by rw [hGn, hG]
        _ ≤ _ := hDj
    constructor
    · have := key _ hcd.contDiffOn (by rfl)
      refine this.trans ?_
      calc D j * min ((t / a) ^ 8) ((a / t) ^ 8) ≤ D j * min 1 ((t / a) ^ 8) := mul_le_mul_of_nonneg_left hm1 (hD0 j)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (le_min zero_le_one (by positivity))
    · have := key _ hcdE (by
        rw [iteratedDeriv_const_sub hj, iteratedDeriv_neg, norm_neg])
      refine this.trans ?_
      calc D j * min ((t / a) ^ 8) ((a / t) ^ 8) ≤ D j * min 1 ((a / t) ^ 8) := mul_le_mul_of_nonneg_left hm2 (hD0 j)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (le_min zero_le_one (by positivity))

end FormalResearch.SignUncertainty.FctSym
