/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctTau0Global

/-!
# The scale-invariant logarithmic derivative `τ₀'/τ₀` of `τ₀` is a symbol on `(0, ∞)` (`fct:bump-sym-check`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (`fct:bump-sym-check`): `∂_L = m'(t)^{-1} ∂_t`, `t = τ₀(L̃)`.

With `A(t) = 1/(t m'(t)) = 1/(1 - πt/sinh πt)` one has `τ₀'/τ₀ = A ∘ τ₀` (`tau0_logDeriv_eq`).

* `tauA_symW`: `A` is a `t`-symbol of weight `max 1 t^{-2}` on `(0, ∞)`: `|t^j A^{(j)}(t)| ≤ K_j max(1, t^{-2})`
  (`t ≤ 1/8`: `A = t^{-2}/mD`, `mD` smooth positive; `t ≥ 1/8`: `A = 1/θ`, `θ = t m' ≥ c` by `theta_ge`, `θ ∈ SymW` by
  `mPrime_iter_bound`).
* `tau0_logDeriv_symbol`: `|∂_x^k (τ₀'/τ₀)(x)| ≤ A_k lam(x)^{k+1}` for all `x > 0`, with `lam x = max 1 x⁻¹` and constants
  `A_k` independent of everything (`F_j = (t^j A^{(j)}) ∘ τ₀` satisfies `F_j' = F_0 (F_{j+1} + j F_j)`, a closed system
  closed by induction on the order with `chain_step_lam`).  This is the hypothesis `ha` of `comp_scale_bound` for `f = τ₀`.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology Finset
open scoped ContDiff Real Nat

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCompD FormalResearch.CohnElkies
  FormalResearch.SignUncertainty.CtOuter

/-- The `t`-weight of `A`: `max 1 t^{-2}`. -/
noncomputable def wA (t : ℝ) : ℝ := max 1 ((t ^ 2)⁻¹)

/-- The scale `lam x = max 1 x⁻¹` of `τ₀'/τ₀ ≈ 1/(2x)` (`x ≤ 1`), `≈ 1` (`x ≥ 1`). -/
noncomputable def lamL (x : ℝ) : ℝ := max 1 x⁻¹

lemma lamL_nonneg (x : ℝ) : 0 ≤ lamL x := (zero_le_one).trans (le_max_left _ _)

lemma one_le_lamL (x : ℝ) : 1 ≤ lamL x := le_max_left _ _

/-! ### `A` as a `t`-symbol -/

lemma mPrime_symW : ∃ K : ℕ → ℝ, SymW (Ioi 0) (fun t => (1 + t)⁻¹) K mPrime := by
  choose C hC using CtMDeriv.mPrime_iter_bound
  refine ⟨fun j => |C j|, ?_⟩
  exact
  { pos := fun x hx => hx
    smooth := ⟨Ioi 0, isOpen_Ioi, subset_rfl, CtMDeriv.contDiffOn_mPrime⟩
    K_nonneg := fun j => abs_nonneg _
    w_nonneg := fun x hx => inv_nonneg.mpr (by have : 0 < x := hx; positivity)
    bound := fun j x hx => by
      have hx0 : 0 < x := hx
      have h1 := hC j x hx0
      have hpow : (1 + x) * x ^ j ≤ (1 + x) ^ (j + 1) := by
        rw [pow_succ']
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0.le (by linarith) _) (by positivity)
      calc |iteratedDeriv j mPrime x| ≤ C j / (1 + x) ^ (j + 1) := h1
        _ ≤ |C j| / ((1 + x) * x ^ j) := by
            refine div_le_div₀ (abs_nonneg _) (le_abs_self _) (by positivity) hpow
        _ = |C j| * (1 + x)⁻¹ * (x ^ j)⁻¹ := by rw [div_eq_mul_inv, mul_inv] ; ring }

lemma theta_symW_Ici : ∃ K : ℕ → ℝ, SymW (Ici (1 / 8 : ℝ)) (fun _ => 1) K (fun t => t * mPrime t) := by
  obtain ⟨K, hK⟩ := mPrime_symW
  have hid := SymW.rpow_gen (S := Ioi (0 : ℝ)) (fun x hx => hx) 1 (1 : ℝ)
  have hid' := hid.congr (U := Ioi 0) isOpen_Ioi subset_rfl (g := fun x => x) (fun x hx => by simp)
  have hmul := hid'.mul hK
  refine ⟨_, ((hmul.congr (U := Ioi 0) isOpen_Ioi subset_rfl (g := fun t => t * mPrime t) (fun x _ => rfl)).mono_set
    (fun x hx => by have : (1 / 8 : ℝ) ≤ x := hx; exact lt_of_lt_of_le (by norm_num) this)).of_le (fun x hx => ?_)
    (fun _ => le_rfl)⟩
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx)
  simp only [abs_one, Real.rpow_one, one_mul]
  rw [← div_eq_mul_inv, div_le_one (by linarith)]
  linarith

lemma tauA_symW_Ici : ∃ K : ℕ → ℝ, SymW (Ici (1 / 8 : ℝ)) (fun _ => 1) K tauA := by
  obtain ⟨K, hK⟩ := theta_symW_Ici
  have hc : 0 < (π * (1 / 8)) ^ 2 / (6 + (π * (1 / 8)) ^ 2) := by positivity
  exact ⟨_, hK.inv hc fun x hx => theta_ge_Ici hx⟩

lemma mD_symW : ∃ K : ℕ → ℝ, SymW (Ioc (0 : ℝ) (1 / 8)) (fun _ => 1) K mD := by
  choose B hB using fun j => CtMDeriv.bdd_iter_on_compact (isOpen_Ioo (a := (-1 / 4 : ℝ)) (b := 1 / 4)) contDiffOn_mD
    (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)) (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) j
  exact ⟨_, SymW.of_bdd (b := 1 / 8) (by norm_num) isOpen_Ioo
    (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) contDiffOn_mD
    (fun r x hx => hB r x ⟨hx.1.le, hx.2⟩)⟩

lemma mD_ge : ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ x ∈ Ioc (0 : ℝ) (1 / 8), m₀ ≤ mD x := by
  have hc : ContinuousOn mD (Icc (0 : ℝ) (1 / 8)) :=
    contDiffOn_mD.continuousOn.mono fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨y₁, hy₁, h₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_isMinOn ⟨0, by simp⟩ hc
  exact ⟨mD y₁, mD_pos_of_mem (abs_lt.mpr ⟨by linarith [hy₁.1], by linarith [hy₁.2]⟩),
    fun x hx => h₁ ⟨hx.1.le, hx.2⟩⟩

lemma tauA_symW_Ioc : ∃ K : ℕ → ℝ, SymW (Ioc (0 : ℝ) (1 / 8)) (fun t => (t ^ 2)⁻¹) K tauA := by
  obtain ⟨K, hK⟩ := mD_symW
  obtain ⟨m₀, hm₀, hge⟩ := mD_ge
  have hinv := hK.inv hm₀ hge
  have hrp := SymW.rpow_gen (S := Ioc (0 : ℝ) (1 / 8)) (fun x hx => hx.1) 1 (-(2 : ℝ))
  have hmul := hrp.mul hinv
  refine ⟨_, (hmul.congr (U := Ioo 0 (1 / 4)) isOpen_Ioo
    (fun x hx => ⟨hx.1, by linarith [hx.2]⟩) (g := tauA) (fun x hx => ?_)).of_le (fun x hx => ?_) (fun _ => le_rfl)⟩
  · have hx0 : 0 < x := hx.1
    have hmd := uctMderiv_eq_mul_mD hx0 hx.2
    have hmp : mPrime x = x * mD x := by rw [← uctMderiv_eq_mPrime hx0, hmd]
    have hmdp := mD_pos_of_mem (abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩ : |x| < 1 / 4)
    unfold tauA
    rw [hmp, Real.rpow_neg hx0.le, Real.rpow_two]
    simp only [one_mul]
    field_simp
  · have hx0 : 0 < x := hx.1
    simp only [abs_one, one_mul, mul_one]
    rw [Real.rpow_neg hx0.le, Real.rpow_two]

/-- **`A = 1/(t m')` is a `t`-symbol of weight `max 1 t^{-2}` on `(0, ∞)`.** -/
theorem tauA_symW : ∃ K : ℕ → ℝ, SymW (Ioi 0) wA K tauA := by
  obtain ⟨K₁, h₁⟩ := tauA_symW_Ioc
  obtain ⟨K₂, h₂⟩ := tauA_symW_Ici
  have h1 := h₁.of_le (w' := wA) (K' := K₁) (fun x hx => le_max_right _ _) (fun _ => le_rfl)
  have h2 := h₂.of_le (w' := wA) (K' := K₂) (fun x hx => le_max_left _ _) (fun _ => le_rfl)
  exact ⟨_, (h1.union h2).mono_set (fun x hx => by
    rcases le_or_gt x (1 / 8) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h.le)⟩


/-! ### `τ₀'/τ₀ = A ∘ τ₀` is a symbol in the scale `lamL` -/

lemma tau0_logDeriv_eq {x : ℝ} (hx : 0 < x) : deriv tau0 x / tau0 x = tauA (tau0 x) := by
  rw [deriv_tau0 hx]
  unfold tauA
  have := tau0_pos hx
  rw [mul_inv, div_eq_mul_inv, mul_comm]

lemma wA_tau0_le : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → wA (tau0 x) ≤ C * lamL x := by
  obtain ⟨c, hc, hsq⟩ := tau0_sq_ge
  have hT : 0 < tau0 1 := tau0_pos one_pos
  refine ⟨max (max 1 c⁻¹) (max 1 ((tau0 1 ^ 2)⁻¹)), lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_left _ _)), fun x hx => ?_⟩
  set C := max (max 1 c⁻¹) (max 1 ((tau0 1 ^ 2)⁻¹)) with hC
  have hC1 : 1 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC2 : c⁻¹ ≤ C := (le_max_right (1 : ℝ) c⁻¹).trans (le_max_left _ _)
  have hC3 : (tau0 1 ^ 2)⁻¹ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  rcases le_or_gt x 1 with h | h
  · have hl : lamL x = x⁻¹ := by
      unfold lamL; exact max_eq_right (one_le_inv_iff₀.mpr ⟨hx, h⟩)
    rw [hl]
    have h1 : (1 : ℝ) ≤ x⁻¹ := one_le_inv_iff₀.mpr ⟨hx, h⟩
    unfold wA
    refine max_le ?_ ?_
    · nlinarith
    · have := hsq x ⟨hx, h⟩
      have h2 : ((tau0 x) ^ 2)⁻¹ ≤ (c * x)⁻¹ := inv_anti₀ (by positivity) this
      calc ((tau0 x) ^ 2)⁻¹ ≤ (c * x)⁻¹ := h2
        _ = c⁻¹ * x⁻¹ := mul_inv _ _
        _ ≤ C * x⁻¹ := mul_le_mul_of_nonneg_right hC2 (inv_nonneg.mpr hx.le)
  · have hl : lamL x = 1 := by
      unfold lamL; exact max_eq_left (inv_le_one_of_one_le₀ h.le)
    rw [hl, mul_one]
    unfold wA
    refine max_le (by linarith) ?_
    have : tau0 1 ≤ tau0 x := tau0_mono one_pos h.le
    exact (inv_anti₀ (by positivity) (pow_le_pow_left₀ hT.le this 2)).trans hC3

/-- **`τ₀'/τ₀` is a symbol with the scale `lam x = max 1 x⁻¹`**: `|∂_x^k (τ₀'/τ₀)| ≤ A_k lam^{k+1}`, constants absolute. -/
theorem tau0_logDeriv_symbol : ∃ A : ℕ → ℝ, (∀ k, 0 ≤ A k) ∧
    ∀ k : ℕ, ∀ x : ℝ, 0 < x → |iteratedDeriv k (fun y => deriv tau0 y / tau0 y) x| ≤ A k * lamL x ^ (k + 1) := by
  obtain ⟨K, hK⟩ := tauA_symW
  obtain ⟨C, hC, hwC⟩ := wA_tau0_le
  obtain ⟨U, hU, hSU, hgU⟩ := hK.smooth
  have hg : ContDiffOn ℝ ∞ tauA (Ioi 0) := hgU.mono hSU
  set F := scaleF tau0 tauA with hF
  have hFs : ∀ j, ContDiffOn ℝ ∞ (F j) (Ioi 0) := fun j =>
    contDiffOn_scaleF contDiffOn_tau0 (fun x hx => tau0_pos hx) hg j
  have haU : ContDiffOn ℝ ∞ (fun y => deriv tau0 y / tau0 y) (Ioi 0) :=
    (contDiffOn_tau0.deriv_of_isOpen isOpen_Ioi (by simp)).div contDiffOn_tau0 fun y hy => (tau0_pos hy).ne'
  have hder : ∀ j, ∀ x ∈ Ioi (0 : ℝ), deriv (F j) x =
      (deriv tau0 x / tau0 x) * (F (j + 1) x + (fun j : ℕ => (j : ℝ)) j * F j x) := fun j x hx =>
    deriv_scaleF isOpen_Ioi contDiffOn_tau0 (fun x hx => tau0_pos hx) hg j hx
  -- the base bound
  have hbase : ∀ j, ∀ x ∈ Ioi (0 : ℝ), |F j x| ≤ (|K j| * C) * lamL x := by
    intro j x hx
    have hx0 : 0 < x := hx
    have := hK.bound j (tau0 x) (tau0_pos hx0)
    have hp := tau0_pos hx0
    have e : F j x = tau0 x ^ j * iteratedDeriv j tauA (tau0 x) := rfl
    rw [e, abs_mul, abs_of_pos (pow_pos hp j)]
    calc tau0 x ^ j * |iteratedDeriv j tauA (tau0 x)| ≤ tau0 x ^ j * (K j * wA (tau0 x) * ((tau0 x) ^ j)⁻¹) :=
          mul_le_mul_of_nonneg_left this (pow_nonneg hp.le _)
      _ = K j * wA (tau0 x) := by field_simp
      _ ≤ |K j| * wA (tau0 x) := mul_le_mul_of_nonneg_right (le_abs_self _) (hK.w_nonneg _ hp)
      _ ≤ |K j| * (C * lamL x) := mul_le_mul_of_nonneg_left (hwC x hx0) (abs_nonneg _)
      _ = _ := by ring
  have claim : ∀ r : ℕ, ∃ M : ℕ → ℝ, (∀ j, 0 ≤ M j) ∧ ∀ j, ∀ x : ℝ, 0 < x → ∀ i ≤ r,
      |iteratedDeriv i (F j) x| ≤ M j * lamL x * lamL x ^ i := by
    intro r
    induction r with
    | zero =>
      refine ⟨fun j => |K j| * C, fun j => by positivity, fun j x hx i hi => ?_⟩
      obtain rfl : i = 0 := by omega
      simpa using hbase j x hx
    | succ r ih =>
      obtain ⟨M, hM0, hM⟩ := ih
      have hstep : ∀ j, ∀ x : ℝ, 0 < x → |iteratedDeriv (r + 1) (F j) x| ≤
          chainStep (fun _ => M 0) (fun j : ℕ => (j : ℝ)) r M j * lamL x * 1 * lamL x ^ (r + 1) := by
        intro j x hx
        refine chain_step_lam (S := Ioi 0) (U := Ioi 0) isOpen_Ioi subset_rfl (F := F)
          (a := fun y => deriv tau0 y / tau0 y) (w := fun _ => 1) (om := lamL) (lam := lamL)
          (κ := fun j : ℕ => (j : ℝ)) (A := fun _ => M 0) (M := M) r hFs haU hder ?_ (fun _ _ => zero_le_one)
          (fun _ => hM0 0) (fun x _ => lamL_nonneg x) (fun x _ => lamL_nonneg x)
          (fun j x hx i hi => hM j x hx i hi) hM0 j hx
        intro k hk y hy
        have hy0 : 0 < y := hy
        have e : iteratedDeriv k (fun y => deriv tau0 y / tau0 y) y = iteratedDeriv k (F 0) y := by
          have hev : (fun y => deriv tau0 y / tau0 y) =ᶠ[nhds y] F 0 := by
            filter_upwards [Ioi_mem_nhds hy0] with z hz
            have hz0 : 0 < z := hz
            rw [tau0_logDeriv_eq hz0]
            simp [hF, scaleF]
          exact hev.iteratedDeriv_eq k
        rw [e]
        have := hM 0 y hy0 k hk
        calc _ ≤ M 0 * lamL y * lamL y ^ k := this
          _ = _ := by ring
      refine ⟨fun j => max (M j) (chainStep (fun _ => M 0) (fun j : ℕ => (j : ℝ)) r M j),
        fun j => (hM0 j).trans (le_max_left _ _), fun j x hx i hi => ?_⟩
      have hl0 := lamL_nonneg x
      rcases Nat.lt_or_ge i (r + 1) with hlt | hge
      · refine (hM j x hx i (by omega)).trans ?_
        have : 0 ≤ lamL x * lamL x ^ i := mul_nonneg hl0 (pow_nonneg hl0 _)
        calc M j * lamL x * lamL x ^ i = M j * (lamL x * lamL x ^ i) := by ring
          _ ≤ _ := by
            have := mul_le_mul_of_nonneg_right (le_max_left (M j) (chainStep (fun _ => M 0) (fun j : ℕ => (j : ℝ)) r M j)) this
            linarith
      · obtain rfl : i = r + 1 := by omega
        refine (hstep j x hx).trans ?_
        have : 0 ≤ lamL x * lamL x ^ (r + 1) := mul_nonneg hl0 (pow_nonneg hl0 _)
        have := mul_le_mul_of_nonneg_right (le_max_right (M j) (chainStep (fun _ => M 0) (fun j : ℕ => (j : ℝ)) r M j)) this
        linarith
  choose M hM0 hM using claim
  refine ⟨fun k => M k 0, fun k => hM0 k 0, fun k x hx => ?_⟩
  have e : iteratedDeriv k (fun y => deriv tau0 y / tau0 y) x = iteratedDeriv k (F 0) x := by
    have hev : (fun y => deriv tau0 y / tau0 y) =ᶠ[nhds x] F 0 := by
      filter_upwards [Ioi_mem_nhds hx] with z hz
      have hz0 : 0 < z := hz
      rw [tau0_logDeriv_eq hz0]
      simp [hF, scaleF]
    exact hev.iteratedDeriv_eq k
  rw [e]
  calc _ ≤ M k 0 * lamL x * lamL x ^ k := hM k 0 x hx k le_rfl
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.FctSym.tau0_logDeriv_symbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tau0_logDeriv_symbol

/-- info: 'FormalResearch.SignUncertainty.FctSym.tauA_symW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tauA_symW

end FormalResearch.SignUncertainty.FctSym
