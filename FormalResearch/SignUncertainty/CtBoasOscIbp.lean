/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib

/-!
# Arbitrary-order non-stationary oscillatory IBP for compactly supported smooth amplitudes (`ct:boas` Step 4)

Helper module for `CtBoasHarmonics`:
- `invDerivConst`, `inv_deriv_iteratedDeriv_bound`: inductive symbol bound for `q(x) = φ(x)⁻¹` via Leibniz on
  `q · φ = 1` (no quotient rule);
- `oscConst`, `oscOp_norm_bound`: inductive derivative bound for iterated `u ↦ -(q u)'`;
- `osc_ibp_r`: `r`-fold integration by parts for `∫ x in a..b, u(x) * exp(i θ(x))` when
  `supp u ⊆ Icc a' b' ⊂ Ioo a b`, giving `‖∫ x in a..b, u(x) * exp(i θ(x))‖ ≤ (b - a) * C_D * μ⁻ʳ * M_u * Eʳ`;
- `osc_ibp_linear_two`: direct 2-fold IBP for `∫ x in a..b, u(x) * exp(i w x)` when `supp u ⊆ Icc a' b' ⊂ Ioo a b`
  and `w ≠ 0`, giving `‖∫ x in a..b, u(x) * exp(i w x)‖ ≤ (b - a) * M₂ / w²`.

Class: proved, unconditional.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff

namespace FormalResearch.SignUncertainty

private noncomputable def oscOp (q : ℝ → ℂ) : ℕ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0, u => u
  | r + 1, u => fun x => -deriv (fun y => q y * oscOp q r u y) x

noncomputable def invDerivConst (B : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => ∑ i : Fin (k + 1), (Nat.choose (k + 1) i : ℝ) * invDerivConst B i * B (k + 1 - i)

lemma invDerivConst_nonneg {B : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (m : ℕ) : 0 ≤ invDerivConst B m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => simp [invDerivConst]
    | succ k =>
      unfold invDerivConst
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ih i i.isLt)) (hB _)

noncomputable def oscConst (C_q : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | k + 1, m => ∑ i ∈ range (m + 2), (Nat.choose (m + 1) i : ℝ) * C_q i * oscConst C_q k (m + 1 - i)

lemma oscConst_nonneg {C_q : ℕ → ℝ} (hCq : ∀ j, 0 ≤ C_q j) (k m : ℕ) :
    0 ≤ oscConst C_q k m := by
  induction k generalizing m with
  | zero => simp [oscConst]
  | succ k ih =>
    unfold oscConst
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCq i)) (ih (m + 1 - i))

private lemma oscOp_support {q : ℝ → ℂ} {a' b' : ℝ} {u : ℝ → ℂ}
    (hsupp : ∀ x ∉ Icc a' b', u x = 0) (r : ℕ) :
    ∀ x ∉ Icc a' b', oscOp q r u x = 0 := by
  induction r with
  | zero => exact hsupp
  | succ r ih =>
    intro x hx
    unfold oscOp
    have hopen : IsOpen ((Icc a' b')ᶜ) := isClosed_Icc.isOpen_compl
    have hev : (fun y => q y * oscOp q r u y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      rw [ih y hy, mul_zero]
    rw [hev.deriv_eq, deriv_const, neg_zero]

private lemma iteratedDeriv_ofReal_eq (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => ((g y : ℝ) : ℂ)) x = ((iteratedDeriv n g x : ℝ) : ℂ) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hfun : iteratedDeriv n (fun y => ((g y : ℝ) : ℂ)) = fun y => ((iteratedDeriv n g y : ℝ) : ℂ) :=
      funext ih
    calc iteratedDeriv (n + 1) (fun y => ((g y : ℝ) : ℂ)) x
        = deriv (iteratedDeriv n (fun y => ((g y : ℝ) : ℂ))) x := by rw [iteratedDeriv_succ]
      _ = deriv (fun y => ((iteratedDeriv n g y : ℝ) : ℂ)) x := by rw [hfun]
      _ = ((deriv (iteratedDeriv n g) x : ℝ) : ℂ) := by
          by_cases hd : DifferentiableAt ℝ (iteratedDeriv n g) x
          · exact ((hd.hasDerivAt).ofReal_comp).deriv
          · have hnd : ¬DifferentiableAt ℝ (fun y : ℝ => ((iteratedDeriv n g y : ℝ) : ℂ)) x := fun hc =>
              hd (Complex.reCLM.differentiableAt.comp x hc)
            rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd, Complex.ofReal_zero]
      _ = ((iteratedDeriv (n + 1) g x : ℝ) : ℂ) := by rw [← iteratedDeriv_succ]

/-- Symbol bound for `φ⁻¹` from `φ` via Leibniz on `q · φ = 1` (no quotient rule). -/
lemma inv_deriv_iteratedDeriv_bound {n : ℕ} {B : ℕ → ℝ} (hB0 : ∀ j, 0 ≤ B j)
    {a₀ b₀ μ Λ : ℝ} {φ : ℝ → ℝ} (hμ : 0 < μ) (hΛ : 1 ≤ Λ)
    (hφ : ContDiffOn ℝ n φ (Ioo a₀ b₀)) (hφ_lb : ∀ x ∈ Ioo a₀ b₀, μ ≤ |φ x|)
    (hφ_sym : ∀ j : ℕ, 1 ≤ j → j ≤ n → ∀ x ∈ Ioo a₀ b₀, |iteratedDeriv j φ x| ≤ B j * |φ x| * Λ ^ j) :
    ContDiffOn ℝ n (fun x => (φ x)⁻¹) (Ioo a₀ b₀) ∧
      ∀ m ≤ n, ∀ x ∈ Ioo a₀ b₀, |iteratedDeriv m (fun x => (φ x)⁻¹) x| ≤ invDerivConst B m * μ⁻¹ * Λ ^ m := by
  have hne : ∀ x ∈ Ioo a₀ b₀, φ x ≠ 0 := fun x hx => abs_pos.1 (lt_of_lt_of_le hμ (hφ_lb x hx))
  have hcd : ContDiffOn ℝ n (fun x => (φ x)⁻¹) (Ioo a₀ b₀) := hφ.inv hne
  refine ⟨hcd, ?_⟩
  intro m hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro x hx
    cases m with
    | zero =>
      simp only [iteratedDeriv_zero, invDerivConst, pow_zero, mul_one, one_mul, abs_inv]
      exact inv_anti₀ hμ (hφ_lb x hx)
    | succ k =>
      have hk1_le : k + 1 ≤ n := hm
      have hcd_q : ContDiffAt ℝ (k + 1) (fun y => (φ y)⁻¹) x :=
        (hcd.contDiffAt (isOpen_Ioo.mem_nhds hx)).of_le (by exact_mod_cast hk1_le)
      have hcd_φ : ContDiffAt ℝ (k + 1) φ x :=
        (hφ.contDiffAt (isOpen_Ioo.mem_nhds hx)).of_le (by exact_mod_cast hk1_le)
      have hev : (fun y => (φ y)⁻¹ * φ y) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        exact inv_mul_cancel₀ (hne y hy)
      have hzero : iteratedDeriv (k + 1) (fun y => (φ y)⁻¹ * φ y) x = 0 := by
        rw [hev.iteratedDeriv_eq (k + 1), iteratedDeriv_const]
        simp
      have hleib := iteratedDeriv_fun_mul (x := x) (n := k + 1) hcd_q hcd_φ
      rw [hzero, Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, Nat.cast_one, one_mul,
        iteratedDeriv_zero] at hleib
      have hq_eq : iteratedDeriv (k + 1) (fun y => (φ y)⁻¹) x =
          -(φ x)⁻¹ * ∑ i ∈ range (k + 1), (Nat.choose (k + 1) i : ℝ) *
            iteratedDeriv i (fun y => (φ y)⁻¹) x * iteratedDeriv (k + 1 - i) φ x := by
        have h1 : iteratedDeriv (k + 1) (fun y => (φ y)⁻¹) x * φ x =
            -(∑ i ∈ range (k + 1), (Nat.choose (k + 1) i : ℝ) *
              iteratedDeriv i (fun y => (φ y)⁻¹) x * iteratedDeriv (k + 1 - i) φ x) := by
          linarith
        calc iteratedDeriv (k + 1) (fun y => (φ y)⁻¹) x
            = (iteratedDeriv (k + 1) (fun y => (φ y)⁻¹) x * φ x) * (φ x)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ (hne x hx), mul_one]
          _ = _ := by rw [h1]; ring
      rw [hq_eq, abs_mul, abs_neg, abs_inv]
      refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 (abs_nonneg _))).trans ?_
      rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
      simp only [invDerivConst, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      have hi_lt : (i : ℕ) < k + 1 := i.isLt
      have hi_le : (i : ℕ) ≤ n := le_trans hi_lt.le hk1_le
      have hsub1 : 1 ≤ k + 1 - (i : ℕ) := by omega
      have hsubn : k + 1 - (i : ℕ) ≤ n := by omega
      have h1 := ih i hi_lt hi_le x hx
      have h2 := hφ_sym (k + 1 - i) hsub1 hsubn x hx
      have hCq_nn := invDerivConst_nonneg hB0 i
      have hpow : Λ ^ (i : ℕ) * Λ ^ (k + 1 - (i : ℕ)) = Λ ^ (k + 1) := by
        rw [← pow_add]; congr 1; omega
      have hcanc : |φ x|⁻¹ * |φ x| = 1 := inv_mul_cancel₀ (abs_pos.2 (hne x hx)).ne'
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ Nat.choose (k + 1) i)]
      calc |φ x|⁻¹ * ((Nat.choose (k + 1) i : ℝ) * |iteratedDeriv i (fun y => (φ y)⁻¹) x| *
              |iteratedDeriv (k + 1 - i) φ x|)
          ≤ |φ x|⁻¹ * ((Nat.choose (k + 1) i : ℝ) * (invDerivConst B i * μ⁻¹ * Λ ^ (i : ℕ)) *
              (B (k + 1 - i) * |φ x| * Λ ^ (k + 1 - (i : ℕ)))) := by
            gcongr
        _ = (Nat.choose (k + 1) i : ℝ) * invDerivConst B i * B (k + 1 - i) *
              (|φ x|⁻¹ * |φ x|) * μ⁻¹ * (Λ ^ (i : ℕ) * Λ ^ (k + 1 - (i : ℕ))) := by ring
        _ = (Nat.choose (k + 1) i : ℝ) * invDerivConst B i * B (k + 1 - i) * μ⁻¹ * Λ ^ (k + 1) := by
            rw [hcanc, mul_one, hpow]

private lemma oscOp_norm_bound {r : ℕ} {B : ℕ → ℝ} (hB0 : ∀ j, 0 ≤ B j)
    {a₀ b₀ a b μ Λ M_u E : ℝ} {φ : ℝ → ℝ} {u : ℝ → ℂ}
    (hμ : 0 < μ) (hΛ : 1 ≤ Λ) (hΛE : Λ ≤ E) (_hMu : 0 ≤ M_u)
    (ha₀ : a₀ < a) (hb₀ : b < b₀) (_hab : a ≤ b)
    (hcd_q : ContDiffOn ℝ r (fun x => (φ x)⁻¹) (Ioo a₀ b₀))
    (hq_sym : ∀ m ≤ r, ∀ x ∈ Ioo a₀ b₀, |iteratedDeriv m (fun x => (φ x)⁻¹) x| ≤ invDerivConst B m * μ⁻¹ * Λ ^ m)
    (hcd_u : ContDiff ℝ r u) (hu_sym : ∀ m ≤ r, ∀ x ∈ Icc a b, ‖iteratedDeriv m u x‖ ≤ M_u * E ^ m) :
    ∀ k m : ℕ, k + m ≤ r →
      ContDiffOn ℝ m (oscOp (fun x => (Complex.I * ((φ x : ℝ) : ℂ))⁻¹) k u) (Ioo a₀ b₀) ∧
        ∀ x ∈ Icc a b,
          ‖iteratedDeriv m (oscOp (fun x => (Complex.I * ((φ x : ℝ) : ℂ))⁻¹) k u) x‖ ≤
            oscConst (invDerivConst B) k m * μ⁻¹ ^ k * M_u * E ^ (k + m) := by
  set qC : ℝ → ℂ := fun x => (Complex.I * ((φ x : ℝ) : ℂ))⁻¹
  have hqC_eq : ∀ y : ℝ, qC y = (-Complex.I) * (((φ y)⁻¹ : ℝ) : ℂ) := fun y => by
    simp only [qC, mul_inv, inv_I]; push_cast; ring
  have hcd_qC : ContDiffOn ℝ r qC (Ioo a₀ b₀) := by
    refine ContDiffOn.congr
      ((contDiffOn_const (c := -Complex.I)).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hcd_q))
      fun y _ => by simpa only [Complex.ofRealCLM_apply, Function.comp_apply] using hqC_eq y
  have hqC_sym : ∀ i ≤ r, ∀ x ∈ Ioo a₀ b₀, ‖iteratedDeriv i qC x‖ ≤ invDerivConst B i * μ⁻¹ * Λ ^ i := by
    intro i hi x hx
    have hfun : qC = fun y : ℝ => (-Complex.I) * (((φ y)⁻¹ : ℝ) : ℂ) := funext hqC_eq
    rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_ofReal_eq (fun y => (φ y)⁻¹) i x,
      norm_mul, norm_neg, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact hq_sym i hi x hx
  have hE1 : 1 ≤ E := hΛ.trans hΛE
  have hE0 : 0 ≤ E := by linarith only [hE1]
  intro k
  induction k with
  | zero =>
    intro m hm
    rw [zero_add] at hm
    refine ⟨(hcd_u.of_le (by exact_mod_cast hm)).contDiffOn, fun x hx => ?_⟩
    simpa [oscOp, oscConst] using hu_sym m hm x hx
  | succ k ih =>
    intro m hm
    have hcd_prev := (ih (m + 1) (by omega)).1
    have hprod_cd : ContDiffOn ℝ ((m : WithTop ℕ∞) + 1) (fun y => qC y * oscOp qC k u y) (Ioo a₀ b₀) :=
      (hcd_qC.of_le (by exact_mod_cast (by omega : m + 1 ≤ r))).mul hcd_prev
    have hcd_next : ContDiffOn ℝ m (oscOp qC (k + 1) u) (Ioo a₀ b₀) := by
      have hs := hprod_cd
      rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo] at hs
      exact hs.2.2.neg
    refine ⟨hcd_next, fun x hx => ?_⟩
    have hx_o : x ∈ Ioo a₀ b₀ := ⟨lt_of_lt_of_le ha₀ hx.1, lt_of_le_of_lt hx.2 hb₀⟩
    have hhev : oscOp qC (k + 1) u = fun y => -deriv (fun z => qC z * oscOp qC k u z) y := rfl
    rw [hhev, iteratedDeriv_fun_neg, norm_neg, ← iteratedDeriv_succ']
    have hq_at : ContDiffAt ℝ (m + 1) qC x :=
      (hcd_qC.contDiffAt (isOpen_Ioo.mem_nhds hx_o)).of_le (by exact_mod_cast (by omega : m + 1 ≤ r))
    have hu_at : ContDiffAt ℝ (m + 1) (oscOp qC k u) x :=
      hcd_prev.contDiffAt (isOpen_Ioo.mem_nhds hx_o)
    rw [iteratedDeriv_fun_mul hq_at hu_at]
    refine (norm_sum_le _ _).trans ?_
    simp only [oscConst, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi_le : i ≤ m + 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 := hqC_sym i (by omega) x hx_o
    have h2 := (ih (m + 1 - i) (by omega)).2 x hx
    have hCq_nn := invDerivConst_nonneg hB0 i
    have hOc_nn := oscConst_nonneg (fun j => invDerivConst_nonneg hB0 j) k (m + 1 - i)
    have hΛp : Λ ^ i ≤ E ^ i := pow_le_pow_left₀ (by linarith only [hΛ]) hΛE i
    have hpow : E ^ i * E ^ (k + (m + 1 - i)) = E ^ (k + 1 + m) := by
      rw [← pow_add]; congr 1; omega
    rw [norm_mul, norm_mul, _root_.norm_natCast]
    calc (Nat.choose (m + 1) i : ℝ) * ‖iteratedDeriv i qC x‖ * ‖iteratedDeriv (m + 1 - i) (oscOp qC k u) x‖
        ≤ (Nat.choose (m + 1) i : ℝ) * (invDerivConst B i * μ⁻¹ * E ^ i) *
            (oscConst (invDerivConst B) k (m + 1 - i) * μ⁻¹ ^ k * M_u * E ^ (k + (m + 1 - i))) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left hΛp (mul_nonneg hCq_nn (inv_nonneg.2 hμ.le)))
      _ = (Nat.choose (m + 1) i : ℝ) * invDerivConst B i * oscConst (invDerivConst B) k (m + 1 - i) *
            μ⁻¹ ^ (k + 1) * M_u * (E ^ i * E ^ (k + (m + 1 - i))) := by
          rw [pow_succ']; ring
      _ = _ := by rw [hpow]

/-- **`r`-fold oscillatory IBP** for `∫ x in a..b, u(x) exp(i θ(x))` with `supp u ⊆ Icc a' b' ⊂ Ioo a b`. -/
theorem osc_ibp_r (r : ℕ) (B : ℕ → ℝ) (hB0 : ∀ j, 0 ≤ B j) :
    ∃ C_D : ℝ, 0 ≤ C_D ∧
      ∀ {a₀ a a' b' b b₀ μ Λ M_u E : ℝ} {θ : ℝ → ℝ} {u : ℝ → ℂ},
        0 < μ → 1 ≤ Λ → Λ ≤ E → 0 ≤ M_u →
        a₀ < a → a < a' → a' ≤ b' → b' < b → b < b₀ →
        ContDiffOn ℝ (r + 1) θ (Ioo a₀ b₀) →
        (∀ x ∈ Ioo a₀ b₀, μ ≤ |deriv θ x|) →
        (∀ j : ℕ, 1 ≤ j → j ≤ r → ∀ x ∈ Ioo a₀ b₀, |iteratedDeriv (j + 1) θ x| ≤ B j * |deriv θ x| * Λ ^ j) →
        ContDiff ℝ r u →
        (∀ x ∉ Icc a' b', u x = 0) →
        (∀ m ≤ r, ∀ x ∈ Icc a b, ‖iteratedDeriv m u x‖ ≤ M_u * E ^ m) →
        ‖∫ x in a..b, u x * Complex.exp (Complex.I * (θ x : ℂ))‖ ≤
          (b - a) * C_D * μ⁻¹ ^ r * M_u * E ^ r := by
  refine ⟨oscConst (invDerivConst B) r 0, oscConst_nonneg (fun j => invDerivConst_nonneg hB0 j) r 0, ?_⟩
  intro a₀ a a' b' b b₀ μ Λ M_u E θ u hμ hΛ hΛE hMu ha₀ haa ha'b' hb'b hbb₀ hθ hθ_lb hθ_sym hu hu_supp hu_sym
  have hab : a ≤ b := by linarith only [haa, ha'b', hb'b]
  have hφ_cd : ContDiffOn ℝ r (deriv θ) (Ioo a₀ b₀) := by
    have hs : ContDiffOn ℝ ((r : WithTop ℕ∞) + 1) θ (Ioo a₀ b₀) := hθ
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo] at hs
    exact hs.2.2
  have hφ_sym : ∀ j : ℕ, 1 ≤ j → j ≤ r → ∀ x ∈ Ioo a₀ b₀,
      |iteratedDeriv j (deriv θ) x| ≤ B j * |deriv θ x| * Λ ^ j := fun j hj1 hjr x hx => by
    rw [← iteratedDeriv_succ']
    exact hθ_sym j hj1 hjr x hx
  obtain ⟨hq_cd, hq_sym⟩ := inv_deriv_iteratedDeriv_bound hB0 hμ hΛ hφ_cd hθ_lb hφ_sym
  have hstep := oscOp_norm_bound hB0 hμ hΛ hΛE hMu ha₀ hbb₀ hab hq_cd hq_sym hu hu_sym
  set qC : ℝ → ℂ := fun x => (Complex.I * ((deriv θ x : ℝ) : ℂ))⁻¹
  have hibp : ∀ k ≤ r, ∫ x in a..b, u x * Complex.exp (Complex.I * (θ x : ℂ)) =
      ∫ x in a..b, oscOp qC k u x * Complex.exp (Complex.I * (θ x : ℂ)) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [ih (Nat.le_of_succ_le hk)]
      have hr1 : 1 ≤ r := by omega
      have hcd_k := (hstep k 1 hk).1
      have hcd_qC : ContDiffOn ℝ 1 qC (Ioo a₀ b₀) := by
        have hq1 := hq_cd.of_le (by exact_mod_cast hr1 : (1 : WithTop ℕ∞) ≤ r)
        refine ContDiffOn.congr
          ((contDiffOn_const (c := -Complex.I)).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hq1))
          fun y _ => by simp only [Complex.ofRealCLM_apply, Function.comp_apply, qC, mul_inv, inv_I]; push_cast; ring
      have hprod_cd : ContDiffOn ℝ 1 (fun y => qC y * oscOp qC k u y) (Ioo a₀ b₀) :=
        hcd_qC.mul hcd_k
      have hθ1 : ContDiffOn ℝ 1 θ (Ioo a₀ b₀) := hθ.of_le (by exact_mod_cast (by omega : 1 ≤ r + 1))
      have hcd_exp : ContDiffOn ℝ 1 (fun y => Complex.exp (Complex.I * (θ y : ℂ))) (Ioo a₀ b₀) :=
        ((contDiffOn_const (c := Complex.I)).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hθ1)).cexp
      have hsub : Icc a b ⊆ Ioo a₀ b₀ := fun x hx => ⟨lt_of_lt_of_le ha₀ hx.1, lt_of_le_of_lt hx.2 hbb₀⟩
      have hcont_exp : ContinuousOn (fun x => Complex.exp (Complex.I * (θ x : ℂ))) (Icc a b) :=
        hcd_exp.continuousOn.mono hsub
      have hderiv_v : ∀ x ∈ Icc a b,
          HasDerivAt (fun y => qC y * oscOp qC k u y) (deriv (fun y => qC y * oscOp qC k u y) x) x :=
        fun x hx => ((hprod_cd.differentiableOn one_ne_zero x (hsub hx)).differentiableAt
          (isOpen_Ioo.mem_nhds (hsub hx))).hasDerivAt
      have hderiv_θ : ∀ x ∈ Icc a b, HasDerivAt θ (deriv θ x) x :=
        fun x hx => ((hθ1.differentiableOn one_ne_zero x (hsub hx)).differentiableAt
          (isOpen_Ioo.mem_nhds (hsub hx))).hasDerivAt
      have hderiv_w : ∀ x ∈ Icc a b,
          HasDerivAt (fun y => Complex.exp (Complex.I * (θ y : ℂ)))
            (Complex.I * ((deriv θ x : ℝ) : ℂ) * Complex.exp (Complex.I * (θ x : ℂ))) x := fun x hx => by
        have h := ((hderiv_θ x hx).ofReal_comp.const_mul Complex.I).cexp
        exact h.congr_deriv (by ring)
      have hne : ∀ x ∈ Icc a b, Complex.I * ((deriv θ x : ℝ) : ℂ) ≠ 0 := fun x hx =>
        mul_ne_zero Complex.I_ne_zero (by exact_mod_cast abs_pos.1 (lt_of_lt_of_le hμ (hθ_lb x (hsub hx))))
      have hderiv_vw : ∀ x ∈ Icc a b,
          HasDerivAt (fun y => (qC y * oscOp qC k u y) * Complex.exp (Complex.I * (θ y : ℂ)))
            (-oscOp qC (k + 1) u x * Complex.exp (Complex.I * (θ x : ℂ)) +
              oscOp qC k u x * Complex.exp (Complex.I * (θ x : ℂ))) x := fun x hx => by
        refine ((hderiv_v x hx).mul (hderiv_w x hx)).congr_deriv ?_
        have hcan : qC x * (Complex.I * ((deriv θ x : ℝ) : ℂ)) = 1 := inv_mul_cancel₀ (hne x hx)
        have hneg : -oscOp qC (k + 1) u x = deriv (fun y => qC y * oscOp qC k u y) x := by
          change -(-deriv (fun y => qC y * oscOp qC k u y) x) = _; ring
        rw [hneg]
        calc deriv (fun y => qC y * oscOp qC k u y) x * Complex.exp (Complex.I * (θ x : ℂ)) +
              (qC x * oscOp qC k u x) * (Complex.I * ((deriv θ x : ℝ) : ℂ) * Complex.exp (Complex.I * (θ x : ℂ)))
            = deriv (fun y => qC y * oscOp qC k u y) x * Complex.exp (Complex.I * (θ x : ℂ)) +
                (qC x * (Complex.I * ((deriv θ x : ℝ) : ℂ))) * (oscOp qC k u x * Complex.exp (Complex.I * (θ x : ℂ))) := by ring
          _ = _ := by rw [hcan, one_mul]
      have hcont_k : ContinuousOn (fun x => oscOp qC k u x * Complex.exp (Complex.I * (θ x : ℂ))) (Icc a b) :=
        (hcd_k.continuousOn.mono hsub).mul hcont_exp
      have hcont_k1 : ContinuousOn (fun x => -oscOp qC (k + 1) u x * Complex.exp (Complex.I * (θ x : ℂ))) (Icc a b) := by
        have hcd_k1 := (hstep (k + 1) 0 hk).1
        exact (hcd_k1.continuousOn.neg.mono hsub).mul hcont_exp
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
        (f := fun y => (qC y * oscOp qC k u y) * Complex.exp (Complex.I * (θ y : ℂ)))
        (f' := fun x => -oscOp qC (k + 1) u x * Complex.exp (Complex.I * (θ x : ℂ)) +
          oscOp qC k u x * Complex.exp (Complex.I * (θ x : ℂ)))
        (by rw [uIcc_of_le hab]; exact hderiv_vw)
        ((hcont_k1.add hcont_k).intervalIntegrable_of_Icc hab)
      have ha_supp : a ∉ Icc a' b' := fun h => by linarith only [haa, h.1]
      have hb_supp : b ∉ Icc a' b' := fun h => by linarith only [hb'b, h.2]
      rw [oscOp_support hu_supp k a ha_supp, oscOp_support hu_supp k b hb_supp] at hftc
      simp only [mul_zero, zero_mul, sub_zero] at hftc
      rw [intervalIntegral.integral_add (hcont_k1.intervalIntegrable_of_Icc hab)
        (hcont_k.intervalIntegrable_of_Icc hab)] at hftc
      have hneg_int : (∫ x in a..b, -oscOp qC (k + 1) u x * Complex.exp (Complex.I * (θ x : ℂ))) =
          -(∫ x in a..b, oscOp qC (k + 1) u x * Complex.exp (Complex.I * (θ x : ℂ))) := by
        simp_rw [neg_mul]
        exact intervalIntegral.integral_neg
      rw [hneg_int] at hftc
      linear_combination hftc
  rw [hibp r le_rfl]
  have hnorm_le : ∀ x ∈ uIoc a b, ‖oscOp qC r u x * Complex.exp (Complex.I * (θ x : ℂ))‖ ≤
      oscConst (invDerivConst B) r 0 * μ⁻¹ ^ r * M_u * E ^ r := by
    intro x hx
    rw [uIoc_of_le hab] at hx
    have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2⟩
    have hre : (Complex.I * (θ x : ℂ)).re = 0 := by simp
    rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one]
    have hb := (hstep r 0 (by omega)).2 x hx'
    simpa only [iteratedDeriv_zero, add_zero] using hb
  calc ‖∫ x in a..b, oscOp qC r u x * Complex.exp (Complex.I * (θ x : ℂ))‖
      ≤ (oscConst (invDerivConst B) r 0 * μ⁻¹ ^ r * M_u * E ^ r) * |b - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hnorm_le
    _ = (b - a) * oscConst (invDerivConst B) r 0 * μ⁻¹ ^ r * M_u * E ^ r := by
        rw [abs_of_nonneg (sub_nonneg.2 hab)]; ring

/-- Direct 2-fold IBP for linear phase `∫ x in a..b, u(x) exp(i w x)` with `supp u ⊆ Icc a' b' ⊂ Ioo a b`. -/
theorem osc_ibp_linear_two {a a' b' b w M₂ : ℝ} {u : ℝ → ℂ}
    (hw : w ≠ 0) (haa : a < a') (ha'b' : a' ≤ b') (hb'b : b' < b)
    (hcd : ContDiff ℝ 2 u) (hsupp : ∀ x ∉ Icc a' b', u x = 0)
    (hbd : ∀ x ∈ Icc a b, ‖iteratedDeriv 2 u x‖ ≤ M₂) :
    ‖∫ x in a..b, u x * Complex.exp (Complex.I * (w : ℂ) * (x : ℂ))‖ ≤ (b - a) * M₂ / w ^ 2 := by
  have hab : a ≤ b := by linarith only [haa, ha'b', hb'b]
  have hM₂ : 0 ≤ M₂ := le_trans (norm_nonneg _) (hbd a ⟨le_rfl, hab⟩)
  set cω : ℂ := Complex.I * (w : ℂ)
  have hcω : cω ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hw)
  have hstep1 : ∀ (f : ℝ → ℂ), ContDiff ℝ 1 f → (∀ x ∉ Icc a' b', f x = 0) →
      ∫ x in a..b, f x * Complex.exp (cω * (x : ℂ)) =
        -(cω⁻¹) * ∫ x in a..b, deriv f x * Complex.exp (cω * (x : ℂ)) := by
    intro f hfc hfs
    have hderiv : ∀ x ∈ Icc a b,
        HasDerivAt (fun y => f y * Complex.exp (cω * (y : ℂ)))
          (deriv f x * Complex.exp (cω * (x : ℂ)) + cω * (f x * Complex.exp (cω * (x : ℂ)))) x := by
      intro x _
      have hf1 : HasDerivAt f (deriv f x) x := (hfc.differentiable one_ne_zero x).hasDerivAt
      have he1 : HasDerivAt (fun y : ℝ => Complex.exp (cω * (y : ℂ))) (cω * Complex.exp (cω * (x : ℂ))) x := by
        have h := (((hasDerivAt_id x).ofReal_comp).const_mul cω).cexp
        exact h.congr_deriv (by simp; ring)
      exact (hf1.mul he1).congr_deriv (by ring)
    have hcd1 : ContinuousOn (fun x => deriv f x * Complex.exp (cω * (x : ℂ))) (Icc a b) := by
      have hdf : Continuous (deriv f) := hfc.continuous_deriv (by simp)
      exact (hdf.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).continuousOn
    have hcd2 : ContinuousOn (fun x => cω * (f x * Complex.exp (cω * (x : ℂ)))) (Icc a b) :=
      (continuous_const.mul (hfc.continuous.mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)))).continuousOn
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
      (f := fun y => f y * Complex.exp (cω * (y : ℂ)))
      (f' := fun x => deriv f x * Complex.exp (cω * (x : ℂ)) + cω * (f x * Complex.exp (cω * (x : ℂ))))
      (by rw [uIcc_of_le hab]; exact hderiv)
      ((hcd1.add hcd2).intervalIntegrable_of_Icc hab)
    rw [hfs a (fun h => by linarith only [haa, h.1]), hfs b (fun h => by linarith only [hb'b, h.2])] at hftc
    simp only [zero_mul, sub_zero] at hftc
    rw [intervalIntegral.integral_add (hcd1.intervalIntegrable_of_Icc hab) (hcd2.intervalIntegrable_of_Icc hab),
      intervalIntegral.integral_const_mul] at hftc
    have hkey : cω * ∫ x in a..b, f x * Complex.exp (cω * (x : ℂ)) =
        -(∫ x in a..b, deriv f x * Complex.exp (cω * (x : ℂ))) :=
      eq_neg_of_add_eq_zero_right hftc
    calc ∫ x in a..b, f x * Complex.exp (cω * (x : ℂ))
        = cω⁻¹ * (cω * ∫ x in a..b, f x * Complex.exp (cω * (x : ℂ))) := by
          rw [← mul_assoc, inv_mul_cancel₀ hcω, one_mul]
      _ = cω⁻¹ * -(∫ x in a..b, deriv f x * Complex.exp (cω * (x : ℂ))) := by rw [hkey]
      _ = -(cω⁻¹) * ∫ x in a..b, deriv f x * Complex.exp (cω * (x : ℂ)) := by ring
  have h1 := hstep1 u (hcd.of_le (by norm_num)) hsupp
  have hdu_supp : ∀ x ∉ Icc a' b', deriv u x = 0 := by
    intro x hx
    have hopen : IsOpen ((Icc a' b')ᶜ) := isClosed_Icc.isOpen_compl
    have hev : u =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hsupp y hy
    rw [hev.deriv_eq, deriv_const]
  have hdu_cd : ContDiff ℝ 1 (deriv u) := by
    have hs : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) u := hcd
    rw [contDiff_succ_iff_deriv] at hs
    exact hs.2.2
  have h2 := hstep1 (deriv u) hdu_cd hdu_supp
  have hrew : ∫ x in a..b, u x * Complex.exp (Complex.I * (w : ℂ) * (x : ℂ)) =
      (-(cω⁻¹)) ^ 2 * ∫ x in a..b, iteratedDeriv 2 u x * Complex.exp (cω * (x : ℂ)) := by
    have h2e : ∀ x, deriv (deriv u) x = iteratedDeriv 2 u x := fun x => by
      rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
    calc ∫ x in a..b, u x * Complex.exp (Complex.I * (w : ℂ) * (x : ℂ))
        = ∫ x in a..b, u x * Complex.exp (cω * (x : ℂ)) := rfl
      _ = (-(cω⁻¹)) * ∫ x in a..b, deriv u x * Complex.exp (cω * (x : ℂ)) := h1
      _ = (-(cω⁻¹)) * ((-(cω⁻¹)) * ∫ x in a..b, deriv (deriv u) x * Complex.exp (cω * (x : ℂ))) := by
          rw [h2]
      _ = (-(cω⁻¹)) ^ 2 * ∫ x in a..b, iteratedDeriv 2 u x * Complex.exp (cω * (x : ℂ)) := by
          simp_rw [h2e]; ring
  rw [hrew, norm_mul, norm_pow, norm_neg, norm_inv]
  have hncω : ‖cω‖ = |w| := by
    simp only [cω, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hint_bd : ‖∫ x in a..b, iteratedDeriv 2 u x * Complex.exp (cω * (x : ℂ))‖ ≤ M₂ * (b - a) := by
    have hnorm_le : ∀ x ∈ uIoc a b, ‖iteratedDeriv 2 u x * Complex.exp (cω * (x : ℂ))‖ ≤ M₂ := by
      intro x hx
      rw [uIoc_of_le hab] at hx
      have hre : (cω * (x : ℂ)).re = 0 := by simp [cω]
      rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one]
      exact hbd x ⟨hx.1.le, hx.2⟩
    simpa [abs_of_nonneg (sub_nonneg.2 hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hnorm_le
  calc (‖cω‖⁻¹) ^ 2 * ‖∫ x in a..b, iteratedDeriv 2 u x * Complex.exp (cω * (x : ℂ))‖
      ≤ (|w|⁻¹) ^ 2 * (M₂ * (b - a)) := by
        rw [hncω]; exact mul_le_mul_of_nonneg_left hint_bd (by positivity)
    _ = (b - a) * M₂ / w ^ 2 := by rw [inv_pow, sq_abs]; ring

end FormalResearch.SignUncertainty