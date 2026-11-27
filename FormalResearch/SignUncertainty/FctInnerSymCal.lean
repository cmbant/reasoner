/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerSymbols
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Symbol-class calculus on `[0, U]` (`FctSymClsOn`)

Algebraic closure and composition lemmas for `FctSymClsOn (Icc 0 U) n p B`:

* Order/constant monotonicity, linearity, real-to-complex cast, and Leibniz product (`S^{p₁} · S^{p₂} ⊆ S^{p₁ + p₂}`).
* Exact affine rescaling `u = u₀ + (1 + u₀) v` (`iteratedDerivWithin_comp_affine`) with `norm_iteratedFDerivWithin_comp_le` for:
  - `g ∘ f ∈ S^0` when `g ∈ C^n` with uniformly bounded derivatives and `|f^{(j)}| ≤ Bf (1 + u)^{1 - j}` (`1 ≤ j ≤ n`), `Bf (1 + U) ≤ M`;
  - `g ∘ f ∈ S^p` (`n ≤ p`) on open `E` when `‖g^{(j)}(t)‖ ≤ Cg t^{p - j}` on `[0, ∞) ∩ E` and `0 ≤ f u ≤ Bf (1 + u)`;
  - `exp(X) - 1 ∈ S^p(C B)` and `exp(X) - 1 - X ∈ S^{2p}(C B²)` when `X ∈ S^p(B)` (`p ≥ 0`, `B (1 + U)^p ≤ 1`);
  - `(1 + X)⁻¹ ∈ S^0(invSymBound n)` when `X ∈ S^p(B)` (`p ≥ 0`, `B (1 + U)^p ≤ 1/2`).

Class: proved.
-/

@[expose] public section

open Set Filter Topology
open scoped Real ContDiff

namespace FormalResearch.SignUncertainty

private lemma contDiffOn_iteratedDerivWithin_of_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {D : Set ℝ} (hDu : UniqueDiffOn ℝ D) {n : ℕ} {h : ℝ → F}
    (hh : ContDiffOn ℝ n h D) :
    ∀ {j : ℕ}, j ≤ n → ContDiffOn ℝ ((n - j : ℕ) : WithTop ℕ∞) (iteratedDerivWithin j h D) D := by
  intro j
  induction j with
  | zero => intro _; simpa using hh
  | succ j ih =>
    intro hj
    have hj' : j ≤ n := Nat.le_of_succ_le hj
    have hprev := ih hj'
    have hsplit : ((n - j : ℕ) : WithTop ℕ∞) = (((n - (j + 1) : ℕ) : ℕ∞) + 1 : ℕ∞) := by
      have hn : n - j = (n - (j + 1)) + 1 := by omega
      rw [hn]; push_cast; rfl
    rw [hsplit] at hprev
    have hd := hprev.derivWithin (m := ((n - (j + 1) : ℕ) : ℕ∞)) hDu
      (by rw [← WithTop.coe_one, ← WithTop.coe_add])
    have hd' : ContDiffOn ℝ ((n - (j + 1) : ℕ) : WithTop ℕ∞) (derivWithin (iteratedDerivWithin j h D) D) D :=
      hd.of_le (by norm_cast)
    simpa [iteratedDerivWithin_succ] using hd'

/-! ### Basic algebra for `FctSymClsOn` -/

lemma FctSymClsOn.mono_n {D : Set ℝ} {m n : ℕ} (hmn : m ≤ n) {p B : ℝ} {κ : ℝ → ℂ}
    (h : FctSymClsOn D n p B κ) : FctSymClsOn D m p B κ :=
  ⟨h.1.of_le (by exact_mod_cast hmn), fun r hr u hu => h.2 r (hr.trans hmn) u hu⟩

lemma FctSymClsOn.mono_set {D D' : Set ℝ} (hDD' : D' ⊆ D) (hDu' : UniqueDiffOn ℝ D')
    (hDu : UniqueDiffOn ℝ D) {n : ℕ} {p B : ℝ} {κ : ℝ → ℂ} (h : FctSymClsOn D n p B κ) :
    FctSymClsOn D' n p B κ := by
  refine ⟨h.1.mono hDD', fun r hr u hu => ?_⟩
  rw [← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedFDerivWithin_subset hDD' hDu' hDu (h.1.of_le (by exact_mod_cast hr)) hu,
    norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  exact h.2 r hr u (hDD' hu)

lemma FctSymClsOn.congr {D : Set ℝ} (_hDu : UniqueDiffOn ℝ D) {n : ℕ} {p B : ℝ}
    {κ₁ κ₂ : ℝ → ℂ} (h : FctSymClsOn D n p B κ₁) (heq : EqOn κ₂ κ₁ D) :
    FctSymClsOn D n p B κ₂ := by
  refine ⟨h.1.congr heq, fun r hr u hu => ?_⟩
  rw [← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedFDerivWithin_congr heq hu r,
    norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  exact h.2 r hr u hu

lemma FctSymClsOn.shrink_p {U : ℝ} (_hU : 0 ≤ U) {n : ℕ} {p p' B : ℝ} {κ : ℝ → ℂ}
    (h : FctSymClsOn (Icc 0 U) n p B κ) (hB : 0 ≤ B) (hp : p' ≤ p) :
    FctSymClsOn (Icc 0 U) n p' (B * (1 + U) ^ (p - p')) κ := by
  refine ⟨h.1, fun r hr u hu => (h.2 r hr u hu).trans ?_⟩
  have hu0 : 0 ≤ u := hu.1
  have huU : u ≤ U := hu.2
  have h1u : 1 ≤ 1 + u := by linarith
  have hp0 : 0 ≤ p - p' := sub_nonneg.mpr hp
  have hpow : (1 + u) ^ (p - p') ≤ (1 + U) ^ (p - p') :=
    Real.rpow_le_rpow (by linarith) (by linarith) hp0
  have hsplit : (1 + u) ^ (p - (r : ℝ)) = (1 + u) ^ (p - p') * (1 + u) ^ (p' - (r : ℝ)) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  rw [hsplit]
  calc B * ((1 + u) ^ (p - p') * (1 + u) ^ (p' - (r : ℝ)))
      ≤ B * ((1 + U) ^ (p - p') * (1 + u) ^ (p' - (r : ℝ))) := by gcongr
    _ = B * (1 + U) ^ (p - p') * (1 + u) ^ (p' - (r : ℝ)) := by ring

lemma iteratedDerivWithin_ofReal_cast {D : Set ℝ} (hDu : UniqueDiffOn ℝ D)
    {n : ℕ} {f : ℝ → ℝ} (hcd : ContDiffOn ℝ n f D) :
    ∀ {r : ℕ}, r ≤ n → ∀ u ∈ D,
      iteratedDerivWithin r (fun x => ((f x : ℝ) : ℂ)) D u = ((iteratedDerivWithin r f D u : ℝ) : ℂ) := by
  intro r
  induction r with
  | zero => intro _ u _; simp
  | succ r ih =>
    intro hr u hu
    have hrn : r ≤ n := Nat.le_of_succ_le hr
    have heq : EqOn (iteratedDerivWithin r (fun x => ((f x : ℝ) : ℂ)) D)
        (fun x => ((iteratedDerivWithin r f D x : ℝ) : ℂ)) D := fun x hx => ih hrn x hx
    have hcd1 : ContDiffOn ℝ 1 (iteratedDerivWithin r f D) D :=
      (contDiffOn_iteratedDerivWithin_of_le hDu hcd hrn).of_le (by exact_mod_cast (by omega : 1 ≤ n - r))
    have hd : HasDerivWithinAt (iteratedDerivWithin r f D)
        (derivWithin (iteratedDerivWithin r f D) D u) D u :=
      (hcd1.differentiableOn (by simp) u hu).hasDerivWithinAt
    rw [iteratedDerivWithin_succ, derivWithin_congr heq (heq hu),
      hd.ofReal_comp.derivWithin (hDu u hu), ← iteratedDerivWithin_succ]

lemma FctSymClsOn.ofReal_cast {D : Set ℝ} (hDu : UniqueDiffOn ℝ D) {n : ℕ} {p B : ℝ} {f : ℝ → ℝ}
    (hcd : ContDiffOn ℝ n f D)
    (hbd : ∀ r : ℕ, r ≤ n → ∀ u ∈ D, |iteratedDerivWithin r f D u| ≤ B * (1 + u) ^ (p - r)) :
    FctSymClsOn D n p B (fun u => ((f u : ℝ) : ℂ)) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp_contDiffOn hcd, fun r hr u hu => ?_⟩
  rw [iteratedDerivWithin_ofReal_cast hDu hcd hr u hu, Complex.norm_real, Real.norm_eq_abs]
  exact hbd r hr u hu

lemma FctSymClsOn.const {D : Set ℝ} (hD : D ⊆ Ici 0) (n : ℕ) (k : ℂ) :
    FctSymClsOn D n 0 ‖k‖ (fun _ => k) := by
  refine ⟨contDiffOn_const, fun r _ u hu => ?_⟩
  rw [iteratedDerivWithin_const]
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp [Real.rpow_zero]
  · simp only [hr0.ne', ↓reduceIte, norm_zero]
    have hu0 : 0 ≤ u := hD hu
    positivity

lemma FctSymClsOn.add {D : Set ℝ} (hDu : UniqueDiffOn ℝ D) {n : ℕ} {p B₁ B₂ : ℝ}
    {κ₁ κ₂ : ℝ → ℂ} (h₁ : FctSymClsOn D n p B₁ κ₁) (h₂ : FctSymClsOn D n p B₂ κ₂) :
    FctSymClsOn D n p (B₁ + B₂) (fun u => κ₁ u + κ₂ u) := by
  refine ⟨h₁.1.add h₂.1, fun r hr u hu => ?_⟩
  change ‖iteratedDerivWithin r (κ₁ + κ₂) D u‖ ≤ _
  rw [iteratedDerivWithin_add hu hDu
    (h₁.1.contDiffWithinAt hu |>.of_le (by exact_mod_cast hr))
    (h₂.1.contDiffWithinAt hu |>.of_le (by exact_mod_cast hr))]
  refine (norm_add_le _ _).trans ?_
  rw [add_mul]
  exact add_le_add (h₁.2 r hr u hu) (h₂.2 r hr u hu)

lemma FctSymClsOn.sub {D : Set ℝ} (hDu : UniqueDiffOn ℝ D) {n : ℕ} {p B₁ B₂ : ℝ}
    {κ₁ κ₂ : ℝ → ℂ} (h₁ : FctSymClsOn D n p B₁ κ₁) (h₂ : FctSymClsOn D n p B₂ κ₂) :
    FctSymClsOn D n p (B₁ + B₂) (fun u => κ₁ u - κ₂ u) := by
  refine ⟨h₁.1.sub h₂.1, fun r hr u hu => ?_⟩
  change ‖iteratedDerivWithin r (κ₁ - κ₂) D u‖ ≤ _
  rw [iteratedDerivWithin_sub hu hDu
    (h₁.1.contDiffWithinAt hu |>.of_le (by exact_mod_cast hr))
    (h₂.1.contDiffWithinAt hu |>.of_le (by exact_mod_cast hr))]
  refine (norm_sub_le _ _).trans ?_
  rw [add_mul]
  exact add_le_add (h₁.2 r hr u hu) (h₂.2 r hr u hu)

lemma FctSymClsOn.neg {D : Set ℝ} {n : ℕ} {p B : ℝ} {κ : ℝ → ℂ}
    (h : FctSymClsOn D n p B κ) : FctSymClsOn D n p B (fun u => -κ u) := by
  refine ⟨h.1.neg, fun r hr u hu => ?_⟩
  change ‖iteratedDerivWithin r (-κ) D u‖ ≤ _
  rw [iteratedDerivWithin_neg, norm_neg]
  exact h.2 r hr u hu

lemma FctSymClsOn.const_mul {D : Set ℝ} (hDu : UniqueDiffOn ℝ D) {n : ℕ} {p B : ℝ}
    (a : ℂ) {κ : ℝ → ℂ} (h : FctSymClsOn D n p B κ) :
    FctSymClsOn D n p (‖a‖ * B) (fun u => a * κ u) := by
  refine ⟨contDiffOn_const.mul h.1, fun r hr u hu => ?_⟩
  rw [iteratedDerivWithin_const_mul hu hDu a (h.1.contDiffWithinAt hu |>.of_le (by exact_mod_cast hr)),
    norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h.2 r hr u hu) (norm_nonneg a)

lemma FctSymClsOn.mul {D : Set ℝ} (hD : D ⊆ Ici 0) (hDu : UniqueDiffOn ℝ D)
    {n : ℕ} {p₁ p₂ B₁ B₂ : ℝ} {κ₁ κ₂ : ℝ → ℂ}
    (h₁ : FctSymClsOn D n p₁ B₁ κ₁) (h₂ : FctSymClsOn D n p₂ B₂ κ₂) :
    FctSymClsOn D n (p₁ + p₂) (2 ^ n * B₁ * B₂) (fun u => κ₁ u * κ₂ u) := by
  refine ⟨h₁.1.mul h₂.1, fun r hr u hu => ?_⟩
  have hu0 : 0 ≤ u := hD hu
  have h1u : 0 < 1 + u := by linarith
  rw [← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  have hle := norm_iteratedFDerivWithin_mul_le h₁.1 h₂.1 hDu hu (n := r) (by exact_mod_cast hr)
  refine hle.trans ?_
  calc ∑ i ∈ Finset.range (r + 1),
        (r.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i κ₁ D u‖ * ‖iteratedFDerivWithin ℝ (r - i) κ₂ D u‖
      ≤ ∑ i ∈ Finset.range (r + 1),
        (r.choose i : ℝ) * (B₁ * (1 + u) ^ (p₁ - i)) * (B₂ * (1 + u) ^ (p₂ - ((r - i : ℕ) : ℝ))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
            norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
          have hB₁ : 0 ≤ B₁ * (1 + u) ^ (p₁ - i) := (norm_nonneg _).trans (h₁.2 i (hir.trans hr) u hu)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (h₁.2 i (hir.trans hr) u hu) (Nat.cast_nonneg _))
            (h₂.2 (r - i) (by omega) u hu) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) hB₁)
    _ = (∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ)) * (B₁ * B₂ * (1 + u) ^ (p₁ + p₂ - r)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hsub : ((r - i : ℕ) : ℝ) = (r : ℝ) - (i : ℝ) := Nat.cast_sub hir
          have hexp : (1 + u) ^ (p₁ - i) * (1 + u) ^ (p₂ - ((r - i : ℕ) : ℝ)) =
              (1 + u) ^ (p₁ + p₂ - r) := by
            rw [← Real.rpow_add h1u, hsub]; congr 1; ring
          calc (r.choose i : ℝ) * (B₁ * (1 + u) ^ (p₁ - i)) * (B₂ * (1 + u) ^ (p₂ - ((r - i : ℕ) : ℝ)))
              = (r.choose i : ℝ) * (B₁ * B₂ * ((1 + u) ^ (p₁ - i) * (1 + u) ^ (p₂ - ((r - i : ℕ) : ℝ)))) := by ring
            _ = (r.choose i : ℝ) * (B₁ * B₂ * (1 + u) ^ (p₁ + p₂ - r)) := by rw [hexp]
    _ = 2 ^ r * (B₁ * B₂ * (1 + u) ^ (p₁ + p₂ - r)) := by
          congr 1; exact_mod_cast Nat.sum_range_choose r
    _ ≤ 2 ^ n * B₁ * B₂ * (1 + u) ^ (p₁ + p₂ - r) := by
          have hB₁ : 0 ≤ B₁ := by
            have h0 := (norm_nonneg (iteratedDerivWithin 0 κ₁ D u)).trans (h₁.2 0 (Nat.zero_le _) u hu)
            rw [Nat.cast_zero, sub_zero] at h0
            exact nonneg_of_mul_nonneg_left h0 (Real.rpow_pos_of_pos h1u p₁)
          have hB₂ : 0 ≤ B₂ := by
            have h0 := (norm_nonneg (iteratedDerivWithin 0 κ₂ D u)).trans (h₂.2 0 (Nat.zero_le _) u hu)
            rw [Nat.cast_zero, sub_zero] at h0
            exact nonneg_of_mul_nonneg_left h0 (Real.rpow_pos_of_pos h1u p₂)
          have h2rn : (2 : ℝ) ^ r ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hr
          have hpow0 : 0 ≤ (1 + u) ^ (p₁ + p₂ - r) := (Real.rpow_pos_of_pos h1u _).le
          calc (2 : ℝ) ^ r * (B₁ * B₂ * (1 + u) ^ (p₁ + p₂ - r))
              ≤ 2 ^ n * (B₁ * B₂ * (1 + u) ^ (p₁ + p₂ - r)) := by gcongr
            _ = _ := by ring

lemma FctSymClsOn.derivWithin_Icc {U : ℝ} (hU : 0 < U) {n : ℕ} (hn : 1 ≤ n) {p B : ℝ}
    {κ : ℝ → ℂ} (h : FctSymClsOn (Icc 0 U) n p B κ) :
    FctSymClsOn (Icc 0 U) (n - 1) (p - 1) B (derivWithin κ (Icc 0 U)) := by
  have hDu : UniqueDiffOn ℝ (Icc 0 U) := uniqueDiffOn_Icc hU
  have hcd : ContDiffOn ℝ ((n - 1 : ℕ) : WithTop ℕ∞) (derivWithin κ (Icc 0 U)) (Icc 0 U) := by
    have h1 : ContDiffOn ℝ (((n - 1 : ℕ) + 1 : ℕ) : WithTop ℕ∞) κ (Icc 0 U) := by
      rw [Nat.sub_add_cancel hn]; exact h.1
    exact h1.derivWithin hDu (by simp)
  refine ⟨hcd, fun r hr u hu => ?_⟩
  rw [← iteratedDerivWithin_succ']
  have hrn : r + 1 ≤ n := by omega
  refine (h.2 (r + 1) hrn u hu).trans (le_of_eq ?_)
  congr 2; push_cast; ring

/-! ### Exact affine rescaling for `iteratedDerivWithin` -/

lemma iteratedDerivWithin_comp_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : Set ℝ} (hDu : UniqueDiffOn ℝ D) {u₀ R₀ : ℝ}
    (hSu : UniqueDiffOn ℝ ((fun v : ℝ => u₀ + R₀ * v) ⁻¹' D))
    {n : ℕ} {h : ℝ → F} (hh : ContDiffOn ℝ n h D) :
    ∀ {j : ℕ}, j ≤ n → ∀ {v : ℝ}, u₀ + R₀ * v ∈ D →
      iteratedDerivWithin j (h ∘ (fun w : ℝ => u₀ + R₀ * w)) ((fun w : ℝ => u₀ + R₀ * w) ⁻¹' D) v =
        (R₀ ^ j) • iteratedDerivWithin j h D (u₀ + R₀ * v) := by
  let ψ : ℝ → ℝ := fun w => u₀ + R₀ * w
  let S : Set ℝ := ψ ⁻¹' D
  have hψ_deriv : ∀ w, HasDerivAt ψ R₀ w := fun w => by
    have h1 := ((hasDerivAt_id w).const_mul R₀).const_add u₀
    simpa [ψ] using h1
  intro j
  induction j with
  | zero =>
    intro _ v _; simp
  | succ j ih =>
    intro hj v hv
    have hj' : j ≤ n := Nat.le_of_succ_le hj
    have heq : EqOn (iteratedDerivWithin j (h ∘ ψ) S)
        (fun w => (R₀ ^ j) • iteratedDerivWithin j h D (ψ w)) S :=
      fun w hw => ih hj' hw
    have hcd1 : ContDiffOn ℝ 1 (iteratedDerivWithin j h D) D :=
      (contDiffOn_iteratedDerivWithin_of_le hDu hh hj').of_le (by exact_mod_cast (by omega : 1 ≤ n - j))
    have hd_at : DifferentiableWithinAt ℝ (iteratedDerivWithin j h D) D (ψ v) :=
      hcd1.differentiableOn (by simp) (ψ v) hv
    have hcomp : HasDerivWithinAt (fun w => (R₀ ^ j) • iteratedDerivWithin j h D (ψ w))
        ((R₀ ^ j) • (R₀ • derivWithin (iteratedDerivWithin j h D) D (ψ v))) S v := by
      have hs1 : HasDerivWithinAt ψ R₀ S v := (hψ_deriv v).hasDerivWithinAt
      have hs2 : HasDerivWithinAt (iteratedDerivWithin j h D)
          (derivWithin (iteratedDerivWithin j h D) D (ψ v)) D (ψ v) :=
        hd_at.hasDerivWithinAt
      have hs3 : HasDerivWithinAt (fun w => iteratedDerivWithin j h D (ψ w))
          (R₀ • derivWithin (iteratedDerivWithin j h D) D (ψ v)) S v :=
        hs2.scomp v hs1 (fun _ hw => hw)
      exact hs3.const_smul (R₀ ^ j)
    rw [iteratedDerivWithin_succ, derivWithin_congr heq (heq hv), hcomp.derivWithin (hSu v hv),
      ← iteratedDerivWithin_succ, smul_smul, pow_succ]

private lemma preimage_affine_Icc {U u₀ R₀ : ℝ} (hR0 : 0 < R₀) :
    (fun v : ℝ => u₀ + R₀ * v) ⁻¹' Icc 0 U = Icc (-u₀ / R₀) ((U - u₀) / R₀) := by
  ext v; simp only [mem_preimage, mem_Icc]
  constructor <;> intro ⟨h1, h2⟩ <;> constructor
  · rw [div_le_iff₀ hR0]; linarith
  · rw [le_div_iff₀ hR0]; linarith
  · rw [div_le_iff₀ hR0] at h1; linarith
  · rw [le_div_iff₀ hR0] at h2; linarith

private lemma preimage_affine_uniqueDiffOn {U u₀ R₀ : ℝ} (hU : 0 < U) (hR0 : 0 < R₀) :
    UniqueDiffOn ℝ ((fun v : ℝ => u₀ + R₀ * v) ⁻¹' Icc 0 U) := by
  rw [preimage_affine_Icc hR0]
  exact uniqueDiffOn_Icc (by rw [div_lt_div_iff_of_pos_right hR0]; linarith)

/-! ### Composition and analytic-map lemmas via affine rescaling -/

/-- Composition on the right with `f : ℝ → ℝ` satisfying `|f^{(j)}(u)| ≤ Bf * (1 + u)^{1 - j}`
(`1 ≤ j ≤ n`) and `Bf * (1 + U) ≤ M` (`M ≥ 1`) preserves `𝒮^0` for any `g ∈ C^n` with bounded derivatives. -/
lemma FctSymClsOn.comp_T_zero {U M : ℝ} (hU : 0 < U) (hM : 1 ≤ M)
    {n : ℕ} {E : Set ℝ} (hEu : UniqueDiffOn ℝ E)
    {g : ℝ → ℂ} (hg : ContDiffOn ℝ n g E) {Cg : ℝ} (_hCg : 0 ≤ Cg)
    (hgb : ∀ i ≤ n, ∀ t ∈ E, ‖iteratedDerivWithin i g E t‖ ≤ Cg)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ n f (Icc 0 U)) (hmaps : MapsTo f (Icc 0 U) E)
    {Bf : ℝ} (hBf0 : 0 ≤ Bf) (hBfM : Bf * (1 + U) ≤ M)
    (hfb : ∀ j : ℕ, 1 ≤ j → j ≤ n → ∀ u ∈ Icc 0 U,
      |iteratedDerivWithin j f (Icc 0 U) u| ≤ Bf * (1 + u) ^ ((1 : ℝ) - j)) :
    FctSymClsOn (Icc 0 U) n 0 ((n.factorial : ℝ) * Cg * M ^ n) (g ∘ f) := by
  have hDu : UniqueDiffOn ℝ (Icc 0 U) := uniqueDiffOn_Icc hU
  have hcomp : ContDiffOn ℝ n (g ∘ f) (Icc 0 U) := hg.comp hf hmaps
  refine ⟨hcomp, fun r hr u hu => ?_⟩
  have h1u0 : 0 < 1 + u := by linarith [hu.1]
  set R₀ : ℝ := 1 + u
  let ψ : ℝ → ℝ := fun v => u + R₀ * v
  let S : Set ℝ := ψ ⁻¹' Icc 0 U
  have hSu : UniqueDiffOn ℝ S := preimage_affine_uniqueDiffOn hU h1u0
  have hψ0 : ψ 0 = u := by simp [ψ]
  have hu_aff : u + R₀ * 0 ∈ Icc 0 U := by simpa using hu
  have h0S : (0 : ℝ) ∈ S := hu_aff
  have hψ_maps : MapsTo ψ S (Icc 0 U) := fun _ hv => hv
  have hψ_cd : ContDiffOn ℝ n ψ S := (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn
  have hH_cd : ContDiffOn ℝ n (f ∘ ψ) S := hf.comp hψ_cd hψ_maps
  have hmaps_fψ : MapsTo (f ∘ ψ) S E := hmaps.comp hψ_maps
  have hH_bd : ∀ j : ℕ, 1 ≤ j → j ≤ r →
      ‖iteratedFDerivWithin ℝ j (f ∘ ψ) S 0‖ ≤ M ^ j := by
    intro j hj1 hjr
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_comp_affine hDu hSu hf (hjr.trans hr) hu_aff]
    simp only [mul_zero, add_zero, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos h1u0]
    have hfj := hfb j hj1 (hjr.trans hr) u hu
    have hpow : R₀ ^ j * (Bf * R₀ ^ ((1 : ℝ) - j)) = Bf * R₀ := by
      have h1 : R₀ ^ ((1 : ℝ) - j) = R₀ * (R₀ ^ j)⁻¹ := by
        rw [Real.rpow_sub h1u0, Real.rpow_one, Real.rpow_natCast, div_eq_mul_inv]
      rw [h1]; field_simp [h1u0.ne']
    have hM1 : Bf * R₀ ≤ M := by
      calc Bf * R₀ ≤ Bf * (1 + U) := mul_le_mul_of_nonneg_left (by linarith [hu.2]) hBf0
        _ ≤ M := hBfM
    have hMj : M ≤ M ^ j := le_self_pow₀ hM (by omega)
    calc R₀ ^ j * |iteratedDerivWithin j f (Icc 0 U) u|
        ≤ R₀ ^ j * (Bf * R₀ ^ ((1 : ℝ) - j)) := mul_le_mul_of_nonneg_left hfj (pow_nonneg h1u0.le j)
      _ = Bf * R₀ := hpow
      _ ≤ M ^ j := hM1.trans hMj
  have hle := norm_iteratedFDerivWithin_comp_le (g := g) (f := f ∘ ψ) (n := r) (N := n)
    hg hH_cd (by exact_mod_cast hr) hEu hSu hmaps_fψ h0S
    (C := Cg) (D := M)
    (fun i hi => by
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
      exact hgb i (hi.trans hr) _ (hmaps_fψ h0S))
    (fun i hi1 hir => hH_bd i hi1 hir)
  have hgf_aff : iteratedDerivWithin r ((g ∘ f) ∘ ψ) S 0 =
      R₀ ^ r * iteratedDerivWithin r (g ∘ f) (Icc 0 U) u := by
    have h := iteratedDerivWithin_comp_affine hDu hSu hcomp hr hu_aff
    simpa [ψ, Function.comp, smul_eq_mul] using h
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin] at hle
  change ‖iteratedDerivWithin r ((g ∘ f) ∘ ψ) S 0‖ ≤ _ at hle
  rw [hgf_aff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1u0] at hle
  have hpowr : (1 + u) ^ ((0 : ℝ) - r) = (R₀ ^ r)⁻¹ := by
    rw [zero_sub, Real.rpow_neg h1u0.le, Real.rpow_natCast]
  rw [hpowr, ← div_eq_mul_inv, le_div_iff₀ (pow_pos h1u0 r), mul_comm _ (R₀ ^ r)]
  refine hle.trans ?_
  have hr_fac : (r.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hr
  have hM_rn : M ^ r ≤ M ^ n := pow_le_pow_right₀ hM hr
  gcongr

/-- Composition on the right with `f : ℝ → ℝ` for homogeneous degree-`p` symbols (`n ≤ p`) on an open set `E`:
if `0 ≤ f u ≤ Bf * (1 + u)`, `|f^{(j)}(u)| ≤ Bf * (1 + u)^{1 - j}` (`1 ≤ j ≤ n`), and
`‖g^{(i)}(t)‖ ≤ Cg * t^{p - i}` for all `i ≤ n` and `t ∈ E ∩ [0, ∞)`, then `g ∘ f ∈ S^p`. -/
lemma FctSymClsOn.comp_T_pow {U : ℝ} (hU : 0 < U)
    {n p : ℕ} (hnp : n ≤ p) {E : Set ℝ} (hEo : IsOpen E)
    {g : ℝ → ℂ} (hg : ContDiffOn ℝ n g E) {Cg : ℝ} (_hCg : 0 ≤ Cg)
    (hgb : ∀ i ≤ n, ∀ t ∈ E, 0 ≤ t → ‖iteratedDerivWithin i g E t‖ ≤ Cg * t ^ (p - i))
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ n f (Icc 0 U)) (hmaps : MapsTo f (Icc 0 U) E)
    {Bf : ℝ} (hBf0 : 0 < Bf)
    (hf0 : ∀ u ∈ Icc 0 U, 0 ≤ f u ∧ f u ≤ Bf * (1 + u))
    (hfb : ∀ j : ℕ, 1 ≤ j → j ≤ n → ∀ u ∈ Icc 0 U,
      |iteratedDerivWithin j f (Icc 0 U) u| ≤ Bf * (1 + u) ^ ((1 : ℝ) - j)) :
    FctSymClsOn (Icc 0 U) n p ((n.factorial : ℝ) * Cg * Bf ^ p) (g ∘ f) := by
  have hEu : UniqueDiffOn ℝ E := hEo.uniqueDiffOn
  have hDu : UniqueDiffOn ℝ (Icc 0 U) := uniqueDiffOn_Icc hU
  have hcomp : ContDiffOn ℝ n (g ∘ f) (Icc 0 U) := hg.comp hf hmaps
  refine ⟨hcomp, fun r hr u hu => ?_⟩
  have h1u0 : 0 < 1 + u := by linarith [hu.1]
  set R₀ : ℝ := 1 + u
  set Scl : ℝ := Bf * R₀
  have hScl0 : 0 < Scl := mul_pos hBf0 h1u0
  let ψ : ℝ → ℝ := fun v => u + R₀ * v
  let S : Set ℝ := ψ ⁻¹' Icc 0 U
  have hSu : UniqueDiffOn ℝ S := preimage_affine_uniqueDiffOn hU h1u0
  have hu_aff : u + R₀ * 0 ∈ Icc 0 U := by simpa using hu
  have h0S : (0 : ℝ) ∈ S := hu_aff
  have hψ_maps : MapsTo ψ S (Icc 0 U) := fun _ hv => hv
  have hψ_cd : ContDiffOn ℝ n ψ S := (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn
  let H : ℝ → ℝ := fun v => Scl⁻¹ * f (ψ v)
  let G : ℝ → ℂ := fun w => g (0 + Scl * w)
  let E_G : Set ℝ := (fun w => 0 + Scl * w) ⁻¹' E
  have hEGu : UniqueDiffOn ℝ E_G :=
    (hEo.preimage (continuous_const.add (continuous_const.mul continuous_id))).uniqueDiffOn
  have hG_cd : ContDiffOn ℝ n G E_G :=
    hg.comp (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn (fun _ hw => hw)
  have hH_cd : ContDiffOn ℝ n H S := contDiffOn_const.mul (hf.comp hψ_cd hψ_maps)
  have hmaps_H : MapsTo H S E_G := fun v hv => by
    show 0 + Scl * (Scl⁻¹ * f (ψ v)) ∈ E
    rw [zero_add, mul_inv_cancel_left₀ hScl0.ne']
    exact hmaps (hψ_maps hv)
  have hH_bd : ∀ j : ℕ, 1 ≤ j → j ≤ r → ‖iteratedFDerivWithin ℝ j H S 0‖ ≤ 1 ^ j := by
    intro j hj1 hjr
    rw [one_pow, norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    have hHeq : H = fun v => Scl⁻¹ * (f ∘ ψ) v := rfl
    rw [hHeq, iteratedDerivWithin_const_mul h0S hSu Scl⁻¹
      ((hf.comp hψ_cd hψ_maps).contDiffWithinAt h0S |>.of_le (by exact_mod_cast (hjr.trans hr)))]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hScl0)]
    rw [iteratedDerivWithin_comp_affine hDu hSu hf (hjr.trans hr) hu_aff]
    simp only [mul_zero, add_zero, smul_eq_mul, abs_mul, abs_pow, abs_of_pos h1u0]
    have hfj := hfb j hj1 (hjr.trans hr) u hu
    have hpow : R₀ ^ j * (Bf * R₀ ^ ((1 : ℝ) - j)) = Scl := by
      have h1 : R₀ ^ ((1 : ℝ) - j) = R₀ * (R₀ ^ j)⁻¹ := by
        rw [Real.rpow_sub h1u0, Real.rpow_one, Real.rpow_natCast, div_eq_mul_inv]
      rw [h1]; dsimp only [Scl]; field_simp [h1u0.ne']
    calc Scl⁻¹ * (R₀ ^ j * |iteratedDerivWithin j f (Icc 0 U) u|)
        ≤ Scl⁻¹ * (R₀ ^ j * (Bf * R₀ ^ ((1 : ℝ) - j))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfj (pow_nonneg h1u0.le j)) (inv_pos.mpr hScl0).le
      _ = 1 := by rw [hpow, inv_mul_cancel₀ hScl0.ne']
  have hG_bd : ∀ i ≤ r, ‖iteratedDerivWithin i G E_G (H 0)‖ ≤ Cg * Scl ^ p := by
    intro i hir
    have h0eq : 0 + Scl * H 0 = f u := by
      simp only [H, ψ, mul_zero, add_zero, zero_add]; rw [mul_inv_cancel_left₀ hScl0.ne']
    have hGe := iteratedDerivWithin_comp_affine hEu hEGu hg (u₀ := 0) (R₀ := Scl)
      (hir.trans hr) (by show 0 + Scl * H 0 ∈ E; rw [h0eq]; exact hmaps hu)
    change iteratedDerivWithin i G E_G (H 0) = Scl ^ i • iteratedDerivWithin i g E (0 + Scl * H 0) at hGe
    rw [hGe, h0eq, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos hScl0]
    have hgi := hgb i (hir.trans hr) (f u) (hmaps hu) (hf0 u hu).1
    have hfu_le : f u ^ (p - i) ≤ Scl ^ (p - i) :=
      pow_le_pow_left₀ (hf0 u hu).1 (hf0 u hu).2 (p - i)
    have hip : i ≤ p := (hir.trans hr).trans hnp
    have hpow_eq : Scl ^ i * Scl ^ (p - i) = Scl ^ p := by
      rw [← pow_add, Nat.add_sub_cancel' hip]
    calc Scl ^ i * ‖iteratedDerivWithin i g E (f u)‖
        ≤ Scl ^ i * (Cg * f u ^ (p - i)) := mul_le_mul_of_nonneg_left hgi (pow_nonneg hScl0.le i)
      _ ≤ Scl ^ i * (Cg * Scl ^ (p - i)) := by gcongr
      _ = Cg * Scl ^ p := by rw [← mul_assoc, mul_comm (Scl ^ i) Cg, mul_assoc, hpow_eq]
  have hle := norm_iteratedFDerivWithin_comp_le (g := G) (f := H) (n := r) (N := n)
    hG_cd hH_cd (by exact_mod_cast hr) hEGu hSu hmaps_H h0S
    (C := Cg * Scl ^ p) (D := 1)
    (fun i hi => by rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]; exact hG_bd i hi)
    (fun i hi1 hir => hH_bd i hi1 hir)
  have hcomp_eq : (G ∘ H) = (g ∘ f) ∘ ψ := by
    ext v; simp [G, H, Function.comp, mul_inv_cancel_left₀ hScl0.ne']
  have hgf_aff : iteratedDerivWithin r (G ∘ H) S 0 =
      R₀ ^ r * iteratedDerivWithin r (g ∘ f) (Icc 0 U) u := by
    rw [hcomp_eq]
    have h := iteratedDerivWithin_comp_affine hDu hSu hcomp hr hu_aff
    simpa [ψ, smul_eq_mul] using h
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin] at hle
  change ‖iteratedDerivWithin r (G ∘ H) S 0‖ ≤ _ at hle
  rw [hgf_aff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1u0, one_pow,
    mul_one] at hle
  have hSclp : Scl ^ p = Bf ^ p * R₀ ^ p := mul_pow Bf R₀ p
  have hpowr : (1 + u) ^ ((p : ℝ) - r) = R₀ ^ p / R₀ ^ r := by
    rw [Real.rpow_sub h1u0, Real.rpow_natCast, Real.rpow_natCast]
  rw [hpowr]
  have hr_fac : (r.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hr
  have hCg0 : 0 ≤ Cg * Scl ^ p := (norm_nonneg _).trans (hG_bd 0 (Nat.zero_le r))
  have hbound : R₀ ^ r * ‖iteratedDerivWithin r (g ∘ f) (Icc 0 U) u‖ ≤
      R₀ ^ r * (((n.factorial : ℝ) * Cg * Bf ^ p) * (R₀ ^ p / R₀ ^ r)) := by
    have heq : R₀ ^ r * (((n.factorial : ℝ) * Cg * Bf ^ p) * (R₀ ^ p / R₀ ^ r)) =
        (n.factorial : ℝ) * (Cg * Scl ^ p) := by
      rw [hSclp]; field_simp [h1u0.ne']
    rw [heq]
    exact hle.trans (mul_le_mul_of_nonneg_right hr_fac hCg0)
  exact le_of_mul_le_mul_left hbound (pow_pos h1u0 r)

private lemma iteratedFDeriv_cexp_const_mul (a c : ℂ) :
    ∀ (i : ℕ), 1 ≤ i → ∀ (w : ℂ) (v : Fin i → ℂ),
      iteratedFDeriv ℝ i (fun z : ℂ => Complex.exp (a * z) - c) w v =
        (a ^ i * Complex.exp (a * w)) * ∏ k : Fin i, v k := by
  intro i hi
  induction i with
  | zero => omega
  | succ i ih =>
    intro w v
    rcases i with _ | i
    · have hd_C : HasDerivAt (fun z : ℂ => Complex.exp (a * z) - c) (a * Complex.exp (a * w)) w := by
        have h1 := ((hasDerivAt_id w).const_mul a).cexp.sub_const c
        refine h1.congr_deriv ?_; simp [mul_comm]
      have hf_R := hd_C.hasFDerivAt.restrictScalars ℝ
      rw [iteratedFDeriv_one_apply, hf_R.fderiv]
      simp [mul_comm]
    · have hi1 : 1 ≤ i + 1 := Nat.succ_pos i
      let Φ : ContinuousMultilinearMap ℝ (fun _ : Fin (i + 1) => ℂ) ℂ :=
        ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin (i + 1)) ℂ
      let s : ℂ → ℂ := fun z => a ^ (i + 1) * Complex.exp (a * z)
      have hfun : iteratedFDeriv ℝ (i + 1) (fun z : ℂ => Complex.exp (a * z) - c) = fun z => s z • Φ := by
        ext z m
        simp only [smul_apply, smul_eq_mul, Φ, s, ContinuousMultilinearMap.mkPiAlgebra_apply]
        exact ih hi1 z m
      have hd_C : HasDerivAt s (a * s w) w := by
        have h1 := ((hasDerivAt_id w).const_mul a).cexp.const_mul (a ^ (i + 1))
        refine h1.congr_deriv ?_
        simp only [id_eq, mul_one, s]; ring
      have hf_R := (hd_C.hasFDerivAt.restrictScalars ℝ).smul_const Φ
      rw [iteratedFDeriv_succ_apply_left, hfun, hf_R.fderiv]
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_restrictScalars',
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
        smul_apply, ContinuousMultilinearMap.mkPiAlgebra_apply, Φ, s]
      have htail : (∏ k : Fin (i + 1), Fin.tail v k) = ∏ k : Fin (i + 1), v k.succ := rfl
      rw [Fin.prod_univ_succ (f := v), htail]
      ring

/-- If `X ∈ S^p(B)` on `[0, U]` with `p ≥ 0` and `B (1 + U)^p ≤ 1`, then
`exp(X) - 1 ∈ S^p(3 n! B)`. -/
lemma FctSymClsOn.cexp_sub_one {U : ℝ} (hU : 0 < U) {n : ℕ} {p B : ℝ}
    (hp0 : 0 ≤ p) (hB0 : 0 ≤ B) (hBU : B * (1 + U) ^ p ≤ 1)
    {X : ℝ → ℂ} (hX : FctSymClsOn (Icc 0 U) n p B X) :
    FctSymClsOn (Icc 0 U) n p (3 * (n.factorial : ℝ) * B) (fun u => Complex.exp (X u) - 1) := by
  rcases eq_or_lt_of_le hB0 with rfl | hBpos
  · have hX0 : EqOn (fun u => Complex.exp (X u) - 1) (fun _ => 0) (Icc 0 U) := fun u hu => by
      have h0 : ‖X u‖ ≤ 0 * (1 + u) ^ (p - (0 : ℕ)) := by simpa using hX.2 0 (Nat.zero_le _) u hu
      have : X u = 0 := norm_le_zero_iff.mp (by simpa using h0)
      simp [this]
    have hcd : ContDiffOn ℝ n (fun u => Complex.exp (X u) - 1) (Icc 0 U) :=
      (Complex.contDiff_exp.comp_contDiffOn hX.1).sub contDiffOn_const
    refine ⟨hcd, fun r hr u hu => ?_⟩
    rw [← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedFDerivWithin_congr hX0 hu r, norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_const]
    split_ifs <;> simp
  have hDu : UniqueDiffOn ℝ (Icc 0 U) := uniqueDiffOn_Icc hU
  have hcd : ContDiffOn ℝ n (fun u => Complex.exp (X u) - 1) (Icc 0 U) :=
    (Complex.contDiff_exp.comp_contDiffOn hX.1).sub contDiffOn_const
  refine ⟨hcd, fun r hr u hu => ?_⟩
  have hu0 : 0 ≤ u := hu.1
  have h1u0 : 0 < 1 + u := by linarith
  set R₀ : ℝ := 1 + u
  set ε : ℝ := B * R₀ ^ p
  have hε0 : 0 < ε := mul_pos hBpos (Real.rpow_pos_of_pos h1u0 p)
  have hε1 : ε ≤ 1 := by
    calc ε ≤ B * (1 + U) ^ p := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow h1u0.le (by linarith [hu.2]) hp0) hB0
      _ ≤ 1 := hBU
  have hXu : ‖X u‖ ≤ ε := by simpa using hX.2 0 (Nat.zero_le _) u hu
  have hexp_u : ‖Complex.exp (X u)‖ ≤ 3 := by
    rw [Complex.norm_exp]
    have hre : (X u).re ≤ 1 := (Complex.re_le_norm _).trans (hXu.trans hε1)
    exact (Real.exp_le_exp.mpr hre).trans (by linarith [Real.exp_one_lt_d9])
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · have hb := Complex.exp_bound (hXu.trans hε1) (n := 1) (by norm_num)
    simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
      Nat.succ_eq_add_one, Nat.factorial_one, mul_one] at hb
    rw [iteratedDerivWithin_zero, Nat.cast_zero, sub_zero]
    have hfac1 : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
    calc ‖Complex.exp (X u) - 1‖ ≤ ‖X u‖ * 2 := by simpa using hb
      _ ≤ ε * 2 := mul_le_mul_of_nonneg_right hXu (by norm_num)
      _ ≤ 3 * (n.factorial : ℝ) * B * R₀ ^ p := by
        have : ε * 2 ≤ 3 * (n.factorial : ℝ) * ε := by nlinarith [hfac1, hε0]
        refine this.trans_eq (by dsimp only [ε]; ring)
  · let ψ : ℝ → ℝ := fun v => u + R₀ * v
    let S : Set ℝ := ψ ⁻¹' Icc 0 U
    have hSu : UniqueDiffOn ℝ S := preimage_affine_uniqueDiffOn hU h1u0
    have hu_aff : u + R₀ * 0 ∈ Icc 0 U := by simpa using hu
    have h0S : (0 : ℝ) ∈ S := hu_aff
    have hψ_maps : MapsTo ψ S (Icc 0 U) := fun _ hv => hv
    have hψ_cd : ContDiffOn ℝ n ψ S := (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn
    let H : ℝ → ℂ := fun v => ((ε⁻¹ : ℝ) : ℂ) * X (ψ v)
    let G : ℂ → ℂ := fun w => Complex.exp (((ε : ℝ) : ℂ) * w) - 1
    have hH_cd : ContDiffOn ℝ n H S := contDiffOn_const.mul (hX.1.comp hψ_cd hψ_maps)
    have hG_cd : ContDiffOn ℝ n G univ :=
      ((Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id)).sub contDiff_const).contDiffOn
    have hH_bd : ∀ j : ℕ, 1 ≤ j → j ≤ r → ‖iteratedFDerivWithin ℝ j H S 0‖ ≤ 1 ^ j := by
      intro j hj1 hjr
      rw [one_pow, norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
      have hHeq : H = fun v => ((ε⁻¹ : ℝ) : ℂ) * (X ∘ ψ) v := rfl
      rw [hHeq, iteratedDerivWithin_const_mul h0S hSu ((ε⁻¹ : ℝ) : ℂ)
        ((hX.1.comp hψ_cd hψ_maps).contDiffWithinAt h0S |>.of_le (by exact_mod_cast (hjr.trans hr)))]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε0)]
      rw [iteratedDerivWithin_comp_affine hDu hSu hX.1 (hjr.trans hr) hu_aff]
      simp only [mul_zero, add_zero, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos h1u0]
      have hXj := hX.2 j (hjr.trans hr) u hu
      have hpow : R₀ ^ j * (B * R₀ ^ (p - (j : ℝ))) = ε := by
        have h1 : R₀ ^ (p - (j : ℝ)) = R₀ ^ p * (R₀ ^ j)⁻¹ := by
          rw [Real.rpow_sub h1u0, Real.rpow_natCast, div_eq_mul_inv]
        rw [h1]; dsimp only [ε]; field_simp [h1u0.ne']
      calc ε⁻¹ * (R₀ ^ j * ‖iteratedDerivWithin j X (Icc 0 U) u‖)
          ≤ ε⁻¹ * (R₀ ^ j * (B * R₀ ^ (p - (j : ℝ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXj (pow_nonneg h1u0.le j)) (inv_pos.mpr hε0).le
        _ = 1 := by rw [hpow, inv_mul_cancel₀ hε0.ne']
    have hG_bd : ∀ i ≤ r, ‖iteratedFDerivWithin ℝ i G univ (H 0)‖ ≤ 3 * ε := by
      intro i _
      rw [iteratedFDerivWithin_univ]
      have hGH0 : (((ε : ℝ) : ℂ) * H 0) = X u := by
        simp only [H, ψ, mul_zero, add_zero]
        rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hε0.ne', Complex.ofReal_one, one_mul]
      rcases i with _ | i
      · rw [norm_iteratedFDeriv_zero]
        change ‖Complex.exp (((ε : ℝ) : ℂ) * H 0) - 1‖ ≤ 3 * ε
        rw [hGH0]
        have hb := Complex.exp_bound (hXu.trans hε1) (n := 1) (by norm_num)
        simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
          Nat.succ_eq_add_one, Nat.factorial_one, mul_one] at hb
        have hb' : ‖Complex.exp (X u) - 1‖ ≤ ‖X u‖ * 2 := by simpa using hb
        linarith [hb', hXu]
      · refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
        rw [iteratedFDeriv_cexp_const_mul ((ε : ℝ) : ℂ) 1 (i + 1) (Nat.succ_pos i) (H 0) v,
          norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0, hGH0]
        have hε_pow : ε ^ (i + 1) ≤ ε := pow_le_of_le_one hε0.le hε1 (Nat.succ_ne_zero i)
        have hprod_le : ‖∏ k : Fin (i + 1), v k‖ ≤ ∏ k : Fin (i + 1), ‖v k‖ := (norm_prod _ _).le
        calc ε ^ (i + 1) * ‖Complex.exp (X u)‖ * ‖∏ k : Fin (i + 1), v k‖
            ≤ (ε * 3) * ∏ k : Fin (i + 1), ‖v k‖ := by
              have h1 : ε ^ (i + 1) * ‖Complex.exp (X u)‖ ≤ ε * 3 :=
                mul_le_mul hε_pow hexp_u (norm_nonneg _) hε0.le
              exact mul_le_mul h1 hprod_le (norm_nonneg _) (by positivity)
          _ = 3 * ε * ∏ k : Fin (i + 1), ‖v k‖ := by ring
    have hle := norm_iteratedFDerivWithin_comp_le (g := G) (f := H) (n := r) (N := n)
      hG_cd hH_cd (by exact_mod_cast hr) uniqueDiffOn_univ hSu (mapsTo_univ _ _) h0S
      (C := 3 * ε) (D := 1)
      (fun i hi => hG_bd i hi) (fun i hi1 hir => hH_bd i hi1 hir)
    have hcomp_eq : (G ∘ H) = (fun u => Complex.exp (X u) - 1) ∘ ψ := by
      ext v
      simp only [G, H, Function.comp]
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hε0.ne', Complex.ofReal_one, one_mul]
    have hgf_aff : iteratedDerivWithin r (G ∘ H) S 0 =
        R₀ ^ r * iteratedDerivWithin r (fun u => Complex.exp (X u) - 1) (Icc 0 U) u := by
      rw [hcomp_eq]
      have h := iteratedDerivWithin_comp_affine hDu hSu hcd hr hu_aff
      simpa [ψ, smul_eq_mul] using h
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin] at hle
    change ‖iteratedDerivWithin r (G ∘ H) S 0‖ ≤ _ at hle
    rw [hgf_aff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1u0, one_pow,
      mul_one] at hle
    have hpowr : (1 + u) ^ (p - (r : ℝ)) = R₀ ^ p / R₀ ^ r := by
      rw [Real.rpow_sub h1u0, Real.rpow_natCast]
    rw [hpowr]
    have hr_fac : (r.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hr
    have hbound : R₀ ^ r * ‖iteratedDerivWithin r (fun u => Complex.exp (X u) - 1) (Icc 0 U) u‖ ≤
        R₀ ^ r * (3 * (n.factorial : ℝ) * B * (R₀ ^ p / R₀ ^ r)) := by
      have heq : R₀ ^ r * (3 * (n.factorial : ℝ) * B * (R₀ ^ p / R₀ ^ r)) =
          (n.factorial : ℝ) * (3 * ε) := by
        dsimp only [ε]; field_simp [h1u0.ne']
      rw [heq]
      exact hle.trans (mul_le_mul_of_nonneg_right hr_fac (by positivity))
    exact le_of_mul_le_mul_left hbound (pow_pos h1u0 r)

/-- If `X ∈ S^p(B)` on `[0, U]` with `1 ≤ n`, `p ≥ 0`, and `B (1 + U)^p ≤ 1`, then
`exp(X) - 1 - X ∈ S^{2p}(3 · 2^n · n! · B²)`. -/
lemma FctSymClsOn.cexp_sub_one_sub {U : ℝ} (hU : 0 < U) {n : ℕ} (hn : 1 ≤ n) {p B : ℝ}
    (hp0 : 0 ≤ p) (hB0 : 0 ≤ B) (hBU : B * (1 + U) ^ p ≤ 1)
    {X : ℝ → ℂ} (hX : FctSymClsOn (Icc 0 U) n p B X) :
    FctSymClsOn (Icc 0 U) n (2 * p) (3 * 2 ^ n * (n.factorial : ℝ) * B ^ 2)
      (fun u => Complex.exp (X u) - 1 - X u) := by
  have hDu : UniqueDiffOn ℝ (Icc 0 U) := uniqueDiffOn_Icc hU
  have hcd : ContDiffOn ℝ n (fun u => Complex.exp (X u) - 1 - X u) (Icc 0 U) :=
    ((Complex.contDiff_exp.comp_contDiffOn hX.1).sub contDiffOn_const).sub hX.1
  have hE1 := hX.cexp_sub_one hU hp0 hB0 hBU
  have hXd := hX.derivWithin_Icc hU hn
  have hprod := (hE1.mono_n (Nat.sub_le n 1)).mul Icc_subset_Ici_self hDu hXd
  have hderiv_eq : EqOn (derivWithin (fun u => Complex.exp (X u) - 1 - X u) (Icc 0 U))
      (fun u => (Complex.exp (X u) - 1) * derivWithin X (Icc 0 U) u) (Icc 0 U) := by
    intro u hu
    have hXw : HasDerivWithinAt X (derivWithin X (Icc 0 U) u) (Icc 0 U) u :=
      (hX.1.differentiableOn (by exact_mod_cast (by omega : n ≠ 0)) u hu).hasDerivWithinAt
    have hd : HasDerivWithinAt (fun z => Complex.exp (X z) - 1 - X z)
        ((Complex.exp (X u) - 1) * derivWithin X (Icc 0 U) u) (Icc 0 U) u := by
      have h1 := ((hXw.cexp.sub_const 1).sub hXw)
      refine h1.congr_deriv ?_; ring
    exact hd.derivWithin (hDu u hu)
  refine ⟨hcd, fun r hr u hu => ?_⟩
  have hu0 : 0 ≤ u := hu.1
  have h1u0 : 0 < 1 + u := by linarith
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · have hXu : ‖X u‖ ≤ B * (1 + u) ^ p := by simpa using hX.2 0 (Nat.zero_le _) u hu
    have hX1 : ‖X u‖ ≤ 1 := hXu.trans (by
      calc B * (1 + u) ^ p ≤ B * (1 + U) ^ p :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h1u0.le (by linarith [hu.2]) hp0) hB0
        _ ≤ 1 := hBU)
    have hb := Complex.exp_bound hX1 (n := 2) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
      Nat.succ_eq_add_one, Nat.reduceAdd, Nat.factorial_two] at hb
    have hsub : Complex.exp (X u) - (1 + X u) = Complex.exp (X u) - 1 - X u := by ring
    rw [hsub] at hb
    have hb' : ‖Complex.exp (X u) - 1 - X u‖ ≤ ‖X u‖ ^ 2 :=
      hb.trans (mul_le_of_le_one_right (sq_nonneg _) (by norm_num))
    rw [iteratedDerivWithin_zero, Nat.cast_zero, sub_zero]
    have hfac1 : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
    have h2n1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    calc ‖Complex.exp (X u) - 1 - X u‖ ≤ ‖X u‖ ^ 2 := hb'
      _ ≤ (B * (1 + u) ^ p) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hXu 2
      _ = B ^ 2 * (1 + u) ^ (2 * p) := by
        rw [mul_pow, ← Real.rpow_natCast ((1 + u) ^ p) 2, ← Real.rpow_mul h1u0.le, mul_comm p]
        norm_num
      _ ≤ 3 * 2 ^ n * (n.factorial : ℝ) * B ^ 2 * (1 + u) ^ (2 * p) := by
        have : 1 ≤ 3 * 2 ^ n * (n.factorial : ℝ) := by nlinarith
        have hpos : 0 ≤ B ^ 2 * (1 + u) ^ (2 * p) := by positivity
        nlinarith
  · rw [← Nat.sub_add_cancel hr0, iteratedDerivWithin_succ',
      ← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedFDerivWithin_congr hderiv_eq hu (r - 1),
      norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    have hbd := hprod.2 (r - 1) (by omega) u hu
    have hexp1 : (p + (p - 1) - ((r - 1 : ℕ) : ℝ)) = 2 * p - (((r - 1 + 1 : ℕ) : ℝ)) := by
      have hsub : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by rw [Nat.cast_sub hr0, Nat.cast_one]
      have hadd : ((r - 1 + 1 : ℕ) : ℝ) = (r : ℝ) := by exact_mod_cast Nat.sub_add_cancel hr0
      rw [hsub, hadd]; ring
    have h2le : (2 : ℝ) ^ (n - 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)
    rw [hexp1] at hbd
    refine hbd.trans ?_
    have hpow0 : 0 ≤ (1 + u) ^ (2 * p - (((r - 1 + 1 : ℕ) : ℝ))) := (Real.rpow_pos_of_pos h1u0 _).le
    have hc_le : 2 ^ (n - 1) * (3 * (n.factorial : ℝ) * B) * B ≤ 3 * 2 ^ n * (n.factorial : ℝ) * B ^ 2 := by
      have : 0 ≤ 3 * (n.factorial : ℝ) * B ^ 2 := by positivity
      calc 2 ^ (n - 1) * (3 * (n.factorial : ℝ) * B) * B
          = 2 ^ (n - 1) * (3 * (n.factorial : ℝ) * B ^ 2) := by ring
        _ ≤ 2 ^ n * (3 * (n.factorial : ℝ) * B ^ 2) := mul_le_mul_of_nonneg_right h2le this
        _ = 3 * 2 ^ n * (n.factorial : ℝ) * B ^ 2 := by ring
    exact mul_le_mul_of_nonneg_right hc_le hpow0

/-- Bound sequence for `(1 + X)⁻¹ ∈ 𝒮^0` by Leibniz induction on `m`. -/
def invSymBound : ℕ → ℝ
  | 0 => 2
  | m + 1 => max (invSymBound m) (4 ^ m * (invSymBound m) ^ 2)

lemma invSymBound_nonneg (m : ℕ) : 0 ≤ invSymBound m := by
  induction m with
  | zero => simp [invSymBound]
  | succ m ih => exact le_max_of_le_left ih

lemma invSymBound_mono {m n : ℕ} (hmn : m ≤ n) : invSymBound m ≤ invSymBound n := by
  induction hmn with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (le_max_left _ _)

/-- If `X ∈ S^p(B)` on `[0, U]` with `p ≥ 0` and `B (1 + U)^p ≤ 1/2`, then
`(1 + X)⁻¹ ∈ S^0(invSymBound n)`. -/
lemma FctSymClsOn.inv_one_add {U : ℝ} (hU : 0 < U) {n : ℕ} {p B : ℝ}
    (hp0 : 0 ≤ p) (hB0 : 0 ≤ B) (hBU : B * (1 + U) ^ p ≤ 1 / 2)
    {X : ℝ → ℂ} (hX : FctSymClsOn (Icc 0 U) n p B X) :
    FctSymClsOn (Icc 0 U) n 0 (invSymBound n) (fun u => (1 + X u)⁻¹) := by
  have hDu : UniqueDiffOn ℝ (Icc 0 U) := uniqueDiffOn_Icc hU
  have hne : ∀ u ∈ Icc 0 U, 1 + X u ≠ 0 := fun u hu => by
    have h1u0 : 0 < 1 + u := by linarith [hu.1]
    have hXu : ‖X u‖ ≤ B * (1 + u) ^ p := by simpa using hX.2 0 (Nat.zero_le _) u hu
    have hle : B * (1 + u) ^ p ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h1u0.le (by linarith [hu.2]) hp0) hB0).trans hBU
    have hlo : 1 / 2 ≤ ‖1 + X u‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-X u)
      simp only [norm_one, norm_neg, sub_neg_eq_add] at this
      linarith
    exact norm_pos_iff.mp (by linarith)
  have hcd_all : ContDiffOn ℝ n (fun u => (1 + X u)⁻¹) (Icc 0 U) :=
    (contDiffOn_const.add hX.1).inv hne
  have hmain : ∀ m : ℕ, m ≤ n → FctSymClsOn (Icc 0 U) m 0 (invSymBound m) (fun u => (1 + X u)⁻¹) := by
    intro m
    induction m with
    | zero =>
      intro hm
      refine ⟨hcd_all.of_le (by exact_mod_cast hm), fun r hr u hu => ?_⟩
      rcases Nat.le_zero.mp hr with rfl
      rw [iteratedDerivWithin_zero, Nat.cast_zero, sub_zero, Real.rpow_zero, mul_one, norm_inv]
      have h1u0 : 0 < 1 + u := by linarith [hu.1]
      have hXu : ‖X u‖ ≤ B * (1 + u) ^ p := by simpa using hX.2 0 (Nat.zero_le _) u hu
      have hle : B * (1 + u) ^ p ≤ 1 / 2 :=
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h1u0.le (by linarith [hu.2]) hp0) hB0).trans hBU
      have hlo : 1 / 2 ≤ ‖1 + X u‖ := by
        have := norm_sub_norm_le (1 : ℂ) (-X u)
        simp only [norm_one, norm_neg, sub_neg_eq_add] at this
        linarith
      rw [inv_le_iff_one_le_mul₀ (by linarith)]
      simpa [invSymBound] using (by linarith : 1 ≤ 2 * ‖1 + X u‖)
    | succ m ih =>
      intro hmn
      have ihm := ih (Nat.le_of_succ_le hmn)
      have hcd_m1 : ContDiffOn ℝ (m + 1 : ℕ) (fun u => (1 + X u)⁻¹) (Icc 0 U) :=
        hcd_all.of_le (by exact_mod_cast hmn)
      have hY2 := ihm.mul Icc_subset_Ici_self hDu ihm
      have hX_m1 : FctSymClsOn (Icc 0 U) (m + 1) p B X := hX.mono_n hmn
      have hXd := hX_m1.derivWithin_Icc hU (Nat.succ_pos m)
      have hXd0 : FctSymClsOn (Icc 0 U) m (-1) (B * (1 + U) ^ p) (derivWithin X (Icc 0 U)) := by
        simpa [Nat.add_sub_cancel, show (p - 1) - (-1 : ℝ) = p by ring] using
          (hXd.shrink_p hU.le hB0 (by linarith : (-1 : ℝ) ≤ p - 1))
      have hprod := (hY2.neg).mul Icc_subset_Ici_self hDu hXd0
      have hderiv_eq : EqOn (derivWithin (fun u => (1 + X u)⁻¹) (Icc 0 U))
          (fun u => -((1 + X u)⁻¹ * (1 + X u)⁻¹) * derivWithin X (Icc 0 U) u) (Icc 0 U) := by
        intro u hu
        have hXw : HasDerivWithinAt X (derivWithin X (Icc 0 U) u) (Icc 0 U) u :=
          (hX.1.differentiableOn (by exact_mod_cast (by omega : n ≠ 0)) u hu).hasDerivWithinAt
        have h1X : HasDerivWithinAt (fun z => 1 + X z) (derivWithin X (Icc 0 U) u) (Icc 0 U) u :=
          (hasDerivWithinAt_const u (Icc 0 U) (1 : ℂ)).add hXw |>.congr_deriv (by simp)
        have hinv := h1X.inv (hne u hu)
        have hd_eq : derivWithin (fun u => (1 + X u)⁻¹) (Icc 0 U) u =
            -derivWithin X (Icc 0 U) u / (1 + X u) ^ 2 := hinv.derivWithin (hDu u hu)
        rw [hd_eq]; field_simp [hne u hu]
      refine ⟨hcd_m1, fun r hr u hu => ?_⟩
      have h1u0 : 0 < 1 + u := by linarith [hu.1]
      have hpow0 : 0 ≤ (1 + u) ^ ((0 : ℝ) - r) := (Real.rpow_pos_of_pos h1u0 _).le
      rcases Nat.lt_or_eq_of_le hr with hlt | rfl
      · refine (ihm.2 r (Nat.lt_succ_iff.mp hlt) u hu).trans ?_
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpow0
      · rw [iteratedDerivWithin_succ', ← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
          iteratedFDerivWithin_congr hderiv_eq hu m, norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
        have hbd := hprod.2 m le_rfl u hu
        have hexp : (0 : ℝ) + 0 + (-1 : ℝ) - (m : ℝ) = (0 : ℝ) - ((m + 1 : ℕ) : ℝ) := by
          push_cast; ring
        rw [hexp] at hbd
        refine hbd.trans (mul_le_mul_of_nonneg_right ?_ hpow0)
        have hBm : 0 ≤ invSymBound m := invSymBound_nonneg m
        have h4 : (2 : ℝ) ^ m * (2 ^ m * invSymBound m * invSymBound m) = 4 ^ m * invSymBound m ^ 2 := by
          have : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
          rw [this]; ring
        calc 2 ^ m * (2 ^ m * invSymBound m * invSymBound m) * (B * (1 + U) ^ p)
            ≤ 2 ^ m * (2 ^ m * invSymBound m * invSymBound m) * (1 / 2) := by
              gcongr
          _ ≤ 4 ^ m * invSymBound m ^ 2 := by
              rw [h4]
              linarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) m) (sq_nonneg (invSymBound m))]
          _ ≤ invSymBound (m + 1) := le_max_right _ _
  exact hmain n le_rfl

end FormalResearch.SignUncertainty
