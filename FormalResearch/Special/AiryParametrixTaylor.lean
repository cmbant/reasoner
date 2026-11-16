module

public import FormalResearch.Special.LangerPhi
public import Mathlib

/-!
# Parametrix defect, part 1: local Taylor tools and the entire functions `Ch`, `Sh`

Tools for the Airy parametrix defect lemma (`AiryParametrixDefect`), no Airy functions yet.

* `apx_taylor_chain`, `apx_taylor_local`: a *local* mean-value Taylor chain (as `airyTaylor_chain` of
  `AiryShiftTaylor`, but the derivative hypotheses are only needed on the segment `[X, X+s]`) and its
  corollary for a function `f ∈ C^n` on an open set `U`: on every segment inside a compact `K ⊆ U`,
  `|f(x+s) - Σ_{k<n} f^{(k)}(x) s^k/k!| ≤ B |s|^n` with `B = sup_K |f^{(n)}|` (no `1/n!` gain).
* `apx_bound_iterate`: all `deriv^[k] f`, `k ≤ n`, are bounded on a compact `K ⊆ U`.
* `langerSinhc w = 2 (cosh √w)'(w) = sinh √w / √w` (`= sin √(-w)/√(-w)` for `w < 0`), the entire function
  `∑ wⁿ/(2n+1)!`, expressed through the existing `langerCosh` of `LangerPhi`; Taylor remainders of `Ch`,
  `Sh`, `Sh'` and of the combination `Sh + 2 w Sh'` (= `(σ ↦ σ Sh(ζσ²))' = Ch`), with `Ch = langerCosh`.

All statements are proved; the constants are existential.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace FormalResearch.Special

/-! ### Local Taylor chain -/

/-- One step of the local chain: if `|g'| ≤ B` on the segment `[0, s]` then `|g t - g 0| ≤ B |s|` there. -/
lemma apx_taylor_step {g g' : ℝ → ℝ} {s B : ℝ}
    (hg : ∀ t ∈ uIcc 0 s, HasDerivAt g (g' t) t)
    (hB : ∀ t ∈ uIcc 0 s, |g' t| ≤ B) : ∀ t ∈ uIcc 0 s, |g t - g 0| ≤ B * |s| := by
  intro t ht
  have h0 : (0 : ℝ) ∈ uIcc 0 s := left_mem_uIcc
  have hsub : uIcc 0 t ⊆ uIcc 0 s := uIcc_subset_uIcc h0 ht
  have := (convex_uIcc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := g') (C := B) (x := 0) (y := t)
    (fun x hx => (hg x (hsub hx)).hasDerivWithinAt) (fun x hx => by simpa using hB x (hsub hx))
    left_mem_uIcc right_mem_uIcc
  simp only [Real.norm_eq_abs, sub_zero] at this
  have hts : |t| ≤ |s| := by
    rcases le_total 0 s with hs | hs
    · rw [uIcc_of_le hs] at ht
      rw [abs_of_nonneg ht.1, abs_of_nonneg hs]; exact ht.2
    · rw [uIcc_of_ge hs] at ht
      rw [abs_of_nonpos ht.2, abs_of_nonpos hs]; linarith [ht.1]
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 h0)
  calc |g t - g 0| ≤ B * |t| := this
    _ ≤ B * |s| := mul_le_mul_of_nonneg_left hts hB0

/-- **Local Taylor chain.**  If `F k` has derivative `F (k+1)` at the points of the segment `[X, X+s]` for
`k < n` and `|F n| ≤ B` there, then `|F 0 (X+t) - Σ_{k<n} F k X t^k/k!| ≤ B |s|^n` for `t ∈ [0, s]`. -/
lemma apx_taylor_chain : ∀ (n : ℕ) (F : ℕ → ℝ → ℝ) (X s B : ℝ),
    (∀ k < n, ∀ t ∈ uIcc 0 s, HasDerivAt (F k) (F (k + 1) (X + t)) (X + t)) →
    (∀ t ∈ uIcc 0 s, |F n (X + t)| ≤ B) →
    ∀ t ∈ uIcc 0 s, |F 0 (X + t) - ∑ k ∈ Finset.range n, F k X * t ^ k / (k.factorial : ℝ)| ≤
      B * |s| ^ n := by
  intro n
  induction n with
  | zero =>
    intro F X s B _ hB t ht
    simpa using hB t ht
  | succ n ih =>
    intro F X s B hF hB t ht
    have hIH := ih (fun k => F (k + 1)) X s B
      (fun k hk t ht => hF (k + 1) (by omega) t ht) hB
    set g : ℝ → ℝ := fun t => F 0 (X + t) -
      ∑ k ∈ Finset.range (n + 1), F k X * t ^ k / (k.factorial : ℝ) with hgdef
    set g' : ℝ → ℝ := fun t => F 1 (X + t) -
      ∑ k ∈ Finset.range n, F (k + 1) X * t ^ k / (k.factorial : ℝ) with hg'def
    have hg : ∀ t ∈ uIcc 0 s, HasDerivAt g (g' t) t := by
      intro t ht
      have h1 : HasDerivAt (fun t => F 0 (X + t)) (F 1 (X + t)) t :=
        (hF 0 (by omega) t ht).comp_const_add X t
      have hterm : ∀ k ∈ Finset.range n, HasDerivAt
          (fun t : ℝ => F (k + 1) X * t ^ (k + 1) / ((k + 1).factorial : ℝ))
          (F (k + 1) X * t ^ k / (k.factorial : ℝ)) t := by
        intro k _
        have := (((hasDerivAt_pow (k + 1) t).const_mul (F (k + 1) X)).div_const
          ((k + 1).factorial : ℝ))
        refine this.congr_deriv ?_
        rw [Nat.factorial_succ]
        push_cast
        have : (k.factorial : ℝ) ≠ 0 := by positivity
        field_simp
      have h2 := (HasDerivAt.fun_sum hterm).add_const (F 0 X)
      have hP : (fun t : ℝ => ∑ k ∈ Finset.range (n + 1), F k X * t ^ k / (k.factorial : ℝ)) =
          fun t => ∑ k ∈ Finset.range n, F (k + 1) X * t ^ (k + 1) / ((k + 1).factorial : ℝ)
            + F 0 X := by
        funext t
        rw [Finset.sum_range_succ']
        simp
      have h3 := h1.sub h2
      rw [← hP] at h3
      exact h3
    have h0 : g 0 = 0 := by
      simp only [hgdef, add_zero]
      rw [Finset.sum_range_succ']
      simp
    have hstep := apx_taylor_step hg (s := s) (B := B * |s| ^ n) (fun t ht => by
      simpa [hg'def] using hIH t ht) t ht
    rw [h0, sub_zero] at hstep
    simpa [hgdef, pow_succ, mul_assoc] using hstep

/-! ### `C^n` functions on an open set: derivatives and bounds -/

/-- The first `n` iterated derivatives of a `C^n` function on an open set are differentiable there, with
derivative the next iterated derivative. -/
lemma apx_hasDerivAt_iterate {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) :
    ∀ k < n, ∀ x ∈ U, HasDerivAt (deriv^[k] f) (deriv^[k + 1] f x) x := by
  have hc : ∀ k : ℕ, k ≤ n → ContDiffOn ℝ ((n - k : ℕ) : ℕ) (deriv^[k] f) U := by
    intro k
    induction k with
    | zero => intro _; simpa using hf
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 : ContDiffOn ℝ ((n - (k + 1) : ℕ) : ℕ) (deriv (deriv^[k] f)) U :=
        h1.deriv_of_isOpen hU (by
          have : n - k = (n - (k + 1)) + 1 := by omega
          rw [this] at *
          exact_mod_cast le_refl _)
      rwa [Function.iterate_succ_apply']
  intro k hk x hx
  have h1 := hc k hk.le
  have hd : DifferentiableOn ℝ (deriv^[k] f) U :=
    h1.differentiableOn (by
      have : (n - k : ℕ) ≠ 0 := by omega
      exact_mod_cast this)
  have := (hd.differentiableAt (hU.mem_nhds hx)).hasDerivAt
  rwa [← Function.iterate_succ_apply' deriv k f] at this

/-- The `n`-th iterated derivative of a `C^n` function on an open set is continuous there (and so are the
lower ones). -/
lemma apx_continuousOn_iterate {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) : ∀ k ≤ n, ContinuousOn (deriv^[k] f) U := by
  have hc : ∀ k : ℕ, k ≤ n → ContDiffOn ℝ ((n - k : ℕ) : ℕ) (deriv^[k] f) U := by
    intro k
    induction k with
    | zero => intro _; simpa using hf
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 : ContDiffOn ℝ ((n - (k + 1) : ℕ) : ℕ) (deriv (deriv^[k] f)) U :=
        h1.deriv_of_isOpen hU (by
          have : n - k = (n - (k + 1)) + 1 := by omega
          rw [this] at *
          exact_mod_cast le_refl _)
      rwa [Function.iterate_succ_apply']
  intro k hk
  exact (hc k hk).continuousOn

/-- Bound of the iterated derivatives on a compact subset. -/
lemma apx_bound_iterate {f : ℝ → ℝ} {U K : Set ℝ} {n : ℕ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) (hK : IsCompact K) (hKU : K ⊆ U) (k : ℕ) (hk : k ≤ n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, |deriv^[k] f x| ≤ B := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    ((apx_continuousOn_iterate hU hf k hk).mono hKU)
  refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
  exact (hB x hx).trans (le_max_left _ _)

/-- **Local Taylor expansion of a `C^n` function.**  For a compact `K ⊆ U` (`U` open) there is `B ≥ 0` with
`|f(x+s) - Σ_{k<n} f^{(k)}(x) s^k/k!| ≤ B |s|^n` whenever the whole segment `[x, x+s]` lies in `K`. -/
lemma apx_taylor_local {f : ℝ → ℝ} {U K : Set ℝ} {n : ℕ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x s : ℝ, (∀ t ∈ uIcc 0 s, x + t ∈ K) →
      |f (x + s) - ∑ k ∈ Finset.range n, deriv^[k] f x * s ^ k / (k.factorial : ℝ)| ≤ B * |s| ^ n := by
  obtain ⟨B, hB0, hB⟩ := apx_bound_iterate hU hf hK hKU n le_rfl
  refine ⟨B, hB0, fun x s hxs => ?_⟩
  have h := apx_taylor_chain n (fun k => deriv^[k] f) x s B
    (fun k hk t ht => apx_hasDerivAt_iterate hU hf k hk (x + t) (hKU (hxs t ht)))
    (fun t ht => hB _ (hxs t ht)) s (by simp)
  simpa using h

/-! ### The entire functions `Ch = langerCosh` and `Sh` -/

/-- `Sh(w) = 2 Ch'(w) = ∑ wⁿ/(2n+1)!` (`= sinh √w / √w` for `w > 0`). -/
noncomputable def langerSinhc (w : ℝ) : ℝ := 2 * deriv langerCosh w

lemma contDiff_langerCosh : ContDiff ℝ ∞ langerCosh :=
  contDiff_iff_contDiffAt.2 fun w => (analyticAt_langerCosh w).contDiffAt

lemma contDiffOn_langerCosh (n : ℕ) : ContDiffOn ℝ n langerCosh Set.univ :=
  (contDiff_langerCosh.of_le (by exact_mod_cast le_top)).contDiffOn

lemma hasDerivAt_langerCosh (w : ℝ) : HasDerivAt langerCosh (deriv langerCosh w) w :=
  ((contDiff_infty_iff_deriv.1 contDiff_langerCosh).1 w).hasDerivAt

lemma hasDerivAt_langerCosh' (w : ℝ) :
    HasDerivAt (deriv langerCosh) (deriv (deriv langerCosh) w) w :=
  ((contDiff_infty_iff_deriv.1 (contDiff_infty_iff_deriv.1 contDiff_langerCosh).2).1 w).hasDerivAt

lemma apx_iterate_langerCosh_zero (k : ℕ) :
    deriv^[k] langerCosh 0 = (k.factorial : ℝ) / ((2 * k).factorial : ℝ) := by
  rw [← iteratedDeriv_eq_iterate]; exact iteratedDeriv_langerCosh_zero k

lemma apx_contDiffOn_deriv_langerCosh (n : ℕ) : ContDiffOn ℝ n (deriv langerCosh) Set.univ :=
  ((contDiff_infty_iff_deriv.1 contDiff_langerCosh).2.of_le (by exact_mod_cast le_top)).contDiffOn

lemma apx_contDiffOn_deriv2_langerCosh (n : ℕ) :
    ContDiffOn ℝ n (deriv (deriv langerCosh)) Set.univ :=
  ((contDiff_infty_iff_deriv.1
    (contDiff_infty_iff_deriv.1 contDiff_langerCosh).2).2.of_le (by exact_mod_cast le_top)).contDiffOn

/-- Taylor remainders of `Ch`, `Ch'`, `Ch''` on `|w| ≤ W` (existential constant):
`Ch = 1 + w/2 + w²/24 + O(w³)`, `2 Ch' = 1 + w/6 + w²/120 + O(w³)`, `2 Ch'' = 1/6 + O(w)`, and
`2 Ch' + 4 w Ch'' = 1 + w/2 + w²/24 + O(w³)` (the derivative `(σ Sh(ζσ²))'` of the truncated sine). -/
theorem langerCosh_taylor (W : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℝ, |w| ≤ W →
    |langerCosh w - (1 + w / 2 + w ^ 2 / 24)| ≤ K * |w| ^ 3 ∧
    |2 * deriv langerCosh w - (1 + w / 6 + w ^ 2 / 120)| ≤ K * |w| ^ 3 ∧
    |2 * deriv (deriv langerCosh) w - 1 / 6| ≤ K * |w| ∧
    |2 * deriv langerCosh w + 4 * w * deriv (deriv langerCosh) w - (1 + w / 2 + w ^ 2 / 24)|
      ≤ K * |w| ^ 3 := by
  have hK : IsCompact (Icc (-|W|) |W|) := isCompact_Icc
  obtain ⟨B1, hB1, h1⟩ := apx_taylor_local (f := langerCosh) (U := Set.univ) (n := 3) isOpen_univ
    (contDiffOn_langerCosh 3) hK (subset_univ _)
  obtain ⟨B2, hB2, h2⟩ := apx_taylor_local (f := deriv langerCosh) (U := Set.univ) (n := 3)
    isOpen_univ (apx_contDiffOn_deriv_langerCosh 3) hK (subset_univ _)
  obtain ⟨B3, hB3, h3⟩ := apx_taylor_local (f := deriv (deriv langerCosh)) (U := Set.univ) (n := 2)
    isOpen_univ (apx_contDiffOn_deriv2_langerCosh 2) hK (subset_univ _)
  have hseg : ∀ w : ℝ, |w| ≤ W → ∀ t ∈ uIcc (0:ℝ) w, 0 + t ∈ Icc (-|W|) |W| := by
    intro w hw t ht
    have : |t| ≤ |w| := by
      rcases le_total 0 w with hs | hs
      · rw [uIcc_of_le hs] at ht
        rw [abs_of_nonneg ht.1, abs_of_nonneg hs]; exact ht.2
      · rw [uIcc_of_ge hs] at ht
        rw [abs_of_nonpos ht.2, abs_of_nonpos hs]; linarith [ht.1]
    have hW : |w| ≤ |W| := hw.trans (le_abs_self W)
    rw [zero_add]
    exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  refine ⟨B1 + 2 * B2 + 4 * B3 + 2 * B3 * |W| + 1, by positivity, fun w hw => ?_⟩
  have hW : |w| ≤ |W| := hw.trans (le_abs_self W)
  have e1 := h1 0 w (hseg w hw)
  have e2 := h2 0 w (hseg w hw)
  have e3 := h3 0 w (hseg w hw)
  have v0 : langerCosh 0 = 1 := by
    have := langerP_zero; unfold langerP at this; linarith
  have v1 : deriv langerCosh 0 = 1 / 2 := by rw [← deriv_langerP]; exact deriv_langerP_zero
  have v2 : deriv (deriv langerCosh) 0 = 1 / 12 := by
    rw [← deriv_langerP]; exact deriv2_langerP_zero
  have v3 : deriv (deriv (deriv langerCosh)) 0 = 1 / 120 := by
    rw [← deriv_langerP]; exact deriv3_langerP_zero
  have it2 : ∀ f : ℝ → ℝ, ∀ x, deriv^[2] f x = deriv (deriv f) x := by
    intro f x; simp [Function.iterate_succ_apply']
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Function.iterate_zero, id_eq,
    Function.iterate_one, it2, v0, v1, v2, v3, Nat.factorial] at e1 e2 e3
  norm_num at e1 e2 e3
  have hw0 := abs_nonneg w
  have hw3 : |w| ^ 3 = |w| * |w| ^ 2 := by ring
  have hw2 : |w| ^ 2 = w ^ 2 := sq_abs w
  have hw3' : 0 ≤ |w| ^ 3 := by positivity
  have hsq : w ^ 2 ≤ |W| * |w| := by rw [← hw2, sq]; exact mul_le_mul_of_nonneg_right hW hw0
  have p1 : B1 * |w| ^ 3 ≤ (B1 + 2 * B2 + 4 * B3 + 2 * B3 * |W| + 1) * |w| ^ 3 := by
    apply mul_le_mul_of_nonneg_right _ hw3'; nlinarith [mul_nonneg hB3 (abs_nonneg W)]
  have p2 : 2 * B2 * |w| ^ 3 ≤ (B1 + 2 * B2 + 4 * B3 + 2 * B3 * |W| + 1) * |w| ^ 3 := by
    apply mul_le_mul_of_nonneg_right _ hw3'; nlinarith [mul_nonneg hB3 (abs_nonneg W)]
  have p4 : (2 * B2 + 4 * B3) * |w| ^ 3 ≤ (B1 + 2 * B2 + 4 * B3 + 2 * B3 * |W| + 1) * |w| ^ 3 := by
    apply mul_le_mul_of_nonneg_right _ hw3'; nlinarith [mul_nonneg hB3 (abs_nonneg W)]
  have p3 : 2 * B3 * |W| * |w| + |w| / 60 ≤
      (B1 + 2 * B2 + 4 * B3 + 2 * B3 * |W| + 1) * |w| := by
    nlinarith [mul_nonneg hB3 (abs_nonneg W)]
  have q3 : B3 * w ^ 2 ≤ B3 * (|W| * |w|) := mul_le_mul_of_nonneg_left hsq hB3
  have q4 : |w| * (B3 * w ^ 2) = B3 * |w| ^ 3 := by rw [← hw2]; ring
  have hr : |4 * w * (deriv (deriv langerCosh) w - (1 / 12 + 1 / 120 * w))| ≤ 4 * B3 * |w| ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    have : |w| * |deriv (deriv langerCosh) w - (1 / 12 + 1 / 120 * w)| ≤ |w| * (B3 * w ^ 2) :=
      mul_le_mul_of_nonneg_left e3 hw0
    nlinarith [this, q4]
  rw [abs_le] at e1 e2 e3 hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith [e1.1, e1.2]
  · rw [abs_le]; constructor <;> linarith [e2.1, e2.2]
  · rw [abs_le]; constructor <;> linarith [e3.1, e3.2, q3, p3, le_abs_self w, neg_abs_le w]
  · rw [abs_le]; constructor <;> linarith [e2.1, e2.2, hr.1, hr.2]

end FormalResearch.Special
