module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumTaylor

/-!
# Paper J, Layer 2: the `C^{M+1}` norm of the Taylor-substituted coefficients `S_l` from the joint norm bound `Sigma_bdd` (L2.S3, L2.S6)

Source: Paper J `app_thmA.tex`, proof of `thm:smo-spec`, paragraph "Substitution `t = h`" (`S^I_l = sum_{i+j=l} (1/i!) d_t^i Sigma_j(X, 0)`,
`S^I_l in C^{M+1}`) and the last paragraph ("these norms are uniform in `mu`", the `C^{M+1}` norms of the `S_l` bounded in terms of the `C^{2M+1}`
norms of the `Sigma_j`).

## Proved here (axiom-pinned)

* `norm_iter_dtN_le`: for `g in C^{k+n}(s)` on a set with unique differentials, `||D^k (d_t^n g)|| <= ||D^{k+n} g||` (within `s`, pointwise): the partial derivative in the
  direction `(0,1)` of norm one lowers the order and costs nothing (induction on `n`, `norm_iteratedFDerivWithin_fderivWithin` and
  `norm_iteratedFDerivWithin_clm_apply_const`).
* `scoef_norm_bound` (**the `C^{M+1}` norm of `S_l` from `Sigma_bdd`**): if `||iteratedFDerivWithin R i (Sigma_j) (J x [-t0,t0]) p|| <= C` for `i <= 2M+1`, `p` in the
  set, then `|iteratedDerivWithin i (Scoef Sigma l) J x| <= (M+1) C` for `l <= M`, `i <= M+1`, `x in J` (restriction to `t = 0` is composition with `inl`
  of norm `<= 1`, `ContinuousLinearMap.iteratedFDerivWithin_comp_right`).

## Differences from the paper

None (the paper's constant is not tracked).  `J` is an interval of positive length and `t0 > 0`.

## Not formalised

Nothing beyond the statement above.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Nat Set FormalResearch.JacobiEigenvectors.Charts

/-- `||D^k (d_t^n g)|| <= ||D^{k+n} g||` within `s` (see the module docstring). -/
lemma norm_iter_dtN_le (s : Set (ℝ × ℝ)) (hs : UniqueDiffOn ℝ s) {g : ℝ × ℝ → ℝ} (n : ℕ) :
    ∀ k : ℕ, ContDiffOn ℝ ((k + n : ℕ) : WithTop ℕ∞) g s → ∀ p ∈ s,
      ‖iteratedFDerivWithin ℝ k (dtN s g n) s p‖ ≤ ‖iteratedFDerivWithin ℝ (k + n) g s p‖ := by
  induction n with
  | zero => intro k hk p hp; simp [dtN]
  | succ n ih =>
    intro k hk p hp
    have h1 : ContDiffOn ℝ ((k + 1 + n : ℕ) : WithTop ℕ∞) g s := by
      have : k + 1 + n = k + (n + 1) := by ring
      rw [this]; exact hk
    have hd : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (dtN s g n) s := dtN_contDiffOn s hs n (k + 1) h1
    have hfd : ContDiffOn ℝ (k : WithTop ℕ∞) (fderivWithin ℝ (dtN s g n) s) s :=
      hd.fderivWithin hs (m := (k : WithTop ℕ∞)) (by exact_mod_cast le_refl (k + 1))
    show ‖iteratedFDerivWithin ℝ k (fun q => fderivWithin ℝ (dtN s g n) s q ((0 : ℝ), (1 : ℝ))) s p‖ ≤ _
    have h2 := norm_iteratedFDerivWithin_clm_apply_const (c := ((0 : ℝ), (1 : ℝ))) (hfd.contDiffWithinAt hp) hs hp le_rfl
    have h3 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
    rw [h3, one_mul] at h2
    refine h2.trans ?_
    rw [norm_iteratedFDerivWithin_fderivWithin hs hp]
    have := ih (k + 1) h1 p hp
    have e : k + 1 + n = k + (n + 1) := by ring
    rwa [e] at this

/-- The `i`-th derivative of the restriction to `t = 0` of `d_t^n g`: bounded by the `(i+n)`-th derivative of `g`. -/
lemma norm_slice_dtN_le (J : Set ℝ) (t0 : ℝ) (ht0 : 0 < t0) (hJ : UniqueDiffOn ℝ J) {g : ℝ × ℝ → ℝ} (n i : ℕ)
    (hg : ContDiffOn ℝ ((i + n : ℕ) : WithTop ℕ∞) g (J ×ˢ Icc (-t0) t0)) {x : ℝ} (hx : x ∈ J) {C : ℝ}
    (hC : ‖iteratedFDerivWithin ℝ (i + n) g (J ×ˢ Icc (-t0) t0) (x, 0)‖ ≤ C) :
    |iteratedDerivWithin i (fun X => dtN (J ×ˢ Icc (-t0) t0) g n (X, 0)) J x| ≤ C := by
  set s : Set (ℝ × ℝ) := J ×ˢ Icc (-t0) t0 with hs
  have hU : UniqueDiffOn ℝ s := hJ.prod (uniqueDiffOn_Icc (by linarith))
  have hx0 : (x, (0 : ℝ)) ∈ s := ⟨hx, by constructor <;> linarith⟩
  have hd : ContDiffOn ℝ (i : WithTop ℕ∞) (dtN s g n) s := dtN_contDiffOn s hU n i hg
  have hpre : ContinuousLinearMap.inl ℝ ℝ ℝ ⁻¹' s = J := by
    ext y
    simp only [Set.mem_preimage, hs, Set.mem_prod, ContinuousLinearMap.inl_apply, Set.mem_Icc]
    constructor
    · intro h; exact h.1
    · intro h; exact ⟨h, by constructor <;> linarith⟩
  have hU' : UniqueDiffOn ℝ (ContinuousLinearMap.inl ℝ ℝ ℝ ⁻¹' s) := by rw [hpre]; exact hJ
  have h1 := (ContinuousLinearMap.inl ℝ ℝ ℝ).iteratedFDerivWithin_comp_right hd hU hU' (x := x)
    (by simpa using hx0) (i := i) le_rfl
  rw [hpre] at h1
  have h2 : (fun X => dtN s g n (X, 0)) = (dtN s g n) ∘ (ContinuousLinearMap.inl ℝ ℝ ℝ) := by
    funext X; simp
  rw [h2, ← Real.norm_eq_abs, ← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, h1]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hn1 : ∏ _j : Fin i, ‖ContinuousLinearMap.inl ℝ ℝ ℝ‖ ≤ 1 := by
    rw [Finset.prod_const]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inl_le_one ℝ ℝ ℝ)
  have h3 := norm_iter_dtN_le s hU n i hg (x, 0) hx0
  have h4 : ‖iteratedFDerivWithin ℝ i (dtN s g n) s ((ContinuousLinearMap.inl ℝ ℝ ℝ) x)‖ ≤ C := by
    simpa using h3.trans hC
  calc ‖iteratedFDerivWithin ℝ i (dtN s g n) s ((ContinuousLinearMap.inl ℝ ℝ ℝ) x)‖ *
        ∏ _j : Fin i, ‖ContinuousLinearMap.inl ℝ ℝ ℝ‖ ≤ ‖iteratedFDerivWithin ℝ i (dtN s g n) s ((ContinuousLinearMap.inl ℝ ℝ ℝ) x)‖ * 1 :=
        mul_le_mul_of_nonneg_left hn1 (norm_nonneg _)
    _ ≤ C := by rw [mul_one]; exact h4

/-- The taylor coefficient is `(n!)^{-1} d_t^n g (X, 0)` for `g = Sigma_j` on `J x [-t0, t0]`. -/
lemma taylorCoeff_eq_dtN {f : ℝ → ℝ → ℝ} {J : Set ℝ} {t0 : ℝ} (ht0 : 0 < t0) (hJ : UniqueDiffOn ℝ J) (n : ℕ)
    (hf : JetRegJ f J t0 n) {X : ℝ} (hX : X ∈ J) :
    taylorCoeff f n X = (n ! : ℝ)⁻¹ * dtN (J ×ˢ Icc (-t0) t0) (fun p : ℝ × ℝ => f p.1 p.2) n (X, 0) := by
  set s : Set (ℝ × ℝ) := J ×ˢ Icc (-t0) t0 with hs
  have hU : UniqueDiffOn ℝ s := hJ.prod (uniqueDiffOn_Icc (by linarith))
  unfold taylorCoeff
  rw [iteratedDeriv_dtN s hU (X := X) (t0 := t0) (fun u hu => ⟨hX, Ioo_subset_Icc_self hu⟩) n hf 0 ⟨by linarith, ht0⟩]

/-- **The `C^{M+1}` norm of `S_l` from the joint norm bound of the `Sigma_j`** (see the module docstring). -/
theorem scoef_norm_bound {Sig : ℕ → ℝ → ℝ → ℝ} {M : ℕ} {J : Set ℝ} {t0 : ℝ} (hJ : UniqueDiffOn ℝ J) (ht0 : 0 < t0)
    (hreg : ∀ j ≤ M, JetRegJ (Sig j) J t0 (2 * M + 1)) (C : ℝ)
    (hb : ∀ j ≤ M, ∀ i ≤ 2 * M + 1, ∀ p ∈ J ×ˢ Icc (-t0) t0,
      ‖iteratedFDerivWithin ℝ i (fun q : ℝ × ℝ => Sig j q.1 q.2) (J ×ˢ Icc (-t0) t0) p‖ ≤ C)
    {l : ℕ} (hl : l ≤ M) {i : ℕ} (hi : i ≤ M + 1) {x : ℝ} (hx : x ∈ J) :
    |iteratedDerivWithin i (Scoef Sig l) J x| ≤ (M + 1) * C := by
  set s : Set (ℝ × ℝ) := J ×ˢ Icc (-t0) t0 with hs
  have hU : UniqueDiffOn ℝ s := hJ.prod (uniqueDiffOn_Icc (by linarith))
  have hC0 : 0 ≤ C := by
    have := hb 0 (Nat.zero_le _) 0 (Nat.zero_le _) (x, 0) ⟨hx, by constructor <;> linarith⟩
    exact (norm_nonneg _).trans this
  -- the term functions
  set F : ℕ → ℝ → ℝ := fun j X => ((l - j)! : ℝ)⁻¹ * dtN s (fun p : ℝ × ℝ => Sig j p.1 p.2) (l - j) (X, 0) with hF
  have hmem : ∀ j ∈ range (l + 1), j ≤ M ∧ i + (l - j) ≤ 2 * M + 1 := by
    intro j hj
    have := Finset.mem_range.mp hj
    constructor <;> omega
  have heq : EqOn (Scoef Sig l) (fun X => ∑ j ∈ range (l + 1), F j X) J := by
    intro X hX'
    unfold Scoef
    refine Finset.sum_congr rfl (fun j hj => ?_)
    obtain ⟨hjM, hij⟩ := hmem j hj
    exact taylorCoeff_eq_dtN ht0 hJ (l - j) ((hreg j hjM).of_le (by exact_mod_cast (by omega : l - j ≤ 2 * M + 1))) hX'
  have hcd : ∀ j ∈ range (l + 1), ContDiffWithinAt ℝ (i : WithTop ℕ∞) (F j) J x := by
    intro j hj
    obtain ⟨hjM, hij⟩ := hmem j hj
    have hg : ContDiffOn ℝ ((i + (l - j) : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℝ => Sig j p.1 p.2) s :=
      (hreg j hjM).of_le (by exact_mod_cast hij)
    have hd : ContDiffOn ℝ (i : WithTop ℕ∞) (dtN s (fun p : ℝ × ℝ => Sig j p.1 p.2) (l - j)) s := dtN_contDiffOn s hU (l - j) i hg
    have hc : ContDiffOn ℝ (i : WithTop ℕ∞) (fun X => dtN s (fun p : ℝ × ℝ => Sig j p.1 p.2) (l - j) (X, 0)) J :=
      hd.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun X hX' => ⟨hX', by constructor <;> linarith⟩)
    exact (contDiffOn_const.mul hc).contDiffWithinAt hx
  have hsumfun : (fun X => ∑ j ∈ range (l + 1), F j X) = ∑ j ∈ range (l + 1), F j := by
    funext X; simp [Finset.sum_apply]
  have hterm : ∀ j ∈ range (l + 1), |iteratedDerivWithin i (F j) J x| ≤ C := by
    intro j hj
    obtain ⟨hjM, hij⟩ := hmem j hj
    have hg : ContDiffOn ℝ ((i + (l - j) : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℝ => Sig j p.1 p.2) s :=
      (hreg j hjM).of_le (by exact_mod_cast hij)
    have hd : ContDiffOn ℝ (i : WithTop ℕ∞) (dtN s (fun p : ℝ × ℝ => Sig j p.1 p.2) (l - j)) s := dtN_contDiffOn s hU (l - j) i hg
    have hc : ContDiffOn ℝ (i : WithTop ℕ∞) (fun X => dtN s (fun p : ℝ × ℝ => Sig j p.1 p.2) (l - j) (X, 0)) J :=
      hd.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun X hX' => ⟨hX', by constructor <;> linarith⟩)
    have hmul : iteratedDerivWithin i (F j) J x
        = ((l - j)! : ℝ)⁻¹ * iteratedDerivWithin i (fun X => dtN s (fun p : ℝ × ℝ => Sig j p.1 p.2) (l - j) (X, 0)) J x :=
      iteratedDerivWithin_const_mul hx hJ _ (hc.contDiffWithinAt hx)
    rw [hmul, abs_mul]
    have hslice := norm_slice_dtN_le J t0 ht0 hJ (g := fun p : ℝ × ℝ => Sig j p.1 p.2) (l - j) i hg hx
      (C := C) (hb j hjM (i + (l - j)) hij (x, 0) ⟨hx, by constructor <;> linarith⟩)
    have hc1 : |((l - j)! : ℝ)⁻¹| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
    calc |((l - j)! : ℝ)⁻¹| * |iteratedDerivWithin i (fun X => dtN s (fun p : ℝ × ℝ => Sig j p.1 p.2) (l - j) (X, 0)) J x|
        ≤ 1 * C := mul_le_mul hc1 hslice (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  rw [iteratedDerivWithin_congr heq hx, hsumfun, iteratedDerivWithin_sum hx hJ hcd]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ range (l + 1), |iteratedDerivWithin i (F j) J x| ≤ ∑ j ∈ range (l + 1), C := Finset.sum_le_sum hterm
    _ = ((l : ℝ) + 1) * C := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ ((M : ℝ) + 1) * C := by
        have : (l : ℝ) ≤ M := by exact_mod_cast hl
        nlinarith

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.norm_iter_dtN_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.norm_iter_dtN_le

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.scoef_norm_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.scoef_norm_bound

end FormalResearch.JacobiEigenvectors.TheoremA
