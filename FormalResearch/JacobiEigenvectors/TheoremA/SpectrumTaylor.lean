module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.Regularity

/-!
# Paper J, Layer 2: the Taylor substitution `t = h` of the phase coefficients (L2.S3)

Source: Paper J `app_thmA.tex`, proof of `thm:smo-spec`, paragraph "Substitution `t = h`": with `Sigma_j in C^{2M+1}(J x [-t0,t0])`,
Taylor's formula in `t` gives, uniformly on `J`,
`Sigma(X,h,h) = sum_{l <= M} h^l S^J_l(X) + O(h^{M+1})`, `S^J_l(X) = sum_{i+j=l} (1/i!) d_t^i Sigma_j(X,0)`, with `S^J_l in C^{M+1}(J)` (eq:smo-BSr3).

## Proved here (axiom-pinned)

* `taylor_pt`: Taylor's formula with remainder for one function `g` of `t`, `C^{n+1}` on `(-t0, t0)` with `|g^{(n+1)}| <= C`:
  `|g(h) - sum_{i <= n} g^{(i)}(0) h^i / i!| <= C h^{n+1}` for `0 < h < t0`.
* `taylor_subst`: for one energy `X`, `|sum_{j<=M} h^j Sigma_j(X,h) - sum_{l<=M} h^l S_l(X)| <= (M+1) C h^{M+1}` (the double sum is regrouped by
  `Finset.sum_range_diag_flip`); `Scoef` is the coefficient `S_l`.
* `Scoef_contDiffOn`: `S_l in C^{M+1}(J)` for `l <= M`, from `JetRegJ (Sigma_j) J t0 (2M+1)` (`JetRegJ` is `ContDiffOn` on `J x [-t0,t0]`): the partial
  derivative in `t` (within the product set, `dtS`) lowers the differentiability class by one (`dtS_contDiffOn`, `dtN_contDiffOn`) and equals
  the one-variable iterated derivative of the slice (`iteratedDeriv_dtN`); evaluation at `t = 0` composes with a `C^infty` map.
* `taylor_bound_of_Sigma_bdd`: the `t`-derivative bound from the uniform joint norm bound (`Sigma_bdd`).
* `phase_substitution`: both statements at once; `Scoef_zero`, `Scoef_one`: `S_0 = Sigma_0(.,0)`, `S_1 = Sigma_1(.,0) + d_t Sigma_0(.,0)`.

## Differences from the paper and findings

* **Uniformity (F-S2-2): CONFIRMED, resolved by the field `BulkPhaseInputs.Sigma_bdd` (round 5).**  The remainder needs a bound for `d_t^{M-j+1} Sigma_j` on `J x (-t0,t0)`; `Sigma_reg` (`JetRegJ`) only
  gives continuity on the *closed* set for each `mu`, hence a bound for each `mu` but not uniform in `mu in K`.  `phase_substitution` keeps the bound as its hypothesis `hC`, and
  `taylor_bound_of_Sigma_bdd` derives `hC` from the joint norm bound of `Sigma_bdd` (`||iteratedFDerivWithin R i (Sigma_j) (J x [-t0,t0])|| <= C`, `i <= 2M+1`; via `dtN_eq_iterated`, `abs_dtN_le`).
  The `C^{M+1}` *norms* of `S_l` (needed by `SmoothExt`) need all mixed derivatives of order `<= 2M+1` of `Sigma_j`, i.e. the same field (not formalised here).
* `t0` is replaced by the open interval `(-t0, t0)` and the threshold is `h < t0` (the closed-interval statement follows by shrinking `t0`); `J` is any set
  with unique derivatives (an interval of positive length), no further condition.
* The coefficients use `iteratedDeriv` at `t = 0`, an interior point (so it is the derivative of the slice).

## Not formalised

The uniform `C^{M+1}` *norm* bound of the `S_l` (it is the bound of the mixed derivatives, see above).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Nat FormalResearch.JacobiEigenvectors.Charts

/-! ### Taylor's formula in `t` -/

lemma taylor_pt (g : ℝ → ℝ) (n : ℕ) (t0 C h : ℝ) (hh : 0 < h) (hht : h < t0)
    (hg : ContDiffOn ℝ (n + 1 : ℕ) g (Set.Ioo (-t0) t0))
    (hC : ∀ t ∈ Set.Ioo (-t0) t0, |iteratedDeriv (n + 1) g t| ≤ C) :
    |g h - ∑ i ∈ range (n + 1), (i ! : ℝ)⁻¹ * iteratedDeriv i g 0 * h ^ i| ≤ C * h ^ (n + 1) := by
  have hsub : Set.Icc 0 h ⊆ Set.Ioo (-t0) t0 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hdAt : ∀ x ∈ Set.Ioo (-t0) t0, ContDiffAt ℝ (n + 1 : ℕ) g x :=
    fun x hx => hg.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hU : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) h) := uniqueDiffOn_Icc hh
  have hgI : ContDiffOn ℝ (n + 1 : ℕ) g (Set.Icc 0 h) := hg.mono hsub
  have hf : ContDiffOn ℝ n g (Set.uIcc 0 h) := by
    rw [Set.uIcc_of_le hh.le]
    exact hgI.of_le (by exact_mod_cast Nat.le_succ n)
  have hf' : DifferentiableOn ℝ (iteratedDerivWithin n g (Set.uIcc 0 h)) (Set.uIoo 0 h) := by
    rw [Set.uIcc_of_le hh.le, Set.uIoo_of_le hh.le]
    exact (hgI.differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self n) hU).mono
      Set.Ioo_subset_Icc_self
  obtain ⟨x', hx', hT⟩ := taylor_mean_remainder_lagrange (n := n) (ne_of_lt hh) hf hf'
  rw [Set.uIcc_of_le hh.le] at hT
  rw [Set.uIoo_of_le hh.le] at hx'
  rw [taylor_within_apply] at hT
  have hx'mem : x' ∈ Set.Ioo (-t0) t0 := hsub (Set.Ioo_subset_Icc_self hx')
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-t0) t0 := hsub ⟨le_rfl, hh.le⟩
  have hder : ∀ k, k ≤ n → iteratedDerivWithin k g (Set.Icc 0 h) 0 = iteratedDeriv k g 0 := by
    intro k hk
    exact iteratedDerivWithin_eq_iteratedDeriv hU ((hdAt 0 h0mem).of_le (by exact_mod_cast Nat.le_succ_of_le hk)) ⟨le_rfl, hh.le⟩
  have hder' : iteratedDerivWithin (n + 1) g (Set.Icc 0 h) x' = iteratedDeriv (n + 1) g x' :=
    iteratedDerivWithin_eq_iteratedDeriv hU (hdAt x' hx'mem) (Set.Ioo_subset_Icc_self hx')
  rw [hder'] at hT
  have hsum : ∑ k ∈ range (n + 1), ((k ! : ℝ)⁻¹ * (h - 0) ^ k) • iteratedDerivWithin k g (Set.Icc 0 h) 0
      = ∑ i ∈ range (n + 1), (i ! : ℝ)⁻¹ * iteratedDeriv i g 0 * h ^ i := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hder k (by have := Finset.mem_range.mp hk; omega), smul_eq_mul]
    ring
  rw [hsum] at hT
  rw [hT, abs_div, abs_mul]
  have hfac : (1 : ℝ) ≤ ((n + 1)! : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hC' := hC x' hx'mem
  have hh' : |(h - 0) ^ (n + 1)| = h ^ (n + 1) := by rw [sub_zero, abs_of_pos (pow_pos hh _)]
  rw [hh', abs_of_pos (by positivity : (0 : ℝ) < ((n + 1)! : ℝ))]
  calc |iteratedDeriv (n + 1) g x'| * h ^ (n + 1) / ((n + 1)! : ℝ) ≤ |iteratedDeriv (n + 1) g x'| * h ^ (n + 1) :=
        div_le_self (by positivity) hfac
    _ ≤ C * h ^ (n + 1) := mul_le_mul_of_nonneg_right hC' (by positivity)

/-- Taylor coefficient `(1/i!) d_t^i f(X, 0)`. -/
def taylorCoeff (f : ℝ → ℝ → ℝ) (i : ℕ) (X : ℝ) : ℝ := (i ! : ℝ)⁻¹ * iteratedDeriv i (fun t => f X t) 0

/-- The coefficient of `h^l` after the substitution `t = h`: `S_l(X) = sum_{i + j = l} (1/i!) d_t^i Sigma_j(X, 0)` (`eq:smo-BSr3`). -/
def Scoef (Sig : ℕ → ℝ → ℝ → ℝ) (l : ℕ) (X : ℝ) : ℝ := ∑ j ∈ range (l + 1), taylorCoeff (Sig j) (l - j) X

lemma Scoef_zero (Sig : ℕ → ℝ → ℝ → ℝ) (X : ℝ) : Scoef Sig 0 X = Sig 0 X 0 := by
  simp [Scoef, taylorCoeff]

lemma Scoef_one (Sig : ℕ → ℝ → ℝ → ℝ) (X : ℝ) :
    Scoef Sig 1 X = Sig 1 X 0 + iteratedDeriv 1 (fun t => Sig 0 X t) 0 := by
  simp [Scoef, taylorCoeff, Finset.sum_range_succ, add_comm]

/-- **L2.S3, value part**: `|sum_j h^j Sigma_j(X,h) - sum_l h^l S_l(X)| <= (M+1) C h^{M+1}`. -/
theorem taylor_subst (Sig : ℕ → ℝ → ℝ → ℝ) (M : ℕ) (X t0 C h : ℝ) (hh : 0 < h) (hht : h < t0)
    (hg : ∀ j ≤ M, ContDiffOn ℝ ((M - j + 1 : ℕ) : WithTop ℕ∞) (fun t => Sig j X t) (Set.Ioo (-t0) t0))
    (hC : ∀ j ≤ M, ∀ t ∈ Set.Ioo (-t0) t0, |iteratedDeriv (M - j + 1) (fun t => Sig j X t) t| ≤ C) :
    |∑ j ∈ range (M + 1), h ^ j * Sig j X h - ∑ l ∈ range (M + 1), h ^ l * Scoef Sig l X|
      ≤ (M + 1) * C * h ^ (M + 1) := by
  have hreg : ∑ l ∈ range (M + 1), h ^ l * Scoef Sig l X
      = ∑ j ∈ range (M + 1), h ^ j * ∑ i ∈ range (M - j + 1), (i ! : ℝ)⁻¹ * iteratedDeriv i (fun t => Sig j X t) 0 * h ^ i := by
    have e1 : ∀ l ∈ range (M + 1), h ^ l * Scoef Sig l X
        = ∑ j ∈ range (l + 1), h ^ ((l - j) + j) * taylorCoeff (Sig j) (l - j) X := by
      intro l hl
      unfold Scoef
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have : (l - j) + j = l := Nat.sub_add_cancel (by have := Finset.mem_range.mp hj; omega)
      rw [this]
    rw [Finset.sum_congr rfl e1]
    have flip := Finset.sum_range_diag_flip (M + 1) (fun a b => h ^ (b + a) * taylorCoeff (Sig a) b X)
    rw [flip]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ M := by have := Finset.mem_range.mp hj; omega
    have hr : M + 1 - j = M - j + 1 := by omega
    rw [hr, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold taylorCoeff
    rw [pow_add]
    ring
  rw [hreg, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j ∈ range (M + 1), |h ^ j * Sig j X h - h ^ j * ∑ i ∈ range (M - j + 1),
      (i ! : ℝ)⁻¹ * iteratedDeriv i (fun t => Sig j X t) 0 * h ^ i| ≤ C * h ^ (M + 1) := by
    intro j hj
    have hj' : j ≤ M := by have := Finset.mem_range.mp hj; omega
    have h1 := taylor_pt (fun t => Sig j X t) (M - j) t0 C h hh hht (by
      have : M - j + 1 = (M - j) + 1 := rfl
      exact hg j hj') (hC j hj')
    rw [← mul_sub, abs_mul, abs_of_pos (pow_pos hh _)]
    calc h ^ j * |Sig j X h - ∑ i ∈ range (M - j + 1), (i ! : ℝ)⁻¹ * iteratedDeriv i (fun t => Sig j X t) 0 * h ^ i|
        ≤ h ^ j * (C * h ^ (M - j + 1)) := mul_le_mul_of_nonneg_left h1 (pow_nonneg hh.le _)
      _ = C * h ^ (M + 1) := by
          have : h ^ j * h ^ (M - j + 1) = h ^ (M + 1) := by rw [← pow_add]; congr 1; omega
          rw [← this]; ring
  calc ∑ j ∈ range (M + 1), |h ^ j * Sig j X h - h ^ j * ∑ i ∈ range (M - j + 1),
        (i ! : ℝ)⁻¹ * iteratedDeriv i (fun t => Sig j X t) 0 * h ^ i| ≤ ∑ j ∈ range (M + 1), C * h ^ (M + 1) :=
        Finset.sum_le_sum hterm
    _ = (M + 1) * C * h ^ (M + 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-! ### Regularity of the coefficients `S_l` -/

variable (s : Set (ℝ × ℝ))

/-- the partial derivative in the second variable, within `s` -/
noncomputable def dtS (g : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => fderivWithin ℝ g s p (0, 1)

/-- iterated -/
noncomputable def dtN (g : ℝ × ℝ → ℝ) : ℕ → ℝ × ℝ → ℝ
  | 0 => g
  | n + 1 => dtS s (dtN g n)

lemma dtS_contDiffOn (hs : UniqueDiffOn ℝ s) {g : ℝ × ℝ → ℝ} {k : ℕ} (hg : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g s) :
    ContDiffOn ℝ (k : WithTop ℕ∞) (dtS s g) s := by
  have := hg.fderivWithin hs (m := (k : WithTop ℕ∞)) (by exact_mod_cast le_refl (k + 1))
  exact this.clm_apply contDiffOn_const

lemma dtN_contDiffOn (hs : UniqueDiffOn ℝ s) {g : ℝ × ℝ → ℝ} (n : ℕ) :
    ∀ k : ℕ, ContDiffOn ℝ ((k + n : ℕ) : WithTop ℕ∞) g s → ContDiffOn ℝ (k : WithTop ℕ∞) (dtN s g n) s := by
  induction n with
  | zero => intro k hk; simpa [dtN] using hk
  | succ n ih =>
    intro k hk
    have h1 : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (dtN s g n) s := ih (k + 1) (by
      have : k + 1 + n = k + (n + 1) := by ring
      rw [this]; exact hk)
    exact dtS_contDiffOn s hs h1

lemma hasDerivAt_dtS {g : ℝ × ℝ → ℝ} (hg : ContDiffOn ℝ (1 : WithTop ℕ∞) g s) {X t t0 : ℝ}
    (hX : ∀ u ∈ Set.Ioo (-t0) t0, (X, u) ∈ s) (ht : t ∈ Set.Ioo (-t0) t0) :
    HasDerivAt (fun u => g (X, u)) (dtS s g (X, t)) t := by
  have hdiff : DifferentiableWithinAt ℝ g s (X, t) := (hg.differentiableOn one_ne_zero) _ (hX t ht)
  have h1 := hdiff.hasFDerivWithinAt
  have hc : HasDerivAt (fun u : ℝ => (X, u)) ((0 : ℝ), (1 : ℝ)) t := (hasDerivAt_const t X).prodMk (hasDerivAt_id t)
  have h2 := h1.comp_hasDerivWithinAt t hc.hasDerivWithinAt (s := Set.Ioo (-t0) t0) (fun u hu => hX u hu)
  exact h2.hasDerivAt (isOpen_Ioo.mem_nhds ht)

lemma iteratedDeriv_dtN (hs : UniqueDiffOn ℝ s) {g : ℝ × ℝ → ℝ} {X t0 : ℝ} (hX : ∀ u ∈ Set.Ioo (-t0) t0, (X, u) ∈ s)
    (n : ℕ) (hg : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) g s) :
    ∀ t ∈ Set.Ioo (-t0) t0, iteratedDeriv n (fun u => g (X, u)) t = dtN s g n (X, t) := by
  induction n with
  | zero => intro t ht; simp [dtN]
  | succ n ih =>
    intro t ht
    have hg' : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) g s := hg.of_le (by exact_mod_cast Nat.le_succ n)
    have hd : ContDiffOn ℝ (1 : WithTop ℕ∞) (dtN s g n) s := by
      have := dtN_contDiffOn s hs n 1 (by
        have e : 1 + n = n + 1 := by ring
        rw [e]; exact hg)
      simpa using this
    have hev : iteratedDeriv n (fun u => g (X, u)) =ᶠ[nhds t] fun u => dtN s g n (X, u) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu using ih hg' u hu
    rw [iteratedDeriv_succ, hev.deriv_eq]
    exact (hasDerivAt_dtS s hd hX ht).deriv


/-- The `t`-derivative `dtN` is the iterated Frechet derivative applied to `(0,1)` repeated. -/
lemma dtN_eq_iterated (hs : UniqueDiffOn ℝ s) {g : ℝ × ℝ → ℝ} (n : ℕ) (hg : ContDiffOn ℝ (n : WithTop ℕ∞) g s) :
    ∀ p ∈ s, dtN s g n p = iteratedFDerivWithin ℝ n g s p (fun _ => ((0 : ℝ), (1 : ℝ))) := by
  induction n with
  | zero => intro p hp; simp [dtN, iteratedFDerivWithin_zero_apply]
  | succ n ih =>
    intro p hp
    have ih' := ih (hg.of_le (by exact_mod_cast Nat.le_succ n))
    have hdA : DifferentiableOn ℝ (iteratedFDerivWithin ℝ n g s) s :=
      hg.differentiableOn_iteratedFDerivWithin (by exact_mod_cast Nat.lt_succ_self n) hs
    show fderivWithin ℝ (dtN s g n) s p ((0 : ℝ), (1 : ℝ)) = _
    set L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ) ℝ →L[ℝ] ℝ :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × ℝ) ℝ (fun _ => ((0 : ℝ), (1 : ℝ))) with hL
    have hLd : HasFDerivWithinAt (fun q => L (iteratedFDerivWithin ℝ n g s q)) (L.comp (fderivWithin ℝ (iteratedFDerivWithin ℝ n g s) s p)) s p :=
      L.hasFDerivAt.comp_hasFDerivWithinAt p (hdA p hp).hasFDerivWithinAt
    have hev : (fun q => L (iteratedFDerivWithin ℝ n g s q)) = fun q => (iteratedFDerivWithin ℝ n g s q) (fun _ => ((0 : ℝ), (1 : ℝ))) := rfl
    rw [fderivWithin_congr ih' (ih' p hp), ← hev, hLd.fderivWithin (hs p hp)]
    rfl

/-- **The `t`-derivative bound from the joint norm bound**: if the `n`-th Frechet derivative of `g` within `s` has norm `<= C` at `(X,t)`, so does the `n`-th derivative of the slice. -/
lemma abs_dtN_le (hs : UniqueDiffOn ℝ s) {g : ℝ × ℝ → ℝ} (n : ℕ) (hg : ContDiffOn ℝ (n : WithTop ℕ∞) g s) {p : ℝ × ℝ} (hp : p ∈ s) {C : ℝ}
    (hC : ‖iteratedFDerivWithin ℝ n g s p‖ ≤ C) : |dtN s g n p| ≤ C := by
  rw [dtN_eq_iterated s hs n hg p hp]
  have h1 := (iteratedFDerivWithin ℝ n g s p).le_opNorm (fun _ => ((0 : ℝ), (1 : ℝ)))
  have h2 : ∏ i : Fin n, ‖((fun _ => ((0 : ℝ), (1 : ℝ))) : Fin n → ℝ × ℝ) i‖ = 1 := by
    simp [Prod.norm_def]
  rw [h2, mul_one] at h1
  have h3 : |(iteratedFDerivWithin ℝ n g s p) (fun _ => ((0 : ℝ), (1 : ℝ)))| ≤ ‖iteratedFDerivWithin ℝ n g s p‖ := by
    simpa [Real.norm_eq_abs] using h1
  exact h3.trans hC

/-- A `C^k` function of `(X,t)` on `J x [-t0,t0]` has `C^k` slices in `t` on the open interval. -/
lemma slice_contDiffOn {f : ℝ → ℝ → ℝ} {J : Set ℝ} {t0 : ℝ} {k : ℕ} (hf : JetRegJ f J t0 k) {X : ℝ} (hX : X ∈ J) :
    ContDiffOn ℝ (k : WithTop ℕ∞) (fun t => f X t) (Set.Ioo (-t0) t0) := by
  have hf' : ContDiffOn ℝ (k : WithTop ℕ∞) (fun p : ℝ × ℝ => f p.1 p.2) (J ×ˢ Set.Icc (-t0) t0) := hf
  have hc : ContDiff ℝ (k : WithTop ℕ∞) (fun t : ℝ => (X, t)) := contDiff_const.prodMk contDiff_id
  exact hf'.comp hc.contDiffOn (fun t ht => ⟨hX, Set.Ioo_subset_Icc_self ht⟩)

/-- **L2.S3, regularity part**: `S_l in C^{M+1}(J)` for `l <= M`, when `Sigma_j in C^{2M+1}(J x [-t0,t0])` (`JetRegJ`), `j <= M`. -/
theorem Scoef_contDiffOn {Sig : ℕ → ℝ → ℝ → ℝ} {M : ℕ} {J : Set ℝ} {t0 : ℝ} (hJ : UniqueDiffOn ℝ J) (ht0 : 0 < t0)
    (hreg : ∀ j ≤ M, JetRegJ (Sig j) J t0 (2 * M + 1)) {l : ℕ} (hl : l ≤ M) :
    ContDiffOn ℝ ((M + 1 : ℕ) : WithTop ℕ∞) (Scoef Sig l) J := by
  set s : Set (ℝ × ℝ) := J ×ˢ Set.Ioo (-t0) t0 with hs
  have hU : UniqueDiffOn ℝ s := hJ.prod isOpen_Ioo.uniqueDiffOn
  have hmap : Set.MapsTo (fun X : ℝ => (X, (0 : ℝ))) J s := fun X hX => ⟨hX, by constructor <;> linarith⟩
  have hterm : ∀ j ∈ range (l + 1), ContDiffOn ℝ ((M + 1 : ℕ) : WithTop ℕ∞) (fun X => taylorCoeff (Sig j) (l - j) X) J := by
    intro j hj
    have hj' : j ≤ M := by have := Finset.mem_range.mp hj; omega
    have hg : ContDiffOn ℝ ((2 * M + 1 : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℝ => Sig j p.1 p.2) s :=
      (hreg j hj').mono (Set.prod_mono le_rfl Set.Ioo_subset_Icc_self)
    have hdt : ContDiffOn ℝ ((M + 1 : ℕ) : WithTop ℕ∞) (dtN s (fun p : ℝ × ℝ => Sig j p.1 p.2) (l - j)) s :=
      dtN_contDiffOn s hU (l - j) (M + 1) (hg.of_le (by exact_mod_cast (by omega : M + 1 + (l - j) ≤ 2 * M + 1)))
    have hcomp : ContDiffOn ℝ ((M + 1 : ℕ) : WithTop ℕ∞) (fun X => dtN s (fun p : ℝ × ℝ => Sig j p.1 p.2) (l - j) (X, 0)) J :=
      hdt.comp (contDiff_id.prodMk contDiff_const).contDiffOn hmap
    have heq : Set.EqOn (fun X => taylorCoeff (Sig j) (l - j) X)
        (fun X => ((l - j)! : ℝ)⁻¹ * dtN s (fun p : ℝ × ℝ => Sig j p.1 p.2) (l - j) (X, 0)) J := by
      intro X hX
      have key : iteratedDeriv (l - j) (fun t => Sig j X t) 0
          = dtN s (fun p : ℝ × ℝ => Sig j p.1 p.2) (l - j) (X, 0) :=
        iteratedDeriv_dtN s hU (X := X) (t0 := t0) (fun u hu => ⟨hX, hu⟩) (l - j)
          (hg.of_le (by exact_mod_cast (by omega : l - j ≤ 2 * M + 1))) 0 ⟨by linarith, ht0⟩
      show ((l - j)! : ℝ)⁻¹ * iteratedDeriv (l - j) (fun t => Sig j X t) 0 = ((l - j)! : ℝ)⁻¹ * _
      rw [key]
    exact (contDiffOn_const.mul hcomp).congr heq
  exact ContDiffOn.sum hterm

/-- **L2.S3**: the Taylor substitution `t = h` on an interval `J`: the coefficients `S_l` are `C^{M+1}(J)` and
`Sigma(X, h, h) = sum_{l <= M} h^l S_l(X) + O(h^{M+1})` uniformly on `J` (with the `t`-derivative bound `hC`, see the module docstring). -/
theorem phase_substitution {Sig : ℕ → ℝ → ℝ → ℝ} {M : ℕ} {J : Set ℝ} {t0 : ℝ} (hJ : UniqueDiffOn ℝ J) (ht0 : 0 < t0)
    (hreg : ∀ j ≤ M, JetRegJ (Sig j) J t0 (2 * M + 1)) (C : ℝ)
    (hC : ∀ X ∈ J, ∀ j ≤ M, ∀ t ∈ Set.Ioo (-t0) t0, |iteratedDeriv (M - j + 1) (fun t => Sig j X t) t| ≤ C) :
    (∀ l ≤ M, ContDiffOn ℝ ((M + 1 : ℕ) : WithTop ℕ∞) (Scoef Sig l) J) ∧
      ∀ X ∈ J, ∀ h : ℝ, 0 < h → h < t0 →
        |∑ j ∈ range (M + 1), h ^ j * Sig j X h - ∑ l ∈ range (M + 1), h ^ l * Scoef Sig l X|
          ≤ (M + 1) * C * h ^ (M + 1) := by
  refine ⟨fun l hl => Scoef_contDiffOn hJ ht0 hreg hl, ?_⟩
  intro X hX h hh hht
  exact taylor_subst Sig M X t0 C h hh hht
    (fun j hj => (slice_contDiffOn (hreg j hj) hX).of_le (by exact_mod_cast (by omega : M - j + 1 ≤ 2 * M + 1)))
    (hC X hX)


/-- **L2.S3 / F-S2-2 bridge**: the `t`-derivative bound `hC` of `phase_substitution` from the uniform joint norm bound (the field `BulkPhaseInputs.Sigma_bdd`):
if `||iteratedFDerivWithin R i (Sigma j) (J x [-t0,t0]) p|| <= C` for `i <= 2M+1`, `p` in the set, then `|d_t^{M-j+1} Sigma_j(X, t)| <= C` for `X in J`, `|t| < t0`. -/
theorem taylor_bound_of_Sigma_bdd {Sig : ℕ → ℝ → ℝ → ℝ} {M : ℕ} {J : Set ℝ} {t0 : ℝ} (hJ : UniqueDiffOn ℝ J) (ht0 : 0 < t0)
    (hreg : ∀ j ≤ M, JetRegJ (Sig j) J t0 (2 * M + 1)) (C : ℝ)
    (hb : ∀ j ≤ M, ∀ i ≤ 2 * M + 1, ∀ p ∈ J ×ˢ Set.Icc (-t0) t0,
      ‖iteratedFDerivWithin ℝ i (fun q : ℝ × ℝ => Sig j q.1 q.2) (J ×ˢ Set.Icc (-t0) t0) p‖ ≤ C) :
    ∀ X ∈ J, ∀ j ≤ M, ∀ t ∈ Set.Ioo (-t0) t0, |iteratedDeriv (M - j + 1) (fun t => Sig j X t) t| ≤ C := by
  intro X hX j hj t ht
  set s : Set (ℝ × ℝ) := J ×ˢ Set.Icc (-t0) t0 with hs
  have hU : UniqueDiffOn ℝ s := hJ.prod (uniqueDiffOn_Icc (by linarith))
  have hg : ContDiffOn ℝ ((2 * M + 1 : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℝ => Sig j p.1 p.2) s := hreg j hj
  have hn : M - j + 1 ≤ 2 * M + 1 := by omega
  have hg' : ContDiffOn ℝ ((M - j + 1 : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℝ => Sig j p.1 p.2) s :=
    hg.of_le (by exact_mod_cast hn)
  rw [iteratedDeriv_dtN s hU (X := X) (t0 := t0) (fun u hu => ⟨hX, Set.Ioo_subset_Icc_self hu⟩) (M - j + 1) hg' t ht]
  exact abs_dtN_le s hU (M - j + 1) hg' ⟨hX, Set.Ioo_subset_Icc_self ht⟩ (hb j hj _ hn _ ⟨hX, Set.Ioo_subset_Icc_self ht⟩)


/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.taylor_pt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.taylor_pt

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.taylor_subst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.taylor_subst

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.Scoef_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.Scoef_contDiffOn

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.phase_substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.phase_substitution

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.taylor_bound_of_Sigma_bdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.taylor_bound_of_Sigma_bdd

end FormalResearch.JacobiEigenvectors.TheoremA
