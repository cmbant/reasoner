module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.EigenvalueStatements

/-!
# Paper J, Layer 2: cor:eigen (c), general order, from the expansion data (L2.E; F-BB-3)

Source: Paper J `thmA.tex`, proof of `cor:eigen`, Step 5 ("for `eq:cor-gapM`, (b) gives `X_k - X_{k+1} = sum_{r <= M} h^r [x_r(y_k) - x_r(y_k + pi h)] + O(h^{M+1})` ... Taylor's formula for `x_r in C^{M+1-r}([0, pi L])`
to order `M - r` has remainder `O(h^{M+1-r})`, uniformly on the closed interval ... collecting the powers `h^{r+q}`, `q >= 1`, gives `eq:cor-gapM`").  Frozen statement: `CorEigenGapM` (`TheoremA/EigenvalueStatements.lean`).

## What remains of cor:eigen after the proved items (exact missing statements)

Proved elsewhere: `BandSlope` (`CorEigenWindows.lean`), `invLevel_of_slope` (b)(ii), `corEigenGap1_of_slope` (c) first part, `corEigenCount_of_slope` (d) (`CorEigenInverse.lean`, `CorEigenCount.lean`); proved here: the general-order gap expansion given the expansion data.
The following are *not* proved; each is stopped at the exact statement below.

1. **Step 1, the derivative of the action** (`eq:cp-S0p`, `eq:cp-dt`): for `X` in the open band that is not a collision energy, `S_0'(X) = -int_{u_-}^{u_+} du/sqrt(T(u;X))` and
   `d/dt actionS0 (frozenFamily F 0) (mu, t) X |_{t=0} = int_{u_-}^{u_+} (B_1 + (X - B_0) G_1/(2 G_0)) T^{-1/2} du`, with the integral absolutely convergent (also at the collisions).  Chain in the paper: Hadamard division
   `d_lambda zeta = s(1-s) kappa`, `1 - zeta^2 = s(1-s) H` after the substitution `u = u_- + (u_+ - u_-) s`, so that `d_lambda arccos zeta` is bounded and continuous and differentiation under the integral is legitimate; the boundary terms
   cancel since `arccos zeta(0) = pi l_-`, `arccos zeta(1) = pi l_+`.  This needs (i) smooth dependence of the turning points `u_pm(lambda)` (implicit function theorem for the simple zeros of `T`), (ii) the Hadamard
   division lemma with continuity of the quotient, (iii) Leibniz differentiation under the integral with a dominating function.  None of it is in the repository (`MonotoneAction.lean` only proves that `S_0` is strictly decreasing).
2. **`CorEigenS1`**: its first conjunct `HasDerivAt (t |-> actionS0 (frozenFamily F 0) (mu, t) X) (S_1 mu X) 0` additionally needs the *identification* `S_1 = Sigma_1(., 0) + d_t Sigma_0(., 0)` for an arbitrary `S` satisfying the three
   properties of the frozen conclusion (uniqueness `thmSmoSpec_unique` against the glued `Scoef`, `Scoef_one`), and `Sigma_0(X, t) = S_0^{(t)}(X)` for `X` in the open band and small `t` (the field `Sigma_zero` of the bulk phase inputs
   for all `t`; for the soft windows `mu0_S0` at `(mu, t)` with the closeness `bandHi_close`).  Both are statements about the Layer-4 data, not about `S`; they are not in `ThmSmoSpec`, so a proof must take the charts as premises (as `thmAi_assembled` does).
3. **`InvS0` edge values** `-S_0'(X_s^pm) = pi sqrt(2/(kappa_pm d_pm))`: the limit `eq:cp-edgelim` of item 1 as `alpha -> 0` (substitution `tau = sqrt(alpha) s`, joint continuity of the integrand in `(sqrt(alpha), s, mu)` with the dominating
   function `C/sqrt(1-s^2)`); the soft chart has `mu0_deriv : 0 < deriv (muS 0 mu) 0` but no value for it (it is *derived* from `eq:cp-S0p` in the paper, not a chart fact).
4. **`InvCoeffs`, the recursion `x_r`** (b)(iii): the root `X(y, h)` of `F_M(x, h) = y` is `C^{M+1}` in `(y, h)` (implicit function theorem on the compact set `[0, pi L] x [0, h_*]`, `-partial_x F_M >= c`), `x_r = d_h^r X(., 0)/r!`;
   the coefficient of `h^r` in `F_M(sum_s h^s x_s, h) = y` gives `x_1 = -S_1(x_0)/S_0'(x_0)` and the stated `x_2`.  Needed in Lean: a *global* `C^{M+1-r}` implicit function on a compact set (Mathlib has the local one), and the uniform
   bound `Cx` on all derivatives (finding F-BB-3: `InvExpansion` has no such bound; **minimal correction**: add `exists Cx, forall mu in K, forall r <= M, forall i <= M+1-r, forall y in [0, pi L], |iteratedDerivWithin i (x r mu) (Icc 0 (pi L)) y| <= Cx`
   to `InvExpansion`; it is true for the actual `x_r` by compactness and joint continuity of the derivatives of `X`).  With that field `corEigenGapM_of_bound` below is the whole of `CorEigenGapM`.

## Proved here (axiom-pinned)

* `contDiffOn_iteratedDerivWithin_nat`: a `C^n` function on a set with unique derivatives has `C^{n-q}` `q`-th iterated derivatives.
* `taylor_Icc`: Lagrange Taylor on a subinterval of `[a, b]`, with the iterated derivatives *within `[a, b]`* and a bound for the `(n+1)`-th one.
* `corEigenGapM_of_bound`: **`CorEigenGapM` for every expansion `x` that carries the uniform derivative bound `Cx`** (the conclusion of `CorEigenGapM`, with `d_p` as stated, `d_p in C^{M+1-p}`).  The hypotheses `IsCompact K`, `HypOn`, `DM`, `SmoothExt`, `EigenRule`
  of the frozen statement are not used: the gap expansion is a consequence of the expansion `InvExpansion` and the bound alone.

## Differences from the paper

The paper's uniformity "on the closed interval" is the hypothesis `Cx` (the paper takes it from the compactness of `[0, pi L] x [0, h_*]`).

## Not formalised

Items 1--4 above.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting

variable {Par : Type*} [TopologicalSpace Par]

lemma contDiffOn_iteratedDerivWithin_nat {f : ℝ → ℝ} {s : Set ℝ} (hs : UniqueDiffOn ℝ s) :
    ∀ (q n : ℕ), q ≤ n → ContDiffOn ℝ (n : WithTop ℕ∞) f s →
      ContDiffOn ℝ ((n - q : ℕ) : WithTop ℕ∞) (iteratedDerivWithin q f s) s := by
  intro q
  induction q generalizing f with
  | zero => intro n _ hf; simpa using hf
  | succ q ih =>
    intro n hq hf
    rw [iteratedDerivWithin_succ']
    have h1 : ContDiffOn ℝ ((n - 1 : ℕ) : WithTop ℕ∞) (derivWithin f s) s :=
      hf.derivWithin hs (by
        have : n - 1 + 1 = n := by omega
        exact_mod_cast this.le)
    have := ih (f := derivWithin f s) (n - 1) (by omega) h1
    have e : n - 1 - q = n - (q + 1) := by omega
    rwa [e] at this

lemma taylor_Icc {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (n : ℕ) (hf : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f (Icc a b)) {C : ℝ}
    (hC : ∀ z ∈ Icc a b, |iteratedDerivWithin (n + 1) f (Icc a b) z| ≤ C) {y y' : ℝ} (hy : y ∈ Icc a b) (hy' : y' ∈ Icc a b)
    (hyy : y ≤ y') :
    |f y' - ∑ i ∈ range (n + 1), (i.factorial : ℝ)⁻¹ * (y' - y) ^ i * iteratedDerivWithin i f (Icc a b) y| ≤
      C * (y' - y) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rcases eq_or_lt_of_le hyy with e | hlt
  · subst e
    simp [Finset.sum_range_succ', zero_pow, iteratedDerivWithin_zero]
  have hsub : Icc y y' ⊆ Icc a b := Icc_subset_Icc hy.1 hy'.2
  have hUt : UniqueDiffOn ℝ (Icc y y') := uniqueDiffOn_Icc hlt
  have hUs : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hft : ContDiffOn ℝ n f (Icc y y') := (hf.mono hsub).of_le (by exact_mod_cast Nat.le_succ n)
  have hf0 : ContDiffOn ℝ n f (Set.uIcc y y') := by rw [Set.uIcc_of_le hlt.le]; exact hft
  have hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Set.uIcc y y')) (Set.uIoo y y') := by
    rw [Set.uIcc_of_le hlt.le, Set.uIoo_of_le hlt.le]
    exact ((hf.mono hsub).differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self n) hUt).mono Ioo_subset_Icc_self
  obtain ⟨x', hx', hT⟩ := taylor_mean_remainder_lagrange (n := n) (ne_of_lt hlt) hf0 hf'
  rw [Set.uIcc_of_le hlt.le] at hT
  rw [Set.uIoo_of_le hlt.le] at hx'
  rw [taylor_within_apply] at hT
  have hconv : ∀ k : ℕ, k ≤ n + 1 → ∀ z ∈ Icc y y', iteratedDerivWithin k f (Icc y y') z = iteratedDerivWithin k f (Icc a b) z := by
    intro k hk z hz
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin,
      iteratedFDerivWithin_subset hsub hUt hUs (hf.of_le (by exact_mod_cast hk)) hz]
  have hsum : ∑ k ∈ range (n + 1), ((k.factorial : ℝ)⁻¹ * (y' - y) ^ k) • iteratedDerivWithin k f (Icc y y') y =
      ∑ i ∈ range (n + 1), (i.factorial : ℝ)⁻¹ * (y' - y) ^ i * iteratedDerivWithin i f (Icc a b) y := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [smul_eq_mul, hconv k (by have := Finset.mem_range.mp hk; omega) y ⟨le_rfl, hlt.le⟩]
  rw [hsum] at hT
  rw [hT, hconv (n + 1) le_rfl x' (Ioo_subset_Icc_self hx'), abs_div, abs_mul, abs_of_nonneg (pow_nonneg (sub_nonneg.2 hyy) _),
    abs_of_pos (by positivity : (0 : ℝ) < ((n + 1).factorial : ℝ))]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right (hC x' (hsub (Ioo_subset_Icc_self hx'))) (pow_nonneg (sub_nonneg.2 hyy) _)

/-- splitting off the `q = 0` term -/
lemma sum_range_succ_Icc (n : ℕ) (g : ℕ → ℝ) : ∑ q ∈ range (n + 1), g q = g 0 + ∑ q ∈ Finset.Icc 1 n, g q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    ring

/-- the reindexing `q = p - r` of the double sum -/
lemma sum_reindex_gap (M : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ p ∈ Finset.Icc 1 M, ∑ r ∈ range p, f r (p - r) = ∑ r ∈ range (M + 1), ∑ q ∈ Finset.Icc 1 (M - r), f r q := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨x.2, x.1 - x.2⟩) (fun x _ => ⟨x.1 + x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p, r⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at h ⊢
    omega
  · rintro ⟨r, q⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at h ⊢
    omega
  · rintro ⟨p, r⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at h
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true, true_and]
    omega
  · rintro ⟨r, q⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at h
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true, true_and]
    omega
  · rintro ⟨p, r⟩ h
    rfl

/-- **`CorEigenGapM` for expansions with the uniform derivative bound** (cor:eigen (c), general order; see the module docstring for the one missing field of `InvExpansion`). -/
theorem corEigenGapM_of_bound (F : SymbolFamily Par) (K : Set Par) (M : ℕ) (S : ℕ → Par → ℝ → ℝ) (x : ℕ → Par → ℝ → ℝ)
    (hx : InvExpansion F K M S x) (Cx : ℝ)
    (hCx : ∀ μ ∈ K, ∀ r ≤ M, ∀ i ≤ M + 1 - r, ∀ y ∈ Icc 0 (Real.pi * F.L), |iteratedDerivWithin i (x r μ) (Icc 0 (Real.pi * F.L)) y| ≤ Cx) :
    ∃ d : ℕ → Par → ℝ → ℝ,
      (∀ μ ∈ K, ∀ p ∈ Finset.Icc 1 M, ContDiffOn ℝ ((M + 1 - p : ℕ) : WithTop ℕ∞) (d p μ) (Set.Icc 0 (Real.pi * F.L)) ∧
        ∀ y ∈ Icc 0 (Real.pi * F.L), d p μ y =
          -∑ r ∈ range p, Real.pi ^ (p - r) / ((p - r).factorial : ℝ) * iteratedDerivWithin (p - r) (x r μ) (Icc 0 (Real.pi * F.L)) y) ∧
      ∃ Cc h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
        ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
          ∀ i j : Fin (N + 1), (j : ℕ) = (i : ℕ) + 1 →
            |(X i - X j) - ∑ p ∈ Finset.Icc 1 M, F.step N ^ p * d p μ (Real.pi * F.step N * ((i : ℕ) + 1 / 2))| ≤ Cc * F.step N ^ (M + 1) := by
  obtain ⟨hreg, -, C, h0, hh0, hexp⟩ := hx
  have hL := F.L_pos
  have hpiL : 0 < Real.pi * F.L := mul_pos Real.pi_pos hL
  have hUs : UniqueDiffOn ℝ (Icc 0 (Real.pi * F.L)) := uniqueDiffOn_Icc hpiL
  refine ⟨fun p μ y => -∑ r ∈ range p, Real.pi ^ (p - r) / ((p - r).factorial : ℝ) *
    iteratedDerivWithin (p - r) (x r μ) (Icc 0 (Real.pi * F.L)) y, ?_, ?_⟩
  · intro μ hμ p hp
    have hp' := Finset.mem_Icc.mp hp
    refine ⟨?_, fun y _ => rfl⟩
    refine (ContDiffOn.sum (fun r hr => ?_)).neg
    have hr' : r < p := Finset.mem_range.mp hr
    have := contDiffOn_iteratedDerivWithin_nat hUs (p - r) (M + 1 - r) (by omega) (hreg μ hμ r (by omega))
    have e : M + 1 - r - (p - r) = M + 1 - p := by omega
    rw [e] at this
    exact contDiffOn_const.mul this
  · refine ⟨2 * |C| + (M + 1) * |Cx| * Real.pi ^ (M + 1), min h0 1, lt_min hh0 one_pos, ?_⟩
    intro μ hμ N hN X Um hE i j hij
    have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have hh1 : F.step N ≤ 1 := hN.trans (min_le_right _ _)
    have hh0' : F.step N ≤ h0 := hN.trans (min_le_left _ _)
    set h := F.step N with hh
    have hmul : h * ((N : ℝ) + 1) = F.L := by
      rw [hh]; unfold SymbolFamily.step FormalResearch.JB.stepSize; field_simp
    have hpi := Real.pi_pos
    have hpi1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hjN : (j : ℕ) ≤ N := by have := j.isLt; omega
    set y : ℝ := Real.pi * h * (((i : ℕ) : ℝ) + 1 / 2) with hy
    set y' : ℝ := Real.pi * h * (((j : ℕ) : ℝ) + 1 / 2) with hy'
    have hyy : y' - y = Real.pi * h := by rw [hy, hy', hij]; push_cast; ring
    have hy0 : 0 ≤ y := by positivity
    have hyy' : y ≤ y' := by have := mul_pos hpi hst; linarith
    have hy'L : y' ≤ Real.pi * F.L := by
      rw [← hmul]
      have : ((j : ℕ) : ℝ) ≤ N := by exact_mod_cast hjN
      rw [hy']
      nlinarith [mul_pos hpi hst]
    have hyI : y ∈ Icc 0 (Real.pi * F.L) := ⟨hy0, hyy'.trans hy'L⟩
    have hy'I : y' ∈ Icc 0 (Real.pi * F.L) := ⟨hy0.trans hyy', hy'L⟩
    -- the Taylor expansion of each `x_r` between `y` and `y'`
    have hd : ∀ r ∈ range (M + 1), |(x r μ y - x r μ y') + ∑ q ∈ Finset.Icc 1 (M - r), (Real.pi * h) ^ q / (q.factorial : ℝ) *
        iteratedDerivWithin q (x r μ) (Icc 0 (Real.pi * F.L)) y| ≤ |Cx| * Real.pi ^ (M + 1) * h ^ (M - r + 1) := by
      intro r hr
      have hr' : r ≤ M := by have := Finset.mem_range.mp hr; omega
      have hf : ContDiffOn ℝ ((M - r + 1 : ℕ) : WithTop ℕ∞) (x r μ) (Icc 0 (Real.pi * F.L)) := by
        have := hreg μ hμ r hr'
        rwa [show M + 1 - r = M - r + 1 by omega] at this
      have hC : ∀ z ∈ Icc 0 (Real.pi * F.L), |iteratedDerivWithin (M - r + 1) (x r μ) (Icc 0 (Real.pi * F.L)) z| ≤ Cx :=
        fun z hz => hCx μ hμ r hr' (M - r + 1) (by omega) z hz
      have ht := taylor_Icc hpiL (M - r) hf hC hyI hy'I hyy'
      rw [sum_range_succ_Icc, hyy] at ht
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_mul, iteratedDerivWithin_zero] at ht
      have e : (x r μ y - x r μ y') + ∑ q ∈ Finset.Icc 1 (M - r), (Real.pi * h) ^ q / (q.factorial : ℝ) *
          iteratedDerivWithin q (x r μ) (Icc 0 (Real.pi * F.L)) y
          = -(x r μ y' - (x r μ y + ∑ q ∈ Finset.Icc 1 (M - r), ((q.factorial : ℝ)⁻¹ * (Real.pi * h) ^ q *
            iteratedDerivWithin q (x r μ) (Icc 0 (Real.pi * F.L)) y))) := by
        have : ∀ q ∈ Finset.Icc 1 (M - r), (Real.pi * h) ^ q / (q.factorial : ℝ) * iteratedDerivWithin q (x r μ) (Icc 0 (Real.pi * F.L)) y
            = (q.factorial : ℝ)⁻¹ * (Real.pi * h) ^ q * iteratedDerivWithin q (x r μ) (Icc 0 (Real.pi * F.L)) y := by
          intro q _; rw [div_eq_inv_mul]
        rw [Finset.sum_congr rfl this]; ring
      rw [e, abs_neg]
      refine ht.trans ?_
      have hfac : (1 : ℝ) ≤ ((M - r + 1).factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hpw : Real.pi ^ (M - r + 1) ≤ Real.pi ^ (M + 1) := pow_le_pow_right₀ hpi1 (by omega)
      have hhp : 0 ≤ h ^ (M - r + 1) := by positivity
      calc Cx * (Real.pi * h) ^ (M - r + 1) / ((M - r + 1).factorial : ℝ)
          ≤ |Cx| * (Real.pi * h) ^ (M - r + 1) := by
            rw [div_le_iff₀ (by positivity)]
            have : 0 ≤ |Cx| * (Real.pi * h) ^ (M - r + 1) := by positivity
            nlinarith [le_abs_self Cx, pow_nonneg (mul_pos hpi hst).le (M - r + 1)]
        _ = |Cx| * Real.pi ^ (M - r + 1) * h ^ (M - r + 1) := by rw [mul_pow]; ring
        _ ≤ |Cx| * Real.pi ^ (M + 1) * h ^ (M - r + 1) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpw (abs_nonneg _)) hhp
    have hEi := hexp μ hμ N hh0' X Um hE i
    have hEj := hexp μ hμ N hh0' X Um hE j
    -- regrouping of the Taylor sums
    have hreg_eq : ∑ r ∈ range (M + 1), h ^ r * ∑ q ∈ Finset.Icc 1 (M - r), (Real.pi * h) ^ q / (q.factorial : ℝ) *
          iteratedDerivWithin q (x r μ) (Icc 0 (Real.pi * F.L)) y
        = ∑ p ∈ Finset.Icc 1 M, h ^ p * ∑ r ∈ range p, Real.pi ^ (p - r) / ((p - r).factorial : ℝ) *
          iteratedDerivWithin (p - r) (x r μ) (Icc 0 (Real.pi * F.L)) y := by
      have key := sum_reindex_gap M (fun r q => h ^ (r + q) * (Real.pi ^ q / (q.factorial : ℝ) *
        iteratedDerivWithin q (x r μ) (Icc 0 (Real.pi * F.L)) y))
      have e1 : ∑ p ∈ Finset.Icc 1 M, h ^ p * ∑ r ∈ range p, Real.pi ^ (p - r) / ((p - r).factorial : ℝ) *
          iteratedDerivWithin (p - r) (x r μ) (Icc 0 (Real.pi * F.L)) y
          = ∑ p ∈ Finset.Icc 1 M, ∑ r ∈ range p, h ^ (r + (p - r)) * (Real.pi ^ (p - r) / ((p - r).factorial : ℝ) *
            iteratedDerivWithin (p - r) (x r μ) (Icc 0 (Real.pi * F.L)) y) := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r hr => ?_)
        have : r + (p - r) = p := by have := Finset.mem_range.mp hr; omega
        rw [this]
      have e2 : ∑ r ∈ range (M + 1), h ^ r * ∑ q ∈ Finset.Icc 1 (M - r), (Real.pi * h) ^ q / (q.factorial : ℝ) *
          iteratedDerivWithin q (x r μ) (Icc 0 (Real.pi * F.L)) y
          = ∑ r ∈ range (M + 1), ∑ q ∈ Finset.Icc 1 (M - r), h ^ (r + q) * (Real.pi ^ q / (q.factorial : ℝ) *
            iteratedDerivWithin q (x r μ) (Icc 0 (Real.pi * F.L)) y) := by
        refine Finset.sum_congr rfl (fun r hr => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        rw [mul_pow, pow_add]; ring
      rw [e1, e2]
      exact key.symm
    show |(X i - X j) - ∑ p ∈ Finset.Icc 1 M, h ^ p * (-∑ r ∈ range p, Real.pi ^ (p - r) / ((p - r).factorial : ℝ) *
      iteratedDerivWithin (p - r) (x r μ) (Icc 0 (Real.pi * F.L)) y)| ≤ _
    have hneg : ∑ p ∈ Finset.Icc 1 M, h ^ p * (-∑ r ∈ range p, Real.pi ^ (p - r) / ((p - r).factorial : ℝ) *
        iteratedDerivWithin (p - r) (x r μ) (Icc 0 (Real.pi * F.L)) y)
        = -∑ r ∈ range (M + 1), h ^ r * ∑ q ∈ Finset.Icc 1 (M - r), (Real.pi * h) ^ q / (q.factorial : ℝ) *
          iteratedDerivWithin q (x r μ) (Icc 0 (Real.pi * F.L)) y := by
      rw [hreg_eq, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [hneg]
    have hid : (X i - X j) - -∑ r ∈ range (M + 1), h ^ r * ∑ q ∈ Finset.Icc 1 (M - r), (Real.pi * h) ^ q / (q.factorial : ℝ) *
          iteratedDerivWithin q (x r μ) (Icc 0 (Real.pi * F.L)) y
        = (X i - ∑ r ∈ range (M + 1), h ^ r * x r μ y) - (X j - ∑ r ∈ range (M + 1), h ^ r * x r μ y')
          + ∑ r ∈ range (M + 1), h ^ r * ((x r μ y - x r μ y') + ∑ q ∈ Finset.Icc 1 (M - r), (Real.pi * h) ^ q / (q.factorial : ℝ) *
            iteratedDerivWithin q (x r μ) (Icc 0 (Real.pi * F.L)) y) := by
      simp only [mul_add, Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hid]
    have hsumb : |∑ r ∈ range (M + 1), h ^ r * ((x r μ y - x r μ y') + ∑ q ∈ Finset.Icc 1 (M - r), (Real.pi * h) ^ q / (q.factorial : ℝ) *
          iteratedDerivWithin q (x r μ) (Icc 0 (Real.pi * F.L)) y)| ≤ (M + 1) * |Cx| * Real.pi ^ (M + 1) * h ^ (M + 1) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ r ∈ range (M + 1), |h ^ r * ((x r μ y - x r μ y') + ∑ q ∈ Finset.Icc 1 (M - r), (Real.pi * h) ^ q / (q.factorial : ℝ) *
          iteratedDerivWithin q (x r μ) (Icc 0 (Real.pi * F.L)) y)| ≤ |Cx| * Real.pi ^ (M + 1) * h ^ (M + 1) := by
        intro r hr
        have hr' : r ≤ M := by have := Finset.mem_range.mp hr; omega
        rw [abs_mul, abs_of_pos (pow_pos hst r)]
        calc h ^ r * |_| ≤ h ^ r * (|Cx| * Real.pi ^ (M + 1) * h ^ (M - r + 1)) :=
              mul_le_mul_of_nonneg_left (hd r hr) (pow_pos hst r).le
          _ = |Cx| * Real.pi ^ (M + 1) * h ^ (M + 1) := by
              have : h ^ r * h ^ (M - r + 1) = h ^ (M + 1) := by rw [← pow_add]; congr 1; omega
              calc h ^ r * (|Cx| * Real.pi ^ (M + 1) * h ^ (M - r + 1)) = |Cx| * Real.pi ^ (M + 1) * (h ^ r * h ^ (M - r + 1)) := by ring
                _ = _ := by rw [this]
      refine (Finset.sum_le_sum this).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring_nf
      exact le_rfl
    have hEi' : |X i - ∑ r ∈ range (M + 1), h ^ r * x r μ y| ≤ |C| * h ^ (M + 1) :=
      hEi.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hst.le _))
    have hEj' : |X j - ∑ r ∈ range (M + 1), h ^ r * x r μ y'| ≤ |C| * h ^ (M + 1) :=
      hEj.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hst.le _))
    calc _ ≤ |(X i - ∑ r ∈ range (M + 1), h ^ r * x r μ y) - (X j - ∑ r ∈ range (M + 1), h ^ r * x r μ y')| + _ := abs_add_le _ _
      _ ≤ (|C| * h ^ (M + 1) + |C| * h ^ (M + 1)) + (M + 1) * |Cx| * Real.pi ^ (M + 1) * h ^ (M + 1) :=
          add_le_add ((abs_sub _ _).trans (add_le_add hEi' hEj')) hsumb
      _ = _ := by ring

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.contDiffOn_iteratedDerivWithin_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.contDiffOn_iteratedDerivWithin_nat

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.taylor_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.taylor_Icc

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.corEigenGapM_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.corEigenGapM_of_bound

end FormalResearch.JacobiEigenvectors.TheoremA

end
