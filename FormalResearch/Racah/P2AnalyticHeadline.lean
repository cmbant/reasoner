module

public import FormalResearch.Racah.P2AnalyticBridge3j
public import FormalResearch.Racah.P2AnalyticBulk3j
public import FormalResearch.Racah.P2AnalyticUniform3j

/-!
# Weyl P2: the analytic headline theorems with the Wigner `d`-function

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:3jeven` (`eq:3jevenexp`),
`rem:movingpoint`, `thm:6jeven` (`eq:6jleading`, `eq:6jevenexp`), `thm:uniformedge`
(`eq:3juniformedge`, `eq:6juniformedge`).

The analytic layer (`P2AnalyticBulk3j`, `Bulk6j`, `Uniform3j`, `Uniform6j`) proves these statements with
the explicit `t = 0` carriers `dZero3`, `dZero6` in place of Wigner's `d`; the bridges
(`P2AnalyticBridge3j`, `Bridge6j`) identify those carriers with `d^L_{Mσ}(arccos x)` and
`d^f_{nm}(arccos x)` (`wignerSmallDx`).  This file combines them, so that every leading coefficient is
the Wigner function, exactly as in the paper.

## Dictionary (paper ↔ Lean)

* `Φ_L^{M,σ}(x; N⁻¹)` = `Phi3j L M σ N μ` at `x = 2μ/N` (`SpecAdm M σ N`, `Lat4 M σ N μ`: the physical
  admissible grid); `d^L_{Mσ}(arccos x)` = `wignerSmallDx L M σ x`.
* The admissibility of `L, M, σ`: `L = L₀ + k` with `L₀ = max |M| |σ|`, `k : ℕ` (`hL`), and
  `M ± σ` integers, recorded as `|M - σ| = α`, `|M + σ| = β` with `α β : ℕ` (`hα`, `hβ`).
* `U = (a, b)` open interval with `K ⊂ U ⋐ (-1,1)`: `K ⊆ Ioo a b`, `Icc a b ⊆ Ioo (-1) 1`.
* `G_L^{M,σ}(x,t)` = `Gc3 M σ k x t` (the closed-form germ); `f_{2r}` = `f3even M σ k r` (its `t^r`
  Taylor coefficient at `t = 0`).
* `Φ_f(A,B,C)` = `Phi6 a b c f m n` at `A = wA a n`, `B = wB b m`, `C = wC c` (the four triads of the
  `6j` family `IsTri`); `d^f_{nm}(arccos x)` = `wignerSmallDx f n m x` (row `n`, column `m`);
  admissible `f, m, n`: `f ± m`, `f ± n` natural numbers; `G_{f,2r}` = `G6even f m n r`; the open
  strict-triangle cone = `StrictTri` (on normalised shapes, scale invariant); `𝒯_δ` = `TriDelta δ`, in
  homogeneous form `δ H ≤ min(A,B,C,A+B-C,A+C-B,B+C-A)` (`Tmin`), `H = max (A,B,C)` (`Hscale`).
* `W(x) = ((1-x)/2)^{p/2} ((1+x)/2)^{q/2}` = `Wedge p q x`; `E_N W_{3j}` = `edgeEnv3 M σ x N⁻²`;
  `E_{A,B}(C) W_{6j}(x)` = `edgeEW`.

## Results

* `thm_3jeven` (**`thm:3jeven`**, proved): germ `G` real analytic on `U × (-ρ,ρ)`,
  `Φ = G(x, N⁻²)` at every large admissible grid point `x ∈ K`, `G(x,0) = d^L_{Mσ}(arccos x)`,
  the expansion `Φ = ∑_{r<R} f_{2r} N^{-2r} + O_K(N^{-2R})`, `f_0 = d^L_{Mσ}(arccos x)` on `[-1,1]`,
  and each `f_{2r}` real analytic on `(-1,1)`.
* `thm_3jeven_noOdd`: the same expansion in powers of `N⁻¹`, whose odd coefficients are `0`.
* `thm_3jeven_leading`: `Φ = d^L_{Mσ}(arccos x) + O_K(N⁻²)`.
* `analyticOnNhd_wignerSmallDx_of_labels`: `x ↦ d^L_{Mσ}(arccos x)` is real analytic on `(-1,1)`.
* `rem_movingpoint` (**`rem:movingpoint`**): along a moving point `x_N = 2μ/N`, `μ` fixed,
  `d(arccos x_N) = d(π/2) + x_N d'(0) + O(N⁻²)` and `Φ` has the same expansion.
* `thm_6jeven` (**`thm:6jeven`**, proved): `G_{f,2r}` real analytic on the whole open strict-triangle
  cone, homogeneous of degree `-2r`, `G_{f,0} = d^f_{nm}(arccos x)`, `x = (A²+B²-C²)/(2AB)`, the germ
  in `S⁻²` (`G_{f,2r} = S^{-2r} a_{f,r}`) with a uniform radius over compact shape sets, and the
  expansion `Φ_f = ∑_{r<R} G_{f,2r} + O(H^{-2R})` on `𝒯_δ`.
* `thm_uniformedge_3j` (**`thm:uniformedge`(a)**) and `thm_uniformedge_6j` (**`thm:uniformedge`(b)**):
  the uniform edge-factorised expansions with `W s_0 = d^L_{Mσ}(arccos x)`, resp.
  `d^f_{nm}(arccos x)`.

Not covered: that the coefficients of `s_r` in (b) are rational in `δ` with poles only at `δ = ±1`
(`P2AnalyticUniform6j` proves analyticity in `δ ∈ (-1,1)`), the convergence-domain statements.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner Set Filter Topology

/-- The edge weight `W(x) = ((1-x)/2)^{p/2} ((1+x)/2)^{q/2}` of the paper (`W_{3j}` with
`(p,q) = (p_+,p_-) = (|M-σ|, |M+σ|)`, `W_{6j}` with `(p,q) = (p_min, p_max)`), with real exponents. -/
noncomputable def Wedge (p q : ℕ) (x : ℝ) : ℝ :=
  ((1 - x) / 2) ^ ((p : ℝ) / 2) * ((1 + x) / 2) ^ ((q : ℝ) / 2)

/-- On `[-1,1]` the weight is the positive square root `√(((1-x)/2)^p ((1+x)/2)^q)`. -/
lemma Wedge_eq_sqrt (p q : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Wedge p q x = Real.sqrt (((1 - x) / 2) ^ p * ((1 + x) / 2) ^ q) := by
  have ha : 0 ≤ (1 - x) / 2 := by linarith [hx.2]
  have hb : 0 ≤ (1 + x) / 2 := by linarith [hx.1]
  rw [Real.sqrt_mul (pow_nonneg ha p), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast ((1 - x) / 2) p, ← Real.rpow_natCast ((1 + x) / 2) q,
    ← Real.rpow_mul ha, ← Real.rpow_mul hb]
  unfold Wedge
  congr 2 <;> ring

/-! ### `thm:3jeven` -/

/-- **`x ↦ d^L_{Mσ}(arccos x)` is real analytic on `(-1,1)`** for admissible labels
(`L = L₀ + k`, `M ± σ` integers): it agrees on `[-1,1]` with the analytic coefficient `f_0`. -/
theorem analyticOnNhd_wignerSmallDx_of_labels (M σ L : ℚ) (k : ℕ) (hL : L = max |M| |σ| + k)
    (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β) :
    AnalyticOnNhd ℝ (wignerSmallDx L M σ) (Ioo (-1 : ℝ) 1) := by
  subst hL
  intro x hx
  refine (analyticOnNhd_f3even M σ k 0 x hx).congr ?_
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  rw [f3even_zero, dZero3_eq_wignerD M σ α β hα hβ (Ioo_subset_Icc_self hy) k]

/-- **`thm:3jeven`** (Regge-midpoint even expansion; proved).  Fix `L = L₀ + k`, `M`, `σ` with
`M ± σ` integers and a compact `K ⊆ (-1,1)`.  There are an open interval `U = (a,b)` with
`K ⊂ U ⋐ (-1,1)`, `ρ > 0` and the function `G = Gc3 M σ k`, real analytic on `U × (-ρ,ρ)`, such that at
every sufficiently large admissible physical grid point `x = 2μ/N ∈ K`,
`Φ_L^{M,σ}(x; N⁻¹) = G(x, N⁻²)`; moreover `G(x,0) = d^L_{Mσ}(arccos x)` on `U`.  Consequently, for every
`R`, `Φ = ∑_{r<R} f_{2r}(x) N^{-2r} + O_K(N^{-2R})` uniformly on the grid points in `K` (`eq:3jevenexp`),
with `f_{2r} = f3even M σ k r` real analytic on `(-1,1)`, `f_0(x) = d^L_{Mσ}(arccos x)` on `[-1,1]`.
No odd power of `N⁻¹` occurs (`thm_3jeven_noOdd`).  Hypotheses: `hL` is `L - L₀ ∈ ℕ`; `hα`, `hβ` say
`M ± σ` are integers (the paper's admissibility of `L, M, σ`); "sufficiently large admissible physical
grid point" is `SpecAdm M σ N`, `Lat4 M σ N μ`, `N₀ ≤ N`. -/
theorem thm_3jeven (M σ L : ℚ) (k : ℕ) (hL : L = max |M| |σ| + k) (α β : ℕ)
    (hα : |M - σ| = α) (hβ : |M + σ| = β) {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    ∃ a b ρ N₀ : ℝ, 0 < ρ ∧ K ⊆ Ioo a b ∧ Icc a b ⊆ Ioo (-1 : ℝ) 1 ∧
      AnalyticOnNhd ℝ (fun q : ℝ × ℝ => Gc3 M σ k q.1 q.2) (Ioo a b ×ˢ Ioo (-ρ) ρ) ∧
      (∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₀ ≤ (N : ℝ) → 2 * (μ : ℝ) / N ∈ K →
        Phi3j L M σ N μ = Gc3 M σ k (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2)) ∧
      (∀ x ∈ Ioo a b, Gc3 M σ k x 0 = wignerSmallDx L M σ x) ∧
      (∀ R : ℕ, ∃ C N₁ : ℝ, ∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₁ ≤ (N : ℝ) →
        2 * (μ : ℝ) / N ∈ K →
        |Phi3j L M σ N μ -
            ∑ r ∈ Finset.range R, f3even M σ k r (2 * (μ : ℝ) / N) / (N : ℝ) ^ (2 * r)| ≤
          C / (N : ℝ) ^ (2 * R)) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, f3even M σ k 0 x = wignerSmallDx L M σ x) ∧
      (∀ r : ℕ, AnalyticOnNhd ℝ (f3even M σ k r) (Ioo (-1 : ℝ) 1)) := by
  obtain ⟨δ, ρ, N₀, hδ, hρ, hKU, hI, hAn, hGeq, hG0, hexp⟩ :=
    Phi3j_thm_3jeven M σ L k hL hK hKI
  have hL' := hL
  subst hL
  refine ⟨-1 + δ, 1 - δ, ρ, N₀, hρ, hKU, hI, hAn, fun N μ hA hlat hN hx => (hGeq N μ hA hlat hN hx).2,
    fun x hx => ?_, hexp, fun x hx => ?_, analyticOnNhd_f3even M σ k⟩
  · exact Gc3_zero_eq_wignerD M σ α β hα hβ (hI ⟨hx.1.le, hx.2.le⟩ |> Ioo_subset_Icc_self) k
  · rw [f3even_zero, dZero3_eq_wignerD M σ α β hα hβ hx k]

/-- **`thm:3jeven` leading term**: `Φ_L^{M,σ}(x; N⁻¹) = d^L_{Mσ}(arccos x) + O_K(N⁻²)` uniformly on the
admissible grid points in `K` (the case `R = 1` of `eq:3jevenexp`, with `f_0 = d`). -/
theorem thm_3jeven_leading (M σ L : ℚ) (k : ℕ) (hL : L = max |M| |σ| + k) (α β : ℕ)
    (hα : |M - σ| = α) (hβ : |M + σ| = β) {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    ∃ C N₀ : ℝ, ∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₀ ≤ (N : ℝ) →
      2 * (μ : ℝ) / N ∈ K →
      |Phi3j L M σ N μ - wignerSmallDx L M σ (2 * (μ : ℝ) / N)| ≤ C / (N : ℝ) ^ 2 := by
  obtain ⟨C, N₀, h⟩ := Phi3j_even_expansion M σ L k hL hK hKI 1
  refine ⟨C, N₀, fun N μ hA hlat hN hx => ?_⟩
  have := h N μ hA hlat hN hx
  have hx1 : 2 * (μ : ℝ) / N ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self (hKI hx)
  simp only [Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, div_one, mul_one] at this
  rw [f3even_zero, hL, dZero3_eq_wignerD M σ α β hα hβ hx1 k] at this
  simpa [hL] using this

/-- The odd-power-free coefficients: `c_j = f_{j/2}` for even `j`, `0` for odd `j`. -/
noncomputable def f3full (M σ : ℚ) (k : ℕ) (j : ℕ) (x : ℝ) : ℝ :=
  if Even j then f3even M σ k (j / 2) x else 0

lemma sum_f3full (M σ : ℚ) (k : ℕ) (N x : ℝ) (R : ℕ) :
    ∑ j ∈ Finset.range (2 * R), f3full M σ k j x / N ^ j =
      ∑ r ∈ Finset.range R, f3even M σ k r x / N ^ (2 * r) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [show 2 * (R + 1) = 2 * R + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    have h1 : f3full M σ k (2 * R) x = f3even M σ k R x := by
      simp [f3full]
    have h2 : f3full M σ k (2 * R + 1) x = 0 := by
      simp [f3full, Nat.not_even_iff_odd.mpr (odd_two_mul_add_one R)]
    rw [h1, h2]; simp

/-- **`thm:3jeven`, "no odd power of `N⁻¹` occurs"**: in powers of `N⁻¹` the expansion is
`Φ = ∑_{j<2R} c_j(x) N^{-j} + O_K(N^{-2R})` with `c_{2r} = f_{2r}` and `c_j = 0` for odd `j`; in
particular the first omitted power is even, so that the remainder is `O(N^{-2R})` rather than
`O(N^{-2R+1})`, and `c_0 = d^L_{Mσ}(arccos x)`. -/
theorem thm_3jeven_noOdd (M σ L : ℚ) (k : ℕ) (hL : L = max |M| |σ| + k) (α β : ℕ)
    (hα : |M - σ| = α) (hβ : |M + σ| = β) {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Ioo (-1 : ℝ) 1) (R : ℕ) :
    (∀ j : ℕ, Odd j → ∀ x, f3full M σ k j x = 0) ∧
    (∀ x ∈ Icc (-1 : ℝ) 1, f3full M σ k 0 x = wignerSmallDx L M σ x) ∧
    ∃ C N₀ : ℝ, ∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₀ ≤ (N : ℝ) →
      2 * (μ : ℝ) / N ∈ K →
      |Phi3j L M σ N μ -
          ∑ j ∈ Finset.range (2 * R), f3full M σ k j (2 * (μ : ℝ) / N) / (N : ℝ) ^ j| ≤
        C / (N : ℝ) ^ (2 * R) := by
  refine ⟨fun j hj x => by simp [f3full, Nat.not_even_iff_odd.mpr hj], fun x hx => ?_, ?_⟩
  · simp only [f3full, Even.zero, ite_true, Nat.zero_div]
    rw [f3even_zero, hL, dZero3_eq_wignerD M σ α β hα hβ hx k]
  · obtain ⟨C, N₀, h⟩ := Phi3j_even_expansion M σ L k hL hK hKI R
    exact ⟨C, N₀, fun N μ hA hlat hN hx => by rw [sum_f3full]; exact h N μ hA hlat hN hx⟩

/-! ### `rem:movingpoint` -/

/-- Second-order Taylor bound at `0` for a function analytic on `(-1,1)`. -/
lemma taylor2_at_zero {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g (Ioo (-1 : ℝ) 1)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ y : ℝ, |y| ≤ ρ → |g y - (g 0 + y * deriv g 0)| ≤ C * y ^ 2 := by
  have hU : IsOpen {q : ℝ × ℝ | q.2 ∈ Ioo (-1 : ℝ) 1} :=
    isOpen_Ioo.preimage continuous_snd
  have hG : AnalyticOnNhd ℝ (fun q : ℝ × ℝ => g q.2) {q : ℝ × ℝ | q.2 ∈ Ioo (-1 : ℝ) 1} :=
    fun q hq => (hg q.2 hq).comp_of_eq analyticAt_snd rfl
  have hKU : ({(0 : ℝ)} : Set ℝ) ×ˢ ({0} : Set ℝ) ⊆ {q : ℝ × ℝ | q.2 ∈ Ioo (-1 : ℝ) 1} := by
    rintro ⟨z, t⟩ ⟨-, ht⟩
    have : t = 0 := ht
    subst this
    exact ⟨by norm_num, by norm_num⟩
  obtain ⟨ρ, hρ, C, hC⟩ := taylor_uniform_of_analytic hU hG isCompact_singleton hKU 2
  refine ⟨ρ, hρ, C, fun y hy => ?_⟩
  have := hC 0 rfl y hy
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, taylorCoeff,
    iteratedDeriv_zero, iteratedDeriv_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
    div_one, pow_zero, pow_one, zero_add, sq_abs] at this
  simpa [mul_comm] using this

/-- **`rem:movingpoint`.**  The even expansion is a statement at fixed `x`.  Along a moving lattice
point `x_N = 2μ/N` with fixed `μ` (`Lat4 M σ N μ`, `N → ∞`) one has, with `d(x) = d^L_{Mσ}(arccos x)`,
`d(x_N) = d(π/2) + x_N d'(0) + O(N⁻²)` and `Φ_L^{M,σ}(x_N; N⁻¹)` equals the same right-hand side up to
`O(N⁻²)`: the `N⁻¹` term is the displacement of the evaluation point, not an odd deformation. -/
theorem rem_movingpoint (M σ L : ℚ) (k : ℕ) (hL : L = max |M| |σ| + k) (α β : ℕ)
    (hα : |M - σ| = α) (hβ : |M + σ| = β) (μ : ℚ) :
    ∃ C N₀ : ℝ, ∀ N : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₀ ≤ (N : ℝ) →
      |wignerSmallD L M σ (Real.pi / 2) + 2 * (μ : ℝ) / N * deriv (wignerSmallDx L M σ) 0 -
          wignerSmallDx L M σ (2 * (μ : ℝ) / N)| ≤ C / (N : ℝ) ^ 2 ∧
      |wignerSmallD L M σ (Real.pi / 2) + 2 * (μ : ℝ) / N * deriv (wignerSmallDx L M σ) 0 -
          Phi3j L M σ N μ| ≤ C / (N : ℝ) ^ 2 := by
  have hg := analyticOnNhd_wignerSmallDx_of_labels M σ L k hL α β hα hβ
  obtain ⟨ρ, hρ, C₁, hC₁⟩ := taylor2_at_zero hg
  have hK : IsCompact (Icc (-(1 / 2 : ℝ)) (1 / 2)) := isCompact_Icc
  have hKI : Icc (-(1 / 2 : ℝ)) (1 / 2) ⊆ Ioo (-1 : ℝ) 1 := by
    intro y hy; constructor <;> linarith [hy.1, hy.2]
  obtain ⟨C₂, N₂, h2⟩ := thm_3jeven_leading M σ L k hL α β hα hβ hK hKI
  have h0 : wignerSmallDx L M σ 0 = wignerSmallD L M σ (Real.pi / 2) := by
    unfold wignerSmallDx; rw [Real.arccos_zero]
  refine ⟨|C₁| * (2 * μ : ℝ) ^ 2 + |C₂|, max N₂ (max 1 (max (4 * |(μ : ℝ)|) (2 * |(μ : ℝ)| / ρ))), ?_⟩
  intro N hA hlat hN
  have hN2 : N₂ ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : 4 * |(μ : ℝ)| ≤ (N : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hN4 : 2 * |(μ : ℝ)| / ρ ≤ (N : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hy : |2 * (μ : ℝ) / N| ≤ 1 / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hNpos, div_le_iff₀ hNpos]
    simp only [abs_two]; nlinarith
  have hyρ : |2 * (μ : ℝ) / N| ≤ ρ := by
    rw [abs_div, abs_mul, abs_of_pos hNpos, div_le_iff₀ hNpos]
    simp only [abs_two]
    rw [div_le_iff₀ hρ] at hN4
    nlinarith
  have hyK : 2 * (μ : ℝ) / N ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := abs_le.mp hy
  have hT := hC₁ _ hyρ
  have hP := h2 N μ hA hlat hN2 hyK
  have e : (2 * (μ : ℝ) / N) ^ 2 = (2 * μ : ℝ) ^ 2 / (N : ℝ) ^ 2 := by rw [div_pow]
  have hT' : |wignerSmallDx L M σ (2 * (μ : ℝ) / N) -
      (wignerSmallD L M σ (Real.pi / 2) + 2 * (μ : ℝ) / N * deriv (wignerSmallDx L M σ) 0)| ≤
        C₁ * ((2 * μ : ℝ) ^ 2 / (N : ℝ) ^ 2) := by
    rw [← e, ← h0]; exact hT
  have hN2pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hb1 : C₁ * ((2 * μ : ℝ) ^ 2 / (N : ℝ) ^ 2) ≤ |C₁| * (2 * μ : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C₁) (sq_nonneg _)) hN2pos.le
  have hb2 : C₂ / (N : ℝ) ^ 2 ≤ |C₂| / (N : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (le_abs_self C₂) hN2pos.le
  have hsum : (|C₁| * (2 * μ : ℝ) ^ 2 + |C₂|) / (N : ℝ) ^ 2 =
      |C₁| * (2 * μ : ℝ) ^ 2 / (N : ℝ) ^ 2 + |C₂| / (N : ℝ) ^ 2 := by ring
  have hnn : 0 ≤ |C₁| * (2 * μ : ℝ) ^ 2 / (N : ℝ) ^ 2 := by positivity
  have hnn2 : 0 ≤ |C₂| / (N : ℝ) ^ 2 := by positivity
  constructor
  · rw [abs_sub_comm, hsum]; linarith
  · rw [hsum]
    have h3 : |wignerSmallD L M σ (Real.pi / 2) + 2 * (μ : ℝ) / N * deriv (wignerSmallDx L M σ) 0 -
        Phi3j L M σ N μ| ≤
        |wignerSmallD L M σ (Real.pi / 2) + 2 * (μ : ℝ) / N * deriv (wignerSmallDx L M σ) 0 -
          wignerSmallDx L M σ (2 * (μ : ℝ) / N)| +
        |wignerSmallDx L M σ (2 * (μ : ℝ) / N) - Phi3j L M σ N μ| := abs_sub_le _ _ _
    rw [abs_sub_comm (wignerSmallDx L M σ _)] at h3
    rw [abs_sub_comm] at hT'
    linarith

/-! ### `thm:uniformedge` (a) -/

/-- At `t = 0` the edge envelope `E_N W_{3j}` is the weight `W_{3j}(x)` (`E_N → 1`). -/
lemma edgeEnv3_zero_eq_Wedge (M σ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : edgeEnv3 M σ x 0 = Wedge α β x := by
  rw [Wedge_eq_sqrt α β hx]
  unfold edgeEnv3
  rw [br3_pPlus hα, br3_pMinus hβ]
  simp [Ct_zero_t]

/-- **`thm:uniformedge` (a)** (`eq:3juniformedge`; proved).  Fix `L = L₀ + k`, `M`, `σ` with `M ± σ`
integers.  The polynomials `s_r = edgeS3 M σ k r` in `t = (1-x)/2` have degree at most `d = L - L₀ = k`,
and `W_{3j}(x) s_0(t) = d^L_{Mσ}(arccos x)` on `[-1,1]`.  For every `R` there are `C, N₀` such that on
the whole admissible physical grid (every `μ` with `Lat4 M σ N μ`, no restriction on `x`)
`|Φ_L^{M,σ} - E_N W_{3j} ∑_{r<R} s_r(t) N^{-2r}| ≤ C · E_N W_{3j} · N^{-2R}`, which is the paper's
`Φ = E_N W_{3j} [∑ s_r N^{-2r} + O(N^{-2R})]` uniformly on `𝒳_N`.  Here `E_N W_{3j}` is
`edgeEnv3 M σ x N⁻²` (the square root of the product of the two centred factors, `= W_{3j}` at
`N⁻² = 0`, `edgeEnv3_zero_eq_Wedge`).  Not covered: the convergence domain `N > L` and its exactness,
and `0 < c ≤ E_N ≤ 1`. -/
theorem thm_uniformedge_3j (M σ L : ℚ) (k : ℕ) (hL : L = max |M| |σ| + k) (α β : ℕ)
    (hα : |M - σ| = α) (hβ : |M + σ| = β) :
    (∀ r : ℕ, (edgeS3 M σ k r).natDegree ≤ k) ∧
    (∀ x ∈ Icc (-1 : ℝ) 1,
      Wedge α β x * (edgeS3 M σ k 0).eval ((1 - x) / 2) = wignerSmallDx L M σ x) ∧
    ∀ R : ℕ, ∃ C N₀ : ℝ, ∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₀ ≤ (N : ℝ) →
      |Phi3j L M σ N μ - edgeEnv3 M σ (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2) *
          ∑ r ∈ Finset.range R,
            (edgeS3 M σ k r).eval ((1 - 2 * (μ : ℝ) / N) / 2) / (N : ℝ) ^ (2 * r)| ≤
        C * edgeEnv3 M σ (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2) / (N : ℝ) ^ (2 * R) := by
  refine ⟨natDegree_edgeS3_le M σ k, fun x hx => ?_, fun R => Phi3j_uniform_edge M σ L k hL R⟩
  rw [← edgeEnv3_zero_eq_Wedge M σ α β hα hβ hx, edgeEnv3_mul_edgeS3_zero, hL,
    dZero3_eq_wignerD M σ α β hα hβ hx k]

/-- info: 'FormalResearch.Racah.analyticOnNhd_wignerSmallDx_of_labels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analyticOnNhd_wignerSmallDx_of_labels

/-- info: 'FormalResearch.Racah.thm_3jeven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_3jeven

/-- info: 'FormalResearch.Racah.thm_3jeven_leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_3jeven_leading

/-- info: 'FormalResearch.Racah.thm_3jeven_noOdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_3jeven_noOdd

/-- info: 'FormalResearch.Racah.rem_movingpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rem_movingpoint

/-- info: 'FormalResearch.Racah.thm_uniformedge_3j' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_uniformedge_3j

end FormalResearch.Racah
