module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Jacobi-chain comparison on the forbidden side (Weyl P3, `prop:forbidden-decay`, `prop:exact-hyperbolicity`)

Source: `Weyl/P3/paper/weyl_midpoint_semiclassics.tex`, `prop:exact-hyperbolicity` (T:996),
`prop:forbidden-decay` (T:1008) and `rem:airy2-R`(b), with the proofs in
`weyl_midpoint_semiclassics_appendices.tex`, subsection "Hyperbolicity and the physical solution on the
forbidden side" (`(F1)`-`(F3)`, `eq:forbidden-slope`, `eq:forbidden-const-ratio`).

## What is formalised (proved; pure order/real-inequality arguments)

* `backward_ratio`: the backward ratio recursion `ρ_{i-1} = A_i/(c_i - A_{i+1}ρ_i)`, `ρ_N = 0`, in the
  form for the solution `Y` of `A_{i+1}Y_{i+1} + A_iY_{i-1} = c_iY_i` (`j ≤ i ≤ N`, `A_i > 0`,
  `A_{N+1} = 0`, `Y_N ≠ 0`) under a constant-ratio supersolution `A_{i+1}y + A_i/y ≤ c_i`: all
  `Y_i` (`j-1 ≤ i ≤ N`) are nonzero of the sign of `Y_N` and `|Y_{i+1}| ≤ y|Y_i|`.  `y = 1` is
  `prop:forbidden-decay`(a) (under exact hyperbolicity `A_i + A_{i+1} ≤ c_i`), general `y` is
  `eq:forbidden-const-ratio`/(b).  (`y ≤ 1` is not needed.)
* `etilde`, `Dom`, `etilde_concaveOn` (`(F1)`: concavity of `ẽ(σ) = √((1-σ/σ₁)(1-σ/σ₂))`, as the
  geometric mean of two nonnegative affine functions, for *all* real `p = σ₁⁻¹`, `q = σ₂⁻¹`),
  `etilde_antitone`, `etilde_le_one`, `etilde_hasDerivAt_zero`, `Psi_plus_concaveOn`,
  `Psi_minus_convexOn`, `Psi_minus_monotoneOn`, `Psi_plus_deriv_zero` (`(F2)`).
* `Phi_convexOn`, `forbidden_slope`: `eq:forbidden-slope`, `Φ(σ) ≥ κ(σ - σ_*)`, from the single fact
  that `Φ = τ(x - β₀σ) - ẽ` is convex for either sign `τ` (this replaces the two-case "Ψ_+ concave,
  Ψ_- convex" argument).
* `hyperbolic_of_slope`: the logical core of the proof of `prop:exact-hyperbolicity`
  (`A_k + A_{k+1} ≤ τ(x - B_k)` from `A_j ≤ ½(1+r₁)ẽ(σ_j)`, `|B_k - β₀σ₀| ≤ r₂`, `κ(σ₀ - σ_*) ≥ r₁ + r₂`);
  `F_le_cosh_etilde`: the Jensen step in the verification of (b).
* `exact_hyperbolicity_hahn_racah`: `prop:exact-hyperbolicity` for the Hahn and centered Racah chains
  *with the paper's explicit constants* `ρ₁ = 4(a²+b²+1/3)/q_*²`, `ρ₂ = β₀(1+2(a²+b²))/4 + 4|ab|/q_*²`,
  `C₀ = (ρ₁+ρ₂)/(2κq_*)` (via `rr_sub_one_le`, `Bk_close`), stated for the closed forms of `A_k`, `B_k`
  (`A:1319-1322`).

## Not formalised

The quantum-`6j` variant of `(F3)` (`sinh/cosh` bounds, `σ = tanh²`); the *verification* part of (b), i.e.
the explicit `D` and the product bound, `(c)` and everything about `Θ`, `ξ` and Olver (the Airy limit for the closed-form
coefficients is `discrete_airy_hahn_racah` in `FormalResearch.Special.DiscreteAiryLimitHahn`, with its own obligations; the
identification of the closed forms with the actual integer-data `3j/6j` chains, `prop:hahn-class`, `prop:racah-class`, is
`hahn_class_chain`, `racah_class_chain` in `FormalResearch.Special.DiscreteAiryLimitChains{3j,6j}`); the Airy
input `|Ŷ_{k_1}| ≤ CN^{1/6}` (the normalisation `|Y_{k₁}| ≤ δ^{-p}` of `DiscreteAiryLimitHyperWindow`, or for the actual
chains the Gauss-weight bound of `DiscreteAiryLimitChains*`).
-/

@[expose] public section

namespace FormalResearch.Racah.P3

open Set

/-- **Backward ratio comparison** (`prop:forbidden-decay` (a),(b), proof in `A:1337-1349`): let
`A_{i+1} Y_{i+1} + A_i Y_{i-1} = c_i Y_i` for `j ≤ i ≤ N` (`1 ≤ j`), `A_i > 0` on `[j,N]`, `A_{N+1} = 0`
(hard edge: row `N` has no forward term) and `Y_N ≠ 0`.  If `y > 0` is a constant-ratio supersolution,
`A_{i+1} y + A_i/y ≤ c_i` on `[j,N]` (`eq:forbidden-const-ratio`), then for all `j-1 ≤ i ≤ N`:
`Y_i Y_N > 0` (all `Y_i` nonzero of the sign of `Y_N`) and, for `i < N`, `|Y_{i+1}| ≤ y |Y_i|`,
i.e. `0 < ρ_i = Y_{i+1}/Y_i ≤ y`.  For `y = 1` the supersolution condition is exactly the exact
hyperbolicity `A_i + A_{i+1} ≤ c_i` and this is `prop:forbidden-decay`(a), `|Ỹ_{i+1}| ≤ |Ỹ_i|`. -/
theorem backward_ratio (A c Y : ℕ → ℝ) (j N : ℕ) (y : ℝ) (hy : 0 < y) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hA : ∀ i, j ≤ i → i ≤ N → 0 < A i) (hend : A (N + 1) = 0)
    (hsup : ∀ i, j ≤ i → i ≤ N → A (i + 1) * y + A i / y ≤ c i)
    (hrow : ∀ i, j ≤ i → i ≤ N → A (i + 1) * Y (i + 1) + A i * Y (i - 1) = c i * Y i)
    (hYN : Y N ≠ 0) :
    ∀ i, j - 1 ≤ i → i ≤ N → 0 < Y i * Y N ∧ (i < N → |Y (i + 1)| ≤ y * |Y i|) := by
  have key : ∀ d, d + j ≤ N + 1 → ∀ i, N - d ≤ i → i ≤ N →
      0 < Y i * Y N ∧ (i < N → |Y (i + 1)| ≤ y * |Y i|) := by
    intro d
    induction d with
    | zero =>
      intro _ i h1 h2
      have : i = N := by omega
      subst this
      exact ⟨mul_self_pos.2 hYN, by intro h; omega⟩
    | succ d ih =>
      intro hd i h1 h2
      by_cases hi : N - d ≤ i
      · exact ih (by omega) i hi h2
      · -- i + 1 = N - d =: k is a row index
        have hk : i + 1 = N - d := by omega
        have hjk : j ≤ i + 1 := by omega
        have hkN : i + 1 ≤ N := by omega
        have IHk := ih (by omega) (i + 1) (by omega) hkN
        have hAk := hA (i + 1) hjk hkN
        have row := hrow (i + 1) hjk hkN
        simp only [Nat.add_sub_cancel] at row
        have hp : 0 < Y (i + 1) * Y N := IHk.1
        -- the forward term
        have hq : A (i + 1 + 1) * (Y (i + 1 + 1) * Y N) ≤ A (i + 1 + 1) * (y * (Y (i + 1) * Y N)) := by
          by_cases hN : i + 1 = N
          · rw [hN, hend]; simp
          · have hlt : i + 1 < N := by omega
            have IHk1 := ih (by omega) (i + 1 + 1) (by omega) (by omega)
            have hAk1 := hA (i + 1 + 1) (by omega) (by omega)
            have h3 := IHk.2 hlt
            have hq1 : 0 < Y (i + 1 + 1) * Y N := IHk1.1
            have e1 : Y (i + 1 + 1) * Y N = |Y (i + 1 + 1)| * |Y N| := by
              rw [← abs_mul, abs_of_pos hq1]
            have e2 : Y (i + 1) * Y N = |Y (i + 1)| * |Y N| := by
              rw [← abs_mul, abs_of_pos hp]
            have : Y (i + 1 + 1) * Y N ≤ y * (Y (i + 1) * Y N) := by
              rw [e1, e2]
              nlinarith [abs_nonneg (Y N), mul_le_mul_of_nonneg_right h3 (abs_nonneg (Y N))]
            exact mul_le_mul_of_nonneg_left this hAk1.le
        have hs := hsup (i + 1) hjk hkN
        have hmul : A (i + 1) * (Y i * Y N) = c (i + 1) * (Y (i + 1) * Y N) -
            A (i + 1 + 1) * (Y (i + 1 + 1) * Y N) := by
          have := congrArg (fun t => t * Y N) row
          linarith
        have hge : A (i + 1) * (Y i * Y N) ≥ A (i + 1) * ((Y (i + 1) * Y N) / y) := by
          have h4 : c (i + 1) * (Y (i + 1) * Y N) ≥
              (A (i + 1 + 1) * y + A (i + 1) / y) * (Y (i + 1) * Y N) :=
            mul_le_mul_of_nonneg_right hs hp.le
          have h5 : A (i + 1) * ((Y (i + 1) * Y N) / y) = A (i + 1) / y * (Y (i + 1) * Y N) := by
            ring
          rw [h5]
          nlinarith [hq, hmul, h4]
        have hge' : Y i * Y N ≥ (Y (i + 1) * Y N) / y := le_of_mul_le_mul_left hge hAk
        have hpos : 0 < Y i * Y N := lt_of_lt_of_le (div_pos hp hy) hge'
        refine ⟨hpos, ?_⟩
        intro _
        have e1 : Y (i + 1) * Y N = |Y (i + 1)| * |Y N| := by rw [← abs_mul, abs_of_pos hp]
        have e2 : Y i * Y N = |Y i| * |Y N| := by rw [← abs_mul, abs_of_pos hpos]
        rw [e1, e2] at hge'
        have hYN' : 0 < |Y N| := abs_pos.2 hYN
        rw [ge_iff_le, div_le_iff₀ hy] at hge'
        nlinarith
  intro i h1 h2
  exact key (N - (j - 1)) (by omega) i (by omega) h2

/-! ### The principal hopping `ẽ` and the slope bound (`(F1)`, `(F2)`, `eq:forbidden-slope`) -/

/-- `ẽ(σ) = √((1-σ/σ₁)(1-σ/σ₂))` of `A:1313`, written with `p = σ₁⁻¹ ≥ 0`, `q = σ₂⁻¹ ≥ 0` (so that
the Hahn case `σ₂ = ∞` is `q = 0`): `ẽ σ = √((1-pσ)(1-qσ))`. -/
noncomputable def etilde (p q σ : ℝ) : ℝ := Real.sqrt ((1 - p * σ) * (1 - q * σ))

/-- The domain `[0, σ_max]`, `σ_max = min(σ₁, σ₂)`: `σ ≥ 0`, `pσ ≤ 1`, `qσ ≤ 1`. -/
def Dom (p q : ℝ) : Set ℝ := {σ | 0 ≤ σ ∧ p * σ ≤ 1 ∧ q * σ ≤ 1}

lemma Dom_convex {p q : ℝ} : Convex ℝ (Dom p q) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  simp only [smul_eq_mul]
  refine ⟨by positivity, ?_, ?_⟩
  · nlinarith
  · nlinarith

lemma Dom_zero {p q : ℝ} : (0 : ℝ) ∈ Dom p q := by
  refine ⟨le_rfl, by simp, by simp⟩

lemma Dom_mono {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ∈ Dom p q) : s ∈ Dom p q :=
  ⟨hs, by nlinarith [ht.2.1], by nlinarith [ht.2.2]⟩

lemma etilde_zero (p q : ℝ) : etilde p q 0 = 1 := by simp [etilde]

lemma etilde_nonneg (p q σ : ℝ) : 0 ≤ etilde p q σ := Real.sqrt_nonneg _

/-- `(F1)`: `0 ≤ ẽ ≤ 1` on `[0, σ_max]`. -/
lemma etilde_le_one {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {σ : ℝ} (hσ : σ ∈ Dom p q) :
    etilde p q σ ≤ 1 := by
  unfold etilde
  rw [Real.sqrt_le_one]
  obtain ⟨h0, h1, h2⟩ := hσ
  have a1 : 0 ≤ 1 - p * σ := by linarith
  have a2 : 0 ≤ 1 - q * σ := by linarith
  have b1 : 1 - p * σ ≤ 1 := by nlinarith
  have b2 : 1 - q * σ ≤ 1 := by nlinarith
  nlinarith

/-- `(F1)`: `ẽ` is decreasing on `[0, σ_max]`. -/
lemma etilde_antitone {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {s t : ℝ} (hst : s ≤ t)
    (ht : t ∈ Dom p q) : etilde p q t ≤ etilde p q s := by
  unfold etilde
  apply Real.sqrt_le_sqrt
  obtain ⟨h0, h1, h2⟩ := ht
  have a1 : 0 ≤ 1 - p * t := by linarith
  have a2 : 0 ≤ 1 - q * t := by linarith
  have b1 : 1 - p * t ≤ 1 - p * s := by nlinarith
  have b2 : 1 - q * t ≤ 1 - q * s := by nlinarith
  nlinarith

/-- Two-point inequality for the geometric mean of two nonnegative affine functions. -/
lemma geomMean_two (f₁ g₁ f₂ g₂ a b : ℝ) (hf₁ : 0 ≤ f₁) (hg₁ : 0 ≤ g₁) (hf₂ : 0 ≤ f₂)
    (hg₂ : 0 ≤ g₂) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * Real.sqrt (f₁ * g₁) + b * Real.sqrt (f₂ * g₂) ≤
      Real.sqrt ((a * f₁ + b * f₂) * (a * g₁ + b * g₂)) := by
  set s₁ := Real.sqrt (f₁ * g₁) with hs₁
  set s₂ := Real.sqrt (f₂ * g₂) with hs₂
  have e₁ : s₁ ^ 2 = f₁ * g₁ := Real.sq_sqrt (by positivity)
  have e₂ : s₂ ^ 2 = f₂ * g₂ := Real.sq_sqrt (by positivity)
  have n₁ : 0 ≤ s₁ := Real.sqrt_nonneg _
  have n₂ : 0 ≤ s₂ := Real.sqrt_nonneg _
  have cross : s₁ * s₂ ≤ (f₁ * g₂ + f₂ * g₁) / 2 := by
    by_contra h
    push Not at h
    have hm : 0 ≤ (f₁ * g₂ + f₂ * g₁) / 2 := by positivity
    have : ((f₁ * g₂ + f₂ * g₁) / 2) ^ 2 < (s₁ * s₂) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (f₁ * g₂ - f₂ * g₁), mul_pow s₁ s₂ 2]
  have h : (a * s₁ + b * s₂) ^ 2 ≤ (a * f₁ + b * f₂) * (a * g₁ + b * g₂) := by
    have e : (a * s₁ + b * s₂) ^ 2 = a ^ 2 * s₁ ^ 2 + b ^ 2 * s₂ ^ 2 + 2 * a * b * (s₁ * s₂) := by
      ring
    rw [e, e₁, e₂]
    nlinarith [mul_le_mul_of_nonneg_left cross (mul_nonneg ha hb)]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

/-- **(F1)**: `ẽ` is concave on `[0, σ_max]` for all real `p, q` (the geometric mean of two nonnegative affine functions;
the paper's `ẽ'' = -(σ₁⁻¹-σ₂⁻¹)²/(4ẽ³) ≤ 0` is not needed). -/
theorem etilde_concaveOn {p q : ℝ} :
    ConcaveOn ℝ (Dom p q) (etilde p q) := by
  refine ⟨Dom_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul, etilde]
  have hb' : b = 1 - a := by linarith
  have := geomMean_two (1 - p * x) (1 - q * x) (1 - p * y) (1 - q * y) a b
    (by linarith [hx.2.1]) (by linarith [hx.2.2]) (by linarith [hy.2.1]) (by linarith [hy.2.2])
    ha hb
  have e1 : a * (1 - p * x) + b * (1 - p * y) = 1 - p * (a * x + b * y) := by
    rw [hb']; ring
  have e2 : a * (1 - q * x) + b * (1 - q * y) = 1 - q * (a * x + b * y) := by
    rw [hb']; ring
  rwa [e1, e2] at this

/-- The characteristic function of the forbidden-side comparison,
`Φ(σ) = τ(x - β₀σ) - ẽ(σ)` with `β₀ = √(pq) = (σ₁σ₂)^{-1/2}` (`A:1313`; `Φ = τ(x - Ψ_τ)` for `τ = ±1`). -/
noncomputable def Phi (p q τ x σ : ℝ) : ℝ := τ * (x - Real.sqrt (p * q) * σ) - etilde p q σ

/-- **`Φ` is convex on `[0, σ_max]`, for either sign `τ`.**  This replaces the paper's separate
statements "`Ψ_+` concave, `Ψ_-` convex" of `(F2)`: only the convexity of `-ẽ` is used. -/
theorem Phi_convexOn {p q : ℝ} (τ x : ℝ) :
    ConvexOn ℝ (Dom p q) (Phi p q τ x) := by
  refine ⟨Dom_convex, ?_⟩
  intro u hu v hv a b ha hb hab
  have hc := (etilde_concaveOn (p := p) (q := q)).2 hu hv ha hb hab
  simp only [smul_eq_mul, Phi] at hc ⊢
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith

/-- **`eq:forbidden-slope`** (integrated form): at a simple turn `Φ(σ_*) = 0`, `0 < σ_* ≤ σ ≤ σ_max`,
`Φ(σ) ≥ κ(σ - σ_*)` with `κ = (1 - τx)/σ_*`.  Needs only the convexity of `Φ`, `Φ(0) = -(1-τx)`
(`ẽ(0) = 1`) and the secant slope `κ` on `[0, σ_*]`; no differentiability.  (The paper's `Φ' ≥ κ` is the
derivative version of the same convexity statement.) -/
theorem forbidden_slope {p q : ℝ} (τ x : ℝ) {σs σ : ℝ} (hσs : 0 < σs)
    (hle : σs ≤ σ) (hσ : σ ∈ Dom p q) (hturn : Phi p q τ x σs = 0) :
    (1 - τ * x) / σs * (σ - σs) ≤ Phi p q τ x σ := by
  rcases eq_or_lt_of_le hle with h | h
  · subst h; rw [hturn]; simp
  · have hconv := Phi_convexOn (p := p) (q := q) τ x
    have := hconv.slope_mono_adjacent Dom_zero hσ hσs h
    have h0 : Phi p q τ x 0 = τ * x - 1 := by simp [Phi, etilde_zero]
    rw [hturn, h0] at this
    have e1 : (0 - (τ * x - 1)) / (σs - 0) = (1 - τ * x) / σs := by ring_nf
    rw [e1, le_div_iff₀ (sub_pos.2 h)] at this
    linarith

/-- `ẽ'(0) = -(σ₁⁻¹+σ₂⁻¹)/2`, so `Ψ_±'(0) = β₀ ∓ (σ₁⁻¹+σ₂⁻¹)/2` (`(F2)`). -/
theorem etilde_hasDerivAt_zero (p q : ℝ) : HasDerivAt (etilde p q) (-(p + q) / 2) 0 := by
  have h1 : HasDerivAt (fun σ : ℝ => 1 - p * σ) (-p) 0 := by
    simpa using (HasDerivAt.const_mul p (hasDerivAt_id (0 : ℝ))).const_sub 1
  have h2 : HasDerivAt (fun σ : ℝ => 1 - q * σ) (-q) 0 := by
    simpa using (HasDerivAt.const_mul q (hasDerivAt_id (0 : ℝ))).const_sub 1
  have h := HasDerivAt.mul h1 h2
  have := HasDerivAt.sqrt h (by simp)
  unfold etilde
  convert this using 1
  simp
  ring

/-- `Ψ_+'(0) = β₀ + ẽ'(0) = -½(√p - √q)² ≤ 0` for `β₀ = √(pq)` (`(F2)`, with `p = σ₁⁻¹`, `q = σ₂⁻¹`). -/
theorem Psi_plus_deriv_zero {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Real.sqrt (p * q) + (-(p + q) / 2) = -((Real.sqrt p - Real.sqrt q) ^ 2) / 2 := by
  have h1 : Real.sqrt (p * q) = Real.sqrt p * Real.sqrt q := Real.sqrt_mul hp q
  have h2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
  have h3 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  rw [h1]; nlinarith

/-- `(F2)`: `Ψ_+ = β₀σ + ẽ` is concave on `[0, σ_max]`. -/
theorem Psi_plus_concaveOn {p q : ℝ} :
    ConcaveOn ℝ (Dom p q) (fun σ => Real.sqrt (p * q) * σ + etilde p q σ) := by
  refine ⟨Dom_convex, ?_⟩
  intro u hu v hv a b ha hb hab
  have hc := (etilde_concaveOn (p := p) (q := q)).2 hu hv ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  nlinarith

/-- `(F2)`: `Ψ_- = β₀σ - ẽ` is convex on `[0, σ_max]`. -/
theorem Psi_minus_convexOn {p q : ℝ} :
    ConvexOn ℝ (Dom p q) (fun σ => Real.sqrt (p * q) * σ - etilde p q σ) := by
  refine ⟨Dom_convex, ?_⟩
  intro u hu v hv a b ha hb hab
  have hc := (etilde_concaveOn (p := p) (q := q)).2 hu hv ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  nlinarith

/-- `(F2)`: `Ψ_-` is increasing on `[0, σ_max]` (`β₀ ≥ 0`, `ẽ` decreasing). -/
theorem Psi_minus_monotoneOn {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    MonotoneOn (fun σ => Real.sqrt (p * q) * σ - etilde p q σ) (Dom p q) := by
  intro s hs t ht hst
  have := etilde_antitone hp hq hst ht
  have h0 : 0 ≤ Real.sqrt (p * q) := Real.sqrt_nonneg _
  simp only
  nlinarith

/-- **Skeleton of `prop:exact-hyperbolicity`** (proof, `A:1352-1353`; the logical core).
Let `σ, σ'` be the symbol values at two consecutive ranks, `σ̄ = (σ+σ')/2`, and suppose
`A ≤ ½(1+r₁) ẽ(σ)`, `A' ≤ ½(1+r₁) ẽ(σ')` (the `(F3)` bound `r_k ≤ 1 + ρ₁h²`, `r₁ = ρ₁h²`), a comparison
point `σ₀ ≤ σ̄` (`σ₀ = q_k²` for Hahn/Racah, `σ₀ = σ̄` for the quantum chain) with `|B - β₀σ₀| ≤ r₂`
(`r₂ = ρ₂h²`), a simple turn `Φ(σ_*) = 0` (`τ = ±1`), `σ_* ≤ σ₀` and `r₁ + r₂ ≤ κ(σ₀ - σ_*)`,
`κ = (1-τx)/σ_*`.  Then `A + A' ≤ τ(x - B)`. -/
theorem hyperbolic_of_slope {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (τ x σs σ₀ σ σ' r₁ r₂ A A' B : ℝ)
    (hτ : τ ^ 2 = 1) (hσ : σ ∈ Dom p q) (hσ' : σ' ∈ Dom p q) (hr₁ : 0 ≤ r₁)
    (hA : A ≤ (1 + r₁) / 2 * etilde p q σ) (hA' : A' ≤ (1 + r₁) / 2 * etilde p q σ')
    (hσ₀ : σ₀ ≤ (σ + σ') / 2) (hB : |B - Real.sqrt (p * q) * σ₀| ≤ r₂)
    (hs : 0 < σs) (hturn : Phi p q τ x σs = 0) (hσs : σs ≤ σ₀)
    (hgap : r₁ + r₂ ≤ (1 - τ * x) / σs * (σ₀ - σs)) :
    A + A' ≤ τ * (x - B) := by
  have hmid : (σ + σ') / 2 ∈ Dom p q := by
    have := Dom_convex hσ hσ' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simp only [smul_eq_mul] at this
    convert this using 1; ring
  have h0 : σ₀ ∈ Dom p q := Dom_mono hp hq (by linarith) hσ₀ hmid
  have hcc := (etilde_concaveOn (p := p) (q := q)).2 hσ hσ' (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have e : (1 / 2 : ℝ) • σ + (1 / 2 : ℝ) • σ' = (σ + σ') / 2 := by simp only [smul_eq_mul]; ring
  rw [e] at hcc
  simp only [smul_eq_mul] at hcc
  have h1 := etilde_le_one hp hq hmid
  have hanti := etilde_antitone hp hq hσ₀ hmid
  have hsl := forbidden_slope (p := p) (q := q) τ x hs hσs h0 hturn
  have hτ1 : |τ| = 1 := by
    have : |τ| ^ 2 = 1 := by rw [sq_abs]; exact hτ
    nlinarith [abs_nonneg τ]
  have hBt : τ * (B - Real.sqrt (p * q) * σ₀) ≤ r₂ := by
    calc τ * (B - Real.sqrt (p * q) * σ₀) ≤ |τ * (B - Real.sqrt (p * q) * σ₀)| := le_abs_self _
      _ = |B - Real.sqrt (p * q) * σ₀| := by rw [abs_mul, hτ1, one_mul]
      _ ≤ r₂ := hB
  unfold Phi at hsl
  nlinarith [mul_le_mul_of_nonneg_left hcc (by linarith : (0 : ℝ) ≤ 1 + r₁)]

/-- **Jensen step of the verification in `prop:forbidden-decay`(b)** (`A:1346`): with `A ≤ ½(1+r₁)ẽ(σ)`,
`A' ≤ ½(1+r₁)ẽ(σ')` for the hoppings `A = A_i`, `A' = A_{i+1}` and `y = e^{-ϑ} > 0`,
`F_i(y) = A' y + A/y ≤ (1+r₁) cosh ϑ · ẽ(σ̃)`, `σ̃ = λσ + (1-λ)σ'`, `λ = 1/(1+y²)`,
`cosh ϑ = (y + 1/y)/2`. -/
theorem F_le_cosh_etilde {p q : ℝ} (σ σ' r₁ A A' y : ℝ) (hy : 0 < y)
    (hσ : σ ∈ Dom p q) (hσ' : σ' ∈ Dom p q) (hr₁ : 0 ≤ r₁)
    (hA : A ≤ (1 + r₁) / 2 * etilde p q σ) (hA' : A' ≤ (1 + r₁) / 2 * etilde p q σ') :
    A' * y + A / y ≤ (1 + r₁) * ((y + 1 / y) / 2) *
      etilde p q ((1 / (1 + y ^ 2)) * σ + (y ^ 2 / (1 + y ^ 2)) * σ') := by
  have hl : 0 ≤ 1 / (1 + y ^ 2) := by positivity
  have hm : 0 ≤ y ^ 2 / (1 + y ^ 2) := by positivity
  have hsum : 1 / (1 + y ^ 2) + y ^ 2 / (1 + y ^ 2) = 1 := by field_simp
  have hcc := (etilde_concaveOn (p := p) (q := q)).2 hσ hσ' hl hm hsum
  simp only [smul_eq_mul] at hcc
  have hpos : 0 ≤ (1 + r₁) * ((y + 1 / y) / 2) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hcc hpos
  have e : (1 + r₁) * ((y + 1 / y) / 2) * (1 / (1 + y ^ 2) * etilde p q σ +
      y ^ 2 / (1 + y ^ 2) * etilde p q σ') =
      (1 + r₁) / 2 * (etilde p q σ / y + y * etilde p q σ') := by
    field_simp
    ring
  rw [e] at h1
  have h2 : A / y ≤ (1 + r₁) / 2 * etilde p q σ / y := div_le_div_of_nonneg_right hA hy.le
  have h3 : A' * y ≤ (1 + r₁) / 2 * etilde p q σ' * y := mul_le_mul_of_nonneg_right hA' hy.le
  have e2 : (1 + r₁) / 2 * (etilde p q σ / y + y * etilde p q σ') =
      (1 + r₁) / 2 * etilde p q σ / y + (1 + r₁) / 2 * etilde p q σ' * y := by ring
  rw [e2] at h1
  linarith

/-! ### The Hahn/Racah instance of `prop:exact-hyperbolicity`, with the explicit constants of `(F3)` -/

lemma sqrt_ratio_close {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |Real.sqrt ((1 - u) * (1 - v) / (1 - t / 4)) - 1| ≤ u + v + t / 3 := by
  have hd : 0 < 1 - t / 4 := by linarith
  set X := (1 - u) * (1 - v) / (1 - t / 4) with hX
  have hN0 : 0 ≤ (1 - u) * (1 - v) := mul_nonneg (by linarith) (by linarith)
  have hX0 : 0 ≤ X := div_nonneg hN0 hd.le
  have hup : X ≤ 1 + t / 3 := by
    rw [hX, div_le_iff₀ hd]
    nlinarith [mul_nonneg hu0 hv0, mul_nonneg ht0.le (sub_nonneg.2 ht1)]
  have hlo : 1 - u - v ≤ X := by
    rw [hX, le_div_iff₀ hd]
    nlinarith [mul_nonneg hu0 hv0, mul_nonneg hN0 ht0.le]
  have hs := Real.sq_sqrt hX0
  have hs0 := Real.sqrt_nonneg X
  have hXm : |X - 1| ≤ u + v + t / 3 := by
    rw [abs_le]; constructor <;> nlinarith
  have : |Real.sqrt X - 1| ≤ |X - 1| := by
    have e : X - 1 = (Real.sqrt X - 1) * (Real.sqrt X + 1) := by nlinarith
    rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.sqrt X + 1)]
    nlinarith [abs_nonneg (Real.sqrt X - 1)]
  linarith

/-- The rank factor `r_k = √((1-a²/k²)(1-b²/k²)/(1-1/(4k²)))` of `A:1319` (Hahn, Racah). -/
noncomputable def rr (a b k : ℝ) : ℝ :=
  Real.sqrt ((1 - a ^ 2 / k ^ 2) * (1 - b ^ 2 / k ^ 2) / (1 - 1 / (4 * k ^ 2)))

/-- **`(F3)`, Hahn/Racah rank factor**: for `k ≥ 1`, `a², b² ≤ k²`: `|r_k - 1| ≤ (a²+b²+1/3)/k²`
(this gives the paper's `ρ₁ = 4(a²+b²+1/3)/q_*²`, since `1/k² ≤ 4h²/q_*²` for `k ≥ q_*N/2`). -/
theorem rr_sub_one_le {a b k : ℝ} (hk : 1 ≤ k) (ha : a ^ 2 ≤ k ^ 2) (hb : b ^ 2 ≤ k ^ 2) :
    |rr a b k - 1| ≤ (a ^ 2 + b ^ 2 + 1 / 3) / k ^ 2 := by
  have hk2 : 0 < k ^ 2 := by positivity
  have h := sqrt_ratio_close (u := a ^ 2 / k ^ 2) (v := b ^ 2 / k ^ 2) (t := 1 / k ^ 2)
    (by positivity) ((div_le_one hk2).2 ha) (by positivity) ((div_le_one hk2).2 hb)
    (by positivity) ((div_le_one hk2).2 (by nlinarith))
  have e1 : 1 - 1 / (4 * k ^ 2) = 1 - 1 / k ^ 2 / 4 := by field_simp
  unfold rr
  rw [e1]
  convert h using 1
  field_simp

/-- **`(F3)`, Hahn/Racah diagonal**: with `B_k - β₀q_k² = β₀h²(1/4 - (a²+b²)/2) + ab/(k(k+1))` and
`k ≥ q_*/(2h)` (`q_* > 0`, `h > 0`, `β₀ ≥ 0`), `|B_k - β₀q_k²| ≤ ρ₂h²` with the paper's
`ρ₂ = β₀(1+2(a²+b²))/4 + 4|ab|/q_*²`. -/
theorem Bk_close {β₀ a b h k qs : ℝ} (hβ : 0 ≤ β₀) (hh : 0 < h) (hqs : 0 < qs) (hk : 1 ≤ k)
    (hkq : qs ≤ 2 * k * h) :
    |β₀ * h ^ 2 * (1 / 4 - (a ^ 2 + b ^ 2) / 2) + a * b / (k * (k + 1))| ≤
      (β₀ * (1 + 2 * (a ^ 2 + b ^ 2)) / 4 + 4 * |a * b| / qs ^ 2) * h ^ 2 := by
  have h1 : |β₀ * h ^ 2 * (1 / 4 - (a ^ 2 + b ^ 2) / 2)| ≤ β₀ * (1 + 2 * (a ^ 2 + b ^ 2)) / 4 * h ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ β₀ * h ^ 2)]
    have : |1 / 4 - (a ^ 2 + b ^ 2) / 2| ≤ (1 + 2 * (a ^ 2 + b ^ 2)) / 4 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
    calc β₀ * h ^ 2 * |1 / 4 - (a ^ 2 + b ^ 2) / 2|
        ≤ β₀ * h ^ 2 * ((1 + 2 * (a ^ 2 + b ^ 2)) / 4) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = β₀ * (1 + 2 * (a ^ 2 + b ^ 2)) / 4 * h ^ 2 := by ring
  have hk0 : 0 < k := by linarith
  have h2 : |a * b / (k * (k + 1))| ≤ 4 * |a * b| / qs ^ 2 * h ^ 2 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < k * (k + 1))]
    have hq2 : qs ^ 2 ≤ 4 * k ^ 2 * h ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    have : 4 * |a * b| / qs ^ 2 * h ^ 2 * (k * (k + 1)) ≥ |a * b| := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ (by positivity)]
      nlinarith [abs_nonneg (a * b), mul_nonneg (abs_nonneg (a * b)) (by positivity : 0 ≤ h ^ 2 * k)]
    exact this
  calc _ ≤ |β₀ * h ^ 2 * (1 / 4 - (a ^ 2 + b ^ 2) / 2)| + |a * b / (k * (k + 1))| := abs_add_le _ _
    _ ≤ _ := by nlinarith

lemma two_mul_le_sq_sub (s Q : ℝ) : 2 * s * (Q - s) ≤ Q ^ 2 - s ^ 2 := by
  nlinarith [sq_nonneg (Q - s)]

/-- The diagonal coefficient `B_k = β₀ σ̄_k - β₀h²(a²+b²)/2 + ab/(k(k+1))`, `σ̄_k = q_k² + h²/4`,
`q_k = (k+1/2)h` of `A:1321` (Hahn, Racah). -/
noncomputable def hrB (β₀ a b h k : ℝ) : ℝ :=
  β₀ * (((k + 1 / 2) * h) ^ 2 + h ^ 2 / 4) - β₀ * h ^ 2 * (a ^ 2 + b ^ 2) / 2 + a * b / (k * (k + 1))

/-- **`prop:exact-hyperbolicity` for the Hahn and centered Racah chains, with the paper's constants**
(`A:1352-1353`): `A_j = ½ r_j ẽ(σ_j)`, `σ_j = (jh)²`, `B_k = hrB`; `p = σ₁⁻¹`, `q = σ₂⁻¹`
(`(p,q) = (1,0)` Hahn, `(1/(4α²), 1/(4β²))` Racah, `β₀ = √(pq)`).  For a simple turn `Φ(q_*²) = 0`
(`τ = ±1`, `1 - τx > 0`) and a rank `k ≥ max(1, |a|, |b|, q_*/(2h))` with `σ_{k+1} ≤ σ_max`,
`A_k + A_{k+1} ≤ τ(x - B_k)` as soon as `(ρ₁ + ρ₂)h² ≤ 2κq_*(q_k - q_*)`, i.e. `q_k - q_* ≥ C₀h²`,
`C₀ = (ρ₁+ρ₂)/(2κ q_*)`, `κ = (1-τx)/q_*²`, `ρ₁ = 4(a²+b²+1/3)/q_*²`,
`ρ₂ = β₀(1+2(a²+b²))/4 + 4|ab|/q_*²`.  Not formalised: the quantum-`6j` variant (`sinh`/`cosh` bounds
and the unimodality of `σ = tanh²`), the passage from the closed forms of `A_k`, `B_k` to the chains
themselves (`prop:hahn-class`, `prop:racah-class`; now `hahn_class_chain`, `racah_class_chain` in
`FormalResearch.Special.DiscreteAiryLimitChains{3j,6j}`, integer data), and `A_{k_max+1} = 0` (here `σ_{k+1}` in the domain
suffices: at the hard edge `ẽ(σ_max) = 0`). -/
theorem exact_hyperbolicity_hahn_racah {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (a b τ x qs h k : ℝ) (hh : 0 < h) (hqs : 0 < qs) (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x)
    (hturn : Phi p q τ x (qs ^ 2) = 0) (hk : 1 ≤ k) (hka : a ^ 2 ≤ k ^ 2) (hkb : b ^ 2 ≤ k ^ 2)
    (hkq : qs ≤ 2 * k * h) (hD : ((k + 1) * h) ^ 2 ∈ Dom p q)
    (hgap : (4 * (a ^ 2 + b ^ 2 + 1 / 3) / qs ^ 2 +
        (Real.sqrt (p * q) * (1 + 2 * (a ^ 2 + b ^ 2)) / 4 + 4 * |a * b| / qs ^ 2)) * h ^ 2 ≤
      2 * ((1 - τ * x) / qs ^ 2) * qs * ((k + 1 / 2) * h - qs)) :
    1 / 2 * rr a b k * etilde p q ((k * h) ^ 2) +
        1 / 2 * rr a b (k + 1) * etilde p q (((k + 1) * h) ^ 2) ≤
      τ * (x - hrB (Real.sqrt (p * q)) a b h k) := by
  set β₀ := Real.sqrt (p * q) with hβ₀
  have hβ : 0 ≤ β₀ := Real.sqrt_nonneg _
  set ρ₁ := 4 * (a ^ 2 + b ^ 2 + 1 / 3) / qs ^ 2 with hρ₁
  set ρ₂ := β₀ * (1 + 2 * (a ^ 2 + b ^ 2)) / 4 + 4 * |a * b| / qs ^ 2 with hρ₂
  have hk0 : 0 < k := by linarith
  have hρ₁0 : 0 ≤ ρ₁ := by positivity
  have hρ₂0 : 0 ≤ ρ₂ := by positivity
  have hkh : 0 ≤ k * h := by positivity
  have hσ' := hD
  have hσ : (k * h) ^ 2 ∈ Dom p q :=
    Dom_mono hp hq (by positivity) (by nlinarith) hD
  -- the rank factors
  have hq2 : qs ^ 2 ≤ 4 * k ^ 2 * h ^ 2 := by nlinarith
  have rk : ∀ j : ℝ, k ≤ j → rr a b j ≤ 1 + ρ₁ * h ^ 2 := by
    intro j hj
    have hj1 : 1 ≤ j := by linarith
    have h1 := rr_sub_one_le (a := a) (b := b) hj1 (by nlinarith) (by nlinarith)
    have h2 : (a ^ 2 + b ^ 2 + 1 / 3) / j ^ 2 ≤ ρ₁ * h ^ 2 := by
      rw [hρ₁, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hj2 : k ^ 2 ≤ j ^ 2 := by nlinarith
      have : qs ^ 2 ≤ 4 * j ^ 2 * h ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hj2 (sq_nonneg h)]
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ a ^ 2 + b ^ 2 + 1 / 3)]
    have := (abs_le.1 h1).2
    linarith
  have hA : 1 / 2 * rr a b k * etilde p q ((k * h) ^ 2) ≤
      (1 + ρ₁ * h ^ 2) / 2 * etilde p q ((k * h) ^ 2) := by
    have := mul_le_mul_of_nonneg_right (rk k le_rfl) (etilde_nonneg p q ((k * h) ^ 2))
    linarith
  have hA' : 1 / 2 * rr a b (k + 1) * etilde p q (((k + 1) * h) ^ 2) ≤
      (1 + ρ₁ * h ^ 2) / 2 * etilde p q (((k + 1) * h) ^ 2) := by
    have := mul_le_mul_of_nonneg_right (rk (k + 1) (by linarith))
      (etilde_nonneg p q (((k + 1) * h) ^ 2))
    linarith
  -- the diagonal
  have hB : |hrB β₀ a b h k - β₀ * (((k + 1 / 2) * h) ^ 2)| ≤ ρ₂ * h ^ 2 := by
    have := Bk_close (β₀ := β₀) (a := a) (b := b) hβ hh hqs hk hkq
    have e : hrB β₀ a b h k - β₀ * (((k + 1 / 2) * h) ^ 2) =
        β₀ * h ^ 2 * (1 / 4 - (a ^ 2 + b ^ 2) / 2) + a * b / (k * (k + 1)) := by
      unfold hrB; ring
    rw [e]; exact this
  -- gap conditions
  have hqk : qs ≤ (k + 1 / 2) * h := by
    by_contra hlt
    push Not at hlt
    have : 2 * ((1 - τ * x) / qs ^ 2) * qs * ((k + 1 / 2) * h - qs) < 0 := by
      have : (k + 1 / 2) * h - qs < 0 := by linarith
      have hpos : 0 < 2 * ((1 - τ * x) / qs ^ 2) * qs := by positivity
      exact mul_neg_of_pos_of_neg hpos this
    have h0 : 0 ≤ (ρ₁ + ρ₂) * h ^ 2 := by positivity
    linarith
  have hsq : qs ^ 2 ≤ ((k + 1 / 2) * h) ^ 2 := pow_le_pow_left₀ hqs.le hqk 2
  have hgap' : ρ₁ * h ^ 2 + ρ₂ * h ^ 2 ≤ (1 - τ * x) / qs ^ 2 * (((k + 1 / 2) * h) ^ 2 - qs ^ 2) := by
    have hκ' : 0 < (1 - τ * x) / qs ^ 2 := by positivity
    have : 2 * qs * ((k + 1 / 2) * h - qs) ≤ ((k + 1 / 2) * h) ^ 2 - qs ^ 2 :=
      two_mul_le_sq_sub qs ((k + 1 / 2) * h)
    calc ρ₁ * h ^ 2 + ρ₂ * h ^ 2 = (ρ₁ + ρ₂) * h ^ 2 := by ring
      _ ≤ 2 * ((1 - τ * x) / qs ^ 2) * qs * ((k + 1 / 2) * h - qs) := hgap
      _ = (1 - τ * x) / qs ^ 2 * (2 * qs * ((k + 1 / 2) * h - qs)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hκ'.le
  have hσ₀ : ((k + 1 / 2) * h) ^ 2 ≤ ((k * h) ^ 2 + ((k + 1) * h) ^ 2) / 2 := by
    have e : ((k * h) ^ 2 + ((k + 1) * h) ^ 2) / 2 - ((k + 1 / 2) * h) ^ 2 = h ^ 2 / 4 := by ring
    linarith [sq_nonneg h]
  have hr1 : 0 ≤ ρ₁ * h ^ 2 := by positivity
  have hr1' : 0 < qs ^ 2 := by positivity
  exact hyperbolic_of_slope (p := p) (q := q) hp hq τ x (qs ^ 2) (((k + 1 / 2) * h) ^ 2)
    ((k * h) ^ 2) (((k + 1) * h) ^ 2) (ρ₁ * h ^ 2) (ρ₂ * h ^ 2)
    (1 / 2 * rr a b k * etilde p q ((k * h) ^ 2))
    (1 / 2 * rr a b (k + 1) * etilde p q (((k + 1) * h) ^ 2))
    (hrB β₀ a b h k) hτ hσ hσ' hr1 hA hA' hσ₀ hB hr1' hturn hsq hgap'

/-- info: 'FormalResearch.Racah.P3.backward_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms backward_ratio

/-- info: 'FormalResearch.Racah.P3.etilde_concaveOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms etilde_concaveOn

/-- info: 'FormalResearch.Racah.P3.forbidden_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forbidden_slope

/-- info: 'FormalResearch.Racah.P3.hyperbolic_of_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hyperbolic_of_slope

/-- info: 'FormalResearch.Racah.P3.exact_hyperbolicity_hahn_racah' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exact_hyperbolicity_hahn_racah

/-- info: 'FormalResearch.Racah.P3.F_le_cosh_etilde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms F_le_cosh_etilde

end FormalResearch.Racah.P3
