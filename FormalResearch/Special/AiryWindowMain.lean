module

public import FormalResearch.Special.AiryWindow

/-!
# The discrete Airy window: exact solution comparison down to `X = -A₀`

Plan M6 of the discrete-to-Airy programme, output theorems.  Source: P3 `thm:general-rank-airy` /
`lem:airy2-recessive` (appendices `A:1105-1183`), W1 `app:airy` (`est:255-345`, the column form `eq:airyfactor`
on bounded windows) and `EC:95-113`; the replacement of the cited external theorem (GBVA/Geronimo 2009, Thm 2.6) by
`recessive_airy` (forbidden side, `X ≥ -1`) + the Grönwall march of `AiryWindow` (oscillatory side, `X ∈ [-A₀, -1]`).

**Setting.**  Sites `J ≤ m ≤ N`, `δ = h^{1/3}`.  Top window `Icc m (N+1)`: an `AiryLattice` (`X ≥ -1`, gaps `≥ c₁ δ`,
`X ≤ B δ⁻²`), the parametrix `ψ` is comparable with `airyWt` there (`κ₁ airyWt ≤ ψ ≤ κ₂ airyWt`, i.e. `ψ = g Ai`,
`g ≍ 1`) and satisfies the relative defect `|jac a c ψ_i| ≤ C₀ δ⁶ ψ_i` (`hdef` of `recessive_airy`).  Oscillatory
window `Icc J m`: gaps `≥ c₁ δ`, `X_J ≥ -A₀`, `X_m ≤ Z` (so `S = A₀ + Z`); **no positivity of `ψ` is assumed there**;
the defect is *absolute*, `|jac a c ψ_i| ≤ C₀ δ⁶ W` with `W` a bound for `sup |ψ|` over the window (in the Airy lane
`W ≍ sup (1+|X|)^{-1/4} ≲ 1`); the coefficients are near-hyperbolic there (`|c_k - a_k - a_{k+1}| ≤ Sg δ²`,
`|a_{k+1} - a_k| ≤ Qq δ²`, `a ≥ c_a`).

Statements (all **proved**, explicit constants):

* `window_len`: `(m - J) δ ≤ S/c₁`;
* `window_hyperbolic_constants` (hypothesis step (1)): from Lipschitz coefficient data (`c - 2a` Lipschitz in the
  position `s` and vanishing at the turn `s*`; `a` Lipschitz; `|s_k - s*| ≤ C_z δ² |X_k|` from the Langer coordinate) the
  near-hyperbolic hypotheses hold with `Sg = L_F C_z A + C_a`, `Qq = L_a C_s` (`A ≥ |X|` on the window);
* **`discrete_airy_window`**: for fixed constants there are `δ₀, C` such that for `δ ≤ δ₀` the exact solution `f` of
  `jac a c f = 0` on the rows `Icc (J+1) N` with `f = ψ` at `N, N+1` satisfies `|f_k - ψ_k| ≤ C δ³ ψ_k` on the top
  window and **`|f_k - ψ_k| ≤ C δ³ W` on the oscillatory window `X_k ∈ [-A₀, Z]`**, `δ³ = h`;
* **`discrete_airy_window_physical`**: every exact solution `Y` of the rows `Icc (J+1) N` with `|Y_N|, |Y_{N+1}| ≤ Y_max`
  is `κ F + μ F₂` on `Icc J (N+1)` (`F` the continuation of `f`, `F₂` that of the reduction-of-order solution
  `f₂ = secondSol a f m`, `μ` exponentially small, `|μ| ≤ 3 κ₂ a_{N+1} Y_max e^{-ξ(X_N)}`) and
  `|Y_k - κ ψ_k| ≤ C δ³ |κ| W + C' |μ| δ⁻¹` on the oscillatory window, `|Y_k - κ ψ_k| ≤ C δ³ |κ| ψ_k + C₂ |μ| δ⁻¹/airyWt(X_k)`
  on the top window.  With `|μ| ≤ δ⁴ |κ|` the `μ`-terms are `≤ |κ| δ³` (the paper's "`|μ f₂|` negligible").

The scalar `κ` is **not** determined here (it needs the Darboux/Wigner-`d` bulk matching; plan §0.3).

**Hypotheses that are supplied elsewhere (precise gaps).**
1. The defect `hdef` on the top window (`ψ = g Ai`, `X ≥ -1`) is the parametrix module `M4` (`AiryParametrix*`).  On the
   oscillatory window the defect `|jac a c ψ| ≤ C₀ δ⁶ W` is *not* a consequence of M2's Taylor lemmas as stated:
   `airy_taylor4/5` (`AiryShiftTaylor`) cover base points `X ≥ -1` only (they use the envelope `airyAi_envelope_real`).
   The underlying `airy_sol_taylor4/5` are valid for all `X` given a sup bound `B` of the jet on the segment, and for
   `X ∈ [-A₀,-1]`, `|s| ≤ 1` the segment lies in `(-∞, 0]`, where `abs_airyAi_le_of_nonpos`, `abs_airyAi'_le_of_nonpos`
   (`AiryKernelOpSharp`) give `|Ai| ≤ 3`, `|Ai'| ≤ 3 (1+A₀)^{1/4}`; so the window version of the Taylor remainder is
   available with `K = K(A₀)` polynomial in `A₀` (`airy_taylor4_window`, `airy_taylor5_window` of `AiryWindowTaylor`, **proved**), and the remaining work in M4 is the bookkeeping of the
   coefficient jets (`g, ζ, a, c` are smooth across the turn: M3).
2. `|ψ_m - ψ_{m+1}| ≤ Λ δ W` (a Lipschitz bound at the junction, true for `ψ = g Ai` at bounded `X`) and `ψ_m ≤ W`.
3. The near-hyperbolic constants `Sg, Qq` for the actual chains (Hahn/Racah, W1 class) via `window_hyperbolic_constants`.

**Not formalised:** the parametrix defect hypotheses themselves (`hdef`, `hdefW`: module `M4`), `ψ ≍ airyWt` for `g Ai`,
the value of `κ` (Darboux matching), `Sg, Qq` for the concrete Hahn/Racah/W1 chains (only the reduction
`window_hyperbolic_constants`), the oscillatory side beyond a bounded window (full GBVA with `M/E` weights), and a
Grönwall norm adapted to the amplitude `|X|^{-1/4}` (would give power instead of `e^{O(A₀²)}` growth).

**Numerics** (see `AiryWindow`; scripts in `/home/user/scratch/m6_numerics/`): model chain, actual `|f-ψ| ≈ 0.0163 h^{4/3}` on `X ∈ [-10,-1]`, independent of `A₀`;
the proved constant `windowConst` is `e^{O(A₀²)}` (pessimistic) times `O(h)` (not sharp).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `(m - J) δ ≤ S / c₁` from the gaps and `X_m - X_J ≤ S`. -/
lemma window_len {X : ℤ → ℝ} {J m : ℤ} {c1 δ S : ℝ} (hc1 : 0 < c1) (hJm : J ≤ m)
    (hgap : ∀ k ∈ Ico J m, c1 * δ ≤ X (k + 1) - X k) (hS : X m - X J ≤ S) :
    ((m - J : ℤ) : ℝ) * δ ≤ S / c1 := by
  have h := window_count hJm hgap
  rw [le_div_iff₀ hc1]
  calc ((m - J : ℤ) : ℝ) * δ * c1 = ((m - J : ℤ) : ℝ) * (c1 * δ) := by ring
    _ ≤ S := h.trans hS

/-- **Step (1): the near-hyperbolic constants from smooth coefficient data** (`P3` `A:870-880`: `A_k = a₀(s) + O(h²)`,
`c = E - b` smooth; W1 `est:266-270`).  Let `s_k` be the positions of the sites, `s*` the turn, `F = c - 2a` the
hyperbolicity defect.  If `|c_k - a_k - a_{k+1}| ≤ L_F |s_k - s*| + C_a δ⁶` (`F` is `L_F`-Lipschitz and vanishes at `s*`;
`a_k + a_{k+1} - 2 a(s_k) = O(h²)` by the midpoint convention, `δ⁶ = h²`), `|s_k - s*| ≤ C_z δ² A` (Langer: `s - s*` is
comparable with `h^{2/3} X`, `δ² = h^{2/3}`; `A ≥ |X_k|`) and `|a_{k+1} - a_k| ≤ L_a |s_{k+1} - s_k| ≤ L_a C_s δ³`
(`L_a` the Lipschitz constant of `a`, `C_s` the maximal spacing in units of `h`), then the hypotheses of the Grönwall
window hold with `Sg = L_F C_z A + C_a`, `Qq = L_a C_s`. -/
theorem window_hyperbolic_constants {s a c : ℤ → ℝ} {J m : ℤ} {δ sStar LF Ca La Cz Cs A : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hLF : 0 ≤ LF) (hCa : 0 ≤ Ca) (hLa : 0 ≤ La) (hCs : 0 ≤ Cs)
    (hc : ∀ k ∈ Ioc J m, |c k - a k - a (k + 1)| ≤ LF * |s k - sStar| + Ca * δ ^ 6)
    (hs : ∀ k ∈ Ioc J m, |s k - sStar| ≤ Cz * δ ^ 2 * A)
    (ha : ∀ k ∈ Ioc J m, |a (k + 1) - a k| ≤ La * |s (k + 1) - s k|)
    (hss : ∀ k ∈ Ioc J m, |s (k + 1) - s k| ≤ Cs * δ ^ 3) :
    (∀ k ∈ Ioc J m, |c k - a k - a (k + 1)| ≤ (LF * Cz * A + Ca) * δ ^ 2) ∧
      (∀ k ∈ Ioc J m, |a (k + 1) - a k| ≤ (La * Cs) * δ ^ 2) := by
  have hδ2 : δ ^ 3 ≤ δ ^ 2 := by nlinarith [pow_pos hδ 2]
  have hδ6 : δ ^ 6 ≤ δ ^ 2 := by
    have : δ ^ 6 ≤ δ ^ 3 := by nlinarith [pow_pos hδ 3, pow_pos hδ 4, pow_pos hδ 5]
    linarith
  constructor
  · intro k hk
    have h1 := hc k hk
    have h2 := mul_le_mul_of_nonneg_left (hs k hk) hLF
    have h3 : Ca * δ ^ 6 ≤ Ca * δ ^ 2 := mul_le_mul_of_nonneg_left hδ6 hCa
    nlinarith
  · intro k hk
    have h1 := (ha k hk).trans (mul_le_mul_of_nonneg_left (hss k hk) hLa)
    have h2 : La * (Cs * δ ^ 3) ≤ La * (Cs * δ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ2 hCs) hLa
    nlinarith

/-- Positivity and size of the window constant. -/
lemma windowConst_ge {c1 ca C0 C5 Λ Sg Qq S : ℝ} (hc1 : 0 < c1) (hca : 0 < ca) (hC0 : 0 ≤ C0) (hC5 : 0 < C5)
    (hΛ : 0 ≤ Λ) (hSg : 0 ≤ Sg) (hQq : 0 ≤ Qq) (hS : 0 ≤ S) :
    C5 ≤ windowConst c1 ca C0 C5 Λ Sg Qq S ∧ 0 < windowConst c1 ca C0 C5 Λ Sg Qq S := by
  have h1 := windowExp_ge_one hc1 hca hSg hQq hS
  unfold windowConst
  have h2 : 0 ≤ 2 * S * C0 / (c1 * ca) := by positivity
  have h3 : 2 * C5 ≤ C5 * (2 + Λ) + 2 * S * C0 / (c1 * ca) := by nlinarith
  constructor
  · nlinarith
  · have : 0 < C5 * (2 + Λ) + 2 * S * C0 / (c1 * ca) := by nlinarith
    positivity

/-- **`discrete_airy_window`** (P3 `thm:general-rank-airy` (i) / `lem:airy2-recessive` + oscillatory window; W1 column
form on `X ≥ -A₀`, up to the normalisation `κ`).  See the module docstring for the setting and constants.
For fixed `(c₁, B, c_a, κ₁, κ₂, C₀, Λ, S, Sg, Qq)` there are `δ₀, C > 0` such that for `δ ≤ δ₀` and all data satisfying
the hypotheses there is an exact solution `f` of the rows `Icc (J+1) N` with `f = ψ` at `N, N+1`,
`|f_k - ψ_k| ≤ C δ³ ψ_k` on `Icc m (N+1)` (`δ³ = h`) and `|f_k - ψ_k| ≤ C δ³ W` on `Icc J m`. -/
theorem discrete_airy_window (c1 B ca κ1 κ2 C0 Λ S Sg Qq : ℝ) (hc1 : 0 < c1) (hca : 0 < ca) (hC0 : 0 ≤ C0)
    (hΛ : 0 ≤ Λ) (hS : 0 ≤ S) (hSg : 0 ≤ Sg) (hQq : 0 ≤ Qq) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (X ψ a c : ℤ → ℝ) (J m N : ℤ) (δ W : ℝ), J ≤ m → m ≤ N → δ ≤ δ0 →
        AiryLattice X m N c1 B δ → AiryComparison ψ X m N κ1 κ2 →
        (∀ k ∈ Ico J m, c1 * δ ≤ X (k + 1) - X k) → X m - X J ≤ S →
        (∀ k ∈ Icc (J + 1) (N + 1), ca ≤ a k) →
        (∀ k ∈ Ioc J m, |c k - a k - a (k + 1)| ≤ Sg * δ ^ 2) →
        (∀ k ∈ Ioc J m, |a (k + 1) - a k| ≤ Qq * δ ^ 2) →
        (∀ i ∈ Icc (m + 1) N, |jac a c ψ i| ≤ C0 * δ ^ 6 * ψ i) →
        (∀ i ∈ Ioc J m, |jac a c ψ i| ≤ C0 * δ ^ 6 * W) →
        ψ m ≤ W → |ψ m - ψ (m + 1)| ≤ Λ * δ * W →
        ∃ f : ℤ → ℝ, (∀ k ∈ Icc (J + 1) N, jac a c f k = 0) ∧ f N = ψ N ∧ f (N + 1) = ψ (N + 1) ∧
          (∀ k ∈ Icc m (N + 1), |f k - ψ k| ≤ C * δ ^ 3 * ψ k) ∧
          (∀ k ∈ Icc J m, |f k - ψ k| ≤ C * δ ^ 3 * W) := by
  obtain ⟨δ0, hδ0, C5, hC5, H⟩ := recessive_airy c1 B ca κ1 κ2 C0 hca hC0
  obtain ⟨hCge, hCpos⟩ := windowConst_ge hc1 hca hC0 hC5 hΛ hSg hQq hS
  refine ⟨δ0, hδ0, windowConst c1 ca C0 C5 Λ Sg Qq S, hCpos, ?_⟩
  intro X ψ a c J m N δ W hJm hmN hδ hL hψ hgap hXS ha hc ha' hdefT hdefW hψW hLip
  have hmem : m ∈ Icc m (N + 1) := by rw [mem_Icc]; omega
  have hmem1 : m + 1 ∈ Icc m (N + 1) := by rw [mem_Icc]; omega
  have hmN' : m ∈ Icc m N := by rw [mem_Icc]; omega
  obtain ⟨f0, hrow, hfN, hfN1, hf1, -, hf3⟩ := H X ψ a c m N δ hmN hδ hL hψ
    (fun k hk => ha k (by rw [mem_Icc] at hk ⊢; omega)) hdefT
  have hnδ := window_len hc1 hJm hgap hXS
  obtain ⟨F, hF, hFf, hFw⟩ := window_from_top (J := J) (m := m) (N := N) (δ := δ) (W := W) (c1 := c1)
    (ca := ca) (C0 := C0) (C5 := C5) (Λ := Λ) (Sg := Sg) (Qq := Qq) (S := S) hL.δ_pos hL.δ_le_one hc1 hca hC0
    hC5.le hΛ hSg hQq hS hJm hmN hnδ ha hc ha' hdefW hrow (hf1 m hmem) (hf3 m hmN') (hψ.pos hmem).le hψW hLip
  refine ⟨F, hF, ?_, ?_, ?_, hFw⟩
  · rw [hFf N (by rw [mem_Icc]; omega), hfN]
  · rw [hFf (N + 1) (by rw [mem_Icc]; omega), hfN1]
  · intro k hk
    rw [hFf k hk]
    refine (hf1 k hk).trans ?_
    have := (hψ.pos hk).le
    have h3 : 0 ≤ δ ^ 3 := by have := hL.δ_pos; positivity
    nlinarith [mul_nonneg h3 this]

/-- info: 'FormalResearch.Special.window_hyperbolic_constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.window_hyperbolic_constants

/-- info: 'FormalResearch.Special.discrete_airy_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.discrete_airy_window

/-- **`discrete_airy_window_physical`**: the version for the physical solution.  As `discrete_airy_window`, with in addition
a lower bound `w₀ ≤ ψ_m` (`ψ_m ≍ Ai(-1) g ≍ 1`) and an arbitrary exact solution `Y` of the rows `Icc (J+1) N` (the
physical solution, extended to the window) with `|Y_N|, |Y_{N+1}| ≤ Y_max`.  Then `Y = κ F + μ F₂` on `Icc J (N+1)`, with
`F` the exact recessive solution continued to the window and `F₂` the continuation of its reduction-of-order partner
`f₂ = secondSol a f m`, `μ` exponentially small (`|μ| ≤ 3 κ₂ a_{N+1} Y_max e^{-ξ(X_N)}`), and:
`|Y_k - κ ψ_k| ≤ C δ³ |κ| W + (2/(c_a w₀)) windowExp · |μ| δ⁻¹` on `Icc J m` (oscillatory window),
`|Y_k - κ ψ_k| ≤ C δ³ |κ| ψ_k + C₂ |μ| δ⁻¹ / airyWt(X_k)` on `Icc m (N+1)` (`C₂ = secondConst`).
The remaining hypotheses are those of `discrete_airy_window`; the scalar `κ` is not determined. -/
theorem discrete_airy_window_physical (c1 B ca κ1 κ2 C0 Λ S Sg Qq w0 : ℝ) (hc1 : 0 < c1) (hca : 0 < ca)
    (hC0 : 0 ≤ C0) (hΛ : 0 ≤ Λ) (hS : 0 ≤ S) (hSg : 0 ≤ Sg) (hQq : 0 ≤ Qq) (hw0 : 0 < w0) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (X ψ a c Y : ℤ → ℝ) (J m N : ℤ) (δ W Ymax : ℝ), J ≤ m → m ≤ N → δ ≤ δ0 →
        AiryLattice X m N c1 B δ → AiryComparison ψ X m N κ1 κ2 →
        (∀ k ∈ Ico J m, c1 * δ ≤ X (k + 1) - X k) → X m - X J ≤ S →
        (∀ k ∈ Icc (J + 1) (N + 1), ca ≤ a k) →
        (∀ k ∈ Ioc J m, |c k - a k - a (k + 1)| ≤ Sg * δ ^ 2) →
        (∀ k ∈ Ioc J m, |a (k + 1) - a k| ≤ Qq * δ ^ 2) →
        (∀ i ∈ Icc (m + 1) N, |jac a c ψ i| ≤ C0 * δ ^ 6 * ψ i) →
        (∀ i ∈ Ioc J m, |jac a c ψ i| ≤ C0 * δ ^ 6 * W) →
        ψ m ≤ W → |ψ m - ψ (m + 1)| ≤ Λ * δ * W → w0 ≤ ψ m →
        (∀ k ∈ Icc (J + 1) N, jac a c Y k = 0) → |Y N| ≤ Ymax → |Y (N + 1)| ≤ Ymax →
        ∃ κ μ : ℝ, |μ| ≤ 3 * κ2 * a (N + 1) * Ymax * Real.exp (-airyXi (X N)) ∧
          (∀ k ∈ Icc J m, |Y k - κ * ψ k| ≤
            C * δ ^ 3 * |κ| * W + 2 / (ca * w0) * windowExp c1 ca Sg Qq S * (|μ| / δ)) ∧
          (∀ k ∈ Icc m (N + 1), |Y k - κ * ψ k| ≤
            C * δ ^ 3 * |κ| * ψ k + secondConst c1 ca κ1 κ2 * |μ| / δ / airyWt (X k)) := by
  obtain ⟨δ0, hδ0, C5, hC5, H⟩ := recessive_airy_selection c1 B ca κ1 κ2 C0 hca hC0
  obtain ⟨hCge, hCpos⟩ := windowConst_ge hc1 hca hC0 hC5 hΛ hSg hQq hS
  refine ⟨δ0, hδ0, windowConst c1 ca C0 C5 Λ Sg Qq S, hCpos, ?_⟩
  intro X ψ a c Y J m N δ W Ymax hJm hmN hδ hL hψ hgap hXS ha hc ha' hdefT hdefW hψW hLip hw hY hYN hYN1
  have hδp := hL.δ_pos
  have hmem : m ∈ Icc m (N + 1) := by rw [mem_Icc]; omega
  have hmem1 : m + 1 ∈ Icc m (N + 1) := by rw [mem_Icc]; omega
  have hmN' : m ∈ Icc m N := by rw [mem_Icc]; omega
  have haTop : ∀ k ∈ Icc (m + 1) (N + 1), ca ≤ a k := fun k hk =>
    ha k (by rw [mem_Icc] at hk ⊢; omega)
  obtain ⟨f0, hrow, hfN, hfN1, hf1, hf2, hf3, hf2row, hcas, hf2bd, hYsel⟩ :=
    H X ψ a c m N δ hmN hδ hL hψ haTop hdefT
  obtain ⟨κ, μ, hdec, hμ⟩ := hYsel Y Ymax (fun k hk => hY k (by rw [mem_Icc] at hk ⊢; omega)) hYN hYN1
  have hnδ := window_len hc1 hJm hgap hXS
  have hane : ∀ k ∈ Icc (J + 1) (N + 1), a k ≠ 0 := fun k hk => (lt_of_lt_of_le hca (ha k hk)).ne'
  obtain ⟨F, hF, hFf, hFw⟩ := window_from_top (J := J) (m := m) (N := N) (δ := δ) (W := W) (c1 := c1)
    (ca := ca) (C0 := C0) (C5 := C5) (Λ := Λ) (Sg := Sg) (Qq := Qq) (S := S) hδp hL.δ_le_one hc1 hca hC0
    hC5.le hΛ hSg hQq hS hJm hmN hnδ ha hc ha' hdefW hrow (hf1 m hmem) (hf3 m hmN') (hψ.pos hmem).le hψW hLip
  obtain ⟨F2, hF2, hF2f⟩ := extend_below a c (secondSol a f0 m) J m N hJm hmN hane hf2row
  -- Y = κ F + μ F₂ on the window
  have hErow : ∀ k ∈ Icc (J + 1) N, jac a c (fun i => Y i - κ * F i - μ * F2 i) k = 0 := by
    intro k hk
    have e1 := hY k hk
    have e2 := hF k hk
    have e3 := hF2 k hk
    simp only [jac] at e1 e2 e3 ⊢
    linear_combination e1 - κ * e2 - μ * e3
  have hEm : Y m - κ * F m - μ * F2 m = 0 := by
    rw [hFf m hmem, hF2f m hmem, hdec m hmem]; ring
  have hEm1 : Y (m + 1) - κ * F (m + 1) - μ * F2 (m + 1) = 0 := by
    rw [hFf (m + 1) hmem1, hF2f (m + 1) hmem1, hdec (m + 1) hmem1]; ring
  have hE := eq_zero_of_two_values a c (fun i => Y i - κ * F i - μ * F2 i) (J + 1) N m hErow hane
    (by rw [mem_Icc]; omega) hEm hEm1
  have hYF : ∀ k ∈ Icc J (N + 1), Y k = κ * F k + μ * F2 k := by
    intro k hk
    have := hE k (by rw [mem_Icc] at hk ⊢; omega)
    linarith
  refine ⟨κ, μ, hμ, ?_, ?_⟩
  · -- oscillatory window
    -- the exact second solution at the junction
    have hf2m : secondSol a f0 m m = 0 := by simp [secondSol, redSum]
    have hcm := hcas m hmN'
    unfold cas at hcm
    rw [hf2m] at hcm
    have hf0m : w0 / 2 ≤ f0 m := by
      have := (hf2 m hmem).1
      linarith
    have ham : ca ≤ a (m + 1) := haTop (m + 1) (by rw [mem_Icc]; omega)
    have hf0mpos : 0 < f0 m := by linarith
    have hapos : 0 < a (m + 1) := lt_of_lt_of_le hca ham
    have hf2pos : secondSol a f0 m (m + 1) = 1 / (a (m + 1) * f0 m) := by
      have hne : a (m + 1) * f0 m ≠ 0 := (mul_pos hapos hf0mpos).ne'
      rw [eq_div_iff hne]
      linarith
    have hf2le : secondSol a f0 m (m + 1) ≤ 2 / (ca * w0) := by
      rw [hf2pos]
      rw [div_le_div_iff₀ (mul_pos hapos hf0mpos) (mul_pos hca hw0)]
      have : ca * (w0 / 2) ≤ a (m + 1) * f0 m := mul_le_mul ham hf0m (by positivity) hapos.le
      linarith
    have hF2m : F2 m = 0 := by rw [hF2f m hmem, hf2m]
    have hF2m1 : F2 (m + 1) = secondSol a f0 m (m + 1) := hF2f (m + 1) hmem1
    have hhom := window_hom_bound (a := a) (c := c) (G := F2) (J := J) (m := m) (δ := δ) (c1 := c1) (ca := ca)
      (Sg := Sg) (Qq := Qq) (S := S) hδp hL.δ_le_one hca hSg hQq hnδ
      (fun k hk => hF2 k (by rw [mem_Ioc] at hk; rw [mem_Icc]; omega))
      (fun k hk => ha k (by rw [mem_Icc] at hk ⊢; omega)) hc ha'
    intro k hk
    have hkN : k ∈ Icc J (N + 1) := by rw [mem_Icc] at hk ⊢; omega
    have hfk := hFw k hk
    have hF2k := hhom k hk
    have hf2nn : 0 ≤ secondSol a f0 m (m + 1) := (hf2bd (m + 1) hmem1).1
    rw [hF2m, hF2m1, zero_sub, abs_neg, abs_zero, zero_add, abs_of_nonneg hf2nn] at hF2k
    have hE1 := windowExp_pos c1 ca Sg Qq S
    have hF2b : |F2 k| ≤ 2 / (ca * w0) * windowExp c1 ca Sg Qq S / δ := by
      refine hF2k.trans ?_
      have : secondSol a f0 m (m + 1) / δ ≤ 2 / (ca * w0) / δ := by gcongr
      calc secondSol a f0 m (m + 1) / δ * windowExp c1 ca Sg Qq S
          ≤ 2 / (ca * w0) / δ * windowExp c1 ca Sg Qq S := by gcongr
        _ = 2 / (ca * w0) * windowExp c1 ca Sg Qq S / δ := by ring
    have hYk : Y k - κ * ψ k = κ * (F k - ψ k) + μ * F2 k := by rw [hYF k hkN]; ring
    rw [hYk]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have b1 : |κ| * |F k - ψ k| ≤ |κ| * (windowConst c1 ca C0 C5 Λ Sg Qq S * δ ^ 3 * W) :=
      mul_le_mul_of_nonneg_left hfk (abs_nonneg _)
    have b2 : |μ| * |F2 k| ≤ |μ| * (2 / (ca * w0) * windowExp c1 ca Sg Qq S / δ) :=
      mul_le_mul_of_nonneg_left hF2b (abs_nonneg _)
    have e : |μ| * (2 / (ca * w0) * windowExp c1 ca Sg Qq S / δ) =
        2 / (ca * w0) * windowExp c1 ca Sg Qq S * (|μ| / δ) := by ring
    nlinarith
  · -- top window
    intro k hk
    have hkN : k ∈ Icc J (N + 1) := by rw [mem_Icc] at hk ⊢; omega
    have hYk : Y k - κ * ψ k = κ * (f0 k - ψ k) + μ * secondSol a f0 m k := by rw [hdec k hk]; ring
    rw [hYk]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have b1 : |κ| * |f0 k - ψ k| ≤ |κ| * (C5 * δ ^ 3 * ψ k) :=
      mul_le_mul_of_nonneg_left (hf1 k hk) (abs_nonneg _)
    have hf2k := hf2bd k hk
    have b2 : |μ| * |secondSol a f0 m k| ≤ |μ| * (secondConst c1 ca κ1 κ2 / δ / airyWt (X k)) := by
      rw [abs_of_nonneg hf2k.1]
      exact mul_le_mul_of_nonneg_left hf2k.2 (abs_nonneg _)
    have hψk := (hψ.pos hk).le
    have h3 : 0 ≤ δ ^ 3 := by positivity
    have hC5C : C5 ≤ windowConst c1 ca C0 C5 Λ Sg Qq S := hCge
    have b3 : |κ| * (C5 * δ ^ 3 * ψ k) ≤ windowConst c1 ca C0 C5 Λ Sg Qq S * δ ^ 3 * |κ| * ψ k := by
      have h4 := mul_nonneg (mul_nonneg h3 hψk) (abs_nonneg κ)
      have h5 := mul_le_mul_of_nonneg_right hC5C h4
      calc |κ| * (C5 * δ ^ 3 * ψ k) = C5 * (δ ^ 3 * ψ k * |κ|) := by ring
        _ ≤ windowConst c1 ca C0 C5 Λ Sg Qq S * (δ ^ 3 * ψ k * |κ|) := h5
        _ = _ := by ring
    have e : |μ| * (secondConst c1 ca κ1 κ2 / δ / airyWt (X k)) =
        secondConst c1 ca κ1 κ2 * |μ| / δ / airyWt (X k) := by ring
    calc _ ≤ |κ| * (C5 * δ ^ 3 * ψ k) + |μ| * (secondConst c1 ca κ1 κ2 / δ / airyWt (X k)) := add_le_add b1 b2
      _ ≤ _ := add_le_add b3 e.le

/-- info: 'FormalResearch.Special.discrete_airy_window_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.discrete_airy_window_physical

end FormalResearch.Special
