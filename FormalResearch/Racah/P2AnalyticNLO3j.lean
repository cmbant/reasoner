module

public import FormalResearch.Racah.P2AnalyticNLO3jAlg
public import FormalResearch.Racah.P2AnalyticNLO3jDeriv
public import FormalResearch.Racah.P2AnalyticBridge3j

/-!
# Next-to-leading squeezed `3j` formula (Weyl P2, `thm:3jNLO`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:3jNLO` (`eq:3jimproved`, `eq:3jf2`,
`eq:3jf2seednorm`), with the uniform remainder of `thm:3jeven` (`Phi3j_even_expansion`).

## Results

* `f3even_one_eq_nloF2` (**`eq:3jf2`**): for `M ± σ` integers, `L = L₀ + k` and `x ∈ (-1,1)`,
  `f_2(x) = ∂_t G(x,t)|_{t=0} = (A_2 f' + B_2 f)/(12(x²-1))`, `f = d^L_{Mσ}(arccos x)`, with the
  paper's `A_2 = 2J(x³-x) - 4x(M²+σ²) + 2Mσ(x²+3) + 4x`, `B_2 = J(x²-3) + 2Mσ x`,
  `J = L(L+1)` (`nloA2`, `nloB2`, `nloF2` of `P2AnalyticNLO3jAlg`).
* `Phi3j_nlo_expansion` (**`eq:3jimproved`**): uniformly on compact `K ⊆ (-1,1)`,
  `|Φ_L^{M,σ}(x;N⁻¹) - f(x) - N⁻² f_2(x)| ≤ C N⁻⁴`.
* `Phi3j_gaunt_nlo` (Gaunt remark to order `N⁻²`): `M = 0`, `μ = 0`:
  `Φ = d^L_{0σ}(π/2) [1 + J/(4N²)] + O(N⁻⁴)`.  (The `N⁻⁴` coefficient `J(5J-4)/32` needs
  `thm:3jNNLO` and is not formalised here.)
* `nlo_e_eq`: the induction statement `√(τ^α τ'^β) q_k = H_{L₀+k} + μ d_{L₀+k}`.
* `P2AnalyticNLO3jUniform`: the `3j` half of `cor:uniformNLO`.

## Route (as in the paper)

`H_L := f_2 - (2L+1)L(L+1)/12 · d_L` satisfies the inhomogeneous rank recurrence `nloH_rec`
(ladders differentiated once in `x`, ODE for `d''`); the true `t`-derivative of the carrier,
`e_k = √(τ^α τ'^β) q_k` with `q_k = ∂_t P̃_{L₀+k}|_{t=0}`, satisfies the same recurrence
(`qt3_rank`, the rank recurrence differentiated in `t`), up to the `L`-independent part `μ d_L`
of the seed derivative (which drops out by the homogeneous recurrence of `d`).  The starts agree
(`e_0 = e_1 = 0`; the seed identity `nlo_seed_alg`, i.e. `eq:3jf2seednorm`, for `M, σ` not both
zero, a direct computation from `d^0_{00} = 1`, `d^1_{00} = x` for `M = σ = 0`), so
`rec_seq_ext` closes the induction.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner Set

/-! ### Real-number bookkeeping for `α = |M-σ|`, `β = |M+σ|` -/

lemma nlo_real_facts (M σ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β) :
    ((max |M| |σ| : ℚ) : ℝ) = ((α : ℝ) + β) / 2 ∧
      (M : ℝ) ^ 2 + (σ : ℝ) ^ 2 = ((α : ℝ) ^ 2 + (β : ℝ) ^ 2) / 2 ∧
      (M : ℝ) * σ = ((β : ℝ) ^ 2 - (α : ℝ) ^ 2) / 4 := by
  have h1 : (M - σ) ^ 2 = (α : ℚ) ^ 2 := by rw [← hα, sq_abs]
  have h2 : (M + σ) ^ 2 = (β : ℚ) ^ 2 := by rw [← hβ, sq_abs]
  have h3 := hahn_alpha_add_beta M σ
  rw [hα, hβ] at h3
  have h1r := congrArg (Rat.cast : ℚ → ℝ) h1
  have h2r := congrArg (Rat.cast : ℚ → ℝ) h2
  have h3r : (α : ℝ) + β = 2 * ((max |M| |σ| : ℚ) : ℝ) := by exact_mod_cast h3
  push_cast at h1r h2r
  refine ⟨by linarith, by nlinarith, by nlinarith⟩

/-- `d^0_{00} = 1` and `d^1_{00} = x`. -/
lemma wdx_zero_zero_zero {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) : wignerSmallDx 0 0 0 y = 1 := by
  have h := dZero3_start_eq_wignerD 0 0 0 0 (by simp) (by simp) hy
  rw [dZero3_zero] at h
  simp [seed3, pPlus3, pMinus3] at h
  simpa using h.symm

lemma wdx_one_zero_zero {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) : wignerSmallDx 1 0 0 y = y := by
  unfold wignerSmallDx
  rw [wignerSmallD_one_zero_zero, Real.cos_arccos hy.1 hy.2]

/-- For `M = σ = 0`: `H_0 = 0` and `H_1 = 0` (the two starts). -/
lemma nloH_zero_zero {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : nloH 0 0 0 x = 0 := by
  have heq : wignerSmallDx 0 0 0 =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact wdx_zero_zero_zero ⟨hy.1.le, hy.2.le⟩
  have h1 : deriv (wignerSmallDx 0 0 0) x = 0 := by rw [heq.deriv_eq]; simp
  have h2 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold nloH nloF2 nloA2 nloB2
  rw [h1, wdx_zero_zero_zero ⟨hx.1.le, hx.2.le⟩]
  simp

lemma nloH_one_zero_zero {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : nloH 1 0 0 x = 0 := by
  have heq : wignerSmallDx 1 0 0 =ᶠ[nhds x] fun y => y := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact wdx_one_zero_zero ⟨hy.1.le, hy.2.le⟩
  have h1 : deriv (wignerSmallDx 1 0 0) x = 1 := by rw [heq.deriv_eq]; simp
  have h2 : x ^ 2 - 1 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold nloH nloF2 nloA2 nloB2
  rw [h1, wdx_one_zero_zero ⟨hx.1.le, hx.2.le⟩]
  simp only [Rat.cast_one, Rat.cast_zero]
  field_simp
  ring

/-! ### The induction -/

/-- `e_k = √(τ^α τ'^β) q_k` equals `H_{L₀+k} + μ d_{L₀+k}`, for every `k`. -/
theorem nlo_e_eq (M σ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (k : ℕ) :
    Real.sqrt (((1 - x) / 2) ^ pPlus3 M σ * ((1 + x) / 2) ^ pMinus3 M σ) *
        qt3 M σ k ((1 - x) / 2) =
      nloH (max |M| |σ| + (k : ℚ)) M σ x +
        nloMu (pPlus3 M σ) (pMinus3 M σ) x * wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x := by
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  set s := Real.sqrt (((1 - x) / 2) ^ pPlus3 M σ * ((1 + x) / 2) ^ pMinus3 M σ) with hs
  set μ := nloMu (pPlus3 M σ) (pMinus3 M σ) x with hμ
  have hd : ∀ j : ℕ, s * ptilde3 M σ j ((1 - x) / 2) 0 =
      wignerSmallDx (max |M| |σ| + (j : ℚ)) M σ x := by
    intro j
    rw [← dZero3_eq_wignerD M σ α β hα hβ hxI j]
    unfold dZero3
    rw [hs]
  have hL0 : (0 : ℚ) ≤ max |M| |σ| := le_trans (abs_nonneg M) (le_max_left _ _)
  obtain ⟨hL0r, hSr, hmr⟩ := nlo_real_facts M σ α β hα hβ
  -- the two starts of `ê_k = H + μ d`
  have hst0 : nloH (max |M| |σ| + ((0 : ℕ) : ℚ)) M σ x +
      μ * wignerSmallDx (max |M| |σ| + ((0 : ℕ) : ℚ)) M σ x = 0 := by
    simp only [Nat.cast_zero, add_zero]
    by_cases h0 : max |M| |σ| = 0
    · have hM : M = 0 := abs_nonpos_iff.mp (h0 ▸ le_max_left _ _)
      have hs0 : σ = 0 := abs_nonpos_iff.mp (h0 ▸ le_max_right _ _)
      subst hM hs0
      simp only [abs_zero, max_self]
      have : μ = 0 := by
        rw [hμ]; unfold nloMu pPlus3 pMinus3; simp [ccCent]
      rw [this, nloH_zero_zero hx]; simp
    · have hLpos : (0 : ℝ) < ((α : ℝ) + β) / 2 := by
        rw [← hL0r]; exact_mod_cast lt_of_le_of_ne hL0 (Ne.symm h0)
      have hlad := wignerSmallDx_rank_lower (max |M| |σ|) M σ hx
      rw [wigR_eq_Rk, Rk_L0, zero_mul] at hlad
      have hseed := nlo_seed_alg x α β (wignerSmallDx (max |M| |σ|) M σ x)
        (deriv (wignerSmallDx (max |M| |σ|) M σ) x) hx.1 hx.2 (by linarith)
        (by
          have e : (σ : ℝ) * M = ((β : ℝ) ^ 2 - (α : ℝ) ^ 2) / 4 := by rw [mul_comm]; exact hmr
          rw [hL0r, e] at hlad
          linear_combination -hlad)
      rw [nloH_eq, hμ, br3_pPlus hα, br3_pMinus hβ]
      unfold nloMu ccCent
      rw [← hL0r, ← hSr, ← hmr] at hseed
      exact hseed
  have hst1 : nloH (max |M| |σ| + ((1 : ℕ) : ℚ)) M σ x +
      μ * wignerSmallDx (max |M| |σ| + ((1 : ℕ) : ℚ)) M σ x = 0 := by
    by_cases h0 : max |M| |σ| = 0
    · have hM : M = 0 := abs_nonpos_iff.mp (h0 ▸ le_max_left _ _)
      have hs0 : σ = 0 := abs_nonpos_iff.mp (h0 ▸ le_max_right _ _)
      subst hM hs0
      simp only [abs_zero, max_self, Nat.cast_one, zero_add]
      have : μ = 0 := by
        rw [hμ]; unfold nloMu pPlus3 pMinus3; simp [ccCent]
      rw [this, nloH_one_zero_zero hx]; simp
    · have hLpos : (0 : ℚ) < max |M| |σ| := lt_of_le_of_ne hL0 (Ne.symm h0)
      have hLr : ((max |M| |σ| : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hLpos.ne'
      have hR : Rk M σ (max |M| |σ| + 1) ≠ 0 := (Rk_pos M σ _ (by linarith)).ne'
      have hH := nloH_rec (max |M| |σ|) M σ hx
      have hW := wignerSmallDx_rank_rec (max |M| |σ|) M σ hxI
      simp only [wigR_eq_Rk, Rk_L0, zero_mul, mul_zero, sub_zero, zero_add]
        at hH hW
      simp only [Nat.cast_one]
      have hst0' : nloH (max |M| |σ|) M σ x + μ * wignerSmallDx (max |M| |σ|) M σ x = 0 := by
        simpa using hst0
      refine mul_left_cancel₀ (mul_ne_zero hLr hR) ?_
      linear_combination (-1) * hH - μ * hW +
        ((2 * ((max |M| |σ| : ℚ) : ℝ) + 1) *
          (((max |M| |σ| : ℚ) : ℝ) * (((max |M| |σ| : ℚ) : ℝ) + 1) * x - (M : ℝ) * σ)) * hst0'
  -- the recurrence
  have hrec : ∀ j : ℕ,
      (((max |M| |σ| + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ) *
        Rk M σ (max |M| |σ| + ((j + 1 : ℕ) : ℚ) + 1)) *
          (s * qt3 M σ (j + 2) ((1 - x) / 2) - (nloH (max |M| |σ| + ((j + 2 : ℕ) : ℚ)) M σ x +
            μ * wignerSmallDx (max |M| |σ| + ((j + 2 : ℕ) : ℚ)) M σ x)) =
      ((2 * ((max |M| |σ| + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) *
        (((max |M| |σ| + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ) *
          (((max |M| |σ| + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) * x - (M : ℝ) * σ)) *
          (s * qt3 M σ (j + 1) ((1 - x) / 2) - (nloH (max |M| |σ| + ((j + 1 : ℕ) : ℚ)) M σ x +
            μ * wignerSmallDx (max |M| |σ| + ((j + 1 : ℕ) : ℚ)) M σ x)) -
      ((((max |M| |σ| + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) *
        Rk M σ (max |M| |σ| + ((j + 1 : ℕ) : ℚ))) *
          (s * qt3 M σ j ((1 - x) / 2) - (nloH (max |M| |σ| + (j : ℚ)) M σ x +
            μ * wignerSmallDx (max |M| |σ| + (j : ℚ)) M σ x)) := by
    intro j
    have hq := qt3_rank M σ j ((1 - x) / 2)
    have e : (1 : ℝ) - 2 * ((1 - x) / 2) = x := by ring
    rw [e] at hq
    have hH := nloH_rec (max |M| |σ| + ((j + 1 : ℕ) : ℚ)) M σ hx
    have hW := wignerSmallDx_rank_rec (max |M| |σ| + ((j + 1 : ℕ) : ℚ)) M σ hxI
    have e1 : max |M| |σ| + ((j + 1 : ℕ) : ℚ) - 1 = max |M| |σ| + (j : ℚ) := by push_cast; ring
    have e2 : max |M| |σ| + ((j + 1 : ℕ) : ℚ) + 1 = max |M| |σ| + ((j + 2 : ℕ) : ℚ) := by
      push_cast; ring
    have hH' : nloH (max |M| |σ| + ((j + 1 : ℕ) : ℚ) + 1) M σ x =
        nloH (max |M| |σ| + ((j + 2 : ℕ) : ℚ)) M σ x := by rw [e2]
    have hW' : wignerSmallDx (max |M| |σ| + ((j + 1 : ℕ) : ℚ) + 1) M σ x =
        wignerSmallDx (max |M| |σ| + ((j + 2 : ℕ) : ℚ)) M σ x := by rw [e2]
    rw [e1, hH'] at hH
    rw [e1, hW'] at hW
    rw [wigR_eq_Rk, wigR_eq_Rk] at hH hW
    have hdj := hd j
    have hdj1 := hd (j + 1)
    set L : ℝ := (((max |M| |σ| + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ)) with hL
    set R1 := Rk M σ (max |M| |σ| + ((j + 1 : ℕ) : ℚ))
    linear_combination (-s) * hq + hH + μ * hW + ((L + 1) * R1 * L ^ 2) * hdj
  have hδ := rec_seq_ext
    (fun j => s * qt3 M σ j ((1 - x) / 2) - (nloH (max |M| |σ| + (j : ℚ)) M σ x +
      μ * wignerSmallDx (max |M| |σ| + (j : ℚ)) M σ x)) (fun _ => (0 : ℝ))
    (fun j => (((max |M| |σ| + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ) *
        Rk M σ (max |M| |σ| + ((j + 1 : ℕ) : ℚ) + 1)))
    (fun j => (2 * ((max |M| |σ| + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) *
        (((max |M| |σ| + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ) *
          (((max |M| |σ| + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) * x - (M : ℝ) * σ))
    (fun j => (((max |M| |σ| + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) *
        Rk M σ (max |M| |σ| + ((j + 1 : ℕ) : ℚ)))
    (by simp only [qt3_zero, mul_zero, zero_sub]; linarith)
    (by simp only [qt3_one, mul_zero, zero_sub]; linarith)
    (by
      intro j
      have hLpos : (0 : ℚ) < max |M| |σ| + ((j + 1 : ℕ) : ℚ) := by
        have : (0 : ℚ) < ((j + 1 : ℕ) : ℚ) := by positivity
        linarith
      have hLr : ((max |M| |σ| + ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hLpos.ne'
      have hR : Rk M σ (max |M| |σ| + ((j + 1 : ℕ) : ℚ) + 1) ≠ 0 := by
        apply (Rk_pos M σ _ _).ne'
        have : (0 : ℚ) ≤ ((j + 1 : ℕ) : ℚ) := Nat.cast_nonneg _
        linarith
      exact mul_ne_zero hLr hR)
    (fun j => hrec j) (fun j => by simp)
  have := hδ k
  linarith

/-- **`thm:3jNLO`, `eq:3jf2`** (proved): for `M ± σ` integers (`α = |M-σ|`, `β = |M+σ|`), `L = L₀ + k`
and `x ∈ (-1,1)`, the first correction `f_2 = ∂_t G(x,t)|_{t=0}` of the squeezed `3j` germ is
`f_2(x) = (A_2(x) f'(x) + B_2(x) f(x)) / (12 (x²-1))`, `f = d^L_{Mσ}(arccos x)`,
`A_2 = 2J(x³-x) - 4x(M²+σ²) + 2Mσ(x²+3) + 4x`, `B_2 = J(x²-3) + 2Mσ x`, `J = L(L+1)`. -/
theorem f3even_one_eq_nloF2 (M σ L : ℚ) (k : ℕ) (hL : L = max |M| |σ| + k) (α β : ℕ)
    (hα : |M - σ| = α) (hβ : |M + σ| = β) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    f3even M σ k 1 x =
      (nloA2 L M σ x * deriv (wignerSmallDx L M σ) x + nloB2 L M σ x * wignerSmallDx L M σ x) /
        (12 * (x ^ 2 - 1)) := by
  subst hL
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  rw [f3even_one_eq M σ k hx, nlo_e_eq M σ α β hα hβ hx k,
    dZero3_eq_wignerD M σ α β hα hβ hxI k]
  obtain ⟨hL0r, -, -⟩ := nlo_real_facts M σ α β hα hβ
  have hc : ccCent (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) / 2 =
      (2 * (((max |M| |σ| + (k : ℚ) : ℚ)) : ℝ) + 1) *
        ((((max |M| |σ| + (k : ℚ) : ℚ)) : ℝ) * ((((max |M| |σ| + (k : ℚ) : ℚ)) : ℝ) + 1)) / 12 := by
    rw [br3_pPlus hα, br3_pMinus hβ]
    unfold ccCent
    have hL0r' : max |(M : ℝ)| |(σ : ℝ)| = ((α : ℝ) + β) / 2 := by
      have := hL0r; push_cast at this; exact this
    push_cast
    rw [hL0r']
    ring
  have hF : nloH (max |M| |σ| + (k : ℚ)) M σ x =
      nloF2 (max |M| |σ| + (k : ℚ)) M σ x -
        (2 * (((max |M| |σ| + (k : ℚ) : ℚ)) : ℝ) + 1) *
          ((((max |M| |σ| + (k : ℚ) : ℚ)) : ℝ) * ((((max |M| |σ| + (k : ℚ) : ℚ)) : ℝ) + 1)) / 12 *
            wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x := rfl
  rw [hF]
  unfold nloF2
  linear_combination (wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x) * hc

/-- **`thm:3jNLO`, `eq:3jimproved`** (proved): uniformly on compact `K ⊆ (-1,1)`,
`Φ_L^{M,σ}(x;N⁻¹) = f(x) + N⁻² (A_2 f' + B_2 f)/(12(x²-1)) + O_K(N⁻⁴)`, `f = d^L_{Mσ}(arccos x)`,
`x = 2μ/N`, over admissible `N` and physical lattice points `μ` (`SpecAdm`, `Lat4`). -/
theorem Phi3j_nlo_expansion (M σ L : ℚ) (k : ℕ) (hL : L = max |M| |σ| + k) {K : Set ℝ}
    (hK : IsCompact K) (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    ∃ C N₀ : ℝ, ∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₀ ≤ (N : ℝ) →
      2 * (μ : ℝ) / N ∈ K →
      |Phi3j L M σ N μ - wignerSmallDx L M σ (2 * (μ : ℝ) / N) -
          (nloA2 L M σ (2 * (μ : ℝ) / N) * deriv (wignerSmallDx L M σ) (2 * (μ : ℝ) / N) +
              nloB2 L M σ (2 * (μ : ℝ) / N) * wignerSmallDx L M σ (2 * (μ : ℝ) / N)) /
            (12 * ((2 * (μ : ℝ) / N) ^ 2 - 1)) / (N : ℝ) ^ 2| ≤ C / (N : ℝ) ^ 4 := by
  obtain ⟨C, N₀, h⟩ := Phi3j_even_expansion M σ L k hL hK hKI 2
  refine ⟨C, N₀, fun N μ hA hlat hN hxK => ?_⟩
  have key := h N μ hA hlat hN hxK
  obtain ⟨α, β, hα, hβ⟩ := specAdm_alpha_beta hA
  have hx := hKI hxK
  have hxI : (2 * (μ : ℝ) / N) ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have h0 : f3even M σ k 0 (2 * (μ : ℝ) / N) = wignerSmallDx L M σ (2 * (μ : ℝ) / N) := by
    rw [f3even_zero, dZero3_eq_wignerD M σ α β hα hβ hxI k, hL]
  have h1 := f3even_one_eq_nloF2 M σ L k hL α β hα hβ hx
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.mul_zero, pow_zero,
    div_one, Nat.mul_one] at key
  rw [h0, h1] at key
  have e : (N : ℝ) ^ (2 * 2) = (N : ℝ) ^ 4 := by norm_num
  rw [e] at key
  rw [sub_sub]
  exact key


/-- At `M = 0`, `x = 0`: `f_2(0) = J f(0)/4`, `J = L(L+1)` (the Gaunt specialization of `eq:3jf2`). -/
lemma nloF2_gaunt (L σ : ℚ) :
    nloF2 L 0 σ 0 = (L : ℝ) * ((L : ℝ) + 1) / 4 * wignerSmallDx L 0 σ 0 := by
  unfold nloF2 nloA2 nloB2
  simp only [Rat.cast_zero]
  ring

/-- **Scalar Gaunt specialization** (`rem` after `thm:3jNLO`, `eq:gauntSpecialization` to order
`N⁻²`; proved): for `M = 0`, `μ = 0` (so `x = 0`) and `L = |σ| + k`,
`Φ_L^{0,σ}(0;N⁻¹) = d^L_{0σ}(π/2) [1 + J/(4N²)] + O(N⁻⁴)`, `J = L(L+1)`, over admissible `N`.
The `N⁻⁴` coefficient `J(5J-4)/32` of the paper's `eq:gauntSpecialization` needs `thm:3jNNLO`
and is not covered here. -/
theorem Phi3j_gaunt_nlo (L σ : ℚ) (k : ℕ) (hL : L = max |(0 : ℚ)| |σ| + k) :
    ∃ C N₀ : ℝ, ∀ N : ℚ, SpecAdm 0 σ N → Lat4 0 σ N 0 → N₀ ≤ (N : ℝ) →
      |Phi3j L 0 σ N 0 - wignerSmallD L 0 σ (Real.pi / 2) *
          (1 + (L : ℝ) * ((L : ℝ) + 1) / (4 * (N : ℝ) ^ 2))| ≤ C / (N : ℝ) ^ 4 := by
  have hK : IsCompact ({0} : Set ℝ) := isCompact_singleton
  have hKI : ({0} : Set ℝ) ⊆ Ioo (-1 : ℝ) 1 := by
    intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; constructor <;> norm_num
  obtain ⟨C, N₀, h⟩ := Phi3j_nlo_expansion 0 σ L k hL hK hKI
  refine ⟨C, N₀, fun N hA hlat hN => ?_⟩
  have key := h N 0 hA hlat hN (by simp)
  have e0 : (2 * ((0 : ℚ) : ℝ) / N) = 0 := by simp
  rw [e0] at key
  have hf : nloF2 L 0 σ 0 = _ := nloF2_gaunt L σ
  unfold nloF2 at hf
  rw [hf] at key
  have hd : wignerSmallD L 0 σ (Real.pi / 2) = wignerSmallDx L 0 σ 0 := by
    unfold wignerSmallDx; rw [Real.arccos_zero]
  rw [hd]
  convert key using 2
  ring

/-- info: 'FormalResearch.Racah.f3even_one_eq_nloF2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms f3even_one_eq_nloF2

/-- info: 'FormalResearch.Racah.Phi3j_nlo_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_nlo_expansion

/-- info: 'FormalResearch.Racah.nlo_e_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nlo_e_eq

/-- info: 'FormalResearch.Racah.Phi3j_gaunt_nlo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_gaunt_nlo

end FormalResearch.Racah
