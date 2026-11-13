module

public import FormalResearch.Racah.P2AnalyticNLO3j

/-!
# Uniform next-to-leading `3j` form (Weyl P2, `cor:uniformNLO`, `3j` half)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `cor:uniformNLO` (`eq:3juniformNLO`),
`thm:uniformedge`(a) and `lem:sqrtfreecarrier` (`eq:sqrtfreecarrier`).

On the physical lattice `Φ = E_N W_{3j} S(τ,t)`, `S = P̃_{L₀+k}(τ;t) / √Ct(2L+1,1,t)`, with
`W_{3j} = √(τ^{p_+} τ'^{p_-})` (`W3`), `E_N² = 𝔠_{p_+}(τ,h) 𝔠_{p_-}(τ',h) / (τ^{p_+} τ'^{p_-})`
(`edgeE3`), `t = N⁻²`.  `S` is analytic near `t = 0`, uniformly for `τ ∈ [0,1]`; its Taylor
coefficients are `W S₀ = d` and `W S₁ = f_2 + μ d` (`μ = nloMu`, so `-N⁻²μ = e_2^{3j}`), which gives

* `Phi3j_uniform_nlo` (**`eq:3juniformNLO`**): uniformly over all admissible `N` and the whole
  physical lattice `μ`,
  `|Φ - E_N [d + N⁻² f_2 - e_2^{3j} d]| ≤ C N⁻⁴ E_N W_{3j}`.

Not covered: the `6j` half of `cor:uniformNLO`, and the statement that `N⁻²f_2 - e_2 d` is `W` times
a polynomial (the explicit polynomial form).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner Set

/-- `W_{3j}(x) = √(((1-x)/2)^{p_+} ((1+x)/2)^{p_-})`. -/
noncomputable def W3 (M σ : ℚ) (x : ℝ) : ℝ :=
  Real.sqrt (((1 - x) / 2) ^ pPlus3 M σ * ((1 + x) / 2) ^ pMinus3 M σ)

/-- The edge factor `E_N(x)` at `t = N⁻²`:
`E² = 𝔠_{p_+}((1-x)/2, h) 𝔠_{p_-}((1+x)/2, h) / (((1-x)/2)^{p_+} ((1+x)/2)^{p_-})`. -/
noncomputable def edgeE3 (M σ : ℚ) (x t : ℝ) : ℝ :=
  Real.sqrt (Ct (pPlus3 M σ) ((1 - x) / 2) t * Ct (pMinus3 M σ) ((1 + x) / 2) t /
    (((1 - x) / 2) ^ pPlus3 M σ * ((1 + x) / 2) ^ pMinus3 M σ))

/-- The paper's `e_2^{3j}(x) = -p_+(p_+²-1)/(12N²(1-x)²) - p_-(p_-²-1)/(12N²(1+x)²)`. -/
noncomputable def e2three (M σ : ℚ) (N x : ℝ) : ℝ :=
  -((pPlus3 M σ : ℝ) * ((pPlus3 M σ : ℝ) ^ 2 - 1)) / (12 * N ^ 2 * (1 - x) ^ 2) -
    ((pMinus3 M σ : ℝ) * ((pMinus3 M σ : ℝ) ^ 2 - 1)) / (12 * N ^ 2 * (1 + x) ^ 2)

/-- On the physical lattice `|x| < 1`. -/
lemma Lat4.x_mem_Ioo {M σ N μ : ℚ} (h : Lat4 M σ N μ) (hN : 0 < N) :
    2 * (μ : ℝ) / N ∈ Ioo (-1 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := h.two_mu_bounds
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1' : -((N : ℝ) - 1) ≤ 2 * μ := by exact_mod_cast h1
  have h2' : 2 * (μ : ℝ) ≤ (N : ℝ) - 1 := by exact_mod_cast h2
  constructor
  · rw [lt_div_iff₀ hNr]; linarith
  · rw [div_lt_iff₀ hNr]; linarith

/-- The analytic factor `S(τ,t) = P̃_{L₀+k}(τ;t)/√Ct(2L+1,1,t)`. -/
noncomputable def Scarrier3 (M σ : ℚ) (k : ℕ) (q : ℝ × ℝ) : ℝ :=
  ptilde3 M σ k q.1 q.2 / Real.sqrt (Ct (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) 1 q.2)

/-- `Gc3 = E · W · S` for `|x| < 1` and `t` where the radicand `Ct(2L+1,1,t)` is positive
(and the radicands of `E` are nonnegative). -/
lemma Gc3_eq_E_W_S (M σ : ℚ) (k : ℕ) {x t : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Gc3 M σ k x t = edgeE3 M σ x t * W3 M σ x * Scarrier3 M σ k ((1 - x) / 2, t) := by
  have hτ : 0 < (1 - x) / 2 := by linarith [hx.2]
  have hτ' : 0 < (1 + x) / 2 := by linarith [hx.1]
  have hQ : 0 < ((1 - x) / 2) ^ pPlus3 M σ * ((1 + x) / 2) ^ pMinus3 M σ := by positivity
  unfold Gc3 edgeE3 W3 Scarrier3
  have hsq : Real.sqrt (Ct (pPlus3 M σ) ((1 - x) / 2) t * Ct (pMinus3 M σ) ((1 + x) / 2) t) =
      Real.sqrt (Ct (pPlus3 M σ) ((1 - x) / 2) t * Ct (pMinus3 M σ) ((1 + x) / 2) t /
        (((1 - x) / 2) ^ pPlus3 M σ * ((1 + x) / 2) ^ pMinus3 M σ)) *
        Real.sqrt (((1 - x) / 2) ^ pPlus3 M σ * ((1 + x) / 2) ^ pMinus3 M σ) := by
    rw [← Real.sqrt_mul' _ hQ.le, div_mul_cancel₀ _ hQ.ne']
  rw [hsq]
  ring

/-- `∂_t S(τ,t)|_{t=0} = (c_n/2) P̃(τ;0) + q_k(τ)` and `S(τ,0) = P̃(τ;0)`. -/
lemma hasDerivAt_Scarrier3 (M σ : ℚ) (k : ℕ) (τ : ℝ) :
    HasDerivAt (fun t => Scarrier3 M σ k (τ, t))
      (cc (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) / 2 * ptilde3 M σ k τ 0 + qt3 M σ k τ) 0 := by
  set n := pPlus3 M σ + pMinus3 M σ + 2 * k + 1
  have hT := hasDerivAt_Ct n (one_ne_zero (α := ℝ))
  have hsT := hT.sqrt (by show Ct n 1 0 ≠ 0; simp [Ct_zero_t])
  have hsTne : Real.sqrt (Ct n 1 0) ≠ 0 := by simp [Ct_zero_t]
  have hinv := hsT.inv hsTne
  have hfin := (hasDerivAt_ptilde3_t M σ k τ).mul hinv
  unfold Scarrier3
  have e : (fun t => ptilde3 M σ k (τ, t).1 (τ, t).2 /
      Real.sqrt (Ct n 1 (τ, t).2)) = fun t => ptilde3 M σ k τ t * (Real.sqrt (Ct n 1 t))⁻¹ := by
    funext t; simp [div_eq_mul_inv]
  rw [e]
  refine hfin.congr_deriv ?_
  simp only [Pi.inv_apply, Ct_zero_t, one_pow, Real.sqrt_one, inv_one]
  ring

/-- **Uniform next-to-leading form, `3j`** (`cor:uniformNLO`, `eq:3juniformNLO`; proved): for fixed
`L = L₀ + k`, `M`, `σ` there are `C, N₀` such that for every admissible `N ≥ N₀` and every point `μ`
of the physical lattice (`x = 2μ/N`, no restriction to a compact subset of `(-1,1)`),
`|Φ - E_N [d + N⁻² f_2 - e_2^{3j} d]| ≤ C N⁻⁴ E_N W_{3j}`,
with `d = d^L_{Mσ}(arccos x)`, `f_2 = (A_2 d' + B_2 d)/(12(x²-1))` (`thm:3jNLO`). -/
theorem Phi3j_uniform_nlo (M σ L : ℚ) (k : ℕ) (hL : L = max |M| |σ| + k) :
    ∃ C N₀ : ℝ, ∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₀ ≤ (N : ℝ) →
      |Phi3j L M σ N μ -
          edgeE3 M σ (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2) *
            (wignerSmallDx L M σ (2 * (μ : ℝ) / N) +
              1 / (N : ℝ) ^ 2 * nloF2 L M σ (2 * (μ : ℝ) / N) -
              e2three M σ N (2 * (μ : ℝ) / N) * wignerSmallDx L M σ (2 * (μ : ℝ) / N))| ≤
        C / (N : ℝ) ^ 4 * (edgeE3 M σ (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2) *
          W3 M σ (2 * (μ : ℝ) / N)) := by
  subst hL
  -- Taylor expansion of `S` uniformly for `τ ∈ [0,1]`
  have hUo : IsOpen {p : ℝ × ℝ | 0 < Ct (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) 1 p.2} := by
    have hB : Continuous (fun q : ℝ × ℝ => Ct (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) 1 q.2) :=
      continuous_iff_continuousAt.mpr fun p => (analyticAt_radicand_B M σ k p).continuousAt
    exact isOpen_lt continuous_const hB
  have hSan : AnalyticOnNhd ℝ (Scarrier3 M σ k)
      {p : ℝ × ℝ | 0 < Ct (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) 1 p.2} := by
    intro p hp
    have h1 := analyticAt_sqrt_comp_3j (analyticAt_radicand_B M σ k p) hp
    have h3 : 0 < Real.sqrt (Ct (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) 1 p.2) :=
      Real.sqrt_pos.mpr hp
    exact (analyticAt_ptilde3 M σ k p).div h1 h3.ne'
  have hKU : (Icc (0 : ℝ) 1) ×ˢ ({0} : Set ℝ) ⊆
      {p : ℝ × ℝ | 0 < Ct (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) 1 p.2} := by
    rintro ⟨z, t⟩ ⟨_, ht⟩
    have : t = 0 := ht
    subst this
    show 0 < Ct _ 1 0
    simp [Ct_zero_t]
  obtain ⟨ρ, hρ, C, hC⟩ := taylor_uniform_of_analytic hUo hSan isCompact_Icc hKU 2
  refine ⟨C, max (((max |M| |σ| + k + 1 : ℚ)) : ℝ) (max 1 (1 / ρ)), ?_⟩
  intro N μ hA hlat hN0
  have hN1 : ((max |M| |σ| + k + 1 : ℚ) : ℝ) ≤ N := le_trans (le_max_left _ _) hN0
  have hN2 : max 1 (1 / ρ) ≤ (N : ℝ) := le_trans (le_max_right _ _) hN0
  have hk : max |M| |σ| + k + 1 ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hN2)
  have hNq : 0 < N := by exact_mod_cast hNpos
  have ht : |1 / (N : ℝ) ^ 2| ≤ ρ := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have h1 : 1 / ρ ≤ N := le_trans (le_max_right _ _) hN2
    have h2 : (1 : ℝ) ≤ N := le_trans (le_max_left _ _) hN2
    have h3 : (N : ℝ) ≤ N ^ 2 := by nlinarith
    have h4 : 1 / ρ ≤ N ^ 2 := le_trans h1 h3
    rw [div_le_iff₀ hρ] at h4
    linarith
  set x : ℝ := 2 * (μ : ℝ) / N with hxdef
  set t : ℝ := 1 / (N : ℝ) ^ 2 with htdef
  have hx : x ∈ Ioo (-1 : ℝ) 1 := Lat4.x_mem_Ioo hlat hNq
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hτK : (1 - x) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have key := hC _ hτK t ht
  obtain ⟨α, β, hα, hβ⟩ := specAdm_alpha_beta hA
  -- identify the Taylor coefficients
  have hc0 : taylorCoeff (fun z t => Scarrier3 M σ k (z, t)) 0 ((1 - x) / 2) =
      ptilde3 M σ k ((1 - x) / 2) 0 := by
    simp [taylorCoeff, Scarrier3, Ct_zero_t]
  have hc1 : taylorCoeff (fun z t => Scarrier3 M σ k (z, t)) 1 ((1 - x) / 2) =
      cc (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) / 2 * ptilde3 M σ k ((1 - x) / 2) 0 +
        qt3 M σ k ((1 - x) / 2) := by
    unfold taylorCoeff
    rw [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, div_one]
    exact (hasDerivAt_Scarrier3 M σ k ((1 - x) / 2)).deriv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
    pow_one, hc0, hc1] at key
  have habs : |t| ^ 2 = t ^ 2 := sq_abs t
  rw [habs] at key
  -- the lattice identity
  have hΦ : Phi3j (max |M| |σ| + k) M σ N μ = edgeE3 M σ x t * W3 M σ x *
      Scarrier3 M σ k ((1 - x) / 2, t) := by
    rw [Phi3j_eq_Gc3_spec M σ N μ hA hNq hlat k hk, Gc3_eq_E_W_S M σ k hx]
  -- coefficient identifications
  have hd : W3 M σ x * ptilde3 M σ k ((1 - x) / 2) 0 =
      wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x := by
    rw [← dZero3_eq_wignerD M σ α β hα hβ hxI k]
    unfold dZero3 W3
    ring
  have hf2 := f3even_one_eq M σ k hx
  have hf2' := f3even_one_eq_nloF2 M σ _ k rfl α β hα hβ hx
  have he := nlo_e_eq M σ α β hα hβ hx k
  have hH : nloH (max |M| |σ| + (k : ℚ)) M σ x =
      nloF2 (max |M| |σ| + (k : ℚ)) M σ x -
        (2 * (((max |M| |σ| + (k : ℚ) : ℚ)) : ℝ) + 1) *
          ((((max |M| |σ| + (k : ℚ) : ℚ)) : ℝ) * ((((max |M| |σ| + (k : ℚ) : ℚ)) : ℝ) + 1)) / 12 *
            wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x := rfl
  have he2 : e2three M σ N x = -t * nloMu (pPlus3 M σ) (pMinus3 M σ) x := by
    have h1 : 1 - x ≠ 0 := by linarith [hx.2]
    have h2 : 1 + x ≠ 0 := by linarith [hx.1]
    have hN : (N : ℝ) ≠ 0 := hNpos.ne'
    unfold e2three nloMu cc
    rw [htdef]
    field_simp
    ring
  -- assemble
  rw [hΦ]
  have hW0 : 0 ≤ W3 M σ x := Real.sqrt_nonneg _
  have hE0 : 0 ≤ edgeE3 M σ x t := Real.sqrt_nonneg _
  set S := Scarrier3 M σ k ((1 - x) / 2, t)
  set p0 := ptilde3 M σ k ((1 - x) / 2) 0
  set q1 := qt3 M σ k ((1 - x) / 2)
  set c := cc (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) / 2
  have hdZ := dZero3_eq_wignerD M σ α β hα hβ hxI k
  have hK : nloF2 (max |M| |σ| + (k : ℚ)) M σ x +
      nloMu (pPlus3 M σ) (pMinus3 M σ) x * wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x -
      c * wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x - W3 M σ x * q1 = 0 := by
    have h := hf2.symm.trans hf2'
    rw [hdZ] at h
    unfold nloF2
    unfold W3
    linear_combination -h
  have hmain : edgeE3 M σ x t * W3 M σ x * S -
      edgeE3 M σ x t * (wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x +
        t * nloF2 (max |M| |σ| + (k : ℚ)) M σ x -
        e2three M σ N x * wignerSmallDx (max |M| |σ| + (k : ℚ)) M σ x) =
      edgeE3 M σ x t * W3 M σ x * (S - (p0 + (c * p0 + q1) * t)) := by
    rw [he2]
    linear_combination (edgeE3 M σ x t * (1 + t * c)) * hd - (edgeE3 M σ x t * t) * hK
  rw [hmain, abs_mul, abs_of_nonneg (mul_nonneg hE0 hW0)]
  calc edgeE3 M σ x t * W3 M σ x * |S - (p0 + (c * p0 + q1) * t)|
      ≤ edgeE3 M σ x t * W3 M σ x * (C * t ^ 2) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg hE0 hW0)
    _ = C / (N : ℝ) ^ 4 * (edgeE3 M σ x t * W3 M σ x) := by
        rw [htdef]; field_simp

/-- info: 'FormalResearch.Racah.Phi3j_uniform_nlo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_uniform_nlo

end FormalResearch.Racah
