module

public import FormalResearch.Racah.P2HahnKernel
public import FormalResearch.Racah.P2HahnReflect
public import FormalResearch.Racah.P2ThreeJRegge

/-!
# The Hahn realization in every chamber (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `sec:explicitHahn`
(`eq:HahnAllChamberPhase`, `eq:HahnInvariantParameters`).

`Phi3j_hahn_all_chambers`: for all `M, σ` with `M ± σ ∈ ℤ`, `L₀ = max(|M|,|σ|)`,
`α_H = |M-σ|`, `β_H = |M+σ|`, `D = N-L₀-1`, `n = L-L₀ ≤ D` and
`u = (N-1-|M-σ|-2μ)/2 ∈ {0,…,D}`,
`Φ_{L₀+n}^{M,σ}(x_u) = ε(M,σ) √(N/(2L+1)) √(w_H(u)/h_{H,n}) Q_n(u;α_H,β_H,D)`,
with `ε = (-1)^{α_H}` for `σ ≤ M` and `ε = 1` for `σ > M`.

The four chambers: `M ≥ |σ|` is `Phi3j_hahn`; `σ ≤ -|M|` follows by the Regge exchange
(`Phi3j_regge`, `M,σ ↦ -σ,-M`, which preserves `α_H`); `σ > |M|` and `M < -|σ|` (`σ > M`) need the
sign symmetry `Phi3j_neg_M` (and the Regge exchange for `σ > |M|`) and exchange `α_H ↔ β_H`, hence use the
Hahn reflection `hahn_normalized_reflect` (`u ↦ D-u`); the signs cancel to `ε = 1`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

private lemma natcast_eq {q : ℚ} {k : ℕ} (h : q = k) : ((q : ℝ)) = (k : ℝ) := by
  rw [h]; push_cast; rfl

/-- Chamber `σ ≤ -|M|` (and `M < |σ|`): Regge exchange. -/
lemma chamber_D (M σ N μ : ℚ) (α β D n u : ℕ) (hα : M - σ = α) (hβ : -(M + σ) = β)
    (hD : N + σ - 1 = D) (hn : n ≤ D) (hu : jPlus N (-M) + mPlus (-σ) μ = u) (huD : u ≤ D) :
    Phi3j (-σ + n) M σ N μ =
      (-1 : ℝ) ^ α * Real.sqrt ((N : ℝ) / (2 * (((-σ : ℚ) : ℝ) + n) + 1)) *
        Real.sqrt ((hahnW α β D u : ℝ) / hahnNorm α β D n) * hahnQ α β D n u := by
  rw [Phi3j_regge]
  exact Phi3j_hahn (M := -σ) (σ := -M) (by linarith) (by linarith) (by linarith) n u hn hu huD

/-- Chamber `M ≤ -|σ|`, `σ > M`: sign symmetry, then reflection. -/
lemma chamber_C (M σ N μ : ℚ) (α β D n u : ℕ) (hα : σ - M = α) (hβ : -M - σ = β)
    (hD : N + M - 1 = D) (hn : n ≤ D) (hu : jPlus N σ + mPlus (-M) (-μ) = ((D - u : ℕ) : ℚ))
    (hu' : u ≤ D) :
    Phi3j (-M + n) M σ N μ =
      (1 : ℝ) * Real.sqrt ((N : ℝ) / (2 * (((-M : ℚ) : ℝ) + n) + 1)) *
        Real.sqrt ((hahnW α β D u : ℝ) / hahnNorm α β D n) * hahnQ α β D n u := by
  have hneg := Phi3j_neg_M (-M + n) (-M) σ N (-μ) ⟨(α : ℤ) + β + 2 * n, by push_cast; linarith⟩
    ⟨(D : ℤ) + α, by push_cast; linarith⟩ ⟨(β : ℤ) + n, by push_cast; linarith⟩
    ⟨((D - u : ℕ) : ℤ), by push_cast; linarith⟩
  rw [neg_neg, neg_neg] at hneg
  have hs : sgn (-M + n - σ) = (-1 : ℝ) ^ (β + n) := by
    rw [show -M + (n : ℚ) - σ = ((β + n : ℕ) : ℚ) by push_cast; linarith, sgn_natCast]
  have hA := Phi3j_hahn (M := -M) (σ := σ) (N := N) (μ := -μ) (α := β) (β := α) (D := D)
    (by linarith) (by linarith) (by linarith) n (D - u) hn hu (by omega)
  rw [hneg, hs, hA]
  have hrefl := hahn_normalized_reflect α β D n u hn hu'
  have key : (-1 : ℝ) ^ (β + n) * (-1 : ℝ) ^ β * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add, ← pow_add, show β + n + β + n = 2 * (β + n) by ring, pow_mul]; simp
  linear_combination ((-1 : ℝ) ^ (β + n) * (-1 : ℝ) ^ β *
      Real.sqrt ((N : ℝ) / (2 * (((-M : ℚ) : ℝ) + n) + 1))) * hrefl +
    (Real.sqrt ((N : ℝ) / (2 * (((-M : ℚ) : ℝ) + n) + 1)) *
      Real.sqrt ((hahnW α β D u : ℝ) / hahnNorm α β D n) * hahnQ α β D n u) * key

/-- Chamber `σ > |M|`: Regge exchange, sign symmetry, then reflection. -/
lemma chamber_B (M σ N μ : ℚ) (α β D n u : ℕ) (hα : σ - M = α) (hβ : σ + M = β)
    (hD : N - σ - 1 = D) (hn : n ≤ D) (hu : jPlus N (-M) + mPlus σ (-μ) = ((D - u : ℕ) : ℚ))
    (hu' : u ≤ D) :
    Phi3j (σ + n) M σ N μ =
      (1 : ℝ) * Real.sqrt ((N : ℝ) / (2 * ((σ : ℝ) + n) + 1)) *
        Real.sqrt ((hahnW α β D u : ℝ) / hahnNorm α β D n) * hahnQ α β D n u := by
  have hneg := Phi3j_neg_M (σ + n) σ (-M) N (-μ) ⟨(α : ℤ) + β + 2 * n, by push_cast; linarith⟩
    ⟨(D : ℤ) + α, by push_cast; linarith⟩ ⟨(β : ℤ) + n, by push_cast; linarith⟩
    ⟨((D - u : ℕ) : ℤ), by push_cast; linarith⟩
  rw [neg_neg] at hneg
  have hs : sgn (σ + n - -M) = (-1 : ℝ) ^ (β + n) := by
    rw [show σ + (n : ℚ) - -M = ((β + n : ℕ) : ℚ) by push_cast; linarith, sgn_natCast]
  have hA := Phi3j_hahn (M := σ) (σ := -M) (N := N) (μ := -μ) (α := β) (β := α) (D := D)
    (by linarith) (by linarith) (by linarith) n (D - u) hn hu (by omega)
  rw [Phi3j_regge, hneg, hs, hA]
  have hrefl := hahn_normalized_reflect α β D n u hn hu'
  have key : (-1 : ℝ) ^ (β + n) * (-1 : ℝ) ^ β * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add, ← pow_add, show β + n + β + n = 2 * (β + n) by ring, pow_mul]; simp
  linear_combination ((-1 : ℝ) ^ (β + n) * (-1 : ℝ) ^ β *
      Real.sqrt ((N : ℝ) / (2 * ((σ : ℝ) + n) + 1))) * hrefl +
    (Real.sqrt ((N : ℝ) / (2 * ((σ : ℝ) + n) + 1)) *
      Real.sqrt ((hahnW α β D u : ℝ) / hahnNorm α β D n) * hahnQ α β D n u) * key

/-- **`eq:ExactHahnKernel` with `eq:HahnAllChamberPhase`, every chamber.**
For rational `M, σ` with `α = |M-σ|`, `β = |M+σ|` natural numbers, `L₀ = max(|M|,|σ|)`,
`D = N-L₀-1`, `0 ≤ n ≤ D`, and the lattice index `u = (N-1-|M-σ|-2μ)/2 ∈ {0,…,D}`:
`Φ_{L₀+n}^{M,σ}(x_u) = ε(M,σ) √(N/(2(L₀+n)+1)) √(w_H(u)/h_{H,n}) Q_n(u;α,β,D)`,
with `ε = (-1)^α` if `σ ≤ M` and `ε = 1` if `σ > M`. -/
theorem Phi3j_hahn_all_chambers (M σ N μ : ℚ) (α β D n u : ℕ) (hα : |M - σ| = α)
    (hβ : |M + σ| = β) (hD : N - max |M| |σ| - 1 = D) (hn : n ≤ D)
    (hu : (N - 1 - |M - σ| - 2 * μ) / 2 = u) (huD : u ≤ D) :
    Phi3j (max |M| |σ| + n) M σ N μ =
      (if σ ≤ M then (-1 : ℝ) ^ α else 1) *
        Real.sqrt ((N : ℝ) / (2 * (((max |M| |σ| : ℚ) : ℝ) + n) + 1)) *
        Real.sqrt ((hahnW α β D u : ℝ) / hahnNorm α β D n) * hahnQ α β D n u := by
  by_cases hA : |σ| ≤ M
  · have hM0 : 0 ≤ M := (abs_nonneg σ).trans hA
    have h1 : |M - σ| = M - σ := abs_of_nonneg (by linarith [le_abs_self σ])
    have h2 : |M + σ| = M + σ := abs_of_nonneg (by linarith [neg_abs_le σ])
    have hmax : max |M| |σ| = M := by rw [abs_of_nonneg hM0]; exact max_eq_left hA
    have hσM : σ ≤ M := (le_abs_self σ).trans hA
    rw [hmax] at hD ⊢
    rw [h1] at hα hu
    rw [h2] at hβ
    rw [ite_eq_left hσM]
    exact Phi3j_hahn hα hβ hD n u hn (by unfold jPlus mPlus; linarith [hu]) huD
  by_cases hDd : σ ≤ M
  · have hσneg : σ < 0 := by
      by_contra hc
      rw [not_lt] at hc
      exact hA (by rw [abs_of_nonneg hc]; exact hDd)
    have hMs : M < -σ := by
      have := not_le.mp hA
      rwa [abs_of_neg hσneg] at this
    have h1 : |M - σ| = M - σ := abs_of_nonneg (by linarith)
    have h2 : |M + σ| = -(M + σ) := abs_of_nonpos (by linarith)
    have hmax : max |M| |σ| = -σ := by
      rw [abs_of_neg hσneg]
      exact max_eq_right (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [hmax] at hD ⊢
    rw [h1] at hα hu
    rw [h2] at hβ
    rw [ite_eq_left hDd]
    exact chamber_D M σ N μ α β D n u hα hβ (by linarith) hn
      (by unfold jPlus mPlus; linarith [hu]) huD
  have hσM : M < σ := not_le.mp hDd
  have h1 : |M - σ| = σ - M := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
  rw [h1] at hα hu
  rw [ite_eq_right hDd]
  have hDq : (D : ℚ) = N - max |M| |σ| - 1 := by exact_mod_cast hD.symm
  by_cases hB : |M| < σ
  · have hσpos : 0 < σ := lt_of_le_of_lt (abs_nonneg M) hB
    have h2 : |M + σ| = σ + M := by
      rw [abs_of_nonneg (by linarith [neg_abs_le M] : 0 ≤ M + σ)]; ring
    have hmax : max |M| |σ| = σ := by
      rw [abs_of_pos hσpos]; exact max_eq_right hB.le
    rw [hmax] at hD hDq ⊢
    rw [h2] at hβ
    have hu2 : jPlus N (-M) + mPlus σ (-μ) = ((D - u : ℕ) : ℚ) := by
      rw [Nat.cast_sub huD, hDq]; unfold jPlus mPlus; linarith [hu]
    exact chamber_B M σ N μ α β D n u hα hβ (by linarith) hn hu2 huD
  · have hM : M < 0 := by
      by_contra hc
      rw [not_lt] at hc
      exact hB (by rw [abs_of_nonneg hc]; exact hσM)
    have hMn : |M| = -M := abs_of_neg hM
    have hσ2 : σ ≤ -M := by rw [not_lt, hMn] at hB; exact hB
    have h2 : |M + σ| = -(M + σ) := abs_of_nonpos (by linarith)
    have hmax : max |M| |σ| = -M := by
      rw [hMn]
      exact max_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [hmax] at hD hDq ⊢
    rw [h2] at hβ
    have hu2 : jPlus N σ + mPlus (-M) (-μ) = ((D - u : ℕ) : ℚ) := by
      rw [Nat.cast_sub huD, hDq]; unfold jPlus mPlus; linarith [hu]
    exact chamber_C M σ N μ α β D n u hα (by linarith) (by linarith) hn hu2 huD

/-- info: 'FormalResearch.Racah.Phi3j_hahn_all_chambers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_hahn_all_chambers

/-- `eq:HahnInvariantParameters`: `α_H + β_H = |M-σ| + |M+σ| = 2 max(|M|,|σ|) = 2L₀`. -/
theorem hahn_alpha_add_beta (M σ : ℚ) : |M - σ| + |M + σ| = 2 * max |M| |σ| := by
  rcases abs_cases (M - σ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases (M + σ) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rcases abs_cases M with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rcases abs_cases σ with ⟨h4, _⟩ | ⟨h4, _⟩ <;>
    rcases max_cases |M| |σ| with ⟨h5, _⟩ | ⟨h5, _⟩ <;> linarith

/-- **`eq:DualHahnSpectralCoordinate`**: `n(n+α_H+β_H+1) = L(L+1) - L₀(L₀+1)` for `α_H+β_H = 2L₀`,
`n = L-L₀`. -/
theorem dualHahn_spectral (L₀ L : ℚ) (n α β : ℕ) (hab : (α : ℚ) + β = 2 * L₀) (hn : L = L₀ + n) :
    (n : ℚ) * (n + α + β + 1) = L * (L + 1) - L₀ * (L₀ + 1) := by
  subst hn
  have : (α : ℚ) + β = 2 * L₀ := hab
  have h : (n : ℚ) + α + β + 1 = n + 2 * L₀ + 1 := by linarith
  rw [h]; ring

end FormalResearch.Racah
