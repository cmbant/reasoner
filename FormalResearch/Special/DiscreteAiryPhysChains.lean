module

public import FormalResearch.Special.DiscreteAiryPhysHahn
public import FormalResearch.Special.DiscreteAiryLimitChains2Nodes
public import FormalResearch.Special.DiscreteAiryLimitChains2Twist

/-!
# The actual Wigner `3j` chain: the unified Airy matching on the whole macroscopic window

`hahn_chain_airy_full` is `thm:hahnAiryConnection`(i) (up to the value of `κ`; `κ ≠ 0` for `τ = +1` is `hahn_chain_kappa`, `DiscreteAiryKappaMain`) for the actual natural-gauge `3j` kernel
`Ŷ_k = √(2k+1) Φ_k^{M,σ}(x; 1/N)` at a lattice node `x_n = x`: composition of `airy_full_compose` (`DiscreteAiryPhysHahn`) with
the identification `hahn_class_chain` (the actual chain solves every row `k ≥ 1` of the closed-form recurrence) and the Gauss-weight
bound `hahn_chain_abs_le` (`|Ŷ_k| ≤ √N`, condition `(R)`).

**Result (proved).**  Fix integers `M, σ` and a rational `x ∈ (0,1)`.  There are `r, δ₀, C, Cmu, ξ₀ > 0` (depending on `M, σ, x` only; for the uniform version, constants depending on `M, σ` and a compact range `x ∈ [x₀, x₁] ⊂ (0,1)` only, see `hahn_chain_airy_full_unif`, `DiscreteAiryUnifHahn`)
such that for every admissible node `(N, n)` with `x_n = x` and `1/N ≤ δ₀³`, `δ = N^{-1/3}` (`h = 1/N`, `q_k = (k+½)h`,
`q_* = √(1-x²)`), there are indices `1 ≤ J < N_w`, `J ≤ m ≤ N_w` with `q_J ∈ [q_* - r, q_* - r + h)`, `q_m ∈ [q_*, q_*+h)`,
`q_{N_w} ≥ q_* + r/4`, `q_{N_w+1} ≤ q_* + r/2`, and `κ, μ` with `|μ| ≤ Cmu √N e^{-ξ₀ N}/δ` such that on the **whole macroscopic window**
`k ∈ [J, N_w+1]` (`q_k ∈ [q_* - r, q_* + r/2]`):
`|Ŷ_k - (κ g Ai(X_k) + μ g Bi(X_k))| ≤ C δ³ (|κ| airyWt(X_k) + |μ| airyBiWt(X_k))`,
`X_k = δ^{-2} ζ(q_k)`, `ζ` the Langer coordinate of `A(q) = ½√(1-q²)`, `u(q) = x/√(1-q²)`, `g` the Langer amplitude.  The
`DaiFull` for the closed-form recurrence (unique recessive `f` and dominant `F₂`, `Ŷ = κ f + μ F₂`) is part of `AiryFullAt`.

Also `τ = -1` (`x ∈ (-1, 0)`, twisted chain `(-1)^k Ŷ_k`) and the versions along infinitely many `N` (`hahn_node_exists`).

**Numerics (mpmath, 50 digits, scratch, not a Lean claim).**  `M = σ = 0`, `x = 1/2`, `N = 4t+2`, `t = 25, 50, 100, 200, 400`
(`n = 3t+1`, `N = 102, 202, 402, 802, 1602`), `Ŷ` from the hard edge `Ŷ_{N-1} = 1`, `r = q_*/4`: least-squares fit of `κ, μ` on
`q_k ∈ [q_* - r, q_* + r/2]` (`X_J` down to `-48`) gives `sup |Ŷ - κ g Ai - μ g Bi|/(δ³(|κ| airyWt + |μ| airyBiWt)) =
0.144, 0.211, 0.241, 0.247, 0.268` (bounded) and `|μ/κ| = 2·10⁻⁹, 3·10⁻¹⁷, 1·10⁻³¹, 5·10⁻⁵⁹, 7·10⁻¹¹⁶` (exponentially small in `N`).  The numerical window uses `r = q_*/4`
(for `x = 1/2`, `q_* + r/2 = 9q_*/8 ≈ 0.97 < 1`, so the sites lie in the Hahn domain); the Lean statement only provides some `r ≤ q_*/4` (`q_* + r₀ < 1` is not
guaranteed at `r₀ = q_*/4`, e.g. `x = 1/2`), so the numerics probe a window at least as large as the proved one.

**Not formalised.**  The value of `κ` (Darboux/Wigner-`d`; `|κ| ≥ κ_min > 0` uniformly in `N` is `hahn_chain_kappa`, `DiscreteAiryKappaMain`, numerically
`|κ| = √2 N^{1/6}`; `κ ≠ 0` for `τ = -1` is open); uniformity of `r, δ₀, C, Cmu, ξ₀` in `x` for the `κ` statements and as `x → 0, 1` (for `x ∈ [x₀, x₁]` it is `hahn_chain_airy_full_unif`, `DiscreteAiryUnifHahn`, which supersedes
this statement for the shape); the radius is the
(existential) radius `r ≤ q_*/4` of the Langer chart, not `q_*/4`; half-integer data; the Hahn/Racah instance of the second-order bracket (S4; the abstract second-order bracket is `airy2_turn_full`, `DiscreteAirySecond*`).
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **The unified Airy matching for the actual `3j` chain at lattice nodes** (`τ = +1`, `x ∈ (0,1)`).  The constants depend on `(M, σ, x)`: for `x` in a compact range
`[x₀, x₁] ⊂ (0,1)`, with constants depending only on `(M, σ, x₀, x₁)` and every lattice node, see `hahn_chain_airy_full_unif` (`DiscreteAiryUnifHahn`). -/
theorem hahn_chain_airy_full (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N → (n : ℤ) < N - max |M| |σ| →
        xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x → 1 / (N : ℝ) ≤ δ0 ^ 3 →
        AiryFullAt 1 0 1 (x : ℝ) (Real.sqrt (1 - (x : ℝ) ^ 2)) (M : ℝ) (σ : ℝ) (hahn3jY M σ N x)
          (Real.sqrt (N : ℝ)) r δ0 C Cmu ξ0 (1 / (N : ℝ)) := by
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hx1' : (x : ℝ) < 1 := by exact_mod_cast hx1
  have hq2 : Real.sqrt (1 - (x : ℝ) ^ 2) ^ 2 = 1 - (x : ℝ) ^ 2 := Real.sq_sqrt (by nlinarith)
  have hqs : 0 < Real.sqrt (1 - (x : ℝ) ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hturn : Phi 1 0 1 (x : ℝ) (Real.sqrt (1 - (x : ℝ) ^ 2) ^ 2) = 0 := by
    unfold Phi etilde
    rw [hq2]
    have : (1 - 1 * (1 - (x : ℝ) ^ 2)) * (1 - 0 * (1 - (x : ℝ) ^ 2)) = (x : ℝ) ^ 2 := by ring
    rw [this, Real.sqrt_sq hx0'.le]
    simp
  obtain ⟨r, δ0, C, Cmu, ξ0, hr, -, hδ0, hC, hCmu, hξ0, H⟩ :=
    airy_full_compose (P := 1) (Q := 0) (by norm_num) (by norm_num) (M : ℝ) (σ : ℝ) 1 (x : ℝ)
      (Real.sqrt (1 - (x : ℝ) ^ 2)) hqs (by norm_num) (by linarith) (by rw [hq2]; nlinarith)
      (by simp) hturn
  refine ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, ?_⟩
  intro N n hN hn hxn hNδ
  have hN0 : (0 : ℤ) < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  refine H (1 / (N : ℝ)) _ _ (by positivity) hNδ (fun k hk => hahn_class_chain M σ N x hN0 k hk) ?_
  intro k
  rw [← hxn]
  exact hahn_chain_abs_le M σ N hN n hn k

/-- **The same for `τ = -1`** (`x ∈ (-1, 0)`, the twisted chain `(-1)^k Ŷ_k`). -/
theorem hahn_chain_airy_full_neg (M σ : ℤ) (x : ℚ) (hx0 : x < 0) (hx1 : -1 < x) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N → (n : ℤ) < N - max |M| |σ| →
        xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x → 1 / (N : ℝ) ≤ δ0 ^ 3 →
        AiryFullAt 1 0 (-1) (x : ℝ) (Real.sqrt (1 - (x : ℝ) ^ 2)) (M : ℝ) (σ : ℝ)
          (fun j => (-1 : ℝ) ^ j * hahn3jY M σ N x j) (Real.sqrt (N : ℝ)) r δ0 C Cmu ξ0 (1 / (N : ℝ)) := by
  have hx0' : (x : ℝ) < 0 := by exact_mod_cast hx0
  have hx1' : (-1 : ℝ) < x := by exact_mod_cast hx1
  have hq2 : Real.sqrt (1 - (x : ℝ) ^ 2) ^ 2 = 1 - (x : ℝ) ^ 2 := Real.sq_sqrt (by nlinarith)
  have hqs : 0 < Real.sqrt (1 - (x : ℝ) ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  obtain ⟨r, δ0, C, Cmu, ξ0, hr, -, hδ0, hC, hCmu, hξ0, H⟩ :=
    airy_full_compose (P := 1) (Q := 0) (by norm_num) (by norm_num) (M : ℝ) (σ : ℝ) (-1) (x : ℝ)
      (Real.sqrt (1 - (x : ℝ) ^ 2)) hqs (by norm_num) (by linarith) (by rw [hq2]; nlinarith) (by simp)
      (hahn_turn_neg hx0' hx1')
  refine ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, ?_⟩
  intro N n hN hn hxn hNδ
  have hN0 : (0 : ℤ) < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  refine H (1 / (N : ℝ)) _ _ (by positivity) hNδ (fun k hk => hahn_class_chain_neg M σ N x hN0 k hk) ?_
  intro k
  have h1 : |(-1 : ℝ) ^ k| = 1 := by simp [abs_zpow]
  rw [abs_mul, h1, one_mul, ← hxn]
  exact hahn_chain_abs_le M σ N hN n hn k

/-- info: 'FormalResearch.Special.hahn_chain_airy_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_airy_full

/-- info: 'FormalResearch.Special.hahn_chain_airy_full_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_airy_full_neg

/-- Existence of arbitrarily large `N` with `1/N ≤ δ₀³` and a node `x_n = x` (`hahn_node_exists`), `x ∈ (0, 1)` rational with the
parity condition. -/
lemma dap_nodes_large (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1)
    (hpar : Odd (x.num + (x.den : ℤ)) ∨ Even (1 + |M + σ|)) (δ0 : ℝ) (hδ0 : 0 < δ0) (N0 : ℕ) :
    ∃ (N : ℤ) (n : ℕ), (N0 : ℤ) < N ∧ max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧
      xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x ∧ 1 / (N : ℝ) ≤ δ0 ^ 3 := by
  have hnum : 0 < x.num := Rat.num_pos.2 hx0
  have hlt : x.num < (x.den : ℤ) := by
    have h1 : (x.num : ℚ) / (x.den : ℚ) < 1 := by rwa [Rat.num_div_den]
    have h2 : (x.num : ℚ) < (x.den : ℚ) := by
      rwa [div_lt_one (by exact_mod_cast x.den_pos)] at h1
    exact_mod_cast h2
  obtain ⟨T, hT⟩ := exists_nat_gt (1 / δ0 ^ 3)
  obtain ⟨N, n, hN0, hN1, hN2, hxn⟩ :=
    hahn_node_exists M σ x.num x.den (by omega) hlt hpar (max N0 T)
  have hxn' : xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x := by
    rw [hxn]; exact_mod_cast Rat.num_div_den x
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℤ) < N := by have := le_max_left N0 T; omega
    exact_mod_cast this
  have hNT : (T : ℝ) < N := by
    have : (T : ℤ) < N := by have := le_max_right N0 T; omega
    exact_mod_cast this
  have hδ : 1 / (N : ℝ) ≤ δ0 ^ 3 := by
    have h3 : 0 < δ0 ^ 3 := by positivity
    rw [div_le_iff₀ hNpos]
    have := (div_lt_iff₀ h3).1 hT
    nlinarith
  exact ⟨N, n, by have := le_max_left N0 T; omega, hN1, hN2, hxn', hδ⟩

/-- **The unified Airy matching along an infinite sequence `N → ∞`** (`hahn_chain_airy_full` + `hahn_node_exists`): for integers
`M, σ` and a rational `x ∈ (0,1)` with `Odd (num + den) ∨ Even (1 + |M+σ|)` (exactly the `x` that occur as nodes, `hahn_node_iff`),
e.g. `M = σ = 0`, `x = 1/2`, `N = 4t+2`. -/
theorem hahn_chain_airy_full_infinite (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1)
    (hpar : Odd (x.num + (x.den : ℤ)) ∨ Even (1 + |M + σ|)) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ N0 : ℕ, ∃ (N : ℤ) (n : ℕ), (N0 : ℤ) < N ∧ max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧
        xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x ∧ 1 / (N : ℝ) ≤ δ0 ^ 3 ∧
        AiryFullAt 1 0 1 (x : ℝ) (Real.sqrt (1 - (x : ℝ) ^ 2)) (M : ℝ) (σ : ℝ) (hahn3jY M σ N x)
          (Real.sqrt (N : ℝ)) r δ0 C Cmu ξ0 (1 / (N : ℝ)) := by
  obtain ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, H⟩ := hahn_chain_airy_full M σ x hx0 hx1
  refine ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, fun N0 => ?_⟩
  obtain ⟨N, n, h1, h2, h3, h4, h5⟩ := dap_nodes_large M σ x hx0 hx1 hpar δ0 hδ0 N0
  exact ⟨N, n, h1, h2, h3, h4, h5, H N n h2 h3 h4 h5⟩

/-- **The same for `τ = -1`** (`x ∈ (-1, 0)`, twisted chain). -/
theorem hahn_chain_airy_full_neg_infinite (M σ : ℤ) (x : ℚ) (hx0 : x < 0) (hx1 : -1 < x)
    (hpar : Odd (x.num + (x.den : ℤ)) ∨ Even (1 + |M + σ|)) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ N0 : ℕ, ∃ (N : ℤ) (n : ℕ), (N0 : ℤ) < N ∧ max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧
        xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x ∧ 1 / (N : ℝ) ≤ δ0 ^ 3 ∧
        AiryFullAt 1 0 (-1) (x : ℝ) (Real.sqrt (1 - (x : ℝ) ^ 2)) (M : ℝ) (σ : ℝ)
          (fun j => (-1 : ℝ) ^ j * hahn3jY M σ N x j) (Real.sqrt (N : ℝ)) r δ0 C Cmu ξ0 (1 / (N : ℝ)) := by
  obtain ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, H⟩ := hahn_chain_airy_full_neg M σ x hx0 hx1
  refine ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, fun N0 => ?_⟩
  have hnum : x.num < 0 := Rat.num_neg.2 hx0
  have hlt : -(x.den : ℤ) < x.num := by
    have h1 : -1 < (x.num : ℚ) / (x.den : ℚ) := by rwa [Rat.num_div_den]
    have hd : (0 : ℚ) < (x.den : ℚ) := by exact_mod_cast x.den_pos
    have h2 : -(x.den : ℚ) < (x.num : ℚ) := by
      rw [lt_div_iff₀ hd] at h1; linarith
    exact_mod_cast h2
  obtain ⟨T, hT⟩ := exists_nat_gt (1 / δ0 ^ 3)
  obtain ⟨N, n, hN0, hN1, hN2, hxn⟩ :=
    hahn_node_exists M σ x.num x.den hlt (by omega) hpar (max N0 T)
  have hxn' : xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x := by
    rw [hxn]; exact_mod_cast Rat.num_div_den x
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℤ) < N := by have := le_max_left N0 T; omega
    exact_mod_cast this
  have hNT : (T : ℝ) < N := by
    have : (T : ℤ) < N := by have := le_max_right N0 T; omega
    exact_mod_cast this
  have hδ : 1 / (N : ℝ) ≤ δ0 ^ 3 := by
    have h3 : 0 < δ0 ^ 3 := by positivity
    rw [div_le_iff₀ hNpos]
    have := (div_lt_iff₀ h3).1 hT
    nlinarith
  exact ⟨N, n, by have := le_max_left N0 T; omega, hN1, hN2, hxn', hδ, H N n hN1 hN2 hxn' hδ⟩

/-- info: 'FormalResearch.Special.hahn_chain_airy_full_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_airy_full_infinite

/-- info: 'FormalResearch.Special.hahn_chain_airy_full_neg_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_airy_full_neg_infinite

/-- **The model case of the numerics**: `M = σ = 0`, `x = 1/2` (nodes `N = 4t+2`, `n = 3t+1`), `q_* = √3/2`. -/
theorem hahn_chain_airy_full_half :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ N0 : ℕ, ∃ (N : ℤ) (n : ℕ), (N0 : ℤ) < N ∧ max |(0 : ℤ)| |(0 : ℤ)| < N ∧ (n : ℤ) < N - max |(0 : ℤ)| |(0 : ℤ)| ∧
        xLat ((0 : ℤ) : ℚ) ((0 : ℤ) : ℚ) (N : ℚ) n = 1 / 2 ∧ 1 / (N : ℝ) ≤ δ0 ^ 3 ∧
        AiryFullAt 1 0 1 (((1 : ℚ) / 2 : ℚ) : ℝ) (Real.sqrt (1 - (((1 : ℚ) / 2 : ℚ) : ℝ) ^ 2)) ((0 : ℤ) : ℝ) ((0 : ℤ) : ℝ)
          (hahn3jY 0 0 N (1 / 2)) (Real.sqrt (N : ℝ)) r δ0 C Cmu ξ0 (1 / (N : ℝ)) := by
  have h1 : ((1 : ℚ) / 2).num = 1 := by decide +kernel
  have h2 : ((1 : ℚ) / 2).den = 2 := by decide +kernel
  exact hahn_chain_airy_full_infinite 0 0 (1 / 2) (by norm_num) (by norm_num)
    (Or.inl (by rw [h1, h2]; decide))

/-- info: 'FormalResearch.Special.hahn_chain_airy_full_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_airy_full_half

end FormalResearch.Special
