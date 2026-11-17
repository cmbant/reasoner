module

public import FormalResearch.Special.DiscreteAiryLimitChains3j

/-!
# The Airy limit for the actual Wigner `3j` chain at the lattice nodes (Weyl P3, `thm:hahnAiryConnection`)

Composition of `discrete_airy_hahn_racah` (the discrete-to-Airy limit for the closed-form Hahn coefficients) with the
identification `hahn_class_chain` (the actual natural-gauge `3j` chain is a solution of exactly that recurrence) and the
Gauss-weight bound `hahn_chain_sq_le` (condition `(R)`, `Ŷ² ≤ N`).

## Result (proved)

`hahn_chain_airy`: fix integers `M, σ`, a rational shape `x ∈ (0,1)` and `A₀ > 0`.  There are constants
`r, δ₀, C, C_osc, C_top, W, C_μ, ξ₀, D > 0` (depending on `M, σ, x, A₀` only) such that for every integer `N > max(|M|,|σ|)`
and every lattice node `x = x_n = xLat M σ N n` (`n < N - max(|M|,|σ|)`) with `N⁻¹ ≤ δ₀³`, writing `δ = N^{-1/3}`
(`h = N⁻¹ = δ³`, sites `q_k = (k+½)h`), there are window indices `1 ≤ J ≤ m ≤ N_w` (positions exported as in
`discrete_airy_hahn_racah`) and `κ, μ ∈ ℝ` with `|μ| ≤ C_μ √N e^{-ξ(X_{N_w})}`, `ξ₀/δ³ ≤ ξ(X_{N_w})` and

* `|Ŷ_k - κ ψ_k| ≤ C δ³ |κ| W + C_osc |μ|/δ` on `[J, m]`,
* `|Ŷ_k - κ ψ_k| ≤ C δ³ |κ| ψ_k + C_top |μ|/(δ airyWt X_k)` on `[m, N_w + 1]`,

for the actual natural-gauge kernel `Ŷ_k = √(2k+1) Φ_k^{M,σ}(x; 1/N)` of the Wigner `3j` symbol, `ψ_k = g(q_k) Ai(X_k)`,
`X_k = h^{-2/3} ζ(q_k)`, `ζ` the Langer coordinate of `A(q) = ½ √(1-q²)`, `u(q) = x/√(1-q²)` at the turn `q_*² = 1 - x²`.
This is `thm:general-rank-airy`(i) / `eq:airyfactor` for the Hahn chain, with the `3j` input `(R)` proved (not assumed).

## Not formalised

`κ` is produced by the recessive selection and is not identified (the Darboux/Wigner-`d` normalisation); `κ ≠ 0` is not part of
this theorem (for `τ = +1` it is `hahn_chain_kappa`, `DiscreteAiryKappaMain`, `|κ| ≥ κ_min > 0` with `κ_min` independent of `N`); the node `x_n` has to equal the fixed shape `x` (the theorem is uniform in `N` for each fixed `x`, but it does not
itself assert that infinitely many `N` admit such a node, and for a compact family of `x` the constants of this recessive statement are not shown
uniform; the full unified statement is uniform in `x ∈ [x₀, x₁]`, `hahn_chain_airy_full_unif`, `DiscreteAiryUnifHahn`).  That infinitely many `N` do is `hahn_node_exists` (`DiscreteAiryLimitChains2Nodes`): `x = p/q` with `p+q` odd
or `M+σ` odd (e.g. `M = σ = 0`, `x = 1/2`, `N = 4t+2`, `n = 3t+1`), with the exact obstruction `hahn_node_obstruction`
(`M = σ = 0`, `x = 1/3` has no node at all); the combined statement is `hahn_chain_airy_infinite`.  Integer data only
here (half-integer: `DiscreteAiryLimitChains2Half3j`); `x ∈ (-1,0)` is the `τ = -1` twist (`hahn_chain_airy_neg`).  Not
formalised in this module: the non-recessive `Ai`/`Bi` pair and the oscillatory side `X < -A₀` (for fixed `x` at a node they are
`hahn_chain_airy_full` etc. in `DiscreteAiryPhysChains`, up to `κ`); the Hahn/Racah instance of the second-order bracket (S4; the abstract second-order bracket is `airy2_turn_full`, `DiscreteAirySecond*`).
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma specAdm_int (M σ N : ℤ) (h : max |M| |σ| < N) : SpecAdm (M : ℚ) (σ : ℚ) (N : ℚ) := by
  have e : max |(M : ℚ)| |(σ : ℚ)| = ((max |M| |σ| : ℤ) : ℚ) := by push_cast; rfl
  have := (hahn_tri_iff (max |M| |σ|) M σ N).2
    ⟨le_max_left _ _, le_max_right _ _, by omega⟩
  unfold SpecAdm
  rw [e]
  exact this

/-- **`(R)` for the `3j` chain, all indices**: at every node of an admissible integer system, `|Ŷ_k| ≤ √N` for every `k ∈ ℤ`. -/
theorem hahn_chain_abs_le (M σ N : ℤ) (hN : max |M| |σ| < N) (n : ℕ) (hn : (n : ℤ) < N - max |M| |σ|) (k : ℤ) :
    |hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) k| ≤ Real.sqrt (N : ℝ) := by
  have hN0 : (0 : ℤ) < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  by_cases hk : |M| ≤ k ∧ |σ| ≤ k ∧ k ≤ N - 1
  · set L0 : ℤ := max |M| |σ| with hL0
    have hlo : L0 ≤ k := max_le hk.1 hk.2.1
    set K : ℕ := (N - L0).toNat with hKdef
    have hK : (K : ℚ) = (N : ℚ) - max |(M : ℚ)| |(σ : ℚ)| := by
      have e : max |(M : ℚ)| |(σ : ℚ)| = (L0 : ℚ) := by rw [hL0]; push_cast; rfl
      rw [e]
      have : (K : ℤ) = N - L0 := Int.toNat_of_nonneg (by omega)
      have h2 : ((K : ℤ) : ℚ) = ((N - L0 : ℤ) : ℚ) := by rw [this]
      push_cast at h2
      exact h2
    have hnK : n < K := by omega
    set i : ℕ := (k - L0).toNat with hi
    have hiK : i < K := by omega
    have hcast : (max |(M : ℚ)| |(σ : ℚ)| + (i : ℚ)) = (k : ℚ) := by
      have e : max |(M : ℚ)| |(σ : ℚ)| = (L0 : ℚ) := by rw [hL0]; push_cast; rfl
      have h3 : (i : ℤ) = k - L0 := Int.toNat_of_nonneg (by omega)
      have h4 : ((i : ℤ) : ℚ) = ((k - L0 : ℤ) : ℚ) := by rw [h3]
      push_cast at h4
      rw [e, h4]; ring
    have hsq := hahn_chain_sq_le (specAdm_int M σ N hN) (by exact_mod_cast hN0) hK hnK hiK
    rw [hcast] at hsq
    have hY : (hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) k) ^ 2 =
        (2 * ((k : ℚ) : ℝ) + 1) * PhiX (k : ℚ) (M : ℚ) (σ : ℚ) (N : ℚ) (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) ^ 2 := by
      unfold hahn3jY
      rw [mul_pow, Real.sq_sqrt (by
        have : (1 : ℝ) ≤ 2 * (k : ℝ) + 1 := by
          have : (0 : ℝ) ≤ k := by
            have : (0 : ℤ) ≤ k := le_trans (le_trans (abs_nonneg M) hk.1) le_rfl
            exact_mod_cast this
          linarith
        linarith)]
      push_cast; ring
    exact Real.abs_le_sqrt (by rw [hY]; push_cast at hsq ⊢; exact hsq)
  · rw [hahn_chain_support M σ N _ k hk]
    simp

/-- **The discrete-to-Airy limit for the actual `3j` chain at the lattice nodes.**  See the module docstring. -/
theorem hahn_chain_airy (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N → (n : ℤ) < N - max |M| |σ| →
        xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x → 1 / (N : ℝ) ≤ δ0 ^ 3 →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ^ 3 = 1 / (N : ℝ) ∧ ∃ J m Nw : ℤ, 1 ≤ J ∧ J ≤ m ∧ m ≤ Nw ∧
          (∀ k ∈ Finset.Icc J (Nw + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - Real.sqrt (1 - (x : ℝ) ^ 2)| ≤ r) ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) - D * δ ^ 2 ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((J : ℝ) + 1 / 2) * δ ^ 3 ≤ Real.sqrt (1 - (x : ℝ) ^ 2) ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((m : ℝ) + 1 / 2) * δ ^ 3 < Real.sqrt (1 - (x : ℝ) ^ 2) + δ ^ 3 ∧
          turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ J ≤ -A0 ∧
          ξ0 / δ ^ 3 ≤ airyXi (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ Nw) ∧
          ∃ κ μ : ℝ, |μ| ≤ Cmu * Real.sqrt (N : ℝ) *
              Real.exp (-airyXi (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ Nw)) ∧
            (∀ k ∈ Finset.Icc J m, |hahn3jY M σ N x k -
                κ * turnPsi (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k| ≤
              C * δ ^ 3 * |κ| * W + Cosc * (|μ| / δ)) ∧
            (∀ k ∈ Finset.Icc m (Nw + 1), |hahn3jY M σ N x k -
                κ * turnPsi (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k| ≤
              C * δ ^ 3 * |κ| * turnPsi (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k +
                Ctop * |μ| / δ / airyWt (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k)) := by
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
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, -, hδ0, -, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    discrete_airy_hahn_racah (P := 1) (Q := 0) (by norm_num) (by norm_num) (M : ℝ) (σ : ℝ) 1 (x : ℝ)
      (Real.sqrt (1 - (x : ℝ) ^ 2)) hqs (by norm_num) (by linarith) (by rw [hq2]; nlinarith)
      (by simp) hturn A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro N n hN hn hxn hNδ
  have hN0 : (0 : ℤ) < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  set δ : ℝ := (1 / (N : ℝ)) ^ ((1 : ℝ) / 3) with hδdef
  have hδ0' : 0 < δ := Real.rpow_pos_of_pos (by positivity) _
  have hδ3 : δ ^ 3 = 1 / (N : ℝ) := by
    rw [hδdef, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hδle : δ ≤ δ0 := by
    by_contra hcon
    push Not at hcon
    have : δ0 ^ 3 < δ ^ 3 := by gcongr
    linarith
  obtain ⟨J, m, Nw, hJ, hJm, hmN, hwin, h1, h2, h3, h4, h5, Hc⟩ := H δ hδ0' hδle
  obtain ⟨hxi, -, -, -, HY⟩ := Hc
  have hrows : ∀ k ∈ Finset.Icc (J + 1) Nw,
      jac (hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) (δ ^ 3)) (hahn3jY M σ N x) k = 0 := by
    intro k hk
    have hk1 : 1 ≤ k := by rw [Finset.mem_Icc] at hk; omega
    have := hahn_class_chain M σ N x hN0 k hk1
    rw [← hδ3] at this
    exact this
  have hbd : ∀ k : ℤ, |hahn3jY M σ N x k| ≤ Real.sqrt (N : ℝ) := by
    intro k
    rw [← hxn]
    exact hahn_chain_abs_le M σ N hN n hn k
  obtain ⟨κ, μ, hμ, hlow, hup⟩ := HY (hahn3jY M σ N x) (Real.sqrt (N : ℝ)) hrows (hbd _) (hbd _)
  exact ⟨δ, hδ0', hδle, hδ3, J, m, Nw, hJ, hJm, hmN, hwin, h1, h2, h3, h4, h5, hxi, κ, μ, hμ, hlow, hup⟩

/-- info: 'FormalResearch.Special.hahn_chain_airy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_chain_airy

/-- info: 'FormalResearch.Special.hahn_chain_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_chain_abs_le

end FormalResearch.Special
