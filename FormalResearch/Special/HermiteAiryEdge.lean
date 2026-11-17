module

public import FormalResearch.Special.HermiteAiryDatum

/-!
# Plancherel–Rotach edge asymptotics of the Hermite functions from the discrete-to-Airy theorem

**Statement formalised** (the Airy-edge part of `Weyl/free_fermion/paper/parts/hermite.tex`, Lemma `lem:PR`, case H;
Szegő, Orthogonal Polynomials, Thm 8.22.8; DLMF §18.15(v), §12.10).  Fix `x > 0` and put `S = x²/2`, `δ = S^{-1/3}`
(`δ³ = 2/x²`).  For the reflected Hermite chain `Y_k = φ_{-k}(x)` (so `n = -k`) on the lattice `q_k = (k - ½)δ³`
(`2n + 1 = x²·(-q)`, turning point `c = -1`, `2n+1 = x²`) there are *absolute* constants `r, δ₀, C, C_μ, ξ₀ > 0` such that for
`δ ≤ δ₀` (`x² ≥ 2/δ₀³`):

* window indices `J < N` with `q_k ∈ [-1-r, -1+r]` on `[J, N+1]` (i.e. `|(2n+1)/x² - 1| ≤ r`, a *macroscopic* window around
  the turn), `q_J ≈ -1-r`, `q_N ≥ -1 + r/4`, `q_{N+1} ≤ -1 + r/2`;
* `DaiFull` for the Hermite coefficients (unique recessive/dominant solutions, `|f - g Ai(X)| ≤ Cδ³ airyWt`, Casoratian `≥ δ/C`);
* real numbers `κ, μ` with
  `|φ_{-k}(x) - (κ g_k Ai(X_k) + μ g_k Bi(X_k))| ≤ C δ³ (|κ| airyWt(X_k) + |μ| airyBiWt(X_k))` for all `k ∈ [J, N+1]`,
  `|μ| ≤ C_μ √(x²+2) e^{-ξ₀/δ³}/δ` (exponentially small in `x²`),

where `X_k = δ⁻² ζ(q_k)`, `ζ = langerZeta hmU (-1)` is the Langer coordinate of the datum (`ζ ζ'² = Φ(u-1)`, closed form below)
and `g = langerAmp hmU hmA (-1)` the Langer amplitude.  So the relative error is `O(δ³) = O(1/x²) = O(1/n)` in the Olver weights
(`airyWt ≍ (1+|X|)^{-1/2}`), exactly the order of the Plancherel–Rotach Airy expansion, uniformly over the whole transition
region `|2n+1-x²| ≤ r x²`.

**Proof.** The chain is *exactly* the Jacobi chain of `hermite_datum` (`E = 0`, `hermite_row`); `discrete_airy_full_unif` (constants
depending only on the datum constants, which are absolute) gives `DaiFull`; `DaiFull.pointwise` with the a priori bound
`|φ_n(x)| ≤ √(2n+2)` (`abs_hermitePhi_le`, polynomial; Cramér's inequality is *not* needed) at the two forbidden-side sites `N, N+1`
(where `-N ≤ x²/2`) gives the decomposition.

**Not formalised (honest accounting).**
* **`κ` is unidentified**: the theorem says nothing about `κ = κ(x)`, in particular neither `κ ≠ 0` nor the size.  Numerically
  (mpmath 30 digits, scratch) `κ = S^{-1/12}(1+O(1/S))`, i.e. `φ_n(x) ≈ S^{-1/12} g Ai(X)`, `S=x²/2`:
  `κ = 0.6431, 0.5729, 0.5104` for `S = 200, 800, 3200`, ratio `4^{-1/12}`; this is numerical evidence only.  The `ℓ²`-mass
  argument of `hahn_chain_kappa` has no analogue (`∑_n φ_n(x)²` diverges at fixed `x`); the available normalisations are
  the transverse `∫ φ_n² dx = 1` (proved, `integral_hermitePhi_sq`) and the Mehler kernel `∑ t^n φ_n(x)² =
  e^{-x²(1-t)/(1+t)}/√(π(1-t²))` (not formalised); either needs control of the bulk (Liouville–Green) region or the
  Airy Laplace transform `∫ Ai² e^{-pX}` plus lattice sums.  Hence the amplitude bound `|φ_n| ≤ C n^{-1/12}` and the
  full Plancherel–Rotach statement (which carries the constant) are **not** obtained here.
* the bulk `|ζ_n| ≤ 1 - ε'` statement (needs a discrete Liouville–Green layer) and the explicit phase;
* negative `x` is not restated (parity `hermitePhi_neg`: `φ_n(-x) = (-1)^n φ_n(x)`, so `|φ_n(-x)| = |φ_n(x)|` and the signed chain
  is multiplied by `(-1)^k`);
* the identification of `ζ` with the closed form `(2/3)(-ζ)^{3/2} = (-q)arccos(1/√(-q)) - √(-q-1)` (`q < -1`) is only
  checked numerically (it reproduces the W1 phase `Φ_n = (2n+1)(2t_n - sin 2t_n)/4 - π/4`, `cos t_n = x/√(2n+1)`).

**Claim class: proved** (conclusions above, under the stated hypotheses); constants existential.
-/

@[expose] public section

open Set Metric FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **Plancherel–Rotach Airy edge for the Hermite functions** (see the module docstring). -/
theorem hermite_airy_edge : ∃ r δ0 C Cmu ξ0 : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
    ∀ x δ : ℝ, 0 < x → 0 < δ → δ ≤ δ0 → δ ^ 3 = 2 / x ^ 2 →
      ∃ J m N : ℤ, J < N ∧ J ≤ m ∧ m ≤ N ∧ N ≤ -1 ∧
        (∀ k ∈ Finset.Icc J (N + 1), dalQ (-δ ^ 3 / 2) δ k ∈ Icc (-1 - r) (-1 + r)) ∧
        -1 - r ≤ dalQ (-δ ^ 3 / 2) δ J ∧ dalQ (-δ ^ 3 / 2) δ J < -1 - r + δ ^ 3 ∧
        -1 ≤ dalQ (-δ ^ 3 / 2) δ m ∧ dalQ (-δ ^ 3 / 2) δ m < -1 + δ ^ 3 ∧
        -1 + r / 4 ≤ dalQ (-δ ^ 3 / 2) δ N ∧ dalQ (-δ ^ 3 / 2) δ (N + 1) ≤ -1 + r / 2 ∧
        DaiFull (hmCoefA δ) (hmCoefC δ) (turnX hmU (-1) (-δ ^ 3 / 2) δ)
          (fun k => langerAmp hmU hmA (-1) (dalQ (-δ ^ 3 / 2) δ k)) J m N δ C Cmu ξ0 ∧
        ∃ κ μ : ℝ,
          |μ| ≤ Cmu * √(x ^ 2 + 2) * Real.exp (-airyXi (turnX hmU (-1) (-δ ^ 3 / 2) δ N)) / δ ∧
          |μ| ≤ Cmu * √(x ^ 2 + 2) * Real.exp (-ξ0 / δ ^ 3) / δ ∧
          ∀ k ∈ Finset.Icc J (N + 1),
            |hermitePsi (-k) x -
                (κ * daoPhi (fun k => langerAmp hmU hmA (-1) (dalQ (-δ ^ 3 / 2) δ k))
                    (turnX hmU (-1) (-δ ^ 3 / 2) δ) k +
                  μ * daoPsi (fun k => langerAmp hmU hmA (-1) (dalQ (-δ ^ 3 / 2) δ k))
                    (turnX hmU (-1) (-δ ^ 3 / 2) δ) k)| ≤
              C * δ ^ 3 * (|κ| * airyWt (turnX hmU (-1) (-δ ^ 3 / 2) δ k) +
                |μ| * airyBiWt (turnX hmU (-1) (-δ ^ 3 / 2) δ k)) := by
  obtain ⟨Ku, m, aLo, aHi, KA, hKu, hm, haLo, haLH, hKA, hD⟩ := hermite_datum
  obtain ⟨r, δ0, C, Cmu, ξ0, hr, hrρ, hδ0, -, hC, hCmu, hξ0, H⟩ :=
    discrete_airy_full_unif (1 / 2) Ku m aLo aHi KA 0 (by norm_num) hKu hm haLo haLH hKA le_rfl
  refine ⟨r, δ0, C, Cmu, ξ0, hr, hrρ, hδ0, hC, hCmu, hξ0, ?_⟩
  intro x δ hx hδ hδδ0 hδx
  obtain ⟨J, m', N, hJN, hJm, hmN, hwin, hJ1, hJ2, hm1, hm2, hN1, hN2, hcoef⟩ :=
    H hD δ (-δ ^ 3 / 2) hδ hδδ0
  have hDF := hcoef (hmCoefA δ) (hmCoefC δ)
    (fun k _ => by simp [hmCoefA])
    (fun k _ => by simp [hmCoefC])
  have hδ3 : 0 < δ ^ 3 := by positivity
  -- `N ≤ -1`
  have hNneg : N ≤ -1 := by
    by_contra hcon
    have h0 : (0 : ℝ) ≤ N := by exact_mod_cast (by omega : (0 : ℤ) ≤ N)
    have : -1 + r / 2 ≥ dalQ (-δ ^ 3 / 2) δ (N + 1) := hN2
    simp only [dalQ] at this
    push_cast at this
    nlinarith [mul_nonneg h0 hδ3.le]
  -- `-N ≤ x²/2`
  have hNlow : ((-N : ℤ) : ℝ) ≤ x ^ 2 / 2 := by
    have h := hN1
    simp only [dalQ] at h
    have hx2 : δ ^ 3 * (x ^ 2 / 2) = 1 := by rw [hδx]; field_simp
    push_cast
    nlinarith
  have hrows : ∀ k ∈ Finset.Icc (J + 1) N, jac (hmCoefA δ) (hmCoefC δ) (hmY x) k = 0 := fun k hk =>
    hermite_row hx hδx k (by rw [Finset.mem_Icc] at hk; omega)
  have hYN : |hmY x N| ≤ √(x ^ 2 + 2) := by
    unfold hmY
    have hN' : 0 ≤ -N := by omega
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hN'
    rw [hn, hermitePsi_natCast]
    refine (abs_hermitePhi_le n x).trans (Real.sqrt_le_sqrt ?_)
    have : (n : ℝ) ≤ x ^ 2 / 2 := by
      have : ((n : ℤ) : ℝ) = ((-N : ℤ) : ℝ) := by rw [hn]
      push_cast at this hNlow ⊢
      linarith
    linarith
  have hYN1 : |hmY x (N + 1)| ≤ √(x ^ 2 + 2) := by
    unfold hmY
    have hN' : 0 ≤ -(N + 1) := by omega
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hN'
    rw [hn, hermitePsi_natCast]
    refine (abs_hermitePhi_le n x).trans (Real.sqrt_le_sqrt ?_)
    have : (n : ℝ) ≤ x ^ 2 / 2 := by
      have h1 : ((n : ℤ) : ℝ) = ((-(N + 1) : ℤ) : ℝ) := by rw [hn]
      push_cast at h1 hNlow ⊢
      linarith
    linarith
  obtain ⟨κ, μ, hμ, hY⟩ := DaiFull.pointwise hDF (hmY x) (√(x ^ 2 + 2)) hrows hYN hYN1
  have hxi : ξ0 / δ ^ 3 ≤ airyXi (turnX hmU (-1) (-δ ^ 3 / 2) δ N) := hDF.1
  have hμ2 : |μ| ≤ Cmu * √(x ^ 2 + 2) * Real.exp (-ξ0 / δ ^ 3) / δ := by
    refine hμ.trans ?_
    gcongr
    have e : -ξ0 / δ ^ 3 = -(ξ0 / δ ^ 3) := neg_div _ _
    rw [e]
    linarith
  exact ⟨J, m', N, hJN, hJm, hmN, hNneg, hwin, hJ1, hJ2, hm1, hm2, hN1, hN2, hDF, κ, μ, hμ, hμ2, hY⟩

/-- info: 'FormalResearch.Special.hermite_airy_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hermite_airy_edge

end FormalResearch.Special
