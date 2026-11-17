module

public import FormalResearch.Special.DiscreteAiryKappaSharpFinalNode

/-!
# The sharp constant `κ² δ → 2` for the actual `3j` chain (plan K1, sharp constant)

Fix integers `M, σ` and a rational `x ∈ (0,1)`; `δ³ = 1/N`.  `hahn_chain_kappa_sharp` extends `hahn_chain_kappa_order` (`DiscreteAiryKappaOrder`): for every
`τ > 0` there is `ε₁ > 0` such that at every lattice node with `1/N ≤ ε₁` the matching `Ŷ = κ g Ai + μ g Bi + O(δ³)` of `hahn_chain_airy_full` holds with

`|κ² δ - 2| ≤ τ`, i.e. `κ² = 2 N^{1/3} (1 + o(1))`, `|κ| = √2 N^{1/6} (1 + o(1))`.

Proof (modules `DiscreteAiryKappaSharp*`): the Ermakov amplitude `I_k(Ŷ)` of the band `α ≥ A` is `κ²δ/π (1 + O(δ))` at the band end (Airy matching, chart identity
`g² = 2√(-ζ)/α`, `ksf_match`), constant along the band up to `O(S)` (`hahn3j_band_clean`), the band mass is `I·Σ P/2 = I (π/2) N (1 - O(A + η))`
(`ksg_sv`), and the Gauss weight `N = ΣŶ²` is the sum of the band (`≤ N`), the left part (`≲ η N/A`, `ksl_left`) and the zone beyond the band (`≲ N √A`, `ksz_zone`);
`ksa_combine` gives `|κ²δ/2 - 1| ≤ 2 max(θ₁, θ₂)`, `θ = O(A + η) + O_A(δ)`; `A = η^{1/2} → 0` after `N → ∞`.

**Claim class: proved**, all constants existential (depending on `M, σ, x`); the rate is `|κ² δ - 2| ≤ C₁ A + C₂(A) δ` for every `A ∈ (0, A₀]`.

The chain is `Ŷ = hahn3jY M σ N x` (`√(2k+1) Φ_k^{M,σ}(x; 1/N)`, the Regge-midpoint `3j` kernel, natural gauge, hard edge at `k = N`) at a lattice node
`xLat M σ N n = x`.  Quantifier order: `r, ε₀, C, C_μ, ξ₀` depend on `(M, σ, x)`; `ε₁` on `(M, σ, x, τ)`; everything else (`δ, J, m, N_w, κ, μ`) is
produced at the node, and `κ, μ` are the Airy/Bi coefficients of the pointwise matching of `Ŷ` on the window (pinned to relative accuracy `Cδ³`).

**Numerics** (not a Lean claim; mpmath 40 digits; exact chain from the closed-form recurrence `hahn_class_chain` run from the hard edge and normalised by
`Σ Ŷ² = N`, checked against `wigner_3j` for `N = 12`; Langer chart `ζ, g` of `u = x/√(1-q²)`, `A = ½√(1-q²)`; least-squares fit of `Ŷ` to `κ g Ai + μ g Bi`
on `-6 ≤ X ≤ 2`): `κ² δ` equals `2.00006, 2.000005, 2.000000, 2.000000` for `(M, σ, x) = (1, 0, ½)`, `N = 200, 800, 3200, 12800`; `2.0017, 2.00027, 2.000038,
2.000006` for `(2, -1, 3/5)` (same `N`); `2.0005, 2.00006, 2.000007, 2.000001` for `(3, 0, ⅓)` (`N = 201, 801, 3201, 12801`); `1.9991, 1.99993, 1.99999,
1.999999` for `(0, 0, 9/10)` (`N = 210, 810, 3210, 12810`); `κ²/(2N^{1/3}) → 1` accordingly.  The observed error is roughly `δ⁴`.  At `N = 3200`,
`(1, 0, ½)`, `Ŷ_k / (g Ai(X_k))` agrees with `√(2/δ)` to relative `4·10⁻⁴` over `-23 ≤ X ≤ 60` (so `μ` is tiny, consistent with the exponential bound).

**Not formalised:** an explicit rate and uniformity in `x` (the constants depend on `x`; the proof gives only `C₁A + C₂(A)δ` with `C₂(A) ~ A⁻⁹`, no
power rate); the Darboux phase and the sign of `κ` (only `κ²` is determined); `τ = -1` and half-integer `(M, σ, N)` for the `3j` chain (the Racah `6j` chain is `racah_chain_kappa_sharp*`, `RacahKappa*`); the hard
edges `x → 0, 1`.
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **The sharp constant of the actual `3j` chain**: `κ² δ → 2` (see the module docstring). -/
theorem hahn_chain_kappa_sharp (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ (r ε0 C Cmu ξ0 : ℝ), 0 < r ∧ 0 < ε0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧ ∀ τ : ℝ, 0 < τ → ∃ ε1 : ℝ, 0 < ε1 ∧ ε1 ≤ ε0 ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N → (n : ℤ) < N - max |M| |σ| →
        xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x → 1 / (N : ℝ) ≤ ε1 →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = 1 / (N : ℝ) ∧ ∃ J m Nw : ℤ, 1 ≤ J ∧ J < Nw ∧ J ≤ m ∧ m < Nw ∧
          (∀ k ∈ Finset.Icc J (Nw + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - Real.sqrt (1 - (x : ℝ) ^ 2)| ≤ r) ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) - r ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((J : ℝ) + 1 / 2) * δ ^ 3 < Real.sqrt (1 - (x : ℝ) ^ 2) - r + δ ^ 3 ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((m : ℝ) + 1 / 2) * δ ^ 3 < Real.sqrt (1 - (x : ℝ) ^ 2) + δ ^ 3 ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) + r / 4 ≤ ((Nw : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((Nw : ℝ) + 1 + 1 / 2) * δ ^ 3 ≤ Real.sqrt (1 - (x : ℝ) ^ 2) + r / 2 ∧
          ∃ κ μ : ℝ, |κ ^ 2 * δ - 2| ≤ τ ∧
            |μ| ≤ Cmu * Real.sqrt (N : ℝ) * Real.exp (-ξ0 / δ ^ 3) / δ ∧
            ∀ k ∈ Finset.Icc J (Nw + 1),
              |hahn3jY M σ N x k -
                  (κ * daoPhi (fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2))
                      (dalQ (δ ^ 3 / 2) δ k))
                    (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ) k +
                   μ * daoPsi (fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2))
                      (dalQ (δ ^ 3 / 2) δ k))
                    (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ) k)| ≤
                C * δ ^ 3 * (|κ| * airyWt (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k) +
                  |μ| * airyBiWt (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k)) := by
  obtain ⟨r, ε0, C, Cmu, ξ0, gmin, gmax, c1, c2, κmin, Cl, hr, hε0, hC, hCmu, hξ0, hgmin, hgg, hc1, hc12, hκmin, hCl, HA⟩ :=
    hahn_chain_kappa_data M σ x hx0 hx1
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hx1' : (x : ℝ) < 1 := by exact_mod_cast hx1
  have hc2 : 0 < c2 := lt_of_lt_of_le hc1 hc12
  have hgmax : 0 < gmax := lt_of_lt_of_le hgmin hgg
  obtain ⟨rs, c1s, c2s, Cs⟩ := ksh_chart (x : ℝ) hx0' hx1'
  have hc1s := Cs.hc1
  have hc2s : 0 < c2s := lt_of_lt_of_le Cs.hc1 Cs.hc12
  -- the smallness of `δ` of the order-sharp theorem
  set σ0 : ℝ := min (√(3 * c1 * r / 4)) (1 / (20 * c2)) with hσ0
  have hσ0p : 0 < σ0 := lt_min (Real.sqrt_pos.2 (by positivity)) (by positivity)
  set B0' : ℝ := (450 * gmax + C) * Cmu with hB0def
  have hB0' : 0 ≤ B0' := by positivity
  set δ1 : ℝ := min (1 / 2) (min (c1 * r / (8 * (c2 + 1))) (min (σ0 / 100) (min (gmin ^ 2 * c1 / (80 * c2 * σ0 * (C + 1) ^ 2))
    (min (σ0 ^ 2 / 2) (min (ξ0 / 14) (κmin * ξ0 ^ 3 / (48 * (B0' + 1)))))))) with hδ1def
  have hδ1p : 0 < δ1 := by
    refine lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity))))))
  refine ⟨r, ε0, C, Cmu, ξ0, hr, hε0, hC, hCmu, hξ0, fun τ hτ => ?_⟩
  -- the constants of the left cut and of the band
  set e : ℝ := ((x : ℝ) + 1) / 2 with hedef
  have hxe : (x : ℝ) < e := by rw [hedef]; linarith
  have he1 : e ≤ 1 := by rw [hedef]; linarith
  set K0 : ℕ := ⌈kl_K0real (M : ℝ) (σ : ℝ) (x : ℝ) e⌉₊ with hK0def
  have hK0 : kl_K0real (M : ℝ) (σ : ℝ) (x : ℝ) e ≤ (K0 : ℝ) := Nat.le_ceil _
  have hβ0 : 0 ≤ kl_beta (M : ℝ) (σ : ℝ) := by unfold kl_beta; positivity
  have hmσ0 : 0 ≤ |(M : ℝ) * (σ : ℝ)| := abs_nonneg _
  set K1 : ℝ := 1 + kl_beta (M : ℝ) (σ : ℝ) + 3 * kl_beta (M : ℝ) (σ : ℝ) / (x : ℝ) ^ 2 + 6 * kl_beta (M : ℝ) (σ : ℝ) +
    |(M : ℝ) * (σ : ℝ)| + (K0 : ℝ) with hK1def
  have hK0n : (0 : ℝ) ≤ (K0 : ℝ) := Nat.cast_nonneg K0
  have h3b : 0 ≤ 3 * kl_beta (M : ℝ) (σ : ℝ) / (x : ℝ) ^ 2 := by positivity
  have hK1a : kl_beta (M : ℝ) (σ : ℝ) < K1 := by rw [hK1def]; linarith
  have hK1b : 3 * kl_beta (M : ℝ) (σ : ℝ) ≤ (x : ℝ) ^ 2 * K1 := by
    have e1 : (x : ℝ) ^ 2 * (3 * kl_beta (M : ℝ) (σ : ℝ) / (x : ℝ) ^ 2) = 3 * kl_beta (M : ℝ) (σ : ℝ) := by field_simp
    have : (x : ℝ) ^ 2 * (3 * kl_beta (M : ℝ) (σ : ℝ) / (x : ℝ) ^ 2) ≤ (x : ℝ) ^ 2 * K1 :=
      mul_le_mul_of_nonneg_left (by rw [hK1def]; linarith) (sq_nonneg _)
    linarith
  have hK1c : 3 * kl_beta (M : ℝ) (σ : ℝ) ≤ K1 / 2 := by rw [hK1def]; linarith
  have hK1d : |(M : ℝ) * (σ : ℝ)| ≤ K1 := by rw [hK1def]; linarith
  have hK1e : (K0 : ℝ) ≤ K1 := by rw [hK1def]; linarith
  have hK11 : 1 ≤ K1 := by rw [hK1def]; linarith
  have hCL1 : 1 ≤ ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 := ke_C_ge_one K0 hx0' hxe he1
  have hqs : 0 < √(1 - (x : ℝ) ^ 2) := Real.sqrt_pos.2 (by nlinarith only [hx0', hx1'])
  have hqs2 : √(1 - (x : ℝ) ^ 2) ^ 2 = 1 - (x : ℝ) ^ 2 := Real.sq_sqrt (by nlinarith only [hx0', hx1'])
  have hqs1 : √(1 - (x : ℝ) ^ 2) < 1 := by nlinarith only [hqs2, hx0', hqs]
  have hx0e : 0 < e := lt_trans hx0' hxe
  have he2 : 0 < 1 - e ^ 2 := by
    have : e < 1 := by rw [hedef]; linarith
    nlinarith only [this, hx0e]
  have hPos : (ksfK M σ (x : ℝ) rs r c1 c1s c2 c2s gmax C e K0 K1).Pos :=
    ⟨hx0', hqs, hqs1, Cs.hr, hr, hc1, hc1s, hc2, hc2s, hgmax, hC, hCL1, hβ0, hmσ0, hK11, Real.sqrt_pos.2 he2,
      (show √(1 - e ^ 2) ≤ 1 from Real.sqrt_le_one.2 (by nlinarith only [hx0e]))⟩
  have hB0 : 0 < min (1 / 5 : ℝ) (τ / 4) := lt_min (by norm_num) (by linarith)
  obtain ⟨A, δ2, hA0, hAq, hA1, hδ20, Hch⟩ := ksfin_choose hPos hB0
  refine ⟨min ε0 (min (δ1 ^ 3) (δ2 ^ 3)), lt_min hε0 (lt_min (by positivity) (by positivity)), min_le_left _ _, ?_⟩
  intro N n hN hn hxn hNε
  obtain ⟨hNε0, hNε2⟩ := le_min_iff.1 hNε
  obtain ⟨hNε1, hNε3⟩ := le_min_iff.1 hNε2
  obtain ⟨δ, hδp, hδ3, hδ3r, J, m, Nw, hJ, hJN, hJm, hm1, hwin, h1, h2, h3, h4, h5, h6, Hc, κ, μ, d⟩ :=
    HA N n hN hn hxn hNε0
  have hδδ1 : δ ≤ δ1 := by
    have : δ ^ 3 ≤ δ1 ^ 3 := by rw [hδ3]; exact hNε1
    exact le_of_pow_le_pow_left₀ (by norm_num) hδ1p.le this
  have hδδ2 : δ ≤ δ2 := by
    have : δ ^ 3 ≤ δ2 ^ 3 := by rw [hδ3]; exact hNε3
    exact le_of_pow_le_pow_left₀ (by norm_num) hδ20.le this
  obtain ⟨hδhalf, hδrest⟩ := le_min_iff.1 hδδ1
  obtain ⟨hδc, hδrest⟩ := le_min_iff.1 hδrest
  obtain ⟨hδσ, hδrest⟩ := le_min_iff.1 hδrest
  obtain ⟨hδ5, hδrest⟩ := le_min_iff.1 hδrest
  obtain ⟨hδs, hδrest⟩ := le_min_iff.1 hδrest
  obtain ⟨hδξ, hδμ⟩ := le_min_iff.1 hδrest
  have s : KkSmall δ r C Cmu ξ0 gmin gmax c1 c2 κmin σ0 :=
    ⟨hδp, hr, hC, hCmu, hξ0, hgmin, hgg, hc1, hc12, hκmin, hσ0, hδhalf, hδc, hδσ, hδ5, hδs, hδξ, hδμ, hδ3r⟩
  obtain ⟨hGeo, hθ⟩ := Hch δ hδp hδδ2
  have hfin := ksfin_node (M := M) (σ := σ) (N := N) (x := x) (e := e) (K0 := K0) (K1 := K1) (A := A) (B0 := min (1 / 5 : ℝ) (τ / 4))
    hx0' hx1' d s Cs hPos hGeo hA0 hAq hA1 hθ (min_le_left _ _) hxe he1 hK0 hK1a hK1b hK1c hK1d hK1e
  refine ⟨δ, hδp, hδ3, J, m, Nw, hJ, hJN, hJm, hm1, hwin, h1, h2, h3, h4, h5, h6, κ, μ, ?_, d.mu,
    fun k hk => by simpa [daoPhi, daoPsi] using d.pt k hk⟩
  refine hfin.trans ?_
  have := min_le_right (1 / 5 : ℝ) (τ / 4)
  linarith

/-- info: 'FormalResearch.Special.hahn_chain_kappa_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_kappa_sharp

end FormalResearch.Special
