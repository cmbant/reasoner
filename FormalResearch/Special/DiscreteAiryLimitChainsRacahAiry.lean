module

public import FormalResearch.Special.DiscreteAiryLimitChains6j

/-!
# The Airy limit for the actual Wigner `6j` chain at the physical `c`-lattice (Weyl P3, `thm:racahAiryConnection`)

Composition of `discrete_airy_hahn_racah` (the discrete-to-Airy limit for the closed-form coefficients) with the
identification `racah_class_chain` (the actual natural-gauge `6j` chain solves exactly that recurrence) and the Gauss-weight
bound `racah_chain_sq_le` (condition `(R)`: `Ŷ_f² ≤ 4AB/(2C)`).

## Result (proved)

`racah_chain_airy`: fix integers `m, n`, shape parameters `α, β > 0` and `x`, `q_*` satisfying the hypotheses of
`discrete_airy_hahn_racah` for `P = 1/(4α²)`, `Q = 1/(4β²)`, `τ = +1` (simple turn `Φ(q_*²) = 0`, `1 - x > 0`, `q_*² P, q_*² Q < 1`),
and `A₀ > 0`.  There are constants `r, δ₀, C, C_osc, C_top, W, C_μ, ξ₀, D > 0` (depending on `α, β, x, q_*, m, n, A₀` only) such that for
every finite Racah system `RacahSystem a b m n D'`, every physical `c = c_i` and every scale `h = δ³ ≤ δ₀³` with `A h = α`,
`B h = β` (`A = a + (n+1)/2`, `B = b + (m+1)/2`) and `x = (A²+B²-C²)/(2AB)` (`C = c+½`), there are window indices
`1 ≤ J ≤ m' ≤ N_w` (positions exported as in `discrete_airy_hahn_racah`) and `κ, μ ∈ ℝ`, `|μ| ≤ C_μ Y_max e^{-ξ(X_{N_w})}`,
`ξ₀/δ³ ≤ ξ(X_{N_w})`, with `Y_max = √(4AB/(2C))` and the same two-sided bounds as in `hahn_chain_airy`, for the actual
natural-gauge kernel `Ŷ_k = √(2k+1) Φ_k` of the Wigner `6j` symbol.  The `6j` input `(R)` is proved from `gaussWeight_6j` and
not assumed.

## Not formalised

`κ` is unidentified (Darboux/Wigner-`d`) and `κ ≠ 0` is not proved; the hypotheses `A h = α`, `B h = β`, `x = cosA …` couple
the integer data to the scale (the theorem is a statement for each such realisation); in this module the turn hypotheses are
taken as hypotheses and only `τ = +1` is covered (`α = β` forces `τ = -1`).  Done in `DiscreteAiryLimitChains2Racah`,
`DiscreteAiryLimitChains2Twist`: the turn from the triangle (`racah_turn_geom_pos/_neg`, `q_* = 2αβ sin θ/γ`), both branches
`τ = ±1` with the `(-1)^k` twist (`racah_chain_airy_geom_pos/_neg`), and infinitely many realisations as `h → 0`
(`racah_realisation`, `racah_chain_airy_family_pos/_neg`; e.g. `α/β = 3`, `x = 5/8`, `m = n = -1`,
`(a, b, c) = (6u+3, 2u+1, 5u+2)`).  Integer data only here (half-integer `m, n`: `DiscreteAiryLimitChains2Half6j`,
`Half6jFam`); the oscillatory side `X < -A₀` and the non-recessive pair (`racah_chain_airy_full_*` in `DiscreteAiryPhysRacah`, integer data,
up to `κ`); the `q`-Racah chain.
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner
  FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **`(R)` for the `6j` chain, all indices**: at a physical `c = c_i` of a finite Racah system with integer data,
`|Ŷ_k| ≤ √(4AB/(2C))` for every `k ∈ ℤ`. -/
theorem racah_chain_abs_le (a b c m n : ℤ) {D : ℕ} (hsys : RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D)
    (i : Fin (D + 1)) (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i) (k : ℤ) :
    |racah6jY a b c m n k| ≤ Real.sqrt (4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ))) := by
  by_cases hk : |m| ≤ k ∧ |n| ≤ k ∧ k ≤ 2 * b + m ∧ k ≤ 2 * a + n
  · set lo : ℤ := max |m| |n| with hlo
    set hi : ℤ := min (2 * b + m) (2 * a + n) with hhi
    have hklo : lo ≤ k := max_le hk.1 hk.2.1
    have hkhi : k ≤ hi := le_min hk.2.2.1 hk.2.2.2
    have hD : (D : ℤ) = hi - lo := by
      have h1 := hsys.dim
      have h2 := cMax_sub_cMin (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ)
      have e1 : fMin (m : ℚ) (n : ℚ) = (lo : ℚ) := by rw [hlo]; unfold fMin; push_cast; rfl
      have e2 : fMax (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) = (hi : ℚ) := by rw [hhi]; unfold fMax; push_cast; exact min_comm _ _
      rw [e1, e2] at h2
      rw [h2] at h1
      have : ((D : ℤ) : ℚ) = ((hi - lo : ℤ) : ℚ) := by push_cast; linarith
      exact_mod_cast this
    have hjD : (k - lo).toNat < D + 1 := by omega
    set j : Fin (D + 1) := ⟨(k - lo).toNat, hjD⟩ with hj
    have hfj : fPt (m : ℚ) (n : ℚ) j = (k : ℚ) := by
      unfold fPt
      have e1 : fMin (m : ℚ) (n : ℚ) = (lo : ℚ) := by rw [hlo]; unfold fMin; push_cast; rfl
      have h3 : (((k - lo).toNat : ℕ) : ℤ) = k - lo := Int.toNat_of_nonneg (by omega)
      have h4 : ((((k - lo).toNat : ℕ) : ℤ) : ℚ) = ((k - lo : ℤ) : ℚ) := by rw [h3]
      push_cast at h4
      show fMin (m : ℚ) (n : ℚ) + (((k - lo).toNat : ℕ) : ℚ) = (k : ℚ)
      rw [e1, h4]; ring
    have hsq := racah_chain_sq_le hsys i j
    rw [← hc, hfj] at hsq
    have hk0 : (0 : ℝ) ≤ k := by
      have : (0 : ℤ) ≤ k := le_trans (abs_nonneg m) hk.1
      exact_mod_cast this
    have hY : (racah6jY a b c m n k) ^ 2 =
        (2 * ((k : ℚ) : ℝ) + 1) * Phi6 (a : ℚ) (b : ℚ) (c : ℚ) (k : ℚ) (m : ℚ) (n : ℚ) ^ 2 := by
      unfold racah6jY
      rw [mul_pow, Real.sq_sqrt (by linarith)]
      push_cast; ring
    exact Real.abs_le_sqrt (by rw [hY]; exact hsq)
  · rw [racah_chain_support a b c m n k hk]
    simp

/-- **The discrete-to-Airy limit for the actual `6j` chain at the physical `c`-lattice.**  See the module docstring. -/
theorem racah_chain_airy (α β x qs : ℝ) (hα0 : 0 < α) (hβ0 : 0 < β) (hqs : 0 < qs) (hκ : 0 < 1 - 1 * x)
    (hα : 0 < 1 - 1 / (4 * α ^ 2) * qs ^ 2) (hβ : 0 < 1 - 1 / (4 * β ^ 2) * qs ^ 2)
    (hturn : Phi (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (qs ^ 2) = 0) (m n : ℤ) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ (i : Fin (D' + 1))
        (h : ℝ), (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → 0 < h → h ≤ δ0 ^ 3 →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ^ 3 = h ∧ ∃ J m' Nw : ℤ, 1 ≤ J ∧ J ≤ m' ∧ m' ≤ Nw ∧
          (∀ k ∈ Finset.Icc J (Nw + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - qs| ≤ r) ∧
          qs - D * δ ^ 2 ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧ ((J : ℝ) + 1 / 2) * δ ^ 3 ≤ qs ∧
          qs ≤ ((m' : ℝ) + 1 / 2) * δ ^ 3 ∧ ((m' : ℝ) + 1 / 2) * δ ^ 3 < qs + δ ^ 3 ∧
          turnX (hrU (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x) qs (δ ^ 3 / 2) δ J ≤ -A0 ∧
          ξ0 / δ ^ 3 ≤ airyXi (turnX (hrU (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x) qs (δ ^ 3 / 2) δ Nw) ∧
          ∃ κ μ : ℝ, |μ| ≤ Cmu * Real.sqrt (4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ))) *
              Real.exp (-airyXi (turnX (hrU (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x) qs (δ ^ 3 / 2) δ Nw)) ∧
            (∀ k ∈ Finset.Icc J m', |racah6jY a b c m n k -
                κ * turnPsi (hrU (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x) (hrA1 (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)))
                  qs (δ ^ 3 / 2) δ k| ≤ C * δ ^ 3 * |κ| * W + Cosc * (|μ| / δ)) ∧
            (∀ k ∈ Finset.Icc m' (Nw + 1), |racah6jY a b c m n k -
                κ * turnPsi (hrU (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x) (hrA1 (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)))
                  qs (δ ^ 3 / 2) δ k| ≤
              C * δ ^ 3 * |κ| * turnPsi (hrU (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x)
                (hrA1 (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2))) qs (δ ^ 3 / 2) δ k +
                Ctop * |μ| / δ / airyWt (turnX (hrU (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x) qs (δ ^ 3 / 2) δ k)) := by
  have hP : (0 : ℝ) ≤ 1 / (4 * α ^ 2) := by positivity
  have hQ : (0 : ℝ) ≤ 1 / (4 * β ^ 2) := by positivity
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, -, hδ0, -, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    discrete_airy_hahn_racah hP hQ (m : ℝ) (n : ℝ) 1 x qs hqs (by norm_num) hκ hα hβ hturn A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro a b c D' hsys i h hc hh hhδ hAh hBh hx
  obtain ⟨δ, hδ0', hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h := by
    refine ⟨h ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos hh _, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    norm_num
  have hδle : δ ≤ δ0 := by
    by_contra hcon
    push Not at hcon
    have : δ0 ^ 3 < δ ^ 3 := by gcongr
    linarith
  obtain ⟨J, m', Nw, hJ, hJm, hmN, hwin, h1, h2, h3, h4, h5, Hc⟩ := H δ hδ0' hδle
  obtain ⟨hxi, -, -, -, HY⟩ := Hc
  have hA : 0 < wA (a : ℚ) (n : ℚ) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hB : 0 < wB (b : ℚ) (m : ℚ) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hrows : ∀ k ∈ Finset.Icc (J + 1) Nw,
      jac (hrAk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) (δ ^ 3))
        (hrCk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (m : ℝ) (n : ℝ) (δ ^ 3)) (racah6jY a b c m n) k = 0 := by
    intro k hk
    have hk1 : 1 ≤ k := by rw [Finset.mem_Icc] at hk; omega
    have := racah_class_chain a b c m n h hh hA hB k hk1
    rw [hAh, hBh, hx] at this
    rw [hδ3]
    exact this
  have hbd : ∀ k : ℤ, |racah6jY a b c m n k| ≤
      Real.sqrt (4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ))) :=
    fun k => racah_chain_abs_le a b c m n hsys i hc k
  obtain ⟨κ, μ, hμ, hlow, hup⟩ := HY (racah6jY a b c m n) _ hrows (hbd _) (hbd _)
  exact ⟨δ, hδ0', hδle, hδ3, J, m', Nw, hJ, hJm, hmN, hwin, h1, h2, h3, h4, h5, hxi, κ, μ, hμ, hlow, hup⟩

/-- info: 'FormalResearch.Special.racah_chain_airy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_chain_airy

/-- info: 'FormalResearch.Special.racah_chain_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_chain_abs_le

end FormalResearch.Special
