module

public import FormalResearch.Racah.P3PhaseDatum
public import FormalResearch.Wigner.WignerDLadder

/-!
# The fixed-rank contact identity of the class (Weyl P3, `prop:general-fixed-rank-contact`)

Source: `Weyl/P3/paper/weyl_midpoint_semiclassics.tex`, `prop:general-fixed-rank-contact` (T:650) and its
proof in `weyl_midpoint_semiclassics_appendices.tex` ("Proof of Proposition
`prop:general-fixed-rank-contact`", the contact identity `eq:general-contact-identity`, the ladders and the
exceptional channel).

## What is formalised (proved, all rational offsets `a, b`, all ranks `k ≥ 1/2`)

* `contact_identity`: `eq:general-contact-identity`, with the natural gauge `√(2k+1)` kept and the
  Wigner coefficients `A0 = A_k^{(0)}`, `B0 = B_k^{(0)}` of `eq:wigner-natural-jacobi`:
  `x û_k - A_{k+1}û_{k+1} - A_kû_{k-1} - B_kû_k
     = -ε₁[(k+1)²A_{k+1}d̂_{k+1} + k²A_kd̂_{k-1}] + (β₁κ²+β₂)d̂_k + λ₁x d̂_k`, `û_j = √(2j+1)𝒬_{2,j}d_j`,
  `d_j = d^j_{ab}(arccos x)` (`wignerSmallDx`).  Hypotheses: `x ∈ (-1,1)`, `|a|,|b| ≤ k` (the range
  `k ≥ k_min`), `k ≥ 1/2`, and at `k = 1/2` that `|a| = 1/2` or `|b| = 1/2`.  The edge row `k = k_min` is not
  a separate case for `k_min ≥ 1` (`R_{k_min} = 0`), nor for `k_min = 1/2` (`A_{1/2}^{(0)} = 0`).
  The proof is the gauge-free algebraic identity `contact_alg` in the variables `(d_k, d_k')` obtained from
  the three Wigner ladders `wignerSmallDx_rank_lower/upper` (at ranks `k`, `k-1`, `k+1`), no three-term
  recurrence and no derivative of `d_{k±1}` beyond the ladders.
* `contact_identity_exceptional`: the exceptional channel `a = b = k = 0` (`d_0 = 1`, `d_1 = x`).
* `contact_identity_hahn`, `contact_identity_racah`: the specialisations to the class data of
  `eq:hahn-class-data`, `eq:racah-class-data` (sources of `A:1372`, `A:1550`).
* `wigner_natural_jacobi`, `wigner_natural_jacobi_zero`: `eq:wigner-natural-jacobi` itself (all rows,
  with the conventions `A_{k_min}^{(0)} = 0`, `B_0^{(0)} = 0`).  This was not formalised before.
* `contact_residual_hasDerivAt`: the reduction "the `t`-coefficient of `𝓡_k(Û^{[2]})` vanishes iff
  `eq:general-contact-identity` holds", for given first-order jets of `A_{k±}(t)`, `B_k(t)`, `Û_j(t)`.
* `Q2_beta2_part`, `Q2_lam1_part`: the "transparent" `β₂`- and `λ₁`-parts of `𝒬_{2,k}`.

## Not formalised

The closed form `ρ₂(0,x)` (`eq:general-rho20`) and the operator `𝒬_{2,k}` are *definitions* copied from the
paper (`rho20`, `Q2` of `P3PhaseDatum`): their derivation from the second-order Weyl density
`eq:generic-second-weyl-density` and the identification of `û_k` with the `t`-coefficient of the corrected
pullback `W^{[2]}_q d^k(Θ^{[2]}_q)` are not formalised (the jets of `Û_j` are *hypotheses* of
`contact_residual_hasDerivAt`).  Nothing about `O_k(t²)` of the residual or about analyticity in `t`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner Set

set_option maxRecDepth 100000 in
/-- **Gauge-free contact identity** (`eq:general-contact-identity` divided by `√(2k+1)`): pure algebra
in the data `u = d_k`, `w = d_k'`, `M = R_k d_{k-1}`, `M' = R_k d_{k-1}'`, `P = R_{k+1} d_{k+1}`,
`P' = R_{k+1} d_{k+1}'`, which the Wigner ladders express through `(u, w)`. -/
theorem contact_alg (a b ε β₁ β₂ l₁ k x u w M M' P P' : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hk : k ≠ 0) (hk1 : k + 1 ≠ 0) (hk2 : 2 * k + 1 ≠ 0)
    (hM : M = k * (1 - x ^ 2) * w + (k ^ 2 * x - a * b) * u)
    (hM' : k * (1 - x ^ 2) * M' = (k ^ 2 * x - a * b) * M - ((k ^ 2 - a ^ 2) * (k ^ 2 - b ^ 2)) * u)
    (hP : P = ((k + 1) ^ 2 * x - a * b) * u - (k + 1) * (1 - x ^ 2) * w)
    (hP' : (k + 1) * (1 - x ^ 2) * P' =
      (((k + 1) ^ 2 - a ^ 2) * ((k + 1) ^ 2 - b ^ 2)) * u - ((k + 1) ^ 2 * x - a * b) * P) :
    (x - a * b / (k * (k + 1))) * Q2 a b (k + 1 / 2) ε β₁ β₂ l₁ (x * ε - β₁) x u w
      - Q2 a b (k + 1 + 1 / 2) ε β₁ β₂ l₁ (x * ε - β₁) x P P' / ((k + 1) * (2 * k + 1))
      - Q2 a b (k - 1 + 1 / 2) ε β₁ β₂ l₁ (x * ε - β₁) x M M' / (k * (2 * k + 1)) =
    -ε * ((k + 1) * P + k * M) / (2 * k + 1) + (β₁ * (k + 1 / 2) ^ 2 + β₂ + l₁ * x) * u := by
  have hs : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have hM'' : M' = ((k ^ 2 * x - a * b) * M - ((k ^ 2 - a ^ 2) * (k ^ 2 - b ^ 2)) * u) /
      (k * (1 - x ^ 2)) := by
    field_simp; linear_combination hM'
  have hP'' : P' = ((((k + 1) ^ 2 - a ^ 2) * ((k + 1) ^ 2 - b ^ 2)) * u -
      ((k + 1) ^ 2 * x - a * b) * P) / ((k + 1) * (1 - x ^ 2)) := by
    field_simp; linear_combination hP'
  have hk2' : 1 + k * 2 ≠ 0 := by intro h; apply hk2; linarith
  have hk2'' : k * 2 + 1 ≠ 0 := by intro h; apply hk2; linarith
  have hk1' : 1 + k ≠ 0 := by intro h; apply hk1; linarith
  rw [Q2_eq _ _ _ _ _ _ _ _ _ _ hx, Q2_eq _ _ _ _ _ _ _ _ _ _ hx, Q2_eq _ _ _ _ _ _ _ _ _ _ hx,
    hM'', hP'', hM, hP]
  field_simp
  ring

/-! ### The natural-gauge objects of the paper -/

/-- Natural-gauge Wigner function `d̂_k = √(2k+1) d^k_{ab}(arccos x)`. -/
noncomputable def dHat (a b k : ℚ) (x : ℝ) : ℝ :=
  Real.sqrt (2 * (k : ℝ) + 1) * wignerSmallDx k a b x

/-- `A_k^{(0)} = R_k/(k √(4k²-1))` of `eq:wigner-natural-jacobi`, with `R_k = wigR`.  With Lean's
division convention `A_{k_min}^{(0)} = 0` holds automatically for `k_min ≥ 1` (`R = 0`) and for
`k_min = 1/2` (`√0 = 0`), and `A_0^{(0)} = 0`, as in the paper. -/
noncomputable def A0 (a b k : ℚ) : ℝ := wigR k a b / ((k : ℝ) * Real.sqrt (4 * (k : ℝ) ^ 2 - 1))

/-- `B_k^{(0)} = ab/(k(k+1))` of `eq:wigner-natural-jacobi` (`B_0^{(0)} = 0` by `x/0 = 0`). -/
noncomputable def B0 (a b k : ℚ) : ℝ := (a : ℝ) * b / ((k : ℝ) * ((k : ℝ) + 1))

/-- The `t`-coefficient `û_k = √(2k+1) 𝒬_{2,k} d_k` of the second-order pullback `Û^{[2]}_k` at fixed
rank (`proof of prop:general-fixed-rank-contact`), `χ = xε₁ - β₁`. -/
noncomputable def uHat (a b k : ℚ) (ε β₁ β₂ l₁ x : ℝ) : ℝ :=
  Real.sqrt (2 * (k : ℝ) + 1) *
    Q2 a b ((k : ℝ) + 1 / 2) ε β₁ β₂ l₁ (x * ε - β₁) x (wignerSmallDx k a b x)
      (deriv (wignerSmallDx k a b) x)

lemma Q2_lin (a b κ ε β₁ β₂ l₁ χ x c d dp : ℝ) :
    Q2 a b κ ε β₁ β₂ l₁ χ x (c * d) (c * dp) = c * Q2 a b κ ε β₁ β₂ l₁ χ x d dp := by
  unfold Q2; ring

lemma A0_succ_gauge (a b k : ℚ) (hk : 0 ≤ (k : ℝ)) :
    A0 a b (k + 1) * Real.sqrt (2 * ((k + 1 : ℚ) : ℝ) + 1) =
      wigR (k + 1) a b / (((k : ℝ) + 1) * Real.sqrt (2 * (k : ℝ) + 1)) := by
  unfold A0
  push_cast
  have h1 : 4 * ((k : ℝ) + 1) ^ 2 - 1 = (2 * k + 1) * (2 * k + 3) := by ring
  have h2 : 2 * ((k : ℝ) + 1) + 1 = 2 * k + 3 := by ring
  have p1 : 0 < Real.sqrt (2 * (k : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
  have p2 : 0 < Real.sqrt (2 * (k : ℝ) + 3) := Real.sqrt_pos.2 (by linarith)
  rw [h1, h2, Real.sqrt_mul (by linarith)]
  field_simp

lemma A0_pred_gauge (a b k : ℚ) (hk : (1 : ℝ) / 2 < (k : ℝ)) :
    A0 a b k * Real.sqrt (2 * ((k - 1 : ℚ) : ℝ) + 1) =
      wigR k a b / ((k : ℝ) * Real.sqrt (2 * (k : ℝ) + 1)) := by
  unfold A0
  push_cast
  have h1 : 4 * (k : ℝ) ^ 2 - 1 = (2 * k - 1) * (2 * k + 1) := by ring
  have h2 : 2 * ((k : ℝ) - 1) + 1 = 2 * k - 1 := by ring
  have p1 : 0 < Real.sqrt (2 * (k : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
  have p2 : 0 < Real.sqrt (2 * (k : ℝ) - 1) := Real.sqrt_pos.2 (by linarith)
  rw [h1, h2, Real.sqrt_mul (by linarith)]
  have : (k : ℝ) ≠ 0 := by linarith
  generalize Real.sqrt (2 * (k : ℝ) - 1) = u at *
  generalize Real.sqrt (2 * (k : ℝ) + 1) = v at *
  field_simp

/-- **`prop:general-fixed-rank-contact`, `eq:general-contact-identity`** (proved).  For rational
offsets `a, b`, a rank `k ≥ max(|a|, |b|)`, `k ≥ 1/2`, and `x ∈ (-1,1)`, with `d_j = d^j_{ab}(arccos x)`,
`d̂_j = √(2j+1) d_j`, `û_j = √(2j+1) 𝒬_{2,j} d_j` and the class data `(ε₁, β₁, β₂, λ₁)`
(`χ = xε₁ - β₁`):

`x û_k - A_{k+1}û_{k+1} - A_k û_{k-1} - B_k û_k
   = -ε₁[(k+1)² A_{k+1} d̂_{k+1} + k² A_k d̂_{k-1}] + (β₁κ² + β₂) d̂_k + λ₁ x d̂_k`,   `κ = k + 1/2`,

with `A_k = A_k^{(0)}`, `B_k = B_k^{(0)}` the Wigner coefficients of `eq:wigner-natural-jacobi`.  This is
the vanishing of the `t`-coefficient of the residual `𝓡_k(Û^{[2]})` (the paper's "if and only if"
reduction is the first-order Taylor bookkeeping `A_k(h) = A_k^{(0)}(1 + (λ₁ - ε₁k²)t)`, etc.).

*Hypotheses.* `|a|, |b| ≤ k` is the range `k ≥ k_min` of the paper (no integrality of `k - a` is needed:
off the Wigner lattice every `d` vanishes).  The edge row `k = k_min` needs no separate case for
`k_min ≥ 1`: `R_{k_min} = 0` kills the `d_{k-1}` terms, as the paper says.  For `k = 1/2` the paper's
`A_{1/2}^{(0)} := 0` is `√0 = 0` in Lean, and the hypothesis `hedge` (`|a| = 1/2` or `|b| = 1/2`, which
holds for every admissible offset pair at `k_min = 1/2`) makes the formal `R_{1/2} d_{-1/2}` term vanish
too.  The exceptional channel `a = b = k = 0` is `contact_identity_exceptional`.

*Not formalised:* the derivation of `û_k = √(2k+1) 𝒬_{2,k} d_k` as the `t`-coefficient of the
pullback `W_q^{[2]} d^k(Θ_q^{[2]})` and of the closed form `ρ₂(0,x)`
(`eq:generic-second-weyl-density`): `Q2`, `rho20` are definitions copied from the paper. -/
theorem contact_identity (a b k : ℚ) (ε β₁ β₂ l₁ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (ha : |(a : ℝ)| ≤ k) (hb : |(b : ℝ)| ≤ k) (hk : (1 : ℝ) / 2 ≤ k)
    (hedge : (k : ℝ) = 1 / 2 → ((1 : ℝ) / 4 - (a : ℝ) ^ 2) * (1 / 4 - (b : ℝ) ^ 2) = 0) :
    x * uHat a b k ε β₁ β₂ l₁ x - A0 a b (k + 1) * uHat a b (k + 1) ε β₁ β₂ l₁ x
        - A0 a b k * uHat a b (k - 1) ε β₁ β₂ l₁ x - B0 a b k * uHat a b k ε β₁ β₂ l₁ x =
      -ε * (((k : ℝ) + 1) ^ 2 * A0 a b (k + 1) * dHat a b (k + 1) x
          + (k : ℝ) ^ 2 * A0 a b k * dHat a b (k - 1) x)
        + (β₁ * ((k : ℝ) + 1 / 2) ^ 2 + β₂) * dHat a b k x + l₁ * x * dHat a b k x := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hσ : 0 < Real.sqrt (2 * (k : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
  set σ := Real.sqrt (2 * (k : ℝ) + 1) with hσdef
  have hσ2 : σ ^ 2 = 2 * (k : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have hs : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  -- the rank factors
  have hA : ((a : ℝ)) ^ 2 ≤ (k : ℝ) ^ 2 := by nlinarith [abs_nonneg (a : ℝ), sq_abs (a : ℝ)]
  have hB : ((b : ℝ)) ^ 2 ≤ (k : ℝ) ^ 2 := by nlinarith [abs_nonneg (b : ℝ), sq_abs (b : ℝ)]
  set R0 := wigR k a b with hR0
  set R1 := wigR (k + 1) a b with hR1
  have hR0sq : R0 ^ 2 = ((k : ℝ) ^ 2 - a ^ 2) * ((k : ℝ) ^ 2 - b ^ 2) := by
    rw [hR0]; unfold wigR
    rw [Real.sq_sqrt (by nlinarith)]; ring
  have hR1sq : R1 ^ 2 = (((k : ℝ) + 1) ^ 2 - a ^ 2) * (((k : ℝ) + 1) ^ 2 - b ^ 2) := by
    rw [hR1]; unfold wigR
    push_cast
    rw [Real.sq_sqrt (by nlinarith)]; ring
  -- the four ladders
  have L0 := wignerSmallDx_rank_lower k a b hx
  have U0 := wignerSmallDx_rank_upper (k - 1) a b hx
  have U1 := wignerSmallDx_rank_upper k a b hx
  have L1 := wignerSmallDx_rank_lower (k + 1) a b hx
  rw [sub_add_cancel] at U0
  rw [add_sub_cancel_right] at L1
  push_cast at U0 U1 L1 L0
  simp only [sub_add_cancel] at U0
  have hs0 : (0 : ℝ) < 1 - x ^ 2 := hs
  have hkk1 : (k : ℝ) + 1 ≠ 0 := by linarith
  have hk2 : 2 * (k : ℝ) + 1 ≠ 0 := by linarith
  -- the algebraic input
  have key := contact_alg (a : ℝ) b ε β₁ β₂ l₁ k x (wignerSmallDx k a b x)
    (deriv (wignerSmallDx k a b) x) (R0 * wignerSmallDx (k - 1) a b x)
    (R0 * deriv (wignerSmallDx (k - 1) a b) x) (R1 * wignerSmallDx (k + 1) a b x)
    (R1 * deriv (wignerSmallDx (k + 1) a b) x) hx hk0.ne' hkk1 hk2
    (by rw [L0]; ring)
    (by
      have : (k : ℝ) * (1 - x ^ 2) * (R0 * deriv (wignerSmallDx (k - 1) a b) x) =
          (k ^ 2 * x - a * b) * (R0 * wignerSmallDx (k - 1) a b x) - R0 ^ 2 * wignerSmallDx k a b x := by
        linear_combination R0 * U0
      rw [this, hR0sq])
    (by rw [U1]; ring)
    (by
      have : ((k : ℝ) + 1) * (1 - x ^ 2) * (R1 * deriv (wignerSmallDx (k + 1) a b) x) =
          R1 ^ 2 * wignerSmallDx k a b x
            - (((k : ℝ) + 1) ^ 2 * x - a * b) * (R1 * wignerSmallDx (k + 1) a b x) := by
        linear_combination (-R1) * L1
      rw [this, hR1sq])
  rw [Q2_lin, Q2_lin] at key
  -- gauge translation
  have hR0z : (k : ℝ) = 1 / 2 → R0 = 0 := by
    intro h
    rw [hR0]; unfold wigR
    have h' : ((k : ℝ) ^ 2 - (b : ℝ) ^ 2) * ((k : ℝ) ^ 2 - (a : ℝ) ^ 2) = 0 := by
      have := hedge h
      rw [h]; nlinarith [this, show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num]
    rw [h']; simp
  have hA0z : (k : ℝ) = 1 / 2 → A0 a b k = 0 := by
    intro h
    unfold A0
    rw [← hR0, hR0z h]; simp
  have E1 : A0 a b (k + 1) * uHat a b (k + 1) ε β₁ β₂ l₁ x =
      σ * (R1 * Q2 a b ((k : ℝ) + 1 + 1 / 2) ε β₁ β₂ l₁ (x * ε - β₁) x
        (wignerSmallDx (k + 1) a b x) (deriv (wignerSmallDx (k + 1) a b) x) /
          (((k : ℝ) + 1) * (2 * k + 1))) := by
    unfold uHat
    rw [← mul_assoc, A0_succ_gauge a b k hk0.le]
    push_cast
    generalize Q2 a b ((k : ℝ) + 1 + 1 / 2) ε β₁ β₂ l₁ (x * ε - β₁) x
        (wignerSmallDx (k + 1) a b x) (deriv (wignerSmallDx (k + 1) a b) x) = q
    rw [← hσdef]
    field_simp
    linear_combination (-(R1 * q)) * hσ2
  have E2 : A0 a b k * uHat a b (k - 1) ε β₁ β₂ l₁ x =
      σ * (R0 * Q2 a b ((k : ℝ) - 1 + 1 / 2) ε β₁ β₂ l₁ (x * ε - β₁) x
        (wignerSmallDx (k - 1) a b x) (deriv (wignerSmallDx (k - 1) a b) x) /
          ((k : ℝ) * (2 * k + 1))) := by
    by_cases hh : (k : ℝ) = 1 / 2
    · rw [hA0z hh, hR0z hh]; simp
    · have hlt : (1 : ℝ) / 2 < k := lt_of_le_of_ne hk (Ne.symm hh)
      unfold uHat
      rw [← mul_assoc, A0_pred_gauge a b k hlt]
      push_cast
      generalize Q2 a b ((k : ℝ) - 1 + 1 / 2) ε β₁ β₂ l₁ (x * ε - β₁) x
          (wignerSmallDx (k - 1) a b x) (deriv (wignerSmallDx (k - 1) a b) x) = q
      rw [← hσdef]
      field_simp
      linear_combination (-(R0 * q)) * hσ2
  have E3 : ((k : ℝ) + 1) ^ 2 * A0 a b (k + 1) * dHat a b (k + 1) x =
      σ * (((k : ℝ) + 1) * (R1 * wignerSmallDx (k + 1) a b x) / (2 * k + 1)) := by
    have : ((k : ℝ) + 1) ^ 2 * A0 a b (k + 1) * dHat a b (k + 1) x =
        ((k : ℝ) + 1) ^ 2 * (A0 a b (k + 1) * Real.sqrt (2 * ((k + 1 : ℚ) : ℝ) + 1)) *
          wignerSmallDx (k + 1) a b x := by unfold dHat; ring
    rw [this, A0_succ_gauge a b k hk0.le]
    generalize wignerSmallDx (k + 1) a b x = q
    rw [← hσdef]
    field_simp
    linear_combination (-(R1 * q)) * hσ2
  have E4 : (k : ℝ) ^ 2 * A0 a b k * dHat a b (k - 1) x =
      σ * ((k : ℝ) * (R0 * wignerSmallDx (k - 1) a b x) / (2 * k + 1)) := by
    by_cases hh : (k : ℝ) = 1 / 2
    · rw [hA0z hh, hR0z hh]; simp
    · have hlt : (1 : ℝ) / 2 < k := lt_of_le_of_ne hk (Ne.symm hh)
      have : (k : ℝ) ^ 2 * A0 a b k * dHat a b (k - 1) x =
          (k : ℝ) ^ 2 * (A0 a b k * Real.sqrt (2 * ((k - 1 : ℚ) : ℝ) + 1)) *
            wignerSmallDx (k - 1) a b x := by unfold dHat; ring
      rw [this, A0_pred_gauge a b k hlt]
      generalize wignerSmallDx (k - 1) a b x = q
      rw [← hσdef]
      field_simp
      linear_combination (-(R0 * q)) * hσ2
  rw [E1, E2, E3, E4]
  unfold uHat dHat B0
  rw [← hσdef]
  linear_combination σ * key

/-! ### The exceptional channel `a = b = k = 0` -/

lemma wignerSmallD_zero_zero_zero (θ : ℝ) : wignerSmallD 0 0 0 θ = 1 := by
  have hf : fq 0 = 1 := by simpa using fq_natCast 0
  have hi : ifa 0 = 1 := by simpa using ifa_natCast 0
  unfold wignerSmallD
  rw [finsum_wignerTerm_eq_sum]
  norm_num [wignerTerm, wignerMag, hf, hi]

/-- **`prop:general-fixed-rank-contact`, exceptional channel `a = b = k = 0`** (the "checked directly"
case of the proof; `d_0 = 1`, `d_1 = x`).  Row `k = 0` of the Jacobi equation has no `A_0 û_{-1}` term, and
`B_0^{(0)} = 0`. -/
theorem contact_identity_exceptional (ε β₁ β₂ l₁ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    x * uHat 0 0 0 ε β₁ β₂ l₁ x - A0 0 0 1 * uHat 0 0 1 ε β₁ β₂ l₁ x
        - B0 0 0 0 * uHat 0 0 0 ε β₁ β₂ l₁ x =
      -ε * (((0 : ℚ) : ℝ) + 1) ^ 2 * A0 0 0 1 * dHat 0 0 1 x
        + (β₁ * (((0 : ℚ) : ℝ) + 1 / 2) ^ 2 + β₂) * dHat 0 0 0 x + l₁ * x * dHat 0 0 0 x := by
  have d0 : wignerSmallDx 0 0 0 = fun _ => 1 := by
    funext y; unfold wignerSmallDx; exact wignerSmallD_zero_zero_zero _
  have d1 : ∀ y ∈ Ioo (-1 : ℝ) 1, wignerSmallDx 1 0 0 y = y := by
    intro y hy
    unfold wignerSmallDx
    rw [wignerSmallD_one_zero_zero, Real.cos_arccos (by linarith [hy.1]) (by linarith [hy.2])]
  have d1' : deriv (wignerSmallDx 1 0 0) x = 1 := by
    have : wignerSmallDx 1 0 0 =ᶠ[nhds x] id :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx) (fun y hy => d1 y hy)
    rw [this.deriv_eq]; simp
  have hR : wigR 1 0 0 = 1 := by unfold wigR; norm_num
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h3sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hA : A0 0 0 1 = 1 / Real.sqrt 3 := by
    unfold A0; rw [hR]; norm_num
  unfold uHat dHat B0
  rw [d0, d1' ]
  simp only [d1 x hx, hA, deriv_const]
  norm_num
  rw [Q2_eq _ _ _ _ _ _ _ _ _ _ hx, Q2_eq _ _ _ _ _ _ _ _ _ _ hx]
  have hs : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  field_simp
  ring

/-! ### The natural-gauge Wigner Jacobi equation `eq:wigner-natural-jacobi` -/

/-- **`eq:wigner-natural-jacobi`** (the Wigner rank recurrence in the natural gauge
`d̂_k = √(2k+1) d^k_{ab}(arccos x)`): `x d̂_k = A_{k+1}^{(0)} d̂_{k+1} + A_k^{(0)} d̂_{k-1} + B_k^{(0)} d̂_k`
for `x ∈ [-1,1]`, `k ≥ 1/2`, and the edge hypothesis at `k = 1/2` as in `contact_identity`
(no hypothesis on `a, b` is needed: off the Wigner lattice all `d` vanish).  Row `k = 0` of the exceptional channel is `wigner_natural_jacobi_zero`.  (The paper's
conventions `A^{(0)}_{k_{min}} := 0`, `B_0^{(0)} := 0` hold by Lean's `x / 0 = 0` and `R_{k_{min}} = 0`.) -/
theorem wigner_natural_jacobi (a b k : ℚ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1)
    (hk : (1 : ℝ) / 2 ≤ k)
    (hedge : (k : ℝ) = 1 / 2 → ((1 : ℝ) / 4 - (a : ℝ) ^ 2) * (1 / 4 - (b : ℝ) ^ 2) = 0) :
    x * dHat a b k x = A0 a b (k + 1) * dHat a b (k + 1) x + A0 a b k * dHat a b (k - 1) x
      + B0 a b k * dHat a b k x := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hσ : 0 < Real.sqrt (2 * (k : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
  have hσ2 : Real.sqrt (2 * (k : ℝ) + 1) ^ 2 = 2 * (k : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have h := wignerSmallDx_rank_rec k a b hx
  have hR0z : (k : ℝ) = 1 / 2 → wigR k a b = 0 := by
    intro hh
    unfold wigR
    have h' : ((k : ℝ) ^ 2 - (b : ℝ) ^ 2) * ((k : ℝ) ^ 2 - (a : ℝ) ^ 2) = 0 := by
      have := hedge hh
      rw [hh]; nlinarith [this, show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num]
    rw [h']; simp
  have E3 : A0 a b (k + 1) * dHat a b (k + 1) x =
      Real.sqrt (2 * (k : ℝ) + 1) * (wigR (k + 1) a b * wignerSmallDx (k + 1) a b x) /
        (((k : ℝ) + 1) * (2 * k + 1)) := by
    have : A0 a b (k + 1) * dHat a b (k + 1) x =
        (A0 a b (k + 1) * Real.sqrt (2 * ((k + 1 : ℚ) : ℝ) + 1)) * wignerSmallDx (k + 1) a b x := by
      unfold dHat; ring
    rw [this, A0_succ_gauge a b k hk0.le]
    generalize wignerSmallDx (k + 1) a b x = q
    generalize Real.sqrt (2 * (k : ℝ) + 1) = σ at *
    have : (k : ℝ) + 1 ≠ 0 := by linarith
    field_simp
    linear_combination (-(wigR (k + 1) a b * q)) * hσ2
  have E4 : A0 a b k * dHat a b (k - 1) x =
      Real.sqrt (2 * (k : ℝ) + 1) * (wigR k a b * wignerSmallDx (k - 1) a b x) /
        ((k : ℝ) * (2 * k + 1)) := by
    by_cases hh : (k : ℝ) = 1 / 2
    · have hA : A0 a b k = 0 := by unfold A0; rw [hR0z hh]; simp
      rw [hA, hR0z hh]; simp
    · have hlt : (1 : ℝ) / 2 < k := lt_of_le_of_ne hk (Ne.symm hh)
      have : A0 a b k * dHat a b (k - 1) x =
          (A0 a b k * Real.sqrt (2 * ((k - 1 : ℚ) : ℝ) + 1)) * wignerSmallDx (k - 1) a b x := by
        unfold dHat; ring
      rw [this, A0_pred_gauge a b k hlt]
      generalize wignerSmallDx (k - 1) a b x = q
      generalize Real.sqrt (2 * (k : ℝ) + 1) = σ at *
      field_simp
      linear_combination (-(wigR k a b * q)) * hσ2
  rw [E3, E4]
  unfold dHat B0
  generalize Real.sqrt (2 * (k : ℝ) + 1) = σ at *
  have hkk : (k : ℝ) + 1 ≠ 0 := by linarith
  have hk2 : 2 * (k : ℝ) + 1 ≠ 0 := by linarith
  field_simp
  linear_combination h

/-- Row `k = 0` of `eq:wigner-natural-jacobi` in the exceptional channel `a = b = 0`:
`x d̂_0 = A_1^{(0)} d̂_1 = d̂_1/√3` (`d_0 = 1`, `d_1 = x`). -/
theorem wigner_natural_jacobi_zero {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    x * dHat 0 0 0 x = A0 0 0 1 * dHat 0 0 1 x := by
  have d0 : wignerSmallDx 0 0 0 x = 1 := by
    unfold wignerSmallDx; exact wignerSmallD_zero_zero_zero _
  have d1 : wignerSmallDx 1 0 0 x = x := by
    unfold wignerSmallDx
    rw [wignerSmallD_one_zero_zero, Real.cos_arccos hx.1 hx.2]
  have hR : wigR 1 0 0 = 1 := by unfold wigR; norm_num
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hA : A0 0 0 1 = 1 / Real.sqrt 3 := by unfold A0; rw [hR]; norm_num
  unfold dHat
  rw [d0, d1, hA]
  norm_num

/-! ### The first-order residual -/

/-- **The `t`-coefficient of the residual `𝓡_k(Û^{[2]})` vanishes** (`prop:general-fixed-rank-contact`,
first assertion; the "if" direction of the paper's reduction, which uses `eq:general-contact-identity`).
Hypotheses (the first-order jets of `(E1)`, and the fixed-rank first-order data of the pullback, all
*assumed*, none derived here): `A_{k+1}(t), A_k(t), B_k(t)` are differentiable at `t = 0` with values the
Wigner coefficients and derivatives `A^{(0)}(λ₁ - ε₁ j²)` (`j = k+1, k`) and `λ₁B_k^{(0)} + β₁κ² + β₂`
(`A_j(h) = A_j^{(0)} e(j²h², h²)`, `B_k(h) = λ B^{(0)} + v(q_k²,h²)`); `Û_j(t)` is differentiable at `0` with
value `d̂_j` and derivative `û_j = √(2j+1) 𝒬_{2,j} d_j`.  Conclusion: the residual
`x Û_k - A_{k+1}Û_{k+1} - A_kÛ_{k-1} - B_kÛ_k` vanishes at `t = 0` and has derivative `0` there, i.e. it is
`o(t)`; the paper's `O_k(t²)` follows when the residual is analytic in `t`. -/
theorem contact_residual_hasDerivAt (a b k : ℚ) (ε β₁ β₂ l₁ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (ha : |(a : ℝ)| ≤ k) (hb : |(b : ℝ)| ≤ k) (hk : (1 : ℝ) / 2 ≤ k)
    (hedge : (k : ℝ) = 1 / 2 → ((1 : ℝ) / 4 - (a : ℝ) ^ 2) * (1 / 4 - (b : ℝ) ^ 2) = 0)
    (Ap Am Bk Up Uk Um : ℝ → ℝ)
    (hAp0 : Ap 0 = A0 a b (k + 1))
    (hAp : HasDerivAt Ap (A0 a b (k + 1) * (l₁ - ε * ((k : ℝ) + 1) ^ 2)) 0)
    (hAm0 : Am 0 = A0 a b k)
    (hAm : HasDerivAt Am (A0 a b k * (l₁ - ε * (k : ℝ) ^ 2)) 0)
    (hB0 : Bk 0 = B0 a b k)
    (hB : HasDerivAt Bk (l₁ * B0 a b k + (β₁ * ((k : ℝ) + 1 / 2) ^ 2 + β₂)) 0)
    (hUp0 : Up 0 = dHat a b (k + 1) x) (hUp : HasDerivAt Up (uHat a b (k + 1) ε β₁ β₂ l₁ x) 0)
    (hUk0 : Uk 0 = dHat a b k x) (hUk : HasDerivAt Uk (uHat a b k ε β₁ β₂ l₁ x) 0)
    (hUm0 : Um 0 = dHat a b (k - 1) x) (hUm : HasDerivAt Um (uHat a b (k - 1) ε β₁ β₂ l₁ x) 0) :
    (x * Uk 0 - Ap 0 * Up 0 - Am 0 * Um 0 - Bk 0 * Uk 0 = 0) ∧
    HasDerivAt (fun t => x * Uk t - Ap t * Up t - Am t * Um t - Bk t * Uk t) 0 0 := by
  have hJ := wigner_natural_jacobi a b k (Ioo_subset_Icc_self hx) hk hedge
  have hC := contact_identity a b k ε β₁ β₂ l₁ hx ha hb hk hedge
  refine ⟨?_, ?_⟩
  · rw [hAp0, hAm0, hB0, hUp0, hUk0, hUm0]; linarith
  · have h := (((hUk.const_mul x).sub (hAp.mul hUp)).sub (hAm.mul hUm)).sub (hB.mul hUk)
    refine h.congr_deriv ?_
    rw [hAp0, hAm0, hB0, hUp0, hUk0, hUm0]
    linear_combination hC + l₁ * hJ

/-! ### Instances and the two transparent parts -/

/-- **Hahn instance** (`eq:hahn-class-data`: `ε₁ = 1/2`, `β₁ = β₂ = λ₁ = 0`): the contact source is
`-½[(k+1)² A_{k+1}^{(0)} d̂_{k+1} + k² A_k^{(0)} d̂_{k-1}]`, with no `d̂_k` term. -/
theorem contact_identity_hahn (a b k : ℚ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (ha : |(a : ℝ)| ≤ k) (hb : |(b : ℝ)| ≤ k) (hk : (1 : ℝ) / 2 ≤ k)
    (hedge : (k : ℝ) = 1 / 2 → ((1 : ℝ) / 4 - (a : ℝ) ^ 2) * (1 / 4 - (b : ℝ) ^ 2) = 0) :
    x * uHat a b k (1 / 2) 0 0 0 x - A0 a b (k + 1) * uHat a b (k + 1) (1 / 2) 0 0 0 x
        - A0 a b k * uHat a b (k - 1) (1 / 2) 0 0 0 x - B0 a b k * uHat a b k (1 / 2) 0 0 0 x =
      -(1 / 2) * (((k : ℝ) + 1) ^ 2 * A0 a b (k + 1) * dHat a b (k + 1) x
          + (k : ℝ) ^ 2 * A0 a b k * dHat a b (k - 1) x) := by
  have := contact_identity a b k (1 / 2) 0 0 0 hx ha hb hk hedge
  linear_combination this

/-- **Racah instance** (`eq:racah-class-data`: `ε₁ = ρ`, `β₁ = w/4`, `β₂ = (1/2-m²-n²)w/8`, `λ₁ = 0`, with
`ρ = (α⁻²+β⁻²)/8`, `w = 1/(αβ)`, offsets `(a,b) = (m,n)`): the diagonal source is
`δ_k^{(6)} = β₁κ² + β₂ = (2k(k+1)+1-m²-n²) w/8` (`A:1550`). -/
theorem contact_identity_racah (a b k : ℚ) (ρ w : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (ha : |(a : ℝ)| ≤ k) (hb : |(b : ℝ)| ≤ k) (hk : (1 : ℝ) / 2 ≤ k)
    (hedge : (k : ℝ) = 1 / 2 → ((1 : ℝ) / 4 - (a : ℝ) ^ 2) * (1 / 4 - (b : ℝ) ^ 2) = 0) :
    x * uHat a b k ρ (w / 4) ((1 / 2 - (a : ℝ) ^ 2 - (b : ℝ) ^ 2) * w / 8) 0 x
        - A0 a b (k + 1) * uHat a b (k + 1) ρ (w / 4) ((1 / 2 - (a : ℝ) ^ 2 - (b : ℝ) ^ 2) * w / 8) 0 x
        - A0 a b k * uHat a b (k - 1) ρ (w / 4) ((1 / 2 - (a : ℝ) ^ 2 - (b : ℝ) ^ 2) * w / 8) 0 x
        - B0 a b k * uHat a b k ρ (w / 4) ((1 / 2 - (a : ℝ) ^ 2 - (b : ℝ) ^ 2) * w / 8) 0 x =
      -ρ * (((k : ℝ) + 1) ^ 2 * A0 a b (k + 1) * dHat a b (k + 1) x
          + (k : ℝ) ^ 2 * A0 a b k * dHat a b (k - 1) x)
        + (2 * (k : ℝ) * (k + 1) + 1 - (a : ℝ) ^ 2 - (b : ℝ) ^ 2) * w / 8 * dHat a b k x := by
  have := contact_identity a b k ρ (w / 4) ((1 / 2 - (a : ℝ) ^ 2 - (b : ℝ) ^ 2) * w / 8) 0 hx ha hb hk hedge
  linear_combination this

/-- The `β₂` part of `𝒬_{2,k}` (proof of `prop:general-fixed-rank-contact`, "the `β₂` part is
transparent"): for `ε₁ = β₁ = λ₁ = 0`, `χ = 0`, `ρ₂₀ = β₂ s^{-1/2}` and
`𝒬_{2,k} = β₂ (-∂_x + x/(2s))`, independent of `k`. -/
theorem Q2_beta2_part (a b κ β₂ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (d dp : ℝ) :
    Q2 a b κ 0 0 β₂ 0 0 x d dp = β₂ * (-dp + x / (2 * (1 - x ^ 2)) * d) := by
  have hs : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [Q2_eq _ _ _ _ _ _ _ _ _ _ hx]
  field_simp
  ring

/-- The `λ₁` part of `𝒬_{2,k}`: for `ε₁ = β₁ = β₂ = 0`, `𝒬_{2,k} = λ₁ (-x ∂_x + x²/(2s))` (the shift
`β₂ ↦ λ₁ x`; `χ = 0`). -/
theorem Q2_lam1_part (a b κ l₁ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (d dp : ℝ) :
    Q2 a b κ 0 0 0 l₁ 0 x d dp = l₁ * (-x * dp + x ^ 2 / (2 * (1 - x ^ 2)) * d) := by
  have hs : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [Q2_eq _ _ _ _ _ _ _ _ _ _ hx]
  field_simp
  ring

/-- info: 'FormalResearch.Racah.contact_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contact_identity

/-- info: 'FormalResearch.Racah.contact_identity_exceptional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contact_identity_exceptional

/-- info: 'FormalResearch.Racah.wigner_natural_jacobi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wigner_natural_jacobi

/-- info: 'FormalResearch.Racah.wigner_natural_jacobi_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wigner_natural_jacobi_zero

/-- info: 'FormalResearch.Racah.contact_residual_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contact_residual_hasDerivAt

/-- info: 'FormalResearch.Racah.contact_identity_hahn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contact_identity_hahn

/-- info: 'FormalResearch.Racah.contact_identity_racah' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contact_identity_racah

end FormalResearch.Racah
