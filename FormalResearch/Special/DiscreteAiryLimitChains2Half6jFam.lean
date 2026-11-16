module

public import FormalResearch.Special.DiscreteAiryLimitChains2Half6j

/-!
# Realisations of the half-integer `6j` chain: infinitely many `(a, b, c)` for a given triangle direction

Half-integer data `m_ = m + ½`, `n_ = n + ½` (`m, n ∈ ℤ`), integer `a, b, c`; `4A = 4a + 2n + 3`, `4B = 4b + 2m + 3`
(odd) and `4C = 4c + 2 ≡ 2 (mod 4)`.  A direction `(P : Q : R)` of an integral triangle is realised by
`(4A, 4B, 4C) = t (P, Q, R)`, `t = t₀ + 4u`, exactly when `t₀ P ≡ 2n+3`, `t₀ Q ≡ 2m+3`, `t₀ R ≡ 2 (mod 4)`.
(Necessity for a primitive `(P,Q,R)`: `t = gcd` is odd since `4A` is, hence `P, Q` odd, `R ≡ 2 (mod 4)` and `t ≡ (2n+3)P ≡
(2m+3)Q (mod 4)`; elementary, not formalised.  Directions with `R ≢ 2 (mod 4)` or `P` even never occur.)

## Results (proved)

* `racah_family_ints_half`, `racah_realisation_half`: for `α, ε > 0` there are integers `a, b, c`, a finite Racah system
  `RacahSystem a b m_ n_ D'`, a physical `c = c_i` and `0 < h ≤ ε` with `A h = α`, `B h = αQ/P`,
  `cosA A B C = (P²+Q²-R²)/(2PQ)`: `a = (tP-2n-3)/4`, `b = (tQ-2m-3)/4`, `c = (tR-2)/4`, `h = 4α/(tP)`.
* `racah_chain_airy_family_half_pos/_neg`: composition with `racah_chain_airy_geom_half_pos/_neg`: the half-integer Airy
  conclusion `AiryOutHalf` holds for every realisation with the same constants; `τ = +1` iff `R² < |P²-Q²|`.
  Example: `(P,Q,R) = (11,3,10)`, `m = n = 0`, `t₀ = 1`: `(a,b,c) = (2,0,2)` for `t = 1`, `τ = +1`
  (`R² = 100 < 112 = |P²-Q²|`); `(5,3,6)`, `m = 0`, `n = 1`: `τ = -1`.

Claim class: **proved**.  Not formalised: `κ`, uniformity, mixed-parity labels.
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner
  FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The explicit family `(4A, 4B, 4C) = (t₀ + 4u)(P, Q, R)`. -/
theorem racah_family_ints_half (P Q R m n t0 : ℤ) (hRlo : |P - Q| < R) (hRhi : R < P + Q) (ht0 : 0 < t0)
    (hP4 : t0 * P ≡ 2 * n + 3 [ZMOD 4]) (hQ4 : t0 * Q ≡ 2 * m + 3 [ZMOD 4]) (hR4 : t0 * R ≡ 2 [ZMOD 4]) (u : ℕ)
    (hu : 2 * |m - n| + 2 * |m + n + 1| + 2 ≤ t0 + 4 * (u : ℤ)) :
    ∃ (a b c : ℤ) (D' : ℕ), wA (a : ℚ) ((n : ℚ) + 1 / 2) = ((t0 : ℝ) + 4 * u) * P / 4 ∧
      wB (b : ℚ) ((m : ℚ) + 1 / 2) = ((t0 : ℝ) + 4 * u) * Q / 4 ∧ wC (c : ℚ) = ((t0 : ℝ) + 4 * u) * R / 4 ∧
      RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' ∧
      ∃ i : Fin (D' + 1), (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i := by
  obtain ⟨wa, hwa⟩ := (Int.modEq_iff_dvd.1 hP4.symm)
  obtain ⟨wb, hwb⟩ := (Int.modEq_iff_dvd.1 hQ4.symm)
  obtain ⟨wc, hwc⟩ := (Int.modEq_iff_dvd.1 hR4.symm)
  set a : ℤ := u * P + wa with ha
  set b : ℤ := u * Q + wb with hb
  set c : ℤ := u * R + wc with hc
  set t : ℚ := (t0 : ℚ) + 4 * u with htdef
  have hwaq : (t0 : ℚ) * P - (2 * n + 3) = 4 * wa := by exact_mod_cast hwa
  have hwbq : (t0 : ℚ) * Q - (2 * m + 3) = 4 * wb := by exact_mod_cast hwb
  have hwcq : (t0 : ℚ) * R - 2 = 4 * wc := by exact_mod_cast hwc
  have hAq : (a : ℚ) + (((n : ℚ) + 1 / 2) + 1) / 2 = t * P / 4 := by
    rw [ha, htdef]; push_cast; linarith
  have hBq : (b : ℚ) + (((m : ℚ) + 1 / 2) + 1) / 2 = t * Q / 4 := by
    rw [hb, htdef]; push_cast; linarith
  have hCq : (c : ℚ) = (t * R - 2) / 4 := by
    rw [hc, htdef]; push_cast; linarith
  have hlab : RacahLabels (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) :=
    ⟨⟨2 * a, by push_cast; ring⟩, ⟨2 * b, by push_cast; ring⟩, ⟨2 * m + 1, by push_cast; ring⟩, ⟨m - n, by push_cast; ring⟩⟩
  have hu' : (0 : ℚ) < t := by
    have h0 : (0 : ℤ) < t0 + 4 * u := by
      have := abs_nonneg (m - n); have := abs_nonneg (m + n + 1); omega
    have : (0 : ℚ) < ((t0 + 4 * u : ℤ) : ℚ) := by exact_mod_cast h0
    rw [htdef]; push_cast at this; exact this
  have h1 : (P : ℚ) - Q ≤ R - 1 := by
    have : P - Q ≤ R - 1 := by have := abs_lt.1 hRlo; omega
    exact_mod_cast this
  have h2 : -((R : ℚ) - 1) ≤ P - Q := by
    have : -(R - 1) ≤ P - Q := by have := abs_lt.1 hRlo; omega
    exact_mod_cast this
  have h3 : (1 : ℚ) ≤ P + Q - R := by
    have : 1 ≤ P + Q - R := by omega
    exact_mod_cast this
  have hmn : 2 * |(m : ℚ) - n| + 2 * |(m : ℚ) + n + 1| + 2 ≤ t := by
    have : ((2 * |m - n| + 2 * |m + n + 1| + 2 : ℤ) : ℚ) ≤ ((t0 + 4 * u : ℤ) : ℚ) := by exact_mod_cast hu
    rw [htdef]; push_cast at this; exact this
  have hlow : cMin (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) ≤ (c : ℚ) := by
    rw [cMin_centered, hAq, hBq, hCq]
    have hab : |t * P / 4 - t * Q / 4| ≤ t * (R - 1) / 4 := by
      rw [abs_le]; constructor <;> nlinarith
    have e : |((m : ℚ) + 1 / 2) - ((n : ℚ) + 1 / 2)| = |(m : ℚ) - n| := by congr 1; ring
    rw [e]
    have := abs_nonneg ((m : ℚ) + n + 1)
    have := abs_nonneg ((m : ℚ) - n)
    nlinarith
  have hup : (c : ℚ) ≤ cMax (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) := by
    rw [cMax_centered, hAq, hBq, hCq]
    have e : |((m : ℚ) + 1 / 2) + ((n : ℚ) + 1 / 2)| = |(m : ℚ) + n + 1| := by congr 1; ring
    rw [e]
    have := abs_nonneg ((m : ℚ) + n + 1)
    have := abs_nonneg ((m : ℚ) - n)
    nlinarith
  obtain ⟨D', hsys⟩ := RacahSystem.exists hlab (hlow.trans hup)
  refine ⟨a, b, c, D', ?_, ?_, ?_, hsys, ?_⟩
  · unfold wA
    have e : ((a : ℚ) : ℝ) + ((((n : ℚ) + 1 / 2 : ℚ) : ℝ) + 1) / 2 = (((t * P / 4 : ℚ)) : ℝ) := by
      rw [← hAq]; push_cast; ring
    push_cast at e ⊢
    rw [htdef] at e
    push_cast at e
    linarith
  · unfold wB
    have e : ((b : ℚ) : ℝ) + ((((m : ℚ) + 1 / 2 : ℚ) : ℝ) + 1) / 2 = (((t * Q / 4 : ℚ)) : ℝ) := by
      rw [← hBq]; push_cast; ring
    push_cast at e ⊢
    rw [htdef] at e
    push_cast at e
    linarith
  · unfold wC
    have e : ((c : ℚ) : ℝ) = (((t * R - 2) / 4 : ℚ) : ℝ) := by rw [hCq]
    rw [htdef] at e
    push_cast at e ⊢
    linarith
  · obtain ⟨z, hz⟩ : ∃ z : ℤ, cMin (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) = (z : ℚ) := by
      refine ⟨max |a - b| |b + m - a - n|, ?_⟩
      have e : (b : ℚ) + ((m : ℚ) + 1 / 2) - a - ((n : ℚ) + 1 / 2) = (b : ℚ) + m - a - n := by ring
      unfold cMin
      rw [e]; push_cast; rfl
    have hcz : 0 ≤ c - z := by
      have : (z : ℚ) ≤ (c : ℚ) := hz ▸ hlow
      have : z ≤ c := by exact_mod_cast this
      omega
    have hD : (D' : ℚ) = cMax (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) -
        cMin (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) := hsys.dim
    have hi : ((c - z).toNat : ℚ) = (c : ℚ) - z := by
      have : (((c - z).toNat : ℕ) : ℤ) = c - z := Int.toNat_of_nonneg hcz
      have h4 : ((((c - z).toNat : ℕ) : ℤ) : ℚ) = ((c - z : ℤ) : ℚ) := by rw [this]
      push_cast at h4
      exact h4
    have hlt : (c - z).toNat < D' + 1 := by
      have : ((c - z).toNat : ℚ) ≤ D' := by rw [hi, hD, hz]; linarith
      have : (c - z).toNat ≤ D' := by exact_mod_cast this
      omega
    refine ⟨⟨(c - z).toNat, hlt⟩, ?_⟩
    unfold cPt
    show (c : ℚ) = cMin (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) + (((c - z).toNat : ℕ) : ℚ)
    rw [hi, hz]; ring

/-- **Realisations with `A h = α`, `B h = αQ/P`, `cosA A B C = (P²+Q²-R²)/(2PQ)` at arbitrarily small `h`
(half-integer `m_, n_`).** -/
theorem racah_realisation_half (P Q R m n t0 : ℤ) (hRlo : |P - Q| < R) (hRhi : R < P + Q) (ht0 : 0 < t0)
    (hP4 : t0 * P ≡ 2 * n + 3 [ZMOD 4]) (hQ4 : t0 * Q ≡ 2 * m + 3 [ZMOD 4]) (hR4 : t0 * R ≡ 2 [ZMOD 4])
    (α ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    ∃ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' ∧
      ∃ (i : Fin (D' + 1)) (h : ℝ), (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i ∧ 0 < h ∧
        h ≤ ε ∧ wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α ∧ wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = α * Q / P ∧
        cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) =
          ((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q) := by
  have h0 := abs_nonneg (P - Q)
  have hl := abs_lt.1 hRlo
  have hP : 0 < P := by omega
  have hQ : 0 < Q := by omega
  have hR : 0 < R := by omega
  obtain ⟨T, hT⟩ := exists_nat_gt (α / (P * ε))
  obtain ⟨a, b, c, D', hA, hB, hC, hsys, i, hi⟩ :=
    racah_family_ints_half P Q R m n t0 hRlo hRhi ht0 hP4 hQ4 hR4
      (2 * |m - n| + 2 * |m + n + 1| + 2 + T).toNat
      (by have h0 : 0 ≤ 2 * |m - n| + 2 * |m + n + 1| + 2 + (T : ℤ) := by positivity
          rw [Int.toNat_of_nonneg h0]; have := abs_nonneg (m - n); have := abs_nonneg (m + n + 1); omega)
  set u : ℕ := (2 * |m - n| + 2 * |m + n + 1| + 2 + T).toNat with hudef
  have hu : (T : ℝ) ≤ u := by
    have h0 : 0 ≤ 2 * |m - n| + 2 * |m + n + 1| + 2 + (T : ℤ) := by positivity
    have : ((u : ℕ) : ℤ) = 2 * |m - n| + 2 * |m + n + 1| + 2 + T := Int.toNat_of_nonneg h0
    have h5 : (T : ℤ) ≤ (u : ℤ) := by
      rw [this]; have := abs_nonneg (m - n); have := abs_nonneg (m + n + 1); omega
    exact_mod_cast h5
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have ht0r : (0 : ℝ) < t0 := by exact_mod_cast ht0
  have htpos : (0 : ℝ) < (t0 : ℝ) + 4 * u := by positivity
  refine ⟨a, b, c, D', hsys, i, 4 * α / (((t0 : ℝ) + 4 * u) * P), hi, by positivity, ?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have h1 : α / (P * ε) < T := hT
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith
  · rw [hA]; field_simp
  · rw [hB]; field_simp
  · rw [hA, hB, hC]
    unfold cosA
    field_simp

/-- **The Airy limit of the actual half-integer `6j` chain along infinitely many realisations, `τ = +1`**
(`R² < |P²-Q²|`). -/
theorem racah_chain_airy_family_half_pos (P Q R m n t0 : ℤ) (hRlo : |P - Q| < R) (hRhi : R < P + Q) (ht0 : 0 < t0)
    (hP4 : t0 * P ≡ 2 * n + 3 [ZMOD 4]) (hQ4 : t0 * Q ≡ 2 * m + 3 [ZMOD 4]) (hR4 : t0 * R ≡ 2 [ZMOD 4])
    (hang : (R : ℝ) ^ 2 < |(P : ℝ) ^ 2 - (Q : ℝ) ^ 2|) (α : ℝ) (hα : 0 < α) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧ ∀ ε : ℝ, 0 < ε → ∃ (a b c : ℤ) (D' : ℕ),
        RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' ∧
        ∃ (i : Fin (D' + 1)) (h : ℝ), (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i ∧ 0 < h ∧
          h ≤ ε ∧ wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α ∧ wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = α * Q / P ∧
          cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) =
            ((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q) ∧
          AiryOutHalf (1 / (4 * α ^ 2)) (1 / (4 * (α * Q / P) ^ 2)) 1 (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))
            (racahQs α (α * Q / P) (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) (racah6jYH a b c m n)
            (Real.sqrt (4 * wA (a : ℚ) ((n : ℚ) + 1 / 2) * wB (b : ℚ) ((m : ℚ) + 1 / 2) / (2 * wC (c : ℚ))))
            A0 r δ0 C Cosc Ctop W Cmu ξ0 D h := by
  obtain ⟨⟨hP, hQ, hR⟩, hx1, hx2, hprod⟩ := racah_family_geom P Q R hRlo hRhi α
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hβ : 0 < α * Q / P := by positivity
  have hneg : (α - α * Q / P * (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) *
      (α * Q / P - α * (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) < 0 := by
    rw [hprod]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have h1 : (R : ℝ) ^ 4 < ((P : ℝ) ^ 2 - Q ^ 2) ^ 2 := by
      have := sq_lt_sq' (by linarith [abs_nonneg ((P : ℝ) ^ 2 - (Q : ℝ) ^ 2), sq_nonneg (R : ℝ)] :
        -|(P : ℝ) ^ 2 - (Q : ℝ) ^ 2| < (R : ℝ) ^ 2) hang
      rw [sq_abs] at this
      nlinarith
    have : 0 < α ^ 2 := by positivity
    nlinarith
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    racah_chain_airy_geom_half_pos α (α * Q / P) _ hα hβ hx1 hx2 hneg m n A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro ε hε
  obtain ⟨a, b, c, D', hsys, i, h, hc, hh, hhε, hAh, hBh, hx⟩ :=
    racah_realisation_half P Q R m n t0 hRlo hRhi ht0 hP4 hQ4 hR4 α (min ε (δ0 ^ 3)) hα (lt_min hε (by positivity))
  exact ⟨a, b, c, D', hsys, i, h, hc, hh, hhε.trans (min_le_left _ _), hAh, hBh, hx,
    H a b c D' hsys i h hc hh (hhε.trans (min_le_right _ _)) hAh hBh hx⟩

/-- **The same, `τ = -1`** (`R² > |P²-Q²|`; twisted chain). -/
theorem racah_chain_airy_family_half_neg (P Q R m n t0 : ℤ) (hRlo : |P - Q| < R) (hRhi : R < P + Q) (ht0 : 0 < t0)
    (hP4 : t0 * P ≡ 2 * n + 3 [ZMOD 4]) (hQ4 : t0 * Q ≡ 2 * m + 3 [ZMOD 4]) (hR4 : t0 * R ≡ 2 [ZMOD 4])
    (hang : |(P : ℝ) ^ 2 - (Q : ℝ) ^ 2| < (R : ℝ) ^ 2) (α : ℝ) (hα : 0 < α) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧ ∀ ε : ℝ, 0 < ε → ∃ (a b c : ℤ) (D' : ℕ),
        RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' ∧
        ∃ (i : Fin (D' + 1)) (h : ℝ), (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i ∧ 0 < h ∧
          h ≤ ε ∧ wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α ∧ wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = α * Q / P ∧
          cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) =
            ((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q) ∧
          AiryOutHalf (1 / (4 * α ^ 2)) (1 / (4 * (α * Q / P) ^ 2)) (-1) (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))
            (racahQs α (α * Q / P) (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q)))
            (fun j => (-1 : ℝ) ^ j * racah6jYH a b c m n j)
            (Real.sqrt (4 * wA (a : ℚ) ((n : ℚ) + 1 / 2) * wB (b : ℚ) ((m : ℚ) + 1 / 2) / (2 * wC (c : ℚ))))
            A0 r δ0 C Cosc Ctop W Cmu ξ0 D h := by
  obtain ⟨⟨hP, hQ, hR⟩, hx1, hx2, hprod⟩ := racah_family_geom P Q R hRlo hRhi α
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hβ : 0 < α * Q / P := by positivity
  have hpos : 0 < (α - α * Q / P * (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) *
      (α * Q / P - α * (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) := by
    rw [hprod]
    apply div_pos _ (by positivity)
    have h1 : ((P : ℝ) ^ 2 - Q ^ 2) ^ 2 < (R : ℝ) ^ 4 := by
      have h2 := abs_lt.1 hang
      have := sq_lt_sq' h2.1 h2.2
      nlinarith
    have : 0 < α ^ 2 := by positivity
    nlinarith
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    racah_chain_airy_geom_half_neg α (α * Q / P) _ hα hβ hx1 hx2 hpos m n A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro ε hε
  obtain ⟨a, b, c, D', hsys, i, h, hc, hh, hhε, hAh, hBh, hx⟩ :=
    racah_realisation_half P Q R m n t0 hRlo hRhi ht0 hP4 hQ4 hR4 α (min ε (δ0 ^ 3)) hα (lt_min hε (by positivity))
  exact ⟨a, b, c, D', hsys, i, h, hc, hh, hhε.trans (min_le_left _ _), hAh, hBh, hx,
    H a b c D' hsys i h hc hh (hhε.trans (min_le_right _ _)) hAh hBh hx⟩

/-- info: 'FormalResearch.Special.racah_realisation_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_realisation_half

/-- info: 'FormalResearch.Special.racah_chain_airy_family_half_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_chain_airy_family_half_pos

/-- info: 'FormalResearch.Special.racah_chain_airy_family_half_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_chain_airy_family_half_neg

end FormalResearch.Special
