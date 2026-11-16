module

public import FormalResearch.Special.DiscreteAiryPhysHahn
public import FormalResearch.Special.DiscreteAiryLimitChains2Racah

/-!
# The actual Wigner `6j` chain: the unified Airy matching on the whole macroscopic window

The `6j` analogue of `DiscreteAiryPhysChains`: composition of `airy_full_compose` (`DiscreteAiryPhysHahn`) with the identification
`racah_class_chain` / `racah_class_chain_neg` (the actual natural-gauge `6j` chain, resp. its `(-1)^k` twist, solves every row `k ≥ 1`
of the closed-form centred Racah recurrence), the Gauss-weight bound `racah_chain_abs_le`, and the geometric turn
`racah_turn_geom_pos/_neg` (`DiscreteAiryLimitChains2Racah`).

* `racah_chain_airy_full_pos/_neg`: shape data `α, β > 0`, `x ∈ (-1,1)` with `(α - βx)(β - αx) < 0` (`τ = +1`) resp. `> 0` (`τ = -1`,
  twisted chain); for every finite Racah system, physical `c`, scale `h = δ³ ≤ δ₀³` with `A h = α`, `B h = β`, `cosA = x`:
  `AiryFullAt` (window `q_k ∈ [q_* - r, q_* + r/2]`, `q_* = 2αβ√(1-x²)/γ`, unified `DaiFull`, and `Ŷ_k = κ g Ai + μ g Bi` up to
  `C δ³ (|κ| airyWt + |μ| airyBiWt)` on all of `[J, N+1]`, `|μ| ≤ Cmu Y_max e^{-ξ₀/δ³}/δ`, `Y_max = √(4AB/(2C))`);
* `racah_chain_airy_full_family_pos/_neg`: along infinitely many integer realisations (`racah_realisation`).

**Claim class: proved** (integer data); same hypotheses and caveats as `DiscreteAiryPhysChains` (`κ` and `κ ≠ 0` not asserted, uniformity in
`(α, β, x)` not shown, `r ≤ q_*/4` the radius of the Langer chart).  Half-integer data (`DiscreteAiryLimitChains2Half6j*`) is not carried
over.
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **Airy limit of the actual `6j` chain from the geometric data, `τ = +1`** (`thm:racahAiryConnection`, no turn
hypotheses). -/
theorem racah_chain_airy_full_pos (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : (α - β * x) * (β - α * x) < 0) (m n : ℤ) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ (i : Fin (D' + 1))
        (h : ℝ), (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → 0 < h → h ≤ δ0 ^ 3 →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        AiryFullAt (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (m : ℝ) (n : ℝ) (racah6jY a b c m n)
          (Real.sqrt (4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ)))) r δ0 C Cmu ξ0 h := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_pos hα hβ hx1 hx2 hprod
  obtain ⟨r, δ0, C, Cmu, ξ0, hr, -, hδ0, hC, hCmu, hξ0, H⟩ :=
    airy_full_compose (P := 1 / (4 * α ^ 2)) (Q := 1 / (4 * β ^ 2)) (by positivity) (by positivity) (m : ℝ) (n : ℝ) 1 x
      (racahQs α β x) hqs (by norm_num) hκ hαq hβq hturn
  refine ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, ?_⟩
  intro a b c D' hsys i h hc hh hhδ hAh hBh hx
  have hA : 0 < wA (a : ℚ) (n : ℚ) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hB : 0 < wB (b : ℚ) (m : ℚ) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  refine H h (racah6jY a b c m n) _ hh hhδ (fun k hk => ?_) (fun k => racah_chain_abs_le a b c m n hsys i hc k)
  have := racah_class_chain a b c m n h hh hA hB k hk
  rw [hAh, hBh, hx] at this
  exact this

/-- **Airy limit of the actual `6j` chain from the geometric data, `τ = -1`** (the twisted chain `(-1)^k Ŷ_k`). -/
theorem racah_chain_airy_full_neg (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : 0 < (α - β * x) * (β - α * x)) (m n : ℤ) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ (i : Fin (D' + 1))
        (h : ℝ), (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → 0 < h → h ≤ δ0 ^ 3 →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        AiryFullAt (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (m : ℝ) (n : ℝ)
          (fun j => (-1 : ℝ) ^ j * racah6jY a b c m n j)
          (Real.sqrt (4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ)))) r δ0 C Cmu ξ0 h := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_neg hα hβ hx1 hx2 hprod
  obtain ⟨r, δ0, C, Cmu, ξ0, hr, -, hδ0, hC, hCmu, hξ0, H⟩ :=
    airy_full_compose (P := 1 / (4 * α ^ 2)) (Q := 1 / (4 * β ^ 2)) (by positivity) (by positivity) (m : ℝ) (n : ℝ) (-1) x
      (racahQs α β x) hqs (by norm_num) hκ hαq hβq hturn
  refine ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, ?_⟩
  intro a b c D' hsys i h hc hh hhδ hAh hBh hx
  have hA : 0 < wA (a : ℚ) (n : ℚ) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hB : 0 < wB (b : ℚ) (m : ℚ) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  refine H h _ _ hh hhδ (fun k hk => ?_) (fun k => ?_)
  · have := racah_class_chain_neg a b c m n h hh hA hB k hk
    rw [hAh, hBh, hx] at this
    exact this
  · have h1 : |(-1 : ℝ) ^ k| = 1 := by simp [abs_zpow]
    rw [abs_mul, h1, one_mul]
    exact racah_chain_abs_le a b c m n hsys i hc k

/-- **The Airy limit of the actual `6j` chain along infinitely many realisations, `τ = +1`** (`R² < |P²-Q²|`, e.g.
`(P,Q,R) = (6,2,5)`, `α/β = 3`, `x = 5/8`; `m = n = -1`). -/
theorem racah_chain_airy_full_family_pos (P Q R m n : ℤ) (hRlo : |P - Q| < R) (hRhi : R < P + Q)
    (hpR : Odd R) (hpP : Even (P - n - 1)) (hpQ : Even (Q - m - 1))
    (hang : (R : ℝ) ^ 2 < |(P : ℝ) ^ 2 - (Q : ℝ) ^ 2|) (α : ℝ) (hα : 0 < α) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧ ∀ ε : ℝ, 0 < ε → ∃ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' ∧
        ∃ (i : Fin (D' + 1)) (h : ℝ), (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i ∧ 0 < h ∧ h ≤ ε ∧
          wA (a : ℚ) (n : ℚ) * h = α ∧ wB (b : ℚ) (m : ℚ) * h = α * Q / P ∧
          cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) =
            ((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q) ∧
          AiryFullAt (1 / (4 * α ^ 2)) (1 / (4 * (α * Q / P) ^ 2)) 1 (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))
            (racahQs α (α * Q / P) (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) (m : ℝ) (n : ℝ) (racah6jY a b c m n)
            (Real.sqrt (4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ)))) r δ0 C Cmu ξ0 h := by
  obtain ⟨⟨hP, hQ, hR⟩, hx1, hx2, hprod⟩ := racah_family_geom P Q R hRlo hRhi α
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hβ : 0 < α * Q / P := by positivity
  have hneg : (α - α * Q / P * (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) *
      (α * Q / P - α * (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) < 0 := by
    rw [hprod]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have h1 : (R : ℝ) ^ 4 < ((P : ℝ) ^ 2 - Q ^ 2) ^ 2 := by
      have := sq_lt_sq' (by linarith [abs_nonneg ((P : ℝ) ^ 2 - Q ^ 2), sq_nonneg (R : ℝ)] :
        -|(P : ℝ) ^ 2 - (Q : ℝ) ^ 2| < (R : ℝ) ^ 2) hang
      rw [sq_abs] at this
      nlinarith
    have : 0 < α ^ 2 := by positivity
    nlinarith
  obtain ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, H⟩ :=
    racah_chain_airy_full_pos α (α * Q / P) _ hα hβ hx1 hx2 hneg m n
  refine ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, ?_⟩
  intro ε hε
  obtain ⟨a, b, c, D', hsys, i, h, hc, hh, hhε, hAh, hBh, hx⟩ :=
    racah_realisation P Q R m n hP hQ hRlo hRhi hpR hpP hpQ α (min ε (δ0 ^ 3)) hα (lt_min hε (by positivity))
  exact ⟨a, b, c, D', hsys, i, h, hc, hh, hhε.trans (min_le_left _ _), hAh, hBh, hx,
    H a b c D' hsys i h hc hh (hhε.trans (min_le_right _ _)) hAh hBh hx⟩

/-- **The Airy limit of the actual `6j` chain along infinitely many realisations, `τ = -1`** (`R² > |P²-Q²|`; the
twisted chain `(-1)^k Ŷ_k`). -/
theorem racah_chain_airy_full_family_neg (P Q R m n : ℤ) (hRlo : |P - Q| < R) (hRhi : R < P + Q)
    (hpR : Odd R) (hpP : Even (P - n - 1)) (hpQ : Even (Q - m - 1))
    (hang : |(P : ℝ) ^ 2 - (Q : ℝ) ^ 2| < (R : ℝ) ^ 2) (α : ℝ) (hα : 0 < α) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧ ∀ ε : ℝ, 0 < ε → ∃ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' ∧
        ∃ (i : Fin (D' + 1)) (h : ℝ), (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i ∧ 0 < h ∧ h ≤ ε ∧
          wA (a : ℚ) (n : ℚ) * h = α ∧ wB (b : ℚ) (m : ℚ) * h = α * Q / P ∧
          cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) =
            ((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q) ∧
          AiryFullAt (1 / (4 * α ^ 2)) (1 / (4 * (α * Q / P) ^ 2)) (-1) (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))
            (racahQs α (α * Q / P) (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) (m : ℝ) (n : ℝ)
            (fun j => (-1 : ℝ) ^ j * racah6jY a b c m n j)
            (Real.sqrt (4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ)))) r δ0 C Cmu ξ0 h := by
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
  obtain ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, H⟩ :=
    racah_chain_airy_full_neg α (α * Q / P) _ hα hβ hx1 hx2 hpos m n
  refine ⟨r, δ0, C, Cmu, ξ0, hr, hδ0, hC, hCmu, hξ0, ?_⟩
  intro ε hε
  obtain ⟨a, b, c, D', hsys, i, h, hc, hh, hhε, hAh, hBh, hx⟩ :=
    racah_realisation P Q R m n hP hQ hRlo hRhi hpR hpP hpQ α (min ε (δ0 ^ 3)) hα (lt_min hε (by positivity))
  exact ⟨a, b, c, D', hsys, i, h, hc, hh, hhε.trans (min_le_left _ _), hAh, hBh, hx,
    H a b c D' hsys i h hc hh (hhε.trans (min_le_right _ _)) hAh hBh hx⟩

/-- info: 'FormalResearch.Special.racah_chain_airy_full_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_airy_full_pos

/-- info: 'FormalResearch.Special.racah_chain_airy_full_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_airy_full_neg

/-- info: 'FormalResearch.Special.racah_chain_airy_full_family_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_airy_full_family_pos

/-- info: 'FormalResearch.Special.racah_chain_airy_full_family_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_airy_full_family_neg

end FormalResearch.Special
