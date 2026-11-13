module

public import FormalResearch.Racah.P2AnalyticCarrier3jSeed

/-!
# The square-root-free `3j` carrier: the identity at every admissible point (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `lem:sqrtfreecarrier`
(`eq:sqrtfreecarrier`, `eq:3jrankpoly`, Appendix G).

`Phi3j_carrier` is the identity `Φ_L^{M,σ} = E_N W_{3j} Π_L^{-1/2} P̃_L` on the physical lattice, in
every chamber, for every rank `L = L₀ + k`, `L ≤ N-1`: with `α = |M-σ|`, `β = |M+σ|`,
`τ = (1-x)/2`, `x = 2μ/N`, `h = 1/N`, `t = h²`,
`Φ_{L₀+k}^{M,σ} = √(𝔠_α(τ,h) 𝔠_β(1-τ,h)) / √(Ct(2L+1, 1, t)) · P̃_{L₀+k}(τ; t)`
(`E_N W_{3j} = √(𝔠_{p_+}((1-x)/2,h) 𝔠_{p_-}((1+x)/2,h))`, `Π_L = 𝔠_{2L+1}(1,h)`).
The proof is the induction in the rank from `Phi3j_rank_recurrence`: the starts are
`Phi3j_carrier_start` (all chambers) and, for `M = σ = 0`, `Phi3j_carrier_start_one`; the
square-root factors cancel because `Π_{L+1} = Π_L (1-(L+1)²t)`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

/-- The algebra of one induction step: given the rank recurrence, the carrier form of `Φ_L` and of
the backward term, the carrier form of `Φ_{L+1}` with `P̃_{L+1}` from the square-root-free
recurrence. -/
lemma glue_alg (A w a b Rl Rl1 L Y Φm Φ Φp Pm P Pp : ℝ) (hw : 0 < w) (hb : 0 < b)
    (hL : L ≠ 0) (hR1 : Rl1 ≠ 0)
    (hrec : (2 * L + 1) * Y * Φ = (L + 1) * (Rl * a) * Φm + L * (Rl1 * b) * Φp)
    (hΦ : Φ = A / w * P) (hback : Rl * Φm = Rl * (A * a / w * Pm))
    (hPp : Pp = ((2 * L + 1) * Y * P - (L + 1) * Rl * a ^ 2 * Pm) / (L * Rl1)) :
    Φp = A / (w * b) * Pp := by
  subst hPp
  have h1 : L * Rl1 * b * Φp = (2 * L + 1) * Y * Φ - (L + 1) * a * (Rl * Φm) := by
    linear_combination hrec.symm
  rw [hback, hΦ] at h1
  have hw' := hw.ne'
  have hb' := hb.ne'
  field_simp
  field_simp at h1
  linear_combination h1

lemma ab_cast {M σ : ℚ} {α β : ℕ} (hα : |M - σ| = α) (hβ : |M + σ| = β) :
    (α : ℝ) + β = 2 * ((max |M| |σ| : ℚ) : ℝ) := by
  have h := hahn_alpha_add_beta M σ
  rw [hα, hβ] at h
  have : ((α : ℚ) + β) = 2 * max |M| |σ| := h
  have := congrArg (Rat.cast : ℚ → ℝ) this
  push_cast at this ⊢
  linarith

/-- `Π_{L+1} = Π_L (1 - (L+1)² t)` for `Π_L = 𝔠_{2L+1}(1;t)`, `2L = α+β`, rank `L = L₀+k`. -/
lemma Ct_step {M σ : ℚ} {α β : ℕ} (hα : |M - σ| = α) (hβ : |M + σ| = β) (k : ℕ) (t : ℝ) :
    Ct (α + β + 2 * (k + 1) + 1) 1 t =
      (1 - (((max |M| |σ| : ℚ) : ℝ) + k + 1) ^ 2 * t) * Ct (α + β + 2 * k + 1) 1 t := by
  have h : α + β + 2 * (k + 1) + 1 = (α + β + 2 * k + 1) + 2 := by ring
  rw [h, Ct_succ_succ]
  have hc := ab_cast hα hβ
  generalize ((max |M| |σ| : ℚ) : ℝ) = L0 at hc ⊢
  congr 1
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have : ((α : ℝ) + β + 2 * k + 1 + 1) / 2 = L0 + k + 1 := by linarith
  have e : ((α : ℝ) + β + 2 * k + 1 + 1) ^ 2 / 4 = (L0 + k + 1) ^ 2 := by
    rw [← this]; ring
  rw [e]; ring

/-- The central product `Ct r 1 (1/N²)` is positive while its largest factor is. -/
lemma Ct_pos (N : ℝ) (hN : 0 < N) : ∀ r : ℕ, ((r : ℝ) - 1) / 2 < N → 0 < Ct r 1 (1 / N ^ 2) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    match r, ih, hr with
    | 0, _, _ => simp [Ct_zero]
    | 1, _, _ => simp [Ct_one]
    | r + 2, ih, hr =>
      rw [Ct_succ_succ]
      have h1 := ih r (by omega) (by push_cast at hr ⊢; linarith)
      have h2 : 0 < (1 : ℝ) ^ 2 - ((r : ℝ) + 1) ^ 2 / 4 * (1 / N ^ 2) := by
        push_cast at hr
        have hr' : ((r : ℝ) + 1) / 2 < N := by linarith
        have hr0 : (0 : ℝ) ≤ ((r : ℝ) + 1) / 2 := by positivity
        have : (((r : ℝ) + 1) / 2) ^ 2 < N ^ 2 := by nlinarith
        have h3 : ((r : ℝ) + 1) ^ 2 / 4 * (1 / N ^ 2) < 1 := by
          rw [show ((r : ℝ) + 1) ^ 2 / 4 * (1 / N ^ 2) = (((r : ℝ) + 1) / 2) ^ 2 / N ^ 2 by ring,
            div_lt_one (by positivity)]
          exact this
        linarith
      exact mul_pos h2 h1

lemma Rk_L0 (M σ : ℚ) : Rk M σ (max |M| |σ|) = 0 := by
  unfold Rk
  rcases max_choice |M| |σ| with h | h
  · have : ((|M| : ℚ) : ℝ) ^ 2 = (M : ℝ) ^ 2 := by rw [Rat.cast_abs, sq_abs]
    rw [h, this]; simp
  · have : ((|σ| : ℚ) : ℝ) ^ 2 = (σ : ℝ) ^ 2 := by rw [Rat.cast_abs, sq_abs]
    rw [h, this]; simp

lemma Rk_pos (M σ L : ℚ) (hL : max |M| |σ| < L) : 0 < Rk M σ L := by
  unfold Rk
  apply Real.sqrt_pos.mpr
  have hL0 : (0 : ℝ) < L := by
    have : (0 : ℚ) < L := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hL
    exact_mod_cast this
  have h1 : |(M : ℝ)| < L := by
    rw [← Rat.cast_abs]; exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hL
  have h2 : |(σ : ℝ)| < L := by
    rw [← Rat.cast_abs]; exact_mod_cast lt_of_le_of_lt (le_max_right _ _) hL
  have e1 : (M : ℝ) ^ 2 < (L : ℝ) ^ 2 := by
    rw [sq_lt_sq, abs_of_pos hL0]; exact h1
  have e2 : (σ : ℝ) ^ 2 < (L : ℝ) ^ 2 := by
    rw [sq_lt_sq, abs_of_pos hL0]; exact h2
  exact mul_pos (by linarith) (by linarith)

/-- **One induction step** of the carrier identity: from the carrier form of `Φ_{L}` (and of the
backward term `R_L Φ_{L-1}`) at `L = L₀+k` to that of `Φ_{L+1}`, with `P̃_{L+1} = step3 … P Pm`. -/
lemma glue_succ {M σ N μ : ℚ} {α β : ℕ} (hα : |M - σ| = α) (hβ : |M + σ| = β)
    (hA : SpecAdm M σ N) (hN : 0 < N) (A P Pm : ℝ) (k : ℕ)
    (hk : max |M| |σ| + k + 2 ≤ N) (hne : max |M| |σ| + (k : ℚ) ≠ 0)
    (hΦ : Phi3j (max |M| |σ| + k) M σ N μ =
      A / Real.sqrt (Ct (α + β + 2 * k + 1) 1 (1 / (N : ℝ) ^ 2)) * P)
    (hback : Rk M σ (max |M| |σ| + k) * Phi3j (max |M| |σ| + k - 1) M σ N μ =
      Rk M σ (max |M| |σ| + k) *
        (A * Real.sqrt (1 - (((max |M| |σ| + k : ℚ)) : ℝ) ^ 2 / (N : ℝ) ^ 2) /
          Real.sqrt (Ct (α + β + 2 * k + 1) 1 (1 / (N : ℝ) ^ 2)) * Pm)) :
    Phi3j (max |M| |σ| + ((k + 1 : ℕ) : ℚ)) M σ N μ =
      A / Real.sqrt (Ct (α + β + 2 * (k + 1) + 1) 1 (1 / (N : ℝ) ^ 2)) *
        step3 M σ (max |M| |σ| + k) ((1 - 2 * (μ : ℝ) / N) / 2) (1 / (N : ℝ) ^ 2) P Pm := by
  obtain ⟨a0, b0, P0, Q0, -, -, -, -, hnrk, -⟩ := specAdm_data hA
  have hkK : k < nrk a0 b0 P0 Q0 := by
    have : (k : ℚ) < ((nrk a0 b0 P0 Q0 : ℕ) : ℚ) := by rw [hnrk]; linarith
    exact_mod_cast this
  have hadm := rank_adm hA hnrk hkK
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hμ : N * (2 * μ / N) / 2 = μ := by field_simp
  have hrec := Phi3j_rank_recurrence (max |M| |σ| + k) M σ N (2 * μ / N) hN hadm.1 hadm.2.1
    hadm.2.2
  simp only [PhiX, hμ] at hrec
  have e1 : max |M| |σ| + ((k + 1 : ℕ) : ℚ) = max |M| |σ| + k + 1 := by push_cast; ring
  rw [e1]
  -- notation
  set L : ℚ := max |M| |σ| + k with hL
  have hL1 : (L : ℝ) ≠ 0 := by exact_mod_cast hne
  have hLk : L + 1 ≤ N - 1 := by rw [hL]; linarith
  have hLpos : (0 : ℝ) ≤ L := by
    have : (0 : ℚ) ≤ L := by
      rw [hL]; have := le_trans (abs_nonneg M) (le_max_left |M| |σ|)
      have : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      linarith
    exact_mod_cast this
  have hLN : (L : ℝ) + 1 < N := by
    have : L + 1 < N := by linarith
    exact_mod_cast this
  have hLN' : (L : ℝ) < N := by linarith
  have hPi : 0 < Ct (α + β + 2 * k + 1) 1 (1 / (N : ℝ) ^ 2) := by
    apply Ct_pos N hNr
    have hc := ab_cast hα hβ
    push_cast
    have : ((max |M| |σ| : ℚ) : ℝ) + k < N := by
      have h2 : ((L : ℚ) : ℝ) = ((max |M| |σ| : ℚ) : ℝ) + k := by rw [hL]; push_cast; rfl
      rw [← h2]; exact hLN'
    linarith
  have hstep := Ct_step hα hβ k (1 / (N : ℝ) ^ 2)
  have hLr : ((max |M| |σ| : ℚ) : ℝ) + k = L := by rw [hL]; push_cast; rfl
  rw [hLr] at hstep
  have hs2 : 0 < 1 - (L : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
    rw [sub_pos, div_lt_one (by positivity)]
    nlinarith
  have hs3 : 0 < 1 - ((L : ℝ) + 1) ^ 2 / (N : ℝ) ^ 2 := by
    rw [sub_pos, div_lt_one (by positivity)]
    have : (0 : ℝ) < (L : ℝ) + 1 := by linarith
    nlinarith
  have hw : 0 < Real.sqrt (Ct (α + β + 2 * k + 1) 1 (1 / (N : ℝ) ^ 2)) := Real.sqrt_pos.mpr hPi
  have hb : 0 < Real.sqrt (1 - ((L : ℝ) + 1) ^ 2 / (N : ℝ) ^ 2) := Real.sqrt_pos.mpr hs3
  have hR1 : Rk M σ (L + 1) ≠ 0 := by
    apply (Rk_pos M σ (L + 1) _).ne'
    rw [hL]
    have : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    linarith
  have hsplit : Real.sqrt (Ct (α + β + 2 * (k + 1) + 1) 1 (1 / (N : ℝ) ^ 2)) =
      Real.sqrt (Ct (α + β + 2 * k + 1) 1 (1 / (N : ℝ) ^ 2)) *
        Real.sqrt (1 - ((L : ℝ) + 1) ^ 2 / (N : ℝ) ^ 2) := by
    rw [hstep, mul_comm, Real.sqrt_mul (by linarith [hs3])]
    congr 2
    ring
  have hx : (((2 * μ / N : ℚ)) : ℝ) = 1 - 2 * ((1 - 2 * (μ : ℝ) / N) / 2) := by
    push_cast; ring
  rw [hx] at hrec
  rw [hsplit]
  have hPhi := glue_alg A (Real.sqrt (Ct (α + β + 2 * k + 1) 1 (1 / (N : ℝ) ^ 2)))
    (Real.sqrt (1 - (L : ℝ) ^ 2 / (N : ℝ) ^ 2)) (Real.sqrt (1 - ((L : ℝ) + 1) ^ 2 / (N : ℝ) ^ 2))
    (Rk M σ L) (Rk M σ (L + 1)) (L : ℝ)
    ((L : ℝ) * ((L : ℝ) + 1) * (1 - 2 * ((1 - 2 * (μ : ℝ) / N) / 2)) - (M : ℝ) * σ)
    (Phi3j (L - 1) M σ N μ) (Phi3j L M σ N μ) (Phi3j (L + 1) M σ N μ) Pm P
    (step3 M σ L ((1 - 2 * (μ : ℝ) / N) / 2) (1 / (N : ℝ) ^ 2) P Pm) hw hb hL1 hR1 hrec hΦ hback
    (by
      unfold step3
      rw [Real.sq_sqrt hs2.le]
      congr 1
      ring)
  exact hPhi

lemma Cprod_eq_Ct' (r : ℕ) (u N : ℝ) : Cprod r u (1 / N) = Ct r u (1 / N ^ 2) := by
  rw [Cprod_eq_Ct, one_div_pow]

/-- The backward term in the induction: `A/√Π_{L-1} = A √(1-L²h²)/√Π_L` for `L = L₀+k+1`. -/
lemma back_eq {M σ N : ℚ} {α β : ℕ} (hα : |M - σ| = α) (hβ : |M + σ| = β) (hN : 0 < N)
    (k : ℕ) (hk : max |M| |σ| + ((k + 1 : ℕ) : ℚ) + 1 ≤ N) (A P Φ : ℝ)
    (hΦ : Φ = A / Real.sqrt (Ct (α + β + 2 * k + 1) 1 (1 / (N : ℝ) ^ 2)) * P) :
    Φ = A * Real.sqrt (1 - (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ)) : ℝ) ^ 2 / (N : ℝ) ^ 2) /
      Real.sqrt (Ct (α + β + 2 * (k + 1) + 1) 1 (1 / (N : ℝ) ^ 2)) * P := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set L : ℚ := max |M| |σ| + ((k + 1 : ℕ) : ℚ) with hL
  have hstep := Ct_step hα hβ k (1 / (N : ℝ) ^ 2)
  have hLr : ((max |M| |σ| : ℚ) : ℝ) + k + 1 = L := by rw [hL]; push_cast; ring
  rw [hLr] at hstep
  have hLpos : (0 : ℝ) ≤ L := by
    have : (0 : ℚ) ≤ L := by
      rw [hL]; have := le_trans (abs_nonneg M) (le_max_left |M| |σ|)
      have : (0 : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := Nat.cast_nonneg _
      linarith
    exact_mod_cast this
  have hLN : (L : ℝ) < N := by
    have : L < N := by linarith
    exact_mod_cast this
  have hs : 0 < 1 - (L : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
    rw [sub_pos, div_lt_one (by positivity)]
    nlinarith
  have hPi : 0 < Ct (α + β + 2 * k + 1) 1 (1 / (N : ℝ) ^ 2) := by
    apply Ct_pos N hNr
    have hc := ab_cast hα hβ
    push_cast
    have h2 : ((L : ℚ) : ℝ) = ((max |M| |σ| : ℚ) : ℝ) + k + 1 := hLr.symm
    linarith
  have hsplit : Real.sqrt (Ct (α + β + 2 * (k + 1) + 1) 1 (1 / (N : ℝ) ^ 2)) =
      Real.sqrt (1 - (L : ℝ) ^ 2 / (N : ℝ) ^ 2) *
        Real.sqrt (Ct (α + β + 2 * k + 1) 1 (1 / (N : ℝ) ^ 2)) := by
    rw [hstep, show (1 : ℝ) - (L : ℝ) ^ 2 * (1 / (N : ℝ) ^ 2) = 1 - (L : ℝ) ^ 2 / (N : ℝ) ^ 2 by ring,
      Real.sqrt_mul hs.le]
  rw [hsplit, hΦ]
  have h1 : 0 < Real.sqrt (1 - (L : ℝ) ^ 2 / (N : ℝ) ^ 2) := Real.sqrt_pos.mpr hs
  have h2 : 0 < Real.sqrt (Ct (α + β + 2 * k + 1) 1 (1 / (N : ℝ) ^ 2)) := Real.sqrt_pos.mpr hPi
  generalize Real.sqrt (1 - (L : ℝ) ^ 2 / (N : ℝ) ^ 2) = a at h1 ⊢
  generalize Real.sqrt (Ct (α + β + 2 * k + 1) 1 (1 / (N : ℝ) ^ 2)) = w at h2 ⊢
  field_simp

/-- **`lem:sqrtfreecarrier`, `eq:sqrtfreecarrier` (3j, every chamber).**
Let `M, σ` with `α = |M-σ|`, `β = |M+σ|` natural numbers (`p_+ = α`, `p_- = β`), `(M,σ,N)`
admissible (`SpecAdm`), `μ` on the physical lattice (`Lat4`), `L₀ = max(|M|,|σ|)`, `L = L₀+k ≤ N-1`,
`h = 1/N`, `x = 2μ/N`, `τ = (1-x)/2`.  Then
`Φ_L^{M,σ}(x;h) = √(𝔠_α(τ,h) 𝔠_β(1-τ,h)) / √(Ct(2L+1, 1, h²)) · P̃_L(τ; h²)`,
with `2L+1 = α+β+2k+1`, `P̃_L = ptilde3 M σ k` (defined by the square-root-free recurrence
`eq:3jrankpoly`), in every chamber (`M ≥ |σ|`, `M ≤ -|σ|`, `σ ≥ |M|`, `σ ≤ -|M|`). -/
theorem Phi3j_carrier (M σ N μ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β)
    (hA : SpecAdm M σ N) (hN : 0 < N) (hlat : Lat4 M σ N μ) (k : ℕ)
    (hk : max |M| |σ| + k + 1 ≤ N) :
    Phi3j (max |M| |σ| + k) M σ N μ =
      Real.sqrt (Cprod α ((1 - 2 * (μ : ℝ) / N) / 2) (1 / N) *
          Cprod β ((1 + 2 * (μ : ℝ) / N) / 2) (1 / N)) /
        Real.sqrt (Ct (α + β + 2 * k + 1) 1 (1 / (N : ℝ) ^ 2)) *
        ptilde3 M σ k ((1 - 2 * (μ : ℝ) / N) / 2) (1 / (N : ℝ) ^ 2) := by
  set Aval : ℝ := Real.sqrt (Cprod α ((1 - 2 * (μ : ℝ) / N) / 2) (1 / N) *
          Cprod β ((1 + 2 * (μ : ℝ) / N) / 2) (1 / N)) with hAval
  have hL0 : (0 : ℚ) ≤ max |M| |σ| := le_trans (abs_nonneg M) (le_max_left _ _)
  -- the claim for ranks `k` and `k+1`
  have key : ∀ j : ℕ,
      (max |M| |σ| + j + 1 ≤ N → Phi3j (max |M| |σ| + j) M σ N μ =
        Aval / Real.sqrt (Ct (α + β + 2 * j + 1) 1 (1 / (N : ℝ) ^ 2)) *
          ptilde3 M σ j ((1 - 2 * (μ : ℝ) / N) / 2) (1 / (N : ℝ) ^ 2)) ∧
      (max |M| |σ| + ((j + 1 : ℕ) : ℚ) + 1 ≤ N → Phi3j (max |M| |σ| + ((j + 1 : ℕ) : ℚ)) M σ N μ =
        Aval / Real.sqrt (Ct (α + β + 2 * (j + 1) + 1) 1 (1 / (N : ℝ) ^ 2)) *
          ptilde3 M σ (j + 1) ((1 - 2 * (μ : ℝ) / N) / 2) (1 / (N : ℝ) ^ 2)) := by
    intro j
    induction j with
    | zero =>
      have c0 : Phi3j (max |M| |σ| + ((0 : ℕ) : ℚ)) M σ N μ =
          Aval / Real.sqrt (Ct (α + β + 2 * 0 + 1) 1 (1 / (N : ℝ) ^ 2)) *
            ptilde3 M σ 0 ((1 - 2 * (μ : ℝ) / N) / 2) (1 / (N : ℝ) ^ 2) := by
        have := Phi3j_carrier_start M σ N μ α β hα hβ hlat
        simp only [Nat.cast_zero, add_zero]
        rw [this, ptilde3_zero, Cprod_eq_Ct' (α + β + 1)]
        rw [hAval, Cprod_eq_Ct', Cprod_eq_Ct']
        ring
      refine ⟨fun _ => by simpa using c0, fun h1 => ?_⟩
      by_cases h0 : max |M| |σ| = 0
      · have hM : M = 0 := by
          have : |M| ≤ 0 := h0 ▸ le_max_left _ _
          exact abs_nonpos_iff.mp this
        have hs : σ = 0 := by
          have : |σ| ≤ 0 := h0 ▸ le_max_right _ _
          exact abs_nonpos_iff.mp this
        subst hM hs
        have hα0 : α = 0 := by
          have : (α : ℚ) = 0 := by rw [← hα]; simp
          exact_mod_cast this
        have hβ0 : β = 0 := by
          have : (β : ℚ) = 0 := by rw [← hβ]; simp
          exact_mod_cast this
        subst hα0 hβ0
        have hN2 : (2 : ℚ) ≤ N := by
          have : max |(0 : ℚ)| |(0 : ℚ)| = 0 := h0
          rw [this] at h1; push_cast at h1; linarith
        have := Phi3j_carrier_start_one N μ hlat hN2
        rw [ptilde3_one_of_eq _ _ _ _ h0]
        rw [h0]
        simp only [zero_add, Nat.cast_one]
        rw [this, hAval, Cprod_eq_Ct' 0, Cprod_eq_Ct' 0, Cprod_eq_Ct' (0 + 0 + 2 + 1)]
        norm_num
        ring
      · have hk2 : max |M| |σ| + ((0 : ℕ) : ℚ) + 2 ≤ N := by
          have h1' : max |M| |σ| + 1 + 1 ≤ N := by simpa using h1
          simp only [Nat.cast_zero, add_zero]; linarith
        have h := glue_succ hα hβ hA hN Aval (ptilde3 M σ 0 ((1 - 2 * (μ : ℝ) / N) / 2)
            (1 / (N : ℝ) ^ 2)) 0 0 hk2 (by simpa using h0)
          (by simpa using c0)
          (by
            simp only [Nat.cast_zero, add_zero, Rk_L0, zero_mul])
        rw [ptilde3_one_of_ne _ _ _ _ h0]
        simp only [Nat.cast_zero, add_zero] at h ⊢
        simpa [ptilde3_zero] using h
    | succ j ih =>
      refine ⟨ih.2, fun h2 => ?_⟩
      have h1 : max |M| |σ| + ((j + 1 : ℕ) : ℚ) + 1 ≤ N := by push_cast at h2 ⊢; linarith
      have h0 : max |M| |σ| + (j : ℚ) + 1 ≤ N := by push_cast at h1 ⊢; linarith
      have hΦj := ih.1 h0
      have hΦj1 := ih.2 h1
      have hne : max |M| |σ| + ((j + 1 : ℕ) : ℚ) ≠ 0 := by
        have : (0 : ℚ) < ((j + 1 : ℕ) : ℚ) := by positivity
        linarith
      have hb := back_eq hα hβ hN j h1 Aval _ _ hΦj
      have h := glue_succ hα hβ hA hN Aval (ptilde3 M σ (j + 1) ((1 - 2 * (μ : ℝ) / N) / 2)
          (1 / (N : ℝ) ^ 2)) (ptilde3 M σ j ((1 - 2 * (μ : ℝ) / N) / 2) (1 / (N : ℝ) ^ 2)) (j + 1)
          (by push_cast at h2 ⊢; linarith) hne hΦj1
          (by
            rw [show max |M| |σ| + ((j + 1 : ℕ) : ℚ) - 1 = max |M| |σ| + (j : ℚ) by
              push_cast; ring, hb])
      rw [ptilde3_succ_succ]
      exact h
  have hk' : max |M| |σ| + k + 1 ≤ N := hk
  rw [(key k).1 hk']

/-- info: 'FormalResearch.Racah.Phi3j_carrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_carrier

end FormalResearch.Racah
