module

public import FormalResearch.Special.DiscreteAiryLimitChainsCore
public import FormalResearch.Racah.P2RacahMidpoint
public import FormalResearch.Racah.P3FluxGauss

/-!
# The actual Wigner `6j` chain is the closed-form centred Racah Jacobi chain (Weyl P3, `prop:racah-class`)

Source: `Weyl/P3/paper/weyl_midpoint_semiclassics.tex`, `prop:racah-class` (`eq:racahnaturalJacobi`,
`eq:racahAkexact`, `eq:racahBkexact`), with the exact centred Racah recurrence `eq:6jrec` (DLMF 34.5.11,
formalised as `Racah.SixJ.Phi6_midpoint_recurrence`).

**Setting.**  Integers `a, b, c, m, n` (the integer case), `A = a + (n+1)/2 = wA`, `B = b + (m+1)/2 = wB`,
`C = c + ½`, `x = (A²+B²-C²)/(2AB) = cosA A B C`, the natural-gauge kernel `Ŷ_f = √(2f+1) Φ_f` with
`Φ_f = (-1)^ξ 2√(AB) {a b c; b+m a+n f}` (`Racah.SixJ.Phi6`, `racah6jY`).  For any scale `h > 0` (the paper's
`h = 1/N`, `α = A h`, `β = B h`) the closed forms of `DiscreteAiryLimitHahn` are those with `P = 1/(4α²)`,
`Q = 1/(4β²)` (so `β₀ = √(PQ) = 1/(4αβ)`), `ẽ((kh)²) = η_k`, `B_k = hrB β₀ m n h k`:
`A_k = ½ r_k ẽ((kh)²)` (`hrAk`), `c_k = x - B_k` (`hrCk … 1 …`, `τ = +1`).

## Results (proved)

* `racah_class_chain` (the identification, `prop:racah-class` in the integer case): for every integer `k ≥ 1`
  `jac (hrAk P Q m n h) (hrCk P Q 1 x m n h) Ŷ k = 0`, i.e. `x Ŷ_k = A_{k+1} Ŷ_{k+1} + A_k Ŷ_{k-1} + B_k Ŷ_k`
  with `A_k = R_k η_k/(k√(4k²-1))` (`eq:racahAkexact`) and `B_k = (2k(k+1)+1-m²-n²)/(8AB) + mn/(k(k+1))`
  (`eq:racahBkexact`) — exactly the closed forms used by `discrete_airy_hahn_racah`.  Hypotheses: `h > 0`, `A, B > 0`.
  (`h` plays no role in the identification: `h²β₀ = 1/(4AB)` and `(kh)²P = k²/(4A²)` are `h`-free.)
* `racah_chain_support`: `Ŷ_k = 0` outside `max(|m|,|n|) ≤ k ≤ min(2b+m, 2a+n)` (the physical `f`-range).
* **End conditions** (`racah_end_upper`, `racah_end_lower`): `A_{kmax+1} = 0` with `kmax = min(2b+m, 2a+n)`, since
  `kmax + 1 = min(2B, 2A)` (`η_{kmax+1} = 0`, the hard edge), and `A_{kmin} = 0` for `kmin = max(|m|,|n|) ≥ 1`.
* `racah_chain_sq_le` (condition `(R)` of `thm:general-rank-airy`(ii), `6j` case): for a finite Racah system and every
  physical `c = c_i`, `Ŷ_f² ≤ 4AB/(2C)`, from `gaussWeight_6j` (`λ² = 4AB/(2C)`).

## Not formalised

* Half-integer data: `a, b, c ∈ ℤ` with `m, n ∈ ℤ + ½` is `DiscreteAiryLimitChains2Half6j`; the mixed-parity labels
  (`a, b, c` half-integer with integer `m, n`, or both half-integer) are not covered.
* The paper's reduction to the canonical chamber `m ≥ |n|` is not needed here (the recurrence holds in every chamber), and
  the dependence on the triple `(α, β, γ)` is not made uniform.
* The `q`-Racah (quantum `6j`) chain.
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner
  FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The natural-gauge `6j` chain `Ŷ_k = √(2k+1) Φ_k(a,b,c;m,n)`, `k ∈ ℤ`. -/
noncomputable def racah6jY (a b c m n : ℤ) (k : ℤ) : ℝ :=
  Real.sqrt (2 * (k : ℝ) + 1) * Phi6 (a : ℚ) (b : ℚ) (c : ℚ) (k : ℚ) (m : ℚ) (n : ℚ)

lemma racah_tri_f (a b m n k : ℤ) :
    (IsTri (k : ℚ) ((b : ℚ) + m) (b : ℚ) ∧ IsTri (k : ℚ) (a : ℚ) ((a : ℚ) + n)) ↔
      (|m| ≤ k ∧ |n| ≤ k ∧ k ≤ 2 * b + m ∧ k ≤ 2 * a + n) := by
  have e1 : (b : ℚ) + m = ((b + m : ℤ) : ℚ) := by push_cast; ring
  have e2 : (a : ℚ) + n = ((a + n : ℤ) : ℚ) := by push_cast; ring
  rw [e1, e2, isTri_int_iff, isTri_int_iff, abs_le, abs_le]
  omega

lemma racah_tri_l (a b m n k : ℤ) :
    (IsTri ((b : ℚ) + m) (b : ℚ) (k : ℚ) ∧ IsTri (a : ℚ) ((a : ℚ) + n) (k : ℚ)) ↔
      (|m| ≤ k ∧ |n| ≤ k ∧ k ≤ 2 * b + m ∧ k ≤ 2 * a + n) := by
  have e1 : (b : ℚ) + m = ((b + m : ℤ) : ℚ) := by push_cast; ring
  have e2 : (a : ℚ) + n = ((a + n : ℤ) : ℚ) := by push_cast; ring
  rw [e1, e2, isTri_int_iff, isTri_int_iff, abs_le, abs_le]
  omega

/-- **Support of the `6j` chain**: `Ŷ_k = 0` unless `max(|m|,|n|) ≤ k ≤ min(2b+m, 2a+n)`. -/
theorem racah_chain_support (a b c m n k : ℤ) (hk : ¬ (|m| ≤ k ∧ |n| ≤ k ∧ k ≤ 2 * b + m ∧ k ≤ 2 * a + n)) :
    racah6jY a b c m n k = 0 := by
  unfold racah6jY Phi6 W6 sixJ
  rw [← racah_tri_l] at hk
  have h0 : triSq ((b : ℚ) + m) (b : ℚ) (k : ℚ) * triSq (a : ℚ) ((a : ℚ) + n) (k : ℚ) = 0 := by
    by_cases h1 : IsTri ((b : ℚ) + m) (b : ℚ) (k : ℚ)
    · have h2 : ¬ IsTri (a : ℚ) ((a : ℚ) + n) (k : ℚ) := fun h2 => hk ⟨h1, h2⟩
      rw [triSq_eq_zero_of_not_isTri h2]; ring
    · rw [triSq_eq_zero_of_not_isTri h1]; ring
  have h1 : Real.sqrt (triSq ((b : ℚ) + m) (b : ℚ) (k : ℚ)) *
      Real.sqrt (triSq (a : ℚ) ((a : ℚ) + n) (k : ℚ)) = 0 := by
    rw [← Real.sqrt_mul (triSq_nonneg _ _ _), h0]; simp
  have e : ∀ T : ℝ, Real.sqrt (triSq (a : ℚ) (b : ℚ) (c : ℚ)) *
      Real.sqrt (triSq (a : ℚ) ((a : ℚ) + n) (k : ℚ)) *
      Real.sqrt (triSq ((b : ℚ) + m) (b : ℚ) (k : ℚ)) * Real.sqrt (triSq ((b : ℚ) + m) ((a : ℚ) + n) (c : ℚ)) * T = 0 := by
    intro T
    linear_combination (Real.sqrt (triSq (a : ℚ) (b : ℚ) (c : ℚ)) * Real.sqrt (triSq ((b : ℚ) + m) ((a : ℚ) + n) (c : ℚ)) * T) * h1
  rw [e]; simp

/-- **`A_{kmax+1} = 0`**: the hard edge of the `6j` chain.  `kmax = min(2b+m, 2a+n)`, so that
`kmax + 1 = min(2B, 2A)` and `η_{kmax+1} = 0`; here `P = 1/(4(Ah)²)`, `Q = 1/(4(Bh)²)`. -/
theorem racah_end_upper (a b m n : ℤ) (h : ℝ) (hh : 0 < h) (hA : 0 < wA (a : ℚ) (n : ℚ))
    (hB : 0 < wB (b : ℚ) (m : ℚ)) (hhi : 0 ≤ min (2 * b + m) (2 * a + n)) :
    hrAk (1 / (4 * (wA (a : ℚ) (n : ℚ) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) (m : ℚ) * h) ^ 2)) (m : ℝ) (n : ℝ) h
      (min (2 * b + m) (2 * a + n) + 1) = 0 := by
  rw [hrAk_eq _ _ _ _ _ _ (by omega)]
  have hA' : wA (a : ℚ) (n : ℚ) ≠ 0 := hA.ne'
  have hB' : wB (b : ℚ) (m : ℚ) ≠ 0 := hB.ne'
  have he : etilde (1 / (4 * (wA (a : ℚ) (n : ℚ) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) (m : ℚ) * h) ^ 2))
      ((((min (2 * b + m) (2 * a + n) + 1 : ℤ) : ℝ) * h) ^ 2) = 0 := by
    unfold etilde
    have hc : ((min (2 * b + m) (2 * a + n) + 1 : ℤ) : ℝ) = 2 * wA (a : ℚ) (n : ℚ) ∨
        ((min (2 * b + m) (2 * a + n) + 1 : ℤ) : ℝ) = 2 * wB (b : ℚ) (m : ℚ) := by
      rcases min_choice (2 * b + m) (2 * a + n) with hc | hc
      · right; rw [hc]; unfold wB; push_cast; ring
      · left; rw [hc]; unfold wA; push_cast; ring
    rw [Real.sqrt_eq_zero_of_nonpos]
    rcases hc with hc | hc
    · rw [hc]
      have : 1 - 1 / (4 * (wA (a : ℚ) (n : ℚ) * h) ^ 2) * ((2 * wA (a : ℚ) (n : ℚ)) * h) ^ 2 = 0 := by
        field_simp; ring
      rw [this]; simp
    · rw [hc]
      have : 1 - 1 / (4 * (wB (b : ℚ) (m : ℚ) * h) ^ 2) * ((2 * wB (b : ℚ) (m : ℚ)) * h) ^ 2 = 0 := by
        field_simp; ring
      rw [this]; simp
  rw [he]; simp

/-- **`A_{kmin} = 0`** at the lower end `kmin = max(|m|,|n|) ≥ 1` (`hrAk_lower_zero`). -/
theorem racah_end_lower (P Q h : ℝ) (m n : ℤ) (hlo : 1 ≤ max |m| |n|) :
    hrAk P Q (m : ℝ) (n : ℝ) h (max |m| |n|) = 0 := hrAk_lower_zero P Q h m n hlo

/-- **`prop:racah-class` (integer case): the actual `6j` chain is the closed-form centred Racah Jacobi chain.**
For integers `a, b, c, m, n` with `A = wA a n > 0`, `B = wB b m > 0`, any `h > 0`, `x = cosA A B (c + ½)`,
`P = 1/(4(Ah)²)`, `Q = 1/(4(Bh)²)`: the natural-gauge kernel `Ŷ_k = √(2k+1) Φ_k` of the Wigner `6j` symbol
satisfies `A_{k+1} Ŷ_{k+1} + A_k Ŷ_{k-1} = c_k Ŷ_k` for every `k ≥ 1`, with the closed forms `A_k = ½ r_k ẽ((kh)²)`,
`c_k = x - B_k` (`hrAk`, `hrCk`, `τ = 1`) of `discrete_airy_hahn_racah`.  End rows included
(`racah_chain_support`, `racah_end_lower`, `racah_end_upper`). -/
theorem racah_class_chain (a b c m n : ℤ) (h : ℝ) (hh : 0 < h) (hA : 0 < wA (a : ℚ) (n : ℚ))
    (hB : 0 < wB (b : ℚ) (m : ℚ)) (k : ℤ) (hk : 1 ≤ k) :
    jac (hrAk (1 / (4 * (wA (a : ℚ) (n : ℚ) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) (m : ℚ) * h) ^ 2)) (m : ℝ) (n : ℝ) h)
      (hrCk (1 / (4 * (wA (a : ℚ) (n : ℚ) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) (m : ℚ) * h) ^ 2)) 1
        (cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ))) (m : ℝ) (n : ℝ) h)
      (racah6jY a b c m n) k = 0 := by
  set A := wA (a : ℚ) (n : ℚ) with hAdef
  set B := wB (b : ℚ) (m : ℚ) with hBdef
  have hA' : A ≠ 0 := hA.ne'
  have hB' : B ≠ 0 := hB.ne'
  have hh' : h ≠ 0 := hh.ne'
  have hAB : 0 < A * B := mul_pos hA hB
  -- the closed forms in terms of `η_k` and `q_k`
  have hη : ∀ j : ℝ, etilde (1 / (4 * (A * h) ^ 2)) (1 / (4 * (B * h) ^ 2)) ((j * h) ^ 2) = etaK A B j := by
    intro j
    unfold etilde etaK
    congr 1
    field_simp
  have hβ : Real.sqrt (1 / (4 * (A * h) ^ 2) * (1 / (4 * (B * h) ^ 2))) = 1 / (4 * (A * B * h ^ 2)) := by
    have e : 1 / (4 * (A * h) ^ 2) * (1 / (4 * (B * h) ^ 2)) = (1 / (4 * (A * B * h ^ 2))) ^ 2 := by
      field_simp
    rw [e, Real.sqrt_sq (by positivity)]
  refine chain_extend_rows _ _ _ (max |m| |n|) (min (2 * b + m) (2 * a + n)) ?_ ?_ ?_ ?_ k hk
  · intro j hj
    apply racah_chain_support
    intro ⟨h1, h2, h3, h4⟩
    rcases hj with hj | hj
    · exact absurd (max_le h1 h2) (not_le.2 hj)
    · exact absurd (le_min h3 h4) (not_le.2 hj)
  · exact fun hlo => racah_end_lower _ _ _ m n hlo
  · intro hhi
    exact racah_end_upper a b m n h hh hA hB hhi
  · intro j hj hlo hhi
    have hlo' : |m| ≤ j ∧ |n| ≤ j := ⟨(le_max_left _ _).trans hlo, (le_max_right _ _).trans hlo⟩
    have hhi' : j ≤ 2 * b + m ∧ j ≤ 2 * a + n := ⟨(min_le_left _ _).trans' hhi, (min_le_right _ _).trans' hhi⟩
    have hadm := (racah_tri_f a b m n j).2 ⟨hlo'.1, hlo'.2, hhi'.1, hhi'.2⟩
    have hrec := Phi6_midpoint_recurrence (a : ℚ) (b : ℚ) (c : ℚ) (j : ℚ) (m : ℚ) (n : ℚ) hadm.1 hadm.2
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hrow := natgauge_row (j : ℝ) (rootR (m : ℝ) (n : ℝ) (j : ℝ) * etaK A B (j : ℝ))
      (rootR (m : ℝ) (n : ℝ) ((j : ℝ) + 1) * etaK A B ((j : ℝ) + 1))
      (Phi6 (a : ℚ) (b : ℚ) (c : ℚ) ((j : ℚ) - 1) (m : ℚ) (n : ℚ)) (Phi6 (a : ℚ) (b : ℚ) (c : ℚ) (j : ℚ) (m : ℚ) (n : ℚ))
      (Phi6 (a : ℚ) (b : ℚ) (c : ℚ) ((j : ℚ) + 1) (m : ℚ) (n : ℚ)) (cosA A B (wC (c : ℚ)))
      (qf (j : ℝ) (m : ℝ) (n : ℝ) A B) ((m : ℝ) * n) hj1 (by
        push_cast at hrec ⊢
        linear_combination hrec)
    have hA1 : hrAk (1 / (4 * (A * h) ^ 2)) (1 / (4 * (B * h) ^ 2)) (m : ℝ) (n : ℝ) h ((j + 1 : ℤ)) =
        rootR (m : ℝ) (n : ℝ) ((j : ℝ) + 1) * etaK A B ((j : ℝ) + 1) /
          (((j : ℝ) + 1) * Real.sqrt (4 * ((j : ℝ) + 1) ^ 2 - 1)) := by
      rw [hrAk_eq _ _ _ _ _ _ (by omega)]
      push_cast
      rw [hη]
      unfold rootR
      ring
    have hA0 : hrAk (1 / (4 * (A * h) ^ 2)) (1 / (4 * (B * h) ^ 2)) (m : ℝ) (n : ℝ) h j =
        rootR (m : ℝ) (n : ℝ) (j : ℝ) * etaK A B (j : ℝ) / ((j : ℝ) * Real.sqrt (4 * (j : ℝ) ^ 2 - 1)) := by
      rw [hrAk_eq _ _ _ _ _ _ hj, hη]
      unfold rootR
      ring
    have hC : hrCk (1 / (4 * (A * h) ^ 2)) (1 / (4 * (B * h) ^ 2)) 1 (cosA A B (wC (c : ℚ))) (m : ℝ) (n : ℝ) h j =
        cosA A B (wC (c : ℚ)) - qf (j : ℝ) (m : ℝ) (n : ℝ) A B - (m : ℝ) * n / ((j : ℝ) * ((j : ℝ) + 1)) := by
      unfold hrCk
      rw [hrB_racah _ _ _ _ _ A B hAB (by rw [hβ]; field_simp)]
      unfold qf
      ring
    unfold jac racah6jY
    rw [hA1, hA0, hC]
    push_cast at hrow ⊢
    linear_combination hrow

/-- **Condition `(R)` for the `6j` chain** (`thm:general-rank-airy`(ii)): for a finite Racah system and every physical
`c = c_i`, every natural-gauge value is bounded, `(2f_j+1) Φ_{f_j}(c_i)² ≤ 4AB/(2C)` (`C = c_i + ½`), from
`gaussWeight_6j`.  (For a compact family of strict triangles `AB/C = O(N)`, so `Ŷ = O(N^{1/2})`.) -/
theorem racah_chain_sq_le {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (i j : Fin (D + 1)) :
    (2 * (fPt m n j : ℝ) + 1) * Phi6 a b (cPt a b m n i) (fPt m n j) m n ^ 2 ≤
      4 * wA a n * wB b m / (2 * wC (cPt a b m n i)) := by
  have hl := (gaussWeight_6j h i).1
  unfold lambdaSq6j at hl
  rw [← hl]
  exact Finset.single_le_sum (f := fun j : Fin (D + 1) => (2 * (fPt m n j : ℝ) + 1) *
    Phi6 a b (cPt a b m n i) (fPt m n j) m n ^ 2) (fun j _ => mul_nonneg (by linarith [fPt_nonneg m n j]) (sq_nonneg _)) (Finset.mem_univ j)

/-- info: 'FormalResearch.Special.racah_class_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_class_chain

/-- info: 'FormalResearch.Special.racah_chain_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_chain_support

/-- info: 'FormalResearch.Special.racah_end_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_end_upper

/-- info: 'FormalResearch.Special.racah_end_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_end_lower

/-- info: 'FormalResearch.Special.racah_chain_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_chain_sq_le

end FormalResearch.Special
