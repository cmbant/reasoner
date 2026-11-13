module

public import FormalResearch.Wigner.Special3j

/-!
# `(j₁ j₂ j₃; 0 0 0)` for even `J` (DLMF 34.3.5)

Racah's sum with `m₁ = m₂ = 0` and `j₁ = v+w`, `j₂ = k+w`, `j₃ = k+v` is evaluated in closed form
(a Dixon-type sum).  The `j₁`-recurrence `racahSum3_recurrence` degenerates for `m = 0` to a two-term
recurrence (the coefficient of `racahSum3 j₁` vanishes), which is run from the stretched value
`k = 0`, where Racah's sum has a single term, to general `k`.
-/

@[expose] public section

namespace FormalResearch.Wigner

/-- The closed form of the Dixon-type Racah sum. -/
noncomputable def dixonRHS (k v w : ℕ) : ℝ :=
  (-1 : ℝ) ^ w * ((k + v + w).factorial : ℝ) /
    ((k.factorial : ℝ) * v.factorial * w.factorial * (v + w).factorial * (k + w).factorial *
      (k + v).factorial)

lemma dixon_key (k v w : ℕ) :
    (((v : ℝ) + w + 2) * (2 * k + 2) * (2 * k + 2 * v + 2 * w + 4)) * dixonRHS (k + 1) v w +
      (((v : ℝ) + w + 1) * (2 * w + 2) * (2 * v + 2) * ((v : ℝ) + w + 2) ^ 2) *
        dixonRHS k (v + 1) (w + 1) = 0 := by
  unfold dixonRHS
  rw [show k + 1 + v + w = (k + v + w) + 1 by ring,
    show k + (v + 1) + (w + 1) = (k + v + w) + 1 + 1 by ring,
    show k + (w + 1) = k + 1 + w by ring, show k + (v + 1) = k + 1 + v by ring,
    show v + 1 + (w + 1) = (v + w) + 1 + 1 by ring,
    Nat.factorial_succ (k + v + w + 1), Nat.factorial_succ (k + v + w), Nat.factorial_succ k,
    Nat.factorial_succ v, Nat.factorial_succ w, Nat.factorial_succ (v + w + 1),
    Nat.factorial_succ (v + w)]
  have h1 : (k.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (v.factorial : ℝ) ≠ 0 := by positivity
  have h3 : (w.factorial : ℝ) ≠ 0 := by positivity
  have h4 : ((v + w).factorial : ℝ) ≠ 0 := by positivity
  have h5 : ((k + 1 + w).factorial : ℝ) ≠ 0 := by positivity
  have h6 : ((k + 1 + v).factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem racahSum3_dixon (k : ℕ) : ∀ v w : ℕ,
    racahSum3 ((v + w : ℕ) : ℚ) ((k + w : ℕ) : ℚ) ((k + v : ℕ) : ℚ) 0 0 = dixonRHS k v w := by
  induction k with
  | zero =>
    intro v w
    simp only [Nat.zero_add]
    unfold racahSum3
    rw [finsum_eq_single _ w]
    · rw [term3_eq]
      rw [show ((v + w : ℕ) : ℚ) + (w : ℚ) - (v : ℚ) - (w : ℚ) = (w : ℚ) by push_cast; ring,
        show ((v + w : ℕ) : ℚ) - 0 - (w : ℚ) = (v : ℚ) by push_cast; ring,
        show (w : ℚ) + 0 - (w : ℚ) = ((0 : ℕ) : ℚ) by push_cast; ring,
        show (v : ℚ) - (w : ℚ) + 0 + (w : ℚ) = (v : ℚ) by ring,
        show (v : ℚ) - ((v + w : ℕ) : ℚ) - 0 + (w : ℚ) = ((0 : ℕ) : ℚ) by push_cast; ring]
      simp only [ifa_natCast, Nat.factorial_zero, Nat.cast_one, inv_one]
      unfold dixonRHS
      simp only [Nat.zero_add, Nat.factorial_zero, Nat.cast_one, one_mul]
      have h2 : (v.factorial : ℝ) ≠ 0 := by positivity
      have h3 : (w.factorial : ℝ) ≠ 0 := by positivity
      have h4 : ((v + w).factorial : ℝ) ≠ 0 := by positivity
      field_simp
    · intro s hs
      rw [term3_eq]
      rcases lt_or_gt_of_ne hs with h | h
      · have : ifa ((v : ℚ) - ((v + w : ℕ) : ℚ) - 0 + (s : ℚ)) = 0 := by
          apply ifa_eq_zero_of_neg
          have : (s : ℚ) + 1 ≤ w := by exact_mod_cast h
          push_cast; linarith
        rw [this]; ring
      · have : ifa ((w : ℚ) + 0 - (s : ℚ)) = 0 := by
          apply ifa_eq_zero_of_neg
          have : (w : ℚ) + 1 ≤ s := by exact_mod_cast h
          linarith
        rw [this]; ring
  | succ k ih =>
    intro v w
    have hrec := racahSum3_recurrence ((v + w + 1 : ℕ) : ℚ) ((k + 1 + w : ℕ) : ℚ)
      ((k + 1 + v : ℕ) : ℚ) 0 0
    have e1 : ((v + w + 1 : ℕ) : ℚ) - 1 = ((v + w : ℕ) : ℚ) := by push_cast; ring
    have e2 : ((v + w + 1 : ℕ) : ℚ) + 1 = ((v + 1 + (w + 1) : ℕ) : ℚ) := by push_cast; ring
    have hih := ih (v + 1) (w + 1)
    rw [show ((k + (w + 1) : ℕ) : ℚ) = ((k + 1 + w : ℕ) : ℚ) by push_cast; ring,
      show ((k + (v + 1) : ℕ) : ℚ) = ((k + 1 + v : ℕ) : ℚ) by push_cast; ring] at hih
    rw [e1, e2, hih] at hrec
    have key := dixon_key k v w
    generalize racahSum3 ((v + w + 1 : ℕ) : ℚ) ((k + 1 + w : ℕ) : ℚ) ((k + 1 + v : ℕ) : ℚ) 0 0 =
      S0 at hrec
    generalize racahSum3 ((v + w : ℕ) : ℚ) ((k + 1 + w : ℕ) : ℚ) ((k + 1 + v : ℕ) : ℚ) 0 0 =
      S1 at hrec ⊢
    have hX : (((v : ℝ) + w + 2) * (2 * k + 2) * (2 * k + 2 * v + 2 * w + 4)) ≠ 0 := by positivity
    have hrec' : (((v : ℝ) + w + 2) * (2 * k + 2) * (2 * k + 2 * v + 2 * w + 4)) *
        S1 +
        (((v : ℝ) + w + 1) * (2 * w + 2) * (2 * v + 2) * ((v : ℝ) + w + 2) ^ 2) *
          dixonRHS k (v + 1) (w + 1) = 0 := by
      push_cast at hrec
      linear_combination hrec
    have : (((v : ℝ) + w + 2) * (2 * k + 2) * (2 * k + 2 * v + 2 * w + 4)) *
        (S1 - dixonRHS (k + 1) v w) = 0 := by
      linear_combination hrec' - key
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hX
    · linarith

lemma triSq_even (u v w : ℕ) :
    triSq ((v + w : ℕ) : ℚ) ((u + w : ℕ) : ℚ) ((u + v : ℕ) : ℚ) =
      ((2 * w).factorial : ℝ) * ((2 * v).factorial : ℝ) * ((2 * u).factorial : ℝ) /
        ((2 * (u + v + w) + 1).factorial : ℝ) := by
  rw [triSq_of_nat (p := 2 * w) (q := 2 * v) (r := 2 * u) (by push_cast; ring)
    (by push_cast; ring) (by push_cast; ring),
    show 2 * w + 2 * v + 2 * u + 1 = 2 * (u + v + w) + 1 by ring]

/-- **DLMF 34.3.5** (even `J = 2(u+v+w)`), in the variables `u = J/2 - j₁`, `v = J/2 - j₂`,
`w = J/2 - j₃`, i.e. `j₁ = v+w`, `j₂ = u+w`, `j₃ = u+v`:
`(j₁ j₂ j₃; 0 0 0) = (-1)^(J/2) √((J-2j₁)!(J-2j₂)!(J-2j₃)!/(J+1)!) · (J/2)!/((J/2-j₁)!(J/2-j₂)!(J/2-j₃)!)`.
Proved: Racah's sum is evaluated by `racahSum3_dixon`. -/
theorem threeJ_zero_zero_zero (u v w : ℕ) :
    threeJ ((v + w : ℕ) : ℚ) ((u + w : ℕ) : ℚ) ((u + v : ℕ) : ℚ) 0 0 0 =
      (-1 : ℝ) ^ (u + v + w) *
        Real.sqrt (((2 * u).factorial : ℝ) * ((2 * v).factorial : ℝ) * ((2 * w).factorial : ℝ) /
          ((2 * (u + v + w) + 1).factorial : ℝ)) *
        (((u + v + w).factorial : ℝ) / ((u.factorial : ℝ) * v.factorial * w.factorial)) := by
  unfold threeJ
  rw [if_pos (by ring), racahSum3_dixon u v w]
  have hS : sgn (((v + w : ℕ) : ℚ) - ((u + w : ℕ) : ℚ) - 0) = (-1 : ℝ) ^ (u + v) := by
    rw [show ((v + w : ℕ) : ℚ) - ((u + w : ℕ) : ℚ) - 0 = (((v : ℤ) - u : ℤ) : ℚ) by
      push_cast; ring, sgn_intCast,
      show (v : ℤ) - u = ((v : ℤ) + u) + 2 * (-(u : ℤ)) by ring, neg_one_zpow_add_two_mul]
    rw [show (v : ℤ) + u = ((v + u : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    rw [add_comm]
  have hT := triSq_even u v w
  have hF : fq (((v + w : ℕ) : ℚ) + 0) * fq (((v + w : ℕ) : ℚ) - 0) * fq (((u + w : ℕ) : ℚ) + 0) *
      fq (((u + w : ℕ) : ℚ) - 0) * fq (((u + v : ℕ) : ℚ) + 0) * fq (((u + v : ℕ) : ℚ) - 0) =
      (((v + w).factorial : ℝ) * (u + w).factorial * (u + v).factorial) ^ 2 := by
    simp only [add_zero, sub_zero, fq_natCast]; ring
  rw [hS, hT, hF, Real.sqrt_sq (by positivity)]
  unfold dixonRHS
  rw [show ((2 * w).factorial : ℝ) * ((2 * v).factorial : ℝ) * ((2 * u).factorial : ℝ) =
      ((2 * u).factorial : ℝ) * ((2 * v).factorial : ℝ) * ((2 * w).factorial : ℝ) by ring,
    pow_add]
  have h1 : (u.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (v.factorial : ℝ) ≠ 0 := by positivity
  have h3 : (w.factorial : ℝ) ≠ 0 := by positivity
  have h4 : ((v + w).factorial : ℝ) ≠ 0 := by positivity
  have h5 : ((u + w).factorial : ℝ) ≠ 0 := by positivity
  have h6 : ((u + v).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- **DLMF 34.3.5** (even `J = 2g`), in the form `(-1)^g Δ(j₁j₂j₃) g!/((g-j₁)!(g-j₂)!(g-j₃)!)`
(`Δ² = triSq`, `(J-2jᵢ)!` are the three factorials of `triSq`), under the integrality hypotheses
that `g - jᵢ` are natural numbers (then `jᵢ` are natural numbers). -/
theorem threeJ_zero_zero_zero_even {j₁ j₂ j₃ : ℚ} {g : ℕ} (hg : j₁ + j₂ + j₃ = 2 * g)
    (h₁ : IsNat (g - j₁)) (h₂ : IsNat (g - j₂)) (h₃ : IsNat (g - j₃)) :
    threeJ j₁ j₂ j₃ 0 0 0 =
      (-1 : ℝ) ^ g * Real.sqrt (triSq j₁ j₂ j₃) *
        (fq g / (fq (g - j₁) * fq (g - j₂) * fq (g - j₃))) := by
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  obtain ⟨w, hw⟩ := h₃
  have hgn : g = u + v + w := by
    have : (g : ℚ) = ((u + v + w : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have e1 : j₁ = ((v + w : ℕ) : ℚ) := by push_cast; linarith
  have e2 : j₂ = ((u + w : ℕ) : ℚ) := by push_cast; linarith
  have e3 : j₃ = ((u + v : ℕ) : ℚ) := by push_cast; linarith
  subst e1 e2 e3 hgn
  rw [threeJ_zero_zero_zero u v w, triSq_even,
    show ((u + v + w : ℕ) : ℚ) - ((v + w : ℕ) : ℚ) = (u : ℚ) by push_cast; ring,
    show ((u + v + w : ℕ) : ℚ) - ((u + w : ℕ) : ℚ) = (v : ℚ) by push_cast; ring,
    show ((u + v + w : ℕ) : ℚ) - ((u + v : ℕ) : ℚ) = (w : ℚ) by push_cast; ring,
    fq_natCast, fq_natCast, fq_natCast, fq_natCast,
    show ((2 * w).factorial : ℝ) * ((2 * v).factorial : ℝ) * ((2 * u).factorial : ℝ) =
      ((2 * u).factorial : ℝ) * ((2 * v).factorial : ℝ) * ((2 * w).factorial : ℝ) by ring]

/-- info: 'FormalResearch.Wigner.threeJ_zero_zero_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_zero_zero_zero

/-- info: 'FormalResearch.Wigner.threeJ_zero_zero_zero_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_zero_zero_zero_even

/-- info: 'FormalResearch.Wigner.racahSum3_dixon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racahSum3_dixon

end FormalResearch.Wigner
