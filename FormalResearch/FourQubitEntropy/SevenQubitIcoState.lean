import Mathlib

/-!
# The seven-qubit icosahedral family's state and reduced matrices

This defines the two integer coefficient tensors in `eq:ico` and checks their support counts and
orthogonality (`thm:ico` in `ResearchNotes/QI/seven_qubit_entanglement/icosahedral_state.tex`). Together with the scalar parameterization, this proves unit norm. It also derives the
three-qubit reduced-matrix entries for one representative cut of each type, directly from the state
tensor.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-- The parameter `u = α²` in the icosahedral family. -/
noncomputable def u (x : ℝ) : ℝ := (1 - 2 * x) / 30

/-- The support counts `30` and `2` give the unit-norm coefficient identity. -/
theorem coefficient_norm_identity (x : ℝ) : 30 * u x + 2 * x = 1 := by
  unfold u
  ring

abbrev BitString := Fin 7 → Bool
abbrev Tail := Fin 6 → Bool

def tail (z : BitString) : Tail := fun i => z i.succ

def tailWeight (s : Tail) : ℕ :=
  ∑ i : Fin 6, if s i then 1 else 0

def negativePair (s : Tail) : Bool :=
  (s 1 && s 3) || (s 2 && s 3) || (s 2 && s 4) || (s 4 && s 5) || (s 1 && s 5)

/-- Integer coefficient of `α` in the state formula `eq:ico`. -/
def alphaCoefficient (z : BitString) : ℤ :=
  if !z 0 && tailWeight (tail z) = 2 then
    if negativePair (tail z) then -1 else 1
  else if z 0 && tailWeight (tail z) = 4 then
    if negativePair (fun i => !(tail z i)) then 1 else -1
  else 0

/-- Integer coefficient of `β` in the state formula `eq:ico`. -/
def betaCoefficient (z : BitString) : ℤ :=
  if !z 0 && tailWeight (tail z) = 6 then 1
  else if z 0 && tailWeight (tail z) = 0 then 1
  else 0

theorem alpha_coefficient_norm : ∑ z : BitString, alphaCoefficient z ^ 2 = 30 := by
  decide +kernel

theorem beta_coefficient_norm : ∑ z : BitString, betaCoefficient z ^ 2 = 2 := by
  decide +kernel

theorem coefficient_cross_term :
    ∑ z : BitString, alphaCoefficient z * betaCoefficient z = 0 := by
  decide +kernel

/-- The real-amplitude version of `ψ_x` from equation `eq:ico`. -/
def icosahedralState (alpha beta : ℝ) (z : BitString) : ℝ :=
  alpha * alphaCoefficient z + beta * betaCoefficient z

theorem icosahedralState_norm_sq (alpha beta : ℝ) :
    ∑ z : BitString, icosahedralState alpha beta z ^ 2 = 30 * alpha ^ 2 + 2 * beta ^ 2 := by
  have hA :
      ∑ z : BitString, (alphaCoefficient z : ℝ) ^ 2 = 30 := by
    exact_mod_cast alpha_coefficient_norm
  have hB :
      ∑ z : BitString, (betaCoefficient z : ℝ) ^ 2 = 2 := by
    exact_mod_cast beta_coefficient_norm
  have hAB :
      ∑ z : BitString, (alphaCoefficient z : ℝ) * betaCoefficient z = 0 := by
    exact_mod_cast coefficient_cross_term
  calc
    ∑ z : BitString, icosahedralState alpha beta z ^ 2 =
        ∑ z : BitString,
          (alpha ^ 2 * (alphaCoefficient z : ℝ) ^ 2 +
            (2 * alpha * beta) * (alphaCoefficient z : ℝ) * betaCoefficient z +
            beta ^ 2 * (betaCoefficient z : ℝ) ^ 2) := by
      apply Finset.sum_congr rfl
      intro z hz
      simp only [icosahedralState]
      ring
    _ = alpha ^ 2 * (∑ z : BitString, (alphaCoefficient z : ℝ) ^ 2) +
          (2 * alpha * beta) * (∑ z : BitString,
            (alphaCoefficient z : ℝ) * betaCoefficient z) +
          beta ^ 2 * (∑ z : BitString, (betaCoefficient z : ℝ) ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    _ = 30 * alpha ^ 2 + 2 * beta ^ 2 := by rw [hA, hAB, hB]; ring

theorem icosahedralState_unit_norm (x alpha beta : ℝ)
    (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x) :
    ∑ z : BitString, icosahedralState alpha beta z ^ 2 = 1 := by
  rw [icosahedralState_norm_sq, hα, hβ]
  have h := coefficient_norm_identity x
  nlinarith

def siteInputs (q : Fin 7) : Finset BitString :=
  Finset.univ.filter (fun z => z q = false)

def flipSiteToOne (q : Fin 7) (z : BitString) : BitString :=
  Function.update z q true

def selectSite (q : Fin 7) (a : Bool) (z : BitString) : BitString :=
  if a then flipSiteToOne q z else z

def integerPairSum (f g : BitString → ℤ) (q : Fin 7) (a b : Bool) : ℤ :=
  ∑ z ∈ siteInputs q, f (selectSite q a z) * g (selectSite q b z)

theorem alpha_pair_sum (q : Fin 7) (a b : Bool) :
    integerPairSum alphaCoefficient alphaCoefficient q a b = if a = b then 15 else 0 := by
  fin_cases q <;> fin_cases a <;> fin_cases b <;> decide +kernel

theorem beta_pair_sum (q : Fin 7) (a b : Bool) :
    integerPairSum betaCoefficient betaCoefficient q a b = if a = b then 1 else 0 := by
  fin_cases q <;> fin_cases a <;> fin_cases b <;> decide +kernel

theorem alpha_beta_pair_sum (q : Fin 7) (a b : Bool) :
    integerPairSum alphaCoefficient betaCoefficient q a b = 0 := by
  fin_cases q <;> fin_cases a <;> fin_cases b <;> decide +kernel

theorem beta_alpha_pair_sum (q : Fin 7) (a b : Bool) :
    integerPairSum betaCoefficient alphaCoefficient q a b = 0 := by
  fin_cases q <;> fin_cases a <;> fin_cases b <;> decide +kernel

def realPairSum (f g : BitString → ℝ) (q : Fin 7) (a b : Bool) : ℝ :=
  ∑ z ∈ siteInputs q, f (selectSite q a z) * g (selectSite q b z)

def alphaReal : BitString → ℝ := fun z => alphaCoefficient z
def betaReal : BitString → ℝ := fun z => betaCoefficient z

theorem alpha_real_pair_sum (q : Fin 7) (a b : Bool) :
    realPairSum alphaReal alphaReal q a b = if a = b then 15 else 0 := by
  have h := alpha_pair_sum q a b
  unfold integerPairSum at h
  unfold realPairSum alphaReal
  exact_mod_cast h

theorem beta_real_pair_sum (q : Fin 7) (a b : Bool) :
    realPairSum betaReal betaReal q a b = if a = b then 1 else 0 := by
  have h := beta_pair_sum q a b
  unfold integerPairSum at h
  unfold realPairSum betaReal
  exact_mod_cast h

theorem alpha_beta_real_pair_sum (q : Fin 7) (a b : Bool) :
    realPairSum alphaReal betaReal q a b = 0 := by
  have h := alpha_beta_pair_sum q a b
  unfold integerPairSum at h
  unfold realPairSum alphaReal betaReal
  exact_mod_cast h

theorem beta_alpha_real_pair_sum (q : Fin 7) (a b : Bool) :
    realPairSum betaReal alphaReal q a b = 0 := by
  have h := beta_alpha_pair_sum q a b
  unfold integerPairSum at h
  unfold realPairSum betaReal alphaReal
  exact_mod_cast h

/-- Reduced one-qubit matrix entry, summing over basis states with the site bit fixed to zero. -/
def oneQubitEntry (alpha beta : ℝ) (q : Fin 7) (a b : Bool) : ℝ :=
  ∑ z ∈ siteInputs q,
    icosahedralState alpha beta (selectSite q a z) *
      icosahedralState alpha beta (selectSite q b z)

theorem oneQubitEntry_expand (alpha beta : ℝ) (q : Fin 7) (a b : Bool) :
    oneQubitEntry alpha beta q a b =
      alpha ^ 2 * realPairSum alphaReal alphaReal q a b +
        alpha * beta * realPairSum alphaReal betaReal q a b +
        alpha * beta * realPairSum betaReal alphaReal q a b +
        beta ^ 2 * realPairSum betaReal betaReal q a b := by
  unfold oneQubitEntry
  calc
    _ = ∑ z ∈ siteInputs q,
        (alpha ^ 2 * (alphaReal (selectSite q a z) * alphaReal (selectSite q b z)) +
          alpha * beta * (alphaReal (selectSite q a z) * betaReal (selectSite q b z)) +
          alpha * beta * (betaReal (selectSite q a z) * alphaReal (selectSite q b z)) +
          beta ^ 2 * (betaReal (selectSite q a z) * betaReal (selectSite q b z))) := by
      apply Finset.sum_congr rfl
      intro z hz
      simp only [icosahedralState, alphaReal, betaReal]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, realPairSum]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

theorem oneQubitEntry_eq (x alpha beta : ℝ) (q : Fin 7) (a b : Bool)
    (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x) :
    oneQubitEntry alpha beta q a b = if a = b then 1 / 2 else 0 := by
  rw [oneQubitEntry_expand, alpha_real_pair_sum, alpha_beta_real_pair_sum,
    beta_alpha_real_pair_sum, beta_real_pair_sum, hα, hβ]
  have h := coefficient_norm_identity x
  by_cases hab : a = b
  · simp [hab] at *
    nlinarith
  · simp [hab] at *

abbrev TripleAssignment := Fin 3 → Bool
abbrev RestAssignment := Fin 4 → Bool

def avoidingSpecialIndex (a : TripleAssignment) (r : RestAssignment) : BitString :=
  fun i =>
    if i = 0 then r 0
    else if i = 1 then a 0
    else if i = 2 then a 1
    else if i = 3 then a 2
    else if i = 4 then r 1
    else if i = 5 then r 2
    else r 3

def containingSpecialIndex (a : TripleAssignment) (r : RestAssignment) : BitString :=
  fun i =>
    if i = 0 then a 0
    else if i = 1 then a 1
    else if i = 2 then a 2
    else if i = 3 then r 0
    else if i = 4 then r 1
    else if i = 5 then r 2
    else r 3

def coefficientGram (encode : TripleAssignment → RestAssignment → BitString)
    (f g : BitString → ℤ) (a b : TripleAssignment) : ℤ :=
  ∑ r : RestAssignment, f (encode a r) * g (encode b r)

/-- A reduced density-matrix entry, with `encode` splitting a cut from its complement. -/
def reducedEntry (encode : TripleAssignment → RestAssignment → BitString)
    (alpha beta : ℝ) (a b : TripleAssignment) : ℝ :=
  ∑ r : RestAssignment,
    icosahedralState alpha beta (encode a r) * icosahedralState alpha beta (encode b r)

theorem reducedEntry_expand (encode : TripleAssignment → RestAssignment → BitString)
    (alpha beta : ℝ) (a b : TripleAssignment) :
    reducedEntry encode alpha beta a b =
      alpha ^ 2 * (coefficientGram encode alphaCoefficient alphaCoefficient a b : ℝ) +
        alpha * beta * (coefficientGram encode alphaCoefficient betaCoefficient a b : ℝ) +
        alpha * beta * (coefficientGram encode betaCoefficient alphaCoefficient a b : ℝ) +
        beta ^ 2 * (coefficientGram encode betaCoefficient betaCoefficient a b : ℝ) := by
  unfold reducedEntry coefficientGram
  calc
    _ = ∑ r : RestAssignment,
        (alpha ^ 2 * ((alphaCoefficient (encode a r) : ℝ) *
            alphaCoefficient (encode b r)) +
          alpha * beta * ((alphaCoefficient (encode a r) : ℝ) *
            betaCoefficient (encode b r)) +
          alpha * beta * ((betaCoefficient (encode a r) : ℝ) *
            alphaCoefficient (encode b r)) +
          beta ^ 2 * ((betaCoefficient (encode a r) : ℝ) *
            betaCoefficient (encode b r))) := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [icosahedralState]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Int.cast_sum, Int.cast_mul]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

def zeroTriple : TripleAssignment := fun _ => false
def oneTriple : TripleAssignment := fun _ => true
def containingSpecialMixedA : TripleAssignment := fun i => decide (i.val ≠ 0)
def containingSpecialMixedB : TripleAssignment := fun i => decide (i.val = 0)

theorem avoiding_aa (a b : TripleAssignment) :
    coefficientGram avoidingSpecialIndex alphaCoefficient alphaCoefficient a b =
      if a = b then if a = zeroTriple ∨ a = oneTriple then 3 else 4 else 0 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem avoiding_bb (a b : TripleAssignment) :
    coefficientGram avoidingSpecialIndex betaCoefficient betaCoefficient a b =
      if a = b then if a = zeroTriple ∨ a = oneTriple then 1 else 0 else 0 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem avoiding_ab (a b : TripleAssignment) :
    coefficientGram avoidingSpecialIndex alphaCoefficient betaCoefficient a b = 0 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem avoiding_ba (a b : TripleAssignment) :
    coefficientGram avoidingSpecialIndex betaCoefficient alphaCoefficient a b = 0 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem containing_aa (a b : TripleAssignment) :
    coefficientGram containingSpecialIndex alphaCoefficient alphaCoefficient a b =
      if a = b then
        if a = zeroTriple ∨ a = oneTriple then 6
        else if a = containingSpecialMixedA then 1
        else if a = containingSpecialMixedB then 1
        else 4
      else if (a = zeroTriple ∧ b = oneTriple) ∨ (a = oneTriple ∧ b = zeroTriple) then -2
      else 0 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem containing_bb (a b : TripleAssignment) :
    coefficientGram containingSpecialIndex betaCoefficient betaCoefficient a b =
      if a = b then
        if a = containingSpecialMixedA then 1
        else if a = containingSpecialMixedB then 1
        else 0
      else 0 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem special_triples_distinct :
    zeroTriple ≠ containingSpecialMixedA ∧ zeroTriple ≠ containingSpecialMixedB ∧
      oneTriple ≠ containingSpecialMixedA ∧ oneTriple ≠ containingSpecialMixedB := by
  decide +kernel

/-- On the cut containing the special qubit the `α`-`β` Gram matrix is not zero (its only entries are
`±1`, between the two mixed triples), but it is antisymmetric, so the cross terms of the reduced
entry cancel. -/
theorem containing_ab_add_ba (a b : TripleAssignment) :
    coefficientGram containingSpecialIndex alphaCoefficient betaCoefficient a b +
      coefficientGram containingSpecialIndex betaCoefficient alphaCoefficient a b = 0 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem reducedEntry_avoidingSpecial (alpha beta : ℝ) (a b : TripleAssignment) :
    reducedEntry avoidingSpecialIndex alpha beta a b =
      if a = b then
        if a = zeroTriple ∨ a = oneTriple then 3 * alpha ^ 2 + beta ^ 2
        else 4 * alpha ^ 2
      else 0 := by
  rw [reducedEntry_expand, avoiding_aa, avoiding_ab, avoiding_ba, avoiding_bb]
  split_ifs <;> push_cast <;> ring

theorem reducedEntry_containingSpecial (alpha beta : ℝ) (a b : TripleAssignment) :
    reducedEntry containingSpecialIndex alpha beta a b =
      if a = b then
        if a = zeroTriple ∨ a = oneTriple then 6 * alpha ^ 2
        else if a = containingSpecialMixedA then alpha ^ 2 + beta ^ 2
        else if a = containingSpecialMixedB then alpha ^ 2 + beta ^ 2
        else 4 * alpha ^ 2
      else if (a = zeroTriple ∧ b = oneTriple) ∨ (a = oneTriple ∧ b = zeroTriple) then
        -2 * alpha ^ 2
      else 0 := by
  have hx : alpha * beta *
        (coefficientGram containingSpecialIndex alphaCoefficient betaCoefficient a b : ℝ) +
      alpha * beta *
        (coefficientGram containingSpecialIndex betaCoefficient alphaCoefficient a b : ℝ) = 0 := by
    rw [← mul_add]
    have h := containing_ab_add_ba a b
    have h' : ((coefficientGram containingSpecialIndex alphaCoefficient betaCoefficient a b +
        coefficientGram containingSpecialIndex betaCoefficient alphaCoefficient a b : ℤ) : ℝ) = 0 := by
      rw [h]; simp
    push_cast at h'
    rw [h']; simp
  obtain ⟨h0A, h0B, h1A, h1B⟩ := special_triples_distinct
  rw [reducedEntry_expand, containing_aa, containing_bb]
  by_cases hab : a = b
  · subst hab
    by_cases h0 : a = zeroTriple ∨ a = oneTriple
    · have hA : a ≠ containingSpecialMixedA := by rcases h0 with rfl | rfl <;> assumption
      have hB : a ≠ containingSpecialMixedB := by rcases h0 with rfl | rfl <;> assumption
      simp only [ite_true, h0, hA, hB, ite_false]
      push_cast
      linarith
    · by_cases hA : a = containingSpecialMixedA
      · simp only [ite_true, h0, eq_true hA, ite_false]
        push_cast
        linarith
      · by_cases hB : a = containingSpecialMixedB
        · simp only [ite_true, h0, hA, eq_true hB, ite_false]
          push_cast
          linarith
        · simp only [ite_true, h0, hA, hB, ite_false]
          push_cast
          linarith
  · by_cases h : (a = zeroTriple ∧ b = oneTriple) ∨ (a = oneTriple ∧ b = zeroTriple)
    · simp only [hab, h, ite_true, ite_false]
      push_cast
      linarith
    · simp only [hab, h, ite_false]
      push_cast
      linarith

end FormalResearch.FourQubitEntropy.SevenQubitIco
