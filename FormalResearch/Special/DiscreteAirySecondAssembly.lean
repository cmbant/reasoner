module

public import FormalResearch.Special.DiscreteAirySecondData
public import FormalResearch.Special.AiryParametrixJets

/-!
# Second-order Airy parametrix, part 9: assembly of the `𝔄`, `𝔅` bounds (Q2)

For the paper-form parametrix `ψ̃ = P χ(X) + t Q χ'(X)`, `Q = t³ q₁`, `P = g + h² p`, row operator with
`a = A + h² A₂` at the half-sites and diagonal `c = 2 A Ch(ζ ζ'²) + h² c₂` (`h = t³`), the two functions `𝔄 = a2AA`, `𝔅 = a2BB`
(the coefficients of `χ` and `t χ'` in the exact two-link identity `airy2_identity`) satisfy

  `|𝔄(q, t)|, |𝔅(q, t)| ≤ K |h|³`   uniformly on `q ∈ J`, `0 < t ≤ 1`, `t³ ≤ τ`,

(`airy2_AB_bounds`) under the following hypotheses (the paper's eikonal / transport conditions):

* **eikonal**: built into the definition of `c` (the diagonal is `2 A Ch(ζ ζ'²) + h² c₂`);
* **transport of `g`** (`hrel`): `g² A ζ' Sh(ζ ζ'²) = 1` (first-order amplitude relation; gives the `h¹` coefficient of `𝔅[g, 0]`);
* **the `q₁`-residual equation** (`hq1`): `2 [h²]𝔄 = c₂ g` with the `q₁`-dependence `2 lkA2` (Olver's transport equation
  `2 W q₁' + W' q₁ = -[h²]𝔄[g,0]` in the paper, `a2Res = 0`); `p` drops out of this equation.

**Claim class: proved.**  Not formalised here: the existence of `q₁` (`DiscreteAirySecondTransport` gives it from smooth data).
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- The coefficient `a(q + h/2) = A + h² A₂` at the half-site `q + h/2`. -/
noncomputable def a2coef (A A2 : ℝ → ℝ) (q h : ℝ) : ℝ := A (q + h / 2) + h ^ 2 * A2 (q + h / 2)
/-- The amplitude `P(q + h) = (g + h² p)(q + h)`. -/
noncomputable def a2P (g p : ℝ → ℝ) (q h : ℝ) : ℝ := g (q + h) + h ^ 2 * p (q + h)
/-- The scaled increment `s(h) = (ζ(q + h) - ζ(q))/h`. -/
noncomputable def a2sh (ζ : ℝ → ℝ) (q h : ℝ) : ℝ := (ζ (q + h) - ζ q) / h
/-- The diagonal coefficient `c = 2 A Ch(ζ ζ'²) + h² c₂`. -/
noncomputable def a2c (ζ A c2 : ℝ → ℝ) (q h : ℝ) : ℝ :=
  2 * A q * langerCosh (ζ q * deriv ζ q ^ 2) + h ^ 2 * c2 q

/-- `𝔄`, the coefficient of `χ(X)` in the row defect of `ψ̃` (`h = t³`). -/
noncomputable def a2AA (ζ A A2 g p q1 c2 : ℝ → ℝ) (q t : ℝ) : ℝ :=
  (a2coef A A2 q (t ^ 3) * a2P g p q (t ^ 3) * apuCs (ζ q) t (a2sh ζ q (t ^ 3)) +
      t ^ 3 * (a2coef A A2 q (t ^ 3) * q1 (q + t ^ 3)) * apuCs1 (ζ q) t (a2sh ζ q (t ^ 3))) +
    (a2coef A A2 q (-(t ^ 3)) * a2P g p q (-(t ^ 3)) * apuCs (ζ q) (-t) (a2sh ζ q (-(t ^ 3))) +
      (-t ^ 3) * (a2coef A A2 q (-(t ^ 3)) * q1 (q + -(t ^ 3))) * apuCs1 (ζ q) (-t) (a2sh ζ q (-(t ^ 3)))) -
    a2c ζ A c2 q (t ^ 3) * (g q + (t ^ 3) ^ 2 * p q)

/-- `𝔅`, the coefficient of `t χ'(X)` in the row defect of `ψ̃`. -/
noncomputable def a2BB (ζ A A2 g p q1 c2 : ℝ → ℝ) (q t : ℝ) : ℝ :=
  (a2coef A A2 q (t ^ 3) * a2P g p q (t ^ 3) * apuSs (ζ q) t (a2sh ζ q (t ^ 3)) +
      t ^ 3 * (a2coef A A2 q (t ^ 3) * q1 (q + t ^ 3)) * apuSs1 (ζ q) t (a2sh ζ q (t ^ 3))) -
    (a2coef A A2 q (-(t ^ 3)) * a2P g p q (-(t ^ 3)) * apuSs (ζ q) (-t) (a2sh ζ q (-(t ^ 3))) +
      (-t ^ 3) * (a2coef A A2 q (-(t ^ 3)) * q1 (q + -(t ^ 3))) * apuSs1 (ζ q) (-t) (a2sh ζ q (-(t ^ 3)))) -
    a2c ζ A c2 q (t ^ 3) * (t ^ 3 * q1 q)

/-- The residual of the `q₁`-transport equation: `2 lkA2(G₂ without p) - c₂ g` (`= 0`: Olver's equation
`2 W q₁' + W' q₁ = -[h²]𝔄[g, 0]` of the paper, after `H₀ = A q₁`, `H₁ = A' q₁/2 + A q₁'`). -/
noncomputable def a2Res (ζ A A2 g q1 c2 : ℝ → ℝ) (q : ℝ) : ℝ :=
  2 * lkA2 (ζ q) (deriv ζ q) (deriv (deriv ζ) q) (deriv (deriv (deriv ζ)) q) (a2G0 A g q) (a2G1 A g q)
    (a2G2 A A2 g (fun _ => 0) q) (a2H0 A q1 q) (a2H1 A q1 q) - c2 q * g q

/-- `p` enters `lkA2` only through `A p E`. -/
lemma a2_lkA2_p (ζ A A2 g p q1 : ℝ → ℝ) (q : ℝ) :
    lkA2 (ζ q) (deriv ζ q) (deriv (deriv ζ) q) (deriv (deriv (deriv ζ)) q) (a2G0 A g q) (a2G1 A g q)
      (a2G2 A A2 g p q) (a2H0 A q1 q) (a2H1 A q1 q) =
    lkA2 (ζ q) (deriv ζ q) (deriv (deriv ζ) q) (deriv (deriv (deriv ζ)) q) (a2G0 A g q) (a2G1 A g q)
      (a2G2 A A2 g (fun _ => 0) q) (a2H0 A q1 q) (a2H1 A q1 q) + A q * p q * apuE (ζ q) (deriv ζ q) := by
  unfold lkA2 a2G2
  ring

/-- **The `g`-transport in the `lkS1` form**: `G₀ lkss1 + G₁ A_s = 0` from `g² A ζ' Sh = 1`. -/
lemma a2_transport_S {U : Set ℝ} {ζ A g : ℝ → ℝ} (hU : IsOpen U) (hζ : ContDiffOn ℝ 3 ζ U)
    (hA : ContDiffOn ℝ 2 A U) (hg : ContDiffOn ℝ 2 g U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    {q : ℝ} (hq : q ∈ U) :
    a2G0 A g q * lkss1 (ζ q) (deriv ζ q) (deriv (deriv ζ) q) + a2G1 A g q * apuA (ζ q) (deriv ζ q) = 0 := by
  have hT := apx_transport hU hζ hA hg hrel hq
  have hode := apu2_ode 0 (ζ q * deriv ζ q ^ 2)
  have e1 : apuc 1 (ζ q * deriv ζ q ^ 2) = deriv langerCosh (ζ q * deriv ζ q ^ 2) := by
    rw [apuc_succ]; rfl
  have e2 : apuc 2 (ζ q * deriv ζ q ^ 2) = deriv (deriv langerCosh) (ζ q * deriv ζ q ^ 2) := by
    rw [apuc_succ]; rfl
  rw [e1, e2] at hode
  simp only [Nat.cast_zero, mul_zero, zero_add, zero_add] at hode
  unfold lkss1 apuE apuB apuA a2G0 a2G1
  rw [e1, e2]
  have e0 : apuc 0 (ζ q * deriv ζ q ^ 2) = langerCosh (ζ q * deriv ζ q ^ 2) := rfl
  rw [e0] at hode ⊢
  rw [hode]
  linear_combination (1 / 2) * hT

/-- The `lkδ`-argument of the plus link is the scaled increment. -/
lemma a2_arg (ζ : ℝ → ℝ) (q h : ℝ) :
    deriv ζ q + (h * deriv (deriv ζ) q / 2 + h ^ 2 * deriv (deriv (deriv ζ)) q / 6 + a2e ζ q h) =
      a2sh ζ q h := by
  unfold a2e a2sh; ring

lemma a2_lkG (A A2 g p : ℝ → ℝ) (q h : ℝ) :
    a2G0 A g q + h * a2G1 A g q + h ^ 2 * a2G2 A A2 g p q + (a2G A A2 g p q h -
      (a2G0 A g q + h * a2G1 A g q + h ^ 2 * a2G2 A A2 g p q)) = a2coef A A2 q h * a2P g p q h := by
  unfold a2G a2coef a2P; ring

lemma a2_lkH (A A2 q1 : ℝ → ℝ) (q h : ℝ) :
    a2H0 A q1 q + h * a2H1 A q1 q + (a2H A A2 q1 q h - (a2H0 A q1 q + h * a2H1 A q1 q)) =
      a2coef A A2 q h * q1 (q + h) := by
  unfold a2H a2coef; ring

/-- **Q2: the `𝔄`, `𝔅` bounds.** -/
theorem airy2_AB_bounds {U J : Set ℝ} {ζ A A2 g p q1 c2 : ℝ → ℝ} (hD : Airy2Data U ζ A A2 g p q1)
    (hc2 : ContinuousOn c2 U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    (hq1 : ∀ q ∈ U, a2Res ζ A A2 g q1 c2 q = 0) (hJ : IsCompact J) (hJU : J ⊆ U) :
    ∃ K τ Z0 : ℝ, 0 ≤ K ∧ 0 < τ ∧ τ ≤ 1 ∧ 0 ≤ Z0 ∧ (∀ q ∈ J, |ζ q| ≤ Z0) ∧
      ∀ q t : ℝ, q ∈ J → 0 < t → t ≤ 1 → t ^ 3 ≤ τ →
        |a2AA ζ A A2 g p q1 c2 q t| ≤ K * |t ^ 3| ^ 3 ∧ |a2BB ζ A A2 g p q1 c2 q t| ≤ K * |t ^ 3| ^ 3 := by
  obtain ⟨τ, Z0, S, B, hτ0, hτ1, hZ0, hS, hB, H⟩ := hD.linkData hJ hJU
  obtain ⟨Cc, hCc⟩ := hJ.exists_bound_of_continuousOn (hc2.mono hJU)
  obtain ⟨Cp, hCp⟩ := hJ.exists_bound_of_continuousOn ((hD.hp.continuousOn).mono hJU)
  obtain ⟨Cq, hCq⟩ := hJ.exists_bound_of_continuousOn ((hD.hq1.continuousOn).mono hJU)
  let D : ℝ × ℝ → Prop := fun a => a.1 ∈ J ∧ 0 < a.2 ∧ a.2 ≤ 1 ∧ a.2 ^ 3 ≤ τ
  have hDq : ∀ a, D a → a.1 ∈ J := fun a ha => ha.1
  have L1 := H D (fun a => a.2 ^ 3) (fun a => a.2) (fun a => a.1) hDq (fun a ha =>
    ⟨rfl, ne_of_gt ha.2.1, by rw [abs_of_pos ha.2.1]; exact ha.2.2.1,
      by rw [abs_of_pos (pow_pos ha.2.1 3)]; exact ha.2.2.2⟩)
  have L2 := H D (fun a => -(a.2 ^ 3)) (fun a => -a.2) (fun a => a.1) hDq (fun a ha =>
    ⟨by ring, neg_ne_zero.2 (ne_of_gt ha.2.1), by rw [abs_neg, abs_of_pos ha.2.1]; exact ha.2.2.1,
      by rw [abs_neg, abs_of_pos (pow_pos ha.2.1 3)]; exact ha.2.2.2⟩)
  have hD1 : ∀ a, D a → |a.2 ^ 3| ≤ 1 := fun a ha => by
    rw [abs_of_pos (pow_pos ha.2.1 3)]; exact pow_le_one₀ ha.2.1.le ha.2.2.1
  obtain ⟨Mz, hMz⟩ := hJ.exists_bound_of_continuousOn ((hD.hζ.continuousOn).mono hJU)
  have hZA : SOB D (fun a => a.2 ^ 3) 3 (fun a => a2c ζ A c2 a.1 (a.2 ^ 3) * (g a.1 + (a.2 ^ 3) ^ 2 * p a.1) -
      (2 * lkA0 (ζ a.1) (deriv ζ a.1) (a2G0 A g a.1) + (a.2 ^ 3) ^ 2 *
        (2 * lkA2 (ζ a.1) (deriv ζ a.1) (deriv (deriv ζ) a.1) (deriv (deriv (deriv ζ)) a.1) (a2G0 A g a.1)
          (a2G1 A g a.1) (a2G2 A A2 g p a.1) (a2H0 A q1 a.1) (a2H1 A q1 a.1)))) := by
    have hb : SOB D (fun a => a.2 ^ 3) 0 (fun a => c2 a.1 * p a.1) :=
      SOB.bdd (M := Cc * Cp) fun a ha => by
        rw [abs_mul]
        exact mul_le_mul (by simpa using hCc a.1 ha.1) (by simpa using hCp a.1 ha.1) (abs_nonneg _)
          ((norm_nonneg _).trans (hCc a.1 ha.1))
    refine (((SOB.hh_pow (D := D) (hh := fun a => a.2 ^ 3) 4).mul hb).mono hD1 (by norm_num)).congr
      fun a ha => ?_
    have hres := hq1 a.1 (hJU ha.1)
    unfold a2Res at hres
    have hp := a2_lkA2_p ζ A A2 g p q1 a.1
    simp only [apuE, apuc, Function.iterate_zero, id_eq, a2G0] at hp hres
    simp only [a2c, lkA0, apuE, apuc, Function.iterate_zero, id_eq, a2G0]
    rw [hp]
    linear_combination ((a.2 ^ 3) ^ 2) * hres
  have hZS : SOB D (fun a => a.2 ^ 3) 3 (fun a => a2c ζ A c2 a.1 (a.2 ^ 3) * (a.2 ^ 3 * q1 a.1) -
      a.2 ^ 3 * (2 * lkS1 (ζ a.1) (deriv ζ a.1) (deriv (deriv ζ) a.1) (a2G0 A g a.1) (a2G1 A g a.1)
        (a2H0 A q1 a.1))) := by
    have hb : SOB D (fun a => a.2 ^ 3) 0 (fun a => c2 a.1 * q1 a.1) :=
      SOB.bdd (M := Cc * Cq) fun a ha => by
        rw [abs_mul]
        exact mul_le_mul (by simpa using hCc a.1 ha.1) (by simpa using hCq a.1 ha.1) (abs_nonneg _)
          ((norm_nonneg _).trans (hCc a.1 ha.1))
    refine ((SOB.hh_pow (D := D) (hh := fun a => a.2 ^ 3) 3).mul hb).congr fun a ha => ?_
    have hT := a2_transport_S hD.hU (hD.hζ.of_le (by norm_num)) (hD.hA.of_le (by norm_num))
      (hD.hg.of_le (by norm_num)) hrel (hJU ha.1)
    have hE : apuE (ζ a.1) (deriv ζ a.1) = langerCosh (ζ a.1 * deriv ζ a.1 ^ 2) := rfl
    unfold lkS1 a2c a2H0
    rw [hE]
    linear_combination (2 * a.2 ^ 3) * hT
  have kA := pair_A (Zc := fun a => a2c ζ A c2 a.1 (a.2 ^ 3) * (g a.1 + (a.2 ^ 3) ^ 2 * p a.1))
    (Zc0 := fun a => 2 * lkA0 (ζ a.1) (deriv ζ a.1) (a2G0 A g a.1))
    (Zc2 := fun a => 2 * lkA2 (ζ a.1) (deriv ζ a.1) (deriv (deriv ζ) a.1) (deriv (deriv (deriv ζ)) a.1)
      (a2G0 A g a.1) (a2G1 A g a.1) (a2G2 A A2 g p a.1) (a2H0 A q1 a.1) (a2H1 A q1 a.1))
    L1 L2 hZA (fun a _ => rfl) (fun a _ => rfl)
  have kS := pair_S (Zc := fun a => a2c ζ A c2 a.1 (a.2 ^ 3) * (a.2 ^ 3 * q1 a.1)) L1 L2 hZS
  have kA' : SOB D (fun a => a.2 ^ 3) 3 (fun a => a2AA ζ A A2 g p q1 c2 a.1 a.2) := by
    refine kA.congr fun a ha => ?_
    simp only [lkG, lkδ, lkH, a2_lkG, a2_lkH, a2_arg]
    unfold a2AA
    ring
  have kS' : SOB D (fun a => a.2 ^ 3) 3 (fun a => a2BB ζ A A2 g p q1 c2 a.1 a.2) := by
    refine kS.congr fun a ha => ?_
    simp only [lkG, lkδ, lkH, a2_lkG, a2_lkH, a2_arg]
    unfold a2BB
    ring
  obtain ⟨KA, hKA, hbA⟩ := kA'
  obtain ⟨KB, hKB, hbB⟩ := kS'
  refine ⟨max KA KB, τ, max Mz 0, le_max_of_le_left hKA, hτ0, hτ1, le_max_right _ _, fun q hq => ?_, ?_⟩
  · exact (by simpa using hMz q hq : |ζ q| ≤ Mz).trans (le_max_left _ _)
  · intro q t hq ht0 ht1 ht3
    have hDa : D (q, t) := ⟨hq, ht0, ht1, ht3⟩
    refine ⟨(hbA (q, t) hDa).trans ?_, (hbB (q, t) hDa).trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- info: 'FormalResearch.Special.airy2_AB_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy2_AB_bounds

end FormalResearch.Special
