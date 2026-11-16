module

public import FormalResearch.Special.DiscreteAirySecondAssembly
public import FormalResearch.Special.DiscreteAirySecondAiry
public import FormalResearch.Special.DiscreteAiryOscBi
public import FormalResearch.Special.DiscreteAiryLimitDefect

/-!
# Second-order Airy parametrix, part 10: the paper-form row defect (Q3)

For a real solution `(y, y')` of `y'' = x y` with envelope bounds `|y| ≤ C_y w`, `|y'| ≤ C_{y'} √(2+|x|) w`, and the paper-form
parametrix `Ψ_t(q) = P(q) y(ζ(q)/t²) + t (t³ q₁(q)) y'(ζ(q)/t²)`, `P = g + t⁶ p`, the three-term row with
`a = A + t⁶ A₂` at the half-sites and diagonal `c = 2 A Ch(ζ ζ'²) + t⁶ c₂` satisfies

  `|row(q)| ≤ K |t³|³ w(ζ(q)/t²)`   for `q ∈ J`, `0 < t ≤ 1`, `t³ ≤ τ`

(`airy2_defect_point`), and on the lattice `q_k = q₀ + k δ³` (`airy2_defect_lattice`, `h = δ³`, defect `K δ⁹ w(X_k)`,
`X_k = ζ(q_k)/δ²`).  Instances `y = Ai` (`w = airyWt`) and `y = Bi` (`w = airyBiWt`): `airy2_defect_Ai`, `airy2_defect_Bi`.
Hypotheses as in `DiscreteAirySecondAssembly`.  **Claim class: proved**; constants existential.
-/

@[expose] public section

open Set FormalResearch.DiscreteAiry

namespace FormalResearch.Special

open SturmAiry

/-- The paper-form parametrix at scale `t` (`h = t³`): `(g + h² p) y(ζ/t²) + t · h q₁ · y'(ζ/t²)`. -/
noncomputable def a2Psi (ζ g p q1 y y' : ℝ → ℝ) (t q : ℝ) : ℝ :=
  (g q + (t ^ 3) ^ 2 * p q) * y (ζ q / t ^ 2) + t * (t ^ 3 * q1 q) * y' (ζ q / t ^ 2)

/-- **The row defect at one point (generic Airy solution).** -/
theorem airy2_defect_point {y y' w : ℝ → ℝ} (hy : IsAirySol y y') (Cy Cy' : ℝ) (hCy : 0 ≤ Cy)
    (hCy' : 0 ≤ Cy') (hw0 : ∀ x, 0 ≤ w x) (hyb : ∀ x, |y x| ≤ Cy * w x)
    (hyb' : ∀ x, |y' x| ≤ Cy' * √(2 + |x|) * w x) {U J : Set ℝ} {ζ A A2 g p q1 c2 : ℝ → ℝ}
    (hD : Airy2Data U ζ A A2 g p q1) (hc2 : ContinuousOn c2 U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    (hq1 : ∀ q ∈ U, a2Res ζ A A2 g q1 c2 q = 0) (hJ : IsCompact J) (hJU : J ⊆ U) :
    ∃ K τ : ℝ, 0 ≤ K ∧ 0 < τ ∧ τ ≤ 1 ∧ ∀ q t : ℝ, q ∈ J → 0 < t → t ≤ 1 → t ^ 3 ≤ τ →
      |a2coef A A2 q (t ^ 3) * a2Psi ζ g p q1 y y' t (q + t ^ 3) +
          a2coef A A2 q (-(t ^ 3)) * a2Psi ζ g p q1 y y' t (q + -(t ^ 3)) -
          a2c ζ A c2 q (t ^ 3) * a2Psi ζ g p q1 y y' t q| ≤ K * |t ^ 3| ^ 3 * w (ζ q / t ^ 2) := by
  obtain ⟨K0, τ, Z0, hK0, hτ, hτ1, hZ0, hzb, H⟩ := airy2_AB_bounds hD hc2 hrel hq1 hJ hJU
  refine ⟨Cy * K0 + Cy' * √(2 + Z0) * K0, τ, by positivity, hτ, hτ1, fun q t hq ht0 ht1 ht3 => ?_⟩
  obtain ⟨hA, hB⟩ := H q t hq ht0 ht1 ht3
  have htne : t ≠ 0 := ne_of_gt ht0
  have h3 : t ^ 3 ≠ 0 := pow_ne_zero 3 htne
  have hid := airy2_identity hy t (ζ q) (a2sh ζ q (t ^ 3)) (-(a2sh ζ q (-(t ^ 3))))
    (a2coef A A2 q (t ^ 3)) (a2coef A A2 q (-(t ^ 3))) (a2P g p q (t ^ 3)) (a2P g p q (-(t ^ 3)))
    (g q + (t ^ 3) ^ 2 * p q) (q1 (q + t ^ 3)) (q1 (q + -(t ^ 3))) (q1 q) (a2c ζ A c2 q (t ^ 3)) htne
  have e1 : ζ q / t ^ 2 + t * a2sh ζ q (t ^ 3) = ζ (q + t ^ 3) / t ^ 2 := by
    unfold a2sh; field_simp; ring
  have e2 : ζ q / t ^ 2 + t * -(a2sh ζ q (-(t ^ 3))) = ζ (q + -(t ^ 3)) / t ^ 2 := by
    unfold a2sh; field_simp; ring
  rw [e1, e2] at hid
  simp only [neg_neg] at hid
  have hrow : a2coef A A2 q (t ^ 3) * a2Psi ζ g p q1 y y' t (q + t ^ 3) +
      a2coef A A2 q (-(t ^ 3)) * a2Psi ζ g p q1 y y' t (q + -(t ^ 3)) -
      a2c ζ A c2 q (t ^ 3) * a2Psi ζ g p q1 y y' t q =
      y (ζ q / t ^ 2) * a2AA ζ A A2 g p q1 c2 q t + t * y' (ζ q / t ^ 2) * a2BB ζ A A2 g p q1 c2 q t := by
    unfold a2Psi a2AA a2BB a2P
    unfold a2P at hid
    linear_combination hid
  rw [hrow]
  have := airy2_defect_of_AB (y := y) (y' := y') (w := w) Cy Cy' hCy hCy' hyb hyb' hw0 htne
    (by rw [abs_of_pos ht0]; exact ht1) ((by simpa using hzb q hq : |ζ q| ≤ Z0)) hA hB
  convert this using 2

/-- **The lattice row defect (generic solution), `h = δ³`.** -/
theorem airy2_defect_lattice {y y' w : ℝ → ℝ} (hy : IsAirySol y y') (Cy Cy' : ℝ) (hCy : 0 ≤ Cy)
    (hCy' : 0 ≤ Cy') (hw0 : ∀ x, 0 ≤ w x) (hyb : ∀ x, |y x| ≤ Cy * w x)
    (hyb' : ∀ x, |y' x| ≤ Cy' * √(2 + |x|) * w x) {U J : Set ℝ} {ζ A A2 g p q1 c2 : ℝ → ℝ}
    (hD : Airy2Data U ζ A A2 g p q1) (hc2 : ContinuousOn c2 U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    (hq1 : ∀ q ∈ U, a2Res ζ A A2 g q1 c2 q = 0) (hJ : IsCompact J) (hJU : J ⊆ U) :
    ∃ K δ0 : ℝ, 0 < K ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∀ k : ℤ, dalQ q₀ δ k ∈ J →
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2) + (δ ^ 3) ^ 2 * A2 (dalQ q₀ δ j - δ ^ 3 / 2))
          (fun j => a2c ζ A c2 (dalQ q₀ δ j) (δ ^ 3))
          (fun j => a2Psi ζ g p q1 y y' δ (dalQ q₀ δ j)) k| ≤
        K * |δ ^ 3| ^ 3 * w (ζ (dalQ q₀ δ k) / δ ^ 2) := by
  obtain ⟨K, τ, hK, hτ, hτ1, H⟩ := airy2_defect_point hy Cy Cy' hCy hCy' hw0 hyb hyb' hD hc2 hrel hq1 hJ hJU
  refine ⟨K + 1, τ, by linarith, hτ, hτ1, fun δ q₀ hδ hδτ k hk => ?_⟩
  have hδ1 : δ ≤ 1 := hδτ.trans hτ1
  have h3 : δ ^ 3 ≤ τ := by
    have : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2, pow_pos hδ 3]
    linarith
  have hq1' : dalQ q₀ δ (k + 1) = dalQ q₀ δ k + δ ^ 3 := by unfold dalQ; push_cast; ring
  have hq2' : dalQ q₀ δ (k - 1) = dalQ q₀ δ k + -(δ ^ 3) := by unfold dalQ; push_cast; ring
  have key := H (dalQ q₀ δ k) δ hk hδ hδ1 h3
  have e1 : dalQ q₀ δ k + δ ^ 3 - δ ^ 3 / 2 = dalQ q₀ δ k + δ ^ 3 / 2 := by ring
  unfold jac
  simp only [hq1', hq2', e1]
  have hcoef : A (dalQ q₀ δ k - δ ^ 3 / 2) + (δ ^ 3) ^ 2 * A2 (dalQ q₀ δ k - δ ^ 3 / 2) =
      a2coef A A2 (dalQ q₀ δ k) (-(δ ^ 3)) := by
    unfold a2coef
    have : dalQ q₀ δ k + -(δ ^ 3) / 2 = dalQ q₀ δ k - δ ^ 3 / 2 := by ring
    rw [this]; ring
  rw [hcoef]
  have hc' : a2coef A A2 (dalQ q₀ δ k) (δ ^ 3) = A (dalQ q₀ δ k + δ ^ 3 / 2) +
      (δ ^ 3) ^ 2 * A2 (dalQ q₀ δ k + δ ^ 3 / 2) := rfl
  rw [← hc']
  have hw := hw0 (ζ (dalQ q₀ δ k) / δ ^ 2)
  calc _ ≤ K * |δ ^ 3| ^ 3 * w (ζ (dalQ q₀ δ k) / δ ^ 2) := key
    _ ≤ _ := by
      have : 0 ≤ |δ ^ 3| ^ 3 * w (ζ (dalQ q₀ δ k) / δ ^ 2) := by positivity
      nlinarith

/-- **The `Ai` row defect on the lattice**: `|row| ≤ K (δ³)³ airyWt(ζ(q_k)/δ²)`. -/
theorem airy2_defect_Ai {U J : Set ℝ} {ζ A A2 g p q1 c2 : ℝ → ℝ} (hD : Airy2Data U ζ A A2 g p q1)
    (hc2 : ContinuousOn c2 U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    (hq1 : ∀ q ∈ U, a2Res ζ A A2 g q1 c2 q = 0) (hJ : IsCompact J) (hJU : J ⊆ U) :
    ∃ K δ0 : ℝ, 0 < K ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∀ k : ℤ, dalQ q₀ δ k ∈ J →
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2) + (δ ^ 3) ^ 2 * A2 (dalQ q₀ δ j - δ ^ 3 / 2))
          (fun j => a2c ζ A c2 (dalQ q₀ δ j) (δ ^ 3))
          (fun j => a2Psi ζ g p q1 airyAi airyAi' δ (dalQ q₀ δ j)) k| ≤
        K * |δ ^ 3| ^ 3 * airyWt (ζ (dalQ q₀ δ k) / δ ^ 2) :=
  airy2_defect_lattice isAirySol_airyAi 25 132500 (by norm_num) (by norm_num) (fun x => (airyWt_pos x).le)
    (fun x => (apx_airy_global x).1) (fun x => (apx_airy_global x).2) hD hc2 hrel hq1 hJ hJU

/-- **The `Bi` row defect on the lattice**: `|row| ≤ K (δ³)³ airyBiWt(ζ(q_k)/δ²)`. -/
theorem airy2_defect_Bi {U J : Set ℝ} {ζ A A2 g p q1 c2 : ℝ → ℝ} (hD : Airy2Data U ζ A A2 g p q1)
    (hc2 : ContinuousOn c2 U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    (hq1 : ∀ q ∈ U, a2Res ζ A A2 g q1 c2 q = 0) (hJ : IsCompact J) (hJU : J ⊆ U) :
    ∃ K δ0 : ℝ, 0 < K ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∀ k : ℤ, dalQ q₀ δ k ∈ J →
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2) + (δ ^ 3) ^ 2 * A2 (dalQ q₀ δ j - δ ^ 3 / 2))
          (fun j => a2c ζ A c2 (dalQ q₀ δ j) (δ ^ 3))
          (fun j => a2Psi ζ g p q1 airyBi airyBiDeriv δ (dalQ q₀ δ j)) k| ≤
        K * |δ ^ 3| ^ 3 * airyBiWt (ζ (dalQ q₀ δ k) / δ ^ 2) :=
  airy2_defect_lattice isAirySol_airyBi_shift 450 2385000 (by norm_num) (by norm_num)
    (fun x => (airyBiWt_pos x).le) (fun x => (apx_airyBi_global x).1) (fun x => (apx_airyBi_global x).2)
    hD hc2 hrel hq1 hJ hJU

/-- info: 'FormalResearch.Special.airy2_defect_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy2_defect_point

/-- info: 'FormalResearch.Special.airy2_defect_Ai' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy2_defect_Ai

/-- info: 'FormalResearch.Special.airy2_defect_Bi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy2_defect_Bi

end FormalResearch.Special
