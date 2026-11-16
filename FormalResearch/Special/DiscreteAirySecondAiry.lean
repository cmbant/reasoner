module

public import FormalResearch.Special.DiscreteAirySecondPair
public import FormalResearch.Special.AiryParametrixUniformPointwise
public import FormalResearch.Special.AiryShift

/-!
# Second-order Airy parametrix, part 6: from the links to the lattice defect (generic solution `χ'' = x χ`)

For a real solution `(y, y')` of `y'' = x y` (the exact shift identity, `airy_shift`) and the paper-form
`ψ̃(q') = P(q') y(X(q')) + t Q(q') y'(X(q'))`, `X(q') = ζ(q')/t²`, `Q = h q₁`, `h = t³`, the row defect is **exactly**
`y(X) · 𝔄 + t y'(X) · 𝔅` with the two-link expressions of `DiscreteAirySecondPair`
(`airy2_identity`; the minus link is the plus link at `-t`, by the definitional parity of the scaled shift functions).
`airy2_defect_of_AB` turns `|𝔄|, |𝔅| ≤ K |h|³` into `|row defect| ≤ K' |h|³ w(X)` for every solution with the envelope bounds
`|y| ≤ C_y w`, `|y'| ≤ C_{y'} √(2+|x|) w` (`t √(2+|z₀/t²|) ≤ √(2+Z₀)`).  **Claim class: proved.**
-/

@[expose] public section

open Set

namespace FormalResearch.Special

open SturmAiry

/-- **The exact two-link identity.** -/
theorem airy2_identity {y y' : ℝ → ℝ} (hy : IsAirySol y y') (t z0 sp sm ap am Pp Pm P0 qp qm q0 c : ℝ) (ht : t ≠ 0) :
    ap * (Pp * y (z0 / t ^ 2 + t * sp) + t * (t ^ 3 * qp) * y' (z0 / t ^ 2 + t * sp)) +
      am * (Pm * y (z0 / t ^ 2 + t * sm) + t * (t ^ 3 * qm) * y' (z0 / t ^ 2 + t * sm)) -
      c * (P0 * y (z0 / t ^ 2) + t * (t ^ 3 * q0) * y' (z0 / t ^ 2)) =
    y (z0 / t ^ 2) *
        ((ap * Pp * apuCs z0 t sp + t ^ 3 * (ap * qp) * apuCs1 z0 t sp) +
          (am * Pm * apuCs z0 (-t) (-sm) + (-t ^ 3) * (am * qm) * apuCs1 z0 (-t) (-sm)) - c * P0) +
      t * y' (z0 / t ^ 2) *
        ((ap * Pp * apuSs z0 t sp + t ^ 3 * (ap * qp) * apuSs1 z0 t sp) -
          (am * Pm * apuSs z0 (-t) (-sm) + (-t ^ 3) * (am * qm) * apuSs1 z0 (-t) (-sm)) - c * (t ^ 3 * q0)) := by
  have hs1 := airy_shift hy (z0 / t ^ 2) (t * sp)
  have hs2 := airy_shift hy (z0 / t ^ 2) (t * sm)
  rw [hs1.1, hs1.2, hs2.1, hs2.2]
  have e2 : (-t) ^ 2 = t ^ 2 := by ring
  have e3 : (-t) * (-sm) = t * sm := by ring
  simp only [apuCs, apuCs1, apuSs, apuSs1, e2, e3]
  field_simp
  ring

/-- `t √(2 + |z₀/t²|) ≤ √(2+Z₀)` for a signed `t` with `0 < |t| ≤ 1`. -/
lemma apu2_t_sqrt {t z0 Z0 : ℝ} (ht0 : t ≠ 0) (ht1 : |t| ≤ 1) (hz0 : |z0| ≤ Z0) :
    |t| * √(2 + |z0 / t ^ 2|) ≤ √(2 + Z0) := by
  have h := apu_t_sqrt (abs_pos.2 ht0) ht1 hz0
  have e : z0 / |t| ^ 2 = z0 / t ^ 2 := by rw [sq_abs]
  rwa [e] at h

/-- **From `|𝔄|, |𝔅| ≤ K |h|³` to the row defect with the Airy envelope.** -/
theorem airy2_defect_of_AB {y y' w : ℝ → ℝ} (Cy Cy' : ℝ) (hCy : 0 ≤ Cy) (hCy' : 0 ≤ Cy')
    (hyb : ∀ x, |y x| ≤ Cy * w x) (hyb' : ∀ x, |y' x| ≤ Cy' * √(2 + |x|) * w x) (hw0 : ∀ x, 0 ≤ w x)
    {t z0 Z0 KA KB AA BB : ℝ} (ht0 : t ≠ 0) (ht1 : |t| ≤ 1) (hz0 : |z0| ≤ Z0)
    (hA : |AA| ≤ KA * |t ^ 3| ^ 3) (hB : |BB| ≤ KB * |t ^ 3| ^ 3) :
    |y (z0 / t ^ 2) * AA + t * y' (z0 / t ^ 2) * BB| ≤
      (Cy * KA + Cy' * √(2 + Z0) * KB) * |t ^ 3| ^ 3 * w (z0 / t ^ 2) := by
  have hts := apu2_t_sqrt ht0 ht1 hz0
  have hw := hw0 (z0 / t ^ 2)
  have h3 : 0 ≤ |t ^ 3| ^ 3 := by positivity
  have e1 : |y (z0 / t ^ 2) * AA| ≤ Cy * KA * |t ^ 3| ^ 3 * w (z0 / t ^ 2) := by
    rw [abs_mul]
    calc |y (z0 / t ^ 2)| * |AA| ≤ (Cy * w (z0 / t ^ 2)) * (KA * |t ^ 3| ^ 3) :=
          mul_le_mul (hyb _) hA (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have e2 : |t * y' (z0 / t ^ 2) * BB| ≤ Cy' * √(2 + Z0) * KB * |t ^ 3| ^ 3 * w (z0 / t ^ 2) := by
    rw [abs_mul, abs_mul]
    have h1 : |t| * |y' (z0 / t ^ 2)| ≤ Cy' * √(2 + Z0) * w (z0 / t ^ 2) := by
      calc |t| * |y' (z0 / t ^ 2)| ≤ |t| * (Cy' * √(2 + |z0 / t ^ 2|) * w (z0 / t ^ 2)) :=
            mul_le_mul_of_nonneg_left (hyb' _) (abs_nonneg _)
        _ = Cy' * (|t| * √(2 + |z0 / t ^ 2|)) * w (z0 / t ^ 2) := by ring
        _ ≤ Cy' * √(2 + Z0) * w (z0 / t ^ 2) := by gcongr
    calc |t| * |y' (z0 / t ^ 2)| * |BB| ≤ (Cy' * √(2 + Z0) * w (z0 / t ^ 2)) * (KB * |t ^ 3| ^ 3) :=
          mul_le_mul h1 hB (abs_nonneg _) (by positivity)
      _ = _ := by ring
  calc |y (z0 / t ^ 2) * AA + t * y' (z0 / t ^ 2) * BB| ≤ _ := abs_add_le _ _
    _ ≤ _ := by nlinarith [e1, e2]

/-- info: 'FormalResearch.Special.airy2_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy2_identity

/-- info: 'FormalResearch.Special.airy2_defect_of_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy2_defect_of_AB

end FormalResearch.Special
