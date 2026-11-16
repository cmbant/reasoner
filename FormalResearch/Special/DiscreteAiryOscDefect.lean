module

public import FormalResearch.Special.AiryParametrixUniformLattice
public import FormalResearch.Special.AiryParametrixLanger

/-!
# The uniform parametrix defect for an arbitrary solution of the Airy equation

`AiryParametrixUniformDefect` proves `|A(q+h/2)ψ(q+h) + A(q-h/2)ψ(q-h) - 2A Ch(ζζ'²) ψ(q)| ≤ K h² airyWt(X)` for
`ψ = g · Ai(h^{-2/3} ζ)`.  The proof uses `Ai` only through (i) the exact shift identity
`y(X+s) = y(X) C(X,s) + y'(X) S(X,s)`, valid for **every** solution `y'' = x y` (`AiryShift.airy_shift`), and (ii) the
envelope bounds `|y| ≤ C_y w`, `|y'| ≤ C_{y'} √(2+|x|) w`.  This module re-runs that proof (`apu_PA`, `apu_PB`, the parity
skeleton and the transport identity are reused unchanged) for an arbitrary real solution `(y, y')` and envelope `w`:

* `dao_pointwise`: the pointwise estimate with `K = C_y K_A + C_{y'} √(2+Z₀) K_B`;
* `dao_defect_core`, `dao_defect`: the `h²`-defect for `ψ = g · y(h^{-2/3} ζ)` at every `q ∈ J`, `|ζ| ≤ ...`, all `X`;
* `dao_defect_lattice`: the lattice form `|jac a c ψ k| ≤ K h² w(X_k)`.

The instance for `y = Bi` (and `w = airyBiWt`) is in `DiscreteAiryOscBi`.  **Claim class: proved**; constants existential.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

open SturmAiry

/-- **Uniform pointwise defect estimate** (the Airy-level statement for real data at one lattice point):
`|G₊ Ai(X+Δ₊) + G₋ Ai(X+Δ₋) - 2 G₀ Ch(F) Ai(X)| ≤ K h² airyWt(X)` with *no* factor `(1+|X|)³`,
`h = t³`, `X = z0/t²`, `Δ± = t s±`, `s± = ±z1 + h z2/2 + e±`, `G± = G₀ ± h G₁ + γ±`, `F = z0 z1²`, given the
transport identity `hTR`.  Replaces `apx_pointwise`. -/
theorem dao_pointwise {y y' w : ℝ → ℝ} (hy : IsAirySol y y') (Cy Cy' : ℝ) (hCy : 0 ≤ Cy)
    (hCy' : 0 ≤ Cy') (hw0 : ∀ x, 0 ≤ w x) (hyb : ∀ x, |y x| ≤ Cy * w x)
    (hyb' : ∀ x, |y' x| ≤ Cy' * √(2 + |x|) * w x) (Z0 S B Ee Γ : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) (hB : 0 ≤ B) (hEe : 0 ≤ Ee)
    (hΓ : 0 ≤ Γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t z0 z1 z2 G0 G1 ep em gp gm : ℝ), 0 < t → t ≤ 1 →
      |z0| ≤ Z0 → |z1| ≤ S → |z2| ≤ B → |G0| ≤ B → |G1| ≤ B →
      |ep| ≤ Ee * (t ^ 3) ^ 2 → |em| ≤ Ee * (t ^ 3) ^ 2 →
      |gp| ≤ Γ * (t ^ 3) ^ 2 → |gm| ≤ Γ * (t ^ 3) ^ 2 →
      |z1 + t ^ 3 * z2 / 2 + ep| ≤ S → |-z1 + t ^ 3 * z2 / 2 + em| ≤ S →
      2 * G1 * z1 * (2 * deriv langerCosh (z0 * z1 ^ 2)) +
        G0 * z2 * (2 * deriv langerCosh (z0 * z1 ^ 2) +
          2 * (z0 * z1 ^ 2) * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2))) +
        G0 * z1 ^ 4 * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2)) = 0 →
      |(G0 + t ^ 3 * G1 + gp) * y (z0 / t ^ 2 + t * (z1 + t ^ 3 * z2 / 2 + ep)) +
        (G0 - t ^ 3 * G1 + gm) * y (z0 / t ^ 2 + t * (-z1 + t ^ 3 * z2 / 2 + em)) -
        2 * G0 * langerCosh (z0 * z1 ^ 2) * y (z0 / t ^ 2)| ≤
        K * (t ^ 3) ^ 2 * w (z0 / t ^ 2) := by
  obtain ⟨KA, hKA0, hA⟩ := apu_PA Z0 S B Ee Γ hZ0 hS hB hEe hΓ
  obtain ⟨KB, hKB0, hB'⟩ := apu_PB Z0 S B Ee Γ hZ0 hS hB hEe hΓ
  refine ⟨Cy * KA + Cy' * √(2 + Z0) * KB, by positivity, ?_⟩
  intro t z0 z1 z2 G0 G1 ep em gp gm ht0 ht1 hz0 hz1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hTR
  have hAA := hA t z0 z1 z2 G0 G1 ep em gp gm ht0 ht1 hz0 hz1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm
  have hBB := hB' t z0 z1 z2 G0 G1 ep em gp gm ht0 ht1 hz0 hz1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hTR
  have hsplit : ∀ (X Dp Dm Gp Gm c : ℝ), Gp * y (X + Dp) + Gm * y (X + Dm) - c * y X =
      y X * (Gp * airyShiftC X Dp + Gm * airyShiftC X Dm - c) +
        y' X * (Gp * airyShiftS X Dp + Gm * airyShiftS X Dm) := by
    intro X Dp Dm Gp Gm c
    rw [(airy_shift hy X Dp).1, (airy_shift hy X Dm).1]; ring
  rw [hsplit]
  set X : ℝ := z0 / t ^ 2 with hX
  have hAi := hyb X
  have hAi' := hyb' X
  have hw := hw0 X
  have hts := apu_t_sqrt ht0 ht1 hz0
  rw [← hX] at hts
  have hh2 : 0 ≤ (t ^ 3) ^ 2 := by positivity
  set Ap : ℝ := (G0 + t ^ 3 * G1 + gp) * airyShiftC X (t * (z1 + t ^ 3 * z2 / 2 + ep)) +
        (G0 - t ^ 3 * G1 + gm) * airyShiftC X (t * (-z1 + t ^ 3 * z2 / 2 + em)) -
        2 * G0 * langerCosh (z0 * z1 ^ 2) with hApdef
  set Bp : ℝ := (G0 + t ^ 3 * G1 + gp) * airyShiftS X (t * (z1 + t ^ 3 * z2 / 2 + ep)) +
        (G0 - t ^ 3 * G1 + gm) * airyShiftS X (t * (-z1 + t ^ 3 * z2 / 2 + em)) with hBpdef
  have e1 : |y X * Ap| ≤ Cy * KA * (t ^ 3) ^ 2 * w X := by
    rw [abs_mul]
    calc |y X| * |Ap| ≤ (Cy * w X) * (KA * (t ^ 3) ^ 2) :=
          mul_le_mul hAi hAA (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have e2 : |y' X * Bp| ≤ Cy' * √(2 + Z0) * KB * (t ^ 3) ^ 2 * w X := by
    rw [abs_mul]
    have h1 : |y' X| * t ≤ Cy' * √(2 + Z0) * w X := by
      calc |y' X| * t ≤ (Cy' * √(2 + |X|) * w X) * t :=
            mul_le_mul_of_nonneg_right hAi' ht0.le
        _ = Cy' * (t * √(2 + |X|)) * w X := by ring
        _ ≤ Cy' * √(2 + Z0) * w X := by gcongr
    calc |y' X| * |Bp| ≤ |y' X| * (KB * t * (t ^ 3) ^ 2) :=
          mul_le_mul_of_nonneg_left hBB (abs_nonneg _)
      _ = (|y' X| * t) * (KB * (t ^ 3) ^ 2) := by ring
      _ ≤ (Cy' * √(2 + Z0) * w X) * (KB * (t ^ 3) ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring
  calc |y X * Ap + y' X * Bp| ≤ |y X * Ap| + |y' X * Bp| := abs_add_le _ _
    _ ≤ _ := by nlinarith [e1, e2]


/-- **Real-variable core of the defect lemma.**  All the Taylor data enter as hypotheses on reals. -/
theorem dao_defect_core {y y' w : ℝ → ℝ} (hy : IsAirySol y y') (Cy Cy' : ℝ) (hCy : 0 ≤ Cy)
    (hCy' : 0 ≤ Cy') (hw0 : ∀ x, 0 ≤ w x) (hyb : ∀ x, |y x| ≤ Cy * w x)
    (hyb' : ∀ x, |y' x| ≤ Cy' * √(2 + |x|) * w x) (Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 : ℝ) (hZ0 : 0 ≤ Z0) (hZ1 : 0 ≤ Z1)
    (hZ2 : 0 ≤ Z2) (hZ3 : 0 ≤ Z3) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hg0 : 0 ≤ g0)
    (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t zp zm Ap Am gP gM z0 z1 z2 a a1 b b1 : ℝ), 0 < t → t ≤ 1 →
      |z0| ≤ Z0 → |z1| ≤ Z1 → |z2| ≤ Z2 → |a| ≤ A0 → |a1| ≤ A1 → |b| ≤ g0 → |b1| ≤ g1 →
      |zp - (z0 + z1 * t ^ 3 + z2 * (t ^ 3) ^ 2 / 2)| ≤ Z3 * (t ^ 3) ^ 3 →
      |zm - (z0 + z1 * -t ^ 3 + z2 * (-t ^ 3) ^ 2 / 2)| ≤ Z3 * (t ^ 3) ^ 3 →
      |Ap - (a + a1 * (t ^ 3 / 2))| ≤ A2 * (t ^ 3 / 2) ^ 2 →
      |Am - (a + a1 * -(t ^ 3 / 2))| ≤ A2 * (t ^ 3 / 2) ^ 2 →
      |gP - (b + b1 * t ^ 3)| ≤ g2 * (t ^ 3) ^ 2 →
      |gM - (b + b1 * -t ^ 3)| ≤ g2 * (t ^ 3) ^ 2 →
      2 * (a1 * b / 2 + a * b1) * z1 * (2 * deriv langerCosh (z0 * z1 ^ 2)) +
        (a * b) * z2 * (2 * deriv langerCosh (z0 * z1 ^ 2) +
          2 * (z0 * z1 ^ 2) * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2))) +
        (a * b) * z1 ^ 4 * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2)) = 0 →
      |Ap * (gP * y (zp / t ^ 2)) + Am * (gM * y (zm / t ^ 2)) -
          2 * a * langerCosh (z0 * z1 ^ 2) * (b * y (z0 / t ^ 2))| ≤
        K * (t ^ 3) ^ 2 * w (z0 / t ^ 2) := by
  set S : ℝ := Z1 + Z2 / 2 + Z3 with hS
  have hS0 : 0 ≤ S := by positivity
  set B : ℝ := Z2 + A0 * g0 + (A1 * g0 / 2 + A0 * g1) with hB
  have hB0 : 0 ≤ B := by positivity
  set Γ : ℝ := A1 * g1 / 2 + (A0 + A1) * g2 + (A2 / 4) * (g0 + g1 + g2) with hΓ
  have hΓ0 : 0 ≤ Γ := by positivity
  obtain ⟨K, hK0, hpt⟩ := dao_pointwise hy Cy Cy' hCy hCy' hw0 hyb hyb' Z0 S B Z3 Γ hZ0 hS0 hB0 hZ3 hΓ0
  refine ⟨K, hK0, ?_⟩
  intro t zp zm Ap Am gP gM z0 z1 z2 a a1 b b1 ht0 ht1 hz0 hz1 hz2 ha ha1 hb hb1 hzp hzm hAp hAm
    hgp hgm hTR
  have hh0 : 0 < t ^ 3 := by positivity
  have hh1 : t ^ 3 ≤ 1 := pow_le_one₀ ht0.le ht1
  -- the increments of `ζ`
  have hep_b : |(zp - z0) / t ^ 3 - (z1 + t ^ 3 * z2 / 2)| ≤ Z3 * (t ^ 3) ^ 2 := by
    have e : (zp - z0) / t ^ 3 - (z1 + t ^ 3 * z2 / 2) =
        (zp - (z0 + z1 * t ^ 3 + z2 * (t ^ 3) ^ 2 / 2)) / t ^ 3 := by
      field_simp; ring
    rw [e]; exact apx_div_h hh0 hzp
  have hem_b : |(zm - z0) / t ^ 3 - (-z1 + t ^ 3 * z2 / 2)| ≤ Z3 * (t ^ 3) ^ 2 := by
    have e : (zm - z0) / t ^ 3 - (-z1 + t ^ 3 * z2 / 2) =
        (zm - (z0 + z1 * -t ^ 3 + z2 * (-t ^ 3) ^ 2 / 2)) / t ^ 3 := by
      field_simp; ring
    rw [e]; exact apx_div_h hh0 hzm
  -- the increments of `G`
  have hGp := apx_prod (a := a) (a1 := a1) (b := b) (b1 := b1)
    (ra := Ap - (a + a1 * (t ^ 3 / 2))) (rb := gP - (b + b1 * t ^ 3))
    (h := t ^ 3) (σ := 1) (A0 := A0) (A1 := A1) (ρA := A2 / 4) (g0 := g0) (g1 := g1) (ρg := g2)
    hh0 hh1 (Or.inl rfl) ha ha1 (by
      calc _ ≤ A2 * (t ^ 3 / 2) ^ 2 := hAp
        _ = A2 / 4 * (t ^ 3) ^ 2 := by ring) hb hb1 hgp
  have hGm := apx_prod (a := a) (a1 := a1) (b := b) (b1 := b1)
    (ra := Am - (a + a1 * -(t ^ 3 / 2))) (rb := gM - (b + b1 * -t ^ 3))
    (h := t ^ 3) (σ := -1) (A0 := A0) (A1 := A1) (ρA := A2 / 4) (g0 := g0) (g1 := g1) (ρg := g2)
    hh0 hh1 (Or.inr rfl) ha ha1 (by
      calc _ ≤ A2 * (t ^ 3 / 2) ^ 2 := hAm
        _ = A2 / 4 * (t ^ 3) ^ 2 := by ring) hb hb1 hgm
  have hgp_b : |Ap * gP - (a * b + t ^ 3 * (a1 * b / 2 + a * b1))| ≤ Γ * (t ^ 3) ^ 2 := by
    have e : Ap * gP - (a * b + t ^ 3 * (a1 * b / 2 + a * b1)) =
        (a + 1 * (t ^ 3 / 2) * a1 + (Ap - (a + a1 * (t ^ 3 / 2)))) *
          (b + 1 * t ^ 3 * b1 + (gP - (b + b1 * t ^ 3))) -
          (a * b + 1 * t ^ 3 * (a1 * b / 2 + a * b1)) := by ring
    rw [e]; exact hGp
  have hgm_b : |Am * gM - (a * b - t ^ 3 * (a1 * b / 2 + a * b1))| ≤ Γ * (t ^ 3) ^ 2 := by
    have e : Am * gM - (a * b - t ^ 3 * (a1 * b / 2 + a * b1)) =
        (a + -1 * (t ^ 3 / 2) * a1 + (Am - (a + a1 * -(t ^ 3 / 2)))) *
          (b + -1 * t ^ 3 * b1 + (gM - (b + b1 * -t ^ 3))) -
          (a * b + -1 * t ^ 3 * (a1 * b / 2 + a * b1)) := by ring
    rw [e]; exact hGm
  have hsp := apx_sp_bound (σ := 1) (by norm_num) hh0 hh1 hz1 hz2 hep_b hZ3
  have hsm := apx_sp_bound (σ := -1) (by norm_num) hh0 hh1 hz1 hz2 hem_b hZ3
  obtain ⟨hG0, hG1⟩ := apx_Gjet_bound ha ha1 hb hb1
  have hz1S : |z1| ≤ S := by rw [hS]; linarith
  have p1 : 0 ≤ A0 * g0 := mul_nonneg hA0 hg0
  have p2 : 0 ≤ A1 * g0 / 2 + A0 * g1 := by positivity
  have hz2B : |z2| ≤ B := by rw [hB]; linarith
  have hG0B : |a * b| ≤ B := by rw [hB]; linarith
  have hG1B : |a1 * b / 2 + a * b1| ≤ B := by rw [hB]; linarith
  have hmain := hpt t z0 z1 z2 (a * b) (a1 * b / 2 + a * b1) _ _ (Ap * gP - (a * b + t ^ 3 * (a1 * b / 2 + a * b1)))
    (Am * gM - (a * b - t ^ 3 * (a1 * b / 2 + a * b1))) ht0 ht1 hz0 hz1S hz2B hG0B hG1B hep_b hem_b
    hgp_b hgm_b (by simpa using hsp) (by simpa using hsm) hTR
  have e1 : a * b + t ^ 3 * (a1 * b / 2 + a * b1) +
      (Ap * gP - (a * b + t ^ 3 * (a1 * b / 2 + a * b1))) = Ap * gP := by ring
  have e2 : a * b - t ^ 3 * (a1 * b / 2 + a * b1) +
      (Am * gM - (a * b - t ^ 3 * (a1 * b / 2 + a * b1))) = Am * gM := by ring
  have e3 : z1 + t ^ 3 * z2 / 2 + ((zp - z0) / t ^ 3 - (z1 + t ^ 3 * z2 / 2)) = (zp - z0) / t ^ 3 := by ring
  have e4 : -z1 + t ^ 3 * z2 / 2 + ((zm - z0) / t ^ 3 - (-z1 + t ^ 3 * z2 / 2)) = (zm - z0) / t ^ 3 := by ring
  rw [e1, e2, e3, e4] at hmain
  have e5 : z0 / t ^ 2 + t * ((zp - z0) / t ^ 3) = zp / t ^ 2 := by field_simp; ring
  have e6 : z0 / t ^ 2 + t * ((zm - z0) / t ^ 3) = zm / t ^ 2 := by field_simp; ring
  rw [e5, e6] at hmain
  convert hmain using 2
  ring


/-- **The Airy parametrix defect lemma, uniform form.**  See the module docstring: no factor `(1+|X|)³`. -/
theorem dao_defect {y y' w : ℝ → ℝ} (hy : IsAirySol y y') (Cy Cy' : ℝ) (hCy : 0 ≤ Cy)
    (hCy' : 0 ≤ Cy') (hw0 : ∀ x, 0 ≤ w x) (hyb : ∀ x, |y x| ≤ Cy * w x)
    (hyb' : ∀ x, |y' x| ≤ Cy' * √(2 + |x|) * w x) {U J : Set ℝ} {ζ A g : ℝ → ℝ} (hU : IsOpen U)
    (hJ : IsCompact J) (hJU : J ⊆ U) (hζ : ContDiffOn ℝ 3 ζ U) (hA : ContDiffOn ℝ 2 A U)
    (hg : ContDiffOn ℝ 2 g U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) :
    ∃ K h0 : ℝ, 0 < K ∧ 0 < h0 ∧ ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ q ∈ J,
      |A (q + h / 2) * (g (q + h) * y (h ^ (-(2 / 3 : ℝ)) * ζ (q + h))) +
          A (q - h / 2) * (g (q - h) * y (h ^ (-(2 / 3 : ℝ)) * ζ (q - h))) -
          2 * A q * langerCosh (ζ q * deriv ζ q ^ 2) * (g q * y (h ^ (-(2 / 3 : ℝ)) * ζ q))| ≤
        K * h ^ 2 * w (h ^ (-(2 / 3 : ℝ)) * ζ q) := by
  obtain ⟨Z0, Z1, Z2, Z3, δζ, hZ0, hZ1, hZ2, hZ3, hδζ, hζj⟩ := apx_jet3 hU hζ hJ hJU
  obtain ⟨A0, A1, A2, δA, hA0, hA1, hA2, hδA, hAj⟩ := apx_jet2 hU hA hJ hJU
  obtain ⟨g0, g1, g2, δg, hg0, hg1, hg2, hδg, hgj⟩ := apx_jet2 hU hg hJ hJU
  obtain ⟨K, hK0, hcore⟩ := dao_defect_core hy Cy Cy' hCy hCy' hw0 hyb hyb' Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 hZ0 hZ1 hZ2 hZ3 hA0
    hA1 hA2 hg0 hg1 hg2
  refine ⟨K + 1, min (min δζ (min (2 * δA) δg)) 1, by linarith, ?_, ?_⟩
  · exact lt_min (lt_min hδζ (lt_min (by linarith) hδg)) one_pos
  intro h hh0 hh0' q hq
  have hhδζ : h ≤ δζ := hh0'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhδA : h / 2 ≤ δA := by
    have := hh0'.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hhδg : h ≤ δg := hh0'.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hh1 : h ≤ 1 := hh0'.trans (min_le_right _ _)
  obtain ⟨t, ht0, ht3, hpow⟩ := apx_rpow hh0
  subst ht3
  have ht1 : t ≤ 1 := by
    by_contra hlt
    have : 1 < t ^ 3 := one_lt_pow₀ (not_le.1 hlt) (by norm_num)
    linarith
  obtain ⟨hζ0, hζ1, hζ2, hζT⟩ := hζj q hq
  obtain ⟨hA0q, hA1q, hAT⟩ := hAj q hq
  obtain ⟨hg0q, hg1q, hgT⟩ := hgj q hq
  have hζp := hζT (t ^ 3) (by rw [abs_of_pos hh0]; exact hhδζ)
  have hζm := hζT (-(t ^ 3)) (by rw [abs_neg, abs_of_pos hh0]; exact hhδζ)
  rw [abs_of_pos hh0] at hζp
  rw [abs_neg, abs_of_pos hh0, ← sub_eq_add_neg] at hζm
  have hAp := hAT (t ^ 3 / 2) (by rw [abs_of_pos (by positivity)]; exact hhδA)
  have hAm := hAT (-(t ^ 3 / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; exact hhδA)
  have hgp := hgT (t ^ 3) (by rw [abs_of_pos hh0]; exact hhδg)
  have hgm := hgT (-(t ^ 3)) (by rw [abs_neg, abs_of_pos hh0]; exact hhδg)
  rw [neg_sq] at hAm hgm
  rw [← sub_eq_add_neg] at hgm hAm
  have hTR := apx_transport hU hζ hA hg hrel (hJU hq)
  have hmain := hcore t (ζ (q + t ^ 3)) (ζ (q - t ^ 3)) (A (q + t ^ 3 / 2)) (A (q - t ^ 3 / 2))
    (g (q + t ^ 3)) (g (q - t ^ 3)) (ζ q) (deriv ζ q) (deriv (deriv ζ) q) (A q) (deriv A q) (g q)
    (deriv g q) ht0 ht1 hζ0 hζ1 hζ2 hA0q hA1q hg0q hg1q hζp hζm hAp hAm hgp hgm hTR
  rw [hpow]
  simp only [inv_mul_eq_div]
  have hX : 0 ≤ (t ^ 3) ^ 2 * w (ζ q / t ^ 2) := by
    have := hw0 (ζ q / t ^ 2)
    positivity
  calc _ ≤ K * (t ^ 3) ^ 2 * w (ζ q / t ^ 2) := hmain
    _ ≤ _ := by nlinarith [hX]


/-- **Uniform defect on a lattice**: `|jac a c ψ k| ≤ K h² airyWt(X_k)`. -/
theorem dao_defect_lattice {y y' w : ℝ → ℝ} (hy : IsAirySol y y') (Cy Cy' : ℝ) (hCy : 0 ≤ Cy)
    (hCy' : 0 ≤ Cy') (hw0 : ∀ x, 0 ≤ w x) (hyb : ∀ x, |y x| ≤ Cy * w x)
    (hyb' : ∀ x, |y' x| ≤ Cy' * √(2 + |x|) * w x) {U J : Set ℝ} {ζ A g : ℝ → ℝ} (hU : IsOpen U)
    (hJ : IsCompact J) (hJU : J ⊆ U) (hζ : ContDiffOn ℝ 3 ζ U) (hA : ContDiffOn ℝ 2 A U)
    (hg : ContDiffOn ℝ 2 g U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) :
    ∃ K h0 : ℝ, 0 < K ∧ 0 < h0 ∧ ∀ (h q₀ : ℝ) (a c ψ : ℤ → ℝ), 0 < h → h ≤ h0 →
      (∀ k : ℤ, a k = A (q₀ + k * h - h / 2)) →
      (∀ k : ℤ, c k = 2 * A (q₀ + k * h) * langerCosh (ζ (q₀ + k * h) * deriv ζ (q₀ + k * h) ^ 2)) →
      (∀ k : ℤ, ψ k = g (q₀ + k * h) * y (h ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * h))) →
      ∀ k : ℤ, q₀ + k * h ∈ J →
        |FormalResearch.DiscreteAiry.jac a c ψ k| ≤
          K * h ^ 2 * w (h ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * h)) := by
  obtain ⟨K, h0, hK, hh0, H⟩ := dao_defect hy Cy Cy' hCy hCy' hw0 hyb hyb' hU hJ hJU hζ hA hg hrel
  refine ⟨K, h0, hK, hh0, fun h q₀ a c ψ hh hh' ha hc hψ k hk => ?_⟩
  have := H h hh hh' (q₀ + k * h) hk
  have q1 : q₀ + ((k + 1 : ℤ) : ℝ) * h = q₀ + k * h + h := by push_cast; ring
  have q2 : q₀ + ((k - 1 : ℤ) : ℝ) * h = q₀ + k * h - h := by push_cast; ring
  have e1 : a (k + 1) = A (q₀ + k * h + h / 2) := by
    rw [ha]; congr 1; push_cast; ring
  have e2 : a k = A (q₀ + k * h - h / 2) := ha k
  have e3 : ψ (k + 1) = g (q₀ + k * h + h) * y (h ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * h + h)) := by
    rw [hψ, q1]
  have e4 : ψ (k - 1) = g (q₀ + k * h - h) * y (h ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * h - h)) := by
    rw [hψ, q2]
  unfold FormalResearch.DiscreteAiry.jac
  rw [e1, e2, e3, e4, hc, hψ]
  convert this using 2


/-- info: 'FormalResearch.Special.dao_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_pointwise

/-- info: 'FormalResearch.Special.dao_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_defect

/-- info: 'FormalResearch.Special.dao_defect_lattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_defect_lattice

end FormalResearch.Special
