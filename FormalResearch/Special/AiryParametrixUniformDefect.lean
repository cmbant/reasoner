module

public import FormalResearch.Special.AiryParametrixUniformPointwise
public import FormalResearch.Special.AiryParametrixDefect

/-!
# The Airy parametrix defect lemma, uniform form (no factor `(1+|X|)³`)

**Setting** as in `AiryParametrixDefect`: `A, g ∈ C²(U)`, `ζ ∈ C³(U)`, `U ⊇ J` open / compact, and the
closed-form amplitude relation `g² A ζ' Sh(ζζ'²) = 1` on `U` (`Sh = 2 Ch'`); row operator
`(Lψ)(q) = A(q+h/2) ψ(q+h) + A(q-h/2) ψ(q-h) - 2A(q) Ch(ζζ'²)(q) ψ(q)`, `ψ = g · Ai(h^{-2/3} ζ)`.

**Main result** (`airyParametrix_defect_uniform`).  There are `K, h₀ > 0` such that for `h ∈ (0, h₀]`,
`q ∈ J`, `X = h^{-2/3} ζ(q)` (any real `X`, including `|X| ~ h^{-2/3}` and the oscillatory side `X ≪ -1`),
`|(Lψ)(q)| ≤ K h² airyWt(X)`.
This removes the factor `(1+|X|)³` of the window form `airyParametrix_defect` (which is useless where
`h²(1+|X|)³ = O(1)`, i.e. `X ~ h^{-2/3}`): the paper's `O(h²) ψ` claim holds on the whole turn
neighbourhood, with the *same* hypotheses.  Consequences: `airyParametrix_defect_uniform_lattice` (the
`jac` form for the M5/M6 consumers) and `airyParametrix_defect_uniform_rel` (the relative form
`|jac ψ_k| ≤ K' h² ψ_k` on `X_k ≥ -1`, using `Ai ≥ airyWt/20` there and `g² ≥ 1/sup|Aζ'Sh|`).

**Proof.**  The same algebra as the window form (exact shift identity `Ai(X+Δ) = Ai(X) C + Ai'(X) S`, parity
skeleton, transport identity) but the exact shift functions are expanded in `h` at fixed `ζ`
(`C(s;ζ,h) = E + hO + O(h²)`, `S(s;ζ,h) = A + hB + O(h²)`, `A:1068-1104`) with closed forms in
`Ch, Ch', Ch'', Ch'''` and a Grönwall remainder for `Y'' = (ζ + hs)Y` (`AiryParametrixUniformODE`).  All
remainders are uniform in `X` because `X` enters only through `ζ = h^{2/3} X` (bounded) and through
`Ai(X), Ai'(X)`, for which `|Ai| ≤ 25 airyWt`, `|Ai'| ≤ C √(2+|X|) airyWt` and `h^{1/3} √(2+|X|) ≤ √(2+Z₀)`
suffice.  The `h¹` coefficient of the `Ai'` part vanishes *exactly* by the transport identity (not just to
`O(F)`).

Numerics (`mpmath`, not committed): relative defect over `h² airyWt` stays below `0.023` up to `|X| ~ 5000`
(reviewer run) and below `0.004` on the model chain `ζ = q`, `A = 1`, `g = Sh(q)^{-1/2}` (`q ∈ ±[0.01, 1.9]`,
`h ∈ {1e-2, 1e-4, 1e-6, 1e-9}`, i.e. `|X|` up to `3·10⁵`); the remainder constants `|C - (E+hO)|/h²`, `|S/t - (A+hB)|/h²` are `1.7e-3 .. 7.1e-3` for
`ζ ∈ [-2, 2]`, `h ∈ [1e-6, 1e-2]` (`AiryParametrixUniformCh`).

Here `hrel` is a hypothesis; it holds for M3's `ζ, g` by `langer_hrel` (`AiryParametrixLanger`).  Not formalised: the
`h²` coefficient, explicit constants.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- **Real-variable core of the defect lemma.**  All the Taylor data enter as hypotheses on reals. -/
theorem apx_defect_core_uniform (Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 : ℝ) (hZ0 : 0 ≤ Z0) (hZ1 : 0 ≤ Z1)
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
      |Ap * (gP * airyAi (zp / t ^ 2)) + Am * (gM * airyAi (zm / t ^ 2)) -
          2 * a * langerCosh (z0 * z1 ^ 2) * (b * airyAi (z0 / t ^ 2))| ≤
        K * (t ^ 3) ^ 2 * airyWt (z0 / t ^ 2) := by
  set S : ℝ := Z1 + Z2 / 2 + Z3 with hS
  have hS0 : 0 ≤ S := by positivity
  set B : ℝ := Z2 + A0 * g0 + (A1 * g0 / 2 + A0 * g1) with hB
  have hB0 : 0 ≤ B := by positivity
  set Γ : ℝ := A1 * g1 / 2 + (A0 + A1) * g2 + (A2 / 4) * (g0 + g1 + g2) with hΓ
  have hΓ0 : 0 ≤ Γ := by positivity
  obtain ⟨K, hK0, hpt⟩ := apu_pointwise Z0 S B Z3 Γ hZ0 hS0 hB0 hZ3 hΓ0
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
theorem airyParametrix_defect_uniform {U J : Set ℝ} {ζ A g : ℝ → ℝ} (hU : IsOpen U)
    (hJ : IsCompact J) (hJU : J ⊆ U) (hζ : ContDiffOn ℝ 3 ζ U) (hA : ContDiffOn ℝ 2 A U)
    (hg : ContDiffOn ℝ 2 g U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) :
    ∃ K h0 : ℝ, 0 < K ∧ 0 < h0 ∧ ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ q ∈ J,
      |A (q + h / 2) * (g (q + h) * airyAi (h ^ (-(2 / 3 : ℝ)) * ζ (q + h))) +
          A (q - h / 2) * (g (q - h) * airyAi (h ^ (-(2 / 3 : ℝ)) * ζ (q - h))) -
          2 * A q * langerCosh (ζ q * deriv ζ q ^ 2) * (g q * airyAi (h ^ (-(2 / 3 : ℝ)) * ζ q))| ≤
        K * h ^ 2 * airyWt (h ^ (-(2 / 3 : ℝ)) * ζ q) := by
  obtain ⟨Z0, Z1, Z2, Z3, δζ, hZ0, hZ1, hZ2, hZ3, hδζ, hζj⟩ := apx_jet3 hU hζ hJ hJU
  obtain ⟨A0, A1, A2, δA, hA0, hA1, hA2, hδA, hAj⟩ := apx_jet2 hU hA hJ hJU
  obtain ⟨g0, g1, g2, δg, hg0, hg1, hg2, hδg, hgj⟩ := apx_jet2 hU hg hJ hJU
  obtain ⟨K, hK0, hcore⟩ := apx_defect_core_uniform Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 hZ0 hZ1 hZ2 hZ3 hA0
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
  have hX : 0 ≤ (t ^ 3) ^ 2 * airyWt (ζ q / t ^ 2) := by
    have := airyWt_pos (ζ q / t ^ 2)
    positivity
  calc _ ≤ K * (t ^ 3) ^ 2 * airyWt (ζ q / t ^ 2) := hmain
    _ ≤ _ := by nlinarith [hX]

/-- info: 'FormalResearch.Special.airyParametrix_defect_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyParametrix_defect_uniform

/-- info: 'FormalResearch.Special.apx_defect_core_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apx_defect_core_uniform

end FormalResearch.Special
