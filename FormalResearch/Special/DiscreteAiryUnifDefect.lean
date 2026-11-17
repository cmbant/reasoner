module

public import FormalResearch.Special.DiscreteAiryLimitDefect
public import FormalResearch.Special.DiscreteAiryOscBi

/-!
# Uniform discrete-to-Airy, step 1: the parametrix defect with constants depending only on jet bounds

The defect lemmas `airyParametrix_defect_uniform_lattice` and `dao_bi_defect_lattice` (and their wrappers `dal_exact_defect`,
`dao_exact_defect_bi`) produce `K, h₀` by *compactness* of `J ⊂ U` for the one given triple `(ζ, A, g)`: `∃ K h₀` stands **after** the
data.  Their real-variable cores `apx_defect_core_uniform`, `dao_defect_core` already have the quantifier order
`∀ (jet bounds) ∃ K ∀ (data)`.  This module re-runs the wrappers in that order:

* `DunJets ζ A g J Z₀ … δ`: the jet hypotheses of the cores on the set `J` (values, first and second derivatives, third-order Taylor
  remainder of `ζ`, second-order Taylor remainders of `A, g`, for increments `|s| ≤ δ`);
* `dun_defect_gen`: for **fixed reals** `Z₀ … g₂, δ` there are `K, h₀ > 0` such that for **every** `(U, J, ζ, A, g)` with the amplitude
  relation and `DunJets` the pointwise parametrix defect `|A(q+h/2)ψ(q+h) + A(q-h/2)ψ(q-h) - 2A Ch(ζζ'²) ψ(q)| ≤ K h² w(X)` holds
  (`y` any Airy solution with an envelope `w`);
* `dun_exact_defect`: the lattice form for the *exact* coefficients `a⁰_k = A(q_k - h/2)`, `c⁰_k = 2A(q_k)u(q_k)` (eikonal relation
  `Ch(ζζ'²) = u`) for both `Ai` (`airyWt`) and `Bi` (`airyBiWt`): `∃ K_A K_B δ₁` before the data.

**Claim class: proved.**  No new analysis: the proofs are those of `airyParametrix_defect_uniform`, `dao_defect`,
`dal_exact_defect`, `dao_exact_defect_bi` with the `apx_jet2/apx_jet3` compactness steps replaced by hypotheses.
-/

@[expose] public section

open Set FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- Jet bounds of `ζ, A, g` on `J`: `|ζ| ≤ Z₀`, `|ζ'| ≤ Z₁`, `|ζ''| ≤ Z₂`, `|ζ(q+s) - ζ - ζ's - ζ''s²/2| ≤ Z₃|s|³` for `|s| ≤ δ`;
`|A| ≤ A₀`, `|A'| ≤ A₁`, `|A(q+s) - A - A's| ≤ A₂ s²`; same for `g` with `g₀, g₁, g₂`. -/
structure DunJets (ζ A g : ℝ → ℝ) (J : Set ℝ) (Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 δ : ℝ) : Prop where
  z0 : ∀ q ∈ J, |ζ q| ≤ Z0
  z1 : ∀ q ∈ J, |deriv ζ q| ≤ Z1
  z2 : ∀ q ∈ J, |deriv (deriv ζ) q| ≤ Z2
  zT : ∀ q ∈ J, ∀ s : ℝ, |s| ≤ δ →
    |ζ (q + s) - (ζ q + deriv ζ q * s + deriv (deriv ζ) q * s ^ 2 / 2)| ≤ Z3 * |s| ^ 3
  a0 : ∀ q ∈ J, |A q| ≤ A0
  a1 : ∀ q ∈ J, |deriv A q| ≤ A1
  aT : ∀ q ∈ J, ∀ s : ℝ, |s| ≤ δ → |A (q + s) - (A q + deriv A q * s)| ≤ A2 * s ^ 2
  g0 : ∀ q ∈ J, |g q| ≤ g0
  g1 : ∀ q ∈ J, |deriv g q| ≤ g1
  gT : ∀ q ∈ J, ∀ s : ℝ, |s| ≤ δ → |g (q + s) - (g q + deriv g q * s)| ≤ g2 * s ^ 2

/-- **The pointwise parametrix defect with constants depending only on jet bounds** (generic Airy solution `y` with envelope `w`;
the cores `dao_defect_core` with the compactness steps of `dao_defect` replaced by `DunJets`). -/
theorem dun_defect_gen {y y' w : ℝ → ℝ} (hy : IsAirySol y y') (Cy Cy' : ℝ) (hCy : 0 ≤ Cy)
    (hCy' : 0 ≤ Cy') (hw0 : ∀ x, 0 ≤ w x) (hyb : ∀ x, |y x| ≤ Cy * w x)
    (hyb' : ∀ x, |y' x| ≤ Cy' * √(2 + |x|) * w x) (Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 δJ : ℝ) (hZ0 : 0 ≤ Z0)
    (hZ1 : 0 ≤ Z1) (hZ2 : 0 ≤ Z2) (hZ3 : 0 ≤ Z3) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) (hδJ : 0 < δJ) :
    ∃ K h0 : ℝ, 0 < K ∧ 0 < h0 ∧ ∀ {U J : Set ℝ} {ζ A g : ℝ → ℝ}, IsOpen U → J ⊆ U →
      ContDiffOn ℝ 3 ζ U → ContDiffOn ℝ 2 A U → ContDiffOn ℝ 2 g U →
      (∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) →
      DunJets ζ A g J Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 δJ →
      ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ q ∈ J,
      |A (q + h / 2) * (g (q + h) * y (h ^ (-(2 / 3 : ℝ)) * ζ (q + h))) +
          A (q - h / 2) * (g (q - h) * y (h ^ (-(2 / 3 : ℝ)) * ζ (q - h))) -
          2 * A q * langerCosh (ζ q * deriv ζ q ^ 2) * (g q * y (h ^ (-(2 / 3 : ℝ)) * ζ q))| ≤
        K * h ^ 2 * w (h ^ (-(2 / 3 : ℝ)) * ζ q) := by
  obtain ⟨K, hK0, hcore⟩ := dao_defect_core hy Cy Cy' hCy hCy' hw0 hyb hyb' Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2
    hZ0 hZ1 hZ2 hZ3 hA0 hA1 hA2 hg0 hg1 hg2
  refine ⟨K + 1, min δJ 1, by linarith, lt_min hδJ one_pos, ?_⟩
  intro U J ζ A g hU hJU hζ hA hg hrel hjets h hh0 hh0' q hq
  have hhδ : h ≤ δJ := hh0'.trans (min_le_left _ _)
  have hh1 : h ≤ 1 := hh0'.trans (min_le_right _ _)
  obtain ⟨t, ht0, ht3, hpow⟩ := apx_rpow hh0
  subst ht3
  have ht1 : t ≤ 1 := by
    by_contra hlt
    have : 1 < t ^ 3 := one_lt_pow₀ (not_le.1 hlt) (by norm_num)
    linarith
  have hζ0 := hjets.z0 q hq
  have hζ1 := hjets.z1 q hq
  have hζ2 := hjets.z2 q hq
  have hA0q := hjets.a0 q hq
  have hA1q := hjets.a1 q hq
  have hg0q := hjets.g0 q hq
  have hg1q := hjets.g1 q hq
  have hζp := hjets.zT q hq (t ^ 3) (by rw [abs_of_pos hh0]; exact hhδ)
  have hζm := hjets.zT q hq (-(t ^ 3)) (by rw [abs_neg, abs_of_pos hh0]; exact hhδ)
  rw [abs_of_pos hh0] at hζp
  rw [abs_neg, abs_of_pos hh0, ← sub_eq_add_neg] at hζm
  have hAp := hjets.aT q hq (t ^ 3 / 2) (by rw [abs_of_pos (by positivity)]; linarith)
  have hAm := hjets.aT q hq (-(t ^ 3 / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
  have hgp := hjets.gT q hq (t ^ 3) (by rw [abs_of_pos hh0]; exact hhδ)
  have hgm := hjets.gT q hq (-(t ^ 3)) (by rw [abs_neg, abs_of_pos hh0]; exact hhδ)
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

/-- **Exact-coefficient lattice defect for a generic Airy solution, constants depending only on jet bounds.**
For `a⁰_k = A(q_k - δ³/2)`, `c⁰_k = 2A(q_k)u(q_k)`, `ψ_k = g(q_k) y(X_k)`: `|jac a⁰ c⁰ ψ k| ≤ K δ⁶ w(X_k)` for `q_k ∈ [c₀ - r, c₀ + r]`. -/
theorem dun_exact_defect_gen {y y' w : ℝ → ℝ} (hy : IsAirySol y y') (Cy Cy' : ℝ) (hCy : 0 ≤ Cy)
    (hCy' : 0 ≤ Cy') (hw0 : ∀ x, 0 ≤ w x) (hyb : ∀ x, |y x| ≤ Cy * w x)
    (hyb' : ∀ x, |y' x| ≤ Cy' * √(2 + |x|) * w x) (Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 δJ : ℝ) (hZ0 : 0 ≤ Z0)
    (hZ1 : 0 ≤ Z1) (hZ2 : 0 ≤ Z2) (hZ3 : 0 ≤ Z3) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) (hδJ : 0 < δJ) :
    ∃ K δ1 : ℝ, 0 < K ∧ 0 < δ1 ∧ δ1 ≤ 1 ∧ ∀ {U : Set ℝ} {ζ A g u : ℝ → ℝ} {c0 r : ℝ}, IsOpen U →
      Icc (c0 - r) (c0 + r) ⊆ U → ContDiffOn ℝ 3 ζ U → ContDiffOn ℝ 2 A U → ContDiffOn ℝ 2 g U →
      (∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) →
      (∀ q ∈ U, langerCosh (ζ q * deriv ζ q ^ 2) = u q) →
      DunJets ζ A g (Icc (c0 - r) (c0 + r)) Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 δJ →
      ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ1 → ∀ k : ℤ, dalQ q₀ δ k ∈ Icc (c0 - r) (c0 + r) →
        |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
            (fun j => g (dalQ q₀ δ j) * y (dalX ζ q₀ δ j)) k| ≤ K * δ ^ 6 * w (dalX ζ q₀ δ k) := by
  obtain ⟨K, h0, hK, hh0, H⟩ := dun_defect_gen hy Cy Cy' hCy hCy' hw0 hyb hyb' Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 δJ
    hZ0 hZ1 hZ2 hZ3 hA0 hA1 hA2 hg0 hg1 hg2 hδJ
  refine ⟨K, min 1 h0, hK, lt_min one_pos hh0, min_le_left _ _, ?_⟩
  intro U ζ A g u c0 r hU hsub hζ hA hg hrel heik hjets δ q₀ hδ hδ1 k hk
  have hδ1' : δ ≤ 1 := hδ1.trans (min_le_left _ _)
  have h3 : 0 < δ ^ 3 := by positivity
  have h3δ : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2, pow_pos hδ 3]
  have hh0δ : δ ^ 3 ≤ h0 := h3δ.trans (hδ1.trans (min_le_right _ _))
  have hkU : q₀ + (k : ℝ) * δ ^ 3 ∈ U := hsub hk
  have hmain := H hU hsub hζ hA hg hrel hjets (δ ^ 3) h3 hh0δ (q₀ + (k : ℝ) * δ ^ 3) hk
  have q1 : q₀ + ((k + 1 : ℤ) : ℝ) * δ ^ 3 = q₀ + k * δ ^ 3 + δ ^ 3 := by push_cast; ring
  have q2 : q₀ + ((k - 1 : ℤ) : ℝ) * δ ^ 3 = q₀ + k * δ ^ 3 - δ ^ 3 := by push_cast; ring
  have e1 : A (q₀ + k * δ ^ 3 + δ ^ 3 - δ ^ 3 / 2) = A (q₀ + k * δ ^ 3 + δ ^ 3 / 2) := by
    congr 1; ring
  have e6 : (δ ^ 3) ^ 2 = δ ^ 6 := by ring
  have hj : jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
      (fun j => g (dalQ q₀ δ j) * y (dalX ζ q₀ δ j)) k =
      A (q₀ + k * δ ^ 3 + δ ^ 3 / 2) * (g (q₀ + k * δ ^ 3 + δ ^ 3) *
          y ((δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * δ ^ 3 + δ ^ 3))) +
        A (q₀ + k * δ ^ 3 - δ ^ 3 / 2) * (g (q₀ + k * δ ^ 3 - δ ^ 3) *
          y ((δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * δ ^ 3 - δ ^ 3))) -
        2 * A (q₀ + k * δ ^ 3) * langerCosh (ζ (q₀ + k * δ ^ 3) * deriv ζ (q₀ + k * δ ^ 3) ^ 2) *
          (g (q₀ + k * δ ^ 3) * y ((δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * δ ^ 3))) := by
    unfold jac
    simp only [dalQ, dalX]
    rw [q1, q2, e1, heik _ hkU]
  rw [hj]
  have := hmain
  rw [e6] at this
  exact this

/-- **Exact-coefficient defect for `Ai` and `Bi`, constants depending only on jet bounds.**  `ψ_k = g(q_k) Ai(X_k)` (`dalPsi`) with
weight `airyWt`, `ψ^B_k = g(q_k) Bi(X_k)` with weight `airyBiWt`, common constant `K` and `δ₁`. -/
theorem dun_exact_defect (Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 δJ : ℝ) (hZ0 : 0 ≤ Z0)
    (hZ1 : 0 ≤ Z1) (hZ2 : 0 ≤ Z2) (hZ3 : 0 ≤ Z3) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) (hδJ : 0 < δJ) :
    ∃ K δ1 : ℝ, 0 < K ∧ 0 < δ1 ∧ δ1 ≤ 1 ∧ ∀ {U : Set ℝ} {ζ A g u : ℝ → ℝ} {c0 r : ℝ}, IsOpen U →
      Icc (c0 - r) (c0 + r) ⊆ U → ContDiffOn ℝ 3 ζ U → ContDiffOn ℝ 2 A U → ContDiffOn ℝ 2 g U →
      (∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) →
      (∀ q ∈ U, langerCosh (ζ q * deriv ζ q ^ 2) = u q) →
      DunJets ζ A g (Icc (c0 - r) (c0 + r)) Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 δJ →
      ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ1 → ∀ k : ℤ, dalQ q₀ δ k ∈ Icc (c0 - r) (c0 + r) →
        |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
            (dalPsi g ζ q₀ δ) k| ≤ K * δ ^ 6 * airyWt (dalX ζ q₀ δ k) ∧
        |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
            (fun j => g (dalQ q₀ δ j) * airyBi (dalX ζ q₀ δ j)) k| ≤ K * δ ^ 6 * airyBiWt (dalX ζ q₀ δ k) := by
  obtain ⟨KA, δA, hKA, hδA, hδA1, HA⟩ := dun_exact_defect_gen isAirySol_airyAi 25 132500 (by norm_num)
    (by norm_num) (fun x => (airyWt_pos x).le) (fun x => (apx_airy_global x).1)
    (fun x => (apx_airy_global x).2) Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 δJ hZ0 hZ1 hZ2 hZ3 hA0 hA1 hA2 hg0 hg1 hg2 hδJ
  obtain ⟨KB, δB, hKB, hδB, hδB1, HB⟩ := dun_exact_defect_gen isAirySol_airyBi_shift 450 2385000 (by norm_num)
    (by norm_num) (fun x => (airyBiWt_pos x).le) (fun x => (apx_airyBi_global x).1)
    (fun x => (apx_airyBi_global x).2) Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 δJ hZ0 hZ1 hZ2 hZ3 hA0 hA1 hA2 hg0 hg1 hg2 hδJ
  refine ⟨max KA KB, min δA δB, lt_max_of_lt_left hKA, lt_min hδA hδB, (min_le_left _ _).trans hδA1, ?_⟩
  intro U ζ A g u c0 r hU hsub hζ hA hg hrel heik hjets δ q₀ hδ hδδ k hk
  have h1 : δ ≤ δA := hδδ.trans (min_le_left _ _)
  have h2 : δ ≤ δB := hδδ.trans (min_le_right _ _)
  have hw : 0 ≤ δ ^ 6 := by positivity
  refine ⟨?_, ?_⟩
  · refine (HA hU hsub hζ hA hg hrel heik hjets δ q₀ hδ h1 k hk).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hw) (airyWt_pos _).le
  · refine (HB hU hsub hζ hA hg hrel heik hjets δ q₀ hδ h2 k hk).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hw) (airyBiWt_pos _).le

/-- info: 'FormalResearch.Special.dun_exact_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dun_exact_defect

end FormalResearch.Special
