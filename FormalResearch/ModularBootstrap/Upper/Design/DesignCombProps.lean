module

public import FormalResearch.ModularBootstrap.Upper.Design.PerturbPhi

/-!
# Properties of a finite modification of the reference comb

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, proof of Lemma `Φ` (`ut:Phi`): "by
`cmb:K1`(a), `B_D^{(f)}` is even, real on `ℝ`, analytic on `|Im b| < 7/8`, with `|B_D^{(f)}| ≤ 1` on
`|Im b| ≤ 1/2` and `|B_D^{(f)}| = 1` on `E_±`".  For `designComb` of an admissible finite
modification (`DesignAdmissible`) this is `designComb_K1a`; evenness is `designComb_neg` and the
reflection symmetry `B(-b̄) = conj B(b)` (equivalent to reality on `ℝ` together with evenness) is
`designComb_neg_conj`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Design

open FormalResearch.ModularBootstrap.Upper.Comb

/-! ### 1. The tail -/

/-- `K1(a)` for the tail `combTail c' N η₀` (the same statements as `refComb_K1a`, with the sites
`χ_k`, `k > N`), together with multipliability of the tail product on `|Im b| < 7/8`; the threshold
in `c'` does not depend on the cut `N`. -/
theorem combTail_K1a_unif {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ N : ℕ,
      (∀ {b : ℂ}, |b.im| ≤ 1 / 2 → ‖combTail c' N η₀ b‖ ≤ 1) ∧
      (∀ {b : ℂ}, |b.im| = 1 / 2 → ‖combTail c' N η₀ b‖ = 1) ∧
      DifferentiableOn ℂ (combTail c' N η₀) {b : ℂ | |b.im| < 7 / 8} ∧
      (∀ {b : ℂ}, |b.im| < 7 / 8 →
        Multipliable fun m : ℕ =>
          pairT (chiQuantile c' (N + 1 + m : ℕ)) (η₀ * siteGap c' (N + 1 + m)) b) := by
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  filter_upwards [eventually_gt_atTop 0, h_ev] with c' hc' ⟨hgap_k, _, _, hgap_1⟩ N
  have hgap_nn : ∀ m : ℕ, 0 ≤ siteGap c' (N + 1 + m) := fun m => siteGap_nonneg hc' (by omega)
  have hε_bd : ∀ m : ℕ, |η₀ * siteGap c' (N + 1 + m)| ≤ 1 / 8 := fun m => by
    rw [abs_of_nonneg (mul_nonneg hη₀0 (hgap_nn m))]
    have hgk := (hgap_k (N + 1 + m) (by omega)).trans hgap_1
    calc η₀ * siteGap c' (N + 1 + m) ≤ (1 / 4) * (1 / 2) :=
          mul_le_mul hη₀1 hgk (hgap_nn m) (by norm_num)
      _ = 1 / 8 := by norm_num
  have hχ_nn : ∀ m : ℕ, 0 ≤ chiQuantile c' (N + 1 + m : ℕ) := fun m => by
    have ha : (1 / 4 : ℝ) ≤ ((N + 1 + m : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((N + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N + 1 + m)
      linarith
    exact xiStar_pos.le.trans (chiQuantile_spec hc' ha).1
  have hsum := summable_exp_neg_pi_chiQuantile hc' N
  refine ⟨fun {b} hb => ?_, fun {b} hb => ?_, ?_, fun {b} hb => ?_⟩
  · exact comb_pairProd_norm_le_one (fun m : ℕ => chiQuantile c' (N + 1 + m : ℕ))
      (fun m : ℕ => η₀ * siteGap c' (N + 1 + m)) hχ_nn hε_bd hsum hb
  · exact comb_pairProd_norm_eq_one (fun m : ℕ => chiQuantile c' (N + 1 + m : ℕ))
      (fun m : ℕ => η₀ * siteGap c' (N + 1 + m)) hχ_nn hε_bd hsum hb
  · exact comb_pairProd_differentiableOn (fun m : ℕ => chiQuantile c' (N + 1 + m : ℕ))
      (fun m : ℕ => η₀ * siteGap c' (N + 1 + m)) hχ_nn hε_bd hsum
  · exact ((comb_pairProd_hasProdLocallyUniformlyOn
      (fun m : ℕ => chiQuantile c' (N + 1 + m : ℕ)) (fun m : ℕ => η₀ * siteGap c' (N + 1 + m))
      hχ_nn hε_bd hsum).hasProd hb).multipliable

/-- `K1(a)` for the tail `combTail c' N η₀` at a fixed cut `N` (`combTail_K1a_unif`). -/
theorem combTail_K1a (N : ℕ) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop,
      (∀ {b : ℂ}, |b.im| ≤ 1 / 2 → ‖combTail c' N η₀ b‖ ≤ 1) ∧
      (∀ {b : ℂ}, |b.im| = 1 / 2 → ‖combTail c' N η₀ b‖ = 1) ∧
      DifferentiableOn ℂ (combTail c' N η₀) {b : ℂ | |b.im| < 7 / 8} ∧
      (∀ {b : ℂ}, |b.im| < 7 / 8 →
        Multipliable fun m : ℕ =>
          pairT (chiQuantile c' (N + 1 + m : ℕ)) (η₀ * siteGap c' (N + 1 + m)) b) :=
  (combTail_K1a_unif hη₀0 hη₀1).mono fun _ h => h N

/-! ### 2. Symmetries -/

lemma pairT_neg (χ ε : ℝ) (b : ℂ) : pairT χ ε (-b) = pairT χ ε b := by
  unfold pairT; rw [blaschkeT_neg_b, blaschkeT_neg_b]

lemma pairT_conj (χ ε : ℝ) (b : ℂ) :
    pairT χ ε (starRingEnd ℂ b) = starRingEnd ℂ (pairT χ ε b) := by
  unfold pairT
  have h1 := blaschkeT_conj ((χ : ℂ) + (ε : ℂ) * Complex.I) b
  have h2 := blaschkeT_conj ((χ : ℂ) - (ε : ℂ) * Complex.I) b
  have e1 : starRingEnd ℂ ((χ : ℂ) + (ε : ℂ) * Complex.I) = (χ : ℂ) - (ε : ℂ) * Complex.I := by
    simp [Complex.conj_ofReal, Complex.conj_I]; ring
  have e2 : starRingEnd ℂ ((χ : ℂ) - (ε : ℂ) * Complex.I) = (χ : ℂ) + (ε : ℂ) * Complex.I := by
    simp [Complex.conj_ofReal, Complex.conj_I]
  rw [e1] at h1
  rw [e2] at h2
  rw [map_mul, ← h1, ← h2, mul_comm]

lemma pairT_neg_conj (χ ε : ℝ) (b : ℂ) :
    pairT χ ε (-(starRingEnd ℂ b)) = starRingEnd ℂ (pairT χ ε b) := by
  rw [pairT_neg, pairT_conj]

lemma blaschkeT_ofReal_neg_conj (y : ℝ) (b : ℂ) :
    blaschkeT (y : ℂ) (-(starRingEnd ℂ b)) = starRingEnd ℂ (blaschkeT (y : ℂ) b) := by
  rw [blaschkeT_neg_b]
  have := blaschkeT_conj (y : ℂ) b
  rwa [Complex.conj_ofReal] at this

lemma combTail_neg (c' : ℝ) (N : ℕ) (η₀ : ℝ) (b : ℂ) :
    combTail c' N η₀ (-b) = combTail c' N η₀ b := by
  unfold combTail
  simp only [pairT_neg]

/-- `B_D(-b̄) = conj B_D(b)` where the tail product converges. -/
lemma combTail_neg_conj (c' : ℝ) (N : ℕ) (η₀ : ℝ) (b : ℂ)
    (hm : Multipliable fun m : ℕ =>
      pairT (chiQuantile c' (N + 1 + m : ℕ)) (η₀ * siteGap c' (N + 1 + m)) b) :
    combTail c' N η₀ (-(starRingEnd ℂ b)) = starRingEnd ℂ (combTail c' N η₀ b) := by
  have h := hm.hasProd.map (starRingEnd ℂ) Complex.continuous_conj
  have e : (starRingEnd ℂ ∘ fun m : ℕ =>
      pairT (chiQuantile c' (N + 1 + m : ℕ)) (η₀ * siteGap c' (N + 1 + m)) b) =
      fun m : ℕ => pairT (chiQuantile c' (N + 1 + m : ℕ)) (η₀ * siteGap c' (N + 1 + m))
        (-(starRingEnd ℂ b)) := by
    funext m
    simp [Function.comp, pairT_neg_conj]
  rw [e] at h
  exact h.tprod_eq

lemma designComb_neg (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) (b : ℂ) :
    designComb c' f N η₀ σ ε (-b) = designComb c' f N η₀ σ ε b := by
  unfold designComb
  simp only [blaschkeT_neg_b, pairT_neg, combTail_neg]

lemma designComb_neg_conj (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) (b : ℂ)
    (hm : Multipliable fun m : ℕ =>
      pairT (chiQuantile c' (N + 1 + m : ℕ)) (η₀ * siteGap c' (N + 1 + m)) b) :
    designComb c' f N η₀ σ ε (-(starRingEnd ℂ b)) =
      starRingEnd ℂ (designComb c' f N η₀ σ ε b) := by
  unfold designComb
  rw [map_mul, map_mul, map_prod, combTail_neg_conj c' N η₀ b hm, blaschkeT_ofReal_neg_conj]
  simp only [pairT_neg_conj]

/-! ### 3. `K1(a)` for the modification -/

lemma differentiableAt_pairT {χ ε : ℝ} (hε : |ε| ≤ 1 / 8) {b : ℂ} (hb : |b.im| < 7 / 8) :
    DifferentiableAt ℂ (pairT χ ε) b := by
  unfold pairT
  have h1 : DifferentiableAt ℂ (blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I)) b :=
    differentiableAt_blaschkeT (by
      have him : |((χ : ℂ) + (ε : ℂ) * Complex.I).im| ≤ 1 / 8 := by simpa using hε
      linarith)
  have h2 : DifferentiableAt ℂ (blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I)) b :=
    differentiableAt_blaschkeT (by
      have him : |((χ : ℂ) - (ε : ℂ) * Complex.I).im| ≤ 1 / 8 := by simpa [abs_neg] using hε
      linarith)
  exact h1.mul h2

/-- **`K1(a)` for `B_D^{(f)}`**: `|B_D| ≤ 1` on `|Im b| ≤ 1/2`, `|B_D| = 1` on `|Im b| = 1/2`,
`B_D` analytic on `|Im b| < 7/8`. -/
theorem designComb_K1a {c' : ℝ} {f N : ℕ} {η₀ : ℝ} {σ ε : ℕ → ℝ}
    (hA : DesignAdmissible c' f N η₀ σ ε)
    (hT1 : ∀ {b : ℂ}, |b.im| ≤ 1 / 2 → ‖combTail c' N η₀ b‖ ≤ 1)
    (hT2 : ∀ {b : ℂ}, |b.im| = 1 / 2 → ‖combTail c' N η₀ b‖ = 1)
    (hT3 : DifferentiableOn ℂ (combTail c' N η₀) {b : ℂ | |b.im| < 7 / 8}) :
    (∀ {b : ℂ}, |b.im| ≤ 1 / 2 → ‖designComb c' f N η₀ σ ε b‖ ≤ 1) ∧
    (∀ {b : ℂ}, |b.im| = 1 / 2 → ‖designComb c' f N η₀ σ ε b‖ = 1) ∧
    DifferentiableOn ℂ (designComb c' f N η₀ σ ε) {b : ℂ | |b.im| < 7 / 8} := by
  have hw : ∀ i ∈ Finset.range (N - f), |ε (f + 1 + i)| ≤ 1 / 4 := fun i hi =>
    (hA.width i (Finset.mem_range.mp hi)).trans (by norm_num)
  refine ⟨fun {b} hb => ?_, fun {b} hb => ?_, fun b hb => ?_⟩
  · unfold designComb
    rw [norm_mul, norm_mul, norm_prod]
    have h1 := norm_blaschkeT_real_le_one (designSite c' σ f) hb
    have h2 : ∏ i ∈ Finset.range (N - f), ‖pairT (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) b‖ ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i hi =>
        norm_pair_blaschkeT_le_one _ _ (hw i hi) hb
    have := mul_le_mul (mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      zero_le_one) (hT1 hb) (norm_nonneg _) (by norm_num)
    simpa using this
  · unfold designComb
    rw [norm_mul, norm_mul, norm_prod, norm_blaschkeT_real_eq_one _ hb, hT2 hb]
    have : ∏ i ∈ Finset.range (N - f), ‖pairT (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) b‖ = 1 :=
      Finset.prod_eq_one fun i hi => norm_pair_blaschkeT_eq_one _ _ (hw i hi) hb
    rw [this]; norm_num
  · have hbm : |b.im| < 7 / 8 := hb
    unfold designComb
    refine DifferentiableWithinAt.mul (DifferentiableWithinAt.mul ?_ ?_) (hT3 b hb)
    · exact (differentiableAt_blaschkeT (by simpa using hbm.trans (by norm_num))
        |>.differentiableWithinAt)
    · exact DifferentiableAt.differentiableWithinAt
        (DifferentiableAt.fun_finsetProd fun i hi =>
          differentiableAt_pairT (hA.width i (Finset.mem_range.mp hi)) hbm)

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.combTail_K1a_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combTail_K1a_unif

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.combTail_K1a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combTail_K1a

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.designComb_neg_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designComb_neg_conj

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.designComb_K1a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designComb_K1a

end FormalResearch.ModularBootstrap.Upper.Design
