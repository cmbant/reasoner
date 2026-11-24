module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityMeasure
public import FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum

/-!
# Non-vacuity of `TwoZeroIdealApprox` (`virasoro_two_level.tex`, `gt:2.6`, *Designs and their limits*)

`TwoZeroIdealApprox` asks, for every admissible ideal datum `δ`, for admissible two-simple-zero designs `𝔇_i` with
`q_i = δ.q`, windows `W_{𝔇_i} → Re F_δ` pointwise and boundedly on compacta, and `limsup ∫ W_{𝔇_i} ≤ ∫ Re F_δ`.

The vacuum half is proved for the data `clarkDatum α z₁ u₂ 0 K` (zeros `z₁`, `u₂ < z₂`, double zeros at the Clark nodes
`z_3, …, z_K`, ideal Airy pairs beyond) from `tendsto_intWr` (`NegativeVacuum`, Tannery for infinite products and Lemma E):

* `win_clarkDatum_eq`: `Re F_δ = Re f_K` (the window function of `WindowOptimum`);
* `twoZeroApprox_vacuum_nonvacuous`: there are admissible two-simple-zero designs `𝔇_j` with `q_j = u₂` and
  `∫ W_{𝔇_j} → ∫ Re F_δ`.

The window half (pointwise and locally uniform convergence `W_{𝔇_j} → Re F_δ`, for all data) is the content of
`TwoZeroIdealApprox` that is not proved here.  All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty
open FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum

lemma Nr_clarkDatum_zero (α u₂ : ℝ) (K : ℕ) (x : ℝ) :
    (clarkDatum α (clarkNode α 1) u₂ 0 K).Nr x = windowNr α K u₂ x := by
  unfold IdealDatum.Nr windowNr
  have : ∏ k ∈ Finset.Icc 3 K, (x - (clarkDatum α (clarkNode α 1) u₂ 0 K).s k) ^ 2 =
      ∏ k ∈ Finset.Icc 3 K, (x - clarkNode α k) ^ 2 :=
    Finset.prod_congr rfl fun k hk => by
      rw [clarkDatum_s_of_ne α _ _ (by have := (Finset.mem_Icc.mp hk).1; omega)]
  simp only [clarkDatum] at this ⊢
  rw [this]

/-- The real part of the ideal window of `clarkDatum α z₁ u₂ 0 K` is `Re f_K`. -/
lemma win_clarkDatum_eq (α u₂ : ℝ) (K : ℕ) (x : ℝ) :
    (clarkDatum α (clarkNode α 1) u₂ 0 K).win x = (windowF α K u₂ (x : ℂ)).re := by
  set δ := clarkDatum α (clarkNode α 1) u₂ 0 K with hδ
  have hdense : Dense {y : ℝ | windowDr K y ≠ 0} := by
    have h1 : Dense ((Set.univ : Set ℝ) \ (airyZero '' (Finset.Icc 1 K : Set ℕ))) :=
      dense_univ.sdiff_finite ((Finset.Icc 1 K).finite_toSet.image _)
    refine h1.mono fun y hy => ?_
    simp only [Set.mem_sdiff, mem_univ, true_and, mem_image, not_exists, not_and] at hy
    show windowDr K y ≠ 0
    intro h0
    unfold windowDr at h0
    obtain ⟨j, hj, hjy⟩ := Finset.prod_eq_zero_iff.1 h0
    exact hy j (by simpa using hj) (sub_eq_zero.1 hjy).symm
  have hc1 : Continuous δ.win := δ.continuous_win
  have hc2 : Continuous fun y : ℝ => (windowF α K u₂ (y : ℂ)).re :=
    Complex.continuous_re.comp ((differentiable_windowF α K u₂).continuous.comp Complex.continuous_ofReal)
  have := Continuous.ext_on hdense hc1 hc2 (fun y hy => by
    have hy' : windowDr K y ≠ 0 := hy
    have h1 := δ.win_spec y
    have hK : δ.K = K := rfl
    rw [hK, Nr_clarkDatum_zero] at h1
    have h2 := windowF_spec α K u₂ (y : ℂ)
    rw [windowD_ofReal, windowN_ofReal, airyAiC_ofReal] at h2
    have h3 : (windowF α K u₂ (y : ℂ)) * (((windowDr K y ^ 2 : ℝ)) : ℂ) =
        ((airyAi y ^ 2 * windowNr α K u₂ y : ℝ) : ℂ) := by
      push_cast at h2 ⊢; exact h2.symm
    have h4 := congrArg Complex.re h3
    rw [Complex.re_mul_ofReal] at h4
    show δ.win y = (windowF α K u₂ (y : ℂ)).re
    apply mul_right_cancel₀ (pow_ne_zero 2 hy')
    rw [h1, h4, Complex.ofReal_re])
  exact congrFun this x

/-- **Non-vacuity of `TwoZeroIdealApprox` (vacuum half).**  For the ideal data of `f_K` there are admissible
two-simple-zero designs with `q_j = u₂` whose vacuum integrals converge to `∫ Re F_δ`. -/
theorem twoZeroApprox_vacuum_nonvacuous (α : ℝ) {K : ℕ} (hK : 3 ≤ K) {u₂ : ℝ} (hu₂ : u₂ < clarkNode α 2) :
    ∃ (n : ℕ → ℕ) (d : ∀ j, TwoZeroDesign (n j)), (∀ j, 1 ≤ n j) ∧ (∀ j, (d j).Adm) ∧
      (∀ j, (d j).q = u₂) ∧
      Tendsto (fun j => ∫ u, (d j).Wr u) atTop
        (𝓝 (∫ u, (clarkDatum α (clarkNode α 1) u₂ 0 K).win u)) := by
  have hz12 : clarkNode α 2 < clarkNode α 1 := clarkNode_lt_of_lt le_rfl (by norm_num) α
  obtain ⟨L, hL⟩ := exists_nat_gt (max 4 (1 / (clarkNode α 1 - clarkNode α 2)))
  have hL4 : (4 : ℝ) < L := lt_of_le_of_lt (le_max_left _ _) hL
  have hLd : 1 / (clarkNode α 1 - clarkNode α 2) < L := lt_of_le_of_lt (le_max_right _ _) hL
  have hηpos : ∀ j : ℕ, 0 < ((j : ℝ) + L)⁻¹ := fun j => by positivity
  have hηd : ∀ j : ℕ, ((j : ℝ) + L)⁻¹ < clarkNode α 1 - clarkNode α 2 := fun j => by
    have hd : 0 < clarkNode α 1 - clarkNode α 2 := by linarith
    have hLpos : (0 : ℝ) < (j : ℝ) + L := by positivity
    rw [inv_lt_comm₀ hLpos hd]
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h2 : ((clarkNode α 1 - clarkNode α 2))⁻¹ < L := by simpa using hLd
    linarith
  refine ⟨fun j => K + j, fun j => negDesign α K (K + j) ((j : ℝ) + L)⁻¹ u₂, fun j => by show 1 ≤ K + j; omega,
    fun j => negDesign_adm α (hηpos j) hu₂ (hηd j), fun j => rfl, ?_⟩
  have h := tendsto_intWr α hK u₂ (L := L) (by exact_mod_cast hL4.le)
  have e : windowInt α K u₂ = ∫ u, (clarkDatum α (clarkNode α 1) u₂ 0 K).win u := by
    unfold windowInt
    exact (integral_congr_ae (Eventually.of_forall fun x => (win_clarkDatum_eq α u₂ K x).symm))
  rwa [e] at h

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.win_clarkDatum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_clarkDatum_eq

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroApprox_vacuum_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroApprox_vacuum_nonvacuous

end FormalResearch.ModularBootstrap.TwoLevel
