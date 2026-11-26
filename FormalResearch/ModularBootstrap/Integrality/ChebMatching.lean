module

public import FormalResearch.ModularBootstrap.Integrality.CorrDef
public import FormalResearch.ModularBootstrap.Integrality.CumulativeRounding
public import FormalResearch.ModularBootstrap.Integrality.ChebAtoms
public import Mathlib.Data.Fin.Tuple.Sort
public import FormalResearch.ModularBootstrap.Integrality.MidpointGrid
public import Mathlib.MeasureTheory.Measure.Sub
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Assembly of the integer moment matching (`int:cheb`, `int:cheb-explicit`)

`CFT/modular_bootstrap/paper/integrality.tex`, Lemma INT-M (`int:cheb`) and Lemma INT-M.exp
(`int:cheb-explicit`): a positive measure `μ` on `[-1,1]` of integer mass with density floor
`μ ≥ W_0 dx` is replaced by an integer-weighted atomic measure with the same polynomial moments
through degree `M`.  The proof is: remove the floor `W_0 dx`, represent the remainder by finitely many
atoms (Carathéodory) and the floor by the Fejér quadrature on the midpoint grid, round cumulatively in
angle order (`CumulativeRounding`), and repair the moment defect by moving `R` integer units at each
grid site (the correction property `Corr`, proved in `CorrEuclid` for the Euclidean inverse).

This file proves the assembly *from `Corr`*; `ChebMatching` is independent of how `Corr` is proved.
**Proved.**
-/

@[expose] public section

open Real Finset MeasureTheory Polynomial
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Integrality

/-- A finite type of angles can be enumerated in nondecreasing angle order. -/
lemma exists_sorted_enum {ι : Type} [Fintype ι] (a : ι → ℝ) :
    ∃ e : Fin (Fintype.card ι) ≃ ι, Monotone (a ∘ e) := by
  let eq := Fintype.equivFin ι
  let b : Fin (Fintype.card ι) → ℝ := a ∘ eq.symm
  refine ⟨(Tuple.sort b).trans eq.symm, ?_⟩
  exact Tuple.monotone_sort b

/-- Reindexing a sorted sum. -/
lemma sum_range_eq_sum {ι : Type} [Fintype ι] {L : ℕ} (e : Fin L ≃ ι) (f : ι → ℝ) (g : ℕ → ℝ)
    (hg : ∀ k (hk : k < L), g k = f (e ⟨k, hk⟩)) : ∑ k ∈ range L, g k = ∑ i, f i := by
  rw [← Fin.sum_univ_eq_sum_range g L, ← Equiv.sum_comp e f]
  exact sum_congr rfl fun k _ => hg k.1 k.2

/-- **Rounding and repair.**  Non-negative weights `w_i ≥ 0` of integer total `N`, at angles
`a_i ∈ [0,π]`, are rounded to naturals `t_i ≥ ⌊w_i⌋` of the same total, and the cosine-moment defect
is repaired by an angle shift `h` of the midpoint grid of size `n` carrying `R` units per site. -/
theorem round_and_repair {ι : Type} [Fintype ι] {n M : ℕ} {R : ℝ} (hR : 0 < R)
    (hcorr : Corr n M R) (a w : ι → ℝ) (ha : ∀ i, a i ∈ Set.Icc (0 : ℝ) π) (hw : ∀ i, 0 ≤ w i)
    (N : ℕ) (hN : ∑ i, w i = N) :
    ∃ (t : ι → ℕ) (h : ℕ → ℝ), (∀ i, ⌊w i⌋₊ ≤ t i) ∧ ∑ i, t i = N ∧
      ∀ m : ℕ, 1 ≤ m → m ≤ M →
        ∑ i, (t i : ℝ) * cos ((m : ℝ) * a i) +
          R * ∑ j ∈ range n, (cos ((m : ℝ) * (midAngle n j + h j)) -
            cos ((m : ℝ) * midAngle n j)) = ∑ i, w i * cos ((m : ℝ) * a i) := by
  obtain ⟨L, e, he⟩ : ∃ (L : ℕ) (e : Fin L ≃ ι), Monotone (a ∘ e) :=
    ⟨_, exists_sorted_enum a⟩
  let w' : ℕ → ℝ := fun k => if hk : k < L then w (e ⟨k, hk⟩) else 0
  let α' : ℕ → ℝ := fun k => if hk : k < L then a (e ⟨k, hk⟩) else π
  have hw'e : ∀ k (hk : k < L), w' k = w (e ⟨k, hk⟩) := fun k hk => by simp [w', hk]
  have hα'e : ∀ k (hk : k < L), α' k = a (e ⟨k, hk⟩) := fun k hk => by simp [α', hk]
  have hα'L : α' L = π := by simp [α']
  have hw'nn : ∀ k < L, 0 ≤ w' k := fun k hk => by rw [hw'e k hk]; exact hw _
  have hN' : ∑ k ∈ range L, w' k = N := by
    rw [sum_range_eq_sum e w w' hw'e]; exact hN
  obtain ⟨t', htot, hfl, S, hS, hdef⟩ := cumulative_rounding w' L hw'nn N hN'
  let t : ι → ℕ := fun i => t' (e.symm i).1
  have hte : ∀ k (hk : k < L), t (e ⟨k, hk⟩) = t' k := fun k hk => by simp [t]
  have hα'mem : ∀ i ≤ L, α' i ∈ Set.Icc (0 : ℝ) π := by
    intro i hi
    by_cases hiL : i < L
    · rw [hα'e i hiL]; exact ha _
    · have : i = L := by omega
      rw [this, hα'L]; exact ⟨pi_pos.le, le_rfl⟩
  have hα'mono : ∀ i < L, α' i ≤ α' (i + 1) := by
    intro i hi
    by_cases hi1 : i + 1 < L
    · rw [hα'e i hi, hα'e (i + 1) hi1]
      exact he (Fin.mk_le_mk.2 (Nat.le_succ i))
    · have : i + 1 = L := by omega
      rw [this, hα'L]; exact ((hα'mem i hi.le).2)
  obtain ⟨h, hh⟩ := hcorr L α' S hα'mem hα'mono hS
  refine ⟨t, h, ?_, ?_, ?_⟩
  · -- `t_i ≥ ⌊w_i⌋`
    intro i
    have hk : (e.symm i).1 < L := (e.symm i).2
    have := hfl _ hk
    rw [hw'e _ hk] at this
    simpa [t] using this
  · -- total
    rw [← Equiv.sum_comp e t]
    have h1 : ∑ k : Fin L, t (e k) = ∑ k : Fin L, t' k.1 := sum_congr rfl fun k _ => hte k.1 k.2
    rw [h1, Fin.sum_univ_eq_sum_range (fun k => t' k) L]
    exact htot
  · intro m hm1 hmM
    have hdefm := hdef (fun k => cos ((m : ℝ) * α' k))
    have hL1 : ∑ k ∈ range L, (w' k - t' k) * cos ((m : ℝ) * α' k) =
        ∑ i, (w i - (t i : ℝ)) * cos ((m : ℝ) * a i) := by
      refine sum_range_eq_sum e (fun i => (w i - (t i : ℝ)) * cos ((m : ℝ) * a i)) _ ?_
      intro k hk
      simp only [hw'e k hk, hα'e k hk, hte k hk]
    rw [hL1] at hdefm
    have hhm := hh m hm1 hmM
    have hRh : R * ∑ j ∈ range n, (cos ((m : ℝ) * (midAngle n j + h j)) -
        cos ((m : ℝ) * midAngle n j)) =
        ∑ i ∈ range L, S i * (cos ((m : ℝ) * α' i) - cos ((m : ℝ) * α' (i + 1))) := by
      rw [hhm]; field_simp
    rw [hRh, ← hdefm]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => by ring

/-- Polynomials are integrable against a finite measure carried by `[-1,1]`. -/
lemma integrable_poly_of_supp {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hsupp : ν (Set.Icc (-1 : ℝ) 1)ᶜ = 0) (P : ℝ[X]) : Integrable (fun x => P.eval x) ν := by
  have hae : ∀ᵐ x ∂ν, x ∈ Set.Icc (-1 : ℝ) 1 := by
    have := measure_eq_zero_iff_ae_notMem.1 hsupp
    exact this.mono fun x hx => by simpa using hx
  have h1 : IntegrableOn (fun x => P.eval x) (Set.Icc (-1 : ℝ) 1) ν :=
    P.continuous.continuousOn.integrableOn_compact isCompact_Icc
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h1

lemma midAngle_mem_Icc {n j : ℕ} (hj : j < n) : midAngle n j ∈ Set.Icc (0 : ℝ) π := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
  unfold midAngle
  constructor
  · positivity
  · rw [div_le_iff₀ hn]
    nlinarith [pi_pos]

/-- **The conclusion of `int:cheb`**: a finitely supported positive integer-weighted atomic measure
`σ = ∑_k d_k δ_{x_k}` on `[-1,1]` (`x_k ∈ [-1,1]`, `d_k ∈ ℤ_{≥ 1}`) with the same polynomial moments
as `μ` through degree `M`. -/
def IntegerMomentMatching (μ : Measure ℝ) (M : ℕ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (x : κ → ℝ) (d : κ → ℕ), (∀ k, x k ∈ Set.Icc (-1 : ℝ) 1) ∧
    (∀ k, 1 ≤ d k) ∧
    ∀ P : ℝ[X], P.degree ≤ M → ∫ t, P.eval t ∂μ = ∑ k, (d k : ℝ) * P.eval (x k)

/-- **Integer atomic moment matching, from the correction property.**  Let `μ` be a finite measure
on `[-1,1]` of integer mass `N`, with the density floor `μ ≥ W_0 dx`, and let `R ≥ 1` integer units
per site of the midpoint grid of size `n ≥ M + 1` be available (`R ≤ 2W_0/n²`) and repair every
rounding defect (`Corr n M R`).  Then there is a finitely supported positive integer-weighted atomic
measure with the same polynomial moments through degree `M`. -/
theorem exists_integer_atomic_of_corr {n M R : ℕ} (hR : 1 ≤ R) (hn : M + 1 ≤ n)
    (hcorr : Corr n M (R : ℝ)) {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hsupp : μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0) {N : ℕ} (hN : μ Set.univ = N)
    {W0 : ℝ} (hW0 : 0 ≤ W0) (hfloor : (R : ℝ) ≤ 2 * W0 / (n : ℝ) ^ 2)
    (hμ : ENNReal.ofReal W0 • volume.restrict (Set.Icc (-1 : ℝ) 1) ≤ μ) :
    IntegerMomentMatching μ M := by
  unfold IntegerMomentMatching
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  set I := Set.Icc (-1 : ℝ) 1 with hI
  set F : Measure ℝ := ENNReal.ofReal W0 • volume.restrict I with hF
  have : IsFiniteMeasure (volume.restrict I) := ⟨by simp [hI]⟩
  have : IsFiniteMeasure F := Measure.smul_finite _ ENNReal.ofReal_ne_top
  set ν : Measure ℝ := μ - F with hν
  have hνF : ν + F = μ := Measure.sub_add_cancel_of_le hμ
  have : IsFiniteMeasure ν :=
    ⟨lt_of_le_of_lt (Measure.sub_le (μ := μ) (ν := F) Set.univ) (measure_lt_top μ _)⟩
  have hνsupp : ν Iᶜ = 0 := le_antisymm ((Measure.sub_le (μ := μ) (ν := F) Iᶜ).trans hsupp.le) bot_le
  have hFsupp : F Iᶜ = 0 := by
    have : (volume.restrict I) Iᶜ = 0 := by
      rw [Measure.restrict_apply (isClosed_Icc.isOpen_compl.measurableSet), Set.compl_inter_self,
        measure_empty]
    simp [hF, this]
  -- the moments of `μ`
  have hmom : ∀ m : ℕ, ∫ x, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x ∂μ =
      ∫ x, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x ∂ν + W0 * chebInt m := by
    intro m
    rw [← hνF, integral_add_measure (integrable_poly_of_supp hνsupp _)
      (integrable_poly_of_supp hFsupp _)]
    congr 1
    rw [hF, integral_smul_measure, ENNReal.toReal_ofReal hW0, smul_eq_mul]
    congr 1
    rw [← integral_chebyshevT m, intervalIntegral.integral_of_le (by norm_num),
      ← integral_Icc_eq_integral_Ioc]
  -- the mass
  have hmass : (N : ℝ) = ν.real Set.univ + 2 * W0 := by
    have h1 : μ Set.univ = ν Set.univ + F Set.univ := by rw [← hνF]; rfl
    have h2 : F Set.univ = ENNReal.ofReal (2 * W0) := by
      simp only [hF, smul_apply, Measure.restrict_apply_univ, hI, Real.volume_Icc,
        smul_eq_mul]
      rw [← ENNReal.ofReal_mul hW0]; congr 1; ring
    have h3 : (μ Set.univ).toReal = (ν Set.univ).toReal + (F Set.univ).toReal := by
      rw [h1, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    rw [h2, ENNReal.toReal_ofReal (by positivity), hN] at h3
    simpa [Measure.real] using h3
  obtain ⟨ι, hι, β, ρ, hβ, hρ, hρsum, hρmom⟩ := exists_atomic_chebyshev hνsupp M
  -- weights and angles of the combined list: grid sites and remainder atoms
  let a : Fin n ⊕ ι → ℝ := Sum.elim (fun j => midAngle n j.1) β
  let w : Fin n ⊕ ι → ℝ := Sum.elim (fun j => W0 * fejerWeight n (M / 2) j.1) ρ
  have hlam : ∀ j : ℕ, 2 / (n : ℝ) ^ 2 ≤ fejerWeight n (M / 2) j := fun j =>
    fejerWeight_ge_sq hn0 hn j
  have ha : ∀ i, a i ∈ Set.Icc (0 : ℝ) π := by
    rintro (j | i)
    · exact midAngle_mem_Icc j.2
    · exact hβ i
  have hw : ∀ i, 0 ≤ w i := by
    rintro (j | i)
    · exact mul_nonneg hW0 (le_trans (by positivity) (hlam j.1))
    · exact (hρ i).le
  have hfejer : ∀ m : ℕ, m ≤ M → ∑ j : Fin n, fejerWeight n (M / 2) j.1 * cos ((m : ℝ) * midAngle n j.1) =
      chebInt m := by
    intro m hm
    rw [Fin.sum_univ_eq_sum_range (fun j => fejerWeight n (M / 2) j * cos ((m : ℝ) * midAngle n j)) n]
    exact fejerWeight_cos_sum hn0 hn hm
  have hsumw : ∑ i, w i = N := by
    rw [Fintype.sum_sum_type]
    simp only [w, Sum.elim_inl, Sum.elim_inr]
    have h0 := hfejer 0 (Nat.zero_le _)
    simp only [Nat.cast_zero, zero_mul, cos_zero, mul_one] at h0
    have hc0 : chebInt 0 = 2 := by simp [chebInt]
    rw [← mul_sum, h0, hc0, hρsum, hmass]
    ring
  obtain ⟨t, h, hfl, htot, hmoment⟩ := round_and_repair (n := n) (M := M) (R := (R : ℝ))
    (by exact_mod_cast hR) hcorr a w ha hw N hsumw
  have hgrid : ∀ j : Fin n, R ≤ t (Sum.inl j) := by
    intro j
    refine le_trans ?_ (hfl (Sum.inl j))
    apply Nat.le_floor
    simp only [w, Sum.elim_inl]
    calc (R : ℝ) ≤ 2 * W0 / (n : ℝ) ^ 2 := hfloor
      _ = W0 * (2 / (n : ℝ) ^ 2) := by ring
      _ ≤ W0 * fejerWeight n (M / 2) j.1 := mul_le_mul_of_nonneg_left (hlam j.1) hW0
  -- the final family: remaining grid weights, remainder atoms, shifted grid sites
  let g : Fin n ⊕ ι → ℕ := Sum.elim (fun _ => R) (fun _ => 0)
  have hgt : ∀ i, g i ≤ t i := by
    rintro (j | i)
    · exact hgrid j
    · exact Nat.zero_le _
  let d' : (Fin n ⊕ ι) ⊕ Fin n → ℕ := Sum.elim (fun i => t i - g i) (fun _ => R)
  let ang : (Fin n ⊕ ι) ⊕ Fin n → ℝ := Sum.elim a (fun j => midAngle n j.1 + h j.1)
  have hQ : ∀ m : ℕ, m ≤ M →
      ∑ k, (d' k : ℝ) * cos ((m : ℝ) * ang k) = ∫ x, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x ∂μ := by
    intro m hm
    rw [Fintype.sum_sum_type]
    simp only [d', ang, Sum.elim_inl, Sum.elim_inr]
    have e1 : ∑ i : Fin n ⊕ ι, ((t i - g i : ℕ) : ℝ) * cos ((m : ℝ) * a i) =
        ∑ i : Fin n ⊕ ι, (t i : ℝ) * cos ((m : ℝ) * a i) -
          ∑ i : Fin n ⊕ ι, (g i : ℝ) * cos ((m : ℝ) * a i) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [Nat.cast_sub (hgt i)]; ring
    have e2 : ∑ i : Fin n ⊕ ι, (g i : ℝ) * cos ((m : ℝ) * a i) =
        ∑ j : Fin n, (R : ℝ) * cos ((m : ℝ) * midAngle n j.1) := by
      rw [Fintype.sum_sum_type]
      simp [g, a]
    rw [e1, e2]
    by_cases hm0 : m = 0
    · subst hm0
      simp only [Nat.cast_zero, zero_mul, cos_zero, mul_one, sum_const, card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hT0 : ∫ x, (Polynomial.Chebyshev.T ℝ 0).eval x ∂μ = N := by
        rw [Polynomial.Chebyshev.T_zero]
        simp [Measure.real, hN]
      rw [hT0]
      have : ∑ i : Fin n ⊕ ι, (t i : ℝ) = N := by exact_mod_cast htot
      rw [this]
      ring
    · have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
      have e3 := hmoment m hm1 hm
      rw [← Fin.sum_univ_eq_sum_range (fun j => cos ((m : ℝ) * (midAngle n j + h j)) -
        cos ((m : ℝ) * midAngle n j)) n] at e3
      have e4 : ∑ i : Fin n ⊕ ι, w i * cos ((m : ℝ) * a i) =
          W0 * chebInt m + ∫ x, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x ∂ν := by
        rw [Fintype.sum_sum_type]
        simp only [w, a, Sum.elim_inl, Sum.elim_inr]
        rw [← hfejer m hm, mul_sum, hρmom m hm1 hm]
        congr 1
        exact sum_congr rfl fun j _ => by ring
      rw [e4] at e3
      rw [hmom m]
      have e5 : ∑ j : Fin n, ((cos ((m : ℝ) * (midAngle n j.1 + h j.1)) -
          cos ((m : ℝ) * midAngle n j.1))) =
          ∑ j : Fin n, cos ((m : ℝ) * (midAngle n j.1 + h j.1)) -
            ∑ j : Fin n, cos ((m : ℝ) * midAngle n j.1) := sum_sub_distrib _ _
      have e6 : ∑ j : Fin n, (R : ℝ) * cos ((m : ℝ) * midAngle n j.1) =
          (R : ℝ) * ∑ j : Fin n, cos ((m : ℝ) * midAngle n j.1) := (mul_sum _ _ _).symm
      have e7 : ∑ j : Fin n, (R : ℝ) * cos ((m : ℝ) * (midAngle n j.1 + h j.1)) =
          (R : ℝ) * ∑ j : Fin n, cos ((m : ℝ) * (midAngle n j.1 + h j.1)) := (mul_sum _ _ _).symm
      rw [e5] at e3
      rw [e6, e7]
      nlinarith [e3]
  -- discard the atoms of zero weight
  classical
  let κ : Type := {k : (Fin n ⊕ ι) ⊕ Fin n // d' k ≠ 0}
  let x : κ → ℝ := fun k => cos (ang k.1)
  let dd : κ → ℕ := fun k => d' k.1
  have hsubsum : ∀ f : (Fin n ⊕ ι) ⊕ Fin n → ℝ, (∀ k, d' k = 0 → f k = 0) →
      ∑ k : κ, f k.1 = ∑ k, f k := by
    intro f hf
    rw [← Finset.sum_subtype (univ.filter fun k => d' k ≠ 0) (p := fun k => d' k ≠ 0)
      (by intro k; simp) f]
    exact Finset.sum_filter_of_ne fun k _ hk => by
      by_contra h0; exact hk (hf k h0)
  refine ⟨κ, inferInstance, x, dd, fun k => ⟨neg_one_le_cos _, cos_le_one _⟩,
    fun k => Nat.pos_of_ne_zero k.2, ?_⟩
  intro P hP
  obtain ⟨c, hc⟩ := exists_chebyshev_expansion M P (by exact_mod_cast hP)
  have hTcos : ∀ (m : ℕ) (k : κ), (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (x k) =
      cos ((m : ℝ) * ang k.1) := by
    intro m k
    simp only [x]
    rw [Polynomial.Chebyshev.T_real_cos]; simp
  have hmk : ∀ m : ℕ, m ≤ M → ∑ k : κ, (dd k : ℝ) * cos ((m : ℝ) * ang k.1) =
      ∫ t, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval t ∂μ := by
    intro m hm
    rw [← hQ m hm]
    exact hsubsum (fun k => (d' k : ℝ) * cos ((m : ℝ) * ang k)) (fun k hk => by simp [hk])
  rw [hc]
  simp only [eval_finsetSum, eval_mul, eval_C]
  rw [integral_finsetSum _ (fun m _ => (integrable_poly_of_supp hsupp _).const_mul _)]
  have e1 : ∀ m ∈ range (M + 1), ∫ t, c m * (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval t ∂μ =
      c m * ∑ k : κ, (dd k : ℝ) * cos ((m : ℝ) * ang k.1) := by
    intro m hm
    rw [integral_const_mul, hmk m (by have := mem_range.1 hm; omega)]
  rw [sum_congr rfl e1]
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  refine sum_congr rfl fun m _ => ?_
  rw [hTcos m k]
  ring

end FormalResearch.ModularBootstrap.Integrality
