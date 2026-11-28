module

public import FormalResearch.ModularBootstrap.Integrality.ChebMatching
public import FormalResearch.ModularBootstrap.Integrality.AngleShift
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lemma INT-7B.exp (`int:cheb2d-explicit`): Explicit two-dimensional moment-matching floor

Proves `int:cheb2d-explicit` (`CFT/modular_bootstrap/paper/integrality_spin.tex`):
for any `M ≥ 1` (`N = M + 1`) and any finite positive Borel measure `μ` supported on `[-1, 1]^2`
with integer total mass `N_tot = μ([-1, 1]^2) ∈ ℤ_{≥ 1}` and uniform density floor
`μ ≥ W_0 dx dy` with `W_0 ≥ 32 N^{13/2}`, there exists a finitely supported positive integer-weighted
atomic measure `σ = ∑_r d_r δ_{(x_r, y_r)}` (`d_r ∈ ℤ_{≥ 1}`, `(x_r, y_r) ∈ [-1, 1]^2`)
matching all bivariate moments `x^m y^k` (`0 ≤ m, k ≤ M`).

Uses bivariate Carathéodory on `[-1, 1]^2`, two labelled product Fejér-I midpoint grids of size
`N × N`, simple floor rounding (with excess units placed at `(0, 0)`), and two-stage Euclidean
angle-shift correction via `Integrality.exists_angleShift`. **Proved**, unconditional.
-/

@[expose] public section

open Real Finset MeasureTheory Polynomial
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap.Integrality
open FormalResearch.ModularBootstrap.Duality

/-- Conclusion of `int:cheb2d` / `int:cheb2d-explicit`: finitely supported positive integer-weighted
atomic measure on `[-1, 1]²` matching all bivariate moments `x^m y^k` through bi-degree `(M, M)`. -/
def IntegerMomentMatching2D (μ : Measure (ℝ × ℝ)) (M : ℕ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (p : κ → ℝ × ℝ) (d : κ → ℕ),
    (∀ r, p r ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) ∧
    (∀ r, 1 ≤ d r) ∧
    ∀ m k : ℕ, m ≤ M → k ≤ M →
      ∫ q : ℝ × ℝ, q.1 ^ m * q.2 ^ k ∂μ = ∑ r, (d r : ℝ) * (p r).1 ^ m * (p r).2 ^ k

/-- Transfer from Chebyshev product moments `T_m(x) T_k(y)` to monomials `x^m y^k`. -/
lemma integerMomentMatching2D_of_chebyshev {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (hsupp : μ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)ᶜ = 0) {M : ℕ}
    {κ : Type} [Fintype κ] {p : κ → ℝ × ℝ} {d : κ → ℕ}
    (hp : ∀ r, p r ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) (hd : ∀ r, 1 ≤ d r)
    (hmom : ∀ m k : ℕ, m ≤ M → k ≤ M →
      ∫ q : ℝ × ℝ, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval q.1 *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval q.2 ∂μ =
      ∑ r, (d r : ℝ) * (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (p r).1 *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (p r).2) :
    IntegerMomentMatching2D μ M := by
  refine ⟨κ, inferInstance, p, d, hp, hd, fun m k hm hk => ?_⟩
  obtain ⟨am, ham⟩ := exists_chebyshev_expansion m (X ^ m) (by rw [degree_X_pow])
  obtain ⟨bk, hbk⟩ := exists_chebyshev_expansion k (X ^ k) (by rw [degree_X_pow])
  have hae : ∀ᵐ q ∂μ, q ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    have := measure_eq_zero_iff_ae_notMem.1 hsupp
    exact this.mono fun q hq => by simpa using hq
  have hint_prod : ∀ i j : ℕ, Integrable (fun q : ℝ × ℝ =>
      am i * bk j * ((Polynomial.Chebyshev.T ℝ (i : ℤ)).eval q.1 *
        (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval q.2)) μ := fun i j => by
    have hcont : Continuous (fun q : ℝ × ℝ => am i * bk j *
        ((Polynomial.Chebyshev.T ℝ (i : ℤ)).eval q.1 *
          (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval q.2)) := by
      have hc1 : Continuous (fun x : ℝ => (Polynomial.Chebyshev.T ℝ (i : ℤ)).eval x) :=
        (Polynomial.Chebyshev.T ℝ (i : ℤ)).continuous
      have hc2 : Continuous (fun y : ℝ => (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval y) :=
        (Polynomial.Chebyshev.T ℝ (j : ℤ)).continuous
      exact continuous_const.mul ((hc1.comp continuous_fst).mul (hc2.comp continuous_snd))
    have h1 : IntegrableOn _ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) μ :=
      hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h1
  have hexp_eval : ∀ x y : ℝ, x ^ m * y ^ k =
      ∑ i ∈ range (m + 1), ∑ j ∈ range (k + 1),
        am i * bk j * ((Polynomial.Chebyshev.T ℝ (i : ℤ)).eval x *
          (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval y) := fun x y => by
    have hx : x ^ m = ∑ i ∈ range (m + 1), am i * (Polynomial.Chebyshev.T ℝ (i : ℤ)).eval x := by
      have := congrArg (fun P : ℝ[X] => P.eval x) ham
      simpa [eval_finsetSum, eval_mul, eval_C] using this
    have hy : y ^ k = ∑ j ∈ range (k + 1), bk j * (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval y := by
      have := congrArg (fun P : ℝ[X] => P.eval y) hbk
      simpa [eval_finsetSum, eval_mul, eval_C] using this
    rw [hx, hy, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ => by ring
  have h1 : ∫ q : ℝ × ℝ, q.1 ^ m * q.2 ^ k ∂μ =
      ∑ i ∈ range (m + 1), ∑ j ∈ range (k + 1), am i * bk j *
        ∫ q : ℝ × ℝ, (Polynomial.Chebyshev.T ℝ (i : ℤ)).eval q.1 *
          (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval q.2 ∂μ := by
    simp_rw [hexp_eval]
    rw [integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hint_prod i j]
    refine sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hint_prod i j]
    refine sum_congr rfl fun j _ => by rw [integral_const_mul]
  rw [h1]
  have h2 : ∑ r, (d r : ℝ) * (p r).1 ^ m * (p r).2 ^ k =
      ∑ i ∈ range (m + 1), ∑ j ∈ range (k + 1), am i * bk j *
        (∑ r, (d r : ℝ) * (Polynomial.Chebyshev.T ℝ (i : ℤ)).eval (p r).1 *
          (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (p r).2) := by
    calc ∑ r, (d r : ℝ) * (p r).1 ^ m * (p r).2 ^ k
        = ∑ r, ∑ i ∈ range (m + 1), ∑ j ∈ range (k + 1),
            (d r : ℝ) * (am i * bk j * ((Polynomial.Chebyshev.T ℝ (i : ℤ)).eval (p r).1 *
              (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (p r).2)) := by
          refine sum_congr rfl fun r _ => ?_
          rw [mul_assoc (d r : ℝ), hexp_eval (p r).1 (p r).2, mul_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [mul_sum]
      _ = ∑ i ∈ range (m + 1), ∑ r, ∑ j ∈ range (k + 1),
            (d r : ℝ) * (am i * bk j * ((Polynomial.Chebyshev.T ℝ (i : ℤ)).eval (p r).1 *
              (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (p r).2)) := sum_comm
      _ = ∑ i ∈ range (m + 1), ∑ j ∈ range (k + 1), ∑ r,
            (d r : ℝ) * (am i * bk j * ((Polynomial.Chebyshev.T ℝ (i : ℤ)).eval (p r).1 *
              (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (p r).2)) :=
          sum_congr rfl fun _ _ => sum_comm
      _ = ∑ i ∈ range (m + 1), ∑ j ∈ range (k + 1), am i * bk j *
            (∑ r, (d r : ℝ) * (Polynomial.Chebyshev.T ℝ (i : ℤ)).eval (p r).1 *
              (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (p r).2) := by
          refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun r _ => by ring
  rw [h2]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  rw [hmom i j (by have := mem_range.1 hi; omega) (by have := mem_range.1 hj; omega)]

private lemma integrable_chebProd_of_supp {ν : Measure (ℝ × ℝ)} [IsFiniteMeasure ν]
    (hsupp : ν (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)ᶜ = 0) (m k : ℕ) :
    Integrable (fun q : ℝ × ℝ => (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval q.1 *
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval q.2) ν := by
  have hae : ∀ᵐ q ∂ν, q ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    have := measure_eq_zero_iff_ae_notMem.1 hsupp
    exact this.mono fun q hq => by simpa using hq
  have hc : Continuous (fun q : ℝ × ℝ => (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval q.1 *
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval q.2) :=
    ((Polynomial.Chebyshev.T ℝ (m : ℤ)).continuous.comp continuous_fst).mul
      ((Polynomial.Chebyshev.T ℝ (k : ℤ)).continuous.comp continuous_snd)
  have h1 : IntegrableOn _ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) ν :=
    hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h1

private lemma exists_atomic_chebyshev_2d {ν : Measure (ℝ × ℝ)} [IsFiniteMeasure ν]
    (hsupp : ν (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)ᶜ = 0) (M : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (α β ρ : ι → ℝ),
      Fintype.card ι ≤ (M + 1) ^ 2 ∧
      (∀ i, α i ∈ Set.Icc (0 : ℝ) π) ∧ (∀ i, β i ∈ Set.Icc (0 : ℝ) π) ∧
      (∀ i, 0 < ρ i) ∧ ∑ i, ρ i = ν.real Set.univ ∧
      ∀ m k : ℕ, m ≤ M → k ≤ M →
        ∑ i, ρ i * cos ((m : ℝ) * α i) * cos ((k : ℝ) * β i) =
          ∫ q : ℝ × ℝ, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval q.1 *
            (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval q.2 ∂ν := by
  by_cases hν : ν = 0
  · refine ⟨Empty, inferInstance, fun _ => 0, fun _ => 0, fun _ => 1,
      by simp, by simp, by simp, by simp, by simp [hν], fun m k _ _ => ?_⟩
    simp [hν]
  have hpos : 0 < ν Set.univ := by
    rw [pos_iff_ne_zero]; intro h; exact hν (Measure.measure_univ_eq_zero.1 h)
  have hfin : ν Set.univ ≠ ∞ := measure_ne_top ν _
  set mass : ℝ := ν.real Set.univ
  have hmass0 : 0 < mass := ENNReal.toReal_pos hpos.ne' hfin
  let P : Measure (ℝ × ℝ) := (ν Set.univ)⁻¹ • ν
  have hP : IsProbabilityMeasure P := ⟨by simp [P, ENNReal.inv_mul_cancel hpos.ne' hfin]⟩
  let Idx := {mk : Fin (M + 1) × Fin (M + 1) // mk ≠ (0, 0)}
  let Φ : ℝ × ℝ → (Idx → ℝ) := fun q mk =>
    (Polynomial.Chebyshev.T ℝ ((mk.1.1 : ℕ) : ℤ)).eval q.1 *
      (Polynomial.Chebyshev.T ℝ ((mk.1.2 : ℕ) : ℤ)).eval q.2
  have hΦc : Continuous Φ := continuous_pi fun mk =>
    ((Polynomial.Chebyshev.T ℝ ((mk.1.1 : ℕ) : ℤ)).continuous.comp continuous_fst).mul
      ((Polynomial.Chebyshev.T ℝ ((mk.1.2 : ℕ) : ℤ)).continuous.comp continuous_snd)
  let R2 : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1
  let K : Set (Idx → ℝ) := Φ '' R2
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image hΦc
  have hhull : IsCompact (convexHull ℝ K) := isCompact_convexHull_of_isCompact hK
  have hPsupp : P R2ᶜ = 0 := by
    show ((ν Set.univ)⁻¹ • ν) R2ᶜ = 0
    rw [smul_apply, show R2 = Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 from rfl, hsupp, smul_zero]
  have hae : ∀ᵐ q ∂P, q ∈ R2 := by
    have := measure_eq_zero_iff_ae_notMem.1 hPsupp
    exact this.mono fun q hq => by simpa using hq
  have hΦint : Integrable Φ P := by
    have h1 : IntegrableOn Φ R2 P := hΦc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h1
  have hmem : (∫ q, Φ q ∂P) ∈ convexHull ℝ K := by
    refine Convex.integral_mem (convex_convexHull ℝ K) hhull.isClosed ?_ hΦint
    exact hae.mono fun q hq => subset_convexHull ℝ K ⟨q, hq, rfl⟩
  obtain ⟨ι, hι, z, w, hzK, hw, hw1, hwz, hcard⟩ := exists_caratheodory hmem
  choose q hqI hqz using fun i => hzK (Set.mem_range_self i)
  have hcard_le : Fintype.card ι ≤ (M + 1) ^ 2 := by
    have hfr : Module.finrank ℝ (Idx → ℝ) = Fintype.card Idx := Module.finrank_pi (R := ℝ)
    have hsub := Fintype.card_subtype_compl (fun mk : Fin (M + 1) × Fin (M + 1) => mk = (0, 0))
    have h0 : Fintype.card {mk : Fin (M + 1) × Fin (M + 1) // mk = (0, 0)} = 1 := by simp
    have htot : Fintype.card (Fin (M + 1) × Fin (M + 1)) = (M + 1) ^ 2 := by
      rw [Fintype.card_prod, Fintype.card_fin]; ring
    have hidx : Fintype.card Idx = Fintype.card {mk : Fin (M + 1) × Fin (M + 1) // ¬ mk = (0, 0)} := rfl
    have hle_tot : Fintype.card {mk : Fin (M + 1) × Fin (M + 1) // ¬ mk = (0, 0)} + 1 = (M + 1) ^ 2 := by
      have hpos : 0 < (M + 1) ^ 2 := by positivity
      have : Fintype.card {mk : Fin (M + 1) × Fin (M + 1) // ¬ mk = (0, 0)} ≤ (M + 1) ^ 2 := by omega
      have : 1 ≤ (M + 1) ^ 2 := hpos
      rw [hsub, htot, h0]
      omega
    omega
  refine ⟨ι, hι, fun i => arccos (q i).1, fun i => arccos (q i).2, fun i => mass * w i,
    hcard_le, fun i => ⟨arccos_nonneg _, arccos_le_pi _⟩,
    fun i => ⟨arccos_nonneg _, arccos_le_pi _⟩, fun i => mul_pos hmass0 (hw i), ?_, ?_⟩
  · rw [← mul_sum, hw1, mul_one]
  · intro m k hm hk
    by_cases hmk : (m, k) = (0, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmk
      simp only [Nat.cast_zero, zero_mul, cos_zero, mul_one, Polynomial.Chebyshev.T_zero, eval_one]
      rw [← mul_sum, hw1, mul_one, integral_const, smul_eq_mul, mul_one]
    · have hi0 : (⟨⟨m, by omega⟩, ⟨k, by omega⟩⟩ : Fin (M + 1) × Fin (M + 1)) ≠ (0, 0) := by
        intro h; apply hmk
        have h1 := congrArg Fin.val (congrArg Prod.fst h)
        have h2 := congrArg Fin.val (congrArg Prod.snd h)
        exact Prod.ext h1 h2
      set idx : Idx := ⟨(⟨m, by omega⟩, ⟨k, by omega⟩), hi0⟩
      have hcomp := congrFun hwz idx
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcomp
      have hint : (∫ q, Φ q ∂P) idx = (ν Set.univ)⁻¹.toReal *
          ∫ q : ℝ × ℝ, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval q.1 *
            (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval q.2 ∂ν := by
        have h1 : (∫ q, Φ q ∂P) idx = ∫ q, Φ q idx ∂P :=
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Idx => ℝ) idx).integral_comp_comm
            hΦint).symm
        rw [h1]
        simp only [Φ, idx]
        rw [integral_smul_measure, smul_eq_mul]
      rw [hint] at hcomp
      have hxm : ∀ i, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (q i).1 =
          cos ((m : ℝ) * arccos (q i).1) := fun i => by
        have := Polynomial.Chebyshev.T_real_cos (arccos (q i).1) (m : ℤ)
        rw [cos_arccos (hqI i).1.1 (hqI i).1.2] at this
        simpa using this
      have hyk : ∀ i, (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (q i).2 =
          cos ((k : ℝ) * arccos (q i).2) := fun i => by
        have := Polynomial.Chebyshev.T_real_cos (arccos (q i).2) (k : ℤ)
        rw [cos_arccos (hqI i).2.1 (hqI i).2.2] at this
        simpa using this
      have hzi : ∀ i, z i idx = cos ((m : ℝ) * arccos (q i).1) * cos ((k : ℝ) * arccos (q i).2) := fun i => by
        rw [← hqz i]
        simp only [Φ, idx, hxm i, hyk i]
      simp_rw [hzi] at hcomp
      have hmass' : ((ν Set.univ)⁻¹).toReal = mass⁻¹ := by rw [ENNReal.toReal_inv]; rfl
      rw [hmass'] at hcomp
      calc ∑ i, mass * w i * cos ((m : ℝ) * arccos (q i).1) * cos ((k : ℝ) * arccos (q i).2)
          = mass * ∑ i, w i * (cos ((m : ℝ) * arccos (q i).1) * cos ((k : ℝ) * arccos (q i).2)) := by
            rw [mul_sum]; refine sum_congr rfl fun i _ => by ring
        _ = _ := by rw [hcomp]; field_simp

private lemma sum_inv_sq_le_seven_fourths (M : ℕ) :
    ∑ i ∈ range M, (((i : ℕ) : ℝ) + 1) ^ (-2 : ℤ) ≤ 7 / 4 := by
  have hsub : ∀ n : ℕ, 2 ≤ n →
      ∑ i ∈ range n, (1 : ℝ) / (((i : ℕ) : ℝ) + 1) ^ 2 ≤ 7 / 4 - 1 / (n : ℝ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      norm_num [sum_range_succ]
    | succ k hk ih =>
      rw [sum_range_succ]
      have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
      have hstep : 1 / ((k : ℝ) + 1) ^ 2 ≤ 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
        have hk0 : (0 : ℝ) < k := by linarith only [hk2]
        have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith only [hk2]
        rw [div_sub_div _ _ hk0.ne' hk1.ne', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith only [hk2]
      push_cast
      linarith only [ih, hstep]
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · interval_cases M <;> norm_num [sum_range_succ]
  · have h1 := hsub M hM2
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have heq : ∑ i ∈ range M, (((i : ℕ) : ℝ) + 1) ^ (-2 : ℤ) =
        ∑ i ∈ range M, (1 : ℝ) / (((i : ℕ) : ℝ) + 1) ^ 2 := by
      refine sum_congr rfl fun i _ => by simp [zpow_neg, one_div]
    rw [heq]
    linarith only [h1, div_pos one_pos hM0]

/-- **Lemma INT-7B.exp (`int:cheb2d-explicit`)**: for `M ≥ 1` (`N = M + 1`), if `μ` is a finite
positive measure on `[-1, 1]^2` of integer total mass `N_tot` obeying `μ ≥ W_0 dx dy` with
`W_0 ≥ 32 N^{13/2}`, then there is a finitely supported positive integer-weighted atomic measure
on `[-1, 1]^2` matching all bivariate polynomial moments through bi-degree `(M, M)`. -/
theorem cheb2d_explicit {M : ℕ} (hM : 1 ≤ M) {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (hsupp : μ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)ᶜ = 0)
    {Ntot : ℕ} (hN : μ Set.univ = Ntot) {W0 : ℝ}
    (hW0 : 32 * ((M : ℝ) + 1) ^ 6 * Real.sqrt ((M : ℝ) + 1) ≤ W0)
    (hμ : ENNReal.ofReal W0 • volume.restrict (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) ≤ μ) :
    IntegerMomentMatching2D μ M := by
  let N : ℕ := M + 1
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNr : (N : ℝ) = (M : ℝ) + 1 := by dsimp [N]; push_cast; ring
  have hN1 : (2 : ℝ) ≤ N := by linarith only [hMr, hNr]
  have hN0 : 0 < N := by omega
  set s : ℝ := Real.sqrt (N : ℝ)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith only [hN1])
  have hss : s ^ 2 = (N : ℝ) := Real.sq_sqrt (by linarith only [hN1])
  have hW0_lb : 32 * (N : ℝ) ^ 6 * s ≤ W0 := by simpa only [← hNr, s] using hW0
  have hW0_nn : 0 ≤ W0 := le_trans (by positivity) hW0_lb
  set R : ℕ := ⌊2 * W0 / (N : ℝ) ^ 4⌋₊
  have hq : 64 * (N : ℝ) ^ 2 * s ≤ 2 * W0 / (N : ℝ) ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    have hmul : 64 * (N : ℝ) ^ 2 * s * (N : ℝ) ^ 4 = 2 * (32 * (N : ℝ) ^ 6 * s) := by ring
    linarith only [hmul, hW0_lb]
  have hRlow : 64 * (N : ℝ) ^ 2 * s - 1 ≤ (R : ℝ) := by
    have := Nat.lt_floor_add_one (2 * W0 / (N : ℝ) ^ 4)
    linarith only [this, hq]
  have hs_ge1 : 1 ≤ s := Real.one_le_sqrt.mpr (by linarith only [hN1])
  have hR_ge : (255 / 4 : ℝ) * (N : ℝ) ^ 2 * s ≤ (R : ℝ) := by
    have hns : 4 ≤ (N : ℝ) ^ 2 * s := by
      have hn2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hN1]
      nlinarith only [hn2, hs_ge1]
    linarith only [hRlow, hns]
  have hR1 : 1 ≤ R := by
    have : (1 : ℝ) ≤ (R : ℝ) := by
      have : 1 ≤ (255 / 4 : ℝ) * (N : ℝ) ^ 2 * s := by
        have hn2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hN1]
        nlinarith only [hn2, hs_ge1]
      linarith only [this, hR_ge]
    exact_mod_cast this
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR1
  have hRle : (R : ℝ) ≤ 2 * W0 / (N : ℝ) ^ 4 := Nat.floor_le (by positivity)
  set R2 : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1
  set F : Measure (ℝ × ℝ) := ENNReal.ofReal W0 • volume.restrict R2
  have hR2_vol : volume R2 = 4 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
    norm_num
  have : IsFiniteMeasure (volume.restrict R2) := ⟨by rw [Measure.restrict_apply_univ, hR2_vol]; norm_num⟩
  have : IsFiniteMeasure F := Measure.smul_finite _ ENNReal.ofReal_ne_top
  set ν : Measure (ℝ × ℝ) := μ - F
  have hνF : ν + F = μ := Measure.sub_add_cancel_of_le hμ
  have : IsFiniteMeasure ν :=
    ⟨lt_of_le_of_lt (Measure.sub_le (μ := μ) (ν := F) Set.univ) (measure_lt_top μ _)⟩
  have hνsupp : ν R2ᶜ = 0 := le_antisymm ((Measure.sub_le (μ := μ) (ν := F) R2ᶜ).trans hsupp.le) bot_le
  have hFsupp : F R2ᶜ = 0 := by
    have : (volume.restrict R2) R2ᶜ = 0 := by
      rw [Measure.restrict_apply (isClosed_Icc.prod isClosed_Icc).isOpen_compl.measurableSet,
        Set.compl_inter_self, measure_empty]
    simp [F, this]
  have hF_moments : ∀ m k : ℕ,
      ∫ q : ℝ × ℝ, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval q.1 *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval q.2 ∂F =
      W0 * (chebInt m * chebInt k) := fun m k => by
    rw [integral_smul_measure, ENNReal.toReal_ofReal hW0_nn, smul_eq_mul]
    congr 1
    rw [Measure.volume_eq_prod, show R2 = Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 from rfl,
      ← Measure.prod_restrict]
    rw [integral_prod_mul (f := fun x => (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x)
      (g := fun y => (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval y)]
    rw [← integral_chebyshevT m, ← integral_chebyshevT k,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  have hmom : ∀ m k : ℕ,
      ∫ q : ℝ × ℝ, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval q.1 *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval q.2 ∂μ =
      ∫ q : ℝ × ℝ, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval q.1 *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval q.2 ∂ν + W0 * (chebInt m * chebInt k) := fun m k => by
    rw [← hνF, integral_add_measure (integrable_chebProd_of_supp hνsupp m k)
      (integrable_chebProd_of_supp hFsupp m k), hF_moments m k]
  have hmass : (Ntot : ℝ) = ν.real Set.univ + 4 * W0 := by
    have h1 : μ Set.univ = ν Set.univ + F Set.univ := by rw [← hνF]; rfl
    have h2 : F Set.univ = ENNReal.ofReal (4 * W0) := by
      simp only [F, smul_apply, Measure.restrict_apply_univ, hR2_vol, smul_eq_mul]
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul hW0_nn,
        mul_comm W0 4]
    have h3 : (μ Set.univ).toReal = (ν Set.univ).toReal + (F Set.univ).toReal := by
      rw [h1, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    rw [h2, ENNReal.toReal_ofReal (by positivity), hN] at h3
    simpa [Measure.real] using h3
  obtain ⟨ι, hι, α, β, ρ, hcard_ι, hα, hβ, hρ, hρsum, hρmom⟩ := exists_atomic_chebyshev_2d hνsupp M
  have hfejer : ∀ m : ℕ, m ≤ M →
      ∑ j : Fin N, fejerWeight N (M / 2) j.1 * cos ((m : ℝ) * midAngle N j.1) = chebInt m := by
    intro m hm
    rw [Fin.sum_univ_eq_sum_range (fun j => fejerWeight N (M / 2) j * cos ((m : ℝ) * midAngle N j)) N]
    exact fejerWeight_cos_sum hN0 (by dsimp [N]; omega) hm
  have hlam : ∀ j : ℕ, 2 / (N : ℝ) ^ 2 ≤ fejerWeight N (M / 2) j := fun j =>
    fejerWeight_ge_sq hN0 (by dsimp [N]; omega) j
  let Γ := (Fin N × Fin N) ⊕ (Fin N × Fin N) ⊕ ι
  let θL : Γ → ℝ := Sum.elim (fun ij => midAngle N ij.1.1)
    (Sum.elim (fun ij => midAngle N ij.1.1) α)
  let θR : Γ → ℝ := Sum.elim (fun ij => midAngle N ij.2.1)
    (Sum.elim (fun ij => midAngle N ij.2.1) β)
  let w : Γ → ℝ := Sum.elim (fun ij => (W0 / 2) * fejerWeight N (M / 2) ij.1.1 * fejerWeight N (M / 2) ij.2.1)
    (Sum.elim (fun ij => (W0 / 2) * fejerWeight N (M / 2) ij.1.1 * fejerWeight N (M / 2) ij.2.1) ρ)
  have hw_nn : ∀ g : Γ, 0 ≤ w g := by
    rintro (ij | (ij | i))
    · exact mul_nonneg (mul_nonneg (by positivity) (le_trans (by positivity) (hlam ij.1.1)))
        (le_trans (by positivity) (hlam ij.2.1))
    · exact mul_nonneg (mul_nonneg (by positivity) (le_trans (by positivity) (hlam ij.1.1)))
        (le_trans (by positivity) (hlam ij.2.1))
    · exact (hρ i).le
  have hgrid_lb : ∀ ij : Fin N × Fin N,
      (R : ℝ) ≤ (W0 / 2) * fejerWeight N (M / 2) ij.1.1 * fejerWeight N (M / 2) ij.2.1 := fun ij => by
    have h1 : 2 / (N : ℝ) ^ 2 ≤ fejerWeight N (M / 2) ij.1.1 := hlam _
    have h2 : 2 / (N : ℝ) ^ 2 ≤ fejerWeight N (M / 2) ij.2.1 := hlam _
    have hprod : 4 / (N : ℝ) ^ 4 ≤ fejerWeight N (M / 2) ij.1.1 * fejerWeight N (M / 2) ij.2.1 := by
      have h1_nn : 0 ≤ (2 / (N : ℝ) ^ 2 : ℝ) := by positivity
      calc 4 / (N : ℝ) ^ 4 = (2 / (N : ℝ) ^ 2) * (2 / (N : ℝ) ^ 2) := by ring
        _ ≤ _ := mul_le_mul h1 h2 h1_nn (h1_nn.trans h1)
    calc (R : ℝ) ≤ 2 * W0 / (N : ℝ) ^ 4 := hRle
      _ = (W0 / 2) * (4 / (N : ℝ) ^ 4) := by ring
      _ ≤ (W0 / 2) * (fejerWeight N (M / 2) ij.1.1 * fejerWeight N (M / 2) ij.2.1) := by
          exact mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = (W0 / 2) * fejerWeight N (M / 2) ij.1.1 * fejerWeight N (M / 2) ij.2.1 := by ring
  have hw_mom : ∀ m k : ℕ, m ≤ M → k ≤ M →
      ∑ g : Γ, w g * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g) =
        ∫ q : ℝ × ℝ, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval q.1 *
          (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval q.2 ∂μ := fun m k hm hk => by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [w, θL, θR, Sum.elim_inl, Sum.elim_inr]
    have hprod_sum :
        ∑ ij : Fin N × Fin N,
          (W0 / 2) * fejerWeight N (M / 2) ij.1.1 * fejerWeight N (M / 2) ij.2.1 *
            cos ((m : ℝ) * midAngle N ij.1.1) * cos ((k : ℝ) * midAngle N ij.2.1) =
        (W0 / 2) * (chebInt m * chebInt k) := by
      rw [Fintype.sum_prod_type]
      calc ∑ i : Fin N, ∑ j : Fin N,
            (W0 / 2) * fejerWeight N (M / 2) i.1 * fejerWeight N (M / 2) j.1 *
              cos ((m : ℝ) * midAngle N i.1) * cos ((k : ℝ) * midAngle N j.1)
          = (W0 / 2) * ∑ i : Fin N, ∑ j : Fin N,
              (fejerWeight N (M / 2) i.1 * cos ((m : ℝ) * midAngle N i.1)) *
                (fejerWeight N (M / 2) j.1 * cos ((k : ℝ) * midAngle N j.1)) := by
            rw [mul_sum]
            refine sum_congr rfl fun i _ => ?_
            rw [mul_sum]
            refine sum_congr rfl fun j _ => by ring
        _ = (W0 / 2) * ((∑ i : Fin N, fejerWeight N (M / 2) i.1 * cos ((m : ℝ) * midAngle N i.1)) *
              (∑ j : Fin N, fejerWeight N (M / 2) j.1 * cos ((k : ℝ) * midAngle N j.1))) := by
            rw [sum_mul_sum]
        _ = (W0 / 2) * (chebInt m * chebInt k) := by rw [hfejer m hm, hfejer k hk]
    rw [hprod_sum, hρmom m k hm hk, hmom m k]
    ring
  have hsum_w : ∑ g : Γ, w g = (Ntot : ℝ) := by
    have h00 := hw_mom 0 0 (Nat.zero_le _) (Nat.zero_le _)
    simp only [Nat.cast_zero, zero_mul, cos_zero, mul_one, Polynomial.Chebyshev.T_zero, eval_one,
      integral_const, smul_eq_mul] at h00
    simpa [Measure.real, hN] using h00
  let t : Γ → ℕ := fun g => ⌊w g⌋₊
  have ht_le : ∀ g : Γ, (t g : ℝ) ≤ w g := fun g => Nat.floor_le (hw_nn g)
  have ht_lt : ∀ g : Γ, w g - (t g : ℝ) < 1 := fun g => by
    have := Nat.lt_floor_add_one (w g)
    linarith only [this]
  have ht_sum_le : ∑ g : Γ, t g ≤ Ntot := by
    have hle : (∑ g : Γ, (t g : ℝ)) ≤ (Ntot : ℝ) := by
      rw [← hsum_w]
      exact sum_le_sum fun g _ => ht_le g
    exact_mod_cast hle
  let D0 : ℕ := Ntot - ∑ g : Γ, t g
  have hD0_eq : (D0 : ℝ) = ∑ g : Γ, (w g - (t g : ℝ)) := by
    rw [Nat.cast_sub ht_sum_le, sum_sub_distrib, hsum_w]; push_cast; rfl
  have hcard_Γ : Fintype.card Γ ≤ 3 * N ^ 2 := by
    dsimp [Γ]
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ← sq]
    dsimp only [N] at hcard_ι ⊢
    omega
  have hD0_lt : (D0 : ℝ) ≤ 3 * (N : ℝ) ^ 2 := by
    rw [hD0_eq]
    calc ∑ g : Γ, (w g - (t g : ℝ)) ≤ ∑ _g : Γ, (1 : ℝ) :=
          sum_le_sum fun g _ => (ht_lt g).le
      _ = (Fintype.card Γ : ℝ) := by simp
      _ ≤ 3 * (N : ℝ) ^ 2 := by exact_mod_cast hcard_Γ
  let Δ : ℕ → ℕ → ℝ := fun m k =>
    (∑ g : Γ, (w g - (t g : ℝ)) * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g)) -
      (D0 : ℝ) * cos ((m : ℝ) * (π / 2)) * cos ((k : ℝ) * (π / 2))
  have hΔ00 : Δ 0 0 = 0 := by
    simp only [Δ, Nat.cast_zero, zero_mul, cos_zero, mul_one, ← hD0_eq, sub_self]
  have hΔ_bd : ∀ m k : ℕ, |Δ m k| ≤ 6 * (N : ℝ) ^ 2 := fun m k => by
    have h1 : |∑ g : Γ, (w g - (t g : ℝ)) * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g)| ≤ (D0 : ℝ) := by
      calc |∑ g : Γ, (w g - (t g : ℝ)) * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g)|
          ≤ ∑ g : Γ, |(w g - (t g : ℝ)) * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g)| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ g : Γ, (w g - (t g : ℝ)) := by
            refine sum_le_sum fun g _ => ?_
            have hnn : 0 ≤ w g - (t g : ℝ) := sub_nonneg.mpr (ht_le g)
            rw [abs_mul, abs_mul, abs_of_nonneg hnn]
            calc (w g - (t g : ℝ)) * |cos ((m : ℝ) * θL g)| * |cos ((k : ℝ) * θR g)|
                ≤ (w g - (t g : ℝ)) * 1 * 1 :=
                  mul_le_mul (mul_le_mul_of_nonneg_left (abs_cos_le_one _) hnn) (abs_cos_le_one _)
                    (abs_nonneg _) (mul_nonneg hnn zero_le_one)
              _ = w g - (t g : ℝ) := by ring
        _ = (D0 : ℝ) := hD0_eq.symm
    have h2 : |(D0 : ℝ) * cos ((m : ℝ) * (π / 2)) * cos ((k : ℝ) * (π / 2))| ≤ (D0 : ℝ) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg D0)]
      calc (D0 : ℝ) * |cos ((m : ℝ) * (π / 2))| * |cos ((k : ℝ) * (π / 2))|
          ≤ (D0 : ℝ) * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left (abs_cos_le_one _) (Nat.cast_nonneg _))
              (abs_cos_le_one _) (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) zero_le_one)
        _ = (D0 : ℝ) := by ring
    exact (abs_sub _ _).trans (by linarith only [h1, h2, hD0_lt])
  have hgridA : ∀ ij : Fin N × Fin N, R ≤ t (Sum.inl ij) := fun ij =>
    Nat.le_floor (hgrid_lb ij)
  have hgridB : ∀ ij : Fin N × Fin N, R ≤ t (Sum.inr (Sum.inl ij)) := fun ij =>
    Nat.le_floor (hgrid_lb ij)
  -- Stage 1: common `y`-shift on Grid A correcting `(0, k)` for `1 ≤ k ≤ M`
  let vY : Fin M → ℝ := fun k => Δ 0 ((k : ℕ) + 1) / ((N : ℝ) * (R : ℝ))
  have hvY_bd : (2 / ((M : ℝ) + 1)) * ∑ k : Fin M, (vY k / (((k : ℕ) : ℝ) + 1)) ^ 2 ≤
      1 / (16 * (M : ℝ) ^ 2) := by
    have hsum_bd : ∑ k : Fin M, (vY k / (((k : ℕ) : ℝ) + 1)) ^ 2 ≤
        ((6 * (N : ℝ) ^ 2 / ((N : ℝ) * (R : ℝ))) ^ 2) * (7 / 4 : ℝ) := by
      calc ∑ k : Fin M, (vY k / (((k : ℕ) : ℝ) + 1)) ^ 2
          = ∑ k : Fin M, (Δ 0 ((k : ℕ) + 1) / ((N : ℝ) * (R : ℝ))) ^ 2 *
              ((((k : ℕ) : ℝ) + 1) ^ (-2 : ℤ)) := by
            refine sum_congr rfl fun k _ => by simp [vY, div_pow, zpow_neg]; ring
        _ ≤ ∑ k : Fin M, (6 * (N : ℝ) ^ 2 / ((N : ℝ) * (R : ℝ))) ^ 2 *
              ((((k : ℕ) : ℝ) + 1) ^ (-2 : ℤ)) := by
            refine sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [← sq_abs (Δ 0 _ / _), abs_div, abs_of_pos (mul_pos (by positivity) hRpos)]
            exact pow_le_pow_left₀ (by positivity)
              (div_le_div_of_nonneg_right (hΔ_bd 0 _) (by positivity)) 2
        _ = (6 * (N : ℝ) ^ 2 / ((N : ℝ) * (R : ℝ))) ^ 2 *
              ∑ k ∈ range M, (((k : ℕ) : ℝ) + 1) ^ (-2 : ℤ) := by
            rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun k : ℕ => (((k : ℕ) : ℝ) + 1) ^ (-2 : ℤ)) M]
        _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_sq_le_seven_fourths M) (sq_nonneg _)
    have hnum_le : (2 / (N : ℝ)) * ((6 * (N : ℝ) ^ 2 / ((N : ℝ) * (R : ℝ))) ^ 2 * (7 / 4 : ℝ)) ≤
        1 / (16 * (M : ℝ) ^ 2) := by
      have hsimp : (2 / (N : ℝ)) * ((6 * (N : ℝ) ^ 2 / ((N : ℝ) * (R : ℝ))) ^ 2 * (7 / 4 : ℝ)) =
          126 * (N : ℝ) / (R : ℝ) ^ 2 := by field_simp; ring
      rw [hsimp, div_le_div_iff₀ (sq_pos_of_pos hRpos) (by positivity)]
      have hMN : (M : ℝ) ≤ (N : ℝ) := by linarith only [hNr]
      have hs2 : 1 ≤ s ^ 2 := by rw [hss]; linarith only [hN1]
      have hR2 : (255 / 4 : ℝ) ^ 2 * (N : ℝ) ^ 5 ≤ (R : ℝ) ^ 2 := by
        calc (255 / 4 : ℝ) ^ 2 * (N : ℝ) ^ 5 = ((255 / 4 : ℝ) * (N : ℝ) ^ 2 * s) ^ 2 := by
              rw [mul_pow, mul_pow, ← pow_mul, hss]; ring
          _ ≤ (R : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hR_ge 2
      have hM2 : (M : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hMN 2
      have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hN1]
      calc 126 * (N : ℝ) * (16 * (M : ℝ) ^ 2)
          ≤ 126 * (N : ℝ) * (16 * (N : ℝ) ^ 2) := by gcongr
        _ = 2016 * (N : ℝ) ^ 3 * 1 := by ring
        _ ≤ 2016 * (N : ℝ) ^ 3 * (N : ℝ) ^ 2 := by gcongr
        _ = 2016 * (N : ℝ) ^ 5 := by ring
        _ ≤ (255 / 4 : ℝ) ^ 2 * (N : ℝ) ^ 5 :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ ≤ 1 * (R : ℝ) ^ 2 := by rw [one_mul]; exact hR2
    rw [← hNr]
    exact (mul_le_mul_of_nonneg_left hsum_bd (by positivity)).trans hnum_le
  obtain ⟨zY, -, hzY⟩ := exists_angleShift hM vY hvY_bd
  -- Stage 2: row-wise `x`-shifts on Grid B correcting `(m, k)` for `1 ≤ m ≤ M, 0 ≤ k ≤ M`
  let dTarget : Fin N → Fin M → ℝ := fun j m =>
    Δ ((m : ℕ) + 1) 0 / (N : ℝ) +
      (2 / (N : ℝ)) * ∑ k : Fin M, Δ ((m : ℕ) + 1) ((k : ℕ) + 1) *
        cos ((((k : ℕ) : ℝ) + 1) * midAngle N j.1)
  have hd_orth : ∀ (m : Fin M) (k : ℕ), k ≤ M →
      ∑ j : Fin N, dTarget j m * cos ((k : ℝ) * midAngle N j.1) = Δ ((m : ℕ) + 1) k := by
    intro m k hk
    have hsum_j : ∀ a b : ℕ, a < N → b < N →
        ∑ j : Fin N, cos ((a : ℝ) * midAngle N j.1) * cos ((b : ℝ) * midAngle N j.1) =
          if a = b then (if a = 0 then (N : ℝ) else (N : ℝ) / 2) else 0 := fun a b ha hb => by
      rw [Fin.sum_univ_eq_sum_range (fun j => cos ((a : ℝ) * midAngle N j) * cos ((b : ℝ) * midAngle N j)) N]
      exact sum_cos_mul_cos hN0 ha hb
    have expand : ∑ j : Fin N, dTarget j m * cos ((k : ℝ) * midAngle N j.1) =
        (Δ ((m : ℕ) + 1) 0 / (N : ℝ)) * (∑ j : Fin N, cos (0 * midAngle N j.1) * cos ((k : ℝ) * midAngle N j.1)) +
        (2 / (N : ℝ)) * ∑ l : Fin M, Δ ((m : ℕ) + 1) ((l : ℕ) + 1) *
          ∑ j : Fin N, cos ((((l : ℕ) : ℝ) + 1) * midAngle N j.1) * cos ((k : ℝ) * midAngle N j.1) := by
      have h_term : ∀ j : Fin N, dTarget j m * cos ((k : ℝ) * midAngle N j.1) =
          (Δ ((m : ℕ) + 1) 0 / (N : ℝ)) * cos ((k : ℝ) * midAngle N j.1) +
          (2 / (N : ℝ) * ∑ l : Fin M, Δ ((m : ℕ) + 1) ((l : ℕ) + 1) *
            cos ((((l : ℕ) : ℝ) + 1) * midAngle N j.1)) * cos ((k : ℝ) * midAngle N j.1) :=
        fun j => _root_.add_mul _ _ _
      simp_rw [h_term, sum_add_distrib]
      congr 1
      · rw [mul_sum]
        refine sum_congr rfl fun j _ => by simp only [zero_mul, cos_zero, one_mul]
      · have h1 : (∑ j : Fin N, (2 / (N : ℝ) * ∑ l : Fin M, Δ ((m : ℕ) + 1) ((l : ℕ) + 1) *
              cos ((((l : ℕ) : ℝ) + 1) * midAngle N j.1)) * cos ((k : ℝ) * midAngle N j.1)) =
            ∑ j : Fin N, ∑ l : Fin M, (2 / (N : ℝ) * Δ ((m : ℕ) + 1) ((l : ℕ) + 1)) *
              (cos ((((l : ℕ) : ℝ) + 1) * midAngle N j.1) * cos ((k : ℝ) * midAngle N j.1)) := by
          refine sum_congr rfl fun j _ => ?_
          calc (2 / (N : ℝ) * ∑ l : Fin M, Δ ((m : ℕ) + 1) ((l : ℕ) + 1) *
                  cos ((((l : ℕ) : ℝ) + 1) * midAngle N j.1)) * cos ((k : ℝ) * midAngle N j.1)
              = (∑ l : Fin M, 2 / (N : ℝ) * (Δ ((m : ℕ) + 1) ((l : ℕ) + 1) *
                  cos ((((l : ℕ) : ℝ) + 1) * midAngle N j.1))) * cos ((k : ℝ) * midAngle N j.1) := by
                rw [mul_sum]
            _ = ∑ l : Fin M, 2 / (N : ℝ) * (Δ ((m : ℕ) + 1) ((l : ℕ) + 1) *
                  cos ((((l : ℕ) : ℝ) + 1) * midAngle N j.1)) * cos ((k : ℝ) * midAngle N j.1) :=
                sum_mul _ _ _
            _ = ∑ l : Fin M, (2 / (N : ℝ) * Δ ((m : ℕ) + 1) ((l : ℕ) + 1)) *
                  (cos ((((l : ℕ) : ℝ) + 1) * midAngle N j.1) * cos ((k : ℝ) * midAngle N j.1)) :=
                sum_congr rfl fun l _ => by ring
        rw [h1, sum_comm]
        rw [mul_sum]
        refine sum_congr rfl fun l _ => ?_
        rw [← mul_sum, mul_assoc]
    rw [expand]
    by_cases hk0 : k = 0
    · subst hk0
      have h00 := hsum_j 0 0 hN0 hN0
      simp only [↓reduceIte, Nat.cast_zero] at h00
      have hhl : ∀ l : Fin M,
          ∑ j : Fin N, cos ((((l : ℕ) : ℝ) + 1) * midAngle N j.1) * cos ((0 : ℝ) * midAngle N j.1) = 0 :=
        fun l => by
          have := hsum_j ((l : ℕ) + 1) 0 (by dsimp [N]; omega) hN0
          simpa using this
      simp only [Nat.cast_zero, hhl, mul_zero, sum_const_zero, add_zero]
      rw [h00]
      field_simp
    · have hk_pos : 1 ≤ k := Nat.pos_of_ne_zero hk0
      have h0k := hsum_j 0 k hN0 (by dsimp [N]; omega)
      simp only [show (0 : ℕ) ≠ k by omega, ↓reduceIte] at h0k
      have hlk : ∀ l : Fin M,
          ∑ j : Fin N, cos ((((l : ℕ) : ℝ) + 1) * midAngle N j.1) * cos ((k : ℝ) * midAngle N j.1) =
            if (l : ℕ) + 1 = k then (N : ℝ) / 2 else 0 := fun l => by
        have := hsum_j ((l : ℕ) + 1) k (by dsimp [N]; omega) (by dsimp [N]; omega)
        push_cast at this
        simpa [Nat.succ_ne_zero] using this
      simp only [Nat.cast_zero] at h0k
      simp only [h0k, mul_zero, zero_add, hlk]
      let k0 : Fin M := ⟨k - 1, by dsimp only [N] at *; omega⟩
      have hsingle : ∑ l : Fin M, Δ ((m : ℕ) + 1) ((l : ℕ) + 1) *
            (if (l : ℕ) + 1 = k then (N : ℝ) / 2 else 0) =
          Δ ((m : ℕ) + 1) k * ((N : ℝ) / 2) := by
        rw [Finset.sum_eq_single k0]
        · have hk_eq : (k0 : ℕ) + 1 = k := by simp [k0]; omega
          simp [hk_eq]
        · intro l _ hl
          have hne_val : (l : ℕ) ≠ (k0 : ℕ) := fun h => hl (Fin.ext h)
          have hk_eq : (k0 : ℕ) + 1 = k := by simp [k0]; omega
          have hne : (l : ℕ) + 1 ≠ k := by omega
          simp [hne]
        · intro hkmem; exact absurd (mem_univ k0) hkmem
      rw [hsingle]
      field_simp
  have hd_sq_bd : ∀ (j : Fin N) (m : Fin M), dTarget j m ^ 2 ≤ 72 * (N : ℝ) ^ 4 := fun j m => by
    have hparseval : ∑ j' : Fin N, dTarget j' m ^ 2 =
        Δ ((m : ℕ) + 1) 0 ^ 2 / (N : ℝ) +
          (2 / (N : ℝ)) * ∑ k : Fin M, Δ ((m : ℕ) + 1) ((k : ℕ) + 1) ^ 2 := by
      have hsq : ∀ j' : Fin N, dTarget j' m ^ 2 =
          dTarget j' m * (Δ ((m : ℕ) + 1) 0 / (N : ℝ) +
            (2 / (N : ℝ)) * ∑ k : Fin M, Δ ((m : ℕ) + 1) ((k : ℕ) + 1) *
              cos ((((k : ℕ) : ℝ) + 1) * midAngle N j'.1)) := fun j' => by rw [sq]
      simp_rw [hsq, mul_add, sum_add_distrib]
      have hpart1 : ∑ j' : Fin N, dTarget j' m * (Δ ((m : ℕ) + 1) 0 / (N : ℝ)) =
          Δ ((m : ℕ) + 1) 0 ^ 2 / (N : ℝ) := by
        have h0 := hd_orth m 0 (Nat.zero_le _)
        simp only [Nat.cast_zero, zero_mul, cos_zero, mul_one] at h0
        calc ∑ j' : Fin N, dTarget j' m * (Δ ((m : ℕ) + 1) 0 / (N : ℝ))
            = (∑ j' : Fin N, dTarget j' m) * (Δ ((m : ℕ) + 1) 0 / (N : ℝ)) := by rw [sum_mul]
          _ = Δ ((m : ℕ) + 1) 0 * (Δ ((m : ℕ) + 1) 0 / (N : ℝ)) := by rw [h0]
          _ = Δ ((m : ℕ) + 1) 0 ^ 2 / (N : ℝ) := by ring
      have hpart2 : ∑ j' : Fin N, dTarget j' m *
            ((2 / (N : ℝ)) * ∑ k : Fin M, Δ ((m : ℕ) + 1) ((k : ℕ) + 1) *
              cos ((((k : ℕ) : ℝ) + 1) * midAngle N j'.1)) =
          (2 / (N : ℝ)) * ∑ k : Fin M, Δ ((m : ℕ) + 1) ((k : ℕ) + 1) ^ 2 := by
        have hswap : ∑ j' : Fin N, dTarget j' m *
              ((2 / (N : ℝ)) * ∑ k : Fin M, Δ ((m : ℕ) + 1) ((k : ℕ) + 1) *
                cos ((((k : ℕ) : ℝ) + 1) * midAngle N j'.1)) =
            (2 / (N : ℝ)) * ∑ k : Fin M, Δ ((m : ℕ) + 1) ((k : ℕ) + 1) *
              (∑ j' : Fin N, dTarget j' m * cos ((((k : ℕ) : ℝ) + 1) * midAngle N j'.1)) := by
          rw [mul_sum]
          calc ∑ j' : Fin N, dTarget j' m * ((2 / (N : ℝ)) *
                  ∑ k : Fin M, Δ ((m : ℕ) + 1) ((k : ℕ) + 1) * cos ((((k : ℕ) : ℝ) + 1) * midAngle N j'.1))
              = ∑ j' : Fin N, ∑ k : Fin M, (2 / (N : ℝ)) *
                  (Δ ((m : ℕ) + 1) ((k : ℕ) + 1) * (dTarget j' m * cos ((((k : ℕ) : ℝ) + 1) * midAngle N j'.1))) := by
                refine sum_congr rfl fun j' _ => ?_
                rw [mul_sum, mul_sum]
                refine sum_congr rfl fun k _ => by ring
            _ = ∑ k : Fin M, ∑ j' : Fin N, (2 / (N : ℝ)) *
                  (Δ ((m : ℕ) + 1) ((k : ℕ) + 1) * (dTarget j' m * cos ((((k : ℕ) : ℝ) + 1) * midAngle N j'.1))) :=
                sum_comm
            _ = _ := by
                refine sum_congr rfl fun k _ => ?_
                rw [← mul_sum, ← mul_sum]
        rw [hswap]
        congr 1
        refine sum_congr rfl fun k _ => ?_
        have hk' := hd_orth m ((k : ℕ) + 1) (by omega)
        push_cast at hk'
        rw [hk', sq]
      rw [hpart1, hpart2]
    have hle_sum : dTarget j m ^ 2 ≤ ∑ j' : Fin N, dTarget j' m ^ 2 :=
      single_le_sum (fun j' _ => sq_nonneg (dTarget j' m)) (mem_univ j)
    have hΔsq : ∀ a b : ℕ, Δ a b ^ 2 ≤ (6 * (N : ℝ) ^ 2) ^ 2 := fun a b => by
      rw [← sq_abs (Δ a b)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hΔ_bd a b) 2
    have hsum_Δ : ∑ k : Fin M, Δ ((m : ℕ) + 1) ((k : ℕ) + 1) ^ 2 ≤ (M : ℝ) * (6 * (N : ℝ) ^ 2) ^ 2 := by
      calc ∑ k : Fin M, Δ ((m : ℕ) + 1) ((k : ℕ) + 1) ^ 2 ≤ ∑ _k : Fin M, (6 * (N : ℝ) ^ 2) ^ 2 :=
            sum_le_sum fun k _ => hΔsq _ _
        _ = (M : ℝ) * (6 * (N : ℝ) ^ 2) ^ 2 := by simp
    have hub : Δ ((m : ℕ) + 1) 0 ^ 2 / (N : ℝ) +
          (2 / (N : ℝ)) * ∑ k : Fin M, Δ ((m : ℕ) + 1) ((k : ℕ) + 1) ^ 2 ≤
        72 * (N : ℝ) ^ 4 := by
      calc Δ ((m : ℕ) + 1) 0 ^ 2 / (N : ℝ) +
            (2 / (N : ℝ)) * ∑ k : Fin M, Δ ((m : ℕ) + 1) ((k : ℕ) + 1) ^ 2
          ≤ (6 * (N : ℝ) ^ 2) ^ 2 / (N : ℝ) + (2 / (N : ℝ)) * ((M : ℝ) * (6 * (N : ℝ) ^ 2) ^ 2) :=
            add_le_add (div_le_div_of_nonneg_right (hΔsq _ 0) (by positivity))
              (mul_le_mul_of_nonneg_left hsum_Δ (by positivity))
        _ = (1 + 2 * (M : ℝ)) * 36 * (N : ℝ) ^ 3 := by field_simp; ring
        _ ≤ (2 * (N : ℝ)) * 36 * (N : ℝ) ^ 3 := by
            have h12M : 1 + 2 * (M : ℝ) ≤ 2 * (N : ℝ) := by linarith only [hNr]
            gcongr
        _ = 72 * (N : ℝ) ^ 4 := by ring
    exact hle_sum.trans (hparseval ▸ hub)
  have hvX_bd : ∀ j : Fin N,
      (2 / ((M : ℝ) + 1)) * ∑ m : Fin M, ((dTarget j m / (R : ℝ)) / (((m : ℕ) : ℝ) + 1)) ^ 2 ≤
        1 / (16 * (M : ℝ) ^ 2) := fun j => by
    have hsum_bd : ∑ m : Fin M, ((dTarget j m / (R : ℝ)) / (((m : ℕ) : ℝ) + 1)) ^ 2 ≤
        (72 * (N : ℝ) ^ 4 / (R : ℝ) ^ 2) * (7 / 4 : ℝ) := by
      calc ∑ m : Fin M, ((dTarget j m / (R : ℝ)) / (((m : ℕ) : ℝ) + 1)) ^ 2
          = ∑ m : Fin M, (dTarget j m ^ 2 / (R : ℝ) ^ 2) * ((((m : ℕ) : ℝ) + 1) ^ (-2 : ℤ)) := by
            refine sum_congr rfl fun m _ => by simp [div_pow, zpow_neg]; ring
        _ ≤ ∑ m : Fin M, (72 * (N : ℝ) ^ 4 / (R : ℝ) ^ 2) * ((((m : ℕ) : ℝ) + 1) ^ (-2 : ℤ)) := by
            refine sum_le_sum fun m _ => mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_right (hd_sq_bd j m) (sq_nonneg _)) (by positivity)
        _ = (72 * (N : ℝ) ^ 4 / (R : ℝ) ^ 2) *
              ∑ m ∈ range M, (((m : ℕ) : ℝ) + 1) ^ (-2 : ℤ) := by
            rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun m : ℕ => (((m : ℕ) : ℝ) + 1) ^ (-2 : ℤ)) M]
        _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_sq_le_seven_fourths M) (by positivity)
    have hnum_le : (2 / (N : ℝ)) * ((72 * (N : ℝ) ^ 4 / (R : ℝ) ^ 2) * (7 / 4 : ℝ)) ≤
        1 / (16 * (M : ℝ) ^ 2) := by
      have hsimp : (2 / (N : ℝ)) * ((72 * (N : ℝ) ^ 4 / (R : ℝ) ^ 2) * (7 / 4 : ℝ)) =
          252 * (N : ℝ) ^ 3 / (R : ℝ) ^ 2 := by field_simp; ring
      rw [hsimp, div_le_div_iff₀ (sq_pos_of_pos hRpos) (by positivity)]
      have hMN : (M : ℝ) ≤ (N : ℝ) := by linarith only [hNr]
      have hR2 : (255 / 4 : ℝ) ^ 2 * (N : ℝ) ^ 5 ≤ (R : ℝ) ^ 2 := by
        calc (255 / 4 : ℝ) ^ 2 * (N : ℝ) ^ 5 = ((255 / 4 : ℝ) * (N : ℝ) ^ 2 * s) ^ 2 := by
              rw [mul_pow, mul_pow, ← pow_mul, hss]; ring
          _ ≤ (R : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hR_ge 2
      have hM2 : (M : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hMN 2
      calc 252 * (N : ℝ) ^ 3 * (16 * (M : ℝ) ^ 2)
          ≤ 252 * (N : ℝ) ^ 3 * (16 * (N : ℝ) ^ 2) := by gcongr
        _ = 4032 * (N : ℝ) ^ 5 := by ring
        _ ≤ (255 / 4 : ℝ) ^ 2 * (N : ℝ) ^ 5 :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ ≤ 1 * (R : ℝ) ^ 2 := by rw [one_mul]; exact hR2
    rw [← hNr]
    exact (mul_le_mul_of_nonneg_left hsum_bd (by positivity)).trans hnum_le
  choose zX _ hzX using fun j : Fin N => exists_angleShift hM (fun m => dTarget j m / (R : ℝ)) (hvX_bd j)
  -- Assemble the integer atomic measure: remaining rounded entries + shifted Grid A + shifted Grid B + D0 at (0,0)
  let baseSub : Γ → ℕ := Sum.elim (fun _ => R) (Sum.elim (fun _ => R) (fun _ => 0))
  have hbase_le : ∀ g : Γ, baseSub g ≤ t g := by
    rintro (ij | (ij | i))
    · exact hgridA ij
    · exact hgridB ij
    · exact Nat.zero_le _
  let κ₀ := Γ ⊕ (Fin N × Fin N) ⊕ (Fin N × Fin N) ⊕ Unit
  let dd₀ : κ₀ → ℕ := Sum.elim (fun g => t g - baseSub g)
    (Sum.elim (fun _ => R) (Sum.elim (fun _ => R) (fun _ => D0)))
  let angL : κ₀ → ℝ := Sum.elim θL
    (Sum.elim (fun ij => midAngle N ij.1.1)
      (Sum.elim (fun ij => midAngle N ij.1.1 + angleShift M (zX ij.2) ij.1.1) (fun _ => π / 2)))
  let angR : κ₀ → ℝ := Sum.elim θR
    (Sum.elim (fun ij => midAngle N ij.2.1 + angleShift M zY ij.2.1)
      (Sum.elim (fun ij => midAngle N ij.2.1) (fun _ => π / 2)))
  have hQ : ∀ m k : ℕ, m ≤ M → k ≤ M →
      ∑ r : κ₀, (dd₀ r : ℝ) * cos ((m : ℝ) * angL r) * cos ((k : ℝ) * angR r) =
        ∫ q : ℝ × ℝ, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval q.1 *
          (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval q.2 ∂μ := by
    intro m k hm hk
    have hsplit_k0 :
        ∑ r : κ₀, (dd₀ r : ℝ) * cos ((m : ℝ) * angL r) * cos ((k : ℝ) * angR r) =
        ∑ g : Γ, ((t g - baseSub g : ℕ) : ℝ) * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g) +
        (∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * midAngle N ij.1.1) *
            cos ((k : ℝ) * (midAngle N ij.2.1 + angleShift M zY ij.2.1)) +
          (∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * (midAngle N ij.1.1 + angleShift M (zX ij.2) ij.1.1)) *
              cos ((k : ℝ) * midAngle N ij.2.1) +
            (D0 : ℝ) * cos ((m : ℝ) * (π / 2)) * cos ((k : ℝ) * (π / 2)))) := by
      dsimp only [κ₀]
      rw [Fintype.sum_sum_type (α₁ := Γ)]
      congr 1
      rw [Fintype.sum_sum_type (α₁ := Fin N × Fin N)]
      congr 1
      rw [Fintype.sum_sum_type (α₁ := Fin N × Fin N)]
      congr 1
      exact Fintype.sum_unique _
    rw [hsplit_k0]
    have hsplit_g :
        ∑ g : Γ, ((t g - baseSub g : ℕ) : ℝ) * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g) =
        ∑ g : Γ, (t g : ℝ) * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g) -
          2 * ∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * midAngle N ij.1.1) *
            cos ((k : ℝ) * midAngle N ij.2.1) := by
      have h1 : ∀ g : Γ, ((t g - baseSub g : ℕ) : ℝ) * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g) =
          (t g : ℝ) * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g) -
            (baseSub g : ℝ) * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g) := fun g => by
        rw [Nat.cast_sub (hbase_le g)]; ring
      simp_rw [h1, sum_sub_distrib]
      congr 1
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp [baseSub, θL, θR, two_mul]
    have hshiftA :
        ∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * midAngle N ij.1.1) *
            cos ((k : ℝ) * (midAngle N ij.2.1 + angleShift M zY ij.2.1)) -
          ∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * midAngle N ij.1.1) *
            cos ((k : ℝ) * midAngle N ij.2.1) =
        if m = 0 then Δ 0 k else 0 := by
      have hexp :
          ∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * midAngle N ij.1.1) *
              cos ((k : ℝ) * (midAngle N ij.2.1 + angleShift M zY ij.2.1)) -
            ∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * midAngle N ij.1.1) *
              cos ((k : ℝ) * midAngle N ij.2.1) =
          (R : ℝ) * (∑ i : Fin N, cos ((m : ℝ) * midAngle N i.1)) *
            ∑ j : Fin N, (cos ((k : ℝ) * (midAngle N j.1 + angleShift M zY j.1)) -
              cos ((k : ℝ) * midAngle N j.1)) := by
        rw [← sum_sub_distrib, Fintype.sum_prod_type]
        calc ∑ i : Fin N, ∑ j : Fin N,
              ((R : ℝ) * cos ((m : ℝ) * midAngle N i.1) *
                cos ((k : ℝ) * (midAngle N j.1 + angleShift M zY j.1)) -
                (R : ℝ) * cos ((m : ℝ) * midAngle N i.1) * cos ((k : ℝ) * midAngle N j.1))
            = ∑ i : Fin N, ((R : ℝ) * cos ((m : ℝ) * midAngle N i.1)) *
                ∑ j : Fin N, (cos ((k : ℝ) * (midAngle N j.1 + angleShift M zY j.1)) -
                  cos ((k : ℝ) * midAngle N j.1)) := by
              refine sum_congr rfl fun i _ => ?_
              rw [mul_sum]
              refine sum_congr rfl fun j _ => by ring
          _ = _ := by
              rw [← sum_mul, ← mul_sum]
      rw [hexp]
      by_cases hm0 : m = 0
      · subst hm0
        simp only [Nat.cast_zero, zero_mul, cos_zero, sum_const, card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one, ↓reduceIte]
        by_cases hk0 : k = 0
        · subst hk0; simp [hΔ00]
        · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
          let k0 : Fin M := ⟨k - 1, by omega⟩
          have hmom := hzY k0
          change ∑ j ∈ range (M + 1), (cos ((((k0 : ℕ) : ℝ) + 1) * (midAngle (M + 1) j +
            angleShift M zY j)) - cos ((((k0 : ℕ) : ℝ) + 1) * midAngle (M + 1) j)) = vY k0 at hmom
          have hkeq : (((k0 : ℕ) : ℝ) + 1) = (k : ℝ) := by
            norm_cast; simp [k0]; omega
          rw [← Fin.sum_univ_eq_sum_range _ N, show M + 1 = N from rfl] at hmom
          simp_rw [hkeq] at hmom
          rw [hmom]
          have hvk : vY k0 = Δ 0 k / ((N : ℝ) * (R : ℝ)) := by
            simp only [vY, show (k0 : ℕ) + 1 = k by simp [k0]; omega]
          rw [hvk]
          field_simp
      · have h0 := sum_cos_midAngle hN0 (Nat.pos_of_ne_zero hm0) (by dsimp [N]; omega)
        rw [← Fin.sum_univ_eq_sum_range (fun i => cos ((m : ℝ) * midAngle N i)) N] at h0
        simp [hm0, h0]
    have hshiftB :
        ∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * (midAngle N ij.1.1 + angleShift M (zX ij.2) ij.1.1)) *
            cos ((k : ℝ) * midAngle N ij.2.1) -
          ∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * midAngle N ij.1.1) *
            cos ((k : ℝ) * midAngle N ij.2.1) =
        if m = 0 then 0 else Δ m k := by
      rw [← sum_sub_distrib, Fintype.sum_prod_type, sum_comm]
      have hrow :
          ∑ j : Fin N, ∑ i : Fin N,
            ((R : ℝ) * cos ((m : ℝ) * (midAngle N i.1 + angleShift M (zX j) i.1)) *
                cos ((k : ℝ) * midAngle N j.1) -
              (R : ℝ) * cos ((m : ℝ) * midAngle N i.1) * cos ((k : ℝ) * midAngle N j.1)) =
          ∑ j : Fin N, ((R : ℝ) * ∑ i : Fin N,
            (cos ((m : ℝ) * (midAngle N i.1 + angleShift M (zX j) i.1)) -
              cos ((m : ℝ) * midAngle N i.1))) * cos ((k : ℝ) * midAngle N j.1) := by
        refine sum_congr rfl fun j _ => ?_
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun i _ => by ring
      rw [hrow]
      by_cases hm0 : m = 0
      · subst hm0; simp
      · have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
        let m0 : Fin M := ⟨m - 1, by omega⟩
        have hmeq : (((m0 : ℕ) : ℝ) + 1) = (m : ℝ) := by
          norm_cast; simp [m0]; omega
        have hrow_val : ∀ j : Fin N,
            (R : ℝ) * ∑ i : Fin N, (cos ((m : ℝ) * (midAngle N i.1 + angleShift M (zX j) i.1)) -
              cos ((m : ℝ) * midAngle N i.1)) = dTarget j m0 := fun j => by
          have hmom := hzX j m0
          change ∑ i ∈ range (M + 1), (cos ((((m0 : ℕ) : ℝ) + 1) * (midAngle (M + 1) i +
            angleShift M (zX j) i)) - cos ((((m0 : ℕ) : ℝ) + 1) * midAngle (M + 1) i)) =
            dTarget j m0 / (R : ℝ) at hmom
          rw [← Fin.sum_univ_eq_sum_range _ N, show M + 1 = N from rfl] at hmom
          simp_rw [hmeq] at hmom
          rw [hmom]
          field_simp
        simp_rw [hrow_val]
        have ho := hd_orth m0 k hk
        simp only [show (m0 : ℕ) + 1 = m by simp [m0]; omega] at ho
        simp [hm0, ho]
    have hΔ_def :
        ∑ g : Γ, (t g : ℝ) * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g) +
          (D0 : ℝ) * cos ((m : ℝ) * (π / 2)) * cos ((k : ℝ) * (π / 2)) =
        ∫ q : ℝ × ℝ, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval q.1 *
          (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval q.2 ∂μ - Δ m k := by
      rw [← hw_mom m k hm hk]
      dsimp [Δ]
      have hdiff : ∑ g : Γ, w g * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g) -
          ∑ g : Γ, (w g - (t g : ℝ)) * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g) =
          ∑ g : Γ, (t g : ℝ) * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g) := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun g _ => by ring
      linarith only [hdiff]
    have hcomb :
        (∑ g : Γ, (t g : ℝ) * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g) -
          2 * ∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * midAngle N ij.1.1) *
            cos ((k : ℝ) * midAngle N ij.2.1)) +
        ((∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * midAngle N ij.1.1) *
            cos ((k : ℝ) * (midAngle N ij.2.1 + angleShift M zY ij.2.1))) +
          ((∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * (midAngle N ij.1.1 + angleShift M (zX ij.2) ij.1.1)) *
              cos ((k : ℝ) * midAngle N ij.2.1)) +
            (D0 : ℝ) * cos ((m : ℝ) * (π / 2)) * cos ((k : ℝ) * (π / 2)))) =
        (∑ g : Γ, (t g : ℝ) * cos ((m : ℝ) * θL g) * cos ((k : ℝ) * θR g) +
          (D0 : ℝ) * cos ((m : ℝ) * (π / 2)) * cos ((k : ℝ) * (π / 2))) +
        (∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * midAngle N ij.1.1) *
            cos ((k : ℝ) * (midAngle N ij.2.1 + angleShift M zY ij.2.1)) -
          ∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * midAngle N ij.1.1) *
            cos ((k : ℝ) * midAngle N ij.2.1)) +
        (∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * (midAngle N ij.1.1 + angleShift M (zX ij.2) ij.1.1)) *
            cos ((k : ℝ) * midAngle N ij.2.1) -
          ∑ ij : Fin N × Fin N, (R : ℝ) * cos ((m : ℝ) * midAngle N ij.1.1) *
            cos ((k : ℝ) * midAngle N ij.2.1)) := by ring
    rw [hsplit_g, hcomb, hΔ_def, hshiftA, hshiftB]
    by_cases hm0 : m = 0
    · subst hm0; simp
    · simp [hm0]
  classical
  let κ := {r : κ₀ // dd₀ r ≠ 0}
  let p : κ → ℝ × ℝ := fun r => (cos (angL r.1), cos (angR r.1))
  let d : κ → ℕ := fun r => dd₀ r.1
  have hsubsum : ∀ f : κ₀ → ℝ, (∀ r, dd₀ r = 0 → f r = 0) → ∑ r : κ, f r.1 = ∑ r, f r := by
    intro f hf
    rw [← Finset.sum_subtype (univ.filter fun r => dd₀ r ≠ 0) (p := fun r => dd₀ r ≠ 0)
      (by intro r; simp) f]
    exact Finset.sum_filter_of_ne fun r _ hr => by by_contra h0; exact hr (hf r h0)
  refine integerMomentMatching2D_of_chebyshev hsupp (κ := κ) (p := p) (d := d)
    (fun r => ⟨⟨neg_one_le_cos _, cos_le_one _⟩, ⟨neg_one_le_cos _, cos_le_one _⟩⟩)
    (fun r => Nat.pos_of_ne_zero r.2) fun m k hm hk => ?_
  rw [← hQ m k hm hk]
  have hTcos : ∀ (n : ℕ) (θ : ℝ), (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (cos θ) = cos ((n : ℝ) * θ) := by
    intro n θ
    rw [Polynomial.Chebyshev.T_real_cos]; simp
  refine (hsubsum (fun r => (dd₀ r : ℝ) * cos ((m : ℝ) * angL r) * cos ((k : ℝ) * angR r))
    (fun r hr => by simp [hr])).symm.trans ?_
  refine sum_congr rfl fun r _ => ?_
  dsimp [d, p]
  rw [hTcos m (angL r.1), hTcos k (angR r.1)]

/-- info: 'FormalResearch.ModularBootstrap.Spin.cheb2d_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.cheb2d_explicit

end FormalResearch.ModularBootstrap.Spin
