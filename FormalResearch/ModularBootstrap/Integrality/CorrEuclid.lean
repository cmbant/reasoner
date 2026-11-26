module

public import FormalResearch.ModularBootstrap.Integrality.AngleShift
public import FormalResearch.ModularBootstrap.Integrality.CorrDef
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The Euclidean correction (`int:cheb-explicit`): Bessel bound and `Corr`

`CFT/modular_bootstrap/paper/integrality.tex`, Lemma INT-M.exp (`int:cheb-explicit`), second
paragraph: the rounding defect satisfies Bessel's inequality
`∑_{m=1}^M |Δ_m/m|² ≤ (π/2) ∫_0^π F² ≤ π²/2` (`int:bessel`); together with the Euclidean
angle-shift inverse of `AngleShift` this gives the correction property `Corr (M+1) M R` as soon as
`R²(M+1) ≥ 16π²M²` (i.e. `R ≥ 4πM/√N`).  **Proved.**
-/

@[expose] public section

open Real Finset

namespace FormalResearch.ModularBootstrap.Integrality

/-- `∫_0^π cos(zθ) dθ = 0` for a nonzero integer frequency. -/
lemma integral_cos_int_zero {z : ℤ} (hz : z ≠ 0) :
    ∫ θ in (0 : ℝ)..π, cos ((z : ℝ) * θ) = 0 := by
  have hz' : (z : ℝ) ≠ 0 := by exact_mod_cast hz
  rw [intervalIntegral.integral_comp_mul_left (fun x => cos x) hz', integral_cos]
  simp [sin_int_mul_pi]

/-- Orthogonality of `sin(mθ)` on `[0, π]`. -/
lemma integral_sin_mul_sin_nat (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    ∫ θ in (0 : ℝ)..π, sin ((m : ℝ) * θ) * sin ((k : ℝ) * θ) = if m = k then π / 2 else 0 := by
  have hpt : ∀ θ : ℝ, sin ((m : ℝ) * θ) * sin ((k : ℝ) * θ) =
      (cos ((((m : ℤ) - k : ℤ) : ℝ) * θ) - cos ((((m : ℤ) + k : ℤ) : ℝ) * θ)) / 2 := by
    intro θ
    have := two_mul_sin_mul_sin ((m : ℝ) * θ) ((k : ℝ) * θ)
    push_cast
    rw [← sub_mul, ← add_mul] at this
    linarith
  simp_rw [hpt]
  have hi : ∀ z : ℤ, IntervalIntegrable (fun θ : ℝ => cos ((z : ℝ) * θ)) MeasureTheory.volume 0 π :=
    fun z => (by fun_prop : Continuous fun θ : ℝ => cos ((z : ℝ) * θ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hi _) (hi _),
    integral_cos_int_zero (by omega : ((m : ℤ) + k) ≠ 0)]
  by_cases hmk : m = k
  · subst hmk
    simp
  · rw [integral_cos_int_zero (by omega : ((m : ℤ) - k) ≠ 0)]
    simp [hmk]

/-- One interval of the Bessel estimate: `S ∫_a^b g ≤ (π/4) S² (b - a) + (1/π) ∫_a^b g²`. -/
lemma bessel_step {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a ≤ b) (S : ℝ) :
    S * ∫ θ in a..b, g θ ≤ π / 4 * S ^ 2 * (b - a) + (1 / π) * ∫ θ in a..b, g θ ^ 2 := by
  have h1 : IntervalIntegrable g MeasureTheory.volume a b := hg.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ => g θ ^ 2) MeasureTheory.volume a b :=
    (hg.pow 2).intervalIntegrable _ _
  have hmono : ∫ θ in a..b, S * g θ ≤ ∫ θ in a..b, (π / 4 * S ^ 2 + (1 / π) * g θ ^ 2) := by
    refine intervalIntegral.integral_mono_on hab (h1.const_mul S)
      ((intervalIntegrable_const).add (h2.const_mul _)) fun θ _ => ?_
    have hπ : 0 < π := pi_pos
    have : 0 ≤ (π / 2 * S - g θ) ^ 2 := sq_nonneg _
    have e : π / 4 * S ^ 2 + (1 / π) * g θ ^ 2 - S * g θ = (1 / π) * (π / 2 * S - g θ) ^ 2 := by
      field_simp; ring
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / π) this]
  have e1 : ∫ θ in a..b, (π / 4 * S ^ 2 + (1 / π) * g θ ^ 2) =
      π / 4 * S ^ 2 * (b - a) + (1 / π) * ∫ θ in a..b, g θ ^ 2 := by
    rw [intervalIntegral.integral_add intervalIntegrable_const (h2.const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
    ring
  have e2 : ∫ θ in a..b, S * g θ = S * ∫ θ in a..b, g θ := intervalIntegral.integral_const_mul _ _
  rw [e1, e2] at hmono
  exact hmono

/-- The rounding defect `Δ_m = ∑_i S_i (cos(mα_i) - cos(mα_{i+1}))` (`int:defect-ibp`). -/
noncomputable def roundingDefect (L : ℕ) (α S : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ range L, S i * (cos ((m : ℝ) * α i) - cos ((m : ℝ) * α (i + 1)))

/-- **Bessel's inequality for the rounding defect** (`int:bessel`):
`∑_{m=1}^M (Δ_m/m)² ≤ π²/2`. -/
theorem bessel_defect (M L : ℕ) (α S : ℕ → ℝ) (hα : ∀ i ≤ L, α i ∈ Set.Icc (0 : ℝ) π)
    (hmono : ∀ i < L, α i ≤ α (i + 1)) (hS : ∀ i < L, 0 ≤ S i ∧ S i < 1) :
    ∑ k ∈ range M, (roundingDefect L α S (k + 1) / (((k : ℕ) : ℝ) + 1)) ^ 2 ≤ π ^ 2 / 2 := by
  have hπ : 0 < π := pi_pos
  set c : ℕ → ℝ := fun k => roundingDefect L α S (k + 1) / (((k : ℕ) : ℝ) + 1) with hc
  set g : ℝ → ℝ := fun θ => ∑ k ∈ range M, c k * sin ((((k : ℕ) : ℝ) + 1) * θ) with hg
  have hgc : Continuous g := by
    refine continuous_finsetSum _ fun k _ => ?_
    fun_prop
  have hI : ∀ i k : ℕ, ∫ θ in α i..α (i + 1), sin ((((k : ℕ) : ℝ) + 1) * θ) =
      (cos ((((k : ℕ) : ℝ) + 1) * α i) - cos ((((k : ℕ) : ℝ) + 1) * α (i + 1))) /
        (((k : ℕ) : ℝ) + 1) := by
    intro i k
    have hk0 : (((k : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun x => sin x) hk0, integral_sin, smul_eq_mul]
    field_simp
  have hck : ∀ k, c k = ∑ i ∈ range L, S i * ∫ θ in α i..α (i + 1), sin ((((k : ℕ) : ℝ) + 1) * θ) := by
    intro k
    simp only [hc, roundingDefect, hI]
    push_cast
    rw [sum_div]
    exact sum_congr rfl fun i _ => by ring
  have hgi : ∀ i, ∫ θ in α i..α (i + 1), g θ =
      ∑ k ∈ range M, c k * ∫ θ in α i..α (i + 1), sin ((((k : ℕ) : ℝ) + 1) * θ) := by
    intro i
    simp only [hg]
    rw [intervalIntegral.integral_finsetSum]
    · exact sum_congr rfl fun k _ => intervalIntegral.integral_const_mul _ _
    · intro k _
      exact (by fun_prop : Continuous fun θ : ℝ => c k * sin ((((k : ℕ) : ℝ) + 1) * θ)).intervalIntegrable _ _
  set A : ℝ := ∑ k ∈ range M, c k ^ 2 with hA
  have hA1 : A = ∑ i ∈ range L, S i * ∫ θ in α i..α (i + 1), g θ := by
    have : ∀ k ∈ range M, c k ^ 2 = ∑ i ∈ range L, c k * (S i *
        ∫ θ in α i..α (i + 1), sin ((((k : ℕ) : ℝ) + 1) * θ)) := by
      intro k _
      calc c k ^ 2 = c k * (∑ i ∈ range L, S i *
            ∫ θ in α i..α (i + 1), sin ((((k : ℕ) : ℝ) + 1) * θ)) := by rw [← hck k, sq]
        _ = _ := mul_sum _ _ _
    rw [hA, sum_congr rfl this, sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [hgi i, mul_sum]
    exact sum_congr rfl fun k _ => by ring
  -- `∫_0^π g² = (π/2) A`
  have hg2 : ∫ θ in (0 : ℝ)..π, g θ ^ 2 = π / 2 * A := by
    have hexp : ∀ θ : ℝ, g θ ^ 2 = ∑ k ∈ range M, ∑ l ∈ range M, c k * c l *
        (sin ((((k : ℕ) : ℝ) + 1) * θ) * sin ((((l : ℕ) : ℝ) + 1) * θ)) := by
      intro θ
      simp only [hg]
      rw [sq, sum_mul_sum]
      exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
    simp_rw [hexp]
    rw [intervalIntegral.integral_finsetSum]
    · have : ∀ k ∈ range M, ∫ θ in (0 : ℝ)..π, ∑ l ∈ range M, c k * c l *
          (sin ((((k : ℕ) : ℝ) + 1) * θ) * sin ((((l : ℕ) : ℝ) + 1) * θ)) = π / 2 * c k ^ 2 := by
        intro k hk
        rw [intervalIntegral.integral_finsetSum]
        · have h2 : ∀ l ∈ range M, ∫ θ in (0 : ℝ)..π, c k * c l *
              (sin ((((k : ℕ) : ℝ) + 1) * θ) * sin ((((l : ℕ) : ℝ) + 1) * θ)) =
              if l = k then π / 2 * c k ^ 2 else 0 := by
            intro l hl
            rw [intervalIntegral.integral_const_mul]
            have := integral_sin_mul_sin_nat (k + 1) (l + 1) (by omega) (by omega)
            push_cast at this
            rw [this]
            by_cases hlk : l = k
            · subst hlk; simp; ring
            · have hkl : ¬ k = l := fun h => hlk h.symm
              simp [hlk, hkl]
          rw [sum_congr rfl h2]
          simp [hk]
        · intro l _
          exact (by fun_prop : Continuous fun θ : ℝ => c k * c l *
            (sin ((((k : ℕ) : ℝ) + 1) * θ) * sin ((((l : ℕ) : ℝ) + 1) * θ))).intervalIntegrable _ _
      rw [sum_congr rfl this, hA, mul_sum]
    · intro k _
      refine (continuous_finsetSum _ fun l _ => ?_).intervalIntegrable _ _
      fun_prop
  -- sum of the step inequalities
  have hstep : ∀ i ∈ range L, S i * ∫ θ in α i..α (i + 1), g θ ≤
      π / 4 * S i ^ 2 * (α (i + 1) - α i) + (1 / π) * ∫ θ in α i..α (i + 1), g θ ^ 2 :=
    fun i hi => bessel_step hgc (hmono i (mem_range.1 hi)) (S i)
  have hsum_g2 : ∑ i ∈ range L, ∫ θ in α i..α (i + 1), g θ ^ 2 ≤ ∫ θ in (0 : ℝ)..π, g θ ^ 2 := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (f := fun θ => g θ ^ 2)
      (fun k _ => (hgc.pow 2).intervalIntegrable _ _)]
    have h0L : ∀ n ≤ L, α 0 ≤ α n := by
      intro n hn
      induction n with
      | zero => exact le_rfl
      | succ n ih => exact (ih (by omega)).trans (hmono n (by omega))
    exact intervalIntegral.integral_mono_interval (hα 0 (Nat.zero_le _)).1 (h0L L le_rfl)
      (hα L le_rfl).2 (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      ((hgc.pow 2).intervalIntegrable _ _)
  have hlen : ∑ i ∈ range L, S i ^ 2 * (α (i + 1) - α i) ≤ π := by
    have h1 : ∑ i ∈ range L, S i ^ 2 * (α (i + 1) - α i) ≤ ∑ i ∈ range L, (α (i + 1) - α i) := by
      refine sum_le_sum fun i hi => ?_
      have hi' := mem_range.1 hi
      have hS' := hS i hi'
      have hd : 0 ≤ α (i + 1) - α i := sub_nonneg.2 (hmono i hi')
      have hS2 : S i ^ 2 ≤ 1 := by nlinarith [hS'.1, hS'.2]
      nlinarith
    rw [sum_range_sub (fun i => α i)] at h1
    have := (hα L le_rfl).2
    have := (hα 0 (Nat.zero_le _)).1
    linarith
  have hmain : A ≤ π / 4 * π + (1 / π) * (π / 2 * A) := by
    calc A = ∑ i ∈ range L, S i * ∫ θ in α i..α (i + 1), g θ := hA1
      _ ≤ ∑ i ∈ range L, (π / 4 * S i ^ 2 * (α (i + 1) - α i) +
            (1 / π) * ∫ θ in α i..α (i + 1), g θ ^ 2) := sum_le_sum hstep
      _ = π / 4 * ∑ i ∈ range L, S i ^ 2 * (α (i + 1) - α i) +
            (1 / π) * ∑ i ∈ range L, ∫ θ in α i..α (i + 1), g θ ^ 2 := by
          rw [sum_add_distrib, mul_sum, mul_sum]
          congr 1
          exact sum_congr rfl fun i _ => by ring
      _ ≤ π / 4 * π + (1 / π) * (π / 2 * A) := by
          rw [← hg2]
          have h1 := mul_le_mul_of_nonneg_left hlen (by positivity : (0 : ℝ) ≤ π / 4)
          have h2 := mul_le_mul_of_nonneg_left hsum_g2 (by positivity : (0 : ℝ) ≤ 1 / π)
          linarith
  have : 1 / π * (π / 2 * A) = A / 2 := by field_simp
  rw [this] at hmain
  have hfin : A ≤ π ^ 2 / 2 := by nlinarith [hmain]
  simpa [hA, hc] using hfin

/-- **The Euclidean correction** (`int:cheb-explicit`): on the midpoint grid of size `M + 1`,
`R` integer units per site repair every rounding defect as soon as `R² (M+1) ≥ 16 π² M²`
(i.e. `R ≥ 4πM/√N`). -/
theorem corr_euclid {M : ℕ} (hM : 1 ≤ M) {R : ℝ} (hR : 0 < R)
    (hRM : 16 * π ^ 2 * (M : ℝ) ^ 2 ≤ R ^ 2 * ((M : ℝ) + 1)) : Corr (M + 1) M R := by
  intro L α S hα hmono hS
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hbes := bessel_defect M L α S hα hmono hS
  obtain ⟨z, -, hz⟩ := exists_angleShift hM (fun i : Fin M => roundingDefect L α S ((i : ℕ) + 1) / R)
    (by
      have h1 : ∑ i : Fin M, (roundingDefect L α S ((i : ℕ) + 1) / R / (((i : ℕ) : ℝ) + 1)) ^ 2 =
          (1 / R ^ 2) * ∑ k ∈ range M,
            (roundingDefect L α S (k + 1) / (((k : ℕ) : ℝ) + 1)) ^ 2 := by
        rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ =>
          (roundingDefect L α S (k + 1) / (((k : ℕ) : ℝ) + 1)) ^ 2) M, mul_sum]
        refine sum_congr rfl fun i _ => ?_
        field_simp
      rw [h1]
      have h2 : (1 / R ^ 2) * ∑ k ∈ range M,
          (roundingDefect L α S (k + 1) / (((k : ℕ) : ℝ) + 1)) ^ 2 ≤ (1 / R ^ 2) * (π ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hbes (by positivity)
      calc 2 / ((M : ℝ) + 1) * ((1 / R ^ 2) * ∑ k ∈ range M,
            (roundingDefect L α S (k + 1) / (((k : ℕ) : ℝ) + 1)) ^ 2)
          ≤ 2 / ((M : ℝ) + 1) * ((1 / R ^ 2) * (π ^ 2 / 2)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = π ^ 2 / (R ^ 2 * ((M : ℝ) + 1)) := by field_simp
        _ ≤ 1 / (16 * (M : ℝ) ^ 2) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hRM])
  refine ⟨angleShift M z, fun m hm1 hmM => ?_⟩
  have hi : m - 1 < M := by omega
  have := hz ⟨m - 1, hi⟩
  simp only [momentMap] at this
  have hm : (((m - 1 : ℕ) : ℝ) + 1) = m := by
    rw [Nat.cast_sub hm1]; push_cast; ring
  rw [hm] at this
  have hmm : ((m - 1 : ℕ) + 1) = m := by omega
  rw [hmm] at this
  rw [this]
  simp only [roundingDefect]
  rw [one_div, inv_mul_eq_div]

/-- info: 'FormalResearch.ModularBootstrap.Integrality.corr_euclid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corr_euclid

end FormalResearch.ModularBootstrap.Integrality
