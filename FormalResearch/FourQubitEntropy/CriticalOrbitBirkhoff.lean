import Mathlib

/-!
# Signed Birkhoff bound for the diagonal overlap (`eq:fqe-signed-diagonal-overlap`)

For `c : ι → ι → ℂ` and real orthogonal `O₁, O₂`,
`‖∑_{i,k} c_{ik} O₁_{ik} O₂_{ik}‖ ≤ max_{π, ε} ‖∑_i ε_i c_{iπ(i)}‖`, with `ε_i = ±1` (`sbirk`).
The paper's proof: `|A_{ik} B_{ik}|` is doubly substochastic.  Here `|O₁_{ik} O₂_{ik}| ≤
(O₁_{ik}² + O₂_{ik}²)/2` and both `O_{ik}²` are doubly stochastic, so Birkhoff's theorem
(`doublyStochastic_eq_convexHull_permMatrix`) applies directly to a linear functional.
-/

open Matrix Finset

namespace FormalResearch.FourQubitEntropy.CO

/-- A linear functional bounded on permutation matrices is bounded on doubly stochastic matrices. -/
theorem birkhoff_linear {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ι → ℝ) (m : ℝ)
    (hm : ∀ σ : Equiv.Perm ι, ∑ i, r i (σ i) ≤ m) (G : Matrix ι ι ℝ)
    (hG : G ∈ doublyStochastic ℝ ι) : ∑ i, ∑ k, r i k * G i k ≤ m := by
  have hG2 : G ∈ (doublyStochastic ℝ ι : Set (Matrix ι ι ℝ)) := hG
  rw [doublyStochastic_eq_convexHull_permMatrix] at hG2
  have hconv : Convex ℝ {G : Matrix ι ι ℝ | ∑ i, ∑ k, r i k * G i k ≤ m} := by
    intro A hA B hB a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hA hB ⊢
    have : ∑ i, ∑ k, r i k * (a • A + b • B) i k
        = a * ∑ i, ∑ k, r i k * A i k + b * ∑ i, ∑ k, r i k * B i k := by
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    have h1 := mul_le_mul_of_nonneg_left hA ha
    have h2 := mul_le_mul_of_nonneg_left hB hb
    have h3 : (a + b) * m = m := by rw [hab, one_mul]
    linarith
  have hsub : {M | ∃ σ : Equiv.Perm ι, σ.permMatrix ℝ = M} ⊆
      {G : Matrix ι ι ℝ | ∑ i, ∑ k, r i k * G i k ≤ m} := by
    rintro _ ⟨σ, rfl⟩
    simp only [Set.mem_ofPred_eq]
    have : ∀ i, ∑ k, r i k * (σ.permMatrix ℝ) i k = r i (σ i) := by
      intro i
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    simp only [this]
    exact hm σ
  exact (convexHull_min hsub hconv) hG2

/-- The entrywise squares of a real orthogonal matrix are doubly stochastic. -/
theorem sq_doublyStochastic {ι : Type*} [Fintype ι] [DecidableEq ι] (O : Matrix ι ι ℝ)
    (h : Oᵀ * O = 1) : (Matrix.of fun i k => O i k ^ 2 : Matrix ι ι ℝ) ∈ doublyStochastic ℝ ι := by
  have h' : O * Oᵀ = 1 := mul_eq_one_comm.mp h
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i k => sq_nonneg _, fun i => ?_, fun k => ?_⟩
  · have := congrFun (congrFun h' i) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at this
    simpa [sq] using this
  · have := congrFun (congrFun h k) k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at this
    simpa [sq] using this

/-- **Signed Birkhoff bound.** -/
theorem sbirk {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ι → ℂ) (O1 O2 : Matrix ι ι ℝ)
    (h1 : O1ᵀ * O1 = 1) (h2 : O2ᵀ * O2 = 1) (B : ℝ)
    (hB : ∀ π : Equiv.Perm ι, ∀ ε : ι → ℝ, (∀ i, ε i ^ 2 = 1) →
      ‖∑ i, (ε i : ℂ) * c i (π i)‖ ≤ B) :
    ‖∑ i, ∑ k, c i k * ((O1 i k * O2 i k : ℝ) : ℂ)‖ ≤ B := by
  set z : ℂ := ∑ i, ∑ k, c i k * ((O1 i k * O2 i k : ℝ) : ℂ) with hz
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 1 (fun _ => 1) (by simp))
  by_cases hz0 : z = 0
  · rw [hz0]; simpa using hB0
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set u : ℂ := (starRingEnd ℂ) z / (‖z‖ : ℂ) with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzn,
      div_self hzn.ne']
  have huz : (u * z).re = ‖z‖ := by
    have : u * z = (‖z‖ : ℂ) := by
      rw [hu, div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hzn.ne'
      push_cast; field_simp
    rw [this]; simp
  -- the real functional
  set r : ι → ι → ℝ := fun i k => |(u * c i k).re| with hr
  have hre : (u * z).re = ∑ i, ∑ k, (u * c i k).re * (O1 i k * O2 i k) := by
    rw [hz, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hle1 : ∀ i k, (u * c i k).re * (O1 i k * O2 i k) ≤
      r i k * ((O1 i k ^ 2 + O2 i k ^ 2) / 2) := by
    intro i k
    have h3 : (u * c i k).re * (O1 i k * O2 i k) ≤ |(u * c i k).re| * |O1 i k * O2 i k| := by
      rw [← abs_mul]; exact le_abs_self _
    have h4 : |O1 i k * O2 i k| ≤ (O1 i k ^ 2 + O2 i k ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|O1 i k| - |O2 i k|), sq_abs (O1 i k), sq_abs (O2 i k)]
    exact h3.trans (mul_le_mul_of_nonneg_left h4 (abs_nonneg _))
  have hperm : ∀ π : Equiv.Perm ι, ∑ i, r i (π i) ≤ B := by
    intro π
    set ε : ι → ℝ := fun i => if 0 ≤ (u * c i (π i)).re then 1 else -1 with hε
    have hε2 : ∀ i, ε i ^ 2 = 1 := by intro i; simp only [hε]; split_ifs <;> norm_num
    have hεr : ∀ i, r i (π i) = ε i * (u * c i (π i)).re := by
      intro i
      simp only [hr, hε]
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (not_le.mp h)]; ring
    have hs : ∑ i, r i (π i) = (u * ∑ i, (ε i : ℂ) * c i (π i)).re := by
      rw [Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hεr]
      have : u * ((ε i : ℂ) * c i (π i)) = (ε i : ℂ) * (u * c i (π i)) := by ring
      rw [this]; simp
    rw [hs]
    calc (u * ∑ i, (ε i : ℂ) * c i (π i)).re ≤ ‖u * ∑ i, (ε i : ℂ) * c i (π i)‖ :=
          Complex.re_le_norm _
      _ = ‖∑ i, (ε i : ℂ) * c i (π i)‖ := by rw [norm_mul, hun, one_mul]
      _ ≤ B := hB π ε hε2
  have hP1 := birkhoff_linear r B hperm _ (sq_doublyStochastic O1 h1)
  have hP2 := birkhoff_linear r B hperm _ (sq_doublyStochastic O2 h2)
  have : ‖z‖ ≤ ∑ i, ∑ k, r i k * ((O1 i k ^ 2 + O2 i k ^ 2) / 2) := by
    rw [← huz, hre]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hle1 i k
  have hsum : ∑ i, ∑ k, r i k * ((O1 i k ^ 2 + O2 i k ^ 2) / 2) =
      (∑ i, ∑ k, r i k * (Matrix.of fun i k => O1 i k ^ 2 : Matrix _ _ ℝ) i k +
        ∑ i, ∑ k, r i k * (Matrix.of fun i k => O2 i k ^ 2 : Matrix _ _ ℝ) i k) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.of_apply]; ring
  rw [hsum] at this
  linarith

end FormalResearch.FourQubitEntropy.CO
