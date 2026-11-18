module

public import Mathlib
public import FormalResearch.JB.JBOneStepChart
public import FormalResearch.JB.JBPolar

/-!
# Paper J, Theorem B reduction: the one-step criterion (`thm:thb-onestep`), proof

Source: Paper J, `/home/user/scratch/paperJ2/thmB.tex`, Theorem `thm:thb-onestep`, Steps 1 and 5
(Steps 2-4, one chart, are in `JBOneStepChart`).

* `jb_onestep : OneStepReduction cs` for every `cs`, with `C* = 2 nb C₁ + 1`, `C₁ = Chart.chartConst cs`.
* Step 1: `‖host1 - U‖ ≤ √D C h^{m+1} log(1/h) ≤ 1`, so every host has norm `≤ 2`
  (`opNorm_le_of_cols`, `‖U‖ ≤ 1`).
* Step 5: `Ĝ^{[m]} - Ĝ^{[m+1]} = Σ_ν T_ν + Out`, `T_ν` the restriction of the difference to the rows covered
  by the two charts of block `ν` and the columns `Σ_ν` (the second chart only on rows not already covered by
  the first), each `T_ν` a zero-padded submatrix of `H^{[m]}_c - H^{[m+1]}_c` (`norm_Tpart_le`), and `Out` has
  all entries `≤ 2 ε5` (`I5`), hence `‖Out‖ ≤ 2 D ε5 ≤ h^m`.  The number `nb` of blocks is a constant of
  `cs`, so `‖Σ T_ν‖ ≤ Σ ‖T_ν‖ ≤ nb · 2 C₁ h^m` (triangle inequality); the sharper `(Σ‖T_ν‖²)^{1/2}` of the
  paper (orthogonal column projections) is not needed for the stated form and is not formalised.
* Third conclusion: `jb_polar`.
-/

@[expose] public section

namespace FormalResearch.JB

open Matrix FormalResearch.MatrixAnalysis
open scoped Matrix.Norms.L2Operator

section Step1

theorem norm_orth_le_one {D : ℕ} {U : Matrix (Fin D) (Fin D) ℝ} (hU : Uᵀ * U = 1) : ‖U‖ ≤ 1 := by
  have h1 := l2_opNorm_conjTranspose_mul_self U
  rw [conjTranspose_eq_transpose_of_trivial, hU] at h1
  have h2 : ‖(1 : Matrix (Fin D) (Fin D) ℝ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one]
    exact FormalResearch.MatrixAnalysis.jop_norm_diagonal_le _ zero_le_one (fun _ => by simp)
  nlinarith [norm_nonneg U]

theorem jbL2_univ_le_of_abs_le {D : ℕ} (v : Fin D → ℝ) {b : ℝ} (hb : 0 ≤ b) (h : ∀ i, |v i| ≤ b) :
    jbL2 Finset.univ v ≤ √(D : ℝ) * b := by
  unfold jbL2
  have e : √(D : ℝ) * b = √((D : ℝ) * b ^ 2) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hb]
  rw [e]
  apply Real.sqrt_le_sqrt
  calc ∑ i, v i ^ 2 ≤ ∑ _i : Fin D, b ^ 2 := Finset.sum_le_sum fun i _ => by
        have := h i
        nlinarith [abs_nonneg (v i), sq_abs (v i)]
    _ = (D : ℝ) * b ^ 2 := by simp

/-- A matrix with all entries `≤ b` in modulus has operator norm `≤ D b`. -/
theorem norm_le_of_entries {D : ℕ} (M : Matrix (Fin D) (Fin D) ℝ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i k, |M i k| ≤ b) : ‖M‖ ≤ (D : ℝ) * b := by
  have := opNorm_le_of_cols M (c := √(D : ℝ) * b)
    (fun j => jbL2_univ_le_of_abs_le _ hb (fun i => h i j))
  have e : √(D : ℝ) * (√(D : ℝ) * b) = (D : ℝ) * b := by
    rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rwa [e] at this

/-- Step 1: the host of order `m + 1` is within `1` of `U`, hence of norm `≤ 2`. -/
theorem norm_le_two_of_close {D : ℕ} {U G : Matrix (Fin D) (Fin D) ℝ} (hU : Uᵀ * U = 1) {η : ℝ}
    (hcol : ∀ j, jbL2 Finset.univ (fun i => G i j - U i j) ≤ η) (hη : √(D : ℝ) * η ≤ 1) :
    ‖G‖ ≤ 2 := by
  have h1 := opNorm_le_of_cols (G - U) (c := η) (fun j => by simpa using hcol j)
  have h2 := norm_orth_le_one hU
  calc ‖G‖ = ‖(G - U) + U‖ := by congr 1; abel
    _ ≤ ‖G - U‖ + ‖U‖ := norm_add_le _ _
    _ ≤ 2 := by linarith

end Step1

section Step5

variable {D R : ℕ} {cols : Finset (Fin D)}

open Classical in
/-- The part of `Δ` on the rows `c.row n` (`n ∈ S`) and the columns `cols`, zero elsewhere. -/
noncomputable def Tpart (c : Chart D R cols) (S : Finset (Fin R)) (Δ : Matrix (Fin D) (Fin D) ℝ) :
    Matrix (Fin D) (Fin D) ℝ :=
  Matrix.of fun i k => if (∃ n ∈ S, c.row n = i) ∧ k ∈ cols then Δ i k else 0

open Classical in
/-- A zero-padded submatrix is bounded by the matrix: `‖Tpart c S Δ‖ ≤ ‖M‖` when `Δ` agrees with `M` on
the rows `S` of the chart. -/
theorem norm_Tpart_le (c : Chart D R cols) (S : Finset (Fin R)) (Δ : Matrix (Fin D) (Fin D) ℝ)
    (M : Matrix (Fin R) cols ℝ) (hM : ∀ n ∈ S, ∀ k : cols, Δ (c.row n) k = M n k) :
    ‖Tpart c S Δ‖ ≤ ‖M‖ := by
  let f : Fin D → Option (Fin R) := fun i =>
    if h : ∃ n ∈ S, c.row n = i then some h.choose else none
  let g : Fin D → Option cols := fun k => if h : k ∈ cols then some ⟨k, h⟩ else none
  have hf : ∀ n n' m, f n = some m → f n' = some m → n = n' := by
    intro i i' a h1 h2
    simp only [f] at h1 h2
    split_ifs at h1 h2 with e1 e2
    have a1 := e1.choose_spec.2
    have a2 := e2.choose_spec.2
    rw [Option.some.injEq] at h1 h2
    rw [← a1, ← a2, h1, h2]
  have hg : ∀ n n' m, g n = some m → g n' = some m → n = n' := by
    intro k k' a h1 h2
    simp only [g] at h1 h2
    split_ifs at h1 h2 with e1 e2
    rw [Option.some.injEq] at h1 h2
    have := congrArg Subtype.val (h1.trans h2.symm)
    simpa using this
  have e : Tpart c S Δ = pad f g M := by
    ext i k
    simp only [Tpart, pad, of_apply]
    by_cases h1 : ∃ n ∈ S, c.row n = i
    · by_cases h2 : k ∈ cols
      · simp only [f, g, h1, h2, dif_pos, and_self, if_true]
        have := hM h1.choose h1.choose_spec.1 ⟨k, h2⟩
        rw [h1.choose_spec.2] at this
        exact this
      · simp [f, g, h1, h2]
    · simp [f, g, h1]
  rw [e]
  exact norm_pad_le f g hf hg M


theorem norm_H1_le {cs : OneStepConsts} {m : ℕ} {h : ℝ} {U : Matrix (Fin D) (Fin D) ℝ}
    {c : Chart D R cols} (hc : c.Ok cs m h U) : ‖c.H1 h‖ ≤ ‖c.host1‖ := by
  have e : c.H1 h = pad (fun n => some (c.row n)) (fun k : cols => some (k : Fin D)) c.host1 := by
    ext n k; simp [pad, hc.host1_eq]
  rw [e]
  refine norm_pad_le _ _ ?_ ?_ _
  · intro a b x h1 h2
    exact c.row_injective ((Option.some.inj h1).trans (Option.some.inj h2).symm)
  · intro a b x h1 h2
    exact Subtype.ext ((Option.some.inj h1).trans (Option.some.inj h2).symm)

end Step5

section Main

variable {cs : OneStepConsts} {D m : ℕ} {h : ℝ} (I : OneStepInputs cs D m h)

/-- Row `i` is covered by one of the two charts of block `ν`. -/
def OneStepInputs.cov (ν : Fin cs.nb) (i : Fin D) : Prop :=
  (∃ n ∈ (I.ch ν 0).used, (I.ch ν 0).row n = i) ∨ (∃ n ∈ (I.ch ν 1).used, (I.ch ν 1).row n = i)

open Classical in
/-- The rows of the second chart not already covered by the first. -/
noncomputable def OneStepInputs.S1 (ν : Fin cs.nb) : Finset (Fin (I.R ν 1)) :=
  (I.ch ν 1).used.filter fun n => ¬ ∃ n' ∈ (I.ch ν 0).used, (I.ch ν 0).row n' = (I.ch ν 1).row n

/-- The part of `Ĝ^{[m]} - Ĝ^{[m+1]}` carried by block `ν`. -/
noncomputable def OneStepInputs.T (ν : Fin cs.nb) : Matrix (Fin D) (Fin D) ℝ :=
  Tpart (I.ch ν 0) (I.ch ν 0).used (I.G0 - I.G1) + Tpart (I.ch ν 1) (I.S1 ν) (I.G0 - I.G1)

open Classical in
theorem OneStepInputs.T_apply (ν : Fin cs.nb) (i k : Fin D) :
    I.T ν i k = if k ∈ I.cols ν ∧ I.cov ν i then (I.G0 - I.G1) i k else 0 := by
  simp only [OneStepInputs.T, Tpart, Matrix.add_apply, of_apply]
  have hS1 : (∃ n ∈ I.S1 ν, (I.ch ν 1).row n = i) ↔
      (∃ n ∈ (I.ch ν 1).used, (I.ch ν 1).row n = i) ∧
        ¬ ∃ n' ∈ (I.ch ν 0).used, (I.ch ν 0).row n' = i := by
    simp only [OneStepInputs.S1, Finset.mem_filter]
    constructor
    · rintro ⟨n, ⟨hn, hne⟩, hr⟩
      exact ⟨⟨n, hn, hr⟩, by rw [← hr]; exact hne⟩
    · rintro ⟨⟨n, hn, hr⟩, hne⟩
      exact ⟨n, ⟨hn, by rw [hr]; exact hne⟩, hr⟩
  rw [if_congr (and_congr_left' hS1) rfl rfl]
  by_cases hk : k ∈ I.cols ν
  · by_cases ha : ∃ n ∈ (I.ch ν 0).used, (I.ch ν 0).row n = i
    · simp [hk, ha, OneStepInputs.cov]
    · by_cases hb : ∃ n ∈ (I.ch ν 1).used, (I.ch ν 1).row n = i
      · simp [hk, ha, hb, OneStepInputs.cov]
      · simp [hk, ha, hb, OneStepInputs.cov]
  · simp [hk]

open Classical in
theorem OneStepInputs.out_entry (i k : Fin D) :
    |((I.G0 - I.G1) - ∑ ν, I.T ν) i k| ≤ 2 * I.ε5 := by
  have hsum : (∑ ν, I.T ν) i k = ∑ ν, (if k ∈ I.cols ν ∧ I.cov ν i then (I.G0 - I.G1) i k else 0) := by
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun ν _ => I.T_apply ν i k
  rw [Matrix.sub_apply, hsum]
  by_cases hcov : ∃ ν, k ∈ I.cols ν ∧ I.cov ν i
  · obtain ⟨ν1, hk1, hc1⟩ := hcov
    have : ∑ ν, (if k ∈ I.cols ν ∧ I.cov ν i then (I.G0 - I.G1) i k else 0) = (I.G0 - I.G1) i k := by
      rw [Finset.sum_eq_single ν1]
      · simp [hk1, hc1]
      · intro ν _ hne
        have hd := I.cols_disjoint ν ν1 hne
        have : k ∉ I.cols ν := fun hk => Finset.disjoint_left.1 hd hk hk1
        simp [this]
      · simp
    rw [this]
    have h0 : (0 : ℝ) ≤ 2 * I.ε5 := by have := I.ε5_nonneg; linarith
    simpa using h0
  · push_neg at hcov
    have : ∑ ν, (if k ∈ I.cols ν ∧ I.cov ν i then (I.G0 - I.G1) i k else 0) = 0 :=
      Finset.sum_eq_zero fun ν _ => by
        have := hcov ν
        by_cases hk : k ∈ I.cols ν
        · simp [hk, this hk]
        · simp [hk]
    rw [this, sub_zero]
    have hout : ¬ ∃ (ν : Fin cs.nb) (j : Fin 2) (n : Fin (I.R ν j)),
        n ∈ (I.ch ν j).used ∧ (I.ch ν j).row n = i ∧ k ∈ I.cols ν := by
      rintro ⟨ν, j, n, hn, hr, hk⟩
      have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
      apply hcov ν hk
      rcases hj with rfl | rfl
      · exact Or.inl ⟨n, hn, hr⟩
      · exact Or.inr ⟨n, hn, hr⟩
    obtain ⟨a0, a1, -⟩ := I.outside i k hout
    rw [Matrix.sub_apply]
    calc |I.G0 i k - I.G1 i k| ≤ |I.G0 i k| + |I.G1 i k| := abs_sub _ _
      _ ≤ 2 * I.ε5 := by linarith

/-- **The one-step criterion** (Paper J, `thm:thb-onestep`): proof of `OneStepReduction`.
`C* = 2 nb C₁ + 1` with `C₁ = Chart.chartConst cs`; it depends only on `cs`. -/
theorem jb_onestep (cs : OneStepConsts) : OneStepReduction cs := by
  intro m
  refine ⟨2 * (cs.nb : ℝ) * Chart.chartConst cs + 1, ?_⟩
  intro D h I hS
  obtain ⟨hh1, hη, h2, h3, hk, h5⟩ := hS
  have hh0 := I.h_pos
  have hhm : 0 < h ^ m := pow_pos hh0 m
  have hC1 := Chart.chartConst_nonneg cs
  -- Step 1
  have hG1 : ‖I.G1 - I.U‖ ≤ √(D : ℝ) * (cs.C * h ^ (m + 1) * Real.log (1 / h)) :=
    opNorm_le_of_cols _ (fun j => by simpa using I.G1_col j)
  have hhost : ∀ ν j, ‖(I.ch ν j).host1‖ ≤ 2 := fun ν j =>
    norm_le_two_of_close I.U_orth (I.chart_ok ν j).host1_col hη
  have hH1 : ∀ ν j, ‖(I.ch ν j).H1 h‖ ≤ 2 := fun ν j =>
    (norm_H1_le (I.chart_ok ν j)).trans (hhost ν j)
  -- Steps 2-4
  have hchart : ∀ ν j, ‖(I.ch ν j).H0 h - (I.ch ν j).H1 h‖ ≤ Chart.chartConst cs * h ^ m := fun ν j =>
    Chart.chart_diff (I.chart_ok ν j) hh0 hh1 h2 h3 hk (hH1 ν j)
  -- Step 5
  have hmatch : ∀ ν j, ∀ n ∈ (I.ch ν j).used, ∀ k : I.cols ν,
      (I.G0 - I.G1) ((I.ch ν j).row n) k = ((I.ch ν j).H0 h - (I.ch ν j).H1 h) n k := by
    intro ν j n hn k
    simp [Matrix.sub_apply, I.match0 ν j n hn k, I.match1 ν j n hn k]
  have hT : ∀ ν, ‖I.T ν‖ ≤ 2 * (Chart.chartConst cs * h ^ m) := by
    intro ν
    have a0 := norm_Tpart_le (I.ch ν 0) (I.ch ν 0).used (I.G0 - I.G1) _ (hmatch ν 0)
    have a1 := norm_Tpart_le (I.ch ν 1) (I.S1 ν) (I.G0 - I.G1) _
      (fun n hn k => hmatch ν 1 n (Finset.mem_filter.1 hn).1 k)
    have := norm_add_le (Tpart (I.ch ν 0) (I.ch ν 0).used (I.G0 - I.G1))
      (Tpart (I.ch ν 1) (I.S1 ν) (I.G0 - I.G1))
    unfold OneStepInputs.T
    linarith [hchart ν 0, hchart ν 1]
  have hOut : ‖(I.G0 - I.G1) - ∑ ν, I.T ν‖ ≤ h ^ m := by
    have := norm_le_of_entries ((I.G0 - I.G1) - ∑ ν, I.T ν) (b := 2 * I.ε5)
      (by have := I.ε5_nonneg; linarith) (fun i k => I.out_entry i k)
    refine this.trans ?_
    linarith
  have hsumT : ‖∑ ν, I.T ν‖ ≤ (cs.nb : ℝ) * (2 * (Chart.chartConst cs * h ^ m)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ ν, ‖I.T ν‖ ≤ ∑ _ν : Fin cs.nb, 2 * (Chart.chartConst cs * h ^ m) :=
          Finset.sum_le_sum fun ν _ => hT ν
      _ = (cs.nb : ℝ) * (2 * (Chart.chartConst cs * h ^ m)) := by simp
  have hdiff : ‖I.G0 - I.G1‖ ≤ (2 * (cs.nb : ℝ) * Chart.chartConst cs + 1) * h ^ m := by
    have e : I.G0 - I.G1 = ∑ ν, I.T ν + ((I.G0 - I.G1) - ∑ ν, I.T ν) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    nlinarith
  refine ⟨hdiff, ?_, fun hlt => ?_⟩
  · calc ‖I.G0 - I.U‖ = ‖(I.G0 - I.G1) + (I.G1 - I.U)‖ := by congr 1; abel
      _ ≤ ‖I.G0 - I.G1‖ + ‖I.G1 - I.U‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hdiff hG1
  · obtain ⟨-, ho, -, -, h2', -⟩ := jb_polar I.G0 I.U I.U_orth hlt
    exact ⟨ho, h2'⟩

/-- info: 'FormalResearch.JB.jb_onestep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JB.jb_onestep

end Main

end FormalResearch.JB
