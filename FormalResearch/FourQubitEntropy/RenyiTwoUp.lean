import FormalResearch.FourQubitEntropy.RenyiRankTwoSharp
import FormalResearch.FourQubitEntropy.Purity

/-!
# High-order Rényi purity deficit (`q ≥ 2`)

For every unit four-qubit vector and every `q ≥ 2`,
`E_q(ψ) ≤ 5/3 - (1/3) log₂(2P - 1) ≤ 5/3`, with `P = Σ_j tr ρ_{1j}²`. At `q = 2` the first bound is
sharp at every `P ∈ [1, 3/2]` (the cluster-to-Bell family), with equality iff two of the three cut
marginals are maximally mixed.

Paper: `cor:fqe-renyi-two-up` (renyi_above_one.tex). The proof is the paper's elementary argument:
`E_2 = -⅓ log₂ ∏ p_j`, the product inequality `∏(1 + x_j) ≥ 1 + Σ x_j` with `x_j = 4p_j - 1 ≥ 0`, and
monotonicity of Rényi entropy in the order.
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

open Real

theorem renyiSpec_two (l : Fin 2 × Fin 2 → ℝ) :
    renyiSpec 2 l = -Real.logb 2 (∑ i, l i ^ 2) := by
  unfold renyiSpec
  simp only [Real.rpow_two]
  rw [show (1 : ℝ) - 2 = -1 by norm_num, div_neg, div_one]

/-- `Σ (λᵢ - 1/4)² = Σ λᵢ² - 1/4` for a probability vector. -/
theorem sum_sq_sub_quarter {l : Fin 2 × Fin 2 → ℝ} (hs : ∑ i, l i = 1) :
    ∑ i, (l i - 1 / 4) ^ 2 = ∑ i, l i ^ 2 - 1 / 4 := by
  have : ∀ i, (l i - 1 / 4) ^ 2 = l i ^ 2 - (1 / 2) * l i + 1 / 16 := fun i => by ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs]
  simp; ring

theorem sum_sq_ge_quarter {l : Fin 2 × Fin 2 → ℝ} (hs : ∑ i, l i = 1) : 1 / 4 ≤ ∑ i, l i ^ 2 := by
  have := sum_sq_sub_quarter hs
  have h0 : 0 ≤ ∑ i, (l i - 1 / 4) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

theorem sum_sq_eq_quarter_iff {l : Fin 2 × Fin 2 → ℝ} (hs : ∑ i, l i = 1) :
    ∑ i, l i ^ 2 = 1 / 4 ↔ ∀ i, l i = 1 / 4 := by
  have := sum_sq_sub_quarter hs
  constructor
  · intro h
    have h0 : ∑ i, (l i - 1 / 4) ^ 2 = 0 := by linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (l i - 1 / 4))).1 h0
    intro i
    have := this i (Finset.mem_univ i)
    nlinarith [sq_nonneg (l i - 1 / 4)]
  · intro h
    have : ∑ i, (l i - 1 / 4) ^ 2 = 0 := Finset.sum_eq_zero fun i _ => by rw [h i]; norm_num
    linarith

/-- The product inequality `p₂p₃p₄ ≥ (2P-1)/32` for `p_j ≥ 1/4`, `P = Σp_j`, and its equality case. -/
theorem prod_ge {p₂ p₃ p₄ : ℝ} (h2 : 1 / 4 ≤ p₂) (h3 : 1 / 4 ≤ p₃) (h4 : 1 / 4 ≤ p₄) :
    (2 * (p₂ + p₃ + p₄) - 1) / 32 ≤ p₂ * p₃ * p₄ ∧
    ((2 * (p₂ + p₃ + p₄) - 1) / 32 = p₂ * p₃ * p₄ ↔
      (p₂ = 1 / 4 ∧ p₃ = 1 / 4) ∨ (p₂ = 1 / 4 ∧ p₄ = 1 / 4) ∨ (p₃ = 1 / 4 ∧ p₄ = 1 / 4)) := by
  obtain ⟨a, ha, rfl⟩ : ∃ a, 0 ≤ a ∧ p₂ = a + 1 / 4 := ⟨p₂ - 1 / 4, by linarith, by ring⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b, 0 ≤ b ∧ p₃ = b + 1 / 4 := ⟨p₃ - 1 / 4, by linarith, by ring⟩
  obtain ⟨c, hc, rfl⟩ : ∃ c, 0 ≤ c ∧ p₄ = c + 1 / 4 := ⟨p₄ - 1 / 4, by linarith, by ring⟩
  have key : (a + 1 / 4) * (b + 1 / 4) * (c + 1 / 4) - (2 * ((a + 1 / 4) + (b + 1 / 4) + (c + 1 / 4)) - 1) / 32
      = a * b * c + (a * b + b * c + a * c) / 4 := by ring
  have hab := mul_nonneg ha hb
  have hbc := mul_nonneg hb hc
  have hac := mul_nonneg ha hc
  have habc := mul_nonneg hab hc
  refine ⟨by nlinarith, ?_⟩
  constructor
  · intro h
    have h0 : a * b = 0 := by nlinarith
    have h1 : b * c = 0 := by nlinarith
    have h2 : a * c = 0 := by nlinarith
    rcases mul_eq_zero.1 h0 with h | h
    · rcases mul_eq_zero.1 h1 with h' | h'
      · subst h; subst h'; left; constructor <;> ring
      · subst h; subst h'; right; left; constructor <;> ring
    · rcases mul_eq_zero.1 h2 with h' | h'
      · subst h; subst h'; left; constructor <;> ring
      · subst h; subst h'; right; right; constructor <;> ring
  · intro h
    have : a * b * c + (a * b + b * c + a * c) / 4 = 0 := by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : a = 0 := by linarith
        have : b = 0 := by linarith
        subst_vars; ring
      · have : a = 0 := by linarith
        have : c = 0 := by linarith
        subst_vars; ring
      · have : b = 0 := by linarith
        have : c = 0 := by linarith
        subst_vars; ring
    linarith

theorem purity_eq_sum_sq (ψ : Psi) :
    purity ψ = ∑ i, (red12_herm ψ).eigenvalues i ^ 2 + ∑ i, (red13_herm ψ).eigenvalues i ^ 2
      + ∑ i, (red14_herm ψ).eigenvalues i ^ 2 := by
  rw [sum_eigenvalues_pow (red12_herm ψ) 2, sum_eigenvalues_pow (red13_herm ψ) 2,
    sum_eigenvalues_pow (red14_herm ψ) 2]
  unfold purity
  simp only [pow_two]

theorem meanRenyi_two (ψ : Psi) :
    meanRenyi 2 ψ = -(Real.logb 2 (∑ i, (red12_herm ψ).eigenvalues i ^ 2)
      + Real.logb 2 (∑ i, (red13_herm ψ).eigenvalues i ^ 2)
      + Real.logb 2 (∑ i, (red14_herm ψ).eigenvalues i ^ 2)) / 3 := by
  simp only [meanRenyi, renyiCut_eq_renyiSpec, renyiSpec_two]; ring

theorem two_up_prep {l₂ l₃ l₄ : Fin 2 × Fin 2 → ℝ}
    (h₂ : IsProb l₂) (h₃ : IsProb l₃) (h₄ : IsProb l₄) :
    (2 * (∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) - 1) / 32 ≤
        (∑ i, l₂ i ^ 2) * (∑ i, l₃ i ^ 2) * (∑ i, l₄ i ^ 2) ∧
      ((2 * (∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) - 1) / 32 =
        (∑ i, l₂ i ^ 2) * (∑ i, l₃ i ^ 2) * (∑ i, l₄ i ^ 2) ↔
        ((∀ i, l₂ i = 1 / 4) ∧ ∀ i, l₃ i = 1 / 4) ∨ ((∀ i, l₂ i = 1 / 4) ∧ ∀ i, l₄ i = 1 / 4) ∨
        ((∀ i, l₃ i = 1 / 4) ∧ ∀ i, l₄ i = 1 / 4)) := by
  obtain ⟨hprod, hiff⟩ := prod_ge (sum_sq_ge_quarter h₂.2) (sum_sq_ge_quarter h₃.2)
    (sum_sq_ge_quarter h₄.2)
  refine ⟨hprod, ?_⟩
  rw [hiff, sum_sq_eq_quarter_iff h₂.2, sum_sq_eq_quarter_iff h₃.2, sum_sq_eq_quarter_iff h₄.2]

theorem logb_two_32 : Real.logb 2 (32 : ℝ) = 5 := by
  rw [show (32 : ℝ) = 2 ^ (5 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]

/-- `E_2 = -⅓ log₂ ∏ p_j` and the product inequality turn into the purity bound. -/
theorem two_up_core_two {l₂ l₃ l₄ : Fin 2 × Fin 2 → ℝ}
    (h₂ : IsProb l₂) (h₃ : IsProb l₃) (h₄ : IsProb l₄) :
    (renyiSpec 2 l₂ + renyiSpec 2 l₃ + renyiSpec 2 l₄) / 3 ≤
      5 / 3 - Real.logb 2 (2 * (∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) - 1) / 3 ∧
    ((renyiSpec 2 l₂ + renyiSpec 2 l₃ + renyiSpec 2 l₄) / 3 =
      5 / 3 - Real.logb 2 (2 * (∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) - 1) / 3 ↔
      ((∀ i, l₂ i = 1 / 4) ∧ ∀ i, l₃ i = 1 / 4) ∨ ((∀ i, l₂ i = 1 / 4) ∧ ∀ i, l₄ i = 1 / 4) ∨
      ((∀ i, l₃ i = 1 / 4) ∧ ∀ i, l₄ i = 1 / 4)) := by
  obtain ⟨hprod, hiff⟩ := two_up_prep h₂ h₃ h₄
  have g2 := sum_sq_ge_quarter h₂.2
  have g3 := sum_sq_ge_quarter h₃.2
  have g4 := sum_sq_ge_quarter h₄.2
  generalize hp2 : ∑ i, l₂ i ^ 2 = p₂ at *
  generalize hp3 : ∑ i, l₃ i ^ 2 = p₃ at *
  generalize hp4 : ∑ i, l₄ i ^ 2 = p₄ at *
  have e : (renyiSpec 2 l₂ + renyiSpec 2 l₃ + renyiSpec 2 l₄) / 3 =
      -(Real.logb 2 p₂ + Real.logb 2 p₃ + Real.logb 2 p₄) / 3 := by
    rw [renyiSpec_two, renyiSpec_two, renyiSpec_two, hp2, hp3, hp4]; ring
  rw [e]
  have h2pos : 0 < 2 * (p₂ + p₃ + p₄) - 1 := by linarith
  have hlog : Real.logb 2 ((2 * (p₂ + p₃ + p₄) - 1) / 32)
      = Real.logb 2 (2 * (p₂ + p₃ + p₄) - 1) - 5 := by
    rw [Real.logb_div h2pos.ne' (by norm_num), logb_two_32]
  have hlog2 : Real.logb 2 (p₂ * p₃ * p₄) = Real.logb 2 p₂ + Real.logb 2 p₃ + Real.logb 2 p₄ := by
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity)]
  constructor
  · have := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) (by positivity)).2 hprod
    rw [hlog, hlog2] at this
    linarith
  · rw [← hiff]
    constructor
    · intro h
      have h' : Real.logb 2 ((2 * (p₂ + p₃ + p₄) - 1) / 32) = Real.logb 2 (p₂ * p₃ * p₄) := by
        rw [hlog, hlog2]; linarith
      exact Real.logb_injOn_pos (by norm_num : (1 : ℝ) < 2) (Set.mem_Ioi.2 (by positivity))
        (Set.mem_Ioi.2 (by positivity)) h'
    · intro h
      have h' := congrArg (Real.logb 2) h
      rw [hlog, hlog2] at h'
      linarith

/-- **High-order Rényi purity deficit** (`cor:fqe-renyi-two-up`): for every unit vector and
every `q ≥ 2`, `E_q(ψ) ≤ 5/3 - ⅓ log₂(2P-1) ≤ 5/3`. -/
theorem renyi_two_up {q : ℝ} (hq : 2 ≤ q) {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    meanRenyi q ψ ≤ 5 / 3 - Real.logb 2 (2 * purity ψ - 1) / 3 ∧
    5 / 3 - Real.logb 2 (2 * purity ψ - 1) / 3 ≤ 5 / 3 := by
  have hP := purity_ge ψ
  rw [hψ] at hP
  have hP1 : 1 ≤ purity ψ := by nlinarith
  have hq2 : 1 < (2 : ℝ) := by norm_num
  have m12 := renyiSpec_anti hq2 hq (isProb12 hψ).1 (isProb12 hψ).2
  have m13 := renyiSpec_anti hq2 hq (isProb13 hψ).1 (isProb13 hψ).2
  have m14 := renyiSpec_anti hq2 hq (isProb14 hψ).1 (isProb14 hψ).2
  have core := (two_up_core_two (isProb12 hψ) (isProb13 hψ) (isProb14 hψ)).1
  rw [← purity_eq_sum_sq] at core
  have hnn : 0 ≤ Real.logb 2 (2 * purity ψ - 1) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  refine ⟨?_, by linarith⟩
  have : meanRenyi q ψ ≤ meanRenyi 2 ψ := by
    simp only [meanRenyi, renyiCut_eq_renyiSpec]; linarith
  have e2 : meanRenyi 2 ψ = (renyiSpec 2 (red12_herm ψ).eigenvalues
      + renyiSpec 2 (red13_herm ψ).eigenvalues + renyiSpec 2 (red14_herm ψ).eigenvalues) / 3 := rfl
  linarith

/-- **Equality at `q = 2`**: `E_2(ψ) = 5/3 - ⅓ log₂(2P-1)` iff two of the three cut marginals
are maximally mixed (all eigenvalues `1/4`). -/
theorem renyi_two_eq_iff {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    meanRenyi 2 ψ = 5 / 3 - Real.logb 2 (2 * purity ψ - 1) / 3 ↔
      ((∀ i, (red12_herm ψ).eigenvalues i = 1 / 4) ∧ ∀ i, (red13_herm ψ).eigenvalues i = 1 / 4) ∨
      ((∀ i, (red12_herm ψ).eigenvalues i = 1 / 4) ∧ ∀ i, (red14_herm ψ).eigenvalues i = 1 / 4) ∨
      ((∀ i, (red13_herm ψ).eigenvalues i = 1 / 4) ∧ ∀ i, (red14_herm ψ).eigenvalues i = 1 / 4) := by
  have core := (two_up_core_two (isProb12 hψ) (isProb13 hψ) (isProb14 hψ)).2
  rw [← purity_eq_sum_sq] at core
  exact core

/-! ### Sharpness along the cluster-to-Bell family -/

theorem purity_quadFam {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) :
    purity (quadFam x y) = (x ^ 2) ^ 2 + (y ^ 2) ^ 2 + 1 / 2 := by
  unfold purity
  have h13 : red13 (quadFam x y) = (((1 / 4 : ℝ)) : ℂ) • (1 : Mat4) := by rw [red13_quadFam, hxy]
  have h14 : red14 (quadFam x y) = (((1 / 4 : ℝ)) : ℂ) • (1 : Mat4) := by rw [red14_quadFam, hxy]
  rw [trace_sq_red12_quadFam, h13, h14]
  simp [Matrix.trace, Matrix.smul_mul, Matrix.mul_smul, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- At `q = 2` the family `ψ_{x,y}` attains the bound of `cor:fqe-renyi-two-up`. -/
theorem renyi_two_quadFam {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) :
    meanRenyi 2 (quadFam x y) = 5 / 3 - Real.logb 2 (2 * purity (quadFam x y) - 1) / 3 :=
  (renyi_two_eq_iff (quadFam_unit hxy)).2
    (Or.inr (Or.inr ⟨quadFam_eig13 hxy, quadFam_eig14 hxy⟩))

/-- **Sharpness at `q = 2` for every purity** (`cor:fqe-renyi-two-up`): for each `P ∈ [1, 3/2]`
there is a unit vector with `purity = P` attaining the bound at `q = 2`. -/
theorem renyi_two_sharp {P : ℝ} (h1 : 1 ≤ P) (h2 : P ≤ 3 / 2) :
    ∃ ψ : Psi, normSqPsi ψ = 1 ∧ purity ψ = P ∧
      meanRenyi 2 ψ = 5 / 3 - Real.logb 2 (2 * purity ψ - 1) / 3 := by
  set r : ℝ := Real.sqrt (2 * (P - 1)) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 2 * (P - 1) := Real.sq_sqrt (by linarith)
  have hr1 : r ≤ 1 := by nlinarith
  set x : ℝ := Real.sqrt ((1 + r) / 2) with hx
  set y : ℝ := Real.sqrt ((1 - r) / 2) with hy
  have hx2 : x ^ 2 = (1 + r) / 2 := Real.sq_sqrt (by linarith)
  have hy2 : y ^ 2 = (1 - r) / 2 := Real.sq_sqrt (by linarith)
  have hxy : x ^ 2 + y ^ 2 = 1 := by rw [hx2, hy2]; ring
  refine ⟨quadFam x y, quadFam_unit hxy, ?_, renyi_two_quadFam hxy⟩
  rw [purity_quadFam hxy, hx2, hy2]
  nlinarith [hr2]

theorem renyiBin_half {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) : renyiBin q (1 / 2) = 1 := by
  have := (renyiSpec_eq_iff hq0 hq1 (l := ![(1 / 2 : ℝ), 1 - 1 / 2]) (by
    intro i; fin_cases i <;> simp <;> norm_num) (by simp [Fin.sum_univ_two])).2 (by
    intro i; fin_cases i <;> simp <;> norm_num)
  simpa [renyiBin] using this

theorem renyiBin_one {q : ℝ} (hq0 : 0 < q) : renyiBin q 1 = 0 := by
  rw [renyiBin_eq]; simp [Real.zero_rpow hq0.ne']

/-- For every `q ≥ 2` the cluster-type vector (`x² = 1/2`) attains the first bound. -/
theorem renyi_two_up_attained_cluster {q : ℝ} (hq : 2 ≤ q) :
    ∃ ψ : Psi, normSqPsi ψ = 1 ∧ purity ψ = 1 ∧
      meanRenyi q ψ = 5 / 3 - Real.logb 2 (2 * purity ψ - 1) / 3 := by
  have hxy : (Real.sqrt (1 / 2)) ^ 2 + (Real.sqrt (1 / 2)) ^ 2 = 1 := by
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  have hx2 : (Real.sqrt (1 / 2)) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hpur : purity (quadFam (Real.sqrt (1 / 2)) (Real.sqrt (1 / 2))) = 1 := by
    rw [purity_quadFam hxy, hx2]; norm_num
  refine ⟨quadFam (Real.sqrt (1 / 2)) (Real.sqrt (1 / 2)), quadFam_unit hxy, hpur, ?_⟩
  obtain ⟨-, h⟩ := renyi_rank_two_sharp (by linarith : 0 < q) (by linarith : q ≠ 1) hxy
  rw [h, hx2, renyiBin_half (by linarith) (by linarith), hpur]
  norm_num

/-- For every `q ≥ 2` the Bell-pair product (`x = 1`, `y = 0`) attains the first bound. -/
theorem renyi_two_up_attained_bell {q : ℝ} (hq : 2 ≤ q) :
    ∃ ψ : Psi, normSqPsi ψ = 1 ∧ purity ψ = 3 / 2 ∧
      meanRenyi q ψ = 5 / 3 - Real.logb 2 (2 * purity ψ - 1) / 3 := by
  have hxy : (1 : ℝ) ^ 2 + 0 ^ 2 = 1 := by norm_num
  have hpur : purity (quadFam 1 0) = 3 / 2 := by
    rw [purity_quadFam hxy]; norm_num
  refine ⟨quadFam 1 0, quadFam_unit hxy, hpur, ?_⟩
  obtain ⟨-, h⟩ := renyi_rank_two_sharp (by linarith : 0 < q) (by linarith : q ≠ 1) hxy
  rw [h, hpur]
  have : renyiBin q ((1 : ℝ) ^ 2) = 0 := by rw [one_pow]; exact renyiBin_one (by linarith)
  rw [this]
  rw [show (2 * (3 / 2 : ℝ) - 1) = 2 by norm_num, Real.logb_self_eq_one (by norm_num)]
  norm_num

/-- info: 'FormalResearch.FourQubitEntropy.renyi_two_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyi_two_up

/-- info: 'FormalResearch.FourQubitEntropy.renyi_two_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyi_two_eq_iff

/-- info: 'FormalResearch.FourQubitEntropy.renyi_two_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyi_two_sharp

/-- info: 'FormalResearch.FourQubitEntropy.renyi_two_up_attained_cluster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms renyi_two_up_attained_cluster

/-- info: 'FormalResearch.FourQubitEntropy.renyi_two_up_attained_bell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyi_two_up_attained_bell

end FormalResearch.FourQubitEntropy
