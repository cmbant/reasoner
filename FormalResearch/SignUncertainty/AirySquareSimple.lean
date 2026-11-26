module

public import FormalResearch.SignUncertainty.AirySquareKernel
public import FormalResearch.SignUncertainty.Radii
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Algebra.Polynomial.Roots

/-!
# The attained Airy square bound for distinct sites (`ce_airy_lp.tex`, Theorem `thm:airy-square-attained`)

Source: `CFT/sign_uncertainty/paper/ce_airy_lp.tex`, Theorem `thm:airy-square-attained` (1)–(3)
(distinct sites), and `CFT/sign_uncertainty/paper/ce_airy_lp_proofs.tex` (proof of
`thm:airy-square-attained`).

Indexing convention (matching `AirySquareKernel` and `FormalResearch.Special`):
`airyZ n = airyZero (n + 1)` (`n : ℕ`) lists the Dirichlet Airy zeros `a_1 > a_2 > …` with `0`-based
indices (`airyZ 0 = a_1`, `airyZ k = a_{k+1}`), so finite sections of order `M` run over `Fin M`
(`{a_1, …, a_M}`) and infinite coefficient sequences live in `lp (fun _ : ℕ => ℝ) 2`.

Main declarations:
* **Part (1):** `airyLambdaSection`, `airyLambda`, `tendsto_airyLambdaSection`,
  `airyLambdaInf_eq_airyLambda`, `isGreatest_airySquareRayleigh` (attainment on the `ℓ²` unit sphere),
  `locallyLipschitzOn_airyLambda` (local Lipschitz continuity on `{s | Function.Injective s}`),
  `airyLambda_sub_section_le_on_compact` (uniform `O(M⁻¹)` rate on compacts),
  `airyLambdaSection_first_eq_iff` (`Λ_{k+1}(s) = a_{k+1}` iff `{s_1, …, s_k} = {a_1, …, a_k}`,
  and then `λ(s) = a_{k+1}`), and `airyLambdaSection_eq_airyLambda_iff` (`Λ_M(s) = λ(s)` iff every
  site is a Dirichlet node).
* **Part (2):** `airySquare_maximizer_representation` — explicit Lagrange multipliers `μ_1, …, μ_k`,
  `O(|a_n|^{-2})` coefficient decay, `∑_n |c_n| < ∞`, and entire representation `(eq:airy-square-rep)`
  `(z - λ(s)) q_c(z) = (∑_n c_n) Ai(z) + ∑_j μ_j K(z, s_j)`.
* **Part (3):** `isGreatest_airySquareClass` (full square class optimality over real entire `q ≢ 0`
  with `q², u q² ∈ 𝒢` and `q(s_j) = 0`), `airyMaximizerWitness` (`H_λ(z) = (z - λ(s)) q_c(z)²`),
  `airyMaximizerWitness_properties` (`H_λ ∈ 𝒢`, `H_λ(s_j) = 0`, `∫ H_λ = 0`, `L_{H_λ}(y) > 0` for
  `y > 0`, weak witness at `λ(s)`, `λ(s) ≤ u_LP(s)`, `u_sh(s) ≤ u_LP(s)`), and
  `airyLambda_le_airyUSh_of_bound` (`λ(s) ≤ u_sh(s)` from `AirySquareBoundInput s`, isolating the
  deferred `lem:airy-square-bound`).
* **Bundled headlines:** `thm_airy_square_attained_simple` (unconditional) and
  `thm_airy_square_attained_simple_full` (with `AirySquareBoundInput s` for `λ(s) ≤ u_sh(s)`).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set Metric
open scoped ENNReal RealInnerProductSpace Real Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-! ### Section 1: Problem Definitions, Zero-Padding, Finite Sections, and Witness Thresholds -/

/-- Cube lower bound `8 (n + 1)² ≤ (-a_{n+1})³` valid for every `n : ℕ` (including `n = 0`). -/
lemma eight_mul_sq_le_neg_airyZ_cube (n : ℕ) :
    8 * ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (-airyZ n) ^ 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h2 : 2 < -airyZ 0 := by linarith only [airyZ_lt_neg_two 0]
    have hcube : (2 : ℝ) ^ 3 ≤ (-airyZ 0) ^ 3 := pow_le_pow_left₀ (by norm_num) h2.le 3
    norm_num at hcube ⊢
    linarith only [hcube]
  · have h := (airyZero_abs_cube_bounds (n := n + 1) (by omega)).1
    unfold airyZ
    have hsq : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := sq_nonneg _
    linarith only [h, hsq]

/-- Telescoping tail bound `∑'_{m : ℕ} 1 / (M + m + 1)² ≤ 1 / M` for `M ≥ 1`. -/
lemma tsum_inv_nat_add_sq_le {M : ℕ} (hM : 1 ≤ M) :
    (∑' m : ℕ, (1 / (((M + m + 1 : ℕ) : ℝ) ^ 2))) ≤ 1 / (M : ℝ) := by
  refine Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun N => ?_
  have hterm : ∀ m : ℕ, 1 / (((M + m + 1 : ℕ) : ℝ) ^ 2) ≤
      1 / ((M + m : ℕ) : ℝ) - 1 / ((M + (m + 1) : ℕ) : ℝ) := by
    intro m
    set x : ℝ := ((M + m : ℕ) : ℝ)
    have hx : 0 < x := by dsimp [x]; exact_mod_cast (by omega : 0 < M + m)
    have hx1 : ((M + m + 1 : ℕ) : ℝ) = x + 1 := by dsimp [x]; push_cast; ring
    have hx2 : ((M + (m + 1) : ℕ) : ℝ) = x + 1 := by dsimp [x]; push_cast; ring
    rw [hx1, hx2]
    have hdiff : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
      have hx' : x ≠ 0 := hx.ne'
      have hx1' : x + 1 ≠ 0 := (by linarith only [hx] : 0 < x + 1).ne'
      field_simp
      ring
    rw [hdiff]
    exact one_div_le_one_div_of_le (mul_pos hx (by linarith only [hx]))
      (by nlinarith only [hx])
  have hsum_le : (∑ m ∈ Finset.range N, 1 / (((M + m + 1 : ℕ) : ℝ) ^ 2)) ≤
      ∑ m ∈ Finset.range N, (1 / ((M + m : ℕ) : ℝ) - 1 / ((M + (m + 1) : ℕ) : ℝ)) :=
    Finset.sum_le_sum fun m _ => hterm m
  have htele : ∀ K : ℕ, (∑ m ∈ Finset.range K,
      (1 / ((M + m : ℕ) : ℝ) - 1 / ((M + (m + 1) : ℕ) : ℝ))) =
      1 / (M : ℝ) - 1 / ((M + K : ℕ) : ℝ) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  rw [htele N] at hsum_le
  have hpos_end : 0 ≤ 1 / ((M + N : ℕ) : ℝ) := by positivity
  linarith only [hsum_le, hpos_end]

lemma summable_inv_nat_add_sq (M : ℕ) :
    Summable (fun m : ℕ => 1 / (((M + m + 1 : ℕ) : ℝ) ^ 2)) := by
  have h := (summable_nat_add_iff (M + 1)).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  refine h.congr fun m => ?_
  have heq : m + (M + 1) = M + m + 1 := by omega
  rw [heq]

lemma memℓp_airyPad {M : ℕ} (c : Fin M → ℝ) :
    Memℓp (fun n : ℕ => if h : n < M then c ⟨n, h⟩ else 0) 2 := by
  refine memℓp_gen ?_
  refine summable_of_ne_finset_zero (s := Finset.range M) fun n hn => ?_
  have hnot : ¬ n < M := by simpa [Finset.mem_range] using hn
  simp [hnot]

/-- Zero-padding of `c : Fin M → ℝ` into `lp (fun _ : ℕ => ℝ) 2`. -/
noncomputable def airyPadLp {M : ℕ} (c : Fin M → ℝ) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨fun n => if h : n < M then c ⟨n, h⟩ else 0, memℓp_airyPad c⟩

lemma airyPadLp_apply_lt {M : ℕ} (c : Fin M → ℝ) {n : ℕ} (hn : n < M) :
    airyPadLp c n = c ⟨n, hn⟩ := by
  simp [airyPadLp, hn]

lemma airyPadLp_apply_ge {M : ℕ} (c : Fin M → ℝ) {n : ℕ} (hn : M ≤ n) :
    airyPadLp c n = 0 := by
  simp [airyPadLp, not_lt.mpr hn]

lemma hasSum_fin_of_ge_zero {M : ℕ} {f : ℕ → ℝ} (hf : ∀ n, M ≤ n → f n = 0) :
    HasSum f (∑ n : Fin M, f n.1) := by
  have h1 : HasSum f (∑ n ∈ Finset.range M, f n) :=
    hasSum_sum_of_ne_finset_zero fun n hn => hf n (not_lt.mp (by simpa [Finset.mem_range] using hn))
  have h2 : (∑ n ∈ Finset.range M, f n) = ∑ n : Fin M, f n.1 := by
    rw [← Fin.sum_univ_eq_sum_range]
  rwa [h2] at h1

lemma norm_sq_airyPadLp {M : ℕ} (c : Fin M → ℝ) :
    ‖airyPadLp c‖ ^ 2 = ∑ n : Fin M, (c n) ^ 2 := by
  have h1 := lp.hasSum_norm (p := 2) (by norm_num) (airyPadLp c)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h1
  have h2 : HasSum (fun n : ℕ => (airyPadLp c n) ^ 2) (∑ n : Fin M, (c n) ^ 2) := by
    have hfin := hasSum_fin_of_ge_zero (M := M) (f := fun n => (airyPadLp c n) ^ 2) fun n hn => by
      rw [airyPadLp_apply_ge c hn, sq, zero_mul]
    have hsum_eq : (∑ n : Fin M, (airyPadLp c n.1) ^ 2) = ∑ n : Fin M, (c n) ^ 2 := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [airyPadLp_apply_lt c n.2]
    rwa [hsum_eq] at hfin
  exact h1.unique h2

lemma summable_abs_airyZ_airyPadLp {M : ℕ} (c : Fin M → ℝ) :
    Summable (fun n : ℕ => |airyZ n| * (airyPadLp c n) ^ 2) := by
  refine summable_of_ne_finset_zero (s := Finset.range M) fun n hn => ?_
  have hnot : M ≤ n := not_lt.mp (by simpa [Finset.mem_range] using hn)
  rw [airyPadLp_apply_ge c hnot, sq, zero_mul, mul_zero]

lemma hasSum_airyZ_airyPadLp {M : ℕ} (c : Fin M → ℝ) :
    HasSum (fun n : ℕ => airyZ n * (airyPadLp c n) ^ 2) (∑ n : Fin M, airyZ n.1 * (c n) ^ 2) := by
  have hfin := hasSum_fin_of_ge_zero (M := M) (f := fun n => airyZ n * (airyPadLp c n) ^ 2)
    fun n hn => by rw [airyPadLp_apply_ge c hn, sq, zero_mul, mul_zero]
  have hsum_eq : (∑ n : Fin M, airyZ n.1 * (airyPadLp c n.1) ^ 2) =
      ∑ n : Fin M, airyZ n.1 * (c n) ^ 2 := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [airyPadLp_apply_lt c n.2]
  rwa [hsum_eq] at hfin

/-- Finite-section cardinal combination `q_c(z) = ∑_{n < M} c_n k_n(z)`. -/
noncomputable def airySectionPoly (M : ℕ) (c : Fin M → ℝ) (z : ℂ) : ℂ :=
  ∑ n : Fin M, (c n : ℂ) * airyCardinal n.1 z

/-- Real-axis finite-section cardinal combination `q_c(u) = ∑_{n < M} c_n k_n(u)`. -/
noncomputable def airySectionPolyR (M : ℕ) (c : Fin M → ℝ) (u : ℝ) : ℝ :=
  ∑ n : Fin M, c n * airyCardinalR n.1 u

lemma airyCardinalSeries_airyPadLp {M : ℕ} (c : Fin M → ℝ) (z : ℂ) :
    airyCardinalSeries (airyPadLp c) z = airySectionPoly M c z := by
  have h1 := airyCardinalSeries_hasSum (airyPadLp c) z
  have h2 : HasSum (fun n : ℕ => (airyPadLp c n : ℂ) * airyCardinal n z)
      (∑ n ∈ Finset.range M, (airyPadLp c n : ℂ) * airyCardinal n z) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by
      have hnot : M ≤ n := not_lt.mp (by simpa [Finset.mem_range] using hn)
      rw [airyPadLp_apply_ge c hnot, Complex.ofReal_zero, zero_mul]
  rw [h1.unique h2]
  unfold airySectionPoly
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [airyPadLp_apply_lt c n.2]

lemma airyCardinalSeriesR_airyPadLp {M : ℕ} (c : Fin M → ℝ) (u : ℝ) :
    airyCardinalSeriesR (airyPadLp c) u = airySectionPolyR M c u := by
  unfold airyCardinalSeriesR airySectionPolyR
  rw [airyCardinalSeries_airyPadLp]
  unfold airySectionPoly
  have hre : (∑ n : Fin M, (c n : ℂ) * airyCardinal n.1 (u : ℂ)).re =
      ∑ n : Fin M, ((c n : ℂ) * airyCardinal n.1 (u : ℂ)).re := Complex.re_sum _ _
  rw [hre]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← ofReal_airyCardinalR, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Set of constrained finite-section Rayleigh quotients (`ce_airy_lp.tex`, eq. (12)). -/
def AirySectionQuotientSet {k : ℕ} (s : Fin k → ℝ) (M : ℕ) : Set ℝ :=
  {r : ℝ | ∃ c : Fin M → ℝ, c ≠ 0 ∧ (∀ j : Fin k, airySectionPolyR M c (s j) = 0) ∧
    r = (∑ n : Fin M, airyZ n.1 * (c n) ^ 2) / (∑ n : Fin M, (c n) ^ 2)}

/-- Finite-section Rayleigh maximum `Λ_M(s)` (`ce_airy_lp.tex`, eq. (12)). -/
noncomputable def airyLambdaSection {k : ℕ} (s : Fin k → ℝ) (M : ℕ) : ℝ :=
  sSup (AirySectionQuotientSet s M)

/-- Limiting threshold `λ(s) = sup_{M ≥ k + 1} Λ_M(s)` (`ce_airy_lp.tex`, `thm:airy-square-attained`(1)). -/
noncomputable def airyLambda {k : ℕ} (s : Fin k → ℝ) : ℝ :=
  ⨆ M : {M : ℕ // k + 1 ≤ M}, airyLambdaSection s M.1

/-- Infinite constrained unit-sphere feasible set
`{c ∈ ℓ² : ∑_n c_n² = 1, ∑_n |a_n| c_n² < ∞, ∀ j, q_c(s_j) = 0}`. -/
def AirySquareUnitFeasible {k : ℕ} (s : Fin k → ℝ) (c : lp (fun _ : ℕ => ℝ) 2) : Prop :=
  HasSum (fun n : ℕ => (c n) ^ 2) 1 ∧
  Summable (fun n : ℕ => |airyZ n| * (c n) ^ 2) ∧
  ∀ j : Fin k, airyCardinalSeriesR c (s j) = 0

/-- Infinite Rayleigh functional `Q(c) = ∑_n a_n c_n²`. -/
noncomputable def airySquareRayleigh (c : lp (fun _ : ℕ => ℝ) 2) : ℝ :=
  ∑' n : ℕ, airyZ n * (c n) ^ 2

lemma airySquareRayleigh_airyPadLp {M : ℕ} (c : Fin M → ℝ) :
    airySquareRayleigh (airyPadLp c) = ∑ n : Fin M, airyZ n.1 * (c n) ^ 2 :=
  (hasSum_airyZ_airyPadLp c).tsum_eq

lemma hasSum_sq_one_iff_norm_eq_one (c : lp (fun _ : ℕ => ℝ) 2) :
    HasSum (fun n : ℕ => (c n) ^ 2) 1 ↔ ‖c‖ = 1 := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) c
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h
  constructor
  · intro h1
    have hsq : ‖c‖ ^ 2 = 1 := h.unique h1
    nlinarith only [hsq, norm_nonneg c]
  · intro hn
    rwa [hn, one_pow] at h

lemma summable_airyZ_mul_sq_iff (c : lp (fun _ : ℕ => ℝ) 2) :
    Summable (fun n : ℕ => |airyZ n| * (c n) ^ 2) ↔
      Summable (fun n : ℕ => airyZ n * (c n) ^ 2) := by
  have heq : (fun n : ℕ => airyZ n * (c n) ^ 2) =
      fun n : ℕ => -(|airyZ n| * (c n) ^ 2) := by
    ext n
    rw [abs_of_neg (airyZ_neg n)]
    ring
  rw [heq, summable_neg_iff]

lemma airySquareRayleigh_eq_neg_tsum_abs (c : lp (fun _ : ℕ => ℝ) 2) :
    airySquareRayleigh c = -∑' n : ℕ, |airyZ n| * (c n) ^ 2 := by
  unfold airySquareRayleigh
  have heq : (fun n : ℕ => airyZ n * (c n) ^ 2) =
      fun n : ℕ => -(|airyZ n| * (c n) ^ 2) := by
    ext n
    rw [abs_of_neg (airyZ_neg n)]
    ring
  rw [heq, tsum_neg]

/-- Full square class (`ce_airy_lp.tex`, `thm:airy-square-attained`(3)): real entire `q ≢ 0` with
`q², u q² ∈ 𝒢` and `q(s_j) = 0`. -/
def IsAirySquareClass {k : ℕ} (s : Fin k → ℝ) (q : ℂ → ℂ) : Prop :=
  Differentiable ℂ q ∧
  (∀ x : ℝ, (q (x : ℂ)).im = 0) ∧
  (∃ z : ℂ, q z ≠ 0) ∧
  InAiryClass (fun z => q z ^ 2) ∧
  InAiryClass (fun z => z * q z ^ 2) ∧
  ∀ j : Fin k, q (s j : ℂ) = 0

/-- Continuous Rayleigh quotient `(∫ u q(u)² du) / (∫ q(u)² du)`. -/
noncomputable def airySquareClassQuotient (q : ℂ → ℂ) : ℝ :=
  (∫ u : ℝ, u * (q (u : ℂ)).re ^ 2) / (∫ u : ℝ, (q (u : ℂ)).re ^ 2)

/-- Weak Airy LP witness at cutoff `v` for a prescribed site set `S ⊆ ℝ`
(`ce_shells.tex`, `eq:ce-witness`). -/
def IsAiryWeakWitness (S : Set ℝ) (v : ℝ) (H : ℂ → ℂ) : Prop :=
  InAiryClass H ∧
  (∃ z : ℂ, H z ≠ 0) ∧
  (∀ s ∈ S, (H (s : ℂ)).re ≤ 0) ∧
  (∀ u : ℝ, u ≤ v → (H (u : ℂ)).re ≤ 0) ∧
  (∀ y : ℝ, 0 ≤ y → 0 ≤ airyLaplace (fun u => (H (u : ℂ)).re) y)

/-- Strict-site Airy LP witness at cutoff `v` for `S ⊆ ℝ` (`ce_shells.tex`, `eq:ce-witness`). -/
def IsAiryStrictWitness (S : Set ℝ) (v : ℝ) (H : ℂ → ℂ) : Prop :=
  IsAiryWeakWitness S v H ∧ ∀ s ∈ S, (H (s : ℂ)).re < 0

/-- Weak Airy LP threshold `u_LP(S)` (`ce_shells.tex`, `eq:ce-witness`). -/
noncomputable def airyULP (S : Set ℝ) : EReal :=
  ⨆ (v : ℝ) (_ : ∃ H, IsAiryWeakWitness S v H), (v : EReal)

/-- Strict-site Airy LP threshold `u_sh(S)` (`ce_shells.tex`, `eq:ce-witness`). -/
noncomputable def airyUSh (S : Set ℝ) : EReal :=
  ⨆ (v : ℝ) (_ : ∃ H, IsAiryStrictWitness S v H), (v : EReal)

theorem airyUSh_le_airyULP (S : Set ℝ) : airyUSh S ≤ airyULP S := by
  unfold airyUSh airyULP
  refine iSup₂_le fun v hv => ?_
  obtain ⟨H, hH, _⟩ := hv
  exact le_iSup₂_of_le v ⟨H, hH⟩ le_rfl

/-- Bridge to `Radii.uLP`: for any `D : ShellHBData`, `airyULP (D.S \ {D.tm}) = uLP D`. -/
theorem airyULP_shellHBData (D : ShellHBData) :
    airyULP ((D.S : Set ℝ) \ {D.tm}) = uLP D := by
  unfold airyULP uLP
  have heq : ∀ v : ℝ,
      (∃ H, IsAiryWeakWitness ((D.S : Set ℝ) \ {D.tm}) v H) ↔ OneProfileFeasible D v := by
    intro v
    constructor
    · rintro ⟨H, h1, h2, h3, h4, h5⟩
      refine ⟨H, h1, h2, fun t ht htm => h3 t ⟨ht, htm⟩, h4, fun y hy => ?_⟩
      have hLy := h5 y hy
      unfold airyLaplace at hLy
      exact nonneg_of_mul_nonneg_right hLy (Real.exp_pos _)
    · rintro ⟨H, h1, h2, h3, h4, h5⟩
      refine ⟨H, h1, h2, fun t ht => h3 t ht.1 ht.2, h4, fun y hy => ?_⟩
      unfold airyLaplace
      exact mul_nonneg (Real.exp_pos _).le (h5 y hy)
  exact le_antisymm
    (iSup₂_le fun v hv => le_iSup₂_of_le v ((heq v).mp hv) le_rfl)
    (iSup₂_le fun v hv => le_iSup₂_of_le v ((heq v).mpr hv) le_rfl)

/-- Explicit single-field hypothesis for the distinct-site finite-section inequality of
`lem:airy-square-bound` (`ce_airy_lp_proofs.tex`), deferred by the M9 step plan and used only to
deduce `λ(s) ≤ u_sh(s)` in Part (3). -/
structure AirySquareBoundInput {k : ℕ} (s : Fin k → ℝ) : Prop where
  section_le_uSh : ∀ M : ℕ, k + 1 ≤ M → (airyLambdaSection s M : EReal) ≤ airyUSh (Set.range s)

/-! ### Finite-section attainment, monotonicity, and universal bounds -/

/-- Finite-section evaluation matrix `B_M(s)_{j,n} = k_n(s_j)`. -/
noncomputable def airyBlockMat {k : ℕ} (s : Fin k → ℝ) (M : ℕ) : Matrix (Fin k) (Fin M) ℝ :=
  Matrix.of fun j n => airyCardinalR n.1 (s j)

lemma airyBlockMat_mulVec {k M : ℕ} (s : Fin k → ℝ) (c : Fin M → ℝ) (j : Fin k) :
    (airyBlockMat s M).mulVec c j = airySectionPolyR M c (s j) := by
  simp only [Matrix.mulVec, dotProduct, airyBlockMat, Matrix.of_apply, airySectionPolyR, mul_comm]

lemma exists_nonzero_ker_airyBlockMat {k M : ℕ} (s : Fin k → ℝ) (hM : k + 1 ≤ M) :
    ∃ c : Fin M → ℝ, c ≠ 0 ∧ ∀ j : Fin k, airySectionPolyR M c (s j) = 0 := by
  let L : (Fin M → ℝ) →ₗ[ℝ] (Fin k → ℝ) := (airyBlockMat s M).mulVecLin
  have hdim : Module.finrank ℝ (LinearMap.ker L) ≠ 0 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker L
    have hdom : Module.finrank ℝ (Fin M → ℝ) = M := Module.finrank_fin_fun ℝ
    have hcod : Module.finrank ℝ (Fin k → ℝ) = k := Module.finrank_fin_fun ℝ
    have hran : Module.finrank ℝ (LinearMap.range L) ≤ k :=
      (Submodule.finrank_le (LinearMap.range L)).trans_eq hcod
    omega
  have hne_bot : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdim
    exact hdim rfl
  obtain ⟨c, hc_mem, hc_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
  refine ⟨c, hc_ne, fun j => ?_⟩
  have h0 : L c = 0 := hc_mem
  have hj := congrFun h0 j
  simpa only [L, Matrix.mulVecLin_apply, airyBlockMat_mulVec, Pi.zero_apply] using hj

lemma sum_sq_pos_of_ne_zero {M : ℕ} {c : Fin M → ℝ} (hc : c ≠ 0) :
    0 < ∑ n : Fin M, (c n) ^ 2 := by
  obtain ⟨n₀, hn₀⟩ := Function.ne_iff.mp hc
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hn₀)
    (Finset.single_le_sum (fun n _ => sq_nonneg (c n)) (Finset.mem_univ n₀))

/-- Every finite section `M ≥ k + 1` attains its Rayleigh maximum `Λ_M(s)`. -/
theorem isGreatest_airySectionQuotientSet {k M : ℕ} (s : Fin k → ℝ) (hM : k + 1 ≤ M) :
    IsGreatest (AirySectionQuotientSet s M) (airyLambdaSection s M) := by
  let U : Set (Fin M → ℝ) :=
    {c : Fin M → ℝ | (∑ n : Fin M, (c n) ^ 2) = 1 ∧ ∀ j : Fin k, airySectionPolyR M c (s j) = 0}
  have hU_sub : U ⊆ closedBall (0 : Fin M → ℝ) 1 := by
    intro c hc
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro n
    have hsq : (c n) ^ 2 ≤ 1 := by
      rw [← hc.1]
      exact Finset.single_le_sum (fun m _ => sq_nonneg (c m)) (Finset.mem_univ n)
    exact (abs_le_of_sq_le_sq' (by simpa using hsq) zero_le_one).2
  have hU_closed : IsClosed U := by
    change IsClosed ({c : Fin M → ℝ | (∑ n : Fin M, (c n) ^ 2) = 1} ∩
      {c : Fin M → ℝ | ∀ j : Fin k, airySectionPolyR M c (s j) = 0})
    refine IsClosed.inter ?_ ?_
    · exact isClosed_eq (continuous_finsetSum _ fun n _ => (continuous_apply n).pow 2)
        (continuous_const : Continuous fun _ : Fin M → ℝ => (1 : ℝ))
    · have hset : {c : Fin M → ℝ | ∀ j : Fin k, airySectionPolyR M c (s j) = 0} =
          ⋂ j : Fin k, {c : Fin M → ℝ | airySectionPolyR M c (s j) = 0} := by
        ext c; simp
      rw [hset]
      refine isClosed_iInter fun j => isClosed_eq ?_
        (continuous_const : Continuous fun _ : Fin M → ℝ => (0 : ℝ))
      unfold airySectionPolyR
      exact continuous_finsetSum _ fun n _ => (continuous_apply n).mul continuous_const
  have hU_comp : IsCompact U := IsCompact.of_isClosed_subset (isCompact_closedBall 0 1) hU_closed hU_sub
  obtain ⟨v, hv_ne, hv_ker⟩ := exists_nonzero_ker_airyBlockMat s hM
  let v₀ : Fin M → ℝ := fun n => v n / √(∑ m : Fin M, (v m) ^ 2)
  have hv₀_mem : v₀ ∈ U := by
    have hpos : 0 < ∑ m : Fin M, (v m) ^ 2 := sum_sq_pos_of_ne_zero hv_ne
    refine ⟨?_, fun j => ?_⟩
    · have hcongr : (∑ n : Fin M, (v₀ n) ^ 2) = (∑ n : Fin M, (v n) ^ 2) / (∑ m : Fin M, (v m) ^ 2) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun n _ => ?_
        dsimp [v₀]
        rw [div_pow, Real.sq_sqrt hpos.le]
      rw [hcongr, div_self hpos.ne']
    · have hj0 : (∑ n : Fin M, v n * airyCardinalR n.1 (s j)) = 0 := hv_ker j
      unfold airySectionPolyR
      have hcongr : (∑ n : Fin M, v₀ n * airyCardinalR n.1 (s j)) =
          (∑ n : Fin M, v n * airyCardinalR n.1 (s j)) / √(∑ m : Fin M, (v m) ^ 2) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun n _ => ?_
        dsimp [v₀]; ring
      rw [hcongr, hj0, zero_div]
  let f : (Fin M → ℝ) → ℝ := fun c => ∑ n : Fin M, airyZ n.1 * (c n) ^ 2
  have hf_cont : Continuous f :=
    continuous_finsetSum _ fun n _ => continuous_const.mul ((continuous_apply n).pow 2)
  have himg_eq : f '' U = AirySectionQuotientSet s M := by
    ext r
    constructor
    · rintro ⟨c, ⟨hc1, hcker⟩, rfl⟩
      have hc_ne : c ≠ 0 := by intro h0; simp [h0] at hc1
      exact ⟨c, hc_ne, hcker, by dsimp [f]; rw [hc1, div_one]⟩
    · rintro ⟨c, hc_ne, hcker, rfl⟩
      have hpos : 0 < ∑ m : Fin M, (c m) ^ 2 := sum_sq_pos_of_ne_zero hc_ne
      let u : Fin M → ℝ := fun n => c n / √(∑ m : Fin M, (c m) ^ 2)
      refine ⟨u, ⟨?_, fun j => ?_⟩, ?_⟩
      · have hcongr : (∑ n : Fin M, (u n) ^ 2) = (∑ n : Fin M, (c n) ^ 2) / (∑ m : Fin M, (c m) ^ 2) := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun n _ => ?_
          dsimp [u]
          rw [div_pow, Real.sq_sqrt hpos.le]
        rw [hcongr, div_self hpos.ne']
      · have hj0 : (∑ n : Fin M, c n * airyCardinalR n.1 (s j)) = 0 := hcker j
        unfold airySectionPolyR
        have hcongr : (∑ n : Fin M, u n * airyCardinalR n.1 (s j)) =
            (∑ n : Fin M, c n * airyCardinalR n.1 (s j)) / √(∑ m : Fin M, (c m) ^ 2) := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun n _ => ?_
          dsimp [u]; ring
        rw [hcongr, hj0, zero_div]
      · dsimp [f, u]
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [div_pow, Real.sq_sqrt hpos.le, mul_div_assoc]
  have himg_comp : IsCompact (AirySectionQuotientSet s M) :=
    himg_eq ▸ hU_comp.image hf_cont
  have himg_ne : (AirySectionQuotientSet s M).Nonempty :=
    himg_eq ▸ ⟨f v₀, ⟨v₀, hv₀_mem, rfl⟩⟩
  obtain ⟨r₀, hr₀⟩ := himg_comp.exists_isGreatest himg_ne
  have heq : airyLambdaSection s M = r₀ := hr₀.csSup_eq
  rwa [heq]

lemma exists_unit_section_maximizer {k M : ℕ} (s : Fin k → ℝ) (hM : k + 1 ≤ M) :
    ∃ c : Fin M → ℝ, (∑ n : Fin M, (c n) ^ 2) = 1 ∧
      (∀ j : Fin k, airySectionPolyR M c (s j) = 0) ∧
      (∑ n : Fin M, airyZ n.1 * (c n) ^ 2) = airyLambdaSection s M := by
  obtain ⟨⟨c, hc_ne, hcker, hceq⟩, _⟩ := isGreatest_airySectionQuotientSet s hM
  have hpos : 0 < ∑ m : Fin M, (c m) ^ 2 := sum_sq_pos_of_ne_zero hc_ne
  let u : Fin M → ℝ := fun n => c n / √(∑ m : Fin M, (c m) ^ 2)
  refine ⟨u, ?_, fun j => ?_, ?_⟩
  · have hcongr : (∑ n : Fin M, (u n) ^ 2) = (∑ n : Fin M, (c n) ^ 2) / (∑ m : Fin M, (c m) ^ 2) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun n _ => ?_
      dsimp [u]
      rw [div_pow, Real.sq_sqrt hpos.le]
    rw [hcongr, div_self hpos.ne']
  · have hj0 : (∑ n : Fin M, c n * airyCardinalR n.1 (s j)) = 0 := hcker j
    unfold airySectionPolyR
    have hcongr : (∑ n : Fin M, u n * airyCardinalR n.1 (s j)) =
        (∑ n : Fin M, c n * airyCardinalR n.1 (s j)) / √(∑ m : Fin M, (c m) ^ 2) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun n _ => ?_
      dsimp [u]; ring
    rw [hcongr, hj0, zero_div]
  · rw [hceq, Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp [u]
    rw [div_pow, Real.sq_sqrt hpos.le, mul_div_assoc]

lemma le_airyLambdaSection_of_mem {k M : ℕ} {s : Fin k → ℝ} (hM : k + 1 ≤ M)
    {r : ℝ} (hr : r ∈ AirySectionQuotientSet s M) :
    r ≤ airyLambdaSection s M :=
  (isGreatest_airySectionQuotientSet s hM).2 hr

/-- `Λ_M(s)` is nondecreasing in `M` for `M ≥ k + 1`. -/
theorem airyLambdaSection_mono {k M₁ M₂ : ℕ} (s : Fin k → ℝ)
    (h1 : k + 1 ≤ M₁) (h12 : M₁ ≤ M₂) :
    airyLambdaSection s M₁ ≤ airyLambdaSection s M₂ := by
  obtain ⟨c, hc1, hcker, hceq⟩ := exists_unit_section_maximizer s h1
  let c' : Fin M₂ → ℝ := fun n => airyPadLp c n.1
  have hpad_ge : ∀ n : ℕ, M₂ ≤ n → airyPadLp c n = 0 :=
    fun n hn => airyPadLp_apply_ge c (h12.trans hn)
  have hc'1 : (∑ n : Fin M₂, (c' n) ^ 2) = 1 := by
    have hfin := hasSum_fin_of_ge_zero (M := M₂) (f := fun n => (airyPadLp c n) ^ 2)
      fun n hn => by rw [hpad_ge n hn, sq, zero_mul]
    have htot := lp.hasSum_norm (p := 2) (by norm_num) (airyPadLp c)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at htot
    rw [norm_sq_airyPadLp, hc1] at htot
    exact hfin.unique htot
  have hc'_ne : c' ≠ 0 := by intro h0; simp [h0] at hc'1
  have hc'_ker : ∀ j : Fin k, airySectionPolyR M₂ c' (s j) = 0 := by
    intro j
    have h1' : airySectionPolyR M₂ c' (s j) = airyCardinalSeriesR (airyPadLp c) (s j) := by
      have hfin := hasSum_fin_of_ge_zero (M := M₂)
        (f := fun n => airyPadLp c n * airyCardinalR n (s j))
        fun n hn => by rw [hpad_ge n hn, zero_mul]
      have hpoly_eq : airySectionPolyR M₂ c' (s j) =
          ∑ n : Fin M₂, airyPadLp c n.1 * airyCardinalR n.1 (s j) := rfl
      rw [hpoly_eq]
      exact hfin.unique (airyCardinalSeriesR_hasSum (airyPadLp c) (s j))
    rw [h1', airyCardinalSeriesR_airyPadLp, hcker j]
  have hc'_val : (∑ n : Fin M₂, airyZ n.1 * (c' n) ^ 2) = airyLambdaSection s M₁ := by
    have hfin := hasSum_fin_of_ge_zero (M := M₂) (f := fun n => airyZ n * (airyPadLp c n) ^ 2)
      fun n hn => by rw [hpad_ge n hn, sq, zero_mul, mul_zero]
    rw [hfin.unique (hasSum_airyZ_airyPadLp c), hceq]
  exact le_airyLambdaSection_of_mem (h1.trans h12)
    ⟨c', hc'_ne, hc'_ker, by rw [hc'_val, hc'1, div_one]⟩

theorem airyZ_le_airyLambdaSection_first {k : ℕ} (s : Fin k → ℝ) :
    airyZ k ≤ airyLambdaSection s (k + 1) := by
  obtain ⟨c, hc1, _, hceq⟩ := exists_unit_section_maximizer s le_rfl
  rw [← hceq]
  calc airyZ k = airyZ k * ∑ n : Fin (k + 1), (c n) ^ 2 := by rw [hc1, mul_one]
    _ = ∑ n : Fin (k + 1), airyZ k * (c n) ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ n : Fin (k + 1), airyZ n.1 * (c n) ^ 2 := by
        refine Finset.sum_le_sum fun n _ => ?_
        exact mul_le_mul_of_nonneg_right (airyZ_anti (Nat.lt_succ_iff.mp n.2)) (sq_nonneg _)

theorem airyLambdaSection_le_airyZ_zero {k M : ℕ} (s : Fin k → ℝ) (hM : k + 1 ≤ M) :
    airyLambdaSection s M ≤ airyZ 0 := by
  obtain ⟨c, hc1, _, hceq⟩ := exists_unit_section_maximizer s hM
  rw [← hceq]
  calc (∑ n : Fin M, airyZ n.1 * (c n) ^ 2)
      ≤ ∑ n : Fin M, airyZ 0 * (c n) ^ 2 := by
        refine Finset.sum_le_sum fun n _ => ?_
        exact mul_le_mul_of_nonneg_right (airyZ_anti (Nat.zero_le n.1)) (sq_nonneg _)
    _ = airyZ 0 * ∑ n : Fin M, (c n) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ = airyZ 0 := by rw [hc1, mul_one]

lemma bddAbove_airyLambdaSection {k : ℕ} (s : Fin k → ℝ) :
    BddAbove (Set.range (fun M : {M : ℕ // k + 1 ≤ M} => airyLambdaSection s M.1)) :=
  ⟨airyZ 0, by rintro _ ⟨M, rfl⟩; exact airyLambdaSection_le_airyZ_zero s M.2⟩

theorem airyLambdaSection_le_airyLambda {k M : ℕ} (s : Fin k → ℝ) (hM : k + 1 ≤ M) :
    airyLambdaSection s M ≤ airyLambda s :=
  le_ciSup (bddAbove_airyLambdaSection s) ⟨M, hM⟩

theorem airyLambda_bounds {k : ℕ} (s : Fin k → ℝ) :
    airyZ k ≤ airyLambda s ∧ airyLambda s ≤ airyZ 0 := by
  refine ⟨(airyZ_le_airyLambdaSection_first s).trans (airyLambdaSection_le_airyLambda s le_rfl), ?_⟩
  have : Nonempty {M : ℕ // k + 1 ≤ M} := ⟨⟨k + 1, le_rfl⟩⟩
  exact ciSup_le fun M => airyLambdaSection_le_airyZ_zero s M.2

/-- `lim_{M → ∞} Λ_M(s) = λ(s)`. -/
theorem tendsto_airyLambdaSection {k : ℕ} (s : Fin k → ℝ) :
    Tendsto (airyLambdaSection s) atTop (𝓝 (airyLambda s)) := by
  have : Nonempty {M : ℕ // k + 1 ≤ M} := ⟨⟨k + 1, le_rfl⟩⟩
  have hmono : Monotone (fun M : {M : ℕ // k + 1 ≤ M} => airyLambdaSection s M.1) :=
    fun M₁ M₂ h => airyLambdaSection_mono s M₁.2 h
  have hsub := tendsto_atTop_ciSup hmono (bddAbove_airyLambdaSection s)
  rw [Metric.tendsto_atTop] at hsub ⊢
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := hsub ε hε
  refine ⟨M₀.1, fun M hM => ?_⟩
  exact hM₀ ⟨M, M₀.2.trans hM⟩ hM

/-! ### Section 2: Evaluation Map, Lipschitz Property, Row Independence, and Uniform Right Inverse -/

/-- Continuous linear evaluation operator `B(s) : ℓ² →L[ℝ] (Fin k → ℝ)`, `(B(s) c)_j = q_c(s_j)`. -/
noncomputable def airyEvalMap {k : ℕ} (s : Fin k → ℝ) :
    lp (fun _ : ℕ => ℝ) 2 →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun j => innerSL ℝ (airyEvalVec (s j))

lemma airyEvalMap_apply {k : ℕ} (s : Fin k → ℝ) (c : lp (fun _ : ℕ => ℝ) 2) (j : Fin k) :
    airyEvalMap s c j = airyCardinalSeriesR c (s j) :=
  inner_airyEvalVec (s j) c

lemma airyEvalMap_eq_zero_iff {k : ℕ} (s : Fin k → ℝ) (c : lp (fun _ : ℕ => ℝ) 2) :
    airyEvalMap s c = 0 ↔ ∀ j : Fin k, airyCardinalSeriesR c (s j) = 0 := by
  simp only [funext_iff, Pi.zero_apply, airyEvalMap_apply]

/-- Exponential majorant on `Ai'` over `[-R, ∞)`: `∃ M ≥ 0, ∀ u ≥ -R, |Ai'(u)| ≤ M e^{-(u + R)/2}`. -/
lemma exists_airyAi'_exp_bound_on_Ici (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, -R ≤ u → |airyAi' u| ≤ M * Real.exp (-(u + R) / 2) := by
  set R' := max R 0
  have hR' : 0 ≤ R' := le_max_right R 0
  have hRR' : R ≤ R' := le_max_left R 0
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc : IsCompact (Icc (-R') (R' + 2))).exists_bound_of_continuousOn
    continuous_airyAi'.continuousOn
  set M := max (max M₁ 0 * Real.exp ((2 * R' + 2) / 2)) (6 * Real.exp (R / 2))
  refine ⟨M, by positivity, fun u hu => ?_⟩
  by_cases hu_hi : u ≤ R' + 2
  · have hmem : u ∈ Icc (-R') (R' + 2) := ⟨by linarith only [hu, hRR'], hu_hi⟩
    have hb1 : |airyAi' u| ≤ max M₁ 0 := by
      have hb0 : |airyAi' u| ≤ M₁ := by simpa [Real.norm_eq_abs] using hM₁ u hmem
      exact hb0.trans (le_max_left _ _)
    have hexp_ge : 1 ≤ Real.exp ((2 * R' + 2) / 2) * Real.exp (-(u + R) / 2) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith only [hu_hi, hRR'])
    calc |airyAi' u| ≤ max M₁ 0 * 1 := by rw [mul_one]; exact hb1
      _ ≤ max M₁ 0 * (Real.exp ((2 * R' + 2) / 2) * Real.exp (-(u + R) / 2)) :=
          mul_le_mul_of_nonneg_left hexp_ge (le_max_right _ _)
      _ = (max M₁ 0 * Real.exp ((2 * R' + 2) / 2)) * Real.exp (-(u + R) / 2) := by ring
      _ ≤ M * Real.exp (-(u + R) / 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · push Not at hu_hi
    have hu1 : 1 ≤ u := by linarith only [hu_hi, hR']
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    have hAi' := airyAi'_abs_le hu0
    have hpow_neg : u ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
    have hpow_pos : u ^ (1 / 4 : ℝ) ≤ u := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
    have hpi_ge : 3 ≤ π := Real.pi_gt_three.le
    have hsqrt_pi : √π ≤ π := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      nlinarith only [hpi_ge]
    have hlin : (1 / (2 * π)) * (√π * u ^ (1 / 4 : ℝ) + u ^ (-(1 / 2 : ℝ))) ≤ u := by
      have hpos14 : 0 < u ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hu0 _
      have hmul_pi : √π * u ^ (1 / 4 : ℝ) ≤ π * u :=
        mul_le_mul hsqrt_pi hpow_pos hpos14.le (by positivity)
      have hnum : √π * u ^ (1 / 4 : ℝ) + u ^ (-(1 / 2 : ℝ)) ≤ π * u + 1 :=
        add_le_add hmul_pi hpow_neg
      rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
      nlinarith only [hnum, hu1, hpi_ge]
    have hu_exp : u ≤ 6 * Real.exp (u / 6) := by
      linarith only [Real.add_one_le_exp (u / 6)]
    have hu32 : u ≤ u ^ (3 / 2 : ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num : (1 : ℝ) ≤ 3 / 2)
    have hexp32 : Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ)) ≤ Real.exp (-(2 / 3) * u) :=
      Real.exp_le_exp.mpr (by linarith only [hu32])
    calc |airyAi' u|
        ≤ (1 / (2 * π)) * (√π * u ^ (1 / 4 : ℝ) + u ^ (-(1 / 2 : ℝ))) *
            Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ)) := hAi'
      _ ≤ u * Real.exp (-(2 / 3) * u) :=
          mul_le_mul hlin hexp32 (Real.exp_pos _).le hu0.le
      _ ≤ (6 * Real.exp (u / 6)) * Real.exp (-(2 / 3) * u) :=
          mul_le_mul_of_nonneg_right hu_exp (Real.exp_pos _).le
      _ = (6 * Real.exp (R / 2)) * Real.exp (-(u + R) / 2) := by
          rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
          congr 2; ring
      _ ≤ M * Real.exp (-(u + R) / 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

lemma integral_Ioi_exp_neg_one : (∫ t : ℝ in Ioi 0, Real.exp (-t)) = 1 := by
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt (fun w : ℝ => -Real.exp (-w)) (Real.exp (-s)) s := by
    intro s _
    exact ((hasDerivAt_neg s).exp.neg).congr_deriv (by ring)
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  have hlim : Tendsto (fun w : ℝ => -Real.exp (-w)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim
  rw [h]
  simp

/-- Lipschitz bound on `x ↦ airyEvalVec x` over `[-R, R]`. -/
theorem exists_airyEvalVec_lipschitz_on_ball (R : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, |x| ≤ R → |y| ≤ R →
      ‖airyEvalVec x - airyEvalVec y‖ ≤ L * |x - y| := by
  set R' := max R 0
  have hR' : 0 ≤ R' := le_max_right R 0
  have hRR' : R ≤ R' := le_max_left R 0
  obtain ⟨M, hM0, hMb⟩ := exists_airyAi'_exp_bound_on_Ici R'
  refine ⟨M, hM0, fun x y hx hy => ?_⟩
  have hx' : -R' ≤ x := by linarith only [(abs_le.mp hx).1, hRR']
  have hy' : -R' ≤ y := by linarith only [(abs_le.mp hy).1, hRR']
  have hpt : ∀ t : ℝ, 0 < t → |airyAi (x + t) - airyAi (y + t)| ≤
      M * Real.exp (-t / 2) * |x - y| := by
    intro t _
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
      (f := airyAi) (f' := airyAi') (s := Ici (-R' + t)) (C := M * Real.exp (-t / 2))
      (x := y + t) (y := x + t)
      (fun u _ => (hasDerivAt_airyAi u).hasDerivWithinAt)
      (fun u hu => by
        rw [Real.norm_eq_abs]
        have huR : -R' ≤ u := by linarith only [mem_Ici.mp hu, ‹0 < t›]
        have hut : t ≤ u + R' := by linarith only [mem_Ici.mp hu]
        exact (hMb u huR).trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith only [hut])) hM0))
      (convex_Ici (-R' + t))
      (mem_Ici.mpr (by linarith only [hy']))
      (mem_Ici.mpr (by linarith only [hx']))
    have hxy : (x + t) - (y + t) = x - y := by ring
    simpa only [Real.norm_eq_abs, hxy] using hmvt
  have hsq_id : ‖airyEvalVec x - airyEvalVec y‖ ^ 2 =
      ∫ t : ℝ in Ioi 0, (airyAi (x + t) - airyAi (y + t)) ^ 2 := by
    have hq := airyKer_quad x y (-1)
    have hcongr : (fun t : ℝ => (airyAi (x + t) + (-1 : ℝ) * airyAi (y + t)) ^ 2) =
        fun t : ℝ => (airyAi (x + t) - airyAi (y + t)) ^ 2 := by ext t; ring
    rw [hcongr] at hq
    rw [norm_sub_airyEvalVec_sq, hq]
    ring
  have hint_lhs : IntegrableOn (fun t : ℝ => (airyAi (x + t) - airyAi (y + t)) ^ 2) (Ioi 0) := by
    have h1 := integrableOn_airyAi_shift_sq x
    have h2 := integrableOn_airyAi_shift_sq y
    have h3 := integrableOn_airyAi_shift_mul x y
    have hsum := (h1.sub (h3.const_mul 2)).add h2
    refine hsum.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hint_rhs : IntegrableOn (fun t : ℝ => (M * |x - y|) ^ 2 * Real.exp (-t)) (Ioi 0) := by
    have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
      simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
    exact hexp.const_mul _
  have hint_le : (∫ t : ℝ in Ioi 0, (airyAi (x + t) - airyAi (y + t)) ^ 2) ≤
      (M * |x - y|) ^ 2 := by
    calc (∫ t : ℝ in Ioi 0, (airyAi (x + t) - airyAi (y + t)) ^ 2)
        ≤ ∫ t : ℝ in Ioi 0, (M * |x - y|) ^ 2 * Real.exp (-t) := by
          refine setIntegral_mono_on hint_lhs hint_rhs measurableSet_Ioi fun t ht => ?_
          have hp := hpt t ht
          have hsq : |airyAi (x + t) - airyAi (y + t)| ^ 2 ≤
              (M * Real.exp (-t / 2) * |x - y|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hp 2
          rw [sq_abs] at hsq
          refine hsq.trans (le_of_eq ?_)
          have hexp2 : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
            rw [sq, ← Real.exp_add]; congr 1; ring
          calc (M * Real.exp (-t / 2) * |x - y|) ^ 2
              = (M * |x - y|) ^ 2 * Real.exp (-t / 2) ^ 2 := by ring
            _ = (M * |x - y|) ^ 2 * Real.exp (-t) := by rw [hexp2]
      _ = (M * |x - y|) ^ 2 * (∫ t : ℝ in Ioi 0, Real.exp (-t)) := integral_const_mul _ _
      _ = (M * |x - y|) ^ 2 := by rw [integral_Ioi_exp_neg_one, mul_one]
  exact le_of_sq_le_sq (hsq_id ▸ hint_le) (mul_nonneg hM0 (abs_nonneg _))

/-- Rational-pole uniqueness: if `∑_{j ∈ T} β_j / (s_j - a_n) = 0` for all `n ≥ N₀` and `s` is
injective, then `β_j = 0` for all `j ∈ T`. -/
lemma sum_div_sub_airyZ_eq_zero {k : ℕ} {s : Fin k → ℝ} (hs : Function.Injective s)
    (T : Finset (Fin k)) (β : Fin k → ℝ) (N₀ : ℕ)
    (hne : ∀ n : ℕ, N₀ ≤ n → ∀ j ∈ T, s j ≠ airyZ n)
    (hvan : ∀ n : ℕ, N₀ ≤ n → (∑ j ∈ T, β j / (s j - airyZ n)) = 0) :
    ∀ j ∈ T, β j = 0 := by
  let Q : ℝ[X] :=
    ∑ j ∈ T, Polynomial.C (β j) * ∏ i ∈ T.erase j, (Polynomial.C (s i) - Polynomial.X)
  have hQ_eval : ∀ x : ℝ, Polynomial.eval x Q =
      ∑ j ∈ T, β j * ∏ i ∈ T.erase j, (s i - x) := by
    intro x
    simp_rw [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
  have hQ_roots : ∀ n : ℕ, N₀ ≤ n → Polynomial.IsRoot Q (airyZ n) := by
    intro n hn
    rw [Polynomial.IsRoot.def, hQ_eval]
    have hprod_eq : ∀ j ∈ T, β j * (∏ i ∈ T.erase j, (s i - airyZ n)) =
        (∏ i ∈ T, (s i - airyZ n)) * (β j / (s j - airyZ n)) := by
      intro j hj
      have hmul := (Finset.mul_prod_erase T (fun i => s i - airyZ n) hj).symm
      have hnz : s j - airyZ n ≠ 0 := sub_ne_zero.mpr (hne n hn j hj)
      rw [hmul]
      field_simp
    calc (∑ j ∈ T, β j * ∏ i ∈ T.erase j, (s i - airyZ n))
        = ∑ j ∈ T, (∏ i ∈ T, (s i - airyZ n)) * (β j / (s j - airyZ n)) :=
          Finset.sum_congr rfl fun j hj => hprod_eq j hj
      _ = (∏ i ∈ T, (s i - airyZ n)) * (∑ j ∈ T, β j / (s j - airyZ n)) :=
          (Finset.mul_sum _ _ _).symm
      _ = 0 := by rw [hvan n hn, mul_zero]
  have hQ_zero : Q = 0 := by
    by_contra hQne
    have hinf : (airyZ '' Set.Ici N₀).Infinite :=
      (Set.Ici_infinite N₀).image (airyZ_injective.injOn)
    have hsub : airyZ '' Set.Ici N₀ ⊆ (Q.roots.toFinset : Set ℝ) := by
      rintro _ ⟨n, hn, rfl⟩
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hQne]
      exact hQ_roots n (mem_Ici.mp hn)
    exact hinf ((Finset.finite_toSet _).subset hsub)
  intro j₀ hj₀
  have heval0 : Polynomial.eval (s j₀) Q = 0 := by rw [hQ_zero, Polynomial.eval_zero]
  rw [hQ_eval] at heval0
  have hsingle : (∑ j ∈ T, β j * ∏ i ∈ T.erase j, (s i - s j₀)) =
      β j₀ * ∏ i ∈ T.erase j₀, (s i - s j₀) := by
    refine Finset.sum_eq_single j₀ (fun j hj hjj₀ => ?_) (fun hnot => absurd hj₀ hnot)
    have hmem_erase : j₀ ∈ T.erase j := Finset.mem_erase.mpr ⟨hjj₀.symm, hj₀⟩
    have hprod0 : (∏ i ∈ T.erase j, (s i - s j₀)) = 0 :=
      Finset.prod_eq_zero hmem_erase (sub_self (s j₀))
    rw [hprod0, mul_zero]
  rw [hsingle] at heval0
  have hprod_ne : (∏ i ∈ T.erase j₀, (s i - s j₀)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    have hij : i ≠ j₀ := (Finset.mem_erase.mp hi).1
    exact sub_ne_zero.mpr (fun heq => hij (hs heq))
  exact (mul_eq_zero.mp heval0).resolve_right hprod_ne

lemma exists_airyZ_eq_of_airyAi_eq_zero {x : ℝ} (hx : airyAi x = 0) :
    ∃ p : ℕ, x = airyZ p := by
  have hxc : airyAiC (x : ℂ) = 0 := by rw [airyAiC_ofReal, hx, Complex.ofReal_zero]
  obtain ⟨m, hm1, hm⟩ := (airyAiC_eq_zero_iff (x : ℂ)).mp hxc
  refine ⟨m - 1, ?_⟩
  unfold airyZ
  rw [Nat.sub_add_cancel hm1]
  exact Complex.ofReal_injective hm

/-- Row independence: for distinct sites `s_1, …, s_k`, the evaluation vectors `airyEvalVec (s_j)`
are linearly independent in `ℓ²`. -/
theorem linearIndependent_airyEvalVec {k : ℕ} {s : Fin k → ℝ} (hs : Function.Injective s) :
    LinearIndependent ℝ (fun j : Fin k => airyEvalVec (s j)) := by
  rw [Fintype.linearIndependent_iff]
  intro α hα
  have hcoord : ∀ n : ℕ, (∑ j : Fin k, α j * airyCardinalR n (s j)) = 0 := by
    intro n
    have hn := congrArg (fun v : lp (fun _ : ℕ => ℝ) 2 => v n) hα
    simpa only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, airyEvalVec_apply, lp.coeFn_zero, Pi.zero_apply] using hn
  set R := (∑ i : Fin k, |s i|) + 1
  have hev := eventually_le_neg_airyZ R
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  have hlt_site : ∀ n : ℕ, N₀ ≤ n → ∀ j : Fin k, airyZ n < s j := by
    intro n hn j
    have h1 := hN₀ n hn
    have h2 : |s j| ≤ ∑ i : Fin k, |s i| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (s i)) (Finset.mem_univ j)
    have h3 : -|s j| ≤ s j := neg_abs_le (s j)
    dsimp [R] at h1
    linarith only [h1, h2, h3]
  let T : Finset (Fin k) := Finset.univ.filter (fun j : Fin k => airyAi (s j) ≠ 0)
  have hoff : ∀ j ∈ T, α j = 0 := by
    have hβ0 : ∀ j ∈ T, α j * airyAi (s j) = 0 := by
      refine sum_div_sub_airyZ_eq_zero hs T (fun j => α j * airyAi (s j)) N₀
        (fun n hn j _ => (hlt_site n hn j).ne') (fun n hn => ?_)
      have htot := hcoord n
      have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j : Fin k => airyAi (s j) ≠ 0) (fun j => α j * airyCardinalR n (s j))).symm
      rw [hsplit] at htot
      have hdir : (∑ j ∈ Finset.univ.filter (fun j : Fin k => ¬ airyAi (s j) ≠ 0),
          α j * airyCardinalR n (s j)) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hAi0 : airyAi (s j) = 0 := not_not.mp (Finset.mem_filter.mp hj).2
        obtain ⟨p, hp⟩ := exists_airyZ_eq_of_airyAi_eq_zero hAi0
        have hnp : n ≠ p := by
          intro heq
          have := hlt_site n hn j
          rw [hp, heq] at this
          exact lt_irrefl _ this
        rw [hp, airyCardinalR_airyZ]
        simp [hnp]
      rw [hdir, add_zero] at htot
      have hcongr : (∑ j ∈ T, (α j * airyAi (s j)) / (s j - airyZ n)) =
          ∑ j ∈ T, α j * airyCardinalR n (s j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [airyCardinalR_of_ne n (hlt_site n hn j).ne', mul_div_assoc]
      rw [hcongr]
      exact htot
    intro j hj
    exact (mul_eq_zero.mp (hβ0 j hj)).resolve_right (Finset.mem_filter.mp hj).2
  intro j₀
  by_cases hj₀ : j₀ ∈ T
  · exact hoff j₀ hj₀
  · have hAi0 : airyAi (s j₀) = 0 := by
      by_contra hne; exact hj₀ (Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, hne⟩)
    obtain ⟨p₀, hp₀⟩ := exists_airyZ_eq_of_airyAi_eq_zero hAi0
    have hp_eq := hcoord p₀
    have hsingle : (∑ j : Fin k, α j * airyCardinalR p₀ (s j)) =
        α j₀ * airyCardinalR p₀ (s j₀) := by
      refine Finset.sum_eq_single j₀ (fun j _ hjj₀ => ?_) (fun hnot => absurd (Finset.mem_univ j₀) hnot)
      by_cases hjT : j ∈ T
      · rw [hoff j hjT, zero_mul]
      · have hAij : airyAi (s j) = 0 := by
          by_contra hne; exact hjT (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩)
        obtain ⟨p, hp⟩ := exists_airyZ_eq_of_airyAi_eq_zero hAij
        have hpp₀ : p₀ ≠ p := by
          intro heq
          apply hjj₀
          apply hs
          rw [hp, hp₀, heq]
        rw [hp, airyCardinalR_airyZ]
        simp [hpp₀]
    simp only [hsingle, hp₀, airyCardinalR_airyZ, ↓reduceIte] at hp_eq
    exact (mul_eq_zero.mp hp_eq).resolve_right (airyAi'_airyZ_ne_zero p₀)

/-- Finite-block Gram matrix `G_J(s) = B_J(s) B_J(s)ᵀ : Matrix (Fin k) (Fin k) ℝ`. -/
noncomputable def airyGramMat {k : ℕ} (s : Fin k → ℝ) (J : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  airyBlockMat s J * (airyBlockMat s J).transpose

lemma dotProduct_airyGramMat_mulVec {k J : ℕ} (s : Fin k → ℝ) (v : Fin k → ℝ) :
    dotProduct v ((airyGramMat s J).mulVec v) =
      ∑ n : Fin J, (∑ j : Fin k, v j * airyCardinalR n.1 (s j)) ^ 2 := by
  unfold airyGramMat
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  simp only [dotProduct, Matrix.vecMul, Matrix.mulVec, airyBlockMat, Matrix.of_apply,
    Matrix.transpose_apply, sq]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1; refine Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma airyGramMat_det_ne_zero_iff {k J : ℕ} (s : Fin k → ℝ) :
    (airyGramMat s J).det ≠ 0 ↔
      ∀ v : Fin k → ℝ, (∀ n : Fin J, (∑ j : Fin k, v j * airyCardinalR n.1 (s j)) = 0) → v = 0 := by
  constructor
  · intro hdet v hv
    have hmul : (airyGramMat s J).mulVec v = 0 := by
      ext i
      unfold airyGramMat
      rw [← Matrix.mulVec_mulVec]
      have htr : (airyBlockMat s J).transpose.mulVec v = 0 := by
        ext n
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, airyBlockMat,
          Matrix.of_apply, Pi.zero_apply]
        simpa only [mul_comm] using hv n
      rw [htr, Matrix.mulVec_zero, Pi.zero_apply]
    by_contra hvne
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hvne, hmul⟩)
  · intro hinj hdet
    obtain ⟨v, hvne, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hdot : dotProduct v ((airyGramMat s J).mulVec v) = 0 := by
      rw [hmul, dotProduct_zero]
    rw [dotProduct_airyGramMat_mulVec] at hdot
    have hall0 : ∀ n : Fin J, (∑ j : Fin k, v j * airyCardinalR n.1 (s j)) = 0 := by
      intro n
      have hsq0 := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => sq_nonneg _)).mp hdot n
        (Finset.mem_univ n)
      exact sq_eq_zero_iff.mp hsq0
    exact hvne (hinj v hall0)

lemma airyGramMat_det_ne_zero_mono {k J₁ J₂ : ℕ} {s : Fin k → ℝ}
    (h1 : (airyGramMat s J₁).det ≠ 0) (h12 : J₁ ≤ J₂) :
    (airyGramMat s J₂).det ≠ 0 := by
  rw [airyGramMat_det_ne_zero_iff] at h1 ⊢
  intro v hv
  exact h1 v fun n => hv ⟨n.1, n.2.trans_le h12⟩

/-- Pointwise existence of a full-row-rank finite block `J ≥ k + 1` at distinct sites `s`. -/
theorem exists_airyGramMat_det_ne_zero {k : ℕ} {s : Fin k → ℝ} (hs : Function.Injective s) :
    ∃ J : ℕ, k + 1 ≤ J ∧ (airyGramMat s J).det ≠ 0 := by
  by_contra hno
  push Not at hno
  have hsing : ∀ m : ℕ, ∃ v : Fin k → ℝ, (∑ j : Fin k, (v j) ^ 2) = 1 ∧
      ∀ n : Fin (k + 1 + m), (∑ j : Fin k, v j * airyCardinalR n.1 (s j)) = 0 := by
    intro m
    have hdet0 := hno (k + 1 + m) (by omega)
    obtain ⟨w, hwne, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
    have hdot : dotProduct w ((airyGramMat s (k + 1 + m)).mulVec w) = 0 := by
      rw [hmul, dotProduct_zero]
    rw [dotProduct_airyGramMat_mulVec] at hdot
    have hall0 : ∀ n : Fin (k + 1 + m),
        (∑ j : Fin k, w j * airyCardinalR n.1 (s j)) = 0 := fun n =>
      sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp
        hdot n (Finset.mem_univ n))
    have hpos : 0 < ∑ j : Fin k, (w j) ^ 2 := sum_sq_pos_of_ne_zero hwne
    let v : Fin k → ℝ := fun j => w j / √(∑ i : Fin k, (w i) ^ 2)
    refine ⟨v, ?_, fun n => ?_⟩
    · have hcongr : (∑ j : Fin k, (v j) ^ 2) =
          (∑ j : Fin k, (w j) ^ 2) / (∑ i : Fin k, (w i) ^ 2) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => by dsimp [v]; rw [div_pow, Real.sq_sqrt hpos.le]
      rw [hcongr, div_self hpos.ne']
    · have hcongr : (∑ j : Fin k, v j * airyCardinalR n.1 (s j)) =
          (∑ j : Fin k, w j * airyCardinalR n.1 (s j)) / √(∑ i : Fin k, (w i) ^ 2) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => by dsimp [v]; ring
      rw [hcongr, hall0 n, zero_div]
  choose v hv1 hv0 using hsing
  let S₁ : Set (Fin k → ℝ) := {u : Fin k → ℝ | (∑ j : Fin k, (u j) ^ 2) = 1}
  have hS₁_comp : IsCompact S₁ := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin k → ℝ) 1) ?_ ?_
    · exact isClosed_eq (continuous_finsetSum _ fun j _ => (continuous_apply j).pow 2) continuous_const
    · intro u hu
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro j
      have hsq : (u j) ^ 2 ≤ 1 := by
        rw [← hu]; exact Finset.single_le_sum (fun i _ => sq_nonneg (u i)) (Finset.mem_univ j)
      exact (abs_le_of_sq_le_sq' (by simpa using hsq) zero_le_one).2
  obtain ⟨v_lim, hv_lim_S₁, φ, hφ_mono, hφ_lim⟩ := hS₁_comp.tendsto_subseq hv1
  have hall_n : ∀ n : ℕ, (∑ j : Fin k, v_lim j * airyCardinalR n (s j)) = 0 := by
    intro n
    have hcont : Continuous (fun u : Fin k → ℝ => ∑ j : Fin k, u j * airyCardinalR n (s j)) :=
      continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const
    have htend := (hcont.tendsto v_lim).comp hφ_lim
    have hev0 : ∀ᶠ m : ℕ in atTop,
        (∑ j : Fin k, v (φ m) j * airyCardinalR n (s j)) = 0 := by
      filter_upwards [eventually_ge_atTop n] with m hm
      have hφm : n ≤ φ m := hm.trans (hφ_mono.id_le m)
      exact hv0 (φ m) ⟨n, by omega⟩
    exact tendsto_nhds_unique htend (tendsto_const_nhds.congr' (hev0.mono fun _ h => h.symm))
  have hv_sum : (∑ j : Fin k, v_lim j • airyEvalVec (s j)) = 0 := by
    ext n
    simpa only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, airyEvalVec_apply, lp.coeFn_zero, Pi.zero_apply] using hall_n n
  have hv_zero : ∀ j : Fin k, v_lim j = 0 :=
    Fintype.linearIndependent_iff.mp (linearIndependent_airyEvalVec hs) v_lim hv_sum
  have h1 : (∑ j : Fin k, (v_lim j) ^ 2) = 1 := hv_lim_S₁
  simp [hv_zero] at h1

/-- Explicit right-inverse matrix `R_J(s) = B_J(s)ᵀ (B_J(s) B_J(s)ᵀ)⁻¹`. -/
noncomputable def airyRightInvMat {k : ℕ} (s : Fin k → ℝ) (J : ℕ) : Matrix (Fin J) (Fin k) ℝ :=
  (airyBlockMat s J).transpose * (airyGramMat s J)⁻¹

lemma airyBlockMat_mul_airyRightInvMat {k J : ℕ} {s : Fin k → ℝ}
    (hdet : (airyGramMat s J).det ≠ 0) :
    airyBlockMat s J * airyRightInvMat s J = 1 := by
  unfold airyRightInvMat
  rw [← Matrix.mul_assoc]
  exact Matrix.mul_nonsing_inv (airyGramMat s J) (isUnit_iff_ne_zero.mpr hdet)

lemma airyBlockMat_mulVec_airyRightInvMat {k J : ℕ} {s : Fin k → ℝ}
    (hdet : (airyGramMat s J).det ≠ 0) (v : Fin k → ℝ) :
    (airyBlockMat s J).mulVec ((airyRightInvMat s J).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, airyBlockMat_mul_airyRightInvMat hdet, Matrix.one_mulVec]

lemma continuous_airyBlockMat (k J : ℕ) :
    Continuous (fun s : Fin k → ℝ => airyBlockMat s J) := by
  refine continuous_matrix fun j n => ?_
  simp only [airyBlockMat, Matrix.of_apply]
  exact (continuous_airyCardinalR n.1).comp (continuous_apply j)

lemma continuous_airyGramMat (k J : ℕ) :
    Continuous (fun s : Fin k → ℝ => airyGramMat s J) := by
  unfold airyGramMat
  exact (continuous_airyBlockMat k J).matrix_mul (continuous_airyBlockMat k J).matrix_transpose

/-- On any compact subset `K` of distinct site vectors, there exist a common block size
`J ≥ k + 1` and a uniform entry bound `M_R ≥ 0` for `airyRightInvMat s J`. -/
theorem exists_uniform_rightInv_on_compact {k : ℕ} {K : Set (Fin k → ℝ)}
    (hK : IsCompact K) (hK_inj : ∀ s ∈ K, Function.Injective s) :
    ∃ (J : ℕ) (M_R : ℝ), k + 1 ≤ J ∧ 0 ≤ M_R ∧
      ∀ s ∈ K, (airyGramMat s J).det ≠ 0 ∧
        ∀ (n : Fin J) (j : Fin k), |airyRightInvMat s J n j| ≤ M_R := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨k + 1, 0, le_rfl, le_rfl, fun _ hs => False.elim hs⟩
  let V : {J : ℕ // k + 1 ≤ J} → Set (Fin k → ℝ) :=
    fun J => {s : Fin k → ℝ | (airyGramMat s J.1).det ≠ 0}
  have hV_open : ∀ J, IsOpen (V J) := fun J =>
    isOpen_ne_fun (continuous_airyGramMat k J.1).matrix_det continuous_const
  have hcover : K ⊆ ⋃ J : {J : ℕ // k + 1 ≤ J}, V J := by
    intro s hs
    obtain ⟨J, hJk, hdet⟩ := exists_airyGramMat_det_ne_zero (hK_inj s hs)
    exact mem_iUnion.mpr ⟨⟨J, hJk⟩, hdet⟩
  obtain ⟨F, hF_cover⟩ := hK.elim_finite_subcover V hV_open hcover
  let J₀ : ℕ := F.sup (fun J => J.1) ⊔ (k + 1)
  have hJ₀_ge : k + 1 ≤ J₀ := le_sup_right
  have hdet_K : ∀ s ∈ K, (airyGramMat s J₀).det ≠ 0 := by
    intro s hs
    have hmem := hF_cover hs
    rw [mem_iUnion₂] at hmem
    obtain ⟨J, hJF, hsJ⟩ := hmem
    have hle : J.1 ≤ J₀ := (Finset.le_sup hJF).trans le_sup_left
    exact airyGramMat_det_ne_zero_mono hsJ hle
  -- Each entry `s ↦ airyRightInvMat s J₀ p.1 p.2` is continuous on `K` via `A⁻¹ = (det A)⁻¹ • adjugate A`.
  have hentry_bdd : ∀ (p : Fin J₀ × Fin k),
      ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ K, |airyRightInvMat s J₀ p.1 p.2| ≤ B := by
    intro p
    have hc : ContinuousOn (fun s : Fin k → ℝ => airyRightInvMat s J₀ p.1 p.2) K := by
      have hform : ∀ s ∈ K, airyRightInvMat s J₀ p.1 p.2 =
          ((airyGramMat s J₀).det)⁻¹ *
            ∑ i : Fin k, airyBlockMat s J₀ i p.1 * (airyGramMat s J₀).adjugate i p.2 := by
        intro s _
        rw [Finset.mul_sum]
        simp only [airyRightInvMat, Matrix.mul_apply, Matrix.transpose_apply,
          Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl fun i _ => by ring
      refine ContinuousOn.congr ?_ hform
      have hsum_cont : Continuous (fun s : Fin k → ℝ =>
          ∑ i : Fin k, airyBlockMat s J₀ i p.1 * (airyGramMat s J₀).adjugate i p.2) :=
        continuous_finsetSum _ fun i _ =>
          ((continuous_airyBlockMat k J₀).matrix_elem i p.1).mul
            ((continuous_airyGramMat k J₀).matrix_adjugate.matrix_elem i p.2)
      exact ((continuous_airyGramMat k J₀).matrix_det.continuousOn.inv₀ hdet_K).mul
        hsum_cont.continuousOn
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
    refine ⟨max B 0, le_max_right B 0, fun s hs => ?_⟩
    have hb0 : |airyRightInvMat s J₀ p.1 p.2| ≤ B := by
      simpa [Real.norm_eq_abs] using hB s hs
    exact hb0.trans (le_max_left B 0)
  choose B hB0 hB using hentry_bdd
  refine ⟨J₀, ∑ p : Fin J₀ × Fin k, B p, hJ₀_ge,
    Finset.sum_nonneg fun p _ => hB0 p, fun s hs => ⟨hdet_K s hs, fun n j => ?_⟩⟩
  exact (hB (n, j) s hs).trans
    (Finset.single_le_sum (fun p _ => hB0 p) (Finset.mem_univ (n, j)))

/-! ### Section 3: Attainment of `airyLambdaInf` and Multiplier Representation -/

/-- Infinite constrained Rayleigh supremum `λ_*(s)` (shown equal to `airyLambda s` in Section 4). -/
noncomputable def airyLambdaInf {k : ℕ} (s : Fin k → ℝ) : ℝ :=
  sSup (airySquareRayleigh '' {c : lp (fun _ : ℕ => ℝ) 2 | AirySquareUnitFeasible s c})

lemma airyPadLp_unitFeasible {k M : ℕ} {s : Fin k → ℝ} {c : Fin M → ℝ}
    (hc1 : (∑ n : Fin M, (c n) ^ 2) = 1)
    (hcker : ∀ j : Fin k, airySectionPolyR M c (s j) = 0) :
    AirySquareUnitFeasible s (airyPadLp c) := by
  refine ⟨?_, summable_abs_airyZ_airyPadLp c, fun j => ?_⟩
  · rw [hasSum_sq_one_iff_norm_eq_one]
    have hsq := norm_sq_airyPadLp c
    rw [hc1] at hsq
    nlinarith only [hsq, norm_nonneg (airyPadLp c)]
  · rw [airyCardinalSeriesR_airyPadLp, hcker j]

lemma airySquareRayleigh_le_airyZ_zero {c : lp (fun _ : ℕ => ℝ) 2}
    (hc1 : HasSum (fun n : ℕ => (c n) ^ 2) 1)
    (hcsum : Summable (fun n : ℕ => |airyZ n| * (c n) ^ 2)) :
    airySquareRayleigh c ≤ airyZ 0 := by
  have hs1 : Summable (fun n : ℕ => airyZ n * (c n) ^ 2) :=
    (summable_airyZ_mul_sq_iff c).mp hcsum
  have hs2 : HasSum (fun n : ℕ => airyZ 0 * (c n) ^ 2) (airyZ 0) := by
    simpa only [mul_one] using hc1.mul_left (airyZ 0)
  unfold airySquareRayleigh
  exact hasSum_le (fun n => mul_le_mul_of_nonneg_right (airyZ_anti (Nat.zero_le n)) (sq_nonneg _))
    hs1.hasSum hs2

lemma bddAbove_airySquareUnitFeasible {k : ℕ} (s : Fin k → ℝ) :
    BddAbove (airySquareRayleigh '' {c : lp (fun _ : ℕ => ℝ) 2 | AirySquareUnitFeasible s c}) :=
  ⟨airyZ 0, by rintro _ ⟨c, ⟨hc1, hcsum, _⟩, rfl⟩; exact airySquareRayleigh_le_airyZ_zero hc1 hcsum⟩

lemma nonempty_airySquareUnitFeasible {k : ℕ} (s : Fin k → ℝ) :
    {c : lp (fun _ : ℕ => ℝ) 2 | AirySquareUnitFeasible s c}.Nonempty := by
  obtain ⟨c, hc1, hcker, _⟩ := exists_unit_section_maximizer s le_rfl
  exact ⟨airyPadLp c, airyPadLp_unitFeasible hc1 hcker⟩

lemma airyLambdaSection_le_airyLambdaInf {k M : ℕ} (s : Fin k → ℝ) (hM : k + 1 ≤ M) :
    airyLambdaSection s M ≤ airyLambdaInf s := by
  obtain ⟨c, hc1, hcker, hceq⟩ := exists_unit_section_maximizer s hM
  rw [← hceq, ← airySquareRayleigh_airyPadLp]
  exact le_csSup (bddAbove_airySquareUnitFeasible s)
    ⟨airyPadLp c, airyPadLp_unitFeasible hc1 hcker, rfl⟩

lemma airyLambda_le_airyLambdaInf {k : ℕ} (s : Fin k → ℝ) :
    airyLambda s ≤ airyLambdaInf s := by
  have : Nonempty {M : ℕ // k + 1 ≤ M} := ⟨⟨k + 1, le_rfl⟩⟩
  exact ciSup_le fun M => airyLambdaSection_le_airyLambdaInf s M.2

lemma airyLambdaInf_bounds {k : ℕ} (s : Fin k → ℝ) :
    airyZ k ≤ airyLambdaInf s ∧ airyLambdaInf s ≤ airyZ 0 := by
  refine ⟨(airyZ_le_airyLambdaSection_first s).trans (airyLambdaSection_le_airyLambdaInf s le_rfl), ?_⟩
  exact csSup_le ((nonempty_airySquareUnitFeasible s).image airySquareRayleigh)
    (by rintro _ ⟨c, ⟨hc1, hcsum, _⟩, rfl⟩; exact airySquareRayleigh_le_airyZ_zero hc1 hcsum)

/-- Sublevel sets of `∑_n |a_n| c_n²` inside the unit ball of `ℓ²` are totally bounded. -/
lemma totallyBounded_moment_ball (K₀ : ℝ) :
    TotallyBounded {c : lp (fun _ : ℕ => ℝ) 2 |
      ‖c‖ ≤ 1 ∧ Summable (fun n : ℕ => |airyZ n| * (c n) ^ 2) ∧
      (∑' n : ℕ, |airyZ n| * (c n) ^ 2) ≤ K₀} := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set K₁ := max K₀ 0 + 1
  have hK₁ : 0 < K₁ := by positivity
  have hev := eventually_le_neg_airyZ ((4 * K₁) / ε ^ 2)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  set δ := ε / (2 * √((N : ℝ) + 1))
  have hδ : 0 < δ := by positivity
  have htb_fin : TotallyBounded (closedBall (0 : Fin N → ℝ) 1) :=
    (isCompact_closedBall (0 : Fin N → ℝ) 1).totallyBounded
  obtain ⟨t, ht_fin, ht_cov⟩ := Metric.totallyBounded_iff.mp htb_fin δ hδ
  refine ⟨airyPadLp '' t, ht_fin.image airyPadLp, ?_⟩
  intro c hc
  obtain ⟨hc_norm, hc_sum, hc_le⟩ := hc
  let c_fin : Fin N → ℝ := fun i => c i.1
  have hc_fin_mem : c_fin ∈ closedBall (0 : Fin N → ℝ) 1 := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hle := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) c i.1
    rw [Real.norm_eq_abs] at hle
    exact hle.trans hc_norm
  have hcov := ht_cov hc_fin_mem
  rw [mem_iUnion₂] at hcov
  obtain ⟨x, hxt, hdist⟩ := hcov
  rw [mem_iUnion₂]
  refine ⟨airyPadLp x, ⟨x, hxt, rfl⟩, ?_⟩
  rw [mem_ball, dist_eq_norm]
  have hnorm_sq := lp.hasSum_norm (p := 2) (by norm_num) (c - airyPadLp x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, lp.coeFn_sub, Pi.sub_apply,
    Real.norm_eq_abs, sq_abs] at hnorm_sq
  have hhead_le : (∑ n ∈ Finset.range N, (c n - airyPadLp x n) ^ 2) ≤ ε ^ 2 / 4 := by
    have hsum_eq : (∑ n ∈ Finset.range N, (c n - airyPadLp x n) ^ 2) =
        ∑ i : Fin N, (c_fin i - x i) ^ 2 := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [airyPadLp_apply_lt x i.2]
    rw [hsum_eq]
    have hdx : ‖c_fin - x‖ < δ := by rwa [mem_ball, dist_eq_norm] at hdist
    have hcoord : ∀ i : Fin N, (c_fin i - x i) ^ 2 ≤ δ ^ 2 := by
      intro i
      have hi : |c_fin i - x i| ≤ δ := (norm_le_pi_norm (c_fin - x) i).trans hdx.le
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hi 2
      rwa [sq_abs] at hsq
    calc (∑ i : Fin N, (c_fin i - x i) ^ 2)
        ≤ ∑ _i : Fin N, δ ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
      _ = (N : ℝ) * δ ^ 2 := by simp
      _ = (N : ℝ) / ((N : ℝ) + 1) * (ε ^ 2 / 4) := by
          dsimp [δ]
          rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
          field_simp
          ring
      _ ≤ 1 * (ε ^ 2 / 4) := by
          gcongr
          rw [div_le_one (by positivity)]
          linarith only
      _ = ε ^ 2 / 4 := one_mul _
  have htail_le : ∀ M : ℕ, (∑ m ∈ Finset.range M, (c (N + m) - airyPadLp x (N + m)) ^ 2) ≤
      ε ^ 2 / 4 := by
    intro M
    have hcongr : (∑ m ∈ Finset.range M, (c (N + m) - airyPadLp x (N + m)) ^ 2) =
        ∑ m ∈ Finset.range M, (c (N + m)) ^ 2 := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [airyPadLp_apply_ge x (Nat.le_add_right N m), sub_zero]
    rw [hcongr]
    have hterm : ∀ m : ℕ, (c (N + m)) ^ 2 ≤
        (ε ^ 2 / (4 * K₁)) * (|airyZ (N + m)| * (c (N + m)) ^ 2) := by
      intro m
      have ha : (4 * K₁) / ε ^ 2 ≤ |airyZ (N + m)| := by
        rw [abs_of_neg (airyZ_neg _)]
        exact hN (N + m) (Nat.le_add_right N m)
      have h1 : 1 ≤ (ε ^ 2 / (4 * K₁)) * |airyZ (N + m)| := by
        have hpos_eps : 0 < ε ^ 2 / (4 * K₁) := by positivity
        have hmul := mul_le_mul_of_nonneg_left ha hpos_eps.le
        have hlhs : (ε ^ 2 / (4 * K₁)) * ((4 * K₁) / ε ^ 2) = 1 := by
          have : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε.ne'
          have : 4 * K₁ ≠ 0 := by positivity
          field_simp
        rwa [hlhs] at hmul
      nlinarith only [h1, sq_nonneg (c (N + m))]
    have hpart_le : (∑ m ∈ Finset.range M, |airyZ (N + m)| * (c (N + m)) ^ 2) ≤ K₀ := by
      have hsub : (Finset.range M).image (fun m => N + m) ⊆ Finset.range (N + M) := by
        intro k hk
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
        exact Finset.mem_range.mpr (Nat.add_lt_add_left (Finset.mem_range.mp hm) N)
      have himg : (∑ m ∈ Finset.range M, |airyZ (N + m)| * (c (N + m)) ^ 2) =
          ∑ k ∈ (Finset.range M).image (fun m => N + m), |airyZ k| * (c k) ^ 2 := by
        rw [Finset.sum_image (fun m₁ _ m₂ _ h => Nat.add_left_cancel h)]
      rw [himg]
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))).trans
        ((hc_sum.sum_le_tsum _ fun k _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)).trans hc_le)
    calc (∑ m ∈ Finset.range M, (c (N + m)) ^ 2)
        ≤ ∑ m ∈ Finset.range M, (ε ^ 2 / (4 * K₁)) * (|airyZ (N + m)| * (c (N + m)) ^ 2) :=
          Finset.sum_le_sum fun m _ => hterm m
      _ = (ε ^ 2 / (4 * K₁)) * ∑ m ∈ Finset.range M, |airyZ (N + m)| * (c (N + m)) ^ 2 :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (ε ^ 2 / (4 * K₁)) * K₀ :=
          mul_le_mul_of_nonneg_left hpart_le (by positivity)
      _ ≤ (ε ^ 2 / (4 * K₁)) * K₁ := by
          gcongr
          dsimp [K₁]
          linarith only [le_max_left K₀ 0]
      _ = ε ^ 2 / 4 := by field_simp
  have htot_le : ‖c - airyPadLp x‖ ^ 2 ≤ ε ^ 2 / 2 := by
    rw [← hnorm_sq.tsum_eq]
    refine Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) fun L => ?_
    by_cases hLN : L ≤ N
    · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hLN)
        (fun _ _ _ => sq_nonneg _)).trans (by linarith only [hhead_le, sq_pos_of_pos hε])
    · push Not at hLN
      obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hLN.le
      rw [Finset.sum_range_add]
      linarith only [hhead_le, htail_le M]
  have hstrict : ‖c - airyPadLp x‖ ^ 2 < ε ^ 2 := by
    linarith only [htot_le, sq_pos_of_pos hε]
  nlinarith only [hstrict, norm_nonneg (c - airyPadLp x), hε]

/-- Attainment of `airyLambdaInf s` on `AirySquareUnitFeasible s`. -/
theorem exists_airyLambdaInf_maximizer {k : ℕ} (s : Fin k → ℝ) :
    ∃ c : lp (fun _ : ℕ => ℝ) 2,
      AirySquareUnitFeasible s c ∧ airySquareRayleigh c = airyLambdaInf s := by
  have happrox : ∀ m : ℕ, ∃ c : lp (fun _ : ℕ => ℝ) 2,
      AirySquareUnitFeasible s c ∧
      airyLambdaInf s - 1 / ((m : ℝ) + 1) < airySquareRayleigh c := by
    intro m
    have hlt : airyLambdaInf s - 1 / ((m : ℝ) + 1) < airyLambdaInf s := by
      have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith only [this]
    obtain ⟨_, ⟨c, hc, rfl⟩, hcr⟩ := exists_lt_of_lt_csSup
      ((nonempty_airySquareUnitFeasible s).image airySquareRayleigh) hlt
    exact ⟨c, hc, hcr⟩
  choose u hu_feas hu_gt using happrox
  set K₀ := 1 - airyLambdaInf s
  let S₀ : Set (lp (fun _ : ℕ => ℝ) 2) :=
    {c : lp (fun _ : ℕ => ℝ) 2 |
      ‖c‖ ≤ 1 ∧ Summable (fun n : ℕ => |airyZ n| * (c n) ^ 2) ∧
      (∑' n : ℕ, |airyZ n| * (c n) ^ 2) ≤ K₀}
  have hu_mem : ∀ m : ℕ, u m ∈ closure S₀ := by
    intro m
    refine subset_closure ⟨?_, (hu_feas m).2.1, ?_⟩
    · rw [(hasSum_sq_one_iff_norm_eq_one (u m)).mp (hu_feas m).1]
    · have hgt := hu_gt m
      rw [airySquareRayleigh_eq_neg_tsum_abs] at hgt
      have h1 : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 :=
        div_le_one_of_le₀ (by linarith only [Nat.cast_nonneg (α := ℝ) m]) (by positivity)
      dsimp [K₀]
      linarith only [hgt, h1]
  have hcomp : IsCompact (closure S₀) :=
    isCompact_iff_totallyBounded_isComplete.mpr
      ⟨(totallyBounded_moment_ball K₀).closure, isClosed_closure.isComplete⟩
  obtain ⟨c, _, φ, hφ_mono, hφ_lim⟩ := hcomp.tendsto_subseq hu_mem
  have hc_norm : ‖c‖ = 1 := by
    have ht1 : Tendsto (fun m => ‖u (φ m)‖) atTop (𝓝 ‖c‖) := hφ_lim.norm
    have ht2 : ∀ m, ‖u (φ m)‖ = 1 := fun m =>
      (hasSum_sq_one_iff_norm_eq_one _).mp (hu_feas (φ m)).1
    exact tendsto_nhds_unique ht1 (tendsto_const_nhds.congr fun m => (ht2 m).symm)
  have hc_ker : ∀ j : Fin k, airyCardinalSeriesR c (s j) = 0 := by
    rw [← airyEvalMap_eq_zero_iff]
    have ht1 : Tendsto (fun m => airyEvalMap s (u (φ m))) atTop (𝓝 (airyEvalMap s c)) :=
      ((airyEvalMap s).continuous.tendsto c).comp hφ_lim
    have ht2 : ∀ m, airyEvalMap s (u (φ m)) = 0 := fun m =>
      (airyEvalMap_eq_zero_iff s _).mpr (hu_feas (φ m)).2.2
    exact tendsto_nhds_unique ht1 (tendsto_const_nhds.congr fun m => (ht2 m).symm)
  have hcoord_lim : ∀ n : ℕ, Tendsto (fun m => u (φ m) n) atTop (𝓝 (c n)) := by
    intro n
    rw [Metric.tendsto_atTop] at hφ_lim ⊢
    intro ε hε
    obtain ⟨M₀, hM₀⟩ := hφ_lim ε hε
    refine ⟨M₀, fun m hm => ?_⟩
    have h1 := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (u (φ m) - c) n
    have h2 : dist (u (φ m)) c < ε := hM₀ m hm
    rw [dist_eq_norm] at h2 ⊢
    exact h1.trans_lt h2
  have hrange_le : ∀ M : ℕ, (∑ n ∈ Finset.range M, |airyZ n| * (c n) ^ 2) ≤ -airyLambdaInf s := by
    intro M
    have ht_sum : Tendsto (fun m => ∑ n ∈ Finset.range M, |airyZ n| * (u (φ m) n) ^ 2)
        atTop (𝓝 (∑ n ∈ Finset.range M, |airyZ n| * (c n) ^ 2)) :=
      tendsto_finsetSum _ fun n _ => tendsto_const_nhds.mul ((hcoord_lim n).pow 2)
    have ht_ub : Tendsto (fun m : ℕ => -airyLambdaInf s + 1 / ((φ m : ℝ) + 1))
        atTop (𝓝 (-airyLambdaInf s + 0)) := by
      refine tendsto_const_nhds.add ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ_mono.tendsto_atTop
    rw [add_zero] at ht_ub
    refine le_of_tendsto_of_tendsto ht_sum ht_ub (Eventually.of_forall fun m => ?_)
    have h1 : (∑ n ∈ Finset.range M, |airyZ n| * (u (φ m) n) ^ 2) ≤
        ∑' n : ℕ, |airyZ n| * (u (φ m) n) ^ 2 :=
      (hu_feas (φ m)).2.1.sum_le_tsum _ fun n _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
    have h2 := hu_gt (φ m)
    rw [airySquareRayleigh_eq_neg_tsum_abs] at h2
    linarith only [h1, h2]
  have hc_sum : Summable (fun n : ℕ => |airyZ n| * (c n) ^ 2) :=
    summable_of_sum_range_le (fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) hrange_le
  have hc_feas : AirySquareUnitFeasible s c :=
    ⟨(hasSum_sq_one_iff_norm_eq_one c).mpr hc_norm, hc_sum, hc_ker⟩
  have hc_ge : airyLambdaInf s ≤ airySquareRayleigh c := by
    have htsum_le : (∑' n : ℕ, |airyZ n| * (c n) ^ 2) ≤ -airyLambdaInf s :=
      Real.tsum_le_of_sum_range_le (fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) hrange_le
    rw [airySquareRayleigh_eq_neg_tsum_abs]
    linarith only [htsum_le]
  have hc_le : airySquareRayleigh c ≤ airyLambdaInf s :=
    le_csSup (bddAbove_airySquareUnitFeasible s) ⟨c, hc_feas, rfl⟩
  exact ⟨c, hc_feas, le_antisymm hc_le hc_ge⟩

lemma summable_shifted_bilinear {c w : lp (fun _ : ℕ => ℝ) 2} (v : ℝ)
    (hc : Summable (fun n : ℕ => |airyZ n| * (c n) ^ 2))
    (hw : Summable (fun n : ℕ => |airyZ n| * (w n) ^ 2)) :
    Summable (fun n : ℕ => (airyZ n - v) * c n * w n) := by
  have hc2 : Summable (fun n : ℕ => (c n) ^ 2) := by
    have h := (lp.hasSum_norm (p := 2) (by norm_num) c).summable
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h
  have hw2 : Summable (fun n : ℕ => (w n) ^ 2) := by
    have h := (lp.hasSum_norm (p := 2) (by norm_num) w).summable
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h
  have hdom : Summable (fun n : ℕ =>
      (1 / 2 : ℝ) * (|airyZ n| * (c n) ^ 2 + |airyZ n| * (w n) ^ 2 +
        |v| * ((c n) ^ 2 + (w n) ^ 2))) :=
    ((hc.add hw).add ((hc2.add hw2).mul_left |v|)).mul_left (1 / 2 : ℝ)
  refine Summable.of_norm_bounded hdom fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have hav : |airyZ n - v| ≤ |airyZ n| + |v| := abs_sub _ _
  have hcw : |c n| * |w n| ≤ ((c n) ^ 2 + (w n) ^ 2) / 2 := by
    have hsq : 0 ≤ (|c n| - |w n|) ^ 2 := sq_nonneg _
    nlinarith only [hsq, sq_abs (c n), sq_abs (w n)]
  have hprod : |airyZ n - v| * (|c n| * |w n|) ≤
      (|airyZ n| + |v|) * (((c n) ^ 2 + (w n) ^ 2) / 2) :=
    mul_le_mul hav hcw (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
  linarith only [hprod,
    show (|airyZ n| + |v|) * (((c n) ^ 2 + (w n) ^ 2) / 2) =
      (1 / 2 : ℝ) * (|airyZ n| * (c n) ^ 2 + |airyZ n| * (w n) ^ 2 +
        |v| * ((c n) ^ 2 + (w n) ^ 2)) by ring]

/-- First-variation stationarity at a maximizer `c` of `airyLambdaInf s`. -/
lemma airyLambdaInf_stationarity {k : ℕ} {s : Fin k → ℝ} {c w : lp (fun _ : ℕ => ℝ) 2}
    (hc : AirySquareUnitFeasible s c) (hc_max : airySquareRayleigh c = airyLambdaInf s)
    (hw_sum : Summable (fun n : ℕ => |airyZ n| * (w n) ^ 2))
    (hw_ker : ∀ j : Fin k, airyCardinalSeriesR w (s j) = 0) :
    (∑' n : ℕ, (airyZ n - airyLambdaInf s) * c n * w n) = 0 := by
  set lam := airyLambdaInf s
  set A := ∑' n : ℕ, (airyZ n - lam) * c n * w n
  set D := ∑' n : ℕ, (airyZ n - lam) * (w n) ^ 2
  have hc2 : HasSum (fun n : ℕ => (c n) ^ 2) 1 := hc.1
  have hw2 : Summable (fun n : ℕ => (w n) ^ 2) := by
    have h := (lp.hasSum_norm (p := 2) (by norm_num) w).summable
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h
  have hsC : HasSum (fun n : ℕ => (airyZ n - lam) * (c n) ^ 2) 0 := by
    have h1 : HasSum (fun n : ℕ => airyZ n * (c n) ^ 2) lam := by
      rw [← hc_max]; exact ((summable_airyZ_mul_sq_iff c).mp hc.2.1).hasSum
    have h2 : HasSum (fun n : ℕ => lam * (c n) ^ 2) lam := by
      simpa only [mul_one] using hc2.mul_left lam
    have hsub := h1.sub h2
    rw [sub_self] at hsub
    exact hsub.congr_fun fun n => by ring
  have hsA : HasSum (fun n : ℕ => (airyZ n - lam) * c n * w n) A :=
    (summable_shifted_bilinear lam hc.2.1 hw_sum).hasSum
  have hsD : HasSum (fun n : ℕ => (airyZ n - lam) * (w n) ^ 2) D := by
    have hsumD : Summable (fun n : ℕ => (airyZ n - lam) * (w n) ^ 2) :=
      (((summable_airyZ_mul_sq_iff w).mp hw_sum).sub (hw2.mul_left lam)).congr fun n => by ring
    exact hsumD.hasSum
  -- Perturb `c + t • w` for `|t| * (‖w‖ + 1) < 1 / 2`.
  have hineq : ∀ t : ℝ, |t| * (‖w‖ + 1) < 1 / 2 → 2 * t * A + t ^ 2 * D ≤ 0 := by
    intro t ht
    let u : lp (fun _ : ℕ => ℝ) 2 := c + t • w
    have hun : ∀ n : ℕ, u n = c n + t * w n :=
      fun n => by rw [lp.coeFn_add, lp.coeFn_smul]; rfl
    have hu_norm_pos : 0 < ‖u‖ := by
      have hc1 : ‖c‖ = 1 := (hasSum_sq_one_iff_norm_eq_one c).mp hc.1
      have htri := norm_add_le (c + t • w) (-(t • w))
      rw [add_neg_cancel_right, norm_neg] at htri
      have htw : ‖t • w‖ ≤ |t| * (‖w‖ + 1) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (by linarith only [norm_nonneg w]) (abs_nonneg t)
      change 0 < ‖c + t • w‖
      linarith only [hc1, htri, htw, ht]
    have hu_sum : Summable (fun n : ℕ => |airyZ n| * (u n) ^ 2) := by
      have hdom : Summable (fun n : ℕ => 2 * (|airyZ n| * (c n) ^ 2) +
          (2 * t ^ 2) * (|airyZ n| * (w n) ^ 2)) :=
        (hc.2.1.mul_left 2).add (hw_sum.mul_left (2 * t ^ 2))
      refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
        (fun n => ?_) hdom
      rw [hun n]
      have hsq : (c n + t * w n) ^ 2 ≤ 2 * (c n) ^ 2 + 2 * t ^ 2 * (w n) ^ 2 := by
        nlinarith only [sq_nonneg (c n - t * w n)]
      have hmul := mul_le_mul_of_nonneg_left hsq (abs_nonneg (airyZ n))
      linarith only [hmul]
    have hu_ker : ∀ j : Fin k, airyCardinalSeriesR u (s j) = 0 := by
      rw [← airyEvalMap_eq_zero_iff]
      change airyEvalMap s (c + t • w) = 0
      rw [map_add, map_smul, (airyEvalMap_eq_zero_iff s c).mpr hc.2.2,
        (airyEvalMap_eq_zero_iff s w).mpr hw_ker, smul_zero, add_zero]
    let u_unit : lp (fun _ : ℕ => ℝ) 2 := (‖u‖⁻¹ : ℝ) • u
    have hu_unit_n : ∀ n : ℕ, u_unit n = ‖u‖⁻¹ * u n :=
      fun n => by simp [u_unit, Pi.smul_apply, smul_eq_mul]
    have hu_unit_feas : AirySquareUnitFeasible s u_unit := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hasSum_sq_one_iff_norm_eq_one]
        change ‖(‖u‖⁻¹ : ℝ) • u‖ = 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu_norm_pos),
          inv_mul_cancel₀ hu_norm_pos.ne']
      · have h := hu_sum.mul_left ((‖u‖⁻¹) ^ 2)
        refine h.congr fun n => ?_
        rw [hu_unit_n n]
        ring
      · rw [← airyEvalMap_eq_zero_iff]
        change airyEvalMap s ((‖u‖⁻¹ : ℝ) • u) = 0
        rw [map_smul, (airyEvalMap_eq_zero_iff s u).mpr hu_ker, smul_zero]
    have hray_le : airySquareRayleigh u_unit ≤ lam :=
      le_csSup (bddAbove_airySquareUnitFeasible s) ⟨u_unit, hu_unit_feas, rfl⟩
    have hray_eq : airySquareRayleigh u_unit = (‖u‖⁻¹) ^ 2 * airySquareRayleigh u := by
      unfold airySquareRayleigh
      rw [← tsum_mul_left]
      congr 1; ext n
      rw [hu_unit_n n]
      ring
    rw [hray_eq] at hray_le
    have hmul_u : airySquareRayleigh u - lam * ‖u‖ ^ 2 ≤ 0 := by
      have hm := mul_le_mul_of_nonneg_left hray_le (sq_nonneg ‖u‖)
      have hlhs : ‖u‖ ^ 2 * ((‖u‖⁻¹) ^ 2 * airySquareRayleigh u) = airySquareRayleigh u := by
        have hne : ‖u‖ ≠ 0 := hu_norm_pos.ne'
        field_simp
      rw [hlhs] at hm
      linarith only [hm]
    have hquad_hasSum : HasSum (fun n : ℕ => (airyZ n - lam) * (u n) ^ 2)
        (2 * t * A + t ^ 2 * D) := by
      have hcomb := (hsC.add (hsA.mul_left (2 * t))).add (hsD.mul_left (t ^ 2))
      rw [zero_add] at hcomb
      refine hcomb.congr_fun fun n => ?_
      rw [hun n]
      ring
    have hquad_eq : airySquareRayleigh u - lam * ‖u‖ ^ 2 = 2 * t * A + t ^ 2 * D := by
      have hu1 := ((summable_airyZ_mul_sq_iff u).mp hu_sum).hasSum
      have hu2_norm := lp.hasSum_norm (p := 2) (by norm_num) u
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at hu2_norm
      have hdiff := hu1.sub (hu2_norm.mul_left lam)
      have hcongr : (fun n : ℕ => airyZ n * (u n) ^ 2 - lam * (u n) ^ 2) =
          fun n : ℕ => (airyZ n - lam) * (u n) ^ 2 := by ext n; ring
      rw [hcongr] at hdiff
      exact hdiff.unique hquad_hasSum
    rwa [hquad_eq] at hmul_u
  by_contra hAne
  set δ := min (1 / (4 * (‖w‖ + 1))) (|A| / (|D| + 1))
  have hδ_pos : 0 < δ := by
    have hApos : 0 < |A| := abs_pos.mpr hAne
    positivity
  have hδ_small : δ * (‖w‖ + 1) < 1 / 2 := by
    have hle : δ ≤ 1 / (4 * (‖w‖ + 1)) := min_le_left _ _
    have hpos : 0 < ‖w‖ + 1 := by positivity
    have hm := mul_le_mul_of_nonneg_right hle hpos.le
    have heq : 1 / (4 * (‖w‖ + 1)) * (‖w‖ + 1) = 1 / 4 := by field_simp
    rw [heq] at hm
    linarith only [hm]
  have hδD : δ * |D| < |A| := by
    have hle : δ ≤ |A| / (|D| + 1) := min_le_right _ _
    have hApos : 0 < |A| := abs_pos.mpr hAne
    calc δ * |D| ≤ (|A| / (|D| + 1)) * |D| := mul_le_mul_of_nonneg_right hle (abs_nonneg D)
      _ < (|A| / (|D| + 1)) * (|D| + 1) :=
          mul_lt_mul_of_pos_left (by linarith only) (div_pos hApos (by positivity))
      _ = |A| := div_mul_cancel₀ |A| (by positivity)
  have hδ2D_nn : 0 ≤ δ ^ 2 * |D| := mul_nonneg (sq_nonneg δ) (abs_nonneg D)
  rcases lt_or_gt_of_ne hAne with hneg | hpos
  · have h := hineq (-δ) (by rwa [abs_neg, abs_of_pos hδ_pos])
    have habsA : |A| = -A := abs_of_neg hneg
    have hD_ge : -|D| ≤ D := neg_abs_le D
    have hD_bound : -(δ ^ 2 * |D|) ≤ δ ^ 2 * D := by
      nlinarith only [hD_ge, sq_nonneg δ]
    have hmulδ := mul_lt_mul_of_pos_left hδD hδ_pos
    rw [← mul_assoc, ← sq, habsA] at hmulδ
    have hlin : 2 * -δ * A + (-δ) ^ 2 * D = 2 * (δ * -A) + δ ^ 2 * D := by ring
    rw [hlin] at h
    linarith only [h, hD_bound, hmulδ, hδ2D_nn]
  · have h := hineq δ (by rwa [abs_of_pos hδ_pos])
    have habsA : |A| = A := abs_of_pos hpos
    have hD_ge : -|D| ≤ D := neg_abs_le D
    have hD_bound : -(δ ^ 2 * |D|) ≤ δ ^ 2 * D := by
      nlinarith only [hD_ge, sq_nonneg δ]
    have hmulδ := mul_lt_mul_of_pos_left hδD hδ_pos
    rw [← mul_assoc, ← sq, habsA] at hmulδ
    rw [mul_assoc] at h
    linarith only [h, hD_bound, hmulδ, hδ2D_nn]

/-- Explicit uniform decay constant `M_c(k, J, M_R, R_s)` for `|c_n| ≤ M_c / a_n²`. -/
noncomputable def airyDecayConst (k J : ℕ) (M_R R_s : ℝ) : ℝ :=
  max ((2 * max |airyZ J| R_s + 1) ^ 2)
    (12 * (k : ℝ) * ((J : ℝ) * (|airyZ J| + |airyZ 0|) * M_R))

lemma airyDecayConst_nonneg (k J : ℕ) (M_R R_s : ℝ) :
    0 ≤ airyDecayConst k J M_R R_s :=
  (sq_nonneg _).trans (le_max_left _ _)

/-- Explicit Lagrange multipliers, uniform coefficient decay `|c_n| ≤ M_c / a_n²`, absolute
summability `∑_n |c_n| < ∞`, and entire representation `(eq:airy-square-rep)` from a full-rank
block `(J, M_R)`. -/
lemma airyLambdaInf_multiplier_rep_from_block {k J : ℕ} {s : Fin k → ℝ} {M_R R_s : ℝ}
    (hJ_pos : k + 1 ≤ J) (_hMR : 0 ≤ M_R) (hRs : (∑ j : Fin k, |s j|) ≤ R_s)
    (hdet : (airyGramMat s J).det ≠ 0)
    (hR_bound : ∀ (n : Fin J) (j : Fin k), |airyRightInvMat s J n j| ≤ M_R)
    {c : lp (fun _ : ℕ => ℝ) 2} (hc : AirySquareUnitFeasible s c)
    (hc_max : airySquareRayleigh c = airyLambdaInf s) :
    ∃ μ : Fin k → ℝ,
      (∀ j : Fin k, |μ j| ≤ (J : ℝ) * (|airyZ J| + |airyZ 0|) * M_R) ∧
      (∀ n : ℕ, (airyZ n - airyLambdaInf s) * c n = ∑ j : Fin k, μ j * airyCardinalR n (s j)) ∧
      (∀ n : ℕ, |c n| ≤ airyDecayConst k J M_R R_s / (airyZ n) ^ 2) ∧
      Summable (fun n : ℕ => |c n|) ∧
      (∀ z : ℂ, (z - (airyLambdaInf s : ℂ)) * airyCardinalSeries c z =
        ((∑' n : ℕ, c n : ℝ) : ℂ) * airyAiC z +
          ∑ j : Fin k, (μ j : ℂ) * airyKerC z (s j : ℂ)) := by
  set lam := airyLambdaInf s
  let μ : Fin k → ℝ := fun j =>
    ∑ m : Fin J, (airyZ m.1 - lam) * c m.1 * airyRightInvMat s J m j
  have hlam_bds := airyLambdaInf_bounds s
  have hc_norm : ‖c‖ = 1 := (hasSum_sq_one_iff_norm_eq_one c).mp hc.1
  have hμ_bound : ∀ j : Fin k, |μ j| ≤ (J : ℝ) * (|airyZ J| + |airyZ 0|) * M_R := by
    intro j
    calc |μ j|
        ≤ ∑ m : Fin J, |(airyZ m.1 - lam) * c m.1 * airyRightInvMat s J m j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m : Fin J, (|airyZ J| + |airyZ 0|) * M_R := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [abs_mul, abs_mul]
          have hcm : |c m.1| ≤ 1 := by
            have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) c m.1
            rw [Real.norm_eq_abs, hc_norm] at h
            exact h
          have hzm : |airyZ m.1 - lam| ≤ |airyZ J| + |airyZ 0| := by
            have h1 : airyZ J ≤ airyZ m.1 := airyZ_anti m.2.le
            have h2 : airyZ m.1 ≤ airyZ 0 := airyZ_anti (Nat.zero_le m.1)
            have hlam_lo : airyZ J ≤ lam := (airyZ_anti (by omega : k ≤ J)).trans hlam_bds.1
            have hz0 : airyZ 0 < 0 := airyZ_neg 0
            have habs0 : 0 ≤ |airyZ 0| := abs_nonneg _
            have habsJ : |airyZ J| = -airyZ J := abs_of_neg (airyZ_neg J)
            rw [habsJ, abs_le]
            constructor <;> linarith only [h1, h2, hlam_lo, hlam_bds.2, hz0, habs0]
          have hRm := hR_bound m j
          calc |airyZ m.1 - lam| * |c m.1| * |airyRightInvMat s J m j|
              ≤ (|airyZ J| + |airyZ 0|) * 1 * M_R := by
                gcongr
            _ = (|airyZ J| + |airyZ 0|) * M_R := by ring
      _ = (J : ℝ) * (|airyZ J| + |airyZ 0|) * M_R := by simp [mul_assoc]
  -- Prove the multiplier equation `(airyZ n - lam) * c n = ∑ j, μ j * airyCardinalR n (s j)` for all `n`.
  have hmult : ∀ n : ℕ, (airyZ n - lam) * c n = ∑ j : Fin k, μ j * airyCardinalR n (s j) := by
    intro n
    let en : lp (fun _ : ℕ => ℝ) 2 := lp.single 2 n (1 : ℝ)
    have hen_apply : ∀ m : ℕ, en m = if m = n then 1 else 0 :=
      fun m => by simp [en, Pi.single_apply]
    let bn : Fin k → ℝ := fun j => airyCardinalR n (s j)
    let dn : Fin J → ℝ := (airyRightInvMat s J).mulVec bn
    let w : lp (fun _ : ℕ => ℝ) 2 := en - airyPadLp dn
    have hw_apply : ∀ m : ℕ, w m = en m - airyPadLp dn m :=
      fun m => by simp [w]
    have hen_sum : Summable (fun m : ℕ => |airyZ m| * (en m) ^ 2) := by
      refine summable_of_ne_finset_zero (s := {n}) fun m hm => ?_
      have hmn : m ≠ n := Finset.notMem_singleton.mp hm
      rw [hen_apply m, ite_eq_right_iff.mpr fun h => absurd h hmn, sq, zero_mul, mul_zero]
    have hw_sum : Summable (fun m : ℕ => |airyZ m| * (w m) ^ 2) := by
      have hdom : Summable (fun m : ℕ => 2 * (|airyZ m| * (en m) ^ 2) +
          2 * (|airyZ m| * (airyPadLp dn m) ^ 2)) :=
        (hen_sum.mul_left 2).add ((summable_abs_airyZ_airyPadLp dn).mul_left 2)
      refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
        (fun m => ?_) hdom
      rw [hw_apply m]
      have hsq : (en m - airyPadLp dn m) ^ 2 ≤ 2 * (en m) ^ 2 + 2 * (airyPadLp dn m) ^ 2 := by
        nlinarith only [sq_nonneg (en m + airyPadLp dn m)]
      have hmul := mul_le_mul_of_nonneg_left hsq (abs_nonneg (airyZ m))
      linarith only [hmul]
    have hw_ker : ∀ j : Fin k, airyCardinalSeriesR w (s j) = 0 := by
      intro j
      rw [← airyEvalMap_apply]
      change airyEvalMap s (en - airyPadLp dn) j = 0
      rw [map_sub, Pi.sub_apply, airyEvalMap_apply, airyEvalMap_apply]
      have hen_eval : airyCardinalSeriesR en (s j) = bn j := by
        have h1 := airyCardinalSeriesR_hasSum en (s j)
        have h2 : HasSum (fun m : ℕ => en m * airyCardinalR m (s j)) (bn j) := by
          refine (hasSum_ite_eq n (airyCardinalR n (s j))).congr_fun fun m => ?_
          rw [hen_apply m]
          by_cases hmn : m = n
          · subst hmn; simp
          · simp [hmn]
        exact h1.unique h2
      have hdn_eval : airyCardinalSeriesR (airyPadLp dn) (s j) = bn j := by
        rw [airyCardinalSeriesR_airyPadLp, ← airyBlockMat_mulVec]
        dsimp [dn]
        rw [airyBlockMat_mulVec_airyRightInvMat hdet]
      rw [hen_eval, hdn_eval, sub_self]
    have hstat := airyLambdaInf_stationarity hc hc_max hw_sum hw_ker
    have hs_en : HasSum (fun m : ℕ => (airyZ m - lam) * c m * en m)
        ((airyZ n - lam) * c n) := by
      refine (hasSum_ite_eq n ((airyZ n - lam) * c n)).congr_fun fun m => ?_
      rw [hen_apply m]
      by_cases hmn : m = n
      · subst hmn; simp
      · simp [hmn]
    have hs_dn : HasSum (fun m : ℕ => (airyZ m - lam) * c m * airyPadLp dn m)
        (∑ j : Fin k, μ j * airyCardinalR n (s j)) := by
      have hfin := hasSum_fin_of_ge_zero (M := J)
        (f := fun m => (airyZ m - lam) * c m * airyPadLp dn m)
        (fun m hm => by rw [airyPadLp_apply_ge dn hm, mul_zero])
      have hsum_eq : (∑ m : Fin J, (airyZ m.1 - lam) * c m.1 * airyPadLp dn m.1) =
          ∑ j : Fin k, μ j * airyCardinalR n (s j) := by
        have h1 : (∑ m : Fin J, (airyZ m.1 - lam) * c m.1 * airyPadLp dn m.1) =
            ∑ m : Fin J, ∑ j : Fin k,
              (airyZ m.1 - lam) * c m.1 * airyRightInvMat s J m j * airyCardinalR n (s j) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [airyPadLp_apply_lt dn m.2]
          dsimp [dn, bn]
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [h1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp [μ]
        rw [Finset.sum_mul]
      rwa [hsum_eq] at hfin
    have hs_diff : HasSum (fun m : ℕ => (airyZ m - lam) * c m * w m)
        ((airyZ n - lam) * c n - ∑ j : Fin k, μ j * airyCardinalR n (s j)) := by
      refine (hs_en.sub hs_dn).congr_fun fun m => ?_
      rw [hw_apply m]
      ring
    have heq0 : (airyZ n - lam) * c n - ∑ j : Fin k, μ j * airyCardinalR n (s j) = 0 :=
      hs_diff.unique (by rw [← hstat]; exact (summable_shifted_bilinear lam hc.2.1 hw_sum).hasSum)
    linarith only [heq0]
  -- Explicit uniform bound `|c n| ≤ airyDecayConst k J M_R R_s / (airyZ n) ^ 2` for all `n : ℕ`.
  have hc_decay : ∀ n : ℕ, |c n| ≤ airyDecayConst k J M_R R_s / (airyZ n) ^ 2 := by
    intro n
    set R_max := max |airyZ J| R_s
    have hR_pos : 0 < R_max := lt_of_lt_of_le (abs_pos.mpr (airyZ_neg J).ne) (le_max_left _ _)
    have han_neg : airyZ n < 0 := airyZ_neg n
    have han_sq_pos : 0 < (airyZ n) ^ 2 := sq_pos_of_ne_zero han_neg.ne
    by_cases hbig : 2 * R_max + 1 ≤ -airyZ n
    · have h1 : |lam| ≤ R_max := by
        have hlam_abs : |lam| ≤ |airyZ J| := by
          rw [abs_of_neg (lt_of_le_of_lt hlam_bds.2 (airyZ_neg 0)), abs_of_neg (airyZ_neg J)]
          have hkJ : airyZ J ≤ airyZ k := airyZ_anti (by omega : k ≤ J)
          linarith only [hlam_bds.1, hkJ]
        exact hlam_abs.trans (le_max_left _ _)
      have hlam_gap : (-airyZ n) / 2 ≤ |airyZ n - lam| := by
        have hlam_ge : -R_max ≤ lam := neg_le_of_abs_le h1
        have hlt : airyZ n - lam < 0 := by linarith only [hbig, hlam_ge, hR_pos]
        rw [abs_of_neg hlt]
        linarith only [hbig, hlam_ge, hR_pos]
      have hkn_le : ∀ j : Fin k, |airyCardinalR n (s j)| ≤ 6 / (-airyZ n) := by
        intro j
        have hsj : |s j| ≤ R_max :=
          ((Finset.single_le_sum (fun i _ => abs_nonneg (s i)) (Finset.mem_univ j)).trans hRs).trans
            (le_max_right _ _)
        have hsj_ge : -R_max ≤ s j := neg_le_of_abs_le hsj
        have hden : (-airyZ n) / 2 ≤ s j - airyZ n := by linarith only [hbig, hsj_ge, hR_pos]
        have hden_pos : 0 < s j - airyZ n := by linarith only [hden, han_neg]
        have hne : s j ≠ airyZ n := sub_ne_zero.mp hden_pos.ne'
        have hden_abs : |s j - airyZ n| = s j - airyZ n := abs_of_pos hden_pos
        rw [airyCardinalR_of_ne n hne, abs_div, hden_abs]
        have hAi := abs_airyAi_le_three (s j)
        calc |airyAi (s j)| / (s j - airyZ n)
            ≤ 3 / ((-airyZ n) / 2) := div_le_div₀ (by norm_num) hAi (by linarith only [han_neg]) hden
          _ = 6 / (-airyZ n) := by ring
      have hμ_sum_le : (∑ j : Fin k, |μ j|) ≤
          (k : ℝ) * ((J : ℝ) * (|airyZ J| + |airyZ 0|) * M_R) := by
        calc (∑ j : Fin k, |μ j|)
            ≤ ∑ _j : Fin k, (J : ℝ) * (|airyZ J| + |airyZ 0|) * M_R :=
              Finset.sum_le_sum fun j _ => hμ_bound j
          _ = (k : ℝ) * ((J : ℝ) * (|airyZ J| + |airyZ 0|) * M_R) := by simp
      have hrhs_le : |∑ j : Fin k, μ j * airyCardinalR n (s j)| ≤
          (6 * ∑ j : Fin k, |μ j|) / (-airyZ n) := by
        calc |∑ j : Fin k, μ j * airyCardinalR n (s j)|
            ≤ ∑ j : Fin k, |μ j * airyCardinalR n (s j)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j : Fin k, |μ j| * (6 / (-airyZ n)) := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hkn_le j) (abs_nonneg _)
          _ = (6 * ∑ j : Fin k, |μ j|) / (-airyZ n) := by
              rw [← Finset.sum_mul]; ring
      have heq_abs : |airyZ n - lam| * |c n| = |∑ j : Fin k, μ j * airyCardinalR n (s j)| := by
        rw [← abs_mul, hmult n]
      have hpos_gap : 0 < (-airyZ n) / 2 := by linarith only [han_neg]
      have hcn_le : |c n| ≤ (12 * ∑ j : Fin k, |μ j|) / (airyZ n) ^ 2 := by
        have hstep : |c n| ≤ ((6 * ∑ j : Fin k, |μ j|) / (-airyZ n)) / ((-airyZ n) / 2) := by
          rw [le_div_iff₀ hpos_gap]
          calc |c n| * ((-airyZ n) / 2)
              ≤ |c n| * |airyZ n - lam| := mul_le_mul_of_nonneg_left hlam_gap (abs_nonneg _)
            _ = |airyZ n - lam| * |c n| := mul_comm _ _
            _ ≤ (6 * ∑ j : Fin k, |μ j|) / (-airyZ n) := heq_abs ▸ hrhs_le
        refine hstep.trans (le_of_eq ?_)
        have hne_z : airyZ n ≠ 0 := han_neg.ne
        field_simp
        ring
      refine hcn_le.trans (div_le_div_of_nonneg_right ?_ han_sq_pos.le)
      have h12 : 12 * ∑ j : Fin k, |μ j| ≤
          12 * (k : ℝ) * ((J : ℝ) * (|airyZ J| + |airyZ 0|) * M_R) := by
        linarith only [hμ_sum_le]
      exact h12.trans (le_max_right _ _)
    · push Not at hbig
      have hcn1 : |c n| ≤ 1 := by
        have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) c n
        rw [Real.norm_eq_abs, hc_norm] at h
        exact h
      have hsq_le : (airyZ n) ^ 2 ≤ (2 * R_max + 1) ^ 2 := by
        have hneg_sq : (airyZ n) ^ 2 = (-airyZ n) ^ 2 := by ring
        rw [hneg_sq]
        exact pow_le_pow_left₀ (by linarith only [han_neg]) hbig.le 2
      rw [le_div_iff₀ han_sq_pos]
      calc |c n| * (airyZ n) ^ 2
          ≤ 1 * (2 * R_max + 1) ^ 2 :=
            mul_le_mul hcn1 hsq_le han_sq_pos.le zero_le_one
        _ = (2 * R_max + 1) ^ 2 := one_mul _
        _ ≤ airyDecayConst k J M_R R_s := le_max_left _ _
  have hc_abs_sum : Summable (fun n : ℕ => |c n|) := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => ?_)
      (summable_airyZ_inv_sq.mul_left (airyDecayConst k J M_R R_s))
    rw [← div_eq_mul_inv]
    exact hc_decay n
  have hc_sum : Summable (fun n : ℕ => c n) := hc_abs_sum.of_abs
  -- Entire representation `(eq:airy-square-rep)`.
  refine ⟨μ, hμ_bound, hmult, hc_decay, hc_abs_sum, fun z => ?_⟩
  have hlhs : HasSum (fun n : ℕ => (z - (lam : ℂ)) * ((c n : ℂ) * airyCardinal n z))
      ((z - (lam : ℂ)) * airyCardinalSeries c z) :=
    (airyCardinalSeries_hasSum c z).mul_left (z - (lam : ℂ))
  have hrhs1 : HasSum (fun n : ℕ => (c n : ℂ) * airyAiC z)
      (((∑' n : ℕ, c n : ℝ) : ℂ) * airyAiC z) :=
    (Complex.hasSum_ofReal.mpr hc_sum.hasSum).mul_right (airyAiC z)
  have hrhs2 : HasSum (fun n : ℕ => ∑ j : Fin k, (μ j : ℂ) *
      (airyCardinal n z * airyCardinal n (s j : ℂ)))
      (∑ j : Fin k, (μ j : ℂ) * airyKerC z (s j : ℂ)) :=
    hasSum_sum fun j _ => (airyCardinal_ker_hasSum z (s j : ℂ)).mul_left (μ j : ℂ)
  have hrhs := hrhs1.add hrhs2
  have hterm_eq : ∀ n : ℕ, (z - (lam : ℂ)) * ((c n : ℂ) * airyCardinal n z) =
      (c n : ℂ) * airyAiC z +
        ∑ j : Fin k, (μ j : ℂ) * (airyCardinal n z * airyCardinal n (s j : ℂ)) := by
    intro n
    have h1 : (z - (lam : ℂ)) * airyCardinal n z =
        airyAiC z + ((airyZ n - lam : ℝ) : ℂ) * airyCardinal n z := by
      have hm := mul_airyCardinal n z
      push_cast
      linear_combination hm
    calc (z - (lam : ℂ)) * ((c n : ℂ) * airyCardinal n z)
        = (c n : ℂ) * ((z - (lam : ℂ)) * airyCardinal n z) := by ring
      _ = (c n : ℂ) * airyAiC z +
            (((airyZ n - lam) * c n : ℝ) : ℂ) * airyCardinal n z := by
          rw [h1]; push_cast; ring
      _ = (c n : ℂ) * airyAiC z +
            ∑ j : Fin k, (μ j : ℂ) * (airyCardinal n z * airyCardinal n (s j : ℂ)) := by
          rw [hmult n, Complex.ofReal_sum, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Complex.ofReal_mul, ofReal_airyCardinalR]
          ring
  exact (hlhs.congr_fun fun n => (hterm_eq n).symm).unique hrhs

/-! ### Section 4: `O(M⁻¹)` Rate, `airyLambdaInf = airyLambda`, Local Lipschitz, and Exactness -/

lemma hasSum_nat_add_shift {f : ℕ → ℝ} {S : ℝ} (M : ℕ) (h : HasSum f S) :
    HasSum (fun m : ℕ => f (M + m)) (S - ∑ n ∈ Finset.range M, f n) := by
  have h' : HasSum f ((S - ∑ n ∈ Finset.range M, f n) + ∑ n ∈ Finset.range M, f n) := by
    simpa only [sub_add_cancel] using h
  exact ((hasSum_nat_add_iff M).mpr h').congr_fun fun m => by rw [Nat.add_comm]

/-- Uniform `O(M⁻¹)` truncation bound on compact sets `K` of distinct site vectors for
`airyLambdaInf`. -/
lemma airyLambdaInf_sub_section_le_on_compact {k : ℕ} {K : Set (Fin k → ℝ)}
    (hK : IsCompact K) (hK_inj : ∀ s ∈ K, Function.Injective s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ∀ M : ℕ, k + 1 ≤ M →
      airyLambdaInf s - airyLambdaSection s M ≤ C / (M : ℝ) := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, le_rfl, fun _ hs => False.elim hs⟩
  obtain ⟨J, M_R, hJ_ge, hMR, hJ_block⟩ := exists_uniform_rightInv_on_compact hK hK_inj
  have hcont_abs : Continuous (fun s : Fin k → ℝ => ∑ j : Fin k, |s j|) :=
    continuous_finsetSum _ fun j _ => (continuous_apply j).abs
  obtain ⟨R_s_raw, hRs_raw⟩ := hK.exists_bound_of_continuousOn hcont_abs.continuousOn
  set R_s := max R_s_raw 0
  have hRs_nn : 0 ≤ R_s := le_max_right _ _
  have hRs_K : ∀ s ∈ K, (∑ j : Fin k, |s j|) ≤ R_s := by
    intro s hs
    have hb0 : (∑ j : Fin k, |s j|) ≤ R_s_raw := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg (s i))]
        using hRs_raw s hs
    exact hb0.trans (le_max_left _ _)
  set M_c := airyDecayConst k J M_R R_s
  have hMc_nn : 0 ≤ M_c := airyDecayConst_nonneg k J M_R R_s
  have hev_site := eventually_le_neg_airyZ (2 * R_s + 1)
  rw [Filter.eventually_atTop] at hev_site
  obtain ⟨N_site, hN_site⟩ := hev_site
  set B_r := 6 * M_c / 8
  set B_d := √(J : ℝ) * ((k : ℝ) * M_R * B_r)
  have hBr_nn : 0 ≤ B_r := by positivity
  have hBd_nn : 0 ≤ B_d := by positivity
  -- Choose threshold `M₀` depending only on `(J, N_site, B_d, M_c)`.
  let M₀ : ℕ := max (max J (N_site + 1)) (⌈max (4 * B_d) (2 * M_c ^ 2)⌉₊ + 1)
  have hM₀_pos : 1 ≤ M₀ := by omega
  have hM₀_J : J ≤ M₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hM₀_N : N_site ≤ M₀ := by
    have : N_site + 1 ≤ M₀ := (le_max_right _ _).trans (le_max_left _ _)
    omega
  set C_hi := 4 * ((|airyZ J| + |airyZ 0|) * B_d ^ 2 + M_c ^ 2 / 8)
  set C_lo := (airyZ 0 - airyZ k) * (M₀ : ℝ)
  set C := max C_hi (max C_lo 0)
  refine ⟨C, (le_max_right _ _).trans (le_max_right _ _), fun s hs M hMk => ?_⟩
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  by_cases hMM₀ : M < M₀
  · -- Small `M < M₀`: bound using `airyZ k ≤ Λ_M(s) ≤ λ_*(s) ≤ airyZ 0`.
    have hb1 := airyLambdaInf_bounds s
    have hb2 := (airyZ_le_airyLambdaSection_first s).trans (airyLambdaSection_mono s le_rfl hMk)
    have hdiff_le : airyLambdaInf s - airyLambdaSection s M ≤ airyZ 0 - airyZ k := by
      linarith only [hb1.2, hb2]
    have hdiff_nn : 0 ≤ airyZ 0 - airyZ k := by
      linarith only [airyZ_anti (Nat.zero_le k)]
    have hM_le_M₀ : (M : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hMM₀.le
    calc airyLambdaInf s - airyLambdaSection s M
        ≤ airyZ 0 - airyZ k := hdiff_le
      _ ≤ (airyZ 0 - airyZ k) * ((M₀ : ℝ) / (M : ℝ)) := by
          have h1 : 1 ≤ (M₀ : ℝ) / (M : ℝ) := (one_le_div hM_pos).mpr hM_le_M₀
          nlinarith only [hdiff_nn, h1]
      _ = C_lo / (M : ℝ) := by dsimp [C_lo]; ring
      _ ≤ C / (M : ℝ) := div_le_div_of_nonneg_right
          ((le_max_left C_lo 0).trans (le_max_right _ _)) hM_pos.le
  · push Not at hMM₀
    have hMJ : J ≤ M := hM₀_J.trans hMM₀
    have hMN : N_site ≤ M := hM₀_N.trans hMM₀
    have hJM_ge1 : 1 ≤ M := by omega
    obtain ⟨hdet, hR_bd⟩ := hJ_block s hs
    obtain ⟨c, hc_feas, hc_max⟩ := exists_airyLambdaInf_maximizer s
    obtain ⟨_, _, _, hc_decay, _, _⟩ :=
      airyLambdaInf_multiplier_rep_from_block hJ_ge hMR (hRs_K s hs) hdet hR_bd hc_feas hc_max
    set lam := airyLambdaInf s
    have hlam_bds := airyLambdaInf_bounds s
    -- Tail of cardinal evaluations at `s j` for `n ≥ M`.
    have hkn_tail : ∀ m : ℕ, ∀ j : Fin k,
        |airyCardinalR (M + m) (s j)| ≤ 6 / (-airyZ (M + m)) := by
      intro m j
      have hbig := hN_site (M + m) (hMN.trans (Nat.le_add_right M m))
      have hsj : |s j| ≤ R_s :=
        (Finset.single_le_sum (fun i _ => abs_nonneg (s i)) (Finset.mem_univ j)).trans (hRs_K s hs)
      have hsj_ge : -R_s ≤ s j := neg_le_of_abs_le hsj
      have han_neg : airyZ (M + m) < 0 := airyZ_neg (M + m)
      have hden : (-airyZ (M + m)) / 2 ≤ s j - airyZ (M + m) := by
        linarith only [hbig, hsj_ge, hRs_nn]
      have hden_pos : 0 < s j - airyZ (M + m) := by linarith only [hden, han_neg]
      have hne : s j ≠ airyZ (M + m) := sub_ne_zero.mp hden_pos.ne'
      have hden_abs : |s j - airyZ (M + m)| = s j - airyZ (M + m) := abs_of_pos hden_pos
      rw [airyCardinalR_of_ne (M + m) hne, abs_div, hden_abs]
      calc |airyAi (s j)| / (s j - airyZ (M + m))
          ≤ 3 / ((-airyZ (M + m)) / 2) :=
            div_le_div₀ (by norm_num) (abs_airyAi_le_three (s j)) (by linarith only [han_neg]) hden
        _ = 6 / (-airyZ (M + m)) := by ring
    let c_M : Fin M → ℝ := fun n => c n.1
    let r : Fin k → ℝ := fun j => airySectionPolyR M c_M (s j)
    have hr_bound : ∀ j : Fin k, |r j| ≤ B_r / (M : ℝ) := by
      intro j
      have htot : HasSum (fun n : ℕ => c n * airyCardinalR n (s j)) 0 := by
        rw [← hc_feas.2.2 j]; exact airyCardinalSeriesR_hasSum c (s j)
      have hshift := hasSum_nat_add_shift M htot
      have hhead_eq : (∑ n ∈ Finset.range M, c n * airyCardinalR n (s j)) = r j := by
        dsimp [r, airySectionPolyR, c_M]
        rw [← Fin.sum_univ_eq_sum_range]
      rw [hhead_eq, zero_sub] at hshift
      have htsum_eq : r j = -∑' m : ℕ, c (M + m) * airyCardinalR (M + m) (s j) := by
        linarith only [hshift.tsum_eq]
      have hterm_le : ∀ m : ℕ, |c (M + m) * airyCardinalR (M + m) (s j)| ≤
          B_r * (1 / (((M + m + 1 : ℕ) : ℝ) ^ 2)) := by
        intro m
        rw [abs_mul]
        have han_neg : airyZ (M + m) < 0 := airyZ_neg (M + m)
        have hpos_z : 0 < -airyZ (M + m) := neg_pos.mpr han_neg
        have hc_m : |c (M + m)| ≤ M_c / (-airyZ (M + m)) ^ 2 := by
          simpa only [neg_sq] using hc_decay (M + m)
        have hcube := eight_mul_sq_le_neg_airyZ_cube (M + m)
        have hpos_idx : (0 : ℝ) < ((M + m + 1 : ℕ) : ℝ) ^ 2 := by positivity
        have hinv_cube : 1 / (-airyZ (M + m)) ^ 3 ≤
            (1 / 8 : ℝ) * (1 / (((M + m + 1 : ℕ) : ℝ) ^ 2)) := by
          rw [one_div_mul_one_div, one_div_le_one_div (pow_pos hpos_z 3) (by positivity)]
          exact hcube
        calc |c (M + m)| * |airyCardinalR (M + m) (s j)|
            ≤ (M_c / (-airyZ (M + m)) ^ 2) * (6 / (-airyZ (M + m))) :=
              mul_le_mul hc_m (hkn_tail m j) (abs_nonneg _) (by positivity)
          _ = 6 * M_c * (1 / (-airyZ (M + m)) ^ 3) := by ring
          _ ≤ 6 * M_c * ((1 / 8 : ℝ) * (1 / (((M + m + 1 : ℕ) : ℝ) ^ 2))) :=
              mul_le_mul_of_nonneg_left hinv_cube (by positivity)
          _ = B_r * (1 / (((M + m + 1 : ℕ) : ℝ) ^ 2)) := by dsimp [B_r]; ring
      have habs_sum : Summable (fun m : ℕ => |c (M + m) * airyCardinalR (M + m) (s j)|) :=
        Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm_le
          ((summable_inv_nat_add_sq M).mul_left B_r)
      have htsum_abs : |∑' m : ℕ, c (M + m) * airyCardinalR (M + m) (s j)| ≤
          ∑' m : ℕ, |c (M + m) * airyCardinalR (M + m) (s j)| := by
        refine abs_le.mpr ⟨?_, Summable.tsum_le_tsum (fun _ => le_abs_self _) hshift.summable habs_sum⟩
        rw [← tsum_neg]
        exact Summable.tsum_le_tsum (fun _ => neg_abs_le _) habs_sum.neg hshift.summable
      rw [htsum_eq, abs_neg]
      calc |∑' m : ℕ, c (M + m) * airyCardinalR (M + m) (s j)|
          ≤ ∑' m : ℕ, |c (M + m) * airyCardinalR (M + m) (s j)| := htsum_abs
        _ ≤ ∑' m : ℕ, B_r * (1 / (((M + m + 1 : ℕ) : ℝ) ^ 2)) :=
            Summable.tsum_le_tsum hterm_le habs_sum ((summable_inv_nat_add_sq M).mul_left B_r)
        _ = B_r * ∑' m : ℕ, (1 / (((M + m + 1 : ℕ) : ℝ) ^ 2)) := tsum_mul_left
        _ ≤ B_r * (1 / (M : ℝ)) :=
            mul_le_mul_of_nonneg_left (tsum_inv_nat_add_sq_le hJM_ge1) hBr_nn
        _ = B_r / (M : ℝ) := mul_one_div _ _
    -- Correct `c_M` on the first `J` coordinates using `airyRightInvMat s J`.
    let d : Fin J → ℝ := -(airyRightInvMat s J).mulVec r
    have hd_entry : ∀ n : Fin J, |d n| ≤ ((k : ℝ) * M_R * B_r) / (M : ℝ) := by
      intro n
      have hdn : d n = -∑ j : Fin k, airyRightInvMat s J n j * r j := by
        simp [d, Matrix.mulVec, dotProduct]
      rw [hdn, abs_neg]
      calc |∑ j : Fin k, airyRightInvMat s J n j * r j|
          ≤ ∑ j : Fin k, |airyRightInvMat s J n j * r j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin k, M_R * (B_r / (M : ℝ)) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            exact mul_le_mul (hR_bd n j) (hr_bound j) (abs_nonneg _) hMR
        _ = ((k : ℝ) * M_R * B_r) / (M : ℝ) := by simp; ring
    have hd_norm_sq : (∑ n : Fin J, (d n) ^ 2) ≤ (B_d / (M : ℝ)) ^ 2 := by
      calc (∑ n : Fin J, (d n) ^ 2)
          ≤ ∑ _n : Fin J, (((k : ℝ) * M_R * B_r) / (M : ℝ)) ^ 2 := by
            refine Finset.sum_le_sum fun n _ => ?_
            rw [← sq_abs (d n)]
            exact pow_le_pow_left₀ (abs_nonneg _) (hd_entry n) 2
        _ = (J : ℝ) * (((k : ℝ) * M_R * B_r) / (M : ℝ)) ^ 2 := by simp
        _ = (B_d / (M : ℝ)) ^ 2 := by
            have hJ2 : √(J : ℝ) ^ 2 = (J : ℝ) := Real.sq_sqrt (Nat.cast_nonneg J)
            have hpow : (√(J : ℝ) * ((k : ℝ) * M_R * B_r) / (M : ℝ)) ^ 2 =
                √(J : ℝ) ^ 2 * (((k : ℝ) * M_R * B_r) / (M : ℝ)) ^ 2 := by ring
            dsimp [B_d]
            rw [hpow, hJ2]
    have hd_norm : ‖airyPadLp d‖ ≤ B_d / (M : ℝ) := by
      refine le_of_sq_le_sq ?_ (div_nonneg hBd_nn hM_pos.le)
      rw [norm_sq_airyPadLp]
      exact hd_norm_sq
    let v : Fin M → ℝ := fun n => c_M n + airyPadLp d n.1
    have hv_ker : ∀ j : Fin k, airySectionPolyR M v (s j) = 0 := by
      intro j
      have hsplit : airySectionPolyR M v (s j) =
          r j + ∑ n : Fin M, airyPadLp d n.1 * airyCardinalR n.1 (s j) := by
        dsimp [r, airySectionPolyR, v]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun n _ => by ring
      have hd_poly : (∑ n : Fin M, airyPadLp d n.1 * airyCardinalR n.1 (s j)) = -r j := by
        have hfin := hasSum_fin_of_ge_zero (M := M)
          (f := fun n => airyPadLp d n * airyCardinalR n (s j))
          fun n hn => by rw [airyPadLp_apply_ge d (hMJ.trans hn), zero_mul]
        have h1 : (∑ n : Fin M, airyPadLp d n.1 * airyCardinalR n.1 (s j)) =
            airyCardinalSeriesR (airyPadLp d) (s j) :=
          hfin.unique (airyCardinalSeriesR_hasSum (airyPadLp d) (s j))
        rw [h1, airyCardinalSeriesR_airyPadLp, ← airyBlockMat_mulVec]
        dsimp [d]
        rw [Matrix.mulVec_neg, Pi.neg_apply, airyBlockMat_mulVec_airyRightInvMat hdet]
      rw [hsplit, hd_poly, add_neg_cancel]
    -- Define `w = airyPadLp v - c ∈ D ∩ ker B(s)`.
    let w : lp (fun _ : ℕ => ℝ) 2 := airyPadLp v - c
    have hw_apply : ∀ n : ℕ, w n = airyPadLp v n - c n := fun n => by simp [w]
    have hw_lt : ∀ n : ℕ, n < M → w n = airyPadLp d n := by
      intro n hn
      rw [hw_apply n, airyPadLp_apply_lt v hn]
      dsimp [v, c_M]
      ring
    have hw_ge : ∀ n : ℕ, M ≤ n → w n = -c n := by
      intro n hn
      rw [hw_apply n, airyPadLp_apply_ge v hn, zero_sub]
    -- Weighted tail bound `∑'_{m : ℕ} |airyZ (M + m)| * (c (M + m))^2 ≤ (M_c^2 / 8) / M`.
    have htail_term : ∀ m : ℕ, |airyZ (M + m)| * (c (M + m)) ^ 2 ≤
        (M_c ^ 2 / 8) * (1 / (((M + m + 1 : ℕ) : ℝ) ^ 2)) := by
      intro m
      have han_neg : airyZ (M + m) < 0 := airyZ_neg (M + m)
      have hpos_z : 0 < -airyZ (M + m) := neg_pos.mpr han_neg
      have habs_z : |airyZ (M + m)| = -airyZ (M + m) := abs_of_neg han_neg
      have hc_m : (c (M + m)) ^ 2 ≤ M_c ^ 2 / (-airyZ (M + m)) ^ 4 := by
        have h1 : |c (M + m)| ≤ M_c / (-airyZ (M + m)) ^ 2 := by
          simpa only [neg_sq] using hc_decay (M + m)
        have hsq := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rw [sq_abs, div_pow, ← pow_mul] at hsq
        exact hsq
      have hcube := eight_mul_sq_le_neg_airyZ_cube (M + m)
      have hinv_cube : 1 / (-airyZ (M + m)) ^ 3 ≤
          (1 / 8 : ℝ) * (1 / (((M + m + 1 : ℕ) : ℝ) ^ 2)) := by
        rw [one_div_mul_one_div, one_div_le_one_div (pow_pos hpos_z 3) (by positivity)]
        exact hcube
      rw [habs_z]
      calc (-airyZ (M + m)) * (c (M + m)) ^ 2
          ≤ (-airyZ (M + m)) * (M_c ^ 2 / (-airyZ (M + m)) ^ 4) :=
            mul_le_mul_of_nonneg_left hc_m hpos_z.le
        _ = M_c ^ 2 * (1 / (-airyZ (M + m)) ^ 3) := by
            have hnz : -airyZ (M + m) ≠ 0 := hpos_z.ne'
            field_simp
        _ ≤ M_c ^ 2 * ((1 / 8 : ℝ) * (1 / (((M + m + 1 : ℕ) : ℝ) ^ 2))) :=
            mul_le_mul_of_nonneg_left hinv_cube (sq_nonneg M_c)
        _ = (M_c ^ 2 / 8) * (1 / (((M + m + 1 : ℕ) : ℝ) ^ 2)) := by ring
    have htail_sum_abs : Summable (fun m : ℕ => |airyZ (M + m)| * (c (M + m)) ^ 2) :=
      ((summable_nat_add_iff M).mpr hc_feas.2.1).congr fun m => by rw [Nat.add_comm]
    have htail_tsum_le : (∑' m : ℕ, |airyZ (M + m)| * (c (M + m)) ^ 2) ≤
        (M_c ^ 2 / 8) / (M : ℝ) := by
      calc (∑' m : ℕ, |airyZ (M + m)| * (c (M + m)) ^ 2)
          ≤ ∑' m : ℕ, (M_c ^ 2 / 8) * (1 / (((M + m + 1 : ℕ) : ℝ) ^ 2)) :=
            Summable.tsum_le_tsum htail_term htail_sum_abs
              ((summable_inv_nat_add_sq M).mul_left (M_c ^ 2 / 8))
        _ = (M_c ^ 2 / 8) * ∑' m : ℕ, (1 / (((M + m + 1 : ℕ) : ℝ) ^ 2)) := tsum_mul_left
        _ ≤ (M_c ^ 2 / 8) * (1 / (M : ℝ)) :=
            mul_le_mul_of_nonneg_left (tsum_inv_nat_add_sq_le hJM_ge1) (by positivity)
        _ = (M_c ^ 2 / 8) / (M : ℝ) := mul_one_div _ _
    -- Bound `‖w‖ ≤ 1 / 2` using `M ≥ M₀`.
    have hw_norm_sq_le : ‖w‖ ^ 2 ≤ (B_d / (M : ℝ)) ^ 2 + (M_c ^ 2 / 8) / (M : ℝ) := by
      have hnorm_w := lp.hasSum_norm (p := 2) (by norm_num) w
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at hnorm_w
      have hshift_w := hasSum_nat_add_shift M hnorm_w
      have hhead_w : (∑ n ∈ Finset.range M, (w n) ^ 2) = ∑ n : Fin J, (d n) ^ 2 := by
        have h1 : (∑ n ∈ Finset.range M, (w n) ^ 2) =
            ∑ n ∈ Finset.range M, (airyPadLp d n) ^ 2 :=
          Finset.sum_congr rfl fun n hn => by rw [hw_lt n (Finset.mem_range.mp hn)]
        have hfin := hasSum_fin_of_ge_zero (M := J) (f := fun n => (airyPadLp d n) ^ 2)
          fun n hn => by rw [airyPadLp_apply_ge d hn, sq, zero_mul]
        have hfinM : HasSum (fun n : ℕ => (airyPadLp d n) ^ 2)
            (∑ n ∈ Finset.range M, (airyPadLp d n) ^ 2) :=
          hasSum_sum_of_ne_finset_zero fun n hn => by
            have hge : M ≤ n := not_lt.mp (by simpa [Finset.mem_range] using hn)
            rw [airyPadLp_apply_ge d (hMJ.trans hge), sq, zero_mul]
        rw [h1, hfinM.unique hfin]
        exact Finset.sum_congr rfl fun n _ => by rw [airyPadLp_apply_lt d n.2]
      have htail_w_eq : (fun m : ℕ => (w (M + m)) ^ 2) = fun m : ℕ => (c (M + m)) ^ 2 := by
        ext m; rw [hw_ge (M + m) (Nat.le_add_right M m), neg_sq]
      rw [hhead_w, htail_w_eq] at hshift_w
      have htail_c2_le : (∑' m : ℕ, (c (M + m)) ^ 2) ≤
          ∑' m : ℕ, |airyZ (M + m)| * (c (M + m)) ^ 2 := by
        refine Summable.tsum_le_tsum (fun m => ?_) hshift_w.summable htail_sum_abs
        have h2 : 2 < |airyZ (M + m)| := two_lt_abs_airyZ (M + m)
        nlinarith only [h2, sq_nonneg (c (M + m))]
      have heq_w : ‖w‖ ^ 2 = (∑ n : Fin J, (d n) ^ 2) + ∑' m : ℕ, (c (M + m)) ^ 2 := by
        linarith only [hshift_w.tsum_eq]
      rw [heq_w]
      exact add_le_add hd_norm_sq (htail_c2_le.trans htail_tsum_le)
    have hM_ge_ceil : (⌈max (4 * B_d) (2 * M_c ^ 2)⌉₊ : ℝ) < (M : ℝ) := by
      have : ⌈max (4 * B_d) (2 * M_c ^ 2)⌉₊ + 1 ≤ M :=
        (le_max_right _ _).trans hMM₀
      exact_mod_cast this
    have hBd_quarter : B_d / (M : ℝ) ≤ 1 / 4 := by
      rw [div_le_iff₀ hM_pos]
      have h1 : 4 * B_d ≤ (⌈max (4 * B_d) (2 * M_c ^ 2)⌉₊ : ℝ) :=
        (le_max_left _ _).trans (Nat.le_ceil _)
      linarith only [h1, hM_ge_ceil]
    have hMc_eighth : (M_c ^ 2 / 8) / (M : ℝ) ≤ 1 / 16 := by
      rw [div_le_iff₀ hM_pos]
      have h1 : 2 * M_c ^ 2 ≤ (⌈max (4 * B_d) (2 * M_c ^ 2)⌉₊ : ℝ) :=
        (le_max_right _ _).trans (Nat.le_ceil _)
      linarith only [h1, hM_ge_ceil]
    have hw_norm_le : ‖w‖ ≤ 1 / 2 := by
      refine le_of_sq_le_sq ?_ (by norm_num)
      have hbd2 : (B_d / (M : ℝ)) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (div_nonneg hBd_nn hM_pos.le) hBd_quarter 2
      linarith only [hw_norm_sq_le, hbd2, hMc_eighth]
    have hv_norm_ge : 1 / 2 ≤ ‖airyPadLp v‖ := by
      have hc1 : ‖c‖ = 1 := (hasSum_sq_one_iff_norm_eq_one c).mp hc_feas.1
      have htri := norm_add_le (airyPadLp v) (-w)
      have hvw : airyPadLp v + -w = c := by dsimp [w]; abel
      rw [hvw, norm_neg, hc1] at htri
      linarith only [htri, hw_norm_le]
    have hv_sq_ge : 1 / 4 ≤ ∑ n : Fin M, (v n) ^ 2 := by
      rw [← norm_sq_airyPadLp]
      have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hv_norm_ge 2
      norm_num at hsq
      exact hsq
    have hv_ne : v ≠ 0 := by
      intro h0
      simp [h0] at hv_sq_ge
      linarith only [hv_sq_ge]
    -- Apply stationarity `E_lam(c, w) = 0` to expand the Rayleigh numerator of `v`.
    have hw_sum : Summable (fun n : ℕ => |airyZ n| * (w n) ^ 2) := by
      have hdom : Summable (fun n : ℕ => 2 * (|airyZ n| * (airyPadLp v n) ^ 2) +
          2 * (|airyZ n| * (c n) ^ 2)) :=
        ((summable_abs_airyZ_airyPadLp v).mul_left 2).add (hc_feas.2.1.mul_left 2)
      refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
        (fun n => ?_) hdom
      rw [hw_apply n]
      have hsq : (airyPadLp v n - c n) ^ 2 ≤ 2 * (airyPadLp v n) ^ 2 + 2 * (c n) ^ 2 := by
        nlinarith only [sq_nonneg (airyPadLp v n + c n)]
      have hmul := mul_le_mul_of_nonneg_left hsq (abs_nonneg (airyZ n))
      linarith only [hmul]
    have hw_ker : ∀ j : Fin k, airyCardinalSeriesR w (s j) = 0 := by
      intro j
      rw [← airyEvalMap_apply]
      change airyEvalMap s (airyPadLp v - c) j = 0
      rw [map_sub, Pi.sub_apply, airyEvalMap_apply, airyEvalMap_apply,
        airyCardinalSeriesR_airyPadLp, hv_ker j, hc_feas.2.2 j, sub_zero]
    have hstat := airyLambdaInf_stationarity hc_feas hc_max hw_sum hw_ker
    have hsC : HasSum (fun n : ℕ => (airyZ n - lam) * (c n) ^ 2) 0 := by
      have h1 : HasSum (fun n : ℕ => airyZ n * (c n) ^ 2) lam := by
        rw [← hc_max]; exact ((summable_airyZ_mul_sq_iff c).mp hc_feas.2.1).hasSum
      have h2 : HasSum (fun n : ℕ => lam * (c n) ^ 2) lam := by
        simpa only [mul_one] using hc_feas.1.mul_left lam
      have hsub := h1.sub h2
      rw [sub_self] at hsub
      exact hsub.congr_fun fun n => by ring
    have hsA : HasSum (fun n : ℕ => (airyZ n - lam) * c n * w n) 0 := by
      rw [← hstat]; exact (summable_shifted_bilinear lam hc_feas.2.1 hw_sum).hasSum
    have hw2_sum : Summable (fun n : ℕ => (w n) ^ 2) := by
      have h := (lp.hasSum_norm (p := 2) (by norm_num) w).summable
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h
    have hsD_sum : Summable (fun n : ℕ => (airyZ n - lam) * (w n) ^ 2) :=
      (((summable_airyZ_mul_sq_iff w).mp hw_sum).sub (hw2_sum.mul_left lam)).congr fun n => by ring
    have hv_quad_eq : (∑ n : Fin M, airyZ n.1 * (v n) ^ 2) -
        lam * (∑ n : Fin M, (v n) ^ 2) = ∑' n : ℕ, (airyZ n - lam) * (w n) ^ 2 := by
      have hv1 := hasSum_airyZ_airyPadLp v
      have hv2 : HasSum (fun n : ℕ => (airyPadLp v n) ^ 2) (∑ n : Fin M, (v n) ^ 2) := by
        rw [← norm_sq_airyPadLp]
        have h := lp.hasSum_norm (p := 2) (by norm_num) (airyPadLp v)
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h
      have hv_lhs : HasSum (fun n : ℕ => (airyZ n - lam) * (airyPadLp v n) ^ 2)
          ((∑ n : Fin M, airyZ n.1 * (v n) ^ 2) - lam * (∑ n : Fin M, (v n) ^ 2)) :=
        (hv1.sub (hv2.mul_left lam)).congr_fun fun n => by ring
      have hv_rhs : HasSum (fun n : ℕ => (airyZ n - lam) * (airyPadLp v n) ^ 2)
          (∑' n : ℕ, (airyZ n - lam) * (w n) ^ 2) := by
        have hcomb := (hsC.add (hsA.mul_left 2)).add hsD_sum.hasSum
        simp only [mul_zero, add_zero, zero_add] at hcomb
        refine hcomb.congr_fun fun n => ?_
        have hvn : airyPadLp v n = c n + w n := by linarith only [hw_apply n]
        rw [hvn]; ring
      exact hv_lhs.unique hv_rhs
    -- Bound `-∑' n, (airyZ n - lam) * (w n)^2` by splitting at `M`.
    have hloss_le : -(∑' n : ℕ, (airyZ n - lam) * (w n) ^ 2) ≤
        ((|airyZ J| + |airyZ 0|) * B_d ^ 2 + M_c ^ 2 / 8) / (M : ℝ) := by
      have hshift_D := hasSum_nat_add_shift M hsD_sum.hasSum
      have hhead_D_eq : (∑ n ∈ Finset.range M, (airyZ n - lam) * (w n) ^ 2) =
          ∑ n : Fin J, (airyZ n.1 - lam) * (d n) ^ 2 := by
        have h1 : (∑ n ∈ Finset.range M, (airyZ n - lam) * (w n) ^ 2) =
            ∑ n ∈ Finset.range M, (airyZ n - lam) * (airyPadLp d n) ^ 2 :=
          Finset.sum_congr rfl fun n hn => by rw [hw_lt n (Finset.mem_range.mp hn)]
        have hfinJ := hasSum_fin_of_ge_zero (M := J)
          (f := fun n => (airyZ n - lam) * (airyPadLp d n) ^ 2)
          fun n hn => by rw [airyPadLp_apply_ge d hn, sq, zero_mul, mul_zero]
        have hfinM : HasSum (fun n : ℕ => (airyZ n - lam) * (airyPadLp d n) ^ 2)
            (∑ n ∈ Finset.range M, (airyZ n - lam) * (airyPadLp d n) ^ 2) :=
          hasSum_sum_of_ne_finset_zero fun n hn => by
            have hge : M ≤ n := not_lt.mp (by simpa [Finset.mem_range] using hn)
            rw [airyPadLp_apply_ge d (hMJ.trans hge), sq, zero_mul, mul_zero]
        rw [h1, hfinM.unique hfinJ]
        exact Finset.sum_congr rfl fun n _ => by rw [airyPadLp_apply_lt d n.2]
      have hhead_D_le : -(∑ n : Fin J, (airyZ n.1 - lam) * (d n) ^ 2) ≤
          ((|airyZ J| + |airyZ 0|) * B_d ^ 2) / (M : ℝ) := by
        calc -(∑ n : Fin J, (airyZ n.1 - lam) * (d n) ^ 2)
            ≤ |∑ n : Fin J, (airyZ n.1 - lam) * (d n) ^ 2| := neg_le_abs _
          _ ≤ ∑ n : Fin J, |(airyZ n.1 - lam) * (d n) ^ 2| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ n : Fin J, (|airyZ J| + |airyZ 0|) * (d n) ^ 2 := by
              refine Finset.sum_le_sum fun n _ => ?_
              rw [abs_mul, abs_of_nonneg (sq_nonneg (d n))]
              have hzm : |airyZ n.1 - lam| ≤ |airyZ J| + |airyZ 0| := by
                have h1 : airyZ J ≤ airyZ n.1 := airyZ_anti n.2.le
                have h2 : airyZ n.1 ≤ airyZ 0 := airyZ_anti (Nat.zero_le n.1)
                have hlam_lo : airyZ J ≤ lam := (airyZ_anti (by omega : k ≤ J)).trans hlam_bds.1
                have hz0 : airyZ 0 < 0 := airyZ_neg 0
                have habs0 : 0 ≤ |airyZ 0| := abs_nonneg _
                rw [abs_of_neg (airyZ_neg J), abs_le]
                constructor <;> linarith only [h1, h2, hlam_lo, hlam_bds.2, hz0, habs0]
              exact mul_le_mul_of_nonneg_right hzm (sq_nonneg _)
          _ = (|airyZ J| + |airyZ 0|) * ∑ n : Fin J, (d n) ^ 2 := (Finset.mul_sum _ _ _).symm
          _ ≤ (|airyZ J| + |airyZ 0|) * (B_d / (M : ℝ)) ^ 2 :=
              mul_le_mul_of_nonneg_left hd_norm_sq (by positivity)
          _ ≤ ((|airyZ J| + |airyZ 0|) * B_d ^ 2) / (M : ℝ) := by
              rw [div_pow, ← mul_div_assoc]
              refine div_le_div₀ (by positivity) le_rfl hM_pos ?_
              have h1M : 1 ≤ (M : ℝ) := by exact_mod_cast hJM_ge1
              nlinarith only [h1M]
      have htail_D_le : -(∑' m : ℕ, (airyZ (M + m) - lam) * (w (M + m)) ^ 2) ≤
          (M_c ^ 2 / 8) / (M : ℝ) := by
        rw [← tsum_neg]
        have hle_abs : ∀ m : ℕ, -((airyZ (M + m) - lam) * (w (M + m)) ^ 2) ≤
            |airyZ (M + m)| * (c (M + m)) ^ 2 := by
          intro m
          rw [hw_ge (M + m) (Nat.le_add_right M m), neg_sq, abs_of_neg (airyZ_neg (M + m))]
          have hlam_neg : lam < 0 := lt_of_le_of_lt hlam_bds.2 (airyZ_neg 0)
          have hgap_le : -(airyZ (M + m) - lam) ≤ -airyZ (M + m) := by linarith only [hlam_neg]
          have hmul := mul_le_mul_of_nonneg_right hgap_le (sq_nonneg (c (M + m)))
          linarith only [hmul]
        exact (Summable.tsum_le_tsum hle_abs hshift_D.summable.neg htail_sum_abs).trans htail_tsum_le
      have hsplit_eq : -(∑' n : ℕ, (airyZ n - lam) * (w n) ^ 2) =
          -(∑ n : Fin J, (airyZ n.1 - lam) * (d n) ^ 2) +
            -(∑' m : ℕ, (airyZ (M + m) - lam) * (w (M + m)) ^ 2) := by
        rw [hhead_D_eq] at hshift_D
        linarith only [hshift_D.tsum_eq]
      rw [hsplit_eq]
      calc -(∑ n : Fin J, (airyZ n.1 - lam) * (d n) ^ 2) +
              -(∑' m : ℕ, (airyZ (M + m) - lam) * (w (M + m)) ^ 2)
          ≤ ((|airyZ J| + |airyZ 0|) * B_d ^ 2) / (M : ℝ) + (M_c ^ 2 / 8) / (M : ℝ) :=
            add_le_add hhead_D_le htail_D_le
        _ = ((|airyZ J| + |airyZ 0|) * B_d ^ 2 + M_c ^ 2 / 8) / (M : ℝ) := (add_div _ _ _).symm
    -- Compare `Λ_M(s)` with the Rayleigh quotient of `v`.
    have hv_sec : (∑ n : Fin M, airyZ n.1 * (v n) ^ 2) / (∑ n : Fin M, (v n) ^ 2) ≤
        airyLambdaSection s M :=
      le_airyLambdaSection_of_mem hMk ⟨v, hv_ne, hv_ker, rfl⟩
    have hv_pos : 0 < ∑ n : Fin M, (v n) ^ 2 := lt_of_lt_of_le (by norm_num) hv_sq_ge
    have hquot_diff : lam - (∑ n : Fin M, airyZ n.1 * (v n) ^ 2) / (∑ n : Fin M, (v n) ^ 2) =
        (-(∑' n : ℕ, (airyZ n - lam) * (w n) ^ 2)) / (∑ n : Fin M, (v n) ^ 2) := by
      have hne_v : (∑ n : Fin M, (v n) ^ 2) ≠ 0 := hv_pos.ne'
      rw [← hv_quad_eq]
      field_simp
      ring
    have hloss_nonneg : 0 ≤ -(∑' n : ℕ, (airyZ n - lam) * (w n) ^ 2) := by
      have hv_ub : airySquareRayleigh ((‖airyPadLp v‖⁻¹ : ℝ) • airyPadLp v) ≤ lam := by
        have hfeas : AirySquareUnitFeasible s ((‖airyPadLp v‖⁻¹ : ℝ) • airyPadLp v) := by
          have hv_n_pos : 0 < ‖airyPadLp v‖ := lt_of_lt_of_le (by norm_num) hv_norm_ge
          refine ⟨?_, ?_, ?_⟩
          · rw [hasSum_sq_one_iff_norm_eq_one, norm_smul, Real.norm_eq_abs,
              abs_of_pos (inv_pos.mpr hv_n_pos), inv_mul_cancel₀ hv_n_pos.ne']
          · refine (summable_abs_airyZ_airyPadLp v |>.mul_left ((‖airyPadLp v‖⁻¹) ^ 2)).congr
              fun n => by simp [Pi.smul_apply, smul_eq_mul]; ring
          · rw [← airyEvalMap_eq_zero_iff, map_smul, (airyEvalMap_eq_zero_iff s _).mpr
              (fun j => by rw [airyCardinalSeriesR_airyPadLp, hv_ker j]), smul_zero]
        exact le_csSup (bddAbove_airySquareUnitFeasible s) ⟨_, hfeas, rfl⟩
      have hray_smul : airySquareRayleigh ((‖airyPadLp v‖⁻¹ : ℝ) • airyPadLp v) =
          (∑ n : Fin M, airyZ n.1 * (v n) ^ 2) / (∑ n : Fin M, (v n) ^ 2) := by
        unfold airySquareRayleigh
        have hcongr : (fun n : ℕ => airyZ n * (((‖airyPadLp v‖⁻¹ : ℝ) • airyPadLp v) n) ^ 2) =
            fun n : ℕ => (‖airyPadLp v‖⁻¹) ^ 2 * (airyZ n * (airyPadLp v n) ^ 2) := by
          ext n; simp [Pi.smul_apply, smul_eq_mul]; ring
        rw [hcongr, tsum_mul_left, ← airySquareRayleigh, airySquareRayleigh_airyPadLp,
          inv_pow, norm_sq_airyPadLp, inv_mul_eq_div]
      rw [hray_smul] at hv_ub
      have hmul := mul_nonneg (sub_nonneg.mpr hv_ub) hv_pos.le
      rw [hquot_diff, div_mul_cancel₀ _ hv_pos.ne'] at hmul
      exact hmul
    calc lam - airyLambdaSection s M
        ≤ lam - (∑ n : Fin M, airyZ n.1 * (v n) ^ 2) / (∑ n : Fin M, (v n) ^ 2) := by
          linarith only [hv_sec]
      _ = (-(∑' n : ℕ, (airyZ n - lam) * (w n) ^ 2)) / (∑ n : Fin M, (v n) ^ 2) := hquot_diff
      _ ≤ (-(∑' n : ℕ, (airyZ n - lam) * (w n) ^ 2)) / (1 / 4 : ℝ) :=
          div_le_div_of_nonneg_left hloss_nonneg (by norm_num) hv_sq_ge
      _ = 4 * (-(∑' n : ℕ, (airyZ n - lam) * (w n) ^ 2)) := by ring
      _ ≤ 4 * (((|airyZ J| + |airyZ 0|) * B_d ^ 2 + M_c ^ 2 / 8) / (M : ℝ)) :=
          mul_le_mul_of_nonneg_left hloss_le (by norm_num)
      _ = C_hi / (M : ℝ) := by dsimp [C_hi]; ring
      _ ≤ C / (M : ℝ) := div_le_div_of_nonneg_right (le_max_left _ _) hM_pos.le

/-- **Identification `λ_*(s) = λ(s)` (`thm:airy-square-attained`(1)):** for distinct sites `s`, the
infinite constrained `ℓ²` Rayleigh supremum `airyLambdaInf s` equals `airyLambda s = sup_M Λ_M(s)`. -/
theorem airyLambdaInf_eq_airyLambda {k : ℕ} {s : Fin k → ℝ} (hs : Function.Injective s) :
    airyLambdaInf s = airyLambda s := by
  refine le_antisymm ?_ (airyLambda_le_airyLambdaInf s)
  obtain ⟨C, _, hC⟩ := airyLambdaInf_sub_section_le_on_compact (K := {s}) isCompact_singleton
    (fun x hx => by rwa [mem_singleton_iff.mp hx])
  have hbound : ∀ᶠ M : ℕ in atTop, airyLambdaInf s ≤ airyLambdaSection s M + C / (M : ℝ) := by
    filter_upwards [eventually_ge_atTop (k + 1)] with M hM
    linarith only [hC s (mem_singleton s) M hM]
  have hlim_rhs : Tendsto (fun M : ℕ => airyLambdaSection s M + C / (M : ℝ)) atTop
      (𝓝 (airyLambda s + 0)) := by
    refine (tendsto_airyLambdaSection s).add ?_
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul C
  rw [add_zero] at hlim_rhs
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim_rhs hbound

/-- **Part (1) attainment (`thm:airy-square-attained`(1)):** `λ(s)` is attained as a maximum on
`AirySquareUnitFeasible s`. -/
theorem isGreatest_airySquareRayleigh {k : ℕ} {s : Fin k → ℝ} (hs : Function.Injective s) :
    IsGreatest (airySquareRayleigh '' {c : lp (fun _ : ℕ => ℝ) 2 | AirySquareUnitFeasible s c})
      (airyLambda s) := by
  rw [← airyLambdaInf_eq_airyLambda hs]
  obtain ⟨c, hc_feas, hc_eq⟩ := exists_airyLambdaInf_maximizer s
  refine ⟨⟨c, hc_feas, hc_eq⟩, ?_⟩
  rintro _ ⟨u, hu_feas, rfl⟩
  exact le_csSup (bddAbove_airySquareUnitFeasible s) ⟨u, hu_feas, rfl⟩

/-- **Part (1) uniform `O(M⁻¹)` rate (`thm:airy-square-attained`(1)):** on any compact subset `K`
of distinct site vectors, `0 ≤ λ(s) - Λ_M(s) ≤ C / M` for all `s ∈ K` and `M ≥ k + 1`. -/
theorem airyLambda_sub_section_le_on_compact {k : ℕ} {K : Set (Fin k → ℝ)}
    (hK : IsCompact K) (hK_inj : ∀ s ∈ K, Function.Injective s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ∀ M : ℕ, k + 1 ≤ M →
      0 ≤ airyLambda s - airyLambdaSection s M ∧
      airyLambda s - airyLambdaSection s M ≤ C / (M : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := airyLambdaInf_sub_section_le_on_compact hK hK_inj
  refine ⟨C, hC0, fun s hs M hM => ⟨?_, ?_⟩⟩
  · linarith only [airyLambdaSection_le_airyLambda s hM]
  · rw [← airyLambdaInf_eq_airyLambda (hK_inj s hs)]
    exact hC s hs M hM

/-- **Part (2) multiplier representation (`thm:airy-square-attained`(2), `eq:airy-square-rep`):**
for any unit maximizer `c` at distinct sites `s`, there exist `μ : Fin k → ℝ` such that
`(a_n - λ(s)) c_n = ∑_j μ_j k_n(s_j)` for all `n`, `|c_n| ≤ M_c / a_n²`, `∑_n |c_n| < ∞`, and
`(z - λ(s)) q_c(z) = (∑_n c_n) Ai(z) + ∑_j μ_j K(z, s_j)` on `ℂ`. -/
theorem airySquare_maximizer_representation {k : ℕ} {s : Fin k → ℝ} (hs : Function.Injective s)
    {c : lp (fun _ : ℕ => ℝ) 2} (hc : AirySquareUnitFeasible s c)
    (hc_max : airySquareRayleigh c = airyLambda s) :
    ∃ (μ : Fin k → ℝ) (M_c : ℝ),
      0 ≤ M_c ∧
      (∀ n : ℕ, (airyZ n - airyLambda s) * c n = ∑ j : Fin k, μ j * airyCardinalR n (s j)) ∧
      (∀ n : ℕ, |c n| ≤ M_c / (airyZ n) ^ 2) ∧
      Summable (fun n : ℕ => |c n|) ∧
      (∀ z : ℂ, (z - (airyLambda s : ℂ)) * airyCardinalSeries c z =
        ((∑' n : ℕ, c n : ℝ) : ℂ) * airyAiC z +
          ∑ j : Fin k, (μ j : ℂ) * airyKerC z (s j : ℂ)) := by
  obtain ⟨J, M_R, hJ_ge, hMR, hblock⟩ := exists_uniform_rightInv_on_compact (K := {s})
    isCompact_singleton (fun x hx => by rwa [mem_singleton_iff.mp hx])
  obtain ⟨hdet, hR_bd⟩ := hblock s (mem_singleton s)
  have hc_inf : airySquareRayleigh c = airyLambdaInf s := by
    rwa [airyLambdaInf_eq_airyLambda hs]
  obtain ⟨μ, _, hmult, hdecay, habs, hrep⟩ :=
    airyLambdaInf_multiplier_rep_from_block hJ_ge hMR (le_rfl : (∑ j : Fin k, |s j|) ≤ ∑ j : Fin k, |s j|)
      hdet hR_bd hc hc_inf
  rw [airyLambdaInf_eq_airyLambda hs] at hmult hrep
  exact ⟨μ, airyDecayConst k J M_R (∑ j : Fin k, |s j|),
    airyDecayConst_nonneg k J M_R _, hmult, hdecay, habs, hrep⟩

/-- Openness of the set `{s : Fin k → ℝ | Function.Injective s}` of distinct site vectors. -/
lemma isOpen_injective_sites (k : ℕ) : IsOpen {s : Fin k → ℝ | Function.Injective s} := by
  have heq : {s : Fin k → ℝ | Function.Injective s} =
      ⋂ (p : Fin k × Fin k) (_ : p.1 ≠ p.2), {s : Fin k → ℝ | s p.1 ≠ s p.2} := by
    ext s
    simp only [mem_ofPred_eq, mem_iInter, Prod.forall]
    exact ⟨fun hs i j hij heq_s => hij (hs heq_s),
      fun h i j heq_s => by_contra fun hij => h i j hij heq_s⟩
  rw [heq]
  exact isOpen_iInter_of_finite fun p => isOpen_iInter_of_finite fun _ =>
    isOpen_ne_fun (continuous_apply p.1) (continuous_apply p.2)

/-- **Part (1) local Lipschitz continuity (`thm:airy-square-attained`(1)):** `airyLambda` is locally
Lipschitz on `{s : Fin k → ℝ | Function.Injective s}`. -/
theorem locallyLipschitzOn_airyLambda (k : ℕ) :
    LocallyLipschitzOn {s : Fin k → ℝ | Function.Injective s} (airyLambda (k := k)) := by
  intro s₀ hs₀
  obtain ⟨r₂, hr₂_pos, hr₂_sub⟩ := Metric.isOpen_iff.mp (isOpen_injective_sites k) s₀ hs₀
  set r₀ := r₂ / 2
  have hr₀_pos : 0 < r₀ := half_pos hr₂_pos
  have hK_sub : closedBall s₀ r₀ ⊆ {s : Fin k → ℝ | Function.Injective s} :=
    (closedBall_subset_ball (half_lt_self hr₂_pos)).trans hr₂_sub
  have hK_comp : IsCompact (closedBall s₀ r₀) := isCompact_closedBall s₀ r₀
  obtain ⟨J, M_R, hJ_ge, hMR, hblock⟩ :=
    exists_uniform_rightInv_on_compact hK_comp fun s hs => hK_sub hs
  set R_ball := ‖s₀‖ + r₀
  obtain ⟨L_ev, hL_ev_nn, hL_ev⟩ := exists_airyEvalVec_lipschitz_on_ball R_ball
  set C_e := (k : ℝ) * M_R * L_ev
  set C_d := √(J : ℝ) * C_e
  have hCe_nn : 0 ≤ C_e := by positivity
  have hCd_nn : 0 ≤ C_d := by positivity
  set r₁ := min r₀ (1 / (4 * (C_d + C_e + 1)))
  have hr₁_pos : 0 < r₁ := lt_min hr₀_pos (by positivity)
  set K_lip := 4 * ((J : ℝ) * (|airyZ J| + |airyZ 0|) * (3 * C_e))
  refine ⟨Real.toNNReal K_lip, closedBall s₀ r₁,
    mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds s₀ hr₁_pos), ?_⟩
  refine LipschitzOnWith.of_le_add_mul' K_lip fun s hs_b s' hs'_b => ?_
  have hs_K : s ∈ closedBall s₀ r₀ := closedBall_subset_closedBall (min_le_left _ _) hs_b
  have hs'_K : s' ∈ closedBall s₀ r₀ := closedBall_subset_closedBall (min_le_left _ _) hs'_b
  have hs_inj : Function.Injective s := hK_sub hs_K
  have hs'_inj : Function.Injective s' := hK_sub hs'_K
  obtain ⟨hdet', hR'_bd⟩ := hblock s' hs'_K
  obtain ⟨⟨c, hc_feas, hc_max⟩, _⟩ := isGreatest_airySquareRayleigh hs_inj
  have hc_norm : ‖c‖ = 1 := (hasSum_sq_one_iff_norm_eq_one c).mp hc_feas.1
  -- Coordinate bounds `|s j|, |s' j| ≤ R_ball`.
  have hcoord_ball : ∀ x ∈ closedBall s₀ r₀, ∀ j : Fin k, |x j| ≤ R_ball := by
    intro x hx j
    have hx_norm : ‖x‖ ≤ R_ball := by
      have h1 := norm_add_le s₀ (x - s₀)
      rw [add_sub_cancel] at h1
      have h2 : ‖x - s₀‖ ≤ r₀ := by rwa [mem_closedBall, dist_eq_norm] at hx
      linarith only [h1, h2]
    exact (norm_le_pi_norm x j).trans hx_norm
  -- Residual `r_vec j = q_c(s' j)` at `s'` has `|r_vec j| ≤ L_ev * dist s s'`.
  let r_vec : Fin k → ℝ := fun j => airyCardinalSeriesR c (s' j)
  have hr_vec_le : ∀ j : Fin k, |r_vec j| ≤ L_ev * dist s s' := by
    intro j
    have heq : r_vec j = inner ℝ (airyEvalVec (s' j) - airyEvalVec (s j)) c := by
      rw [inner_sub_left, inner_airyEvalVec, inner_airyEvalVec, hc_feas.2.2 j, sub_zero]
    rw [heq]
    have hcs := abs_real_inner_le_norm (airyEvalVec (s' j) - airyEvalVec (s j)) c
    rw [hc_norm, mul_one] at hcs
    have hlip := hL_ev (s' j) (s j) (hcoord_ball s' hs'_K j) (hcoord_ball s hs_K j)
    have hcoord_dist : |s' j - s j| ≤ dist s s' := by
      rw [dist_comm, dist_eq_norm]
      exact norm_le_pi_norm (s' - s) j
    exact hcs.trans (hlip.trans (mul_le_mul_of_nonneg_left hcoord_dist hL_ev_nn))
  -- Finite-block correction `d = -R_J(s') r_vec`.
  let d : Fin J → ℝ := -(airyRightInvMat s' J).mulVec r_vec
  have hd_entry : ∀ n : Fin J, |d n| ≤ C_e * dist s s' := by
    intro n
    have hdn : d n = -∑ j : Fin k, airyRightInvMat s' J n j * r_vec j := by
      simp [d, Matrix.mulVec, dotProduct]
    rw [hdn, abs_neg]
    calc |∑ j : Fin k, airyRightInvMat s' J n j * r_vec j|
        ≤ ∑ j : Fin k, |airyRightInvMat s' J n j * r_vec j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin k, M_R * (L_ev * dist s s') := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hR'_bd n j) (hr_vec_le j) (abs_nonneg _) hMR
      _ = C_e * dist s s' := by dsimp [C_e]; simp; ring
  have hd_norm : ‖airyPadLp d‖ ≤ C_d * dist s s' := by
    refine le_of_sq_le_sq ?_ (mul_nonneg hCd_nn dist_nonneg)
    rw [norm_sq_airyPadLp]
    calc (∑ n : Fin J, (d n) ^ 2)
        ≤ ∑ _n : Fin J, (C_e * dist s s') ^ 2 := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [← sq_abs (d n)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hd_entry n) 2
      _ = (J : ℝ) * (C_e * dist s s') ^ 2 := by simp
      _ = (C_d * dist s s') ^ 2 := by
          have hJ2 : √(J : ℝ) ^ 2 = (J : ℝ) := Real.sq_sqrt (Nat.cast_nonneg J)
          have hpow : (√(J : ℝ) * C_e * dist s s') ^ 2 =
              √(J : ℝ) ^ 2 * (C_e * dist s s') ^ 2 := by ring
          dsimp [C_d]
          rw [hpow, hJ2]
  have hdist_le : dist s s' ≤ 2 * r₁ := by
    calc dist s s' ≤ dist s s₀ + dist s₀ s' := dist_triangle s s₀ s'
      _ = dist s s₀ + dist s' s₀ := by rw [dist_comm s₀ s']
      _ ≤ r₁ + r₁ := add_le_add (mem_closedBall.mp hs_b) (mem_closedBall.mp hs'_b)
      _ = 2 * r₁ := by ring
  have hsmall_prod : (C_d + C_e + 1) * dist s s' ≤ 1 / 2 := by
    have hr₁_le : r₁ ≤ 1 / (4 * (C_d + C_e + 1)) := min_le_right _ _
    calc (C_d + C_e + 1) * dist s s'
        ≤ (C_d + C_e + 1) * (2 * r₁) := mul_le_mul_of_nonneg_left hdist_le (by positivity)
      _ ≤ (C_d + C_e + 1) * (2 * (1 / (4 * (C_d + C_e + 1)))) :=
          mul_le_mul_of_nonneg_left (by linarith only [hr₁_le]) (by positivity)
      _ = 1 / 2 := by
          have : C_d + C_e + 1 ≠ 0 := by positivity
          field_simp; ring
  have hd_norm_half : ‖airyPadLp d‖ ≤ 1 / 2 := by
    have h1 : C_d * dist s s' ≤ (C_d + C_e + 1) * dist s s' :=
      mul_le_mul_of_nonneg_right (by linarith only [hCe_nn]) dist_nonneg
    exact hd_norm.trans (h1.trans hsmall_prod)
  have hd_entry_one : ∀ n : Fin J, |d n| ≤ 1 := by
    intro n
    have h1 : C_e * dist s s' ≤ (C_d + C_e + 1) * dist s s' :=
      mul_le_mul_of_nonneg_right (by linarith only [hCd_nn]) dist_nonneg
    exact (hd_entry n).trans ((h1.trans hsmall_prod).trans (by norm_num))
  let u : lp (fun _ : ℕ => ℝ) 2 := c + airyPadLp d
  have hu_apply : ∀ n : ℕ, u n = c n + airyPadLp d n := fun n => by simp [u]
  have hu_norm_ge : 1 / 2 ≤ ‖u‖ := by
    have htri := norm_add_le u (-airyPadLp d)
    have huv : u + -airyPadLp d = c := by dsimp [u]; abel
    rw [huv, norm_neg, hc_norm] at htri
    linarith only [htri, hd_norm_half]
  have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le (by norm_num) hu_norm_ge
  have hu_sq_ge : 1 / 4 ≤ ‖u‖ ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hu_norm_ge 2
    norm_num at h; exact h
  have hu_sum : Summable (fun n : ℕ => |airyZ n| * (u n) ^ 2) := by
    have hdom : Summable (fun n : ℕ => 2 * (|airyZ n| * (c n) ^ 2) +
        2 * (|airyZ n| * (airyPadLp d n) ^ 2)) :=
      (hc_feas.2.1.mul_left 2).add ((summable_abs_airyZ_airyPadLp d).mul_left 2)
    refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
      (fun n => ?_) hdom
    rw [hu_apply n]
    have hsq : (c n + airyPadLp d n) ^ 2 ≤ 2 * (c n) ^ 2 + 2 * (airyPadLp d n) ^ 2 := by
      nlinarith only [sq_nonneg (c n - airyPadLp d n)]
    have hmul := mul_le_mul_of_nonneg_left hsq (abs_nonneg (airyZ n))
    linarith only [hmul]
  have hu_ker : ∀ j : Fin k, airyCardinalSeriesR u (s' j) = 0 := by
    intro j
    rw [← airyEvalMap_apply]
    change airyEvalMap s' (c + airyPadLp d) j = 0
    rw [map_add, Pi.add_apply, airyEvalMap_apply, airyEvalMap_apply, airyCardinalSeriesR_airyPadLp,
      ← airyBlockMat_mulVec]
    dsimp [d]
    rw [Matrix.mulVec_neg, Pi.neg_apply, airyBlockMat_mulVec_airyRightInvMat hdet', add_neg_cancel]
  -- Normalize `u` to compete in `airyLambda s'`.
  let u_unit : lp (fun _ : ℕ => ℝ) 2 := (‖u‖⁻¹ : ℝ) • u
  have hu_unit_feas : AirySquareUnitFeasible s' u_unit := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hasSum_sq_one_iff_norm_eq_one]
      change ‖(‖u‖⁻¹ : ℝ) • u‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu_pos), inv_mul_cancel₀ hu_pos.ne']
    · refine (hu_sum.mul_left ((‖u‖⁻¹) ^ 2)).congr fun n => ?_
      simp [u_unit, Pi.smul_apply, smul_eq_mul]; ring
    · rw [← airyEvalMap_eq_zero_iff]
      change airyEvalMap s' ((‖u‖⁻¹ : ℝ) • u) = 0
      rw [map_smul, (airyEvalMap_eq_zero_iff s' u).mpr hu_ker, smul_zero]
  have hu_ray_le : airySquareRayleigh u / ‖u‖ ^ 2 ≤ airyLambda s' := by
    have h1 : airySquareRayleigh u_unit ≤ airyLambda s' :=
      (isGreatest_airySquareRayleigh hs'_inj).2 ⟨u_unit, hu_unit_feas, rfl⟩
    have h2 : airySquareRayleigh u_unit = airySquareRayleigh u / ‖u‖ ^ 2 := by
      unfold airySquareRayleigh
      have hcongr : (fun n : ℕ => airyZ n * (u_unit n) ^ 2) =
          fun n : ℕ => (‖u‖⁻¹) ^ 2 * (airyZ n * (u n) ^ 2) := by
        ext n; simp [u_unit, Pi.smul_apply, smul_eq_mul]; ring
      rw [hcongr, tsum_mul_left, inv_pow, inv_mul_eq_div]
    rwa [h2] at h1
  -- Finite-sum difference `(airyLambda s * ‖u‖² - airySquareRayleigh u)`.
  set lam := airyLambda s
  have hfin_diff : lam * ‖u‖ ^ 2 - airySquareRayleigh u =
      ∑ n : Fin J, (lam - airyZ n.1) * (2 * c n.1 * d n + (d n) ^ 2) := by
    have hc1_sum : HasSum (fun n : ℕ => airyZ n * (c n) ^ 2) lam := by
      rw [← hc_max]; exact ((summable_airyZ_mul_sq_iff c).mp hc_feas.2.1).hasSum
    have hc2_sum : HasSum (fun n : ℕ => lam * (c n) ^ 2) lam := by
      simpa only [mul_one] using hc_feas.1.mul_left lam
    have hc_zero : HasSum (fun n : ℕ => (lam - airyZ n) * (c n) ^ 2) 0 := by
      have h := hc2_sum.sub hc1_sum
      rw [sub_self] at h
      exact h.congr_fun fun n => by ring
    have hu1_sum := ((summable_airyZ_mul_sq_iff u).mp hu_sum).hasSum
    have hu2_sum : HasSum (fun n : ℕ => lam * (u n) ^ 2) (lam * ‖u‖ ^ 2) := by
      have h := lp.hasSum_norm (p := 2) (by norm_num) u
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h
      exact h.mul_left lam
    have hu_diff : HasSum (fun n : ℕ => (lam - airyZ n) * (u n) ^ 2)
        (lam * ‖u‖ ^ 2 - airySquareRayleigh u) :=
      (hu2_sum.sub hu1_sum).congr_fun fun n => by ring
    have hcomb := hu_diff.sub hc_zero
    rw [sub_zero] at hcomb
    have hfin := hasSum_fin_of_ge_zero (M := J)
      (f := fun n => (lam - airyZ n) * (u n) ^ 2 - (lam - airyZ n) * (c n) ^ 2)
      fun n hn => by
        rw [hu_apply n, airyPadLp_apply_ge d hn, add_zero, sub_self]
    rw [hcomb.unique hfin]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hu_apply n.1, airyPadLp_apply_lt d n.2]
    ring
  have hfin_bound : |lam * ‖u‖ ^ 2 - airySquareRayleigh u| ≤
      ((J : ℝ) * (|airyZ J| + |airyZ 0|) * (3 * C_e)) * dist s s' := by
    rw [hfin_diff]
    have hlam_bds := airyLambda_bounds s
    calc |∑ n : Fin J, (lam - airyZ n.1) * (2 * c n.1 * d n + (d n) ^ 2)|
        ≤ ∑ n : Fin J, |(lam - airyZ n.1) * (2 * c n.1 * d n + (d n) ^ 2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n : Fin J, (|airyZ J| + |airyZ 0|) * (3 * (C_e * dist s s')) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [abs_mul]
          have hzm : |lam - airyZ n.1| ≤ |airyZ J| + |airyZ 0| := by
            have h1 : airyZ J ≤ airyZ n.1 := airyZ_anti n.2.le
            have h2 : airyZ n.1 ≤ airyZ 0 := airyZ_anti (Nat.zero_le n.1)
            have hlam_lo : airyZ J ≤ lam := (airyZ_anti (by omega : k ≤ J)).trans hlam_bds.1
            have hz0 : airyZ 0 < 0 := airyZ_neg 0
            have habs0 : 0 ≤ |airyZ 0| := abs_nonneg _
            rw [abs_of_neg (airyZ_neg J), abs_le]
            constructor <;> linarith only [h1, h2, hlam_lo, hlam_bds.2, hz0, habs0]
          have hcn1 : |c n.1| ≤ 1 := by
            have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) c n.1
            rw [Real.norm_eq_abs, hc_norm] at h
            exact h
          have hquad_d : |2 * c n.1 * d n + (d n) ^ 2| ≤ 3 * (C_e * dist s s') := by
            have htri1 := abs_add_le (2 * c n.1 * d n) ((d n) ^ 2)
            rw [abs_mul, abs_mul, Nat.abs_ofNat, abs_pow] at htri1
            have hpart1 : 2 * |c n.1| * |d n| ≤ 2 * |d n| := by
              nlinarith only [hcn1, abs_nonneg (d n)]
            have hpart2 : |d n| ^ 2 ≤ |d n| := by
              nlinarith only [hd_entry_one n, abs_nonneg (d n)]
            linarith only [htri1, hpart1, hpart2, hd_entry n]
          exact mul_le_mul hzm hquad_d (abs_nonneg _) (by positivity)
      _ = ((J : ℝ) * (|airyZ J| + |airyZ 0|) * (3 * C_e)) * dist s s' := by simp; ring
  have hquot_id : lam - airySquareRayleigh u / ‖u‖ ^ 2 =
      (lam * ‖u‖ ^ 2 - airySquareRayleigh u) / ‖u‖ ^ 2 := by
    have hne_u : ‖u‖ ^ 2 ≠ 0 := (sq_pos_of_pos hu_pos).ne'
    field_simp
  have hstep : lam - airyLambda s' ≤ K_lip * dist s s' := by
    calc lam - airyLambda s'
        ≤ lam - airySquareRayleigh u / ‖u‖ ^ 2 := by linarith only [hu_ray_le]
      _ = (lam * ‖u‖ ^ 2 - airySquareRayleigh u) / ‖u‖ ^ 2 := hquot_id
      _ ≤ |lam * ‖u‖ ^ 2 - airySquareRayleigh u| / ‖u‖ ^ 2 :=
          div_le_div_of_nonneg_right (le_abs_self _) (sq_nonneg _)
      _ ≤ |lam * ‖u‖ ^ 2 - airySquareRayleigh u| / (1 / 4 : ℝ) :=
          div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hu_sq_ge
      _ = 4 * |lam * ‖u‖ ^ 2 - airySquareRayleigh u| := by ring
      _ ≤ 4 * (((J : ℝ) * (|airyZ J| + |airyZ 0|) * (3 * C_e)) * dist s s') :=
          mul_le_mul_of_nonneg_left hfin_bound (by norm_num)
      _ = K_lip * dist s s' := by dsimp [K_lip]; ring
  linarith only [hstep]

/-- **Part (1) general finite-section exactness (`thm:airy-square-attained`(1)):** for distinct
sites `s` and `M ≥ k + 1`, `Λ_M(s) = λ(s)` if and only if every site `s j` is a Dirichlet node
`airyZ n`. -/
theorem airyLambdaSection_eq_airyLambda_iff {k M : ℕ} {s : Fin k → ℝ}
    (hs : Function.Injective s) (hM : k + 1 ≤ M) :
    airyLambdaSection s M = airyLambda s ↔ ∀ j : Fin k, ∃ n : ℕ, s j = airyZ n := by
  constructor
  · intro heq
    obtain ⟨c_fin, hc1, hcker, hceq⟩ := exists_unit_section_maximizer s hM
    let c : lp (fun _ : ℕ => ℝ) 2 := airyPadLp c_fin
    have hc_feas : AirySquareUnitFeasible s c := airyPadLp_unitFeasible hc1 hcker
    have hc_max : airySquareRayleigh c = airyLambda s := by
      rw [airySquareRayleigh_airyPadLp, hceq, heq]
    obtain ⟨μ, _, _, hmult, _, _, _⟩ := airySquare_maximizer_representation hs hc_feas hc_max
    -- Beyond `M` and all sites, `c_n = 0` kills off-node multipliers via `sum_div_sub_airyZ_eq_zero`.
    set R := (∑ i : Fin k, |s i|) + 1
    have hev := eventually_le_neg_airyZ R
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N₁, hN₁⟩ := hev
    let N₀ := max M N₁
    have hlt_site : ∀ n : ℕ, N₀ ≤ n → ∀ j : Fin k, airyZ n < s j := by
      intro n hn j
      have h1 := hN₁ n ((le_max_right M N₁).trans hn)
      have h2 : |s j| ≤ ∑ i : Fin k, |s i| :=
        Finset.single_le_sum (fun i _ => abs_nonneg (s i)) (Finset.mem_univ j)
      have h3 : -|s j| ≤ s j := neg_abs_le (s j)
      dsimp [R] at h1
      linarith only [h1, h2, h3]
    let T : Finset (Fin k) := Finset.univ.filter (fun j : Fin k => airyAi (s j) ≠ 0)
    have hμ_off : ∀ j ∈ T, μ j = 0 := by
      have hβ0 : ∀ j ∈ T, μ j * airyAi (s j) = 0 := by
        refine sum_div_sub_airyZ_eq_zero hs T (fun j => μ j * airyAi (s j)) N₀
          (fun n hn j _ => (hlt_site n hn j).ne') (fun n hn => ?_)
        have htot := hmult n
        have hcn0 : c n = 0 := airyPadLp_apply_ge c_fin ((le_max_left M N₁).trans hn)
        rw [hcn0, mul_zero] at htot
        have htot' := htot.symm
        have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun j : Fin k => airyAi (s j) ≠ 0) (fun j => μ j * airyCardinalR n (s j))).symm
        rw [hsplit] at htot'
        have hdir : (∑ j ∈ Finset.univ.filter (fun j : Fin k => ¬ airyAi (s j) ≠ 0),
            μ j * airyCardinalR n (s j)) = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          have hAi0 : airyAi (s j) = 0 := not_not.mp (Finset.mem_filter.mp hj).2
          obtain ⟨p, hp⟩ := exists_airyZ_eq_of_airyAi_eq_zero hAi0
          have hnp : n ≠ p := by
            intro hnp_eq
            have := hlt_site n hn j
            rw [hp, hnp_eq] at this
            exact lt_irrefl _ this
          rw [hp, airyCardinalR_airyZ]
          simp [hnp]
        rw [hdir, add_zero] at htot'
        have hcongr : (∑ j ∈ T, (μ j * airyAi (s j)) / (s j - airyZ n)) =
            ∑ j ∈ T, μ j * airyCardinalR n (s j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [airyCardinalR_of_ne n (hlt_site n hn j).ne', mul_div_assoc]
        rwa [hcongr]
      intro j hj
      exact (mul_eq_zero.mp (hβ0 j hj)).resolve_right (Finset.mem_filter.mp hj).2
    -- Every `n : ℕ` satisfies `(airyZ n - airyLambda s) * c n = 0`.
    have heig : ∀ n : ℕ, (airyZ n - airyLambda s) * c n = 0 := by
      intro n
      by_cases hmem : airyZ n ∈ Set.range s
      · obtain ⟨j₁, hj₁⟩ := hmem
        have heval := hc_feas.2.2 j₁
        rw [hj₁, airyCardinalSeriesR_airyZ] at heval
        have hcn0 : c n = 0 := (mul_eq_zero.mp heval).resolve_right (airyAi'_airyZ_ne_zero n)
        rw [hcn0, mul_zero]
      · rw [hmult n]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hjT : j ∈ T
        · rw [hμ_off j hjT, zero_mul]
        · have hAi0 : airyAi (s j) = 0 := by
            by_contra hne; exact hjT (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩)
          obtain ⟨p, hp⟩ := exists_airyZ_eq_of_airyAi_eq_zero hAi0
          have hnp : n ≠ p := by
            intro hnp_eq
            exact hmem ⟨j, by rw [hp, hnp_eq]⟩
          rw [hp, airyCardinalR_airyZ]
          simp [hnp]
    -- Since `‖c‖ = 1`, some coordinate `p₀` has `c p₀ ≠ 0`, so `c` is supported on `{p₀}`.
    have hc_ne : ∃ p₀ : ℕ, c p₀ ≠ 0 := by
      by_contra hall0
      push Not at hall0
      have h01 : (0 : ℝ) = 1 := hasSum_zero.unique (by simpa [hall0] using hc_feas.1)
      norm_num at h01
    obtain ⟨p₀, hp₀_ne⟩ := hc_ne
    have hlam_eq : airyLambda s = airyZ p₀ := by
      have h0 : airyZ p₀ - airyLambda s = 0 := (mul_eq_zero.mp (heig p₀)).resolve_right hp₀_ne
      linarith only [h0]
    have hc_other : ∀ n : ℕ, n ≠ p₀ → c n = 0 := by
      intro n hnp
      have hne_z : airyZ n - airyLambda s ≠ 0 := by
        rw [hlam_eq]
        exact sub_ne_zero.mpr fun h => hnp (airyZ_injective h)
      exact (mul_eq_zero.mp (heig n)).resolve_left hne_z
    -- Hence `q_c(u) = c p₀ * k_{p₀}(u)`, and `q_c(s j) = 0` forces `Ai(s j) = 0`.
    intro j
    have hseries_single : airyCardinalSeriesR c (s j) = c p₀ * airyCardinalR p₀ (s j) := by
      have h1 := airyCardinalSeriesR_hasSum c (s j)
      have h2 : HasSum (fun n : ℕ => c n * airyCardinalR n (s j))
          (c p₀ * airyCardinalR p₀ (s j)) := by
        refine (hasSum_ite_eq p₀ (c p₀ * airyCardinalR p₀ (s j))).congr_fun fun n => ?_
        by_cases hnp : n = p₀
        · subst hnp; simp
        · simp [hnp, hc_other n hnp]
      exact h1.unique h2
    have hcard0 : airyCardinalR p₀ (s j) = 0 := by
      have h0 := hc_feas.2.2 j
      rw [hseries_single] at h0
      exact (mul_eq_zero.mp h0).resolve_left hp₀_ne
    have hsj_ne : s j ≠ airyZ p₀ := by
      intro heq_z
      rw [heq_z, airyCardinalR_airyZ] at hcard0
      simp only [↓reduceIte] at hcard0
      exact airyAi'_airyZ_ne_zero p₀ hcard0
    rw [airyCardinalR_of_ne p₀ hsj_ne, div_eq_zero_iff] at hcard0
    exact exists_airyZ_eq_of_airyAi_eq_zero (hcard0.resolve_right (sub_ne_zero.mpr hsj_ne))
  · intro hall
    choose p hp using hall
    let P_set : Finset ℕ := Finset.univ.image p
    have hcard_lt : P_set.card < (Finset.range (k + 1)).card := by
      have h1 : P_set.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
      simp only [Finset.card_univ, Fintype.card_fin, Finset.card_range] at h1 ⊢
      omega
    have hdiff_ne : (Finset.range (k + 1) \ P_set).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hempty
      exact not_le.mpr hcard_lt (Finset.card_le_card hempty)
    let n₀ : ℕ := (Finset.range (k + 1) \ P_set).min' hdiff_ne
    have hn₀_mem : n₀ ∈ Finset.range (k + 1) \ P_set := Finset.min'_mem _ hdiff_ne
    have hn₀_lt_k1 : n₀ < k + 1 := Finset.mem_range.mp (Finset.mem_sdiff.mp hn₀_mem).1
    have hn₀_lt_M : n₀ < M := hn₀_lt_k1.trans_le hM
    have hn₀_not_P : ∀ j : Fin k, n₀ ≠ p j := by
      intro j heq_p
      exact (Finset.mem_sdiff.mp hn₀_mem).2 (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, heq_p.symm⟩)
    -- Lower bound `airyZ n₀ ≤ airyLambdaSection s M` via `e_{n₀}`.
    let idx₀ : Fin M := ⟨n₀, hn₀_lt_M⟩
    let v : Fin M → ℝ := Pi.single idx₀ 1
    have hv1 : (∑ n : Fin M, (v n) ^ 2) = 1 := by
      rw [Finset.sum_eq_single idx₀]
      · simp [v]
      · intro n _ hne; simp [v, Pi.single_eq_of_ne hne]
      · intro hnot; exact absurd (Finset.mem_univ idx₀) hnot
    have hv_ne : v ≠ 0 := by intro h0; simp [h0] at hv1
    have hv_ker : ∀ j : Fin k, airySectionPolyR M v (s j) = 0 := by
      intro j
      unfold airySectionPolyR
      rw [Finset.sum_eq_single idx₀]
      · simp only [v, Pi.single_eq_same, one_mul, idx₀, hp j, airyCardinalR_airyZ]
        exact ite_eq_right_iff.mpr fun h => absurd h (hn₀_not_P j)
      · intro n _ hne; simp [v, Pi.single_eq_of_ne hne]
      · intro hnot; exact absurd (Finset.mem_univ idx₀) hnot
    have hv_ray : (∑ n : Fin M, airyZ n.1 * (v n) ^ 2) = airyZ n₀ := by
      rw [Finset.sum_eq_single idx₀]
      · simp [v, idx₀]
      · intro n _ hne; simp [v, Pi.single_eq_of_ne hne]
      · intro hnot; exact absurd (Finset.mem_univ idx₀) hnot
    have hsec_ge : airyZ n₀ ≤ airyLambdaSection s M :=
      le_airyLambdaSection_of_mem hM ⟨v, hv_ne, hv_ker, by rw [hv_ray, hv1, div_one]⟩
    -- Upper bound `airyLambda s ≤ airyZ n₀` because all `m < n₀` lie in `P_set`.
    obtain ⟨⟨c, hc_feas, hc_max⟩, _⟩ := isGreatest_airySquareRayleigh hs
    have hc_lt_zero : ∀ m : ℕ, m < n₀ → c m = 0 := by
      intro m hm_lt
      have hm_in_P : m ∈ P_set := by
        by_contra hm_not
        have hm_sdiff : m ∈ Finset.range (k + 1) \ P_set :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (hm_lt.trans hn₀_lt_k1), hm_not⟩
        exact not_le.mpr hm_lt (Finset.min'_le _ m hm_sdiff)
      obtain ⟨j, _, hjm⟩ := Finset.mem_image.mp hm_in_P
      have heval := hc_feas.2.2 j
      rw [hp j, hjm, airyCardinalSeriesR_airyZ] at heval
      exact (mul_eq_zero.mp heval).resolve_right (airyAi'_airyZ_ne_zero m)
    have hlam_le : airyLambda s ≤ airyZ n₀ := by
      rw [← hc_max]
      have hs1 := ((summable_airyZ_mul_sq_iff c).mp hc_feas.2.1).hasSum
      have hs2 : HasSum (fun n : ℕ => airyZ n₀ * (c n) ^ 2) (airyZ n₀) := by
        simpa only [mul_one] using hc_feas.1.mul_left (airyZ n₀)
      refine hasSum_le (fun n => ?_) hs1 hs2
      by_cases hlt : n < n₀
      · rw [hc_lt_zero n hlt, sq, zero_mul, mul_zero, mul_zero]
      · exact mul_le_mul_of_nonneg_right (airyZ_anti (not_lt.mp hlt)) (sq_nonneg _)
    exact le_antisymm (airyLambdaSection_le_airyLambda s hM) (hlam_le.trans hsec_ge)

/-- **Part (1) first-section exactness (`thm:airy-square-attained`(1)):** for distinct sites `s`,
`Λ_{k+1}(s) = a_{k+1}` (`airyZ k`) if and only if `{s_1, …, s_k} = {a_1, …, a_k}`
(`Set.range s = airyZ '' ↑(Finset.range k)`), and then `λ(s) = a_{k+1}` as well. -/
theorem airyLambdaSection_first_eq_iff {k : ℕ} {s : Fin k → ℝ} (hs : Function.Injective s) :
    (airyLambdaSection s (k + 1) = airyZ k ↔
      Set.range s = airyZ '' (Finset.range k : Set ℕ)) ∧
    (Set.range s = airyZ '' (Finset.range k : Set ℕ) → airyLambda s = airyZ k) := by
  have h_if_range : Set.range s = airyZ '' (Finset.range k : Set ℕ) →
      airyLambdaSection s (k + 1) = airyZ k ∧ airyLambda s = airyZ k := by
    intro hrange
    have hall : ∀ j : Fin k, ∃ n : ℕ, s j = airyZ n := by
      intro j
      have hj : s j ∈ airyZ '' (Finset.range k : Set ℕ) := hrange ▸ mem_range_self j
      obtain ⟨n, _, hzn⟩ := hj
      exact ⟨n, hzn.symm⟩
    have hsec_eq_lam := (airyLambdaSection_eq_airyLambda_iff hs le_rfl).mpr hall
    obtain ⟨c, hc1, hcker, hceq⟩ := exists_unit_section_maximizer s le_rfl
    have hc_lt : ∀ m : ℕ, (hm : m < k) → c ⟨m, hm.trans (Nat.lt_succ_self k)⟩ = 0 := by
      intro m hm
      have hz_in : airyZ m ∈ Set.range s :=
        hrange.symm ▸ ⟨m, Finset.mem_coe.mpr (Finset.mem_range.mpr hm), rfl⟩
      obtain ⟨j, hj⟩ := hz_in
      have heval := hcker j
      rw [hj] at heval
      unfold airySectionPolyR at heval
      let idx_m : Fin (k + 1) := ⟨m, hm.trans (Nat.lt_succ_self k)⟩
      have hsingle : (∑ n : Fin (k + 1), c n * airyCardinalR n.1 (airyZ m)) =
          c idx_m * airyCardinalR m (airyZ m) := by
        refine Finset.sum_eq_single idx_m (fun n _ hne => ?_)
          (fun hnot => absurd (Finset.mem_univ idx_m) hnot)
        have hval_ne : n.1 ≠ m := fun heq => hne (Fin.ext heq)
        simp [airyCardinalR_airyZ, hval_ne]
      have hsingle' : c idx_m * airyCardinalR m (airyZ m) = c idx_m * airyAi' (airyZ m) := by
        simp [airyCardinalR_airyZ]
      rw [hsingle, hsingle'] at heval
      exact (mul_eq_zero.mp heval).resolve_right (airyAi'_airyZ_ne_zero m)
    have hval : airyLambdaSection s (k + 1) = airyZ k := by
      rw [← hceq]
      let idx_k : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
      have h1 : (∑ n : Fin (k + 1), airyZ n.1 * (c n) ^ 2) = airyZ k * (c idx_k) ^ 2 := by
        refine Finset.sum_eq_single idx_k (fun n _ hne => ?_)
          (fun hnot => absurd (Finset.mem_univ idx_k) hnot)
        have hlt : n.1 < k := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp n.2)
          fun heq => hne (Fin.ext heq)
        rw [hc_lt n.1 hlt, sq, zero_mul, mul_zero]
      have h2 : (c idx_k) ^ 2 = 1 := by
        rw [← hc1, eq_comm]
        refine Finset.sum_eq_single idx_k (fun n _ hne => ?_)
          (fun hnot => absurd (Finset.mem_univ idx_k) hnot)
        have hlt : n.1 < k := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp n.2)
          fun heq => hne (Fin.ext heq)
        rw [hc_lt n.1 hlt, sq, zero_mul]
      rw [h1, h2, mul_one]
    exact ⟨hval, hsec_eq_lam.symm.trans hval⟩
  refine ⟨⟨fun hsec => ?_, fun hrange => (h_if_range hrange).1⟩, fun hrange => (h_if_range hrange).2⟩
  -- Every kernel vector `v` of `airyBlockMat s (k + 1)` vanishes on coordinates `< k`.
  have hker_vanish : ∀ v : Fin (k + 1) → ℝ,
      (∀ j : Fin k, airySectionPolyR (k + 1) v (s j) = 0) →
      ∀ n : Fin (k + 1), n.1 < k → v n = 0 := by
    intro v hv n hnk
    by_cases hv0 : v = 0
    · simp [hv0]
    · have hle : (∑ m : Fin (k + 1), airyZ m.1 * (v m) ^ 2) / (∑ m : Fin (k + 1), (v m) ^ 2) ≤
          airyZ k := by
        rw [← hsec]
        exact le_airyLambdaSection_of_mem le_rfl ⟨v, hv0, hv, rfl⟩
      have hpos : 0 < ∑ m : Fin (k + 1), (v m) ^ 2 := sum_sq_pos_of_ne_zero hv0
      have hmul := (div_le_iff₀ hpos).mp hle
      have hsum_nonpos : (∑ m : Fin (k + 1), (airyZ m.1 - airyZ k) * (v m) ^ 2) ≤ 0 := by
        have heq : (∑ m : Fin (k + 1), (airyZ m.1 - airyZ k) * (v m) ^ 2) =
            (∑ m : Fin (k + 1), airyZ m.1 * (v m) ^ 2) -
              airyZ k * (∑ m : Fin (k + 1), (v m) ^ 2) := by
          simp_rw [sub_mul]
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        linarith only [hmul, heq]
      have hterm_nn : ∀ m : Fin (k + 1), 0 ≤ (airyZ m.1 - airyZ k) * (v m) ^ 2 := fun m =>
        mul_nonneg (sub_nonneg.mpr (airyZ_anti (Nat.lt_succ_iff.mp m.2))) (sq_nonneg _)
      have hsum_zero : (∑ m : Fin (k + 1), (airyZ m.1 - airyZ k) * (v m) ^ 2) = 0 :=
        le_antisymm hsum_nonpos (Finset.sum_nonneg fun m _ => hterm_nn m)
      have hn_zero := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => hterm_nn m)).mp
        hsum_zero n (Finset.mem_univ n)
      have hgap_pos : 0 < airyZ n.1 - airyZ k := sub_pos.mpr (airyZ_strictAnti hnk)
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hn_zero).resolve_left hgap_pos.ne')
  -- Pick a nonzero vector `v₀` in the kernel: its `k`-th coordinate is nonzero, forcing `s j = airyZ (p j)` with `p j ≠ k`.
  obtain ⟨v₀, hv₀_ne, hv₀_ker⟩ := exists_nonzero_ker_airyBlockMat s le_rfl
  let lastIdx : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hv₀_last : v₀ lastIdx ≠ 0 := by
    intro hlast0
    apply hv₀_ne
    ext n
    by_cases hnk : n.1 < k
    · exact hker_vanish v₀ hv₀_ker n hnk
    · have hne_eq : n = lastIdx := Fin.ext (by dsimp [lastIdx]; have := n.2; omega)
      rw [hne_eq, hlast0]; rfl
  have hall_dir : ∀ j : Fin k, ∃ p : ℕ, p < k ∧ s j = airyZ p := by
    intro j
    have heval := hv₀_ker j
    unfold airySectionPolyR at heval
    have hsingle : (∑ n : Fin (k + 1), v₀ n * airyCardinalR n.1 (s j)) =
        v₀ lastIdx * airyCardinalR k (s j) := by
      refine Finset.sum_eq_single lastIdx (fun n _ hne => ?_)
        (fun hnot => absurd (Finset.mem_univ lastIdx) hnot)
      have hnk : n.1 < k := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp n.2)
        fun heq => hne (Fin.ext heq)
      rw [hker_vanish v₀ hv₀_ker n hnk, zero_mul]
    rw [hsingle] at heval
    have hcard0 : airyCardinalR k (s j) = 0 := (mul_eq_zero.mp heval).resolve_left hv₀_last
    have hsj_ne : s j ≠ airyZ k := by
      intro heq_z
      rw [heq_z, airyCardinalR_airyZ] at hcard0
      simp only [↓reduceIte] at hcard0
      exact airyAi'_airyZ_ne_zero k hcard0
    rw [airyCardinalR_of_ne k hsj_ne, div_eq_zero_iff] at hcard0
    obtain ⟨p, hp⟩ := exists_airyZ_eq_of_airyAi_eq_zero
      (hcard0.resolve_right (sub_ne_zero.mpr hsj_ne))
    have hpk_ne : p ≠ k := fun heq_p => hsj_ne (by rw [hp, heq_p])
    -- Rule out `k < p`: if `k + 1 ≤ p`, row `j` of `airyBlockMat s (k + 1)` is zero, leaving a nonzero kernel vector supported on `< k`.
    have hpk_lt : p < k := by
      by_contra hge
      have hp_ge : k + 1 ≤ p := by omega
      let R_sub := {i : Fin k // i ≠ j}
      let B' : Matrix R_sub (Fin k) ℝ := Matrix.of fun i m => airyCardinalR m.1 (s i.1)
      let L' : (Fin k → ℝ) →ₗ[ℝ] (R_sub → ℝ) := B'.mulVecLin
      have hcard_R : Fintype.card R_sub < k := by
        rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
        exact Nat.sub_lt (Nat.pos_of_ne_zero fun hk0 => by subst hk0; exact Fin.elim0 j) zero_lt_one
      have hdim : Module.finrank ℝ (LinearMap.ker L') ≠ 0 := by
        have hrn := LinearMap.finrank_range_add_finrank_ker L'
        have hdom : Module.finrank ℝ (Fin k → ℝ) = k := Module.finrank_fin_fun ℝ
        have hcod : Module.finrank ℝ (R_sub → ℝ) = Fintype.card R_sub := Module.finrank_pi ℝ
        have hran : Module.finrank ℝ (LinearMap.range L') ≤ Fintype.card R_sub :=
          (Submodule.finrank_le (LinearMap.range L')).trans_eq hcod
        omega
      have hne_bot : LinearMap.ker L' ≠ ⊥ := by
        intro hbot; rw [hbot, finrank_bot] at hdim; exact hdim rfl
      obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
      let w' : Fin (k + 1) → ℝ := fun n => if h : n.1 < k then w ⟨n.1, h⟩ else 0
      have hw'_ker : ∀ i : Fin k, airySectionPolyR (k + 1) w' (s i) = 0 := by
        intro i
        by_cases hij : i = j
        · subst hij
          unfold airySectionPolyR
          refine Finset.sum_eq_zero fun n _ => ?_
          have hnp : n.1 ≠ p := by have := n.2; omega
          rw [hp, airyCardinalR_airyZ]
          simp [hnp]
        · unfold airySectionPolyR
          have hsplit : (∑ n : Fin (k + 1), w' n * airyCardinalR n.1 (s i)) =
              ∑ m : Fin k, w m * airyCardinalR m.1 (s i) := by
            have h1 : (∑ n : Fin (k + 1), w' n * airyCardinalR n.1 (s i)) =
                ∑ n ∈ Finset.range (k + 1),
                  (if h : n < k then w ⟨n, h⟩ else 0) * airyCardinalR n (s i) :=
              Fin.sum_univ_eq_sum_range
                (fun n => (if h : n < k then w ⟨n, h⟩ else 0) * airyCardinalR n (s i)) (k + 1)
            rw [h1, Finset.sum_range_succ]
            have hlast : (if h : k < k then w ⟨k, h⟩ else 0) * airyCardinalR k (s i) = 0 := by simp
            rw [hlast, add_zero, ← Fin.sum_univ_eq_sum_range]
            exact Finset.sum_congr rfl fun m _ => by simp [m.2]
          rw [hsplit]
          have hi0 := congrFun (hw_mem : L' w = 0) ⟨i, hij⟩
          simpa only [L', Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, B',
            Matrix.of_apply, Pi.zero_apply, mul_comm] using hi0
      obtain ⟨m₀, hm₀_ne⟩ := Function.ne_iff.mp hw_ne
      have hw'_m0 : w' ⟨m₀.1, m₀.2.trans (Nat.lt_succ_self k)⟩ = 0 :=
        hker_vanish w' hw'_ker ⟨m₀.1, m₀.2.trans (Nat.lt_succ_self k)⟩ m₀.2
      simp [w', m₀.2] at hw'_m0
      exact hm₀_ne hw'_m0
    exact ⟨p, hpk_lt, hp⟩
  choose p hp_lt hp_eq using hall_dir
  have hp_inj : Function.Injective p := by
    intro i j hij
    apply hs
    rw [hp_eq i, hp_eq j, hij]
  have himg_eq : Finset.univ.image p = Finset.range k := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro m hm
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_range.mpr (hp_lt j)
    · rw [Finset.card_image_of_injective _ hp_inj, Finset.card_univ, Fintype.card_fin,
        Finset.card_range]
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨p j, Finset.mem_coe.mpr (Finset.mem_range.mpr (hp_lt j)), (hp_eq j).symm⟩
  · rintro ⟨m, hm, rfl⟩
    have hm_img : m ∈ Finset.univ.image p := himg_eq.symm ▸ Finset.mem_coe.mp hm
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hm_img
    exact ⟨j, hp_eq j⟩

/-! ### Section 5: Part (3) — Full Square Class, Weak Witness `H_λ`, and Bundled Headlines -/

lemma re_sq_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : (z ^ 2).re = z.re ^ 2 := by
  simp [sq, Complex.mul_re, hz]

lemma re_mul_sq_of_im_eq_zero (u : ℝ) {z : ℂ} (hz : z.im = 0) :
    ((u : ℂ) * z ^ 2).re = u * z.re ^ 2 := by
  simp [sq, Complex.mul_re, Complex.mul_im, hz]

/-- Real-valued Dirichlet quadrature for `F ∈ InAiryClass`:
`∑_n Re F(a_{n+1}) / Ai'(a_{n+1})² = ∫_ℝ Re F(u) du`. -/
lemma inAiryClass_quadrature_re {F : ℂ → ℂ} (hF : InAiryClass F) :
    HasSum (fun n : ℕ => (F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2)
      (∫ u : ℝ, (F (u : ℂ)).re) := by
  obtain ⟨C, ν, hC, hb⟩ := hF.2.2.1
  have hsum := airyQ_hasSum_unc hF.1 hF.2.1 hC hb
  have hre := hsum.map Complex.reCLM.toAddMonoidHom Complex.continuous_re
  change HasSum
    (fun n : ℕ => (F (airyZ n : ℂ) / (deriv airyAiC (airyZ n : ℂ)) ^ 2).re)
    (∫ x : ℝ, F (x : ℂ)).re at hre
  have hint_re : (∫ u : ℝ, (F (u : ℂ)).re) = (∫ x : ℝ, F (x : ℂ)).re := integral_re hF.2.1
  rw [← hint_re] at hre
  refine hre.congr_fun fun n => ?_
  rw [deriv_airyAiC_ofReal, ← Complex.ofReal_pow, Complex.div_ofReal_re]

/-- If `f₁, f₂` are entire, real on `ℝ`, and `f₁², f₂² ∈ InAiryClass`, then `f₁ f₂ ∈ InAiryClass`. -/
lemma InAiryClass.mul_of_sq {f₁ f₂ : ℂ → ℂ}
    (hd₁ : Differentiable ℂ f₁) (hd₂ : Differentiable ℂ f₂)
    (hr₁ : ∀ x : ℝ, (f₁ (x : ℂ)).im = 0) (hr₂ : ∀ x : ℝ, (f₂ (x : ℂ)).im = 0)
    (hsq₁ : InAiryClass (fun z => f₁ z ^ 2)) (hsq₂ : InAiryClass (fun z => f₂ z ^ 2)) :
    InAiryClass (fun z => f₁ z * f₂ z) := by
  have hreal : ∀ x : ℝ, (f₁ (x : ℂ) * f₂ (x : ℂ)).im = 0 := by
    intro x
    simp [Complex.mul_im, hr₁ x, hr₂ x]
  refine ⟨hd₁.mul hd₂, ?_, ?_, hreal⟩
  · have hdom : Integrable (fun x : ℝ =>
        ((f₁ (x : ℂ) ^ 2).re + (f₂ (x : ℂ) ^ 2).re) / 2) :=
      (hsq₁.2.1.re.add hsq₂.2.1.re).div_const 2
    have hmeas : AEStronglyMeasurable (fun x : ℝ => f₁ (x : ℂ) * f₂ (x : ℂ)) volume :=
      ((hd₁.mul hd₂).continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
    refine hdom.mono' hmeas (Eventually.of_forall fun x => ?_)
    have hn₁ : ‖f₁ (x : ℂ)‖ = |(f₁ (x : ℂ)).re| := by
      have he₁ : f₁ (x : ℂ) = ((f₁ (x : ℂ)).re : ℂ) := Complex.ext rfl (hr₁ x)
      conv_lhs => rw [he₁]
      rw [Complex.norm_real, Real.norm_eq_abs]
    have hn₂ : ‖f₂ (x : ℂ)‖ = |(f₂ (x : ℂ)).re| := by
      have he₂ : f₂ (x : ℂ) = ((f₂ (x : ℂ)).re : ℂ) := Complex.ext rfl (hr₂ x)
      conv_lhs => rw [he₂]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, hn₁, hn₂, re_sq_of_im_eq_zero (hr₁ x), re_sq_of_im_eq_zero (hr₂ x)]
    nlinarith only [sq_nonneg (|(f₁ (x : ℂ)).re| - |(f₂ (x : ℂ)).re|),
      sq_abs ((f₁ (x : ℂ)).re), sq_abs ((f₂ (x : ℂ)).re)]
  · obtain ⟨C₁, ν₁, hC₁, hb₁⟩ := hsq₁.2.2.1
    obtain ⟨C₂, ν₂, hC₂, hb₂⟩ := hsq₂.2.2.1
    set C := max C₁ C₂
    set ν := max ν₁ ν₂
    have hC : 0 ≤ C := hC₁.trans (le_max_left _ _)
    refine ⟨C, ν, hC, fun z => ?_⟩
    have h1z : 1 ≤ 1 + ‖z‖ := by linarith only [norm_nonneg z]
    have henv_nn : 0 ≤ airyEnv z := (airyEnv_pos z).le
    have hp₁ : (1 + ‖z‖) ^ ν₁ ≤ (1 + ‖z‖) ^ ν :=
      Real.rpow_le_rpow_of_exponent_le h1z (le_max_left _ _)
    have hp₂ : (1 + ‖z‖) ^ ν₂ ≤ (1 + ‖z‖) ^ ν :=
      Real.rpow_le_rpow_of_exponent_le h1z (le_max_right _ _)
    have hu₁ : ‖f₁ z‖ ^ 2 ≤ C * (1 + ‖z‖) ^ ν * airyEnv z := by
      rw [← norm_pow]
      exact (hb₁ z).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul (le_max_left _ _) hp₁ (Real.rpow_nonneg (by positivity) _) hC) henv_nn)
    have hu₂ : ‖f₂ z‖ ^ 2 ≤ C * (1 + ‖z‖) ^ ν * airyEnv z := by
      rw [← norm_pow]
      exact (hb₂ z).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul (le_max_right _ _) hp₂ (Real.rpow_nonneg (by positivity) _) hC) henv_nn)
    refine le_of_sq_le_sq ?_ (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by positivity) _)) henv_nn)
    rw [norm_mul, mul_pow, sq (C * _ * _)]
    exact mul_le_mul hu₁ hu₂ (sq_nonneg _)
      (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by positivity) _)) henv_nn)

/-- Weighted square membership `z ↦ z * q_c(z)² ∈ InAiryClass` for any maximizer `c` at distinct
sites `s`. -/
theorem airyMaximizer_mul_z_sq_inAiryClass {k : ℕ} {s : Fin k → ℝ} (hs : Function.Injective s)
    {c : lp (fun _ : ℕ => ℝ) 2} (hc : AirySquareUnitFeasible s c)
    (hc_max : airySquareRayleigh c = airyLambda s) :
    InAiryClass (fun z => z * airyCardinalSeries c z ^ 2) := by
  have hq2 := airyCardinalSeries_sq_inAiryClass c
  obtain ⟨μ, _, _, _, _, _, hrep⟩ := airySquare_maximizer_representation hs hc hc_max
  set lam := airyLambda s
  set C₀ : ℝ := ∑' n : ℕ, c n
  have hdiff : Differentiable ℂ (fun z => z * airyCardinalSeries c z ^ 2) :=
    differentiable_id.mul ((differentiable_airyCardinalSeries c).pow 2)
  have hreal : ∀ x : ℝ, ((x : ℂ) * airyCardinalSeries c (x : ℂ) ^ 2).im = 0 := by
    intro x
    rw [← ofReal_airyCardinalSeriesR, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im]
  obtain ⟨C_sq, ν_sq, hC_sq, hb_sq⟩ := hq2.2.2.1
  have henv_bound : ∀ z : ℂ, ‖z * airyCardinalSeries c z ^ 2‖ ≤
      C_sq * (1 + ‖z‖) ^ (ν_sq + 1) * airyEnv z := by
    intro z
    have h1z : 0 < 1 + ‖z‖ := by linarith only [norm_nonneg z]
    have hz_le : ‖z‖ ≤ (1 + ‖z‖) ^ (1 : ℝ) := by
      rw [Real.rpow_one]; linarith only [norm_nonneg z]
    have hpow_add : (1 + ‖z‖) ^ (1 : ℝ) * (1 + ‖z‖) ^ ν_sq = (1 + ‖z‖) ^ (ν_sq + 1) := by
      rw [← Real.rpow_add h1z, add_comm (1 : ℝ) ν_sq]
    rw [norm_mul]
    calc ‖z‖ * ‖airyCardinalSeries c z ^ 2‖
        ≤ (1 + ‖z‖) ^ (1 : ℝ) * (C_sq * (1 + ‖z‖) ^ ν_sq * airyEnv z) :=
          mul_le_mul hz_le (hb_sq z) (norm_nonneg _) (Real.rpow_nonneg h1z.le _)
      _ = C_sq * ((1 + ‖z‖) ^ (1 : ℝ) * (1 + ‖z‖) ^ ν_sq) * airyEnv z := by ring
      _ = C_sq * (1 + ‖z‖) ^ (ν_sq + 1) * airyEnv z := by rw [hpow_add]
  refine ⟨hdiff, ?_, ⟨C_sq, ν_sq + 1, hC_sq, henv_bound⟩, hreal⟩
  -- Split `ℝ = Iio (-R₀) ∪ Icc (-R₀) 0 ∪ Ioi 0`.
  set R₀ : ℝ := 2 * max |lam| (∑ j : Fin k, |s j|) + 2
  have hR₀_ge2 : 2 ≤ R₀ := by
    have : 0 ≤ max |lam| (∑ j : Fin k, |s j|) := (abs_nonneg lam).trans (le_max_left _ _)
    dsimp [R₀]; linarith only [this]
  have hcont_f : Continuous (fun x : ℝ => (x : ℂ) * airyCardinalSeries c (x : ℂ) ^ 2) :=
    hdiff.continuous.comp Complex.continuous_ofReal
  -- Positive ray `Ioi 0`: dominated by `integrableOn_airy_exp_Ioi` with `b = 0`.
  have hint_pos : IntegrableOn (fun x : ℝ => (x : ℂ) * airyCardinalSeries c (x : ℂ) ^ 2) (Ioi 0) := by
    have hdom := integrableOn_airy_exp_Ioi (C₂ := C_sq) (ν := ν_sq + 1) (b := 0) hC_sq
    simp only [zero_mul, Real.exp_zero, mul_one] at hdom
    refine hdom.mono' hcont_f.aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 0 < u) => ?_)
    have hb := henv_bound (u : ℂ)
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu] at hb
  -- Compact middle interval `Icc (-R₀) 0`.
  have hint_mid : IntegrableOn (fun x : ℝ => (x : ℂ) * airyCardinalSeries c (x : ℂ) ^ 2)
      (Icc (-R₀) 0) := hcont_f.continuousOn.integrableOn_Icc
  -- Negative ray `Iio (-R₀)`: `O(|u|^{-3/2})` via `(eq:airy-square-rep)`.
  have hint_neg : IntegrableOn (fun x : ℝ => (x : ℂ) * airyCardinalSeries c (x : ℂ) ^ 2)
      (Iio (-R₀)) := by
    set M_rhs : ℝ := 3 * |C₀| +
      ∑ j : Fin k, |μ j| * (2 * (3 * ‖deriv airyAiC (s j : ℂ)‖ + 30))
    have hMrhs_nn : 0 ≤ M_rhs := by
      dsimp [M_rhs]
      exact add_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (by positivity))
    have hdom_pos : IntegrableOn (fun v : ℝ => (2 * M_rhs) ^ 2 * v ^ (-3 / 2 : ℝ)) (Ioi R₀) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1)
        (by linarith only [hR₀_ge2] : 0 < R₀)).const_mul ((2 * M_rhs) ^ 2)
    have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (MeasurableEquiv.neg ℝ).measurableEmbedding
      (f := fun v : ℝ => (2 * M_rhs) ^ 2 * v ^ (-3 / 2 : ℝ)) (s := Ioi R₀)
    have hpre : (fun u : ℝ => -u) ⁻¹' Ioi R₀ = Iio (-R₀) := by ext u; simp
    rw [hpre] at hmp
    have hdom_neg : IntegrableOn (fun u : ℝ => (2 * M_rhs) ^ 2 * (-u) ^ (-3 / 2 : ℝ))
        (Iio (-R₀)) := by
      simpa [Function.comp_def] using hmp.mpr hdom_pos
    refine hdom_neg.mono' hcont_f.aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem measurableSet_Iio fun u (hu : u < -R₀) => ?_)
    have hu_neg : u < 0 := by linarith only [hu, hR₀_ge2]
    have habs_u : |u| = -u := abs_of_neg hu_neg
    have hu_gt2 : 2 < -u := by linarith only [hu, hR₀_ge2]
    have hu_pos : 0 < -u := by linarith only [hu_gt2]
    have hu_ge1 : 1 ≤ -u := by linarith only [hu_gt2]
    -- Vanishing of `Re (u^{3/2})` on `u < 0`.
    have hre32 : (((u : ℂ) ^ (3 / 2 : ℂ)).re) = 0 := by
      have h := airyEnv_ofReal_neg hu_neg
      unfold airyEnv at h
      have := Real.exp_injective (h.trans Real.exp_zero.symm)
      linarith only [this]
    -- `‖Ai(u)‖ ≤ 3 (-u)^{-1/4}` and `‖Ai'(u)‖ ≤ 10 (-u)^{1/4}` for `u < -R₀`.
    have hAi_pow : ‖airyAiC (u : ℂ)‖ ≤ 3 * (-u) ^ (-(1 / 4 : ℝ)) := by
      have henv := airyAiC_envelope (u : ℂ)
      rw [hre32, mul_zero, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs, habs_u] at henv
      have hmono : (1 + -u) ^ (-(1 / 4 : ℝ)) ≤ (-u) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hu_pos (by linarith only) (by norm_num)
      exact henv.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))
    have hAi_three : ‖airyAiC (u : ℂ)‖ ≤ 3 := by
      rw [airyAiC_ofReal, Complex.norm_real, Real.norm_eq_abs]
      exact abs_airyAi_le_three u
    have hAi'_pow : ‖deriv airyAiC (u : ℂ)‖ ≤ 10 * (-u) ^ (1 / 4 : ℝ) := by
      have henv := airyAiC_deriv_envelope (u : ℂ)
      rw [hre32, mul_zero, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs, habs_u] at henv
      have h16 : (1 + -u) ^ (1 / 4 : ℝ) ≤ 2 * (-u) ^ (1 / 4 : ℝ) := by
        have hle16 : 1 + -u ≤ 16 * (-u) := by linarith only [hu_ge1]
        have hrpow := Real.rpow_le_rpow (by positivity) hle16 (by norm_num : (0 : ℝ) ≤ 1 / 4)
        have h16_eq : (16 * (-u)) ^ (1 / 4 : ℝ) = 2 * (-u) ^ (1 / 4 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) hu_pos.le]
          have h2 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
            have : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
            rw [this, ← Real.rpow_mul (by norm_num)]
            norm_num
          rw [h2]
        rwa [h16_eq] at hrpow
      linarith only [henv, h16]
    -- Bound each kernel term `‖airyKerC (u : ℂ) (s j : ℂ)‖`.
    have hker_le : ∀ j : Fin k, ‖airyKerC (u : ℂ) (s j : ℂ)‖ ≤
        (2 * (3 * ‖deriv airyAiC (s j : ℂ)‖ + 30)) * (-u) ^ (-(1 / 4 : ℝ)) := by
      intro j
      have hsj_le : |s j| ≤ max |lam| (∑ i : Fin k, |s i|) :=
        (Finset.single_le_sum (fun i _ => abs_nonneg (s i)) (Finset.mem_univ j)).trans (le_max_right _ _)
      have hsj_lo : -max |lam| (∑ i : Fin k, |s i|) ≤ s j := neg_le_of_abs_le hsj_le
      have hden_ge : (-u) / 2 ≤ s j - u := by
        dsimp [R₀] at hu
        linarith only [hu, hsj_lo]
      have hne_c : (u : ℂ) ≠ (s j : ℂ) := by
        intro heq_c
        have heq_r := Complex.ofReal_injective heq_c
        linarith only [heq_r, hden_ge, hu_pos]
      have hnorm_sub : ‖(u : ℂ) - (s j : ℂ)‖ = s j - u := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
          abs_of_pos (by linarith only [hden_ge, hu_pos])]
      rw [airyKerC_of_ne hne_c, airyKernelXY, norm_div, hnorm_sub]
      have hpow_ge1 : 1 ≤ (-u) ^ (1 / 4 : ℝ) :=
        Real.one_le_rpow hu_ge1 (by norm_num)
      have hAi_sj : ‖airyAiC (s j : ℂ)‖ ≤ 3 := by
        rw [airyAiC_ofReal, Complex.norm_real, Real.norm_eq_abs]
        exact abs_airyAi_le_three (s j)
      have hnum_le : ‖airyAiC (u : ℂ) * deriv airyAiC (s j : ℂ) -
          deriv airyAiC (u : ℂ) * airyAiC (s j : ℂ)‖ ≤
          (3 * ‖deriv airyAiC (s j : ℂ)‖ + 30) * (-u) ^ (1 / 4 : ℝ) := by
        calc ‖airyAiC (u : ℂ) * deriv airyAiC (s j : ℂ) -
                deriv airyAiC (u : ℂ) * airyAiC (s j : ℂ)‖
            ≤ ‖airyAiC (u : ℂ)‖ * ‖deriv airyAiC (s j : ℂ)‖ +
                ‖deriv airyAiC (u : ℂ)‖ * ‖airyAiC (s j : ℂ)‖ := by
              refine (norm_sub_le _ _).trans ?_
              rw [norm_mul, norm_mul]
          _ ≤ 3 * ‖deriv airyAiC (s j : ℂ)‖ * 1 + (10 * (-u) ^ (1 / 4 : ℝ)) * 3 := by
              rw [mul_one]
              exact add_le_add (mul_le_mul_of_nonneg_right hAi_three (norm_nonneg _))
                (mul_le_mul hAi'_pow hAi_sj (norm_nonneg _) (by positivity))
          _ ≤ 3 * ‖deriv airyAiC (s j : ℂ)‖ * (-u) ^ (1 / 4 : ℝ) +
                30 * (-u) ^ (1 / 4 : ℝ) := by
              have h1 := mul_le_mul_of_nonneg_left hpow_ge1
                (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (norm_nonneg (deriv airyAiC (s j : ℂ))))
              linarith only [h1]
          _ = (3 * ‖deriv airyAiC (s j : ℂ)‖ + 30) * (-u) ^ (1 / 4 : ℝ) := by ring
      have hexp_34 : (-u) ^ (1 / 4 : ℝ) / (-u) ≤ (-u) ^ (-(1 / 4 : ℝ)) := by
        have h34 : (-u) ^ (1 / 4 : ℝ) / (-u) = (-u) ^ (-(3 / 4 : ℝ)) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hu_pos]
          norm_num
        rw [h34]
        exact Real.rpow_le_rpow_of_exponent_le hu_ge1 (by norm_num)
      calc ‖airyAiC (u : ℂ) * deriv airyAiC (s j : ℂ) -
              deriv airyAiC (u : ℂ) * airyAiC (s j : ℂ)‖ / (s j - u)
          ≤ ((3 * ‖deriv airyAiC (s j : ℂ)‖ + 30) * (-u) ^ (1 / 4 : ℝ)) / ((-u) / 2) :=
            div_le_div₀ (by positivity) hnum_le (by positivity) hden_ge
        _ = (2 * (3 * ‖deriv airyAiC (s j : ℂ)‖ + 30)) * ((-u) ^ (1 / 4 : ℝ) / (-u)) := by ring
        _ ≤ (2 * (3 * ‖deriv airyAiC (s j : ℂ)‖ + 30)) * (-u) ^ (-(1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hexp_34 (by positivity)
    -- Combine via `hrep (u : ℂ)` to get `‖q (u : ℂ)‖ ≤ 2 * M_rhs * (-u)^{-5/4}`.
    have hrhs_bound : ‖((u : ℂ) - (lam : ℂ)) * airyCardinalSeries c (u : ℂ)‖ ≤
        M_rhs * (-u) ^ (-(1 / 4 : ℝ)) := by
      rw [hrep (u : ℂ)]
      calc ‖(C₀ : ℂ) * airyAiC (u : ℂ) + ∑ j : Fin k, (μ j : ℂ) * airyKerC (u : ℂ) (s j : ℂ)‖
          ≤ ‖(C₀ : ℂ) * airyAiC (u : ℂ)‖ +
              ∑ j : Fin k, ‖(μ j : ℂ) * airyKerC (u : ℂ) (s j : ℂ)‖ :=
            (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
        _ ≤ |C₀| * (3 * (-u) ^ (-(1 / 4 : ℝ))) +
              ∑ j : Fin k, |μ j| *
                ((2 * (3 * ‖deriv airyAiC (s j : ℂ)‖ + 30)) * (-u) ^ (-(1 / 4 : ℝ))) := by
            refine add_le_add ?_ (Finset.sum_le_sum fun j _ => ?_)
            · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_left hAi_pow (abs_nonneg _)
            · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_left (hker_le j) (abs_nonneg _)
        _ = M_rhs * (-u) ^ (-(1 / 4 : ℝ)) := by
            dsimp [M_rhs]
            rw [add_mul, Finset.sum_mul]
            congr 1
            · ring
            · exact Finset.sum_congr rfl fun j _ => by ring
    have hlam_gap : (-u) / 2 ≤ ‖(u : ℂ) - (lam : ℂ)‖ := by
      have hlam_lo : -max |lam| (∑ i : Fin k, |s i|) ≤ lam :=
        neg_le_of_abs_le (le_max_left _ _)
      have hsub_pos : (-u) / 2 ≤ lam - u := by
        dsimp [R₀] at hu
        linarith only [hu, hlam_lo]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
        abs_of_pos (by linarith only [hsub_pos, hu_pos])]
      exact hsub_pos
    have hq_le : ‖airyCardinalSeries c (u : ℂ)‖ ≤ 2 * M_rhs * (-u) ^ (-(5 / 4 : ℝ)) := by
      rw [norm_mul] at hrhs_bound
      have hstep : ‖airyCardinalSeries c (u : ℂ)‖ ≤
          (M_rhs * (-u) ^ (-(1 / 4 : ℝ))) / ((-u) / 2) := by
        rw [le_div_iff₀ (by positivity)]
        calc ‖airyCardinalSeries c (u : ℂ)‖ * ((-u) / 2)
            ≤ ‖airyCardinalSeries c (u : ℂ)‖ * ‖(u : ℂ) - (lam : ℂ)‖ :=
              mul_le_mul_of_nonneg_left hlam_gap (norm_nonneg _)
          _ = ‖(u : ℂ) - (lam : ℂ)‖ * ‖airyCardinalSeries c (u : ℂ)‖ := mul_comm _ _
          _ ≤ M_rhs * (-u) ^ (-(1 / 4 : ℝ)) := hrhs_bound
      refine hstep.trans (le_of_eq ?_)
      have hpow_54 : (-u) ^ (-(1 / 4 : ℝ)) / (-u) = (-u) ^ (-(5 / 4 : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hu_pos]
        norm_num
      calc (M_rhs * (-u) ^ (-(1 / 4 : ℝ))) / ((-u) / 2)
          = 2 * M_rhs * ((-u) ^ (-(1 / 4 : ℝ)) / (-u)) := by ring
        _ = 2 * M_rhs * (-u) ^ (-(5 / 4 : ℝ)) := by rw [hpow_54]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, habs_u]
    calc (-u) * ‖airyCardinalSeries c (u : ℂ)‖ ^ 2
        ≤ (-u) * (2 * M_rhs * (-u) ^ (-(5 / 4 : ℝ))) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq_le 2) hu_pos.le
      _ = (2 * M_rhs) ^ 2 * ((-u) ^ (1 : ℝ) * ((-u) ^ (-(5 / 4 : ℝ)) * (-u) ^ (-(5 / 4 : ℝ)))) := by
          rw [Real.rpow_one]; ring
      _ = (2 * M_rhs) ^ 2 * (-u) ^ (-3 / 2 : ℝ) := by
          rw [← Real.rpow_add hu_pos, ← Real.rpow_add hu_pos]
          norm_num
  have hint_left : IntegrableOn (fun x : ℝ => (x : ℂ) * airyCardinalSeries c (x : ℂ) ^ 2) (Iic 0) := by
    rw [← Set.Iio_union_Icc_eq_Iic (by linarith only [hR₀_ge2] : -R₀ ≤ 0)]
    exact hint_neg.union hint_mid
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact hint_left.union hint_pos

/-- Weak witness profile `H_λ(z) = (z - λ(s)) q_c(z)²` associated to a sequence `c ∈ ℓ²`. -/
noncomputable def airyMaximizerWitness {k : ℕ} (s : Fin k → ℝ)
    (c : lp (fun _ : ℕ => ℝ) 2) (z : ℂ) : ℂ :=
  (z - (airyLambda s : ℂ)) * airyCardinalSeries c z ^ 2

lemma airyMaximizerWitness_re {k : ℕ} (s : Fin k → ℝ) (c : lp (fun _ : ℕ => ℝ) 2) (u : ℝ) :
    (airyMaximizerWitness s c (u : ℂ)).re =
      (u - airyLambda s) * airyCardinalSeriesR c u ^ 2 := by
  unfold airyMaximizerWitness
  rw [← ofReal_airyCardinalSeriesR, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Part (3) witness properties (`thm:airy-square-attained`(3)):** for a unit maximizer `c` at
distinct sites `s`, `H_λ = (z - λ(s)) q_c²` belongs to `𝒢`, vanishes at every `s_j`, satisfies
`∫ H_λ = 0` and `L_{H_λ}(y) > 0` for all `y > 0`, is a weak witness at `λ(s)`, and hence
`λ(s) ≤ u_LP(s)`. -/
theorem airyMaximizerWitness_properties {k : ℕ} {s : Fin k → ℝ} (hs : Function.Injective s)
    {c : lp (fun _ : ℕ => ℝ) 2} (hc : AirySquareUnitFeasible s c)
    (hc_max : airySquareRayleigh c = airyLambda s) :
    InAiryClass (airyMaximizerWitness s c) ∧
    (∀ j : Fin k, airyMaximizerWitness s c (s j : ℂ) = 0) ∧
    (∫ u : ℝ, (airyMaximizerWitness s c (u : ℂ)).re) = 0 ∧
    (∀ y : ℝ, 0 < y → 0 < airyLaplace (fun u => (airyMaximizerWitness s c (u : ℂ)).re) y) ∧
    IsAiryWeakWitness (Set.range s) (airyLambda s) (airyMaximizerWitness s c) ∧
    (airyLambda s : EReal) ≤ airyULP (Set.range s) := by
  set lam := airyLambda s
  have hq2 := airyCardinalSeries_sq_inAiryClass c
  have hzq2 := airyMaximizer_mul_z_sq_inAiryClass hs hc hc_max
  have hH_class : InAiryClass (airyMaximizerWitness s c) := by
    have heq : airyMaximizerWitness s c =
        fun z => z * airyCardinalSeries c z ^ 2 - (lam : ℂ) * airyCardinalSeries c z ^ 2 := by
      ext z; unfold airyMaximizerWitness; ring
    rw [heq]
    exact hzq2.sub (hq2.smul lam)
  have hH_sites : ∀ j : Fin k, airyMaximizerWitness s c (s j : ℂ) = 0 := by
    intro j
    unfold airyMaximizerWitness
    rw [← ofReal_airyCardinalSeriesR, hc.2.2 j, Complex.ofReal_zero, sq, zero_mul, mul_zero]
  have hq_int1 : (∫ u : ℝ, airyCardinalSeriesR c u ^ 2) = 1 := by
    rw [integral_sq_airyCardinalSeriesR, (hasSum_sq_one_iff_norm_eq_one c).mp hc.1, one_pow]
  have hH_int0 : (∫ u : ℝ, (airyMaximizerWitness s c (u : ℂ)).re) = 0 := by
    have hquad := inAiryClass_quadrature_re hH_class
    have hs1 : HasSum (fun n : ℕ => airyZ n * (c n) ^ 2) lam := by
      rw [← hc_max]; exact ((summable_airyZ_mul_sq_iff c).mp hc.2.1).hasSum
    have hs2 : HasSum (fun n : ℕ => lam * (c n) ^ 2) lam := by
      simpa only [mul_one] using hc.1.mul_left lam
    have hs_zero : HasSum (fun n : ℕ => (airyZ n - lam) * (c n) ^ 2) 0 := by
      have h := hs1.sub hs2
      rw [sub_self] at h
      exact h.congr_fun fun n => by ring
    have hcongr : (fun n : ℕ => (airyMaximizerWitness s c (airyZ n : ℂ)).re /
        airyAi' (airyZ n) ^ 2) = fun n : ℕ => (airyZ n - lam) * (c n) ^ 2 := by
      ext n
      rw [airyMaximizerWitness_re, airyCardinalSeriesR_airyZ]
      have hne : airyAi' (airyZ n) ≠ 0 := airyAi'_airyZ_ne_zero n
      dsimp [lam]
      field_simp
    rw [hcongr] at hquad
    exact hquad.unique hs_zero
  -- Strict positivity of `airyLaplace H_λ y` for `y > 0`.
  have hH_lap_pos : ∀ y : ℝ, 0 < y →
      0 < airyLaplace (fun u => (airyMaximizerWitness s c (u : ℂ)).re) y := by
    intro y hy
    unfold airyLaplace
    refine mul_pos (Real.exp_pos _) ?_
    have hint_exp : Integrable (fun u : ℝ =>
        (airyMaximizerWitness s c (u : ℂ)).re * Real.exp (y * u)) :=
      hH_class.to_polyLeftAiryRightBound.integrable_exp hy
    have hint_base : Integrable (fun u : ℝ => (airyMaximizerWitness s c (u : ℂ)).re) :=
      hH_class.2.1.re
    let g : ℝ → ℝ := fun u =>
      (u - lam) * (Real.exp (y * u) - Real.exp (y * lam)) * airyCardinalSeriesR c u ^ 2
    have hg_eq : g = fun u : ℝ => (airyMaximizerWitness s c (u : ℂ)).re * Real.exp (y * u) -
        Real.exp (y * lam) * (airyMaximizerWitness s c (u : ℂ)).re := by
      ext u
      dsimp [g]
      rw [airyMaximizerWitness_re]
      ring
    have hg_int : Integrable g := by
      rw [hg_eq]
      exact hint_exp.sub (hint_base.const_mul _)
    have hg_integral_eq : (∫ u : ℝ, g u) =
        ∫ u : ℝ, (airyMaximizerWitness s c (u : ℂ)).re * Real.exp (y * u) := by
      rw [hg_eq, integral_sub hint_exp (hint_base.const_mul _), integral_const_mul,
        hH_int0, mul_zero, sub_zero]
    rw [← hg_integral_eq]
    have hg_nn : ∀ u : ℝ, 0 ≤ g u := by
      intro u
      dsimp [g]
      refine mul_nonneg ?_ (sq_nonneg _)
      rcases le_or_gt u lam with hle | hgt
      · have hexp_le : Real.exp (y * u) ≤ Real.exp (y * lam) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle hy.le)
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith only [hle]) (by linarith only [hexp_le])
      · have hexp_gt : Real.exp (y * lam) < Real.exp (y * u) :=
          Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hgt hy)
        exact mul_nonneg (by linarith only [hgt]) (by linarith only [hexp_gt])
    have hg_int_nn : 0 ≤ ∫ u : ℝ, g u := integral_nonneg hg_nn
    by_contra hnot_pos
    have hg_int0 : (∫ u : ℝ, g u) = 0 := le_antisymm (not_lt.mp hnot_pos) hg_int_nn
    have hae : g =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg hg_nn hg_int).mp hg_int0
    have hg_cont : Continuous g := by
      dsimp [g]
      exact ((continuous_id.sub continuous_const).mul
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
          continuous_const)).mul ((continuous_airyCardinalSeriesR c).pow 2)
    have hg_zero : ∀ u : ℝ, g u = 0 := fun u =>
      congrFun ((Continuous.ae_eq_iff_eq volume hg_cont continuous_const).mp hae) u
    have hq_zero_int : ∀ x : ℝ, lam + 1 < x → x < lam + 2 →
        airyCardinalSeries c (x : ℂ) = 0 := by
      intro x hx1 _
      have hx_gt : lam < x := by linarith only [hx1]
      have hg0 := hg_zero x
      dsimp [g] at hg0
      have hfac1 : x - lam ≠ 0 := (sub_pos.mpr hx_gt).ne'
      have hfac2 : Real.exp (y * x) - Real.exp (y * lam) ≠ 0 :=
        (sub_pos.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hx_gt hy))).ne'
      have hsq0 : airyCardinalSeriesR c x ^ 2 = 0 :=
        (mul_eq_zero.mp hg0).resolve_left (mul_ne_zero hfac1 hfac2)
      rw [← ofReal_airyCardinalSeriesR, sq_eq_zero_iff.mp hsq0, Complex.ofReal_zero]
    have hq_all0 := airy_entire_eq_zero_of_real_interval (differentiable_airyCardinalSeries c)
      (by linarith only : lam + 1 < lam + 2) hq_zero_int
    have hint_zero : (∫ u : ℝ, airyCardinalSeriesR c u ^ 2) = 0 := by
      have h0 : ∀ u : ℝ, airyCardinalSeriesR c u ^ 2 = 0 := fun u => by
        unfold airyCardinalSeriesR
        rw [hq_all0 (u : ℂ), Complex.zero_re, sq, zero_mul]
      simp [h0]
    linarith only [hq_int1, hint_zero]
  -- Non-vanishing of `H_λ`.
  have hH_nz : ∃ z : ℂ, airyMaximizerWitness s c z ≠ 0 := by
    by_contra hall0
    push Not at hall0
    have hre0 : ∀ u : ℝ, (airyMaximizerWitness s c (u : ℂ)).re = 0 :=
      fun u => by rw [hall0 (u : ℂ), Complex.zero_re]
    have hlap1 := hH_lap_pos 1 zero_lt_one
    unfold airyLaplace at hlap1
    simp [hre0] at hlap1
  have hwit : IsAiryWeakWitness (Set.range s) lam (airyMaximizerWitness s c) := by
    refine ⟨hH_class, hH_nz, ?_, ?_, ?_⟩
    · rintro _ ⟨j, rfl⟩
      rw [hH_sites j, Complex.zero_re]
    · intro u hu
      rw [airyMaximizerWitness_re]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) (sq_nonneg _)
    · intro y hy
      rcases hy.eq_or_lt with rfl | hpos
      · unfold airyLaplace
        simp [hH_int0]
      · exact (hH_lap_pos y hpos).le
  have hle_ulp : (lam : EReal) ≤ airyULP (Set.range s) :=
    le_iSup₂_of_le lam ⟨airyMaximizerWitness s c, hwit⟩ le_rfl
  exact ⟨hH_class, hH_sites, hH_int0, hH_lap_pos, hwit, hle_ulp⟩

/-- From the deferred finite-section inequality `AirySquareBoundInput s` (`lem:airy-square-bound`),
`λ(s) ≤ u_sh(s) ≤ u_LP(s)`. -/
theorem airyLambda_le_airyUSh_of_bound {k : ℕ} (s : Fin k → ℝ) (h : AirySquareBoundInput s) :
    (airyLambda s : EReal) ≤ airyUSh (Set.range s) := by
  have : Nonempty {M : ℕ // k + 1 ≤ M} := ⟨⟨k + 1, le_rfl⟩⟩
  generalize hu : airyUSh (Set.range s) = u
  induction u using EReal.rec with
  | bot =>
    have h1 := h.section_le_uSh (k + 1) le_rfl
    rw [hu] at h1
    exact False.elim (not_le_of_gt (EReal.bot_lt_coe _) h1)
  | coe r =>
    rw [EReal.coe_le_coe_iff]
    refine ciSup_le fun M => ?_
    have hM := h.section_le_uSh M.1 M.2
    rw [hu, EReal.coe_le_coe_iff] at hM
    exact hM
  | top => exact le_top

/-- Every unit maximizer `c` at distinct sites `s` produces a member `q_c` of the full square class
`IsAirySquareClass s` with quotient equal to `airyLambda s`. -/
lemma airyCardinalSeries_mem_squareClass_of_maximizer {k : ℕ} {s : Fin k → ℝ}
    (hs : Function.Injective s) {c : lp (fun _ : ℕ => ℝ) 2}
    (hc : AirySquareUnitFeasible s c) (hc_max : airySquareRayleigh c = airyLambda s) :
    IsAirySquareClass s (airyCardinalSeries c) ∧
    airySquareClassQuotient (airyCardinalSeries c) = airyLambda s := by
  have hq2 := airyCardinalSeries_sq_inAiryClass c
  have hzq2 := airyMaximizer_mul_z_sq_inAiryClass hs hc hc_max
  have hq_int1 : (∫ u : ℝ, (airyCardinalSeries c (u : ℂ)).re ^ 2) = 1 := by
    change (∫ u : ℝ, airyCardinalSeriesR c u ^ 2) = 1
    rw [integral_sq_airyCardinalSeriesR, (hasSum_sq_one_iff_norm_eq_one c).mp hc.1, one_pow]
  have hq_nz : ∃ z : ℂ, airyCardinalSeries c z ≠ 0 := by
    by_contra hall0
    push Not at hall0
    simp [hall0] at hq_int1
  have hmem : IsAirySquareClass s (airyCardinalSeries c) := by
    refine ⟨differentiable_airyCardinalSeries c, airyCardinalSeries_ofReal_im c,
      hq_nz, hq2, hzq2, fun j => ?_⟩
    rw [← ofReal_airyCardinalSeriesR, hc.2.2 j, Complex.ofReal_zero]
  obtain ⟨_, _, hH_int0, _, _, _⟩ := airyMaximizerWitness_properties hs hc hc_max
  have hnum_eq : (∫ u : ℝ, u * (airyCardinalSeries c (u : ℂ)).re ^ 2) = airyLambda s := by
    have h1 : Integrable (fun u : ℝ => u * (airyCardinalSeries c (u : ℂ)).re ^ 2) := by
      refine hzq2.2.1.re.congr (Eventually.of_forall fun u => ?_)
      dsimp only
      rw [← ofReal_airyCardinalSeriesR, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
        Complex.ofReal_re]
      rfl
    have h2 : Integrable (fun u : ℝ =>
        airyLambda s * (airyCardinalSeries c (u : ℂ)).re ^ 2) := by
      exact (integrable_sq_airyCardinalSeriesR c).const_mul (airyLambda s)
    have hsub : (∫ u : ℝ, u * (airyCardinalSeries c (u : ℂ)).re ^ 2) -
        airyLambda s * (∫ u : ℝ, (airyCardinalSeries c (u : ℂ)).re ^ 2) =
        ∫ u : ℝ, (airyMaximizerWitness s c (u : ℂ)).re := by
      rw [← integral_const_mul, ← integral_sub h1 h2]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      dsimp only
      rw [airyMaximizerWitness_re]
      unfold airyCardinalSeriesR
      ring
    rw [hq_int1, mul_one, hH_int0] at hsub
    linarith only [hsub]
  exact ⟨hmem, by unfold airySquareClassQuotient; rw [hnum_eq, hq_int1, div_one]⟩

/-- **Part (3) full square class optimality (`thm:airy-square-attained`(3)):** the maximum of
`(∫ u q(u)² du) / (∫ q(u)² du)` over all `q` satisfying `IsAirySquareClass s q` equals `λ(s)`,
and is attained by the maximizing cardinal series `q_c`. -/
theorem isGreatest_airySquareClass {k : ℕ} {s : Fin k → ℝ} (hs : Function.Injective s) :
    IsGreatest (airySquareClassQuotient '' {q : ℂ → ℂ | IsAirySquareClass s q})
      (airyLambda s) := by
  obtain ⟨⟨c, hc_feas, hc_max⟩, _⟩ := isGreatest_airySquareRayleigh hs
  obtain ⟨hqc_mem, hqc_val⟩ := airyCardinalSeries_mem_squareClass_of_maximizer hs hc_feas hc_max
  refine ⟨⟨airyCardinalSeries c, hqc_mem, hqc_val⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨hq_diff, hq_real, hq_nz, hq2, hzq2, hq_sites⟩ := hq
  -- `∫ q² > 0` by non-vanishing and the identity theorem.
  have hq2_int : Integrable (fun u : ℝ => (q (u : ℂ)).re ^ 2) := by
    refine hq2.2.1.re.congr (Eventually.of_forall fun u => ?_)
    exact re_sq_of_im_eq_zero (hq_real u)
  have hq2_pos : 0 < ∫ u : ℝ, (q (u : ℂ)).re ^ 2 := by
    have hnn : 0 ≤ ∫ u : ℝ, (q (u : ℂ)).re ^ 2 := integral_nonneg fun u => sq_nonneg _
    by_contra hnot
    have hint0 : (∫ u : ℝ, (q (u : ℂ)).re ^ 2) = 0 := le_antisymm (not_lt.mp hnot) hnn
    have hae := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg _) hq2_int).mp hint0
    have hcont : Continuous (fun u : ℝ => (q (u : ℂ)).re ^ 2) :=
      (Complex.continuous_re.comp (hq_diff.continuous.comp Complex.continuous_ofReal)).pow 2
    have hre0 : ∀ u : ℝ, (q (u : ℂ)).re = 0 := fun u =>
      sq_eq_zero_iff.mp (congrFun ((Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hae) u)
    have hall0 := airy_entire_eq_zero_of_real_interval hq_diff (by norm_num : (0 : ℝ) < 1)
      fun x _ _ => Complex.ext (hre0 x) (hq_real x)
    obtain ⟨z₀, hz₀⟩ := hq_nz
    exact hz₀ (hall0 z₀)
  -- Quadrature on `q²` puts `d_n = q(a_n) / Ai'(a_n)` into `ℓ²`.
  let d_raw : ℕ → ℝ := fun n => (q (airyZ n : ℂ)).re / airyAi' (airyZ n)
  have hd_hasSum : HasSum (fun n : ℕ => (d_raw n) ^ 2) (∫ u : ℝ, (q (u : ℂ)).re ^ 2) := by
    have hquad := inAiryClass_quadrature_re hq2
    have hrhs_eq : (∫ u : ℝ, (q (u : ℂ) ^ 2).re) = ∫ u : ℝ, (q (u : ℂ)).re ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun u => re_sq_of_im_eq_zero (hq_real u))
    rw [hrhs_eq] at hquad
    refine hquad.congr_fun fun n => ?_
    dsimp [d_raw]
    rw [re_sq_of_im_eq_zero (hq_real (airyZ n)), div_pow]
  have hd_mem : Memℓp d_raw 2 := by
    refine memℓp_gen ?_
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hd_hasSum.summable
  let d : lp (fun _ : ℕ => ℝ) 2 := ⟨d_raw, hd_mem⟩
  have hd_apply : ∀ n : ℕ, d n = d_raw n := fun _ => rfl
  -- Identify `q = airyCardinalSeries d` directly by applying quadrature to `(q - q_d)² ∈ 𝒢`!
  have hqd_mul : InAiryClass (fun z => q z * airyCardinalSeries d z) :=
    InAiryClass.mul_of_sq hq_diff (differentiable_airyCardinalSeries d)
      hq_real (airyCardinalSeries_ofReal_im d) hq2 (airyCardinalSeries_sq_inAiryClass d)
  have hdiff_sq_class : InAiryClass (fun z => (q z - airyCardinalSeries d z) ^ 2) := by
    have heq2 : (fun z => (q z - airyCardinalSeries d z) ^ 2) =
        fun z => (q z ^ 2 - ((2 : ℝ) : ℂ) * (q z * airyCardinalSeries d z)) +
          airyCardinalSeries d z ^ 2 := by
      ext z; push_cast; ring
    rw [heq2]
    exact (hq2.sub (hqd_mul.smul 2)).add (airyCardinalSeries_sq_inAiryClass d)
  have hdiff_nodes : ∀ n : ℕ, ((q (airyZ n : ℂ) - airyCardinalSeries d (airyZ n : ℂ)) ^ 2).re = 0 := by
    intro n
    rw [airyCardinalSeries_airyZ, hd_apply]
    dsimp [d_raw]
    have hmul_cancel : (q (airyZ n : ℂ)).re / airyAi' (airyZ n) * airyAi' (airyZ n) =
        (q (airyZ n : ℂ)).re := div_mul_cancel₀ _ (airyAi'_airyZ_ne_zero n)
    have hq_n : q (airyZ n : ℂ) = ((q (airyZ n : ℂ)).re : ℂ) := Complex.ext rfl (hq_real (airyZ n))
    rw [hmul_cancel, ← hq_n, sub_self, sq, zero_mul, Complex.zero_re]
  have hdiff_int0 : (∫ u : ℝ, ((q (u : ℂ) - airyCardinalSeries d (u : ℂ)) ^ 2).re) = 0 := by
    have hquad := inAiryClass_quadrature_re hdiff_sq_class
    have h0 : (fun n : ℕ => ((q (airyZ n : ℂ) - airyCardinalSeries d (airyZ n : ℂ)) ^ 2).re /
        airyAi' (airyZ n) ^ 2) = fun _ => 0 := by
      ext n; rw [hdiff_nodes n, zero_div]
    rw [h0] at hquad
    exact hquad.unique hasSum_zero
  have hq_eq_qd : ∀ z : ℂ, q z = airyCardinalSeries d z := by
    have hre_sq : ∀ u : ℝ, ((q (u : ℂ) - airyCardinalSeries d (u : ℂ)) ^ 2).re =
        ((q (u : ℂ)).re - airyCardinalSeriesR d u) ^ 2 := by
      intro u
      have him_sub : (q (u : ℂ) - airyCardinalSeries d (u : ℂ)).im = 0 := by
        simp [hq_real u, airyCardinalSeries_ofReal_im d u]
      rw [re_sq_of_im_eq_zero him_sub, Complex.sub_re, airyCardinalSeriesR]
    simp_rw [hre_sq] at hdiff_int0
    have hint_diff : Integrable (fun u : ℝ => ((q (u : ℂ)).re - airyCardinalSeriesR d u) ^ 2) :=
      hdiff_sq_class.2.1.re.congr (Eventually.of_forall fun u => hre_sq u)
    have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint_diff).mp hdiff_int0
    have hcont : Continuous (fun u : ℝ => ((q (u : ℂ)).re - airyCardinalSeriesR d u) ^ 2) :=
      ((Complex.continuous_re.comp (hq_diff.continuous.comp Complex.continuous_ofReal)).sub
        (continuous_airyCardinalSeriesR d)).pow 2
    have hreal_eq : ∀ u : ℝ, q (u : ℂ) = airyCardinalSeries d (u : ℂ) := by
      intro u
      have hsq0 : ((q (u : ℂ)).re - airyCardinalSeriesR d u) ^ 2 = 0 :=
        congrFun ((Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hae) u
      have hre_eq : (q (u : ℂ)).re = airyCardinalSeriesR d u :=
        sub_eq_zero.mp (sq_eq_zero_iff.mp hsq0)
      exact Complex.ext hre_eq ((hq_real u).trans (airyCardinalSeries_ofReal_im d u).symm)
    have hsub0 := airy_entire_eq_zero_of_real_interval
      (hq_diff.sub (differentiable_airyCardinalSeries d)) (by norm_num : (0 : ℝ) < 1)
      fun x _ _ => sub_eq_zero.mpr (hreal_eq x)
    exact fun z => sub_eq_zero.mp (hsub0 z)
  -- Quadrature on `z * q(z)² ∈ 𝒢` gives `HasSum (fun n => airyZ n * (d n)²) (∫ u * q(u)²)`.
  have hnum_hasSum : HasSum (fun n : ℕ => airyZ n * (d n) ^ 2)
      (∫ u : ℝ, u * (q (u : ℂ)).re ^ 2) := by
    have hquad := inAiryClass_quadrature_re hzq2
    have hrhs_eq : (∫ u : ℝ, ((u : ℂ) * q (u : ℂ) ^ 2).re) =
        ∫ u : ℝ, u * (q (u : ℂ)).re ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun u => re_mul_sq_of_im_eq_zero u (hq_real u))
    rw [hrhs_eq] at hquad
    refine hquad.congr_fun fun n => ?_
    rw [hd_apply]
    dsimp [d_raw]
    rw [re_mul_sq_of_im_eq_zero (airyZ n) (hq_real (airyZ n)), div_pow, mul_div_assoc]
  have hd_abs_sum : Summable (fun n : ℕ => |airyZ n| * (d n) ^ 2) :=
    (summable_airyZ_mul_sq_iff d).mpr hnum_hasSum.summable
  have hd_ker : ∀ j : Fin k, airyCardinalSeriesR d (s j) = 0 := by
    intro j
    unfold airyCardinalSeriesR
    rw [← hq_eq_qd (s j : ℂ), hq_sites j, Complex.zero_re]
  have hd_norm_sq : ‖d‖ ^ 2 = ∫ u : ℝ, (q (u : ℂ)).re ^ 2 := by
    have h1 := lp.hasSum_norm (p := 2) (by norm_num) d
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h1
    exact h1.unique hd_hasSum
  have hd_norm_pos : 0 < ‖d‖ := by
    have hsq_pos : 0 < ‖d‖ ^ 2 := hd_norm_sq.symm ▸ hq2_pos
    nlinarith only [hsq_pos, norm_nonneg d]
  let d_unit : lp (fun _ : ℕ => ℝ) 2 := (‖d‖⁻¹ : ℝ) • d
  have hd_unit_feas : AirySquareUnitFeasible s d_unit := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hasSum_sq_one_iff_norm_eq_one]
      change ‖(‖d‖⁻¹ : ℝ) • d‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd_norm_pos),
        inv_mul_cancel₀ hd_norm_pos.ne']
    · refine (hd_abs_sum.mul_left ((‖d‖⁻¹) ^ 2)).congr fun n => ?_
      simp [d_unit, Pi.smul_apply, smul_eq_mul]; ring
    · rw [← airyEvalMap_eq_zero_iff]
      change airyEvalMap s ((‖d‖⁻¹ : ℝ) • d) = 0
      rw [map_smul, (airyEvalMap_eq_zero_iff s d).mpr hd_ker, smul_zero]
  have hd_unit_le : airySquareRayleigh d_unit ≤ airyLambda s :=
    (isGreatest_airySquareRayleigh hs).2 ⟨d_unit, hd_unit_feas, rfl⟩
  have hquot_eq : airySquareClassQuotient q = airySquareRayleigh d_unit := by
    unfold airySquareClassQuotient airySquareRayleigh
    rw [← hnum_hasSum.tsum_eq, ← hd_norm_sq]
    have hcongr : (fun n : ℕ => airyZ n * (d_unit n) ^ 2) =
        fun n : ℕ => (‖d‖⁻¹) ^ 2 * (airyZ n * (d n) ^ 2) := by
      ext n; simp [d_unit, Pi.smul_apply, smul_eq_mul]; ring
    rw [hcongr, tsum_mul_left, inv_pow, inv_mul_eq_div]
  rwa [hquot_eq]

/-- **Theorem `thm:airy-square-attained` (distinct sites, unconditional parts (1)–(3);
`ce_airy_lp.tex`).**
Bundles all unconditional assertions of Theorem `thm:airy-square-attained` for distinct real sites
`s : Fin k → ℝ`:
* **(1)** `Λ_M(s) → λ(s)` (`tendsto_airyLambdaSection`), attainment on `AirySquareUnitFeasible s`
  (`isGreatest_airySquareRayleigh`), local Lipschitz continuity on `{s | Function.Injective s}`
  (`locallyLipschitzOn_airyLambda`), uniform `O(M⁻¹)` rate on compacts
  (`airyLambda_sub_section_le_on_compact`), `λ(s) ≥ Λ_{k+1}(s) ≥ a_{k+1}`, and both exactness
  criteria (`airyLambdaSection_first_eq_iff`, `airyLambdaSection_eq_airyLambda_iff`);
* **(2)** Lagrange multipliers `μ`, `O(|a_n|^{-2})` decay, `∑_n |c_n| < ∞`, and entire
  representation `(eq:airy-square-rep)` (`airySquare_maximizer_representation`);
* **(3)** optimality over the full square class `IsAirySquareClass s`
  (`isGreatest_airySquareClass`), weak witness `H_λ = (z - λ(s)) q_c² ∈ 𝒢` with `H_λ(s_j) = 0`,
  `∫ H_λ = 0`, `L_{H_λ}(y) > 0` (`y > 0`), `λ(s) ≤ u_LP(s)`, and `u_sh(s) ≤ u_LP(s)`
  (`airyMaximizerWitness_properties`, `airyUSh_le_airyULP`). -/
theorem thm_airy_square_attained_simple {k : ℕ} {s : Fin k → ℝ} (hs : Function.Injective s) :
    Tendsto (airyLambdaSection s) atTop (𝓝 (airyLambda s)) ∧
    IsGreatest (airySquareRayleigh '' {c : lp (fun _ : ℕ => ℝ) 2 | AirySquareUnitFeasible s c})
      (airyLambda s) ∧
    LocallyLipschitzOn {x : Fin k → ℝ | Function.Injective x} (airyLambda (k := k)) ∧
    (∀ K : Set (Fin k → ℝ), IsCompact K → (∀ x ∈ K, Function.Injective x) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ M : ℕ, k + 1 ≤ M →
        0 ≤ airyLambda x - airyLambdaSection x M ∧
        airyLambda x - airyLambdaSection x M ≤ C / (M : ℝ)) ∧
    (airyZ k ≤ airyLambdaSection s (k + 1) ∧ airyLambdaSection s (k + 1) ≤ airyLambda s) ∧
    ((airyLambdaSection s (k + 1) = airyZ k ↔
        Set.range s = airyZ '' (Finset.range k : Set ℕ)) ∧
      (Set.range s = airyZ '' (Finset.range k : Set ℕ) → airyLambda s = airyZ k)) ∧
    (∀ M : ℕ, k + 1 ≤ M →
      (airyLambdaSection s M = airyLambda s ↔ ∀ j : Fin k, ∃ n : ℕ, s j = airyZ n)) ∧
    (∀ c : lp (fun _ : ℕ => ℝ) 2,
      AirySquareUnitFeasible s c → airySquareRayleigh c = airyLambda s →
      (∃ (μ : Fin k → ℝ) (M_c : ℝ),
        0 ≤ M_c ∧
        (∀ n : ℕ, (airyZ n - airyLambda s) * c n = ∑ j : Fin k, μ j * airyCardinalR n (s j)) ∧
        (∀ n : ℕ, |c n| ≤ M_c / (airyZ n) ^ 2) ∧
        Summable (fun n : ℕ => |c n|) ∧
        (∀ z : ℂ, (z - (airyLambda s : ℂ)) * airyCardinalSeries c z =
          ((∑' n : ℕ, c n : ℝ) : ℂ) * airyAiC z +
            ∑ j : Fin k, (μ j : ℂ) * airyKerC z (s j : ℂ))) ∧
      IsAirySquareClass s (airyCardinalSeries c) ∧
      airySquareClassQuotient (airyCardinalSeries c) = airyLambda s ∧
      InAiryClass (airyMaximizerWitness s c) ∧
      (∀ j : Fin k, airyMaximizerWitness s c (s j : ℂ) = 0) ∧
      (∫ u : ℝ, (airyMaximizerWitness s c (u : ℂ)).re) = 0 ∧
      (∀ y : ℝ, 0 < y → 0 < airyLaplace (fun u => (airyMaximizerWitness s c (u : ℂ)).re) y) ∧
      IsAiryWeakWitness (Set.range s) (airyLambda s) (airyMaximizerWitness s c)) ∧
    IsGreatest (airySquareClassQuotient '' {q : ℂ → ℂ | IsAirySquareClass s q}) (airyLambda s) ∧
    (airyLambda s : EReal) ≤ airyULP (Set.range s) ∧
    airyUSh (Set.range s) ≤ airyULP (Set.range s) := by
  obtain ⟨⟨c₀, hc₀_feas, hc₀_max⟩, hmax_ub⟩ := isGreatest_airySquareRayleigh hs
  obtain ⟨_, _, _, _, _, hle_ulp⟩ := airyMaximizerWitness_properties hs hc₀_feas hc₀_max
  refine ⟨tendsto_airyLambdaSection s, ⟨⟨c₀, hc₀_feas, hc₀_max⟩, hmax_ub⟩,
    locallyLipschitzOn_airyLambda k,
    fun K hK hK_inj => airyLambda_sub_section_le_on_compact hK hK_inj,
    ⟨airyZ_le_airyLambdaSection_first s, airyLambdaSection_le_airyLambda s le_rfl⟩,
    airyLambdaSection_first_eq_iff hs,
    fun M hM => airyLambdaSection_eq_airyLambda_iff hs hM,
    fun c hc hc_max => ?_,
    isGreatest_airySquareClass hs,
    hle_ulp,
    airyUSh_le_airyULP (Set.range s)⟩
  obtain ⟨hqc_mem, hqc_val⟩ := airyCardinalSeries_mem_squareClass_of_maximizer hs hc hc_max
  obtain ⟨hH_cl, hH_s, hH_i0, hH_pos, hwit, _⟩ := airyMaximizerWitness_properties hs hc hc_max
  exact ⟨airySquare_maximizer_representation hs hc hc_max, hqc_mem, hqc_val,
    hH_cl, hH_s, hH_i0, hH_pos, hwit⟩

/-- **Theorem `thm:airy-square-attained` (distinct sites, full chain with `AirySquareBoundInput`;
`ce_airy_lp.tex`).**
Combines `thm_airy_square_attained_simple` with `λ(s) ≤ u_sh(s) ≤ u_LP(s)` given the deferred
distinct-site finite-section inequality `AirySquareBoundInput s` (`lem:airy-square-bound`). -/
theorem thm_airy_square_attained_simple_full {k : ℕ} {s : Fin k → ℝ} (hs : Function.Injective s)
    (hbound : AirySquareBoundInput s) :
    IsGreatest (airySquareRayleigh '' {c : lp (fun _ : ℕ => ℝ) 2 | AirySquareUnitFeasible s c})
      (airyLambda s) ∧
    IsGreatest (airySquareClassQuotient '' {q : ℂ → ℂ | IsAirySquareClass s q}) (airyLambda s) ∧
    (airyLambda s : EReal) ≤ airyUSh (Set.range s) ∧
    airyUSh (Set.range s) ≤ airyULP (Set.range s) :=
  ⟨isGreatest_airySquareRayleigh hs, isGreatest_airySquareClass hs,
    airyLambda_le_airyUSh_of_bound s hbound, airyUSh_le_airyULP (Set.range s)⟩

/-- info: 'FormalResearch.SignUncertainty.isGreatest_airySquareRayleigh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.isGreatest_airySquareRayleigh

/-- info: 'FormalResearch.SignUncertainty.locallyLipschitzOn_airyLambda' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.locallyLipschitzOn_airyLambda

/-- info: 'FormalResearch.SignUncertainty.airyLambda_sub_section_le_on_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airyLambda_sub_section_le_on_compact

/-- info: 'FormalResearch.SignUncertainty.airySquare_maximizer_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airySquare_maximizer_representation

/-- info: 'FormalResearch.SignUncertainty.isGreatest_airySquareClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.isGreatest_airySquareClass

/-- info: 'FormalResearch.SignUncertainty.thm_airy_square_attained_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.thm_airy_square_attained_simple

/-- info: 'FormalResearch.SignUncertainty.thm_airy_square_attained_simple_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.thm_airy_square_attained_simple_full

end FormalResearch.SignUncertainty

