module

public import FormalResearch.SignUncertainty.AirySquareKernel
public import FormalResearch.SignUncertainty.Radii
public import FormalResearch.CohnElkies.OriginMellinAndS0
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Constrained Airy Square Witnesses (`ce_airy_lp_proofs.tex`, Lemma `lem:airy-square-bound`)

Source:
* `CFT/sign_uncertainty/paper/ce_airy_lp.tex` (§6(d): finite-section Rayleigh quotients `Λ_M(s)`,
  limiting threshold `λ(s)`, `Λ_M(s) ≤ u_sh(s) ≤ u_LP(s) ≤ a_1`, and the ray-dropped lower bound
  `u_sh(S) ≥ sup {v : v < λ(S ∩ (v, ∞))}` with `λ(∅) = a_1`).
* `CFT/sign_uncertainty/paper/ce_airy_lp_proofs.tex`, Lemma `lem:al-reference-positive` (`J_0`) and
  Lemma `lem:airy-square-bound` (trial-cutoff strict-site witness from `F_v - η J_0`, `Λ_M(s) ≤ u_sh(s)`
  for `M ≥ |s| + 1`, `Λ_m > a_m` for Hermite–Biehler sites with `m ≥ 2`, and `t_{m+1} ∈ (a_{m+1}, a_m)`
  so `t_{m+1} < a_m < Λ_m` for `m ∈ {2, 3}`).

Main declarations:
* **Finite sections and LP thresholds:** `airyPadLp`, `airySectionPoly`, `airySectionPolyR`,
  `AirySectionQuotientSet`, `airyLambdaSection` (`Λ_M(s)`), `airyLambda` (`λ(s)`),
  `IsAiryWeakWitness`, `IsAiryStrictWitness`, `airyULP` (`u_LP`), `airyUSh` (`u_sh`), `airySites`,
  `isGreatest_airySectionQuotientSet`, `airyLambdaSection_mono`, `tendsto_airyLambdaSection`,
  `airyLambdaSection_first_eq_imp_range`.
* **Positive reference profile (`lem:al-reference-positive`):** `airyRefJ0` (`J_0 = g_1 + g_1'`),
  `airyRefJ0_inAiryClass`, `airyRefJ0_pos`, `airyLaplace_airyRefJ0_bounds`
  (`c₁ (1 + y)^{-5/2} ≤ ℒ_y(J_0) ≤ C₁ (1 + y)^{-5/2}` on `y ≥ 0`, via `positive_source_S0_floor`).
* **Trial-cutoff strict-site witnesses & ray-dropped bound (`lem:airy-square-bound`):**
  `exists_airyLagrangeSection`, `exists_section_rayleigh_gt_and_sum_ne_zero`,
  `exists_isAiryStrictWitness_of_lt_airyLambdaSection`,
  `exists_isAiryStrictWitness_of_lt_section_above`,
  `airyLambdaSection_le_airyUSh`, `airyLambda_le_airyUSh`, `airyULP_le_airyZ_zero`,
  `airyLambda_empty_eq`, `airyUSh_ge_rayDropped`.
* **Hermite–Biehler clauses (`lem:airy-square-bound`):**
  `airyLambdaSection_hb_gt_airyZero` (`Λ_m > a_m` for `m ≥ 2`) and
  `hb_m23_node_interlace` (`t_1 > a_1`, `t_{n+1} ∈ (a_{n+1}, a_n)` for `n ≥ 1`, hence
  `a_{m+1} < t_{m+1} < a_m < Λ_m` for `m ∈ {2, 3}`).
* **Bundled headline:** `lem_airy_square_bound`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set Metric
open scoped ENNReal RealInnerProductSpace Real Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.CohnElkies

/-! ### Section 1: Finite-Section Problem, LP Thresholds, Attainment, and Monotonicity -/

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

lemma ofReal_airySectionPolyR {M : ℕ} (c : Fin M → ℝ) (u : ℝ) :
    (airySectionPolyR M c u : ℂ) = airySectionPoly M c (u : ℂ) := by
  rw [← airyCardinalSeriesR_airyPadLp, ← airyCardinalSeries_airyPadLp, ofReal_airyCardinalSeriesR]

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

/-- Universal Airy sign-uncertainty upper bound `u_LP(S) ≤ a_1` (`ce_airy_lp.tex`, line 15). -/
theorem airyULP_le_airyZ_zero (S : Set ℝ) : airyULP S ≤ (airyZ 0 : EReal) := by
  unfold airyULP
  refine iSup₂_le fun v hv => ?_
  obtain ⟨H, hH_cl, hHnz, _, hHray, hHlap⟩ := hv
  obtain ⟨hNd, hNi, ⟨C, ν, hC, hNb⟩, hNreal⟩ := hH_cl.neg
  rw [EReal.coe_le_coe_iff]
  have hlap0 := hHlap 0 le_rfl
  unfold airyLaplace at hlap0
  have hint_nn : 0 ≤ ∫ u : ℝ, (H (u : ℂ)).re := by
    have hexp0 : Real.exp (-(0 ^ 3) / 12) = 1 := by norm_num
    rw [hexp0, one_mul] at hlap0
    simpa using hlap0
  have hneg_int : (∫ x : ℝ, (-H (x : ℂ)).re) ≤ 0 := by
    have heq : (fun x : ℝ => (-H (x : ℂ)).re) = fun x : ℝ => -(H (x : ℂ)).re := by
      ext x; simp
    rw [heq, integral_neg]
    linarith only [hint_nn]
  obtain ⟨z₀, hz₀⟩ := hHnz
  exact airy_sign_uncertainty hNd hNi hC hNb hNreal
    (fun x hx => by simp [hHray x hx])
    hneg_int ⟨z₀, neg_ne_zero.mpr hz₀⟩

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

/-- The sites of a finite set `s : Finset ℝ` as an injective vector `Fin s.card → ℝ`. -/
noncomputable def airySites (s : Finset ℝ) : Fin s.card → ℝ := fun i => (s.equivFin.symm i : ℝ)

lemma airySites_injective (s : Finset ℝ) : Function.Injective (airySites s) := by
  intro i j h
  exact s.equivFin.symm.injective (Subtype.ext h)

lemma range_airySites (s : Finset ℝ) : Set.range (airySites s) = (s : Set ℝ) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i).2
  · intro hx
    exact ⟨s.equivFin ⟨x, hx⟩, by simp [airySites]⟩

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

/-- Deleting site constraints only increases `Λ_M`: if `Set.range s₁ ⊆ Set.range s₂`, then
`Λ_M(s₂) ≤ Λ_M(s₁)`. -/
theorem airyLambdaSection_le_of_range_subset {k₁ k₂ M : ℕ} {s₁ : Fin k₁ → ℝ} {s₂ : Fin k₂ → ℝ}
    (hsub : Set.range s₁ ⊆ Set.range s₂) (hM₁ : k₁ + 1 ≤ M) (hM₂ : k₂ + 1 ≤ M) :
    airyLambdaSection s₂ M ≤ airyLambdaSection s₁ M := by
  obtain ⟨c, hc1, hcker, hceq⟩ := exists_unit_section_maximizer s₂ hM₂
  have hc_ne : c ≠ 0 := by intro h0; simp [h0] at hc1
  have hcker₁ : ∀ i : Fin k₁, airySectionPolyR M c (s₁ i) = 0 := by
    intro i
    obtain ⟨j, hj⟩ := hsub ⟨i, rfl⟩
    rw [← hj]
    exact hcker j
  exact le_airyLambdaSection_of_mem hM₁ ⟨c, hc_ne, hcker₁, by rw [hceq, hc1, div_one]⟩

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

/-- Empty site list: `Λ_M(∅) = a_1` (`M ≥ 1`) and `λ(∅) = a_1` (`ce_airy_lp.tex`, line 63). -/
theorem airyLambdaSection_empty_eq {M : ℕ} (s : Fin 0 → ℝ) (hM : 1 ≤ M) :
    airyLambdaSection s M = airyZ 0 :=
  le_antisymm (airyLambdaSection_le_airyZ_zero s hM)
    ((airyZ_le_airyLambdaSection_first s).trans (airyLambdaSection_mono s le_rfl hM))

theorem airyLambda_empty_eq (s : Fin 0 → ℝ) : airyLambda s = airyZ 0 :=
  le_antisymm (airyLambda_bounds s).2 (airyLambda_bounds s).1

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

lemma exists_airyZ_eq_of_airyAi_eq_zero {x : ℝ} (h : airyAi x = 0) :
    ∃ n : ℕ, x = airyZ n := by
  have hle : x ≤ 0 := by
    by_contra hpos
    exact (airyAi_pos (not_le.mp hpos).le).ne' h
  obtain ⟨m, hm1, rfl⟩ := exists_airyZero_eq h hle
  exact ⟨m - 1, by unfold airyZ; congr 1; omega⟩

/-- Finite-dimensional forward half of `thm:airy-square-attained`(1) exactness:
if `Λ_{k+1}(s) = a_{k+1}` for distinct sites `s`, then `{s_1, …, s_k} = {a_1, …, a_k}`. -/
theorem airyLambdaSection_first_eq_imp_range {k : ℕ} {s : Fin k → ℝ} (hs : Function.Injective s)
    (hsec : airyLambdaSection s (k + 1) = airyZ k) :
    Set.range s = airyZ '' (Finset.range k : Set ℕ) := by
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

/-! ### Section 2: Reference Function `J_0 = g_1 + g_1'` (`lem:al-reference-positive`) -/

/-- Entire cardinal quotient `Ai'(z) / (z - a_1')` at the first derivative zero `a_1'`. -/
noncomputable def airyDerivCardinalC (z : ℂ) : ℂ :=
  dslope (deriv airyAiC) (airyDerivFirstZero : ℂ) z

/-- Complex extension of `J_0(u) = g_1(u) + g_1'(u)` (`ce_airy_lp_proofs.tex`,
`eq:al-reference-positive`), agreeing on `ℝ` with `ceS0 (airyZero 1) airyDerivFirstZero`. -/
noncomputable def airyRefJ0 (z : ℂ) : ℂ :=
  airyCardinal 0 z ^ 2 + airyDerivCardinalC z ^ 2

lemma differentiable_airyDerivCardinalC : Differentiable ℂ airyDerivCardinalC := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr
    differentiable_airyAiC.deriv.differentiableOn

lemma airyDerivCardinalC_ofReal (u : ℝ) :
    airyDerivCardinalC (u : ℂ) = ((dslope airyAi' airyDerivFirstZero u : ℝ) : ℂ) := by
  set a1' := airyDerivFirstZero
  have hne_eq : ∀ x : ℝ, x ≠ a1' →
      airyDerivCardinalC (x : ℂ) = ((dslope airyAi' a1' x : ℝ) : ℂ) := by
    intro x hx
    have hxc : (x : ℂ) ≠ (a1' : ℂ) := fun h => hx (Complex.ofReal_injective h)
    unfold airyDerivCardinalC
    rw [dslope_of_ne _ hxc, dslope_of_ne _ hx, slope_def_field, slope_def_field,
      deriv_airyAiC_ofReal, deriv_airyAiC_ofReal]
    push_cast
    rfl
  by_cases hu : u = a1'
  · subst hu
    have h0_seq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hseq : Tendsto (fun n : ℕ => a1' + 1 / ((n : ℝ) + 1)) atTop (𝓝 a1') := by
      simpa only [add_zero] using (tendsto_const_nhds (x := a1')).add h0_seq
    have hne_n : ∀ n : ℕ, a1' + 1 / ((n : ℝ) + 1) ≠ a1' := by
      intro n h
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith only [h, hpos]
    have hcontL : Continuous (fun x : ℝ => airyDerivCardinalC (x : ℂ)) :=
      differentiable_airyDerivCardinalC.continuous.comp Complex.continuous_ofReal
    have hd_real : Differentiable ℝ airyAi' := fun x => (hasDerivAt_airyAi' x).differentiableAt
    have hcont_d : Continuous (dslope airyAi' a1') := by
      rw [← continuousOn_univ, continuousOn_dslope univ_mem]
      exact ⟨hd_real.continuous.continuousOn, hd_real a1'⟩
    have hcontR : Continuous (fun x : ℝ => ((dslope airyAi' a1' x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hcont_d
    have htL := (hcontL.tendsto a1').comp hseq
    have htR := (hcontR.tendsto a1').comp hseq
    exact tendsto_nhds_unique htL (htR.congr fun n => (hne_eq _ (hne_n n)).symm)
  · exact hne_eq u hu

lemma airyCardinalR_zero_eq_dslope (u : ℝ) :
    airyCardinalR 0 u = dslope airyAi (airyZero 1) u := by
  have hne_eq : ∀ x : ℝ, x ≠ airyZero 1 →
      airyCardinalR 0 x = dslope airyAi (airyZero 1) x := by
    intro x hx
    have hx' : x ≠ airyZ 0 := hx
    rw [airyCardinalR_of_ne 0 hx', dslope_of_ne _ hx, slope_def_field, airyAi_airyZero 1, sub_zero]
    rfl
  by_cases hu : u = airyZero 1
  · subst hu
    have h0_seq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hseq : Tendsto (fun n : ℕ => airyZero 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (airyZero 1)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := airyZero 1)).add h0_seq
    have hne_n : ∀ n : ℕ, airyZero 1 + 1 / ((n : ℝ) + 1) ≠ airyZero 1 := by
      intro n h
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith only [h, hpos]
    have hcont_d : Continuous (dslope airyAi (airyZero 1)) := by
      rw [← continuousOn_univ, continuousOn_dslope univ_mem]
      exact ⟨differentiable_airyAi.continuous.continuousOn, differentiable_airyAi _⟩
    exact tendsto_nhds_unique ((continuous_airyCardinalR 0).tendsto _ |>.comp hseq)
      ((hcont_d.tendsto _ |>.comp hseq).congr fun n => (hne_eq _ (hne_n n)).symm)
  · exact hne_eq u hu

/-- On `ℝ`, `airyRefJ0` coincides with `ceS0 (airyZero 1) airyDerivFirstZero`. -/
theorem airyRefJ0_ofReal (u : ℝ) :
    airyRefJ0 (u : ℂ) = ((ceS0 (airyZero 1) airyDerivFirstZero u : ℝ) : ℂ) := by
  unfold airyRefJ0 ceS0 ceG1 ceG1Deriv
  rw [← ofReal_airyCardinalR, airyCardinalR_zero_eq_dslope, airyDerivCardinalC_ofReal]
  push_cast
  ring

theorem airyRefJ0_re (u : ℝ) :
    (airyRefJ0 (u : ℂ)).re = ceS0 (airyZero 1) airyDerivFirstZero u := by
  rw [airyRefJ0_ofReal, Complex.ofReal_re]

theorem airyRefJ0_pos (u : ℝ) : 0 < (airyRefJ0 (u : ℂ)).re := by
  rw [airyRefJ0_re]
  exact ceS0_pos (airyZero 1) airyDerivFirstZero (airyAi_airyZero 1) airyDerivFirstZero_spec.2.2 u

/-- `J_0 ∈ 𝒢` (`lem:al-reference-positive`). -/
theorem airyRefJ0_inAiryClass : InAiryClass airyRefJ0 := by
  have hg1 : InAiryClass (fun z => airyCardinal 0 z ^ 2) := by
    refine inAiryClass_of_airyClassG
      (by simpa only [sq] using airyCardinal_mul_mem_airyClassG 0 0) fun x => ?_
    rw [← ofReal_airyCardinalR, ← Complex.ofReal_pow, Complex.ofReal_im]
  have hg1' : InAiryClass (fun z => airyDerivCardinalC z ^ 2) := by
    set a1' := airyDerivFirstZero
    have ha1'_zero : deriv airyAiC (a1' : ℂ) = 0 := by
      rw [deriv_airyAiC_ofReal, airyDerivFirstZero_spec.2.2, Complex.ofReal_zero]
    have hd : Differentiable ℂ (fun z => airyDerivCardinalC z ^ 2) :=
      differentiable_airyDerivCardinalC.pow 2
    have hreal : ∀ x : ℝ, (airyDerivCardinalC (x : ℂ) ^ 2).im = 0 := by
      intro x
      rw [airyDerivCardinalC_ofReal, ← Complex.ofReal_pow, Complex.ofReal_im]
    have hint : Integrable (fun x : ℝ => airyDerivCardinalC (x : ℂ) ^ 2) := by
      have hdom := ceS0_integrable (airyAi_airyZero 1) airyDerivFirstZero_spec.2.2
      refine hdom.mono' (hd.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      rw [airyDerivCardinalC_ofReal, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)]
      unfold ceS0 ceG1 ceG1Deriv
      linarith only [sq_nonneg (dslope airyAi (airyZero 1) x)]
    have henv : ∃ C ν : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
        ‖airyDerivCardinalC z ^ 2‖ ≤ C * (1 + ‖z‖) ^ ν * airyEnv z := by
      set B : ℝ := |a1'| + 1
      have hB0 : 0 ≤ B := by positivity
      obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) B).exists_bound_of_continuousOn
        hd.continuous.continuousOn
      set e0 : ℝ := Real.exp (-(4 / 3) * B ^ (3 / 2 : ℝ))
      have he0p : 0 < e0 := Real.exp_pos _
      refine ⟨max 25 (|M| / e0), 1 / 2, by positivity, fun z => ?_⟩
      by_cases hz : ‖z‖ ≤ B
      · have h1 : ‖airyDerivCardinalC z ^ 2‖ ≤ |M| :=
          (hM z (by simpa using hz)).trans (le_abs_self _)
        have h2 : e0 ≤ airyEnv z := at47_env_lower hz hB0
        have h3 : 1 ≤ (1 + ‖z‖) ^ (1 / 2 : ℝ) :=
          Real.one_le_rpow (by linarith only [norm_nonneg z]) (by norm_num)
        have h4 : e0 ≤ (1 + ‖z‖) ^ (1 / 2 : ℝ) * airyEnv z := by
          calc e0 = 1 * e0 := (one_mul _).symm
            _ ≤ (1 + ‖z‖) ^ (1 / 2 : ℝ) * airyEnv z :=
              mul_le_mul h3 h2 he0p.le (by positivity)
        have h5 : |M| ≤ (|M| / e0) * ((1 + ‖z‖) ^ (1 / 2 : ℝ) * airyEnv z) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ he0p]
          exact mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
        calc ‖airyDerivCardinalC z ^ 2‖
            ≤ (|M| / e0) * ((1 + ‖z‖) ^ (1 / 2 : ℝ) * airyEnv z) := h1.trans h5
          _ ≤ max 25 (|M| / e0) * ((1 + ‖z‖) ^ (1 / 2 : ℝ) * airyEnv z) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _)
                (mul_nonneg (by positivity) (airyEnv_pos z).le)
          _ = max 25 (|M| / e0) * (1 + ‖z‖) ^ (1 / 2 : ℝ) * airyEnv z := by ring
      · replace hz := not_le.mp hz
        have hne : z ≠ (a1' : ℂ) := by
          intro h; rw [h, Complex.norm_real, Real.norm_eq_abs] at hz; dsimp [B] at hz; linarith
        have hge1 : 1 ≤ ‖z - (a1' : ℂ)‖ := by
          have htri := norm_sub_norm_le z (a1' : ℂ)
          rw [Complex.norm_real, Real.norm_eq_abs] at htri
          dsimp [B] at hz
          linarith
        have hd_le : ‖airyDerivCardinalC z‖ ≤ ‖deriv airyAiC z‖ := by
          unfold airyDerivCardinalC
          rw [dslope_of_ne _ hne, slope_def_field, ha1'_zero, sub_zero, norm_div]
          exact div_le_self (norm_nonneg _) hge1
        calc ‖airyDerivCardinalC z ^ 2‖
            = ‖airyDerivCardinalC z‖ ^ 2 := norm_pow _ 2
          _ ≤ ‖deriv airyAiC z‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd_le 2
          _ ≤ 25 * (1 + ‖z‖) ^ (1 / 2 : ℝ) * airyEnv z := at47_airyAiC_deriv_norm_sq_le z
          _ ≤ max 25 (|M| / e0) * (1 + ‖z‖) ^ (1 / 2 : ℝ) * airyEnv z := by
              have hnn := mul_nonneg (Real.rpow_nonneg (by linarith [norm_nonneg z] : (0 : ℝ) ≤ 1 + ‖z‖) (1 / 2 : ℝ))
                (airyEnv_pos z).le
              have := mul_le_mul_of_nonneg_right (le_max_left 25 (|M| / e0)) hnn
              linarith
    exact ⟨hd, hint, henv, hreal⟩
  exact hg1.add hg1'

/-- Positive-axis upper bound `J_0(u) ≤ C_J u^{-3/2} exp(-(4/3) u^{3/2})` for `u ≥ 1`
(`eq:al-reference-positive-bounds`, first display). -/
lemma airyRefJ0_pos_tail :
    ∃ C_J : ℝ, 0 < C_J ∧ ∀ u : ℝ, 1 ≤ u →
      (airyRefJ0 (u : ℂ)).re ≤ C_J * u ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by
  obtain ⟨R_plus, C_tl, hC_tl, htail, hR_bd⟩ :=
    ceS0_pos_tail (airyAi_airyZero 1) airyDerivFirstZero_spec.2.2
  refine ⟨(1 / (2 * π) + C_tl) / 2 + 1, by positivity, fun u hu1 => ?_⟩
  rw [airyRefJ0_re]
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  set s := √u
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hu1
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hsq : s ^ 2 = u := Real.sq_sqrt hu0.le
  have hcube : s ^ 3 = u ^ (3 / 2 : ℝ) := by
    have : u ^ (3 / 2 : ℝ) = s * u := by
      dsimp [s]; rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hu0.ne']; norm_num
    rw [this, ← hsq]; ring
  have ht := htail s hs1
  rw [hsq, hcube] at ht
  have hs2 : s ^ (-2 : ℝ) = u⁻¹ := by
    rw [Real.rpow_neg hs0.le, show s ^ (2 : ℝ) = s ^ 2 by norm_cast, hsq]
  have hs4 : s ^ (-4 : ℝ) ≤ s ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num)
  have hR_le : R_plus s ≤ C_tl * u⁻¹ := by
    calc R_plus s ≤ |R_plus s| := le_abs_self _
      _ ≤ C_tl * s ^ (-4 : ℝ) := hR_bd s hs1
      _ ≤ C_tl * s ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hs4 hC_tl
      _ = C_tl * u⁻¹ := by rw [hs2]
  have h2s_le : 2 * s * ceS0 (airyZero 1) airyDerivFirstZero u ≤
      (1 / (2 * π) + C_tl) * u⁻¹ * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by
    rw [ht, hs2]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    linarith only [hR_le]
  have hdiv : ceS0 (airyZero 1) airyDerivFirstZero u ≤
      ((1 / (2 * π) + C_tl) / 2) * (u⁻¹ / s) * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by
    calc ceS0 (airyZero 1) airyDerivFirstZero u
        ≤ ((1 / (2 * π) + C_tl) * u⁻¹ * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ))) / (2 * s) :=
          (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm (2 * s)] using h2s_le)
      _ = ((1 / (2 * π) + C_tl) / 2) * (u⁻¹ / s) * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by ring
  have hrpow : u⁻¹ / s = u ^ (-(3 / 2 : ℝ)) := by
    dsimp [s]
    rw [div_eq_mul_inv, ← Real.rpow_neg_one u, Real.sqrt_eq_rpow, ← Real.rpow_neg hu0.le,
      ← Real.rpow_add hu0]
    norm_num
  rw [hrpow] at hdiv
  have hnn : 0 ≤ u ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by positivity
  calc ceS0 (airyZero 1) airyDerivFirstZero u
      ≤ ((1 / (2 * π) + C_tl) / 2) * (u ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ))) := by
        simpa only [mul_assoc] using hdiv
    _ ≤ ((1 / (2 * π) + C_tl) / 2 + 1) * u ^ (-(3 / 2 : ℝ)) *
          Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by
        nlinarith only [hnn]

/-- Two-sided Laplace bounds `c₁ (1 + y)^{-5/2} ≤ ℒ_y(J_0) ≤ C₁ (1 + y)^{-5/2}` for all `y ≥ 0`
(`eq:al-reference-positive-bounds`, second display, from `positive_source_S0_floor`). -/
theorem airyLaplace_airyRefJ0_bounds :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ c₁ ≤ C₁ ∧ ∀ y : ℝ, 0 ≤ y →
      c₁ * (1 + y) ^ (-(5 / 2 : ℝ)) ≤ airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y ∧
      airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y ≤ C₁ * (1 + y) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨_, _, c_lo, C_hi, hc_lo, hle_c, hbd⟩ := positive_source_S0_floor
  have hc_lo_pos : 0 < c_lo := hc_lo
  have hC_hi_pos : 0 < C_hi := lt_of_lt_of_le hc_lo_pos hle_c
  have hcs_pos : 0 < ceCs := ceCs_pos
  have hk_pos : 0 < ceK := ceK_pos
  set m_cs : ℝ := min 1 ceCs⁻¹
  set M_cs : ℝ := max 1 ceCs⁻¹
  have hm_pos : 0 < m_cs := lt_min one_pos (inv_pos.mpr hcs_pos)
  have hM_pos : 0 < M_cs := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hm_le_M : m_cs ≤ M_cs := (min_le_left _ _).trans (le_max_left _ _)
  set c₁ : ℝ := (c_lo / ceK) * M_cs ^ (-(5 / 2 : ℝ))
  set C₁ : ℝ := (C_hi / ceK) * m_cs ^ (-(5 / 2 : ℝ))
  have hc₁_pos : 0 < c₁ := by positivity
  have hc₁_le_C₁ : c₁ ≤ C₁ := by
    dsimp [c₁, C₁]
    exact mul_le_mul (div_le_div_of_nonneg_right hle_c hk_pos.le)
      (Real.rpow_le_rpow_of_nonpos hm_pos hm_le_M (by norm_num))
      (by positivity) (by positivity)
  refine ⟨c₁, C₁, hc₁_pos, hc₁_le_C₁, fun y hy => ?_⟩
  have hfun : (fun u : ℝ => (airyRefJ0 (u : ℂ)).re) = ceS0 (airyZero 1) airyDerivFirstZero := by
    ext u; exact airyRefJ0_re u
  rw [hfun]
  set x : ℝ := y / ceCs
  have hx0 : 0 ≤ x := div_nonneg hy hcs_pos.le
  have hcx : ceCs * x = y := mul_div_cancel₀ y hcs_pos.ne'
  obtain ⟨hlo_x, hhi_x⟩ := hbd x hx0
  rw [hcx] at hlo_x hhi_x
  have htw : airyTwistedLaplace (ceS0 (airyZero 1) airyDerivFirstZero) y =
      ceK * airyLaplace (ceS0 (airyZero 1) airyDerivFirstZero) y := by
    unfold airyTwistedLaplace airyLaplace
    ring
  rw [htw] at hlo_x hhi_x
  have h1x_lo : m_cs * (1 + y) ≤ 1 + x := by
    have h1 : m_cs ≤ 1 := min_le_left _ _
    have h2 : m_cs ≤ ceCs⁻¹ := min_le_right _ _
    dsimp [x]
    rw [div_eq_mul_inv]
    nlinarith only [h1, h2, hy]
  have h1x_hi : 1 + x ≤ M_cs * (1 + y) := by
    have h1 : 1 ≤ M_cs := le_max_left _ _
    have h2 : ceCs⁻¹ ≤ M_cs := le_max_right _ _
    dsimp [x]
    rw [div_eq_mul_inv]
    nlinarith only [h1, h2, hy]
  have h1y_pos : 0 < 1 + y := by linarith only [hy]
  have hrpow_lo : M_cs ^ (-(5 / 2 : ℝ)) * (1 + y) ^ (-(5 / 2 : ℝ)) ≤ (1 + x) ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.mul_rpow hM_pos.le h1y_pos.le]
    exact Real.rpow_le_rpow_of_nonpos (by linarith only [hx0]) h1x_hi (by norm_num)
  have hrpow_hi : (1 + x) ^ (-(5 / 2 : ℝ)) ≤ m_cs ^ (-(5 / 2 : ℝ)) * (1 + y) ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.mul_rpow hm_pos.le h1y_pos.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hm_pos h1y_pos) h1x_lo (by norm_num)
  constructor
  · have hdiv : (c_lo / ceK) * (1 + x) ^ (-(5 / 2 : ℝ)) ≤
        airyLaplace (ceS0 (airyZero 1) airyDerivFirstZero) y := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hk_pos]
      simpa only [mul_comm ceK] using hlo_x
    calc c₁ * (1 + y) ^ (-(5 / 2 : ℝ))
        = (c_lo / ceK) * (M_cs ^ (-(5 / 2 : ℝ)) * (1 + y) ^ (-(5 / 2 : ℝ))) := by dsimp [c₁]; ring
      _ ≤ (c_lo / ceK) * (1 + x) ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hrpow_lo (by positivity)
      _ ≤ airyLaplace (ceS0 (airyZero 1) airyDerivFirstZero) y := hdiv
  · have hdiv : airyLaplace (ceS0 (airyZero 1) airyDerivFirstZero) y ≤
        (C_hi / ceK) * (1 + x) ^ (-(5 / 2 : ℝ)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hk_pos]
      simpa only [mul_comm ceK] using hhi_x
    calc airyLaplace (ceS0 (airyZero 1) airyDerivFirstZero) y
        ≤ (C_hi / ceK) * (1 + x) ^ (-(5 / 2 : ℝ)) := hdiv
      _ ≤ (C_hi / ceK) * (m_cs ^ (-(5 / 2 : ℝ)) * (1 + y) ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hrpow_hi (by positivity)
      _ = C₁ * (1 + y) ^ (-(5 / 2 : ℝ)) := by dsimp [C₁]; ring

/-! ### Section 3: Partial-Fraction Lagrange Vector and Maximizer Perturbation -/

/-- Partial-fraction / Lagrange-interpolation vector (`ce_airy_lp_proofs.tex`, lines 227–233):
for any `s : Fin k → ℝ` and `M ≥ k + 1`, there exists `d : Fin M → ℝ` in the constrained space
`∀ j, q_d(s_j) = 0` whose entries sum to `1`. -/
theorem exists_airyLagrangeSection {k M : ℕ} (s : Fin k → ℝ) (hM : k + 1 ≤ M) :
    ∃ d : Fin M → ℝ, (∑ n : Fin M, d n) = 1 ∧ ∀ j : Fin k, airySectionPolyR M d (s j) = 0 := by
  let P_num : ℝ[X] := ∏ j : Fin k, (Polynomial.X - Polynomial.C (s j))
  let L_basis : Fin (k + 1) → ℝ[X] := fun n =>
    ∏ m ∈ Finset.univ.erase n, (Polynomial.X - Polynomial.C (airyZ m.1))
  let d₀ : Fin (k + 1) → ℝ := fun n =>
    (∏ j : Fin k, (airyZ n.1 - s j)) /
      (∏ m ∈ Finset.univ.erase n, (airyZ n.1 - airyZ m.1))
  have hP_monic : P_num.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (s j)
  have hP_deg : P_num.natDegree = k := by
    dsimp [P_num]
    rw [Polynomial.natDegree_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (s j)]
    simp
  have hL_monic : ∀ n : Fin (k + 1), (L_basis n).Monic := fun n =>
    Polynomial.monic_prod_of_monic _ _ fun m _ => Polynomial.monic_X_sub_C (airyZ m.1)
  have hL_deg : ∀ n : Fin (k + 1), (L_basis n).natDegree = k := by
    intro n
    dsimp [L_basis]
    rw [Polynomial.natDegree_prod_of_monic _ _ fun m _ => Polynomial.monic_X_sub_C (airyZ m.1)]
    simp [Finset.card_erase_of_mem (Finset.mem_univ n)]
  have hden_ne : ∀ n : Fin (k + 1),
      (∏ m ∈ Finset.univ.erase n, (airyZ n.1 - airyZ m.1)) ≠ 0 := by
    intro n
    refine Finset.prod_ne_zero_iff.mpr fun m hm => sub_ne_zero.mpr ?_
    have hmn : m ≠ n := (Finset.mem_erase.mp hm).1
    exact fun heq => hmn (Fin.ext (airyZ_strictAnti.injective heq)).symm
  let Q_diff : ℝ[X] := P_num - ∑ n : Fin (k + 1), Polynomial.C (d₀ n) * L_basis n
  have hQ_deg : Q_diff.natDegree ≤ k := by
    dsimp [Q_diff]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le hP_deg.le ?_)
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    simp only [Finset.fold_max_le]
    refine ⟨Nat.zero_le k, fun n _ => ?_⟩
    exact (Polynomial.natDegree_C_mul_le (d₀ n) (L_basis n)).trans (hL_deg n).le
  have hQ_eval_zero : ∀ p : Fin (k + 1), Q_diff.eval (airyZ p.1) = 0 := by
    intro p
    dsimp [Q_diff]
    rw [Polynomial.eval_sub, Polynomial.eval_finsetSum]
    have hpP : P_num.eval (airyZ p.1) = ∏ j : Fin k, (airyZ p.1 - s j) := by
      simp [P_num, Polynomial.eval_prod]
    have hsum_eq : (∑ n : Fin (k + 1), (Polynomial.C (d₀ n) * L_basis n).eval (airyZ p.1)) =
        ∏ j : Fin k, (airyZ p.1 - s j) := by
      rw [Finset.sum_eq_single p]
      · simp only [Polynomial.eval_mul, Polynomial.eval_C, L_basis, Polynomial.eval_prod,
          Polynomial.eval_sub, Polynomial.eval_X, d₀]
        exact div_mul_cancel₀ _ (hden_ne p)
      · intro n _ hnp
        simp only [Polynomial.eval_mul, Polynomial.eval_C, L_basis, Polynomial.eval_prod,
          Polynomial.eval_sub, Polynomial.eval_X]
        have hp_mem : p ∈ Finset.univ.erase n := Finset.mem_erase.mpr ⟨hnp.symm, Finset.mem_univ p⟩
        rw [Finset.prod_eq_zero hp_mem (sub_self _), mul_zero]
      · intro hnot; exact absurd (Finset.mem_univ p) hnot
    rw [hpP, hsum_eq, sub_self]
  have hQ_zero : Q_diff = 0 := by
    by_contra hQne
    let Z_fin : Finset ℝ := Finset.univ.image (fun p : Fin (k + 1) => airyZ p.1)
    have hZ_inj : Function.Injective (fun p : Fin (k + 1) => airyZ p.1) :=
      fun p₁ p₂ h => Fin.ext (airyZ_strictAnti.injective h)
    have hZ_card : Z_fin.card = k + 1 := by
      dsimp [Z_fin]
      rw [Finset.card_image_of_injective _ hZ_inj, Finset.card_univ, Fintype.card_fin]
    have hZ_sub : Z_fin ⊆ Q_diff.roots.toFinset := by
      intro x hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hQne]
      exact hQ_eval_zero p
    have h1 : k + 1 ≤ Q_diff.roots.toFinset.card := hZ_card ▸ Finset.card_le_card hZ_sub
    have h2 : Q_diff.roots.toFinset.card ≤ Q_diff.roots.card := Multiset.toFinset_card_le _
    have h3 : Q_diff.roots.card ≤ Q_diff.natDegree := Polynomial.card_roots' Q_diff
    omega
  have hd₀_sum : (∑ n : Fin (k + 1), d₀ n) = 1 := by
    have hcoeff := congrArg (Polynomial.lcoeff ℝ k) hQ_zero
    simp only [Q_diff, map_sub, map_sum, Polynomial.lcoeff_apply,
      Polynomial.coeff_C_mul, map_zero] at hcoeff
    have hP_c : P_num.coeff k = 1 := by
      rw [← hP_deg, Polynomial.coeff_natDegree]
      exact hP_monic.leadingCoeff
    have hL_c : ∀ n : Fin (k + 1), (L_basis n).coeff k = 1 := by
      intro n
      rw [← hL_deg n, Polynomial.coeff_natDegree]
      exact (hL_monic n).leadingCoeff
    simp_rw [hP_c, hL_c, mul_one] at hcoeff
    linarith only [hcoeff]
  have hd₀_ker : ∀ j : Fin k, airySectionPolyR (k + 1) d₀ (s j) = 0 := by
    intro j
    by_cases hnode : ∃ p : Fin (k + 1), s j = airyZ p.1
    · obtain ⟨p, hp⟩ := hnode
      unfold airySectionPolyR
      refine Finset.sum_eq_zero fun n _ => ?_
      by_cases hnp : n = p
      · subst hnp
        have hd_p : d₀ n = 0 := by
          dsimp [d₀]
          have hnum0 : (∏ i : Fin k, (airyZ n.1 - s i)) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hp, sub_self])
          rw [hnum0, zero_div]
        rw [hd_p, zero_mul]
      · have hn_ne : n.1 ≠ p.1 := fun heq => hnp (Fin.ext heq)
        rw [hp, airyCardinalR_airyZ]
        simp [hn_ne]
    · push Not at hnode
      have heval_s := congrArg (Polynomial.eval (s j)) hQ_zero
      simp only [Q_diff, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_zero] at heval_s
      have hP_sj : P_num.eval (s j) = 0 := by
        dsimp [P_num]
        rw [Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
      rw [hP_sj, zero_sub, neg_eq_zero] at heval_s
      set prodZ : ℝ := ∏ m : Fin (k + 1), (s j - airyZ m.1)
      have hprodZ_ne : prodZ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun m _ => sub_ne_zero.mpr (hnode m)
      have hL_eval : ∀ n : Fin (k + 1), (L_basis n).eval (s j) = prodZ / (s j - airyZ n.1) := by
        intro n
        have hmul : (L_basis n).eval (s j) * (s j - airyZ n.1) = prodZ := by
          dsimp [L_basis, prodZ]
          rw [Polynomial.eval_prod]
          have hcongr : (∏ m ∈ Finset.univ.erase n, (Polynomial.X - Polynomial.C (airyZ m.1)).eval (s j)) =
              ∏ m ∈ Finset.univ.erase n, (s j - airyZ m.1) :=
            Finset.prod_congr rfl fun m _ => by simp
          rw [hcongr]
          exact Finset.prod_erase_mul Finset.univ (fun m : Fin (k + 1) => s j - airyZ m.1)
            (Finset.mem_univ n)
        exact eq_div_of_mul_eq (sub_ne_zero.mpr (hnode n)) hmul
      simp_rw [hL_eval] at heval_s
      have hsum_frac : (∑ n : Fin (k + 1), d₀ n / (s j - airyZ n.1)) = 0 := by
        have h1 : (∑ n : Fin (k + 1), d₀ n * (prodZ / (s j - airyZ n.1))) =
            prodZ * (∑ n : Fin (k + 1), d₀ n / (s j - airyZ n.1)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by ring
        rw [h1] at heval_s
        exact (mul_eq_zero.mp heval_s).resolve_left hprodZ_ne
      unfold airySectionPolyR
      have hcard_eq : ∀ n : Fin (k + 1),
          d₀ n * airyCardinalR n.1 (s j) = airyAi (s j) * (d₀ n / (s j - airyZ n.1)) := by
        intro n
        rw [airyCardinalR_of_ne n.1 (hnode n)]
        ring
      simp_rw [hcard_eq]
      rw [← Finset.mul_sum, hsum_frac, mul_zero]
  -- Pad `d₀` with zeros from `k + 1` to `M`.
  let d : Fin M → ℝ := fun n => airyPadLp d₀ n.1
  refine ⟨d, ?_, fun j => ?_⟩
  · have hfinM := hasSum_fin_of_ge_zero (M := M) (f := fun n => airyPadLp d₀ n)
      fun n hn => airyPadLp_apply_ge d₀ (hM.trans hn)
    have hfinK := hasSum_fin_of_ge_zero (M := k + 1) (f := fun n => airyPadLp d₀ n)
      fun n hn => airyPadLp_apply_ge d₀ hn
    have hsum_eq : (∑ m : Fin (k + 1), airyPadLp d₀ m.1) = ∑ m : Fin (k + 1), d₀ m :=
      Finset.sum_congr rfl fun m _ => airyPadLp_apply_lt d₀ m.2
    rw [hfinM.unique hfinK, hsum_eq, hd₀_sum]
  · have hfinM := hasSum_fin_of_ge_zero (M := M)
      (f := fun n => airyPadLp d₀ n * airyCardinalR n (s j))
      fun n hn => by rw [airyPadLp_apply_ge d₀ (hM.trans hn), zero_mul]
    have h1 : airySectionPolyR M d (s j) = airyCardinalSeriesR (airyPadLp d₀) (s j) := by
      unfold airySectionPolyR
      exact hfinM.unique (airyCardinalSeriesR_hasSum (airyPadLp d₀) (s j))
    rw [h1, airyCardinalSeriesR_airyPadLp, hd₀_ker j]

/-- Perturbing a finite-section maximizer by `exists_airyLagrangeSection` (`ce_airy_lp_proofs.tex`,
lines 233–235): whenever `v < Λ_M(s)` (`M ≥ k + 1`), there exists `c : Fin M → ℝ` with `q_c(s_j) = 0`,
`∑_{n < M} (a_n - v) c_n² > 0`, and `∑_{n < M} c_n ≠ 0`. -/
theorem exists_section_rayleigh_gt_and_sum_ne_zero {k M : ℕ} (s : Fin k → ℝ) (hM : k + 1 ≤ M)
    {v : ℝ} (hv : v < airyLambdaSection s M) :
    ∃ c : Fin M → ℝ,
      (∀ j : Fin k, airySectionPolyR M c (s j) = 0) ∧
      0 < (∑ n : Fin M, (airyZ n.1 - v) * (c n) ^ 2) ∧
      (∑ n : Fin M, c n) ≠ 0 := by
  obtain ⟨c₀, hc₀_norm, hc₀_ker, hc₀_val⟩ := exists_unit_section_maximizer s hM
  have hc₀_pos : 0 < ∑ n : Fin M, (airyZ n.1 - v) * (c₀ n) ^ 2 := by
    have heq : (∑ n : Fin M, (airyZ n.1 - v) * (c₀ n) ^ 2) =
        (∑ n : Fin M, airyZ n.1 * (c₀ n) ^ 2) - v * (∑ n : Fin M, (c₀ n) ^ 2) := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [heq, hc₀_val, hc₀_norm, mul_one]
    linarith only [hv]
  by_cases hsum0 : (∑ n : Fin M, c₀ n) ≠ 0
  · exact ⟨c₀, hc₀_ker, hc₀_pos, hsum0⟩
  · push Not at hsum0
    obtain ⟨d, hd_sum, hd_ker⟩ := exists_airyLagrangeSection s hM
    let φ : ℝ → ℝ := fun t => ∑ n : Fin M, (airyZ n.1 - v) * (c₀ n + t * d n) ^ 2
    have hφ_cont : Continuous φ := by
      dsimp [φ]
      exact continuous_finsetSum _ fun n _ =>
        continuous_const.mul ((continuous_const.add (continuous_id.mul continuous_const)).pow 2)
    have hφ0 : 0 < φ 0 := by simpa [φ] using hc₀_pos
    obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.continuousAt_iff.mp hφ_cont.continuousAt
      (φ 0 / 2) (half_pos hφ0)
    set t₀ : ℝ := δ / 2
    have ht₀_pos : 0 < t₀ := half_pos hδ_pos
    have ht₀_dist : dist t₀ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht₀_pos]
      dsimp [t₀]; linarith only [hδ_pos]
    have hφ_t₀ : 0 < φ t₀ := by
      have hd_lt := hδ_ball ht₀_dist
      rw [Real.dist_eq, abs_lt] at hd_lt
      linarith only [hd_lt.1, hφ0]
    let c : Fin M → ℝ := fun n => c₀ n + t₀ * d n
    refine ⟨c, fun j => ?_, hφ_t₀, ?_⟩
    · have hlin : airySectionPolyR M c (s j) =
          airySectionPolyR M c₀ (s j) + t₀ * airySectionPolyR M d (s j) := by
        unfold airySectionPolyR
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun n _ => by dsimp [c]; ring
      rw [hlin, hc₀_ker j, hd_ker j, mul_zero, add_zero]
    · have hsum_c : (∑ n : Fin M, c n) = (∑ n : Fin M, c₀ n) + t₀ * (∑ n : Fin M, d n) := by
        dsimp [c]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hsum_c, hsum0, hd_sum, zero_add, mul_one]
      exact ht₀_pos.ne'

/-! ### Section 4: Square Trial Profile `F_v` and Strictification `F_v - η J_0` -/

/-- For any finite-section coefficient vector `c : Fin M → ℝ`, `z ↦ z * q_c(z)²` belongs to
`InAiryClass` (`ce_airy_lp_proofs.tex`, line 236). -/
lemma airySectionPoly_mul_z_sq_inAiryClass {M : ℕ} (c : Fin M → ℝ) :
    InAiryClass (fun z => z * airySectionPoly M c z ^ 2) := by
  have hq2 : InAiryClass (fun z => airySectionPoly M c z ^ 2) := by
    have heq : (fun z => airySectionPoly M c z ^ 2) =
        fun z => airyCardinalSeries (airyPadLp c) z ^ 2 := by
      ext z; rw [airyCardinalSeries_airyPadLp]
    rw [heq]
    exact airyCardinalSeries_sq_inAiryClass (airyPadLp c)
  have hdiff : Differentiable ℂ (fun z => z * airySectionPoly M c z ^ 2) :=
    differentiable_id.mul hq2.1
  have hreal : ∀ x : ℝ, ((x : ℂ) * airySectionPoly M c (x : ℂ) ^ 2).im = 0 := by
    intro x
    rw [← ofReal_airySectionPolyR, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im]
  obtain ⟨C, ν, hC, hb⟩ := hq2.2.2.1
  have henv : ∀ z : ℂ,
      ‖z * airySectionPoly M c z ^ 2‖ ≤ C * (1 + ‖z‖) ^ (ν + 1) * airyEnv z := by
    intro z
    have h1z_pos : 0 < 1 + ‖z‖ := by linarith only [norm_nonneg z]
    have hz_le : ‖z‖ ≤ 1 + ‖z‖ := by linarith only [norm_nonneg z]
    rw [norm_mul]
    calc ‖z‖ * ‖airySectionPoly M c z ^ 2‖
        ≤ (1 + ‖z‖) * (C * (1 + ‖z‖) ^ ν * airyEnv z) :=
          mul_le_mul hz_le (hb z) (norm_nonneg _) h1z_pos.le
      _ = C * ((1 + ‖z‖) ^ (1 : ℝ) * (1 + ‖z‖) ^ ν) * airyEnv z := by
          rw [Real.rpow_one]; ring
      _ = C * (1 + ‖z‖) ^ (ν + 1) * airyEnv z := by
          rw [← Real.rpow_add h1z_pos, add_comm 1 ν]
  -- Integrability on `ℝ = Iio (-R) ∪ Icc (-R) 0 ∪ Ioi 0`.
  set R : ℝ := max 2 (∑ n : Fin M, (2 * |airyZ n.1| + 2))
  have hR2 : 2 ≤ R := le_max_left _ _
  have hcont_f : Continuous (fun x : ℝ => (x : ℂ) * airySectionPoly M c (x : ℂ) ^ 2) :=
    hdiff.continuous.comp Complex.continuous_ofReal
  have hint_pos : IntegrableOn (fun x : ℝ => (x : ℂ) * airySectionPoly M c (x : ℂ) ^ 2) (Ioi 0) := by
    have hdom := integrableOn_airy_exp_Ioi (C₂ := C) (ν := ν + 1) (b := 0) hC
    refine hdom.mono' hcont_f.aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x (hx : 0 < x) => ?_)
    have hbx := henv (x : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] at hbx
    simpa only [zero_mul, Real.exp_zero, mul_one] using hbx
  have hint_mid : IntegrableOn (fun x : ℝ => (x : ℂ) * airySectionPoly M c (x : ℂ) ^ 2) (Icc (-R) 0) :=
    hcont_f.continuousOn.integrableOn_Icc
  have hint_neg : IntegrableOn (fun x : ℝ => (x : ℂ) * airySectionPoly M c (x : ℂ) ^ 2) (Iio (-R)) := by
    set K_c : ℝ := ∑ n : Fin M, 6 * |c n|
    have hdom_pos : IntegrableOn (fun y : ℝ => K_c ^ 2 * y ^ (-(3 / 2 : ℝ))) (Ioi R) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1)
        (by linarith only [hR2] : 0 < R)).const_mul (K_c ^ 2)
    have hdom_neg : IntegrableOn (fun x : ℝ => K_c ^ 2 * (-x) ^ (-(3 / 2 : ℝ))) (Iio (-R)) := by
      have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (MeasurableEquiv.neg ℝ).measurableEmbedding
        (f := fun y : ℝ => K_c ^ 2 * y ^ (-(3 / 2 : ℝ))) (s := Ioi R)
      have hpre : (fun x : ℝ => -x) ⁻¹' (Ioi R) = Iio (-R) := by ext x; simp
      rw [hpre] at hmp
      simpa [Function.comp_def] using hmp.mpr hdom_pos
    refine hdom_neg.mono' hcont_f.aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem measurableSet_Iio fun u (hu : u < -R) => ?_)
    have hu_neg : u < 0 := by linarith only [hu, hR2]
    have hu_pos : 0 < -u := by linarith only [hu_neg]
    have habs_u : |u| = -u := abs_of_neg hu_neg
    have hq_le : |airySectionPolyR M c u| ≤ K_c * (-u) ^ (-(5 / 4 : ℝ)) := by
      unfold airySectionPolyR
      calc |∑ n : Fin M, c n * airyCardinalR n.1 u|
          ≤ ∑ n : Fin M, |c n * airyCardinalR n.1 u| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n : Fin M, (6 * |c n|) * (-u) ^ (-(5 / 4 : ℝ)) := by
            refine Finset.sum_le_sum fun n _ => ?_
            have hn_le : 2 * |airyZ n.1| + 2 ≤ R :=
              (Finset.single_le_sum (f := fun m : Fin M => 2 * |airyZ m.1| + 2)
                (fun _ _ => by positivity) (Finset.mem_univ n)).trans (le_max_right _ _)
            have hu_n : u ≤ 2 * airyZ n.1 - 1 := by
              rw [abs_of_neg (airyZ_neg n.1)] at hn_le
              linarith only [hu, hn_le]
            have hcard := airyCardinalR_neg_decay n.1 hu_n
            rw [habs_u] at hcard
            rw [abs_mul]
            calc |c n| * |airyCardinalR n.1 u|
                ≤ |c n| * (6 * (-u) ^ (-(5 / 4 : ℝ))) :=
                  mul_le_mul_of_nonneg_left hcard (abs_nonneg _)
              _ = (6 * |c n|) * (-u) ^ (-(5 / 4 : ℝ)) := by ring
        _ = K_c * (-u) ^ (-(5 / 4 : ℝ)) := by
            dsimp [K_c]; rw [Finset.sum_mul]
    rw [← ofReal_airySectionPolyR, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, habs_u]
    calc (-u) * |airySectionPolyR M c u| ^ 2
        ≤ (-u) * (K_c * (-u) ^ (-(5 / 4 : ℝ))) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hq_le 2) hu_pos.le
      _ = K_c ^ 2 * ((-u) ^ (1 : ℝ) * ((-u) ^ (-(5 / 4 : ℝ)) * (-u) ^ (-(5 / 4 : ℝ)))) := by
          rw [Real.rpow_one]; ring
      _ = K_c ^ 2 * (-u) ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_add hu_pos, ← Real.rpow_add hu_pos]; norm_num
  have hint_left : IntegrableOn (fun x : ℝ => (x : ℂ) * airySectionPoly M c (x : ℂ) ^ 2) (Iic 0) := by
    rw [← Set.Iio_union_Icc_eq_Iic (by linarith only [hR2] : -R ≤ 0)]
    exact hint_neg.union hint_mid
  have hint_all : Integrable (fun x : ℝ => (x : ℂ) * airySectionPoly M c (x : ℂ) ^ 2) := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    exact hint_left.union hint_pos
  exact ⟨hdiff, hint_all, ⟨C, ν + 1, hC, henv⟩, hreal⟩

/-- Finite-section trial profile `F_v(z) = (z - v) q_c(z)²` (`ce_airy_lp_proofs.tex`, line 236). -/
noncomputable def airyTrialSquareWitness (M : ℕ) (c : Fin M → ℝ) (v : ℝ) (z : ℂ) : ℂ :=
  (z - (v : ℂ)) * airySectionPoly M c z ^ 2

lemma airyTrialSquareWitness_re (M : ℕ) (c : Fin M → ℝ) (v u : ℝ) :
    (airyTrialSquareWitness M c v (u : ℂ)).re = (u - v) * airySectionPolyR M c u ^ 2 := by
  unfold airyTrialSquareWitness
  rw [← ofReal_airySectionPolyR, ← Complex.ofReal_pow, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
    Complex.ofReal_re]

lemma airyTrialSquareWitness_inAiryClass {M : ℕ} (c : Fin M → ℝ) (v : ℝ) :
    InAiryClass (airyTrialSquareWitness M c v) := by
  have hq2 : InAiryClass (fun z => airySectionPoly M c z ^ 2) := by
    have heq : (fun z => airySectionPoly M c z ^ 2) =
        fun z => airyCardinalSeries (airyPadLp c) z ^ 2 := by
      ext z; rw [airyCardinalSeries_airyPadLp]
    rw [heq]
    exact airyCardinalSeries_sq_inAiryClass (airyPadLp c)
  have hzq2 := airySectionPoly_mul_z_sq_inAiryClass c
  have heq : airyTrialSquareWitness M c v =
      fun z => z * airySectionPoly M c z ^ 2 - (v : ℂ) * airySectionPoly M c z ^ 2 := by
    ext z; unfold airyTrialSquareWitness; ring
  rw [heq]
  exact hzq2.sub (hq2.smul v)

/-- Quadrature identity `(eq. 239)` of `ce_airy_lp_proofs.tex`:
`∫_ℝ F_v(u) du = ∑_{n < M} (a_n - v) c_n²`. -/
lemma integral_airyTrialSquareWitness {M : ℕ} (c : Fin M → ℝ) (v : ℝ) :
    (∫ u : ℝ, (airyTrialSquareWitness M c v (u : ℂ)).re) =
      ∑ n : Fin M, (airyZ n.1 - v) * (c n) ^ 2 := by
  have hquad := inAiryClass_quadrature_re (airyTrialSquareWitness_inAiryClass c v)
  have hterm : (fun m : ℕ => (airyTrialSquareWitness M c v (airyZ m : ℂ)).re /
      airyAi' (airyZ m) ^ 2) = fun m : ℕ => (airyZ m - v) * (airyPadLp c m) ^ 2 := by
    ext m
    rw [airyTrialSquareWitness_re, ← airyCardinalSeriesR_airyPadLp, airyCardinalSeriesR_airyZ]
    have hne : airyAi' (airyZ m) ≠ 0 := airyAi'_airyZ_ne_zero m
    field_simp
  rw [hterm] at hquad
  have hfin := hasSum_fin_of_ge_zero (M := M)
    (f := fun m : ℕ => (airyZ m - v) * (airyPadLp c m) ^ 2) fun m hm => by
      rw [airyPadLp_apply_ge c hm, sq, zero_mul, mul_zero]
  have hsum_eq : (∑ n : Fin M, (airyZ n.1 - v) * (airyPadLp c n.1) ^ 2) =
      ∑ n : Fin M, (airyZ n.1 - v) * (c n) ^ 2 :=
    Finset.sum_congr rfl fun n _ => by rw [airyPadLp_apply_lt c n.2]
  rw [hsum_eq] at hfin
  exact hquad.unique hfin

/-- For `∑_{n < M} c_n ≠ 0`, `F_v(u) ≥ b J_0(u)` for all `u ≥ U` with some `U > max 0 v`, `b > 0`
(`ce_airy_lp_proofs.tex`, lines 244–245). -/
lemma airyTrialSquareWitness_ge_refJ0_tail {M : ℕ} {c : Fin M → ℝ}
    (hsum_ne : (∑ n : Fin M, c n) ≠ 0) (v : ℝ) :
    ∃ U b : ℝ, max 0 v < U ∧ 0 < b ∧ ∀ u : ℝ, U ≤ u →
      b * (airyRefJ0 (u : ℂ)).re ≤ (airyTrialSquareWitness M c v (u : ℂ)).re := by
  set S_c : ℝ := ∑ n : Fin M, c n
  have hS_pos : 0 < |S_c| := abs_pos.mpr hsum_ne
  have hS_sq_pos : 0 < S_c ^ 2 := sq_pos_of_ne_zero hsum_ne
  -- `∑_{n < M} c_n * (u / (u - a_n)) → S_c` as `u → ∞`.
  have hlim_sum : Tendsto (fun u : ℝ => ∑ n : Fin M, c n * (u / (u - airyZ n.1))) atTop (𝓝 S_c) := by
    dsimp [S_c]
    refine tendsto_finsetSum Finset.univ fun n _ => ?_
    have h1 : Tendsto (fun u : ℝ => 1 - airyZ n.1 / u) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
    rw [sub_zero] at h1
    have h2 : Tendsto (fun u : ℝ => (1 - airyZ n.1 / u)⁻¹) atTop (𝓝 1⁻¹) :=
      h1.inv₀ one_ne_zero
    rw [inv_one] at h2
    have h3 : Tendsto (fun u : ℝ => u / (u - airyZ n.1)) atTop (𝓝 1) := by
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu0
      have han : airyZ n.1 < 0 := airyZ_neg n.1
      have hden_ne : u - airyZ n.1 ≠ 0 := by linarith only [hu0, han]
      have hu_ne : u ≠ 0 := hu0.ne'
      field_simp
    simpa only [mul_one] using tendsto_const_nhds.mul h3
  obtain ⟨U₁, hU₁⟩ := Metric.tendsto_atTop.mp hlim_sum (|S_c| / 2) (half_pos hS_pos)
  obtain ⟨C_J, hCJ_pos, hJ_tail⟩ := airyRefJ0_pos_tail
  set U : ℝ := max (max U₁ 1) (2 * max 0 v + 2)
  have hU_gt_max : max 0 v < U := by
    have h0 : 0 ≤ max 0 v := le_max_left 0 v
    have h2 : 2 * max 0 v + 2 ≤ U := le_max_right _ _
    linarith only [h0, h2]
  have hU_ge1 : 1 ≤ U := (le_max_right U₁ 1).trans (le_max_left _ _)
  have hU_ge_U1 : U₁ ≤ U := (le_max_left U₁ 1).trans (le_max_left _ _)
  set b : ℝ := S_c ^ 2 / (128 * π * C_J)
  have hb_pos : 0 < b := by positivity
  refine ⟨U, b, hU_gt_max, hb_pos, fun u hu => ?_⟩
  have hu1 : 1 ≤ u := hU_ge1.trans hu
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hu_U1 : U₁ ≤ u := hU_ge_U1.trans hu
  -- Lower bound on `|∑ c_n * (u / (u - a_n))|`.
  have hsum_lb : |S_c| / 2 ≤ |∑ n : Fin M, c n * (u / (u - airyZ n.1))| := by
    have hdist := hU₁ u hu_U1
    rw [Real.dist_eq] at hdist
    have htri := abs_sub_abs_le_abs_sub S_c (∑ n : Fin M, c n * (u / (u - airyZ n.1)))
    rw [abs_sub_comm] at hdist
    linarith only [hdist, htri]
  -- Express `u * airySectionPolyR M c u`.
  have hq_id : u * airySectionPolyR M c u =
      airyAi u * (∑ n : Fin M, c n * (u / (u - airyZ n.1))) := by
    unfold airySectionPolyR
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have han : airyZ n.1 < 0 := airyZ_neg n.1
    have hne : u ≠ airyZ n.1 := by linarith only [hu0, han]
    rw [airyCardinalR_of_ne n.1 hne]
    ring
  have hq_sq_lb : (S_c ^ 2 / 4) * (airyAi u ^ 2 / u ^ 2) ≤ airySectionPolyR M c u ^ 2 := by
    have hsq1 : (|S_c| / 2) ^ 2 ≤ (∑ n : Fin M, c n * (u / (u - airyZ n.1))) ^ 2 := by
      rw [← sq_abs (∑ n : Fin M, c n * (u / (u - airyZ n.1)))]
      exact pow_le_pow_left₀ (by positivity) hsum_lb 2
    have hsq2 : (S_c ^ 2 / 4) * airyAi u ^ 2 ≤ (u * airySectionPolyR M c u) ^ 2 := by
      rw [hq_id, mul_pow]
      have h1 : (|S_c| / 2) ^ 2 = S_c ^ 2 / 4 := by rw [div_pow, sq_abs]; norm_num
      rw [← h1, mul_comm (airyAi u ^ 2)]
      exact mul_le_mul_of_nonneg_right hsq1 (sq_nonneg _)
    rw [mul_div_assoc', div_le_iff₀ (sq_pos_of_pos hu0)]
    simpa only [mul_pow, mul_comm (u ^ 2)] using hsq2
  -- Lower bound on `airyAi u ^ 2` for `u ≥ 1` via `airyAi_sub_leading_le`.
  have hAi_sq_lb : (1 / (16 * π)) * u ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) ≤ airyAi u ^ 2 := by
    have hlead := airyAi_sub_leading_le hu0
    set P := 1 / (2 * √π) * u ^ (-(1 / 4 : ℝ)) * Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ))
    have hP_pos : 0 < P := by dsimp [P]; positivity
    have h5_48 : 5 / 48 / u ^ (3 / 2 : ℝ) ≤ 1 / 2 := by
      have hc : 1 ≤ u ^ (3 / 2 : ℝ) := Real.one_le_rpow hu1 (by norm_num)
      have : 5 / 48 / u ^ (3 / 2 : ℝ) ≤ 5 / 48 := div_le_self (by norm_num) hc
      linarith only [this]
    have hAi_lb : P / 2 ≤ airyAi u := by
      have h1 := (abs_le.mp hlead).1
      have h2 : 5 / 48 / u ^ (3 / 2 : ℝ) * P ≤ (1 / 2) * P :=
        mul_le_mul_of_nonneg_right h5_48 hP_pos.le
      linarith only [h1, h2]
    have hP2_eq : (P / 2) ^ 2 =
        (1 / (16 * π)) * u ^ (-(1 / 2 : ℝ)) * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by
      dsimp [P]
      have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
      have hr : (u ^ (-(1 / 4 : ℝ))) ^ 2 = u ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast (u ^ (-(1 / 4 : ℝ))) 2, ← Real.rpow_mul hu0.le]; norm_num
      have he : Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ)) ^ 2 =
          Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      calc (1 / (2 * √π) * u ^ (-(1 / 4 : ℝ)) * Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ)) / 2) ^ 2
          = (1 / (16 * (√π * √π))) * (u ^ (-(1 / 4 : ℝ))) ^ 2 *
              Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ)) ^ 2 := by ring
        _ = (1 / (16 * π)) * u ^ (-(1 / 2 : ℝ)) * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by
            rw [hπ, hr, he]
    rw [← hP2_eq]
    exact pow_le_pow_left₀ (by positivity) hAi_lb 2
  have huv_lb : u / 2 ≤ u - v := by
    have hv_le : v ≤ max 0 v := le_max_right 0 v
    have h2 : 2 * max 0 v + 2 ≤ u := (le_max_right _ _).trans hu
    linarith only [hv_le, h2]
  have hF_lb : (S_c ^ 2 / (128 * π)) * u ^ (-(3 / 2 : ℝ)) *
      Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) ≤ (airyTrialSquareWitness M c v (u : ℂ)).re := by
    rw [airyTrialSquareWitness_re]
    have h1 : (u / 2) * ((S_c ^ 2 / 4) * (airyAi u ^ 2 / u ^ 2)) ≤
        (u - v) * airySectionPolyR M c u ^ 2 :=
      mul_le_mul huv_lb hq_sq_lb (by positivity) (by linarith only [huv_lb, hu0])
    refine le_trans ?_ h1
    have hu_pow : u / u ^ 2 * u ^ (-(1 / 2 : ℝ)) = u ^ (-(3 / 2 : ℝ)) := by
      have hdiv_u : u / u ^ 2 = u ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]; field_simp [hu0.ne']
      rw [hdiv_u, ← Real.rpow_add hu0]; norm_num
    calc (S_c ^ 2 / (128 * π)) * u ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ))
        = (u / 2) * ((S_c ^ 2 / 4) * (((1 / (16 * π)) * u ^ (-(1 / 2 : ℝ)) *
            Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ))) / u ^ 2)) := by
          rw [← hu_pow]; field_simp [hu0.ne']; ring
      _ ≤ (u / 2) * ((S_c ^ 2 / 4) * (airyAi u ^ 2 / u ^ 2)) := by
          gcongr
  calc b * (airyRefJ0 (u : ℂ)).re
      ≤ b * (C_J * u ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hJ_tail u hu1) hb_pos.le
    _ = (S_c ^ 2 / (128 * π)) * u ^ (-(3 / 2 : ℝ)) *
          Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by
        dsimp [b]; field_simp [hCJ_pos.ne']
    _ ≤ (airyTrialSquareWitness M c v (u : ℂ)).re := hF_lb

/-- Subtracting a small multiple of `J_0` from `F_v` produces a strict-site witness on any site set
`S ⊆ ℝ` whose elements above `v` lie in `{s_1, …, s_k}` (`ce_airy_lp_proofs.tex`, lines 241–252). -/
lemma exists_isAiryStrictWitness_of_section_vec {k M : ℕ} {s : Fin k → ℝ} {c : Fin M → ℝ} {v : ℝ}
    {S : Set ℝ} (hS_above : ∀ x ∈ S, v < x → ∃ j : Fin k, s j = x)
    (hker : ∀ j : Fin k, airySectionPolyR M c (s j) = 0)
    (hray_pos : 0 < ∑ n : Fin M, (airyZ n.1 - v) * (c n) ^ 2)
    (hsum_ne : (∑ n : Fin M, c n) ≠ 0) :
    ∃ H : ℂ → ℂ, IsAiryStrictWitness S v H := by
  let F := airyTrialSquareWitness M c v
  have hF_cl : InAiryClass F := airyTrialSquareWitness_inAiryClass c v
  have hJ_cl : InAiryClass airyRefJ0 := airyRefJ0_inAiryClass
  have hF_int_pos : 0 < ∫ u : ℝ, (F (u : ℂ)).re := by
    rw [integral_airyTrialSquareWitness]
    exact hray_pos
  -- `ℒ_y(F) > 0` for all `y ≥ 0` via `(u - v)(e^{yu} - e^{yv}) ≥ 0`.
  have hF_lap_pos : ∀ y : ℝ, 0 ≤ y → 0 < airyLaplace (fun u => (F (u : ℂ)).re) y := by
    intro y hy
    unfold airyLaplace
    refine mul_pos (Real.exp_pos _) ?_
    have hint_exp : Integrable (fun u : ℝ => (F (u : ℂ)).re * Real.exp (y * u)) :=
      hF_cl.integrable_exp_nonneg hy
    have hint_base : Integrable (fun u : ℝ => Real.exp (y * v) * (F (u : ℂ)).re) :=
      hF_cl.2.1.re.const_mul _
    have hpt : ∀ u : ℝ, Real.exp (y * v) * (F (u : ℂ)).re ≤ (F (u : ℂ)).re * Real.exp (y * u) := by
      intro u
      have hdiff : 0 ≤ (F (u : ℂ)).re * Real.exp (y * u) - Real.exp (y * v) * (F (u : ℂ)).re := by
        have heq : (F (u : ℂ)).re * Real.exp (y * u) - Real.exp (y * v) * (F (u : ℂ)).re =
            (u - v) * (Real.exp (y * u) - Real.exp (y * v)) * airySectionPolyR M c u ^ 2 := by
          dsimp [F]; rw [airyTrialSquareWitness_re]; ring
        rw [heq]
        refine mul_nonneg ?_ (sq_nonneg _)
        rcases le_or_gt u v with hle | hgt
        · have hexp : Real.exp (y * u) ≤ Real.exp (y * v) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle hy)
          exact mul_nonneg_of_nonpos_of_nonpos (by linarith only [hle]) (by linarith only [hexp])
        · have hexp : Real.exp (y * v) ≤ Real.exp (y * u) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hgt.le hy)
          exact mul_nonneg (by linarith only [hgt]) (by linarith only [hexp])
      linarith only [hdiff]
    have hmono := integral_mono hint_base hint_exp hpt
    rw [integral_const_mul] at hmono
    exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hF_int_pos) hmono
  -- Tail comparison `F ≥ b J_0` on `[U, ∞)` and large-`y` Laplace domination.
  obtain ⟨U, b, hU_gt, hb_pos, htail_ge⟩ := airyTrialSquareWitness_ge_refJ0_tail hsum_ne v
  have hU_pos : 0 < U := lt_of_le_of_lt (le_max_left 0 v) hU_gt
  obtain ⟨c₁, _, hc₁_pos, _, hJ_lap_bd⟩ := airyLaplace_airyRefJ0_bounds
  let g_err : ℝ → ℝ := fun u => (F (u : ℂ)).re - b * (airyRefJ0 (u : ℂ)).re
  have hg_int : Integrable g_err := hF_cl.2.1.re.sub (hJ_cl.2.1.re.const_mul b)
  set M_err : ℝ := ∫ u : ℝ, |g_err u|
  have hM_err_nn : 0 ≤ M_err := integral_nonneg fun _ => abs_nonneg _
  -- `(1 + y)^{5/2} * exp(y * U - y^3 / 12) → 0` as `y → ∞`.
  have hlim_err : Tendsto (fun y : ℝ =>
      M_err * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (y * U - y ^ 3 / 12)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => (2 * y) ^ (5 / 2 : ℝ) * Real.exp (-(1 / 24 : ℝ) * y))
        atTop (𝓝 0) := by
      have ha := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 / 2 : ℝ) (1 / 24 : ℝ) (by norm_num)
      have hb := ha.const_mul ((2 : ℝ) ^ (5 / 2 : ℝ))
      rw [mul_zero] at hb
      refine hb.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy0
      rw [Real.mul_rpow (by norm_num) hy0, mul_assoc]
    have h2 := h1.const_mul M_err
    rw [mul_zero] at h2
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [eventually_ge_atTop (max 1 (Real.sqrt (24 * U + 2)))] with y hy
    have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
    have hy_sq : 24 * U + 2 ≤ y ^ 2 := by
      have hsr : Real.sqrt (24 * U + 2) ≤ y := (le_max_right _ _).trans hy
      have hnn : 0 ≤ 24 * U + 2 := by positivity
      calc 24 * U + 2 = (Real.sqrt (24 * U + 2)) ^ 2 := (Real.sq_sqrt hnn).symm
        _ ≤ y ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsr 2
    have hexp_le : y * U - y ^ 3 / 12 ≤ -(1 / 24 : ℝ) * y := by
      have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy1
      have hy3 : 0 ≤ y ^ 3 := by positivity
      have hmul : (24 * U + 2) * y ≤ y ^ 3 := by
        calc (24 * U + 2) * y ≤ y ^ 2 * y := mul_le_mul_of_nonneg_right hy_sq hy0.le
          _ = y ^ 3 := by ring
      have h24 : 24 * (y * U - y ^ 3 / 12 + (1 / 24 : ℝ) * y) =
          ((24 * U + 2) * y - y ^ 3) - y ^ 3 - y := by ring
      have hnp : 24 * (y * U - y ^ 3 / 12 + (1 / 24 : ℝ) * y) ≤ 0 := by
        linarith only [h24, hmul, hy3, hy0]
      linarith only [hnp]
    have hrpow_le : (1 + y) ^ (5 / 2 : ℝ) ≤ (2 * y) ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith only [hy1]) (by norm_num)
    rw [Real.norm_of_nonneg (by positivity)]
    calc M_err * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (y * U - y ^ 3 / 12)
        = M_err * ((1 + y) ^ (5 / 2 : ℝ) * Real.exp (y * U - y ^ 3 / 12)) := by ring
      _ ≤ M_err * ((2 * y) ^ (5 / 2 : ℝ) * Real.exp (-(1 / 24 : ℝ) * y)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hrpow_le (Real.exp_le_exp.mpr hexp_le) (Real.exp_pos _).le (by positivity))
            hM_err_nn
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp
    (hlim_err.eventually (gt_mem_nhds (mul_pos (half_pos hb_pos) hc₁_pos)))
  set Y : ℝ := max Y₀ 1
  have hY_pos : 0 < Y := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  -- For `y ≥ Y`, `(b / 2) * ℒ_y(J_0) ≤ ℒ_y(F)`.
  have hlap_large : ∀ y : ℝ, Y ≤ y →
      (b / 2) * airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y ≤
        airyLaplace (fun u => (F (u : ℂ)).re) y := by
    intro y hy
    have hy0 : 0 ≤ y := (hY_pos.trans_le hy).le
    have hyY0 : Y₀ ≤ y := (le_max_left _ _).trans hy
    have hF_y : Integrable (fun u : ℝ => (F (u : ℂ)).re * Real.exp (y * u)) :=
      hF_cl.integrable_exp_nonneg hy0
    have hJ_y : Integrable (fun u : ℝ => (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) :=
      hJ_cl.integrable_exp_nonneg hy0
    have hg_y : Integrable (fun u : ℝ => g_err u * Real.exp (y * u)) := by
      have heq : (fun u : ℝ => g_err u * Real.exp (y * u)) =
          fun u : ℝ => (F (u : ℂ)).re * Real.exp (y * u) -
            b * ((airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) := by
        ext u; dsimp [g_err]; ring
      rw [heq]
      exact hF_y.sub (hJ_y.const_mul b)
    have hsplit_g : (∫ u : ℝ, g_err u * Real.exp (y * u)) =
        (∫ u in Iic U, g_err u * Real.exp (y * u)) + ∫ u in Ioi U, g_err u * Real.exp (y * u) := by
      rw [← compl_Iic]
      exact (integral_add_compl measurableSet_Iic hg_y).symm
    have hIoi_nn : 0 ≤ ∫ u in Ioi U, g_err u * Real.exp (y * u) := by
      refine setIntegral_nonneg measurableSet_Ioi fun u (hu : U < u) => ?_
      refine mul_nonneg ?_ (Real.exp_pos _).le
      dsimp [g_err]
      linarith only [htail_ge u hu.le]
    have hIic_lb : -M_err * Real.exp (y * U) ≤ ∫ u in Iic U, g_err u * Real.exp (y * u) := by
      have h1 : (∫ u in Iic U, -(g_err u * Real.exp (y * u))) ≤
          ∫ u in Iic U, |g_err u| * Real.exp (y * U) := by
        refine setIntegral_mono_on hg_y.neg.integrableOn (hg_int.abs.mul_const _).integrableOn
          measurableSet_Iic fun u (hu : u ≤ U) => ?_
        have hexp : Real.exp (y * u) ≤ Real.exp (y * U) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu hy0)
        have habs := neg_abs_le (g_err u)
        nlinarith only [hexp, habs, Real.exp_pos (y * u), abs_nonneg (g_err u)]
      have h2 : (∫ u in Iic U, |g_err u| * Real.exp (y * U)) ≤ M_err * Real.exp (y * U) := by
        rw [integral_mul_const]
        exact mul_le_mul_of_nonneg_right
          (setIntegral_le_integral hg_int.abs (Eventually.of_forall fun _ => abs_nonneg _))
          (Real.exp_pos _).le
      rw [integral_neg] at h1
      linarith only [h1, h2]
    have hg_int_lb : -M_err * Real.exp (y * U) ≤
        (∫ u : ℝ, (F (u : ℂ)).re * Real.exp (y * u)) -
          b * ∫ u : ℝ, (airyRefJ0 (u : ℂ)).re * Real.exp (y * u) := by
      have heq_int : (∫ u : ℝ, g_err u * Real.exp (y * u)) =
          (∫ u : ℝ, (F (u : ℂ)).re * Real.exp (y * u)) -
            b * ∫ u : ℝ, (airyRefJ0 (u : ℂ)).re * Real.exp (y * u) := by
        have heq : (fun u : ℝ => g_err u * Real.exp (y * u)) =
            fun u : ℝ => (F (u : ℂ)).re * Real.exp (y * u) -
              b * ((airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) := by
          ext u; dsimp [g_err]; ring
        rw [heq, integral_sub hF_y (hJ_y.const_mul b), integral_const_mul]
      linarith only [heq_int, hsplit_g, hIoi_nn, hIic_lb]
    have hlap_diff : -M_err * Real.exp (y * U - y ^ 3 / 12) ≤
        airyLaplace (fun u => (F (u : ℂ)).re) y -
          b * airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y := by
      unfold airyLaplace
      have hexp_prod : Real.exp (-(y ^ 3) / 12) * (-M_err * Real.exp (y * U)) =
          -M_err * Real.exp (y * U - y ^ 3 / 12) := by
        have : Real.exp (-(y ^ 3) / 12) * Real.exp (y * U) = Real.exp (y * U - y ^ 3 / 12) := by
          rw [← Real.exp_add]; congr 1; ring
        calc Real.exp (-(y ^ 3) / 12) * (-M_err * Real.exp (y * U))
            = -M_err * (Real.exp (-(y ^ 3) / 12) * Real.exp (y * U)) := by ring
          _ = -M_err * Real.exp (y * U - y ^ 3 / 12) := by rw [this]
      have hmul := mul_le_mul_of_nonneg_left hg_int_lb (Real.exp_pos (-(y ^ 3) / 12)).le
      linarith only [hmul, hexp_prod]
    have herr_small : M_err * Real.exp (y * U - y ^ 3 / 12) ≤
        (b / 2) * airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y := by
      have hlt := (hY₀ y hyY0).le
      have h1y_pos : 0 < (1 + y) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith only [hy0]) _
      have hrpow_inv : (1 + y) ^ (-(5 / 2 : ℝ)) = ((1 + y) ^ (5 / 2 : ℝ))⁻¹ :=
        Real.rpow_neg (by linarith only [hy0]) (5 / 2)
      have hdiv : M_err * Real.exp (y * U - y ^ 3 / 12) ≤
          (b / 2) * (c₁ * (1 + y) ^ (-(5 / 2 : ℝ))) := by
        rw [hrpow_inv, ← mul_assoc, ← div_eq_mul_inv, le_div_iff₀ h1y_pos]
        calc M_err * Real.exp (y * U - y ^ 3 / 12) * (1 + y) ^ (5 / 2 : ℝ)
            = M_err * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (y * U - y ^ 3 / 12) := by ring
          _ ≤ b / 2 * c₁ := hlt
      exact hdiv.trans (mul_le_mul_of_nonneg_left (hJ_lap_bd y hy0).1 (by positivity))
    linarith only [hlap_diff, herr_small]
  -- On `[0, Y]`, `y ↦ ℒ_y(F) / ℒ_y(J_0)` is continuous and strictly positive.
  have hcont_LF : ContinuousOn (airyLaplace (fun u => (F (u : ℂ)).re)) (Icc 0 Y) := by
    unfold airyLaplace
    exact (Real.continuous_exp.comp
      ((continuous_pow 3).neg.div_const 12)).continuousOn.mul
      (hF_cl.laplace_continuousOn_Ici.mono Icc_subset_Ici_self)
  have hcont_LJ : ContinuousOn (airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re)) (Icc 0 Y) := by
    unfold airyLaplace
    exact (Real.continuous_exp.comp
      ((continuous_pow 3).neg.div_const 12)).continuousOn.mul
      (hJ_cl.laplace_continuousOn_Ici.mono Icc_subset_Ici_self)
  have hLJ_pos : ∀ y : ℝ, 0 ≤ y → 0 < airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y := by
    intro y hy
    exact lt_of_lt_of_le (by positivity) (hJ_lap_bd y hy).1
  let ratio : ℝ → ℝ := fun y =>
    airyLaplace (fun u => (F (u : ℂ)).re) y / airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y
  have hcont_ratio : ContinuousOn ratio (Icc 0 Y) :=
    hcont_LF.div hcont_LJ fun y hy => (hLJ_pos y hy.1).ne'
  obtain ⟨y_min, hy_min_mem, hy_min⟩ :=
    isCompact_Icc.exists_isMinOn ⟨0, le_rfl, hY_pos.le⟩ hcont_ratio
  have hr_min_pos : 0 < ratio y_min :=
    div_pos (hF_lap_pos y_min hy_min_mem.1) (hLJ_pos y_min hy_min_mem.1)
  set η : ℝ := min (b / 4) (ratio y_min / 2)
  have hη_pos : 0 < η := lt_min (by positivity) (half_pos hr_min_pos)
  let H : ℂ → ℂ := fun z => F z - (η : ℂ) * airyRefJ0 z
  have hH_cl : InAiryClass H := hF_cl.sub (hJ_cl.smul η)
  have hH_re : ∀ u : ℝ, (H (u : ℂ)).re = (F (u : ℂ)).re - η * (airyRefJ0 (u : ℂ)).re := by
    intro u
    dsimp [H]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hH_lap_pos : ∀ y : ℝ, 0 ≤ y → 0 < airyLaplace (fun u => (H (u : ℂ)).re) y := by
    intro y hy
    have hF_y := hF_cl.integrable_exp_nonneg hy
    have hJ_y := hJ_cl.integrable_exp_nonneg hy
    have hlap_sub : airyLaplace (fun u => (H (u : ℂ)).re) y =
        airyLaplace (fun u => (F (u : ℂ)).re) y -
          η * airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y := by
      unfold airyLaplace
      have heq : (fun u : ℝ => (H (u : ℂ)).re * Real.exp (y * u)) =
          fun u : ℝ => (F (u : ℂ)).re * Real.exp (y * u) -
            η * ((airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) := by
        ext u; rw [hH_re]; ring
      rw [heq, integral_sub hF_y (hJ_y.const_mul η), integral_const_mul]
      ring
    rw [hlap_sub]
    have hLJ := hLJ_pos y hy
    rcases le_or_gt y Y with hle | hgt
    · have hη_lt : η < ratio y_min := (min_le_right _ _).trans_lt (half_lt_self hr_min_pos)
      have hr_le : ratio y_min ≤ ratio y := hy_min ⟨hy, hle⟩
      have hlt_r : η < ratio y := hη_lt.trans_le hr_le
      have hmul := (lt_div_iff₀ hLJ).mp hlt_r
      linarith only [hmul]
    · have hη_lt_b : η < b / 2 :=
        (min_le_left _ _).trans_lt (by linarith only [hb_pos])
      have h1 : η * airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y <
          (b / 2) * airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y :=
        mul_lt_mul_of_pos_right hη_lt_b hLJ
      linarith only [h1, hlap_large y hgt.le]
  have hH_nz : ∃ z : ℂ, H z ≠ 0 := by
    by_contra hall0
    push Not at hall0
    have hre0 : ∀ u : ℝ, (H (u : ℂ)).re = 0 := fun u => by rw [hall0 (u : ℂ), Complex.zero_re]
    have hlap0 := hH_lap_pos 0 le_rfl
    unfold airyLaplace at hlap0
    simp [hre0] at hlap0
  have hH_ray_lt : ∀ u : ℝ, u ≤ v → (H (u : ℂ)).re < 0 := by
    intro u hu
    rw [hH_re]
    have hF_le : (F (u : ℂ)).re ≤ 0 := by
      dsimp [F]
      rw [airyTrialSquareWitness_re]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) (sq_nonneg _)
    have hJ_pos : 0 < η * (airyRefJ0 (u : ℂ)).re := mul_pos hη_pos (airyRefJ0_pos u)
    linarith only [hF_le, hJ_pos]
  have hH_sites_lt : ∀ x ∈ S, (H (x : ℂ)).re < 0 := by
    intro x hx
    rcases le_or_gt x v with hle | hgt
    · exact hH_ray_lt x hle
    · obtain ⟨j, hj⟩ := hS_above x hx hgt
      rw [hH_re]
      have hF0 : (F (x : ℂ)).re = 0 := by
        dsimp [F]
        rw [airyTrialSquareWitness_re, ← hj, hker j, sq, zero_mul, mul_zero]
      have hJ_pos : 0 < η * (airyRefJ0 (x : ℂ)).re := mul_pos hη_pos (airyRefJ0_pos x)
      linarith only [hF0, hJ_pos]
  exact ⟨H, ⟨hH_cl, hH_nz, fun x hx => (hH_sites_lt x hx).le,
    fun u hu => (hH_ray_lt u hu).le, fun y hy => (hH_lap_pos y hy).le⟩, hH_sites_lt⟩

/-- If `M ≥ k + 1` and `v < Λ_M(s)` (arbitrary `s : Fin k → ℝ`), there exists a strict-site
witness at cutoff `v` for `Set.range s` (`lem:airy-square-bound`). -/
theorem exists_isAiryStrictWitness_of_lt_airyLambdaSection {k M : ℕ} (s : Fin k → ℝ)
    (hM : k + 1 ≤ M) {v : ℝ} (hv : v < airyLambdaSection s M) :
    ∃ H : ℂ → ℂ, IsAiryStrictWitness (Set.range s) v H := by
  obtain ⟨c, hker, hray, hsum⟩ := exists_section_rayleigh_gt_and_sum_ne_zero s hM hv
  exact exists_isAiryStrictWitness_of_section_vec (fun _ hx _ => hx) hker hray hsum

/-- Trial-cutoff strict-site witness (`ce_airy_lp_proofs.tex`, `lem:airy-square-bound`):
for any finite set `S : Finset ℝ`, cutoff `v : ℝ`, and `M ≥ |S ∩ (v, ∞)| + 1` with
`v < Λ_M(S ∩ (v, ∞))`, there exists a strict-site witness at `v` for all of `S`. -/
theorem exists_isAiryStrictWitness_of_lt_section_above (S : Finset ℝ) (v : ℝ) {M : ℕ}
    (hM : (S.filter (v < ·)).card + 1 ≤ M)
    (hv : v < airyLambdaSection (airySites (S.filter (v < ·))) M) :
    ∃ H : ℂ → ℂ, IsAiryStrictWitness (S : Set ℝ) v H := by
  obtain ⟨c, hker, hray, hsum⟩ :=
    exists_section_rayleigh_gt_and_sum_ne_zero (airySites (S.filter (v < ·))) hM hv
  refine exists_isAiryStrictWitness_of_section_vec (fun x hx hgt => ?_) hker hray hsum
  have hx_mem : x ∈ ((S.filter (v < ·) : Finset ℝ) : Set ℝ) :=
    Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hx, hgt⟩)
  rwa [← range_airySites] at hx_mem

/-- Finite-section bound (`ce_airy_lp.tex`, line 15; `ce_airy_lp_proofs.tex`,
`lem:airy-square-bound`): `Λ_M(s) ≤ u_sh(s)` for every `s : Fin k → ℝ` and `M ≥ k + 1`. -/
theorem airyLambdaSection_le_airyUSh {k M : ℕ} (s : Fin k → ℝ) (hM : k + 1 ≤ M) :
    (airyLambdaSection s M : EReal) ≤ airyUSh (Set.range s) := by
  set L : ℝ := airyLambdaSection s M
  have hbelow : ∀ v : ℝ, v < L → ((v : ℝ) : EReal) ≤ airyUSh (Set.range s) := fun v hv =>
    le_iSup₂_of_le v (exists_isAiryStrictWitness_of_lt_airyLambdaSection s hM hv) le_rfl
  generalize hu : airyUSh (Set.range s) = u
  induction u using EReal.rec with
  | bot =>
    have h1 := hbelow (L - 1) (by linarith)
    rw [hu] at h1
    exact False.elim (not_le_of_gt (EReal.bot_lt_coe _) h1)
  | coe r =>
    rw [EReal.coe_le_coe_iff]
    by_contra hnot
    have hgt : r < L := not_le.mp hnot
    have hmid := hbelow ((r + L) / 2) (by linarith only [hgt])
    rw [hu, EReal.coe_le_coe_iff] at hmid
    linarith only [hgt, hmid]
  | top => exact le_top

/-- Finite-set form of `airyLambdaSection_le_airyUSh`: for `S : Finset ℝ` and `M ≥ S.card + 1`,
`Λ_M(S) ≤ u_sh(S)`. -/
theorem airyLambdaSection_airySites_le_airyUSh (S : Finset ℝ) {M : ℕ} (hM : S.card + 1 ≤ M) :
    (airyLambdaSection (airySites S) M : EReal) ≤ airyUSh (S : Set ℝ) := by
  simpa only [range_airySites] using airyLambdaSection_le_airyUSh (airySites S) hM

/-- Limiting Airy square bound (`ce_airy_lp.tex`, `thm:airy-square-attained`(3)):
`λ(s) ≤ u_sh(s)` for every `s : Fin k → ℝ`. -/
theorem airyLambda_le_airyUSh {k : ℕ} (s : Fin k → ℝ) :
    (airyLambda s : EReal) ≤ airyUSh (Set.range s) := by
  have : Nonempty {M : ℕ // k + 1 ≤ M} := ⟨⟨k + 1, le_rfl⟩⟩
  generalize hu : airyUSh (Set.range s) = u
  induction u using EReal.rec with
  | bot =>
    have h1 := airyLambdaSection_le_airyUSh s (M := k + 1) le_rfl
    rw [hu] at h1
    exact False.elim (not_le_of_gt (EReal.bot_lt_coe _) h1)
  | coe r =>
    rw [EReal.coe_le_coe_iff]
    refine ciSup_le fun M => ?_
    have hM := airyLambdaSection_le_airyUSh s M.2
    rw [hu, EReal.coe_le_coe_iff] at hM
    exact hM
  | top => exact le_top

/-- If `v < λ(S ∩ (v, ∞))` for a finite set `S : Finset ℝ`, there exists a strict-site witness at
cutoff `v` for `S` (`ce_airy_lp.tex`, lines 60–63; `lem:airy-square-bound`). -/
theorem exists_isAiryStrictWitness_of_lt_airyLambda_above (S : Finset ℝ) {v : ℝ}
    (hv : v < airyLambda (airySites (S.filter (v < ·)))) :
    ∃ H : ℂ → ℂ, IsAiryStrictWitness (S : Set ℝ) v H := by
  set S_v := S.filter (v < ·)
  have : Nonempty {M : ℕ // S_v.card + 1 ≤ M} := ⟨⟨S_v.card + 1, le_rfl⟩⟩
  obtain ⟨⟨M, hM⟩, hvM⟩ :=
    (lt_ciSup_iff (bddAbove_airyLambdaSection (airySites S_v))).mp hv
  exact exists_isAiryStrictWitness_of_lt_section_above S v hM hvM

/-- Ray-dropped lower bound (`ce_airy_lp.tex`, line 61; `ce_airy_lp_proofs.tex`,
`lem:airy-square-bound`): for every finite site set `S : Finset ℝ`,
`sup {v : ℝ | v < λ(S ∩ (v, ∞))} ≤ u_sh(S)`. -/
theorem airyUSh_ge_rayDropped (S : Finset ℝ) :
    (⨆ (v : ℝ) (_ : v < airyLambda (airySites (S.filter (v < ·)))), (v : EReal)) ≤
      airyUSh (S : Set ℝ) :=
  iSup₂_le fun v hv =>
    le_iSup₂_of_le v (exists_isAiryStrictWitness_of_lt_airyLambda_above S hv) le_rfl

/-- Vector-indexed ray-dropped lower bound for `Set.range s` (`s : Fin k → ℝ`). -/
theorem airyUSh_range_ge_rayDropped {k : ℕ} (s : Fin k → ℝ) :
    (⨆ (v : ℝ)
      (_ : v < airyLambda (airySites ((Finset.univ.image s).filter (v < ·)))),
        (v : EReal)) ≤
      airyUSh (Set.range s) := by
  have hset : ((Finset.univ.image s : Finset ℝ) : Set ℝ) = Set.range s := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  simpa only [hset] using airyUSh_ge_rayDropped (Finset.univ.image s)

/-! ### Section 5: Hermite–Biehler Clauses of `lem:airy-square-bound` -/

/-- **Hermite–Biehler strict gap (`ce_airy_lp_proofs.tex`, `lem:airy-square-bound`):**
for any Hermite–Biehler configuration `D : ShellHBData` with `m = D.S.card ≥ 2` and prescribed
sites `S₀ = D.S \ {t_m}`, `Λ_m(S₀) > a_m`.
(Note: `airyLambdaSection (airySites (D.S.erase D.tm)) D.S.card` is definitionally
`CeCanonicalDefs.airyLambdaM (shellSites D) D.S.card`.) -/
theorem airyLambdaSection_hb_gt_airyZero (D : ShellHBData) (hm : 2 ≤ D.S.card) :
    airyZero D.S.card < airyLambdaSection (airySites (D.S.erase D.tm)) D.S.card := by
  set S₀ : Finset ℝ := D.S.erase D.tm
  have hcard : S₀.card + 1 = D.S.card := by
    dsimp [S₀]
    rw [Finset.card_erase_of_mem D.tm_mem]
    omega
  have hle : airyZero D.S.card ≤ airyLambdaSection (airySites S₀) D.S.card := by
    have h0 := airyZ_le_airyLambdaSection_first (airySites S₀)
    unfold airyZ at h0
    rwa [hcard] at h0
  refine lt_of_le_of_ne hle fun heq => ?_
  have heq' : airyLambdaSection (airySites S₀) (S₀.card + 1) = airyZ S₀.card := by
    unfold airyZ
    rw [hcard]
    exact heq.symm
  have hran := airyLambdaSection_first_eq_imp_range (airySites_injective S₀) heq'
  rw [range_airySites] at hran
  have hQ_info : D.Q ≠ 0 ∧ D.S.card = at47_m D.P D.Q := by
    rcases D.m_eq with ⟨_, hc1⟩ | h2
    · omega
    · exact h2
  obtain ⟨hQ_ne, hm_eq⟩ := hQ_info
  have hm_ge_Q : 2 * D.Q.natDegree + 2 ≤ D.S.card := hm_eq ▸ at47_m_ge_Q D.P D.Q
  -- Every `airyZ n` (`n < S₀.card`) belongs to `S₀ ⊆ D.S`, forcing `D.Q.eval (airyZ n) = 0`.
  have hQ_root : ∀ n : ℕ, n < S₀.card → D.Q.eval (airyZ n) = 0 := by
    intro n hn
    have hmem_S₀ : airyZ n ∈ (S₀ : Set ℝ) := by
      rw [hran]
      exact ⟨n, Finset.mem_coe.mpr (Finset.mem_range.mpr hn), rfl⟩
    have hmem_S : airyZ n ∈ D.S := Finset.erase_subset D.tm D.S (Finset.mem_coe.mp hmem_S₀)
    have hpr0 : at47_pr D.S (airyZ n : ℂ) = 0 := at47_pr_eq_zero hmem_S
    have hprod := D.G_prod_eq (airyZ n : ℂ)
    rw [hpr0, mul_zero] at hprod
    have hsign_ne : (((-1 : ℝ) ^ D.S.card : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    have hN2_0 : airyPQN D.P D.Q (airyZ n : ℂ) ^ 2 = 0 :=
      (mul_eq_zero.mp hprod.symm).resolve_left hsign_ne
    have hN0 : airyPQN D.P D.Q (airyZ n : ℂ) = 0 := sq_eq_zero_iff.mp hN2_0
    rw [airyPQN_ofReal, Complex.ofReal_eq_zero, airyAi_airyZ, mul_zero, zero_add] at hN0
    exact (mul_eq_zero.mp hN0).resolve_right (airyAi'_airyZ_ne_zero n)
  let Z_fin : Finset ℝ := (Finset.range S₀.card).image airyZ
  have hZ_card : Z_fin.card = S₀.card := by
    dsimp [Z_fin]
    rw [Finset.card_image_of_injective _ airyZ_injective, Finset.card_range]
  have hZ_sub : Z_fin ⊆ D.Q.roots.toFinset := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ_ne]
    exact hQ_root n (Finset.mem_range.mp hn)
  have h1 : S₀.card ≤ D.Q.roots.toFinset.card := hZ_card ▸ Finset.card_le_card hZ_sub
  have h2 : D.Q.roots.toFinset.card ≤ D.Q.roots.card := Multiset.toFinset_card_le _
  have h3 : D.Q.roots.card ≤ D.Q.natDegree := Polynomial.card_roots' D.Q
  omega

/-- Auxiliary positivity `0 < Ai'(a_1)` at the first Airy zero `a_1 = airyZero 1`. -/
private lemma airyAi'_airyZero_one_pos : 0 < airyAi' (airyZero 1) := by
  have ha1_lt0 : airyZero 1 < 0 := airyZero_neg 1
  have hno_zero : ∀ x ∈ Ioo (airyZero 1) 1, airyAi x ≠ 0 := by
    intro x hx h0
    rcases le_or_gt x 0 with hx0 | hx0
    · obtain ⟨m, hm1, rfl⟩ := exists_airyZero_eq h0 hx0
      have hle : airyZero m ≤ airyZero 1 := by
        rcases hm1.eq_or_lt with rfl | hlt
        · exact le_rfl
        · exact (airyZero_lt_of_lt (by omega) hlt).le
      linarith only [hx.1, hle]
    · exact (airyAi_pos hx0.le).ne' h0
  have hpos_on : ∀ x ∈ Ioo (airyZero 1) 1, 0 < airyAi x := by
    rcases at47_const_sign differentiable_airyAi.continuous hno_zero with hp | hn
    · exact hp
    · exfalso
      have h0_mem : (0 : ℝ) ∈ Ioo (airyZero 1) 1 := ⟨ha1_lt0, zero_lt_one⟩
      linarith only [hn 0 h0_mem, airyAi_pos (le_rfl : (0 : ℝ) ≤ 0)]
  have hnn : 0 ≤ airyAi' (airyZero 1) :=
    at47_deriv_right_nonneg (hasDerivAt_airyAi (airyZero 1)) (airyAi_airyZero 1)
      (by linarith only [ha1_lt0] : airyZero 1 < 1) hpos_on
  exact lt_of_le_of_ne hnn (at47_airyAi'_zero_ne 1).symm

/-- Energy bound `Ai'(x) ≤ -√x * Ai(x)` for all `x ≥ 0` (from `integral_Ioi_airyAi_sq`). -/
private lemma airyAi'_le_neg_sqrt_mul_airyAi {x : ℝ} (hx : 0 ≤ x) :
    airyAi' x ≤ -√x * airyAi x := by
  have hint_nn : 0 ≤ ∫ t in Ioi x, airyAi t ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  rw [integral_Ioi_airyAi_sq x] at hint_nn
  have hsq : (√x * airyAi x) ^ 2 ≤ (-airyAi' x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hx, neg_sq]
    linarith only [hint_nn]
  have hle : √x * airyAi x ≤ -airyAi' x := by
    have hpos_r : 0 ≤ -airyAi' x := by linarith only [airyAi'_neg hx]
    have hpos_l : 0 ≤ √x * airyAi x := mul_nonneg (Real.sqrt_nonneg x) (airyAi_pos hx).le
    nlinarith only [hsq, hpos_r, hpos_l]
  linarith only [hle]

/-- **Hermite–Biehler node interlacing for `m ∈ {2, 3}` (`ce_airy_lp_proofs.tex`,
`lem:airy-square-bound`, lines 261–266):**
when `m = D.S.card ∈ {2, 3}`, `Q` is a nonzero constant and `deg P ≤ 1`, so the strictly decreasing
enumeration `t : ℕ → ℝ` (`t k = t_{k+1}`) of the real zeros of `N = P Ai + Q Ai'` satisfies
`t_1 > a_1` (`airyZero 1 < t 0`), `t_{n+1} ∈ (a_{n+1}, a_n)` for all `n ≥ 1`
(`airyZero (n + 1) < t n ∧ t n < airyZero n`), and in particular
`a_{m+1} < t_{m+1} < a_m < Λ_m(D.S \ {t_m})`. -/
theorem hb_m23_node_interlace (D : ShellHBData) (hm : D.S.card = 2 ∨ D.S.card = 3)
    {t : ℕ → ℝ} (ht_anti : StrictAnti t)
    (ht_zeros : ∀ x : ℝ, at47_Nf D.P D.Q x = 0 ↔ ∃ n : ℕ, t n = x) :
    airyZero 1 < t 0 ∧
    (∀ n : ℕ, 1 ≤ n → airyZero (n + 1) < t n ∧ t n < airyZero n) ∧
    airyZero (D.S.card + 1) < t D.S.card ∧
    t D.S.card < airyZero D.S.card ∧
    airyZero D.S.card < airyLambdaSection (airySites (D.S.erase D.tm)) D.S.card := by
  have hm_ge2 : 2 ≤ D.S.card := by rcases hm with h | h <;> omega
  have hm_le3 : D.S.card ≤ 3 := by rcases hm with h | h <;> omega
  have hQ_info : D.Q ≠ 0 ∧ D.S.card = at47_m D.P D.Q := by
    rcases D.m_eq with ⟨_, hc1⟩ | h2
    · omega
    · exact h2
  obtain ⟨hQ_ne, hm_eq⟩ := hQ_info
  have hQ_deg0 : D.Q.natDegree = 0 := by
    have := hm_eq ▸ at47_m_ge_Q D.P D.Q
    omega
  have hP_deg1 : D.P.natDegree ≤ 1 := by
    have := hm_eq ▸ at47_m_ge_P D.P D.Q
    omega
  set q₀ : ℝ := D.Q.coeff 0
  have hQ_eq : D.Q = Polynomial.C q₀ := Polynomial.eq_C_of_natDegree_eq_zero hQ_deg0
  have hq₀_ne : q₀ ≠ 0 := by
    intro h0; apply hQ_ne; rw [hQ_eq, h0, Polynomial.C_0]
  have hQ_eval : ∀ x : ℝ, D.Q.eval x = q₀ := fun x => by rw [hQ_eq, Polynomial.eval_C]
  have hQ_eval_ne : ∀ x : ℝ, D.Q.eval x ≠ 0 := fun x => by rw [hQ_eval]; exact hq₀_ne
  set p₀ : ℝ := D.P.coeff 0
  set p₁ : ℝ := D.P.coeff 1
  have hP_eq : D.P = Polynomial.C p₀ + Polynomial.C p₁ * Polynomial.X := by
    ext k
    rcases k with _ | _ | k
    · simp [p₀]
    · simp [p₁]
    · have hk_gt : D.P.natDegree < k + 2 := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk_gt]
      simp
  have hP_eval : ∀ x : ℝ, D.P.eval x = p₀ + p₁ * x := fun x => by
    rw [hP_eq]; simp
  -- Wronskian `P Q' - Q P' ≥ 0` at `0` gives `-q₀ * p₁ ≥ 0`, hence `p₁ / q₀ ≤ 0`.
  have hp₁_div_nonpos : p₁ / q₀ ≤ 0 := by
    have hW := airyPQHB_wronskian_nonneg D.hHB 0
    have hdQ : (Polynomial.derivative D.Q).eval 0 = 0 := by
      rw [hQ_eq, Polynomial.derivative_C, Polynomial.eval_zero]
    have hdP : (Polynomial.derivative D.P).eval 0 = p₁ := by
      rw [hP_eq]; simp
    rw [hQ_eval 0, hdQ, hdP, mul_zero, zero_sub] at hW
    have hmul_np : p₁ * q₀ ≤ 0 := by linarith only [hW]
    rw [div_eq_mul_inv]
    have hq2_pos : 0 < q₀ ^ 2 := sq_pos_of_ne_zero hq₀_ne
    have hinv_sign : p₁ * q₀⁻¹ = (p₁ * q₀) / q₀ ^ 2 := by field_simp
    rw [hinv_sign]
    exact div_nonpos_of_nonpos_of_nonneg hmul_np hq2_pos.le
  -- Zero of `N` are never zeros of `Ai`.
  have hAi_ne_of_N0 : ∀ x : ℝ, at47_Nf D.P D.Q x = 0 → airyAi x ≠ 0 := by
    intro x hN hAi0
    unfold at47_Nf at hN
    rw [hAi0, mul_zero, zero_add, hQ_eval x] at hN
    exact airyAi_ne_zero_of_deriv_zero ((mul_eq_zero.mp hN).resolve_left hq₀_ne) hAi0
  -- `airyNIdx` is injective on all real zeros of `N` via `airyPQ_injOn_far`.
  have hIdx_inj : ∀ x₁ x₂ : ℝ, at47_Nf D.P D.Q x₁ = 0 → at47_Nf D.P D.Q x₂ = 0 →
      airyNIdx x₁ = airyNIdx x₂ → x₁ = x₂ := by
    intro x₁ x₂ hx₁ hx₂ hidx
    have hN₁ : airyPQN D.P D.Q (x₁ : ℂ) = 0 := by
      rw [airyPQN_ofReal]; exact Complex.ofReal_eq_zero.mpr hx₁
    have hN₂ : airyPQN D.P D.Q (x₂ : ℂ) = 0 := by
      rw [airyPQN_ofReal]; exact Complex.ofReal_eq_zero.mpr hx₂
    exact airyPQ_injOn_far D.hHB (T₀ := -max x₁ x₂)
      (fun u _ => hQ_eval_ne u)
      (by simp) (by simp) hN₁ hN₂ hidx
  -- `airyNIdx` is strictly antitone on all real zeros of `N`.
  have hIdx_anti : ∀ x₁ x₂ : ℝ, at47_Nf D.P D.Q x₁ = 0 → at47_Nf D.P D.Q x₂ = 0 →
      x₁ < x₂ → airyNIdx x₂ < airyNIdx x₁ := by
    intro x₁ x₂ hx₁ hx₂ hlt
    by_contra hnot
    have hle : airyNIdx x₁ ≤ airyNIdx x₂ := not_lt.mp hnot
    rcases hle.eq_or_lt with heq | hlt_idx
    · exact hlt.ne (hIdx_inj x₁ x₂ hx₁ hx₂ heq)
    · have hj1 : 1 ≤ airyNIdx x₂ := by omega
      have h1 := (airyNIdx_gap (hAi_ne_of_N0 x₂ hx₂) hj1).1 le_rfl
      have h2 := (airyNIdx_gap (hAi_ne_of_N0 x₁ hx₁) hj1).2 hlt_idx
      linarith only [hlt, h1, h2]
  have hN_cont : Continuous (at47_Nf D.P D.Q) := by
    unfold at47_Nf
    have := continuous_airyAi; have := continuous_airyAi'
    have := Polynomial.continuous D.P
    have := Polynomial.continuous D.Q
    fun_prop
  -- Existence of a zero `y` with `airyNIdx y = k` for every `k : ℕ`.
  have hex_idx : ∀ k : ℕ, ∃ y : ℝ, at47_Nf D.P D.Q y = 0 ∧ airyNIdx y = k := by
    intro k
    rcases k with _ | m_idx
    · -- `k = 0`: IVT for `g(x) = at47_Nf D.P D.Q x / q₀` on `[airyZero 1, X]`.
      set a₁ : ℝ := airyZero 1
      set X : ℝ := (|p₀ / q₀| + 1) ^ 2
      have ha₁_neg : a₁ < 0 := airyZero_neg 1
      have hX_pos : 0 < X := by dsimp [X]; positivity
      have ha₁_lt_X : a₁ < X := ha₁_neg.trans hX_pos
      let g : ℝ → ℝ := fun x => at47_Nf D.P D.Q x / q₀
      have hg_cont : Continuous g := hN_cont.div_const q₀
      have hg_a₁ : 0 < g a₁ := by
        dsimp [g, at47_Nf, a₁]
        rw [airyAi_airyZero 1, mul_zero, zero_add, hQ_eval, mul_div_cancel_left₀ _ hq₀_ne]
        exact airyAi'_airyZero_one_pos
      have hg_X : g X < 0 := by
        have hsqrt_X : √X = |p₀ / q₀| + 1 := Real.sqrt_sq (by positivity)
        have hAi_pos : 0 < airyAi X := airyAi_pos hX_pos.le
        have hAi'_le := airyAi'_le_neg_sqrt_mul_airyAi hX_pos.le
        have hrew : g X = (p₀ / q₀ + (p₁ / q₀) * X) * airyAi X + airyAi' X := by
          dsimp [g, at47_Nf]
          rw [hP_eval X, hQ_eval X]
          field_simp
        rw [hrew]
        have hpX_le : p₀ / q₀ + (p₁ / q₀) * X ≤ |p₀ / q₀| := by
          have h1 : p₀ / q₀ ≤ |p₀ / q₀| := le_abs_self _
          have h2 : (p₁ / q₀) * X ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp₁_div_nonpos hX_pos.le
          linarith only [h1, h2]
        have h1 : (p₀ / q₀ + (p₁ / q₀) * X) * airyAi X ≤ |p₀ / q₀| * airyAi X :=
          mul_le_mul_of_nonneg_right hpX_le hAi_pos.le
        rw [hsqrt_X] at hAi'_le
        linarith only [h1, hAi'_le, hAi_pos]
      have h0_mem : (0 : ℝ) ∈ uIcc (g a₁) (g X) := by
        rw [mem_uIcc]; right; exact ⟨hg_X.le, hg_a₁.le⟩
      obtain ⟨y, hy_mem, hy0⟩ := intermediate_value_uIcc hg_cont.continuousOn h0_mem
      rw [uIcc_of_le ha₁_lt_X.le] at hy_mem
      have hy_N0 : at47_Nf D.P D.Q y = 0 := by
        dsimp [g] at hy0
        exact (div_eq_zero_iff.mp hy0).resolve_right hq₀_ne
      have hy_gt : a₁ < y := lt_of_le_of_ne hy_mem.1 fun heq => by
        rw [← heq] at hy0; exact hg_a₁.ne' hy0
      have hidx0 : airyNIdx y = 0 := by
        unfold airyNIdx
        exact Nat.le_zero.mp (Nat.find_min' (airyN_exists_idx y) hy_gt)
      exact ⟨y, hy_N0, hidx0⟩
    · -- `k = m_idx + 1 ≥ 1`: IVT on `[airyZero (k + 1), airyZero k]`.
      set k := m_idx + 1
      have hk1 : 1 ≤ k := Nat.succ_le_succ (Nat.zero_le m_idx)
      set a := airyZero (k + 1)
      set b := airyZero k
      have hab : a < b := airyZero_strictAnti hk1
      have hflip := at47_sign_flip (g := airyAi) (g' := airyAi') hasDerivAt_airyAi hab
        (airyAi_airyZero (k + 1)) (airyAi_airyZero k)
        (fun x hx h0 => by
          have := airyZero_next hk1 h0 hx.2
          linarith only [hx.1, this])
        (at47_airyAi'_zero_ne (k + 1)) (at47_airyAi'_zero_ne k)
      have hNa : at47_Nf D.P D.Q a = q₀ * airyAi' a := by
        unfold at47_Nf; rw [airyAi_airyZero (k + 1), hQ_eval a]; ring
      have hNb : at47_Nf D.P D.Q b = q₀ * airyAi' b := by
        unfold at47_Nf; rw [airyAi_airyZero k, hQ_eval b]; ring
      have hNp : at47_Nf D.P D.Q a * at47_Nf D.P D.Q b < 0 := by
        rw [hNa, hNb]
        have hq2 : 0 < q₀ ^ 2 := sq_pos_of_ne_zero hq₀_ne
        have heq : q₀ * airyAi' a * (q₀ * airyAi' b) = q₀ ^ 2 * (airyAi' a * airyAi' b) := by ring
        rw [heq]
        exact mul_neg_of_pos_of_neg hq2 hflip
      have h0_mem : (0 : ℝ) ∈ uIcc (at47_Nf D.P D.Q a) (at47_Nf D.P D.Q b) := by
        rw [mem_uIcc]
        rcases lt_or_gt_of_ne (show at47_Nf D.P D.Q a ≠ 0 from
            fun h => by rw [h, zero_mul] at hNp; exact lt_irrefl 0 hNp) with h1 | h1
        · left; exact ⟨h1.le, by by_contra h2; push Not at h2; nlinarith only [hNp, h1, h2]⟩
        · right; exact ⟨by by_contra h2; push Not at h2; nlinarith only [hNp, h1, h2], h1.le⟩
      obtain ⟨y, hy_mem, hy_N0⟩ := intermediate_value_uIcc hN_cont.continuousOn h0_mem
      rw [uIcc_of_le hab.le] at hy_mem
      have hy_gt_a : a < y := lt_of_le_of_ne hy_mem.1 fun heq => by
        rw [heq, hy_N0, zero_mul] at hNp
        exact lt_irrefl 0 hNp
      have hy_lt_b : y < b := lt_of_le_of_ne hy_mem.2 fun heq => by
        rw [← heq, hy_N0, mul_zero] at hNp
        exact lt_irrefl 0 hNp
      have hidx_le : airyNIdx y ≤ k := by
        unfold airyNIdx
        exact Nat.find_min' (airyN_exists_idx y) hy_gt_a
      have hidx_ge : k ≤ airyNIdx y := by
        by_contra hlt_k
        have hj_lt : airyNIdx y < k := not_le.mp hlt_k
        have hspec := airyNIdx_spec y
        have hle_b : b ≤ airyZero (airyNIdx y + 1) := by
          dsimp [b]
          rcases (Nat.succ_le_of_lt hj_lt).eq_or_lt with heq | hlt2
          · rw [← heq]
          · exact (airyZero_lt_of_lt (by omega) hlt2).le
        linarith only [hy_lt_b, hspec, hle_b]
      exact ⟨y, hy_N0, le_antisymm hidx_le hidx_ge⟩
  -- `n ↦ airyNIdx (t n)` is strictly increasing and surjective onto `ℕ`, hence equal to `id`.
  have ht_N0 : ∀ n : ℕ, at47_Nf D.P D.Q (t n) = 0 := fun n => (ht_zeros (t n)).mpr ⟨n, rfl⟩
  let f : ℕ → ℕ := fun n => airyNIdx (t n)
  have hf_mono : StrictMono f := fun a b hab =>
    hIdx_anti (t b) (t a) (ht_N0 b) (ht_N0 a) (ht_anti hab)
  have hf_surj : Function.Surjective f := by
    intro k
    obtain ⟨y, hy0, hy_idx⟩ := hex_idx k
    obtain ⟨n, rfl⟩ := (ht_zeros y).mp hy0
    exact ⟨n, hy_idx⟩
  have hf_id : ∀ n : ℕ, f n = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      obtain ⟨m, hm_eq_n⟩ := hf_surj n
      rcases lt_trichotomy m n with hmn | rfl | hnm
      · have := ih m hmn
        omega
      · exact hm_eq_n
      · have hle : n ≤ f n := hf_mono.id_le n
        have hlt : f n < f m := hf_mono hnm
        omega
  -- Read off the gap intervals for `t 0` and every `t n` (`n ≥ 1`).
  have ht0_gt : airyZero 1 < t 0 := by
    have h0 := airyNIdx_spec (t 0)
    have hid0 : airyNIdx (t 0) = 0 := hf_id 0
    rwa [hid0] at h0
  have htn_gap : ∀ n : ℕ, 1 ≤ n → airyZero (n + 1) < t n ∧ t n < airyZero n := by
    intro n hn1
    have hidn : airyNIdx (t n) = n := hf_id n
    have h1 : airyZero (n + 1) < t n := by
      have hs := airyNIdx_spec (t n)
      rwa [hidn] at hs
    have h2 : t n < airyZero n := by
      have hg := (airyNIdx_gap (hAi_ne_of_N0 (t n) (ht_N0 n)) hn1).1
      rw [hidn] at hg
      exact hg le_rfl
    exact ⟨h1, h2⟩
  obtain ⟨hcard_lo, hcard_hi⟩ := htn_gap D.S.card (by omega)
  exact ⟨ht0_gt, htn_gap, hcard_lo, hcard_hi, airyLambdaSection_hb_gt_airyZero D hm_ge2⟩

/-- **Lemma `lem:airy-square-bound` (`ce_airy_lp_proofs.tex`, lines 215–224; `ce_airy_lp.tex`,
lines 15, 57–63):**
bundles all clauses of `lem:airy-square-bound`:
1. Reference profile `J_0 ∈ 𝒢` with `J_0 > 0` on `ℝ` and `ℒ_y(J_0) ≍ (1 + y)^{-5/2}` on `y ≥ 0`
   (`lem:al-reference-positive`);
2. Trial-cutoff strict-site witness: for finite `S ⊂ ℝ`, `v ∈ ℝ`, and `M ≥ |S ∩ (v, ∞)| + 1` with
   `v < Λ_M(S ∩ (v, ∞))`, there exists `H` with `IsAiryStrictWitness S v H`;
3. Finite-section and limiting chain: `Λ_M(s) ≤ λ(s)`, `(Λ_M(s) : EReal) ≤ u_sh(s) ≤ u_LP(s) ≤ a_1`
   for `M ≥ k + 1` (`(λ(s) : EReal) ≤ u_sh(s)`), `λ(∅) = a_1`, and the ray-dropped lower bound
   `sup {v : v < λ(S ∩ (v, ∞))} ≤ u_sh(S)`;
4. Hermite–Biehler clauses: for `D : ShellHBData` with `m = D.S.card ≥ 2`,
   `a_m < Λ_m(D.S \ {t_m})`, and for `m ∈ {2, 3}` with strictly decreasing zero enumeration `t` of
   `N = P Ai + Q Ai'`, `a_1 < t_1` and `t_{n+1} ∈ (a_{n+1}, a_n)` (`n ≥ 1`), so
   `a_{m+1} < t_{m+1} < a_m < Λ_m(D.S \ {t_m})`. -/
theorem lem_airy_square_bound :
    (InAiryClass airyRefJ0 ∧ (∀ u : ℝ, 0 < (airyRefJ0 (u : ℂ)).re) ∧
      ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ c₁ ≤ C₁ ∧ ∀ y : ℝ, 0 ≤ y →
        c₁ * (1 + y) ^ (-(5 / 2 : ℝ)) ≤ airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y ∧
        airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y ≤ C₁ * (1 + y) ^ (-(5 / 2 : ℝ))) ∧
    (∀ (S : Finset ℝ) (v : ℝ) (M : ℕ),
      (S.filter (v < ·)).card + 1 ≤ M →
      v < airyLambdaSection (airySites (S.filter (v < ·))) M →
      ∃ H : ℂ → ℂ, IsAiryStrictWitness (S : Set ℝ) v H) ∧
    (∀ (k M : ℕ) (s : Fin k → ℝ), k + 1 ≤ M →
      airyLambdaSection s M ≤ airyLambda s ∧
      (airyLambdaSection s M : EReal) ≤ airyUSh (Set.range s) ∧
      (airyLambda s : EReal) ≤ airyUSh (Set.range s) ∧
      airyUSh (Set.range s) ≤ airyULP (Set.range s) ∧
      airyULP (Set.range s) ≤ (airyZ 0 : EReal)) ∧
    (∀ s : Fin 0 → ℝ, airyLambda s = airyZ 0) ∧
    (∀ S : Finset ℝ,
      (⨆ (v : ℝ) (_ : v < airyLambda (airySites (S.filter (v < ·)))), (v : EReal)) ≤
        airyUSh (S : Set ℝ)) ∧
    (∀ D : ShellHBData, 2 ≤ D.S.card →
      airyZero D.S.card < airyLambdaSection (airySites (D.S.erase D.tm)) D.S.card) ∧
    (∀ (D : ShellHBData), (D.S.card = 2 ∨ D.S.card = 3) →
      ∀ (t : ℕ → ℝ), StrictAnti t →
        (∀ x : ℝ, at47_Nf D.P D.Q x = 0 ↔ ∃ n : ℕ, t n = x) →
        airyZero 1 < t 0 ∧
        (∀ n : ℕ, 1 ≤ n → airyZero (n + 1) < t n ∧ t n < airyZero n) ∧
        airyZero (D.S.card + 1) < t D.S.card ∧
        t D.S.card < airyZero D.S.card ∧
        airyZero D.S.card < airyLambdaSection (airySites (D.S.erase D.tm)) D.S.card) :=
  ⟨⟨airyRefJ0_inAiryClass, airyRefJ0_pos, airyLaplace_airyRefJ0_bounds⟩,
    fun S v _ hM hv => exists_isAiryStrictWitness_of_lt_section_above S v hM hv,
    fun _ _ s hM => ⟨airyLambdaSection_le_airyLambda s hM, airyLambdaSection_le_airyUSh s hM,
      airyLambda_le_airyUSh s, airyUSh_le_airyULP (Set.range s),
      airyULP_le_airyZ_zero (Set.range s)⟩,
    airyLambda_empty_eq,
    airyUSh_ge_rayDropped,
    airyLambdaSection_hb_gt_airyZero,
    fun D hm _ ht hz => hb_m23_node_interlace D hm ht hz⟩

/-- info: 'FormalResearch.SignUncertainty.airyRefJ0_inAiryClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airyRefJ0_inAiryClass

/-- info: 'FormalResearch.SignUncertainty.airyLaplace_airyRefJ0_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airyLaplace_airyRefJ0_bounds

/-- info: 'FormalResearch.SignUncertainty.exists_isAiryStrictWitness_of_lt_section_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.exists_isAiryStrictWitness_of_lt_section_above

/-- info: 'FormalResearch.SignUncertainty.airyLambdaSection_le_airyUSh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airyLambdaSection_le_airyUSh

/-- info: 'FormalResearch.SignUncertainty.airyLambda_le_airyUSh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airyLambda_le_airyUSh

/-- info: 'FormalResearch.SignUncertainty.airyUSh_ge_rayDropped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airyUSh_ge_rayDropped

/-- info: 'FormalResearch.SignUncertainty.airyLambdaSection_hb_gt_airyZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airyLambdaSection_hb_gt_airyZero

/-- info: 'FormalResearch.SignUncertainty.hb_m23_node_interlace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hb_m23_node_interlace

/-- info: 'FormalResearch.SignUncertainty.lem_airy_square_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.lem_airy_square_bound

end FormalResearch.SignUncertainty
