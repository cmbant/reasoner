module

public import FormalResearch.JacobiEigenvectors.Charts.BulkWeber
public import FormalResearch.JacobiEigenvectors.Engine.LadderStability
public import FormalResearch.JacobiEigenvectors.Setting.EigenSystem
public import FormalResearch.JacobiEigenvectors.TheoremA.Comparison

/-!
# Paper J, Layer 2: general lemmas for the bulk normalisation (L2.C2, `PropThaW` conjunct 1)

Source: Paper J `thmA.tex` `prop:tha-W` (2) and `app_thmA.tex` "The bulk: proof of Proposition prop:tha-W", Step 2.  This module collects the
general facts used by the assembly in `TheoremA/BulkProof.lean`; each is stated and proved for a general symbol family.

* `Lop_smul`, `jacSol_smul`, `jacSol_mono`: the recurrence `Lop` is linear and monotone in the number of rows.
* `sNode_mirror`, `bondA_mirror`, `diagQ_mirror`: the bonds and diagonal of the mirror family are those of `F` reflected, `k <-> N - k`.
* `lop_mirror`: a solution of the recurrence of `F` on rows `0..N` is reflected to a solution of the recurrence of `mirrorFamily F`.
* `seed_zero_eq_zero`: a solution of the recurrence with zero seed vanishes on all rows, if the bonds on the rows are nonzero.
* `cas_lower_chart`: the Casoratian lower bound of a chain on its window (`ladder_S1` for patch `1`), which gives nonzero bonds.

No axioms beyond the standard three; no placeholder.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*}

open scoped Matrix

/-! ### uNode and step helpers -/

lemma uNode_le_of_le {h : ℝ} (hh : 0 ≤ h) {a b : ℤ} (hab : a ≤ b) : uNode h a ≤ uNode h b := by
  unfold uNode
  have : (a : ℝ) ≤ b := by exact_mod_cast hab
  nlinarith

lemma uNode_mirror (L h : ℝ) (N : ℕ) (n : ℤ) (hL : h * ((N : ℝ) + 1) = L) :
    uNode h ((N : ℤ) - n) = L - uNode h n := by
  unfold uNode
  push_cast
  linear_combination hL

lemma step_mul_succ {Par : Type*} (F : SymbolFamily Par) (N : ℕ) : F.step N * ((N : ℝ) + 1) = F.L := by
  unfold SymbolFamily.step FormalResearch.JB.stepSize
  exact div_mul_cancel₀ F.L (by positivity)


/-- `Lop` is linear. -/
lemma Lop_smul (A Q f : ℤ → ℝ) (c : ℝ) (j : ℤ) : Lop A Q (fun n => c * f n) j = c * Lop A Q f j := by
  unfold Lop
  ring

/-- Scalar multiples of solutions of the recurrence are solutions. -/
lemma jacSol_smul {F : SymbolFamily Par} {μ : Par} {N : ℕ} {X : ℝ} {NR : ℤ} {f : ℤ → ℝ}
    (hf : JacSol F μ N X NR f) (c : ℝ) : JacSol F μ N X NR (fun n => c * f n) := by
  intro n h0 h1
  rw [Lop_smul, hf n h0 h1, mul_zero]

/-- A solution on rows `0 .. NR-1` is a solution on the shorter range `0 .. NR'-1`. -/
lemma jacSol_mono {F : SymbolFamily Par} {μ : Par} {N : ℕ} {X : ℝ} {NR NR' : ℤ} {f : ℤ → ℝ}
    (hf : JacSol F μ N X NR f) (hle : NR' ≤ NR) : JacSol F μ N X NR' f := by
  intro n h0 h1
  exact hf n h0 (lt_of_lt_of_le h1 hle)

lemma sNode_mirror (L h : ℝ) (N : ℕ) (k : ℤ) (hL : h * ((N : ℝ) + 1) = L) :
    sNode h ((N : ℤ) - 1 - k) = L - sNode h k := by
  unfold sNode
  push_cast
  linear_combination hL

/-- The bonds of the mirror family: `a^{mirror}_k = a_{N-1-k}`. -/
theorem bondA_mirror (F : SymbolFamily Par) (μ : Par) (N : ℕ) (k : ℤ) :
    (mirrorFamily F).bondA μ N k = F.bondA μ N ((N : ℤ) - 1 - k) := by
  have hL : F.step N * ((N : ℝ) + 1) = F.L := step_mul_succ F N
  unfold SymbolFamily.bondA
  by_cases hk : 0 ≤ k ∧ k < (N : ℤ)
  · have hk' : 0 ≤ (N : ℤ) - 1 - k ∧ (N : ℤ) - 1 - k < (N : ℤ) := by omega
    rw [if_pos hk, if_pos hk']
    congr 1
    show sNode (F.step N) k * (F.L - sNode (F.step N) k) * F.Gh μ (F.step N) (F.L - sNode (F.step N) k)
      = F.entryE μ N ((N : ℤ) - 1 - k)
    unfold SymbolFamily.entryE
    rw [sNode_mirror F.L (F.step N) N k hL, sub_sub_cancel]
    ring
  · have hk' : ¬ (0 ≤ (N : ℤ) - 1 - k ∧ (N : ℤ) - 1 - k < (N : ℤ)) := by omega
    rw [if_neg hk, if_neg hk']

/-- The diagonal of the mirror family: `(X - B^{mirror}_k) = (X - B_{N-k})`. -/
theorem diagQ_mirror (F : SymbolFamily Par) (μ : Par) (N : ℕ) (X : ℝ) (k : ℤ) :
    (mirrorFamily F).diagQ μ N X k = F.diagQ μ N X ((N : ℤ) - k) := by
  have hL : F.step N * ((N : ℝ) + 1) = F.L := step_mul_succ F N
  have e := uNode_mirror F.L (F.step N) N k hL
  unfold SymbolFamily.diagQ SymbolFamily.entryB
  show X - F.Bh μ (F.step N) (F.L - uNode (F.step N) k) = X - F.Bh μ (F.step N) (uNode (F.step N) ((N : ℤ) - k))
  rw [e]

/-- **Reflection of a solution**: if `f` solves the recurrence of `F` on the rows `0 .. N`, then `k ↦ f (N - k)` solves the recurrence of
`mirrorFamily F` on the rows `0 .. N`. -/
theorem lop_mirror (F : SymbolFamily Par) (μ : Par) (N : ℕ) (X : ℝ) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 0 ≤ j → j < (N : ℤ) + 1 → Lop (F.bondA μ N) (F.diagQ μ N X) f j = 0)
    (k : ℤ) (hk0 : 0 ≤ k) (hkN : k < (N : ℤ) + 1) :
    Lop ((mirrorFamily F).bondA μ N) ((mirrorFamily F).diagQ μ N X) (fun i => f ((N : ℤ) - i)) k = 0 := by
  have h := hf ((N : ℤ) - k) (by omega) (by omega)
  unfold Lop at h ⊢
  simp only [bondA_mirror, diagQ_mirror]
  have e1 : (N : ℤ) - 1 - k = (N : ℤ) - k - 1 := by ring
  have e2 : (N : ℤ) - 1 - (k - 1) = (N : ℤ) - k := by ring
  have e3 : (N : ℤ) - (k + 1) = (N : ℤ) - k - 1 := by ring
  have e4 : (N : ℤ) - (k - 1) = (N : ℤ) - k + 1 := by ring
  rw [e1, e2, e3, e4]
  linarith [h]

/-- A solution with zero seed and nonzero bonds on rows `0 .. NR-1` vanishes on rows `0 .. NR`. -/
theorem seed_zero_eq_zero {F : SymbolFamily Par} {μ : Par} {N : ℕ} {X : ℝ} {NR : ℤ} {f : ℤ → ℝ}
    (hf : JacSol F μ N X NR f) (hA : ∀ k : ℤ, 0 ≤ k → k < NR → F.bondA μ N k ≠ 0) (h0 : f 0 = 0) :
    ∀ k : ℕ, (k : ℤ) ≤ NR → f k = 0 := by
  have hneg : ∀ n : ℤ, n < 0 → F.bondA μ N n = 0 := by
    intro n hn
    unfold SymbolFamily.bondA
    rw [if_neg (by omega)]
  -- invariant: `f k = 0` and `a_{k-1} f_{k-1} = 0` (automatic for `k = 0`, as `a_{-1} = 0`)
  have key : ∀ k : ℕ, (k : ℤ) ≤ NR → f k = 0 ∧ F.bondA μ N ((k : ℤ) - 1) * f ((k : ℤ) - 1) = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨by simpa using h0, ?_⟩
      simp [hneg]
    | succ k ih =>
      intro hk
      obtain ⟨hk0, hprev⟩ := ih (by omega)
      have hL := hf (k : ℤ) (by omega) (by omega)
      unfold Lop at hL
      rw [hk0, mul_zero, sub_zero] at hL
      have hAk : F.bondA μ N (k : ℤ) ≠ 0 := hA (k : ℤ) (by omega) (by omega)
      have hsum : F.bondA μ N (k : ℤ) * f ((k : ℤ) + 1) = 0 := by linarith [hL, hprev]
      have hf1 : f ((k : ℤ) + 1) = 0 := (mul_eq_zero.mp hsum).resolve_left hAk
      refine ⟨?_, ?_⟩
      · push_cast
        exact hf1
      · have e : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
        rw [e, hk0, mul_zero]
  exact fun k hk => (key k hk).1

/-! ### Sums over the rows and the orthonormality of an eigen-column -/

/-- A sum over the rows `0 .. N` (as `ℤ`) is the sum over `Fin (N+1)`. -/
theorem sum_rowsOf_eq_fin (N : ℕ) (g : ℤ → ℝ) :
    ∑ n ∈ rowsOf N, g n = ∑ i : Fin (N + 1), g (i.val : ℤ) := by
  refine Finset.sum_bij (fun n hn => (⟨n.toNat, by have := Finset.mem_Icc.mp hn; unfold rowsOf at hn; omega⟩ : Fin (N + 1)))
    ?_ ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_univ _
  · intro a ha b hb hab
    have h1 := Finset.mem_Icc.mp ha
    have h2 := Finset.mem_Icc.mp hb
    have := congrArg Fin.val hab
    simp only at this
    omega
  · intro b _
    refine ⟨(b.val : ℤ), ?_, ?_⟩
    · unfold rowsOf
      exact Finset.mem_Icc.mpr ⟨by positivity, by have := b.isLt; omega⟩
    · ext
      simp
  · intro a ha
    have h1 := Finset.mem_Icc.mp ha
    simp only
    congr 1
    omega

/-- Each column of an orthogonal eigenvector matrix has unit norm over the rows `0 .. N`. -/
theorem eigVec_sq_sum (N : ℕ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hO : Umᵀ * Um = 1) (k : Fin (N + 1)) :
    ∑ n ∈ rowsOf N, eigVec Um k n ^ 2 = 1 := by
  rw [sum_rowsOf_eq_fin]
  have h := congrFun (congrFun hO k) k
  rw [Matrix.mul_apply] at h
  simp only [Matrix.one_apply_eq, Matrix.transpose_apply] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  have hev : eigVec Um k (i.val : ℤ) = Um i k := extV_fin (fun j => Um j k) i
  rw [hev]
  ring

/-! ### The bonds are bounded, by the jets of `EK` on a compact parameter set -/

/-- **Bounded bonds.**  From `(E_K)` on a compact `P`: the bonds `a_n = sqrt E_n` of all `N` and all rows are bounded uniformly. -/
theorem bondA_bound_of_EK [TopologicalSpace Par] (F : SymbolFamily Par) (P : Set Par) (Kidx r : ℕ)
    (hP : IsCompact P) (hEK : EK F P Kidx r) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∀ μ ∈ P, ∀ N : ℕ, ∀ n : ℤ, |F.bondA μ N n| ≤ CA := by
  have hjet : ∀ j ∈ range (Kidx + 1), ∃ B : ℝ, ∀ μ ∈ P, ∀ s ∈ Set.Icc 0 F.L, |F.G (2 * j) μ s| ≤ B := by
    intro j hj
    have hj' : j ≤ Kidx := by
      have := Finset.mem_range.mp hj
      omega
    have hc : ContinuousOn (fun p : Par × ℝ => iteratedDerivWithin 0 (F.G (2 * j) p.1) (Set.Icc 0 F.L) p.2)
        (P ×ˢ Set.Icc 0 F.L) := ((hEK.reg j hj').1.2) 0 (Nat.zero_le _)
    simp only [iteratedDerivWithin_zero] at hc
    obtain ⟨B, hB⟩ := (hP.prod isCompact_Icc).exists_bound_of_continuousOn hc
    refine ⟨B, fun μ hμ s hs => ?_⟩
    have := hB (μ, s) (Set.mk_mem_prod hμ hs)
    simpa [Real.norm_eq_abs] using this
  choose! B hB using hjet
  obtain ⟨Cr, hCr⟩ := hEK.rem
  set Λ : ℝ := max F.L 1 with hΛ
  have hΛ1 : 1 ≤ Λ := le_max_right _ _
  have hΛL : F.L ≤ Λ := le_max_left _ _
  set Bs : ℝ := ∑ j ∈ range (Kidx + 1), |B j| with hBs
  have hBs_nn : 0 ≤ Bs := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  set CG : ℝ := Λ ^ (2 * Kidx + 2) * (Bs + |Cr|) with hCG
  have hCG_nn : 0 ≤ CG := mul_nonneg (pow_nonneg (by linarith) _) (add_nonneg hBs_nn (abs_nonneg _))
  have hGh : ∀ μ ∈ P, ∀ N : ℕ, ∀ s ∈ Set.Icc 0 F.L, |F.Gh μ (F.step N) s| ≤ CG := by
    intro μ hμ N s hs
    have hstep0 : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have hstepL : F.step N ≤ Λ := by
      have : F.step N ≤ F.L := by
        unfold SymbolFamily.step FormalResearch.JB.stepSize
        rw [div_le_iff₀ (by positivity)]
        nlinarith [F.L_pos, (N.cast_nonneg : (0 : ℝ) ≤ N)]
      linarith
    have hrem := (hCr μ hμ N s hs).1
    have hsplit : |F.Gh μ (F.step N) s| ≤
        |F.Gh μ (F.step N) s - ∑ j ∈ range (Kidx + 1), F.step N ^ (2 * j) * F.G (2 * j) μ s|
          + |∑ j ∈ range (Kidx + 1), F.step N ^ (2 * j) * F.G (2 * j) μ s| := by
      have := abs_add_le (F.Gh μ (F.step N) s - ∑ j ∈ range (Kidx + 1), F.step N ^ (2 * j) * F.G (2 * j) μ s)
        (∑ j ∈ range (Kidx + 1), F.step N ^ (2 * j) * F.G (2 * j) μ s)
      rwa [sub_add_cancel] at this
    have hpow : F.step N ^ (2 * Kidx + 2) ≤ Λ ^ (2 * Kidx + 2) := pow_le_pow_left₀ hstep0.le hstepL _
    have hremb : |F.Gh μ (F.step N) s - ∑ j ∈ range (Kidx + 1), F.step N ^ (2 * j) * F.G (2 * j) μ s|
        ≤ |Cr| * Λ ^ (2 * Kidx + 2) := by
      calc _ ≤ Cr * F.step N ^ (2 * Kidx + 2) := hrem
        _ ≤ |Cr * F.step N ^ (2 * Kidx + 2)| := le_abs_self _
        _ = |Cr| * F.step N ^ (2 * Kidx + 2) := by rw [abs_mul, abs_of_nonneg (pow_nonneg hstep0.le _)]
        _ ≤ |Cr| * Λ ^ (2 * Kidx + 2) := mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    have hsum : |∑ j ∈ range (Kidx + 1), F.step N ^ (2 * j) * F.G (2 * j) μ s| ≤ Λ ^ (2 * Kidx + 2) * Bs := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hBs, Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' : j ≤ Kidx := by
        have := Finset.mem_range.mp hj
        omega
      rw [abs_mul, abs_of_nonneg (pow_nonneg hstep0.le _)]
      have hp : F.step N ^ (2 * j) ≤ Λ ^ (2 * Kidx + 2) :=
        calc F.step N ^ (2 * j) ≤ Λ ^ (2 * j) := pow_le_pow_left₀ hstep0.le hstepL _
          _ ≤ Λ ^ (2 * Kidx + 2) := pow_le_pow_right₀ hΛ1 (by omega)
      have hG : |F.G (2 * j) μ s| ≤ |B j| :=
        (hB j (Finset.mem_range.mpr (by omega)) μ hμ s hs).trans (le_abs_self _)
      exact mul_le_mul hp hG (abs_nonneg _) (by positivity)
    calc |F.Gh μ (F.step N) s| ≤ _ := hsplit
      _ ≤ |Cr| * Λ ^ (2 * Kidx + 2) + Λ ^ (2 * Kidx + 2) * Bs := add_le_add hremb hsum
      _ = CG := by rw [hCG]; ring
  refine ⟨Real.sqrt (F.L ^ 2 * CG), Real.sqrt_nonneg _, fun μ hμ N n => ?_⟩
  by_cases hn : 0 ≤ n ∧ n < (N : ℤ)
  · have hbd : F.bondA μ N n = Real.sqrt (F.entryE μ N n) := by
      unfold SymbolFamily.bondA
      rw [if_pos hn]
    rw [hbd, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    unfold SymbolFamily.entryE
    have hL : F.step N * ((N : ℝ) + 1) = F.L := step_mul_succ F N
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hnN : (n : ℝ) + 1 ≤ (N : ℝ) := by
      have : n + 1 ≤ (N : ℤ) := by omega
      exact_mod_cast this
    have hstep0 : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have hs0 : 0 ≤ sNode (F.step N) n := by
      unfold sNode
      positivity
    have hsL : sNode (F.step N) n ≤ F.L := by
      unfold sNode
      nlinarith
    have hG := hGh μ hμ N (sNode (F.step N) n) ⟨hs0, hsL⟩
    have hprod : sNode (F.step N) n * (F.L - sNode (F.step N) n) ≤ F.L ^ 2 := by
      nlinarith
    calc sNode (F.step N) n * (F.L - sNode (F.step N) n) * F.Gh μ (F.step N) (sNode (F.step N) n)
        ≤ |sNode (F.step N) n * (F.L - sNode (F.step N) n) * F.Gh μ (F.step N) (sNode (F.step N) n)| :=
          le_abs_self _
      _ = sNode (F.step N) n * (F.L - sNode (F.step N) n) * |F.Gh μ (F.step N) (sNode (F.step N) n)| := by
          rw [abs_mul, abs_of_nonneg (mul_nonneg hs0 (by linarith))]
      _ ≤ F.L ^ 2 * CG := mul_le_mul hprod hG (abs_nonneg _) (sq_nonneg _)
  · have hz : F.bondA μ N n = 0 := by
      unfold SymbolFamily.bondA
      rw [if_neg hn]
    rw [hz, abs_zero]
    exact Real.sqrt_nonneg _

end FormalResearch.JacobiEigenvectors.TheoremA
