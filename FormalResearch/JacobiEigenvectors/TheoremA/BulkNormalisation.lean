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

/-- On patch `1` the comparison sequence of a ladder chain is the first comparison pair (`cvec 1 = (1,0)`). -/
lemma psiHat_one_eq (D : LadderData) (h : ℝ) (j : ℤ) : D.psiHat h 1 j = D.phi h 0 1 j := by
  unfold LadderData.psiHat Engine.psiHat
  rw [cvec_one]
  simp

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
    rw [ite_eq_left hk, ite_eq_left hk']
    congr 1
    show sNode (F.step N) k * (F.L - sNode (F.step N) k) * F.Gh μ (F.step N) (F.L - sNode (F.step N) k)
      = F.entryE μ N ((N : ℤ) - 1 - k)
    unfold SymbolFamily.entryE
    rw [sNode_mirror F.L (F.step N) N k hL, sub_sub_cancel]
    ring
  · have hk' : ¬ (0 ≤ (N : ℤ) - 1 - k ∧ (N : ℤ) - 1 - k < (N : ℤ)) := by omega
    rw [ite_eq_right hk, ite_eq_right hk']

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
    rw [ite_eq_right (by omega)]
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
      rw [ite_eq_left hn]
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
      rw [ite_eq_right hn]
    rw [hz, abs_zero]
    exact Real.sqrt_nonneg _

/-! ### Overlap counting and sums -/

/-- **Pairs in an interval.**  The number of rows `n` with `c' <= u_n` and `u_{n+1} <= c` is at least `(c - c')/h - 3`, and these rows lie in `0 .. N-1`. -/
theorem count_pairs (h Lr c' c : ℝ) (N : ℕ) (hh : 0 < h) (hN : h * ((N : ℝ) + 1) = Lr) (hc'pos : 0 < c')
    (hcc' : c' < c) (hcL : c + h ≤ Lr) :
    ∃ S : Finset ℤ, (∀ n ∈ S, 0 ≤ n ∧ n + 1 ≤ (N : ℤ) ∧ c' ≤ uNode h n ∧ uNode h (n + 1) ≤ c) ∧
      (c - c') / h - 3 ≤ (S.card : ℝ) := by
  refine ⟨Finset.Icc (⌈c' / h - 1 / 2⌉) (⌊c / h - 3 / 2⌋), ?_, ?_⟩
  · intro n hn
    obtain ⟨hn0, hn1⟩ := Finset.mem_Icc.mp hn
    have hceil : c' / h - 1 / 2 ≤ (n : ℝ) := by
      have := Int.ceil_le.mp hn0
      exact_mod_cast this
    have hfl : (n : ℝ) ≤ c / h - 3 / 2 := by
      have := Int.le_floor.mp hn1
      exact_mod_cast this
    have hu1 : c' ≤ uNode h n := by
      unfold uNode
      have : c' / h ≤ (n : ℝ) + 1 / 2 := by linarith
      rw [div_le_iff₀ hh] at this
      linarith
    have hu2 : uNode h (n + 1) ≤ c := by
      unfold uNode
      push_cast
      have : (n : ℝ) + 1 + 1 / 2 ≤ c / h := by linarith
      rw [le_div_iff₀ hh] at this
      linarith
    have hpos : (-1 : ℝ) < n := by
      have : 0 < uNode h n := lt_of_lt_of_le hc'pos hu1
      unfold uNode at this
      have h2 : 0 < (n : ℝ) + 1 / 2 := by
        by_contra hc
        push Not at hc
        have : ((n : ℝ) + 1 / 2) * h ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hh.le
        linarith
      linarith
    have hn0' : 0 ≤ n := by
      have : (-1 : ℤ) < n := by exact_mod_cast hpos
      omega
    have hNle : (n : ℝ) + 3 / 2 ≤ (N : ℝ) := by
      have h1 : (n : ℝ) + 3 / 2 ≤ c / h := by linarith
      have h2 : c / h ≤ (N : ℝ) + 1 - 1 := by
        rw [div_le_iff₀ hh]
        nlinarith
      linarith
    have hn1' : n + 1 ≤ (N : ℤ) := by
      have : (n : ℝ) + 1 < (N : ℝ) := by linarith
      have : n + 1 < (N : ℤ) := by exact_mod_cast this
      omega
    exact ⟨hn0', hn1', hu1, hu2⟩
  · have hcard := Int.card_Icc (⌈c' / h - 1 / 2⌉) (⌊c / h - 3 / 2⌋)
    rw [hcard]
    have hz : ((⌊c / h - 3 / 2⌋ + 1 - ⌈c' / h - 1 / 2⌉) : ℤ) ≤ ((⌊c / h - 3 / 2⌋ + 1 - ⌈c' / h - 1 / 2⌉).toNat : ℤ) :=
      Int.self_le_toNat _
    have hz' : ((⌊c / h - 3 / 2⌋ + 1 - ⌈c' / h - 1 / 2⌉ : ℤ) : ℝ) ≤ (((⌊c / h - 3 / 2⌋ + 1 - ⌈c' / h - 1 / 2⌉).toNat : ℤ) : ℝ) := by
      exact_mod_cast hz
    have hfl : c / h - 3 / 2 - 1 < (⌊c / h - 3 / 2⌋ : ℝ) := Int.sub_one_lt_floor _
    have hce : ((⌈c' / h - 1 / 2⌉ : ℤ) : ℝ) < c' / h - 1 / 2 + 1 := Int.ceil_lt_add_one _
    have hdiff : (c - c') / h - 3 ≤ ((⌊c / h - 3 / 2⌋ + 1 - ⌈c' / h - 1 / 2⌉ : ℤ) : ℝ) := by
      push_cast
      have : (c - c') / h = c / h - c' / h := by ring
      linarith
    have hcast : (((⌊c / h - 3 / 2⌋ + 1 - ⌈c' / h - 1 / 2⌉).toNat : ℤ) : ℝ) = ((((⌊c / h - 3 / 2⌋ + 1 - ⌈c' / h - 1 / 2⌉).toNat : ℕ) : ℝ)) := by
      norm_cast
    rw [← hcast]
    linarith

/-- **Lower bound of a sum over a window from pairs.**  If each pair `(n, n+1)` of `S` has `|f n| + |f(n+1)| >= c1` and both points lie in the window
`W`, then `|S| c1^2 <= 4 sum_W f^2`. -/
theorem overlap_sum_lower (f : ℤ → ℝ) (W S : Finset ℤ) (c1 : ℝ) (hc1 : 0 ≤ c1)
    (hS : ∀ n ∈ S, n ∈ W ∧ n + 1 ∈ W) (hpair : ∀ n ∈ S, c1 ≤ |f n| + |f (n + 1)|) :
    (S.card : ℝ) * c1 ^ 2 ≤ 4 * ∑ m ∈ W, f m ^ 2 := by
  have hA : ∑ n ∈ S, f (n + 1) ^ 2 ≤ ∑ m ∈ W, f m ^ 2 := by
    have himg : ∑ m ∈ S.image (fun n => n + 1), f m ^ 2 = ∑ n ∈ S, f (n + 1) ^ 2 := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      simpa using hab
    rw [← himg]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
      exact (hS n hn).2
    · intro m _ _
      positivity
  have hB : ∑ n ∈ S, f n ^ 2 ≤ ∑ m ∈ W, f m ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      exact (hS m hm).1
    · intro m _ _
      positivity
  have hpt : ∀ n ∈ S, c1 ^ 2 ≤ 2 * (f n ^ 2 + f (n + 1) ^ 2) := by
    intro n hn
    have h1 := hpair n hn
    have h2 : c1 ^ 2 ≤ (|f n| + |f (n + 1)|) ^ 2 := pow_le_pow_left₀ hc1 h1 2
    have h3 : (|f n| + |f (n + 1)|) ^ 2 ≤ 2 * (f n ^ 2 + f (n + 1) ^ 2) := by
      have e1 : |f n| ^ 2 = f n ^ 2 := sq_abs _
      have e2 : |f (n + 1)| ^ 2 = f (n + 1) ^ 2 := sq_abs _
      nlinarith [sq_nonneg (|f n| - |f (n + 1)|), e1, e2]
    linarith
  have hsum : (S.card : ℝ) * c1 ^ 2 ≤ ∑ n ∈ S, 2 * (f n ^ 2 + f (n + 1) ^ 2) := by
    have := Finset.sum_le_sum hpt
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hexp : ∑ n ∈ S, 2 * (f n ^ 2 + f (n + 1) ^ 2) = 2 * (∑ n ∈ S, f n ^ 2) + 2 * ∑ n ∈ S, f (n + 1) ^ 2 := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  linarith [hsum, hexp, hA, hB]

/-! ### Ladder-level facts on the single patch (`P = 1`, hard-edge seed) -/

/-- The window of patch `1` is `0 .. NR`, and the seed index is `0`. -/
lemma window_one (D : LadderData) (cs : ChainConsts) (h : ℝ) (m : ℕ) (hV : D.Valid cs h m) (hP1 : D.P = 1) :
    (1 : ℕ) ∈ Finset.Icc 1 D.P ∧ D.jj (1 - 1) = 0 ∧ D.jj 1 = D.NR - 1 := by
  refine ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_, ?_⟩
  · have h11 : (1 : ℕ) - 1 = 0 := rfl
    rw [h11]
    exact hV.jj0
  · have := hV.jj_last
    rw [hP1] at this
    exact this

/-- **Envelope bound of the comparison pair on patch 1**: `|psihat^{(alpha)}_j| <= K W_j^{+-1} M_j` on `0 <= j <= NR`. -/
theorem ladder_phi_bound (D : LadderData) (cs : ChainConsts) (h : ℝ) (m : ℕ) (hV : D.Valid cs h m) (hP1 : D.P = 1)
    (j : ℤ) (hj0 : 0 ≤ j) (hjN : j ≤ D.NR) :
    |D.phi h 0 1 j| ≤ (cs.KA + cs.KB) * cs.Kw * D.W j * D.M j ∧
    |D.phi h 1 1 j| ≤ (cs.KA + cs.KB) * cs.Kw * (D.W j)⁻¹ * D.M j := by
  obtain ⟨hp1, hjj0, hjj1⟩ := window_one D cs h m hV hP1
  have hw : j ∈ Finset.Icc (max (D.jj (1 - 1)) 0) (D.jj 1 + 1) := by
    rw [hjj0, hjj1, max_self]
    exact Finset.mem_Icc.mpr ⟨hj0, by omega⟩
  have hWj := hV.W_pos j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩)
  have hMj := hV.M_pos j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩)
  obtain ⟨e0, e1, e2, e3⟩ := hV.env 1 hp1 j hw
  have hA := hV.A_bd 1 hp1 j hw
  have hB := hV.B_bd 1 hp1 j hw
  constructor
  · exact ladder_S2 (D.AA 1) (D.BB 1) (D.wf 1) (1 / 2) h 0 j cs.KA cs.KB cs.Kw (D.W j) (D.M j) (D.ρ j) (D.ρt j)
      cs.Kw_nonneg hWj.le hMj.le (hV.ρ_nonneg j) (hV.ρt_pos j hj0) hA hB e0 e2
  · exact ladder_S2 (D.AA 1) (D.BB 1) (D.wf 1) (1 / 2) h 1 j cs.KA cs.KB cs.Kw (D.W j)⁻¹ (D.M j) (D.ρ j) (D.ρt j)
      cs.Kw_nonneg (inv_nonneg.mpr hWj.le) hMj.le (hV.ρ_nonneg j) (hV.ρt_pos j hj0) hA hB e1 e3

/-- **Casoratian lower bound on the window of patch 1** (`ladder_S1`): `|omega_1(h)| c_- <= |cas(A, psihat^{(0)}, psihat^{(1)})_j|`. -/
theorem ladder_cas_lower (D : LadderData) (cs : ChainConsts) (h : ℝ) (m : ℕ) (hV : D.Valid cs h m) (hP1 : D.P = 1)
    (j : ℤ) (hj0 : 0 ≤ j) (hjN : j ≤ D.NR - 1) :
    cs.cm * |D.ω 1 h| ≤ |cas D.A (D.phi h 0 1) (D.phi h 1 1) j| := by
  obtain ⟨hp1, hjj0, hjj1⟩ := window_one D cs h m hV hP1
  have hw : j ∈ Finset.Icc (max (D.jj (1 - 1)) 0) (D.jj 1 + 1) := by
    rw [hjj0, hjj1, max_self]
    exact Finset.mem_Icc.mpr ⟨hj0, by omega⟩
  have hS0 := ladder_S1 (hV.ladder 1 hp1) (D.AA 1) (D.BB 1) hV.h_pos j hj0 (hV.cas_lb 1 hp1 j hw)
  have hAj : ladderA (D.dd 1) (D.pp 1) (1 / 2) h j = D.A j :=
    hV.A_eq 1 hp1 j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hc := cas_congr_site (f := D.phi h 0 1) (g := D.phi h 1 1) hAj.symm
  rw [hc]
  calc cs.cm * |D.ω 1 h| = |D.ω 1 h| * cs.cm := mul_comm _ _
    _ ≤ _ := hS0

/-- **Pair bound on the overlap**: if the bond is bounded by `CA`, the envelopes of the two rows are `<= Mb` with `W = 1`, then
`c_- |omega| <= CA (K Mb) (|psihat_j| + |psihat_{j+1}|)`. -/
theorem ladder_pair_bound (D : LadderData) (cs : ChainConsts) (h : ℝ) (m : ℕ) (hV : D.Valid cs h m) (hP1 : D.P = 1)
    (j : ℤ) (hj0 : 0 ≤ j) (hjN : j ≤ D.NR - 1) (CA Mb : ℝ) (hA : |D.A j| ≤ CA)
    (hW1 : D.W j = 1) (hW2 : D.W (j + 1) = 1) (hM1 : D.M j ≤ Mb) (hM2 : D.M (j + 1) ≤ Mb) :
    cs.cm * |D.ω 1 h| ≤ CA * ((cs.KA + cs.KB) * cs.Kw * Mb) * (|D.phi h 0 1 j| + |D.phi h 0 1 (j + 1)|) := by
  have hcas := ladder_cas_lower D cs h m hV hP1 j hj0 hjN
  have hK0 : 0 ≤ (cs.KA + cs.KB) * cs.Kw := mul_nonneg (add_nonneg cs.KA_nonneg cs.KB_nonneg) cs.Kw_nonneg
  have hCA0 : 0 ≤ CA := (abs_nonneg _).trans hA
  have hg0 := (ladder_phi_bound D cs h m hV hP1 j hj0 (by omega)).2
  have hg1 := (ladder_phi_bound D cs h m hV hP1 (j + 1) (by omega) (by omega)).2
  rw [hW1, inv_one, mul_one] at hg0
  rw [hW2, inv_one, mul_one] at hg1
  have hgj : |D.phi h 1 1 j| ≤ (cs.KA + cs.KB) * cs.Kw * Mb :=
    hg0.trans (mul_le_mul_of_nonneg_left hM1 hK0)
  have hgj1 : |D.phi h 1 1 (j + 1)| ≤ (cs.KA + cs.KB) * cs.Kw * Mb :=
    hg1.trans (mul_le_mul_of_nonneg_left hM2 hK0)
  have hZ : |D.phi h 0 1 (j + 1) * D.phi h 1 1 j - D.phi h 0 1 j * D.phi h 1 1 (j + 1)|
      ≤ (cs.KA + cs.KB) * cs.Kw * Mb * (|D.phi h 0 1 j| + |D.phi h 0 1 (j + 1)|) := by
    calc _ ≤ |D.phi h 0 1 (j + 1) * D.phi h 1 1 j| + |D.phi h 0 1 j * D.phi h 1 1 (j + 1)| := abs_sub _ _
      _ = |D.phi h 0 1 (j + 1)| * |D.phi h 1 1 j| + |D.phi h 0 1 j| * |D.phi h 1 1 (j + 1)| := by
          rw [abs_mul, abs_mul]
      _ ≤ |D.phi h 0 1 (j + 1)| * ((cs.KA + cs.KB) * cs.Kw * Mb) + |D.phi h 0 1 j| * ((cs.KA + cs.KB) * cs.Kw * Mb) :=
          add_le_add (mul_le_mul_of_nonneg_left hgj (abs_nonneg _)) (mul_le_mul_of_nonneg_left hgj1 (abs_nonneg _))
      _ = (cs.KA + cs.KB) * cs.Kw * Mb * (|D.phi h 0 1 j| + |D.phi h 0 1 (j + 1)|) := by ring
  have hcas' : |cas D.A (D.phi h 0 1) (D.phi h 1 1) j|
      = |D.A j| * |D.phi h 0 1 (j + 1) * D.phi h 1 1 j - D.phi h 0 1 j * D.phi h 1 1 (j + 1)| := by
    unfold cas
    rw [abs_mul]
  calc cs.cm * |D.ω 1 h| ≤ |cas D.A (D.phi h 0 1) (D.phi h 1 1) j| := hcas
    _ = |D.A j| * |D.phi h 0 1 (j + 1) * D.phi h 1 1 j - D.phi h 0 1 j * D.phi h 1 1 (j + 1)| := hcas'
    _ ≤ CA * |D.phi h 0 1 (j + 1) * D.phi h 1 1 j - D.phi h 0 1 j * D.phi h 1 1 (j + 1)| :=
        mul_le_mul_of_nonneg_right hA (abs_nonneg _)
    _ ≤ CA * ((cs.KA + cs.KB) * cs.Kw * Mb * (|D.phi h 0 1 j| + |D.phi h 0 1 (j + 1)|)) :=
        mul_le_mul_of_nonneg_left hZ hCA0
    _ = CA * ((cs.KA + cs.KB) * cs.Kw * Mb) * (|D.phi h 0 1 j| + |D.phi h 0 1 (j + 1)|) := by ring

/-- **Sum of the squared envelopes on patch 1** from the modulus sum: `sum_{k <= NR-1} M_k^2 <= C_sum / sqrt h`. -/
theorem ladder_sum_M_sq (D : LadderData) (cs : ChainConsts) (h : ℝ) (m : ℕ) (hV : D.Valid cs h m) (hP1 : D.P = 1)
    (hs0 : D.s0 = 0) (Csum : ℝ) (hθ : D.theta h ≤ Csum) (hρ1 : ∀ k ∈ Finset.Icc (0 : ℤ) (D.NR - 1), D.ρ k = 1)
    (hω : D.ω 1 h = Real.sqrt h) :
    ∑ k ∈ Finset.Icc (0 : ℤ) (D.NR - 1), D.M k ^ 2 ≤ Csum / Real.sqrt h := by
  have hsq : 0 < Real.sqrt h := Real.sqrt_pos.mpr hV.h_pos
  have hsum : ∑ k ∈ Finset.Icc (0 : ℤ) (D.NR - 1), D.ρ k * D.M k ^ 2 = ∑ k ∈ Finset.Icc (0 : ℤ) (D.NR - 1), D.M k ^ 2 :=
    Finset.sum_congr rfl (fun k hk => by rw [hρ1 k hk, one_mul])
  have hjj1 : D.jj 1 = D.NR - 1 := by
    have := hV.jj_last
    rw [hP1] at this
    exact this
  have hth : D.theta h = h / Real.sqrt h * ∑ k ∈ Finset.Icc (0 : ℤ) (D.NR - 1), D.M k ^ 2 := by
    unfold LadderData.theta volTheta
    rw [hω, abs_of_nonneg hsq.le, hP1, Finset.Icc_self, Finset.sum_singleton, eqLo_one, hs0, hjj1, hsum]
  have hdiv : h / Real.sqrt h = Real.sqrt h := by
    rw [div_eq_iff hsq.ne']
    exact (Real.mul_self_sqrt hV.h_pos.le).symm
  have hθ' := hθ
  rw [hth, hdiv] at hθ'
  rw [le_div_iff₀ hsq]
  calc (∑ k ∈ Finset.Icc (0 : ℤ) (D.NR - 1), D.M k ^ 2) * Real.sqrt h
      = Real.sqrt h * ∑ k ∈ Finset.Icc (0 : ℤ) (D.NR - 1), D.M k ^ 2 := mul_comm _ _
    _ ≤ Csum := hθ'

/-! ### Chart-level facts of one bulk chart, at a fixed `(mu, X, N)` -/

/-- The fourth root of the step, `q = h^{1/4}`, with `q^2 = sqrt h` and `q > 0`. -/
lemma fourth_root_sq (h : ℝ) (hh : 0 < h) : ((h ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt h) ∧ 0 < h ^ ((1 : ℝ) / 4) := by
  refine ⟨?_, Real.rpow_pos_of_pos hh _⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le, Real.sqrt_eq_rpow]
  norm_num

/-- **Chart envelope facts** (on the chart rows `0 .. NR`, patch `1`): the comparison pair is bounded by the envelope, `W <= C_E`,
and the envelope squares are summable: `sum_{0..NR} M^2 <= C_sum / sqrt h + C_M^2 sqrt h`. -/
theorem chart_row_facts {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (p : Par × ℝ) (hp : p ∈ P)
    (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi) (N : ℕ) (hN : C.N0 ≤ N) (hh : 0 < G.step N) (hhc : G.step N ≤ C.c - C.c') :
    (∀ j : ℤ, 0 ≤ j → j ≤ (C.chain p X N).NR → (C.chain p X N).W j ≤ C.cs.CE) ∧
    (∑ j ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, (C.chain p X N).M j ^ 2
      ≤ C.Csum / Real.sqrt (G.step N) + C.CM ^ 2 * Real.sqrt (G.step N)) := by
  obtain ⟨hP1, hs0, hNR0, hNRc, hNRc'⟩ := C.shape p hp X hX N hN
  have hV := C.valid p hp X hX N hN
  have hsqrt : 0 < Real.sqrt (G.step N) := Real.sqrt_pos.mpr hh
  -- the last row lies in the oscillatory overlap
  have hNRov : C.c' ≤ uNode (G.step N) ((C.chain p X N).NR) := by
    have h1 : uNode (G.step N) ((C.chain p X N).NR + 1) = uNode (G.step N) ((C.chain p X N).NR) + G.step N := by
      unfold uNode
      push_cast
      ring
    linarith
  have hWNR : (C.chain p X N).W ((C.chain p X N).NR) = 1 :=
    C.W_osc p hp X hX N hN _ (Finset.mem_Icc.mpr ⟨hNR0, le_rfl⟩) hNRov
  constructor
  · intro j hj0 hjN
    have hm := hV.W_mono j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩) ((C.chain p X N).NR) (Finset.mem_Icc.mpr ⟨hNR0, le_rfl⟩) hjN
    rw [hWNR, mul_one] at hm
    exact hm
  · have hsplit : Finset.Icc (0 : ℤ) (C.chain p X N).NR
        = insert ((C.chain p X N).NR) (Finset.Icc (0 : ℤ) ((C.chain p X N).NR - 1)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : (C.chain p X N).NR ∉ Finset.Icc (0 : ℤ) ((C.chain p X N).NR - 1) := by
      simp only [Finset.mem_Icc, not_and, not_le]
      intro _
      omega
    rw [hsplit, Finset.sum_insert hnot]
    have hθ := C.theta_le p hp X hX N hN
    have hρ1 : ∀ k ∈ Finset.Icc (0 : ℤ) ((C.chain p X N).NR - 1), (C.chain p X N).ρ k = 1 := by
      intro k hk
      have hk' := Finset.mem_Icc.mp hk
      exact (C.rho_one p hp X hX N hN k (Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩)).1
    have hsum := ladder_sum_M_sq (C.chain p X N) C.cs (G.step N) m hV hP1 hs0 C.Csum hθ hρ1
      (C.omega_sqrt p hp X hX N hN)
    -- the last row: `M_NR <= C_M sqrt(sqrt h)`  so `M_NR^2 <= C_M^2 sqrt h`
    have hMNR := C.M_osc p hp X hX N hN _ (Finset.mem_Icc.mpr ⟨hNR0, le_rfl⟩) hNRov
    have hq := fourth_root_sq (G.step N) hh
    have hM2 : (C.chain p X N).M ((C.chain p X N).NR) ^ 2 ≤ C.CM ^ 2 * Real.sqrt (G.step N) := by
      have hMpos : 0 ≤ (C.chain p X N).M ((C.chain p X N).NR) :=
        (hV.M_pos _ (Finset.mem_Icc.mpr ⟨hNR0, le_rfl⟩)).le
      have h2 := pow_le_pow_left₀ hMpos hMNR.2 2
      rw [mul_pow, hq.1] at h2
      exact h2
    linarith [hsum, hM2]


/-- **Chart pair bound on the oscillatory overlap**: for rows `j, j+1` with `c' <= u_j`, `u_{j+1} <= c`,
`c_- sqrt h <= CA (K C_M h^{1/4}) (|psihat_j| + |psihat_{j+1}|)` (`K = (K_A+K_B) K_w`). -/
theorem chart_pair_bound {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (p : Par × ℝ) (hp : p ∈ P)
    (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi) (N : ℕ) (hN : C.N0 ≤ N) (CA : ℝ)
    (hCA : ∀ j : ℤ, 0 ≤ j → j ≤ (C.chain p X N).NR - 1 → |(C.chain p X N).A j| ≤ CA)
    (j : ℤ) (hj0 : 0 ≤ j) (hj1 : j + 1 ≤ (C.chain p X N).NR)
    (hov : C.c' ≤ uNode (G.step N) j ∧ uNode (G.step N) (j + 1) ≤ C.c) :
    C.cs.cm * Real.sqrt (G.step N) ≤
      CA * ((C.cs.KA + C.cs.KB) * C.cs.Kw * C.CM * (G.step N) ^ ((1 : ℝ) / 4))
        * (|(C.chain p X N).phi (G.step N) 0 1 j| + |(C.chain p X N).phi (G.step N) 0 1 (j + 1)|) := by
  obtain ⟨hP1, -, -, -, -⟩ := C.shape p hp X hX N hN
  have hV := C.valid p hp X hX N hN
  have hst : 0 < G.step N := FormalResearch.JB.stepSize_pos G.L_pos N
  have hjN : j ≤ (C.chain p X N).NR - 1 := by omega
  have hW1 : (C.chain p X N).W j = 1 := C.W_osc p hp X hX N hN j (Finset.mem_Icc.mpr ⟨hj0, by omega⟩) hov.1
  have hW2 : (C.chain p X N).W (j + 1) = 1 := C.W_osc p hp X hX N hN (j + 1) (Finset.mem_Icc.mpr ⟨by omega, hj1⟩)
    (le_trans hov.1 (uNode_le_of_le hst.le (by omega)))
  have hM1 := (C.M_osc p hp X hX N hN j (Finset.mem_Icc.mpr ⟨hj0, by omega⟩) hov.1).2
  have hM2 := (C.M_osc p hp X hX N hN (j + 1) (Finset.mem_Icc.mpr ⟨by omega, hj1⟩)
    (le_trans hov.1 (uNode_le_of_le hst.le (by omega)))).2
  have hpb := ladder_pair_bound (C.chain p X N) C.cs (G.step N) m hV hP1 j hj0 hjN CA
    (C.CM * (G.step N) ^ ((1 : ℝ) / 4)) (hCA j hj0 hjN) hW1 hW2 hM1 hM2
  rw [C.omega_sqrt p hp X hX N hN, abs_of_nonneg (Real.sqrt_nonneg _)] at hpb
  calc _ ≤ _ := hpb
    _ = _ := by ring


/-! ### The normalisation algebra (pure real analysis) -/

/-- **Normalisation algebra.**  Given the scale `a` of the left comparison, the ratio `Kt = b/a` of the right one, the sums of the glued vector
(`TL`, `SR`, `SΩr`, `XΩ`), the normalisation identity `1 = NL + NRp` with its errors, and the bounds of the ratio, the glued normaliser
`nn = sqrt(TL + kk^2 SR)` (`kk = XΩ/SΩr`) satisfies `sqrt(cΩ)/q <= nn <= C/q`, `|kk|` is bounded above and below, and `|a nn - 1| <= Ca ε`. -/
theorem normalisation_algebra (q ε a Kt TL SR SΩr XΩ NL NRp cΩ CT Cenv Cκe CKu cK : ℝ)
    (hq : 0 < q) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 < a)
    (hcΩ : 0 < cΩ) (hCT : 0 < CT) (hcK : 0 < cK) (hCenv : 0 < Cenv) (hCκe : 0 ≤ Cκe) (hCKu : 0 ≤ CKu)
    (hNL : 1 = NL + NRp)
    (hNL1 : |NL - a ^ 2 * TL| ≤ a ^ 2 * (Cenv * ε) / q ^ 2)
    (hNR1 : |NRp - (Kt * a) ^ 2 * SR| ≤ (Kt * a) ^ 2 * (Cenv * ε) / q ^ 2)
    (hTL1 : cΩ / q ^ 2 ≤ TL) (hTL3 : TL ≤ CT / q ^ 2) (hSR1 : 0 ≤ SR) (hSR2 : SR ≤ CT / q ^ 2)
    (hSΩr1 : 0 < SΩr) (hκ : |XΩ / SΩr - Kt| ≤ Cκe * ε * (1 + |Kt|))
    (hKt1 : cK ≤ |Kt|) (hKt2 : |Kt| ≤ CKu)
    (hsm1 : (1 + CKu ^ 2) * Cenv * ε ≤ cΩ / 2)
    (hsm2 : Cκe * ε * (1 + CKu) ≤ cK / 2) :
    let kk := XΩ / SΩr
    let nn := Real.sqrt (TL + kk ^ 2 * SR)
    (Real.sqrt cΩ / q ≤ nn ∧ nn ≤ Real.sqrt (CT + (CKu + Cκe * (1 + CKu)) ^ 2 * CT) / q) ∧
    (cK / 2 ≤ |kk| ∧ |kk| ≤ CKu + Cκe * (1 + CKu)) ∧
    |a * nn - 1| ≤ (2 / cΩ) * (Cκe * (1 + CKu) * ((CKu + Cκe * (1 + CKu)) + CKu) * CT + (1 + CKu ^ 2) * Cenv) * ε := by
  intro kk nn
  set CκU : ℝ := CKu + Cκe * (1 + CKu) with hCκU
  have hεKu : Cκe * ε * (1 + |Kt|) ≤ Cκe * (1 + CKu) := by
    have h1 : Cκe * ε * (1 + |Kt|) ≤ Cκe * 1 * (1 + CKu) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hε1 hCκe) (by linarith) (by positivity) (mul_nonneg hCκe zero_le_one)
    linarith
  have hκup : |kk| ≤ CκU := by
    have h1 : |kk - Kt| ≤ Cκe * (1 + CKu) := hκ.trans hεKu
    have h2 : |kk| ≤ |kk - Kt| + |Kt| := by
      have := abs_add_le (kk - Kt) Kt
      simpa using this
    linarith
  have hκlo : cK / 2 ≤ |kk| := by
    have h1 : |Kt| - |kk| ≤ |Kt - kk| := abs_sub_abs_le_abs_sub _ _
    have h2 : |Kt - kk| = |kk - Kt| := abs_sub_comm _ _
    have h3 : Cκe * ε * (1 + |Kt|) ≤ Cκe * ε * (1 + CKu) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hCκe hε)
    linarith
  have hκsq : kk ^ 2 ≤ CκU ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg kk) hκup 2
    rwa [sq_abs] at this
  have hKtsq : Kt ^ 2 ≤ CKu ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg Kt) hKt2 2
    rwa [sq_abs] at this
  -- the error of the normalisation identity
  have herr2 : |(NL - a ^ 2 * TL) + (NRp - (Kt * a) ^ 2 * SR)| ≤ a ^ 2 * (1 + CKu ^ 2) * Cenv * ε / q ^ 2 := by
    have hA : |(NL - a ^ 2 * TL) + (NRp - (Kt * a) ^ 2 * SR)| ≤
        |NL - a ^ 2 * TL| + |NRp - (Kt * a) ^ 2 * SR| := abs_add_le _ _
    have e : a ^ 2 * (Cenv * ε) / q ^ 2 + (Kt * a) ^ 2 * (Cenv * ε) / q ^ 2
        = a ^ 2 * (1 + Kt ^ 2) * Cenv * ε / q ^ 2 := by ring
    have hB : a ^ 2 * (1 + Kt ^ 2) * Cenv * ε / q ^ 2 ≤ a ^ 2 * (1 + CKu ^ 2) * Cenv * ε / q ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : a ^ 2 * (1 + Kt ^ 2) ≤ a ^ 2 * (1 + CKu ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hCenv.le) hε
    linarith [hNL1, hNR1, hA, hB, e]
  have herr : |(NL - a ^ 2 * TL) + (NRp - (Kt * a) ^ 2 * SR)| ≤ a ^ 2 * TL / 2 := by
    refine herr2.trans ?_
    have e : a ^ 2 * (1 + CKu ^ 2) * Cenv * ε / q ^ 2 = a ^ 2 * ((1 + CKu ^ 2) * Cenv * ε) / q ^ 2 := by ring
    rw [e]
    have h2 : a ^ 2 * ((1 + CKu ^ 2) * Cenv * ε) ≤ a ^ 2 * (cΩ / 2) :=
      mul_le_mul_of_nonneg_left hsm1 (by positivity)
    have h3 : a ^ 2 * (cΩ / 2) / q ^ 2 ≤ a ^ 2 * TL / 2 := by
      have e2 : a ^ 2 * (cΩ / 2) / q ^ 2 = a ^ 2 * (cΩ / q ^ 2) / 2 := by ring
      rw [e2]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hTL1 (by positivity)
    exact (div_le_div_of_nonneg_right h2 (by positivity)).trans h3
  -- the identity `1 = a^2 (TL + Kt^2 SR) + err`
  have hid : 1 = a ^ 2 * TL + Kt ^ 2 * a ^ 2 * SR + ((NL - a ^ 2 * TL) + (NRp - (Kt * a) ^ 2 * SR)) := by
    have e : (Kt * a) ^ 2 = Kt ^ 2 * a ^ 2 := by ring
    rw [e]
    linarith
  have hlow2 : a ^ 2 * TL ≤ 2 := by
    have h1 := (abs_le.mp herr).2
    have h2 : 0 ≤ Kt ^ 2 * a ^ 2 * SR := by positivity
    have h1' := (abs_le.mp herr).1
    linarith [h1', h2, hid]
  have ha2 : a ^ 2 ≤ 2 * q ^ 2 / cΩ := by
    have h1 : a ^ 2 * (cΩ / q ^ 2) ≤ a ^ 2 * TL := mul_le_mul_of_nonneg_left hTL1 (by positivity)
    have h2 : a ^ 2 * (cΩ / q ^ 2) ≤ 2 := le_trans h1 hlow2
    have e : a ^ 2 * (cΩ / q ^ 2) * q ^ 2 = a ^ 2 * cΩ := by field_simp
    have h4 : a ^ 2 * cΩ ≤ 2 * q ^ 2 := by
      have := mul_le_mul_of_nonneg_right h2 (sq_nonneg q)
      rw [e] at this
      linarith
    exact (le_div_iff₀ hcΩ).mpr h4
  -- the normaliser
  have hTL0 : 0 ≤ TL := le_trans (by positivity) hTL1
  have hsum_nn : 0 ≤ TL + kk ^ 2 * SR := by
    have : 0 ≤ kk ^ 2 * SR := by positivity
    linarith
  have hnn2 : nn ^ 2 = TL + kk ^ 2 * SR := Real.sq_sqrt hsum_nn
  have hnn_nonneg : 0 ≤ nn := Real.sqrt_nonneg _
  have hq2 : Real.sqrt cΩ / q = Real.sqrt (cΩ / q ^ 2) := by
    rw [Real.sqrt_div hcΩ.le, Real.sqrt_sq hq.le]
  have hnn_lo : Real.sqrt cΩ / q ≤ nn := by
    have h1 : cΩ / q ^ 2 ≤ TL + kk ^ 2 * SR := by
      have : 0 ≤ kk ^ 2 * SR := by positivity
      linarith
    rw [hq2]
    exact Real.sqrt_le_sqrt h1
  have hnn_hi : nn ≤ Real.sqrt (CT + CκU ^ 2 * CT) / q := by
    have hle : TL + kk ^ 2 * SR ≤ (CT + CκU ^ 2 * CT) / q ^ 2 := by
      have h1 : kk ^ 2 * SR ≤ CκU ^ 2 * (CT / q ^ 2) :=
        mul_le_mul hκsq hSR2 hSR1 (by positivity)
      have e : (CT + CκU ^ 2 * CT) / q ^ 2 = CT / q ^ 2 + CκU ^ 2 * (CT / q ^ 2) := by ring
      rw [e]
      linarith
    have e : Real.sqrt (CT + CκU ^ 2 * CT) / q = Real.sqrt ((CT + CκU ^ 2 * CT) / q ^ 2) := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_sq hq.le]
    rw [e]
    exact Real.sqrt_le_sqrt hle
  -- the scale of the normalisation
  have hnn_pos : 0 < nn := lt_of_lt_of_le (div_pos (Real.sqrt_pos.mpr hcΩ) hq) hnn_lo
  have hana : |a * nn - 1| ≤ |a ^ 2 * nn ^ 2 - 1| := by
    have hx : 0 ≤ a * nn := by positivity
    have e : a ^ 2 * nn ^ 2 - 1 = (a * nn - 1) * (a * nn + 1) := by ring
    rw [e, abs_mul]
    have h1 : 1 ≤ |a * nn + 1| := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact le_mul_of_one_le_right (abs_nonneg _) h1
  -- the main error `a^2 nn^2 - 1 = a^2 (kk^2 - Kt^2) SR - err`
  have hmain : a ^ 2 * nn ^ 2 - 1 = a ^ 2 * (kk ^ 2 - Kt ^ 2) * SR - ((NL - a ^ 2 * TL) + (NRp - (Kt * a) ^ 2 * SR)) := by
    rw [hnn2]
    have e : (Kt * a) ^ 2 = Kt ^ 2 * a ^ 2 := by ring
    rw [e] at hid ⊢
    linarith [hid]
  have hkk : |kk ^ 2 - Kt ^ 2| ≤ Cκe * (1 + CKu) * (CκU + CKu) * ε := by
    have e : kk ^ 2 - Kt ^ 2 = (kk - Kt) * (kk + Kt) := by ring
    rw [e, abs_mul]
    have h1 : |kk - Kt| ≤ Cκe * ε * (1 + CKu) :=
      hκ.trans (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hCκe hε))
    have h2 : |kk + Kt| ≤ CκU + CKu := by
      have := abs_add_le kk Kt
      linarith
    have h3 : |kk - Kt| * |kk + Kt| ≤ (Cκe * ε * (1 + CKu)) * (CκU + CKu) :=
      mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    calc |kk - Kt| * |kk + Kt| ≤ (Cκe * ε * (1 + CKu)) * (CκU + CKu) := h3
      _ = Cκe * (1 + CKu) * (CκU + CKu) * ε := by ring
  have hmain2 : |a ^ 2 * nn ^ 2 - 1| ≤ a ^ 2 * (Cκe * (1 + CKu) * (CκU + CKu) * ε) * SR
      + a ^ 2 * (1 + CKu ^ 2) * Cenv * ε / q ^ 2 := by
    rw [hmain]
    refine (abs_sub _ _).trans ?_
    have h1 : |a ^ 2 * (kk ^ 2 - Kt ^ 2) * SR| ≤ a ^ 2 * (Cκe * (1 + CKu) * (CκU + CKu) * ε) * SR := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg a), abs_of_nonneg hSR1]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkk (sq_nonneg a)) hSR1
    linarith [h1, herr2]
  have hfin : a ^ 2 * (Cκe * (1 + CKu) * (CκU + CKu) * ε) * SR + a ^ 2 * (1 + CKu ^ 2) * Cenv * ε / q ^ 2
      ≤ (2 / cΩ) * (Cκe * (1 + CKu) * (CκU + CKu) * CT + (1 + CKu ^ 2) * Cenv) * ε := by
    have hS : a ^ 2 * (Cκe * (1 + CKu) * (CκU + CKu) * ε) * SR ≤ a ^ 2 * (Cκe * (1 + CKu) * (CκU + CKu) * ε) * (CT / q ^ 2) :=
      mul_le_mul_of_nonneg_left hSR2 (by positivity)
    have hfactor : a ^ 2 / q ^ 2 ≤ 2 / cΩ := by
      rw [div_le_div_iff₀ (by positivity) hcΩ]
      exact (le_div_iff₀ hcΩ).mp ha2
    have e1 : a ^ 2 * (Cκe * (1 + CKu) * (CκU + CKu) * ε) * (CT / q ^ 2)
        = (a ^ 2 / q ^ 2) * (Cκe * (1 + CKu) * (CκU + CKu) * CT) * ε := by ring
    have e2 : a ^ 2 * (1 + CKu ^ 2) * Cenv * ε / q ^ 2 = (a ^ 2 / q ^ 2) * ((1 + CKu ^ 2) * Cenv) * ε := by ring
    have hpos : 0 ≤ ε := hε
    have hC : 0 ≤ Cκe * (1 + CKu) * (CκU + CKu) * CT + (1 + CKu ^ 2) * Cenv := by positivity
    have key : (a ^ 2 / q ^ 2) * (Cκe * (1 + CKu) * (CκU + CKu) * CT + (1 + CKu ^ 2) * Cenv) * ε
        ≤ (2 / cΩ) * (Cκe * (1 + CKu) * (CκU + CKu) * CT + (1 + CKu ^ 2) * Cenv) * ε := by
      apply mul_le_mul_of_nonneg_right _ hpos
      exact mul_le_mul_of_nonneg_right hfactor hC
    have e3 : (a ^ 2 / q ^ 2) * (Cκe * (1 + CKu) * (CκU + CKu) * CT + (1 + CKu ^ 2) * Cenv) * ε
        = (a ^ 2 / q ^ 2) * (Cκe * (1 + CKu) * (CκU + CKu) * CT) * ε + (a ^ 2 / q ^ 2) * ((1 + CKu ^ 2) * Cenv) * ε := by
      ring
    have hlin : a ^ 2 * (Cκe * (1 + CKu) * (CκU + CKu) * ε) * SR + a ^ 2 * (1 + CKu ^ 2) * Cenv * ε / q ^ 2
        ≤ (a ^ 2 / q ^ 2) * (Cκe * (1 + CKu) * (CκU + CKu) * CT) * ε + (a ^ 2 / q ^ 2) * ((1 + CKu ^ 2) * Cenv) * ε := by
      rw [← e2]
      linarith [hS, e1]
    linarith [hlin, key, e3]
  refine ⟨⟨hnn_lo, hnn_hi⟩, ⟨hκlo, hκup⟩, ?_⟩
  have := hana.trans (hmain2.trans hfin)
  exact this


/-- **Side facts of one bulk chart** (the comparison sequence `psihat` and its envelope `e = W M` at a fixed `(mu, X, N)`), with the
constants of the chart replaced by common (larger, resp. smaller) constants `Kg, CEg, CMg, cmg, Csg, CAg`. -/
theorem chart_side_facts {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (p : Par × ℝ) (hp : p ∈ P)
    (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi) (N : ℕ) (hN : C.N0 ≤ N) (hhc : G.step N ≤ C.c - C.c')
    (Kg CEg CMg cmg Csg CAg : ℝ) (hKg : 0 < Kg) (hCEg : 0 < CEg) (hCMg : 0 < CMg) (hcmg : 0 < cmg) (hCAg : 0 < CAg)
    (hKgC : (C.cs.KA + C.cs.KB) * C.cs.Kw ≤ Kg) (hCEgC : C.cs.CE ≤ CEg) (hCMgC : C.CM ≤ CMg)
    (hcmgC : cmg ≤ C.cs.cm) (hCsgC : C.Csum ≤ Csg)
    (hA : ∀ j : ℤ, 0 ≤ j → j ≤ (C.chain p X N).NR - 1 → |(C.chain p X N).A j| ≤ CAg) :
    (∀ j : ℤ, 0 ≤ j → j ≤ (C.chain p X N).NR → |C.psiHatL p X N j| ≤ Kg * C.envL p X N j) ∧
    (∀ j : ℤ, 0 ≤ j → j ≤ (C.chain p X N).NR → 0 ≤ C.envL p X N j ∧ C.envL p X N j ≤ CEg * (C.chain p X N).M j) ∧
    (∑ j ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, C.envL p X N j ^ 2
      ≤ CEg ^ 2 * (Csg / Real.sqrt (G.step N) + CMg ^ 2 * Real.sqrt (G.step N))) ∧
    (∀ j : ℤ, 0 ≤ j → j ≤ (C.chain p X N).NR → C.c' ≤ uNode (G.step N) j →
      C.envL p X N j ≤ CMg * (G.step N) ^ ((1 : ℝ) / 4)) ∧
    (∀ j : ℤ, 0 ≤ j → j + 1 ≤ (C.chain p X N).NR → C.c' ≤ uNode (G.step N) j →
      uNode (G.step N) (j + 1) ≤ C.c →
      cmg * (G.step N) ^ ((1 : ℝ) / 4) ≤ CAg * Kg * CMg * (|C.psiHatL p X N j| + |C.psiHatL p X N (j + 1)|)) := by
  obtain ⟨hP1, -, -, -, -⟩ := C.shape p hp X hX N hN
  have hV := C.valid p hp X hX N hN
  have hst : 0 < G.step N := FormalResearch.JB.stepSize_pos G.L_pos N
  obtain ⟨hq2, hq⟩ := fourth_root_sq (G.step N) hst
  obtain ⟨-, -, -, -, -, hcM0, hcMCM, -, hCsum0, -⟩ := C.consts_pos
  have hCM0 : 0 ≤ C.CM := le_trans hcM0.le hcMCM
  have hK0 : 0 ≤ (C.cs.KA + C.cs.KB) * C.cs.Kw :=
    mul_nonneg (add_nonneg C.cs.KA_nonneg C.cs.KB_nonneg) C.cs.Kw_nonneg
  have hrow := chart_row_facts C p hp X hX N hN hst hhc
  have hpsi : ∀ j : ℤ, C.psiHatL p X N j = (C.chain p X N).phi (G.step N) 0 1 j := fun j =>
    psiHat_one_eq (C.chain p X N) (G.step N) j
  have hWM : ∀ j : ℤ, 0 ≤ j → j ≤ (C.chain p X N).NR → 0 ≤ C.envL p X N j := by
    intro j hj0 hjN
    have hW := (C.valid p hp X hX N hN).W_pos j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩)
    have hM := (C.valid p hp X hX N hN).M_pos j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩)
    unfold BulkWeberChart.envL
    exact (mul_pos hW hM).le
  have hEle : ∀ j : ℤ, 0 ≤ j → j ≤ (C.chain p X N).NR → C.envL p X N j ≤ CEg * (C.chain p X N).M j := by
    intro j hj0 hjN
    have hW : (C.chain p X N).W j ≤ C.cs.CE := hrow.1 j hj0 hjN
    have hM := (hV.M_pos j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩)).le
    unfold BulkWeberChart.envL
    exact mul_le_mul_of_nonneg_right ((hW.trans hCEgC)) hM
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj0 hjN
    rw [hpsi]
    have h1 := (ladder_phi_bound (C.chain p X N) C.cs (G.step N) m hV hP1 j hj0 hjN).1
    have hen := hWM j hj0 hjN
    have hKe : (C.cs.KA + C.cs.KB) * C.cs.Kw * (C.chain p X N).W j * (C.chain p X N).M j
        ≤ Kg * C.envL p X N j := by
      unfold BulkWeberChart.envL at hen ⊢
      have e1 : (C.cs.KA + C.cs.KB) * C.cs.Kw * (C.chain p X N).W j * (C.chain p X N).M j
          = (C.cs.KA + C.cs.KB) * C.cs.Kw * ((C.chain p X N).W j * (C.chain p X N).M j) := by ring
      have e2 : (C.cs.KA + C.cs.KB) * C.cs.Kw * ((C.chain p X N).W j * (C.chain p X N).M j)
          ≤ Kg * ((C.chain p X N).W j * (C.chain p X N).M j) :=
        mul_le_mul_of_nonneg_right hKgC hen
      rw [e1]
      exact e2
    exact h1.trans hKe
  · intro j hj0 hjN
    exact ⟨hWM j hj0 hjN, hEle j hj0 hjN⟩
  · have hsum1 : ∑ j ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, C.envL p X N j ^ 2
        ≤ ∑ j ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, (CEg * (C.chain p X N).M j) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hj0, hjN⟩ := Finset.mem_Icc.mp hj
      exact pow_le_pow_left₀ (hWM j hj0 hjN) (hEle j hj0 hjN) 2
    have hsum2 : ∑ j ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, (CEg * (C.chain p X N).M j) ^ 2
        = CEg ^ 2 * ∑ j ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, (C.chain p X N).M j ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hM2 : ∑ j ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, (C.chain p X N).M j ^ 2
        ≤ Csg / Real.sqrt (G.step N) + CMg ^ 2 * Real.sqrt (G.step N) := by
      have h1 : C.Csum / Real.sqrt (G.step N) ≤ Csg / Real.sqrt (G.step N) :=
        div_le_div_of_nonneg_right hCsgC (Real.sqrt_nonneg _)
      have h2 : C.CM ^ 2 * Real.sqrt (G.step N) ≤ CMg ^ 2 * Real.sqrt (G.step N) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hCM0 hCMgC 2) (Real.sqrt_nonneg _)
      linarith [hrow.2]
    calc ∑ j ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, C.envL p X N j ^ 2
        ≤ ∑ j ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, (CEg * (C.chain p X N).M j) ^ 2 := hsum1
      _ = CEg ^ 2 * ∑ j ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, (C.chain p X N).M j ^ 2 := hsum2
      _ ≤ CEg ^ 2 * (Csg / Real.sqrt (G.step N) + CMg ^ 2 * Real.sqrt (G.step N)) :=
          mul_le_mul_of_nonneg_left hM2 (sq_nonneg _)
  · intro j hj0 hjN hcj
    have hW1 := C.W_osc p hp X hX N hN j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩) hcj
    have hM := (C.M_osc p hp X hX N hN j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩) hcj).2
    unfold BulkWeberChart.envL
    rw [hW1, one_mul]
    exact hM.trans (mul_le_mul_of_nonneg_right hCMgC hq.le)
  · intro j hj0 hj1 hc1 hc2
    have hpb := chart_pair_bound C p hp X hX N hN CAg hA j hj0 hj1 ⟨hc1, hc2⟩
    rw [← hpsi j, ← hpsi (j + 1)] at hpb
    set q : ℝ := (G.step N) ^ ((1 : ℝ) / 4) with hqdef
    rw [← hq2] at hpb
    have hS0 : 0 ≤ |C.psiHatL p X N j| + |C.psiHatL p X N (j + 1)| := by positivity
    have hKCM : (C.cs.KA + C.cs.KB) * C.cs.Kw * C.CM ≤ Kg * CMg :=
      mul_le_mul hKgC hCMgC hCM0 (le_trans hK0 hKgC)
    have hcm' : cmg * q ^ 2 ≤ C.cs.cm * q ^ 2 := mul_le_mul_of_nonneg_right hcmgC (sq_nonneg q)
    have hmid : CAg * ((C.cs.KA + C.cs.KB) * C.cs.Kw * C.CM * q) * (|C.psiHatL p X N j| + |C.psiHatL p X N (j + 1)|)
        ≤ CAg * (Kg * CMg * q) * (|C.psiHatL p X N j| + |C.psiHatL p X N (j + 1)|) := by
      apply mul_le_mul_of_nonneg_right _ hS0
      apply mul_le_mul_of_nonneg_left _ hCAg.le
      exact mul_le_mul_of_nonneg_right hKCM hq.le
    have h2 : (cmg * q) * q ≤ (CAg * Kg * CMg * (|C.psiHatL p X N j| + |C.psiHatL p X N (j + 1)|)) * q := by
      calc (cmg * q) * q = cmg * q ^ 2 := by ring
        _ ≤ C.cs.cm * q ^ 2 := hcm'
        _ ≤ CAg * ((C.cs.KA + C.cs.KB) * C.cs.Kw * C.CM * q) * (|C.psiHatL p X N j| + |C.psiHatL p X N (j + 1)|) := hpb
        _ ≤ CAg * (Kg * CMg * q) * (|C.psiHatL p X N j| + |C.psiHatL p X N (j + 1)|) := hmid
        _ = (CAg * Kg * CMg * (|C.psiHatL p X N j| + |C.psiHatL p X N (j + 1)|)) * q := by ring
    exact le_of_mul_le_mul_right h2 hq

/-- **Reflection of a row sum**: a sum of a nonnegative function over the rows `n` with `N - n` in `T` is at most the sum over `T`. -/
theorem sum_reflect_le (N : ℕ) (S T : Finset ℤ) (g : ℤ → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hS : ∀ n ∈ S, (N : ℤ) - n ∈ T) (hinj : Set.InjOn (fun n : ℤ => (N : ℤ) - n) S) :
    ∑ n ∈ S, g ((N : ℤ) - n) ≤ ∑ k ∈ T, g k := by
  rw [← Finset.sum_image (f := g) (g := fun n : ℤ => (N : ℤ) - n) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    exact hS n hn
  · intro k _ _
    exact hg k


end FormalResearch.JacobiEigenvectors.TheoremA
