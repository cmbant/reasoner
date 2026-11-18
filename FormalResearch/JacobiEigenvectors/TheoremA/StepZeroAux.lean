module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Setting.JacobiFamily

/-!
# Paper J, Layer 2: auxiliary lemmas for Step 0 (eigenvalue location)

Support module of `TheoremA/StepZero.lean` (plan item L2.C8).  Nothing here is a paper statement; the lemmas are the elementary analytic and compactness facts used there:

* `eig_gershgorin`: for an eigen-system of `F.jacobiMat mu N` every eigenvalue `X_k` satisfies `|X_k - B_i| <= a_i + a_{i-1}` for the site `i` where the eigenvector is largest
  (the numerical-range bound `<v, J v> <= sum (B_n + a_n + a_{n-1}) v_n^2` of app_thmA Step 0, in the form used);
* `sqrt_le_tangent`, `sqrt_le_add`, `second_diff_le`: concavity of `sqrt` (tangent line) and the one-sided second-difference bound (Taylor with second derivative);
* `exists_modulus`: a modulus of continuity uniform over a compact space (no uniform structure on the parameter space is needed).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting

/-! ### Gershgorin bound for an eigenvalue of `J_h` -/

lemma bondA_nonneg {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ) (n : ℤ) : 0 ≤ F.bondA μ N n := by
  unfold SymbolFamily.bondA
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_rfl

lemma sum_ite_unique_le {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (hP : ∀ j j', P j → P j' → j = j') (a : ℝ) (ha : 0 ≤ a) :
    ∑ j : Fin n, (if P j then a else 0) ≤ a := by
  by_cases h : ∃ j, P j
  · obtain ⟨j0, hj0⟩ := h
    rw [Finset.sum_eq_single j0]
    · simp [hj0]
    · intro b _ hb
      have : ¬ P b := fun hh => hb (hP b j0 hh hj0)
      simp [this]
    · simp
  · push Not at h
    apply le_of_eq_of_le (Finset.sum_eq_zero _) ha
    intro j _
    simp [h j]

/-- **Gershgorin bound** (the numerical-range bound of app_thmA Step 0): every eigenvalue `X_k` of an eigen-system of `J_h` is within `a_i + a_{i-1}` of the diagonal
entry `B_i` for some site `i` (the site where the eigenvector is largest). -/
lemma eig_gershgorin {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ)
    {X : Fin (N + 1) → ℝ} {U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hE : IsEigenSystem (F.jacobiMat μ N) X U) (k : Fin (N + 1)) :
    ∃ i : Fin (N + 1), |X k - F.entryB μ N (i : ℤ)| ≤ F.bondA μ N (i : ℤ) + F.bondA μ N ((i : ℤ) - 1) := by
  set v : Fin (N + 1) → ℝ := fun j => U j k with hv
  have heig : ∀ i, ∑ j, F.jacobiMat μ N i j * v j = X k * v i := by
    intro i
    have h1 := congrFun (congrFun hE.eig i) k
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at h1
    simpa [hv, mul_comm] using h1
  have hnorm : ∑ j, v j * v j = 1 := by
    have h1 := congrFun (congrFun hE.orth k) k
    simpa [Matrix.mul_apply, Matrix.transpose_apply, hv] using h1
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => |v j|) ⟨0, Finset.mem_univ _⟩
  have hvi : 0 < |v i| := by
    by_contra hcon
    have h0 : |v i| = 0 := le_antisymm (not_lt.mp hcon) (abs_nonneg _)
    have hall : ∀ j, v j = 0 := fun j => abs_eq_zero.mp (le_antisymm (h0 ▸ hi j (Finset.mem_univ _)) (abs_nonneg _))
    simp [hall] at hnorm
  refine ⟨i, ?_⟩
  have hrow := heig i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hrow
  have hdiag : F.jacobiMat μ N i i = F.entryB μ N (i : ℤ) := by simp [SymbolFamily.jacobiMat]
  rw [hdiag] at hrow
  have hoff : ∀ j ∈ Finset.univ.erase i, |F.jacobiMat μ N i j| ≤
      (if (j : ℕ) = (i : ℕ) + 1 then F.bondA μ N (i : ℤ) else 0) +
        (if (i : ℕ) = (j : ℕ) + 1 then F.bondA μ N ((i : ℤ) - 1) else 0) := by
    intro j hj
    have hji : i ≠ j := fun h => (Finset.ne_of_mem_erase hj) h.symm
    have hA := bondA_nonneg F μ N (i : ℤ)
    have hA' := bondA_nonneg F μ N ((i : ℤ) - 1)
    by_cases h1 : (j : ℕ) = (i : ℕ) + 1
    · have h2 : ¬ (i : ℕ) = (j : ℕ) + 1 := by omega
      have hJ : F.jacobiMat μ N i j = F.bondA μ N (i : ℤ) := by simp [SymbolFamily.jacobiMat, hji, h1]
      rw [hJ, abs_of_nonneg hA, if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : (i : ℕ) = (j : ℕ) + 1
      · have hc : ((j : ℕ) : ℤ) = (i : ℤ) - 1 := by omega
        have hJ : F.jacobiMat μ N i j = F.bondA μ N ((i : ℤ) - 1) := by
          have hJ' : F.jacobiMat μ N i j = F.bondA μ N ((j : ℕ) : ℤ) := by
            simp only [SymbolFamily.jacobiMat, Matrix.of_apply]
            rw [if_neg hji, if_neg h1, if_pos h2]
          rw [hJ', hc]
        rw [hJ, abs_of_nonneg hA', if_neg h1, if_pos h2, zero_add]
      · have hJ : F.jacobiMat μ N i j = 0 := by simp [SymbolFamily.jacobiMat, hji, h1, h2]
        rw [hJ, abs_zero]
        split_ifs <;> linarith
  have hsum : ∑ j ∈ Finset.univ.erase i, |F.jacobiMat μ N i j| ≤ F.bondA μ N (i : ℤ) + F.bondA μ N ((i : ℤ) - 1) := by
    calc _ ≤ ∑ j ∈ Finset.univ.erase i, ((if (j : ℕ) = (i : ℕ) + 1 then F.bondA μ N (i : ℤ) else 0) +
        (if (i : ℕ) = (j : ℕ) + 1 then F.bondA μ N ((i : ℤ) - 1) else 0)) := Finset.sum_le_sum hoff
      _ ≤ ∑ j : Fin (N + 1), ((if (j : ℕ) = (i : ℕ) + 1 then F.bondA μ N (i : ℤ) else 0) +
        (if (i : ℕ) = (j : ℕ) + 1 then F.bondA μ N ((i : ℤ) - 1) else 0)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          intro j _ _
          have hA := bondA_nonneg F μ N (i : ℤ)
          have hA' := bondA_nonneg F μ N ((i : ℤ) - 1)
          split_ifs <;> linarith
      _ ≤ _ := by
          rw [Finset.sum_add_distrib]
          exact add_le_add
            (sum_ite_unique_le (fun j : Fin (N + 1) => (j : ℕ) = (i : ℕ) + 1)
              (fun j j' h h' => Fin.ext (h.trans h'.symm)) _ (bondA_nonneg F μ N _))
            (sum_ite_unique_le (fun j : Fin (N + 1) => (i : ℕ) = (j : ℕ) + 1)
              (fun j j' h h' => Fin.ext (by omega)) _ (bondA_nonneg F μ N _))
  have hbound : |(X k - F.entryB μ N (i : ℤ)) * v i| ≤ (F.bondA μ N (i : ℤ) + F.bondA μ N ((i : ℤ) - 1)) * |v i| := by
    have heq : (X k - F.entryB μ N (i : ℤ)) * v i = ∑ j ∈ Finset.univ.erase i, F.jacobiMat μ N i j * v j := by
      linarith
    rw [heq]
    calc |∑ j ∈ Finset.univ.erase i, F.jacobiMat μ N i j * v j|
        ≤ ∑ j ∈ Finset.univ.erase i, |F.jacobiMat μ N i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.univ.erase i, |F.jacobiMat μ N i j| * |v i| := by
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ _)) (abs_nonneg _)
      _ = (∑ j ∈ Finset.univ.erase i, |F.jacobiMat μ N i j|) * |v i| := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
  rw [abs_mul] at hbound
  exact le_of_mul_le_mul_right hbound hvi

/-! ### Elementary real analysis -/

/-- Concavity of `sqrt`: the tangent line at `y > 0` lies above, `sqrt x <= sqrt y + (x - y)/(2 sqrt y)` for `x >= 0`. -/
lemma sqrt_le_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) : Real.sqrt x ≤ Real.sqrt y + (x - y) / (2 * Real.sqrt y) := by
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hsx := Real.sq_sqrt hx
  have hsy2 := Real.sq_sqrt hy.le
  rw [← sub_nonneg]
  have : Real.sqrt y + (x - y) / (2 * Real.sqrt y) - Real.sqrt x = (Real.sqrt x - Real.sqrt y) ^ 2 / (2 * Real.sqrt y) := by
    field_simp
    nlinarith [hsx, hsy2]
  rw [this]; positivity

/-- `sqrt x <= sqrt y + |x - y|/(2 sqrt y)` for `y > 0`, also for negative `x` (`sqrt x = 0`). -/
lemma sqrt_le_add (x y : ℝ) (hy : 0 < y) : Real.sqrt x ≤ Real.sqrt y + |x - y| / (2 * Real.sqrt y) := by
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have h2 : 0 ≤ |x - y| / (2 * Real.sqrt y) := by positivity
  by_cases hx : 0 ≤ x
  · have key := sqrt_le_tangent hx hy
    have : (x - y) / (2 * Real.sqrt y) ≤ |x - y| / (2 * Real.sqrt y) :=
      div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
    linarith
  · rw [Real.sqrt_eq_zero_of_nonpos (not_le.mp hx).le]
    have := Real.sqrt_nonneg y
    linarith

/-- **One-sided second difference**: if `phi'' <= M` on `[u - d, u + d]`, then `phi(u+d) + phi(u-d) - 2 phi(u) <= M d^2`. -/
lemma second_diff_le (φ φ' φ'' : ℝ → ℝ) (u d M : ℝ) (hd : 0 ≤ d)
    (h1 : ∀ t ∈ Icc (u - d) (u + d), HasDerivAt φ (φ' t) t)
    (h2 : ∀ t ∈ Icc (u - d) (u + d), HasDerivAt φ' (φ'' t) t)
    (hM : ∀ t ∈ Icc (u - d) (u + d), φ'' t ≤ M) :
    φ (u + d) + φ (u - d) - 2 * φ u ≤ M * d ^ 2 := by
  -- g'(t) = φ'(u+t) - φ'(u-t) - 2 M t is antitone-bounded by 0 on [0,d]
  set g' : ℝ → ℝ := fun t => φ' (u + t) - φ' (u - t) - 2 * M * t with hg'
  have hmem : ∀ t ∈ Icc (0 : ℝ) d, u + t ∈ Icc (u - d) (u + d) ∧ u - t ∈ Icc (u - d) (u + d) := by
    intro t ht
    exact ⟨⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩, ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩⟩
  have hg'd : ∀ t ∈ Icc (0 : ℝ) d, HasDerivAt g' (φ'' (u + t) + φ'' (u - t) - 2 * M) t := by
    intro t ht
    have a1 : HasDerivAt (fun t => φ' (u + t)) (φ'' (u + t)) t := by
      exact HasDerivAt.comp_const_add u t (h2 (u + t) (hmem t ht).1)
    have a2 : HasDerivAt (fun t => φ' (u - t)) (-φ'' (u - t)) t := by
      exact HasDerivAt.comp_const_sub u t (h2 (u - t) (hmem t ht).2)
    have a3 : HasDerivAt (fun t : ℝ => 2 * M * t) (2 * M) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * M)
    have := (a1.sub a2).sub a3
    convert this using 1
    ring
  have hg'0 : g' 0 = 0 := by simp [hg']
  have hg'le : ∀ t ∈ Icc (0 : ℝ) d, g' t ≤ 0 := by
    have hanti : AntitoneOn g' (Icc 0 d) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 d)
      · intro t ht; exact (hg'd t ht).continuousAt.continuousWithinAt
      · intro t ht; exact (hg'd t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [(hg'd t (interior_subset ht)).deriv]
        have a := hM _ (hmem t (interior_subset ht)).1
        have b := hM _ (hmem t (interior_subset ht)).2
        linarith
    intro t ht
    have := hanti (show (0 : ℝ) ∈ Icc 0 d from ⟨le_rfl, hd⟩) ht ht.1
    linarith
  set g : ℝ → ℝ := fun t => φ (u + t) + φ (u - t) - 2 * φ u - M * t ^ 2 with hg
  have hgd : ∀ t ∈ Icc (0 : ℝ) d, HasDerivAt g (g' t) t := by
    intro t ht
    have a1 : HasDerivAt (fun t => φ (u + t)) (φ' (u + t)) t := by
      exact HasDerivAt.comp_const_add u t (h1 (u + t) (hmem t ht).1)
    have a2 : HasDerivAt (fun t => φ (u - t)) (-φ' (u - t)) t := by
      exact HasDerivAt.comp_const_sub u t (h1 (u - t) (hmem t ht).2)
    have a3 : HasDerivAt (fun t : ℝ => M * t ^ 2) (M * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul M)
    have := ((a1.add a2).sub_const (2 * φ u)).sub a3
    convert this using 1
    simp only [hg']
    ring
  have hanti : AntitoneOn g (Icc 0 d) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 d)
    · intro t ht; exact (hgd t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hgd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hgd t (interior_subset ht)).deriv]
      exact hg'le t (interior_subset ht)
  have := hanti (show (0 : ℝ) ∈ Icc 0 d from ⟨le_rfl, hd⟩) (show d ∈ Icc 0 d from ⟨hd, le_rfl⟩) hd
  simp only [hg] at this
  simp at this
  linarith

/-- A modulus of continuity uniform over a compact space (no uniform structure needed): if `D < eps` where `phi = 0`, then `D < eps` where `phi < delta`. -/
lemma exists_modulus {X : Type*} [TopologicalSpace X] [CompactSpace X] (D φ : X → ℝ) (hD : Continuous D) (hφ : Continuous φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (ε : ℝ) (h0 : ∀ x, φ x = 0 → D x < ε) :
    ∃ δ > 0, ∀ x, φ x < δ → D x < ε := by
  set Z : Set X := {x | ε ≤ D x} with hZ
  have hZc : IsCompact Z := (isClosed_le continuous_const hD).isCompact
  rcases Z.eq_empty_or_nonempty with hZe | hZne
  · exact ⟨1, one_pos, fun x _ => by
      by_contra hcon
      have : x ∈ Z := not_lt.mp hcon
      rw [hZe] at this; exact this⟩
  · obtain ⟨x0, hx0, hmin⟩ := hZc.exists_isMinOn hZne hφ.continuousOn
    have hpos : 0 < φ x0 := by
      rcases (hφ0 x0).eq_or_lt with h | h
      · exact absurd (h0 x0 h.symm) (not_lt.mpr hx0)
      · exact h
    refine ⟨φ x0, hpos, fun x hx => ?_⟩
    by_contra hcon
    have hxZ : x ∈ Z := not_lt.mp hcon
    have := hmin hxZ
    have h3 : φ x0 ≤ φ x := this
    linarith

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.eig_gershgorin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.eig_gershgorin

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.second_diff_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.second_diff_le

end FormalResearch.JacobiEigenvectors.TheoremA
