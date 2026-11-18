module

public import Mathlib
public import FormalResearch.JB.JBDefs

/-!
# Paper J, Theorem B reduction: Schur multipliers of bounded mixed variation (`lem:thb-schur`, C² form)

Source: Paper J, `/home/user/scratch/paperJ2/thmB.tex`, Lemma `lem:thb-schur`, the smooth case
`ν = ∂_u ∂_X φ du dX` (the only case used by (I2)).

* `jb_schur_of_C2` : for `φ` on the rectangle `[a,b] × [c,d]` with `∂ₜφ = φ₁`, `∂ₓφ₁ = φ₁₂`, `φ₁, φ₁₂`
  continuous on the rectangle and bounds `|φ(u,c)| ≤ S₁`, `|φ(a,X) − φ(a,c)| ≤ S₂`, `|φ₁₂| ≤ S₃`, the
  matrix `(φ(u_n, X_k))` has Schur bound `S₁ + S₂ + (b−a)(d−c) S₃`, for arbitrary finite families
  `u_n ∈ [a,b]`, `X_k ∈ [c,d]`.
* `jb_schur_inv`, `jb_schur_div` : quotients with a denominator bounded below by `c₀ > 0`.

Proof: the double fundamental theorem of calculus turns the mixed difference into a double integral of
`φ₁₂`, which on the finitely many row and column points is a finite cell sum (sorted grid through the
points, `intervalIntegral.sum_integral_adjacent_intervals` twice); then the finite form
`jop_schur_finite` of the Jacobi-operator package applies.

Differences from the plan / paper statement: `φ` and `∂ₓφ` need not be assumed continuous or
differentiable in `jb_schur_of_C2` (only `∂ₜφ`, `∂ₓ∂ₜφ`, continuity of `φ₁`, `φ₁₂`; derivatives are
one-sided at the boundary, `HasDerivWithinAt` on the closed interval).  `jb_schur_inv` needs `∂ₓφ` as
well (for the mixed derivative of `1/φ`).  Not formalised: the measure-theoretic form with a signed
Borel measure `ν` (not used by the C² application); `‖ν‖_TV` as a norm.
-/

@[expose] public section

namespace FormalResearch.JB

open Matrix Set MeasureTheory intervalIntegral
open scoped Matrix.Norms.L2Operator

/-! ### 1. Fundamental theorem on a closed interval, with one-sided derivatives -/

theorem jb_ftc {f f' : ℝ → ℝ} {a b x y : ℝ} (hxy : x ≤ y) (hsub : Icc x y ⊆ Icc a b)
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t)
    (hc : ContinuousOn f' (Icc a b)) : ∫ t in x..y, f' t = f y - f x := by
  have hax : a ≤ x := (hsub (left_mem_Icc.2 hxy)).1
  have hyb : y ≤ b := (hsub (right_mem_Icc.2 hxy)).2
  refine integral_eq_sub_of_hasDeriv_right_of_le hxy
    (fun t ht => (hd t (hsub ht)).continuousWithinAt.mono hsub) (fun t ht => ?_) ?_
  · have : t ∈ Ioo a b := ⟨lt_of_le_of_lt hax ht.1, lt_of_lt_of_le ht.2 hyb⟩
    exact ((hd t (Ioo_subset_Icc_self this)).hasDerivAt (Icc_mem_nhds this.1 this.2)).hasDerivWithinAt
  · exact (hc.mono hsub).intervalIntegrable_of_Icc hxy

/-! ### 2. Sorted grids through finitely many points -/

/-- A monotone grid `p 0 = a ≤ … ≤ p m = b`, strictly increasing on `i < m`, passing through every
point of `V ⊆ [a,b]` (with `a ∈ V`). -/
theorem jb_grid {a b : ℝ} (V : Finset ℝ) (ha : a ∈ V) (hV : ∀ v ∈ V, v ∈ Icc a b) :
    ∃ (m : ℕ) (p : ℕ → ℝ), Monotone p ∧ p 0 = a ∧ p m = b ∧
      (∀ i < m, ∀ j < m, i < j → p i < p j) ∧ (∀ v ∈ V, ∃ j < m, p j = v) := by
  classical
  have hne : V.Nonempty := ⟨a, ha⟩
  have hk : 0 < V.card := Finset.card_pos.2 hne
  set k := V.card with hkdef
  let e := V.orderEmbOfFin rfl
  have hab : a ≤ b := (hV a ha).2
  have heb : ∀ i : Fin k, (e i : ℝ) ≤ b := fun i => (hV _ (V.orderEmbOfFin_mem rfl i)).2
  let p : ℕ → ℝ := fun i => if h : i < k then (e ⟨i, h⟩ : ℝ) else b
  refine ⟨k, p, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hj : j < k
    · have hi : i < k := lt_of_le_of_lt hij hj
      simp only [p, hi, hj, dite_true]
      exact e.monotone (Fin.mk_le_mk.2 hij)
    · by_cases hi : i < k
      · simp only [p, hi, hj, dite_true, dite_false]; exact heb _
      · simp only [p, hi, hj, dite_false]; exact le_rfl
  · have := V.orderEmbOfFin_zero (rfl : V.card = k) hk
    simp only [p, hk, dite_true]
    rw [this]
    exact le_antisymm (Finset.min'_le _ _ ha) (Finset.le_min' _ _ _ fun v hv => (hV v hv).1)
  · simp [p]
  · intro i hi j hj hij
    simp only [p, hi, hj, dite_true]
    exact e.strictMono (Fin.mk_lt_mk.2 hij)
  · intro v hv
    have : v ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; exact hv
    obtain ⟨i, hi⟩ := this
    have hik : (i : ℕ) < k := i.2
    refine ⟨i.1, hik, ?_⟩
    simp only [p, hik, dite_true]
    exact hi

/-! ### 3. Cell decomposition of a double integral -/

theorem jb_cell_sum {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) (p q : ℕ → ℝ) (j j' : ℕ) :
    ∫ t in p 0..p j, ∫ s in q 0..q j', g t s =
      ∑ i ∈ Finset.range j, ∑ l ∈ Finset.range j',
        ∫ t in p i..p (i + 1), ∫ s in q l..q (l + 1), g t s := by
  have hgt : ∀ t, Continuous (g t) := fun t => hg.comp (Continuous.prodMk_right t)
  have hH : ∀ l, Continuous fun t => ∫ s in q l..q (l + 1), g t s := fun l =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg _ _
  have h1 : ∀ t, ∫ s in q 0..q j', g t s = ∑ l ∈ Finset.range j', ∫ s in q l..q (l + 1), g t s :=
    fun t => (sum_integral_adjacent_intervals
      (fun l _ => (hgt t).intervalIntegrable _ _)).symm
  simp_rw [h1]
  rw [intervalIntegral.integral_finsetSum (fun l _ => (hH l).intervalIntegrable _ _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact (sum_integral_adjacent_intervals (fun i _ => (hH l).intervalIntegrable _ _)).symm

/-! ### 4. The smooth case of `lem:thb-schur` -/

/-- Regularity package of `lem:thb-schur` in the smooth case, on the closed rectangle `[a,b] × [c,d]`:
`φ₁ = ∂ₜφ`, `φ₁₂ = ∂ₓφ₁` (one-sided at the boundary), and `φ₁, φ₁₂` jointly continuous. -/
structure MixedC2 (φ φ₁ φ₁₂ : ℝ → ℝ → ℝ) (a b c d : ℝ) : Prop where
  d1 : ∀ s ∈ Icc c d, ∀ t ∈ Icc a b, HasDerivWithinAt (fun t => φ t s) (φ₁ t s) (Icc a b) t
  d12 : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, HasDerivWithinAt (φ₁ t) (φ₁₂ t s) (Icc c d) s
  cont₁ : ContinuousOn (Function.uncurry φ₁) (Icc a b ×ˢ Icc c d)
  cont₁₂ : ContinuousOn (Function.uncurry φ₁₂) (Icc a b ×ˢ Icc c d)

/-- The mixed difference is the double integral of `φ₁₂` (double fundamental theorem of calculus). -/
theorem jb_mixed_identity {φ φ₁ φ₁₂ : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (h : MixedC2 φ φ₁ φ₁₂ a b c d) {u X : ℝ} (hu : u ∈ Icc a b) (hX : X ∈ Icc c d) :
    φ u X - φ u c - φ a X + φ a c = ∫ t in a..u, ∫ s in c..X, φ₁₂ t s := by
  have hau : a ≤ u := hu.1
  have hcX : c ≤ X := hX.1
  have hcd : c ≤ d := hcX.trans hX.2
  have hsubt : Icc a u ⊆ Icc a b := Icc_subset_Icc le_rfl hu.2
  have hsubs : Icc c X ⊆ Icc c d := Icc_subset_Icc le_rfl hX.2
  have hc1 : ∀ s ∈ Icc c d, ContinuousOn (fun t => φ₁ t s) (Icc a b) := fun s hs =>
    h.cont₁.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht, hs⟩)
  have hinner : ∀ t ∈ Icc a b, ∫ s in c..X, φ₁₂ t s = φ₁ t X - φ₁ t c := fun t ht => by
    refine jb_ftc (f := φ₁ t) hcX hsubs (h.d12 t ht) ?_
    exact h.cont₁₂.comp (continuousOn_const.prodMk continuousOn_id) (fun s hs => ⟨ht, hs⟩)
  have hcongr : ∫ t in a..u, ∫ s in c..X, φ₁₂ t s = ∫ t in a..u, (φ₁ t X - φ₁ t c) := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le hau] at ht
    exact hinner t (hsubt ht)
  rw [hcongr]
  have := jb_ftc (f := fun t => φ t X - φ t c) (f' := fun t => φ₁ t X - φ₁ t c) hau hsubt
    (fun t ht => (h.d1 X hX t ht).sub (h.d1 c ⟨le_rfl, hcd⟩ t ht))
    ((hc1 X hX).sub (hc1 c ⟨le_rfl, hcd⟩))
  rw [this]; ring

theorem jb_sum_fin_ite (m j : ℕ) (hj : j ≤ m) (F : ℕ → ℝ) :
    ∑ i : Fin m, F i * (if (i : ℕ) < j then (1 : ℝ) else 0) = ∑ i ∈ Finset.range j, F i := by
  have h1 : ∑ i : Fin m, F i * (if (i : ℕ) < j then (1 : ℝ) else 0) =
      ∑ i ∈ Finset.range m, F i * (if i < j then (1 : ℝ) else 0) :=
    Fin.sum_univ_eq_sum_range (fun i => F i * (if i < j then (1 : ℝ) else 0)) m
  rw [h1]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext i; simp; omega

/-- **Schur multipliers of bounded mixed variation, smooth case** (Paper J `lem:thb-schur`).
For arbitrary finite families `u_n ∈ [a,b]`, `X_k ∈ [c,d]`, the matrix `(φ(u_n, X_k))` has Schur bound
`S₁ + S₂ + (b−a)(d−c) S₃`.  Proved; the measure-theoretic form is not covered. -/
theorem jb_schur_of_C2 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (u : ι → ℝ) (X : κ → ℝ)
    (hu : ∀ n, u n ∈ Icc a b) (hX : ∀ k, X k ∈ Icc c d)
    {φ φ₁ φ₁₂ : ℝ → ℝ → ℝ} (h : MixedC2 φ φ₁ φ₁₂ a b c d) {S₁ S₂ S₃ : ℝ}
    (hS₁ : ∀ t ∈ Icc a b, |φ t c| ≤ S₁) (hS₂ : ∀ s ∈ Icc c d, |φ a s - φ a c| ≤ S₂)
    (hS₃ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |φ₁₂ t s| ≤ S₃) :
    IsSchurBdd (Matrix.of fun n k => φ (u n) (X k)) (S₁ + S₂ + (b - a) * (d - c) * S₃) := by
  classical
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hc : c ∈ Icc c d := ⟨le_rfl, hcd⟩
  have hS₁0 : 0 ≤ S₁ := (abs_nonneg _).trans (hS₁ a ha)
  have hS₂0 : 0 ≤ S₂ := (abs_nonneg _).trans (hS₂ c hc)
  have hS₃0 : 0 ≤ S₃ := (abs_nonneg _).trans (hS₃ a ha c hc)
  -- clamped, globally continuous version of `φ₁₂`
  let ct : ℝ → ℝ := fun t => max a (min b t)
  let cs : ℝ → ℝ := fun s => max c (min d s)
  have hct : ∀ t, ct t ∈ Icc a b := fun t => ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hcs : ∀ s, cs s ∈ Icc c d := fun s => ⟨le_max_left _ _, max_le hcd (min_le_left _ _)⟩
  have hct_eq : ∀ t ∈ Icc a b, ct t = t := fun t ht => by
    simp only [ct]; rw [min_eq_right ht.2, max_eq_right ht.1]
  have hcs_eq : ∀ s ∈ Icc c d, cs s = s := fun s hs => by
    simp only [cs]; rw [min_eq_right hs.2, max_eq_right hs.1]
  let g : ℝ → ℝ → ℝ := fun t s => φ₁₂ (ct t) (cs s)
  have hgc : Continuous (Function.uncurry g) := by
    have hf : Continuous fun x : ℝ × ℝ => (ct x.1, cs x.2) := by fun_prop
    exact h.cont₁₂.comp_continuous hf (fun x => ⟨hct _, hcs _⟩)
  have hgb : ∀ t s, |g t s| ≤ S₃ := fun t s => hS₃ _ (hct t) _ (hcs s)
  -- grids through the points
  obtain ⟨m, p, pmono, p0, pm, pstrict, pmem⟩ := jb_grid (a := a) (b := b)
    (insert a (Finset.univ.image u)) (Finset.mem_insert_self _ _) (by
      intro v hv
      rcases Finset.mem_insert.1 hv with rfl | hv
      · exact ha
      · obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hv; exact hu n)
  obtain ⟨m', q, qmono, q0, qm, qstrict, qmem⟩ := jb_grid (a := c) (b := d)
    (insert c (Finset.univ.image X)) (Finset.mem_insert_self _ _) (by
      intro v hv
      rcases Finset.mem_insert.1 hv with rfl | hv
      · exact hc
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hv; exact hX k)
  choose j hjm hpj using fun n => pmem (u n) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ n)))
  choose j' hjm' hqj using fun k => qmem (X k) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
  let W : ℕ → ℕ → ℝ := fun i l => ∫ t in p i..p (i + 1), ∫ s in q l..q (l + 1), g t s
  let w : Fin m × Fin m' → ℝ := fun z => W z.1 z.2
  have hlt : ∀ n (i : ℕ), i < m → (p i < u n ↔ i < j n) := fun n i hi => by
    rw [← hpj n]
    constructor
    · intro hlt'; by_contra hge; exact absurd (pmono (not_lt.1 hge)) (not_le.2 hlt')
    · intro hij; exact pstrict i hi _ (hjm n) hij
  have hlt' : ∀ k (l : ℕ), l < m' → (q l < X k ↔ l < j' k) := fun k l hl => by
    rw [← hqj k]
    constructor
    · intro hlt'; by_contra hge; exact absurd (qmono (not_lt.1 hge)) (not_le.2 hlt')
    · intro hij; exact qstrict l hl _ (hjm' k) hij
  have hν : ∀ n k, φ (u n) (X k) - φ (u n) c - φ a (X k) + φ a c =
      ∑ z, w z * (if p z.1 < u n then 1 else 0) * (if q z.2 < X k then 1 else 0) := by
    intro n k
    rw [jb_mixed_identity h (hu n) (hX k)]
    have e1 : ∫ t in a..u n, ∫ s in c..X k, φ₁₂ t s = ∫ t in p 0..p (j n), ∫ s in q 0..q (j' k), g t s := by
      rw [p0, q0, hpj n, hqj k]
      refine integral_congr fun t ht => ?_
      rw [uIcc_of_le (hu n).1] at ht
      have htb : t ∈ Icc a b := ⟨ht.1, ht.2.trans (hu n).2⟩
      refine integral_congr fun s hs => ?_
      rw [uIcc_of_le (hX k).1] at hs
      have hsb : s ∈ Icc c d := ⟨hs.1, hs.2.trans (hX k).2⟩
      simp only [g, hct_eq t htb, hcs_eq s hsb]
    rw [e1, jb_cell_sum hgc p q (j n) (j' k)]
    rw [Fintype.sum_prod_type]
    simp only [w]
    have e2 : ∀ i : Fin m, ∑ l : Fin m', W i l * (if p i < u n then (1 : ℝ) else 0) * (if q l < X k then (1 : ℝ) else 0)
        = (if (i : ℕ) < j n then (1 : ℝ) else 0) * ∑ l ∈ Finset.range (j' k), W i l := by
      intro i
      have : (if p i < u n then (1 : ℝ) else 0) = if (i : ℕ) < j n then (1 : ℝ) else 0 := by
        simp only [hlt n i i.2]
      rw [this, ← jb_sum_fin_ite m' (j' k) (hjm' k).le (fun l => W i l), Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hlt' k l l.2]; ring
    simp_rw [e2]
    rw [← jb_sum_fin_ite m (j n) (hjm n).le (fun i => ∑ l ∈ Finset.range (j' k), W i l)]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hfin := FormalResearch.MatrixAnalysis.jop_schur_finite φ a c u X w (fun z => p z.1)
    (fun z => q z.2) hν hS₁0 hS₂0 (fun n => hS₁ _ (hu n)) (fun k => hS₂ _ (hX k))
  -- total variation of the cell weights
  have hw : ∀ z : Fin m × Fin m', |w z| ≤ S₃ * ((p (z.1 + 1) - p z.1) * (q (z.2 + 1) - q z.2)) := by
    intro z
    have hΔp : 0 ≤ p (z.1 + 1) - p z.1 := sub_nonneg.2 (pmono (Nat.le_succ _))
    have hΔq : 0 ≤ q (z.2 + 1) - q z.2 := sub_nonneg.2 (qmono (Nat.le_succ _))
    have hin : ∀ t, ‖∫ s in q z.2..q (z.2 + 1), g t s‖ ≤ S₃ * (q (z.2 + 1) - q z.2) := fun t => by
      have := norm_integral_le_of_norm_le_const (a := q z.2) (b := q (z.2 + 1)) (C := S₃)
        (f := g t) (fun s _ => by simpa using hgb t s)
      rwa [abs_of_nonneg hΔq] at this
    have hout := norm_integral_le_of_norm_le_const (a := p z.1) (b := p (z.1 + 1))
      (C := S₃ * (q (z.2 + 1) - q z.2)) (f := fun t => ∫ s in q z.2..q (z.2 + 1), g t s)
      (fun t _ => hin t)
    rw [abs_of_nonneg hΔp] at hout
    simp only [w, W, Real.norm_eq_abs] at hout ⊢
    nlinarith [hout]
  have hsum : ∑ z, |w z| ≤ (b - a) * (d - c) * S₃ := by
    calc ∑ z, |w z| ≤ ∑ z : Fin m × Fin m', S₃ * ((p (z.1 + 1) - p z.1) * (q (z.2 + 1) - q z.2)) :=
          Finset.sum_le_sum fun z _ => hw z
      _ = S₃ * ((∑ i ∈ Finset.range m, (p (i + 1) - p i)) * (∑ l ∈ Finset.range m', (q (l + 1) - q l))) := by
          rw [← Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_mul_sum]
          congr 1
          rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ l ∈ Finset.range m', (p (i + 1) - p i) * (q (l + 1) - q l)) m]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Fin.sum_univ_eq_sum_range (fun l => (p (i + 1) - p i) * (q (l + 1) - q l)) m']
      _ = (b - a) * (d - c) * S₃ := by
          rw [Finset.sum_range_sub p m, Finset.sum_range_sub q m', pm, p0, qm, q0]; ring
  exact IsSchurBdd.mono ((isSchurBdd_iff_jop _ _).2 hfin) (by linarith)

/-- info: 'FormalResearch.JB.jb_schur_of_C2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JB.jb_schur_of_C2

/-! ### 5. Quotients -/

/-- Full `C²` package on the rectangle (both first partials and the mixed partial `∂ₓ∂ₜφ`). -/
structure FullC2 (φ φ₁ φ₂ φ₁₂ : ℝ → ℝ → ℝ) (a b c d : ℝ) : Prop extends MixedC2 φ φ₁ φ₁₂ a b c d where
  cont : ContinuousOn (Function.uncurry φ) (Icc a b ×ˢ Icc c d)
  d2 : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, HasDerivWithinAt (φ t) (φ₂ t s) (Icc c d) s
  cont₂ : ContinuousOn (Function.uncurry φ₂) (Icc a b ×ˢ Icc c d)

/-- If `φ` is `C²` and `|φ| ≥ c₀ > 0` on the rectangle, then `1/φ` satisfies the `MixedC2` package with
explicit derivatives. -/
theorem jb_inv_mixedC2 {φ φ₁ φ₂ φ₁₂ : ℝ → ℝ → ℝ} {a b c d : ℝ} (h : FullC2 φ φ₁ φ₂ φ₁₂ a b c d)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hφ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, c₀ ≤ |φ t s|) :
    MixedC2 (fun t s => (φ t s)⁻¹) (fun t s => -φ₁ t s * ((φ t s)⁻¹) * (φ t s)⁻¹)
      (fun t s => -φ₁₂ t s * ((φ t s)⁻¹) * (φ t s)⁻¹ +
        2 * φ₁ t s * φ₂ t s * (φ t s)⁻¹ * (φ t s)⁻¹ * (φ t s)⁻¹) a b c d := by
  have hne : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, φ t s ≠ 0 := fun t ht s hs h0 => by
    have := hφ t ht s hs; rw [h0, abs_zero] at this; linarith
  have hcr : ContinuousOn (fun p : ℝ × ℝ => (φ p.1 p.2)⁻¹) (Icc a b ×ˢ Icc c d) :=
    h.cont.inv₀ (fun p hp => hne p.1 hp.1 p.2 hp.2)
  refine ⟨fun s hs t ht => ?_, fun t ht s hs => ?_, ?_, ?_⟩
  · have := ((h.d1 s hs t ht).inv (hne t ht s hs))
    refine this.congr_deriv ?_
    have := hne t ht s hs
    field_simp
  · have hr := (h.d2 t ht s hs).inv (hne t ht s hs)
    have := ((h.d12 t ht s hs).neg.mul hr).mul hr
    refine this.congr_deriv ?_
    have := hne t ht s hs
    simp only [Pi.neg_apply, Pi.mul_apply, Pi.inv_apply]
    field_simp
    ring
  · exact ((h.cont₁.neg.mul hcr).mul hcr)
  · have h2 : ContinuousOn (fun p : ℝ × ℝ => φ₁₂ p.1 p.2) _ := h.cont₁₂
    have h1 : ContinuousOn (fun p : ℝ × ℝ => φ₁ p.1 p.2) _ := h.cont₁
    have h3 : ContinuousOn (fun p : ℝ × ℝ => φ₂ p.1 p.2) _ := h.cont₂
    exact ((h2.neg.mul hcr).mul hcr).add ((((continuousOn_const.mul h1).mul h3).mul hcr).mul hcr |>.mul hcr)

/-- **Schur bound for a reciprocal** (consequence of `lem:thb-schur`): `φ` of class `C²` with
`|φ| ≥ c₀ > 0` on the rectangle, `|∂ₜφ| ≤ M₁`, `|∂ₓφ| ≤ M₂`, `|∂ₓ∂ₜφ| ≤ M₁₂`.  Then `(1/φ(u_n,X_k))` has Schur
bound `3/c₀ + (b−a)(d−c)(M₁₂/c₀² + 2 M₁ M₂/c₀³)`. -/
theorem jb_schur_inv {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (u : ι → ℝ) (X : κ → ℝ)
    (hu : ∀ n, u n ∈ Icc a b) (hX : ∀ k, X k ∈ Icc c d)
    {φ φ₁ φ₂ φ₁₂ : ℝ → ℝ → ℝ} (h : FullC2 φ φ₁ φ₂ φ₁₂ a b c d) {c₀ M₁ M₂ M₁₂ : ℝ} (hc₀ : 0 < c₀)
    (hφ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, c₀ ≤ |φ t s|)
    (hM₁ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |φ₁ t s| ≤ M₁)
    (hM₂ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |φ₂ t s| ≤ M₂)
    (hM₁₂ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |φ₁₂ t s| ≤ M₁₂) :
    IsSchurBdd (Matrix.of fun n k => (φ (u n) (X k))⁻¹)
      (c₀⁻¹ + 2 * c₀⁻¹ + (b - a) * (d - c) *
        (M₁₂ * c₀⁻¹ * c₀⁻¹ + 2 * M₁ * M₂ * c₀⁻¹ * c₀⁻¹ * c₀⁻¹)) := by
  have hx : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |(φ t s)⁻¹| ≤ c₀⁻¹ := fun t ht s hs => by
    rw [abs_inv]; exact inv_anti₀ hc₀ (hφ t ht s hs)
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hc : c ∈ Icc c d := ⟨le_rfl, hcd⟩
  have hM₁0 : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ a ha c hc)
  have hM₂0 : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ a ha c hc)
  have hM₁₂0 : 0 ≤ M₁₂ := (abs_nonneg _).trans (hM₁₂ a ha c hc)
  have hr0 : 0 ≤ c₀⁻¹ := inv_nonneg.2 hc₀.le
  refine jb_schur_of_C2 hab hcd u X hu hX (jb_inv_mixedC2 h hc₀ hφ) (S₁ := c₀⁻¹) (S₂ := 2 * c₀⁻¹)
    (S₃ := M₁₂ * c₀⁻¹ * c₀⁻¹ + 2 * M₁ * M₂ * c₀⁻¹ * c₀⁻¹ * c₀⁻¹) (fun t ht => hx t ht c hc)
    (fun s hs => ?_) (fun t ht s hs => ?_)
  · have h1 := hx a ha s hs
    have h2 := hx a ha c hc
    calc |(φ a s)⁻¹ - (φ a c)⁻¹| ≤ |(φ a s)⁻¹| + |(φ a c)⁻¹| := abs_sub _ _
      _ ≤ 2 * c₀⁻¹ := by linarith
  · have hxx := hx t ht s hs
    have hx0 := abs_nonneg (φ t s)⁻¹
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · simp only [abs_mul, abs_neg]
      have := hM₁₂ t ht s hs
      gcongr
    · simp only [abs_mul, abs_two]
      have := hM₁ t ht s hs
      have := hM₂ t ht s hs
      gcongr

/-- **Schur bound for a quotient** `φ/ψ`: the Schur bounds of `φ` and `1/ψ` multiply
(`IsSchurBdd.hadamard`).  Here `φ` carries the mixed `C²` package (bounds `S₁ S₂ S₃` as in
`jb_schur_of_C2`) and `ψ` the full package with `|ψ| ≥ c₀ > 0` (bounds as in `jb_schur_inv`). -/
theorem jb_schur_div {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (u : ι → ℝ) (X : κ → ℝ)
    (hu : ∀ n, u n ∈ Icc a b) (hX : ∀ k, X k ∈ Icc c d)
    {φ φ₁ φ₁₂ : ℝ → ℝ → ℝ} (h : MixedC2 φ φ₁ φ₁₂ a b c d) {S₁ S₂ S₃ : ℝ}
    (hS₁ : ∀ t ∈ Icc a b, |φ t c| ≤ S₁) (hS₂ : ∀ s ∈ Icc c d, |φ a s - φ a c| ≤ S₂)
    (hS₃ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |φ₁₂ t s| ≤ S₃)
    {ψ ψ₁ ψ₂ ψ₁₂ : ℝ → ℝ → ℝ} (hψ : FullC2 ψ ψ₁ ψ₂ ψ₁₂ a b c d) {c₀ M₁ M₂ M₁₂ : ℝ} (hc₀ : 0 < c₀)
    (hψ0 : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, c₀ ≤ |ψ t s|)
    (hM₁ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |ψ₁ t s| ≤ M₁)
    (hM₂ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |ψ₂ t s| ≤ M₂)
    (hM₁₂ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |ψ₁₂ t s| ≤ M₁₂) :
    IsSchurBdd (Matrix.of fun n k => φ (u n) (X k) / ψ (u n) (X k))
      ((S₁ + S₂ + (b - a) * (d - c) * S₃) *
        (c₀⁻¹ + 2 * c₀⁻¹ + (b - a) * (d - c) *
          (M₁₂ * c₀⁻¹ * c₀⁻¹ + 2 * M₁ * M₂ * c₀⁻¹ * c₀⁻¹ * c₀⁻¹))) := by
  have h1 := jb_schur_of_C2 hab hcd u X hu hX h hS₁ hS₂ hS₃
  have h2 := jb_schur_inv hab hcd u X hu hX hψ hc₀ hψ0 hM₁ hM₂ hM₁₂
  have := h1.hadamard h2
  convert this using 2
  ext n k
  simp [div_eq_mul_inv]

/-- info: 'FormalResearch.JB.jb_schur_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JB.jb_schur_div

/-- info: 'FormalResearch.JB.jb_schur_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JB.jb_schur_inv

/-- Non-vacuity of the hypotheses: `φ(t,s) = t s` on `[0,1]²` is of class `FullC2`, and by
`jb_schur_of_C2` every matrix `(u_n X_k)` with `u_n, X_k ∈ [0,1]` has Schur bound `1` (`S₁ = 0`,
`S₂ = 0`, `S₃ = 1`).  (Numerical evidence only, not proved here: for the cutoff `1_{u_n < X_k}`, which
is not of this class, the Schur norm grows like `log D`; see the remark after eq. (thb-frob) in
Paper J.) -/
theorem jb_fullC2_mul : FullC2 (fun t s => t * s) (fun _ s => s) (fun t _ => t) (fun _ _ => 1)
    0 1 0 1 where
  d1 := fun s _ t _ => by simpa using (hasDerivAt_id t).mul_const s |>.hasDerivWithinAt
  d12 := fun t _ s _ => (hasDerivAt_id' s).hasDerivWithinAt
  cont₁ := by fun_prop
  cont₁₂ := by fun_prop
  cont := by fun_prop
  d2 := fun t _ s _ => by simpa using ((hasDerivAt_id s).const_mul t).hasDerivWithinAt
  cont₂ := by fun_prop

theorem jb_schur_mul_example {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (u : ι → ℝ) (X : κ → ℝ) (hu : ∀ n, u n ∈ Icc (0 : ℝ) 1) (hX : ∀ k, X k ∈ Icc (0 : ℝ) 1) :
    IsSchurBdd (Matrix.of fun n k => u n * X k) 1 := by
  have := jb_schur_of_C2 zero_le_one zero_le_one u X hu hX jb_fullC2_mul.toMixedC2
    (S₁ := 0) (S₂ := 0) (S₃ := 1) (fun t _ => by simp) (fun s _ => by simp)
    (fun t _ s _ => by simp)
  simpa using this

end FormalResearch.JB
