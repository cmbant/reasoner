module

public import FormalResearch.Special.DiscreteJacobiCalculus

/-!
# Discrete Jacobi calculus III: recessive selection, two-solution expansion, Z-matrix comparison

Airy-free abstract lemmas, all **proved** with explicit constants.

* `exists_combination`: any solution `Y` on `Icc lo N` is `κ f1 + μ f2` on `Icc (lo-1) (N+1)` for two solutions
  with `cas a f1 f2 N ≠ 0`; `κ = cas Y f2 / W`, `μ = cas f1 Y / W`.
* `recessive_selection` (abstract form of W1 `lem:recessive`, est:291-299): let `Y = κ f1 + μ f2` at two nodes
  `k0 < k1` (inner and outer), with `|Y k1| ≤ |Y k0|` (monotone decay), `f1` non-increasing in modulus
  (`|f1 k1| ≤ |f1 k0|`, recessive) and `f2` growing by a factor `λ > 1` (`λ|f2 k0| ≤ |f2 k1|`; the paper has
  `Bi` growing by `λ = 3` between the node windows).  Then `|μ| ≤ (2/(λ-1)) |κ| |f1 k0|/|f2 k0|`, i.e.
  `|μ| ≤ |κ| |f1 k0 / f2 k0|` for `λ = 3` (`recessive_selection_three`), and `κ ≠ 0` whenever `Y k0 ≠ 0`
  (`kappa_ne_zero`).  Without the monotonicity of `f1`: `|μ|(λ-1)|f2 k0| ≤ |κ|(|f1 k0| + |f1 k1|)`.
  The *derivation of the monotone decay of `|Y|`* from the margin of the rows is the backward-ratio
  comparison `FormalResearch.Racah.P3.backward_ratio` (Racah/P3JacobiComparison); it is not repeated here.
* `zmatrix_min_principle`, `zmatrix_comparison` (W1 `lem:ec-olver`(ii), EC:95): for the Z-matrix operator
  `zop a c y k = c k y k - a (k+1) y (k+1) - a k y (k-1) = - jac a c y k` with `a > 0` and a positive strict
  supersolution `w` (`zop w > 0`): `|zop e| ≤ K zop w` on the interior and `|e| ≤ K w` at the two ends imply
  `|e| ≤ K w` everywhere.  This is the discrete maximum principle; it is a two-sided inhomogeneous
  comparison, whereas `backward_ratio` is a one-sided ratio bound for solutions of the homogeneous equation
  from a hard edge (both are consequences of the same minimum-of-`y/w` argument; no dependence between them).

**Not formalised:** the weak-supersolution version (`zop w ≥ 0`, which needs `a > 0`-propagation of the
minimum), and any Airy-specific supersolution (`g Ai(x - θ)`).
-/

@[expose] public section

open Finset

namespace FormalResearch.DiscreteAiry

/-- Every solution on `Icc lo N` is a combination `κ f1 + μ f2` of two solutions with nonzero Casoratian. -/
theorem exists_combination (a c f1 f2 Y : ℤ → ℝ) (lo N : ℤ) (hlo : lo ≤ N + 1)
    (hf1 : ∀ k ∈ Icc lo N, jac a c f1 k = 0) (hf2 : ∀ k ∈ Icc lo N, jac a c f2 k = 0)
    (hY : ∀ k ∈ Icc lo N, jac a c Y k = 0) (ha : ∀ k ∈ Icc lo (N + 1), a k ≠ 0)
    (hW : cas a f1 f2 N ≠ 0) :
    ∃ κ μ : ℝ, ∀ k ∈ Icc (lo - 1) (N + 1), Y k = κ * f1 k + μ * f2 k := by
  refine ⟨cas a Y f2 N / cas a f1 f2 N, cas a f1 Y N / cas a f1 f2 N, ?_⟩
  set κ := cas a Y f2 N / cas a f1 f2 N with hκ
  set μ := cas a f1 Y N / cas a f1 f2 N with hμ
  have hN : Y N = κ * f1 N + μ * f2 N ∧ Y (N + 1) = κ * f1 (N + 1) + μ * f2 (N + 1) := by
    have key0 : cas a Y f2 N * f1 N + cas a f1 Y N * f2 N = Y N * cas a f1 f2 N := by
      unfold cas; ring
    have key1 : cas a Y f2 N * f1 (N + 1) + cas a f1 Y N * f2 (N + 1) = Y (N + 1) * cas a f1 f2 N := by
      unfold cas; ring
    constructor
    · rw [hκ, hμ]; field_simp; linarith
    · rw [hκ, hμ]; field_simp; linarith
  clear_value κ μ
  have hd : ∀ k ∈ Icc lo N, jac a c (fun i => Y i - (κ * f1 i + μ * f2 i)) k = 0 := by
    intro k hk
    have e1 := hY k hk; have e2 := hf1 k hk; have e3 := hf2 k hk
    simp only [jac] at e1 e2 e3 ⊢
    linear_combination e1 - κ * e2 - μ * e3
  have hz := eq_zero_of_two_values a c _ lo N N hd ha (by simp only [mem_Icc]; omega)
    (by simp [hN.1]) (by simp [hN.2])
  intro k hk
  have := hz k hk
  simpa [sub_eq_zero] using this

/-- **Recessive selection**, general form: with `Y = κ f1 + μ f2` at the nodes `k0, k1`,
`|Y k1| ≤ |Y k0|` and `λ |f2 k0| ≤ |f2 k1|` (`λ > 1`):
`|μ| (λ - 1) |f2 k0| ≤ |κ| (|f1 k0| + |f1 k1|)`. -/
theorem recessive_selection_general (f1 f2 Y : ℤ → ℝ) (κ μ lam : ℝ) (k0 k1 : ℤ)
    (h0 : Y k0 = κ * f1 k0 + μ * f2 k0) (h1 : Y k1 = κ * f1 k1 + μ * f2 k1)
    (hmono : |Y k1| ≤ |Y k0|) (hgrow : lam * |f2 k0| ≤ |f2 k1|) :
    |μ| * ((lam - 1) * |f2 k0|) ≤ |κ| * (|f1 k0| + |f1 k1|) := by
  have e1 : |μ| * |f2 k1| ≤ |Y k1| + |κ| * |f1 k1| := by
    have : μ * f2 k1 = Y k1 - κ * f1 k1 := by rw [h1]; ring
    rw [← abs_mul, this]
    calc |Y k1 - κ * f1 k1| ≤ |Y k1| + |κ * f1 k1| := abs_sub _ _
      _ = _ := by rw [abs_mul]
  have e0 : |Y k0| ≤ |κ| * |f1 k0| + |μ| * |f2 k0| := by
    rw [h0]; refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
  have := mul_le_mul_of_nonneg_left hgrow (abs_nonneg μ)
  nlinarith

/-- **Recessive selection** (abstract `lem:recessive`, est:291): in addition `|f1 k1| ≤ |f1 k0|` and
`|f2 k0| > 0`, `λ > 1`: `|μ| ≤ (2/(λ-1)) |κ| (|f1 k0|/|f2 k0|)`. -/
theorem recessive_selection (f1 f2 Y : ℤ → ℝ) (κ μ lam : ℝ) (k0 k1 : ℤ)
    (h0 : Y k0 = κ * f1 k0 + μ * f2 k0) (h1 : Y k1 = κ * f1 k1 + μ * f2 k1)
    (hmono : |Y k1| ≤ |Y k0|) (hlam : 1 < lam) (hgrow : lam * |f2 k0| ≤ |f2 k1|)
    (hdec : |f1 k1| ≤ |f1 k0|) (hpos : 0 < |f2 k0|) :
    |μ| ≤ 2 / (lam - 1) * (|κ| * (|f1 k0| / |f2 k0|)) := by
  have h := recessive_selection_general f1 f2 Y κ μ lam k0 k1 h0 h1 hmono hgrow
  have hl : 0 < lam - 1 := by linarith
  have h2 : |μ| * ((lam - 1) * |f2 k0|) ≤ |κ| * (2 * |f1 k0|) := by
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)); linarith
  have hrhs : 2 / (lam - 1) * (|κ| * (|f1 k0| / |f2 k0|)) =
      (|κ| * (2 * |f1 k0|)) / ((lam - 1) * |f2 k0|) := by
    field_simp
  rw [hrhs, le_div_iff₀ (by positivity)]
  exact h2

/-- The paper's constant: growth factor `λ = 3` gives `|μ| ≤ |κ| |f1 k0| / |f2 k0|`. -/
theorem recessive_selection_three (f1 f2 Y : ℤ → ℝ) (κ μ : ℝ) (k0 k1 : ℤ)
    (h0 : Y k0 = κ * f1 k0 + μ * f2 k0) (h1 : Y k1 = κ * f1 k1 + μ * f2 k1)
    (hmono : |Y k1| ≤ |Y k0|) (hgrow : 3 * |f2 k0| ≤ |f2 k1|)
    (hdec : |f1 k1| ≤ |f1 k0|) (hpos : 0 < |f2 k0|) : |μ| ≤ |κ| * (|f1 k0| / |f2 k0|) := by
  have := recessive_selection f1 f2 Y κ μ 3 k0 k1 h0 h1 hmono (by norm_num) hgrow hdec hpos
  norm_num at this
  exact this

/-- `κ ≠ 0` whenever `Y k0 ≠ 0` (the recessive solution carries a nonzero `f1`-component). -/
theorem kappa_ne_zero (f1 f2 Y : ℤ → ℝ) (κ μ lam : ℝ) (k0 k1 : ℤ)
    (h0 : Y k0 = κ * f1 k0 + μ * f2 k0) (h1 : Y k1 = κ * f1 k1 + μ * f2 k1)
    (hmono : |Y k1| ≤ |Y k0|) (hlam : 1 < lam) (hgrow : lam * |f2 k0| ≤ |f2 k1|)
    (hpos : 0 < |f2 k0|) (hY : Y k0 ≠ 0) : κ ≠ 0 := by
  intro hκ
  have h := recessive_selection_general f1 f2 Y κ μ lam k0 k1 h0 h1 hmono hgrow
  rw [hκ] at h
  simp only [abs_zero, zero_mul] at h
  have hμ : μ = 0 := by
    by_contra hμ
    have : 0 < |μ| * ((lam - 1) * |f2 k0|) := by
      have : 0 < |μ| := abs_pos.mpr hμ
      have : 0 < lam - 1 := by linarith
      positivity
    linarith
  apply hY; rw [h0, hκ, hμ]; ring

/-- The Z-matrix row operator `zop a c y k = c k y k - a (k+1) y (k+1) - a k y (k-1) = - jac a c y k`. -/
def zop (a c y : ℤ → ℝ) (k : ℤ) : ℝ := c k * y k - a (k + 1) * y (k + 1) - a k * y (k - 1)

lemma zop_eq_neg_jac (a c y : ℤ → ℝ) (k : ℤ) : zop a c y k = - jac a c y k := by
  simp only [zop, jac]; ring

/-- **Discrete minimum principle** for a Z-matrix with positive supersolution: `a > 0` on `Icc m (N+1)`,
`w > 0` on `Icc (m-1) (N+1)` with `zop w > 0` on `Icc m N`; if `zop u ≥ 0` on `Icc m N` and
`u ≥ 0` at `m-1` and `N+1`, then `u ≥ 0` on `Icc (m-1) (N+1)`. -/
theorem zmatrix_min_principle (a c w u : ℤ → ℝ) (m N : ℤ) (ha : ∀ k ∈ Icc m (N + 1), 0 < a k)
    (hw : ∀ k ∈ Icc (m - 1) (N + 1), 0 < w k) (hLw : ∀ k ∈ Icc m N, 0 < zop a c w k)
    (hLu : ∀ k ∈ Icc m N, 0 ≤ zop a c u k) (h0 : 0 ≤ u (m - 1)) (h1 : 0 ≤ u (N + 1)) :
    ∀ k ∈ Icc (m - 1) (N + 1), 0 ≤ u k := by
  by_contra hcon
  simp only [not_forall, not_le] at hcon
  obtain ⟨k1, hk1, hneg⟩ := hcon
  obtain ⟨ks, hks, hmin⟩ := Finset.exists_min_image (Icc (m - 1) (N + 1)) (fun j => u j / w j)
    ⟨k1, hk1⟩
  have hvneg : u ks / w ks < 0 := by
    refine lt_of_le_of_lt (hmin k1 hk1) ?_
    exact div_neg_of_neg_of_pos hneg (hw k1 hk1)
  have hks' := hks
  rw [mem_Icc] at hks'
  have hint : m ≤ ks ∧ ks ≤ N := by
    constructor
    · by_contra h
      have : ks = m - 1 := by omega
      rw [this] at hvneg
      exact absurd hvneg (not_lt.mpr (div_nonneg h0 (hw (m - 1) (by simp only [mem_Icc]; omega)).le))
    · by_contra h
      have : ks = N + 1 := by omega
      rw [this] at hvneg
      exact absurd hvneg (not_lt.mpr (div_nonneg h1 (hw (N + 1) (by simp only [mem_Icc]; omega)).le))
  set v : ℤ → ℝ := fun j => u j / w j with hv
  have hu : ∀ j ∈ Icc (m - 1) (N + 1), u j = v j * w j := by
    intro j hj
    have := (hw j hj).ne'
    simp only [hv]; field_simp
  have hz : zop a c u ks = v ks * zop a c w ks + a (ks + 1) * w (ks + 1) * (v ks - v (ks + 1))
      + a ks * w (ks - 1) * (v ks - v (ks - 1)) := by
    have e0 := hu (ks - 1) (by simp only [mem_Icc]; omega)
    have e1 := hu ks (by simp only [mem_Icc]; omega)
    have e2 := hu (ks + 1) (by simp only [mem_Icc]; omega)
    simp only [zop]; rw [e0, e1, e2]; ring
  have hp := ha (ks + 1) (by simp only [mem_Icc]; omega)
  have hq := ha ks (by simp only [mem_Icc]; omega)
  have hwp := (hw (ks + 1) (by simp only [mem_Icc]; omega))
  have hwq := (hw (ks - 1) (by simp only [mem_Icc]; omega))
  have m1 : v ks ≤ v (ks + 1) := hmin _ (by simp only [mem_Icc]; omega)
  have m2 : v ks ≤ v (ks - 1) := hmin _ (by simp only [mem_Icc]; omega)
  have t1 : a (ks + 1) * w (ks + 1) * (v ks - v (ks + 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have t2 : a ks * w (ks - 1) * (v ks - v (ks - 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have t3 : v ks * zop a c w ks < 0 := mul_neg_of_neg_of_pos hvneg (hLw ks (by simp only [mem_Icc]; omega))
  have := hLu ks (by simp only [mem_Icc]; omega)
  linarith

/-- **Z-matrix comparison / discrete maximum principle** (W1 `lem:ec-olver`(ii)): `a > 0`, `w > 0`,
`zop w > 0` on the interior, `|zop e k| ≤ K zop w k` for `k ∈ Icc m N` and `|e| ≤ K w` at `m-1`
and `N+1` imply `|e k| ≤ K w k` for all `k ∈ Icc (m-1) (N+1)`. -/
theorem zmatrix_comparison (a c w e : ℤ → ℝ) (m N : ℤ) (K : ℝ) (ha : ∀ k ∈ Icc m (N + 1), 0 < a k)
    (hw : ∀ k ∈ Icc (m - 1) (N + 1), 0 < w k) (hLw : ∀ k ∈ Icc m N, 0 < zop a c w k)
    (hLe : ∀ k ∈ Icc m N, |zop a c e k| ≤ K * zop a c w k)
    (h0 : |e (m - 1)| ≤ K * w (m - 1)) (h1 : |e (N + 1)| ≤ K * w (N + 1)) :
    ∀ k ∈ Icc (m - 1) (N + 1), |e k| ≤ K * w k := by
  have hlin : ∀ (s : ℝ) k, zop a c (fun j => K * w j + s * e j) k = K * zop a c w k + s * zop a c e k := by
    intro s k; simp only [zop]; ring
  have hpos := zmatrix_min_principle a c w (fun j => K * w j + 1 * e j) m N ha hw hLw
    (fun k hk => by
      rw [hlin 1 k]; have := (abs_le.mp (hLe k hk)).1; linarith)
    (by have := (abs_le.mp h0).1; linarith) (by have := (abs_le.mp h1).1; linarith)
  have hneg := zmatrix_min_principle a c w (fun j => K * w j + (-1) * e j) m N ha hw hLw
    (fun k hk => by
      rw [hlin (-1) k]; have := (abs_le.mp (hLe k hk)).2; linarith)
    (by have := (abs_le.mp h0).2; linarith) (by have := (abs_le.mp h1).2; linarith)
  intro k hk
  rw [abs_le]
  have := hpos k hk; have := hneg k hk
  constructor <;> linarith

/-- info: 'FormalResearch.DiscreteAiry.exists_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.exists_combination

/-- info: 'FormalResearch.DiscreteAiry.recessive_selection_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.recessive_selection_general

/-- info: 'FormalResearch.DiscreteAiry.recessive_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.recessive_selection

/-- info: 'FormalResearch.DiscreteAiry.recessive_selection_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.recessive_selection_three

/-- info: 'FormalResearch.DiscreteAiry.kappa_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.kappa_ne_zero

/-- info: 'FormalResearch.DiscreteAiry.zmatrix_min_principle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.zmatrix_min_principle

/-- info: 'FormalResearch.DiscreteAiry.zmatrix_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.zmatrix_comparison

end FormalResearch.DiscreteAiry
