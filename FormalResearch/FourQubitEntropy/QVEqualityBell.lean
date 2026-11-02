import FormalResearch.FourQubitEntropy.QVEqualityFamily
import FormalResearch.FourQubitEntropy.RenyiFullStateEq
import FormalResearch.FourQubitEntropy.PaperEGapTwoFlatQF

/-!
# Equality in (QK) away from `P = 1`: the purity box, Bell-pair products, and the converses

Paper E, `sup_renyi.tex` (`sec:sup-qk`), proof of `thm:fqe-quadratic-variance`.

* `qk_strict_scalar`: for cut purities in the box `[1/4, 1]` with `P > 3/2` (QK) is strict
  (`eq:fqe-purity-box`, the scalar certificate); `eq_three_two`: at `P = 3/2` equality in (QK) forces `F = 0` and
  the purities to be a permutation of `(1, 1/4, 1/4)`.
* `IsBellTriple`: spectra `(pure, (1/4)⁴, (1/4)⁴)` up to ordering of cuts; `isBellTriple_iff_bellProduct`:
  for unit `ψ` this holds iff `ψ` is a local-unitary image of a product of two Bell pairs
  (`bell2`, `bell13`, `bell14`), via `prop:fqe-two-flat-rigidity`.
* `hs_triple_eq`, `cluster_triple_eq`, `bell_triple_eq`: all three spectral types attain equality in (QK).
-/

set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix

namespace FormalResearch.FourQubitEntropy.QVEquality

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.RenyiFull

/-! ### The purity box -/

/-- Above `P = 3/2`, (QK) is strict for cut purities in the box `[1/4, 1]` (`eq:fqe-purity-box`). -/
theorem qk_strict_scalar {a b c F : ℝ} (ha : 1 / 4 ≤ a) (ha' : a ≤ 1) (hb : 1 / 4 ≤ b) (hb' : b ≤ 1)
    (hc : 1 / 4 ≤ c) (hc' : c ≤ 1) (h : 3 / 2 < a + b + c) :
    6 * ((a - (a + b + c) / 3) ^ 2 + (b - (a + b + c) / 3) ^ 2 + (c - (a + b + c) / 3) ^ 2)
      < F ^ 2 + 9 / 2 * (a + b + c - 1) := by
  have h' := sub_pos.2 h
  nlinarith [sq_nonneg F, mul_nonneg (sub_nonneg.2 ha') (sub_nonneg.2 hb'),
      mul_nonneg (sub_nonneg.2 hb') (sub_nonneg.2 hc'), mul_nonneg (sub_nonneg.2 ha') (sub_nonneg.2 hc'),
      mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb), mul_nonneg (sub_nonneg.2 hb) (sub_nonneg.2 hc),
      mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hc), mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 ha'),
      mul_nonneg (sub_nonneg.2 hb) (sub_nonneg.2 hb'), mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 hc'),
      mul_nonneg h'.le (sub_nonneg.2 ha'), mul_nonneg h'.le (sub_nonneg.2 hb'),
      mul_nonneg h'.le (sub_nonneg.2 hc'), mul_nonneg h'.le (sub_nonneg.2 ha),
      mul_nonneg h'.le (sub_nonneg.2 hb), mul_nonneg h'.le (sub_nonneg.2 hc)]

/-- At `P = 3/2`, equality in (QK) forces `F = 0` and purities a permutation of `(1, 1/4, 1/4)`. -/
theorem eq_three_two {a b c F : ℝ} (ha : 1 / 4 ≤ a) (ha' : a ≤ 1) (hb : 1 / 4 ≤ b) (hb' : b ≤ 1)
    (hc : 1 / 4 ≤ c) (hc' : c ≤ 1) (h : a + b + c = 3 / 2)
    (heq : 6 * ((a - (a + b + c) / 3) ^ 2 + (b - (a + b + c) / 3) ^ 2 + (c - (a + b + c) / 3) ^ 2)
      = F ^ 2 + 9 / 2 * (a + b + c - 1)) :
    F = 0 ∧ ((a = 1 ∧ b = 1 / 4 ∧ c = 1 / 4) ∨ (a = 1 / 4 ∧ b = 1 ∧ c = 1 / 4) ∨
      (a = 1 / 4 ∧ b = 1 / 4 ∧ c = 1)) := by
  rw [h] at heq
  have hx : 0 ≤ a - 1 / 4 := by linarith
  have hy : 0 ≤ b - 1 / 4 := by linarith
  have hz : 0 ≤ c - 1 / 4 := by linarith
  have p1 := mul_nonneg hx hy
  have p2 := mul_nonneg hx hz
  have p3 := mul_nonneg hy hz
  have e1 : (a - 1 / 4) * (b - 1 / 4) = 0 := by nlinarith [sq_nonneg F]
  have e2 : (a - 1 / 4) * (c - 1 / 4) = 0 := by nlinarith [sq_nonneg F]
  have e3 : (b - 1 / 4) * (c - 1 / 4) = 0 := by nlinarith [sq_nonneg F]
  have e4 : F = 0 := by nlinarith [sq_nonneg F]
  refine ⟨e4, ?_⟩
  rcases mul_eq_zero.mp e1 with h1 | h1
  · rcases mul_eq_zero.mp e3 with h3 | h3
    · exact Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩)
    · exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
  · rcases mul_eq_zero.mp e2 with h2 | h2
    · exact Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩)
    · exact Or.inl ⟨by linarith, by linarith, by linarith⟩

/-! ### The three spectral types -/

/-- Pure spectrum `(1, 0, 0, 0)` up to order. -/
def UniformOne (l : Fin 4 → ℝ) : Prop := ∃ i, l i = 1 ∧ ∀ k, k ≠ i → l k = 0

/-- `((1,0,0,0), (1/4)⁴, (1/4)⁴)` up to ordering of the cuts and of each spectrum: the cut spectra of a product
of two Bell pairs. -/
def IsBellTriple (l₂ l₃ l₄ : Fin 4 → ℝ) : Prop :=
  (UniformOne l₂ ∧ UniformFour l₃ ∧ UniformFour l₄) ∨
  (UniformFour l₂ ∧ UniformOne l₃ ∧ UniformFour l₄) ∨
  (UniformFour l₂ ∧ UniformFour l₃ ∧ UniformOne l₄)

theorem uniformOne_of_pur {l : Fin 4 → ℝ} (h : IsProb4 l) (hp : pur l = 1) : UniformOne l := by
  obtain ⟨h0, hs⟩ := h
  unfold pur at hp
  simp only [Fin.sum_univ_four] at hs hp
  have a0 := h0 0
  have a1 := h0 1
  have a2 := h0 2
  have a3 := h0 3
  have u0 : l 0 ≤ 1 := by linarith
  have u1 : l 1 ≤ 1 := by linarith
  have u2 : l 2 ≤ 1 := by linarith
  have u3 : l 3 ≤ 1 := by linarith
  have t0 := mul_nonneg a0 (sub_nonneg.2 u0)
  have t1 := mul_nonneg a1 (sub_nonneg.2 u1)
  have t2 := mul_nonneg a2 (sub_nonneg.2 u2)
  have t3 := mul_nonneg a3 (sub_nonneg.2 u3)
  have z : ∀ x : ℝ, 0 ≤ x * (1 - x) → x * (1 - x) ≤ 0 → x = 0 ∨ x = 1 := fun x h1 h2 => by
    have : x * (1 - x) = 0 := le_antisymm h2 h1
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have z0 := z (l 0) t0 (by nlinarith)
  have z1 := z (l 1) t1 (by nlinarith)
  have z2 := z (l 2) t2 (by nlinarith)
  have z3 := z (l 3) t3 (by nlinarith)
  rcases z0 with e0 | e0 <;> rcases z1 with e1 | e1 <;> rcases z2 with e2 | e2 <;>
    rcases z3 with e3 | e3 <;>
    first
    | (exfalso; linarith)
    | exact ⟨0, e0, fun k hk => by fin_cases k <;> simp_all⟩
    | exact ⟨1, e1, fun k hk => by fin_cases k <;> simp_all⟩
    | exact ⟨2, e2, fun k hk => by fin_cases k <;> simp_all⟩
    | exact ⟨3, e3, fun k hk => by fin_cases k <;> simp_all⟩

/-! ### Moments of the spectral types -/

theorem uniformOne_pur_cub {l : Fin 4 → ℝ} (h : UniformOne l) : pur l = 1 ∧ cub l = 1 := by
  obtain ⟨i, hi, hk⟩ := h
  unfold pur cub
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_eq_single i (fun k _ hk' => by rw [hk k hk']; norm_num) (by simp), hi]; norm_num
  · rw [Finset.sum_eq_single i (fun k _ hk' => by rw [hk k hk']; norm_num) (by simp), hi]; norm_num

theorem uniformTwo_pur_cub {l : Fin 4 → ℝ} (h : UniformTwo l) : pur l = 1 / 2 ∧ cub l = 1 / 4 := by
  obtain ⟨i, j, hij, hi, hj, hk⟩ := h
  unfold pur cub
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_eq_add i j hij (fun k _ hk' => by rw [hk k hk'.1 hk'.2]; norm_num) (by simp) (by simp),
      hi, hj]; norm_num
  · rw [Finset.sum_eq_add i j hij (fun k _ hk' => by rw [hk k hk'.1 hk'.2]; norm_num) (by simp) (by simp),
      hi, hj]; norm_num

theorem uniformFour_cub {l : Fin 4 → ℝ} (h : UniformFour l) : cub l = 1 / 16 := by
  unfold cub; simp only [Fin.sum_univ_four, h _]; norm_num

/-- The scalar form of the three equality types. -/
theorem qk_eq_vals {l₂ l₃ l₄ : Fin 4 → ℝ} {a b c x y z : ℝ} (ha : pur l₂ = a) (hb : pur l₃ = b)
    (hc : pur l₄ = c) (hx : cub l₂ = x) (hy : cub l₃ = y) (hz : cub l₄ = z)
    (hsc : 6 * ((a - (a + b + c) / 3) ^ 2 + (b - (a + b + c) / 3) ^ 2 + (c - (a + b + c) / 3) ^ 2) =
      (17 * (a + b + c) - 12 * (x + y + z) - 12) ^ 2 + 9 / 2 * (a + b + c - 1)) :
    6 * RenyiFull.Vm l₂ l₃ l₄ = RenyiFull.Fm l₂ l₃ l₄ ^ 2 + 9 / 2 * (RenyiFull.Pm l₂ l₃ l₄ - 1) := by
  unfold RenyiFull.Vm RenyiFull.Fm RenyiFull.Tm RenyiFull.Pm
  rw [ha, hb, hc, hx, hy, hz]
  exact hsc

/-- **HS cut spectra attain equality in (QK).** -/
theorem hs_triple_eq {l₂ l₃ l₄ : Fin 4 → ℝ} (h : IsHsTriple l₂ l₃ l₄) :
    6 * RenyiFull.Vm l₂ l₃ l₄ = RenyiFull.Fm l₂ l₃ l₄ ^ 2 + 9 / 2 * (RenyiFull.Pm l₂ l₃ l₄ - 1) := by
  obtain ⟨h2, h3, h4⟩ := h
  obtain ⟨a2, b2⟩ := pur_cub_of_hsPerm h2
  obtain ⟨a3, b3⟩ := pur_cub_of_hsPerm h3
  obtain ⟨a4, b4⟩ := pur_cub_of_hsPerm h4
  exact qk_eq_vals a2 a3 a4 b2 b3 b4 (by norm_num)

/-- **Cluster cut spectra attain equality in (QK).** -/
theorem cluster_triple_eq {l₂ l₃ l₄ : Fin 4 → ℝ} (h : IsClusterTriple l₂ l₃ l₄) :
    6 * RenyiFull.Vm l₂ l₃ l₄ = RenyiFull.Fm l₂ l₃ l₄ ^ 2 + 9 / 2 * (RenyiFull.Pm l₂ l₃ l₄ - 1) := by
  rcases h with ⟨t2, f3, f4⟩ | ⟨f2, t3, f4⟩ | ⟨f2, f3, t4⟩
  · obtain ⟨a, b⟩ := uniformTwo_pur_cub t2
    exact qk_eq_vals a (uniformFour_pur f3) (uniformFour_pur f4) b (uniformFour_cub f3)
      (uniformFour_cub f4) (by norm_num)
  · obtain ⟨a, b⟩ := uniformTwo_pur_cub t3
    exact qk_eq_vals (uniformFour_pur f2) a (uniformFour_pur f4) (uniformFour_cub f2) b
      (uniformFour_cub f4) (by norm_num)
  · obtain ⟨a, b⟩ := uniformTwo_pur_cub t4
    exact qk_eq_vals (uniformFour_pur f2) (uniformFour_pur f3) a (uniformFour_cub f2)
      (uniformFour_cub f3) b (by norm_num)

/-- **Bell-product cut spectra attain equality in (QK).** -/
theorem bell_triple_eq {l₂ l₃ l₄ : Fin 4 → ℝ} (h : IsBellTriple l₂ l₃ l₄) :
    6 * RenyiFull.Vm l₂ l₃ l₄ = RenyiFull.Fm l₂ l₃ l₄ ^ 2 + 9 / 2 * (RenyiFull.Pm l₂ l₃ l₄ - 1) := by
  rcases h with ⟨t2, f3, f4⟩ | ⟨f2, t3, f4⟩ | ⟨f2, f3, t4⟩
  · obtain ⟨a, b⟩ := uniformOne_pur_cub t2
    exact qk_eq_vals a (uniformFour_pur f3) (uniformFour_pur f4) b (uniformFour_cub f3)
      (uniformFour_cub f4) (by norm_num)
  · obtain ⟨a, b⟩ := uniformOne_pur_cub t3
    exact qk_eq_vals (uniformFour_pur f2) a (uniformFour_pur f4) (uniformFour_cub f2) b
      (uniformFour_cub f4) (by norm_num)
  · obtain ⟨a, b⟩ := uniformOne_pur_cub t4
    exact qk_eq_vals (uniformFour_pur f2) (uniformFour_pur f3) a (uniformFour_cub f2)
      (uniformFour_cub f3) b (by norm_num)

/-! ### Bell-pair products -/

theorem pur_cutSpec₂ (ψ : Psi) : pur (cutSpec₂ ψ) = cutPurity12 ψ := by
  unfold cutSpec₂ cutPurity12; rw [pur_spec4]
theorem pur_cutSpec₃ (ψ : Psi) : pur (cutSpec₃ ψ) = cutPurity13 ψ := by
  unfold cutSpec₃ cutPurity13; rw [pur_spec4]
theorem pur_cutSpec₄ (ψ : Psi) : pur (cutSpec₄ ψ) = cutPurity14 ψ := by
  unfold cutSpec₄ cutPurity14; rw [pur_spec4]

theorem pcut12 (ψ : Psi) : PaperECritical.cutPurity12 ψ = cutPurity12 ψ := by
  unfold PaperECritical.cutPurity12 cutPurity12
  rw [sum_eigenvalues_pow (red12_herm ψ) 2, pow_two]
theorem pcut13 (ψ : Psi) : PaperECritical.cutPurity13 ψ = cutPurity13 ψ := by
  unfold PaperECritical.cutPurity13 cutPurity13
  rw [sum_eigenvalues_pow (red13_herm ψ) 2, pow_two]
theorem pcut14 (ψ : Psi) : PaperECritical.cutPurity14 ψ = cutPurity14 ψ := by
  unfold PaperECritical.cutPurity14 cutPurity14
  rw [sum_eigenvalues_pow (red14_herm ψ) 2, pow_two]

/-- Cut purities `(1, 1/4, 1/4)` up to order give the Bell spectral triple. -/
theorem bellTriple_of_purities {ψ : Psi} (hψ : normSqPsi ψ = 1)
    (h : (cutPurity12 ψ = 1 ∧ cutPurity13 ψ = 1 / 4 ∧ cutPurity14 ψ = 1 / 4) ∨
      (cutPurity12 ψ = 1 / 4 ∧ cutPurity13 ψ = 1 ∧ cutPurity14 ψ = 1 / 4) ∨
      (cutPurity12 ψ = 1 / 4 ∧ cutPurity13 ψ = 1 / 4 ∧ cutPurity14 ψ = 1)) :
    IsBellTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) := by
  have p2 := isProb4_spec4 (isProb12 hψ)
  have p3 := isProb4_spec4 (isProb13 hψ)
  have p4 := isProb4_spec4 (isProb14 hψ)
  rcases h with ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩
  · exact Or.inl ⟨uniformOne_of_pur p2 (by rw [pur_cutSpec₂]; exact h2),
      pur_eq_quarter p3 (by rw [pur_cutSpec₃]; exact h3), pur_eq_quarter p4 (by rw [pur_cutSpec₄]; exact h4)⟩
  · exact Or.inr (Or.inl ⟨pur_eq_quarter p2 (by rw [pur_cutSpec₂]; exact h2),
      uniformOne_of_pur p3 (by rw [pur_cutSpec₃]; exact h3), pur_eq_quarter p4 (by rw [pur_cutSpec₄]; exact h4)⟩)
  · exact Or.inr (Or.inr ⟨pur_eq_quarter p2 (by rw [pur_cutSpec₂]; exact h2),
      pur_eq_quarter p3 (by rw [pur_cutSpec₃]; exact h3), uniformOne_of_pur p4 (by rw [pur_cutSpec₄]; exact h4)⟩)

theorem purities_of_bellTriple {ψ : Psi}
    (h : IsBellTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) :
    (cutPurity12 ψ = 1 ∧ cutPurity13 ψ = 1 / 4 ∧ cutPurity14 ψ = 1 / 4) ∨
      (cutPurity12 ψ = 1 / 4 ∧ cutPurity13 ψ = 1 ∧ cutPurity14 ψ = 1 / 4) ∨
      (cutPurity12 ψ = 1 / 4 ∧ cutPurity13 ψ = 1 / 4 ∧ cutPurity14 ψ = 1) := by
  rcases h with ⟨t2, f3, f4⟩ | ⟨f2, t3, f4⟩ | ⟨f2, f3, t4⟩
  · exact Or.inl ⟨by rw [← pur_cutSpec₂]; exact (uniformOne_pur_cub t2).1,
      by rw [← pur_cutSpec₃]; exact uniformFour_pur f3, by rw [← pur_cutSpec₄]; exact uniformFour_pur f4⟩
  · exact Or.inr (Or.inl ⟨by rw [← pur_cutSpec₂]; exact uniformFour_pur f2,
      by rw [← pur_cutSpec₃]; exact (uniformOne_pur_cub t3).1, by rw [← pur_cutSpec₄]; exact uniformFour_pur f4⟩)
  · exact Or.inr (Or.inr ⟨by rw [← pur_cutSpec₂]; exact uniformFour_pur f2,
      by rw [← pur_cutSpec₃]; exact uniformFour_pur f3, by rw [← pur_cutSpec₄]; exact (uniformOne_pur_cub t4).1⟩)

/-- "`ψ` is a product of two Bell pairs": a local-unitary image of `bell2` (pairs `12|34`), `bell13` (pairs
`13|24`) or `bell14` (pairs `14|23`). -/
def IsBellProduct (ψ : Psi) : Prop := LUEquiv bell2 ψ ∨ LUEquiv bell13 ψ ∨ LUEquiv bell14 ψ

theorem bell2_eq_quadFam : bell2 = quadFam 1 0 := by
  funext a b c d
  simp [bell2, quadFam]

/-- The end `x = 1, y = 0` of (QF): a member of the family with `12|34` purity `1` is the Bell product. -/
theorem bell2_of_QF {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) (hx : 1 / 2 ≤ x ^ 2)
    (hp : PaperECritical.cutPurity12 (quadFam x y) = 1) : LUEquiv bell2 (quadFam x y) := by
  have h1 : (x ^ 2) ^ 2 + (y ^ 2) ^ 2 = 1 := by
    have := trace_sq_red12_quadFam x y
    unfold PaperECritical.cutPurity12 at hp; rw [this] at hp; exact hp
  have hy2 : y ^ 2 = 0 := by
    have hyy : y ^ 2 = 1 - x ^ 2 := by linarith
    rw [hyy] at h1 ⊢
    nlinarith
  have hy : y = 0 := by simpa using hy2
  subst hy
  rw [PaperECritical.quadFam_eq_Gv]
  refine PaperECritical.LU_bell2_of_single _ ?_ ⟨(0, 0), fun j hj => ?_⟩
  · simp only [Fintype.sum_prod_type, Fin.sum_univ_two, PaperECritical.qfVec]
    simp [Complex.normSq_apply]; nlinarith
  · simp [PaperECritical.qfVec, hj]

theorem cp12_swap23 (φ : Psi) : PaperECritical.cutPurity12 (swap23 φ) = PaperECritical.cutPurity13 φ := by
  unfold PaperECritical.cutPurity12 PaperECritical.cutPurity13; rw [red12_swap23]
theorem cp13_swap23 (φ : Psi) : PaperECritical.cutPurity13 (swap23 φ) = PaperECritical.cutPurity12 φ := by
  unfold PaperECritical.cutPurity12 PaperECritical.cutPurity13; rw [red13_swap23]
theorem cp14_swap23 (φ : Psi) : PaperECritical.cutPurity14 (swap23 φ) = PaperECritical.cutPurity14 φ := by
  unfold PaperECritical.cutPurity14; rw [red14_swap23]
theorem cp14_swap24 (φ : Psi) : PaperECritical.cutPurity14 (swap24 φ) = PaperECritical.cutPurity12 φ := by
  unfold PaperECritical.cutPurity12 PaperECritical.cutPurity14; rw [red14_swap24]

/-- **Bell-pair products have the Bell spectral triple** (the cut purities `(1, 1/4, 1/4)` up to order). -/
theorem bellTriple_of_product {ψ : Psi} (hψ : normSqPsi ψ = 1) (h : IsBellProduct ψ) :
    IsBellTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) := by
  have hb := PaperECritical.quadFam_two_flat (x := 1) (y := 0) (by norm_num)
  have hb12 : PaperECritical.cutPurity12 bell2 = 1 := by
    unfold PaperECritical.cutPurity12
    rw [bell2_eq_quadFam, trace_sq_red12_quadFam]; norm_num
  have hb13 : PaperECritical.cutPurity13 bell2 = 1 / 4 := by rw [bell2_eq_quadFam]; exact hb.1
  have hb14 : PaperECritical.cutPurity14 bell2 = 1 / 4 := by rw [bell2_eq_quadFam]; exact hb.2
  apply bellTriple_of_purities hψ
  rcases h with h | h | h
  · obtain ⟨e12, e13, e14⟩ := PaperECritical.cutPurities_LUEquiv h
    left
    refine ⟨?_, ?_, ?_⟩
    · rw [← pcut12, e12, hb12]
    · rw [← pcut13, e13, hb13]
    · rw [← pcut14, e14, hb14]
  · obtain ⟨e12, e13, e14⟩ := PaperECritical.cutPurities_LUEquiv h
    rw [← PaperECritical.swap23_bell2] at e12 e13 e14
    rw [cp12_swap23, hb13] at e12
    rw [cp13_swap23, hb12] at e13
    rw [cp14_swap23, hb14] at e14
    right; left
    refine ⟨?_, ?_, ?_⟩
    · rw [← pcut12, e12]
    · rw [← pcut13, e13]
    · rw [← pcut14, e14]
  · obtain ⟨e12, e13, e14⟩ := PaperECritical.cutPurities_LUEquiv h
    have s13 : PaperECritical.cutPurity13 (swap24 bell2) = 1 / 4 := by
      rw [PaperECritical.cutPurity13_swap24]; exact hb13
    rw [← PaperECritical.swap24_bell2] at e12 e13 e14
    rw [PaperECritical.cutPurity12_swap24, hb14] at e12
    rw [s13] at e13
    rw [cp14_swap24, hb12] at e14
    right; right
    refine ⟨?_, ?_, ?_⟩
    · rw [← pcut12, e12]
    · rw [← pcut13, e13]
    · rw [← pcut14, e14]

/-- **The Bell spectral triple forces a product of two Bell pairs** (`prop:fqe-two-flat-rigidity`:
two maximally mixed cuts put `ψ` in (QF), and the third cut is then pure, i.e. `ψ_{1,0}`). -/
theorem bellProduct_of_bellTriple {ψ : Psi} (hψ : normSqPsi ψ = 1)
    (h : IsBellTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) : IsBellProduct ψ := by
  rcases purities_of_bellTriple h with ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩
  · obtain ⟨x, y, hxy, hx, -, hLU⟩ := PaperECritical.two_flat_QF_13_14 ψ hψ (by rw [pcut13]; exact h3)
      (by rw [pcut14]; exact h4)
    have hp : PaperECritical.cutPurity12 (quadFam x y) = 1 := by
      rw [← (PaperECritical.cutPurities_LUEquiv hLU).1, pcut12]; exact h2
    exact Or.inl ((bell2_of_QF hxy hx hp).trans hLU)
  · obtain ⟨x, y, hxy, hx, -, hLU⟩ := PaperECritical.two_flat_QF_12_14 ψ hψ (by rw [pcut12]; exact h2)
      (by rw [pcut14]; exact h4)
    have hp : PaperECritical.cutPurity12 (quadFam x y) = 1 := by
      rw [← (PaperECritical.cutPurities_LUEquiv hLU).1, cp12_swap23, pcut13]; exact h3
    have := LUEquiv.swap23 ((bell2_of_QF hxy hx hp).trans hLU)
    rw [PaperECritical.swap23_bell2] at this
    exact Or.inr (Or.inl this)
  · obtain ⟨x, y, hxy, hx, -, hLU⟩ := PaperECritical.two_flat_QF_12_13 ψ hψ (by rw [pcut12]; exact h2)
      (by rw [pcut13]; exact h3)
    have hp : PaperECritical.cutPurity12 (quadFam x y) = 1 := by
      rw [← (PaperECritical.cutPurities_LUEquiv hLU).1, PaperECritical.cutPurity12_swap24, pcut14]; exact h4
    have := LUEquiv.swap24 ((bell2_of_QF hxy hx hp).trans hLU)
    rw [PaperECritical.swap24_bell2] at this
    exact Or.inr (Or.inr this)

/-- For a unit state: Bell spectral triple `⟺` product of two Bell pairs. -/
theorem isBellTriple_iff_bellProduct {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    IsBellTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ↔ IsBellProduct ψ :=
  ⟨bellProduct_of_bellTriple hψ, bellTriple_of_product hψ⟩

end FormalResearch.FourQubitEntropy.QVEquality
