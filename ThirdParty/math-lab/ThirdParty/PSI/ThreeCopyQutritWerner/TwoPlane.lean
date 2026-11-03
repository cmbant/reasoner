module

public import ThreeCopyQutritWerner.TwoCutFactor

@[expose] public section


/-!
# A two-dimensional span of product tensors varies at one site

Manuscript Section 3.1: a two-dimensional linear space of product tensors varies at only one
site, because two spanning product tensors whose factor rays differ at two sites have a sum of
Schmidt rank two at one of those cuts; hence `ran P = E ⊗ u ⊗ v` up to site permutation.

`two_plane_of_product` proves this for an orthonormal pair of product tensors
`e₁ = a₁ ⊗ a₂ ⊗ a₃`, `e₂ = b₁ ⊗ b₂ ⊗ b₃` on `a ⊗ b ⊗ c` whose sum is a product across the
cuts `1|23` and `2|13`: then `|e₁⟩⟨e₁| + |e₂⟩⟨e₂|` equals
`(|f₁⟩⟨f₁| + |f₂⟩⟨f₂|) ⊗ |u⟩⟨u| ⊗ |v⟩⟨v|` up to site permutation, with `f₁`, `f₂`
orthonormal and `u`, `v` unit vectors.

Route: `TwoPlane.IsMultiple x y` says that `y` is a complex multiple of `x`.  If the factor
pairs at two sites are not proportional, the `2 × 2` minor of `e₁ + e₂` at a cut separating
them is the product of two nonzero minors (`TwoPlane.not_product_of_minors`), so `e₁ + e₂`
is not a product across that cut.  Normalizing the two common factors then gives the
statement (`TwoPlane.site₁`, `TwoPlane.site₂`, `TwoPlane.site₃`).
-/

noncomputable section

open scoped ComplexConjugate

namespace ThreeCopyQutritWerner

namespace TwoPlane

/-- `y` is a complex multiple of `x`. -/
def IsMultiple {ι : Type*} (x y : ι → ℂ) : Prop := ∃ c : ℂ, ∀ i, y i = c * x i

/-- Vanishing `2 × 2` minors and `x ≠ 0` make `y` a multiple of `x`. -/
theorem isMultiple_of_minors {ι : Type*} (x y : ι → ℂ) (hx : ∃ i, x i ≠ 0)
    (h : ∀ l l', x l * y l' = x l' * y l) : IsMultiple x y := by
  obtain ⟨l₀, hl₀⟩ := hx
  have hinv : x l₀ * (x l₀)⁻¹ = 1 := mul_inv_cancel₀ hl₀
  unfold IsMultiple
  refine ⟨y l₀ * (x l₀)⁻¹, fun i => ?_⟩
  linear_combination (-(y i)) * hinv + (x l₀)⁻¹ * h l₀ i

/-- If `x ≠ 0` and `y` is not a multiple of `x`, some `2 × 2` minor is nonzero. -/
theorem exists_minor_ne_zero {ι : Type*} (x y : ι → ℂ) (hx : ∃ i, x i ≠ 0)
    (h : ¬ IsMultiple x y) : ∃ l l', x l * y l' - x l' * y l ≠ 0 := by
  by_contra hcon
  exact h (isMultiple_of_minors x y hx fun l l' =>
    sub_eq_zero.mp (Classical.byContradiction fun hne => hcon ⟨l, l', hne⟩))

/-- A sum of two product vectors with a nonzero minor on each side is not a product: the
`2 × 2` minor of the sum is the product of the two minors. -/
theorem not_product_of_minors {L R : Type*} (x y : L → ℂ) (X Y : R → ℂ)
    (hl : ∃ l l', x l * y l' - x l' * y l ≠ 0) (hr : ∃ r r', X r * Y r' - X r' * Y r ≠ 0)
    (α : L → ℂ) (β : R → ℂ) (h : ∀ l r, x l * X r + y l * Y r = α l * β r) : False := by
  obtain ⟨l, l', hl⟩ := hl
  obtain ⟨r, r', hr⟩ := hr
  have key : (x l * y l' - x l' * y l) * (X r * Y r' - X r' * Y r) = 0 := by
    linear_combination (x l * X r + y l * Y r) * h l' r' + (α l' * β r') * h l r
      - (x l * X r' + y l * Y r') * h l' r - (α l' * β r) * h l r'
  exact mul_ne_zero hl hr key

/-- Non-proportional left factors give non-proportional product vectors. -/
theorem not_isMultiple_prod_left {A B : Type*} (x y : A → ℂ) (z w : B → ℂ)
    (hw : ∃ k, w k ≠ 0) (h : ¬ IsMultiple x y) :
    ¬ IsMultiple (fun p : A × B => x p.1 * z p.2) (fun p : A × B => y p.1 * w p.2) := by
  intro hm
  unfold IsMultiple at hm
  obtain ⟨c, hc⟩ := hm
  obtain ⟨k, hk⟩ := hw
  have hinv : w k * (w k)⁻¹ = 1 := mul_inv_cancel₀ hk
  apply h
  unfold IsMultiple
  refine ⟨c * z k * (w k)⁻¹, fun i => ?_⟩
  have h1 : y i * w k = c * (x i * z k) := hc (i, k)
  linear_combination (w k)⁻¹ * h1 - y i * hinv

/-- Non-proportional right factors give non-proportional product vectors. -/
theorem not_isMultiple_prod_right {A B : Type*} (x y : A → ℂ) (z w : B → ℂ)
    (hy : ∃ i, y i ≠ 0) (h : ¬ IsMultiple z w) :
    ¬ IsMultiple (fun p : A × B => x p.1 * z p.2) (fun p : A × B => y p.1 * w p.2) := by
  intro hm
  unfold IsMultiple at hm
  obtain ⟨c, hc⟩ := hm
  obtain ⟨i, hi⟩ := hy
  have hinv : y i * (y i)⁻¹ = 1 := mul_inv_cancel₀ hi
  apply h
  unfold IsMultiple
  refine ⟨c * x i * (y i)⁻¹, fun k => ?_⟩
  have h1 : y i * w k = c * (x i * z k) := hc (i, k)
  linear_combination (y i)⁻¹ * h1 - w k * hinv

theorem exists_prod_ne_zero {A B : Type*} (x : A → ℂ) (z : B → ℂ) (hx : ∃ i, x i ≠ 0)
    (hz : ∃ k, z k ≠ 0) : ∃ p : A × B, x p.1 * z p.2 ≠ 0 := by
  obtain ⟨i, hi⟩ := hx
  obtain ⟨k, hk⟩ := hz
  exact ⟨(i, k), mul_ne_zero hi hk⟩

theorem exists_ne_zero_of_vecNormSq_eq_one {ι : Type*} [Fintype ι] (e : ι → ℂ)
    (h : vecNormSq e = 1) : ∃ x, e x ≠ 0 := by
  by_contra hcon
  have hz : ∀ x, e x = 0 := fun x => Classical.byContradiction fun hne => hcon ⟨x, hne⟩
  have h0 : vecNormSq e = 0 := by
    unfold vecNormSq
    exact Finset.sum_eq_zero fun x _ => by simp [hz x]
  exact absurd (h0.symm.trans h) zero_ne_one

/-- Every factor of a unit product vector is nonzero. -/
theorem factors_ne_zero {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (a₁ : a → ℂ) (a₂ : b → ℂ) (a₃ : c → ℂ) (e : a × b × c → ℂ)
    (he : ∀ i j k, e (i, j, k) = a₁ i * a₂ j * a₃ k) (hn : vecNormSq e = 1) :
    (∃ i, a₁ i ≠ 0) ∧ (∃ j, a₂ j ≠ 0) ∧ (∃ k, a₃ k ≠ 0) := by
  obtain ⟨⟨i, j, k⟩, h0⟩ := exists_ne_zero_of_vecNormSq_eq_one e hn
  rw [he] at h0
  exact ⟨⟨i, left_ne_zero_of_mul (left_ne_zero_of_mul h0)⟩,
    ⟨j, right_ne_zero_of_mul (left_ne_zero_of_mul h0)⟩, ⟨k, right_ne_zero_of_mul h0⟩⟩

/-- A nonzero vector is a scalar multiple of a unit vector. -/
theorem exists_unit_factor {ι : Type*} [Fintype ι] (p : ι → ℂ) (hp : ∃ j, p j ≠ 0) :
    ∃ (u : ι → ℂ) (t : ℂ), vecNormSq u = 1 ∧ ∀ j, p j = t * u j := by
  obtain ⟨j₀, hj₀⟩ := hp
  have hne : vecNormSq p ≠ 0 := fun h => hj₀ (eq_zero_of_vecNormSq_eq_zero p h j₀)
  have hpos : 0 < vecNormSq p := lt_of_le_of_ne (vecNormSq_nonneg p) (Ne.symm hne)
  obtain ⟨s, hs0, hss⟩ : ∃ s : ℝ, 0 < s ∧ s * s = vecNormSq p :=
    ⟨Real.sqrt (vecNormSq p), Real.sqrt_pos.mpr hpos, Real.mul_self_sqrt (vecNormSq_nonneg p)⟩
  have hsi : s⁻¹ * s = 1 := inv_mul_cancel₀ hs0.ne'
  have hsi' : (s : ℂ) * ((s⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hs0.ne', Complex.ofReal_one]
  refine ⟨fun j => ((s⁻¹ : ℝ) : ℂ) * p j, (s : ℂ), ?_, fun j => ?_⟩
  · rw [vecNormSq_real_smul, ← hss]
    linear_combination (s⁻¹ * s + 1) * hsi
  · show p j = (s : ℂ) * (((s⁻¹ : ℝ) : ℂ) * p j)
    linear_combination (-(p j)) * hsi'

/-- `⟨x ⊗ y ⊗ z, x' ⊗ y' ⊗ z'⟩ = ⟨x, x'⟩ ⟨y, y'⟩ ⟨z, z'⟩`. -/
theorem braket_prod₃ {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (x x' : A → ℂ) (y y' : B → ℂ) (z z' : C → ℂ) (e e' : A × B × C → ℂ)
    (he : ∀ i j k, e (i, j, k) = x i * y j * z k)
    (he' : ∀ i j k, e' (i, j, k) = x' i * y' j * z' k) :
    braket e e' = braket x x' * braket y y' * braket z z' := by
  unfold braket
  calc ∑ p : A × B × C, conj (e p) * e' p
      = ∑ p : A × B × C, (conj (x p.1) * x' p.1) *
          ((conj (y p.2.1) * y' p.2.1) * (conj (z p.2.2) * z' p.2.2)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        have h1 : e p = x p.1 * y p.2.1 * z p.2.2 := he p.1 p.2.1 p.2.2
        have h2 : e' p = x' p.1 * y' p.2.1 * z' p.2.2 := he' p.1 p.2.1 p.2.2
        rw [h1, h2]
        simp only [map_mul]
        ring
    _ = (∑ i, conj (x i) * x' i) *
          ∑ q : B × C, (conj (y q.1) * y' q.1) * (conj (z q.2) * z' q.2) :=
        sum_prod_single (fun i => conj (x i) * x' i)
          (fun q : B × C => (conj (y q.1) * y' q.1) * (conj (z q.2) * z' q.2))
    _ = (∑ i, conj (x i) * x' i) *
          ((∑ j, conj (y j) * y' j) * ∑ k, conj (z k) * z' k) :=
        congrArg (fun S => (∑ i, conj (x i) * x' i) * S)
          (sum_prod_single (fun j => conj (y j) * y' j) (fun k => conj (z k) * z' k))
    _ = (∑ i, conj (x i) * x' i) * (∑ j, conj (y j) * y' j) * ∑ k, conj (z k) * z' k := by
        ring

/-- `‖x ⊗ y ⊗ z‖² = ‖x‖² ‖y‖² ‖z‖²`. -/
theorem vecNormSq_prod₃ {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (x : A → ℂ) (y : B → ℂ) (z : C → ℂ) (e : A × B × C → ℂ)
    (he : ∀ i j k, e (i, j, k) = x i * y j * z k) :
    vecNormSq e = vecNormSq x * vecNormSq y * vecNormSq z := by
  have h := braket_prod₃ x x y y z z e e he he
  simp only [braket_self] at h
  exact_mod_cast h

/-- Conclusion when site 1 is the active site. -/
theorem site₁ {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (e₁ e₂ : a × b × c → ℂ) (f₁ f₂ : a → ℂ) (u : b → ℂ) (v : c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1)
    (he₁ : ∀ i j k, e₁ (i, j, k) = f₁ i * u j * v k)
    (he₂ : ∀ i j k, e₂ (i, j, k) = f₂ i * u j * v k)
    (hn₁ : vecNormSq e₁ = 1) (hn₂ : vecNormSq e₂ = 1) (ho : braket e₁ e₂ = 0) :
    vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧ braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧
      vecNormSq v = 1 ∧
      ketBra e₁ e₁ + ketBra e₂ e₂ =
        tensor₃ (ketBra f₁ f₁ + ketBra f₂ f₂) (ketBra u u) (ketBra v v) := by
  have hm₁ := vecNormSq_prod₃ f₁ u v e₁ he₁
  have hm₂ := vecNormSq_prod₃ f₂ u v e₂ he₂
  have hb := braket_prod₃ f₁ f₂ u u v v e₁ e₂ he₁ he₂
  have hbu : braket u u = 1 := by simp [braket_self, hu]
  have hbv : braket v v = 1 := by simp [braket_self, hv]
  refine ⟨?_, ?_, ?_, hu, hv, ?_⟩
  · linear_combination hn₁ - hm₁ - vecNormSq f₁ * vecNormSq u * hv - vecNormSq f₁ * hu
  · linear_combination hn₂ - hm₂ - vecNormSq f₂ * vecNormSq u * hv - vecNormSq f₂ * hu
  · linear_combination ho - hb - braket f₁ f₂ * braket u u * hbv - braket f₁ f₂ * hbu
  · ext x y
    obtain ⟨i, j, k⟩ := x
    obtain ⟨i', j', k'⟩ := y
    simp only [Matrix.add_apply, tensor₃, ketBra, he₁, he₂, map_mul]
    ring

/-- Conclusion when site 2 is the active site. -/
theorem site₂ {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (e₁ e₂ : a × b × c → ℂ) (u : a → ℂ) (f₁ f₂ : b → ℂ) (v : c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1)
    (he₁ : ∀ i j k, e₁ (i, j, k) = u i * f₁ j * v k)
    (he₂ : ∀ i j k, e₂ (i, j, k) = u i * f₂ j * v k)
    (hn₁ : vecNormSq e₁ = 1) (hn₂ : vecNormSq e₂ = 1) (ho : braket e₁ e₂ = 0) :
    vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧ braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧
      vecNormSq v = 1 ∧
      ketBra e₁ e₁ + ketBra e₂ e₂ =
        tensor₃ (ketBra u u) (ketBra f₁ f₁ + ketBra f₂ f₂) (ketBra v v) := by
  have hm₁ := vecNormSq_prod₃ u f₁ v e₁ he₁
  have hm₂ := vecNormSq_prod₃ u f₂ v e₂ he₂
  have hb := braket_prod₃ u u f₁ f₂ v v e₁ e₂ he₁ he₂
  have hbu : braket u u = 1 := by simp [braket_self, hu]
  have hbv : braket v v = 1 := by simp [braket_self, hv]
  refine ⟨?_, ?_, ?_, hu, hv, ?_⟩
  · linear_combination hn₁ - hm₁ - vecNormSq f₁ * vecNormSq u * hv - vecNormSq f₁ * hu
  · linear_combination hn₂ - hm₂ - vecNormSq f₂ * vecNormSq u * hv - vecNormSq f₂ * hu
  · linear_combination ho - hb - braket f₁ f₂ * braket u u * hbv - braket f₁ f₂ * hbu
  · ext x y
    obtain ⟨i, j, k⟩ := x
    obtain ⟨i', j', k'⟩ := y
    simp only [Matrix.add_apply, tensor₃, ketBra, he₁, he₂, map_mul]
    ring

/-- Conclusion when site 3 is the active site. -/
theorem site₃ {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (e₁ e₂ : a × b × c → ℂ) (u : a → ℂ) (v : b → ℂ) (f₁ f₂ : c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1)
    (he₁ : ∀ i j k, e₁ (i, j, k) = u i * v j * f₁ k)
    (he₂ : ∀ i j k, e₂ (i, j, k) = u i * v j * f₂ k)
    (hn₁ : vecNormSq e₁ = 1) (hn₂ : vecNormSq e₂ = 1) (ho : braket e₁ e₂ = 0) :
    vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧ braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧
      vecNormSq v = 1 ∧
      ketBra e₁ e₁ + ketBra e₂ e₂ =
        tensor₃ (ketBra u u) (ketBra v v) (ketBra f₁ f₁ + ketBra f₂ f₂) := by
  have hm₁ := vecNormSq_prod₃ u v f₁ e₁ he₁
  have hm₂ := vecNormSq_prod₃ u v f₂ e₂ he₂
  have hb := braket_prod₃ u u v v f₁ f₂ e₁ e₂ he₁ he₂
  have hbu : braket u u = 1 := by simp [braket_self, hu]
  have hbv : braket v v = 1 := by simp [braket_self, hv]
  refine ⟨?_, ?_, ?_, hu, hv, ?_⟩
  · linear_combination hn₁ - hm₁ - vecNormSq f₁ * vecNormSq u * hv - vecNormSq f₁ * hu
  · linear_combination hn₂ - hm₂ - vecNormSq f₂ * vecNormSq u * hv - vecNormSq f₂ * hu
  · linear_combination ho - hb - braket f₁ f₂ * braket u u * hbv - braket f₁ f₂ * hbu
  · ext x y
    obtain ⟨i, j, k⟩ := x
    obtain ⟨i', j', k'⟩ := y
    simp only [Matrix.add_apply, tensor₃, ketBra, he₁, he₂, map_mul]
    ring

end TwoPlane

open TwoPlane in
/-- Manuscript Section 3.1: an orthonormal pair of product tensors whose sum is a product
across the cuts `1|23` and `2|13` spans `E ⊗ u ⊗ v` up to site permutation; the projection
`|e₁⟩⟨e₁| + |e₂⟩⟨e₂|` is `(|f₁⟩⟨f₁| + |f₂⟩⟨f₂|) ⊗ |u⟩⟨u| ⊗ |v⟩⟨v|` with the active factor
at site 1, 2 or 3. -/
theorem two_plane_of_product {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (a₁ b₁ : a → ℂ) (a₂ b₂ : b → ℂ) (a₃ b₃ : c → ℂ) (e₁ e₂ : a × b × c → ℂ)
    (he₁ : ∀ i j k, e₁ (i, j, k) = a₁ i * a₂ j * a₃ k)
    (he₂ : ∀ i j k, e₂ (i, j, k) = b₁ i * b₂ j * b₃ k)
    (hn₁ : vecNormSq e₁ = 1) (hn₂ : vecNormSq e₂ = 1) (ho : braket e₁ e₂ = 0)
    (hcut₁ : ∃ (α : a → ℂ) (β : b × c → ℂ), ∀ i j k, e₁ (i, j, k) + e₂ (i, j, k) = α i * β (j, k))
    (hcut₂ : ∃ (α : b → ℂ) (β : a × c → ℂ), ∀ i j k, e₁ (i, j, k) + e₂ (i, j, k) = α j * β (i, k)) :
    (∃ (f₁ f₂ : a → ℂ) (u : b → ℂ) (v : c → ℂ), vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧
        braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧ vecNormSq v = 1 ∧
        ketBra e₁ e₁ + ketBra e₂ e₂ = tensor₃ (ketBra f₁ f₁ + ketBra f₂ f₂) (ketBra u u) (ketBra v v)) ∨
    (∃ (u : a → ℂ) (f₁ f₂ : b → ℂ) (v : c → ℂ), vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧
        braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧ vecNormSq v = 1 ∧
        ketBra e₁ e₁ + ketBra e₂ e₂ = tensor₃ (ketBra u u) (ketBra f₁ f₁ + ketBra f₂ f₂) (ketBra v v)) ∨
    (∃ (u : a → ℂ) (v : b → ℂ) (f₁ f₂ : c → ℂ), vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧
        braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧ vecNormSq v = 1 ∧
        ketBra e₁ e₁ + ketBra e₂ e₂ = tensor₃ (ketBra u u) (ketBra v v) (ketBra f₁ f₁ + ketBra f₂ f₂)) := by
  obtain ⟨ha₁, ha₂, ha₃⟩ := factors_ne_zero a₁ a₂ a₃ e₁ he₁ hn₁
  obtain ⟨hb₁, hb₂, hb₃⟩ := factors_ne_zero b₁ b₂ b₃ e₂ he₂ hn₂
  -- the cut `1|23`
  have cut₁ : ¬ IsMultiple a₁ b₁ →
      ¬ IsMultiple (fun p : b × c => a₂ p.1 * a₃ p.2) (fun p : b × c => b₂ p.1 * b₃ p.2) →
        False := by
    intro h₁ h₂₃
    obtain ⟨α, β, hαβ⟩ := hcut₁
    refine not_product_of_minors a₁ b₁ (fun p : b × c => a₂ p.1 * a₃ p.2)
      (fun p : b × c => b₂ p.1 * b₃ p.2) (exists_minor_ne_zero a₁ b₁ ha₁ h₁)
      (exists_minor_ne_zero (fun p : b × c => a₂ p.1 * a₃ p.2)
        (fun p : b × c => b₂ p.1 * b₃ p.2) (exists_prod_ne_zero a₂ a₃ ha₂ ha₃) h₂₃) α β ?_
    rintro i ⟨j, k⟩
    show a₁ i * (a₂ j * a₃ k) + b₁ i * (b₂ j * b₃ k) = α i * β (j, k)
    have h := hαβ i j k
    rw [he₁, he₂] at h
    linear_combination h
  -- the cut `2|13`
  have cut₂ : ¬ IsMultiple a₂ b₂ →
      ¬ IsMultiple (fun p : a × c => a₁ p.1 * a₃ p.2) (fun p : a × c => b₁ p.1 * b₃ p.2) →
        False := by
    intro h₂ h₁₃
    obtain ⟨α, β, hαβ⟩ := hcut₂
    refine not_product_of_minors a₂ b₂ (fun p : a × c => a₁ p.1 * a₃ p.2)
      (fun p : a × c => b₁ p.1 * b₃ p.2) (exists_minor_ne_zero a₂ b₂ ha₂ h₂)
      (exists_minor_ne_zero (fun p : a × c => a₁ p.1 * a₃ p.2)
        (fun p : a × c => b₁ p.1 * b₃ p.2) (exists_prod_ne_zero a₁ a₃ ha₁ ha₃) h₁₃) α β ?_
    rintro j ⟨i, k⟩
    show a₂ j * (a₁ i * a₃ k) + b₂ j * (b₁ i * b₃ k) = α j * β (i, k)
    have h := hαβ i j k
    rw [he₁, he₂] at h
    linear_combination h
  by_cases P₂ : IsMultiple a₂ b₂
  · by_cases P₃ : IsMultiple a₃ b₃
    · -- active site 1
      left
      unfold IsMultiple at P₂ P₃
      obtain ⟨c₂, hc₂⟩ := P₂
      obtain ⟨c₃, hc₃⟩ := P₃
      obtain ⟨u, t₂, hu, hu'⟩ := exists_unit_factor a₂ ha₂
      obtain ⟨v, t₃, hv, hv'⟩ := exists_unit_factor a₃ ha₃
      refine ⟨fun i => t₂ * t₃ * a₁ i, fun i => c₂ * c₃ * t₂ * t₃ * b₁ i, u, v,
        site₁ e₁ e₂ _ _ u v hu hv ?_ ?_ hn₁ hn₂ ho⟩
      · intro i j k
        show e₁ (i, j, k) = t₂ * t₃ * a₁ i * u j * v k
        rw [he₁, hu' j, hv' k]
        ring
      · intro i j k
        show e₂ (i, j, k) = c₂ * c₃ * t₂ * t₃ * b₁ i * u j * v k
        rw [he₂, hc₂ j, hc₃ k, hu' j, hv' k]
        ring
    · -- active site 3
      have P₁ : IsMultiple a₁ b₁ := by
        by_contra h₁
        exact cut₁ h₁ (not_isMultiple_prod_right a₂ b₂ a₃ b₃ hb₂ P₃)
      right; right
      unfold IsMultiple at P₁ P₂
      obtain ⟨c₁, hc₁⟩ := P₁
      obtain ⟨c₂, hc₂⟩ := P₂
      obtain ⟨u, t₁, hu, hu'⟩ := exists_unit_factor a₁ ha₁
      obtain ⟨v, t₂, hv, hv'⟩ := exists_unit_factor a₂ ha₂
      refine ⟨u, v, fun k => t₁ * t₂ * a₃ k, fun k => c₁ * c₂ * t₁ * t₂ * b₃ k,
        site₃ e₁ e₂ u v _ _ hu hv ?_ ?_ hn₁ hn₂ ho⟩
      · intro i j k
        show e₁ (i, j, k) = u i * v j * (t₁ * t₂ * a₃ k)
        rw [he₁, hu' i, hv' j]
        ring
      · intro i j k
        show e₂ (i, j, k) = u i * v j * (c₁ * c₂ * t₁ * t₂ * b₃ k)
        rw [he₂, hc₁ i, hc₂ j, hu' i, hv' j]
        ring
  · -- active site 2
    have P₁ : IsMultiple a₁ b₁ := by
      by_contra h₁
      exact cut₂ P₂ (not_isMultiple_prod_left a₁ b₁ a₃ b₃ hb₃ h₁)
    have P₃ : IsMultiple a₃ b₃ := by
      by_contra h₃
      exact cut₂ P₂ (not_isMultiple_prod_right a₁ b₁ a₃ b₃ hb₁ h₃)
    right; left
    unfold IsMultiple at P₁ P₃
    obtain ⟨c₁, hc₁⟩ := P₁
    obtain ⟨c₃, hc₃⟩ := P₃
    obtain ⟨u, t₁, hu, hu'⟩ := exists_unit_factor a₁ ha₁
    obtain ⟨v, t₃, hv, hv'⟩ := exists_unit_factor a₃ ha₃
    refine ⟨u, fun j => t₁ * t₃ * a₂ j, fun j => c₁ * c₃ * t₁ * t₃ * b₂ j, v,
      site₂ e₁ e₂ u _ _ v hu hv ?_ ?_ hn₁ hn₂ ho⟩
    · intro i j k
      show e₁ (i, j, k) = u i * (t₁ * t₃ * a₂ j) * v k
      rw [he₁, hu' i, hv' k]
      ring
    · intro i j k
      show e₂ (i, j, k) = u i * (c₁ * c₃ * t₁ * t₃ * b₂ j) * v k
      rw [he₂, hc₁ i, hc₃ k, hu' i, hv' k]
      ring

end ThreeCopyQutritWerner

end
