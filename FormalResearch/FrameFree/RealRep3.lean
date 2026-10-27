import FormalResearch.FrameFree.Foundations

/-!
# Real representatives of three-qubit vectors (`RealRep3`)

Every three-qubit vector lies in the `GL(2,ℂ)³`-orbit of a real vector (Dür-Vidal-Cirac; Paper P,
`sec:s3-hierarchy`).  Proof here, without the SLOCC classification: view `ψ = |0⟩⊗M₀ + |1⟩⊗M₁` as a pencil of
`2×2` matrices.

1. A quadratic root (`quad_root`, `real3`) gives a site-0 operator making `M₀` singular (`det(sM₀+M₁)=0`).
2. If `M₀ ≠ 0` (`slice_case`, swaps to move a nonzero entry to `(0,0)`), elimination on sites 1, 2 makes
   `M₀ = E₀₀` (`pivot_case`), then `E00_dne` (`M₁ ~ E₁₁`, GHZ-type) or `E00_deq` (`M₁` has zero corner,
   entries rescaled to be real, covering W-type and the degenerate classes).
3. If `M₀ = 0`: either `M₁` is invertible (`B = M₁⁻¹`) or `M₁` is singular and a site-0 swap reduces to 2
   (`sing_case`).

`Real3 ψ` says `rot ![A,B,C] ψ` is real for some invertible `A, B, C`; `realRep3_core` is the statement of
`Ceilings.RealRep3`.  Everything is proved (no new axioms).
-/

open scoped ComplexConjugate Matrix BigOperators
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FrameFree.RealRep3

theorem sum_cons3 {β : Type*} [AddCommMonoid β] (n : ℕ) (f : (Fin (n + 1) → Fin 2) → β) :
    ∑ x, f x = ∑ a : Fin 2, ∑ y : Fin n → Fin 2, f (Fin.cons a y) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 2)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem cons3 (a b c : Fin 2) (z : Fin 0 → Fin 2) :
    (Fin.cons a (Fin.cons b (Fin.cons c z)) : Fin 3 → Fin 2) = ![a, b, c] := by
  ext i; fin_cases i <;> rfl

theorem vec3 (x : Fin 3 → Fin 2) : x = ![x 0, x 1, x 2] := by
  ext i; fin_cases i <;> rfl

theorem rot_apply3 (A : Fin 3 → Op1) (ψ : Ψ 3) (a b c : Fin 2) :
    rot A ψ ![a, b, c] = ∑ i, ∑ j, ∑ k, A 0 a i * A 1 b j * A 2 c k * ψ ![i, j, k] := by
  unfold rot
  simp only [sum_cons3 2, sum_cons3 1, sum_cons3 0, Fin.sum_univ_two, Finset.univ_unique,
    Finset.sum_singleton, cons3]
  simp [Fin.prod_univ_three]


theorem rot3_apply (A B C : Op1) (ψ : Ψ 3) (a b c : Fin 2) :
    rot ![A, B, C] ψ ![a, b, c] = ∑ i, ∑ j, ∑ k, A a i * B b j * C c k * ψ ![i, j, k] := by
  rw [rot_apply3]; rfl

/-- `ψ` becomes real after an invertible local operator. -/
def Real3 (ψ : Ψ 3) : Prop :=
  ∃ A B C : Op1, A.det ≠ 0 ∧ B.det ≠ 0 ∧ C.det ≠ 0 ∧
    ∀ a b c, conj (rot ![A, B, C] ψ ![a, b, c]) = rot ![A, B, C] ψ ![a, b, c]

theorem Real3.of_rot {ψ : Ψ 3} (A B C : Op1) (hA : A.det ≠ 0) (hB : B.det ≠ 0) (hC : C.det ≠ 0)
    (h : Real3 (rot ![A, B, C] ψ)) : Real3 ψ := by
  obtain ⟨A', B', C', hA', hB', hC', h⟩ := h
  refine ⟨A' * A, B' * B, C' * C, by rw [Matrix.det_mul]; exact mul_ne_zero hA' hA,
    by rw [Matrix.det_mul]; exact mul_ne_zero hB' hB, by rw [Matrix.det_mul]; exact mul_ne_zero hC' hC, ?_⟩
  have : rot ![A' * A, B' * B, C' * C] ψ = rot ![A', B', C'] (rot ![A, B, C] ψ) := by
    rw [rot_comp]; congr 1; ext i; fin_cases i <;> rfl
  rw [this]; exact h

theorem Real3.zero : Real3 (0 : Ψ 3) := by
  refine ⟨1, 1, 1, by simp, by simp, by simp, fun a b c => ?_⟩
  simp [rot3_apply]


theorem Real3.of_vals {ψ : Ψ 3} (A B C : Op1) (hA : A.det ≠ 0) (hB : B.det ≠ 0) (hC : C.det ≠ 0)
    (r : Fin 2 → Fin 2 → Fin 2 → ℝ)
    (h : ∀ a b c, rot ![A, B, C] ψ ![a, b, c] = (r a b c : ℂ)) : Real3 ψ :=
  ⟨A, B, C, hA, hB, hC, fun a b c => by rw [h]; exact Complex.conj_ofReal _⟩

/-- Slice `0` equal to `E₀₀` with `d ≠ 0`. -/
theorem E00_dne {ψ : Ψ 3} (h0 : ψ ![0, 0, 0] = 1) (h1 : ψ ![0, 0, 1] = 0) (h2 : ψ ![0, 1, 0] = 0)
    (h3 : ψ ![0, 1, 1] = 0) (hd : ψ ![1, 1, 1] ≠ 0) : Real3 ψ := by
  obtain ⟨a, ha⟩ : ∃ a, ψ ![1, 0, 0] = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ a, ψ ![1, 0, 1] = a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ a, ψ ![1, 1, 0] = a := ⟨_, rfl⟩
  obtain ⟨d, hd'⟩ : ∃ a, ψ ![1, 1, 1] = a := ⟨_, rfl⟩
  rw [hd'] at hd
  refine Real3.of_vals !![1, 0; -(a - b * c / d) / d, 1 / d] !![1, -b / d; 0, 1] !![1, -c / d; 0, 1]
    (by simp [Matrix.det_fin_two, hd]) (by simp [Matrix.det_fin_two]) (by simp [Matrix.det_fin_two])
    (fun x y z => if x = 1 ∧ y = 1 ∧ z = 1 then 1 else if x = 0 ∧ y = 0 ∧ z = 0 then 1 else 0)
    fun x y z => ?_
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
  simp [rot3_apply, Fin.sum_univ_two, h0, h1, h2, h3, ha, hb, hc, hd'] <;> field_simp <;> ring


theorem exists_scale (z : ℂ) : ∃ w : ℂ, w ≠ 0 ∧ ∃ r : ℝ, z * w = r := by
  by_cases hz : z = 0
  · exact ⟨1, one_ne_zero, 0, by simp [hz]⟩
  · exact ⟨z⁻¹, inv_ne_zero hz, 1, by simp [hz]⟩

/-- Slice `0` equal to `E₀₀` with `d = 0`. -/
theorem E00_deq {ψ : Ψ 3} (h0 : ψ ![0, 0, 0] = 1) (h1 : ψ ![0, 0, 1] = 0) (h2 : ψ ![0, 1, 0] = 0)
    (h3 : ψ ![0, 1, 1] = 0) (hd : ψ ![1, 1, 1] = 0) : Real3 ψ := by
  obtain ⟨a, ha⟩ : ∃ a, ψ ![1, 0, 0] = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ a, ψ ![1, 0, 1] = a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ a, ψ ![1, 1, 0] = a := ⟨_, rfl⟩
  obtain ⟨wb, hwb, rb, hrb⟩ := exists_scale b
  obtain ⟨wc, hwc, rc, hrc⟩ := exists_scale c
  refine Real3.of_vals !![1, 0; -a, 1] !![1, 0; 0, wc] !![1, 0; 0, wb]
    (by simp [Matrix.det_fin_two]) (by simp [Matrix.det_fin_two, hwc]) (by simp [Matrix.det_fin_two, hwb])
    (fun x y z => if x = 0 ∧ y = 0 ∧ z = 0 then 1 else if x = 1 ∧ y = 0 ∧ z = 1 then rb else
      if x = 1 ∧ y = 1 ∧ z = 0 then rc else 0)
    fun x y z => ?_
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
  simp [rot3_apply, Fin.sum_univ_two, h0, h1, h2, h3, ha, hb, hc, hd] <;> first | linear_combination hrb | linear_combination hrc


theorem E00_case {ψ : Ψ 3} (h0 : ψ ![0, 0, 0] = 1) (h1 : ψ ![0, 0, 1] = 0) (h2 : ψ ![0, 1, 0] = 0)
    (h3 : ψ ![0, 1, 1] = 0) : Real3 ψ := by
  by_cases hd : ψ ![1, 1, 1] = 0
  · exact E00_deq h0 h1 h2 h3 hd
  · exact E00_dne h0 h1 h2 h3 hd

/-- Pivot at `(0,0,0)` and singular slice `0`. -/
theorem pivot_case {ψ : Ψ 3} (h0 : ψ ![0, 0, 0] ≠ 0)
    (hs : ψ ![0, 0, 0] * ψ ![0, 1, 1] = ψ ![0, 0, 1] * ψ ![0, 1, 0]) : Real3 ψ := by
  obtain ⟨a, ha⟩ : ∃ a, ψ ![0, 0, 0] = a := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ a, ψ ![0, 0, 1] = a := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ a, ψ ![0, 1, 0] = a := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ a, ψ ![0, 1, 1] = a := ⟨_, rfl⟩
  rw [ha] at h0 hs
  rw [hp, hq, hr] at hs
  refine Real3.of_rot !![1 / a, 0; 0, 1] !![1, 0; -q / a, 1] !![1, 0; -p / a, 1]
    (by simp [Matrix.det_fin_two, h0]) (by simp [Matrix.det_fin_two]) (by simp [Matrix.det_fin_two])
    (E00_case ?_ ?_ ?_ ?_) <;>
  simp [rot3_apply, Fin.sum_univ_two, ha, hp, hq, hr] <;> field_simp <;> first | ring1 | linear_combination hs


theorem slice_case {ψ : Ψ 3} (hs : ψ ![0, 0, 0] * ψ ![0, 1, 1] = ψ ![0, 0, 1] * ψ ![0, 1, 0])
    (hne : ψ ![0, 0, 0] ≠ 0 ∨ ψ ![0, 0, 1] ≠ 0 ∨ ψ ![0, 1, 0] ≠ 0 ∨ ψ ![0, 1, 1] ≠ 0) :
    Real3 ψ := by
  have hX : (!![0, 1; 1, 0] : Op1).det ≠ 0 := by simp [Matrix.det_fin_two]
  have h1 : (1 : Op1).det ≠ 0 := by simp
  rcases hne with h | h | h | h
  · exact pivot_case h hs
  · refine Real3.of_rot 1 1 !![0, 1; 1, 0] h1 h1 hX (pivot_case ?_ ?_) <;>
    simp [rot3_apply, Fin.sum_univ_two, h]
    · linear_combination (-1 : ℂ) * hs
  · refine Real3.of_rot 1 !![0, 1; 1, 0] 1 h1 hX h1 (pivot_case ?_ ?_) <;>
    simp [rot3_apply, Fin.sum_univ_two, h]
    · linear_combination (-1 : ℂ) * hs
  · refine Real3.of_rot 1 !![0, 1; 1, 0] !![0, 1; 1, 0] h1 hX hX (pivot_case ?_ ?_) <;>
    simp [rot3_apply, Fin.sum_univ_two, h]
    linear_combination hs


theorem eq_zero_of_coords {ψ : Ψ 3} (h : ∀ a b c, ψ ![a, b, c] = 0) : ψ = 0 := by
  funext x; rw [vec3 x]; exact h _ _ _

/-- Singular slice `0` (so the pencil `(M₀, M₁)` has a singular member). -/
theorem sing_case {ψ : Ψ 3} (hs : ψ ![0, 0, 0] * ψ ![0, 1, 1] = ψ ![0, 0, 1] * ψ ![0, 1, 0]) :
    Real3 ψ := by
  by_cases hne : ψ ![0, 0, 0] ≠ 0 ∨ ψ ![0, 0, 1] ≠ 0 ∨ ψ ![0, 1, 0] ≠ 0 ∨ ψ ![0, 1, 1] ≠ 0
  · exact slice_case hs hne
  push Not at hne
  obtain ⟨e0, e1, e2, e3⟩ := hne
  have hX : (!![0, 1; 1, 0] : Op1).det ≠ 0 := by simp [Matrix.det_fin_two]
  have h1 : (1 : Op1).det ≠ 0 := by simp
  by_cases hD : ψ ![1, 0, 0] * ψ ![1, 1, 1] - ψ ![1, 0, 1] * ψ ![1, 1, 0] = 0
  · refine Real3.of_rot !![0, 1; 1, 0] 1 1 hX h1 h1 ?_
    by_cases hne' : ψ ![1, 0, 0] ≠ 0 ∨ ψ ![1, 0, 1] ≠ 0 ∨ ψ ![1, 1, 0] ≠ 0 ∨ ψ ![1, 1, 1] ≠ 0
    · refine slice_case ?_ ?_
      · simp [rot3_apply, Fin.sum_univ_two]; linear_combination hD
      · simpa [rot3_apply, Fin.sum_univ_two] using hne'
    · push Not at hne'
      obtain ⟨f0, f1, f2, f3⟩ := hne'
      have : ψ = 0 := eq_zero_of_coords fun a b c => by
        fin_cases a <;> fin_cases b <;> fin_cases c <;> assumption
      subst this
      have : rot ![!![0, 1; 1, 0], 1, 1] (0 : Ψ 3) = 0 := by
        funext x; rw [vec3 x]; simp [rot3_apply]
      rw [this]; exact Real3.zero
  · obtain ⟨a, ha⟩ : ∃ a, ψ ![1, 0, 0] = a := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ a, ψ ![1, 0, 1] = a := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ a, ψ ![1, 1, 0] = a := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ a, ψ ![1, 1, 1] = a := ⟨_, rfl⟩
    rw [ha, hb, hc, hd] at hD
    refine Real3.of_vals 1 ((a * d - b * c)⁻¹ • !![d, -b; -c, a]) 1 h1 ?_ h1
      (fun x y z => if x = 1 ∧ y = z then 1 else 0) fun x y z => ?_
    · have hD' : a * d - b * c ≠ 0 := hD
      have : (a * d - b * c)⁻¹ * d * ((a * d - b * c)⁻¹ * a) -
          (a * d - b * c)⁻¹ * b * ((a * d - b * c)⁻¹ * c) = (a * d - b * c)⁻¹ := by
        field_simp
      simp [Matrix.det_fin_two, this, hD']
    · fin_cases x <;> fin_cases y <;> fin_cases z <;>
      simp [rot3_apply, Fin.sum_univ_two, e0, e1, e2, e3, ha, hb, hc, hd] <;> field_simp <;> ring


theorem quad_root (d0 d1 m w : ℂ) (h : d0 ≠ 0) (hw : m ^ 2 - 4 * d0 * d1 = w * w) :
    d0 * ((-m + w) / (2 * d0)) ^ 2 + m * ((-m + w) / (2 * d0)) + d1 = 0 := by
  field_simp
  linear_combination (-1 : ℂ) * hw

/-- Every three-qubit vector is `GL(2,ℂ)³`-equivalent to a real one. -/
theorem real3 (ψ : Ψ 3) : Real3 ψ := by
  have h1 : (1 : Op1).det ≠ 0 := by simp
  by_cases hd0 : ψ ![0, 0, 0] * ψ ![0, 1, 1] - ψ ![0, 0, 1] * ψ ![0, 1, 0] = 0
  · exact sing_case (sub_eq_zero.mp hd0)
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_eq_mul_self
    ((ψ ![0, 0, 0] * ψ ![1, 1, 1] + ψ ![0, 1, 1] * ψ ![1, 0, 0] - ψ ![0, 0, 1] * ψ ![1, 1, 0]
        - ψ ![0, 1, 0] * ψ ![1, 0, 1]) ^ 2 -
      4 * (ψ ![0, 0, 0] * ψ ![0, 1, 1] - ψ ![0, 0, 1] * ψ ![0, 1, 0]) *
        (ψ ![1, 0, 0] * ψ ![1, 1, 1] - ψ ![1, 0, 1] * ψ ![1, 1, 0]))
  have hq := quad_root _ _ _ w hd0 hw
  refine Real3.of_rot !![(-(ψ ![0, 0, 0] * ψ ![1, 1, 1] + ψ ![0, 1, 1] * ψ ![1, 0, 0] -
      ψ ![0, 0, 1] * ψ ![1, 1, 0] - ψ ![0, 1, 0] * ψ ![1, 0, 1]) + w) /
      (2 * (ψ ![0, 0, 0] * ψ ![0, 1, 1] - ψ ![0, 0, 1] * ψ ![0, 1, 0])), 1; 1, 0] 1 1
    (by simp [Matrix.det_fin_two]) h1 h1 (sing_case ?_)
  simp only [rot3_apply, Fin.sum_univ_two]
  simp
  linear_combination hq

theorem realRep3_core (φ : Ψ 3) :
    ∃ A : Fin 3 → Op1, (∀ i, (A i).det ≠ 0) ∧ ∃ r : Ψ 3, cj r = r ∧ φ = rot A r := by
  obtain ⟨A, B, C, hA, hB, hC, h⟩ := real3 φ
  refine ⟨![A⁻¹, B⁻¹, C⁻¹], ?_, rot ![A, B, C] φ, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [Matrix.det_nonsing_inv, hA, hB, hC]
  · funext x; rw [vec3 x]; exact h _ _ _
  · rw [rot_comp]
    have : (fun i => (![A⁻¹, B⁻¹, C⁻¹] : Fin 3 → Op1) i * (![A, B, C] : Fin 3 → Op1) i) =
        fun _ => (1 : Op1) := by
      funext i
      fin_cases i
      · exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)
      · exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB)
      · exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hC)
    rw [this, rot_one]

end FormalResearch.FrameFree.RealRep3
