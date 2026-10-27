import Mathlib

/-!
# The Weyl-vertex quantity of a magic-diagonal state

Paper P (`paper/long/sec4_exceptional.tex`, Theorem `thm:weyl`, recalled input R7): for a unit
`d ∈ ℂ⁴` the rotation overlap of the magic-diagonal state `ψ_d` with its time reverse is
`F_K(ψ_d) = max_{w ∈ W(D₄)} |dᵀ w d|²`, `W(D₄)` the 192 signed permutation matrices of size 4 with
an even number of minus signs.  This file defines `weylVal`, `FKmag` (the right-hand side) and proves
its finite consequences used in the paper: the singlet-sphere formula (`eq:s4-singletFK`), and the
values `4/9` for `M₄` and `1/2` for `ψ₊`.  The Weyl-vertex formula itself (that `FKmag` is the rotation
overlap) is the recalled input and is not proved here.
-/

open Finset

namespace FormalResearch.FrameFree

/-- A signed permutation of the four coordinates: `(σ, e)` acts by `(w d)_k = (-1)^{e k} d_{σ k}`. -/
abbrev SP := Equiv.Perm (Fin 4) × (Fin 4 → Bool)

/-- `-1` for `true`, `+1` for `false`. -/
def sg (b : Bool) : ℤ := if b then -1 else 1

/-- `W(D₄)`: signed permutations with an even number of minus signs (192 of them). -/
def weylSet : Finset SP := univ.filter fun w => ∏ k, sg (w.2 k) = 1

theorem weylSet_card : weylSet.card = 192 := by decide +kernel

theorem one_mem_weylSet : ((1 : Equiv.Perm (Fin 4)), fun _ => false) ∈ weylSet := by decide +kernel

/-- `dᵀ w d = ∑_k (-1)^{e k} d_k d_{σ k}`. -/
def weylVal (d : Fin 4 → ℂ) (w : SP) : ℂ := ∑ k, (sg (w.2 k) : ℂ) * d k * d (w.1 k)

/-- `max_{w ∈ W(D₄)} |dᵀ w d|²`: the rotation overlap of `ψ_d` with its time reverse (Weyl-vertex formula). -/
noncomputable def FKmag (d : Fin 4 → ℂ) : ℝ :=
  weylSet.sup' ⟨_, one_mem_weylSet⟩ fun w => Complex.normSq (weylVal d w)

theorem le_FKmag (d : Fin 4 → ℂ) {w : SP} (hw : w ∈ weylSet) :
    Complex.normSq (weylVal d w) ≤ FKmag d :=
  Finset.le_sup' (fun w => Complex.normSq (weylVal d w)) hw

theorem FKmag_le_iff (d : Fin 4 → ℂ) (r : ℝ) :
    FKmag d ≤ r ↔ ∀ w ∈ weylSet, Complex.normSq (weylVal d w) ≤ r :=
  Finset.sup'_le_iff _ _

theorem FKmag_nonneg (d : Fin 4 → ℂ) : 0 ≤ FKmag d :=
  le_trans (Complex.normSq_nonneg _) (le_FKmag d one_mem_weylSet)

/-! ### Homogeneity -/

theorem weylVal_smul (c : ℂ) (d : Fin 4 → ℂ) (w : SP) :
    weylVal (c • d) w = c ^ 2 * weylVal d w := by
  unfold weylVal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem FKmag_smul_le (c : ℂ) (d : Fin 4 → ℂ) :
    FKmag (c • d) ≤ Complex.normSq c ^ 2 * FKmag d := by
  rw [FKmag_le_iff]
  intro w hw
  rw [weylVal_smul, map_mul, map_pow]
  exact mul_le_mul_of_nonneg_left (le_FKmag d hw) (by positivity)

theorem FKmag_smul (c : ℂ) (d : Fin 4 → ℂ) : FKmag (c • d) = Complex.normSq c ^ 2 * FKmag d := by
  by_cases hc : c = 0
  · subst hc
    have h0 := FKmag_smul_le 0 d
    rw [map_zero] at h0
    have h1 : FKmag ((0 : ℂ) • d) ≤ 0 := by simpa using h0
    rw [map_zero]
    simpa using le_antisymm h1 (FKmag_nonneg _)
  · apply le_antisymm (FKmag_smul_le c d)
    have h := FKmag_smul_le c⁻¹ (c • d)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, map_inv₀] at h
    have hpos : 0 < Complex.normSq c := Complex.normSq_pos.2 hc
    have : Complex.normSq c ^ 2 * (Complex.normSq c ^ 2)⁻¹ = 1 := by field_simp
    calc Complex.normSq c ^ 2 * FKmag d ≤ Complex.normSq c ^ 2 * ((Complex.normSq c)⁻¹ ^ 2 * FKmag (c • d)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = FKmag (c • d) := by field_simp

/-! ### The singlet sphere `d ∝ (1,1,1,z)` -/

/-- Coefficients `(a,b,c)` with `d^T w d = a + b z + c z²` for `d = (1,1,1,z)`. -/
def coef (w : SP) : ℤ × ℤ × ℤ :=
  (∑ k, if (k = 3 ∨ w.1 k = 3) then 0 else sg (w.2 k),
   ∑ k, if (k = 3 ∧ ¬ w.1 k = 3) ∨ (¬ k = 3 ∧ w.1 k = 3) then sg (w.2 k) else 0,
   ∑ k, if (k = 3 ∧ w.1 k = 3) then sg (w.2 k) else 0)

/-- The singlet-sphere vector `(1,1,1,z)`. -/
def dz (z : ℂ) : Fin 4 → ℂ := ![1, 1, 1, z]

theorem weylVal_dz (z : ℂ) (w : SP) :
    weylVal (dz z) w = (coef w).1 + (coef w).2.1 * z + (coef w).2.2 * z ^ 2 := by
  unfold weylVal coef
  have h : ∀ k : Fin 4, (dz z) k = if k = 3 then z else 1 := by
    intro k; fin_cases k <;> simp [dz]
  simp only [h, Fin.sum_univ_four]
  push_cast
  by_cases h0 : w.1 0 = 3 <;> by_cases h1 : w.1 1 = 3 <;> by_cases h2 : w.1 2 = 3 <;>
    by_cases h3 : w.1 3 = 3 <;> simp [h0, h1, h2, h3] <;> ring

theorem coef_image : weylSet.image coef =
    {(-3, 0, -1), (-2, -2, 0), (-2, 2, 0), (-1, 0, 1), (0, 0, 0), (1, 0, -1), (2, -2, 0), (2, 2, 0),
      (3, 0, 1)} := by
  decide +kernel

/-! ### Symmetries: coordinate permutations and even sign changes -/

theorem sg_xor (a b : Bool) : sg (xor a b) = sg a * sg b := by
  cases a <;> cases b <;> simp [sg]

theorem sg_sq (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

/-- Conjugating a signed permutation by a coordinate permutation `τ`. -/
def conjSP (τ : Equiv.Perm (Fin 4)) (w : SP) : SP := (τ * w.1 * τ⁻¹, fun k => w.2 (τ⁻¹ k))

theorem conjSP_mem (τ : Equiv.Perm (Fin 4)) {w : SP} (hw : w ∈ weylSet) : conjSP τ w ∈ weylSet := by
  simp only [weylSet, mem_filter, mem_univ, true_and] at hw ⊢
  exact (Equiv.prod_comp τ⁻¹ (fun k => sg (w.2 k))).trans hw

theorem weylVal_comp (τ : Equiv.Perm (Fin 4)) (d : Fin 4 → ℂ) (w : SP) :
    weylVal (d ∘ τ) w = weylVal d (conjSP τ w) := by
  unfold weylVal conjSP
  rw [← Equiv.sum_comp τ (fun k => (sg (w.2 (τ⁻¹ k)) : ℂ) * d k * d ((τ * w.1 * τ⁻¹) k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Equiv.Perm.mul_apply]

theorem FKmag_comp_le (τ : Equiv.Perm (Fin 4)) (d : Fin 4 → ℂ) : FKmag (d ∘ τ) ≤ FKmag d := by
  rw [FKmag_le_iff]
  intro w hw
  rw [weylVal_comp]
  exact le_FKmag d (conjSP_mem τ hw)

/-- `FKmag` is invariant under permuting the four coordinates of `d`. -/
theorem FKmag_comp (τ : Equiv.Perm (Fin 4)) (d : Fin 4 → ℂ) : FKmag (d ∘ τ) = FKmag d := by
  apply le_antisymm (FKmag_comp_le τ d)
  have := FKmag_comp_le τ⁻¹ (d ∘ τ)
  simpa [Function.comp_def] using this

/-- Multiplying the coordinates by signs `ε` with an even number of minus signs. -/
def signFlip (ε : Fin 4 → Bool) (d : Fin 4 → ℂ) : Fin 4 → ℂ := fun k => (sg (ε k) : ℂ) * d k

theorem flipSP_mem (ε : Fin 4 → Bool) (hε : ∏ k, sg (ε k) = 1) {w : SP} (hw : w ∈ weylSet) :
    (w.1, fun k => xor (w.2 k) (xor (ε k) (ε (w.1 k)))) ∈ weylSet := by
  simp only [weylSet, mem_filter, mem_univ, true_and] at hw ⊢
  simp only [sg_xor, Finset.prod_mul_distrib]
  rw [hw, hε, Equiv.prod_comp w.1 (fun k => sg (ε k)), hε]; norm_num

theorem weylVal_signFlip (ε : Fin 4 → Bool) (d : Fin 4 → ℂ) (w : SP) :
    weylVal (signFlip ε d) w = weylVal d (w.1, fun k => xor (w.2 k) (xor (ε k) (ε (w.1 k)))) := by
  unfold weylVal signFlip
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [sg_xor]
  have h1 : ((sg (ε k) : ℤ) : ℂ) * (sg (ε k)) = 1 := by exact_mod_cast sg_sq (ε k)
  push_cast
  ring

theorem FKmag_signFlip_le (ε : Fin 4 → Bool) (hε : ∏ k, sg (ε k) = 1) (d : Fin 4 → ℂ) :
    FKmag (signFlip ε d) ≤ FKmag d := by
  rw [FKmag_le_iff]
  intro w hw
  rw [weylVal_signFlip]
  exact le_FKmag d (flipSP_mem ε hε hw)

/-- `FKmag` is invariant under sign changes with an even number of minus signs. -/
theorem FKmag_signFlip (ε : Fin 4 → Bool) (hε : ∏ k, sg (ε k) = 1) (d : Fin 4 → ℂ) :
    FKmag (signFlip ε d) = FKmag d := by
  apply le_antisymm (FKmag_signFlip_le ε hε d)
  have := FKmag_signFlip_le ε hε (signFlip ε d)
  have e : signFlip ε (signFlip ε d) = d := by
    funext k
    simp only [signFlip]
    have h1 : ((sg (ε k) : ℤ) : ℂ) * (sg (ε k)) = 1 := by exact_mod_cast sg_sq (ε k)
    rw [← mul_assoc, h1, one_mul]
  rwa [e] at this

/-! ### The singlet-sphere formula -/

theorem normSq_int_mul (n : ℤ) (u : ℂ) : Complex.normSq ((n : ℂ) * u) = (n : ℝ) ^ 2 * Complex.normSq u := by
  rw [map_mul]
  have : Complex.normSq (n : ℂ) = (n : ℝ) ^ 2 := by
    rw [Complex.normSq_intCast]; ring
  rw [this]

theorem normSq_one_add_sq_le (z : ℂ) :
    Complex.normSq (1 + z ^ 2) ≤ max (Complex.normSq (3 + z ^ 2)) (Complex.normSq (1 - z ^ 2)) := by
  have h : (1 + z ^ 2) = ((1 : ℂ) / 2) * ((3 + z ^ 2) + (z ^ 2 - 1)) := by ring
  have hn : ‖1 + z ^ 2‖ ≤ max ‖3 + z ^ 2‖ ‖1 - z ^ 2‖ := by
    rw [h, norm_mul]
    have h2 : ‖(z ^ 2 - 1)‖ = ‖1 - z ^ 2‖ := norm_sub_rev _ _
    have := norm_add_le (3 + z ^ 2) (z ^ 2 - 1)
    rw [h2] at this
    have hm := le_max_left ‖3 + z ^ 2‖ ‖1 - z ^ 2‖
    have hm' := le_max_right ‖3 + z ^ 2‖ ‖1 - z ^ 2‖
    simp only [norm_div, norm_one, RCLike.norm_ofNat]
    linarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rcases le_total ‖3 + z ^ 2‖ ‖1 - z ^ 2‖ with h1 | h1
  · rw [max_eq_right h1] at hn
    exact le_max_of_le_right (by gcongr)
  · rw [max_eq_left h1] at hn
    exact le_max_of_le_left (by gcongr)

/-- The explicit maximum of the paper's equation `eq:s4-singletFK` (numerator). -/
noncomputable def singletMax (z : ℂ) : ℝ :=
  max (max (max (max (Complex.normSq (3 + z ^ 2)) (Complex.normSq (1 + z ^ 2)))
    (Complex.normSq (1 - z ^ 2))) (4 * Complex.normSq (1 + z))) (4 * Complex.normSq (1 - z))

theorem weylVal_dz_le (z : ℂ) {w : SP} (hw : w ∈ weylSet) :
    Complex.normSq (weylVal (dz z) w) ≤ singletMax z := by
  have hmem : coef w ∈ weylSet.image coef := Finset.mem_image_of_mem _ hw
  rw [coef_image] at hmem
  rw [weylVal_dz]
  have a1 := le_max_left (Complex.normSq (3 + z ^ 2)) (Complex.normSq (1 + z ^ 2))
  have h3 : Complex.normSq (3 + z ^ 2) ≤ singletMax z := by
    unfold singletMax; exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_left _ _)))
  have h1 : Complex.normSq (1 - z ^ 2) ≤ singletMax z := by
    unfold singletMax; exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have hp : 4 * Complex.normSq (1 + z) ≤ singletMax z := by
    unfold singletMax; exact le_max_of_le_left (le_max_right _ _)
  have hm : 4 * Complex.normSq (1 - z) ≤ singletMax z := by
    unfold singletMax; exact le_max_right _ _
  have h0 : 0 ≤ singletMax z := le_trans (Complex.normSq_nonneg _) h3
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h <;> rw [h]
  · have : ((-3 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * z + ((-1 : ℤ) : ℂ) * z ^ 2 = ((-1 : ℤ) : ℂ) * (3 + z ^ 2) := by
      push_cast; ring
    rw [this, normSq_int_mul]; norm_num; exact h3
  · have : ((-2 : ℤ) : ℂ) + ((-2 : ℤ) : ℂ) * z + ((0 : ℤ) : ℂ) * z ^ 2 = ((-2 : ℤ) : ℂ) * (1 + z) := by
      push_cast; ring
    rw [this, normSq_int_mul]; norm_num; linarith
  · have : ((-2 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * z + ((0 : ℤ) : ℂ) * z ^ 2 = ((-2 : ℤ) : ℂ) * (1 - z) := by
      push_cast; ring
    rw [this, normSq_int_mul]; norm_num; linarith
  · have : ((-1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * z + ((1 : ℤ) : ℂ) * z ^ 2 = ((-1 : ℤ) : ℂ) * (1 - z ^ 2) := by
      push_cast; ring
    rw [this, normSq_int_mul]; norm_num; exact h1
  · simpa using h0
  · have : ((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * z + ((-1 : ℤ) : ℂ) * z ^ 2 = ((1 : ℤ) : ℂ) * (1 - z ^ 2) := by
      push_cast; ring
    rw [this, normSq_int_mul]; norm_num; exact h1
  · have : ((2 : ℤ) : ℂ) + ((-2 : ℤ) : ℂ) * z + ((0 : ℤ) : ℂ) * z ^ 2 = ((2 : ℤ) : ℂ) * (1 - z) := by
      push_cast; ring
    rw [this, normSq_int_mul]; norm_num; linarith
  · have : ((2 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * z + ((0 : ℤ) : ℂ) * z ^ 2 = ((2 : ℤ) : ℂ) * (1 + z) := by
      push_cast; ring
    rw [this, normSq_int_mul]; norm_num; linarith
  · have : ((3 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * z + ((1 : ℤ) : ℂ) * z ^ 2 = ((1 : ℤ) : ℂ) * (3 + z ^ 2) := by
      push_cast; ring
    rw [this, normSq_int_mul]; norm_num; exact h3

/-- Witnesses for the coefficient triples. -/
theorem exists_coef (t : ℤ × ℤ × ℤ)
    (ht : t ∈ ({(3, 0, 1), (1, 0, -1), (2, 2, 0), (2, -2, 0)} : Finset (ℤ × ℤ × ℤ))) :
    ∃ w ∈ weylSet, coef w = t := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> decide +kernel

theorem FKmag_dz (z : ℂ) : FKmag (dz z) = singletMax z := by
  apply le_antisymm
  · exact (FKmag_le_iff _ _).2 fun w hw => weylVal_dz_le z hw
  · have hv : ∀ w ∈ weylSet, ∀ a b c : ℤ, coef w = (a, b, c) →
        weylVal (dz z) w = (a : ℂ) + (b : ℂ) * z + (c : ℂ) * z ^ 2 := by
      intro w _ a b c h
      rw [weylVal_dz, h]
    obtain ⟨w1, hw1, h1⟩ := exists_coef (3, 0, 1) (by simp)
    obtain ⟨w2, hw2, h2⟩ := exists_coef (1, 0, -1) (by simp)
    obtain ⟨w3, hw3, h3⟩ := exists_coef (2, 2, 0) (by simp)
    obtain ⟨w4, hw4, h4⟩ := exists_coef (2, -2, 0) (by simp)
    have e1 := le_FKmag (dz z) hw1
    have e2 := le_FKmag (dz z) hw2
    have e3 := le_FKmag (dz z) hw3
    have e4 := le_FKmag (dz z) hw4
    rw [hv w1 hw1 3 0 1 h1] at e1
    rw [hv w2 hw2 1 0 (-1) h2] at e2
    rw [hv w3 hw3 2 2 0 h3] at e3
    rw [hv w4 hw4 2 (-2) 0 h4] at e4
    have f1 : ((3 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * z + ((1 : ℤ) : ℂ) * z ^ 2 = 3 + z ^ 2 := by push_cast; ring
    have f2 : ((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * z + ((-1 : ℤ) : ℂ) * z ^ 2 = 1 - z ^ 2 := by push_cast; ring
    have f3 : ((2 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * z + ((0 : ℤ) : ℂ) * z ^ 2 = (2 : ℤ) * (1 + z) := by push_cast; ring
    have f4 : ((2 : ℤ) : ℂ) + ((-2 : ℤ) : ℂ) * z + ((0 : ℤ) : ℂ) * z ^ 2 = (2 : ℤ) * (1 - z) := by push_cast; ring
    rw [f1] at e1
    rw [f2] at e2
    rw [f3, normSq_int_mul] at e3
    rw [f4, normSq_int_mul] at e4
    have hr := normSq_one_add_sq_le z
    unfold singletMax
    refine max_le (max_le (max_le (max_le e1 ?_) e2) (by norm_num at e3; linarith)) (by norm_num at e4; linarith)
    exact le_trans hr (max_le e1 e2)

/-! ### The two exceptional states -/

theorem sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow]; simp

theorem singletMax_M4 : singletMax (Complex.I * (Real.sqrt 3 : ℝ)) = 16 := by
  have h3 := sqrt3_sq
  have hz : (Complex.I * ((Real.sqrt 3 : ℝ) : ℂ)) ^ 2 = -3 := by
    rw [mul_pow, Complex.I_sq, h3]; ring
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e1 : Complex.normSq (1 + Complex.I * ((Real.sqrt 3 : ℝ) : ℂ)) = 4 := by
    rw [Complex.normSq_apply]; simp; nlinarith
  have e2 : Complex.normSq (1 - Complex.I * ((Real.sqrt 3 : ℝ) : ℂ)) = 4 := by
    rw [Complex.normSq_apply]; simp; nlinarith
  unfold singletMax
  rw [hz, e1, e2]
  have a : (3 : ℂ) + -3 = 0 := by ring
  have b : (1 : ℂ) + -3 = -2 := by ring
  have c : (1 : ℂ) - -3 = 4 := by ring
  rw [a, b, c]
  have n2 : Complex.normSq (-2 : ℂ) = 4 := by simp; norm_num
  have n4 : Complex.normSq (4 : ℂ) = 16 := by simp; norm_num
  rw [n2, n4]; simp; norm_num

/-- `M₄`'s magic diagonal `(1,1,1,i√3)/√6` is a unit vector and `F_K(M₄) = 4/9`. -/
theorem FKmag_M4 :
    FKmag (((1 / Real.sqrt 6 : ℝ) : ℂ) • dz (Complex.I * (Real.sqrt 3 : ℝ))) = 4 / 9 := by
  rw [FKmag_smul, FKmag_dz, singletMax_M4, Complex.normSq_ofReal]
  have h6 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  field_simp
  nlinarith [h6]

theorem singletMax_psiPlus : singletMax Complex.I = 8 := by
  have e1 : Complex.normSq (1 + Complex.I) = 2 := by
    rw [Complex.normSq_apply]; simp; norm_num
  have e2 : Complex.normSq (1 - Complex.I) = 2 := by
    rw [Complex.normSq_apply]; simp; norm_num
  unfold singletMax
  rw [Complex.I_sq, e1, e2]
  have a : (3 : ℂ) + -1 = 2 := by ring
  have b : (1 : ℂ) + -1 = 0 := by ring
  have c : (1 : ℂ) - -1 = 2 := by ring
  rw [a, b, c]
  have n2 : Complex.normSq (2 : ℂ) = 4 := by simp; norm_num
  rw [n2]; simp; norm_num

/-- `ψ₊`'s magic diagonal `(1,1,1,i)/2` is a unit vector and `F_K(ψ₊) = 1/2`. -/
theorem FKmag_psiPlus : FKmag (((1 / 2 : ℝ) : ℂ) • dz Complex.I) = 1 / 2 := by
  rw [FKmag_smul, FKmag_dz, singletMax_psiPlus, Complex.normSq_ofReal]
  norm_num

/-- Unit-vector form of `eq:s4-singletFK`: for `d = (1,1,1,z)/√(3+|z|²)`,
`F_K = singletMax z / (3+|z|²)²`. -/
theorem FKmag_singlet_sphere (z : ℂ) :
    FKmag (((1 / Real.sqrt (3 + Complex.normSq z) : ℝ) : ℂ) • dz z) =
      singletMax z / (3 + Complex.normSq z) ^ 2 := by
  rw [FKmag_smul, FKmag_dz, Complex.normSq_ofReal]
  have hp : 0 < 3 + Complex.normSq z := by have := Complex.normSq_nonneg z; linarith
  have hs : Real.sqrt (3 + Complex.normSq z) * Real.sqrt (3 + Complex.normSq z) = 3 + Complex.normSq z :=
    Real.mul_self_sqrt hp.le
  have hq : 0 < Real.sqrt (3 + Complex.normSq z) := Real.sqrt_pos.2 hp
  field_simp
  rw [show Real.sqrt (3 + Complex.normSq z) ^ 4 = (Real.sqrt (3 + Complex.normSq z) * Real.sqrt (3 + Complex.normSq z)) ^ 2 by ring, hs]

end FormalResearch.FrameFree
