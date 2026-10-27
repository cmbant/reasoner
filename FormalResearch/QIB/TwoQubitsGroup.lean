import Mathlib
import FormalResearch.QIB.TwoQubitsStabiliser
import FormalResearch.QIB.BlockCoordinates

/-!
# Collective `SU(2)` on `d` copies of two qubits: weights and the commutant of the group

Namespace `FormalResearch.QIB.TwoQubits`.  Claim class: **proved** (finite linear algebra).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Matrix
open FormalResearch.FrameFree.Helstrom
open FormalResearch.FrameFree.NQubit (SU2 Op1)

namespace FormalResearch.QIB.TwoQubits

/-! ## Diagonal operators -/

section Diag

variable {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α] [DecidableEq α]

theorem kron_diagonal (g : I → α → ℂ) :
    kron (fun i => diagonal (g i)) = diagonal (fun s => ∏ i, g i (s i)) := by
  ext x y
  simp only [kron, diagonal_apply]
  rw [Finset.prod_ite_zero]
  by_cases h : x = y
  · subst h; simp
  · have : ¬ ∀ i ∈ (Finset.univ : Finset I), x i = y i := fun h' => h (funext fun i => h' i (Finset.mem_univ i))
    simp only [this, h, ↓reduceIte]

theorem emb_diagonal (f : α → ℂ) (i : I) :
    emb i (diagonal f) = diagonal (fun s : I → α => f (s i)) := by
  unfold emb
  have : (fun j => if j = i then diagonal f else (1 : Matrix α α ℂ))
      = fun j => diagonal (if j = i then f else fun _ => 1) := by
    funext j
    split_ifs <;> simp [diagonal_one]
  rw [this, kron_diagonal]
  congr 1
  funext s
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem coll_diagonal (f : α → ℂ) :
    coll (I := I) (diagonal f) = diagonal (fun s : I → α => ∑ i, f (s i)) := by
  show (∑ i : I, emb i (diagonal f)) = _
  simp_rw [emb_diagonal]
  ext x y
  by_cases h : x = y
  · subst h; simp [Matrix.sum_apply]
  · simp [Matrix.sum_apply, diagonal_apply, h]

end Diag


/-! ## Weights -/

section Weight

variable {d : ℕ}

/-- The `H₁`-eigenvalue of a basis state of one qubit. -/
def hh (a : Fin 2) : ℤ := if a = 0 then 1 else -1

/-- The total weight (eigenvalue of `Lc d H₁`) of a basis state of `d` copies of two qubits. -/
def wt (x : Copies 2 d) : ℤ := ∑ j, ∑ i, hh (x j i)

theorem H1_eq : H1 = diagonal (fun a : Fin 2 => (hh a : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H1, hh]

theorem Lc_H1 : Lc d H1 = diagonal (fun x : Copies 2 d => (wt x : ℂ)) := by
  unfold Lc
  rw [H1_eq, coll_diagonal, coll_diagonal]
  congr 1
  funext x
  simp [wt]

theorem prod_zpow_sum {ι : Type*} (s : Finset ι) (z : ℂ) (hz : z ≠ 0) (f : ι → ℤ) :
    ∏ i ∈ s, z ^ f i = z ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hz]

/-- The diagonal unit `diag(z, z⁻¹)`. -/
noncomputable def Dz (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![z, 0; 0, z⁻¹]

theorem Dz_eq (z : ℂ) : Dz z = diagonal (fun a : Fin 2 => z ^ hh a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dz, hh]

theorem rotK_Dz (z : ℂ) (hz : z ≠ 0) :
    rotK d (fun _ : Fin 2 => Dz z) = diagonal (fun x : Copies 2 d => z ^ wt x) := by
  unfold rotK
  simp only [Dz_eq z, kron_diagonal]
  congr 1
  funext x
  rw [wt, ← prod_zpow_sum _ z hz]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← prod_zpow_sum _ z hz]

theorem abs_wt_le (x : Copies 2 d) : |wt x| ≤ 2 * d := by
  have h1 : ∀ a : Fin 2, |hh a| ≤ 1 := by
    intro a; fin_cases a <;> simp [hh]
  have h2 : ∀ j : Fin d, |∑ i : Fin 2, hh (x j i)| ≤ 2 := by
    intro j
    calc |∑ i : Fin 2, hh (x j i)| ≤ ∑ i : Fin 2, |hh (x j i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 2, (1 : ℤ) := Finset.sum_le_sum fun i _ => h1 _
      _ = 2 := by simp
  calc |wt x| ≤ ∑ j : Fin d, |∑ i : Fin 2, hh (x j i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin d, (2 : ℤ) := Finset.sum_le_sum fun j _ => h2 j
    _ = 2 * d := by simp [mul_comm]

/-- Commuting with a diagonal operator transfers along coarsenings of its level sets. -/
theorem comm_diagonal_of_level {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (f g : ι → ℂ) (h : ∀ x y, f x = f y → g x = g y)
    (hM : M * diagonal f = diagonal f * M) : M * diagonal g = diagonal g * M := by
  ext x y
  have e := congrFun (congrFun hM x) y
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at e ⊢
  by_cases hxy : f x = f y
  · rw [h x y hxy]; ring
  · have : M x y = 0 := by
      have : M x y * (f y - f x) = 0 := by linear_combination e
      rcases mul_eq_zero.1 this with h' | h'
      · exact h'
      · exact absurd (sub_eq_zero.1 h').symm hxy
    rw [this]; ring

/-- A unit-modulus root of unity separating all weights. -/
theorem exists_weight_root (d : ℕ) :
    ∃ z : ℂ, z * (starRingEnd ℂ) z = 1 ∧ ∀ k : ℤ, |k| ≤ 4 * d → z ^ k = 1 → k = 0 := by
  have hn : (4 * d + 1 : ℕ) ≠ 0 := by omega
  have hprim := Complex.isPrimitiveRoot_exp (4 * d + 1) hn
  refine ⟨Complex.exp (2 * Real.pi * Complex.I / (4 * d + 1 : ℕ)), ?_, ?_⟩
  · have h1 := hprim.norm'_eq_one hn
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
    simp
  · intro k hk h1
    rw [hprim.zpow_eq_one_iff_dvd] at h1
    obtain ⟨m, hm⟩ := h1
    by_contra hk0
    have hm0 : m ≠ 0 := by
      rintro rfl; simp at hm; exact hk0 hm
    have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0
    have hab : |k| = (4 * d + 1 : ℕ) * |m| := by
      rw [hm, abs_mul, Nat.abs_cast]
    push_cast at hab
    nlinarith

end Weight


/-! ## The collective group and its commutant (direction `L1`) -/

section Group

variable {d : ℕ}

/-- The collective `SU(2)`: `u^{⊗ 2d}` on `d` copies of two qubits. -/
def Gcoll (d : ℕ) : Set (Matrix (Copies 2 d) (Copies 2 d) ℂ) :=
  {M | ∃ u : Op1, SU2 u ∧ M = rotK d (fun _ : Fin 2 => u)}

theorem Gcoll_star_closed (d : ℕ) : ∀ U ∈ Gcoll d, Uᴴ ∈ Gcoll d := by
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨uᴴ, FormalResearch.FrameFree.NQubit.SU2_adjoint hu, rotK_conjTranspose d _⟩

theorem SU2_Dz {z : ℂ} (hz : z * (starRingEnd ℂ) z = 1) : SU2 (Dz z) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hc : (starRingEnd ℂ) z = z⁻¹ := eq_inv_of_mul_eq_one_right hz
  have hc' : (starRingEnd ℂ) z⁻¹ = z := by rw [map_inv₀, hc, inv_inv]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Dz, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply, hc, hc', hz0]
  · simp [Dz, Matrix.det_fin_two, hz0]

/-- `M` commutes with `rotK u` for `u ∈ SU(2)`. -/
def CommGroup (d : ℕ) (M : Matrix (Copies 2 d) (Copies 2 d) ℂ) : Prop :=
  ∀ u : Op1, SU2 u → Commute M (rotK d (fun _ : Fin 2 => u))

theorem CommGroup.conj {M : Matrix (Copies 2 d) (Copies 2 d) ℂ} (hM : CommGroup d M) {V W : Op1}
    (hV : SU2 V) (hW : SU2 W) (hVW : V * W = 1) {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : Commute M (Lc d X)) : Commute M (Lc d (V * X * W)) := by
  rw [← Lc_conj V W X hVW]
  exact ((hM V hV).mul_right hX).mul_right (hM W hW)

noncomputable def Rot : Matrix (Fin 2) (Fin 2) ℂ := !![(3 / 5 : ℂ), 4 / 5; -4 / 5, 3 / 5]

theorem SU2_Rot : SU2 Rot := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Rot, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply, map_ofNat] <;> norm_num
  · simp [Rot, Matrix.det_fin_two]; norm_num

theorem Rot_mul_adj : Rot * Rotᴴ = 1 := mul_eq_one_comm.mp SU2_Rot.1

theorem Rot_conj_H1 :
    Rot * H1 * Rotᴴ = (-7 / 25 : ℂ) • H1 + (-24 / 25 : ℂ) • (E1 + F1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rot, H1, E1, F1, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply, map_ofNat] <;> norm_num


theorem exists_sqrt_I : ∃ w : ℂ, w ^ 2 = Complex.I ∧ w * (starRingEnd ℂ) w = 1 := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq Complex.I (n := 2) (by norm_num)
  refine ⟨w, hw, ?_⟩
  have h1 : Complex.normSq w ^ 2 = 1 := by
    rw [← map_pow, hw]; simp
  have h2 : 0 ≤ Complex.normSq w := Complex.normSq_nonneg w
  have h3 : Complex.normSq w = 1 := by nlinarith
  rw [Complex.mul_conj, h3]; simp

theorem Dz_mul_inv {w : ℂ} (hw : w ≠ 0) : Dz w * Dz w⁻¹ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dz, Matrix.mul_apply, Fin.sum_univ_two, hw]

theorem Dz_conj_EF {w : ℂ} (hw2 : w ^ 2 = Complex.I) :
    Dz w * (E1 + F1) * Dz w⁻¹ = Complex.I • (E1 - F1) := by
  have h1 : w⁻¹ * w⁻¹ = -Complex.I := by
    rw [← sq, inv_pow, hw2, Complex.inv_I]
  have h2 : w * w = Complex.I := by rw [← sq, hw2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dz, E1, F1, Matrix.mul_apply, Fin.sum_univ_two, h1, h2]

/-- **`L1`.**  A matrix commuting with the collective `SU(2)` commutes with `Lc H₁`, `Lc E₁`, `Lc F₁`. -/
theorem commute_Lc_of_commGroup {M : Matrix (Copies 2 d) (Copies 2 d) ℂ} (hM : CommGroup d M) :
    Commute M (Lc d H1) ∧ Commute M (Lc d E1) ∧ Commute M (Lc d F1) := by
  -- the weight operator
  have hH : Commute M (Lc d H1) := by
    obtain ⟨z, hz, hroot⟩ := exists_weight_root d
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    have h := (hM (Dz z) (SU2_Dz hz)).eq
    rw [rotK_Dz z hz0] at h
    rw [Lc_H1]
    refine comm_diagonal_of_level M _ _ (fun x y hxy => ?_) h
    have h1 : z ^ (wt x - wt y) = 1 := by
      rw [zpow_sub₀ hz0, hxy, div_self (zpow_ne_zero _ hz0)]
    have hb : |wt x - wt y| ≤ 4 * d := by
      calc |wt x - wt y| ≤ |wt x| + |wt y| := abs_sub _ _
        _ ≤ 2 * d + 2 * d := add_le_add (abs_wt_le x) (abs_wt_le y)
        _ = 4 * d := by ring
    have := hroot _ hb h1
    exact_mod_cast sub_eq_zero.1 this
  -- the sum `E₁ + F₁`
  have hS : Commute M (Lc d (E1 + F1)) := by
    have hR := hM.conj SU2_Rot (FormalResearch.FrameFree.NQubit.SU2_adjoint SU2_Rot) Rot_mul_adj hH
    rw [Rot_conj_H1, Lc_add, Lc_smul, Lc_smul] at hR
    have e : Lc d (E1 + F1) = (-25 / 24 : ℂ) • ((-7 / 25 : ℂ) • Lc d H1 + (-24 / 25 : ℂ) • Lc d (E1 + F1))
        - (7 / 24 : ℂ) • Lc d H1 := by
      module
    rw [e]
    exact (hR.smul_right _).sub_right (hH.smul_right _)
  -- the difference `E₁ - F₁`
  have hD : Commute M (Lc d (E1 - F1)) := by
    obtain ⟨w, hw2, hw⟩ := exists_sqrt_I
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    have hwi : w⁻¹ * (starRingEnd ℂ) w⁻¹ = 1 := by
      rw [map_inv₀, ← mul_inv, hw, inv_one]
    have hc := hM.conj (SU2_Dz hw) (SU2_Dz hwi) (Dz_mul_inv hw0) hS
    rw [Dz_conj_EF hw2, Lc_smul] at hc
    have e : Lc d (E1 - F1) = (-Complex.I) • (Complex.I • Lc d (E1 - F1)) := by
      rw [smul_smul]; simp
    rw [e]
    exact hc.smul_right _
  have eE : Lc d E1 = (1 / 2 : ℂ) • (Lc d (E1 + F1) + Lc d (E1 - F1)) := by
    rw [← Lc_add, ← Lc_smul]; congr 1; module
  have eF : Lc d F1 = (1 / 2 : ℂ) • (Lc d (E1 + F1) - Lc d (E1 - F1)) := by
    rw [← Lc_sub, ← Lc_smul]; congr 1; module
  refine ⟨hH, ?_, ?_⟩
  · rw [eE]; exact (hS.add_right hD).smul_right _
  · rw [eF]; exact (hS.sub_right hD).smul_right _

end Group

end FormalResearch.QIB.TwoQubits
