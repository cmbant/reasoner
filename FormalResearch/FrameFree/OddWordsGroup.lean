import Mathlib
import FormalResearch.FrameFree.OddWordsStrata
import FormalResearch.FrameFree.OddWordsFockData
import FormalResearch.FrameFree.TwirlsOdd

/-!
# Real matrices commuting with the total spin operators commute with `SU(2)^{⊗n}`
(Paper P, `prop:oddwords` (iii))

Namespace `FormalResearch.FrameFree.OddWords`.  Claim class: **proved**.

`commutes_tpow_of_det_one`: a real matrix `X` commuting with `Lm n` and `(Lm n)ᵀ` commutes
(as a complex matrix) with `u^{⊗n}` for every `u ∈ SL₂(ℂ)`.  Route: for the unipotent
`lowM t = (1 0; t 1)` one has `(lowM t)^{⊗n} = Σ_k t^k Strat k` (`tpow_lowM`), with `Strat k ∝ Lm^k`
(`OddWordsStrata`); the transposed unipotent is handled by transposition; diagonal tensor powers
are functions of the Hamming weight, hence commute with any `X` commuting with `Hm`; and every
`u ∈ SL₂(ℂ)` is a product of such matrices (`gauss`, with the Weyl element for `a = 0`).
Together with `Twirls.commutant_eq_blockPermSpan` this gives `X ∈ blockPermSpan`
(`mem_blockPermSpan_of_comm`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Matrix

namespace FormalResearch.FrameFree.OddWords

open FormalResearch.FrameFree.NQubit (Op1 SU2)
open FormalResearch.FrameFree.Twirls (tensOp tensOp_mul)

variable {n : ℕ}

/-- The `n`-fold tensor power `u^{⊗n}` with the same frame on every slot. -/
noncomputable def tpow (n : ℕ) (u : Op1) : Matrix (Cube n) (Cube n) ℂ :=
  tensOp (fun _ : Fin n => ()) (fun _ => u)

theorem tpow_apply (u : Op1) (x z : Cube n) : tpow n u x z = ∏ i, u (x i) (z i) := rfl

theorem tpow_mul (u v : Op1) : tpow n (u * v) = tpow n u * tpow n v := by
  rw [tpow, tpow, tpow, tensOp_mul]

theorem tpow_transpose (u : Op1) : tpow n uᵀ = (tpow n u)ᵀ := by
  ext x z; simp [tpow_apply]

/-- The unipotent `(1 0; t 1)`. -/
def lowM (t : ℂ) : Op1 := Matrix.of fun a b => if a = b then 1 else if a = 1 ∧ b = 0 then t else 0

/-- The diagonal matrix `diag (s, s⁻¹)`. -/
noncomputable def diagM (s : ℂ) : Op1 := Matrix.of fun a b => if a = b then (if a = 0 then s else s⁻¹) else 0

theorem tpow_lowM (t : ℂ) :
    tpow n (lowM t) = ∑ k ∈ range (n + 1), t ^ k • (Strat n k).map Complex.ofReal := by
  classical
  ext x z
  rw [tpow_apply, Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.map_apply, Strat, Matrix.of_apply, smul_eq_mul]
  by_cases hb : Below x z
  · have hf : ∀ i, lowM t (x i) (z i) = if x i = 1 ∧ z i = 0 then t else 1 := by
      intro i
      have := hb i
      rcases Fin.exists_fin_two.1 ⟨x i, rfl⟩ with h1 | h1 <;>
        rcases Fin.exists_fin_two.1 ⟨z i, rfl⟩ with h2 | h2 <;> simp_all [lowM]
    simp_rw [hf]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    have hd : dd x z = (Finset.univ.filter fun i => x i = 1 ∧ z i = 0).card := by
      unfold dd; rw [Finset.card_filter]
    have hdn : dd x z ≤ n := by
      rw [hd]; calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
        _ = n := by simp
    rw [← hd, Finset.sum_eq_single (dd x z)]
    · simp [hb]
    · intro k _ hk; simp [Ne.symm hk]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hdn)) h
  · obtain ⟨j, hj1, hj2⟩ : ∃ j, z j = 1 ∧ x j ≠ 1 := by
      by_contra h; push Not at h; exact hb h
    have h0 : x j = 0 := by
      rcases Fin.exists_fin_two.1 ⟨x j, rfl⟩ with h | h
      · exact h
      · exact absurd h hj2
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [lowM, h0, hj1])]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    simp [hb]

/-- Hypothesis: `X` commutes with `Lm n` and its transpose. -/
def CommR (X : Matrix (Cube n) (Cube n) ℝ) : Prop :=
  X * Lm n = Lm n * X ∧ X * (Lm n)ᵀ = (Lm n)ᵀ * X

theorem CommR.strat {X : Matrix (Cube n) (Cube n) ℝ} (h : CommR X) (k : ℕ) :
    X * Strat n k = Strat n k * X := by
  have hp : X * Lm n ^ k = Lm n ^ k * X := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h.1, ← Matrix.mul_assoc]
  rw [Lm_pow_eq, Matrix.mul_smul, Matrix.smul_mul] at hp
  exact smul_right_injective _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)) hp

theorem CommR.strat_transpose {X : Matrix (Cube n) (Cube n) ℝ} (h : CommR X) (k : ℕ) :
    X * (Strat n k)ᵀ = (Strat n k)ᵀ * X := by
  have hp : X * ((Lm n)ᵀ) ^ k = ((Lm n)ᵀ) ^ k * X := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h.2, ← Matrix.mul_assoc]
  rw [← Matrix.transpose_pow, Lm_pow_eq, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul] at hp
  exact smul_right_injective _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)) hp

/-- Real matrices commuting with `Lm n`, as complex matrices. -/
noncomputable abbrev cx (X : Matrix (Cube n) (Cube n) ℝ) : Matrix (Cube n) (Cube n) ℂ :=
  X.map Complex.ofReal

theorem cx_mul (X Y : Matrix (Cube n) (Cube n) ℝ) : cx (X * Y) = cx X * cx Y :=
  (Matrix.map_mul (f := Complex.ofRealHom))

theorem CommR.commute_lowM {X : Matrix (Cube n) (Cube n) ℝ} (h : CommR X) (t : ℂ) :
    cx X * tpow n (lowM t) = tpow n (lowM t) * cx X := by
  rw [tpow_lowM, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, ← cx_mul, ← cx_mul, h.strat k]

theorem CommR.commute_upM {X : Matrix (Cube n) (Cube n) ℝ} (h : CommR X) (t : ℂ) :
    cx X * tpow n (lowM t)ᵀ = tpow n (lowM t)ᵀ * cx X := by
  rw [tpow_transpose, tpow_lowM, Matrix.transpose_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.transpose_smul, ← Matrix.transpose_map, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  have := h.strat_transpose k
  have h2 := congrArg cx this
  rw [cx_mul, cx_mul] at h2
  simpa [cx, Matrix.transpose_map] using h2

theorem CommR.hm {X : Matrix (Cube n) (Cube n) ℝ} (h : CommR X) : X * Hm n = Hm n * X := by
  rw [← Rm_mul_Lm_sub, Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  · rw [← Matrix.mul_assoc, h.2, Matrix.mul_assoc, h.1, ← Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, h.1, Matrix.mul_assoc, h.2, ← Matrix.mul_assoc]

theorem CommR.wt_eq {X : Matrix (Cube n) (Cube n) ℝ} (h : CommR X) {x y : Cube n}
    (hxy : X x y ≠ 0) : wt x = wt y := by
  have := congrFun (congrFun h.hm x) y
  rw [Hm_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  by_contra hne
  have h2 : (X x y) * (2 * ((wt x : ℝ) - wt y)) = 0 := by linarith
  have h3 : (2 * ((wt x : ℝ) - wt y)) ≠ 0 := by
    intro h0; apply hne; have : (wt x : ℝ) = wt y := by linarith
    exact_mod_cast this
  exact hxy ((mul_eq_zero.1 h2).resolve_right h3)

theorem CommR.diag {X : Matrix (Cube n) (Cube n) ℝ} (h : CommR X) (f : ℕ → ℂ) :
    cx X * Matrix.diagonal (fun x : Cube n => f (wt x)) =
      Matrix.diagonal (fun x : Cube n => f (wt x)) * cx X := by
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hx : X x y = 0
  · simp [cx, hx]
  · rw [h.wt_eq hx, mul_comm]

theorem tpow_diagM (s : ℂ) :
    tpow n (diagM s) = Matrix.diagonal (fun x : Cube n => s⁻¹ ^ wt x * s ^ (n - wt x)) := by
  classical
  ext x z
  rw [tpow_apply, Matrix.diagonal_apply]
  by_cases hxz : x = z
  · subst hxz
    rw [if_pos rfl]
    have hf : ∀ i, diagM s (x i) (x i) = if x i = 1 then s⁻¹ else s := by
      intro i
      rcases Fin.exists_fin_two.1 ⟨x i, rfl⟩ with h1 | h1 <;> simp [diagM, h1]
    simp_rw [hf]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, ← wt_eq_card]
    congr 2
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => x i = 1)
    rw [← wt_eq_card] at this
    simp at this
    omega
  · rw [if_neg hxz]
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ z j := by
      by_contra h; push Not at h; exact hxz (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [diagM, hj])

theorem CommR.commute_diagM {X : Matrix (Cube n) (Cube n) ℝ} (h : CommR X) (s : ℂ) :
    cx X * tpow n (diagM s) = tpow n (diagM s) * cx X := by
  rw [tpow_diagM]
  exact h.diag (fun w => s⁻¹ ^ w * s ^ (n - w))

/-- The set of `u` with `u^{⊗n}` commuting with `cx X` is closed under products. -/
theorem commutes_mul {X : Matrix (Cube n) (Cube n) ℝ} {u v : Op1}
    (hu : cx X * tpow n u = tpow n u * cx X) (hv : cx X * tpow n v = tpow n v * cx X) :
    cx X * tpow n (u * v) = tpow n (u * v) * cx X := by
  rw [tpow_mul, ← Matrix.mul_assoc, hu, Matrix.mul_assoc, hv, Matrix.mul_assoc]

/-- The unipotent `(1 t; 0 1)`. -/
def upM (t : ℂ) : Op1 := (lowM t)ᵀ

theorem gauss (u : Op1) (ha : u 0 0 ≠ 0) (hdet : u.det = 1) :
    u = lowM (u 1 0 / u 0 0) * diagM (u 0 0) * upM (u 0 1 / u 0 0) := by
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowM, diagM, upM, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> linear_combination hdet

theorem CommR.commute_of_a_ne {X : Matrix (Cube n) (Cube n) ℝ} (h : CommR X) {u : Op1}
    (ha : u 0 0 ≠ 0) (hdet : u.det = 1) : cx X * tpow n u = tpow n u * cx X := by
  rw [gauss u ha hdet]
  exact commutes_mul (commutes_mul (h.commute_lowM _) (h.commute_diagM _)) (h.commute_upM _)

/-- The Weyl element `(0 1; -1 0)`. -/
def weylM : Op1 := Matrix.of fun a b => if a = 0 ∧ b = 1 then 1 else if a = 1 ∧ b = 0 then -1 else 0

theorem weylM_eq : weylM = upM 1 * lowM (-1) * upM 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylM, lowM, upM, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Commutation with `SL₂(ℂ)^{⊗n}`.** -/
theorem CommR.commute_of_det {X : Matrix (Cube n) (Cube n) ℝ} (h : CommR X) {u : Op1}
    (hdet : u.det = 1) : cx X * tpow n u = tpow n u * cx X := by
  by_cases ha : u 0 0 = 0
  · have hdet' := hdet
    rw [Matrix.det_fin_two, ha] at hdet'
    have hc : u 1 0 ≠ 0 := by
      intro h0; rw [h0] at hdet'; simp at hdet'
    let u' : Op1 := Matrix.of fun a b => if a = 0 then (if b = 0 then -u 1 0 else -u 1 1)
      else (if b = 0 then u 0 0 else u 0 1)
    have hu : u = weylM * u' := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [weylM, u', Matrix.mul_apply, Fin.sum_univ_two]
    have hdu' : u'.det = 1 := by
      rw [Matrix.det_fin_two]
      simp only [u', Matrix.of_apply]
      rw [Matrix.det_fin_two] at hdet
      simpa using (by linear_combination hdet : (-u 1 0) * u 0 1 - (-u 1 1) * u 0 0 = 1)
    have h1 : cx X * tpow n weylM = tpow n weylM * cx X := by
      rw [weylM_eq]
      exact commutes_mul (commutes_mul (h.commute_upM _) (h.commute_lowM _)) (h.commute_upM _)
    have h2 : cx X * tpow n u' = tpow n u' * cx X :=
      h.commute_of_a_ne (by simp [u', hc]) hdu'
    rw [hu]
    exact commutes_mul h1 h2
  · exact h.commute_of_a_ne ha hdet

/-- A real matrix commuting with `Lm n` and `(Lm n)ᵀ` lies in the block-permutation span
(Schur--Weyl, via `Twirls.commutant_eq_blockPermSpan`). -/
theorem CommR.mem_blockPermSpan {X : Matrix (Cube n) (Cube n) ℝ} (h : CommR X) :
    cx X ∈ FormalResearch.FrameFree.Twirls.blockPermSpan (fun _ : Fin n => ()) := by
  rw [← FormalResearch.FrameFree.Twirls.commutant_eq_blockPermSpan]
  intro u hu
  exact h.commute_of_det (u := u ()) (hu ()).2

end FormalResearch.FrameFree.OddWords
