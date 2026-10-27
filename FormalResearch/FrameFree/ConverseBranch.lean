import FormalResearch.FrameFree.ConverseProjector
import FormalResearch.FrameFree.RealRep3

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ComplexConjugate Matrix BigOperators ComplexOrder
open Matrix FormalResearch.FrameFree.NQubit FormalResearch.FrameFree.Helstrom

namespace FormalResearch.FrameFree.Converse

/-! ### Branches of the first qubit -/

/-- The branch `ξ_a = ⟨a|₀ ξ` of the first qubit. -/
def sl {m : ℕ} (a : Fin 2) (ξ : Ψ (m + 1)) : Ψ m := fun y => ξ (Fin.cons a y)

theorem ext_sl {m : ℕ} {ξ ξ' : Ψ (m + 1)} (h : ∀ a, sl a ξ = sl a ξ') : ξ = ξ' := by
  funext x
  have := congr_fun (h (x 0)) (Fin.tail x)
  simpa [sl, Fin.cons_self_tail] using this

theorem sl_rot_cons {m : ℕ} (A : Op1) (B : Fin m → Op1) (ξ : Ψ (m + 1)) (a : Fin 2) :
    sl a (rot (Fin.cons A B : Fin (m + 1) → Op1) ξ) = ∑ b, A a b • rot B (sl b ξ) := by
  funext y
  simp only [sl, rot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [RealRep3.sum_cons3 (β := ℂ) m (fun x : Fin (m + 1) → Fin 2 =>
    (∏ i, (Fin.cons A B : Fin (m + 1) → Op1) i ((Fin.cons a y : Fin (m + 1) → Fin 2) i) (x i)) * ξ x)]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.mul_sum]
  simp only [mul_assoc]

theorem nsq_eq_sum_sl {m : ℕ} (ξ : Ψ (m + 1)) : nsq ξ = ∑ a, nsq (sl a ξ) := by
  unfold nsq sl
  rw [RealRep3.sum_cons3, Finset.sum_comm]

theorem sl_cj {m : ℕ} (a : Fin 2) (ξ : Ψ (m + 1)) : sl a (cj ξ) = cj (sl a ξ) := rfl

theorem sl_add {m : ℕ} (a : Fin 2) (ξ ξ' : Ψ (m + 1)) : sl a (ξ + ξ') = sl a ξ + sl a ξ' := rfl

/-- The branches of `Θψ`: `(Θψ)₀ = Θ ψ₁`, `(Θψ)₁ = -Θ ψ₀`. -/
theorem sl_Θ_zero {m : ℕ} (ψ : Ψ (m + 1)) : sl 0 (Θ ψ) = Θ (sl 1 ψ) := by
  have e : (fun _ : Fin (m + 1) => eps) = (Fin.cons eps (fun _ : Fin m => eps) : Fin (m + 1) → Op1) := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [Θ_eq_rot, e, sl_rot_cons, Fin.sum_univ_two]
  simp [eps, Θ_eq_rot, sl_cj]

theorem sl_Θ_one {m : ℕ} (ψ : Ψ (m + 1)) : sl 1 (Θ ψ) = -Θ (sl 0 ψ) := by
  have e : (fun _ : Fin (m + 1) => eps) = (Fin.cons eps (fun _ : Fin m => eps) : Fin (m + 1) → Op1) := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [Θ_eq_rot, e, sl_rot_cons, Fin.sum_univ_two]
  simp [eps, Θ_eq_rot, sl_cj]

/-! ### `SU(2)` elements with prescribed first column -/

/-- The `SU(2)` matrix with first column `g` (for a unit vector `g`). -/
def Ug (g : Fin 2 → ℂ) : Op1 := !![g 0, -conj (g 1); g 1, conj (g 0)]

theorem SU2_Ug {g : Fin 2 → ℂ} (hg : conj (g 0) * g 0 + conj (g 1) * g 1 = 1) : SU2 (Ug g) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ug, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
      first | exact hg | linear_combination hg | ring
  · rw [Matrix.det_fin_two]
    simp only [Ug, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    linear_combination hg

/-! ### The branch criterion -/

/-- The branch `⟨e|₀ ψ = Σ_b conj(e_b) ψ_b` of the first qubit along `e`. -/
noncomputable def bra {m : ℕ} (e : Fin 2 → ℂ) (ψ : Ψ (m + 1)) : Ψ m := ∑ b, conj (e b) • sl b ψ

/-- The rank-one projector `|e⟩⟨e|`. -/
def Pr (e : Fin 2 → ℂ) : Op1 := Matrix.of fun a b => e a * conj (e b)

theorem Pr_proj {e : Fin 2 → ℂ} (he : conj (e 0) * e 0 + conj (e 1) * e 1 = 1) :
    (Pr e)ᴴ = Pr e ∧ Pr e * Pr e = Pr e := by
  constructor
  · ext i j; simp [Pr, Matrix.conjTranspose_apply, mul_comm]
  · ext i j
    simp only [Pr, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]
    linear_combination (e i * conj (e j)) * he

theorem isLocalProj_cons_Pr {m : ℕ} {e : Fin 2 → ℂ} (he : conj (e 0) * e 0 + conj (e 1) * e 1 = 1) :
    IsLocalProj (Fin.cons (Pr e) (fun _ : Fin m => (1 : Op1)) : Fin (m + 1) → Op1) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using Pr_proj he
  · simp

theorem sl_rot_Pr {m : ℕ} (e : Fin 2 → ℂ) (ξ : Ψ (m + 1)) (a : Fin 2) :
    sl a (rot (Fin.cons (Pr e) (fun _ : Fin m => (1 : Op1)) : Fin (m + 1) → Op1) ξ)
      = e a • bra e ξ := by
  rw [sl_rot_cons]
  simp only [rot_one, bra, Pr, Matrix.of_apply, Finset.smul_sum, smul_smul]

theorem normSq_sum_of_unit {e : Fin 2 → ℂ} (he : conj (e 0) * e 0 + conj (e 1) * e 1 = 1) :
    Complex.normSq (e 0) + Complex.normSq (e 1) = 1 := by
  have := congrArg Complex.re he
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.one_re] at this
  simp only [Complex.normSq_apply]
  nlinarith

theorem nsq_rot_Pr {m : ℕ} {e : Fin 2 → ℂ} (he : conj (e 0) * e 0 + conj (e 1) * e 1 = 1)
    (ξ : Ψ (m + 1)) :
    nsq (rot (Fin.cons (Pr e) (fun _ : Fin m => (1 : Op1)) : Fin (m + 1) → Op1) ξ) = nsq (bra e ξ) := by
  rw [nsq_eq_sum_sl]
  simp only [sl_rot_Pr, nsq_smul', Fin.sum_univ_two, ← add_mul, normSq_sum_of_unit he, one_mul]

theorem Θ_bra {m : ℕ} (e : Fin 2 → ℂ) (ψ : Ψ (m + 1)) :
    Θ (bra e ψ) = e 0 • Θ (sl 0 ψ) + e 1 • Θ (sl 1 ψ) := by
  simp only [bra, Fin.sum_univ_two, Θ_add', Θ_smul', Complex.conj_conj]

/-- **The branch criterion.**  Let `ψ` be an `(m+1)`-qubit state, `e` a unit vector of the first qubit and
`β = ⟨e|₀ψ` the corresponding `m`-qubit branch.  If `β ≠ 0` is *achiral* (`v Θβ = c β` for a local frame
`v ∈ SU(2)^m`, `|c| = 1`), then `ψ` has an achiral projected branch of weight `‖β‖²`. -/
theorem achiralBranch_of_branch {m : ℕ} (ψ : Ψ (m + 1)) {e : Fin 2 → ℂ}
    (he : conj (e 0) * e 0 + conj (e 1) * e 1 = 1) {v : Fin m → Op1} (hv : ∀ i, SU2 (v i)) {c : ℂ}
    (hc : ‖c‖ = 1) (hpos : 0 < nsq (bra e ψ)) (hach : rot v (Θ (bra e ψ)) = c • bra e ψ) :
    AchiralBranch ψ (nsq (bra e ψ)) := by
  set f : Fin 2 → ℂ := ![conj (e 1), -conj (e 0)] with hfdef
  have hf : conj (f 0) * f 0 + conj (f 1) * f 1 = 1 := by
    simp only [hfdef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, map_neg,
      Complex.conj_conj]
    linear_combination he
  set v₀ : Op1 := Ug e * (Ug f)ᴴ with hv₀
  have hv₀su : SU2 v₀ := SU2_mul (SU2_Ug he) (SU2_adjoint (SU2_Ug hf))
  have hg0 : ∑ c, conj (e c) * v₀ c 0 = e 1 := by
    simp only [hv₀, hfdef, Ug, Fin.sum_univ_two, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, map_neg, Complex.conj_conj, star_neg,
      Complex.star_def, neg_neg, neg_mul]
    linear_combination (e 1) * he
  have hg1 : ∑ c, conj (e c) * v₀ c 1 = -e 0 := by
    simp only [hv₀, hfdef, Ug, Fin.sum_univ_two, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, map_neg, Complex.conj_conj, star_neg,
      Complex.star_def, neg_neg, neg_mul]
    linear_combination (-e 0) * he
  refine ⟨hpos, Fin.cons (Pr e) (fun _ : Fin m => (1 : Op1)), Fin.cons v₀ v, c,
    isLocalProj_cons_Pr he, ?_, hc, nsq_rot_Pr he ψ, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hv₀su
    · simpa using hv j
  · have hcons : (fun i => (Fin.cons (Pr e) (fun _ : Fin m => (1 : Op1)) : Fin (m + 1) → Op1) i *
        (Fin.cons v₀ v : Fin (m + 1) → Op1) i) = Fin.cons (Pr e * v₀) (fun j => 1 * v j) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [hcons]
    apply ext_sl
    intro a
    have hsc : ∀ (z : ℂ) (ξ : Ψ (m + 1)), sl a (z • ξ) = z • sl a ξ := fun z ξ => rfl
    rw [hsc, sl_rot_Pr, sl_rot_cons]
    simp only [Fin.sum_univ_two, one_mul]
    have hP : ∀ b, (Pr e * v₀) a b = e a * ∑ c, conj (e c) * v₀ c b := by
      intro b
      simp only [Pr, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, mul_assoc]
    rw [hP 0, hP 1, hg0, hg1, sl_Θ_zero, sl_Θ_one, smul_smul]
    have hΘ : e 1 • Θ (sl 1 ψ) + (-e 0) • -Θ (sl 0 ψ) = Θ (bra e ψ) := by
      rw [Θ_bra, neg_smul, smul_neg, neg_neg, add_comm]
    have : (e a * e 1) • rot v (Θ (sl 1 ψ)) + (e a * -e 0) • rot v (-Θ (sl 0 ψ))
        = e a • rot v (Θ (bra e ψ)) := by
      rw [← hΘ, rot_add', rot_smul', rot_smul', smul_add, smul_smul, smul_smul]
    rw [this, hach, smul_smul, mul_comm]

end FormalResearch.FrameFree.Converse
