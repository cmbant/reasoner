import FormalResearch.FrameFree.Foundations
import FormalResearch.FrameFree.HelstromPure

/-!
# The frame-free error `P_e(k)` and the upper bound `ξ_inv ≤ C_K` (Paper P, `thm:window`)

Namespace `FormalResearch.FrameFree.Helstrom`.  Builds on `FrameFree.NQubit` (`Ψ n`, `rot`, `SU2`, `Θ`, `FK`,
`FKΘ`, `CK`) and on the generic pure-state Helstrom bound of `HelstromPure.lean`.

**Definitions.**
* `kron M`: the Kronecker product of local matrices `M i`; `rot u ψ = kron u *ᵥ ψ` (`rot_eq_kron`).
* `Copies n k = (Fin k → Fin n → Fin 2)`: basis of `k` copies of an `n`-qubit system; `copies k ψ = ψ^{⊗k}`;
  `rotK k u = (u₁ ⊗ ⋯ ⊗ uₙ)^{⊗k}`, the frame `u ∈ SU(2)^n` acting on all `k` copies.
* `IsInvEffect k E`: `0 ≤ E ≤ 1` and `E` commutes with `rotK k u` for all `u ∈ SU(2)^n` (a `K`-invariant test).
* `Pe k ψ`: the best error over `K`-invariant tests between `ψ^{⊗k}` and `(Θψ)^{⊗k}` with equal priors.
  This is the "best `K`-invariant measurement" description of `P_e(k)` in `def:setting`; the identification with
  the Helstrom error of the Haar-twirled states is *not* formalised (see `Helstrom.lean`'s end notes).
* `err_frame`: an invariant test has the same error in every frame `u`.

**Proved.**
* `Pe_ge_of_rot`, `Pe_ge_quarter`: for unit `ψ` and every `u ∈ SU(2)^n`,
  `|⟨ψ|uΘψ⟩|^{2k}/4 ≤ P_e(k)`, hence `F_K(ψ)^k/4 ≲ P_e(k)`.
* `neg_log_Pe_le`, `limsup_neg_log_Pe_le_CK`: `-(1/k) log P_e(k) ≤ C_K + (log 4)/k` (all `ε`-versions) and
  `limsup_k -(1/k) log P_e(k) ≤ C_K(ψ)`: the upper half of `thm:window`.
-/

open scoped ComplexConjugate Matrix BigOperators
open Matrix FormalResearch.FrameFree.NQubit
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace FormalResearch.FrameFree.Helstrom

/-! ### Kronecker products and copies -/

/-- Kronecker product of local matrices. -/
def kron {I α : Type*} [Fintype I] (M : I → Matrix α α ℂ) : Matrix (I → α) (I → α) ℂ :=
  fun x y => ∏ i, M i (x i) (y i)

theorem rot_eq_kron {n : ℕ} (u : Fin n → Op1) (ψ : Ψ n) : rot u ψ = kron u *ᵥ ψ := rfl

section kron
variable {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α] [DecidableEq α]

/-- `kron M` applied to a product vector. -/
theorem kron_mulVec_prod (M : I → Matrix α α ℂ) (φ : I → α → ℂ) :
    kron M *ᵥ (fun x => ∏ i, φ i (x i)) = fun x => ∏ i, (M i *ᵥ φ i) (x i) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, kron]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  rw [Finset.prod_univ_sum]

/-- Pairing of product vectors. -/
theorem star_dot_prod (φ ψ : I → α → ℂ) :
    star (fun x : I → α => ∏ i, φ i (x i)) ⬝ᵥ (fun x : I → α => ∏ i, ψ i (x i))
      = ∏ i, star (φ i) ⬝ᵥ ψ i := by
  simp only [dotProduct, Pi.star_apply, star_prod]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ, Finset.prod_univ_sum]

theorem kron_unitary (M : I → Matrix α α ℂ) (hM : ∀ i, (M i)ᴴ * M i = 1) :
    (kron M)ᴴ * kron M = 1 := by
  ext y z
  have key : ∀ i, ∑ b, conj (M i b (y i)) * M i b (z i) = if y i = z i then 1 else 0 := by
    intro i
    have := congrFun (congrFun (hM i) (y i)) (z i)
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using this
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, kron, Matrix.one_apply, star_prod,
    Complex.star_def]
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_prod_pi (fun i b => conj (M i b (y i)) * M i b (z i))]
  simp_rw [key]
  rw [Finset.prod_boole]
  simp [funext_iff]

end kron

/-- Basis of `k` copies of an `n`-qubit system. -/
abbrev Copies (n k : ℕ) := Fin k → Fin n → Fin 2

/-- `ψ^{⊗k}`. -/
def copies {n : ℕ} (k : ℕ) (ψ : Ψ n) : Copies n k → ℂ := fun x => ∏ j, ψ (x j)

/-- The frame `u ∈ SU(2)^n` acting identically on all `k` copies. -/
def rotK {n : ℕ} (k : ℕ) (u : Fin n → Op1) : Matrix (Copies n k) (Copies n k) ℂ :=
  kron (fun _ : Fin k => kron u)

theorem copies_rot {n : ℕ} (k : ℕ) (u : Fin n → Op1) (ψ : Ψ n) :
    copies k (rot u ψ) = rotK k u *ᵥ copies k ψ := by
  unfold copies rotK
  rw [kron_mulVec_prod (fun _ : Fin k => kron u) (fun _ => ψ)]
  rfl

theorem star_copies_dot {n : ℕ} (k : ℕ) (ψ φ : Ψ n) :
    star (copies k ψ) ⬝ᵥ copies k φ = (star ψ ⬝ᵥ φ) ^ k := by
  unfold copies
  rw [star_dot_prod (fun _ : Fin k => ψ) (fun _ : Fin k => φ)]
  simp

theorem ip_eq_dot {n : ℕ} (ψ φ : Ψ n) : ip ψ φ = star ψ ⬝ᵥ φ := rfl

theorem rotK_unitary {n : ℕ} (k : ℕ) (u : Fin n → Op1) (hu : ∀ i, SU2 (u i)) :
    (rotK k u)ᴴ * rotK k u = 1 := by
  unfold rotK
  refine kron_unitary _ fun _ => ?_
  exact kron_unitary u fun i => (hu i).1

/-! ### Invariant tests and `P_e(k)` -/

/-- A `K`-invariant test on `k` copies: an effect commuting with all `rotK k u`, `u ∈ SU(2)^n`. -/
def IsInvEffect {n : ℕ} (k : ℕ) (E : Matrix (Copies n k) (Copies n k) ℂ) : Prop :=
  IsEffect E ∧ ∀ u : Fin n → Op1, (∀ i, SU2 (u i)) → rotK k u * E = E * rotK k u

/-- The frame-free error: the best equal-prior error of a `K`-invariant test between `ψ^{⊗k}` and
`(Θψ)^{⊗k}`. -/
noncomputable def Pe {n : ℕ} (k : ℕ) (ψ : Ψ n) : ℝ :=
  sInf {r | ∃ E, IsInvEffect (n := n) k E ∧ r = err E (copies k ψ) (copies k (Θ ψ))}

theorem isInvEffect_zero {n : ℕ} (k : ℕ) : IsInvEffect (n := n) k 0 := by
  refine ⟨⟨Matrix.PosSemidef.zero, by simpa using Matrix.PosSemidef.one⟩, fun u _ => by simp⟩

theorem err_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Matrix ι ι ℂ} (hE : IsEffect E)
    (a b : ι → ℂ) : 0 ≤ err E a b := by
  unfold err
  have h1 := qf_re_nonneg hE.1 a
  have h2 := qf_re_nonneg hE.2 b
  linarith

theorem Pe_nonneg {n : ℕ} (k : ℕ) (ψ : Ψ n) : 0 ≤ Pe k ψ := by
  refine Real.sInf_nonneg ?_
  rintro r ⟨E, hE, rfl⟩
  exact err_nonneg hE.1 _ _

theorem Pe_le_half {n : ℕ} (k : ℕ) (ψ : Ψ n) (hψ : nsq ψ = 1) : Pe k ψ ≤ 1 / 2 := by
  have hbdd : BddBelow {r | ∃ E, IsInvEffect (n := n) k E ∧ r = err E (copies k ψ) (copies k (Θ ψ))} :=
    ⟨0, by rintro r ⟨E, hE, rfl⟩; exact err_nonneg hE.1 _ _⟩
  refine (csInf_le hbdd ⟨0, isInvEffect_zero k, rfl⟩).trans ?_
  have : err (0 : Matrix (Copies n k) (Copies n k) ℂ) (copies k ψ) (copies k (Θ ψ))
      = (star (copies k (Θ ψ)) ⬝ᵥ copies k (Θ ψ)).re / 2 := by
    simp [err, qf]
  rw [this, star_copies_dot, ← ip_eq_dot, ip_self, nsq_Θ, hψ]
  simp

/-- Frame invariance of the error of an invariant test. -/
theorem qf_frame {ι : Type*} [Fintype ι] [DecidableEq ι] {M U : Matrix ι ι ℂ}
    (hU : Uᴴ * U = 1) (hc : U * M = M * U) (v w : ι → ℂ) :
    qf M (U *ᵥ v) (U *ᵥ w) = qf M v w := by
  unfold qf
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU, Matrix.vecMul_one]

theorem err_frame {n : ℕ} {k : ℕ} {E : Matrix (Copies n k) (Copies n k) ℂ} (hE : IsInvEffect k E)
    (u : Fin n → Op1) (hu : ∀ i, SU2 (u i)) (a b : Copies n k → ℂ) :
    err E (rotK k u *ᵥ a) (rotK k u *ᵥ b) = err E a b := by
  have hU := rotK_unitary k u hu
  have hc : rotK k u * (1 - E) = (1 - E) * rotK k u := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hE.2 u hu]
  unfold err
  rw [qf_frame hU (hE.2 u hu), qf_frame hU hc]

/-- Only the second hypothesis is rotated. -/
theorem err_rot_right {n : ℕ} {k : ℕ} {E : Matrix (Copies n k) (Copies n k) ℂ} (hE : IsInvEffect k E)
    (u : Fin n → Op1) (hu : ∀ i, SU2 (u i)) (a b : Copies n k → ℂ) :
    err E a (rotK k u *ᵥ b) = err E a b := by
  have hU := rotK_unitary k u hu
  have hc : rotK k u * (1 - E) = (1 - E) * rotK k u := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hE.2 u hu]
  unfold err
  rw [qf_frame hU hc]

theorem star_copies_self {n : ℕ} (k : ℕ) (ψ : Ψ n) (hψ : nsq ψ = 1) :
    star (copies k ψ) ⬝ᵥ copies k ψ = 1 := by
  rw [star_copies_dot, ← ip_eq_dot, ip_self, hψ]; simp

/-- **Lower bound on the frame-free error** (`thm:window`, upper half, one step).  For unit `ψ`, every
frame `u ∈ SU(2)^n` and every `k`, `|⟨ψ|uΘψ⟩|^{2k}/4 ≤ P_e(k)`. -/
theorem Pe_ge_of_rot {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) (u : Fin n → Op1) (hu : ∀ i, SU2 (u i))
    (k : ℕ) : Complex.normSq (ip ψ (rot u (Θ ψ))) ^ k / 4 ≤ Pe k ψ := by
  refine le_csInf ⟨_, 0, isInvEffect_zero k, rfl⟩ ?_
  rintro r ⟨E, hE, rfl⟩
  rw [← err_rot_right hE u hu, ← copies_rot]
  have hΘ : nsq (Θ ψ) = 1 := by rw [nsq_Θ, hψ]
  have hrot : nsq (rot u (Θ ψ)) = 1 := by rw [nsq_rot u hu, hΘ]
  have h := quarter_le_err hE.1 (star_copies_self k ψ hψ) (star_copies_self k (rot u (Θ ψ)) hrot)
  rw [star_copies_dot, ← ip_eq_dot, map_pow] at h
  exact h

/-- For `ε`-near-optimal frames: `P_e(k) ≥ F^k/4` for every `F < F_K(ψ)`. -/
theorem Pe_ge_quarter {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) {F : ℝ} (hF0 : 0 ≤ F) (hF : F < FKΘ ψ)
    (k : ℕ) : F ^ k / 4 ≤ Pe k ψ := by
  obtain ⟨r, ⟨u, hu, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (rotSet_nonempty ψ (Θ ψ)) hF
  refine le_trans ?_ (Pe_ge_of_rot ψ hψ u hu k)
  have := pow_le_pow_left₀ hF0 hlt.le k
  linarith

theorem Pe_pos {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) (k : ℕ) : 0 < Pe k ψ := by
  have hpos := FKΘ_pos ψ hψ
  have := Pe_ge_quarter ψ hψ (F := FKΘ ψ / 2) (by linarith) (by linarith) k
  have h2 : 0 < (FKΘ ψ / 2) ^ k / 4 := by positivity
  linarith

/-- `-(1/k) log P_e(k) ≤ -log F + (log 4)/k` for every `0 < F < F_K(ψ)`, `k ≥ 1`. -/
theorem neg_log_Pe_le {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) {F : ℝ} (hF0 : 0 < F) (hF : F < FKΘ ψ)
    {k : ℕ} (hk : 1 ≤ k) : -(1 / (k : ℝ)) * Real.log (Pe k ψ) ≤ -Real.log F + Real.log 4 / k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h := Real.log_le_log (by positivity) (Pe_ge_quarter ψ hψ hF0.le hF k)
  rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h
  have : -(1 / (k : ℝ)) * Real.log (Pe k ψ) ≤ -(1 / (k : ℝ)) * (k * Real.log F - Real.log 4) :=
    mul_le_mul_of_nonpos_left h (by have : 0 < 1 / (k : ℝ) := by positivity
                                    linarith)
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

/-- Eventual form of `limsup_k -(1/k) log P_e(k) ≤ C_K`: for every `c > C_K(ψ)`, eventually
`-(1/k) log P_e(k) ≤ c`. -/
theorem eventually_neg_log_Pe_le {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) {c : ℝ} (hc : CK ψ < c) :
    ∀ᶠ k : ℕ in Filter.atTop, -(1 / (k : ℝ)) * Real.log (Pe k ψ) ≤ c := by
  have hpos := FKΘ_pos ψ hψ
  set δ := (c - CK ψ) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set F := FKΘ ψ * Real.exp (-δ) with hFdef
  have hF0 : 0 < F := by positivity
  have hF : F < FKΘ ψ := by
    rw [hFdef]
    have : Real.exp (-δ) < 1 := by
      have := Real.exp_lt_exp.2 (show -δ < 0 by linarith)
      simpa using this
    nlinarith
  have hlogF : -Real.log F = CK ψ + δ := by
    rw [hFdef, Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    unfold CK; ring
  filter_upwards [Filter.eventually_ge_atTop (max 1 ⌈Real.log 4 / δ⌉₊)] with k hk
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : Real.log 4 / δ ≤ k := le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hk)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have h4 : Real.log 4 / k ≤ δ := by
    rw [div_le_iff₀ hkpos]
    rw [div_le_iff₀ hδpos] at hk2
    linarith
  have := neg_log_Pe_le ψ hψ hF0 hF hk1
  linarith

/-- **`thm:window`, upper half: `limsup_k -(1/k) log P_e(k) ≤ C_K(ψ)`** for every unit `ψ`. -/
theorem limsup_neg_log_Pe_le_CK {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) :
    Filter.limsup (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (Pe k ψ)) Filter.atTop ≤ CK ψ := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  have hcb : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (Pe k ψ)) := by
    refine Filter.isCoboundedUnder_le_of_le Filter.atTop (x := 0) fun k => ?_
    have h1 : Real.log (Pe k ψ) ≤ 0 :=
      Real.log_nonpos (Pe_nonneg k ψ) ((Pe_le_half k ψ hψ).trans (by norm_num))
    have h2 : 0 ≤ 1 / (k : ℝ) := by positivity
    nlinarith
  exact Filter.limsup_le_of_le hcb (eventually_neg_log_Pe_le ψ hψ hc)

end FormalResearch.FrameFree.Helstrom
