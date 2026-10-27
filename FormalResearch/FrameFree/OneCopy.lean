import FormalResearch.FrameFree.Foundations
import FormalResearch.FrameFree.Sharing
import FormalResearch.FrameFree.ScalarChirality
import FormalResearch.FrameFree.Unify
import FormalResearch.FrameFree.Ceilings

open scoped ComplexConjugate Matrix BigOperators

/-!
# What one copy sees (Paper P, `sec1_setting.tex`, `thm:onecopy`)

Namespace `FormalResearch.FrameFree.OneCopy`.  `NQubit.ip`/`NQubit.SU2` are always written qualified
(the namespace `FormalResearch.FrameFree` has its own four-qubit `ip`, `SU2`).

## Proved here

* **Permutation operators** on `Ψ n` (`permN σ ψ = ψ ∘ (· ∘ σ)`): `rot_permN` (a local operator `rot u`
  with `u ∘ σ = u` commutes with `permN σ`; no unitarity or determinant condition needed),
  `Θ_permN` (`Θ` commutes with `permN σ`), `ip_permN` (`permN σ` has adjoint `permN σ⁻¹`).
* **Odd observables** `oddOp σ = i (P_σ - P_σ⁻¹)` (`Prop oddwords` (iii), any `n`, any `σ`):
  `ip_oddOp` (Hermitian), `oddOp_rot` (commutes with every block-constant local operator), `Θ_oddOp`
  (`Θ`-odd: `Θ (oddOp σ ψ) = - oddOp σ (Θ ψ)`).
* **`thm:onecopy` (c), general version** (`FKΘs_eq_zero_of_odd`, `FCΘs_eq_zero_of_odd`).  If the
  permutation `σ` preserves the blocks of the sharing pattern `g` and `ψ` is an eigenvector of
  `oddOp σ` with nonzero eigenvalue, then `⟨ψ|rot (v ∘ g) Θψ⟩ = 0` for *every* choice of one-qubit
  operators `v` (`ip_rot_Θ_eq_zero`), so `F_K^π(ψ) = F_C^π(ψ) = 0`.
* **Scalar chirality** `chiN i j l = (i/4)(C - C⁻¹)`, `C = SWAP_{il} SWAP_{ij}` on `n` qubits
  (`chiN_rot`, `ip_chiN`, `Θ_chiN`: commutes with block frames, Hermitian, `Θ`-odd), and
  `FKΘs_eq_zero_of_chiN`, `FCΘs_eq_zero_of_chiN`: three spins `i, j, l` in one block and `ψ` an eigenvector
  of `chiN i j l` with eigenvalue `μ ≠ 0` give `F_K^π = F_C^π = 0` (`n` arbitrary), and
  `FKΘs_FCΘs_tens_eq_zero_of_chiN` is the paper's "eigenvector on the three spins, tensored with any
  state `φ` of the other spins" (`chiN_tens`).
* **Link to the four-qubit operator** `ScalarChirality.chi` (`S_i·(S_j×S_l)` written in Paulis):
  `toN_chi : toN (chi i j l ψ) = chiN i j l (toN ψ)` (from `chi_eq_cyc`), and
  `FKΘs_eq_zero_of_chi`, `FCΘs_eq_zero_of_chi` for `ψ : Psi` with `chi i j l ψ = μ • ψ`.
* `M4_triple_of_chirality`: `thm:m4sharing` (a) (`F_K^π(M₄) = F_C^π(M₄) = 0` when a block has three
  spins) re-derived from the chirality eigenvalues `chi_M4_012, …` of `ScalarChirality`; it agrees with
  `Sharing.FKΘs_M4_triple`, `FCΘs_M4_triple`, whose Weyl-algebra proofs it does not need.
* **`thm:onecopy` (a), the part that is elementary**: `FKΘs_eq_zero_iff`, `FCΘs_eq_zero_iff`
  (`F_K^π = 0` iff `⟨ψ|rot (v∘g) Θψ⟩ = 0` for all `SU(2)` frames, `F_C^π = 0` iff it vanishes for all
  `SL(2,ℂ)` frames) and `FKΘs_eq_zero_of_FCΘs_eq_zero` (unit `ψ`; `F_K^π ≤ F_C^π`).
* **`thm:hierarchy` (i)**: `FKΘ_eq_FCΘ_eq_one_of_le_two` (`F_K = F_C = 1` for one or two qubits, in the
  `Ceilings` form of `F_C`) and `FCΘs_id_eq_one_of_le_two` (the same in the `Sharing` form with
  independent frames).  **`thm:hierarchy` (iii)**: `negLog_FC_four_le_log_two`
  (`-log F_C ≤ log 2` for four qubits, under the `RealRep3` hypothesis of `Ceilings`).

## NOT proved here

* **`thm:onecopy` (a), the converse `F_K^π = 0 ⟹ F_C^π = 0`.**  The paper obtains it from Schur--Weyl
  duality: the complex span of `K_π` contains `𝒢_π`; equivalently, a polynomial vanishing on
  `SU(2)^b` vanishes on `SL(2,ℂ)^b` (Zariski density).  Neither is in Mathlib in usable form; the same gap
  is recorded in `Sharing.FCΘs_of_invariant`.  Only `F_C^π = 0 ⟹ F_K^π = 0` is proved in general; for the
  chirality mechanism of (c) both vanish directly.
* **`thm:onecopy` (a), orthogonal supports of the one-copy twirls** and **(b)** (twirl equality and
  `F_K^π > 0` for blocks of at most two spins): these need the Haar twirl over `K_π` (or Schur--Weyl
  duality), which is not formalised.  `F_K^π > 0` for such patterns is not elementary either (the Pauli
  floor `2⁻ⁿ` of `Foundations.two_pow_neg_le_FKΘ` is for independent frames only).
* The eigenvalue spectrum of `χ` (`±√3/4`, `0` on spin `3/2`) is `ScalarChirality.chi_cube`,
  `chi3_multiplicities`; it is not needed for (c).
-/

namespace FormalResearch.FrameFree.OneCopy

open FormalResearch.FrameFree.NQubit (Ψ Op1 rot Θ cj nsq)
open FormalResearch.FrameFree.Sharing (FKs FCs FKΘs FCΘs)

/-! ## Part 1. Permutation operators and linearity -/

/-- The permutation operator `(P_σ ψ)(x) = ψ(x ∘ σ)` on `n` qubits. -/
def permN {n : ℕ} (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) : Ψ n := fun x => ψ (x ∘ σ)

theorem permN_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (ψ : Ψ n) :
    permN σ (permN τ ψ) = permN (σ * τ) ψ := rfl

theorem permN_one {n : ℕ} (ψ : Ψ n) : permN (1 : Equiv.Perm (Fin n)) ψ = ψ := rfl

theorem permN_cj {n : ℕ} (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) : cj (permN σ ψ) = permN σ (cj ψ) := rfl

theorem permN_sub {n : ℕ} (σ : Equiv.Perm (Fin n)) (a b : Ψ n) :
    permN σ (a - b) = permN σ a - permN σ b := rfl

theorem permN_smul {n : ℕ} (σ : Equiv.Perm (Fin n)) (c : ℂ) (a : Ψ n) :
    permN σ (c • a) = c • permN σ a := rfl

theorem rot_sub {n : ℕ} (u : Fin n → Op1) (a b : Ψ n) : rot u (a - b) = rot u a - rot u b := by
  funext x
  simp only [rot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem rot_smul {n : ℕ} (u : Fin n → Op1) (c : ℂ) (a : Ψ n) : rot u (c • a) = c • rot u a := by
  funext x
  simp only [rot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem cj_sub {n : ℕ} (a b : Ψ n) : cj (a - b) = cj a - cj b := by
  funext x; simp [cj]

theorem cj_smul {n : ℕ} (c : ℂ) (a : Ψ n) : cj (c • a) = conj c • cj a := by
  funext x; simp [cj]

theorem Θ_sub {n : ℕ} (a b : Ψ n) : Θ (a - b) = Θ a - Θ b := by
  rw [NQubit.Θ_eq_rot, NQubit.Θ_eq_rot, NQubit.Θ_eq_rot, cj_sub, rot_sub]

theorem Θ_smul {n : ℕ} (c : ℂ) (a : Ψ n) : Θ (c • a) = conj c • Θ a := by
  rw [NQubit.Θ_eq_rot, NQubit.Θ_eq_rot, cj_smul, rot_smul]

theorem ip_sub_right {n : ℕ} (φ a b : Ψ n) :
    NQubit.ip φ (a - b) = NQubit.ip φ a - NQubit.ip φ b := by
  simp only [NQubit.ip, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem ip_smul_right {n : ℕ} (φ a : Ψ n) (c : ℂ) : NQubit.ip φ (c • a) = c * NQubit.ip φ a := by
  simp only [NQubit.ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem ip_smul_left {n : ℕ} (φ a : Ψ n) (c : ℂ) : NQubit.ip (c • φ) a = conj c * NQubit.ip φ a := by
  simp only [NQubit.ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem ip_sub_left {n : ℕ} (a b φ : Ψ n) :
    NQubit.ip (a - b) φ = NQubit.ip a φ - NQubit.ip b φ := by
  simp only [NQubit.ip, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

/-- A local operator `rot u` whose factors are constant along the cycles of `σ` commutes with
`P_σ` (no unitarity or determinant condition). -/
theorem rot_permN {n : ℕ} (u : Fin n → Op1) (σ : Equiv.Perm (Fin n)) (hu : ∀ k, u (σ k) = u k)
    (ψ : Ψ n) : rot u (permN σ ψ) = permN σ (rot u ψ) := by
  funext x
  show ∑ y, (∏ i, u i (x i) (y i)) * ψ (y ∘ σ) = ∑ z, (∏ i, u i (x (σ i)) (z i)) * ψ z
  have e : ∀ f : (Fin n → Fin 2) → ℂ, ∑ y, f (y ∘ σ) = ∑ z, f z := fun f =>
    Equiv.sum_comp (σ.symm.arrowCongr (Equiv.refl (Fin 2))) f
  rw [← e (fun z => (∏ i, u i (x (σ i)) (z i)) * ψ z)]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h : ∏ i, u i (x (σ i)) (y (σ i)) = ∏ i, u i (x i) (y i) := by
    rw [← Equiv.prod_comp σ (fun k => u k (x k) (y k))]
    exact Finset.prod_congr rfl fun i _ => by rw [hu i]
  simp only [Function.comp_apply, h]

/-- `Θ` commutes with every permutation of the qubits. -/
theorem Θ_permN {n : ℕ} (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) : Θ (permN σ ψ) = permN σ (Θ ψ) := by
  rw [NQubit.Θ_eq_rot, NQubit.Θ_eq_rot, permN_cj]
  exact rot_permN _ σ (fun _ => rfl) _

/-- The adjoint of `P_σ` is `P_{σ⁻¹}`. -/
theorem ip_permN {n : ℕ} (σ : Equiv.Perm (Fin n)) (φ ψ : Ψ n) :
    NQubit.ip φ (permN σ ψ) = NQubit.ip (permN σ⁻¹ φ) ψ := by
  have e : ∀ f : (Fin n → Fin 2) → ℂ, ∑ y, f (y ∘ σ) = ∑ z, f z := fun f =>
    Equiv.sum_comp (σ.symm.arrowCongr (Equiv.refl (Fin 2))) f
  unfold NQubit.ip permN
  rw [← e (fun z => conj (φ (z ∘ ⇑σ⁻¹)) * ψ z)]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h2 : (y ∘ ⇑σ) ∘ ⇑σ⁻¹ = y := by funext k; simp
  rw [h2]

/-! ## Part 2. Odd observables -/

/-- The odd observable `i (P_σ - P_σ⁻¹)` of `Prop oddwords` (iii) (twice the paper's normalised one,
`i/2 (W - W⁻¹)`, up to the factor `2`). -/
noncomputable def oddOp {n : ℕ} (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) : Ψ n :=
  Complex.I • (permN σ ψ - permN σ⁻¹ ψ)

/-- `oddOp σ` is Hermitian. -/
theorem ip_oddOp {n : ℕ} (σ : Equiv.Perm (Fin n)) (φ ψ : Ψ n) :
    NQubit.ip φ (oddOp σ ψ) = NQubit.ip (oddOp σ φ) ψ := by
  unfold oddOp
  rw [ip_smul_right, ip_smul_left, ip_sub_right, ip_sub_left, ip_permN, ip_permN, inv_inv]
  simp only [Complex.conj_I]
  ring

/-- `oddOp σ` commutes with every local operator that is constant along the cycles of `σ`. -/
theorem oddOp_rot {n : ℕ} (u : Fin n → Op1) (σ : Equiv.Perm (Fin n)) (hu : ∀ k, u (σ k) = u k)
    (ψ : Ψ n) : oddOp σ (rot u ψ) = rot u (oddOp σ ψ) := by
  have hu' : ∀ k, u (σ⁻¹ k) = u k := fun k => by
    have := hu (σ⁻¹ k)
    simpa using this.symm
  unfold oddOp
  rw [rot_smul, rot_sub, rot_permN u σ hu, rot_permN u σ⁻¹ hu']

/-- `oddOp σ` is `Θ`-odd. -/
theorem Θ_oddOp {n : ℕ} (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) :
    Θ (oddOp σ ψ) = - oddOp σ (Θ ψ) := by
  unfold oddOp
  rw [Θ_smul, Θ_sub, Θ_permN, Θ_permN, Complex.conj_I, neg_smul]

/-! ## Part 3. `thm:onecopy` (c), general version -/

/-- The core of `thm:onecopy` (c): an eigenvector `ψ` of `oddOp σ` with eigenvalue `ν ≠ 0` is orthogonal
to `rot u Θψ` for every local operator `u` constant along the cycles of `σ`. -/
theorem ip_rot_Θ_eq_zero_of_odd {n : ℕ} (σ : Equiv.Perm (Fin n)) (u : Fin n → Op1)
    (hu : ∀ k, u (σ k) = u k) (ψ : Ψ n) (ν : ℂ) (hν : ν ≠ 0) (hψ : oddOp σ ψ = ν • ψ) :
    NQubit.ip ψ (rot u (Θ ψ)) = 0 := by
  set ξ := rot u (Θ ψ) with hξ
  have h2 : oddOp σ (Θ ψ) = (-conj ν) • Θ ψ := by
    have := Θ_oddOp σ ψ
    rw [hψ, Θ_smul] at this
    rw [neg_smul]
    calc oddOp σ (Θ ψ) = -(-(oddOp σ (Θ ψ))) := (neg_neg _).symm
      _ = -(conj ν • Θ ψ) := by rw [← this]
  have h1 : oddOp σ ξ = (-conj ν) • ξ := by
    rw [hξ, oddOp_rot u σ hu, h2, rot_smul]
  have h4 := ip_oddOp σ ψ ξ
  rw [h1, hψ, ip_smul_left, ip_smul_right] at h4
  have : (2 * conj ν) * NQubit.ip ψ ξ = 0 := by linear_combination -h4
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (by simpa using h) hν
  · exact h

theorem ip_rot_Θ_eq_zero {n : ℕ} {β : Type*} (g : Fin n → β) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ k, g (σ k) = g k) (ψ : Ψ n) (ν : ℂ) (hν : ν ≠ 0) (hψ : oddOp σ ψ = ν • ψ)
    (v : β → Op1) : NQubit.ip ψ (rot (fun i => v (g i)) (Θ ψ)) = 0 :=
  ip_rot_Θ_eq_zero_of_odd σ _ (fun k => by simp only [hσ k]) ψ ν hν hψ

/-! ### Elementary reformulations of `F_K^π = 0`, `F_C^π = 0` -/

section Zero

variable {n : ℕ} {β : Type*}

theorem FKs_eq_zero_of_forall (g : Fin n → β) (ψ φ : Ψ n)
    (h : ∀ v : β → Op1, (∀ b, NQubit.SU2 (v b)) → NQubit.ip ψ (rot (fun i => v (g i)) φ) = 0) :
    FKs g ψ φ = 0 := by
  unfold FKs
  apply le_antisymm
  · refine csSup_le (Sharing.shSet_nonempty g ψ φ) ?_
    rintro r ⟨v, hv, rfl⟩
    rw [h v hv]; simp
  · refine Real.sSup_nonneg ?_
    rintro r ⟨v, hv, rfl⟩
    exact Complex.normSq_nonneg _

theorem FKs_eq_zero_iff (g : Fin n → β) (ψ φ : Ψ n) :
    FKs g ψ φ = 0 ↔
      ∀ v : β → Op1, (∀ b, NQubit.SU2 (v b)) → NQubit.ip ψ (rot (fun i => v (g i)) φ) = 0 := by
  refine ⟨fun h v hv => ?_, FKs_eq_zero_of_forall g ψ φ⟩
  have h1 := Sharing.le_FKs g ψ φ v hv
  rw [h] at h1
  exact Complex.normSq_eq_zero.1 (le_antisymm h1 (Complex.normSq_nonneg _))

theorem ip_eq_zero_of_nsq_zero {n : ℕ} (ψ ξ : Ψ n) (h : nsq ξ = 0) : NQubit.ip ψ ξ = 0 := by
  have hx : ∀ x, ξ x = 0 := fun x => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Complex.normSq_nonneg (ξ x))).1 h x
      (Finset.mem_univ x)
    exact Complex.normSq_eq_zero.1 this
  simp [NQubit.ip, hx]

theorem FCs_eq_zero_of_forall (g : Fin n → β) (ψ φ : Ψ n)
    (h : ∀ v : β → Op1, (∀ b, (v b).det = 1) → NQubit.ip ψ (rot (fun i => v (g i)) φ) = 0) :
    FCs g ψ φ = 0 := by
  unfold FCs
  apply le_antisymm
  · refine csSup_le (Sharing.fiSet_nonempty g ψ φ) ?_
    rintro r ⟨v, hv, rfl⟩
    rw [h v hv]; simp
  · refine Real.sSup_nonneg ?_
    rintro r ⟨v, hv, rfl⟩
    exact div_nonneg (Complex.normSq_nonneg _) (Sharing.nsq_nonneg _)

theorem FCs_eq_zero_iff (g : Fin n → β) (ψ φ : Ψ n) :
    FCs g ψ φ = 0 ↔
      ∀ v : β → Op1, (∀ b, (v b).det = 1) → NQubit.ip ψ (rot (fun i => v (g i)) φ) = 0 := by
  refine ⟨fun h v hv => ?_, FCs_eq_zero_of_forall g ψ φ⟩
  have h1 : Complex.normSq (NQubit.ip ψ (rot (fun i => v (g i)) φ)) /
      nsq (rot (fun i => v (g i)) φ) ≤ FCs g ψ φ :=
    le_csSup (Sharing.fiSet_bddAbove g ψ φ) ⟨v, hv, rfl⟩
  rw [h] at h1
  by_cases hn : nsq (rot (fun i => v (g i)) φ) = 0
  · exact ip_eq_zero_of_nsq_zero _ _ hn
  · have hpos : 0 < nsq (rot (fun i => v (g i)) φ) :=
      lt_of_le_of_ne (Sharing.nsq_nonneg _) (Ne.symm hn)
    have h2 : Complex.normSq (NQubit.ip ψ (rot (fun i => v (g i)) φ)) ≤ 0 := by
      have := (div_le_iff₀ hpos).1 h1
      simpa using this
    exact Complex.normSq_eq_zero.1 (le_antisymm h2 (Complex.normSq_nonneg _))

theorem FKΘs_eq_zero_iff (g : Fin n → β) (ψ : Ψ n) :
    FKΘs g ψ = 0 ↔
      ∀ v : β → Op1, (∀ b, NQubit.SU2 (v b)) → NQubit.ip ψ (rot (fun i => v (g i)) (Θ ψ)) = 0 :=
  FKs_eq_zero_iff g ψ (Θ ψ)

theorem FCΘs_eq_zero_iff (g : Fin n → β) (ψ : Ψ n) :
    FCΘs g ψ = 0 ↔
      ∀ v : β → Op1, (∀ b, (v b).det = 1) → NQubit.ip ψ (rot (fun i => v (g i)) (Θ ψ)) = 0 :=
  FCs_eq_zero_iff g ψ (Θ ψ)

/-- **`thm:onecopy` (a)**, the direction `F_C^π = 0 ⟹ F_K^π = 0` (unit `ψ`; the converse is the
Zariski-density step, not formalised). -/
theorem FKΘs_eq_zero_of_FCΘs_eq_zero (g : Fin n → β) (ψ : Ψ n) (hψ : nsq ψ = 1)
    (h : FCΘs g ψ = 0) : FKΘs g ψ = 0 := by
  have h1 : FKΘs g ψ ≤ FCΘs g ψ := Sharing.FKs_le_FCs g ψ (Θ ψ) (by rw [NQubit.nsq_Θ, hψ])
  have h2 : 0 ≤ FKΘs g ψ := Real.sSup_nonneg (by
    rintro r ⟨v, hv, rfl⟩
    exact Complex.normSq_nonneg _)
  linarith

/-- Chirality (and any odd observable) kills both overlaps. -/
theorem FKΘs_eq_zero_of_odd (g : Fin n → β) (σ : Equiv.Perm (Fin n)) (hσ : ∀ k, g (σ k) = g k)
    (ψ : Ψ n) (ν : ℂ) (hν : ν ≠ 0) (hψ : oddOp σ ψ = ν • ψ) : FKΘs g ψ = 0 :=
  (FKΘs_eq_zero_iff g ψ).2 fun v _ => ip_rot_Θ_eq_zero g σ hσ ψ ν hν hψ v

theorem FCΘs_eq_zero_of_odd (g : Fin n → β) (σ : Equiv.Perm (Fin n)) (hσ : ∀ k, g (σ k) = g k)
    (ψ : Ψ n) (ν : ℂ) (hν : ν ≠ 0) (hψ : oddOp σ ψ = ν • ψ) : FCΘs g ψ = 0 :=
  (FCΘs_eq_zero_iff g ψ).2 fun v _ => ip_rot_Θ_eq_zero g σ hσ ψ ν hν hψ v

end Zero

/-! ## Part 4. The scalar chirality `χ_{ijl}` on `n` qubits -/

/-- The scalar chirality `χ_{ijl} = S_i·(S_j×S_l) = (i/4)(C - C⁻¹)`, `C = SWAP_{il} SWAP_{ij}` (`n` qubits).
The identification with the Pauli expression is `ScalarChirality.chi_eq_cyc` (four qubits), see
`toN_chi`. -/
noncomputable def chiN {n : ℕ} (i j l : Fin n) (ψ : Ψ n) : Ψ n :=
  (Complex.I / 4) • (permN (Equiv.swap i l * Equiv.swap i j) ψ -
    permN (Equiv.swap i j * Equiv.swap i l) ψ)

theorem inv_cycle {n : ℕ} (i j l : Fin n) :
    (Equiv.swap i l * Equiv.swap i j)⁻¹ = Equiv.swap i j * Equiv.swap i l := by
  rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]

theorem oddOp_cycle {n : ℕ} (i j l : Fin n) (ψ : Ψ n) :
    oddOp (Equiv.swap i l * Equiv.swap i j) ψ = (4 : ℂ) • chiN i j l ψ := by
  unfold oddOp chiN
  rw [inv_cycle, smul_smul]
  have : (4 : ℂ) * (Complex.I / 4) = Complex.I := by ring
  rw [this]

/-- The cycle `C = SWAP_{il} SWAP_{ij}` preserves the blocks when `i, j, l` lie in one block. -/
theorem block_cycle {n : ℕ} {β : Type*} (g : Fin n → β) (i j l : Fin n) (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) (hgij : g i = g j) (hgjl : g j = g l) (k : Fin n) :
    g ((Equiv.swap i l * Equiv.swap i j) k) = g k := by
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  by_cases hki : k = i
  · rw [hki, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hij.symm hjl]
    exact hgij.symm
  by_cases hkj : k = j
  · rw [hkj, Equiv.swap_apply_right, Equiv.swap_apply_left]
    exact hgjl.symm
  by_cases hkl : k = l
  · rw [hkl, Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm, Equiv.swap_apply_right]
    exact hgij.trans hgjl
  rw [Equiv.swap_apply_of_ne_of_ne hki hkj, Equiv.swap_apply_of_ne_of_ne hki hkl]

theorem conj_quarter : (starRingEnd ℂ) (1 / 4 : ℂ) = 1 / 4 := by
  rw [map_div₀, map_one, map_ofNat]

theorem chiN_eq_oddOp {n : ℕ} (i j l : Fin n) (ψ : Ψ n) :
    chiN i j l ψ = (1 / 4 : ℂ) • oddOp (Equiv.swap i l * Equiv.swap i j) ψ := by
  rw [oddOp_cycle, smul_smul]
  norm_num

/-- `χ_{ijl}` commutes with every local operator that is constant on `i, j, l` (in particular with a
shared frame, rotation or `SL(2,ℂ)`). -/
theorem chiN_rot {n : ℕ} (u : Fin n → Op1) (i j l : Fin n) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hui : u i = u j) (huj : u j = u l) (ψ : Ψ n) :
    chiN i j l (rot u ψ) = rot u (chiN i j l ψ) := by
  rw [chiN_eq_oddOp, chiN_eq_oddOp, oddOp_rot u _ (block_cycle u i j l hij hil hjl hui huj), rot_smul]

/-- `χ_{ijl}` is Hermitian. -/
theorem ip_chiN {n : ℕ} (i j l : Fin n) (φ ψ : Ψ n) :
    NQubit.ip φ (chiN i j l ψ) = NQubit.ip (chiN i j l φ) ψ := by
  rw [chiN_eq_oddOp, chiN_eq_oddOp, ip_smul_right, ip_smul_left, ip_oddOp, conj_quarter]

/-- `χ_{ijl}` is `Θ`-odd. -/
theorem Θ_chiN {n : ℕ} (i j l : Fin n) (ψ : Ψ n) : Θ (chiN i j l ψ) = - chiN i j l (Θ ψ) := by
  rw [chiN_eq_oddOp, chiN_eq_oddOp, Θ_smul, Θ_oddOp, conj_quarter, smul_neg]

/-- **`thm:onecopy` (c)**, `n` qubits: three spins `i, j, l` in one block of the sharing pattern and `ψ`
an eigenvector of the scalar chirality `χ_{ijl}` with eigenvalue `μ ≠ 0` have `F_K^π(ψ) = 0`. -/
theorem FKΘs_eq_zero_of_chiN {n : ℕ} {β : Type*} (g : Fin n → β) (i j l : Fin n) (hij : i ≠ j)
    (hil : i ≠ l) (hjl : j ≠ l) (hgij : g i = g j) (hgjl : g j = g l) (ψ : Ψ n) (μ : ℂ) (hμ : μ ≠ 0)
    (hψ : chiN i j l ψ = μ • ψ) : FKΘs g ψ = 0 := by
  refine FKΘs_eq_zero_of_odd g _ (block_cycle g i j l hij hil hjl hgij hgjl) ψ (4 * μ)
    (mul_ne_zero (by norm_num) hμ) ?_
  rw [oddOp_cycle, hψ, smul_smul]

/-- **`thm:onecopy` (c)**, `n` qubits, filters: the same hypotheses give `F_C^π(ψ) = 0`. -/
theorem FCΘs_eq_zero_of_chiN {n : ℕ} {β : Type*} (g : Fin n → β) (i j l : Fin n) (hij : i ≠ j)
    (hil : i ≠ l) (hjl : j ≠ l) (hgij : g i = g j) (hgjl : g j = g l) (ψ : Ψ n) (μ : ℂ) (hμ : μ ≠ 0)
    (hψ : chiN i j l ψ = μ • ψ) : FCΘs g ψ = 0 := by
  refine FCΘs_eq_zero_of_odd g _ (block_cycle g i j l hij hil hjl hgij hgjl) ψ (4 * μ)
    (mul_ne_zero (by norm_num) hμ) ?_
  rw [oddOp_cycle, hψ, smul_smul]

/-! ### Tensoring with a state of the other spins -/

theorem tens_sub {k m : ℕ} (a b : Ψ k) (φ : Ψ m) :
    NQubit.tens (a - b) φ = NQubit.tens a φ - NQubit.tens b φ := by
  funext x; simp [NQubit.tens, sub_mul]

theorem tens_smul {k m : ℕ} (c : ℂ) (a : Ψ k) (φ : Ψ m) :
    NQubit.tens (c • a) φ = c • NQubit.tens a φ := by
  funext x; simp [NQubit.tens, mul_assoc]

/-- A swap inside the first `k` of `k + m` spins acts on `ψ ⊗ φ` through `ψ` alone. -/
theorem permN_swap_tens {k m : ℕ} (a b : Fin k) (ψ : Ψ k) (φ : Ψ m) :
    permN (Equiv.swap (Fin.castAdd m a) (Fin.castAdd m b)) (NQubit.tens ψ φ) =
      NQubit.tens (permN (Equiv.swap a b) ψ) φ := by
  funext x
  have h1 : ∀ i : Fin k, Equiv.swap (Fin.castAdd m a) (Fin.castAdd m b) (Fin.castAdd m i) =
      Fin.castAdd m (Equiv.swap a b i) := fun i =>
    (Fin.castAdd_injective k m).swap_apply a b i
  have h2 : ∀ j : Fin m, Equiv.swap (Fin.castAdd m a) (Fin.castAdd m b) (Fin.natAdd k j) =
      Fin.natAdd k j := fun j => by
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_ <;>
    · intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      have := a.isLt
      have := b.isLt
      omega
  simp only [permN, NQubit.tens, Function.comp_apply, h1, h2]
  rfl

/-- The cycle `C` of three spins inside the first `k` acts on `ψ ⊗ φ` through `ψ`. -/
theorem chiN_tens {k m : ℕ} (i j l : Fin k) (ψ : Ψ k) (φ : Ψ m) :
    chiN (Fin.castAdd m i) (Fin.castAdd m j) (Fin.castAdd m l) (NQubit.tens ψ φ) =
      NQubit.tens (chiN i j l ψ) φ := by
  unfold chiN
  rw [tens_smul, tens_sub, ← permN_mul, ← permN_mul, permN_swap_tens, permN_swap_tens,
    ← permN_mul, ← permN_mul, permN_swap_tens, permN_swap_tens]

/-- **`thm:onecopy` (c), as stated in the paper**: an eigenvector `ψ` (eigenvalue `μ ≠ 0`) of the chirality
of three spins `i, j, l` lying in one block, tensored with any state `φ` of the other spins, has
`F_K^π = F_C^π = 0`. -/
theorem FKΘs_FCΘs_tens_eq_zero_of_chiN {k m : ℕ} {β : Type*} (g : Fin (k + m) → β) (i j l : Fin k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (hgij : g (Fin.castAdd m i) = g (Fin.castAdd m j))
    (hgjl : g (Fin.castAdd m j) = g (Fin.castAdd m l)) (ψ : Ψ k) (φ : Ψ m) (μ : ℂ) (hμ : μ ≠ 0)
    (hψ : chiN i j l ψ = μ • ψ) :
    FKΘs g (NQubit.tens ψ φ) = 0 ∧ FCΘs g (NQubit.tens ψ φ) = 0 := by
  have hc : ∀ {a b : Fin k}, a ≠ b → Fin.castAdd m a ≠ Fin.castAdd m b := fun h =>
    (Fin.castAdd_injective k m).ne h
  have he : chiN (Fin.castAdd m i) (Fin.castAdd m j) (Fin.castAdd m l) (NQubit.tens ψ φ) =
      μ • NQubit.tens ψ φ := by
    rw [chiN_tens, hψ, tens_smul]
  exact ⟨FKΘs_eq_zero_of_chiN g _ _ _ (hc hij) (hc hil) (hc hjl) hgij hgjl _ μ hμ he,
    FCΘs_eq_zero_of_chiN g _ _ _ (hc hij) (hc hil) (hc hjl) hgij hgjl _ μ hμ he⟩

/-! ## Part 5. Link to the four-qubit Pauli expression `ScalarChirality.chi` -/

open FormalResearch.FourQubitEntropy (Psi) in
theorem toN_permPsi (σ : Equiv.Perm (Fin 4)) (ψ : Psi) :
    Unify.toN (ScalarChirality.permPsi σ ψ) = permN σ (Unify.toN ψ) := by
  funext x
  exact ScalarChirality.ev_perm σ ψ x

open FormalResearch.FourQubitEntropy (Psi) in
/-- The four-qubit `χ_{ijl} = (1/8) Σ ε_{abc} σ_a σ_b σ_c` of `ScalarChirality` is `chiN` under the bridge
`toN : Psi → Ψ 4`. -/
theorem toN_chi (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (ψ : Psi) :
    Unify.toN (ScalarChirality.chi i j l ψ) = chiN i j l (Unify.toN ψ) := by
  have h : ScalarChirality.chi i j l ψ =
      (Complex.I / 4) • (ScalarChirality.permPsi (Equiv.swap i l * Equiv.swap i j) ψ -
        ScalarChirality.permPsi (Equiv.swap i j * Equiv.swap i l) ψ) := by
    rw [ScalarChirality.chi_eq_cyc i j l hij hil hjl]
    rfl
  rw [h]
  unfold chiN
  rw [← toN_permPsi, ← toN_permPsi]
  rfl

open FormalResearch.FourQubitEntropy (Psi) in
/-- **`thm:onecopy` (c)** for the four-qubit operator `ScalarChirality.chi`. -/
theorem FKΘs_eq_zero_of_chi {β : Type*} (g : Fin 4 → β) (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) (hgij : g i = g j) (hgjl : g j = g l) (ψ : Psi) (μ : ℂ) (hμ : μ ≠ 0)
    (hψ : ScalarChirality.chi i j l ψ = μ • ψ) : FKΘs g (Unify.toN ψ) = 0 := by
  refine FKΘs_eq_zero_of_chiN g i j l hij hil hjl hgij hgjl _ μ hμ ?_
  rw [← toN_chi i j l hij hil hjl, hψ]
  rfl

open FormalResearch.FourQubitEntropy (Psi) in
theorem FCΘs_eq_zero_of_chi {β : Type*} (g : Fin 4 → β) (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) (hgij : g i = g j) (hgjl : g j = g l) (ψ : Psi) (μ : ℂ) (hμ : μ ≠ 0)
    (hψ : ScalarChirality.chi i j l ψ = μ • ψ) : FCΘs g (Unify.toN ψ) = 0 := by
  refine FCΘs_eq_zero_of_chiN g i j l hij hil hjl hgij hgjl _ μ hμ ?_
  rw [← toN_chi i j l hij hil hjl, hψ]
  rfl

/-- **`thm:m4sharing` (a)** from the chirality mechanism: `M₄` is an eigenvector, with eigenvalue
`±√3/4 ≠ 0`, of the chirality of each of its four triples (`ScalarChirality.chi_M4_012, …`), so any block
with three spins kills both overlaps.  (Same statement as `Sharing.FKΘs_M4_triple`,
`Sharing.FCΘs_M4_triple`, which are proved by the Weyl-algebra computation.) -/
theorem M4_triple_of_chirality {β : Type*} (g : Fin 4 → β) (h : Sharing.HasTriple g) :
    FKΘs g Sharing.M4n = 0 ∧ FCΘs g Sharing.M4n = 0 := by
  have hs : ((Real.sqrt 3 / 4 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have hn : ((-(Real.sqrt 3 / 4) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by
    have : (0 : ℝ) < Real.sqrt 3 / 4 := by positivity
    linarith)
  have key : ∀ (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (hgij : g i = g j)
      (hgjl : g j = g l) (μ : ℂ), μ ≠ 0 →
      ScalarChirality.chi i j l FormalResearch.FourQubitEntropy.M4 =
        μ • FormalResearch.FourQubitEntropy.M4 →
      FKΘs g Sharing.M4n = 0 ∧ FCΘs g Sharing.M4n = 0 := fun i j l hij hil hjl hgij hgjl μ hμ hψ =>
    ⟨FKΘs_eq_zero_of_chi g i j l hij hil hjl hgij hgjl _ μ hμ hψ,
     FCΘs_eq_zero_of_chi g i j l hij hil hjl hgij hgjl _ μ hμ hψ⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key 0 1 2 (by decide) (by decide) (by decide) h1 h2 _ hn ScalarChirality.chi_M4_012
  · exact key 0 1 3 (by decide) (by decide) (by decide) h1 h2 _ hs ScalarChirality.chi_M4_013
  · exact key 0 2 3 (by decide) (by decide) (by decide) h1 h2 _ hn ScalarChirality.chi_M4_023
  · exact key 1 2 3 (by decide) (by decide) (by decide) h1 h2 _ hs ScalarChirality.chi_M4_123

/-! ## Part 6. `thm:hierarchy` (i), (iii) -/

theorem FKΘ_le_FCΘ {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) : NQubit.FKΘ ψ ≤ Ceilings.FCΘ ψ := by
  unfold NQubit.FKΘ NQubit.FK
  refine csSup_le (NQubit.rotSet_nonempty _ _) ?_
  rintro r ⟨u, hu, rfl⟩
  have hn : nsq (rot u (Θ ψ)) = 1 := by rw [NQubit.nsq_rot u hu, NQubit.nsq_Θ, hψ]
  have := Ceilings.le_FC_det ψ (Θ ψ) u (fun i => by rw [(hu i).2]; exact one_ne_zero) (by rw [hn]; exact one_ne_zero)
  rwa [hn, div_one] at this

/-- **`thm:hierarchy` (i)**: for one or two spins, `F_K = F_C = 1` (every state is achiral). -/
theorem FKΘ_eq_FCΘ_eq_one_of_le_two {b : ℕ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) (ψ : Ψ b) (hψ : nsq ψ = 1) :
    NQubit.FKΘ ψ = 1 ∧ Ceilings.FCΘ ψ = 1 := by
  have hK := Ceilings.FKΘ_eq_one_of_le_two hb1 hb2 ψ hψ
  refine ⟨hK, le_antisymm ?_ (hK ▸ FKΘ_le_FCΘ ψ hψ)⟩
  have := Ceilings.FCΘ_le ψ
  rwa [hψ] at this

theorem FCs_le_nsq {n : ℕ} {β : Type*} (g : Fin n → β) (ψ φ : Ψ n) : FCs g ψ φ ≤ nsq ψ :=
  csSup_le (Sharing.fiSet_nonempty g ψ φ) (by
    rintro r ⟨v, -, rfl⟩
    exact Sharing.ratio_le _ _)

/-- `thm:hierarchy` (i) in the frame-sharing vocabulary with independent frames (`g = id`). -/
theorem FCΘs_id_eq_one_of_le_two {b : ℕ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) (ψ : Ψ b) (hψ : nsq ψ = 1) :
    FKΘs (id : Fin b → Fin b) ψ = 1 ∧ FCΘs (id : Fin b → Fin b) ψ = 1 := by
  have hK : FKΘs (id : Fin b → Fin b) ψ = 1 := Ceilings.FKΘ_eq_one_of_le_two hb1 hb2 ψ hψ
  refine ⟨hK, le_antisymm ?_ ?_⟩
  · have := FCs_le_nsq (id : Fin b → Fin b) ψ (Θ ψ)
    rwa [hψ] at this
  · have := Sharing.FKs_le_FCs (id : Fin b → Fin b) ψ (Θ ψ) (by rw [NQubit.nsq_Θ, hψ])
    exact hK ▸ this

/-- **`thm:hierarchy` (iii)**: four qubits; the support test certifies at most `log 2`
(`F_C ≥ 1/2`, `Ceilings.ceiling_half`, under the `RealRep3` hypothesis of `Ceilings`). -/
theorem negLog_FC_four_le_log_two (hR : Ceilings.RealRep3) (ψ : Ψ 4) (hψ : nsq ψ = 1) :
    -Real.log (Ceilings.FCΘ ψ) ≤ Real.log 2 := by
  have h := Ceilings.ceiling_half hR ψ hψ
  have := Real.log_le_log (by norm_num) h
  rw [one_div, Real.log_inv] at this
  linarith

end FormalResearch.FrameFree.OneCopy
