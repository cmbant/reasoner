import Mathlib
import FormalResearch.FrameFree.Foundations
import FormalResearch.FrameFree.HelstromTwirl
import FormalResearch.FrameFree.TwirlsSchurWeyl

/-!
# Haar-free twirls over `K_π` and the slot-permutation criterion (Paper P, `thm:copythreshold` (a))

Namespace `FormalResearch.FrameFree.Twirls`.  Claim class: **proved**.

`IsTwirl π R Z` says `Z` lies in every closed convex set containing the orbit `{U R U†}` and commutes
with `K_π` (the Haar average without a Haar measure; existence from `Helstrom.twirl_exists`).

* `IsTwirl.trace_eq`: `Tr(S Z) = Tr(S R)` for every `S` commuting with `K_π`; with Schur-Weyl
  (`IsTwirl.mem_span`) this gives uniqueness `IsTwirl.unique` and the **criterion** `twirl_eq_iff`: twirls of
  `R, R'` agree iff `Tr(P_σ R) = Tr(P_σ R')` for all block-preserving slot permutations `σ`.
* `thm:copythreshold` (a): `twirl_thetaConj_eq_iff` (operator form, `R` against `E R̄ E†`),
  `copy_twirl_eq_iff` (`R = ρ^{⊗k}`, slots `α × Fin k`, blocks `∏_B S_{|B|k}`), and the `|B|k ≤ 2` clause
  `copy_twirl_eq_of_small` (twirls of `ρ^{⊗k}` and `(ΘρΘ⁻¹)^{⊗k}` coincide, `ρ` Hermitian).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
open scoped ComplexOrder
open FormalResearch.FrameFree.NQubit (Op1 SU2)

namespace FormalResearch.FrameFree.Twirls

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ### The frame group `K_π` as a set of unitary matrices -/

theorem tensOp_mul (π : ι → κ) (u v : κ → Op1) :
    tensOp π u * tensOp π v = tensOp π (fun b => u b * v b) := by
  ext x z
  simp only [Matrix.mul_apply, tensOp, Matrix.of_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [FormalResearch.FrameFree.NQubit.sum_prod_pi (fun i b => u (π i) (x i) b * v (π i) b (z i))]

theorem tensOp_conjTranspose (π : ι → κ) (u : κ → Op1) :
    (tensOp π u)ᴴ = tensOp π (fun b => (u b)ᴴ) := by
  ext x y
  simp [tensOp, Matrix.conjTranspose_apply]

theorem tensOp_one (π : ι → κ) : tensOp π (fun _ => (1 : Op1)) = 1 := by
  ext x y
  simp only [tensOp, Matrix.of_apply, Matrix.one_apply, Finset.prod_boole]
  simp [funext_iff]

theorem tensOp_unitary (π : ι → κ) (u : κ → Op1) (hu : ∀ b, (u b)ᴴ * u b = 1) :
    (tensOp π u)ᴴ * tensOp π u = 1 := by
  rw [tensOp_conjTranspose, tensOp_mul, show (fun b => (u b)ᴴ * u b) = fun _ => (1 : Op1) from
    funext hu, tensOp_one]

section Twirl

variable (π : ι → κ)

/-- The nuisance group `K_π = ∏_B SU(2)` acting as `⊗_i u_{π i}` on the qubits `ι`. -/
def frameGroup : Set (OpS ι) := {U | ∃ u : κ → Op1, (∀ b, SU2 (u b)) ∧ U = tensOp π u}

theorem frameGroup_unitary {U : OpS ι} (hU : U ∈ frameGroup π) : Uᴴ * U = 1 := by
  obtain ⟨u, hu, rfl⟩ := hU
  exact tensOp_unitary π u fun b => (hu b).1

theorem frameGroup_mul {U V : OpS ι} (hU : U ∈ frameGroup π) (hV : V ∈ frameGroup π) :
    U * V ∈ frameGroup π := by
  obtain ⟨u, hu, rfl⟩ := hU
  obtain ⟨v, hv, rfl⟩ := hV
  exact ⟨_, fun b => FormalResearch.FrameFree.NQubit.SU2_mul (hu b) (hv b), tensOp_mul π u v⟩

theorem frameGroup_one : (1 : OpS ι) ∈ frameGroup π :=
  ⟨fun _ => 1, fun _ => FormalResearch.FrameFree.NQubit.SU2_one, (tensOp_one π).symm⟩

theorem frameGroup_conjTranspose {U : OpS ι} (hU : U ∈ frameGroup π) : Uᴴ ∈ frameGroup π := by
  obtain ⟨u, hu, rfl⟩ := hU
  exact ⟨_, fun b => FormalResearch.FrameFree.NQubit.SU2_adjoint (hu b), tensOp_conjTranspose π u⟩

/-- `Z` is **a twirl of `R` over `K_π`**: it commutes with `K_π` and lies in every closed convex set
containing the orbit `{U R U†}` (so it is the Haar average, with no Haar measure). -/
def IsTwirl (R Z : OpS ι) : Prop :=
  (∀ C : Set (OpS ι), IsClosed C → Convex ℝ C → (∀ U ∈ frameGroup π, U * R * Uᴴ ∈ C) → Z ∈ C) ∧
    ∀ U ∈ frameGroup π, U * Z = Z * U

/-- Existence of a twirl (`Helstrom.twirl_exists`). -/
theorem exists_twirl (R : OpS ι) : ∃ Z, IsTwirl π R Z :=
  FormalResearch.FrameFree.Helstrom.twirl_exists (frameGroup π) (fun _ hU => frameGroup_unitary π hU)
    (fun _ hU _ hV => frameGroup_mul π hU hV) ⟨1, frameGroup_one π⟩ R

/-- The twirl preserves the pairing with every operator commuting with `K_π`. -/
theorem IsTwirl.trace_eq {R Z : OpS ι} (h : IsTwirl π R Z) (S : OpS ι)
    (hS : ∀ U ∈ frameGroup π, S * U = U * S) : (S * Z).trace = (S * R).trace := by
  refine h.1 {W | (S * W).trace = (S * R).trace} ?_ ?_ ?_
  · exact isClosed_eq (Continuous.matrix_trace (continuous_const.matrix_mul continuous_id))
      continuous_const
  · intro x hx y hy a b ha hb hab
    show (S * (a • x + b • y)).trace = _
    have hx' : (S * x).trace = (S * R).trace := hx
    have hy' : (S * y).trace = (S * R).trace := hy
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_smul, hx', hy', ← add_smul, hab, one_smul]
  · intro U hU
    show (S * (U * R * Uᴴ)).trace = _
    have e : S * (U * R * Uᴴ) = U * (S * R) * Uᴴ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hS U hU]
    rw [e, Matrix.trace_mul_cycle, frameGroup_unitary π hU, Matrix.one_mul]

/-- A real half-space `{W | c ≤ Re Tr(Q W)}` containing the orbit contains the twirl. -/
theorem IsTwirl.le_re_trace {R Z : OpS ι} (h : IsTwirl π R Z) (Q : OpS ι) (c : ℝ)
    (hc : ∀ U ∈ frameGroup π, c ≤ (Q * (U * R * Uᴴ)).trace.re) : c ≤ (Q * Z).trace.re := by
  refine h.1 {W | c ≤ (Q * W).trace.re} ?_ ?_ hc
  · exact isClosed_le continuous_const (Complex.continuous_re.comp
      (Continuous.matrix_trace (continuous_const.matrix_mul continuous_id)))
  · exact convex_halfSpace_ge (f := fun W : OpS ι => (Q * W).trace.re)
      ⟨fun A B => by simp [Matrix.mul_add, Matrix.trace_add],
       fun r A => by simp [Matrix.trace_smul]⟩ c

/-- The twirl of a Hermitian operator is Hermitian. -/
theorem IsTwirl.isHermitian {R Z : OpS ι} (h : IsTwirl π R Z) (hR : Rᴴ = R) : Zᴴ = Z := by
  refine h.1 {W | Wᴴ = W} ?_ ?_ ?_
  · exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  · intro A hA B hB a b _ _ _
    have hA' : Aᴴ = A := hA
    have hB' : Bᴴ = B := hB
    show (a • A + b • B)ᴴ = a • A + b • B
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, hA', hB',
      star_trivial, star_trivial]
  · intro U _
    show (U * R * Uᴴ)ᴴ = U * R * Uᴴ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hR,
      Matrix.mul_assoc]

theorem IsTwirl.mem_span {R Z : OpS ι} (h : IsTwirl π R Z) : Z ∈ blockPermSpan π :=
  (commutant_eq_blockPermSpan π Z).1 (fun u hu => (h.2 _ ⟨u, hu, rfl⟩).symm)

theorem trace_eq_of_mem_span {R Z : OpS ι} (h : IsTwirl π R Z) {S : OpS ι}
    (hS : S ∈ blockPermSpan π) : (S * Z).trace = (S * R).trace :=
  h.trace_eq π S fun U hU => by
    obtain ⟨u, _, rfl⟩ := hU
    exact (tensOp_commute_of_mem π u hS).symm

/-- Elements of the permutation algebra are determined by their pairings with it. -/
theorem eq_of_pairing {Z Z' : OpS ι} (hZ : Z ∈ blockPermSpan π) (hZ' : Z' ∈ blockPermSpan π)
    (h : ∀ S ∈ blockPermSpan π, (S * Z).trace = (S * Z').trace) : Z = Z' := by
  have hD : Z - Z' ∈ blockPermSpan π := Submodule.sub_mem _ hZ hZ'
  have h0 : ((Z - Z')ᴴ * (Z - Z')).trace = 0 := by
    rw [Matrix.mul_sub, Matrix.trace_sub, h _ (conjTranspose_mem_blockPermSpan π hD), sub_self]
  exact sub_eq_zero.1 (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h0)

/-- **The twirl is unique** (Schur--Weyl): two twirls of `R` coincide. -/
theorem IsTwirl.unique {R Z Z' : OpS ι} (h : IsTwirl π R Z) (h' : IsTwirl π R Z') : Z = Z' :=
  eq_of_pairing π h.mem_span h'.mem_span fun S hS => by
    rw [trace_eq_of_mem_span π h hS, trace_eq_of_mem_span π h' hS]

/-- **Twirl equality criterion.**  The twirls of `R` and `R'` coincide iff the expectations of all
block-preserving slot permutations agree (the "if" direction is Schur--Weyl duality). -/
theorem twirl_eq_iff {R R' Z Z' : OpS ι} (h : IsTwirl π R Z) (h' : IsTwirl π R' Z') :
    Z = Z' ↔ ∀ σ : Equiv.Perm ι, (∀ i, π (σ i) = π i) →
      (permOp σ * R).trace = (permOp σ * R').trace := by
  constructor
  · intro hZ σ hσ
    have h1 := trace_eq_of_mem_span π h (permOp_mem_blockPermSpan π σ hσ)
    have h2 := trace_eq_of_mem_span π h' (permOp_mem_blockPermSpan π σ hσ)
    rw [← h1, ← h2, hZ]
  · intro hσ
    have hall : ∀ S ∈ blockPermSpan π, (S * R).trace = (S * R').trace := by
      intro S hS
      induction hS using Submodule.span_induction with
      | mem x hx => obtain ⟨σ, hσ', rfl⟩ := hx; exact hσ σ hσ'
      | zero => simp
      | add y z _ _ hy hz => simp only [Matrix.add_mul, Matrix.trace_add, hy, hz]
      | smul c y _ hy => simp only [Matrix.smul_mul, Matrix.trace_smul, hy]
    refine eq_of_pairing π h.mem_span h'.mem_span fun S hS => ?_
    rw [trace_eq_of_mem_span π h hS, trace_eq_of_mem_span π h' hS, hall S hS]

end Twirl

/-! ### Time reversal `R ↦ E R̄ E†` and the reality criterion -/

/-- `E = ε^{⊗ι}`. -/
noncomputable def epsOp (ι : Type*) [Fintype ι] [DecidableEq ι] : OpS ι :=
  tensOp (fun _ : ι => ()) (fun _ => FormalResearch.FrameFree.NQubit.eps)

/-- Time reversal of an operator, `Θ R Θ⁻¹ = E R̄ E†`. -/
noncomputable def thetaConj (R : OpS ι) : OpS ι := epsOp ι * R.map conj * (epsOp ι)ᴴ

theorem epsOp_unitary : (epsOp ι)ᴴ * epsOp ι = 1 :=
  tensOp_unitary _ _ fun _ => FormalResearch.FrameFree.NQubit.SU2_eps.1

theorem epsOp_commute_permOp (σ : Equiv.Perm ι) : epsOp ι * permOp σ = permOp σ * epsOp ι :=
  tensOp_commute _ _ σ fun _ => rfl

theorem permOp_map_conj (σ : Equiv.Perm ι) : (permOp σ).map conj = permOp σ := by
  ext x y
  simp only [Matrix.map_apply, permOp, Matrix.of_apply]
  split_ifs <;> simp

theorem conj_trace_eq (A : OpS ι) : conj A.trace = (A.map conj).trace := by
  simp [Matrix.trace, map_sum]

/-- `Tr(P_σ · ΘRΘ⁻¹) = conj Tr(P_σ R)` for every slot permutation `σ`. -/
theorem trace_permOp_thetaConj (σ : Equiv.Perm ι) (R : OpS ι) :
    (permOp σ * thetaConj R).trace = conj (permOp σ * R).trace := by
  rw [conj_trace_eq, Matrix.map_mul, permOp_map_conj, thetaConj]
  have e : permOp σ * (epsOp ι * R.map conj * (epsOp ι)ᴴ)
      = epsOp ι * (permOp σ * R.map conj) * (epsOp ι)ᴴ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← epsOp_commute_permOp]
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_cycle, epsOp_unitary, Matrix.one_mul]

section Criterion

variable (π : ι → κ)

/-- **`thm:copythreshold` (a), operator form.**  The twirls of `R` and of its time reversal
`E R̄ E†` coincide iff `Tr(s R)` is real for every block-preserving slot permutation `s`
(for `R = ρ^{⊗k}`: `s ∈ ∏_B S_{|B|k}`). -/
theorem twirl_thetaConj_eq_iff {R Z Z' : OpS ι} (h : IsTwirl π R Z) (h' : IsTwirl π (thetaConj R) Z') :
    Z = Z' ↔ ∀ σ : Equiv.Perm ι, (∀ i, π (σ i) = π i) → conj (permOp σ * R).trace = (permOp σ * R).trace := by
  rw [twirl_eq_iff π h h']
  refine forall_congr' fun σ => forall_congr' fun _ => ?_
  rw [trace_permOp_thetaConj]
  exact eq_comm

/-- If no block has three slots, every block-preserving permutation is an involution. -/
theorem perm_mul_self_of_small_blocks
    (hπ : ∀ i j l, π i = π j → π j = π l → i = j ∨ j = l ∨ i = l)
    (σ : Equiv.Perm ι) (hσ : ∀ i, π (σ i) = π i) : σ * σ = 1 := by
  ext i
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  by_cases h : σ i = i
  · rw [h, h]
  · have h1 : π i = π (σ i) := (hσ i).symm
    have h2 : π (σ i) = π (σ (σ i)) := (hσ (σ i)).symm
    rcases hπ i (σ i) (σ (σ i)) h1 h2 with h3 | h3 | h3
    · exact absurd h3.symm h
    · exact absurd (σ.injective (by rw [← h3])).symm h
    · exact h3.symm

/-- **`thm:copythreshold` (a), blocks of at most two slots.**  For a Hermitian `R` (a state, e.g.
`ρ^{⊗k}` when no block has more than two slots in the `k` copies) the twirls of `R` and of its time
reversal coincide. -/
theorem twirl_thetaConj_eq_of_small_blocks
    (hπ : ∀ i j l, π i = π j → π j = π l → i = j ∨ j = l ∨ i = l)
    {R Z Z' : OpS ι} (hR : Rᴴ = R) (h : IsTwirl π R Z) (h' : IsTwirl π (thetaConj R) Z') : Z = Z' := by
  rw [twirl_thetaConj_eq_iff π h h']
  intro σ hσ
  have hinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right (perm_mul_self_of_small_blocks π hπ σ hσ)
  have : conj (permOp σ * R).trace = ((permOp σ * R)ᴴ).trace := by
    rw [Matrix.trace_conjTranspose]; rfl
  rw [this, Matrix.conjTranspose_mul, hR, permOp_conjTranspose, hinv, Matrix.trace_mul_comm]

end Criterion

/-! ### `k` copies: `ρ^{⊗k}` on the slots `α × γ` -/

section Copies

variable {α γ : Type*} [Fintype α] [DecidableEq α] [Fintype γ] [DecidableEq γ]

/-- The tensor power `ρ^{⊗γ}` on the slots `α × γ` (slot `(a, c)` is spin `a` of copy `c`). -/
noncomputable def kronPow (γ : Type*) [Fintype γ] (ρ : OpS α) : OpS (α × γ) :=
  Matrix.of fun x y => ∏ c, ρ (fun a => x (a, c)) (fun a => y (a, c))

/-- Regrouping the qubits of `α × γ` copy by copy. -/
def copyEquiv : (α × γ → Fin 2) ≃ (γ → α → Fin 2) where
  toFun x c a := x (a, c)
  invFun w q := w q.2 q.1
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_copies (f : γ → (α → Fin 2) → ℂ) :
    ∑ y : α × γ → Fin 2, ∏ c, f c (fun a => y (a, c)) = ∏ c, ∑ b : α → Fin 2, f c b := by
  rw [← Equiv.sum_comp (copyEquiv (α := α) (γ := γ)).symm]
  rw [← FormalResearch.FrameFree.NQubit.sum_prod_pi f]
  refine Finset.sum_congr rfl fun w _ => Finset.prod_congr rfl fun c _ => ?_
  rfl

theorem kronPow_mul (A B : OpS α) : kronPow γ A * kronPow γ B = kronPow γ (A * B) := by
  ext x z
  simp only [Matrix.mul_apply, kronPow, Matrix.of_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_copies (fun c b => A (fun a => x (a, c)) b * B b (fun a => z (a, c)))]

theorem kronPow_conjTranspose (A : OpS α) : (kronPow γ A)ᴴ = kronPow γ Aᴴ := by
  ext x y
  simp [kronPow, Matrix.conjTranspose_apply]

theorem kronPow_map_conj (A : OpS α) : (kronPow γ A).map conj = kronPow γ (A.map conj) := by
  ext x y
  simp [kronPow, map_prod]

theorem epsOp_prod : epsOp (α × γ) = kronPow γ (epsOp α) := by
  ext x y
  simp only [epsOp, tensOp, kronPow, Matrix.of_apply]
  rw [Fintype.prod_prod_type_right]

/-- Time reversal commutes with taking `k` copies: `(ΘρΘ⁻¹)^{⊗k} = Θ ρ^{⊗k} Θ⁻¹`. -/
theorem thetaConj_kronPow (ρ : OpS α) :
    thetaConj (kronPow γ ρ) = kronPow γ (thetaConj ρ) := by
  rw [thetaConj, thetaConj, epsOp_prod, kronPow_map_conj, kronPow_conjTranspose, kronPow_mul,
    kronPow_mul]

theorem kronPow_isHermitian {ρ : OpS α} (hρ : ρᴴ = ρ) : (kronPow γ ρ)ᴴ = kronPow γ ρ := by
  rw [kronPow_conjTranspose, hρ]

variable (π : α → κ)

/-- The sharing pattern on the `k`-copy slots: slot `(a, c)` has the frame of the block of `a`. -/
def copyPattern (γ : Type*) (π : α → κ) : α × γ → κ := fun q => π q.1

/-- **`thm:copythreshold` (a).**  The twirls over `K_π` of `ρ^{⊗k}` and of `(ΘρΘ⁻¹)^{⊗k}` coincide iff
`Tr(s ρ^{⊗k})` is real for every `s ∈ ∏_B S_{|B|k}`, the permutations of the `|B|k` slots of each
block. -/
theorem copy_twirl_eq_iff (ρ : OpS α) {Z Z' : OpS (α × γ)}
    (h : IsTwirl (copyPattern γ π) (kronPow γ ρ) Z)
    (h' : IsTwirl (copyPattern γ π) (kronPow γ (thetaConj ρ)) Z') :
    Z = Z' ↔ ∀ s : Equiv.Perm (α × γ), (∀ q, π (s q).1 = π q.1) →
      conj (permOp s * kronPow γ ρ).trace = (permOp s * kronPow γ ρ).trace := by
  rw [← thetaConj_kronPow] at h'
  exact twirl_thetaConj_eq_iff (copyPattern γ π) h h'

/-- Blocks of at most two slots over all `k` copies: `|B|·k ≤ 2` for every block. -/
theorem copyPattern_small (hk : ∀ b : κ, (Finset.univ.filter fun a => π a = b).card * Fintype.card γ ≤ 2) :
    ∀ i j l : α × γ, copyPattern γ π i = copyPattern γ π j → copyPattern γ π j = copyPattern γ π l →
      i = j ∨ j = l ∨ i = l := by
  intro i j l hij hjl
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3⟩ := hne
  have hsub : ({i, j, l} : Finset (α × γ)) ⊆
      (Finset.univ.filter fun a => π a = copyPattern γ π i) ×ˢ (Finset.univ : Finset γ) := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    rcases hq with rfl | rfl | rfl
    · rfl
    · exact hij.symm
    · exact (hij.trans hjl).symm
  have := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_eq_three.2 ⟨i, j, l, h1, h3, h2, rfl⟩, Finset.card_univ] at this
  have h4 := hk (copyPattern γ π i)
  omega

/-- **`thm:copythreshold` (a), `bk ≤ 2`.**  If every block has at most two slots over all `k` copies,
the twirls of `ρ^{⊗k}` and `(ΘρΘ⁻¹)^{⊗k}` coincide for every Hermitian `ρ`. -/
theorem copy_twirl_eq_of_small (hk : ∀ b : κ, (Finset.univ.filter fun a => π a = b).card *
      Fintype.card γ ≤ 2) {ρ : OpS α} (hρ : ρᴴ = ρ) {Z Z' : OpS (α × γ)}
    (h : IsTwirl (copyPattern γ π) (kronPow γ ρ) Z)
    (h' : IsTwirl (copyPattern γ π) (kronPow γ (thetaConj ρ)) Z') : Z = Z' := by
  rw [← thetaConj_kronPow] at h'
  exact twirl_thetaConj_eq_of_small_blocks (copyPattern γ π) (copyPattern_small π hk)
    (kronPow_isHermitian hρ) h h'

end Copies

end FormalResearch.FrameFree.Twirls
