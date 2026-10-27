import FormalResearch.FourQubitEntropy.Bridge
import FormalResearch.FourQubitEntropy.Attainment

/-!
# Scalar spin chirality on three and four qubits

Exact identities behind the "scalar chirality" statements of the antiunitary-occupation programme
(`ResearchNotes/QI/antiunitary_occupation`, Theorem *What one copy sees* (c), Proposition *Odd
invariants* (iii), and the notation of `M₄`).  Everything lives in the namespace
`FormalResearch.FrameFree.ScalarChirality`.

Conventions.  A four-qubit vector is `ψ : Psi`, `ψ a b c d` the amplitude of `|a b c d⟩`; qubits
`1,2,3,4` of the paper are `0,1,2,3 : Fin 4`.  `chi i j l` is
`(1/8) Σ ε_{abc} σ_a^{(i)} σ_b^{(j)} σ_c^{(l)} = S_i · (S_j × S_l)` (a linear map on `Psi`).

Contents.

* `chi_eq_commutator`, `swap3_commutator`: `i [SWAP_{il}, SWAP_{ij}] = 4 χ_{ijl}` (four qubits, any
  distinct `i j l`; and `i [SWAP₁₃, SWAP₁₂] = 4 χ₁₂₃` as `8 × 8` matrices on three qubits).
  Equivalently `χ_{ijl} = (i/4)(C - C⁻¹)` with the three-cycle `C = SWAP_{il} SWAP_{ij}` (`chi_eq_cyc`).
* `chi_hermitian`, `chi_cube`: `χ` is Hermitian and `χ³ = (3/16) χ`, so its spectrum lies in
  `{0, ±√3/4}`.
* `chi3_multiplicities`: on three qubits the eigenspaces of `χ₁₂₃` for `+√3/4`, `-√3/4`, `0` have
  dimensions `2, 2, 4` (from `tr χ = 0`, `tr χ² = 3/4`, `χ³ = (3/16) χ`).  `chi_bridge` identifies the
  four-qubit `χ₁₂₃` with `χ₁₂₃ ⊗ 1`.
* `chi_M4_012`, `chi_M4_013`, `chi_M4_023`, `chi_M4_123` (and `_conj`): `M₄` is an eigenvector of every
  scalar chirality, with eigenvalues `-√3/4, +√3/4, -√3/4, +√3/4` on the triples
  `(1,2,3), (1,2,4), (1,3,4), (2,3,4)`; `conj M₄` has the opposite signs.
* `chi_Theta_odd`: `⟨Θψ|χ Θψ⟩ = -⟨ψ|χ ψ⟩` for `Θψ = (ε⊗ε⊗ε⊗ε) conj ψ`.
* `oddDim_values`, `totalDim_values`: the dimensions `0, 1, 4, 16, 56` of the odd-invariant spaces for
  one copy of `n = 2, …, 6` spins with a common frame, and the check `Σ (2j+1) g_j = 2ⁿ`.
-/

open scoped ComplexConjugate
open FormalResearch.FourQubitEntropy

namespace FormalResearch.FrameFree.ScalarChirality

/-! ### Basic layer: tuples, permutations of qubits, inner product -/

theorem vec4 (x : Fin 4 → Fin 2) : ![x 0, x 1, x 2, x 3] = x := by
  funext k; fin_cases k <;> rfl

/-- Amplitude at a basis tuple `x : Fin 4 → Fin 2`. -/
def ev (ψ : Psi) (x : Fin 4 → Fin 2) : ℂ := ψ (x 0) (x 1) (x 2) (x 3)

theorem eq_of_ev {ψ φ : Psi} (h : ∀ x, ev ψ x = ev φ x) : ψ = φ := by
  funext a b c d; exact h ![a, b, c, d]

/-- The permutation operator: `(permPsi σ ψ)(x) = ψ(x ∘ σ)`. -/
def permPsi (σ : Equiv.Perm (Fin 4)) (ψ : Psi) : Psi := fun a b c d =>
  ψ (![a, b, c, d] (σ 0)) (![a, b, c, d] (σ 1)) (![a, b, c, d] (σ 2)) (![a, b, c, d] (σ 3))

theorem ev_perm (σ : Equiv.Perm (Fin 4)) (ψ : Psi) (x : Fin 4 → Fin 2) :
    ev (permPsi σ ψ) x = ev ψ (x ∘ σ) := by
  show ψ (![x 0, x 1, x 2, x 3] (σ 0)) (![x 0, x 1, x 2, x 3] (σ 1)) (![x 0, x 1, x 2, x 3] (σ 2))
    (![x 0, x 1, x 2, x 3] (σ 3)) = _
  rw [vec4]; rfl

theorem permPsi_mul (σ τ : Equiv.Perm (Fin 4)) (ψ : Psi) :
    permPsi σ (permPsi τ ψ) = permPsi (σ * τ) ψ := by
  apply eq_of_ev; intro x
  rw [ev_perm, ev_perm, ev_perm]; rfl

theorem permPsi_one (ψ : Psi) : permPsi 1 ψ = ψ := by
  apply eq_of_ev; intro x
  rw [ev_perm]; rfl

/-- `permPsi σ` as a linear operator. -/
def permL (σ : Equiv.Perm (Fin 4)) : Module.End ℂ Psi where
  toFun := permPsi σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem permL_apply (σ : Equiv.Perm (Fin 4)) (ψ : Psi) : permL σ ψ = permPsi σ ψ := rfl

theorem permL_mul (σ τ : Equiv.Perm (Fin 4)) : permL (σ * τ) = permL σ * permL τ := by
  exact LinearMap.ext fun ψ => (permPsi_mul σ τ ψ).symm

theorem permL_one : permL 1 = 1 := by
  exact LinearMap.ext fun ψ => permPsi_one ψ

theorem sum_pi4 (f : (Fin 4 → Fin 2) → ℂ) :
    ∑ x, f x = ∑ a, ∑ b, ∑ c, ∑ d, f ![a, b, c, d] := by
  let e : (Fin 4 → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 × Fin 2 :=
    { toFun := fun x => (x 0, x 1, x 2, x 3)
      invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
      left_inv := fun x => vec4 x
      right_inv := fun p => rfl }
  rw [← Equiv.sum_comp e.symm f, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

/-- The inner product `⟨φ|ψ⟩`. -/
noncomputable def ip (φ ψ : Psi) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, conj (φ a b c d) * ψ a b c d

theorem ip_eq (φ ψ : Psi) : ip φ ψ = ∑ x, conj (ev φ x) * ev ψ x := by
  rw [sum_pi4]; rfl

theorem ip_perm (σ : Equiv.Perm (Fin 4)) (φ ψ : Psi) :
    ip φ (permPsi σ ψ) = ip (permPsi σ⁻¹ φ) ψ := by
  rw [ip_eq, ip_eq]
  simp only [ev_perm]
  have := Equiv.sum_comp (σ.symm.arrowCongr (Equiv.refl (Fin 2)))
    (fun y => conj (ev φ (y ∘ ⇑σ⁻¹)) * ev ψ y)
  rw [← this]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : (σ.symm.arrowCongr (Equiv.refl (Fin 2))) x = x ∘ σ := by
    funext k; simp
  rw [h]
  have h2 : (x ∘ ⇑σ) ∘ ⇑σ⁻¹ = x := by funext k; simp
  rw [h2]

theorem ip_conj_symm (φ ψ : Psi) : ip φ ψ = conj (ip ψ φ) := by
  simp only [ip, map_sum, map_mul, Complex.conj_conj]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring


/-! ### Local operators and the scalar chirality -/

theorem ev_actOn (i : Fin 4) (σ : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Psi) (x : Fin 4 → Fin 2) :
    ev (actOn i σ ψ) x = ∑ t, σ (x i) t * ev ψ (Function.update x i t) := by
  fin_cases i <;> simp [ev, actOn]

/-- Relabelling qubits: `σ^{(i)} P_τ = P_τ σ^{(τ⁻¹ i)}`. -/
theorem actOn_perm (i : Fin 4) (σ : Matrix (Fin 2) (Fin 2) ℂ) (τ : Equiv.Perm (Fin 4)) (ψ : Psi) :
    actOn i σ (permPsi τ ψ) = permPsi τ (actOn (τ.symm i) σ ψ) := by
  apply eq_of_ev; intro x
  rw [ev_actOn, ev_perm, ev_actOn]
  simp only [ev_perm]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : (x ∘ ⇑τ) (τ.symm i) = x i := by simp
  rw [h1, ← Function.update_comp_equiv]

/-- The one-qubit operator `σ^{(i)}` as a linear map. -/
def actL (i : Fin 4) (σ : Matrix (Fin 2) (Fin 2) ℂ) : Module.End ℂ Psi where
  toFun := actOn i σ
  map_add' ψ φ := by
    funext a b c d
    fin_cases i <;> simp [actOn, mul_add, Finset.sum_add_distrib]
  map_smul' r ψ := by
    funext a b c d
    fin_cases i <;> simp [actOn, mul_left_comm, mul_add]

theorem actL_apply (i : Fin 4) (σ : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Psi) :
    actL i σ ψ = actOn i σ ψ := rfl

def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![pauliX, pauliY, pauliZ]

/-- The Levi-Civita symbol on `Fin 3`. -/
noncomputable def eps3 (a b c : Fin 3) : ℂ :=
  (((a : ℕ) : ℂ) - (b : ℕ)) * (((b : ℕ) : ℂ) - (c : ℕ)) * (((c : ℕ) : ℂ) - (a : ℕ)) / 2

/-- The scalar spin chirality `χ_{ijl} = S_i · (S_j × S_l) = (1/8) Σ ε_{abc} σ_a^{(i)} σ_b^{(j)} σ_c^{(l)}`
on four qubits (qubits `i, j, l` should be distinct). -/
noncomputable def chi (i j l : Fin 4) : Module.End ℂ Psi :=
  (1 / 8 : ℂ) • ∑ a, ∑ b, ∑ c, eps3 a b c • (actL i (pauli a) * actL j (pauli b) * actL l (pauli c))

theorem chi_apply (i j l : Fin 4) (ψ : Psi) : chi i j l ψ =
    (1 / 8 : ℂ) • ∑ a, ∑ b, ∑ c, eps3 a b c • actOn i (pauli a) (actOn j (pauli b) (actOn l (pauli c) ψ)) := by
  simp [chi, LinearMap.sum_apply, Module.End.mul_apply, actL_apply]

theorem chi_six (i j l : Fin 4) (ψ : Psi) : chi i j l ψ = (1 / 8 : ℂ) • (
    actOn i pauliX (actOn j pauliY (actOn l pauliZ ψ))
    - actOn i pauliX (actOn j pauliZ (actOn l pauliY ψ))
    + actOn i pauliY (actOn j pauliZ (actOn l pauliX ψ))
    - actOn i pauliY (actOn j pauliX (actOn l pauliZ ψ))
    + actOn i pauliZ (actOn j pauliX (actOn l pauliY ψ))
    - actOn i pauliZ (actOn j pauliY (actOn l pauliX ψ))) := by
  rw [chi_apply]
  simp only [Fin.sum_univ_three, eps3, pauli]
  congr 1
  funext a b c d
  simp
  norm_num
  ring

theorem chi_perm (τ : Equiv.Perm (Fin 4)) (i j l : Fin 4) (ψ : Psi) :
    chi (τ i) (τ j) (τ l) (permPsi τ ψ) = permPsi τ (chi i j l ψ) := by
  simp only [chi_apply, actOn_perm, Equiv.symm_apply_apply]
  simp only [← permL_apply, map_smul, map_sum]

theorem chi_conj_perm (τ : Equiv.Perm (Fin 4)) (i j l : Fin 4) :
    chi (τ i) (τ j) (τ l) = permL τ * chi i j l * permL τ⁻¹ := by
  have h : permL τ * permL τ⁻¹ = 1 := by rw [← permL_mul, mul_inv_cancel, permL_one]
  apply LinearMap.ext; intro ψ
  have := chi_perm τ i j l (permPsi τ⁻¹ ψ)
  rw [permPsi_mul, mul_inv_cancel, permPsi_one] at this
  rw [Module.End.mul_apply, Module.End.mul_apply, this]
  rfl

set_option maxHeartbeats 4000000 in
theorem chi_eq_base (ψ : Psi) :
    (4 : ℂ) • chi 0 1 2 ψ = Complex.I • (permPsi (Equiv.swap 0 2) (permPsi (Equiv.swap 0 1) ψ)
      - permPsi (Equiv.swap 0 1) (permPsi (Equiv.swap 0 2) ψ)) := by
  rw [chi_six]
  funext a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [permPsi, actOn, Fin.sum_univ_two, pauliX, pauliY, pauliZ, Equiv.swap_apply_def] <;> ring

theorem exists_perm : ∀ i j l : Fin 4, i ≠ j → i ≠ l → j ≠ l →
    ∃ τ : Equiv.Perm (Fin 4), τ 0 = i ∧ τ 1 = j ∧ τ 2 = l := by decide

/-- `4 χ_{ijl} = i [SWAP_{il}, SWAP_{ij}]`, for distinct qubits (operator form). -/
theorem chi_eq_commutator (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    (4 : ℂ) • chi i j l = Complex.I • (permL (Equiv.swap i l) * permL (Equiv.swap i j)
      - permL (Equiv.swap i j) * permL (Equiv.swap i l)) := by
  obtain ⟨τ, h0, h1, h2⟩ := exists_perm i j l hij hil hjl
  subst h0 h1 h2
  have hb : (4 : ℂ) • chi 0 1 2 = Complex.I • (permL (Equiv.swap 0 2) * permL (Equiv.swap 0 1)
      - permL (Equiv.swap 0 1) * permL (Equiv.swap 0 2)) :=
    LinearMap.ext fun ψ => chi_eq_base ψ
  have hτ : permL τ⁻¹ * permL τ = 1 := by rw [← permL_mul, inv_mul_cancel, permL_one]
  have hτ' : permL τ * permL τ⁻¹ = 1 := by rw [← permL_mul, mul_inv_cancel, permL_one]
  have hs : ∀ p q : Fin 4, permL (Equiv.swap (τ p) (τ q)) = permL τ * permL (Equiv.swap p q) * permL τ⁻¹ := by
    intro p q
    rw [Equiv.swap_apply_apply, permL_mul, permL_mul]
  rw [chi_conj_perm, hs, hs]
  calc (4 : ℂ) • (permL τ * chi 0 1 2 * permL τ⁻¹)
      = permL τ * ((4 : ℂ) • chi 0 1 2) * permL τ⁻¹ := by
        rw [mul_smul_comm, smul_mul_assoc]
    _ = _ := by
        rw [hb]
        simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, smul_sub]
        congr 2
        · calc permL τ * (permL (Equiv.swap 0 2) * permL (Equiv.swap 0 1)) * permL τ⁻¹
              = permL τ * permL (Equiv.swap 0 2) * (permL τ⁻¹ * permL τ) * permL (Equiv.swap 0 1) * permL τ⁻¹ := by
                rw [hτ]; simp only [mul_assoc, mul_one]
            _ = _ := by simp only [mul_assoc]
        · calc permL τ * (permL (Equiv.swap 0 1) * permL (Equiv.swap 0 2)) * permL τ⁻¹
              = permL τ * permL (Equiv.swap 0 1) * (permL τ⁻¹ * permL τ) * permL (Equiv.swap 0 2) * permL τ⁻¹ := by
                rw [hτ]; simp only [mul_assoc, mul_one]
            _ = _ := by simp only [mul_assoc]


/-! ### `χ = (i/4)(C - C⁻¹)` for the three-cycle `C`, and its consequences -/

theorem cyc_cube : ∀ i j l : Fin 4, i ≠ j → i ≠ l → j ≠ l →
    (Equiv.swap i l * Equiv.swap i j) * (Equiv.swap i l * Equiv.swap i j) *
      (Equiv.swap i l * Equiv.swap i j) = 1 := by decide

theorem cyc_cube' : ∀ i j l : Fin 4, i ≠ j → i ≠ l → j ≠ l →
    (Equiv.swap i j * Equiv.swap i l) * (Equiv.swap i j * Equiv.swap i l) *
      (Equiv.swap i j * Equiv.swap i l) = 1 := by decide

/-- `χ_{ijl} = (i/4)(C - C⁻¹)` with `C = SWAP_{il} SWAP_{ij}`. -/
theorem chi_eq_cyc (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    chi i j l = (Complex.I / 4) • (permL (Equiv.swap i l * Equiv.swap i j)
      - permL (Equiv.swap i j * Equiv.swap i l)) := by
  have h := chi_eq_commutator i j l hij hil hjl
  rw [← permL_mul, ← permL_mul] at h
  have h4 : chi i j l = (1 / 4 : ℂ) • ((4 : ℂ) • chi i j l) := by
    rw [smul_smul]; norm_num
  rw [h4, h, smul_smul]
  congr 1; ring

theorem cube_aux {R : Type*} [Ring R] [Algebra ℂ R] (A B : R) (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : A * A * A = 1) (hB : B * B * B = 1) :
    (A - B) * (A - B) * (A - B) = (-3 : ℂ) • (A - B) := by
  have h3 : A * A * B = A := by rw [mul_assoc, hAB, mul_one]
  have h6 : B * B * A = B := by rw [mul_assoc, hBA, mul_one]
  simp only [mul_sub, sub_mul, hA, hB, hAB, hBA, h3, h6, one_mul]
  module

/-- The eigenvalue equation `χ³ = (3/16) χ`: the spectrum lies in `{0, ±√3/4}`. -/
theorem chi_cube (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    chi i j l * chi i j l * chi i j l = (3 / 16 : ℂ) • chi i j l := by
  have hAB : permL (Equiv.swap i l * Equiv.swap i j) * permL (Equiv.swap i j * Equiv.swap i l) = 1 := by
    rw [← permL_mul]
    have : (Equiv.swap i l * Equiv.swap i j) * (Equiv.swap i j * Equiv.swap i l) = 1 := by
      simp [mul_assoc]
    rw [this, permL_one]
  have hBA : permL (Equiv.swap i j * Equiv.swap i l) * permL (Equiv.swap i l * Equiv.swap i j) = 1 := by
    rw [← permL_mul]
    have : (Equiv.swap i j * Equiv.swap i l) * (Equiv.swap i l * Equiv.swap i j) = 1 := by
      simp [mul_assoc]
    rw [this, permL_one]
  have hA : permL (Equiv.swap i l * Equiv.swap i j) * permL (Equiv.swap i l * Equiv.swap i j) *
      permL (Equiv.swap i l * Equiv.swap i j) = 1 := by
    rw [← permL_mul, ← permL_mul, cyc_cube i j l hij hil hjl, permL_one]
  have hB : permL (Equiv.swap i j * Equiv.swap i l) * permL (Equiv.swap i j * Equiv.swap i l) *
      permL (Equiv.swap i j * Equiv.swap i l) = 1 := by
    rw [← permL_mul, ← permL_mul, cyc_cube' i j l hij hil hjl, permL_one]
  rw [chi_eq_cyc i j l hij hil hjl]
  simp only [smul_mul_smul_comm, smul_smul]
  rw [cube_aux _ _ hAB hBA hA hB, smul_smul]
  congr 1
  linear_combination (-(3 / 64) * Complex.I) * Complex.I_sq

theorem ip_sub_right (φ ψ₁ ψ₂ : Psi) : ip φ (ψ₁ - ψ₂) = ip φ ψ₁ - ip φ ψ₂ := by
  simp only [ip, ← Finset.sum_sub_distrib, Pi.sub_apply, mul_sub]

theorem ip_smul_right (φ ψ : Psi) (r : ℂ) : ip φ (r • ψ) = r * ip φ ψ := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/-- `χ_{ijl}` is Hermitian: `⟨φ|χψ⟩ = conj ⟨ψ|χφ⟩`. -/
theorem chi_hermitian (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (φ ψ : Psi) :
    ip φ (chi i j l ψ) = conj (ip ψ (chi i j l φ)) := by
  have key : ∀ χ : Psi → Psi, (∀ ξ, χ ξ = (Complex.I / 4) • (permPsi (Equiv.swap i l * Equiv.swap i j) ξ
      - permPsi (Equiv.swap i j * Equiv.swap i l) ξ)) →
      ip φ (χ ψ) = conj (ip ψ (χ φ)) := by
    intro χ hχ
    rw [hχ, hχ, ip_smul_right, ip_smul_right, ip_sub_right, ip_sub_right, ip_perm, ip_perm]
    have e1 : (Equiv.swap i l * Equiv.swap i j)⁻¹ = Equiv.swap i j * Equiv.swap i l := by
      simp [mul_inv_rev]
    have e2 : (Equiv.swap i j * Equiv.swap i l)⁻¹ = Equiv.swap i l * Equiv.swap i j := by
      simp [mul_inv_rev]
    rw [e1, e2, ip_conj_symm (permPsi (Equiv.swap i j * Equiv.swap i l) φ) ψ,
      ip_conj_symm (permPsi (Equiv.swap i l * Equiv.swap i j) φ) ψ]
    simp only [map_mul, map_sub, map_div₀, Complex.conj_I, map_ofNat]
    ring
  exact key (chi i j l) fun ξ => by
    rw [chi_eq_cyc i j l hij hil hjl]; rfl


/-! ### Time reversal -/

/-- `ε = [[0,1],[-1,0]]`. -/
def epsM : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- `Θψ = (ε⊗ε⊗ε⊗ε) conj ψ`. -/
noncomputable def Theta (ψ : Psi) : Psi := fun a b c d =>
  ∑ t₁, ∑ t₂, ∑ t₃, ∑ t₄, epsM a t₁ * epsM b t₂ * epsM c t₃ * epsM d t₄ * conj (ψ t₁ t₂ t₃ t₄)

/-- The sign `ε a (a+1)`. -/
def sgn : Fin 2 → ℂ := ![1, -1]

theorem Theta_apply (ψ : Psi) (a b c d : Fin 2) :
    Theta ψ a b c d = sgn a * sgn b * sgn c * sgn d * conj (ψ (a + 1) (b + 1) (c + 1) (d + 1)) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [Theta, epsM, sgn, Fin.sum_univ_two]

theorem sgn_sq (a : Fin 2) : sgn a * sgn a = 1 := by
  fin_cases a <;> simp [sgn]

theorem ev_Theta (ψ : Psi) (x : Fin 4 → Fin 2) :
    ev (Theta ψ) x = (∏ k, sgn (x k)) * conj (ev ψ fun k => x k + 1) := by
  simp only [ev, Theta_apply, Fin.prod_univ_four]

theorem Theta_perm (σ : Equiv.Perm (Fin 4)) (ψ : Psi) :
    Theta (permPsi σ ψ) = permPsi σ (Theta ψ) := by
  apply eq_of_ev; intro x
  rw [ev_Theta, ev_perm, ev_perm, ev_Theta]
  have : ∏ k, sgn ((x ∘ σ) k) = ∏ k, sgn (x k) :=
    Equiv.prod_comp σ (fun k => sgn (x k))
  rw [this]
  rfl

theorem ip_Theta (φ ψ : Psi) : ip (Theta φ) (Theta ψ) = conj (ip φ ψ) := by
  simp only [ip, Theta_apply, Fin.sum_univ_two, map_mul, map_add, Complex.conj_conj]
  simp [sgn]
  ring


theorem chi_apply_cyc (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (ξ : Psi) :
    chi i j l ξ = (Complex.I / 4) • (permPsi (Equiv.swap i l * Equiv.swap i j) ξ
      - permPsi (Equiv.swap i j * Equiv.swap i l) ξ) := by
  rw [chi_eq_cyc i j l hij hil hjl]; rfl

/-- `χ_{ijl}` is odd under time reversal: `⟨Θψ|χ Θψ⟩ = -⟨ψ|χ ψ⟩`. -/
theorem chi_Theta_odd (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (ψ : Psi) :
    ip (Theta ψ) (chi i j l (Theta ψ)) = - ip ψ (chi i j l ψ) := by
  rw [chi_apply_cyc i j l hij hil hjl, chi_apply_cyc i j l hij hil hjl, ← Theta_perm, ← Theta_perm,
    ip_smul_right, ip_smul_right, ip_sub_right, ip_sub_right, ip_Theta, ip_Theta]
  have e1 : ip ψ (permPsi (Equiv.swap i j * Equiv.swap i l) ψ)
      = conj (ip ψ (permPsi (Equiv.swap i l * Equiv.swap i j) ψ)) := by
    rw [ip_perm, ip_conj_symm]
    simp [mul_inv_rev]
  rw [e1]
  simp only [Complex.conj_conj]
  ring

/-! ### Complex conjugation -/

theorem conj_perm (σ : Equiv.Perm (Fin 4)) (ψ : Psi) :
    Psi.conj (permPsi σ ψ) = permPsi σ (Psi.conj ψ) := by
  funext a b c d
  rfl

/-- `χ` anticommutes with complex conjugation (each Pauli string contains exactly one `σ_y`). -/
theorem chi_conj (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (ψ : Psi) :
    chi i j l (Psi.conj ψ) = - Psi.conj (chi i j l ψ) := by
  rw [chi_apply_cyc i j l hij hil hjl, chi_apply_cyc i j l hij hil hjl, ← conj_perm, ← conj_perm]
  funext a b c d
  simp only [Psi.conj, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul, map_mul, map_sub,
    map_div₀, Complex.conj_I, map_ofNat]
  ring

/-! ### `M₄` -/

theorem omega_eq' : omega = -1 / 2 + (((Real.sqrt 3 : ℝ) : ℂ) / 2) * Complex.I := by
  apply Complex.ext <;> simp [omega]

theorem omega_conj_eq' : conj omega = -1 / 2 - (((Real.sqrt 3 : ℝ) : ℂ) / 2) * Complex.I := by
  rw [omega_eq']; simp [map_add, map_mul, map_div₀, map_ofNat]; ring

theorem sqrt3_sq : (((Real.sqrt 3 : ℝ) : ℂ)) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow]; simp

abbrev Mat8 := Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ

def kron3 (A B C : Matrix (Fin 2) (Fin 2) ℂ) : Mat8 :=
  Matrix.of fun x y => A x.1 y.1 * B x.2.1 y.2.1 * C x.2.2 y.2.2

/-- `χ_{123}` on three qubits as an `8 × 8` matrix. -/
noncomputable def chi3 : Mat8 :=
  (1 / 8 : ℂ) • ∑ a, ∑ b, ∑ c, eps3 a b c • kron3 (pauli a) (pauli b) (pauli c)

/-- `SWAP_{13}` and `SWAP_{12}` on three qubits. -/
def swap13 : Mat8 := Matrix.of fun x y => if y = (x.2.2, x.2.1, x.1) then 1 else 0
def swap12 : Mat8 := Matrix.of fun x y => if y = (x.2.1, x.1, x.2.2) then 1 else 0

theorem chi3_six : chi3 = (1 / 8 : ℂ) • (
    kron3 pauliX pauliY pauliZ - kron3 pauliX pauliZ pauliY + kron3 pauliY pauliZ pauliX
    - kron3 pauliY pauliX pauliZ + kron3 pauliZ pauliX pauliY - kron3 pauliZ pauliY pauliX) := by
  unfold chi3
  simp only [Fin.sum_univ_three, eps3, pauli]
  congr 1
  ext x y
  simp
  norm_num
  ring

set_option maxHeartbeats 4000000 in
theorem swap3_commutator : (Complex.I) • (swap13 * swap12 - swap12 * swap13) = (4 : ℂ) • chi3 := by
  rw [chi3_six]
  ext ⟨a, b, c⟩ ⟨a', b', c'⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
  simp [swap13, swap12, kron3, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    pauliX, pauliY, pauliZ] <;> ring

theorem swap13_sq : swap13 * swap13 = 1 := by
  ext ⟨a, b, c⟩ ⟨a', b', c'⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
  simp [swap13, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem swap12_sq : swap12 * swap12 = 1 := by
  ext ⟨a, b, c⟩ ⟨a', b', c'⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
  simp [swap12, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

set_option maxHeartbeats 4000000 in
theorem swap_braid : swap13 * swap12 * swap13 = swap12 * swap13 * swap12 := by
  ext ⟨a, b, c⟩ ⟨a', b', c'⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
  simp [swap13, swap12, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]


set_option maxHeartbeats 4000000 in
theorem trace_swap_cyc : Matrix.trace (swap13 * swap12) = 2 := by
  simp [Matrix.trace, Matrix.mul_apply, swap13, swap12, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

theorem chi3_eq_cyc : chi3 = (Complex.I / 4) • (swap13 * swap12 - swap12 * swap13) := by
  have h := swap3_commutator
  have h4 : chi3 = (1 / 4 : ℂ) • ((4 : ℂ) • chi3) := by
    rw [smul_smul]; norm_num
  rw [h4, ← h, smul_smul]
  congr 1; ring

theorem sq13' (X : Mat8) : swap13 * (swap13 * X) = X := by
  rw [← mul_assoc, swap13_sq, one_mul]

theorem sq12' (X : Mat8) : swap12 * (swap12 * X) = X := by
  rw [← mul_assoc, swap12_sq, one_mul]

theorem cyc3_AB : (swap13 * swap12) * (swap12 * swap13) = 1 := by
  simp only [mul_assoc]; rw [← mul_assoc swap12 swap12, swap12_sq, one_mul, swap13_sq]

theorem cyc3_BA : (swap12 * swap13) * (swap13 * swap12) = 1 := by
  simp only [mul_assoc]; rw [← mul_assoc swap13 swap13, swap13_sq, one_mul, swap12_sq]

theorem cyc3_A3 : (swap13 * swap12) * (swap13 * swap12) * (swap13 * swap12) = 1 := by
  calc (swap13 * swap12) * (swap13 * swap12) * (swap13 * swap12)
      = (swap13 * swap12 * swap13) * (swap12 * swap13 * swap12) := by simp only [mul_assoc]
    _ = (swap12 * swap13 * swap12) * (swap12 * swap13 * swap12) := by rw [swap_braid]
    _ = 1 := by
      simp only [mul_assoc, sq12', sq13', swap12_sq]

theorem cyc3_B3 : (swap12 * swap13) * (swap12 * swap13) * (swap12 * swap13) = 1 := by
  calc (swap12 * swap13) * (swap12 * swap13) * (swap12 * swap13)
      = (swap12 * swap13 * swap12) * (swap13 * swap12 * swap13) := by simp only [mul_assoc]
    _ = (swap13 * swap12 * swap13) * (swap13 * swap12 * swap13) := by rw [swap_braid]
    _ = 1 := by
      simp only [mul_assoc, sq12', sq13', swap13_sq]

theorem chi3_cube' : chi3 * chi3 * chi3 = (3 / 16 : ℂ) • chi3 := by
  rw [chi3_eq_cyc]
  simp only [smul_mul_smul_comm, smul_smul]
  rw [cube_aux _ _ cyc3_AB cyc3_BA cyc3_A3 cyc3_B3, smul_smul]
  congr 1
  linear_combination (-(3 / 64) * Complex.I) * Complex.I_sq

theorem trace_chi3 : Matrix.trace chi3 = 0 := by
  rw [chi3_eq_cyc, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm swap12 swap13,
    sub_self, smul_zero]

theorem trace_chi3_sq : Matrix.trace (chi3 * chi3) = 3 / 4 := by
  have hAA : (swap13 * swap12) * (swap13 * swap12) = swap12 * swap13 := by
    calc (swap13 * swap12) * (swap13 * swap12)
        = (swap12 * swap13) * ((swap13 * swap12) * (swap13 * swap12) * (swap13 * swap12)) := by
          simp only [mul_assoc, sq12', sq13']
      _ = _ := by rw [cyc3_A3, mul_one]
  have hBB : (swap12 * swap13) * (swap12 * swap13) = swap13 * swap12 := by
    calc (swap12 * swap13) * (swap12 * swap13)
        = (swap13 * swap12) * ((swap12 * swap13) * (swap12 * swap13) * (swap12 * swap13)) := by
          simp only [mul_assoc, sq12', sq13']
      _ = _ := by rw [cyc3_B3, mul_one]
  rw [chi3_eq_cyc, smul_mul_smul_comm, Matrix.trace_smul]
  simp only [mul_sub, sub_mul, hAA, hBB, cyc3_AB, cyc3_BA, Matrix.trace_sub, Matrix.trace_one,
    trace_swap_cyc, Matrix.trace_mul_comm swap12 swap13]
  simp
  linear_combination (-3 / 4 : ℂ) * Complex.I_sq


/-! #### Spectral multiplicities `(2, 2, 4)` -/

theorem proj_aux {R : Type*} [Ring R] [Algebra ℂ R] (X : R) (μ : ℂ) (hμ : μ * μ = 3 / 16)
    (h3 : X * X * X = (3 / 16 : ℂ) • X) :
    ((8 / 3 : ℂ) • (X * X + μ • X)) * ((8 / 3 : ℂ) • (X * X + μ • X)) = (8 / 3 : ℂ) • (X * X + μ • X)
    ∧ X * ((8 / 3 : ℂ) • (X * X + μ • X)) = μ • ((8 / 3 : ℂ) • (X * X + μ • X)) := by
  have h3' : X * (X * X) = (3 / 16 : ℂ) • X := by rw [← mul_assoc]; exact h3
  have h4 : X * X * (X * X) = (3 / 16 : ℂ) • (X * X) := by
    rw [show X * X * (X * X) = X * X * X * X by simp only [mul_assoc], h3, smul_mul_assoc]
  constructor
  · simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_smul, h4, h3, h3']
    match_scalars <;> first | ring1 | linear_combination (64 / 9 : ℂ) * hμ
  · simp only [mul_add, mul_smul_comm, smul_smul, h3']
    match_scalars <;> first | ring1 | linear_combination (-8 / 3 : ℂ) * hμ


theorem proj_zero {R : Type*} [Ring R] [Algebra ℂ R] (X : R) (h3 : X * X * X = (3 / 16 : ℂ) • X) :
    (1 - (16 / 3 : ℂ) • (X * X)) * (1 - (16 / 3 : ℂ) • (X * X)) = 1 - (16 / 3 : ℂ) • (X * X)
    ∧ X * (1 - (16 / 3 : ℂ) • (X * X)) = (0 : ℂ) • (1 - (16 / 3 : ℂ) • (X * X)) := by
  have h3' : X * (X * X) = (3 / 16 : ℂ) • X := by rw [← mul_assoc]; exact h3
  have h4 : X * X * (X * X) = (3 / 16 : ℂ) • (X * X) := by
    rw [show X * X * (X * X) = X * X * X * X by simp only [mul_assoc], h3, smul_mul_assoc]
  constructor
  · simp only [mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, smul_smul, h4]
    match_scalars <;> ring1
  · simp only [mul_sub, mul_one, mul_smul_comm, smul_smul, h3', zero_smul]
    match_scalars
    ring1

theorem eigenspace_finrank (X P : Mat8) (μ : ℂ) (n : ℕ) (hP : P * P = P) (hXP : X * P = μ • P)
    (hv : ∀ v, X.mulVec v = μ • v → P.mulVec v = v) (htr : P.trace = n) :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' X) μ) = n := by
  have hrange : Module.End.eigenspace (Matrix.toLin' X) μ = LinearMap.range (Matrix.toLin' P) := by
    ext v
    simp only [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, LinearMap.mem_range]
    constructor
    · intro h; exact ⟨v, hv v h⟩
    · rintro ⟨w, rfl⟩
      rw [Matrix.mulVec_mulVec, hXP, Matrix.smul_mulVec]
  rw [hrange]
  have hproj : LinearMap.IsProj (LinearMap.range (Matrix.toLin' P)) (Matrix.toLin' P) := by
    rw [LinearMap.isProj_range_iff_isIdempotentElem]
    show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    have h := Matrix.toLin'_mul P P
    rw [hP] at h
    exact h.symm
  have := hproj.trace
  rw [Matrix.trace_toLin'_eq, htr] at this
  exact_mod_cast this.symm


theorem eig_vec (X : Mat8) (μ : ℂ) (hμ : μ * μ = 3 / 16) (v : Fin 2 × Fin 2 × Fin 2 → ℂ)
    (hv : X.mulVec v = μ • v) : ((8 / 3 : ℂ) • (X * X + μ • X)).mulVec v = v := by
  have e : (X * X).mulVec v = μ • μ • v := by
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, hv]
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, e, Matrix.smul_mulVec, hv]
  match_scalars
  linear_combination (16 / 3 : ℂ) * hμ

theorem eig_vec_zero (X : Mat8) (v : Fin 2 × Fin 2 × Fin 2 → ℂ)
    (hv : X.mulVec v = (0 : ℂ) • v) : (1 - (16 / 3 : ℂ) • (X * X)).mulVec v = v := by
  have e : (X * X).mulVec v = 0 := by
    rw [← Matrix.mulVec_mulVec, hv, zero_smul, Matrix.mulVec_zero]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, e, Matrix.one_mulVec]
  simp

theorem chi3_multiplicities :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' chi3) ((Real.sqrt 3 : ℝ) / 4 : ℂ)) = 2 ∧
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' chi3) (-((Real.sqrt 3 : ℝ) / 4 : ℂ))) = 2 ∧
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' chi3) 0) = 4 := by
  have hl : (((Real.sqrt 3 : ℝ) / 4 : ℂ)) * (((Real.sqrt 3 : ℝ) / 4 : ℂ)) = 3 / 16 := by
    have := sqrt3_sq
    linear_combination (1 / 16 : ℂ) * this
  have hl' : (-((Real.sqrt 3 : ℝ) / 4 : ℂ)) * (-((Real.sqrt 3 : ℝ) / 4 : ℂ)) = 3 / 16 := by
    linear_combination hl
  have hXX := trace_chi3_sq
  have hX := trace_chi3
  have hc := chi3_cube'
  have tr8 : Matrix.trace (1 : Mat8) = 8 := by simp [Matrix.trace_one]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hP, hXP⟩ := proj_aux chi3 _ hl hc
    refine eigenspace_finrank chi3 _ _ 2 hP hXP (fun v hv => eig_vec chi3 _ hl v hv) ?_
    simp [Matrix.trace_add, Matrix.trace_smul, hXX, hX]
    norm_num
  · obtain ⟨hP, hXP⟩ := proj_aux chi3 _ hl' hc
    refine eigenspace_finrank chi3 _ _ 2 hP hXP (fun v hv => eig_vec chi3 _ hl' v hv) ?_
    simp [Matrix.trace_add, Matrix.trace_smul, hXX, hX]
    norm_num
  · obtain ⟨hP, hXP⟩ := proj_zero chi3 hc
    refine eigenspace_finrank chi3 _ _ 4 hP hXP (fun v hv => eig_vec_zero chi3 v hv) ?_
    simp [Matrix.trace_sub, Matrix.trace_smul, hXX, tr8]
    norm_num


/-! ### `M₄` is an eigenvector of every scalar chirality -/

/-- `χ_{123} M₄ = -(√3/4) M₄`. -/
theorem chi_M4_012 : chi 0 1 2 M4 = ((-(Real.sqrt 3 / 4) : ℝ) : ℂ) • M4 := by
  rw [chi_apply_cyc 0 1 2 (by decide) (by decide) (by decide)]
  funext a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [permPsi, M4, Equiv.swap_apply_def]
  all_goals ((try rw [omega_conj_eq']); (try rw [omega_eq']); ring_nf; simp only [Complex.I_sq, sqrt3_sq]; ring_nf)

/-- `χ_{124} M₄ = +(√3/4) M₄`. -/
theorem chi_M4_013 : chi 0 1 3 M4 = (((Real.sqrt 3 / 4) : ℝ) : ℂ) • M4 := by
  rw [chi_apply_cyc 0 1 3 (by decide) (by decide) (by decide)]
  funext a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [permPsi, M4, Equiv.swap_apply_def]
  all_goals ((try rw [omega_conj_eq']); (try rw [omega_eq']); ring_nf; simp only [Complex.I_sq, sqrt3_sq]; ring_nf)

/-- `χ_{134} M₄ = -(√3/4) M₄`. -/
theorem chi_M4_023 : chi 0 2 3 M4 = ((-(Real.sqrt 3 / 4) : ℝ) : ℂ) • M4 := by
  rw [chi_apply_cyc 0 2 3 (by decide) (by decide) (by decide)]
  funext a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [permPsi, M4, Equiv.swap_apply_def]
  all_goals ((try rw [omega_conj_eq']); (try rw [omega_eq']); ring_nf; simp only [Complex.I_sq, sqrt3_sq]; ring_nf)

/-- `χ_{234} M₄ = +(√3/4) M₄`. -/
theorem chi_M4_123 : chi 1 2 3 M4 = (((Real.sqrt 3 / 4) : ℝ) : ℂ) • M4 := by
  rw [chi_apply_cyc 1 2 3 (by decide) (by decide) (by decide)]
  funext a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [permPsi, M4, Equiv.swap_apply_def]
  all_goals ((try rw [omega_conj_eq']); (try rw [omega_eq']); ring_nf; simp only [Complex.I_sq, sqrt3_sq]; ring_nf)

/-- If `χ ψ = r ψ` with `r` real then `χ (conj ψ) = -r (conj ψ)`. -/
theorem chi_conj_eigen (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (ψ : Psi) (r : ℝ)
    (h : chi i j l ψ = (r : ℂ) • ψ) : chi i j l (Psi.conj ψ) = ((-r : ℝ) : ℂ) • Psi.conj ψ := by
  rw [chi_conj i j l hij hil hjl, h]
  funext a b c d
  simp [Psi.conj]

theorem chi_M4_012_conj :
    chi 0 1 2 (Psi.conj M4) = (((Real.sqrt 3 / 4) : ℝ) : ℂ) • Psi.conj M4 := by
  have := chi_conj_eigen 0 1 2 (by decide) (by decide) (by decide) M4 _ chi_M4_012
  simpa using this

theorem chi_M4_013_conj :
    chi 0 1 3 (Psi.conj M4) = ((-(Real.sqrt 3 / 4) : ℝ) : ℂ) • Psi.conj M4 :=
  chi_conj_eigen 0 1 3 (by decide) (by decide) (by decide) M4 _ chi_M4_013

theorem chi_M4_023_conj :
    chi 0 2 3 (Psi.conj M4) = (((Real.sqrt 3 / 4) : ℝ) : ℂ) • Psi.conj M4 := by
  have := chi_conj_eigen 0 2 3 (by decide) (by decide) (by decide) M4 _ chi_M4_023
  simpa using this

theorem chi_M4_123_conj :
    chi 1 2 3 (Psi.conj M4) = ((-(Real.sqrt 3 / 4) : ℝ) : ℂ) • Psi.conj M4 :=
  chi_conj_eigen 1 2 3 (by decide) (by decide) (by decide) M4 _ chi_M4_123

/-! ### The four-qubit `χ₁₂₃` is `χ₁₂₃ ⊗ 1` -/

set_option maxHeartbeats 4000000 in
theorem chi_bridge (ψ : Psi) (a b c d : Fin 2) :
    chi 0 1 2 ψ a b c d = ∑ x : Fin 2 × Fin 2 × Fin 2, chi3 (a, b, c) x * ψ x.1 x.2.1 x.2.2 d := by
  rw [chi_six, chi3_six]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [actOn, kron3, Fintype.sum_prod_type, Fin.sum_univ_two,
    pauliX, pauliY, pauliZ, Finset.sum_add_distrib] <;> ring

/-! ### Dimension of the odd-invariant space for `n` spins with a common frame -/

/-- Multiplicity `g_j = C(n, j') - C(n, j'-1)` of total spin `j = n/2 - j'` among `n` spin-`1/2`. -/
def mult (n j' : ℕ) : ℕ := Nat.choose n j' - (if j' = 0 then 0 else Nat.choose n (j' - 1))

/-- `Σ_j C(g_j, 2)`, the dimension of the real space of odd invariants (`j' = n/2 - j = 0, …, ⌊n/2⌋`). -/
def oddDim (n : ℕ) : ℕ := ∑ j' ∈ Finset.range (n / 2 + 1), Nat.choose (mult n j') 2

/-- `Σ_j (2j+1) g_j`, with `2j + 1 = n - 2j' + 1`. -/
def totalDim (n : ℕ) : ℕ := ∑ j' ∈ Finset.range (n / 2 + 1), (n - 2 * j' + 1) * mult n j'

theorem oddDim_values :
    oddDim 2 = 0 ∧ oddDim 3 = 1 ∧ oddDim 4 = 4 ∧ oddDim 5 = 16 ∧ oddDim 6 = 56 := by
  decide

theorem totalDim_values :
    totalDim 2 = 2 ^ 2 ∧ totalDim 3 = 2 ^ 3 ∧ totalDim 4 = 2 ^ 4 ∧ totalDim 5 = 2 ^ 5 ∧
      totalDim 6 = 2 ^ 6 := by
  decide

/-- The multiplicities themselves, `j' = 0, 1, …`. -/
theorem mult_values :
    (List.range 2).map (mult 2) = [1, 1] ∧ (List.range 2).map (mult 3) = [1, 2] ∧
    (List.range 3).map (mult 4) = [1, 3, 2] ∧ (List.range 3).map (mult 5) = [1, 4, 5] ∧
    (List.range 4).map (mult 6) = [1, 5, 9, 5] := by
  decide

end FormalResearch.FrameFree.ScalarChirality

