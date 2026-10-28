import FormalResearch.FourQubitEntropy.SevenQubitIcoState

/-!
# Local time-reversal shadows of the icosahedral state (`prop:ico-shadow-geometry`, TR-1, TR-2)

`ResearchNotes/QI/seven_qubit_entanglement/shadow_equality_geometry.tex`. For a seven-qubit tensor
`F` (real, which is all that is needed for `icosahedralState`) and a site `q`:

* `That F q a b = ⟨e_a, J₆ e_b⟩` is the normalized Schmidt spin-flip overlap matrix at `q`, where
  `e_a = √2 · F(·, bit q = a)` are the two normalized Schmidt branches (when the marginal at `q` is
  `I/2`) and `J₆ = ε^{⊗6} K` acts on the other six qubits as `(J₆ v)(x) = (-1)^{|x|} v(x̄)`
  (`ε = ((0,1),(-1,0))`; `ε^{⊗6}` does not depend on the sign convention of `ε`);
* `shadowComp α F q = ⟨F, σ_α^{(q)} J₇ F⟩` for `α ∈ {x, y, z}` with `J₇ = ε^{⊗7} K`, and
  `shadowQ F q = ∑_α |⟨F, σ_α^{(q)} J₇ F⟩|²` is `q_q` of `prop:shadow-complement`.

Results, for the whole family `icosahedralState α β` and then at `Ψico` (`α² = 15/524`, `β² = 37/524`):

* `That_ico`: `T̂^{(s)} = [[0, -30α²+2β²], [-30α²+2β², 0]]` at the special site `0` and
  `T̂^{(i)} = [[0, -10α²-2β²], [·, 0]]` at each of the six ordinary sites; at `Ψico` these are
  `-94/131` and `-56/131`;
* `shadowQ_ico`: `q_s = (94/131)²`, `q_i = (56/131)²`, hence `S₁ = q_s + 6 q_i = 27652/17161`
  (`shadowQ_sum_ico`).

The Pauli weight distributions `B^{(s)}`, `B^{(i)}`, `A`, `S` of the proposition are not treated here.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

open Finset

/-- Bitwise complement of a string. -/
def compl (y : BitString) : BitString := fun j => !(y j)

/-- Flip the bit at site `q`. -/
def flipAt (q : Fin 7) (y : BitString) : BitString := Function.update y q (!(y q))

/-- Flip every bit except the one at `q`. -/
def flipOthers (q : Fin 7) (y : BitString) : BitString := compl (flipAt q y)

/-- `(-1)^{|y|}`. -/
def sgnW (y : BitString) : ℤ := (-1) ^ (∑ j, if y j then 1 else 0 : ℕ)

/-! ### The overlap matrix `T̂` -/

/-- Normalized Schmidt spin-flip overlap `T̂^{(q)}_{ab} = ⟨e_a, J₆ e_b⟩ = 2 ∑_x u_a(x) (-1)^{|x|} u_b(x̄)`,
where `u_a = F(·, bit q = a)` and `x` runs over the six other bits (here carried by strings `y` with
`y q = a`; `Function.update y q false` removes the contribution of site `q` to the weight). -/
def That (F : BitString → ℝ) (q : Fin 7) (a b : Bool) : ℝ :=
  2 * ∑ y ∈ univ.filter (fun y : BitString => y q = a),
    (sgnW (Function.update y q false) : ℝ) * F y * F (Function.update (flipOthers q y) q b)

/-! ### The shadow overlaps `q_q` -/

/-- The spin flip `J₇ F (y) = (-1)^{|y|} F(ȳ)` of a real tensor (`ε^{⊗7} K`). -/
def J7 (F : BitString → ℝ) (y : BitString) : ℝ := (sgnW y : ℝ) * F (compl y)

/-- The Pauli matrices `σ_x, σ_y, σ_z` (index `0, 1, 2`), entry `(a, b)`. -/
def pauli : Fin 3 → Bool → Bool → ℂ
  | 0 => fun a b => if a = b then 0 else 1
  | 1 => fun a b => if a = b then 0 else (if a then Complex.I else -Complex.I)
  | 2 => fun a b => if a = b then (if a then -1 else 1) else 0

/-- `⟨F, σ_α^{(q)} J₇ F⟩`. -/
noncomputable def shadowComp (α : Fin 3) (F : BitString → ℝ) (q : Fin 7) : ℂ :=
  ∑ y : BitString, (F y : ℂ) *
    ∑ b : Bool, pauli α (y q) b * (J7 F (Function.update y q b) : ℂ)

/-- `q_q = ∑_α |⟨F, σ_α^{(q)} J₇ F⟩|²`. -/
noncomputable def shadowQ (F : BitString → ℝ) (q : Fin 7) : ℝ :=
  ∑ α : Fin 3, Complex.normSq (shadowComp α F q)

/-! ### Integer bilinear forms -/

/-- `∑_y c(y) f(y) g(π y)` over the integers. -/
def formZ (c : BitString → ℤ) (π : BitString → BitString) (f g : BitString → ℤ) : ℤ :=
  ∑ y, c y * f y * g (π y)

/-- The same over the reals. -/
def formR (c : BitString → ℤ) (π : BitString → BitString) (F G : BitString → ℝ) : ℝ :=
  ∑ y, (c y : ℝ) * F y * G (π y)

theorem formR_ico (c : BitString → ℤ) (π : BitString → BitString) (alpha beta : ℝ) :
    formR c π (icosahedralState alpha beta) (icosahedralState alpha beta) =
      alpha ^ 2 * (formZ c π alphaCoefficient alphaCoefficient : ℝ) +
        alpha * beta * ((formZ c π alphaCoefficient betaCoefficient +
          formZ c π betaCoefficient alphaCoefficient : ℤ) : ℝ) +
        beta ^ 2 * (formZ c π betaCoefficient betaCoefficient : ℝ) := by
  unfold formR formZ
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [icosahedralState]
  ring

/-! ### The values -/

/-- The weight function and map for `T̂^{(q)}_{ab}`. -/
def thatC (q : Fin 7) (a : Bool) (y : BitString) : ℤ :=
  2 * (if y q = a then sgnW (Function.update y q false) else 0)

def thatPi (q : Fin 7) (b : Bool) (y : BitString) : BitString :=
  Function.update (flipOthers q y) q b

theorem That_eq_formR (F : BitString → ℝ) (q : Fin 7) (a b : Bool) :
    That F q a b = formR (thatC q a) (thatPi q b) F F := by
  unfold That formR thatC thatPi
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : y q = a <;> simp [h] <;> ring

/-- Diagonal entries of `T̂`: all four integer forms vanish. -/
theorem that_diag : ∀ (q : Fin 7) (a : Bool),
    formZ (thatC q a) (thatPi q a) alphaCoefficient alphaCoefficient = 0 ∧
    formZ (thatC q a) (thatPi q a) alphaCoefficient betaCoefficient +
      formZ (thatC q a) (thatPi q a) betaCoefficient alphaCoefficient = 0 ∧
    formZ (thatC q a) (thatPi q a) betaCoefficient betaCoefficient = 0 := by
  decide +kernel

/-- Off-diagonal entries of `T̂`. -/
theorem that_offdiag : ∀ (q : Fin 7) (a : Bool),
    formZ (thatC q a) (thatPi q (!a)) alphaCoefficient alphaCoefficient =
      (if q = 0 then -30 else -10) ∧
    formZ (thatC q a) (thatPi q (!a)) alphaCoefficient betaCoefficient +
      formZ (thatC q a) (thatPi q (!a)) betaCoefficient alphaCoefficient = 0 ∧
    formZ (thatC q a) (thatPi q (!a)) betaCoefficient betaCoefficient =
      (if q = 0 then 2 else -2) := by
  decide +kernel

/-- **TR-1.** The overlap matrix `T̂^{(q)}` of the family `ψ_x`: zero diagonal and off-diagonal
entry `-30α²+2β²` at the special site `0` and `-10α²-2β²` at the six ordinary sites. -/
theorem That_ico (alpha beta : ℝ) (q : Fin 7) (a b : Bool) :
    That (icosahedralState alpha beta) q a b =
      if a = b then 0
      else if q = 0 then -30 * alpha ^ 2 + 2 * beta ^ 2 else -10 * alpha ^ 2 - 2 * beta ^ 2 := by
  rw [That_eq_formR, formR_ico]
  by_cases hab : a = b
  · subst hab
    obtain ⟨h1, h2, h4⟩ := that_diag q a
    rw [h1, h2, h4]; simp
  · have hb : b = !a := by cases a <;> cases b <;> simp_all
    subst hb
    obtain ⟨h1, h2, h4⟩ := that_offdiag q a
    rw [h1, h2, h4]
    by_cases hq : q = 0 <;> simp [hq] <;> ring

/-- At `Ψico`: `T̂^{(s)}` has off-diagonal entry `-94/131`. -/
theorem That_ico_special (alpha beta : ℝ) (hα : alpha ^ 2 = u (37 / 524))
    (hβ : beta ^ 2 = 37 / 524) (a b : Bool) :
    That (icosahedralState alpha beta) 0 a b = if a = b then 0 else -94 / 131 := by
  rw [That_ico]
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, if_false, if_true, hα, hβ]; unfold u; norm_num

/-- At `Ψico`: `T̂^{(i)}` has off-diagonal entry `-56/131` at each ordinary site. -/
theorem That_ico_ordinary (alpha beta : ℝ) (hα : alpha ^ 2 = u (37 / 524))
    (hβ : beta ^ 2 = 37 / 524) (q : Fin 7) (hq : q ≠ 0) (a b : Bool) :
    That (icosahedralState alpha beta) q a b = if a = b then 0 else -56 / 131 := by
  rw [That_ico]
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, hq, if_false, hα, hβ]; unfold u; norm_num

/-! ### The shadow overlaps -/

/-- The three real forms underlying `shadowComp`. -/
def shC (α : Fin 3) (q : Fin 7) (y : BitString) : ℤ :=
  match α with
  | 0 => sgnW (flipAt q y)
  | 1 => (if y q then 1 else -1) * sgnW (flipAt q y)
  | 2 => (if y q then -1 else 1) * sgnW y

def shPi (α : Fin 3) (q : Fin 7) (y : BitString) : BitString :=
  match α with
  | 0 => compl (flipAt q y)
  | 1 => compl (flipAt q y)
  | 2 => compl y

theorem shadowComp_x (F : BitString → ℝ) (q : Fin 7) :
    shadowComp 0 F q = ((formR (shC 0 q) (shPi 0 q) F F : ℝ) : ℂ) := by
  unfold shadowComp formR
  push_cast
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Fintype.sum_bool]
  cases h : y q <;>
    simp [pauli, shC, shPi, J7, flipAt, h] <;> ring

theorem shadowComp_y (F : BitString → ℝ) (q : Fin 7) :
    shadowComp 1 F q = Complex.I * ((formR (shC 1 q) (shPi 1 q) F F : ℝ) : ℂ) := by
  unfold shadowComp formR
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Fintype.sum_bool]
  cases h : y q <;>
    simp [pauli, shC, shPi, J7, flipAt, h] <;> ring

theorem shadowComp_z (F : BitString → ℝ) (q : Fin 7) :
    shadowComp 2 F q = ((formR (shC 2 q) (shPi 2 q) F F : ℝ) : ℂ) := by
  unfold shadowComp formR
  push_cast
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Fintype.sum_bool]
  have e : Function.update y q (y q) = y := Function.update_eq_self q y
  cases h : y q <;> rw [h] at e <;>
    simp [pauli, shC, shPi, J7, h, e] <;> ring

theorem shadowQ_eq (F : BitString → ℝ) (q : Fin 7) :
    shadowQ F q = (formR (shC 0 q) (shPi 0 q) F F) ^ 2 + (formR (shC 1 q) (shPi 1 q) F F) ^ 2 +
      (formR (shC 2 q) (shPi 2 q) F F) ^ 2 := by
  unfold shadowQ
  rw [Fin.sum_univ_three, shadowComp_x, shadowComp_y, shadowComp_z]
  simp [Complex.normSq_ofReal, Complex.normSq_mul, sq]

/-- The integer forms for the three components. -/
theorem shadow_forms : ∀ q : Fin 7,
    (formZ (shC 0 q) (shPi 0 q) alphaCoefficient alphaCoefficient = 0 ∧
     formZ (shC 0 q) (shPi 0 q) alphaCoefficient betaCoefficient +
       formZ (shC 0 q) (shPi 0 q) betaCoefficient alphaCoefficient = 0 ∧
     formZ (shC 0 q) (shPi 0 q) betaCoefficient betaCoefficient = 0) ∧
    (formZ (shC 1 q) (shPi 1 q) alphaCoefficient alphaCoefficient = 0 ∧
     formZ (shC 1 q) (shPi 1 q) alphaCoefficient betaCoefficient +
       formZ (shC 1 q) (shPi 1 q) betaCoefficient alphaCoefficient = 0 ∧
     formZ (shC 1 q) (shPi 1 q) betaCoefficient betaCoefficient = 0) ∧
    (formZ (shC 2 q) (shPi 2 q) alphaCoefficient alphaCoefficient = (if q = 0 then -30 else -10) ∧
     formZ (shC 2 q) (shPi 2 q) alphaCoefficient betaCoefficient +
       formZ (shC 2 q) (shPi 2 q) betaCoefficient alphaCoefficient = 0 ∧
     formZ (shC 2 q) (shPi 2 q) betaCoefficient betaCoefficient = (if q = 0 then 2 else -2)) := by
  decide +kernel

/-- **TR-2.** The shadow overlap `q_q` of the family: `(−30α²+2β²)²` at the special site and
`(10α²+2β²)²` at an ordinary site. (Only the `σ_z`-component is nonzero.) -/
theorem shadowQ_ico (alpha beta : ℝ) (q : Fin 7) :
    shadowQ (icosahedralState alpha beta) q =
      if q = 0 then (-30 * alpha ^ 2 + 2 * beta ^ 2) ^ 2 else (10 * alpha ^ 2 + 2 * beta ^ 2) ^ 2 := by
  rw [shadowQ_eq, formR_ico, formR_ico, formR_ico]
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩⟩ := shadow_forms q
  rw [a1, a2, a3, b1, b2, b3, c1, c2, c3]
  by_cases hq : q = 0 <;> simp [hq] <;> ring

/-- At `Ψico`, `q_s = (94/131)²`. -/
theorem shadowQ_ico_special (alpha beta : ℝ) (hα : alpha ^ 2 = u (37 / 524))
    (hβ : beta ^ 2 = 37 / 524) :
    shadowQ (icosahedralState alpha beta) 0 = (94 / 131) ^ 2 := by
  rw [shadowQ_ico]; simp only [if_true, hα, hβ]; unfold u; norm_num

/-- At `Ψico`, `q_i = (56/131)²` at each ordinary site. -/
theorem shadowQ_ico_ordinary (alpha beta : ℝ) (hα : alpha ^ 2 = u (37 / 524))
    (hβ : beta ^ 2 = 37 / 524) (q : Fin 7) (hq : q ≠ 0) :
    shadowQ (icosahedralState alpha beta) q = (56 / 131) ^ 2 := by
  rw [shadowQ_ico]; simp only [hq, if_false, hα, hβ]; unfold u; norm_num

/-- At `Ψico`, `S₁ = ∑_q q_q = q_s + 6 q_i = 27652/17161`. -/
theorem shadowQ_sum_ico (alpha beta : ℝ) (hα : alpha ^ 2 = u (37 / 524))
    (hβ : beta ^ 2 = 37 / 524) :
    ∑ q : Fin 7, shadowQ (icosahedralState alpha beta) q = 27652 / 17161 := by
  rw [Fin.sum_univ_succ]
  simp only [shadowQ_ico_ordinary alpha beta hα hβ _ (Fin.succ_ne_zero _), shadowQ_ico_special alpha beta hα hβ]
  simp [Fin.sum_const]
  norm_num

/-- Each branch of `T̂` has `|T̂_{01}| = √q`: `q_q = (T̂^{(q)}_{01})²`
(`q = (t₁² + t₂²)/2` with both Takagi values `t = |T̂₀₁|`). -/
theorem shadowQ_eq_That_sq (alpha beta : ℝ) (q : Fin 7) :
    shadowQ (icosahedralState alpha beta) q =
      (That (icosahedralState alpha beta) q false true) ^ 2 := by
  rw [shadowQ_ico, That_ico]
  by_cases hq : q = 0 <;> simp [hq] <;> ring

end FormalResearch.FourQubitEntropy.SevenQubitIco
