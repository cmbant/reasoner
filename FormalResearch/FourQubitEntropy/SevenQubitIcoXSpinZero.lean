import FormalResearch.FourQubitEntropy.SevenQubitIcoCert
import FormalResearch.FourQubitEntropy.Attainment

/-!
# The four-qubit singlet sector of the icosahedral family (`prop:ico-m4-spinzero`, IM-1)

`ResearchNotes/QI/seven_qubit_entanglement/balanced_purity.tex`, `prop:ico-m4-spinzero`.

On four qubits (a four-site set `T`, ordered as the `l = 4` side of `maskCut 3 4 m`) the total-spin-zero
subspace of `(ℝ²)^{⊗4}` is two-dimensional. `SpinZero v` is the real-linear condition
`S^z v = 0 ∧ S^+ v = 0`; `spinZero_iff` shows it holds exactly on the span of the two pair-singlet
products `w1 = (12|34)`, `w2 = (13|24)`, i.e. exactly on the range of the integer projector `P6/6`
(`P6 = 2(w1w1ᵀ + w2w2ᵀ) - w1w2ᵀ - w2w1ᵀ`, the Gram matrix of `(w1, w2)` being `[[4,2],[2,4]]`).
`P6_eq_M4` identifies `P6/6 = |M₄⟩⟨M₄| + |M̄₄⟩⟨M̄₄|` with the Higuchi–Sudbery state
`M₄ = (|0011⟩+|1100⟩+ω(|0101⟩+|1010⟩)+ω²(|0110⟩+|1001⟩))/√6`.

For the icosahedral family `ψ_x = α U + β V` and each of the 35 four-site sets `T`
(`T` = complement of the three-site side `m`; `site 0` is the special qubit `s`):

* `P0_V` : `P₀ V = 0` (all 35 cuts);
* `P0rhoP0_rank_one` : `P₀ ρ_T P₀ = κ v vᵀ` has rank at most one;
* `qformC_values`, `table_counts` : `6 tr(P₀ ρ_T) / α² ∈ {0, 16, 48}`, i.e.
  `tr(P₀ρ_T) ∈ {0, 8u/3, 8u}` with `u = α²`, with the table of counts
  `s∈T: 5, 15, 0` and `s∉T: 0, 10, 5`;
* `weight48_product_singlet` : on the five cuts of weight `8u` the nonzero spin-zero column is
  `w_π (w_πᵀ U)/4` for one of the three pair-singlet products `w_π`;
* `weight16_orthogonal` : on the other cuts with nonzero weight, `w_πᵀ U = 0` for one `π`;
* `fidelity_M4`: `⟨M₄, ρ_T M₄⟩ = ⟨M̄₄, ρ_T M̄₄⟩ = tr(P₀ρ_T)/2`, so the fidelities lie in
  `{0, 4u/3, 4u}`, equal to `{0, 5/131, 15/131}` at `Ψico`.
-/

open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-- Basis strings of the four-site set `T`. -/
abbrev Quad := Fin 4 → Bool

/-- Singlet coefficient `|01⟩ - |10⟩` of a pair of bits. -/
def sing (a b : Bool) : ℤ := if a = b then 0 else if a then -1 else 1

/-- The product of two pair singlets on `{i,j}` and `{k,l}`. -/
def pairVec (i j k l : Fin 4) (r : Quad) : ℤ := sing (r i) (r j) * sing (r k) (r l)

/-- The three pairings `12|34`, `13|24`, `14|23`. -/
def pairing : Fin 3 → Quad → ℤ
  | 0 => pairVec 0 1 2 3
  | 1 => pairVec 0 2 1 3
  | 2 => pairVec 0 3 1 2

def w1 : Quad → ℤ := pairing 0
def w2 : Quad → ℤ := pairing 1

/-- Six times the projector onto the total-spin-zero space. -/
def P6 (r s : Quad) : ℤ :=
  2 * (w1 r * w1 s + w2 r * w2 s) - w1 r * w2 s - w2 r * w1 s

/-- `S^z v = 0`: `v` is supported on strings with two excitations. -/
def SzZero (v : Quad → ℝ) : Prop := ∀ r : Quad, (∑ i, if r i then 1 else 0 : ℕ) ≠ 2 → v r = 0

/-- `S^+ v = 0`: `∑_{i : r i = 1} v(r with bit i lowered) = 0` for all `r`. -/
def SplusZero (v : Quad → ℝ) : Prop :=
  ∀ r : Quad, ∑ i, (if r i then v (Function.update r i false) else 0) = 0

/-- Total spin zero. -/
def SpinZero (v : Quad → ℝ) : Prop := SzZero v ∧ SplusZero v

theorem P6_symm : ∀ r s : Quad, P6 r s = P6 s r := by decide +kernel

theorem P6_idem : ∀ r s : Quad, ∑ t, P6 r t * P6 t s = 6 * P6 r s := by decide +kernel

theorem P6_trace : ∑ r : Quad, P6 r r = 12 := by decide +kernel

theorem gram_w : (∑ r : Quad, w1 r * w1 r = 4) ∧ (∑ r : Quad, w1 r * w2 r = 2) ∧
    (∑ r : Quad, w2 r * w2 r = 4) := by decide +kernel

theorem w1_spinZero : SpinZero (fun r => (w1 r : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro r hr
    have : ∀ r : Quad, (∑ i, if r i then 1 else 0 : ℕ) ≠ 2 → w1 r = 0 := by decide +kernel
    simp [this r hr]
  · intro r
    have : ∀ r : Quad, ∑ i, (if r i then w1 (Function.update r i false) else 0) = 0 := by
      decide +kernel
    beta_reduce
    exact_mod_cast this r

theorem w2_spinZero : SpinZero (fun r => (w2 r : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro r hr
    have : ∀ r : Quad, (∑ i, if r i then 1 else 0 : ℕ) ≠ 2 → w2 r = 0 := by decide +kernel
    simp [this r hr]
  · intro r
    have : ∀ r : Quad, ∑ i, (if r i then w2 (Function.update r i false) else 0) = 0 := by
      decide +kernel
    beta_reduce
    exact_mod_cast this r

theorem P6_w1 : ∀ r : Quad, ∑ s, P6 r s * w1 s = 6 * w1 r := by decide +kernel
theorem P6_w2 : ∀ r : Quad, ∑ s, P6 r s * w2 s = 6 * w2 r := by decide +kernel

/-! ### The spin-zero space is the range of `P6/6` -/

def s0011 : Quad := ![false, false, true, true]
def s0101 : Quad := ![false, true, false, true]
def s0110 : Quad := ![false, true, true, false]
def s1001 : Quad := ![true, false, false, true]
def s1010 : Quad := ![true, false, true, false]
def s1100 : Quad := ![true, true, false, false]

theorem weight_two_cases : ∀ r : Quad, (∑ i, if r i then 1 else 0 : ℕ) = 2 →
    r = s0011 ∨ r = s0101 ∨ r = s0110 ∨ r = s1001 ∨ r = s1010 ∨ r = s1100 := by
  decide +kernel

theorem w1_off : ∀ r : Quad, (∑ i, if r i then 1 else 0 : ℕ) ≠ 2 → w1 r = 0 ∧ w2 r = 0 := by
  decide +kernel

theorem splus_0111 (v : Quad → ℝ) :
    ∑ i, (if (![false, true, true, true] : Quad) i then
      v (Function.update (![false, true, true, true] : Quad) i false) else 0) =
      v s0011 + v s0101 + v s0110 := by
  have u1 : Function.update (![false, true, true, true] : Quad) 1 false = s0011 := by decide +kernel
  have u2 : Function.update (![false, true, true, true] : Quad) 2 false = s0101 := by decide +kernel
  have u3 : Function.update (![false, true, true, true] : Quad) 3 false = s0110 := by decide +kernel
  simp [Fin.sum_univ_four, u1, u2, u3]

theorem splus_1011 (v : Quad → ℝ) :
    ∑ i, (if (![true, false, true, true] : Quad) i then
      v (Function.update (![true, false, true, true] : Quad) i false) else 0) =
      v s0011 + v s1001 + v s1010 := by
  have u1 : Function.update (![true, false, true, true] : Quad) 0 false = s0011 := by decide +kernel
  have u2 : Function.update (![true, false, true, true] : Quad) 2 false = s1001 := by decide +kernel
  have u3 : Function.update (![true, false, true, true] : Quad) 3 false = s1010 := by decide +kernel
  simp [Fin.sum_univ_four, u1, u2, u3]

theorem splus_1101 (v : Quad → ℝ) :
    ∑ i, (if (![true, true, false, true] : Quad) i then
      v (Function.update (![true, true, false, true] : Quad) i false) else 0) =
      v s0101 + v s1001 + v s1100 := by
  have u1 : Function.update (![true, true, false, true] : Quad) 0 false = s0101 := by decide +kernel
  have u2 : Function.update (![true, true, false, true] : Quad) 1 false = s1001 := by decide +kernel
  have u3 : Function.update (![true, true, false, true] : Quad) 3 false = s1100 := by decide +kernel
  simp [Fin.sum_univ_four, u1, u2, u3]

theorem splus_1110 (v : Quad → ℝ) :
    ∑ i, (if (![true, true, true, false] : Quad) i then
      v (Function.update (![true, true, true, false] : Quad) i false) else 0) =
      v s0110 + v s1010 + v s1100 := by
  have u1 : Function.update (![true, true, true, false] : Quad) 0 false = s0110 := by decide +kernel
  have u2 : Function.update (![true, true, true, false] : Quad) 1 false = s1010 := by decide +kernel
  have u3 : Function.update (![true, true, true, false] : Quad) 2 false = s1100 := by decide +kernel
  simp [Fin.sum_univ_four, u1, u2, u3]

/-- Every total-spin-zero vector is a combination of the two pair-singlet products. -/
theorem spinZero_comb (v : Quad → ℝ) (hv : SpinZero v) :
    ∃ a b : ℝ, ∀ r, v r = a * w1 r + b * w2 r := by
  obtain ⟨hz, hp⟩ := hv
  have e1 := hp ![false, true, true, true]
  have e2 := hp ![true, false, true, true]
  have e3 := hp ![true, true, false, true]
  have e4 := hp ![true, true, true, false]
  rw [splus_0111] at e1
  rw [splus_1011] at e2
  rw [splus_1101] at e3
  rw [splus_1110] at e4
  refine ⟨v s0101, v s0011, fun r => ?_⟩
  by_cases hr : (∑ i, if r i then 1 else 0 : ℕ) = 2
  · have hw : w1 s0011 = 0 ∧ w2 s0011 = 1 ∧ w1 s0101 = 1 ∧ w2 s0101 = 0 ∧ w1 s0110 = -1 ∧
        w2 s0110 = -1 ∧ w1 s1001 = -1 ∧ w2 s1001 = -1 ∧ w1 s1010 = 1 ∧ w2 s1010 = 0 ∧
        w1 s1100 = 0 ∧ w2 s1100 = 1 := by decide +kernel
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hw
    rcases weight_two_cases r hr with h | h | h | h | h | h <;> subst h <;>
      simp only [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12] <;> push_cast <;> linarith
  · obtain ⟨h1, h2⟩ := w1_off r hr
    rw [hz r hr, h1, h2]; simp

theorem spinZero_of_comb (a b : ℝ) : SpinZero (fun r => a * w1 r + b * w2 r) := by
  obtain ⟨⟨hz1, hp1⟩, ⟨hz2, hp2⟩⟩ := And.intro w1_spinZero w2_spinZero
  refine ⟨fun r hr => ?_, fun r => ?_⟩
  · have := hz1 r hr; have := hz2 r hr; simp_all
  · have h := hp1 r
    have h' := hp2 r
    calc ∑ i, (if r i then (fun r => a * ↑(w1 r) + b * ↑(w2 r)) (Function.update r i false) else 0)
        = a * ∑ i, (if r i then (w1 (Function.update r i false) : ℝ) else 0) +
          b * ∑ i, (if r i then (w2 (Function.update r i false) : ℝ) else 0) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs <;> simp
      _ = 0 := by
          simp only [] at h h'
          rw [h, h']; ring

theorem spinZero_iff (v : Quad → ℝ) :
    SpinZero v ↔ ∀ r, ∑ s, (P6 r s : ℝ) * v s = 6 * v r := by
  have h1 : ∀ r, (∑ s, (P6 r s : ℝ) * w1 s) = 6 * w1 r := fun r => by exact_mod_cast P6_w1 r
  have h2 : ∀ r, (∑ s, (P6 r s : ℝ) * w2 s) = 6 * w2 r := fun r => by exact_mod_cast P6_w2 r
  constructor
  · intro hv
    obtain ⟨a, b, h⟩ := spinZero_comb v hv
    intro r
    calc ∑ s, (P6 r s : ℝ) * v s
        = a * ∑ s, (P6 r s : ℝ) * w1 s + b * ∑ s, (P6 r s : ℝ) * w2 s := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun s _ => by rw [h s]; ring
      _ = 6 * v r := by rw [h1, h2, h r]; ring
  · intro hfix
    have hv : ∀ r, v r = (((2 * ∑ s, (w1 s : ℝ) * v s - ∑ s, (w2 s : ℝ) * v s) / 6) * w1 r +
        ((2 * ∑ s, (w2 s : ℝ) * v s - ∑ s, (w1 s : ℝ) * v s) / 6) * w2 r) := by
      intro r
      have := hfix r
      have e : ∑ s, (P6 r s : ℝ) * v s =
          (2 * ∑ s, (w1 s : ℝ) * v s - ∑ s, (w2 s : ℝ) * v s) * w1 r +
          (2 * ∑ s, (w2 s : ℝ) * v s - ∑ s, (w1 s : ℝ) * v s) * w2 r := by
        simp only [P6]; push_cast
        simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      linarith
    have : v = fun r => ((2 * ∑ s, (w1 s : ℝ) * v s - ∑ s, (w2 s : ℝ) * v s) / 6) * w1 r +
        ((2 * ∑ s, (w2 s : ℝ) * v s - ∑ s, (w1 s : ℝ) * v s) / 6) * w2 r := funext hv
    rw [this]
    exact spinZero_of_comb _ _

/-! ### The 35 four-site sets -/

/-- `U`-pattern (`α` coefficients) flattened as a `16 × 8` matrix: row `r` = string on the four-site
set `T`, column `a` = string on the three-site side. -/
def Uz (m : Fin 7 → Bool) (r : Quad) (a : Triple) : ℤ :=
  alphaCoefficient (encode (maskCut 3 4 m) a r)

/-- `V`-pattern (`β` coefficients). -/
def Vz (m : Fin 7 → Bool) (r : Quad) (a : Triple) : ℤ :=
  betaCoefficient (encode (maskCut 3 4 m) a r)

/-- `∑_r w(r) U(r, a)` for the pairing `i`. -/
def cz (i : Fin 3) (m : Fin 7 → Bool) (a : Triple) : ℤ := ∑ r, pairing i r * Uz m r a

/-- `∑_r w(r) V(r, a)`. -/
def cV (i : Fin 3) (m : Fin 7 → Bool) (a : Triple) : ℤ := ∑ r, pairing i r * Vz m r a

/-- `6 tr(P₀ U Uᵀ) = ∑_a uₐᵀ P6 uₐ`. -/
def qform (m : Fin 7 → Bool) : ℤ := ∑ a : Triple, ∑ r, ∑ s, Uz m r a * P6 r s * Uz m s a

/-- `P6 f = (2⟨w1,f⟩ - ⟨w2,f⟩) w1 + (2⟨w2,f⟩ - ⟨w1,f⟩) w2`. -/
theorem P6_mul (f : Quad → ℤ) (r : Quad) :
    ∑ s, P6 r s * f s = (2 * ∑ s, w1 s * f s - ∑ s, w2 s * f s) * w1 r +
      (2 * ∑ s, w2 s * f s - ∑ s, w1 s * f s) * w2 r := by
  simp only [P6, add_mul, sub_mul, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_assoc, ← Finset.mul_sum]
  ring

theorem qform_eq (m : Fin 7 → Bool) : qform m =
    ∑ a : Triple, (2 * cz 0 m a ^ 2 + 2 * cz 1 m a ^ 2 - 2 * cz 0 m a * cz 1 m a) := by
  unfold qform
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 : ∀ r : Quad, ∑ s, Uz m r a * P6 r s * Uz m s a = Uz m r a * ∑ s, P6 r s * Uz m s a := by
    intro r; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  have key : ∀ r, ∑ s, P6 r s * Uz m s a =
      (2 * cz 0 m a - cz 1 m a) * w1 r + (2 * cz 1 m a - cz 0 m a) * w2 r :=
    fun r => P6_mul (fun s => Uz m s a) r
  have e : ∀ r : Quad, Uz m r a * ((2 * cz 0 m a - cz 1 m a) * w1 r +
      (2 * cz 1 m a - cz 0 m a) * w2 r) =
      (2 * cz 0 m a - cz 1 m a) * (w1 r * Uz m r a) +
        (2 * cz 1 m a - cz 0 m a) * (w2 r * Uz m r a) := fun r => by ring
  simp only [h1, key, e, Finset.sum_add_distrib, ← Finset.mul_sum]
  have c0 : ∑ r, w1 r * Uz m r a = cz 0 m a := rfl
  have c1 : ∑ r, w2 r * Uz m r a = cz 1 m a := rfl
  rw [c0, c1]
  ring

/-! ### The finite checks (all 35 four-site sets) -/

/-- `6 tr(P₀ U Uᵀ)` in coordinates. -/
def qformC (m : Fin 7 → Bool) : ℤ :=
  ∑ a : Triple, (2 * cz 0 m a ^ 2 + 2 * cz 1 m a ^ 2 - 2 * cz 0 m a * cz 1 m a)

/-- The finite data of one cut. -/
def CutFacts (m : Fin 7 → Bool) : Prop :=
  -- `P₀ V = 0`, in coordinates
  (∀ a : Triple, cV 0 m a = 0 ∧ cV 1 m a = 0) ∧
  -- the `2 × 8` coordinate matrix of `P₀ U` has rank at most one
  (∀ a a' : Triple, cz 0 m a * cz 1 m a' = cz 0 m a' * cz 1 m a) ∧
  -- the three possible weights
  (qformC m = 0 ∨ qformC m = 16 ∨ qformC m = 48) ∧
  -- weight 48: the spin-zero column is `w_π (w_πᵀ U)/4`
  (qformC m = 48 → ∃ i : Fin 3, ∀ (a : Triple) (r : Quad),
    4 * ((2 * cz 0 m a - cz 1 m a) * w1 r + (2 * cz 1 m a - cz 0 m a) * w2 r) =
      6 * pairing i r * cz i m a) ∧
  -- weight 16: orthogonal to one product singlet
  (qformC m = 16 → ∃ i : Fin 3, ∀ a : Triple, cz i m a = 0)

instance (m : Fin 7 → Bool) : Decidable (CutFacts m) := by unfold CutFacts; infer_instance

/-- All four-site sets satisfy `CutFacts`, and the counts of the table hold. -/
theorem cut_facts_all :
    (∀ m ∈ tripleMasks, CutFacts m) ∧
    [(tripleMasks.filter fun m => m 0 = false ∧ qformC m = 0).card,
     (tripleMasks.filter fun m => m 0 = false ∧ qformC m = 16).card,
     (tripleMasks.filter fun m => m 0 = false ∧ qformC m = 48).card,
     (tripleMasks.filter fun m => m 0 = true ∧ qformC m = 0).card,
     (tripleMasks.filter fun m => m 0 = true ∧ qformC m = 16).card,
     (tripleMasks.filter fun m => m 0 = true ∧ qformC m = 48).card] = [5, 15, 0, 0, 10, 5] := by
  decide +kernel

/-! ### The reduced matrices on the four-site sets -/

/-- The reduced density matrix of `icosahedralState α β` on the four-site side of the cut `m`. -/
def entryT (m : Fin 7 → Bool) (alpha beta : ℝ) (r r' : Quad) : ℝ :=
  ∑ a : Triple, icosahedralState alpha beta (encode (maskCut 3 4 m) a r) *
    icosahedralState alpha beta (encode (maskCut 3 4 m) a r')

/-- `P₀ ρ_T P₀`. -/
noncomputable def P0rhoP0 (m : Fin 7 → Bool) (alpha beta : ℝ) (r r' : Quad) : ℝ :=
  (1 / 36) * ∑ s, ∑ t, (P6 r s : ℝ) * entryT m alpha beta s t * (P6 t r' : ℝ)

/-- `tr(P₀ ρ_T)`. -/
noncomputable def trP0rho (m : Fin 7 → Bool) (alpha beta : ℝ) : ℝ :=
  (1 / 6) * ∑ s, ∑ t, (P6 s t : ℝ) * entryT m alpha beta t s

/-- **IM-1, `P₀ V = 0`** on all 35 four-site sets (`P6 = 6 P₀`). -/
theorem P0_V (m : Fin 7 → Bool) (hm : m ∈ tripleMasks) (r : Quad) (a : Triple) :
    ∑ s, P6 r s * Vz m s a = 0 := by
  obtain ⟨h0, h1⟩ := (cut_facts_all.1 m hm).1 a
  rw [P6_mul]
  have h0' : ∑ s, w1 s * Vz m s a = 0 := h0
  have h1' : ∑ s, w2 s * Vz m s a = 0 := h1
  rw [h0', h1']; ring

/-- `P6 · ψ = α · P6 U`: the pattern `V` is annihilated (`P₀ V = 0`). -/
theorem P6_psi (m : Fin 7 → Bool) (hm : m ∈ tripleMasks) (alpha beta : ℝ) (r : Quad) (a : Triple) :
    ∑ s, (P6 r s : ℝ) * icosahedralState alpha beta (encode (maskCut 3 4 m) a s) =
      alpha * ((∑ s, P6 r s * Uz m s a : ℤ) : ℝ) := by
  have hV : ∑ s, P6 r s * Vz m s a = 0 := P0_V m hm r a
  have hV' : ∑ s, (P6 r s : ℝ) * (Vz m s a : ℝ) = 0 := by exact_mod_cast hV
  calc ∑ s, (P6 r s : ℝ) * icosahedralState alpha beta (encode (maskCut 3 4 m) a s)
      = alpha * ∑ s, (P6 r s : ℝ) * (Uz m s a : ℝ) + beta * ∑ s, (P6 r s : ℝ) * (Vz m s a : ℝ) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ => by
          simp only [icosahedralState, Uz, Vz]; ring
    _ = alpha * ((∑ s, P6 r s * Uz m s a : ℤ) : ℝ) := by rw [hV']; push_cast; ring

/-- Sandwiching a Gram matrix. -/
theorem sandwich (P : Quad → Quad → ℝ) (hP : ∀ r s, P r s = P s r) (ψ : Quad → Triple → ℝ)
    (r r' : Quad) :
    ∑ s, ∑ t, P r s * (∑ a, ψ s a * ψ t a) * P t r' =
      ∑ a, (∑ s, P r s * ψ s a) * (∑ t, P r' t * ψ t a) := by
  calc ∑ s, ∑ t, P r s * (∑ a, ψ s a * ψ t a) * P t r'
      = ∑ s, ∑ t, ∑ a, P r s * ψ s a * (P r' t * ψ t a) := by
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
        rw [hP t r', Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ s, ∑ a, ∑ t, P r s * ψ s a * (P r' t * ψ t a) :=
        Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = ∑ a, ∑ s, ∑ t, P r s * ψ s a * (P r' t * ψ t a) := Finset.sum_comm
    _ = ∑ a, (∑ s, P r s * ψ s a) * (∑ t, P r' t * ψ t a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul_sum]

/-- `⟨f, P6 g⟩` in coordinates. -/
theorem sum_P6 (f g : Quad → ℤ) :
    ∑ s, f s * ∑ t, P6 s t * g t =
      2 * (∑ s, w1 s * f s) * (∑ s, w1 s * g s) + 2 * (∑ s, w2 s * f s) * (∑ s, w2 s * g s) -
        (∑ s, w1 s * f s) * (∑ s, w2 s * g s) - (∑ s, w2 s * f s) * (∑ s, w1 s * g s) := by
  have h : ∀ s, f s * ∑ t, P6 s t * g t =
      (2 * ∑ t, w1 t * g t - ∑ t, w2 t * g t) * (w1 s * f s) +
        (2 * ∑ t, w2 t * g t - ∑ t, w1 t * g t) * (w2 s * f s) := by
    intro s; rw [P6_mul]; ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The matrix `X = P6 U`, as reals. -/
def Xm (m : Fin 7 → Bool) (r : Quad) (a : Triple) : ℝ := ((∑ s, P6 r s * Uz m s a : ℤ) : ℝ)

theorem P0rhoP0_eq (m : Fin 7 → Bool) (hm : m ∈ tripleMasks) (alpha beta : ℝ) (r r' : Quad) :
    P0rhoP0 m alpha beta r r' = alpha ^ 2 / 36 * ∑ a : Triple, Xm m r a * Xm m r' a := by
  unfold P0rhoP0 entryT
  have hs := sandwich (fun r s => (P6 r s : ℝ)) (fun r s => by exact_mod_cast P6_symm r s)
    (fun s a => icosahedralState alpha beta (encode (maskCut 3 4 m) a s)) r r'
  rw [hs, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [P6_psi m hm, P6_psi m hm]
  simp only [Xm]; ring

theorem exists_line (c0 c1 : Triple → ℝ) (h : ∀ a a', c0 a * c1 a' = c0 a' * c1 a) :
    ∃ l0 l1 : ℝ, ∃ g : Triple → ℝ, ∀ a, c0 a = l0 * g a ∧ c1 a = l1 * g a := by
  by_cases hz : ∀ a, c0 a = 0 ∧ c1 a = 0
  · exact ⟨0, 0, fun _ => 0, fun a => ⟨by simp [(hz a).1], by simp [(hz a).2]⟩⟩
  · push Not at hz
    obtain ⟨a₀, ha₀⟩ := hz
    by_cases h0 : c0 a₀ = 0
    · have h1 : c1 a₀ ≠ 0 := fun h1 => by
        by_cases hh : c0 a₀ = 0
        · exact absurd h1 (ha₀ hh)
        · exact hh h0
      refine ⟨c0 a₀ / c1 a₀, 1, c1, fun a => ⟨?_, by simp⟩⟩
      have := h a₀ a
      field_simp
      linarith
    · refine ⟨1, c1 a₀ / c0 a₀, c0, fun a => ⟨by simp, ?_⟩⟩
      have := h a a₀
      field_simp
      linarith

/-- **`P₀ ρ_T P₀` has rank at most one**: it equals `κ v vᵀ`. -/
theorem P0rhoP0_rank_one (m : Fin 7 → Bool) (hm : m ∈ tripleMasks) (alpha beta : ℝ) :
    ∃ (v : Quad → ℝ) (κ : ℝ), ∀ r r', P0rhoP0 m alpha beta r r' = κ * v r * v r' := by
  have hmin := (cut_facts_all.1 m hm).2.1
  have h' : ∀ a a', (cz 0 m a : ℝ) * (cz 1 m a' : ℝ) = (cz 0 m a' : ℝ) * (cz 1 m a : ℝ) :=
    fun a a' => by exact_mod_cast hmin a a'
  obtain ⟨l0, l1, g, hg⟩ := exists_line _ _ h'
  have hX : ∀ r a, Xm m r a = g a * ((2 * l0 - l1) * w1 r + (2 * l1 - l0) * w2 r) := by
    intro r a
    unfold Xm
    rw [P6_mul]
    have e0 : (∑ s, w1 s * Uz m s a : ℤ) = cz 0 m a := rfl
    have e1 : (∑ s, w2 s * Uz m s a : ℤ) = cz 1 m a := rfl
    rw [e0, e1]
    push_cast
    rw [(hg a).1, (hg a).2]; ring
  refine ⟨fun r => (2 * l0 - l1) * w1 r + (2 * l1 - l0) * w2 r,
    alpha ^ 2 / 36 * ∑ a, g a ^ 2, fun r r' => ?_⟩
  rw [P0rhoP0_eq m hm]
  simp only [hX]
  have e : ∑ a, g a * ((2 * l0 - l1) * (w1 r : ℝ) + (2 * l1 - l0) * (w2 r : ℝ)) *
      (g a * ((2 * l0 - l1) * (w1 r' : ℝ) + (2 * l1 - l0) * (w2 r' : ℝ))) =
      (∑ a, g a ^ 2) * (((2 * l0 - l1) * (w1 r : ℝ) + (2 * l1 - l0) * (w2 r : ℝ)) *
        ((2 * l0 - l1) * (w1 r' : ℝ) + (2 * l1 - l0) * (w2 r' : ℝ))) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => by ring
  rw [e]; ring

theorem entryT_symm (m : Fin 7 → Bool) (alpha beta : ℝ) (s t : Quad) :
    entryT m alpha beta s t = entryT m alpha beta t s := by
  unfold entryT
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- `tr(P₀ ρ_T) = α² · 6 tr(P₀ U Uᵀ)/6 = α² qformC / 6`. -/
theorem trP0rho_eq (m : Fin 7 → Bool) (hm : m ∈ tripleMasks) (alpha beta : ℝ) :
    trP0rho m alpha beta = alpha ^ 2 * (qformC m : ℝ) / 6 := by
  unfold trP0rho entryT
  set ψ : Quad → Triple → ℝ := fun s a => icosahedralState alpha beta (encode (maskCut 3 4 m) a s)
    with hψ
  have h1 : ∑ s, ∑ t, (P6 s t : ℝ) * ∑ a, ψ t a * ψ s a =
      ∑ a, ∑ s, ψ s a * ∑ t, (P6 s t : ℝ) * ψ t a := by
    calc ∑ s, ∑ t, (P6 s t : ℝ) * ∑ a, ψ t a * ψ s a
        = ∑ s, ∑ t, ∑ a, ψ s a * ((P6 s t : ℝ) * ψ t a) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
      _ = ∑ s, ∑ a, ∑ t, ψ s a * ((P6 s t : ℝ) * ψ t a) :=
          Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = ∑ a, ∑ s, ∑ t, ψ s a * ((P6 s t : ℝ) * ψ t a) := Finset.sum_comm
      _ = ∑ a, ∑ s, ψ s a * ∑ t, (P6 s t : ℝ) * ψ t a := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum]
  have h2 : ∀ a, ∑ s, ψ s a * ∑ t, (P6 s t : ℝ) * ψ t a =
      alpha ^ 2 * ((2 * cz 0 m a ^ 2 + 2 * cz 1 m a ^ 2 - 2 * cz 0 m a * cz 1 m a : ℤ) : ℝ) := by
    intro a
    have hU := sum_P6 (fun s => Uz m s a) (fun s => Uz m s a)
    have hVU := sum_P6 (fun s => Vz m s a) (fun s => Uz m s a)
    obtain ⟨c0, c1⟩ := (cut_facts_all.1 m hm).1 a
    have c0' : ∑ s, w1 s * Vz m s a = 0 := c0
    have c1' : ∑ s, w2 s * Vz m s a = 0 := c1
    rw [c0', c1'] at hVU
    have e0 : (∑ s, w1 s * Uz m s a : ℤ) = cz 0 m a := rfl
    have e1 : (∑ s, w2 s * Uz m s a : ℤ) = cz 1 m a := rfl
    rw [e0, e1] at hU
    have hUX : ∑ s, (Uz m s a : ℝ) * Xm m s a =
        2 * (cz 0 m a : ℝ) ^ 2 + 2 * (cz 1 m a : ℝ) ^ 2 - 2 * (cz 0 m a : ℝ) * (cz 1 m a : ℝ) := by
      have : ((∑ s, Uz m s a * ∑ t, P6 s t * Uz m t a : ℤ) : ℝ) =
          ((2 * cz 0 m a * cz 0 m a + 2 * cz 1 m a * cz 1 m a - cz 0 m a * cz 1 m a -
            cz 1 m a * cz 0 m a : ℤ) : ℝ) := by rw [hU]
      push_cast at this
      simp only [Xm]; push_cast
      linarith [this]
    have hVX : ∑ s, (Vz m s a : ℝ) * Xm m s a = 0 := by
      have : ((∑ s, Vz m s a * ∑ t, P6 s t * Uz m t a : ℤ) : ℝ) = 0 := by rw [hVU]; simp
      push_cast at this
      simp only [Xm]; push_cast
      linarith [this]
    calc ∑ s, ψ s a * ∑ t, (P6 s t : ℝ) * ψ t a
        = ∑ s, ψ s a * (alpha * Xm m s a) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [hψ]; simp only []
          rw [P6_psi m hm]; rfl
      _ = alpha ^ 2 * ∑ s, (Uz m s a : ℝ) * Xm m s a +
            alpha * beta * ∑ s, (Vz m s a : ℝ) * Xm m s a := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun s _ => ?_
          simp only [hψ, icosahedralState, Uz, Vz]; ring
      _ = alpha ^ 2 * ((2 * cz 0 m a ^ 2 + 2 * cz 1 m a ^ 2 - 2 * cz 0 m a * cz 1 m a : ℤ) : ℝ) := by
          rw [hUX, hVX]; push_cast; ring
  rw [h1]
  simp only [h2]
  unfold qformC
  push_cast
  rw [← Finset.mul_sum]
  ring

/-- The table of `qformC` values and counts. `m 0 = false` means that the special site `s` lies in
the four-site set `T`. -/
theorem table_counts :
    (tripleMasks.filter fun m => m 0 = false ∧ qformC m = 0).card = 5 ∧
    (tripleMasks.filter fun m => m 0 = false ∧ qformC m = 16).card = 15 ∧
    (tripleMasks.filter fun m => m 0 = false ∧ qformC m = 48).card = 0 ∧
    (tripleMasks.filter fun m => m 0 = true ∧ qformC m = 0).card = 0 ∧
    (tripleMasks.filter fun m => m 0 = true ∧ qformC m = 16).card = 10 ∧
    (tripleMasks.filter fun m => m 0 = true ∧ qformC m = 48).card = 5 := by
  have := cut_facts_all.2
  simp only [List.cons.injEq, and_true] at this
  exact this

theorem qformC_values (m : Fin 7 → Bool) (hm : m ∈ tripleMasks) :
    qformC m = 0 ∨ qformC m = 16 ∨ qformC m = 48 := (cut_facts_all.1 m hm).2.2.1

/-- **IM-1, weights.** `tr(P₀ ρ_T) ∈ {0, 8u/3, 8u}` with `u = α²`. -/
theorem trP0rho_values (m : Fin 7 → Bool) (hm : m ∈ tripleMasks) (alpha beta : ℝ) :
    trP0rho m alpha beta = 0 ∨ trP0rho m alpha beta = 8 * alpha ^ 2 / 3 ∨
      trP0rho m alpha beta = 8 * alpha ^ 2 := by
  rw [trP0rho_eq m hm]
  rcases qformC_values m hm with h | h | h <;> rw [h] <;> push_cast
  · left; ring
  · right; left; ring
  · right; right; ring

/-- **IM-1, weight `8u`**: on the cuts of weight `8u`, `P₀ U = w_π (w_πᵀ U)/4` for one of the three
product singlets `w_π`; i.e. the nonzero spin-zero column vector is `w_π`, a product of two pair
singlets. -/
theorem weight48_product_singlet (m : Fin 7 → Bool) (hm : m ∈ tripleMasks) (h : qformC m = 48) :
    ∃ i : Fin 3, ∀ (a : Triple) (r : Quad),
      4 * (∑ s, P6 r s * Uz m s a) = 6 * pairing i r * ∑ s, pairing i s * Uz m s a := by
  obtain ⟨i, hi⟩ := (cut_facts_all.1 m hm).2.2.2.1 h
  refine ⟨i, fun a r => ?_⟩
  rw [P6_mul]
  exact hi a r

/-- **IM-1, weight `8u/3`**: the nonzero spin-zero vector is orthogonal to a product singlet `w_π`
(`w_πᵀ U = 0`). -/
theorem weight16_orthogonal (m : Fin 7 → Bool) (hm : m ∈ tripleMasks) (h : qformC m = 16) :
    ∃ i : Fin 3, ∀ a : Triple, ∑ r, pairing i r * Uz m r a = 0 :=
  (cut_facts_all.1 m hm).2.2.2.2 h

/-! ### The chiral states `M₄`, `M̄₄` -/

open scoped ComplexConjugate

/-- The coefficient table of `M₄ √6` on strings `r₀r₁r₂r₃`. -/
noncomputable def m4tab : Bool → Bool → Bool → Bool → ℂ
  | false, false, true, true => 1
  | true, true, false, false => 1
  | false, true, false, true => omega
  | true, false, true, false => omega
  | false, true, true, false => conj omega
  | true, false, false, true => conj omega
  | _, _, _, _ => 0

/-- The Higuchi–Sudbery state `M₄ = (|0011⟩ + |1100⟩ + ω(|0101⟩ + |1010⟩) + ω²(|0110⟩ + |1001⟩))/√6`. -/
noncomputable def m4 (r : Quad) : ℂ := ((1 / Real.sqrt 6 : ℝ) : ℂ) * m4tab (r 0) (r 1) (r 2) (r 3)

theorem conj_omega_eq : conj omega = -1 - omega := by
  rw [← omega_sq]; linear_combination omega_sq_add

theorem m4_eq (r : Quad) : m4 r = ((1 / Real.sqrt 6 : ℝ) : ℂ) * (omega * (w1 r : ℂ) + (w2 r : ℂ)) := by
  unfold m4
  congr 1
  have key : ∀ a b c d : Bool, m4tab a b c d =
      omega * ((w1 ![a, b, c, d] : ℤ) : ℂ) + ((w2 ![a, b, c, d] : ℤ) : ℂ) := by
    intro a b c d
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [m4tab, w1, w2, pairing, pairVec, sing, conj_omega_eq] <;> ring
  have hr : r = ![r 0, r 1, r 2, r 3] := by
    ext i; fin_cases i <;> rfl
  rw [key]
  rw [← hr]

theorem sqrt6_sq : ((1 / Real.sqrt 6 : ℝ) : ℂ) * ((1 / Real.sqrt 6 : ℝ) : ℂ) = 1 / 6 := by
  have h6 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
  have : (1 / Real.sqrt 6) * (1 / Real.sqrt 6) = (1 / 6 : ℝ) := by
    field_simp; linarith
  rw [← Complex.ofReal_mul, this]; push_cast; norm_num

/-- `P6/6 = |M₄⟩⟨M₄| + |M̄₄⟩⟨M̄₄|`. -/
theorem P6_eq_M4 (r s : Quad) :
    (P6 r s : ℂ) = 6 * (m4 r * conj (m4 s) + conj (m4 r) * m4 s) := by
  rw [m4_eq, m4_eq, map_mul, map_mul, map_add, map_mul, map_add, map_mul, conj_omega_eq]
  simp only [Complex.conj_ofReal, map_intCast]
  have hc := sqrt6_sq
  generalize ((1 / Real.sqrt 6 : ℝ) : ℂ) = c at hc ⊢
  unfold P6
  push_cast
  linear_combination (-6 * (2 * (w1 r : ℂ) * w1 s + 2 * (w2 r : ℂ) * w2 s - w1 r * w2 s -
      w2 r * w1 s)) * hc + (12 * (c * c) * (w1 r * w1 s)) * omega_sq_add

/-- `M₄` is a unit vector. -/
theorem m4_norm : ∑ r : Quad, conj (m4 r) * m4 r = 1 := by
  have h : ∀ r : Quad, (P6 r r : ℂ) = 12 * (conj (m4 r) * m4 r) := fun r => by
    rw [P6_eq_M4]; ring
  have h12 : ∑ r : Quad, (P6 r r : ℂ) = 12 := by exact_mod_cast P6_trace
  simp only [h, ← Finset.mul_sum] at h12
  linear_combination h12 / 12

/-- `M₄ ⟂ M̄₄` (`⟨M₄, M̄₄⟩ = ∑ conj(M₄) conj(M₄) = 0`). -/
theorem m4_orth : ∑ r : Quad, conj (m4 r) * conj (m4 r) = 0 := by
  obtain ⟨g11, g12, g22⟩ := gram_w
  have g11' : ∑ r : Quad, (w1 r : ℂ) * w1 r = 4 := by exact_mod_cast g11
  have g12' : ∑ r : Quad, (w1 r : ℂ) * w2 r = 2 := by exact_mod_cast g12
  have g22' : ∑ r : Quad, (w2 r : ℂ) * w2 r = 4 := by exact_mod_cast g22
  have hc := sqrt6_sq
  have e : ∀ r : Quad, conj (m4 r) * conj (m4 r) =
      (((1 / Real.sqrt 6 : ℝ) : ℂ) * ((1 / Real.sqrt 6 : ℝ) : ℂ)) *
        ((-1 - omega) ^ 2 * ((w1 r : ℂ) * w1 r) + 2 * (-1 - omega) * ((w1 r : ℂ) * w2 r) +
          ((w2 r : ℂ) * w2 r)) := by
    intro r
    rw [m4_eq, map_mul, map_add, map_mul, conj_omega_eq]
    simp only [Complex.conj_ofReal, map_intCast]
    ring
  simp only [e, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [g11', g12', g22']
  linear_combination (4 * (((1 / Real.sqrt 6 : ℝ) : ℂ) * ((1 / Real.sqrt 6 : ℝ) : ℂ))) * omega_sq_add

/-- The overlap `⟨v, ρ v⟩` of a vector with a real matrix. -/
noncomputable def fid (v : Quad → ℂ) (ρ : Quad → Quad → ℝ) : ℂ :=
  ∑ s, ∑ t, conj (v s) * (ρ s t : ℂ) * v t

theorem sum_P6_rho_eq_fid (ρ : Quad → Quad → ℝ) (hρ : ∀ s t, ρ s t = ρ t s) :
    (((∑ s, ∑ t, (P6 s t : ℝ) * ρ t s : ℝ)) : ℂ) = 12 * fid m4 ρ := by
  push_cast
  have hA : ∑ s, ∑ t, m4 s * conj (m4 t) * (ρ t s : ℂ) = fid m4 ρ := by
    unfold fid
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
  have hB : ∑ s, ∑ t, conj (m4 s) * m4 t * (ρ t s : ℂ) = fid m4 ρ := by
    unfold fid
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by rw [hρ t s]; ring
  have : ∀ s t : Quad, ((P6 s t : ℤ) : ℂ) * (ρ t s : ℂ) =
      6 * (m4 s * conj (m4 t) * (ρ t s : ℂ)) + 6 * (conj (m4 s) * m4 t * (ρ t s : ℂ)) := by
    intro s t
    rw [P6_eq_M4 s t]; ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hA, hB]
  ring

/-- **IM-1, equal chiral fidelities.** `⟨M₄, ρ_T M₄⟩ = ⟨M̄₄, ρ_T M̄₄⟩ = tr(P₀ ρ_T)/2`. -/
theorem fidelity_M4 (m : Fin 7 → Bool) (alpha beta : ℝ) :
    fid m4 (entryT m alpha beta) = ((trP0rho m alpha beta / 2 : ℝ) : ℂ) ∧
    fid (fun r => conj (m4 r)) (entryT m alpha beta) = ((trP0rho m alpha beta / 2 : ℝ) : ℂ) := by
  have h := sum_P6_rho_eq_fid (entryT m alpha beta) (entryT_symm m alpha beta)
  have h1 : fid m4 (entryT m alpha beta) = ((trP0rho m alpha beta / 2 : ℝ) : ℂ) := by
    have e : trP0rho m alpha beta = (1 / 6) * ∑ s, ∑ t, (P6 s t : ℝ) * entryT m alpha beta t s := rfl
    rw [e]
    push_cast at h ⊢
    linear_combination (-1 / 12 : ℂ) * h
  refine ⟨h1, ?_⟩
  have hc : fid (fun r => conj (m4 r)) (entryT m alpha beta) = conj (fid m4 (entryT m alpha beta)) := by
    unfold fid
    simp only [map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  rw [hc, h1, Complex.conj_ofReal]

/-- **IM-1, fidelity values.** For every `ψ_x` and every four-site set, the common chiral fidelity
lies in `{0, 4u/3, 4u}` with `u = α²`. -/
theorem fidelity_values (m : Fin 7 → Bool) (hm : m ∈ tripleMasks) (alpha beta : ℝ) :
    fid m4 (entryT m alpha beta) = 0 ∨ fid m4 (entryT m alpha beta) = ((4 * alpha ^ 2 / 3 : ℝ) : ℂ) ∨
      fid m4 (entryT m alpha beta) = ((4 * alpha ^ 2 : ℝ) : ℂ) := by
  rw [(fidelity_M4 m alpha beta).1]
  rcases trP0rho_values m hm alpha beta with h | h | h <;> rw [h]
  · left; simp
  · right; left; push_cast; ring
  · right; right; push_cast; ring

/-- At `Ψico` (`α² = 15/524`) the possible fidelities are `0, 5/131, 15/131`. -/
theorem fidelity_values_ico (m : Fin 7 → Bool) (hm : m ∈ tripleMasks) (alpha beta : ℝ)
    (hα : alpha ^ 2 = u (37 / 524)) :
    fid m4 (entryT m alpha beta) = 0 ∨ fid m4 (entryT m alpha beta) = ((5 / 131 : ℝ) : ℂ) ∨
      fid m4 (entryT m alpha beta) = ((15 / 131 : ℝ) : ℂ) := by
  have hu : alpha ^ 2 = 15 / 524 := by rw [hα]; unfold u; norm_num
  rcases fidelity_values m hm alpha beta with h | h | h <;> rw [h]
  · left; rfl
  · right; left; rw [hu]; congr 1; norm_num
  · right; right; rw [hu]; congr 1; norm_num

end FormalResearch.FourQubitEntropy.SevenQubitIco
