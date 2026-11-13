module

public import FormalResearch.NQubit.Pauli.Hermitian
public import FormalResearch.NQubit.Reduced.MeanPurity
public import FormalResearch.NQubit.Graph.State

/-!
# Cut purities of graph states: `tr ρ_S² = 2^{-rk_2 Γ[S,S^c]}`

The statement is proved from the swap form of the purity (`swapPurity`), not by stabiliser counting.
For the unnormalised graph state `graphState Γ` and `u = x + y` (mod 2), `q(x) + q(y) + q(swapOn S x y) +
q(swapOn S y x)` is the bilinear form `Σ_{i ∈ S, j ∉ S} Γ_ij u_i u_j` (`qf_four`), so
`swapPurity (graphState Γ) S = 2^n Σ_u (-1)^{u_S^T B u_{S^c}} = 2^n 2^{|S|} #ker B = 2^{2n - rk B}`, with
`B = Γ[S,S^c]`.

* `cutMat Γ S : Matrix {i // i ∈ S} {j // j ∉ S} (ZMod 2)`: the biadjacency matrix `Γ[S,S^c]`;
* `graphCutRank Γ S = (cutMat Γ S).rank`;
* `purity_gsn`: for the normalised graph state `graphStateNorm Γ`,
  `cutPurity (graphStateNorm Γ) S = (1/2)^{graphCutRank Γ S}`.
-/

@[expose] public section


open scoped ComplexConjugate BigOperators
open FormalResearch.NQubit.Pauli
open FormalResearch.NQubit.Reduced
open FormalResearch.NQubit.TimeReversal

namespace FormalResearch.NQubit.Graph

variable {n : ℕ}

theorem swapPurity_graphState (Γ : Fin n → Fin n → Bool) (S : Finset (Fin n)) :
    swapPurity (graphState Γ) S = ∑ x : Cfg n, ∑ y : Cfg n,
      chi (qf Γ x + qf Γ y + qf Γ (swapOn S x y) + qf Γ (swapOn S y x)) := by
  unfold swapPurity
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  unfold graphState
  rw [conj_chi, conj_chi, chi_add, chi_add, chi_add]
  ring


/-- The cross form `Σ_{i ∈ S, j ∉ S} Γ_ij u_i u_j` over `𝔽₂`. -/
def cutCrossForm (Γ : Fin n → Fin n → Bool) (S : Finset (Fin n)) (u : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, if i ∈ S ∧ j ∉ S ∧ Γ i j = true then u i * u j else 0

theorem zx_sw (S : Finset (Fin n)) (x y : Cfg n) (i : Fin n) :
    zx (swapOn S x y i) = if i ∈ S then zx (y i) else zx (x i) := by
  unfold swapOn; split_ifs <;> rfl

theorem two_eq_zero_zmod : (2 : ZMod 2) = 0 := rfl

/-- Pairwise identity behind `qf_four`. -/
theorem pair_four (a b c d : ZMod 2) (hi hj : Prop) [Decidable hi] [Decidable hj] :
    (a * b + c * d) + ((if hi then c else a) * (if hj then d else b)
      + (if hi then a else c) * (if hj then b else d))
      = if hi ∧ ¬ hj ∨ ¬ hi ∧ hj then (a + c) * (b + d) else 0 := by
  by_cases h1 : hi <;> by_cases h2 : hj <;> simp only [h1, h2, and_true,
    not_true, not_false_eq_true, or_true, and_false, or_false, ite_true,
    ite_false]
  · linear_combination (a * b + c * d) * two_eq_zero_zmod
  · ring
  · ring
  · linear_combination (a * b + c * d) * two_eq_zero_zmod


/-- `cutCrossForm` as a sum over ordered pairs `i < j`. -/
theorem cutCrossForm_eq (Γ : Fin n → Fin n → Bool) (hsym : ∀ i j, Γ i j = Γ j i) (S : Finset (Fin n))
    (u : Fin n → ZMod 2) :
    cutCrossForm Γ S u = ∑ i, ∑ j, if i < j ∧ Γ i j = true then
      (if (i ∈ S ∧ j ∉ S ∨ i ∉ S ∧ j ∈ S) then u i * u j else 0) else 0 := by
  unfold cutCrossForm
  have h1 : ∀ i j, (if i ∈ S ∧ j ∉ S ∧ Γ i j = true then u i * u j else 0)
      = (if i < j ∧ Γ i j = true then (if i ∈ S ∧ j ∉ S then u i * u j else 0) else 0)
        + (if j < i ∧ Γ i j = true then (if i ∈ S ∧ j ∉ S then u i * u j else 0) else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · have : ¬ j < i := not_lt.mpr h.le
      by_cases h2 : i ∈ S ∧ j ∉ S <;> by_cases h3 : Γ i j = true <;> simp [h, this, h2, h3]
    · subst h; by_cases h2 : i ∈ S <;> simp [h2]
    · have : ¬ i < j := not_lt.mpr h.le
      by_cases h2 : i ∈ S ∧ j ∉ S <;> by_cases h3 : Γ i j = true <;>
        simp [h, this, h2, h3]
  simp_rw [h1, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if j < i ∧ Γ i j = true then
    (if i ∈ S ∧ j ∉ S then u i * u j else 0) else 0), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i < j ∧ Γ i j = true
  · simp only [h, and_self, ite_true]
    have hs' : Γ j i = true := by rw [hsym j i]; exact h.2
    by_cases h2 : i ∈ S ∧ j ∉ S
    · have : ¬ (i ∉ S ∧ j ∈ S) := fun h' => h'.1 h2.1
      simp [h2, hs']
    · by_cases h3 : i ∉ S ∧ j ∈ S
      · simp [h3, hs', mul_comm]
      · have h4 : ¬ (j ∈ S ∧ i ∉ S) := fun h' => h3 ⟨h'.2, h'.1⟩
        simp [h2, h3, h4, hs']
  · have h' : ¬ (i < j ∧ Γ j i = true) := by rw [hsym j i]; exact h
    simp [h, h']

theorem qf_four (Γ : Fin n → Fin n → Bool) (hsym : ∀ i j, Γ i j = Γ j i) (S : Finset (Fin n))
    (x y : Cfg n) :
    qf Γ x + qf Γ y + qf Γ (swapOn S x y) + qf Γ (swapOn S y x)
      = cutCrossForm Γ S (fun i => zx (x i) + zx (y i)) := by
  rw [cutCrossForm_eq Γ hsym]
  unfold qf
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i < j ∧ Γ i j = true
  · simp only [h, and_self, ite_true]
    rw [zx_sw, zx_sw, zx_sw, zx_sw]
    have := pair_four (zx (x i)) (zx (x j)) (zx (y i)) (zx (y j)) (i ∈ S) (j ∈ S)
    rw [← add_assoc] at this
    rw [this]
  · simp [h]


/-! ### Evaluating the character sum -/

/-- `Σ_x Σ_y F(x + y) = 2^n Σ_u F(u)`. -/
theorem sum_xy (F : (Fin n → ZMod 2) → ℂ) :
    ∑ x : Cfg n, ∑ y : Cfg n, F (fun i => zx (x i) + zx (y i))
      = (2 : ℂ) ^ n * ∑ u : Fin n → ZMod 2, F u := by
  have eZ : Function.Bijective (zx : Fin 2 → ZMod 2) := by decide
  let e : Cfg n ≃ (Fin n → ZMod 2) := Equiv.piCongrRight fun _ => Equiv.ofBijective zx eZ
  have h1 : ∀ x : Cfg n, ∑ y : Cfg n, F (fun i => zx (x i) + zx (y i))
      = ∑ u : Fin n → ZMod 2, F u := by
    intro x
    calc ∑ y : Cfg n, F (fun i => zx (x i) + zx (y i))
        = ∑ y : Cfg n, (fun v : Fin n → ZMod 2 => F (fun i => zx (x i) + v i)) (e y) := rfl
      _ = ∑ v : Fin n → ZMod 2, F (fun i => zx (x i) + v i) :=
          Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = ∑ u : Fin n → ZMod 2, F u :=
          Fintype.sum_equiv (Equiv.addLeft (e x)) _ _ (fun _ => rfl)
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [Fintype.card_pi]


/-- The biadjacency matrix `Γ[S,S^c]` over `𝔽₂`. -/
def cutMat (Γ : Fin n → Fin n → Bool) (S : Finset (Fin n)) :
    Matrix {i // i ∈ S} {j // j ∉ S} (ZMod 2) :=
  fun i j => if Γ i j = true then 1 else 0

/-- `rk_2 Γ[S,S^c]`. -/
noncomputable def graphCutRank (Γ : Fin n → Fin n → Bool) (S : Finset (Fin n)) : ℕ := (cutMat Γ S).rank

theorem sum_subtype_ite {α R : Type*} [Fintype α] [AddCommMonoid R] (p : α → Prop) [DecidablePred p]
    [Fintype {i // p i}] (f : α → R) : ∑ i, (if p i then f i else 0) = ∑ i : {i // p i}, f i := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) f

theorem cutCrossForm_sub (Γ : Fin n → Fin n → Bool) (S : Finset (Fin n)) (u : Fin n → ZMod 2) :
    cutCrossForm Γ S u = ∑ i : {i // i ∈ S}, ∑ j : {j // j ∉ S}, if Γ i j = true then u i * u j else 0 := by
  unfold cutCrossForm
  have h1 : ∀ i, (∑ j, if i ∈ S ∧ j ∉ S ∧ Γ i j = true then u i * u j else 0)
      = if i ∈ S then ∑ j : {j // j ∉ S}, (if Γ i j = true then u i * u j else 0) else 0 := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, true_and, ite_true]
      rw [← sum_subtype_ite (fun j => j ∉ S) (fun j => if Γ i j = true then u i * u j else 0)]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ∉ S <;> by_cases hg : Γ i j = true <;> simp [hj, hg]
    · simp [hi]
  simp_rw [h1]
  exact sum_subtype_ite (fun i => i ∈ S) (fun i => ∑ j : {j // j ∉ S},
    if Γ i j = true then u i * u j else 0)

theorem sum_chi_lin' {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ZMod 2) :
    ∑ a : ι → ZMod 2, chi (∑ i, a i * c i) = ∏ i, (1 + chi (c i)) := by
  have h : ∀ a : ι → ZMod 2, chi (∑ i, a i * c i) = ∏ i, chi (a i * c i) := fun a => chi_sum _ _
  simp_rw [h]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun i : ι => (Finset.univ : Finset (ZMod 2)))
    (fun i z => chi (z * c i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl]
  simp [chi_zero]

theorem prod_one_add_chi {ι : Type*} [Fintype ι] (c : ι → ZMod 2) :
    ∏ i, (1 + chi (c i)) = if c = 0 then (2 : ℂ) ^ Fintype.card ι else 0 := by
  by_cases hc : c = 0
  · subst hc
    simp [chi_zero]
    norm_num
  · obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h; push Not at h; exact hc (funext h)
    simp only [hc, ite_false]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have : c i = 1 := by
      revert hi; generalize c i = z; revert z; decide
    rw [this, chi_one]; norm_num


theorem sum_chi_cross (Γ : Fin n → Fin n → Bool) (S : Finset (Fin n)) :
    ∑ u : Fin n → ZMod 2, chi (cutCrossForm Γ S u)
      = (2 : ℂ) ^ S.card * ((Finset.univ.filter fun b : {j // j ∉ S} → ZMod 2 =>
          (cutMat Γ S).mulVec b = 0).card : ℂ) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ : Fin n => ZMod 2)
  have h1 : ∑ u : Fin n → ZMod 2, chi (cutCrossForm Γ S u)
      = ∑ p : ({i // i ∈ S} → ZMod 2) × ({j // j ∉ S} → ZMod 2), chi (cutCrossForm Γ S (e.symm p)) :=
    (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm
  rw [h1, Fintype.sum_prod_type]
  have h2 : ∀ (a : {i // i ∈ S} → ZMod 2) (b : {j // j ∉ S} → ZMod 2),
      cutCrossForm Γ S (e.symm (a, b)) = ∑ i, a i * (cutMat Γ S).mulVec b i := by
    intro a b
    rw [cutCrossForm_sub]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : e.symm (a, b) i.1 = a i := by
      simp [e, Equiv.piEquivPiSubtypeProd, i.2]
    have hj : ∀ j : {j // j ∉ S}, e.symm (a, b) j.1 = b j := by
      intro j; simp [e, Equiv.piEquivPiSubtypeProd, j.2]
    simp only [hi, hj, Matrix.mulVec, dotProduct, cutMat, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hg : Γ i j = true <;> simp [hg]
  simp_rw [h2]
  rw [Finset.sum_comm]
  have h3 : ∀ b : {j // j ∉ S} → ZMod 2,
      ∑ a : {i // i ∈ S} → ZMod 2, chi (∑ i, a i * (cutMat Γ S).mulVec b i)
        = if (cutMat Γ S).mulVec b = 0 then (2 : ℂ) ^ S.card else 0 := by
    intro b
    rw [sum_chi_lin', prod_one_add_chi]
    simp
  simp_rw [h3]
  simp [Finset.sum_ite, mul_comm]


theorem card_ker_mul (Γ : Fin n → Fin n → Bool) (S : Finset (Fin n)) :
    (Finset.univ.filter fun b : {j // j ∉ S} → ZMod 2 => (cutMat Γ S).mulVec b = 0).card
        * 2 ^ graphCutRank Γ S = 2 ^ Sᶜ.card := by
  classical
  set K : ({j // j ∉ S} → ZMod 2) →ₗ[ZMod 2] ({i // i ∈ S} → ZMod 2) := (cutMat Γ S).mulVecLin
  have : Fintype (LinearMap.ker K) := Fintype.ofFinite _
  have h1 : (Finset.univ.filter fun b : {j // j ∉ S} → ZMod 2 => (cutMat Γ S).mulVec b = 0).card
      = Fintype.card (LinearMap.ker K) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun b => by simp [K, LinearMap.mem_ker])
  have h2 : Fintype.card (LinearMap.ker K) = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker K) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2)]
    simp
  have h3 := LinearMap.finrank_range_add_finrank_ker K
  have h4 : Module.finrank (ZMod 2) ({j // j ∉ S} → ZMod 2) = Sᶜ.card := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_subtype_compl, Finset.card_compl]
  rw [h1, h2, ← pow_add]
  unfold graphCutRank Matrix.rank
  rw [add_comm, h3, h4]


/-- `swapPurity (graphState Γ) S · 2^{rk Γ[S,S^c]} = 2^{2n}` for the unnormalised graph state. -/
theorem swapPurity_graphState_mul (Γ : Fin n → Fin n → Bool) (hsym : ∀ i j, Γ i j = Γ j i) (S : Finset (Fin n)) :
    swapPurity (graphState Γ) S * 2 ^ graphCutRank Γ S = (2 : ℂ) ^ (2 * n) := by
  rw [swapPurity_graphState]
  simp_rw [qf_four Γ hsym]
  rw [sum_xy (fun u => chi (cutCrossForm Γ S u)), sum_chi_cross]
  have h := card_ker_mul Γ S
  have h' : ((Finset.univ.filter fun b : {j // j ∉ S} → ZMod 2 =>
      (cutMat Γ S).mulVec b = 0).card : ℂ) * 2 ^ graphCutRank Γ S = 2 ^ Sᶜ.card := by
    exact_mod_cast h
  have hc : S.card + Sᶜ.card = n := by rw [Finset.card_add_card_compl]; simp
  calc (2 : ℂ) ^ n * ((2 : ℂ) ^ S.card * ((Finset.univ.filter fun b : {j // j ∉ S} → ZMod 2 =>
          (cutMat Γ S).mulVec b = 0).card : ℂ)) * 2 ^ graphCutRank Γ S
      = (2 : ℂ) ^ n * (2 : ℂ) ^ S.card * (((Finset.univ.filter fun b : {j // j ∉ S} → ZMod 2 =>
          (cutMat Γ S).mulVec b = 0).card : ℂ) * 2 ^ graphCutRank Γ S) := by ring
    _ = (2 : ℂ) ^ n * (2 : ℂ) ^ S.card * 2 ^ Sᶜ.card := by rw [h']
    _ = (2 : ℂ) ^ (2 * n) := by
      rw [mul_assoc, ← pow_add, hc, ← pow_add]; ring_nf

/-- The normalised graph state `2^{-n/2} Σ_x (-1)^{q(x)} |x⟩`. -/
noncomputable def graphStateNorm (Γ : Fin n → Fin n → Bool) : Ψ n :=
  fun x => (((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℝ) : ℂ) * graphState Γ x

theorem swapPurity_smul (c : ℝ) (ψ : Ψ n) (S : Finset (Fin n)) :
    swapPurity (fun x => (c : ℂ) * ψ x) S = ((c ^ 4 : ℝ) : ℂ) * swapPurity ψ S := by
  unfold swapPurity
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

theorem nsq_graphStateNorm (Γ : Fin n → Fin n → Bool) : nsq (graphStateNorm Γ) = 1 := by
  unfold nsq graphStateNorm
  simp only [map_mul, Complex.normSq_ofReal, chi_normSq, graphState]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [mul_one, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin]
  have h : (0 : ℝ) < 2 ^ n := by positivity
  have h2 : ((Real.sqrt ((2 : ℝ) ^ n))⁻¹) * ((Real.sqrt ((2 : ℝ) ^ n))⁻¹) = ((2 : ℝ) ^ n)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt h.le]
  push_cast
  rw [h2]
  field_simp

/-- **`tr ρ_S² = 2^{-rk_2 Γ[S,S^c]}`** for the normalised graph state. -/
theorem purity_gsn (Γ : Fin n → Fin n → Bool) (hsym : ∀ i j, Γ i j = Γ j i) (S : Finset (Fin n)) :
    cutPurity (graphStateNorm Γ) S = (1 / 2 : ℝ) ^ graphCutRank Γ S := by
  have h1 : graphStateNorm Γ = fun x => (((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℝ) : ℂ) * graphState Γ x := rfl
  have h2 : swapPurity (graphStateNorm Γ) S = (((1 / 2 : ℝ) ^ graphCutRank Γ S : ℝ) : ℂ) := by
    rw [h1, swapPurity_smul]
    have h := swapPurity_graphState_mul Γ hsym S
    have hpos : ((2 : ℂ)) ^ graphCutRank Γ S ≠ 0 := pow_ne_zero _ two_ne_zero
    have h3 : swapPurity (graphState Γ) S = (2 : ℂ) ^ (2 * n) / 2 ^ graphCutRank Γ S := by
      rw [eq_div_iff hpos]; exact h
    rw [h3]
    have h4 : ((Real.sqrt ((2 : ℝ) ^ n))⁻¹) ^ 4 = ((2 : ℝ) ^ n)⁻¹ ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, inv_pow, Real.sq_sqrt (by positivity)]
    rw [h4]
    push_cast
    simp only [one_div, inv_pow]
    field_simp
    rw [← pow_mul, mul_comm]
  unfold cutPurity
  rw [h2]
  exact Complex.ofReal_re _

/-- info: 'FormalResearch.NQubit.Graph.purity_gsn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms purity_gsn

end FormalResearch.NQubit.Graph
