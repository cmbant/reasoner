import FormalResearch.FourQubitEntropy.SpinFlipOmega

open scoped ComplexConjugate BigOperators Matrix
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.SpinFlip

/-- Hamming distance of two computational-basis configurations. -/
def ham {n : ℕ} (x y : Cfg n) : ℕ := (Finset.univ.filter fun i => x i ≠ y i).card

/-- The cross term `⟨f| P_a |g⟩` (with `P_a = ⊗ pauliSU (aᵢ)`). -/
noncomputable def cross {n : ℕ} (f g : Ψ n) (a : Fin n → Fin 4) : ℂ :=
  ip f (rot (fun i => pauliSU (a i)) g)

/-- A Pauli word of weight `< d(x,y)` has zero matrix element between `x` and `y`. -/
theorem pauli_elem_zero {n : ℕ} (a : Fin n → Fin 4) (x y : Cfg n) (h : wt a < ham x y) :
    ∏ i, pauliSU (a i) (x i) (y i) = 0 := by
  by_contra hne
  apply absurd h
  rw [not_lt]
  unfold ham wt
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨Finset.mem_univ _, fun h0 => hne ?_⟩
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  have hp : (pauliSU 0 : Op1) = 1 := rfl
  rw [h0, hp]
  simp [hi.2]

theorem cross_zero {n : ℕ} (f g : Ψ n) (a : Fin n → Fin 4)
    (h : ∀ x y, f x ≠ 0 → g y ≠ 0 → wt a < ham x y) : cross f g a = 0 := by
  unfold cross ip rot
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hf : f x = 0
  · simp [hf]
  · rw [Finset.sum_eq_zero, mul_zero]
    intro y _
    by_cases hg : g y = 0
    · simp [hg]
    · rw [pauli_elem_zero a x y (h x y hf hg), zero_mul]

theorem bil_sum_diff {X : Type*} [Fintype X] (M : X → X → ℂ) (u v : X → ℂ) :
    (∑ x, conj ((u + v) x) * ∑ y, M x y * (u + v) y) -
      (∑ x, conj ((v - u) x) * ∑ y, M x y * (v - u) y) =
    2 * ((∑ x, conj (u x) * ∑ y, M x y * v y) + (∑ x, conj (v x) * ∑ y, M x y * u y)) := by
  have e : ∀ f g : X → ℂ, (∑ x, conj (f x) * ∑ y, M x y * g y) =
      ∑ x, ∑ y, conj (f x) * M x y * g y := by
    intro f g; simp [Finset.mul_sum, mul_assoc]
  simp only [e]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Pi.add_apply, Pi.sub_apply, map_add, map_sub]
  ring

/-- The matrix of the Pauli word `a`. -/
def Mat {n : ℕ} (a : Fin n → Fin 4) (x y : Cfg n) : ℂ := ∏ i, pauliSU (a i) (x i) (y i)

theorem pexp_mat {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) :
    pexp ψ a = ∑ x, conj (ψ x) * ∑ y, Mat a x y * ψ y := rfl

theorem cross_mat {n : ℕ} (f g : Ψ n) (a : Fin n → Fin 4) :
    cross f g a = ∑ x, conj (f x) * ∑ y, Mat a x y * g y := rfl

theorem pexp_sum_diff {n : ℕ} (u v : Ψ n) (a : Fin n → Fin 4) :
    pexp (u + v) a - pexp (v - u) a = 2 * (cross u v a + cross v u a) := by
  rw [pexp_mat, pexp_mat, cross_mat, cross_mat]
  exact bil_sum_diff (Mat a) u v

/-- **`thm:spinflip-double`, odd-weight selection** (unnormalised `Ω_{u,v}`; the scalar prefactor is
irrelevant for vanishing).  If the supports of `u` and `v` are at Hamming distance `≥ D`, every odd
Pauli word of weight `q < D` supported on the last `m` qubits has zero expectation in
`|0⟩(u+v) + |1⟩ Θ_m(v-u)`.  (`D > 0` is automatic: the statement is vacuous for `D = 0`.) -/
theorem spinflip_double_odd {m : ℕ} (u v : Ψ m) (D : ℕ)
    (hD : ∀ x y, u x ≠ 0 → v y ≠ 0 → D ≤ ham x y)
    (a' : Fin m → Fin 4) (hq : wt a' < D) (hodd : Odd (wt a')) :
    pexp (branch (u + v) (Θ (v - u))) (Fin.cons 0 a') = 0 := by
  rw [pexp_branch, pexp_Θ, conj_pexp, hodd.neg_one_pow]
  have h1 : cross u v a' = 0 :=
    cross_zero u v a' fun x y hx hy => lt_of_lt_of_le hq (hD x y hx hy)
  have h2 : cross v u a' = 0 :=
    cross_zero v u a' fun x y hx hy => by
      have : ham y x = ham x y := by
        unfold ham; congr 1; ext i; simp [eq_comm]
      rw [← this]; exact lt_of_lt_of_le hq (hD y x hy hx)
  have := pexp_sum_diff u v a'
  rw [h1, h2] at this
  linear_combination this

/-! ### Triple purities from vanishing odd correlations (`eq:ordinary-triple-purity`) -/

theorem pw_zero {n : ℕ} (ψ : Ψ n) : pw ψ (fun _ => 0) = nsq ψ * nsq ψ := by
  have h := A_zero ψ
  have hset : (Finset.univ.filter fun a : Fin n → Fin 4 => wt a = 0) = {fun _ => 0} := by
    ext a
    simp [wt, Finset.card_eq_zero, Finset.filter_eq_empty_iff, funext_iff]
  unfold A at h
  rwa [hset, Finset.sum_singleton] at h

/-- `thm`-free core of `cor:ordinary-triples`: for any `ψ` and any triple `U` of sites, if all
odd-weight Pauli words supported in `U` have zero expectation, then
`tr ρ_U² = ½ Σ_{S ⊆ U, |S| = 2} tr ρ_S² - ‖ψ‖⁴/4`. -/
theorem triple_purity {n : ℕ} (ψ : Ψ n) (U : Finset (Fin n)) (hU : U.card = 3)
    (h1 : ∀ a ∈ wsupp U, Odd (wt a) → pw ψ a = 0) :
    purity ψ U = PurU ψ U 2 / 2 - (nsq ψ * nsq ψ) / 4 := by
  have hP := two_pow_mul_purity ψ U
  have hQ := two_pow_mul_PurU ψ U 2
  rw [hU] at hP hQ
  have key : ∀ a ∈ wsupp U,
      pw ψ a - (if wt a ≤ 2 then (Nat.choose (3 - wt a) (2 - wt a) : ℝ) else 0) * pw ψ a
        = if a = (fun _ => 0) then -2 * pw ψ a else 0 := by
    intro a ha
    have hw : wt a ≤ 3 := by
      rw [← card_nz, ← hU]; exact Finset.card_le_card (mem_wsupp_iff_nz.mp ha)
    have hz : wt a = 0 ↔ a = (fun _ => 0) := by
      constructor
      · intro h
        funext i
        by_contra hne
        have : i ∈ nz a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
        have := Finset.card_pos.mpr ⟨i, this⟩
        rw [card_nz] at this; omega
      · rintro rfl; simp [wt]
    have hif : (if a = (fun _ => 0) then -2 * pw ψ a else 0)
        = if wt a = 0 then -2 * pw ψ a else 0 := by simp only [hz]
    rw [hif]
    interval_cases hwt : wt a
    · simp; ring
    · have := h1 a ha (by rw [hwt]; exact odd_one); simp [this]
    · simp
    · have := h1 a ha (by rw [hwt]; decide); simp [this]
  have hsum : (2 : ℝ) ^ 3 * purity ψ U - 2 ^ 2 * PurU ψ U 2
      = ∑ a ∈ wsupp U, (if a = (fun _ => 0) then -2 * pw ψ a else 0) := by
    rw [hP, hQ, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl key
  have h0 : (fun _ : Fin n => (0 : Fin 4)) ∈ wsupp U := by
    rw [mem_wsupp]; intro i _; rfl
  rw [Finset.sum_ite_eq' (wsupp U) (fun _ : Fin n => (0 : Fin 4))] at hsum
  simp only [h0, ↓reduceIte, pw_zero] at hsum
  linarith

theorem powersetCard_two_triple {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ({i, j, k} : Finset (Fin n)).powersetCard 2 = {{i, j}, {i, k}, {j, k}} := by
  ext S
  simp only [Finset.mem_powersetCard, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hsub, hc⟩
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc
    have hx := hsub (by simp : x ∈ ({x, y} : Finset (Fin n)))
    have hy := hsub (by simp : y ∈ ({x, y} : Finset (Fin n)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact absurd rfl hxy | skip
    all_goals first
      | (left; rfl) | (right; left; rfl) | (right; right; rfl)
      | (left; exact Finset.pair_comm _ _) | (right; left; exact Finset.pair_comm _ _)
      | (right; right; exact Finset.pair_comm _ _)
  · rintro (rfl | rfl | rfl)
    · refine ⟨?_, Finset.card_pair hij⟩
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢; tauto
    · refine ⟨?_, Finset.card_pair hik⟩
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢; tauto
    · refine ⟨?_, Finset.card_pair hjk⟩
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢; tauto

theorem PurU_triple {n : ℕ} (ψ : Ψ n) (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    PurU ψ {i, j, k} 2 = purity ψ {i, j} + purity ψ {i, k} + purity ψ {j, k} := by
  have n1 : ({i, j} : Finset (Fin n)) ≠ {i, k} := by
    intro h
    have : j ∈ ({i, k} : Finset (Fin n)) := h ▸ (by simp)
    simp [hij.symm, hjk] at this
  have n2 : ({i, j} : Finset (Fin n)) ≠ {j, k} := by
    intro h
    have : i ∈ ({j, k} : Finset (Fin n)) := h ▸ (by simp)
    simp [hij, hik] at this
  have n3 : ({i, k} : Finset (Fin n)) ≠ {j, k} := by
    intro h
    have : i ∈ ({j, k} : Finset (Fin n)) := h ▸ (by simp)
    simp [hij, hik] at this
  unfold PurU
  rw [powersetCard_two_triple i j k hij hik hjk, Finset.sum_insert (by simp [n1, n2]),
    Finset.sum_pair n3, add_assoc]

/-- **`cor:ordinary-triples`** (general form, any `m`).  Let `Ω = |0⟩(u+v) + |1⟩ Θ_m(v-u)` with the
supports of `u`, `v` at Hamming distance `≥ 4`.  For every three distinct ordinary sites `i, j, k`,
`tr ρ_{ijk}² = ½(tr ρ_{ij}² + tr ρ_{ik}² + tr ρ_{jk}²) - ‖Ω‖⁴/4` (`‖Ω‖ = 1` when normalised). -/
theorem ordinary_triple_purity {m : ℕ} (u v : Ψ m)
    (hD : ∀ x y, u x ≠ 0 → v y ≠ 0 → 4 ≤ ham x y) (i j k : Fin m)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    purity (branch (u + v) (Θ (v - u))) {i.succ, j.succ, k.succ} =
      (purity (branch (u + v) (Θ (v - u))) {i.succ, j.succ}
        + purity (branch (u + v) (Θ (v - u))) {i.succ, k.succ}
        + purity (branch (u + v) (Θ (v - u))) {j.succ, k.succ}) / 2
      - (nsq (branch (u + v) (Θ (v - u))) * nsq (branch (u + v) (Θ (v - u)))) / 4 := by
  have hij' : i.succ ≠ j.succ := fun h => hij (Fin.succ_injective _ h)
  have hik' : i.succ ≠ k.succ := fun h => hik (Fin.succ_injective _ h)
  have hjk' : j.succ ≠ k.succ := fun h => hjk (Fin.succ_injective _ h)
  have hcard : ({i.succ, j.succ, k.succ} : Finset (Fin (m + 1))).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hij', hik']), Finset.card_pair hjk']
  have h1 : ∀ a ∈ wsupp ({i.succ, j.succ, k.succ} : Finset (Fin (m + 1))),
      Odd (wt a) → pw (branch (u + v) (Θ (v - u))) a = 0 := by
    intro a ha hodd
    have h0 : a 0 = 0 := by
      rw [mem_wsupp] at ha
      exact ha 0 (by simp [(Fin.succ_ne_zero _).symm])
    have hw : wt a ≤ 3 := by
      rw [← card_nz, ← hcard]; exact Finset.card_le_card (mem_wsupp_iff_nz.mp ha)
    have ha' : a = Fin.cons 0 (Fin.tail a) := by
      rw [← h0]; exact (Fin.cons_self_tail a).symm
    have hwt : wt (Fin.tail a) = wt a := by
      conv_rhs => rw [ha']
      rw [wt_cons]; simp
    have : pexp (branch (u + v) (Θ (v - u))) a = 0 := by
      rw [ha']
      exact spinflip_double_odd u v 4 hD (Fin.tail a) (by omega) (by rw [hwt]; exact hodd)
    unfold pw; rw [this]; simp
  rw [triple_purity _ _ hcard h1, PurU_triple _ _ _ _ hij' hik' hjk']

end FormalResearch.FourQubitEntropy.SpinFlip
