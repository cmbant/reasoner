module

public import FormalResearch.NQubit.Pauli.Weight

/-!
# Subsystem purities in Pauli coordinates, complementarity, and the rank-two reduction (any `n`)

`swapPurity ψ S = ⟨ψ⊗ψ | F_S | ψ⊗ψ⟩` is the two-copy swap expectation, i.e. `tr ρ_S²`; `cutPurity` is its real
part.  `cutPurity_eq_trace` in `Reduced/PartialTrace.lean` identifies it with the trace of the square of the
explicit partial trace.

* `two_pow_mul_cutPurity`: `tr ρ_S² = 2^{-|S|} Σ_{supp P ⊆ S} ⟨P⟩²`,
* `cutPurity_compl`: `tr ρ_S² = tr ρ_{Sᶜ}²` for a pure state (a one-line consequence of the swap form),
* `two_pow_mul_cutPuritySum` (via `PurU`): `2^s Σ_{|S|=s} tr ρ_S² = Σ_{j ≤ s} C(n-j, s-j) A_j`,
* `cutPuritySum_compl`: `Σ_{|S|=s} = Σ_{|S|=n-s}`,
* `cutPuritySum_split`: for a distinguished site `s`, `Σ_{|T|=k} tr ρ_T² = Q_k + Q_{n-k}` with
  `Q_r = Σ_{|S|=r, s∉S} tr ρ_S²`,
* `two_pow_mul_Q`: `Q_r(ρ) = 2^{-r} Σ_j C(m-j,r-j) B_j(ρ)` with `m = n - 1`.
-/

@[expose] public section


open scoped ComplexConjugate BigOperators
open FormalResearch.NQubit.Pauli

namespace FormalResearch.NQubit.Reduced

variable {n : ℕ}

/-- `swapOn S x y`: the configuration equal to `y` on `S` and to `x` off `S`. -/
def swapOn (S : Finset (Fin n)) (x y : Cfg n) : Cfg n := fun i => if i ∈ S then y i else x i

/-- `tr ρ_S² = ⟨ψ⊗ψ | F_S | ψ⊗ψ⟩`, `F_S` swapping the two copies of the qubits in `S`. -/
noncomputable def swapPurity (ψ : Ψ n) (S : Finset (Fin n)) : ℂ :=
  ∑ x, ∑ y, conj (ψ x) * conj (ψ y) * (ψ (swapOn S x y) * ψ (swapOn S y x))

/-- Pauli words supported inside `S`. -/
def wsupp (S : Finset (Fin n)) : Finset (Fin n → Fin 4) :=
  Fintype.piFinset fun i => if i ∈ S then Finset.univ else {0}

theorem mem_wsupp {S : Finset (Fin n)} {a : Fin n → Fin 4} :
    a ∈ wsupp S ↔ ∀ i, i ∉ S → a i = 0 := by
  unfold wsupp
  rw [Fintype.mem_piFinset]
  refine forall_congr' fun i => ?_
  by_cases h : i ∈ S <;> simp [h]

/-- The set of non-identity positions of a word. -/
def pauliSupport {n : ℕ} (a : Fin n → Fin 4) : Finset (Fin n) := Finset.univ.filter fun i => a i ≠ 0

theorem card_pauliSupport {n : ℕ} (a : Fin n → Fin 4) : (pauliSupport a).card = pauliWeight a := rfl

theorem mem_wsupp_iff_pauliSupport {S : Finset (Fin n)} {a : Fin n → Fin 4} : a ∈ wsupp S ↔ pauliSupport a ⊆ S := by
  rw [mem_wsupp]
  constructor
  · intro h i hi
    by_contra hS
    exact (Finset.mem_filter.mp hi).2 (h i hS)
  · intro h i hi
    by_contra hne
    exact hi (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩))

/-- The completeness kernel on words supported in `S`. -/
theorem kernel_supp (S : Finset (Fin n)) (x y x' y' : Cfg n) :
    ∑ a ∈ wsupp S, (∏ i, pauliSU (a i) (x i) (y i)) * conj (∏ i, pauliSU (a i) (x' i) (y' i))
      = (2 : ℂ) ^ S.card *
        (if y = swapOn S x y' ∧ x' = swapOn S y' x then 1 else 0) := by
  simp_rw [map_prod, ← Finset.prod_mul_distrib]
  unfold wsupp
  rw [← Finset.prod_univ_sum (fun i => if i ∈ S then (Finset.univ : Finset (Fin 4)) else {0})
    (fun i b => pauliSU b (x i) (y i) * conj (pauliSU b (x' i) (y' i)))]
  have hfac : ∀ i, ∑ b ∈ (if i ∈ S then (Finset.univ : Finset (Fin 4)) else {0}),
      pauliSU b (x i) (y i) * conj (pauliSU b (x' i) (y' i))
      = (if i ∈ S then (2 : ℂ) else 1) *
        (if y i = swapOn S x y' i ∧ x' i = swapOn S y' x i then 1 else 0) := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, ite_true, swapOn, pauliSU_sum]
      by_cases h1 : x i = x' i <;> by_cases h2 : y i = y' i <;> simp [h1, h2, eq_comm]
    · simp only [hi, ite_false, swapOn]
      by_cases h1 : x i = y i <;> by_cases h2 : x' i = y' i <;>
        simp [pauliSU, h1, h2, eq_comm]
  simp_rw [hfac]
  rw [Finset.prod_mul_distrib, Finset.prod_boole]
  have hS : ∏ i : Fin n, (if i ∈ S then (2 : ℂ) else 1) = 2 ^ S.card := by
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  rw [hS]
  congr 2
  apply propext
  constructor
  · intro h
    exact ⟨funext fun i => (h i (Finset.mem_univ i)).1, funext fun i => (h i (Finset.mem_univ i)).2⟩
  · rintro ⟨h1, h2⟩ i _
    exact ⟨congrFun h1 i, congrFun h2 i⟩

theorem collapse2 (F : Cfg n → Cfg n → ℂ) (u v : Cfg n) :
    ∑ y, ∑ x', F y x' * (if y = u ∧ x' = v then 1 else 0) = F u v := by
  simp [ite_and, mul_ite, Finset.sum_ite_eq']

theorem collapse3 (F : Cfg n → Cfg n → Cfg n → ℂ) (u v : Cfg n → Cfg n) :
    ∑ y, ∑ x', ∑ y', F y x' y' * (if y = u y' ∧ x' = v y' then 1 else 0)
      = ∑ y', F (u y') (v y') y' := by
  calc _ = ∑ y, ∑ y', ∑ x', F y x' y' * (if y = u y' ∧ x' = v y' then 1 else 0) :=
        Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ y', ∑ y, ∑ x', F y x' y' * (if y = u y' ∧ x' = v y' then 1 else 0) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun y' _ => collapse2 (fun y x' => F y x' y') (u y') (v y')

/-- **`tr ρ_S² = 2^{-|S|} Σ_{supp P ⊆ S} ⟨P⟩²`** (as an identity in `ℂ`, i.e. `2^{|S|} swapPurity = Σ pauliSq`). -/
theorem two_pow_mul_swapPurity (ψ : Ψ n) (S : Finset (Fin n)) :
    (2 : ℂ) ^ S.card * swapPurity ψ S = ∑ a ∈ wsupp S, (pauliSq ψ a : ℂ) := by
  have h := wavg_aux (wsupp S)
    (fun (a : Fin n → Fin 4) (x y : Cfg n) => ∏ i, pauliSU (a i) (x i) (y i)) (fun _ => (1 : ℂ))
    (fun x y x' y' => (2 : ℂ) ^ S.card * (if y = swapOn S x y' ∧ x' = swapOn S y' x then 1 else 0))
    (fun x y x' y' => by simpa using kernel_supp S x y x' y') ψ ψ
  simp only [one_mul] at h
  have e : ∑ a ∈ wsupp S, (pauliSq ψ a : ℂ) = ∑ a ∈ wsupp S,
      ((Complex.normSq (∑ x, conj (ψ x) * ∑ y, (∏ i, pauliSU (a i) (x i) (y i)) * ψ y) : ℝ) : ℂ) :=
    rfl
  have step : ∀ x y x' y' : Cfg n,
      (conj (ψ x) * ψ y * (ψ x' * conj (ψ y'))) *
        ((2 : ℂ) ^ S.card * (if y = swapOn S x y' ∧ x' = swapOn S y' x then 1 else 0))
      = (2 : ℂ) ^ S.card * ((conj (ψ x) * ψ y * (ψ x' * conj (ψ y'))) *
        (if y = swapOn S x y' ∧ x' = swapOn S y' x then 1 else 0)) := by
    intros; ring
  rw [e, h]
  unfold swapPurity
  simp_rw [step]
  simp_rw [← Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Eq.trans ?_ (collapse3 (fun y x' y' => conj (ψ x) * ψ y * (ψ x' * conj (ψ y')))
    (fun y' => swapOn S x y') (fun y' => swapOn S y' x)).symm
  exact Finset.sum_congr rfl fun y _ => by ring

theorem swapOn_compl (S : Finset (Fin n)) (x y : Cfg n) : swapOn Sᶜ x y = swapOn S y x := by
  funext i
  by_cases h : i ∈ S <;> simp [swapOn, h]

theorem swapPurity_compl (ψ : Ψ n) (S : Finset (Fin n)) : swapPurity ψ Sᶜ = swapPurity ψ S := by
  unfold swapPurity
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [swapOn_compl, swapOn_compl]
  ring

/-- Reduced purity `tr ρ_S²` (real part of `swapPurity`). -/
noncomputable def cutPurity (ψ : Ψ n) (S : Finset (Fin n)) : ℝ := (swapPurity ψ S).re

theorem swapPurity_eq_real (ψ : Ψ n) (S : Finset (Fin n)) :
    swapPurity ψ S = (((∑ a ∈ wsupp S, pauliSq ψ a) / 2 ^ S.card : ℝ) : ℂ) := by
  have h := two_pow_mul_swapPurity ψ S
  have h2 : (2 : ℂ) ^ S.card ≠ 0 := pow_ne_zero _ two_ne_zero
  push_cast
  rw [eq_div_iff h2, mul_comm, h]

theorem cutPurity_eq (ψ : Ψ n) (S : Finset (Fin n)) :
    cutPurity ψ S = (∑ a ∈ wsupp S, pauliSq ψ a) / 2 ^ S.card := by
  unfold cutPurity; rw [swapPurity_eq_real]; exact Complex.ofReal_re _

theorem swapPurity_eq (ψ : Ψ n) (S : Finset (Fin n)) : swapPurity ψ S = (cutPurity ψ S : ℂ) := by
  rw [cutPurity_eq]; exact swapPurity_eq_real ψ S

/-- `2^{|S|} tr ρ_S² = Σ_{supp P ⊆ S} ⟨P⟩²`. -/
theorem two_pow_mul_cutPurity (ψ : Ψ n) (S : Finset (Fin n)) :
    (2 : ℝ) ^ S.card * cutPurity ψ S = ∑ a ∈ wsupp S, pauliSq ψ a := by
  rw [cutPurity_eq]
  field_simp

theorem cutPurity_nonneg (ψ : Ψ n) (S : Finset (Fin n)) : 0 ≤ cutPurity ψ S := by
  have h := two_pow_mul_cutPurity ψ S
  have : 0 ≤ ∑ a ∈ wsupp S, pauliSq ψ a := Finset.sum_nonneg fun a _ => pauliSq_nonneg ψ a
  have h2 : (0 : ℝ) < 2 ^ S.card := by positivity
  nlinarith

/-- **Complementarity**: `tr ρ_S² = tr ρ_{Sᶜ}²` for every vector (pure state). -/
theorem cutPurity_compl (ψ : Ψ n) (S : Finset (Fin n)) : cutPurity ψ Sᶜ = cutPurity ψ S := by
  unfold cutPurity; rw [swapPurity_compl]

theorem cutPurity_empty (ψ : Ψ n) : cutPurity ψ ∅ = (nsq ψ) ^ 2 := by
  have h := two_pow_mul_cutPurity ψ ∅
  have hw : wsupp (∅ : Finset (Fin n)) = {fun _ => 0} := by
    ext a; simp [mem_wsupp, funext_iff]
  rw [hw, Finset.sum_singleton] at h
  simp at h
  rw [h]
  unfold pauliSq pexp
  have : rot (fun i => pauliSU ((fun _ => (0 : Fin 4)) i)) ψ = ψ := by
    have : (fun i : Fin n => pauliSU ((fun _ => (0 : Fin 4)) i)) = fun _ => (1 : Op1) := by
      funext i; rfl
    rw [this, rot_one]
  rw [this, ip_self]
  simp [Complex.normSq_ofReal, sq]

/-! ### Sums over subsets of a fixed size -/

/-- `Σ_{S ⊆ U, |S| = r} tr ρ_S²`. -/
noncomputable def cutPuritySumOn (ψ : Ψ n) (U : Finset (Fin n)) (r : ℕ) : ℝ :=
  ∑ S ∈ U.powersetCard r, cutPurity ψ S

/-- `Σ_{|S| = r} tr ρ_S²`. -/
noncomputable def cutPuritySum (ψ : Ψ n) (r : ℕ) : ℝ := cutPuritySumOn ψ Finset.univ r

/-- Counting: `2^r Σ_{S ⊆ U, |S|=r} tr ρ_S² = Σ_{supp a ⊆ U} [pauliWeight a ≤ r] C(|U|-wt a, r-wt a) ⟨P_a⟩²`. -/
theorem two_pow_mul_cutPuritySumOn (ψ : Ψ n) (U : Finset (Fin n)) (r : ℕ) :
    (2 : ℝ) ^ r * cutPuritySumOn ψ U r =
      ∑ a ∈ wsupp U, (if pauliWeight a ≤ r then (Nat.choose (U.card - pauliWeight a) (r - pauliWeight a) : ℝ) else 0) * pauliSq ψ a := by
  unfold cutPuritySumOn
  rw [Finset.mul_sum]
  have h1 : ∀ S ∈ U.powersetCard r, (2 : ℝ) ^ r * cutPurity ψ S = ∑ a ∈ wsupp S, pauliSq ψ a := by
    intro S hS
    rw [← (Finset.mem_powersetCard.mp hS).2]
    exact two_pow_mul_cutPurity ψ S
  rw [Finset.sum_congr rfl h1]
  have h2 : ∀ S ∈ U.powersetCard r, ∑ a ∈ wsupp S, pauliSq ψ a
      = ∑ a ∈ wsupp U, if pauliSupport a ⊆ S then pauliSq ψ a else 0 := by
    intro S hS
    have hSU : S ⊆ U := (Finset.mem_powersetCard.mp hS).1
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext a
    simp only [Finset.mem_filter, mem_wsupp_iff_pauliSupport]
    constructor
    · intro h; exact ⟨h.trans hSU, h⟩
    · intro h; exact h.2
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hnzU : pauliSupport a ⊆ U := mem_wsupp_iff_pauliSupport.mp ha
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  by_cases hle : pauliWeight a ≤ r
  · rw [Finset.card_filter_powersetCard_subset (pauliSupport a) U r hnzU (by rw [card_pauliSupport]; exact hle),
      card_pauliSupport]
    simp only [hle, ↓reduceIte]
  · simp only [hle, ↓reduceIte]
    have : (Finset.filter (fun S => pauliSupport a ⊆ S) (U.powersetCard r)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro S hS hsub
      have := Finset.card_le_card hsub
      rw [card_pauliSupport, (Finset.mem_powersetCard.mp hS).2] at this
      exact hle this
    rw [this]; simp

theorem cutPuritySum_eq (ψ : Ψ n) (r : ℕ) :
    (2 : ℝ) ^ r * cutPuritySum ψ r =
      ∑ j ∈ Finset.range (n + 1), (if j ≤ r then (Nat.choose (n - j) (r - j) : ℝ) else 0) * weightEnum ψ j := by
  unfold cutPuritySum
  rw [two_pow_mul_cutPuritySumOn, sum_weightEnum_eq ψ (fun j => if j ≤ r then (Nat.choose (n - j) (r - j) : ℝ) else 0)]
  have hU : wsupp (Finset.univ : Finset (Fin n)) = Finset.univ := by
    ext a; simp [mem_wsupp]
  rw [hU]
  simp [Finset.card_univ]

/-- **Complementarity for subset sums**: `Σ_{|S|=r} tr ρ_S² = Σ_{|S|=n-r} tr ρ_S²` (`a_s = a_{n-s}`). -/
theorem cutPuritySum_compl (ψ : Ψ n) (r : ℕ) (hr : r ≤ n) : cutPuritySum ψ r = cutPuritySum ψ (n - r) := by
  unfold cutPuritySum cutPuritySumOn
  refine Finset.sum_nbij' (fun S => Sᶜ) (fun S => Sᶜ) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rw [Finset.mem_powersetCard] at hS ⊢
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_compl, hS.2, Fintype.card_fin]
  · intro S hS
    rw [Finset.mem_powersetCard] at hS ⊢
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_compl, hS.2, Fintype.card_fin]; omega
  · intro S _; simp
  · intro S _; simp
  · intro S _; exact (cutPurity_compl ψ S).symm

theorem mem_pc_erase {s : Fin n} {S : Finset (Fin n)} {k : ℕ} :
    S ∈ (Finset.univ.erase s).powersetCard k ↔ s ∉ S ∧ S.card = k := by
  rw [Finset.mem_powersetCard]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun hs => by simpa using h1 hs, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun x hx => Finset.mem_erase.mpr ⟨fun hxs => h1 (hxs ▸ hx), Finset.mem_univ x⟩, h2⟩

/-- **Rank-two (qubit) reduction, forward direction.**
For a distinguished site `s`, with `ρ = tr_s |ψ⟩⟨ψ|` and `Q_r = Σ_{S ⊆ [n]∖{s}, |S| = r} tr ρ_S²`
(the subset-`r` purities of `ρ`; `Q_r = 0` for `r > n-1`):
`Σ_{|T|=k} tr ρ_T² = Q_k + Q_{n-k}`. -/
theorem cutPuritySum_split (ψ : Ψ n) (s : Fin n) (k : ℕ) (hk : k ≤ n) :
    cutPuritySum ψ k = cutPuritySumOn ψ (Finset.univ.erase s) k + cutPuritySumOn ψ (Finset.univ.erase s) (n - k) := by
  unfold cutPuritySum cutPuritySumOn
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.powersetCard k (Finset.univ : Finset (Fin n)))
    (fun S => s ∈ S)]
  rw [add_comm]
  congr 1
  · -- sets avoiding `s`
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext S
    rw [Finset.mem_filter, mem_pc_erase, Finset.mem_powersetCard]
    simp [and_comm]
  · -- sets containing `s`, via complements
    refine Finset.sum_nbij' (fun S => Sᶜ) (fun S => Sᶜ) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hS
      rw [mem_pc_erase]
      exact ⟨by simpa using hS.2, by rw [Finset.card_compl, hS.1.2, Fintype.card_fin]⟩
    · intro S hS
      rw [mem_pc_erase] at hS
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, ?_⟩, by simpa using hS.1⟩
      rw [Finset.card_compl, hS.2, Fintype.card_fin]; omega
    · intro S _; simp
    · intro S _; simp
    · intro S _; exact (cutPurity_compl ψ S).symm

/-- `Σ_{a : a_s = 0, pauliWeight a = j} ⟨P_a⟩²`: the Pauli weight distribution of the reduction `ρ = tr_s |ψ⟩⟨ψ|`
(words with the identity on `s`). -/
noncomputable def weightEnumExcl (ψ : Ψ n) (s : Fin n) (j : ℕ) : ℝ :=
  ∑ a ∈ (wsupp (Finset.univ.erase s)).filter (fun a => pauliWeight a = j), pauliSq ψ a

theorem sum_wt_fiber (T : Finset (Fin n → Fin 4)) (f : ℕ → ℝ) (g : (Fin n → Fin 4) → ℝ) :
    ∑ a ∈ T, f (pauliWeight a) * g a
      = ∑ j ∈ Finset.range (n + 1), f j * ∑ a ∈ T.filter (fun a => pauliWeight a = j), g a := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := Finset.range (n + 1)) (g := pauliWeight)
    (fun a _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (pauliWeight_le a)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.mp ha).2]

/-- **Rank-two reduction, last formula (`d = 2`).**
`2^r Q_r(ρ) = Σ_{j ≤ r} C(m-j, r-j) B_j(ρ)` with `m = n - 1`. -/
theorem two_pow_mul_Q (ψ : Ψ n) (s : Fin n) (r : ℕ) :
    (2 : ℝ) ^ r * cutPuritySumOn ψ (Finset.univ.erase s) r =
      ∑ j ∈ Finset.range (n + 1),
        (if j ≤ r then (Nat.choose (n - 1 - j) (r - j) : ℝ) else 0) * weightEnumExcl ψ s j := by
  rw [two_pow_mul_cutPuritySumOn]
  have hc : (Finset.univ.erase s).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ, Fintype.card_fin]
  rw [hc]
  exact sum_wt_fiber (wsupp (Finset.univ.erase s))
    (fun j => if j ≤ r then (Nat.choose (n - 1 - j) (r - j) : ℝ) else 0) (pauliSq ψ)

end FormalResearch.NQubit.Reduced
