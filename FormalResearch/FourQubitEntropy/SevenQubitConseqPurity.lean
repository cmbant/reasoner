import FormalResearch.FourQubitEntropy.SevenQubitConseqPauli

/-!
# Consequences of the sharp seven-qubit purity bound: Pauli weights and cut compatibility

Conditional on `SevenPurityBound` (`π₃ ≥ 121/917` for every pure seven-qubit state, the content of
`cor:seven-global-from-fivecopy`; its proof is a computer certificate and is **not** formalized), this
file derives the elementary consequences `cor:sevenpauli` and `prop:seven-purity-cut-compatibility` of
`ResearchNotes/QI/seven_qubit_entanglement/balanced_purity.tex` and `seven_qubit_entropy_global_upper.tex`.

A pure state is `ψ : BitString → ℂ` with `∑ |ψ z|² = 1`; the purity of a cut is computed from the reduced
matrix `∑_r ψ(a,r) conj ψ(b,r)` exactly as in `SevenQubitIcoPurity` (same `Cut`, `encode`, `maskCut`).
-/

open scoped ComplexConjugate
open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

open FormalResearch.FourQubitEntropy.SevenQubitIco

/-! ### Definitions -/

/-- Reduced density matrix entry (ket `a`, bra `b`) of a pure state `ψ` across a cut. -/
def redEntry {k l : ℕ} (c : Cut k l) (ψ : BitString → ℂ) (a b : Fin k → Bool) : ℂ :=
  ∑ r : Fin l → Bool, ψ (encode c a r) * conj (ψ (encode c b r))

/-- Purity `tr ρ²` of the reduced state across a cut. -/
def cutPurity {k l : ℕ} (c : Cut k l) (ψ : BitString → ℂ) : ℝ :=
  ∑ a, ∑ b, Complex.normSq (redEntry c ψ a b)

/-- `π₃`: mean purity over the 35 three-qubit cuts. -/
noncomputable def meanPurity3 (ψ : BitString → ℂ) : ℝ :=
  (∑ m ∈ tripleMasks, cutPurity (maskCut 3 4 m) ψ) / 35

/-- A unit vector of `(ℂ²)^{⊗7}`. -/
def UnitVec (ψ : BitString → ℂ) : Prop := ∑ z, Complex.normSq (ψ z) = 1

/-- The sharp seven-qubit balanced purity bound (`cor:seven-global-from-fivecopy`), as a hypothesis. -/
def SevenPurityBound : Prop := ∀ ψ : BitString → ℂ, UnitVec ψ → 121 / 917 ≤ meanPurity3 ψ

/-- Pauli expectation `⟨ψ|P_μ|ψ⟩` of the Pauli string `μ` (`0,1,2,3 = I,X,Y,Z`). -/
def pexp (ψ : BitString → ℂ) (μ : Fin 7 → Fin 4) : ℂ :=
  ∑ z, ∑ w, conj (ψ z) * (∏ i, pauli (μ i) (z i) (w i)) * ψ w

/-- Squared Pauli expectation. -/
def psq (ψ : BitString → ℂ) (μ : Fin 7 → Fin 4) : ℝ := Complex.normSq (pexp ψ μ)

/-- Pauli weight of a string: the number of non-identity sites. -/
def pwt (μ : Fin 7 → Fin 4) : ℕ := (univ.filter fun i => μ i ≠ 0).card

/-- Pauli weight distribution `A_j = ∑_{wt P = j} ⟨P⟩²`. -/
def pauliA (ψ : BitString → ℂ) (j : ℕ) : ℝ := ∑ μ ∈ univ.filter fun μ => pwt μ = j, psq ψ μ

/-! ### Reduction of Pauli strings supported on a cut -/

/-- The Pauli string equal to `ν` on the `k`-side of the cut and to the identity on the complement. -/
def extPauli {k l : ℕ} (c : Cut k l) (ν : Fin k → Fin 4) : Fin 7 → Fin 4 :=
  fun i => Sum.elim ν (fun _ => 0) (c i)

theorem encode_bijective {k l : ℕ} (c : Cut k l) (hc : Function.Bijective c) :
    Function.Bijective (fun p : (Fin k → Bool) × (Fin l → Bool) => encode c p.1 p.2) := by
  constructor
  · rintro ⟨a, r⟩ ⟨a', r'⟩ h
    have h' : ∀ i, Sum.elim a r (c i) = Sum.elim a' r' (c i) := fun i => congrFun h i
    have key : ∀ j, Sum.elim a r j = Sum.elim a' r' j := fun j => by
      obtain ⟨i, rfl⟩ := hc.surjective j
      exact h' i
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · simpa using key (Sum.inl j)
    · simpa using key (Sum.inr j)
  · intro z
    refine ⟨(fun j => z (Function.surjInv hc.surjective (Sum.inl j)),
      fun j => z (Function.surjInv hc.surjective (Sum.inr j))), funext fun i => ?_⟩
    simp only [encode]
    rcases hci : c i with j | j
    · have e : Function.surjInv hc.surjective (Sum.inl j) = i :=
        hc.injective ((Function.surjInv_eq hc.surjective (Sum.inl j)).trans hci.symm)
      simp [e]
    · have e : Function.surjInv hc.surjective (Sum.inr j) = i :=
        hc.injective ((Function.surjInv_eq hc.surjective (Sum.inr j)).trans hci.symm)
      simp [e]

theorem pauli_zero (x y : Bool) : pauli 0 x y = if x = y then 1 else 0 := rfl

theorem prod_pauli_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (r r' : ι → Bool) :
    ∏ j, pauli 0 (r j) (r' j) = if r = r' then 1 else 0 := by
  simp only [pauli_zero]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

theorem prod_ext_pauli {k l : ℕ} (c : Cut k l) (hc : Function.Bijective c) (ν : Fin k → Fin 4)
    (a b : Fin k → Bool) (r r' : Fin l → Bool) :
    ∏ i, pauli (extPauli c ν i) (encode c a r i) (encode c b r' i) =
      (∏ j, pauli (ν j) (a j) (b j)) * (if r = r' then 1 else 0) := by
  have h := Fintype.prod_bijective c hc
    (fun i => pauli (extPauli c ν i) (encode c a r i) (encode c b r' i))
    (fun j => pauli (Sum.elim ν (fun _ => (0 : Fin 4)) j) (Sum.elim a r j) (Sum.elim b r' j))
    (fun i => rfl)
  rw [h, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [prod_pauli_zero]

theorem pexp_ext {k l : ℕ} (c : Cut k l) (hc : Function.Bijective c) (ψ : BitString → ℂ)
    (ν : Fin k → Fin 4) : pexp ψ (extPauli c ν) = trP (redEntry c ψ) ν := by
  have hf := encode_bijective c hc
  set G : BitString → BitString → ℂ := fun z w =>
    conj (ψ z) * (∏ i, pauli (extPauli c ν i) (z i) (w i)) * ψ w with hG
  have e1 : ∑ z, ∑ w, G z w =
      ∑ p : (Fin k → Bool) × (Fin l → Bool), ∑ q : (Fin k → Bool) × (Fin l → Bool),
        G (encode c p.1 p.2) (encode c q.1 q.2) := by
    rw [← hf.sum_comp]
    exact Finset.sum_congr rfl fun p _ => (hf.sum_comp (G (encode c p.1 p.2))).symm
  show ∑ z, ∑ w, G z w = _
  rw [e1]
  simp only [Fintype.sum_prod_type, hG, prod_ext_pauli c hc]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  unfold trP redEntry
  simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-! ### The two Parseval identities for a cut -/

theorem purity_sum {k l : ℕ} (c : Cut k l) (hc : Function.Bijective c) (ψ : BitString → ℂ) :
    ∑ ν : Fin k → Fin 4, psq ψ (extPauli c ν) = 2 ^ k * cutPurity c ψ := by
  simp only [psq, pexp_ext c hc, sum_sq_trP, Fintype.card_fin]
  rfl

/-- The sign `(-1)^{wt μ}` of a Pauli string. -/
def psgn (μ : Fin 7 → Fin 4) : ℝ := ∏ i, (if μ i = 0 then (1 : ℝ) else -1)

theorem psgn_ext {k l : ℕ} (c : Cut k l) (hc : Function.Bijective c) (ν : Fin k → Fin 4) :
    psgn (extPauli c ν) = ∏ j, (if ν j = 0 then (1 : ℝ) else -1) := by
  have h := Fintype.prod_bijective c hc
    (fun i => if extPauli c ν i = 0 then (1 : ℝ) else -1)
    (fun j => if Sum.elim ν (fun _ => (0 : Fin 4)) j = 0 then (1 : ℝ) else -1) (fun i => rfl)
  unfold psgn
  rw [h, Fintype.prod_sum_type]
  simp
  rfl

theorem psgn_eq (μ : Fin 7 → Fin 4) : psgn μ = (-1) ^ pwt μ := by
  unfold psgn pwt
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]

/-- Shadow positivity (Rains): the sign-weighted sum over strings supported on a cut is `≥ 0`. -/
theorem shadow_sum {k l : ℕ} (c : Cut k l) (hc : Function.Bijective c) (ψ : BitString → ℂ) :
    0 ≤ ∑ ν : Fin k → Fin 4, psgn (extPauli c ν) * psq ψ (extPauli c ν) := by
  have h := sum_sign_sq_trP (fun (a : Fin k → Bool) (r : Fin l → Bool) => ψ (encode c a r))
  have e : ∑ ν : Fin k → Fin 4, psgn (extPauli c ν) * psq ψ (extPauli c ν) =
      ∑ ν : Fin k → Fin 4, (∏ i, (if ν i = 0 then (1 : ℝ) else -1)) *
        Complex.normSq (trP (fun a b => ∑ r, ψ (encode c a r) * conj (ψ (encode c b r))) ν) := by
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [psgn_ext c hc, psq, pexp_ext c hc]
    rfl
  rw [e, h]
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun r' _ => Complex.normSq_nonneg _)

/-! ### Strings supported on the cut of a mask -/

/-- Pauli strings supported on the sites selected by the mask `m`. -/
def suppSet (m : Fin 7 → Bool) : Finset (Fin 7 → Fin 4) :=
  univ.filter fun μ => ∀ i, μ i ≠ 0 → m i = true

theorem maskCut_inl_iff (m : Fin 7 → Bool) (i : Fin 7) :
    (∃ j, maskCut 3 4 m i = Sum.inl j) ↔ m i = true := by
  unfold maskCut
  by_cases h : m i = true <;> simp [h]

theorem extPauli_injective (m : Fin 7 → Bool) (hm : weight m = 3) :
    Function.Injective (extPauli (maskCut 3 4 m) : (Fin 3 → Fin 4) → Fin 7 → Fin 4) := by
  have hc := maskCut_bijective_three m hm
  intro ν ν' h
  funext j
  obtain ⟨i, hi⟩ := hc.surjective (Sum.inl j)
  have := congrFun h i
  simpa [extPauli, hi] using this

theorem image_ext_mask (m : Fin 7 → Bool) (hm : weight m = 3) :
    Finset.univ.image (extPauli (maskCut 3 4 m) : (Fin 3 → Fin 4) → Fin 7 → Fin 4) = suppSet m := by
  have hc := maskCut_bijective_three m hm
  ext μ
  simp only [Finset.mem_image, Finset.mem_univ, true_and, suppSet, Finset.mem_filter]
  constructor
  · rintro ⟨ν, rfl⟩ i hi
    by_contra hmi
    have : maskCut 3 4 m i = Sum.inr (Fin.ofNat 4 (countBefore m false i)) := by
      unfold maskCut; simp [hmi]
    simp [extPauli, this] at hi
  · intro h
    refine ⟨fun j => μ (Function.surjInv hc.surjective (Sum.inl j)), funext fun i => ?_⟩
    simp only [extPauli]
    rcases hci : maskCut 3 4 m i with j | j
    · have e : Function.surjInv hc.surjective (Sum.inl j) = i :=
        hc.injective ((Function.surjInv_eq hc.surjective (Sum.inl j)).trans hci.symm)
      simp [e]
    · by_contra hne
      have := (maskCut_inl_iff m i).2 (h i (Ne.symm (by simpa using hne)))
      obtain ⟨j', hj'⟩ := this
      rw [hci] at hj'
      cases hj'

theorem sum_ext_mask (m : Fin 7 → Bool) (hm : weight m = 3) (F : (Fin 7 → Fin 4) → ℝ) :
    ∑ ν : Fin 3 → Fin 4, F (extPauli (maskCut 3 4 m) ν) = ∑ μ ∈ suppSet m, F μ := by
  rw [← image_ext_mask m hm, Finset.sum_image (fun x _ y _ h => extPauli_injective m hm h)]

theorem purity_mask (m : Fin 7 → Bool) (hm : weight m = 3) (ψ : BitString → ℂ) :
    ∑ μ ∈ suppSet m, psq ψ μ = 8 * cutPurity (maskCut 3 4 m) ψ := by
  rw [← sum_ext_mask m hm, purity_sum _ (maskCut_bijective_three m hm)]
  norm_num

theorem shadow_mask (m : Fin 7 → Bool) (hm : weight m = 3) (ψ : BitString → ℂ) :
    0 ≤ ∑ μ ∈ suppSet m, psgn μ * psq ψ μ := by
  rw [← sum_ext_mask m hm (fun μ => psgn μ * psq ψ μ)]
  exact shadow_sum _ (maskCut_bijective_three m hm) ψ

/-! ### The Pauli weight enumerator and the counting of cuts -/

theorem psq_zero (ψ : BitString → ℂ) (hψ : UnitVec ψ) : psq ψ 0 = 1 := by
  have h : pexp ψ 0 = ((∑ z, Complex.normSq (ψ z) : ℝ) : ℂ) := by
    unfold pexp
    simp only [Pi.zero_apply, prod_pauli_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp [Complex.normSq_eq_conj_mul_self]
  unfold psq
  rw [h, hψ]
  simp

theorem pwt_zero : pwt 0 = 0 := by simp [pwt]

theorem pwt_lt (μ : Fin 7 → Fin 4) : pwt μ < 8 := by
  unfold pwt
  have := Finset.card_le_univ (univ.filter fun i => μ i ≠ 0)
  simp only [Fintype.card_fin] at this
  omega

/-- The number of three-site masks containing a given set of sites. -/
def cntN (j : ℕ) : ℕ := if j = 0 then 35 else if j = 1 then 15 else if j = 2 then 5 else if j = 3 then 1 else 0

theorem mask_count : ∀ s : Fin 7 → Bool,
    (tripleMasks.filter fun m => ∀ i, s i = true → m i = true).card = cntN (weight s) := by
  decide +kernel

theorem pwt_eq_weight (μ : Fin 7 → Fin 4) :
    pwt μ = weight (fun i => decide (μ i ≠ 0)) := by
  simp [pwt, weight]

theorem sum_by_pwt (ψ : BitString → ℂ) (f : ℕ → ℝ) :
    ∑ μ : Fin 7 → Fin 4, f (pwt μ) * psq ψ μ = ∑ j ∈ range 8, f j * pauliA ψ j := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range 8) (g := pwt)
    (fun μ _ => Finset.mem_range.2 (pwt_lt μ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold pauliA
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [(Finset.mem_filter.1 hμ).2]

/-- Summing the cut identity over the 35 cuts: `∑_S 8 tr ρ_S² = ∑_μ N(wt μ) ⟨P_μ⟩²`. -/
theorem sum_cuts_pauli (ψ : BitString → ℂ) :
    ∑ m ∈ tripleMasks, ∑ μ ∈ suppSet m, psq ψ μ = ∑ μ : Fin 7 → Fin 4, (cntN (pwt μ) : ℝ) * psq ψ μ := by
  have h1 : ∀ m : Fin 7 → Bool, ∑ μ ∈ suppSet m, psq ψ μ =
      ∑ μ : Fin 7 → Fin 4, if (∀ i, μ i ≠ 0 → m i = true) then psq ψ μ else 0 := by
    intro m
    unfold suppSet
    rw [Finset.sum_filter]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, pwt_eq_weight]
  have := mask_count (fun i => decide (μ i ≠ 0))
  simp only [decide_eq_true_eq] at this
  rw [this, mul_comm]

theorem mean_purity_pauli (ψ : BitString → ℂ) (hψ : UnitVec ψ) :
    meanPurity3 ψ = 1 / 8 + (15 * pauliA ψ 1 + 5 * pauliA ψ 2 + pauliA ψ 3) / 280 := by
  have h1 : ∑ m ∈ tripleMasks, ∑ μ ∈ suppSet m, psq ψ μ =
      8 * ∑ m ∈ tripleMasks, cutPurity (maskCut 3 4 m) ψ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m hm => purity_mask m (Finset.mem_filter.1 hm).2 ψ
  have h2 := sum_cuts_pauli ψ
  have h3 := sum_by_pwt ψ (fun j => (cntN j : ℝ))
  have hA0 : pauliA ψ 0 = 1 := by
    unfold pauliA
    have : (univ.filter fun μ : Fin 7 → Fin 4 => pwt μ = 0) = {0} := by
      ext μ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        funext i
        by_contra hi
        have : i ∈ univ.filter fun i => μ i ≠ 0 := by simpa using hi
        have := Finset.card_pos.2 ⟨i, this⟩
        unfold pwt at h
        omega
      · rintro rfl; exact pwt_zero
    rw [this, Finset.sum_singleton, psq_zero ψ hψ]
  rw [h1] at h2
  rw [h3] at h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cntN] at h2
  norm_num at h2
  unfold meanPurity3
  rw [hA0] at h2
  linarith

/-! ### `cor:sevenpauli` -/

/-- **`cor:sevenpauli` (conditional).** Under the sharp purity bound, every unit seven-qubit state has
`15A₁ + 5A₂ + A₃ ≥ 255/131`. -/
theorem cor_sevenpauli (h : SevenPurityBound) (ψ : BitString → ℂ) (hψ : UnitVec ψ) :
    255 / 131 ≤ 15 * pauliA ψ 1 + 5 * pauliA ψ 2 + pauliA ψ 3 := by
  have h1 := h ψ hψ
  rw [mean_purity_pauli ψ hψ] at h1
  linarith

/-! ### `prop:seven-purity-cut-compatibility` -/

/-- The Pauli excess `e_S = 8 tr ρ_S² - 1` of the three-site cut with mask `m`. -/
def excess (m : Fin 7 → Bool) (ψ : BitString → ℂ) : ℝ := 8 * cutPurity (maskCut 3 4 m) ψ - 1

/-- `R = ∑_{|S|=3} e_S`. -/
noncomputable def excessSum (ψ : BitString → ℂ) : ℝ := ∑ m ∈ tripleMasks, excess m ψ

theorem excessSum_eq (ψ : BitString → ℂ) : excessSum ψ = 280 * meanPurity3 ψ - 35 := by
  unfold excessSum excess meanPurity3
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [tripleMasks_card]
  ring

theorem zero_mem_suppSet (m : Fin 7 → Bool) : (0 : Fin 7 → Fin 4) ∈ suppSet m := by
  simp [suppSet]

theorem pwt_le_of_mem_suppSet (m : Fin 7 → Bool) (hm : weight m = 3) {μ : Fin 7 → Fin 4}
    (h : μ ∈ suppSet m) : pwt μ ≤ 3 := by
  unfold pwt
  rw [← hm]
  unfold weight
  apply Finset.card_le_card
  intro i hi
  simp only [suppSet, Finset.mem_filter, Finset.mem_univ, true_and] at h hi ⊢
  exact h i hi

theorem excess_nonneg (m : Fin 7 → Bool) (hm : weight m = 3) (ψ : BitString → ℂ) (hψ : UnitVec ψ) :
    0 ≤ excess m ψ := by
  have h1 := purity_mask m hm ψ
  have h2 : psq ψ 0 ≤ ∑ μ ∈ suppSet m, psq ψ μ :=
    Finset.single_le_sum (f := psq ψ) (fun μ _ => Complex.normSq_nonneg _) (zero_mem_suppSet m)
  rw [psq_zero ψ hψ, h1] at h2
  unfold excess
  linarith

/-- **`prop:seven-purity-cut-compatibility`.** For every unit seven-qubit state and three-site cut
`S`: `3 e_S ≤ R + 2` (and `0 ≤ e_S`, `excess_nonneg`). -/
theorem cut_compat (m : Fin 7 → Bool) (hm : weight m = 3) (ψ : BitString → ℂ) (hψ : UnitVec ψ) :
    3 * excess m ψ ≤ excessSum ψ + 2 := by
  have hI1 := purity_mask m hm ψ
  have hI2 := shadow_mask m hm ψ
  have hS : ∑ m' ∈ tripleMasks, ∑ μ ∈ suppSet m', psq ψ μ =
      ∑ μ : Fin 7 → Fin 4, (cntN (pwt μ) : ℝ) * psq ψ μ := sum_cuts_pauli ψ
  have hS' : ∑ m' ∈ tripleMasks, ∑ μ ∈ suppSet m', psq ψ μ =
      8 * ∑ m' ∈ tripleMasks, cutPurity (maskCut 3 4 m') ψ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m' hm' => purity_mask m' (Finset.mem_filter.1 hm').2 ψ
  set κ : (Fin 7 → Fin 4) → ℝ := fun μ =>
    (cntN (pwt μ) : ℝ) - (if μ ∈ suppSet m then 3 + 2 * psgn μ else 0) with hκ
  have hκnn : ∀ μ, 0 ≤ κ μ := by
    intro μ
    simp only [hκ]
    by_cases hμ : μ ∈ suppSet m
    · have h3 := pwt_le_of_mem_suppSet m hm hμ
      rw [if_pos hμ, psgn_eq]
      generalize pwt μ = j at h3
      interval_cases j <;> simp [cntN] <;> norm_num
    · rw [if_neg hμ]; simp
  have hK : κ 0 * psq ψ 0 ≤ ∑ μ, κ μ * psq ψ μ :=
    Finset.single_le_sum (f := fun μ => κ μ * psq ψ μ)
      (fun μ _ => mul_nonneg (hκnn μ) (Complex.normSq_nonneg _)) (Finset.mem_univ _)
  have hκ0 : κ 0 = 30 := by
    simp only [hκ]
    rw [if_pos (zero_mem_suppSet m), psgn_eq, pwt_zero]
    simp [cntN]
    norm_num
  have hexp : ∑ μ, κ μ * psq ψ μ =
      ∑ μ : Fin 7 → Fin 4, (cntN (pwt μ) : ℝ) * psq ψ μ -
        (3 * ∑ μ ∈ suppSet m, psq ψ μ + 2 * ∑ μ ∈ suppSet m, psgn μ * psq ψ μ) := by
    have : ∀ μ, κ μ * psq ψ μ = (cntN (pwt μ) : ℝ) * psq ψ μ -
        (if μ ∈ suppSet m then 3 * psq ψ μ + 2 * (psgn μ * psq ψ μ) else 0) := by
      intro μ
      simp only [hκ]
      split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
  rw [hκ0, psq_zero ψ hψ, hexp, ← hS, hS', hI1] at hK
  have hR := excessSum_eq ψ
  unfold meanPurity3 at hR
  unfold excess
  linarith

end FormalResearch.FourQubitEntropy.SevenQubitConseq
