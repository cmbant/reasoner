module

public import FormalResearch.PPTThreeQubit.MomentCone
public import FormalResearch.ConvexGeometry.ConeCaratheodory
public import FormalResearch.PPTThreeQubit.CurveParam
public import FormalResearch.GurvitsBarnum.Closed

/-!
# The Carathéodory bound for the moment cone (`thm:ppt3-universal-moments`)

Source: `relaxations_and_scope.tex`, `thm:ppt3-universal-moments` ("every biseparable operator on
`R` is a sum of at most `25` cut-product projectors") and `appendix_moment_cone.tex` (proof: the cone
over the compact set of trace-one product projectors is closed, and Carathéodory's theorem in the
`25`-dimensional real space of Hermitian `5 × 5` matrices bounds the number of terms).

* `finrank_hermitian_le`: the real space of Hermitian `n × n` matrices has dimension at most `n²`.
* `biseparable_card_le_25`: for `B` of full column rank with the cut curves `B T_c ν(a)`
  (`CutCurve`, `T_c` invertible), a biseparable `B X Bᴴ` is a sum of at most `25` cut-product
  projectors.  Via the generic conic Carathéodory `FormalResearch.ConvexGeometry.ConeCar.exists_coneRep_card_le`.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix FormalResearch.GurvitsBarnum
open scoped ComplexOrder

noncomputable section

/-- The real subspace of Hermitian matrices. -/
def hermSub (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {M | Mᴴ = M}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at *
    rw [conjTranspose_add, ha, hb]
  zero_mem' := by simp
  smul_mem' := fun r {a} ha => by
    simp only [Set.mem_ofPred_eq] at *
    rw [conjTranspose_smul, ha]; simp

/-- The real space of Hermitian `n × n` matrices has dimension at most `n²`. -/
theorem finrank_hermitian_le (n : ℕ) : Module.finrank ℝ (hermSub n) ≤ n ^ 2 := by
  let f : hermSub n →ₗ[ℝ] (Fin n × Fin n → ℝ) :=
    { toFun := fun M p => if p.1 ≤ p.2 then (M.1 p.1 p.2).re else (M.1 p.1 p.2).im
      map_add' := fun M N => by
        ext p; by_cases h : p.1 ≤ p.2 <;> simp [h]
      map_smul' := fun r M => by
        ext p; by_cases h : p.1 ≤ p.2 <;> simp [h] }
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro M hM
    have hH : (M.1)ᴴ = M.1 := M.2
    have hent : ∀ i j, M.1 j i = star (M.1 i j) := fun i j => by
      have := congrFun (congrFun hH j) i
      simpa [conjTranspose_apply] using this.symm
    have h0 : ∀ i j : Fin n, (if i ≤ j then (M.1 i j).re else (M.1 i j).im) = 0 :=
      fun i j => congrFun hM (i, j)
    have hz : ∀ i j, M.1 i j = 0 := by
      intro i j
      rcases lt_trichotomy i j with h | h | h
      · have r := h0 i j
        have im := h0 j i
        rw [ite_eq_left h.le] at r
        rw [ite_eq_right (not_le.2 h)] at im
        have h1 : (M.1 j i).im = -(M.1 i j).im := by rw [hent i j]; simp
        apply Complex.ext
        · simpa using r
        · simp only [Complex.zero_im]; linarith
      · subst h
        have r := h0 i i
        rw [ite_eq_left le_rfl] at r
        have h1 : (M.1 i i).im = -(M.1 i i).im := by
          conv_lhs => rw [hent i i]
          simp
        apply Complex.ext
        · simpa using r
        · simp only [Complex.zero_im]; linarith
      · have r := h0 i j
        have re := h0 j i
        rw [ite_eq_right (not_le.2 h)] at r
        rw [ite_eq_left h.le] at re
        have h1 : (M.1 i j).re = (M.1 j i).re := by rw [hent j i]; simp
        apply Complex.ext
        · simp only [Complex.zero_re]; linarith
        · simpa using r
    exact Subtype.ext (by ext i j; exact hz i j)
  calc Module.finrank ℝ (hermSub n) ≤ Module.finrank ℝ (Fin n × Fin n → ℝ) :=
        LinearMap.finrank_le_finrank_of_injective hf
    _ = n ^ 2 := by simp [Module.finrank_fintype_fun_eq_card, sq]

/-- The real part of the trace as a real-linear functional. -/
def reTrace (ι : Type*) [Fintype ι] : Matrix ι ι ℂ →ₗ[ℝ] ℝ where
  toFun X := (trace X).re
  map_add' X Y := by simp [trace_add]
  map_smul' r X := by simp [trace_smul]

/-- The generators `T_c ν(a) ν(a)ᴴ T_cᴴ`, `a ≠ 0`, of the cone `∑_c T_c 𝓜₄ T_cᴴ`. -/
def genS (T : Fin 3 → Matrix (Fin 5) (Fin 5) ℂ) : Set (Matrix (Fin 5) (Fin 5) ℂ) :=
  {M | ∃ (c : Fin 3) (a : Fin 2 → ℂ), a ≠ 0 ∧
    M = T c * vecMulVec (nuVec a) (star (nuVec a)) * (T c)ᴴ}

theorem nuVec_ne_zero {a : Fin 2 → ℂ} (ha : a ≠ 0) : nuVec a ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h4 := congrFun h 4
  simp [nuVec] at h0 h4
  apply ha
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h4

theorem reTrace_pos {T : Fin 3 → Matrix (Fin 5) (Fin 5) ℂ} (hT : ∀ c, IsUnit (T c).det)
    {M : Matrix (Fin 5) (Fin 5) ℂ} (hM : M ∈ genS T) : 0 < reTrace (Fin 5) M := by
  obtain ⟨c, a, ha, rfl⟩ := hM
  have hinj : Function.Injective (T c).mulVec := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (hT c))
  have hpd := Matrix.PosDef.conjTranspose_mul_self (T c) hinj
  have := hpd.re_dotProduct_pos (nuVec_ne_zero ha)
  have h2 := trace_mul_curve 1 (T c) (nuVec a)
  simp only [Matrix.one_mul] at h2
  show 0 < (trace (T c * vecMulVec (nuVec a) (star (nuVec a)) * (T c)ᴴ)).re
  rw [h2]
  simpa using this

theorem genS_hermitian {T : Fin 3 → Matrix (Fin 5) (Fin 5) ℂ} : genS T ⊆ (hermSub 5 : Set _) := by
  rintro _ ⟨c, a, ha, rfl⟩
  show (T c * vecMulVec (nuVec a) (star (nuVec a)) * (T c)ᴴ)ᴴ = _
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  congr 2
  ext i j
  simp [vecMulVec_apply, mul_comm]

/-- A cone term is a cut-product projector: `B (w T ν νᴴ Tᴴ) Bᴴ = |φ⟩⟨φ|`. -/
theorem term_eq (B : Matrix (Fin 8) (Fin 5) ℂ) (t : Matrix (Fin 5) (Fin 5) ℂ) (a : Fin 2 → ℂ)
    {w : ℝ} (hw : 0 ≤ w) :
    B * ((w : ℂ) • (t * vecMulVec (nuVec a) (star (nuVec a)) * tᴴ)) * Bᴴ =
      vecMulVec (((Real.sqrt w : ℝ) : ℂ) • (B *ᵥ (t *ᵥ nuVec a)))
        (star (((Real.sqrt w : ℝ) : ℂ) • (B *ᵥ (t *ᵥ nuVec a)))) := by
  rw [← mulVec_smul, vecMulVec_curve, Complex.normSq_ofReal, Real.mul_self_sqrt hw,
    Matrix.mul_smul, Matrix.smul_mul]

/-- **`thm:ppt3-universal-moments`: at most `25` terms.**  Let `B` have full column rank and the
cut-`c` product rays of `range B` be exactly the rays of `B T_c ν(a)` (`CutCurve`, with `T_c`
invertible).  Then every biseparable `B X Bᴴ` is a sum of at most `25` cut-product projectors
`|φᵢ⟩⟨φᵢ|`.  (Carathéodory's theorem in the `25`-dimensional real space of Hermitian `5 × 5`
matrices, in its conic form `FormalResearch.ConvexGeometry.ConeCar.exists_coneRep_card_le`.) -/
theorem biseparable_card_le_25 (B : Matrix (Fin 8) (Fin 5) ℂ) (T : Fin 3 → Matrix (Fin 5) (Fin 5) ℂ)
    (hB : Function.Injective B.mulVec) (hT : CutCurve B T) (hTu : ∀ c, IsUnit (T c).det)
    (X : Matrix (Fin 5) (Fin 5) ℂ) (hX : IsBiseparable (B * X * Bᴴ)) :
    ∃ n ≤ 25, ∃ φ : Fin n → Fin 8 → ℂ, (∀ i, IsCutProduct (φ i)) ∧
      B * X * Bᴴ = ∑ i, vecMulVec (φ i) (star (φ i)) := by
  classical
  obtain ⟨n, c, a, w, hw, hXe⟩ := (biseparable_iff_mem_cone B T hB hT X).1 hX
  set a₀ : Fin 2 → ℂ := ![1, 0] with ha₀
  have ha₀ne : a₀ ≠ 0 := fun h => by simpa [ha₀] using congrFun h 0
  set s₀ : Matrix (Fin 5) (Fin 5) ℂ :=
    T 0 * vecMulVec (nuVec a₀) (star (nuVec a₀)) * (T 0)ᴴ with hs₀
  have hs₀S : s₀ ∈ genS T := ⟨0, a₀, ha₀ne, rfl⟩
  have hrep : FormalResearch.ConvexGeometry.ConeCar.ConeRep (genS T) n X := by
    refine ⟨fun i => if a i = 0 then 0 else w i,
      fun i => if a i = 0 then s₀ else T (c i) * vecMulVec (nuVec (a i)) (star (nuVec (a i))) *
        (T (c i))ᴴ, fun i => ?_, fun i => ?_, ?_⟩
    · by_cases h : a i = 0 <;> simp [h, hw i]
    · by_cases h : a i = 0
      · simp [h, hs₀S]
      · simp only [h, ite_false]; exact ⟨c i, a i, h, rfl⟩
    · rw [hXe]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : a i = 0
      · simp [h, nuVec_zero]
      · simp [h, Complex.coe_smul]
  obtain ⟨m, hm, w', s', hw', hs', hXm⟩ := FormalResearch.ConvexGeometry.ConeCar.exists_coneRep_card_le (reTrace (Fin 5))
    (fun M hM => reTrace_pos hTu hM) (hermSub 5) genS_hermitian hrep
  have hm25 : m ≤ 25 := hm.trans (by simpa using finrank_hermitian_le 5)
  choose c' a' ha' hs'e using hs'
  refine ⟨m, hm25, fun j => ((Real.sqrt (w' j) : ℝ) : ℂ) • (B *ᵥ (T (c' j) *ᵥ nuVec (a' j))), ?_, ?_⟩
  · intro j
    rw [isCutProduct_iff]
    refine ⟨c' j, ?_⟩
    have := (hT (c' j) (((Real.sqrt (w' j) : ℝ) : ℂ) • (T (c' j) *ᵥ nuVec (a' j)))).2
      ⟨a' j, ((Real.sqrt (w' j) : ℝ) : ℂ), ha' j, by rw [mulVec_smul]⟩
    rwa [mulVec_smul] at this
  · rw [hXm, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hs'e j, ← term_eq B _ _ (hw' j), Complex.coe_smul]

/-! ### The biseparable cone is closed, with at most `64` terms -/

/-- The unit-trace cut-product projectors of three qubits: `|α⊗μ⟩⟨α⊗μ|` with unit `α ∈ ℂ²`,
`μ ∈ ℂ⁴`, reindexed to `ℂ⁸` along each of the three cuts. -/
def S8 : Set (Matrix (Fin 8) (Fin 8) ℂ) :=
  ⋃ c : Fin 3, (fun X : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ =>
    X.submatrix (cutEquiv c) (cutEquiv c)) '' unitProd (Fin 2) (Fin 4)

theorem continuous_submatrix_equiv (e : Fin 8 ≃ Fin 2 × Fin 4) :
    Continuous fun X : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ => X.submatrix e e :=
  continuous_matrix fun i j => continuous_id.matrix_elem (e i) (e j)

theorem isCompact_S8 : IsCompact S8 :=
  isCompact_iUnion fun _c => isCompact_unitProd.image (continuous_submatrix_equiv _)

theorem continuous_reTrace : Continuous (reTrace (Fin 8)) := by
  show Continuous fun X : Matrix (Fin 8) (Fin 8) ℂ => (trace X).re
  exact Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => continuous_id.matrix_elem i i)

theorem reTrace_S8 {M : Matrix (Fin 8) (Fin 8) ℂ} (hM : M ∈ S8) : reTrace (Fin 8) M = 1 := by
  obtain ⟨c, h⟩ := Set.mem_iUnion.1 hM
  obtain ⟨P, hP, rfl⟩ := h
  have h1 : trace (P.submatrix (cutEquiv c) (cutEquiv c)) = trace P := by
    unfold Matrix.trace
    simp only [diag_apply, submatrix_apply]
    exact Equiv.sum_comp (cutEquiv c) (fun p => P p p)
  show (trace (P.submatrix (cutEquiv c) (cutEquiv c))).re = 1
  rw [h1]
  exact trRe_of_mem_unitProd hP

theorem S8_hermitian : S8 ⊆ (hermSub 8 : Set (Matrix (Fin 8) (Fin 8) ℂ)) := by
  intro M hM
  obtain ⟨c, h⟩ := Set.mem_iUnion.1 hM
  obtain ⟨P, ⟨⟨u, v⟩, -, rfl⟩, rfl⟩ := h
  have hP : (prodRankOne u.ofLp v.ofLp)ᴴ = prodRankOne u.ofLp v.ofLp := by
    rw [prodRankOne_eq]
    ext p q
    simp [vecMulVec_apply, mul_comm]
  show ((prodRankOne u.ofLp v.ofLp).submatrix (cutEquiv c) (cutEquiv c))ᴴ = _
  rw [conjTranspose_submatrix, hP]

theorem exists_smul_mem_S8 {φ : Fin 8 → ℂ} (h : IsCutProduct φ) :
    ∃ s : ℝ, 0 ≤ s ∧ ∃ P ∈ S8, vecMulVec φ (star φ) = s • P := by
  obtain ⟨c, hc⟩ := (isCutProduct_iff φ).1 h
  obtain ⟨α, μ, hxe⟩ := (isCutProdAt_iff c φ).1 hc
  obtain ⟨s, hs, P, hP, hPe⟩ := exists_smul_mem_unitProd α μ
  refine ⟨s, hs, P.submatrix (cutEquiv c) (cutEquiv c), Set.mem_iUnion.2 ⟨c, P, hP, rfl⟩, ?_⟩
  have : vecMulVec φ (star φ) = (prodRankOne α μ).submatrix (cutEquiv c) (cutEquiv c) := by
    ext i j
    rw [prodRankOne_eq]
    simp [vecMulVec_apply, kroneckerVec, hxe]
  rw [this, hPe]
  ext i j; simp

theorem exists_cutProduct_of_mem_S8 {M : Matrix (Fin 8) (Fin 8) ℂ} (hM : M ∈ S8) {w : ℝ}
    (hw : 0 ≤ w) : ∃ φ : Fin 8 → ℂ, IsCutProduct φ ∧ w • M = vecMulVec φ (star φ) := by
  obtain ⟨c, h⟩ := Set.mem_iUnion.1 hM
  obtain ⟨P, ⟨⟨u, v⟩, -, rfl⟩, rfl⟩ := h
  refine ⟨fun i => ((Real.sqrt w : ℝ) : ℂ) *
    (u.ofLp ((cutEquiv c) i).1 * v.ofLp ((cutEquiv c) i).2), ?_, ?_⟩
  · rw [isCutProduct_iff]
    refine ⟨c, (isCutProdAt_iff c _).2 ⟨((Real.sqrt w : ℝ) : ℂ) • u.ofLp, v.ofLp, fun i => ?_⟩⟩
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  · ext i j
    simp only [Matrix.smul_apply, submatrix_apply, prodRankOne_eq, vecMulVec_apply, kroneckerVec,
      Pi.star_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
    have hs : ((Real.sqrt w : ℝ) : ℂ) * ((Real.sqrt w : ℝ) : ℂ) = (w : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hw]
    rw [Complex.real_smul]
    linear_combination (-(u.ofLp ((cutEquiv c) i).1 * v.ofLp ((cutEquiv c) i).2 *
      (starRingEnd ℂ (u.ofLp ((cutEquiv c) j).1) * starRingEnd ℂ (v.ofLp ((cutEquiv c) j).2)))) * hs

/-- Biseparability is membership in the cone generated by the compact set `S8`. -/
theorem isBiseparable_iff_cone (ρ : Matrix (Fin 8) (Fin 8) ℂ) :
    IsBiseparable ρ ↔ ∃ n, FormalResearch.ConvexGeometry.ConeCar.ConeRep S8 n ρ := by
  constructor
  · rintro ⟨n, φ, hφ, rfl⟩
    choose s hs P hP hsP using fun i => exists_smul_mem_S8 (hφ i)
    exact ⟨n, s, P, hs, hP, Finset.sum_congr rfl fun i _ => hsP i⟩
  · rintro ⟨n, w, M, hw, hM, rfl⟩
    choose φ hφ hφe using fun i => exists_cutProduct_of_mem_S8 (hM i) (hw i)
    exact ⟨n, φ, hφ, Finset.sum_congr rfl fun i _ => hφe i⟩

/-- **The set of biseparable three-qubit operators is closed.**  (The cone over the compact set of
unit-trace cut-product projectors.) -/
theorem isClosed_isBiseparable : IsClosed {ρ : Matrix (Fin 8) (Fin 8) ℂ | IsBiseparable ρ} := by
  have : {ρ : Matrix (Fin 8) (Fin 8) ℂ | IsBiseparable ρ} = {x | ∃ n, FormalResearch.ConvexGeometry.ConeCar.ConeRep S8 n x} := by
    ext ρ; exact isBiseparable_iff_cone ρ
  rw [this]
  exact FormalResearch.ConvexGeometry.ConeCar.isClosed_cone_of_isCompact isCompact_S8 (reTrace (Fin 8)) continuous_reTrace
    (fun s hs => by rw [reTrace_S8 hs]; exact one_pos)

/-- Every biseparable three-qubit operator is a sum of at most `64` cut-product projectors
(Carathéodory in the `64`-dimensional real space of Hermitian `8 × 8` matrices). -/
theorem isBiseparable_card_le_64 {ρ : Matrix (Fin 8) (Fin 8) ℂ} (h : IsBiseparable ρ) :
    ∃ n ≤ 64, ∃ φ : Fin n → Fin 8 → ℂ, (∀ i, IsCutProduct (φ i)) ∧
      ρ = ∑ i, vecMulVec (φ i) (star (φ i)) := by
  obtain ⟨n, hn⟩ := (isBiseparable_iff_cone ρ).1 h
  obtain ⟨m, hm, w, M, hw, hM, hρ⟩ := FormalResearch.ConvexGeometry.ConeCar.exists_coneRep_card_le (reTrace (Fin 8))
    (fun s hs => by rw [reTrace_S8 hs]; exact one_pos) (hermSub 8) S8_hermitian hn
  choose φ hφ hφe using fun i => exists_cutProduct_of_mem_S8 (hM i) (hw i)
  refine ⟨m, hm.trans (by simpa using finrank_hermitian_le 8), φ, hφ, ?_⟩
  rw [hρ]
  exact Finset.sum_congr rfl fun i _ => hφe i

/-- **`thm:ppt3-universal-moments`: the cone `∑_c T_c 𝓜₄ T_cᴴ` is closed** (for `B` of full column
rank with the cut curves of `CutCurve`).  It is the preimage of the closed set of biseparable
operators under `X ↦ B X Bᴴ`, by `biseparable_iff_mem_cone`. -/
theorem isClosed_inMomentCone (B : Matrix (Fin 8) (Fin 5) ℂ) (T : Fin 3 → Matrix (Fin 5) (Fin 5) ℂ)
    (hB : Function.Injective B.mulVec) (hT : CutCurve B T) :
    IsClosed {X : Matrix (Fin 5) (Fin 5) ℂ | InMomentCone T X} := by
  have hcont : Continuous fun X : Matrix (Fin 5) (Fin 5) ℂ => B * X * Bᴴ := by fun_prop
  have := isClosed_isBiseparable.preimage hcont
  convert this using 1
  ext X
  exact (biseparable_iff_mem_cone B T hB hT X).symm

end

end FormalResearch.PPTThreeQubit

/-- info: 'FormalResearch.PPTThreeQubit.biseparable_card_le_25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.biseparable_card_le_25

/-- info: 'FormalResearch.PPTThreeQubit.isClosed_isBiseparable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.isClosed_isBiseparable

/-- info: 'FormalResearch.PPTThreeQubit.isBiseparable_card_le_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.isBiseparable_card_le_64

/-- info: 'FormalResearch.PPTThreeQubit.isClosed_inMomentCone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.isClosed_inMomentCone
