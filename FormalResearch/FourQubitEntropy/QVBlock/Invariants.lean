import Mathlib

/-!
# Invariant bases and the group-average projection (QV block calculus, T7)

For a finite group `G` and a matrix representation `ρ : G →* Matrix M M 𝕜` over a field of
characteristic `0`, `repAvg ρ = (1/|G|) ∑_g ρ g` is an idempotent with `ρ h * R = R = R * ρ h`.

`repAvg_eq_mul_invariants` (T7): if `V` has `n` linearly independent invariant columns and
`n = tr R` (the character-average formula `n = (1/|G|) ∑ tr ρ g`), then `R = V Λ` for some `Λ`; with
a similar `W` of left invariants, `R = V Λ Wᵀ`.
-/

open scoped Matrix BigOperators

namespace FormalResearch.FourQubitEntropy.QVBlock

set_option linter.unusedSectionVars false

section
variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
variable {G : Type*} [Group G] [Fintype G]
variable {M : Type*} [Fintype M] [DecidableEq M]

/-- The group-average projection `R = (1/|G|) ∑_g ρ g`. -/
noncomputable def repAvg (ρ : G →* Matrix M M 𝕜) : Matrix M M 𝕜 :=
  ((Fintype.card G : 𝕜)⁻¹) • ∑ g, ρ g

theorem card_ne_zero' : (Fintype.card G : 𝕜) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

theorem sum_const_smul' {α : Type*} [AddCommGroup α] [Module 𝕜 α] (a : α) :
    ∑ _g : G, a = (Fintype.card G : 𝕜) • a := by
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul 𝕜]

theorem mul_repAvg (ρ : G →* Matrix M M 𝕜) (h : G) : ρ h * repAvg ρ = repAvg ρ := by
  unfold repAvg
  rw [Matrix.mul_smul, Matrix.mul_sum]
  congr 1
  simp_rw [← map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft h) (fun g => ρ (h * g)) (fun g => ρ g) (fun _ => rfl)

theorem repAvg_mul (ρ : G →* Matrix M M 𝕜) (h : G) : repAvg ρ * ρ h = repAvg ρ := by
  unfold repAvg
  rw [Matrix.smul_mul, Matrix.sum_mul]
  congr 1
  simp_rw [← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight h) (fun g => ρ (g * h)) (fun g => ρ g) (fun _ => rfl)

theorem repAvg_mul_of_invariant (ρ : G →* Matrix M M 𝕜) {N : Type*} [Fintype N]
    (V : Matrix M N 𝕜) (hV : ∀ g, ρ g * V = V) : repAvg ρ * V = V := by
  have h1 : (∑ g, ρ g) * V = (Fintype.card G : 𝕜) • V := by
    rw [Matrix.sum_mul]
    simp only [hV]
    exact sum_const_smul' V
  unfold repAvg
  rw [Matrix.smul_mul, h1, smul_smul, inv_mul_cancel₀ card_ne_zero', one_smul]

theorem repAvg_mul_self (ρ : G →* Matrix M M 𝕜) : repAvg ρ * repAvg ρ = repAvg ρ :=
  repAvg_mul_of_invariant ρ (repAvg ρ) (mul_repAvg ρ)

theorem trace_repAvg (ρ : G →* Matrix M M 𝕜) :
    (repAvg ρ).trace = ((Fintype.card G : 𝕜)⁻¹) * ∑ g, (ρ g).trace := by
  simp [repAvg, Matrix.trace_smul, Matrix.trace_sum]

/-- **T7 (right invariants).** If `V` has `n` linearly independent `ρ`-invariant columns and
`n = tr (repAvg ρ)` then `repAvg ρ = V Λ`. -/
theorem repAvg_eq_mul_invariants (ρ : G →* Matrix M M 𝕜) {n : ℕ} (V : Matrix M (Fin n) 𝕜)
    (hV : ∀ g, ρ g * V = V) (hli : LinearIndependent 𝕜 Vᵀ)
    (hn : (n : 𝕜) = (repAvg ρ).trace) : ∃ Λ : Matrix (Fin n) M 𝕜, repAvg ρ = V * Λ := by
  set R := repAvg ρ with hR
  have hRV : R * V = V := repAvg_mul_of_invariant ρ V hV
  let f : Module.End 𝕜 (M → 𝕜) := Matrix.toLin' R
  have hidem : IsIdempotentElem f := by
    show f * f = f
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hR, repAvg_mul_self]
  have htr : LinearMap.trace 𝕜 _ f = (Module.finrank 𝕜 (LinearMap.range f) : 𝕜) :=
    (LinearMap.IsIdempotentElem.isProj_range f hidem).trace
  have hfin : Module.finrank 𝕜 (LinearMap.range f) = n := by
    rw [Matrix.trace_toLin'_eq] at htr
    exact_mod_cast (hn.trans htr).symm
  have hfV : ∀ i, f (Vᵀ i) = Vᵀ i := by
    intro i
    ext a
    have := congrFun (congrFun hRV a) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, f] using this
  have hspan : Submodule.span 𝕜 (Set.range Vᵀ) ≤ LinearMap.range f := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Vᵀ i, hfV i⟩
  have heq : Submodule.span 𝕜 (Set.range Vᵀ) = LinearMap.range f :=
    Submodule.eq_of_le_of_finrank_eq hspan (by rw [finrank_span_eq_card hli, hfin]; simp)
  have hcol : ∀ j, ∃ c : Fin n → 𝕜, R.mulVec (Pi.single j 1) = V.mulVec c := by
    intro j
    have hmem : R.mulVec (Pi.single j 1) ∈ Submodule.span 𝕜 (Set.range Vᵀ) := by
      rw [heq]; exact ⟨Pi.single j 1, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hmem
    refine ⟨c, ?_⟩
    rw [← hc]
    ext a
    simp [Matrix.mulVec, dotProduct, mul_comm]
  choose c hc using hcol
  refine ⟨Matrix.of fun i j => c j i, ?_⟩
  ext a j
  have := congrFun (hc j) a
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Pi.single_apply] using this

/-- The representation `g ↦ (ρ g⁻¹)ᵀ` (left invariants of `ρ` are its invariants). -/
def transRep (ρ : G →* Matrix M M 𝕜) : G →* Matrix M M 𝕜 where
  toFun g := (ρ g⁻¹)ᵀ
  map_one' := by simp
  map_mul' g h := by simp [mul_inv_rev, map_mul, Matrix.transpose_mul]

theorem repAvg_transRep (ρ : G →* Matrix M M 𝕜) : repAvg (transRep ρ) = (repAvg ρ)ᵀ := by
  unfold repAvg
  rw [Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) (fun g => (transRep ρ) g) (fun g => (ρ g)ᵀ)
    (fun g => rfl)

/-- **T7 (two-sided).** With `n` linearly independent right-invariant columns `V`, `n` linearly
independent left-invariant columns `W` (`(ρ g)ᵀ W = W`), and `n = tr R`, we get `R = V Λ Wᵀ`. -/
theorem repAvg_eq_mul_invariants_mul (ρ : G →* Matrix M M 𝕜) {n : ℕ}
    (V W : Matrix M (Fin n) 𝕜) (hV : ∀ g, ρ g * V = V) (hW : ∀ g, (ρ g)ᵀ * W = W)
    (hVli : LinearIndependent 𝕜 Vᵀ) (hWli : LinearIndependent 𝕜 Wᵀ)
    (hn : (n : 𝕜) = (repAvg ρ).trace) :
    ∃ Λ : Matrix (Fin n) (Fin n) 𝕜, repAvg ρ = V * Λ * Wᵀ := by
  obtain ⟨A, hA⟩ := repAvg_eq_mul_invariants ρ V hV hVli hn
  obtain ⟨B, hB⟩ := repAvg_eq_mul_invariants (transRep ρ) W
    (fun g => by simpa [transRep] using hW g⁻¹) hWli
    (by rw [repAvg_transRep, Matrix.trace_transpose]; exact hn)
  rw [repAvg_transRep] at hB
  have hB' : repAvg ρ = Bᵀ * Wᵀ := by
    rw [← Matrix.transpose_transpose (repAvg ρ), hB, Matrix.transpose_mul]
  refine ⟨A * Bᵀ, ?_⟩
  calc repAvg ρ = repAvg ρ * repAvg ρ := (repAvg_mul_self ρ).symm
    _ = (V * A) * (Bᵀ * Wᵀ) := by rw [← hA, ← hB']
    _ = V * (A * Bᵀ) * Wᵀ := by simp only [Matrix.mul_assoc]

/-- Linear independence of the columns of `V` from a nonzero `n × n` minor. -/
theorem linearIndependent_cols_of_det_ne_zero {m : Type*} [Fintype m] {n : ℕ}
    (V : Matrix m (Fin n) 𝕜) (piv : Fin n → m) (h : (V.submatrix piv id).det ≠ 0) :
    LinearIndependent 𝕜 Vᵀ := by
  refine Fintype.linearIndependent_iff.mpr ?_
  intro c hc
  have : (V.submatrix piv id) *ᵥ c = 0 := by
    ext j
    have := congrFun hc (piv j)
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero h this) i

/-- **T8 (finite check).** If `Wᵀ Y V = 0` then `R Y R = 0`. -/
theorem repAvg_mul_mul_repAvg_eq_zero (ρ : G →* Matrix M M 𝕜) {n : ℕ}
    (V W : Matrix M (Fin n) 𝕜) (hV : ∀ g, ρ g * V = V) (hW : ∀ g, (ρ g)ᵀ * W = W)
    (hVli : LinearIndependent 𝕜 Vᵀ) (hWli : LinearIndependent 𝕜 Wᵀ)
    (hn : (n : 𝕜) = (repAvg ρ).trace) (Y : Matrix M M 𝕜) (hY : Wᵀ * Y * V = 0) :
    repAvg ρ * Y * repAvg ρ = 0 := by
  obtain ⟨Λ, hΛ⟩ := repAvg_eq_mul_invariants_mul ρ V W hV hW hVli hWli hn
  rw [hΛ]
  calc V * Λ * Wᵀ * Y * (V * Λ * Wᵀ) = V * Λ * (Wᵀ * Y * V) * Λ * Wᵀ := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hY]; simp

/-- Invariance under generators gives invariance under the whole monoid. -/
theorem invariant_of_closure {H : Type*} [Monoid H] (φ : H →* Matrix M M 𝕜) (gens : Set H)
    (hg : Submonoid.closure gens = ⊤) {N : Type*} [Fintype N] (V : Matrix M N 𝕜)
    (h : ∀ s ∈ gens, φ s * V = V) : ∀ g, φ g * V = V := by
  let S : Submonoid H :=
    { carrier := {g | φ g * V = V}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        show φ (a * b) * V = V
        rw [map_mul, Matrix.mul_assoc]
        show φ a * (φ b * V) = V
        rw [show φ b * V = V from hb]
        exact ha }
  have : Submonoid.closure gens ≤ S := Submonoid.closure_le.mpr (fun s hs => h s hs)
  intro g
  have hgS : g ∈ S := this (by rw [hg]; trivial)
  exact hgS

/-- Left-invariance version of `invariant_of_closure`. -/
theorem left_invariant_of_closure {H : Type*} [Monoid H] (φ : H →* Matrix M M 𝕜) (gens : Set H)
    (hg : Submonoid.closure gens = ⊤) {N : Type*} [Fintype N] (W : Matrix M N 𝕜)
    (h : ∀ s ∈ gens, (φ s)ᵀ * W = W) : ∀ g, (φ g)ᵀ * W = W := by
  let S : Submonoid H :=
    { carrier := {g | (φ g)ᵀ * W = W}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        show (φ (a * b))ᵀ * W = W
        rw [map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
        show (φ b)ᵀ * ((φ a)ᵀ * W) = W
        rw [show (φ a)ᵀ * W = W from ha]
        exact hb }
  have : Submonoid.closure gens ≤ S := Submonoid.closure_le.mpr (fun s hs => h s hs)
  intro g
  have hgS : g ∈ S := this (by rw [hg]; trivial)
  exact hgS

end

end FormalResearch.FourQubitEntropy.QVBlock
