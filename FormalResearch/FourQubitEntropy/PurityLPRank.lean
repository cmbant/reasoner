import Mathlib

/-!
# Rank over `𝔽₂` by bitmask elimination (Stage 4 infrastructure)

A kernel-evaluable Gaussian elimination on rows stored as natural-number bitmasks, with a proof that it computes
`finrank_{𝔽₂}` of the row space.  Used (via `PurityLPGraph.lean`) to compute the ranks `rk_2 Γ[S,S^c]` of
`even_qubit_purity_minima.tex`, `thm:lptable`(2), `thm:fourteenfifteen`, `thm:sixteenseventeen`,
`thm:eighteen` for every balanced cut by `decide +kernel`.

* `toVec c r`: the first `c` bits of `r` as a vector in `𝔽₂^c`;
* `f2rank rows`: eliminate with pivot `= r.log2` (highest set bit): `rows ↦ rows.map (xor with pivot row where the
  pivot bit is set)`, one rank per non-zero pivot row;
* `f2rank_eq`: if every row is `< 2^c` then `f2rank rows = finrank (span (toVec c '' rows))`.
-/

open Module

namespace FormalResearch.FourQubitEntropy.PurityLP

/-- The first `c` bits of `r`, as a vector over `𝔽₂`. -/
def toVec (c r : ℕ) : Fin c → ZMod 2 := fun j => if r.testBit j then 1 else 0

theorem toVec_zero (c : ℕ) : toVec c 0 = 0 := by
  ext j; simp [toVec]

theorem toVec_xor (c r s : ℕ) : toVec c (r ^^^ s) = toVec c r + toVec c s := by
  ext j
  simp only [toVec, Nat.testBit_xor, Pi.add_apply]
  cases r.testBit j <;> cases s.testBit j <;> decide

/-- One elimination step: clear the pivot bit of `s` using the pivot row `r`. -/
def stepRow (r s : ℕ) : ℕ := if s.testBit r.log2 then s ^^^ r else s

/-- Gaussian elimination with fuel (structural recursion, kernel-reducible). -/
def rkF : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | f + 1, r :: rs => if r = 0 then rkF f rs else rkF f (rs.map (stepRow r)) + 1

/-- The `𝔽₂`-rank of a list of bitmask rows. -/
def f2rank (rows : List ℕ) : ℕ := rkF rows.length rows

/-- The row space of a list of bitmask rows inside `𝔽₂^c`. -/
def rowSpan (c : ℕ) (rows : List ℕ) : Submodule (ZMod 2) (Fin c → ZMod 2) :=
  Submodule.span (ZMod 2) {v | v ∈ rows.map (toVec c)}

theorem stepRow_lt {c r s : ℕ} (hr : r < 2 ^ c) (hs : s < 2 ^ c) : stepRow r s < 2 ^ c := by
  unfold stepRow
  split_ifs
  · exact Nat.xor_lt_two_pow hs hr
  · exact hs

theorem rowSpan_cons_zero (c : ℕ) (rs : List ℕ) : rowSpan c (0 :: rs) = rowSpan c rs := by
  unfold rowSpan
  simp only [List.map_cons, toVec_zero, List.mem_cons]
  rw [show {v | v = (0 : Fin c → ZMod 2) ∨ v ∈ rs.map (toVec c)}
    = insert 0 {v | v ∈ rs.map (toVec c)} from rfl]
  exact Submodule.span_insert_zero

theorem rowSpan_nil (c : ℕ) : rowSpan c [] = ⊥ := by
  unfold rowSpan; simp

theorem vec_add_self {c : ℕ} (v : Fin c → ZMod 2) : v + v = 0 := by
  ext j
  exact CharTwo.add_self_eq_zero (v j)

theorem mem_rowSpan (c : ℕ) {l : List ℕ} {s : ℕ} (hs : s ∈ l) : toVec c s ∈ rowSpan c l :=
  Submodule.subset_span (List.mem_map_of_mem hs)

theorem toVec_stepRow (c r s : ℕ) :
    toVec c (stepRow r s) = toVec c s ∨ toVec c (stepRow r s) = toVec c s + toVec c r := by
  unfold stepRow
  split_ifs
  · exact Or.inr (toVec_xor c s r)
  · exact Or.inl rfl

/-- Soundness of the elimination: `rkF` computes the dimension of the row space. -/
theorem rkF_eq (c : ℕ) : ∀ (f : ℕ) (rows : List ℕ), rows.length ≤ f → (∀ r ∈ rows, r < 2 ^ c) →
    rkF f rows = finrank (ZMod 2) (rowSpan c rows) := by
  intro f
  induction f with
  | zero =>
    intro rows hl _
    have : rows = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
    subst this
    show 0 = _
    rw [rowSpan_nil, finrank_bot]
  | succ f ih =>
    intro rows hl hb
    cases rows with
    | nil =>
      show 0 = _
      rw [rowSpan_nil, finrank_bot]
    | cons r rs =>
      have hl' : rs.length ≤ f := by simpa using hl
      have hbr : r < 2 ^ c := hb r (by simp)
      have hbs : ∀ s ∈ rs, s < 2 ^ c := fun s hs => hb s (by simp [hs])
      by_cases hr0 : r = 0
      · subst hr0
        rw [rowSpan_cons_zero]
        simp only [rkF, ite_true]
        exact ih rs hl' hbs
      · simp only [rkF, hr0, ite_false]
        have hl'' : (rs.map (stepRow r)).length ≤ f := by simpa using hl'
        have hb'' : ∀ s ∈ rs.map (stepRow r), s < 2 ^ c := by
          intro s hs
          obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
          exact stepRow_lt hbr (hbs s' hs')
        rw [ih _ hl'' hb'']
        have hp : r.log2 < c := (Nat.log2_lt hr0).mpr hbr
        have hr1 : r.testBit r.log2 = true := Nat.testBit_log2 hr0
        have hv0p : toVec c r ⟨r.log2, hp⟩ = 1 := by simp [toVec, hr1]
        have hTp : ∀ x ∈ rowSpan c (rs.map (stepRow r)), x ⟨r.log2, hp⟩ = 0 := by
          intro x hx
          have hle : rowSpan c (rs.map (stepRow r)) ≤
              LinearMap.ker (LinearMap.proj (⟨r.log2, hp⟩ : Fin c) :
                (Fin c → ZMod 2) →ₗ[ZMod 2] ZMod 2) := by
            apply Submodule.span_le.mpr
            intro y hy
            obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hy
            obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hu
            simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply]
            unfold stepRow toVec
            by_cases hsb : s.testBit r.log2
            · simp [hsb, Nat.testBit_xor, hr1]
            · simp [hsb]
          exact hle hx
        have hspan : rowSpan c (r :: rs) = rowSpan c (rs.map (stepRow r)) ⊔
            Submodule.span (ZMod 2) {toVec c r} := by
          apply le_antisymm
          · apply Submodule.span_le.mpr
            intro y hy
            simp only [List.map_cons, List.mem_cons] at hy
            rcases hy with rfl | hy
            · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
            · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
              have hm : toVec c (stepRow r s) ∈ rowSpan c (rs.map (stepRow r)) :=
                mem_rowSpan c (List.mem_map_of_mem hs)
              rcases toVec_stepRow c r s with h | h
              · exact Submodule.mem_sup_left (h ▸ hm)
              · have : toVec c s = toVec c (stepRow r s) + toVec c r := by
                  rw [h, add_assoc, vec_add_self, add_zero]
                rw [SetLike.mem_coe, this]
                exact Submodule.add_mem _ (Submodule.mem_sup_left hm)
                  (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
          · apply sup_le
            · apply Submodule.span_le.mpr
              intro y hy
              obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hy
              obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hu
              have h1 : toVec c s ∈ rowSpan c (r :: rs) := mem_rowSpan c (by simp [hs])
              have h2 : toVec c r ∈ rowSpan c (r :: rs) := mem_rowSpan c (by simp)
              rcases toVec_stepRow c r s with h | h
              · rw [SetLike.mem_coe, h]; exact h1
              · rw [SetLike.mem_coe, h]; exact Submodule.add_mem _ h1 h2
            · apply Submodule.span_le.mpr
              intro y hy
              rw [Set.mem_singleton_iff] at hy
              subst hy
              exact mem_rowSpan c (by simp)
        have hinf : rowSpan c (rs.map (stepRow r)) ⊓ Submodule.span (ZMod 2) {toVec c r} = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          obtain ⟨hx1, hx2⟩ := hx
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx2
          have h0 := hTp _ hx1
          simp only [Pi.smul_apply, hv0p, smul_eq_mul, mul_one] at h0
          rw [h0, zero_smul]
          exact Submodule.zero_mem _
        have hv0ne : toVec c r ≠ 0 := by
          intro h
          have := congrFun h ⟨r.log2, hp⟩
          rw [hv0p] at this
          exact one_ne_zero this
        have := Submodule.finrank_sup_add_finrank_inf_eq (rowSpan c (rs.map (stepRow r)))
          (Submodule.span (ZMod 2) {toVec c r})
        rw [hinf, finrank_bot, finrank_span_singleton hv0ne, ← hspan] at this
        omega

theorem f2rank_eq (c : ℕ) (rows : List ℕ) (hb : ∀ r ∈ rows, r < 2 ^ c) :
    f2rank rows = finrank (ZMod 2) (rowSpan c rows) :=
  rkF_eq c rows.length rows le_rfl hb

end FormalResearch.FourQubitEntropy.PurityLP
