module

public import FormalResearch.NQubit.Graph.MeanPurity

/-!
# Symmetry reduction of cut-rank sums

A sum `Σ_{|S| = k} F(rk_2 Γ[S,S^c])` over all `k`-subsets of the vertices of a graph `Γ` with a group `G` of automorphisms
is the sum over orbit representatives weighted by the orbit sizes.  The module proves this with a *cheap, data-light
certificate*, so that a kernel check needs only the cut ranks of the representatives.

* `graphCutRank_image`, `graphCutBits_image`: for an automorphism `σ` (`Γ (σ i) (σ j) = Γ i j`),
  `rk_2 Γ[σ S, (σ S)^c] = rk_2 Γ[S, S^c]`.
* Masks: `cutMask S` is the bitmask of `S`, `unmask n m` its inverse, `maskCard`, and
  `imageMask n q m` the mask of the image of `m` under a permutation whose *inverse* is the list `q`.
* The group is `Subgroup.closure gens` for a list `gens` of permutations of `Fin n`; its elements are listed (as the
  lists `q = lst g⁻¹`) along a derivation `D` (`derivQ`; every listed element is a word in the generators, `goQ_sound`)
  and the list is closed under the generator lists (so it is the whole group, `closure_mem_Q`).
* `sum_rankFn_eq_reps`: for representatives `R = [(m_r, w_r)]` (masks in increasing order, each the minimum of its orbit,
  checked by `repOK`; `w_r` the orbit size, `Σ w_r = C(n,k)`), `Σ_{|S| = k} F(S) = Σ_r w_r F(unmask m_r)` for every
  automorphism-invariant `F` of the form `g ∘ graphCutRankBits`.

Everything here is general and carries no data; the data-specific checks are `decide +kernel` calls in the users.
-/

@[expose] public section

open scoped BigOperators

namespace FormalResearch.NQubit.Graph

variable {n : ℕ}

/-! ### Cut rank under automorphisms -/

theorem graphCutRank_image (Γ : Fin n → Fin n → Bool) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i j, Γ (σ i) (σ j) = Γ i j) (S : Finset (Fin n)) :
    graphCutRank Γ (S.image σ) = graphCutRank Γ S := by
  unfold graphCutRank
  let e1 : {i // i ∈ S} ≃ {i // i ∈ S.image σ} :=
    Equiv.subtypeEquiv σ (fun a => by simp)
  let e2 : {j // j ∉ S} ≃ {j // j ∉ S.image σ} :=
    Equiv.subtypeEquiv σ (fun a => by simp)
  have h : cutMat Γ (S.image σ) = (cutMat Γ S).submatrix e1.symm e2.symm := by
    ext i j
    simp only [cutMat, Matrix.submatrix_apply]
    have := hσ (e1.symm i) (e2.symm j)
    have h1 : σ (e1.symm i) = i.1 := by
      have := e1.apply_symm_apply i
      exact congrArg Subtype.val this
    have h2 : σ (e2.symm j) = j.1 := by
      have := e2.apply_symm_apply j
      exact congrArg Subtype.val this
    rw [h1, h2] at this
    rw [this]
  rw [h]
  exact Matrix.rank_submatrix _ _ _

theorem graphCutBits_image (adj : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i j, (adj (σ i)).testBit (σ j) = (adj i).testBit j) (S : Finset (Fin n)) :
    graphCutRankBits adj (S.image σ) = graphCutRankBits adj S := by
  rw [← graphCutRank_eq_bits, ← graphCutRank_eq_bits]
  exact graphCutRank_image _ σ hσ S

/-- The automorphisms of the graph with neighbourhood bitmasks `adj` form a subgroup of `Perm (Fin n)`. -/
def autGroup (adj : Fin n → ℕ) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ i j, (adj (σ i)).testBit (σ j) = (adj i).testBit j}
  mul_mem' := by
    intro a b ha hb i j
    simp only [Set.mem_ofPred_eq, Equiv.Perm.coe_mul, Function.comp] at *
    rw [ha, hb]
  one_mem' := by intro i j; rfl
  inv_mem' := by
    intro a ha i j
    simp only [Set.mem_ofPred_eq] at *
    rw [← ha (a⁻¹ i) (a⁻¹ j)]
    simp

/-! ### Bitmasks of cuts -/

/-- The bitmask of a set of positions. -/
def cutMask (S : Finset (Fin n)) : ℕ := ofBitsL ((List.finRange n).map fun j => decide (j ∈ S))

theorem testBit_cutMask (S : Finset (Fin n)) (j : Fin n) : (cutMask S).testBit j = decide (j ∈ S) := by
  unfold cutMask
  rw [testBit_ofBitsL]
  simp [List.getD_eq_getElem?_getD]

theorem testBit_cutMask_ge (S : Finset (Fin n)) {j : ℕ} (hj : n ≤ j) : (cutMask S).testBit j = false := by
  unfold cutMask
  rw [testBit_ofBitsL]
  simp [List.getD_eq_getElem?_getD, hj]

theorem cutMask_injective : Function.Injective (cutMask (n := n)) := by
  intro S S' h
  ext j
  have := congrArg (fun m => m.testBit j) h
  simp only [testBit_cutMask, decide_eq_decide] at this
  exact this

/-- The set of positions `< n` with bit set in `m`. -/
def unmask (n m : ℕ) : Finset (Fin n) := Finset.univ.filter fun j => m.testBit j

theorem mem_unmask (m : ℕ) (j : Fin n) : j ∈ unmask n m ↔ m.testBit j = true := by
  simp [unmask]

theorem cutMask_unmask (m : ℕ) (hm : m < 2 ^ n) : cutMask (unmask n m) = m := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · have := testBit_cutMask (unmask n m) ⟨j, hj⟩
    simp only at this
    rw [this]
    by_cases h : m.testBit j = true <;> simp [mem_unmask, h]
  · rw [testBit_cutMask_ge _ (not_lt.mp hj)]
    symm
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hj)))

/-- The number of bits `< n` set in `m`. -/
def maskCard (n m : ℕ) : ℕ := ((List.finRange n).filter fun j : Fin n => m.testBit j.1).length

theorem card_unmask (m : ℕ) : (unmask n m).card = maskCard n m := by
  unfold unmask maskCard
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext j; simp

theorem unmask_cutMask (S : Finset (Fin n)) : unmask n (cutMask S) = S := by
  ext j
  simp [mem_unmask, testBit_cutMask]

/-- The mask of the image of a mask: bit `j` of the result is bit `q j` of `m`
(`q` lists the inverse of the permutation, see `cutMask_image`). -/
def imageMask (n : ℕ) (q : List ℕ) (m : ℕ) : ℕ :=
  ofBitsL ((List.range n).map fun j => m.testBit (q.getD j 0))

/-- The list `[σ 0, …, σ (n-1)]`. -/
def lst (σ : Equiv.Perm (Fin n)) : List ℕ := (List.finRange n).map fun i => (σ i : ℕ)

theorem lst_getD (σ : Equiv.Perm (Fin n)) (i : Fin n) : (lst σ).getD i 0 = σ i := by
  simp [lst, List.getD_eq_getElem?_getD]

theorem lst_one : lst (1 : Equiv.Perm (Fin n)) = List.range n := by
  unfold lst
  simp only [Equiv.Perm.coe_one, id_eq]
  exact List.map_coe_finRange_eq_range

theorem cutMask_image (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    cutMask (S.image σ) = imageMask n (lst σ⁻¹) (cutMask S) := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · have h1 := testBit_cutMask (S.image σ) ⟨j, hj⟩
    simp only at h1
    rw [h1]
    unfold imageMask
    rw [testBit_ofBitsL]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hj,
      Option.map_some, Option.getD_some]
    have h2 := lst_getD σ⁻¹ ⟨j, hj⟩
    simp only [List.getD_eq_getElem?_getD] at h2
    rw [h2, testBit_cutMask]
    simp only [Finset.mem_image, decide_eq_decide]
    constructor
    · rintro ⟨a, ha, h⟩
      have : σ⁻¹ ⟨j, hj⟩ = a := by rw [← h]; simp
      rw [this]; exact ha
    · intro h
      exact ⟨_, h, by simp⟩
  · rw [testBit_cutMask_ge _ (not_lt.mp hj)]
    unfold imageMask
    rw [testBit_ofBitsL]
    simp [List.getD_eq_getElem?_getD, hj]

/-! ### Lists of group elements -/

/-- Composition of permutation lists: `(q ∘ p) i = q (p i)`. -/
def compL (q p : List ℕ) : List ℕ := p.map fun i => q.getD i 0

theorem lst_mul (σ τ : Equiv.Perm (Fin n)) : lst (σ * τ) = compL (lst σ) (lst τ) := by
  unfold compL lst
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  simp [List.getD_eq_getElem?_getD]

theorem lst_length (σ : Equiv.Perm (Fin n)) : (lst σ).length = n := by simp [lst]

theorem lst_lt (σ : Equiv.Perm (Fin n)) : ∀ x ∈ lst σ, x < n := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact (σ i).2

theorem lst_injective : Function.Injective (lst (n := n)) := by
  intro σ τ h
  ext i
  have := congrArg (fun l => l.getD i 0) h
  simp only [lst_getD] at this
  exact this

/-- The right multipliers of the group generated by `gens`: `lst x` and `lst x⁻¹`. -/
def genLists (gens : List (Equiv.Perm (Fin n))) : List (List ℕ) := gens.flatMap fun x => [lst x, lst x⁻¹]

theorem genLists_mem {gens : List (Equiv.Perm (Fin n))} {gl : List ℕ} (h : gl ∈ genLists gens) :
    ∃ x ∈ Subgroup.closure {x | x ∈ gens}, gl = lst x ∨ gl = lst x⁻¹ := by
  unfold genLists at h
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨x, hx, h⟩ := h
  exact ⟨x, Subgroup.subset_closure hx, h⟩

theorem genLists_valid {gens : List (Equiv.Perm (Fin n))} {gl : List ℕ} (h : gl ∈ genLists gens) :
    gl.length = n ∧ ∀ x ∈ gl, x < n := by
  obtain ⟨x, _, rfl | rfl⟩ := genLists_mem h
  · exact ⟨lst_length x, lst_lt x⟩
  · exact ⟨lst_length x⁻¹, lst_lt x⁻¹⟩

/-- Completeness: if `Q` contains the identity and is closed under right composition with the generator lists, it contains
`lst g⁻¹` for every `g` of the group. -/
theorem closure_mem_Q (gens : List (Equiv.Perm (Fin n))) (Q : List (List ℕ)) (hid : List.range n ∈ Q)
    (hcl : ∀ q ∈ Q, ∀ gl ∈ genLists gens, compL q gl ∈ Q) :
    ∀ g ∈ Subgroup.closure {x | x ∈ gens}, lst g⁻¹ ∈ Q := by
  intro g hg
  induction hg using Subgroup.closure_induction_left with
  | one => simpa [lst_one] using hid
  | mul_left x hx y hy ih =>
    have : lst (x * y)⁻¹ = compL (lst y⁻¹) (lst x⁻¹) := by rw [mul_inv_rev, lst_mul]
    rw [this]
    exact hcl _ ih _ (by unfold genLists; simp only [List.mem_flatMap]; exact ⟨x, hx, by simp⟩)
  | inv_mul_cancel x hx y hy ih =>
    have : lst (x⁻¹ * y)⁻¹ = compL (lst y⁻¹) (lst x) := by rw [mul_inv_rev, inv_inv, lst_mul]
    rw [this]
    exact hcl _ ih _ (by unfold genLists; simp only [List.mem_flatMap]; exact ⟨x, hx, by simp⟩)

/-! ### Images of masks -/

theorem testBit_imageMask (q : List ℕ) (m j : ℕ) :
    (imageMask n q m).testBit j = (decide (j < n) && m.testBit (q.getD j 0)) := by
  unfold imageMask
  rw [testBit_ofBitsL]
  by_cases hj : j < n
  · simp [List.getD_eq_getElem?_getD, hj]
  · simp [List.getD_eq_getElem?_getD, hj]

theorem imageMask_lt (q : List ℕ) (m : ℕ) : imageMask n q m < 2 ^ n := by
  unfold imageMask
  have h := ofBitsL_lt ((List.range n).map fun j => m.testBit (q.getD j 0))
  rwa [List.length_map, List.length_range] at h

theorem imageMask_range (m : ℕ) (hm : m < 2 ^ n) : imageMask n (List.range n) m = m := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_imageMask]
  by_cases hj : j < n
  · simp [hj, List.getD_eq_getElem?_getD]
  · have : m.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hj)))
    simp [hj, this]

/-- Applying `gl` after `d`. -/
theorem imageMask_compL (d gl : List ℕ) (hlen : gl.length = n) (hlt : ∀ x ∈ gl, x < n) (m : ℕ) :
    imageMask n (compL d gl) m = imageMask n gl (imageMask n d m) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_imageMask, testBit_imageMask]
  by_cases hj : j < n
  · have hjl : j < gl.length := hlen ▸ hj
    have hgj : gl.getD j 0 < n := hlt _ (by simp [List.getD_eq_getElem?_getD, hjl])
    rw [testBit_imageMask]
    simp only [hj, hgj, decide_true, Bool.true_and]
    simp [compL, List.getD_eq_getElem?_getD, hjl]
  · simp [hj]

/-- Cyclic rotation list: position `j` takes the value of `j + s`. -/
def rotList (n s : ℕ) : List ℕ := (List.range n).map fun j => (j + s) % n

/-- The same rotation on masks, by shifts. -/
def rotM (n s m : ℕ) : ℕ := ((m >>> s) ||| (m <<< (n - s))) &&& (2 ^ n - 1)

theorem rotM_lt (n s m : ℕ) : rotM n s m < 2 ^ n := by
  unfold rotM
  exact lt_of_le_of_lt (Nat.and_le_right) (Nat.sub_lt (Nat.two_pow_pos n) one_pos)

theorem rotM_eq (s m : ℕ) (hs : s < n) (hm : m < 2 ^ n) : rotM n s m = imageMask n (rotList n s) m := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_imageMask]
  unfold rotM
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < n
  · have hbig : ∀ i, n ≤ i → m.testBit i = false := fun i hi =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hi))
    have hr : (rotList n s).getD j 0 = (j + s) % n := by
      simp [rotList, List.getD_eq_getElem?_getD, hj]
    rw [hr]
    by_cases h1 : j + s < n
    · rw [Nat.mod_eq_of_lt h1]
      have : ¬ (n - s ≤ j) := by omega
      simp [hj, this, add_comm]
    · have h2 : (j + s) % n = j + s - n := by
        have : j + s < 2 * n := by omega
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [h2, hbig (s + j) (by omega)]
      have : n - s ≤ j := by omega
      have h3 : j - (n - s) = j + s - n := by omega
      simp [hj, this, h3]
  · simp [hj]

/-- The image of a mask under a generator list: shifts for rotations (`s ≠ 0`), the general list otherwise. -/
def genImg (n : ℕ) (gl : List ℕ) (s y : ℕ) : ℕ := if s = 0 then imageMask n gl y else rotM n s y

theorem genImg_eq (gl : List ℕ) (s y : ℕ) (hs : s < n) (hr : s = 0 ∨ gl = rotList n s) (hy : y < 2 ^ n) :
    genImg n gl s y = imageMask n gl y := by
  unfold genImg
  by_cases h0 : s = 0
  · simp [h0]
  · rw [show (if s = 0 then imageMask n gl y else rotM n s y) = rotM n s y from by simp [h0], rotM_eq s y hs hy]
    rcases hr with h | h
    · exact absurd h h0
    · rw [h]

/-! ### Derivations of the group elements and of the images of a mask

`D` lists the elements of the group (after the identity): the entry `(fromRoot, g)` is the right composition of the identity
(`fromRoot`) or of the previous element with the `g`-th generator list `GLs[g]`.  The images of a mask `m` are computed along
the same derivation, with cheap shifts for rotation generators (`GS[g] ≠ 0`). -/

/-- The elements of the group, as lists, along the derivation `D`. -/
def goQ (GLs : List (List ℕ)) : List (Bool × ℕ) → List ℕ → List ℕ → List (List ℕ)
  | [], _, _ => []
  | (fr, g) :: D, root, prev =>
      let q := compL (if fr then root else prev) (GLs.getD g [])
      q :: goQ GLs D root q

/-- `[id, …]`: the group elements derived by `D`. -/
def derivQ (n : ℕ) (GLs : List (List ℕ)) (D : List (Bool × ℕ)) : List (List ℕ) :=
  List.range n :: goQ GLs D (List.range n) (List.range n)

/-- The images of the mask `y₀ = m` under these elements, computed along the derivation. -/
def goI (n : ℕ) (GLs : List (List ℕ)) (GS : List ℕ) : List (Bool × ℕ) → ℕ → ℕ → List ℕ
  | [], _, _ => []
  | (fr, g) :: D, root, prev =>
      let x := genImg n (GLs.getD g []) (GS.getD g 0) (if fr then root else prev)
      x :: goI n GLs GS D root x

def imgs (n : ℕ) (GLs : List (List ℕ)) (GS : List ℕ) (D : List (Bool × ℕ)) (m : ℕ) : List ℕ :=
  m :: goI n GLs GS D m m

theorem goQ_sound (gens : List (Equiv.Perm (Fin n))) (GLs : List (List ℕ)) (hGL : GLs = genLists gens)
    (D : List (Bool × ℕ)) (hD : ∀ e ∈ D, e.2 < GLs.length) :
    ∀ (root prev : List ℕ), (∃ g ∈ Subgroup.closure {x | x ∈ gens}, root = lst g⁻¹) →
      (∃ g ∈ Subgroup.closure {x | x ∈ gens}, prev = lst g⁻¹) →
      ∀ q ∈ goQ GLs D root prev, ∃ g ∈ Subgroup.closure {x | x ∈ gens}, q = lst g⁻¹ := by
  subst hGL
  induction D with
  | nil => intro _ _ _ _ q hq; simp [goQ] at hq
  | cons e D ih =>
    obtain ⟨fr, g⟩ := e
    intro root prev hroot hprev q hq
    simp only [goQ, List.mem_cons] at hq
    have hmem : (genLists gens).getD g [] ∈ genLists gens := by
      have := hD (fr, g) (by simp)
      simp only at this
      simp [List.getD_eq_getElem?_getD, this]
    have hq0 : ∃ g' ∈ Subgroup.closure {x | x ∈ gens},
        compL (if fr then root else prev) ((genLists gens).getD g []) = lst g'⁻¹ := by
      have hpar : ∃ g0 ∈ Subgroup.closure {x | x ∈ gens}, (if fr then root else prev) = lst g0⁻¹ := by
        split_ifs
        · exact hroot
        · exact hprev
      obtain ⟨g0, hg0, hp⟩ := hpar
      obtain ⟨x, hx, hgl⟩ := genLists_mem hmem
      rw [hp]
      rcases hgl with h | h
      · refine ⟨x⁻¹ * g0, Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hg0, ?_⟩
        rw [h, mul_inv_rev, inv_inv, lst_mul]
      · refine ⟨x * g0, Subgroup.mul_mem _ hx hg0, ?_⟩
        rw [h, mul_inv_rev, lst_mul]
    rcases hq with rfl | hq
    · exact hq0
    · exact ih (fun e he => hD e (List.mem_cons_of_mem _ he)) root _ hroot hq0 q hq

theorem goI_eq (gens : List (Equiv.Perm (Fin n))) (GLs : List (List ℕ)) (hGL : GLs = genLists gens) (GS : List ℕ)
    (hGS : ∀ j < GLs.length, GS.getD j 0 < n ∧ (GS.getD j 0 = 0 ∨ GLs.getD j [] = rotList n (GS.getD j 0)))
    (D : List (Bool × ℕ)) (hD : ∀ e ∈ D, e.2 < GLs.length) (m : ℕ) :
    ∀ (rootq prevq : List ℕ) (root prev : ℕ), root = imageMask n rootq m → prev = imageMask n prevq m →
      goI n GLs GS D root prev = (goQ GLs D rootq prevq).map fun q => imageMask n q m := by
  subst hGL
  induction D with
  | nil => intros; simp [goI, goQ]
  | cons e D ih =>
    obtain ⟨fr, g⟩ := e
    intro rootq prevq root prev hroot hprev
    have hg : g < (genLists gens).length := hD (fr, g) (by simp)
    have hmem : (genLists gens).getD g [] ∈ genLists gens := by simp [List.getD_eq_getElem?_getD, hg]
    obtain ⟨hlen, hlt⟩ := genLists_valid hmem
    obtain ⟨hs, hr⟩ := hGS g hg
    have hpar : (if fr then root else prev) = imageMask n (if fr then rootq else prevq) m := by
      split_ifs
      · exact hroot
      · exact hprev
    have hx : genImg n ((genLists gens).getD g []) (GS.getD g 0) (if fr then root else prev)
        = imageMask n (compL (if fr then rootq else prevq) ((genLists gens).getD g [])) m := by
      rw [imageMask_compL _ _ hlen hlt, genImg_eq _ _ _ hs hr, hpar]
      rw [hpar]; exact imageMask_lt _ _
    simp only [goI, goQ, List.map_cons]
    rw [hx]
    congr 1
    exact ih (fun e he => hD e (List.mem_cons_of_mem _ he)) rootq _ root _ hroot rfl

theorem imgs_eq (gens : List (Equiv.Perm (Fin n))) (GLs : List (List ℕ)) (hGL : GLs = genLists gens) (GS : List ℕ)
    (hGS : ∀ j < GLs.length, GS.getD j 0 < n ∧ (GS.getD j 0 = 0 ∨ GLs.getD j [] = rotList n (GS.getD j 0)))
    (D : List (Bool × ℕ)) (hD : ∀ e ∈ D, e.2 < GLs.length) (m : ℕ) (hm : m < 2 ^ n) :
    imgs n GLs GS D m = (derivQ n GLs D).map fun q => imageMask n q m := by
  unfold imgs derivQ
  rw [List.map_cons, imageMask_range m hm]
  congr 1
  exact goI_eq gens GLs hGL GS hGS D hD m _ _ m m (imageMask_range m hm).symm (imageMask_range m hm).symm

/-! ### Counting over orbit representatives -/

theorem sum_eq_sum_reps {X M : Type*} [DecidableEq X] [AddCommMonoid M] (T : Finset X) (E : X → X → Prop)
    [DecidableRel E] (hsymm : ∀ x y, E x y → E y x) (htrans : ∀ x y z, E x y → E y z → E x z)
    (f : X → M) (hf : ∀ x y, E x y → f x = f y) (R : Finset X)
    (hdisj : ∀ r ∈ R, ∀ r' ∈ R, E r r' → r = r')
    (hcount : ∑ r ∈ R, (T.filter (E r)).card = T.card) :
    ∑ x ∈ T, f x = ∑ r ∈ R, (T.filter (E r)).card • f r := by
  have hpd : (↑R : Set X).PairwiseDisjoint (fun r => T.filter (E r)) := by
    intro r hr r' hr' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_filter] at hx hx'
    exact hne (hdisj r hr r' hr' (htrans _ _ _ hx.2 (hsymm _ _ hx'.2)))
  have hsub : R.biUnion (fun r => T.filter (E r)) ⊆ T := by
    intro x hx
    obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hr).1
  have heq : R.biUnion (fun r => T.filter (E r)) = T :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_biUnion hpd]; exact hcount.ge)
  calc ∑ x ∈ T, f x = ∑ x ∈ R.biUnion (fun r => T.filter (E r)), f x := by rw [heq]
    _ = _ := by
      rw [Finset.sum_biUnion hpd]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_const]
      refine Finset.sum_congr rfl fun x hx => ?_
      exact (hf r x (Finset.mem_filter.mp hx).2).symm

section Reps

variable (gens : List (Equiv.Perm (Fin n)))

/-- The orbit relation of the group generated by `gens` on subsets. -/
def OrbRel (S S' : Finset (Fin n)) : Prop :=
  ∃ g ∈ Subgroup.closure {x | x ∈ gens}, S' = S.image g

theorem orbRel_symm (S S' : Finset (Fin n)) (h : OrbRel gens S S') : OrbRel gens S' S := by
  obtain ⟨g, hg, rfl⟩ := h
  refine ⟨g⁻¹, Subgroup.inv_mem _ hg, ?_⟩
  rw [Finset.image_image]
  simp

theorem orbRel_trans (S S' S'' : Finset (Fin n)) (h : OrbRel gens S S') (h' : OrbRel gens S' S'') :
    OrbRel gens S S'' := by
  obtain ⟨g, hg, rfl⟩ := h
  obtain ⟨g', hg', rfl⟩ := h'
  refine ⟨g' * g, Subgroup.mul_mem _ hg' hg, ?_⟩
  rw [Finset.image_image]
  rfl

/-- Invariance under the group generated by automorphisms. -/
theorem rankFn_orbRel (adj : Fin n → ℕ) (hgens : ∀ x ∈ gens, ∀ i j, (adj (x i)).testBit (x j) = (adj i).testBit j)
    (g : ℕ → ℕ) (S S' : Finset (Fin n)) (h : OrbRel gens S S') :
    g (graphCutRankBits adj S) = g (graphCutRankBits adj S') := by
  obtain ⟨σ, hσ, rfl⟩ := h
  have hle : Subgroup.closure {x | x ∈ gens} ≤ autGroup adj :=
    (Subgroup.closure_le _).mpr fun x hx => hgens x hx
  rw [graphCutBits_image adj σ (hle hσ)]

theorem image_mul (a b : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : S.image (a * b) = (S.image b).image a := by
  rw [Finset.image_image]; rfl

open Classical in
/-- **Orbit–stabiliser** in list form: if `Q` lists the (inverses of the) elements of the group once each, then the orbit
of `S` has `|Q| / #{q ∈ Q : q fixes S}` elements. -/
theorem orbit_card_mul (T : Finset (Finset (Fin n))) (hT : ∀ S ∈ T, ∀ g : Equiv.Perm (Fin n), S.image g ∈ T)
    (Q : List (List ℕ)) (hnd : Q.Nodup)
    (hsound : ∀ q ∈ Q, ∃ g ∈ Subgroup.closure {x | x ∈ gens}, q = lst g⁻¹)
    (hcomplete : ∀ g ∈ Subgroup.closure {x | x ∈ gens}, lst g⁻¹ ∈ Q) (S : Finset (Fin n)) (hS : S ∈ T) :
    (T.filter (OrbRel gens S)).card *
      (Q.filter fun q => imageMask n q (cutMask S) == cutMask S).length = Q.length := by
  classical
  set G := Subgroup.closure {x | x ∈ gens} with hG
  set Gf : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter (· ∈ G) with hGf
  set ψ : Equiv.Perm (Fin n) → List ℕ := fun g => lst g⁻¹ with hψ
  have hψinj : Function.Injective ψ := fun a b h => inv_injective (lst_injective h)
  have hQ : Q.toFinset = Gf.image ψ := by
    ext q
    simp only [List.mem_toFinset, Finset.mem_image, hGf, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hq
      obtain ⟨g, hg, rfl⟩ := hsound q hq
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact hcomplete g hg
  have hQlen : Q.length = Gf.card := by
    rw [← List.toFinset_card_of_nodup hnd, hQ, Finset.card_image_of_injective _ hψinj]
  set Stab : Finset (Equiv.Perm (Fin n)) := Gf.filter (fun g : Equiv.Perm (Fin n) => S.image (g : Fin n → Fin n) = S) with hStab
  have hcnt : (Q.filter fun q => imageMask n q (cutMask S) == cutMask S).length = Stab.card := by
    rw [← List.toFinset_card_of_nodup (hnd.filter _)]
    have : (Q.filter fun q => imageMask n q (cutMask S) == cutMask S).toFinset = Stab.image ψ := by
      ext q
      simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq, Finset.mem_image, hStab, Finset.mem_filter]
      constructor
      · rintro ⟨hq, hq2⟩
        obtain ⟨g, hg, rfl⟩ := hsound q hq
        refine ⟨g, ⟨by simpa [hGf] using hg, ?_⟩, rfl⟩
        have : cutMask (S.image g) = cutMask S := by rw [cutMask_image]; exact hq2
        exact cutMask_injective this
      · rintro ⟨g, ⟨hg, hg2⟩, rfl⟩
        refine ⟨hcomplete g (by simpa [hGf] using hg), ?_⟩
        rw [← cutMask_image, hg2]
    rw [this, Finset.card_image_of_injective _ hψinj]
  set cls : Finset (Finset (Fin n)) :=
    Gf.image (fun g : Equiv.Perm (Fin n) => S.image (g : Fin n → Fin n)) with hclsdef
  have hcls : T.filter (OrbRel gens S) = cls := by
    ext S'
    simp only [Finset.mem_filter, hclsdef, Finset.mem_image, hGf, Finset.mem_univ, true_and, OrbRel]
    constructor
    · rintro ⟨_, g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨hT S hS g, g, hg, rfl⟩
  have hfib : ∀ b ∈ cls, (Gf.filter fun g : Equiv.Perm (Fin n) => S.image (g : Fin n → Fin n) = b).card = Stab.card := by
    intro b hb
    obtain ⟨g1, hg1, rfl⟩ := Finset.mem_image.mp hb
    have hg1G : g1 ∈ G := by simpa [hGf] using hg1
    refine Finset.card_nbij' (fun g => g1⁻¹ * g) (fun h => g1 * h) ?_ ?_ ?_ ?_
    · intro g hg
      simp only [Finset.mem_coe, Finset.mem_filter, hGf, Finset.mem_univ, true_and] at hg
      simp only [Finset.mem_coe, hStab, Finset.mem_filter, hGf, Finset.mem_univ, true_and]
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hg1G) hg.1, ?_⟩
      rw [image_mul, hg.2, ← image_mul]
      simp
    · intro h hh
      simp only [Finset.mem_coe, hStab, Finset.mem_filter, hGf, Finset.mem_univ, true_and] at hh
      simp only [Finset.mem_coe, Finset.mem_filter, hGf, Finset.mem_univ, true_and]
      refine ⟨Subgroup.mul_mem _ hg1G hh.1, ?_⟩
      rw [image_mul, hh.2]
    · intro g _; simp
    · intro h _; simp
  have hsum : Gf.card = cls.card * Stab.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Equiv.Perm (Fin n) => S.image (g : Fin n → Fin n)) (t := cls)
      (fun g hg => by rw [hclsdef]; exact Finset.mem_image_of_mem _ (by simpa using hg))]
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  rw [hcls, hcnt, hQlen, hsum]

/-- One pass over the images `xs` of a mask `m`: are they all `≥ m`, and how many equal `m`? -/
def scanImgs (m : ℕ) : List ℕ → Bool × ℕ
  | [] => (true, 0)
  | x :: xs =>
    match scanImgs m xs with
    | (b, c) => (decide (m ≤ x) && b, (if x == m then 1 else 0) + c)

theorem scanImgs_eq (m : ℕ) (xs : List ℕ) :
    scanImgs m xs = (xs.all fun x => decide (m ≤ x), xs.countP fun x => x == m) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [scanImgs, ih, List.all_cons, List.countP_cons]
    congr 1
    omega

/-- The kernel check of one orbit representative `(m, w)`: `m < 2^n`, `|m| = k`, `m` is the least image of itself, and
`w · #{stabiliser} = |G|`. -/
def repOK (n k : ℕ) (GLs : List (List ℕ)) (GS : List ℕ) (D : List (Bool × ℕ)) (p : ℕ × ℕ) : Bool :=
  match scanImgs p.1 (imgs n GLs GS D p.1) with
  | (b, c) => decide (p.1 < 2 ^ n) && decide (maskCard n p.1 = k) && b && (c * p.2 == D.length + 1)

/-- Strictly increasing first components (a linear scan, evaluated by the kernel without deep recursion). -/
def incrB : List (ℕ × ℕ) → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => decide (a.1 < b.1) && incrB (b :: l)

theorem incrB_pairwise : ∀ l : List (ℕ × ℕ), incrB l = true → l.Pairwise (fun a b : ℕ × ℕ => a.1 < b.1) := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons a l ih =>
    intro h
    cases l with
    | nil => exact List.pairwise_singleton _ _
    | cons b l =>
      simp only [incrB, Bool.and_eq_true, decide_eq_true_eq] at h
      have hb := ih h.2
      refine List.Pairwise.cons ?_ hb
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1
      · exact lt_trans h.1 (List.rel_of_pairwise_cons hb hx)

theorem length_goQ (GLs : List (List ℕ)) (D : List (Bool × ℕ)) :
    ∀ r q : List ℕ, (goQ GLs D r q).length = D.length := by
  induction D with
  | nil => intros; rfl
  | cons e D ih => intro r q; obtain ⟨fr, g⟩ := e; simp [goQ, ih]

/-- **Orbit-representative sum.**  `GLs = genLists gens` are the generator lists, `D` a derivation listing the elements of
the group (`Q = derivQ n GLs D`, each once, closed under the generators), `GS` the rotation shifts of the generator lists.
Each representative `(m, w)` of `R` is the minimum of the images of `m`, `w` is its orbit size (`|Q|` over the number of
group elements fixing `m`), the masks increase and the sizes add up to `C(n,k)`.  Then the sum over all `k`-subsets of
an automorphism-invariant function is the weighted sum over the representatives. -/
theorem sum_rankFn_eq_reps (adj : Fin n → ℕ)
    (hgens : ∀ x ∈ gens, ∀ i j, (adj (x i)).testBit (x j) = (adj i).testBit j)
    (g : ℕ → ℕ) (k : ℕ) (GLs : List (List ℕ)) (hGL : GLs = genLists gens) (GS : List ℕ)
    (hGS : ∀ j < GLs.length, GS.getD j 0 < n ∧ (GS.getD j 0 = 0 ∨ GLs.getD j [] = rotList n (GS.getD j 0)))
    (D : List (Bool × ℕ)) (hD : ∀ e ∈ D, e.2 < GLs.length) (Q : List (List ℕ)) (hQ : Q = derivQ n GLs D)
    (hnd : Q.Nodup) (hclosed : ∀ q ∈ Q, ∀ gl ∈ GLs, compL q gl ∈ Q)
    (R : List (ℕ × ℕ)) (hlt : incrB R = true)
    (hR : R.all (repOK n k GLs GS D) = true)
    (hsum : (R.map Prod.snd).sum = Nat.choose n k) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, g (graphCutRankBits adj S)
      = (R.map fun p => p.2 * g (graphCutRankBits adj (unmask n p.1))).sum := by
  classical
  have hQlen : Q.length = D.length + 1 := by
    rw [hQ]; simp [derivQ, length_goQ]
  have hsound : ∀ q ∈ Q, ∃ x ∈ Subgroup.closure {x | x ∈ gens}, q = lst x⁻¹ := by
    intro q hq
    rw [hQ] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨1, Subgroup.one_mem _, by simp [lst_one]⟩
    · exact goQ_sound gens GLs hGL D hD (List.range n) (List.range n)
        ⟨1, Subgroup.one_mem _, by simp [lst_one]⟩ ⟨1, Subgroup.one_mem _, by simp [lst_one]⟩ q hq
  have hcomplete : ∀ x ∈ Subgroup.closure {x | x ∈ gens}, lst x⁻¹ ∈ Q := by
    refine closure_mem_Q gens Q (by rw [hQ]; exact List.mem_cons_self) ?_
    intro q hq gl hgl
    exact hclosed q hq gl (hGL ▸ hgl)
  -- per representative facts
  have hspec : ∀ p ∈ R, p.1 < 2 ^ n ∧ maskCard n p.1 = k ∧ (∀ q ∈ Q, p.1 ≤ imageMask n q p.1) ∧
      (Q.filter fun q => imageMask n q p.1 == p.1).length * p.2 = Q.length := by
    intro p hp
    have h := (List.all_eq_true.mp hR) p hp
    unfold repOK at h
    have himg := imgs_eq gens GLs hGL GS hGS D hD p.1
    rw [scanImgs_eq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rw [himg h1, ← hQ] at h3 h4
    refine ⟨h1, h2, ?_, ?_⟩
    · intro q hq
      simpa using h3 _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
    · rw [hQlen, ← h4, List.countP_map, List.countP_eq_length_filter]
      rfl
  have hmaskOf : ∀ p ∈ R, cutMask (unmask n p.1) = p.1 := fun p hp => cutMask_unmask _ (hspec p hp).1
  have hchainP : List.Pairwise (fun a b : ℕ × ℕ => a.1 < b.1) R := incrB_pairwise R hlt
  set T : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard k with hT
  have hmemT : ∀ p ∈ R, unmask n p.1 ∈ T := by
    intro p hp
    rw [hT, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by rw [card_unmask]; exact (hspec p hp).2.1⟩
  have hTcl : ∀ S ∈ T, ∀ σ : Equiv.Perm (Fin n), S.image σ ∈ T := by
    intro S hS σ
    rw [hT, Finset.mem_powersetCard] at hS ⊢
    exact ⟨Finset.subset_univ _, by rw [Finset.card_image_of_injective _ σ.injective]; exact hS.2⟩
  have hnodup : (R.map fun p => unmask n p.1).Nodup := by
    refine List.Nodup.of_map cutMask ?_
    rw [List.map_map]
    have h2 : List.map (cutMask ∘ fun p : ℕ × ℕ => unmask n p.1) R = R.map Prod.fst :=
      List.map_congr_left (fun p hp => hmaskOf p hp)
    rw [h2]
    exact hchainP.map Prod.fst (fun a b h => ne_of_lt h)
  have hclass : ∀ p ∈ R, (T.filter (OrbRel gens (unmask n p.1))).card = p.2 := by
    intro p hp
    obtain ⟨_, _, _, hc⟩ := hspec p hp
    have h := orbit_card_mul gens T hTcl Q hnd hsound hcomplete (unmask n p.1) (hmemT p hp)
    rw [hmaskOf p hp] at h
    have hpos : 0 < (Q.filter fun q => imageMask n q p.1 == p.1).length := by
      rcases Nat.eq_zero_or_pos (Q.filter fun q => imageMask n q p.1 == p.1).length with h0 | h0
      · rw [h0, zero_mul, hQlen] at hc; omega
      · exact h0
    exact Nat.eq_of_mul_eq_mul_right hpos (h.trans hc.symm |>.trans (mul_comm _ _) |>.trans rfl)
  have hle : ∀ p ∈ R, ∀ p' ∈ R, OrbRel gens (unmask n p.1) (unmask n p'.1) → p.1 ≤ p'.1 := by
    intro p hp p' hp' ⟨g, hg, h⟩
    have h1 := congrArg cutMask h
    rw [cutMask_image, hmaskOf p hp, hmaskOf p' hp'] at h1
    rw [h1]
    exact (hspec p hp).2.2.1 _ (hcomplete g hg)
  have hmemR : ∀ r ∈ (R.map fun p => unmask n p.1).toFinset, ∃ p ∈ R, r = unmask n p.1 := by
    intro r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
    exact ⟨p, hp, rfl⟩
  have key := sum_eq_sum_reps T (OrbRel gens) (orbRel_symm gens) (orbRel_trans gens)
    (fun S => g (graphCutRankBits adj S)) (rankFn_orbRel gens adj hgens g)
    (R.map fun p => unmask n p.1).toFinset
    (by
      intro r hr r' hr' h
      obtain ⟨p, hp, rfl⟩ := hmemR r hr
      obtain ⟨p', hp', rfl⟩ := hmemR r' hr'
      have h1 := hle p hp p' hp' h
      have h2 := hle p' hp' p hp (orbRel_symm gens _ _ h)
      rw [le_antisymm h1 h2])
    (by
      rw [List.sum_toFinset _ hnodup, List.map_map, hT, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin, ← hsum]
      congr 1
      refine List.map_congr_left fun p hp => ?_
      simp only [Function.comp]
      rw [← hT, hclass p hp])
  rw [key, List.sum_toFinset _ hnodup, List.map_map]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  simp only [Function.comp, smul_eq_mul]
  rw [hclass p hp]

end Reps

end FormalResearch.NQubit.Graph
