module

public import Mathlib
public import FormalResearch.FourQubitEntropy.GOProbe.PolySound
public import FormalResearch.FourQubitEntropy.GOProbe.Block

/-!
# GO certificate: soundness of the block expansion

For a point `y`, a constraint matrix `M` (of polynomials) and a block `b`, let `u_i[a] = ev y (rowComp a (basis i))`
and `Q_ij = ∑_{a,c} u_i[a] M[a][c](y) u_j[c]`.  Then `ev y (uPart W cons blocks)` is
`∑_c ∑_{B : cid B = c} ∑_{i,j < m_B} W_B i j · Q^{B}_ij`, provided all atoms and constraint entries have total degree
`≤ 16` (so that every product is carry free).  Claim class: proved.
-/

@[expose] public section


open Finset

namespace FormalResearch.FourQubitEntropy.GOProbe

theorem list_sum_range {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem entry_mapmap {k : ℕ} (F : ℕ → ℕ → SP) {a c : ℕ} (ha : a < k) (hc : c < k) :
    entry ((List.range k).map fun a => (List.range k).map fun c => F a c) a c = F a c := by
  simp [entry, List.getD_eq_getElem?_getD, ha, hc]

theorem entry_map_range {n : ℕ} (_F : ℕ → SP) {j : ℕ} (hj : j < n) (l : ℕ → List SP) :
    (((List.range n).map l).getD j []) = l j := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem getD_mem {α : Type*} (l : List α) (i : ℕ) (d : α) : l.getD i d ∈ l ∨ l.getD i d = d := by
  by_cases h : i < l.length
  · left; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · right; exact List.getD_eq_default _ _ (by omega)

/-- The polynomial in position `(i, a)` of a table is `[]` or comes from the table. -/
theorem entry_mem {l : List (List SP)} {i a : ℕ} {P : SP → Prop} (hl : ∀ r ∈ l, ∀ p ∈ r, P p)
    (h0 : P []) : P (entry l i a) := by
  unfold entry
  rcases getD_mem l i [] with h1 | h1
  · rcases getD_mem (l.getD i []) a [] with h2 | h2
    · exact hl _ h1 _ h2
    · rw [h2]; exact h0
  · rw [h1]; simpa using h0

/-! ### Degrees -/

def AtomsDg (d : ℕ) (b : GBlock) : Prop := ∀ row ∈ b.basis, ∀ t ∈ row, dsum t.2.1 ≤ d

theorem atomsDg_of {d : ℕ} {b : GBlock} (h : b.atomsDg d = true) : AtomsDg d b := by
  simp only [GBlock.atomsDg, List.all_eq_true, decide_eq_true_eq] at h
  exact fun row hr t ht => h row hr t ht

theorem Dg_rowComp {d : ℕ} (c : ℕ) {row : List (Nat × Nat × Int)} (h : ∀ t ∈ row, dsum t.2.1 ≤ d) :
    Dg d (rowComp c row) := by
  unfold rowComp
  apply Dg_normSP
  intro t ht
  obtain ⟨s, hs, hst⟩ := List.mem_filterMap.1 ht
  split_ifs at hst
  · cases hst; exact h s hs

theorem Dg_pre {d : ℕ} {k : ℕ} {b : GBlock} (hb : AtomsDg d b) (i a : ℕ) :
    Dg d (entry (preOf k b.basis) i a) := by
  apply entry_mem (P := Dg d) _ (Dg_nil d)
  intro r hr p hp
  unfold preOf at hr
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hr
  obtain ⟨a', _, rfl⟩ := List.mem_map.1 hp
  exact Dg_rowComp a' (hb row hrow)

theorem Dg_lcomb {d : ℕ} (W : ℕ → ℕ → ℤ) (m : ℕ) {pre : List (List SP)} (hpre : ∀ i a, Dg d (entry pre i a))
    (j a : ℕ) : Dg d (lcomb W m pre j a) := by
  unfold lcomb
  apply Dg_sumSP
  intro p hp
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hp
  exact Dg_scaleSP _ (hpre i a)

/-! ### Semantics of the block expansion -/

/-- `u_i[a]` at the point `y`. -/
noncomputable def uv (y : ℕ → ℝ) (pre : List (List SP)) (i a : ℕ) : ℝ := ev y (entry pre i a)

/-- `M[a][c](y)`. -/
noncomputable def Mev (y : ℕ → ℝ) (M : List (List SP)) (a c : ℕ) : ℝ := ev y (entry M a c)

/-- The bilinear form of `M(y)` on `ℕ → ℝ` (restricted to indices `< k`). -/
noncomputable def Bf (y : ℕ → ℝ) (k : ℕ) (M : List (List SP)) (v w : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range k, ∑ c ∈ range k, v a * Mev y M a c * w c

theorem ev_lcomb (y : ℕ → ℝ) (W : ℕ → ℕ → ℤ) (m : ℕ) {pre : List (List SP)} {d : ℕ}
    (_hpre : ∀ i a, Dg d (entry pre i a)) (j a : ℕ) :
    ev y (lcomb W m pre j a) = ∑ i ∈ range m, (W i j : ℝ) * uv y pre i a := by
  unfold lcomb
  rw [ev_sumSP, List.map_map, list_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Function.comp, ev_scaleSP, uv]

theorem blockSlots_spec (y : ℕ → ℝ) (W : ℕ → ℕ → ℤ) (k : ℕ) {b : GBlock} (hb : AtomsDg 16 b) (a c : ℕ) :
    Dg 32 (entry (blockSlots W k b) a c) ∧
      (a < k → c < k → ev y (entry (blockSlots W k b) a c) =
        ∑ j ∈ range b.m, (∑ i ∈ range b.m, (W i j : ℝ) * uv y (preOf k b.basis) i a) *
          uv y (preOf k b.basis) j c) := by
  have hpre : ∀ i a, Dg 16 (entry (preOf k b.basis) i a) := Dg_pre hb
  have hL : ∀ j a, Dg 16 (lcomb W b.m (preOf k b.basis) j a) := Dg_lcomb W b.m hpre
  set pre := preOf k b.basis with hpre_def
  set Ls : List (List SP) := (List.range b.m).map fun j => (List.range k).map fun a => lcomb W b.m pre j a
    with hLs
  have hLsDg : ∀ j a, Dg 16 (entry Ls j a) := by
    intro j a
    apply entry_mem (P := Dg 16) _ (Dg_nil 16)
    intro r hr p hp
    obtain ⟨j', _, rfl⟩ := List.mem_map.1 hr
    obtain ⟨a', _, rfl⟩ := List.mem_map.1 hp
    exact hL j' a'
  have hslot : ∀ a c, Dg 32 (sumSP ((List.range b.m).map fun j => mulSP (entry Ls j a) (entry pre j c))) := by
    intro a c
    apply Dg_sumSP
    intro p hp
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hp
    exact Dg_mulSP (hLsDg j a) (hpre j c) (by norm_num)
  constructor
  · unfold blockSlots
    apply entry_mem (P := Dg 32) _ (Dg_nil 32)
    intro r hr p hp
    obtain ⟨a', _, rfl⟩ := List.mem_map.1 hr
    obtain ⟨c', _, rfl⟩ := List.mem_map.1 hp
    exact hslot a' c'
  · intro ha hc
    unfold blockSlots
    simp only []
    rw [entry_mapmap (k := k) (fun a c => sumSP ((List.range b.m).map fun j => mulSP (entry Ls j a) (entry pre j c))) ha hc]
    rw [ev_sumSP, List.map_map, list_sum_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < b.m := Finset.mem_range.1 hj
    have hE : entry Ls j a = lcomb W b.m pre j a := by
      simp only [entry, hLs]
      rw [entry_map_range (n := b.m) (fun _ => []) hj' (fun j => (List.range k).map fun a => lcomb W b.m pre j a)]
      simp [List.getD_eq_getElem?_getD, ha]
    simp only [Function.comp]
    rw [ev_mulSP y (hLsDg j a) (hpre j c) (by norm_num), hE, ev_lcomb y W b.m hpre j a]
    rfl

theorem conSlots_spec (y : ℕ → ℝ) (wf : GBlock → ℕ → ℕ → ℤ) (k : ℕ) (bs : List GBlock)
    (hbs : ∀ b ∈ bs, AtomsDg 16 b) (a c : ℕ) :
    Dg 32 (entry (conSlots wf k bs) a c) ∧
      (a < k → c < k → ev y (entry (conSlots wf k bs) a c) =
        (bs.map fun b => ev y (entry (blockSlots (wf b) k b) a c)).sum) := by
  have hdg : ∀ a c, Dg 32 (sumSP ((bs.map fun b => blockSlots (wf b) k b).map fun s => entry s a c)) := by
    intro a c
    apply Dg_sumSP
    intro p hp
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hp
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hs
    exact (blockSlots_spec y (wf b) k (hbs b hb) a c).1
  constructor
  · unfold conSlots
    apply entry_mem (P := Dg 32) _ (Dg_nil 32)
    intro r hr p hp
    obtain ⟨a', _, rfl⟩ := List.mem_map.1 hr
    obtain ⟨c', _, rfl⟩ := List.mem_map.1 hp
    exact hdg a' c'
  · intro ha hc
    unfold conSlots
    simp only []
    rw [entry_mapmap (k := k) (fun a c => sumSP ((bs.map fun b => blockSlots (wf b) k b).map fun s => entry s a c)) ha hc]
    rw [ev_sumSP, List.map_map, List.map_map]
    rfl

theorem pairProd_spec (y : ℕ → ℝ) (k : ℕ) {M G : List (List SP)} (hM : ∀ a c, Dg 16 (entry M a c))
    (hG : ∀ a c, Dg 32 (entry G a c)) :
    Dg 48 (pairProd k M G) ∧
      ev y (pairProd k M G) = ∑ a ∈ range k, ∑ c ∈ range k, ev y (entry G a c) * ev y (entry M a c) := by
  unfold pairProd
  constructor
  · apply Dg_sumSP
    intro p hp
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hp
    apply Dg_sumSP
    intro q hq
    obtain ⟨c, _, rfl⟩ := List.mem_map.1 hq
    exact Dg_mulSP (hG a c) (hM a c) (by norm_num)
  · rw [ev_sumSP, List.map_map, list_sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Function.comp]
    rw [ev_sumSP, List.map_map, list_sum_range]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Function.comp]
    exact ev_mulSP y (hG a c) (hM a c) (by norm_num)

theorem alg_block (k m : ℕ) (W u : ℕ → ℕ → ℝ) (Mv : ℕ → ℕ → ℝ) :
    ∑ a ∈ range k, ∑ c ∈ range k,
        (∑ j ∈ range m, (∑ i ∈ range m, W i j * u i a) * u j c) * Mv a c
      = ∑ i ∈ range m, ∑ j ∈ range m, W i j * ∑ a ∈ range k, ∑ c ∈ range k, u i a * Mv a c * u j c := by
  have h1 : ∀ a c, (∑ j ∈ range m, (∑ i ∈ range m, W i j * u i a) * u j c) * Mv a c
      = ∑ j ∈ range m, ∑ i ∈ range m, W i j * (u i a * Mv a c * u j c) := by
    intro a c
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∀ i j, W i j * ∑ a ∈ range k, ∑ c ∈ range k, u i a * Mv a c * u j c
      = ∑ a ∈ range k, ∑ c ∈ range k, W i j * (u i a * Mv a c * u j c) := by
    intro i j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
  simp only [h1, h2]
  calc ∑ a ∈ range k, ∑ c ∈ range k, ∑ j ∈ range m, ∑ i ∈ range m, W i j * (u i a * Mv a c * u j c)
      = ∑ a ∈ range k, ∑ j ∈ range m, ∑ c ∈ range k, ∑ i ∈ range m, W i j * (u i a * Mv a c * u j c) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ j ∈ range m, ∑ a ∈ range k, ∑ c ∈ range k, ∑ i ∈ range m, W i j * (u i a * Mv a c * u j c) :=
        Finset.sum_comm
    _ = ∑ j ∈ range m, ∑ a ∈ range k, ∑ i ∈ range m, ∑ c ∈ range k, W i j * (u i a * Mv a c * u j c) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ j ∈ range m, ∑ i ∈ range m, ∑ a ∈ range k, ∑ c ∈ range k, W i j * (u i a * Mv a c * u j c) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i ∈ range m, ∑ j ∈ range m, ∑ a ∈ range k, ∑ c ∈ range k, W i j * (u i a * Mv a c * u j c) :=
        Finset.sum_comm

theorem sum_list_swap {β : Type*} (k : ℕ) (bs : List β) (g : β → ℕ → ℕ → ℝ) (Mv : ℕ → ℕ → ℝ) :
    ∑ a ∈ range k, ∑ c ∈ range k, (bs.map fun B => g B a c).sum * Mv a c
      = (bs.map fun B => ∑ a ∈ range k, ∑ c ∈ range k, g B a c * Mv a c).sum := by
  induction bs with
  | nil => simp
  | cons B bs ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
    rw [ih]

/-- The matrix `M_c` of constraint `c`: every entry has total degree `≤ d`. -/
def ConsDg (d : ℕ) (cons : List (List (List SP))) : Prop :=
  ∀ M ∈ cons, ∀ row ∈ M, ∀ p ∈ row, Dg d p

theorem consDg_of {d : ℕ} {cons : List (List (List SP))} (h : consDg d cons = true) : ConsDg d cons := by
  simp only [consDg, List.all_eq_true, dgOK, decide_eq_true_eq] at h
  intro M hM row hr p hp t ht
  exact h M hM row hr p hp t ht

/-- The block contribution `∑_{i,j} W_ij Q_ij` at the point `y` against the constraint matrix `M`. -/
noncomputable def blockVal (y : ℕ → ℝ) (W : ℕ → ℕ → ℤ) (M : List (List SP)) (b : GBlock) : ℝ :=
  ∑ i ∈ range b.m, ∑ j ∈ range b.m, (W i j : ℝ) *
    Bf y M.length M (uv y (preOf M.length b.basis) i) (uv y (preOf M.length b.basis) j)

theorem uPart_spec (y : ℕ → ℝ) (wf : GBlock → ℕ → ℕ → ℤ) (cons : List (List (List SP)))
    (blocks : List GBlock) (hcons : ConsDg 16 cons) (hbl : ∀ b ∈ blocks, AtomsDg 16 b) :
    Dg 48 (uPart wf cons blocks) ∧
      ev y (uPart wf cons blocks) = ∑ c ∈ range cons.length,
        ((blocks.filter fun b => b.cid == c).map fun b => blockVal y (wf b) (cons.getD c []) b).sum := by
  have hM : ∀ c a c', Dg 16 (entry (cons.getD c []) a c') := by
    intro c a c'
    apply entry_mem (P := Dg 16) _ (Dg_nil 16)
    rcases getD_mem cons c [] with h | h
    · exact hcons _ h
    · rw [h]; simp
  have hf : ∀ c, ∀ b ∈ blocks.filter (fun b => b.cid == c), AtomsDg 16 b :=
    fun c b hb => hbl b (List.mem_filter.1 hb).1
  unfold uPart
  constructor
  · apply Dg_sumSP
    intro p hp
    obtain ⟨c, _, rfl⟩ := List.mem_map.1 hp
    exact (pairProd_spec y _ (hM c) (fun a c' => (conSlots_spec y wf _ _ (hf c) a c').1)).1
  · rw [ev_sumSP, List.map_map, list_sum_range]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Function.comp]
    set M := cons.getD c [] with hMdef
    set bs := blocks.filter fun b => b.cid == c with hbs
    rw [(pairProd_spec y _ (hM c) (fun a c' => (conSlots_spec y wf _ _ (hf c) a c').1)).2]
    have h1 : ∀ a ∈ range M.length, ∀ c' ∈ range M.length,
        ev y (entry (conSlots wf M.length bs) a c') * ev y (entry M a c')
          = (bs.map fun b => ∑ j ∈ range b.m, (∑ i ∈ range b.m,
              (wf b i j : ℝ) * uv y (preOf M.length b.basis) i a) * uv y (preOf M.length b.basis) j c').sum
              * Mev y M a c' := by
      intro a ha c' hc'
      rw [(conSlots_spec y wf _ _ (hf c) a c').2 (Finset.mem_range.1 ha) (Finset.mem_range.1 hc')]
      unfold Mev
      congr 1
      congr 1
      refine List.map_congr_left fun b hb => ?_
      exact (blockSlots_spec y (wf b) _ (hf c b hb) a c').2 (Finset.mem_range.1 ha) (Finset.mem_range.1 hc')
    rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c' hc' => h1 a ha c' hc']
    rw [sum_list_swap M.length bs (fun b a c' => ∑ j ∈ range b.m, (∑ i ∈ range b.m,
        (wf b i j : ℝ) * uv y (preOf M.length b.basis) i a) * uv y (preOf M.length b.basis) j c')
        (Mev y M)]
    refine congrArg List.sum (List.map_congr_left fun b _ => ?_)
    rw [alg_block M.length b.m (fun i j => (wf b i j : ℝ)) (uv y (preOf M.length b.basis)) (Mev y M)]
    rfl

end FormalResearch.FourQubitEntropy.GOProbe
