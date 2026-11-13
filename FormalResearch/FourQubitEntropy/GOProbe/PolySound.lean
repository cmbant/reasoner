module

public import Mathlib
public import FormalResearch.FourQubitEntropy.GOProbe.Poly

/-!
# GO certificate: semantics and soundness of the sparse polynomial operations

`evK x k = ∏_{i<19} x_i^{dig i k}` and `ev x p = ∑ c · evK x k`.  The additive operations (`addSP`, `sumSP`,
`scaleSP`, `normSP`) are sound unconditionally; `mulSP` is sound when the total degrees of the factors add to at
most `255` (so that no base-256 digit carries).  `Dg d p` ("all keys have total degree `≤ d`") is propagated
through every operation.  `actSP` substitutes `x_i ↦ sg_i x_{mi i}`.  Claim class: proved.
-/

@[expose] public section


open Finset

namespace FormalResearch.FourQubitEntropy.GOProbe

/-! ### Base-256 digits -/

theorem dig_lt (i k : ℕ) : dig i k < 256 := Nat.mod_lt _ (by norm_num)

theorem mod_succ (k i : ℕ) : k % 256 ^ (i + 1) = k % 256 ^ i + 256 ^ i * dig i k := by
  unfold dig
  rw [pow_succ]
  exact Nat.mod_mul

theorem dig_add_aux (a b : ℕ) : ∀ n : ℕ, (∀ i < n, dig i a + dig i b ≤ 255) →
    (a + b) % 256 ^ n = a % 256 ^ n + b % 256 ^ n ∧ ∀ i < n, dig i (a + b) = dig i a + dig i b := by
  intro n
  induction n with
  | zero => intro _; simp [Nat.mod_one]
  | succ n ih =>
    intro h
    obtain ⟨hlow, hdig⟩ := ih fun i hi => h i (Nat.lt_succ_of_lt hi)
    have hpos : 0 < 256 ^ n := by positivity
    have hlt : a % 256 ^ n + b % 256 ^ n < 256 ^ n := by
      rw [← hlow]; exact Nat.mod_lt _ hpos
    have hdiv : (a + b) / 256 ^ n = a / 256 ^ n + b / 256 ^ n := by
      rw [Nat.add_div hpos, ite_eq_right (by omega)]; simp
    have hn := h n (Nat.lt_succ_self n)
    have hdn : dig n (a + b) = dig n a + dig n b := by
      unfold dig at hn ⊢
      rw [hdiv, Nat.add_mod, Nat.mod_eq_of_lt (by omega : (a / 256 ^ n % 256 + b / 256 ^ n % 256) < 256)]
    refine ⟨?_, ?_⟩
    · rw [mod_succ (a + b) n, mod_succ a n, mod_succ b n, hlow, hdn]; ring
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact hdig i hi
      · subst hi; exact hdn

theorem dig_add (a b i : ℕ) (h : ∀ j ≤ i, dig j a + dig j b ≤ 255) :
    dig i (a + b) = dig i a + dig i b :=
  (dig_add_aux a b (i + 1) fun j hj => h j (Nat.lt_succ_iff.1 hj)).2 i (Nat.lt_succ_self i)

theorem listSum_range (n : ℕ) (f : ℕ → ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem dsum_eq (k : ℕ) : dsum k = ∑ i ∈ range 19, dig i k := listSum_range 19 _

theorem dig_le_dsum {i : ℕ} (hi : i < 19) (k : ℕ) : dig i k ≤ dsum k := by
  rw [dsum_eq]
  exact Finset.single_le_sum (f := fun i => dig i k) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hi)

theorem dig_add' {a b : ℕ} (h : dsum a + dsum b ≤ 255) {i : ℕ} (hi : i < 19) :
    dig i (a + b) = dig i a + dig i b := by
  refine dig_add a b i fun j hj => ?_
  have := dig_le_dsum (lt_of_le_of_lt hj hi) a
  have := dig_le_dsum (lt_of_le_of_lt hj hi) b
  omega

theorem dsum_add {a b : ℕ} (h : dsum a + dsum b ≤ 255) : dsum (a + b) = dsum a + dsum b := by
  rw [dsum_eq, dsum_eq, dsum_eq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi => dig_add' h (Finset.mem_range.1 hi)

/-! ### Evaluation -/

noncomputable def evK (x : ℕ → ℝ) (k : ℕ) : ℝ := ∏ i ∈ range 19, x i ^ dig i k

noncomputable def ev (x : ℕ → ℝ) (p : SP) : ℝ := (p.map fun t => (t.2 : ℝ) * evK x t.1).sum

def Dg (d : ℕ) (p : SP) : Prop := ∀ t ∈ p, dsum t.1 ≤ d

theorem evK_add {a b : ℕ} (h : dsum a + dsum b ≤ 255) (x : ℕ → ℝ) :
    evK x (a + b) = evK x a * evK x b := by
  unfold evK
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i hi => by rw [dig_add' h (Finset.mem_range.1 hi), pow_add]

@[simp] theorem ev_nil (x : ℕ → ℝ) : ev x [] = 0 := by simp [ev]

theorem ev_cons (x : ℕ → ℝ) (t : Nat × Int) (p : SP) :
    ev x (t :: p) = (t.2 : ℝ) * evK x t.1 + ev x p := by simp [ev]

theorem ev_append (x : ℕ → ℝ) (p q : SP) : ev x (p ++ q) = ev x p + ev x q := by
  simp [ev, List.map_append, List.sum_append]

theorem ev_reverse (x : ℕ → ℝ) (p : SP) : ev x p.reverse = ev x p := by
  simp [ev, List.map_reverse, List.sum_reverse]

theorem ev_reverseAux (x : ℕ → ℝ) (acc p : SP) : ev x (acc.reverseAux p) = ev x acc + ev x p := by
  rw [List.reverseAux_eq, ev_append, ev_reverse]

theorem Dg_nil (d : ℕ) : Dg d [] := by simp [Dg]

theorem Dg_cons {d : ℕ} {t : Nat × Int} {p : SP} : Dg d (t :: p) ↔ dsum t.1 ≤ d ∧ Dg d p := by
  simp [Dg]

theorem Dg_append {d : ℕ} {p q : SP} : Dg d (p ++ q) ↔ Dg d p ∧ Dg d q := by
  simp [Dg, or_imp, forall_and]

theorem Dg_reverseAux {d : ℕ} {acc p : SP} : Dg d (acc.reverseAux p) ↔ Dg d acc ∧ Dg d p := by
  rw [List.reverseAux_eq, Dg_append]
  simp [Dg]

theorem Dg_mono {d d' : ℕ} (h : d ≤ d') {p : SP} (hp : Dg d p) : Dg d' p :=
  fun t ht => le_trans (hp t ht) h

/-! ### Addition -/

theorem addGo_spec (x : ℕ → ℝ) (d : ℕ) : ∀ (f : ℕ) (acc p q : SP),
    ev x (addGo f acc p q) = ev x acc + ev x p + ev x q ∧
      (Dg d acc → Dg d p → Dg d q → Dg d (addGo f acc p q)) := by
  intro f
  induction f with
  | zero =>
    intro acc p q
    simp only [addGo]
    refine ⟨by rw [ev_reverseAux, ev_append]; ring, fun h1 h2 h3 => ?_⟩
    rw [Dg_reverseAux, Dg_append]; exact ⟨h1, h2, h3⟩
  | succ f ih =>
    intro acc p q
    cases p with
    | nil =>
      simp only [addGo]
      refine ⟨by rw [ev_reverseAux]; simp, fun h1 _ h3 => ?_⟩
      rw [Dg_reverseAux]; exact ⟨h1, h3⟩
    | cons a p =>
      cases q with
      | nil =>
        simp only [addGo]
        refine ⟨by rw [ev_reverseAux]; simp, fun h1 h2 _ => ?_⟩
        rw [Dg_reverseAux]; exact ⟨h1, h2⟩
      | cons b q =>
        simp only [addGo]
        by_cases h1 : a.1 < b.1
        · rw [ite_eq_left h1]
          obtain ⟨e, dg⟩ := ih (a :: acc) p (b :: q)
          refine ⟨by rw [e, ev_cons, ev_cons, ev_cons]; ring, fun ha hp hq => ?_⟩
          rw [Dg_cons] at hp hq
          exact dg (Dg_cons.2 ⟨hp.1, ha⟩) hp.2 (Dg_cons.2 hq)
        · rw [ite_eq_right h1]
          by_cases h2 : b.1 < a.1
          · rw [ite_eq_left h2]
            obtain ⟨e, dg⟩ := ih (b :: acc) (a :: p) q
            refine ⟨by rw [e, ev_cons, ev_cons, ev_cons]; ring, fun ha hp hq => ?_⟩
            rw [Dg_cons] at hp hq
            exact dg (Dg_cons.2 ⟨hq.1, ha⟩) (Dg_cons.2 hp) hq.2
          · rw [ite_eq_right h2]
            have hk : a.1 = b.1 := by omega
            by_cases h3 : a.2 + b.2 = 0
            · rw [ite_eq_left h3]
              obtain ⟨e, dg⟩ := ih acc p q
              refine ⟨?_, fun ha hp hq => ?_⟩
              · rw [e, ev_cons, ev_cons, ← hk]
                have : (a.2 : ℝ) + b.2 = 0 := by exact_mod_cast h3
                linear_combination (-(evK x a.1)) * this
              · rw [Dg_cons] at hp hq
                exact dg ha hp.2 hq.2
            · rw [ite_eq_right h3]
              obtain ⟨e, dg⟩ := ih ((a.1, a.2 + b.2) :: acc) p q
              refine ⟨?_, fun ha hp hq => ?_⟩
              · rw [e, ev_cons, ev_cons, ev_cons, ← hk]
                push_cast
                ring
              · rw [Dg_cons] at hp hq
                exact dg (Dg_cons.2 ⟨hp.1, ha⟩) hp.2 hq.2

theorem ev_addSP (x : ℕ → ℝ) (p q : SP) : ev x (addSP p q) = ev x p + ev x q := by
  have := (addGo_spec x 0 (p.length + q.length + 1) [] p q).1
  simpa [addSP] using this

theorem Dg_addSP {d : ℕ} {p q : SP} (hp : Dg d p) (hq : Dg d q) : Dg d (addSP p q) :=
  (addGo_spec (fun _ => 0) d (p.length + q.length + 1) [] p q).2 (Dg_nil d) hp hq

theorem ev_pairUp (x : ℕ → ℝ) : ∀ l : List SP, ((pairUp l).map (ev x)).sum = (l.map (ev x)).sum
  | [] => by simp [pairUp]
  | [a] => by simp [pairUp]
  | a :: b :: t => by
    rw [pairUp, List.map_cons, List.sum_cons, ev_pairUp x t, ev_addSP]
    simp; ring

theorem Dg_pairUp {d : ℕ} : ∀ l : List SP, (∀ p ∈ l, Dg d p) → ∀ p ∈ pairUp l, Dg d p
  | [], _ => by simp [pairUp]
  | [a], h => by simpa [pairUp] using h
  | a :: b :: t, h => by
    intro p hp
    rw [pairUp] at hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact Dg_addSP (h a (by simp)) (h b (by simp))
    · exact Dg_pairUp t (fun q hq => h q (by simp [hq])) p hp

theorem sumFuel_spec (x : ℕ → ℝ) (d : ℕ) : ∀ (f : ℕ) (l : List SP),
    ev x (sumFuel f l) = (l.map (ev x)).sum ∧ ((∀ p ∈ l, Dg d p) → Dg d (sumFuel f l)) := by
  intro f
  induction f with
  | zero =>
    intro l
    simp only [sumFuel]
    induction l with
    | nil => simp [Dg_nil]
    | cons a t ih =>
      obtain ⟨e, dg⟩ := ih
      refine ⟨by rw [List.foldr_cons, ev_addSP, e]; simp, fun h => ?_⟩
      rw [List.foldr_cons]
      exact Dg_addSP (h a (by simp)) (dg fun p hp => h p (by simp [hp]))
  | succ f ih =>
    intro l
    match l with
    | [] => simp [sumFuel, Dg_nil]
    | [a] => simp [sumFuel]
    | a :: b :: t =>
      simp only [sumFuel]
      obtain ⟨e, dg⟩ := ih (pairUp (a :: b :: t))
      refine ⟨by rw [e, ev_pairUp], fun h => dg (Dg_pairUp _ h)⟩

theorem ev_sumSP (x : ℕ → ℝ) (l : List SP) : ev x (sumSP l) = (l.map (ev x)).sum :=
  (sumFuel_spec x 0 64 l).1

theorem Dg_sumSP {d : ℕ} {l : List SP} (h : ∀ p ∈ l, Dg d p) : Dg d (sumSP l) :=
  (sumFuel_spec (fun _ => 0) d 64 l).2 h

/-! ### Multiplication, scaling, normalisation -/

theorem ev_mulTerm (x : ℕ → ℝ) (k : ℕ) (c : ℤ) (q : SP) (hq : ∀ s ∈ q, dsum k + dsum s.1 ≤ 255) :
    ev x (mulTerm k c q) = c * evK x k * ev x q := by
  induction q with
  | nil => simp [mulTerm]
  | cons s q ih =>
    have h1 := hq s (by simp)
    have h2 := ih (fun r hr => hq r (by simp [hr]))
    have : mulTerm k c (s :: q) = (k + s.1, c * s.2) :: mulTerm k c q := rfl
    rw [this, ev_cons, ev_cons, h2, evK_add h1]
    push_cast
    ring

theorem Dg_mulTerm {d1 d2 k : ℕ} {c : ℤ} {q : SP} (hk : dsum k ≤ d1) (hq : Dg d2 q) (h : d1 + d2 ≤ 255) :
    Dg (d1 + d2) (mulTerm k c q) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
  have := hq s hs
  show dsum (k + s.1) ≤ d1 + d2
  rw [dsum_add (by omega)]
  omega

theorem mulSP_list (x : ℕ → ℝ) {d1 d2 : ℕ} (q : SP) (hq : Dg d2 q) (h : d1 + d2 ≤ 255) :
    ∀ p : SP, Dg d1 p → (((p.map fun t => mulTerm t.1 t.2 q).map (ev x)).sum) = ev x p * ev x q
  | [], _ => by simp
  | t :: p, hp => by
    rw [Dg_cons] at hp
    rw [List.map_cons, List.map_cons, List.sum_cons, mulSP_list x q hq h p hp.2, ev_cons,
      ev_mulTerm x t.1 t.2 q (fun s hs => by have := hq s hs; omega)]
    ring

theorem ev_mulSP (x : ℕ → ℝ) {d1 d2 : ℕ} {p q : SP} (hp : Dg d1 p) (hq : Dg d2 q) (h : d1 + d2 ≤ 255) :
    ev x (mulSP p q) = ev x p * ev x q := by
  unfold mulSP
  rw [ev_sumSP]
  exact mulSP_list x q hq h p hp

theorem Dg_mulSP {d1 d2 : ℕ} {p q : SP} (hp : Dg d1 p) (hq : Dg d2 q) (h : d1 + d2 ≤ 255) :
    Dg (d1 + d2) (mulSP p q) := by
  unfold mulSP
  apply Dg_sumSP
  intro r hr
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hr
  exact Dg_mulTerm (hp t ht) hq h

theorem ev_scaleSP (x : ℕ → ℝ) (c : ℤ) (p : SP) : ev x (scaleSP c p) = c * ev x p := by
  unfold scaleSP
  by_cases hc : c = 0
  · simp [hc]
  · rw [ite_eq_right hc]
    induction p with
    | nil => simp
    | cons t p ih =>
      rw [List.map_cons, ev_cons, ih, ev_cons]
      push_cast
      ring

theorem Dg_scaleSP {d : ℕ} (c : ℤ) {p : SP} (hp : Dg d p) : Dg d (scaleSP c p) := by
  unfold scaleSP
  split_ifs
  · exact Dg_nil d
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
    exact hp s hs

theorem ev_normSP (x : ℕ → ℝ) (l : List (Nat × Int)) : ev x (normSP l) = (l.map fun t => (t.2 : ℝ) * evK x t.1).sum := by
  unfold normSP
  rw [ev_sumSP]
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ← ih]
    by_cases ht : t.2 = 0
    · simp [ht]
    · simp [ht, ev_cons]

theorem Dg_normSP {d : ℕ} {l : List (Nat × Int)} (hl : ∀ t ∈ l, dsum t.1 ≤ d) : Dg d (normSP l) := by
  unfold normSP
  apply Dg_sumSP
  intro r hr
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hr
  split_ifs
  · exact Dg_nil d
  · intro s hs
    rw [List.mem_singleton] at hs
    rw [hs]
    exact hl t ht

theorem eqSP_sound : ∀ p q : SP, eqSP p q = true → p = q
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [eqSP] at h
  | _ :: _, [], h => by simp [eqSP] at h
  | a :: p, b :: q, h => by
    simp only [eqSP, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [eqSP_sound p q h3]
    exact congrArg (· :: q) (Prod.ext h1 h2)

/-! ### Signed coordinate maps -/

theorem dig_shift (d m j : ℕ) (hd : d < 256) : dig j (d * 256 ^ m) = if j = m then d else 0 := by
  unfold dig
  rcases lt_trichotomy j m with h | h | h
  · obtain ⟨t, rfl⟩ : ∃ t, m = j + t + 1 := ⟨m - j - 1, by omega⟩
    have e : d * 256 ^ (j + t + 1) = (d * 256 ^ t * 256) * 256 ^ j := by ring
    rw [e, Nat.mul_div_cancel _ (by positivity), ite_eq_right (by omega)]
    generalize d * 256 ^ t = y
    omega
  · subst h
    rw [Nat.mul_div_cancel _ (by positivity), ite_eq_left rfl]
    exact Nat.mod_eq_of_lt hd
  · obtain ⟨t, rfl⟩ : ∃ t, j = m + t + 1 := ⟨j - m - 1, by omega⟩
    have e : (256 : ℕ) ^ (m + t + 1) = 256 ^ m * 256 ^ (t + 1) := by ring
    rw [ite_eq_right (by omega), e, mul_comm d (256 ^ m), Nat.mul_div_mul_left _ _ (by positivity)]
    have : d / 256 ^ (t + 1) = 0 := by
      apply Nat.div_eq_of_lt
      calc d < 256 := hd
        _ = 256 ^ 1 := by norm_num
        _ ≤ 256 ^ (t + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [this]

theorem dig_sum_shift (d m : ℕ → ℕ) (hd : ∀ i, d i < 256) :
    ∀ n j, ∑ i ∈ range n, d i ≤ 255 →
      dig j (∑ i ∈ range n, d i * 256 ^ m i) = ∑ i ∈ (range n).filter (fun i => m i = j), d i := by
  intro n
  induction n with
  | zero => intro j _; simp [dig]
  | succ n ih =>
    intro j hsum
    rw [Finset.sum_range_succ] at hsum
    have hsum' : ∑ i ∈ range n, d i ≤ 255 := by omega
    have hdig_b : ∀ i', dig i' (d n * 256 ^ m n) = if i' = m n then d n else 0 :=
      fun i' => dig_shift _ _ _ (hd n)
    have hsub : ∀ i', ∑ i ∈ (range n).filter (fun i => m i = i'), d i ≤ ∑ i ∈ range n, d i :=
      fun i' => Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hS : ∀ i', ∑ i ∈ (range n).filter (fun i => m i = i'), d i + (if i' = m n then d n else 0) ≤ 255 := by
      intro i'
      have := hsub i'
      split_ifs <;> omega
    rw [Finset.sum_range_succ, dig_add (∑ i ∈ range n, d i * 256 ^ m i) (d n * 256 ^ m n) j
      (fun j' _ => by rw [ih j' hsum', hdig_b]; exact hS j'), ih j hsum', hdig_b, Finset.range_add_one,
      Finset.filter_insert]
    by_cases h : m n = j
    · simp [h, add_comm]
    · simp [h, Ne.symm h]

theorem dig_actKey {mi : List ℕ} {k : ℕ} (hk : dsum k ≤ 255) {j : ℕ} :
    dig j (actKey mi k) = ∑ i ∈ (range 19).filter (fun i => mi.getD i 0 = j), dig i k := by
  unfold actKey
  rw [listSum_range 19 (fun i => dig i k * 256 ^ (mi.getD i 0))]
  exact dig_sum_shift (fun i => dig i k) (fun i => mi.getD i 0) (fun i => dig_lt i k) 19 j
    (by rw [← dsum_eq]; exact hk)

theorem evK_actKey {mi : List ℕ} (hmi : ∀ i < 19, mi.getD i 0 < 19) {k : ℕ} (hk : dsum k ≤ 255)
    (x : ℕ → ℝ) : evK x (actKey mi k) = ∏ i ∈ range 19, x (mi.getD i 0) ^ dig i k := by
  unfold evK
  have h1 : ∀ j ∈ range 19, x j ^ dig j (actKey mi k)
      = ∏ i ∈ (range 19).filter (fun i => mi.getD i 0 = j), x (mi.getD i 0) ^ dig i k := by
    intro j _
    rw [dig_actKey hk, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
  rw [Finset.prod_congr rfl h1]
  exact Finset.prod_fiberwise_of_maps_to (g := fun i => mi.getD i 0) (s := range 19) (t := range 19)
    (fun i hi => Finset.mem_range.2 (hmi i (Finset.mem_range.1 hi))) (fun i => x (mi.getD i 0) ^ dig i k)

theorem listProd_range (n : ℕ) (f : ℕ → ℤ) : ((List.range n).map f).prod = ∏ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]; simp

/-- The point `i ↦ sg_i x_{mi i}`. -/
noncomputable def act (g : List ℕ × List ℤ) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun i => ((g.2.getD i 1 : ℤ) : ℝ) * x (g.1.getD i 0)

theorem ev_actSP (g : List ℕ × List ℤ) (hg : ∀ i < 19, g.1.getD i 0 < 19) (x : ℕ → ℝ) :
    ∀ p : SP, Dg 255 p → ev x (actSP g p) = ev (act g x) p := by
  intro p hp
  unfold actSP
  rw [ev_normSP]
  induction p with
  | nil => simp
  | cons t p ih =>
    rw [Dg_cons] at hp
    rw [List.map_cons, List.map_cons, List.sum_cons, ih hp.2, ev_cons]
    congr 1
    dsimp only
    rw [evK_actKey hg hp.1 x]
    unfold evK actCoef
    rw [listProd_range 19 (fun i => g.2.getD i 1 ^ dig i t.1)]
    simp only [act, mul_pow, Finset.prod_mul_distrib]
    push_cast
    ring

/-- The point `i ↦ f_i x_i`. -/
noncomputable def flipPt (f : List ℤ) (x : ℕ → ℝ) : ℕ → ℝ := fun i => ((f.getD i 1 : ℤ) : ℝ) * x i

theorem ev_flipSP (f : List ℤ) (x : ℕ → ℝ) : ∀ p : SP, ev x (flipSP f p) = ev (flipPt f x) p
  | [] => by simp [flipSP]
  | t :: p => by
    have : flipSP f (t :: p) = (t.1, actCoef f t.1 * t.2) :: flipSP f p := rfl
    rw [this, ev_cons, ev_cons, ev_flipSP f x p]
    congr 1
    unfold evK actCoef
    rw [listProd_range 19 (fun i => f.getD i 1 ^ dig i t.1)]
    simp only [flipPt, mul_pow, Finset.prod_mul_distrib]
    push_cast
    ring

end FormalResearch.FourQubitEntropy.GOProbe
