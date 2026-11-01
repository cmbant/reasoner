import Mathlib
import FormalResearch.FourQubitEntropy.GOProbe.GramSound
import FormalResearch.FourQubitEntropy.GOProbe.BlockSound

/-!
# GO certificate: soundness theorem of the reflective checker

`go_sound`: if `check cons acts lit grid s2 cd blocks = true` and, at every point `g•x` of the orbit of `x`, every
constraint matrix `cons[c]` (evaluated at that point) is positive semidefinite, then `ev x lit ≥ 0`.
Here `cons`, `acts`, `lit` and `blocks` are arbitrary data; the generated data (`GOConst`, `GOData_*`) instantiate
them, the identification of `lit` with the paper's target polynomial and the positivity of the constraints at
closest points are separate obligations.  Claim class: proved.
-/

open Finset

namespace FormalResearch.FourQubitEntropy.GOProbe

/-! ### The bilinear form of a constraint matrix -/

noncomputable def BfL (y : ℕ → ℝ) (k : ℕ) (M : List (List SP)) : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => Bf y k M v w)
    (by intro v1 v2 w; simp only [Bf, Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (by
      intro r v w
      simp only [Bf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring)
    (by intro v w1 w2; simp only [Bf, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (by
      intro r v w
      simp only [Bf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring)

theorem BfL_apply (y : ℕ → ℝ) (k : ℕ) (M : List (List SP)) (v w : ℕ → ℝ) :
    BfL y k M v w = Bf y k M v w := rfl

/-- `M(y)` is positive semidefinite. -/
def Psd (y : ℕ → ℝ) (M : List (List SP)) : Prop := ∀ v : ℕ → ℝ, 0 ≤ Bf y M.length M v v

/-! ### Block data lemmas -/

theorem dot_eq_sum : ∀ (f g : List ℤ) (N : ℕ), f.length ≤ N →
    dot f g = ∑ k ∈ range N, f.getD k 0 * g.getD k 0
  | [], g, N, _ => by simp [dot]
  | a :: p, [], N, _ => by simp [dot]
  | a :: p, b :: q, N, h => by
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at h; omega⟩
    rw [dot, dot_eq_sum p q N' (by simpa using h), Finset.sum_range_succ']
    simp [add_comm]

theorem Rs_symm (b : GBlock) (i j : ℕ) : b.Rs i j = b.Rs j i := by
  unfold GBlock.Rs
  by_cases h : i ≤ j
  · by_cases h' : j ≤ i
    · have : i = j := le_antisymm h h'
      subst this; rfl
    · rw [if_pos h, if_neg h']
  · have h' : j ≤ i := by omega
    rw [if_neg h, if_pos h']

theorem Cs_symm (b : GBlock) (i j : ℕ) : b.Cs i j = b.Cs j i := by
  unfold GBlock.Cs
  by_cases h : i ≤ j
  · by_cases h' : j ≤ i
    · have : i = j := le_antisymm h h'
      subst this; rfl
    · rw [if_pos h, if_neg h']
  · have h' : j ≤ i := by omega
    rw [if_neg h, if_pos h']

theorem gramOK_dd {cd : ℤ} {b : GBlock} (h : b.gramOK cd = true) :
    ∀ i : Fin b.m, (b.m : ℤ) * cd <
      2 * ((cd * b.Rs i i + b.Cs i i) - ∑ j : Fin b.m, if i = j then 0 else |cd * b.Rs i j + b.Cs i j|) := by
  intro i
  unfold GBlock.gramOK at h
  rw [List.all_eq_true] at h
  have hi := h i (List.mem_range.2 i.2)
  rw [decide_eq_true_eq, list_sum_range] at hi
  have e : ∑ j : Fin b.m, (if i = j then (0 : ℤ) else |cd * b.Rs i j + b.Cs i j|)
      = ∑ j ∈ range b.m, (if (i : ℕ) = j then (0 : ℤ) else ((b.Dm cd i j).natAbs : ℤ)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => if (i : ℕ) = j then (0 : ℤ) else ((b.Dm cd i j).natAbs : ℤ)) b.m]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · rw [if_neg hij, if_neg (fun h' => hij (Fin.ext h'))]
      exact Int.abs_eq_natAbs _
  rw [e]
  exact hi

/-! ### Positivity of one block -/

theorem blockVal_nonneg {grid s2 cd : ℤ} (hg : 0 < grid) (hs : 0 < s2) (h2 : (2 : ℤ) ∣ s2) (hcd : 0 < cd)
    {y : ℕ → ℝ} {M : List (List SP)} (hpsd : Psd y M) {b : GBlock} (hgram : b.gramOK cd = true) :
    0 ≤ (cd : ℝ) * blockVal y (b.Wb grid s2) M b + blockVal y b.Wc M b := by
  set m := b.m with hm
  set N : ℕ := (b.factor.map List.length).sum with hN
  have hlen : ∀ i : ℕ, (b.factor.getD i []).length ≤ N := by
    intro i
    rcases getD_mem b.factor i [] with h | h
    · exact List.le_sum_of_mem (List.mem_map_of_mem h)
    · rw [h]; simp
  let A : Fin m → Fin N → ℤ := fun i k => (b.factor.getD i []).getD k 0
  let R : Fin m → Fin m → ℤ := fun i j => b.Rs i j
  let C : Fin m → Fin m → ℤ := fun i j => b.Cs i j
  let u : Fin m → (ℕ → ℝ) := fun i => uv y (preOf M.length b.basis) i
  have hB : ∀ v, 0 ≤ BfL y M.length M v v := fun v => hpsd v
  have key := inner_nonneg (BfL y M.length M) hB u A R C (fun i j => Rs_symm b i j) (fun i j => Cs_symm b i j)
    grid s2 cd hg hs h2 hcd (gramOK_dd hgram)
  have hdot : ∀ i j : Fin m, (∑ k : Fin N, A i k * A j k)
      = dot (b.factor.getD i []) (b.factor.getD j []) := by
    intro i j
    rw [dot_eq_sum _ _ N (hlen i), ← Fin.sum_univ_eq_sum_range (fun k => (b.factor.getD i []).getD k 0 *
      (b.factor.getD j []).getD k 0) N]
  have hgr : (0 : ℝ) < grid := by exact_mod_cast hg
  have hcr : (0 : ℝ) < cd := by exact_mod_cast hcd
  have hsum : ∀ (W : ℕ → ℕ → ℤ), blockVal y W M b
      = ∑ i : Fin m, ∑ j : Fin m, (W i j : ℝ) * BfL y M.length M (u i) (u j) := by
    intro W
    unfold blockVal
    rw [← hm, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range]
    rfl
  rw [hsum, hsum]
  set Gf : Fin m → Fin m → ℝ := fun i j =>
    (((((grid * (∑ k, A i k * A j k) + s2 / 2) / s2 + R i j : ℤ) : ℝ) + (C i j : ℝ) / cd) / grid) with hGf
  have key' : 0 ≤ ∑ i : Fin m, ∑ j : Fin m, Gf i j * BfL y M.length M (u i) (u j) := key
  have hW : ∀ i j : Fin m, (b.Wb grid s2 i j) = (grid * (∑ k, A i k * A j k) + s2 / 2) / s2 + R i j := by
    intro i j
    simp only [GBlock.Wb, hval, R]
    rw [hdot]
  have hpt : ∀ i j : Fin m, (cd : ℝ) * ((b.Wb grid s2 i j : ℝ) * BfL y M.length M (u i) (u j))
      + (b.Wc i j : ℝ) * BfL y M.length M (u i) (u j)
      = ((cd : ℝ) * grid) * (Gf i j * BfL y M.length M (u i) (u j)) := by
    intro i j
    simp only [hGf]
    rw [← hW i j]
    have hC' : (C i j : ℝ) = ((b.Wc i j : ℤ) : ℝ) := rfl
    rw [hC']
    generalize ((b.Wb grid s2 i j : ℤ) : ℝ) = a
    generalize ((b.Wc i j : ℤ) : ℝ) = c
    generalize BfL y M.length M (u i) (u j) = q
    field_simp
  have : (cd : ℝ) * ∑ i : Fin m, ∑ j : Fin m, (b.Wb grid s2 i j : ℝ) * BfL y M.length M (u i) (u j)
      + ∑ i : Fin m, ∑ j : Fin m, (b.Wc i j : ℝ) * BfL y M.length M (u i) (u j)
      = ((cd : ℝ) * grid) * ∑ i : Fin m, ∑ j : Fin m, Gf i j * BfL y M.length M (u i) (u j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hpt i j
  rw [this]
  exact mul_nonneg (by positivity) key'

/-! ### The total polynomial -/

theorem list_sum_lin {β : Type*} (l : List β) (c : ℝ) (f g : β → ℝ) :
    c * (l.map f).sum + (l.map g).sum = (l.map fun b => c * f b + g b).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

theorem uTotal_spec {cons : List (List (List SP))} {blocks : List GBlock} (grid s2 cd : ℤ)
    (hcons : ConsDg 16 cons) (hbl : ∀ b ∈ blocks, AtomsDg 16 b) :
    Dg 48 (uTotal grid s2 cd cons blocks) ∧
      ∀ y : ℕ → ℝ, ev y (uTotal grid s2 cd cons blocks) =
        ∑ c ∈ range cons.length, ((blocks.filter fun b => b.cid == c).map fun b =>
          (cd : ℝ) * blockVal y (b.Wb grid s2) (cons.getD c []) b + blockVal y b.Wc (cons.getD c []) b).sum := by
  have h1 := fun y => uPart_spec y (fun b => b.Wb grid s2) cons blocks hcons hbl
  have h2 := fun y => uPart_spec y (fun b => b.Wc) cons blocks hcons hbl
  constructor
  · unfold uTotal
    apply Dg_sumSP
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Dg_scaleSP _ (h1 (fun _ => 0)).1
    · exact (h2 (fun _ => 0)).1
  · intro y
    unfold uTotal
    rw [ev_sumSP]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ev_scaleSP]
    rw [(h1 y).2, (h2 y).2, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => list_sum_lin _ _ _ _

theorem uTotal_nonneg {cons : List (List (List SP))} {blocks : List GBlock} {grid s2 cd : ℤ}
    (hg : 0 < grid) (hs : 0 < s2) (h2 : (2 : ℤ) ∣ s2) (hcd : 0 < cd)
    (hcons : ConsDg 16 cons) (hbl : ∀ b ∈ blocks, AtomsDg 16 b)
    (hgram : ∀ b ∈ blocks, b.gramOK cd = true) {y : ℕ → ℝ}
    (hpsd : ∀ c < cons.length, Psd y (cons.getD c [])) :
    0 ≤ ev y (uTotal grid s2 cd cons blocks) := by
  rw [(uTotal_spec grid s2 cd hcons hbl).2 y]
  refine Finset.sum_nonneg fun c hc => List.sum_nonneg fun r hr => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hr
  have hb' := List.mem_filter.1 hb
  exact blockVal_nonneg hg hs h2 hcd (hpsd c (Finset.mem_range.1 hc)) (hgram b hb'.1)

/-! ### The soundness theorem -/

theorem go_sound {cons : List (List (List SP))} {acts : List (List ℕ × List ℤ)} {lit : SP}
    {grid s2 cd : ℤ} {blocks : List GBlock}
    (hchk : check cons acts lit grid s2 cd blocks = true) (x : ℕ → ℝ)
    (hpsd : ∀ g ∈ acts, ∀ c < cons.length, Psd (act g x) (cons.getD c [])) :
    0 ≤ ev x lit := by
  unfold check at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hcd, hg⟩, hs⟩, h2m⟩, ha0⟩, hacts⟩, hcdg⟩, hatoms⟩, hgram⟩, heq⟩ := hchk
  have h2 : (2 : ℤ) ∣ s2 := Int.dvd_of_emod_eq_zero h2m
  have hcons : ConsDg 16 cons := consDg_of hcdg
  have hbl : ∀ b ∈ blocks, AtomsDg 16 b := fun b hb => atomsDg_of (hatoms b hb)
  set U := uTotal grid s2 cd cons blocks with hU
  have hUd : Dg 255 U := Dg_mono (by norm_num) (uTotal_spec grid s2 cd hcons hbl).1
  have hmi : ∀ g ∈ acts, ∀ i < 19, g.1.getD i 0 < 19 := by
    intro g hg i hi
    have := hacts g hg i (List.mem_range.2 hi)
    exact this
  have heq' := eqSP_sound _ _ heq
  have h0 : ev x (sumSP [sumSP (acts.map fun g => actSP g U), scaleSP (-((acts.length : ℤ) * cd)) lit]) = 0 := by
    rw [heq']; simp
  rw [ev_sumSP] at h0
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ev_scaleSP, ev_sumSP,
    List.map_map] at h0
  have hl : ((acts.map ((ev x) ∘ fun g => actSP g U))).sum = (acts.map fun g => ev (act g x) U).sum := by
    refine congrArg List.sum (List.map_congr_left fun g hg => ?_)
    exact ev_actSP g (hmi g hg) x U hUd
  rw [hl] at h0
  have hnn : 0 ≤ (acts.map fun g => ev (act g x) U).sum := by
    refine List.sum_nonneg fun r hr => ?_
    obtain ⟨g, hgm, rfl⟩ := List.mem_map.1 hr
    exact uTotal_nonneg hg hs h2 hcd hcons hbl (fun b hb => hgram b hb) (hpsd g hgm)
  have hpos : (0 : ℝ) < (acts.length : ℝ) * cd := by
    have : (0 : ℝ) < acts.length := by exact_mod_cast ha0
    have : (0 : ℝ) < cd := by exact_mod_cast hcd
    positivity
  push_cast at h0
  nlinarith

end FormalResearch.FourQubitEntropy.GOProbe
