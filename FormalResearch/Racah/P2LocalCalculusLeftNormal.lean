module

public import Mathlib
public import FormalResearch.Racah.P2LocalCalculusSeries

/-!
# Local calculus: left-normal operators, the recursion for `𝒢_{2r}`, and the start (Weyl P2, `prop:localcalculus`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, appendix `app:localgeneral`, `eq:3jJoperator`,
`eq:3jB2r`, `eq:3jD2rrecursive`, `prop:localcalculus` (a) and (b).

Abstract setting (as in `P2LocalCalculus`): `K` a field of characteristic zero, `M` a `K`-module,
`x, D, H ∈ End_K(M)` with `[D, x] = 1` (`x` multiplication by the cosine, `D = ∂_x`, `H = 𝖧₀`), and a
subalgebra `C ⊆ End_K(M)` of "multiplication operators": its elements commute with `x`, it contains
`x`, and it is stable under `c ↦ [D, c]` (the derivative of the multiplier).  `LN` is the
`K`-span of the left-normal monomials `c D^j`, `c ∈ C` (the paper's left-normal operators
`∑ b_j(x) ∂_x^j`).

* `LN_mul_mem`, `lnAlg`: `LN` is a subalgebra (left-normal operators form a ring);
* `comm_mem`, `Ns_mem`, `Bop_mem`: `[x, ·]`, `𝒩_s[·]` and `𝖡_{r}` of `eq:3jB2r` preserve `LN`;
* `exists_comm_eq`: `[x, ·]` is onto `LN` (`eq:3jJoperator`, via `commutator_J`), so `𝒥(𝖡)` exists in `LN`;
* `exists_solution`: **`prop:localcalculus` (a)**, the recursion `𝒢_{r+1} = 𝒥(𝖡_{r+1}) + ψ_{r+1}`
  (`eq:3jD2rrecursive`) for every multiplier rule `ψ_{r+1} = Ψ(r+1, 𝖡_{r+1}) ∈ C`;
* `exists_mult_eq`: if `D d₀ = w d₀` with `w ∈ C` (`d₀` the extremal Wigner function), every
  `T ∈ LN` acts on `d₀` as a multiplier, `T d₀ = ψ d₀`, `ψ ∈ C` (the pointwise division of `eq:3jpsi2r`);
* `local_calculus_start` (**`prop:localcalculus` (b)**, `eq:3jpsi2r`): for prescribed multipliers `κ_r ∈ C`
  the multipliers `ψ_r` can be chosen so that `𝒢_r d₀ = κ_r d₀` for all `r`, and then the formal series
  `∑ t^r 𝒢_r d_k` is the unique solution of the rank recurrence with start `d₀ ∑ κ_r t^r`
  (`local_calculus_start_unique`).

The paper's `ψ_{2r} = κ_r - 𝒥(𝖡_{2r}) d₀ / d₀` is exactly the multiplier `ψ ∈ C` with
`ψ d₀ = κ_r d₀ - 𝒥(𝖡_{2r}) d₀`.  Not formalised here: the analytic content (functions, convergence), see
`P2LocalCalculusWigner`.
-/

@[expose] public section

namespace FormalResearch.Racah.LocalCalculus

open Polynomial Module

section LeftNormal

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]
variable (D : End K M) (C : Subalgebra K (End K M))

/-- The left-normal monomials `c D^j`, `c ∈ C`. -/
def lnGen : Set (End K M) := {T | ∃ c ∈ C, ∃ j : ℕ, T = c * D ^ j}

/-- Left-normal operators: the `K`-span of `c D^j`, `c ∈ C`. -/
def LN : Submodule K (End K M) := Submodule.span K (lnGen D C)

variable {D C}

lemma mem_LN_gen {c : End K M} (hc : c ∈ C) (j : ℕ) : c * D ^ j ∈ LN D C :=
  Submodule.subset_span ⟨c, hc, j, rfl⟩

lemma C_le_LN {c : End K M} (hc : c ∈ C) : c ∈ LN D C := by
  simpa using mem_LN_gen (D := D) hc 0

lemma D_mem_LN : D ∈ LN D C := by simpa using mem_LN_gen (D := D) C.one_mem 1

lemma LN_mul_left {c T : End K M} (hc : c ∈ C) (hT : T ∈ LN D C) : c * T ∈ LN D C := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨c', hc', j, rfl⟩ := hT
    rw [← mul_assoc]; exact mem_LN_gen (C.mul_mem hc hc') j
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | smul a T _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h

lemma LN_mul_D {T : End K M} (hT : T ∈ LN D C) : T * D ∈ LN D C := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨c', hc', j, rfl⟩ := hT
    rw [mul_assoc, ← pow_succ]; exact mem_LN_gen hc' _
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul a T _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h

lemma LN_mul_D_pow {T : End K M} (hT : T ∈ LN D C) (i : ℕ) : T * D ^ i ∈ LN D C := by
  induction i with
  | zero => simpa using hT
  | succ i ih => rw [pow_succ, ← mul_assoc]; exact LN_mul_D ih

lemma LN_D_mul (hCD : ∀ c ∈ C, D * c - c * D ∈ C) {T : End K M} (hT : T ∈ LN D C) :
    D * T ∈ LN D C := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨c', hc', j, rfl⟩ := hT
    have : D * (c' * D ^ j) = (D * c' - c' * D) * D ^ j + c' * D ^ (j + 1) := by
      rw [pow_succ']; noncomm_ring
    rw [this]
    exact add_mem (mem_LN_gen (hCD c' hc') j) (mem_LN_gen hc' _)
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | smul a T _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h

lemma LN_D_pow_mul_C (hCD : ∀ c ∈ C, D * c - c * D ∈ C) {c : End K M} (hc : c ∈ C) (j : ℕ) :
    D ^ j * c ∈ LN D C := by
  induction j with
  | zero => simpa using C_le_LN hc
  | succ j ih => rw [pow_succ', mul_assoc]; exact LN_D_mul hCD ih

/-- Left-normal operators are closed under products. -/
theorem LN_mul_mem (hCD : ∀ c ∈ C, D * c - c * D ∈ C) {T T' : End K M} (hT : T ∈ LN D C)
    (hT' : T' ∈ LN D C) : T * T' ∈ LN D C := by
  induction hT' using Submodule.span_induction with
  | mem T' hT' =>
    obtain ⟨c', hc', j', rfl⟩ := hT'
    induction hT using Submodule.span_induction with
    | mem T hT =>
      obtain ⟨c, hc, j, rfl⟩ := hT
      have : c * D ^ j * (c' * D ^ j') = c * (D ^ j * c') * D ^ j' := by noncomm_ring
      rw [this]
      exact LN_mul_D_pow (LN_mul_left hc (LN_D_pow_mul_C hCD hc' j)) _
    | zero => simp
    | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
    | smul a T _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | smul a T _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h

/-- The ring of left-normal operators. -/
def lnAlg (hCD : ∀ c ∈ C, D * c - c * D ∈ C) : Subalgebra K (End K M) where
  carrier := LN D C
  mul_mem' := fun ha hb => LN_mul_mem hCD ha hb
  one_mem' := C_le_LN C.one_mem
  add_mem' := fun ha hb => add_mem ha hb
  zero_mem' := zero_mem _
  algebraMap_mem' := fun r => C_le_LN (C.algebraMap_mem r)

lemma aeval_mem_LN (hCD : ∀ c ∈ C, D * c - c * D ∈ C) {H : End K M} (hH : H ∈ LN D C) (p : K[X]) :
    aeval H p ∈ LN D C := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
    rw [aeval_monomial]
    exact (lnAlg hCD).mul_mem ((lnAlg hCD).algebraMap_mem a) ((lnAlg hCD).pow_mem hH n)

/-- Normal form of a left-normal operator: `T = ∑_{j ≤ J} b_j D^j` with `b_j ∈ C`. -/
theorem exists_rep {T : End K M} (hT : T ∈ LN D C) :
    ∃ (J : ℕ) (b : ℕ → End K M), (∀ j, b j ∈ C) ∧ T = leftNormal D b J := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨c, hc, j, rfl⟩ := hT
    refine ⟨j, fun i => if i = j then c else 0, fun i => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact hc
      · exact C.zero_mem
    · simp [leftNormal, Finset.sum_ite_eq']
  | zero => exact ⟨0, fun _ => 0, fun _ => C.zero_mem, by simp [leftNormal]⟩
  | add a b _ _ ha hb =>
    obtain ⟨J, f, hf, rfl⟩ := ha
    obtain ⟨J', g, hg, rfl⟩ := hb
    refine ⟨max J J', fun j => (if j ≤ J then f j else 0) + (if j ≤ J' then g j else 0),
      fun j => C.add_mem (by split_ifs; exacts [hf j, C.zero_mem])
        (by split_ifs; exacts [hg j, C.zero_mem]), ?_⟩
    have e1 : ∀ (h : ℕ → End K M) (J N : ℕ), J ≤ N →
        leftNormal D (fun j => if j ≤ J then h j else 0) N = leftNormal D h J := by
      intro h J N hJN
      unfold leftNormal
      simp only [ite_mul, zero_mul]
      rw [← Finset.sum_filter]
      congr 1
      ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
    unfold leftNormal at *
    simp only [add_mul, Finset.sum_add_distrib]
    have := e1 f J (max J J') (le_max_left _ _)
    have := e1 g J' (max J J') (le_max_right _ _)
    unfold leftNormal at *
    simp only [ite_mul, zero_mul] at *
    congr 1 <;> simp_all
  | smul a T _ h =>
    obtain ⟨J, f, hf, rfl⟩ := h
    refine ⟨J, fun j => a • f j, fun j => C.smul_mem (hf j) a, ?_⟩
    simp [leftNormal, Finset.smul_sum]

variable {x : End K M}

/-- `[x, ·]` preserves `LN`, when `x` commutes with `C` and `[D, x] = 1`. -/
theorem comm_mem [CharZero K] (hD : D * x - x * D = 1) (hCx : ∀ c ∈ C, x * c = c * x)
    {T : End K M} (hT : T ∈ LN D C) : comm x T ∈ LN D C := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨c, hc, j, rfl⟩ := hT
    cases j with
    | zero => simp [comm, hCx c hc]
    | succ n =>
      have h := derivPow_mul_x x D hD n
      have : comm x (c * D ^ (n + 1)) = -(((n : K) + 1) • (c * D ^ n)) := by
        unfold comm
        rw [← mul_assoc, hCx c hc, mul_assoc, mul_assoc, h, mul_add, mul_smul_comm]
        simp
      rw [this]
      exact neg_mem (Submodule.smul_mem _ _ (mem_LN_gen hc n))
  | zero => simp [comm]
  | add a b _ _ ha hb =>
    have : comm x (a + b) = comm x a + comm x b := by simp [comm, mul_add, add_mul]; abel
    rw [this]; exact add_mem ha hb
  | smul a T _ h =>
    have : comm x (a • T) = a • comm x T := by simp [comm, smul_sub]
    rw [this]; exact Submodule.smul_mem _ _ h

/-- **`eq:3jJoperator`**: every left-normal `𝖡` is `[x, 𝒥(𝖡)]` for a left-normal `𝒥(𝖡)`. -/
theorem exists_comm_eq [CharZero K] (hD : D * x - x * D = 1) (hCx : ∀ c ∈ C, x * c = c * x)
    {B : End K M} (hB : B ∈ LN D C) : ∃ S ∈ LN D C, comm x S = B := by
  obtain ⟨J, b, hb, rfl⟩ := exists_rep hB
  refine ⟨Jop D b J, ?_, commutator_J x D hD b (fun j => hCx _ (hb j)) J⟩
  unfold Jop
  exact neg_mem (sum_mem fun j _ => Submodule.smul_mem _ _ (mem_LN_gen (hb j) _))

/-- `𝒩_s[·]` preserves left-normal operators (for left-normal `𝖧₀`). -/
theorem Ns_mem [CharZero K] (hD : D * x - x * D = 1) (hCx : ∀ c ∈ C, x * c = c * x)
    (hCD : ∀ c ∈ C, D * c - c * D ∈ C) (hxC : x ∈ C) {H A : End K M} (hH : H ∈ LN D C)
    (hA : A ∈ LN D C) (τ : K) (π πt : K[X]) : Ns x H A τ π πt ∈ LN D C := by
  have hx : x ∈ LN D C := C_le_LN hxC
  have h1 := aeval_mem_LN hCD hH π
  have h2 := aeval_mem_LN hCD hH πt
  unfold Ns
  refine sub_mem (sub_mem (LN_mul_mem hCD (LN_mul_mem hCD hx hA) h1)
    (Submodule.smul_mem _ _ (LN_mul_mem hCD hA h2))) (Submodule.smul_mem _ _ (add_mem ?_ ?_))
  · exact comm_mem hD hCx (LN_mul_mem hCD hA h1)
  · exact LN_mul_mem hCD (comm_mem hD hCx hA) h1

/-- `𝖡_{r+1}` of `eq:3jB2r` is left-normal when `𝒢_0, …, 𝒢_r` are. -/
theorem Bop_mem [CharZero K] (hD : D * x - x * D = 1) (hCx : ∀ c ∈ C, x * c = c * x)
    (hCD : ∀ c ∈ C, D * c - c * D ∈ C) (hxC : x ∈ C) {H : End K M} (hH : H ∈ LN D C) (q : K[X])
    (e : ℕ → K) (τ : K) {g : ℕ → End K M} {r : ℕ} (hg : ∀ n ≤ r, g n ∈ LN D C) :
    Bop x H q e τ g r ∈ LN D C := by
  unfold Bop
  refine add_mem (LN_mul_mem hCD (hg r le_rfl) (aeval_mem_LN hCD hH q)) (sum_mem fun s hs => ?_)
  exact Submodule.smul_mem _ _ (Ns_mem hD hCx hCD hxC hH (hg _ (Nat.sub_le _ _)) _ _ _)

open Classical in
/-- A chosen left-normal `𝒥(𝖡)` with `[x, 𝒥(𝖡)] = 𝖡` (`0` when none exists). -/
noncomputable def Jsol (x D : End K M) (C : Subalgebra K (End K M)) (B : End K M) : End K M :=
  if h : ∃ S ∈ LN D C, comm x S = B then h.choose else 0

theorem Jsol_spec [CharZero K] (hD : D * x - x * D = 1) (hCx : ∀ c ∈ C, x * c = c * x)
    {B : End K M} (hB : B ∈ LN D C) : Jsol x D C B ∈ LN D C ∧ comm x (Jsol x D C B) = B := by
  have h := exists_comm_eq hD hCx hB
  unfold Jsol
  rw [dif_pos h]
  exact ⟨h.choose_spec.1, h.choose_spec.2⟩

/-- The sequence `𝒢_r` of `eq:3jD2rrecursive`, prefix by prefix: `step i B` is the choice of
`𝒢_i` given `𝖡_i = B`. -/
noncomputable def Fseq [CharZero K] (x H : End K M) (q : K[X]) (e : ℕ → K) (τ : K)
    (step : ℕ → End K M → End K M) : ℕ → ℕ → End K M
  | 0 => fun n => if n = 0 then 1 else 0
  | r + 1 => Function.update (Fseq x H q e τ step r) (r + 1)
      (step (r + 1) (Bop x H q e τ (Fseq x H q e τ step r) r))

/-- `𝒢_r = Fseq r r`. -/
noncomputable def Gseq [CharZero K] (x H : End K M) (q : K[X]) (e : ℕ → K) (τ : K)
    (step : ℕ → End K M → End K M) (r : ℕ) : End K M := Fseq x H q e τ step r r

lemma Fseq_apply_le [CharZero K] (x H : End K M) (q : K[X]) (e : ℕ → K) (τ : K)
    (step : ℕ → End K M → End K M) (r : ℕ) : ∀ n ≤ r, Fseq x H q e τ step r n = Gseq x H q e τ step n := by
  induction r with
  | zero => intro n hn; obtain rfl : n = 0 := by omega
            rfl
  | succ r ih =>
    intro n hn
    by_cases hnr : n = r + 1
    · subst hnr; rfl
    · rw [Fseq, Function.update_of_ne hnr]; exact ih n (by omega)

lemma Gseq_zero [CharZero K] (x H : End K M) (q : K[X]) (e : ℕ → K) (τ : K)
    (step : ℕ → End K M → End K M) : Gseq x H q e τ step 0 = 1 := by
  simp [Gseq, Fseq]

lemma Gseq_succ [CharZero K] (x H : End K M) (q : K[X]) (e : ℕ → K) (τ : K)
    (step : ℕ → End K M → End K M) (r : ℕ) :
    Gseq x H q e τ step (r + 1) = step (r + 1) (Bop x H q e τ (Gseq x H q e τ step) r) := by
  have : Gseq x H q e τ step (r + 1) =
      step (r + 1) (Bop x H q e τ (Fseq x H q e τ step r) r) := by
    simp [Gseq, Fseq]
  rw [this]
  congr 1
  exact Bop_congr x H q e τ (fun n hn => Fseq_apply_le x H q e τ step r n hn)

/-- **`prop:localcalculus` (a)**: the recursion `𝒢_{r+1} = 𝒥(𝖡_{r+1}) + ψ_{r+1}` of `eq:3jD2rrecursive`
exists, for every multiplier rule `ψ_{r+1} = Ψ(r+1, 𝖡_{r+1}) ∈ C`, with all `𝒢_r` left-normal and
`[x, 𝒢_{r+1}] = 𝖡_{r+1}` (`eq:3jB2r`), hence (by `local_calculus_series`) the formal series
`∑ t^r 𝒢_r d_k` solves the deformed rank recurrence. -/
theorem exists_solution [CharZero K] (hD : D * x - x * D = 1) (hCx : ∀ c ∈ C, x * c = c * x)
    (hCD : ∀ c ∈ C, D * c - c * D ∈ C) (hxC : x ∈ C) {H : End K M} (hH : H ∈ LN D C) (q : K[X])
    (e : ℕ → K) (τ : K) (Ψ : ℕ → End K M → End K M) (hΨ : ∀ i B, B ∈ LN D C → Ψ i B ∈ C) :
    ∃ G : ℕ → End K M, G 0 = 1 ∧ (∀ r, G r ∈ LN D C) ∧
      (∀ r, comm x (G (r + 1)) = Bop x H q e τ G r) ∧
      ∀ r, G (r + 1) = Jsol x D C (Bop x H q e τ G r) + Ψ (r + 1) (Bop x H q e τ G r) := by
  set step : ℕ → End K M → End K M := fun i B => Jsol x D C B + Ψ i B with hstep
  set G := Gseq x H q e τ step with hG
  have hG0 : G 0 = 1 := Gseq_zero x H q e τ step
  have hGs : ∀ r, G (r + 1) = Jsol x D C (Bop x H q e τ G r) + Ψ (r + 1) (Bop x H q e τ G r) :=
    fun r => Gseq_succ x H q e τ step r
  have hmem : ∀ r, ∀ n ≤ r, G n ∈ LN D C := by
    intro r
    induction r with
    | zero => intro n hn; obtain rfl : n = 0 := by omega
              rw [hG0]; exact C_le_LN C.one_mem
    | succ r ih =>
      intro n hn
      by_cases hnr : n = r + 1
      · subst hnr
        have hB := Bop_mem hD hCx hCD hxC hH q e τ ih
        rw [hGs]
        exact add_mem (Jsol_spec hD hCx hB).1 (C_le_LN (hΨ _ _ hB))
      · exact ih n (by omega)
  refine ⟨G, hG0, fun r => hmem r r le_rfl, fun r => ?_, hGs⟩
  have hB := Bop_mem hD hCx hCD hxC hH q e τ (hmem r)
  rw [hGs r]
  have h1 := (Jsol_spec hD hCx hB).2
  have h2 : comm x (Ψ (r + 1) (Bop x H q e τ G r)) = 0 := by
    have := hCx _ (hΨ (r + 1) _ hB); simp [comm, this]
  have : comm x (Jsol x D C (Bop x H q e τ G r) + Ψ (r + 1) (Bop x H q e τ G r)) =
      comm x (Jsol x D C (Bop x H q e τ G r)) + comm x (Ψ (r + 1) (Bop x H q e τ G r)) := by
    simp [comm, mul_add, add_mul]; abel
  rw [this, h1, h2, add_zero]

/-- If `D d₀ = w d₀` with `w ∈ C`, then `D^j d₀ = u_j d₀` with `u_j ∈ C`. -/
lemma D_pow_apply_C (hCD : ∀ c ∈ C, D * c - c * D ∈ C) {d0 : M} {w : End K M} (hw : w ∈ C)
    (hdw : D d0 = w d0) (j : ℕ) : ∃ u ∈ C, (D ^ j) d0 = u d0 := by
  induction j with
  | zero => exact ⟨1, C.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨u, hu, hj⟩ := ih
    refine ⟨(D * u - u * D) + u * w, C.add_mem (hCD u hu) (C.mul_mem hu hw), ?_⟩
    rw [pow_succ', Module.End.mul_apply, hj]
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, hdw]
    abel

/-- **The pointwise division of `eq:3jpsi2r`.**  If `D d₀ = w d₀` with `w ∈ C` (for the extremal Wigner
function `d₀`, `w = d₀'/d₀` is rational), every left-normal `T` acts on `d₀` as a multiplier:
`T d₀ = ψ d₀` for some `ψ ∈ C` (`ψ = T d₀ / d₀`). -/
theorem exists_mult_eq (hCD : ∀ c ∈ C, D * c - c * D ∈ C) {d0 : M} {w : End K M} (hw : w ∈ C)
    (hdw : D d0 = w d0) {T : End K M} (hT : T ∈ LN D C) : ∃ ψ ∈ C, T d0 = ψ d0 := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨c, hc, j, rfl⟩ := hT
    obtain ⟨u, hu, hj⟩ := D_pow_apply_C hCD hw hdw j
    exact ⟨c * u, C.mul_mem hc hu, by rw [Module.End.mul_apply, hj]; rfl⟩
  | zero => exact ⟨0, C.zero_mem, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨ψ, hψ, h1⟩ := ha
    obtain ⟨ψ', hψ', h2⟩ := hb
    exact ⟨ψ + ψ', C.add_mem hψ hψ', by simp [h1, h2]⟩
  | smul a T _ h =>
    obtain ⟨ψ, hψ, h1⟩ := h
    exact ⟨a • ψ, C.smul_mem hψ a, by simp [h1]⟩

/-- **`prop:localcalculus` (b)** (`eq:3jpsi2r`).  Let `d₀` be a vector with `D d₀ = w d₀`, `w ∈ C` (the
extremal Wigner function), and let `κ_r ∈ C` (`κ_0 = 1`) be prescribed multipliers.  Then the
multipliers `ψ_{r+1}` of the recursion `𝒢_{r+1} = 𝒥(𝖡_{r+1}) + ψ_{r+1}` can be chosen in `C` so that
`𝒢_r d₀ = κ_r d₀` for all `r`: `ψ_{r+1} d₀ = κ_{r+1} d₀ - 𝒥(𝖡_{r+1}) d₀`, i.e. the paper's
`ψ_{2r} = κ_r - 𝒥(𝖡_{2r}) d₀ / d₀`, and `𝖡_{r+1}` involves only `ψ_{r'}` with `r' ≤ r` (the recursion
is not circular). -/
theorem local_calculus_start [CharZero K] (hD : D * x - x * D = 1) (hCx : ∀ c ∈ C, x * c = c * x)
    (hCD : ∀ c ∈ C, D * c - c * D ∈ C) (hxC : x ∈ C) {H : End K M} (hH : H ∈ LN D C) (q : K[X])
    (e : ℕ → K) (τ : K) {d0 : M} {w : End K M} (hw : w ∈ C) (hdw : D d0 = w d0)
    (κ : ℕ → End K M) (hκ : ∀ r, κ r ∈ C) (hκ0 : κ 0 = 1) :
    ∃ G : ℕ → End K M, G 0 = 1 ∧ (∀ r, G r ∈ LN D C) ∧
      (∀ r, comm x (G (r + 1)) = Bop x H q e τ G r) ∧ (∀ r, G r d0 = κ r d0) ∧
      ∀ r, ∃ ψ ∈ C, G (r + 1) = Jsol x D C (Bop x H q e τ G r) + ψ ∧
        ψ d0 = κ (r + 1) d0 - Jsol x D C (Bop x H q e τ G r) d0 := by
  classical
  let Ψ : ℕ → End K M → End K M := fun i B =>
    if h : κ i - Jsol x D C B ∈ LN D C then (exists_mult_eq hCD hw hdw h).choose else 0
  have hΨ : ∀ i B, B ∈ LN D C → Ψ i B ∈ C := by
    intro i B hB
    have hJ := (Jsol_spec hD hCx hB).1
    have h : κ i - Jsol x D C B ∈ LN D C := sub_mem (C_le_LN (hκ i)) hJ
    simp only [Ψ, dif_pos h]
    exact (exists_mult_eq hCD hw hdw h).choose_spec.1
  obtain ⟨G, hG0, hGm, hGB, hGs⟩ := exists_solution hD hCx hCD hxC hH q e τ Ψ hΨ
  have hpsi : ∀ r, Ψ (r + 1) (Bop x H q e τ G r) ∈ C ∧
      Ψ (r + 1) (Bop x H q e τ G r) d0 = κ (r + 1) d0 - Jsol x D C (Bop x H q e τ G r) d0 := by
    intro r
    have hB := Bop_mem hD hCx hCD hxC hH q e τ (g := G) (r := r) (fun n _ => hGm n)
    have hJ := (Jsol_spec hD hCx hB).1
    have h : κ (r + 1) - Jsol x D C (Bop x H q e τ G r) ∈ LN D C := sub_mem (C_le_LN (hκ _)) hJ
    refine ⟨hΨ _ _ hB, ?_⟩
    have hc := (exists_mult_eq hCD hw hdw h).choose_spec.2
    simp only [Ψ, dif_pos h]
    rw [← hc]; simp
  refine ⟨G, hG0, hGm, hGB, fun r => ?_, fun r => ⟨_, (hpsi r).1, hGs r, (hpsi r).2⟩⟩
  cases r with
  | zero => rw [hG0, hκ0]
  | succ r => rw [hGs r, LinearMap.add_apply, (hpsi r).2]; abel

/-- The vector `d_{n-1}` of rank index `n` (`d_{-1} = 0`). -/
def prevV (d : ℕ → M) : ℕ → M
  | 0 => 0
  | n + 1 => d n

/-- **`prop:localcalculus` (a) at all ranks.**  For a family `d_n` (rank `k₀ + n`) with the eigen-equations
`𝖧₀d_n = λ_{k₀+n}d_n` and the Wigner rank recurrence at every rank (the term `d_{-1}` is multiplied by
`R_0`, which vanishes at a one-sided start), the formal series `Φ_n = ∑_r t^r 𝒢_r d_n` satisfy the deformed
rank recurrence `eq:generalrankrec` at every rank. -/
theorem local_calculus_ranks [CharZero K] (x H : End K M) (q : K[X]) (e : ℕ → K) (he0 : e 0 = 1)
    (G : ℕ → End K M) (hG0 : G 0 = 1) (τ k0 : K) (R : ℕ → K) (d : ℕ → M)
    (hH : ∀ n : ℕ, H (d n) = lam (k0 + n) • d n)
    (hW : ∀ n : ℕ, ((k0 + n) * R (n + 1)) • d (n + 1) + ((k0 + n + 1) * R n) • prevV d n =
      (2 * (k0 + n) + 1) • (lam (k0 + n) • x (d n) - τ • d n))
    (hB : ∀ r, comm x (G (r + 1)) = Bop x H q e τ G r) (n : ℕ) :
    rankDefect x q e τ k0 R (fun n => serG G (d n)) n = 0 := by
  have hz : ∀ n, prevS (fun n => serG G (d n)) n = serG G (prevV d n) := by
    intro n; cases n with
    | zero => funext r; simp [serG, prevV, prevS]
    | succ n => rfl
  unfold rankDefect
  rw [hz n]
  refine local_calculus_series x H q e he0 G hG0 (k0 + n) (R n) (R (n + 1)) τ (prevV d n) (d n)
    (d (n + 1)) (hW n) ?_ (hH n) ?_ hB
  · cases n with
    | zero => simp [prevV]
    | succ n =>
      have : k0 + ((n + 1 : ℕ) : K) - 1 = k0 + n := by push_cast; ring
      rw [this]; exact hH n
  · have : k0 + (n : K) + 1 = k0 + ((n + 1 : ℕ) : K) := by push_cast; ring
    rw [this]; exact hH (n + 1)

/-- **`prop:localcalculus` (a) and (b), abstract all-order statement.**  Under the hypotheses of the
paper's setting (`R_{k₀} = 0` at the one-sided start, `k₀R_{k₀+1} ≠ 0`, nonzero forward coefficients, and
`D d₀ = w d₀`, `w ∈ C`, for `d₀ = d_{k₀}`), for any multipliers `κ_r ∈ C` (`κ_0 = 1`) there are left-normal
operators `𝒢_r = 𝒥(𝖡_r) + ψ_r` (`𝒢_0 = 1`, `[x, 𝒢_{r+1}] = 𝖡_{r+1}`) with
`𝒢_r d₀ = κ_r d₀`, such that the formal series `Φ_n = ∑_r t^r 𝒢_r d_n` solve the deformed rank recurrence
at every rank, and they are the *only* formal solution with the start `Φ_0 = ∑_r t^r κ_r d₀`. -/
theorem prop_localcalculus [CharZero K] (hD : D * x - x * D = 1) (hCx : ∀ c ∈ C, x * c = c * x)
    (hCD : ∀ c ∈ C, D * c - c * D ∈ C) (hxC : x ∈ C) {H : End K M} (hH : H ∈ LN D C) (q : K[X])
    (e : ℕ → K) (he0 : e 0 = 1) (τ k0 : K) (R : ℕ → K) (hR0 : R 0 = 0)
    (hfwd : ∀ n : ℕ, (k0 + n) * R (n + 1) ≠ 0) (d : ℕ → M)
    (hHd : ∀ n : ℕ, H (d n) = lam (k0 + n) • d n)
    (hW : ∀ n : ℕ, ((k0 + n) * R (n + 1)) • d (n + 1) + ((k0 + n + 1) * R n) • prevV d n =
      (2 * (k0 + n) + 1) • (lam (k0 + n) • x (d n) - τ • d n))
    {w : End K M} (hw : w ∈ C) (hdw : D (d 0) = w (d 0))
    (κ : ℕ → End K M) (hκ : ∀ r, κ r ∈ C) (hκ0 : κ 0 = 1) :
    ∃ G : ℕ → End K M, G 0 = 1 ∧ (∀ r, G r ∈ LN D C) ∧
      (∀ r, comm x (G (r + 1)) = Bop x H q e τ G r) ∧ (∀ r, G r (d 0) = κ r (d 0)) ∧
      (∀ n, rankDefect x q e τ k0 R (fun n => serG G (d n)) n = 0) ∧
      ∀ Φ' : ℕ → ℕ → M, (∀ n, rankDefect x q e τ k0 R Φ' n = 0) →
        Φ' 0 = (fun r => κ r (d 0)) → Φ' = fun n => serG G (d n) := by
  obtain ⟨G, hG0, hGm, hGB, hGκ, -⟩ := local_calculus_start hD hCx hCD hxC hH q e τ hw hdw κ hκ hκ0
  refine ⟨G, hG0, hGm, hGB, hGκ, local_calculus_ranks x H q e he0 G hG0 τ k0 R d hHd hW hGB, ?_⟩
  intro Φ' hΦ' h0
  refine rank_unique_of_start x q e he0 τ k0 R hR0 hfwd hΦ'
    (local_calculus_ranks x H q e he0 G hG0 τ k0 R d hHd hW hGB) ?_ 
  rw [h0]; funext r; exact (hGκ r).symm

end LeftNormal

end FormalResearch.Racah.LocalCalculus

/-- info: 'FormalResearch.Racah.LocalCalculus.exists_comm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.exists_comm_eq

/-- info: 'FormalResearch.Racah.LocalCalculus.exists_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.exists_solution

/-- info: 'FormalResearch.Racah.LocalCalculus.local_calculus_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.local_calculus_start

/-- info: 'FormalResearch.Racah.LocalCalculus.local_calculus_ranks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.local_calculus_ranks

/-- info: 'FormalResearch.Racah.LocalCalculus.prop_localcalculus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.prop_localcalculus
