module

public import FormalResearch.Racah.P2ThreeJHahn

/-!
# The Hahn three-term recurrence in the degree (Weyl P2)

Finite-sum identity (DLMF 18.22.15 for the Hahn polynomials `Q_n(u;α,β,D)`, `eq:HahnDefinitionPaper`):
`-u Q_n(u) = A_n Q_{n+1}(u) - (A_n + C_n) Q_n(u) + C_n Q_{n-1}(u)` for `n < D`, with
`A_n = (n+α+β+1)(n+α+1)(D-n)/((2n+α+β+1)(2n+α+β+2))`,
`C_n = n(n+α+β+D+1)(n+β)/((2n+α+β)(2n+α+β+1))`.
It is proved coefficientwise in the basis `(-u)_k`, using `u (-u)_k = -(-u)_{k+1} + k (-u)_k`.
-/

@[expose] public section

namespace FormalResearch.Racah

open Polynomial

/-- Hahn recurrence coefficient `A_n`. -/
noncomputable def hahnA (α β D n : ℕ) : ℝ :=
  ((n : ℝ) + α + β + 1) * ((n : ℝ) + α + 1) * ((D : ℝ) - n) /
    ((2 * (n : ℝ) + α + β + 1) * (2 * (n : ℝ) + α + β + 2))

/-- Hahn recurrence coefficient `C_n`. -/
noncomputable def hahnC (α β D n : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) + α + β + D + 1) * ((n : ℝ) + β) /
    ((2 * (n : ℝ) + α + β) * (2 * (n : ℝ) + α + β + 1))

/-- The coefficient of `(-u)_k` in `Q_m`. -/
noncomputable def hc (α β D m k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval (-(m : ℝ)) * (ascPochhammer ℝ k).eval ((m : ℝ) + α + β + 1) /
    ((ascPochhammer ℝ k).eval ((α : ℝ) + 1) * (ascPochhammer ℝ k).eval (-(D : ℝ)) *
      (k.factorial : ℝ))

lemma hc_eq_zero (α β D m k : ℕ) (h : m < k) : hc α β D m k = 0 := by
  unfold hc
  rw [ascPochhammer_eval_neg_coe_nat_of_lt h]
  simp

lemma hahnQ_eq_hc (α β D m u : ℕ) :
    hahnQ α β D m u =
      ∑ k ∈ Finset.range (m + 1), hc α β D m k * (ascPochhammer ℝ k).eval (-(u : ℝ)) := by
  unfold hahnQ hc
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma hahnQ_ext (α β D m u K : ℕ) (hK : m < K) :
    hahnQ α β D m u =
      ∑ k ∈ Finset.range K, hc α β D m k * (ascPochhammer ℝ k).eval (-(u : ℝ)) := by
  rw [hahnQ_eq_hc]
  apply Finset.sum_subset
  · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
  · intro k hk hk'
    simp only [Finset.mem_range, not_lt] at hk hk'
    rw [hc_eq_zero α β D m k (by omega)]; simp

lemma poch_A (x : ℝ) (i : ℕ) :
    (ascPochhammer ℝ (i + 2)).eval (x - 1) = (x - 1) * x * (ascPochhammer ℝ i).eval (x + 1) := by
  rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp]
  simp only [eval_add, eval_X, eval_one]
  rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp]
  simp only [eval_add, eval_X, eval_one]
  rw [show x - 1 + 1 + 1 = x + 1 by ring, show x - 1 + 1 = x by ring]
  ring

lemma poch_B (x : ℝ) (i : ℕ) :
    (ascPochhammer ℝ (i + 2)).eval x = x * (x + i + 1) * (ascPochhammer ℝ i).eval (x + 1) := by
  rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp]
  simp only [eval_add, eval_X, eval_one]
  rw [ascPochhammer_succ_eval]
  ring

lemma poch_C (x : ℝ) (i : ℕ) :
    (ascPochhammer ℝ (i + 2)).eval (x + 1) =
      (x + i + 1) * (x + i + 2) * (ascPochhammer ℝ i).eval (x + 1) := by
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
  push_cast; ring

lemma poch_D (x : ℝ) (i : ℕ) :
    (ascPochhammer ℝ (i + 1)).eval x = x * (ascPochhammer ℝ i).eval (x + 1) := by
  rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp]
  simp only [eval_add, eval_X, eval_one]


lemma D_ne (D k : ℕ) (hk : k ≤ D) : (ascPochhammer ℝ k).eval (-(D : ℝ)) ≠ 0 := by
  rw [Ne, ascPochhammer_eval_eq_zero_iff]
  rintro ⟨r, hr, hrD⟩
  have : (r : ℝ) = D := by linarith
  have : r = D := by exact_mod_cast this
  omega

lemma al_pos (α k : ℕ) : 0 < (ascPochhammer ℝ k).eval ((α : ℝ) + 1) :=
  ascPochhammer_pos k _ (by positivity)

/-- The pointwise (coefficient) form of the Hahn recurrence, for `n = m+1`. -/
lemma hc_rec_succ (α β D m j : ℕ) (hj : j + 1 ≤ D) :
    hahnA α β D (m + 1) * hc α β D (m + 2) (j + 1) -
      (hahnA α β D (m + 1) + hahnC α β D (m + 1)) * hc α β D (m + 1) (j + 1) +
      hahnC α β D (m + 1) * hc α β D m (j + 1) + ((j : ℝ) + 1) * hc α β D (m + 1) (j + 1) -
      hc α β D (m + 1) j = 0 := by
  have hd1 := (al_pos α (j + 1)).ne'
  have hd0 := (al_pos α j).ne'
  have he1 := D_ne D (j + 1) hj
  have he0 := D_ne D j (by omega)
  have hf1 : ((j + 1).factorial : ℝ) ≠ 0 := by positivity
  have hf0 : (j.factorial : ℝ) ≠ 0 := by positivity
  rcases j with _ | i
  · simp only [hc, ascPochhammer_one, ascPochhammer_zero, eval_one, eval_X, Nat.factorial_zero,
      Nat.cast_one, zero_add, mul_one, Nat.factorial_one, hahnA, hahnC]
    push_cast
    have hD' : (D : ℝ) ≠ 0 := by
      have : D ≠ 0 := by omega
      exact_mod_cast this
    have h1 : (2 * ((m : ℝ) + 1) + α + β + 1) ≠ 0 := by positivity
    have h2 : (2 * ((m : ℝ) + 1) + α + β + 2) ≠ 0 := by positivity
    have h3 : (2 * ((m : ℝ) + 1) + α + β) ≠ 0 := by positivity
    have h4 : (α : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  · obtain ⟨x, hx⟩ : ∃ x : ℝ, x = -(((m + 1 : ℕ)) : ℝ) := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (((m + 1 : ℕ)) : ℝ) + α + β + 1 := ⟨_, rfl⟩
    have e1 : -((m + 2 : ℕ) : ℝ) = x - 1 := by rw [hx]; push_cast; ring
    have e2 : ((m + 2 : ℕ) : ℝ) + α + β + 1 = y + 1 := by rw [hy]; push_cast; ring
    have e3 : -((m : ℕ) : ℝ) = x + 1 := by rw [hx]; push_cast; ring
    have e4 : ((m : ℕ) : ℝ) + α + β + 1 = y - 1 := by rw [hy]; push_cast; ring
    have hd2 : (ascPochhammer ℝ (i + 2)).eval ((α : ℝ) + 1) =
        (ascPochhammer ℝ (i + 1)).eval ((α : ℝ) + 1) * ((α : ℝ) + 1 + (i + 1 : ℕ)) :=
      ascPochhammer_succ_eval (i + 1) _
    have he2 : (ascPochhammer ℝ (i + 2)).eval (-(D : ℝ)) =
        (ascPochhammer ℝ (i + 1)).eval (-(D : ℝ)) * (-(D : ℝ) + (i + 1 : ℕ)) :=
      ascPochhammer_succ_eval (i + 1) _
    have hf2 : (((i + 2).factorial : ℕ) : ℝ) = ((i : ℝ) + 2) * ((i + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    unfold hc
    rw [e1, e2, e3, e4, ← hx, ← hy, show i + 1 + 1 = i + 2 from rfl, poch_A x i, poch_B x i,
      poch_C x i, poch_C y i, poch_B y i, poch_A y i, poch_D x i, poch_D y i, hd2, he2, hf2]
    generalize (ascPochhammer ℝ i).eval (x + 1) = Gx
    generalize (ascPochhammer ℝ i).eval (y + 1) = Gy
    generalize (ascPochhammer ℝ (i + 1)).eval ((α : ℝ) + 1) = d at hd0 ⊢
    generalize (ascPochhammer ℝ (i + 1)).eval (-(D : ℝ)) = e at he0 ⊢
    generalize (((i + 1).factorial : ℕ) : ℝ) = f at hf0 ⊢
    have hDi : (-(D : ℝ) + ((i + 1 : ℕ) : ℝ)) ≠ 0 := by
      have : ((i + 1 : ℕ) : ℝ) + 1 ≤ D := by exact_mod_cast hj
      push_cast at this ⊢
      intro h; linarith
    have hai : (α : ℝ) + 1 + ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hi2 : ((i : ℝ) + 2) ≠ 0 := by positivity
    have h1 : (2 * ((m : ℝ) + 1) + α + β + 1) ≠ 0 := by positivity
    have h2 : (2 * ((m : ℝ) + 1) + α + β + 2) ≠ 0 := by positivity
    have h3 : (2 * ((m : ℝ) + 1) + α + β) ≠ 0 := by positivity
    unfold hahnA hahnC
    rw [hx, hy]
    push_cast at hDi hai ⊢
    field_simp
    ring


lemma hc_zero_index (α β D m : ℕ) : hc α β D m 0 = 1 := by
  simp [hc]

/-- `hc` shifted by one in `k` (`0` at `k = 0`). -/
noncomputable def hcPrev (α β D n k : ℕ) : ℝ := if k = 0 then 0 else hc α β D n (k - 1)

lemma hc_rec (α β D n k : ℕ) (hk : k ≤ n + 1) (hn : n + 1 ≤ D) :
    hahnA α β D n * hc α β D (n + 1) k - (hahnA α β D n + hahnC α β D n) * hc α β D n k +
      hahnC α β D n * hc α β D (n - 1) k + (k : ℝ) * hc α β D n k - hcPrev α β D n k = 0 := by
  rcases k with _ | j
  · simp [hcPrev, hc_zero_index]
  · rcases n with _ | m
    · have hj : j = 0 := by omega
      subst hj
      have hC : hahnC α β D 0 = 0 := by simp [hahnC]
      have h1 : hc α β D 0 1 = 0 := hc_eq_zero α β D 0 1 (by omega)
      have h2 : hc α β D 1 1 = ((α : ℝ) + β + 2) / (((α : ℝ) + 1) * D) := by
        simp only [hc, ascPochhammer_one, eval_X]
        have hD' : (D : ℝ) ≠ 0 := by
          have : D ≠ 0 := by omega
          exact_mod_cast this
        push_cast
        field_simp
        ring
      have hA : hahnA α β D 0 * (((α : ℝ) + β + 2) / (((α : ℝ) + 1) * D)) = 1 := by
        have hD' : (D : ℝ) ≠ 0 := by
          have : D ≠ 0 := by omega
          exact_mod_cast this
        unfold hahnA
        push_cast
        field_simp
        ring
      simp only [hcPrev, hC, h1, h2]
      simp only [Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one]
      push_cast
      rw [hc_zero_index]
      linear_combination hA
    · have := hc_rec_succ α β D m j (by omega)
      rw [show m + 1 - 1 = m from rfl]
      simpa [hcPrev] using this


/-- **Hahn three-term recurrence in the degree** (DLMF 18.22.15), for `n < D`:
`-u Q_n(u) = A_n Q_{n+1}(u) - (A_n + C_n) Q_n(u) + C_n Q_{n-1}(u)`; for `n = 0`, `C_0 = 0` and the
(natural-number) `Q_{0-1} = Q_0` term has coefficient zero. -/
theorem hahnQ_rec (α β D n u : ℕ) (hn : n + 1 ≤ D) :
    -(u : ℝ) * hahnQ α β D n u =
      hahnA α β D n * hahnQ α β D (n + 1) u - (hahnA α β D n + hahnC α β D n) * hahnQ α β D n u +
        hahnC α β D n * hahnQ α β D (n - 1) u := by
  set W : ℕ → ℝ := fun k => (ascPochhammer ℝ k).eval (-(u : ℝ)) with hWdef
  have hW : ∀ k : ℕ, (u : ℝ) * W k = (k : ℝ) * W k - W (k + 1) := by
    intro k
    simp only [hWdef]
    rw [ascPochhammer_succ_eval]
    ring
  have e1 := hahnQ_ext α β D (n + 1) u (n + 2) (by omega)
  have e2 := hahnQ_ext α β D n u (n + 2) (by omega)
  have e3 := hahnQ_ext α β D (n - 1) u (n + 2) (by omega)
  have hshift : ∑ k ∈ Finset.range (n + 2), hc α β D n k * W (k + 1) =
      ∑ k ∈ Finset.range (n + 2), hcPrev α β D n k * W k := by
    have h1 := Finset.sum_range_succ' (fun k => hcPrev α β D n k * W k) (n + 2)
    have h2 := Finset.sum_range_succ (fun k => hcPrev α β D n k * W k) (n + 2)
    have h0 : hcPrev α β D n 0 = 0 := by simp [hcPrev]
    have hl : hcPrev α β D n (n + 2) = 0 := by
      simp only [hcPrev, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ite_false]
      exact hc_eq_zero α β D n (n + 2 - 1) (by omega)
    have hs : ∀ k, hcPrev α β D n (k + 1) = hc α β D n k := by intro k; simp [hcPrev]
    simp only [h0, zero_mul, add_zero, hl, hs] at h1 h2
    linarith
  have hsum : ∑ k ∈ Finset.range (n + 2),
      (hahnA α β D n * (hc α β D (n + 1) k * W k) -
        (hahnA α β D n + hahnC α β D n) * (hc α β D n k * W k) +
        hahnC α β D n * (hc α β D (n - 1) k * W k) + (u : ℝ) * (hc α β D n k * W k)) = 0 := by
    have hterm : ∀ k ∈ Finset.range (n + 2),
        (hahnA α β D n * (hc α β D (n + 1) k * W k) -
          (hahnA α β D n + hahnC α β D n) * (hc α β D n k * W k) +
          hahnC α β D n * (hc α β D (n - 1) k * W k) + (u : ℝ) * (hc α β D n k * W k)) =
        hcPrev α β D n k * W k - hc α β D n k * W (k + 1) := by
      intro k hk
      have hE := hc_rec α β D n k (by simp only [Finset.mem_range] at hk; omega) hn
      have hu := hW k
      linear_combination (W k) * hE + (hc α β D n k) * hu
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hshift]
    ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [e1, e2, e3]
  linarith

/-- info: 'FormalResearch.Racah.hahnQ_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahnQ_rec

end FormalResearch.Racah
