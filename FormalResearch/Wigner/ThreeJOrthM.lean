module

public import FormalResearch.Racah.P2ThreeJRecAll

/-!
# Off-diagonal orthogonality of the `3j` symbol in the rank (DLMF 34.3.17, `j₃ ≠ j₃'` part)

Fix `j₂ j₃ M` and write `tt L m = (L j₂ j₃; M m (-M-m))`.  In the projection `m = m₂` the symbol
satisfies the *symmetric* three-term recurrence `threeJ_recurrence_m_all` (DLMF 34.3.14) whose
spectral parameter is `L(L+1)` (`tt_rec_m`, valid for all rational `L` and `m`).  The discrete Green
identity `green_msum` then gives `∑_m tt L m · tt L' m = 0` as soon as `L(L+1) ≠ L'(L'+1)`
(`tt_orth_offdiag`).  The sum `msum j₂ f = ∑_{k∈ℕ} f (j₂ - k)` is over the lattice `m = j₂ - k`
which contains every `m` with `j₂ - m ∈ ℕ`; the symbol is zero-extended, so it is the finite sum over
the admissible `m`.
-/

@[expose] public section

namespace FormalResearch.Wigner

open FormalResearch.Racah

/-- Sum over the lattice `m = a - k`, `k ∈ ℕ`. -/
noncomputable def msum (a : ℚ) (f : ℚ → ℝ) : ℝ := ∑ᶠ k : ℕ, f (a - k)

lemma msum_eq_sum {a : ℚ} {f : ℚ → ℝ} (hf : ∀ x : ℚ, x < -a → f x = 0) (N : ℕ)
    (hN : 2 * a < N) : msum a f = ∑ k ∈ Finset.range N, f (a - k) := by
  unfold msum
  apply finsum_eq_sum_of_support_subset
  intro k hk
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  apply hk
  apply hf
  have : (N : ℚ) ≤ k := by exact_mod_cast not_lt.mp hlt
  linarith

lemma exists_nat_gt_two_mul (a : ℚ) : ∃ N : ℕ, 2 * a + 1 < N :=
  ⟨⌈2 * a + 1⌉₊ + 1, by
    have := Nat.le_ceil (2 * a + 1)
    push_cast; linarith⟩

lemma msum_comb {a : ℚ} {f g : ℚ → ℝ} (hf : ∀ x : ℚ, x < -a → f x = 0)
    (hg : ∀ x : ℚ, x < -a → g x = 0) (p q : ℝ) :
    msum a (fun x => p * f x + q * g x) = p * msum a f + q * msum a g := by
  obtain ⟨N0, hN0⟩ := exists_nat_gt_two_mul a
  have h1 : ∀ x : ℚ, x < -a → p * f x + q * g x = 0 := by
    intro x hx; rw [hf x hx, hg x hx]; ring
  rw [msum_eq_sum h1 N0 (by linarith), msum_eq_sum hf N0 (by linarith),
    msum_eq_sum hg N0 (by linarith), Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

lemma msum_congr {a : ℚ} {f g : ℚ → ℝ} (h : ∀ x, f x = g x) : msum a f = msum a g := by
  unfold msum; simp only [h]

lemma msum_smul {a : ℚ} {f : ℚ → ℝ} (hf : ∀ x : ℚ, x < -a → f x = 0) (p : ℝ) :
    msum a (fun x => p * f x) = p * msum a f := by
  have := msum_comb (a := a) (f := f) (g := f) hf hf p 0
  simpa using this

/-- **Discrete Green identity** for symmetric three-term recurrences on the lattice `a - ℕ`:
if `s`, `s'` solve `(c x + Λ) s x = F x s(x+1) + F(x-1) s(x-1)` (resp. with `Λ'`), vanish below `-a`
and `F a = 0`, then `(Λ - Λ') ∑ s s' = 0`. -/
theorem green_msum {a : ℚ} {F s s' c : ℚ → ℝ} {Λ Λ' : ℝ}
    (hs : ∀ x : ℚ, x < -a → s x = 0) (hs' : ∀ x : ℚ, x < -a → s' x = 0) (hF : F a = 0)
    (hr : ∀ x : ℚ, (c x + Λ) * s x = F x * s (x + 1) + F (x - 1) * s (x - 1))
    (hr' : ∀ x : ℚ, (c x + Λ') * s' x = F x * s' (x + 1) + F (x - 1) * s' (x - 1)) :
    (Λ - Λ') * msum a (fun x => s x * s' x) = 0 := by
  set H : ℚ → ℝ := fun y => F y * (s (y + 1) * s' y - s' (y + 1) * s y) with hH
  have hpt : ∀ x : ℚ, (Λ - Λ') * (s x * s' x) = H x - H (x - 1) := by
    intro x
    simp only [hH, sub_add_cancel]
    linear_combination (s' x) * hr x - (s x) * hr' x
  obtain ⟨N0, hN0⟩ := exists_nat_gt_two_mul a
  have hz : ∀ x : ℚ, x < -a → s x * s' x = 0 := by
    intro x hx; rw [hs x hx]; ring
  rw [msum_eq_sum hz N0 (by linarith)]
  have hS : ∑ k ∈ Finset.range N0, (H (a - k) - H (a - k - 1)) = 0 := by
    have := Finset.sum_range_sub' (fun i : ℕ => H (a - i)) N0
    have e : ∀ k : ℕ, H (a - k) - H (a - k - 1) = H (a - k) - H (a - ((k + 1 : ℕ) : ℚ)) := by
      intro k
      rw [show (a - k - 1 : ℚ) = a - ((k + 1 : ℕ) : ℚ) by push_cast; ring]
    rw [Finset.sum_congr rfl (fun k _ => e k), this]
    have h1 : H (a - ((0 : ℕ) : ℚ)) = 0 := by
      simp [hH, hF]
    have h2 : H (a - (N0 : ℚ)) = 0 := by
      have a1 : s (a - (N0 : ℚ) + 1) = 0 := hs _ (by linarith)
      have a2 : s' (a - (N0 : ℚ) + 1) = 0 := hs' _ (by linarith)
      have a3 : s (a - (N0 : ℚ)) = 0 := hs _ (by linarith)
      have a4 : s' (a - (N0 : ℚ)) = 0 := hs' _ (by linarith)
      simp [hH, a1, a2, a3, a4]
    rw [h1, h2]; ring
  rw [Finset.mul_sum]
  rw [← hS]
  exact Finset.sum_congr rfl fun k _ => hpt (a - k)

/-! ### The symbol as a function of the projection and its recurrence in `m` -/

/-- `tt j₂ j₃ M L m = (L j₂ j₃; M m (-M-m))`. -/
noncomputable def tt (j₂ j₃ M L m : ℚ) : ℝ := threeJ L j₂ j₃ M m (-M - m)

/-- The coefficient `F(m) = √((j₂-m)(j₂+m+1)(j₃+M+m+1)(j₃-M-m))` of DLMF 34.3.14. -/
noncomputable def Fm (j₂ j₃ M m : ℚ) : ℝ :=
  Real.sqrt (((j₂ : ℝ) - m) * ((j₂ : ℝ) + m + 1) * ((j₃ : ℝ) + M + m + 1) * ((j₃ : ℝ) - M - m))

lemma threeJ_eq_zero_of_racah {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (h : racahSum3 j₁ j₂ j₃ m₁ m₂ = 0) :
    threeJ j₁ j₂ j₃ m₁ m₂ m₃ = 0 := by
  unfold threeJ
  split_ifs
  · rw [h]; ring
  · rfl

/-- Admissibility of the projection `m = m₂` (with `m₃ = -M-m`). -/
def MAdm (j₂ j₃ M m : ℚ) : Prop :=
  IsNat (j₂ + m) ∧ IsNat (j₂ - m) ∧ IsNat (j₃ + (-M - m)) ∧ IsNat (j₃ - (-M - m))

lemma tt_eq_zero_of_not_madm {j₂ j₃ M m : ℚ} (L : ℚ) (h : ¬ MAdm j₂ j₃ M m) :
    tt j₂ j₃ M L m = 0 := by
  apply threeJ_eq_zero_of_racah
  apply racahSum3_zero_of_not_isNat _ _ _ _ _ (-M - m) (by ring)
  unfold MAdm at h
  by_contra hcon
  push Not at hcon
  exact h ⟨hcon.2.2.2.2.2.1, hcon.2.2.2.2.2.2.1, hcon.2.2.2.2.2.2.2.1, hcon.2.2.2.2.2.2.2.2⟩

lemma tj_isNat_add_one {x : ℚ} (h : IsNat x) : IsNat (x + 1) := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨n + 1, by push_cast; rfl⟩

/-- If `y + 1` is a natural number and `y` is not, then `y + 1 = 0`. -/
lemma tj_succ_zero {y : ℚ} (h1 : IsNat (y + 1)) (h0 : ¬ IsNat y) : y + 1 = 0 := by
  obtain ⟨n, hn⟩ := h1
  rcases n with _ | n
  · simpa using hn
  · exfalso; apply h0
    exact ⟨n, by push_cast at hn; linarith⟩

lemma Fm_eq_zero_of_factor {j₂ j₃ M m : ℚ}
    (h : (j₂ : ℝ) - m = 0 ∨ (j₂ : ℝ) + m + 1 = 0 ∨ (j₃ : ℝ) + M + m + 1 = 0 ∨
      (j₃ : ℝ) - M - m = 0) : Fm j₂ j₃ M m = 0 := by
  unfold Fm
  have : ((j₂ : ℝ) - m) * ((j₂ : ℝ) + m + 1) * ((j₃ : ℝ) + M + m + 1) * ((j₃ : ℝ) - M - m) = 0 := by
    rcases h with h | h | h | h <;> rw [h] <;> ring
  rw [this, Real.sqrt_zero]

/-- If the upper neighbour of an inadmissible projection is admissible, `F m = 0`. -/
lemma Fm_up {j₂ j₃ M m : ℚ} (h : ¬ MAdm j₂ j₃ M m) (hn : MAdm j₂ j₃ M (m + 1)) :
    Fm j₂ j₃ M m = 0 := by
  obtain ⟨n1, n2, n3, n4⟩ := hn
  have c2 : IsNat (j₂ - m) := by convert tj_isNat_add_one n2 using 1; ring
  have c3 : IsNat (j₃ + (-M - m)) := by convert tj_isNat_add_one n3 using 1; ring
  by_cases c1 : IsNat (j₂ + m)
  · by_cases c4 : IsNat (j₃ - (-M - m))
    · exact absurd ⟨c1, c2, c3, c4⟩ h
    · apply Fm_eq_zero_of_factor; right; right; left
      have := tj_succ_zero (y := j₃ - (-M - m)) (by convert n4 using 1; ring) c4
      have h' : j₃ + M + m + 1 = 0 := by linarith
      exact_mod_cast h'
  · apply Fm_eq_zero_of_factor; right; left
    have := tj_succ_zero (y := j₂ + m) (by convert n1 using 1; ring) c1
    exact_mod_cast this

/-- If the lower neighbour of an inadmissible projection is admissible, `F (m-1) = 0`. -/
lemma Fm_down {j₂ j₃ M m : ℚ} (h : ¬ MAdm j₂ j₃ M m) (hn : MAdm j₂ j₃ M (m - 1)) :
    Fm j₂ j₃ M (m - 1) = 0 := by
  obtain ⟨n1, n2, n3, n4⟩ := hn
  have c1 : IsNat (j₂ + m) := by convert tj_isNat_add_one n1 using 1; ring
  have c4 : IsNat (j₃ - (-M - m)) := by convert tj_isNat_add_one n4 using 1; ring
  by_cases c2 : IsNat (j₂ - m)
  · by_cases c3 : IsNat (j₃ + (-M - m))
    · exact absurd ⟨c1, c2, c3, c4⟩ h
    · apply Fm_eq_zero_of_factor; right; right; right
      have := tj_succ_zero (y := j₃ + (-M - m)) (by convert n3 using 1; ring) c3
      have h' : j₃ - M - (m - 1) = 0 := by linarith
      push_cast
      exact_mod_cast h'
  · apply Fm_eq_zero_of_factor; left
    have := tj_succ_zero (y := j₂ - m) (by convert n2 using 1; ring) c2
    have h' : j₂ - (m - 1) = 0 := by linarith
    exact_mod_cast h'

/-- **DLMF 34.3.14** for the symbol `tt`, for every rational `L` and `m`. -/
theorem tt_rec_m (j₂ j₃ M L m : ℚ) :
    (((L : ℝ) * (L + 1) - j₂ * (j₂ + 1) - j₃ * (j₃ + 1)) - 2 * (m : ℝ) * (-M - m)) *
        tt j₂ j₃ M L m =
      Fm j₂ j₃ M m * tt j₂ j₃ M L (m + 1) + Fm j₂ j₃ M (m - 1) * tt j₂ j₃ M L (m - 1) := by
  by_cases hc : MAdm j₂ j₃ M m
  · obtain ⟨a1, b1, b3, a4⟩ := hc
    have e := threeJ_recurrence_m_all L j₂ j₃ M m (-M - m) (by ring) a1 a4 b1 b3
    unfold tt
    rw [show (-M - (m + 1) : ℚ) = -M - m - 1 by ring,
      show (-M - (m - 1) : ℚ) = -M - m + 1 by ring]
    have f1 : Fm j₂ j₃ M m = Real.sqrt (((j₂ : ℝ) - m) * ((j₂ : ℝ) + m + 1) *
        ((j₃ : ℝ) - ((-M - m : ℚ) : ℝ) + 1) * ((j₃ : ℝ) + ((-M - m : ℚ) : ℝ))) := by
      unfold Fm; congr 1; push_cast; ring
    have f2 : Fm j₂ j₃ M (m - 1) = Real.sqrt (((j₂ : ℝ) - m + 1) * ((j₂ : ℝ) + m) *
        ((j₃ : ℝ) - ((-M - m : ℚ) : ℝ)) * ((j₃ : ℝ) + ((-M - m : ℚ) : ℝ) + 1)) := by
      unfold Fm; congr 1; push_cast; ring
    rw [f1, f2]
    push_cast at e ⊢
    linear_combination e
  · have z0 : tt j₂ j₃ M L m = 0 := tt_eq_zero_of_not_madm L hc
    have z1 : Fm j₂ j₃ M m * tt j₂ j₃ M L (m + 1) = 0 := by
      by_cases hu : MAdm j₂ j₃ M (m + 1)
      · rw [Fm_up hc hu]; ring
      · rw [tt_eq_zero_of_not_madm L hu]; ring
    have z2 : Fm j₂ j₃ M (m - 1) * tt j₂ j₃ M L (m - 1) = 0 := by
      by_cases hd : MAdm j₂ j₃ M (m - 1)
      · rw [Fm_down hc hd]; ring
      · rw [tt_eq_zero_of_not_madm L hd]; ring
    rw [z0, z1, z2]; ring

lemma tt_neg_m (j₂ j₃ M L : ℚ) {m : ℚ} (hm : m < -j₂) : tt j₂ j₃ M L m = 0 := by
  apply tt_eq_zero_of_not_madm
  rintro ⟨⟨n, hn⟩, -⟩
  have : (0 : ℚ) ≤ n := by positivity
  linarith

lemma Fm_top (j₂ j₃ M : ℚ) : Fm j₂ j₃ M j₂ = 0 := by
  apply Fm_eq_zero_of_factor; left; ring

/-- **DLMF 34.3.17, off-diagonal part**: if `L(L+1) ≠ L'(L'+1)` then
`∑_m (L j₂ j₃; M m -M-m)(L' j₂ j₃; M m -M-m) = 0`. -/
theorem tt_orth_offdiag (j₂ j₃ M L L' : ℚ) (hne : (L : ℝ) * (L + 1) ≠ L' * (L' + 1)) :
    msum j₂ (fun m => tt j₂ j₃ M L m * tt j₂ j₃ M L' m) = 0 := by
  have hmain := green_msum (a := j₂) (F := fun y : ℚ => Fm j₂ j₃ M y)
    (s := fun m : ℚ => tt j₂ j₃ M L m) (s' := fun m : ℚ => tt j₂ j₃ M L' m)
    (c := fun x : ℚ => -(j₂ : ℝ) * (j₂ + 1) - j₃ * (j₃ + 1) - 2 * (x : ℝ) * (-M - x))
    (Λ := (L : ℝ) * (L + 1)) (Λ' := (L' : ℝ) * (L' + 1))
    (fun x hx => tt_neg_m j₂ j₃ M L (by linarith)) (fun x hx => tt_neg_m j₂ j₃ M L' (by linarith))
    (Fm_top j₂ j₃ M)
    (fun x => by have := tt_rec_m j₂ j₃ M L x; linear_combination this)
    (fun x => by have := tt_rec_m j₂ j₃ M L' x; linear_combination this)
  rcases mul_eq_zero.mp hmain with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/-- info: 'FormalResearch.Wigner.tt_rec_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tt_rec_m

/-- info: 'FormalResearch.Wigner.tt_orth_offdiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tt_orth_offdiag

end FormalResearch.Wigner
