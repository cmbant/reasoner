import Mathlib

/-!
# Algebra of the zeros of the critical-slice sextic

The elementary part of `prop:fqe-moment-zeros` (`sextic_identity.tex`): classification of the
solutions of the twelve equations (`ZE`) `p_i (x_j - x_k) + 2 x_i (p_j - p_k) = 0` with
`|x_i| = p_i ≥ 0`, `Σ p_i = 1` (here `x_i = v_i²`, `p_i = |v_i|²`). Pure algebra over `ℂ`; no
hypotheses beyond those displayed, no `native_decide`.
-/

namespace FormalResearch.FourQubitEntropy.PaperECritical

theorem sum_four {M : Type*} [AddCommMonoid M] (f : Fin 4 → M) (a b c d : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∑ i, f i = f a + f b + f c + f d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd rfl hab | exact absurd rfl hac | exact absurd rfl had
    | exact absurd rfl hbc | exact absurd rfl hbd | exact absurd rfl hcd
    | (simp [Fin.sum_univ_four]; try abel)

theorem cover4 : ∀ {a b c d : Fin 4}, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∀ i, i = a ∨ i = b ∨ i = c ∨ i = d := by decide

theorem exists_complement : ∀ a b : Fin 4, a ≠ b →
    ∃ c d : Fin 4, c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by decide

/-- The equations `(ZE)` on `p_j u_j - p_k u_k + 2 u_i (p_j - p_k) = 0`. -/
def ZE (p : Fin 4 → ℝ) (u : Fin 4 → ℂ) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (p j : ℂ) * u j - p k * u k + 2 * u i * ((p j : ℂ) - p k) = 0

theorem step_eq {p : Fin 4 → ℝ} {u : Fin 4 → ℂ} (h : ZE p u) {a b c d : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hp : p a ≠ p b) : u c = u d := by
  have h1 := h c a b hac.symm hbc.symm hab
  have h2 := h d a b had.symm hbd.symm hab
  have hne : ((p a : ℂ) - p b) ≠ 0 := by
    intro h0; apply hp; exact_mod_cast sub_eq_zero.mp h0
  have : (2 * (p a - p b : ℂ)) * (u c - u d) = 0 := by linear_combination h1 - h2
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (by simpa using h0) hne
  · exact sub_eq_zero.mp h0

theorem step_p {p : Fin 4 → ℝ} {u : Fin 4 → ℂ} (h : ZE p u) (hu : ∀ i, ‖u i‖ = 1)
    {a c d : Fin 4} (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d) (hcd' : u c = u d) :
    p c = p d := by
  by_contra hne
  have h1 := h a c d hac had hcd
  rw [hcd'] at h1
  have hne' : ((p c : ℂ) - p d) ≠ 0 := by
    intro h0; apply hne; exact_mod_cast sub_eq_zero.mp h0
  have : ((p c : ℂ) - p d) * (u d + 2 * u a) = 0 := by linear_combination h1
  have h2 : u d + 2 * u a = 0 := by
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hne'
    · exact h0
  have h3 : u d = -(2 * u a) := by linear_combination h2
  have h4 := congrArg norm h3
  rw [norm_neg, norm_mul, hu d, hu a] at h4
  norm_num at h4

theorem final_case {p : Fin 4 → ℝ} {u : Fin 4 → ℂ} (h : ZE p u) (hu : ∀ i, ‖u i‖ = 1)
    (hpos : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) {a b c d : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hu' : u c = u d) (hp' : p c = p d) (hne : p a ≠ p c) :
    (∀ i, p i = 1 / 6 ∨ p i = 1 / 2) ∧ ∑ i, (p i : ℂ) * u i = 0 := by
  -- u b = u d
  have e1 := h b a c hab.symm hbc hac
  have e2 := h d a c had.symm hcd.symm hac
  have hne' : ((p a : ℂ) - p c) ≠ 0 := by
    intro h0; apply hne; exact_mod_cast sub_eq_zero.mp h0
  have hbd' : u b = u d := by
    have : (2 * ((p a : ℂ) - p c)) * (u b - u d) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (by simpa using h0) hne'
    · exact sub_eq_zero.mp h0
  have hbc' : u b = u c := by rw [hbd', hu']
  -- the pair (a, b) with i = c
  have e3 := h c a b hac.symm hbc.symm hab
  -- p b = p c
  have hu0 : u c ≠ 0 := by
    intro h0; have := hu c; rw [h0] at this; simp at this
  rw [hbc'] at e1 e3
  have hpb : p b = p c := by
    have : (3 * u c) * ((p b : ℂ) - p c) = 0 := by linear_combination e1 - e3
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (mul_ne_zero (by norm_num) hu0)
    · exact_mod_cast sub_eq_zero.mp h0
  -- p a u a = u (3 t - 2 p a)
  have hA : (p a : ℂ) * u a = u c * (3 * (p c : ℂ) - 2 * p a) := by linear_combination e1
  have n1 : ‖(p a : ℂ) * u a‖ = p a := by
    rw [norm_mul, hu a, mul_one, Complex.norm_real, Real.norm_of_nonneg (hpos a).le]
  have n2 : ‖u c * (3 * (p c : ℂ) - 2 * p a)‖ = |3 * p c - 2 * p a| := by
    have : (3 * (p c : ℂ) - 2 * p a) = ((3 * p c - 2 * p a : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, hu c, one_mul, this, Complex.norm_real, Real.norm_eq_abs]
  have hnorm : p a = |3 * p c - 2 * p a| :=
    calc p a = ‖(p a : ℂ) * u a‖ := n1.symm
      _ = ‖u c * (3 * (p c : ℂ) - 2 * p a)‖ := by rw [hA]
      _ = _ := n2
  have hpa : p a = 3 * p c := by
    rcases abs_cases (3 * p c - 2 * p a) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1] at hnorm; exact absurd (by linarith) hne
    · rw [h1] at hnorm; linarith
  have hcov := cover4 hab hac had hbc hbd hcd
  have hs : p a + p b + p c + p d = 1 := by
    rw [← sum_four p a b c d hab hac had hbc hbd hcd]; exact hsum
  have ht : p c = 1 / 6 := by
    have : p d = p c := hp'.symm
    linarith
  refine ⟨?_, ?_⟩
  · intro i
    rcases hcov i with rfl | rfl | rfl | rfl
    · right; linarith
    · left; linarith
    · left; exact ht
    · left; linarith
  · rw [sum_four (fun i => (p i : ℂ) * u i) a b c d hab hac had hbc hbd hcd]
    show (p a : ℂ) * u a + (p b : ℂ) * u b + (p c : ℂ) * u c + (p d : ℂ) * u d = 0
    have hpa' : (p a : ℂ) = 3 * p c := by exact_mod_cast hpa
    have hpb' : (p b : ℂ) = p c := by exact_mod_cast hpb
    have hpd' : (p d : ℂ) = p c := by exact_mod_cast hp'.symm
    rw [hbc', ← hu', hpb', hpd', hA, hpa']
    ring


theorem core_pos {p : Fin 4 → ℝ} {u : Fin 4 → ℂ} (h : ZE p u) (hu : ∀ i, ‖u i‖ = 1)
    (hpos : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    (∀ i, p i = 1 / 4 ∧ u i = u 0) ∨
      ((∀ i, p i = 1 / 6 ∨ p i = 1 / 2) ∧ ∑ i, (p i : ℂ) * u i = 0) := by
  by_cases hall : ∀ i j, p i = p j
  · left
    have h4 : p 0 = 1 / 4 := by
      rw [Fin.sum_univ_four] at hsum
      have := hall 1 0; have := hall 2 0; have := hall 3 0; linarith
    have hp4 : ∀ i, p i = 1 / 4 := fun i => (hall i 0).trans h4
    refine fun i => ⟨hp4 i, ?_⟩
    by_cases hi : i = 0
    · rw [hi]
    · obtain ⟨c, d, hcd, hic, hid, h0c, h0d⟩ := exists_complement i 0 hi
      have e := h c i 0 hic.symm h0c.symm hi
      rw [hp4 i, hp4 0] at e
      have : ((1 : ℂ) / 4) * (u i - u 0) = 0 := by
        push_cast at e; linear_combination e
      rcases mul_eq_zero.mp this with h1 | h1
      · norm_num at h1
      · exact sub_eq_zero.mp h1
  · right
    push Not at hall
    obtain ⟨a, b, hab'⟩ := hall
    have hab : a ≠ b := fun h0 => hab' (by rw [h0])
    obtain ⟨c, d, hcd, hac, had, hbc, hbd⟩ := exists_complement a b hab
    have huc := step_eq h hab hac had hbc hbd hcd hab'
    have hpc := step_p h hu hac had hcd huc
    by_cases hpa : p a = p c
    · have hpb : p b ≠ p c := fun h0 => hab' (hpa.trans h0.symm)
      exact final_case h hu hpos hsum hab.symm hbc hbd hac had hcd huc hpc hpb
    · exact final_case h hu hpos hsum hab hac had hbc hbd hcd huc hpc hpa


/-- **Zero classification, algebraic core** (proved): the solutions of `(ZE)` with `|x_i| = p_i`,
`Σ p_i = 1` are (A) a single nonzero coordinate, (B) `p ≡ 1/4` with all `x_i` equal, or
(C) `p_i ∈ {1/6, 1/2}` for all `i` with `Σ x_i = 0` (the Hilbert-Schmidt family
`v = (√3, ±i, ±i, ±i)/√6` up to position and phase). -/
theorem zero_classify (x : Fin 4 → ℂ) (p : Fin 4 → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hx : ∀ i, ‖x i‖ = p i) (hsum : ∑ i, p i = 1)
    (hE : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (p i : ℂ) * (x j - x k) + 2 * x i * ((p j : ℂ) - p k) = 0) :
    (∃ i, ∀ j, j ≠ i → x j = 0) ∨ (∀ i, p i = 1 / 4 ∧ x i = x 0) ∨
      ((∀ i, p i = 1 / 6 ∨ p i = 1 / 2) ∧ ∑ i, x i = 0) := by
  by_cases hz : ∃ k, p k = 0
  · left
    obtain ⟨k, hk⟩ := hz
    have hxk : x k = 0 := by
      have := hx k; rw [hk] at this; exact norm_eq_zero.mp this
    have hprod : ∀ i j, i ≠ j → p i * p j = 0 := by
      intro i j hij
      by_cases hik : i = k
      · rw [hik, hk, zero_mul]
      by_cases hjk : j = k
      · rw [hjk, hk, mul_zero]
      have e := hE i j k hij hik hjk
      rw [hxk, hk] at e
      have e2 : (p i : ℂ) * x j = -(2 * x i * p j) := by
        push_cast at e; linear_combination e
      have n := congrArg norm e2
      rw [norm_mul, norm_neg, norm_mul, norm_mul, hx i, hx j, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (hp0 i), Real.norm_of_nonneg (hp0 j)] at n
      norm_num at n
      rcases n with n | n
      · have : p i = 0 := by linarith
        rw [this, zero_mul]
      · rw [n, mul_zero]
    have hex : ∃ i, p i ≠ 0 := by
      by_contra hne
      push Not at hne
      have : ∑ i, p i = 0 := Finset.sum_eq_zero fun i _ => hne i
      linarith
    obtain ⟨i, hi⟩ := hex
    refine ⟨i, fun j hj => ?_⟩
    have : p j = 0 := by
      rcases mul_eq_zero.mp (hprod i j hj.symm) with h0 | h0
      · exact absurd h0 hi
      · exact h0
    have := hx j; rw [‹p j = 0›] at this; exact norm_eq_zero.mp this
  · right
    push Not at hz
    have hpos : ∀ i, 0 < p i := fun i => lt_of_le_of_ne (hp0 i) (Ne.symm (hz i))
    set u : Fin 4 → ℂ := fun i => x i / p i with hu_def
    have hu : ∀ i, ‖u i‖ = 1 := by
      intro i
      simp only [hu_def, norm_div, hx i, Complex.norm_real, Real.norm_of_nonneg (hp0 i)]
      exact div_self (hpos i).ne'
    have hxu : ∀ i, x i = p i * u i := by
      intro i
      simp only [hu_def]
      field_simp [(hpos i).ne']
    have hZ : ZE p u := by
      intro i j k hij hik hjk
      have e := hE i j k hij hik hjk
      have hpi : (p i : ℂ) ≠ 0 := by exact_mod_cast (hpos i).ne'
      have : (p i : ℂ) * ((p j : ℂ) * u j - p k * u k + 2 * u i * ((p j : ℂ) - p k)) = 0 := by
        rw [hxu i, hxu j, hxu k] at e
        linear_combination e
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hpi
      · exact h0
    rcases core_pos hZ hu hpos hsum with hB | ⟨hC1, hC2⟩
    · left
      refine fun i => ⟨(hB i).1, ?_⟩
      rw [hxu i, hxu 0, (hB i).1, (hB 0).1, (hB i).2]
    · right
      refine ⟨hC1, ?_⟩
      have : ∑ i, x i = ∑ i, (p i : ℂ) * u i := Finset.sum_congr rfl fun i _ => hxu i
      rw [this]; exact hC2

end FormalResearch.FourQubitEntropy.PaperECritical
