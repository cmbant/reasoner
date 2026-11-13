module

public import FormalResearch.Wigner.ThreeJSym

/-!
# Wigner's small `d`-function: definition and basic structure

`wignerSmallD j m' m θ = d^j_{m'm}(θ)` is Wigner's explicit sum (Edmonds 4.1.15, Varshalovich 4.3.1(2))

  `d^j_{m'm}(θ) = √((j+m')!(j-m')!(j+m)!(j-m)!) ·
      ∑_s (-1)^{m'-m+s} cos(θ/2)^{2j+m-m'-2s} sin(θ/2)^{m'-m+2s} / ((j+m-s)! s! (m'-m+s)! (j-m'-s)!)`

with spins as rationals and the zero-extended factorials of `FormalResearch.Wigner.Basic`
(`ifa`, `fq`), exactly in the style of `threeJ`.

**Convention.**  This is the Condon–Shortley / Edmonds / Varshalovich / Sakurai matrix
`d^j_{m'm}(θ) = ⟨j m'| exp(-i θ J_y) |j m⟩` (the same as `sympy.physics.quantum.spin.Rotation.d`,
against which the definition was checked numerically for all `j ≤ 3`):
`d^{1/2}_{1/2,1/2} = cos(θ/2)`, `d^{1/2}_{1/2,-1/2} = -sin(θ/2)`, `d^{1/2}_{-1/2,1/2} = sin(θ/2)`,
`d^1_{1,0} = -sin θ/√2`, `d^1_{0,0} = cos θ`.

**Encoding.**  The summand `wignerTerm` uses natural-number exponents `⌊·⌋₊` of the four
factorial arguments `a = j+m-s`, `b = s`, `c = m'-m+s`, `d = j-m'-s` (the exponent of `cos(θ/2)` is
`a + d = 2j+m-m'-2s`, that of `sin(θ/2)` is `b + c = m'-m+2s`, the sign is `(-1)^c`).  Whenever
the term is nonzero all four are natural numbers, so the floors are exact; otherwise the
`ifa` factors kill the term.  `wignerSmallD_eq_textbook` recovers the displayed formula with
integer exponents.

Contents: sanity values (`wignerSmallD_zero`, the `j = 1/2` table, `d^1_{00}`, `d^1_{10}`, `d^1_{11}`),
the symmetries `d^j_{m'm} = (-1)^{m'-m} d^j_{mm'} = d^j_{-m,-m'}` and `d^j_{m'm}(-θ) = d^j_{mm'}(θ)`
(Varshalovich 4.4.1), proved termwise by reindexing.
-/

@[expose] public section

namespace FormalResearch.Wigner

/-- The sign-free part of `wignerTerm`: `(1/(a! b! c! d!)) · cos(θ/2)^(a+d) · sin(θ/2)^(b+c)`. -/
noncomputable def wignerMag (j m' m : ℚ) (θ : ℝ) (s : ℕ) : ℝ :=
  (ifa (j + m - s) * ifa (s : ℚ) * ifa (m' - m + s) * ifa (j - m' - s)) *
    Real.cos (θ / 2) ^ (⌊j + m - s⌋₊ + ⌊j - m' - s⌋₊) *
    Real.sin (θ / 2) ^ (s + ⌊m' - m + s⌋₊)

/-- The summand of Wigner's sum for `d^j_{m'm}(θ)` at the index `s`, without the square-root
prefactor: `(-1)^c · (1/(a! b! c! d!)) · cos(θ/2)^(a+d) · sin(θ/2)^(b+c)` with
`a = j+m-s`, `b = s`, `c = m'-m+s`, `d = j-m'-s`; the exponents are natural-number floors
(exact whenever the term is nonzero). -/
noncomputable def wignerTerm (j m' m : ℚ) (θ : ℝ) (s : ℕ) : ℝ :=
  (-1 : ℝ) ^ ⌊m' - m + s⌋₊ * wignerMag j m' m θ s

/-- **Wigner's small `d`-function** `d^j_{m'm}(θ) = ⟨j m'| e^{-iθJ_y} |j m⟩` by Wigner's explicit
sum (Edmonds 4.1.15, Varshalovich 4.3.1(2)), Condon–Shortley convention; zero-extended, so it
vanishes unless the four numbers `j±m`, `j±m'` are natural. -/
noncomputable def wignerSmallD (j m' m : ℚ) (θ : ℝ) : ℝ :=
  Real.sqrt (fq (j + m') * fq (j - m') * fq (j + m) * fq (j - m)) *
    ∑ᶠ s : ℕ, wignerTerm j m' m θ s

lemma wignerTerm_eq_zero_of_gt {j m' m : ℚ} {θ : ℝ} {s : ℕ} (hs : ⌊j - m'⌋₊ < s) :
    wignerTerm j m' m θ s = 0 := by
  have h1 : j - m' - s < 0 := by
    have h2 : j - m' < (⌊j - m'⌋₊ : ℚ) + 1 := Nat.lt_floor_add_one _
    have h3 : (⌊j - m'⌋₊ : ℚ) + 1 ≤ s := by exact_mod_cast hs
    linarith
  unfold wignerTerm wignerMag
  rw [ifa_eq_zero_of_neg h1]; ring

lemma wignerTerm_eq_zero_of_neg {j m' m : ℚ} {θ : ℝ} {s : ℕ} (h : m' - m + s < 0) :
    wignerTerm j m' m θ s = 0 := by
  unfold wignerTerm wignerMag
  rw [ifa_eq_zero_of_neg h]; ring

lemma wignerTerm_support_subset (j m' m : ℚ) (θ : ℝ) :
    Function.support (wignerTerm j m' m θ) ⊆ ↑(Finset.range (⌊j - m'⌋₊ + 1)) := by
  intro s hs
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  exact hs (wignerTerm_eq_zero_of_gt (by omega))

lemma wignerTerm_support_finite (j m' m : ℚ) (θ : ℝ) :
    (Function.support (wignerTerm j m' m θ)).Finite :=
  (Finset.finite_toSet _).subset (wignerTerm_support_subset j m' m θ)

lemma finsum_wignerTerm_eq_sum (j m' m : ℚ) (θ : ℝ) :
    ∑ᶠ s : ℕ, wignerTerm j m' m θ s = ∑ s ∈ Finset.range (⌊j - m'⌋₊ + 1), wignerTerm j m' m θ s :=
  finsum_eq_sum_of_support_subset _ (wignerTerm_support_subset j m' m θ)

/-! ### The textbook formula -/

lemma wignerTerm_textbook {j m' m : ℚ} {θ : ℝ} (e₁ e₂ : ℤ) (he₁ : (e₁ : ℚ) = 2 * j + m - m')
    (he₂ : (e₂ : ℚ) = m' - m) (s : ℕ) :
    wignerTerm j m' m θ s =
      (-1 : ℝ) ^ (e₂ + s) *
        (ifa (j + m - s) * ifa (s : ℚ) * ifa (m' - m + s) * ifa (j - m' - s)) *
        Real.cos (θ / 2) ^ (e₁ - 2 * (s : ℤ)) * Real.sin (θ / 2) ^ (e₂ + 2 * (s : ℤ)) := by
  by_cases h : ifa (j + m - s) * ifa (s : ℚ) * ifa (m' - m + s) * ifa (j - m' - s) = 0
  · unfold wignerTerm wignerMag; rw [h]; simp
  · simp only [mul_ne_zero_iff] at h
    obtain ⟨⟨⟨h1, -⟩, h3⟩, h4⟩ := h
    obtain ⟨a, ha⟩ := ifa_ne_zero_isNat h1
    obtain ⟨c, hc⟩ := ifa_ne_zero_isNat h3
    obtain ⟨d, hd⟩ := ifa_ne_zero_isNat h4
    unfold wignerTerm wignerMag
    rw [ha, hc, hd, Nat.floor_natCast, Nat.floor_natCast, Nat.floor_natCast]
    have hc' : (c : ℤ) = e₂ + s := by
      have : ((c : ℤ) : ℚ) = ((e₂ + s : ℤ) : ℚ) := by push_cast; linarith
      exact_mod_cast this
    have hexp : ((a : ℤ) + d) = e₁ - 2 * s := by
      have : (((a : ℤ) + d : ℤ) : ℚ) = ((e₁ - 2 * s : ℤ) : ℚ) := by push_cast; linarith
      exact_mod_cast this
    have hsin : ((s : ℤ) + c) = e₂ + 2 * s := by omega
    rw [← hc', ← hexp, ← hsin]
    simp only [← Int.natCast_add, zpow_natCast]
    ring

/-- **Wigner's formula** for `d^j_{m'm}(θ)` in the textbook form (Edmonds 4.1.15, Varshalovich
4.3.1(2)), with `N = j - m'` a natural number and integer exponents
`e₁ = 2j+m-m'`, `e₂ = m'-m`; terms outside the range of the four factorials are zero. -/
theorem wignerSmallD_eq_textbook {j m' m : ℚ} {θ : ℝ} {N : ℕ} (hN : j - m' = N) (e₁ e₂ : ℤ)
    (he₁ : (e₁ : ℚ) = 2 * j + m - m') (he₂ : (e₂ : ℚ) = m' - m) :
    wignerSmallD j m' m θ =
      Real.sqrt (fq (j + m') * fq (j - m') * fq (j + m) * fq (j - m)) *
        ∑ s ∈ Finset.range (N + 1), (-1 : ℝ) ^ (e₂ + s) *
          (ifa (j + m - s) * ifa (s : ℚ) * ifa (m' - m + s) * ifa (j - m' - s)) *
          Real.cos (θ / 2) ^ (e₁ - 2 * (s : ℤ)) * Real.sin (θ / 2) ^ (e₂ + 2 * (s : ℤ)) := by
  unfold wignerSmallD
  have hfl : ⌊j - m'⌋₊ = N := by rw [hN, Nat.floor_natCast]
  rw [finsum_wignerTerm_eq_sum, hfl]
  congr 1
  exact Finset.sum_congr rfl fun s _ => wignerTerm_textbook e₁ e₂ he₁ he₂ s

/-- For `j + m`, `j + m'` and `j - m'` natural, the integer exponents of the textbook formula exist. -/
lemma exists_textbook_exponents {j m' m : ℚ} (h1 : IsNat (j + m)) (h2 : IsNat (j - m'))
    (h3 : IsNat (j + m')) :
    ∃ e₁ e₂ : ℤ, (e₁ : ℚ) = 2 * j + m - m' ∧ (e₂ : ℚ) = m' - m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨d, hd⟩ := h2
  obtain ⟨c, hc⟩ := h3
  exact ⟨(a : ℤ) + d, (c : ℤ) - a, by push_cast; linarith, by push_cast; linarith⟩

/-! ### Symmetries -/

lemma finsum_shift_nat (G : ℕ → ℝ) (k M : ℕ) (hM : ∀ s, M < s → G s = 0)
    (hk : ∀ s, s < k → G s = 0) : ∑ᶠ s, G s = ∑ᶠ s, G (s + k) := by
  have sL : Function.support G ⊆ ↑(Finset.range (k + (M + 1))) := by
    intro s hs
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hs (hM s (by omega))
  have sR : Function.support (fun s => G (s + k)) ⊆ ↑(Finset.range (M + 1)) := by
    intro s hs
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hs (hM _ (by omega))
  rw [finsum_eq_sum_of_support_subset _ sL, finsum_eq_sum_of_support_subset _ sR,
    Finset.sum_range_add, Finset.sum_eq_zero (fun s hs => hk s (Finset.mem_range.mp hs)), zero_add]
  exact Finset.sum_congr rfl fun s _ => by rw [add_comm]

lemma neg_one_pow_mul_self_add (k s : ℕ) : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (k + s) = (-1 : ℝ) ^ s := by
  rw [← pow_add, show k + (k + s) = 2 * k + s by ring, pow_add, pow_mul]; simp

lemma wignerMag_shift {j m' m : ℚ} {θ : ℝ} {k : ℕ} (hk : m' - m = k) (s : ℕ) :
    wignerMag j m m' θ (s + k) = wignerMag j m' m θ s := by
  have hm' : m' = m + k := by linarith
  subst hm'
  have e1 : m - (m + (k : ℚ)) + ((s + k : ℕ) : ℚ) = (s : ℚ) := by push_cast; ring
  have e2 : j + (m + (k : ℚ)) - ((s + k : ℕ) : ℚ) = j + m - s := by push_cast; ring
  have e3 : j - m - ((s + k : ℕ) : ℚ) = j - (m + k) - s := by push_cast; ring
  have e4 : m + (k : ℚ) - m + s = ((k + s : ℕ) : ℚ) := by push_cast; ring
  have e5 : ((s + k : ℕ) : ℚ) = ((k + s : ℕ) : ℚ) := by rw [add_comm]
  unfold wignerMag
  rw [e1, e2, e3, e4, e5, Nat.floor_natCast, Nat.floor_natCast, add_comm s k]
  ring

/-- Shifting the index by `k = m' - m` exchanges `d^j_{m'm}` and `d^j_{mm'}` termwise. -/
lemma wignerTerm_shift {j m' m : ℚ} {θ : ℝ} {k : ℕ} (hk : m' - m = k) (s : ℕ) :
    wignerTerm j m m' θ (s + k) = (-1 : ℝ) ^ k * wignerTerm j m' m θ s := by
  have e1 : m - m' + ((s + k : ℕ) : ℚ) = (s : ℚ) := by push_cast; linarith
  have e4 : m' - m + (s : ℚ) = ((k + s : ℕ) : ℚ) := by push_cast; linarith
  unfold wignerTerm
  rw [wignerMag_shift hk, e1, e4, Nat.floor_natCast, Nat.floor_natCast, ← mul_assoc,
    neg_one_pow_mul_self_add]

lemma finsum_wignerTerm_swap_aux {j m' m : ℚ} {θ : ℝ} {k : ℕ} (hk : m' - m = k) :
    ∑ᶠ s : ℕ, wignerTerm j m m' θ s = (-1 : ℝ) ^ k * ∑ᶠ s : ℕ, wignerTerm j m' m θ s := by
  rw [finsum_shift_nat _ k ⌊j - m⌋₊ (fun s hs => wignerTerm_eq_zero_of_gt hs)
    (fun s hs => wignerTerm_eq_zero_of_neg (by
      have : (s : ℚ) < k := by exact_mod_cast hs
      linarith)), mul_finsum]
  exact finsum_congr fun s => wignerTerm_shift hk s

lemma finsum_wignerTerm_eq_zero_of_not_int {j m' m : ℚ} {θ : ℝ}
    (h : ¬ ∃ n : ℤ, m' - m = n) : ∑ᶠ s : ℕ, wignerTerm j m' m θ s = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro s
  have : ifa (m' - m + s) = 0 := by
    apply ifa_of_not_int
    rintro ⟨n, hn⟩
    exact h ⟨n - s, by push_cast; linarith⟩
  unfold wignerTerm wignerMag
  rw [this]; ring

/-- `d^j_{m'm}(θ) = 0` unless `m' - m` is an integer. -/
theorem wignerSmallD_eq_zero_of_not_int {j m' m : ℚ} (θ : ℝ) (h : ¬ ∃ n : ℤ, m' - m = n) :
    wignerSmallD j m' m θ = 0 := by
  unfold wignerSmallD
  rw [finsum_wignerTerm_eq_zero_of_not_int h]; ring

/-- **Varshalovich 4.4.1**: `d^j_{m'm}(θ) = (-1)^{m'-m} d^j_{mm'}(θ)`, with the zero-extended sign
`sgn`; both sides vanish when `m' - m` is not an integer. -/
theorem wignerSmallD_swap (j m' m : ℚ) (θ : ℝ) :
    wignerSmallD j m' m θ = sgn (m' - m) * wignerSmallD j m m' θ := by
  by_cases h : ∃ n : ℤ, m' - m = n
  · have hpre : fq (j + m') * fq (j - m') * fq (j + m) * fq (j - m) =
        fq (j + m) * fq (j - m) * fq (j + m') * fq (j - m') := by ring
    unfold wignerSmallD
    rw [hpre]
    obtain ⟨n, hn⟩ := h
    rcases le_or_gt 0 n with h0 | h0
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
      have hk : m' - m = k := by rw [hn]; simp
      rw [hk, sgn_natCast, finsum_wignerTerm_swap_aux hk]
      have : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
      linear_combination (-(Real.sqrt (fq (j + m) * fq (j - m) * fq (j + m') * fq (j - m')) *
        ∑ᶠ s : ℕ, wignerTerm j m' m θ s)) * this
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -n)
      have hk' : m - m' = k := by
        have : ((-n : ℤ) : ℚ) = (k : ℚ) := by exact_mod_cast hk
        push_cast at this; linarith
      have e : m' - m = -(k : ℚ) := by linarith
      rw [e, sgn_neg', sgn_natCast, finsum_wignerTerm_swap_aux hk']
      ring
  · rw [wignerSmallD_eq_zero_of_not_int θ h]
    simp [sgn, h]

/-- **Varshalovich 4.4.1**: `d^j_{m'm}(θ) = d^j_{-m,-m'}(θ)`. -/
theorem wignerSmallD_neg (j m' m : ℚ) (θ : ℝ) :
    wignerSmallD j (-m) (-m') θ = wignerSmallD j m' m θ := by
  have hpre : fq (j + -m) * fq (j - -m) * fq (j + -m') * fq (j - -m') =
      fq (j + m') * fq (j - m') * fq (j + m) * fq (j - m) := by
    simp only [← sub_eq_add_neg, sub_neg_eq_add]; ring
  have hterm : ∀ s, wignerTerm j (-m) (-m') θ s = wignerTerm j m' m θ s := by
    intro s
    have e1 : j + -m' - (s : ℚ) = j - m' - s := by ring
    have e2 : -m - -m' + (s : ℚ) = m' - m + s := by ring
    have e3 : j - -m - (s : ℚ) = j + m - s := by ring
    unfold wignerTerm wignerMag
    rw [e1, e2, e3]; ring
  unfold wignerSmallD
  rw [hpre]
  congr 1
  exact finsum_congr hterm

lemma wignerTerm_neg_theta (j m' m : ℚ) (θ : ℝ) (s : ℕ) :
    wignerTerm j m' m (-θ) s = sgn (m' - m) * wignerTerm j m' m θ s := by
  by_cases hc : ifa (m' - m + s) = 0
  · unfold wignerTerm wignerMag
    rw [hc]; ring
  · obtain ⟨p, hp⟩ := ifa_ne_zero_isNat hc
    have hsg : sgn (m' - m) = (-1 : ℝ) ^ (p + s) := by
      have : m' - m = (((p : ℤ) - (s : ℤ) : ℤ) : ℚ) := by push_cast; linarith
      rw [this, sgn_intCast, show (p : ℤ) - s = ((p + s : ℕ) : ℤ) + 2 * (-(s : ℤ)) by push_cast; ring,
        neg_one_zpow_add_two_mul, zpow_natCast]
    unfold wignerTerm wignerMag
    rw [hsg, hp, Nat.floor_natCast, neg_div, Real.cos_neg, Real.sin_neg, neg_pow, pow_add (-1 : ℝ) p s]
    ring

/-- **Varshalovich 4.4.1**: `d^j_{m'm}(-θ) = d^j_{mm'}(θ)`. -/
theorem wignerSmallD_neg_theta (j m' m : ℚ) (θ : ℝ) :
    wignerSmallD j m' m (-θ) = wignerSmallD j m m' θ := by
  by_cases h : ∃ n : ℤ, m' - m = n
  · have h1 : wignerSmallD j m' m (-θ) = sgn (m' - m) * wignerSmallD j m' m θ := by
      unfold wignerSmallD
      rw [show ∑ᶠ s : ℕ, wignerTerm j m' m (-θ) s =
        ∑ᶠ s : ℕ, sgn (m' - m) * wignerTerm j m' m θ s from finsum_congr
          (wignerTerm_neg_theta j m' m θ), ← mul_finsum]
      ring
    rw [h1, wignerSmallD_swap j m' m θ, ← mul_assoc, sgn_mul_self_of_int (by
      obtain ⟨n, hn⟩ := h; exact ⟨n, hn⟩), one_mul]
  · have h' : ¬ ∃ n : ℤ, m - m' = n := by
      rintro ⟨n, hn⟩; exact h ⟨-n, by push_cast; linarith⟩
    unfold wignerSmallD
    rw [show ∑ᶠ s : ℕ, wignerTerm j m' m (-θ) s = 0 from
      finsum_wignerTerm_eq_zero_of_not_int h, finsum_wignerTerm_eq_zero_of_not_int h']
    ring

/-! ### Sanity values -/

private lemma wd_ifa_zero : ifa 0 = 1 := by simpa using ifa_natCast 0
private lemma wd_ifa_one : ifa 1 = 1 := by simpa using ifa_natCast 1
private lemma wd_ifa_two : ifa 2 = 1 / 2 := by simpa using ifa_natCast 2
private lemma wd_ifa_neg_one : ifa (-1) = 0 := ifa_eq_zero_of_neg (by norm_num)
private lemma wd_fq_zero : fq 0 = 1 := by simpa using fq_natCast 0
private lemma wd_fq_one : fq 1 = 1 := by simpa using fq_natCast 1
private lemma wd_fq_two : fq 2 = 2 := by simpa using fq_natCast 2

/-- `d^j_{m'm}(0) = δ_{m'm}` (for `j ± m` natural). -/
theorem wignerSmallD_zero {j : ℚ} (m' m : ℚ) (h1 : IsNat (j + m)) (h2 : IsNat (j - m)) :
    wignerSmallD j m' m 0 = if m' = m then 1 else 0 := by
  have hsin : Real.sin (0 / 2) = 0 := by simp
  have hcos : Real.cos (0 / 2) = 1 := by simp
  by_cases hmm : m' = m
  · subst hmm
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    have hsum : ∑ᶠ s : ℕ, wignerTerm j m' m' 0 s = wignerTerm j m' m' 0 0 := by
      apply finsum_eq_single
      intro s hs
      unfold wignerTerm wignerMag
      rw [hsin, zero_pow (by omega)]; ring
    unfold wignerSmallD
    rw [hsum]
    simp only [↓reduceIte]
    unfold wignerTerm wignerMag
    simp only [sub_self, Nat.cast_zero, sub_zero, hsin, hcos, ha, hb, Nat.floor_zero, wd_ifa_zero,
      add_zero, pow_zero, mul_one, one_mul, Nat.floor_natCast]
    rw [fq_natCast, fq_natCast, ifa_natCast, ifa_natCast, one_pow,
      show ((a.factorial : ℝ) * b.factorial * a.factorial * b.factorial) =
        (a.factorial * b.factorial) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    field_simp
  · simp only [hmm, ↓reduceIte]
    have hz : ∀ s : ℕ, wignerTerm j m' m 0 s = 0 := by
      intro s
      unfold wignerTerm wignerMag
      by_cases hs : s = 0
      · subst hs
        by_cases hc : ifa (m' - m + ((0 : ℕ) : ℚ)) = 0
        · rw [hc]; ring
        · obtain ⟨n, hn⟩ := ifa_ne_zero_isNat hc
          have hn0 : n ≠ 0 := by
            rintro rfl
            apply hmm
            simp at hn; linarith
          rw [hn, Nat.floor_natCast, hsin, zero_pow (by omega)]; ring
      · rw [hsin, zero_pow (by omega)]; ring
    unfold wignerSmallD
    rw [finsum_eq_zero_of_forall_eq_zero hz]; ring

private lemma wd_floor_ofNat2 : ⌊(2 : ℚ)⌋₊ = 2 := by norm_num
private lemma wd_floor_neg_one : ⌊(-1 : ℚ)⌋₊ = 0 := Nat.floor_of_nonpos (by norm_num)

/-- `d^{1/2}_{1/2,1/2}(θ) = cos(θ/2)`. -/
theorem wignerSmallD_half_pp (θ : ℝ) : wignerSmallD (1 / 2) (1 / 2) (1 / 2) θ = Real.cos (θ / 2) := by
  unfold wignerSmallD
  rw [finsum_wignerTerm_eq_sum]
  norm_num [Finset.sum_range_succ, wignerTerm, wignerMag, wd_ifa_zero, wd_ifa_one, wd_fq_zero,
    wd_fq_one]

/-- `d^{1/2}_{1/2,-1/2}(θ) = -sin(θ/2)`. -/
theorem wignerSmallD_half_pm (θ : ℝ) :
    wignerSmallD (1 / 2) (1 / 2) (-(1 / 2)) θ = -Real.sin (θ / 2) := by
  unfold wignerSmallD
  rw [finsum_wignerTerm_eq_sum]
  norm_num [Finset.sum_range_succ, wignerTerm, wignerMag, wd_ifa_zero, wd_ifa_one, wd_fq_zero,
    wd_fq_one]

/-- `d^{1/2}_{-1/2,1/2}(θ) = sin(θ/2)`. -/
theorem wignerSmallD_half_mp (θ : ℝ) :
    wignerSmallD (1 / 2) (-(1 / 2)) (1 / 2) θ = Real.sin (θ / 2) := by
  unfold wignerSmallD
  rw [finsum_wignerTerm_eq_sum]
  norm_num [Finset.sum_range_succ, wignerTerm, wignerMag, wd_ifa_zero, wd_ifa_one, wd_fq_zero,
    wd_fq_one, wd_ifa_neg_one, wd_floor_neg_one]

/-- `d^{1/2}_{-1/2,-1/2}(θ) = cos(θ/2)`. -/
theorem wignerSmallD_half_mm (θ : ℝ) :
    wignerSmallD (1 / 2) (-(1 / 2)) (-(1 / 2)) θ = Real.cos (θ / 2) := by
  unfold wignerSmallD
  rw [finsum_wignerTerm_eq_sum]
  norm_num [Finset.sum_range_succ, wignerTerm, wignerMag, wd_ifa_zero, wd_ifa_one, wd_fq_zero,
    wd_fq_one, wd_ifa_neg_one, wd_floor_neg_one]

/-- `d^1_{00}(θ) = cos θ`. -/
theorem wignerSmallD_one_zero_zero (θ : ℝ) : wignerSmallD 1 0 0 θ = Real.cos θ := by
  unfold wignerSmallD
  rw [finsum_wignerTerm_eq_sum]
  norm_num [Finset.sum_range_succ, wignerTerm, wignerMag, wd_ifa_zero, wd_ifa_one, wd_fq_zero,
    wd_fq_one]
  have h : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
  rw [h, Real.cos_two_mul, Real.sin_sq]; ring

/-- `d^1_{10}(θ) = -sin θ / √2`. -/
theorem wignerSmallD_one_one_zero (θ : ℝ) :
    wignerSmallD 1 1 0 θ = -(Real.sin θ / Real.sqrt 2) := by
  unfold wignerSmallD
  rw [finsum_wignerTerm_eq_sum]
  norm_num [Finset.sum_range_succ, wignerTerm, wignerMag, wd_ifa_zero, wd_ifa_one, wd_fq_zero,
    wd_fq_one, wd_fq_two]
  have h : Real.sin θ = Real.sin (2 * (θ / 2)) := by ring_nf
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h3 : 0 < Real.sqrt 2 := by positivity
  rw [h, Real.sin_two_mul]
  field_simp
  linear_combination (Real.cos (θ / 2) * Real.sin (θ / 2)) * h2

/-- `d^1_{11}(θ) = (1 + cos θ)/2`. -/
theorem wignerSmallD_one_one_one (θ : ℝ) : wignerSmallD 1 1 1 θ = (1 + Real.cos θ) / 2 := by
  unfold wignerSmallD
  rw [finsum_wignerTerm_eq_sum]
  norm_num [Finset.sum_range_succ, wignerTerm, wignerMag, wd_ifa_zero, wd_ifa_one, wd_fq_zero,
    wd_fq_one, wd_fq_two, wd_ifa_two]
  have h : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
  rw [h, Real.cos_two_mul]; ring

/-- info: 'FormalResearch.Wigner.wignerSmallD_eq_textbook' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_eq_textbook

/-- info: 'FormalResearch.Wigner.wignerSmallD_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_swap

/-- info: 'FormalResearch.Wigner.wignerSmallD_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_neg

/-- info: 'FormalResearch.Wigner.wignerSmallD_neg_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_neg_theta

/-- info: 'FormalResearch.Wigner.wignerSmallD_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_zero

/-- info: 'FormalResearch.Wigner.wignerSmallD_half_pp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_half_pp

/-- info: 'FormalResearch.Wigner.wignerSmallD_half_pm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_half_pm

/-- info: 'FormalResearch.Wigner.wignerSmallD_half_mp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_half_mp

/-- info: 'FormalResearch.Wigner.wignerSmallD_half_mm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_half_mm

/-- info: 'FormalResearch.Wigner.wignerSmallD_one_zero_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_one_zero_zero

/-- info: 'FormalResearch.Wigner.wignerSmallD_one_one_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_one_one_zero

/-- info: 'FormalResearch.Wigner.wignerSmallD_one_one_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_one_one_one

end FormalResearch.Wigner
