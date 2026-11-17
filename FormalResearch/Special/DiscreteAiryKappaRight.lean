module

public import FormalResearch.Special.DiscreteAiryLimitChains3j
public import FormalResearch.Special.DiscreteAiryKappaLeftBand
public import FormalResearch.Special.DiscreteAiryKappaEdge

/-!
# Monotone decay of the Hahn chain beyond the turning point (plan K1, step M-d, part 1)

On the forbidden side the exact `3j` chain, which vanishes beyond `k = N - 1`, is monotone: if `c_k ≥ a_k + a_{k+1}` and `a_k > 0`
for `m₁ < k ≤ N₀` and `Y_{N₀+1} = 0`, `Y_{N₀+2} = 0`, then `|Y_{k+1}| ≤ |Y_k|` for all `k ≥ m₁` (downward induction, the invariant
being `Y_{k+1}² ≤ Y_k²`: from the row, `a_k Y_{k-1} Y_k = c_k Y_k² - a_{k+1} Y_k Y_{k+1} ≥ a_k Y_k²`).

* `kr_down`: the abstract monotonicity, `kr_le_start`: `Y_k² ≤ Y_{m₁}²` for `k ≥ m₁`.
* `kr_margin_hahn`: for the closed-form Hahn coefficients, the margin `a_k + a_{k+1} ≤ c_k` holds for every `k` with `kh ≥ q_* + 3h/2`,
  `q_* = √(1-x²)`, once `h` is small (`h ≤ 3q_*³/(2x(|Mσ|+1))`, `(|Mσ|+1) h² ≤ x q_*²`).  Explicit, no chart input.
* `kr_chain_mono`: for the actual `3j` chain at a node: `Ŷ_k² ≤ Ŷ_{m+1}²` for every `k ≥ m + 1`, if `q_* ≤ (m + ½) h`.

**Claim class: proved.**

**Not formalised.**  The half-integer `3j` chain (the Racah right side is `rd_mono`, `rdH_mono` in `RacahKappa*`).
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry FormalResearch.Racah

namespace FormalResearch.Special

/-- The invariant `Y_{k+1}² ≤ Y_k²` propagates one step to the left. -/
lemma kr_step {a b c y0 y1 y2 : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hrow : a * y0 = c * y1 - b * y2)
    (hmarg : a + b ≤ c) (h1 : y2 ^ 2 ≤ y1 ^ 2) : y1 ^ 2 ≤ y0 ^ 2 := by
  have h3 : y1 * y2 ≤ y1 ^ 2 := by
    have : (y1 * y2) ^ 2 ≤ (y1 ^ 2) ^ 2 := by nlinarith [sq_nonneg y1, mul_le_mul_of_nonneg_left h1 (sq_nonneg y1)]
    exact le_of_sq_le_sq (by simpa using this) (sq_nonneg y1)
  have h4 : a * (y0 * y1) = c * y1 ^ 2 - b * (y1 * y2) := by linear_combination y1 * hrow
  have h5 : a * y1 ^ 2 ≤ a * (y0 * y1) := by
    rw [h4]
    nlinarith [mul_le_mul_of_nonneg_left h3 hb, mul_nonneg (sub_nonneg.2 hmarg) (sq_nonneg y1)]
  have h6 : y1 ^ 2 ≤ y0 * y1 := le_of_mul_le_mul_left h5 ha
  by_cases hy : y1 = 0
  · rw [hy]; nlinarith [sq_nonneg y0]
  · have hy2 : 0 < y1 ^ 2 := by positivity
    have : y1 ^ 2 * y1 ^ 2 ≤ y1 ^ 2 * y0 ^ 2 := by nlinarith [h6, sq_nonneg (y0 * y1 - y1 ^ 2)]
    exact le_of_mul_le_mul_left this hy2

/-- **Downward monotonicity.**  Rows and margins on `Icc (m₁+1) N₀`, `Y_{N₀+1} = 0`: then `Y_{k+1}² ≤ Y_k²` for all `k ≥ m₁`. -/
lemma kr_down {a c Y : ℤ → ℝ} {m1 N0 : ℤ} (hm : m1 ≤ N0)
    (hrow : ∀ k ∈ Finset.Icc (m1 + 1) N0, jac a c Y k = 0)
    (hpos : ∀ k ∈ Finset.Icc (m1 + 1) N0, 0 < a k ∧ 0 ≤ a (k + 1) ∧ a k + a (k + 1) ≤ c k)
    (hend : ∀ k, N0 < k → Y k = 0) : ∀ k, m1 ≤ k → Y (k + 1) ^ 2 ≤ Y k ^ 2 := by
  have hP : ∀ n : ℕ, (n : ℤ) ≤ N0 - m1 → Y (N0 - n + 1) ^ 2 ≤ Y (N0 - n) ^ 2 := by
    intro n
    induction n with
    | zero =>
      intro _
      have : Y (N0 + 1) = 0 := hend _ (by omega)
      simp only [Nat.cast_zero, sub_zero]
      rw [this]
      nlinarith [sq_nonneg (Y N0)]
    | succ n ih =>
      intro hn
      have hn' : (n : ℤ) ≤ N0 - m1 := by push_cast at hn; omega
      have i1 := ih hn'
      set k : ℤ := N0 - n with hk
      have hkmem : k ∈ Finset.Icc (m1 + 1) N0 := by
        rw [Finset.mem_Icc]; push_cast at hn; omega
      obtain ⟨hp1, hp2, hp3⟩ := hpos k hkmem
      have hr := hrow k hkmem
      unfold jac at hr
      have := kr_step hp1 hp2 (y0 := Y (k - 1)) (y1 := Y k) (y2 := Y (k + 1)) (by linarith) hp3 i1
      have e1 : N0 - ((n + 1 : ℕ) : ℤ) = k - 1 := by rw [hk]; push_cast; ring
      rw [e1, show k - 1 + 1 = k by ring]
      exact this
  intro k hk
  by_cases hkN : k ≤ N0
  · have := hP (N0 - k).toNat (by omega)
    rwa [show N0 - ((N0 - k).toNat : ℤ) = k by omega] at this
  · push Not at hkN
    simp [hend k hkN, hend (k + 1) (by omega)]

/-- `Y_k² ≤ Y_{m₁}²` for all `k ≥ m₁`. -/
lemma kr_le_start {Y : ℤ → ℝ} {m1 : ℤ} (hmono : ∀ k, m1 ≤ k → Y (k + 1) ^ 2 ≤ Y k ^ 2) :
    ∀ k, m1 ≤ k → Y k ^ 2 ≤ Y m1 ^ 2 := by
  intro k hk
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = k - m1 := ⟨(k - m1).toNat, Int.toNat_of_nonneg (by omega)⟩
  have : ∀ n : ℕ, Y (m1 + (n : ℤ)) ^ 2 ≤ Y m1 ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hmono (m1 + (n : ℤ)) (by omega)
      rw [show m1 + ((n + 1 : ℕ) : ℤ) = m1 + (n : ℤ) + 1 by push_cast; ring]
      linarith
  have := this n
  rwa [show m1 + (n : ℤ) = k by omega] at this

/-- `rr M σ j ≤ 1 + 1/j²` for `2 ≤ j`, `|M|, |σ| ≤ j`. -/
lemma kr_rr_le {M σ j : ℝ} (hj : 2 ≤ j) (hM : |M| ≤ j) (hσ : |σ| ≤ j) : rr M σ j ≤ 1 + 1 / j ^ 2 := by
  unfold rr
  have hj0 : 0 < j := by linarith
  have ht : 1 / j ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have ht0 : 0 < 1 / j ^ 2 := by positivity
  set t : ℝ := 1 / j ^ 2 with htdef
  have hf : ∀ {m : ℝ}, |m| ≤ j → 0 ≤ 1 - m ^ 2 / j ^ 2 ∧ 1 - m ^ 2 / j ^ 2 ≤ 1 := by
    intro m hm
    have h1 : m ^ 2 ≤ j ^ 2 := by nlinarith [sq_abs m, abs_nonneg m]
    constructor
    · have : m ^ 2 / j ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact h1
      linarith
    · have : 0 ≤ m ^ 2 / j ^ 2 := by positivity
      linarith
  obtain ⟨a1, a2⟩ := hf hM
  obtain ⟨b1, b2⟩ := hf hσ
  have hd : 1 / (4 * j ^ 2) = t / 4 := by rw [htdef]; field_simp
  rw [hd]
  apply Real.sqrt_le_iff.2
  refine ⟨by linarith, ?_⟩
  have hpos : 0 < 1 - t / 4 := by linarith
  rw [div_le_iff₀ hpos]
  have h1 : (1 - M ^ 2 / j ^ 2) * (1 - σ ^ 2 / j ^ 2) ≤ 1 := by
    nlinarith [mul_le_mul a2 b2 b1 (by norm_num : (0 : ℝ) ≤ 1)]
  nlinarith [mul_nonneg ht0.le ht0.le, mul_nonneg (mul_nonneg ht0.le ht0.le) ht0.le]

/-- **The margin for the closed-form Hahn coefficients on the forbidden side**: `a_j + a_{j+1} ≤ c_j` for `j h ≥ q_* + 3h/2`
(`q_*² = 1 - x²`), `h` small. -/
lemma kr_margin_hahn {M σ x qs h j : ℝ} (hx : 0 < x) (hqs : qs ^ 2 = 1 - x ^ 2) (hqs0 : 0 < qs) (hh : 0 < h)
    (hh1 : 2 * x * (|M * σ| + 1) * h ≤ 3 * qs ^ 3) (hh2 : (|M * σ| + 1) * h ^ 2 ≤ x * qs ^ 2)
    (hMσ : (|M| + |σ| + 2) * h ≤ qs) (hj : qs + 3 * h / 2 ≤ j * h) :
    1 / 2 * rr M σ j * Real.sqrt (1 - (j * h) ^ 2) +
      1 / 2 * rr M σ (j + 1) * Real.sqrt (1 - ((j + 1) * h) ^ 2) ≤ x - M * σ / (j * (j + 1)) := by
  have hjqs : qs ≤ j * h := by linarith
  have hj0 : 0 < j := by
    by_contra hcon; push Not at hcon; nlinarith [mul_nonneg (neg_nonneg.2 hcon) hh.le]
  have hjq : qs / h ≤ j := by rw [div_le_iff₀ hh]; linarith
  have hjMσ : |M| + |σ| + 2 ≤ j := by
    have : (|M| + |σ| + 2) * h ≤ j * h := by linarith
    exact le_of_mul_le_mul_right this hh
  have hj2 : (2 : ℝ) ≤ j := by linarith [abs_nonneg M, abs_nonneg σ]
  have hMj : |M| ≤ j := by linarith [abs_nonneg σ]
  have hσj : |σ| ≤ j := by linarith [abs_nonneg M]
  have hj1 : (2 : ℝ) ≤ j + 1 := by linarith
  have r1 := kr_rr_le hj2 hMj hσj
  have r2 := kr_rr_le (M := M) (σ := σ) (j := j + 1) hj1 (by linarith) (by linarith)
  have hjj : 1 / (j + 1) ^ 2 ≤ 1 / j ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  -- E_j and E_{j+1}
  have hE0 : 0 ≤ Real.sqrt (1 - (j * h) ^ 2) := Real.sqrt_nonneg _
  have hEmono : Real.sqrt (1 - ((j + 1) * h) ^ 2) ≤ Real.sqrt (1 - (j * h) ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_pos hj0 hh, mul_pos hh hh]
  have hE1 : Real.sqrt (1 - (j * h) ^ 2) ≤ 1 := by
    apply Real.sqrt_le_one.2; nlinarith [sq_nonneg (j * h)]
  -- E_j ≤ x - η
  set η : ℝ := (|M * σ| + 1) / j ^ 2 with hη
  have hj2' : 0 < j ^ 2 := by positivity
  have hη1 : η ≤ (|M * σ| + 1) * h ^ 2 / qs ^ 2 := by
    rw [hη, div_le_div_iff₀ hj2' (by positivity)]
    have : qs ^ 2 ≤ (j * h) ^ 2 := pow_le_pow_left₀ hqs0.le hjqs 2
    nlinarith [abs_nonneg (M * σ), mul_nonneg (add_nonneg (abs_nonneg (M * σ)) zero_le_one) (sq_nonneg h)]
  have hqs2 : 0 < qs ^ 2 := by positivity
  have hηx : η ≤ x := by
    refine hη1.trans ?_
    rw [div_le_iff₀ hqs2]; linarith
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  have h2xη : 2 * x * η ≤ 3 * qs * h := by
    have : 2 * x * η ≤ 2 * x * ((|M * σ| + 1) * h ^ 2 / qs ^ 2) := by
      apply mul_le_mul_of_nonneg_left hη1; positivity
    refine this.trans ?_
    rw [show 2 * x * ((|M * σ| + 1) * h ^ 2 / qs ^ 2) = (2 * x * (|M * σ| + 1) * h) * h / qs ^ 2 by ring,
      div_le_iff₀ hqs2]
    nlinarith [mul_le_mul_of_nonneg_right hh1 hh.le]
  have hEx : Real.sqrt (1 - (j * h) ^ 2) ≤ x - η := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    have h3 : (qs + 3 * h / 2) ^ 2 ≤ (j * h) ^ 2 := pow_le_pow_left₀ (by positivity) hj 2
    nlinarith [sq_nonneg η, mul_pos hh hh]
  -- assemble
  have hc : x - |M * σ| / j ^ 2 ≤ x - M * σ / (j * (j + 1)) := by
    have : M * σ / (j * (j + 1)) ≤ |M * σ| / j ^ 2 := by
      calc M * σ / (j * (j + 1)) ≤ |M * σ / (j * (j + 1))| := le_abs_self _
        _ = |M * σ| / (j * (j + 1)) := by rw [abs_div, abs_of_pos (by positivity : 0 < j * (j + 1))]
        _ ≤ |M * σ| / j ^ 2 := div_le_div_of_nonneg_left (abs_nonneg _) hj2' (by nlinarith)
    linarith
  have hr1 : 1 / 2 * rr M σ j * Real.sqrt (1 - (j * h) ^ 2) ≤ 1 / 2 * (1 + 1 / j ^ 2) * Real.sqrt (1 - (j * h) ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ hE0
    linarith
  have hr2 : 1 / 2 * rr M σ (j + 1) * Real.sqrt (1 - ((j + 1) * h) ^ 2) ≤
      1 / 2 * (1 + 1 / j ^ 2) * Real.sqrt (1 - (j * h) ^ 2) := by
    have h0 : 0 ≤ Real.sqrt (1 - ((j + 1) * h) ^ 2) := Real.sqrt_nonneg _
    have rr0 : 0 ≤ rr M σ (j + 1) := by unfold rr; exact Real.sqrt_nonneg _
    have : rr M σ (j + 1) * Real.sqrt (1 - ((j + 1) * h) ^ 2) ≤ (1 + 1 / j ^ 2) * Real.sqrt (1 - (j * h) ^ 2) :=
      mul_le_mul (by linarith) hEmono h0 (by positivity)
    linarith
  have ht : 1 / j ^ 2 * Real.sqrt (1 - (j * h) ^ 2) ≤ 1 / j ^ 2 := mul_le_of_le_one_right (by positivity) hE1
  have e1 : |M * σ| / j ^ 2 + η = (|M * σ| + (|M * σ| + 1)) / j ^ 2 := by rw [hη]; ring
  have e2 : (|M * σ| + 1) / j ^ 2 = |M * σ| / j ^ 2 + 1 / j ^ 2 := by ring
  have : 1 / 2 * (1 + 1 / j ^ 2) * Real.sqrt (1 - (j * h) ^ 2) + 1 / 2 * (1 + 1 / j ^ 2) * Real.sqrt (1 - (j * h) ^ 2) =
      Real.sqrt (1 - (j * h) ^ 2) + 1 / j ^ 2 * Real.sqrt (1 - (j * h) ^ 2) := by ring
  rw [hη] at hEx
  linarith

/-- **Monotone decay of the actual `3j` chain beyond the turn** (see the module docstring): `h = 1/N`, `q_*² = 1 - x²`,
`q_* ≤ (m + ½) h`, `h` small.  Then `Ŷ_k² ≤ Ŷ_{m+1}²` for every `k ≥ m + 1`. -/
theorem kr_chain_mono (M σ N m : ℤ) (x : ℚ) (hN : 0 < N) (hx0 : (0 : ℝ) < x) {qs : ℝ} (hqs : qs ^ 2 = 1 - (x : ℝ) ^ 2)
    (hqs0 : 0 < qs) (hm : qs ≤ ((m : ℝ) + 1 / 2) * (1 / (N : ℝ)))
    (hh1 : 2 * (x : ℝ) * (|(M : ℝ) * σ| + 1) * (1 / (N : ℝ)) ≤ 3 * qs ^ 3)
    (hh2 : (|(M : ℝ) * σ| + 1) * (1 / (N : ℝ)) ^ 2 ≤ (x : ℝ) * qs ^ 2)
    (hMσ : (|(M : ℝ)| + |(σ : ℝ)| + 2) * (1 / (N : ℝ)) ≤ qs) :
    ∀ k : ℤ, m + 1 ≤ k → hahn3jY M σ N x k ^ 2 ≤ hahn3jY M σ N x (m + 1) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set h : ℝ := 1 / (N : ℝ) with hh
  have hh0 : 0 < h := by positivity
  have hm0 : 0 ≤ m := by
    by_contra hcon
    push Not at hcon
    have : (m : ℝ) + 1 / 2 ≤ -1 / 2 := by
      have : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
      linarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ -((m : ℝ) + 1 / 2)) hh0.le]
  have hend : ∀ k : ℤ, N - 1 < k → hahn3jY M σ N x k = 0 := fun k hk =>
    hahn_chain_support M σ N x k (fun ⟨_, _, h3⟩ => by omega)
  -- the smallness `kmin + 2 ≤ k` for `k ≥ m + 2`
  have hkbig : ∀ k : ℤ, m + 2 ≤ k → |(M : ℝ)| + |(σ : ℝ)| + 2 ≤ (k : ℝ) := by
    intro k hk
    have hk' : (m : ℝ) + 2 ≤ k := by exact_mod_cast hk
    have h1 : qs ≤ (k : ℝ) * h := by nlinarith
    have : (|(M : ℝ)| + |(σ : ℝ)| + 2) * h ≤ (k : ℝ) * h := hMσ.trans h1
    exact le_of_mul_le_mul_right this hh0
  by_cases hmN : m + 1 ≤ N - 1
  · have hmono := kr_down (a := hrAk 1 0 (M : ℝ) (σ : ℝ) h) (c := hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) h)
      (Y := hahn3jY M σ N x) (m1 := m + 1) (N0 := N - 1) hmN
      (fun k hk => hahn_class_chain M σ N x hN k (by rw [Finset.mem_Icc] at hk; omega))
      (fun k hk => by
        rw [Finset.mem_Icc] at hk
        have hk2 : m + 2 ≤ k := by omega
        have hkb := hkbig k hk2
        have hkr : (m : ℝ) + 2 ≤ k := by exact_mod_cast hk2
        rw [kl_hrAk_eq, kl_hrCk_eq]
        have hk1 : (1 : ℝ) ≤ k := by linarith [abs_nonneg (M : ℝ), abs_nonneg (σ : ℝ)]
        have hrpos : 0 < rr (M : ℝ) (σ : ℝ) (k : ℝ) :=
          lt_of_lt_of_le (by positivity) (ke_rr_lower hk1 (by linarith [abs_nonneg (σ : ℝ)])
            (by linarith [abs_nonneg (M : ℝ)]))
        have hkN : (k : ℝ) < N := by exact_mod_cast (by omega : k < N)
        have hEpos : 0 < Real.sqrt (1 - ((k : ℝ) * h) ^ 2) := by
          apply Real.sqrt_pos.2
          have : (k : ℝ) * h < 1 := by
            rw [hh, ← div_eq_mul_one_div, div_lt_one hNr]; exact hkN
          have : 0 < (k : ℝ) * h := by positivity
          nlinarith
        refine ⟨by unfold kl_a; exact mul_pos (mul_pos (by norm_num) hrpos) hEpos, by unfold kl_a rr; positivity, ?_⟩
        have := kr_margin_hahn (M := (M : ℝ)) (σ := (σ : ℝ)) (x := (x : ℝ)) (qs := qs) (h := h) (j := (k : ℝ)) hx0 hqs hqs0
          hh0 hh1 hh2 hMσ (by nlinarith)
        have e1 : (((k + 1 : ℤ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        unfold kl_a kl_c
        rw [e1]
        exact this)
      hend
    intro k hk
    exact kr_le_start (fun k hk => hmono k hk) k hk
  · push Not at hmN
    intro k hk
    have h1 : hahn3jY M σ N x k = 0 := hend k (by omega)
    rw [h1]
    have := sq_nonneg (hahn3jY M σ N x (m + 1))
    simpa using this

/-- info: 'FormalResearch.Special.kr_chain_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kr_chain_mono

end FormalResearch.Special
