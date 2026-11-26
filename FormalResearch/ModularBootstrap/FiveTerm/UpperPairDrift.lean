module

public import FormalResearch.ModularBootstrap.FiveTerm.UpperPairPhi
public import FormalResearch.ModularBootstrap.FiveTerm.UpperPairTaylor

/-!
# Pair-drift cancellation for the design comb (FIVE-U; `cts:tip-shared` (b1))

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Lemma C11$_0$ (`cts:tip-shared`) (b1).

`pair_drift` states (b1) in explicit-constant form: for a scale function `s` and a design weight `w`
(`ScaleHyp`, `WeightHyp` of `UpperPairTaylor`), a point `x` in cell `n`, and `1 ≤ M ≤ n/2`, the sum over the
`2M` neighbouring sites of `log(1 + w_k/(s_k - x)²)` equals the equispaced comb
`∑_{m ≤ M} [log(1 + W_n/(m+ς)²) + log(1 + W_n/(m-ς)²)]` up to `C W_b/n` plus the explicit jump terms of
the relative weight perturbations `θ_k` (the paper's `ϑ_N/(|n-N_split|+1)` and `λ 1_{n ≤ 2n₀}` terms are the
sums of the `θ`-term over the sites across a join).

Differences from the paper: the paper writes the right side with `W_n = w♯(n)/s'(n)²` and the error as
`O(W̄/n)` with `W̄ = max_{|m|≤M} W_{n+m}`; here the hypothesis is only `W_n ≤ W_b ≤ c₀` (the neighbours' weights are
controlled by the regularity `|w'| ≤ C₀ w/a`, `|w''| ≤ C₀ w/a²`), which is weaker and implies the paper's form
since `W_n ≤ W̄`. The hypotheses are `n ≥ n₁(C₀,c₀)` and `M ≤ n/2`; `C` depends only on `C₀, c₀`.

All statements are proved.
-/

@[expose] public section

open Set

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma sum_inv_sq_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, 1 / ((m : ℝ) ^ 2) ≤ 2 - 1 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have : 1 / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ hk0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hk0]
    linarith


noncomputable def pairK (C0 : ℝ) : ℝ := 1 + 2 * C0 * Real.exp C0 + C0
noncomputable def pairc (C0 : ℝ) : ℝ := Real.exp (-C0) / 4

lemma pairK_ge {C0 : ℝ} (hC0 : 0 ≤ C0) : 1 ≤ pairK C0 := by
  unfold pairK
  have : 0 ≤ 2 * C0 * Real.exp C0 := by positivity
  linarith

lemma pairc_pos (C0 : ℝ) : 0 < pairc C0 := by unfold pairc; positivity

lemma pairc_le {C0 : ℝ} (hC0 : 0 ≤ C0) : pairc C0 ≤ 1 / 4 := by
  unfold pairc
  have : Real.exp (-C0) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

/-- The common set-up of one `±m` pair: all the data and bounds needed by `pair_cancel`. -/
lemma pair_setup {C0 : ℝ} (hC0 : 0 ≤ C0) (s s1 s2 s3 w w1 w2 : ℝ → ℝ) (hs : ScaleHyp s s1 s2 s3 C0)
    (hw : WeightHyp w w1 w2 C0) (n m x : ℝ) (hn2 : 3 * C0 + 2 ≤ n) (hm : 1 ≤ m) (hmn : 2 * m ≤ n)
    (hx1 : s (n - 1 / 2) ≤ x) (hx2 : x ≤ s (n + 1 / 2)) :
    ∃ ς W0 W1 W2 b k r1 r2 ρ1 ρ2 u1 u2 : ℝ,
      ς = (s n - x) / s1 n ∧ |ς| ≤ 3 / 4 ∧ W0 = w n / s1 n ^ 2 ∧ 0 ≤ W0 ∧
      W1 = w (n + m) / s1 n ^ 2 ∧ W2 = w (n - m) / s1 n ^ 2 ∧ 0 ≤ W1 ∧ 0 ≤ W2 ∧
      u1 = (s (n + m) - x) / s1 n ∧ u2 = (x - s (n - m)) / s1 n ∧
      u1 = (m + ς) + k * m ^ 2 / 2 + r1 ∧ pairc C0 * m ≤ u1 ∧
      u2 = (m - ς) + (-k) * m ^ 2 / 2 + (-r2) ∧ pairc C0 * m ≤ u2 ∧
      W1 = W0 * (1 + b * m + ρ1) ∧ W2 = W0 * (1 + (-b) * m + ρ2) ∧
      |b| ≤ pairK C0 / n ∧ |k| ≤ pairK C0 / n ∧ |r1| ≤ pairK C0 * m ^ 3 / n ^ 2 ∧
      |r2| ≤ pairK C0 * m ^ 3 / n ^ 2 ∧ |ρ1| ≤ pairK C0 * m ^ 2 / n ^ 2 ∧ |ρ2| ≤ pairK C0 * m ^ 2 / n ^ 2 := by
  have hKge := pairK_ge hC0
  set K : ℝ := pairK C0 with hK
  set c : ℝ := pairc C0 with hc
  have hKdef : K = 1 + 2 * C0 * Real.exp C0 + C0 := rfl
  have hcdef : c = Real.exp (-C0) / 4 := rfl
  have hn3 : 2 ≤ n := by linarith
  have hn4 : 1 ≤ n := by linarith
  have hm0 : 0 < m := by linarith
  have hs1 : 0 < s1 n := hs.pos n hn4
  have hw0 : 0 < w n := hw.pos n hn4
  have hmabs : |m| ≤ n / 2 := by rw [abs_of_pos hm0]; linarith
  have hmabs' : |-m| ≤ n / 2 := by rw [abs_neg]; exact hmabs
  set ς : ℝ := (s n - x) / s1 n with hς
  have hςb : |ς| ≤ 3 / 4 := hs.varsigma_le hn2 hx1 hx2
  have tay1 := hs.taylor hn3 hmabs
  have tay2 := hs.taylor hn3 hmabs'
  have wt1 := hw.taylor hn3 hmabs
  have wt2 := hw.taylor hn3 hmabs'
  rw [show n + -m = n - m by ring, abs_neg] at tay2
  rw [show n + -m = n - m by ring, neg_sq] at wt2
  have hmn' : m ≤ n / 2 := by linarith
  have dr := hs.dist_right hn3 hm hmn' hx2
  have dl := hs.dist_left hn3 hm hmn' hx1
  -- the data
  set s1n := s1 n with hs1n
  set k : ℝ := s2 n / s1n with hk
  set b : ℝ := w1 n / w n with hb
  set r1 : ℝ := (s (n + m) - s n - m * s1n - m ^ 2 / 2 * s2 n) / s1n with hr1
  set r2 : ℝ := (s (n - m) - s n - (-m) * s1n - (-m) ^ 2 / 2 * s2 n) / s1n with hr2
  set ρ1 : ℝ := (w (n + m) - w n - m * w1 n) / w n with hρ1
  set ρ2 : ℝ := (w (n - m) - w n - (-m) * w1 n) / w n with hρ2
  set W0 : ℝ := w n / s1n ^ 2 with hW0
  have hW0p : 0 ≤ W0 := by positivity
  have hA1 := hs.b2 n hn4
  have hB1 := hw.b1 n hn4
  have hKC : C0 ≤ K := by have : 0 ≤ 2 * C0 * Real.exp C0 := by positivity
                          linarith
  have hKe : 2 * C0 * Real.exp C0 ≤ K := by linarith
  have bk : |k| ≤ K / n := by
    rw [hk, abs_div, abs_of_pos hs1, div_le_div_iff₀ hs1 (by linarith)]
    have : |s2 n| * n ≤ C0 * s1n := by
      have := hA1; rw [le_div_iff₀ (by linarith)] at this; linarith
    nlinarith only [this, hKC, hs1]
  have bb : |b| ≤ K / n := by
    rw [hb, abs_div, abs_of_pos hw0, div_le_div_iff₀ hw0 (by linarith)]
    have : |w1 n| * n ≤ C0 * w n := by
      have := hB1; rw [le_div_iff₀ (by linarith)] at this; linarith
    nlinarith only [this, hKC, hw0]
  have br1 : |r1| ≤ K * m ^ 3 / n ^ 2 := by
    rw [hr1, abs_div, abs_of_pos hs1, div_le_iff₀ hs1]
    refine tay1.trans ?_
    rw [abs_of_pos hm0]
    have e : 4 * C0 * Real.exp C0 * s1n / n ^ 2 * m ^ 3 / 6 = (2 * C0 * Real.exp C0) * (1 / 3) * m ^ 3 / n ^ 2 * s1n := by
      field_simp; ring
    rw [e]
    have : (2 * C0 * Real.exp C0) * (1 / 3) ≤ K := by nlinarith only [hKe, hKge]
    have h3 : 0 ≤ m ^ 3 / n ^ 2 * s1n := by positivity
    calc (2 * C0 * Real.exp C0) * (1 / 3) * m ^ 3 / n ^ 2 * s1n
        = ((2 * C0 * Real.exp C0) * (1 / 3)) * (m ^ 3 / n ^ 2 * s1n) := by ring
      _ ≤ K * (m ^ 3 / n ^ 2 * s1n) := mul_le_mul_of_nonneg_right this h3
      _ = K * m ^ 3 / n ^ 2 * s1n := by ring
  have br2 : |r2| ≤ K * m ^ 3 / n ^ 2 := by
    rw [hr2, abs_div, abs_of_pos hs1, div_le_iff₀ hs1]
    refine tay2.trans ?_
    rw [abs_of_pos hm0]
    have e : 4 * C0 * Real.exp C0 * s1n / n ^ 2 * m ^ 3 / 6 = (2 * C0 * Real.exp C0) * (1 / 3) * m ^ 3 / n ^ 2 * s1n := by
      field_simp; ring
    rw [e]
    have : (2 * C0 * Real.exp C0) * (1 / 3) ≤ K := by nlinarith only [hKe, hKge]
    have h3 : 0 ≤ m ^ 3 / n ^ 2 * s1n := by positivity
    calc (2 * C0 * Real.exp C0) * (1 / 3) * m ^ 3 / n ^ 2 * s1n
        = ((2 * C0 * Real.exp C0) * (1 / 3)) * (m ^ 3 / n ^ 2 * s1n) := by ring
      _ ≤ K * (m ^ 3 / n ^ 2 * s1n) := mul_le_mul_of_nonneg_right this h3
      _ = K * m ^ 3 / n ^ 2 * s1n := by ring
  have bρ1 : |ρ1| ≤ K * m ^ 2 / n ^ 2 := by
    rw [hρ1, abs_div, abs_of_pos hw0, div_le_iff₀ hw0]
    refine wt1.trans ?_
    have e : 4 * C0 * Real.exp C0 * w n / n ^ 2 * m ^ 2 / 2 = (2 * C0 * Real.exp C0) * m ^ 2 / n ^ 2 * w n := by
      field_simp; ring
    rw [e]
    have h3 : 0 ≤ m ^ 2 / n ^ 2 * w n := by positivity
    calc 2 * C0 * Real.exp C0 * m ^ 2 / n ^ 2 * w n = (2 * C0 * Real.exp C0) * (m ^ 2 / n ^ 2 * w n) := by ring
      _ ≤ K * (m ^ 2 / n ^ 2 * w n) := mul_le_mul_of_nonneg_right hKe h3
      _ = K * m ^ 2 / n ^ 2 * w n := by ring
  have bρ2 : |ρ2| ≤ K * m ^ 2 / n ^ 2 := by
    rw [hρ2, abs_div, abs_of_pos hw0, div_le_iff₀ hw0]
    refine wt2.trans ?_
    have e : 4 * C0 * Real.exp C0 * w n / n ^ 2 * m ^ 2 / 2 = (2 * C0 * Real.exp C0) * m ^ 2 / n ^ 2 * w n := by
      field_simp; ring
    rw [e]
    have h3 : 0 ≤ m ^ 2 / n ^ 2 * w n := by positivity
    calc 2 * C0 * Real.exp C0 * m ^ 2 / n ^ 2 * w n = (2 * C0 * Real.exp C0) * (m ^ 2 / n ^ 2 * w n) := by ring
      _ ≤ K * (m ^ 2 / n ^ 2 * w n) := mul_le_mul_of_nonneg_right hKe h3
      _ = K * m ^ 2 / n ^ 2 * w n := by ring
  set u1 : ℝ := (s (n + m) - x) / s1n with hu1d
  set u2 : ℝ := (x - s (n - m)) / s1n with hu2d
  have hu1 : u1 = (m + ς) + k * m ^ 2 / 2 + r1 := by
    rw [hu1d, hς, hk, hr1]; field_simp; ring
  have hu2 : u2 = (m - ς) + (-k) * m ^ 2 / 2 + (-r2) := by
    rw [hu2d, hς, hk, hr2]; field_simp; ring
  have hcu1 : c * m ≤ u1 := by
    rw [hu1d, le_div_iff₀ hs1]
    have : c * m * s1n ≤ Real.exp (-C0) / 2 * m * s1n := by
      rw [hcdef]; have : 0 ≤ Real.exp (-C0) * m * s1n := by positivity
      nlinarith only [this]
    linarith
  have hcu2 : c * m ≤ u2 := by
    rw [hu2d, le_div_iff₀ hs1]
    have : c * m * s1n ≤ Real.exp (-C0) / 2 * m * s1n := by
      rw [hcdef]; have : 0 ≤ Real.exp (-C0) * m * s1n := by positivity
      nlinarith only [this]
    linarith
  set W1 : ℝ := w (n + m) / s1n ^ 2 with hW1d
  set W2 : ℝ := w (n - m) / s1n ^ 2 with hW2d
  have hW1 : W1 = W0 * (1 + b * m + ρ1) := by
    rw [hW1d, hW0, hb, hρ1]; field_simp; ring
  have hW2 : W2 = W0 * (1 + (-b) * m + ρ2) := by
    rw [hW2d, hW0, hb, hρ2]; field_simp; ring
  have hn1m : 1 ≤ n - m := by linarith
  have hW1p : 0 ≤ W1 := (div_pos (hw.pos _ (by linarith)) (by positivity)).le
  have hW2p : 0 ≤ W2 := (div_pos (hw.pos _ hn1m) (by positivity)).le
  exact ⟨ς, W0, W1, W2, b, k, r1, r2, ρ1, ρ2, u1, u2, hς, hςb, hW0, hW0p, hW1d, hW2d, hW1p, hW2p, hu1d, hu2d,
    hu1, hcu1, hu2, hcu2, hW1, hW2, bb, bk, br1, br2, bρ1, bρ2⟩

/-- One `±m` pair of sites against the equispaced comb (`cts:tip-shared` (b1), single pair). -/
lemma pair_term {C0 c0 : ℝ} (hC0 : 0 ≤ C0) (hc0 : 1 ≤ c0) :
    ∃ C n1 : ℝ, 0 ≤ C ∧ ∀ (s s1 s2 s3 w w1 w2 : ℝ → ℝ), ScaleHyp s s1 s2 s3 C0 → WeightHyp w w1 w2 C0 →
      ∀ (n m : ℝ) (x Wb : ℝ), n1 ≤ n → 1 ≤ m → 2 * m ≤ n →
        s (n - 1 / 2) ≤ x → x ≤ s (n + 1 / 2) → w n / (s1 n) ^ 2 ≤ Wb → Wb ≤ c0 →
        |(Real.log (1 + w (n + m) / (s (n + m) - x) ^ 2) + Real.log (1 + w (n - m) / (s (n - m) - x) ^ 2)) -
          (Real.log (1 + (w n / s1 n ^ 2) / (m + (s n - x) / s1 n) ^ 2) +
            Real.log (1 + (w n / s1 n ^ 2) / (m - (s n - x) / s1 n) ^ 2))| ≤
          C * Wb * (1 / (n * m ^ 2) + 1 / n ^ 2) := by
  obtain ⟨Cp, np, hCp, hP⟩ := pair_cancel (K := pairK C0) (c := pairc C0) (c0 := c0) (pairK_ge hC0)
    (pairc_pos C0) (pairc_le hC0) hc0
  refine ⟨Cp, max np (3 * C0 + 2), hCp, ?_⟩
  intro s s1 s2 s3 w w1 w2 hs hw n m x Wb hn hm hmn hx1 hx2 hWb hWbc
  have hn1 : np ≤ n := (le_max_left _ _).trans hn
  have hn2 : 3 * C0 + 2 ≤ n := (le_max_right _ _).trans hn
  have hn4 : 1 ≤ n := by linarith
  have hs1 : 0 < s1 n := hs.pos n hn4
  obtain ⟨ς, W0, W1, W2, b, k, r1, r2, ρ1, ρ2, u1, u2, hς, hςb, hW0, hW0p, hW1d, hW2d, hW1p, hW2p, hu1d, hu2d,
    hu1, hcu1, hu2, hcu2, hW1, hW2, bb, bk, br1, br2, bρ1, bρ2⟩ :=
    pair_setup hC0 s s1 s2 s3 w w1 w2 hs hw n m x hn2 hm hmn hx1 hx2
  have key := hP m n ς W0 W1 W2 b k r1 r2 ρ1 ρ2 Wb u1 u2 hm hmn hn1 hςb hu1 hcu1 hu2 hcu2 hW1 hW2 hW0p
    (hW0 ▸ hWb) hWbc hW1p hW2p bb bk br1 br2 bρ1 bρ2
  have l1 : Real.log (1 + w (n + m) / (s (n + m) - x) ^ 2) = Real.log (1 + W1 / u1 ^ 2) := by
    congr 2; rw [hW1d, hu1d]; field_simp
  have l2 : Real.log (1 + w (n - m) / (s (n - m) - x) ^ 2) = Real.log (1 + W2 / u2 ^ 2) := by
    congr 2; rw [hW2d, hu2d]; field_simp; ring
  rw [l1, l2, hW0, hς] at *
  exact key

lemma abs_log_one_add_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.log (1 + a) - Real.log (1 + b)| ≤ |a - b| := by
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → Real.log (1 + a) - Real.log (1 + b) ≤ |a - b| := by
    intro a b ha hb
    have h1 : 0 < 1 + a := by linarith
    have h2 : 0 < 1 + b := by linarith
    have : Real.log (1 + a) - Real.log (1 + b) = Real.log ((1 + a) / (1 + b)) := by
      rw [Real.log_div h1.ne' h2.ne']
    rw [this]
    have h3 := Real.log_le_sub_one_of_pos (div_pos h1 h2)
    have h4 : (1 + a) / (1 + b) - 1 = (a - b) / (1 + b) := by field_simp; ring
    have h5 : (a - b) / (1 + b) ≤ |a - b| := by
      calc (a - b) / (1 + b) ≤ |a - b| / (1 + b) := div_le_div_of_nonneg_right (le_abs_self _) h2.le
        _ ≤ |a - b| := div_le_self (abs_nonneg _) (by linarith)
    linarith
  rw [abs_le]
  constructor
  · have := key b a hb ha
    rw [abs_sub_comm] at this; linarith
  · exact key a b ha hb

/-- Perturbing a weight by a relative amount `t` (with `1 + t ≥ 0`) changes `log(1 + A/d²)` by at most `A|t|/d²`. -/
lemma theta_perturb {A t d : ℝ} (hA : 0 ≤ A) (ht : 0 ≤ 1 + t) :
    |Real.log (1 + A * (1 + t) / d ^ 2) - Real.log (1 + A / d ^ 2)| ≤ A * |t| / d ^ 2 := by
  have h := abs_log_one_add_sub_le (a := A * (1 + t) / d ^ 2) (b := A / d ^ 2) (by positivity) (by positivity)
  refine h.trans ?_
  have : A * (1 + t) / d ^ 2 - A / d ^ 2 = A * t / d ^ 2 := by ring
  rw [this, abs_div, abs_mul, abs_of_nonneg hA, abs_of_nonneg (sq_nonneg d)]


/-- **Pair-drift cancellation, `cts:tip-shared` (b1)** (explicit-constant form). For a scale function `s`
and a design weight `w` (`ScaleHyp`, `WeightHyp`), a point `x` in cell `n` (`s(n-1/2) ≤ x ≤ s(n+1/2)`),
`1 ≤ M ≤ n/2` and relative weight perturbations `θ` (`1 + θ ≥ 0`), the sum over the `2M` neighbouring
sites of `log(1 + w_k/(s_k - x)²)`, `w_k = w(k)(1+θ_k)`, equals the equispaced comb
`∑_{1≤m≤M} [log(1 + W_n/(m+ς)²) + log(1 + W_n/(m-ς)²)]`, `W_n = w(n)/s'(n)²`, `ς = (s(n)-x)/s'(n)`, up to
`C W_b / n` plus the explicit jump terms `C ∑_m (w_{n+m}|θ_{n+m}| + w_{n-m}|θ_{n-m}|)/(s'(n)² m²)`,
where `W_n ≤ W_b ≤ c₀`. The constant `C` and the threshold `n₁` depend only on `C₀, c₀`. -/
theorem pair_drift {C0 c0 : ℝ} (hC0 : 0 ≤ C0) (hc0 : 1 ≤ c0) :
    ∃ C n1 : ℝ, 0 ≤ C ∧ ∀ (s s1 s2 s3 w w1 w2 θ : ℝ → ℝ), ScaleHyp s s1 s2 s3 C0 → WeightHyp w w1 w2 C0 →
      ∀ (n M : ℕ) (x Wb : ℝ), n1 ≤ (n : ℝ) → 1 ≤ M → 2 * (M : ℝ) ≤ n →
        s ((n : ℝ) - 1 / 2) ≤ x → x ≤ s ((n : ℝ) + 1 / 2) → w n / (s1 n) ^ 2 ≤ Wb → Wb ≤ c0 →
        (∀ m ∈ Finset.Icc 1 M, 0 ≤ 1 + θ ((n : ℝ) + m) ∧ 0 ≤ 1 + θ ((n : ℝ) - m)) →
        |∑ m ∈ Finset.Icc 1 M,
            (Real.log (1 + w ((n : ℝ) + m) * (1 + θ ((n : ℝ) + m)) / (s ((n : ℝ) + m) - x) ^ 2) +
              Real.log (1 + w ((n : ℝ) - m) * (1 + θ ((n : ℝ) - m)) / (s ((n : ℝ) - m) - x) ^ 2)) -
          ∑ m ∈ Finset.Icc 1 M,
            (Real.log (1 + (w n / s1 n ^ 2) / ((m : ℝ) + (s n - x) / s1 n) ^ 2) +
              Real.log (1 + (w n / s1 n ^ 2) / ((m : ℝ) - (s n - x) / s1 n) ^ 2))| ≤
          C * Wb / n + C * ∑ m ∈ Finset.Icc 1 M,
            (w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| + w ((n : ℝ) - m) * |θ ((n : ℝ) - m)|) /
              (s1 n ^ 2 * (m : ℝ) ^ 2) := by
  obtain ⟨Cp, n1, hCp, hP⟩ := pair_term (C0 := C0) (c0 := c0) hC0 hc0
  refine ⟨3 * Cp + 4 * Real.exp (2 * C0), n1, by positivity, ?_⟩
  intro s s1 s2 s3 w w1 w2 θ hs hw n M x Wb hn hM hMn hx1 hx2 hWb hWbc hθ
  have hn3 : (2 : ℝ) ≤ n := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hn4 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hs1 : 0 < s1 n := hs.pos n hn4
  have hE : 0 < Real.exp (-C0) := Real.exp_pos _
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  -- per-term bound
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      |(Real.log (1 + w ((n : ℝ) + m) * (1 + θ ((n : ℝ) + m)) / (s ((n : ℝ) + m) - x) ^ 2) +
          Real.log (1 + w ((n : ℝ) - m) * (1 + θ ((n : ℝ) - m)) / (s ((n : ℝ) - m) - x) ^ 2)) -
        (Real.log (1 + (w n / s1 n ^ 2) / ((m : ℝ) + (s n - x) / s1 n) ^ 2) +
          Real.log (1 + (w n / s1 n ^ 2) / ((m : ℝ) - (s n - x) / s1 n) ^ 2))| ≤
      Cp * Wb * (1 / ((n : ℝ) * (m : ℝ) ^ 2) + 1 / (n : ℝ) ^ 2) +
        4 * Real.exp (2 * C0) * ((w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| + w ((n : ℝ) - m) * |θ ((n : ℝ) - m)|) /
          (s1 n ^ 2 * (m : ℝ) ^ 2)) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have hmn : 2 * (m : ℝ) ≤ n := by linarith
    have hm0 : (0 : ℝ) < m := by linarith
    have hmn' : (m : ℝ) ≤ n / 2 := by linarith
    obtain ⟨h1, h2⟩ := hθ m hm
    have P := hP s s1 s2 s3 w w1 w2 hs hw n m x Wb hn hm1 hmn hx1 hx2 hWb hWbc
    have dr := hs.dist_right hn3 hm1 hmn' hx2
    have dl := hs.dist_left hn3 hm1 hmn' hx1
    have hd1 : 4 * Real.exp (2 * C0) / (s1 n ^ 2 * (m : ℝ) ^ 2) ≥ 1 / (s ((n : ℝ) + m) - x) ^ 2 := by
      have hpos : 0 < Real.exp (-C0) / 2 * m * s1 n := by positivity
      have : (Real.exp (-C0) / 2 * m * s1 n) ^ 2 ≤ (s ((n : ℝ) + m) - x) ^ 2 :=
        pow_le_pow_left₀ hpos.le dr 2
      rw [ge_iff_le, div_le_div_iff₀ (by nlinarith only [this, hpos]) (by positivity)]
      have e1 : Real.exp (-C0) ^ 2 * Real.exp (2 * C0) = 1 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      have e2 : (Real.exp (-C0) / 2 * m * s1 n) ^ 2 * (4 * Real.exp (2 * C0)) = s1 n ^ 2 * (m : ℝ) ^ 2 := by
        have : (Real.exp (-C0) / 2 * m * s1 n) ^ 2 * (4 * Real.exp (2 * C0)) =
            (Real.exp (-C0) ^ 2 * Real.exp (2 * C0)) * ((m : ℝ) * s1 n) ^ 2 := by ring
        rw [this, e1]; ring
      nlinarith only [this, e2, show 0 ≤ 4 * Real.exp (2 * C0) from by positivity]
    have hd2 : 4 * Real.exp (2 * C0) / (s1 n ^ 2 * (m : ℝ) ^ 2) ≥ 1 / (s ((n : ℝ) - m) - x) ^ 2 := by
      have hpos : 0 < Real.exp (-C0) / 2 * m * s1 n := by positivity
      have : (Real.exp (-C0) / 2 * m * s1 n) ^ 2 ≤ (s ((n : ℝ) - m) - x) ^ 2 := by
        have h := pow_le_pow_left₀ hpos.le dl 2
        rw [show (s ((n : ℝ) - m) - x) ^ 2 = (x - s ((n : ℝ) - m)) ^ 2 by ring]; exact h
      rw [ge_iff_le, div_le_div_iff₀ (by nlinarith only [this, hpos]) (by positivity)]
      have e1 : Real.exp (-C0) ^ 2 * Real.exp (2 * C0) = 1 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      have e2 : (Real.exp (-C0) / 2 * m * s1 n) ^ 2 * (4 * Real.exp (2 * C0)) = s1 n ^ 2 * (m : ℝ) ^ 2 := by
        have : (Real.exp (-C0) / 2 * m * s1 n) ^ 2 * (4 * Real.exp (2 * C0)) =
            (Real.exp (-C0) ^ 2 * Real.exp (2 * C0)) * ((m : ℝ) * s1 n) ^ 2 := by ring
        rw [this, e1]; ring
      nlinarith only [this, e2, show 0 ≤ 4 * Real.exp (2 * C0) from by positivity]
    have hw1 : 0 < w ((n : ℝ) + m) := hw.pos _ (by linarith)
    have hw2 : 0 < w ((n : ℝ) - m) := hw.pos _ (by linarith)
    have t1 := theta_perturb (A := w ((n : ℝ) + m)) (t := θ ((n : ℝ) + m)) (d := s ((n : ℝ) + m) - x) hw1.le h1
    have t2 := theta_perturb (A := w ((n : ℝ) - m)) (t := θ ((n : ℝ) - m)) (d := s ((n : ℝ) - m) - x) hw2.le h2
    have t1' : w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| / (s ((n : ℝ) + m) - x) ^ 2 ≤
        4 * Real.exp (2 * C0) * (w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| / (s1 n ^ 2 * (m : ℝ) ^ 2)) := by
      have := mul_le_mul_of_nonneg_left hd1 (by positivity : 0 ≤ w ((n : ℝ) + m) * |θ ((n : ℝ) + m)|)
      calc _ = w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| * (1 / (s ((n : ℝ) + m) - x) ^ 2) := by ring
        _ ≤ w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| * (4 * Real.exp (2 * C0) / (s1 n ^ 2 * (m : ℝ) ^ 2)) := this
        _ = _ := by ring
    have t2' : w ((n : ℝ) - m) * |θ ((n : ℝ) - m)| / (s ((n : ℝ) - m) - x) ^ 2 ≤
        4 * Real.exp (2 * C0) * (w ((n : ℝ) - m) * |θ ((n : ℝ) - m)| / (s1 n ^ 2 * (m : ℝ) ^ 2)) := by
      have := mul_le_mul_of_nonneg_left hd2 (by positivity : 0 ≤ w ((n : ℝ) - m) * |θ ((n : ℝ) - m)|)
      calc _ = w ((n : ℝ) - m) * |θ ((n : ℝ) - m)| * (1 / (s ((n : ℝ) - m) - x) ^ 2) := by ring
        _ ≤ w ((n : ℝ) - m) * |θ ((n : ℝ) - m)| * (4 * Real.exp (2 * C0) / (s1 n ^ 2 * (m : ℝ) ^ 2)) := this
        _ = _ := by ring
    set L1 := Real.log (1 + w ((n : ℝ) + m) * (1 + θ ((n : ℝ) + m)) / (s ((n : ℝ) + m) - x) ^ 2)
    set L2 := Real.log (1 + w ((n : ℝ) - m) * (1 + θ ((n : ℝ) - m)) / (s ((n : ℝ) - m) - x) ^ 2)
    set A1 := Real.log (1 + w ((n : ℝ) + m) / (s ((n : ℝ) + m) - x) ^ 2)
    set A2 := Real.log (1 + w ((n : ℝ) - m) / (s ((n : ℝ) - m) - x) ^ 2)
    have e : (L1 + L2) - (Real.log (1 + (w n / s1 n ^ 2) / ((m : ℝ) + (s n - x) / s1 n) ^ 2) +
          Real.log (1 + (w n / s1 n ^ 2) / ((m : ℝ) - (s n - x) / s1 n) ^ 2)) =
        ((A1 + A2) - (Real.log (1 + (w n / s1 n ^ 2) / ((m : ℝ) + (s n - x) / s1 n) ^ 2) +
          Real.log (1 + (w n / s1 n ^ 2) / ((m : ℝ) - (s n - x) / s1 n) ^ 2))) + ((L1 - A1) + (L2 - A2)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add P ((abs_add_le _ _).trans ?_))
    calc |L1 - A1| + |L2 - A2| ≤ _ := add_le_add t1 t2
      _ ≤ 4 * Real.exp (2 * C0) * (w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| / (s1 n ^ 2 * (m : ℝ) ^ 2)) +
          4 * Real.exp (2 * C0) * (w ((n : ℝ) - m) * |θ ((n : ℝ) - m)| / (s1 n ^ 2 * (m : ℝ) ^ 2)) :=
          add_le_add t1' t2'
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsum : ∑ m ∈ Finset.Icc 1 M, (1 / ((n : ℝ) * (m : ℝ) ^ 2) + 1 / (n : ℝ) ^ 2) ≤ 3 / (n : ℝ) := by
    rw [Finset.sum_add_distrib]
    have h1 : ∑ m ∈ Finset.Icc 1 M, 1 / ((n : ℝ) * (m : ℝ) ^ 2) ≤ 2 / (n : ℝ) := by
      have : ∑ m ∈ Finset.Icc 1 M, 1 / ((n : ℝ) * (m : ℝ) ^ 2) =
          (1 / (n : ℝ)) * ∑ m ∈ Finset.Icc 1 M, 1 / ((m : ℝ) ^ 2) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_; field_simp
      rw [this]
      have := sum_inv_sq_le M hM
      have h2 : 1 / (M : ℝ) ≥ 0 := by positivity
      calc 1 / (n : ℝ) * ∑ m ∈ Finset.Icc 1 M, 1 / ((m : ℝ) ^ 2) ≤ 1 / (n : ℝ) * 2 :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 2 / (n : ℝ) := by ring
    have h2 : ∑ m ∈ Finset.Icc 1 M, 1 / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) := by
      rw [Finset.sum_const, Nat.card_Icc]
      simp only [Nat.add_sub_cancel, nsmul_eq_mul]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) hn0]
      have : (M : ℝ) * n ≤ n ^ 2 := by nlinarith only [hMn, hn0]
      nlinarith only [this]
    have e3 : 3 / (n : ℝ) = 2 / (n : ℝ) + 1 / (n : ℝ) := by ring
    rw [e3]; exact add_le_add h1 h2
  have hWb0 : 0 ≤ Wb := by
    have : 0 ≤ w n / s1 n ^ 2 := (div_pos (hw.pos n hn4) (by positivity)).le
    linarith
  have hQ : 0 ≤ ∑ m ∈ Finset.Icc 1 M, (w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| + w ((n : ℝ) - m) * |θ ((n : ℝ) - m)|) /
              (s1 n ^ 2 * (m : ℝ) ^ 2) := by
    refine Finset.sum_nonneg fun m hm => ?_
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have hw1 : 0 < w ((n : ℝ) + m) := hw.pos _ (by linarith)
    have hw2 : 0 < w ((n : ℝ) - m) := hw.pos _ (by linarith)
    positivity
  have hm1 : Cp * Wb * (∑ m ∈ Finset.Icc 1 M, (1 / ((n : ℝ) * (m : ℝ) ^ 2) + 1 / (n : ℝ) ^ 2)) ≤
      (3 * Cp + 4 * Real.exp (2 * C0)) * Wb / n := by
    calc _ ≤ Cp * Wb * (3 / (n : ℝ)) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 3 * Cp * Wb / n := by ring
      _ ≤ (3 * Cp + 4 * Real.exp (2 * C0)) * Wb / n := by
          apply div_le_div_of_nonneg_right _ hn0.le
          have : 0 ≤ 4 * Real.exp (2 * C0) * Wb := by positivity
          nlinarith only [this]
  have hm2 : 4 * Real.exp (2 * C0) * ∑ m ∈ Finset.Icc 1 M, (w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| + w ((n : ℝ) - m) * |θ ((n : ℝ) - m)|) /
              (s1 n ^ 2 * (m : ℝ) ^ 2) ≤ (3 * Cp + 4 * Real.exp (2 * C0)) * ∑ m ∈ Finset.Icc 1 M, (w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| + w ((n : ℝ) - m) * |θ ((n : ℝ) - m)|) /
              (s1 n ^ 2 * (m : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hQ
  linarith

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.pair_drift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pair_drift

end FormalResearch.ModularBootstrap.FiveTerm
