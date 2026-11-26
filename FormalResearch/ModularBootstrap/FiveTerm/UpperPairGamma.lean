module

public import FormalResearch.ModularBootstrap.FiveTerm.UpperPairDrift

/-!
# Weighted pair drift (FIVE-U; `cts:tip-shared` (b2))

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Lemma C11$_0$ (`cts:tip-shared`) (b2).

With the kernel `f(u, W) = W u/(u² + W)` (`fpair`), `T_k (x - s_k) = ∓ s'(n) f(±u, W)`, the antisymmetrised pair
`f(u_{+m}, W_{+m}) - f(u_{-m}, W_{-m})` is `O(W_b (1/n + 1/m²))` (`pairf_cancel`); `pair_drift_gamma` is (b2) in
explicit-constant form: for `|γ_k| ≤ C₀ λ`, `|γ_{n±m} - γ_n| ≤ C₀ λ m/n`, `|θ_k| ≤ 1`,
`|∑_{m ≤ M} (γ_{n+m} T_{n+m}(x - s_{n+m}) + γ_{n-m} T_{n-m}(x - s_{n-m}))| ≤ C λ s'(n) (W_b + ∑_m (w|θ| terms)/(s'² m))`.

All statements are proved. The hypotheses are `n ≥ n₁(C₀,c₀)`, `1 ≤ M ≤ n/2`, `W_n ≤ W_b ≤ c₀`.
-/

@[expose] public section

open Set

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- The pair-height kernel `f(u, W) = W u / (u² + W)` (the paper's `T (s - s_k)` up to the scale). -/
noncomputable def fpair (u W : ℝ) : ℝ := W * u / (u ^ 2 + W)

lemma fpair_neg (u W : ℝ) : fpair (-u) W = -fpair u W := by
  unfold fpair; ring_nf

lemma abs_fpair_le {u W : ℝ} (hu : 0 < u) (hW : 0 ≤ W) : |fpair u W| ≤ W / u := by
  unfold fpair
  rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hu]
  nlinarith only [mul_nonneg hW (sq_nonneg u), mul_nonneg hW hW, hu]

lemma fpair_W_lip {u W V : ℝ} (hu : 0 < u) (hW : 0 ≤ W) (hV : 0 ≤ V) :
    |fpair u V - fpair u W| ≤ |V - W| / u := by
  unfold fpair
  have hid : V * u / (u ^ 2 + V) - W * u / (u ^ 2 + W) =
      u ^ 3 * (V - W) / ((u ^ 2 + V) * (u ^ 2 + W)) := by
    field_simp; ring
  rw [hid, abs_div, abs_mul, abs_of_pos (by positivity : 0 < u ^ 3),
    abs_of_pos (by positivity : 0 < (u ^ 2 + V) * (u ^ 2 + W)), div_le_div_iff₀ (by positivity) hu]
  have h1 : u ^ 4 ≤ (u ^ 2 + V) * (u ^ 2 + W) := by
    nlinarith only [mul_nonneg hW (sq_nonneg u), mul_nonneg hV (sq_nonneg u), mul_nonneg hW hV, sq_nonneg u]
  have h2 : 0 ≤ |V - W| := abs_nonneg _
  nlinarith only [mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 hu.le), h2, hu]

lemma fpair_u_lip {u0 u1 W : ℝ} (h0 : 0 < u0) (h1 : 0 < u1) (hW : 0 ≤ W) :
    |fpair u1 W - fpair u0 W| ≤ W * |u1 - u0| * (W + u0 * u1) / (u0 ^ 2 * u1 ^ 2) := by
  unfold fpair
  have hid : W * u1 / (u1 ^ 2 + W) - W * u0 / (u0 ^ 2 + W) =
      W * ((u1 - u0) * (W - u0 * u1)) / ((u1 ^ 2 + W) * (u0 ^ 2 + W)) := by
    field_simp; ring
  rw [hid, abs_div, abs_mul, abs_mul, abs_of_nonneg hW,
    abs_of_pos (by positivity : 0 < (u1 ^ 2 + W) * (u0 ^ 2 + W))]
  have hd : u0 ^ 2 * u1 ^ 2 ≤ (u1 ^ 2 + W) * (u0 ^ 2 + W) := by
    nlinarith only [mul_nonneg hW (sq_nonneg u0), mul_nonneg hW (sq_nonneg u1), mul_nonneg hW hW,
      sq_nonneg u0, sq_nonneg u1]
  have hn : |W - u0 * u1| ≤ W + u0 * u1 := by
    rw [abs_le]; constructor <;> nlinarith only [mul_pos h0 h1, hW]
  calc W * (|u1 - u0| * |W - u0 * u1|) / ((u1 ^ 2 + W) * (u0 ^ 2 + W)) ≤
        W * (|u1 - u0| * (W + u0 * u1)) / (u0 ^ 2 * u1 ^ 2) := by
        apply div_le_div₀ (by positivity) _ (by positivity) hd
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (abs_nonneg _)) hW
    _ = _ := by ring


/-- One-sided Lipschitz estimate for the pair-height kernel. -/
lemma pairf_one_sided {K c c0 : ℝ} (hK : 1 ≤ K) (hc : 0 < c) (hc4 : c ≤ 1 / 4) (hc0 : 1 ≤ c0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n u0 u1 W0 W1 b k r ρ Wb : ℝ), 1 ≤ m → 2 * m ≤ n →
      m / 4 ≤ u0 → u0 ≤ 2 * m → u1 = u0 + k * m ^ 2 / 2 + r → c * m ≤ u1 →
      W1 = W0 * (1 + b * m + ρ) → 0 ≤ W0 → W0 ≤ Wb → Wb ≤ c0 → 0 ≤ W1 →
      |b| ≤ K / n → |k| ≤ K / n → |r| ≤ K * m ^ 3 / n ^ 2 → |ρ| ≤ K * m ^ 2 / n ^ 2 →
      |fpair u1 W1 - fpair u0 W0| ≤ C * Wb / n := by
  refine ⟨3 * K / (2 * c) + 16 * K * (c0 + 4 + K) / c ^ 2, by positivity, ?_⟩
  intro m n u0 u1 W0 W1 b k r ρ Wb hm hn hu0 hu0' hu1 hcu hW1 hW0 hW0b hWbc hW1p hb hk hr hρ
  have hn0 : 0 < n := by linarith
  have hm0 : 0 < m := by linarith
  have hu0p : 0 < u0 := by linarith
  have hu1p : 0 < u1 := by nlinarith only [hcu, hm0, hc]
  obtain ⟨hd, -⟩ := inv_sq_diff_le hm hn hK hc hu0 hu0' hu1 hcu hc4 hk hr
  have hWb0 : 0 ≤ Wb := hW0.trans hW0b
  have hbm : |b * m + ρ| ≤ 3 * K * m / (2 * n) := by
    have h1 : |b * m| ≤ K * m / n := by
      rw [abs_mul, abs_of_pos hm0]
      calc |b| * m ≤ K / n * m := mul_le_mul_of_nonneg_right hb hm0.le
        _ = K * m / n := by ring
    have h2 : |ρ| ≤ K * m / (2 * n) := by
      refine hρ.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ K * m * n)]
    calc |b * m + ρ| ≤ |b * m| + |ρ| := abs_add_le _ _
      _ ≤ K * m / n + K * m / (2 * n) := add_le_add h1 h2
      _ = 3 * K * m / (2 * n) := by field_simp; ring
  have t1 : |fpair u1 W1 - fpair u1 W0| ≤ 3 * K / (2 * c) * Wb / n := by
    refine (fpair_W_lip hu1p hW0 hW1p).trans ?_
    have hW10 : W1 - W0 = W0 * (b * m + ρ) := by rw [hW1]; ring
    rw [hW10, abs_mul, abs_of_nonneg hW0]
    calc W0 * |b * m + ρ| / u1 ≤ Wb * (3 * K * m / (2 * n)) / (c * m) :=
          div_le_div₀ (by positivity) (mul_le_mul hW0b hbm (abs_nonneg _) hWb0) (by positivity) hcu
      _ = 3 * K / (2 * c) * Wb / n := by field_simp
  have t2 : |fpair u1 W0 - fpair u0 W0| ≤ 16 * K * (c0 + 4 + K) / c ^ 2 * Wb / n := by
    refine (fpair_u_lip hu0p hu1p hW0).trans ?_
    have hu1u : u1 ≤ (2 + K / 2) * m := by
      have : u1 ≤ u0 + K * m ^ 2 / n := by linarith [(abs_le.mp hd).2]
      have h5 : K * m ^ 2 / n ≤ K * m / 2 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith only [mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ K * m)]
      nlinarith only [this, h5, hu0']
    have hnum : W0 + u0 * u1 ≤ (c0 + 4 + K) * m ^ 2 := by
      have h1 : u0 * u1 ≤ (2 * m) * ((2 + K / 2) * m) :=
        mul_le_mul hu0' hu1u hu1p.le (by positivity)
      have hm2 : (1 : ℝ) ≤ m ^ 2 := by nlinarith only [hm]
      have h2 : W0 ≤ c0 * m ^ 2 := by
        nlinarith only [hW0b, hWbc, mul_le_mul_of_nonneg_left hm2 (by linarith : (0:ℝ) ≤ c0)]
      nlinarith only [h1, h2, hm]
    have hden : c ^ 2 * m ^ 4 / 16 ≤ u0 ^ 2 * u1 ^ 2 := by
      have h6 : (m / 4) ^ 2 * (c * m) ^ 2 ≤ u0 ^ 2 * u1 ^ 2 :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hu0 2) (pow_le_pow_left₀ (by positivity) hcu 2)
          (by positivity) (by positivity)
      nlinarith only [h6]
    have hnum2 : W0 * |u1 - u0| * (W0 + u0 * u1) ≤ Wb * (K * m ^ 2 / n) * ((c0 + 4 + K) * m ^ 2) :=
      mul_le_mul (mul_le_mul hW0b hd (abs_nonneg _) hWb0) hnum (by positivity) (by positivity)
    calc W0 * |u1 - u0| * (W0 + u0 * u1) / (u0 ^ 2 * u1 ^ 2) ≤
          Wb * (K * m ^ 2 / n) * ((c0 + 4 + K) * m ^ 2) / (c ^ 2 * m ^ 4 / 16) :=
          div_le_div₀ (by positivity) hnum2 (by positivity) hden
      _ = 16 * K * (c0 + 4 + K) / c ^ 2 * Wb / n := by field_simp
  calc |fpair u1 W1 - fpair u0 W0| = |(fpair u1 W1 - fpair u1 W0) + (fpair u1 W0 - fpair u0 W0)| := by
        congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add t1 t2)
    _ = _ := by ring


/-- The antisymmetrised pair of pair-height kernels is `O(W_b (1/n + 1/m²))`. -/
lemma pairf_cancel {K c c0 : ℝ} (hK : 1 ≤ K) (hc : 0 < c) (hc4 : c ≤ 1 / 4) (hc0 : 1 ≤ c0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n ς W0 W1 W2 b k r1 r2 ρ1 ρ2 Wb u1 u2 : ℝ), 1 ≤ m → 2 * m ≤ n →
      |ς| ≤ 3 / 4 →
      u1 = (m + ς) + k * m ^ 2 / 2 + r1 → c * m ≤ u1 →
      u2 = (m - ς) + (-k) * m ^ 2 / 2 + (-r2) → c * m ≤ u2 →
      W1 = W0 * (1 + b * m + ρ1) → W2 = W0 * (1 + (-b) * m + ρ2) → 0 ≤ W0 → W0 ≤ Wb → Wb ≤ c0 →
      0 ≤ W1 → 0 ≤ W2 → |b| ≤ K / n → |k| ≤ K / n → |r1| ≤ K * m ^ 3 / n ^ 2 → |r2| ≤ K * m ^ 3 / n ^ 2 →
      |ρ1| ≤ K * m ^ 2 / n ^ 2 → |ρ2| ≤ K * m ^ 2 / n ^ 2 →
      |fpair u1 W1 - fpair u2 W2| ≤ C * Wb * (1 / n + 1 / m ^ 2) := by
  obtain ⟨C1, hC1, hL⟩ := pairf_one_sided (K := K) (c := c) (c0 := c0) hK hc hc4 hc0
  refine ⟨2 * C1 + 384 * (c0 + 4), by positivity, ?_⟩
  intro m n ς W0 W1 W2 b k r1 r2 ρ1 ρ2 Wb u1 u2 hm hn hς hu1 hcu1 hu2 hcu2 hW1 hW2 hW0 hW0b hWbc hW1p hW2p
    hb hk hr1 hr2 hρ1 hρ2
  have hn0 : 0 < n := by linarith
  have hm0 : 0 < m := by linarith
  have hς' := abs_le.mp hς
  have hu0 : m / 4 ≤ m + ς := by linarith
  have hu0' : m + ς ≤ 2 * m := by linarith
  have hv0 : m / 4 ≤ m - ς := by linarith
  have hv0' : m - ς ≤ 2 * m := by linarith
  have hWb0 : 0 ≤ Wb := hW0.trans hW0b
  have A1 := hL m n (m + ς) u1 W0 W1 b k r1 ρ1 Wb hm hn hu0 hu0' hu1 hcu1 hW1 hW0 hW0b hWbc hW1p hb hk hr1 hρ1
  have A2 := hL m n (m - ς) u2 W0 W2 (-b) (-k) (-r2) ρ2 Wb hm hn hv0 hv0' hu2 hcu2 hW2 hW0 hW0b hWbc hW2p
    (by rwa [abs_neg]) (by rwa [abs_neg]) (by rwa [abs_neg]) hρ2
  have hu0p : 0 < m + ς := by linarith
  have hv0p : 0 < m - ς := by linarith
  have hsym : |fpair (m + ς) W0 - fpair (m - ς) W0| ≤ 384 * (c0 + 4) * Wb / m ^ 2 := by
    refine (fpair_u_lip hv0p hu0p hW0).trans ?_
    have hm2 : (1 : ℝ) ≤ m ^ 2 := by nlinarith only [hm]
    have hd : m ^ 4 / 256 ≤ (m - ς) ^ 2 * (m + ς) ^ 2 := by
      have := mul_le_mul (pow_le_pow_left₀ (by positivity) hv0 2) (pow_le_pow_left₀ (by positivity) hu0 2)
        (by positivity) (by positivity)
      nlinarith only [this]
    have hW0c : W0 ≤ c0 * m ^ 2 := by
      nlinarith only [hW0b, hWbc, mul_le_mul_of_nonneg_left hm2 (by linarith : (0:ℝ) ≤ c0)]
    have huv : (m - ς) * (m + ς) ≤ 4 * m ^ 2 := by nlinarith only [sq_nonneg ς, sq_nonneg m]
    have hnum : W0 * |m + ς - (m - ς)| * (W0 + (m - ς) * (m + ς)) ≤
        Wb * (3 / 2) * ((c0 + 4) * m ^ 2) := by
      have h1 : |m + ς - (m - ς)| ≤ 3 / 2 := by
        rw [show m + ς - (m - ς) = 2 * ς by ring, abs_mul, abs_two]; linarith
      have h2 : W0 + (m - ς) * (m + ς) ≤ (c0 + 4) * m ^ 2 := by nlinarith only [hW0c, huv]
      exact mul_le_mul (mul_le_mul hW0b h1 (abs_nonneg _) hWb0) h2 (by positivity) (by positivity)
    calc W0 * |m + ς - (m - ς)| * (W0 + (m - ς) * (m + ς)) / ((m - ς) ^ 2 * (m + ς) ^ 2) ≤
          Wb * (3 / 2) * ((c0 + 4) * m ^ 2) / (m ^ 4 / 256) :=
          div_le_div₀ (by positivity) hnum (by positivity) hd
      _ = 384 * (c0 + 4) * Wb / m ^ 2 := by field_simp; ring
  have hodd : fpair u1 W1 - fpair u2 W2 =
      (fpair u1 W1 - fpair (m + ς) W0) - (fpair u2 W2 - fpair (m - ς) W0) +
        (fpair (m + ς) W0 - fpair (m - ς) W0) := by ring
  rw [hodd]
  calc _ ≤ |(fpair u1 W1 - fpair (m + ς) W0) - (fpair u2 W2 - fpair (m - ς) W0)| +
        |fpair (m + ς) W0 - fpair (m - ς) W0| := abs_add_le _ _
    _ ≤ (C1 * Wb / n + C1 * Wb / n) + 384 * (c0 + 4) * Wb / m ^ 2 :=
        add_le_add ((abs_sub _ _).trans (add_le_add A1 A2)) hsym
    _ = (2 * C1) * Wb / n + 384 * (c0 + 4) * Wb / m ^ 2 := by ring
    _ ≤ _ := by
        have h1 : 0 ≤ 2 * C1 * Wb / m ^ 2 := by positivity
        have h2 : 0 ≤ 384 * (c0 + 4) * Wb / n := by positivity
        have e : (2 * C1 + 384 * (c0 + 4)) * Wb * (1 / n + 1 / m ^ 2) =
            2 * C1 * Wb / n + 384 * (c0 + 4) * Wb / m ^ 2 + (384 * (c0 + 4) * Wb / n + 2 * C1 * Wb / m ^ 2) := by
          field_simp; ring
        rw [e]; linarith


/-- One `±m` pair of the `γ`-weighted pair-height sum (`cts:tip-shared` (b2), single pair). -/
lemma gamma_term {C0 c0 : ℝ} (hC0 : 0 ≤ C0) (hc0 : 1 ≤ c0) :
    ∃ C n1 : ℝ, 0 ≤ C ∧ ∀ (s s1 s2 s3 w w1 w2 : ℝ → ℝ), ScaleHyp s s1 s2 s3 C0 → WeightHyp w w1 w2 C0 →
      ∀ (n m x Wb lam γp γm γ0 θp θm : ℝ), n1 ≤ n → 1 ≤ m → 2 * m ≤ n →
        s (n - 1 / 2) ≤ x → x ≤ s (n + 1 / 2) → w n / (s1 n) ^ 2 ≤ Wb → Wb ≤ c0 → 0 ≤ lam →
        |γ0| ≤ C0 * lam → |γp - γ0| ≤ C0 * lam * m / n → |γm - γ0| ≤ C0 * lam * m / n →
        |θp| ≤ 1 → |θm| ≤ 1 →
        |γp * (w (n + m) * (1 + θp) / ((s (n + m) - x) ^ 2 + w (n + m) * (1 + θp)) * (x - s (n + m))) +
          γm * (w (n - m) * (1 + θm) / ((s (n - m) - x) ^ 2 + w (n - m) * (1 + θm)) * (x - s (n - m)))| ≤
        C * lam * s1 n * (Wb * (1 / n + 1 / m ^ 2) + Wb / n +
          (w (n + m) * |θp| + w (n - m) * |θm|) / (s1 n ^ 2 * m)) := by
  obtain ⟨C2, hC2, hP⟩ := pairf_cancel (K := pairK C0) (c := pairc C0) (c0 := c0) (pairK_ge hC0)
    (pairc_pos C0) (pairc_le hC0) hc0
  have hK := pairK_ge hC0
  have hcp := pairc_pos C0
  refine ⟨C0 * C2 + C0 / pairc C0 + 4 * (1 + pairK C0) * C0 / pairc C0, 3 * C0 + 2, by positivity, ?_⟩
  intro s s1 s2 s3 w w1 w2 hs hw n m x Wb lam γp γm γ0 θp θm hn hm hmn hx1 hx2 hWb hWbc hlam hγ0 hγp hγm
    hθp hθm
  have hn4 : 1 ≤ n := by linarith
  have hn0 : 0 < n := by linarith
  have hm0 : 0 < m := by linarith
  have hs1 : 0 < s1 n := hs.pos n hn4
  obtain ⟨ς, W0, W1, W2, b, k, r1, r2, ρ1, ρ2, u1, u2, hς, hςb, hW0, hW0p, hW1d, hW2d, hW1p, hW2p, hu1d, hu2d,
    hu1, hcu1, hu2, hcu2, hW1, hW2, bb, bk, br1, br2, bρ1, bρ2⟩ :=
    pair_setup hC0 s s1 s2 s3 w w1 w2 hs hw n m x hn hm hmn hx1 hx2
  have hWb' : W0 ≤ Wb := hW0 ▸ hWb
  have hWb0 : 0 ≤ Wb := hW0p.trans hWb'
  have P := hP m n ς W0 W1 W2 b k r1 r2 ρ1 ρ2 Wb u1 u2 hm hmn hςb hu1 hcu1 hu2 hcu2 hW1 hW2 hW0p hWb' hWbc
    hW1p hW2p bb bk br1 br2 bρ1 bρ2
  have hu1p : 0 < u1 := lt_of_lt_of_le (by positivity) hcu1
  have hu2p : 0 < u2 := lt_of_lt_of_le (by positivity) hcu2
  have hn1m : 1 ≤ n - m := by linarith
  have hw1p : 0 < w (n + m) := hw.pos _ (by linarith)
  have hw2p : 0 < w (n - m) := hw.pos _ hn1m
  have h1θ : 0 ≤ 1 + θp := by linarith [(abs_le.mp hθp).1]
  have h2θ : 0 ≤ 1 + θm := by linarith [(abs_le.mp hθm).1]
  -- the two pair terms in terms of the kernel
  have hd1p : 0 < s (n + m) - x := by
    rw [hu1d] at hu1p; exact (div_pos_iff_of_pos_right hs1).mp hu1p
  have hd2p : 0 < x - s (n - m) := by
    rw [hu2d] at hu2p; exact (div_pos_iff_of_pos_right hs1).mp hu2p
  have hden1 : 0 < (s (n + m) - x) ^ 2 + w (n + m) * (1 + θp) :=
    add_pos_of_pos_of_nonneg (pow_pos hd1p 2) (mul_nonneg hw1p.le h1θ)
  have hden2 : 0 < (s (n - m) - x) ^ 2 + w (n - m) * (1 + θm) :=
    add_pos_of_pos_of_nonneg (by nlinarith only [hd2p]) (mul_nonneg hw2p.le h2θ)
  have ea : w (n + m) * (1 + θp) / ((s (n + m) - x) ^ 2 + w (n + m) * (1 + θp)) * (x - s (n + m)) =
      -(s1 n * fpair u1 (W1 * (1 + θp))) := by
    unfold fpair
    rw [hW1d, hu1d]
    field_simp
    ring
  have eb : w (n - m) * (1 + θm) / ((s (n - m) - x) ^ 2 + w (n - m) * (1 + θm)) * (x - s (n - m)) =
      s1 n * fpair u2 (W2 * (1 + θm)) := by
    unfold fpair
    rw [hW2d, hu2d]
    have : (s (n - m) - x) ^ 2 = (x - s (n - m)) ^ 2 := by ring
    rw [this] at hden2 ⊢
    field_simp
  rw [ea, eb]
  set Fp := fpair u1 (W1 * (1 + θp)) with hFp
  set Fm := fpair u2 (W2 * (1 + θm)) with hFm
  have hKm : 0 < pairK C0 := by linarith
  -- sizes of the weights
  have hmn' : m / n ≤ 1 / 2 := by rw [div_le_iff₀ hn0]; linarith
  have hW1le : W1 ≤ (1 + pairK C0) * Wb := by
    have hbm : |b * m| ≤ pairK C0 / 2 := by
      rw [abs_mul, abs_of_pos hm0]
      calc |b| * m ≤ pairK C0 / n * m := mul_le_mul_of_nonneg_right bb hm0.le
        _ = pairK C0 * (m / n) := by ring
        _ ≤ pairK C0 * (1 / 2) := mul_le_mul_of_nonneg_left hmn' hKm.le
        _ = pairK C0 / 2 := by ring
    have hρ : |ρ1| ≤ pairK C0 / 4 := by
      refine bρ1.trans ?_
      have : m ^ 2 / n ^ 2 ≤ 1 / 4 := by
        rw [← div_pow]; nlinarith only [hmn', div_nonneg hm0.le hn0.le]
      calc pairK C0 * m ^ 2 / n ^ 2 = pairK C0 * (m ^ 2 / n ^ 2) := by ring
        _ ≤ pairK C0 * (1 / 4) := mul_le_mul_of_nonneg_left this hKm.le
        _ = _ := by ring
    have h3 : 1 + b * m + ρ1 ≤ 1 + pairK C0 := by
      have := (abs_le.mp hbm).2; have := (abs_le.mp hρ).2; linarith
    rw [hW1]
    calc W0 * (1 + b * m + ρ1) ≤ W0 * (1 + pairK C0) := mul_le_mul_of_nonneg_left h3 hW0p
      _ ≤ Wb * (1 + pairK C0) := mul_le_mul_of_nonneg_right hWb' (by linarith)
      _ = _ := by ring
  have hW2le : W2 ≤ (1 + pairK C0) * Wb := by
    have hbm : |(-b) * m| ≤ pairK C0 / 2 := by
      rw [abs_mul, abs_neg, abs_of_pos hm0]
      calc |b| * m ≤ pairK C0 / n * m := mul_le_mul_of_nonneg_right bb hm0.le
        _ = pairK C0 * (m / n) := by ring
        _ ≤ pairK C0 * (1 / 2) := mul_le_mul_of_nonneg_left hmn' hKm.le
        _ = pairK C0 / 2 := by ring
    have hρ : |ρ2| ≤ pairK C0 / 4 := by
      refine bρ2.trans ?_
      have : m ^ 2 / n ^ 2 ≤ 1 / 4 := by
        rw [← div_pow]; nlinarith only [hmn', div_nonneg hm0.le hn0.le]
      calc pairK C0 * m ^ 2 / n ^ 2 = pairK C0 * (m ^ 2 / n ^ 2) := by ring
        _ ≤ pairK C0 * (1 / 4) := mul_le_mul_of_nonneg_left this hKm.le
        _ = _ := by ring
    have h3 : 1 + (-b) * m + ρ2 ≤ 1 + pairK C0 := by
      have := (abs_le.mp hbm).2; have := (abs_le.mp hρ).2; linarith
    rw [hW2]
    calc W0 * (1 + (-b) * m + ρ2) ≤ W0 * (1 + pairK C0) := mul_le_mul_of_nonneg_left h3 hW0p
      _ ≤ Wb * (1 + pairK C0) := mul_le_mul_of_nonneg_right hWb' (by linarith)
      _ = _ := by ring
  have hcm : 0 < pairc C0 * m := by positivity
  have hFp_le : |Fp| ≤ 2 * (1 + pairK C0) * Wb / (pairc C0 * m) := by
    refine (abs_fpair_le hu1p (mul_nonneg hW1p h1θ)).trans ?_
    calc W1 * (1 + θp) / u1 ≤ (2 * ((1 + pairK C0) * Wb)) / (pairc C0 * m) := by
          apply div_le_div₀ (by positivity) _ hcm hcu1
          have : 1 + θp ≤ 2 := by linarith [(abs_le.mp hθp).2]
          nlinarith only [mul_le_mul hW1le this h1θ (by positivity), hW1p, h1θ]
      _ = _ := by ring
  have hFm_le : |Fm| ≤ 2 * (1 + pairK C0) * Wb / (pairc C0 * m) := by
    refine (abs_fpair_le hu2p (mul_nonneg hW2p h2θ)).trans ?_
    calc W2 * (1 + θm) / u2 ≤ (2 * ((1 + pairK C0) * Wb)) / (pairc C0 * m) := by
          apply div_le_div₀ (by positivity) _ hcm hcu2
          have : 1 + θm ≤ 2 := by linarith [(abs_le.mp hθm).2]
          nlinarith only [mul_le_mul hW2le this h2θ (by positivity), hW2p, h2θ]
      _ = _ := by ring
  -- the θ-perturbations
  have hθ1 : |Fp - fpair u1 W1| ≤ W1 * |θp| / (pairc C0 * m) := by
    refine (fpair_W_lip hu1p hW1p (mul_nonneg hW1p h1θ)).trans ?_
    have : W1 * (1 + θp) - W1 = W1 * θp := by ring
    rw [this, abs_mul, abs_of_nonneg hW1p]
    exact div_le_div_of_nonneg_left (by positivity) hcm hcu1
  have hθ2 : |Fm - fpair u2 W2| ≤ W2 * |θm| / (pairc C0 * m) := by
    refine (fpair_W_lip hu2p hW2p (mul_nonneg hW2p h2θ)).trans ?_
    have : W2 * (1 + θm) - W2 = W2 * θm := by ring
    rw [this, abs_mul, abs_of_nonneg hW2p]
    exact div_le_div_of_nonneg_left (by positivity) hcm hcu2
  have hdiff : |Fm - Fp| ≤ C2 * Wb * (1 / n + 1 / m ^ 2) + (W2 * |θm| + W1 * |θp|) / (pairc C0 * m) := by
    have e : Fm - Fp = (Fm - fpair u2 W2) + (-(fpair u1 W1 - fpair u2 W2)) - (Fp - fpair u1 W1) := by ring
    rw [e]
    calc _ ≤ |Fm - fpair u2 W2| + |-(fpair u1 W1 - fpair u2 W2)| + |Fp - fpair u1 W1| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ W2 * |θm| / (pairc C0 * m) + C2 * Wb * (1 / n + 1 / m ^ 2) + W1 * |θp| / (pairc C0 * m) := by
          rw [abs_neg]; exact add_le_add (add_le_add hθ2 P) hθ1
      _ = _ := by ring
  -- assemble
  have hfin : γp * -(s1 n * Fp) + γm * (s1 n * Fm) =
      γ0 * s1 n * (Fm - Fp) + (γm - γ0) * (s1 n * Fm) - (γp - γ0) * (s1 n * Fp) := by ring
  rw [hfin]
  have b1 : |γ0 * s1 n * (Fm - Fp)| ≤ C0 * lam * s1 n *
      (C2 * Wb * (1 / n + 1 / m ^ 2) + (W2 * |θm| + W1 * |θp|) / (pairc C0 * m)) := by
    rw [abs_mul, abs_mul, abs_of_pos hs1]
    calc |γ0| * s1 n * |Fm - Fp| ≤ (C0 * lam) * s1 n * (C2 * Wb * (1 / n + 1 / m ^ 2) +
          (W2 * |θm| + W1 * |θp|) / (pairc C0 * m)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hγ0 hs1.le) hdiff (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have b2 : |(γm - γ0) * (s1 n * Fm)| ≤ C0 * lam * s1 n * (2 * (1 + pairK C0) * Wb / (pairc C0 * n)) := by
    rw [abs_mul, abs_mul, abs_of_pos hs1]
    calc |γm - γ0| * (s1 n * |Fm|) ≤ (C0 * lam * m / n) * (s1 n * (2 * (1 + pairK C0) * Wb / (pairc C0 * m))) :=
          mul_le_mul hγm (mul_le_mul_of_nonneg_left hFm_le hs1.le) (by positivity) (by positivity)
      _ = _ := by field_simp
  have b3 : |(γp - γ0) * (s1 n * Fp)| ≤ C0 * lam * s1 n * (2 * (1 + pairK C0) * Wb / (pairc C0 * n)) := by
    rw [abs_mul, abs_mul, abs_of_pos hs1]
    calc |γp - γ0| * (s1 n * |Fp|) ≤ (C0 * lam * m / n) * (s1 n * (2 * (1 + pairK C0) * Wb / (pairc C0 * m))) :=
          mul_le_mul hγp (mul_le_mul_of_nonneg_left hFp_le hs1.le) (by positivity) (by positivity)
      _ = _ := by field_simp
  have hq : (W2 * |θm| + W1 * |θp|) / (pairc C0 * m) =
      (1 / pairc C0) * ((w (n + m) * |θp| + w (n - m) * |θm|) / (s1 n ^ 2 * m)) := by
    rw [hW1d, hW2d]; field_simp; ring
  calc _ ≤ |γ0 * s1 n * (Fm - Fp)| + |(γm - γ0) * (s1 n * Fm)| + |(γp - γ0) * (s1 n * Fp)| := by
        refine (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C0 * lam * s1 n * (C2 * Wb * (1 / n + 1 / m ^ 2) + (W2 * |θm| + W1 * |θp|) / (pairc C0 * m)) +
          C0 * lam * s1 n * (2 * (1 + pairK C0) * Wb / (pairc C0 * n)) +
          C0 * lam * s1 n * (2 * (1 + pairK C0) * Wb / (pairc C0 * n)) := add_le_add (add_le_add b1 b2) b3
    _ ≤ _ := by
        rw [hq]
        set Q : ℝ := (w (n + m) * |θp| + w (n - m) * |θm|) / (s1 n ^ 2 * m) with hQ
        have q0 : 0 ≤ Q := by positivity
        have hL : 0 ≤ lam * s1 n := by positivity
        have ha : 0 ≤ Wb * (1 / n + 1 / m ^ 2) := by positivity
        have hd : 0 ≤ Wb / n := by positivity
        have e1 : C0 * lam * s1 n * (C2 * Wb * (1 / n + 1 / m ^ 2) + 1 / pairc C0 * Q) +
            C0 * lam * s1 n * (2 * (1 + pairK C0) * Wb / (pairc C0 * n)) +
            C0 * lam * s1 n * (2 * (1 + pairK C0) * Wb / (pairc C0 * n)) =
            lam * s1 n * ((C0 * C2) * (Wb * (1 / n + 1 / m ^ 2)) + (C0 / pairc C0) * Q +
              (4 * (1 + pairK C0) * C0 / pairc C0) * (Wb / n)) := by ring
        rw [e1]
        have hB : (C0 * C2 + C0 / pairc C0 + 4 * (1 + pairK C0) * C0 / pairc C0) * lam * s1 n *
            (Wb * (1 / n + 1 / m ^ 2) + Wb / n + Q) -
            lam * s1 n * ((C0 * C2) * (Wb * (1 / n + 1 / m ^ 2)) + (C0 / pairc C0) * Q +
              (4 * (1 + pairK C0) * C0 / pairc C0) * (Wb / n)) =
            lam * s1 n * ((C0 / pairc C0 + 4 * (1 + pairK C0) * C0 / pairc C0) * (Wb * (1 / n + 1 / m ^ 2)) +
              (C0 * C2 + C0 / pairc C0) * (Wb / n) + (C0 * C2 + 4 * (1 + pairK C0) * C0 / pairc C0) * Q) := by
          ring
        have hnn : 0 ≤ lam * s1 n * ((C0 / pairc C0 + 4 * (1 + pairK C0) * C0 / pairc C0) * (Wb * (1 / n + 1 / m ^ 2)) +
              (C0 * C2 + C0 / pairc C0) * (Wb / n) + (C0 * C2 + 4 * (1 + pairK C0) * C0 / pairc C0) * Q) := by
          positivity
        linarith


/-- **Weighted pair drift, `cts:tip-shared` (b2)** (explicit-constant form). With `T_k = w_k/((x-s_k)² + w_k)`,
`w_k = w(k)(1+θ_k)`, `|θ_k| ≤ 1`, `|γ_k| ≤ C₀ λ` and `|γ_{n±m} - γ_n| ≤ C₀ λ m/n`,
`|∑_{1≤m≤M} (γ_{n+m} T_{n+m} (x - s_{n+m}) + γ_{n-m} T_{n-m} (x - s_{n-m}))|` is at most
`C λ s'(n) (W_b + ∑_m (w_{n+m}|θ_{n+m}| + w_{n-m}|θ_{n-m}|)/(s'(n)² m))`
(the paper's `O(λ s_n' W̄) + O(λ s_n' ϑ_N log(2M))`, the `θ`-sum over the sites across a join being
`≤ ϑ ∑ w/(s'² m) ≲ W̄ ϑ log (2M)`). Here `W_n = w(n)/s'(n)² ≤ W_b ≤ c₀`. -/
theorem pair_drift_gamma {C0 c0 : ℝ} (hC0 : 0 ≤ C0) (hc0 : 1 ≤ c0) :
    ∃ C n1 : ℝ, 0 ≤ C ∧ ∀ (s s1 s2 s3 w w1 w2 θ γ : ℝ → ℝ), ScaleHyp s s1 s2 s3 C0 → WeightHyp w w1 w2 C0 →
      ∀ (n M : ℕ) (x Wb lam : ℝ), n1 ≤ (n : ℝ) → 1 ≤ M → 2 * (M : ℝ) ≤ n →
        s ((n : ℝ) - 1 / 2) ≤ x → x ≤ s ((n : ℝ) + 1 / 2) → w n / (s1 n) ^ 2 ≤ Wb → Wb ≤ c0 → 0 ≤ lam →
        |γ n| ≤ C0 * lam →
        (∀ m ∈ Finset.Icc 1 M, |θ ((n : ℝ) + m)| ≤ 1 ∧ |θ ((n : ℝ) - m)| ≤ 1 ∧
          |γ ((n : ℝ) + m) - γ n| ≤ C0 * lam * m / n ∧ |γ ((n : ℝ) - m) - γ n| ≤ C0 * lam * m / n) →
        |∑ m ∈ Finset.Icc 1 M,
            (γ ((n : ℝ) + m) * (w ((n : ℝ) + m) * (1 + θ ((n : ℝ) + m)) /
                ((s ((n : ℝ) + m) - x) ^ 2 + w ((n : ℝ) + m) * (1 + θ ((n : ℝ) + m))) * (x - s ((n : ℝ) + m))) +
              γ ((n : ℝ) - m) * (w ((n : ℝ) - m) * (1 + θ ((n : ℝ) - m)) /
                ((s ((n : ℝ) - m) - x) ^ 2 + w ((n : ℝ) - m) * (1 + θ ((n : ℝ) - m))) * (x - s ((n : ℝ) - m))))| ≤
          C * lam * s1 n * (Wb + ∑ m ∈ Finset.Icc 1 M,
            (w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| + w ((n : ℝ) - m) * |θ ((n : ℝ) - m)|) /
              (s1 n ^ 2 * (m : ℝ))) := by
  obtain ⟨Cg, n1, hCg, hG⟩ := gamma_term (C0 := C0) (c0 := c0) hC0 hc0
  refine ⟨3 * Cg, n1, by positivity, ?_⟩
  intro s s1 s2 s3 w w1 w2 θ γ hs hw n M x Wb lam hn hM hMn hx1 hx2 hWb hWbc hlam hγ0 hdat
  have hn3 : (2 : ℝ) ≤ n := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hn4 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hs1 : 0 < s1 n := hs.pos n hn4
  have hWb0 : 0 ≤ Wb := by
    have : 0 ≤ w n / s1 n ^ 2 := (div_pos (hw.pos n hn4) (by positivity)).le
    linarith
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      |γ ((n : ℝ) + m) * (w ((n : ℝ) + m) * (1 + θ ((n : ℝ) + m)) /
                ((s ((n : ℝ) + m) - x) ^ 2 + w ((n : ℝ) + m) * (1 + θ ((n : ℝ) + m))) * (x - s ((n : ℝ) + m))) +
              γ ((n : ℝ) - m) * (w ((n : ℝ) - m) * (1 + θ ((n : ℝ) - m)) /
                ((s ((n : ℝ) - m) - x) ^ 2 + w ((n : ℝ) - m) * (1 + θ ((n : ℝ) - m))) * (x - s ((n : ℝ) - m)))| ≤
      Cg * lam * s1 n * (Wb * (1 / (n : ℝ) + 1 / (m : ℝ) ^ 2) + Wb / (n : ℝ) +
          (w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| + w ((n : ℝ) - m) * |θ ((n : ℝ) - m)|) /
            (s1 n ^ 2 * (m : ℝ))) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have hmn : 2 * (m : ℝ) ≤ n := by linarith
    obtain ⟨h1, h2, h3, h4⟩ := hdat m hm
    exact hG s s1 s2 s3 w w1 w2 hs hw n m x Wb lam (γ ((n : ℝ) + m)) (γ ((n : ℝ) - m)) (γ n)
      (θ ((n : ℝ) + m)) (θ ((n : ℝ) - m)) hn hm1 hmn hx1 hx2 hWb hWbc hlam hγ0 h3 h4 h1 h2
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsum1 : ∑ m ∈ Finset.Icc 1 M, (1 / (n : ℝ) + 1 / (m : ℝ) ^ 2) ≤ 5 / 2 := by
    rw [Finset.sum_add_distrib]
    have h1 : ∑ m ∈ Finset.Icc 1 M, 1 / (n : ℝ) ≤ 1 / 2 := by
      rw [Finset.sum_const, Nat.card_Icc]
      simp only [Nat.add_sub_cancel, nsmul_eq_mul]
      rw [mul_one_div, div_le_div_iff₀ hn0 (by norm_num)]
      linarith
    have h2 := sum_inv_sq_le M hM
    have h3 : 1 / (M : ℝ) ≥ 0 := by positivity
    linarith
  have hsum2 : ∑ m ∈ Finset.Icc 1 M, Wb / (n : ℝ) ≤ Wb / 2 := by
    rw [Finset.sum_const, Nat.card_Icc]
    simp only [Nat.add_sub_cancel, nsmul_eq_mul]
    rw [mul_div_assoc', div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith only [mul_le_mul_of_nonneg_left hMn hWb0]
  have hQ : 0 ≤ ∑ m ∈ Finset.Icc 1 M, (w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| + w ((n : ℝ) - m) * |θ ((n : ℝ) - m)|) /
              (s1 n ^ 2 * (m : ℝ)) := by
    refine Finset.sum_nonneg fun m hm => ?_
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have hw1 : 0 < w ((n : ℝ) + m) := hw.pos _ (by linarith)
    have hw2 : 0 < w ((n : ℝ) - m) := hw.pos _ (by linarith)
    positivity
  have hL : 0 ≤ Cg * lam * s1 n := by positivity
  have : Wb * ∑ m ∈ Finset.Icc 1 M, (1 / (n : ℝ) + 1 / (m : ℝ) ^ 2) + ∑ m ∈ Finset.Icc 1 M, Wb / (n : ℝ) ≤ 3 * Wb := by
    nlinarith only [mul_le_mul_of_nonneg_left hsum1 hWb0, hsum2]
  calc _ ≤ Cg * lam * s1 n * (3 * Wb + ∑ m ∈ Finset.Icc 1 M, (w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| + w ((n : ℝ) - m) * |θ ((n : ℝ) - m)|) /
              (s1 n ^ 2 * (m : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hL
        linarith
    _ ≤ _ := by
        have : Cg * lam * s1 n * (3 * Wb + ∑ m ∈ Finset.Icc 1 M, (w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| + w ((n : ℝ) - m) * |θ ((n : ℝ) - m)|) /
              (s1 n ^ 2 * (m : ℝ))) ≤ 3 * Cg * lam * s1 n * (Wb + ∑ m ∈ Finset.Icc 1 M, (w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| + w ((n : ℝ) - m) * |θ ((n : ℝ) - m)|) /
              (s1 n ^ 2 * (m : ℝ))) := by
          have h3 : 0 ≤ Cg * lam * s1 n * (2 * ∑ m ∈ Finset.Icc 1 M, (w ((n : ℝ) + m) * |θ ((n : ℝ) + m)| + w ((n : ℝ) - m) * |θ ((n : ℝ) - m)|) /
              (s1 n ^ 2 * (m : ℝ))) := by positivity
          nlinarith only [h3]
        exact this

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.pair_drift_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pair_drift_gamma

end FormalResearch.ModularBootstrap.FiveTerm
