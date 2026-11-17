module

public import FormalResearch.Special.DiscreteAiryKappaChart
public import FormalResearch.Special.DiscreteAiryKappaRight
public import FormalResearch.Special.DiscreteAiryKappaEdge
public import FormalResearch.Special.DiscreteAiryLimitChainsHahnAiry
public import FormalResearch.Special.DiscreteAiryOscBi
public import FormalResearch.Special.AiryEnvelopeReal

/-!
# `κ ≠ 0` for the actual `3j` chain at a lattice node (plan K1, steps M-d, M-e)

Fix integers `M, σ` and a rational `x ∈ (0,1)`; `h = 1/N`, `q_* = √(1-x²)`, `Ŷ_k = √(2k+1) Φ_k` the natural-gauge chain at the node
`x_n = x`.  `hahn_chain_airy_full` (`DiscreteAiryPhysChains`) writes `Ŷ = κ g Ai(X) + μ g Bi(X)` up to `C δ³ (|κ| airyWt + |μ| airyBiWt)` on the
macroscopic window `[J, N_w + 1]` but leaves `κ` unidentified.  The mass argument (Gauss weight `Σ_k Ŷ_k² = N`) bounds `κ` from below:

1. **window** (`DiscreteAiryKappaChart`): for `J ≤ k ≤ m + 1` (`X_k ≤ 1/4`, `g ≤ g_max`): `|Ŷ_k| ≤ A_κ |κ| + A_μ |μ|`, and
   `|μ| ≤ C_μ |Ŷ_{m+1}| e^{-ξ₀ N}/δ` (apply `DaiFull.pointwise` with `Y_max = |Ŷ_{m+1}|`, legitimate by step 3), hence `|Ŷ_k| ≤ 2 A_κ |κ|`;
2. **left** (`kl_hahn_left`, `DiscreteAiryKappaEdge`): `Ŷ_k² ≤ C_left (Ŷ_{J+1}² + Ŷ_J²)` for **every** `k ≤ J + 1` including the hard
   edge `k = O(1)`;
3. **right** (`kr_chain_mono`, `DiscreteAiryKappaRight`): `Ŷ_k² ≤ Ŷ_{m+1}²` for all `k ≥ m + 1`;
4. **mass** (`gaussWeight_3j`, `kf_mass_le`): `N = Σ Ŷ_k² ≤ N sup_k Ŷ_k² ≤ N · 8 C_left A_κ² κ²`, so `κ² ≥ 1/(8 C_left A_κ²)`.

**Claim class: proved** (`hahn_chain_kappa`), all constants explicit in the constants of `kc_hahn_full`, `ke_C`.  The bound `|κ| ≥ κ_min > 0` is
uniform in `N` but crude (`e^{O(1)}` control of the adiabatic invariant only).  It is superseded for the size of `κ` by `hahn_chain_kappa_order`
(`c_lo ≤ κ² δ ≤ c_up`, `δ³ = 1/N`, `DiscreteAiryKappaOrder`) and for its value by `hahn_chain_kappa_sharp` (`|κ² δ - 2| ≤ τ` for `1/N ≤ ε₁(τ)`, i.e.
`κ² = 2N^{1/3}(1+o(1))`, `DiscreteAiryKappaSharpFinal`), which use the second-order (Ermakov) adiabatic invariant with `1 + o(1)` amplitude over the whole left band
(`DiscreteAiryKappaErmakov`, `DiscreteAiryKappaSharp*`); this module keeps the mass argument and its ingredients that the later modules reuse
(`kf_mass_le`, `kf_window_abs`, `kf_mu_bound`, `kf_absorb`).  *Numerical check of the theorem (mpmath, 30 digits, scratch, not a Lean claim):* for the actual
chain `|κ| = |Ŷ_k|/(g Ai(X_k))` near the turn is `√2 N^{1/6}(1 + o(1))`: `M = σ = 0`, `x = 1/2`, `N = 22, 86, 342`:
`2.37, 2.97, 3.74` against `√2 N^{1/6} = 2.37, 2.97, 3.74`.  The heuristic mass identity
`N = Σ Ŷ² ≈ N κ² N^{-1/3}/(2π) ∫_0^{q_*} dq/(A sin φ) = κ² N^{2/3}/2` (`A sin φ = ½√(q_*² - q²)`, `∫ = π`) gives `κ² = 2 N^{1/3}`, independent of
`(M, σ, x)`; its rigorous version is `hahn_chain_kappa_sharp`.

**Not formalised** (anywhere in the tree; this module proves only `κ_min`, the order and the value are in the modules named above): the Darboux phase and sign of `κ`; `τ = -1`; half-integer chains; Racah;
uniformity of the constants in `x` (the matching without `κ` is uniform in `x ∈ [x₀, x₁]`: `hahn_chain_airy_full_unif`, `DiscreteAiryUnifHahn`; `κ_min` is not).
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `|Ai(X)| ≤ 3` for every real `X` (from the complex envelope `airyAiC_envelope`). -/
lemma kf_abs_airyAi_le (X : ℝ) : |airyAi X| ≤ 3 := by
  have h := airyAiC_envelope (X : ℂ)
  rw [norm_airyAiC_ofReal, re_ofReal_cpow_three_halves, Complex.norm_real, Real.norm_eq_abs] at h
  have h1 : (1 + |X|) ^ (-(1 / 4) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg X]) (by norm_num)
  have h2 : Real.exp (-(2 / 3) * (max X 0) ^ (3 / 2 : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (max X 0) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (le_max_right _ _) _
    linarith
  have h3 : 0 ≤ (1 + |X|) ^ (-(1 / 4) : ℝ) := Real.rpow_nonneg (by positivity) _
  have h4 := Real.exp_pos (-(2 / 3) * (max X 0) ^ (3 / 2 : ℝ))
  calc |airyAi X| ≤ _ := h
    _ ≤ 3 * 1 * 1 := by gcongr
    _ = 3 := by norm_num

/-- `airyBiWt X ≤ 8` for `X ≤ 1`. -/
lemma kf_airyBiWt_le {X : ℝ} (hX : X ≤ 1) : airyBiWt X ≤ 8 := by
  rw [airyBiWt_eq_mul]
  have h1 := airyWt_le_one X
  have h2 : airyXi X ≤ 2 / 3 := by
    unfold airyXi
    have h0 : 0 ≤ max X 0 := le_max_right _ _
    have h3 : max X 0 ≤ 1 := max_le hX zero_le_one
    have : (max X 0) ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one h0 h3 (by norm_num)
    linarith
  have h4 : Real.exp (2 * airyXi X) ≤ 8 := by
    have : Real.exp (2 * airyXi X) ≤ Real.exp 2 := Real.exp_le_exp.2 (by linarith)
    have h5 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h6 := Real.exp_one_lt_d9
    nlinarith [Real.exp_pos 1]
  have h7 := airyWt_pos X
  nlinarith [Real.exp_pos (2 * airyXi X)]

/-- Window estimate at one site: if `|Y - (κ g Ai(X) + μ g Bi(X))| ≤ C δ³ (|κ| airyWt + |μ| airyBiWt)`, `|g| ≤ g_max`, `X ≤ 1`, `δ³ ≤ 1`:
`|Y| ≤ (3 g_max + C) |κ| + (3600 g_max + 8 C) |μ|`. -/
lemma kf_window_site {Y g X κ μ C δ3 gmax : ℝ} (hC : 0 ≤ C) (hδ1 : δ3 ≤ 1) (hg : |g| ≤ gmax) (hX : X ≤ 1)
    (hY : |Y - (κ * (g * airyAi X) + μ * (g * airyBi X))| ≤ C * δ3 * (|κ| * airyWt X + |μ| * airyBiWt X)) :
    |Y| ≤ (3 * gmax + C) * |κ| + (3600 * gmax + 8 * C) * |μ| := by
  have hg0 : 0 ≤ gmax := (abs_nonneg _).trans hg
  have hAi := kf_abs_airyAi_le X
  have hBi := (apx_airyBi_global X).1
  have hBw := kf_airyBiWt_le hX
  have hW := airyWt_le_one X
  have hBw0 := (airyBiWt_pos X).le
  have hW0 := (airyWt_pos X).le
  have t1 : |κ * (g * airyAi X)| ≤ 3 * gmax * |κ| := by
    rw [abs_mul, abs_mul]
    have := mul_le_mul hg hAi (abs_nonneg _) hg0
    nlinarith [abs_nonneg κ]
  have t2 : |μ * (g * airyBi X)| ≤ 3600 * gmax * |μ| := by
    rw [abs_mul, abs_mul]
    have h450 : |airyBi X| ≤ 450 * 8 := hBi.trans (by linarith)
    have := mul_le_mul hg h450 (abs_nonneg _) hg0
    nlinarith [abs_nonneg μ]
  have t3 : C * δ3 * (|κ| * airyWt X + |μ| * airyBiWt X) ≤ C * (|κ| + 8 * |μ|) := by
    have h1 : |κ| * airyWt X ≤ |κ| := mul_le_of_le_one_right (abs_nonneg _) hW
    have h2 : |μ| * airyBiWt X ≤ |μ| * 8 := mul_le_mul_of_nonneg_left hBw (abs_nonneg _)
    have h3 : C * δ3 ≤ C := mul_le_of_le_one_right hC hδ1
    calc _ ≤ C * (|κ| * airyWt X + |μ| * airyBiWt X) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ ≤ C * (|κ| + 8 * |μ|) := by apply mul_le_mul_of_nonneg_left _ hC; linarith
  have e : Y = (Y - (κ * (g * airyAi X) + μ * (g * airyBi X))) + (κ * (g * airyAi X) + μ * (g * airyBi X)) := by ring
  calc |Y| = |(Y - (κ * (g * airyAi X) + μ * (g * airyBi X))) + (κ * (g * airyAi X) + μ * (g * airyBi X))| := by rw [← e]
    _ ≤ |Y - (κ * (g * airyAi X) + μ * (g * airyBi X))| + |κ * (g * airyAi X) + μ * (g * airyBi X)| := abs_add_le _ _
    _ ≤ |Y - (κ * (g * airyAi X) + μ * (g * airyBi X))| + (|κ * (g * airyAi X)| + |μ * (g * airyBi X)|) := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by nlinarith [abs_nonneg κ, abs_nonneg μ]

/-- **The mass bound** (`gaussWeight_3j`): if `Ŷ_k² ≤ B` for all `k` then `N ≤ N B`. -/
lemma kf_mass_le (M σ N : ℤ) (hN : max |M| |σ| < N) (n : ℕ) (hn : (n : ℤ) < N - max |M| |σ|) {B : ℝ}
    (hB : ∀ k : ℤ, hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) k ^ 2 ≤ B) : (N : ℝ) ≤ N * B := by
  have hN0 : (0 : ℤ) < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  set L0 : ℤ := max |M| |σ| with hL0
  have hL00 : 0 ≤ L0 := le_trans (abs_nonneg M) (le_max_left _ _)
  set K : ℕ := (N - L0).toNat with hKdef
  have hK : (K : ℚ) = (N : ℚ) - max |(M : ℚ)| |(σ : ℚ)| := by
    have e : max |(M : ℚ)| |(σ : ℚ)| = (L0 : ℚ) := by rw [hL0]; push_cast; rfl
    rw [e]
    have : (K : ℤ) = N - L0 := Int.toNat_of_nonneg (by omega)
    have h2 : ((K : ℤ) : ℚ) = ((N - L0 : ℤ) : ℚ) := by rw [this]
    push_cast at h2
    exact h2
  have hnK : n < K := by omega
  have hg := (gaussWeight_3j (specAdm_int M σ N hN) (by exact_mod_cast hN0) hK hnK).1
  unfold lambdaSq3j at hg
  have hB0 : 0 ≤ B := le_trans (sq_nonneg _) (hB 0)
  have hterm : ∀ i ∈ Finset.range K, (2 * ((max |(M : ℚ)| |(σ : ℚ)| + i : ℚ) : ℝ) + 1) *
      PhiX (max |(M : ℚ)| |(σ : ℚ)| + i) (M : ℚ) (σ : ℚ) (N : ℚ) (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) ^ 2 ≤ B := by
    intro i _
    have hcast : (max |(M : ℚ)| |(σ : ℚ)| + (i : ℚ)) = ((L0 + (i : ℤ) : ℤ) : ℚ) := by
      have e : max |(M : ℚ)| |(σ : ℚ)| = (L0 : ℚ) := by rw [hL0]; push_cast; rfl
      rw [e]; push_cast; ring
    rw [hcast]
    have hk0 : (0 : ℝ) ≤ ((L0 + (i : ℤ) : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ L0 + (i : ℤ))
    have hY : (hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) (L0 + (i : ℤ))) ^ 2 =
        (2 * ((((L0 + (i : ℤ) : ℤ)) : ℚ) : ℝ) + 1) *
          PhiX (((L0 + (i : ℤ) : ℤ) : ℚ)) (M : ℚ) (σ : ℚ) (N : ℚ) (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) ^ 2 := by
      unfold hahn3jY
      rw [mul_pow, Real.sq_sqrt (by linarith)]
      push_cast; ring
    rw [← hY]
    exact hB _
  have hsum := Finset.sum_le_card_nsmul (Finset.range K) _ B hterm
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  have hKN : (K : ℝ) ≤ N := by
    have : (K : ℤ) ≤ N := by omega
    exact_mod_cast this
  calc (N : ℝ) = _ := hg.symm
    _ ≤ K * B := hsum
    _ ≤ N * B := mul_le_mul_of_nonneg_right hKN hB0

/-- The smallness thresholds, as one `ε₀`: every `h ≤ ε₀` has a cube root `δ ≤ δ₀` with `δ² ≤ ξ₀/(2 A_μ C_μ)`, and
`h ≤ r/8`, `(K₀+1) h ≤ q_* - r`, `2x(μ₀+1) h ≤ 3 q_*³`, `(μ₀+1) h ≤ x q_*²`, `(m₀+2) h ≤ q_*`. -/
lemma kf_small {x qs r δ0 Cmu Aμ ξ0 μ0 m0 : ℝ} (K0 : ℕ) (hx : 0 < x) (hqs : 0 < qs) (hr : 0 < r) (hδ0 : 0 < δ0)
    (hCmu : 0 < Cmu) (hAμ : 0 < Aμ) (hξ0 : 0 < ξ0) (hμ0 : 0 ≤ μ0) (hm0 : 0 ≤ m0) (hrq : r < qs) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ h : ℝ, 0 < h → h ≤ ε0 →
      (∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h ∧ δ ≤ δ0 ∧ δ ^ 2 ≤ ξ0 / (2 * Aμ * Cmu)) ∧ h ≤ r / 8 ∧
        ((K0 : ℝ) + 1) * h ≤ qs - r ∧ 2 * x * (μ0 + 1) * h ≤ 3 * qs ^ 3 ∧ (μ0 + 1) * h ≤ x * qs ^ 2 ∧
        (m0 + 2) * h ≤ qs := by
  set δ1 : ℝ := min δ0 (Real.sqrt (ξ0 / (2 * Aμ * Cmu))) with hδ1
  have hδ1p : 0 < δ1 := lt_min hδ0 (Real.sqrt_pos.2 (by positivity))
  have hK : (0 : ℝ) < (K0 : ℝ) + 1 := by positivity
  have hμ1 : 0 < μ0 + 1 := by linarith
  have hm2 : 0 < m0 + 2 := by linarith
  refine ⟨min (δ1 ^ 3) (min (r / 8) (min ((qs - r) / ((K0 : ℝ) + 1)) (min (3 * qs ^ 3 / (2 * x * (μ0 + 1)))
    (min (x * qs ^ 2 / (μ0 + 1)) (qs / (m0 + 2)))))), ?_, ?_⟩
  · refine lt_min (by positivity) (lt_min (by positivity) (lt_min (div_pos (by linarith) hK)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))))
  intro h hh hle
  obtain ⟨h0, h1⟩ := le_min_iff.1 hle
  obtain ⟨h2, h3⟩ := le_min_iff.1 h1
  obtain ⟨h4, h5⟩ := le_min_iff.1 h3
  obtain ⟨h6, h7⟩ := le_min_iff.1 h5
  obtain ⟨h8, h9⟩ := le_min_iff.1 h7
  refine ⟨⟨h ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos hh _, ?_, ?_, ?_⟩, h2, ?_, ?_, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]; norm_num
  · have hd3 : (h ^ ((1 : ℝ) / 3)) ^ 3 = h := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]; norm_num
    have : (h ^ ((1 : ℝ) / 3)) ^ 3 ≤ δ1 ^ 3 := by rw [hd3]; exact h0
    exact (le_of_pow_le_pow_left₀ (by norm_num) hδ1p.le this).trans (min_le_left _ _)
  · have hd3 : (h ^ ((1 : ℝ) / 3)) ^ 3 = h := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]; norm_num
    have : (h ^ ((1 : ℝ) / 3)) ^ 3 ≤ δ1 ^ 3 := by rw [hd3]; exact h0
    have h5 := (le_of_pow_le_pow_left₀ (by norm_num) hδ1p.le this).trans (min_le_right _ _)
    have h6 : (h ^ ((1 : ℝ) / 3)) ^ 2 ≤ Real.sqrt (ξ0 / (2 * Aμ * Cmu)) ^ 2 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hh.le _) h5 2
    rwa [Real.sq_sqrt (by positivity)] at h6
  · have := (le_div_iff₀ hK).1 h4; linarith
  · have := (le_div_iff₀ (by positivity : 0 < 2 * x * (μ0 + 1))).1 h6; linarith
  · have := (le_div_iff₀ hμ1).1 h8; linarith
  · have := (le_div_iff₀ hm2).1 h9; linarith

/-- Absorbing the `μ` term: if `|Y_k| ≤ A_κ|κ| + A_μ|μ|` on the window, `|μ| ≤ C_μ |Y_{m+1}| ε` and `A_μ C_μ ε ≤ 1/2`, then
`|Y_k| ≤ 2 A_κ |κ|` on the window. -/
lemma kf_absorb {Y : ℤ → ℝ} {J m : ℤ} {Aκ Aμ Cmu ε κ μ : ℝ} (hJm : J ≤ m) (hAμ : 0 ≤ Aμ)
    (hw : ∀ k ∈ Finset.Icc J (m + 1), |Y k| ≤ Aκ * |κ| + Aμ * |μ|) (hμ : |μ| ≤ Cmu * |Y (m + 1)| * ε)
    (hε : Aμ * Cmu * ε ≤ 1 / 2) : ∀ k ∈ Finset.Icc J (m + 1), |Y k| ≤ 2 * (Aκ * |κ|) := by
  have hm1 := hw (m + 1) (by rw [Finset.mem_Icc]; omega)
  have hY0 := abs_nonneg (Y (m + 1))
  have h1 : Aμ * |μ| ≤ Aμ * (Cmu * |Y (m + 1)| * ε) := mul_le_mul_of_nonneg_left hμ hAμ
  have h2 : Aμ * (Cmu * |Y (m + 1)| * ε) = (Aμ * Cmu * ε) * |Y (m + 1)| := by ring
  have h3 : (Aμ * Cmu * ε) * |Y (m + 1)| ≤ 1 / 2 * |Y (m + 1)| := mul_le_mul_of_nonneg_right hε hY0
  have h4 : |Y (m + 1)| ≤ 2 * (Aκ * |κ|) := by linarith
  intro k hk
  have := hw k hk
  linarith

/-- Assembly of the pointwise bound on all of `ℤ` from the three regions. -/
lemma kf_assemble {Y : ℤ → ℝ} {J m : ℤ} {Aκ κ Cl : ℝ} (hJm : J ≤ m) (hCl : 1 ≤ Cl)
    (hwin : ∀ k ∈ Finset.Icc J (m + 1), |Y k| ≤ 2 * (Aκ * |κ|))
    (hleft : ∀ k : ℤ, k ≤ J + 1 → Y k ^ 2 ≤ Cl * (Y (J + 1) ^ 2 + Y (J + 1 - 1) ^ 2))
    (hright : ∀ k : ℤ, m + 1 ≤ k → Y k ^ 2 ≤ Y (m + 1) ^ 2) :
    ∀ k : ℤ, Y k ^ 2 ≤ 8 * Cl * Aκ ^ 2 * κ ^ 2 := by
  have hB0 : 0 ≤ Aκ ^ 2 * κ ^ 2 := by positivity
  have hsq : ∀ k ∈ Finset.Icc J (m + 1), Y k ^ 2 ≤ 4 * (Aκ ^ 2 * κ ^ 2) := by
    intro k hk
    have h1 := hwin k hk
    have h2 : Y k ^ 2 ≤ (2 * (Aκ * |κ|)) ^ 2 := by
      rw [← sq_abs (Y k)]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : (2 * (Aκ * |κ|)) ^ 2 = 4 * (Aκ ^ 2 * κ ^ 2) := by rw [mul_pow, mul_pow, sq_abs]; ring
    linarith
  intro k
  have e8 : 8 * Cl * Aκ ^ 2 * κ ^ 2 = 8 * Cl * (Aκ ^ 2 * κ ^ 2) := by ring
  rw [e8]
  by_cases hk1 : k ≤ J + 1
  · have h1 := hleft k hk1
    have h2 := hsq (J + 1) (by rw [Finset.mem_Icc]; omega)
    have h3 := hsq J (by rw [Finset.mem_Icc]; omega)
    rw [show J + 1 - 1 = J by ring] at h1
    nlinarith
  · push Not at hk1
    by_cases hk2 : k ≤ m + 1
    · have h2 := hsq k (by rw [Finset.mem_Icc]; omega)
      nlinarith
    · push Not at hk2
      have h1 := hright k (by omega)
      have h2 := hsq (m + 1) (by rw [Finset.mem_Icc]; omega)
      nlinarith

/-- **The window bound near the turn** (abstract form): from the pointwise Airy comparison, `g ≤ g_max`, `X_k ≤ 1/4` on `[J, m+1]` and
`|μ| ≤ C_μ |Y_{m+1}| ε` with `A_μ C_μ ε ≤ 1/2`: `|Y_k| ≤ 2 A_κ |κ|` for `J ≤ k ≤ m+1`. -/
lemma kf_window_abs {Y g X : ℤ → ℝ} {J m Nw : ℤ} {κ μ C δ3 gmax Aκ Aμ Cmu ε : ℝ} (hJm : J ≤ m) (hm1 : m + 1 ≤ Nw)
    (hC : 0 ≤ C) (hδ31 : δ3 ≤ 1) (hAκ : Aκ = 3 * gmax + C) (hAμ : Aμ = 3600 * gmax + 8 * C)
    (hg : ∀ k ∈ Finset.Icc J (Nw + 1), |g k| ≤ gmax) (hX : ∀ k ∈ Finset.Icc J (m + 1), X k ≤ 1 / 4)
    (hpt : ∀ k ∈ Finset.Icc J (Nw + 1), |Y k - (κ * daoPhi g X k + μ * daoPsi g X k)| ≤
      C * δ3 * (|κ| * airyWt (X k) + |μ| * airyBiWt (X k)))
    (hμ : |μ| ≤ Cmu * |Y (m + 1)| * ε) (hε : Aμ * Cmu * ε ≤ 1 / 2) :
    ∀ k ∈ Finset.Icc J (m + 1), |Y k| ≤ 2 * (Aκ * |κ|) := by
  have hgmax0 : 0 ≤ gmax := by
    have := hg J (by rw [Finset.mem_Icc]; omega)
    exact (abs_nonneg _).trans this
  have hAμ0 : 0 ≤ Aμ := by rw [hAμ]; positivity
  have hw : ∀ k ∈ Finset.Icc J (m + 1), |Y k| ≤ Aκ * |κ| + Aμ * |μ| := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk' : k ∈ Finset.Icc J (Nw + 1) := by rw [Finset.mem_Icc]; omega
    have := kf_window_site (Y := Y k) (g := g k) (X := X k) (κ := κ) (μ := μ) (C := C) (δ3 := δ3) (gmax := gmax) hC hδ31
      (hg k hk') (by have := hX k (by rw [Finset.mem_Icc]; omega); linarith) (by simpa [daoPhi, daoPsi] using hpt k hk')
    rw [hAκ, hAμ]
    exact this
  exact kf_absorb hJm hAμ0 hw hμ hε

/-- `e^{-ξ₀/δ³}/δ ≤ δ²/ξ₀`. -/
lemma kf_exp_le {δ ξ0 : ℝ} (hδ : 0 < δ) (hξ : 0 < ξ0) : Real.exp (-ξ0 / δ ^ 3) / δ ≤ δ ^ 2 / ξ0 := by
  have ht : 0 < ξ0 / δ ^ 3 := by positivity
  have h1 : ξ0 / δ ^ 3 ≤ Real.exp (ξ0 / δ ^ 3) := by linarith [Real.add_one_le_exp (ξ0 / δ ^ 3)]
  have h2 : Real.exp (-ξ0 / δ ^ 3) = (Real.exp (ξ0 / δ ^ 3))⁻¹ := by rw [neg_div, Real.exp_neg]
  have h3 : (Real.exp (ξ0 / δ ^ 3))⁻¹ ≤ (ξ0 / δ ^ 3)⁻¹ := inv_anti₀ ht h1
  have h4 : (ξ0 / δ ^ 3)⁻¹ = δ ^ 3 / ξ0 := by rw [inv_div]
  rw [h2, div_le_iff₀ hδ]
  have : δ ^ 2 / ξ0 * δ = δ ^ 3 / ξ0 := by ring
  rw [this, ← h4]; exact h3

lemma kf_idx_lt {q r h : ℝ} {m Nw : ℤ} (hh : 0 < h) (hhr : h ≤ r / 8)
    (h4 : ((m : ℝ) + 1 / 2) * h < q + h) (h5 : q + r / 4 ≤ ((Nw : ℝ) + 1 / 2) * h) : m + 1 ≤ Nw := by
  by_contra hcon
  push Not at hcon
  have h1 : (Nw : ℝ) ≤ m := by exact_mod_cast (by omega : Nw ≤ m)
  have h2 : ((Nw : ℝ) + 1 / 2) * h ≤ ((m : ℝ) + 1 / 2) * h := mul_le_mul_of_nonneg_right (by linarith) hh.le
  linarith

lemma kf_hh2 {μ0 x qs h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hμ0 : 0 ≤ μ0) (h5 : (μ0 + 1) * h ≤ x * qs ^ 2) :
    (μ0 + 1) * h ^ 2 ≤ x * qs ^ 2 := by
  have : h ^ 2 ≤ h := by nlinarith
  have h2 : (μ0 + 1) * h ^ 2 ≤ (μ0 + 1) * h := mul_le_mul_of_nonneg_left this (by linarith)
  linarith

lemma kf_eps_half {δ ξ0 Aμ Cmu : ℝ} (hδ : 0 < δ) (hξ : 0 < ξ0) (hA : 0 < Aμ) (hC : 0 < Cmu)
    (hsq : δ ^ 2 ≤ ξ0 / (2 * Aμ * Cmu)) : Aμ * Cmu * (Real.exp (-ξ0 / δ ^ 3) / δ) ≤ 1 / 2 := by
  have h1' := kf_exp_le hδ hξ
  have h3 : δ ^ 2 / ξ0 ≤ 1 / (2 * Aμ * Cmu) := by
    rw [div_le_iff₀ hξ]
    have h4 : δ ^ 2 * (2 * Aμ * Cmu) ≤ ξ0 := (le_div_iff₀ (by positivity)).1 hsq
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    linarith
  have h2' : Aμ * Cmu * (δ ^ 2 / ξ0) ≤ 1 / 2 := by
    calc Aμ * Cmu * (δ ^ 2 / ξ0) ≤ Aμ * Cmu * (1 / (2 * Aμ * Cmu)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 1 / 2 := by field_simp
  exact (mul_le_mul_of_nonneg_left h1' (by positivity)).trans h2'

lemma kf_mu_bound {μ Cmu Ys δ ξ0 ξX : ℝ} (hδ : 0 < δ) (hC : 0 ≤ Cmu) (hY : 0 ≤ Ys)
    (hμ : |μ| ≤ Cmu * Ys * Real.exp (-ξX) / δ) (hxi : ξ0 / δ ^ 3 ≤ ξX) :
    |μ| ≤ Cmu * Ys * (Real.exp (-ξ0 / δ ^ 3) / δ) := by
  have hexp : Real.exp (-ξX) ≤ Real.exp (-ξ0 / δ ^ 3) := by
    apply Real.exp_le_exp.2
    rw [neg_div]
    exact neg_le_neg hxi
  refine hμ.trans ?_
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hδ.le
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **The left bound for the actual chain** (instance of `kl_hahn_left` with `k₁ = J + 1`, `h = 1/N`, `e² = 1 - (q_* - r/2)²`). -/
lemma kf_left {M σ N J : ℤ} {x : ℚ} {qs r e : ℝ} {K0 : ℕ} (hN0 : 0 < N) (hx0 : 0 < (x : ℝ)) (hxe : (x : ℝ) < e)
    (he1 : e ≤ 1) (he2 : e ^ 2 = 1 - (qs - r / 2) ^ 2) (hqr : 0 < qs - r / 2)
    (hK0 : kl_K0real (M : ℝ) (σ : ℝ) (x : ℝ) e ≤ (K0 : ℝ)) (hK3 : ((K0 : ℝ) + 1) * (1 / (N : ℝ)) ≤ qs - r)
    (hh8 : 1 / (N : ℝ) ≤ r / 8) (h1 : qs - r ≤ ((J : ℝ) + 1 / 2) * (1 / (N : ℝ)))
    (h2 : ((J : ℝ) + 1 / 2) * (1 / (N : ℝ)) < qs - r + 1 / (N : ℝ)) :
    ∀ k : ℤ, k ≤ J + 1 → hahn3jY M σ N x k ^ 2 ≤
      ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 * (hahn3jY M σ N x (J + 1) ^ 2 + hahn3jY M σ N x (J + 1 - 1) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  set h : ℝ := 1 / (N : ℝ) with hh
  have hh0 : 0 < h := by positivity
  have hk1 : (K0 : ℤ) ≤ J + 1 := by
    have h3 : ((K0 : ℝ) + 1) * h ≤ ((J : ℝ) + 1 / 2) * h := hK3.trans h1
    have h4 : (K0 : ℝ) + 1 ≤ (J : ℝ) + 1 / 2 := le_of_mul_le_mul_right h3 hh0
    have h5 : (K0 : ℝ) < J := by linarith
    have h6 : (K0 : ℤ) < J := by exact_mod_cast h5
    omega
  have hband : ((((J + 1 : ℤ) : ℝ) + 1) * h) ^ 2 ≤ 1 - e ^ 2 := by
    rw [he2]
    have h3 : (((J + 1 : ℤ) : ℝ) + 1) * h ≤ qs - r / 2 := by
      have : (((J + 1 : ℤ) : ℝ) + 1) * h = ((J : ℝ) + 1 / 2) * h + 3 / 2 * h := by push_cast; ring
      rw [this]; linarith
    have h4 : 0 ≤ (((J + 1 : ℤ) : ℝ) + 1) * h := by
      have : 0 ≤ ((J : ℝ) + 1 / 2) := by
        by_contra hcon; push Not at hcon
        nlinarith [mul_nonneg (neg_nonneg.2 hcon.le) hh0.le]
      push_cast
      nlinarith
    nlinarith
  refine kl_hahn_left (M := M) (σ := σ) (x := (x : ℝ)) (e := e) (h := h) hx0 hxe he1 hh0 (Y := hahn3jY M σ N x)
    (K0 := K0) hK0 (k1 := J + 1) hk1 hband ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1' : 1 ≤ k := by have := le_max_left |M| |σ|; have := abs_nonneg M; omega
    have := hahn_class_chain M σ N x hN0 k hk1'
    rw [kl_hrAk_eq, kl_hrCk_eq] at this
    exact this
  · intro k hk
    apply hahn_chain_support
    intro ⟨h1, h2, _⟩
    exact absurd (max_le h1 h2) (not_le.2 hk)

lemma kf_kappa_ge {Aκ Cl κ : ℝ} (hA : 0 < Aκ) (hC : 0 < 8 * Cl) (h : 1 ≤ 8 * Cl * Aκ ^ 2 * κ ^ 2) :
    1 / (Aκ * Real.sqrt (8 * Cl)) ≤ |κ| := by
  have hs : 0 < Real.sqrt (8 * Cl) := Real.sqrt_pos.2 hC
  have hsq : Real.sqrt (8 * Cl) ^ 2 = 8 * Cl := Real.sq_sqrt hC.le
  have h1 : 1 ≤ (Aκ * Real.sqrt (8 * Cl) * |κ|) ^ 2 := by
    have : (Aκ * Real.sqrt (8 * Cl) * |κ|) ^ 2 = 8 * Cl * Aκ ^ 2 * κ ^ 2 := by
      rw [mul_pow, mul_pow, hsq, sq_abs]; ring
    linarith
  have h2 : 1 ≤ Aκ * Real.sqrt (8 * Cl) * |κ| := by
    by_contra hcon
    push Not at hcon
    have h3 : 0 ≤ Aκ * Real.sqrt (8 * Cl) * |κ| := by positivity
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **`κ ≠ 0` for the actual `3j` chain at a lattice node** (see the module docstring).  `q_* = √(1 - x²)`; the conclusion is
that of `hahn_chain_airy_full` (positions, `DaiFull`, `Ŷ = κ g Ai + μ g Bi` up to `C δ³(|κ| airyWt + |μ| airyBiWt)` on
`[J, N_w + 1]`, `|μ| ≤ C_μ √N e^{-ξ₀ N}/δ`) together with the **lower bound `|κ| ≥ κ_min > 0`**, `κ_min` independent of `N`. -/
theorem hahn_chain_kappa (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ (r ε0 C Cmu ξ0 κmin : ℝ), 0 < r ∧ 0 < ε0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < κmin ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N → (n : ℤ) < N - max |M| |σ| →
        xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x → 1 / (N : ℝ) ≤ ε0 →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = 1 / (N : ℝ) ∧ ∃ J m Nw : ℤ, 1 ≤ J ∧ J < Nw ∧ J ≤ m ∧ m < Nw ∧
          (∀ k ∈ Finset.Icc J (Nw + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - Real.sqrt (1 - (x : ℝ) ^ 2)| ≤ r) ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) - r ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((J : ℝ) + 1 / 2) * δ ^ 3 < Real.sqrt (1 - (x : ℝ) ^ 2) - r + δ ^ 3 ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((m : ℝ) + 1 / 2) * δ ^ 3 < Real.sqrt (1 - (x : ℝ) ^ 2) + δ ^ 3 ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) + r / 4 ≤ ((Nw : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((Nw : ℝ) + 1 + 1 / 2) * δ ^ 3 ≤ Real.sqrt (1 - (x : ℝ) ^ 2) + r / 2 ∧
          DaiFull (hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) (δ ^ 3))
            (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ)
            (fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2)) (dalQ (δ ^ 3 / 2) δ k))
            J m Nw δ C Cmu ξ0 ∧
          ∃ κ μ : ℝ, κmin ≤ |κ| ∧ |μ| ≤ Cmu * Real.sqrt (N : ℝ) * Real.exp (-ξ0 / δ ^ 3) / δ ∧
            ∀ k ∈ Finset.Icc J (Nw + 1),
              |hahn3jY M σ N x k -
                  (κ * daoPhi (fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2))
                      (dalQ (δ ^ 3 / 2) δ k))
                    (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ) k +
                   μ * daoPsi (fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2))
                      (dalQ (δ ^ 3 / 2) δ k))
                    (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ) k)| ≤
                C * δ ^ 3 * (|κ| * airyWt (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k) +
                  |μ| * airyBiWt (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k)) := by
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hx1' : (x : ℝ) < 1 := by exact_mod_cast hx1
  have hq2 : Real.sqrt (1 - (x : ℝ) ^ 2) ^ 2 = 1 - (x : ℝ) ^ 2 := Real.sq_sqrt (by nlinarith)
  have hqs : 0 < Real.sqrt (1 - (x : ℝ) ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hturn : Phi 1 0 1 (x : ℝ) (Real.sqrt (1 - (x : ℝ) ^ 2) ^ 2) = 0 := by
    unfold Phi etilde
    rw [hq2]
    have : (1 - 1 * (1 - (x : ℝ) ^ 2)) * (1 - 0 * (1 - (x : ℝ) ^ 2)) = (x : ℝ) ^ 2 := by ring
    rw [this, Real.sqrt_sq hx0'.le]
    simp
  obtain ⟨r, δ0, C, Cmu, ξ0, gmax, hr, hrq, hδ0, -, hC, hCmu, hξ0, hgmax, H⟩ :=
    kc_hahn_full (P := 1) (Q := 0) (by norm_num) (by norm_num) (M : ℝ) (σ : ℝ) 1 (x : ℝ)
      (Real.sqrt (1 - (x : ℝ) ^ 2)) hqs (by norm_num) (by linarith) (by rw [hq2]; nlinarith) (by simp) hturn
  set qs := Real.sqrt (1 - (x : ℝ) ^ 2) with hqsdef
  have hq1 : qs < 1 := by nlinarith
  have hqr : 0 < qs - r / 2 := by linarith
  set e : ℝ := Real.sqrt (1 - (qs - r / 2) ^ 2) with hedef
  have he2 : e ^ 2 = 1 - (qs - r / 2) ^ 2 := Real.sq_sqrt (by nlinarith)
  have hxe : (x : ℝ) < e := by
    by_contra hcon
    push Not at hcon
    have h1 : e ^ 2 ≤ (x : ℝ) ^ 2 := by nlinarith [Real.sqrt_nonneg (1 - (qs - r / 2) ^ 2)]
    nlinarith
  have he1 : e ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
  set K0 : ℕ := ⌈kl_K0real (M : ℝ) (σ : ℝ) (x : ℝ) e⌉₊ with hK0def
  have hK0 : kl_K0real (M : ℝ) (σ : ℝ) (x : ℝ) e ≤ (K0 : ℝ) := Nat.le_ceil _
  set Cl : ℝ := ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 with hCldef
  have hCl : 1 ≤ Cl := ke_C_ge_one K0 hx0' hxe he1
  set Aκ : ℝ := 3 * gmax + C with hAκ
  set Aμ : ℝ := 3600 * gmax + 8 * C with hAμ
  have hAκ0 : 0 < Aκ := by positivity
  have hAμ0 : 0 < Aμ := by positivity
  obtain ⟨ε0, hε0, Hε⟩ := kf_small (x := (x : ℝ)) (qs := qs) (r := r) (δ0 := δ0) (Cmu := Cmu) (Aμ := Aμ)
    (ξ0 := ξ0) (μ0 := |(M : ℝ) * σ|) (m0 := |(M : ℝ)| + |(σ : ℝ)|) K0 hx0' hqs hr hδ0 hCmu hAμ0 hξ0
    (abs_nonneg _) (by positivity) (by linarith)
  have h8Cl : 0 < 8 * Cl := by linarith
  refine ⟨r, ε0, C, Cmu, ξ0, 1 / (Aκ * Real.sqrt (8 * Cl)), hr, hε0, hC, hCmu, hξ0, by positivity, ?_⟩
  intro N n hN hn hxn hNε
  have hN0 : (0 : ℤ) < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hh0 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  obtain ⟨⟨δ, hδp, hδ3, hδle, hδsq⟩, hhr, hK3, hc4, hc5, hc6⟩ := Hε _ hh0 hNε
  obtain ⟨J, m, Nw, hJ, hJN, hJm, hmN, hwin, h1, h2, h3, h4, h5, h6, hg, hXm, Hc⟩ := H δ hδp hδle
  have hhle : δ ^ 3 ≤ r / 8 := by rw [hδ3]; exact hhr
  have hδ31 : δ ^ 3 ≤ 1 := by linarith
  have hm1 : m + 1 ≤ Nw := kf_idx_lt (pow_pos hδp 3) hhle h4 h5
  -- the chain
  have hrows' : ∀ k ∈ Finset.Icc (J + 1) Nw,
      jac (hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) (δ ^ 3)) (hahn3jY M σ N x) k = 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [hδ3]
    exact hahn_class_chain M σ N x hN0 k (by omega)
  have hmono := kr_chain_mono M σ N m x hN0 hx0' hq2 hqs (by rw [← hδ3]; exact h3) hc4
    (kf_hh2 hh0 (by linarith) (abs_nonneg _) hc5) hc6
  have hYN : |hahn3jY M σ N x Nw| ≤ |hahn3jY M σ N x (m + 1)| := sq_le_sq.1 (hmono Nw hm1)
  have hYN1 : |hahn3jY M σ N x (Nw + 1)| ≤ |hahn3jY M σ N x (m + 1)| := sq_le_sq.1 (hmono (Nw + 1) (by omega))
  obtain ⟨κ, μ, hμ, hpt⟩ := Hc.pointwise (hahn3jY M σ N x) _ hrows' hYN hYN1
  have hμ' := kf_mu_bound hδp hCmu.le (abs_nonneg _) hμ Hc.1
  have hε := kf_eps_half hδp hξ0 hAμ0 hCmu hδsq
  have hwin2 := kf_window_abs (Y := hahn3jY M σ N x) (hJm) hm1 hC.le hδ31 hAκ hAμ hg hXm hpt hμ' hε
  have hleft := kf_left (M := M) (σ := σ) (N := N) (J := J) (x := x) (qs := qs) (r := r) (e := e) (K0 := K0) hN0 hx0'
    hxe he1 he2 hqr hK0 hK3 hhr (by rw [← hδ3]; exact h1) (by rw [← hδ3]; exact h2)
  have hall := kf_assemble (Y := hahn3jY M σ N x) (Aκ := Aκ) (κ := κ) (Cl := Cl) hJm hCl hwin2 hleft
    (fun k hk => hmono k hk)
  have hmass := kf_mass_le M σ N hN n hn (B := 8 * Cl * Aκ ^ 2 * κ ^ 2) (by rw [hxn]; exact hall)
  have hB1 : 1 ≤ 8 * Cl * Aκ ^ 2 * κ ^ 2 := by
    by_contra hcon
    push Not at hcon
    have : (N : ℝ) * (8 * Cl * Aκ ^ 2 * κ ^ 2) < N * 1 := mul_lt_mul_of_pos_left hcon hNr
    linarith
  have hYs : |hahn3jY M σ N x (m + 1)| ≤ Real.sqrt (N : ℝ) := by
    have := hahn_chain_abs_le M σ N hN n hn (m + 1)
    rwa [hxn] at this
  have hμ2 : |μ| ≤ Cmu * Real.sqrt (N : ℝ) * Real.exp (-ξ0 / δ ^ 3) / δ := by
    refine hμ'.trans ?_
    have h0 : 0 ≤ Real.exp (-ξ0 / δ ^ 3) / δ := by positivity
    calc Cmu * |hahn3jY M σ N x (m + 1)| * (Real.exp (-ξ0 / δ ^ 3) / δ)
        ≤ Cmu * Real.sqrt (N : ℝ) * (Real.exp (-ξ0 / δ ^ 3) / δ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYs hCmu.le) h0
      _ = _ := by ring
  exact ⟨δ, hδp, hδ3, J, m, Nw, hJ, hJN, hJm, hm1, hwin, h1, h2, h3, h4, h5, h6, Hc, κ, μ,
    kf_kappa_ge hAκ0 h8Cl hB1, hμ2, hpt⟩

/-- info: 'FormalResearch.Special.hahn_chain_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_kappa

end FormalResearch.Special
