module

public import FormalResearch.Special.AiryZeroSpacing

/-!
# Tail estimate for the window weights from abstract node data (`virasoro_two_level.tex`, Proposition 2.3 `gt:2.3`)

For a decreasing family of Airy zeros `p k = |a_k|` and Clark nodes `q k = |z_k|` interlacing as
`p (k-1) < q k < p k`, with the cube-root spacing `p_k ≍ k^{2/3}`, `p_k - p_{k-1} ≍ k^{-1/3}` and the node fraction
in `[9/20, 11/20]` from `k0` on (`NodeHyp`), the quantity

`absTerm p q K n = (q_n - p_2)^{-3} (∏_{k=3}^K (q_n - q_k)/(q_n - p_k))² (∏_{k=3}^K (q_k - q_2)/(p_k - q_2))^{-2}`

satisfies `absTerm K (K+1+i) ≤ C K^{-1/15} (i+1)^{-6/5}` (`NodeHyp.term_bound`), a summable majorant that tends to
`0` with `K`.  The exponents are not sharp (the paper's rate is `K^{-1/3} log K`); only the decay is used.
-/

@[expose] public section

open Finset

namespace FormalResearch.ModularBootstrap.TwoLevel

lemma prod_Ioc_telescope (x : ℕ → ℝ) (m : ℕ) (K : ℕ) (hx : ∀ k, m ≤ k → k ≤ K → x k ≠ 0) :
    m ≤ K → ∏ k ∈ Finset.Ioc m K, x (k - 1) / x k = x m / x K := by
  intro hK
  induction K, hK using Nat.le_induction with
  | base => simp [hx m le_rfl le_rfl]
  | succ K hK ih =>
    rw [Finset.prod_Ioc_succ_top (by omega), ih (fun k h1 h2 => hx k h1 (by omega))]
    have h1 := hx K hK (by omega)
    have h2 := hx (K + 1) (by omega) le_rfl
    simp only [Nat.add_sub_cancel]
    field_simp

lemma bern01 (r s : ℝ) (hr : 0 < r) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : r ^ s ≤ 1 + s * (r - 1) := by
  have := rpow_one_add_le_one_add_mul_self (s := r - 1) (by linarith) hs0 hs1
  simpa using this

lemma bern_ge (x : ℝ) (hx : 0 ≤ x) : 1 + (6/5 : ℝ) * x ≤ (1 + x) ^ (6/5 : ℝ) := by
  have := one_add_mul_self_le_rpow_one_add (s := x) (by linarith) (p := 6/5) (by norm_num)
  simpa using this

lemma cube_core (κ t g u : ℝ) (hκ : 2 ≤ κ) (ht : 8 ≤ t) (hu : 0 < u)
    (h1 : κ * g ^ 3 ≤ 8.4) (h2 : 5.8 * (t - 1) ^ 3 ≤ (κ + t) * u ^ 3) : g ≤ 3 / 10 * u := by
  by_contra hcon
  push Not at hcon
  have hcube : 0.027 * u ^ 3 < g ^ 3 := by
    have := pow_lt_pow_left₀ hcon (by positivity) (by norm_num : (3 : ℕ) ≠ 0)
    nlinarith
  have hs : 0 ≤ t - 8 := by linarith
  have h8 : 8.4 + 4.2 * t ≤ 0.027 * (5.8 * (t - 1) ^ 3) := by
    have hs7 : 0 ≤ (t - 1) * ((t - 1) - 7) * ((t - 1) + 7) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith
  have key : 8.4 * (κ + t) ≤ 0.027 * (5.8 * (t - 1) ^ 3) * κ := by
    have : 8.4 * (κ + t) ≤ (8.4 + 4.2 * t) * κ := by nlinarith
    exact this.trans (by nlinarith)
  have hκt : 0 < κ + t := by linarith
  have A1 : κ * (κ + t) * (0.027 * u ^ 3) < κ * (κ + t) * g ^ 3 :=
    mul_lt_mul_of_pos_left hcube (by positivity)
  have A2 : κ * (κ + t) * g ^ 3 ≤ (κ + t) * 8.4 := by
    have := mul_le_mul_of_nonneg_left h1 hκt.le
    nlinarith
  have A3 : 0.027 * (5.8 * (t - 1) ^ 3) * κ ≤ κ * (κ + t) * (0.027 * u ^ 3) := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 0.027 * κ)
    nlinarith
  linarith

lemma rpow_combine (Kr nr m A B D : ℝ) (hK : 1 ≤ Kr) (hn : Kr ≤ nr) (hm : 1 ≤ m) (hA : 0 < A)
    (hAu : A ≤ 3 * Kr ^ (2 / 3 : ℝ)) (hB : nr ^ (2 / 3 : ℝ) ≤ B)
    (hD : 0.7 * m * nr ^ (-(1 / 3) : ℝ) ≤ D) :
    A ^ (11 / 10 : ℝ) * B ^ (6 / 5 - 3 : ℝ) * D ^ (-(6 / 5) : ℝ) ≤
      (3 ^ (11 / 10 : ℝ) * 0.7 ^ (-(6 / 5) : ℝ)) * Kr ^ (-(1 / 15) : ℝ) * m ^ (-(6 / 5) : ℝ) := by
  have hK0 : 0 < Kr := by linarith
  have hn0 : 0 < nr := by linarith
  have hm0 : 0 < m := by linarith
  have hnp : 0 < nr ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hnm : 0 < 0.7 * m * nr ^ (-(1 / 3) : ℝ) := by positivity
  have hD0 : 0 < D := lt_of_lt_of_le hnm hD
  -- pieces
  have h1 : A ^ (11 / 10 : ℝ) ≤ 3 ^ (11 / 10 : ℝ) * Kr ^ (11 / 15 : ℝ) := by
    calc A ^ (11 / 10 : ℝ) ≤ (3 * Kr ^ (2 / 3 : ℝ)) ^ (11 / 10 : ℝ) :=
          Real.rpow_le_rpow hA.le hAu (by norm_num)
      _ = 3 ^ (11 / 10 : ℝ) * Kr ^ (11 / 15 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hK0.le _), ← Real.rpow_mul hK0.le]
          norm_num
  have h2 : B ^ (6 / 5 - 3 : ℝ) ≤ nr ^ (-(6 / 5) : ℝ) := by
    calc B ^ (6 / 5 - 3 : ℝ) ≤ (nr ^ (2 / 3 : ℝ)) ^ (6 / 5 - 3 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hnp hB (by norm_num)
      _ = nr ^ (-(6 / 5) : ℝ) := by
          rw [← Real.rpow_mul hn0.le]; norm_num
  have h3 : D ^ (-(6 / 5) : ℝ) ≤ 0.7 ^ (-(6 / 5) : ℝ) * m ^ (-(6 / 5) : ℝ) * nr ^ (2 / 5 : ℝ) := by
    calc D ^ (-(6 / 5) : ℝ) ≤ (0.7 * m * nr ^ (-(1 / 3) : ℝ)) ^ (-(6 / 5) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hnm hD (by norm_num)
      _ = 0.7 ^ (-(6 / 5) : ℝ) * m ^ (-(6 / 5) : ℝ) * nr ^ (2 / 5 : ℝ) := by
          rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hn0.le _),
            Real.mul_rpow (by norm_num) hm0.le, ← Real.rpow_mul hn0.le]
          norm_num
  have h4 : nr ^ (-(6 / 5) : ℝ) * nr ^ (2 / 5 : ℝ) ≤ Kr ^ (-(4 / 5) : ℝ) := by
    rw [← Real.rpow_add hn0]
    norm_num
    exact Real.rpow_le_rpow_of_nonpos hK0 hn (by norm_num)
  have hKe : Kr ^ (11 / 15 : ℝ) * Kr ^ (-(4 / 5) : ℝ) = Kr ^ (-(1 / 15) : ℝ) := by
    rw [← Real.rpow_add hK0]; norm_num
  have hpos1 : 0 ≤ nr ^ (-(6 / 5) : ℝ) := Real.rpow_nonneg hn0.le _
  have hpos2 : 0 ≤ 0.7 ^ (-(6 / 5) : ℝ) * m ^ (-(6 / 5) : ℝ) * nr ^ (2 / 5 : ℝ) := by positivity
  calc A ^ (11 / 10 : ℝ) * B ^ (6 / 5 - 3 : ℝ) * D ^ (-(6 / 5) : ℝ)
      ≤ (3 ^ (11 / 10 : ℝ) * Kr ^ (11 / 15 : ℝ)) * nr ^ (-(6 / 5) : ℝ) *
          (0.7 ^ (-(6 / 5) : ℝ) * m ^ (-(6 / 5) : ℝ) * nr ^ (2 / 5 : ℝ)) :=
        mul_le_mul (mul_le_mul h1 h2 (Real.rpow_nonneg (hnp.trans_le hB).le _) (by positivity)) h3
          (Real.rpow_nonneg hD0.le _) (by positivity)
    _ = (3 ^ (11 / 10 : ℝ) * 0.7 ^ (-(6 / 5) : ℝ)) * m ^ (-(6 / 5) : ℝ) *
          (Kr ^ (11 / 15 : ℝ) * (nr ^ (-(6 / 5) : ℝ) * nr ^ (2 / 5 : ℝ))) := by ring
    _ ≤ (3 ^ (11 / 10 : ℝ) * 0.7 ^ (-(6 / 5) : ℝ)) * m ^ (-(6 / 5) : ℝ) *
          (Kr ^ (11 / 15 : ℝ) * Kr ^ (-(4 / 5) : ℝ)) := by
        gcongr
    _ = _ := by rw [hKe]; ring


structure NodeHyp (p q : ℕ → ℝ) (k0 : ℕ) : Prop where
  k0_ge : 3 ≤ k0
  pos : ∀ k : ℕ, 1 ≤ k → 0 < p k
  mono : ∀ k : ℕ, 1 ≤ k → p k < p (k + 1)
  int_lo : ∀ k : ℕ, 2 ≤ k → p (k - 1) < q k
  int_hi : ∀ k : ℕ, 2 ≤ k → q k < p k
  gap_up : ∀ k : ℕ, 3 ≤ k → ((k : ℝ) - 1) * (p k - p (k - 1)) ^ 3 ≤ 8.4
  gap_lo : ∀ j n : ℕ, 2 ≤ j → j < n → 5.8 * ((n : ℝ) - j) ^ 3 ≤ n * (p n - p j) ^ 3
  cube_lo : ∀ k : ℕ, 2 ≤ k → 16 * (k : ℝ) ^ 2 ≤ p k ^ 3
  cube_hi : ∀ k : ℕ, 2 ≤ k → p k ^ 3 ≤ 23 * (k : ℝ) ^ 2
  frac : ∀ k : ℕ, k0 ≤ k → 9 / 20 * (p k - p (k - 1)) ≤ q k - p (k - 1) ∧
    q k - p (k - 1) ≤ 11 / 20 * (p k - p (k - 1))

/-- The constant bounding a single factor `((q_n - q_k)/(q_n - p_k))²` for every `n > k`. -/
noncomputable def Bk (p q : ℕ → ℝ) (k : ℕ) : ℝ := (1 + (p k - p (k - 1)) / (q (k + 1) - p k)) ^ 2

/-- The abstract tail term (see `WindowOptimum` for its origin): `(q_n - p_2)^{-3} U² V^{-2}`. -/
noncomputable def absTerm (p q : ℕ → ℝ) (K n : ℕ) : ℝ :=
  ((q n - p 2) ^ 3)⁻¹ * (∏ k ∈ Finset.Ioc 2 K, (q n - q k) / (q n - p k)) ^ 2 *
    ((∏ k ∈ Finset.Ioc 2 K, (q k - q 2) / (p k - q 2))⁻¹) ^ 2

namespace NodeHyp
variable {p q : ℕ → ℝ} {k0 : ℕ} (h : NodeHyp p q k0)
include h

lemma mono' {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) : p j ≤ p k := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact ih.trans (h.mono k (by omega)).le

lemma mono_lt {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k) : p j < p k := by
  have := h.mono' (by omega : 1 ≤ j + 1) (show j + 1 ≤ k by omega)
  exact (h.mono j hj).trans_le this

lemma q_gt_p {k n : ℕ} (hk : 1 ≤ k) (hkn : k < n) : p k < q n := by
  have := h.int_lo n (by omega)
  have h2 : p k ≤ p (n - 1) := h.mono' hk (by omega)
  linarith


lemma pk_sub_q2_pos {k : ℕ} (hk : 2 ≤ k) : 0 < p k - q 2 := by
  have h1 := h.int_hi 2 le_rfl
  have h2 : p 2 ≤ p k := h.mono' (by omega) hk
  linarith

lemma pk1_sub_q2_pos {k : ℕ} (hk : 3 ≤ k) : 0 < p (k - 1) - q 2 :=
  h.pk_sub_q2_pos (by omega)

/-- `(q_k - q_2)/(p_k - q_2) ≥ r_k^s`, `r_k = (p_{k-1}-q_2)/(p_k-q_2)`, `s = 11/20`. -/
lemma V_factor {k : ℕ} (hk : k0 ≤ k) :
    ((p (k - 1) - q 2) / (p k - q 2)) ^ (11 / 20 : ℝ) ≤ (q k - q 2) / (p k - q 2) := by
  have hk3 : 3 ≤ k := h.k0_ge.trans hk
  have hd := h.pk_sub_q2_pos (by omega : 2 ≤ k)
  have hr : 0 < (p (k - 1) - q 2) / (p k - q 2) := div_pos (h.pk1_sub_q2_pos hk3) hd
  have hb := bern01 _ (11 / 20) hr (by norm_num) (by norm_num)
  refine hb.trans ?_
  obtain ⟨hf1, -⟩ := h.frac k hk
  rw [le_div_iff₀ hd]
  have e : (1 + 11 / 20 * ((p (k - 1) - q 2) / (p k - q 2) - 1)) * (p k - q 2) =
      (p k - q 2) - 11 / 20 * (p k - p (k - 1)) := by
    field_simp; ring
  rw [e]
  linarith

lemma V_bound {K : ℕ} (hK : k0 ≤ K) :
    (∏ k ∈ Finset.Ioc 2 (k0 - 1), (q k - q 2) / (p k - q 2)) *
        ((p (k0 - 1) - q 2) / (p K - q 2)) ^ (11 / 20 : ℝ) ≤
      ∏ k ∈ Finset.Ioc 2 K, (q k - q 2) / (p k - q 2) := by
  have h3 := h.k0_ge
  rw [← Finset.prod_Ioc_consecutive _ (show 2 ≤ k0 - 1 by omega) (show k0 - 1 ≤ K by omega)]
  refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg (fun k hk => ?_))
  · have hmem : ∀ k ∈ Finset.Ioc (k0 - 1) K, k0 ≤ k := fun k hk => by
      have := (Finset.mem_Ioc.mp hk).1; omega
    calc ((p (k0 - 1) - q 2) / (p K - q 2)) ^ (11 / 20 : ℝ)
        = (∏ k ∈ Finset.Ioc (k0 - 1) K, (p (k - 1) - q 2) / (p k - q 2)) ^ (11 / 20 : ℝ) := by
          rw [prod_Ioc_telescope (fun k => p k - q 2) (k0 - 1) K
            (fun k hk _ => (h.pk_sub_q2_pos (by omega : 2 ≤ k)).ne') (by omega)]
      _ = ∏ k ∈ Finset.Ioc (k0 - 1) K, ((p (k - 1) - q 2) / (p k - q 2)) ^ (11 / 20 : ℝ) := by
          rw [Real.finsetProd_rpow]
          intro k hk
          have := hmem k hk
          exact (div_pos (h.pk1_sub_q2_pos (by omega)) (h.pk_sub_q2_pos (by omega))).le
      _ ≤ _ := by
          refine Finset.prod_le_prod₀ (fun k hk => ?_) (fun k hk => h.V_factor (hmem k hk))
          have := hmem k hk
          exact Real.rpow_nonneg (div_pos (h.pk1_sub_q2_pos (by omega)) (h.pk_sub_q2_pos (by omega))).le _
  · have hk' := (Finset.mem_Ioc.mp hk)
    have h1 := h.q_gt_p (k := 2) (n := k) (by norm_num) (by omega)
    have h2 := h.pk_sub_q2_pos (by omega : 2 ≤ k)
    have h4 : q 2 < p 2 := h.int_hi 2 le_rfl
    exact (div_pos (by linarith) h2).le


lemma g_pos {k : ℕ} (hk : 2 ≤ k) : 0 < p k - p (k - 1) := by
  have := h.mono_lt (j := k - 1) (k := k) (by omega) (by omega)
  linarith

lemma u_pos {k n : ℕ} (hk : 1 ≤ k) (hkn : k < n) : 0 < q n - p k := by
  have := h.q_gt_p hk hkn; linarith

/-- far factor: `((q_n - q_k)/(q_n - p_k))² ≤ ((q_n - p_{k-1})/(q_n - p_k))^{6/5}`. -/
lemma far_factor {k n : ℕ} (hk : k0 ≤ k) (hn : k + 8 ≤ n) :
    ((q n - q k) / (q n - p k)) ^ 2 ≤ ((q n - p (k - 1)) / (q n - p k)) ^ (6 / 5 : ℝ) := by
  have hk3 : 3 ≤ k := h.k0_ge.trans hk
  have hu := h.u_pos (by omega : 1 ≤ k) (by omega : k < n)
  have hg := h.g_pos (by omega : 2 ≤ k)
  set u := q n - p k with hu_def
  set g := p k - p (k - 1) with hg_def
  have hv : q n - p (k - 1) = u + g := by rw [hu_def, hg_def]; ring
  obtain ⟨hf1, -⟩ := h.frac k hk
  have hq1 : q n - q k ≤ u + 11 / 20 * g := by rw [hu_def, hg_def]; linarith
  have hq0 : 0 ≤ q n - q k := by
    have := h.q_gt_p (k := k) (n := n) (by omega) (by omega)
    have := h.int_hi k (by omega)
    linarith
  have hx : g ≤ 3 / 10 * u := by
    have h1 := h.gap_up k hk3
    have h2 := h.gap_lo k (n - 1) (by omega) (by omega)
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hn1] at h2
    have hpn : p k < p (n - 1) := h.mono_lt (by omega) (by omega)
    have hpq : p (n - 1) < q n := h.int_lo n (by omega)
    have hu3 : (p (n - 1) - p k) ^ 3 ≤ u ^ 3 :=
      pow_le_pow_left₀ (by linarith) (by rw [hu_def]; linarith) 3
    have hκ2 : (2 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      linarith
    have ht8 : (8 : ℝ) ≤ (n : ℝ) - k := by
      have : (k : ℝ) + 8 ≤ n := by exact_mod_cast hn
      linarith
    have hnk : (n : ℝ) - 1 = ((k : ℝ) - 1) + ((n : ℝ) - k) := by ring
    have hnk1 : (n : ℝ) - 1 - k = ((n : ℝ) - k) - 1 := by ring
    rw [hnk1] at h2
    have hpos : 0 < (n : ℝ) - 1 := by linarith
    have hu3' : 5.8 * (((n : ℝ) - k) - 1) ^ 3 ≤ (((k : ℝ) - 1) + ((n : ℝ) - k)) * u ^ 3 := by
      rw [← hnk]; exact h2.trans (mul_le_mul_of_nonneg_left hu3 hpos.le)
    exact cube_core _ _ _ _ hκ2 ht8 hu h1 hu3'
  have hx0 : 0 ≤ g / u := by positivity
  have hxle : g / u ≤ 3 / 10 := by rw [div_le_iff₀ hu]; linarith
  have hratio : (q n - q k) / u ≤ 1 + 11 / 20 * (g / u) := by
    rw [div_le_iff₀ hu]
    have : (1 + 11 / 20 * (g / u)) * u = u + 11 / 20 * g := by field_simp
    rw [this]; exact hq1
  have hr0 : 0 ≤ (q n - q k) / u := div_nonneg hq0 hu.le
  have hsq : ((q n - q k) / u) ^ 2 ≤ (1 + 11 / 20 * (g / u)) ^ 2 := pow_le_pow_left₀ hr0 hratio 2
  have hb := bern_ge (g / u) hx0
  have hvu : (q n - p (k - 1)) / u = 1 + g / u := by rw [hv]; field_simp
  rw [hvu]
  refine hsq.trans (le_trans ?_ hb)
  nlinarith [mul_nonneg hx0 hx0, hxle]


lemma d_pos {k : ℕ} (hk : 2 ≤ k) : 0 < q (k + 1) - p k := by
  have := h.q_gt_p (k := k) (n := k + 1) (by omega) (by omega)
  linarith

lemma d_le_u {k n : ℕ} (hk : 2 ≤ k) (hkn : k < n) : q (k + 1) - p k ≤ q n - p k := by
  rcases Nat.eq_or_lt_of_le (show k + 1 ≤ n by omega) with h1 | h1
  · rw [h1]
  · have h2 := h.q_gt_p (k := k + 1) (n := n) (by omega) h1
    have h3 := h.int_hi (k + 1) (by omega)
    linarith

lemma Bk_ge_one {k : ℕ} (hk : 3 ≤ k) : 1 ≤ Bk p q k := by
  unfold Bk
  have hg := h.g_pos (by omega : 2 ≤ k)
  have hd := h.d_pos (by omega : 2 ≤ k)
  have : 0 ≤ (p k - p (k - 1)) / (q (k + 1) - p k) := by positivity
  nlinarith

lemma near_factor {k n : ℕ} (hk : 3 ≤ k) (hkn : k < n) :
    ((q n - q k) / (q n - p k)) ^ 2 ≤ Bk p q k := by
  unfold Bk
  have hu := h.u_pos (by omega : 1 ≤ k) hkn
  have hg := h.g_pos (by omega : 2 ≤ k)
  have hd := h.d_pos (by omega : 2 ≤ k)
  have hdu := h.d_le_u (by omega : 2 ≤ k) hkn
  have hq0 : 0 ≤ q n - q k := by
    have := h.q_gt_p (k := k) (n := n) (by omega) hkn
    have := h.int_hi k (by omega)
    linarith
  have hlo := h.int_lo k (by omega)
  have h1 : (q n - q k) / (q n - p k) ≤ 1 + (p k - p (k - 1)) / (q (k + 1) - p k) := by
    have a1 : (q n - q k) / (q n - p k) ≤ 1 + (p k - p (k - 1)) / (q n - p k) := by
      rw [div_le_iff₀ hu]
      have : (1 + (p k - p (k - 1)) / (q n - p k)) * (q n - p k) = (q n - p k) + (p k - p (k - 1)) := by
        field_simp
      rw [this]; linarith
    have a2 : (p k - p (k - 1)) / (q n - p k) ≤ (p k - p (k - 1)) / (q (k + 1) - p k) :=
      div_le_div_of_nonneg_left hg.le hd hdu
    linarith
  exact pow_le_pow_left₀ (div_nonneg hq0 hu.le) h1 2

lemma Bk_le {k : ℕ} (hk : k0 ≤ k) : Bk p q k ≤ 18 := by
  have hk3 : 3 ≤ k := h.k0_ge.trans hk
  unfold Bk
  have hg := h.g_pos (by omega : 2 ≤ k)
  have hg1 := h.g_pos (by omega : 2 ≤ k + 1)
  have hd := h.d_pos (by omega : 2 ≤ k)
  obtain ⟨hf1, -⟩ := h.frac (k + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hf1 hg1
  have hup := h.gap_up k hk3
  have hlo := h.gap_lo k (k + 1) (by omega) (by omega)
  have hκ : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  push_cast at hlo
  have hlo' : 5.8 ≤ ((k : ℝ) + 1) * (p (k + 1) - p k) ^ 3 := by nlinarith
  -- g_k ≤ 1.43 g_{k+1}
  have hrat : p k - p (k - 1) ≤ 1.43 * (p (k + 1) - p k) := by
    by_contra hcon
    push Not at hcon
    have hc := pow_lt_pow_left₀ hcon (by positivity) (by norm_num : (3 : ℕ) ≠ 0)
    have e : (1.43 * (p (k + 1) - p k)) ^ 3 = 2.924207 * (p (k + 1) - p k) ^ 3 := by ring
    rw [e] at hc
    have b1 : (k - 1 : ℝ) * (p k - p (k - 1)) ^ 3 ≤ 8.4 := hup
    have b2 : 2.924207 * 5.8 ≤ 2.924207 * (((k : ℝ) + 1) * (p (k + 1) - p k) ^ 3) :=
      mul_le_mul_of_nonneg_left hlo' (by norm_num)
    have : ((k : ℝ) - 1) * (2.924207 * (p (k + 1) - p k) ^ 3) < ((k : ℝ) - 1) * (p k - p (k - 1)) ^ 3 :=
      mul_lt_mul_of_pos_left hc (by linarith)
    nlinarith
  have hdlow : 9 / 20 * (p (k + 1) - p k) ≤ q (k + 1) - p k := hf1
  have hq : (p k - p (k - 1)) / (q (k + 1) - p k) ≤ 3.2 := by
    rw [div_le_iff₀ hd]
    nlinarith
  have hx0 : 0 ≤ (p k - p (k - 1)) / (q (k + 1) - p k) := by positivity
  nlinarith [mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ 3.2 - (p k - p (k - 1)) / (q (k + 1) - p k))]


/-- The `U`-product bound: `(∏_{k=3}^K (q_n - q_k)/(q_n - p_k))² ≤ C_U ((q_n - p_2)/(q_n - p_K))^{6/5}`. -/
lemma U_bound {K n : ℕ} (hK : k0 ≤ K) (hn : K < n) :
    (∏ k ∈ Finset.Ioc 2 K, (q n - q k) / (q n - p k)) ^ 2 ≤
      ((∏ k ∈ Finset.Ioc 2 (k0 - 1), Bk p q k) * 18 ^ 8) *
        ((q n - p 2) / (q n - p K)) ^ (6 / 5 : ℝ) := by
  have h3 := h.k0_ge
  set c : ℕ → ℝ := fun k => if k < k0 then Bk p q k else if n < k + 8 then 18 else 1 with hc
  set hh : ℕ → ℝ := fun k => (q n - p (k - 1)) / (q n - p k) with hhh
  have hu : ∀ k ∈ Finset.Ioc 2 K, 0 < q n - p k := fun k hk => by
    have := Finset.mem_Ioc.mp hk
    exact h.u_pos (by omega) (by omega)
  have hh1 : ∀ k ∈ Finset.Ioc 2 K, 1 ≤ hh k := fun k hk => by
    have hk' := Finset.mem_Ioc.mp hk
    have hu' := hu k hk
    have hg := h.g_pos (by omega : 2 ≤ k)
    simp only [hhh]
    rw [le_div_iff₀ hu']; linarith
  have hpt : ∀ k ∈ Finset.Ioc 2 K, ((q n - q k) / (q n - p k)) ^ 2 ≤ c k * hh k ^ (6 / 5 : ℝ) := by
    intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    have hrp : 1 ≤ hh k ^ (6 / 5 : ℝ) := Real.one_le_rpow (hh1 k hk) (by norm_num)
    by_cases hkk : k < k0
    · have := h.near_factor (k := k) (n := n) (by omega) (by omega)
      simp only [hc, if_pos hkk]
      nlinarith [h.Bk_ge_one (k := k) (by omega)]
    · push Not at hkk
      by_cases hnk : n < k + 8
      · have := h.near_factor (k := k) (n := n) (by omega) (by omega)
        have h18 := h.Bk_le hkk
        simp only [hc, if_neg (not_lt.mpr hkk), if_pos hnk]
        nlinarith
      · push Not at hnk
        have := h.far_factor hkk hnk
        simp only [hc, if_neg (not_lt.mpr hkk), if_neg (not_lt.mpr hnk)]
        simpa [hhh] using this
  have hprod : ∏ k ∈ Finset.Ioc 2 K, ((q n - q k) / (q n - p k)) ^ 2 ≤
      (∏ k ∈ Finset.Ioc 2 K, c k) * ∏ k ∈ Finset.Ioc 2 K, hh k ^ (6 / 5 : ℝ) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun k _ => sq_nonneg _) hpt
  have htel : ∏ k ∈ Finset.Ioc 2 K, hh k = (q n - p 2) / (q n - p K) := by
    simp only [hhh]
    exact prod_Ioc_telescope (fun k => q n - p k) 2 K (fun k h1 h2 =>
      (h.u_pos (by omega) (by omega)).ne') (by omega)
  have hcprod : ∏ k ∈ Finset.Ioc 2 K, c k ≤ (∏ k ∈ Finset.Ioc 2 (k0 - 1), Bk p q k) * 18 ^ 8 := by
    rw [← Finset.prod_Ioc_consecutive _ (show 2 ≤ k0 - 1 by omega) (show k0 - 1 ≤ K by omega)]
    have e1 : ∏ k ∈ Finset.Ioc 2 (k0 - 1), c k = ∏ k ∈ Finset.Ioc 2 (k0 - 1), Bk p q k := by
      refine Finset.prod_congr rfl (fun k hk => ?_)
      have := (Finset.mem_Ioc.mp hk).2
      simp only [hc]; rw [if_pos (by omega)]
    have hB : 0 ≤ ∏ k ∈ Finset.Ioc 2 (k0 - 1), Bk p q k :=
      Finset.prod_nonneg (fun k hk => by
        have := Finset.mem_Ioc.mp hk
        exact (h.Bk_ge_one (by omega)).trans' zero_le_one)
    rw [e1]
    refine mul_le_mul_of_nonneg_left ?_ hB
    have e2 : ∏ k ∈ Finset.Ioc (k0 - 1) K, c k =
        ∏ k ∈ Finset.Ioc (k0 - 1) K, (if n < k + 8 then (18 : ℝ) else 1) := by
      refine Finset.prod_congr rfl (fun k hk => ?_)
      have := (Finset.mem_Ioc.mp hk).1
      simp only [hc]; rw [if_neg (by omega)]
    rw [e2, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    refine pow_le_pow_right₀ (by norm_num) ?_
    calc ((Finset.Ioc (k0 - 1) K).filter (fun k => n < k + 8)).card
        ≤ (Finset.Ioc (n - 8) K).card := by
          refine Finset.card_le_card (fun k hk => ?_)
          have := Finset.mem_filter.mp hk
          have := Finset.mem_Ioc.mp this.1
          simp only [Finset.mem_Ioc]; omega
      _ ≤ 8 := by simp; omega
  have hpow : ∏ k ∈ Finset.Ioc 2 K, hh k ^ (6 / 5 : ℝ) = (∏ k ∈ Finset.Ioc 2 K, hh k) ^ (6 / 5 : ℝ) := by
    rw [Real.finsetProd_rpow]
    intro k hk
    exact (hh1 k hk).trans' zero_le_one
  rw [← Finset.prod_pow]
  refine hprod.trans ?_
  rw [hpow, htel]
  refine mul_le_mul_of_nonneg_right hcprod (Real.rpow_nonneg ?_ _)
  have hnK := h.u_pos (k := K) (n := n) (by omega) hn
  have h2K : p 2 ≤ p K := h.mono' (by omega) (by omega)
  exact div_nonneg (by linarith) hnK.le


/-- Cube-root form of `B ≥ n^{2/3}`: `q_n - p_2 ≥ n^{2/3}` for `n ≥ 9`. -/
lemma B_lower {n : ℕ} (hn : 9 ≤ n) : (n : ℝ) ^ (2 / 3 : ℝ) ≤ q n - p 2 := by
  have hnr : (9 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := h.cube_lo (n - 1) (by omega)
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hn1] at h1
  have h2 := h.cube_hi 2 le_rfl
  have hp2 : p 2 ≤ 5 := by
    by_contra hcon
    push Not at hcon
    have := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at h2 this
    linarith
  have hpn : 10 ≤ p (n - 1) := by
    by_contra hcon
    push Not at hcon
    have hp0 : 0 ≤ p (n - 1) := (h.pos (n - 1) (by omega)).le
    have := pow_lt_pow_left₀ hcon hp0 (by norm_num : (3 : ℕ) ≠ 0)
    nlinarith
  have hq := h.int_lo n (by omega)
  have hB : p (n - 1) / 2 ≤ q n - p 2 := by linarith
  have hB3 : (p (n - 1) / 2) ^ 3 ≤ (q n - p 2) ^ 3 := pow_le_pow_left₀ (by linarith) hB 3
  have hn0 : 0 < (n : ℝ) := by linarith
  have hc : ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (n : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  refine le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by linarith) ?_
  rw [hc]
  have : (p (n - 1) / 2) ^ 3 = p (n - 1) ^ 3 / 8 := by ring
  nlinarith

/-- `D = q_n - p_K` satisfies `D³ n ≥ (1/2) (n-K)³` for `K ≥ k0`, `K < n`. -/
lemma D_lower {K n : ℕ} (hK : k0 ≤ K) (hn : K < n) :
    (1 / 2 : ℝ) * ((n : ℝ) - K) ^ 3 ≤ n * (q n - p K) ^ 3 := by
  have h3 := h.k0_ge
  have hK3 : 3 ≤ K := by omega
  have hnr : (K : ℝ) + 1 ≤ n := by exact_mod_cast hn
  rcases Nat.eq_or_lt_of_le (show K + 1 ≤ n by omega) with h1 | h1
  · subst h1
    obtain ⟨hf, -⟩ := h.frac (K + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hf
    have hg := h.g_pos (by omega : 2 ≤ K + 1)
    simp only [Nat.add_sub_cancel] at hg
    have hlo := h.gap_lo K (K + 1) (by omega) (by omega)
    push_cast at hlo
    have hlo' : 5.8 ≤ ((K : ℝ) + 1) * (p (K + 1) - p K) ^ 3 := by nlinarith
    have hD : 9 / 20 * (p (K + 1) - p K) ≤ q (K + 1) - p K := hf
    have hc := pow_le_pow_left₀ (by positivity) hD 3
    have e : (9 / 20 * (p (K + 1) - p K)) ^ 3 = 0.091125 * (p (K + 1) - p K) ^ 3 := by ring
    rw [e] at hc
    push_cast
    have : ((K : ℝ) + 1) * (0.091125 * (p (K + 1) - p K) ^ 3) ≤ ((K : ℝ) + 1) * (q (K + 1) - p K) ^ 3 :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    nlinarith
  · have h2 := h.gap_lo K (n - 1) (by omega) (by omega)
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hn1] at h2
    have hpq : p (n - 1) < q n := h.int_lo n (by omega)
    have hpK : p K < p (n - 1) := h.mono_lt (by omega) (by omega)
    have hu3 : (p (n - 1) - p K) ^ 3 ≤ (q n - p K) ^ 3 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 3
    have hm2 : (2 : ℝ) ≤ (n : ℝ) - K := by
      have : (K : ℝ) + 2 ≤ n := by exact_mod_cast (show K + 2 ≤ n by omega)
      linarith
    have hn0 : (0 : ℝ) < n - 1 := by linarith
    have hh : 5.8 * (((n : ℝ) - 1) - K) ^ 3 ≤ ((n : ℝ) - 1) * (q n - p K) ^ 3 :=
      h2.trans (mul_le_mul_of_nonneg_left hu3 hn0.le)
    have hD0 : 0 ≤ (q n - p K) ^ 3 := by
      have : 0 < q n - p K := by linarith
      positivity
    have hm1 : (n : ℝ) - K ≤ 2 * (((n : ℝ) - 1) - K) := by linarith
    have hm1' : ((n : ℝ) - K) ^ 3 ≤ 8 * (((n : ℝ) - 1) - K) ^ 3 := by
      have := pow_le_pow_left₀ (by linarith) hm1 3
      nlinarith
    have : ((n : ℝ) - 1) * (q n - p K) ^ 3 ≤ n * (q n - p K) ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) hD0
    nlinarith

lemma A_upper {K : ℕ} (hK : 2 ≤ K) : p K - q 2 ≤ 3 * (K : ℝ) ^ (2 / 3 : ℝ) := by
  have h1 := h.cube_hi K hK
  have hq2 : 0 < q 2 := by
    have := h.int_lo 2 le_rfl
    have h4 := h.pos 1 le_rfl
    simpa using h4.trans this
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hc : (3 * (K : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 27 * (K : ℝ) ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast ((K : ℝ) ^ (2 / 3 : ℝ)) 3, ← Real.rpow_mul hK0.le]; norm_num
  have hpk0 : 0 < p K := h.pos K (by omega)
  refine le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by positivity) ?_
  rw [hc]
  have : (p K - q 2) ^ 3 ≤ p K ^ 3 := pow_le_pow_left₀ (h.pk_sub_q2_pos hK).le (by linarith) 3
  nlinarith [sq_nonneg (K : ℝ)]


/-- The constant of the tail bound. -/
noncomputable def absConst (p q : ℕ → ℝ) (k0 : ℕ) : ℝ :=
  ((∏ k ∈ Finset.Ioc 2 (k0 - 1), Bk p q k) * 18 ^ 8) *
    ((∏ k ∈ Finset.Ioc 2 (k0 - 1), (q k - q 2) / (p k - q 2)) *
        (p (k0 - 1) - q 2) ^ (11 / 20 : ℝ))⁻¹ ^ 2 *
    (3 ^ (11 / 10 : ℝ) * 0.7 ^ (-(6 / 5) : ℝ))

lemma V_pos {K : ℕ} (hK : 2 ≤ K) : 0 < ∏ k ∈ Finset.Ioc 2 K, (q k - q 2) / (p k - q 2) := by
  refine Finset.prod_pos (fun k hk => ?_)
  have hk' := Finset.mem_Ioc.mp hk
  have h1 := h.q_gt_p (k := 2) (n := k) (by norm_num) (by omega)
  have h4 : q 2 < p 2 := h.int_hi 2 le_rfl
  exact div_pos (by linarith) (h.pk_sub_q2_pos (by omega))

/-- **Termwise bound** for `n = K + 1 + i`. -/
lemma term_bound {K : ℕ} (hK : max k0 8 ≤ K) (i : ℕ) :
    absTerm p q K (K + 1 + i) ≤ absConst p q k0 * (K : ℝ) ^ (-(1 / 15) : ℝ) * ((i : ℝ) + 1) ^ (-(6 / 5) : ℝ) := by
  have hk0K : k0 ≤ K := (le_max_left _ _).trans hK
  have h8K : 8 ≤ K := (le_max_right _ _).trans hK
  have h3 := h.k0_ge
  set n := K + 1 + i with hn
  have hKn : K < n := by omega
  have hnr : (K : ℝ) ≤ n := by exact_mod_cast (by omega : K ≤ n)
  set A := p K - q 2 with hA
  set B := q n - p 2 with hB
  set D := q n - p K with hD
  have hApos : 0 < A := h.pk_sub_q2_pos (by omega)
  have hDpos : 0 < D := h.u_pos (by omega) hKn
  have hBge := h.B_lower (n := n) (by omega)
  have hBpos : 0 < B := lt_of_lt_of_le (Real.rpow_pos_of_pos (by positivity) _) hBge
  set U := ∏ k ∈ Finset.Ioc 2 K, (q n - q k) / (q n - p k) with hU
  set V := ∏ k ∈ Finset.Ioc 2 K, (q k - q 2) / (p k - q 2) with hV
  set V0 := ∏ k ∈ Finset.Ioc 2 (k0 - 1), (q k - q 2) / (p k - q 2) with hV0
  set A0 := p (k0 - 1) - q 2 with hA0
  have hV0pos : 0 < V0 := h.V_pos (by omega)
  have hA0pos : 0 < A0 := h.pk_sub_q2_pos (by omega : 2 ≤ k0 - 1)
  have hVpos : 0 < V := h.V_pos (by omega)
  have hVlow := h.V_bound hk0K
  rw [← hV0, ← hV, ← hA0, ← hA] at hVlow
  have hUb := h.U_bound hk0K hKn
  rw [← hU, ← hB, ← hD] at hUb
  -- V⁻¹ ≤ (V0 A0^s)⁻¹ A^s
  have hAs : 0 < A ^ (11 / 20 : ℝ) := Real.rpow_pos_of_pos hApos _
  have hA0s : 0 < A0 ^ (11 / 20 : ℝ) := Real.rpow_pos_of_pos hA0pos _
  have hVinv : V⁻¹ ≤ (V0 * A0 ^ (11 / 20 : ℝ))⁻¹ * A ^ (11 / 20 : ℝ) := by
    have e : V0 * (A0 / A) ^ (11 / 20 : ℝ) = (V0 * A0 ^ (11 / 20 : ℝ)) * (A ^ (11 / 20 : ℝ))⁻¹ := by
      rw [Real.div_rpow hA0pos.le hApos.le]; field_simp
    rw [e] at hVlow
    rw [inv_le_comm₀ hVpos (by positivity)]
    calc ((V0 * A0 ^ (11 / 20 : ℝ))⁻¹ * A ^ (11 / 20 : ℝ))⁻¹
        = (V0 * A0 ^ (11 / 20 : ℝ)) * (A ^ (11 / 20 : ℝ))⁻¹ := by
          rw [mul_inv, inv_inv, mul_comm]
      _ ≤ V := hVlow
  have hV2 : (V⁻¹) ^ 2 ≤ ((V0 * A0 ^ (11 / 20 : ℝ))⁻¹) ^ 2 * A ^ (11 / 10 : ℝ) := by
    calc (V⁻¹) ^ 2 ≤ ((V0 * A0 ^ (11 / 20 : ℝ))⁻¹ * A ^ (11 / 20 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (inv_nonneg.mpr hVpos.le) hVinv 2
      _ = ((V0 * A0 ^ (11 / 20 : ℝ))⁻¹) ^ 2 * A ^ (11 / 10 : ℝ) := by
          rw [mul_pow]; congr 1
          rw [← Real.rpow_natCast (A ^ (11 / 20 : ℝ)) 2, ← Real.rpow_mul hApos.le]; norm_num
  -- main chain
  have hB3 : (B ^ 3)⁻¹ = B ^ (-3 : ℝ) := by
    rw [Real.rpow_neg hBpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hQ : (B / D) ^ (6 / 5 : ℝ) = B ^ (6 / 5 : ℝ) * D ^ (-(6 / 5) : ℝ) := by
    rw [Real.div_rpow hBpos.le hDpos.le, Real.rpow_neg hDpos.le, div_eq_mul_inv]
  have hBe : B ^ (-3 : ℝ) * B ^ (6 / 5 : ℝ) = B ^ (6 / 5 - 3 : ℝ) := by
    rw [← Real.rpow_add hBpos]; ring_nf
  unfold absTerm
  rw [← hU, ← hV, ← hB]
  have hCU : 0 ≤ (∏ k ∈ Finset.Ioc 2 (k0 - 1), Bk p q k) * 18 ^ 8 := by
    have : 0 ≤ ∏ k ∈ Finset.Ioc 2 (k0 - 1), Bk p q k :=
      Finset.prod_nonneg (fun k hk => by
        have := Finset.mem_Ioc.mp hk
        exact (h.Bk_ge_one (by omega)).trans' zero_le_one)
    positivity
  calc (B ^ 3)⁻¹ * U ^ 2 * (V⁻¹) ^ 2
      ≤ B ^ (-3 : ℝ) * (((∏ k ∈ Finset.Ioc 2 (k0 - 1), Bk p q k) * 18 ^ 8) * (B / D) ^ (6 / 5 : ℝ)) *
          (((V0 * A0 ^ (11 / 20 : ℝ))⁻¹) ^ 2 * A ^ (11 / 10 : ℝ)) := by
        rw [hB3]
        refine mul_le_mul (mul_le_mul_of_nonneg_left hUb (Real.rpow_nonneg hBpos.le _)) hV2
          (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg hBpos.le _) (mul_nonneg hCU (Real.rpow_nonneg (div_nonneg hBpos.le hDpos.le) _)))
    _ = (((∏ k ∈ Finset.Ioc 2 (k0 - 1), Bk p q k) * 18 ^ 8) * ((V0 * A0 ^ (11 / 20 : ℝ))⁻¹) ^ 2) *
          (A ^ (11 / 10 : ℝ) * B ^ (6 / 5 - 3 : ℝ) * D ^ (-(6 / 5) : ℝ)) := by
        rw [hQ, ← hBe]; ring
    _ ≤ (((∏ k ∈ Finset.Ioc 2 (k0 - 1), Bk p q k) * 18 ^ 8) * ((V0 * A0 ^ (11 / 20 : ℝ))⁻¹) ^ 2) *
          ((3 ^ (11 / 10 : ℝ) * 0.7 ^ (-(6 / 5) : ℝ)) * (K : ℝ) ^ (-(1 / 15) : ℝ) *
            ((i : ℝ) + 1) ^ (-(6 / 5) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCU (sq_nonneg _))
        have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
        have hm : (1 : ℝ) ≤ (i : ℝ) + 1 := by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
        have hmn : (n : ℝ) - K = (i : ℝ) + 1 := by rw [hn]; push_cast; ring
        have hDlow : 0.7 * ((i : ℝ) + 1) * (n : ℝ) ^ (-(1 / 3) : ℝ) ≤ D := by
          have hD3 := h.D_lower hk0K hKn
          rw [hmn] at hD3
          have hn0 : (0 : ℝ) < n := by linarith
          have hc : (0.7 * ((i : ℝ) + 1) * (n : ℝ) ^ (-(1 / 3) : ℝ)) ^ 3 =
              0.343 * ((i : ℝ) + 1) ^ 3 / n := by
            rw [mul_pow, mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-(1 / 3) : ℝ)) 3,
              ← Real.rpow_mul hn0.le]
            norm_num
            rw [Real.rpow_neg_one]; ring
          refine le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) hDpos.le ?_
          rw [hc, div_le_iff₀ hn0]
          nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ (i : ℝ) + 1) 3]
        exact rpow_combine (K : ℝ) (n : ℝ) ((i : ℝ) + 1) A B D hKr hnr hm hApos
          (h.A_upper (by omega)) hBge hDlow
    _ = _ := by unfold absConst; ring

end NodeHyp

end FormalResearch.ModularBootstrap.TwoLevel
