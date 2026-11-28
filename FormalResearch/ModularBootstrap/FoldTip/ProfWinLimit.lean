module

public import FormalResearch.ModularBootstrap.FoldTip.DualMeasures
public import FormalResearch.ModularBootstrap.Upper.Assembly.BumpedDesignWindow

/-!
# Local uniform and quadrature limits for approximating `profWin` designs

For `s ≥ 2`, `b ∈ ℝ`, `uF ∈ ℝ`, and an `InAiryClass` function `W_ideal` whose meromorphic factor is
`((z - b)/(z - a_s))² ((z - uF)/(z - a₁)) G_Ai(z)` and which vanishes at every `a_n` (`n ∉ {1, s}`):

* `profWin_disp_tendstoLocallyUniformly_C`: the approximating profile products `profW` with `N_n = s + n`,
  `η_n = 1/(n+4)`, and displaced site `a_s ↦ b` converge locally uniformly on `ℂ` to `W_ideal`.
* `profWin_disp_V_tendsto`: the quadrature sums `(D n).V` converge to `∫ u, (W_ideal (u : ℂ)).re`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal Real

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.Special FormalResearch.SignUncertainty
  FormalResearch.ModularBootstrap.Upper.Rigidity
  FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Ramped
  FormalResearch.ModularBootstrap.Upper.Assembly
  Polynomial

private lemma norm_tprod_sub_one_le {f : ℕ → ℂ} {P : ℂ} (hp : HasProd f P)
    (hs : Summable fun m => ‖f m - 1‖) {B : ℝ} (hB : ∑' m, ‖f m - 1‖ ≤ B) :
    ‖P - 1‖ ≤ Real.exp B - 1 := by
  have hfin : ∀ S : Finset ℕ, ‖∏ m ∈ S, f m - 1‖ ≤ (∏ m ∈ S, (1 + ‖f m - 1‖)) - 1 := by
    intro S
    induction S using Finset.induction with
    | empty => simp
    | @insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hid : f a * (∏ m ∈ S, f m) - 1 = (f a - 1) * (∏ m ∈ S, f m - 1) + (f a - 1) +
          (∏ m ∈ S, f m - 1) := by ring
      rw [hid]
      have ha_nn : 0 ≤ ‖f a - 1‖ := norm_nonneg _
      have h1 : ‖(f a - 1) * (∏ m ∈ S, f m - 1) + (f a - 1)‖ ≤
          ‖(f a - 1) * (∏ m ∈ S, f m - 1)‖ + ‖f a - 1‖ := norm_add_le _ _
      have h2 : ‖(f a - 1) * (∏ m ∈ S, f m - 1) + (f a - 1) + (∏ m ∈ S, f m - 1)‖ ≤
          ‖(f a - 1) * (∏ m ∈ S, f m - 1) + (f a - 1)‖ + ‖∏ m ∈ S, f m - 1‖ := norm_add_le _ _
      have hmul : ‖(f a - 1) * (∏ m ∈ S, f m - 1)‖ ≤
          ‖f a - 1‖ * ((∏ m ∈ S, (1 + ‖f m - 1‖)) - 1) := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left ih ha_nn
      linarith
  have hexp : ∀ S : Finset ℕ, (∏ m ∈ S, (1 + ‖f m - 1‖)) - 1 ≤ Real.exp B - 1 := fun S => by
    have h1 : ∏ m ∈ S, (1 + ‖f m - 1‖) ≤ ∏ m ∈ S, Real.exp ‖f m - 1‖ :=
      Finset.prod_le_prod₀ (fun m _ => show (0 : ℝ) ≤ 1 + ‖f m - 1‖ by positivity)
        (fun m _ => by linarith [Real.add_one_le_exp ‖f m - 1‖])
    rw [← Real.exp_sum] at h1
    have hsum : ∑ m ∈ S, ‖f m - 1‖ ≤ B :=
      (hs.sum_le_tsum S (fun _ _ => norm_nonneg _)).trans hB
    linarith [Real.exp_le_exp.mpr hsum]
  have ht : Tendsto (fun S : Finset ℕ => ‖∏ m ∈ S, f m - 1‖) atTop (𝓝 ‖P - 1‖) :=
    continuous_norm.continuousAt.tendsto.comp (hp.sub tendsto_const_nhds)
  exact le_of_tendsto ht (Eventually.of_forall fun S => (hfin S).trans (hexp S))

private lemma exists_radius_avoid_airyZero (R : ℝ) :
    ∃ R' : ℝ, R < R' ∧ ∀ k : ℕ, 1 ≤ k → R' ≠ |airyZero k| := by
  have hc : Tendsto (fun k : ℕ => |airyZero (k + 1)|) atTop atTop := by
    have ht := tendsto_airyNode
    have heq : (fun k : ℕ => |airyZero (k + 1)|) = fun k => -(airyNode k) := by
      ext k; exact abs_of_neg (airyZero_neg (k + 1))
    rw [heq]
    exact Filter.tendsto_neg_atBot_atTop.comp ht
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hc.eventually_gt_atTop R)
  have hanti : airyZero (N + 2) < airyZero (N + 1) :=
    airyZero_lt_of_lt (by omega : 1 ≤ N + 1) (Nat.lt_succ_self (N + 1))
  have hneg1 : airyZero (N + 1) < 0 := airyZero_neg (N + 1)
  have hneg2 : airyZero (N + 2) < 0 := airyZero_neg (N + 2)
  have hlt : |airyZero (N + 1)| < |airyZero (N + 2)| := by
    rw [abs_of_neg hneg1, abs_of_neg hneg2]; linarith
  refine ⟨(|airyZero (N + 1)| + |airyZero (N + 2)|) / 2, ?_, fun k hk heq => ?_⟩
  · linarith [hN N le_rfl]
  · rcases le_or_gt k (N + 1) with hk1 | hk2
    · have hle : |airyZero k| ≤ |airyZero (N + 1)| := by
        rcases eq_or_lt_of_le hk1 with rfl | hklt
        · exact le_rfl
        · have hklt' := airyZero_lt_of_lt hk hklt
          rw [abs_of_neg (airyZero_neg k), abs_of_neg hneg1]; linarith
      linarith
    · have hge : |airyZero (N + 2)| ≤ |airyZero k| := by
        rcases eq_or_lt_of_le (by omega : N + 2 ≤ k) with rfl | hklt
        · exact le_rfl
        · have hklt' := airyZero_lt_of_lt (by omega) hklt
          rw [abs_of_neg hneg2, abs_of_neg (airyZero_neg k)]; linarith
      linarith

private lemma airyZero_abs_ge_of_large (R' : ℝ) :
    ∃ K₀ : ℕ, 2 ≤ K₀ ∧ ∀ k : ℕ, K₀ ≤ k → ∀ z : ℂ, ‖z‖ ≤ R' →
      (k : ℝ) ^ ((2 : ℝ) / 3) ≤ ‖z - (airyZero k : ℂ)‖ ∧ R' ≠ |airyZero k| := by
  let K₀ := ⌈(max R' 0 + 1) ^ ((3 : ℝ) / 2)⌉₊ + 2
  refine ⟨K₀, by omega, fun k hk z hz => ?_⟩
  have hk2 : 2 ≤ k := by omega
  have hk_r : max R' 0 + 1 ≤ (k : ℝ) ^ ((2 : ℝ) / 3) := by
    have hc : (max R' 0 + 1) ^ ((3 : ℝ) / 2) ≤ (k : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈(max R' 0 + 1) ^ ((3 : ℝ) / 2)⌉₊ ≤ k))
    have hpow := Real.rpow_le_rpow (by positivity) hc (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one] at hpow
    exact hpow
  obtain ⟨ha_lo, -⟩ := airyZero_abs_bounds hk2
  have hneg := abs_of_neg (airyZero_neg k)
  rw [← hneg] at ha_lo
  have hz_norm : ‖(airyZero k : ℂ)‖ = |airyZero k| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have htri : |airyZero k| - R' ≤ ‖z - (airyZero k : ℂ)‖ := by
    have h := norm_sub_norm_le (airyZero k : ℂ) z
    rw [norm_sub_rev, hz_norm] at h
    linarith
  have hkpos : 0 < (k : ℝ) ^ ((2 : ℝ) / 3) := by positivity
  have h1 : R' ≤ (k : ℝ) ^ ((2 : ℝ) / 3) := (le_max_left R' 0).trans (by linarith)
  have h2 : (k : ℝ) ^ ((2 : ℝ) / 3) ≤ |airyZero k| - R' := by linarith
  refine ⟨h2.trans htri, fun h => ?_⟩
  linarith

private lemma airyProdFactor_sub_one_bound (uSite epsU : ℕ → ℝ) (k : ℕ) {z : ℂ}
    (hz : z ≠ (airyZero k : ℂ)) :
    ‖airyProdFactor uSite epsU k z - 1‖ ≤
      2 * |uSite k - airyZero k| / ‖z - (airyZero k : ℂ)‖ +
        (|uSite k - airyZero k| ^ 2 + |epsU k| ^ 2) / ‖z - (airyZero k : ℂ)‖ ^ 2 := by
  have hne : z - (airyZero k : ℂ) ≠ 0 := sub_ne_zero.mpr hz
  have hid : airyProdFactor uSite epsU k z - 1 =
      (((uSite k - airyZero k : ℝ) : ℂ) ^ 2 + ((epsU k : ℝ) : ℂ) ^ 2 -
        2 * ((uSite k - airyZero k : ℝ) : ℂ) * (z - (airyZero k : ℂ))) /
        (z - (airyZero k : ℂ)) ^ 2 := by
    unfold airyProdFactor
    push_cast; field_simp; ring
  rw [hid, norm_div, norm_pow]
  have htop : ‖((uSite k - airyZero k : ℝ) : ℂ) ^ 2 + ((epsU k : ℝ) : ℂ) ^ 2 -
        2 * ((uSite k - airyZero k : ℝ) : ℂ) * (z - (airyZero k : ℂ))‖ ≤
      (|uSite k - airyZero k| ^ 2 + |epsU k| ^ 2) +
        2 * |uSite k - airyZero k| * ‖z - (airyZero k : ℂ)‖ := by
    have h1 := norm_sub_le
      (((uSite k - airyZero k : ℝ) : ℂ) ^ 2 + ((epsU k : ℝ) : ℂ) ^ 2)
      (2 * ((uSite k - airyZero k : ℝ) : ℂ) * (z - (airyZero k : ℂ)))
    have h2 := norm_add_le (((uSite k - airyZero k : ℝ) : ℂ) ^ 2) (((epsU k : ℝ) : ℂ) ^ 2)
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_ofNat] at h1 h2
    linarith
  have hpos : 0 < ‖z - (airyZero k : ℂ)‖ := norm_pos_iff.mpr hne
  have hdiv : ((|uSite k - airyZero k| ^ 2 + |epsU k| ^ 2) +
        2 * |uSite k - airyZero k| * ‖z - (airyZero k : ℂ)‖) / ‖z - (airyZero k : ℂ)‖ ^ 2 =
      2 * |uSite k - airyZero k| / ‖z - (airyZero k : ℂ)‖ +
        (|uSite k - airyZero k| ^ 2 + |epsU k| ^ 2) / ‖z - (airyZero k : ℂ)‖ ^ 2 := by
    field_simp [hpos.ne']; ring
  exact (div_le_div_of_nonneg_right htop (sq_nonneg _)).trans_eq hdiv

private lemma sphere_dist_min (K₀ : ℕ) (hK₀ : 2 ≤ K₀) (R' : ℝ) (hR' : ∀ k : ℕ, 1 ≤ k → R' ≠ |airyZero k|) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ, 1 ≤ k → k < K₀ → ∀ z : ℂ, ‖z‖ = R' → δ ≤ ‖z - (airyZero k : ℂ)‖ := by
  have hfin : (Finset.Ico 1 K₀).Nonempty := ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
  have hpos : ∀ k ∈ Finset.Ico 1 K₀, 0 < |R' - (|airyZero k|)| := fun k hk =>
    abs_pos.mpr (sub_ne_zero.mpr (hR' k (Finset.mem_Ico.mp hk).1))
  let δ : ℝ := (Finset.Ico 1 K₀).inf' hfin (fun k => |R' - (|airyZero k|)|)
  refine ⟨δ, (Finset.lt_inf'_iff hfin).2 hpos, fun k hk1 hkK z hz => ?_⟩
  have hinf : δ ≤ |R' - (|airyZero k|)| := Finset.inf'_le _ (Finset.mem_Ico.mpr ⟨hk1, hkK⟩)
  have hz_norm : ‖(airyZero k : ℂ)‖ = |airyZero k| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have htri : |R' - (|airyZero k|)| ≤ ‖z - (airyZero k : ℂ)‖ := by
    rw [← hz_norm, ← hz]
    exact abs_norm_sub_norm_le z (airyZero k : ℂ)
  exact hinf.trans htri

private lemma tendsto_one_div_add_four :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 4)) atTop (𝓝 0) := by
  have h : (fun n : ℕ => 1 / ((n : ℝ) + 4)) = fun n : ℕ => 1 / (((n + 3 : ℕ) : ℝ) + 1) := by
    funext n; push_cast; ring
  rw [h]
  exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 3)

private lemma tendsto_airyProdTailExcept_disp_sphere (s : ℕ) (hs : 2 ≤ s) (e_s R' : ℝ)
    (hR' : ∀ k : ℕ, 1 ≤ k → R' ≠ |airyZero k|) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ z : ℂ, ‖z‖ = R' →
      ‖airyProdTailExcept 1 s (dispSite (s + n) (dispE s e_s))
        (designWidthU (s + n) (1 / ((n : ℝ) + 4))) z - 1‖ ≤ ε := by
  have hη0 : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 4) := fun _ => by positivity
  have hη1 : ∀ n : ℕ, 1 / ((n : ℝ) + 4) ≤ (1 / 4 : ℝ) := fun n => by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < n + 4)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨K₀, hK₀2, hK₀⟩ := airyZero_abs_ge_of_large R'
  obtain ⟨δ, hδpos, hδ_bd⟩ := sphere_dist_min K₀ hK₀2 R' hR'
  obtain ⟨C_Z, hC_Z, hZ_bd⟩ := deltaWKB_le_exists
  let C_g : ℝ := (2 / 3 : ℝ) * kappaAiry * (4 / 3 : ℝ) ^ (1 / 3 : ℝ)
  have hCg_pos : 0 < C_g := by dsimp [C_g]; have := kappaAiry_pos; positivity
  have hgapWKB : ∀ k : ℕ, 1 ≤ k → gapWKB k ≤ C_g * (k : ℝ) ^ (-(1 / 3 : ℝ)) :=
    fun k hk => gapWKB_le_mul_rpow hk
  have hsum2 : Summable (fun m : ℕ => 1 / ((m : ℝ) + 2) ^ 2) := by
    have h := (summable_nat_add_iff 2).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
    simpa [one_div, add_comm] using h
  set Z₂ : ℝ := ∑' m : ℕ, 1 / ((m : ℝ) + 2) ^ 2
  set C_tail : ℝ := 2 * C_Z + C_Z ^ 2 + (C_g / 4) ^ 2
  have hC_tail_nn : 0 ≤ C_tail := by positivity
  let tailSum : ℕ → ℝ := fun N =>
    (∑' m : ℕ, C_tail * (1 / ((m : ℝ) + 2) ^ 2)) - ∑ m ∈ Finset.range N, C_tail * (1 / ((m : ℝ) + 2) ^ 2)
  have htail_sum_tend : Tendsto tailSum atTop (𝓝 0) := by
    have hsumC : Summable (fun m : ℕ => C_tail * (1 / ((m : ℝ) + 2) ^ 2)) := hsum2.mul_left C_tail
    have h0 := hsumC.hasSum.tendsto_sum_nat
    have h1 : Tendsto (fun N : ℕ => (∑' m : ℕ, C_tail * (1 / ((m : ℝ) + 2) ^ 2)) -
        ∑ m ∈ Finset.range N, C_tail * (1 / ((m : ℝ) + 2) ^ 2)) atTop
        (𝓝 ((∑' m : ℕ, C_tail * (1 / ((m : ℝ) + 2) ^ 2)) - ∑' m : ℕ, C_tail * (1 / ((m : ℝ) + 2) ^ 2))) :=
      Tendsto.sub tendsto_const_nhds h0
    simpa only [sub_self] using h1
  let B : ℕ → ℝ := fun n =>
    (1 / ((n : ℝ) + 4)) ^ 2 * (K₀ * (C_g ^ 2 / δ ^ 2) + C_g ^ 2 * Z₂) + tailSum (s + n - 1)
  have hB_tend : Tendsto B atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 4)) ^ 2 * (K₀ * (C_g ^ 2 / δ ^ 2) + C_g ^ 2 * Z₂))
        atTop (𝓝 0) := by
      have := (tendsto_one_div_add_four.pow 2).mul_const (K₀ * (C_g ^ 2 / δ ^ 2) + C_g ^ 2 * Z₂)
      simpa using this
    have h2 : Tendsto (fun n : ℕ => tailSum (s + n - 1)) atTop (𝓝 0) := by
      have hfn : (fun n : ℕ => tailSum (s + n - 1)) = fun n : ℕ => tailSum (n + (s - 1)) := by
        funext n; congr 1; omega
      rw [hfn]
      exact htail_sum_tend.comp (tendsto_add_atTop_nat (s - 1))
    have hsum_t : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 4)) ^ 2 * (K₀ * (C_g ^ 2 / δ ^ 2) + C_g ^ 2 * Z₂) +
        tailSum (s + n - 1)) atTop (𝓝 (0 + 0)) := h1.add h2
    simpa only [zero_add] using hsum_t
  have hexp_tend : Tendsto (fun n : ℕ => Real.exp (B n) - 1) atTop (𝓝 0) := by
    have h := (Real.continuous_exp.continuousAt.tendsto.comp hB_tend).sub
      (tendsto_const_nhds (x := (1 : ℝ)))
    rw [Real.exp_zero, sub_self] at h
    exact h
  intro ε hε
  have hlt_exp : ∀ᶠ n : ℕ in atTop, Real.exp (B n) - 1 < ε :=
    hexp_tend.eventually (Iio_mem_nhds hε)
  filter_upwards [eventually_ge_atTop K₀, hlt_exp] with n hnK hexp z hzR
  set η := 1 / ((n : ℝ) + 4)
  set N := s + n
  set uSite := dispSite N (dispE s e_s)
  set epsU := designWidthU N η
  have hH := dispTailHyp s e_s N (hη0 n) (hη1 n)
  have hne : ∀ k : ℕ, 1 < k → k ≠ s → z ≠ (airyZero k : ℂ) := fun k hk _ heq => by
    have h1 : R' = |airyZero k| := by rw [← hzR, heq, Complex.norm_real, Real.norm_eq_abs]
    exact hR' k (by omega) h1
  have hp := hasProd_airyProdTailExcept hH hne
  let term : ℕ → ℂ := fun m => if 2 + m = s then 1 else airyProdFactor uSite epsU (2 + m) z
  have hp' : HasProd term (airyProdTailExcept 1 s uSite epsU z) := by
    simpa only [term, show ∀ m, 1 + 1 + m = 2 + m by intro m; omega] using hp
  let maj : ℕ → ℝ := fun m =>
    (if m < K₀ then η ^ 2 * (C_g ^ 2 / δ ^ 2) else 0) +
    η ^ 2 * C_g ^ 2 * (1 / ((m : ℝ) + 2) ^ 2) +
    (if N - 1 ≤ m then C_tail * (1 / ((m : ℝ) + 2) ^ 2) else 0)
  have hs1 : Summable (fun m : ℕ => if m < K₀ then η ^ 2 * (C_g ^ 2 / δ ^ 2) else 0) :=
    summable_of_ne_finset_zero (s := Finset.range K₀) fun m hm => by
      rw [Finset.mem_range, not_lt] at hm; simp [not_lt.mpr hm]
  have hs2 : Summable (fun m : ℕ => η ^ 2 * C_g ^ 2 * (1 / ((m : ℝ) + 2) ^ 2)) := hsum2.mul_left _
  have hs3 : Summable (fun m : ℕ => if N - 1 ≤ m then C_tail * (1 / ((m : ℝ) + 2) ^ 2) else 0) :=
    Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity)
      (fun _ => by split_ifs <;> [exact le_rfl; exact mul_nonneg hC_tail_nn (by positivity)])
      (hsum2.mul_left C_tail)
  have hmaj_sum : Summable maj := (hs1.add hs2).add hs3
  have hpw : ∀ m : ℕ, ‖term m - 1‖ ≤ maj m := by
    intro m
    by_cases hms : 2 + m = s
    · simp only [term, hms, ↓reduceIte, sub_self, norm_zero]
      dsimp [maj]; positivity
    · have hm2 : 2 ≤ 2 + m := by omega
      have hnz : z ≠ (airyZero (2 + m) : ℂ) := hne (2 + m) hm2 hms
      have hfb := airyProdFactor_sub_one_bound uSite epsU (2 + m) hnz
      have hg_k := hgapWKB (2 + m) (by omega)
      have hgk_nn : 0 ≤ gapWKB (2 + m) := (gapWKB_pos (by omega)).le
      by_cases hmN : 2 + m ≤ N
      · have hu_eq : uSite (2 + m) = airyZero (2 + m) := by
          dsimp [uSite, dispSite, designSiteU, dispE]; simp [hmN, hms]
        have he_eq : epsU (2 + m) = η * gapWKB (2 + m) := by
          dsimp [epsU, designWidthU]; simp [hmN]
        have hsub0 : uSite (2 + m) - airyZero (2 + m) = 0 := sub_eq_zero.mpr hu_eq
        have hfb' : ‖term m - 1‖ ≤ (η * gapWKB (2 + m)) ^ 2 / ‖z - (airyZero (2 + m) : ℂ)‖ ^ 2 := by
          dsimp only [term]
          simp only [hms, ↓reduceIte]
          refine hfb.trans_eq ?_
          rw [hsub0, abs_zero, he_eq, abs_of_nonneg (mul_nonneg (hη0 n) hgk_nn)]
          ring
        by_cases hmK : 2 + m < K₀
        · have hd_le : δ ≤ ‖z - (airyZero (2 + m) : ℂ)‖ := hδ_bd (2 + m) (by omega) hmK z hzR
          have hpow : (2 + m : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ 2 + m)) (by norm_num)
          have he_le : η * gapWKB (2 + m) ≤ η * C_g := by
            calc η * gapWKB (2 + m) ≤ η * (C_g * ((2 + m : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) :=
                  mul_le_mul_of_nonneg_left hg_k (hη0 n)
              _ ≤ η * (C_g * 1) := by gcongr; simpa using hpow
              _ = η * C_g := by ring
          have hmK' : m < K₀ := by omega
          have hstep : ‖term m - 1‖ ≤ η ^ 2 * (C_g ^ 2 / δ ^ 2) := by
            calc ‖term m - 1‖ ≤ (η * gapWKB (2 + m)) ^ 2 / ‖z - (airyZero (2 + m) : ℂ)‖ ^ 2 := hfb'
              _ ≤ (η * C_g) ^ 2 / δ ^ 2 := by gcongr
              _ = η ^ 2 * (C_g ^ 2 / δ ^ 2) := by ring
          dsimp [maj]
          simp only [hmK', ↓reduceIte]
          linarith [show 0 ≤ η ^ 2 * C_g ^ 2 * (1 / ((m : ℝ) + 2) ^ 2) from by positivity,
            show 0 ≤ (if N - 1 ≤ m then C_tail * (1 / ((m : ℝ) + 2) ^ 2) else 0) from by split_ifs <;> positivity]
        · have hmK_ge : K₀ ≤ 2 + m := not_lt.mp hmK
          have hnorm_k := (hK₀ (2 + m) hmK_ge z hzR.le).1
          have hk_pos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
          have hnorm_k' : ((m : ℝ) + 2) ^ ((2 : ℝ) / 3) ≤ ‖z - (airyZero (2 + m) : ℂ)‖ := by
            simpa [show ((2 + m : ℕ) : ℝ) = (m : ℝ) + 2 by push_cast; ring] using hnorm_k
          have hsq_den : ((m : ℝ) + 2) ^ ((4 : ℝ) / 3) ≤ ‖z - (airyZero (2 + m) : ℂ)‖ ^ 2 := by
            have hp2 := pow_le_pow_left₀ (by positivity) hnorm_k' 2
            have hrp : (((m : ℝ) + 2) ^ ((2 : ℝ) / 3)) ^ (2 : ℕ) = ((m : ℝ) + 2) ^ ((4 : ℝ) / 3) := by
              rw [← Real.rpow_natCast (((m : ℝ) + 2) ^ ((2 : ℝ) / 3)) 2, ← Real.rpow_mul hk_pos.le]
              norm_num
            rwa [hrp] at hp2
          have he_le : η * gapWKB (2 + m) ≤ η * C_g * ((m : ℝ) + 2) ^ (-(1 / 3 : ℝ)) := by
            have hmul := mul_le_mul_of_nonneg_left hg_k (show (0 : ℝ) ≤ η by dsimp [η]; positivity)
            simpa [show ((2 + m : ℕ) : ℝ) = (m : ℝ) + 2 by push_cast; ring, mul_assoc] using hmul
          have hsq_num : (η * gapWKB (2 + m)) ^ 2 ≤ η ^ 2 * C_g ^ 2 * ((m : ℝ) + 2) ^ (-(2 / 3 : ℝ)) := by
            have hp2 := pow_le_pow_left₀ (mul_nonneg (hη0 n) hgk_nn) he_le 2
            have hrp : (((m : ℝ) + 2) ^ (-(1 / 3 : ℝ))) ^ (2 : ℕ) = ((m : ℝ) + 2) ^ (-(2 / 3 : ℝ)) := by
              rw [← Real.rpow_natCast (((m : ℝ) + 2) ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hk_pos.le]
              norm_num
            calc (η * gapWKB (2 + m)) ^ 2
                ≤ (η * C_g * ((m : ℝ) + 2) ^ (-(1 / 3 : ℝ))) ^ 2 := hp2
              _ = η ^ 2 * C_g ^ 2 * (((m : ℝ) + 2) ^ (-(1 / 3 : ℝ))) ^ (2 : ℕ) := by ring
              _ = η ^ 2 * C_g ^ 2 * ((m : ℝ) + 2) ^ (-(2 / 3 : ℝ)) := by rw [hrp]
          have hdiv_r : ((m : ℝ) + 2) ^ (-(2 / 3 : ℝ)) / ((m : ℝ) + 2) ^ ((4 : ℝ) / 3) =
              1 / ((m : ℝ) + 2) ^ 2 := by
            rw [← Real.rpow_sub hk_pos, show -(2 / 3 : ℝ) - 4 / 3 = -2 by norm_num, Real.rpow_neg hk_pos.le,
              Real.rpow_two, one_div]
          have hstep : ‖term m - 1‖ ≤ η ^ 2 * C_g ^ 2 * (1 / ((m : ℝ) + 2) ^ 2) := by
            calc ‖term m - 1‖ ≤ (η * gapWKB (2 + m)) ^ 2 / ‖z - (airyZero (2 + m) : ℂ)‖ ^ 2 := hfb'
              _ ≤ (η ^ 2 * C_g ^ 2 * ((m : ℝ) + 2) ^ (-(2 / 3 : ℝ))) / ((m : ℝ) + 2) ^ ((4 : ℝ) / 3) := by gcongr
              _ = η ^ 2 * C_g ^ 2 * (1 / ((m : ℝ) + 2) ^ 2) := by rw [← hdiv_r]; ring
          dsimp [maj]
          linarith [show 0 ≤ (if m < K₀ then η ^ 2 * (C_g ^ 2 / δ ^ 2) else 0) from by split_ifs <;> positivity,
            show 0 ≤ (if N - 1 ≤ m then C_tail * (1 / ((m : ℝ) + 2) ^ 2) else 0) from by split_ifs <;> positivity]
      · have hmN_lt : N < 2 + m := not_le.mp hmN
        have hmK_ge : K₀ ≤ 2 + m := by dsimp [N] at hmN_lt; omega
        have hm_ge_N : N - 1 ≤ m := by omega
        have hu_eq : uSite (2 + m) = uWKB (2 + m) := by
          dsimp [uSite, dispSite, designSiteU, dispE]; simp [not_le.mpr hmN_lt, hms]
        have he_eq : epsU (2 + m) = (1 / 4 : ℝ) * gapWKB (2 + m) := by
          dsimp [epsU, designWidthU]; simp [not_le.mpr hmN_lt]
        have hnorm_k := (hK₀ (2 + m) hmK_ge z hzR.le).1
        have hk_pos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
        have hk_ge1 : (1 : ℝ) ≤ (m : ℝ) + 2 := by linarith
        have hnorm_k' : ((m : ℝ) + 2) ^ ((2 : ℝ) / 3) ≤ ‖z - (airyZero (2 + m) : ℂ)‖ := by
          simpa [show ((2 + m : ℕ) : ℝ) = (m : ℝ) + 2 by push_cast; ring] using hnorm_k
        have hZ_m : |uSite (2 + m) - airyZero (2 + m)| ≤ C_Z * ((m : ℝ) + 2) ^ (-(4 / 3 : ℝ)) := by
          rw [hu_eq, abs_sub_comm]
          have := hZ_bd (2 + m) (by omega)
          unfold deltaWKB at this
          simpa [show ((2 + m : ℕ) : ℝ) = (m : ℝ) + 2 by push_cast; ring] using this
        have he_m : |epsU (2 + m)| ≤ (C_g / 4) * ((m : ℝ) + 2) ^ (-(1 / 3 : ℝ)) := by
          rw [he_eq, abs_of_nonneg (mul_nonneg (by norm_num) hgk_nn)]
          calc (1 / 4 : ℝ) * gapWKB (2 + m)
              ≤ (1 / 4 : ℝ) * (C_g * ((2 + m : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) :=
                mul_le_mul_of_nonneg_left hg_k (by norm_num)
            _ = (C_g / 4) * ((m : ℝ) + 2) ^ (-(1 / 3 : ℝ)) := by
                rw [show ((2 + m : ℕ) : ℝ) = (m : ℝ) + 2 by push_cast; ring]; ring
        have h_u1 : 2 * |uSite (2 + m) - airyZero (2 + m)| / ‖z - (airyZero (2 + m) : ℂ)‖ ≤
            2 * C_Z * (1 / ((m : ℝ) + 2) ^ 2) := by
          have hd_r : ((m : ℝ) + 2) ^ (-(4 / 3 : ℝ)) / ((m : ℝ) + 2) ^ ((2 : ℝ) / 3) =
              1 / ((m : ℝ) + 2) ^ 2 := by
            rw [← Real.rpow_sub hk_pos, show -(4 / 3 : ℝ) - 2 / 3 = -2 by norm_num, Real.rpow_neg hk_pos.le,
              Real.rpow_two, one_div]
          calc 2 * |uSite (2 + m) - airyZero (2 + m)| / ‖z - (airyZero (2 + m) : ℂ)‖
              ≤ 2 * (C_Z * ((m : ℝ) + 2) ^ (-(4 / 3 : ℝ))) / ((m : ℝ) + 2) ^ ((2 : ℝ) / 3) := by gcongr
            _ = 2 * C_Z * (1 / ((m : ℝ) + 2) ^ 2) := by rw [← hd_r]; ring
        have h_u2 : |uSite (2 + m) - airyZero (2 + m)| ^ 2 / ‖z - (airyZero (2 + m) : ℂ)‖ ^ 2 ≤
            C_Z ^ 2 * (1 / ((m : ℝ) + 2) ^ 2) := by
          have hpow_z : |uSite (2 + m) - airyZero (2 + m)| ^ 2 ≤
              C_Z ^ 2 * ((m : ℝ) + 2) ^ (-(8 / 3 : ℝ)) := by
            have hp2 := pow_le_pow_left₀ (abs_nonneg _) hZ_m 2
            have hrp : (((m : ℝ) + 2) ^ (-(4 / 3 : ℝ))) ^ (2 : ℕ) = ((m : ℝ) + 2) ^ (-(8 / 3 : ℝ)) := by
              rw [← Real.rpow_natCast (((m : ℝ) + 2) ^ (-(4 / 3 : ℝ))) 2, ← Real.rpow_mul hk_pos.le]
              norm_num
            rw [mul_pow, hrp] at hp2
            exact hp2
          have hpow_d : ((m : ℝ) + 2) ^ ((4 : ℝ) / 3) ≤ ‖z - (airyZero (2 + m) : ℂ)‖ ^ 2 := by
            have hp2 := pow_le_pow_left₀ (by positivity) hnorm_k' 2
            have hrp : (((m : ℝ) + 2) ^ ((2 : ℝ) / 3)) ^ (2 : ℕ) = ((m : ℝ) + 2) ^ ((4 : ℝ) / 3) := by
              rw [← Real.rpow_natCast (((m : ℝ) + 2) ^ ((2 : ℝ) / 3)) 2, ← Real.rpow_mul hk_pos.le]
              norm_num
            rwa [hrp] at hp2
          have hd_r : ((m : ℝ) + 2) ^ (-(8 / 3 : ℝ)) / ((m : ℝ) + 2) ^ ((4 : ℝ) / 3) ≤
              1 / ((m : ℝ) + 2) ^ 2 := by
            rw [← Real.rpow_sub hk_pos, show -(8 / 3 : ℝ) - 4 / 3 = -4 by norm_num,
              show (1 / ((m : ℝ) + 2) ^ 2 : ℝ) = ((m : ℝ) + 2) ^ (-2 : ℝ) by
                rw [Real.rpow_neg hk_pos.le, Real.rpow_two, one_div]]
            exact Real.rpow_le_rpow_of_exponent_le hk_ge1 (by norm_num)
          calc |uSite (2 + m) - airyZero (2 + m)| ^ 2 / ‖z - (airyZero (2 + m) : ℂ)‖ ^ 2
              ≤ (C_Z ^ 2 * ((m : ℝ) + 2) ^ (-(8 / 3 : ℝ))) / ((m : ℝ) + 2) ^ ((4 : ℝ) / 3) := by gcongr
            _ = C_Z ^ 2 * (((m : ℝ) + 2) ^ (-(8 / 3 : ℝ)) / ((m : ℝ) + 2) ^ ((4 : ℝ) / 3)) := by ring
            _ ≤ C_Z ^ 2 * (1 / ((m : ℝ) + 2) ^ 2) := mul_le_mul_of_nonneg_left hd_r (by positivity)
        have h_e2 : |epsU (2 + m)| ^ 2 / ‖z - (airyZero (2 + m) : ℂ)‖ ^ 2 ≤
            (C_g / 4) ^ 2 * (1 / ((m : ℝ) + 2) ^ 2) := by
          have hpow_e : |epsU (2 + m)| ^ 2 ≤ (C_g / 4) ^ 2 * ((m : ℝ) + 2) ^ (-(2 / 3 : ℝ)) := by
            have hp2 := pow_le_pow_left₀ (abs_nonneg _) he_m 2
            have hrp : (((m : ℝ) + 2) ^ (-(1 / 3 : ℝ))) ^ (2 : ℕ) = ((m : ℝ) + 2) ^ (-(2 / 3 : ℝ)) := by
              rw [← Real.rpow_natCast (((m : ℝ) + 2) ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hk_pos.le]
              norm_num
            rw [mul_pow, hrp] at hp2
            exact hp2
          have hpow_d : ((m : ℝ) + 2) ^ ((4 : ℝ) / 3) ≤ ‖z - (airyZero (2 + m) : ℂ)‖ ^ 2 := by
            have hp2 := pow_le_pow_left₀ (by positivity) hnorm_k' 2
            have hrp : (((m : ℝ) + 2) ^ ((2 : ℝ) / 3)) ^ (2 : ℕ) = ((m : ℝ) + 2) ^ ((4 : ℝ) / 3) := by
              rw [← Real.rpow_natCast (((m : ℝ) + 2) ^ ((2 : ℝ) / 3)) 2, ← Real.rpow_mul hk_pos.le]
              norm_num
            rwa [hrp] at hp2
          have hd_r : ((m : ℝ) + 2) ^ (-(2 / 3 : ℝ)) / ((m : ℝ) + 2) ^ ((4 : ℝ) / 3) =
              1 / ((m : ℝ) + 2) ^ 2 := by
            rw [← Real.rpow_sub hk_pos, show -(2 / 3 : ℝ) - 4 / 3 = -2 by norm_num, Real.rpow_neg hk_pos.le,
              Real.rpow_two, one_div]
          calc |epsU (2 + m)| ^ 2 / ‖z - (airyZero (2 + m) : ℂ)‖ ^ 2
              ≤ ((C_g / 4) ^ 2 * ((m : ℝ) + 2) ^ (-(2 / 3 : ℝ))) / ((m : ℝ) + 2) ^ ((4 : ℝ) / 3) := by gcongr
            _ = (C_g / 4) ^ 2 * (1 / ((m : ℝ) + 2) ^ 2) := by rw [← hd_r]; ring
        have hstep : ‖term m - 1‖ ≤ C_tail * (1 / ((m : ℝ) + 2) ^ 2) := by
          have hadd := add_div (|uSite (2 + m) - airyZero (2 + m)| ^ 2) (|epsU (2 + m)| ^ 2)
            (‖z - (airyZero (2 + m) : ℂ)‖ ^ 2)
          calc ‖term m - 1‖
              ≤ 2 * |uSite (2 + m) - airyZero (2 + m)| / ‖z - (airyZero (2 + m) : ℂ)‖ +
                  (|uSite (2 + m) - airyZero (2 + m)| ^ 2 + |epsU (2 + m)| ^ 2) /
                    ‖z - (airyZero (2 + m) : ℂ)‖ ^ 2 := by simpa [term, hms] using hfb
            _ ≤ 2 * C_Z * (1 / ((m : ℝ) + 2) ^ 2) +
                  (C_Z ^ 2 * (1 / ((m : ℝ) + 2) ^ 2) + (C_g / 4) ^ 2 * (1 / ((m : ℝ) + 2) ^ 2)) := by
                rw [hadd]; exact add_le_add h_u1 (add_le_add h_u2 h_e2)
            _ = C_tail * (1 / ((m : ℝ) + 2) ^ 2) := by dsimp [C_tail]; ring
        dsimp [maj]
        simp only [hm_ge_N, ↓reduceIte]
        linarith [show 0 ≤ (if m < K₀ then η ^ 2 * (C_g ^ 2 / δ ^ 2) else 0) from by split_ifs <;> positivity,
          show 0 ≤ η ^ 2 * C_g ^ 2 * (1 / ((m : ℝ) + 2) ^ 2) from by positivity]
  have hsum_term : Summable (fun m => ‖term m - 1‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpw hmaj_sum
  have hmaj_le : ∑' m : ℕ, maj m ≤ B n := by
    have htsum_eq : ∑' m : ℕ, maj m =
        (∑' m : ℕ, if m < K₀ then η ^ 2 * (C_g ^ 2 / δ ^ 2) else 0) +
        (∑' m : ℕ, η ^ 2 * C_g ^ 2 * (1 / ((m : ℝ) + 2) ^ 2)) +
        (∑' m : ℕ, if N - 1 ≤ m then C_tail * (1 / ((m : ℝ) + 2) ^ 2) else 0) := by
      simp_rw [maj]
      rw [(hs1.add hs2).tsum_add hs3, hs1.tsum_add hs2]
    have hpart1 : ∑' m : ℕ, (if m < K₀ then η ^ 2 * (C_g ^ 2 / δ ^ 2) else 0) =
        (K₀ : ℝ) * (η ^ 2 * (C_g ^ 2 / δ ^ 2)) := by
      rw [tsum_eq_sum (s := Finset.range K₀)]
      · rw [Finset.sum_ite_of_true (fun m hm => Finset.mem_range.mp hm)]
        simp
      · intro m hm; rw [Finset.mem_range, not_lt] at hm; simp [not_lt.mpr hm]
    have hpart2 : ∑' m : ℕ, η ^ 2 * C_g ^ 2 * (1 / ((m : ℝ) + 2) ^ 2) =
        η ^ 2 * (C_g ^ 2 * Z₂) := by
      rw [tsum_mul_left]; dsimp [Z₂]; ring
    have hpart3 : ∑' m : ℕ, (if N - 1 ≤ m then C_tail * (1 / ((m : ℝ) + 2) ^ 2) else 0) =
        tailSum (N - 1) := by
      let M := N - 1
      have hev : (fun m : ℕ => if M ≤ m then C_tail * (1 / ((m : ℝ) + 2) ^ 2) else 0) =
          fun m => if m < M then 0 else C_tail * (1 / ((m : ℝ) + 2) ^ 2) := by
        ext m; by_cases hm : M ≤ m <;> simp [hm]
      have hsa : Summable (fun m : ℕ => if m < M then C_tail * (1 / ((m : ℝ) + 2) ^ 2) else 0) :=
        summable_of_ne_finset_zero (s := Finset.range M) fun m hm => by
          rw [Finset.mem_range] at hm; simp [hm]
      have hsb : Summable (fun m : ℕ => if m < M then 0 else C_tail * (1 / ((m : ℝ) + 2) ^ 2)) := by
        simpa only [← hev] using hs3
      have hadd2 : (∑' m : ℕ, if m < M then C_tail * (1 / ((m : ℝ) + 2) ^ 2) else 0) +
          (∑' m : ℕ, if m < M then 0 else C_tail * (1 / ((m : ℝ) + 2) ^ 2)) =
          ∑' m : ℕ, C_tail * (1 / ((m : ℝ) + 2) ^ 2) := by
        rw [← hsa.tsum_add hsb]
        refine tsum_congr fun m => by split_ifs <;> ring
      have hfin1 : (∑' m : ℕ, if m < M then C_tail * (1 / ((m : ℝ) + 2) ^ 2) else 0) =
          ∑ m ∈ Finset.range M, C_tail * (1 / ((m : ℝ) + 2) ^ 2) := by
        rw [tsum_eq_sum (s := Finset.range M)]
        · refine Finset.sum_congr rfl fun m hm => ?_; simp [Finset.mem_range.mp hm]
        · intro m hm; rw [Finset.mem_range, not_lt] at hm; simp [not_lt.mpr hm]
      rw [hev]
      dsimp [tailSum]
      linarith
    rw [htsum_eq, hpart1, hpart2, hpart3]
    dsimp [B, η, N]
    linarith
  exact (norm_tprod_sub_one_le hp' hsum_term ((hsum_term.tsum_le_tsum hpw hmaj_sum).trans hmaj_le)).trans
    hexp.le

private lemma airyProdTail_split_except (f n : ℕ) (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis f uSite epsU)
    {u : ℂ} (hfn : f < n) (hu : ∀ k : ℕ, f < k → u ≠ (airyZero k : ℂ)) :
    airyProdTail f uSite epsU u = airyProdFactor uSite epsU n u * airyProdTailExcept f n uSite epsU u := by
  have hp := hasProd_airyProdTail hH hu
  have hpe := hasProd_airyProdTailExcept (n := n) hH fun k hk _ => hu k hk
  let m0 := n - (f + 1)
  have hm0 : f + 1 + m0 = n := by omega
  have hev : ∀ᶠ S : Finset ℕ in atTop,
      ∏ m ∈ S, airyProdFactor uSite epsU (f + 1 + m) u =
        airyProdFactor uSite epsU n u *
          ∏ m ∈ S, (if f + 1 + m = n then 1 else airyProdFactor uSite epsU (f + 1 + m) u) := by
    refine eventually_atTop.2 ⟨{m0}, fun S hS => ?_⟩
    have hmS : m0 ∈ S := hS (Finset.mem_singleton_self m0)
    rw [← Finset.mul_prod_erase S _ hmS]
    congr 1
    · rw [hm0]
    · rw [← Finset.mul_prod_erase S _ hmS]
      have h1 : (if f + 1 + m0 = n then (1 : ℂ) else airyProdFactor uSite epsU (f + 1 + m0) u) = 1 := by
        simp [hm0]
      rw [h1, one_mul]
      refine Finset.prod_congr rfl fun m hm => ?_
      have hne : m ≠ m0 := (Finset.mem_erase.mp hm).1
      have hne2 : f + 1 + m ≠ n := by omega
      simp [hne2]
  exact tendsto_nhds_unique hp ((hpe.const_mul _).congr' (hev.mono fun _ h => h.symm))

/-- Local uniform convergence on `ℂ` of the displaced profile products `profW` to `W_ideal`. -/
theorem profWin_disp_tendstoLocallyUniformly_C (s : ℕ) (hs : 2 ≤ s) (b uF : ℝ)
    (W_ideal : ℂ → ℂ) (hW_diff : Differentiable ℂ W_ideal)
    (hW_eq : ∀ z : ℂ, (∀ k : ℕ, 1 ≤ k → z ≠ (airyZero k : ℂ)) →
      W_ideal z = ((z - (b : ℂ)) / (z - (airyZero s : ℂ))) ^ 2 *
        ((z - (uF : ℂ)) / (z - (airyZero 1 : ℂ))) * ShellHBData.airy.G z) :
    TendstoLocallyUniformly (fun n : ℕ => profW (dispSite (s + n) (dispE s (b - airyZero s)))
      (designWidthU (s + n) (1 / ((n : ℝ) + 4))) (airyZero 1 - uF)) W_ideal atTop := by
  have hη0 : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 4) := fun _ => by positivity
  have hη1 : ∀ n : ℕ, 1 / ((n : ℝ) + 4) ≤ (1 / 4 : ℝ) := fun n => by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < n + 4)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  let e_s : ℝ := b - airyZero s
  let d : ℝ := airyZero 1 - uF
  let W_n : ℕ → ℂ → ℂ := fun n =>
    profW (dispSite (s + n) (dispE s e_s)) (designWidthU (s + n) (1 / ((n : ℝ) + 4))) d
  have huF_eq : airyZero 1 - d = uF := by dsimp [d]; ring
  have hW_n_diff : ∀ n : ℕ, Differentiable ℂ (W_n n) := fun n =>
    profW_differentiable _ _ (dispTailHyp s e_s (s + n) (hη0 n) (hη1 n)) d
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨R', hRR', hR'⟩ := exists_radius_avoid_airyZero (max R 0 + 1)
  have hR'_pos : 0 < R' := lt_of_le_of_lt (by positivity) hRR'
  have hK_sub : K ⊆ ball (0 : ℂ) R' := fun z hz => by
    rw [mem_ball_zero_iff]
    exact (hR z hz).trans_lt (by linarith [le_max_left R 0])
  have hne_sp : ∀ z : ℂ, ‖z‖ = R' → ∀ k : ℕ, 1 ≤ k → z ≠ (airyZero k : ℂ) := by
    intro z hz k hk heq
    exact hR' k hk (by rw [← hz, heq, Complex.norm_real, Real.norm_eq_abs])
  have hne_ball : ∀ n : ℕ, ∀ z : ℂ, ‖z‖ = R' →
      let uSite := dispSite (s + n) (dispE s e_s)
      let epsU := designWidthU (s + n) (1 / ((n : ℝ) + 4))
      W_n n z - W_ideal z =
        ((z - (uF : ℂ)) / (z - (airyZero 1 : ℂ))) * ShellHBData.airy.G z *
          (airyProdFactor uSite epsU s z * airyProdTailExcept 1 s uSite epsU z -
            ((z - (b : ℂ)) / (z - (airyZero s : ℂ))) ^ 2) := by
    intro n z hz uSite epsU
    have hnz := hne_sp z hz
    have hH := dispTailHyp s e_s (s + n) (hη0 n) (hη1 n)
    have hWn : W_n n z = airyWindowProd 1 uF uSite epsU z := by
      dsimp [W_n, profW]; rw [huF_eq]
    rw [hWn, airyWindowProd_eq_of_ne 1 uF uSite epsU hnz,
      airyProdTail_split_except 1 s uSite epsU hH (by omega) (fun k hk => hnz k (by omega))]
    have hGprod := ShellHBData.airy.G_prod_eq z
    have hGeq : -airyAiC z ^ 2 / (z - (airyZero 1 : ℂ)) = ShellHBData.airy.G z := by
      have hpr : at47_pr ShellHBData.airy.S z = z - (airyZero 1 : ℂ) := by
        unfold at47_pr; simp [ShellHBData.airy]
      have hAi : airyPQN ShellHBData.airy.P ShellHBData.airy.Q z = airyAiC z := by
        unfold airyPQN
        simp only [ShellHBData.airy]
        rw [airyPQc_zero, zero_mul, add_zero]
        have h1c : airyPQc (1 : ℝ[X]) z = 1 := by
          rw [← Polynomial.C_1]; exact airyPQc_C (1 : ℝ) z
        rw [h1c, one_mul]
      have hcard : ShellHBData.airy.S.card = 1 := by simp [ShellHBData.airy]
      rw [hpr, hAi, hcard] at hGprod
      have h1 : z - (airyZero 1 : ℂ) ≠ 0 := sub_ne_zero.mpr (hnz 1 le_rfl)
      apply mul_right_cancel₀ h1
      rw [div_mul_cancel₀ _ h1, hGprod]
      push_cast; ring
    have hfac1 : -airyAiC z ^ 2 * (z - (uF : ℂ)) /
          (∏ k ∈ Finset.Icc 1 1, (z - (airyZero k : ℂ)) ^ 2) =
        ((z - (uF : ℂ)) / (z - (airyZero 1 : ℂ))) * ShellHBData.airy.G z := by
      rw [Finset.Icc_self, Finset.prod_singleton, ← hGeq]
      have h1 : z - (airyZero 1 : ℂ) ≠ 0 := sub_ne_zero.mpr (hnz 1 le_rfl)
      field_simp
    rw [hfac1, hW_eq z hnz]
    ring
  have hpre_bd : ∃ M : ℝ, 0 < M ∧ ∀ z : ℂ, ‖z‖ = R' →
      ‖((z - (uF : ℂ)) / (z - (airyZero 1 : ℂ))) * ShellHBData.airy.G z‖ ≤ M ∧
      ‖((z - (b : ℂ)) / (z - (airyZero s : ℂ))) ^ 2‖ ≤ M := by
    have hcomp : IsCompact (closedBall (0 : ℂ) R') := isCompact_closedBall 0 R'
    have hd1 : 0 < |R' - (|airyZero 1|)| := abs_pos.mpr (sub_ne_zero.mpr (hR' 1 le_rfl))
    have hds : 0 < |R' - (|airyZero s|)| := abs_pos.mpr (sub_ne_zero.mpr (hR' s (by omega)))
    obtain ⟨MG, hMG⟩ := hcomp.exists_bound_of_continuousOn
      ShellHBData.airy.G_diff.continuous.continuousOn
    let M : ℝ := max 1 (max ((R' + |uF|) / |R' - (|airyZero 1|)| * max MG 0)
      (((R' + |b|) / |R' - (|airyZero s|)|) ^ 2))
    refine ⟨M, by positivity, fun z hz => ?_⟩
    have hz_ball : z ∈ closedBall (0 : ℂ) R' := by rw [mem_closedBall_zero_iff]; exact hz.le
    have hG_le : ‖ShellHBData.airy.G z‖ ≤ max MG 0 := (hMG z hz_ball).trans (le_max_left _ _)
    have hd_ge1 : |R' - (|airyZero 1|)| ≤ ‖z - (airyZero 1 : ℂ)‖ := by
      have htri := abs_norm_sub_norm_le z (airyZero 1 : ℂ)
      simpa [hz, Complex.norm_real, Real.norm_eq_abs] using htri
    have hd_ges : |R' - (|airyZero s|)| ≤ ‖z - (airyZero s : ℂ)‖ := by
      have htri := abs_norm_sub_norm_le z (airyZero s : ℂ)
      simpa [hz, Complex.norm_real, Real.norm_eq_abs] using htri
    have hnu : ‖z - (uF : ℂ)‖ ≤ R' + |uF| := by
      have := norm_sub_le z (uF : ℂ)
      simpa [hz, Complex.norm_real, Real.norm_eq_abs] using this
    have hnb : ‖z - (b : ℂ)‖ ≤ R' + |b| := by
      have := norm_sub_le z (b : ℂ)
      simpa [hz, Complex.norm_real, Real.norm_eq_abs] using this
    constructor
    · rw [norm_mul, norm_div]
      calc (‖z - (uF : ℂ)‖ / ‖z - (airyZero 1 : ℂ)‖) * ‖ShellHBData.airy.G z‖
          ≤ ((R' + |uF|) / |R' - (|airyZero 1|)|) * max MG 0 := by gcongr
        _ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    · rw [norm_pow, norm_div]
      have hfrac : ‖z - (b : ℂ)‖ / ‖z - (airyZero s : ℂ)‖ ≤ (R' + |b|) / |R' - (|airyZero s|)| := by
        gcongr
      calc (‖z - (b : ℂ)‖ / ‖z - (airyZero s : ℂ)‖) ^ 2
          ≤ ((R' + |b|) / |R' - (|airyZero s|)|) ^ 2 := by gcongr
        _ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨M, hMpos, hM⟩ := hpre_bd
  have hds : 0 < |R' - (|airyZero s|)| := abs_pos.mpr (sub_ne_zero.mpr (hR' s (by omega)))
  have hε_tail : 0 < ε / (4 * M * (M + 1)) := by positivity
  have h_ex := tendsto_airyProdTailExcept_disp_sphere s hs e_s R' hR' (min 1 (ε / (4 * M * (M + 1))))
    (lt_min one_pos hε_tail)
  have h_ηs : ∀ᶠ n : ℕ in atTop,
      ((1 / ((n : ℝ) + 4)) * gapWKB s) ^ 2 / |R' - (|airyZero s|)| ^ 2 ≤ ε / (8 * M) := by
    have h1 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 4)) * gapWKB s) ^ 2 / |R' - (|airyZero s|)| ^ 2)
        atTop (𝓝 0) := by
      have := ((tendsto_one_div_add_four.mul_const (gapWKB s)).pow 2).div_const (|R' - (|airyZero s|)| ^ 2)
      simpa using this
    exact h1.eventually (eventually_le_nhds (by positivity))
  filter_upwards [h_ex, h_ηs] with n hn_ex hn_ηs z hzK
  have hbd_sp : ∀ w : ℂ, w ∈ frontier (ball (0 : ℂ) R') → ‖W_n n w - W_ideal w‖ ≤ ε / 2 := by
    intro w hw
    rw [frontier_ball (0 : ℂ) hR'_pos.ne', mem_sphere_zero_iff_norm] at hw
    rw [hne_ball n w hw, norm_mul]
    set uSite := dispSite (s + n) (dispE s e_s)
    set epsU := designWidthU (s + n) (1 / ((n : ℝ) + 4))
    have h_f_sub : airyProdFactor uSite epsU s w - ((w - (b : ℂ)) / (w - (airyZero s : ℂ))) ^ 2 =
        ((epsU s : ℂ) ^ 2) / (w - (airyZero s : ℂ)) ^ 2 := by
      have hus : uSite s = b := by dsimp [uSite, dispSite, designSiteU, dispE, e_s]; simp
      unfold airyProdFactor; rw [hus]
      have hnz : w - (airyZero s : ℂ) ≠ 0 := sub_ne_zero.mpr (hne_sp w hw s (by omega))
      field_simp; ring
    have heps_s : epsU s = (1 / ((n : ℝ) + 4)) * gapWKB s := by dsimp [epsU, designWidthU]; simp
    have hd_ges : |R' - (|airyZero s|)| ≤ ‖w - (airyZero s : ℂ)‖ := by
      have htri := abs_norm_sub_norm_le w (airyZero s : ℂ)
      simpa [hw, Complex.norm_real, Real.norm_eq_abs] using htri
    have hfnorm : ‖airyProdFactor uSite epsU s w - ((w - (b : ℂ)) / (w - (airyZero s : ℂ))) ^ 2‖ ≤
        ε / (8 * M) := by
      rw [h_f_sub, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, heps_s, sq_abs]
      calc ((1 / ((n : ℝ) + 4)) * gapWKB s) ^ 2 / ‖w - (airyZero s : ℂ)‖ ^ 2
          ≤ ((1 / ((n : ℝ) + 4)) * gapWKB s) ^ 2 / |R' - (|airyZero s|)| ^ 2 := by gcongr
        _ ≤ ε / (8 * M) := hn_ηs
    have hex1 : ‖airyProdTailExcept 1 s uSite epsU w - 1‖ ≤ min 1 (ε / (4 * M * (M + 1))) :=
      hn_ex w hw
    have hex_le1 : ‖airyProdTailExcept 1 s uSite epsU w‖ ≤ 2 := by
      have h2 := norm_sub_norm_le (airyProdTailExcept 1 s uSite epsU w) 1
      have h3 := hex1.trans (min_le_left _ _)
      rw [norm_one] at h2
      linarith
    have hsplit : airyProdFactor uSite epsU s w * airyProdTailExcept 1 s uSite epsU w -
          ((w - (b : ℂ)) / (w - (airyZero s : ℂ))) ^ 2 =
        (airyProdFactor uSite epsU s w - ((w - (b : ℂ)) / (w - (airyZero s : ℂ))) ^ 2) *
          airyProdTailExcept 1 s uSite epsU w +
        ((w - (b : ℂ)) / (w - (airyZero s : ℂ))) ^ 2 *
          (airyProdTailExcept 1 s uSite epsU w - 1) := by ring
    have hterm2 : ‖((w - (b : ℂ)) / (w - (airyZero s : ℂ))) ^ 2 *
          (airyProdTailExcept 1 s uSite epsU w - 1)‖ ≤ M * (ε / (4 * M * (M + 1))) := by
      rw [norm_mul]
      exact mul_le_mul (hM w hw).2 (hex1.trans (min_le_right _ _)) (norm_nonneg _) hMpos.le
    have hM_mul : M * (ε / (4 * M * (M + 1))) ≤ ε / (4 * M) := by
      have : M * (ε / (4 * M * (M + 1))) = (ε / (4 * M)) * (M / (M + 1)) := by field_simp
      rw [this]
      exact mul_le_of_le_one_right (by positivity) ((div_le_one (by linarith)).2 (by linarith))
    have hprod_le : ‖airyProdFactor uSite epsU s w * airyProdTailExcept 1 s uSite epsU w -
          ((w - (b : ℂ)) / (w - (airyZero s : ℂ))) ^ 2‖ ≤ ε / (2 * M) := by
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      have hterm1 : ‖(airyProdFactor uSite epsU s w - ((w - (b : ℂ)) / (w - (airyZero s : ℂ))) ^ 2) *
            airyProdTailExcept 1 s uSite epsU w‖ ≤ (ε / (8 * M)) * 2 := by
        rw [norm_mul]; exact mul_le_mul hfnorm hex_le1 (norm_nonneg _) (by positivity)
      have hdiv2 : (ε / (8 * M)) * 2 + ε / (4 * M) = ε / (2 * M) := by field_simp; ring
      linarith
    have hfin_le : ‖((w - (uF : ℂ)) / (w - (airyZero 1 : ℂ))) * ShellHBData.airy.G w‖ *
          ‖airyProdFactor uSite epsU s w * airyProdTailExcept 1 s uSite epsU w -
            ((w - (b : ℂ)) / (w - (airyZero s : ℂ))) ^ 2‖ ≤ M * (ε / (2 * M)) :=
      mul_le_mul (hM w hw).1 hprod_le (norm_nonneg _) hMpos.le
    have hM2 : M * (ε / (2 * M)) = ε / 2 := by field_simp
    linarith
  have hdc : DiffContOnCl ℂ (fun w => W_n n w - W_ideal w) (ball (0 : ℂ) R') :=
    ((hW_n_diff n).sub hW_diff).differentiableOn.diffContOnCl
  have hle := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc hbd_sp
    (subset_closure (hK_sub hzK))
  rw [dist_eq_norm, norm_sub_rev]
  exact hle.trans_lt (by linarith)

private lemma abs_profPi_le (uSite epsU : ℕ → ℝ) (d : ℝ) {m : ℕ} (_hm : 2 ≤ m)
    (h0 : 0 ≤ profPi0 uSite epsU m) :
    |profPi uSite epsU d m| ≤ profPi uSite epsU (-|d|) m := by
  unfold profPi
  rw [abs_mul, abs_of_nonneg h0]
  refine mul_le_mul_of_nonneg_left ?_ h0
  have h1 : |1 - d / (|airyZero m - airyZero 1|)| ≤ 1 + |d| / |airyZero m - airyZero 1| := by
    calc |1 - d / (|airyZero m - airyZero 1|)|
        ≤ |1| + |d / (|airyZero m - airyZero 1|)| := abs_sub _ _
      _ = 1 + |d| / |airyZero m - airyZero 1| := by rw [abs_one, abs_div, abs_abs]
  rw [neg_div, sub_neg_eq_add]
  exact h1

/-- Convergence of the quadrature sums `(D n).V` to `∫ u, (W_ideal (u : ℂ)).re`. -/
theorem profWin_disp_V_tendsto (s : ℕ) (hs : 2 ≤ s) (b uF : ℝ) (W_ideal : ℂ → ℂ)
    (hW_cl : InAiryClass W_ideal)
    (hW_eq : ∀ z : ℂ, (∀ k : ℕ, 1 ≤ k → z ≠ (airyZero k : ℂ)) →
      W_ideal z = ((z - (b : ℂ)) / (z - (airyZero s : ℂ))) ^ 2 *
        ((z - (uF : ℂ)) / (z - (airyZero 1 : ℂ))) * ShellHBData.airy.G z)
    (hW_zeros : ∀ n : ℕ, n ≠ 0 → n ≠ s - 1 → (W_ideal (airyNode n : ℂ)).re = 0) :
    let e := dispE s (b - airyZero s)
    let η : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 4)
    let D : ℕ → Window := fun n =>
      profWin (dispSite (s + n) e) (designWidthU (s + n) (η n))
        (dispTailHyp s (b - airyZero s) (s + n) (by positivity)
          (by rw [div_le_iff₀ (by positivity : (0 : ℝ) < n + 4)]; linarith [Nat.cast_nonneg (α := ℝ) n]))
        (fun k hk => by
          unfold designWidthU
          exact mul_ne_zero (by split_ifs <;> positivity) (gapWKB_pos (by omega)).ne')
        (airyZero 1 - uF)
    Tendsto (fun n => (D n).V) atTop (𝓝 (∫ u : ℝ, (W_ideal (u : ℂ)).re)) := by
  intro e η D
  have hη0 : ∀ n : ℕ, 0 ≤ η n := fun _ => by positivity
  have hη1 : ∀ n : ℕ, η n ≤ 1 / 4 := fun n => by
    dsimp [η]; rw [div_le_iff₀ (by positivity : (0 : ℝ) < n + 4)]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hloc := profWin_disp_tendstoLocallyUniformly_C s hs b uF W_ideal hW_cl.1 hW_eq
  have ht_pt : ∀ x : ℝ, Tendsto (fun n : ℕ => (D n).W x) atTop (𝓝 (W_ideal (x : ℂ)).re) := fun x => by
    have htC : Tendsto (fun n : ℕ => profW (dispSite (s + n) (dispE s (b - airyZero s)))
        (designWidthU (s + n) (1 / ((n : ℝ) + 4))) (airyZero 1 - uF) (x : ℂ)) atTop (𝓝 (W_ideal (x : ℂ))) := by
      rw [tendstoLocallyUniformly_iff_forall_isCompact] at hloc
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.1
        (Metric.tendstoUniformlyOn_iff.mp (hloc {(x : ℂ)} isCompact_singleton) ε hε)
      exact ⟨N, fun n hn => by simpa [dist_comm] using hN n hn (x : ℂ) (mem_singleton _)⟩
    exact Complex.continuous_re.continuousAt.tendsto.comp htC
  have ht_pi0 : Tendsto (fun n : ℕ => (D n).pi 0) atTop
      (𝓝 ((W_ideal (airyZero 1 : ℂ)).re * airyNodeWeight 0)) := by
    have h0 : ∀ n : ℕ, (D n).pi 0 = (D n).W (airyNode 0) * airyNodeWeight 0 := fun _ => rfl
    simp_rw [h0]
    exact (ht_pt (airyNode 0)).mul_const (airyNodeWeight 0)
  have ht_pis : Tendsto (fun n : ℕ => (D n).pi (s - 1)) atTop
      (𝓝 ((W_ideal (airyZero s : ℂ)).re * airyNodeWeight (s - 1))) := by
    have hs1 : airyNode (s - 1) = airyZero s := by
      show airyZero (s - 1 + 1) = airyZero s; rw [Nat.sub_add_cancel (by omega)]
    have h0 : ∀ n : ℕ, (D n).pi (s - 1) = (D n).W (airyNode (s - 1)) * airyNodeWeight (s - 1) :=
      fun _ => rfl
    simp_rw [h0, hs1]
    exact (ht_pt (airyZero s)).mul_const (airyNodeWeight (s - 1))
  have hrest_tend : Tendsto (fun n : ℕ =>
      ∑' j : ℕ, if j + 2 = s then 0 else
        profPi (dispSite (s + n) e) (designWidthU (s + n) (η n)) (airyZero 1 - uF) (j + 2))
      atTop (𝓝 0) := by
    obtain ⟨B, hBpos, hB⟩ := exists_dispRest_le_D ({s} : Finset ℕ) e
      (fun k hk => dispE_of_ne (b - airyZero s) (by simpa using hk))
      (|airyZero 1 - uF|) (abs_nonneg _)
    have hmaj_tend : Tendsto (fun n : ℕ => B * (η n ^ 2 + ((s + n : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))))
        atTop (𝓝 0) := by
      have h1 : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_four
      have h2 : Tendsto (fun n : ℕ => ((s + n : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
        have hfn : (fun n : ℕ => ((s + n : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) =
            fun n => (((n + s : ℕ) : ℝ)) ^ (-(1 / 3 : ℝ)) := by
          funext n; rw [add_comm]
        rw [hfn]
        exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat s))
      have h3 := (h1.pow 2).add h2
      simpa using h3.const_mul B
    have hmaj_bd : ∀ n : ℕ, |∑' j : ℕ, if j + 2 = s then 0 else
        profPi (dispSite (s + n) e) (designWidthU (s + n) (η n)) (airyZero 1 - uF) (j + 2)| ≤
        B * (η n ^ 2 + ((s + n : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) := by
      intro n
      have hH := dispTailHyp s (b - airyZero s) (s + n) (hη0 n) (hη1 n)
      obtain ⟨hsum_nn, htsum_nn⟩ := hB (s + n) (by omega) (η n) (hη0 n) (hη1 n)
      have hsum_abs : Summable (fun j : ℕ => if j + 2 = s then 0 else
          |profPi (dispSite (s + n) e) (designWidthU (s + n) (η n)) (airyZero 1 - uF) (j + 2)|) := by
        refine Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity) (fun j => ?_) hsum_nn
        by_cases hjs : j + 2 = s <;> simp [hjs, Finset.mem_singleton]
        exact abs_profPi_le _ _ (airyZero 1 - uF) (by omega) (profPi0_nonneg _ _ hH (by omega))
      have h1 : |∑' j : ℕ, if j + 2 = s then 0 else
            profPi (dispSite (s + n) e) (designWidthU (s + n) (η n)) (airyZero 1 - uF) (j + 2)| ≤
          ∑' j : ℕ, |if j + 2 = s then 0 else
            profPi (dispSite (s + n) e) (designWidthU (s + n) (η n)) (airyZero 1 - uF) (j + 2)| := by
        have hsum_norm : Summable (fun j : ℕ => ‖if j + 2 = s then (0 : ℝ) else
            profPi (dispSite (s + n) e) (designWidthU (s + n) (η n)) (airyZero 1 - uF) (j + 2)‖) := by
          convert hsum_abs using 1; ext j; split_ifs <;> simp [Real.norm_eq_abs]
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsum_norm
      have h2 : ∑' j : ℕ, |if j + 2 = s then 0 else
            profPi (dispSite (s + n) e) (designWidthU (s + n) (η n)) (airyZero 1 - uF) (j + 2)| ≤
          ∑' j : ℕ, if j + 2 ∈ ({s} : Finset ℕ) then 0 else
            profPi (dispSite (s + n) e) (designWidthU (s + n) (η n)) (-|airyZero 1 - uF|) (j + 2) := by
        refine Summable.tsum_le_tsum (fun j => ?_) ?_ hsum_nn
        · by_cases hjs : j + 2 = s <;> simp [hjs, Finset.mem_singleton]
          exact abs_profPi_le _ _ (airyZero 1 - uF) (by omega) (profPi0_nonneg _ _ hH (by omega))
        · convert hsum_abs using 1; ext j; split_ifs <;> simp
      exact (h1.trans h2).trans htsum_nn
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hmaj_tend.neg) hmaj_tend
      (fun n => (abs_le.mp (hmaj_bd n)).1) (fun n => (abs_le.mp (hmaj_bd n)).2)
  have hquad : (W_ideal (airyZero 1 : ℂ)).re * airyNodeWeight 0 +
      (W_ideal (airyZero s : ℂ)).re * airyNodeWeight (s - 1) =
      ∫ u : ℝ, (W_ideal (u : ℂ)).re := by
    have ht := hbZeroEnum_spec ShellHBData.airy
    have hq := hb_real_quadrature ShellHBData.airy ht hW_cl
    have hts : ∫ u : ℝ, (W_ideal (u : ℂ)).re =
        ∑ m ∈ ({0, s - 1} : Finset ℕ),
          airyPQDr ShellHBData.airy.P ShellHBData.airy.Q (hbZeroEnum ShellHBData.airy m) *
            (W_ideal (hbZeroEnum ShellHBData.airy m : ℂ)).re /
              ((airyPQN' ShellHBData.airy.P ShellHBData.airy.Q (hbZeroEnum ShellHBData.airy m : ℂ)).re) ^ 2 := by
      rw [← hq.tsum_eq, tsum_eq_sum]
      intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      rw [hbZeroEnum_airy_eq m, hW_zeros m hm.1 hm.2, mul_zero, zero_div]
    rw [hts, Finset.sum_pair (by omega : (0 : ℕ) ≠ s - 1)]
    have h0' : hbZeroEnum ShellHBData.airy 0 = airyZero 1 := by rw [hbZeroEnum_airy_eq 0]; rfl
    have hs' : hbZeroEnum ShellHBData.airy (s - 1) = airyZero s := by
      rw [hbZeroEnum_airy_eq (s - 1)]; show airyZero (s - 1 + 1) = airyZero s; rw [Nat.sub_add_cancel (by omega)]
    rw [h0', hs']
    have hw0 := hbQuadWeight_airy_eq 0
    have hws := hbQuadWeight_airy_eq (s - 1)
    unfold hbQuadWeight at hw0 hws
    have hnode0 : airyNode 0 = airyZero 1 := rfl
    have hnodes : airyNode (s - 1) = airyZero s := by
      show airyZero (s - 1 + 1) = airyZero s; rw [Nat.sub_add_cancel (by omega)]
    rw [hnode0] at hw0
    rw [hnodes] at hws
    rw [← hw0, ← hws]
    ring
  have hsum_split : ∀ n : ℕ, (D n).V = (D n).pi 0 + (D n).pi (s - 1) +
      ∑' j : ℕ, if j + 2 = s then 0 else
        profPi (dispSite (s + n) e) (designWidthU (s + n) (η n)) (airyZero 1 - uF) (j + 2) := by
    intro n
    rw [← (D n).tsum_pi, (D n).summable_pi.tsum_eq_zero_add]
    have hs_succ : Summable (fun j : ℕ => (D n).pi (j + 1)) :=
      (summable_nat_add_iff 1).mpr (D n).summable_pi
    have hite : (D n).pi (s - 1) + ∑' j : ℕ, (if j + 2 = s then 0 else (D n).pi (j + 1)) =
        ∑' j : ℕ, (D n).pi (j + 1) := by
      have h1 := hs_succ.tsum_eq_add_tsum_ite (s - 2)
      have heq_ite : (fun j : ℕ => if j = s - 2 then 0 else (D n).pi (j + 1)) =
          fun j : ℕ => if j + 2 = s then 0 else (D n).pi (j + 1) := by
        ext j; congr 1; exact propext (by omega : j = s - 2 ↔ j + 2 = s)
      have hs1 : s - 2 + 1 = s - 1 := by omega
      rw [hs1, heq_ite] at h1
      exact h1.symm
    rw [← hite]
    dsimp [D]
    simp_rw [profWin_pi_succ]
    ring
  simp_rw [hsum_split]
  have hlim := (ht_pi0.add ht_pis).add hrest_tend
  rw [add_zero, hquad] at hlim
  exact hlim

end FormalResearch.ModularBootstrap.FoldTip
