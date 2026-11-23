module

public import FormalResearch.Special.AiryCftQuadrature
public import FormalResearch.Complex.HadamardAiry
public import FormalResearch.Special.AiryZeroSecondOrder
public import FormalResearch.ModularBootstrap.Constants

/-!
# Airy Window Product and Lemma G (`upper_transfer.tex`, `ut:G`)

Formalizes the Airy-window coordinates, Lemma Z glue, the general-$f$ Airy product `W^{(f)}(u)`,
the design $D(N, \eta_*, d)$ product `W(u)`, the $u$-variable gap summation lemma, and **Lemma G**
(`ut:G`, `upper_transfer.tex` lines 573--581):

* `kappaAiry`, `phiWKB`, `uWKB`, `sNodeAiry`, `deltaWKB`, `gapWKB`, `airyGap`.
* `airyGap_kernel_sum`: $\sum_{k \ge 1} \mathrm{gap}_k^2 / |u - a_k|^2 \le C(c_0)$ uniformly for
  $u \in \mathbb{C}$ satisfying $|u - a_k| \ge c_0\,\mathrm{gap}_k$ for all $k \ge 1$.
* `airyWindowProd`: entire Airy product $W^{(f)}(u)$ for arbitrary $f \ge 1$ and finite
  modifications of the WKB reference sites and widths, defined with removable singularities at
  the Airy zeros $a_n$ so that it is globally entire and evaluates directly at $a_n$.
* `designWindowW`: the $f = 1$ design product $W(u)$ for $D(N, \eta_*, d)$.
* **Lemma G (`ut:G`)**: `designWindowW_differentiable`, `designWindowW_im_eq_zero`,
  `lemma_G_bound` ($\|W(u)\| \le C (1 + \|u\|)^{-3/2} e(u)$), `lemma_G_integrable`
  ($W \in L^1(\mathbb{R})$), and `lemma_G_circle_ratio` ($\|W(u) / \Ai(u)^2\| \le C / \|u\|$).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Window

open FormalResearch.Special

/-! ### Section 1: Airy window parameters and Lemma Z glue -/

/-- Airy window scaling parameter $\kappa = (3\pi / 2)^{2/3}$. -/
noncomputable def kappaAiry : ℝ := (3 * π / 2) ^ (2 / 3 : ℝ)

/-- WKB phase coordinate $\Phi_k = (k - 1/4)^{2/3}$. -/
noncomputable def phiWKB (k : ℕ) : ℝ := ((k : ℝ) - 1 / 4) ^ (2 / 3 : ℝ)

/-- WKB Airy zero approximation $u_k^W = -\kappa \Phi_k$. -/
noncomputable def uWKB (k : ℕ) : ℝ := -kappaAiry * phiWKB k

/-- Scaled Airy zero $s_k = |a_k| / \kappa$. -/
noncomputable def sNodeAiry (k : ℕ) : ℝ := |airyZero k| / kappaAiry

/-- WKB displacement $\delta_k = a_k - u_k^W$. -/
noncomputable def deltaWKB (k : ℕ) : ℝ := airyZero k - uWKB k

/-- WKB gap $\Delta_k = u_k^W - u_{k+1}^W$. -/
noncomputable def gapWKB (k : ℕ) : ℝ := uWKB k - uWKB (k + 1)

/-- Airy zero gap $\mathrm{gap}_k = a_k - a_{k+1}$. -/
noncomputable def airyGap (k : ℕ) : ℝ := airyZero k - airyZero (k + 1)

lemma kappaAiry_pos : 0 < kappaAiry := by
  unfold kappaAiry; positivity

lemma four_thirds_kappaAiry_rpow : (4 / 3 : ℝ) * kappaAiry ^ (3 / 2 : ℝ) = 2 * π := by
  unfold kappaAiry
  have hpi : 0 < 3 * π / 2 := by positivity
  rw [← Real.rpow_mul hpi.le, show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one]
  ring

lemma uWKB_eq_neg_airyZeroT {k : ℕ} (hk : 1 ≤ k) :
    uWKB k = -airyZeroT k ^ (2 / 3 : ℝ) := by
  unfold uWKB kappaAiry phiWKB airyZeroT
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 / 4 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [neg_mul, ← Real.mul_rpow (by positivity) hk1]

lemma deltaWKB_eq {k : ℕ} (hk : 1 ≤ k) :
    deltaWKB k = airyZero k + airyZeroT k ^ (2 / 3 : ℝ) := by
  unfold deltaWKB
  rw [uWKB_eq_neg_airyZeroT hk]
  ring

lemma sNodeAiry_sub_phiWKB {k : ℕ} (_hk : 1 ≤ k) :
    sNodeAiry k - phiWKB k = -deltaWKB k / kappaAiry := by
  unfold sNodeAiry deltaWKB uWKB
  rw [abs_of_neg (airyZero_neg k)]
  have hκ : kappaAiry ≠ 0 := kappaAiry_pos.ne'
  field_simp
  ring

/-- **Lemma Z (`ut:Z`)**: WKB displacement bound $|\delta_k| \le C k^{-4/3}$ for all $k \ge 1$. -/
theorem deltaWKB_le_exists :
    ∃ C > 0, ∀ k : ℕ, 1 ≤ k → |deltaWKB k| ≤ C * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ := airyZero_delta_exists
  refine ⟨max C₀ 1, by positivity, fun k hk => ?_⟩
  rw [deltaWKB_eq hk]
  have hk0 : 0 ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
  exact (hC₀ k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hk0)

/-- Lower and upper bounds on the WKB gap $\Delta_k = u_k^W - u_{k+1}^W$ for $k \ge 1$. -/
theorem gapWKB_bounds {k : ℕ} (hk : 1 ≤ k) :
    (2 / 3 : ℝ) * kappaAiry * ((k : ℝ) + 3 / 4) ^ (-(1 / 3 : ℝ)) ≤ gapWKB k ∧
      gapWKB k ≤ (2 / 3 : ℝ) * kappaAiry * ((k : ℝ) - 1 / 4) ^ (-(1 / 3 : ℝ)) := by
  unfold gapWKB uWKB phiWKB
  have hκ : 0 < kappaAiry := kappaAiry_pos
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set a : ℝ := (k : ℝ) - 1 / 4
  set b : ℝ := (k : ℝ) + 3 / 4
  have ha : 0 < a := by dsimp [a]; linarith
  have hb_eq : b = ((k + 1 : ℕ) : ℝ) - 1 / 4 := by dsimp [b]; push_cast; ring
  have hab : a < b := by dsimp [a, b]; linarith
  have hgap : -kappaAiry * a ^ (2 / 3 : ℝ) - -kappaAiry * (((k + 1 : ℕ) : ℝ) - 1 / 4) ^ (2 / 3 : ℝ) =
      kappaAiry * (b ^ (2 / 3 : ℝ) - a ^ (2 / 3 : ℝ)) := by
    rw [hb_eq]; ring
  rw [hgap]
  have hcont : ContinuousOn (fun t : ℝ => t ^ (2 / 3 : ℝ)) (Icc a b) :=
    continuousOn_id.rpow_const fun t ht => Or.inl (lt_of_lt_of_le ha ht.1).ne'
  have hdiff : ∀ t ∈ Ioo a b, HasDerivAt (fun x : ℝ => x ^ (2 / 3 : ℝ))
      ((2 / 3 : ℝ) * t ^ (-(1 / 3 : ℝ))) t := fun t ht => by
    have ht0 : 0 < t := lt_trans ha ht.1
    simpa [show (2 / 3 : ℝ) - 1 = -(1 / 3 : ℝ) by norm_num] using
      (hasDerivAt_id t).rpow_const (p := (2 / 3 : ℝ)) (Or.inl ht0.ne')
  obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (2 / 3 : ℝ))
    (fun t => (2 / 3 : ℝ) * t ^ (-(1 / 3 : ℝ))) hab hcont hdiff
  have hba : b - a = 1 := by dsimp [a, b]; ring
  have hslope : b ^ (2 / 3 : ℝ) - a ^ (2 / 3 : ℝ) = (2 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ)) := by
    rw [eq_div_iff (sub_ne_zero.mpr hab.ne'), hba, mul_one] at hmv
    exact hmv.symm
  rw [hslope]
  have hc_pos : 0 < c := lt_trans ha hc.1
  have hc_le : b ^ (-(1 / 3 : ℝ)) ≤ c ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hc_pos hc.2.le (by norm_num)
  have ha_ge : c ^ (-(1 / 3 : ℝ)) ≤ a ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ha hc.1.le (by norm_num)
  constructor <;> nlinarith

lemma gapWKB_pos {k : ℕ} (hk : 1 ≤ k) : 0 < gapWKB k := by
  have h1 := (gapWKB_bounds hk).1
  have hκ := kappaAiry_pos
  have hk0 : (0 : ℝ) < (k : ℝ) + 3 / 4 := by positivity
  exact lt_of_lt_of_le (by positivity) h1

lemma gapWKB_le_mul_rpow {k : ℕ} (hk : 1 ≤ k) :
    gapWKB k ≤ (2 / 3 : ℝ) * kappaAiry * (4 / 3 : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have h2 := (gapWKB_bounds hk).2
  have hκ := kappaAiry_pos
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha_ge : (3 / 4 : ℝ) * k ≤ (k : ℝ) - 1 / 4 := by linarith
  have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (3 / 4 : ℝ) * k)
    ha_ge (by norm_num : -(1 / 3 : ℝ) ≤ 0)
  have hmul : ((3 / 4 : ℝ) * k) ^ (-(1 / 3 : ℝ)) = (4 / 3 : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity),
      show (3 / 4 : ℝ) ^ (-(1 / 3 : ℝ)) = ((3 / 4 : ℝ)⁻¹) ^ (1 / 3 : ℝ) by
        rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)],
      show (3 / 4 : ℝ)⁻¹ = 4 / 3 by norm_num]
  rw [hmul] at hpow
  nlinarith

lemma airyGap_pos {k : ℕ} (hk : 1 ≤ k) : 0 < airyGap k := by
  unfold airyGap
  linarith [airyZero_strictAnti hk]

/-- Uniform lower and upper bounds on $\mathrm{gap}_k = a_k - a_{k+1}$ for all $k \ge 1$. -/
theorem airyGap_bounds_exists :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 1 ≤ k →
      c₁ * (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ airyGap k ∧ airyGap k ≤ c₂ * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
  refine ⟨min (9 / 5 * (1 / 2 : ℝ) ^ (1 / 3 : ℝ)) (airyGap 1), max (41 / 20) (airyGap 1), ?_, ?_, fun k hk => ?_⟩
  · exact lt_min (by positivity) (airyGap_pos le_rfl)
  · exact lt_max_of_lt_left (by norm_num)
  · rcases hk.eq_or_lt with rfl | hk2
    · simp only [Nat.cast_one, Real.one_rpow, mul_one]
      exact ⟨min_le_right _ _, le_max_right _ _⟩
    · obtain ⟨hl, hu⟩ := airyZero_gap_bounds hk2
      have hl' : (9 / 5 : ℝ) * ((k : ℝ) + 1) ^ (-(1 / 3 : ℝ)) ≤ airyGap k := by
        unfold airyGap; linarith
      have hu' : airyGap k ≤ (41 / 20 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
        unfold airyGap; linarith
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have h2k : (k : ℝ) + 1 ≤ 2 * k := by linarith
      have hpow : (2 * (k : ℝ)) ^ (-(1 / 3 : ℝ)) ≤ ((k : ℝ) + 1) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h2k (by norm_num)
      have h2eq : (2 * (k : ℝ)) ^ (-(1 / 3 : ℝ)) = (1 / 2 : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity),
          show (2 : ℝ) ^ (-(1 / 3 : ℝ)) = (1 / 2 : ℝ) ^ (1 / 3 : ℝ) by
            rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num), one_div]; norm_num]
      rw [h2eq] at hpow
      have hkpow : 0 ≤ (k : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
      constructor
      · calc min (9 / 5 * (1 / 2 : ℝ) ^ (1 / 3 : ℝ)) (airyGap 1) * (k : ℝ) ^ (-(1 / 3 : ℝ))
            ≤ (9 / 5 * (1 / 2 : ℝ) ^ (1 / 3 : ℝ)) * (k : ℝ) ^ (-(1 / 3 : ℝ)) :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) hkpow
          _ = 9 / 5 * ((1 / 2 : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ))) := by ring
          _ ≤ 9 / 5 * ((k : ℝ) + 1) ^ (-(1 / 3 : ℝ)) := mul_le_mul_of_nonneg_left hpow (by norm_num)
          _ ≤ airyGap k := hl'
      · exact hu'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hkpow)

lemma gapWKB_le_mul_airyGap :
    ∃ C > 0, ∀ k : ℕ, 1 ≤ k → gapWKB k ≤ C * airyGap k := by
  obtain ⟨c₁, _, hc₁, _, hgap⟩ := airyGap_bounds_exists
  set C := (2 / 3 : ℝ) * kappaAiry * (4 / 3 : ℝ) ^ (1 / 3 : ℝ) / c₁
  have hκ := kappaAiry_pos
  refine ⟨C, by positivity, fun k hk => ?_⟩
  have h1 := gapWKB_le_mul_rpow hk
  have h2 := (hgap k hk).1
  have hC : C * c₁ = (2 / 3 : ℝ) * kappaAiry * (4 / 3 : ℝ) ^ (1 / 3 : ℝ) := by
    dsimp [C]; field_simp [hc₁.ne']
  calc gapWKB k ≤ (2 / 3 : ℝ) * kappaAiry * (4 / 3 : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := h1
    _ = C * (c₁ * (k : ℝ) ^ (-(1 / 3 : ℝ))) := by rw [← hC]; ring
    _ ≤ C * airyGap k := mul_le_mul_of_nonneg_left h2 (by positivity)

/-! ### Section 2: The $u$-variable gap summation lemma -/

private lemma rpow_neg_two_thirds_partial_sum (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, ((k : ℝ) ^ (-(2 / 3 : ℝ))) ≤ 3 * (M : ℝ) ^ (1 / 3 : ℝ) := by
  induction M with
  | zero => simp
  | succ m ih =>
    have h1 : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [h1, Finset.sum_insert (by simp)]
    rcases m.eq_zero_or_pos with rfl | hm
    · simp
    · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      have h_mvt : 3 * ((m : ℝ) + 1) ^ (1 / 3 : ℝ) - 3 * (m : ℝ) ^ (1 / 3 : ℝ) ≥
          ((m + 1 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) := by
        have hcont : ContinuousOn (fun t : ℝ => t ^ (1 / 3 : ℝ)) (Icc (m : ℝ) ((m : ℝ) + 1)) :=
          continuousOn_id.rpow_const fun t ht => Or.inl (lt_of_lt_of_le hm0 ht.1).ne'
        have hdiff : ∀ t ∈ Ioo (m : ℝ) ((m : ℝ) + 1),
            HasDerivAt (fun x : ℝ => x ^ (1 / 3 : ℝ)) ((1 / 3 : ℝ) * t ^ (-(2 / 3 : ℝ))) t := fun t ht => by
          have ht0 : 0 < t := lt_trans hm0 ht.1
          have hd := (hasDerivAt_id' t).rpow_const (p := (1 / 3 : ℝ)) (Or.inl ht0.ne')
          rw [show (1 / 3 : ℝ) * t ^ (-(2 / 3 : ℝ)) = 1 * (1 / 3 : ℝ) * t ^ ((1 / 3 : ℝ) - 1) by
            rw [one_mul, show (1 / 3 : ℝ) - 1 = -(2 / 3 : ℝ) by norm_num]]
          exact hd
        obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (1 / 3 : ℝ))
          (fun t => (1 / 3 : ℝ) * t ^ (-(2 / 3 : ℝ))) (by linarith) hcont hdiff
        rw [show (m : ℝ) + 1 - m = 1 by ring, div_one] at hmv
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        have hpow : ((m + 1 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(2 / 3 : ℝ)) := by
          rw [hcast]
          exact Real.rpow_le_rpow_of_nonpos (lt_trans hm0 hc.1) hc.2.le (by norm_num)
        linarith
      calc ((m + 1 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) + ∑ k ∈ Finset.Icc 1 m, (k : ℝ) ^ (-(2 / 3 : ℝ))
          ≤ (3 * ((m : ℝ) + 1) ^ (1 / 3 : ℝ) - 3 * (m : ℝ) ^ (1 / 3 : ℝ)) + 3 * (m : ℝ) ^ (1 / 3 : ℝ) :=
            add_le_add h_mvt ih
        _ = 3 * ((m + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) := by push_cast; ring

/-- **Summation lemma (`ut:G`)**: for any $c_0 > 0$, there is $C(c_0) > 0$ such that for every
$u \in \mathbb{C}$ satisfying $\|u - a_k\| \ge c_0\,\mathrm{gap}_k$ for all $k \ge 1$,
$\sum_{k \ge 1} \mathrm{gap}_k^2 / \|u - a_k\|^2 \le C(c_0)$ (and the series is summable). -/
theorem airyGap_kernel_sum {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C > 0, ∀ u : ℂ,
      (∀ k : ℕ, 1 ≤ k → c₀ * airyGap k ≤ ‖u - (airyZero k : ℂ)‖) →
      Summable (fun k : ℕ => airyGap (k + 1) ^ 2 / ‖u - (airyZero (k + 1) : ℂ)‖ ^ 2) ∧
      ∑' k : ℕ, airyGap (k + 1) ^ 2 / ‖u - (airyZero (k + 1) : ℂ)‖ ^ 2 ≤ C := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hgap⟩ := airyGap_bounds_exists
  set Z : ℝ := ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ 2
  have hZs : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  have hZ0 : 0 ≤ Z := tsum_nonneg fun _ => by positivity
  set C₁ : ℝ := c₂ * (2 : ℝ) ^ (1 / 3 : ℝ) / (9 / 10 : ℝ)
  set C₂ : ℝ := 3 * c₂ ^ 2 / (9 / 20 : ℝ) ^ 2
  set C := 1 / c₀ ^ 2 + 2 * C₁ ^ 2 * Z + C₂
  refine ⟨C, by positivity, fun u hu => ?_⟩
  have hsep_ev : ∃ K : ℕ, 1 ≤ K ∧ ∀ k : ℕ, K ≤ k → ‖u - (airyZero 1 : ℂ)‖ ≤ ‖u - (airyZero k : ℂ)‖ := by
    have hlim : Tendsto (fun k : ℕ => -airyZero k) atTop atTop := by
      have h_ref : Tendsto (fun k : ℕ => (5 / 2 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ)) atTop atTop :=
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
          tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
      refine tendsto_atTop_mono' atTop ?_ h_ref
      filter_upwards [eventually_ge_atTop 2] with k hk
      have h1 := (airyZero_abs_bounds hk).1
      linarith
    have hnorm : Tendsto (fun k : ℕ => ‖u - (airyZero k : ℂ)‖) atTop atTop := by
      have hge : ∀ k : ℕ, -airyZero k - ‖u‖ ≤ ‖u - (airyZero k : ℂ)‖ := fun k => by
        have h1 := norm_sub_norm_le ((airyZero k : ℂ)) u
        rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (airyZero_neg k)] at h1
        exact h1
      exact tendsto_atTop_mono hge (hlim.atTop_add tendsto_const_nhds)
    obtain ⟨K₀, hK₀⟩ := (hnorm.eventually (eventually_ge_atTop ‖u - (airyZero 1 : ℂ)‖)).exists_forall_of_atTop
    exact ⟨max K₀ 1, le_max_right _ _, fun k hk => hK₀ k (le_trans (le_max_left _ _) hk)⟩
  obtain ⟨K, hK1, hK_ge⟩ := hsep_ev
  obtain ⟨kstar, hkstar_mem, hkstar_min⟩ :=
    (Finset.Icc 1 K).exists_min_image (fun k => ‖u - (airyZero k : ℂ)‖) ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hK1⟩⟩
  have hkstar1 : 1 ≤ kstar := (Finset.mem_Icc.mp hkstar_mem).1
  have hkstar_all : ∀ k : ℕ, 1 ≤ k → ‖u - (airyZero kstar : ℂ)‖ ≤ ‖u - (airyZero k : ℂ)‖ := by
    intro k hk
    by_cases hle : k ≤ K
    · exact hkstar_min k (Finset.mem_Icc.mpr ⟨hk, hle⟩)
    · have h1 := hkstar_min 1 (Finset.mem_Icc.mpr ⟨le_rfl, hK1⟩)
      exact h1.trans (hK_ge k (by omega))
  have hterm_le : ∀ k : ℕ, 1 ≤ k →
      airyGap k ^ 2 / ‖u - (airyZero k : ℂ)‖ ^ 2 ≤
        (if k = kstar then 1 / c₀ ^ 2 else 0) +
        (if k ≠ kstar ∧ kstar ≤ 2 * k then C₁ ^ 2 / ((k : ℝ) - kstar) ^ 2 else 0) +
        (if 2 * k < kstar then (c₂ ^ 2 / (9 / 20 : ℝ) ^ 2) * (kstar : ℝ) ^ (-(4 / 3 : ℝ)) * (k : ℝ) ^ (-(2 / 3 : ℝ)) else 0) := by
    intro k hk
    have hgap_k := hgap k hk
    have hden_pos : 0 < ‖u - (airyZero k : ℂ)‖ :=
      lt_of_lt_of_le (mul_pos hc₀ (airyGap_pos hk)) (hu k hk)
    by_cases hkk : k = kstar
    · subst hkk
      have hnot_lt : ¬(2 * k < k) := by omega
      simp only [ite_true, ne_eq, not_true_eq_false, false_and, ite_false, hnot_lt, add_zero]
      have h1 : airyGap k ≤ ‖u - (airyZero k : ℂ)‖ / c₀ := by
        rw [le_div_iff₀ hc₀, mul_comm]; exact hu k hk
      have h2 : airyGap k ^ 2 ≤ ‖u - (airyZero k : ℂ)‖ ^ 2 / c₀ ^ 2 := by
        have := pow_le_pow_left₀ (airyGap_pos hk).le h1 2
        rwa [div_pow] at this
      rw [div_le_iff₀ (sq_pos_of_pos hden_pos)]
      calc airyGap k ^ 2 ≤ ‖u - (airyZero k : ℂ)‖ ^ 2 / c₀ ^ 2 := h2
        _ = 1 / c₀ ^ 2 * ‖u - (airyZero k : ℂ)‖ ^ 2 := by ring
    · have hdist : |airyZero k - airyZero kstar| ≤ 2 * ‖u - (airyZero k : ℂ)‖ := by
        have htri := norm_sub_le ((airyZero kstar : ℂ) - u) ((airyZero k : ℂ) - u)
        have heq : (airyZero kstar : ℂ) - u - ((airyZero k : ℂ) - u) = ((airyZero kstar - airyZero k : ℝ) : ℂ) := by
          push_cast; ring
        rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at htri
        have hmin := hkstar_all k hk
        rw [norm_sub_rev] at htri
        rw [norm_sub_rev (airyZero k : ℂ) u] at htri
        linarith
      have hsep := airyZero_abs_sub_ge hk hkstar1 hkk
      rw [abs_sub_comm (airyZero kstar) (airyZero k), abs_sub_comm (kstar : ℝ) k, max_comm] at hsep
      have hsep' : (9 / 10 : ℝ) * |(k : ℝ) - kstar| * ((max k kstar : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) ≤
          ‖u - (airyZero k : ℂ)‖ := by
        linarith
      have hkstar_pos : (0 : ℝ) < kstar := by exact_mod_cast (by omega : 0 < kstar)
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      by_cases hmid : kstar ≤ 2 * k
      · have hne_mid : k ≠ kstar ∧ kstar ≤ 2 * k := ⟨hkk, hmid⟩
        have hlt_false : ¬(2 * k < kstar) := by omega
        simp only [if_neg hkk, if_pos hne_mid, if_neg hlt_false, zero_add, add_zero]
        have hmax_le : ((max k kstar : ℕ) : ℝ) ≤ 2 * k := by
          have : max k kstar ≤ 2 * k := max_le (by omega) hmid
          exact_mod_cast this
        have hmax_pow : (2 * (k : ℝ)) ^ (-(1 / 3 : ℝ)) ≤ ((max k kstar : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hmax_le (by norm_num)
        have h2eq : (2 * (k : ℝ)) ^ (-(1 / 3 : ℝ)) = (1 / 2 : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
          rw [Real.mul_rpow (by norm_num) hk_pos.le,
            show (2 : ℝ) ^ (-(1 / 3 : ℝ)) = (1 / 2 : ℝ) ^ (1 / 3 : ℝ) by
              rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num), one_div]; norm_num]
        rw [h2eq] at hmax_pow
        have h_abs_pos : (0 : ℝ) < |(k : ℝ) - kstar| := abs_pos.mpr (by
          intro h0; apply hkk; exact_mod_cast sub_eq_zero.mp h0)
        have h_lb : (9 / 10 : ℝ) * |(k : ℝ) - kstar| * ((1 / 2 : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ))) ≤
            ‖u - (airyZero k : ℂ)‖ := by
          have := mul_le_mul_of_nonneg_left hmax_pow (by positivity : 0 ≤ (9 / 10 : ℝ) * |(k : ℝ) - kstar|)
          exact this.trans hsep'
        have hratio : airyGap k / ‖u - (airyZero k : ℂ)‖ ≤ C₁ / |(k : ℝ) - kstar| := by
          rw [div_le_div_iff₀ hden_pos h_abs_pos]
          have hC1_eq : C₁ * (9 / 10 : ℝ) * (1 / 2 : ℝ) ^ (1 / 3 : ℝ) = c₂ := by
            dsimp [C₁]
            have h2p : (2 : ℝ) ^ (1 / 3 : ℝ) * (1 / 2 : ℝ) ^ (1 / 3 : ℝ) = 1 := by
              rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
            calc c₂ * (2 : ℝ) ^ (1 / 3 : ℝ) / (9 / 10 : ℝ) * (9 / 10 : ℝ) * (1 / 2 : ℝ) ^ (1 / 3 : ℝ)
                = c₂ * ((2 : ℝ) ^ (1 / 3 : ℝ) * (1 / 2 : ℝ) ^ (1 / 3 : ℝ)) := by ring
              _ = c₂ := by rw [h2p, mul_one]
          calc airyGap k * |(k : ℝ) - kstar|
              ≤ (c₂ * (k : ℝ) ^ (-(1 / 3 : ℝ))) * |(k : ℝ) - kstar| := mul_le_mul_of_nonneg_right hgap_k.2 h_abs_pos.le
            _ = C₁ * ((9 / 10 : ℝ) * |(k : ℝ) - kstar| * ((1 / 2 : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)))) := by
                rw [← hC1_eq]; ring
            _ ≤ C₁ * ‖u - (airyZero k : ℂ)‖ := mul_le_mul_of_nonneg_left h_lb (by positivity)
        have hsq := pow_le_pow_left₀ (div_nonneg (airyGap_pos hk).le hden_pos.le) hratio 2
        rw [div_pow, div_pow, sq_abs] at hsq
        exact hsq
      · have hlt : 2 * k < kstar := by omega
        have hnot_mid : ¬(k ≠ kstar ∧ kstar ≤ 2 * k) := fun h => hlt.not_ge h.2
        simp only [if_neg hkk, if_neg hnot_mid, if_pos hlt, zero_add]
        have hmax_eq : max k kstar = kstar := max_eq_right (by omega)
        rw [hmax_eq] at hsep'
        have hkdiff : (kstar : ℝ) / 2 ≤ |(k : ℝ) - kstar| := by
          have hk_lt : (k : ℝ) < (kstar : ℝ) / 2 := by
            have : (2 * k : ℝ) < kstar := by exact_mod_cast hlt
            linarith
          rw [abs_of_neg (by linarith)]
          linarith
        have hkstar_pow : 0 < (kstar : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
        have h_lb : (9 / 20 : ℝ) * (kstar : ℝ) ^ (2 / 3 : ℝ) ≤ ‖u - (airyZero k : ℂ)‖ := by
          have h1 : (9 / 20 : ℝ) * (kstar : ℝ) * (kstar : ℝ) ^ (-(1 / 3 : ℝ)) ≤
              (9 / 10 : ℝ) * |(k : ℝ) - kstar| * (kstar : ℝ) ^ (-(1 / 3 : ℝ)) := by
            nlinarith
          have h2 : (kstar : ℝ) * (kstar : ℝ) ^ (-(1 / 3 : ℝ)) = (kstar : ℝ) ^ (2 / 3 : ℝ) := by
            conv_lhs => arg 1; rw [← Real.rpow_one (kstar : ℝ)]
            rw [← Real.rpow_add hkstar_pos]; norm_num
          rw [mul_assoc, h2] at h1
          exact h1.trans hsep'
        have h_lb_sq : (9 / 20 : ℝ) ^ 2 * (kstar : ℝ) ^ (4 / 3 : ℝ) ≤ ‖u - (airyZero k : ℂ)‖ ^ 2 := by
          have hsq := pow_le_pow_left₀ (by positivity) h_lb 2
          rw [mul_pow, ← Real.rpow_natCast ((kstar : ℝ) ^ (2 / 3 : ℝ)) 2, ← Real.rpow_mul hkstar_pos.le,
            show (2 / 3 : ℝ) * ((2 : ℕ) : ℝ) = 4 / 3 by norm_num] at hsq
          exact hsq
        have h_num_le : airyGap k ^ 2 ≤ c₂ ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
          have hsq := pow_le_pow_left₀ (airyGap_pos hk).le hgap_k.2 2
          rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hk_pos.le,
            show -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) by norm_num] at hsq
          exact hsq
        have hkstar43 : (kstar : ℝ) ^ (-(4 / 3 : ℝ)) = ((kstar : ℝ) ^ (4 / 3 : ℝ))⁻¹ :=
          Real.rpow_neg hkstar_pos.le (4 / 3 : ℝ)
        calc airyGap k ^ 2 / ‖u - (airyZero k : ℂ)‖ ^ 2
            ≤ (c₂ ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ))) / ((9 / 20 : ℝ) ^ 2 * (kstar : ℝ) ^ (4 / 3 : ℝ)) := by
              gcongr
          _ = (c₂ ^ 2 / (9 / 20 : ℝ) ^ 2) * (kstar : ℝ) ^ (-(4 / 3 : ℝ)) * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
              rw [hkstar43]; ring
  have hsum_bd : ∀ N : ℕ,
      ∑ m ∈ Finset.range N, airyGap (m + 1) ^ 2 / ‖u - (airyZero (m + 1) : ℂ)‖ ^ 2 ≤ C := by
    intro N
    have h1 : ∑ m ∈ Finset.range N, airyGap (m + 1) ^ 2 / ‖u - (airyZero (m + 1) : ℂ)‖ ^ 2 ≤
        ∑ m ∈ Finset.range N,
          ((if m + 1 = kstar then 1 / c₀ ^ 2 else 0) +
           (if m + 1 ≠ kstar ∧ kstar ≤ 2 * (m + 1) then C₁ ^ 2 / (((m + 1 : ℕ) : ℝ) - kstar) ^ 2 else 0) +
           (if 2 * (m + 1) < kstar then
             (c₂ ^ 2 / (9 / 20 : ℝ) ^ 2) * (kstar : ℝ) ^ (-(4 / 3 : ℝ)) * ((m + 1 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) else 0)) :=
      Finset.sum_le_sum fun m _ => hterm_le (m + 1) (by omega)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h1
    have s1 : ∑ m ∈ Finset.range N, (if m + 1 = kstar then (1 / c₀ ^ 2 : ℝ) else 0) ≤ 1 / c₀ ^ 2 := by
      rw [← Finset.sum_filter]
      have hcard : ((Finset.range N).filter (fun m => m + 1 = kstar)).card ≤ 1 := by
        refine Finset.card_le_one.mpr fun a ha b hb => ?_
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        omega
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_of_le_one_left (by positivity) (by exact_mod_cast hcard)
    have s2 : ∑ m ∈ Finset.range N,
        (if m + 1 ≠ kstar ∧ kstar ≤ 2 * (m + 1) then C₁ ^ 2 / (((m + 1 : ℕ) : ℝ) - kstar) ^ 2 else 0) ≤
        2 * C₁ ^ 2 * Z := by
      set S := (Finset.range N).filter (fun m => m + 1 ≠ kstar ∧ kstar ≤ 2 * (m + 1))
      have hS_eq : ∑ m ∈ Finset.range N,
          (if m + 1 ≠ kstar ∧ kstar ≤ 2 * (m + 1) then C₁ ^ 2 / (((m + 1 : ℕ) : ℝ) - kstar) ^ 2 else 0) =
          C₁ ^ 2 * ∑ m ∈ S, 1 / (((m + 1 : ℕ) : ℝ) - kstar) ^ 2 := by
        rw [← Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => by ring
      rw [hS_eq]
      have hsplit : S = S.filter (fun m => kstar < m + 1) ∪ S.filter (fun m => m + 1 < kstar) := by
        ext m; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hm
          have hne : m + 1 ≠ kstar := by
            have hm' := hm
            dsimp [S] at hm'
            exact (Finset.mem_filter.mp hm').2.1
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact Or.inr ⟨hm, hlt⟩
          · exact Or.inl ⟨hm, hgt⟩
        · rintro (⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm
      have hdisj : Disjoint (S.filter (fun m => kstar < m + 1)) (S.filter (fun m => m + 1 < kstar)) :=
        Finset.disjoint_filter.mpr fun m _ h1 h2 => by omega
      rw [hsplit, Finset.sum_union hdisj]
      have s_hi : ∑ m ∈ S.filter (fun m => kstar < m + 1), 1 / (((m + 1 : ℕ) : ℝ) - kstar) ^ 2 ≤ Z := by
        let φ : ℕ → ℕ := fun m => m + 1 - kstar - 1
        have hinj : Set.InjOn φ (S.filter (fun m => kstar < m + 1)) := by
          intro a ha b hb h
          have ha' := (Finset.mem_filter.mp ha).2
          have hb' := (Finset.mem_filter.mp hb).2
          dsimp [φ] at h
          omega
        have him : ∑ m ∈ S.filter (fun m => kstar < m + 1), 1 / (((m + 1 : ℕ) : ℝ) - kstar) ^ 2 =
            ∑ j ∈ (S.filter (fun m => kstar < m + 1)).image φ, 1 / ((j : ℝ) + 1) ^ 2 := by
          rw [Finset.sum_image hinj]
          refine Finset.sum_congr rfl fun m hm => ?_
          have hm' := (Finset.mem_filter.mp hm).2
          have hcast : ((φ m : ℕ) : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) - kstar := by
            dsimp [φ]
            have h2 : (m + 1 - kstar - 1 + 1 : ℕ) + kstar = m + 1 := by omega
            have h2' : ((m + 1 - kstar - 1 + 1 : ℕ) : ℝ) + (kstar : ℝ) = ((m + 1 : ℕ) : ℝ) := by exact_mod_cast h2
            push_cast at h2' ⊢; linarith
          rw [hcast]
        rw [him]
        exact hZs.sum_le_tsum _ fun _ _ => by positivity
      have s_lo : ∑ m ∈ S.filter (fun m => m + 1 < kstar), 1 / (((m + 1 : ℕ) : ℝ) - kstar) ^ 2 ≤ Z := by
        let ψ : ℕ → ℕ := fun m => kstar - (m + 1) - 1
        have hinj : Set.InjOn ψ (S.filter (fun m => m + 1 < kstar)) := by
          intro a ha b hb h
          have ha' := (Finset.mem_filter.mp ha).2
          have hb' := (Finset.mem_filter.mp hb).2
          dsimp [ψ] at h
          omega
        have him : ∑ m ∈ S.filter (fun m => m + 1 < kstar), 1 / (((m + 1 : ℕ) : ℝ) - kstar) ^ 2 =
            ∑ j ∈ (S.filter (fun m => m + 1 < kstar)).image ψ, 1 / ((j : ℝ) + 1) ^ 2 := by
          rw [Finset.sum_image hinj]
          refine Finset.sum_congr rfl fun m hm => ?_
          have hm' := (Finset.mem_filter.mp hm).2
          have hcast : ((ψ m : ℕ) : ℝ) + 1 = (kstar : ℝ) - ((m + 1 : ℕ) : ℝ) := by
            dsimp [ψ]
            have h2 : (kstar - (m + 1) - 1 + 1 : ℕ) + (m + 1) = kstar := by omega
            have h2' : ((kstar - (m + 1) - 1 + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ) = (kstar : ℝ) := by exact_mod_cast h2
            push_cast at h2' ⊢; linarith
          rw [hcast, show (((m + 1 : ℕ) : ℝ) - kstar) ^ 2 = ((kstar : ℝ) - ((m + 1 : ℕ) : ℝ)) ^ 2 by ring]
        rw [him]
        exact hZs.sum_le_tsum _ fun _ _ => by positivity
      calc C₁ ^ 2 * (∑ m ∈ S.filter (fun m => kstar < m + 1), 1 / (((m + 1 : ℕ) : ℝ) - kstar) ^ 2 +
            ∑ m ∈ S.filter (fun m => m + 1 < kstar), 1 / (((m + 1 : ℕ) : ℝ) - kstar) ^ 2)
          ≤ C₁ ^ 2 * (Z + Z) := mul_le_mul_of_nonneg_left (add_le_add s_hi s_lo) (by positivity)
        _ = 2 * C₁ ^ 2 * Z := by ring
    have s3 : ∑ m ∈ Finset.range N, (if 2 * (m + 1) < kstar then
        (c₂ ^ 2 / (9 / 20 : ℝ) ^ 2) * (kstar : ℝ) ^ (-(4 / 3 : ℝ)) * ((m + 1 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) else 0) ≤ C₂ := by
      rw [← Finset.sum_filter, ← Finset.mul_sum]
      set T := (Finset.range N).filter (fun m => 2 * (m + 1) < kstar)
      have hsub : T.image (fun m => m + 1) ⊆ Finset.Icc 1 kstar := by
        intro x hx
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
        have hm' := (Finset.mem_filter.mp hm).2
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hinj : Set.InjOn (fun m : ℕ => m + 1) T := fun a _ b _ h => Nat.succ.inj h
      have hsum_sub : ∑ m ∈ T, ((m + 1 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) ≤
          ∑ k ∈ Finset.Icc 1 kstar, (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
        rw [← Finset.sum_image (f := fun k : ℕ => (k : ℝ) ^ (-(2 / 3 : ℝ))) hinj]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      have hrp := hsum_sub.trans (rpow_neg_two_thirds_partial_sum kstar)
      have hkstar_pos : (0 : ℝ) < kstar := by exact_mod_cast (by omega : 0 < kstar)
      have hmul_pow : (kstar : ℝ) ^ (-(4 / 3 : ℝ)) * (kstar : ℝ) ^ (1 / 3 : ℝ) = (kstar : ℝ)⁻¹ := by
        rw [← Real.rpow_add hkstar_pos, show -(4 / 3 : ℝ) + 1 / 3 = -1 by norm_num, Real.rpow_neg_one]
      have hkstar_inv : (kstar : ℝ)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]; right; exact_mod_cast hkstar1
      calc (c₂ ^ 2 / (9 / 20 : ℝ) ^ 2) * (kstar : ℝ) ^ (-(4 / 3 : ℝ)) *
            ∑ m ∈ T, ((m + 1 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ))
          ≤ (c₂ ^ 2 / (9 / 20 : ℝ) ^ 2) * (kstar : ℝ) ^ (-(4 / 3 : ℝ)) * (3 * (kstar : ℝ) ^ (1 / 3 : ℝ)) := by
            gcongr
        _ = C₂ * ((kstar : ℝ) ^ (-(4 / 3 : ℝ)) * (kstar : ℝ) ^ (1 / 3 : ℝ)) := by
            dsimp [C₂]; ring
        _ = C₂ * (kstar : ℝ)⁻¹ := by rw [hmul_pow]
        _ ≤ C₂ * 1 := mul_le_mul_of_nonneg_left hkstar_inv (by positivity)
        _ = C₂ := mul_one _
    exact h1.trans (add_le_add (add_le_add s1 s2) s3)
  have hsum : Summable (fun k : ℕ => airyGap (k + 1) ^ 2 / ‖u - (airyZero (k + 1) : ℂ)‖ ^ 2) :=
    summable_of_sum_range_le (fun _ => by positivity) hsum_bd
  exact ⟨hsum, hsum.tsum_le_of_sum_range_le hsum_bd⟩

/-! ### Section 3: The entire Airy product `W^{(f)}(u)` and design product `W(u)` -/

/-- The single factor $\frac{(u - u_k)^2 + \varepsilon_k^2}{(u - a_k)^2}$ in the Airy product. -/
noncomputable def airyProdFactor (uSite epsU : ℕ → ℝ) (k : ℕ) (u : ℂ) : ℂ :=
  (((u - (uSite k : ℂ)) ^ 2 + (epsU k : ℂ) ^ 2) / (u - (airyZero k : ℂ)) ^ 2)

/-- The shifted infinite product $\prod_{k > f} \frac{(u - u_k)^2 + \varepsilon_k^2}{(u - a_k)^2}$. -/
noncomputable def airyProdTail (f : ℕ) (uSite epsU : ℕ → ℝ) (u : ℂ) : ℂ :=
  ∏' m : ℕ, airyProdFactor uSite epsU (f + 1 + m) u

/-- The shifted infinite product omitting index `n` ($k > f, k \ne n$). -/
noncomputable def airyProdTailExcept (f n : ℕ) (uSite epsU : ℕ → ℝ) (u : ℂ) : ℂ :=
  ∏' m : ℕ, if f + 1 + m = n then 1 else airyProdFactor uSite epsU (f + 1 + m) u

open Classical in
/-- The Airy product $W^{(f)}(u) = -\Ai(u)^2 (u - u_f) \frac{\prod_{k > f} ((u - u_k)^2 + \varepsilon_{k,u}^2)}{\prod_{k \ge 1} (u - a_k)^2}$,
defined with explicit removable-singularity values at every Airy zero $u = a_n$ ($n \ge 1$). -/
noncomputable def airyWindowProd (f : ℕ) (uF : ℝ) (uSite epsU : ℕ → ℝ) (u : ℂ) : ℂ :=
  if h : ∃ n : ℕ, 1 ≤ n ∧ u = (airyZero n : ℂ) then
    let n := Nat.find h
    if n ≤ f then
      -(deriv airyAiC (airyZero n : ℂ)) ^ 2 * (u - (uF : ℂ)) /
        (∏ k ∈ (Finset.Icc 1 f).erase n, (u - (airyZero k : ℂ)) ^ 2) *
        airyProdTail f uSite epsU u
    else
      -(deriv airyAiC (airyZero n : ℂ)) ^ 2 * (u - (uF : ℂ)) /
        (∏ k ∈ Finset.Icc 1 f, (u - (airyZero k : ℂ)) ^ 2) *
        ((u - (uSite n : ℂ)) ^ 2 + (epsU n : ℂ) ^ 2) *
        airyProdTailExcept f n uSite epsU u
  else
    -airyAiC u ^ 2 * (u - (uF : ℂ)) /
      (∏ k ∈ Finset.Icc 1 f, (u - (airyZero k : ℂ)) ^ 2) *
      airyProdTail f uSite epsU u

/-- The $u$-variable site $u_k$ for the $f = 1$ design $D(N, \eta_*, d)$ ($k \ge 2$). -/
noncomputable def designSiteU (N : ℕ) (k : ℕ) : ℝ :=
  if k ≤ N then airyZero k else uWKB k

/-- The $u$-variable imaginary width $\varepsilon_k$ for the $f = 1$ design $D(N, \eta_*, d)$ ($k \ge 2$). -/
noncomputable def designWidthU (N : ℕ) (etaStar : ℝ) (k : ℕ) : ℝ :=
  (if k ≤ N then etaStar else 1 / 4) * gapWKB k

/-- The Airy product $W(u) = W^{(1)}(u)$ for the design $D(N, \eta_*, d)$. -/
noncomputable def designWindowW (N : ℕ) (etaStar d : ℝ) (u : ℂ) : ℂ :=
  airyWindowProd 1 (airyZero 1 - d) (designSiteU N) (designWidthU N etaStar) u

/-! ### Section 4: Local product convergence and entireness of `W^{(f)}(u)` -/

/-- General tail convergence hypothesis: $u_k - u_k^W = O(k^{-4/3})$ and $|\varepsilon_k| \le C k^{-1/3}$. -/
def AiryProdTailHypothesis (f : ℕ) (uSite epsU : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ k : ℕ, f < k → |uSite k - uWKB k| ≤ C * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧
    |epsU k| ≤ C * (k : ℝ) ^ (-(1 / 3 : ℝ))

lemma design_tail_hypothesis (N : ℕ) (etaStar : ℝ) :
    AiryProdTailHypothesis 1 (designSiteU N) (designWidthU N etaStar) := by
  obtain ⟨C₀, hC₀, hδ⟩ := deltaWKB_le_exists
  set C₁ := (2 / 3 : ℝ) * kappaAiry * (4 / 3 : ℝ) ^ (1 / 3 : ℝ)
  refine ⟨max C₀ (max |etaStar| (1 / 4) * C₁), by positivity, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := by omega
  constructor
  · unfold designSiteU
    split_ifs
    · have h1 := hδ k hk1
      unfold deltaWKB at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · simp only [sub_self, abs_zero]
      positivity
  · unfold designWidthU
    have hgap := gapWKB_le_mul_rpow hk1
    have hgap_nn : 0 ≤ gapWKB k := (gapWKB_pos hk1).le
    rw [abs_mul, abs_of_nonneg hgap_nn]
    have hη : |(if k ≤ N then etaStar else (1 / 4 : ℝ))| ≤ max |etaStar| (1 / 4) := by
      split_ifs
      · exact le_max_left _ _
      · rw [abs_of_nonneg (by norm_num)]; exact le_max_right _ _
    calc |(if k ≤ N then etaStar else (1 / 4 : ℝ))| * gapWKB k
        ≤ max |etaStar| (1 / 4) * (C₁ * (k : ℝ) ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul hη hgap hgap_nn (by positivity)
      _ = (max |etaStar| (1 / 4) * C₁) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by ring
      _ ≤ max C₀ (max |etaStar| (1 / 4) * C₁) * (k : ℝ) ^ (-(1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

private lemma airyProdFactor_sub_one_eq (uSite epsU : ℕ → ℝ) (k : ℕ) {u : ℂ}
    (hu : u ≠ (airyZero k : ℂ)) :
    airyProdFactor uSite epsU k u - 1 =
      2 * ((airyZero k - uSite k : ℝ) : ℂ) / (u - (airyZero k : ℂ)) +
      (((airyZero k - uSite k : ℝ) : ℂ) ^ 2 + (epsU k : ℂ) ^ 2) / (u - (airyZero k : ℂ)) ^ 2 := by
  unfold airyProdFactor
  have hne : u - (airyZero k : ℂ) ≠ 0 := sub_ne_zero.mpr hu
  have heq : u - (uSite k : ℂ) = (u - (airyZero k : ℂ)) + ((airyZero k - uSite k : ℝ) : ℂ) := by
    push_cast; ring
  rw [heq]
  field_simp [hne]
  push_cast
  ring

private lemma norm_airyProdFactor_sub_one_le (uSite epsU : ℕ → ℝ) (k : ℕ) {u : ℂ}
    (hu : u ≠ (airyZero k : ℂ)) :
    ‖airyProdFactor uSite epsU k u - 1‖ ≤
      2 * |airyZero k - uSite k| / ‖u - (airyZero k : ℂ)‖ +
      (|airyZero k - uSite k| ^ 2 + |epsU k| ^ 2) / ‖u - (airyZero k : ℂ)‖ ^ 2 := by
  rw [airyProdFactor_sub_one_eq uSite epsU k hu]
  refine (norm_add_le _ _).trans ?_
  gcongr
  · rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  · rw [norm_div, norm_pow]
    gcongr
    exact (norm_add_le _ _).trans (by
      rw [norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs])

lemma airyZero_injective_on : ∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → airyZero m = airyZero n → m = n := by
  intro m n hm hn h
  rcases lt_trichotomy m n with hlt | rfl | hgt
  · exact absurd h (airyZero_lt_of_lt hm hlt).ne'
  · rfl
  · exact absurd h.symm (airyZero_lt_of_lt hn hgt).ne'

/-- On any compact set $K \subset \mathbb{C}$, all but finitely many Airy zeros lie outside $K$
(in fact $\|u - a_k\| \ge k^{2/3}$ eventually). -/
lemma norm_sub_airyZero_ge_eventually (R : ℝ) :
    ∃ K₀ : ℕ, 2 ≤ K₀ ∧ ∀ k : ℕ, K₀ ≤ k → ∀ u : ℂ, ‖u‖ ≤ R →
      (k : ℝ) ^ (2 / 3 : ℝ) ≤ ‖u - (airyZero k : ℂ)‖ := by
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt ((max R 0 + 1) ^ (3 / 2 : ℝ))
  refine ⟨max K₀ 2, le_max_right _ _, fun k hk u hu => ?_⟩
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hk
  have hK_le : K₀ ≤ k := le_trans (le_max_left _ _) hk
  have hk_gt : (max R 0 + 1) ^ (3 / 2 : ℝ) < (k : ℝ) := hK₀.trans_le (by exact_mod_cast hK_le)
  have hR_lt : R + 1 < (k : ℝ) ^ (2 / 3 : ℝ) := by
    have h1 : max R 0 + 1 < (k : ℝ) ^ (2 / 3 : ℝ) := by
      have hm : 0 ≤ max R 0 + 1 := by positivity
      have hpow := Real.rpow_lt_rpow (by positivity) hk_gt (by norm_num : (0 : ℝ) < 2 / 3)
      rw [← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one] at hpow
      exact hpow
    linarith [le_max_left R 0]
  have h1 := (airyZero_abs_bounds hk2).1
  have htri := norm_sub_norm_le ((airyZero k : ℂ)) u
  rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (airyZero_neg k)] at htri
  have hkpow : 0 ≤ (k : ℝ) ^ (2 / 3 : ℝ) := by positivity
  linarith

private lemma hasProdLocallyUniformlyOn_airyProdTail_aux
    (f : ℕ) (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis f uSite epsU)
    (skip : ℕ → Prop) [DecidablePred skip] :
    HasProdLocallyUniformlyOn
      (fun m u => if skip (f + 1 + m) then 1 else airyProdFactor uSite epsU (f + 1 + m) u)
      (fun u => ∏' m : ℕ, if skip (f + 1 + m) then 1 else airyProdFactor uSite epsU (f + 1 + m) u)
      {u : ℂ | ∀ m : ℕ, ¬skip (f + 1 + m) → u ≠ (airyZero (f + 1 + m) : ℂ)} := by
  set U : Set ℂ := {u : ℂ | ∀ m : ℕ, ¬skip (f + 1 + m) → u ≠ (airyZero (f + 1 + m) : ℂ)}
  have hU_open : IsOpen U := by
    rw [isOpen_iff_forall_mem_open]
    intro u hu
    obtain ⟨K₀, _, hK₀⟩ := norm_sub_airyZero_ge_eventually (‖u‖ + 1)
    have hfin : (Finset.range K₀).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
    set r : ℝ := min 1 ((Finset.range K₀).inf' hfin fun m =>
      if skip (f + 1 + m) then 1 else ‖u - (airyZero (f + 1 + m) : ℂ)‖)
    have hr_pos : 0 < r := by
      refine lt_min zero_lt_one ?_
      rw [Finset.lt_inf'_iff]
      intro m _
      split_ifs with hs
      · exact zero_lt_one
      · exact norm_pos_iff.mpr (sub_ne_zero.mpr (hu m hs))
    refine ⟨ball u r, fun z hz m hns => ?_, isOpen_ball, mem_ball_self hr_pos⟩
    have hzr : ‖z - u‖ < r := mem_ball_iff_norm.mp hz
    by_cases hm : m < K₀
    · have hle : r ≤ ‖u - (airyZero (f + 1 + m) : ℂ)‖ := by
        have hinf := Finset.inf'_le (fun m =>
            if skip (f + 1 + m) then 1 else ‖u - (airyZero (f + 1 + m) : ℂ)‖)
          (Finset.mem_range.mpr hm)
        simp only [if_neg hns] at hinf
        exact (min_le_right _ _).trans hinf
      intro hzeq
      rw [hzeq, norm_sub_rev] at hzr
      linarith
    · have hkm : K₀ ≤ f + 1 + m := by omega
      have hzn : ‖z‖ ≤ ‖u‖ + 1 := by
        have h1 : ‖z‖ ≤ ‖u‖ + ‖z - u‖ := by simpa using norm_add_le u (z - u)
        linarith [min_le_left 1 ((Finset.range K₀).inf' hfin fun m =>
          if skip (f + 1 + m) then 1 else ‖u - (airyZero (f + 1 + m) : ℂ)‖)]
      have hge := hK₀ (f + 1 + m) hkm z hzn
      have hkpos : (0 : ℝ) < ((f + 1 + m : ℕ) : ℝ) ^ (2 / 3 : ℝ) :=
        Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < f + 1 + m)) _
      exact norm_pos_iff.mp (lt_of_lt_of_le hkpos hge) ∘ sub_eq_zero.mpr
  refine hasProdLocallyUniformlyOn_of_forall_compact hU_open fun K hKU hKcomp => ?_
  obtain ⟨R, hR⟩ := hKcomp.isBounded.exists_norm_le
  obtain ⟨K₀, _, hK₀⟩ := norm_sub_airyZero_ge_eventually (max R 0)
  obtain ⟨C_H, hC_H, hH_bd⟩ := hH
  obtain ⟨C_Z, hC_Z, hZ_bd⟩ := deltaWKB_le_exists
  set M_H := C_H + C_Z
  have hM_H : 0 < M_H := by positivity
  set C_maj : ℝ := 2 * M_H + (M_H ^ 2 + C_H ^ 2)
  have hsum_maj : Summable (fun m : ℕ => C_maj * (((f + 1 + m : ℕ) : ℝ) ^ (-2 : ℝ))) := by
    have h2 : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
      simpa using this
    refine (h2.mul_left C_maj).of_nonneg_of_le (fun _ => by positivity) fun m => ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
    exact_mod_cast (by omega : m + 1 ≤ f + 1 + m)
  let g : ℕ → ℂ → ℂ := fun m u =>
    (if skip (f + 1 + m) then (1 : ℂ) else airyProdFactor uSite epsU (f + 1 + m) u) - 1
  have hg_eq : ∀ m u, 1 + g m u =
      if skip (f + 1 + m) then (1 : ℂ) else airyProdFactor uSite epsU (f + 1 + m) u :=
    fun m u => by dsimp [g]; ring
  have hsum_g : HasProdUniformlyOn (fun m u => 1 + g m u) (fun u => ∏' m : ℕ, (1 + g m u)) K := by
    refine Summable.hasProdUniformlyOn_one_add hKcomp hsum_maj ?_ fun m => ?_
    · filter_upwards [Nat.cofinite_eq_atTop.symm ▸ eventually_ge_atTop K₀] with m hm u hu
      dsimp [g]
      set k := f + 1 + m
      by_cases hskip : skip k
      · simp only [if_pos hskip, sub_self, norm_zero]
        positivity
      · simp only [if_neg hskip]
        have huR : ‖u‖ ≤ max R 0 := (hR u hu).trans (le_max_left _ _)
        have hkm : K₀ ≤ k := by omega
        have hk1 : 1 ≤ k := by omega
        have hfk : f < k := by omega
        have hdist := hK₀ k hkm u huR
        have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
        have hu_ne : u ≠ (airyZero k : ℂ) := hKU hu m hskip
        have hnorm := norm_airyProdFactor_sub_one_le uSite epsU k hu_ne
        obtain ⟨h_u, h_e⟩ := hH_bd k hfk
        have h_δ := hZ_bd k hk1
        have h_diff : |airyZero k - uSite k| ≤ M_H * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
          have htri : |airyZero k - uSite k| ≤ |airyZero k - uWKB k| + |uSite k - uWKB k| := by
            have : airyZero k - uSite k = (airyZero k - uWKB k) - (uSite k - uWKB k) := by ring
            rw [this]; exact abs_sub _ _
          have h_δ' : |airyZero k - uWKB k| ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ)) := h_δ
          calc |airyZero k - uSite k|
              ≤ |airyZero k - uWKB k| + |uSite k - uWKB k| := htri
            _ ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ)) + C_H * (k : ℝ) ^ (-(4 / 3 : ℝ)) := add_le_add h_δ' h_u
            _ = M_H * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by dsimp [M_H]; ring
        have h1 : 2 * |airyZero k - uSite k| / ‖u - (airyZero k : ℂ)‖ ≤ 2 * M_H * (k : ℝ) ^ (-2 : ℝ) := by
          calc 2 * |airyZero k - uSite k| / ‖u - (airyZero k : ℂ)‖
              ≤ 2 * (M_H * (k : ℝ) ^ (-(4 / 3 : ℝ))) / (k : ℝ) ^ (2 / 3 : ℝ) := by gcongr
            _ = 2 * M_H * ((k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ)) := by ring
            _ = 2 * M_H * (k : ℝ) ^ (-2 : ℝ) := by
                rw [← Real.rpow_sub hk_pos]
                congr 2; norm_num
        have hsq_diff : |airyZero k - uSite k| ^ 2 ≤ M_H ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
          have h1' := pow_le_pow_left₀ (abs_nonneg _) h_diff 2
          rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (-(4 / 3 : ℝ))) 2, ← Real.rpow_mul hk_pos.le,
            show -(4 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(8 / 3 : ℝ) by norm_num] at h1'
          refine h1'.trans ?_
          have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hk1' (by norm_num)) (by positivity)
        have hsq_eps : |epsU k| ^ 2 ≤ C_H ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
          have h1' := pow_le_pow_left₀ (abs_nonneg _) h_e 2
          rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hk_pos.le,
            show -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) by norm_num] at h1'
          exact h1'
        have h2 : (|airyZero k - uSite k| ^ 2 + |epsU k| ^ 2) / ‖u - (airyZero k : ℂ)‖ ^ 2 ≤
            (M_H ^ 2 + C_H ^ 2) * (k : ℝ) ^ (-2 : ℝ) := by
          have hdist2 : (k : ℝ) ^ (4 / 3 : ℝ) ≤ ‖u - (airyZero k : ℂ)‖ ^ 2 := by
            have := pow_le_pow_left₀ (by positivity) hdist 2
            rwa [← Real.rpow_natCast, ← Real.rpow_mul hk_pos.le,
              show (2 / 3 : ℝ) * ((2 : ℕ) : ℝ) = 4 / 3 by norm_num] at this
          calc (|airyZero k - uSite k| ^ 2 + |epsU k| ^ 2) / ‖u - (airyZero k : ℂ)‖ ^ 2
              ≤ (M_H ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) + C_H ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ))) /
                  (k : ℝ) ^ (4 / 3 : ℝ) := by gcongr
            _ = (M_H ^ 2 + C_H ^ 2) * ((k : ℝ) ^ (-(2 / 3 : ℝ)) / (k : ℝ) ^ (4 / 3 : ℝ)) := by ring
            _ = (M_H ^ 2 + C_H ^ 2) * (k : ℝ) ^ (-2 : ℝ) := by
                rw [← Real.rpow_sub hk_pos]; congr 2; norm_num
        calc ‖airyProdFactor uSite epsU k u - 1‖
            ≤ 2 * M_H * (k : ℝ) ^ (-2 : ℝ) + (M_H ^ 2 + C_H ^ 2) * (k : ℝ) ^ (-2 : ℝ) :=
                hnorm.trans (add_le_add h1 h2)
          _ = C_maj * (k : ℝ) ^ (-2 : ℝ) := by dsimp [C_maj]; ring
    · dsimp [g]
      refine ContinuousOn.sub ?_ continuousOn_const
      by_cases hskip : skip (f + 1 + m)
      · simp only [if_pos hskip]; exact continuousOn_const
      · simp only [if_neg hskip]
        intro u hu
        have hu_ne : u - (airyZero (f + 1 + m) : ℂ) ≠ 0 := sub_ne_zero.mpr (hKU hu m hskip)
        unfold airyProdFactor
        refine ContinuousAt.continuousWithinAt ?_
        fun_prop (disch := exact pow_ne_zero 2 hu_ne)
  simpa only [hg_eq] using hsum_g

lemma hasProd_airyProdTail {f : ℕ} {uSite epsU : ℕ → ℝ}
    (hH : AiryProdTailHypothesis f uSite epsU) {u : ℂ}
    (hu : ∀ k : ℕ, f < k → u ≠ (airyZero k : ℂ)) :
    HasProd (fun m : ℕ => airyProdFactor uSite epsU (f + 1 + m) u)
      (airyProdTail f uSite epsU u) := by
  have hp := (hasProdLocallyUniformlyOn_airyProdTail_aux f uSite epsU hH (fun _ => False)).hasProd
    (fun m _ => hu (f + 1 + m) (by omega))
  simpa only [↓reduceIte, airyProdTail] using hp

lemma hasProd_airyProdTailExcept {f n : ℕ} {uSite epsU : ℕ → ℝ}
    (hH : AiryProdTailHypothesis f uSite epsU) {u : ℂ}
    (hu : ∀ k : ℕ, f < k → k ≠ n → u ≠ (airyZero k : ℂ)) :
    HasProd (fun m : ℕ => if f + 1 + m = n then 1 else airyProdFactor uSite epsU (f + 1 + m) u)
      (airyProdTailExcept f n uSite epsU u) :=
  (hasProdLocallyUniformlyOn_airyProdTail_aux f uSite epsU hH (fun k => k = n)).hasProd
    (fun m hm => hu (f + 1 + m) (by omega) hm)

lemma differentiableOn_airyProdTail (f : ℕ) (uSite epsU : ℕ → ℝ)
    (hH : AiryProdTailHypothesis f uSite epsU) :
    DifferentiableOn ℂ (airyProdTail f uSite epsU)
      {u : ℂ | ∀ k : ℕ, f < k → u ≠ (airyZero k : ℂ)} := by
  set skip : ℕ → Prop := fun _ => False
  have hprod := hasProdLocallyUniformlyOn_airyProdTail_aux f uSite epsU hH skip
  set U : Set ℂ := {u : ℂ | ∀ m : ℕ, ¬skip (f + 1 + m) → u ≠ (airyZero (f + 1 + m) : ℂ)}
  have hU_eq : U = {u : ℂ | ∀ k : ℕ, f < k → u ≠ (airyZero k : ℂ)} := by
    ext u; simp only [U, skip, not_false_eq_true, forall_true_left, mem_setOf_eq]
    constructor
    · intro h k hk
      obtain ⟨m, rfl⟩ : ∃ m, k = f + 1 + m := ⟨k - f - 1, by omega⟩
      exact h m
    · intro h m; exact h (f + 1 + m) (by omega)
  have hU_open : IsOpen U := by
    rw [hU_eq, isOpen_iff_forall_mem_open]
    intro u hu
    obtain ⟨K₀, _, hK₀⟩ := norm_sub_airyZero_ge_eventually (‖u‖ + 1)
    have hfin : (Finset.Icc (f + 1) (max K₀ (f + 1))).Nonempty := ⟨f + 1, Finset.mem_Icc.mpr ⟨le_rfl, le_max_right _ _⟩⟩
    set r := min 1 ((Finset.Icc (f + 1) (max K₀ (f + 1))).inf' hfin fun k => ‖u - (airyZero k : ℂ)‖)
    have hr : 0 < r := lt_min zero_lt_one ((Finset.lt_inf'_iff _).mpr fun k hk =>
      norm_pos_iff.mpr (sub_ne_zero.mpr (hu k (Finset.mem_Icc.mp hk).1)))
    refine ⟨ball u r, fun z hz k hk => ?_, isOpen_ball, mem_ball_self hr⟩
    have hzr : ‖z - u‖ < r := mem_ball_iff_norm.mp hz
    by_cases hle : k ≤ max K₀ (f + 1)
    · have := Finset.inf'_le (f := fun k => ‖u - (airyZero k : ℂ)‖) (Finset.mem_Icc.mpr ⟨hk, hle⟩)
      have hrl : r ≤ ‖u - (airyZero k : ℂ)‖ := (min_le_right _ _).trans this
      intro hzeq; rw [hzeq, norm_sub_rev] at hzr; linarith
    · have hzn : ‖z‖ ≤ ‖u‖ + 1 := by
        have := norm_add_le u (z - u)
        simpa [add_sub_cancel] using this.trans (by linarith [min_le_left 1 ((Finset.Icc (f + 1) (max K₀ (f + 1))).inf' hfin fun k => ‖u - (airyZero k : ℂ)‖)])
      have hge := hK₀ k (by omega) z hzn
      have hkpos : (0 : ℝ) < (k : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < k)) _
      exact norm_pos_iff.mp (lt_of_lt_of_le hkpos hge) ∘ sub_eq_zero.mpr
  have hdiff : DifferentiableOn ℂ
      (fun u => ∏' m : ℕ, if skip (f + 1 + m) then 1 else airyProdFactor uSite epsU (f + 1 + m) u) U := by
    refine hprod.differentiableOn ?_ hU_open
    filter_upwards with s
    intro u hu
    refine DifferentiableAt.differentiableWithinAt ?_
    change DifferentiableAt ℂ (fun z => ∏ m ∈ s, airyProdFactor uSite epsU (f + 1 + m) z) u
    refine DifferentiableAt.fun_finsetProd fun m _ => ?_
    have hne : u - (airyZero (f + 1 + m) : ℂ) ≠ 0 := sub_ne_zero.mpr (hu m (by simp [skip]))
    unfold airyProdFactor
    fun_prop (disch := exact pow_ne_zero 2 hne)
  have heq : (fun u => ∏' m : ℕ, if skip (f + 1 + m) then 1 else airyProdFactor uSite epsU (f + 1 + m) u) =
      airyProdTail f uSite epsU := by
    ext u; simp [airyProdTail, skip]
  rw [← hU_eq, ← heq]
  exact hdiff

private lemma differentiableOn_airyProdTailExcept (f n : ℕ) (uSite epsU : ℕ → ℝ)
    (hH : AiryProdTailHypothesis f uSite epsU) :
    DifferentiableOn ℂ (airyProdTailExcept f n uSite epsU)
      {u : ℂ | ∀ k : ℕ, f < k → k ≠ n → u ≠ (airyZero k : ℂ)} := by
  set skip : ℕ → Prop := fun k => k = n
  have hprod := hasProdLocallyUniformlyOn_airyProdTail_aux f uSite epsU hH skip
  set U : Set ℂ := {u : ℂ | ∀ m : ℕ, ¬skip (f + 1 + m) → u ≠ (airyZero (f + 1 + m) : ℂ)}
  have hU_eq : U = {u : ℂ | ∀ k : ℕ, f < k → k ≠ n → u ≠ (airyZero k : ℂ)} := by
    ext u; simp only [U, skip, mem_setOf_eq]
    constructor
    · intro h k hk hkn
      obtain ⟨m, rfl⟩ : ∃ m, k = f + 1 + m := ⟨k - f - 1, by omega⟩
      exact h m hkn
    · intro h m hm; exact h (f + 1 + m) (by omega) hm
  have hU_open : IsOpen U := by
    rw [hU_eq, isOpen_iff_forall_mem_open]
    intro u hu
    obtain ⟨K₀, _, hK₀⟩ := norm_sub_airyZero_ge_eventually (‖u‖ + 1)
    set S := (Finset.Icc (f + 1) (max K₀ (f + 1))).filter (fun k => k ≠ n)
    by_cases hSne : S.Nonempty
    · set r := min 1 (S.inf' hSne fun k => ‖u - (airyZero k : ℂ)‖)
      have hr : 0 < r := lt_min zero_lt_one ((Finset.lt_inf'_iff _).mpr fun k hk =>
        let hk' := Finset.mem_filter.mp hk
        norm_pos_iff.mpr (sub_ne_zero.mpr (hu k (Finset.mem_Icc.mp hk'.1).1 hk'.2)))
      refine ⟨ball u r, fun z hz k hk hkn => ?_, isOpen_ball, mem_ball_self hr⟩
      have hzr : ‖z - u‖ < r := mem_ball_iff_norm.mp hz
      by_cases hle : k ≤ max K₀ (f + 1)
      · have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk, hle⟩, hkn⟩
        have hrl : r ≤ ‖u - (airyZero k : ℂ)‖ := (min_le_right _ _).trans (Finset.inf'_le _ hkS)
        intro hzeq; rw [hzeq, norm_sub_rev] at hzr; linarith
      · have hzn : ‖z‖ ≤ ‖u‖ + 1 := by
          have := norm_add_le u (z - u)
          simpa [add_sub_cancel] using this.trans (by linarith [min_le_left 1 (S.inf' hSne fun k => ‖u - (airyZero k : ℂ)‖)])
        have hge := hK₀ k (by omega) z hzn
        have hkpos : (0 : ℝ) < (k : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < k)) _
        exact norm_pos_iff.mp (lt_of_lt_of_le hkpos hge) ∘ sub_eq_zero.mpr
    · refine ⟨ball u 1, fun z hz k hk hkn => ?_, isOpen_ball, mem_ball_self zero_lt_one⟩
      have hle : ¬(k ≤ max K₀ (f + 1)) := fun hle =>
        hSne ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk, hle⟩, hkn⟩⟩
      have hzn : ‖z‖ ≤ ‖u‖ + 1 := by
        have := norm_add_le u (z - u)
        simpa [add_sub_cancel] using this.trans (by linarith [mem_ball_iff_norm.mp hz])
      have hge := hK₀ k (by omega) z hzn
      have hkpos : (0 : ℝ) < (k : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < k)) _
      exact norm_pos_iff.mp (lt_of_lt_of_le hkpos hge) ∘ sub_eq_zero.mpr
  have hdiff : DifferentiableOn ℂ
      (fun u => ∏' m : ℕ, if skip (f + 1 + m) then 1 else airyProdFactor uSite epsU (f + 1 + m) u) U := by
    refine hprod.differentiableOn ?_ hU_open
    filter_upwards with s
    intro u hu
    refine DifferentiableAt.differentiableWithinAt ?_
    change DifferentiableAt ℂ (fun z => ∏ m ∈ s,
      (if skip (f + 1 + m) then 1 else airyProdFactor uSite epsU (f + 1 + m) z)) u
    refine DifferentiableAt.fun_finsetProd fun m _ => ?_
    by_cases hm : skip (f + 1 + m)
    · simp [hm]
    · simp only [hm, ↓reduceIte]
      have hne : u - (airyZero (f + 1 + m) : ℂ) ≠ 0 := sub_ne_zero.mpr (hu m hm)
      unfold airyProdFactor
      fun_prop (disch := exact pow_ne_zero 2 hne)
  rw [← hU_eq]
  exact hdiff

/-- Off the Airy zeros $\{a_k : k \ge 1\}$, `airyWindowProd` equals the standard formula. -/
lemma airyWindowProd_eq_of_ne (f : ℕ) (uF : ℝ) (uSite epsU : ℕ → ℝ) {u : ℂ}
    (hu : ∀ n : ℕ, 1 ≤ n → u ≠ (airyZero n : ℂ)) :
    airyWindowProd f uF uSite epsU u =
      -airyAiC u ^ 2 * (u - (uF : ℂ)) /
        (∏ k ∈ Finset.Icc 1 f, (u - (airyZero k : ℂ)) ^ 2) *
        airyProdTail f uSite epsU u := by
  unfold airyWindowProd
  have hnot : ¬∃ n : ℕ, 1 ≤ n ∧ u = (airyZero n : ℂ) := by
    rintro ⟨n, hn, rfl⟩; exact hu n hn rfl
  simp [hnot]

/-- At an Airy zero $a_n$ with $n \le f$, `airyWindowProd` takes the explicit removable value. -/
lemma airyWindowProd_at_airyZero_le (f : ℕ) (uF : ℝ) (uSite epsU : ℕ → ℝ) {n : ℕ}
    (hn : 1 ≤ n) (_hnf : n ≤ f) :
    airyWindowProd f uF uSite epsU (airyZero n : ℂ) =
      -(deriv airyAiC (airyZero n : ℂ)) ^ 2 * ((airyZero n : ℂ) - (uF : ℂ)) /
        (∏ k ∈ (Finset.Icc 1 f).erase n, ((airyZero n : ℂ) - (airyZero k : ℂ)) ^ 2) *
        airyProdTail f uSite epsU (airyZero n : ℂ) := by
  unfold airyWindowProd
  have hex : ∃ m : ℕ, 1 ≤ m ∧ (airyZero n : ℂ) = (airyZero m : ℂ) := ⟨n, hn, rfl⟩
  have hfind : Nat.find hex = n := by
    obtain ⟨hm1, hmeq⟩ := Nat.find_spec hex
    exact airyZero_injective_on hm1 hn (Complex.ofReal_injective hmeq.symm)
  simp only [hex, ↓reduceDIte, hfind, _hnf, ↓reduceIte]

/-- At an Airy zero $a_n$ with $f < n$, `airyWindowProd` takes the explicit removable value. -/
lemma airyWindowProd_at_airyZero_gt (f : ℕ) (uF : ℝ) (uSite epsU : ℕ → ℝ) {n : ℕ}
    (hn : f < n) :
    airyWindowProd f uF uSite epsU (airyZero n : ℂ) =
      -(deriv airyAiC (airyZero n : ℂ)) ^ 2 * ((airyZero n : ℂ) - (uF : ℂ)) /
        (∏ k ∈ Finset.Icc 1 f, ((airyZero n : ℂ) - (airyZero k : ℂ)) ^ 2) *
        (((airyZero n : ℂ) - (uSite n : ℂ)) ^ 2 + (epsU n : ℂ) ^ 2) *
        airyProdTailExcept f n uSite epsU (airyZero n : ℂ) := by
  have hn1 : 1 ≤ n := by omega
  unfold airyWindowProd
  have hex : ∃ m : ℕ, 1 ≤ m ∧ (airyZero n : ℂ) = (airyZero m : ℂ) := ⟨n, hn1, rfl⟩
  have hfind : Nat.find hex = n := by
    obtain ⟨hm1, hmeq⟩ := Nat.find_spec hex
    exact airyZero_injective_on hm1 hn1 (Complex.ofReal_injective hmeq.symm)
  have hnot : ¬(n ≤ f) := by omega
  simp only [hex, ↓reduceDIte, hfind, hnot, ↓reduceIte]

/-- `airyWindowProd` is entire on $\mathbb{C}$. -/
theorem airyWindowProd_differentiable (f : ℕ) (_hf : 1 ≤ f) (uF : ℝ) (uSite epsU : ℕ → ℝ)
    (hH : AiryProdTailHypothesis f uSite epsU) :
    Differentiable ℂ (airyWindowProd f uF uSite epsU) := by
  intro u
  by_cases hu : ∃ n : ℕ, 1 ≤ n ∧ u = (airyZero n : ℂ)
  · obtain ⟨n, hn, rfl⟩ := hu
    obtain ⟨K₀, _, hK₀⟩ := norm_sub_airyZero_ge_eventually (‖(airyZero n : ℂ)‖ + 1)
    set S := (Finset.Icc 1 (max K₀ n)).filter (fun k => k ≠ n)
    have hSn : ∀ k ∈ S, (airyZero n : ℂ) ≠ (airyZero k : ℂ) := fun k hk h => by
      have hk' := Finset.mem_filter.mp hk
      exact hk'.2 (airyZero_injective_on (Finset.mem_Icc.mp hk'.1).1 hn (Complex.ofReal_injective h.symm))
    set r : ℝ := if hSne : S.Nonempty then
        min 1 (S.inf' hSne fun k => ‖(airyZero n : ℂ) - (airyZero k : ℂ)‖) else 1
    have hr_pos : 0 < r := by
      dsimp [r]; split_ifs with hSne
      · exact lt_min zero_lt_one ((Finset.lt_inf'_iff _).mpr fun k hk =>
          norm_pos_iff.mpr (sub_ne_zero.mpr (hSn k hk)))
      · exact zero_lt_one
    have hball_avoid : ∀ z ∈ ball (airyZero n : ℂ) r, ∀ k : ℕ, 1 ≤ k → k ≠ n →
        z ≠ (airyZero k : ℂ) := by
      intro z hz k hk hkn
      have hzr : ‖z - (airyZero n : ℂ)‖ < r := mem_ball_iff_norm.mp hz
      by_cases hle : k ≤ max K₀ n
      · have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk, hle⟩, hkn⟩
        have hSne : S.Nonempty := ⟨k, hkS⟩
        have hrl : r ≤ ‖(airyZero n : ℂ) - (airyZero k : ℂ)‖ := by
          dsimp [r]; rw [dif_pos hSne]; exact (min_le_right _ _).trans (Finset.inf'_le _ hkS)
        intro hzeq; rw [hzeq, norm_sub_rev] at hzr; linarith
      · have hr1 : r ≤ 1 := by
          dsimp [r]; split_ifs
          · exact min_le_left _ _
          · exact le_rfl
        have hzn : ‖z‖ ≤ ‖(airyZero n : ℂ)‖ + 1 := by
          have h1 := norm_add_le (airyZero n : ℂ) (z - (airyZero n : ℂ))
          rw [add_sub_cancel] at h1
          linarith
        have hge := hK₀ k (by omega) z hzn
        have hkpos : (0 : ℝ) < (k : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < k)) _
        exact norm_pos_iff.mp (lt_of_lt_of_le hkpos hge) ∘ sub_eq_zero.mpr
    have hdslope_diff : Differentiable ℂ (dslope airyAiC (airyZero n : ℂ)) :=
      differentiableOn_univ.mp ((Complex.differentiableOn_dslope (s := univ) (f := airyAiC)
        (c := (airyZero n : ℂ)) Filter.univ_mem).2 differentiable_airyAiC.differentiableOn)
    by_cases hnf : n ≤ f
    · set F : ℂ → ℂ := fun z =>
        -(dslope airyAiC (airyZero n : ℂ) z) ^ 2 * (z - (uF : ℂ)) /
          (∏ k ∈ (Finset.Icc 1 f).erase n, (z - (airyZero k : ℂ)) ^ 2) *
          airyProdTail f uSite epsU z
      have hF_diff : DifferentiableAt ℂ F (airyZero n : ℂ) := by
        have hden : ∏ k ∈ (Finset.Icc 1 f).erase n, ((airyZero n : ℂ) - (airyZero k : ℂ)) ^ 2 ≠ 0 := by
          rw [Finset.prod_ne_zero_iff]
          intro k hk
          have hk' := Finset.mem_erase.mp hk
          exact pow_ne_zero 2 (sub_ne_zero.mpr (hball_avoid (airyZero n : ℂ)
            (mem_ball_self hr_pos) k (Finset.mem_Icc.mp hk'.2).1 hk'.1))
        have htail_diff : DifferentiableAt ℂ (airyProdTail f uSite epsU) (airyZero n : ℂ) := by
          have hsub : ball (airyZero n : ℂ) r ⊆ {z : ℂ | ∀ k : ℕ, f < k → z ≠ (airyZero k : ℂ)} :=
            fun z hz k hk => hball_avoid z hz k (by omega) (by omega)
          exact ((differentiableOn_airyProdTail f uSite epsU hH).mono hsub).differentiableAt
            (isOpen_ball.mem_nhds (mem_ball_self hr_pos))
        have hd1 : DifferentiableAt ℂ (fun z => -(dslope airyAiC (airyZero n : ℂ) z) ^ 2 * (z - (uF : ℂ)) /
            (∏ k ∈ (Finset.Icc 1 f).erase n, (z - (airyZero k : ℂ)) ^ 2)) (airyZero n : ℂ) := by
          refine DifferentiableAt.div ?_ ?_ hden
          · exact ((hdslope_diff (airyZero n : ℂ)).pow 2).neg.mul ((differentiableAt_id).sub_const _)
          · exact DifferentiableAt.fun_finsetProd fun k _ => ((differentiableAt_id).sub_const _).pow 2
        exact hd1.mul htail_diff
      have hFeq : airyWindowProd f uF uSite epsU =ᶠ[𝓝 (airyZero n : ℂ)] F := by
        filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr_pos)] with z hz
        by_cases hzn : z = (airyZero n : ℂ)
        · subst hzn
          rw [airyWindowProd_at_airyZero_le f uF uSite epsU hn hnf]
          dsimp [F]
          rw [dslope_same]
        · have hz_avoid : ∀ k : ℕ, 1 ≤ k → z ≠ (airyZero k : ℂ) := fun k hk => by
            by_cases hkn : k = n
            · subst hkn; exact hzn
            · exact hball_avoid z hz k hk hkn
          rw [airyWindowProd_eq_of_ne f uF uSite epsU hz_avoid]
          dsimp [F]
          rw [dslope_of_ne _ hzn, slope_def_field, airyAiC_ofReal, airyAi_airyZero, Complex.ofReal_zero, sub_zero]
          have hsplit_prod : (∏ k ∈ Finset.Icc 1 f, (z - (airyZero k : ℂ)) ^ 2) =
              (z - (airyZero n : ℂ)) ^ 2 * ∏ k ∈ (Finset.Icc 1 f).erase n, (z - (airyZero k : ℂ)) ^ 2 :=
            (Finset.mul_prod_erase (Finset.Icc 1 f) (fun k => (z - (airyZero k : ℂ)) ^ 2)
              (Finset.mem_Icc.mpr ⟨hn, hnf⟩)).symm
          rw [hsplit_prod]
          have hz0 : z - (airyZero n : ℂ) ≠ 0 := sub_ne_zero.mpr hzn
          have hden : ∏ k ∈ (Finset.Icc 1 f).erase n, (z - (airyZero k : ℂ)) ^ 2 ≠ 0 := by
            rw [Finset.prod_ne_zero_iff]
            intro k hk
            have hk' := Finset.mem_erase.mp hk
            exact pow_ne_zero 2 (sub_ne_zero.mpr (hz_avoid k (Finset.mem_Icc.mp hk'.2).1))
          generalize dslope airyAiC (airyZero n : ℂ) z = S
          generalize (z - (uF : ℂ)) = Zf
          generalize ∏ k ∈ (Finset.Icc 1 f).erase n, (z - (airyZero k : ℂ)) ^ 2 = P
          generalize airyProdTail f uSite epsU z = T
          field_simp [hz0, hden]
      exact hF_diff.congr_of_eventuallyEq hFeq
    · have hfn : f < n := by omega
      set F : ℂ → ℂ := fun z =>
        -(dslope airyAiC (airyZero n : ℂ) z) ^ 2 * (z - (uF : ℂ)) /
          (∏ k ∈ Finset.Icc 1 f, (z - (airyZero k : ℂ)) ^ 2) *
          ((z - (uSite n : ℂ)) ^ 2 + (epsU n : ℂ) ^ 2) *
          airyProdTailExcept f n uSite epsU z
      have hF_diff : DifferentiableAt ℂ F (airyZero n : ℂ) := by
        have hden : ∏ k ∈ Finset.Icc 1 f, ((airyZero n : ℂ) - (airyZero k : ℂ)) ^ 2 ≠ 0 := by
          rw [Finset.prod_ne_zero_iff]
          intro k hk
          have hk' := Finset.mem_Icc.mp hk
          exact pow_ne_zero 2 (sub_ne_zero.mpr (hball_avoid (airyZero n : ℂ)
            (mem_ball_self hr_pos) k hk'.1 (by omega)))
        have htail_diff : DifferentiableAt ℂ (airyProdTailExcept f n uSite epsU) (airyZero n : ℂ) := by
          have hsub : ball (airyZero n : ℂ) r ⊆
              {z : ℂ | ∀ k : ℕ, f < k → k ≠ n → z ≠ (airyZero k : ℂ)} :=
            fun z hz k hk hkn => hball_avoid z hz k (by omega) hkn
          exact ((differentiableOn_airyProdTailExcept f n uSite epsU hH).mono hsub).differentiableAt
            (isOpen_ball.mem_nhds (mem_ball_self hr_pos))
        have hd1 : DifferentiableAt ℂ (fun z => -(dslope airyAiC (airyZero n : ℂ) z) ^ 2 * (z - (uF : ℂ)) /
            (∏ k ∈ Finset.Icc 1 f, (z - (airyZero k : ℂ)) ^ 2)) (airyZero n : ℂ) := by
          refine DifferentiableAt.div ?_ ?_ hden
          · exact ((hdslope_diff (airyZero n : ℂ)).pow 2).neg.mul ((differentiableAt_id).sub_const _)
          · exact DifferentiableAt.fun_finsetProd fun k _ => ((differentiableAt_id).sub_const _).pow 2
        have hd2 : DifferentiableAt ℂ (fun z => (z - (uSite n : ℂ)) ^ 2 + (epsU n : ℂ) ^ 2) (airyZero n : ℂ) :=
          (((differentiableAt_id).sub_const _).pow 2).add_const _
        exact (hd1.mul hd2).mul htail_diff
      have hFeq : airyWindowProd f uF uSite epsU =ᶠ[𝓝 (airyZero n : ℂ)] F := by
        filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr_pos)] with z hz
        by_cases hzn : z = (airyZero n : ℂ)
        · subst hzn
          rw [airyWindowProd_at_airyZero_gt f uF uSite epsU hfn]
          dsimp [F]
          rw [dslope_same]
        · have hz_avoid : ∀ k : ℕ, 1 ≤ k → z ≠ (airyZero k : ℂ) := fun k hk => by
            by_cases hkn : k = n
            · subst hkn; exact hzn
            · exact hball_avoid z hz k hk hkn
          rw [airyWindowProd_eq_of_ne f uF uSite epsU hz_avoid]
          dsimp [F]
          rw [dslope_of_ne _ hzn, slope_def_field, airyAiC_ofReal, airyAi_airyZero, Complex.ofReal_zero, sub_zero]
          obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, f + 1 + m₀ = n := ⟨n - f - 1, by omega⟩
          have hprod2 : Multipliable (fun m : ℕ =>
              if f + 1 + m = n then (1 : ℂ) else airyProdFactor uSite epsU (f + 1 + m) z) :=
            (hasProd_airyProdTailExcept hH fun k hk _ => hz_avoid k (by omega)).multipliable
          have hupd : Function.update (fun m : ℕ => airyProdFactor uSite epsU (f + 1 + m) z) m₀ 1 =
              fun m => if f + 1 + m = n then 1 else airyProdFactor uSite epsU (f + 1 + m) z := by
            ext m
            by_cases hmm : m = m₀
            · subst hmm; simp [Function.update, hm₀]
            · simp [Function.update, hmm, show f + 1 + m ≠ n by omega]
          have hprod_upd : Multipliable
              (Function.update (fun m : ℕ => airyProdFactor uSite epsU (f + 1 + m) z) m₀ 1) := by
            rw [hupd]; exact hprod2
          have htail_split : airyProdTail f uSite epsU z =
              airyProdFactor uSite epsU n z * airyProdTailExcept f n uSite epsU z := by
            unfold airyProdTail airyProdTailExcept
            have h1 := Multipliable.tprod_eq_mul_tprod_ite' m₀ hprod_upd
            rw [hm₀] at h1
            refine h1.trans ?_
            congr 1
            refine tprod_congr fun m => ?_
            have hiff : (m = m₀) ↔ (f + 1 + m = n) := ⟨fun h => by omega, fun h => by omega⟩
            simp [hiff]
          rw [htail_split]
          unfold airyProdFactor
          have hz0 : z - (airyZero n : ℂ) ≠ 0 := sub_ne_zero.mpr hzn
          have hden : ∏ k ∈ Finset.Icc 1 f, (z - (airyZero k : ℂ)) ^ 2 ≠ 0 := by
            rw [Finset.prod_ne_zero_iff]
            intro k hk
            exact pow_ne_zero 2 (sub_ne_zero.mpr (hz_avoid k (Finset.mem_Icc.mp hk).1))
          generalize dslope airyAiC (airyZero n : ℂ) z = S
          generalize (z - (uF : ℂ)) = Zf
          generalize ∏ k ∈ Finset.Icc 1 f, (z - (airyZero k : ℂ)) ^ 2 = P
          generalize airyProdTailExcept f n uSite epsU z = T
          field_simp [hz0, hden]
      exact hF_diff.congr_of_eventuallyEq hFeq
  · push_neg at hu
    obtain ⟨K₀, _, hK₀⟩ := norm_sub_airyZero_ge_eventually (‖u‖ + 1)
    set S := Finset.Icc 1 K₀
    have hSn : ∀ k ∈ S, u ≠ (airyZero k : ℂ) := fun k hk => hu k (Finset.mem_Icc.mp hk).1
    have hSne : S.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
    set r : ℝ := min 1 (S.inf' hSne fun k => ‖u - (airyZero k : ℂ)‖)
    have hr_pos : 0 < r := lt_min zero_lt_one ((Finset.lt_inf'_iff _).mpr fun k hk =>
      norm_pos_iff.mpr (sub_ne_zero.mpr (hSn k hk)))
    have hball_avoid : ∀ z ∈ ball u r, ∀ k : ℕ, 1 ≤ k → z ≠ (airyZero k : ℂ) := by
      intro z hz k hk
      have hzr : ‖z - u‖ < r := mem_ball_iff_norm.mp hz
      by_cases hle : k ≤ K₀
      · have hrl : r ≤ ‖u - (airyZero k : ℂ)‖ :=
          (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hk, hle⟩))
        intro hzeq; rw [hzeq, norm_sub_rev] at hzr; linarith
      · have hzn : ‖z‖ ≤ ‖u‖ + 1 := by
          have := norm_add_le u (z - u)
          simpa [add_sub_cancel] using this.trans (by linarith [min_le_left 1 (S.inf' hSne fun k => ‖u - (airyZero k : ℂ)‖)])
        have hge := hK₀ k (by omega) z hzn
        have hkpos : (0 : ℝ) < (k : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < k)) _
        exact norm_pos_iff.mp (lt_of_lt_of_le hkpos hge) ∘ sub_eq_zero.mpr
    set F : ℂ → ℂ := fun z =>
      -airyAiC z ^ 2 * (z - (uF : ℂ)) /
        (∏ k ∈ Finset.Icc 1 f, (z - (airyZero k : ℂ)) ^ 2) *
        airyProdTail f uSite epsU z
    have hF_diff : DifferentiableAt ℂ F u := by
      have hden : ∏ k ∈ Finset.Icc 1 f, (u - (airyZero k : ℂ)) ^ 2 ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro k hk
        exact pow_ne_zero 2 (sub_ne_zero.mpr (hu k (Finset.mem_Icc.mp hk).1))
      have htail_diff : DifferentiableAt ℂ (airyProdTail f uSite epsU) u := by
        have hsub : ball u r ⊆ {z : ℂ | ∀ k : ℕ, f < k → z ≠ (airyZero k : ℂ)} :=
          fun z hz k hk => hball_avoid z hz k (by omega)
        exact ((differentiableOn_airyProdTail f uSite epsU hH).mono hsub).differentiableAt
          (isOpen_ball.mem_nhds (mem_ball_self hr_pos))
      have hd1 : DifferentiableAt ℂ (fun z => -airyAiC z ^ 2 * (z - (uF : ℂ)) /
          (∏ k ∈ Finset.Icc 1 f, (z - (airyZero k : ℂ)) ^ 2)) u := by
        refine DifferentiableAt.div ?_ ?_ hden
        · exact (((differentiable_airyAiC u).pow 2).neg).mul ((differentiableAt_id).sub_const _)
        · exact DifferentiableAt.fun_finsetProd fun k _ => ((differentiableAt_id).sub_const _).pow 2
      exact hd1.mul htail_diff
    have hFeq : airyWindowProd f uF uSite epsU =ᶠ[𝓝 u] F := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr_pos)] with z hz
      exact airyWindowProd_eq_of_ne f uF uSite epsU (hball_avoid z hz)
    exact hF_diff.congr_of_eventuallyEq hFeq

/-- `airyWindowProd` is real on $\mathbb{R}$. -/
lemma airyWindowProd_im_eq_zero (f : ℕ) (uF : ℝ) (uSite epsU : ℕ → ℝ)
    (hH : AiryProdTailHypothesis f uSite epsU) (x : ℝ) :
    (airyWindowProd f uF uSite epsU (x : ℂ)).im = 0 := by
  have hreal_factor : ∀ k : ℕ, (airyProdFactor uSite epsU k (x : ℂ)).im = 0 := fun k => by
    unfold airyProdFactor
    have : (((x : ℂ) - (uSite k : ℂ)) ^ 2 + (epsU k : ℂ) ^ 2) / ((x : ℂ) - (airyZero k : ℂ)) ^ 2 =
        ((((x - uSite k) ^ 2 + epsU k ^ 2) / (x - airyZero k) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_im]
  have htail_im : (airyProdTail f uSite epsU (x : ℂ)).im = 0 := by
    by_cases hx : ∀ k : ℕ, f < k → (x : ℂ) ≠ (airyZero k : ℂ)
    · have hp := hasProd_airyProdTail hH hx
      have him : Tendsto (fun s : Finset ℕ => (∏ m ∈ s, airyProdFactor uSite epsU (f + 1 + m) (x : ℂ)).im)
          atTop (𝓝 (airyProdTail f uSite epsU (x : ℂ)).im) :=
        Complex.continuous_im.continuousAt.tendsto.comp hp
      have hzero : ∀ s : Finset ℕ, (∏ m ∈ s, airyProdFactor uSite epsU (f + 1 + m) (x : ℂ)).im = 0 := fun s => by
        have : ∏ m ∈ s, airyProdFactor uSite epsU (f + 1 + m) (x : ℂ) =
            ((∏ m ∈ s, (airyProdFactor uSite epsU (f + 1 + m) (x : ℂ)).re : ℝ) : ℂ) := by
          push_cast
          refine Finset.prod_congr rfl fun m _ => Complex.ext rfl (hreal_factor _)
        rw [this, Complex.ofReal_im]
      simp_rw [hzero] at him
      exact (tendsto_const_nhds_iff.mp him).symm
    · push_neg at hx
      obtain ⟨n, hfn, hnx⟩ := hx
      obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, f + 1 + m₀ = n := ⟨n - f - 1, by omega⟩
      have hfac0 : airyProdFactor uSite epsU (f + 1 + m₀) (x : ℂ) = 0 := by
        unfold airyProdFactor
        rw [hm₀, hnx, sub_self, zero_pow two_ne_zero, div_zero]
      by_cases hmult : Multipliable (fun m : ℕ => airyProdFactor uSite epsU (f + 1 + m) (x : ℂ))
      · have ht : Tendsto (fun s : Finset ℕ => ∏ m ∈ s, airyProdFactor uSite epsU (f + 1 + m) (x : ℂ))
            atTop (𝓝 (airyProdTail f uSite epsU (x : ℂ))) := hmult.hasProd
        have hev : ∀ᶠ s : Finset ℕ in atTop,
            ∏ m ∈ s, airyProdFactor uSite epsU (f + 1 + m) (x : ℂ) = 0 := by
          filter_upwards [eventually_ge_atTop {m₀}] with s hs
          exact Finset.prod_eq_zero (hs (Finset.mem_singleton_self m₀)) hfac0
        have h0 : airyProdTail f uSite epsU (x : ℂ) = 0 :=
          tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))
        rw [h0, Complex.zero_im]
      · unfold airyProdTail
        rw [tprod_eq_one_of_not_multipliable hmult, Complex.one_im]
  by_cases hx : ∃ n : ℕ, 1 ≤ n ∧ (x : ℂ) = (airyZero n : ℂ)
  · obtain ⟨n, hn, hnx⟩ := hx
    have hxr : x = airyZero n := Complex.ofReal_injective hnx
    subst hxr
    by_cases hnf : n ≤ f
    · rw [airyWindowProd_at_airyZero_le f uF uSite epsU hn hnf]
      have htail_re : airyProdTail f uSite epsU (airyZero n : ℂ) =
          ((airyProdTail f uSite epsU (airyZero n : ℂ)).re : ℂ) :=
        Complex.ext rfl htail_im
      have hda_re : deriv airyAiC (airyZero n : ℂ) = ((airyAi' (airyZero n) : ℝ) : ℂ) :=
        deriv_airyAiC_ofReal _
      rw [hda_re, htail_re]
      have hall : -((airyAi' (airyZero n) : ℝ) : ℂ) ^ 2 * ((airyZero n : ℂ) - (uF : ℂ)) /
          (∏ k ∈ (Finset.Icc 1 f).erase n, ((airyZero n : ℂ) - (airyZero k : ℂ)) ^ 2) *
          ((airyProdTail f uSite epsU (airyZero n : ℂ)).re : ℂ) =
          (((-(airyAi' (airyZero n)) ^ 2 * (airyZero n - uF) /
            (∏ k ∈ (Finset.Icc 1 f).erase n, (airyZero n - airyZero k) ^ 2) *
            (airyProdTail f uSite epsU (airyZero n : ℂ)).re : ℝ)) : ℂ) := by
        push_cast; rfl
      rw [hall, Complex.ofReal_im]
    · have hfn : f < n := by omega
      rw [airyWindowProd_at_airyZero_gt f uF uSite epsU hfn]
      have htail_exc_im : (airyProdTailExcept f n uSite epsU (airyZero n : ℂ)).im = 0 := by
        have hp := hasProd_airyProdTailExcept (f := f) (n := n) hH fun k hk hkn h =>
          hkn (airyZero_injective_on (by omega) hn (Complex.ofReal_injective h.symm))
        have him : Tendsto (fun s : Finset ℕ =>
            (∏ m ∈ s, if f + 1 + m = n then (1 : ℂ) else airyProdFactor uSite epsU (f + 1 + m) (airyZero n : ℂ)).im)
            atTop (𝓝 (airyProdTailExcept f n uSite epsU (airyZero n : ℂ)).im) :=
          Complex.continuous_im.continuousAt.tendsto.comp hp
        have hzero : ∀ s : Finset ℕ,
            (∏ m ∈ s, if f + 1 + m = n then (1 : ℂ) else airyProdFactor uSite epsU (f + 1 + m) (airyZero n : ℂ)).im = 0 := by
          intro s
          have him1 : ∀ m ∈ s,
              (if f + 1 + m = n then (1 : ℂ) else airyProdFactor uSite epsU (f + 1 + m) (airyZero n : ℂ)).im = 0 := by
            intro m _
            split_ifs
            · simp
            · exact hreal_factor (f + 1 + m)
          have heq : ∏ m ∈ s, (if f + 1 + m = n then (1 : ℂ) else airyProdFactor uSite epsU (f + 1 + m) (airyZero n : ℂ)) =
              ((∏ m ∈ s, (if f + 1 + m = n then (1 : ℂ) else airyProdFactor uSite epsU (f + 1 + m) (airyZero n : ℂ)).re : ℝ) : ℂ) := by
            push_cast
            refine Finset.prod_congr rfl fun m hm => Complex.ext rfl (him1 m hm)
          rw [heq, Complex.ofReal_im]
        simp_rw [hzero] at him
        exact (tendsto_const_nhds_iff.mp him).symm
      have hda_re : deriv airyAiC (airyZero n : ℂ) = ((airyAi' (airyZero n) : ℝ) : ℂ) :=
        deriv_airyAiC_ofReal _
      have htail_re : airyProdTailExcept f n uSite epsU (airyZero n : ℂ) =
          ((airyProdTailExcept f n uSite epsU (airyZero n : ℂ)).re : ℂ) :=
        Complex.ext rfl htail_exc_im
      rw [hda_re, htail_re]
      have hall : -((airyAi' (airyZero n) : ℝ) : ℂ) ^ 2 * ((airyZero n : ℂ) - (uF : ℂ)) /
          (∏ k ∈ Finset.Icc 1 f, ((airyZero n : ℂ) - (airyZero k : ℂ)) ^ 2) *
          (((airyZero n : ℂ) - (uSite n : ℂ)) ^ 2 + (epsU n : ℂ) ^ 2) *
          ((airyProdTailExcept f n uSite epsU (airyZero n : ℂ)).re : ℂ) =
          (((-(airyAi' (airyZero n)) ^ 2 * (airyZero n - uF) /
            (∏ k ∈ Finset.Icc 1 f, (airyZero n - airyZero k) ^ 2) *
            ((airyZero n - uSite n) ^ 2 + epsU n ^ 2) *
            (airyProdTailExcept f n uSite epsU (airyZero n : ℂ)).re : ℝ)) : ℂ) := by
        push_cast; rfl
      rw [hall, Complex.ofReal_im]
  · push_neg at hx
    rw [airyWindowProd_eq_of_ne f uF uSite epsU hx, airyAiC_ofReal]
    have htail_re : airyProdTail f uSite epsU (x : ℂ) = ((airyProdTail f uSite epsU (x : ℂ)).re : ℂ) :=
      Complex.ext rfl htail_im
    rw [htail_re]
    have hall : -((airyAi x : ℝ) : ℂ) ^ 2 * ((x : ℂ) - (uF : ℂ)) /
        (∏ k ∈ Finset.Icc 1 f, ((x : ℂ) - (airyZero k : ℂ)) ^ 2) *
        ((airyProdTail f uSite epsU (x : ℂ)).re : ℂ) =
        (((-(airyAi x) ^ 2 * (x - uF) /
          (∏ k ∈ Finset.Icc 1 f, (x - airyZero k) ^ 2) *
          (airyProdTail f uSite epsU (x : ℂ)).re : ℝ)) : ℂ) := by
      push_cast; rfl
    rw [hall, Complex.ofReal_im]

/-! ### Section 5: Lemma G (`ut:G`) — uniform growth bound, $L^1$, and gap-circle ratio -/

/-- For $u \in \mathbb{C}$ outside the $c_0\,\mathrm{gap}_k$-discs, $\|P(u)\| \le C(c_0)$. -/
lemma airyProdTail_norm_le_of_avoid (f : ℕ) (uSite epsU : ℕ → ℝ)
    (hH : AiryProdTailHypothesis f uSite epsU) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C > 0, ∀ u : ℂ, (∀ k : ℕ, 1 ≤ k → c₀ * airyGap k ≤ ‖u - (airyZero k : ℂ)‖) →
      ‖airyProdTail f uSite epsU u‖ ≤ C := by
  obtain ⟨K_sum, hK_sum, hsum_lem⟩ := airyGap_kernel_sum hc₀
  obtain ⟨C_H, hC_H, hH_bd⟩ := id hH
  obtain ⟨C_Z, hC_Z, hZ_bd⟩ := deltaWKB_le_exists
  obtain ⟨c₁, _, hc₁, _, hgap⟩ := airyGap_bounds_exists
  set Z₂ : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2
  have hZ₂ : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  have hZ₂_nn : 0 ≤ Z₂ := tsum_nonneg fun _ => by positivity
  set M_H := (C_H + C_Z) / c₁
  set C_eps := C_H / c₁
  set B := 2 * M_H * √(K_sum * Z₂) + (M_H ^ 2 + C_eps ^ 2) * K_sum
  refine ⟨Real.exp B, Real.exp_pos _, fun u hu => ?_⟩
  have hu_ne : ∀ k : ℕ, f < k → u ≠ (airyZero k : ℂ) := fun k hk h => by
    have := hu k (by omega)
    rw [h, sub_self, norm_zero] at this
    linarith [mul_pos hc₀ (airyGap_pos (by omega : 1 ≤ k))]
  have hp := hasProd_airyProdTail hH hu_ne
  have hnorm_tend : Tendsto (fun s : Finset ℕ => ‖∏ m ∈ s, airyProdFactor uSite epsU (f + 1 + m) u‖)
      atTop (𝓝 ‖airyProdTail f uSite epsU u‖) :=
    continuous_norm.continuousAt.tendsto.comp hp
  obtain ⟨hker_sum, hker_le⟩ := hsum_lem u hu
  refine le_of_tendsto hnorm_tend (Eventually.of_forall fun s => ?_)
  rw [norm_prod]
  have hfac_bd : ∀ m : ℕ,
      ‖airyProdFactor uSite epsU (f + 1 + m) u‖ ≤
        Real.exp (2 * M_H * (airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖) *
            (1 / ((f + 1 + m : ℕ) : ℝ)) +
          (M_H ^ 2 + C_eps ^ 2) *
            (airyGap (f + 1 + m) ^ 2 / ‖u - (airyZero (f + 1 + m) : ℂ)‖ ^ 2)) := by
    intro m
    set k := f + 1 + m
    have hk1 : 1 ≤ k := by omega
    have hfk : f < k := by omega
    have hnorm := norm_airyProdFactor_sub_one_le uSite epsU k (hu_ne k hfk)
    have htri : ‖airyProdFactor uSite epsU k u‖ ≤ 1 + ‖airyProdFactor uSite epsU k u - 1‖ := by
      have := norm_add_le (1 : ℂ) (airyProdFactor uSite epsU k u - 1)
      simpa using this
    obtain ⟨h_u, h_e⟩ := hH_bd k hfk
    have h_δ := hZ_bd k hk1
    have hgap_k := (hgap k hk1).1
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hk_rpow : (k : ℝ) ^ (-(4 / 3 : ℝ)) = (k : ℝ) ^ (-(1 / 3 : ℝ)) / k := by
      conv_rhs => rw [div_eq_mul_inv, ← Real.rpow_neg_one (k : ℝ)]
      rw [← Real.rpow_add hk_pos]; congr 2; norm_num
    have h_diff : |airyZero k - uSite k| ≤ M_H * airyGap k / k := by
      have htri2 : |airyZero k - uSite k| ≤ |airyZero k - uWKB k| + |uSite k - uWKB k| := by
        have : airyZero k - uSite k = (airyZero k - uWKB k) - (uSite k - uWKB k) := by ring
        rw [this]; exact abs_sub _ _
      have h1 : |airyZero k - uSite k| ≤ (C_H + C_Z) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
        have : |airyZero k - uWKB k| ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ)) := h_δ
        linarith
      rw [hk_rpow] at h1
      calc |airyZero k - uSite k| ≤ (C_H + C_Z) * ((k : ℝ) ^ (-(1 / 3 : ℝ)) / k) := h1
        _ = M_H * (c₁ * (k : ℝ) ^ (-(1 / 3 : ℝ))) / k := by dsimp [M_H]; field_simp [hc₁.ne']
        _ ≤ M_H * airyGap k / k := by gcongr
    have h_eps : |epsU k| ≤ C_eps * airyGap k := by
      calc |epsU k| ≤ C_H * (k : ℝ) ^ (-(1 / 3 : ℝ)) := h_e
        _ = C_eps * (c₁ * (k : ℝ) ^ (-(1 / 3 : ℝ))) := by dsimp [C_eps]; field_simp [hc₁.ne']
        _ ≤ C_eps * airyGap k := by gcongr
    have h_abs1 : 2 * |airyZero k - uSite k| / ‖u - (airyZero k : ℂ)‖ ≤
        2 * M_H * (airyGap k / ‖u - (airyZero k : ℂ)‖) * (1 / (k : ℝ)) := by
      calc 2 * |airyZero k - uSite k| / ‖u - (airyZero k : ℂ)‖
          ≤ 2 * (M_H * airyGap k / k) / ‖u - (airyZero k : ℂ)‖ := by gcongr
        _ = 2 * M_H * (airyGap k / ‖u - (airyZero k : ℂ)‖) * (1 / (k : ℝ)) := by ring
    have h_abs2 : (|airyZero k - uSite k| ^ 2 + |epsU k| ^ 2) / ‖u - (airyZero k : ℂ)‖ ^ 2 ≤
        (M_H ^ 2 + C_eps ^ 2) * (airyGap k ^ 2 / ‖u - (airyZero k : ℂ)‖ ^ 2) := by
      have hk_ge1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have h_diff2 : |airyZero k - uSite k| ≤ M_H * airyGap k := by
        calc |airyZero k - uSite k| ≤ M_H * airyGap k / k := h_diff
          _ ≤ M_H * airyGap k / 1 := by gcongr; exact mul_nonneg (by positivity) (airyGap_pos hk1).le
          _ = M_H * airyGap k := div_one _
      have hs1 := pow_le_pow_left₀ (abs_nonneg _) h_diff2 2
      have hs2 := pow_le_pow_left₀ (abs_nonneg _) h_eps 2
      rw [mul_pow] at hs1 hs2
      calc (|airyZero k - uSite k| ^ 2 + |epsU k| ^ 2) / ‖u - (airyZero k : ℂ)‖ ^ 2
          ≤ ((M_H * airyGap k) ^ 2 + (C_eps * airyGap k) ^ 2) / ‖u - (airyZero k : ℂ)‖ ^ 2 := by gcongr
        _ = (M_H ^ 2 + C_eps ^ 2) * (airyGap k ^ 2 / ‖u - (airyZero k : ℂ)‖ ^ 2) := by ring
    exact (htri.trans (by linarith [hnorm, h_abs1, h_abs2])).trans (Real.add_one_le_exp _)
  have hprod_le : ∏ m ∈ s, ‖airyProdFactor uSite epsU (f + 1 + m) u‖ ≤
      Real.exp (∑ m ∈ s, (2 * M_H * (airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖) *
          (1 / ((f + 1 + m : ℕ) : ℝ)) +
        (M_H ^ 2 + C_eps ^ 2) * (airyGap (f + 1 + m) ^ 2 / ‖u - (airyZero (f + 1 + m) : ℂ)‖ ^ 2))) := by
    calc ∏ m ∈ s, ‖airyProdFactor uSite epsU (f + 1 + m) u‖
        ≤ ∏ m ∈ s, Real.exp _ := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun m _ => hfac_bd m)
      _ = Real.exp _ := (Real.exp_sum s _).symm
  refine hprod_le.trans (Real.exp_le_exp.mpr ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  set S_ker := ∑ m ∈ s, airyGap (f + 1 + m) ^ 2 / ‖u - (airyZero (f + 1 + m) : ℂ)‖ ^ 2
  have hS_ker_le : S_ker ≤ K_sum := by
    have hinj : Set.InjOn (fun m : ℕ => f + m) s := fun a _ b _ h => Nat.add_left_cancel h
    have hsub_sum : S_ker = ∑ j ∈ s.image (fun m => f + m),
        airyGap (j + 1) ^ 2 / ‖u - (airyZero (j + 1) : ℂ)‖ ^ 2 := by
      dsimp [S_ker]; rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun m _ => by
        rw [show f + m + 1 = f + 1 + m by ring]
    rw [hsub_sum]
    exact (hker_sum.sum_le_tsum _ fun _ _ => by positivity).trans hker_le
  have hS_inv_le : ∑ m ∈ s, (1 / ((f + 1 + m : ℕ) : ℝ)) ^ 2 ≤ Z₂ := by
    have hinj : Set.InjOn (fun m : ℕ => f + m) s := fun a _ b _ h => Nat.add_left_cancel h
    have hsub_sum : ∑ m ∈ s, (1 / ((f + 1 + m : ℕ) : ℝ)) ^ 2 =
        ∑ j ∈ s.image (fun m => f + m), 1 / ((j : ℝ) + 1) ^ 2 := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun m _ => by push_cast; rw [one_div, one_div, inv_pow]; congr 1; ring
    rw [hsub_sum]
    exact hZ₂.sum_le_tsum _ fun _ _ => by positivity
  have hcs : ∑ m ∈ s, 2 * M_H * (airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖) *
      (1 / ((f + 1 + m : ℕ) : ℝ)) ≤ 2 * M_H * √(K_sum * Z₂) := by
    have h1 : ∑ m ∈ s, 2 * M_H * (airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖) *
        (1 / ((f + 1 + m : ℕ) : ℝ)) =
        2 * M_H * ∑ m ∈ s, (airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖) *
          (1 / ((f + 1 + m : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    rw [h1]
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun m => airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖)
      (fun m => 1 / ((f + 1 + m : ℕ) : ℝ))
    have hsq_ker : ∑ m ∈ s, (airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖) ^ 2 = S_ker := by
      refine Finset.sum_congr rfl fun m _ => by rw [div_pow]
    rw [hsq_ker] at hcs0
    have hsqrt := Real.sqrt_le_sqrt hcs0
    have hnn : 0 ≤ ∑ m ∈ s, (airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖) *
        (1 / ((f + 1 + m : ℕ) : ℝ)) :=
      Finset.sum_nonneg fun m _ => mul_nonneg (div_nonneg (airyGap_pos (by omega)).le (norm_nonneg _)) (by positivity)
    rw [Real.sqrt_sq hnn] at hsqrt
    have hprod_le2 : S_ker * ∑ m ∈ s, (1 / ((f + 1 + m : ℕ) : ℝ)) ^ 2 ≤ K_sum * Z₂ :=
      mul_le_mul hS_ker_le hS_inv_le (Finset.sum_nonneg fun _ _ => by positivity) hK_sum.le
    exact mul_le_mul_of_nonneg_left (hsqrt.trans (Real.sqrt_le_sqrt hprod_le2)) (by positivity)
  have h2 : (M_H ^ 2 + C_eps ^ 2) * S_ker ≤ (M_H ^ 2 + C_eps ^ 2) * K_sum :=
    mul_le_mul_of_nonneg_left hS_ker_le (by positivity)
  linarith

/-- On each closed disc $\overline{D_n} = \overline{B}(a_n, \mathrm{gap}_n / 4)$ ($n \ge 1$),
$e(u) = \exp(-(4/3) \operatorname{Re} u^{3/2})$ satisfies $1 \le e(u) \le C_e$ with $C_e$ absolute. -/
private lemma airyEnv_on_gap_disc_bounds :
    ∃ C_e > 0, ∀ n : ℕ, 1 ≤ n → ∀ u : ℂ, ‖u - (airyZero n : ℂ)‖ ≤ airyGap n / 4 →
      1 ≤ airyEnv u ∧ airyEnv u ≤ C_e := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hgap⟩ := airyGap_bounds_exists
  set B := (3 / 2 : ℝ) * c₂ + 2 * (c₂ / 8) ^ 3
  refine ⟨Real.exp (4 / 3 * B), Real.exp_pos _, fun n hn u hu => ?_⟩
  have h_gap_bd : airyGap n ≤ c₂ * (n : ℝ) ^ (-(1 / 3 : ℝ)) := (hgap n hn).2
  have hx_lb : 1 ≤ -u.re := by
    have ha1 : (233 / 100 : ℝ) < -airyZero 1 := by linarith [airyZero_one.2]
    have han : (233 / 100 : ℝ) < -airyZero n := by
      rcases hn.eq_or_lt with rfl | h1n
      · exact ha1
      · linarith [airyZero_lt_of_lt le_rfl h1n]
    have hre : u.re - airyZero n ≤ airyGap n / 4 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hu)).2
    have hgap_ub : airyGap n / 4 ≤ 1 := by
      rcases hn.eq_or_lt with rfl | hn2
      · unfold airyGap
        have h1 := airyZero_one.2
        have h2 := airyZero_two.1
        linarith
      · have hg := (airyZero_gap_bounds hn2).2
        have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        have hpow : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
        have hgap1 : airyGap n ≤ 2.05 := by unfold airyGap; nlinarith
        linarith
    linarith
  have hx_ub : -u.re ≤ 4 * (n : ℝ) ^ (2 / 3 : ℝ) := by
    have hre : -(airyGap n / 4) ≤ u.re - airyZero n := (abs_le.mp ((Complex.abs_re_le_norm _).trans hu)).1
    rcases hn.eq_or_lt with rfl | hn2
    · simp only [Nat.cast_one, Real.one_rpow, mul_one]
      have h1 := airyZero_one.1
      have h2 := airyZero_two.1
      unfold airyGap at hre
      linarith
    · have han_ub := (airyZero_abs_bounds hn2).2
      have hgap2 : airyGap n ≤ 2.05 * (n : ℝ) ^ (-(1 / 3 : ℝ)) := (airyZero_gap_bounds hn2).2
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpow_le : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (n : ℝ) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      have hgap3 : airyGap n ≤ 2.05 * (n : ℝ) ^ (2 / 3 : ℝ) :=
        hgap2.trans (mul_le_mul_of_nonneg_left hpow_le (by norm_num))
      unfold airyGap at hgap3 hre
      linarith
  set x := -u.re
  set y := u.im
  set α := airySqrtRe u
  set β := (u ^ (1 / 2 : ℂ)).im
  have h1 := airySqrtRe_sq_sub u
  have h2 := airySqrtRe_mul_im u
  dsimp [airySqrtRe] at h1 h2
  have hα_nn : 0 ≤ α := cpow_half_re_nonneg u
  have hα2 : α ^ 2 - β ^ 2 = -x := by
    change (u ^ (1 / 2 : ℂ)).re ^ 2 - (u ^ (1 / 2 : ℂ)).im ^ 2 = -(-u.re)
    rw [neg_neg]; exact h1
  have hβ2 : x ≤ β ^ 2 := by linarith [sq_nonneg α]
  have h_re_cube : (u ^ (3 / 2 : ℂ)).re = α * (α ^ 2 - 3 * β ^ 2) := by
    rw [← cpow_half_cube, re_cube]
    change (u ^ (1 / 2 : ℂ)).re ^ 3 - 3 * (u ^ (1 / 2 : ℂ)).re * (u ^ (1 / 2 : ℂ)).im ^ 2 =
      (u ^ (1 / 2 : ℂ)).re * ((u ^ (1 / 2 : ℂ)).re ^ 2 - 3 * (u ^ (1 / 2 : ℂ)).im ^ 2)
    ring
  have h_re_nonpos : (u ^ (3 / 2 : ℂ)).re ≤ 0 := by
    rw [h_re_cube]
    have : α ^ 2 - 3 * β ^ 2 ≤ 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
    exact mul_nonpos_of_nonneg_of_nonpos hα_nn this
  have h_env_ge : 1 ≤ airyEnv u := by
    unfold airyEnv; exact Real.one_le_exp (by linarith)
  have h_im_le : |y| ≤ airyGap n / 4 := by
    have := (Complex.abs_im_le_norm (u - (airyZero n : ℂ))).trans hu
    simpa [y] using this
  have h_sqrt_x : √x ≤ |β| := by
    rw [← Real.sqrt_sq (abs_nonneg β), sq_abs]
    exact Real.sqrt_le_sqrt hβ2
  have h_sqrt_x_pos : 0 < √x := Real.sqrt_pos.mpr (by linarith)
  have h_α_le : α ≤ |y| / (2 * √x) := by
    have h2ab : 2 * α * |β| = |y| := by
      have : |2 * α * β| = |y| := congrArg abs h2
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num), abs_of_nonneg hα_nn] at this
      exact this
    rw [le_div_iff₀ (by positivity)]
    calc α * (2 * √x) ≤ α * (2 * |β|) := by gcongr
      _ = 2 * α * |β| := by ring
      _ = |y| := h2ab
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_α_rpow : α ≤ c₂ * (n : ℝ) ^ (-(1 / 3 : ℝ)) / (8 * √x) := by
    calc α ≤ |y| / (2 * √x) := h_α_le
      _ ≤ (airyGap n / 4) / (2 * √x) := by gcongr
      _ ≤ (c₂ * (n : ℝ) ^ (-(1 / 3 : ℝ)) / 4) / (2 * √x) := by gcongr
      _ = c₂ * (n : ℝ) ^ (-(1 / 3 : ℝ)) / (8 * √x) := by ring
  have h_α_sqrt : α * √x ≤ c₂ / 8 * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    calc α * √x ≤ (c₂ * (n : ℝ) ^ (-(1 / 3 : ℝ)) / (8 * √x)) * √x := by gcongr
      _ = c₂ / 8 * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by field_simp [h_sqrt_x_pos.ne']
  have h_sx_ub : √x ≤ 2 * (n : ℝ) ^ (1 / 3 : ℝ) := by
    have h1' := Real.sqrt_le_sqrt hx_ub
    have h4 : √(4 * (n : ℝ) ^ (2 / 3 : ℝ)) = 2 * (n : ℝ) ^ (1 / 3 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num), show √(4 : ℝ) = 2 by norm_num, Real.sqrt_eq_rpow,
        ← Real.rpow_mul hn_pos.le]
      norm_num
    linarith
  have h_α_ub : α ≤ c₂ / 8 := by
    have h1' : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by norm_num)
    have h2' : 1 ≤ √x := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hx_lb
    calc α ≤ c₂ * (n : ℝ) ^ (-(1 / 3 : ℝ)) / (8 * √x) := h_α_rpow
      _ ≤ c₂ * 1 / (8 * 1) := by gcongr
      _ = c₂ / 8 := by ring
  have h_cube_eq : -(u ^ (3 / 2 : ℂ)).re = 3 * α * x + 2 * α ^ 3 := by
    rw [h_re_cube, show β ^ 2 = x + α ^ 2 by linarith]
    ring
  have h_3ax : 3 * α * x ≤ (3 / 2 : ℝ) * c₂ := by
    have hx_sq : x = √x * √x := (Real.mul_self_sqrt (by linarith)).symm
    have hmul : (n : ℝ) ^ (-(1 / 3 : ℝ)) * (n : ℝ) ^ (1 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hn_pos, neg_add_cancel, Real.rpow_zero]
    calc 3 * α * x = 3 * (α * √x) * √x := by (conv_lhs => rw [hx_sq]); ring
      _ ≤ 3 * (c₂ / 8 * (n : ℝ) ^ (-(1 / 3 : ℝ))) * (2 * (n : ℝ) ^ (1 / 3 : ℝ)) := by
          gcongr
      _ = (3 / 4 : ℝ) * c₂ * ((n : ℝ) ^ (-(1 / 3 : ℝ)) * (n : ℝ) ^ (1 / 3 : ℝ)) := by ring
      _ = (3 / 4 : ℝ) * c₂ := by rw [hmul, mul_one]
      _ ≤ (3 / 2 : ℝ) * c₂ := by linarith
  have h_2a3 : 2 * α ^ 3 ≤ 2 * (c₂ / 8) ^ 3 := by
    gcongr
  have h_env_le : airyEnv u ≤ Real.exp (4 / 3 * B) := by
    unfold airyEnv
    refine Real.exp_le_exp.mpr ?_
    have : -(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re = 4 / 3 * (3 * α * x + 2 * α ^ 3) := by
      rw [← h_cube_eq]; ring
    rw [this]
    dsimp [B]
    linarith
  exact ⟨h_env_ge, h_env_le⟩

private lemma gap_disc_disjoint {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hkn : k ≠ n) :
    airyGap k / 4 + airyGap n / 4 < |airyZero k - airyZero n| := by
  have h_ordered : ∀ a b : ℕ, 1 ≤ a → a < b →
      airyGap a / 4 + airyGap b / 4 < airyZero a - airyZero b := by
    intro a b ha hab
    have hba : airyZero b ≤ airyZero (a + 1) := by
      rcases eq_or_lt_of_le (by omega : a + 1 ≤ b) with rfl | hlt
      · exact le_rfl
      · exact (airyZero_lt_of_lt (by omega) hlt).le
    have hgap_a : airyGap a ≤ airyZero a - airyZero b := by unfold airyGap; linarith
    rcases ha.eq_or_lt with rfl | ha2
    · have hg1 : airyGap 1 ≤ 251 / 100 := by
        unfold airyGap; linarith [airyZero_one.2, airyZero_two.1]
      have h12 : 165 / 100 ≤ airyGap 1 := by
        unfold airyGap; linarith [airyZero_one.1, airyZero_two.2]
      have hb2 : 2 ≤ b := by omega
      have hgb : airyGap b ≤ (41 / 20 : ℝ) * (2 : ℝ) ^ (-(1 / 3 : ℝ)) := by
        have h1 : airyGap b ≤ (41 / 20 : ℝ) * (b : ℝ) ^ (-(1 / 3 : ℝ)) := by
          unfold airyGap; linarith [(airyZero_gap_bounds hb2).2]
        have hpow : (b : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (2 : ℝ) ^ (-(1 / 3 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hb2) (by norm_num)
        linarith
      have h2pow : (2 : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 4 / 5 := by
        refine le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by norm_num) ?_
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          show -(1 / 3 : ℝ) * ((3 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
        norm_num
      linarith
    · have hga : (9 / 5 : ℝ) * ((a : ℝ) + 1) ^ (-(1 / 3 : ℝ)) ≤ airyGap a := by
        unfold airyGap; linarith [(airyZero_gap_bounds ha2).1]
      have hgb : airyGap b ≤ (41 / 20 : ℝ) * (b : ℝ) ^ (-(1 / 3 : ℝ)) := by
        unfold airyGap; linarith [(airyZero_gap_bounds (by omega : 2 ≤ b)).2]
      have hpow : (b : ℝ) ^ (-(1 / 3 : ℝ)) ≤ ((a : ℝ) + 1) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast (by omega : a + 1 ≤ b)) (by norm_num)
      have hgb' : airyGap b ≤ (41 / 20 : ℝ) * ((a : ℝ) + 1) ^ (-(1 / 3 : ℝ)) := by linarith
      have hgab : airyGap b ≤ (41 / 36 : ℝ) * airyGap a := by linarith
      have hga_pos := airyGap_pos ha
      linarith
  rcases lt_or_gt_of_ne hkn with hlt | hgt
  · rw [abs_of_nonneg (sub_nonneg.mpr (airyZero_lt_of_lt hk hlt).le)]
    exact h_ordered k n hk hlt
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (airyZero_lt_of_lt hn hgt).le), add_comm]
    exact h_ordered n k hn hgt

private lemma ratio_prefix_bound (f : ℕ) (uF : ℝ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C_rat > 0, ∀ u : ℂ, (∀ k : ℕ, 1 ≤ k → c₀ * airyGap k ≤ ‖u - (airyZero k : ℂ)‖) →
      ‖(u - (uF : ℂ)) / (∏ k ∈ Finset.Icc 1 f, (u - (airyZero k : ℂ)) ^ 2)‖ ≤
        C_rat * (1 + ‖u‖) ^ (1 - 2 * (f : ℝ)) := by
  set M_k : ℕ → ℝ := fun k => 1 + (1 + |airyZero k|) / (c₀ * airyGap k)
  have hM_pos : ∀ k : ℕ, 1 ≤ k → 0 < M_k k := fun k hk => by
    dsimp [M_k]; have := airyGap_pos hk; positivity
  set C_prod : ℝ := ∏ k ∈ Finset.Icc 1 f, M_k k ^ 2
  have hC_prod_pos : 0 < C_prod := Finset.prod_pos fun k hk =>
    pow_pos (hM_pos k (Finset.mem_Icc.mp hk).1) 2
  set C_rat : ℝ := (1 + |uF|) * C_prod
  refine ⟨C_rat, by positivity, fun u hu => ?_⟩
  have hnum : ‖u - (uF : ℂ)‖ ≤ (1 + |uF|) * (1 + ‖u‖) := by
    have h1 : ‖u - (uF : ℂ)‖ ≤ ‖u‖ + |uF| := by
      have := norm_sub_le u (uF : ℂ)
      rwa [Complex.norm_real, Real.norm_eq_abs] at this
    nlinarith [norm_nonneg u, abs_nonneg uF]
  have hden_term : ∀ k ∈ Finset.Icc 1 f,
      1 + ‖u‖ ≤ M_k k * ‖u - (airyZero k : ℂ)‖ := fun k hk => by
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hgap := hu k hk1
    have hgap_pos : 0 < c₀ * airyGap k := mul_pos hc₀ (airyGap_pos hk1)
    have h1 : 1 + ‖u‖ ≤ ‖u - (airyZero k : ℂ)‖ + (1 + |airyZero k|) := by
      have htri := norm_add_le (u - (airyZero k : ℂ)) (airyZero k : ℂ)
      rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at htri
      linarith
    have h2 : 1 + |airyZero k| ≤ ((1 + |airyZero k|) / (c₀ * airyGap k)) * ‖u - (airyZero k : ℂ)‖ := by
      calc 1 + |airyZero k|
          = ((1 + |airyZero k|) / (c₀ * airyGap k)) * (c₀ * airyGap k) :=
            (div_mul_cancel₀ (1 + |airyZero k|) hgap_pos.ne').symm
        _ ≤ ((1 + |airyZero k|) / (c₀ * airyGap k)) * ‖u - (airyZero k : ℂ)‖ := by gcongr
    calc 1 + ‖u‖ ≤ ‖u - (airyZero k : ℂ)‖ + (1 + |airyZero k|) := h1
      _ ≤ ‖u - (airyZero k : ℂ)‖ + ((1 + |airyZero k|) / (c₀ * airyGap k)) * ‖u - (airyZero k : ℂ)‖ := by
          gcongr
      _ = M_k k * ‖u - (airyZero k : ℂ)‖ := by dsimp [M_k]; ring
  have hden_sq : ∀ k ∈ Finset.Icc 1 f,
      (1 + ‖u‖) ^ 2 ≤ M_k k ^ 2 * ‖u - (airyZero k : ℂ)‖ ^ 2 := fun k hk => by
    have h1 := pow_le_pow_left₀ (by positivity) (hden_term k hk) 2
    rwa [mul_pow] at h1
  have hden_prod : (1 + ‖u‖) ^ (2 * f) ≤
      C_prod * ∏ k ∈ Finset.Icc 1 f, ‖u - (airyZero k : ℂ)‖ ^ 2 := by
    have h1 := Finset.prod_le_prod₀ (fun _ _ => by positivity) hden_sq
    have hcard : (Finset.Icc 1 f).card = f := by simp
    rw [Finset.prod_const, hcard, ← pow_mul, Finset.prod_mul_distrib] at h1
    exact h1
  have hden_pos : 0 < ∏ k ∈ Finset.Icc 1 f, ‖u - (airyZero k : ℂ)‖ ^ 2 := by
    refine Finset.prod_pos fun k hk => sq_pos_of_pos ?_
    have hk1 := (Finset.mem_Icc.mp hk).1
    exact lt_of_lt_of_le (mul_pos hc₀ (airyGap_pos hk1)) (hu k hk1)
  have h1u : 0 < 1 + ‖u‖ := by positivity
  rw [norm_div, norm_prod]
  simp_rw [norm_pow]
  calc ‖u - (uF : ℂ)‖ / ∏ k ∈ Finset.Icc 1 f, ‖u - (airyZero k : ℂ)‖ ^ 2
      ≤ ((1 + |uF|) * (1 + ‖u‖)) / ((1 + ‖u‖) ^ (2 * f) / C_prod) := by
        gcongr
        rw [div_le_iff₀ hC_prod_pos]
        linarith
    _ = C_rat * ((1 + ‖u‖) / (1 + ‖u‖) ^ (2 * f)) := by
        dsimp [C_rat]; field_simp [hC_prod_pos.ne']
    _ = C_rat * (1 + ‖u‖) ^ (1 - 2 * (f : ℝ)) := by
        congr 1
        have h2f : (1 + ‖u‖) ^ (2 * f) = (1 + ‖u‖) ^ ((2 * f : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
        rw [h2f]
        conv_lhs => arg 1; rw [← Real.rpow_one (1 + ‖u‖)]
        rw [← Real.rpow_sub h1u]
        push_cast; rfl

/-- **General growth bound for $W^{(f)}(u)$** (`ut:G` for $f = 1$):
$\|W^{(f)}(u)\| \le C (1 + \|u\|)^{-(2f - 1/2)} e(u)$ for all $u \in \mathbb{C}$. -/
theorem airyWindowProd_bound (f : ℕ) (hf : 1 ≤ f) (uF : ℝ) (uSite epsU : ℕ → ℝ)
    (hH : AiryProdTailHypothesis f uSite epsU) :
    ∃ C > 0, ∀ u : ℂ, ‖airyWindowProd f uF uSite epsU u‖ ≤
      C * (1 + ‖u‖) ^ (-((2 * (f : ℝ) - 1 / 2))) * airyEnv u := by
  obtain ⟨C_tail, hC_tail, htail_bd⟩ :=
    airyProdTail_norm_le_of_avoid f uSite epsU hH (c₀ := 1 / 4) (by norm_num)
  obtain ⟨C_rat, hC_rat, hrat_bd⟩ := ratio_prefix_bound f uF (c₀ := 1 / 4) (by norm_num)
  obtain ⟨C_env, hC_env, henv_disc⟩ := airyEnv_on_gap_disc_bounds
  set C_out := 9 * C_rat * C_tail
  have hC_out : 0 < C_out := by positivity
  have h_out : ∀ u : ℂ, (∀ k : ℕ, 1 ≤ k → airyGap k / 4 ≤ ‖u - (airyZero k : ℂ)‖) →
      ‖airyWindowProd f uF uSite epsU u‖ ≤
        C_out * (1 + ‖u‖) ^ (-((2 * (f : ℝ) - 1 / 2))) * airyEnv u := by
    intro u hu
    have hu' : ∀ k : ℕ, 1 ≤ k → (1 / 4 : ℝ) * airyGap k ≤ ‖u - (airyZero k : ℂ)‖ := fun k hk => by
      linarith [hu k hk]
    have hu_ne : ∀ k : ℕ, 1 ≤ k → u ≠ (airyZero k : ℂ) := fun k hk h => by
      have := hu k hk
      rw [h, sub_self, norm_zero] at this
      linarith [airyGap_pos hk]
    rw [airyWindowProd_eq_of_ne f uF uSite epsU hu_ne]
    have hai := airyAiC_norm_sq_le u
    have hrat := hrat_bd u hu'
    have htail := htail_bd u hu'
    have h1u : 0 < 1 + ‖u‖ := by positivity
    have henv_nn : 0 ≤ airyEnv u := (airyEnv_pos u).le
    have h_eq : -airyAiC u ^ 2 * (u - (uF : ℂ)) /
        (∏ k ∈ Finset.Icc 1 f, (u - (airyZero k : ℂ)) ^ 2) * airyProdTail f uSite epsU u =
        (-airyAiC u ^ 2) * ((u - (uF : ℂ)) / ∏ k ∈ Finset.Icc 1 f, (u - (airyZero k : ℂ)) ^ 2) *
          airyProdTail f uSite epsU u := by ring
    rw [h_eq, norm_mul, norm_mul, norm_neg, norm_pow]
    have hrpow : (1 + ‖u‖) ^ (-(1 / 2 : ℝ)) * (1 + ‖u‖) ^ (1 - 2 * (f : ℝ)) =
        (1 + ‖u‖) ^ (-((2 * (f : ℝ) - 1 / 2))) := by
      rw [← Real.rpow_add h1u]
      congr 1; ring
    calc ‖airyAiC u‖ ^ 2 * ‖(u - (uF : ℂ)) / ∏ k ∈ Finset.Icc 1 f, (u - (airyZero k : ℂ)) ^ 2‖ *
          ‖airyProdTail f uSite epsU u‖
        ≤ (9 * (1 + ‖u‖) ^ (-(1 / 2 : ℝ)) * airyEnv u) *
            (C_rat * (1 + ‖u‖) ^ (1 - 2 * (f : ℝ))) * C_tail := by
          gcongr
      _ = C_out * ((1 + ‖u‖) ^ (-(1 / 2 : ℝ)) * (1 + ‖u‖) ^ (1 - 2 * (f : ℝ))) * airyEnv u := by
          dsimp [C_out]; ring
      _ = C_out * (1 + ‖u‖) ^ (-((2 * (f : ℝ) - 1 / 2))) * airyEnv u := by rw [hrpow]
  set C := (3 : ℝ) ^ (2 * (f : ℝ) - 1 / 2) * C_env * C_out
  refine ⟨C, by positivity, fun u => ?_⟩
  by_cases hu : ∀ k : ℕ, 1 ≤ k → airyGap k / 4 ≤ ‖u - (airyZero k : ℂ)‖
  · refine (h_out u hu).trans ?_
    have h13 : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * (f : ℝ) - 1 / 2) := by
      refine Real.one_le_rpow (by norm_num) ?_
      have : (1 : ℝ) ≤ f := by exact_mod_cast hf
      linarith
    have h1e : 1 ≤ C_env := by
      have := henv_disc 1 le_rfl (airyZero 1 : ℂ)
        (by rw [sub_self, norm_zero]; exact div_nonneg (airyGap_pos le_rfl).le (by norm_num))
      linarith [this.1, this.2]
    have hle : C_out ≤ C := by
      dsimp [C]
      calc C_out = 1 * 1 * C_out := by ring
        _ ≤ (3 : ℝ) ^ (2 * (f : ℝ) - 1 / 2) * C_env * C_out := by gcongr
    gcongr
    exact (airyEnv_pos u).le
  · push_neg at hu
    obtain ⟨n, hn, hu_in⟩ := hu
    set r := airyGap n / 4
    have hr_pos : 0 < r := by dsimp [r]; linarith [airyGap_pos hn]
    have hdiff_W := airyWindowProd_differentiable f hf uF uSite epsU hH
    have hdc : DiffContOnCl ℂ (airyWindowProd f uF uSite epsU) (ball (airyZero n : ℂ) r) :=
      hdiff_W.differentiableOn.diffContOnCl
    have hfr_out : ∀ w ∈ frontier (ball (airyZero n : ℂ) r),
        ∀ k : ℕ, 1 ≤ k → airyGap k / 4 ≤ ‖w - (airyZero k : ℂ)‖ := by
      intro w hw k hk
      rw [frontier_ball (airyZero n : ℂ) hr_pos.ne'] at hw
      have hwn : ‖w - (airyZero n : ℂ)‖ = r := mem_sphere_iff_norm.mp hw
      by_cases hkn : k = n
      · subst hkn; exact hwn.ge
      · have hdisj := gap_disc_disjoint hk hn hkn
        have h_ak : ‖(airyZero k : ℂ) - (airyZero n : ℂ)‖ ≤ ‖w - (airyZero k : ℂ)‖ + ‖w - (airyZero n : ℂ)‖ := by
          have := norm_add_le ((airyZero k : ℂ) - w) (w - (airyZero n : ℂ))
          rw [sub_add_sub_cancel, norm_sub_rev (airyZero k : ℂ) w] at this
          exact this
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hwn] at h_ak
        dsimp [r] at h_ak
        linarith
    have hgap_le_4 : airyGap n ≤ 4 := by
      rcases hn.eq_or_lt with rfl | hn2
      · unfold airyGap; linarith [airyZero_one.2, airyZero_two.1]
      · have hg : airyGap n ≤ (41 / 20 : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
          unfold airyGap; linarith [(airyZero_gap_bounds hn2).2]
        have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        have hpow : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
        linarith
    have hbd_fr : ∀ w ∈ frontier (ball (airyZero n : ℂ) r),
        ‖airyWindowProd f uF uSite epsU w‖ ≤ C * (1 + ‖u‖) ^ (-((2 * (f : ℝ) - 1 / 2))) * airyEnv u := by
      intro w hw
      have h_w_out := h_out w (hfr_out w hw)
      rw [frontier_ball (airyZero n : ℂ) hr_pos.ne'] at hw
      have hwn : ‖w - (airyZero n : ℂ)‖ = r := mem_sphere_iff_norm.mp hw
      have henv_w := (henv_disc n hn w hwn.le).2
      have henv_u := (henv_disc n hn u hu_in.le).1
      have hnorm_uw : 1 + ‖u‖ ≤ 3 * (1 + ‖w‖) := by
        have h1 : ‖u - w‖ ≤ ‖u - (airyZero n : ℂ)‖ + ‖w - (airyZero n : ℂ)‖ := by
          have := norm_sub_le (u - (airyZero n : ℂ)) (w - (airyZero n : ℂ))
          simpa [sub_sub_sub_cancel_right] using this
        have h2 : ‖u‖ ≤ ‖w‖ + ‖u - w‖ := by
          have := norm_add_le w (u - w)
          simpa [add_sub_cancel] using this
        have h_r2 : 2 * r ≤ 2 := by dsimp [r]; linarith
        linarith [norm_nonneg w]
      have h_exp_pos : 0 < 2 * (f : ℝ) - 1 / 2 := by
        have : (1 : ℝ) ≤ f := by exact_mod_cast hf
        linarith
      have hrpow_le : (1 + ‖w‖) ^ (-((2 * (f : ℝ) - 1 / 2))) ≤
          (3 : ℝ) ^ (2 * (f : ℝ) - 1 / 2) * (1 + ‖u‖) ^ (-((2 * (f : ℝ) - 1 / 2))) := by
        have h1w : 0 < 1 + ‖w‖ := by positivity
        have h1u : 0 < 1 + ‖u‖ := by positivity
        have hpow := Real.rpow_le_rpow_of_nonpos h1u hnorm_uw (neg_nonpos.mpr h_exp_pos.le)
        rw [Real.mul_rpow (by norm_num) h1w.le, Real.rpow_neg (by norm_num)] at hpow
        have h3pos : 0 < (3 : ℝ) ^ (2 * (f : ℝ) - 1 / 2) := by positivity
        calc (1 + ‖w‖) ^ (-((2 * (f : ℝ) - 1 / 2)))
            = (3 : ℝ) ^ (2 * (f : ℝ) - 1 / 2) *
                (((3 : ℝ) ^ (2 * (f : ℝ) - 1 / 2))⁻¹ * (1 + ‖w‖) ^ (-((2 * (f : ℝ) - 1 / 2)))) := by
              field_simp [h3pos.ne']
          _ ≤ (3 : ℝ) ^ (2 * (f : ℝ) - 1 / 2) * (1 + ‖u‖) ^ (-((2 * (f : ℝ) - 1 / 2))) := by
              gcongr
      calc ‖airyWindowProd f uF uSite epsU w‖
          ≤ C_out * (1 + ‖w‖) ^ (-((2 * (f : ℝ) - 1 / 2))) * airyEnv w := h_w_out
        _ ≤ C_out * ((3 : ℝ) ^ (2 * (f : ℝ) - 1 / 2) * (1 + ‖u‖) ^ (-((2 * (f : ℝ) - 1 / 2)))) *
              (C_env * airyEnv u) := by
            have henv_w_nn : 0 ≤ airyEnv w := (airyEnv_pos w).le
            have henv_le_mul : airyEnv w ≤ C_env * airyEnv u := by
              calc airyEnv w ≤ C_env := henv_w
                _ = C_env * 1 := (mul_one C_env).symm
                _ ≤ C_env * airyEnv u := mul_le_mul_of_nonneg_left henv_u hC_env.le
            gcongr
        _ = C * (1 + ‖u‖) ^ (-((2 * (f : ℝ) - 1 / 2))) * airyEnv u := by dsimp [C]; ring
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc hbd_fr
      (subset_closure (mem_ball_iff_norm.mpr hu_in))

/-- **Lemma G (`ut:G`), entireness**: $W$ is entire on $\mathbb{C}$. -/
theorem designWindowW_differentiable (N : ℕ) (etaStar d : ℝ) :
    Differentiable ℂ (designWindowW N etaStar d) :=
  airyWindowProd_differentiable 1 le_rfl (airyZero 1 - d) (designSiteU N) (designWidthU N etaStar)
    (design_tail_hypothesis N etaStar)

/-- **Lemma G (`ut:G`), reality on $\mathbb{R}$**: $W(x) \in \mathbb{R}$ for $x \in \mathbb{R}$. -/
lemma designWindowW_im_eq_zero (N : ℕ) (etaStar d x : ℝ) :
    (designWindowW N etaStar d (x : ℂ)).im = 0 :=
  airyWindowProd_im_eq_zero 1 (airyZero 1 - d) (designSiteU N) (designWidthU N etaStar)
    (design_tail_hypothesis N etaStar) x

/-- **Lemma G (`ut:G`), uniform envelope**: $\|W(u)\| \le C(N, \eta_*, d)(1 + \|u\|)^{-3/2} e(u)$
for all $u \in \mathbb{C}$. -/
theorem lemma_G_bound (N : ℕ) (etaStar d : ℝ) :
    ∃ C > 0, ∀ u : ℂ, ‖designWindowW N etaStar d u‖ ≤ C * (1 + ‖u‖) ^ (-(3 / 2 : ℝ)) * airyEnv u := by
  obtain ⟨C, hC, hbd⟩ := airyWindowProd_bound 1 le_rfl (airyZero 1 - d) (designSiteU N)
    (designWidthU N etaStar) (design_tail_hypothesis N etaStar)
  refine ⟨C, hC, fun u => ?_⟩
  have hu := hbd u
  rw [show -((2 * ((1 : ℕ) : ℝ) - 1 / 2)) = -(3 / 2 : ℝ) by norm_num] at hu
  exact hu

/-- **Lemma G (`ut:G`), integrability**: $W \in L^1(\mathbb{R})$. -/
theorem lemma_G_integrable (N : ℕ) (etaStar d : ℝ) :
    Integrable (fun x : ℝ => designWindowW N etaStar d (x : ℂ)) := by
  obtain ⟨C, hC, hbd⟩ := lemma_G_bound N etaStar d
  exact airy_integrable_real (designWindowW_differentiable N etaStar d) hC.le (by norm_num) hbd

/-- **Lemma G (`ut:G`), circle ratio**: for any $c_0 > 0$, there is $C > 0$ such that on every
gap-avoiding point $u \ne 0$ with $\|u - a_k\| \ge c_0\,\mathrm{gap}_k$ for all $k \ge 1$,
$\|W(u) / \Ai(u)^2\| \le C / \|u\|$. -/
theorem lemma_G_circle_ratio (N : ℕ) (etaStar d : ℝ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C > 0, ∀ u : ℂ, u ≠ 0 →
      (∀ k : ℕ, 1 ≤ k → c₀ * airyGap k ≤ ‖u - (airyZero k : ℂ)‖) →
      ‖designWindowW N etaStar d u / airyAiC u ^ 2‖ ≤ C / ‖u‖ := by
  obtain ⟨C_tail, hC_tail, htail⟩ := airyProdTail_norm_le_of_avoid 1 (designSiteU N)
    (designWidthU N etaStar) (design_tail_hypothesis N etaStar) hc₀
  obtain ⟨C_rat, hC_rat, hrat⟩ := ratio_prefix_bound 1 (airyZero 1 - d) hc₀
  refine ⟨C_rat * C_tail, by positivity, fun u hu0 hu => ?_⟩
  have hu_ne : ∀ k : ℕ, 1 ≤ k → u ≠ (airyZero k : ℂ) := fun k hk h => by
    have := hu k hk
    rw [h, sub_self, norm_zero] at this
    linarith [mul_pos hc₀ (airyGap_pos hk)]
  have hai_ne : airyAiC u ≠ 0 := by
    intro h0
    obtain ⟨k, hkeq⟩ := FormalResearch.Hadamard.exists_airyA_eq h0
    exact hu_ne (k + 1) (by omega) hkeq.symm
  unfold designWindowW
  rw [airyWindowProd_eq_of_ne 1 (airyZero 1 - d) (designSiteU N) (designWidthU N etaStar) hu_ne]
  have h_simp : -airyAiC u ^ 2 * (u - ((airyZero 1 - d : ℝ) : ℂ)) /
      (∏ k ∈ Finset.Icc 1 1, (u - (airyZero k : ℂ)) ^ 2) *
      airyProdTail 1 (designSiteU N) (designWidthU N etaStar) u / airyAiC u ^ 2 =
      -((u - ((airyZero 1 - d : ℝ) : ℂ)) / (∏ k ∈ Finset.Icc 1 1, (u - (airyZero k : ℂ)) ^ 2)) *
        airyProdTail 1 (designSiteU N) (designWidthU N etaStar) u := by
    have hai2 : airyAiC u ^ 2 ≠ 0 := pow_ne_zero 2 hai_ne
    field_simp [hai2]
  rw [h_simp, norm_mul, norm_neg]
  have h1 := hrat u hu
  have h2 := htail u hu
  have h1u : (1 + ‖u‖) ^ (1 - 2 * ((1 : ℕ) : ℝ)) ≤ ‖u‖⁻¹ := by
    have h_exp : 1 - 2 * ((1 : ℕ) : ℝ) = -1 := by norm_num
    rw [h_exp, Real.rpow_neg_one]
    exact inv_anti₀ (norm_pos_iff.mpr hu0) (by linarith [norm_nonneg u])
  calc ‖(u - ((airyZero 1 - d : ℝ) : ℂ)) / ∏ k ∈ Finset.Icc 1 1, (u - (airyZero k : ℂ)) ^ 2‖ *
        ‖airyProdTail 1 (designSiteU N) (designWidthU N etaStar) u‖
      ≤ (C_rat * (1 + ‖u‖) ^ (1 - 2 * ((1 : ℕ) : ℝ))) * C_tail := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ ≤ (C_rat * ‖u‖⁻¹) * C_tail := by gcongr
    _ = C_rat * C_tail / ‖u‖ := by rw [div_eq_mul_inv]; ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.designWindowW_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Window.designWindowW_differentiable

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.lemma_G_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Window.lemma_G_bound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.lemma_G_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Window.lemma_G_integrable

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.lemma_G_circle_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Window.lemma_G_circle_ratio

end FormalResearch.ModularBootstrap.Upper.Window
