module

public import FormalResearch.ModularBootstrap.Upper.Assembly.DisplacedFamily
public import FormalResearch.ModularBootstrap.Upper.Assembly.DisplacedDesign

/-!
# The omitted family by far-first-site designs, and `Σ` at Virasoro without hypotheses

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` (`sr:Sigma` Step 6, the sign law of §2).

`sr:Sigma` Step 6 uses designs with `f - 1` omitted sites (`f ≥ 2`).  The Lean proof replaces them by
**far-first-site designs with `f = 1`** (this file): for `m ≥ 1` the design has its simple zero (first kept
site) at `u_1 = a_{m+1}` (`d = a_1 - a_{m+1}`), the sites `2, …, m` displaced by one fixed shift `ρ_m > 0`
with `2 ρ_m ≤ |a_s - a_j|` (`s ≠ j ≤ m`), the sites `m + 1 < k ≤ N` ideal with detuning `η_*`, and the reference
tail beyond `N`.  The sign law of `profWin` gives `Π_i < 0` (`i < m`, i.e. the zeros `a_1, …, a_m` lie above `u_f`),
`Π_m = 0`, `Π_i > 0` beyond.  The bounds of the omitted-site designs are replaced by

* `pi_lower`: `-Π_1 = d R_1 ≥ d (1/4)^m / 2` and, for `2 ≤ s ≤ m`, `-Π_s = Π_s(0)(d/|a_s - a_1| - 1)` with
  `Π_s(0) ≥ ρ_m² (1/4)^m / (2|a_s - a_1|)` (`exists_dispR1_lower`, `exists_dispPi0_lower_D`: the
  displaced factors are `≥ 1/4` because `2ρ_m ≤ |a_s - a_j|`, the ideal ones `≥ 1`, the tail `≥ 1/2`);
* `tail_small`: `∑_{i > m} Π_i ≤ ∑_{n ≥ m + 2} Π_n(0) = O(η_*² + N^{-1/3})` (`exists_dispRest_le_D`).

The comb side is `Assembly.DisplacedDesign` (`displacedPropertyP_virasoro`: Property `sr:P` for every
first-site shift `d ∈ ℝ` and finitely many displaced sites), so no `f ≥ 2` comb is needed.

* `farFamily`: `OmittedFamily (designClass ∪ displacedClassX)`.
* **`virasoro_sigma_unconditional`**: Theorem `Σ` at Virasoro for the extremal measures, no hypothesis.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Ramped

/-! ### The fixed displacement -/

lemma airyZero_le_of_le' {i f : ℕ} (hi : 1 ≤ i) (h : i ≤ f) : airyZero f ≤ airyZero i := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (airyZero_lt_of_lt hi h).le

lemma gap_le_abs_airyZero_succ {i f : ℕ} (hi : 1 ≤ i) (hif : i ≤ f) :
    airyZero f - airyZero (f + 1) ≤ |airyZero (f + 1) - airyZero i| := by
  have h1 := airyZero_le_of_le' hi hif
  rw [abs_sub_comm, abs_of_nonneg (by linarith [airyZero_lt_of_lt (by omega : 1 ≤ i) (by omega : i < f + 1)])]
  linarith

/-- A uniform separation of the zeros `a_1, …, a_f`: `2ρ ≤ |a_s - a_j|` for `s ≠ j` in `[1, f]`. -/
lemma exists_farSep (f : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s j : ℕ, 1 ≤ s → s ≤ f → 1 ≤ j → j ≤ f → s ≠ j →
      2 * ρ ≤ |airyZero s - airyZero j| := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · exact ⟨1, one_pos, fun s j hs hsf => by omega⟩
  induction f, hf using Nat.le_induction with
  | base =>
    exact ⟨1, one_pos, fun s j hs hsf hj hjf hne => by omega⟩
  | succ f hf ih =>
    obtain ⟨ρ, hρ, h⟩ := ih
    have hgap : 0 < airyZero f - airyZero (f + 1) := sub_pos.2 (airyZero_strictAnti hf)
    refine ⟨min ρ ((airyZero f - airyZero (f + 1)) / 2), lt_min hρ (by positivity),
      fun s j hs hsf hj hjf hne => ?_⟩
    have hm1 : min ρ ((airyZero f - airyZero (f + 1)) / 2) ≤ ρ := min_le_left _ _
    have hm2 : min ρ ((airyZero f - airyZero (f + 1)) / 2) ≤ (airyZero f - airyZero (f + 1)) / 2 :=
      min_le_right _ _
    by_cases hsj : s ≤ f ∧ j ≤ f
    · have := h s j hs hsj.1 hj hsj.2 hne
      linarith
    · have hcase : (s = f + 1 ∧ j ≤ f) ∨ (j = f + 1 ∧ s ≤ f) := by omega
      rcases hcase with ⟨rfl, hjf'⟩ | ⟨rfl, hsf'⟩
      · have := gap_le_abs_airyZero_succ hj hjf'
        linarith
      · have := gap_le_abs_airyZero_succ hs hsf'
        rw [abs_sub_comm] at this
        linarith

/-- The fixed shift `ρ_f` of the displaced sites `2, …, f`. -/
noncomputable def farRho (f : ℕ) : ℝ := (exists_farSep f).choose

lemma farRho_pos (f : ℕ) : 0 < farRho f := (exists_farSep f).choose_spec.1

lemma farRho_sep {f s j : ℕ} (hs : 1 ≤ s) (hsf : s ≤ f) (hj : 1 ≤ j) (hjf : j ≤ f) (hne : s ≠ j) :
    2 * farRho f ≤ |airyZero s - airyZero j| :=
  (exists_farSep f).choose_spec.2 s j hs hsf hj hjf hne

/-- The displacement vector: `ρ_f` at the sites `2 ≤ k ≤ f`, `0` elsewhere. -/
noncomputable def farE (f : ℕ) (k : ℕ) : ℝ := if 2 ≤ k ∧ k ≤ f then farRho f else 0

lemma farE_of_mem {f k : ℕ} (h2 : 2 ≤ k) (hk : k ≤ f) : farE f k = farRho f := by
  unfold farE; simp [h2, hk]

lemma farE_of_gt {f k : ℕ} (h : f < k) : farE f k = 0 := by
  unfold farE; simp [show ¬ k ≤ f by omega]

lemma farE_of_lt {f k : ℕ} (h : k < 2) : farE f k = 0 := by
  unfold farE; simp [show ¬ 2 ≤ k by omega]

/-- The first-site shift `d = a_1 - a_{f+1}` (first kept site `u_1 = a_{f+1}`). -/
noncomputable def farD (f : ℕ) : ℝ := airyZero 1 - airyZero (f + 1)

lemma farD_pos {f : ℕ} (hf : 1 ≤ f) : 0 < farD f :=
  sub_pos.2 (airyZero_lt_of_lt le_rfl (by omega))

lemma airyZero_sub_farD (f : ℕ) : airyZero 1 - farD f = airyZero (f + 1) := by
  unfold farD; ring

/-- `((x - ρ)² + ε²)/x² ≥ 1/4` when `2ρ ≤ |x|`: a displaced factor is not small. -/
lemma far_factor_ge_quarter {x ρ ε : ℝ} (hρ : 0 < ρ) (hx : 2 * ρ ≤ |x|) :
    1 / 4 ≤ ((x - ρ) ^ 2 + ε ^ 2) / x ^ 2 := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h, abs_zero] at hx; linarith
  have hxsq : 0 < x ^ 2 := by positivity
  rw [le_div_iff₀ hxsq]
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h] at hx; nlinarith [sq_nonneg ε]
  · rw [h] at hx; nlinarith [sq_nonneg ε]

/-! ### Lower bounds uniform in the cut -/

lemma far_factor_dispSite {f N : ℕ} (hfN : f ≤ N) (η : ℝ) {s j : ℕ} (hs : 1 ≤ s) (hsf : s ≤ f)
    (hj2 : 2 ≤ j) (hjf : j ≤ f) (hne : s ≠ j) :
    1 / 4 ≤ profRealFactor (dispSite N (farE f)) (designWidthU N η) s j := by
  have hsite : dispSite N (farE f) j = airyZero j + farRho f := by
    unfold dispSite; rw [farE_of_mem hj2 hjf]; simp [designSiteU, show j ≤ N by omega]
  unfold profRealFactor
  rw [hsite]
  have := far_factor_ge_quarter (ε := designWidthU N η j) (farRho_pos f)
    (farRho_sep hs hsf (by omega) hjf hne)
  have e : airyZero s - (airyZero j + farRho f) = (airyZero s - airyZero j) - farRho f := by ring
  rw [e]
  exact this

/-- The lower bounds of `R_1` and of `Π_s(0)` (`2 ≤ s ≤ f`) for the far-first-site designs, for every cut
`N ≥ J` and every `η_* ∈ (0, 1/4]`. -/
lemma far_lowers (f : ℕ) :
    ∃ J : ℕ, f ≤ J ∧ ∀ N : ℕ, J ≤ N → ∀ η : ℝ, 0 < η → η ≤ 1 / 4 →
      (1 / 4 : ℝ) ^ f / 2 ≤ profR1 (dispSite N (farE f)) (designWidthU N η) ∧
      ∀ s : ℕ, 2 ≤ s → s ≤ f →
        farRho f ^ 2 * ((1 / 4 : ℝ) ^ f / 2) / |airyZero s - airyZero 1| ≤
          profPi0 (dispSite N (farE f)) (designWidthU N η) s := by
  obtain ⟨J₁, hJ₁, h₁⟩ := exists_dispR1_lower f
  have hev : ∀ᶠ N : ℕ in atTop, ∀ s ∈ Finset.Icc 2 f, ∀ η : ℝ, 0 < η → η ≤ 1 / 4 →
      farRho f ^ 2 * ((1 / 4 : ℝ) ^ f / 2) / |airyZero s - airyZero 1| ≤
        profPi0 (dispSite N (farE f)) (designWidthU N η) s := by
    refine (Finset.eventually_all (Finset.Icc 2 f)).2 fun s hs => ?_
    obtain ⟨hs2, hsf⟩ := Finset.mem_Icc.mp hs
    obtain ⟨J, hJ, h⟩ := exists_dispPi0_lower_D hs2 f hsf
    filter_upwards [eventually_ge_atTop J] with N hN η hη0 hη1
    have := h N hN η (farE f) hη0 hη1 (fun k hk => farE_of_gt hk) (1 / 4) (by norm_num) (by norm_num)
      (fun j hj2 hjf hjne => far_factor_dispSite (hJ.trans hN) η (by omega) hsf hj2 hjf hjne.symm)
    rwa [farE_of_mem hs2 hsf] at this
  obtain ⟨J₂, hJ₂⟩ := eventually_atTop.mp hev
  refine ⟨max J₁ J₂, hJ₁.trans (le_max_left _ _), fun N hN η hη0 hη1 => ⟨?_, fun s hs2 hsf => ?_⟩⟩
  · exact h₁ N ((le_max_left _ _).trans hN) η (farE f) hη0 hη1 (fun k hk => farE_of_gt hk) (1 / 4)
      (by norm_num) (by norm_num)
      (fun j hj2 hjf => far_factor_dispSite (hJ₁.trans ((le_max_left _ _).trans hN)) η le_rfl
        (by omega) hj2 hjf (by omega))
  · exact hJ₂ N ((le_max_right _ _).trans hN) s (Finset.mem_Icc.mpr ⟨hs2, hsf⟩) η hη0 hη1

/-- The number of sites after which the lower bounds of `far_lowers` hold. -/
noncomputable def farJ (f : ℕ) : ℕ := (far_lowers f).choose

lemma farJ_ge (f : ℕ) : f ≤ farJ f := (far_lowers f).choose_spec.1

lemma farJ_R1 (f N : ℕ) (hN : farJ f ≤ N) (η : ℝ) (h0 : 0 < η) (h1 : η ≤ 1 / 4) :
    (1 / 4 : ℝ) ^ f / 2 ≤ profR1 (dispSite N (farE f)) (designWidthU N η) :=
  (((far_lowers f).choose_spec.2 N hN η h0 h1).1)

lemma farJ_Pi0 (f N : ℕ) (hN : farJ f ≤ N) (η : ℝ) (h0 : 0 < η) (h1 : η ≤ 1 / 4) {s : ℕ}
    (hs2 : 2 ≤ s) (hsf : s ≤ f) :
    farRho f ^ 2 * ((1 / 4 : ℝ) ^ f / 2) / |airyZero s - airyZero 1| ≤
      profPi0 (dispSite N (farE f)) (designWidthU N η) s :=
  (((far_lowers f).choose_spec.2 N hN η h0 h1).2 s hs2 hsf)

/-- The cut of the `k`-th design of the `f`-th far-first-site family. -/
noncomputable def farN (f k : ℕ) : ℕ := farJ f + k

lemma farN_ge (f k : ℕ) : farJ f ≤ farN f k := Nat.le_add_right _ _

lemma f_le_farN (f k : ℕ) : f ≤ farN f k := (farJ_ge f).trans (farN_ge f k)

lemma one_le_farN {f : ℕ} (hf : 1 ≤ f) (k : ℕ) : 1 ≤ farN f k := hf.trans (f_le_farN f k)

lemma farE_support (f N : ℕ) (hfN : f ≤ N) : ∀ k, (k < 2 ∨ N < k) → farE f k = 0 := by
  intro k hk
  rcases hk with hk | hk
  · exact farE_of_lt hk
  · exact farE_of_gt (by omega)

lemma farTail (f k : ℕ) :
    AiryProdTailHypothesis 1 (dispSite (farN f k) (farE f))
      (designWidthU (farN f k) (1 / ((k : ℝ) + 4))) :=
  dispTailHyp_D (Finset.range (f + 1)) (farE f)
    (fun j hj => farE_of_gt (by simp only [Finset.mem_range] at hj; omega)) _
    (eta_pos k).le (eta_le k)

/-- The `k`-th window of the `f`-th far-first-site family: first kept site `a_{f+1}`, sites `2, …, f`
displaced by `ρ_f`, cut `N_k = J_f + k`, detuning `η_* = 1/(k+4)`. -/
noncomputable def farWin (f k : ℕ) : Window :=
  profWin (dispSite (farN f k) (farE f)) (designWidthU (farN f k) (1 / ((k : ℝ) + 4))) (farTail f k)
    (fun _ hj => designWidthU_ne_zero _ (eta_pos k) hj) (farD f)

lemma farWin_mem {f : ℕ} (hf : 1 ≤ f) (k : ℕ) : farWin f k ∈ designClass ∪ displacedClassX :=
  Or.inr (profWin_mem_displacedClassX (eta_pos k) (farTail f k) (one_le_farN hf k) (eta_le k)
    (farE_support f _ (f_le_farN f k)))

/-! ### The sign law -/

lemma farWin_pi_neg (f k i : ℕ) (hi : i < f) : (farWin f k).pi i < 0 := by
  refine profWin_pi_neg _ _ _ _ _ ?_
  rw [airyZero_sub_farD]
  exact airyZero_lt_of_lt (by omega) (by omega)

lemma farWin_pi_first (f k : ℕ) : (farWin f k).pi f = 0 := by
  refine profWin_pi_eq_zero _ _ _ _ _ ?_
  rw [airyZero_sub_farD]; rfl

lemma farWin_pi_nonneg (f k i : ℕ) (hi : f < i) : 0 ≤ (farWin f k).pi i := by
  refine profWin_pi_nonneg_of_le _ _ _ _ _ ?_
  rw [airyZero_sub_farD]
  exact (airyZero_lt_of_lt (by omega) (by omega)).le

/-! ### `pi_lower` -/

lemma farWin_pi_lower {f : ℕ} (hf : 1 ≤ f) (i : ℕ) (hi : i < f) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ k, ω ≤ -(farWin f k).pi i := by
  have hd := farD_pos hf
  have hρ := farRho_pos f
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · refine ⟨farD f * ((1 / 4 : ℝ) ^ f / 2), by positivity, fun k => ?_⟩
    have h := farJ_R1 f (farN f k) (farN_ge f k) (1 / (↑k + 4)) (eta_pos k) (eta_le k)
    unfold farWin
    rw [profWin_pi_zero]
    nlinarith
  · obtain ⟨i₀, rfl⟩ : ∃ i₀, i = i₀ + 1 := ⟨i - 1, by omega⟩
    have hn2 : 2 ≤ i₀ + 2 := by omega
    have hnf : i₀ + 2 ≤ f := by omega
    have hpos : 0 < |airyZero (i₀ + 2) - airyZero 1| := abs_airyZero_sub_one_pos hn2
    have habs : |airyZero (i₀ + 2) - airyZero 1| = airyZero 1 - airyZero (i₀ + 2) := by
      rw [abs_sub_comm, abs_of_nonneg]
      linarith [airyZero_lt_of_lt (by omega : 1 ≤ 1) (by omega : 1 < i₀ + 2)]
    have hq : 1 < farD f / |airyZero (i₀ + 2) - airyZero 1| := by
      rw [one_lt_div hpos, habs]
      unfold farD
      linarith [airyZero_lt_of_lt (by omega : 1 ≤ i₀ + 2) (by omega : i₀ + 2 < f + 1)]
    have hq1 : 0 < farD f / |airyZero (i₀ + 2) - airyZero 1| - 1 := by linarith
    refine ⟨farRho f ^ 2 * ((1 / 4 : ℝ) ^ f / 2) / |airyZero (i₀ + 2) - airyZero 1| *
      (farD f / |airyZero (i₀ + 2) - airyZero 1| - 1), by positivity, fun k => ?_⟩
    have h := farJ_Pi0 f (farN f k) (farN_ge f k) (1 / (↑k + 4)) (eta_pos k) (eta_le k) hn2 hnf
    unfold farWin
    rw [profWin_pi_succ]
    unfold profPi
    have e : 1 - farD f / |airyZero (i₀ + 2) - airyZero 1| =
        -(farD f / |airyZero (i₀ + 2) - airyZero 1| - 1) := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right h hq1.le]

/-! ### `tail_small` -/

lemma farWin_pi_le {f : ℕ} (hf : 1 ≤ f) (k j : ℕ) :
    (if f < j + 1 then (farWin f k).pi (j + 1) else 0) ≤
      (if j + 2 ∈ Finset.Icc 2 (f + 1) then 0 else
        profPi (dispSite (farN f k) (farE f)) (designWidthU (farN f k) (1 / ((k : ℝ) + 4))) (-0) (j + 2)) := by
  by_cases h : f < j + 1
  · have hn : j + 2 ∉ Finset.Icc 2 (f + 1) := by
      simp only [Finset.mem_Icc]; omega
    simp only [h, hn, ↓reduceIte]
    unfold farWin
    rw [profWin_pi_succ]
    unfold profPi
    have h0 := profPi0_nonneg (dispSite (farN f k) (farE f))
      (designWidthU (farN f k) (1 / ((k : ℝ) + 4))) (farTail f k) (by omega : 2 ≤ j + 2)
    have hd := (farD_pos hf).le
    have hx : 0 ≤ farD f / |airyZero (j + 2) - airyZero 1| := div_nonneg hd (abs_nonneg _)
    rw [neg_zero, zero_div, sub_zero, mul_one]
    nlinarith
  · simp only [h, ↓reduceIte]
    split_ifs
    · exact le_rfl
    · have h0 := profPi0_nonneg (dispSite (farN f k) (farE f))
        (designWidthU (farN f k) (1 / ((k : ℝ) + 4))) (farTail f k) (by omega : 2 ≤ j + 2)
      unfold profPi
      rw [neg_zero, zero_div, sub_zero, mul_one]
      exact h0

lemma farWin_tail {f : ℕ} (hf : 1 ≤ f) :
    Tendsto (fun k => ∑' i, if f < i then (farWin f k).pi i else 0) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := exists_dispRest_le_D (Finset.Icc 2 (f + 1)) (farE f)
    (fun k hk => by
      rw [Finset.mem_Icc] at hk
      by_cases h : k < 2
      · exact farE_of_lt h
      · exact farE_of_gt (by omega)) 0 le_rfl
  have hη : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 4)) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => ((k : ℝ) + 4)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact this.inv_tendsto_atTop.congr (fun k => by simp [one_div])
  have hN : Tendsto (fun k : ℕ => ((farN f k : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun k : ℕ => farN f k) atTop atTop :=
      tendsto_atTop_mono (fun k => Nat.le_add_left k (farJ f)) tendsto_id
    have h1 : Tendsto (fun k : ℕ => ((farN f k : ℕ) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp h0
    exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp h1
  have hb : Tendsto (fun k : ℕ => B * ((1 / ((k : ℝ) + 4)) ^ 2 +
      ((farN f k : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)))) atTop (𝓝 0) := by
    have h4 := (((hη.pow 2).add hN).const_mul B)
    have h0 : B * ((0 : ℝ) ^ 2 + 0) = 0 := by ring
    rw [h0] at h4
    exact h4
  refine squeeze_zero (fun k => ?_) (fun k => ?_) hb
  · exact tsum_nonneg fun i => by
      split_ifs with h
      · exact farWin_pi_nonneg f k i h
      · exact le_rfl
  · obtain ⟨hHs, hHle⟩ := hbound (farN f k) (one_le_farN hf k) _ (eta_pos k).le (eta_le k)
    refine le_trans ?_ hHle
    set g : ℕ → ℝ := fun i => if f < i then (farWin f k).pi i else 0 with hg
    have hg0 : ∀ i, 0 ≤ g i := fun i => by
      simp only [hg]; split_ifs with h
      · exact farWin_pi_nonneg f k i h
      · exact le_rfl
    have hgs1 : Summable (fun j : ℕ => g (j + 1)) :=
      Summable.of_nonneg_of_le (fun j => hg0 _) (fun j => farWin_pi_le hf k j) hHs
    have hgs : Summable g := (summable_nat_add_iff 1).1 hgs1
    have hg00 : g 0 = 0 := by simp [hg]
    rw [hgs.tsum_eq_zero_add, hg00, zero_add]
    exact hgs1.tsum_le_tsum (fun j => farWin_pi_le hf k j) hHs

/-! ### The omitted family and `Σ` at Virasoro -/

/-- **The omitted family** (`sr:Sigma` Step 6, by far-first-site designs). -/
noncomputable def farFamily : OmittedFamily (designClass ∪ displacedClassX) where
  win := farWin
  mem := fun _ k hf => farWin_mem hf k
  pi_neg := fun f k i _ hi => farWin_pi_neg f k i hi
  pi_first := fun f k _ => farWin_pi_first f k
  pi_nonneg := fun f k i _ hi => farWin_pi_nonneg f k i hi
  pi_lower := fun f i hf hi => by
    obtain ⟨ω, hω, h⟩ := farWin_pi_lower hf i hi
    exact ⟨ω, hω, Filter.Eventually.of_forall h⟩
  tail_small := fun f hf => farWin_tail hf

/-- **Theorem `Σ` for a weight-one problem, no hypothesis beyond the threshold lower bound `hLo`**
(`sr:Sigma`): for every `c`-sequence tending to infinity (and above a threshold) there is an extremal
crossing sequence whose limit measure satisfies the conclusion of `Σ`. -/
theorem sigma_unconditional_prob (prob : FixedWeightProblem) (hw : prob.w = 1)
    (hLo : FormalResearch.ModularBootstrap.FixedWeight.FixedWeightLowerBoundInput prob) :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence prob, S.c = cSeq ∧
        (∀ j, S.τ j = prob.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        SigmaConclusion S.μS :=
  sigma_of_omitted_prob prob hw hLo displacedClass_subset (fun S => displacedPropertyP_prob prob hw S)
    farFamily

/-- **Theorem `Σ` at Virasoro, no hypothesis** (`sr:Sigma`): for every `c`-sequence tending to infinity (and
above a threshold) there is an extremal crossing sequence whose limit measure satisfies the conclusion of
`Σ`. -/
theorem virasoro_sigma_unconditional :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence virasoroProblem, S.c = cSeq ∧
        (∀ j, S.τ j = virasoroProblem.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        SigmaConclusion S.μS :=
  sigma_unconditional_prob virasoroProblem rfl FormalResearch.ModularBootstrap.FixedWeight.virasoro_lowerBoundInput

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.farFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms farFamily

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.virasoro_sigma_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_sigma_unconditional

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.sigma_unconditional_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sigma_unconditional_prob

end FormalResearch.ModularBootstrap.Upper.Assembly
