module

public import FormalResearch.ModularBootstrap.TwoLevel.IdealApproxWindow

/-!
# The approximating designs of an ideal datum (`virasoro_two_level.tex`, `gt:2.6`, *Designs and their limits*)

For an ideal datum `δ = (p, q, K, s)`, `n ≥ 1` modified pairs and `η > 0` the design `idealDesign δ n η` has zeros
`p, q`, modified pairs `k = 3, …, n + 2` at the sites `s_k` (`k ≤ K`) and the Airy zeros `a_k` (`K < k ≤ n + 2`) with
half-widths `η gap_k`, and the reference pairs beyond.  As `η → 0`, `n → ∞` its window tends to `Re F_δ`:

* `idealDesign_adm`: admissibility, from `IdealDatum.Adm` (the sites `s_k` are pairwise distinct and differ from the
  Airy zeros `a_j`, `j > K`);
* `unifTail_ideal`: the family of designs satisfies the uniform tail bound `UnifTail`;
* `F_eq_winC`: `F_δ = winC p q (idealLim s K) 0`, the Airy product with zero widths;
* `ideal_Wr_bound`, `ideal_tendsto_Wr`: local uniform bound of `W_{𝔇}` and pointwise convergence
  `W_{idealDesign δ (K + j) η_j}(x) → Re F_δ(x)` at every real `x`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel.IdealApprox

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window
open FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum

/-- Sites of the approximating designs: `k ∈ [3, n + 2]` at `s k` (`k ≤ K`) or `a_k`, reference beyond. -/
noncomputable def idealSite (s : ℕ → ℝ) (K n : ℕ) (k : ℕ) : ℝ :=
  if 3 ≤ k ∧ k ≤ n + 2 then (if k ≤ K then s k else airyZero k) else uWKB k

/-- Half-widths of the approximating designs. -/
noncomputable def idealWidth (n : ℕ) (η : ℝ) (k : ℕ) : ℝ :=
  (if 3 ≤ k ∧ k ≤ n + 2 then η else 1 / 4) * gapWKB k

/-- The limit sites (`n = ∞`); the limit widths are `0`. -/
noncomputable def idealLim (s : ℕ → ℝ) (K : ℕ) (k : ℕ) : ℝ :=
  if 3 ≤ k then (if k ≤ K then s k else airyZero k) else uWKB k

/-- The approximating design of an ideal datum. -/
noncomputable def idealDesign (δ : IdealDatum) (n : ℕ) (η : ℝ) : TwoZeroDesign n where
  p := δ.p
  q := δ.q
  s := fun i => if (i : ℕ) + 3 ≤ δ.K then δ.s ((i : ℕ) + 3) else airyZero ((i : ℕ) + 3)
  e := fun i => η * gapWKB ((i : ℕ) + 3)

lemma idealDesign_site (δ : IdealDatum) (n : ℕ) (η : ℝ) :
    (idealDesign δ n η).site = idealSite δ.s δ.K n := by
  funext k
  unfold TwoZeroDesign.site idealSite
  by_cases h : 3 ≤ k ∧ k ≤ n + 2
  · simp only [h, and_self, dite_true, ↓reduceIte, idealDesign]
    rw [Nat.sub_add_cancel h.1]
  · simp only [h, dite_false, ↓reduceIte]

lemma idealDesign_width (δ : IdealDatum) (n : ℕ) (η : ℝ) :
    (idealDesign δ n η).width = idealWidth n η := by
  funext k
  unfold TwoZeroDesign.width idealWidth
  by_cases h : 3 ≤ k ∧ k ≤ n + 2
  · simp only [h, and_self, dite_true, ↓reduceIte, idealDesign]
    rw [Nat.sub_add_cancel h.1]
  · simp only [h, dite_false, ↓reduceIte]

/-- The approximating design with the first zero `p` replaced (for `p → δ.p`). -/
noncomputable def idealDesignP (δ : IdealDatum) (p : ℝ) (n : ℕ) (η : ℝ) : TwoZeroDesign n :=
  { idealDesign δ n η with p := p }

lemma idealDesignP_site (δ : IdealDatum) (p : ℝ) (n : ℕ) (η : ℝ) :
    (idealDesignP δ p n η).site = idealSite δ.s δ.K n := idealDesign_site δ n η

lemma idealDesignP_width (δ : IdealDatum) (p : ℝ) (n : ℕ) (η : ℝ) :
    (idealDesignP δ p n η).width = idealWidth n η := idealDesign_width δ n η

lemma idealDesign_W (δ : IdealDatum) (n : ℕ) (η : ℝ) :
    (idealDesign δ n η).W = winC δ.p δ.q (idealSite δ.s δ.K n) (idealWidth n η) := by
  funext u
  unfold TwoZeroDesign.W winC
  rw [idealDesign_site, idealDesign_width]
  rfl

/-- Admissibility of the approximating designs. -/
lemma idealDesign_adm {δ : IdealDatum} (hδ : δ.Adm) (n : ℕ) {η : ℝ} (hη : 0 < η) :
    (idealDesign δ n η).Adm := by
  obtain ⟨hqp, hq0, hK2, hneg, hinj, hair⟩ := hδ
  refine ⟨hqp, hq0, fun i => ?_, ?_, fun i => ?_⟩
  · show (if (i : ℕ) + 3 ≤ δ.K then δ.s ((i : ℕ) + 3) else airyZero ((i : ℕ) + 3)) < 0
    split_ifs with h
    · exact hneg _ (by omega) h
    · exact airyZero_neg _
  · intro i j hij
    have hij' : (if (i : ℕ) + 3 ≤ δ.K then δ.s ((i : ℕ) + 3) else airyZero ((i : ℕ) + 3)) =
        (if (j : ℕ) + 3 ≤ δ.K then δ.s ((j : ℕ) + 3) else airyZero ((j : ℕ) + 3)) := hij
    apply Fin.ext
    by_cases hi : (i : ℕ) + 3 ≤ δ.K <;> by_cases hj : (j : ℕ) + 3 ≤ δ.K <;> simp only [hi, hj, ↓reduceIte] at hij'
    · have := hinj _ _ (by omega) hi (by omega) hj hij'
      omega
    · exact absurd hij' (hair _ (by omega) hi _ (by omega))
    · exact absurd hij'.symm (hair _ (by omega) hj _ (by omega))
    · have := airyZero_injective_on (by omega) (by omega) hij'
      omega
  · show 0 < η * gapWKB ((i : ℕ) + 3)
    exact mul_pos hη (gapWKB_pos (by omega))

/-- **The approximating designs satisfy one uniform tail bound.** -/
lemma unifTail_ideal (s : ℕ → ℝ) (K : ℕ) (n : ℕ → ℕ) (η : ℕ → ℝ) (hη0 : ∀ j, 0 ≤ η j) (hη1 : ∀ j, η j ≤ 1) :
    UnifTail (fun j => idealSite s K (n j)) (fun j => idealWidth (n j) (η j)) := by
  obtain ⟨A₀, hA₀, hb⟩ := uniform_wkb_bound
  set SB : ℝ := ∑ k ∈ Finset.Icc 3 K, |s k - airyZero k| * (k : ℝ) ^ (4 / 3 : ℝ) with hSBdef
  have hSB0 : 0 ≤ SB := Finset.sum_nonneg fun k _ => by positivity
  refine ⟨A₀ + SB, by positivity, fun j k hk1 => ⟨?_, ?_⟩⟩
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hp : 0 ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
    show |idealSite s K (n j) k - airyZero k| ≤ _
    unfold idealSite
    by_cases h : 3 ≤ k ∧ k ≤ n j + 2
    · by_cases hkK : k ≤ K
      · simp only [h, and_self, ↓reduceIte, hkK]
        have hle : |s k - airyZero k| * (k : ℝ) ^ (4 / 3 : ℝ) ≤ SB :=
          Finset.single_le_sum (f := fun k : ℕ => |s k - airyZero k| * (k : ℝ) ^ (4 / 3 : ℝ))
            (fun k _ => by positivity) (Finset.mem_Icc.mpr ⟨h.1, hkK⟩)
        have e : (k : ℝ) ^ (4 / 3 : ℝ) * (k : ℝ) ^ (-(4 / 3 : ℝ)) = 1 := by
          rw [← Real.rpow_add hk0]; simp
        calc |s k - airyZero k| = (|s k - airyZero k| * (k : ℝ) ^ (4 / 3 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
              rw [mul_assoc, e, mul_one]
          _ ≤ SB * (k : ℝ) ^ (-(4 / 3 : ℝ)) := mul_le_mul_of_nonneg_right hle hp
          _ ≤ (A₀ + SB) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by gcongr; linarith
      · simp only [h, and_self, ↓reduceIte, hkK, sub_self, abs_zero]
        positivity
    · simp only [h, ↓reduceIte]
      rw [abs_sub_comm]
      exact (hb k hk1).1.trans (by gcongr; linarith)
  · show |idealWidth (n j) (η j) k| ≤ _
    unfold idealWidth
    have hg := (gapWKB_pos hk1).le
    rw [abs_mul, abs_of_nonneg hg]
    have hη : |(if 3 ≤ k ∧ k ≤ n j + 2 then η j else (1 / 4 : ℝ))| ≤ 1 := by
      split_ifs
      · rw [abs_of_nonneg (hη0 j)]; exact hη1 j
      · rw [abs_of_nonneg (by norm_num)]; norm_num
    calc |(if 3 ≤ k ∧ k ≤ n j + 2 then η j else (1 / 4 : ℝ))| * gapWKB k ≤ 1 * gapWKB k :=
        mul_le_mul_of_nonneg_right hη hg
      _ ≤ A₀ * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by linarith [(hb k hk1).2]
      _ ≤ (A₀ + SB) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by gcongr; linarith

lemma tendsto_idealSite (s : ℕ → ℝ) (K : ℕ) {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (fun j => idealSite s K (n j) k) atTop (𝓝 (idealLim s K k)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hn.eventually_ge_atTop k] with j hj
  unfold idealSite idealLim
  simp only [show 3 ≤ k ∧ k ≤ n j + 2 from ⟨hk, by omega⟩, and_self, ↓reduceIte]

lemma tendsto_idealWidth {n : ℕ → ℕ} {η : ℕ → ℝ} (hn : Tendsto n atTop atTop) (hη : Tendsto η atTop (𝓝 0))
    {k : ℕ} (hk : 3 ≤ k) : Tendsto (fun j => idealWidth (n j) (η j) k) atTop (𝓝 ((fun _ => (0 : ℝ)) k)) := by
  have hlim : Tendsto (fun j => η j * gapWKB k) atTop (𝓝 0) := by
    simpa using hη.mul_const (gapWKB k)
  refine hlim.congr' ?_
  filter_upwards [hn.eventually_ge_atTop k] with j hj
  unfold idealWidth
  simp only [show 3 ≤ k ∧ k ≤ n j + 2 from ⟨hk, by omega⟩, and_self, ↓reduceIte]

lemma idealLim_eq_airy (s : ℕ → ℝ) {K k : ℕ} (hK : 2 ≤ K) (hk : K < k) : idealLim s K k = airyZero k := by
  unfold idealLim
  simp only [show 3 ≤ k by omega, ↓reduceIte, show ¬(k ≤ K) by omega]

/-- The tail of the limit data is `1`. -/
lemma airyProdTail_idealLim (s : ℕ → ℝ) {K : ℕ} (hK : 2 ≤ K) {u : ℂ}
    (hu : ∀ k : ℕ, K < k → u ≠ (airyZero k : ℂ)) :
    airyProdTail K (idealLim s K) (fun _ => 0) u = 1 := by
  unfold airyProdTail
  have : ∀ m : ℕ, airyProdFactor (idealLim s K) (fun _ => 0) (K + 1 + m) u = 1 := fun m => by
    have hk : K < K + 1 + m := by omega
    have hden : (u - (airyZero (K + 1 + m) : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (hu _ hk))
    unfold airyProdFactor
    rw [idealLim_eq_airy s hK hk]
    simp only [Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    exact div_self hden
  simp only [this, tprod_one]

/-- **`F_δ` is the Airy product with zero widths**: `F_δ = winC p q (idealLim s K) 0`. -/
theorem F_eq_winC (δ : IdealDatum) (hK : 2 ≤ δ.K) :
    δ.F = winC δ.p δ.q (idealLim δ.s δ.K) (fun _ => 0) := by
  have hH := tailHyp_of_eventually_airy (S' := idealLim δ.s δ.K) (W' := fun _ => 0) (M₀ := δ.K)
    (fun k hk => idealLim_eq_airy δ.s hK hk) (fun k _ => rfl) δ.K
  have hH2 := tailHyp_of_eventually_airy (S' := idealLim δ.s δ.K) (W' := fun _ => 0) (M₀ := δ.K)
    (fun k hk => idealLim_eq_airy δ.s hK hk) (fun k _ => rfl) 2
  have hne : ∀ u : ℂ, u.im ≠ 0 → δ.F u = winC δ.p δ.q (idealLim δ.s δ.K) (fun _ => 0) u := by
    intro u hu
    have hu' : ∀ k : ℕ, 1 ≤ k → u ≠ (airyZero k : ℂ) := fun k _ => airyZero_ne_of_im_ne_zero hu k
    have hD : windowD δ.K u ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (hu' k (Finset.mem_Icc.mp hk).1)
    have h1 := δ.F_spec u
    have h2 := airyH_spec δ.K u
    have h3 : δ.F u * windowD δ.K u ^ 2 = airyH δ.K u * δ.N u * windowD δ.K u ^ 2 := by
      rw [← h1]; rw [h2]; ring
    have h4 := mul_right_cancel₀ (pow_ne_zero 2 hD) h3
    rw [winC_eq_of_ne δ.p δ.q hK hH hu', airyProdTail_idealLim δ.s hK (fun k _ => hu' k (by omega)), h4]
    unfold finQ IdealDatum.N
    have : ∏ k ∈ Finset.Icc 3 δ.K, ((u - ((idealLim δ.s δ.K k : ℝ) : ℂ)) ^ 2 + (((fun _ => (0 : ℝ)) k : ℝ) : ℂ) ^ 2) =
        ∏ k ∈ Finset.Icc 3 δ.K, (u - (δ.s k : ℂ)) ^ 2 := by
      refine Finset.prod_congr rfl fun k hk => ?_
      obtain ⟨hk3, hkK⟩ := Finset.mem_Icc.mp hk
      have : idealLim δ.s δ.K k = δ.s k := by
        unfold idealLim; simp only [hk3, hkK, ↓reduceIte]
      rw [this]; simp
    rw [this]; ring
  funext u₀
  by_cases hu₀ : u₀.im = 0
  · exact eq_of_continuousAt_of_im_ne_zero hu₀ δ.differentiable_F.continuous.continuousAt
      (differentiable_winC δ.p δ.q hH2).continuous.continuousAt hne
  · exact hne u₀ hu₀


lemma idealDesign_Wr (δ : IdealDatum) (n : ℕ) (η : ℝ) (u : ℝ) :
    (idealDesign δ n η).Wr u = (winC δ.p δ.q (idealSite δ.s δ.K n) (idealWidth n η) (u : ℂ)).re := by
  unfold TwoZeroDesign.Wr
  rw [idealDesign_W]

/-- **Local uniform bound** of the windows of the approximating designs. -/
theorem ideal_Wr_bound (δ : IdealDatum) (n : ℕ → ℕ) (η : ℕ → ℝ) (hη0 : ∀ j, 0 ≤ η j) (hη1 : ∀ j, η j ≤ 1)
    (R : ℝ) : ∃ M : ℝ, ∀ (j : ℕ) (u : ℝ), |u| ≤ R → |(idealDesign δ (n j) (η j)).Wr u| ≤ M := by
  obtain ⟨M, hM⟩ := exists_winC_bound (unifTail_ideal δ.s δ.K n η hη0 hη1) δ.p δ.q R
  refine ⟨M, fun j u hu => ?_⟩
  rw [idealDesign_Wr]
  exact (Complex.abs_re_le_norm _).trans (hM j u hu)

/-- **Pointwise limit**: `W_{idealDesign δ (n_j) η_j}(x) → Re F_δ(x)` at every real `x`. -/
theorem ideal_tendsto_Wr (δ : IdealDatum) (hK : 2 ≤ δ.K) {n : ℕ → ℕ} {η : ℕ → ℝ} (hn : Tendsto n atTop atTop)
    (hη0 : ∀ j, 0 ≤ η j) (hη1 : ∀ j, η j ≤ 1) (hη : Tendsto η atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun j => (idealDesign δ (n j) (η j)).Wr x) atTop (𝓝 (δ.win x)) := by
  have h := tendsto_winC (unifTail_ideal δ.s δ.K n η hη0 hη1) δ.p δ.q (idealLim δ.s δ.K) (fun _ => 0)
    (M₀ := δ.K) (fun k hk => idealLim_eq_airy δ.s hK hk) (fun k _ => rfl)
    (fun k hk => tendsto_idealSite δ.s δ.K hn hk) (fun k hk => tendsto_idealWidth hn hη hk) x
  have h' := (Complex.continuous_re.tendsto _).comp h
  have e : δ.win x = (winC δ.p δ.q (idealLim δ.s δ.K) (fun _ => 0) (x : ℂ)).re := by
    unfold IdealDatum.win
    rw [F_eq_winC δ hK]
  rw [e]
  refine h'.congr fun j => ?_
  exact (idealDesign_Wr δ (n j) (η j) x).symm

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealApprox.F_eq_winC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms F_eq_winC

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealApprox.ideal_Wr_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ideal_Wr_bound

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealApprox.ideal_tendsto_Wr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ideal_tendsto_Wr

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealApprox.idealDesign_adm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealDesign_adm

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealApprox.unifTail_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unifTail_ideal

end FormalResearch.ModularBootstrap.TwoLevel.IdealApprox
