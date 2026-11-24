module

public import FormalResearch.ModularBootstrap.TwoLevel.IdealApproxTail

/-!
# `TwoZeroIdealApprox`: every admissible ideal datum is a limit of two-simple-zero designs (`virasoro_two_level.tex`,
`gt:2.6`, *Designs and their limits*)

For an admissible ideal datum `δ = (p, q, K, s)` (`IdealDatum.Adm`) the designs `𝔇_j = idealDesign δ (K + j) η_j`,
`η_j = 1/(j + 4)`, have zeros `p, q`, modified pairs at the sites `s_k` (`3 ≤ k ≤ K`) and at the Airy zeros `a_k`
(`K < k ≤ K + j + 2`), half-widths `η_j gap_k`, and reference pairs beyond.

* `ideal_tendsto_intWr`, `IdealApprox.ideal_tendsto_intWr_gen` (any `n_j → ∞`, `η_j → 0`, first zeros `p_j → p`):
  `∫ W_{𝔇_j} → ∫ Re F_δ`.  Proof: Airy quadrature `∫ W = Σ_ν Re nodeC ν`; the nodes `ν ≤ K`
  converge (Tannery for infinite products, `IdealApprox.tendsto_nodeC`) to those of the limit data, which sum to
  `∫ Re F_δ` (`IdealApprox.intWin_eq_sum`); the nodes `ν > K` are bounded multiples of the weights `Π_ν(0)` of the
  `f = 1` design of `ut:V` and sum to `O(η² + N^{-1/3})` by Lemma E (`IdealApprox.tail_sum_bound`);
* `nonempty_twoZeroApprox`: the designs satisfy every clause of `TwoZeroApprox δ` (admissible, `q_j = q`, windows bounded on
  compacta, `W_{𝔇_j} → Re F_δ` pointwise at every real `u`, vacuum integrals converge);
* `twoZeroIdealApprox`: **`TwoZeroIdealApprox`, unconditionally**;
* `not_adm_of_site_eq_airyZero`, `idealDesign_not_adm_of_site_eq_airyZero`: the admissibility clause that no site `s_k`
  (`k ≤ K`) is an Airy zero `a_j` with `j > K` is necessary for this construction: the design would repeat a site.

All results are proved unconditionally.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window
open FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum FormalResearch.ModularBootstrap.TwoLevel.IdealApprox

namespace IdealApprox

/-- The half-width parameters `η_j = 1/(j + 4)` of the approximating designs. -/
noncomputable def idealEta (j : ℕ) : ℝ := 1 / ((j : ℝ) + 4)

lemma idealEta_pos (j : ℕ) : 0 < idealEta j := by unfold idealEta; positivity

lemma idealEta_le (j : ℕ) : idealEta j ≤ 1 / 4 := by
  unfold idealEta
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

lemma tendsto_idealEta : Tendsto idealEta atTop (𝓝 0) := by
  unfold idealEta
  have h1 : Tendsto (fun j : ℕ => (j : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  simp only [one_div]
  exact h1.inv_tendsto_atTop

lemma tendsto_idealK (K : ℕ) : Tendsto (fun j : ℕ => K + j) atTop atTop :=
  tendsto_atTop_mono (fun j : ℕ => Nat.le_add_left j K) tendsto_id

/-- Node decomposition of `∫ W_𝔇` for an approximating design (first zero `p`). -/
lemma intWr_ideal_decomp (δ : IdealDatum) (p : ℝ) (n : ℕ) (η : ℝ) :
    ∫ u, (idealDesignP δ p n η).Wr u =
      ∑ m ∈ Finset.range δ.K, (nodeC p δ.q (idealSite δ.s δ.K n) (idealWidth n η) (m + 1)).re +
        ∑' m : ℕ, (nodeC p δ.q (idealSite δ.s δ.K n) (idealWidth n η) (δ.K + 1 + m)).re := by
  have h := intWr_decomp' (idealDesignP δ p n η) δ.K
  rw [idealDesignP_site, idealDesignP_width] at h
  exact h

/-- **The vacuum integrals of the approximating designs converge to `∫ Re F_δ`** (first zeros `p_j → p`,
half-width parameters `η_j ∈ (0, 1/4]`, `η_j → 0`, numbers of modified pairs `n_j ≥ K`, `n_j → ∞`). -/
theorem ideal_tendsto_intWr_gen (δ : IdealDatum) (hK : 2 ≤ δ.K) {n : ℕ → ℕ} {η p : ℕ → ℝ}
    (hn : Tendsto n atTop atTop) (hnK : ∀ j, δ.K ≤ n j) (hη0 : ∀ j, 0 < η j) (hη1 : ∀ j, η j ≤ 1 / 4)
    (hη : Tendsto η atTop (𝓝 0)) (hp : Tendsto p atTop (𝓝 δ.p)) :
    Tendsto (fun j : ℕ => ∫ u, (idealDesignP δ (p j) (n j) (η j)).Wr u) atTop (𝓝 (∫ u, δ.win u)) := by
  have hU := unifTail_ideal δ.s δ.K n η (fun j => (hη0 j).le) (fun j => (hη1 j).trans (by norm_num))
  have hfirst : Tendsto (fun j : ℕ => ∑ m ∈ Finset.range δ.K,
      (nodeC (p j) δ.q (idealSite δ.s δ.K (n j)) (idealWidth (n j) (η j)) (m + 1)).re) atTop
      (𝓝 (∫ u, δ.win u)) := by
    rw [intWin_eq_sum δ hK]
    refine tendsto_finsetSum _ fun m _ => ?_
    exact (Complex.continuous_re.tendsto _).comp
      (tendsto_nodeC hU hp (idealLim δ.s δ.K) (fun _ => 0)
        (fun k hk => tendsto_idealSite δ.s δ.K hn hk) (fun k hk => tendsto_idealWidth hn hη hk) (by omega))
  obtain ⟨M, hM0, N₀, hM⟩ := tail_sum_bound δ.s hK δ.q (|airyZero 1 - δ.p| + 1)
  have hrate : Tendsto (fun j : ℕ => M * (η j ^ 2 + (((n j) + 2 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => (((n j) + 2 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun j : ℕ => Nat.le_add_right (n j) 2) hn)
    have h2 : Tendsto (fun j : ℕ => (((n j) + 2 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp h1
    have h3 := ((hη.pow 2).add h2).const_mul M
    simpa using h3
  have hpb : ∀ᶠ j in atTop, |airyZero 1 - p j| ≤ |airyZero 1 - δ.p| + 1 := by
    filter_upwards [hp.eventually (Metric.ball_mem_nhds δ.p one_pos)] with j hj
    rw [Real.dist_eq] at hj
    calc |airyZero 1 - p j| = |(airyZero 1 - δ.p) + (δ.p - p j)| := by ring_nf
      _ ≤ |airyZero 1 - δ.p| + |δ.p - p j| := abs_add_le _ _
      _ ≤ |airyZero 1 - δ.p| + 1 := by rw [abs_sub_comm δ.p (p j)]; linarith
  have htail : Tendsto (fun j : ℕ => ∑' m : ℕ,
      (nodeC (p j) δ.q (idealSite δ.s δ.K (n j)) (idealWidth (n j) (η j)) (δ.K + 1 + m)).re)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hrate
    filter_upwards [hn.eventually_ge_atTop N₀, hpb] with j hj hjp
    rw [Real.norm_eq_abs]
    exact hM (n j) (hnK j) (by omega) _ (p j) (hη0 j) (hη1 j) hjp
  have := hfirst.add htail
  rw [add_zero] at this
  refine this.congr fun j => ?_
  exact (intWr_ideal_decomp δ (p j) (n j) (η j)).symm

/-- **The vacuum integrals of the approximating designs converge to `∫ Re F_δ`.** -/
theorem ideal_tendsto_intWr (δ : IdealDatum) (hK : 2 ≤ δ.K) :
    Tendsto (fun j : ℕ => ∫ u, (idealDesign δ (δ.K + j) (idealEta j)).Wr u) atTop (𝓝 (∫ u, δ.win u)) :=
  ideal_tendsto_intWr_gen δ hK (p := fun _ => δ.p) (tendsto_idealK δ.K) (fun _ => Nat.le_add_right _ _)
    idealEta_pos idealEta_le tendsto_idealEta tendsto_const_nhds

end IdealApprox

/-- **Every admissible ideal datum has a two-simple-zero approximation** (`ε_k → 0`, `N → ∞`, `η_* → 0` of the TeX):
the designs `idealDesign δ (K + j) η_j` are admissible, have `q_j = q`, windows bounded on compacta, windows converging
pointwise to `Re F_δ` and vacuum integrals converging to `∫ Re F_δ`. -/
theorem nonempty_twoZeroApprox (δ : IdealDatum) (hδ : δ.Adm) : Nonempty (TwoZeroApprox δ) := by
  have hK : 2 ≤ δ.K := hδ.2.2.1
  have hη0 : ∀ j, 0 ≤ idealEta j := fun j => (idealEta_pos j).le
  have hη1 : ∀ j, idealEta j ≤ 1 := fun j => (idealEta_le j).trans (by norm_num)
  have hn := tendsto_idealK δ.K
  have hint := ideal_tendsto_intWr δ hK
  refine ⟨{
    n := fun j => δ.K + j
    d := fun j => idealDesign δ (δ.K + j) (idealEta j)
    n_pos := fun j => by omega
    adm := fun j => idealDesign_adm hδ _ (idealEta_pos j)
    q_eq := fun j => rfl
    bdd := fun R => by
      obtain ⟨M, hM⟩ := ideal_Wr_bound δ (fun j => δ.K + j) idealEta hη0 hη1 R
      exact ⟨M, fun j u hu => hM j u (abs_le.2 ⟨hu.1, hu.2⟩)⟩
    tendsto_pt := fun u => ideal_tendsto_Wr δ hK hn hη0 hη1 tendsto_idealEta u
    limsup_le := fun ε hε => by
      filter_upwards [hint.eventually (Iio_mem_nhds (by linarith : ∫ u, δ.win u < (∫ u, δ.win u) + ε))]
        with j hj
      exact le_of_lt hj }⟩

/-- **`TwoZeroIdealApprox`** (window analysis, no comb): every admissible ideal datum is a limit of two-simple-zero
designs, proved. -/
theorem twoZeroIdealApprox : TwoZeroIdealApprox := nonempty_twoZeroApprox

/-- **Negative regression**: a datum with a site `s_k = a_j`, `k ≤ K < j`, is not admissible. -/
theorem not_adm_of_site_eq_airyZero (δ : IdealDatum) {k j : ℕ} (hk3 : 3 ≤ k) (hkK : k ≤ δ.K) (hj : δ.K < j)
    (h : δ.s k = airyZero j) : ¬ δ.Adm :=
  fun hδ => hδ.2.2.2.2.2 k hk3 hkK j hj h

/-- **Negative regression, design level**: for such a datum the approximating design, which puts the ideal pair
`a_j` at the site `a_j = s_k`, repeats a site and so is not admissible. -/
theorem idealDesign_not_adm_of_site_eq_airyZero (δ : IdealDatum) {k j n : ℕ} (hk3 : 3 ≤ k) (hkK : k ≤ δ.K)
    (hj : δ.K < j) (hjn : j ≤ n + 2) (h : δ.s k = airyZero j) (η : ℝ) : ¬ (idealDesign δ n η).Adm := by
  intro hA
  have hi : k - 3 < n := by omega
  have hi' : j - 3 < n := by omega
  have := hA.2.2.2.1 (a₁ := (⟨k - 3, hi⟩ : Fin n)) (a₂ := ⟨j - 3, hi'⟩) (by
    show (if k - 3 + 3 ≤ δ.K then δ.s (k - 3 + 3) else airyZero (k - 3 + 3)) =
      (if j - 3 + 3 ≤ δ.K then δ.s (j - 3 + 3) else airyZero (j - 3 + 3))
    rw [show k - 3 + 3 = k by omega, show j - 3 + 3 = j by omega]
    simp only [hkK, show ¬ (j ≤ δ.K) from by omega, ↓reduceIte]
    exact h)
  have := congrArg Fin.val this
  simp only at this
  omega

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealApprox.ideal_tendsto_intWr_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IdealApprox.ideal_tendsto_intWr_gen

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealApprox.ideal_tendsto_intWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IdealApprox.ideal_tendsto_intWr

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.nonempty_twoZeroApprox' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonempty_twoZeroApprox

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroIdealApprox' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroIdealApprox

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.not_adm_of_site_eq_airyZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_adm_of_site_eq_airyZero

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.idealDesign_not_adm_of_site_eq_airyZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealDesign_not_adm_of_site_eq_airyZero

end FormalResearch.ModularBootstrap.TwoLevel
