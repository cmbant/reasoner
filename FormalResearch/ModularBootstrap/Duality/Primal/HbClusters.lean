module

public import FormalResearch.ModularBootstrap.Duality.Primal.ClusterZerosAndBounds

/-!
# Common exact clusters at prescribed Hermite–Biehler levels (`dsl:hb-clusters`)

Formalizes `Theorem E'-HB` (`dsl:hb-clusters`, parts (a) and (b)) in `dual_spectrum_limit.tex` for
any `FixedWeightProblem`, arbitrary Hermite–Biehler limit datum `H : HermiteBiehlerData` (including
both `HermiteBiehlerData.airy` and general `(P, Q)` via `HermiteBiehlerData.ofQNeZero`), and any
compact window `[a, b]` isolating the first `K` nodes `z_0 > z_1 > … > z_{K-1}`.

Main results:
* `hb_clusters`: existence of measure-independent support points `tStar k n`, simple/double
  multiplicity at every weak extremal, convergence `uAiry (c n) (tStar k n) → z k`, uniform
  normalised weight convergence to `ω k`, uniform `dsl:hb-raw` asymptotic for attaining measures,
  and `dsl:hb-raw` at prescribed sites for near-optimal measures;
* `hb_clusters_inactive`: part (b) inactivity of additional compact sets `E_n` whose Airy images lie
  in a fixed compact subset of `{u > H.tm : (normProfile H.G u).re > 0}`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.WeightAxioms FormalResearch.ModularBootstrap.ConcreteBootstrap
  FormalResearch.ModularBootstrap.FixedWeightTip FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Bessel
  FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ArgPrinciple

/-! ### 1. Setup data, cluster measure, and continuous bump helpers -/

/-- Window data for `dsl:hb-clusters` around a fixed `HermiteBiehlerData` datum `H`:
ordered real nodes `z 0 > z 1 > … > z (K-1)` inside `(a, b)`, exhausting all zeros of
`normProfile H.G` in `{w : ℂ | w.re ∈ [a, b]}` with analytic orders `1` on `H.S` and `2`
elsewhere, and positive limiting weights `ω k`. -/
structure HbClusterData (H : HermiteBiehlerData) where
  K : ℕ
  hK : 1 ≤ K
  z : Fin K → ℝ
  hz_anti : StrictAnti z
  hz_zero : ∀ k : Fin K, H.G (z k : ℂ) = 0
  a : ℝ
  b : ℝ
  ha : a < z ⟨K - 1, by omega⟩
  hb : z ⟨0, by omega⟩ < b
  hzero_win : ∀ w : ℂ, w.re ∈ Icc a b →
    (normProfile H.G w = 0 ↔ ∃ k : Fin K, w = (z k : ℂ))
  hord : ∀ k : Fin K,
    analyticOrderNatAt (normProfile H.G) (z k : ℂ) = if z k ∈ H.S then 1 else 2
  hS_sub : ∀ i ∈ H.S, ∃ k : Fin K, i = z k
  hS_top : ∀ k : Fin K, z k ∈ H.S ↔ H.tm ≤ z k
  ω : Fin K → ℝ
  hω_pos : ∀ k : Fin K, 0 < ω k

/-- The prescribed discrete support set `F_n = {s_{i,n} : i ∈ H.S \ {H.tm}}`. -/
def hbPrescribedSet {H : HermiteBiehlerData} (s : HbNodes H → ℕ → ℝ) (n : ℕ) : Set ℝ :=
  Set.range fun i : HbNodes H => s i n

private instance (H : HermiteBiehlerData) : Finite (HbNodes H) :=
  Finite.of_injective (fun i : HbNodes H => (⟨i.1, i.2.1⟩ : H.S))
    (fun _ _ h => Subtype.ext (Subtype.mk.inj h))

lemma isCompact_hbPrescribedSet {H : HermiteBiehlerData} (s : HbNodes H → ℕ → ℝ) (n : ℕ) :
    IsCompact (hbPrescribedSet s n) :=
  Set.Finite.isCompact (Set.finite_range _)

lemma hbPrescribedSet_subset_Ioi {H : HermiteBiehlerData} {s : HbNodes H → ℕ → ℝ}
    (hs_pos : ∀ i : HbNodes H, ∀ᶠ n in atTop, 0 < s i n) :
    ∀ᶠ n in atTop, hbPrescribedSet s n ⊆ Ioi 0 := by
  have hall : ∀ᶠ n in atTop, ∀ i : HbNodes H, 0 < s i n :=
    eventually_all.2 hs_pos
  filter_upwards [hall] with n hn t ⟨i, hi⟩
  exact hi ▸ hn i

/-- Limiting atomic measure on the cluster window `[a, b]`. -/
noncomputable def hbClusterMeasure {H : HermiteBiehlerData} (CD : HbClusterData H) :
    Measure ℝ :=
  ∑ k : Fin CD.K, ENNReal.ofReal (CD.ω k) • Measure.dirac (CD.z k)

lemma exists_bump_near {x₀ r : ℝ} (hr : 0 < r) :
    ∃ f : ℝ → ℝ, Continuous f ∧ HasCompactSupport f ∧
      (∀ u, 0 ≤ f u ∧ f u ≤ 1) ∧
      (∀ u ∈ Icc (x₀ - r / 2) (x₀ + r / 2), f u = 1) ∧
      (∀ u ∉ Ioo (x₀ - r) (x₀ + r), f u = 0) ∧
      tsupport f ⊆ Icc (x₀ - r) (x₀ + r) := by
  have hK : IsCompact (Icc (x₀ - r / 2) (x₀ + r / 2)) := isCompact_Icc
  have hU : IsOpen (Ioo (x₀ - r) (x₀ + r)) := isOpen_Ioo
  have hKU : Icc (x₀ - r / 2) (x₀ + r / 2) ⊆ Ioo (x₀ - r) (x₀ + r) := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  obtain ⟨f, hfK, hfU, -, hf01⟩ := exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr hKU)
  have hsupp : Function.support f ⊆ Icc (x₀ - r) (x₀ + r) := fun u hu => by
    by_contra hn
    have hnot : u ∉ Ioo (x₀ - r) (x₀ + r) := fun h => hn (Ioo_subset_Icc_self h)
    exact hu (hfU hnot)
  have htsupp : tsupport f ⊆ Icc (x₀ - r) (x₀ + r) :=
    closure_minimal hsupp isClosed_Icc
  exact ⟨f, f.continuous, isCompact_Icc.of_isClosed_subset isClosed_closure htsupp,
    hf01, hfK, hfU, htsupp⟩

/-! ### 2. Weak-extremal definition, `psiTilde` sign dictionary, and `bl:norm` -/

/-- A normalised weak extremal of `theorem_primal` at charge `c` on `F ∪ [B, ∞)`. -/
def IsWeakExtremal (prob : FixedWeightProblem) (c : ℝ) (F : Set ℝ) (B : ℝ) (gs : ℝ → ℝ) : Prop :=
  TestClass prob (c / 12) gs ∧ prob.cardyNorm (c / 12) gs = 1 ∧
    prob.gVac (c / 12) gs = 0 ∧ ∀ t ∈ F ∪ Ici B, 0 ≤ gs t

lemma isWeakExtremal_slackFeasible {prob : FixedWeightProblem} {c : ℝ} {F : Set ℝ} {B : ℝ}
    {gs : ℝ → ℝ} (h : IsWeakExtremal prob c F B gs) :
    IsSlackFeasible prob (c / 12) B 0 gs := by
  have hgV0 : ∫ t in Ioi (0 : ℝ), gs t * prob.cardyV (c / 12) t = 0 := by
    have hvac : prob.gVac (c / 12) gs = -2 * Real.pi * ∫ t in Ioi (0 : ℝ), gs t * prob.cardyV (c / 12) t := rfl
    rw [h.2.2.1] at hvac
    nlinarith [Real.pi_pos]
  exact ⟨h.1, by rw [h.2.1]; exact zero_lt_one, by simp [hgV0], fun t ht => h.2.2.2 t (Or.inr ht)⟩

lemma virasoroAC_sq_eventually_ge {c : ℕ → ℝ} (hc : Tendsto c atTop atTop) (R : ℝ) :
    ∀ᶠ n in atTop, R ≤ virasoroAC (c n) ^ 2 := by
  have h1 : Tendsto (fun n => virasoroAC (c n) ^ 2) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
      (mul_pos two_pos (pow_pos virasoroBV_pos 2))).comp hc |>.congr'
      (by filter_upwards [hc.eventually_ge_atTop 0] with n hn
          dsimp only [Function.comp_apply]; rw [virasoroAC_sq (c n) hn])
  exact h1.eventually_ge_atTop R

lemma chartAC_sq_eventually_ge {r1 : ℝ} (hr1 : 0 < r1) {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) (R : ℝ) :
    ∀ᶠ n in atTop, R ≤ chartAC r1 (c n) ^ 2 := by
  have h1 : Tendsto (fun n => chartAC r1 (c n) ^ 2) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
      (mul_pos two_pos (pow_pos (chartBV_pos hr1) 2))).comp hc |>.congr'
      (by filter_upwards [hc.eventually_ge_atTop 0] with n hn
          dsimp only [Function.comp_apply]; rw [chartAC_sq r1 (c n) hn])
  exact h1.eventually_ge_atTop R

lemma psiTilde_pref_pos (prob : FixedWeightProblem) {c' : ℝ} (hc' : 0 < c')
    (hsh : prob.totalShift ≤ c' / 12) {g : ℝ → ℝ} (hM : 0 < prob.cardyNorm (c' / 12) g)
    {u : ℝ} (hu : |u| ≤ virasoroAC c' ^ 2) :
    0 < (prob.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
      prob.cardyV (c' / 12) (virasoroDeltaChart c' u) := by
  obtain ⟨_, _, hderiv⟩ := virasoroDeltaChart_deriv_abs_bounds
  have hd_pos : 0 < -deriv (virasoroDeltaChart c') u :=
    lt_of_lt_of_le (mul_pos (half_pos cStar_pos) (Real.rpow_pos_of_pos hc' _)) (hderiv hc' hu).1
  have ht_pos : 0 < virasoroDeltaChart c' u := virasoroDeltaChart_pos hc' hu
  have hV_pos : 0 < prob.cardyV (c' / 12) (virasoroDeltaChart c' u) := prob.cardyV_pos hsh ht_pos
  positivity

lemma psiTilde_eq_zero_iff (prob : FixedWeightProblem) {c' : ℝ} (hc' : 0 < c')
    (hsh : prob.totalShift ≤ c' / 12) {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hM : 0 < prob.cardyNorm (c' / 12) g) {u : ℝ} (hu : |u| ≤ virasoroAC c' ^ 2) :
    psiTilde prob c' g (u : ℂ) = 0 ↔ g (virasoroDeltaChart c' u) = 0 := by
  have him := psiTilde_im_ofReal prob hc' hg hu
  have hre := psiTilde_re_ofReal prob hc' hg hu
  have hpf := psiTilde_pref_pos prob hc' hsh hM hu
  have hre_eq : (psiTilde prob c' g (u : ℂ)).re =
      ((prob.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
        prob.cardyV (c' / 12) (virasoroDeltaChart c' u)) * g (virasoroDeltaChart c' u) := by
    rw [hre]; ring
  constructor
  · intro hz
    have h0 : (psiTilde prob c' g (u : ℂ)).re = 0 := by rw [hz]; simp
    rw [hre_eq, mul_eq_zero] at h0
    exact h0.resolve_left hpf.ne'
  · intro hg0
    refine Complex.ext ?_ him
    rw [hre_eq, hg0, mul_zero, Complex.zero_re]

lemma psiTilde_re_pos_iff (prob : FixedWeightProblem) {c' : ℝ} (hc' : 0 < c')
    (hsh : prob.totalShift ≤ c' / 12) {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hM : 0 < prob.cardyNorm (c' / 12) g) {u : ℝ} (hu : |u| ≤ virasoroAC c' ^ 2) :
    0 < (psiTilde prob c' g (u : ℂ)).re ↔ 0 < g (virasoroDeltaChart c' u) := by
  have hre := psiTilde_re_ofReal prob hc' hg hu
  have hpf := psiTilde_pref_pos prob hc' hsh hM hu
  have hre_eq : (psiTilde prob c' g (u : ℂ)).re =
      ((prob.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
        prob.cardyV (c' / 12) (virasoroDeltaChart c' u)) * g (virasoroDeltaChart c' u) := by
    rw [hre]; ring
  rw [hre_eq]
  exact mul_pos_iff_of_pos_left hpf

lemma weakExtremal_blnorm (prob : FixedWeightProblem) (H : HermiteBiehlerData)
    {c : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    {s : HbNodes H → ℕ → ℝ} (hs_pos : ∀ i : HbNodes H, ∀ᶠ n in atTop, 0 < s i n)
    (hs_tend : ∀ i : HbNodes H, Tendsto (fun n => uAiry (c n) (s i n)) atTop (𝓝 i.1))
    {B : ℕ → ℝ} (hB_tend : Tendsto (fun n => uAiry (c n) (B n)) atTop (𝓝 H.tm))
    {gs : ℕ → ℝ → ℝ} (hgs : ∀ᶠ n in atTop, IsWeakExtremal prob (c n) (hbPrescribedSet s n) (B n) (gs n)) :
    Tendsto (fun n => chartUT (c n) (B n)) atTop (𝓝 H.tm) ∧
      (∀ m : ℕ, TendstoUniformlyOn (fun n => psiTilde prob (c n) (gs n))
        (normProfile H.G) atTop (closedBall (0 : ℂ) ((m : ℝ) + 1))) := by
  have hB_pos := eventually_pos_of_uAiry_tendsto hc hB_tend
  obtain ⟨CB, cB, _, hcB1, hCB⟩ := chartUT_sub_uAiry_err (show 0 ≤ |H.tm| + 1 by positivity)
  have hB_chart : Tendsto (fun n => chartUT (c n) (B n)) atTop (𝓝 H.tm) := by
    have hev : ∀ᶠ n in atTop, |uAiry (c n) (B n) - chartUT (c n) (B n)| ≤ CB * (c n) ^ (-(2 / 3 : ℝ)) := by
      have hbd := hB_tend.eventually (Metric.ball_mem_nhds H.tm zero_lt_one)
      filter_upwards [hc.eventually_ge_atTop cB, hB_pos, hbd] with n hcn hBn hball
      have huM : |uAiry (c n) (B n)| ≤ |H.tm| + 1 := by
        rw [Real.dist_eq] at hball
        calc |uAiry (c n) (B n)| = |(uAiry (c n) (B n) - H.tm) + H.tm| := by ring_nf
          _ ≤ |uAiry (c n) (B n) - H.tm| + |H.tm| := abs_add_le _ _
          _ ≤ 1 + |H.tm| := by linarith
          _ = |H.tm| + 1 := by ring
      exact (hCB hcn hBn huM).2.2
    have hzero : Tendsto (fun n => uAiry (c n) (B n) - chartUT (c n) (B n)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => CB * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
        simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc).const_mul CB
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using h0.neg) h0 ?_ ?_
      · filter_upwards [hev] with n hn; linarith [(abs_le.mp hn).1]
      · filter_upwards [hev] with n hn; linarith [(abs_le.mp hn).2]
    simpa using hB_tend.sub hzero
  have hK : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop, B n ≤ virasoroDeltaChart (c n) (-K) := by
    refine ⟨|H.tm| + 1, by positivity, ?_⟩
    have hball_u := hB_tend.eventually (Metric.ball_mem_nhds H.tm zero_lt_one)
    filter_upwards [hc.eventually_ge_atTop cB, hB_pos, hball_u,
      virasoroAC_sq_eventually_ge hc (|H.tm| + 1),
      hB_chart.eventually (Metric.ball_mem_nhds H.tm zero_lt_one)] with n hcn hBn hbu hac hbc
    have hc_pos : 0 < c n := lt_of_lt_of_le zero_lt_one (hcB1.trans hcn)
    have huM : |uAiry (c n) (B n)| ≤ |H.tm| + 1 := by
      rw [Real.dist_eq, abs_lt] at hbu
      rw [abs_le]; constructor <;> linarith [neg_abs_le H.tm, le_abs_self H.tm]
    have hΔB := (hCB hcn hBn huM).2.1
    have h_ge : -(|H.tm| + 1) ≤ chartUT (c n) (B n) := by
      rw [Real.dist_eq, abs_lt] at hbc
      linarith [neg_abs_le H.tm]
    have h_le : chartUT (c n) (B n) ≤ |H.tm| + 1 := by
      rw [Real.dist_eq, abs_lt] at hbc
      linarith [le_abs_self H.tm]
    have hanti := (virasoroDeltaChart_strictAnti hc_pos).antitoneOn
    rw [← hΔB]
    exact hanti ⟨by linarith, by linarith⟩ ⟨by linarith [h_ge], h_le.trans hac⟩ h_ge
  have hnode : ∀ i : HbNodes H, ∃ ũ : ℕ → ℝ, Tendsto ũ atTop (𝓝 i.1) ∧
      ∀ᶠ n in atTop, 0 ≤ gs n (virasoroDeltaChart (c n) (ũ n)) := by
    intro i
    refine ⟨fun n => chartUT (c n) (s i n), ?_, ?_⟩
    · obtain ⟨Ci, ci, _, _, hCi⟩ := chartUT_sub_uAiry_err (show 0 ≤ |i.1| + 1 by positivity)
      have hball_u := (hs_tend i).eventually (Metric.ball_mem_nhds i.1 zero_lt_one)
      have hev : ∀ᶠ n in atTop, |uAiry (c n) (s i n) - chartUT (c n) (s i n)| ≤ Ci * (c n) ^ (-(2 / 3 : ℝ)) := by
        filter_upwards [hc.eventually_ge_atTop ci, hs_pos i, hball_u] with n hcn hsn hb
        rw [Real.dist_eq] at hb
        have huM : |uAiry (c n) (s i n)| ≤ |i.1| + 1 := by
          calc |uAiry (c n) (s i n)| = |(uAiry (c n) (s i n) - i.1) + i.1| := by ring_nf
            _ ≤ |uAiry (c n) (s i n) - i.1| + |i.1| := abs_add_le _ _
            _ ≤ 1 + |i.1| := by linarith
            _ = |i.1| + 1 := by ring
        exact (hCi hcn hsn huM).2.2
      have hzero : Tendsto (fun n => uAiry (c n) (s i n) - chartUT (c n) (s i n)) atTop (𝓝 0) := by
        have h0 : Tendsto (fun n => Ci * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
          simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc).const_mul Ci
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using h0.neg) h0 ?_ ?_
        · filter_upwards [hev] with n hn; linarith [(abs_le.mp hn).1]
        · filter_upwards [hev] with n hn; linarith [(abs_le.mp hn).2]
      simpa using (hs_tend i).sub hzero
    · obtain ⟨Ci, ci, _, _, hCi⟩ := chartUT_sub_uAiry_err (show 0 ≤ |i.1| + 1 by positivity)
      have hball_u := (hs_tend i).eventually (Metric.ball_mem_nhds i.1 zero_lt_one)
      filter_upwards [hc.eventually_ge_atTop ci, hs_pos i, hball_u, hgs] with n hcn hsn hb hwe
      rw [Real.dist_eq] at hb
      have huM : |uAiry (c n) (s i n)| ≤ |i.1| + 1 := by
        calc |uAiry (c n) (s i n)| = |(uAiry (c n) (s i n) - i.1) + i.1| := by ring_nf
          _ ≤ |uAiry (c n) (s i n) - i.1| + |i.1| := abs_add_le _ _
          _ ≤ 1 + |i.1| := by linarith
          _ = |i.1| + 1 := by ring
      rw [(hCi hcn hsn huM).2.1]
      exact hwe.2.2.2 _ (Or.inl ⟨i, rfl⟩)
  have hsf : ∀ᶠ n in atTop, IsSlackFeasible prob (c n / 12) (B n) 0 (gs n) :=
    hgs.mono fun _ hn => isWeakExtremal_slackFeasible hn
  obtain ⟨D_p⟩ := UniformPropositionPData.of_problem prob
  have hbl := (hb_blnorm D_p H hc tendsto_const_nhds
    (Eventually.of_forall fun _ => le_rfl) hsf hK hnode).2
    (fun x hx => hB_chart.eventually (le_mem_nhds hx))
  exact ⟨hB_chart, hbl.2.1⟩

/-! ### 3. Hurwitz disc isolation on a window for any HB cluster setup -/

lemma exists_window_radius {H : HermiteBiehlerData} (CD : HbClusterData H) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      (∀ k : Fin CD.K, CD.a < CD.z k - 2 * r₀ ∧ CD.z k + 2 * r₀ < CD.b) ∧
      (∀ j k : Fin CD.K, j ≠ k → 4 * r₀ ≤ |CD.z j - CD.z k|) ∧
      (∀ k : Fin CD.K, CD.z k ≠ H.tm → 2 * r₀ ≤ |CD.z k - H.tm|) := by
  have hK1 : CD.K - 1 < CD.K := Nat.sub_lt CD.hK zero_lt_one
  have hK0 : 0 < CD.K := CD.hK
  let margin : ℝ := min (CD.z ⟨CD.K - 1, hK1⟩ - CD.a) (CD.b - CD.z ⟨0, hK0⟩) / 4
  have hmargin : 0 < margin := by
    have := CD.ha; have := CD.hb; positivity
  let sepSet : Finset ℝ :=
    (Finset.univ.product Finset.univ |>.filter (fun p : Fin CD.K × Fin CD.K => p.1 ≠ p.2)).image
      (fun p => |CD.z p.1 - CD.z p.2| / 5)
  let tmSet : Finset ℝ :=
    (Finset.univ.filter (fun k : Fin CD.K => CD.z k ≠ H.tm)).image (fun k => |CD.z k - H.tm| / 3)
  let allR : Finset ℝ := insert margin (sepSet ∪ tmSet)
  have hpos_all : ∀ x ∈ allR, 0 < x := by
    intro x hx
    simp only [allR, Finset.mem_insert, Finset.mem_union, sepSet, tmSet, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with rfl | ⟨⟨j, k⟩, hjk, rfl⟩ | ⟨k, hk, rfl⟩
    · exact hmargin
    · exact div_pos (abs_pos.mpr (sub_ne_zero.mpr (CD.hz_anti.injective.ne hjk.2))) (by norm_num)
    · exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hk)) (by norm_num)
  have hne : allR.Nonempty := ⟨margin, Finset.mem_insert_self _ _⟩
  refine ⟨allR.min' hne, hpos_all _ (allR.min'_mem hne), ?_, ?_, ?_⟩
  · intro k
    have hm : allR.min' hne ≤ margin := allR.min'_le _ (Finset.mem_insert_self _ _)
    have hk_lo : CD.z ⟨CD.K - 1, hK1⟩ ≤ CD.z k := by
      rcases eq_or_lt_of_le (show (k : ℕ) ≤ CD.K - 1 by omega) with h | h
      · exact (congrArg CD.z (Fin.ext h.symm)).le
      · exact (CD.hz_anti h).le
    have hk_hi : CD.z k ≤ CD.z ⟨0, hK0⟩ := by
      rcases eq_or_lt_of_le (Nat.zero_le (k : ℕ)) with h | h
      · exact (congrArg CD.z (Fin.ext h.symm)).le
      · exact (CD.hz_anti h).le
    have hm1 : 2 * margin < CD.z ⟨CD.K - 1, hK1⟩ - CD.a := by
      have hml := min_le_left (CD.z ⟨CD.K - 1, hK1⟩ - CD.a) (CD.b - CD.z ⟨0, hK0⟩)
      have := CD.ha
      dsimp [margin]; linarith
    have hm2 : 2 * margin < CD.b - CD.z ⟨0, hK0⟩ := by
      have hmr := min_le_right (CD.z ⟨CD.K - 1, hK1⟩ - CD.a) (CD.b - CD.z ⟨0, hK0⟩)
      have := CD.hb
      dsimp [margin]; linarith
    constructor <;> linarith [hpos_all _ (allR.min'_mem hne)]
  · intro j k hjk
    have hle : allR.min' hne ≤ |CD.z j - CD.z k| / 5 := by
      refine allR.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_))
      simp only [sepSet, Finset.mem_image, Finset.mem_filter]
      exact ⟨(j, k), ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hjk⟩, rfl⟩
    linarith [hpos_all _ (allR.min'_mem hne)]
  · intro k hk
    have hle : allR.min' hne ≤ |CD.z k - H.tm| / 3 := by
      refine allR.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_))
      simp only [tmSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨k, hk, rfl⟩
    linarith [hpos_all _ (allR.min'_mem hne)]

lemma unique_double_zero_of_zeroCount_two {f : ℂ → ℂ} {c₀ u₀ : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hf : DifferentiableOn ℂ f (ball c₀ R))
    (hne : ∀ z ∈ sphere c₀ r, f z ≠ 0) (hzc : zeroCount f c₀ r = 2)
    (hu₀ : u₀ ∈ ball c₀ r) (hord2 : 2 ≤ analyticOrderNatAt f u₀) :
    analyticOrderNatAt f u₀ = 2 ∧ ∀ z ∈ ball c₀ r, f z = 0 → z = u₀ := by
  obtain ⟨hw, hfw⟩ := exists_nonzero_of_sphere hr hrR hne
  have hfin := support_orderNat_finite hf hw hfw hrR
  have hsum : zeroCount f c₀ r = ∑ z ∈ hfin.toFinset, analyticOrderNatAt f z := by
    unfold zeroCount
    rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hu_mem : u₀ ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hu₀, show analyticOrderNatAt f u₀ ≠ 0 by omega⟩
  have hle2 : analyticOrderNatAt f u₀ ≤ zeroCount f c₀ r := by
    rw [hsum]
    exact Finset.single_le_sum (f := fun z => analyticOrderNatAt f z) (fun _ _ => Nat.zero_le _) hu_mem
  have hord_eq : analyticOrderNatAt f u₀ = 2 := by omega
  refine ⟨hord_eq, fun z hz hfz => ?_⟩
  by_contra hzu
  have hz_pos : 0 < analyticOrderNatAt f z :=
    Nat.pos_of_ne_zero ((orderNat_ne_zero_iff hf hw hfw (ball_subset_ball hrR.le hz)).mpr hfz)
  have hz_mem : z ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hz, hz_pos.ne'⟩
  have hsub : ({u₀, z} : Finset ℂ) ⊆ hfin.toFinset := by
    intro w hw'; simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
    rcases hw' with rfl | rfl <;> assumption
  have hsum2 : analyticOrderNatAt f u₀ + analyticOrderNatAt f z ≤ zeroCount f c₀ r := by
    rw [hsum, ← Finset.sum_pair (Ne.symm hzu)]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
  omega

lemma exists_atom_in_set {ν : Measure ℝ} {S Z : Set ℝ}
    (hZ : Z.Finite) (hνS : 0 < ν S) (hnull : ν (S \ Z) = 0) :
    ∃ t ∈ S ∩ Z, 0 < ν {t} := by
  have hsub : S ⊆ (S \ Z) ∪ (S ∩ Z) := fun t ht => by
    by_cases htZ : t ∈ Z <;> [exact Or.inr ⟨ht, htZ⟩; exact Or.inl ⟨ht, htZ⟩]
  have hpos_int : 0 < ν (S ∩ Z) := by
    have h1 := measure_mono hsub (μ := ν) |>.trans (measure_union_le (S \ Z) (S ∩ Z))
    rw [hnull, zero_add] at h1
    exact lt_of_lt_of_le hνS h1
  have hfin_int : (S ∩ Z).Finite := hZ.subset Set.inter_subset_right
  have hbi : S ∩ Z = ⋃ t ∈ hfin_int.toFinset, ({t} : Set ℝ) := by
    ext t; simp [hfin_int.mem_toFinset]
  have hle : ν (S ∩ Z) ≤ ∑ t ∈ hfin_int.toFinset, ν {t} := by
    conv_lhs => rw [hbi]
    exact measure_biUnion_finset_le _ _
  have hsum_pos : 0 < ∑ t ∈ hfin_int.toFinset, ν {t} := lt_of_lt_of_le hpos_int hle
  by_contra hcon
  push Not at hcon
  have hsum0 : ∑ t ∈ hfin_int.toFinset, ν {t} = 0 :=
    Finset.sum_eq_zero fun t ht => le_antisymm (hcon t (hfin_int.mem_toFinset.mp ht)) (zero_le)
  exact hsum_pos.ne' hsum0

lemma setIntegral_Ioi_of_singleton {ν : Measure ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ Ioi (0 : ℝ))
    (F : ℝ → ℝ) (hnull : ν ((Ioi (0 : ℝ) ∩ {t | F t ≠ 0}) \ {t₀}) = 0) :
    ∫ t in Ioi (0 : ℝ), F t ∂ν = (ν {t₀}).toReal * F t₀ := by
  have hae0 : ∀ᵐ t ∂ν, t ∉ ((Ioi (0 : ℝ) ∩ {t | F t ≠ 0}) \ {t₀}) :=
    measure_eq_zero_iff_ae_notMem.1 hnull
  have hae : ∀ᵐ t ∂(ν.restrict (Ioi (0 : ℝ))), t ∉ ({t₀} : Set ℝ) → F t = 0 := by
    have h1 := ae_restrict_of_ae (μ := ν) (s := Ioi (0 : ℝ)) hae0
    have h2 := ae_restrict_mem (μ := ν) (measurableSet_Ioi (a := (0 : ℝ)))
    filter_upwards [h1, h2] with t ht1 ht2 ht0
    by_contra hFt
    exact ht1 ⟨⟨ht2, hFt⟩, ht0⟩
  have hrest : (ν.restrict (Ioi (0 : ℝ))).restrict {t₀} = ν {t₀} • Measure.dirac t₀ := by
    rw [Measure.restrict_restrict (measurableSet_singleton t₀), singleton_inter_of_mem ht₀,
      Measure.restrict_singleton]
  have h_ae_ind : F =ᵐ[ν.restrict (Ioi (0 : ℝ))] ({t₀} : Set ℝ).indicator F := by
    filter_upwards [hae] with t ht
    by_cases h : t ∈ ({t₀} : Set ℝ)
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h, ht h]
  rw [integral_congr_ae h_ae_ind, integral_indicator (measurableSet_singleton t₀), hrest,
    integral_smul_measure, integral_dirac, smul_eq_mul]

lemma spectralMeasure_bump_pos (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c)
    (hsh : prob.totalShift ≤ c / 12) (ν : Measure ℝ) {f : ℝ → ℝ} (hf : Continuous f)
    {U : Set ℝ} (hU_supp : ∀ u ∉ U, f u = 0)
    (hpos : 0 < ∫ u, f u ∂(spectralMeasure prob c ν)) :
    0 < ν (Ioi (0 : ℝ) ∩ uAiry c ⁻¹' U) := by
  rw [integral_spectralMeasure prob hc hsh ν hf] at hpos
  by_contra h0
  have hnull : ν (Ioi (0 : ℝ) ∩ uAiry c ⁻¹' U) = 0 := nonpos_iff_eq_zero.1 (not_lt.1 h0)
  have hae : ∀ᵐ t ∂(ν.restrict (Ioi (0 : ℝ))), spectralWeight prob c t * f (uAiry c t) = 0 := by
    have h1 := ae_restrict_of_ae (μ := ν) (s := Ioi (0 : ℝ))
      (measure_eq_zero_iff_ae_notMem.1 hnull)
    have h2 := ae_restrict_mem (μ := ν) (measurableSet_Ioi (a := (0 : ℝ)))
    filter_upwards [h1, h2] with t ht1 ht2
    have hnot : uAiry c t ∉ U := fun hu => ht1 ⟨ht2, hu⟩
    rw [hU_supp _ hnot, mul_zero]
  have hzero : ∫ t in Ioi (0 : ℝ), spectralWeight prob c t * f (uAiry c t) ∂ν = 0 :=
    integral_eq_zero_of_ae hae
  linarith

/-! ### 4. Hurwitz disc isolation on a window for any weak-extremal sequence -/

lemma hurwitz_window_isolation (prob : FixedWeightProblem) (H : HermiteBiehlerData)
    (CD : HbClusterData H) {c : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    {s : HbNodes H → ℕ → ℝ} (hs_pos : ∀ i : HbNodes H, ∀ᶠ n in atTop, 0 < s i n)
    (hs_tend : ∀ i : HbNodes H, Tendsto (fun n => uAiry (c n) (s i n)) atTop (𝓝 i.1))
    (hB_tend : Tendsto (fun n => uAiry (c n) (constrainedThreshold prob (c n) (hbPrescribedSet s n)))
      atTop (𝓝 H.tm))
    {gs : ℕ → ℝ → ℝ} (hgs : ∀ᶠ n in atTop,
      IsWeakExtremal prob (c n) (hbPrescribedSet s n)
        (constrainedThreshold prob (c n) (hbPrescribedSet s n)) (gs n))
    {r : ℝ} (hr0 : 0 < r)
    (hr_win : ∀ k : Fin CD.K, CD.a < CD.z k - 2 * r ∧ CD.z k + 2 * r < CD.b)
    (hr_sep : ∀ j k : Fin CD.K, j ≠ k → 4 * r ≤ |CD.z j - CD.z k|) :
    ∀ᶠ n in atTop,
      let R_m : ℝ := ↑(Nat.ceil (max |CD.a| |CD.b| + 2 * r + 2)) + 1
      DifferentiableOn ℂ (psiTilde prob (c n) (gs n)) (ball (0 : ℂ) R_m) ∧
      (∀ u : ℝ, u ∈ Icc CD.a CD.b → (∀ k : Fin CD.K, (u : ℂ) ∉ ball (CD.z k : ℂ) r) →
        psiTilde prob (c n) (gs n) (u : ℂ) ≠ 0) ∧
      (∀ k : Fin CD.K,
        (∀ w ∈ sphere (CD.z k : ℂ) r, psiTilde prob (c n) (gs n) w ≠ 0) ∧
        zeroCount (psiTilde prob (c n) (gs n)) (CD.z k : ℂ) r =
          if CD.z k ∈ H.S then 1 else 2) := by
  let m : ℕ := Nat.ceil (max |CD.a| |CD.b| + 2 * r + 2)
  let R_m : ℝ := (m : ℝ) + 1
  have hm_ge : max |CD.a| |CD.b| + 2 * r + 2 ≤ R_m := by
    have := Nat.le_ceil (max |CD.a| |CD.b| + 2 * r + 2)
    dsimp [R_m]; linarith
  have hRm_pos : 0 < R_m := by positivity
  let U : Set ℂ := ball (0 : ℂ) R_m
  have hU_open : IsOpen U := isOpen_ball
  obtain ⟨hB_chart, hbl⟩ := weakExtremal_blnorm prob H hc hs_pos hs_tend hB_tend hgs
  have hloc : TendstoLocallyUniformlyOn (fun n => psiTilde prob (c n) (gs n))
      (normProfile H.G) atTop U :=
    (hbl m).tendstoLocallyUniformlyOn.mono ball_subset_closedBall
  obtain ⟨c_an, hc_an, han⟩ := psiTilde_analyticOnNhd prob
  have hDiff_ev : ∀ᶠ n in atTop, DifferentiableOn ℂ (psiTilde prob (c n) (gs n)) U := by
    obtain ⟨D_p⟩ := UniformPropositionPData.of_problem prob
    have hD := D_p.hr1_pos
    filter_upwards [hc.eventually_ge_atTop c_an,
      chartAC_sq_eventually_ge hD hc R_m, hgs] with n hcn hAc hwe
    have hcpos : 0 < c n := hc_an.trans_le hcn
    have hsub : U ⊆ psiDom (c n) :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hAc)).trans
        (closedBall_chartAC_subset_psiDom hD hcpos)
    exact ((han hcn hwe.1).mono hsub).differentiableOn
  have hCont_ev : ∀ᶠ n in atTop, ContinuousOn (psiTilde prob (c n) (gs n)) U :=
    hDiff_ev.mono fun _ hd => hd.continuousOn
  have hG_diff : DifferentiableOn ℂ (normProfile H.G) U :=
    (normProfile_differentiable (hbExtremalProfile H)).differentiableOn
  let K_seg : Set ℂ := Complex.ofReal '' Icc CD.a CD.b
  have hK_seg : IsCompact K_seg := isCompact_Icc.image Complex.continuous_ofReal
  have hK_sub : K_seg ⊆ U := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    have hab : |u| ≤ max |CD.a| |CD.b| :=
      abs_le.mpr ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, hu.1],
        by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, hu.2]⟩
    linarith
  let W : Set ℂ := ⋃ k : Fin CD.K, ball (CD.z k : ℂ) r
  have hW_open : IsOpen W := isOpen_iUnion fun _ => isOpen_ball
  have hK_zeros : ∀ w ∈ K_seg, normProfile H.G w = 0 → w ∈ W := by
    rintro _ ⟨u, hu, rfl⟩ hw0
    obtain ⟨k, hk⟩ := (CD.hzero_win (u : ℂ) (by simpa using hu)).mp hw0
    exact mem_iUnion.mpr ⟨k, hk ▸ mem_ball_self hr0⟩
  have hOff := hurwitz_no_zeros_off hU_open hloc hCont_ev hK_seg hK_sub hW_open hK_zeros
  have hDiscs : ∀ k : Fin CD.K, ∀ᶠ n in atTop,
      (∀ w ∈ sphere (CD.z k : ℂ) r, psiTilde prob (c n) (gs n) w ≠ 0) ∧
      zeroCount (psiTilde prob (c n) (gs n)) (CD.z k : ℂ) r =
        if CD.z k ∈ H.S then 1 else 2 := by
    intro k
    let R' : ℝ := r + r / 2
    have hrR' : r < R' := by dsimp [R']; linarith
    have hballR' : ball (CD.z k : ℂ) R' ⊆ U := by
      intro w hw
      rw [mem_ball] at hw
      rw [mem_ball_zero_iff]
      have hzk : ‖(CD.z k : ℂ)‖ ≤ max |CD.a| |CD.b| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        have hz_in : CD.z k ∈ Icc CD.a CD.b :=
          ⟨by linarith [(hr_win k).1], by linarith [(hr_win k).2]⟩
        exact abs_le.mpr ⟨by linarith [neg_abs_le CD.a, le_max_left |CD.a| |CD.b|, hz_in.1],
          by linarith [le_abs_self CD.b, le_max_right |CD.a| |CD.b|, hz_in.2]⟩
      calc ‖w‖ ≤ ‖w - (CD.z k : ℂ)‖ + ‖(CD.z k : ℂ)‖ := norm_le_norm_sub_add w (CD.z k : ℂ)
        _ < R' + max |CD.a| |CD.b| := by
            linarith [show dist w (CD.z k : ℂ) = ‖w - (CD.z k : ℂ)‖ from dist_eq_norm w _]
        _ ≤ R_m := by dsimp [R']; linarith
    have hne_sph : ∀ w ∈ sphere (CD.z k : ℂ) r, normProfile H.G w ≠ 0 := by
      intro w hw hw0
      rw [mem_sphere, dist_eq_norm] at hw
      have hre : w.re ∈ Icc CD.a CD.b := by
        have h1 : |w.re - CD.z k| ≤ r := by
          calc |w.re - CD.z k| = |(w - (CD.z k : ℂ)).re| := by simp
            _ ≤ ‖w - (CD.z k : ℂ)‖ := Complex.abs_re_le_norm _
            _ = r := hw
        have := abs_le.mp h1
        exact ⟨by linarith [(hr_win k).1], by linarith [(hr_win k).2]⟩
      obtain ⟨j, hj⟩ := (CD.hzero_win w hre).mp hw0
      by_cases hjk : j = k
      · rw [hj, hjk, sub_self, norm_zero] at hw; linarith
      · have hdist : 4 * r ≤ ‖(CD.z j : ℂ) - (CD.z k : ℂ)‖ := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          exact hr_sep j k hjk
        rw [hj] at hw; linarith
    have hne_off : ∀ w ∈ ball (CD.z k : ℂ) R', w ≠ (CD.z k : ℂ) → normProfile H.G w ≠ 0 := by
      intro w hw hne hw0
      rw [mem_ball, dist_eq_norm] at hw
      have hre : w.re ∈ Icc CD.a CD.b := by
        have h1 : |w.re - CD.z k| ≤ R' := by
          calc |w.re - CD.z k| = |(w - (CD.z k : ℂ)).re| := by simp
            _ ≤ ‖w - (CD.z k : ℂ)‖ := Complex.abs_re_le_norm _
            _ ≤ R' := hw.le
        have h12 := abs_le.mp h1
        dsimp [R'] at h12
        exact ⟨by linarith [h12.1, (hr_win k).1], by linarith [h12.2, (hr_win k).2]⟩
      obtain ⟨j, hj⟩ := (CD.hzero_win w hre).mp hw0
      by_cases hjk : j = k
      · exact hne (hj.trans (by rw [hjk]))
      · have hdist : 4 * r ≤ ‖(CD.z j : ℂ) - (CD.z k : ℂ)‖ := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          exact hr_sep j k hjk
        rw [hj] at hw; dsimp [R'] at hw; linarith
    have hzc_G : zeroCount (normProfile H.G) (CD.z k : ℂ) r =
        if CD.z k ∈ H.S then 1 else 2 := by
      rw [zeroCount_eq_orderNat (hG_diff.mono hballR') hr0 hrR' hrR'
        (fun w hw0 hwR => hne_off w (mem_ball.mpr hwR) (dist_pos.mp hw0)), CD.hord k]
    filter_upwards [hurwitz_zeroCount hU_open hloc hDiff_ev hG_diff hr0 hrR' hballR' hne_sph]
      with n ⟨hsph, hzc⟩
    exact ⟨hsph, hzc.trans hzc_G⟩
  filter_upwards [hDiff_ev, hOff, eventually_all.2 hDiscs] with n hD hO hDi
  dsimp only
  refine ⟨hD, fun u hu hnot => ?_, hDi⟩
  exact hO (u : ℂ) ⟨⟨u, hu, rfl⟩, fun hw => by
    obtain ⟨k, hk⟩ := mem_iUnion.mp hw
    exact hnot k hk⟩

/-- Equivalence of `uAiry` and `chartUT` limits on bounded windows. -/
lemma chartUT_tendsto_of_uAiry {c t : ℕ → ℝ} {z : ℝ} (hc : Tendsto c atTop atTop)
    (ht : ∀ᶠ n in atTop, 0 < t n) (hu : Tendsto (fun n => uAiry (c n) (t n)) atTop (𝓝 z)) :
    Tendsto (fun n => chartUT (c n) (t n)) atTop (𝓝 z) := by
  obtain ⟨C, c0, _, _, hC⟩ := chartUT_sub_uAiry_err (show 0 ≤ |z| + 1 by positivity)
  have hbu := hu.eventually (Metric.ball_mem_nhds z zero_lt_one)
  have hev : ∀ᶠ n in atTop, |uAiry (c n) (t n) - chartUT (c n) (t n)| ≤ C * (c n) ^ (-(2 / 3 : ℝ)) := by
    filter_upwards [hc.eventually_ge_atTop c0, ht, hbu] with n hcn htn hb
    rw [Real.dist_eq, abs_lt] at hb
    have huM : |uAiry (c n) (t n)| ≤ |z| + 1 := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le z, le_abs_self z]
    exact (hC hcn htn huM).2.2
  have h0 : Tendsto (fun n => C * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc).const_mul C
  have hsub : Tendsto (fun n => uAiry (c n) (t n) - chartUT (c n) (t n)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using h0.neg) h0
      (hev.mono fun _ h => by linarith [(abs_le.mp h).1])
      (hev.mono fun _ h => by linarith [(abs_le.mp h).2])
  simpa using hu.sub hsub

end FormalResearch.ModularBootstrap.FixedWeight


