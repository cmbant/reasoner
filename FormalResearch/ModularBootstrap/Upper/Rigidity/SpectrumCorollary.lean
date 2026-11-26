module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Wiring

/-!
# Corollary `sr:cor`: the spectrum in `t` (clusters of a near-extremal measure)

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex`, Corollary `sr:cor` (spectrum in `t`).

Input: vague convergence `μ_j → μ_A` of the spectral measures `μ_j = μ_{S_j}` (the conclusion of
Theorem `Σ`, `SigmaConclusion`, component 5, `sigma_unconditional_probW`).  For a crossing sequence
`S` with `IsVagueLimit atTop S.μS airyMeasure` and the cluster `𝒞_{n}(r) = {t > 0 : |u(t) - a_n| ≤ r}`
(`r` small: `2r <` the gap of the nodes at `a_n`):

* `vague_node_mass`: `μ_j(|u - a_n| ≤ r) → 1/Ai'(a_n)²`;
* `cluster_mass_tendsto`: the Cardy-normalised cluster weight `Σ_{𝒞_n} d/(2π V(t))` (the integral
  `∫_{𝒞_n} (2πV)⁻¹ dν_j`) satisfies `c_j'^{-1/3} Σ_{𝒞_n} d/(2π V) → c_* /Ai'(a_n)²`, `c_* = 2ξ_*/(3β)`
  (`cStar`); the paper's `(1 + O(r) + o(1))` is `1 + o(1)` here;
* `position_identity`, `cluster_position`: exactly `(t - ξ̄ c')c'^{-1/3} = -c_* u(t) + c'^{-2/3} u(t)²/(3β²)`, hence on
  `𝒞_n(r)`: `|(t - ξ̄ c')c'^{-1/3} - c_*|a_n|| ≤ c_* r + c'^{-2/3}(|a_n| + r)²/(3β²)`
  (`c_*|a_n| = (|a_n|/|a_1|) A_opt`);
* `heavy_atom_near_node` (and `cluster_position_tendsto`, the `ρ`-form of the position statement): for compact `K`, `δ > 0` and `r > 0`, eventually every atom `t` of `ν_j`
  with `u(t) ∈ K` and window weight `ν_j{t}/(2πV(t)J(t)) ≥ δ` lies in some cluster
  `|u(t) - a_n| < r`.

Not formalised: the barycentre assertion `(t̄₂ - t̄₁)c'^{-1/3} → 0.20705` (a consequence of the first
two items), the single-level ratios `R_n` (conditional) and the degeneracy asymptotics `(sr:eD1)`
(needs the Cardy density asymptotics of Lemma 4(f)).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal Real

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.Duality

/-! ### Part 1: portmanteau for the vague limit `μ_A` -/

/-- `limsup μ_j(C) ≤ b` for a compact `C ⊆ U`, `U` open with `μ_A(U) ≤ b`. -/
lemma vague_limsup_le {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)]
    (hν : IsVagueLimit atTop μ airyMeasure) {C U : Set ℝ} (hC : IsCompact C) (hU : IsOpen U)
    (hCU : C ⊆ U) {b : ℝ} (hb0 : 0 ≤ b) (hb : airyMeasure U ≤ ENNReal.ofReal b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, (μ j C).toReal ≤ b + ε := by
  obtain ⟨f, hfC, hfU, hfcs, hf01⟩ := exists_continuous_one_zero_of_isCompact hC hU.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr hCU)
  have hlim := hν f f.continuous hfcs
  have hfν : ∫ u, f u ∂airyMeasure ≤ b := by
    have h1 : ENNReal.ofReal (∫ u, f u ∂airyMeasure) ≤ airyMeasure U :=
      integral_le_measure (fun x _ => (hf01 x).2) (fun x hx => by simp [hfU hx])
    exact (ENNReal.ofReal_le_ofReal_iff hb0).1 (h1.trans hb)
  filter_upwards [hlim.eventually (gt_mem_nhds (show ∫ u, f u ∂airyMeasure < b + ε by linarith))]
    with j hj
  have hint := integrable_of_cs (μ := μ j) f.continuous hfcs
  have h1 : μ j C ≤ ENNReal.ofReal (∫ u, f u ∂(μ j)) :=
    hint.measure_le_integral (Eventually.of_forall fun x => (hf01 x).1)
      (fun x hx => by simp [hfC hx])
  have hnn : 0 ≤ ∫ u, f u ∂(μ j) := integral_nonneg fun x => (hf01 x).1
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_ofReal hnn] at this
  linarith

/-- The airy measure of an open set containing no node vanishes. -/
lemma airyMeasure_eq_zero_of_forall {U : Set ℝ} (hU : MeasurableSet U) (h : ∀ i, airyNode i ∉ U) :
    airyMeasure U = 0 := by
  unfold airyMeasure
  rw [Measure.sum_apply _ hU]
  refine tsum_eq_zero_iff.2 fun i => ?_
  simp [Measure.dirac_apply' _ hU, Set.indicator, h i]

/-- A bump function around a node: `f(u) = max 0 (1 - |u - a|/s)`. -/
noncomputable def nodeBump (a s : ℝ) (u : ℝ) : ℝ := max 0 (1 - |u - a| / s)

lemma continuous_nodeBump (a s : ℝ) : Continuous (nodeBump a s) := by
  unfold nodeBump; fun_prop

lemma nodeBump_nonneg (a s u : ℝ) : 0 ≤ nodeBump a s u := le_max_left _ _

lemma nodeBump_le_one {s : ℝ} (hs : 0 < s) (a u : ℝ) : nodeBump a s u ≤ 1 := by
  unfold nodeBump
  refine max_le zero_le_one ?_
  have : 0 ≤ |u - a| / s := div_nonneg (abs_nonneg _) hs.le
  linarith

lemma nodeBump_self {s : ℝ} (_hs : 0 < s) (a : ℝ) : nodeBump a s a = 1 := by
  unfold nodeBump; simp

lemma nodeBump_eq_zero {s : ℝ} (hs : 0 < s) {a u : ℝ} (h : s ≤ |u - a|) : nodeBump a s u = 0 := by
  unfold nodeBump
  have : 1 ≤ |u - a| / s := by rw [le_div_iff₀ hs]; linarith
  exact max_eq_left (by linarith)

lemma hasCompactSupport_nodeBump {s : ℝ} (hs : 0 < s) (a : ℝ) : HasCompactSupport (nodeBump a s) := by
  refine HasCompactSupport.intro (K := Icc (a - s) (a + s)) isCompact_Icc fun u hu => ?_
  refine nodeBump_eq_zero hs ?_
  by_contra h
  push Not at h
  rw [abs_lt] at h
  exact hu ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `μ_A`-integral of a bump centred at a node `i` that vanishes at the other nodes. -/
lemma integral_nodeBump {i : ℕ} {s : ℝ} (hs : 0 < s)
    (hsep : ∀ k, k ≠ i → s ≤ |airyNode k - airyNode i|) :
    ∫ u, nodeBump (airyNode i) s u ∂airyMeasure = airyNodeWeight i := by
  rw [integral_airyMeasure (continuous_nodeBump _ _)
    (summable_of_cs (hasCompactSupport_nodeBump hs _) _), tsum_eq_single i]
  · rw [nodeBump_self hs, one_mul]
  · intro k hk
    rw [nodeBump_eq_zero hs (hsep k hk), zero_mul]

/-- **Mass of a node neighbourhood**: if the nodes `a_k`, `k ≠ i`, are at distance `≥ 2r` from `a_i`,
then `μ_j([a_i - r, a_i + r]) → 1/Ai'(a_i)²`. -/
theorem vague_node_mass {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)]
    (hν : IsVagueLimit atTop μ airyMeasure) (i : ℕ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ k, k ≠ i → 2 * r ≤ |airyNode k - airyNode i|) :
    Tendsto (fun j => (μ j (Icc (airyNode i - r) (airyNode i + r))).toReal) atTop
      (𝓝 (airyNodeWeight i)) := by
  set a := airyNode i with ha
  set w := airyNodeWeight i with hw
  have hw0 : 0 < w := airyNodeWeight_pos i
  have hr2 : 0 < 2 * r := by linarith
  -- lower bound: bump of width `r`
  have hlow : Tendsto (fun j => ∫ u, nodeBump a r u ∂(μ j)) atTop (𝓝 w) := by
    have := hν (nodeBump a r) (continuous_nodeBump _ _) (hasCompactSupport_nodeBump hr _)
    rwa [integral_nodeBump hr (fun k hk => by linarith [hsep k hk])] at this
  have hlow_le : ∀ j, ∫ u, nodeBump a r u ∂(μ j) ≤ (μ j (Icc (a - r) (a + r))).toReal := by
    intro j
    have h1 : ENNReal.ofReal (∫ u, nodeBump a r u ∂(μ j)) ≤ μ j (Icc (a - r) (a + r)) :=
      integral_le_measure (fun x _ => nodeBump_le_one hr _ _) (fun x hx => by
        refine le_of_eq (nodeBump_eq_zero hr ?_)
        by_contra h
        push Not at h
        rw [abs_lt] at h
        exact hx ⟨by linarith [h.1], by linarith [h.2]⟩)
    have hfin : μ j (Icc (a - r) (a + r)) < ∞ := isCompact_Icc.measure_lt_top
    exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 h1
  -- upper bound: `limsup ≤ w + ε` for every `ε`
  have hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, (μ j (Icc (a - r) (a + r))).toReal ≤ w + ε := by
    intro ε hε
    refine vague_limsup_le hν isCompact_Icc (U := Ioo (a - 2 * r) (a + 2 * r)) isOpen_Ioo
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) hw0.le ?_ hε
    -- `μ_A(U) = w`: only the node `a_i` lies in `U`
    unfold airyMeasure
    rw [Measure.sum_apply _ isOpen_Ioo.measurableSet]
    have hmem : a ∈ Ioo (a - 2 * r) (a + 2 * r) := ⟨by linarith, by linarith⟩
    refine le_trans (le_of_eq ?_) (le_refl _)
    rw [tsum_eq_single i]
    · rw [smul_apply, Measure.dirac_apply_of_mem hmem, smul_eq_mul, mul_one]
    · intro k hk
      have hk' : 2 * r ≤ |airyNode k - a| := hsep k hk
      have : airyNode k ∉ Ioo (a - 2 * r) (a + 2 * r) := by
        intro hmem
        have : |airyNode k - a| < 2 * r := by rw [abs_lt]; constructor <;> linarith [hmem.1, hmem.2]
        linarith
      simp [Measure.dirac_apply' _ isOpen_Ioo.measurableSet, Set.indicator, this]
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hlow.eventually (lt_mem_nhds (show w - ε < w by linarith)),
    hup (ε / 2) (half_pos hε)] with j h1 h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hlow_le j]

/-- **No mass off the nodes**: for compact `K` and `r > 0`, `μ_j(K ∩ {u : ∀ i, |u - a_i| ≥ r}) → 0`. -/
theorem vague_off_nodes {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)]
    (hν : IsVagueLimit atTop μ airyMeasure) {K : Set ℝ} (hK : IsCompact K) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun j => (μ j (K ∩ {u | ∀ i, r ≤ |u - airyNode i|})).toReal) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set F : Set ℕ := {i | -(|R| + 1) ≤ airyNode i} with hF
  have hFfin : F.Finite := by
    have h1 : ∀ᶠ i in atTop, airyNode i < -(|R| + 1) := tendsto_airyNode.eventually (eventually_lt_atBot _)
    obtain ⟨N, hN⟩ := eventually_atTop.1 h1
    refine (Set.finite_lt_nat N).subset fun i hi => ?_
    show i < N
    by_contra hcon
    exact absurd (hN i (not_lt.mp hcon)) (not_lt.mpr hi)
  set C : Set ℝ := K ∩ {u | ∀ i ∈ F, r ≤ |u - airyNode i|} with hC
  have hCclosed : IsClosed {u : ℝ | ∀ i ∈ F, r ≤ |u - airyNode i|} := by
    have : {u : ℝ | ∀ i ∈ F, r ≤ |u - airyNode i|} = ⋂ i ∈ F, {u | r ≤ |u - airyNode i|} := by
      ext u; simp
    rw [this]
    exact isClosed_biInter fun i _ => isClosed_le continuous_const (by fun_prop)
  have hCcpt : IsCompact C := hK.inter_right hCclosed
  set U : Set ℝ := Ioo (-(|R| + 1)) (|R| + 1) ∩ ⋂ i ∈ F, {u | r / 2 < |u - airyNode i|} with hU
  have hUopen : IsOpen U := by
    refine isOpen_Ioo.inter (hFfin.isOpen_biInter fun i _ => ?_)
    exact isOpen_lt continuous_const (by fun_prop)
  have hCU : C ⊆ U := by
    intro u hu
    refine ⟨?_, ?_⟩
    · have := hR hu.1
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      exact ⟨by linarith [(abs_le.mp this).1, le_abs_self R],
        by linarith [(abs_le.mp this).2, le_abs_self R]⟩
    · simp only [mem_iInter]
      intro i hi
      have := hu.2 i hi
      show r / 2 < |u - airyNode i|
      linarith
  have hν0 : airyMeasure U = 0 := by
    refine airyMeasure_eq_zero_of_forall hUopen.measurableSet fun k hk => ?_
    by_cases hkF : k ∈ F
    · have := (mem_iInter₂.1 hk.2) k hkF
      simp at this
      linarith
    · have hk' : airyNode k < -(|R| + 1) := not_le.mp hkF
      linarith [hk.1.1]
  have hlim := fun ε (hε : 0 < ε) => vague_limsup_le hν hCcpt hUopen hCU le_rfl
    (by rw [hν0]; simp) hε
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hlim (ε / 2) (half_pos hε)] with j hj
  have hsub : K ∩ {u | ∀ i, r ≤ |u - airyNode i|} ⊆ C := fun u hu => ⟨hu.1, fun i _ => hu.2 i⟩
  have hfin : μ j C < ∞ := hCcpt.measure_lt_top
  have h1 : (μ j (K ∩ {u | ∀ i, r ≤ |u - airyNode i|})).toReal ≤ (μ j C).toReal :=
    ENNReal.toReal_mono hfin.ne (measure_mono hsub)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  linarith


/-! ### Part 2: the chart `u ↔ t` -/

/-- `J(t) = c_* c^{1/3} (1 - u ε/(β ξ_*))`. -/
lemma jAiry_eq {c : ℝ} (hc : 0 < c) (t : ℝ) :
    jAiry c t = cStar * c ^ ((1 : ℝ) / 3) * (1 - uAiry c t * epsAiry c / (betaTip * xiStar)) := by
  have h := xi_sub_uAiry_mul_slope hc t
  have hb := betaTip_pos.ne'
  have hx := xiStar_pos.ne'
  unfold jAiry cStar
  rw [← h]
  unfold slopeAiry
  field_simp

/-- `|J(t) - c_* c^{1/3}| ≤ c_* c^{1/3} · M ε/(β ξ_*)` when `|u(t)| ≤ M`. -/
lemma jAiry_bounds {c : ℝ} (hc : 0 < c) {t M : ℝ} (hM : |uAiry c t| ≤ M) :
    |jAiry c t - cStar * c ^ ((1 : ℝ) / 3)| ≤
      cStar * c ^ ((1 : ℝ) / 3) * (M * epsAiry c / (betaTip * xiStar)) := by
  have hK : 0 < cStar * c ^ ((1 : ℝ) / 3) := mul_pos cStar_pos (Real.rpow_pos_of_pos hc _)
  have hd : 0 < betaTip * xiStar := mul_pos betaTip_pos xiStar_pos
  have he := epsAiry_pos hc
  rw [jAiry_eq hc t]
  have : cStar * c ^ ((1 : ℝ) / 3) * (1 - uAiry c t * epsAiry c / (betaTip * xiStar)) -
      cStar * c ^ ((1 : ℝ) / 3) =
      -(cStar * c ^ ((1 : ℝ) / 3)) * (uAiry c t * epsAiry c / (betaTip * xiStar)) := by ring
  rw [this, abs_mul, abs_neg, abs_of_pos hK, abs_div, abs_mul, abs_of_pos he, abs_of_pos hd]
  refine mul_le_mul_of_nonneg_left ?_ hK.le
  rw [div_le_div_iff_of_pos_right hd]
  exact mul_le_mul_of_nonneg_right hM he.le

/-- **The chart identity**: for `t ≥ 0`, with `u = u(t)`,
`t - ξ̄ c = c^{1/3} (-c_* u + c^{-2/3} u²/(3β²))`. -/
lemma position_identity {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    t - xiBar * c = c ^ ((1 : ℝ) / 3) *
      (-cStar * uAiry c t + epsAiry c * uAiry c t ^ 2 / (3 * betaTip ^ 2)) := by
  have h1 : t = c / 3 * (xiStar - uAiry c t * slopeAiry c) ^ 2 := by
    rw [xi_sub_uAiry_mul_slope hc, Real.sq_sqrt (by positivity)]
    field_simp
  generalize uAiry c t = u at h1 ⊢
  have hb := betaTip_pos.ne'
  rw [← c_mul_eps hc]
  unfold xiBar cStar slopeAiry at *
  rw [h1]
  field_simp
  ring

/-- **Position of a cluster**: if `|u(t) - a| ≤ r` then
`|(t - ξ̄ c)c^{-1/3} - c_*(-a)| ≤ c_* r + c^{-2/3}(|a| + r)²/(3β²)`. -/
theorem cluster_position {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) {a r : ℝ}
    (h : |uAiry c t - a| ≤ r) :
    |(t - xiBar * c) / c ^ ((1 : ℝ) / 3) - cStar * (-a)| ≤
      cStar * r + epsAiry c * (|a| + r) ^ 2 / (3 * betaTip ^ 2) := by
  have hcp : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
  have hid : (t - xiBar * c) / c ^ ((1 : ℝ) / 3) =
      -cStar * uAiry c t + epsAiry c * uAiry c t ^ 2 / (3 * betaTip ^ 2) := by
    rw [position_identity hc ht, mul_div_cancel_left₀ _ hcp.ne']
  rw [hid]
  set u := uAiry c t
  have hu : |u| ≤ |a| + r := by
    have := abs_sub_abs_le_abs_sub u a
    linarith
  have hu2 : u ^ 2 ≤ (|a| + r) ^ 2 := by
    rw [← sq_abs u]; exact pow_le_pow_left₀ (abs_nonneg _) hu 2
  have he := epsAiry_pos hc
  have hb : 0 < 3 * betaTip ^ 2 := by have := betaTip_pos; positivity
  have hcs := cStar_pos
  have e1 : -cStar * u + epsAiry c * u ^ 2 / (3 * betaTip ^ 2) - cStar * (-a) =
      -(cStar * (u - a)) + epsAiry c * u ^ 2 / (3 * betaTip ^ 2) := by ring
  rw [e1]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_neg, abs_mul, abs_of_pos hcs]
    exact mul_le_mul_of_nonneg_left h hcs.le
  · rw [abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu2 he.le) hb.le

/-! ### Part 3: cluster weights -/

/-- The Cardy-normalised weight of the cluster `{t > 0 : u(t) ∈ B}`:
`∫_{u(t) ∈ B} 1/(2π V(c/12, t)) dν(t)` (for `ν = Σ d_n δ_{t_n}`: `Σ d_n/(2π V(t_n))`). -/
noncomputable def clusterWeight (prob : FixedWeightProblem) (c : ℝ) (ν : Measure ℝ) (B : Set ℝ) :
    ℝ≥0∞ :=
  ∫⁻ t in uAiry c ⁻¹' B ∩ Ioi 0, ENNReal.ofReal (1 / (2 * π * prob.cardyV (c / 12) t)) ∂ν

lemma spectralMeasure_apply (prob : FixedWeightProblem) (c : ℝ) (ν : Measure ℝ) {B : Set ℝ}
    (hB : MeasurableSet B) :
    spectralMeasure prob c ν B = ∫⁻ t in uAiry c ⁻¹' B ∩ Ioi 0, spectralDensity prob c t ∂ν := by
  unfold spectralMeasure
  rw [Measure.map_apply (continuous_uAiry c).measurable hB,
    withDensity_apply _ ((continuous_uAiry c).measurable hB),
    Measure.restrict_restrict ((continuous_uAiry c).measurable hB)]

lemma weight_eq_jAiry_mul {prob : FixedWeightProblem} {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) {t : ℝ} (ht : 0 < t) :
    1 / (2 * π * prob.cardyV (c / 12) t) = jAiry c t * spectralWeight prob c t := by
  have hJ := (jAiry_pos hc ht).ne'
  have hV := (prob.cardyV_pos ha ht).ne'
  unfold spectralWeight
  field_simp

lemma clusterWeight_le {prob : FixedWeightProblem} {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) (ν : Measure ℝ) {B : Set ℝ} (hB : MeasurableSet B) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ t, 0 < t → uAiry c t ∈ B → jAiry c t ≤ A) :
    clusterWeight prob c ν B ≤ ENNReal.ofReal A * spectralMeasure prob c ν B := by
  rw [spectralMeasure_apply prob c ν hB,
    ← lintegral_const_mul' (ENNReal.ofReal A) (spectralDensity prob c) ENNReal.ofReal_ne_top]
  unfold clusterWeight
  refine setLIntegral_mono' (((continuous_uAiry c).measurable hB).inter measurableSet_Ioi)
    fun t ht => ?_
  rw [weight_eq_jAiry_mul hc ha ht.2]
  unfold spectralDensity
  rw [← ENNReal.ofReal_mul hA0]
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (hA t ht.2 ht.1) (spectralWeight_pos hc ha ht.2).le)

lemma le_clusterWeight {prob : FixedWeightProblem} {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) (ν : Measure ℝ) {B : Set ℝ} (hB : MeasurableSet B) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ t, 0 < t → uAiry c t ∈ B → A ≤ jAiry c t) :
    ENNReal.ofReal A * spectralMeasure prob c ν B ≤ clusterWeight prob c ν B := by
  rw [spectralMeasure_apply prob c ν hB,
    ← lintegral_const_mul' (ENNReal.ofReal A) (spectralDensity prob c) ENNReal.ofReal_ne_top]
  unfold clusterWeight
  refine setLIntegral_mono' (((continuous_uAiry c).measurable hB).inter measurableSet_Ioi)
    fun t ht => ?_
  rw [weight_eq_jAiry_mul hc ha ht.2]
  unfold spectralDensity
  rw [← ENNReal.ofReal_mul hA0]
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (hA t ht.2 ht.1) (spectralWeight_pos hc ha ht.2).le)

lemma tendsto_epsAiry {c : ℕ → ℝ} (hct : Tendsto c atTop atTop) :
    Tendsto (fun j => epsAiry (c j)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hct

/-- **Cluster mass (`sr:cor`, masses)**: if `μ_j = μ_{S_j} → μ_A` vaguely and `[a_i - r, a_i + r]`
contains no other node, then the Cardy-normalised cluster weight satisfies
`c_j^{-1/3} ∫_{|u(t) - a_i| ≤ r} (2πV)⁻¹ dν_j → c_*/Ai'(a_i)²`. -/
theorem cluster_mass_tendsto {prob : FixedWeightProblem} {c : ℕ → ℝ} {ν : ℕ → Measure ℝ}
    (hct : Tendsto c atTop atTop) (hcpos : ∀ j, 0 < c j)
    (hshift : ∀ j, prob.totalShift ≤ c j / 12)
    [∀ j, IsLocallyFiniteMeasure (spectralMeasure prob (c j) (ν j))]
    (hν : IsVagueLimit atTop (fun j => spectralMeasure prob (c j) (ν j)) airyMeasure)
    (i : ℕ) {r : ℝ} (hr : 0 < r) (hsep : ∀ k, k ≠ i → 2 * r ≤ |airyNode k - airyNode i|) :
    Tendsto (fun j => (clusterWeight prob (c j) (ν j)
        (Icc (airyNode i - r) (airyNode i + r))).toReal / (c j) ^ ((1 : ℝ) / 3)) atTop
      (𝓝 (cStar * airyNodeWeight i)) := by
  set a := airyNode i with ha
  set B : Set ℝ := Icc (a - r) (a + r) with hBdef
  have hBm : MeasurableSet B := measurableSet_Icc
  have hBc : IsCompact B := isCompact_Icc
  set M : ℝ := |a| + r with hM
  have hBM : ∀ u ∈ B, |u| ≤ M := fun u hu => by
    have h1 : |u - a| ≤ r := abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have := abs_sub_abs_le_abs_sub u a
    linarith
  set e : ℕ → ℝ := fun j => M * epsAiry (c j) / (betaTip * xiStar) with he
  have hd : 0 < betaTip * xiStar := mul_pos betaTip_pos xiStar_pos
  have he0 : Tendsto e atTop (𝓝 0) := by
    have := ((tendsto_epsAiry hct).const_mul M).div_const (betaTip * xiStar)
    simpa [he] using this
  have hm : Tendsto (fun j => (spectralMeasure prob (c j) (ν j) B).toReal) atTop
      (𝓝 (airyNodeWeight i)) := vague_node_mass hν i hr hsep
  have hlow : Tendsto (fun j => cStar * (1 - e j) * (spectralMeasure prob (c j) (ν j) B).toReal)
      atTop (𝓝 (cStar * airyNodeWeight i)) := by
    have := (((he0.const_sub 1).const_mul cStar).mul hm)
    simpa using this
  have hup : Tendsto (fun j => cStar * (1 + e j) * (spectralMeasure prob (c j) (ν j) B).toReal)
      atTop (𝓝 (cStar * airyNodeWeight i)) := by
    have := (((he0.const_add 1).const_mul cStar).mul hm)
    simpa using this
  have hsand : ∀ j, e j < 1 →
      cStar * (1 - e j) * (spectralMeasure prob (c j) (ν j) B).toReal ≤
          (clusterWeight prob (c j) (ν j) B).toReal / (c j) ^ ((1 : ℝ) / 3) ∧
        (clusterWeight prob (c j) (ν j) B).toReal / (c j) ^ ((1 : ℝ) / 3) ≤
          cStar * (1 + e j) * (spectralMeasure prob (c j) (ν j) B).toReal := by
    intro j hj
    have hc := hcpos j
    have hK : 0 < c j ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
    have hKc : 0 < cStar * c j ^ ((1 : ℝ) / 3) := mul_pos cStar_pos hK
    have hej : e j = M * epsAiry (c j) / (betaTip * xiStar) := rfl
    have hM0 : 0 < M := by have := abs_nonneg a; rw [hM]; linarith
    have he_nn : 0 ≤ e j := by
      rw [hej]; exact div_nonneg (mul_nonneg hM0.le (epsAiry_pos hc).le) hd.le
    have hbd : ∀ t, 0 < t → uAiry (c j) t ∈ B →
        |jAiry (c j) t - cStar * c j ^ ((1 : ℝ) / 3)| ≤ cStar * c j ^ ((1 : ℝ) / 3) * e j := by
      intro t _ ht
      rw [hej]; exact jAiry_bounds hc (hBM _ ht)
    have hlo : ∀ t, 0 < t → uAiry (c j) t ∈ B →
        cStar * c j ^ ((1 : ℝ) / 3) * (1 - e j) ≤ jAiry (c j) t := by
      intro t ht1 ht2
      have := (abs_le.1 (hbd t ht1 ht2)).1
      linarith
    have hhi : ∀ t, 0 < t → uAiry (c j) t ∈ B →
        jAiry (c j) t ≤ cStar * c j ^ ((1 : ℝ) / 3) * (1 + e j) := by
      intro t ht1 ht2
      have := (abs_le.1 (hbd t ht1 ht2)).2
      linarith
    have hA0 : 0 ≤ cStar * c j ^ ((1 : ℝ) / 3) * (1 - e j) :=
      mul_nonneg hKc.le (by linarith)
    have hA0' : 0 ≤ cStar * c j ^ ((1 : ℝ) / 3) * (1 + e j) :=
      mul_nonneg hKc.le (by linarith)
    have hWl := le_clusterWeight hc (hshift j) (ν j) hBm hA0 hlo
    have hWu := clusterWeight_le hc (hshift j) (ν j) hBm hA0' hhi
    have hμfin : spectralMeasure prob (c j) (ν j) B < ∞ := hBc.measure_lt_top
    have hWfin : clusterWeight prob (c j) (ν j) B ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμfin.ne) hWu
    have h1 := ENNReal.toReal_mono hWfin hWl
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμfin.ne) hWu
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA0] at h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA0'] at h2
    constructor
    · rw [le_div_iff₀ hK]; linarith only [h1]
    · rw [div_le_iff₀ hK]; linarith only [h2]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [he0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with j hj
    exact (hsand j hj).1
  · filter_upwards [he0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with j hj
    exact (hsand j hj).2


/-! ### Part 4: heavy atoms, cluster positions, and `sr:cor` for crossing sequences -/

/-- **Heavy atoms sit at the nodes**: for compact `K`, `δ, r > 0`, eventually every atom `t > 0` of
`ν_j` with `u(t) ∈ K` and spectral weight `ν_j{t}/(2πV(t)J(t)) ≥ δ` lies within `r` (in `u`) of a node. -/
theorem heavy_atom_near_node {prob : FixedWeightProblem} {c : ℕ → ℝ} {ν : ℕ → Measure ℝ}
    [∀ j, IsLocallyFiniteMeasure (spectralMeasure prob (c j) (ν j))]
    (hν : IsVagueLimit atTop (fun j => spectralMeasure prob (c j) (ν j)) airyMeasure)
    {K : Set ℝ} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ j in atTop, ∀ t : ℝ, 0 < t → uAiry (c j) t ∈ K →
      ENNReal.ofReal δ ≤ ν j {t} * spectralDensity prob (c j) t →
        ∃ i, |uAiry (c j) t - airyNode i| < r := by
  have hlim := vague_off_nodes hν hK hr
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with j hj t ht hKt hw
  by_contra hno
  push Not at hno
  set E : Set ℝ := K ∩ {u | ∀ i, r ≤ |u - airyNode i|} with hE
  have hmem : uAiry (c j) t ∈ E := ⟨hKt, hno⟩
  have h1 : ν j {t} * spectralDensity prob (c j) t ≤
      spectralMeasure prob (c j) (ν j) {uAiry (c j) t} := by
    rw [spectralMeasure_apply prob (c j) (ν j) (measurableSet_singleton _), mul_comm]
    calc spectralDensity prob (c j) t * ν j {t}
        = ∫⁻ x in {t}, spectralDensity prob (c j) x ∂(ν j) := (lintegral_singleton _ _).symm
      _ ≤ _ := lintegral_mono_set (by
          intro x hx
          rw [mem_singleton_iff] at hx
          subst hx
          exact ⟨rfl, ht⟩)
  have h2 : spectralMeasure prob (c j) (ν j) {uAiry (c j) t} ≤
      spectralMeasure prob (c j) (ν j) E := measure_mono (by simpa using hmem)
  have hfin : spectralMeasure prob (c j) (ν j) E < ∞ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left) hK.measure_lt_top
  have h3 : ENNReal.ofReal δ ≤ spectralMeasure prob (c j) (ν j) E := hw.trans (h1.trans h2)
  have := (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 h3
  linarith

/-- **Positions of the clusters**: for every `ρ > 0` there is `r₀ > 0` such that for `r ≤ r₀`,
eventually every `t ≥ 0` with `|u(t) - a_i| ≤ r` has `(t - ξ̄ c_j) c_j^{-1/3}` within `ρ` of
`c_* |a_i|`. (`c_* |a_i| = (|a_i|/|a_1|) A_opt`.) -/
theorem cluster_position_tendsto {c : ℕ → ℝ} (hct : Tendsto c atTop atTop) (hcpos : ∀ j, 0 < c j)
    (i : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ᶠ j in atTop, ∀ t : ℝ, 0 ≤ t →
      |uAiry (c j) t - airyNode i| ≤ r →
        |(t - xiBar * c j) / (c j) ^ ((1 : ℝ) / 3) - cStar * (|airyNode i|)| ≤ ρ := by
  have hcs := cStar_pos
  have hb : 0 < 3 * betaTip ^ 2 := by have := betaTip_pos; positivity
  refine ⟨ρ / (2 * cStar), by positivity, fun r hr hr0 => ?_⟩
  have hcr : cStar * r ≤ ρ / 2 := by
    have := mul_le_mul_of_nonneg_left hr0 hcs.le
    have e : cStar * (ρ / (2 * cStar)) = ρ / 2 := by field_simp
    linarith
  have hev := (tendsto_epsAiry hct).eventually
    (gt_mem_nhds (show (0 : ℝ) < ρ / 2 / ((|airyNode i| + r) ^ 2 / (3 * betaTip ^ 2) + 1) by
      have : 0 < (|airyNode i| + r) ^ 2 / (3 * betaTip ^ 2) + 1 := by positivity
      positivity))
  filter_upwards [hev] with j hj t ht h
  have hc := hcpos j
  have h1 := cluster_position hc ht h
  have hneg : -airyNode i = |airyNode i| := by
    rw [abs_of_neg (airyNode_neg i)]
  rw [hneg] at h1
  refine h1.trans ?_
  set Q := (|airyNode i| + r) ^ 2 / (3 * betaTip ^ 2) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have he := epsAiry_pos hc
  have : epsAiry (c j) * (|airyNode i| + r) ^ 2 / (3 * betaTip ^ 2) = epsAiry (c j) * Q := by
    rw [hQ]; ring
  rw [this]
  have h2 : epsAiry (c j) * (Q + 1) < ρ / 2 := by
    rwa [lt_div_iff₀ (by positivity)] at hj
  nlinarith only [h2, he, hQ0, hcr]

/-- **`sr:cor` for a crossing sequence** (`spectral_rigidity.tex`): for the spectral measures
`μ_j = μ_{S_j}` satisfying the conclusion of Theorem `Σ`, the cluster `{|u(t) - a_i| ≤ r}` has
Cardy-normalised weight `c_j^{-1/3} Σ d/(2πV) → c_*/Ai'(a_i)²`. -/
theorem crossing_cluster_mass {prob : FixedWeightProblem} (S : CrossingSequence prob)
    (hσ : SigmaConclusion S.μS) (i : ℕ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ k, k ≠ i → 2 * r ≤ |airyNode k - airyNode i|) :
    Tendsto (fun j => (clusterWeight prob (S.c j) (S.meas j).ν
        (Icc (airyNode i - r) (airyNode i + r))).toReal / (S.c j) ^ ((1 : ℝ) / 3)) atTop
      (𝓝 (cStar * airyNodeWeight i)) := by
  have : ∀ j, IsLocallyFiniteMeasure (spectralMeasure prob (S.c j) (S.meas j).ν) :=
    S.isLocallyFinite
  exact cluster_mass_tendsto S.tendsto_c S.c_pos S.shift_le hσ.2.2.2.1 i hr hsep

/-- Heavy atoms of a crossing sequence satisfying `Σ` sit within `r` of the nodes. -/
theorem crossing_heavy_atom {prob : FixedWeightProblem} (S : CrossingSequence prob)
    (hσ : SigmaConclusion S.μS) {K : Set ℝ} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) {r : ℝ}
    (hr : 0 < r) :
    ∀ᶠ j in atTop, ∀ t : ℝ, 0 < t → uAiry (S.c j) t ∈ K →
      ENNReal.ofReal δ ≤ (S.meas j).ν {t} * spectralDensity prob (S.c j) t →
        ∃ i, |uAiry (S.c j) t - airyNode i| < r := by
  have : ∀ j, IsLocallyFiniteMeasure (spectralMeasure prob (S.c j) (S.meas j).ν) :=
    S.isLocallyFinite
  exact heavy_atom_near_node hσ.2.2.2.1 hK hδ hr

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.cluster_mass_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cluster_mass_tendsto

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.heavy_atom_near_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms heavy_atom_near_node

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.cluster_position_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cluster_position_tendsto

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.crossing_cluster_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms crossing_cluster_mass

end FormalResearch.ModularBootstrap.Upper.Rigidity
