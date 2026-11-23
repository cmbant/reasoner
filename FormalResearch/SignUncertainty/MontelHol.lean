module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Analysis.Complex.Basic

/-!
# Montel's theorem on the right half-plane

A sequence of holomorphic functions that are eventually holomorphic and locally uniformly bounded on
`{Re w > 0}` (exhausted by the open sets `montelO j`) has a subsequence converging locally uniformly there
(`montel_rightHalfPlane`).  Mathlib has no normal-family theorem; this one is proved by the Cauchy estimate,
Arzelà–Ascoli on closed rectangles, and a diagonal argument.
-/

@[expose] public section

open Complex Set Filter Topology Metric
open scoped BoundedContinuousFunction

namespace FormalResearch.SignUncertainty

/-- Cauchy estimate: a function holomorphic on `O`, bounded by `M` on the `δ`-thickening of a convex `K ⊆ O`,
is `M/δ`-Lipschitz on `K`. -/
lemma montel_lipschitz {g : ℂ → ℂ} {O K : Set ℂ} {δ M : ℝ} (hO : IsOpen O)
    (hg : DifferentiableOn ℂ g O) (hK : Convex ℝ K) (hδ : 0 < δ) (hKO : ∀ z ∈ K, closedBall z δ ⊆ O)
    (hM : ∀ z ∈ K, ∀ w ∈ closedBall z δ, ‖g w‖ ≤ M) {z w : ℂ} (hz : z ∈ K) (hw : w ∈ K) :
    ‖g z - g w‖ ≤ M / δ * ‖z - w‖ := by
  have hder : ∀ x ∈ K, ‖deriv g x‖ ≤ M / δ := by
    intro x hx
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ ?_ ?_
    · refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball _ hδ.ne']
      exact hg.mono (hKO x hx)
    · intro y hy
      exact hM x hx y (sphere_subset_closedBall hy)
  have hdiff : ∀ x ∈ K, DifferentiableAt ℂ g x := fun x hx =>
    hg.differentiableAt (hO.mem_nhds (hKO x hx (mem_closedBall_self hδ.le)))
  exact Convex.norm_image_sub_le_of_norm_deriv_le hdiff hder hK hw hz

/-- Relative compactness on one compact convex set: the restrictions to `K` of a sequence bounded on the
`δ`-thickening of `K` form a relatively compact set of bounded continuous functions. -/
lemma montel_bcf {g : ℕ → ℂ → ℂ} {O K : Set ℂ} {δ M : ℝ} (hO : IsOpen O)
    (hg : ∀ n, DifferentiableOn ℂ (g n) O) (hKc : IsCompact K) (hK : Convex ℝ K) (hδ : 0 < δ)
    (hKO : ∀ z ∈ K, closedBall z δ ⊆ O)
    (hM : ∀ n, ∀ z ∈ K, ∀ w ∈ closedBall z δ, ‖g n w‖ ≤ M) :
    ∃ h : ℕ → (K →ᵇ ℂ), (∀ n (z : K), h n z = g n z) ∧ IsCompact (closure (Set.range h)) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hcont : ∀ n, Continuous (K.restrict (g n)) := fun n =>
    ((hg n).continuousOn.mono (fun z hz => hKO z hz (mem_closedBall_self hδ.le))).restrict
  let h : ℕ → (K →ᵇ ℂ) := fun n => BoundedContinuousFunction.mkOfCompact ⟨_, hcont n⟩
  have hh : ∀ n (z : K), h n z = g n z := fun n z => rfl
  refine ⟨h, hh, ?_⟩
  set A : Set (K →ᵇ ℂ) := range h with hA
  have hlip : ∀ i : A, LipschitzWith (Real.toNNReal (M / δ)) (fun z : K => (i : K →ᵇ ℂ) z) := by
    rintro ⟨_, n, rfl⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have := montel_lipschitz hO (hg n) hK hδ hKO (hM n) x.2 y.2
    simp only [dist_eq_norm, hh, Real.coe_toNNReal']
    refine this.trans ?_
    have hM0 : 0 ≤ M / δ := by
      have := hM 0 x.1 x.2 x.1 (mem_closedBall_self hδ.le)
      exact div_nonneg ((norm_nonneg _).trans this) hδ.le
    simp [max_eq_left hM0, Subtype.dist_eq, dist_eq_norm]
  have heq : Equicontinuous ((↑) : A → K → ℂ) :=
    (LipschitzWith.uniformEquicontinuous (fun (i : A) (z : K) => (i : K →ᵇ ℂ) z) _ hlip).equicontinuous
  exact BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) M) (isCompact_closedBall 0 M) A
    (by
      rintro f x ⟨n, rfl⟩
      simpa [hh] using hM n x.1 x.2 x.1 (mem_closedBall_self hδ.le)) heq

/-- The rectangle `K_j = {1/(j+1) ≤ Re w ≤ j+1, |Im w| ≤ j+1}`. -/
def montelK (j : ℕ) : Set ℂ :=
  {w | 1 / ((j : ℝ) + 1) ≤ w.re ∧ w.re ≤ (j : ℝ) + 1 ∧ |w.im| ≤ (j : ℝ) + 1}

/-- The open rectangle `O_j ⊇` the `1/(2(j+1))`-thickening of `K_j`. -/
def montelO (j : ℕ) : Set ℂ :=
  {w | 1 / (4 * ((j : ℝ) + 1)) < w.re ∧ w.re < (j : ℝ) + 2 ∧ |w.im| < (j : ℝ) + 2}

lemma isOpen_montelO (j : ℕ) : IsOpen (montelO j) := by
  unfold montelO
  refine (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const))

lemma convex_montelK (j : ℕ) : Convex ℝ (montelK j) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  simp only [montelK, mem_setOf_eq, Complex.add_re, Complex.smul_re, Complex.add_im, Complex.smul_im,
    smul_eq_mul]
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  calc |a * x.im + b * y.im| ≤ |a * x.im| + |b * y.im| := abs_add_le _ _
    _ = a * |x.im| + b * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * ((j : ℝ) + 1) + b * ((j : ℝ) + 1) := by gcongr
    _ = (j : ℝ) + 1 := by rw [← add_mul, hab, one_mul]

lemma isCompact_montelK (j : ℕ) : IsCompact (montelK j) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · unfold montelK
    refine (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2 * ((j : ℝ) + 1))).subset ?_
    intro w ⟨h1, h2, h3⟩
    rw [mem_closedBall_zero_iff]
    have := Complex.norm_le_abs_re_add_abs_im w
    have h4 : |w.re| ≤ (j : ℝ) + 1 := by
      rw [abs_of_nonneg (le_trans (by positivity) h1)]; exact h2
    linarith

lemma montelK_closedBall_subset (j : ℕ) {z : ℂ} (hz : z ∈ montelK j) :
    closedBall z (1 / (2 * ((j : ℝ) + 1))) ⊆ montelO j := by
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  obtain ⟨h1, h2, h3⟩ := hz
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hre : |w.re - z.re| ≤ 1 / (2 * ((j : ℝ) + 1)) := by
    have := Complex.abs_re_le_norm (w - z); simpa using this.trans hw
  have him : |w.im - z.im| ≤ 1 / (2 * ((j : ℝ) + 1)) := by
    have := Complex.abs_im_le_norm (w - z); simpa using this.trans hw
  have hδ1 : 1 / (2 * ((j : ℝ) + 1)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hδ2 : 1 / (2 * ((j : ℝ) + 1)) = 2 * (1 / (4 * ((j : ℝ) + 1))) := by field_simp; ring
  have hlow : 1 / ((j : ℝ) + 1) = 4 * (1 / (4 * ((j : ℝ) + 1))) := by field_simp
  have hpos : 0 < 1 / (4 * ((j : ℝ) + 1)) := by positivity
  rw [abs_le] at hre him
  refine ⟨by linarith, by linarith, ?_⟩
  rw [abs_lt]; constructor <;> linarith [abs_le.mp h3]

lemma exists_montelK_superset {K : Set ℂ} (hK : IsCompact K) (hKs : K ⊆ {w : ℂ | 0 < w.re}) :
    ∃ j : ℕ, K ⊆ montelK j := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, empty_subset _⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hr0 : 0 < z₀.re := hKs hz₀
  obtain ⟨j, hj⟩ := exists_nat_ge (max R (1 / z₀.re))
  refine ⟨j, fun w hw => ?_⟩
  have h1 : 1 / z₀.re ≤ (j : ℝ) := (le_max_right _ _).trans hj
  have h2 : R ≤ (j : ℝ) := (le_max_left _ _).trans hj
  have hw0 : 0 < w.re := hKs hw
  have hwR := hR w hw
  have hre : z₀.re ≤ w.re := hmin hw
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hr0] at h1
    nlinarith
  · have := Complex.re_le_norm w; linarith
  · have := Complex.abs_im_le_norm w; linarith

/-- **Montel's theorem on the right half-plane.** -/
theorem montel_rightHalfPlane (g : ℕ → ℂ → ℂ)
    (hd : ∀ j : ℕ, ∃ N, ∀ n ≥ N, DifferentiableOn ℂ (g n) (montelO j))
    (hb : ∀ j : ℕ, ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ w ∈ montelO j, ‖g n w‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (G : ℂ → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun k => g (φ k)) G atTop {w : ℂ | 0 < w.re} := by
  classical
  choose N1 hN1 using hd
  choose M N2 hMN using hb
  set N : ℕ → ℕ := fun j => max (N1 j) (N2 j) with hN
  have hNge : ∀ j n, N j ≤ max n (N j) := fun j n => le_max_right _ _
  have hgj : ∀ j n, DifferentiableOn ℂ (g (max n (N j))) (montelO j) := fun j n =>
    hN1 j _ ((le_max_left _ _).trans (hNge j n))
  have hbj : ∀ j n, ∀ z ∈ montelK j, ∀ w ∈ closedBall z (1 / (2 * ((j : ℝ) + 1))),
      ‖g (max n (N j)) w‖ ≤ M j := fun j n z hz w hw =>
    hMN j _ ((le_max_right _ _).trans (hNge j n)) w (montelK_closedBall_subset j hz hw)
  have hex := fun j : ℕ => montel_bcf (g := fun n => g (max n (N j))) (isOpen_montelO j) (hgj j)
    (isCompact_montelK j) (convex_montelK j) (δ := 1 / (2 * ((j : ℝ) + 1))) (by positivity)
    (fun z hz => montelK_closedBall_subset j hz) (hbj j)
  choose h hh hcomp using hex
  have hS : IsCompact (Set.pi univ (fun j : ℕ => closure (range (h j)))) := isCompact_univ_pi hcomp
  obtain ⟨a, -, ψ, hψ, hlim⟩ := hS.tendsto_subseq
    (x := fun n j => h j n) (fun n j _ => subset_closure ⟨n, rfl⟩)
  have hj : ∀ j, ∃ E : ℂ → ℂ, TendstoUniformlyOn (fun k => g (ψ k)) E atTop (montelK j) := by
    intro j
    have h1 := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp ((tendsto_pi_nhds.mp hlim) j)
    refine ⟨fun z => if hz : z ∈ montelK j then a j ⟨z, hz⟩ else 0, ?_⟩
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have hG : ((fun z => if hz : z ∈ montelK j then a j ⟨z, hz⟩ else 0) ∘ ((↑) : montelK j → ℂ)) = a j := by
      funext x; simp [x.2]
    rw [hG]
    intro u hu
    filter_upwards [h1 u hu, eventually_ge_atTop (N j)] with k hk hk2 x
    have hmax : max (ψ k) (N j) = ψ k := max_eq_left (hk2.trans (hψ.id_le k))
    have := hh j (ψ k) x
    simp only [hmax] at this
    have hk' : (a j x, h j (ψ k) x) ∈ u := hk x
    rw [this] at hk'
    exact hk'
  -- the global limit
  choose E hE using hj
  let G : ℂ → ℂ := fun w =>
    if hl : ∃ l, Tendsto (fun k => g (ψ k) w) atTop (𝓝 l) then hl.choose else 0
  have hGE : ∀ j, ∀ w ∈ montelK j, G w = E j w := by
    intro j w hw
    have ht := (hE j).tendsto_at hw
    have hl : ∃ l, Tendsto (fun k => g (ψ k) w) atTop (𝓝 l) := ⟨_, ht⟩
    simp only [G, dif_pos hl]
    exact tendsto_nhds_unique hl.choose_spec ht
  refine ⟨ψ, G, hψ, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_lt continuous_const Complex.continuous_re)]
  intro K hKs hKc
  obtain ⟨j, hj⟩ := exists_montelK_superset hKc hKs
  exact ((hE j).mono hj).congr_right (fun w hw => (hGE j w (hj hw)).symm)

/-- info: 'FormalResearch.SignUncertainty.montel_rightHalfPlane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms montel_rightHalfPlane

end FormalResearch.SignUncertainty
