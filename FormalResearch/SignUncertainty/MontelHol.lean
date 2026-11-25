module

public import FormalResearch.Complex.Montel

/-!
# Montel's theorem on the right half-plane, eventual form

A sequence of functions that are eventually holomorphic and eventually locally uniformly bounded on each open
rectangle `montelO j` exhausting `{Re w > 0}` has a subsequence converging locally uniformly there
(`montel_rightHalfPlane`).  It is a corollary of `FormalResearch.Montel` (`isCompact_closure_range`): the closures of
the ranges on the `montelO j` are compact in `C(montelO j, ℂ)`, their product over `j` is compact and metrizable, and a
convergent subsequence is extracted at once (no diagonal argument).
-/

@[expose] public section

open Complex Set Filter Topology Metric

namespace FormalResearch.SignUncertainty

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

lemma montelK_subset_montelO (j : ℕ) : montelK j ⊆ montelO j := fun z hz =>
  montelK_closedBall_subset j hz (mem_closedBall_self (by positivity))

/-- **Montel's theorem on the right half-plane** (eventual form). -/
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
  have hbj : ∀ j, FormalResearch.Montel.LocallyBounded (fun n => g (max n (N j))) (montelO j) :=
    fun j K hK _ => ⟨M j, fun n z hz =>
      hMN j _ ((le_max_right _ _).trans (hNge j n)) z (hK hz)⟩
  have hcomp := fun j : ℕ => FormalResearch.Montel.isCompact_closure_range (isOpen_montelO j)
    (F := fun n => g (max n (N j))) (hgj j) (hbj j)
  have : ∀ j : ℕ, LocallyCompactSpace (montelO j) := fun j => (isOpen_montelO j).locallyCompactSpace
  have hS : IsCompact (Set.pi univ fun j : ℕ =>
      closure (Set.range (FormalResearch.Montel.toCont (F := fun n => g (max n (N j))) (hgj j)))) :=
    isCompact_univ_pi hcomp
  obtain ⟨a, -, ψ, hψ, hlim⟩ := hS.tendsto_subseq
    (x := fun n j => FormalResearch.Montel.toCont (F := fun n => g (max n (N j))) (hgj j) n)
    (fun n j _ => subset_closure ⟨n, rfl⟩)
  have hj : ∀ j, ∃ E : ℂ → ℂ,
      TendstoLocallyUniformlyOn (fun k => g (ψ k)) E atTop (montelO j) := by
    intro j
    have hl := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ((tendsto_pi_nhds.mp hlim) j)
    refine ⟨fun z => if h : z ∈ montelO j then a j ⟨z, h⟩ else 0, ?_⟩
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have h2 : ((fun z => if h : z ∈ montelO j then a j ⟨z, h⟩ else 0) ∘ Subtype.val) = ⇑(a j) := by
      funext x; simp
    rw [h2]
    refine hl.congr_inseparable ?_
    filter_upwards [eventually_ge_atTop (N j)] with k hk x
    have hmax : max (ψ k) (N j) = ψ k := max_eq_left (hk.trans (hψ.id_le k))
    refine .of_eq ?_
    simp [FormalResearch.Montel.toCont, hmax]
  choose E hE using hj
  let G : ℂ → ℂ := fun w =>
    if hl : ∃ l, Tendsto (fun k => g (ψ k) w) atTop (𝓝 l) then hl.choose else 0
  have hGE : ∀ j, ∀ w ∈ montelO j, G w = E j w := by
    intro j w hw
    have ht := (hE j).tendsto_at hw
    have hl : ∃ l, Tendsto (fun k => g (ψ k) w) atTop (𝓝 l) := ⟨_, ht⟩
    simp only [G, dite_eq_left hl]
    exact tendsto_nhds_unique hl.choose_spec ht
  refine ⟨ψ, G, hψ, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_lt continuous_const Complex.continuous_re)]
  intro K hKs hKc
  obtain ⟨j, hj⟩ := exists_montelK_superset hKc hKs
  have hjO : K ⊆ montelO j := hj.trans (montelK_subset_montelO j)
  have hu := ((tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_montelO j)).mp (hE j)) K hjO hKc
  exact hu.congr_right (fun w hw => (hGE j w (hjO hw)).symm)

/-- info: 'FormalResearch.SignUncertainty.montel_rightHalfPlane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms montel_rightHalfPlane

end FormalResearch.SignUncertainty
