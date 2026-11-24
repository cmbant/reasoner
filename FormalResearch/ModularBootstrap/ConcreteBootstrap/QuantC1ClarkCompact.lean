module

public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuantC1ClarkLimit

/-!
# Clark `TE.0'`: compactness in the first level and identification of the limit

For a sequence of admissible test functions (`QuantC1ClarkHyp`) with `c'_n → ∞` and Clark labels
`γ_n` in a compact set `K ⊂ ℝ`, a subsequence has `γ_n → γ_∞ ∈ K` and `Ψ_n → c · g_{α(γ_∞)}`
locally uniformly on `ℂ`, with `c > 0` and `g_α` the Clark extremal. The closing step is the Clark
two-node equality case (`clark_two_node_equality`), in place of `airy_sign_equality` at `α = 0`.

* `clark_compactness`: the combined statement.
* `clark_deriv_tendsto_comp`: `Ψ_{φ k}'(w_k) → Φ'(w_∞)` for `w_k → w_∞`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.ConcreteBootstrap

open FormalResearch.Special FormalResearch.SignUncertainty

/-- Locally uniform convergence of holomorphic functions gives convergence of derivatives along
convergent sequences. -/
lemma clark_deriv_tendsto_comp {F : ℕ → ℂ → ℂ} {Φ : ℂ → ℂ} {φ : ℕ → ℕ}
    (hU : ∀ m : ℕ, TendstoUniformlyOn (fun k => F (φ k)) Φ atTop (closedBall (0 : ℂ) ((m : ℝ) + 1)))
    (hAn : ∀ m : ℕ, ∀ᶠ k in atTop, AnalyticOnNhd ℂ (F (φ k)) (closedBall (0 : ℂ) ((m : ℝ) + 1)))
    (hΦ : Differentiable ℂ Φ) {w : ℕ → ℂ} {wlim : ℂ} (hw : Tendsto w atTop (𝓝 wlim)) :
    Tendsto (fun k => deriv (F (φ k)) (w k)) atTop (𝓝 (deriv Φ wlim)) := by
  set m : ℕ := ⌈‖wlim‖⌉₊ with hm
  have hmem_ball : wlim ∈ ball (0 : ℂ) ((m : ℝ) + 1) := by
    rw [mem_ball_zero_iff]; linarith [Nat.le_ceil ‖wlim‖]
  have hloc : TendstoLocallyUniformlyOn (fun k => F (φ k)) Φ atTop (ball (0 : ℂ) ((m : ℝ) + 1)) :=
    (hU m).tendstoLocallyUniformlyOn.mono ball_subset_closedBall
  have hdiffOn : ∀ᶠ k in atTop, DifferentiableOn ℂ (F (φ k)) (ball (0 : ℂ) ((m : ℝ) + 1)) :=
    (hAn m).mono fun k hk => hk.differentiableOn.mono ball_subset_closedBall
  have hder := hloc.deriv hdiffOn isOpen_ball
  have hcont : Continuous (deriv Φ) := (hΦ.contDiff (n := 1)).continuous_deriv le_rfl
  have hg : Tendsto w atTop (𝓝[ball (0 : ℂ) ((m : ℝ) + 1)] wlim) :=
    tendsto_nhdsWithin_iff.mpr ⟨hw, hw (isOpen_ball.mem_nhds hmem_ball)⟩
  exact hder.tendsto_comp hcont.continuousWithinAt hmem_ball hg

/-- **Compactness and identification** (Clark `TE.0'`, the sequence step). -/
theorem clark_compactness {C_0 : ℝ} (hC0 : 0 < C_0)
    (R_dom ς δ_lobe ρ : ℝ → ℝ)
    (hR_lim : Tendsto R_dom atTop atTop)
    (hς_nn : ∀ᶠ c in atTop, 0 ≤ ς c) (hς_lim : Tendsto ς atTop (𝓝 0))
    (hδ_nn : ∀ᶠ c in atTop, 0 ≤ δ_lobe c) (hδ_lim : Tendsto δ_lobe atTop (𝓝 0))
    (hρ_lim : Tendsto ρ atTop (𝓝 0))
    {Kc : Set ℝ} (hK : IsCompact Kc)
    {c'_seq : ℕ → ℝ} (hc'_atTop : Tendsto c'_seq atTop atTop)
    {γ_seq : ℕ → ℝ} (hγK : ∀ n, γ_seq n ∈ Kc)
    {Ψ_seq : ℕ → ℂ → ℂ} {uT_seq ũ_seq : ℕ → ℝ}
    (hspec : ∀ n, QuantC1ClarkHyp C_0 (R_dom (c'_seq n)) (ς (c'_seq n)) (δ_lobe (c'_seq n))
      (ρ (c'_seq n)) (γ_seq n) (Ψ_seq n) (uT_seq n) (ũ_seq n)) :
    ∃ (θ : ℕ → ℕ) (γlim : ℝ) (Φ : ℂ → ℂ) (α c : ℝ), StrictMono θ ∧ γlim ∈ Kc ∧
      Tendsto (fun k => γ_seq (θ k)) atTop (𝓝 γlim) ∧
      Real.sin α ≠ 0 ∧ (∀ n : ℕ, clarkNode α n = airyClarkNode γlim n) ∧ 0 < c ∧
      (∀ u : ℂ, Φ u = (c : ℂ) * clarkExtremal α u) ∧ Differentiable ℂ Φ ∧
      (∀ m : ℕ, TendstoUniformlyOn (fun k => Ψ_seq (θ k)) Φ atTop
        (closedBall (0 : ℂ) ((m : ℝ) + 1))) ∧
      (∀ m : ℕ, ∀ᶠ k in atTop,
        AnalyticOnNhd ℂ (Ψ_seq (θ k)) (closedBall (0 : ℂ) ((m : ℝ) + 1))) := by
  obtain ⟨γlim, hγlim_mem, ψ₀, hψ₀_mono, hψ₀_tend⟩ := hK.tendsto_subseq hγK
  have hc'_sub : Tendsto (fun n => c'_seq (ψ₀ n)) atTop atTop :=
    hc'_atTop.comp hψ₀_mono.tendsto_atTop
  obtain ⟨φ, Φ, hφ_mono, hunif, hdiff, hint, ⟨C, ν, hC, henv⟩, hreal, hint0, hnode, hpos, hne⟩ :=
    clark_limit_extraction hC0 R_dom ς δ_lobe ρ hR_lim hς_nn hς_lim hδ_nn hδ_lim hρ_lim
      (c'_seq := fun n => c'_seq (ψ₀ n)) hc'_sub (γ_seq := fun n => γ_seq (ψ₀ n))
      (γlim := γlim) hψ₀_tend (Ψ_seq := fun n => Ψ_seq (ψ₀ n))
      (uT_seq := fun n => uT_seq (ψ₀ n)) (ũ_seq := fun n => ũ_seq (ψ₀ n))
      (fun n => hspec (ψ₀ n))
  obtain ⟨α, hα, hnodes⟩ := exists_clarkAngle_node γlim
  have hnode' : 0 ≤ (Φ (clarkNode α 1 : ℂ)).re := by rw [hnodes]; exact hnode
  have hpos' : ∀ x : ℝ, x ≤ clarkNode α 2 → 0 ≤ (Φ (x : ℂ)).re := by
    intro x hx; rw [hnodes] at hx; exact hpos x hx
  obtain ⟨c, hc, hΦeq, -⟩ := clark_two_node_equality hα hdiff hint hC henv hreal hint0 hnode' hpos' hne
  refine ⟨fun k => ψ₀ (φ k), γlim, Φ, α, c, hψ₀_mono.comp hφ_mono, hγlim_mem,
    hψ₀_tend.comp hφ_mono.tendsto_atTop, hα, hnodes, hc, hΦeq, hdiff, hunif, fun m => ?_⟩
  have hR_eventually : ∀ᶠ k in atTop, ((m : ℝ) + 1) ≤ R_dom (c'_seq (ψ₀ (φ k))) :=
    (hR_lim.comp (hc'_sub.comp hφ_mono.tendsto_atTop)).eventually (eventually_ge_atTop _)
  filter_upwards [hR_eventually] with k hk
  exact (hspec (ψ₀ (φ k))).analytic.mono (closedBall_subset_closedBall hk)

end FormalResearch.ModularBootstrap.ConcreteBootstrap
