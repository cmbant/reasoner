module

public import FormalResearch.ModularBootstrap.TwoLevel.PinnedLimit

/-!
# Pinned first level: the equality case (`virasoro_two_level.tex`, Theorem 2.1)

For a `RigidityFamilyPackage` `F`, a pinned point `σ n → -u₁/β` with `Φ_n(σ n) ≥ 0`, and
`(t₁ - ξ̄ c')/c'^{1/3} → c_* |z₂(α(u₁))|` (equality in `twoLevel_liminf` along `p`):

* `l1_of_tendstoLocallyUniformlyOn`: locally uniform convergence to a profile of unit `L¹` norm
  gives `L¹` convergence of the blow-ups (the first two clauses of `theorem_R2`, for any limit);
* `twoLevel_rigidity`: `s₁ → -z₂/β`, `Φ_n → c · g_α(-β ·)` locally uniformly and in `L¹`, `γ → 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.Analysis

/-- **Two-level equality case** (`virasoro_two_level.tex`, Theorem 2.1): if the pinned family has
`(t₁ - ξ̄ c')/c'^{1/3} → c_* |z₂(α(u₁))|`, then `s₁ → -z₂/β`, `γ → 0` and
`Φ_n → c · g_α(-β ·)` locally uniformly and in `L¹`, with `c > 0` fixed by `‖c · g_α(-β ·)‖₁ = 1`. -/
theorem twoLevel_rigidity {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    (F : RigidityFamilyPackage ι p) {u₁ : ℝ} (hu₁ : airyZero 1 < u₁)
    {σ : ι → ℝ} (hσ : Tendsto σ p (nhds (-u₁ / betaTip)))
    (hpin : ∀ᶠ n in p, 0 ≤ (F.Φ n (σ n : ℂ)).re)
    (hEq : Tendsto (fun n => (F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ)) p
      (nhds (cStar * |clarkNode (clarkAngle u₁) 2|))) :
    ∃ c : ℝ, 0 < c ∧ (∫ s : ℝ, ‖clarkProfile (clarkAngle u₁) c (s : ℂ)‖ = 1) ∧
      Tendsto F.s₁ p (nhds (-clarkNode (clarkAngle u₁) 2 / betaTip)) ∧
      TendstoLocallyUniformlyOn F.Φ (clarkProfile (clarkAngle u₁) c) p univ ∧
      Tendsto F.γ p (nhds 0) ∧
      Tendsto (fun n => ∫ s : ℝ, ‖phiExt F n s - clarkProfile (clarkAngle u₁) c (s : ℂ)‖) p
        (nhds 0) ∧
      Tendsto (fun n => ∫ s in Ioi (-xiStar * (F.c' n) ^ (2 / 3 : ℝ)),
        ‖F.Φ n (s : ℂ) - clarkProfile (clarkAngle u₁) c (s : ℂ)‖) p (nhds 0) := by
  have hα : Real.sin (clarkAngle u₁) ≠ 0 := sin_clarkAngle_ne_zero hu₁
  have hz := clarkNode_two_neg hu₁
  have hs₁ : Tendsto F.s₁ p (nhds (-clarkNode (clarkAngle u₁) 2 / betaTip)) := by
    have h := tendsto_s₁_of_tendsto_excess F.toBlowupFamilyPackage hEq
    rwa [cStar_mul_abs_of_neg hz, mul_div_cancel_left₀ _ two_thirds_xiStar_pos.ne'] at h
  -- every subsequence has a further subsequence converging to a profile
  have K : ∀ ns : ℕ → ι, Tendsto ns atTop p → ∃ (ms : ℕ → ℕ) (c : ℝ), StrictMono ms ∧ 0 < c ∧
      (∫ s : ℝ, ‖clarkProfile (clarkAngle u₁) c (s : ℂ)‖ = 1) ∧
      TendstoLocallyUniformlyOn (fun k => F.Φ (ns (ms k))) (clarkProfile (clarkAngle u₁) c) atTop univ ∧
      Tendsto (fun k => F.γ (ns (ms k))) atTop (nhds 0) := by
    intro ns hns
    have hmem : ∀ᶠ k in atTop, F.s₁ (ns k) ≤ -clarkNode (clarkAngle u₁) 2 / betaTip + 1 ∧
        0 ≤ (F.Φ (ns k) (σ (ns k) : ℂ)).re :=
      (hns.eventually (hs₁.eventually (eventually_le_nhds (by linarith)))).and (hns.eventually hpin)
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hmem
    obtain ⟨ms, s₁Star, Ψ, γLim, hms, hs₁Star, hΦ, hγ, -, hΨi, -, heq⟩ :=
      pinned_limit F.toBlowupFamilyPackage hu₁ hσ (fun k => ns (k + k₀)) (hns.comp (tendsto_add_atTop_nat k₀))
        (fun k => (hk₀ (k + k₀) (Nat.le_add_left k₀ k)).2)
        ⟨-clarkNode (clarkAngle u₁) 2 / betaTip + 1, fun k => (hk₀ (k + k₀) (Nat.le_add_left k₀ k)).1⟩
    have hs₁_eq : s₁Star = -clarkNode (clarkAngle u₁) 2 / betaTip :=
      tendsto_nhds_unique hs₁Star
        (hs₁.comp ((hns.comp (tendsto_add_atTop_nat k₀)).comp hms.tendsto_atTop))
    obtain ⟨c, hc, hΨc, hγ0, hnorm⟩ := heq (by
      rw [hs₁_eq]; field_simp [betaTip_pos.ne'])
    have hΨeq : Ψ = clarkProfile (clarkAngle u₁) c := funext hΨc
    subst hΨeq
    refine ⟨fun k => ms k + k₀, c, fun a b hab => Nat.add_lt_add_right (hms hab) k₀, hc, hnorm,
      hΦ, ?_⟩
    rw [hγ0] at hγ
    exact hγ
  obtain ⟨x, hx⟩ := Filter.exists_seq_tendsto p
  obtain ⟨-, c₀, -, hc₀, hn₀, -⟩ := K x hx
  have hunique : ∀ c : ℝ, 0 < c → (∫ s : ℝ, ‖clarkProfile (clarkAngle u₁) c (s : ℂ)‖ = 1) → c = c₀ := by
    intro c hc hn
    rw [clarkProfile_norm_integral (clarkAngle u₁) hc.le] at hn
    rw [clarkProfile_norm_integral (clarkAngle u₁) hc₀.le] at hn₀
    have hN : clarkProfileNorm (clarkAngle u₁) ≠ 0 := by
      intro h; rw [h, mul_zero] at hn₀; exact zero_ne_one hn₀
    exact mul_right_cancel₀ hN (hn.trans hn₀.symm)
  have hΦlim : TendstoLocallyUniformlyOn F.Φ (clarkProfile (clarkAngle u₁) c₀) p univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro Kc _ hKc; rw [Metric.tendstoUniformlyOn_iff]; intro ε hε
    by_contra hnot
    have hfreq : ∃ᶠ n in p, ∃ z ∈ Kc, ε ≤ dist (clarkProfile (clarkAngle u₁) c₀ z) (F.Φ n z) := by
      rw [Filter.not_eventually] at hnot
      refine hnot.mono fun n hn => ?_
      push Not at hn; exact hn
    obtain ⟨ns, hns, hbad⟩ := exists_seq_forall_of_frequently hfreq
    obtain ⟨ms, c, -, hc, hcn, hΦms, -⟩ := K ns hns
    have hcc : c = c₀ := hunique c hc hcn
    subst hcc
    have hev := Metric.tendstoUniformlyOn_iff.mp
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΦms Kc (subset_univ Kc) hKc) ε hε
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hev
    obtain ⟨z, hzK, hzbad⟩ := hbad (ms k₀)
    linarith [hk₀ k₀ le_rfl z hzK]
  have hγlim : Tendsto F.γ p (nhds 0) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨ms, c, -, -, -, -, hγ⟩ := K ns hns
    exact ⟨ms, hγ⟩
  have hL1 := l1_of_tendstoLocallyUniformlyOn F (clarkProfile_integrable hα c₀) hn₀ hΦlim
  exact ⟨c₀, hc₀, hn₀, hs₁, hΦlim, hγlim, hL1.1, hL1.2⟩

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoLevel_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoLevel_rigidity

end FormalResearch.ModularBootstrap.TwoLevel
