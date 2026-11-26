module

public import FormalResearch.SignUncertainty.CeCanonicalDefs

/-!
# Algebra of profile convergence (`ProfileConv`) for the endpoint clause of `thm:ce-shell-gap`

`ProfileConv Φ L` is local uniform convergence on `ℝ` together with `L¹` convergence. This file proves the
elementary closure properties used to assemble `ShellGapEndpoint`:

* `profileConv_of_subseq`: convergence of the whole sequence from convergence of a further subsequence of every
  subsequence (uniqueness of the limit upgrades subsequential limits).
* `ProfileConv.sub`, `ProfileConv.div_const`: differences and division by a convergent scalar sequence
  (integrability of the profiles is a hypothesis, so that the Bochner integrals are the true `L¹` distances).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace FormalResearch.SignUncertainty

/-- Local uniform convergence on `ℝ` of the whole sequence from that of a further subsequence of every
subsequence tending to infinity. -/
lemma tendstoLocallyUniformlyOn_of_subseq {Φ : ℕ → ℝ → ℝ} {L : ℝ → ℝ}
    (h : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ,
      TendstoLocallyUniformlyOn (fun n => Φ (ns (ms n))) L atTop univ) :
    TendstoLocallyUniformlyOn Φ L atTop univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  have hfreq : ∃ᶠ n in atTop, ¬ ∀ x ∈ K, dist (L x) (Φ n x) < ε := not_eventually.mp hcon
  obtain ⟨ns, hns, hbad⟩ := Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨ms, hms⟩ := h ns hns.tendsto_atTop
  have hK' : TendstoUniformlyOn (fun n => Φ (ns (ms n))) L atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).1 hms K (subset_univ _) hK
  have hev := Metric.tendstoUniformlyOn_iff.1 hK' ε hε
  obtain ⟨n, hn⟩ := hev.exists
  exact hbad (ms n) hn

/-- `ProfileConv` of the whole sequence from `ProfileConv` of a further subsequence of every subsequence. -/
lemma profileConv_of_subseq {Φ : ℕ → ℝ → ℝ} {L : ℝ → ℝ}
    (h : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ,
      ProfileConv (fun n => Φ (ns (ms n))) L) : ProfileConv Φ L := by
  refine ⟨tendstoLocallyUniformlyOn_of_subseq fun ns hns => ?_, ?_⟩
  · obtain ⟨ms, hms⟩ := h ns hns
    exact ⟨ms, hms.1⟩
  · refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨ms, hms⟩ := h ns hns
    exact ⟨ms, hms.2⟩

/-- Differences of convergent profile sequences. -/
lemma ProfileConv.sub {A B : ℕ → ℝ → ℝ} {LA LB : ℝ → ℝ} (hA : ProfileConv A LA)
    (hB : ProfileConv B LB) (hAi : ∀ k, Integrable (A k)) (hBi : ∀ k, Integrable (B k))
    (hLA : Integrable LA) (hLB : Integrable LB) :
    ProfileConv (fun k u => B k u - A k u) (fun u => LB u - LA u) := by
  refine ⟨hB.1.sub hA.1, ?_⟩
  refine squeeze_zero (fun k => integral_nonneg fun u => abs_nonneg _) (fun k => ?_)
    (by simpa using hB.2.add hA.2)
  have h1 : Integrable (fun u => |B k u - LB u|) := ((hBi k).sub hLB).abs
  have h2 : Integrable (fun u => |A k u - LA u|) := ((hAi k).sub hLA).abs
  have h3 : Integrable (fun u => |B k u - A k u - (LB u - LA u)|) :=
    (((hBi k).sub (hAi k)).sub (hLB.sub hLA)).abs
  dsimp only
  rw [← integral_add h1 h2]
  refine integral_mono h3 (h1.add h2) fun u => ?_
  have := abs_sub (B k u - LB u) (A k u - LA u)
  rwa [show B k u - LB u - (A k u - LA u) = (B k u - A k u) - (LB u - LA u) by ring] at this

/-- Division by a convergent scalar sequence with nonzero limit. -/
lemma ProfileConv.div_const {Φ : ℕ → ℝ → ℝ} {L : ℝ → ℝ} (h : ProfileConv Φ L)
    (hΦi : ∀ k, Integrable (Φ k)) (hLi : Integrable L) (hLc : Continuous L) {s : ℕ → ℝ} {s₀ : ℝ}
    (hs : Tendsto s atTop (𝓝 s₀)) (hs₀ : s₀ ≠ 0) :
    ProfileConv (fun k u => Φ k u / s k) (fun u => L u / s₀) := by
  have hsi : Tendsto (fun k => (s k)⁻¹) atTop (𝓝 s₀⁻¹) := hs.inv₀ hs₀
  refine ⟨?_, ?_⟩
  · have hc : TendstoLocallyUniformlyOn (fun k (_ : ℝ) => (s k)⁻¹) (fun _ => s₀⁻¹) atTop univ :=
      tendstoLocallyUniformlyOn_univ.2 hsi.tendstoUniformly_const.tendstoLocallyUniformly
    have := TendstoLocallyUniformlyOn.mul₀ h.1 hc hLc.continuousOn continuousOn_const
    simp_rw [div_eq_mul_inv]
    exact this
  · have hbound := ((hsi.abs).mul h.2).add
      ((hsi.sub_const s₀⁻¹).abs.mul (tendsto_const_nhds (x := ∫ u, |L u|)))
    simp only [mul_zero, sub_self, abs_zero, zero_mul, add_zero] at hbound
    refine squeeze_zero (fun k => integral_nonneg fun u => abs_nonneg _) (fun k => ?_) hbound
    have e : ∀ u, |Φ k u / s k - L u / s₀| ≤ |(s k)⁻¹| * |Φ k u - L u| + |L u| * |(s k)⁻¹ - s₀⁻¹| :=
      fun u => by
        have : Φ k u / s k - L u / s₀ = (Φ k u - L u) * (s k)⁻¹ + L u * ((s k)⁻¹ - s₀⁻¹) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring
        rw [this]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        linarith [mul_comm |Φ k u - L u| |(s k)⁻¹|]
    calc ∫ u, |Φ k u / s k - L u / s₀|
        ≤ ∫ u, (|(s k)⁻¹| * |Φ k u - L u| + |(s k)⁻¹ - s₀⁻¹| * |L u|) := by
          refine integral_mono (((hΦi k).div_const _).sub (hLi.div_const _)).abs
            ((((hΦi k).sub hLi).abs.const_mul _).add (hLi.abs.const_mul _)) fun u => ?_
          simpa [mul_comm] using e u
      _ = |(s k)⁻¹| * (∫ u, |Φ k u - L u|) + |(s k)⁻¹ - s₀⁻¹| * ∫ u, |L u| := by
          have i1 : Integrable (fun u => |(s k)⁻¹| * |Φ k u - L u|) :=
            ((hΦi k).sub hLi).abs.const_mul _
          have i2 : Integrable (fun u => |(s k)⁻¹ - s₀⁻¹| * |L u|) := hLi.abs.const_mul _
          rw [integral_add i1 i2, integral_const_mul, integral_const_mul]

lemma ProfileConv.congr {Φ Φ' : ℕ → ℝ → ℝ} {L L' : ℝ → ℝ} (h : ProfileConv Φ L)
    (hΦ : ∀ k u, Φ k u = Φ' k u) (hL : ∀ u, L u = L' u) : ProfileConv Φ' L' := by
  have e1 : Φ = Φ' := funext fun k => funext (hΦ k)
  have e2 : L = L' := funext hL
  subst e1; subst e2; exact h

end FormalResearch.SignUncertainty
