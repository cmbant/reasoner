module

public import FormalResearch.SignUncertainty.ShellGapHankel
public import FormalResearch.SignUncertainty.RadialCompactnessProof
public import FormalResearch.SignUncertainty.DeepLobeMass

/-!
# `thm:ce-shell-gap`, step (a): the mass ratios `M[p]/M[q]` are bounded

For eigenfunctions `p ∈ 𝒜_c^{+1}` and integrable `q` with `|p| ≤ q` on `Δ ≥ T`, where the threshold
satisfies `T ≤ c/π² - (u₀/β₁) c^{1/3} + o(c^{1/3})` and `c → ∞`, the ratio `M[p]/M[q]` is bounded
(`mass_ratio_bdd`). Proof: otherwise the mass-normalised window profiles of `p` converge
(`RadialCompactness.normalized_compactness`) to an entire function `F` that vanishes on a real interval
(the part of the window beyond `u₀ - 1` carries mass `≤ M[q]/M[p] → 0`) yet keeps at least half of the
mass in a bounded window (`deep_lobe_mass_thm`), which is impossible for an entire function.

The Hankel-profile consequences (`h(0) = M[ĥ]`, `∫ f = 0`, `q ≠ 0`) are in the later sections.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace FormalResearch.SignUncertainty

/-! ### An entire function vanishing on a real interval -/

lemma entire_eq_zero_of_zero_on_Icc {F : ℂ → ℂ} (hF : Differentiable ℂ F) {a b : ℝ} (hab : a < b)
    (h0 : ∀ u ∈ Icc a b, F (u : ℂ) = 0) : ∀ z, F z = 0 := by
  have han : AnalyticOnNhd ℂ F univ := fun z _ => hF.analyticAt z
  set m : ℝ := (a + b) / 2 with hm
  have hmi : m ∈ Ioo a b := ⟨by rw [hm]; linarith, by rw [hm]; linarith⟩
  have hfreq : ∃ᶠ z in 𝓝[≠] ((m : ℝ) : ℂ), F z = 0 := by
    have h1 : ∃ᶠ s in 𝓝[≠] m, s ∈ Icc a b := by
      have hev : ∀ᶠ s in 𝓝[≠] m, s ∈ Icc a b :=
        mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hmi.1 hmi.2)
      exact hev.frequently
    have htend : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] m) (𝓝[≠] ((m : ℝ) : ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun s hs => by
          simp only [mem_compl_iff, mem_singleton_iff] at hs ⊢
          exact fun h => hs (Complex.ofReal_injective h))
    exact htend.frequently (h1.mono fun s hs => h0 s hs)
  intro z
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ _) hfreq
    (mem_univ z)

/-! ### Window integrals -/

lemma hankelWindowProfile_nonneg_abs {c : ℝ} (hc : 0 < c) (q : ℝ → ℝ) (u : ℝ) :
    0 ≤ hankelWindowProfile c (fun Δ => |q Δ|) u := by
  unfold hankelWindowProfile
  dsimp only
  split_ifs with h
  · exact mul_nonneg (div_nonneg (Real.rpow_nonneg hc.le _) hankelBeta1_pos.le)
      (mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc h.le))
  · exact le_rfl

/-- The part of the window profile of `p` beyond `u₁` (that is, `Δ ≥ T`) has mass at most `M[q]`
when `|p| ≤ q` on `[T, ∞)`. -/
lemma window_lower_tail_le {c : ℝ} (hc : 0 < c) {T u₁ : ℝ}
    (hT : T ≤ c / π ^ 2 - u₁ / hankelBeta1 * c ^ (1 / 3 : ℝ)) {p q : ℝ → ℝ}
    (hq : IntegrableOn (fun Δ => q Δ * hankelRho0 c Δ) (Ioi 0))
    (hdom : ∀ Δ, T ≤ Δ → |p Δ| ≤ q Δ) :
    ∫ u in Iic u₁, |hankelWindowProfile c p u| ≤ hankelMass c q := by
  set g : ℝ → ℝ := hankelWindowProfile c (fun Δ => |q Δ|) with hg
  have hg_int : Integrable g :=
    (integrable_hankelWindowProfile_iff hc _).mpr (abs_mul_rho0_integrableOn hc hq)
  have hg_nn : ∀ u, 0 ≤ g u := fun u => hankelWindowProfile_nonneg_abs hc q u
  have hgint : ∫ u, g u = hankelMass c q := integral_hankelWindowProfile hc (fun Δ => |q Δ|)
  have hpt : ∀ u ∈ Iic u₁, |hankelWindowProfile c p u| ≤ g u := by
    intro u hu
    have hΔ : T ≤ c / π ^ 2 - u / hankelBeta1 * c ^ (1 / 3 : ℝ) := by
      refine le_trans hT ?_
      have h1 : u / hankelBeta1 ≤ u₁ / hankelBeta1 :=
        div_le_div_of_nonneg_right hu hankelBeta1_pos.le
      have := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hc.le (1 / 3 : ℝ))
      linarith
    simp only [hg]
    unfold hankelWindowProfile
    dsimp only
    split_ifs with h
    · have ha : 0 ≤ c ^ (1 / 3 : ℝ) / hankelBeta1 :=
        div_nonneg (Real.rpow_nonneg hc.le _) hankelBeta1_pos.le
      have hρ := hankelRho0_nonneg hc h.le
      rw [abs_mul, abs_of_nonneg ha, abs_mul, abs_of_nonneg hρ]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hρ) ha
      exact (hdom _ hΔ).trans (le_abs_self _)
    · simp
  calc ∫ u in Iic u₁, |hankelWindowProfile c p u|
      ≤ ∫ u in Iic u₁, g u := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun u => abs_nonneg _)
          hg_int.integrableOn ?_
        exact (ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall hpt)
    _ ≤ ∫ u, g u := setIntegral_le_integral hg_int (Eventually.of_forall hg_nn)
    _ = hankelMass c q := hgint

/-! ### Boundedness of `M[p]/M[q]` -/

private lemma setIntegral_Icc_tendsto_of_tendstoUniformlyOn
    {g : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hunif : TendstoUniformlyOn g G atTop (Icc a b))
    (hg_int : ∀ᶠ k in atTop, IntegrableOn (g k) (Icc a b))
    (hG_int : IntegrableOn G (Icc a b)) :
    Tendsto (fun k => ∫ u in Icc a b, g k u) atTop (𝓝 (∫ u in Icc a b, G u)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / (b - a + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hunif' := Metric.tendstoUniformlyOn_iff.mp hunif δ hδ
  filter_upwards [hg_int, hunif'] with k hki hku
  rw [Real.dist_eq, ← integral_sub hki hG_int]
  have h1 : |∫ u in Icc a b, (g k u - G u)| ≤ ∫ u in Icc a b, |g k u - G u| :=
    by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun u => g k u - G u)
  have h2 : ∫ u in Icc a b, |g k u - G u| ≤ ∫ _u in Icc a b, δ := by
    refine setIntegral_mono_on (hki.sub hG_int).abs continuousOn_const.integrableOn_Icc
      measurableSet_Icc fun u hu => ?_
    simpa [Real.dist_eq, abs_sub_comm] using (hku u hu).le
  have h3 : ∫ _u in Icc a b, δ = (b - a) * δ := by
    rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]
  have h4 : (b - a) * δ < ε := by
    dsimp [δ]; rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  linarith


lemma bdd_of_eventually {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 < b k) {C : ℝ}
    (h : ∀ᶠ k in atTop, a k ≤ C * b k) : ∃ C' : ℝ, ∀ k, a k ≤ C' * b k := by
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 h
  refine ⟨max C (∑ k ∈ Finset.range k0, a k / b k), fun k => ?_⟩
  by_cases hk : k0 ≤ k
  · exact (hk0 k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hb k).le)
  · have hk' : k ∈ Finset.range k0 := Finset.mem_range.2 (not_le.1 hk)
    have h1 : a k / b k ≤ ∑ j ∈ Finset.range k0, a j / b j :=
      Finset.single_le_sum (f := fun j => a j / b j) (fun j _ => div_nonneg (ha j) (hb j).le) hk'
    calc a k = a k / b k * b k := by field_simp [(hb k).ne']
      _ ≤ max C (∑ j ∈ Finset.range k0, a j / b j) * b k :=
        mul_le_mul_of_nonneg_right (h1.trans (le_max_right _ _)) (hb k).le

theorem mass_ratio_bdd (H : RadialCompactness) {c : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    (hcpos : ∀ k, 0 < c k) {p q : ℕ → ℝ → ℝ} (hp : ∀ k, IsHankelEigenfn (c k) 1 (p k))
    (hq : ∀ k, IntegrableOn (fun Δ => q k Δ * hankelRho0 (c k) Δ) (Ioi 0))
    (hqpos : ∀ k, 0 < hankelMass (c k) (q k)) {u₀ : ℝ} {T ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hT : ∀ k, T k ≤ c k / π ^ 2 - (u₀ / hankelBeta1) * c k ^ (1 / 3 : ℝ) + ε k * c k ^ (1 / 3 : ℝ))
    (hdom : ∀ k Δ, T k ≤ Δ → |p k Δ| ≤ q k Δ) :
    ∃ C : ℝ, ∀ k, hankelMass (c k) (p k) ≤ C * hankelMass (c k) (q k) := by
  suffices hev : ∃ C : ℝ, ∀ᶠ k in atTop, hankelMass (c k) (p k) ≤ C * hankelMass (c k) (q k) by
    obtain ⟨C, hC⟩ := hev
    exact bdd_of_eventually (fun k => hankelMass_nonneg (hcpos k) _) hqpos hC
  by_contra hne
  push Not at hne
  have hfreq : ∀ n : ℕ, ∃ᶠ k in atTop,
      ((n : ℝ) + 1) * hankelMass (c k) (q k) < hankelMass (c k) (p k) := fun n =>
    hne ((n : ℝ) + 1)
  obtain ⟨ns, hns, hnsP⟩ := Filter.extraction_forall_of_frequently hfreq
  obtain ⟨ms, F, C, ν, hms, hloc, -, -, hFd, hFi, hC, hFb, hFreal⟩ :=
    H.normalized_compactness 1 (Or.inl rfl) (fun k => c (ns k)) (fun k => p (ns k))
      (hc.comp hns.tendsto_atTop) (fun k => hp (ns k))
  set K : ℕ → ℕ := fun k => ns (ms k) with hK
  have hKt : Tendsto K atTop atTop := hns.tendsto_atTop.comp hms.tendsto_atTop
  have hMp : ∀ k, 0 < hankelMass (c (K k)) (p (K k)) := fun k => by
    have h := hnsP (ms k)
    have h0 := hankelMass_nonneg (hcpos (ns (ms k))) (q (ns (ms k)))
    have : (0 : ℝ) ≤ ((ms k : ℝ) + 1) * hankelMass (c (ns (ms k))) (q (ns (ms k))) := by positivity
    exact lt_of_le_of_lt this h
  have hratio : ∀ k, hankelMass (c (K k)) (q (K k)) / hankelMass (c (K k)) (p (K k)) ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have h := hnsP (ms k)
    have hk : (k : ℝ) ≤ ms k := by exact_mod_cast hms.id_le k
    rw [div_le_div_iff₀ (hMp k) (by positivity)]
    have hq0 := (hqpos (K k)).le
    have : ((k : ℝ) + 1) * hankelMass (c (K k)) (q (K k)) ≤
        ((ms k : ℝ) + 1) * hankelMass (c (K k)) (q (K k)) :=
      mul_le_mul_of_nonneg_right (by linarith) hq0
    linarith [h]
    -- window parameters
  set u₁ : ℝ := u₀ - 1 with hu₁
  have hβ := hankelBeta1_pos
  obtain ⟨R₀, hR₀1, hR₀b, hR₀e⟩ : ∃ R₀ : ℝ, 13 ≤ R₀ ∧ u₁ < R₀ * hankelBeta1 ∧
      8 * Real.exp (-5 * R₀ ^ (3 / 2 : ℝ)) ≤ 1 / 8 := by
    refine ⟨max 13 (u₁ / hankelBeta1 + 1), le_max_left _ _, ?_, ?_⟩
    · have h1 : u₁ / hankelBeta1 + 1 ≤ max 13 (u₁ / hankelBeta1 + 1) := le_max_right _ _
      have h2 := mul_le_mul_of_nonneg_right h1 hβ.le
      have h3 : (u₁ / hankelBeta1 + 1) * hankelBeta1 = u₁ + hankelBeta1 := by field_simp
      linarith
    · have h13 : (13 : ℝ) ≤ max 13 (u₁ / hankelBeta1 + 1) := le_max_left _ _
      have h1 : max 13 (u₁ / hankelBeta1 + 1) ≤ max 13 (u₁ / hankelBeta1 + 1) ^ (3 / 2 : ℝ) := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ max 13 (u₁ / hankelBeta1 + 1))
          (by norm_num : (1 : ℝ) ≤ 3 / 2)
      have h2 := Real.add_one_le_exp (5 * max 13 (u₁ / hankelBeta1 + 1) ^ (3 / 2 : ℝ))
      rw [neg_mul, Real.exp_neg]
      have h66 : (66 : ℝ) ≤ Real.exp (5 * max 13 (u₁ / hankelBeta1 + 1) ^ (3 / 2 : ℝ)) := by linarith
      have h3 : (Real.exp (5 * max 13 (u₁ / hankelBeta1 + 1) ^ (3 / 2 : ℝ)))⁻¹ ≤ (66 : ℝ)⁻¹ :=
        inv_anti₀ (by norm_num) h66
      linarith [show (8 : ℝ) * (66 : ℝ)⁻¹ ≤ 1 / 8 by norm_num]
  have hev1 : ∀ᶠ k in atTop, 1625 ≤ c (K k) := (hc.comp hKt).eventually (eventually_ge_atTop 1625)
  have hev3 : ∀ᶠ k in atTop, ε (K k) * hankelBeta1 ≤ 1 := by
    have := ((hε.comp hKt).mul_const hankelBeta1)
    simpa using this.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) * hankelBeta1 < 1))
  have hev4 : ∀ᶠ k : ℕ in atTop, 3 ≤ k := eventually_ge_atTop 3
  -- pointwise-in-k bounds
  have key : ∀ k, 1625 ≤ c (K k) → ε (K k) * hankelBeta1 ≤ 1 → 3 ≤ k →
      (∫ u in Icc (u₁ - 1) u₁, |hankelWindowProfile (c (K k)) (p (K k)) u / hankelMass (c (K k)) (p (K k))|)
          ≤ 1 / ((k : ℝ) + 1) ∧
      1 / 2 ≤ ∫ u in Icc u₁ (R₀ * hankelBeta1),
          |hankelWindowProfile (c (K k)) (p (K k)) u / hankelMass (c (K k)) (p (K k))| := by
    intro k h1 h3 h4
    have hc0 := hcpos (K k)
    have hMk := hMp k
    have hr := hratio k
    have hk4 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / 4 := by
      have : (4 : ℝ) ≤ (k : ℝ) + 1 := by
        have : (3 : ℝ) ≤ k := by exact_mod_cast h4
        linarith
      exact one_div_le_one_div_of_le (by norm_num) this
    have hMq : hankelMass (c (K k)) (q (K k)) ≤ hankelMass (c (K k)) (p (K k)) / 4 := by
      rw [div_le_iff₀ hMk] at hr
      have := (hr.trans (by
        calc 1 / ((k : ℝ) + 1) * hankelMass (c (K k)) (p (K k))
            ≤ 1 / 4 * hankelMass (c (K k)) (p (K k)) :=
              mul_le_mul_of_nonneg_right hk4 hMk.le
          _ = hankelMass (c (K k)) (p (K k)) / 4 := by ring))
      exact this
    set b : ℝ := R₀ * hankelBeta1 with hb
    have hψint : Integrable (fun u => |hankelWindowProfile (c (K k)) (p (K k)) u|) :=
      ((integrable_hankelWindowProfile_iff hc0 _).mpr (hp (K k)).int).abs
    have htot : ∫ u, |hankelWindowProfile (c (K k)) (p (K k)) u| = hankelMass (c (K k)) (p (K k)) :=
      integral_abs_hankelWindowProfile hc0 _
    have hT' : T (K k) ≤ c (K k) / π ^ 2 - u₁ / hankelBeta1 * c (K k) ^ (1 / 3 : ℝ) := by
      have hh := hT (K k)
      have hε' : ε (K k) ≤ 1 / hankelBeta1 := by rw [le_div_iff₀ hβ]; exact h3
      have h13 : 0 ≤ c (K k) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
      have e : (u₀ / hankelBeta1) * c (K k) ^ (1 / 3 : ℝ) =
          (u₁ / hankelBeta1) * c (K k) ^ (1 / 3 : ℝ) + (1 / hankelBeta1) * c (K k) ^ (1 / 3 : ℝ) := by
        rw [hu₁]; ring
      have := mul_le_mul_of_nonneg_right hε' h13
      linarith
    have hA := window_lower_tail_le hc0 hT' (hq (K k)) (hdom (K k))
    have hB : ∫ u in Ioi b, |hankelWindowProfile (c (K k)) (p (K k)) u| ≤
        hankelMass (c (K k)) (p (K k)) / 4 := by
      rw [hb, integral_tail_abs_hankelWindowProfile hc0 (p (K k)) R₀]
      refine (deep_lobe_mass_thm (by linarith) (hp (K k)) (Or.inl rfl) (by linarith)).trans ?_
      have h66 : (66 : ℝ) ≤ Real.exp (1 / 25 * c (K k)) := by
        linarith [Real.add_one_le_exp (1 / 25 * c (K k))]
      have h3' : 8 * Real.exp (-(1 / 25) * c (K k)) ≤ 1 / 8 := by
        rw [neg_mul, Real.exp_neg]
        have : (Real.exp (1 / 25 * c (K k)))⁻¹ ≤ (66 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h66
        linarith [show (8 : ℝ) * (66 : ℝ)⁻¹ ≤ 1 / 8 by norm_num]
      have hM := hMk.le
      calc 8 * hankelMass (c (K k)) (p (K k)) *
            (Real.exp (-5 * R₀ ^ (3 / 2 : ℝ)) + Real.exp (-(1 / 25) * c (K k)))
          = hankelMass (c (K k)) (p (K k)) *
            (8 * Real.exp (-5 * R₀ ^ (3 / 2 : ℝ)) + 8 * Real.exp (-(1 / 25) * c (K k))) := by ring
        _ ≤ hankelMass (c (K k)) (p (K k)) * (1 / 8 + 1 / 8) :=
            mul_le_mul_of_nonneg_left (add_le_add hR₀e h3') hM
        _ = hankelMass (c (K k)) (p (K k)) / 4 := by ring
    have hsplit : ∫ u, |hankelWindowProfile (c (K k)) (p (K k)) u| =
        (∫ u in Iic u₁, |hankelWindowProfile (c (K k)) (p (K k)) u|) +
          ((∫ u in Ioc u₁ b, |hankelWindowProfile (c (K k)) (p (K k)) u|) +
            ∫ u in Ioi b, |hankelWindowProfile (c (K k)) (p (K k)) u|) := by
      rw [← integral_add_compl measurableSet_Iic hψint, compl_Iic]
      congr 1
      rw [← Set.Ioc_union_Ioi_eq_Ioi hR₀b.le,
        setIntegral_union (by
          rw [Set.disjoint_left]
          intro x hx hx'
          exact absurd hx.2 (not_le.2 hx')) measurableSet_Ioi hψint.integrableOn hψint.integrableOn]
    have hmid : hankelMass (c (K k)) (p (K k)) / 2 ≤
        ∫ u in Ioc u₁ b, |hankelWindowProfile (c (K k)) (p (K k)) u| := by
      linarith
    have hnorm : ∀ u, |hankelWindowProfile (c (K k)) (p (K k)) u / hankelMass (c (K k)) (p (K k))| =
        |hankelWindowProfile (c (K k)) (p (K k)) u| / hankelMass (c (K k)) (p (K k)) := fun u => by
      rw [abs_div, abs_of_pos hMk]
    simp only [hnorm]
    rw [integral_div, integral_div]
    constructor
    · calc (∫ u in Icc (u₁ - 1) u₁, |hankelWindowProfile (c (K k)) (p (K k)) u|) /
            hankelMass (c (K k)) (p (K k))
          ≤ (∫ u in Iic u₁, |hankelWindowProfile (c (K k)) (p (K k)) u|) /
              hankelMass (c (K k)) (p (K k)) := by
            refine div_le_div_of_nonneg_right ?_ hMk.le
            refine setIntegral_mono_set hψint.integrableOn
              (Eventually.of_forall fun u => abs_nonneg _) ?_
            exact (Icc_subset_Iic_self).eventuallyLE
        _ ≤ hankelMass (c (K k)) (q (K k)) / hankelMass (c (K k)) (p (K k)) :=
            div_le_div_of_nonneg_right hA hMk.le
        _ ≤ 1 / ((k : ℝ) + 1) := hr
    · rw [le_div_iff₀ hMk]
      have : ∫ u in Ioc u₁ b, |hankelWindowProfile (c (K k)) (p (K k)) u| ≤
          ∫ u in Icc u₁ b, |hankelWindowProfile (c (K k)) (p (K k)) u| :=
        setIntegral_mono_set hψint.integrableOn (Eventually.of_forall fun u => abs_nonneg _)
          Ioc_subset_Icc_self.eventuallyLE
      linarith
  have hc_cont : Continuous (fun u : ℝ => (F (u : ℂ)).re) :=
    Complex.continuous_re.comp (hFd.continuous.comp Complex.continuous_ofReal)
  have hloc' : ∀ α β : ℝ, TendstoUniformlyOn (fun k u => hankelWindowProfile (c (K k)) (p (K k)) u /
      hankelMass (c (K k)) (p (K k))) (fun u => (F (u : ℂ)).re) atTop (Icc α β) := fun α β =>
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).1 hloc _ (subset_univ _)
      isCompact_Icc
  have hunifabs : ∀ α β : ℝ, TendstoUniformlyOn (fun k u => |hankelWindowProfile (c (K k)) (p (K k)) u /
      hankelMass (c (K k)) (p (K k))|) (fun u => |(F (u : ℂ)).re|) atTop (Icc α β) := by
    intro α β
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hloc' α β) δ hδ] with k hk x hx
    refine lt_of_le_of_lt ?_ (hk x hx)
    rw [Real.dist_eq, Real.dist_eq]
    exact abs_abs_sub_abs_le_abs_sub _ _
  have hlim : ∀ α β : ℝ, α ≤ β → Tendsto (fun k => ∫ u in Icc α β,
      |hankelWindowProfile (c (K k)) (p (K k)) u / hankelMass (c (K k)) (p (K k))|) atTop
      (𝓝 (∫ u in Icc α β, |(F (u : ℂ)).re|)) := by
    intro α β hαβ
    refine setIntegral_Icc_tendsto_of_tendstoUniformlyOn hαβ (hunifabs α β) ?_
      hc_cont.abs.continuousOn.integrableOn_Icc
    exact Eventually.of_forall fun k =>
      (((integrable_hankelWindowProfile_iff (hcpos (K k)) _).mpr (hp (K k)).int).div_const _).abs.integrableOn
  have hsmall : ∫ u in Icc (u₁ - 1) u₁, |(F (u : ℂ)).re| = 0 := by
    refine le_antisymm ?_ (setIntegral_nonneg measurableSet_Icc fun u _ => abs_nonneg _)
    refine le_of_tendsto_of_tendsto (hlim (u₁ - 1) u₁ (by linarith))
      tendsto_one_div_add_atTop_nhds_zero_nat ?_
    filter_upwards [hev1, hev3, hev4] with k h1 h3 h4 using (key k h1 h3 h4).1
  have hF0 : ∀ z, F z = 0 := by
    refine entire_eq_zero_of_zero_on_Icc hFd (by linarith : u₁ - 1 < u₁) fun u hu => ?_
    have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun u => abs_nonneg _)
      hc_cont.abs.continuousOn.integrableOn_Icc).1 hsmall
    have heq := Measure.eqOn_Icc_of_ae_eq volume (by linarith : u₁ - 1 ≠ u₁) hae
      hc_cont.abs.continuousOn (continuous_const (y := (0 : ℝ))).continuousOn hu
    have h1 : (F (u : ℂ)).re = 0 := abs_eq_zero.1 heq
    exact Complex.ext (by simpa using h1) (by simpa using hFreal u)
  have hbig : (1 : ℝ) / 2 ≤ ∫ u in Icc u₁ (R₀ * hankelBeta1), |(F (u : ℂ)).re| :=
    ge_of_tendsto (hlim u₁ (R₀ * hankelBeta1) hR₀b.le) (by
      filter_upwards [hev1, hev3, hev4] with k h1 h3 h4 using (key k h1 h3 h4).2)
  have hz : ∫ u in Icc u₁ (R₀ * hankelBeta1), |(F (u : ℂ)).re| = 0 := by simp [hF0]
  linarith

/-! ### Hankel profiles: `p = (ĥ + h)/2`, `q = (ĥ - h)/2` -/

/-- The even part `p = (G + 𝓗_c G)/2` of a Hankel profile. -/
noncomputable def hankelPlus (c : ℝ) (G : ℝ → ℝ) : ℝ → ℝ :=
  fun s => (1 / 2 : ℝ) * (G s + besselHankelTransform c G s)

/-- The odd part `q = (𝓗_c G - G)/2` of a Hankel profile. -/
noncomputable def hankelMinus (c : ℝ) (G : ℝ → ℝ) : ℝ → ℝ :=
  fun s => (1 / 2 : ℝ) * (besselHankelTransform c G s - G s)

lemma hankelMass_add_le {c : ℝ} (hc : 0 < c) {f g : ℝ → ℝ}
    (hf : IntegrableOn (fun Δ => f Δ * hankelRho0 c Δ) (Ioi 0))
    (hg : IntegrableOn (fun Δ => g Δ * hankelRho0 c Δ) (Ioi 0)) :
    hankelMass c (fun Δ => f Δ + g Δ) ≤ hankelMass c f + hankelMass c g := by
  unfold hankelMass
  have hf_abs := abs_mul_rho0_integrableOn hc hf
  have hg_abs := abs_mul_rho0_integrableOn hc hg
  have hadd_int : IntegrableOn (fun Δ => |f Δ + g Δ| * hankelRho0 c Δ) (Ioi 0) :=
    abs_mul_rho0_integrableOn hc
      ((hf.add hg).congr (Eventually.of_forall fun Δ => by simp only [Pi.add_apply]; ring))
  have hrhs_int : IntegrableOn (fun Δ => |f Δ| * hankelRho0 c Δ + |g Δ| * hankelRho0 c Δ) (Ioi 0) :=
    hf_abs.add hg_abs
  rw [← integral_add hf_abs hg_abs]
  refine setIntegral_mono_on hadd_int hrhs_int measurableSet_Ioi fun Δ hΔ => ?_
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (hankelRho0_nonneg hc hΔ.le)

namespace HankelShellProfile

variable {c T : ℝ} {G : ℝ → ℝ}

lemma T_pos (P : HankelShellProfile c T G) : 0 < T := by
  by_contra h
  push Not at h
  have := P.tail 0 h
  linarith [P.origin_pos]

lemma plus {d : ℕ} (hd : 2 ≤ d) (P : HankelShellProfile ((d : ℝ) / 2) T G) :
    IsHankelEigenfn ((d : ℝ) / 2) 1 (hankelPlus ((d : ℝ) / 2) G) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hc : (((n + 1 : ℕ) : ℝ) / 2) = ((n : ℝ) + 1) / 2 := by push_cast; ring
  rw [hc] at P ⊢
  exact isHankelEigenfn_plus n (by omega) P.cont P.int P.cont_hat P.int_hat

lemma minus {d : ℕ} (hd : 2 ≤ d) (P : HankelShellProfile ((d : ℝ) / 2) T G) :
    IsHankelEigenfn ((d : ℝ) / 2) (-1) (hankelMinus ((d : ℝ) / 2) G) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hc : (((n + 1 : ℕ) : ℝ) / 2) = ((n : ℝ) + 1) / 2 := by push_cast; ring
  rw [hc] at P ⊢
  exact isHankelEigenfn_minus n (by omega) P.cont P.int P.cont_hat P.int_hat

lemma abs_plus_le_minus (P : HankelShellProfile c T G) {Δ : ℝ} (hΔ : T ≤ Δ) :
    |hankelPlus c G Δ| ≤ hankelMinus c G Δ := by
  have hΔ0 : 0 ≤ Δ := P.T_pos.le.trans hΔ
  have h1 := P.nonneg_hat Δ hΔ0
  have h2 := P.tail Δ hΔ
  unfold hankelPlus hankelMinus
  rw [abs_le]
  constructor <;> linarith

/-- Hankel inversion at the origin: `h(0) = ∫ ĥ ρ₀`. -/
lemma integral_hat_eq {d : ℕ} (hd : 2 ≤ d) (P : HankelShellProfile ((d : ℝ) / 2) T G) :
    ∫ s in Ioi (0 : ℝ), besselHankelTransform ((d : ℝ) / 2) G s * hankelRho0 ((d : ℝ) / 2) s = G 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hc : (((n + 1 : ℕ) : ℝ) / 2) = ((n : ℝ) + 1) / 2 := by push_cast; ring
  rw [hc] at P ⊢
  have hc0 : 0 < ((n : ℝ) + 1) / 2 := by positivity
  have := besselHankel_involutive n (by omega) P.cont P.int P.cont_hat P.int_hat (le_refl (0 : ℝ))
  rw [besselHankelTransform_zero hc0] at this
  exact this

lemma integral_eq {d : ℕ} (hd : 2 ≤ d) (P : HankelShellProfile ((d : ℝ) / 2) T G) :
    ∫ s in Ioi (0 : ℝ), G s * hankelRho0 ((d : ℝ) / 2) s = G 0 := by
  have hc0 : 0 < (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have := P.origin
  rw [besselHankelTransform_zero hc0] at this
  exact this.symm

lemma hankelMass_hat {d : ℕ} (hd : 2 ≤ d) (P : HankelShellProfile ((d : ℝ) / 2) T G) :
    hankelMass ((d : ℝ) / 2) (besselHankelTransform ((d : ℝ) / 2) G) = G 0 := by
  rw [← P.integral_hat_eq hd]
  unfold hankelMass
  refine setIntegral_congr_fun measurableSet_Ioi fun Δ hΔ => ?_
  rw [abs_of_nonneg (P.nonneg_hat Δ (le_of_lt hΔ))]

lemma origin_le_mass {d : ℕ} (hd : 2 ≤ d) (P : HankelShellProfile ((d : ℝ) / 2) T G) :
    G 0 ≤ hankelMass ((d : ℝ) / 2) (hankelPlus ((d : ℝ) / 2) G) +
      hankelMass ((d : ℝ) / 2) (hankelMinus ((d : ℝ) / 2) G) := by
  have hc0 : 0 < (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  rw [← P.hankelMass_hat hd]
  have heq : besselHankelTransform ((d : ℝ) / 2) G =
      fun Δ => hankelPlus ((d : ℝ) / 2) G Δ + hankelMinus ((d : ℝ) / 2) G Δ := by
    funext Δ; unfold hankelPlus hankelMinus; ring
  rw [heq]
  exact hankelMass_add_le hc0 (P.plus hd).int (P.minus hd).int

/-- `∫ ĥ ρ₀ = ∫ h ρ₀`: the odd part `q` has zero integral. -/
lemma integral_minus_eq_zero {d : ℕ} (hd : 2 ≤ d) (P : HankelShellProfile ((d : ℝ) / 2) T G) :
    ∫ s in Ioi (0 : ℝ), hankelMinus ((d : ℝ) / 2) G s * hankelRho0 ((d : ℝ) / 2) s = 0 := by
  have h1 := P.integral_hat_eq hd
  have h2 := P.integral_eq hd
  have hĜ := P.int_hat
  have hG := P.int
  have : (fun s => hankelMinus ((d : ℝ) / 2) G s * hankelRho0 ((d : ℝ) / 2) s) =
      fun s => (1 / 2 : ℝ) * (besselHankelTransform ((d : ℝ) / 2) G s * hankelRho0 ((d : ℝ) / 2) s -
        G s * hankelRho0 ((d : ℝ) / 2) s) := by
    funext s; unfold hankelMinus; ring
  rw [this, integral_const_mul, integral_sub hĜ hG, h1, h2]
  ring

lemma minus_ne_zero {d : ℕ} (hd : 2 ≤ d) (P : HankelShellProfile ((d : ℝ) / 2) T G) :
    ∃ Δ : ℝ, 0 ≤ Δ ∧ hankelMinus ((d : ℝ) / 2) G Δ ≠ 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hc : (((n + 1 : ℕ) : ℝ) / 2) = ((n : ℝ) + 1) / 2 := by push_cast; ring
  rw [hc] at P ⊢
  by_contra hcon
  push Not at hcon
  have hGhat : ∀ Δ : ℝ, 0 ≤ Δ → besselHankelTransform (((n : ℝ) + 1) / 2) G Δ = G Δ := by
    intro Δ hΔ
    have := hcon Δ hΔ
    unfold hankelMinus at this
    linarith
  have hGzero : ∀ Δ : ℝ, T ≤ Δ → G Δ = 0 := fun Δ hΔ => by
    refine le_antisymm (P.tail Δ hΔ) ?_
    have hΔ0 : 0 ≤ Δ := P.T_pos.le.trans hΔ
    rw [← hGhat Δ hΔ0]
    exact P.nonneg_hat Δ hΔ0
  set f : EuclSp (n + 1) → ℂ := fun x => (G (‖x‖ ^ 2 / 2) : ℂ) with hf
  have hfc : Continuous f :=
    Complex.continuous_ofReal.comp (P.cont.comp_continuous
      ((continuous_norm.pow 2).div_const 2) fun x => (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2 / 2))
  have hfi : Integrable f := (integrable_radialLift_iff n hn G).2 P.int
  have hsupp : HasCompactSupport f := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : EuclSp (n + 1)) (√(2 * T))) ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    have hr0 := Real.sqrt_nonneg (2 * T)
    have hsq := Real.sq_sqrt (by linarith [P.T_pos] : 0 ≤ 2 * T)
    have : T ≤ ‖x‖ ^ 2 / 2 := by nlinarith
    simp only [hf, hGzero _ this, Complex.ofReal_zero]
  have hF : ∀ y : EuclSp (n + 1), 𝓕 f y = ((G (‖y‖ ^ 2 / 2) : ℝ) : ℂ) := fun y => by
    rw [hf, fourier_radial_hankel n hn P.cont hfi y, hGhat _ (by positivity)]
  have hf0 := fourier_compact_support_eq_zero hfc hsupp (√(2 * T)) fun y hy => by
    rw [hF]
    have hr0 := Real.sqrt_nonneg (2 * T)
    have hsq := Real.sq_sqrt (by linarith [P.T_pos] : 0 ≤ 2 * T)
    have : T ≤ ‖y‖ ^ 2 / 2 := by nlinarith
    simp [hGzero _ this]
  have h0 := congrFun hf0 0
  simp only [hf, norm_zero, Pi.zero_apply] at h0
  have : G 0 = 0 := by simpa using h0
  linarith [P.origin_pos]

end HankelShellProfile

/-! ### Step (a) for Hankel profiles -/

theorem hankelShell_mass_ratio_bdd (H : RadialCompactness) {dk : ℕ → ℕ}
    (hdk : Tendsto dk atTop atTop) (h2 : ∀ k, 2 ≤ dk k) {u_star : ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) {G : ℕ → ℝ → ℝ} {T : ℕ → ℝ}
    (hP : ∀ k, HankelShellProfile ((dk k : ℝ) / 2) (T k) (G k))
    (hT : ∀ k, T k ≤ (dk k : ℝ) / (2 * π ^ 2) - (u_star / hankelBeta1) * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)
      + ε k * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)) :
    ∃ C : ℝ, ∀ k, hankelMass ((dk k : ℝ) / 2) (hankelPlus ((dk k : ℝ) / 2) (G k)) ≤
      C * hankelMass ((dk k : ℝ) / 2) (hankelMinus ((dk k : ℝ) / 2) (G k)) := by
  have hcpos : ∀ k, 0 < (dk k : ℝ) / 2 := fun k => by
    have : (2 : ℝ) ≤ dk k := by exact_mod_cast h2 k
    positivity
  refine mass_ratio_bdd H (c := fun k => (dk k : ℝ) / 2)
    ((tendsto_natCast_atTop_atTop.comp hdk).atTop_div_const (by norm_num)) hcpos
    (p := fun k => hankelPlus ((dk k : ℝ) / 2) (G k))
    (q := fun k => hankelMinus ((dk k : ℝ) / 2) (G k))
    (fun k => (hP k).plus (h2 k)) (fun k => ((hP k).minus (h2 k)).int)
    (fun k => hankelMass_pos_of_continuousOn (hcpos k) ((hP k).minus (h2 k)).cont
      ((hP k).minus (h2 k)).int ((hP k).minus_ne_zero (h2 k)))
    hε (u₀ := u_star) (T := T) (fun k => ?_) (fun k Δ hΔ => (hP k).abs_plus_le_minus hΔ)
  have := hT k
  rwa [show (dk k : ℝ) / (2 * π ^ 2) = ((dk k : ℝ) / 2) / π ^ 2 by rw [div_div]] at this

/-- info: 'FormalResearch.SignUncertainty.entire_eq_zero_of_zero_on_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entire_eq_zero_of_zero_on_Icc

/-- info: 'FormalResearch.SignUncertainty.mass_ratio_bdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mass_ratio_bdd

/-- info: 'FormalResearch.SignUncertainty.HankelShellProfile.integral_hat_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HankelShellProfile.integral_hat_eq

/-- info: 'FormalResearch.SignUncertainty.HankelShellProfile.integral_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HankelShellProfile.integral_eq

/-- info: 'FormalResearch.SignUncertainty.HankelShellProfile.hankelMass_hat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HankelShellProfile.hankelMass_hat

/-- info: 'FormalResearch.SignUncertainty.HankelShellProfile.origin_le_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HankelShellProfile.origin_le_mass

/-- info: 'FormalResearch.SignUncertainty.HankelShellProfile.integral_minus_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HankelShellProfile.integral_minus_eq_zero

/-- info: 'FormalResearch.SignUncertainty.HankelShellProfile.minus_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HankelShellProfile.minus_ne_zero

/-- info: 'FormalResearch.SignUncertainty.hankelShell_mass_ratio_bdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelShell_mass_ratio_bdd

end FormalResearch.SignUncertainty
