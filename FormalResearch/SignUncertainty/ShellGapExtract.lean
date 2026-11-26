module

public import FormalResearch.SignUncertainty.ShellGapMassRatio
public import FormalResearch.SignUncertainty.ShellGapMellin
public import FormalResearch.SignUncertainty.ShellGapTransport
public import FormalResearch.SignUncertainty.RadialCompactnessProof

/-!
# Extraction of the two limit profiles and their constraints (`thm:ce-shell-gap`)

For sequences `p_k ∈ 𝒜_{c_k}^{+1}`, `q_k ∈ 𝒜_{c_k}^{-1}` with `M[p_k] ≤ B M[q_k]` (`mass_ratio_bdd`):
`extract_two` extracts a common subsequence along which `Ψ_{p_k}/M[q_k]` and `Ψ_{q_k}/M[q_k]` converge
locally uniformly to the real parts of entire functions of the Airy class (`profile_compactness`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

lemma tlu_comp_index {ι ι' α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ι → α → β} {f : α → β} {s : Set α} {p : Filter ι}
    (h : TendstoLocallyUniformlyOn F f p s) {g : ι' → ι} {p' : Filter ι'}
    (hg : Tendsto g p' p) : TendstoLocallyUniformlyOn (fun n => F (g n)) f p' s := by
  intro u hu x hx
  obtain ⟨t, ht, hh⟩ := h u hu x hx
  exact ⟨t, ht, hg.eventually hh⟩

theorem extract_two (H : RadialCompactness) {c : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    {p q : ℕ → ℝ → ℝ} (hp : ∀ k, IsHankelEigenfn (c k) 1 (p k))
    (hq : ∀ k, IsHankelEigenfn (c k) (-1) (q k)) {μ : ℕ → ℝ} (hμ : ∀ k, 0 < μ k) {B : ℝ}
    (hpB : ∀ k, hankelMass (c k) (p k) ≤ B * μ k) (hqB : ∀ k, hankelMass (c k) (q k) ≤ B * μ k) :
    ∃ (K : ℕ → ℕ) (Fp Fq : ℂ → ℂ), StrictMono K ∧ InAiryClass Fp ∧ InAiryClass Fq ∧
      TendstoLocallyUniformlyOn
        (fun n u => hankelWindowProfile (c (K n)) (p (K n)) u / μ (K n))
        (fun u => (Fp (u : ℂ)).re) atTop univ ∧
      TendstoLocallyUniformlyOn
        (fun n u => hankelWindowProfile (c (K n)) (q (K n)) u / μ (K n))
        (fun u => (Fq (u : ℂ)).re) atTop univ := by
  set p' : ℕ → ℝ → ℝ := fun k Δ => (μ k)⁻¹ * p k Δ with hp'
  set q' : ℕ → ℝ → ℝ := fun k Δ => (μ k)⁻¹ * q k Δ with hq'
  have hmass : ∀ (f : ℕ → ℝ → ℝ) (k : ℕ), hankelMass (c k) (f k) ≤ B * μ k →
      hankelMass (c k) (fun Δ => (μ k)⁻¹ * f k Δ) ≤ B := by
    intro f k h
    rw [hankelMass_smul, abs_of_pos (inv_pos.mpr (hμ k))]
    calc (μ k)⁻¹ * hankelMass (c k) (f k) ≤ (μ k)⁻¹ * (B * μ k) :=
          mul_le_mul_of_nonneg_left h (inv_pos.mpr (hμ k)).le
      _ = B := by have := (hμ k).ne'; field_simp
  have hwin : ∀ (f : ℕ → ℝ → ℝ) (k : ℕ) (u : ℝ),
      hankelWindowProfile (c k) (fun Δ => (μ k)⁻¹ * f k Δ) u =
        hankelWindowProfile (c k) (f k) u / μ k := by
    intro f k u
    rw [hankelWindowProfile_smul, inv_mul_eq_div]
  obtain ⟨ms₁, Fq, Cq, νq, hms₁, hlocq, -, -, hFqd, hFqi, hCq, hFqb, hFqr⟩ :=
    H.profile_compactness B (-1) (Or.inr rfl) c q' hc (fun k => (hq k).smul (μ k)⁻¹)
      (fun k => hmass q k (hqB k))
  obtain ⟨ms₂, Fp, Cp, νp, hms₂, hlocp, -, -, hFpd, hFpi, hCp, hFpb, hFpr⟩ :=
    H.profile_compactness B 1 (Or.inl rfl) (fun n => c (ms₁ n)) (fun n => p' (ms₁ n))
      (hc.comp hms₁.tendsto_atTop) (fun n => (hp (ms₁ n)).smul (μ (ms₁ n))⁻¹)
      (fun n => hmass p (ms₁ n) (hpB (ms₁ n)))
  refine ⟨fun n => ms₁ (ms₂ n), Fp, Fq, hms₁.comp hms₂, ⟨hFpd, hFpi, ⟨Cp, νp, hCp, hFpb⟩, hFpr⟩,
    ⟨hFqd, hFqi, ⟨Cq, νq, hCq, hFqb⟩, hFqr⟩, ?_, ?_⟩
  · exact hlocp.congr (fun n u _ => hwin p (ms₁ (ms₂ n)) u)
  · have h := tlu_comp_index hlocq (g := ms₂) hms₂.tendsto_atTop
    exact h.congr (fun n u _ => hwin q (ms₁ (ms₂ n)) u)

/-! ### Window-profile algebra and signs -/

lemma hankelWindowProfile_add (c : ℝ) (f g : ℝ → ℝ) (u : ℝ) :
    hankelWindowProfile c (fun Δ => f Δ + g Δ) u =
      hankelWindowProfile c f u + hankelWindowProfile c g u := by
  unfold hankelWindowProfile
  dsimp only
  split_ifs <;> ring

lemma hankelWindowProfile_sub (c : ℝ) (f g : ℝ → ℝ) (u : ℝ) :
    hankelWindowProfile c (fun Δ => f Δ - g Δ) u =
      hankelWindowProfile c f u - hankelWindowProfile c g u := by
  unfold hankelWindowProfile
  dsimp only
  split_ifs <;> ring

lemma hankelWindowProfile_nonneg_of {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ} {u : ℝ}
    (h : 0 < winDelta c u → 0 ≤ f (winDelta c u)) : 0 ≤ hankelWindowProfile c f u := by
  unfold hankelWindowProfile
  dsimp only
  split_ifs with hΔ
  · have h := h hΔ
    have hρ := hankelRho0_pos hc hΔ
    have ha : 0 ≤ c ^ (1 / 3 : ℝ) / hankelBeta1 :=
      div_nonneg (Real.rpow_nonneg hc.le _) hankelBeta1_pos.le
    exact mul_nonneg ha (mul_nonneg h hρ.le)
  · exact le_refl _

lemma hankelWindowProfile_nonpos_of {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ} {u : ℝ}
    (h : 0 < winDelta c u → f (winDelta c u) ≤ 0) : hankelWindowProfile c f u ≤ 0 := by
  unfold hankelWindowProfile
  dsimp only
  split_ifs with hΔ
  · have h := h hΔ
    have hρ := hankelRho0_pos hc hΔ
    have ha : 0 ≤ c ^ (1 / 3 : ℝ) / hankelBeta1 :=
      div_nonneg (Real.rpow_nonneg hc.le _) hankelBeta1_pos.le
    exact mul_nonpos_of_nonneg_of_nonpos ha (mul_nonpos_of_nonpos_of_nonneg h hρ.le)
  · exact le_refl _

lemma winDelta_ge {c T ε ustar a u : ℝ} (hc : 0 < c)
    (hT : T ≤ c / Real.pi ^ 2 - (ustar / hankelBeta1) * c ^ (1 / 3 : ℝ) + ε * c ^ (1 / 3 : ℝ))
    (hε : ε ≤ (ustar - a) / hankelBeta1) (hu : u ≤ a) : T ≤ winDelta c u := by
  have ht0 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have hβ := hankelBeta1_pos
  unfold winDelta
  have h1 : ε * c ^ (1 / 3 : ℝ) ≤ (ustar - a) / hankelBeta1 * c ^ (1 / 3 : ℝ) :=
    mul_le_mul_of_nonneg_right hε ht0.le
  have h2 : a / hankelBeta1 * c ^ (1 / 3 : ℝ) ≥ u / hankelBeta1 * c ^ (1 / 3 : ℝ) :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hu hβ.le) ht0.le
  have h3 : (ustar - a) / hankelBeta1 * c ^ (1 / 3 : ℝ) =
      ustar / hankelBeta1 * c ^ (1 / 3 : ℝ) - a / hankelBeta1 * c ^ (1 / 3 : ℝ) := by ring
  linarith

lemma limit_nonneg {c μ : ℕ → ℝ} {p q : ℕ → ℝ → ℝ} (hcpos : ∀ k, 0 < c k) (hμ : ∀ k, 0 < μ k)
    (hhat : ∀ k Δ, 0 ≤ Δ → 0 ≤ p k Δ + q k Δ) {P Q : ℝ → ℝ}
    (hP : TendstoLocallyUniformlyOn
      (fun n u => hankelWindowProfile (c n) (p n) u / μ n) P atTop univ)
    (hQ : TendstoLocallyUniformlyOn
      (fun n u => hankelWindowProfile (c n) (q n) u / μ n) Q atTop univ) (u : ℝ) :
    0 ≤ P u + Q u := by
  have h := (hP.tendsto_at (mem_univ u)).add (hQ.tendsto_at (mem_univ u))
  refine ge_of_tendsto' h fun n => ?_
  have e : hankelWindowProfile (c n) (p n) u / μ n + hankelWindowProfile (c n) (q n) u / μ n =
      hankelWindowProfile (c n) (fun Δ => p n Δ + q n Δ) u / μ n := by
    rw [hankelWindowProfile_add]; ring
  rw [e]
  refine div_nonneg (hankelWindowProfile_nonneg_of (hcpos n) ?_) (hμ n).le
  exact fun hΔ => hhat n _ hΔ.le

lemma limit_sub_nonpos {Φp Φq : ℕ → ℝ → ℝ} {P Q : ℝ → ℝ}
    (hP : TendstoLocallyUniformlyOn Φp P atTop univ) (hQ : TendstoLocallyUniformlyOn Φq Q atTop univ)
    (hPc : Continuous P) (hQc : Continuous Q) {u : ℕ → ℝ} {t : ℝ} (hu : Tendsto u atTop (𝓝 t))
    (h : ∀ᶠ n in atTop, Φp n (u n) - Φq n (u n) ≤ 0) : P t - Q t ≤ 0 := by
  have h1 := (tendstoLocallyUniformlyOn_univ.mp hP).tendsto_comp hPc.continuousAt hu
  have h2 := (tendstoLocallyUniformlyOn_univ.mp hQ).tendsto_comp hQc.continuousAt hu
  exact le_of_tendsto (h1.sub h2) h

lemma limit_left {c μ T ε : ℕ → ℝ} {p q : ℕ → ℝ → ℝ} (hcpos : ∀ k, 0 < c k) (hμ : ∀ k, 0 < μ k)
    {ustar : ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hT : ∀ k, T k ≤ c k / Real.pi ^ 2 - (ustar / hankelBeta1) * c k ^ (1 / 3 : ℝ) +
      ε k * c k ^ (1 / 3 : ℝ))
    (hdom : ∀ k Δ, T k ≤ Δ → |p k Δ| ≤ q k Δ) {P Q : ℝ → ℝ}
    (hP : TendstoLocallyUniformlyOn
      (fun n u => hankelWindowProfile (c n) (p n) u / μ n) P atTop univ)
    (hQ : TendstoLocallyUniformlyOn
      (fun n u => hankelWindowProfile (c n) (q n) u / μ n) Q atTop univ)
    (hPc : Continuous P) (hQc : Continuous Q) : ∀ u ≤ ustar, P u - Q u ≤ 0 := by
  have hlt : ∀ u < ustar, P u - Q u ≤ 0 := by
    intro u hu
    have hpos : 0 < (ustar - u) / hankelBeta1 := div_pos (sub_pos.2 hu) hankelBeta1_pos
    refine limit_sub_nonpos hP hQ hPc hQc (u := fun _ => u) tendsto_const_nhds ?_
    filter_upwards [hε.eventually (Iio_mem_nhds hpos)] with n hn
    have hge := winDelta_ge (hcpos n) (hT n) hn.le (le_refl u)
    have h2 : hankelWindowProfile (c n) (p n) u / μ n - hankelWindowProfile (c n) (q n) u / μ n =
        hankelWindowProfile (c n) (fun Δ => p n Δ - q n Δ) u / μ n := by
      rw [hankelWindowProfile_sub]; ring
    rw [h2]
    refine div_nonpos_of_nonpos_of_nonneg (hankelWindowProfile_nonpos_of (hcpos n) ?_) (hμ n).le
    intro _
    have := hdom n _ hge
    have h3 := le_abs_self (p n (winDelta (c n) u))
    linarith
  have hclosed : IsClosed {u : ℝ | P u - Q u ≤ 0} := isClosed_le (hPc.sub hQc) continuous_const
  intro u hu
  have : u ∈ closure (Iio ustar) := by
    rw [closure_Iio]; exact hu
  exact closure_minimal (fun x hx => hlt x hx) hclosed this

lemma limit_transport {c μ T ε : ℕ → ℝ} {q : ℕ → ℝ → ℝ} {ustar : ℝ}
    (hc : Tendsto c atTop atTop) (hcpos : ∀ k, 0 < c k)
    (hq : ∀ k, IsHankelEigenfn (c k) (-1) (q k)) (hμ : ∀ k, μ k = hankelMass (c k) (q k))
    (hμpos : ∀ k, 0 < μ k)
    (hzero : ∀ k, ∫ Δ in Ioi (0 : ℝ), q k Δ * hankelRho0 (c k) Δ = 0)
    (hε : Tendsto ε atTop (𝓝 0))
    (hT : ∀ k, T k ≤ c k / Real.pi ^ 2 - (ustar / hankelBeta1) * c k ^ (1 / 3 : ℝ) +
      ε k * c k ^ (1 / 3 : ℝ))
    (hqnn : ∀ k Δ, T k ≤ Δ → 0 ≤ q k Δ) {Q : ℝ → ℝ}
    (hQc : Continuous Q) (hQi : Integrable Q)
    (hQ : TendstoLocallyUniformlyOn
      (fun n u => hankelWindowProfile (c n) (q n) u / μ n) Q atTop univ) :
    (∫ u, |Q u| ≤ 1) ∧ (∫ u, Q u ≤ 0) ∧ (1 / 2 ≤ ∫ u in Ioi ustar, max (-Q u) 0) := by
  refine mass_transport (Φ := fun n u => hankelWindowProfile (c n) (q n) u / μ n) hQc hQi
    (fun n => ((integrable_hankelWindowProfile_iff (hcpos n) (q n)).2 (hq n).int).div_const _)
    hQ (fun n => ?_) (fun n => ?_) (fun a ha => ?_) (fun δ hδ => ?_)
  · rw [integral_div, integral_hankelWindowProfile (hcpos n), hzero n, zero_div]
  · simp_rw [abs_div, abs_of_pos (hμpos n)]
    rw [integral_div, integral_abs_hankelWindowProfile (hcpos n), ← hμ n]
    exact div_self (hμpos n).ne'
  · have hpos : 0 < (ustar - a) / hankelBeta1 := div_pos (sub_pos.2 ha) hankelBeta1_pos
    filter_upwards [hε.eventually (Iio_mem_nhds hpos)] with n hn u hu
    refine div_nonneg (hankelWindowProfile_nonneg_of (hcpos n) fun _ => ?_) (hμpos n).le
    exact hqnn n _ (winDelta_ge (hcpos n) (hT n) hn.le hu)
  · have t1 : Tendsto (fun x : ℝ => 8 * Real.exp (-5 * x ^ (3 / 2 : ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => x ^ (3 / 2 : ℝ)) atTop atTop :=
        tendsto_rpow_atTop (by norm_num)
      have h2 : Tendsto (fun x : ℝ => -5 * x ^ (3 / 2 : ℝ)) atTop atBot :=
        h1.const_mul_atTop_of_neg (by norm_num)
      simpa using (Real.tendsto_exp_atBot.comp h2).const_mul 8
    obtain ⟨R₀, hR₀1, hR₀⟩ : ∃ R₀ : ℝ, 1 ≤ R₀ ∧ 8 * Real.exp (-5 * R₀ ^ (3 / 2 : ℝ)) ≤ δ / 2 := by
      obtain ⟨x, h1, h2⟩ := ((eventually_ge_atTop (1 : ℝ)).and
        (t1.eventually (Iic_mem_nhds (half_pos hδ)))).exists
      exact ⟨x, h1, h2⟩
    refine ⟨R₀ * hankelBeta1, fun b hb => ?_⟩
    have hβ := hankelBeta1_pos
    set R : ℝ := b / hankelBeta1 with hR
    have hRb : R * hankelBeta1 = b := by rw [hR]; field_simp
    have hR₀R : R₀ ≤ R := by rw [hR, le_div_iff₀ hβ]; exact hb
    have e1 : 8 * Real.exp (-5 * R ^ (3 / 2 : ℝ)) ≤ δ / 2 := by
      refine le_trans ?_ hR₀
      have : R₀ ^ (3 / 2 : ℝ) ≤ R ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by linarith) hR₀R (by norm_num)
      have := Real.exp_le_exp.mpr (by linarith : -5 * R ^ (3 / 2 : ℝ) ≤ -5 * R₀ ^ (3 / 2 : ℝ))
      linarith
    have t2 : Tendsto (fun n => 8 * Real.exp (-(1 / 25) * c n)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n => -(1 / 25) * c n) atTop atBot :=
        hc.const_mul_atTop_of_neg (by norm_num)
      simpa using (Real.tendsto_exp_atBot.comp h2).const_mul 8
    filter_upwards [hc.eventually_ge_atTop 56, t2.eventually (Iic_mem_nhds (half_pos hδ))] with n hn56 hn2
    have hc0 := hcpos n
    have hμn := hμpos n
    have hdl := deep_lobe_mass_thm hn56 (hq n) (Or.inr rfl) (R := R) (by linarith)
    simp_rw [abs_div, abs_of_pos hμn]
    rw [integral_div, ← hRb, integral_tail_abs_hankelWindowProfile hc0 (q n) R, div_le_iff₀ hμn]
    refine hdl.trans ?_
    rw [← hμ n]
    nlinarith

lemma limit_laplace {c μ : ℕ → ℝ} {p q : ℕ → ℝ → ℝ} (hc : Tendsto c atTop atTop)
    (hp : ∀ k, IsHankelEigenfn (c k) 1 (p k)) (hq : ∀ k, IsHankelEigenfn (c k) (-1) (q k))
    (hμ : ∀ k, 0 < μ k) {B : ℝ} (hpB : ∀ k, hankelMass (c k) (p k) ≤ B * μ k)
    (hqB : ∀ k, hankelMass (c k) (q k) ≤ B * μ k)
    (hhat : ∀ k Δ, 0 ≤ Δ → 0 ≤ p k Δ + q k Δ) {P Q : ℝ → ℝ} (hPc : Continuous P)
    (hQc : Continuous Q)
    (hP : TendstoLocallyUniformlyOn
      (fun n u => hankelWindowProfile (c n) (p n) u / μ n) P atTop univ)
    (hQ : TendstoLocallyUniformlyOn
      (fun n u => hankelWindowProfile (c n) (q n) u / μ n) Q atTop univ)
    {y : ℝ} (hy : 0 < y) (hPi : Integrable (fun u => P u * Real.exp (y * u)))
    (hQi : Integrable (fun u => Q u * Real.exp (y * u))) :
    0 ≤ ∫ u, (P u - Q u) * Real.exp (y * u) := by
  have hy0 : 0 ≤ y := hy.le
  have lp := laplace_limit hc (Or.inl rfl) hp hμ hpB hPc hP hy hPi
  have lq := laplace_limit hc (Or.inr rfl) hq hμ hqB hQc hQ hy hQi
  have hd := lp.sub lq
  have e56 : ∀ᶠ k in atTop, 56 ≤ c k := hc.eventually_ge_atTop 56
  have eζ : ∀ᶠ k in atTop, laplaceZeta (c k) y ≤ 1 / 4 :=
    ((tendsto_laplaceZeta y).comp hc).eventually (Iic_mem_nhds (by norm_num))
  have hnn : ∀ᶠ k in atTop,
      0 ≤ (∫ Δ in Ioi (0 : ℝ), p k Δ * hankelRho0 (c k) Δ * laplaceWeight (c k) y Δ) / μ k -
        (∫ Δ in Ioi (0 : ℝ), q k Δ * hankelRho0 (c k) Δ * laplaceWeight (c k) y Δ) / μ k := by
    filter_upwards [e56, eζ] with k hk hζk
    have hpi : IntegrableOn (fun Δ => p k Δ * hankelRho0 (c k) Δ * laplaceWeight (c k) y Δ) (Ioi 0) :=
      (integrableOn_weighted hk hy0 hζk (hp k) (Or.inl rfl)).congr_fun (fun Δ _ => by ring)
        measurableSet_Ioi
    have hqi : IntegrableOn (fun Δ => q k Δ * hankelRho0 (c k) Δ * laplaceWeight (c k) y Δ) (Ioi 0) :=
      (integrableOn_weighted hk hy0 hζk (hq k) (Or.inr rfl)).congr_fun (fun Δ _ => by ring)
        measurableSet_Ioi
    have h := weighted_nonneg hk hy hζk (hp k) (hq k) (hhat k)
    have hs : ∫ Δ in Ioi (0 : ℝ), (p k Δ - q k Δ) * hankelRho0 (c k) Δ * laplaceWeight (c k) y Δ =
        (∫ Δ in Ioi (0 : ℝ), p k Δ * hankelRho0 (c k) Δ * laplaceWeight (c k) y Δ) -
          ∫ Δ in Ioi (0 : ℝ), q k Δ * hankelRho0 (c k) Δ * laplaceWeight (c k) y Δ := by
      rw [← integral_sub hpi hqi]
      refine integral_congr_ae (Eventually.of_forall fun Δ => ?_)
      simp only; ring
    rw [hs] at h
    rw [← sub_div]
    exact div_nonneg h (hμ k).le
  have hlim := ge_of_tendsto hd hnn
  have hw : ∀ (G : ℝ → ℝ), (∫ u, G u * Real.exp (-(y ^ 3) / 12 + y * u)) =
      Real.exp (-(y ^ 3) / 12) * ∫ u, G u * Real.exp (y * u) := by
    intro G
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only; rw [Real.exp_add]; ring
  have hsub : (∫ u, P u * Real.exp (-(y ^ 3) / 12 + y * u)) -
      ∫ u, Q u * Real.exp (-(y ^ 3) / 12 + y * u) =
        Real.exp (-(y ^ 3) / 12) * ∫ u, (P u - Q u) * Real.exp (y * u) := by
    rw [hw P, hw Q, ← mul_sub, ← integral_sub hPi hQi]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only; ring
  rw [hsub] at hlim
  exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp hlim

/-! ### The shell sites in the window variable -/

lemma winDelta_anti {c u v : ℝ} (hc : 0 < c) (h : u ≤ v) : winDelta c v ≤ winDelta c u := by
  have ht0 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  unfold winDelta
  have := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h hankelBeta1_pos.le) ht0.le
  linarith

lemma eventually_pos_winDelta (a : ℝ) : ∀ᶠ c : ℝ in atTop, 0 < winDelta c a := by
  have hβ := hankelBeta1_pos
  have hπ : 0 < Real.pi ^ 2 := by positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually_ge_atTop
      (max 1 (Real.pi ^ 2 * |a| / hankelBeta1 + 1))] with c hc0 ht
  set t3 : ℝ := c ^ (1 / 3 : ℝ) with ht3def
  have ht3 : t3 ^ 3 = c := by
    rw [ht3def, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have h1 : 1 ≤ t3 := le_trans (le_max_left _ _) ht
  have h2 : Real.pi ^ 2 * |a| / hankelBeta1 + 1 ≤ t3 := le_trans (le_max_right _ _) ht
  have h3 : a / hankelBeta1 ≤ |a| / hankelBeta1 :=
    div_le_div_of_nonneg_right (le_abs_self a) hβ.le
  have h4 : |a| / hankelBeta1 + 1 / Real.pi ^ 2 ≤ t3 ^ 2 / Real.pi ^ 2 := by
    have : Real.pi ^ 2 * |a| / hankelBeta1 + 1 ≤ t3 ^ 2 := by nlinarith
    calc |a| / hankelBeta1 + 1 / Real.pi ^ 2 = (Real.pi ^ 2 * |a| / hankelBeta1 + 1) / Real.pi ^ 2 := by
          field_simp
      _ ≤ t3 ^ 2 / Real.pi ^ 2 := div_le_div_of_nonneg_right this hπ.le
  have h5 : 0 < 1 / Real.pi ^ 2 := by positivity
  unfold winDelta
  rw [← ht3def]
  have : a / hankelBeta1 < t3 ^ 2 / Real.pi ^ 2 := by linarith
  have h6 : 0 < t3 ^ 2 / Real.pi ^ 2 - a / hankelBeta1 := by linarith
  have h7 : 0 < t3 := by linarith
  calc (0 : ℝ) < t3 * (t3 ^ 2 / Real.pi ^ 2 - a / hankelBeta1) := mul_pos h7 h6
    _ = c / Real.pi ^ 2 - a / hankelBeta1 * t3 := by rw [← ht3]; ring

lemma shell_window_point {t : ℝ} {r : ℕ → ℝ}
    (hr : Tendsto (fun d : ℕ => r d / ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) atTop (𝓝 0))
    {dk : ℕ → ℕ} (hdk : Tendsto dk atTop atTop) (h2 : ∀ k, 2 ≤ dk k) :
    ∃ u : ℕ → ℝ, Tendsto u atTop (𝓝 t) ∧
      (∀ n, winDelta ((dk n : ℝ) / 2) (u n) = shellSite t r (dk n)) ∧
      ∀ᶠ n in atTop, 0 < shellSite t r (dk n) := by
  have hβ := hankelBeta1_pos
  set u : ℕ → ℝ := fun n => t - hankelBeta1 * (r (dk n) / ((dk n : ℝ) / 2) ^ (1 / 3 : ℝ)) with hu
  have hcpos : ∀ n, 0 < (dk n : ℝ) / 2 := fun n => by
    have : (2 : ℝ) ≤ dk n := by exact_mod_cast h2 n
    positivity
  have hutend : Tendsto u atTop (𝓝 t) := by
    have := (hr.comp hdk).const_mul hankelBeta1
    have := (tendsto_const_nhds (x := t)).sub this
    simpa [hu, Function.comp_def] using this
  have hw : ∀ n, winDelta ((dk n : ℝ) / 2) (u n) = shellSite t r (dk n) := by
    intro n
    have ht0 : 0 < ((dk n : ℝ) / 2) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (hcpos n) _
    unfold winDelta shellSite
    simp only [hu]
    field_simp
    ring
  refine ⟨u, hutend, hw, ?_⟩
  have hc : Tendsto (fun n => (dk n : ℝ) / 2) atTop atTop :=
    ((tendsto_natCast_atTop_atTop.comp hdk).atTop_div_const (by norm_num))
  have hev := hc.eventually (eventually_pos_winDelta (t + 1))
  have hu1 : ∀ᶠ n in atTop, u n ≤ t + 1 := hutend.eventually (Iic_mem_nhds (by linarith))
  filter_upwards [hev, hu1] with n h1 h2'
  rw [← hw n]
  exact lt_of_lt_of_le h1 (winDelta_anti (hcpos n) h2')

/-! ### Theorem H.14 in Hankel form -/

lemma two_mul_half (z : ℂ) : (2 : ℂ) * (((1 / 2 : ℝ) : ℂ) * z) = z := by
  push_cast; ring

/-- **`thm:ce-shell-gap`, Hankel form** (the extraction and constraint system `eq:ce-laplace-constraint`, with the
extracted subsequence and its limit profiles `P_∞ = Fp/2`, `Q_∞ = Fq/2` exposed, normalised by `M[q_k] = M[f_k]/2`;
not the origin floor or the endpoint case): proved from `radial_compactness`,
the mass-ratio bound `mass_ratio_bdd`, the Mellin reflection `weighted_nonneg`, the mass transport
`mass_transport` and the Laplace limit `laplace_limit`. -/
theorem hankelShellGap_sub (D : ShellHBData) :
    ∀ r : ℝ → ℕ → ℝ, (∀ t : ℝ, Tendsto (fun d : ℕ => r t d / ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) atTop (𝓝 0)) →
    ∀ (u_star : ℝ) (dk : ℕ → ℕ), Tendsto dk atTop atTop → (∀ k, 2 ≤ dk k) →
      ∀ (ε : ℕ → ℝ), Tendsto ε atTop (𝓝 0) →
        ∀ (G : ℕ → ℝ → ℝ) (T : ℕ → ℝ), (∀ k, HankelShellProfile ((dk k : ℝ) / 2) (T k) (G k)) →
          (∀ k, ∀ t ∈ D.S, t ≠ D.tm → 0 ≤ shellSite t (r t) (dk k) →
            G k (shellSite t (r t) (dk k)) ≤ 0) →
          (∀ k, T k ≤ (dk k : ℝ) / (2 * π ^ 2) - (u_star / hankelBeta1) * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)
            + ε k * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)) →
          ∃ (K : ℕ → ℕ) (Fp Fq : ℂ → ℂ), StrictMono K ∧ InAiryClass Fp ∧ InAiryClass Fq ∧
            TendstoLocallyUniformlyOn
              (fun n u => hankelWindowProfile ((dk (K n) : ℝ) / 2)
                  (hankelPlus ((dk (K n) : ℝ) / 2) (G (K n))) u /
                hankelMass ((dk (K n) : ℝ) / 2) (hankelMinus ((dk (K n) : ℝ) / 2) (G (K n))))
              (fun u => (Fp (u : ℂ)).re) atTop univ ∧
            TendstoLocallyUniformlyOn
              (fun n u => hankelWindowProfile ((dk (K n) : ℝ) / 2)
                  (hankelMinus ((dk (K n) : ℝ) / 2) (G (K n))) u /
                hankelMass ((dk (K n) : ℝ) / 2) (hankelMinus ((dk (K n) : ℝ) / 2) (G (K n))))
              (fun u => (Fq (u : ℂ)).re) atTop univ ∧
            TwoProfileFeasibleWitness D u_star (fun z => ((1 / 2 : ℝ) : ℂ) * (Fp z + Fq z))
              (fun z => ((1 / 2 : ℝ) : ℂ) * Fq z) := by
  have H := radial_compactness
  intro r hr u_star dk hdk h2 ε hε G T hP hshell hT
  have hβ := hankelBeta1_pos
  set c : ℕ → ℝ := fun k => (dk k : ℝ) / 2 with hcdef
  have hcpos : ∀ k, 0 < c k := fun k => by
    have : (2 : ℝ) ≤ dk k := by exact_mod_cast h2 k
    simp only [hcdef]; positivity
  have hc : Tendsto c atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hdk).atTop_div_const (by norm_num)
  set p : ℕ → ℝ → ℝ := fun k => hankelPlus (c k) (G k) with hpdef
  set q : ℕ → ℝ → ℝ := fun k => hankelMinus (c k) (G k) with hqdef
  have hp : ∀ k, IsHankelEigenfn (c k) 1 (p k) := fun k => (hP k).plus (h2 k)
  have hq : ∀ k, IsHankelEigenfn (c k) (-1) (q k) := fun k => (hP k).minus (h2 k)
  have hqpos : ∀ k, 0 < hankelMass (c k) (q k) := fun k =>
    hankelMass_pos_of_continuousOn (hcpos k) (hq k).cont (hq k).int ((hP k).minus_ne_zero (h2 k))
  obtain ⟨C, hC⟩ := hankelShell_mass_ratio_bdd H hdk h2 hε hP hT
  have hC' : ∀ k, hankelMass (c k) (p k) ≤ C * hankelMass (c k) (q k) := hC
  set μ : ℕ → ℝ := fun k => hankelMass (c k) (q k) with hμdef
  have hμpos : ∀ k, 0 < μ k := hqpos
  set B : ℝ := max C 1 with hBdef
  have hpB : ∀ k, hankelMass (c k) (p k) ≤ B * μ k := fun k =>
    (hC' k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hqpos k).le)
  have hqB : ∀ k, hankelMass (c k) (q k) ≤ B * μ k := fun k =>
    calc hankelMass (c k) (q k) = 1 * μ k := (one_mul _).symm
      _ ≤ B * μ k := mul_le_mul_of_nonneg_right (le_max_right _ _) (hqpos k).le
  have hTc : ∀ k, T k ≤ c k / Real.pi ^ 2 - (u_star / hankelBeta1) * c k ^ (1 / 3 : ℝ) +
      ε k * c k ^ (1 / 3 : ℝ) := fun k => by
    have := hT k
    rwa [show (dk k : ℝ) / (2 * Real.pi ^ 2) = ((dk k : ℝ) / 2) / Real.pi ^ 2 by rw [div_div]] at this
  have hdom : ∀ k Δ, T k ≤ Δ → |p k Δ| ≤ q k Δ := fun k Δ hΔ => (hP k).abs_plus_le_minus hΔ
  have hqnn : ∀ k Δ, T k ≤ Δ → 0 ≤ q k Δ := fun k Δ hΔ => (abs_nonneg _).trans (hdom k Δ hΔ)
  have hhat : ∀ k Δ, 0 ≤ Δ → 0 ≤ p k Δ + q k Δ := fun k Δ hΔ => by
    have := (hP k).nonneg_hat Δ hΔ
    simp only [hpdef, hqdef, hankelPlus, hankelMinus]; linarith
  have hGpq : ∀ k Δ, p k Δ - q k Δ = G k Δ := fun k Δ => by
    simp only [hpdef, hqdef, hankelPlus, hankelMinus]; ring
  have hzero : ∀ k, ∫ Δ in Ioi (0 : ℝ), q k Δ * hankelRho0 (c k) Δ = 0 := fun k =>
    (hP k).integral_minus_eq_zero (h2 k)
  obtain ⟨K, Fp, Fq, hK, hFp, hFq, hlocp, hlocq⟩ := extract_two H hc hp hq hμpos hpB hqB
  have hKt : Tendsto K atTop atTop := hK.tendsto_atTop
  have hc' : Tendsto (fun n => c (K n)) atTop atTop := hc.comp hKt
  have hcpos' : ∀ n, 0 < c (K n) := fun n => hcpos _
  have hμpos' : ∀ n, 0 < μ (K n) := fun n => hμpos _
  have hε' : Tendsto (fun n => ε (K n)) atTop (𝓝 0) := hε.comp hKt
  set Pr : ℝ → ℝ := fun u => (Fp (u : ℂ)).re with hPr
  set Qr : ℝ → ℝ := fun u => (Fq (u : ℂ)).re with hQr
  have hPc : Continuous Pr :=
    Complex.continuous_re.comp (hFp.1.continuous.comp Complex.continuous_ofReal)
  have hQc : Continuous Qr :=
    Complex.continuous_re.comp (hFq.1.continuous.comp Complex.continuous_ofReal)
  have hQi : Integrable Qr := by simpa using hFq.2.1.re
  have hnonneg : ∀ u, 0 ≤ Pr u + Qr u :=
    limit_nonneg (c := fun n => c (K n)) (μ := fun n => μ (K n)) (p := fun n => p (K n))
      (q := fun n => q (K n)) hcpos' hμpos' (fun n => hhat (K n)) hlocp hlocq
  have hleft : ∀ u ≤ u_star, Pr u - Qr u ≤ 0 :=
    limit_left (c := fun n => c (K n)) (μ := fun n => μ (K n)) (p := fun n => p (K n))
      (q := fun n => q (K n)) (T := fun n => T (K n)) (ε := fun n => ε (K n)) hcpos' hμpos'
      hε' (fun n => hTc (K n)) (fun n => hdom (K n)) hlocp hlocq hPc hQc
  have htrans := limit_transport (c := fun n => c (K n)) (μ := fun n => μ (K n))
    (q := fun n => q (K n)) (T := fun n => T (K n)) (ε := fun n => ε (K n)) hc' hcpos'
    (fun n => hq (K n)) (fun n => rfl) hμpos' (fun n => hzero (K n)) hε' (fun n => hTc (K n))
    (fun n => hqnn (K n)) hQc hQi hlocq
  have hshellP : ∀ t ∈ D.S, t ≠ D.tm → Pr t - Qr t ≤ 0 := by
    intro t ht htm
    obtain ⟨u, hut, huw, hpos⟩ := shell_window_point (t := t) (r := r t) (hr t)
      (dk := fun n => dk (K n)) (hdk.comp hKt) (fun n => h2 _)
    refine limit_sub_nonpos hlocp hlocq hPc hQc hut ?_
    filter_upwards [hpos] with n hn
    have e : hankelWindowProfile (c (K n)) (p (K n)) (u n) / μ (K n) -
        hankelWindowProfile (c (K n)) (q (K n)) (u n) / μ (K n) =
        hankelWindowProfile (c (K n)) (fun Δ => p (K n) Δ - q (K n) Δ) (u n) / μ (K n) := by
      rw [hankelWindowProfile_sub]; ring
    show hankelWindowProfile (c (K n)) (p (K n)) (u n) / μ (K n) -
        hankelWindowProfile (c (K n)) (q (K n)) (u n) / μ (K n) ≤ 0
    rw [e]
    refine div_nonpos_of_nonpos_of_nonneg (hankelWindowProfile_nonpos_of (hcpos' n) ?_) (hμpos' n).le
    intro _
    show p (K n) (winDelta (c (K n)) (u n)) - q (K n) (winDelta (c (K n)) (u n)) ≤ 0
    rw [hGpq, show winDelta (c (K n)) (u n) = shellSite t (r t) (dk (K n)) from huw n]
    exact hshell (K n) t ht htm hn.le
  have hlap : ∀ y : ℝ, 0 ≤ y → 0 ≤ ∫ u, (Pr u - Qr u) * Real.exp (y * u) := by
    intro y hy0
    have hpos : ∀ y : ℝ, 0 < y → 0 ≤ ∫ u, (Pr u - Qr u) * Real.exp (y * u) := fun y hy =>
      limit_laplace (c := fun n => c (K n)) (μ := fun n => μ (K n)) (p := fun n => p (K n))
        (q := fun n => q (K n)) hc' (fun n => hp (K n)) (fun n => hq (K n)) hμpos'
        (B := B) (fun n => hpB (K n)) (fun n => hqB (K n)) (fun n => hhat (K n)) hPc hQc hlocp
        hlocq hy (hFp.integrable_exp_nonneg hy.le) (hFq.integrable_exp_nonneg hy.le)
    rcases hy0.eq_or_lt with rfl | hy
    · have hF := hFp.sub hFq
      have hcont := hF.laplace_continuousOn_Ici 0 (mem_Ici.2 le_rfl)
      have hlim := (hcont.mono Ioi_subset_Ici_self).tendsto
      have key : 0 ≤ ∫ u : ℝ, ((Fp (u : ℂ) - Fq (u : ℂ)).re) * Real.exp (0 * u) := by
        refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun y hy => ?_)
        have := hpos y hy
        simpa [Complex.sub_re] using this
      simpa [Complex.sub_re] using key
    · exact hpos y hy
  refine ⟨K, Fp, Fq, hK, hFp, hFq, hlocp, hlocq, (hFp.add hFq).smul (1 / 2), hFq.smul (1 / 2),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    have := hnonneg u
    simp only [Complex.re_ofReal_mul, Complex.add_re]
    simp only [hPr, hQr] at this
    linarith
  · simp_rw [two_mul_half]
    have e : ∀ u : ℝ, ‖Fq (u : ℂ)‖ = |Qr u| := fun u =>
      (Complex.abs_re_eq_norm.mpr (hFq.2.2.2 u)).symm
    simp_rw [e]
    exact htrans.1
  · simp_rw [two_mul_half]
    exact htrans.2.1
  · simp_rw [two_mul_half]
    exact htrans.2.2
  · intro t ht htm
    have := hshellP t ht htm
    rw [two_mul_half, Complex.sub_re, Complex.re_ofReal_mul, Complex.add_re]
    simp only [hPr, hQr] at this
    linarith
  · intro u hu
    have := hleft u hu
    rw [two_mul_half, Complex.sub_re, Complex.re_ofReal_mul, Complex.add_re]
    simp only [hPr, hQr] at this
    linarith
  · intro y hy
    have := hlap y hy
    have e : ∀ u : ℝ, (((1 / 2 : ℝ) : ℂ) * (Fp (u : ℂ) + Fq (u : ℂ)) -
        2 * (((1 / 2 : ℝ) : ℂ) * Fq (u : ℂ))).re * Real.exp (y * u) =
        1 / 2 * ((Pr u - Qr u) * Real.exp (y * u)) := fun u => by
      rw [two_mul_half, Complex.sub_re, Complex.re_ofReal_mul, Complex.add_re]
      simp only [hPr, hQr]; ring
    simp_rw [e]
    rw [integral_const_mul]
    positivity

/-- **`thm:ce-shell-gap`, Hankel form** (`HankelShellGapLimit`): the conclusion of `hankelShellGap_sub` without the
subsequence. -/
theorem hankelShellGapLimit_proved (D : ShellHBData) : HankelShellGapLimit D := by
  intro r hr u_star dk hdk h2 ε hε G T hP hshell hT
  obtain ⟨_, _, _, _, _, _, _, _, hw⟩ := hankelShellGap_sub D r hr u_star dk hdk h2 ε hε G T hP hshell hT
  exact ⟨_, _, hw⟩

/-- info: 'FormalResearch.SignUncertainty.hankelShellGap_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelShellGap_sub

/-- info: 'FormalResearch.SignUncertainty.extract_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extract_two

/-- info: 'FormalResearch.SignUncertainty.limit_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limit_laplace

/-- info: 'FormalResearch.SignUncertainty.limit_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limit_transport

/-- info: 'FormalResearch.SignUncertainty.hankelShellGapLimit_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelShellGapLimit_proved

end FormalResearch.SignUncertainty
