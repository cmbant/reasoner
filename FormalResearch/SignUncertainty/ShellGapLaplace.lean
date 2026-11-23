module

public import FormalResearch.SignUncertainty.ShellGapWeight

/-!
# The Laplace limit `eq:ce-laplace-limit` (proof of `thm:ce-shell-gap`)

Window-variable bridges for the weight `W = laplaceWeight c y` (`LaplaceWeight.lean`) and the
convergence of weighted integrals of window profiles.

* `winDelta c u = c/π² - (u/β₁) c^{1/3}`, the `Δ`-coordinate of the window variable `u`;
  `hankelWindowProfile_mul`, `integral_window_weighted`: `∫ Ψ_f(u) φ(Δ_c u) du = ∫_{Δ>0} f φ ρ₀`.
* `tail_weighted_u`: the weighted right tail `∫_{u > R β₁} |Ψ_g| W(Δ_c u)` equals
  `∫_{0<Δ<P-Rt} |g| ρ₀ W`, controlled in `ShellGapWeight.lean` (`right_tail_weighted`).
* `left_tail_weighted_u`: the weighted left tail is at most `W(P + R t) M[g]` (`W` is decreasing).
* `integrable_weighted_window`: `Ψ_g(u) W(Δ_c u)` is integrable.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

/-- The `Δ`-coordinate `c/π² - (u/β₁) c^{1/3}` of the window variable `u`. -/
noncomputable def winDelta (c u : ℝ) : ℝ := c / Real.pi ^ 2 - u / hankelBeta1 * c ^ (1 / 3 : ℝ)

lemma continuous_winDelta (c : ℝ) : Continuous (winDelta c) := by
  unfold winDelta; fun_prop

lemma hankelWindowProfile_mul (c : ℝ) (f φ : ℝ → ℝ) (u : ℝ) :
    hankelWindowProfile c (fun Δ => f Δ * φ Δ) u =
      hankelWindowProfile c f u * φ (winDelta c u) := by
  unfold hankelWindowProfile winDelta
  dsimp only
  split_ifs <;> ring

lemma integral_window_weighted {c : ℝ} (hc : 0 < c) (f φ : ℝ → ℝ) :
    ∫ u, hankelWindowProfile c f u * φ (winDelta c u) =
      ∫ Δ in Ioi (0 : ℝ), f Δ * φ Δ * hankelRho0 c Δ := by
  have h := integral_hankelWindowProfile hc (fun Δ => f Δ * φ Δ)
  simp_rw [hankelWindowProfile_mul] at h
  exact h

lemma abs_window_weight {c y : ℝ} (hc : 0 < c) (hy : 0 ≤ y) (hζ : laplaceZeta c y < 1)
    (g : ℝ → ℝ) (u : ℝ) :
    |hankelWindowProfile c (fun Δ => |g Δ| * laplaceWeight c y Δ) u| =
      |hankelWindowProfile c g u| * laplaceWeight c y (winDelta c u) := by
  unfold hankelWindowProfile winDelta
  dsimp only
  split_ifs with h
  · have hW := laplaceWeight_pos hc hy hζ h
    have hρ := hankelRho0_pos hc h
    have ha : 0 ≤ c ^ (1 / 3 : ℝ) / hankelBeta1 :=
      div_nonneg (Real.rpow_nonneg hc.le _) hankelBeta1_pos.le
    simp only [abs_mul, abs_abs, abs_of_nonneg ha, abs_of_nonneg hW.le, abs_of_nonneg hρ.le]
    ring
  · simp

lemma tail_weighted_u {c y : ℝ} (hc : 0 < c) (hy : 0 ≤ y) (hζ : laplaceZeta c y < 1)
    (g : ℝ → ℝ) (R : ℝ) :
    ∫ u in Ioi (R * hankelBeta1), |hankelWindowProfile c g u| * laplaceWeight c y (winDelta c u) =
      ∫ Δ in Ioo 0 (c / Real.pi ^ 2 - R * c ^ (1 / 3 : ℝ)),
        |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ := by
  have h := integral_tail_abs_hankelWindowProfile hc (fun Δ => |g Δ| * laplaceWeight c y Δ) R
  calc ∫ u in Ioi (R * hankelBeta1), |hankelWindowProfile c g u| * laplaceWeight c y (winDelta c u)
      = ∫ u in Ioi (R * hankelBeta1),
          |hankelWindowProfile c (fun Δ => |g Δ| * laplaceWeight c y Δ) u| :=
        setIntegral_congr_fun measurableSet_Ioi fun u _ => (abs_window_weight hc hy hζ g u).symm
    _ = ∫ Δ in Ioo 0 (c / Real.pi ^ 2 - R * c ^ (1 / 3 : ℝ)),
          |(|g Δ| * laplaceWeight c y Δ)| * hankelRho0 c Δ := h
    _ = _ := by
        refine setIntegral_congr_fun measurableSet_Ioo fun Δ hΔ => ?_
        have hW := laplaceWeight_pos hc hy hζ hΔ.1
        simp only [abs_mul, abs_abs, abs_of_nonneg hW.le]
        ring

lemma left_tail_weighted_u {c y : ℝ} {ε : ℝ} {g : ℝ → ℝ} (hc : 0 < c) (hy : 0 ≤ y)
    (hζ : laplaceZeta c y < 1) (hg : IsHankelEigenfn c ε g) {R : ℝ} (hR : 0 ≤ R) :
    ∫ u in Iio (-(R * hankelBeta1)), |hankelWindowProfile c g u| * laplaceWeight c y (winDelta c u) ≤
      laplaceWeight c y (c / Real.pi ^ 2 + R * c ^ (1 / 3 : ℝ)) * hankelMass c g := by
  set t : ℝ := c ^ (1 / 3 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hc _
  set Q : ℝ := c / Real.pi ^ 2 + R * t with hQ
  have hQ0 : 0 < Q := by positivity
  set W₀ : ℝ := laplaceWeight c y Q with hW₀
  have hW₀0 : 0 < W₀ := laplaceWeight_pos hc hy hζ hQ0
  have hΨ : Integrable (hankelWindowProfile c g) :=
    (integrable_hankelWindowProfile_iff hc g).2 hg.int
  have hge : ∀ u ∈ Iio (-(R * hankelBeta1)), Q ≤ winDelta c u := by
    intro u hu
    have hu' : u < -(R * hankelBeta1) := hu
    have : -(u / hankelBeta1) > R := by
      rw [neg_div', gt_iff_lt, lt_div_iff₀ hankelBeta1_pos]; linarith
    unfold winDelta
    rw [← ht, hQ]
    nlinarith
  have hcont : ContinuousOn (fun u => laplaceWeight c y (winDelta c u)) (Iio (-(R * hankelBeta1))) := by
    refine (continuousOn_laplaceWeight hc hy hζ).comp (continuous_winDelta c).continuousOn ?_
    intro u hu
    exact lt_of_lt_of_le hQ0 (hge u hu)
  have hmaj : IntegrableOn (fun u => W₀ * |hankelWindowProfile c g u|) (Iio (-(R * hankelBeta1))) :=
    (hΨ.abs.const_mul W₀).integrableOn
  have hint : IntegrableOn (fun u => |hankelWindowProfile c g u| * laplaceWeight c y (winDelta c u))
      (Iio (-(R * hankelBeta1))) := by
    refine Integrable.mono' hmaj ?_ ?_
    · exact (hΨ.abs.aestronglyMeasurable.restrict).mul
        (hcont.aestronglyMeasurable measurableSet_Iio)
    · refine ae_restrict_of_forall_mem measurableSet_Iio fun u hu => ?_
      have hw := laplaceWeight_pos hc hy hζ (lt_of_lt_of_le hQ0 (hge u hu))
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hw.le)]
      have := laplaceWeight_anti hc hy hζ hQ0 (hge u hu)
      nlinarith [abs_nonneg (hankelWindowProfile c g u)]
  have hpt : ∀ u ∈ Iio (-(R * hankelBeta1)),
      |hankelWindowProfile c g u| * laplaceWeight c y (winDelta c u) ≤
        W₀ * |hankelWindowProfile c g u| := by
    intro u hu
    have := laplaceWeight_anti hc hy hζ hQ0 (hge u hu)
    nlinarith [abs_nonneg (hankelWindowProfile c g u)]
  calc ∫ u in Iio (-(R * hankelBeta1)),
        |hankelWindowProfile c g u| * laplaceWeight c y (winDelta c u)
      ≤ ∫ u in Iio (-(R * hankelBeta1)), W₀ * |hankelWindowProfile c g u| :=
        setIntegral_mono_on hint hmaj measurableSet_Iio hpt
    _ = W₀ * ∫ u in Iio (-(R * hankelBeta1)), |hankelWindowProfile c g u| := by
        rw [integral_const_mul]
    _ ≤ W₀ * ∫ u, |hankelWindowProfile c g u| := by
        refine mul_le_mul_of_nonneg_left ?_ hW₀0.le
        exact setIntegral_le_integral hΨ.abs (Eventually.of_forall fun u => abs_nonneg _)
    _ = W₀ * hankelMass c g := by rw [integral_abs_hankelWindowProfile hc]

lemma integrableOn_weighted {c y ε : ℝ} {g : ℝ → ℝ} (hc : 56 ≤ c) (hy : 0 ≤ y)
    (hζ : laplaceZeta c y ≤ 1 / 4) (hg : IsHankelEigenfn c ε g) (hε : ε = 1 ∨ ε = -1) :
    IntegrableOn (fun Δ => g Δ * laplaceWeight c y Δ * hankelRho0 c Δ) (Ioi 0) := by
  have hc0 : 0 < c := by linarith
  have hζ1 : laplaceZeta c y < 1 := by linarith
  set Δ₁ : ℝ := c * (1 / Real.pi ^ 2 - 1 / 48) with hΔ₁
  have hΔ₁pos : 0 < Δ₁ := Delta1_pos hc0
  have hcont : ContinuousOn (fun Δ => g Δ * laplaceWeight c y Δ * hankelRho0 c Δ) (Ioi 0) :=
    ((hg.cont.mono Ioi_subset_Ici_self).mul (continuousOn_laplaceWeight hc0 hy hζ1)).mul
      (continuousOn_hankelRho0 c)
  rw [← Ioc_union_Ioi_eq_Ioi hΔ₁pos.le]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (regionII_weighted hc hy hζ hg hε).1
      (hcont.mono Ioc_subset_Ioi_self |>.aestronglyMeasurable measurableSet_Ioc) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun Δ hΔ => ?_
    have hW := laplaceWeight_pos hc0 hy hζ1 hΔ.1
    have hρ := hankelRho0_nonneg hc0 hΔ.1.le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hW.le, abs_of_nonneg hρ]
    exact le_of_eq (by ring)
  · have h0 := hg.int.norm.const_mul (laplaceWeight c y Δ₁)
    have hmaj : IntegrableOn (fun Δ => laplaceWeight c y Δ₁ * |g Δ * hankelRho0 c Δ|) (Ioi Δ₁) :=
      Integrable.mono_measure h0 (Measure.restrict_mono (Ioi_subset_Ioi hΔ₁pos.le) le_rfl)
    refine Integrable.mono' hmaj
      (hcont.mono (Ioi_subset_Ioi hΔ₁pos.le) |>.aestronglyMeasurable measurableSet_Ioi) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun Δ hΔ => ?_
    have hΔ0 : 0 < Δ := lt_trans hΔ₁pos hΔ
    have hW := laplaceWeight_pos hc0 hy hζ1 hΔ0
    have hle := laplaceWeight_anti hc0 hy hζ1 hΔ₁pos (le_of_lt hΔ)
    rw [Real.norm_eq_abs, show g Δ * laplaceWeight c y Δ * hankelRho0 c Δ =
      (g Δ * hankelRho0 c Δ) * laplaceWeight c y Δ by ring, abs_mul, abs_of_nonneg hW.le]
    nlinarith [abs_nonneg (g Δ * hankelRho0 c Δ)]

lemma integrable_weighted_window {c y ε : ℝ} {g : ℝ → ℝ} (hc : 56 ≤ c) (hy : 0 ≤ y)
    (hζ : laplaceZeta c y ≤ 1 / 4) (hg : IsHankelEigenfn c ε g) (hε : ε = 1 ∨ ε = -1) :
    Integrable (fun u => hankelWindowProfile c g u * laplaceWeight c y (winDelta c u)) := by
  have hc0 : 0 < c := by linarith
  have h := (integrable_hankelWindowProfile_iff hc0 (fun Δ => g Δ * laplaceWeight c y Δ)).2
    (integrableOn_weighted hc hy hζ hg hε)
  refine h.congr (Eventually.of_forall fun u => ?_)
  exact hankelWindowProfile_mul c g (laplaceWeight c y) u

/-! ### Convergence of integrals with uniform tail control -/

lemma setIntegral_Icc_tendsto_unif {g : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
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

lemma exists_compl_small {a : ℝ → ℝ} (ha : Integrable a) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∫ u in (Icc (-R) R)ᶜ, |a u| ≤ δ := by
  have hmono : Monotone (fun n : ℕ => Icc (-(n : ℝ)) n) := fun m n hmn =>
    Icc_subset_Icc (neg_le_neg (by exact_mod_cast hmn)) (by exact_mod_cast hmn)
  have hU : (⋃ n : ℕ, Icc (-(n : ℝ)) n) = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact mem_iUnion.2 ⟨n, abs_le.mp hn⟩
  have ht := tendsto_setIntegral_of_monotone (μ := volume) (f := fun u => |a u|)
    (fun n => measurableSet_Icc) hmono (by rw [hU]; exact ha.abs.integrableOn)
  rw [hU, Measure.restrict_univ] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (Ioi_mem_nhds
    (by linarith [show (∫ u, |a u|) - δ < ∫ u, |a u| by linarith] :
      (∫ u, |a u|) - δ < ∫ u, |a u|))).exists
  refine ⟨n, by positivity, ?_⟩
  have hsplit := integral_add_compl (μ := volume) (measurableSet_Icc (a := -(n : ℝ)) (b := n)) ha.abs
  have hn' : (∫ u, |a u|) - δ < ∫ u in Icc (-(n : ℝ)) n, |a u| := hn
  linarith

lemma tendsto_integral_of_tails {A : ℕ → ℝ → ℝ} {a : ℝ → ℝ}
    (hA : ∀ᶠ k in atTop, Integrable (A k)) (ha : Integrable a)
    (hloc : ∀ R : ℝ, TendstoUniformlyOn A a atTop (Icc (-R) R))
    (htail : ∀ δ > 0, ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ k in atTop, ∫ u in (Icc (-R) R)ᶜ, |A k u| ≤ δ) :
    Tendsto (fun k => ∫ u, A k u) atTop (𝓝 (∫ u, a u)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / 4 := by positivity
  obtain ⟨R₁, hR₁, hA₁⟩ := htail (ε / 4) hδ
  obtain ⟨R₂, hR₂, ha₂⟩ := exists_compl_small ha hδ
  set R : ℝ := max R₁ R₂ with hR
  have hR0 : 0 ≤ R := le_trans hR₁ (le_max_left _ _)
  have hsubA : (Icc (-R) R)ᶜ ⊆ (Icc (-R₁) R₁)ᶜ := by
    intro x hx hx'
    exact hx ⟨le_trans (neg_le_neg (le_max_left _ _)) hx'.1, le_trans hx'.2 (le_max_left _ _)⟩
  have hsuba : (Icc (-R) R)ᶜ ⊆ (Icc (-R₂) R₂)ᶜ := by
    intro x hx hx'
    exact hx ⟨le_trans (neg_le_neg (le_max_right _ _)) hx'.1, le_trans hx'.2 (le_max_right _ _)⟩
  have haR : ∫ u in (Icc (-R) R)ᶜ, |a u| ≤ ε / 4 :=
    le_trans (setIntegral_mono_set ha.abs.integrableOn (Eventually.of_forall fun u => abs_nonneg _)
      hsubA.eventuallyLE |> fun h => by
        exact le_trans (setIntegral_mono_set ha.abs.integrableOn
          (Eventually.of_forall fun u => abs_nonneg _) hsuba.eventuallyLE) ha₂) le_rfl
  have hcI := setIntegral_Icc_tendsto_unif (by linarith : -R ≤ R) (hloc R)
    (hA.mono fun k hk => hk.integrableOn) ha.integrableOn
  rw [Metric.tendsto_nhds] at hcI
  filter_upwards [hA, hA₁, hcI (ε / 4) hδ] with k hk hk1 hk2
  have hkR : ∫ u in (Icc (-R) R)ᶜ, |A k u| ≤ ε / 4 :=
    le_trans (setIntegral_mono_set hk.abs.integrableOn (Eventually.of_forall fun u => abs_nonneg _)
      hsubA.eventuallyLE) hk1
  have e1 := integral_add_compl (μ := volume) (measurableSet_Icc (a := -R) (b := R)) hk
  have e2 := integral_add_compl (μ := volume) (measurableSet_Icc (a := -R) (b := R)) ha
  have t1 : |∫ u in (Icc (-R) R)ᶜ, A k u| ≤ ε / 4 :=
    le_trans (by simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict (Icc (-R) R)ᶜ) (A k)) hkR
  have t2 : |∫ u in (Icc (-R) R)ᶜ, a u| ≤ ε / 4 :=
    le_trans (by simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict (Icc (-R) R)ᶜ) a) haR
  rw [Real.dist_eq] at hk2 ⊢
  rw [← e1, ← e2]
  have := abs_le.mp t1
  have := abs_le.mp t2
  have := abs_lt.mp hk2
  rw [abs_lt]
  constructor <;> linarith

lemma tendstoUniformlyOn_mul_real {s : Set ℝ} {F F' : ℕ → ℝ → ℝ} {f f' : ℝ → ℝ}
    (hF : TendstoUniformlyOn F f atTop s) (hF' : TendstoUniformlyOn F' f' atTop s)
    (hfb : ∃ B, ∀ x ∈ s, |f x| ≤ B) (hf'b : ∃ B, ∀ x ∈ s, |f' x| ≤ B) :
    TendstoUniformlyOn (fun k x => F k x * F' k x) (fun x => f x * f' x) atTop s := by
  obtain ⟨B₁, hB₁⟩ := hfb
  obtain ⟨B₂, hB₂⟩ := hf'b
  set B : ℝ := max B₁ B₂ with hB
  have hB1 : ∀ x ∈ s, |f x| ≤ B := fun x hx => (hB₁ x hx).trans (le_max_left _ _)
  have hB2 : ∀ x ∈ s, |f' x| ≤ B := fun x hx => (hB₂ x hx).trans (le_max_right _ _)
  have hBnn : ∀ x ∈ s, 0 ≤ B := fun x hx => (abs_nonneg _).trans (hB1 x hx)
  rw [Metric.tendstoUniformlyOn_iff] at hF hF' ⊢
  intro ε hε
  set δ : ℝ := min 1 (ε / (2 * |B| + 3)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  filter_upwards [hF δ hδ0, hF' δ hδ0] with k h1 h2 x hx
  have e1 := h1 x hx
  have e2 := h2 x hx
  rw [Real.dist_eq] at e1 e2 ⊢
  have hBa : B ≤ |B| := le_abs_self B
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε / (2 * |B| + 3) := min_le_right _ _
  have hF'b : |F' k x| ≤ B + 1 := by
    have := abs_sub (f' x) (f' x - F' k x)
    rw [sub_sub_cancel] at this
    linarith [hB2 x hx]
  have key : f x * f' x - F k x * F' k x =
      (f x - F k x) * F' k x + f x * (f' x - F' k x) := by ring
  rw [key]
  have hpos : 0 < 2 * |B| + 3 := by positivity
  have hfin : δ * (2 * |B| + 3) ≤ ε := by
    calc δ * (2 * |B| + 3) ≤ ε / (2 * |B| + 3) * (2 * |B| + 3) :=
          mul_le_mul_of_nonneg_right hδ2 hpos.le
      _ = ε := by field_simp
  calc |(f x - F k x) * F' k x + f x * (f' x - F' k x)|
      ≤ |(f x - F k x) * F' k x| + |f x * (f' x - F' k x)| := abs_add_le _ _
    _ = |f x - F k x| * |F' k x| + |f x| * |f' x - F' k x| := by rw [abs_mul, abs_mul]
    _ ≤ δ * (B + 1) + B * δ :=
        add_le_add (mul_le_mul e1.le hF'b (abs_nonneg _) hδ0.le)
          (mul_le_mul (hB1 x hx) e2.le (abs_nonneg _) (hBnn x hx))
    _ < ε := by nlinarith [hδ0, hBa]

/-! ### The Laplace limit -/

lemma window_ne_zero_pos {c : ℝ} {g : ℝ → ℝ} {u : ℝ} (h : hankelWindowProfile c g u ≠ 0) :
    0 < winDelta c u := by
  by_contra hneg
  apply h
  unfold hankelWindowProfile
  rw [if_neg]
  exact hneg

lemma abs_window_div_weight {c y μ : ℝ} (hc : 0 < c) (hy : 0 ≤ y) (hζ : laplaceZeta c y < 1)
    (hμ : 0 < μ) (g : ℝ → ℝ) (u : ℝ) :
    |hankelWindowProfile c g u / μ * laplaceWeight c y (winDelta c u)| =
      |hankelWindowProfile c g u| * laplaceWeight c y (winDelta c u) / μ := by
  by_cases h0 : hankelWindowProfile c g u = 0
  · simp [h0]
  · have hW := laplaceWeight_pos hc hy hζ (window_ne_zero_pos h0)
    rw [abs_mul, abs_div, abs_of_pos hμ, abs_of_pos hW]
    ring

lemma tendstoLocallyUniformly_weight {c : ℕ → ℝ} (hc : Tendsto c atTop atTop) (y : ℝ) :
    TendstoLocallyUniformly (fun k u => laplaceWeight (c k) y (winDelta (c k) u))
      (fun u => Real.exp (-(y ^ 3) / 12 + y * u)) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro x
  have h := laplaceWeight_tendsto (l := (atTop : Filter ℕ) ×ˢ 𝓝 x) (c := fun p : ℕ × ℝ => c p.1)
    (u := fun p => p.2) (u₀ := x) y (hc.comp Filter.tendsto_fst) Filter.tendsto_snd
  have hw : Tendsto (fun p : ℕ × ℝ => Real.exp (-(y ^ 3) / 12 + y * p.2))
      ((atTop : Filter ℕ) ×ˢ 𝓝 x) (𝓝 (Real.exp (-(y ^ 3) / 12 + y * x))) :=
    (((Real.continuous_exp.comp (by fun_prop : Continuous fun u : ℝ => -(y ^ 3) / 12 + y * u)).tendsto
      x).comp Filter.tendsto_snd)
  rw [tendsto_uniformity_iff_dist_tendsto_zero]
  have := hw.dist h
  rw [dist_self] at this
  exact this

theorem laplace_limit {c : ℕ → ℝ} (hc : Tendsto c atTop atTop) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {g : ℕ → ℝ → ℝ} (hg : ∀ k, IsHankelEigenfn (c k) ε (g k))
    {μ : ℕ → ℝ} (hμ : ∀ k, 0 < μ k) {B : ℝ} (hB : ∀ k, hankelMass (c k) (g k) ≤ B * μ k)
    {G : ℝ → ℝ} (hGc : Continuous G)
    (hloc : TendstoLocallyUniformlyOn
      (fun k u => hankelWindowProfile (c k) (g k) u / μ k) G atTop univ)
    {y : ℝ} (hy : 0 < y) (hGi : Integrable (fun u => G u * Real.exp (y * u))) :
    Tendsto (fun k => (∫ Δ in Ioi (0 : ℝ), g k Δ * hankelRho0 (c k) Δ * laplaceWeight (c k) y Δ) / μ k)
      atTop (𝓝 (∫ u, G u * Real.exp (-(y ^ 3) / 12 + y * u))) := by
  have hy0 : 0 ≤ y := hy.le
  have e56 : ∀ᶠ k in atTop, 56 ≤ c k := hc.eventually_ge_atTop 56
  have eζ : ∀ᶠ k in atTop, laplaceZeta (c k) y ≤ 1 / 4 :=
    ((tendsto_laplaceZeta y).comp hc).eventually (Iic_mem_nhds (by norm_num))
  set A : ℕ → ℝ → ℝ := fun k u =>
    hankelWindowProfile (c k) (g k) u / μ k * laplaceWeight (c k) y (winDelta (c k) u) with hA
  set a : ℝ → ℝ := fun u => G u * Real.exp (-(y ^ 3) / 12 + y * u) with ha
  -- the identity with the window integral
  have hid : ∀ᶠ k in atTop,
      (∫ Δ in Ioi (0 : ℝ), g k Δ * hankelRho0 (c k) Δ * laplaceWeight (c k) y Δ) / μ k =
        ∫ u, A k u := by
    filter_upwards [e56] with k hk
    have hc0 : 0 < c k := by linarith
    have h1 := integral_window_weighted hc0 (g k) (laplaceWeight (c k) y)
    have h2 : ∫ u, A k u = (∫ u, hankelWindowProfile (c k) (g k) u *
        laplaceWeight (c k) y (winDelta (c k) u)) / μ k := by
      rw [← integral_div]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only [hA]; ring
    rw [h2, h1]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun Δ _ => ?_
    ring
  have hAint : ∀ᶠ k in atTop, Integrable (A k) := by
    filter_upwards [e56, eζ] with k hk hζk
    have := (integrable_weighted_window hk hy0 hζk (hg k) hε).div_const (μ k)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [hA]; ring
  have haint : Integrable a := by
    have := hGi.const_mul (Real.exp (-(y ^ 3) / 12))
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [ha]; rw [Real.exp_add]; ring
  have hΦ : ∀ R : ℝ, TendstoUniformlyOn (fun k u => hankelWindowProfile (c k) (g k) u / μ k) G
      atTop (Icc (-R) R) := fun R =>
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
      (hloc.mono (subset_univ _))
  have hW : ∀ R : ℝ, TendstoUniformlyOn (fun k u => laplaceWeight (c k) y (winDelta (c k) u))
      (fun u => Real.exp (-(y ^ 3) / 12 + y * u)) atTop (Icc (-R) R) := fun R =>
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
      ((tendstoLocallyUniformly_weight hc y).tendstoLocallyUniformlyOn.mono (subset_univ _))
  have hloc' : ∀ R : ℝ, TendstoUniformlyOn A a atTop (Icc (-R) R) := by
    intro R
    refine tendstoUniformlyOn_mul_real (hΦ R) (hW R) ?_ ?_
    · obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (f := G) (s := Icc (-R) R) hGc.continuousOn
      exact ⟨C, fun x hx => by simpa using hC x hx⟩
    · obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (f := fun u : ℝ => Real.exp (-(y ^ 3) / 12 + y * u)) (s := Icc (-R) R)
        (Real.continuous_exp.comp (by fun_prop)).continuousOn
      exact ⟨C, fun x hx => by simpa using hC x hx⟩
  have htail : ∀ δ > 0, ∃ R : ℝ, 0 ≤ R ∧
      ∀ᶠ k in atTop, ∫ u in (Icc (-R) R)ᶜ, |A k u| ≤ δ := by
    intro δ hδ
    set B' : ℝ := max B 1 with hB'
    have hB'pos : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hBB' : B ≤ B' := le_max_left _ _
    set η : ℝ := δ / (4 * B') with hη
    have hηpos : 0 < η := by positivity
    have hex : ∃ R' : ℝ, max 0 (regionIThreshold y) ≤ R' ∧ 16 * Real.exp (-(10 * R')) ≤ η ∧
        2 * Real.exp (-(y * hankelBeta1 * R')) ≤ η := by
      have t1 : Tendsto (fun R : ℝ => 16 * Real.exp (-(10 * R))) atTop (𝓝 0) := by
        have := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
          (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 10)))).const_mul 16
        simpa using this
      have t2 : Tendsto (fun R : ℝ => 2 * Real.exp (-(y * hankelBeta1 * R))) atTop (𝓝 0) := by
        have := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
          (tendsto_id.const_mul_atTop (by have := hankelBeta1_pos; positivity :
            (0 : ℝ) < y * hankelBeta1)))).const_mul 2
        simpa using this
      obtain ⟨R', h1, h2, h3⟩ := ((eventually_ge_atTop (max 0 (regionIThreshold y))).and
        ((t1.eventually (Iic_mem_nhds hηpos)).and (t2.eventually (Iic_mem_nhds hηpos)))).exists
      exact ⟨R', h1, h2, h3⟩
    obtain ⟨R', hR'1, hR'2, hR'3⟩ := hex
    have hR'0 : 0 ≤ R' := le_trans (le_max_left _ _) hR'1
    have hR'T : regionIThreshold y ≤ R' := le_trans (le_max_right _ _) hR'1
    refine ⟨R' * hankelBeta1, by have := hankelBeta1_pos; positivity, ?_⟩
    obtain ⟨c₁, hc₁⟩ := right_tail_weighted hy0 hηpos
    have eR : ∀ᶠ k in atTop, c₁ ≤ c k := hc.eventually_ge_atTop c₁
    have eL : ∀ᶠ k in atTop, laplaceWeight (c k) y (c k / Real.pi ^ 2 + R' * (c k) ^ (1 / 3 : ℝ)) ≤
        η := by
      have h := laplaceWeight_tendsto_const y (-(hankelBeta1 * R'))
      have e : ∀ c : ℝ, c / Real.pi ^ 2 - (-(hankelBeta1 * R') / hankelBeta1) * c ^ (1 / 3 : ℝ) =
          c / Real.pi ^ 2 + R' * c ^ (1 / 3 : ℝ) := fun c => by
        have := hankelBeta1_pos.ne'
        field_simp
        ring
      have h2 : Tendsto (fun c : ℝ => laplaceWeight c y (c / Real.pi ^ 2 + R' * c ^ (1 / 3 : ℝ)))
          atTop (𝓝 (Real.exp (-(y ^ 3) / 12 + y * (-(hankelBeta1 * R'))))) :=
        h.congr (fun c => by rw [e c])
      have hlt : Real.exp (-(y ^ 3) / 12 + y * (-(hankelBeta1 * R'))) < η := by
        have h1 : Real.exp (-(y ^ 3) / 12 + y * (-(hankelBeta1 * R'))) ≤
            Real.exp (-(y * hankelBeta1 * R')) := by
          refine Real.exp_le_exp.mpr ?_
          have : 0 ≤ y ^ 3 := by positivity
          nlinarith
        have h3 : 0 < Real.exp (-(y * hankelBeta1 * R')) := Real.exp_pos _
        linarith
      exact ((h2.comp hc).eventually (gt_mem_nhds hlt)).mono fun k hk => hk.le
    filter_upwards [eR, eL, e56, eζ, hAint] with k hkR hkL hk56 hkζ hkA
    have hc0 : 0 < c k := by linarith
    have hζ1 : laplaceZeta (c k) y < 1 := by linarith
    have hμk := hμ k
    have hmass := hB k
    have hmass0 := hankelMass_nonneg hc0 (g k)
    have hcompl : (Icc (-(R' * hankelBeta1)) (R' * hankelBeta1))ᶜ =
        Iio (-(R' * hankelBeta1)) ∪ Ioi (R' * hankelBeta1) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
        not_and_or, not_le]
    have hRb : 0 ≤ R' * hankelBeta1 := by have := hankelBeta1_pos; positivity
    have habs : ∀ u, |A k u| =
        |hankelWindowProfile (c k) (g k) u| * laplaceWeight (c k) y (winDelta (c k) u) / μ k :=
      fun u => abs_window_div_weight hc0 hy0 hζ1 hμk (g k) u
    have hdisj : Disjoint (Iio (-(R' * hankelBeta1))) (Ioi (R' * hankelBeta1)) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      have h1 : x < -(R' * hankelBeta1) := hx
      have h2 : R' * hankelBeta1 < x := hx'
      linarith
    rw [hcompl, setIntegral_union hdisj measurableSet_Ioi hkA.abs.integrableOn hkA.abs.integrableOn]
    have hL : ∫ u in Iio (-(R' * hankelBeta1)), |A k u| ≤ η * B' := by
      simp_rw [habs]
      rw [integral_div]
      have := left_tail_weighted_u hc0 hy0 hζ1 (hg k) hR'0
      rw [div_le_iff₀ hμk]
      calc _ ≤ laplaceWeight (c k) y (c k / Real.pi ^ 2 + R' * (c k) ^ (1 / 3 : ℝ)) *
            hankelMass (c k) (g k) := this
        _ ≤ η * (B' * μ k) := by
            refine mul_le_mul hkL (hmass.trans (mul_le_mul_of_nonneg_right hBB' hμk.le))
              hmass0 hηpos.le
        _ = η * B' * μ k := by ring
    have hR : ∫ u in Ioi (R' * hankelBeta1), |A k u| ≤ 2 * η * B' := by
      simp_rw [habs]
      rw [integral_div, tail_weighted_u hc0 hy0 hζ1 (g k) R']
      obtain ⟨_, hbound⟩ := hc₁ (c k) hkR ε (g k) R' hε (hg k) hR'T
      rw [div_le_iff₀ hμk]
      calc _ ≤ hankelMass (c k) (g k) * (16 * Real.exp (-(10 * R')) + η) := hbound
        _ ≤ (B' * μ k) * (η + η) := by
            refine mul_le_mul (hmass.trans (mul_le_mul_of_nonneg_right hBB' hμk.le)) ?_
              (by positivity) (by positivity)
            linarith
        _ = 2 * η * B' * μ k := by ring
    have : 3 * η * B' = 3 * δ / 4 := by rw [hη]; field_simp
    nlinarith
  have hmain := tendsto_integral_of_tails hAint haint hloc' htail
  exact hmain.congr' (hid.mono fun k hk => hk.symm)

end FormalResearch.SignUncertainty
