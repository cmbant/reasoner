module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Qualitative mass transfer under local convergence (`lem:qual-compact`)

Source: `CFT/sign_uncertainty/paper/airy_extremal.tex`, `lem:qual-compact` (Paper I), shared by the fold-tip
blow-up and the Cohn-Elkies shell transfers (`thm:ce-physical-profile`, `thm:ce-shell-gap`), and recalled in
Paper II as `dsl:compact-mass`.

* `qual_compact` (any measure space with a measurable exhaustion `K n ↑ X`): integrable `F_j` with
  `‖F_j‖₁ = 1`, `limsup ∫ F_j ≤ 0`, local `L¹` convergence `F_j → G` on every `K n` and tight negative parts give
  `G ∈ L¹`, `‖G‖₁ ≤ 1`, `∫ G ≤ 0`, `∫ G₋ ≥ 1/2`; and `∫ G = 0` forces `‖G‖₁ = 1` and `F_j → G` in `L¹`.
* `qual_compact_real` (`ℝ`, `K n = [-n, n]`): the tightness hypothesis is replaced by the ray hypotheses of the
  paper (`F_j ≥ 0` on every fixed half line `(-∞, a]`, `a < v`, for large `j`, and a uniform tail bound), and
  for continuous `G` the ray sign `G ≥ 0` on `(-∞, v]` and `∫_v^∞ G₋ ≥ 1/2` are added.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace FormalResearch.Analysis

section General

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Local `L¹` convergence passes through a `1`-Lipschitz map. -/
lemma tendsto_setIntegral_lip {s : Set X} {φ : ℝ → ℝ} (hφ : ∀ x y, |φ x - φ y| ≤ |x - y|)
    {F : ℕ → X → ℝ} {G : X → ℝ}
    (hφF : ∀ j, IntegrableOn (fun x => φ (F j x)) s μ) (hφG : IntegrableOn (fun x => φ (G x)) s μ)
    (hF : ∀ j, IntegrableOn (F j) s μ) (hG : IntegrableOn G s μ)
    (hloc : Tendsto (fun j => ∫ x in s, |F j x - G x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x in s, φ (F j x) ∂μ) atTop (𝓝 (∫ x in s, φ (G x) ∂μ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hloc
  rw [← integral_sub (hφF j) hφG]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine setIntegral_mono ((hφF j).sub hφG).norm ((hF j).sub hG).norm fun x => ?_
  simpa [Real.norm_eq_abs] using hφ (F j x) (G x)

lemma abs_sub_abs_le' : ∀ x y : ℝ, abs (abs x - abs y) ≤ |x - y| := fun x y => abs_abs_sub_abs_le_abs_sub x y

lemma pos_part_lip : ∀ x y : ℝ, |max x 0 - max y 0| ≤ |x - y| := fun x y => abs_max_sub_max_le_abs x y 0

lemma neg_part_lip : ∀ x y : ℝ, |max (-x) 0 - max (-y) 0| ≤ |x - y| := fun x y => by
  have := abs_max_sub_max_le_abs (-x) (-y) 0
  rwa [show -x - -y = -(x - y) by ring, abs_neg] at this

lemma integral_pos_part_eq {f : X → ℝ} (hf : Integrable f μ) :
    ∫ x, max (f x) 0 ∂μ = ((∫ x, |f x| ∂μ) + ∫ x, f x ∂μ) / 2 := by
  rw [← integral_add hf.abs hf, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rcases le_total 0 (f x) with h | h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right h, abs_of_nonpos h]; ring

lemma integral_neg_part_eq {f : X → ℝ} (hf : Integrable f μ) :
    ∫ x, max (-f x) 0 ∂μ = ((∫ x, |f x| ∂μ) - ∫ x, f x ∂μ) / 2 := by
  rw [← integral_sub hf.abs hf, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rcases le_total 0 (f x) with h | h
  · rw [max_eq_right (by linarith), abs_of_nonneg h]; ring
  · rw [max_eq_left (by linarith), abs_of_nonpos h]; ring

/-- **Lemma `lem:qual-compact`** (qualitative mass transfer under local convergence).
Let `F_j` be integrable with `∫ |F_j| = 1` and `limsup_j ∫ F_j ≤ 0`, let `K n` be a measurable exhaustion
(`K n` monotone with union `X`), let `G` be integrable on every `K n` and `F_j → G` in `L¹(K n)` for each `n`,
and let the negative parts be tight: for every `η > 0` there is `n` with `∫_{(K n)ᶜ} (F_j)₋ ≤ η` for large `j`.
Then `G ∈ L¹`, `‖G‖₁ ≤ 1`, `∫ G ≤ 0`, `∫ G₋ ≥ 1/2`; if `∫ G = 0` then `‖G‖₁ = 1` and `F_j → G` in `L¹`.
(Proved.) -/
theorem qual_compact {F : ℕ → X → ℝ} {G : X → ℝ} {K : ℕ → Set X}
    (hKm : ∀ n, MeasurableSet (K n)) (hKmono : Monotone K) (hKU : ⋃ n, K n = univ)
    (hFi : ∀ j, Integrable (F j) μ) (hGi : ∀ n, IntegrableOn G (K n) μ)
    (hnorm : ∀ j, ∫ x, |F j x| ∂μ = 1)
    (hmass : ∀ ε > 0, ∀ᶠ j in atTop, ∫ x, F j x ∂μ ≤ ε)
    (hloc : ∀ n, Tendsto (fun j => ∫ x in K n, |F j x - G x| ∂μ) atTop (𝓝 0))
    (htight : ∀ η > 0, ∃ n, ∀ᶠ j in atTop, ∫ x in (K n)ᶜ, max (-F j x) 0 ∂μ ≤ η) :
    Integrable G μ ∧ ∫ x, |G x| ∂μ ≤ 1 ∧ ∫ x, G x ∂μ ≤ 0 ∧ 1 / 2 ≤ ∫ x, max (-G x) 0 ∂μ ∧
      (∫ x, G x ∂μ = 0 → ∫ x, |G x| ∂μ = 1 ∧
        Tendsto (fun j => ∫ x, |F j x - G x| ∂μ) atTop (𝓝 0)) := by
  have hFK : ∀ n j, IntegrableOn (F j) (K n) μ := fun n j => (hFi j).integrableOn
  -- local convergence of the three parts
  have hA : ∀ n, Tendsto (fun j => ∫ x in K n, |F j x| ∂μ) atTop (𝓝 (∫ x in K n, |G x| ∂μ)) :=
    fun n => tendsto_setIntegral_lip (φ := fun t => |t|) abs_sub_abs_le'
      (fun j => (hFi j).abs.integrableOn) (hGi n).abs (hFK n) (hGi n) (hloc n)
  have hP : ∀ n, Tendsto (fun j => ∫ x in K n, max (F j x) 0 ∂μ) atTop
      (𝓝 (∫ x in K n, max (G x) 0 ∂μ)) :=
    fun n => tendsto_setIntegral_lip (φ := fun t => max t 0) pos_part_lip
      (fun j => (hFi j).pos_part.integrableOn) (hGi n).pos_part (hFK n) (hGi n) (hloc n)
  have hN : ∀ n, Tendsto (fun j => ∫ x in K n, max (-F j x) 0 ∂μ) atTop
      (𝓝 (∫ x in K n, max (-G x) 0 ∂μ)) :=
    fun n => tendsto_setIntegral_lip (φ := fun t => max (-t) 0) neg_part_lip
      (fun j => (hFi j).neg_part.integrableOn) (hGi n).neg_part (hFK n) (hGi n) (hloc n)
  -- `G` is integrable
  have hGabs_le : ∀ n, ∫ x in K n, |G x| ∂μ ≤ 1 := fun n =>
    le_of_tendsto (hA n) (Eventually.of_forall fun j => by
      rw [← hnorm j]
      exact setIntegral_le_integral (hFi j).abs (Eventually.of_forall fun x => abs_nonneg _))
  have hGint : Integrable G μ := by
    refine ⟨?_, ?_⟩
    · have h : AEStronglyMeasurable G (μ.restrict (⋃ n, K n)) :=
        aestronglyMeasurable_iUnion_iff.2 fun n => (hGi n).aestronglyMeasurable
      rwa [hKU, Measure.restrict_univ] at h
    · rw [hasFiniteIntegral_iff_eNorm]
      calc ∫⁻ x, ‖G x‖ₑ ∂μ = ∫⁻ x in ⋃ n, K n, ‖G x‖ₑ ∂μ := by rw [hKU, Measure.restrict_univ]
        _ = ⨆ n, ∫⁻ x in K n, ‖G x‖ₑ ∂μ := setLIntegral_iUnion_of_directed _ hKmono.directed_le
        _ ≤ ENNReal.ofReal 1 := iSup_le fun n => by
            rw [← ofReal_integral_norm_eq_lintegral_eNorm (hGi n)]
            exact ENNReal.ofReal_le_ofReal (by simpa using hGabs_le n)
        _ < ⊤ := ENNReal.ofReal_lt_top
  have hlim : ∀ f : X → ℝ, Integrable f μ →
      Tendsto (fun n => ∫ x in K n, f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := fun f hf => by
    have h := tendsto_setIntegral_of_monotone (μ := μ) (f := f) hKm hKmono
      (by rw [hKU]; exact hf.integrableOn)
    rwa [hKU, Measure.restrict_univ] at h
  have hGabs : ∫ x, |G x| ∂μ ≤ 1 :=
    le_of_tendsto (hlim _ hGint.abs) (Eventually.of_forall hGabs_le)
  -- `∫ G₊ ≤ 1/2`
  have hGpos : ∫ x, max (G x) 0 ∂μ ≤ 1 / 2 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    refine le_of_tendsto (hlim _ hGint.pos_part) (Eventually.of_forall fun n => ?_)
    refine le_of_tendsto (hP n) ?_
    filter_upwards [hmass ε hε] with j hj
    calc ∫ x in K n, max (F j x) 0 ∂μ ≤ ∫ x, max (F j x) 0 ∂μ :=
          setIntegral_le_integral (hFi j).pos_part (Eventually.of_forall fun x => le_max_right _ _)
      _ = (1 + ∫ x, F j x ∂μ) / 2 := by rw [integral_pos_part_eq (hFi j), hnorm j]
      _ ≤ 1 / 2 + ε := by linarith
  -- `∫ G₋ ≥ 1/2`
  have hGneg : 1 / 2 ≤ ∫ x, max (-G x) 0 ∂μ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := htight (ε / 2) (by positivity)
    have h1 : 1 / 2 - ε ≤ ∫ x in K n, max (-G x) 0 ∂μ := by
      refine ge_of_tendsto (hN n) ?_
      filter_upwards [hn, hmass ε hε] with j hj hj'
      have hs := integral_add_compl (hKm n) (hFi j).neg_part
      rw [integral_neg_part_eq (hFi j), hnorm j] at hs
      linarith
    have h2 : ∫ x in K n, max (-G x) 0 ∂μ ≤ ∫ x, max (-G x) 0 ∂μ :=
      setIntegral_le_integral hGint.neg_part (Eventually.of_forall fun x => le_max_right _ _)
    linarith
  have hsplit : ∫ x, G x ∂μ = ∫ x, max (G x) 0 ∂μ - ∫ x, max (-G x) 0 ∂μ := by
    rw [← integral_sub hGint.pos_part hGint.neg_part]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rcases le_total 0 (G x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have habs_split : ∫ x, |G x| ∂μ = ∫ x, max (G x) 0 ∂μ + ∫ x, max (-G x) 0 ∂μ := by
    rw [← integral_add hGint.pos_part hGint.neg_part]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rcases le_total 0 (G x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring
    · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring
  refine ⟨hGint, hGabs, by linarith, hGneg, fun h0 => ?_⟩
  have habs1 : ∫ x, |G x| ∂μ = 1 := by linarith
  refine ⟨habs1, ?_⟩
  -- `L¹` convergence
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := ((hlim _ hGint.abs).eventually (Ioi_mem_nhds (show 1 - ε / 4 < ∫ x, |G x| ∂μ by
    linarith))).exists
  have hn' : 1 - ε / 4 < ∫ x in K n, |G x| ∂μ := hn
  filter_upwards [(hloc n).eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity)),
    (hA n).eventually (Ioi_mem_nhds (show (∫ x in K n, |G x| ∂μ) - ε / 4 <
      ∫ x in K n, |G x| ∂μ by linarith))] with j h1 h2
  have h2' : (∫ x in K n, |G x| ∂μ) - ε / 4 < ∫ x in K n, |F j x| ∂μ := h2
  have hint : Integrable (fun x => |F j x - G x|) μ := ((hFi j).sub hGint).abs
  have hs := integral_add_compl (hKm n) hint
  have hF1 := integral_add_compl (hKm n) (hFi j).abs
  have hG1 := integral_add_compl (hKm n) hGint.abs
  have hle : ∫ x in (K n)ᶜ, |F j x - G x| ∂μ ≤
      (∫ x in (K n)ᶜ, |F j x| ∂μ) + ∫ x in (K n)ᶜ, |G x| ∂μ := by
    rw [← integral_add (hFi j).abs.integrableOn hGint.abs.integrableOn]
    refine setIntegral_mono hint.integrableOn ((hFi j).abs.integrableOn.add hGint.abs.integrableOn)
      fun x => ?_
    simpa using abs_sub (F j x) (G x)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun x => abs_nonneg _)]
  rw [hnorm j] at hF1
  linarith

end General

/-! ### The real line -/

section Real

/-- **`lem:qual-compact` on `ℝ`** (Lebesgue measure, exhaustion `[-n, n]`): the tightness hypothesis is the ray
condition of the paper, namely `F_j ≥ 0` on every fixed half line `(-∞, a]`, `a < v`, for large `j`, together with
the uniform tail bound `lim_{b → ∞} limsup_j ∫_b^∞ |F_j| = 0` (`eq:qual-compact-tight`). For continuous `G`
the ray sign passes to `G`: `G ≥ 0` on `(-∞, v]` and `∫_v^∞ G₋ ≥ 1/2`. (Proved.) -/
theorem qual_compact_real {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {v : ℝ}
    (hFi : ∀ j, Integrable (F j)) (hGi : ∀ n : ℕ, IntegrableOn G (Icc (-(n : ℝ)) n))
    (hnorm : ∀ j, ∫ x, |F j x| = 1)
    (hmass : ∀ ε > 0, ∀ᶠ j in atTop, ∫ x, F j x ≤ ε)
    (hloc : ∀ n : ℕ, Tendsto (fun j => ∫ x in Icc (-(n : ℝ)) n, |F j x - G x|) atTop (𝓝 0))
    (hleft : ∀ a < v, ∀ᶠ j in atTop, ∀ u ≤ a, 0 ≤ F j u)
    (htail : ∀ δ > 0, ∃ b₀ : ℝ, ∀ b ≥ b₀, ∀ᶠ j in atTop, ∫ u in Ioi b, |F j u| ≤ δ) :
    Integrable G ∧ ∫ x, |G x| ≤ 1 ∧ ∫ x, G x ≤ 0 ∧ 1 / 2 ≤ ∫ x, max (-G x) 0 ∧
      (∫ x, G x = 0 → ∫ x, |G x| = 1 ∧ Tendsto (fun j => ∫ x, |F j x - G x|) atTop (𝓝 0)) ∧
      (Continuous G → (∀ u ≤ v, 0 ≤ G u) ∧ 1 / 2 ≤ ∫ u in Ioi v, max (-G u) 0) := by
  have hKm : ∀ n : ℕ, MeasurableSet (Icc (-(n : ℝ)) n) := fun n => measurableSet_Icc
  have hKmono : Monotone (fun n : ℕ => Icc (-(n : ℝ)) n) := fun m n hmn =>
    Icc_subset_Icc (neg_le_neg (by exact_mod_cast hmn)) (by exact_mod_cast hmn)
  have hKU : (⋃ n : ℕ, Icc (-(n : ℝ)) n) = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact mem_iUnion.2 ⟨n, abs_le.mp hn⟩
  have htight : ∀ η > 0, ∃ n : ℕ, ∀ᶠ j in atTop,
      ∫ x in (Icc (-(n : ℝ)) n)ᶜ, max (-F j x) 0 ≤ η := by
    intro η hη
    obtain ⟨b₀, hb₀⟩ := htail η hη
    obtain ⟨n, hn⟩ := exists_nat_ge (max b₀ (1 - v))
    have hnb : b₀ ≤ n := (le_max_left _ _).trans hn
    have hnv : 1 - v ≤ n := (le_max_right _ _).trans hn
    refine ⟨n, ?_⟩
    filter_upwards [hleft (v - 1) (by linarith), hb₀ n hnb] with j hj1 hj2
    calc ∫ x in (Icc (-(n : ℝ)) n)ᶜ, max (-F j x) 0
        ≤ ∫ x in (Icc (-(n : ℝ)) n)ᶜ, (Ioi (n : ℝ)).indicator (fun u => |F j u|) x := by
          refine setIntegral_mono_on (hFi j).neg_part.integrableOn
            (((hFi j).abs.indicator measurableSet_Ioi).integrableOn) measurableSet_Icc.compl
            fun x hx => ?_
          by_cases hx' : x ∈ Ioi (n : ℝ)
          · rw [indicator_of_mem hx']; exact max_le (neg_le_abs _) (abs_nonneg _)
          · rw [indicator_of_notMem hx']
            have hxn : x < -(n : ℝ) := by
              by_contra hlt
              exact hx ⟨not_lt.mp hlt, not_lt.mp hx'⟩
            have := hj1 x (by linarith)
            rw [max_eq_right (by linarith)]
      _ ≤ ∫ x, (Ioi (n : ℝ)).indicator (fun u => |F j u|) x :=
          setIntegral_le_integral ((hFi j).abs.indicator measurableSet_Ioi)
            (Eventually.of_forall fun x => indicator_nonneg (fun _ _ => abs_nonneg _) x)
      _ = ∫ x in Ioi (n : ℝ), |F j x| := integral_indicator measurableSet_Ioi
      _ ≤ η := hj2
  have hmain := qual_compact (μ := volume) hKm hKmono hKU hFi hGi hnorm hmass hloc htight
  obtain ⟨hGint, hGabs, hG0, hGneg, hEq⟩ := hmain
  refine ⟨hGint, hGabs, hG0, hGneg, hEq, fun hGc => ?_⟩
  -- the ray sign
  have hsign : ∀ a < v, ∀ u ≤ a, 0 ≤ G u := by
    intro a ha u hu
    obtain ⟨n, hn⟩ := exists_nat_ge (max (-u) (|a| + 1))
    have hnu : -u ≤ n := (le_max_left _ _).trans hn
    have hna : |a| + 1 ≤ n := (le_max_right _ _).trans hn
    have hab1 := neg_abs_le a
    have hab2 := le_abs_self a
    set s : Set ℝ := Icc (-(n : ℝ)) a with hs
    have hsub : s ⊆ Icc (-(n : ℝ)) n := Icc_subset_Icc le_rfl (by linarith)
    have hGs : IntegrableOn G s := (hGi n).mono_set hsub
    have hlocs : Tendsto (fun j => ∫ x in s, |F j x - G x|) atTop (𝓝 0) := by
      refine squeeze_zero (fun j => setIntegral_nonneg measurableSet_Icc fun x _ => abs_nonneg _)
        (fun j => ?_) (hloc n)
      exact setIntegral_mono_set (((hFi j).sub hGint).abs.integrableOn)
        (Eventually.of_forall fun x => abs_nonneg _) (Eventually.of_forall fun x hx => hsub hx)
    have hlim0 := tendsto_setIntegral_lip (s := s) (φ := fun t => max (-t) 0) neg_part_lip
      (fun j => (hFi j).neg_part.integrableOn) hGs.neg_part (fun j => (hFi j).integrableOn) hGs hlocs
    have hzero : ∫ x in s, max (-G x) 0 = 0 := by
      refine tendsto_nhds_unique hlim0 (tendsto_const_nhds.congr' ?_)
      filter_upwards [hleft a ha] with j hj
      symm
      refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      exact max_eq_right (by linarith [hj x hx.2])
    have hGnc : Continuous fun x => max (-G x) 0 := (hGc.neg).max continuous_const
    have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun x => le_max_right _ _)
      hGnc.continuousOn.integrableOn_Icc).1 hzero
    have heq := Measure.eqOn_Icc_of_ae_eq volume (by linarith : -(n : ℝ) ≠ a) hae
      hGnc.continuousOn (continuous_const (y := (0 : ℝ))).continuousOn
      (show u ∈ Icc (-(n : ℝ)) a from ⟨by linarith, hu⟩)
    have := heq
    simp only [Pi.zero_apply] at this
    by_contra hneg
    push Not at hneg
    rw [max_eq_left (by linarith)] at this
    linarith
  have hsign_v : ∀ u ≤ v, 0 ≤ G u := by
    have hcl : IsClosed {u : ℝ | 0 ≤ G u} := isClosed_le continuous_const hGc
    intro u hu
    have : u ∈ closure (Iio v) := by rw [closure_Iio]; exact hu
    exact closure_minimal (fun x hx => hsign x hx x le_rfl) hcl this
  refine ⟨hsign_v, ?_⟩
  have hzero_left : ∫ u in Iic v, max (-G u) 0 = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    exact max_eq_right (by linarith [hsign_v x hx])
  have hsp := integral_add_compl (μ := volume) (measurableSet_Iic (a := v)) hGint.neg_part
  rw [compl_Iic, hzero_left, zero_add] at hsp
  linarith

/-- info: 'FormalResearch.Analysis.qual_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Analysis.qual_compact

/-- info: 'FormalResearch.Analysis.qual_compact_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Analysis.qual_compact_real

end Real

end FormalResearch.Analysis
