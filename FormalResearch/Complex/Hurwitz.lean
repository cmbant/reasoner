module

public import FormalResearch.Complex.Rouche
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Hurwitz's theorem

Generic complex analysis (no application content).  **Proved**, for a net of holomorphic functions `F n` converging
locally uniformly on an open set `U` (`TendstoLocallyUniformlyOn F f p U`, along any filter `p`, in particular sequences).

Statements formalised (Hurwitz 1889; Conway, *Functions of One Complex Variable*, VII.2.5; Stein–Shakarchi, Ch. 3 Prop. 4.2
for the non-vanishing form):

* `hurwitz_zeroCount`: if `f` has no zero on the circle `sphere c r` (`r < R`, `ball c R ⊆ U`) then eventually
  `F n` is non-vanishing on the circle and has the same number of zeros as `f`, with multiplicity, in `ball c r`
  (Rouché applied to `F n` and `f`; `hurwitz_rouche_eventually` is the uniform-convergence step);
* `hurwitz_zeroCount_small`: if `f` has a zero of order `m` at `z₀` and `f` is not identically zero near `z₀`, there is
  `r₀ > 0` such that for **every** `r ∈ (0, r₀]`, eventually `F n` has exactly `m` zeros (with multiplicity) in
  `ball z₀ r`; they therefore converge to `z₀` (`hurwitz_exists_zero_near`: every zero of `f`, not identically zero near
  it, is a limit of zeros of `F n`);
* `hurwitz_nonvanishing`: if `U` is open and connected, the `F n` are zero-free on `U` and `f ≢ 0` then `f` has no zero in `U`;
* `hurwitz_simple_real_zero`: for real `F n` (`F n (conj z) = conj (F n z)`), a simple real zero `x₀` of `f` is a limit of
  real zeros of `F n` (the unique zero in the disc is fixed by conjugation), the form used for persistence of simple real zeros;
* `hurwitz_no_zeros_off`: on a compact `K ⊆ U` and an open `W` containing the zeros of `f` in `K`, eventually `F n` has no zero
  in `K \ W` (this is uniform convergence only; `f` need not be holomorphic).

**Not formalised.** Hurwitz for univalent limits (injectivity), the meromorphic version, a quantitative rate.
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ArgPrinciple

variable {ι : Type*} {p : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {r R : ℝ}

/-- Uniform convergence on a circle on which `f` does not vanish gives the Rouché inequality eventually. -/
theorem hurwitz_rouche_eventually (hU : IsOpen U) (hF : TendstoLocallyUniformlyOn F f p U)
    (hf : DifferentiableOn ℂ f U) (hr : 0 < r) (hrR : r < R) (hball : ball c R ⊆ U)
    (hne : ∀ z ∈ sphere c r, f z ≠ 0) :
    ∀ᶠ n in p, ∀ z ∈ sphere c r, ‖F n z - f z‖ < ‖f z‖ := by
  have hsphU : sphere c r ⊆ U := sphere_subset_closedBall.trans ((closedBall_subset_ball hrR).trans hball)
  have hne' : (sphere c r).Nonempty := ⟨c + r, by simp [abs_of_pos hr]⟩
  obtain ⟨z0, hz0, hmin⟩ := (isCompact_sphere c r).exists_isMinOn hne'
    (hf.continuousOn.mono hsphU).norm
  have hm : 0 < ‖f z0‖ := norm_pos_iff.mpr (hne z0 hz0)
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hF (sphere c r) hsphU (isCompact_sphere c r)
  have h1 := Metric.tendstoUniformlyOn_iff.mp hunif ‖f z0‖ hm
  filter_upwards [h1] with n hn z hz
  have := hn z hz
  rw [dist_eq_norm] at this
  calc ‖F n z - f z‖ = ‖f z - F n z‖ := norm_sub_rev _ _
    _ < ‖f z0‖ := this
    _ ≤ ‖f z‖ := isMinOn_iff.mp hmin z hz

/-- **Hurwitz, counting form.**  `f` holomorphic on `U`, non-vanishing on `sphere c r`, `r < R`, `ball c R ⊆ U`:
eventually `F n` is non-vanishing on the circle and has as many zeros (with multiplicity) in `ball c r` as `f`. -/
theorem hurwitz_zeroCount (hU : IsOpen U) (hF : TendstoLocallyUniformlyOn F f p U)
    (hFd : ∀ᶠ n in p, DifferentiableOn ℂ (F n) U) (hf : DifferentiableOn ℂ f U)
    (hr : 0 < r) (hrR : r < R) (hball : ball c R ⊆ U) (hne : ∀ z ∈ sphere c r, f z ≠ 0) :
    ∀ᶠ n in p, (∀ z ∈ sphere c r, F n z ≠ 0) ∧ zeroCount (F n) c r = zeroCount f c r := by
  filter_upwards [hurwitz_rouche_eventually hU hF hf hr hrR hball hne, hFd] with n hn hd
  refine ⟨fun z hz h0 => ?_, rouche hr hrR (hd.mono hball) (hf.mono hball) fun z hz => ?_⟩
  · have := hn z hz
    rw [h0, zero_sub, norm_neg] at this
    exact lt_irrefl _ this
  · exact hn z hz

/-- A zero in the disc, of a function that is not identically zero, gives a non-zero count. -/
lemma zeroCount_ne_zero (hf : DifferentiableOn ℂ f (ball c R)) (hr : 0 < r) (hrR : r < R)
    (hne : ∀ z ∈ sphere c r, f z ≠ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ ball c r) (hfz₀ : f z₀ = 0) :
    zeroCount f c r ≠ 0 := by
  obtain ⟨hw, hfw⟩ := exists_nonzero_of_sphere hr hrR hne
  have hfin := support_orderNat_finite hf hw hfw hrR
  have hz₀R : z₀ ∈ ball c R := ball_subset_ball hrR.le hz₀
  have hmem : z₀ ∈ ball c r ∩ Function.support fun z => analyticOrderNatAt f z :=
    ⟨hz₀, (orderNat_ne_zero_iff hf hw hfw hz₀R).mpr hfz₀⟩
  have h1 : zeroCount f c r = ∑ z ∈ hfin.toFinset, analyticOrderNatAt f z := by
    unfold zeroCount
    rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have h2 : analyticOrderNatAt f z₀ ≤ ∑ z ∈ hfin.toFinset, analyticOrderNatAt f z :=
    Finset.single_le_sum (f := fun z => analyticOrderNatAt f z) (fun _ _ => Nat.zero_le _)
      (hfin.mem_toFinset.mpr hmem)
  have := Nat.pos_of_ne_zero (show analyticOrderNatAt f z₀ ≠ 0 from hmem.2)
  omega

/-- A non-zero count produces a zero in the disc. -/
lemma exists_zero_of_zeroCount_ne_zero {g : ℂ → ℂ} (h : zeroCount g c r ≠ 0) :
    ∃ z ∈ ball c r, g z = 0 := by
  by_contra hcon
  push Not at hcon
  refine h (finsum_mem_eq_zero_of_forall_eq_zero fun z hz => ?_)
  by_contra hz0
  exact hcon z hz (apply_eq_zero_of_analyticOrderNatAt_ne_zero hz0)

/-- If `f` has no zeros on the punctured disc `0 < ‖z - z₀‖ < ρ` (and is holomorphic on `ball z₀ R`, `r < min ρ R`,
`r > 0`) then its count in `ball z₀ r` is its order at `z₀`. -/
lemma zeroCount_eq_orderNat (hf : DifferentiableOn ℂ f (ball c R)) {ρ : ℝ} (hr : 0 < r) (hrR : r < R)
    (hrρ : r < ρ) (hρ : ∀ z, 0 < dist z c → dist z c < ρ → f z ≠ 0) :
    zeroCount f c r = analyticOrderNatAt f c := by
  have hne : ∀ z ∈ sphere c r, f z ≠ 0 := fun z hz =>
    hρ z (by rw [mem_sphere.mp hz]; exact hr) (by rw [mem_sphere.mp hz]; exact hrρ)
  obtain ⟨hw, hfw⟩ := exists_nonzero_of_sphere hr hrR hne
  have hcb : c ∈ ball c r := mem_ball_self hr
  have hsupp : ball c r ∩ Function.support (fun z => analyticOrderNatAt f z) ⊆ {c} := by
    intro z ⟨hz, hz0⟩
    have hzR : z ∈ ball c R := ball_subset_ball hrR.le hz
    have hfz := (orderNat_ne_zero_iff hf hw hfw hzR).mp hz0
    by_contra hzc
    have hzc' : 0 < dist z c := dist_pos.mpr hzc
    exact hρ z hzc' (lt_trans (mem_ball.mp hz) hrρ) hfz
  unfold zeroCount
  rw [← finsum_mem_inter_support]
  by_cases hk : analyticOrderNatAt f c = 0
  · have : ball c r ∩ Function.support (fun z => analyticOrderNatAt f z) = ∅ := by
      refine Set.eq_empty_of_subset_empty fun z hz => ?_
      have := hsupp hz
      rw [Set.mem_singleton_iff] at this
      subst this
      exact hz.2 hk
    rw [this]; simp [hk]
  · have : ball c r ∩ Function.support (fun z => analyticOrderNatAt f z) = {c} :=
      Set.Subset.antisymm hsupp (Set.singleton_subset_iff.mpr ⟨hcb, hk⟩)
    rw [this, finsum_mem_singleton]

/-- A holomorphic function that is not identically zero near `z₀` has a punctured disc around `z₀` free of zeros. -/
lemma exists_punctured_disc (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hnz : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0) :
    ∃ ρ > 0, ball z₀ ρ ⊆ U ∧ ∀ z, 0 < dist z z₀ → dist z z₀ < ρ → f z ≠ 0 := by
  have han : AnalyticAt ℂ f z₀ := (hf.analyticOnNhd hU) z₀ hz₀
  have h1 : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 :=
    (han.eventually_eq_zero_or_eventually_ne_zero).resolve_left hnz
  obtain ⟨ρ1, hρ1, hb1⟩ := Metric.mem_nhdsWithin_iff.mp h1
  obtain ⟨ρ2, hρ2, hb2⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, (ball_subset_ball (min_le_right _ _)).trans hb2, fun z hz0 hz1 => ?_⟩
  exact hb1 ⟨(mem_ball.mpr (lt_of_lt_of_le hz1 (min_le_left _ _))), (dist_pos.mp hz0)⟩

/-- **Hurwitz: the count near a zero.**  If `f` (a locally uniform limit of holomorphic `F n`) is not identically zero
near `z₀ ∈ U`, there is `r₀ > 0` such that for every `0 < r ≤ r₀`, eventually `F n` has exactly `ord_{z₀} f` zeros, with
multiplicity, in `ball z₀ r`.  (Zeros of `f` that are not identically-zero points.) -/
theorem hurwitz_zeroCount_small (hU : IsOpen U) (hF : TendstoLocallyUniformlyOn F f p U)
    (hFd : ∀ᶠ n in p, DifferentiableOn ℂ (F n) U) (hf : DifferentiableOn ℂ f U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hnz : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ᶠ n in p, zeroCount (F n) z₀ r = analyticOrderNatAt f z₀ := by
  obtain ⟨ρ, hρ, hρU, hρne⟩ := exists_punctured_disc hf hU hz₀ hnz
  refine ⟨ρ / 2, by positivity, fun r hr hrle => ?_⟩
  have hrρ : r < ρ := by linarith
  have h1 := hurwitz_zeroCount hU hF hFd hf hr hrρ hρU (fun z hz =>
    hρne z (by rw [mem_sphere.mp hz]; exact hr) (by rw [mem_sphere.mp hz]; exact hrρ))
  have h2 := zeroCount_eq_orderNat (hf.mono hρU) hr hrρ hrρ hρne
  exact h1.mono fun n hn => hn.2.trans h2

/-- **Hurwitz: zeros of the limit are limits of zeros.**  If `f z₀ = 0`, `z₀ ∈ U` and `f` is not identically zero near
`z₀`, then for every `ε > 0`, eventually `F n` has a zero in `U ∩ ball z₀ ε`. -/
theorem hurwitz_exists_zero_near (hU : IsOpen U) (hF : TendstoLocallyUniformlyOn F f p U)
    (hFd : ∀ᶠ n in p, DifferentiableOn ℂ (F n) U) (hf : DifferentiableOn ℂ f U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hfz₀ : f z₀ = 0) (hnz : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in p, ∃ z ∈ ball z₀ ε, z ∈ U ∧ F n z = 0 := by
  obtain ⟨ρ, hρ, hρU, hρne⟩ := exists_punctured_disc hf hU hz₀ hnz
  set r := min (ρ / 2) (ε / 2) with hrdef
  have hr : 0 < r := by positivity
  have hrρ : r < ρ := by have := min_le_left (ρ / 2) (ε / 2); linarith
  have hrε : r < ε := by have := min_le_right (ρ / 2) (ε / 2); linarith
  have hsph : ∀ z ∈ sphere z₀ r, f z ≠ 0 := fun z hz =>
    hρne z (by rw [mem_sphere.mp hz]; exact hr) (by rw [mem_sphere.mp hz]; exact hrρ)
  have h1 := hurwitz_zeroCount hU hF hFd hf hr hrρ hρU hsph
  have hne : zeroCount f z₀ r ≠ 0 :=
    zeroCount_ne_zero (hf.mono hρU) hr hrρ hsph (mem_ball_self hr) hfz₀
  filter_upwards [h1] with n hn
  have : zeroCount (F n) z₀ r ≠ 0 := by rw [hn.2]; exact hne
  obtain ⟨z, hz, hFz⟩ := exists_zero_of_zeroCount_ne_zero this
  exact ⟨z, ball_subset_ball hrε.le hz, hρU (ball_subset_ball hrρ.le hz), hFz⟩

/-- **Hurwitz's theorem (non-vanishing form).**  A locally uniform limit, on an open connected set, of zero-free
holomorphic functions is either identically zero or zero-free. -/
theorem hurwitz_nonvanishing [p.NeBot] (hU : IsOpen U) (hconn : IsPreconnected U)
    (hF : TendstoLocallyUniformlyOn F f p U) (hFd : ∀ᶠ n in p, DifferentiableOn ℂ (F n) U)
    (hFz : ∀ᶠ n in p, ∀ z ∈ U, F n z ≠ 0) {w : ℂ} (hw : w ∈ U) (hfw : f w ≠ 0) :
    ∀ z ∈ U, f z ≠ 0 := by
  intro z₀ hz₀ hfz₀
  have hf : DifferentiableOn ℂ f U := hF.differentiableOn hFd hU
  have hnz : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0 := fun h =>
    hfw ((hf.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz₀ h hw)
  have h1 := hurwitz_exists_zero_near hU hF hFd hf hz₀ hfz₀ hnz one_pos
  obtain ⟨n, ⟨z, -, hzU, hz⟩, hn⟩ := (h1.and hFz).exists
  exact hn z hzU hz

/-- **Uniform non-vanishing away from the zeros of the limit.**  If `F n → f` locally uniformly on `U`, `K ⊆ U` is
compact and `W` is open and contains every zero of `f` in `K`, then eventually `F n` has no zero in `K \ W`. -/
theorem hurwitz_no_zeros_off [p.NeBot] (hU : IsOpen U) (hF : TendstoLocallyUniformlyOn F f p U)
    (hFc : ∀ᶠ n in p, ContinuousOn (F n) U) {K W : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    (hW : IsOpen W) (hz : ∀ z ∈ K, f z = 0 → z ∈ W) :
    ∀ᶠ n in p, ∀ z ∈ K \ W, F n z ≠ 0 := by
  have hKW : IsCompact (K \ W) := hK.diff hW
  have hsub : K \ W ⊆ U := Set.sdiff_subset.trans hKU
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hF (K \ W) hsub hKW
  by_cases hne : (K \ W).Nonempty
  · have hfc : ContinuousOn f U := hF.continuousOn hFc.frequently
    obtain ⟨z1, hz1, hmin⟩ := hKW.exists_isMinOn hne (hfc.mono hsub).norm
    have hfz1 : f z1 ≠ 0 := fun h0 => hz1.2 (hz z1 hz1.1 h0)
    have hm : 0 < ‖f z1‖ := norm_pos_iff.mpr hfz1
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif ‖f z1‖ hm] with n hn z hzK h0
    have h1 := hn z hzK
    rw [h0, dist_zero_right] at h1
    exact absurd (isMinOn_iff.mp hmin z hzK) (not_le.mpr h1)
  · refine Eventually.of_forall fun n z hzK => absurd ⟨z, hzK⟩ hne


/-- If the count in `ball c r` is one, there is only one zero there. -/
lemma eq_of_zeroCount_eq_one (hf : DifferentiableOn ℂ f (ball c R)) (hr : 0 < r) (hrR : r < R)
    (hne : ∀ z ∈ sphere c r, f z ≠ 0) (hcount : zeroCount f c r = 1) {z w : ℂ} (hz : z ∈ ball c r)
    (hw : w ∈ ball c r) (hfz : f z = 0) (hfw : f w = 0) : z = w := by
  by_contra hzw
  obtain ⟨hw0, hfw0⟩ := exists_nonzero_of_sphere hr hrR hne
  have hfin := support_orderNat_finite hf hw0 hfw0 hrR
  have h1 : zeroCount f c r = ∑ z ∈ hfin.toFinset, analyticOrderNatAt f z := by
    unfold zeroCount
    rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hmem : ∀ x ∈ ball c r, f x = 0 → x ∈ hfin.toFinset := fun x hx hfx =>
    hfin.mem_toFinset.mpr ⟨hx, (orderNat_ne_zero_iff hf hw0 hfw0 (ball_subset_ball hrR.le hx)).mpr hfx⟩
  have hpos : ∀ x ∈ ball c r, f x = 0 → 1 ≤ analyticOrderNatAt f x := fun x hx hfx =>
    Nat.pos_of_ne_zero ((orderNat_ne_zero_iff hf hw0 hfw0 (ball_subset_ball hrR.le hx)).mpr hfx)
  have h2 : ∑ x ∈ ({z, w} : Finset ℂ), analyticOrderNatAt f x ≤ ∑ z ∈ hfin.toFinset, analyticOrderNatAt f z := by
    refine Finset.sum_le_sum_of_subset ?_
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hmem _ hz hfz
    · rw [Finset.mem_singleton.mp hx]; exact hmem _ hw hfw
  rw [Finset.sum_pair hzw] at h2
  have := hpos z hz hfz
  have := hpos w hw hfw
  omega

/-- **Hurwitz for simple real zeros.**  Let `F n` be real (`F n (conj z) = conj (F n z)`), `F n → f` locally uniformly on
`U`, and let `x₀ ∈ ℝ ∩ U` be a simple zero of `f` (`analyticOrderNatAt f x₀ = 1`).  Then for every `ε > 0`, eventually `F n`
has a real zero within `ε` of `x₀` (and no other zero in `ball x₀ r` for small `r`, by `hurwitz_zeroCount_small`). -/
theorem hurwitz_simple_real_zero (hU : IsOpen U) (hF : TendstoLocallyUniformlyOn F f p U)
    (hFd : ∀ᶠ n in p, DifferentiableOn ℂ (F n) U) (hf : DifferentiableOn ℂ f U)
    (hsym : ∀ᶠ n in p, ∀ z, F n (starRingEnd ℂ z) = starRingEnd ℂ (F n z))
    {x₀ : ℝ} (hx₀ : (x₀ : ℂ) ∈ U) (hord : analyticOrderNatAt f (x₀ : ℂ) = 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in p, ∃ x : ℝ, |x - x₀| < ε ∧ F n x = 0 := by
  have hnz : ¬ ∀ᶠ z in 𝓝 (x₀ : ℂ), f z = 0 := fun h => by
    have : analyticOrderAt f (x₀ : ℂ) = ⊤ := analyticOrderAt_eq_top.mpr h
    simp [analyticOrderNatAt, this] at hord
  obtain ⟨ρ, hρ, hρU, hρne⟩ := exists_punctured_disc hf hU hx₀ hnz
  set r := min (ρ / 2) (ε / 2) with hrdef
  have hr : 0 < r := by positivity
  have hrρ : r < ρ := by have := min_le_left (ρ / 2) (ε / 2); linarith
  have hrε : r < ε := by have := min_le_right (ρ / 2) (ε / 2); linarith
  have hsph : ∀ z ∈ sphere (x₀ : ℂ) r, f z ≠ 0 := fun z hz =>
    hρne z (by rw [mem_sphere.mp hz]; exact hr) (by rw [mem_sphere.mp hz]; exact hrρ)
  have h1 := hurwitz_zeroCount hU hF hFd hf hr hrρ hρU hsph
  have h2 := zeroCount_eq_orderNat (hf.mono hρU) hr hrρ hrρ hρne
  filter_upwards [h1, hFd, hsym] with n hn hd hs
  have hcount : zeroCount (F n) (x₀ : ℂ) r = 1 := by rw [hn.2, h2, hord]
  have hne : zeroCount (F n) (x₀ : ℂ) r ≠ 0 := by rw [hcount]; exact one_ne_zero
  obtain ⟨z, hz, hFz⟩ := exists_zero_of_zeroCount_ne_zero hne
  have hzc : starRingEnd ℂ z ∈ ball (x₀ : ℂ) r := by
    rw [mem_ball, dist_eq_norm] at hz ⊢
    have : starRingEnd ℂ z - (x₀ : ℂ) = starRingEnd ℂ (z - (x₀ : ℂ)) := by simp
    rw [this, Complex.norm_conj]; exact hz
  have hFzc : F n (starRingEnd ℂ z) = 0 := by rw [hs, hFz]; simp
  have hzz := eq_of_zeroCount_eq_one (hd.mono hρU) hr hrρ hn.1 hcount hz hzc hFz hFzc
  have him : z.im = 0 := by
    have := congrArg Complex.im hzz
    simp at this; linarith
  refine ⟨z.re, ?_, ?_⟩
  · have h3 : |(z - (x₀ : ℂ)).re| ≤ ‖z - (x₀ : ℂ)‖ := abs_re_le_norm _
    have h4 : ‖z - (x₀ : ℂ)‖ < r := by rw [← dist_eq_norm]; exact mem_ball.mp hz
    simp at h3
    linarith
  · have : (z.re : ℂ) = z := Complex.ext (by simp) (by simp [him])
    rw [this]; exact hFz

/-- info: 'FormalResearch.ArgPrinciple.hurwitz_zeroCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ArgPrinciple.hurwitz_zeroCount

/-- info: 'FormalResearch.ArgPrinciple.hurwitz_zeroCount_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ArgPrinciple.hurwitz_zeroCount_small

/-- info: 'FormalResearch.ArgPrinciple.hurwitz_exists_zero_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ArgPrinciple.hurwitz_exists_zero_near

/-- info: 'FormalResearch.ArgPrinciple.hurwitz_nonvanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ArgPrinciple.hurwitz_nonvanishing

/-- info: 'FormalResearch.ArgPrinciple.hurwitz_no_zeros_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ArgPrinciple.hurwitz_no_zeros_off

/-- info: 'FormalResearch.ArgPrinciple.hurwitz_simple_real_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ArgPrinciple.hurwitz_simple_real_zero

end FormalResearch.ArgPrinciple
