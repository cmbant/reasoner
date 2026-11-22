module

public import Mathlib

/-!
# Paper J, Layer 2: stability of the allowed interval and continuity of `int q / sqrt T` (L2.E, Step 1 of cor:eigen, part 1)

Source: Paper J `thmA.tex`, proof of `cor:eigen`, Step 1 ("Hadamard division ... the turning points `u_pm(lambda)` depend smoothly on the parameters, `T >= c (u - u_-)(u_+ - u)`").
These are the analytic estimates behind `eq:cp-S0p` and `eq:cp-dt` (`TheoremA/ActionDerivativeShift.lean`, `TheoremA/ActionDerivative.lean`); nothing here mentions Jacobi matrices.

## Proved here

Let `f : R -> Lambda -> R` be a family of functions on `[0, L]` (`Lambda` a topological space), jointly continuous, with `u`-derivative `f1` jointly continuous (`HasDerivWithinAt` on `[0, L]`), and `f(0, l) <= 0`, `f(L, l) <= 0`
for all `l` (the hard edges: `E_0(0) = E_0(L) = 0`).

* `end_left`, `end_right`: if at `l0` the function `f(., l0)` has a simple zero at `a0` (resp. `b0`) with `f < 0` on the outer side and `f > 0` on the inner side, then for `l` near `l0` it has a unique zero `a(l)` near `a0`, `a` is continuous at every `l` of an
  open neighbourhood, `f(., l) < 0` on `[0, a(l))` and `f(u, l) >= c_0 (u - a(l))` near `a(l)`.  (Quantitative mean value theorem on the interval where `f1 >= c_0`; intermediate value theorem for existence.)
* `stable_structure`: if at `l0` the set `{f >= 0}` is `[a0, b0]`, `f > 0` on `(a0, b0)`, both zeros simple, then on an open neighbourhood `V` of `l0`: `{f(., l) >= 0} = [a(l), b(l)]`, `a, b` continuous, `f(a l) = f(b l) = 0` and
  `f(u, l) >= c (u - a(l))(b(l) - u)` on `[a(l), b(l)]` (Hadamard lower bound, uniform on `V`).
* `intervalIntegrable_inv_sqrt`: `u -> 1 / sqrt((u - a)(b - u))` is integrable on `[a, b]` (it is the derivative of `arcsin((2u - a - b)/(b - a))`).
* `integral_inv_sqrt_continuousAt`: under the structure of `stable_structure` on an open `V`, for continuous `q`, each `l -> int_0^L q(u, l)/sqrt(f(u, l)) du` is interval integrable and continuous at every `l in V`
  (substitution `u = a + (b - a) s`, dominating function `C / sqrt(c s (1 - s))`).

## Differences from the paper

The paper obtains `T >= c (u - u_-)(u_+ - u)` from smoothness of `u_pm(lambda)` (implicit function theorem); here only continuity of the end points is needed and proved directly (quantitative monotonicity near a simple zero), so no implicit function theorem is used.
The convention `x / sqrt(y) = 0` for `y <= 0` of Lean makes `q / sqrt f` vanish outside the allowed set without an indicator.

## Not formalised

Differentiability of `a, b` in `l` (not needed).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv

open Set Filter Topology MeasureTheory
open scoped Interval

variable {Λ : Type*} [TopologicalSpace Λ]

lemma ev_forall_lt {L : ℝ} {f : ℝ → Λ → ℝ} {K : Set ℝ} (hK : IsCompact K) (hKS : K ⊆ Icc 0 L)
    (hc : ContinuousOn (fun p : ℝ × Λ => f p.1 p.2) (Icc 0 L ×ˢ univ)) {l0 : Λ} {c : ℝ}
    (h : ∀ u ∈ K, f u l0 < c) : ∀ᶠ l in 𝓝 l0, ∀ u ∈ K, f u l < c := by
  refine hK.eventually_forall_of_forall_eventually (P := fun l u => u ∈ Icc 0 L → f u l < c) ?_ |>.mono ?_
  · intro u hu
    have h1 := (hc (u, l0) ⟨hKS hu, mem_univ _⟩).eventually (eventually_lt_nhds (h u hu))
    have h2 := eventually_nhdsWithin_iff.1 h1
    have h3 := (continuous_swap.tendsto (l0, u)).eventually h2
    refine h3.mono ?_
    intro z hz hzu
    exact hz ⟨hzu, mem_univ _⟩
  · intro l hl u hu
    exact hl u hu (hKS hu)

lemma ev_forall_gt {L : ℝ} {f : ℝ → Λ → ℝ} {K : Set ℝ} (hK : IsCompact K) (hKS : K ⊆ Icc 0 L)
    (hc : ContinuousOn (fun p : ℝ × Λ => f p.1 p.2) (Icc 0 L ×ˢ univ)) {l0 : Λ} {c : ℝ}
    (h : ∀ u ∈ K, c < f u l0) : ∀ᶠ l in 𝓝 l0, ∀ u ∈ K, c < f u l := by
  have := ev_forall_lt (f := fun u l => -f u l) hK hKS hc.neg (c := -c) (l0 := l0)
    (fun u hu => by have := h u hu; show -f u l0 < -c; linarith)
  refine this.mono fun l hl u hu => ?_
  have : -f u l < -c := hl u hu
  linarith

lemma end_left {L : ℝ} {f f1 : ℝ → Λ → ℝ} {l0 : Λ} {a0 δ1 : ℝ}
    (hc : ContinuousOn (fun p : ℝ × Λ => f p.1 p.2) (Icc 0 L ×ˢ univ))
    (hd : ∀ l, ∀ u ∈ Icc 0 L, HasDerivWithinAt (fun v => f v l) (f1 u l) (Icc 0 L) u)
    (hc1 : ContinuousOn (fun p : ℝ × Λ => f1 p.1 p.2) (Icc 0 L ×ˢ univ))
    (h0 : ∀ l, f 0 l ≤ 0) (ha0 : 0 ≤ a0) (hδ1 : 0 < δ1) (hδL : a0 + δ1 ≤ L)
    (hz : f a0 l0 = 0) (hneg : ∀ u ∈ Ico 0 a0, f u l0 < 0) (hpos : ∀ u ∈ Ioc a0 (a0 + δ1), 0 < f u l0)
    (hder : 0 < f1 a0 l0) :
    ∃ δ c0 : ℝ, 0 < δ ∧ δ ≤ δ1 ∧ 0 < c0 ∧ ∃ W : Set Λ, IsOpen W ∧ l0 ∈ W ∧ ∃ a : Λ → ℝ,
      (∀ l ∈ W, ContinuousAt a l) ∧ a l0 = a0 ∧
      ∀ l ∈ W, 0 ≤ a l ∧ a l < a0 + δ ∧ f (a l) l = 0 ∧ (∀ u ∈ Ico 0 (a l), f u l < 0) ∧
        ∀ u ∈ Icc (a l) (a0 + δ), c0 * (u - a l) ≤ f u l := by
  classical
  have ha0L : a0 ∈ Icc 0 L := ⟨ha0, by linarith⟩
  obtain ⟨c0, hc0pos, hc0lt⟩ : ∃ c0 : ℝ, 0 < c0 ∧ c0 < f1 a0 l0 := ⟨f1 a0 l0 / 2, by linarith, by linarith⟩
  have h1 : ∀ᶠ p in 𝓝[Icc 0 L ×ˢ (univ : Set Λ)] (a0, l0), c0 < f1 p.1 p.2 :=
    (hc1 (a0, l0) ⟨ha0L, mem_univ _⟩).eventually (eventually_gt_nhds hc0lt)
  have h2 : ∀ᶠ p in 𝓝 (a0, l0), p ∈ Icc 0 L ×ˢ (univ : Set Λ) → c0 < f1 p.1 p.2 :=
    eventually_nhdsWithin_iff.1 h1
  rw [nhds_prod_eq, eventually_prod_iff] at h2
  obtain ⟨pa, hpa, pb, hpb, hpp⟩ := h2
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff.1 hpa
  set δ := min (ρ / 2) δ1 with hδ
  have hδpos : 0 < δ := lt_min (by linarith) hδ1
  have hδρ : δ < ρ := by have := min_le_left (ρ / 2) δ1; linarith
  have hδδ1 : δ ≤ δ1 := min_le_right _ _
  set p := max 0 (a0 - δ) with hp
  have hp0 : 0 ≤ p := le_max_left _ _
  have hpa0 : p ≤ a0 := max_le ha0 (by linarith)
  have hpL : a0 + δ ≤ L := by linarith
  have hpq : p ≤ a0 + δ := by linarith
  -- eventual sign conditions
  have E1 : ∀ᶠ l in 𝓝 l0, ∀ u ∈ Icc 0 (a0 - δ), f u l < 0 :=
    ev_forall_lt (isCompact_Icc) (fun u hu => ⟨hu.1, by linarith [hu.2]⟩) hc
      (fun u hu => hneg u ⟨hu.1, by linarith [hu.2]⟩)
  have E2 : ∀ᶠ l in 𝓝 l0, ∀ u ∈ ({a0 + δ} : Set ℝ), 0 < f u l :=
    ev_forall_gt (isCompact_singleton) (by rintro u rfl; exact ⟨by linarith, hpL⟩) hc
      (by rintro u rfl; exact hpos _ ⟨by linarith, by linarith⟩)
  have hA : {l | (∀ u ∈ Icc 0 (a0 - δ), f u l < 0) ∧ (∀ u ∈ ({a0 + δ} : Set ℝ), 0 < f u l) ∧ pb l} ∈ 𝓝 l0 :=
    E1.and (E2.and hpb)
  set W := interior {l | (∀ u ∈ Icc 0 (a0 - δ), f u l < 0) ∧ (∀ u ∈ ({a0 + δ} : Set ℝ), 0 < f u l) ∧ pb l} with hW
  have hWo : IsOpen W := isOpen_interior
  have hl0W : l0 ∈ W := mem_interior_iff_mem_nhds.2 hA
  have hWA : ∀ l ∈ W, (∀ u ∈ Icc 0 (a0 - δ), f u l < 0) ∧ 0 < f (a0 + δ) l ∧ pb l := by
    intro l hl
    have := interior_subset hl
    exact ⟨this.1, this.2.1 _ rfl, this.2.2⟩
  -- the quantitative increase
  have Q : ∀ l ∈ W, ∀ x ∈ Icc p (a0 + δ), ∀ y ∈ Icc p (a0 + δ), x ≤ y → c0 * (y - x) ≤ f y l - f x l := by
    intro l hl
    have hpbl := (hWA l hl).2.2
    have hcont : ContinuousOn (fun v => f v l) (Icc p (a0 + δ)) := by
      intro v hv
      exact ((hd l v ⟨le_trans hp0 hv.1, le_trans hv.2 hpL⟩).continuousWithinAt).mono
        (Icc_subset_Icc hp0 hpL)
    have hdiff : DifferentiableOn ℝ (fun v => f v l) (interior (Icc p (a0 + δ))) := by
      rw [interior_Icc]
      intro v hv
      have hv0 : 0 < v := lt_of_le_of_lt hp0 hv.1
      have hvL : v < L := lt_of_lt_of_le hv.2 hpL
      exact ((hd l v ⟨hv0.le, hvL.le⟩).hasDerivAt (Icc_mem_nhds hv0 hvL)).differentiableAt.differentiableWithinAt
    refine (convex_Icc p (a0 + δ)).mul_sub_le_image_sub_of_le_deriv hcont hdiff ?_
    intro v hv
    rw [interior_Icc] at hv
    have hv0 : 0 < v := lt_of_le_of_lt hp0 hv.1
    have hvL : v < L := lt_of_lt_of_le hv.2 hpL
    rw [((hd l v ⟨hv0.le, hvL.le⟩).hasDerivAt (Icc_mem_nhds hv0 hvL)).deriv]
    have hva : dist v a0 < ρ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · have : a0 - δ ≤ p := le_max_right _ _
        linarith [hv.1]
      · linarith [hv.2]
    exact (hpp (hρ' hva) hpbl ⟨⟨hv0.le, hvL.le⟩, mem_univ _⟩).le
  -- root
  have hroot : ∀ l ∈ W, ∃ x ∈ Icc p (a0 + δ), f x l = 0 := by
    intro l hl
    have hcont : ContinuousOn (fun v => f v l) (Icc p (a0 + δ)) := by
      intro v hv
      exact ((hd l v ⟨le_trans hp0 hv.1, le_trans hv.2 hpL⟩).continuousWithinAt).mono
        (Icc_subset_Icc hp0 hpL)
    have hfp : f p l ≤ 0 := by
      by_cases hcase : a0 - δ ≤ 0
      · have : p = 0 := by rw [hp]; exact max_eq_left hcase
        rw [this]; exact h0 l
      · have hcase := not_le.mp hcase
        have : p = a0 - δ := by rw [hp]; exact max_eq_right hcase.le
        rw [this]
        exact ((hWA l hl).1 (a0 - δ) ⟨by linarith, le_rfl⟩).le
    have hfq := (hWA l hl).2.1
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hpq hcont ⟨hfp, hfq.le⟩
    exact ⟨x, hx, hfx⟩
  have hD0 : ∀ l ∈ W, ∀ x ∈ Icc p (a0 + δ), ∀ y ∈ Icc p (a0 + δ), f x l = 0 → f y l = 0 → x = y := by
    intro l hl x hx y hy hfx hfy
    rcases lt_trichotomy x y with h | h | h
    · have := Q l hl x hx y hy h.le; rw [hfx, hfy] at this; nlinarith
    · exact h
    · have := Q l hl y hy x hx h.le; rw [hfx, hfy] at this; nlinarith
  let a : Λ → ℝ := fun l => Classical.epsilon (fun x => x ∈ Icc p (a0 + δ) ∧ f x l = 0)
  have ha_spec : ∀ l ∈ W, a l ∈ Icc p (a0 + δ) ∧ f (a l) l = 0 := by
    intro l hl
    exact Classical.epsilon_spec (hroot l hl)
  have hapos : ∀ l ∈ W, ∀ u ∈ Icc p (a0 + δ), u ≤ a l → f u l ≤ - c0 * (a l - u) := by
    intro l hl u hu hua
    have := Q l hl u hu (a l) (ha_spec l hl).1 hua
    rw [(ha_spec l hl).2] at this
    linarith
  refine ⟨δ, c0, hδpos, hδδ1, hc0pos, W, hWo, hl0W, a, ?_, ?_, ?_⟩
  · -- continuity
    intro l' hl'
    have hS : Tendsto (fun l => (a l', l)) (𝓝 l') (𝓝[Icc 0 L ×ˢ (univ : Set Λ)] (a l', l')) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun l => ⟨?_, mem_univ _⟩⟩
      · exact (continuous_const.prodMk continuous_id).tendsto l'
      · exact ⟨le_trans hp0 (ha_spec l' hl').1.1, le_trans (ha_spec l' hl').1.2 hpL⟩
    have hg : Tendsto (fun l => f (a l') l) (𝓝 l') (𝓝 0) := by
      have := (hc (a l', l') ⟨⟨le_trans hp0 (ha_spec l' hl').1.1, le_trans (ha_spec l' hl').1.2 hpL⟩, mem_univ _⟩).tendsto.comp hS
      have e : f (a l') l' = 0 := (ha_spec l' hl').2
      simpa [Function.comp_def, e] using this
    have hg' : Tendsto (fun l => |f (a l') l| / c0) (𝓝 l') (𝓝 0) := by
      have := (hg.abs).div_const c0
      simpa using this
    have hsq : Tendsto (fun l => a l - a l') (𝓝 l') (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hg'
      filter_upwards [hWo.mem_nhds hl'] with l hl
      rw [Real.norm_eq_abs, le_div_iff₀ hc0pos]
      have h1 := ha_spec l hl
      have h2 := ha_spec l' hl'
      rcases le_total (a l) (a l') with h | h
      · have := Q l hl _ h1.1 _ h2.1 h
        rw [h1.2] at this
        rw [abs_of_nonpos (by linarith)]
        have := le_abs_self (f (a l') l)
        nlinarith
      · have := Q l hl _ h2.1 _ h1.1 h
        rw [h1.2] at this
        rw [abs_of_nonneg (by linarith)]
        have := neg_le_abs (f (a l') l)
        nlinarith
    have : Tendsto a (𝓝 l') (𝓝 (a l')) := by simpa using hsq.add_const (a l')
    exact this
  · -- a l0 = a0
    exact hD0 l0 hl0W _ (ha_spec l0 hl0W).1 a0 ⟨hpa0, by linarith⟩ (ha_spec l0 hl0W).2 hz
  · intro l hl
    have hs := ha_spec l hl
    refine ⟨le_trans hp0 hs.1.1, ?_, hs.2, ?_, ?_⟩
    · rcases hs.1.2.lt_or_eq with h | h
      · exact h
      · exfalso
        have := (hWA l hl).2.1
        rw [← h, hs.2] at this
        exact lt_irrefl _ this
    · intro u hu
      by_cases hup : p ≤ u
      · have := hapos l hl u ⟨hup, by linarith [hu.2, hs.1.2]⟩ hu.2.le
        nlinarith [hu.2]
      · have hup := not_le.mp hup
        have hpe : p = a0 - δ := by
          by_contra hne
          have : p = 0 := by
            rcases max_choice 0 (a0 - δ) with h | h
            · exact h
            · exact absurd h hne
          linarith [hu.1]
        exact (hWA l hl).1 u ⟨hu.1, by linarith⟩
    · intro u hu
      have := Q l hl _ hs.1 u ⟨le_trans hs.1.1 hu.1, hu.2⟩ hu.1
      rw [hs.2] at this
      linarith

lemma end_right {L : ℝ} {f f1 : ℝ → Λ → ℝ} {l0 : Λ} {b0 δ1 : ℝ}
    (hc : ContinuousOn (fun p : ℝ × Λ => f p.1 p.2) (Icc 0 L ×ˢ univ))
    (hd : ∀ l, ∀ u ∈ Icc 0 L, HasDerivWithinAt (fun v => f v l) (f1 u l) (Icc 0 L) u)
    (hc1 : ContinuousOn (fun p : ℝ × Λ => f1 p.1 p.2) (Icc 0 L ×ˢ univ))
    (hL : ∀ l, f L l ≤ 0) (hb0 : b0 ≤ L) (hδ1 : 0 < δ1) (hδ0 : δ1 ≤ b0)
    (hz : f b0 l0 = 0) (hneg : ∀ u ∈ Ioc b0 L, f u l0 < 0) (hpos : ∀ u ∈ Ico (b0 - δ1) b0, 0 < f u l0)
    (hder : f1 b0 l0 < 0) :
    ∃ δ c0 : ℝ, 0 < δ ∧ δ ≤ δ1 ∧ 0 < c0 ∧ ∃ W : Set Λ, IsOpen W ∧ l0 ∈ W ∧ ∃ b : Λ → ℝ,
      (∀ l ∈ W, ContinuousAt b l) ∧
      ∀ l ∈ W, b l ≤ L ∧ b0 - δ < b l ∧ f (b l) l = 0 ∧ (∀ u ∈ Ioc (b l) L, f u l < 0) ∧
        ∀ u ∈ Icc (b0 - δ) (b l), c0 * (b l - u) ≤ f u l := by
  have hmaps : MapsTo (fun p : ℝ × Λ => (L - p.1, p.2)) (Icc 0 L ×ˢ univ) (Icc 0 L ×ˢ univ) := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩, mem_univ _⟩
  have hcont : Continuous (fun p : ℝ × Λ => (L - p.1, p.2)) := by fun_prop
  have hc' : ContinuousOn (fun p : ℝ × Λ => f (L - p.1) p.2) (Icc 0 L ×ˢ univ) :=
    hc.comp hcont.continuousOn hmaps
  have hc1' : ContinuousOn (fun p : ℝ × Λ => -f1 (L - p.1) p.2) (Icc 0 L ×ˢ univ) :=
    (hc1.comp hcont.continuousOn hmaps).neg
  have hd' : ∀ l, ∀ u ∈ Icc 0 L, HasDerivWithinAt (fun v => f (L - v) l) (-f1 (L - u) l) (Icc 0 L) u := by
    intro l u hu
    have h1 : HasDerivWithinAt (fun v : ℝ => L - v) (-1) (Icc 0 L) u :=
      ((hasDerivWithinAt_id u (Icc 0 L)).const_sub L)
    have h2 := (hd l (L - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩).scomp u h1
      (fun v hv => ⟨by linarith [hv.2], by linarith [hv.1]⟩)
    simpa [Function.comp_def] using h2
  obtain ⟨δ, c0, hδ, hδδ1, hc0, W, hWo, hl0W, a, hac, ha0, hprop⟩ :=
    end_left (f := fun u l => f (L - u) l) (f1 := fun u l => -f1 (L - u) l) (l0 := l0) (a0 := L - b0) (δ1 := δ1)
      hc' hd' hc1' (fun l => by simpa using hL l) (by linarith) hδ1 (by linarith)
      (by simpa using hz)
      (fun u hu => hneg (L - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩)
      (fun u hu => hpos (L - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩)
      (by simpa using hder)
  refine ⟨δ, c0, hδ, hδδ1, hc0, W, hWo, hl0W, fun l => L - a l, fun l hl => continuousAt_const.sub (hac l hl), ?_⟩
  intro l hl
  obtain ⟨h1, h2, h3, h4, h5⟩ := hprop l hl
  refine ⟨by linarith, by linarith, by simpa using h3, ?_, ?_⟩
  · intro u hu
    have := h4 (L - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
    simpa using this
  · intro u hu
    have := h5 (L - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have e : L - u - a l = L - a l - u := by ring
    simpa [e] using this

/-- **Stable simple-zero structure** of a family `f(., l)` of functions on `[0, L]`: if at `l0` the set `{f >= 0}` is `[a0, b0]` with
`f > 0` inside and simple zeros at the ends, then for `l` near `l0` it is `[a l, b l]` with continuous end points, and `f >= c (u - a)(b - u)` on it. -/
lemma stable_structure {L : ℝ} {f f1 : ℝ → Λ → ℝ} {l0 : Λ} {a0 b0 : ℝ}
    (hc : ContinuousOn (fun p : ℝ × Λ => f p.1 p.2) (Icc 0 L ×ˢ univ))
    (hd : ∀ l, ∀ u ∈ Icc 0 L, HasDerivWithinAt (fun v => f v l) (f1 u l) (Icc 0 L) u)
    (hc1 : ContinuousOn (fun p : ℝ × Λ => f1 p.1 p.2) (Icc 0 L ×ˢ univ))
    (h0 : ∀ l, f 0 l ≤ 0) (hL : ∀ l, f L l ≤ 0) (ha0 : 0 ≤ a0) (hab : a0 < b0) (hb0 : b0 ≤ L)
    (hza : f a0 l0 = 0) (hzb : f b0 l0 = 0)
    (hneg : ∀ u ∈ Icc 0 L, u ∉ Icc a0 b0 → f u l0 < 0) (hpos : ∀ u ∈ Ioo a0 b0, 0 < f u l0)
    (hda : 0 < f1 a0 l0) (hdb : f1 b0 l0 < 0) :
    ∃ V : Set Λ, IsOpen V ∧ l0 ∈ V ∧ ∃ a b : Λ → ℝ, ∃ c : ℝ, 0 < c ∧
      (∀ l ∈ V, ContinuousAt a l ∧ ContinuousAt b l) ∧
      ∀ l ∈ V, 0 ≤ a l ∧ a l < b l ∧ b l ≤ L ∧ f (a l) l = 0 ∧ f (b l) l = 0 ∧
        (∀ u ∈ Icc 0 L, 0 ≤ f u l ↔ u ∈ Icc (a l) (b l)) ∧
        ∀ u ∈ Icc (a l) (b l), c * ((u - a l) * (b l - u)) ≤ f u l := by
  have hL0 : 0 < L := by linarith
  have hδ1 : 0 < (b0 - a0) / 3 := by linarith
  obtain ⟨δa, ca, hδa, hδa1, hca, Wa, hWao, hl0Wa, a, hac, -, hpa⟩ :=
    end_left hc hd hc1 h0 ha0 hδ1 (by linarith) hza
      (fun u hu => hneg u ⟨hu.1, by linarith [hu.2]⟩ (fun h => by linarith [h.1, hu.2]))
      (fun u hu => hpos u ⟨hu.1, by linarith [hu.2]⟩) hda
  obtain ⟨δb, cb, hδb, hδb1, hcb, Wb, hWbo, hl0Wb, b, hbc, hpb⟩ :=
    end_right hc hd hc1 hL hb0 hδ1 (by linarith) hzb
      (fun u hu => hneg u ⟨by linarith [hu.1], hu.2⟩ (fun h => by linarith [h.2, hu.1]))
      (fun u hu => hpos u ⟨by linarith [hu.1], hu.2⟩) hdb
  -- middle part
  set K := Icc (a0 + δa) (b0 - δb) with hK
  have hKne : (a0 + δa) ≤ (b0 - δb) := by linarith
  have hKsub : K ⊆ Ioo a0 b0 := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hKL : K ⊆ Icc 0 L := fun u hu => ⟨by linarith [hu.1, hδa], by linarith [hu.2, hδb]⟩
  have hcl0 : ContinuousOn (fun u => f u l0) K := fun u hu => ((hd l0 u (hKL hu)).continuousWithinAt).mono hKL
  obtain ⟨u1, hu1K, hu1min⟩ := (isCompact_Icc : IsCompact K).exists_isMinOn ⟨a0 + δa, le_rfl, hKne⟩ hcl0
  set m := f u1 l0 with hm
  have hmpos : 0 < m := hpos u1 (hKsub hu1K)
  have EM : ∀ᶠ l in 𝓝 l0, ∀ u ∈ K, m / 2 < f u l :=
    ev_forall_gt isCompact_Icc hKL hc (fun u hu => by have h' : m ≤ f u l0 := hu1min hu; linarith)
  set V := Wa ∩ Wb ∩ interior {l | ∀ u ∈ K, m / 2 < f u l} with hV
  have hVo : IsOpen V := (hWao.inter hWbo).inter isOpen_interior
  have hl0V : l0 ∈ V := ⟨⟨hl0Wa, hl0Wb⟩, mem_interior_iff_mem_nhds.2 EM⟩
  refine ⟨V, hVo, hl0V, a, b, min (min (ca / L) (cb / L)) (m / (2 * L ^ 2)), ?_, ?_, ?_⟩
  · have := div_pos hca hL0
    exact lt_min (lt_min (div_pos hca hL0) (div_pos hcb hL0)) (by positivity)
  · intro l hl
    exact ⟨hac l hl.1.1, hbc l hl.1.2⟩
  · intro l hl
    obtain ⟨hl1, hl2⟩ := hl.1
    have hmid : ∀ u ∈ K, m / 2 < f u l := interior_subset hl.2
    obtain ⟨ha1, ha2, ha3, ha4, ha5⟩ := hpa l hl1
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hpb l hl2
    have hab' : a l < b l := by linarith
    have hbL : b l ≤ L := hb1
    have haL0 : 0 ≤ a l := ha1
    have hlow : ∀ u ∈ Icc (a l) (b l), 0 ≤ f u l := by
      intro u hu
      by_cases h1 : u ≤ a0 + δa
      · have := ha5 u ⟨hu.1, h1⟩
        nlinarith [hu.1]
      · by_cases h2 : b0 - δb ≤ u
        · have := hb5 u ⟨h2, hu.2⟩
          nlinarith [hu.2]
        · have := hmid u ⟨by linarith, by linarith⟩
          linarith
    refine ⟨ha1, hab', hbL, ha3, hb3, ?_, ?_⟩
    · intro u hu
      constructor
      · intro hfu
        constructor
        · by_contra h
          have := ha4 u ⟨hu.1, not_le.1 h⟩
          linarith
        · by_contra h
          have := hb4 u ⟨not_le.1 h, hu.2⟩
          linarith
      · intro h
        exact hlow u h
    · intro u hu
      have hP0 : 0 ≤ (u - a l) * (b l - u) := mul_nonneg (by linarith [hu.1]) (by linarith [hu.2])
      have hP1 : (u - a l) * (b l - u) ≤ (u - a l) * L := by
        apply mul_le_mul_of_nonneg_left _ (by linarith [hu.1])
        linarith [hu.1, hu.2, haL0]
      have hP2 : (u - a l) * (b l - u) ≤ L * (b l - u) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith [hu.2])
        linarith [hu.1, hu.2, hbL, haL0]
      have hP3 : (u - a l) * (b l - u) ≤ L * L := by
        calc (u - a l) * (b l - u) ≤ (u - a l) * L := hP1
          _ ≤ L * L := by
            apply mul_le_mul_of_nonneg_right _ hL0.le
            linarith [hu.1, hu.2, hbL, haL0]
      set c := min (min (ca / L) (cb / L)) (m / (2 * L ^ 2)) with hc
      have hc1 : c ≤ ca / L := le_trans (min_le_left _ _) (min_le_left _ _)
      have hc2 : c ≤ cb / L := le_trans (min_le_left _ _) (min_le_right _ _)
      have hc3 : c ≤ m / (2 * L ^ 2) := min_le_right _ _
      have hcpos : 0 ≤ c := le_min (le_min (div_pos hca hL0).le (div_pos hcb hL0).le) (by positivity)
      by_cases h1 : u ≤ a0 + δa
      · have := ha5 u ⟨hu.1, h1⟩
        have e1 : c * ((u - a l) * (b l - u)) ≤ (ca / L) * ((u - a l) * (b l - u)) :=
          mul_le_mul_of_nonneg_right hc1 hP0
        have e2 : (ca / L) * ((u - a l) * (b l - u)) ≤ (ca / L) * ((u - a l) * L) :=
          mul_le_mul_of_nonneg_left hP1 (div_pos hca hL0).le
        have e3 : (ca / L) * ((u - a l) * L) = ca * (u - a l) := by field_simp
        linarith
      · by_cases h2 : b0 - δb ≤ u
        · have := hb5 u ⟨h2, hu.2⟩
          have e1 : c * ((u - a l) * (b l - u)) ≤ (cb / L) * ((u - a l) * (b l - u)) :=
            mul_le_mul_of_nonneg_right hc2 hP0
          have e2 : (cb / L) * ((u - a l) * (b l - u)) ≤ (cb / L) * (L * (b l - u)) :=
            mul_le_mul_of_nonneg_left hP2 (div_pos hcb hL0).le
          have e3 : (cb / L) * (L * (b l - u)) = cb * (b l - u) := by field_simp
          linarith
        · have hfu := hmid u ⟨by linarith, by linarith⟩
          have e1 : c * ((u - a l) * (b l - u)) ≤ (m / (2 * L ^ 2)) * ((u - a l) * (b l - u)) :=
            mul_le_mul_of_nonneg_right hc3 hP0
          have e2 : (m / (2 * L ^ 2)) * ((u - a l) * (b l - u)) ≤ (m / (2 * L ^ 2)) * (L * L) :=
            mul_le_mul_of_nonneg_left hP3 (by positivity)
          have e3 : (m / (2 * L ^ 2)) * (L * L) = m / 2 := by field_simp
          linarith

lemma intervalIntegrable_inv_sqrt {a b : ℝ} (hab : a < b) :
    IntervalIntegrable (fun u => (Real.sqrt ((u - a) * (b - u)))⁻¹) volume a b := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hcont : ContinuousOn (fun u => Real.arcsin ((2 * u - a - b) / (b - a))) (uIcc a b) :=
    (Real.continuous_arcsin.comp (by fun_prop)).continuousOn
  refine intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := fun u => Real.arcsin ((2 * u - a - b) / (b - a))) hcont ?_ ?_
  · intro u hu
    rw [min_eq_left hab.le, max_eq_right hab.le] at hu
    have hw : HasDerivAt (fun u : ℝ => (2 * u - a - b) / (b - a)) (2 / (b - a)) u := by
      have := (((hasDerivAt_id u).const_mul 2).sub_const a |>.sub_const b).div_const (b - a)
      simpa using this
    have h1 : (2 * u - a - b) / (b - a) ≠ -1 := by
      intro h; rw [div_eq_iff hba.ne'] at h; linarith [hu.1]
    have h2 : (2 * u - a - b) / (b - a) ≠ 1 := by
      intro h; rw [div_eq_iff hba.ne'] at h; linarith [hu.2]
    have := (Real.hasDerivAt_arcsin h1 h2).comp u hw
    refine this.congr_deriv ?_
    have hpos : 0 < (u - a) * (b - u) := mul_pos (by linarith [hu.1]) (by linarith [hu.2])
    have e : 1 - ((2 * u - a - b) / (b - a)) ^ 2 = 4 * ((u - a) * (b - u)) / (b - a) ^ 2 := by
      field_simp
      ring
    rw [e, Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hba.le]
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    rw [h4]
    have hs : 0 < Real.sqrt ((u - a) * (b - u)) := Real.sqrt_pos.2 hpos
    field_simp
  · intro u hu
    rw [min_eq_left hab.le, max_eq_right hab.le] at hu
    exact inv_nonneg.2 (Real.sqrt_nonneg _)

lemma cont_slice {L : ℝ} {g : ℝ → Λ → ℝ} (hg : ContinuousOn (fun p : ℝ × Λ => g p.1 p.2) (Icc 0 L ×ˢ univ)) (l : Λ) :
    ContinuousOn (fun u => g u l) (Icc 0 L) :=
  hg.comp (continuous_id.prodMk continuous_const).continuousOn (fun u hu => ⟨hu, mem_univ _⟩)

lemma contAt_comp_path {L : ℝ} {g : ℝ → Λ → ℝ} (hg : ContinuousOn (fun p : ℝ × Λ => g p.1 p.2) (Icc 0 L ×ˢ univ))
    {x : Λ} {u : Λ → ℝ} (hu : ContinuousAt u x) (huS : ∀ᶠ l in 𝓝 x, u l ∈ Icc 0 L) :
    ContinuousAt (fun l => g (u l) l) x := by
  have hx : u x ∈ Icc 0 L := huS.self_of_nhds
  have h1 : Tendsto (fun l => (u l, l)) (𝓝 x) (𝓝[Icc 0 L ×ˢ (univ : Set Λ)] (u x, x)) :=
    tendsto_nhdsWithin_iff.2 ⟨hu.prodMk continuousAt_id |>.tendsto, huS.mono fun l hl => ⟨hl, mem_univ _⟩⟩
  exact (hg (u x, x) ⟨hx, mem_univ _⟩).tendsto.comp h1

/-- **Continuity of `l -> int_0^L q(u,l) / sqrt(f(u,l)) du`** across a family with the stable structure `[a l, b l]`, `f >= c (u-a)(b-u)`. -/
lemma integral_inv_sqrt_continuousAt [FirstCountableTopology Λ] {L : ℝ} {f : ℝ → Λ → ℝ} {q : ℝ → Λ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × Λ => f p.1 p.2) (Icc 0 L ×ˢ univ))
    (hq : ContinuousOn (fun p : ℝ × Λ => q p.1 p.2) (Icc 0 L ×ˢ univ))
    {V : Set Λ} {a b : Λ → ℝ} {c : ℝ} (hc0 : 0 < c) (hVo : IsOpen V)
    (hab : ∀ l ∈ V, ContinuousAt a l ∧ ContinuousAt b l)
    (hprop : ∀ l ∈ V, 0 ≤ a l ∧ a l < b l ∧ b l ≤ L ∧ f (a l) l = 0 ∧ f (b l) l = 0 ∧
        (∀ u ∈ Icc 0 L, 0 ≤ f u l ↔ u ∈ Icc (a l) (b l)) ∧
        ∀ u ∈ Icc (a l) (b l), c * ((u - a l) * (b l - u)) ≤ f u l) :
    ∀ l ∈ V, IntervalIntegrable (fun u => q u l / Real.sqrt (f u l)) volume 0 L ∧
      ContinuousAt (fun l => ∫ u in (0 : ℝ)..L, q u l / Real.sqrt (f u l)) l := by
  intro l1 hl1
  -- vanishing outside `(a, b)`
  have hzero : ∀ l ∈ V, ∀ u ∈ Icc 0 L, u ∉ Ioo (a l) (b l) → q u l / Real.sqrt (f u l) = 0 := by
    intro l hl u hu hnot
    obtain ⟨-, hab', -, hfa, hfb, hiff, -⟩ := hprop l hl
    have hf : f u l ≤ 0 := by
      by_cases hmem : u ∈ Icc (a l) (b l)
      · have : u = a l ∨ u = b l := by
          rcases hmem.1.lt_or_eq with h1 | h1
          · rcases hmem.2.lt_or_eq with h2 | h2
            · exact absurd ⟨h1, h2⟩ hnot
            · exact Or.inr h2
          · exact Or.inl h1.symm
        rcases this with rfl | rfl
        · exact hfa.le
        · exact hfb.le
      · exact (not_le.1 (fun h => hmem ((hiff u hu).1 h))).le
    rw [Real.sqrt_eq_zero_of_nonpos hf, div_zero]
  -- positivity inside
  have hposin : ∀ l ∈ V, ∀ u ∈ Ioo (a l) (b l), 0 < f u l := by
    intro l hl u hu
    obtain ⟨-, -, -, -, -, -, hlow⟩ := hprop l hl
    have := hlow u ⟨hu.1.le, hu.2.le⟩
    have hp : 0 < c * ((u - a l) * (b l - u)) :=
      mul_pos hc0 (mul_pos (by linarith [hu.1]) (by linarith [hu.2]))
    linarith
  -- continuity of `F l` inside
  have hFcont : ∀ l ∈ V, ContinuousOn (fun u => q u l / Real.sqrt (f u l)) (Ioo (a l) (b l)) := by
    intro l hl
    obtain ⟨ha0, hab', hbL, -⟩ := hprop l hl
    have hsub : Ioo (a l) (b l) ⊆ Icc 0 L := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hf : ContinuousOn (fun u => f u l) (Icc 0 L) := cont_slice hc l
    refine ((cont_slice hq l).mono hsub).div
      (Real.continuous_sqrt.comp_continuousOn (hf.mono hsub)) (fun u hu => ?_)
    exact (Real.sqrt_pos.2 (hposin l hl u hu)).ne'
  -- integrability for each `l ∈ V`
  have hint : ∀ l ∈ V, IntervalIntegrable (fun u => q u l / Real.sqrt (f u l)) volume 0 L := by
    intro l hl
    obtain ⟨ha0, hab', hbL, -⟩ := hprop l hl
    have hL0 : 0 ≤ L := by linarith
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL0]
    obtain ⟨Q, hQ⟩ := (isCompact_Icc (a := (0:ℝ)) (b := L)).exists_bound_of_continuousOn (cont_slice hq l)
    have hg := (intervalIntegrable_inv_sqrt hab').const_mul (Q / Real.sqrt c)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab'.le] at hg
    have hIoo : IntegrableOn (fun u => q u l / Real.sqrt (f u l)) (Ioo (a l) (b l)) := by
      refine Integrable.mono' (hg.mono_set Ioo_subset_Ioc_self) ?_ ?_
      · exact (hFcont l hl).aestronglyMeasurable measurableSet_Ioo
      · rw [ae_restrict_iff' measurableSet_Ioo]
        refine Eventually.of_forall fun u hu => ?_
        obtain ⟨-, -, -, -, -, -, hlow⟩ := hprop l hl
        have hu' : u ∈ Icc 0 L := ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have hfu := hlow u ⟨hu.1.le, hu.2.le⟩
        have hP : 0 < (u - a l) * (b l - u) := mul_pos (by linarith [hu.1]) (by linarith [hu.2])
        have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
        have hsP : 0 < Real.sqrt ((u - a l) * (b l - u)) := Real.sqrt_pos.2 hP
        have h1 : Real.sqrt c * Real.sqrt ((u - a l) * (b l - u)) ≤ Real.sqrt (f u l) := by
          rw [← Real.sqrt_mul hc0.le]
          exact Real.sqrt_le_sqrt hfu
        have h2 : 0 < Real.sqrt (f u l) := lt_of_lt_of_le (by positivity) h1
        rw [Real.norm_eq_abs, abs_div, abs_of_pos h2]
        have h3 : |q u l| ≤ Q := by simpa using hQ u hu'
        calc |q u l| / Real.sqrt (f u l) ≤ Q / (Real.sqrt c * Real.sqrt ((u - a l) * (b l - u))) := by
              apply div_le_div₀ ((abs_nonneg _).trans h3) h3 (by positivity) h1
          _ = Q / Real.sqrt c * (Real.sqrt ((u - a l) * (b l - u)))⁻¹ := by
              field_simp
    refine IntegrableOn.of_forall_sdiff_eq_zero (s := Ioo (a l) (b l)) hIoo measurableSet_Ioc ?_
    intro u hu
    exact hzero l hl u ⟨hu.1.1.le, hu.1.2⟩ hu.2
  refine ⟨hint l1 hl1, ?_⟩
  have hVn : V ∈ 𝓝 l1 := hVo.mem_nhds hl1
  have hrep : ∀ l ∈ V, ∫ u in (0 : ℝ)..L, q u l / Real.sqrt (f u l) =
      ∫ s in (0 : ℝ)..1, (b l - a l) * (q ((b l - a l) * s + a l) l / Real.sqrt (f ((b l - a l) * s + a l) l)) := by
    intro l hl
    obtain ⟨ha0, hab', hbL, -⟩ := hprop l hl
    have h1 : ∫ u in (0 : ℝ)..L, q u l / Real.sqrt (f u l) = ∫ u in a l..b l, q u l / Real.sqrt (f u l) := by
      rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le hab'.le]
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc (Ioc_subset_Ioc ha0 hbL) ?_
      intro u hu
      exact hzero l hl u ⟨hu.1.1.le, hu.1.2⟩ (fun h => hu.2 ⟨h.1, h.2.le⟩)
    rw [h1]
    have := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
      (f := fun u => q u l / Real.sqrt (f u l)) (b l - a l) (a l)
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul] at this
    rw [← this, intervalIntegral.integral_const_mul]
  -- uniform bound for `q`
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_bound_of_continuousOn (cont_slice hq l1)
  have hL0 : 0 ≤ L := by
    obtain ⟨ha0, hab', hbL, -⟩ := hprop l1 hl1
    linarith
  have hC0nn : 0 ≤ C0 := (norm_nonneg _).trans (hC0 0 ⟨le_rfl, hL0⟩)
  have EQ1 : ∀ᶠ l in 𝓝 l1, ∀ u ∈ Icc 0 L, q u l < C0 + 1 :=
    ev_forall_lt isCompact_Icc subset_rfl hq (fun u hu => by
      have := hC0 u hu; rw [Real.norm_eq_abs] at this; linarith [le_abs_self (q u l1)])
  have EQ2 : ∀ᶠ l in 𝓝 l1, ∀ u ∈ Icc 0 L, -q u l < C0 + 1 :=
    ev_forall_lt (f := fun u l => -q u l) isCompact_Icc subset_rfl hq.neg (fun u hu => by
      have := hC0 u hu; rw [Real.norm_eq_abs] at this
      show -q u l1 < C0 + 1
      linarith [neg_abs_le (q u l1)])
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
  have hbint : IntervalIntegrable (fun s : ℝ => (C0 + 1) / Real.sqrt c * (Real.sqrt ((s - 0) * (1 - s)))⁻¹)
      volume 0 1 := (intervalIntegrable_inv_sqrt zero_lt_one).const_mul _
  have hmeas : ∀ l ∈ V, AEStronglyMeasurable
      (fun s => (b l - a l) * (q ((b l - a l) * s + a l) l / Real.sqrt (f ((b l - a l) * s + a l) l)))
      (volume.restrict (Ι (0 : ℝ) 1)) := by
    intro l hl
    obtain ⟨ha0, hab', hbL, -⟩ := hprop l hl
    have hmaps : MapsTo (fun s : ℝ => (b l - a l) * s + a l) (Ioo 0 1) (Ioo (a l) (b l)) := by
      intro s hs
      constructor
      · nlinarith [hs.1]
      · nlinarith [hs.2]
    have hcon : ContinuousOn (fun s : ℝ => (b l - a l) * (q ((b l - a l) * s + a l) l /
        Real.sqrt (f ((b l - a l) * s + a l) l))) (Ioo 0 1) :=
      continuousOn_const.mul ((hFcont l hl).comp (by fun_prop) hmaps)
    have h1 := hcon.aestronglyMeasurable (μ := volume) measurableSet_Ioo
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc, ← Set.uIoc_of_le zero_le_one] at h1
  have hbd : ∀ᶠ l in 𝓝 l1, ∀ᵐ s ∂volume, s ∈ Ι (0 : ℝ) 1 →
      ‖(b l - a l) * (q ((b l - a l) * s + a l) l / Real.sqrt (f ((b l - a l) * s + a l) l))‖ ≤
        (C0 + 1) / Real.sqrt c * (Real.sqrt ((s - 0) * (1 - s)))⁻¹ := by
    filter_upwards [hVn, EQ1, EQ2] with l hl e1 e2
    filter_upwards [(Set.countable_singleton (1 : ℝ)).ae_notMem volume] with s hs1 hsI
    rw [Set.uIoc_of_le zero_le_one] at hsI
    have hs1' : s < 1 := lt_of_le_of_ne hsI.2 (fun h => hs1 (by simp [h]))
    obtain ⟨ha0, hab', hbL, -, -, -, hlow⟩ := hprop l hl
    set w := b l - a l with hw
    have hwpos : 0 < w := by rw [hw]; linarith
    set u := w * s + a l with hu
    have hua : u - a l = w * s := by rw [hu]; ring
    have hbu : b l - u = w * (1 - s) := by rw [hu, hw]; ring
    have huI : u ∈ Icc (a l) (b l) := ⟨by nlinarith [hsI.1], by nlinarith⟩
    have hu0 : u ∈ Icc 0 L := ⟨by linarith [huI.1], by linarith [huI.2]⟩
    have hfu := hlow u huI
    have hP : (u - a l) * (b l - u) = w ^ 2 * (s * (1 - s)) := by rw [hua, hbu]; ring
    have hsP : 0 < s * (1 - s) := mul_pos hsI.1 (by linarith)
    have hsqP : Real.sqrt ((u - a l) * (b l - u)) = w * Real.sqrt (s * (1 - s)) := by
      rw [hP, Real.sqrt_mul (sq_nonneg w), Real.sqrt_sq hwpos.le]
    have h1 : Real.sqrt c * (w * Real.sqrt (s * (1 - s))) ≤ Real.sqrt (f u l) := by
      rw [← hsqP, ← Real.sqrt_mul hc0.le]
      exact Real.sqrt_le_sqrt hfu
    have hss : 0 < Real.sqrt (s * (1 - s)) := Real.sqrt_pos.2 hsP
    have h2 : 0 < Real.sqrt (f u l) := lt_of_lt_of_le (by positivity) h1
    have h3 : |q u l| ≤ C0 + 1 := abs_le.2 ⟨by linarith [e2 u hu0], (e1 u hu0).le⟩
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos h2, abs_of_pos hwpos, sub_zero]
    calc w * (|q u l| / Real.sqrt (f u l)) ≤ w * ((C0 + 1) / (Real.sqrt c * (w * Real.sqrt (s * (1 - s))))) := by
          apply mul_le_mul_of_nonneg_left _ hwpos.le
          exact div_le_div₀ ((abs_nonneg _).trans h3) h3 (by positivity) h1
      _ = (C0 + 1) / Real.sqrt c * (Real.sqrt (s * (1 - s)))⁻¹ := by field_simp
  have hct : ∀ᵐ s ∂volume, s ∈ Ι (0 : ℝ) 1 → ContinuousAt (fun l =>
      (b l - a l) * (q ((b l - a l) * s + a l) l / Real.sqrt (f ((b l - a l) * s + a l) l))) l1 := by
    filter_upwards [(Set.countable_singleton (1 : ℝ)).ae_notMem volume] with s hs1 hsI
    rw [Set.uIoc_of_le zero_le_one] at hsI
    have hs1' : s < 1 := lt_of_le_of_ne hsI.2 (fun h => hs1 (by simp [h]))
    obtain ⟨ha1, hb1⟩ := hab l1 hl1
    have hu : ContinuousAt (fun l => (b l - a l) * s + a l) l1 := ((hb1.sub ha1).mul continuousAt_const).add ha1
    have huS : ∀ᶠ l in 𝓝 l1, (b l - a l) * s + a l ∈ Icc 0 L := by
      filter_upwards [hVn] with l hl
      obtain ⟨ha0, hab', hbL, -⟩ := hprop l hl
      exact ⟨by nlinarith [hsI.1], by nlinarith [hsI.2]⟩
    have hq' := contAt_comp_path hq hu huS
    have hf' := contAt_comp_path hc hu huS
    obtain ⟨ha0, hab', hbL, -⟩ := hprop l1 hl1
    have hin : (b l1 - a l1) * s + a l1 ∈ Ioo (a l1) (b l1) := ⟨by nlinarith [hsI.1], by nlinarith⟩
    have hne : Real.sqrt (f ((b l1 - a l1) * s + a l1) l1) ≠ 0 := (Real.sqrt_pos.2 (hposin l1 hl1 _ hin)).ne'
    exact (hb1.sub ha1).mul (hq'.div hf'.sqrt hne)
  have hDCT := intervalIntegral.continuousAt_of_dominated_interval
    (F := fun l s => (b l - a l) * (q ((b l - a l) * s + a l) l / Real.sqrt (f ((b l - a l) * s + a l) l)))
    (x₀ := l1) (bound := fun s : ℝ => (C0 + 1) / Real.sqrt c * (Real.sqrt ((s - 0) * (1 - s)))⁻¹)
    (a := 0) (b := 1) (μ := volume)
    (Filter.eventually_of_mem hVn hmeas) hbd hbint hct
  refine hDCT.congr ?_
  filter_upwards [hVn] with l hl
  exact (hrep l hl).symm


/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.stable_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.stable_structure

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.integral_inv_sqrt_continuousAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.integral_inv_sqrt_continuousAt

end FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv
