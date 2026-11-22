module

public import FormalResearch.Complex.StripPoisson
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Total-Variation Product Helpers and Prefactor Bounds for Band Reduction (Proposition TE.3(1))

Source: `CFT/common/two_edge_bootstrap.tex` (Proposition `TE.3` `teb:mellin`, proof of `(1)`,
l.460–471).

* `eVariationOn_mul_le`, `bv_norm_add_tv_mul`: submultiplicativity of `‖f‖_∞ + TV(f)` on an
  interval `Icc a b`.
* `eVariationOn_unimodal_Icc_le`: `TV_J(f) ≤ 2` on `J ⊆ (0, ∞)` for `0 ≤ f ≤ 1` unimodal on
  `Ioi 0`.
* `eVariationOn_le_of_hasDerivAt_le`, `eVariationOn_le_integral_norm_deriv`: TV bounds from
  pointwise or integrable derivatives on `Icc a b`.
* `tebCutoff`, `tebPrefactor`, `tebAmp0`: the cutoff `χ`, strip prefactor
  `c^{5/6} (ζ(1 - ζ))^{5/2} e^{-ζ(1 - ζ)}`, and boundary factor `𝒜₀(τ)` with uniform `BV` bounds
  on dyadic blocks `[s, 2s]`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.StripBand

open FormalResearch.StripPoisson

section BVHelpers

lemma eVariationOn_ofReal (f : ℝ → ℝ) (S : Set ℝ) :
    eVariationOn (fun x => (f x : ℂ)) S = eVariationOn f S := by
  simp only [eVariationOn, edist_dist, Complex.dist_eq, ← Complex.ofReal_sub,
    Complex.norm_real, Real.dist_eq, Real.norm_eq_abs]

lemma eVariationOn_comp_neg (f : ℝ → ℝ) :
    eVariationOn (fun τ => f (-τ)) univ ≤ eVariationOn f univ := by
  refine iSup_le fun ⟨n, u, hu, _⟩ => ?_
  let v : ℕ → ℝ := fun i => if i ≤ n then -u (n - i) else -u 0
  have hv_mono : Monotone v := by
    intro i j hij
    dsimp [v]
    split_ifs with hi hj hj
    · exact neg_le_neg (hu (by omega))
    · exact neg_le_neg (hu (by omega))
    · exfalso; omega
    · exact le_rfl
  have hsum : ∑ i ∈ Finset.range n, edist (f (-u (i + 1))) (f (-u i)) =
      ∑ j ∈ Finset.range n, edist (f (v (j + 1))) (f (v j)) := by
    rw [← Finset.sum_range_reflect (fun i => edist (f (-u (i + 1))) (f (-u i))) n]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_lt : j < n := Finset.mem_range.mp hj
    have hv1 : v (j + 1) = -u (n - (j + 1)) := by
      simp only [v, show j + 1 ≤ n by omega, ↓reduceIte]
    have hv0 : v j = -u (n - j) := by
      simp only [v, show j ≤ n by omega, ↓reduceIte]
    have h1 : n - 1 - j + 1 = n - j := by omega
    have h2 : n - 1 - j = n - (j + 1) := by omega
    rw [hv1, hv0, edist_comm, h1, h2]
  rw [hsum]
  exact eVariationOn.sum_le hv_mono (fun _ => mem_univ _)

/-- Submultiplicativity of `eVariationOn` for `ℂ`-valued functions bounded on `S`. -/
lemma eVariationOn_mul_le {f g : ℝ → ℂ} {S : Set ℝ} {Mf Mg : ℝ}
    (hf : ∀ x ∈ S, ‖f x‖ ≤ Mf) (hg : ∀ x ∈ S, ‖g x‖ ≤ Mg) :
    eVariationOn (fun x => f x * g x) S ≤
      ENNReal.ofReal Mf * eVariationOn g S + ENNReal.ofReal Mg * eVariationOn f S := by
  refine iSup_le fun ⟨n, u, hu, hus⟩ => ?_
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) * g (u (i + 1))) (f (u i) * g (u i))
      ≤ ∑ i ∈ Finset.range n,
          (ENNReal.ofReal Mf * edist (g (u (i + 1))) (g (u i)) +
            ENNReal.ofReal Mg * edist (f (u (i + 1))) (f (u i))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [edist_dist, edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, dist_eq_norm]
        have hid : f (u (i + 1)) * g (u (i + 1)) - f (u i) * g (u i) =
            f (u (i + 1)) * (g (u (i + 1)) - g (u i)) + (f (u (i + 1)) - f (u i)) * g (u i) := by
          ring
        have hnorm : ‖f (u (i + 1)) * g (u (i + 1)) - f (u i) * g (u i)‖ ≤
            Mf * ‖g (u (i + 1)) - g (u i)‖ + Mg * ‖f (u (i + 1)) - f (u i)‖ := by
          rw [hid]
          calc ‖f (u (i + 1)) * (g (u (i + 1)) - g (u i)) + (f (u (i + 1)) - f (u i)) * g (u i)‖
              ≤ ‖f (u (i + 1)) * (g (u (i + 1)) - g (u i))‖ +
                  ‖(f (u (i + 1)) - f (u i)) * g (u i)‖ := norm_add_le _ _
            _ = ‖f (u (i + 1))‖ * ‖g (u (i + 1)) - g (u i)‖ +
                  ‖f (u (i + 1)) - f (u i)‖ * ‖g (u i)‖ := by rw [norm_mul, norm_mul]
            _ ≤ Mf * ‖g (u (i + 1)) - g (u i)‖ + ‖f (u (i + 1)) - f (u i)‖ * Mg := by
                  gcongr
                  · exact hf _ (hus _)
                  · exact hg _ (hus _)
            _ = Mf * ‖g (u (i + 1)) - g (u i)‖ + Mg * ‖f (u (i + 1)) - f (u i)‖ := by ring
        have hMf_nn : 0 ≤ Mf := (norm_nonneg _).trans (hf _ (hus 0))
        have hMg_nn : 0 ≤ Mg := (norm_nonneg _).trans (hg _ (hus 0))
        calc ENNReal.ofReal ‖f (u (i + 1)) * g (u (i + 1)) - f (u i) * g (u i)‖
            ≤ ENNReal.ofReal (Mf * ‖g (u (i + 1)) - g (u i)‖ +
                Mg * ‖f (u (i + 1)) - f (u i)‖) := ENNReal.ofReal_le_ofReal hnorm
          _ = ENNReal.ofReal Mf * ENNReal.ofReal ‖g (u (i + 1)) - g (u i)‖ +
                ENNReal.ofReal Mg * ENNReal.ofReal ‖f (u (i + 1)) - f (u i)‖ := by
              rw [ENNReal.ofReal_add (by positivity) (by positivity),
                ENNReal.ofReal_mul hMf_nn, ENNReal.ofReal_mul hMg_nn]
    _ = ENNReal.ofReal Mf * ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) +
          ENNReal.ofReal Mg * ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ ENNReal.ofReal Mf * eVariationOn g S + ENNReal.ofReal Mg * eVariationOn f S := by
        gcongr <;> exact eVariationOn.sum_le hu hus

/-- Submultiplicativity of the BV norm `sup ‖·‖ + TV(·)` for `ℂ`-valued functions on `S`. -/
lemma bv_norm_add_tv_mul {f g : ℝ → ℂ} {S : Set ℝ} {Mf Mg Vf Vg : ℝ}
    (hMf : 0 ≤ Mf) (hMg : 0 ≤ Mg) (hVf : 0 ≤ Vf) (hVg : 0 ≤ Vg)
    (hf_bd : ∀ x ∈ S, ‖f x‖ ≤ Mf) (hg_bd : ∀ x ∈ S, ‖g x‖ ≤ Mg)
    (hf_bv : eVariationOn f S ≤ ENNReal.ofReal Vf)
    (hg_bv : eVariationOn g S ≤ ENNReal.ofReal Vg) :
    BoundedVariationOn (fun x => f x * g x) S ∧
    eVariationOn (fun x => f x * g x) S ≤ ENNReal.ofReal (Mf * Vg + Mg * Vf) ∧
    ∀ x ∈ S, ‖f x * g x‖ + (eVariationOn (fun y => f y * g y) S).toReal ≤
      (Mf + Vf) * (Mg + Vg) := by
  have hmul_bv : eVariationOn (fun x => f x * g x) S ≤ ENNReal.ofReal (Mf * Vg + Mg * Vf) := by
    calc eVariationOn (fun x => f x * g x) S
        ≤ ENNReal.ofReal Mf * eVariationOn g S + ENNReal.ofReal Mg * eVariationOn f S :=
          eVariationOn_mul_le hf_bd hg_bd
      _ ≤ ENNReal.ofReal Mf * ENNReal.ofReal Vg + ENNReal.ofReal Mg * ENNReal.ofReal Vf := by
          gcongr
      _ = ENNReal.ofReal (Mf * Vg + Mg * Vf) := by
          rw [← ENNReal.ofReal_mul hMf, ← ENNReal.ofReal_mul hMg,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hbv : BoundedVariationOn (fun x => f x * g x) S :=
    ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne hmul_bv
  refine ⟨hbv, hmul_bv, fun x hx => ?_⟩
  have hnorm : ‖f x * g x‖ ≤ Mf * Mg := by
    rw [norm_mul]
    exact mul_le_mul (hf_bd x hx) (hg_bd x hx) (norm_nonneg _) hMf
  have htv : (eVariationOn (fun y => f y * g y) S).toReal ≤ Mf * Vg + Mg * Vf :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hmul_bv
  nlinarith [mul_nonneg hVf hVg]

/-- Unimodal `[0, 1]`-valued function on `Ioi 0` has variation `≤ 2` on `Icc a b` (`0 < a ≤ b`). -/
lemma eVariationOn_unimodal_Icc_le {f : ℝ → ℝ} {a b τ_p : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x) (hf1 : ∀ x ∈ Icc a b, f x ≤ 1)
    (hmono : MonotoneOn f (Ioi 0 ∩ Iic τ_p)) (hanti : AntitoneOn f (Ioi 0 ∩ Ici τ_p)) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal 2 := by
  have hIcc_pos : Icc a b ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  rcases le_or_gt b τ_p with hbτ | hτb
  · have hm : MonotoneOn f (Icc a b) := hmono.mono fun x hx => ⟨hIcc_pos hx, hx.2.trans hbτ⟩
    have hev := hm.eVariationOn_eq (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    rw [inter_self] at hev
    rw [hev]
    exact ENNReal.ofReal_le_ofReal (by linarith [hf0 a (left_mem_Icc.mpr hab), hf1 b (right_mem_Icc.mpr hab)])
  · rcases le_or_gt τ_p a with hτa | haτ
    · have ha' : AntitoneOn f (Icc a b) := hanti.mono fun x hx => ⟨hIcc_pos hx, hτa.trans hx.1⟩
      have hm : MonotoneOn (-f) (Icc a b) := fun x hx y hy hxy => neg_le_neg (ha' hx hy hxy)
      have hev : eVariationOn f (Icc a b) = eVariationOn (-f) (Icc a b) := by
        simp only [eVariationOn, Pi.neg_apply, edist_neg_neg]
      have hev1 := hm.eVariationOn_eq (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
      rw [inter_self] at hev1
      rw [hev, hev1]
      simp only [Pi.neg_apply, neg_sub_neg]
      exact ENNReal.ofReal_le_ofReal (by linarith [hf1 a (left_mem_Icc.mpr hab), hf0 b (right_mem_Icc.mpr hab)])
    · have hmem : τ_p ∈ Icc a b := ⟨haτ.le, hτb.le⟩
      have hsplit := eVariationOn.Icc_add_Icc f haτ.le hτb.le hmem
      have hI1 : Icc a b ∩ Icc a τ_p = Icc a τ_p := inter_eq_right.mpr (Icc_subset_Icc_right hτb.le)
      have hI2 : Icc a b ∩ Icc τ_p b = Icc τ_p b := inter_eq_right.mpr (Icc_subset_Icc_left haτ.le)
      rw [inter_self, hI1, hI2] at hsplit
      have hm1 : MonotoneOn f (Icc a τ_p) := hmono.mono fun x hx => ⟨lt_of_lt_of_le ha hx.1, hx.2⟩
      have ha2 : AntitoneOn f (Icc τ_p b) := hanti.mono fun x hx => ⟨lt_of_lt_of_le ha (haτ.le.trans hx.1), hx.1⟩
      have hm2 : MonotoneOn (-f) (Icc τ_p b) := fun x hx y hy hxy => neg_le_neg (ha2 hx hy hxy)
      have hev2 : eVariationOn f (Icc τ_p b) = eVariationOn (-f) (Icc τ_p b) := by
        simp only [eVariationOn, Pi.neg_apply, edist_neg_neg]
      have hev1' := hm1.eVariationOn_eq (left_mem_Icc.mpr haτ.le) (right_mem_Icc.mpr haτ.le)
      have hev2' := hm2.eVariationOn_eq (left_mem_Icc.mpr hτb.le) (right_mem_Icc.mpr hτb.le)
      rw [inter_self] at hev1' hev2'
      rw [← hsplit, hev1', hev2, hev2']
      simp only [Pi.neg_apply, neg_sub_neg]
      have hd1 : 0 ≤ f τ_p - f a := sub_nonneg.mpr (hm1 (left_mem_Icc.mpr haτ.le) (right_mem_Icc.mpr haτ.le) haτ.le)
      have hd2 : 0 ≤ f τ_p - f b := sub_nonneg.mpr (ha2 (left_mem_Icc.mpr hτb.le) (right_mem_Icc.mpr hτb.le) hτb.le)
      rw [← ENNReal.ofReal_add hd1 hd2]
      exact ENNReal.ofReal_le_ofReal (by
        linarith [hf0 a (left_mem_Icc.mpr hab), hf0 b (right_mem_Icc.mpr hab), hf1 τ_p hmem])

/-- TV bound on `Icc a b` from a uniform derivative bound `‖f' x‖ ≤ K`. -/
lemma eVariationOn_le_of_hasDerivAt_le {f f' : ℝ → ℂ} {a b K : ℝ} (_hab : a ≤ b) (hK : 0 ≤ K)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Icc a b, ‖f' x‖ ≤ K) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal (K * (b - a)) := by
  have hmv : ∀ x y : ℝ, x ∈ Icc a b → y ∈ Icc a b → x ≤ y → ‖f y - f x‖ ≤ K * (y - x) := by
    intro x y hx hy hxy
    have h_sub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
    have h1 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f') (C := K)
      (fun t ht => (hf t (h_sub ht)).hasDerivWithinAt) (fun t ht => hf' t (h_sub ht))
      (convex_Icc x y) (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
    simpa only [Real.norm_of_nonneg (sub_nonneg.mpr hxy)] using h1
  refine iSup_le fun ⟨n, u, hu, hus⟩ => ?_
  have hsum : ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ≤
      ∑ i ∈ Finset.range n, ENNReal.ofReal (K * (u (i + 1) - u i)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [edist_dist, dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal (hmv (u i) (u (i + 1)) (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
  have htele : ∑ i ∈ Finset.range n, ENNReal.ofReal (K * (u (i + 1) - u i)) =
      ENNReal.ofReal (K * (u n - u 0)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hK (sub_nonneg.mpr (hu (Nat.le_succ i))))]
    congr 1
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => u i)]
  refine hsum.trans (htele.symm ▸ ENNReal.ofReal_le_ofReal ?_)
  have hu0 : a ≤ u 0 := (hus 0).1
  have hun : u n ≤ b := (hus n).2
  exact mul_le_mul_of_nonneg_left (by linarith) hK

/-- TV bound on `Icc a b` from an integrable real derivative `g'`. -/
lemma eVariationOn_le_integral_abs_deriv {g g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x) (hg' : IntervalIntegrable g' volume a b) :
    eVariationOn g (Icc a b) ≤ ENNReal.ofReal (∫ t in a..b, |g' t|) := by
  have hg'_abs : IntervalIntegrable (fun t => |g' t|) volume a b := hg'.abs
  refine iSup_le fun ⟨n, u, hu, hus⟩ => ?_
  have hstep : ∀ i ∈ Finset.range n,
      edist (g (u (i + 1))) (g (u i)) ≤ ENNReal.ofReal (∫ t in u i..u (i + 1), |g' t|) := by
    intro i _
    have hui : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    have h_sub : Icc (u i) (u (i + 1)) ⊆ Icc a b := Icc_subset_Icc (hus i).1 (hus (i + 1)).2
    have hi_int : IntervalIntegrable g' volume (u i) (u (i + 1)) :=
      hg'.mono_set (by rw [uIcc_of_le hui, uIcc_of_le hab]; exact h_sub)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => by
      rw [uIcc_of_le hui] at hx; exact hg x (h_sub hx)) hi_int
    rw [edist_dist, Real.dist_eq, ← hftc]
    have hnorm : ‖∫ t in u i..u (i + 1), g' t‖ ≤ ∫ t in u i..u (i + 1), ‖g' t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hui
    simpa only [Real.norm_eq_abs] using ENNReal.ofReal_le_ofReal hnorm
  have hsum : ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) ≤
      ∑ i ∈ Finset.range n, ENNReal.ofReal (∫ t in u i..u (i + 1), |g' t|) :=
    Finset.sum_le_sum hstep
  have h_nn : ∀ i ∈ Finset.range n, 0 ≤ ∫ t in u i..u (i + 1), |g' t| := fun i _ =>
    intervalIntegral.integral_nonneg (hu (Nat.le_succ i)) (fun _ _ => abs_nonneg _)
  have htele : ∑ i ∈ Finset.range n, ENNReal.ofReal (∫ t in u i..u (i + 1), |g' t|) =
      ENNReal.ofReal (∫ t in u 0..u n, |g' t|) := by
    rw [← ENNReal.ofReal_sum_of_nonneg h_nn]
    congr 1
    exact intervalIntegral.sum_integral_adjacent_intervals fun i _ =>
      hg'_abs.mono_set (by
        rw [uIcc_of_le (hu (Nat.le_succ i)), uIcc_of_le hab]
        exact Icc_subset_Icc (hus i).1 (hus (i + 1)).2)
  refine hsum.trans (htele.symm ▸ ENNReal.ofReal_le_ofReal ?_)
  exact intervalIntegral.integral_mono_interval (hus 0).1 (hu (Nat.zero_le n)) (hus n).2
    (Eventually.of_forall fun _ => abs_nonneg _) hg'_abs

end BVHelpers

section CutoffAndPrefactor

/-- Even piecewise-linear cutoff `χ(τ)` vanishing on `|τ| ≤ 2 δ` and equal to `1` on `|τ| ≥ 4 δ`. -/
noncomputable def tebCutoff (δ τ : ℝ) : ℝ :=
  min 1 (max 0 (|τ| / (2 * δ) - 1))

lemma tebCutoff_even (δ τ : ℝ) : tebCutoff δ (-τ) = tebCutoff δ τ := by
  simp [tebCutoff, abs_neg]

lemma tebCutoff_nonneg (δ τ : ℝ) : 0 ≤ tebCutoff δ τ :=
  le_min zero_le_one (le_max_left _ _)

lemma tebCutoff_le_one (δ τ : ℝ) : tebCutoff δ τ ≤ 1 :=
  min_le_left _ _

lemma tebCutoff_continuous (δ : ℝ) : Continuous (tebCutoff δ) := by
  unfold tebCutoff
  fun_prop

lemma tebCutoff_eq_zero {δ τ : ℝ} (hδ : 0 < δ) (hτ : |τ| ≤ 2 * δ) : tebCutoff δ τ = 0 := by
  unfold tebCutoff
  have h1 : |τ| / (2 * δ) - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one (by positivity)]
    exact hτ
  rw [max_eq_left h1, min_eq_right zero_le_one]

lemma tebCutoff_eq_one {δ τ : ℝ} (hδ : 0 < δ) (hτ : 4 * δ ≤ |τ|) : tebCutoff δ τ = 1 := by
  unfold tebCutoff
  have h1 : 1 ≤ |τ| / (2 * δ) - 1 := by
    rw [le_sub_iff_add_le]
    norm_num
    rw [le_div_iff₀ (by positivity)]
    linarith
  rw [max_eq_right (by linarith), min_eq_left h1]

lemma tebCutoff_monotoneOn_Ici (δ : ℝ) (hδ : 0 < δ) : MonotoneOn (tebCutoff δ) (Ici 0) := by
  intro x hx y hy hxy
  unfold tebCutoff
  rw [abs_of_nonneg hx, abs_of_nonneg hy]
  refine min_le_min le_rfl (max_le_max le_rfl (sub_le_sub_right ?_ 1))
  exact div_le_div_of_nonneg_right hxy (by positivity)

lemma tebCutoff_eVariationOn_le {δ a b : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hab : a ≤ b) :
    eVariationOn (tebCutoff δ) (Icc a b) ≤ ENNReal.ofReal 1 := by
  have hm : MonotoneOn (tebCutoff δ) (Icc a b) :=
    (tebCutoff_monotoneOn_Ici δ hδ).mono fun x hx => ha.trans hx.1
  have hev := hm.eVariationOn_eq (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  rw [inter_self] at hev
  rw [hev]
  exact ENNReal.ofReal_le_ofReal (by linarith [tebCutoff_nonneg δ a, tebCutoff_le_one δ b])

/-- Strip damping prefactor `H(ζ)/W̃_c(ζ) = c^{5/6} (ζ(1 - ζ))^{5/2} e^{-ζ(1 - ζ)}`. -/
noncomputable def tebPrefactor (c : ℝ) (ζ : ℂ) : ℂ :=
  ((c ^ (5 / 6 : ℝ) : ℝ) : ℂ) * (ζ * (1 - ζ)) ^ (5 / 2 : ℂ) * Complex.exp (-(ζ * (1 - ζ)))

/-- Boundary prefactor `𝒜₀(τ) = tebPrefactor c (i τ)`. -/
noncomputable def tebAmp0 (c τ : ℝ) : ℂ :=
  tebPrefactor c ((τ : ℂ) * Complex.I)

lemma tebPrefactor_symm (c : ℝ) (ζ : ℂ) : tebPrefactor c (1 - ζ) = tebPrefactor c ζ := by
  unfold tebPrefactor
  have h1 : (1 - ζ) * (1 - (1 - ζ)) = ζ * (1 - ζ) := by ring
  rw [h1]

lemma re_mul_one_sub_nonneg {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    0 ≤ (ζ * (1 - ζ)).re := by
  have heq : (ζ * (1 - ζ)).re = ζ.re * (1 - ζ.re) + ζ.im ^ 2 := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  rw [heq]
  nlinarith [sq_nonneg ζ.im]

lemma re_mul_one_sub_pos {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1) :
    0 < (ζ * (1 - ζ)).re := by
  have heq : (ζ * (1 - ζ)).re = ζ.re * (1 - ζ.re) + ζ.im ^ 2 := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  rw [heq]
  nlinarith [sq_nonneg ζ.im]

lemma norm_cpow_ofReal {z : ℂ} {r : ℝ} (hr : 0 < r) :
    ‖z ^ (r : ℂ)‖ = ‖z‖ ^ r := by
  by_cases hz : z = 0
  · rw [hz, Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hr.ne'), norm_zero,
      Real.zero_rpow hr.ne']
  · rw [Complex.cpow_def_of_ne_zero hz, Complex.norm_exp, Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
    congr 1
    simp only [Complex.mul_re, Complex.log_re, Complex.ofReal_re, Complex.log_im, Complex.ofReal_im,
      mul_zero, sub_zero, mul_comm]

lemma tebPrefactor_continuousOn (c : ℝ) :
    ContinuousOn (fun ζ => tebPrefactor c ζ) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} := by
  intro ζ hζ
  unfold tebPrefactor
  have hcpow : ContinuousAt (fun w : ℂ => w ^ (5 / 2 : ℂ)) (ζ * (1 - ζ)) :=
    Complex.continuousAt_cpow_const_of_re_pos (Or.inl (re_mul_one_sub_nonneg hζ.1 hζ.2))
      (by norm_num)
  have hcomp : ContinuousAt (fun z : ℂ => (z * (1 - z)) ^ (5 / 2 : ℂ)) ζ :=
    hcpow.comp (f := fun z : ℂ => z * (1 - z))
      (continuousAt_id.mul (continuousAt_const.sub continuousAt_id))
  exact ((continuousAt_const.mul hcomp).mul (by fun_prop)).continuousWithinAt

lemma tebPrefactor_differentiableOn (c : ℝ) :
    DifferentiableOn ℂ (tebPrefactor c) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} := by
  intro ζ hζ
  unfold tebPrefactor
  have hslit : ζ * (1 - ζ) ∈ slitPlane :=
    Or.inl (re_mul_one_sub_pos hζ.1 hζ.2)
  have hd_inner : HasDerivAt (fun z : ℂ => z * (1 - z)) (1 - 2 * ζ) ζ := by
    have h := (hasDerivAt_id ζ).mul ((hasDerivAt_const ζ (1 : ℂ)).sub (hasDerivAt_id ζ))
    refine h.congr_deriv ?_
    simp; ring
  have hd_cpow : DifferentiableAt ℂ (fun z : ℂ => (z * (1 - z)) ^ (5 / 2 : ℂ)) ζ :=
    (hd_inner.cpow_const hslit).differentiableAt
  exact ((differentiableAt_const _).mul hd_cpow |>.mul (by fun_prop)).differentiableWithinAt

lemma norm_tebPrefactor_le (c : ℝ) (hc : 0 ≤ c) {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    ‖tebPrefactor c ζ‖ ≤ c ^ (5 / 6 : ℝ) * ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) * Real.exp (-ζ.im ^ 2) := by
  unfold tebPrefactor
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc _),
    Complex.norm_exp]
  have hcpow : ‖(ζ * (1 - ζ)) ^ (5 / 2 : ℂ)‖ = ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) := by
    simpa using norm_cpow_ofReal (z := ζ * (1 - ζ)) (r := 5 / 2) (by norm_num)
  have hexp : Real.exp (-(ζ * (1 - ζ))).re ≤ Real.exp (-ζ.im ^ 2) := by
    apply Real.exp_le_exp.mpr
    have heq : (ζ * (1 - ζ)).re = ζ.re * (1 - ζ.re) + ζ.im ^ 2 := by
      simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      ring
    rw [Complex.neg_re, heq]
    nlinarith
  rw [hcpow]
  gcongr

lemma norm_tebPrefactor_ge_on_annulus {c ρ_min : ℝ} (hc : 0 < c) (hρ : 0 < ρ_min)
    {ζ : ℂ} (hlo : ρ_min ≤ ‖ζ‖) (hhi : ‖ζ‖ ≤ 0.035) :
    c ^ (5 / 6 : ℝ) * (ρ_min ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04)) ≤
      ‖tebPrefactor c ζ‖ := by
  unfold tebPrefactor
  have hζ_ne : ζ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hρ hlo)
  have h1ζ_lb : (0.965 : ℝ) ≤ ‖1 - ζ‖ := by
    have h := norm_sub_norm_le 1 ζ
    rw [norm_one] at h
    linarith
  have hprod_lb : ρ_min * 0.965 ≤ ‖ζ * (1 - ζ)‖ := by
    rw [norm_mul]
    exact mul_le_mul hlo h1ζ_lb (by norm_num) (norm_nonneg ζ)
  have hcpow_eq : ‖(ζ * (1 - ζ)) ^ (5 / 2 : ℂ)‖ = ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) := by
    simpa using norm_cpow_ofReal (z := ζ * (1 - ζ)) (r := 5 / 2) (by norm_num)
  have hexp_lb : Real.exp (-0.04) ≤ Real.exp (-(ζ * (1 - ζ))).re := by
    apply Real.exp_le_exp.mpr
    have hre : (ζ * (1 - ζ)).re ≤ ‖ζ * (1 - ζ)‖ := Complex.re_le_norm _
    have h1ζ_ub : ‖1 - ζ‖ ≤ 1 + 0.035 := by
      calc ‖1 - ζ‖ ≤ ‖(1 : ℂ)‖ + ‖ζ‖ := norm_sub_le _ _
        _ ≤ 1 + 0.035 := by rw [norm_one]; linarith
    have hprod_ub : ‖ζ * (1 - ζ)‖ ≤ 0.035 * (1 + 0.035) := by
      rw [norm_mul]
      exact mul_le_mul hhi h1ζ_ub (norm_nonneg _) (by norm_num)
    rw [Complex.neg_re]
    linarith
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc.le _),
    hcpow_eq, Complex.norm_exp]
  have hpow_lb : ρ_min ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) ≤ ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) := by
    rw [← Real.mul_rpow hρ.le (by norm_num)]
    exact Real.rpow_le_rpow (by positivity) hprod_lb (by norm_num)
  calc c ^ (5 / 6 : ℝ) * (ρ_min ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04))
      = c ^ (5 / 6 : ℝ) * (ρ_min ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ)) * Real.exp (-0.04) := by
        ring
    _ ≤ c ^ (5 / 6 : ℝ) * ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) * Real.exp (-(ζ * (1 - ζ))).re := by
        gcongr

lemma norm_tebAmp0_le {c τ : ℝ} (hc : 0 ≤ c) :
    ‖tebAmp0 c τ‖ ≤ c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * Real.exp (-τ ^ 2) := by
  unfold tebAmp0
  have hre : ((τ : ℂ) * Complex.I).re = 0 := by simp
  have h := norm_tebPrefactor_le c hc hre.ge (by linarith)
  have him : ((τ : ℂ) * Complex.I).im = τ := by simp
  rw [him] at h
  have hprod : ‖((τ : ℂ) * Complex.I) * (1 - (τ : ℂ) * Complex.I)‖ ≤ |τ| * (1 + |τ|) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    have h1 : ‖1 - (τ : ℂ) * Complex.I‖ ≤ 1 + |τ| := by
      calc ‖1 - (τ : ℂ) * Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖(τ : ℂ) * Complex.I‖ := norm_sub_le _ _
        _ = 1 + |τ| := by
          rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hpow : ‖((τ : ℂ) * Complex.I) * (1 - (τ : ℂ) * Complex.I)‖ ^ (5 / 2 : ℝ) ≤
      |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) := by
    rw [← Real.mul_rpow (abs_nonneg τ) (by positivity)]
    exact Real.rpow_le_rpow (norm_nonneg _) hprod (by norm_num)
  calc ‖tebPrefactor c ((τ : ℂ) * Complex.I)‖
      ≤ c ^ (5 / 6 : ℝ) * ‖((τ : ℂ) * Complex.I) * (1 - (τ : ℂ) * Complex.I)‖ ^ (5 / 2 : ℝ) *
          Real.exp (-τ ^ 2) := h
    _ ≤ c ^ (5 / 6 : ℝ) * (|τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ)) * Real.exp (-τ ^ 2) := by
        gcongr
    _ = c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * Real.exp (-τ ^ 2) := by ring

/-- Derivative and block BV bound for `τ ↦ tebAmp0 c (sgn * τ)` on `Icc s (2 * s)` (`s > 0`, `|sgn| = 1`). -/
lemma tebAmp0_block_bv_le {c sgn s : ℝ} (hc : 0 ≤ c) (hsgn : |sgn| = 1) (hs : 0 < s) :
    (∀ τ ∈ Icc s (2 * s),
      ‖tebAmp0 c (sgn * τ)‖ +
        (eVariationOn (fun t => tebAmp0 c (sgn * t)) (Icc s (2 * s))).toReal ≤
      272 * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) * Real.exp (-s ^ 2)) ∧
    BoundedVariationOn (fun t => tebAmp0 c (sgn * t)) (Icc s (2 * s)) := by
  have hsgn2 : sgn ^ 2 = 1 := by rw [← sq_abs sgn, hsgn, one_pow]
  let w : ℝ → ℂ := fun t => ((t ^ 2 : ℝ) : ℂ) + Complex.I * ((sgn * t : ℝ) : ℂ)
  let w' : ℝ → ℂ := fun t => ((2 * t : ℝ) : ℂ) + Complex.I * (sgn : ℂ)
  have h_eq : ∀ t : ℝ, tebAmp0 c (sgn * t) =
      ((c ^ (5 / 6 : ℝ) : ℝ) : ℂ) * (w t) ^ (5 / 2 : ℂ) * Complex.exp (-(w t)) := fun t => by
    unfold tebAmp0 tebPrefactor
    have hw_id : ((sgn * t : ℝ) : ℂ) * Complex.I * (1 - ((sgn * t : ℝ) : ℂ) * Complex.I) = w t := by
      dsimp [w]
      have hsq : ((sgn : ℂ) ^ 2) = 1 := by exact_mod_cast hsgn2
      push_cast
      calc ((sgn : ℂ) * (t : ℂ)) * Complex.I * (1 - ((sgn : ℂ) * (t : ℂ)) * Complex.I)
          = (sgn : ℂ) ^ 2 * (t : ℂ) ^ 2 * (-(Complex.I ^ 2)) + Complex.I * ((sgn : ℂ) * (t : ℂ)) := by
            ring
        _ = (t : ℂ) ^ 2 + Complex.I * ((sgn : ℂ) * (t : ℂ)) := by
            rw [hsq, Complex.I_sq]; ring
    rw [hw_id]
  let f' : ℝ → ℂ := fun t =>
    ((c ^ (5 / 6 : ℝ) : ℝ) : ℂ) *
      (((5 / 2 : ℂ) * (w t) ^ (3 / 2 : ℂ) * w' t - (w t) ^ (5 / 2 : ℂ) * w' t) *
        Complex.exp (-(w t)))
  have h_deriv : ∀ t ∈ Icc s (2 * s), HasDerivAt (fun u => tebAmp0 c (sgn * u)) (f' t) t := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le hs ht.1
    have hw_slit : w t ∈ slitPlane := Or.inl (by
      simp only [w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero]
      exact sq_pos_of_pos ht_pos)
    have hw_deriv : HasDerivAt w (w' t) t := by
      dsimp [w, w']
      have h1 : HasDerivAt (fun u : ℝ => ((u ^ 2 : ℝ) : ℂ)) ((2 * t : ℝ) : ℂ) t := by
        have hd := ((hasDerivAt_id t).pow 2).ofReal_comp
        refine hd.congr_deriv ?_
        simp [mul_comm]
      have h2 : HasDerivAt (fun u : ℝ => Complex.I * ((sgn * u : ℝ) : ℂ)) (Complex.I * (sgn : ℂ)) t := by
        have hlin : HasDerivAt (fun u : ℝ => sgn * u) sgn t := by
          simpa using (hasDerivAt_id t).const_mul sgn
        simpa using (hlin.ofReal_comp).const_mul Complex.I
      exact h1.add h2
    have hpow : HasDerivAt (fun u => (w u) ^ (5 / 2 : ℂ))
        ((5 / 2 : ℂ) * (w t) ^ ((5 / 2 : ℂ) - 1) * w' t) t := by
      have hcpow : HasDerivAt (fun z : ℂ => z ^ (5 / 2 : ℂ))
          ((5 / 2 : ℂ) * (w t) ^ ((5 / 2 : ℂ) - 1)) (w t) := by
        simpa [mul_one] using (hasDerivAt_id (w t)).cpow_const hw_slit (c := (5 / 2 : ℂ))
      exact (hcpow.scomp t hw_deriv).congr_deriv (by ring)
    have hexp : HasDerivAt (fun u => Complex.exp (-(w u))) (Complex.exp (-(w t)) * (-w' t)) t :=
      (hw_deriv.neg).cexp
    have hmul : HasDerivAt (fun u => (w u) ^ (5 / 2 : ℂ) * Complex.exp (-(w u)))
        (((5 / 2 : ℂ) * (w t) ^ (3 / 2 : ℂ) * w' t) * Complex.exp (-(w t)) +
          (w t) ^ (5 / 2 : ℂ) * (Complex.exp (-(w t)) * (-w' t))) t := by
      convert hpow.mul hexp using 2
      norm_num
    have hconst := hmul.const_mul ((c ^ (5 / 6 : ℝ) : ℝ) : ℂ)
    have heq_fun : (fun u => ((c ^ (5 / 6 : ℝ) : ℝ) : ℂ) * ((w u) ^ (5 / 2 : ℂ) * Complex.exp (-(w u)))) =
        fun u => tebAmp0 c (sgn * u) := by
      ext u; rw [h_eq u]; ring
    rw [heq_fun] at hconst
    refine hconst.congr_deriv ?_
    dsimp [f']; ring
  have hw_norm : ∀ t ∈ Icc s (2 * s), ‖w t‖ ≤ 4 * s * (1 + s) := by
    intro t ht
    have ht_nn : 0 ≤ t := hs.le.trans ht.1
    calc ‖w t‖ ≤ ‖((t ^ 2 : ℝ) : ℂ)‖ + ‖Complex.I * ((sgn * t : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = t ^ 2 + t := by
          rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg t), norm_mul, Complex.norm_I,
            one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, hsgn, one_mul,
            abs_of_nonneg ht_nn]
      _ ≤ (2 * s) ^ 2 + 2 * s := by gcongr; exact ht.2; exact ht.2
      _ = 4 * s ^ 2 + 2 * s := by ring
      _ ≤ 4 * s * (1 + s) := by nlinarith
  have hw'_norm : ∀ t ∈ Icc s (2 * s), ‖w' t‖ ≤ 4 * (1 + s) := by
    intro t ht
    have ht_nn : 0 ≤ t := hs.le.trans ht.1
    calc ‖w' t‖ ≤ ‖((2 * t : ℝ) : ℂ)‖ + ‖Complex.I * (sgn : ℂ)‖ := norm_add_le _ _
      _ = 2 * t + 1 := by
          rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_I,
            one_mul, Complex.norm_real, Real.norm_eq_abs, hsgn]
      _ ≤ 2 * (2 * s) + 1 := by gcongr; exact ht.2
      _ ≤ 4 * (1 + s) := by linarith
  have hexp_norm : ∀ t ∈ Icc s (2 * s), ‖Complex.exp (-(w t))‖ ≤ Real.exp (-s ^ 2) := by
    intro t ht
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (-(w t)).re = -t ^ 2 := by
      simp only [w, Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero]
    rw [hre]
    nlinarith [ht.1]
  let K : ℝ := 208 * c ^ (5 / 6 : ℝ) * s ^ (3 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) * Real.exp (-s ^ 2)
  have hK_nn : 0 ≤ K := by positivity
  have hf'_bound : ∀ t ∈ Icc s (2 * s), ‖f' t‖ ≤ K := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le hs ht.1
    have hw_ne : w t ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp only [w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, Complex.zero_re] at this
      nlinarith
    have hw32 : ‖(w t) ^ (3 / 2 : ℂ)‖ ≤ (4 * s * (1 + s)) ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, norm_cpow_ofReal (by norm_num)]
      exact Real.rpow_le_rpow (norm_nonneg _) (hw_norm t ht) (by norm_num)
    have hw52 : ‖(w t) ^ (5 / 2 : ℂ)‖ ≤ (4 * s * (1 + s)) ^ (5 / 2 : ℝ) := by
      rw [show (5 / 2 : ℂ) = ((5 / 2 : ℝ) : ℂ) by norm_num, norm_cpow_ofReal (by norm_num)]
      exact Real.rpow_le_rpow (norm_nonneg _) (hw_norm t ht) (by norm_num)
    have h4_32 : (4 : ℝ) ^ (3 / 2 : ℝ) = 8 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h4_52 : (4 : ℝ) ^ (5 / 2 : ℝ) = 32 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num)]
      norm_num
    have ht1 : (5 / 2 : ℝ) * (4 * s * (1 + s)) ^ (3 / 2 : ℝ) * (4 * (1 + s)) ≤
        80 * s ^ (3 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hs.le, h4_32]
      have h1s : (1 + s) ^ (3 / 2 : ℝ) * (1 + s) ≤ (1 + s) ^ (9 / 2 : ℝ) := by
        have h := (Real.rpow_add (by linarith : 0 < 1 + s) (3 / 2) 1).symm
        rw [Real.rpow_one] at h
        rw [h]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      calc (5 / 2 : ℝ) * (8 * s ^ (3 / 2 : ℝ) * (1 + s) ^ (3 / 2 : ℝ)) * (4 * (1 + s))
          = 80 * s ^ (3 / 2 : ℝ) * ((1 + s) ^ (3 / 2 : ℝ) * (1 + s)) := by ring
        _ ≤ 80 * s ^ (3 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) := by gcongr
    have ht2 : (4 * s * (1 + s)) ^ (5 / 2 : ℝ) * (4 * (1 + s)) ≤
        128 * s ^ (3 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hs.le, h4_52]
      have hs_eq : s ^ (5 / 2 : ℝ) = s ^ (3 / 2 : ℝ) * s := by
        have h := (Real.rpow_add hs (3 / 2) 1).symm
        rw [Real.rpow_one, show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num] at h
        exact h.symm
      have h1s : s * ((1 + s) ^ (5 / 2 : ℝ) * (1 + s)) ≤ (1 + s) ^ (9 / 2 : ℝ) := by
        have h := (Real.rpow_add (by linarith : 0 < 1 + s) (5 / 2) 1).symm
        rw [Real.rpow_one, show (5 / 2 : ℝ) + 1 = 7 / 2 by norm_num] at h
        have hs1 : s ≤ 1 + s := by linarith
        have h92 : (1 + s) * (1 + s) ^ (7 / 2 : ℝ) = (1 + s) ^ (9 / 2 : ℝ) := by
          have h' := (Real.rpow_add (by linarith : 0 < 1 + s) 1 (7 / 2)).symm
          rw [Real.rpow_one, show (1 : ℝ) + 7 / 2 = 9 / 2 by norm_num] at h'
          exact h'
        calc s * ((1 + s) ^ (5 / 2 : ℝ) * (1 + s))
            = s * (1 + s) ^ (7 / 2 : ℝ) := by rw [h]
          _ ≤ (1 + s) * (1 + s) ^ (7 / 2 : ℝ) := mul_le_mul_of_nonneg_right hs1 (by positivity)
          _ = (1 + s) ^ (9 / 2 : ℝ) := h92
      calc (32 * s ^ (5 / 2 : ℝ) * (1 + s) ^ (5 / 2 : ℝ)) * (4 * (1 + s))
          = 128 * s ^ (3 / 2 : ℝ) * (s * ((1 + s) ^ (5 / 2 : ℝ) * (1 + s))) := by
            rw [hs_eq]; ring
        _ ≤ 128 * s ^ (3 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) := by gcongr
    dsimp [f']
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc _)]
    have hmid : ‖(5 / 2 : ℂ) * (w t) ^ (3 / 2 : ℂ) * w' t - (w t) ^ (5 / 2 : ℂ) * w' t‖ ≤
        208 * s ^ (3 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) := by
      calc ‖(5 / 2 : ℂ) * (w t) ^ (3 / 2 : ℂ) * w' t - (w t) ^ (5 / 2 : ℂ) * w' t‖
          ≤ ‖(5 / 2 : ℂ) * (w t) ^ (3 / 2 : ℂ) * w' t‖ + ‖(w t) ^ (5 / 2 : ℂ) * w' t‖ :=
            norm_sub_le _ _
        _ = (5 / 2 : ℝ) * ‖(w t) ^ (3 / 2 : ℂ)‖ * ‖w' t‖ + ‖(w t) ^ (5 / 2 : ℂ)‖ * ‖w' t‖ := by
            rw [norm_mul, norm_mul, norm_mul]
            norm_num
        _ ≤ (5 / 2 : ℝ) * (4 * s * (1 + s)) ^ (3 / 2 : ℝ) * (4 * (1 + s)) +
              (4 * s * (1 + s)) ^ (5 / 2 : ℝ) * (4 * (1 + s)) := by
            have hw't := hw'_norm t ht
            gcongr
        _ ≤ 80 * s ^ (3 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) +
              128 * s ^ (3 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) := add_le_add ht1 ht2
        _ = 208 * s ^ (3 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) := by ring
    calc c ^ (5 / 6 : ℝ) *
          (‖(5 / 2 : ℂ) * (w t) ^ (3 / 2 : ℂ) * w' t - (w t) ^ (5 / 2 : ℂ) * w' t‖ *
            ‖Complex.exp (-(w t))‖)
        ≤ c ^ (5 / 6 : ℝ) *
            ((208 * s ^ (3 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ)) * Real.exp (-s ^ 2)) := by
          gcongr
          exact hexp_norm t ht
      _ = K := by dsimp [K]; ring
  have hev := eVariationOn_le_of_hasDerivAt_le (by linarith : s ≤ 2 * s) hK_nn h_deriv hf'_bound
  have hbv : BoundedVariationOn (fun t => tebAmp0 c (sgn * t)) (Icc s (2 * s)) :=
    ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne hev
  have hKs : K * (2 * s - s) =
      208 * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) * Real.exp (-s ^ 2) := by
    dsimp [K]
    have hs_eq : s ^ (3 / 2 : ℝ) * s = s ^ (5 / 2 : ℝ) := by
      have h := (Real.rpow_add hs (3 / 2) 1).symm
      rw [Real.rpow_one, show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num] at h
      exact h
    calc 208 * c ^ (5 / 6 : ℝ) * s ^ (3 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) * Real.exp (-s ^ 2) * (2 * s - s)
        = 208 * c ^ (5 / 6 : ℝ) * (s ^ (3 / 2 : ℝ) * s) * (1 + s) ^ (9 / 2 : ℝ) * Real.exp (-s ^ 2) := by ring
      _ = 208 * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) * Real.exp (-s ^ 2) := by
          rw [hs_eq]
  have hc56 : 0 ≤ c ^ (5 / 6 : ℝ) := Real.rpow_nonneg hc _
  have hs52 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.le _
  have h1s92 : 0 ≤ (1 + s) ^ (9 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have htv_le : (eVariationOn (fun t => tebAmp0 c (sgn * t)) (Icc s (2 * s))).toReal ≤
      208 * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) * Real.exp (-s ^ 2) :=
    (ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK_nn (by linarith)) hev).trans_eq hKs
  refine ⟨fun τ hτ => ?_, hbv⟩
  have hnorm_τ : ‖tebAmp0 c (sgn * τ)‖ ≤
      64 * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) * Real.exp (-s ^ 2) := by
    have h0 := norm_tebAmp0_le hc (τ := sgn * τ)
    have h_abs : |sgn * τ| = τ := by
      rw [abs_mul, hsgn, one_mul, abs_of_nonneg (hs.le.trans hτ.1)]
    have h_sq : -(sgn * τ) ^ 2 = -τ ^ 2 := by rw [mul_pow, hsgn2, one_mul]
    rw [h_abs, h_sq] at h0
    have hτ_le : τ ≤ 2 * s := hτ.2
    have h1τ_le : 1 + τ ≤ 2 * (1 + s) := by linarith
    have hexp_le : Real.exp (-τ ^ 2) ≤ Real.exp (-s ^ 2) := Real.exp_le_exp.mpr (by nlinarith [hτ.1])
    have h2_52 : (2 : ℝ) ^ (5 / 2 : ℝ) ≤ 8 := by
      have h1 : (2 : ℝ) ^ (5 / 2 : ℝ) ≤ (2 : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      norm_num at h1; exact h1
    have hpow1 : τ ^ (5 / 2 : ℝ) ≤ 8 * s ^ (5 / 2 : ℝ) := by
      calc τ ^ (5 / 2 : ℝ) ≤ (2 * s) ^ (5 / 2 : ℝ) :=
            Real.rpow_le_rpow (hs.le.trans hτ.1) hτ_le (by norm_num)
        _ = (2 : ℝ) ^ (5 / 2 : ℝ) * s ^ (5 / 2 : ℝ) := Real.mul_rpow (by norm_num) hs.le
        _ ≤ 8 * s ^ (5 / 2 : ℝ) := mul_le_mul_of_nonneg_right h2_52 hs52
    have hpow2 : (1 + τ) ^ (5 / 2 : ℝ) ≤ 8 * (1 + s) ^ (9 / 2 : ℝ) := by
      have h1s_ge : 1 ≤ 1 + s := by linarith
      calc (1 + τ) ^ (5 / 2 : ℝ) ≤ (2 * (1 + s)) ^ (5 / 2 : ℝ) :=
            Real.rpow_le_rpow (by linarith [hs.le, hτ.1]) h1τ_le (by norm_num)
        _ = (2 : ℝ) ^ (5 / 2 : ℝ) * (1 + s) ^ (5 / 2 : ℝ) := Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ 8 * (1 + s) ^ (9 / 2 : ℝ) :=
            mul_le_mul h2_52 (Real.rpow_le_rpow_of_exponent_le h1s_ge (by norm_num))
              (Real.rpow_nonneg (by linarith) _) (by norm_num)
    have hprod_le : τ ^ (5 / 2 : ℝ) * (1 + τ) ^ (5 / 2 : ℝ) ≤
        64 * s ^ (5 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) := by
      calc τ ^ (5 / 2 : ℝ) * (1 + τ) ^ (5 / 2 : ℝ)
          ≤ (8 * s ^ (5 / 2 : ℝ)) * (8 * (1 + s) ^ (9 / 2 : ℝ)) :=
            mul_le_mul hpow1 hpow2 (Real.rpow_nonneg (by linarith [hs.le, hτ.1]) _)
              (mul_nonneg (by norm_num) hs52)
        _ = 64 * s ^ (5 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) := by ring
    calc ‖tebAmp0 c (sgn * τ)‖
        ≤ c ^ (5 / 6 : ℝ) * τ ^ (5 / 2 : ℝ) * (1 + τ) ^ (5 / 2 : ℝ) * Real.exp (-τ ^ 2) := h0
      _ = c ^ (5 / 6 : ℝ) * (τ ^ (5 / 2 : ℝ) * (1 + τ) ^ (5 / 2 : ℝ)) * Real.exp (-τ ^ 2) := by ring
      _ ≤ c ^ (5 / 6 : ℝ) * (64 * s ^ (5 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ)) * Real.exp (-s ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hprod_le hc56) hexp_le
            (Real.exp_pos _).le (mul_nonneg hc56 (mul_nonneg (mul_nonneg (by norm_num) hs52) h1s92))
      _ = 64 * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) * Real.exp (-s ^ 2) := by
          ring
  linarith

end CutoffAndPrefactor

end FormalResearch.ModularBootstrap.StripBand
