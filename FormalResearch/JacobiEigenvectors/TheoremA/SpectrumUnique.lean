module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumTaylor

/-!
# Paper J, Layer 2: uniqueness of the eigenvalue-rule coefficients, abstract core (L2.S6 (b), L2.S7)

Source: Paper J `app_thmA.tex`, proof of `thm:smo-spec`, paragraph "Uniqueness, extensions and dependence on the jets":
if `d_j = S_j - S'_j` are `C^{M+1}` on `[a - delta, b + delta]`, `sum_j h^j d_j(x) = O(h^{M+1})` on a set of points `x` (the eigenvalues, with the *same* labels)
which are `O(h)`-dense in the band `[a, b]` and lie within `O(h)` of it, then `d_j = 0` on `[a, b]` for all `j <= M`; by induction on `j`:
`d_i = 0` on `[a,b]` for `i < j` makes `d_i` flat of order `M+1` at `a, b`, so `h^i d_i(x) = O(h^{M+1+i})` at the points `x`, hence `|d_j(x)| <= C h`, and the density and
the Lipschitz bound give `d_j = 0`.

## Proved here (axiom-pinned)

* `flat_one_sided`, `iteratedDeriv_zero_of_flat`, `flat_bound`: a `C^{M+1}` function vanishing on `[a,b]` satisfies `|d(x)| <= C_n e^{M+1}` whenever `x` is within `e` of `[a,b]`
  (Taylor's formula at the end points, `taylor_pt`).
* `unique_core`: the induction above, for an abstract family of point sets `Ev N` and steps `hs N -> 0`; **no eigenvalue is mentioned**: the eigenvalue input are the three
  hypotheses `hrule` (the rule for `d`), `hnear` (within `C_P h` of the band: Step 0, `StepZeroD0`) and `hdense` (`C_D h`-density of the eigenvalues in the band: L2.S5, "Density").

## Differences from the paper

* The `C^{M+1}` regularity and the norm bound `C_n` are on the open interval `(a - delta, b + delta)` (the closed interval statement implies this one); the norm bound is stated for the
  derivatives `iteratedDeriv i`, `i <= M+1` (the paper's `C^{M+1}` norm).
* Constants and the threshold `h_0` are explicit arguments (chosen before the steps).

## Not formalised

The identification of `Ev N` with the set of eigenvalues of `J_h`, `h = L/(N+1)`, and of `hnear`, `hdense` with Step 0 and the density statement (`SmoothSpectrum.lean`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Nat Set

/-- one-sided flatness: if all derivatives of order `<= M` of `g` vanish at `0`, `|g h| <= C h^{M+1}` -/
lemma flat_one_sided (g : ℝ → ℝ) (M : ℕ) (δ C : ℝ)
    (hg : ContDiffOn ℝ (M + 1 : ℕ) g (Ioo (-δ) δ)) (hC : ∀ t ∈ Ioo (-δ) δ, |iteratedDeriv (M + 1) g t| ≤ C)
    (h0 : ∀ i ≤ M, iteratedDeriv i g 0 = 0) {h : ℝ} (hh : 0 < h) (hhδ : h < δ) : |g h| ≤ C * h ^ (M + 1) := by
  have := taylor_pt g M δ C h hh hhδ hg hC
  have hz : ∑ i ∈ range (M + 1), (i ! : ℝ)⁻¹ * iteratedDeriv i g 0 * h ^ i = 0 :=
    Finset.sum_eq_zero (fun i hi => by rw [h0 i (by have := Finset.mem_range.mp hi; omega)]; ring)
  rwa [hz, sub_zero] at this

/-- derivatives of a function vanishing on `[a,b]` vanish at `b` and at `a`. -/
lemma iteratedDeriv_zero_of_flat (d : ℝ → ℝ) {a b p q : ℝ} (hab : a < b) (hpq : p < a ∧ b < q) (M : ℕ)
    (hreg : ContDiffOn ℝ (M + 1 : ℕ) d (Ioo p q)) (hz : ∀ x ∈ Icc a b, d x = 0) {x : ℝ} (hx : x = a ∨ x = b) (i : ℕ)
    (hi : i ≤ M + 1) : iteratedDeriv i d x = 0 := by
  have hxI : x ∈ Icc a b := by rcases hx with rfl | rfl <;> constructor <;> linarith
  have hxo : x ∈ Ioo p q := by rcases hx with rfl | rfl <;> constructor <;> linarith [hpq.1, hpq.2]
  have hcd : ContDiffAt ℝ (i : WithTop ℕ∞) d x :=
    (hreg.contDiffAt (isOpen_Ioo.mem_nhds hxo)).of_le (by exact_mod_cast hi)
  have h1 := iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hcd hxI
  rw [← h1]
  have h2 : iteratedDerivWithin i d (Icc a b) x = iteratedDerivWithin i (fun _ => (0 : ℝ)) (Icc a b) x :=
    iteratedDerivWithin_congr hz hxI
  rw [h2]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) (contDiffAt_const) hxI]
    simp

lemma flat_bound (d : ℝ → ℝ) {a b δ Cn : ℝ} (hab : a < b) (hδ : 0 < δ) (M : ℕ)
    (hreg : ContDiffOn ℝ (M + 1 : ℕ) d (Ioo (a - δ) (b + δ)))
    (hbd : ∀ x ∈ Ioo (a - δ) (b + δ), |iteratedDeriv (M + 1) d x| ≤ Cn) (hz : ∀ x ∈ Icc a b, d x = 0)
    {x e : ℝ} (hx : x ∈ Ioo (a - δ) (b + δ)) (y : ℝ) (hy : y ∈ Icc a b) (hxy : |x - y| ≤ e) :
    |d x| ≤ Cn * e ^ (M + 1) := by
  have hCn : 0 ≤ Cn := (abs_nonneg _).trans (hbd a ⟨by linarith, by linarith⟩)
  have he : 0 ≤ e := (abs_nonneg _).trans hxy
  have hpq : a - δ < a ∧ b < b + δ := ⟨by linarith, by linarith⟩
  rcases lt_or_ge b x with hxb | hxb
  · -- right of `b`
    have hh : 0 < x - b := by linarith
    have hhδ : x - b < δ := by linarith [hx.2]
    have hmaps : MapsTo (fun t : ℝ => b + t) (Ioo (-δ) δ) (Ioo (a - δ) (b + δ)) :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hg : ContDiffOn ℝ (M + 1 : ℕ) (fun t => d (b + t)) (Ioo (-δ) δ) :=
      hreg.comp (contDiff_const.add contDiff_id).contDiffOn hmaps
    have hC : ∀ t ∈ Ioo (-δ) δ, |iteratedDeriv (M + 1) (fun t => d (b + t)) t| ≤ Cn := by
      intro t ht
      rw [iteratedDeriv_comp_const_add]
      exact hbd _ (hmaps ht)
    have h0 : ∀ i ≤ M, iteratedDeriv i (fun t => d (b + t)) 0 = 0 := by
      intro i hi
      rw [iteratedDeriv_comp_const_add]
      show iteratedDeriv i d (b + 0) = 0
      rw [add_zero]
      exact iteratedDeriv_zero_of_flat d hab hpq M hreg hz (Or.inr rfl) i (by omega)
    have := flat_one_sided _ M δ Cn hg hC h0 hh hhδ
    have e1 : b + (x - b) = x := by ring
    simp only [e1] at this
    refine this.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh.le ?_ _) hCn)
    have := (abs_le.mp hxy).1
    have := hy.2
    linarith [(abs_le.mp hxy).1, (abs_le.mp hxy).2]
  · rcases lt_or_ge x a with hxa | hxa
    · have hh : 0 < a - x := by linarith
      have hhδ : a - x < δ := by linarith [hx.1]
      have hmaps : MapsTo (fun t : ℝ => a - t) (Ioo (-δ) δ) (Ioo (a - δ) (b + δ)) :=
        fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hg : ContDiffOn ℝ (M + 1 : ℕ) (fun t => d (a - t)) (Ioo (-δ) δ) :=
        hreg.comp (contDiff_const.sub contDiff_id).contDiffOn hmaps
      have hC : ∀ t ∈ Ioo (-δ) δ, |iteratedDeriv (M + 1) (fun t => d (a - t)) t| ≤ Cn := by
        intro t ht
        rw [iteratedDeriv_comp_const_sub]
        simp only [smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        exact hbd _ (hmaps ht)
      have h0 : ∀ i ≤ M, iteratedDeriv i (fun t => d (a - t)) 0 = 0 := by
        intro i hi
        rw [iteratedDeriv_comp_const_sub]
        show (-1 : ℝ) ^ i • iteratedDeriv i d (a - 0) = 0
        rw [sub_zero, iteratedDeriv_zero_of_flat d hab hpq M hreg hz (Or.inl rfl) i (by omega)]
        simp
      have := flat_one_sided _ M δ Cn hg hC h0 hh hhδ
      have e1 : a - (a - x) = x := by ring
      simp only [e1] at this
      refine this.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh.le ?_ _) hCn)
      linarith [(abs_le.mp hxy).1, (abs_le.mp hxy).2, hy.1]
    · rw [hz x ⟨hxa, hxb⟩, abs_zero]
      positivity

/-- A function with a Lipschitz-type derivative bound on an open interval is Lipschitz there. -/
lemma lip_on_Ioo (f : ℝ → ℝ) {p q Cn : ℝ} (hf : ContDiffOn ℝ (1 : WithTop ℕ∞) f (Ioo p q))
    (hd : ∀ x ∈ Ioo p q, |deriv f x| ≤ Cn) {x y : ℝ} (hx : x ∈ Ioo p q) (hy : y ∈ Ioo p q) :
    |f y - f x| ≤ Cn * |y - x| := by
  have hdiff : ∀ z ∈ Ioo p q, DifferentiableAt ℝ f z := fun z hz =>
    ((hf.differentiableOn one_ne_zero) z hz).differentiableAt (isOpen_Ioo.mem_nhds hz)
  have := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := f) (s := Ioo p q) hdiff
    (fun z hz => by simpa [Real.norm_eq_abs] using hd z hz) (convex_Ioo p q) hx hy
  simpa [Real.norm_eq_abs] using this

/-- **Uniqueness core** (see the module docstring). -/
theorem unique_core (a b δ : ℝ) (hab : a < b) (hδ : 0 < δ) (M : ℕ) (d : ℕ → ℝ → ℝ)
    (hreg : ∀ j ≤ M, ContDiffOn ℝ (M + 1 : ℕ) (d j) (Ioo (a - δ) (b + δ)))
    (Cn : ℝ) (hbd : ∀ j ≤ M, ∀ i ≤ M + 1, ∀ x ∈ Ioo (a - δ) (b + δ), |iteratedDeriv i (d j) x| ≤ Cn)
    (hs : ℕ → ℝ) (hspos : ∀ N, 0 < hs N) (hs0 : ∀ ε > 0, ∃ N0, ∀ N ≥ N0, hs N < ε)
    (Ev : ℕ → Set ℝ) (C h0 CP CD : ℝ) (hh0 : 0 < h0)
    (hrule : ∀ N, hs N ≤ h0 → ∀ x ∈ Ev N, |∑ j ∈ range (M + 1), hs N ^ j * d j x| ≤ C * hs N ^ (M + 1))
    (hnear : ∀ N, hs N ≤ h0 → ∀ x ∈ Ev N, ∃ y ∈ Icc a b, |x - y| ≤ CP * hs N)
    (hdense : ∀ N, hs N ≤ h0 → ∀ X ∈ Icc a b, ∃ x ∈ Ev N, |x - X| ≤ CD * hs N) :
    ∀ j ≤ M, ∀ X ∈ Icc a b, d j X = 0 := by
  have hCn : 0 ≤ Cn := (abs_nonneg _).trans (hbd 0 (Nat.zero_le _) 0 (Nat.zero_le _) a ⟨by linarith, by linarith⟩)
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hjM X hX
  obtain ⟨CP', hCP'⟩ : ∃ x : ℝ, x = |CP| := ⟨_, rfl⟩
  obtain ⟨CD', hCD'⟩ : ∃ x : ℝ, x = |CD| := ⟨_, rfl⟩
  have hCP0 : 0 ≤ CP' := by rw [hCP']; exact abs_nonneg _
  have hCD0 : 0 ≤ CD' := by rw [hCD']; exact abs_nonneg _
  obtain ⟨K, hK⟩ : ∃ x : ℝ, x = |C| + M * (Cn * CP' ^ (M + 1) + Cn) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have key : ∀ N, hs N ≤ min (min 1 h0) (min (δ / (CP' + 1)) (δ / (CD' + 1))) →
      |d j X| ≤ (K + Cn * CD') * hs N := by
    intro N hN
    have hpos := hspos N
    have h1 : hs N ≤ 1 := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hh0N : hs N ≤ h0 := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hP : CP' * hs N < δ := by
      have := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
      rw [le_div_iff₀ (by linarith)] at this
      nlinarith
    have hD : CD' * hs N < δ := by
      have := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
      rw [le_div_iff₀ (by linarith)] at this
      nlinarith
    obtain ⟨x, hxE, hxX⟩ := hdense N hh0N X hX
    obtain ⟨y, hy, hxy⟩ := hnear N hh0N x hxE
    have hxy' : |x - y| ≤ CP' * hs N := hxy.trans (mul_le_mul_of_nonneg_right (by rw [hCP']; exact le_abs_self _) hpos.le)
    have hxX' : |x - X| ≤ CD' * hs N := hxX.trans (mul_le_mul_of_nonneg_right (by rw [hCD']; exact le_abs_self _) hpos.le)
    have hxdom : x ∈ Ioo (a - δ) (b + δ) := by
      have := abs_le.mp hxy'
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hXdom : X ∈ Ioo (a - δ) (b + δ) := ⟨by linarith [hX.1], by linarith [hX.2]⟩
    -- Step A: `h^j |d_j x| <= K h^{j+1}`
    have hflat : ∀ i < j, |d i x| ≤ Cn * (CP' * hs N) ^ (M + 1) := by
      intro i hi
      exact flat_bound (d i) hab hδ M (hreg i (by omega)) (fun z hz => hbd i (by omega) (M + 1) le_rfl z hz)
        (fun z hz => ih i hi (by omega) z hz) hxdom y hy hxy'
    have hterm : ∀ i ∈ (range (M + 1)).erase j, |hs N ^ i * d i x| ≤ (Cn * CP' ^ (M + 1) + Cn) * hs N ^ (j + 1) := by
      intro i hi
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      have hiM : i ≤ M := by have := (Finset.mem_erase.mp hi).2; have := Finset.mem_range.mp this; omega
      rw [abs_mul, abs_of_pos (pow_pos hpos _)]
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have h2 := hflat i hlt
        have e : (CP' * hs N) ^ (M + 1) = CP' ^ (M + 1) * hs N ^ (M + 1) := mul_pow _ _ _
        calc hs N ^ i * |d i x| ≤ hs N ^ i * (Cn * (CP' ^ (M + 1) * hs N ^ (M + 1))) := by
              rw [← e]; exact mul_le_mul_of_nonneg_left h2 (pow_nonneg hpos.le _)
          _ = Cn * CP' ^ (M + 1) * hs N ^ (i + (M + 1)) := by rw [pow_add]; ring
          _ ≤ Cn * CP' ^ (M + 1) * hs N ^ (j + 1) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hpos.le h1 (by omega)) (by positivity)
          _ ≤ (Cn * CP' ^ (M + 1) + Cn) * hs N ^ (j + 1) :=
              mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hpos.le _)
      · have h2 := hbd i hiM 0 (Nat.zero_le _) x hxdom
        rw [iteratedDeriv_zero] at h2
        calc hs N ^ i * |d i x| ≤ hs N ^ (j + 1) * Cn :=
              mul_le_mul (pow_le_pow_of_le_one hpos.le h1 (by omega)) h2 (abs_nonneg _) (pow_nonneg hpos.le _)
          _ = Cn * hs N ^ (j + 1) := by ring
          _ ≤ (Cn * CP' ^ (M + 1) + Cn) * hs N ^ (j + 1) :=
              mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hCn (pow_nonneg hCP0 (M + 1))]) (pow_nonneg hpos.le _)
    have hsumE : |∑ i ∈ (range (M + 1)).erase j, hs N ^ i * d i x| ≤ M * ((Cn * CP' ^ (M + 1) + Cn) * hs N ^ (j + 1)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ (range (M + 1)).erase j, |hs N ^ i * d i x|
          ≤ ∑ i ∈ (range (M + 1)).erase j, (Cn * CP' ^ (M + 1) + Cn) * hs N ^ (j + 1) := Finset.sum_le_sum hterm
        _ = M * ((Cn * CP' ^ (M + 1) + Cn) * hs N ^ (j + 1)) := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_range.mpr (show j < M + 1 by omega)), Finset.card_range, nsmul_eq_mul]
            simp
    have hdecomp : hs N ^ j * d j x = (∑ i ∈ range (M + 1), hs N ^ i * d i x) - ∑ i ∈ (range (M + 1)).erase j, hs N ^ i * d i x := by
      have := Finset.add_sum_erase (range (M + 1)) (fun i => hs N ^ i * d i x) (Finset.mem_range.mpr (show j < M + 1 by omega))
      linarith
    have hrx := hrule N hh0N x hxE
    have hCle : C * hs N ^ (M + 1) ≤ |C| * hs N ^ (j + 1) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hpos.le _)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hpos.le h1 (by omega)) (abs_nonneg _))
    have hA : hs N ^ j * |d j x| ≤ K * hs N ^ (j + 1) := by
      rw [← abs_of_pos (pow_pos hpos j), ← abs_mul, hdecomp]
      calc |(∑ i ∈ range (M + 1), hs N ^ i * d i x) - ∑ i ∈ (range (M + 1)).erase j, hs N ^ i * d i x|
          ≤ |∑ i ∈ range (M + 1), hs N ^ i * d i x| + |∑ i ∈ (range (M + 1)).erase j, hs N ^ i * d i x| := abs_sub _ _
        _ ≤ |C| * hs N ^ (j + 1) + M * ((Cn * CP' ^ (M + 1) + Cn) * hs N ^ (j + 1)) := add_le_add (hrx.trans hCle) hsumE
        _ = K * hs N ^ (j + 1) := by rw [hK]; ring
    have hAj : |d j x| ≤ K * hs N := by
      have h3 : hs N ^ j * |d j x| ≤ hs N ^ j * (K * hs N) := by
        calc hs N ^ j * |d j x| ≤ K * hs N ^ (j + 1) := hA
          _ = hs N ^ j * (K * hs N) := by rw [pow_succ]; ring
      exact le_of_mul_le_mul_left h3 (pow_pos hpos j)
    -- Step B: Lipschitz bound
    have hlip := lip_on_Ioo (d j) (p := a - δ) (q := b + δ) (Cn := Cn)
      ((hreg j hjM).of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)))
      (fun z hz => by
        have := hbd j hjM 1 (by omega) z hz
        rwa [iteratedDeriv_one] at this) hXdom hxdom
    calc |d j X| = |d j X - d j x + d j x| := by ring_nf
      _ ≤ |d j X - d j x| + |d j x| := abs_add_le _ _
      _ ≤ Cn * |X - x| + K * hs N := by
          refine add_le_add ?_ hAj
          have := lip_on_Ioo (d j) (p := a - δ) (q := b + δ) (Cn := Cn)
            ((hreg j hjM).of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)))
            (fun z hz => by
              have := hbd j hjM 1 (by omega) z hz
              rwa [iteratedDeriv_one] at this) hxdom hXdom
          exact this
      _ ≤ (K + Cn * CD') * hs N := by
          have h5 : Cn * |X - x| ≤ Cn * (CD' * hs N) := by
            rw [abs_sub_comm]; exact mul_le_mul_of_nonneg_left hxX' hCn
          calc Cn * |X - x| + K * hs N ≤ Cn * (CD' * hs N) + K * hs N := by linarith
            _ = (K + Cn * CD') * hs N := by ring
  by_contra hne
  have hpos' : 0 < |d j X| := abs_pos.mpr hne
  obtain ⟨N0, hN0⟩ := hs0 (min (min (min 1 h0) (min (δ / (CP' + 1)) (δ / (CD' + 1)))) (|d j X| / (K + Cn * CD' + 1)))
    (lt_min (lt_min (lt_min one_pos hh0) (lt_min (div_pos hδ (by linarith)) (div_pos hδ (by linarith))))
      (div_pos hpos' (by nlinarith [mul_nonneg hCn hCD0])))
  have hN := hN0 N0 le_rfl
  have hk := key N0 (hN.le.trans (min_le_left _ _))
  have hlt : hs N0 < |d j X| / (K + Cn * CD' + 1) := hN.trans_le (min_le_right _ _)
  rw [lt_div_iff₀ (by nlinarith [mul_nonneg hCn hCD0])] at hlt
  nlinarith [mul_nonneg hCn hCD0, hspos N0]


/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.flat_one_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.flat_one_sided

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.iteratedDeriv_zero_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.iteratedDeriv_zero_of_flat

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.flat_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.flat_bound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.unique_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.unique_core

end FormalResearch.JacobiEigenvectors.TheoremA
