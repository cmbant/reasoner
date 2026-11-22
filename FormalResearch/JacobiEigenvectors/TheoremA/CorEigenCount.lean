module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.CorEigenBase

/-!
# Paper J, Layer 2: cor:eigen (d), counting and density of states (L2.E)

Source: Paper J `thmA.tex`, proof of `cor:eigen`, Step 6 ("part (d)"); statement `CorEigenCount` of `TheoremA/EigenvalueStatements.lean` (`main_results.tex`, `eq:cor-count`, `eq:cor-dos`).
Chain of lemmas: see `CorEigenBase.lean` (B1--B5); this file is B5 and Step 6.

## Proved here (axiom-pinned)

* `ncard_nominal_lt`, `ncard_nominal_bound`: `#{k < n : w (k + 1/2) < T}` is `min n ceil(T/w - 1/2)`, and within `|e| + 1` of `s` for `T = w (s + e)`, `0 <= s <= n`.
* `count_abstract` (the paper's inequalities (cp-nu)): points `X_k` with nearest-band-point `Xc_k` and `|Phi(Xc_k) - w (k + 1/2)| <= E`, `Phi` decreasing from `w n` to `0` on `[lo, hi]`:
  `|#{k : Y < X_k} - Phi(Y)/w| <= E/w + 2` on `[lo, hi]`.
* `midpoint_riemann` (the midpoint rule for a Lipschitz function: `|sum w G(w(k+1/2)) - int_0^{n w} G| <= n Lip w^2/2`), `cov_lemma` (substitution `y = S_0(X)`).
* `localise_rule` (B5): Step 0 (`stepZeroD0`) puts `X_k` within `C_z h` of the band, and the rule at `M = 0` plus the Lipschitz bound of `S_0` on the extended interval gives
  `|S_0(clamp X_k) - pi h (k + 1/2)| <= (|C| + |Cn| C_z) h`.
* `corEigenCount_count` (eq:cor-count), `corEigenCount_dos` (eq:cor-dos, `delta' = delta`), `corEigenCount_of_slope : CountConcl F K S` = the conclusion of the frozen `CorEigenCount`.

## Differences from the paper

* Premises of the theorems here: `0 < delta` (finding F-BB-1, now also a premise of the frozen `CorEigenCount`) and the slope input `BandSlope F K S` (F-BB-2; discharged from the windows in `Assembly/CorEigen.lean`); see `CorEigenBase.lean`.  Everything else of the frozen `CorEigenCount` is the conclusion.
* The paper takes a linear `C^1` extension of `S_0` beyond the band; here `S` is the given extension and Step 6's monotonicity is applied at the nearest band point `Xc_k` (the extension moves `S_0` by
  at most `Cn C_z h`, since `|X_k - Xc_k| <= C_z h`), so no property of the extension beyond `SmoothExt` is used.  The constant of `eq:cor-dos` is `|C_z| + C_2/(2 c_0) + pi/(4 c_0)`.

## Not formalised

The slope `|S_0'| >= 2 c_0` itself (hypothesis `BandSlope`; discharged from the window data of the assembly: `CorEigenWindows.lean`, `bandSlope_of_layer4` in `Assembly/CorEigen.lean`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting

/-- Number of nominal points `pi h (k + 1/2)`, `0 <= k <= N`, below a level `T`, as a `ceil`. -/
lemma ncard_nominal_lt (n : ℕ) {w : ℝ} (hw : 0 < w) (T : ℝ) :
    Set.ncard {k : Fin n | w * ((k : ℕ) + 1 / 2) < T} = min n ⌈T / w - 1 / 2⌉₊ := by
  have hset : {k : Fin n | w * ((k : ℕ) + 1 / 2) < T} = ↑(Finset.univ.filter (fun k : Fin n => (k : ℕ) < ⌈T / w - 1 / 2⌉₊)) := by
    ext k
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    rw [Nat.lt_ceil, lt_sub_iff_add_lt, lt_div_iff₀ hw]
    constructor <;> intro h <;> linarith
  rw [hset, Set.ncard_coe_finset]
  exact Fin.card_filter_val_lt

/-- The bounds `|#{k < n : w (k + 1/2) < s w + e} - s| <= |e| + 1` for `0 <= s <= n` and `|e| <= a`... -/
lemma ncard_nominal_bound (n : ℕ) {w : ℝ} (hw : 0 < w) {s a e : ℝ} (hs0 : 0 ≤ s) (hsn : s ≤ n) (he : |e| ≤ a) :
    |(Set.ncard {k : Fin n | w * ((k : ℕ) + 1 / 2) < w * (s + e)} : ℝ) - s| ≤ a + 1 := by
  rw [ncard_nominal_lt n hw]
  have h1 : w * (s + e) / w = s + e := by field_simp
  rw [h1]
  have hce1 : (⌈s + e - 1 / 2⌉₊ : ℝ) < max 0 (s + e - 1 / 2) + 1 := by
    rcases le_or_gt 0 (s + e - 1 / 2) with h | h
    · rw [max_eq_right h]; exact Nat.ceil_lt_add_one h
    · rw [max_eq_left h.le, Nat.ceil_eq_zero.mpr h.le]; simp
  have hce2 : s + e - 1 / 2 ≤ (⌈s + e - 1 / 2⌉₊ : ℝ) := Nat.le_ceil _
  have hea := abs_le.mp he
  rw [abs_le]
  constructor
  · rcases le_total (n : ℝ) (⌈s + e - 1 / 2⌉₊ : ℝ) with h | h
    · have : ((min n ⌈s + e - 1 / 2⌉₊ : ℕ) : ℝ) = n := by
        rw [min_eq_left (by exact_mod_cast h)]
      rw [this]; linarith
    · have : ((min n ⌈s + e - 1 / 2⌉₊ : ℕ) : ℝ) = (⌈s + e - 1 / 2⌉₊ : ℝ) := by
        rw [min_eq_right (by exact_mod_cast h)]
      rw [this]; linarith
  · have : ((min n ⌈s + e - 1 / 2⌉₊ : ℕ) : ℝ) ≤ (⌈s + e - 1 / 2⌉₊ : ℝ) := by
      exact_mod_cast min_le_right _ _
    have h3 : max 0 (s + e - 1 / 2) ≤ s + a := by
      apply max_le <;> linarith
    linarith

/-- **Abstract counting** (Step 6 of the proof of cor:eigen, first half): points `X k` whose clamped values `Xc k` in `[lo, hi]` satisfy `|Phi(Xc k) - w (k + 1/2)| <= E` for a
function `Phi` decreasing on `[lo, hi]` from `w n` to `0`: `|#{k : Y < X k} - Phi(Y)/w| <= E/w + 2` for `Y in [lo, hi]`. -/
lemma count_abstract (n : ℕ) {w E lo hi : ℝ} (hw : 0 < w) (hE : 0 ≤ E) (X Xc : Fin n → ℝ) (Φ : ℝ → ℝ)
    (hmem : ∀ k, Xc k ∈ Icc lo hi) (hr1 : ∀ k, ∀ Y ∈ Icc lo hi, Y < X k → Y ≤ Xc k)
    (hr2 : ∀ k, ∀ Y ∈ Icc lo hi, Y < Xc k → Y < X k) (hanti : AntitoneOn Φ (Icc lo hi))
    (hhi : Φ hi = 0) (hlo : Φ lo = w * n) (hlh : lo ≤ hi)
    (hy : ∀ k : Fin n, |Φ (Xc k) - w * ((k : ℕ) + 1 / 2)| ≤ E) {Y : ℝ} (hY : Y ∈ Icc lo hi) :
    |(Set.ncard {k : Fin n | Y < X k} : ℝ) - Φ Y / w| ≤ E / w + 2 := by
  have hΦ0 : 0 ≤ Φ Y := by rw [← hhi]; exact hanti hY ⟨hlh, le_rfl⟩ hY.2
  have hΦn : Φ Y ≤ w * n := by rw [← hlo]; exact hanti ⟨le_rfl, hlh⟩ hY hY.1
  set s := Φ Y / w with hs
  have hws : w * s = Φ Y := by rw [hs]; field_simp
  have hs0 : 0 ≤ s := div_nonneg hΦ0 hw.le
  have hsn : s ≤ n := by rw [hs, div_le_iff₀ hw]; linarith
  have hEw : 0 ≤ E / w := div_nonneg hE hw.le
  -- lower inclusion
  have hlow : {k : Fin n | w * ((k : ℕ) + 1 / 2) < w * (s + (-(E / w)))} ⊆ {k : Fin n | Y < X k} := by
    intro k hk
    simp only [Set.mem_setOf_eq] at hk ⊢
    have h1 : w * (s + (-(E / w))) = Φ Y - E := by
      have : w * (E / w) = E := by field_simp
      rw [mul_add, hws, mul_neg, this]; ring
    rw [h1] at hk
    have hk2 := (abs_le.mp (hy k)).2
    by_contra hcon
    have hXc : Xc k ≤ Y := by
      by_contra h3
      exact hcon (hr2 k Y hY (not_le.mp h3))
    have := hanti (hmem k) hY hXc
    have := (abs_le.mp (hy k)).1
    linarith
  have hup : {k : Fin n | Y < X k} ⊆ {k : Fin n | w * ((k : ℕ) + 1 / 2) < w * (s + (E / w + 1))} := by
    intro k hk
    simp only [Set.mem_setOf_eq] at hk ⊢
    have h1 : w * (s + (E / w + 1)) = Φ Y + E + w := by
      have : w * (E / w) = E := by field_simp
      rw [mul_add, hws, mul_add, this]; ring
    rw [h1]
    have h2 := hanti hY (hmem k) (hr1 k Y hY hk)
    have h3 := (abs_le.mp (hy k)).1
    linarith
  have hfin : ∀ T : Set (Fin n), T.Finite := fun T => Set.toFinite T
  have hb1 := ncard_nominal_bound n hw hs0 hsn (e := -(E / w)) (a := E / w) (by rw [abs_neg, abs_of_nonneg hEw])
  have hb2 := ncard_nominal_bound n hw hs0 hsn (e := E / w + 1) (a := E / w + 1) (by rw [abs_of_nonneg (by linarith)])
  have c1 := Set.ncard_le_ncard hlow (hfin _)
  have c2 := Set.ncard_le_ncard hup (hfin _)
  have c1' : ((Set.ncard {k : Fin n | w * ((k : ℕ) + 1 / 2) < w * (s + (-(E / w)))} : ℕ) : ℝ) ≤ (Set.ncard {k : Fin n | Y < X k} : ℝ) := by exact_mod_cast c1
  have c2' : ((Set.ncard {k : Fin n | Y < X k} : ℕ) : ℝ) ≤ (Set.ncard {k : Fin n | w * ((k : ℕ) + 1 / 2) < w * (s + (E / w + 1))} : ℝ) := by exact_mod_cast c2
  rw [abs_le] at hb1 hb2 ⊢
  constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2]

/-- **Midpoint rule for a Lipschitz function** (Step 6, second half): the `n` cells `[k w, (k+1) w]` of `[0, n w]` with midpoints `w (k + 1/2)`. -/
lemma midpoint_riemann (n : ℕ) {w Λ : ℝ} (hw : 0 < w) (hΛ : 0 ≤ Λ) (G : ℝ → ℝ)
    (hG : ∀ a ∈ Icc (0 : ℝ) (n * w), ∀ b ∈ Icc (0 : ℝ) (n * w), |G a - G b| ≤ Λ * |a - b|) :
    |∑ k ∈ range n, w * G (w * ((k : ℝ) + 1 / 2)) - ∫ y in (0 : ℝ)..(n * w), G y| ≤ n * (Λ * w ^ 2 / 2) := by
  have hcont : ContinuousOn G (Icc (0 : ℝ) (n * w)) := by
    have : LipschitzOnWith Λ.toNNReal G (Icc (0 : ℝ) (n * w)) := by
      refine LipschitzOnWith.of_dist_le_mul (fun a ha b hb => ?_)
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hΛ]
      exact hG a ha b hb
    exact this.continuousOn
  have hcell : ∀ k : ℕ, k < n → Icc ((k : ℝ) * w) (((k : ℝ) + 1) * w) ⊆ Icc (0 : ℝ) (n * w) := by
    intro k hk
    have hk' : ((k : ℝ) + 1) ≤ n := by exact_mod_cast hk
    exact Icc_subset_Icc (by positivity) (by nlinarith)
  have hint : ∀ k < n, IntervalIntegrable G MeasureTheory.volume ((fun j : ℕ => (j : ℝ) * w) k) ((fun j : ℕ => (j : ℝ) * w) (k + 1)) := by
    intro k hk
    have hle : (k : ℝ) * w ≤ (((k + 1 : ℕ) : ℝ)) * w := by push_cast; nlinarith
    refine (hcont.mono ?_).intervalIntegrable_of_Icc hle |>.symm.symm
    intro x hx
    exact hcell k hk (by simpa using hx)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := G) (μ := MeasureTheory.volume) (a := fun j : ℕ => (j : ℝ) * w) (n := n) hint
  simp only [Nat.cast_zero, zero_mul] at hsum
  rw [← hsum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ range n, |w * G (w * ((k : ℝ) + 1 / 2)) - ∫ x in ((k : ℝ) * w)..(((k + 1 : ℕ) : ℝ) * w), G x|
      ≤ ∑ k ∈ range n, Λ * w ^ 2 / 2 := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hk' : k < n := Finset.mem_range.mp hk
        have hkr : ((k : ℝ) + 1) ≤ n := by exact_mod_cast hk'
        have hle : (k : ℝ) * w ≤ (((k + 1 : ℕ) : ℝ)) * w := by push_cast; nlinarith
        have hi := hint k hk'
        have hc : ∫ x in ((k : ℝ) * w)..(((k + 1 : ℕ) : ℝ) * w), G (w * ((k : ℝ) + 1 / 2)) = w * G (w * ((k : ℝ) + 1 / 2)) := by
          rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; push_cast; ring
        have hd : w * G (w * ((k : ℝ) + 1 / 2)) - ∫ x in ((k : ℝ) * w)..(((k + 1 : ℕ) : ℝ) * w), G x =
            ∫ x in ((k : ℝ) * w)..(((k + 1 : ℕ) : ℝ) * w), (G (w * ((k : ℝ) + 1 / 2)) - G x) := by
          rw [intervalIntegral.integral_sub intervalIntegrable_const hi, hc]
        rw [hd]
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (k : ℝ) * w) (b := (((k + 1 : ℕ) : ℝ) * w))
          (C := Λ * (w / 2)) (f := fun x => G (w * ((k : ℝ) + 1 / 2)) - G x) (fun x hx => by
            rw [Set.uIoc_of_le hle] at hx
            have hxI : x ∈ Icc (0 : ℝ) (n * w) := hcell k hk' ⟨hx.1.le, by push_cast at hx; exact hx.2⟩
            have hmI : w * ((k : ℝ) + 1 / 2) ∈ Icc (0 : ℝ) (n * w) := hcell k hk' ⟨by nlinarith, by nlinarith⟩
            rw [Real.norm_eq_abs]
            refine (hG _ hmI _ hxI).trans (mul_le_mul_of_nonneg_left ?_ hΛ)
            rw [abs_le]
            obtain ⟨hx1, hx2⟩ := hx
            push_cast at hx2
            constructor <;> nlinarith)
        rw [Real.norm_eq_abs] at this
        refine this.trans (le_of_eq ?_)
        rw [abs_of_nonneg (by push_cast; nlinarith)]
        push_cast; ring
    _ = n * (Λ * w ^ 2 / 2) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

variable {Par : Type*} [TopologicalSpace Par]

/-- **Localisation of the rule** (B5): for `h` below the thresholds, the nearest band point `Xc_k` of every eigenvalue satisfies `|X_k - Xc_k| <= C_z h` (Step 0) and
`|S_0(Xc_k) - pi h (k + 1/2)| <= (|C| + |Cn| C_z) h` (the rule at `M = 0` and the Lipschitz bound of `S_0` on the extended interval). -/
lemma localise_rule {F : SymbolFamily Par} {K : Set Par} {S : ℕ → Par → ℝ → ℝ} {δ Cn hM C Cz hz : ℝ}
    (hS : SmoothExt F K 0 S δ Cn) (hlt : ∀ μ ∈ K, F.bandLo μ < F.bandHi μ)
    (hR : ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hM → ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
      IsEigenSystem (F.jacobiMat μ N) X Um → ∀ k : Fin (N + 1),
        |∑ j ∈ range (0 + 1), F.step N ^ j * S j μ (X k) - Real.pi * F.step N * ((k : ℕ) + 1 / 2)| ≤ C * F.step N ^ (0 + 1))
    (hZ : ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hz → ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
      IsEigenSystem (F.jacobiMat μ N) X Um → ∀ k : Fin (N + 1),
        F.bandLo μ - Cz * F.step N ≤ X k ∧ X k ≤ F.bandHi μ + Cz * F.step N)
    (hδ : 0 < δ) {μ : Par} (hμ : μ ∈ K) {N : ℕ}
    (hN : F.step N ≤ min (min hM hz) (δ / (|Cz| + 1)))
    {X : Fin (N + 1) → ℝ} {Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hE : IsEigenSystem (F.jacobiMat μ N) X Um) (k : Fin (N + 1)) :
    |X k - clampB (F.bandLo μ) (F.bandHi μ) (X k)| ≤ |Cz| * F.step N ∧
    |S 0 μ (clampB (F.bandLo μ) (F.bandHi μ) (X k)) - Real.pi * F.step N * ((k : ℕ) + 1 / 2)| ≤ (|C| + |Cn| * |Cz|) * F.step N := by
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have h1 : F.step N ≤ hM := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : F.step N ≤ hz := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : F.step N ≤ δ / (|Cz| + 1) := hN.trans (min_le_right _ _)
  have hCzh : |Cz| * F.step N ≤ δ := by
    rw [le_div_iff₀ (by positivity)] at h3
    nlinarith [abs_nonneg Cz]
  obtain ⟨hz1, hz2⟩ := hZ μ hμ N h2 X Um hE k
  have hle : Cz * F.step N ≤ |Cz| * F.step N := mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le
  have hle2 : -(Cz * F.step N) ≤ |Cz| * F.step N := by
    have := mul_le_mul_of_nonneg_right (neg_le_abs Cz) hpos.le
    linarith
  have hd := clampB_dist (hlt μ hμ).le (mul_nonneg (abs_nonneg Cz) hpos.le) (c := |Cz| * F.step N) (x := X k) (by linarith) (by linarith)
  refine ⟨hd, ?_⟩
  have hcm := clampB_mem (hlt μ hμ).le (X k)
  have hXD : X k ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ) := ⟨by linarith, by linarith⟩
  have hcD : clampB (F.bandLo μ) (F.bandHi μ) (X k) ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ) :=
    band_sub_ext hδ (hlt μ hμ) hcm
  have hlip := hS.lip_zero hμ (Nat.zero_le _) hXD hcD
  have hrule := hR μ hμ N h1 X Um hE k
  simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, pow_one] at hrule
  have hCn : 0 ≤ Cn := by
    have := (hS μ hμ 0 le_rfl).2 0 (Nat.zero_le _) (X k) hXD
    exact (abs_nonneg _).trans this
  have e : S 0 μ (clampB (F.bandLo μ) (F.bandHi μ) (X k)) - Real.pi * F.step N * ((k : ℕ) + 1 / 2) =
      (S 0 μ (X k) - Real.pi * F.step N * ((k : ℕ) + 1 / 2)) - (S 0 μ (X k) - S 0 μ (clampB (F.bandLo μ) (F.bandHi μ) (X k))) := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  have hb1 : |S 0 μ (X k) - Real.pi * F.step N * ((k : ℕ) + 1 / 2)| ≤ |C| * F.step N :=
    hrule.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le)
  have hb2 : |S 0 μ (X k) - S 0 μ (clampB (F.bandLo μ) (F.bandHi μ) (X k))| ≤ |Cn| * |Cz| * F.step N :=
    hlip.trans (by
      calc Cn * |X k - clampB (F.bandLo μ) (F.bandHi μ) (X k)| ≤ |Cn| * (|Cz| * F.step N) :=
            mul_le_mul (le_abs_self _) hd (abs_nonneg _) (abs_nonneg _)
        _ = |Cn| * |Cz| * F.step N := by ring)
  calc _ ≤ |C| * F.step N + |Cn| * |Cz| * F.step N := add_le_add hb1 hb2
    _ = (|C| + |Cn| * |Cz|) * F.step N := by ring

/-- **Substitution `y = S_0(X)`** (Step 6): `int_{lo}^{hi} g(X) (-S_0'(X)) dX = int_0^Pi g(x_0(y)) dy` for `S_0` strictly decreasing and `C^1` from `Pi` to `0`, `x_0` its inverse. -/
lemma cov_lemma {lo hi Pi0 : ℝ} {S0 S0' g x0 : ℝ → ℝ} (hlh : lo ≤ hi)
    (hf : ContinuousOn S0 (Icc lo hi)) (hder : ∀ x ∈ Ioo lo hi, HasDerivAt S0 (S0' x) x) (hf' : ContinuousOn S0' (Icc lo hi))
    (hanti : StrictAntiOn S0 (Icc lo hi)) (hhi : S0 hi = 0) (hlo : S0 lo = Pi0)
    (hg : ContinuousOn g (Icc lo hi)) (hx0 : ∀ y ∈ Icc 0 Pi0, x0 y ∈ Icc lo hi ∧ S0 (x0 y) = y)
    (hGc : ContinuousOn (fun y => g (x0 y)) (Icc 0 Pi0)) :
    ∫ Y in lo..hi, g Y * (-S0' Y) = ∫ y in (0 : ℝ)..Pi0, g (x0 y) := by
  have hrange : ∀ x ∈ Icc lo hi, S0 x ∈ Icc 0 Pi0 := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [← hhi]; exact hanti.antitoneOn hx ⟨hlh, le_rfl⟩ hx.2
    · rw [← hlo]; exact hanti.antitoneOn ⟨le_rfl, hlh⟩ hx hx.1
  have hinv : ∀ x ∈ Icc lo hi, x0 (S0 x) = x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hx0 _ (hrange x hx)
    exact hanti.injOn h1 hx h2
  have hP : (0 : ℝ) ≤ Pi0 := by rw [← hlo]; exact (hrange lo ⟨le_rfl, hlh⟩).1
  have key := intervalIntegral.integral_comp_mul_deriv'' (a := lo) (b := hi) (f := S0) (f' := S0')
    (g := fun y => g (x0 y)) (by rwa [Set.uIcc_of_le hlh]) (fun x hx => by
      rw [min_eq_left hlh, max_eq_right hlh] at hx
      exact (hder x hx).hasDerivWithinAt) (by rwa [Set.uIcc_of_le hlh]) (by
      refine hGc.mono ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [Set.uIcc_of_le hlh] at hx
      exact hrange x hx)
  have lhs : ∫ x in lo..hi, ((fun y => g (x0 y)) ∘ S0) x * S0' x = ∫ x in lo..hi, g x * S0' x := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hlh] at hx
    simp only [Function.comp, hinv x hx]
  rw [lhs, hhi, hlo, intervalIntegral.integral_symm (0 : ℝ) Pi0] at key
  have : ∫ Y in lo..hi, g Y * (-S0' Y) = -∫ x in lo..hi, g x * S0' x := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr (fun x _ => by ring)
  rw [this, key]
  ring

/-- The conclusion of `CorEigenCount` for one family `S` (exactly the frozen text). -/
def CountConcl (F : SymbolFamily Par) (K : Set Par) (S : ℕ → Par → ℝ → ℝ) : Prop :=
  (∃ C1 h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
    ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
      ∀ Y ∈ Icc (F.bandLo μ) (F.bandHi μ),
        |(Set.ncard {k : Fin (N + 1) | Y < X k} : ℝ) - S 0 μ Y / (Real.pi * F.step N)| ≤ C1) ∧
  (∃ δ' : ℝ, 0 < δ' ∧ ∃ C1 h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
    ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
      ∀ (g : ℝ → ℝ) (Lg : ℝ), 0 ≤ Lg →
        (∀ a ∈ Icc (F.bandLo μ - δ') (F.bandHi μ + δ'), ∀ b ∈ Icc (F.bandLo μ - δ') (F.bandHi μ + δ'), |g a - g b| ≤ Lg * |a - b|) →
          |F.step N / F.L * ∑ k : Fin (N + 1), g (X k) -
            1 / (Real.pi * F.L) * ∫ Y in (F.bandLo μ)..(F.bandHi μ), g Y * (-deriv (S 0 μ) Y)| ≤ C1 * F.step N * Lg)

/-- **cor:eigen (d), counting, first half** (`eq:cor-count`), under `(D_0)`, `0 < delta` (finding F-BB-1) and the slope input `BandSlope` (F-BB-2). -/
theorem corEigenCount_count (F : SymbolFamily Par) (K : Set Par) (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K 0)
    (S : ℕ → Par → ℝ → ℝ) (δ Cn hM C : ℝ) (hδ : 0 < δ) (hS : SmoothExt F K 0 S δ Cn) (hR : EigenRule F K 0 S hM C)
    (hA : ActionFormula F K S) (hsl : BandSlope F K S) :
    ∃ C1 h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ Y ∈ Icc (F.bandLo μ) (F.bandHi μ),
          |(Set.ncard {k : Fin (N + 1) | Y < X k} : ℝ) - S 0 μ Y / (Real.pi * F.step N)| ≤ C1 := by
  obtain ⟨c0, hc0, hsl⟩ := hsl
  obtain ⟨Cz, hz0, hzp, hzero⟩ := stepZeroD0 F K hK hH hD
  obtain ⟨hMpos, hrule⟩ := hR
  have hlt := bandLo_lt_bandHi F K 0 hH hD
  refine ⟨(|C| + |Cn| * |Cz|) / Real.pi + 2, min (min hM hz0) (δ / (|Cz| + 1)),
    lt_min (lt_min hMpos hzp) (div_pos hδ (by positivity)), ?_⟩
  intro μ hμ N hN X Um hE Y hY
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hloc := fun k => localise_rule hS hlt hrule hzero hδ hμ hN hE k
  have hL : F.step N * ((N : ℝ) + 1) = F.L := step_mul_succ_aux F N
  have hanti := (BandSlope.strictAnti hS hδ hμ (hlt μ hμ) hc0 (hsl μ hμ)).antitoneOn
  have hw : 0 < Real.pi * F.step N := mul_pos Real.pi_pos hpos
  have key := count_abstract (N + 1) hw (E := (|C| + |Cn| * |Cz|) * F.step N) (lo := F.bandLo μ) (hi := F.bandHi μ)
    (mul_nonneg (by positivity) hpos.le) X (fun k => clampB (F.bandLo μ) (F.bandHi μ) (X k)) (S 0 μ)
    (fun k => clampB_mem (hlt μ hμ).le _)
    (fun k Y' hY' hlt' => by
      unfold clampB
      exact le_max_of_le_right (le_min hlt'.le hY'.2))
    (fun k Y' hY' hlt' => by
      by_contra hcon
      have h1 : X k ≤ Y' := not_lt.mp hcon
      have : clampB (F.bandLo μ) (F.bandHi μ) (X k) ≤ Y' := by
        unfold clampB
        exact max_le hY'.1 ((min_le_left _ _).trans h1)
      linarith)
    hanti
    (by rw [hA μ hμ _ ⟨(hlt μ hμ).le, le_rfl⟩]; exact actionS0_bandHi F K hH hD hμ)
    (by
      rw [hA μ hμ _ ⟨le_rfl, (hlt μ hμ).le⟩, actionS0_bandLo F K hH hD hμ]
      push_cast
      nlinarith [hL])
    (hlt μ hμ).le (fun k => by
      have := (hloc k).2
      simpa [mul_assoc] using this) hY
  refine key.trans (le_of_eq ?_)
  field_simp

/-- **cor:eigen (d), density of states** (`eq:cor-dos`), under `(D_0)`, `0 < delta` and `BandSlope`; the neighbourhood radius is `delta' = delta`. -/
theorem corEigenCount_dos (F : SymbolFamily Par) (K : Set Par) (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K 0)
    (S : ℕ → Par → ℝ → ℝ) (δ Cn hM C : ℝ) (hδ : 0 < δ) (hS : SmoothExt F K 0 S δ Cn) (hR : EigenRule F K 0 S hM C)
    (hA : ActionFormula F K S) (hsl : BandSlope F K S) :
    ∃ C1 h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ (g : ℝ → ℝ) (Lg : ℝ), 0 ≤ Lg →
          (∀ a ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ), ∀ b ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ), |g a - g b| ≤ Lg * |a - b|) →
            |F.step N / F.L * ∑ k : Fin (N + 1), g (X k) -
              1 / (Real.pi * F.L) * ∫ Y in (F.bandLo μ)..(F.bandHi μ), g Y * (-deriv (S 0 μ) Y)| ≤ C1 * F.step N * Lg := by
  obtain ⟨c0, hc0, hsl⟩ := hsl
  obtain ⟨Cz, hz0, hzp, hzero⟩ := stepZeroD0 F K hK hH hD
  obtain ⟨hMpos, hrule⟩ := hR
  have hlt := bandLo_lt_bandHi F K 0 hH hD
  set C2 : ℝ := |C| + |Cn| * |Cz| with hC2
  have hC2nn : 0 ≤ C2 := by positivity
  refine ⟨|Cz| + C2 / (2 * c0) + Real.pi / (4 * c0), min (min hM hz0) (δ / (|Cz| + 1)),
    lt_min (lt_min hMpos hzp) (div_pos hδ (by positivity)), ?_⟩
  intro μ hμ N hN X Um hE g Lg hLg hg
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hloc := fun k => localise_rule hS hlt hrule hzero hδ hμ hN hE k
  have hL : F.step N * ((N : ℝ) + 1) = F.L := step_mul_succ_aux F N
  have hLpos := F.L_pos
  set h := F.step N with hh
  set lo := F.bandLo μ with hlo
  set hi := F.bandHi μ with hhi
  have hlth := hlt μ hμ
  have hanti := BandSlope.strictAnti hS hδ hμ hlth hc0 (hsl μ hμ)
  have hsub : ∀ x ∈ Icc lo hi, ∀ y ∈ Icc lo hi, 2 * c0 * |x - y| ≤ |S 0 μ x - S 0 μ y| :=
    fun x hx y hy => BandSlope.sub_ge hS hδ hμ hlth hc0.le (hsl μ hμ) hx hy
  have hPi : Real.pi * F.L = ((N : ℝ) + 1) * (Real.pi * h) := by rw [← hL]; ring
  -- the inverse x_0
  have hex : ∀ y ∈ Icc (0 : ℝ) (Real.pi * F.L), ∃ Z, Z ∈ Icc lo hi ∧ S 0 μ Z = y := fun y hy =>
    BandSlope.surj hS hδ hA hH hD hμ hlth hy
  choose! x0 hx0 using hex
  have hx0lip : ∀ y ∈ Icc (0 : ℝ) (Real.pi * F.L), ∀ y' ∈ Icc (0 : ℝ) (Real.pi * F.L), |x0 y - x0 y'| ≤ |y - y'| / (2 * c0) := by
    intro y hy y' hy'
    have := hsub _ (hx0 y hy).1 _ (hx0 y' hy').1
    rw [(hx0 y hy).2, (hx0 y' hy').2] at this
    rw [le_div_iff₀ (by positivity)]
    linarith
  set Lam : ℝ := Lg / (2 * c0) with hLam
  have hLam0 : 0 ≤ Lam := by positivity
  set G : ℝ → ℝ := fun y => g (x0 y) with hG
  have hGlip : ∀ a ∈ Icc (0 : ℝ) (((N + 1 : ℕ) : ℝ) * (Real.pi * h)), ∀ b ∈ Icc (0 : ℝ) (((N + 1 : ℕ) : ℝ) * (Real.pi * h)),
      |G a - G b| ≤ Lam * |a - b| := by
    intro a ha b hb
    push_cast at ha hb
    rw [← hPi] at ha hb
    have h1 := hg _ (band_sub_ext hδ hlth (hx0 a ha).1) _ (band_sub_ext hδ hlth (hx0 b hb).1)
    have h2 := hx0lip a ha b hb
    calc |G a - G b| ≤ Lg * |x0 a - x0 b| := h1
      _ ≤ Lg * (|a - b| / (2 * c0)) := mul_le_mul_of_nonneg_left h2 hLg
      _ = Lam * |a - b| := by rw [hLam]; ring
  -- continuity of G on [0, pi L]
  have hGcont : ContinuousOn G (Icc (0 : ℝ) (Real.pi * F.L)) := by
    have : LipschitzOnWith Lam.toNNReal G (Icc (0 : ℝ) (Real.pi * F.L)) := by
      refine LipschitzOnWith.of_dist_le_mul (fun a ha b hb => ?_)
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hLam0]
      refine hGlip a ?_ b ?_ <;> (push_cast; rw [← hPi]; assumption)
    exact this.continuousOn
  have hgcont : ContinuousOn g (Icc lo hi) := by
    have : LipschitzOnWith Lg.toNNReal g (Icc lo hi) := by
      refine LipschitzOnWith.of_dist_le_mul (fun a ha b hb => ?_)
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hLg]
      exact hg a (band_sub_ext hδ hlth ha) b (band_sub_ext hδ hlth hb)
    exact this.continuousOn
  -- change of variables
  have hcov : ∫ Y in lo..hi, g Y * (-deriv (S 0 μ) Y) = ∫ y in (0 : ℝ)..(Real.pi * F.L), G y := by
    refine cov_lemma hlth.le (((hS μ hμ 0 le_rfl).1.continuousOn).mono (band_sub_ext hδ hlth)) (fun x hx => ?_) ?_ hanti
      (by rw [hA μ hμ _ ⟨hlth.le, le_rfl⟩]; exact actionS0_bandHi F K hH hD hμ)
      (by rw [hA μ hμ _ ⟨le_rfl, hlth.le⟩]; exact actionS0_bandLo F K hH hD hμ) hgcont hx0 hGcont
    · exact (hS.diffAt hμ (Nat.zero_le _) (ioo_band_sub_ext hδ hx)).hasDerivAt
    · exact (hS.deriv_continuousOn hμ (Nat.zero_le _) (by linarith)).mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  -- the per-eigenvalue comparison
  have hCzh : |Cz| * h ≤ δ := by
    have h3 : h ≤ δ / (|Cz| + 1) := hN.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h3
    nlinarith [abs_nonneg Cz]
  have hk : ∀ k : Fin (N + 1), |g (X k) - G (Real.pi * h * ((k : ℕ) + 1 / 2))| ≤ Lg * ((|Cz| + C2 / (2 * c0)) * h) := by
    intro k
    obtain ⟨hd, hrl⟩ := hloc k
    have hcm := clampB_mem hlth.le (X k)
    have hyk : Real.pi * h * ((k : ℕ) + 1 / 2) ∈ Icc (0 : ℝ) (Real.pi * F.L) := by
      have hk1 : ((k : ℕ) : ℝ) + 1 / 2 ≤ (N : ℝ) + 1 := by
        have : ((k : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp k.isLt
        linarith
      refine ⟨by positivity, ?_⟩
      rw [hPi]
      have := mul_le_mul_of_nonneg_left hk1 (mul_nonneg Real.pi_pos.le hpos.le)
      nlinarith
    obtain ⟨hxm, hxe⟩ := hx0 _ hyk
    have h1 : 2 * c0 * |clampB lo hi (X k) - x0 (Real.pi * h * ((k : ℕ) + 1 / 2))| ≤ C2 * h := by
      have := hsub _ hcm _ hxm
      rw [hxe] at this
      exact this.trans hrl
    have h2 : |clampB lo hi (X k) - x0 (Real.pi * h * ((k : ℕ) + 1 / 2))| ≤ C2 * h / (2 * c0) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hXD : X k ∈ Icc (lo - δ) (hi + δ) := by
      have := abs_le.mp hd
      exact ⟨by linarith [hcm.1], by linarith [hcm.2]⟩
    have h3 := hg _ hXD _ (band_sub_ext hδ hlth hxm)
    refine h3.trans (mul_le_mul_of_nonneg_left ?_ hLg)
    calc |X k - x0 (Real.pi * h * ((k : ℕ) + 1 / 2))|
        = |(X k - clampB lo hi (X k)) + (clampB lo hi (X k) - x0 (Real.pi * h * ((k : ℕ) + 1 / 2)))| := by ring_nf
      _ ≤ |X k - clampB lo hi (X k)| + |clampB lo hi (X k) - x0 (Real.pi * h * ((k : ℕ) + 1 / 2))| := abs_add_le _ _
      _ ≤ |Cz| * h + C2 * h / (2 * c0) := add_le_add hd h2
      _ = (|Cz| + C2 / (2 * c0)) * h := by ring
  -- sums
  have hmid := midpoint_riemann (N + 1) (w := Real.pi * h) (Λ := Lam) (mul_pos Real.pi_pos hpos) hLam0 G hGlip
  have hupper : ((N + 1 : ℕ) : ℝ) * (Real.pi * h) = Real.pi * F.L := by push_cast; rw [hPi]
  rw [hupper] at hmid
  have hsumFin : ∑ k : Fin (N + 1), G (Real.pi * h * ((k : ℕ) + 1 / 2)) = ∑ k ∈ range (N + 1), G (Real.pi * h * ((k : ℝ) + 1 / 2)) :=
    Fin.sum_univ_eq_sum_range (fun j : ℕ => G (Real.pi * h * ((j : ℝ) + 1 / 2))) (N + 1)
  have hsumA : |∑ k : Fin (N + 1), g (X k) - ∑ k : Fin (N + 1), G (Real.pi * h * ((k : ℕ) + 1 / 2))| ≤
      ((N : ℝ) + 1) * (Lg * ((|Cz| + C2 / (2 * c0)) * h)) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k : Fin (N + 1), |g (X k) - G (Real.pi * h * ((k : ℕ) + 1 / 2))| ≤ ∑ k : Fin (N + 1), Lg * ((|Cz| + C2 / (2 * c0)) * h) :=
          Finset.sum_le_sum (fun k _ => hk k)
      _ = ((N : ℝ) + 1) * (Lg * ((|Cz| + C2 / (2 * c0)) * h)) := by simp
  rw [hcov]
  -- assemble
  set SG := ∑ k : Fin (N + 1), G (Real.pi * h * ((k : ℕ) + 1 / 2)) with hSG
  set Sg := ∑ k : Fin (N + 1), g (X k) with hSg
  set I := ∫ y in (0 : ℝ)..(Real.pi * F.L), G y with hI
  have hmid' : |Real.pi * h * SG - I| ≤ ((N : ℝ) + 1) * (Lam * (Real.pi * h) ^ 2 / 2) := by
    have : ∑ k ∈ range (N + 1), Real.pi * h * G (Real.pi * h * ((k : ℝ) + 1 / 2)) = Real.pi * h * SG := by
      rw [← Finset.mul_sum, ← hsumFin]
    rw [this] at hmid
    simpa using hmid
  have e1 : h / F.L * Sg - 1 / (Real.pi * F.L) * I = h / F.L * (Sg - SG) + 1 / (Real.pi * F.L) * (Real.pi * h * SG - I) := by
    field_simp
    ring
  rw [e1]
  have hnh : h * ((N : ℝ) + 1) = F.L := hL
  have hn0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have b1 : |h / F.L * (Sg - SG)| ≤ Lg * (|Cz| + C2 / (2 * c0)) * h := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < h / F.L)]
    calc h / F.L * |Sg - SG| ≤ h / F.L * (((N : ℝ) + 1) * (Lg * ((|Cz| + C2 / (2 * c0)) * h))) :=
          mul_le_mul_of_nonneg_left hsumA (by positivity)
      _ = Lg * (|Cz| + C2 / (2 * c0)) * h := by
          rw [← hnh]; field_simp
  have b2 : |1 / (Real.pi * F.L) * (Real.pi * h * SG - I)| ≤ Lg * (Real.pi / (4 * c0)) * h := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (Real.pi * F.L))]
    calc 1 / (Real.pi * F.L) * |Real.pi * h * SG - I| ≤ 1 / (Real.pi * F.L) * (((N : ℝ) + 1) * (Lam * (Real.pi * h) ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left hmid' (by positivity)
      _ = Lg * (Real.pi / (4 * c0)) * h := by
          rw [hLam, ← hnh]; field_simp; ring
  calc _ ≤ |h / F.L * (Sg - SG)| + |1 / (Real.pi * F.L) * (Real.pi * h * SG - I)| := abs_add_le _ _
    _ ≤ Lg * (|Cz| + C2 / (2 * c0)) * h + Lg * (Real.pi / (4 * c0)) * h := add_le_add b1 b2
    _ = (|Cz| + C2 / (2 * c0) + Real.pi / (4 * c0)) * h * Lg := by ring

/-- **cor:eigen (d)** (`CorEigenCount`, both parts), under `(D_0)`, `0 < delta` (F-BB-1) and the slope input `BandSlope` (F-BB-2). -/
theorem corEigenCount_of_slope (F : SymbolFamily Par) (K : Set Par) (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K 0)
    (S : ℕ → Par → ℝ → ℝ) (δ Cn hM C : ℝ) (hδ : 0 < δ) (hS : SmoothExt F K 0 S δ Cn) (hR : EigenRule F K 0 S hM C)
    (hA : ActionFormula F K S) (hsl : BandSlope F K S) : CountConcl F K S :=
  ⟨corEigenCount_count F K hK hH hD S δ Cn hM C hδ hS hR hA hsl,
    δ, hδ, corEigenCount_dos F K hK hH hD S δ Cn hM C hδ hS hR hA hsl⟩

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.corEigenCount_of_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.corEigenCount_of_slope

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.count_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.count_abstract

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.midpoint_riemann' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.midpoint_riemann

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.cov_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.cov_lemma

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.corEigenCount_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.corEigenCount_count

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.corEigenCount_dos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.corEigenCount_dos

end FormalResearch.JacobiEigenvectors.TheoremA
