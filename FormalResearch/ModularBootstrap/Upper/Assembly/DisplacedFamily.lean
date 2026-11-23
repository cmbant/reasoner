module

public import FormalResearch.ModularBootstrap.Upper.Assembly.ProfileWindow
public import FormalResearch.ModularBootstrap.Upper.Assembly.TailBounds

/-!
# The displaced family `DisplacedFamily (designClass ∪ displacedClass)` (`sr:Sigma` Step 5)

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex`, proof of `sr:Sigma`, Step 5 (designs with
`f = 1`, `d = -κ`, the site `n` displaced by `e`, the others ideal with small detuning), `sr:P` (the design
class), `upper_transfer.tex` (`ut:V`, `ut:E`, `ut:Z`).

For a (0-indexed) site `n ≥ 1`, i.e. the zero `a_{n+1}`, `s = n + 1 ≥ 2`, the window `dispWin n k` is
`profWin` of the design with `N = J_n + k` ideal sites, the site `s` displaced by `e = |a_1|/2`, heights
`η_k = 1/(k + 4)` (`ε_j = η_k gap_j` for `j ≤ N`, `gap_j/4` beyond), and `d = -κ`, `κ = d₀/2`.

* `dispPi0_lower`: `Π_s(0) ≥ e²/(2|a_s - a_1|)` for `N ≥ J_s`, uniformly in `η`: the factors `j ≤ N`,
  `j ≠ s` are `≥ 1`, those `j > N` are `≥ exp(-4 (C_Z/2)/j²)` (`designFac_tail_lower`, with `u = a_s`, `j ≠ s`),
  summed by `hasProd_ge_half_of_tail_lower` (the summation of `exists_designFac_lower`), times the diagonal
  factor `((a_s - u_s)² + ε_s²)/|a_s - a_1| ≥ e²/|a_s - a_1|`.
* `dispRest_tendsto`: `∑_{m ≥ 2, m ≠ s} Π_m(d) → 0`: `Π_m(-κ) ≤ (1 + κ/Δ₁) Π_m(0)`
  (`profPi_neg_le`), `Π_m(0) ≤ C_P((a_m - u_m)² + ε_m²) m^{-2/3}` for the admissible profile
  (`profPi0_le_unif`, constant uniform in `N`, `η` since the displacement is one fixed site), and the sum of the
  majorant is `O(η² + N^{-1/3})`.
* **`virasoro_sigma_of_omitted`**: `virasoro_sigma` with the `SameSiteFamily` and the displaced family discharged: the
  remaining inputs of `Σ` at Virasoro are `∀ S, DesignPropertyP S.μS 𝒟x` and `OmittedFamily (designClass ∪ 𝒟x)`.
* **`displacedFamily`**: `DisplacedFamily displacedClass`; `displacedFamily_union`:
  `DisplacedFamily (designClass ∪ displacedClass)`, the input of `virasoro_sigma`.  All fields are proved:
  `pi_nonneg` is `W ≥ 0` on `u ≤ u_f = a_1 + κ` (every `a_n ≤ a_1 < u_f`), not `profV_identity`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Ramped

/-! ### Estimates for the design sites and widths -/

lemma gapWKB_sq_le {n : ℕ} (hn : 1 ≤ n) :
    gapWKB n ^ 2 ≤ gapConst ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsq := pow_le_pow_left₀ (gapWKB_pos hn).le (gapWKB_le_mul_rpow hn) 2
  change gapWKB n ^ 2 ≤ (gapConst * (n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 at hsq
  rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hn_pos.le,
    show -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) by norm_num] at hsq
  exact hsq

/-- **Majorant of the diagonal factor** for the design `D(N, η, ·)`: for every `n ≥ 2`,
`((a_n - u_n)² + ε_n²) n^{-2/3} ≤ A (η² n^{-4/3} + 1_{n > N} n^{-4/3})`. -/
lemma design_diag_le :
    ∃ A > 0, ∀ (N : ℕ) (η : ℝ), 0 ≤ η → η ≤ 1 / 4 → ∀ n : ℕ, 2 ≤ n →
      ((airyZero n - designSiteU N n) ^ 2 + (designWidthU N η n) ^ 2) * (n : ℝ) ^ (-(2 / 3 : ℝ)) ≤
        A * (η ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) + (if N < n then (n : ℝ) ^ (-(4 / 3 : ℝ)) else 0)) := by
  obtain ⟨C_Z, hC_Z, hδ⟩ := deltaWKB_le_exists
  have hg := gapConst_pos
  refine ⟨max (gapConst ^ 2) (C_Z ^ 2 + gapConst ^ 2), by positivity, fun N η hη0 hη1 n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hp23 : 0 ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  have e2 : (n : ℝ) ^ (-(2 / 3 : ℝ)) * (n : ℝ) ^ (-(2 / 3 : ℝ)) = (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
    rw [← Real.rpow_add hn_pos]; norm_num
  have h43 : 0 ≤ (n : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
  have hmax1 : gapConst ^ 2 ≤ max (gapConst ^ 2) (C_Z ^ 2 + gapConst ^ 2) := le_max_left _ _
  have hmax2 : C_Z ^ 2 + gapConst ^ 2 ≤ max (gapConst ^ 2) (C_Z ^ 2 + gapConst ^ 2) := le_max_right _ _
  have hgap := gapWKB_sq_le hn1
  by_cases hnN : n ≤ N
  · have hs : designSiteU N n = airyZero n := by simp [designSiteU, hnN]
    have hw : designWidthU N η n = η * gapWKB n := by simp [designWidthU, hnN]
    have hnl : ¬ N < n := not_lt.mpr hnN
    rw [hs, sub_self, zero_pow two_ne_zero, zero_add, hw, mul_pow]
    simp only [hnl, ↓reduceIte, add_zero]
    calc η ^ 2 * gapWKB n ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ))
        ≤ η ^ 2 * (gapConst ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ))) * (n : ℝ) ^ (-(2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap (sq_nonneg _)) hp23
      _ = gapConst ^ 2 * (η ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ))) := by rw [← e2]; ring
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_right hmax1 (mul_nonneg (sq_nonneg η) h43)
          nlinarith
  · have hNn : N < n := by omega
    have hs : designSiteU N n = uWKB n := by simp [designSiteU, hnN]
    have hw : designWidthU N η n = (1 / 4 : ℝ) * gapWKB n := by simp [designWidthU, hnN]
    have h1 : |airyZero n - uWKB n| ≤ C_Z * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
      simpa [deltaWKB] using hδ n hn1
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-(4 / 3 : ℝ))) 2, ← Real.rpow_mul hn_pos.le,
      show -(4 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(8 / 3 : ℝ) by norm_num] at h2
    have h10 : (n : ℝ) ^ (-(8 / 3 : ℝ)) * (n : ℝ) ^ (-(2 / 3 : ℝ)) ≤ (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hn_pos]
      exact Real.rpow_le_rpow_of_exponent_le hn1' (by norm_num)
    rw [hs, hw]
    simp only [hNn, ↓reduceIte]
    have hw2 : ((1 / 4 : ℝ) * gapWKB n) ^ 2 ≤ gapConst ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
      rw [mul_pow]
      nlinarith [sq_nonneg (gapWKB n)]
    have hsum : (airyZero n - uWKB n) ^ 2 + ((1 / 4 : ℝ) * gapWKB n) ^ 2 ≤
        C_Z ^ 2 * (n : ℝ) ^ (-(8 / 3 : ℝ)) + gapConst ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ)) :=
      add_le_add h2 hw2
    calc ((airyZero n - uWKB n) ^ 2 + ((1 / 4 : ℝ) * gapWKB n) ^ 2) * (n : ℝ) ^ (-(2 / 3 : ℝ))
        ≤ (C_Z ^ 2 * (n : ℝ) ^ (-(8 / 3 : ℝ)) + gapConst ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ))) *
            (n : ℝ) ^ (-(2 / 3 : ℝ)) := mul_le_mul_of_nonneg_right hsum hp23
      _ = C_Z ^ 2 * ((n : ℝ) ^ (-(8 / 3 : ℝ)) * (n : ℝ) ^ (-(2 / 3 : ℝ))) +
            gapConst ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by rw [← e2]; ring
      _ ≤ C_Z ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) + gapConst ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
          have := mul_le_mul_of_nonneg_left h10 (sq_nonneg C_Z)
          linarith
      _ = (C_Z ^ 2 + gapConst ^ 2) * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by ring
      _ ≤ _ := by
          have h3 := mul_le_mul_of_nonneg_right hmax2 h43
          nlinarith [mul_nonneg (sq_nonneg η) h43, mul_nonneg (le_trans (by positivity) hmax1) (mul_nonneg (sq_nonneg η) h43)]

/-! ### One displaced site -/

/-- The displacement vector: `e` at the site `s`, `0` elsewhere. -/
noncomputable def dispE (s : ℕ) (e : ℝ) (k : ℕ) : ℝ := if k = s then e else 0

lemma dispE_self (s : ℕ) (e : ℝ) : dispE s e s = e := by simp [dispE]

lemma dispE_of_ne {s k : ℕ} (e : ℝ) (h : k ≠ s) : dispE s e k = 0 := by simp [dispE, h]

/-- The admissible-profile constant of the designs with finitely many displaced sites (`e` supported on the
finite set `D`) is uniform in `N` and `η`. -/
lemma dispProfHyp_D (D : Finset ℕ) (e : ℕ → ℝ) (he : ∀ k, k ∉ D → e k = 0) :
    ∃ C0 > 0, ∀ (N : ℕ) (η : ℝ), 0 ≤ η → η ≤ 1 / 4 →
      ProfHyp C0 (dispSite N e) (designWidthU N η) := by
  obtain ⟨C0r, hC0r, hprof⟩ := rampedProfile_profHyp
  refine ⟨C0r + ∑ j ∈ D, |e j| * (j : ℝ) ^ (4 / 3 : ℝ), by positivity, fun N η hη0 hη1 k hk => ?_⟩
  have hηf : AdmHeights (fun j => if j ≤ N then η else 1 / 4) := fun j _ => by
    show 0 ≤ (if j ≤ N then η else 1 / 4) ∧ (if j ≤ N then η else 1 / 4) ≤ 1 / 4
    split_ifs
    · exact ⟨hη0, hη1⟩
    · exact ⟨by norm_num, le_rfl⟩
  have hw : designWidthU N η = rampedWidthU (fun j => if j ≤ N then η else 1 / 4) := rfl
  obtain ⟨h1, h2, h3⟩ := hprof N _ hηf k hk
  rw [← hw] at h2 h3
  have hk43 : 0 ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
  have hk13 : 0 ≤ (k : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  have hB : 0 ≤ ∑ j ∈ D, |e j| * (j : ℝ) ^ (4 / 3 : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨?_, h2, h3.trans (mul_le_mul_of_nonneg_right (by linarith) hk13)⟩
  have hdisp : |e k| ≤ (∑ j ∈ D, |e j| * (j : ℝ) ^ (4 / 3 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
    by_cases hkD : k ∈ D
    · have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hle := Finset.single_le_sum (f := fun j : ℕ => |e j| * (j : ℝ) ^ (4 / 3 : ℝ))
        (fun _ _ => by positivity) hkD
      have h1 : (k : ℝ) ^ (4 / 3 : ℝ) * (k : ℝ) ^ (-(4 / 3 : ℝ)) = 1 := by
        rw [← Real.rpow_add hk0]; norm_num
      calc |e k| = |e k| * (k : ℝ) ^ (4 / 3 : ℝ) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
            rw [mul_assoc, h1, mul_one]
        _ ≤ _ := mul_le_mul_of_nonneg_right hle (by positivity)
    · rw [he k hkD, abs_zero]
      positivity
  calc |dispSite N e k - airyZero k|
      = |(designSiteU N k - airyZero k) + e k| := by unfold dispSite; ring_nf
    _ ≤ |designSiteU N k - airyZero k| + |e k| := abs_add_le _ _
    _ ≤ C0r * (k : ℝ) ^ (-(4 / 3 : ℝ)) + (∑ j ∈ D, |e j| * (j : ℝ) ^ (4 / 3 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ)) :=
        add_le_add h1 hdisp
    _ = _ := by ring

/-- The admissible-profile constant of the displaced designs is uniform in `N` and `η`. -/
lemma dispProfHyp (s : ℕ) (e : ℝ) :
    ∃ C0 > 0, ∀ (N : ℕ) (η : ℝ), 0 ≤ η → η ≤ 1 / 4 →
      ProfHyp C0 (dispSite N (dispE s e)) (designWidthU N η) :=
  by
  obtain ⟨C0, hC0, h⟩ := dispProfHyp_D {s} (dispE s e) (fun k hk => dispE_of_ne e (by simpa using hk))
  exact ⟨C0, hC0, h⟩

/-- The tail hypothesis for the designs with finitely many displaced sites. -/
lemma dispTailHyp_D (D : Finset ℕ) (e : ℕ → ℝ) (he : ∀ k, k ∉ D → e k = 0) (N : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) :
    AiryProdTailHypothesis 1 (dispSite N e) (designWidthU N η) := by
  obtain ⟨C0, hC0, hP⟩ := dispProfHyp_D D e he
  exact ProfHyp.tailHyp (f := 1) le_rfl hC0 (hP N η hη0 hη1)

lemma dispTailHyp (s : ℕ) (e : ℝ) (N : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) :
    AiryProdTailHypothesis 1 (dispSite N (dispE s e)) (designWidthU N η) :=
  dispTailHyp_D {s} (dispE s e) (fun k hk => dispE_of_ne e (by simpa using hk)) N hη0 hη1

/-! ### Lower bounds `Π_s(0) ≥ e²/(2|a_s - a_1|)`, `R_1 ≥ c^f/2` -/

/-- **Product lower bound for the designs with finitely many displaced sites** (`e` supported on `[1, f]`):
for `N ≥ J(n, f)` (independent of `η` and `e`), if the factors `j ≤ f`, `j ≠ n` of the product at the zero
`a_n` are `≥ c` (`0 < c ≤ 1`), then the whole product `∏_{j ≥ 2, j ≠ n}` is `≥ c^f / 2` (the factors
`f < j ≤ N` are `≥ 1`, those `j > N` are `≥ exp(-4 (C_Z/2)/j²)`). -/
lemma exists_profProd_lower {n : ℕ} (hn : 1 ≤ n) (f : ℕ) :
    ∃ J : ℕ, f ≤ J ∧ ∀ N : ℕ, J ≤ N → ∀ (η : ℝ) (e : ℕ → ℝ), 0 < η → η ≤ 1 / 4 →
      (∀ k, f < k → e k = 0) → ∀ c : ℝ, 0 < c → c ≤ 1 →
      (∀ j : ℕ, 2 ≤ j → j ≤ f → j ≠ n →
        c ≤ profRealFactor (dispSite N e) (designWidthU N η) n j) →
      ∀ T : ℝ, HasProd (fun m : ℕ => if m + 2 = n then (1 : ℝ)
        else profRealFactor (dispSite N e) (designWidthU N η) n (m + 2)) T → c ^ f / 2 ≤ T := by
  obtain ⟨C_Z, hC_Z, hZ⟩ := deltaWKB_le_exists
  set r : ℝ := -airyZero n with hr
  refine ⟨⌈max (max (max (4 * C_Z) ((2 * r) ^ 3)) 2) (f : ℝ)⌉₊, ?_,
    fun N hN η e hη0 hη1 he c hc0 hc1 hcf T hT => ?_⟩
  · have h : (f : ℝ) ≤ ⌈max (max (max (4 * C_Z) ((2 * r) ^ 3)) 2) (f : ℝ)⌉₊ :=
      (le_max_right _ _).trans (Nat.le_ceil _)
    exact_mod_cast h
  have hNge : max (max (max (4 * C_Z) ((2 * r) ^ 3)) 2) (f : ℝ) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hNC : 4 * C_Z ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hNge))
  have hNr : (2 * r) ^ 3 ≤ N :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hNge))
  have hN2' : (2 : ℝ) ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hNge)
  have hN2 : 2 ≤ N := by exact_mod_cast hN2'
  have hfN' : (f : ℝ) ≤ N := (le_max_right _ _).trans hNge
  have hfN : f ≤ N := by exact_mod_cast hfN'
  refine hasProd_ge_pow_half_of_tail_lower hC_Z hN2 hNC hfN hc0 hc1 hT fun m => ?_
  by_cases hm : m + 2 = n
  · simp only [hm, ↓reduceIte]
    split_ifs
    · exact hc1
    · exact le_rfl
    · exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
  · simp only [hm, ↓reduceIte]
    by_cases h1 : m + 2 ≤ f
    · simp only [h1, ↓reduceIte]
      exact hcf (m + 2) (by omega) h1 hm
    · simp only [h1, ↓reduceIte]
      have hsite : dispSite N e (m + 2) = designSiteU N (m + 2) :=
        dispSite_of_eq_zero (he _ (by omega))
      have hne : airyZero n ≠ airyZero (m + 2) := fun h =>
        hm (airyZero_injective_on (by omega) (by omega) h).symm
      have hfac : profRealFactor (dispSite N e) (designWidthU N η) n (m + 2) =
          designFac N η (airyZero n) (m + 2) := by
        unfold profRealFactor designFac; rw [hsite]
      rw [hfac]
      split_ifs with h
      · unfold designFac
        have hs' : designSiteU N (m + 2) = airyZero (m + 2) := by simp [designSiteU, h]
        rw [hs']
        have hpos : 0 < (airyZero n - airyZero (m + 2)) ^ 2 := by
          have := sub_ne_zero.mpr hne
          positivity
        rw [le_div_iff₀ hpos]
        nlinarith [sq_nonneg (designWidthU N η (m + 2))]
      · exact designFac_tail_lower hC_Z hZ (by omega) hN2 hNC hNr η (airyZero n) (by rw [hr]; linarith)

/-- **`pi_lower`, product part**, finitely many displaced sites: for the site `2 ≤ s ≤ f`, if the other
factors `j ≤ f` are `≥ c`, then `Π_s(0) ≥ e_s² c^f / (2 |a_s - a_1|)` for every `N ≥ J` and every `η`. -/
lemma exists_dispPi0_lower_D {s : ℕ} (hs : 2 ≤ s) (f : ℕ) (hsf : s ≤ f) :
    ∃ J : ℕ, f ≤ J ∧ ∀ N : ℕ, J ≤ N → ∀ (η : ℝ) (e : ℕ → ℝ), 0 < η → η ≤ 1 / 4 →
      (∀ k, f < k → e k = 0) → ∀ c : ℝ, 0 < c → c ≤ 1 →
      (∀ j : ℕ, 2 ≤ j → j ≤ f → j ≠ s →
        c ≤ profRealFactor (dispSite N e) (designWidthU N η) s j) →
      (e s) ^ 2 * (c ^ f / 2) / |airyZero s - airyZero 1| ≤
        profPi0 (dispSite N e) (designWidthU N η) s := by
  obtain ⟨J, hJ, h⟩ := exists_profProd_lower (n := s) (by omega) f
  refine ⟨J, hJ, fun N hN η e hη0 hη1 he c hc0 hc1 hcf => ?_⟩
  have hsN : s ≤ N := hsf.trans (hJ.trans hN)
  have hH := dispTailHyp_D (Finset.range (f + 1)) e (fun k hk => he k (by simpa using hk)) N hη0.le hη1
  have hp := (profPi0_hasProd (dispSite N e) (designWidthU N η) hH hs).1
  have hT := h N hN η e hη0 hη1 he c hc0 hc1 hcf _ hp
  unfold profPi0
  have hdiag : (e s) ^ 2 / |airyZero s - airyZero 1| ≤
      ((airyZero s - dispSite N e s) ^ 2 + (designWidthU N η s) ^ 2) / |airyZero s - airyZero 1| := by
    refine div_le_div_of_nonneg_right ?_ (abs_airyZero_sub_one_pos hs).le
    have : dispSite N e s = airyZero s + e s := by
      unfold dispSite; rw [show designSiteU N s = airyZero s by simp [designSiteU, hsN]]
    rw [this]; nlinarith [sq_nonneg (designWidthU N η s)]
  have hnn : 0 ≤ (e s) ^ 2 / |airyZero s - airyZero 1| := by positivity
  calc (e s) ^ 2 * (c ^ f / 2) / |airyZero s - airyZero 1|
      = (e s) ^ 2 / |airyZero s - airyZero 1| * (c ^ f / 2) := by ring
    _ ≤ _ := mul_le_mul hdiag hT (by positivity) (hnn.trans hdiag)

lemma one_le_profRealFactor {uSite epsU : ℕ → ℝ} {n j : ℕ} (h : uSite j = airyZero j)
    (hne : airyZero n ≠ airyZero j) : 1 ≤ profRealFactor uSite epsU n j := by
  unfold profRealFactor
  rw [h]
  have hpos : 0 < (airyZero n - airyZero j) ^ 2 := by
    have := sub_ne_zero.mpr hne
    positivity
  rw [le_div_iff₀ hpos]
  nlinarith [sq_nonneg (epsU j)]

/-- **`pi_lower`, product part**: the designs with the site `s ≥ 2` displaced by `e` have
`Π_s(0) ≥ e²/(2|a_s - a_1|)` for every `N ≥ J` and every `η`. -/
lemma exists_dispPi0_lower {s : ℕ} (hs : 2 ≤ s) :
    ∃ J : ℕ, s ≤ J ∧ ∀ N : ℕ, J ≤ N → ∀ (η e : ℝ), 0 < η → η ≤ 1 / 4 →
      e ^ 2 / (2 * |airyZero s - airyZero 1|) ≤
        profPi0 (dispSite N (dispE s e)) (designWidthU N η) s := by
  obtain ⟨J, hJ, h⟩ := exists_dispPi0_lower_D hs s le_rfl
  refine ⟨J, hJ, fun N hN η e hη0 hη1 => ?_⟩
  have h1 := h N hN η (dispE s e) hη0 hη1 (fun k hk => dispE_of_ne e (by omega)) 1 one_pos le_rfl
    (fun j hj2 hjf hjne => by
      refine one_le_profRealFactor ?_ (fun h => hjne (airyZero_injective_on (by omega) (by omega) h).symm)
      rw [dispSite_of_eq_zero (dispE_of_ne e hjne)]
      simp [designSiteU, show j ≤ N by omega])
  have hpos : 0 < |airyZero s - airyZero 1| := abs_airyZero_sub_one_pos hs
  rw [dispE_self] at h1
  calc e ^ 2 / (2 * |airyZero s - airyZero 1|) = e ^ 2 * (1 ^ s / 2) / |airyZero s - airyZero 1| := by
        rw [one_pow]; field_simp
    _ ≤ _ := h1

/-- **Lower bound of `R_1`**, finitely many displaced sites: if the factors `2 ≤ j ≤ f` of
`R_1 = ∏_{j ≥ 2} ((a_1 - u_j)² + ε_j²)/(a_1 - a_j)²` are `≥ c`, then `R_1 ≥ c^f/2` for `N ≥ J`. -/
lemma exists_dispR1_lower (f : ℕ) :
    ∃ J : ℕ, f ≤ J ∧ ∀ N : ℕ, J ≤ N → ∀ (η : ℝ) (e : ℕ → ℝ), 0 < η → η ≤ 1 / 4 →
      (∀ k, f < k → e k = 0) → ∀ c : ℝ, 0 < c → c ≤ 1 →
      (∀ j : ℕ, 2 ≤ j → j ≤ f →
        c ≤ profRealFactor (dispSite N e) (designWidthU N η) 1 j) →
      c ^ f / 2 ≤ profR1 (dispSite N e) (designWidthU N η) := by
  obtain ⟨J, hJ, h⟩ := exists_profProd_lower (n := 1) le_rfl f
  refine ⟨J, hJ, fun N hN η e hη0 hη1 he c hc0 hc1 hcf => ?_⟩
  have hH := dispTailHyp_D (Finset.range (f + 1)) e (fun k hk => he k (by simpa using hk)) N hη0.le hη1
  have hp := (profR1_hasProd (dispSite N e) (designWidthU N η) hH).1
  refine h N hN η e hη0 hη1 he c hc0 hc1 (fun j hj hjf _ => hcf j hj hjf) _ ?_
  simpa [show ∀ m : ℕ, m + 2 ≠ 1 by intro m; omega] using hp

/-! ### The tail sum `∑_{m > N} m^{-4/3}` -/

lemma summable_z43 : Summable (fun m : ℕ => ((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ))) :=
  (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(4 / 3 : ℝ) < -1))

/-- `∑_m 1_{N < m+2} (m+2)^{-4/3} ≤ 3 N^{-1/3}`, with summability. -/
lemma tsum_tail_z43 (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun m : ℕ => if N < m + 2 then ((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) else 0) ∧
    ∑' m : ℕ, (if N < m + 2 then ((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) else 0) ≤
      3 * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hGs : Summable (fun m : ℕ => if N < m + 2 then ((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) else 0) :=
    Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity)
      (fun m => by split_ifs <;> first | exact le_rfl | positivity) summable_z43
  refine ⟨hGs, ?_⟩
  have hsplit := hGs.sum_add_tsum_nat_add (N - 1)
  rw [← hsplit]
  have h0 : ∑ i ∈ Finset.range (N - 1),
      (if N < i + 2 then ((i + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have := Finset.mem_range.mp hi
      have hh : ¬ N < i + 2 := by omega
      simp only [hh, ↓reduceIte]
  rw [h0, zero_add]
  refine le_trans (le_of_eq ?_) (rpow_neg_four_thirds_sum_tail N hN)
  refine tsum_congr fun m => ?_
  have hidx : m + (N - 1) + 2 = N + 1 + m := by omega
  have hh : N < N + 1 + m := by omega
  rw [hidx]
  simp only [hh, ↓reduceIte]

/-! ### The sum of the other `Π_m` -/

/-- Termwise bound of the weights `Π_m(-κ)` at the undisplaced sites `m` (`e m = 0`) by
`B (η² m^{-4/3} + 1_{m > N} m^{-4/3})`, uniformly in `N`, `η`, for the designs with finitely many displaced
sites. -/
lemma exists_dispPi_le_D (D : Finset ℕ) (e : ℕ → ℝ) (he : ∀ k, k ∉ D → e k = 0) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ B > 0, ∀ (N : ℕ) (η : ℝ), 0 ≤ η → η ≤ 1 / 4 → ∀ m : ℕ, e m = 0 → 2 ≤ m →
      profPi (dispSite N e) (designWidthU N η) (-κ) m ≤
        B * (η ^ 2 * (m : ℝ) ^ (-(4 / 3 : ℝ)) + (if N < m then (m : ℝ) ^ (-(4 / 3 : ℝ)) else 0)) := by
  obtain ⟨C0, hC0, hP⟩ := dispProfHyp_D D e he
  obtain ⟨CP, hCP, hbd⟩ := profPi0_le_unif hC0
  obtain ⟨A, hA, hdiag⟩ := design_diag_le
  have hΔ := gapOne_pos
  have hc : 0 ≤ 1 + κ / (airyZero 1 - airyZero 2) := by positivity
  refine ⟨(1 + κ / (airyZero 1 - airyZero 2)) * (CP * A), by positivity, fun N η hη0 hη1 m hem hm => ?_⟩
  have hH := dispTailHyp_D D e he N hη0 hη1
  have h1 := profPi_neg_le hH hκ hm
  have h2 := hbd _ _ (hP N η hη0 hη1) m hm
  have hsite : dispSite N e m = designSiteU N m := dispSite_of_eq_zero hem
  rw [hsite] at h2
  have h3 := hdiag N η hη0 hη1 m hm
  calc profPi (dispSite N e) (designWidthU N η) (-κ) m
      ≤ (1 + κ / (airyZero 1 - airyZero 2)) * profPi0 (dispSite N e) (designWidthU N η) m := h1
    _ ≤ (1 + κ / (airyZero 1 - airyZero 2)) *
          (CP * ((airyZero m - designSiteU N m) ^ 2 + (designWidthU N η m) ^ 2) * (m : ℝ) ^ (-(2 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 hc
    _ = (1 + κ / (airyZero 1 - airyZero 2)) * (CP *
          (((airyZero m - designSiteU N m) ^ 2 + (designWidthU N η m) ^ 2) * (m : ℝ) ^ (-(2 / 3 : ℝ)))) := by
        ring
    _ ≤ (1 + κ / (airyZero 1 - airyZero 2)) * (CP * (A * (η ^ 2 * (m : ℝ) ^ (-(4 / 3 : ℝ)) +
          (if N < m then (m : ℝ) ^ (-(4 / 3 : ℝ)) else 0)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hCP.le) hc
    _ = _ := by ring

/-- Termwise bound of the weights `Π_m(-κ)`, `m ≠ s`, by `B (η² m^{-4/3} + 1_{m > N} m^{-4/3})`,
uniformly in `N`, `η`. -/
lemma exists_dispPi_le (s : ℕ) (e κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ B > 0, ∀ (N : ℕ) (η : ℝ), 0 ≤ η → η ≤ 1 / 4 → ∀ m : ℕ, m ≠ s → 2 ≤ m →
      profPi (dispSite N (dispE s e)) (designWidthU N η) (-κ) m ≤
        B * (η ^ 2 * (m : ℝ) ^ (-(4 / 3 : ℝ)) + (if N < m then (m : ℝ) ^ (-(4 / 3 : ℝ)) else 0)) :=
  by
  obtain ⟨B, hB, h⟩ := exists_dispPi_le_D {s} (dispE s e) (fun k hk => dispE_of_ne e (by simpa using hk)) κ hκ
  exact ⟨B, hB, fun N η hη0 hη1 m hms hm => h N η hη0 hη1 m (dispE_of_ne e hms) hm⟩

/-- The sum `∑_{m ≥ 2, m ∉ D} Π_m(-κ)` is `O(η² + N^{-1/3})` for the designs with finitely many displaced
sites (`e` supported on `D`). -/
lemma exists_dispRest_le_D (D : Finset ℕ) (e : ℕ → ℝ) (he : ∀ k, k ∉ D → e k = 0) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ B > 0, ∀ (N : ℕ), 1 ≤ N → ∀ (η : ℝ), 0 ≤ η → η ≤ 1 / 4 →
      Summable (fun j : ℕ => if j + 2 ∈ D then 0 else
        profPi (dispSite N e) (designWidthU N η) (-κ) (j + 2)) ∧
      ∑' j : ℕ, (if j + 2 ∈ D then 0 else
        profPi (dispSite N e) (designWidthU N η) (-κ) (j + 2)) ≤
        B * (η ^ 2 + (N : ℝ) ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨B0, hB0, hB⟩ := exists_dispPi_le_D D e he κ hκ
  set Z : ℝ := ∑' m : ℕ, ((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun _ => by positivity
  refine ⟨B0 * (Z + 3), by positivity, fun N hN η hη0 hη1 => ?_⟩
  obtain ⟨hGs, hGle⟩ := tsum_tail_z43 N hN
  have hNn : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  set H : ℕ → ℝ := fun m => η ^ 2 * ((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) +
    (if N < m + 2 then ((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) else 0) with hHdef
  have hHs : Summable H := (summable_z43.mul_left (η ^ 2)).add hGs
  have hHtsum : ∑' m, H m = η ^ 2 * Z + ∑' m : ℕ,
      (if N < m + 2 then ((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) else 0) := by
    rw [hHdef, (summable_z43.mul_left (η ^ 2)).tsum_add hGs, tsum_mul_left]
  have hH0 : ∀ m, 0 ≤ H m := fun m => by
    simp only [hHdef]; split_ifs <;> positivity
  have hterm : ∀ j : ℕ, (if j + 2 ∈ D then 0 else
      profPi (dispSite N e) (designWidthU N η) (-κ) (j + 2)) ≤ B0 * H j := by
    intro j
    split_ifs with h
    · exact mul_nonneg hB0.le (hH0 j)
    · exact hB N η hη0 hη1 (j + 2) (he _ h) (by omega)
  have hnonneg : ∀ j : ℕ, 0 ≤ (if j + 2 ∈ D then 0 else
      profPi (dispSite N e) (designWidthU N η) (-κ) (j + 2)) := by
    intro j
    split_ifs with h
    · exact le_rfl
    · exact le_trans (profPi0_nonneg _ _ (dispTailHyp_D D e he N hη0 hη1) (by omega))
        (profPi_ge_profPi0 (dispTailHyp_D D e he N hη0 hη1) hκ (by omega))
  have hsum : Summable (fun j : ℕ => if j + 2 ∈ D then 0 else
      profPi (dispSite N e) (designWidthU N η) (-κ) (j + 2)) :=
    Summable.of_nonneg_of_le hnonneg hterm (hHs.mul_left B0)
  refine ⟨hsum, ?_⟩
  calc ∑' j : ℕ, (if j + 2 ∈ D then 0 else
          profPi (dispSite N e) (designWidthU N η) (-κ) (j + 2))
      ≤ ∑' j, B0 * H j := hsum.tsum_le_tsum hterm (hHs.mul_left B0)
    _ = B0 * ∑' j, H j := tsum_mul_left
    _ = B0 * (η ^ 2 * Z + ∑' m : ℕ,
          (if N < m + 2 then ((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) else 0)) := by rw [hHtsum]
    _ ≤ B0 * (η ^ 2 * Z + 3 * (N : ℝ) ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) hB0.le
    _ ≤ B0 * (Z + 3) * (η ^ 2 + (N : ℝ) ^ (-(1 / 3 : ℝ))) := by
        have hη2 : η ^ 2 ≤ 1 := by nlinarith
        have h1 : η ^ 2 * Z ≤ Z * η ^ 2 := le_of_eq (mul_comm _ _)
        have h2 : 3 * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 3 * (η ^ 2 + (N : ℝ) ^ (-(1 / 3 : ℝ))) := by
          nlinarith [sq_nonneg η]
        nlinarith [mul_nonneg hZ0 (sq_nonneg η), mul_nonneg hZ0 hNn, mul_nonneg hB0.le hZ0,
          mul_nonneg hB0.le (sq_nonneg η), mul_nonneg hB0.le hNn]

/-- The sum `∑_{m ≥ 2, m ≠ s} Π_m(-κ)` is `O(η² + N^{-1/3})`. -/
lemma exists_dispRest_le (s : ℕ) (e κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ B > 0, ∀ (N : ℕ), 1 ≤ N → ∀ (η : ℝ), 0 ≤ η → η ≤ 1 / 4 →
      ∑' j : ℕ, (if j + 2 = s then 0 else
        profPi (dispSite N (dispE s e)) (designWidthU N η) (-κ) (j + 2)) ≤
        B * (η ^ 2 + (N : ℝ) ^ (-(1 / 3 : ℝ))) :=
  by
  obtain ⟨B, hB, h⟩ := exists_dispRest_le_D {s} (dispE s e) (fun k hk => dispE_of_ne e (by simpa using hk)) κ hκ
  exact ⟨B, hB, fun N hN η hη0 hη1 => by simpa only [Finset.mem_singleton] using (h N hN η hη0 hη1).2⟩

/-! ### The family -/

lemma exists_dispJ (n : ℕ) :
    ∃ J : ℕ, n + 1 ≤ J ∧ 1 ≤ J ∧ (1 ≤ n → ∀ N : ℕ, J ≤ N → ∀ (η e : ℝ), 0 < η → η ≤ 1 / 4 →
      e ^ 2 / (2 * |airyZero (n + 1) - airyZero 1|) ≤
        profPi0 (dispSite N (dispE (n + 1) e)) (designWidthU N η) (n + 1)) := by
  by_cases hn : 1 ≤ n
  · obtain ⟨J, hJ, h⟩ := exists_dispPi0_lower (s := n + 1) (by omega)
    exact ⟨J, hJ, by omega, fun _ => h⟩
  · exact ⟨n + 1, le_rfl, by omega, fun h => absurd h hn⟩

/-- The number of ideal sites `J_n`. -/
noncomputable def dispJ (n : ℕ) : ℕ := (exists_dispJ n).choose

lemma dispJ_spec (n : ℕ) :
    n + 1 ≤ dispJ n ∧ 1 ≤ dispJ n ∧ (1 ≤ n → ∀ N : ℕ, dispJ n ≤ N → ∀ (η e : ℝ), 0 < η → η ≤ 1 / 4 →
      e ^ 2 / (2 * |airyZero (n + 1) - airyZero 1|) ≤
        profPi0 (dispSite N (dispE (n + 1) e)) (designWidthU N η) (n + 1)) :=
  (exists_dispJ n).choose_spec

/-- The displacement `e = |a_1|/2` of `sr:Sigma` Step 5. -/
noncomputable def dispShift : ℝ := -airyZero 1 / 2

lemma dispShift_pos : 0 < dispShift := by
  unfold dispShift; have := airyZero_neg 1; linarith

/-- The shift `κ = d₀/2`, `d = -κ`. -/
noncomputable def dispKappa : ℝ := designRadius / 2

lemma dispKappa_pos : 0 < dispKappa := by unfold dispKappa; have := designRadius_pos; positivity

/-- The number of ideal sites of the `k`-th design. -/
noncomputable def dispN (n k : ℕ) : ℕ := dispJ n + k

lemma one_le_dispN (n k : ℕ) : 1 ≤ dispN n k :=
  ((dispJ_spec n).2.1).trans (Nat.le_add_right _ _)

lemma dispTail (n k : ℕ) :
    AiryProdTailHypothesis 1 (dispSite (dispN n k) (dispE (n + 1) dispShift))
      (designWidthU (dispN n k) (1 / ((k : ℝ) + 4))) :=
  dispTailHyp (n + 1) dispShift (dispN n k) (eta_pos k).le (eta_le k)

/-- The `k`-th window of the displaced family at the site `n`: see the module docstring. -/
noncomputable def dispWin (n k : ℕ) : Window :=
  profWin (dispSite (dispN n k) (dispE (n + 1) dispShift)) (designWidthU (dispN n k) (1 / ((k : ℝ) + 4)))
    (dispTail n k) (fun _ hk => designWidthU_ne_zero _ (eta_pos k) hk) (-dispKappa)

lemma dispWin_mem (n k : ℕ) (hn : 1 ≤ n) : dispWin n k ∈ displacedClass := by
  have hNJ : n + 1 ≤ dispN n k := (dispJ_spec n).1.trans (Nat.le_add_right _ _)
  refine profWin_mem_displacedClass (eta_pos k) (dispTail n k) (one_le_dispN n k) (eta_le k)
    (fun j hj => dispE_of_ne _ (by omega)) (fun j hj2 hjN => ?_) ?_
  · have hj : airyZero j ≤ airyZero 1 := by
      have := airyNode_le_airyNode_zero (j - 1)
      unfold airyNode at this
      rwa [show j - 1 + 1 = j by omega] at this
    by_cases hjs : j = n + 1
    · subst hjs
      rw [dispE_self]
      unfold dispShift
      have := airyZero_neg 1
      linarith
    · rw [dispE_of_ne _ hjs, add_zero]
      exact airyZero_neg j
  · have := designRadius_pos
    have hk := dispKappa_pos
    rw [abs_neg, abs_of_pos hk]
    unfold dispKappa; linarith

lemma dispWin_pi_nonneg (n k i : ℕ) : 0 ≤ (dispWin n k).pi i := by
  refine profWin_pi_nonneg_of_le _ _ _ _ _ ?_
  have := airyNode_le_airyNode_zero i
  have := dispKappa_pos
  linarith

lemma dispWin_pi_lower (n : ℕ) (hn : 1 ≤ n) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ k, ω ≤ (dispWin n k).pi n := by
  refine ⟨dispShift ^ 2 / (2 * |airyZero (n + 1) - airyZero 1|), ?_, fun k => ?_⟩
  · have := abs_airyZero_sub_one_pos (n := n + 1) (by omega)
    have := dispShift_pos
    positivity
  · obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
    have hlow := (dispJ_spec (i + 1)).2.2 hn (dispN (i + 1) k) (Nat.le_add_right _ _)
      (1 / ((k : ℝ) + 4)) dispShift (eta_pos k) (eta_le k)
    have hge := profPi_ge_profPi0 (dispTail (i + 1) k) dispKappa_pos.le (n := i + 2) (by omega)
    unfold dispWin
    rw [profWin_pi_succ]
    exact hlow.trans (hge.trans' le_rfl)

lemma dispWin_rest (n : ℕ) :
    Tendsto (fun k => ∑' i, if i = 0 ∨ i = n then 0 else (dispWin n k).pi i) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := exists_dispRest_le (n + 1) dispShift dispKappa dispKappa_pos.le
  have hη : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 4)) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => ((k : ℝ) + 4)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact this.inv_tendsto_atTop.congr (fun k => by simp [one_div])
  have hN : Tendsto (fun k : ℕ => ((dispN n k : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun k : ℕ => dispN n k) atTop atTop :=
      tendsto_atTop_mono (fun k => Nat.le_add_left k (dispJ n)) tendsto_id
    have h1 : Tendsto (fun k : ℕ => ((dispN n k : ℕ) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp h0
    exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp h1
  have hb : Tendsto (fun k : ℕ => B * ((1 / ((k : ℝ) + 4)) ^ 2 +
      ((dispN n k : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)))) atTop (𝓝 0) := by
    have h4 := (((hη.pow 2).add hN).const_mul B)
    have h0 : B * ((0 : ℝ) ^ 2 + 0) = 0 := by ring
    rw [h0] at h4
    exact h4
  have heq : ∀ k, (∑' i, if i = 0 ∨ i = n then (0 : ℝ) else (dispWin n k).pi i) =
      ∑' j : ℕ, (if j + 2 = n + 1 then 0 else
        profPi (dispSite (dispN n k) (dispE (n + 1) dispShift))
          (designWidthU (dispN n k) (1 / ((k : ℝ) + 4))) (-dispKappa) (j + 2)) := by
    intro k
    set f : ℕ → ℝ := fun i => if i = 0 ∨ i = n then 0 else (dispWin n k).pi i with hf
    have hf0 : ∀ i, 0 ≤ f i := fun i => by
      simp only [hf]; split_ifs
      · exact le_rfl
      · exact dispWin_pi_nonneg n k i
    have hfs : Summable f :=
      Summable.of_nonneg_of_le hf0 (fun i => by
        simp only [hf]; split_ifs
        · exact dispWin_pi_nonneg n k i
        · exact le_rfl) (dispWin n k).summable_pi
    rw [hfs.tsum_eq_zero_add]
    have : f 0 = 0 := by simp [hf]
    rw [this, zero_add]
    refine tsum_congr fun j => ?_
    simp only [hf]
    by_cases hj : j + 1 = n
    · have h1 : (j + 1 = 0 ∨ j + 1 = n) := Or.inr hj
      have h2 : j + 2 = n + 1 := by omega
      simp only [h1, h2, ↓reduceIte]
    · have h1 : ¬ (j + 1 = 0 ∨ j + 1 = n) := by omega
      have h2 : ¬ j + 2 = n + 1 := by omega
      simp only [h1, h2, ↓reduceIte]
      unfold dispWin
      rw [profWin_pi_succ]
  refine squeeze_zero (fun k => ?_) (fun k => ?_) hb
  · rw [heq k]
    refine tsum_nonneg fun j => ?_
    split_ifs with h
    · exact le_rfl
    · exact le_trans (profPi0_nonneg _ _ (dispTail n k) (by omega))
        (profPi_ge_profPi0 (dispTail n k) dispKappa_pos.le (by omega))
  · rw [heq k]
    exact hbound (dispN n k) (one_le_dispN n k) _ (eta_pos k).le (eta_le k)

/-- **`DisplacedFamily displacedClass`** (`sr:Sigma` Step 5): for each site `n ≥ 1` (the zero `a_{n+1}`)
windows with all `Π_m ≥ 0`, `Π_n ≥ ω > 0` and `∑_{m ≠ 1, n+1} Π_m → 0`. -/
noncomputable def displacedFamily : DisplacedFamily displacedClass where
  win := dispWin
  mem := fun n k hn => dispWin_mem n k hn
  pi_nonneg := fun n k i _ => dispWin_pi_nonneg n k i
  pi_lower := fun n hn => dispWin_pi_lower n hn
  rest_small := fun n _ => dispWin_rest n

/-- **`DisplacedFamily (designClass ∪ displacedClass)`**: the input `Dis` of `virasoro_sigma` with
`𝒟x = displacedClass`. -/
noncomputable def displacedFamily_union : DisplacedFamily (designClass ∪ displacedClass) :=
  DisplacedFamily.mono Set.subset_union_right displacedFamily

/-- The window family is nonempty for every class containing `displacedClass`. -/
theorem displacedFamily_exists {𝒟 : Set Window} (h : displacedClass ⊆ 𝒟) :
    Nonempty (DisplacedFamily 𝒟) :=
  ⟨DisplacedFamily.mono h displacedFamily⟩

/-- **`Σ` for a weight-one problem, for the extremal measures, with the same-site and displaced families
proved** (given the threshold lower bound `hLo`): the remaining inputs are Property `sr:P` for the class
`𝒟x ⊇ displacedClass` and the omitted family. -/
theorem sigma_of_omitted_prob (prob : FixedWeightProblem) (hw : prob.w = 1)
    (hLo : FormalResearch.ModularBootstrap.FixedWeight.FixedWeightLowerBoundInput prob) {𝒟x : Set Window} (hsub : displacedClass ⊆ 𝒟x)
    (hPx : ∀ S : CrossingSequence prob, DesignPropertyP S.μS 𝒟x)
    (Om : OmittedFamily (designClass ∪ 𝒟x)) :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence prob, S.c = cSeq ∧
        (∀ j, S.τ j = prob.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        SigmaConclusion S.μS :=
  sigma_prob prob hw hLo hPx sameSiteFamily_designClass_exists.some
    (DisplacedFamily.mono (hsub.trans Set.subset_union_right) displacedFamily) Om

/-- **`Σ` at Virasoro for the extremal measures with the same-site and displaced families proved**: the
remaining inputs are Property `sr:P` for the class `𝒟x ⊇ displacedClass` (`Σ3`) and the omitted family
(`Σ4`). -/
theorem virasoro_sigma_of_omitted {𝒟x : Set Window} (hsub : displacedClass ⊆ 𝒟x)
    (hPx : ∀ S : CrossingSequence virasoroProblem, DesignPropertyP S.μS 𝒟x)
    (Om : OmittedFamily (designClass ∪ 𝒟x)) :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence virasoroProblem, S.c = cSeq ∧
        (∀ j, S.τ j = virasoroProblem.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        SigmaConclusion S.μS :=
  sigma_of_omitted_prob virasoroProblem rfl FormalResearch.ModularBootstrap.FixedWeight.virasoro_lowerBoundInput hsub hPx Om

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.exists_dispPi0_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_dispPi0_lower

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.exists_dispRest_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_dispRest_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.displacedFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms displacedFamily

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.virasoro_sigma_of_omitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_sigma_of_omitted

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.displacedFamily_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms displacedFamily_union

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.sigma_of_omitted_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sigma_of_omitted_prob

end FormalResearch.ModularBootstrap.Upper.Assembly
