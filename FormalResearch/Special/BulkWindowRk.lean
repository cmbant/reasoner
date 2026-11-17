module

public import FormalResearch.Special.BulkWindowChart
public import FormalResearch.Special.BulkWindowCount

/-!
# Bulk window, part 5: the node count of the Airy window (generic form)

`BwnSetup` collects the data of an Airy window `RkWinAt 1 0 1 x q_* Y ...` of the Hahn data `(P, Q, τ, s) = (1, 0, 1, 1)` and the numerical
smallness conditions under which `bwn_window_count`-type statements hold; **`BwnSetup.count`** is the conclusion:

at a window site `K + i` with `q ∈ [q_* - ρ, q_*)`, `Φ(q)/δ³ ≥ 16/3` and `|cos(Φ(q)/δ³ - π/4)| > 1/10`, the sequence `u_j = Y_{K+j}` has exactly
`⌊Φ(q_{K+i})/(π δ³) + 1/4⌋` nodes (sign changes `u_j u_{j+1} < 0` plus interior zeros, `bix_c`) in the bonds `i, …, m_w - K - 1`, where
`m_w` is the turning site of the window.

Proof (`BwnSetup.hu_site`, `hz_bond`, `hnd_site`, `end_site`, `start_site`, then `BwnWin.count` of `BulkWindowCount`): the window gives
`Y_k = κ g_k Ai(X_k) + μ g_k Bi(X_k) + O(δ³ ...)` with `μ/κ ≤ δ³`; so `u` is a noisy positive multiple of the sampling `f_j = Ai(X_{K+j})` with
tolerance `E = (1350 + 4C/g_min) δ³` (`bwn_err`); the zeros of `Ai` between consecutive sites number at most one (`bwn_count_step`: the lattice step
`X_{k+1} - X_k ≤ c₂ δ` is below the zero spacing `π/√v` because `c₂ δ √v ≤ 1/4`, `bwn_vbounds`); a site with `|f| ≤ E` is isolated, with
definite neighbours of opposite sign (`bwn_nz`: the lattice step `≥ c₁ δ` exceeds the distance `~ E/|Ai'|` to the zero); the identification
`(2/3)(-X)^{3/2} = Φ/δ³` (`bwn_chart_X`) turns the zero count `⌊(2/3) v^{3/2}/π + 1/4⌋` (`bwn_count_floor`) into the Bohr-Sommerfeld count.

**Claim class: proved.**  **Not formalised:** that the hypotheses of `BwnSetup` hold for the `3j` chain at small `δ` (`BulkWindowHahn`).
-/

@[expose] public section

open Finset Set FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special


/-- The tolerance `E = (1350 + 4C/g_min) δ³` of the window sampling. -/
noncomputable def bwnE (C gmin δ : ℝ) : ℝ := (1350 + 4 * C / gmin) * δ ^ 3

lemma bwnE_nonneg {C gmin δ : ℝ} (hC : 0 < C) (hg : 0 < gmin) (hδ : 0 < δ) : 0 ≤ bwnE C gmin δ := by
  unfold bwnE; positivity

/-- **Error of the Airy window against the sampling of `Ai`** (the `μ Bi` part and the `O(δ³)` part), in units of `|κ| g`. -/
lemma bwn_err {Y κ μ g Ai Bi Wa Wb C gmin δ : ℝ} (hg : gmin ≤ g) (hgmin : 0 < gmin) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hμ : |μ| ≤ δ ^ 3 * |κ|) (hBi : |Bi| ≤ 1350) (hWa : Wa ≤ 1) (hWb : Wb ≤ 3)
    (hY : |Y - (κ * (g * Ai) + μ * (g * Bi))| ≤ C * δ ^ 3 * (|κ| * Wa + |μ| * Wb)) (hWb0 : 0 ≤ Wb) (hC : 0 < C) :
    |Y - κ * (g * Ai)| ≤ bwnE C gmin δ * (|κ| * g) := by
  have hg0 : 0 < g := lt_of_lt_of_le hgmin hg
  have hδ3 : 0 ≤ δ ^ 3 := by positivity
  have hδ31 : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have h1 : |Y - κ * (g * Ai)| ≤ |Y - (κ * (g * Ai) + μ * (g * Bi))| + |μ * (g * Bi)| := by
    have := abs_add_le (Y - (κ * (g * Ai) + μ * (g * Bi))) (μ * (g * Bi))
    convert this using 2; ring
  have h2 : |μ * (g * Bi)| ≤ 1350 * δ ^ 3 * (|κ| * g) := by
    rw [abs_mul, abs_mul, abs_of_pos hg0]
    have : |μ| * (g * |Bi|) ≤ (δ ^ 3 * |κ|) * (g * 1350) :=
      mul_le_mul hμ (mul_le_mul_of_nonneg_left hBi hg0.le) (by positivity) (by positivity)
    nlinarith
  have h3 : C * δ ^ 3 * (|κ| * Wa + |μ| * Wb) ≤ 4 * C / gmin * δ ^ 3 * (|κ| * g) := by
    have hk0 : 0 ≤ |κ| := abs_nonneg _
    have a1 : |κ| * Wa + |μ| * Wb ≤ |κ| * 1 + (δ ^ 3 * |κ|) * 3 :=
      add_le_add (mul_le_mul_of_nonneg_left hWa hk0) (mul_le_mul hμ hWb hWb0 (by positivity))
    have a2 : |κ| * 1 + (δ ^ 3 * |κ|) * 3 ≤ 4 * |κ| := by nlinarith
    have a3 : 4 * |κ| ≤ 4 / gmin * (|κ| * g) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hgmin]; nlinarith [mul_le_mul_of_nonneg_left hg hk0]
    calc C * δ ^ 3 * (|κ| * Wa + |μ| * Wb) ≤ C * δ ^ 3 * (4 / gmin * (|κ| * g)) :=
          mul_le_mul_of_nonneg_left (a1.trans (a2.trans a3)) (by positivity)
      _ = 4 * C / gmin * δ ^ 3 * (|κ| * g) := by ring
  unfold bwnE
  nlinarith [hY, h1, h2, h3]

/-- The lattice variable `X_k = h^{-2/3} ζ(q_k)` of the Hahn window. -/
noncomputable def bwnX (x δ : ℝ) : ℤ → ℝ := turnX (hrU 1 0 1 x) (√(1 - x ^ 2)) (δ ^ 3 / 2) δ

/-- The Langer amplitude along the lattice. -/
noncomputable def bwnG (x δ : ℝ) : ℤ → ℝ :=
  fun k => langerAmp (hrU 1 0 1 x) (hrA1 1 0) (√(1 - x ^ 2)) (dalQ (δ ^ 3 / 2) δ k)

/-- The lattice site `q_k = (k + 1/2) δ³`. -/
noncomputable def bwnQ (δ : ℝ) (k : ℤ) : ℝ := ((k : ℝ) + 1 / 2) * δ ^ 3

lemma bwnQ_mono {δ : ℝ} (hδ : 0 < δ) {k k' : ℤ} (h : k ≤ k') : bwnQ δ k ≤ bwnQ δ k' := by
  unfold bwnQ
  have : (k : ℝ) ≤ k' := by exact_mod_cast h
  have : 0 < δ ^ 3 := by positivity
  nlinarith

lemma bwnQ_succ (δ : ℝ) (k : ℤ) : bwnQ δ (k + 1) = bwnQ δ k + δ ^ 3 := by
  unfold bwnQ; push_cast; ring

lemma bwn_dalQ (δ : ℝ) (k : ℤ) : dalQ (δ ^ 3 / 2) δ k = bwnQ δ k := by unfold dalQ bwnQ; ring

/-- The hypotheses of `bwn_window_count`, collected (see there). -/
structure BwnSetup (x : ℝ) (Y : ℤ → ℝ) (r C gmin c1 c2 δ κ μ ρ ρ0 cpos : ℝ) (J mw N' K : ℤ) (i : ℕ) : Prop where
  hx0 : 0 < x
  hx1 : x < 1
  hgmin : 0 < gmin
  hC : 0 < C
  hc1 : 0 < c1
  hc12 : c1 ≤ c2
  hδ : 0 < δ
  hδ1 : δ ≤ 1
  hκ : 1 ≤ κ ^ 2 * δ
  hμ : |μ| ≤ δ ^ 3 * |κ|
  hρ : 0 < ρ
  hρr : ρ ≤ r
  hρ0 : ρ < ρ0
  hρ4 : ρ ≤ 1 / 4
  hρc : 200 * c2 ^ 3 * ρ ≤ 1
  hchart : ∀ q : ℝ, √(1 - x ^ 2) - ρ0 < q → q < √(1 - x ^ 2) →
      langerZeta (hrU 1 0 1 x) (√(1 - x ^ 2)) q < 0 ∧
      2 / 3 * (-langerZeta (hrU 1 0 1 x) (√(1 - x ^ 2)) q) ^ (3 / 2 : ℝ) = bkPhase 1 0 1 x (√(1 - x ^ 2)) q
  hcpos : ∀ X ∈ Set.Icc (-1 : ℝ) (1 / 4), cpos ≤ airyAi X
  hE1 : bwnE C gmin δ < cpos
  hE2 : 8 * bwnE C gmin δ ≤ bwn_c0 * (c1 * δ)
  hE3 : bwnE C gmin δ ^ 2 / δ ^ 2 ≤ bwn_c0 ^ 2 / 2
  hE4 : bwnE C gmin δ < δ / 25
  hJ1 : 1 ≤ J
  hJm : J ≤ mw
  hmN : mw ≤ N'
  hqJ : bwnQ δ J < √(1 - x ^ 2) - r + δ ^ 3
  hqm1 : √(1 - x ^ 2) ≤ bwnQ δ mw
  hqm2 : bwnQ δ mw < √(1 - x ^ 2) + δ ^ 3
  hXle : ∀ k ∈ Finset.Icc J (mw + 1), bwnX x δ k ≤ 1 / 4
  hgm : ∀ k ∈ Finset.Icc J (N' + 1), gmin ≤ bwnG x δ k
  hstep : ∀ k ∈ Finset.Icc J N', c1 * δ ≤ bwnX x δ (k + 1) - bwnX x δ k ∧ bwnX x δ (k + 1) - bwnX x δ k ≤ c2 * δ
  hXm : 0 ≤ bwnX x δ mw ∧ bwnX x δ mw ≤ c2 * δ
  hYk : ∀ k ∈ Finset.Icc J (N' + 1),
    |Y k - (κ * (bwnG x δ k * airyAi (bwnX x δ k)) + μ * (bwnG x δ k * airyBi (bwnX x δ k)))| ≤
      C * δ ^ 3 * (|κ| * airyWt (bwnX x δ k) + |μ| * airyBiWt (bwnX x δ k))
  hq0 : √(1 - x ^ 2) - ρ ≤ bwnQ δ (K + i)
  hq1 : bwnQ δ (K + i) < √(1 - x ^ 2)
  hbig : 16 / 3 ≤ bkPhase 1 0 1 x (√(1 - x ^ 2)) (bwnQ δ (K + i)) / δ ^ 3
  hcos : 1 / 10 < |Real.cos (bkPhase 1 0 1 x (√(1 - x ^ 2)) (bwnQ δ (K + i)) / δ ^ 3 - π / 4)|

namespace BwnSetup

variable {x r C gmin c1 c2 δ κ μ ρ ρ0 cpos : ℝ} {Y : ℤ → ℝ} {J mw N' K : ℤ} {i : ℕ}

lemma hδ3 (P : BwnSetup x Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) : 0 < δ ^ 3 := by
  have := P.hδ; positivity

lemma hqs (P : BwnSetup x Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) : 0 < √(1 - x ^ 2) := by
  have := P.hx0; have := P.hx1
  exact Real.sqrt_pos.2 (by nlinarith)

/-- The site `K + i` precedes the turning site. -/
lemma hlt (P : BwnSetup x Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) : K + (i : ℤ) < mw := by
  by_contra hc
  push Not at hc
  have h1 := bwnQ_mono P.hδ hc
  have h2 := P.hq1
  have h3 := P.hqm1
  linarith

/-- The site `K + i` lies in the window. -/
lemma hJle (P : BwnSetup x Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) : J ≤ K + (i : ℤ) := by
  by_contra hc
  push Not at hc
  have h1 : K + (i : ℤ) ≤ J - 1 := by omega
  have h2 := bwnQ_mono P.hδ h1
  have h4 : bwnQ δ (J - 1 + 1) = bwnQ δ J := by congr 1; ring
  have h5 := bwnQ_succ δ (J - 1)
  rw [h4] at h5
  have h6 := P.hqJ
  have h7 := P.hq0
  have h8 := P.hρr
  linarith


/-- Inner sites (before the turning site): the chart is valid, `X < 0`, `(2/3)(-X)^{3/2} = Φ(q)/δ³`, and `δ √(-X)` is small. -/
lemma inner (P : BwnSetup x Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) {k : ℤ} (h1 : K + (i : ℤ) ≤ k) (h2 : k < mw) :
    bwnX x δ k < 0 ∧
      2 / 3 * (-bwnX x δ k) ^ (3 / 2 : ℝ) = bkPhase 1 0 1 x (√(1 - x ^ 2)) (bwnQ δ k) / δ ^ 3 ∧
      c2 * δ * √(-bwnX x δ k) ≤ 1 / 4 ∧ (-bwnX x δ k) * δ ^ 2 ≤ 1 := by
  have hδ3 := P.hδ3
  have hqlo : √(1 - x ^ 2) - ρ ≤ bwnQ δ k := P.hq0.trans (bwnQ_mono P.hδ h1)
  have hqhi : bwnQ δ k < √(1 - x ^ 2) := by
    have h3 : k + 1 ≤ mw := h2
    have h4 := bwnQ_mono P.hδ h3
    rw [bwnQ_succ] at h4
    have := P.hqm2
    linarith
  have hJ := P.hJle
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by have := P.hJ1; omega : (1 : ℤ) ≤ k)
  have hq0' : 0 ≤ bwnQ δ k := by unfold bwnQ; positivity
  obtain ⟨hneg, hI⟩ := P.hchart _ (by linarith [P.hρ0]) hqhi
  obtain ⟨hpos, hI2⟩ := bwn_chart_X (neg_pos.2 hneg) hδ3 hI
  have hv : -bwnX x δ k = (δ ^ 3) ^ (-(2 / 3) : ℝ) * (-langerZeta (hrU 1 0 1 x) (√(1 - x ^ 2)) (bwnQ δ k)) := by
    unfold bwnX turnX dalX
    rw [bwn_dalQ]; ring
  have hvpos : 0 < -bwnX x δ k := by rw [hv]; exact hpos
  have hξ : 2 / 3 * (-bwnX x δ k) ^ (3 / 2 : ℝ) = bkPhase 1 0 1 x (√(1 - x ^ 2)) (bwnQ δ k) / δ ^ 3 := by
    rw [hv]; exact hI2
  refine ⟨by linarith, hξ, ?_⟩
  have hph := (bwn_phase_bounds P.hx0 P.hx1 hq0' hqhi.le).2
  have hξ' : 2 / 3 * (-bwnX x δ k) ^ (3 / 2 : ℝ) ≤ π / 2 * ρ / δ ^ 3 := by
    rw [hξ]
    apply div_le_div_of_nonneg_right _ hδ3.le
    refine hph.trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact bwn_vbounds hvpos P.hδ (by linarith [P.hc1, P.hc12]) P.hρ4 P.hρ.le P.hρc hξ'


/-- The zero count of `Ai` at consecutive lattice points: antitone, dropping by at most one. -/
lemma hz_bond (P : BwnSetup x Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) {k : ℤ} (h1 : K + (i : ℤ) ≤ k) (h2 : k + 1 ≤ mw) :
    airyZeroCount (bwnX x δ (k + 1)) ≤ airyZeroCount (bwnX x δ k) ∧
      airyZeroCount (bwnX x δ k) ≤ airyZeroCount (bwnX x δ (k + 1)) + 1 := by
  have hJ := P.hJle
  have hmN := P.hmN
  have hst := P.hstep k (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hd0 : 0 < c1 * δ := mul_pos P.hc1 P.hδ
  have hle : bwnX x δ k ≤ bwnX x δ (k + 1) := by linarith [hst.1]
  refine ⟨bwn_count_anti hle, ?_⟩
  by_cases hX : -1 ≤ bwnX x δ k
  · rw [bwn_count_zero hX]; exact Nat.zero_le _
  · push Not at hX
    obtain ⟨hneg, -, hc2, -⟩ := P.inner h1 (by omega : k < mw)
    set v := -bwnX x δ k with hv
    have hv1 : 1 < v := by rw [hv]; linarith
    have hsq : 1 ≤ √v := by rw [Real.one_le_sqrt]; exact hv1.le
    have hc2δ : c2 * δ ≤ 1 / 4 := by
      have : c2 * δ * 1 ≤ c2 * δ * √v := mul_le_mul_of_nonneg_left hsq (mul_pos (lt_of_lt_of_le P.hc1 P.hc12) P.hδ).le
      linarith
    have hx' : bwnX x δ (k + 1) ≤ 0 := by linarith [hst.2]
    have hcount := bwn_count_step (x := bwnX x δ k) (x' := bwnX x δ (k + 1)) (Y := v) (by linarith) (by rw [hv]; linarith)
      hle hx' (by
        have : (bwnX x δ (k + 1) - bwnX x δ k) * √v ≤ c2 * δ * √v :=
          mul_le_mul_of_nonneg_right hst.2 (Real.sqrt_nonneg _)
        linarith [Real.pi_gt_three])
    exact hcount

/-- The error of the sampling, in units of `|κ| g`. -/
lemma hu_site (P : BwnSetup x Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) {k : ℤ} (h1 : K + (i : ℤ) ≤ k) (h2 : k ≤ mw) :
    |Y k - κ * (bwnG x δ k * airyAi (bwnX x δ k))| ≤ bwnE C gmin δ * (|κ| * bwnG x δ k) := by
  have hJ := P.hJle
  have hmN := P.hmN
  have hk : k ∈ Finset.Icc J (N' + 1) := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hX1 := P.hXle k (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  obtain ⟨hW1, hW2, hB⟩ := bwn_wt_le hX1
  exact bwn_err (P.hgm k hk) P.hgmin P.hδ P.hδ1 P.hμ hB hW1 hW2 (P.hYk k hk) (airyBiWt_pos _).le P.hC

/-- At the turning site `Ai(X_{m_w}) > E`. -/
lemma end_site (P : BwnSetup x Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) :
    bwnE C gmin δ < |airyAi (bwnX x δ mw)| := by
  have h1 := P.hXle mw (Finset.mem_Icc.2 ⟨P.hJm, by omega⟩)
  have h2 := P.hcpos (bwnX x δ mw) ⟨by linarith [P.hXm.1], h1⟩
  have := P.hE1
  rw [abs_of_pos (by linarith [P.hE1, bwnE_nonneg P.hC P.hgmin P.hδ])]
  linarith

/-- The start site has `v ≥ 4`, and the count of zeros is the floor. -/
lemma start_site (P : BwnSetup x Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) :
    bwnE C gmin δ < |airyAi (bwnX x δ (K + i))| ∧
      (airyZeroCount (bwnX x δ (K + i)) : ℤ) =
        ⌊bkPhase 1 0 1 x (√(1 - x ^ 2)) (bwnQ δ (K + i)) / (π * δ ^ 3) + 1 / 4⌋ := by
  obtain ⟨hneg, hξ, -, hvδ⟩ := P.inner (le_refl _) P.hlt
  set v := -bwnX x δ (K + i) with hv
  have hvpos : 0 < v := by rw [hv]; linarith
  have hv4 : 4 ≤ v := by
    by_contra hc
    push Not at hc
    have h1 : v ^ (3 / 2 : ℝ) < (4 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_lt_rpow hvpos.le hc (by norm_num)
    have e : (4 : ℝ) ^ (3 / 2 : ℝ) = 8 := by
      rw [← sqrt_cube_eq_rpow (by norm_num : (0 : ℝ) < 4)]
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num
    have := P.hbig
    rw [← hξ] at this
    linarith
  have hcos' : 1 / 10 < |Real.cos (2 / 3 * v ^ (3 / 2 : ℝ) - π / 4)| := by
    rw [hξ]; exact P.hcos
  refine ⟨?_, ?_⟩
  · have := bwn_Ai_lower hv4 hvδ P.hδ P.hδ1 hcos'
    have e : bwnX x δ (K + i) = -v := by rw [hv]; ring
    rw [e]
    linarith [P.hE4]
  · have := bwn_count_floor hvpos hcos'
    have e : bwnX x δ (K + i) = -v := by rw [hv]; ring
    rw [e, this, hξ]
    congr 1
    field_simp


/-- **Isolation of a near-zero site**: an interior site with `|Ai(X_k)| ≤ E` has definite neighbours of opposite signs. -/
lemma hnd_site (P : BwnSetup x Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) {k : ℤ} (h1 : K + (i : ℤ) < k) (h2 : k < mw)
    (hs : |airyAi (bwnX x δ k)| ≤ bwnE C gmin δ) :
    bwnE C gmin δ < |airyAi (bwnX x δ (k - 1))| ∧ bwnE C gmin δ < |airyAi (bwnX x δ (k + 1))| ∧
      airyAi (bwnX x δ (k - 1)) * airyAi (bwnX x δ (k + 1)) < 0 := by
  have hJ := P.hJle
  have hmN := P.hmN
  have hE0 := bwnE_nonneg P.hC P.hgmin P.hδ
  have hc0 := bwn_c0_pos
  have hX1 := P.hXle k (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hXlt : bwnX x δ k < -1 := by
    by_contra hc
    push Not at hc
    have := P.hcpos (bwnX x δ k) ⟨hc, hX1⟩
    have h3 := P.hE1
    have h4 := le_abs_self (airyAi (bwnX x δ k))
    linarith
  obtain ⟨hneg, -, hc2, hvδ⟩ := P.inner h1.le h2
  set v := -bwnX x δ k with hv
  have hvpos : 0 < v := by rw [hv]; linarith
  have hst := P.hstep k (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hst' := P.hstep (k - 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have e1 : k - 1 + 1 = k := by ring
  rw [e1] at hst'
  have hd0 : 0 < c1 * δ := mul_pos P.hc1 P.hδ
  have hδ2 : 0 < δ ^ 2 := by have := P.hδ; positivity
  -- the hypotheses of the linearisation lemma
  have hεc : -bwnX x δ k * bwnE C gmin δ ^ 2 ≤ bwn_c0 ^ 2 / 2 := by
    have h3 : v * bwnE C gmin δ ^ 2 ≤ bwnE C gmin δ ^ 2 / δ ^ 2 := by
      rw [le_div_iff₀ hδ2]
      have := mul_le_mul_of_nonneg_right hvδ (sq_nonneg (bwnE C gmin δ))
      nlinarith
    have := P.hE3
    rw [← hv]; linarith
  have hdw : (bwnX x δ (k + 1) - bwnX x δ k) * √(-bwnX x δ k) ≤ 1 / 4 := by
    have : (bwnX x δ (k + 1) - bwnX x δ k) * √v ≤ c2 * δ * √v :=
      mul_le_mul_of_nonneg_right hst.2 (Real.sqrt_nonneg _)
    linarith
  have hdw' : (bwnX x δ k - bwnX x δ (k - 1)) * √(-bwnX x δ k) ≤ 1 / 4 := by
    have : (bwnX x δ k - bwnX x δ (k - 1)) * √v ≤ c2 * δ * √v :=
      mul_le_mul_of_nonneg_right hst'.2 (Real.sqrt_nonneg _)
    linarith
  have hdε : 8 * bwnE C gmin δ ≤ bwn_c0 * (bwnX x δ (k + 1) - bwnX x δ k) := by
    have := mul_le_mul_of_nonneg_left hst.1 hc0.le
    linarith [P.hE2]
  have hdε' : 8 * bwnE C gmin δ ≤ bwn_c0 * (bwnX x δ k - bwnX x δ (k - 1)) := by
    have := mul_le_mul_of_nonneg_left hst'.1 hc0.le
    linarith [P.hE2]
  obtain ⟨s, hs1, h3, h4⟩ := bwn_nz (x := bwnX x δ k) (ε := bwnE C gmin δ) (by linarith) hs hεc
    (by linarith [hst.1]) (by linarith [hst'.1]) hdw hdw' hdε hdε'
  have e2 : bwnX x δ k + (bwnX x δ (k + 1) - bwnX x δ k) = bwnX x δ (k + 1) := by ring
  have e3 : bwnX x δ k - (bwnX x δ k - bwnX x δ (k - 1)) = bwnX x δ (k - 1) := by ring
  rw [e2] at h3
  rw [e3] at h4
  have hss : s * s = 1 := by rcases hs1 with h | h <;> rw [h] <;> norm_num
  have habs : ∀ t a : ℝ, (t = 1 ∨ t = -1) → |t * a| = |a| := by
    intro t a ht
    rw [abs_mul]
    have : |t| = 1 := by rcases ht with h | h <;> rw [h] <;> norm_num
    rw [this, one_mul]
  have hns : -s = 1 ∨ -s = -1 := by rcases hs1 with h | h <;> rw [h] <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [← habs (-s) _ hns]; exact lt_of_lt_of_le h4 (le_abs_self _)
  · rw [← habs s _ hs1]; exact lt_of_lt_of_le h3 (le_abs_self _)
  · have := mul_pos (lt_of_le_of_lt hE0 h3) (lt_of_le_of_lt hE0 h4)
    nlinarith


/-- **The node count of the Airy window** (generic form): at the site `K + i` the sequence `u_j = Y_{K+j}` has exactly
`⌊Φ(q_{K+i})/(π δ³) + 1/4⌋` nodes in the bonds from `i` up to the turning site `m_w - K`. -/
theorem count (P : BwnSetup x Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) :
    K + (i : ℤ) < mw ∧
      ((∑ j ∈ Finset.Ico i (mw - K).toNat, bix_c (fun j : ℕ => Y (K + j)) j : ℕ) : ℤ) =
        ⌊bkPhase 1 0 1 x (√(1 - x ^ 2)) (bwnQ δ (K + i)) / (π * δ ^ 3) + 1 / 4⌋ := by
  have hlt := P.hlt
  refine ⟨hlt, ?_⟩
  have hJ := P.hJle
  have hmN := P.hmN
  have hE0 := bwnE_nonneg P.hC P.hgmin P.hδ
  have hκ0 : κ ≠ 0 := by
    intro h; have := P.hκ; rw [h] at this; norm_num at this
  set k₁ : ℕ := (mw - K).toNat with hk₁
  have hk₁' : (k₁ : ℤ) = mw - K := by rw [hk₁]; omega
  have hik : i ≤ k₁ := by omega
  have hmem : ∀ j : ℕ, i ≤ j → j ≤ k₁ → K + (i : ℤ) ≤ K + (j : ℤ) ∧ K + (j : ℤ) ≤ mw := by
    intro j h1 h2; constructor <;> omega
  set s : ℝ := if 0 < κ then 1 else -1 with hs
  have hs1 : s = 1 ∨ s = -1 := by rw [hs]; split_ifs <;> simp
  have hsκ : s * |κ| = κ := by
    rw [hs]; split_ifs with h
    · rw [abs_of_pos h]; ring
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hκ0)]; ring
  have W : BwnWin (fun j : ℕ => Y (K + j)) (fun j : ℕ => airyAi (bwnX x δ (K + j)))
      (fun j : ℕ => |κ| * bwnG x δ (K + j)) (fun j : ℕ => airyZeroCount (bwnX x δ (K + j))) s (bwnE C gmin δ) i k₁ := by
    refine ⟨hs1, hE0, ?_, ?_, ?_, ?_, ?_⟩
    · intro j h1 h2
      obtain ⟨a1, a2⟩ := hmem j h1 h2
      have hg := P.hgm (K + j) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      exact mul_pos (abs_pos.2 hκ0) (lt_of_lt_of_le P.hgmin hg)
    · intro j h1 h2
      obtain ⟨a1, a2⟩ := hmem j h1 h2
      have := P.hu_site a1 a2
      have e : s * (|κ| * bwnG x δ (K + j)) * airyAi (bwnX x δ (K + j)) = κ * (bwnG x δ (K + j) * airyAi (bwnX x δ (K + j))) := by
        rw [show κ * (bwnG x δ (K + j) * airyAi (bwnX x δ (K + j))) =
          (s * |κ|) * (bwnG x δ (K + j) * airyAi (bwnX x δ (K + j))) by rw [hsκ]]; ring
      rw [e]; exact this
    · intro j h1 h2 hne
      exact bwn_sign_all _ hne
    · intro j h1 h2
      obtain ⟨a1, a2⟩ := hmem j h1 h2.le
      have e : K + ((j + 1 : ℕ) : ℤ) = K + (j : ℤ) + 1 := by push_cast; ring
      have := P.hz_bond a1 (by omega : K + (j : ℤ) + 1 ≤ mw)
      simp only [e]
      exact this
    · intro j h1 h2 hs'
      have a1 : K + (i : ℤ) < K + (j : ℤ) := by omega
      have a2 : K + (j : ℤ) < mw := by omega
      obtain ⟨b1, b2, b3⟩ := P.hnd_site a1 a2 hs'
      have e1 : K + ((j - 1 : ℕ) : ℤ) = K + (j : ℤ) - 1 := by omega
      have e2 : K + ((j + 1 : ℕ) : ℤ) = K + (j : ℤ) + 1 := by push_cast; ring
      simp only [e1, e2]
      exact ⟨b1, b2, b3⟩
  have hstart := P.start_site
  have hdef0 : bwnE C gmin δ < |airyAi (bwnX x δ (K + (i : ℤ)))| := hstart.1
  have hdef1 : bwnE C gmin δ < |airyAi (bwnX x δ (K + (k₁ : ℤ)))| := by
    have : K + (k₁ : ℤ) = mw := by omega
    rw [this]; exact P.end_site
  have hmain := BwnWin.count W (k₁ - i) i le_rfl (by omega) hdef0 (by
    have : i + (k₁ - i) = k₁ := by omega
    rw [this]; exact hdef1)
  have e : i + (k₁ - i) = k₁ := by omega
  rw [e] at hmain
  rw [hmain]
  have hz1 : airyZeroCount (bwnX x δ (K + (k₁ : ℤ))) = 0 := by
    have : K + (k₁ : ℤ) = mw := by omega
    rw [this]
    exact bwn_count_zero (by linarith [P.hXm.1])
  simp only [hz1]
  rw [hstart.2]
  simp

end BwnSetup


/-- info: 'FormalResearch.Special.BwnSetup.count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.BwnSetup.count

end FormalResearch.Special
