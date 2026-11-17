module

public import FormalResearch.Special.RacahWindowGeom
public import FormalResearch.Special.BulkWindowRk

/-!
# Racah window, part 2: the node count of an Airy window (generic centred Racah data, `τ = ±1`)

`RwnSetup` is `BwnSetup` (`BulkWindowRk`) for general centred Racah data `(P, Q, τ, x, q_*)` (the `3j` chain is `(P, Q) = (1, 0)`, `q_* = √(1-x²)`) and the lattice `q_k = (k + θ) δ³`
(`θ = 1/2`: integer data; `θ = 1`: half-integer data): the Airy window `RkWinAtG θ (θ δ³) P Q τ x q_* Y ...` with `κ²δ ≥ 1`, `|μ| ≤ δ³|κ|`, the chart identity and the smallness conditions.
**`RwnSetup.count`**: at a window site `K + i` with `q ∈ [q_* - ρ, q_*)`, `Φ(q)/δ³ ≥ 16/3`, `|cos(Φ/δ³ - π/4)| > 1/10`, the sequence `u_j = Y_{K+j}` has exactly `⌊Φ(q_{K+i})/(π δ³) + 1/4⌋` nodes
(`bix_c`) in the bonds `i, …, m_w - K - 1` (`m_w` the turning site).  The proof is the proof of `BwnSetup.count` verbatim; the only change is that the two facts specific to `3j`
(`x ∈ (0,1)`, `Φ ≤ (π/2)(q_* - q)`) are replaced by the hypotheses `hqs0` and `hphase`.

**Claim class: proved.**  **Not formalised:** that the hypotheses hold for the `6j` chain (`RacahWindowChain`).
-/

@[expose] public section

open Finset Set FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- The lattice site `q_k = (k + θ) δ³`. -/
noncomputable def rwnQ (θ δ : ℝ) (k : ℤ) : ℝ := ((k : ℝ) + θ) * δ ^ 3

lemma rwnQ_mono {δ : ℝ} (θ : ℝ) (hδ : 0 < δ) {k k' : ℤ} (h : k ≤ k') : rwnQ θ δ k ≤ rwnQ θ δ k' := by
  unfold rwnQ
  have : (k : ℝ) ≤ k' := by exact_mod_cast h
  have : 0 < δ ^ 3 := by positivity
  nlinarith

lemma rwnQ_succ (θ δ : ℝ) (k : ℤ) : rwnQ θ δ (k + 1) = rwnQ θ δ k + δ ^ 3 := by
  unfold rwnQ; push_cast; ring

lemma rwn_dalQ (θ δ : ℝ) (k : ℤ) : dalQ (θ * δ ^ 3) δ k = rwnQ θ δ k := by unfold dalQ rwnQ; ring

/-- The lattice variable `X_k = h^{-2/3} ζ(q_k)` of the window. -/
noncomputable def rwnX (P Q τ x qs θ δ : ℝ) : ℤ → ℝ := turnX (hrU P Q τ x) qs (θ * δ ^ 3) δ

/-- The Langer amplitude along the lattice. -/
noncomputable def rwnG (P Q τ x qs θ δ : ℝ) : ℤ → ℝ :=
  fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (θ * δ ^ 3) δ k)

/-- The hypotheses of `RwnSetup.count`, collected. -/
structure RwnSetup (P Q τ x qs θ : ℝ) (Y : ℤ → ℝ) (r C gmin c1 c2 δ κ μ ρ ρ0 cpos : ℝ) (J mw N' K : ℤ) (i : ℕ) : Prop where
  hqs0 : 0 < qs
  hθ : 0 ≤ θ
  hphase : ∀ q : ℝ, qs - ρ0 < q → q < qs → bkPhase P Q τ x qs q ≤ π / 2 * (qs - q)
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
  hchart : ∀ q : ℝ, qs - ρ0 < q → q < qs →
      langerZeta (hrU P Q τ x) (qs) q < 0 ∧
      2 / 3 * (-langerZeta (hrU P Q τ x) (qs) q) ^ (3 / 2 : ℝ) = bkPhase P Q τ x (qs) q
  hcpos : ∀ X ∈ Set.Icc (-1 : ℝ) (1 / 4), cpos ≤ airyAi X
  hE1 : bwnE C gmin δ < cpos
  hE2 : 8 * bwnE C gmin δ ≤ bwn_c0 * (c1 * δ)
  hE3 : bwnE C gmin δ ^ 2 / δ ^ 2 ≤ bwn_c0 ^ 2 / 2
  hE4 : bwnE C gmin δ < δ / 25
  hJ1 : 1 ≤ J
  hJm : J ≤ mw
  hmN : mw ≤ N'
  hqJ : rwnQ θ δ J < qs - r + δ ^ 3
  hqm1 : qs ≤ rwnQ θ δ mw
  hqm2 : rwnQ θ δ mw < qs + δ ^ 3
  hXle : ∀ k ∈ Finset.Icc J (mw + 1), rwnX P Q τ x qs θ δ k ≤ 1 / 4
  hgm : ∀ k ∈ Finset.Icc J (N' + 1), gmin ≤ rwnG P Q τ x qs θ δ k
  hstep : ∀ k ∈ Finset.Icc J N', c1 * δ ≤ rwnX P Q τ x qs θ δ (k + 1) - rwnX P Q τ x qs θ δ k ∧ rwnX P Q τ x qs θ δ (k + 1) - rwnX P Q τ x qs θ δ k ≤ c2 * δ
  hXm : 0 ≤ rwnX P Q τ x qs θ δ mw ∧ rwnX P Q τ x qs θ δ mw ≤ c2 * δ
  hYk : ∀ k ∈ Finset.Icc J (N' + 1),
    |Y k - (κ * (rwnG P Q τ x qs θ δ k * airyAi (rwnX P Q τ x qs θ δ k)) + μ * (rwnG P Q τ x qs θ δ k * airyBi (rwnX P Q τ x qs θ δ k)))| ≤
      C * δ ^ 3 * (|κ| * airyWt (rwnX P Q τ x qs θ δ k) + |μ| * airyBiWt (rwnX P Q τ x qs θ δ k))
  hq0 : qs - ρ ≤ rwnQ θ δ (K + i)
  hq1 : rwnQ θ δ (K + i) < qs
  hbig : 16 / 3 ≤ bkPhase P Q τ x (qs) (rwnQ θ δ (K + i)) / δ ^ 3
  hcos : 1 / 10 < |Real.cos (bkPhase P Q τ x (qs) (rwnQ θ δ (K + i)) / δ ^ 3 - π / 4)|

namespace RwnSetup

variable {P Q τ x qs θ r C gmin c1 c2 δ κ μ ρ ρ0 cpos : ℝ} {Y : ℤ → ℝ} {J mw N' K : ℤ} {i : ℕ}

lemma hδ3 (S : RwnSetup P Q τ x qs θ Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) : 0 < δ ^ 3 := by
  have := S.hδ; positivity

/-- The site `K + i` precedes the turning site. -/
lemma hlt (S : RwnSetup P Q τ x qs θ Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) : K + (i : ℤ) < mw := by
  by_contra hc
  push Not at hc
  have h1 := rwnQ_mono θ S.hδ hc
  have h2 := S.hq1
  have h3 := S.hqm1
  linarith

/-- The site `K + i` lies in the window. -/
lemma hJle (S : RwnSetup P Q τ x qs θ Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) : J ≤ K + (i : ℤ) := by
  by_contra hc
  push Not at hc
  have h1 : K + (i : ℤ) ≤ J - 1 := by omega
  have h2 := rwnQ_mono θ S.hδ h1
  have h4 : rwnQ θ δ (J - 1 + 1) = rwnQ θ δ J := by congr 1; ring
  have h5 := rwnQ_succ θ δ (J - 1)
  rw [h4] at h5
  have h6 := S.hqJ
  have h7 := S.hq0
  have h8 := S.hρr
  linarith


/-- Inner sites (before the turning site): the chart is valid, `X < 0`, `(2/3)(-X)^{3/2} = Φ(q)/δ³`, and `δ √(-X)` is small. -/
lemma inner (S : RwnSetup P Q τ x qs θ Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) {k : ℤ} (h1 : K + (i : ℤ) ≤ k) (h2 : k < mw) :
    rwnX P Q τ x qs θ δ k < 0 ∧
      2 / 3 * (-rwnX P Q τ x qs θ δ k) ^ (3 / 2 : ℝ) = bkPhase P Q τ x (qs) (rwnQ θ δ k) / δ ^ 3 ∧
      c2 * δ * √(-rwnX P Q τ x qs θ δ k) ≤ 1 / 4 ∧ (-rwnX P Q τ x qs θ δ k) * δ ^ 2 ≤ 1 := by
  have hδ3 := S.hδ3
  have hqlo : qs - ρ ≤ rwnQ θ δ k := S.hq0.trans (rwnQ_mono θ S.hδ h1)
  have hqhi : rwnQ θ δ k < qs := by
    have h3 : k + 1 ≤ mw := h2
    have h4 := rwnQ_mono θ S.hδ h3
    rw [rwnQ_succ] at h4
    have := S.hqm2
    linarith
  have hJ := S.hJle
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by have := S.hJ1; omega : (1 : ℤ) ≤ k)
  obtain ⟨hneg, hI⟩ := S.hchart _ (by linarith [S.hρ0]) hqhi
  obtain ⟨hpos, hI2⟩ := bwn_chart_X (neg_pos.2 hneg) hδ3 hI
  have hv : -rwnX P Q τ x qs θ δ k = (δ ^ 3) ^ (-(2 / 3) : ℝ) * (-langerZeta (hrU P Q τ x) (qs) (rwnQ θ δ k)) := by
    unfold rwnX turnX dalX
    rw [rwn_dalQ]; ring
  have hvpos : 0 < -rwnX P Q τ x qs θ δ k := by rw [hv]; exact hpos
  have hξ : 2 / 3 * (-rwnX P Q τ x qs θ δ k) ^ (3 / 2 : ℝ) = bkPhase P Q τ x (qs) (rwnQ θ δ k) / δ ^ 3 := by
    rw [hv]; exact hI2
  refine ⟨by linarith, hξ, ?_⟩
  have hph := S.hphase _ (by linarith [S.hρ0]) hqhi
  have hξ' : 2 / 3 * (-rwnX P Q τ x qs θ δ k) ^ (3 / 2 : ℝ) ≤ π / 2 * ρ / δ ^ 3 := by
    rw [hξ]
    apply div_le_div_of_nonneg_right _ hδ3.le
    refine hph.trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact bwn_vbounds hvpos S.hδ (by linarith [S.hc1, S.hc12]) S.hρ4 S.hρ.le S.hρc hξ'


/-- The zero count of `Ai` at consecutive lattice points: antitone, dropping by at most one. -/
lemma hz_bond (S : RwnSetup P Q τ x qs θ Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) {k : ℤ} (h1 : K + (i : ℤ) ≤ k) (h2 : k + 1 ≤ mw) :
    airyZeroCount (rwnX P Q τ x qs θ δ (k + 1)) ≤ airyZeroCount (rwnX P Q τ x qs θ δ k) ∧
      airyZeroCount (rwnX P Q τ x qs θ δ k) ≤ airyZeroCount (rwnX P Q τ x qs θ δ (k + 1)) + 1 := by
  have hJ := S.hJle
  have hmN := S.hmN
  have hst := S.hstep k (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hd0 : 0 < c1 * δ := mul_pos S.hc1 S.hδ
  have hle : rwnX P Q τ x qs θ δ k ≤ rwnX P Q τ x qs θ δ (k + 1) := by linarith [hst.1]
  refine ⟨bwn_count_anti hle, ?_⟩
  by_cases hX : -1 ≤ rwnX P Q τ x qs θ δ k
  · rw [bwn_count_zero hX]; exact Nat.zero_le _
  · push Not at hX
    obtain ⟨hneg, -, hc2, -⟩ := S.inner h1 (by omega : k < mw)
    set v := -rwnX P Q τ x qs θ δ k with hv
    have hv1 : 1 < v := by rw [hv]; linarith
    have hsq : 1 ≤ √v := by rw [Real.one_le_sqrt]; exact hv1.le
    have hc2δ : c2 * δ ≤ 1 / 4 := by
      have : c2 * δ * 1 ≤ c2 * δ * √v := mul_le_mul_of_nonneg_left hsq (mul_pos (lt_of_lt_of_le S.hc1 S.hc12) S.hδ).le
      linarith
    have hx' : rwnX P Q τ x qs θ δ (k + 1) ≤ 0 := by linarith [hst.2]
    have hcount := bwn_count_step (x := rwnX P Q τ x qs θ δ k) (x' := rwnX P Q τ x qs θ δ (k + 1)) (Y := v) (by linarith) (by rw [hv]; linarith)
      hle hx' (by
        have : (rwnX P Q τ x qs θ δ (k + 1) - rwnX P Q τ x qs θ δ k) * √v ≤ c2 * δ * √v :=
          mul_le_mul_of_nonneg_right hst.2 (Real.sqrt_nonneg _)
        linarith [Real.pi_gt_three])
    exact hcount

/-- The error of the sampling, in units of `|κ| g`. -/
lemma hu_site (S : RwnSetup P Q τ x qs θ Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) {k : ℤ} (h1 : K + (i : ℤ) ≤ k) (h2 : k ≤ mw) :
    |Y k - κ * (rwnG P Q τ x qs θ δ k * airyAi (rwnX P Q τ x qs θ δ k))| ≤ bwnE C gmin δ * (|κ| * rwnG P Q τ x qs θ δ k) := by
  have hJ := S.hJle
  have hmN := S.hmN
  have hk : k ∈ Finset.Icc J (N' + 1) := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hX1 := S.hXle k (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  obtain ⟨hW1, hW2, hB⟩ := bwn_wt_le hX1
  exact bwn_err (S.hgm k hk) S.hgmin S.hδ S.hδ1 S.hμ hB hW1 hW2 (S.hYk k hk) (airyBiWt_pos _).le S.hC

/-- At the turning site `Ai(X_{m_w}) > E`. -/
lemma end_site (S : RwnSetup P Q τ x qs θ Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) :
    bwnE C gmin δ < |airyAi (rwnX P Q τ x qs θ δ mw)| := by
  have h1 := S.hXle mw (Finset.mem_Icc.2 ⟨S.hJm, by omega⟩)
  have h2 := S.hcpos (rwnX P Q τ x qs θ δ mw) ⟨by linarith [S.hXm.1], h1⟩
  have := S.hE1
  rw [abs_of_pos (by linarith [S.hE1, bwnE_nonneg S.hC S.hgmin S.hδ])]
  linarith

/-- The start site has `v ≥ 4`, and the count of zeros is the floor. -/
lemma start_site (S : RwnSetup P Q τ x qs θ Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) :
    bwnE C gmin δ < |airyAi (rwnX P Q τ x qs θ δ (K + i))| ∧
      (airyZeroCount (rwnX P Q τ x qs θ δ (K + i)) : ℤ) =
        ⌊bkPhase P Q τ x (qs) (rwnQ θ δ (K + i)) / (π * δ ^ 3) + 1 / 4⌋ := by
  obtain ⟨hneg, hξ, -, hvδ⟩ := S.inner (le_refl _) S.hlt
  set v := -rwnX P Q τ x qs θ δ (K + i) with hv
  have hvpos : 0 < v := by rw [hv]; linarith
  have hv4 : 4 ≤ v := by
    by_contra hc
    push Not at hc
    have h1 : v ^ (3 / 2 : ℝ) < (4 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_lt_rpow hvpos.le hc (by norm_num)
    have e : (4 : ℝ) ^ (3 / 2 : ℝ) = 8 := by
      rw [← sqrt_cube_eq_rpow (by norm_num : (0 : ℝ) < 4)]
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num
    have := S.hbig
    rw [← hξ] at this
    linarith
  have hcos' : 1 / 10 < |Real.cos (2 / 3 * v ^ (3 / 2 : ℝ) - π / 4)| := by
    rw [hξ]; exact S.hcos
  refine ⟨?_, ?_⟩
  · have := bwn_Ai_lower hv4 hvδ S.hδ S.hδ1 hcos'
    have e : rwnX P Q τ x qs θ δ (K + i) = -v := by rw [hv]; ring
    rw [e]
    linarith [S.hE4]
  · have := bwn_count_floor hvpos hcos'
    have e : rwnX P Q τ x qs θ δ (K + i) = -v := by rw [hv]; ring
    rw [e, this, hξ]
    congr 1
    field_simp


/-- **Isolation of a near-zero site**: an interior site with `|Ai(X_k)| ≤ E` has definite neighbours of opposite signs. -/
lemma hnd_site (S : RwnSetup P Q τ x qs θ Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) {k : ℤ} (h1 : K + (i : ℤ) < k) (h2 : k < mw)
    (hs : |airyAi (rwnX P Q τ x qs θ δ k)| ≤ bwnE C gmin δ) :
    bwnE C gmin δ < |airyAi (rwnX P Q τ x qs θ δ (k - 1))| ∧ bwnE C gmin δ < |airyAi (rwnX P Q τ x qs θ δ (k + 1))| ∧
      airyAi (rwnX P Q τ x qs θ δ (k - 1)) * airyAi (rwnX P Q τ x qs θ δ (k + 1)) < 0 := by
  have hJ := S.hJle
  have hmN := S.hmN
  have hE0 := bwnE_nonneg S.hC S.hgmin S.hδ
  have hc0 := bwn_c0_pos
  have hX1 := S.hXle k (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hXlt : rwnX P Q τ x qs θ δ k < -1 := by
    by_contra hc
    push Not at hc
    have := S.hcpos (rwnX P Q τ x qs θ δ k) ⟨hc, hX1⟩
    have h3 := S.hE1
    have h4 := le_abs_self (airyAi (rwnX P Q τ x qs θ δ k))
    linarith
  obtain ⟨hneg, -, hc2, hvδ⟩ := S.inner h1.le h2
  set v := -rwnX P Q τ x qs θ δ k with hv
  have hvpos : 0 < v := by rw [hv]; linarith
  have hst := S.hstep k (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hst' := S.hstep (k - 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have e1 : k - 1 + 1 = k := by ring
  rw [e1] at hst'
  have hd0 : 0 < c1 * δ := mul_pos S.hc1 S.hδ
  have hδ2 : 0 < δ ^ 2 := by have := S.hδ; positivity
  -- the hypotheses of the linearisation lemma
  have hεc : -rwnX P Q τ x qs θ δ k * bwnE C gmin δ ^ 2 ≤ bwn_c0 ^ 2 / 2 := by
    have h3 : v * bwnE C gmin δ ^ 2 ≤ bwnE C gmin δ ^ 2 / δ ^ 2 := by
      rw [le_div_iff₀ hδ2]
      have := mul_le_mul_of_nonneg_right hvδ (sq_nonneg (bwnE C gmin δ))
      nlinarith
    have := S.hE3
    rw [← hv]; linarith
  have hdw : (rwnX P Q τ x qs θ δ (k + 1) - rwnX P Q τ x qs θ δ k) * √(-rwnX P Q τ x qs θ δ k) ≤ 1 / 4 := by
    have : (rwnX P Q τ x qs θ δ (k + 1) - rwnX P Q τ x qs θ δ k) * √v ≤ c2 * δ * √v :=
      mul_le_mul_of_nonneg_right hst.2 (Real.sqrt_nonneg _)
    linarith
  have hdw' : (rwnX P Q τ x qs θ δ k - rwnX P Q τ x qs θ δ (k - 1)) * √(-rwnX P Q τ x qs θ δ k) ≤ 1 / 4 := by
    have : (rwnX P Q τ x qs θ δ k - rwnX P Q τ x qs θ δ (k - 1)) * √v ≤ c2 * δ * √v :=
      mul_le_mul_of_nonneg_right hst'.2 (Real.sqrt_nonneg _)
    linarith
  have hdε : 8 * bwnE C gmin δ ≤ bwn_c0 * (rwnX P Q τ x qs θ δ (k + 1) - rwnX P Q τ x qs θ δ k) := by
    have := mul_le_mul_of_nonneg_left hst.1 hc0.le
    linarith [S.hE2]
  have hdε' : 8 * bwnE C gmin δ ≤ bwn_c0 * (rwnX P Q τ x qs θ δ k - rwnX P Q τ x qs θ δ (k - 1)) := by
    have := mul_le_mul_of_nonneg_left hst'.1 hc0.le
    linarith [S.hE2]
  obtain ⟨s, hs1, h3, h4⟩ := bwn_nz (x := rwnX P Q τ x qs θ δ k) (ε := bwnE C gmin δ) (by linarith) hs hεc
    (by linarith [hst.1]) (by linarith [hst'.1]) hdw hdw' hdε hdε'
  have e2 : rwnX P Q τ x qs θ δ k + (rwnX P Q τ x qs θ δ (k + 1) - rwnX P Q τ x qs θ δ k) = rwnX P Q τ x qs θ δ (k + 1) := by ring
  have e3 : rwnX P Q τ x qs θ δ k - (rwnX P Q τ x qs θ δ k - rwnX P Q τ x qs θ δ (k - 1)) = rwnX P Q τ x qs θ δ (k - 1) := by ring
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
theorem count (S : RwnSetup P Q τ x qs θ Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i) :
    K + (i : ℤ) < mw ∧
      ((∑ j ∈ Finset.Ico i (mw - K).toNat, bix_c (fun j : ℕ => Y (K + j)) j : ℕ) : ℤ) =
        ⌊bkPhase P Q τ x (qs) (rwnQ θ δ (K + i)) / (π * δ ^ 3) + 1 / 4⌋ := by
  have hlt := S.hlt
  refine ⟨hlt, ?_⟩
  have hJ := S.hJle
  have hmN := S.hmN
  have hE0 := bwnE_nonneg S.hC S.hgmin S.hδ
  have hκ0 : κ ≠ 0 := by
    intro h; have := S.hκ; rw [h] at this; norm_num at this
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
  have W : BwnWin (fun j : ℕ => Y (K + j)) (fun j : ℕ => airyAi (rwnX P Q τ x qs θ δ (K + j)))
      (fun j : ℕ => |κ| * rwnG P Q τ x qs θ δ (K + j)) (fun j : ℕ => airyZeroCount (rwnX P Q τ x qs θ δ (K + j))) s (bwnE C gmin δ) i k₁ := by
    refine ⟨hs1, hE0, ?_, ?_, ?_, ?_, ?_⟩
    · intro j h1 h2
      obtain ⟨a1, a2⟩ := hmem j h1 h2
      have hg := S.hgm (K + j) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      exact mul_pos (abs_pos.2 hκ0) (lt_of_lt_of_le S.hgmin hg)
    · intro j h1 h2
      obtain ⟨a1, a2⟩ := hmem j h1 h2
      have := S.hu_site a1 a2
      have e : s * (|κ| * rwnG P Q τ x qs θ δ (K + j)) * airyAi (rwnX P Q τ x qs θ δ (K + j)) = κ * (rwnG P Q τ x qs θ δ (K + j) * airyAi (rwnX P Q τ x qs θ δ (K + j))) := by
        rw [show κ * (rwnG P Q τ x qs θ δ (K + j) * airyAi (rwnX P Q τ x qs θ δ (K + j))) =
          (s * |κ|) * (rwnG P Q τ x qs θ δ (K + j) * airyAi (rwnX P Q τ x qs θ δ (K + j))) by rw [hsκ]]; ring
      rw [e]; exact this
    · intro j h1 h2 hne
      exact bwn_sign_all _ hne
    · intro j h1 h2
      obtain ⟨a1, a2⟩ := hmem j h1 h2.le
      have e : K + ((j + 1 : ℕ) : ℤ) = K + (j : ℤ) + 1 := by push_cast; ring
      have := S.hz_bond a1 (by omega : K + (j : ℤ) + 1 ≤ mw)
      simp only [e]
      exact this
    · intro j h1 h2 hs'
      have a1 : K + (i : ℤ) < K + (j : ℤ) := by omega
      have a2 : K + (j : ℤ) < mw := by omega
      obtain ⟨b1, b2, b3⟩ := S.hnd_site a1 a2 hs'
      have e1 : K + ((j - 1 : ℕ) : ℤ) = K + (j : ℤ) - 1 := by omega
      have e2 : K + ((j + 1 : ℕ) : ℤ) = K + (j : ℤ) + 1 := by push_cast; ring
      simp only [e1, e2]
      exact ⟨b1, b2, b3⟩
  have hstart := S.start_site
  have hdef0 : bwnE C gmin δ < |airyAi (rwnX P Q τ x qs θ δ (K + (i : ℤ)))| := hstart.1
  have hdef1 : bwnE C gmin δ < |airyAi (rwnX P Q τ x qs θ δ (K + (k₁ : ℤ)))| := by
    have : K + (k₁ : ℤ) = mw := by omega
    rw [this]; exact S.end_site
  have hmain := BwnWin.count W (k₁ - i) i le_rfl (by omega) hdef0 (by
    have : i + (k₁ - i) = k₁ := by omega
    rw [this]; exact hdef1)
  have e : i + (k₁ - i) = k₁ := by omega
  rw [e] at hmain
  rw [hmain]
  have hz1 : airyZeroCount (rwnX P Q τ x qs θ δ (K + (k₁ : ℤ))) = 0 := by
    have : K + (k₁ : ℤ) = mw := by omega
    rw [this]
    exact bwn_count_zero (by linarith [S.hXm.1])
  simp only [hz1]
  rw [hstart.2]
  simp

end RwnSetup


/-- info: 'FormalResearch.Special.RwnSetup.count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.RwnSetup.count

end FormalResearch.Special
