module

public import Mathlib

/-!
# Paper J: the order argument for the bulk labels (thm:A (i), "Location and labels"), abstractly

Source: Paper J `thmA.tex`, proof of `thm:A (i)`, paragraph "Location and labels" (the windows of consecutive bulk eigenvalues are consecutive; the label is anchored at the soft window `0`).

An eigenvalue list is abstracted to a set `Eig` of reals, the action `S_0^{(t)}` to a function `S`, and the bulk blocks to finitely many closed intervals `[lo nu, hi nu]` covering `B = [Jlo, Jhi]`.
The Prop-structure `ScaleFacts` collects what `bulk_count`, `bulk_zero_window` (windows, at most one eigenvalue per window, one in every window whose bracket lies in `S_0(block)`) and the quantitative slope
of `S_0` give at fixed `(mu, N)`; everything else here is real analysis.

## Proved here (axiom-pinned)

* `leb_blocks`: a Lebesgue number of the block cover (`cover_bulk`: every point of `B` is in the relative interior of a block).
* `ScaleFacts.consec`: two consecutive eigenvalues of `B` (nothing of `Eig` strictly between) have consecutive windows `lab x' = lab x + 1`, `lab y = floor (S y / (pi h))`.
* `ScaleFacts.anchor_exists`: an eigenvalue of `Eig` in `[Jhi - eps, Jhi]` (from the existence clause for a window inside the last block).
* `labels_of_anchor`: along a strictly decreasing eigenvalue list `X`, if `lab (X a) = a` for one `a` with `X a` in `B`, then `lab (X i) = i` for every `i` with `X i` in `B`.

## Differences from the paper

The paper argues with the (fixed) windows of the soft edge and induction down the blocks; here the induction is on the eigenvalue index along the whole of `B`, and blocks enter only through the Lebesgue number.

## Not formalised

The identification of `ScaleFacts` with the spectral data (`TheoremA/Labels.lean`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Set

/-- Lebesgue number of the block cover. -/
theorem leb_blocks {nb : ℕ} (lo hi : Fin nb → ℝ) (Jlo Jhi : ℝ)
    (hcov : ∀ X, Jlo ≤ X → X ≤ Jhi → ∃ ν, lo ν ≤ X ∧ X ≤ hi ν ∧ (lo ν < X ∨ lo ν = Jlo) ∧ (X < hi ν ∨ hi ν = Jhi))
    (hJ : ∀ ν, Jlo ≤ lo ν ∧ lo ν ≤ hi ν ∧ hi ν ≤ Jhi) :
    ∃ δ > 0, ∀ x ∈ Icc Jlo Jhi, ∃ ν, Metric.ball x δ ∩ Icc Jlo Jhi ⊆ Icc (lo ν) (hi ν) := by
  let W : Fin nb → Set ℝ := fun ν => {z | (lo ν < z ∨ lo ν = Jlo) ∧ (z < hi ν ∨ hi ν = Jhi)}
  have hopen : ∀ ν, IsOpen (W ν) := by
    intro ν
    have h1 : IsOpen {z : ℝ | lo ν < z ∨ lo ν = Jlo} := by
      by_cases h : lo ν = Jlo
      · simp [h]
      · simp only [h, or_false]; exact isOpen_Ioi
    have h2 : IsOpen {z : ℝ | z < hi ν ∨ hi ν = Jhi} := by
      by_cases h : hi ν = Jhi
      · simp [h]
      · simp only [h, or_false]; exact isOpen_Iio
    exact h1.inter h2
  have hsub : Icc Jlo Jhi ⊆ ⋃ ν, W ν := by
    intro X hX
    obtain ⟨ν, -, -, h1, h2⟩ := hcov X hX.1 hX.2
    exact mem_iUnion.mpr ⟨ν, h1, h2⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hopen hsub
  refine ⟨δ, hδ, fun x hx => ?_⟩
  obtain ⟨ν, hν⟩ := hball x hx
  refine ⟨ν, fun z hz => ?_⟩
  obtain ⟨hzb, hzI⟩ := hz
  obtain ⟨h1, h2⟩ := hν hzb
  obtain ⟨hl, hu, -⟩ := hJ ν
  refine ⟨?_, ?_⟩
  · rcases h1 with h | h
    · exact h.le
    · rw [h]; exact hzI.1
  · rcases h2 with h | h
    · exact h.le
    · rw [h]; exact hzI.2

/-- two points of `B` within `delta` lie in a common block -/
lemma common_block {nb : ℕ} {lo hi : Fin nb → ℝ} {Jlo Jhi δ : ℝ} (hδ : 0 < δ)
    (hleb : ∀ x ∈ Icc Jlo Jhi, ∃ ν, Metric.ball x δ ∩ Icc Jlo Jhi ⊆ Icc (lo ν) (hi ν))
    {a b : ℝ} (ha : a ∈ Icc Jlo Jhi) (hb : b ∈ Icc Jlo Jhi) (hab : a ≤ b) (hd : b - a < δ) :
    ∃ ν, a ∈ Icc (lo ν) (hi ν) ∧ b ∈ Icc (lo ν) (hi ν) := by
  obtain ⟨ν, hν⟩ := hleb a ha
  exact ⟨ν, hν ⟨Metric.mem_ball_self hδ, ha⟩,
    hν ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]; linarith, hb⟩⟩

/-- strict monotonicity on every block gives it on `B` -/
theorem strictAntiOn_of_blocks {nb : ℕ} {lo hi : Fin nb → ℝ} {Jlo Jhi δ : ℝ} (hδ : 0 < δ) (S : ℝ → ℝ)
    (hleb : ∀ x ∈ Icc Jlo Jhi, ∃ ν, Metric.ball x δ ∩ Icc Jlo Jhi ⊆ Icc (lo ν) (hi ν))
    (hanti : ∀ ν, StrictAntiOn S (Icc (lo ν) (hi ν))) : StrictAntiOn S (Icc Jlo Jhi) := by
  have key : ∀ n : ℕ, ∀ x ∈ Icc Jlo Jhi, ∀ y ∈ Icc Jlo Jhi, x < y → y - x ≤ n * (δ / 2) → S y < S x := by
    intro n
    induction n with
    | zero => intro x hx y hy hxy hd; simp at hd; linarith
    | succ n ih =>
      intro x hx y hy hxy hd
      by_cases hnear : y - x < δ
      · obtain ⟨ν, h1, h2⟩ := common_block hδ hleb hx hy hxy.le hnear
        exact hanti ν h1 h2 hxy
      · push Not at hnear
        have hz : x + δ / 2 ∈ Icc Jlo Jhi := ⟨by linarith [hx.1], by linarith [hy.2]⟩
        obtain ⟨ν, h1, h2⟩ := common_block hδ hleb hx hz (by linarith) (by linarith)
        have e1 : S (x + δ / 2) < S x := hanti ν h1 h2 (by linarith)
        have e2 : S y < S (x + δ / 2) := ih _ hz y hy (by linarith) (by push_cast at hd; nlinarith)
        linarith
  intro x hx y hy hxy
  obtain ⟨n, hn⟩ := exists_nat_ge ((y - x) / (δ / 2))
  exact key n x hx y hy hxy (by rw [div_le_iff₀ (by positivity)] at hn; exact hn)

/-- continuity on every block gives it on `B` -/
theorem continuousOn_of_blocks {nb : ℕ} {lo hi : Fin nb → ℝ} {Jlo Jhi δ : ℝ} (hδ : 0 < δ) (S : ℝ → ℝ)
    (hleb : ∀ x ∈ Icc Jlo Jhi, ∃ ν, Metric.ball x δ ∩ Icc Jlo Jhi ⊆ Icc (lo ν) (hi ν))
    (hcont : ∀ ν, ContinuousOn S (Icc (lo ν) (hi ν))) : ContinuousOn S (Icc Jlo Jhi) := by
  intro z hz
  obtain ⟨ν, hν⟩ := hleb z hz
  have hmem : Icc (lo ν) (hi ν) ∈ nhdsWithin z (Icc Jlo Jhi) := by
    refine Filter.mem_of_superset (inter_mem_nhdsWithin (Icc Jlo Jhi) (Metric.ball_mem_nhds z hδ)) ?_
    intro w hw
    exact hν ⟨hw.2, hw.1⟩
  exact (hcont ν z (hν ⟨Metric.mem_ball_self hδ, hz⟩)).mono_of_mem_nhdsWithin hmem

/-- the floor label of a window of half-width `p/8` -/
lemma floor_lab_eq {s p : ℝ} {j : ℕ} (hp : 0 < p) (hw : |s - p * ((j : ℝ) + 1 / 2)| ≤ p / 8) : ⌊s / p⌋₊ = j := by
  obtain ⟨h1, h2⟩ := abs_le.mp hw
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hs : 0 ≤ s / p := div_nonneg (by nlinarith) hp.le
  rw [Nat.floor_eq_iff hs]
  constructor
  · rw [le_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-- **The facts about the scale `h`, the action `S` and the eigenvalue set `Eig`** (what `bulk_count`, `bulk_zero_window` and the slope of `S_0` give at one `(mu, N)`). -/
structure ScaleFacts (S : ℝ → ℝ) (Eig : Set ℝ) (Jlo Jhi : ℝ) {nb : ℕ} (lo hi : Fin nb → ℝ) (h : ℝ) (ε : Fin nb → ℝ)
    (c C1 δ : ℝ) : Prop where
  h_pos : 0 < h
  c_pos : 0 < c
  δ_pos : 0 < δ
  eps_small : ∀ ν, ε ν ≤ Real.pi * h / 8
  small : (Real.pi + C1) * h < c * (δ / 2)
  anti : StrictAntiOn S (Icc Jlo Jhi)
  cont : ContinuousOn S (Icc Jlo Jhi)
  nonneg : ∀ x ∈ Icc Jlo Jhi, 0 ≤ S x
  blocks : ∀ ν, Jlo ≤ lo ν ∧ lo ν ≤ hi ν ∧ hi ν ≤ Jhi
  leb : ∀ x ∈ Icc Jlo Jhi, ∃ ν, Metric.ball x δ ∩ Icc Jlo Jhi ⊆ Icc (lo ν) (hi ν)
  slope : ∀ ν, ∀ x ∈ Icc (lo ν) (hi ν), ∀ y ∈ Icc (lo ν) (hi ν), x ≤ y → c * (y - x) - C1 * h ≤ S x - S y
  win : ∀ ν, ∀ x ∈ Eig, x ∈ Icc (lo ν) (hi ν) → ∃ j : ℕ, |S x - Real.pi * h * ((j : ℝ) + 1 / 2)| ≤ ε ν
  uniq : ∀ ν (j : ℕ), ∀ x ∈ Eig, x ∈ Icc (lo ν) (hi ν) → ∀ x' ∈ Eig, x' ∈ Icc (lo ν) (hi ν) →
    |S x - Real.pi * h * ((j : ℝ) + 1 / 2)| ≤ ε ν → |S x' - Real.pi * h * ((j : ℝ) + 1 / 2)| ≤ ε ν → x = x'
  exist : ∀ ν (j : ℕ), Icc (Real.pi * h * j) (Real.pi * h * (j + 1)) ⊆ S '' Icc (lo ν) (hi ν) →
    ∃ x ∈ Eig, x ∈ Icc (lo ν) (hi ν) ∧ |S x - Real.pi * h * ((j : ℝ) + 1 / 2)| ≤ ε ν

namespace ScaleFacts

variable {S : ℝ → ℝ} {Eig : Set ℝ} {Jlo Jhi : ℝ} {nb : ℕ} {lo hi : Fin nb → ℝ} {h : ℝ} {ε : Fin nb → ℝ} {c C1 δ : ℝ}

/-- the window integer (floor label) -/
def lab (S : ℝ → ℝ) (h : ℝ) (x : ℝ) : ℕ := ⌊S x / (Real.pi * h)⌋₊

lemma pih_pos (F : ScaleFacts S Eig Jlo Jhi lo hi h ε c C1 δ) : 0 < Real.pi * h := mul_pos Real.pi_pos F.h_pos

/-- an eigenvalue in a block lies in the window of its label -/
lemma win_lab (F : ScaleFacts S Eig Jlo Jhi lo hi h ε c C1 δ) {ν : Fin nb} {x : ℝ} (hx : x ∈ Eig) (hxν : x ∈ Icc (lo ν) (hi ν)) :
    |S x - Real.pi * h * ((lab S h x : ℝ) + 1 / 2)| ≤ ε ν := by
  obtain ⟨j, hj⟩ := F.win ν x hx hxν
  have h8 : |S x - Real.pi * h * ((j : ℝ) + 1 / 2)| ≤ Real.pi * h / 8 := hj.trans (F.eps_small ν)
  have : lab S h x = j := floor_lab_eq F.pih_pos h8
  rw [this]; exact hj

/-- every point of `B` lies in a block -/
lemma exists_block (F : ScaleFacts S Eig Jlo Jhi lo hi h ε c C1 δ) {x : ℝ} (hx : x ∈ Icc Jlo Jhi) : ∃ ν, x ∈ Icc (lo ν) (hi ν) := by
  obtain ⟨ν, hν⟩ := F.leb x hx
  exact ⟨ν, hν ⟨Metric.mem_ball_self F.δ_pos, hx⟩⟩

/-- the global quantitative slope -/
lemma global_slope (F : ScaleFacts S Eig Jlo Jhi lo hi h ε c C1 δ) {x y : ℝ} (hx : x ∈ Icc Jlo Jhi) (hy : y ∈ Icc Jlo Jhi) (hxy : x ≤ y) :
    c * min (y - x) (δ / 2) - C1 * h ≤ S x - S y := by
  by_cases hd : y - x < δ
  · obtain ⟨ν, hν⟩ := F.leb x hx
    have hxν : x ∈ Icc (lo ν) (hi ν) := hν ⟨Metric.mem_ball_self F.δ_pos, hx⟩
    have hyν : y ∈ Icc (lo ν) (hi ν) := hν ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]; linarith, hy⟩
    have := F.slope ν x hxν y hyν hxy
    have hm : min (y - x) (δ / 2) ≤ y - x := min_le_left _ _
    nlinarith [F.c_pos]
  · push Not at hd
    set y' := x + δ / 2 with hy'
    have hδ := F.δ_pos
    have hy'B : y' ∈ Icc Jlo Jhi := ⟨by linarith [hx.1], by linarith [hy.2]⟩
    obtain ⟨ν, hν⟩ := F.leb x hx
    have hxν : x ∈ Icc (lo ν) (hi ν) := hν ⟨Metric.mem_ball_self hδ, hx⟩
    have hyν : y' ∈ Icc (lo ν) (hi ν) := hν ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]; linarith, hy'B⟩
    have h1 := F.slope ν x hxν y' hyν (by linarith)
    have h2 : S y ≤ S y' := by
      rcases eq_or_lt_of_le (show y' ≤ y by linarith) with e | e
      · rw [e]
      · exact (F.anti hy'B hy e).le
    have hm : min (y - x) (δ / 2) ≤ δ / 2 := min_le_right _ _
    nlinarith [F.c_pos]

/-- **Consecutive eigenvalues have consecutive windows.** -/
theorem consec (F : ScaleFacts S Eig Jlo Jhi lo hi h ε c C1 δ) {x x' : ℝ} (hx : x ∈ Eig) (hx' : x' ∈ Eig)
    (hxB : x ∈ Icc Jlo Jhi) (hx'B : x' ∈ Icc Jlo Jhi) (hlt : x' < x) (hnone : ∀ y ∈ Eig, ¬ (x' < y ∧ y < x)) :
    lab S h x' = lab S h x + 1 := by
  have hp := F.pih_pos
  have hpi := Real.pi_pos
  have hh := F.h_pos
  obtain ⟨νx, hνx⟩ := F.exists_block hxB
  obtain ⟨νx', hνx'⟩ := F.exists_block hx'B
  have hwx := (F.win_lab hx hνx).trans (F.eps_small νx)
  have hwx' := (F.win_lab hx' hνx').trans (F.eps_small νx')
  have hSlt : S x < S x' := F.anti hx'B hxB hlt
  obtain ⟨hxw1, hxw2⟩ := abs_le.mp hwx
  obtain ⟨hxw1', hxw2'⟩ := abs_le.mp hwx'
  set j := lab S h x with hj
  set j' := lab S h x' with hj'
  have hjj : j ≤ j' := by
    refine Nat.floor_mono (div_le_div_of_nonneg_right hSlt.le hp.le)
  have hcm : ∀ a b : ℝ, a ∈ Icc Jlo Jhi → b ∈ Icc Jlo Jhi → a ≤ b → b - a < δ → ∃ ν, a ∈ Icc (lo ν) (hi ν) ∧ b ∈ Icc (lo ν) (hi ν) := by
    intro a b ha hb hab hd
    obtain ⟨ν, hν⟩ := F.leb a ha
    exact ⟨ν, hν ⟨Metric.mem_ball_self F.δ_pos, ha⟩,
      hν ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]; linarith, hb⟩⟩
  by_contra hne
  have hcase : j' = j ∨ j + 2 ≤ j' := by omega
  rcases hcase with e | e
  · -- same window: uniqueness inside a common block
    have hdrop : c * min (x - x') (δ / 2) - C1 * h ≤ S x' - S x := F.global_slope hx'B hxB hlt.le
    have hS : S x' - S x ≤ Real.pi * h / 4 := by
      have : (j' : ℝ) = j := by exact_mod_cast e
      rw [this] at hxw1' hxw2'
      linarith
    have hmin : min (x - x') (δ / 2) = x - x' := by
      by_contra hn
      have : min (x - x') (δ / 2) = δ / 2 := by
        rcases min_choice (x - x') (δ / 2) with h1 | h1
        · exact absurd h1 hn
        · exact h1
      rw [this] at hdrop
      nlinarith [F.small, F.c_pos]
    have hxd : x - x' < δ := by
      have : c * (x - x') ≤ Real.pi * h / 4 + C1 * h := by rw [hmin] at hdrop; linarith
      by_contra hn
      push Not at hn
      nlinarith [F.small, F.c_pos]
    obtain ⟨ν, h1, h2⟩ := hcm x' x hx'B hxB hlt.le hxd
    have h8 := F.win_lab hx h2
    have h8' := F.win_lab hx' h1
    have : (j : ℝ) = (j' : ℝ) := by exact_mod_cast e.symm
    have hu := F.uniq ν j x hx h2 x' hx' h1 h8 (by rw [← hj'] at h8'; rw [e] at h8'; exact h8')
    exact absurd hu (ne_of_gt hlt)
  · -- a window is skipped: an eigenvalue of the skipped window lies strictly between
    have hjR : (j : ℝ) + 2 ≤ j' := by exact_mod_cast e
    have hSx : S x < Real.pi * h * ((j : ℝ) + 1) := by nlinarith
    have hSx' : Real.pi * h * ((j : ℝ) + 2) < S x' := by nlinarith
    have hcont' : ContinuousOn S (Icc x' x) := F.cont.mono (Icc_subset_Icc hx'B.1 hxB.2)
    have hivt := intermediate_value_Icc' hlt.le hcont'
    obtain ⟨x1, hx1, hx1S⟩ := hivt (show Real.pi * h * ((j : ℝ) + 1) ∈ Icc (S x) (S x') from ⟨hSx.le, by nlinarith⟩)
    obtain ⟨x2, hx2, hx2S⟩ := hivt (show Real.pi * h * ((j : ℝ) + 2) ∈ Icc (S x) (S x') from ⟨by nlinarith, hSx'.le⟩)
    have hx1B : x1 ∈ Icc Jlo Jhi := ⟨by linarith [hx1.1, hx'B.1], by linarith [hx1.2, hxB.2]⟩
    have hx2B : x2 ∈ Icc Jlo Jhi := ⟨by linarith [hx2.1, hx'B.1], by linarith [hx2.2, hxB.2]⟩
    have h21 : x2 < x1 := by
      by_contra hn
      push Not at hn
      rcases eq_or_lt_of_le hn with e' | e'
      · rw [← e'] at hx2S; nlinarith [hx1S]
      · have := F.anti hx1B hx2B e'
        nlinarith
    have hdrop : c * min (x1 - x2) (δ / 2) - C1 * h ≤ S x2 - S x1 := F.global_slope hx2B hx1B h21.le
    have hS : S x2 - S x1 = Real.pi * h := by rw [hx2S, hx1S]; ring
    have hmin : min (x1 - x2) (δ / 2) = x1 - x2 := by
      by_contra hn
      have : min (x1 - x2) (δ / 2) = δ / 2 := by
        rcases min_choice (x1 - x2) (δ / 2) with h1 | h1
        · exact absurd h1 hn
        · exact h1
      rw [this, hS] at hdrop
      nlinarith [F.small, F.c_pos]
    have hxd : x1 - x2 < δ := by
      rw [hmin, hS] at hdrop
      by_contra hn
      push Not at hn
      nlinarith [F.small, F.c_pos]
    obtain ⟨ν, hν2, hν1⟩ := hcm x2 x1 hx2B hx1B h21.le hxd
    have hsub : Icc x2 x1 ⊆ Icc (lo ν) (hi ν) := Icc_subset_Icc hν2.1 hν1.2
    have hcont2 : ContinuousOn S (Icc x2 x1) := F.cont.mono (Icc_subset_Icc hx2B.1 hx1B.2)
    have hivt2 := intermediate_value_Icc' h21.le hcont2
    have hbr : Icc (Real.pi * h * (((j + 1 : ℕ) : ℝ))) (Real.pi * h * (((j + 1 : ℕ) : ℝ) + 1)) ⊆ S '' Icc (lo ν) (hi ν) := by
      refine Subset.trans ?_ (Set.image_mono hsub)
      refine Subset.trans ?_ hivt2
      rw [hx1S, hx2S]
      push_cast
      refine Icc_subset_Icc le_rfl (le_of_eq (by ring))
    obtain ⟨y, hyE, hyν, hyw⟩ := F.exist ν (j + 1) hbr
    have hyB : y ∈ Icc Jlo Jhi := ⟨(F.blocks ν).1.trans hyν.1, hyν.2.trans (F.blocks ν).2.2⟩
    obtain ⟨hyw1, hyw2⟩ := abs_le.mp (hyw.trans (F.eps_small ν))
    push_cast at hyw1 hyw2
    have hy1 : S x < S y := by nlinarith
    have hy2 : S y < S x' := by nlinarith
    have hyx : y < x := by
      by_contra hn
      push Not at hn
      rcases eq_or_lt_of_le hn with e' | e'
      · rw [← e'] at hy1; exact lt_irrefl _ hy1
      · have := F.anti hxB hyB e'
        linarith
    have hx'y : x' < y := by
      by_contra hn
      push Not at hn
      rcases eq_or_lt_of_le hn with e' | e'
      · rw [e'] at hy2; exact lt_irrefl _ hy2
      · have := F.anti hyB hx'B e'
        linarith
    exact hnone y hyE ⟨hx'y, hyx⟩

/-- **An eigenvalue near the top of `B`.**  If `block ν*` ends at `Jhi` and the slope drop over its last `min (..) eps''` is at least `2 pi h` (plus the slope loss), there is an eigenvalue in `[Jhi - eps'', Jhi]`. -/
theorem anchor_exists (F : ScaleFacts S Eig Jlo Jhi lo hi h ε c C1 δ) (ν : Fin nb) (hνtop : hi ν = Jhi) (hνlt : lo ν < Jhi)
    (e : ℝ) (he : 0 < e) (hbig : (2 * Real.pi + C1) * h ≤ c * min (Jhi - lo ν) e) :
    ∃ y ∈ Eig, Jhi - e ≤ y ∧ y ≤ Jhi ∧ y ∈ Icc Jlo Jhi := by
  have hp := F.pih_pos
  have hpi := Real.pi_pos
  have hh := F.h_pos
  obtain ⟨hb1, hb2, hb3⟩ := F.blocks ν
  set xl := max (lo ν) (Jhi - e) with hxl
  have hxl1 : lo ν ≤ xl := le_max_left _ _
  have hxl2 : xl ≤ Jhi := max_le hνlt.le (by linarith)
  have hxlB : xl ∈ Icc Jlo Jhi := ⟨hb1.trans hxl1, hxl2⟩
  have hJB : Jhi ∈ Icc Jlo Jhi := ⟨hb1.trans (hb2.trans hb3), le_rfl⟩
  have hxlν : xl ∈ Icc (lo ν) (hi ν) := ⟨hxl1, by rw [hνtop]; exact hxl2⟩
  have hJν : Jhi ∈ Icc (lo ν) (hi ν) := ⟨hνlt.le, hνtop.ge⟩
  have hdrop := F.slope ν xl hxlν Jhi hJν hxl2
  have hlen : c * min (Jhi - lo ν) e ≤ c * (Jhi - xl) := by
    refine mul_le_mul_of_nonneg_left ?_ F.c_pos.le
    rw [hxl]
    rcases le_total (lo ν) (Jhi - e) with h1 | h1
    · rw [max_eq_right h1]; exact (min_le_right _ _).trans (by linarith)
    · rw [max_eq_left h1]; exact (min_le_left _ _).trans (by linarith)
  have hS2 : 2 * (Real.pi * h) ≤ S xl - S Jhi := by nlinarith
  set a := S Jhi / (Real.pi * h) with ha
  have ha0 : 0 ≤ a := div_nonneg (F.nonneg Jhi hJB) hp.le
  set k := ⌈a⌉₊ with hk
  have hk1 : a ≤ k := Nat.le_ceil a
  have hk2 : (k : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
  have hSa : S Jhi = Real.pi * h * a := by rw [ha]; field_simp
  have hlow : S Jhi ≤ Real.pi * h * k := by rw [hSa]; exact mul_le_mul_of_nonneg_left hk1 hp.le
  have hup : Real.pi * h * (k + 1) ≤ S xl := by
    have : Real.pi * h * ((k : ℝ) + 1) ≤ Real.pi * h * (a + 2) := mul_le_mul_of_nonneg_left (by linarith) hp.le
    rw [hSa] at hS2
    nlinarith
  have hcont : ContinuousOn S (Icc xl Jhi) := F.cont.mono (Icc_subset_Icc hxlB.1 le_rfl)
  have hivt := intermediate_value_Icc' hxl2 hcont
  have hbr : Icc (Real.pi * h * k) (Real.pi * h * (k + 1)) ⊆ S '' Icc (lo ν) (hi ν) := by
    refine Subset.trans ?_ (Set.image_mono (Icc_subset_Icc hxl1 (by rw [hνtop])))
    refine Subset.trans ?_ hivt
    exact Icc_subset_Icc hlow hup
  obtain ⟨y, hyE, hyν, hyw⟩ := F.exist ν k hbr
  have hyB : y ∈ Icc Jlo Jhi := ⟨hb1.trans hyν.1, hyν.2.trans hb3⟩
  obtain ⟨hyw1, hyw2⟩ := abs_le.mp (hyw.trans (F.eps_small ν))
  have hyl : xl ≤ y := by
    by_contra hn
    push Not at hn
    have := F.anti hyB hxlB hn
    nlinarith
  refine ⟨y, hyE, ?_, hyν.2.trans (by rw [hνtop]), hyB⟩
  have : Jhi - e ≤ xl := le_max_right _ _
  linarith

end ScaleFacts

/-- **The label induction along the eigenvalue list.**  `X` strictly decreasing, `Eig = range X`; if the label of one eigenvalue `X a` of `B` is its index, then so is that of every eigenvalue of `B`. -/
theorem labels_of_anchor {S : ℝ → ℝ} {Jlo Jhi : ℝ} {nb : ℕ} {lo hi : Fin nb → ℝ} {h : ℝ} {ε : Fin nb → ℝ} {c C1 δ : ℝ} {N : ℕ}
    (X : Fin (N + 1) → ℝ) (hX : StrictAnti X) (F : ScaleFacts S (Set.range X) Jlo Jhi lo hi h ε c C1 δ)
    (a : Fin (N + 1)) (haB : X a ∈ Icc Jlo Jhi) (hal : ScaleFacts.lab S h (X a) = (a : ℕ)) :
    ∀ i : Fin (N + 1), X i ∈ Icc Jlo Jhi → ScaleFacts.lab S h (X i) = (i : ℕ) := by
  have hstep : ∀ i : ℕ, ∀ hi : i + 1 < N + 1, X ⟨i, by omega⟩ ∈ Icc Jlo Jhi → X ⟨i + 1, hi⟩ ∈ Icc Jlo Jhi →
      ScaleFacts.lab S h (X ⟨i + 1, hi⟩) = ScaleFacts.lab S h (X ⟨i, by omega⟩) + 1 := by
    intro i hi h1 h2
    refine F.consec ⟨_, rfl⟩ ⟨_, rfl⟩ h1 h2 (hX (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))) ?_
    rintro y ⟨l, rfl⟩ ⟨hy1, hy2⟩
    have hl1 : (⟨i, by omega⟩ : Fin (N + 1)) < l := hX.lt_iff_gt.mp hy2
    have hl2 : l < (⟨i + 1, hi⟩ : Fin (N + 1)) := hX.lt_iff_gt.mp hy1
    rw [Fin.lt_def] at hl1 hl2
    simp only at hl1 hl2
    omega
  obtain ⟨a', ha'⟩ := a
  simp only at hal haB
  have hanti : ∀ (i j : ℕ) (hi : i < N + 1) (hj : j < N + 1), i ≤ j → X ⟨j, hj⟩ ≤ X ⟨i, hi⟩ :=
    fun i j hi hj hij => hX.antitone (Fin.mk_le_mk.mpr hij)
  -- upward
  have hup : ∀ d : ℕ, ∀ hi : a' + d < N + 1, X ⟨a' + d, hi⟩ ∈ Icc Jlo Jhi →
      ScaleFacts.lab S h (X ⟨a' + d, hi⟩) = a' + d := by
    intro d
    induction d with
    | zero => intro hi _; exact hal
    | succ d ih =>
      intro hi hB
      have hi0 : a' + d < N + 1 := by omega
      have hprev : X ⟨a' + d, hi0⟩ ∈ Icc Jlo Jhi :=
        ⟨hB.1.trans (hanti (a' + d) (a' + (d + 1)) hi0 hi (by omega)), (hanti a' (a' + d) ha' hi0 (by omega)).trans haB.2⟩
      have := hstep (a' + d) hi hprev hB
      have h3 := ih hi0 hprev
      exact this.trans (by rw [h3]; rfl)
  -- downward
  have hdown : ∀ d : ℕ, ∀ hd : d ≤ a', X ⟨a' - d, by omega⟩ ∈ Icc Jlo Jhi →
      ScaleFacts.lab S h (X ⟨a' - d, by omega⟩) = a' - d := by
    intro d
    induction d with
    | zero => intro hd _; simpa using hal
    | succ d ih =>
      intro hd hB
      have hi1 : a' - d < N + 1 := by omega
      have hi0 : a' - (d + 1) < N + 1 := by omega
      have hnext : X ⟨a' - d, hi1⟩ ∈ Icc Jlo Jhi :=
        ⟨haB.1.trans (hanti (a' - d) a' hi1 ha' (by omega)), (hanti (a' - (d + 1)) (a' - d) hi0 hi1 (by omega)).trans hB.2⟩
      have h1 := ih (by omega) hnext
      have h2 := hstep (a' - (d + 1)) (by omega) hB (by
        have : a' - (d + 1) + 1 = a' - d := by omega
        simpa [this] using hnext)
      have e : a' - (d + 1) + 1 = a' - d := by omega
      simp only [e] at h2
      omega
  intro i hiB
  obtain ⟨i', hi'⟩ := i
  simp only at hiB ⊢
  rcases le_total a' i' with hle | hle
  · have := hup (i' - a') (by omega) (by simpa [Nat.add_sub_cancel' hle] using hiB)
    simpa [Nat.add_sub_cancel' hle] using this
  · have := hdown (a' - i') (Nat.sub_le _ _) (by simpa [Nat.sub_sub_self hle] using hiB)
    simpa [Nat.sub_sub_self hle] using this

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.leb_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.leb_blocks

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.strictAntiOn_of_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.strictAntiOn_of_blocks

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.continuousOn_of_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.continuousOn_of_blocks

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ScaleFacts.consec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ScaleFacts.consec

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ScaleFacts.anchor_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ScaleFacts.anchor_exists

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.labels_of_anchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.labels_of_anchor

end FormalResearch.JacobiEigenvectors.TheoremA

end
