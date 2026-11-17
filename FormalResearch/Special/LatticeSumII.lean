module

public import FormalResearch.Special.LatticeSum

/-!
# `lem:latticesum` (ii), abstract form

* `card_le_eq` : `#{x ∈ S : x ≤ s} = ⌊t(s)⌋ - ⌈t(-X)⌉ + 1` on `[-X, X]` (the paper's
  `N(s) = ⌊τ(s)⌋ + κ₀`, with `κ₀` identified);
* `sum_eq_levels` : `∑_{x∈S} φ(x) = ⌊t(X)⌋ φ(X) + (1 - ⌈t(-X)⌉) φ(-X) - ∫ φ' t + ∫ φ' {t}`;
* `latticeII_bound` : `‖∑_{x∈S} φ(x) - ∫_{-X}^{X} φ t₀'‖ ≤ (1+2ε) C_φ e^{-κX} + 2ε C_φ'/κ + (i)-bound(φ')`.

Both boundary coefficients `⌊t(X)⌋ - t₀(X) + ½` and `t₀(-X) + 1 - ⌈t(-X)⌉ - ½` have modulus `≤ ½ + ε`
whatever the offset `θ₀`; this removes the reduction `|θ₀| ≤ π` and the bound on `κ₀` of the paper.
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

namespace LevelData

variable {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ} {t : ℝ → ℝ} {S : Finset ℝ}

theorem card_le_eq (h : LevelData τ0 X y0 m M K ε t S) {s : ℝ} (hs : s ∈ Icc (-X) X) :
    (((S.filter (fun x => x ≤ s)).card : ℕ) : ℤ) = ⌊t s⌋ - ⌈t (-X)⌉ + 1 := by
  have hXs : -X ≤ s := hs.1
  have hmX : (-X) ∈ Icc (-X) X := ⟨le_rfl, by linarith [hs.1, hs.2]⟩
  have hts : t (-X) ≤ t s := h.mono.monotoneOn hmX hs hXs
  have hcard : (S.filter (fun x => x ≤ s)).card = (Finset.Icc ⌈t (-X)⌉ ⌊t s⌋).card := by
    refine Finset.card_bij (fun x _ => ⌊t x⌋) (fun x hx => ?_) (fun x hx y hy hxy => ?_) (fun k hk => ?_)
    · simp only [Finset.mem_filter] at hx
      obtain ⟨hxS, hxs⟩ := hx
      obtain ⟨hx1, n, hn⟩ := (h.mem x).mp hxS
      simp only [Finset.mem_Icc]
      have hfl : ⌊t x⌋ = n := by rw [hn, Int.floor_intCast]
      rw [hfl]
      have h1 : t (-X) ≤ t x := h.mono.monotoneOn hmX hx1 hx1.1
      have h2 : t x ≤ t s := h.mono.monotoneOn hx1 hs hxs
      rw [hn] at h1 h2
      exact ⟨Int.ceil_le.mpr h1, Int.le_floor.mpr h2⟩
    · simp only [Finset.mem_filter] at hx hy
      obtain ⟨hx1, n, hn⟩ := (h.mem x).mp hx.1
      obtain ⟨hy1, k, hk⟩ := (h.mem y).mp hy.1
      have : t x = t y := by
        rw [hn, hk]; rw [hn, Int.floor_intCast] at hxy; rw [hk, Int.floor_intCast] at hxy
        rw [hxy]
      exact h.mono.injOn hx1 hy1 this
    · simp only [Finset.mem_Icc] at hk
      have hk1 : t (-X) ≤ k := Int.ceil_le.mp hk.1
      have hk2 : (k : ℝ) ≤ t s := Int.le_floor.mp hk.2
      have hcont : ContinuousOn t (Icc (-X) s) := h.cont.continuousOn
      obtain ⟨x, hx, hxk⟩ := intermediate_value_Icc hXs hcont ⟨hk1, hk2⟩
      have hxI : x ∈ Icc (-X) X := ⟨hx.1, hx.2.trans hs.2⟩
      refine ⟨x, ?_, ?_⟩
      · simp only [Finset.mem_filter]
        exact ⟨(h.mem x).mpr ⟨hxI, k, hxk⟩, hx.2⟩
      · show ⌊t x⌋ = k
        rw [hxk, Int.floor_intCast]
  rw [hcard, Int.card_Icc]
  have hle : ⌈t (-X)⌉ ≤ ⌊t s⌋ + 1 := (Int.ceil_mono hts).trans (Int.ceil_le_floor_add_one _)
  rw [Int.natCast_toNat_eq_self.mpr (by omega)]
  ring

end LevelData

end FormalResearch.Special.Lattice
