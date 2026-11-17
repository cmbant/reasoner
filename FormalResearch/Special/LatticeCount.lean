module

public import FormalResearch.Special.LatticeSetup

/-!
# Level counting for a calibrated phase lattice: `lem:latticesum` (o)

`LevelData` packages the data of the lemma: a continuous `t = Θ/π`, strictly increasing on `[-X,X]`,
`ε`-close to the calibrated phase `t₀ = Re τ₀` on `[-X-1,X+1]`, and the finite set `S` of levels
`{x ∈ [-X,X] : t x ∈ ℤ}`.

* `card_levels_le` : `#(S ∩ [a,b]) ≤ M (b-a) + 2ε + 1` (so each unit interval contains `≤ M+2ε+1`
  levels, and `n ≤ 2MX + 2ε + 1`);
* `spacing_ge`, `spacing_le` : consecutive levels are at distance in
  `[(1-2ε)/M, (1+2ε)/m]` (the paper's `c/(ϰ log L) ≤ spacing ≤ C/(ϰ log L)`);
* `nearInt_meas` : the set where `t₀` is within `ε` of an integer has measure
  `≤ (M+2ε+1)·4ε/m` in each unit interval (the key to `(i)`: no factor `X`).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

/-- Data of the lattice lemma: `t = Θ/π`, levels `S`. -/
structure LevelData (τ0 : ℂ → ℂ) (X y0 m M K ε : ℝ) (t : ℝ → ℝ) (S : Finset ℝ) : Prop where
  cal : CalPhase τ0 X y0 m M K
  eps : 0 ≤ ε
  cont : Continuous t
  mono : StrictMonoOn t (Icc (-X) X)
  close : ∀ s : ℝ, |s| ≤ X + 1 → |t s - realPhase τ0 s| ≤ ε
  mem : ∀ x, x ∈ S ↔ x ∈ Icc (-X) X ∧ ∃ n : ℤ, t x = n

namespace LevelData

variable {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ} {t : ℝ → ℝ} {S : Finset ℝ}

lemma M_pos (h : LevelData τ0 X y0 m M K ε t S) : 0 < M := by
  have h1 := h.cal.ge ((0 : ℝ) : ℂ) (CalPhase.inWin_real (by simp; linarith [h.cal.hX]) h.cal.hy0.le)
  have h2 := h.cal.le 0 (by simp; linarith [h.cal.hX])
  linarith [h.cal.hm]

lemma m_le_M (h : LevelData τ0 X y0 m M K ε t S) : m ≤ M := by
  have h1 := h.cal.ge ((0 : ℝ) : ℂ) (CalPhase.inWin_real (by simp; linarith [h.cal.hX]) h.cal.hy0.le)
  have h2 := h.cal.le 0 (by simp; linarith [h.cal.hX])
  linarith

lemma mem_Icc_win {x : ℝ} (hx : x ∈ Icc (-X) X) : |x| ≤ X + 1 := by
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2]

/-- Cardinality of levels in an interval. -/
theorem card_levels_le (h : LevelData τ0 X y0 m M K ε t S) {a b : ℝ} (hab : a ≤ b) (ha : -X ≤ a)
    (hb : b ≤ X) :
    ((S.filter fun x => x ∈ Icc a b).card : ℝ) ≤ M * (b - a) + 2 * ε + 1 := by
  have hwa : |a| ≤ X + 1 := mem_Icc_win ⟨ha, by linarith⟩
  have hwb : |b| ≤ X + 1 := mem_Icc_win ⟨by linarith, hb⟩
  have hMpos := h.M_pos
  set lo : ℤ := ⌈realPhase τ0 a - ε⌉ with hlo
  set hi : ℤ := ⌊realPhase τ0 b + ε⌋ with hhi
  have hsl := h.cal.real_slope_le hwa hwb hab
  have hinj : Set.InjOn (fun x => ⌊t x⌋) (↑(S.filter fun x => x ∈ Icc a b) : Set ℝ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    obtain ⟨hxS, _⟩ := hx
    obtain ⟨hyS, _⟩ := hy
    obtain ⟨hx1, n, hn⟩ := (h.mem x).mp hxS
    obtain ⟨hy1, k, hk⟩ := (h.mem y).mp hyS
    simp only at hxy
    have : t x = t y := by
      rw [hn, hk]; rw [hn, Int.floor_intCast] at hxy; rw [hk, Int.floor_intCast] at hxy
      rw [hxy]
    exact h.mono.injOn hx1 hy1 this
  have hmaps : ∀ x ∈ S.filter fun x => x ∈ Icc a b, (fun x => ⌊t x⌋) x ∈ Finset.Icc lo hi := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    obtain ⟨hxS, hxab⟩ := hx
    obtain ⟨hx1, n, hn⟩ := (h.mem x).mp hxS
    have hfl : ⌊t x⌋ = n := by rw [hn, Int.floor_intCast]
    simp only [hfl, Finset.mem_Icc]
    have ha1 : a ∈ Icc (-X) X := ⟨ha, by linarith⟩
    have hb1 : b ∈ Icc (-X) X := ⟨by linarith, hb⟩
    have h1 : t a ≤ t x := h.mono.monotoneOn ha1 hx1 hxab.1
    have h2 : t x ≤ t b := h.mono.monotoneOn hx1 hb1 hxab.2
    have c1 := abs_le.mp (h.close a hwa)
    have c2 := abs_le.mp (h.close b hwb)
    constructor
    · rw [hlo, Int.ceil_le]; rw [hn] at h1; linarith
    · rw [hhi, Int.le_floor]; rw [hn] at h2; linarith
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Int.card_Icc] at hcard
  have e1 : (lo : ℝ) ≥ realPhase τ0 a - ε := Int.le_ceil _
  have e2 : (hi : ℝ) ≤ realPhase τ0 b + ε := Int.floor_le _
  have : (((hi + 1 - lo).toNat : ℕ) : ℝ) ≤ M * (b - a) + 2 * ε + 1 := by
    have h0 : (0 : ℝ) ≤ M * (b - a) + 2 * ε + 1 := by
      have := h.eps; nlinarith
    have : (((hi + 1 - lo).toNat : ℕ) : ℝ) = max ((hi + 1 - lo : ℤ) : ℝ) 0 := by
      rw [← Int.cast_natCast (R := ℝ), Int.toNat_eq_max]; push_cast; rfl
    rw [this]
    refine max_le ?_ h0
    push_cast; linarith
  calc ((S.filter fun x => x ∈ Icc a b).card : ℝ) ≤ (((hi + 1 - lo).toNat : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ _ := this

/-- Consecutive levels differ by exactly one unit of `t`. -/
lemma consecutive_diff (h : LevelData τ0 X y0 m M K ε t S) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x < y) (hcons : ∀ z ∈ S, ¬(x < z ∧ z < y)) : t y - t x = 1 := by
  obtain ⟨hx1, n, hn⟩ := (h.mem x).mp hx
  obtain ⟨hy1, k, hk⟩ := (h.mem y).mp hy
  have hlt : t x < t y := h.mono hx1 hy1 hxy
  rw [hn, hk] at hlt
  have hnk : n < k := by exact_mod_cast hlt
  by_contra hne
  have hk2 : n + 1 < k := by
    rcases (show n + 1 = k ∨ n + 1 < k by omega) with h1 | h1
    · exact absurd (by rw [hn, hk, ← h1]; push_cast; ring) hne
    · exact h1
  have hivt := intermediate_value_Ioo hxy.le (h.cont.continuousOn (s := Icc x y))
  have hmem : ((n + 1 : ℤ) : ℝ) ∈ Ioo (t x) (t y) := by
    rw [hn, hk]; constructor <;> exact_mod_cast (by omega)
  obtain ⟨z, hz, hzt⟩ := hivt hmem
  have hzI : z ∈ Icc (-X) X := ⟨by linarith [hx1.1, hz.1], by linarith [hy1.2, hz.2]⟩
  exact hcons z ((h.mem z).mpr ⟨hzI, n + 1, hzt⟩) hz

lemma spacing_ge (h : LevelData τ0 X y0 m M K ε t S) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x < y) (hcons : ∀ z ∈ S, ¬(x < z ∧ z < y)) : (1 - 2 * ε) / M ≤ y - x := by
  have hd := h.consecutive_diff hx hy hxy hcons
  have hx1 := ((h.mem x).mp hx).1
  have hy1 := ((h.mem y).mp hy).1
  have c1 := abs_le.mp (h.close x (mem_Icc_win hx1))
  have c2 := abs_le.mp (h.close y (mem_Icc_win hy1))
  have hsl := h.cal.real_slope_le (mem_Icc_win hx1) (mem_Icc_win hy1) hxy.le
  rw [div_le_iff₀ h.M_pos]
  linarith

lemma spacing_le (h : LevelData τ0 X y0 m M K ε t S) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x < y) (hcons : ∀ z ∈ S, ¬(x < z ∧ z < y)) : y - x ≤ (1 + 2 * ε) / m := by
  have hd := h.consecutive_diff hx hy hxy hcons
  have hx1 := ((h.mem x).mp hx).1
  have hy1 := ((h.mem y).mp hy).1
  have c1 := abs_le.mp (h.close x (mem_Icc_win hx1))
  have c2 := abs_le.mp (h.close y (mem_Icc_win hy1))
  have hsl := h.cal.real_slope_ge (mem_Icc_win hx1) (mem_Icc_win hy1) hxy.le
  rw [le_div_iff₀ h.cal.hm]
  linarith

end LevelData

namespace CalPhase

variable {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ}

lemma M_pos' (h : CalPhase τ0 X y0 m M K) : m ≤ M := by
  have h1 := h.ge ((0 : ℝ) : ℂ) (inWin_real (by simp; linarith [h.hX]) h.hy0.le)
  have h2 := h.le 0 (by simp; linarith [h.hX])
  linarith

/-- Points of the unit interval `[a,a+1]` where the real phase is within `ε` of an integer. -/
def nearInt (τ0 : ℂ → ℂ) (ε a : ℝ) : Set ℝ :=
  {s | s ∈ Icc a (a + 1) ∧ ∃ n : ℤ, |realPhase τ0 s - n| ≤ ε}

lemma J_subset (h : CalPhase τ0 X y0 m M K) (hε : 0 ≤ ε) {a : ℝ} (ha : -(X + 1) ≤ a)
    (hb : a + 1 ≤ X + 1) (n : ℤ) :
    volume {s : ℝ | s ∈ Icc a (a + 1) ∧ |realPhase τ0 s - n| ≤ ε} ≤ ENNReal.ofReal (4 * ε / m) := by
  by_cases hne : ∃ s0, s0 ∈ Icc a (a + 1) ∧ |realPhase τ0 s0 - n| ≤ ε
  · obtain ⟨s0, hs0, hn0⟩ := hne
    have hsub : {s : ℝ | s ∈ Icc a (a + 1) ∧ |realPhase τ0 s - n| ≤ ε} ⊆
        Icc (s0 - 2 * ε / m) (s0 + 2 * ε / m) := by
      intro s ⟨hs, hn⟩
      have hws : |s| ≤ X + 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hws0 : |s0| ≤ X + 1 := abs_le.mpr ⟨by linarith [hs0.1], by linarith [hs0.2]⟩
      have c1 := abs_le.mp hn
      have c2 := abs_le.mp hn0
      have hm := h.hm
      have key : |s - s0| ≤ 2 * ε / m := by
        rw [le_div_iff₀ hm]
        rcases le_total s0 s with h1 | h1
        · have := h.real_slope_ge hws0 hws h1
          rw [abs_of_nonneg (by linarith)]
          nlinarith
        · have := h.real_slope_ge hws hws0 h1
          rw [abs_of_nonpos (by linarith)]
          nlinarith
      have := abs_le.mp key
      constructor <;> linarith
    calc _ ≤ volume (Icc (s0 - 2 * ε / m) (s0 + 2 * ε / m)) := measure_mono hsub
      _ = ENNReal.ofReal (4 * ε / m) := by
        rw [Real.volume_Icc]; congr 1; ring
  · push_neg at hne
    have : {s : ℝ | s ∈ Icc a (a + 1) ∧ |realPhase τ0 s - n| ≤ ε} = ∅ := by
      ext s; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro ⟨h1, h2⟩; exact absurd h2 (not_le.mpr (hne s h1))
    rw [this]; simp

end CalPhase

namespace CalPhase

variable {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ}

/-- **Measure of the near-integer set** in a unit interval of the window. -/
theorem nearInt_meas (h : CalPhase τ0 X y0 m M K) (hε : 0 ≤ ε) {a : ℝ} (ha : -(X + 1) ≤ a)
    (hb : a + 1 ≤ X + 1) :
    volume (nearInt τ0 ε a) ≤ ENNReal.ofReal ((M + 2 * ε + 1) * (4 * ε / m)) := by
  have hwa : |a| ≤ X + 1 := abs_le.mpr ⟨ha, by linarith⟩
  have hwb : |a + 1| ≤ X + 1 := abs_le.mpr ⟨by linarith, hb⟩
  have hm := h.hm
  have hMm := h.M_pos'
  set lo : ℤ := ⌈realPhase τ0 a - ε⌉ with hlo
  set hi : ℤ := ⌊realPhase τ0 (a + 1) + ε⌋ with hhi
  have hcover : nearInt τ0 ε a ⊆ ⋃ n ∈ Finset.Icc lo hi,
      {s : ℝ | s ∈ Icc a (a + 1) ∧ |realPhase τ0 s - n| ≤ ε} := by
    intro s ⟨hs, n, hn⟩
    have hws : |s| ≤ X + 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have c := abs_le.mp hn
    have s1 := h.real_slope_ge hwa hws hs.1
    have s2 := h.real_slope_ge hws hwb hs.2
    have p1 : 0 ≤ m * (s - a) := mul_nonneg hm.le (by linarith [hs.1])
    have p2 : 0 ≤ m * (a + 1 - s) := mul_nonneg hm.le (by linarith [hs.2])
    simp only [mem_iUnion, mem_setOf_eq, Finset.mem_Icc]
    refine ⟨n, ⟨?_, ?_⟩, hs, hn⟩
    · rw [hlo, Int.ceil_le]; linarith
    · rw [hhi, Int.le_floor]; linarith
  have hsl := h.real_slope_le hwa hwb (by linarith : a ≤ a + 1)
  calc volume (nearInt τ0 ε a) ≤ volume (⋃ n ∈ Finset.Icc lo hi,
      {s : ℝ | s ∈ Icc a (a + 1) ∧ |realPhase τ0 s - n| ≤ ε}) := measure_mono hcover
    _ ≤ ∑ n ∈ Finset.Icc lo hi, volume {s : ℝ | s ∈ Icc a (a + 1) ∧ |realPhase τ0 s - n| ≤ ε} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ Finset.Icc lo hi, ENNReal.ofReal (4 * ε / m) :=
        Finset.sum_le_sum (fun n _ => J_subset h hε ha hb n)
    _ = ((Finset.Icc lo hi).card : ENNReal) * ENNReal.ofReal (4 * ε / m) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((M + 2 * ε + 1) * (4 * ε / m)) := by
        rw [ENNReal.ofReal_mul (by linarith)]
        gcongr
        rw [Int.card_Icc]
        have e1 : (lo : ℝ) ≥ realPhase τ0 a - ε := Int.le_ceil _
        have e2 : (hi : ℝ) ≤ realPhase τ0 (a + 1) + ε := Int.floor_le _
        have h0 : (0 : ℝ) ≤ M + 2 * ε + 1 := by linarith
        rw [← ENNReal.ofReal_natCast]
        apply ENNReal.ofReal_le_ofReal
        have : (((hi + 1 - lo).toNat : ℕ) : ℝ) = max ((hi + 1 - lo : ℤ) : ℝ) 0 := by
          rw [← Int.cast_natCast (R := ℝ), Int.toNat_eq_max]; push_cast; rfl
        rw [this]
        refine max_le ?_ h0
        push_cast; linarith

end CalPhase

end FormalResearch.Special.Lattice
