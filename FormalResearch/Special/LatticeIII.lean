module

public import FormalResearch.Special.LatticeNu

/-!
# `lem:latticesum` (iii), abstract form

Source: `Weyl/free_fermion/paper/parts/constants.tex`, `lem:latticesum` (iii).  For `ν(e) = (1+e^e)⁻¹`
and levels `S = {x ∈ [-X,X] : t x ∈ ℤ}` of a strictly increasing `t = Θ/π`, the offset sum
`∑_{x∈S} [ν(2πx) - 1_{x<0}]` equals `{t₀} - ½ + 1_{t₀∈ℤ}` up to an explicit error (`t₀ = t 0`).

The proof here is a variant of the paper's: instead of the counting identities `N_±` and a limit `ε ↓ 0`
for `t₀ ∈ ℤ`, the summation by parts of `LatticeSum` (`sum_by_parts` with `φ = ν(2π·)`, `φ' = -w`) and
the exact count `N(s) = ⌊t s⌋ - ⌈t(-X)⌉ + 1` (`card_le_eq`) give, for every `t₀`, the identity
`S_ν = ∫_{-X}^X w(s)(⌊t(s)⌋ - ⌊t₀⌋) ds + 1_{t₀∈ℤ} + ν(2πX)(n - 2N₀)`
(`offset_identity`).  Then `⌊t⌋ - ⌊t₀⌋ = (t - t₀) - ({t} - ½) + ({t₀} - ½)`; the first integral is bounded by
oddness of `rp - rp(0)` (`rp = Re τ₀`) and the closeness `|t - rp| ≤ ε`, the second is `latticeI_bound`.

* `sum_nuR_eq` : summation by parts for `ν(2π·)`;
* `offset_identity` : the exact identity above;
* `latticeIII_bound` : `|S_ν - ({t₀} - ½) - 1_{t₀∈ℤ}| ≤ 2ε + B_I(w) + ν(2πX)(2MX + 2ε + 2)`.
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex Barnes MeasureTheory intervalIntegral

/-- Summation by parts for the Fermi function: `∑ ν(2πx) = ν(2πX)·#S + ∫ w N`. -/
theorem sum_nuR_eq {X : ℝ} (hX : 0 ≤ X) {S : Finset ℝ} (hS : ∀ x ∈ S, x ∈ Icc (-X) X) :
    ∑ x ∈ S, nuR (2 * Real.pi * x) = nuR (2 * Real.pi * X) * S.card +
      ∫ s in (-X)..X, wnu s * ((S.filter (fun x => x ≤ s)).card : ℝ) := by
  have hφd : ∀ s : ℝ, HasDerivAt (fun x : ℝ => ((nuR (2 * Real.pi * x) : ℝ) : ℂ))
      (((-wnu s : ℝ) : ℂ)) s := fun s => (hasDerivAt_nu2pi s).ofReal_comp
  have h := sum_by_parts hS (φ := fun x : ℝ => ((nuR (2 * Real.pi * x) : ℝ) : ℂ))
    (φ' := fun s : ℝ => ((-wnu s : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (continuous_nuR.comp (continuous_const.mul continuous_id)))
    (fun s _ => hφd s)
    (Complex.continuous_ofReal.comp continuous_wnu.neg).continuousOn hX
  have e : ∀ s : ℝ, ((-wnu s : ℝ) : ℂ) * (((S.filter (fun x => x ≤ s)).card : ℕ) : ℂ) =
      ((-(wnu s * ((S.filter (fun x => x ≤ s)).card : ℝ)) : ℝ) : ℂ) := fun s => by push_cast; ring
  simp_rw [e] at h
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_neg] at h
  apply Complex.ofReal_injective
  push_cast at h ⊢
  rw [h]; ring

lemma intervalIntegrable_mul_fract_real {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ} (hg : Continuous g)
    {t : ℝ → ℝ} (ht : Continuous t) :
    IntervalIntegrable (fun s => g s * (Int.fract (t s) - 1 / 2)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hm : AEStronglyMeasurable (fun s : ℝ => g s * (Int.fract (t s) - 1 / 2))
      (volume.restrict (Icc a b)) := by
    refine hg.aestronglyMeasurable.mul ?_
    exact ((measurable_fract.comp ht.measurable).aemeasurable.sub_const (1 / 2 : ℝ)).aestronglyMeasurable
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hg.continuousOn
  refine Integrable.of_bound hm (C * (1 / 2)) ?_
  refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall (fun s hs => ?_))
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : |Int.fract (t s) - 1 / 2| ≤ 1 / 2 := by
    have := Int.fract_nonneg (t s); have := Int.fract_lt_one (t s)
    rw [abs_le]; constructor <;> linarith
  have h0 : 0 ≤ C := (norm_nonneg _).trans (hC s hs)
  exact mul_le_mul (by simpa using hC s hs) h1 (abs_nonneg _) h0

lemma fract_eq_zero_iff' {x : ℝ} : Int.fract x = 0 ↔ ∃ n : ℤ, x = n := by
  constructor
  · intro h; exact ⟨⌊x⌋, by rw [Int.fract] at h; linarith⟩
  · rintro ⟨n, rfl⟩; exact Int.fract_intCast n

namespace LevelData

variable {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ} {t : ℝ → ℝ} {S : Finset ℝ}

lemma subset_Icc (h : LevelData τ0 X y0 m M K ε t S) : ∀ x ∈ S, x ∈ Icc (-X) X :=
  fun x hx => ((h.mem x).mp hx).1

lemma zero_mem_Icc (h : LevelData τ0 X y0 m M K ε t S) : (0 : ℝ) ∈ Icc (-X) X :=
  ⟨by linarith [h.cal.hX], h.cal.hX.le⟩

/-- `0 ∈ S` iff `t 0 ∈ ℤ`. -/
lemma zero_mem_iff (h : LevelData τ0 X y0 m M K ε t S) : (0 : ℝ) ∈ S ↔ Int.fract (t 0) = 0 := by
  rw [h.mem, fract_eq_zero_iff']; exact ⟨fun hh => hh.2, fun hh => ⟨h.zero_mem_Icc, hh⟩⟩

/-- Exact count `N(s) = (⌊t s⌋ - ⌊t 0⌋) + N(0)` on the window, as reals. -/
lemma card_le_real (h : LevelData τ0 X y0 m M K ε t S) {s : ℝ} (hs : s ∈ Icc (-X) X) :
    (((S.filter (fun x => x ≤ s)).card : ℕ) : ℝ) =
      ((⌊t s⌋ : ℝ) - ⌊t 0⌋) + (((S.filter (fun x => x ≤ 0)).card : ℕ) : ℝ) := by
  have h1 := h.card_le_eq hs
  have h2 := h.card_le_eq h.zero_mem_Icc
  have : (((S.filter (fun x => x ≤ s)).card : ℕ) : ℤ) =
      (⌊t s⌋ - ⌊t 0⌋) + (((S.filter (fun x => x ≤ 0)).card : ℕ) : ℤ) := by rw [h1, h2]; ring
  exact_mod_cast this

lemma card_lt_real (h : LevelData τ0 X y0 m M K ε t S) :
    (((S.filter (fun x => x < 0)).card : ℕ) : ℝ) =
      (((S.filter (fun x => x ≤ 0)).card : ℕ) : ℝ) - (if Int.fract (t 0) = 0 then 1 else 0) := by
  classical
  have hsplit : S.filter (fun x => x ≤ 0) = S.filter (fun x => x < 0) ∪ S.filter (fun x => x = 0) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hx, hle⟩
      rcases lt_or_eq_of_le hle with hl | he
      · exact Or.inl ⟨hx, hl⟩
      · exact Or.inr ⟨hx, he⟩
    · rintro (⟨hx, hl⟩ | ⟨hx, he⟩)
      · exact ⟨hx, hl.le⟩
      · exact ⟨hx, he.le⟩
  have hdisj : Disjoint (S.filter (fun x => x < 0)) (S.filter (fun x => x = 0)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter] at hx hx'
    linarith [hx.2, hx'.2]
  have hc : (S.filter (fun x => x ≤ 0)).card =
      (S.filter (fun x => x < 0)).card + (S.filter (fun x => x = 0)).card := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
  have hz : ((S.filter (fun x => x = 0)).card : ℝ) = if Int.fract (t 0) = 0 then 1 else 0 := by
    by_cases hn : Int.fract (t 0) = 0
    · have h0 : (0 : ℝ) ∈ S := h.zero_mem_iff.mpr hn
      have : S.filter (fun x => x = 0) = {0} := by
        ext x; simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · exact fun hx => hx.2
        · intro hx; subst hx; exact ⟨h0, rfl⟩
      rw [this]; simp [hn]
    · have h0 : (0 : ℝ) ∉ S := fun hh => hn (h.zero_mem_iff.mp hh)
      have : S.filter (fun x => x = 0) = ∅ := by
        ext x; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hx hx0; subst hx0; exact h0 hx
      rw [this]; simp [hn]
  have hc' : (((S.filter (fun x => x ≤ 0)).card : ℕ) : ℝ) =
      ((S.filter (fun x => x < 0)).card : ℝ) + ((S.filter (fun x => x = 0)).card : ℝ) := by
    exact_mod_cast hc
  linarith

end LevelData

lemma intervalIntegrable_wnu_floor {a b : ℝ} (hab : a ≤ b) {t : ℝ → ℝ} (ht : Continuous t) (c : ℝ) :
    IntervalIntegrable (fun s => wnu s * ((⌊t s⌋ : ℝ) - c)) volume a b := by
  have hw := continuous_wnu
  have h1 : IntervalIntegrable (fun s => wnu s * (t s - c - 1 / 2)) volume a b :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have h2 := intervalIntegrable_mul_fract_real hab continuous_wnu ht
  refine (h1.sub h2).congr (fun s _ => ?_)
  show wnu s * (t s - c - 1 / 2) - wnu s * (Int.fract (t s) - 1 / 2) = wnu s * ((⌊t s⌋ : ℝ) - c)
  rw [Int.fract]; ring

/-- Splitting `⌊t⌋ - ⌊t₀⌋ = (t - t₀) - ({t} - ½) + ({t₀} - ½)` inside the weighted integral. -/
lemma integral_wnu_floor_split {X : ℝ} {t : ℝ → ℝ} (ht : Continuous t) (hX : 0 ≤ X) :
    ∫ s in (-X)..X, wnu s * ((⌊t s⌋ : ℝ) - ⌊t 0⌋) =
      (∫ s in (-X)..X, wnu s * (t s - t 0)) - (∫ s in (-X)..X, wnu s * (Int.fract (t s) - 1 / 2)) +
        (Int.fract (t 0) - 1 / 2) * (1 - 2 * nuR (2 * Real.pi * X)) := by
  have hle : -X ≤ X := by linarith
  have hw := continuous_wnu
  have i1 : IntervalIntegrable (fun s => wnu s * (t s - t 0)) volume (-X) X :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have i2 := intervalIntegrable_mul_fract_real hle continuous_wnu ht
  have i3 : IntervalIntegrable (fun s => (Int.fract (t 0) - 1 / 2) * wnu s) volume (-X) X :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have e : ∀ s, wnu s * ((⌊t s⌋ : ℝ) - ⌊t 0⌋) = wnu s * (t s - t 0) - wnu s * (Int.fract (t s) - 1 / 2) +
      (Int.fract (t 0) - 1 / 2) * wnu s := fun s => by
    rw [Int.fract, Int.fract]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const_mul, integral_wnu_sym]

/-- The exact identity behind `lem:latticesum` (iii). -/
theorem LevelData.offset_identity {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ} {t : ℝ → ℝ} {S : Finset ℝ}
    (h : LevelData τ0 X y0 m M K ε t S) :
    ∑ x ∈ S, (nuR (2 * Real.pi * x) - if x < 0 then (1 : ℝ) else 0) =
      (∫ s in (-X)..X, wnu s * ((⌊t s⌋ : ℝ) - ⌊t 0⌋)) + (if Int.fract (t 0) = 0 then 1 else 0) +
        nuR (2 * Real.pi * X) * ((S.card : ℝ) - 2 * (((S.filter (fun x => x ≤ 0)).card : ℕ) : ℝ)) := by
  have hX := h.cal.hX
  have hle : -X ≤ X := by linarith
  have hr0 : ∑ x ∈ S, (if x < 0 then (1 : ℝ) else 0) = (((S.filter (fun x => x < 0)).card : ℕ) : ℝ) := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [Finset.sum_sub_distrib, hr0, sum_nuR_eq hX.le h.subset_Icc, h.card_lt_real]
  set N0 : ℝ := (((S.filter (fun x => x ≤ 0)).card : ℕ) : ℝ) with hN0
  have hi := intervalIntegrable_wnu_floor hle h.cont (⌊t 0⌋ : ℝ)
  have hint : ∫ s in (-X)..X, wnu s * (((S.filter (fun x => x ≤ s)).card : ℕ) : ℝ) =
      (∫ s in (-X)..X, wnu s * ((⌊t s⌋ : ℝ) - ⌊t 0⌋)) + N0 * (1 - 2 * nuR (2 * Real.pi * X)) := by
    have e : ∀ s ∈ uIcc (-X) X, wnu s * (((S.filter (fun x => x ≤ s)).card : ℕ) : ℝ) =
        wnu s * ((⌊t s⌋ : ℝ) - ⌊t 0⌋) + N0 * wnu s := by
      intro s hs
      rw [uIcc_of_le hle] at hs
      rw [h.card_le_real hs]; ring
    rw [intervalIntegral.integral_congr e,
      intervalIntegral.integral_add hi
        (Continuous.intervalIntegrable (by have := continuous_wnu; fun_prop : Continuous fun s => N0 * wnu s) _ _),
      intervalIntegral.integral_const_mul, integral_wnu_sym]
  rw [hint]
  ring

lemma integral_odd_sym {f : ℝ → ℝ} {X : ℝ} (hf : ∀ s, f (-s) = -f s) :
    ∫ s in (-X)..X, f s = 0 := by
  have h1 : ∫ s in (-X)..X, f (-s) = ∫ s in (-X)..X, f s := by
    rw [intervalIntegral.integral_comp_neg (fun s => f s)]; simp
  have h2 : ∫ s in (-X)..X, f (-s) = -∫ s in (-X)..X, f s := by
    simp_rw [hf]; rw [intervalIntegral.integral_neg]
  linarith

/-- The `t - t₀` integral: by oddness of `rp - rp(0)` it is bounded by `2ε`. -/
lemma integral_wnu_t_sub_le {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ} {t : ℝ → ℝ} {S : Finset ℝ}
    (hd : LevelData τ0 X y0 m M K ε t S)
    (hodd : ∀ s : ℝ, realPhase τ0 (-s) - realPhase τ0 0 = -(realPhase τ0 s - realPhase τ0 0)) :
    |∫ s in (-X)..X, wnu s * (t s - t 0)| ≤ 2 * ε := by
  have hX := hd.cal.hX
  have hle : -X ≤ X := by linarith
  have hsub : Icc (-X) X ⊆ Icc (-(X + 1)) (X + 1) := Icc_subset_Icc (by linarith) (by linarith)
  have hwc := continuous_wnu
  have iA : IntervalIntegrable (fun s => wnu s * (t s - t 0)) volume (-X) X :=
    Continuous.intervalIntegrable (by have := hd.cont; fun_prop) _ _
  have iB : IntervalIntegrable (fun s => wnu s * (realPhase τ0 s - realPhase τ0 0)) volume (-X) X := by
    refine ContinuousOn.intervalIntegrable_of_Icc hle ?_
    exact hwc.continuousOn.mul ((hd.cal.continuousOn_realPhase.mono hsub).sub continuousOn_const)
  have hzero : ∫ s in (-X)..X, wnu s * (realPhase τ0 s - realPhase τ0 0) = 0 := by
    refine integral_odd_sym (fun s => ?_)
    rw [wnu_neg, hodd s]; ring
  have hsubint : ∫ s in (-X)..X, wnu s * (t s - t 0) =
      ∫ s in (-X)..X, (wnu s * (t s - t 0) - wnu s * (realPhase τ0 s - realPhase τ0 0)) := by
    rw [intervalIntegral.integral_sub iA iB, hzero, sub_zero]
  rw [hsubint]
  have hb : ∀ s ∈ Icc (-X) X, |wnu s * (t s - t 0) - wnu s * (realPhase τ0 s - realPhase τ0 0)| ≤
      2 * ε * wnu s := by
    intro s hs
    have h1 := hd.close s (LevelData.mem_Icc_win hs)
    have h2 := hd.close 0 (LevelData.mem_Icc_win hd.zero_mem_Icc)
    have e : wnu s * (t s - t 0) - wnu s * (realPhase τ0 s - realPhase τ0 0) =
        wnu s * ((t s - realPhase τ0 s) - (t 0 - realPhase τ0 0)) := by ring
    rw [e, abs_mul, abs_of_nonneg (wnu_nonneg s), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (wnu_nonneg s)
    calc |(t s - realPhase τ0 s) - (t 0 - realPhase τ0 0)|
        ≤ |t s - realPhase τ0 s| + |t 0 - realPhase τ0 0| := abs_sub _ _
      _ ≤ ε + ε := add_le_add h1 h2
      _ = 2 * ε := by ring
  have hint2 : IntervalIntegrable (fun s => 2 * ε * wnu s) volume (-X) X :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  calc |∫ s in (-X)..X, (wnu s * (t s - t 0) - wnu s * (realPhase τ0 s - realPhase τ0 0))|
      ≤ ∫ s in (-X)..X, |wnu s * (t s - t 0) - wnu s * (realPhase τ0 s - realPhase τ0 0)| :=
        intervalIntegral.abs_integral_le_integral_abs hle
    _ ≤ ∫ s in (-X)..X, 2 * ε * wnu s := by
        refine intervalIntegral.integral_mono_on hle (iA.sub iB).abs hint2 (fun s hs => hb s hs)
    _ = 2 * ε * (1 - 2 * nuR (2 * Real.pi * X)) := by
        rw [intervalIntegral.integral_const_mul, integral_wnu_sym]
    _ ≤ 2 * ε := by
        have := (nuR_mem (2 * Real.pi * X)).1
        have := hd.eps
        nlinarith

/-- **`lem:latticesum` (iii)**, abstract form.  `t₀ = t 0`, `Z = 1_{t₀∈ℤ}`; explicit error
`2ε + B_I(w) + ν(2πX)(2MX + 2ε + 2)`, with `B_I` the bound of `latticeI_bound` for `φ = w`
(`C_w = 4π`, `κ = 2π`), `y₁ + r ≤ y₀ ≤ ¼`.  The hypothesis `hodd` says `rp - rp(0)` is odd
(`rp = Re τ₀`; for the Gamma phase it follows from oddness of `arg Γ(½+is)`). -/
theorem latticeIII_bound {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ} {t : ℝ → ℝ} {S : Finset ℝ}
    (hd : LevelData τ0 X y0 m M K ε t S) {y1 r : ℝ} (hy1 : 0 < y1) (hr : 0 < r) (hyr : y1 + r ≤ y0)
    (hy0 : y0 ≤ 1 / 4)
    (hodd : ∀ s : ℝ, realPhase τ0 (-s) - realPhase τ0 0 = -(realPhase τ0 s - realPhase τ0 0)) :
    |(∑ x ∈ S, (nuR (2 * Real.pi * x) - if x < 0 then (1 : ℝ) else 0)) -
        ((Int.fract (t 0) - 1 / 2) + if Int.fract (t 0) = 0 then 1 else 0)| ≤
      2 * ε + ((4 * Real.pi) * wconst (2 * Real.pi) * ε * (1 + 4 * (M + 2 * ε + 1) / m) +
        ((4 * Real.pi) * Real.exp (-(2 * Real.pi) * X) / m +
          1 / 12 * (2 * smoothCw (4 * Real.pi) (2 * Real.pi) r m K * y1 * Real.exp (-(2 * Real.pi) * X) +
            2 * smoothCw (4 * Real.pi) (2 * Real.pi) r m K / (2 * Real.pi) *
              Real.exp (-(2 * Real.pi * m * y1))))) +
        nuR (2 * Real.pi * X) * (M * (2 * X) + 2 * ε + 2) := by
  have hX := hd.cal.hX
  have hpi := Real.pi_pos
  have hle : -X ≤ X := by linarith
  have hy0pos : 0 < y0 := hd.cal.hy0
  -- the exact identity and the splitting
  have hid := hd.offset_identity
  rw [integral_wnu_floor_split hd.cont hX.le] at hid
  set A1 := ∫ s in (-X)..X, wnu s * (t s - t 0) with hA1
  set A2 := ∫ s in (-X)..X, wnu s * (Int.fract (t s) - 1 / 2) with hA2
  set N0 : ℝ := (((S.filter (fun x => x ≤ 0)).card : ℕ) : ℝ) with hN0
  set νX := nuR (2 * Real.pi * X) with hνX
  set Z : ℝ := if Int.fract (t 0) = 0 then 1 else 0 with hZ
  have hνX0 : 0 ≤ νX := (nuR_mem _).1
  have hA1b : |A1| ≤ 2 * ε := integral_wnu_t_sub_le hd hodd
  -- the fractional-part integral
  have hA2b : |A2| ≤ (4 * Real.pi) * wconst (2 * Real.pi) * ε * (1 + 4 * (M + 2 * ε + 1) / m) +
        ((4 * Real.pi) * Real.exp (-(2 * Real.pi) * X) / m +
          1 / 12 * (2 * smoothCw (4 * Real.pi) (2 * Real.pi) r m K * y1 * Real.exp (-(2 * Real.pi) * X) +
            2 * smoothCw (4 * Real.pi) (2 * Real.pi) r m K / (2 * Real.pi) *
              Real.exp (-(2 * Real.pi * m * y1)))) := by
    have hdiff : DifferentiableOn ℂ wC {s | |s.im| ≤ y0} :=
      differentiableOn_wC.mono (fun s (hs : |s.im| ≤ y0) => show |s.im| ≤ 1 / 4 from hs.trans hy0)
    have hb : ∀ s : ℂ, |s.im| ≤ y0 → ‖wC s‖ ≤ (4 * Real.pi) * Real.exp (-(2 * Real.pi) * |s.re|) :=
      fun s hs => norm_wC_le (hs.trans hy0)
    have h := latticeI_bound hd (φ := wC) (Cφ := 4 * Real.pi) (κ := 2 * Real.pi) (y1 := y1) (r := r)
      (by positivity) (by positivity) hy1 hr hyr hdiff hb
    have e : ∫ s in (-X)..X, wC (s : ℂ) * (((Int.fract (t s) - 1 / 2 : ℝ)) : ℂ) = ((A2 : ℝ) : ℂ) := by
      rw [hA2, intervalIntegral.integral_ofReal.symm]
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      simp only [wC_real]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  -- cardinality bounds
  have hSc : (S.card : ℝ) ≤ M * (2 * X) + 2 * ε + 1 := by
    have := hd.card_levels_le (a := -X) (b := X) hle le_rfl le_rfl
    have hf : S.filter (fun x => x ∈ Icc (-X) X) = S := Finset.filter_true_of_mem hd.subset_Icc
    rw [hf] at this
    linarith
  have hN0n : N0 ≤ S.card := by
    rw [hN0]; exact_mod_cast Finset.card_filter_le _ _
  have hN00 : 0 ≤ N0 := Nat.cast_nonneg _
  have hfr0 := Int.fract_nonneg (t 0)
  have hfr1 := Int.fract_lt_one (t 0)
  have hE : (∑ x ∈ S, (nuR (2 * Real.pi * x) - if x < 0 then (1 : ℝ) else 0)) -
      ((Int.fract (t 0) - 1 / 2) + Z) =
      A1 - A2 - 2 * νX * (Int.fract (t 0) - 1 / 2) + νX * ((S.card : ℝ) - 2 * N0) := by
    rw [hid]; ring
  rw [hE]
  have b1 : |2 * νX * (Int.fract (t 0) - 1 / 2)| ≤ νX := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * νX)]
    have : |Int.fract (t 0) - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    nlinarith
  have b2 : |νX * ((S.card : ℝ) - 2 * N0)| ≤ νX * S.card := by
    rw [abs_mul, abs_of_nonneg hνX0]
    refine mul_le_mul_of_nonneg_left ?_ hνX0
    rw [abs_le]; constructor <;> nlinarith
  have hcard0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  calc _ ≤ |A1 - A2 - 2 * νX * (Int.fract (t 0) - 1 / 2)| + |νX * ((S.card : ℝ) - 2 * N0)| := abs_add_le _ _
    _ ≤ (|A1| + |A2| + |2 * νX * (Int.fract (t 0) - 1 / 2)|) + νX * S.card := by
        refine add_le_add ?_ b2
        calc |A1 - A2 - 2 * νX * (Int.fract (t 0) - 1 / 2)| ≤ |A1 - A2| + |2 * νX * (Int.fract (t 0) - 1 / 2)| :=
              abs_sub _ _
          _ ≤ (|A1| + |A2|) + |2 * νX * (Int.fract (t 0) - 1 / 2)| := by
              have := abs_sub A1 A2; linarith
    _ ≤ 2 * ε + (_ ) + νX * (M * (2 * X) + 2 * ε + 2) := by
        have : νX * S.card ≤ νX * (M * (2 * X) + 2 * ε + 1) := mul_le_mul_of_nonneg_left hSc hνX0
        nlinarith [hA1b, hA2b, b1]

/-- The two forms of the paper's (iii) from the bound with the integer correction `Z`. -/
lemma offset_of_bound {Sν t0 E : ℝ}
    (h : |Sν - ((Int.fract t0 - 1 / 2) + if Int.fract t0 = 0 then 1 else 0)| ≤ E) :
    (Int.fract t0 ≠ 0 → |Sν - (Int.fract t0 - 1 / 2)| ≤ E) ∧ ∃ m : ℤ, |Sν - t0 + 1 / 2 - m| ≤ E := by
  constructor
  · intro hf
    have h0 : (if Int.fract t0 = 0 then (1 : ℝ) else 0) = 0 := by simp [hf]
    rw [h0, add_zero] at h
    exact h
  · refine ⟨(if Int.fract t0 = 0 then 1 else 0) - ⌊t0⌋, ?_⟩
    have e : Sν - t0 + 1 / 2 - (((if Int.fract t0 = 0 then 1 else 0) - ⌊t0⌋ : ℤ) : ℝ) =
        Sν - ((Int.fract t0 - 1 / 2) + if Int.fract t0 = 0 then 1 else 0) := by
      push_cast
      split_ifs <;> (rw [Int.fract]; ring)
    rw [e]; exact h

/-- info: 'FormalResearch.Special.Lattice.latticeIII_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms latticeIII_bound

end FormalResearch.Special.Lattice
