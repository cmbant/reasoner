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

end FormalResearch.Special.Lattice
