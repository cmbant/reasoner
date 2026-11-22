module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Engine.Corrector

/-!
# Paper J engine, WP0b: compact-interval localisation of `thm:eng-corr`

Source: Paper J `engine.tex`, `thm:eng-corr` on a closed interval `I_u = [a, b]` inside a thickened
domain `I_out = [a - η, b + η]` (`0 < η`), replacing global `ℝ`-uniformity (`UO`, `PApprox`,
`BSmooth`) by interval-localised uniformity (`UOOn`, `PApproxOn`, `BSmoothOn`).

## Design
* `UOOn`, `PApproxOn` are bridged to global `UO`, `PApprox` via zero extension off the interval
  (`restrictFn`), so `PApprox.peel`, `PApprox.lift` and `PApprox.exists_coeff` transfer in a few
  lines with zero duplication of polynomial/parity algebra.
* `BSmoothOn` (`ContDiffOn ℝ N` bridge `bsmoothOn_Icc_of_contDiffOn`) gives local Taylor
  expansions `BSmoothOn.papprox_shift_Icc` on any strictly smaller closed subinterval `[a', b'] ⊆ (L, R)`
  for `|h|` small enough that `u + c * h ∈ [L, R]`.
* Every `dA` / `lA` / `lB` estimate runs on `I_in = [a, b]`; the even flux `F_cas` runs on
  `I_mid = [a - η/2, b + η/2]` so the centred difference `F_cas(u ± h/2)` in the Green identity
  stays inside `I_mid` when `u ∈ I_in` and `|h| < η`.
-/

@[expose] public section

noncomputable section

open Finset Polynomial Set Classical

namespace FormalResearch.JacobiEigenvectors.Engine

/-! ### Localised uniform orders and polynomial expansions via `restrictFn` -/

/-- Zero extension of `f` outside `I`. -/
def restrictFn (I : Set ℝ) (f : ℝ → ℝ → ℝ) (u h : ℝ) : ℝ :=
  if u ∈ I then f u h else 0

/-- `UOOn I n f`: `f(u, h) = O(h^n)` as `h → 0`, uniformly for `u ∈ I`. -/
def UOOn (I : Set ℝ) (n : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ C δ : ℝ, 0 < δ ∧ ∀ u ∈ I, ∀ h : ℝ, |h| < δ → |f u h| ≤ C * |h| ^ n

lemma uoOn_iff_uo {I : Set ℝ} {n : ℕ} {f : ℝ → ℝ → ℝ} :
    UOOn I n f ↔ UO n (restrictFn I f) := by
  constructor
  · rintro ⟨C, δ, hδ, H⟩
    refine ⟨max C 0, δ, hδ, fun u h hh => ?_⟩
    by_cases hu : u ∈ I
    · simp only [restrictFn, hu, ↓reduceIte]
      exact (H u hu h hh).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity))
    · simp only [restrictFn, hu, ↓reduceIte, abs_zero]
      exact mul_nonneg (le_max_right C 0) (by positivity)
  · rintro ⟨C, δ, hδ, H⟩
    refine ⟨C, δ, hδ, fun u hu h hh => ?_⟩
    simpa [restrictFn, hu] using H u h hh

lemma UOOn.norm {I : Set ℝ} {n : ℕ} {f : ℝ → ℝ → ℝ} (hf : UOOn I n f) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ ∀ u ∈ I, ∀ h : ℝ, |h| < δ → |f u h| ≤ C * |h| ^ n := by
  obtain ⟨C, δ, hC, hδ, hδ1, H⟩ := (uoOn_iff_uo.mp hf).norm
  exact ⟨C, δ, hC, hδ, hδ1, fun u hu h hh => by simpa [restrictFn, hu] using H u h hh⟩

lemma UOOn.mono {I : Set ℝ} {n m : ℕ} {f : ℝ → ℝ → ℝ} (hnm : n ≤ m) (hf : UOOn I m f) : UOOn I n f :=
  uoOn_iff_uo.mpr ((uoOn_iff_uo.mp hf).mono hnm)

lemma UOOn.subset {I J : Set ℝ} {n : ℕ} {f : ℝ → ℝ → ℝ} (hIJ : I ⊆ J) (hf : UOOn J n f) : UOOn I n f := by
  obtain ⟨C, δ, hδ, H⟩ := hf
  exact ⟨C, δ, hδ, fun u hu h hh => H u (hIJ hu) h hh⟩

lemma UOOn.zero (I : Set ℝ) (n : ℕ) : UOOn I n (fun _ _ => 0) :=
  ⟨0, 1, one_pos, fun _ _ _ _ => by simp⟩

lemma UOOn.add {I : Set ℝ} {n : ℕ} {f g : ℝ → ℝ → ℝ} (hf : UOOn I n f) (hg : UOOn I n g) :
    UOOn I n (fun u h => f u h + g u h) := by
  refine uoOn_iff_uo.mpr (((uoOn_iff_uo.mp hf).add (uoOn_iff_uo.mp hg)).congr fun u h => ?_)
  by_cases hu : u ∈ I <;> simp [restrictFn, hu]

lemma UOOn.neg {I : Set ℝ} {n : ℕ} {f : ℝ → ℝ → ℝ} (hf : UOOn I n f) :
    UOOn I n (fun u h => -f u h) := by
  refine uoOn_iff_uo.mpr ((uoOn_iff_uo.mp hf).neg.congr fun u h => ?_)
  by_cases hu : u ∈ I <;> simp [restrictFn, hu]

lemma UOOn.sub {I : Set ℝ} {n : ℕ} {f g : ℝ → ℝ → ℝ} (hf : UOOn I n f) (hg : UOOn I n g) :
    UOOn I n (fun u h => f u h - g u h) := by
  refine uoOn_iff_uo.mpr (((uoOn_iff_uo.mp hf).sub (uoOn_iff_uo.mp hg)).congr fun u h => ?_)
  by_cases hu : u ∈ I <;> simp [restrictFn, hu]

lemma UOOn.mul {I : Set ℝ} {n m : ℕ} {f g : ℝ → ℝ → ℝ} (hf : UOOn I n f) (hg : UOOn I m g) :
    UOOn I (n + m) (fun u h => f u h * g u h) := by
  refine uoOn_iff_uo.mpr (((uoOn_iff_uo.mp hf).mul (uoOn_iff_uo.mp hg)).congr fun u h => ?_)
  by_cases hu : u ∈ I <;> simp [restrictFn, hu]

lemma UOOn.hpow (I : Set ℝ) (j : ℕ) : UOOn I j (fun _ h => h ^ j) :=
  ⟨1, 1, one_pos, fun _ _ _ _ => by simp [abs_pow]⟩

lemma UOOn.hpow_mul {I : Set ℝ} {n : ℕ} (j : ℕ) {f : ℝ → ℝ → ℝ} (hf : UOOn I n f) :
    UOOn I (j + n) (fun u h => h ^ j * f u h) :=
  (UOOn.hpow I j).mul hf

lemma UOOn.sum {ι : Type*} (s : Finset ι) {I : Set ℝ} {n : ℕ} {f : ι → ℝ → ℝ → ℝ}
    (hf : ∀ i ∈ s, UOOn I n (f i)) : UOOn I n (fun u h => ∑ i ∈ s, f i u h) := by
  refine uoOn_iff_uo.mpr ((UO.sum s fun i hi => uoOn_iff_uo.mp (hf i hi)).congr fun u h => ?_)
  by_cases hu : u ∈ I <;> simp [restrictFn, hu]

lemma UOOn.congr {I : Set ℝ} {n : ℕ} {f g : ℝ → ℝ → ℝ} (hf : UOOn I n f)
    (hfg : ∀ u ∈ I, ∀ h, f u h = g u h) : UOOn I n g := by
  obtain ⟨C, δ, hδ, H⟩ := hf
  exact ⟨C, δ, hδ, fun u hu h hh => by rw [← hfg u hu h]; exact H u hu h hh⟩

lemma UOOn.congr_loc {I : Set ℝ} {n : ℕ} {f g : ℝ → ℝ → ℝ} (hf : UOOn I n f) {δ0 : ℝ} (hδ0 : 0 < δ0)
    (hfg : ∀ u ∈ I, ∀ h, |h| < δ0 → f u h = g u h) : UOOn I n g := by
  obtain ⟨C, δ, hδ, H⟩ := hf
  refine ⟨C, min δ δ0, lt_min hδ hδ0, fun u hu h hh => ?_⟩
  rw [← hfg u hu h (lt_of_lt_of_le hh (min_le_right _ _))]
  exact H u hu h (lt_of_lt_of_le hh (min_le_left _ _))

lemma UOOn.of_bdd {I : Set ℝ} {f : ℝ → ℝ → ℝ} {C : ℝ} (H : ∀ u ∈ I, ∀ h, |f u h| ≤ C) : UOOn I 0 f :=
  ⟨C, 1, one_pos, fun u hu h _ => by simpa using H u hu h⟩

lemma UOOn.div_of_lower {I : Set ℝ} {n : ℕ} {A f : ℝ → ℝ → ℝ}
    (hA : ∃ m δ : ℝ, 0 < m ∧ 0 < δ ∧ ∀ u ∈ I, ∀ h, |h| < δ → m ≤ |A u h|)
    (hf : UOOn I n (fun u h => A u h * f u h)) : UOOn I n f := by
  obtain ⟨m, δ, hm, hδ, hAm⟩ := hA
  obtain ⟨C, δ', hC, hδ', _, H⟩ := hf.norm
  refine ⟨C / m, min δ δ', lt_min hδ hδ', fun u hu h hh => ?_⟩
  have h1 := hAm u hu h (lt_of_lt_of_le hh (min_le_left _ _))
  have h2 := H u hu h (lt_of_lt_of_le hh (min_le_right _ _))
  rw [abs_mul] at h2
  have : m * |f u h| ≤ C * |h| ^ n :=
    calc m * |f u h| ≤ |A u h| * |f u h| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ _ := h2
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  linarith

lemma UOOn.shift_of_mem {I J : Set ℝ} {n : ℕ} {f : ℝ → ℝ → ℝ} (hf : UOOn J n f) {c δs : ℝ}
    (hδs : 0 < δs) (hsub : ∀ u ∈ I, ∀ h, |h| < δs → u + c * h ∈ J) :
    UOOn I n (fun u h => f (u + c * h) h) := by
  obtain ⟨C, δ, hδ, H⟩ := hf
  refine ⟨C, min δ δs, lt_min hδ hδs, fun u hu h hh => ?_⟩
  exact H (u + c * h) (hsub u hu h (lt_of_lt_of_le hh (min_le_right _ _))) h
    (lt_of_lt_of_le hh (min_le_left _ _))

lemma UOOn.shift_Icc {a b η : ℝ} (hη : 0 < η) {n : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : UOOn (Icc (a - η) (b + η)) n f) (c : ℝ) :
    UOOn (Icc a b) n (fun u h => f (u + c * h) h) := by
  refine hf.shift_of_mem (c := c) (δs := η / (|c| + 1)) (by positivity) fun u hu h hh => ?_
  have hch : |c * h| ≤ η := by
    rw [abs_mul]
    have hc : |c| ≤ |c| + 1 := by linarith
    calc |c| * |h| ≤ (|c| + 1) * |h| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
      _ ≤ (|c| + 1) * (η / (|c| + 1)) := mul_le_mul_of_nonneg_left hh.le (by positivity)
      _ = η := by field_simp
  have h1 : -η ≤ c * h := (abs_le.mp hch).1
  have h2 : c * h ≤ η := (abs_le.mp hch).2
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- `PApproxOn I N f`: uniform polynomial expansion of order `N` in `h` for `u ∈ I`. -/
def PApproxOn (I : Set ℝ) (N : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ (D : ℕ) (C : ℝ) (p : ℝ → Polynomial ℝ), (∀ u ∈ I, (p u).natDegree ≤ D) ∧
    (∀ u ∈ I, ∀ n, |(p u).coeff n| ≤ C) ∧ UOOn I N (fun u h => f u h - (p u).eval h)

private lemma restrictFn_sub_ite {I : Set ℝ} {f : ℝ → ℝ → ℝ} {p : ℝ → Polynomial ℝ} (u h : ℝ) :
    restrictFn I f u h - (if u ∈ I then p u else (0 : Polynomial ℝ)).eval h =
      restrictFn I (fun u h => f u h - (p u).eval h) u h := by
  by_cases hu : u ∈ I <;> simp [restrictFn, hu]

lemma papproxOn_iff_papprox {I : Set ℝ} {N : ℕ} {f : ℝ → ℝ → ℝ} :
    PApproxOn I N f ↔ PApprox N (restrictFn I f) := by
  constructor
  · rintro ⟨D, C, p, hD, hC, hr⟩
    refine ⟨D, max C 0, fun u => if u ∈ I then p u else 0, fun u => ?_, fun u n => ?_, ?_⟩
    · by_cases hu : u ∈ I
      · simp [hu, hD u hu]
      · simp [hu]
    · by_cases hu : u ∈ I
      · simp only [hu, ↓reduceIte]; exact (hC u hu n).trans (le_max_left C 0)
      · simp [hu]
    · exact (uoOn_iff_uo.mp hr).congr fun u h => (restrictFn_sub_ite u h).symm
  · rintro ⟨D, C, p, hD, hC, hr⟩
    refine ⟨D, C, p, fun u _ => hD u, fun u _ n => hC u n, ?_⟩
    obtain ⟨C', δ', hδ', H'⟩ := hr
    refine ⟨C', δ', hδ', fun u hu h hh => ?_⟩
    simpa [restrictFn, hu] using H' u h hh

lemma PApproxOn.bdd {I : Set ℝ} {N : ℕ} {f : ℝ → ℝ → ℝ} (hf : PApproxOn I N f) : UOOn I 0 f :=
  uoOn_iff_uo.mpr (papproxOn_iff_papprox.mp hf).bdd

lemma PApproxOn.bdd' {I : Set ℝ} {N : ℕ} {f : ℝ → ℝ → ℝ} (hf : PApproxOn I N f) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ u ∈ I, ∀ h, |h| < δ → |f u h| ≤ C := by
  obtain ⟨C, δ, hδ, H⟩ := hf.bdd
  exact ⟨C, δ, hδ, fun u hu h hh => by simpa using H u hu h hh⟩

lemma PApproxOn.mono {I : Set ℝ} {N M : ℕ} {f : ℝ → ℝ → ℝ} (hNM : M ≤ N) (hf : PApproxOn I N f) :
    PApproxOn I M f :=
  papproxOn_iff_papprox.mpr ((papproxOn_iff_papprox.mp hf).mono hNM)

lemma PApproxOn.subset {I J : Set ℝ} {N : ℕ} {f : ℝ → ℝ → ℝ} (hIJ : I ⊆ J) (hf : PApproxOn J N f) :
    PApproxOn I N f := by
  obtain ⟨D, C, p, hD, hC, hr⟩ := hf
  exact ⟨D, C, p, fun u hu => hD u (hIJ hu), fun u hu => hC u (hIJ hu), hr.subset hIJ⟩

lemma PApproxOn.congr {I : Set ℝ} {N : ℕ} {f g : ℝ → ℝ → ℝ} (hf : PApproxOn I N f)
    (hfg : ∀ u ∈ I, ∀ h, f u h = g u h) : PApproxOn I N g := by
  obtain ⟨D, C, p, hD, hC, hr⟩ := hf
  exact ⟨D, C, p, hD, hC, hr.congr fun u hu h => by rw [hfg u hu h]⟩

lemma PApproxOn.add {I : Set ℝ} {N : ℕ} {f g : ℝ → ℝ → ℝ} (hf : PApproxOn I N f)
    (hg : PApproxOn I N g) : PApproxOn I N (fun u h => f u h + g u h) := by
  refine papproxOn_iff_papprox.mpr
    (((papproxOn_iff_papprox.mp hf).add (papproxOn_iff_papprox.mp hg)).congr fun u h => ?_)
  by_cases hu : u ∈ I <;> simp [restrictFn, hu]

lemma PApproxOn.sub {I : Set ℝ} {N : ℕ} {f g : ℝ → ℝ → ℝ} (hf : PApproxOn I N f)
    (hg : PApproxOn I N g) : PApproxOn I N (fun u h => f u h - g u h) := by
  refine papproxOn_iff_papprox.mpr
    (((papproxOn_iff_papprox.mp hf).sub (papproxOn_iff_papprox.mp hg)).congr fun u h => ?_)
  by_cases hu : u ∈ I <;> simp [restrictFn, hu]

lemma PApproxOn.mul {I : Set ℝ} {N : ℕ} {f g : ℝ → ℝ → ℝ} (hf : PApproxOn I N f)
    (hg : PApproxOn I N g) : PApproxOn I N (fun u h => f u h * g u h) := by
  refine papproxOn_iff_papprox.mpr
    (((papproxOn_iff_papprox.mp hf).mul (papproxOn_iff_papprox.mp hg)).congr fun u h => ?_)
  by_cases hu : u ∈ I <;> simp [restrictFn, hu]

lemma PApproxOn.sum {ι : Type*} (s : Finset ι) {I : Set ℝ} {N : ℕ} {f : ι → ℝ → ℝ → ℝ}
    (hf : ∀ i ∈ s, PApproxOn I N (f i)) : PApproxOn I N (fun u h => ∑ i ∈ s, f i u h) := by
  refine papproxOn_iff_papprox.mpr
    ((PApprox.sum s fun i hi => papproxOn_iff_papprox.mp (hf i hi)).congr fun u h => ?_)
  by_cases hu : u ∈ I <;> simp [restrictFn, hu]

lemma PApproxOn.of_fun {I : Set ℝ} {N : ℕ} (c : ℝ → ℝ) {C : ℝ} (hc : ∀ x ∈ I, |c x| ≤ C) :
    PApproxOn I N (fun u _ => c u) :=
  ⟨0, C, fun u => Polynomial.C (c u), fun _ _ => by simp, fun u hu n => by
    rcases n with _ | n
    · simpa using hc u hu
    · simp; exact (abs_nonneg _).trans (hc u hu),
    (UOOn.zero I N).congr fun u _ h => by simp⟩

lemma PApproxOn.hpow (I : Set ℝ) {N : ℕ} (j : ℕ) : PApproxOn I N (fun _ h => h ^ j) :=
  ⟨j, 1, fun _ => X ^ j, fun _ _ => natDegree_X_pow_le j,
    fun _ _ n => by simp [coeff_X_pow]; split_ifs <;> norm_num,
    (UOOn.zero I N).congr fun u _ h => by simp⟩

lemma PApproxOn.hpow_mul {I : Set ℝ} {N : ℕ} (j : ℕ) {f : ℝ → ℝ → ℝ} (hf : PApproxOn I N f) :
    PApproxOn I N (fun u h => h ^ j * f u h) :=
  (PApproxOn.hpow I j).mul hf

lemma PApproxOn.order1 {I : Set ℝ} {f : ℝ → ℝ → ℝ} (hf : PApproxOn I 1 f) :
    UOOn I 1 (fun u h => f u h - f u 0) := by
  refine uoOn_iff_uo.mpr ((papproxOn_iff_papprox.mp hf).order1.congr fun u h => ?_)
  by_cases hu : u ∈ I <;> simp [restrictFn, hu]

lemma PApproxOn.lift {I : Set ℝ} {n : ℕ} {σ δ0 : ℝ} (hσ : σ * (-1) ^ n = -1) {f : ℝ → ℝ → ℝ}
    (hf : PApproxOn I (n + 1) f) (h0 : UOOn I n f) (hδ0 : 0 < δ0)
    (hpar : ∀ u ∈ I, ∀ h, |h| < δ0 → f u (-h) = σ * f u h) : UOOn I (n + 1) f := by
  refine uoOn_iff_uo.mpr (PApprox.lift hσ (papproxOn_iff_papprox.mp hf) (uoOn_iff_uo.mp h0) hδ0 ?_)
  intro u h hh
  by_cases hu : u ∈ I
  · simp [restrictFn, hu, hpar u hu h hh]
  · simp [restrictFn, hu]

lemma PApproxOn.exists_coeff {I : Set ℝ} {n : ℕ} {σ δ0 : ℝ} (hσ : σ * (-1) ^ n = 1) {f : ℝ → ℝ → ℝ}
    (hf : PApproxOn I (n + 2) f) (h0 : UOOn I n f) (hδ0 : 0 < δ0)
    (hpar : ∀ u ∈ I, ∀ h, |h| < δ0 → f u (-h) = σ * f u h) :
    ∃ a : ℝ → ℝ, (∃ C, ∀ u ∈ I, |a u| ≤ C) ∧ UOOn I (n + 2) (fun u h => f u h - h ^ n * a u) := by
  have h1 := PApprox.exists_coeff hσ (papproxOn_iff_papprox.mp hf) (uoOn_iff_uo.mp h0) hδ0 (fun u h hh => by
    by_cases hu : u ∈ I
    · simp [restrictFn, hu, hpar u hu h hh]
    · simp [restrictFn, hu])
  obtain ⟨a, ⟨Ca, hCa⟩, C', δ', hδ', H'⟩ := h1
  refine ⟨a, ⟨Ca, fun u _ => hCa u⟩, C', δ', hδ', fun u hu h hh => ?_⟩
  simpa [restrictFn, hu] using H' u h hh

/-! ### Smoothness and Taylor expansions on intervals -/

/-- `BSmoothOn I N g`: `g` is `N` times differentiable on `I` and `g, g', ..., g^{(N)}` are bounded on `I`. -/
def BSmoothOn (I : Set ℝ) : ℕ → (ℝ → ℝ) → Prop
  | 0, g => ∃ C, ∀ x ∈ I, |g x| ≤ C
  | N + 1, g => (∃ C, ∀ x ∈ I, |g x| ≤ C) ∧ (∀ x ∈ I, DifferentiableAt ℝ g x) ∧ BSmoothOn I N (deriv g)

lemma BSmoothOn.bdd : ∀ {I : Set ℝ} {N : ℕ} {g : ℝ → ℝ}, BSmoothOn I N g → ∃ C, ∀ x ∈ I, |g x| ≤ C
  | _, 0, _, h => h
  | _, _ + 1, _, h => h.1

lemma BSmoothOn.d {I : Set ℝ} {N : ℕ} {g : ℝ → ℝ} (h : BSmoothOn I (N + 1) g) :
    BSmoothOn I N (deriv g) := h.2.2

lemma BSmoothOn.diff {I : Set ℝ} {N : ℕ} {g : ℝ → ℝ} (h : BSmoothOn I (N + 1) g) :
    ∀ x ∈ I, DifferentiableAt ℝ g x := h.2.1

lemma BSmoothOn.mono : ∀ {I : Set ℝ} {N M : ℕ} {g : ℝ → ℝ}, M ≤ N → BSmoothOn I N g → BSmoothOn I M g
  | _, _, 0, _, _, h => h.bdd
  | _, 0, _ + 1, _, hM, _ => absurd hM (by omega)
  | _, _ + 1, _ + 1, _, hM, h => ⟨h.1, h.2.1, BSmoothOn.mono (by omega) h.2.2⟩

lemma BSmoothOn.subset : ∀ {I J : Set ℝ} {N : ℕ} {g : ℝ → ℝ}, I ⊆ J → BSmoothOn J N g → BSmoothOn I N g
  | _, _, 0, _, hIJ, ⟨C, hC⟩ => ⟨C, fun x hx => hC x (hIJ hx)⟩
  | _, _, _N + 1, _, hIJ, ⟨⟨C, hC⟩, hd, hnext⟩ =>
      ⟨⟨C, fun x hx => hC x (hIJ hx)⟩, fun x hx => hd x (hIJ hx), hnext.subset hIJ⟩

lemma BSmoothOn.iter_bdd : ∀ {I : Set ℝ} {N : ℕ} {g : ℝ → ℝ}, BSmoothOn I N g →
    ∃ C, 0 ≤ C ∧ ∀ n ≤ N, ∀ x ∈ I, |deriv^[n] g x| ≤ C
  | _, 0, _, h => by
      obtain ⟨C, hC⟩ := h
      refine ⟨|C|, abs_nonneg _, fun n hn x hx => ?_⟩
      have : n = 0 := by omega
      subst this
      exact (hC x hx).trans (le_abs_self C)
  | I, N + 1, g, h => by
      obtain ⟨C0, hC0⟩ := h.bdd
      obtain ⟨C1, _, H1⟩ := h.d.iter_bdd
      refine ⟨max |C0| C1, le_max_of_le_left (abs_nonneg _), fun n hn x hx => ?_⟩
      rcases n with _ | n
      · exact ((hC0 x hx).trans (le_abs_self C0)).trans (le_max_left _ _)
      · rw [Function.iterate_succ_apply]
        exact (H1 n (by omega) x hx).trans (le_max_right _ _)

/-- Bridge from `ContDiffOn ℝ N g (Ioo A B)` to `BSmoothOn (Icc a b) N g` for `[a, b] ⊆ (A, B)`. -/
theorem bsmoothOn_Icc_of_contDiffOn_Ioo (N : ℕ) {A B a b : ℝ} (ha : A < a) (_hab : a ≤ b) (hb : b < B)
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ N g (Ioo A B)) : BSmoothOn (Icc a b) N g := by
  induction N generalizing g with
  | zero =>
      have hsub : Icc a b ⊆ Ioo A B := fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn.mono hsub)
      exact ⟨C, fun x hx => by simpa using hC x hx⟩
  | succ N ih =>
      have hsub : Icc a b ⊆ Ioo A B := fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn.mono hsub)
      have hdiff : DifferentiableOn ℝ g (Ioo A B) := hg.differentiableOn (by simp)
      have hd : ∀ x ∈ Icc a b, DifferentiableAt ℝ g x := fun x hx =>
        hdiff.differentiableAt (isOpen_Ioo.mem_nhds (hsub hx))
      have hcd : ContDiffOn ℝ N (deriv g) (Ioo A B) :=
        hg.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact ⟨⟨C, fun x hx => by simpa using hC x hx⟩, hd, ih hcd⟩

lemma bsmoothOn_of_contDiffOn {N : ℕ} {A B a b : ℝ} (ha : A < a) (hab : a ≤ b) (hb : b < B)
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ N g (Icc A B)) : BSmoothOn (Icc a b) N g :=
  bsmoothOn_Icc_of_contDiffOn_Ioo N ha hab hb (hg.mono Ioo_subset_Icc_self)

/-- Taylor's formula with uniform remainder on a thickened closed interval `[L, R] ⊃ [a', b']`. -/
lemma BSmoothOn.taylor_Icc : ∀ {N : ℕ} {L R a' b' : ℝ} (_hL : L < a') (_hR : b' < R) {g : ℝ → ℝ},
    BSmoothOn (Icc L R) N g →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Icc a' b', ∀ t : ℝ, |t| ≤ min (a' - L) (R - b') →
      |g (u + t) - tay g N u t| ≤ C * |t| ^ N
  | 0, L, R, a', b', hL, hR, g, hg => by
      obtain ⟨C, hC⟩ := hg
      refine ⟨|C|, abs_nonneg _, fun u hu t ht => ?_⟩
      have h1 : |t| ≤ a' - L := ht.trans (min_le_left _ _)
      have h2 : |t| ≤ R - b' := ht.trans (min_le_right _ _)
      have hus : u + t ∈ Icc L R :=
        ⟨by linarith [hu.1, (abs_le.mp h1).1], by linarith [hu.2, (abs_le.mp h2).2]⟩
      simpa [tay] using (hC (u + t) hus).trans (le_abs_self C)
  | N + 1, L, R, a', b', hL, hR, g, hg => by
      obtain ⟨C, hC0, hC⟩ := BSmoothOn.taylor_Icc hL hR hg.d
      refine ⟨C, hC0, fun u hu t ht => ?_⟩
      set ψ : ℝ → ℝ := fun s => g (u + s) - tay g (N + 1) u s with hψ
      have hus_mem : ∀ s, |s| ≤ |t| → u + s ∈ Icc L R := by
        intro s hs
        have hst := hs.trans ht
        have h1 : -(a' - L) ≤ s := (abs_le.mp (hst.trans (min_le_left _ _))).1
        have h2 : s ≤ R - b' := (abs_le.mp (hst.trans (min_le_right _ _))).2
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hψd : ∀ s, |s| ≤ |t| → HasDerivAt ψ (deriv g (u + s) - tay (deriv g) N u s) s := by
        intro s hs
        have h1 : HasDerivAt (fun s => g (u + s)) (deriv g (u + s)) s :=
          (hg.diff (u + s) (hus_mem s hs)).hasDerivAt.comp_const_add u s
        exact h1.sub (tay_hasDerivAt g N u s)
      have hbound : ∀ s ∈ Metric.closedBall (0 : ℝ) |t|, ‖deriv ψ s‖ ≤ C * |t| ^ N := by
        intro s hs
        have hs' : |s| ≤ |t| := by simpa [Metric.mem_closedBall, dist_zero_right] using hs
        rw [(hψd s hs').deriv, Real.norm_eq_abs]
        calc |deriv g (u + s) - tay (deriv g) N u s| ≤ C * |s| ^ N :=
              hC u hu s (hs'.trans ht)
          _ ≤ C * |t| ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hs' N) hC0
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := ψ) (s := Metric.closedBall (0 : ℝ) |t|)
        (fun s hs => (hψd s (by simpa [Metric.mem_closedBall, dist_zero_right] using hs)).differentiableAt)
        hbound (convex_closedBall _ _)
        (Metric.mem_closedBall_self (abs_nonneg t))
        (show t ∈ Metric.closedBall (0 : ℝ) |t| by simp [Metric.mem_closedBall, dist_zero_right])
      have h0 : ψ 0 = 0 := by simp [hψ, tay, Finset.sum_range_succ', zero_pow]
      simp only [Real.norm_eq_abs, h0, sub_zero] at hmv
      calc |g (u + t) - tay g (N + 1) u t| = |ψ t| := rfl
        _ ≤ C * |t| ^ N * |t| := hmv
        _ = C * |t| ^ (N + 1) := by ring

lemma BSmoothOn.order1_Icc {L R a' b' : ℝ} (hL : L < a') (hR : b' < R) {g : ℝ → ℝ}
    (hg : BSmoothOn (Icc L R) 2 g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Icc a' b', ∀ t : ℝ, |t| ≤ min (a' - L) (R - b') →
      |g (u + t) - g u - t * deriv g u| ≤ C * t ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := BSmoothOn.taylor_Icc (N := 2) hL hR hg
  refine ⟨C, hC0, fun u hu t ht => ?_⟩
  have h1 := hC u hu t ht
  have e : tay g 2 u t = g u + t * deriv g u := by
    simp [tay, Finset.sum_range_succ]
    ring
  rw [e, sq_abs] at h1
  have e2 : g (u + t) - g u - t * deriv g u = g (u + t) - (g u + t * deriv g u) := by ring
  rw [e2]; simpa [sq_abs] using h1

lemma BSmoothOn.uo_shift_order1_Icc {L R a' b' : ℝ} (hL : L < a') (hR : b' < R) {g : ℝ → ℝ}
    (hg : BSmoothOn (Icc L R) 2 g) (c : ℝ) {σ : ℝ → ℝ → ℝ} (hσ : ∀ u h, σ u h = u + c * h) :
    UOOn (Icc a' b') 2 (fun u h => g (σ u h) - g u - (c * h) * deriv g u) := by
  obtain ⟨C, _, hC⟩ := BSmoothOn.order1_Icc hL hR hg
  set δm := min (a' - L) (R - b') with hδm
  have hδm_pos : 0 < δm := lt_min (by linarith) (by linarith)
  refine ⟨C * c ^ 2, δm / (|c| + 1), by positivity, fun u hu h hh => ?_⟩
  have hch : |c * h| ≤ δm := by
    rw [abs_mul]
    calc |c| * |h| ≤ (|c| + 1) * |h| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ (|c| + 1) * (δm / (|c| + 1)) := mul_le_mul_of_nonneg_left hh.le (by positivity)
      _ = δm := by field_simp
  show |g (σ u h) - g u - c * h * deriv g u| ≤ _
  rw [hσ]
  calc |g (u + c * h) - g u - c * h * deriv g u| ≤ C * (c * h) ^ 2 := hC u hu (c * h) hch
    _ = C * c ^ 2 * |h| ^ 2 := by rw [mul_pow, ← sq_abs h]; ring

lemma BSmoothOn.papprox_shift_Icc {L R a' b' : ℝ} (hL : L < a') (hR : b' < R) {N : ℕ} {g : ℝ → ℝ}
    (hg : BSmoothOn (Icc L R) N g) (c : ℝ) :
    PApproxOn (Icc a' b') N (fun u h => g (u + c * h)) := by
  have hsub : Icc a' b' ⊆ Icc L R := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨Cd, _, hCd⟩ := (hg.subset hsub).iter_bdd
  obtain ⟨Ct, _, hCt⟩ := BSmoothOn.taylor_Icc hL hR hg
  set δm := min (a' - L) (R - b')
  have hδm_pos : 0 < δm := lt_min (by linarith) (by linarith)
  let coeff : ℕ → ℝ → ℝ := fun n u => c ^ n * (deriv^[n] g u / (n.factorial : ℝ))
  let p : ℝ → Polynomial ℝ := fun u => ∑ n ∈ range N, Polynomial.C (coeff n u) * X ^ n
  have hdeg : ∀ u ∈ Icc a' b', (p u).natDegree ≤ N := fun u _ => by
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    refine Finset.sup_le fun n hn => ?_
    calc (Polynomial.C (coeff n u) * X ^ n).natDegree
        ≤ (Polynomial.C (coeff n u)).natDegree + (X ^ n).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 0 + n := add_le_add (natDegree_C _).le (natDegree_X_pow_le n)
      _ ≤ N := by have := Finset.mem_range.mp hn; omega
  have hcb : ∀ u ∈ Icc a' b', ∀ n, |(p u).coeff n| ≤ (1 + |c|) ^ N * Cd := fun u hu n => by
    simp only [p, finsetSum_coeff, coeff_C_mul_X_pow]
    by_cases hn : n < N
    · rw [Finset.sum_eq_single n]
      · simp only [↓reduceIte, coeff]
        have h1 := hCd n hn.le u hu
        have hf : (1 : ℝ) ≤ n.factorial := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
        have h2 : |deriv^[n] g u / (n.factorial : ℝ)| ≤ Cd := by
          rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < n.factorial)]
          calc |deriv^[n] g u| / n.factorial ≤ |deriv^[n] g u| / 1 :=
                div_le_div_of_nonneg_left (abs_nonneg _) one_pos hf
            _ ≤ Cd := by simpa using h1
        have h3 : |c| ^ n ≤ (1 + |c|) ^ N := by
          calc |c| ^ n ≤ (1 + |c|) ^ n := pow_le_pow_left₀ (abs_nonneg _) (by linarith) n
            _ ≤ (1 + |c|) ^ N := pow_le_pow_right₀ (by linarith [abs_nonneg c]) hn.le
        rw [abs_mul, abs_pow]
        exact mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
      · intro k _ hkn; simp [hkn.symm]
      · intro hn'; exact absurd (Finset.mem_range.mpr hn) hn'
    · rw [Finset.sum_eq_zero]
      · simp only [abs_zero]; positivity
      · intro k hk
        have hkn : k ≠ n := by have := Finset.mem_range.mp hk; omega
        simp [hkn.symm]
  refine ⟨N, (1 + |c|) ^ N * Cd, p, hdeg, hcb, Ct * |c| ^ N, δm / (|c| + 1), by positivity, ?_⟩
  intro u hu h hh
  have hch : |c * h| ≤ δm := by
    rw [abs_mul]
    calc |c| * |h| ≤ (|c| + 1) * |h| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ (|c| + 1) * (δm / (|c| + 1)) := mul_le_mul_of_nonneg_left hh.le (by positivity)
      _ = δm := by field_simp
  have hpe : (p u).eval h = tay g N u (c * h) := by
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, coeff, tay]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_pow]; ring
  change |g (u + c * h) - (p u).eval h| ≤ _
  rw [hpe]
  calc |g (u + c * h) - tay g N u (c * h)| ≤ Ct * |c * h| ^ N := hCt u hu (c * h) hch
    _ = Ct * |c| ^ N * |h| ^ N := by rw [abs_mul, mul_pow]; ring

lemma BSmoothOn.papprox_shift_Icc' {L R a' b' : ℝ} (hL : L < a') (hR : b' < R) {N : ℕ}
    {g : ℝ → ℝ} (hg : BSmoothOn (Icc L R) N g) (c : ℝ) {σ : ℝ → ℝ → ℝ}
    (hσ : ∀ u h, σ u h = u + c * h) : PApproxOn (Icc a' b') N (fun u h => g (σ u h)) :=
  (BSmoothOn.papprox_shift_Icc hL hR hg c).congr fun u _ h => by rw [hσ]

/-! ### Local analytic inputs and operators -/

/-- Localised `SymbolExp` on `I`. -/
structure SymbolExpOn (I : Set ℝ) (N : ℕ) (pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2) : Prop where
  sP : ∀ i j, PApproxOn I N (fun u h => pp (u + h / 2) h * PiP u h i j)
  sM : ∀ i j, PApproxOn I N (fun u h => pp (u - h / 2) h * PiM u h i j)
  qe : PApproxOn I N qq
  cM : ∀ i j, PApproxOn I N (fun s h => pp s h * PiM (s + h / 2) h i j)
  bddP : ∀ i j, UOOn I 0 (fun u h => PiP u h i j)
  bddM : ∀ i j, UOOn I 0 (fun u h => PiM u h i j)

lemma SymbolExpOn.subset {I J : Set ℝ} {N : ℕ} {pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2}
    (hIJ : I ⊆ J) (h : SymbolExpOn J N pp qq PiP PiM) : SymbolExpOn I N pp qq PiP PiM where
  sP i j := (h.sP i j).subset hIJ
  sM i j := (h.sM i j).subset hIJ
  qe := h.qe.subset hIJ
  cM i j := (h.cM i j).subset hIJ
  bddP i j := (h.bddP i j).subset hIJ
  bddM i j := (h.bddM i j).subset hIJ

lemma Aans_papprox_Icc {L R a' b' : ℝ} (hL : L < a') (hR : b' < R) {N k : ℕ} {g : ℕ → ℝ → ℝ}
    (hg : ∀ i < k, BSmoothOn (Icc L R) N (g i)) (c : ℝ) {σ : ℝ → ℝ → ℝ}
    (hσ : ∀ u h, σ u h = u + c * h) : PApproxOn (Icc a' b') N (fun u h => Aans g k (σ u h) h) := by
  unfold Aans
  refine PApproxOn.sum (range k) fun i hi => ?_
  have hgi := BSmoothOn.papprox_shift_Icc' hL hR (hg i (Finset.mem_range.mp hi)) c hσ
  exact PApproxOn.hpow_mul (2 * i) hgi

lemma Bans_papprox_Icc {L R a' b' : ℝ} (hL : L < a') (hR : b' < R) {N l : ℕ} {b : ℕ → ℝ → ℝ}
    (hb : ∀ i, 1 ≤ i → i ≤ l → BSmoothOn (Icc L R) N (b i)) (c : ℝ) {σ : ℝ → ℝ → ℝ}
    (hσ : ∀ u h, σ u h = u + c * h) : PApproxOn (Icc a' b') N (fun u h => Bans b l (σ u h) h) := by
  unfold Bans
  refine PApproxOn.sum (range l) fun i hi => ?_
  have hbi := BSmoothOn.papprox_shift_Icc' hL hR
    (hb (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega)) c hσ
  exact PApproxOn.hpow_mul (2 * i) hbi

lemma uoOn1_of_zero {I : Set ℝ} {f : ℝ → ℝ → ℝ} (hf : PApproxOn I 1 f) (h0 : ∀ u ∈ I, f u 0 = 0) :
    UOOn I 1 f :=
  hf.order1.congr fun u hu h => by rw [h0 u hu, sub_zero]

lemma lA_UO2_local {a b η : ℝ} (hη : 0 < η) {N : ℕ} (hN : 2 ≤ N)
    {pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2}
    (hS : SymbolExpOn (Icc a b) N pp qq PiP PiM)
    (hpar : ∀ u h, PiP u (-h) = Sg * PiM u h * Sg)
    (hP : ∀ s h, pp s (-h) = pp s h) (hQ : ∀ u h, qq u (-h) = qq u h)
    (hlang : ∀ u ∈ Icc a b, pp u 0 * (PiP u 0 0 0 + PiM u 0 0 0) = qq u 0)
    {g : ℝ → ℝ} (hg : BSmoothOn (Icc (a - η) (b + η)) 2 g) :
    UOOn (Icc a b) 2 (lA pp qq PiP PiM g) := by
  have hla : ∀ u ∈ Icc a b, lA pp qq PiP PiM g u 0 = 0 := fun u hu => by
    simp only [lA, zero_div, add_zero, sub_zero]
    linear_combination g u * hlang u hu
  have gp := BSmoothOn.papprox_shift_Icc' (L := a - η) (R := b + η) (a' := a) (b' := b)
    (by linarith [hη]) (by linarith [hη]) hg 1 (σ := fun u h => u + h) (fun _ _ => by ring)
  have gm := BSmoothOn.papprox_shift_Icc' (L := a - η) (R := b + η) (a' := a) (b' := b)
    (by linarith [hη]) (by linarith [hη]) hg (-1) (σ := fun u h => u - h) (fun _ _ => by ring)
  have g0 := BSmoothOn.papprox_shift_Icc' (L := a - η) (R := b + η) (a' := a) (b' := b)
    (by linarith [hη]) (by linarith [hη]) hg 0 (σ := fun u _ => u) (fun _ _ => by ring)
  have hpa : PApproxOn (Icc a b) 2 (lA pp qq PiP PiM g) := by
    unfold lA
    exact ((((hS.sP 0 0).mono hN).mul gp).add (((hS.sM 0 0).mono hN).mul gm)).sub
      ((hS.qe.mono hN).mul g0)
  have h1 : UOOn (Icc a b) 1 (lA pp qq PiP PiM g) := uoOn1_of_zero (hpa.mono (by norm_num)) hla
  exact PApproxOn.lift (n := 1) (σ := 1) (δ0 := 1) (by norm_num) hpa h1 one_pos
    (fun u _ h _ => by rw [one_mul]; exact lA_even_of_par hpar hP hQ g u h)

lemma Mdev_local {I : Set ℝ} {N : ℕ} (hN : 2 ≤ N)
    {pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2} (hS : SymbolExpOn I N pp qq PiP PiM)
    (hpar : ∀ u h, PiP u (-h) = Sg * PiM u h * Sg)
    (hadj : ∀ u h, PiP u h = Matrix.adjugate (PiM (u + h) h))
    (hP : ∀ s h, pp s (-h) = pp s h) :
    UOOn I 2 (fun s h => Mfun pp PiM s h - M0fun pp PiM s) := by
  have hf : PApproxOn I 2 (Mfun pp PiM) := (hS.cM 1 0).mono hN
  have hval : ∀ s, Mfun pp PiM s 0 = M0fun pp PiM s := fun s => by simp [Mfun, M0fun]
  obtain ⟨C, δ, hδ, hb⟩ := hf.bdd'
  have hg : PApproxOn I 2 (fun s h => Mfun pp PiM s h - M0fun pp PiM s) :=
    hf.sub (PApproxOn.of_fun (M0fun pp PiM) (C := C) fun s hs => by
      have := hb s hs 0 (by simpa using hδ)
      rwa [hval] at this)
  have h1 : UOOn I 1 (fun s h => Mfun pp PiM s h - M0fun pp PiM s) := by
    have := (hf.mono (by norm_num : 1 ≤ 2)).order1
    exact this.congr fun s _ h => by simp [hval]
  exact PApproxOn.lift (n := 1) (σ := 1) (δ0 := 1) (by norm_num) hg h1 one_pos
    (fun s _ h _ => by
      simp [Mfun_even_of_adj hpar hP s h (by have := hadj (s - h / 2) h; rwa [show s - h / 2 + h = s + h / 2 by ring] at this)])

lemma transportOp_bdd_on {I : Set ℝ} {M0 b : ℝ → ℝ} (hM0 : BSmoothOn I 1 M0) (hb : BSmoothOn I 1 b) :
    ∃ C, ∀ x ∈ I, |transportOp M0 b x| ≤ C := by
  obtain ⟨Cm, hCm⟩ := hM0.bdd
  obtain ⟨Cm', hCm'⟩ := hM0.d.bdd
  obtain ⟨Cb, hCb⟩ := hb.bdd
  obtain ⟨Cb', hCb'⟩ := hb.d.bdd
  refine ⟨2 * |Cm| * |Cb'| + |Cm'| * |Cb|, fun x hx => ?_⟩
  unfold transportOp
  rw [abs_neg]
  have a1 : |M0 x| ≤ |Cm| := (hCm x hx).trans (le_abs_self Cm)
  have a2 : |deriv b x| ≤ |Cb'| := (hCb' x hx).trans (le_abs_self Cb')
  have a3 : |deriv M0 x| ≤ |Cm'| := (hCm' x hx).trans (le_abs_self Cm')
  have a4 : |b x| ≤ |Cb| := (hCb x hx).trans (le_abs_self Cb)
  have t1 : |2 * M0 x * deriv b x| ≤ 2 * |Cm| * |Cb'| := by
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_mul (mul_le_mul_of_nonneg_left a1 (by norm_num)) a2 (abs_nonneg _) (by positivity)
  have t2 : |deriv M0 x * b x| ≤ |Cm'| * |Cb| := by
    rw [abs_mul]
    exact mul_le_mul a3 a4 (abs_nonneg _) (abs_nonneg _)
  exact (abs_add_le _ _).trans (add_le_add t1 t2)

lemma lB_UO3_local {a b η : ℝ} (hη : 0 < η) {N : ℕ} (hN : 3 ≤ N)
    {pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2}
    (hS : SymbolExpOn (Icc (a - η) (b + η)) N pp qq PiP PiM)
    (hpar : ∀ u h, PiP u (-h) = Sg * PiM u h * Sg)
    (hadj : ∀ u h, PiP u h = Matrix.adjugate (PiM (u + h) h))
    (hP : ∀ s h, pp s (-h) = pp s h)
    (hM0 : BSmoothOn (Icc (a - η) (b + η)) 2 (M0fun pp PiM))
    {b_fn : ℝ → ℝ} (hb : BSmoothOn (Icc (a - η) (b + η)) 3 b_fn) :
    UOOn (Icc a b) 3 (fun u h => lB pp PiP PiM b_fn u h - h * transportOp (M0fun pp PiM) b_fn u) := by
  have hIm : Icc (a - η / 2) (b + η / 2) ⊆ Icc (a - η) (b + η) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hIi : Icc a b ⊆ Icc (a - η) (b + η) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hMd := Mdev_local (by omega : 2 ≤ N) (hS.subset hIm) hpar hadj hP
  have hb2 : BSmoothOn (Icc (a - η) (b + η)) 2 b_fn := hb.mono (by norm_num)
  have εp : UOOn (Icc a b) 2 (fun u h => Mfun pp PiM (u + h / 2) h - M0fun pp PiM (u + h / 2)) :=
    (hMd.shift_Icc (by positivity) (1 / 2)).congr fun u _ h => by simp only [one_div]; ring_nf
  have εm : UOOn (Icc a b) 2 (fun u h => Mfun pp PiM (u - h / 2) h - M0fun pp PiM (u - h / 2)) :=
    (hMd.shift_Icc (by positivity) (-1 / 2)).congr fun u _ h => by ring_nf
  have emp := BSmoothOn.uo_shift_order1_Icc (L := a - η) (R := b + η) (a' := a) (b' := b)
    (by linarith [hη]) (by linarith [hη]) hM0 (1 / 2) (σ := fun u h => u + h / 2) (fun u h => by ring)
  have emm := BSmoothOn.uo_shift_order1_Icc (L := a - η) (R := b + η) (a' := a) (b' := b)
    (by linarith [hη]) (by linarith [hη]) hM0 (-1 / 2) (σ := fun u h => u - h / 2) (fun u h => by ring)
  have ebp := BSmoothOn.uo_shift_order1_Icc (L := a - η) (R := b + η) (a' := a) (b' := b)
    (by linarith [hη]) (by linarith [hη]) hb2 1 (σ := fun u h => u + h) (fun u h => by ring)
  have ebm := BSmoothOn.uo_shift_order1_Icc (L := a - η) (R := b + η) (a' := a) (b' := b)
    (by linarith [hη]) (by linarith [hη]) hb2 (-1) (σ := fun u h => u - h) (fun u h => by ring)
  obtain ⟨Cb, hCb⟩ := (hb.subset hIi).bdd
  obtain ⟨Cb', hCb'⟩ := (hb.subset hIi).d.bdd
  obtain ⟨Cm, hCm⟩ := (hM0.subset hIi).bdd
  obtain ⟨Cm', hCm'⟩ := (hM0.subset hIi).d.bdd
  have βp : UOOn (Icc a b) 0 (fun u h => b_fn (u + h)) := by
    obtain ⟨C, hC⟩ := (hb.subset hIm).bdd
    refine ⟨C, η / 2, by positivity, fun u hu h hh => ?_⟩
    have hmem : u + h ∈ Icc (a - η / 2) (b + η / 2) :=
      ⟨by linarith [hu.1, (abs_lt.mp hh).1], by linarith [hu.2, (abs_lt.mp hh).2]⟩
    simpa using hC (u + h) hmem
  have βm : UOOn (Icc a b) 0 (fun u h => b_fn (u - h)) := by
    obtain ⟨C, hC⟩ := (hb.subset hIm).bdd
    refine ⟨C, η / 2, by positivity, fun u hu h hh => ?_⟩
    have hmem : u - h ∈ Icc (a - η / 2) (b + η / 2) :=
      ⟨by linarith [hu.1, (abs_lt.mp hh).2], by linarith [hu.2, (abs_lt.mp hh).1]⟩
    simpa using hC (u - h) hmem
  have b0 : UOOn (Icc a b) 0 (fun u (_ : ℝ) => b_fn u) := UOOn.of_bdd fun u hu _ => hCb u hu
  have b1 : UOOn (Icc a b) 0 (fun u (_ : ℝ) => deriv b_fn u) := UOOn.of_bdd fun u hu _ => hCb' u hu
  have μ0 : UOOn (Icc a b) 0 (fun u (_ : ℝ) => M0fun pp PiM u) := UOOn.of_bdd fun u hu _ => hCm u hu
  have μ1 : UOOn (Icc a b) 0 (fun u (_ : ℝ) => deriv (M0fun pp PiM) u / 2) :=
    UOOn.of_bdd fun x hx _ => by
      rw [abs_div, abs_two]
      exact (div_le_self (abs_nonneg _) (by norm_num)).trans ((hCm' x hx).trans (le_abs_self Cm'))
  have T1 := (εp.mul βp).mono (by norm_num : 2 ≤ 2 + 0)
  have T2 := (εm.mul βm).mono (by norm_num : 2 ≤ 2 + 0)
  have T3 := (μ0.mul (ebm.sub ebp)).mono (by norm_num : 2 ≤ 0 + 2)
  have T4 := (UOOn.hpow_mul 1 (μ1.mul (ebp.add ebm))).mono (by norm_num : 2 ≤ 1 + (0 + 2))
  have T5 := (b0.mul (emm.sub emp)).mono (by norm_num : 2 ≤ 0 + 2)
  have T6 := (UOOn.hpow_mul 1 (b1.mul (emp.add emm))).mono (by norm_num : 2 ≤ 1 + (0 + 2))
  have T7 := (emm.mul ebm).mono (by norm_num : 2 ≤ 2 + 2)
  have T8 := (emp.mul ebp).mono (by norm_num : 2 ≤ 2 + 2)
  have key : UOOn (Icc a b) 2 (fun u h =>
      -((Mfun pp PiM (u + h / 2) h - M0fun pp PiM (u + h / 2)) * b_fn (u + h))
      + (Mfun pp PiM (u - h / 2) h - M0fun pp PiM (u - h / 2)) * b_fn (u - h)
      + M0fun pp PiM u * ((b_fn (u - h) - b_fn u - (-1 * h) * deriv b_fn u) - (b_fn (u + h) - b_fn u - (1 * h) * deriv b_fn u))
      - h * (deriv (M0fun pp PiM) u / 2 * ((b_fn (u + h) - b_fn u - (1 * h) * deriv b_fn u)
          + (b_fn (u - h) - b_fn u - (-1 * h) * deriv b_fn u)))
      + b_fn u * ((M0fun pp PiM (u - h / 2) - M0fun pp PiM u - (-1 / 2 * h) * deriv (M0fun pp PiM) u)
          - (M0fun pp PiM (u + h / 2) - M0fun pp PiM u - (1 / 2 * h) * deriv (M0fun pp PiM) u))
      - h * (deriv b_fn u * ((M0fun pp PiM (u + h / 2) - M0fun pp PiM u - (1 / 2 * h) * deriv (M0fun pp PiM) u)
          + (M0fun pp PiM (u - h / 2) - M0fun pp PiM u - (-1 / 2 * h) * deriv (M0fun pp PiM) u)))
      + (M0fun pp PiM (u - h / 2) - M0fun pp PiM u - (-1 / 2 * h) * deriv (M0fun pp PiM) u)
          * (b_fn (u - h) - b_fn u - (-1 * h) * deriv b_fn u)
      - (M0fun pp PiM (u + h / 2) - M0fun pp PiM u - (1 / 2 * h) * deriv (M0fun pp PiM) u)
          * (b_fn (u + h) - b_fn u - (1 * h) * deriv b_fn u)) := by
    have h4 : UOOn (Icc a b) 2 (fun u h =>
        h ^ 1 * (deriv (M0fun pp PiM) u / 2 * ((b_fn (u + h) - b_fn u - (1 * h) * deriv b_fn u)
          + (b_fn (u - h) - b_fn u - (-1 * h) * deriv b_fn u)))) := T4
    have h6 : UOOn (Icc a b) 2 (fun u h =>
        h ^ 1 * (deriv b_fn u * ((M0fun pp PiM (u + h / 2) - M0fun pp PiM u - (1 / 2 * h) * deriv (M0fun pp PiM) u)
          + (M0fun pp PiM (u - h / 2) - M0fun pp PiM u - (-1 / 2 * h) * deriv (M0fun pp PiM) u)))) := T6
    refine ((((((T1.neg.add T2).add T3).sub h4).add T5).sub h6).add T7).sub T8 |>.congr fun u _ h => ?_
    simp only [pow_one]
  have h2 : UOOn (Icc a b) 2 (fun u h => lB pp PiP PiM b_fn u h - h * transportOp (M0fun pp PiM) b_fn u) := by
    refine key.congr fun u _ h => ?_
    rw [lB_eq_of_adj b_fn u h (hadj u h)]
    simp only [transportOp]
    ring
  have hpa : PApproxOn (Icc a b) 3 (fun u h => lB pp PiP PiM b_fn u h - h * transportOp (M0fun pp PiM) b_fn u) := by
    have s1 := BSmoothOn.papprox_shift_Icc' (L := a - η) (R := b + η) (a' := a) (b' := b)
      (by linarith [hη]) (by linarith [hη]) hb 1 (σ := fun u h => u + h) (fun _ _ => by ring)
    have s2 := BSmoothOn.papprox_shift_Icc' (L := a - η) (R := b + η) (a' := a) (b' := b)
      (by linarith [hη]) (by linarith [hη]) hb (-1) (σ := fun u h => u - h) (fun _ _ => by ring)
    obtain ⟨CT, hCT⟩ := transportOp_bdd_on ((hM0.subset hIi).mono (by norm_num)) ((hb.subset hIi).mono (by norm_num))
    have hT : PApproxOn (Icc a b) 3 (fun u _ => transportOp (M0fun pp PiM) b_fn u) :=
      PApproxOn.of_fun (transportOp (M0fun pp PiM) b_fn) hCT
    unfold lB
    have hSi := hS.subset hIi
    exact ((((hSi.sP 1 0).mono hN).mul s1).add (((hSi.sM 1 0).mono hN).mul s2)).sub
      ((PApproxOn.hpow_mul 1 hT).congr fun u _ h => by simp)
  exact PApproxOn.lift (n := 2) (σ := -1) (δ0 := 1) (by norm_num) hpa h2 one_pos
    (fun u _ h _ => by rw [lB_odd_of_par hpar hP]; ring)

lemma defect_papprox_I {I : Set ℝ} {N : ℕ} {pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2}
    (hS : SymbolExpOn I N pp qq PiP PiM) {AA BB : ℝ → ℝ → ℝ}
    (hAp : PApproxOn I N (fun u h => AA (u + h) h)) (hAm : PApproxOn I N (fun u h => AA (u - h) h))
    (hA0 : PApproxOn I N AA)
    (hBp : PApproxOn I N (fun u h => BB (u + h) h)) (hBm : PApproxOn I N (fun u h => BB (u - h) h))
    (hB0 : PApproxOn I N BB) (k : Fin 2) :
    PApproxOn I N (fun u h => defectRow pp qq AA BB PiP PiM u h k) := by
  have hh := PApproxOn.hpow I (N := N) 1
  fin_cases k
  · have hpa := (((hAp.mul (hS.sP 0 0)).add ((hh.mul hBp).mul (hS.sP 1 0))).add
      ((hAm.mul (hS.sM 0 0)).add ((hh.mul hBm).mul (hS.sM 1 0)))).sub (hS.qe.mul hA0)
    change PApproxOn I N (fun u h => defectRow pp qq AA BB PiP PiM u h 0)
    exact hpa.congr fun u _ h => by
      rw [defectRow_zero_eq pp qq PiP PiM AA BB u h]; simp only [pow_one]; ring
  · have hpa := (((hAp.mul (hS.sP 0 1)).add ((hh.mul hBp).mul (hS.sP 1 1))).add
      ((hAm.mul (hS.sM 0 1)).add ((hh.mul hBm).mul (hS.sM 1 1)))).sub (hh.mul (hS.qe.mul hB0))
    change PApproxOn I N (fun u h => defectRow pp qq AA BB PiP PiM u h 1)
    exact hpa.congr fun u _ h => by
      rw [defectRow_one_eq pp qq PiP PiM AA BB u h]; simp only [pow_one]; ring

lemma Fcas_papprox_I {I : Set ℝ} {N : ℕ} {pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2}
    (hS : SymbolExpOn I N pp qq PiP PiM) {AA BB : ℝ → ℝ → ℝ}
    (hAp : PApproxOn I N (fun s h => AA (s + h / 2) h)) (hAm : PApproxOn I N (fun s h => AA (s - h / 2) h))
    (hBp : PApproxOn I N (fun s h => BB (s + h / 2) h)) (hBm : PApproxOn I N (fun s h => BB (s - h / 2) h)) :
    PApproxOn I N (Fcas pp AA BB PiM) := by
  have hh := PApproxOn.hpow I (N := N) 1
  have hh2 := PApproxOn.hpow I (N := N) 2
  have hpa := ((((hS.cM 0 1).mul (hAp.mul hAm)).add ((hh.mul (hS.cM 1 1)).mul (hAp.mul hBm))).sub
    ((hh.mul (hS.cM 0 0)).mul (hBp.mul hAm))).sub ((hh2.mul (hS.cM 1 0)).mul (hBp.mul hBm))
  exact hpa.congr fun s _ h => by simp [Fcas_expand]

lemma dFA_UO1_local {L R a' b' : ℝ} (hL : L < a') (hR : b' < R) {N : ℕ} (hN : 1 ≤ N)
    {pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2} (hS : SymbolExpOn (Icc a' b') N pp qq PiP PiM)
    {g b : ℕ → ℝ → ℝ} {k l : ℕ} (hk : 1 ≤ k)
    (hg : ∀ i ≤ k, BSmoothOn (Icc L R) N (g i)) (hb : ∀ i, 1 ≤ i → i ≤ l → BSmoothOn (Icc L R) N (b i)) :
    UOOn (Icc a' b') (2 * k + 1) (fun s h => Fcas pp (Aans g (k + 1)) (Bans b l) PiM s h
      - Fcas pp (Aans g k) (Bans b l) PiM s h - h ^ (2 * k) * (2 * V0fun pp PiM s * g 0 s * g k s)) := by
  have hgk : ∀ i < k, BSmoothOn (Icc L R) N (g i) := fun i hi => hg i hi.le
  set Φ : ℝ → ℝ → ℝ := fun s h =>
    (pp s h * PiM (s + h / 2) h 0 1) * (Aans g k (s + h / 2) h * g k (s - h / 2) + g k (s + h / 2) * Aans g k (s - h / 2) h
      + h ^ (2 * k) * (g k (s + h / 2) * g k (s - h / 2)))
    + h * (pp s h * PiM (s + h / 2) h 1 1) * (g k (s + h / 2) * Bans b l (s - h / 2) h)
    - h * (pp s h * PiM (s + h / 2) h 0 0) * (Bans b l (s + h / 2) h * g k (s - h / 2)) with hΦ
  have hdiff : ∀ s h, Fcas pp (Aans g (k + 1)) (Bans b l) PiM s h - Fcas pp (Aans g k) (Bans b l) PiM s h
      = h ^ (2 * k) * Φ s h := fun s h => by
    rw [Fcas_expand, Fcas_expand]; simp only [Aans_succ, hΦ]; ring
  have gp := BSmoothOn.papprox_shift_Icc' hL hR (hg k le_rfl) (1 / 2) (σ := fun s h => s + h / 2) (fun _ _ => by ring)
  have gm := BSmoothOn.papprox_shift_Icc' hL hR (hg k le_rfl) (-1 / 2) (σ := fun s h => s - h / 2) (fun _ _ => by ring)
  have ap := Aans_papprox_Icc hL hR hgk (1 / 2) (σ := fun s h => s + h / 2) (fun _ _ => by ring)
  have am := Aans_papprox_Icc hL hR hgk (-1 / 2) (σ := fun s h => s - h / 2) (fun _ _ => by ring)
  have bp := Bans_papprox_Icc hL hR hb (1 / 2) (σ := fun s h => s + h / 2) (fun _ _ => by ring)
  have bm := Bans_papprox_Icc hL hR hb (-1 / 2) (σ := fun s h => s - h / 2) (fun _ _ => by ring)
  have hh := PApproxOn.hpow (Icc a' b') (N := N) 1
  have h2k := PApproxOn.hpow (Icc a' b') (N := N) (2 * k)
  have hpa : PApproxOn (Icc a' b') N Φ := by
    have hraw := ((((hS.cM 0 1).mul (((ap.mul gm).add (gp.mul am)).add (h2k.mul (gp.mul gm)))).add
      ((hh.mul (hS.cM 1 1)).mul (gp.mul bm))).sub ((hh.mul (hS.cM 0 0)).mul (bp.mul gm)))
    exact hraw.congr fun s _ h => by simp only [hΦ, pow_one]
  have hΦ0 : ∀ s, Φ s 0 = 2 * V0fun pp PiM s * g 0 s * g k s := fun s => by
    simp only [hΦ, V0fun, zero_div, add_zero, sub_zero, zero_mul,
      Aans_zero_h g hk, zero_pow (by omega : 2 * k ≠ 0)]
    ring
  have h1 : UOOn (Icc a' b') 1 (fun s h => Φ s h - 2 * V0fun pp PiM s * g 0 s * g k s) :=
    (hpa.mono hN).order1.congr fun s _ h => by simp [hΦ0]
  refine (UOOn.hpow_mul (2 * k) h1).congr fun s _ h => ?_
  have := hdiff s h
  linear_combination (-1 : ℝ) * this

lemma dFB_UO_local {L R a' b' : ℝ} (hL : L < a') (hR : b' < R) {N : ℕ}
    {pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2} (hS : SymbolExpOn (Icc a' b') N pp qq PiP PiM)
    {g b : ℕ → ℝ → ℝ} {k l : ℕ}
    (hg : ∀ i < k, BSmoothOn (Icc L R) N (g i)) (hb : ∀ i, 1 ≤ i → i ≤ l + 1 → BSmoothOn (Icc L R) N (b i)) :
    UOOn (Icc a' b') (2 * l + 1)
      (fun s h => Fcas pp (Aans g k) (Bans b (l + 1)) PiM s h - Fcas pp (Aans g k) (Bans b l) PiM s h) := by
  have hbl : ∀ i, 1 ≤ i → i ≤ l → BSmoothOn (Icc L R) N (b i) := fun i h1 h2 => hb i h1 (by omega)
  have hbk := hb (l + 1) (by omega) le_rfl
  set Ψ : ℝ → ℝ → ℝ := fun s h =>
    (pp s h * PiM (s + h / 2) h 1 1) * (Aans g k (s + h / 2) h * b (l + 1) (s - h / 2))
    - (pp s h * PiM (s + h / 2) h 0 0) * (b (l + 1) (s + h / 2) * Aans g k (s - h / 2) h)
    - h * (pp s h * PiM (s + h / 2) h 1 0) * (Bans b l (s + h / 2) h * b (l + 1) (s - h / 2)
        + b (l + 1) (s + h / 2) * Bans b l (s - h / 2) h
        + h ^ (2 * l) * (b (l + 1) (s + h / 2) * b (l + 1) (s - h / 2))) with hΨ
  have hdiff : ∀ s h, Fcas pp (Aans g k) (Bans b (l + 1)) PiM s h - Fcas pp (Aans g k) (Bans b l) PiM s h
      = h ^ (2 * l + 1) * Ψ s h := fun s h => by
    rw [Fcas_expand, Fcas_expand]; simp only [Bans_succ, hΨ]; ring
  have βp := BSmoothOn.papprox_shift_Icc' hL hR hbk (1 / 2) (σ := fun s h => s + h / 2) (fun _ _ => by ring)
  have βm := BSmoothOn.papprox_shift_Icc' hL hR hbk (-1 / 2) (σ := fun s h => s - h / 2) (fun _ _ => by ring)
  have ap := Aans_papprox_Icc hL hR hg (1 / 2) (σ := fun s h => s + h / 2) (fun _ _ => by ring)
  have am := Aans_papprox_Icc hL hR hg (-1 / 2) (σ := fun s h => s - h / 2) (fun _ _ => by ring)
  have bp := Bans_papprox_Icc hL hR hbl (1 / 2) (σ := fun s h => s + h / 2) (fun _ _ => by ring)
  have bm := Bans_papprox_Icc hL hR hbl (-1 / 2) (σ := fun s h => s - h / 2) (fun _ _ => by ring)
  have hh := PApproxOn.hpow (Icc a' b') (N := N) 1
  have h2l := PApproxOn.hpow (Icc a' b') (N := N) (2 * l)
  have hpa : PApproxOn (Icc a' b') N Ψ := by
    have hraw := (((hS.cM 1 1).mul (ap.mul βm)).sub ((hS.cM 0 0).mul (βp.mul am))).sub
      ((hh.mul (hS.cM 1 0)).mul ((((bp.mul βm).add (βp.mul bm)).add (h2l.mul (βp.mul βm)))))
    exact hraw.congr fun s _ h => by simp only [hΨ, pow_one]
  refine (UOOn.hpow_mul (2 * l + 1) hpa.bdd).congr fun s _ h => (hdiff s h).symm

lemma defect_remainder_I {I : Set ℝ} {n : ℕ} {PiP PiM : ℝ → ℝ → M2}
    (hbP : ∀ i j, UOOn I 0 (fun u h => PiP u h i j)) (hbM : ∀ i j, UOOn I 0 (fun u h => PiM u h i j))
    {RP RQ : ℝ → ℝ → ℝ} (_hRP : UOOn I 0 RP) (hRQ : UOOn I 0 RQ) {AA BB : ℝ → ℝ → ℝ}
    (hAp : UOOn I 0 (fun u h => AA (u + h) h)) (hAm : UOOn I 0 (fun u h => AA (u - h) h)) (hA0 : UOOn I 0 AA)
    (hBp : UOOn I 0 (fun u h => BB (u + h) h)) (hBm : UOOn I 0 (fun u h => BB (u - h) h)) (hB0 : UOOn I 0 BB)
    (hRPp : UOOn I 0 (fun u h => RP (u + h / 2) h)) (hRPm : UOOn I 0 (fun u h => RP (u - h / 2) h))
    (k : Fin 2) :
    UOOn I n (fun u h => defectRow (fun s h => h ^ n * RP s h) (fun u h => h ^ n * RQ u h) AA BB PiP PiM u h k) := by
  have hh : UOOn I 0 (fun _ h => h) := ((UOOn.hpow I 1).mono (Nat.zero_le 1)).congr fun _ _ _ => by simp
  fin_cases k
  · change UOOn I n (fun u h => defectRow (fun s h => h ^ n * RP s h) (fun u h => h ^ n * RQ u h) AA BB PiP PiM u h 0)
    have br := ((hRPp.mul ((hAp.mul (hbP 0 0)).add ((hh.mul hBp).mul (hbP 1 0)))).add
      (hRPm.mul ((hAm.mul (hbM 0 0)).add ((hh.mul hBm).mul (hbM 1 0))))).sub (hRQ.mul hA0)
    exact (UOOn.hpow_mul n br).congr fun u _ h => by rw [defectRow_zero_eq]; ring
  · change UOOn I n (fun u h => defectRow (fun s h => h ^ n * RP s h) (fun u h => h ^ n * RQ u h) AA BB PiP PiM u h 1)
    have br := ((hRPp.mul ((hAp.mul (hbP 0 1)).add ((hh.mul hBp).mul (hbP 1 1)))).add
      (hRPm.mul ((hAm.mul (hbM 0 1)).add ((hh.mul hBm).mul (hbM 1 1))))).sub (hRQ.mul (hh.mul hB0))
    exact (UOOn.hpow_mul n br).congr fun u _ h => by rw [defectRow_one_eq]; ring

/-! ### Local standing hypotheses, correctors, and `localized_eng_corr_full` -/

/-- Localised standing hypotheses of `thm:eng-corr` on `[a, b]` with outer thickened interval `[a - η, b + η]`. -/
structure LocalCorrSetting (K : ℕ) (a b η : ℝ) (pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2) : Prop where
  ha : a ≤ b
  hη : 0 < η
  par_Pi : ∀ u h, PiP u (-h) = Sg * PiM u h * Sg
  adj_Pi : ∀ u h, PiP u h = Matrix.adjugate (PiM (u + h) h)
  pp_even : ∀ s h, pp s (-h) = pp s h
  qq_even : ∀ u h, qq u (-h) = qq u h
  exp : SymbolExpOn (Icc (a - η) (b + η)) (2 * K + 3) pp qq PiP PiM
  langer : ∀ u ∈ Icc (a - η) (b + η), pp u 0 * (PiP u 0 0 0 + PiM u 0 0 0) = qq u 0
  M0_smooth : BSmoothOn (Icc (a - η) (b + η)) 2 (M0fun pp PiM)

/-- Localised correctors on `[a, b]` inside `[a - η, b + η]` (with flux recursion on `[a - η / 2, b + η / 2]`). -/
structure LocalCorrectors (K : ℕ) (a b η : ℝ) (pp : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2) (qq : ℝ → ℝ → ℝ)
    (g b_fn : ℕ → ℝ → ℝ) (c : ℕ → ℝ) : Prop where
  g0 : ∀ u ∈ Icc (a - η) (b + η), g 0 u = Real.sqrt (c 0 / V0fun pp PiM u)
  c0_sign : ∀ u ∈ Icc (a - η) (b + η), 0 < c 0 / V0fun pp PiM u
  g0_pos : ∃ m0 : ℝ, 0 < m0 ∧ ∀ u ∈ Icc (a - η) (b + η), m0 ≤ g 0 u
  g_reg : ∀ i, i ≤ K → BSmoothOn (Icc (a - η) (b + η)) (2 * K + 3) (g i)
  b_reg : ∀ i, 1 ≤ i → i ≤ K → BSmoothOn (Icc (a - η) (b + η)) (2 * K + 3) (b_fn i)
  transport : ∀ k, 1 ≤ k → k ≤ K → ∀ a_fn : ℝ → ℝ,
    UOOn (Icc a b) (2 * k + 2) (fun u h => dA pp qq PiP PiM g b_fn k (k - 1) u h - h ^ (2 * k) * a_fn u) →
    ∀ u ∈ Icc a b, transportOp (M0fun pp PiM) (b_fn k) u = -a_fn u
  flux : ∀ k, 1 ≤ k → k ≤ K → ∀ f_fn : ℝ → ℝ,
    UOOn (Icc (a - η / 2) (b + η / 2)) (2 * k + 2)
      (fun s h => FF pp PiM g b_fn k k s h - Pc c k h - h ^ (2 * k) * f_fn s) →
    ∀ s ∈ Icc (a - η / 2) (b + η / 2), 2 * V0fun pp PiM s * g 0 s * g k s = c k - f_fn s

section LocalMain

variable {K : ℕ} {a b η : ℝ} {pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2}
  {g b_fn : ℕ → ℝ → ℝ} {c : ℕ → ℝ}

private lemma LocalCorrSetting.I_in_sub (S : LocalCorrSetting K a b η pp qq PiP PiM) :
    Icc a b ⊆ Icc (a - η) (b + η) :=
  fun _ hx => ⟨by linarith [hx.1, S.hη], by linarith [hx.2, S.hη]⟩

private lemma LocalCorrSetting.I_mid_sub (S : LocalCorrSetting K a b η pp qq PiP PiM) :
    Icc (a - η / 2) (b + η / 2) ⊆ Icc (a - η) (b + η) :=
  fun _ hx => ⟨by linarith [hx.1, S.hη], by linarith [hx.2, S.hη]⟩

private lemma defectRow_parity_loc (hpar : ∀ u h, PiP u (-h) = Sg * PiM u h * Sg)
    (hP : ∀ s h, pp s (-h) = pp s h) (hQ : ∀ u h, qq u (-h) = qq u h)
    {AA BB : ℝ → ℝ → ℝ} (hAe : ∀ u h, AA u (-h) = AA u h) (hBe : ∀ u h, BB u (-h) = BB u h)
    (u h : ℝ) :
    defectRow pp qq AA BB PiP PiM u (-h) 0 = defectRow pp qq AA BB PiP PiM u h 0 ∧
    defectRow pp qq AA BB PiP PiM u (-h) 1 = -defectRow pp qq AA BB PiP PiM u h 1 := by
  obtain ⟨p00, p01, p10, p11, m00, m01, m10, m11⟩ := par_Pi_entries_of_par hpar u h
  have e1 : u + -h / 2 = u - h / 2 := by ring
  have e2 : u - -h / 2 = u + h / 2 := by ring
  have e3 : u + -h = u - h := by ring
  have e4 : u - -h = u + h := by ring
  simp only [defectRow, e1, e2, e3, e4, hP, hQ, vrow, hAe, hBe, p00, p01, p10, p11, m00, m01, m10, m11,
    rowMul, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> ring

private lemma LocalCorrSetting.dA_even (S : LocalCorrSetting K a b η pp qq PiP PiM) (k l : ℕ) (u h : ℝ) :
    dA pp qq PiP PiM g b_fn k l u (-h) = dA pp qq PiP PiM g b_fn k l u h :=
  (defectRow_parity_loc S.par_Pi S.pp_even S.qq_even (Aans_even g k) (Bans_even b_fn l) u h).1

private lemma LocalCorrSetting.FF_even (S : LocalCorrSetting K a b η pp qq PiP PiM) (k l : ℕ) (s h : ℝ) :
    FF pp PiM g b_fn k l s (-h) = FF pp PiM g b_fn k l s h :=
  Fcas_even_of_adj S.par_Pi S.pp_even (Aans_even g k) (Bans_even b_fn l) s h
    (by have := S.adj_Pi (s - h / 2) h; rwa [show s - h / 2 + h = s + h / 2 by ring] at this)

private lemma LocalCorrSetting.ans_papprox_on (S : LocalCorrSetting K a b η pp qq PiP PiM)
    (C : LocalCorrectors K a b η pp PiP PiM qq g b_fn c) (a' b' : ℝ)
    (ha' : a - η < a') (hb' : b' < b + η) {k l : ℕ} (hk : k ≤ K + 1) (hl : l ≤ K) :
    PApproxOn (Icc a' b') (2 * K + 3) (dA pp qq PiP PiM g b_fn k l) ∧
    PApproxOn (Icc a' b') (2 * K + 3) (dB pp qq PiP PiM g b_fn k l) ∧
    PApproxOn (Icc a' b') (2 * K + 3) (FF pp PiM g b_fn k l) := by
  have hsub : Icc a' b' ⊆ Icc (a - η) (b + η) := fun _ hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hS := S.exp.subset hsub
  have hgk : ∀ i < k, BSmoothOn (Icc (a - η) (b + η)) (2 * K + 3) (g i) := fun i hi => C.g_reg i (by omega)
  have hbl : ∀ i, 1 ≤ i → i ≤ l → BSmoothOn (Icc (a - η) (b + η)) (2 * K + 3) (b_fn i) :=
    fun i h1 h2 => C.b_reg i h1 (by omega)
  have Ap := Aans_papprox_Icc ha' hb' hgk 1 (σ := fun u h => u + h) (fun _ _ => by ring)
  have Am := Aans_papprox_Icc ha' hb' hgk (-1) (σ := fun u h => u - h) (fun _ _ => by ring)
  have A0 := Aans_papprox_Icc ha' hb' hgk 0 (σ := fun u _ => u) (fun _ _ => by ring)
  have Bp := Bans_papprox_Icc ha' hb' hbl 1 (σ := fun u h => u + h) (fun _ _ => by ring)
  have Bm := Bans_papprox_Icc ha' hb' hbl (-1) (σ := fun u h => u - h) (fun _ _ => by ring)
  have B0 := Bans_papprox_Icc ha' hb' hbl 0 (σ := fun u _ => u) (fun _ _ => by ring)
  have Ah := Aans_papprox_Icc ha' hb' hgk (1 / 2) (σ := fun u h => u + h / 2) (fun _ _ => by ring)
  have Ah' := Aans_papprox_Icc ha' hb' hgk (-1 / 2) (σ := fun u h => u - h / 2) (fun _ _ => by ring)
  have Bh := Bans_papprox_Icc ha' hb' hbl (1 / 2) (σ := fun u h => u + h / 2) (fun _ _ => by ring)
  have Bh' := Bans_papprox_Icc ha' hb' hbl (-1 / 2) (σ := fun u h => u - h / 2) (fun _ _ => by ring)
  exact ⟨defect_papprox_I hS Ap Am A0 Bp Bm B0 0, defect_papprox_I hS Ap Am A0 Bp Bm B0 1,
    Fcas_papprox_I hS Ah Ah' Bh Bh'⟩

private lemma LocalCorrSetting.D1_bound (S : LocalCorrSetting K a b η pp qq PiP PiM) {AA BB : ℝ → ℝ → ℝ}
    {n : ℕ}
    (hlow : ∃ m δ : ℝ, 0 < m ∧ 0 < δ ∧ ∀ u ∈ Icc a b, ∀ h, |h| < δ → m ≤ |AA u h|)
    (hBD : UOOn (Icc a b) n (fun u h => h * BB u h * defectRow pp qq AA BB PiP PiM u h 0))
    {P : ℝ → ℝ} (hF : UOOn (Icc (a - η / 2) (b + η / 2)) n (fun s h => Fcas pp AA BB PiM s h - P h)) :
    UOOn (Icc a b) n (fun u h => defectRow pp qq AA BB PiP PiM u h 1) := by
  have hFp : UOOn (Icc a b) n (fun u h => Fcas pp AA BB PiM (u + h / 2) h - P h) :=
    (hF.shift_Icc (by linarith [S.hη] : 0 < η / 2) (1 / 2)).congr fun u _ h => by simp only [one_div]; ring_nf
  have hFm : UOOn (Icc a b) n (fun u h => Fcas pp AA BB PiM (u - h / 2) h - P h) :=
    (hF.shift_Icc (by linarith [S.hη] : 0 < η / 2) (-1 / 2)).congr fun u _ h => by ring_nf
  have hX : UOOn (Icc a b) n (fun u h => h * BB u h * defectRow pp qq AA BB PiP PiM u h 0
      - ((Fcas pp AA BB PiM (u + h / 2) h - P h) - (Fcas pp AA BB PiM (u - h / 2) h - P h))) :=
    hBD.sub (hFp.sub hFm)
  have hAD : UOOn (Icc a b) n (fun u h => AA u h * defectRow pp qq AA BB PiP PiM u h 1) := by
    refine hX.congr fun u _ h => ?_
    have := green_identity_of_adj pp qq AA BB PiP PiM u h (S.adj_Pi u h)
    linear_combination (-1 : ℝ) * this
  exact UOOn.div_of_lower hlow hAD

private lemma LocalCorrSetting.D1_lift (S : LocalCorrSetting K a b η pp qq PiP PiM) {AA BB : ℝ → ℝ → ℝ}
    (hAe : ∀ u h, AA u (-h) = AA u h) (hBe : ∀ u h, BB u (-h) = BB u h) {n : ℕ} (hn : Even n)
    (hpa : PApproxOn (Icc a b) (n + 1) (fun u h => defectRow pp qq AA BB PiP PiM u h 1))
    (h0 : UOOn (Icc a b) n (fun u h => defectRow pp qq AA BB PiP PiM u h 1)) :
    UOOn (Icc a b) (n + 1) (fun u h => defectRow pp qq AA BB PiP PiM u h 1) := by
  refine PApproxOn.lift (n := n) (σ := -1) (δ0 := 1) (by rw [hn.neg_one_pow]; norm_num) hpa h0 one_pos
    (fun u _ h _ => ?_)
  have := (defectRow_parity_loc S.par_Pi S.pp_even S.qq_even hAe hBe u h).2
  rw [this]; ring

private lemma Pc_papproxOn (I : Set ℝ) (c : ℕ → ℝ) (k N : ℕ) :
    PApproxOn I N (fun _ h => Pc c k h) := by
  unfold Pc
  exact PApproxOn.sum (range k) fun i _ =>
    (PApproxOn.of_fun (fun _ => c i) (C := |c i|) fun _ _ => le_rfl).mul (PApproxOn.hpow I (2 * i))

private lemma LocalCorrectors.g0_sq (_S : LocalCorrSetting K a b η pp qq PiP PiM)
    (C : LocalCorrectors K a b η pp PiP PiM qq g b_fn c) (u : ℝ) (hu : u ∈ Icc (a - η) (b + η)) :
    g 0 u ^ 2 * V0fun pp PiM u = c 0 := by
  have hpos := C.c0_sign u hu
  have hV : V0fun pp PiM u ≠ 0 := by
    intro h0; rw [h0, div_zero] at hpos; exact lt_irrefl _ hpos
  rw [C.g0 u hu, Real.sq_sqrt hpos.le]
  field_simp

private lemma LocalCorrectors.lower (S : LocalCorrSetting K a b η pp qq PiP PiM)
    (C : LocalCorrectors K a b η pp PiP PiM qq g b_fn c) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ K + 1) :
    ∃ m δ : ℝ, 0 < m ∧ 0 < δ ∧ ∀ u ∈ Icc a b, ∀ h, |h| < δ → m ≤ |Aans g k u h| := by
  obtain ⟨m0, hm0, hgm⟩ := C.g0_pos
  have hg : ∀ i < k, ∃ C0, ∀ x ∈ Icc a b, |g i x| ≤ C0 := fun i hi =>
    ((C.g_reg i (by omega)).subset S.I_in_sub).bdd
  have hsub : UOOn (Icc a b) 2 (fun u h => Aans g k u h - g 0 u) := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have e : ∀ u h, Aans g (k' + 1) u h - g 0 u = ∑ i ∈ range k', h ^ (2 * (i + 1)) * g (i + 1) u := by
      intro u h; simp [Aans, Finset.sum_range_succ']
    refine (UOOn.sum (range k') fun i hi => ?_).congr fun u _ h => (e u h).symm
    obtain ⟨C0, hC0⟩ := hg (i + 1) (by have := Finset.mem_range.mp hi; omega)
    exact (UOOn.hpow_mul (2 * (i + 1)) (UOOn.of_bdd fun u hu _ => hC0 u hu)).mono (by omega)
  obtain ⟨C0, δ, hC0, hδ, hδ1, H⟩ := hsub.norm
  refine ⟨m0 / 2, min δ (m0 / (2 * (C0 + 1))), by positivity, lt_min hδ (by positivity), fun u hu h hh => ?_⟩
  have h1 : |h| < δ := lt_of_lt_of_le hh (min_le_left _ _)
  have h2 : |h| < m0 / (2 * (C0 + 1)) := lt_of_lt_of_le hh (min_le_right _ _)
  have h3 := H u hu h h1
  have h4 : |h| ≤ 1 := (h1.trans_le hδ1).le
  have h5 : |h| ^ 2 ≤ |h| := by nlinarith [abs_nonneg h]
  have h6 : C0 * |h| ^ 2 ≤ m0 / 2 := by
    calc C0 * |h| ^ 2 ≤ C0 * |h| := mul_le_mul_of_nonneg_left h5 hC0
      _ ≤ (C0 + 1) * |h| := by nlinarith [abs_nonneg h]
      _ ≤ (C0 + 1) * (m0 / (2 * (C0 + 1))) := mul_le_mul_of_nonneg_left h2.le (by linarith)
      _ = m0 / 2 := by field_simp
  have hu0 := hgm u (S.I_in_sub hu)
  have h7 : g 0 u - |Aans g k u h - g 0 u| ≤ |Aans g k u h| := by
    have := abs_sub_abs_le_abs_sub (g 0 u) (Aans g k u h)
    rw [abs_of_pos (lt_of_lt_of_le hm0 hu0)] at this
    rw [abs_sub_comm] at this
    linarith
  linarith

private lemma LocalCorrectors.Bans_bdd (S : LocalCorrSetting K a b η pp qq PiP PiM)
    (C : LocalCorrectors K a b η pp PiP PiM qq g b_fn c) {l : ℕ} (hl : l ≤ K) :
    UOOn (Icc a b) 0 (Bans b_fn l) := by
  have hbl : ∀ i, 1 ≤ i → i ≤ l → BSmoothOn (Icc (a - η) (b + η)) (2 * K + 3) (b_fn i) :=
    fun i h1 h2 => C.b_reg i h1 (by omega)
  exact (Bans_papprox_Icc (by linarith [S.hη]) (by linarith [S.hη]) hbl 0 (σ := fun u _ => u) (fun _ _ => by ring)).bdd

def PInvOn (a b η : ℝ) (pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2)
    (g b_fn : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (j : ℕ) : Prop :=
  UOOn (Icc a b) (2 * j + 2) (dA pp qq PiP PiM g b_fn (j + 1) j) ∧
  UOOn (Icc a b) (2 * j + 3) (dB pp qq PiP PiM g b_fn (j + 1) j) ∧
  UOOn (Icc (a - η / 2) (b + η / 2)) (2 * j + 2) (fun s h => FF pp PiM g b_fn (j + 1) j s h - Pc c (j + 1) h)

def QInvOn (a b η : ℝ) (pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2)
    (g b_fn : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (j : ℕ) : Prop :=
  UOOn (Icc a b) (2 * j + 4) (dA pp qq PiP PiM g b_fn (j + 1) (j + 1)) ∧
  UOOn (Icc a b) (2 * j + 3) (dB pp qq PiP PiM g b_fn (j + 1) (j + 1)) ∧
  UOOn (Icc (a - η / 2) (b + η / 2)) (2 * j + 2) (fun s h => FF pp PiM g b_fn (j + 1) (j + 1) s h - Pc c (j + 1) h)

private lemma PInvOn_zero (S : LocalCorrSetting K a b η pp qq PiP PiM)
    (C : LocalCorrectors K a b η pp PiP PiM qq g b_fn c) :
    PInvOn a b η pp qq PiP PiM g b_fn c 0 := by
  have hd0 : UOOn (Icc a b) 2 (dA pp qq PiP PiM g b_fn 1 0) := by
    refine (lA_UO2_local S.hη (by omega) (S.exp.subset S.I_in_sub) S.par_Pi S.pp_even S.qq_even
      (fun u hu => S.langer u (S.I_in_sub hu)) ((C.g_reg 0 (by omega)).mono (by omega))).congr fun u _ h => ?_
    rw [dA_succ_A, dA_zero_zero]; simp
  obtain ⟨_, hpaD1, _⟩ := S.ans_papprox_on C a b (by linarith [S.hη]) (by linarith [S.hη])
    (k := 1) (l := 0) (by omega) (by omega)
  obtain ⟨_, _, hpaF⟩ := S.ans_papprox_on C (a - η / 2) (b + η / 2)
    (by linarith [S.hη]) (by linarith [S.hη]) (k := 1) (l := 0) (by omega) (by omega)
  have hF0 : ∀ s ∈ Icc (a - η / 2) (b + η / 2), FF pp PiM g b_fn 1 0 s 0 = c 0 := fun s hs => by
    have := Fcas_zero pp (Aans g 1) (Bans b_fn 0) PiM s
    have e : Aans g 1 s 0 = g 0 s := Aans_zero_h g le_rfl s
    unfold FF
    rw [this, e, ← C.g0_sq S s (S.I_mid_sub hs)]
    simp [V0fun]
  have hP1 : ∀ h : ℝ, Pc c 1 h = c 0 := fun h => by simp [Pc]
  have hFP : UOOn (Icc (a - η / 2) (b + η / 2)) 2 (fun s h => FF pp PiM g b_fn 1 0 s h - Pc c 1 h) := by
    have h1 : UOOn (Icc (a - η / 2) (b + η / 2)) 1 (fun s h => FF pp PiM g b_fn 1 0 s h - Pc c 1 h) :=
      (hpaF.mono (by omega : 1 ≤ 2 * K + 3)).order1.congr fun s hs h => by rw [hF0 s hs, hP1]
    have hpa := (hpaF.mono (by omega : 2 ≤ 2 * K + 3)).sub (Pc_papproxOn _ c 1 2)
    exact PApproxOn.lift (n := 1) (σ := 1) (δ0 := 1) (by norm_num) hpa h1 one_pos
      (fun s _ h _ => by rw [one_mul, S.FF_even 1 0 s h, Pc_even])
  refine ⟨hd0, ?_, hFP⟩
  have hAe := Aans_even g 1
  have hBe := Bans_even b_fn 0
  have h2 : UOOn (Icc a b) 2 (dB pp qq PiP PiM g b_fn 1 0) := by
    refine S.D1_bound (AA := Aans g 1) (BB := Bans b_fn 0) (C.lower S le_rfl (by omega)) ?_ hFP
    exact (UOOn.zero _ 2).congr fun u _ h => by simp [Bans]
  exact S.D1_lift hAe hBe (n := 2) (by decide) (hpaD1.mono (by omega)) h2

private lemma PInvOn_to_QInvOn (S : LocalCorrSetting K a b η pp qq PiP PiM)
    (C : LocalCorrectors K a b η pp PiP PiM qq g b_fn c) {j : ℕ}
    (hj : j + 1 ≤ K) (hP : PInvOn a b η pp qq PiP PiM g b_fn c j) :
    QInvOn a b η pp qq PiP PiM g b_fn c j := by
  obtain ⟨hD0, _, hF⟩ := hP
  have hN4 : 2 * j + 4 ≤ 2 * K + 3 := by omega
  obtain ⟨hpaD0, _, _⟩ := S.ans_papprox_on C a b (by linarith [S.hη]) (by linarith [S.hη])
    (k := j + 1) (l := j) (by omega) (by omega)
  obtain ⟨_, hpaD1', _⟩ := S.ans_papprox_on C a b (by linarith [S.hη]) (by linarith [S.hη])
    (k := j + 1) (l := j + 1) (by omega) (by omega)
  obtain ⟨_, _, hpaFm⟩ := S.ans_papprox_on C (a - η / 2) (b + η / 2)
    (by linarith [S.hη]) (by linarith [S.hη]) (k := j + 1) (l := j) (by omega) (by omega)
  obtain ⟨_, _, hpaFm'⟩ := S.ans_papprox_on C (a - η / 2) (b + η / 2)
    (by linarith [S.hη]) (by linarith [S.hη]) (k := j + 1) (l := j + 1) (by omega) (by omega)
  obtain ⟨a_fn, _, ha_fn⟩ := PApproxOn.exists_coeff (n := 2 * j + 2) (σ := 1) (δ0 := 1)
    (by rw [(show Even (2 * j + 2) from ⟨j + 1, by ring⟩).neg_one_pow]; norm_num) (hpaD0.mono hN4) hD0 one_pos
    (fun u _ h _ => by rw [one_mul]; exact S.dA_even (j + 1) j u h)
  have hTa : ∀ u ∈ Icc a b, transportOp (M0fun pp PiM) (b_fn (j + 1)) u = -a_fn u := by
    refine C.transport (j + 1) (by omega) hj a_fn ?_
    have e : 2 * (j + 1) + 2 = 2 * j + 2 + 2 := by ring
    rw [e]
    refine ha_fn.congr fun u _ h => ?_
    simp only [Nat.add_sub_cancel]
    rw [show 2 * (j + 1) = 2 * j + 2 by ring]
  have hlB := lB_UO3_local S.hη (N := 2 * K + 3) (by omega) S.exp S.par_Pi S.adj_Pi S.pp_even S.M0_smooth
    ((C.b_reg (j + 1) (by omega) hj).mono (by omega))
  have hq0 : UOOn (Icc a b) (2 * j + 4) (dA pp qq PiP PiM g b_fn (j + 1) (j + 1)) := by
    have := ha_fn.add (UOOn.hpow_mul (2 * j + 1) hlB)
    have e : 2 * j + 2 + 2 = 2 * j + 4 := by ring
    have e' : 2 * j + 1 + 3 = 2 * j + 4 := by ring
    rw [e, e'] at this
    refine this.congr fun u hu h => ?_
    rw [dA_succ_B]
    have := hTa u hu
    linear_combination (-(h ^ (2 * j + 2))) * this
  have hΔ : UOOn (Icc (a - η / 2) (b + η / 2)) (2 * j + 2)
      (fun s h => FF pp PiM g b_fn (j + 1) (j + 1) s h - FF pp PiM g b_fn (j + 1) j s h) := by
    have h1 := dFB_UO_local (by linarith [S.hη]) (by linarith [S.hη]) (S.exp.subset S.I_mid_sub)
      (g := g) (b := b_fn) (k := j + 1) (l := j) (fun i hi => C.g_reg i (by omega)) (fun i h1 h2 => C.b_reg i h1 (by omega))
    have hpa := (hpaFm'.mono (by omega : 2 * j + 1 + 1 ≤ 2 * K + 3)).sub (hpaFm.mono (by omega))
    exact PApproxOn.lift (n := 2 * j + 1) (σ := 1) (δ0 := 1)
      (by rw [(show Odd (2 * j + 1) from ⟨j, rfl⟩).neg_one_pow]; norm_num) hpa h1 one_pos
      (fun s _ h _ => by rw [one_mul, S.FF_even _ _ s h, S.FF_even _ _ s h])
  have hq2 : UOOn (Icc (a - η / 2) (b + η / 2)) (2 * j + 2)
      (fun s h => FF pp PiM g b_fn (j + 1) (j + 1) s h - Pc c (j + 1) h) :=
    (hF.add hΔ).congr fun s _ h => by ring
  refine ⟨hq0, ?_, hq2⟩
  have hAe := Aans_even g (j + 1)
  have hBe := Bans_even b_fn (j + 1)
  have hBD : UOOn (Icc a b) (2 * j + 2)
      (fun u h => h * Bans b_fn (j + 1) u h * defectRow pp qq (Aans g (j + 1)) (Bans b_fn (j + 1)) PiP PiM u h 0) := by
    have hh : UOOn (Icc a b) 1 (fun _ h => h) := (UOOn.hpow _ 1).congr fun _ _ _ => by simp
    exact ((hh.mul (C.Bans_bdd S (l := j + 1) hj)).mul hq0).mono (by omega)
  have h2 : UOOn (Icc a b) (2 * j + 2) (dB pp qq PiP PiM g b_fn (j + 1) (j + 1)) :=
    S.D1_bound (AA := Aans g (j + 1)) (BB := Bans b_fn (j + 1)) (C.lower S (by omega) (by omega)) hBD hq2
  exact S.D1_lift hAe hBe (n := 2 * j + 2) ⟨j + 1, by ring⟩ (hpaD1'.mono (by omega)) h2

private lemma QInvOn_to_PInvOn (S : LocalCorrSetting K a b η pp qq PiP PiM)
    (C : LocalCorrectors K a b η pp PiP PiM qq g b_fn c) {j : ℕ}
    (hj : j + 1 ≤ K) (hQ : QInvOn a b η pp qq PiP PiM g b_fn c j) :
    PInvOn a b η pp qq PiP PiM g b_fn c (j + 1) := by
  obtain ⟨hq0, _, hqF⟩ := hQ
  have hN4 : 2 * j + 4 ≤ 2 * K + 3 := by omega
  obtain ⟨_, hpaD1', _⟩ := S.ans_papprox_on C a b (by linarith [S.hη]) (by linarith [S.hη])
    (k := j + 2) (l := j + 1) (by omega) (by omega)
  obtain ⟨_, _, hpaFm⟩ := S.ans_papprox_on C (a - η / 2) (b + η / 2)
    (by linarith [S.hη]) (by linarith [S.hη]) (k := j + 1) (l := j + 1) (by omega) (by omega)
  obtain ⟨_, _, hpaFm'⟩ := S.ans_papprox_on C (a - η / 2) (b + η / 2)
    (by linarith [S.hη]) (by linarith [S.hη]) (k := j + 2) (l := j + 1) (by omega) (by omega)
  have hpaFP := (hpaFm.mono (by omega : 2 * j + 2 + 2 ≤ 2 * K + 3)).sub (Pc_papproxOn _ c (j + 1) _)
  obtain ⟨f_fn, _, hf_fn⟩ := PApproxOn.exists_coeff (n := 2 * j + 2) (σ := 1) (δ0 := 1)
    (by rw [(show Even (2 * j + 2) from ⟨j + 1, by ring⟩).neg_one_pow]; norm_num) hpaFP hqF one_pos
    (fun s _ h _ => by rw [one_mul, S.FF_even _ _ s h, Pc_even])
  have hfl : ∀ s ∈ Icc (a - η / 2) (b + η / 2), 2 * V0fun pp PiM s * g 0 s * g (j + 1) s = c (j + 1) - f_fn s := by
    refine C.flux (j + 1) (by omega) hj f_fn ?_
    have e : 2 * (j + 1) + 2 = 2 * j + 2 + 2 := by ring
    rw [e]
    refine hf_fn.congr fun u _ h => ?_
    rw [show 2 * (j + 1) = 2 * j + 2 by ring]
  have hbd : ∃ Cb, ∀ s ∈ Icc (a - η / 2) (b + η / 2), |2 * V0fun pp PiM s * g 0 s * g (j + 1) s| ≤ Cb := by
    obtain ⟨CV, δV, hδV, hV⟩ := ((S.exp.subset S.I_mid_sub).cM 0 1).bdd'
    obtain ⟨C0, h0⟩ := ((C.g_reg 0 (by omega)).subset S.I_mid_sub).bdd
    obtain ⟨C1, h1⟩ := ((C.g_reg (j + 1) hj).subset S.I_mid_sub).bdd
    refine ⟨2 * |CV| * |C0| * |C1|, fun s hs => ?_⟩
    have hv : |V0fun pp PiM s| ≤ |CV| := by
      have := hV s hs 0 (by simpa using hδV)
      simp only [V0fun]; simpa using this.trans (le_abs_self CV)
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    have a0 : |g 0 s| ≤ |C0| := (h0 s hs).trans (le_abs_self _)
    have a1 : |g (j + 1) s| ≤ |C1| := (h1 s hs).trans (le_abs_self _)
    have t1 : 2 * |V0fun pp PiM s| ≤ 2 * |CV| := by linarith
    exact mul_le_mul (mul_le_mul t1 a0 (abs_nonneg _) (by positivity)) a1 (abs_nonneg _) (by positivity)
  have hX1 := dFA_UO1_local (by linarith [S.hη]) (by linarith [S.hη]) (N := 2 * K + 3) (by omega)
    (S.exp.subset S.I_mid_sub) (g := g) (b := b_fn) (k := j + 1) (l := j + 1) (by omega)
    (fun i hi => C.g_reg i (by omega)) (fun i h1 h2 => C.b_reg i h1 (by omega))
  obtain ⟨Cb, hCb⟩ := hbd
  have hXpa : PApproxOn (Icc (a - η / 2) (b + η / 2)) (2 * (j + 1) + 1 + 1)
      (fun s h => Fcas pp (Aans g (j + 1 + 1)) (Bans b_fn (j + 1)) PiM s h
        - Fcas pp (Aans g (j + 1)) (Bans b_fn (j + 1)) PiM s h
        - h ^ (2 * (j + 1)) * (2 * V0fun pp PiM s * g 0 s * g (j + 1) s)) :=
    ((hpaFm'.mono (by omega)).sub (hpaFm.mono (by omega))).sub
      (PApproxOn.hpow_mul (2 * (j + 1))
        (PApproxOn.of_fun (I := Icc (a - η / 2) (b + η / 2)) (N := 2 * (j + 1) + 1 + 1)
          (fun s => 2 * V0fun pp PiM s * g 0 s * g (j + 1) s) hCb))
  have hX := PApproxOn.lift (n := 2 * (j + 1) + 1) (σ := 1) (δ0 := 1)
    (by rw [(show Odd (2 * (j + 1) + 1) from ⟨j + 1, rfl⟩).neg_one_pow]; norm_num) hXpa hX1 one_pos
    (fun s _ h _ => by
      have e1 := S.FF_even (g := g) (b_fn := b_fn) (j + 1 + 1) (j + 1) s h
      have e2 := S.FF_even (g := g) (b_fn := b_fn) (j + 1) (j + 1) s h
      simp only [FF] at e1 e2
      rw [one_mul, e1, e2]; simp [pow_mul])
  have hF2 : UOOn (Icc (a - η / 2) (b + η / 2)) (2 * (j + 1) + 2)
      (fun s h => FF pp PiM g b_fn (j + 1 + 1) (j + 1) s h - Pc c (j + 1 + 1) h) := by
    refine (hf_fn.add hX).congr fun s hs h => ?_
    simp only [FF, Pc_succ]
    have := hfl s hs
    linear_combination (-(h ^ (2 * (j + 1)))) * this
  have hlA := lA_UO2_local S.hη (N := 2 * K + 3) (by omega) (S.exp.subset S.I_in_sub) S.par_Pi S.pp_even S.qq_even
    (fun u hu => S.langer u (S.I_in_sub hu)) ((C.g_reg (j + 1) hj).mono (by omega))
  have hd0 : UOOn (Icc a b) (2 * (j + 1) + 2) (dA pp qq PiP PiM g b_fn (j + 1 + 1) (j + 1)) := by
    have := (hq0.mono (by omega : 2 * (j + 1) + 2 ≤ 2 * j + 4)).add (UOOn.hpow_mul (2 * (j + 1)) hlA)
    exact (this.mono (by omega)).congr fun u _ h => (dA_succ_A pp qq PiP PiM g b_fn (j + 1) (j + 1) u h).symm
  have hAe := Aans_even g (j + 1 + 1)
  have hBe := Bans_even b_fn (j + 1)
  have hBD : UOOn (Icc a b) (2 * (j + 1) + 2)
      (fun u h => h * Bans b_fn (j + 1) u h * defectRow pp qq (Aans g (j + 1 + 1)) (Bans b_fn (j + 1)) PiP PiM u h 0) := by
    have hh : UOOn (Icc a b) 1 (fun _ h => h) := (UOOn.hpow _ 1).congr fun _ _ _ => by simp
    exact ((hh.mul (C.Bans_bdd S (l := j + 1) hj)).mul hd0).mono (by omega)
  have h2 : UOOn (Icc a b) (2 * (j + 1) + 2) (dB pp qq PiP PiM g b_fn (j + 1 + 1) (j + 1)) :=
    S.D1_bound (AA := Aans g (j + 1 + 1)) (BB := Bans b_fn (j + 1))
      (C.lower S (by omega) (by omega)) hBD (P := Pc c (j + 1 + 1)) hF2
  exact ⟨hd0, S.D1_lift hAe hBe (n := 2 * (j + 1) + 2) ⟨j + 2, by ring⟩ (hpaD1'.mono (by omega)) h2, hF2⟩

theorem PInvOn_all (S : LocalCorrSetting K a b η pp qq PiP PiM)
    (C : LocalCorrectors K a b η pp PiP PiM qq g b_fn c) :
    ∀ j, j ≤ K → PInvOn a b η pp qq PiP PiM g b_fn c j := by
  intro j
  induction j with
  | zero => intro _; exact PInvOn_zero S C
  | succ j ih => intro hj; exact QInvOn_to_PInvOn S C (by omega) (PInvOn_to_QInvOn S C (by omega) (ih (by omega)))

theorem QInvOn_all (S : LocalCorrSetting K a b η pp qq PiP PiM)
    (C : LocalCorrectors K a b η pp PiP PiM qq g b_fn c) :
    ∀ j, j + 1 ≤ K → QInvOn a b η pp qq PiP PiM g b_fn c j :=
  fun j hj => PInvOn_to_QInvOn S C hj (PInvOn_all S C j (by omega))

theorem localized_eng_corr (S : LocalCorrSetting K a b η pp qq PiP PiM)
    (C : LocalCorrectors K a b η pp PiP PiM qq g b_fn c) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ 2 * K + 1) :
    (Odd m → UOOn (Icc a b) (m + 1) (fun u h => defectRow pp qq (Ahat g m) (Bhat b_fn m) PiP PiM u h 0) ∧
        UOOn (Icc a b) (m + 2) (fun u h => defectRow pp qq (Ahat g m) (Bhat b_fn m) PiP PiM u h 1)) ∧
    (Even m → UOOn (Icc a b) (m + 2) (fun u h => defectRow pp qq (Ahat g m) (Bhat b_fn m) PiP PiM u h 0) ∧
        UOOn (Icc a b) (m + 1) (fun u h => defectRow pp qq (Ahat g m) (Bhat b_fn m) PiP PiM u h 1)) := by
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨h0, h1, -⟩ := PInvOn_all S C j (by omega)
    rw [Ahat_odd, Bhat_odd]; exact ⟨h0, h1⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 2 := ⟨i - 1, by omega⟩
    obtain ⟨h0, h1, -⟩ := QInvOn_all S C j (by omega)
    rw [Ahat_even, Bhat_even]; exact ⟨h0, h1⟩

/-- **Localised `thm:eng-corr` with remainders `(eq:eng-factor)` on `[a, b]`**: under `LocalCorrSetting`
and `LocalCorrectors` on `[a - η, b + η]` and bounded remainders `RP, RQ` on `[a - η, b + η]`,
both defect components are `O(h^{m+1})` uniformly on `u ∈ [a, b]` (with `O(h^{m+2})` refinement for `m ≤ 2K`). -/
theorem localized_eng_corr_full (S : LocalCorrSetting K a b η pp qq PiP PiM)
    (C : LocalCorrectors K a b η pp PiP PiM qq g b_fn c)
    {RP RQ : ℝ → ℝ → ℝ} (hRP : UOOn (Icc (a - η) (b + η)) 0 RP) (hRQ : UOOn (Icc (a - η) (b + η)) 0 RQ)
    {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 2 * K + 1) :
    (∀ k : Fin 2, UOOn (Icc a b) (m + 1) (fun u h => defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h)
        (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h) (Ahat g m) (Bhat b_fn m) PiP PiM u h k)) ∧
    (m ≤ 2 * K →
      (Odd m → UOOn (Icc a b) (m + 1) (fun u h => defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h)
            (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h) (Ahat g m) (Bhat b_fn m) PiP PiM u h 0) ∧
          UOOn (Icc a b) (m + 2) (fun u h => defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h)
            (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h) (Ahat g m) (Bhat b_fn m) PiP PiM u h 1)) ∧
      (Even m → UOOn (Icc a b) (m + 2) (fun u h => defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h)
            (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h) (Ahat g m) (Bhat b_fn m) PiP PiM u h 0) ∧
          UOOn (Icc a b) (m + 1) (fun u h => defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h)
            (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h) (Ahat g m) (Bhat b_fn m) PiP PiM u h 1))) := by
  have hgk : ∀ i < (m + 1) / 2, BSmoothOn (Icc (a - η) (b + η)) (2 * K + 3) (g i) :=
    fun i hi => C.g_reg i (by omega)
  have hbl : ∀ i, 1 ≤ i → i ≤ m / 2 → BSmoothOn (Icc (a - η) (b + η)) (2 * K + 3) (b_fn i) :=
    fun i h1 h2 => C.b_reg i h1 (by omega)
  have Ap := (Aans_papprox_Icc (L := a - η) (R := b + η) (a' := a) (b' := b)
    (by linarith [S.hη]) (by linarith [S.hη]) hgk 1 (σ := fun u h => u + h) (fun _ _ => by ring)).bdd
  have Am := (Aans_papprox_Icc (L := a - η) (R := b + η) (a' := a) (b' := b)
    (by linarith [S.hη]) (by linarith [S.hη]) hgk (-1) (σ := fun u h => u - h) (fun _ _ => by ring)).bdd
  have A0 := (Aans_papprox_Icc (L := a - η) (R := b + η) (a' := a) (b' := b)
    (by linarith [S.hη]) (by linarith [S.hη]) hgk 0 (σ := fun u _ => u) (fun _ _ => by ring)).bdd
  have Bp := (Bans_papprox_Icc (L := a - η) (R := b + η) (a' := a) (b' := b)
    (by linarith [S.hη]) (by linarith [S.hη]) hbl 1 (σ := fun u h => u + h) (fun _ _ => by ring)).bdd
  have Bm := (Bans_papprox_Icc (L := a - η) (R := b + η) (a' := a) (b' := b)
    (by linarith [S.hη]) (by linarith [S.hη]) hbl (-1) (σ := fun u h => u - h) (fun _ _ => by ring)).bdd
  have B0 := (Bans_papprox_Icc (L := a - η) (R := b + η) (a' := a) (b' := b)
    (by linarith [S.hη]) (by linarith [S.hη]) hbl 0 (σ := fun u _ => u) (fun _ _ => by ring)).bdd
  have hSi := S.exp.subset S.I_in_sub
  have hRPp : UOOn (Icc a b) 0 (fun u h => RP (u + h / 2) h) :=
    (hRP.shift_Icc S.hη (1 / 2)).congr fun u _ h => by ring_nf
  have hRPm : UOOn (Icc a b) 0 (fun u h => RP (u - h / 2) h) :=
    (hRP.shift_Icc S.hη (-1 / 2)).congr fun u _ h => by ring_nf
  have hrem : ∀ k : Fin 2, UOOn (Icc a b) (2 * K + 2)
      (fun u h => defectRow (fun s h => h ^ (2 * K + 2) * RP s h)
        (fun u h => h ^ (2 * K + 2) * RQ u h) (Ahat g m) (Bhat b_fn m) PiP PiM u h k) :=
    fun k => defect_remainder_I hSi.bddP hSi.bddM (hRP.subset S.I_in_sub) (hRQ.subset S.I_in_sub)
      Ap Am A0 Bp Bm B0 hRPp hRPm k
  have hsplit : ∀ (k : Fin 2) (u h : ℝ),
      defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h) (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h)
        (Ahat g m) (Bhat b_fn m) PiP PiM u h k
      = defectRow pp qq (Ahat g m) (Bhat b_fn m) PiP PiM u h k
        + defectRow (fun s h => h ^ (2 * K + 2) * RP s h) (fun u h => h ^ (2 * K + 2) * RQ u h)
          (Ahat g m) (Bhat b_fn m) PiP PiM u h k := fun k u h =>
    defectRow_add_symbols (pp := pp) (pp' := fun s h => h ^ (2 * K + 2) * RP s h) (qq := qq)
      (qq' := fun u h => h ^ (2 * K + 2) * RQ u h) _ _ u h k
  have key : ∀ (k : Fin 2) (n : ℕ), n ≤ 2 * K + 2 →
      UOOn (Icc a b) n (fun u h => defectRow pp qq (Ahat g m) (Bhat b_fn m) PiP PiM u h k) →
      UOOn (Icc a b) n (fun u h => defectRow (fun s h => pp s h + h ^ (2 * K + 2) * RP s h)
        (fun u h => qq u h + h ^ (2 * K + 2) * RQ u h) (Ahat g m) (Bhat b_fn m) PiP PiM u h k) :=
    fun k n hn hs => (hs.add ((hrem k).mono hn)).congr fun u _ h => (hsplit k u h).symm
  obtain ⟨hodd, heven⟩ := localized_eng_corr S C hm1 hm
  refine ⟨fun k => ?_, fun hm2 => ⟨fun ho => ?_, fun he => ?_⟩⟩
  · rcases Nat.even_or_odd m with he | ho
    · obtain ⟨h0, h1⟩ := heven he
      fin_cases k
      · exact key 0 (m + 1) (by omega) (h0.mono (by omega))
      · exact key 1 (m + 1) (by omega) h1
    · obtain ⟨h0, h1⟩ := hodd ho
      fin_cases k
      · exact key 0 (m + 1) (by omega) h0
      · exact key 1 (m + 1) (by omega) (h1.mono (by omega))
  · obtain ⟨h0, h1⟩ := hodd ho
    exact ⟨key 0 (m + 1) (by omega) h0, key 1 (m + 2) (by omega) h1⟩
  · obtain ⟨h0, h1⟩ := heven he
    exact ⟨key 0 (m + 2) (by omega) h0, key 1 (m + 1) (by omega) h1⟩

end LocalMain

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.localized_eng_corr' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.localized_eng_corr

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.localized_eng_corr_full' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.localized_eng_corr_full

end FormalResearch.JacobiEigenvectors.Engine

end
