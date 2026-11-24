module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroTransferWindow
public import FormalResearch.ModularBootstrap.Upper.Window.Identification
public import FormalResearch.ModularBootstrap.Upper.Window.LemmaR
public import FormalResearch.ModularBootstrap.Upper.Design.PerturbP

/-!
# The `f = 2` comb dictionary of a two-simple-zero design (`upper_transfer.tex`, `ut:T2`, setup)

The comb `B₁` of `ut:T2` is the `f = 2` reference comb with its simple zero moved to `χ(q)` and the pairs
`3 ≤ k ≤ N = n + 2` moved to `χ(u_k) ± iλε_k/κ`, `χ(v) = ξ_* - λ v/κ`.  This module translates a
`TwoZeroDesign n` into the data of the `f`-general window machinery of `Upper.Window`:

* `TwoZeroDesign.toModified d : ModifiedCombData 2 (n + 2)`: `σ₂ = -q/κ`, `σ_k = -u_k/κ`, `ε̂_k = ε_k/κ`
  (constant in `c'`), `η₀ = 1/4`; `toModified_allSigmaLim`, `toModified_allEpsLim` identify the full limit
  sequences with the design's sites and widths (the reference ones beyond `N`).
* `TwoZeroDesign.designComb_eq_modifiedCombB`: `designComb c' 2 (n+2) (1/4) σ (λ ε̂) = modifiedCombB 2 (n+2) _ c'`
  for every `c'` (the `f = 1` analogue `sigComb_eq_modifiedCombB` needs a clipping threshold; here the widths are
  not clipped).
* `IsCompactFamily.exists_bound`, `toModifiedFamily`: a compact family of admissible designs is a
  `CompactCombFamily 2 (n + 2)` (`toModifiedFamily_mem`).
* `lemma_ID_modified`: `ut:ID` for any finite modification `ModifiedCombData f N`, every `f ≥ 1` (the `f`-general
  form of `lemma_ID_mod`); `tildeW_toModified`: `W̃^{±(2)}(σ) = C_*^{(2)} κ Re W^{(2)}(-κσ)` with
  `W^{(2)} = airyWindowProd 2 q (site) (width)`; `Wr_eq_neg_mul_re`, `tildeW_toModified_Wr`: `W_2 = -(u - p) W^{(2)}` and
  `W̃^{±(2)}(σ)(σ - σ_p) = C_* κ² W_2(-κσ)`.
* `lemma_R_lower_two`, `toModified_posLimitWidths`: admissibility gives `ε̂_k^* ≠ 0`, hence Lemma R at `f = 2`;
  `IsCompactFamily.exists_bound`, `exists_margins`: uniform bounds and margins `p - q, -q, -s_i, e_i ≥ c₀ > 0`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design

/-! ### `ut:ID` for finite modifications of every level `f` -/

/-- **Lemma ID (`ut:ID`), any level `f ≥ 1`, any finite modification** `ModifiedCombData f N` with
`η₀ ∈ [0, 1/4]`: `W̃^{±(f)}(σ) = C_*^{(f)} κ Re W^{(f)}(-κσ)`, `W^{(f)}` the Airy product with zero `-κ σ_f`,
sites `-κ σ_k` and widths `κ ε̂_k` (`k ≤ N`) and the reference tail. -/
theorem lemma_ID_modified (f N : ℕ) (hf : 1 ≤ f) (hN : f ≤ N) (dc : ModifiedCombData f N)
    (hη0 : 0 ≤ dc.eta0) (hη1 : dc.eta0 ≤ 1 / 4) (σ : ℝ) :
    tildeW f dc.sigmaFLim dc.allSigmaLim dc.allEpsLim σ =
      CStarF f * kappaAiry *
        (airyWindowProd f (-kappaAiry * dc.sigmaFLim) (fun k => -kappaAiry * dc.allSigmaLim k)
          (fun k => kappaAiry * dc.allEpsLim k) ((-kappaAiry * σ : ℝ) : ℂ)).re := by
  set M : ℝ := |dc.sigmaFLim| + 1 +
    (Finset.Icc (f + 1) N).sum (fun k => |dc.allSigmaLim k| + |dc.allEpsLim k|)
  have hs : 0 ≤ (Finset.Icc (f + 1) N).sum (fun k => |dc.allSigmaLim k| + |dc.allEpsLim k|) :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hσf : |dc.sigmaFLim| ≤ M := by dsimp [M]; linarith
  have hmod : ∀ k ∈ Finset.Icc (f + 1) N, |dc.allSigmaLim k| ≤ M ∧ |dc.allEpsLim k| ≤ M := by
    intro k hk
    have hle := Finset.single_le_sum (f := fun j => |dc.allSigmaLim j| + |dc.allEpsLim j|)
      (fun _ _ => by positivity) hk
    constructor <;> dsimp [M] <;>
      linarith [abs_nonneg dc.sigmaFLim, abs_nonneg (dc.allSigmaLim k), abs_nonneg (dc.allEpsLim k)]
  exact lemma_ID f N hf hN hM one_pos hσf hmod (dc.tail_bound_all hη0 hη1) σ

namespace TwoZeroDesign

variable {n : ℕ}

/-! ### The dictionary -/

/-- The scaled zero `σ₂ = -q/κ`. -/
noncomputable def sigmaF (d : TwoZeroDesign n) : ℝ := -d.q / kappaAiry

/-- The scaled sites `σ_k = -u_k/κ` (`k ≥ 3`). -/
noncomputable def sigmaSite (d : TwoZeroDesign n) (k : ℕ) : ℝ := -d.site k / kappaAiry

/-- The scaled half-widths `ε̂_k = ε_k/κ` (`k ≥ 3`). -/
noncomputable def epsHatSite (d : TwoZeroDesign n) (k : ℕ) : ℝ := d.width k / kappaAiry

/-- The full scaled sequence: `σ₂ = -q/κ`, `σ_k = -u_k/κ` otherwise (input of `designComb`). -/
noncomputable def sigmaSeq (d : TwoZeroDesign n) (k : ℕ) : ℝ := if k = 2 then d.sigmaF else d.sigmaSite k

/-- The comb `B₁` of `ut:T2` as `ModifiedCombData 2 (n + 2)`. -/
noncomputable def toModified (d : TwoZeroDesign n) : ModifiedCombData 2 (n + 2) where
  sigmaF _ := d.sigmaF
  sigmaK _ k := d.sigmaSite k
  epsHat _ k := d.epsHatSite k
  eta0 := 1 / 4
  sigmaFLim := d.sigmaF
  sigmaKLim k := d.sigmaSite k
  epsHatLim k := d.epsHatSite k

lemma toModified_eta0_nonneg (d : TwoZeroDesign n) : 0 ≤ d.toModified.eta0 := by
  show (0 : ℝ) ≤ 1 / 4; norm_num

lemma toModified_eta0_le (d : TwoZeroDesign n) : d.toModified.eta0 ≤ 1 / 4 := le_rfl

lemma toModified_allSigmaLim (d : TwoZeroDesign n) {k : ℕ} (_hk : 2 < k) :
    -kappaAiry * d.toModified.allSigmaLim k = d.site k := by
  have hκ := kappaAiry_pos
  unfold ModifiedCombData.allSigmaLim
  by_cases hkN : k ≤ n + 2
  · simp only [hkN, ↓reduceIte]
    show -kappaAiry * (-d.site k / kappaAiry) = d.site k
    field_simp
  · simp only [hkN, ↓reduceIte]
    rw [d.site_of_gt (by omega)]
    rfl

lemma toModified_allEpsLim (d : TwoZeroDesign n) {k : ℕ} (_hk : 2 < k) :
    kappaAiry * d.toModified.allEpsLim k = d.width k := by
  have hκ := kappaAiry_pos
  unfold ModifiedCombData.allEpsLim
  by_cases hkN : k ≤ n + 2
  · simp only [hkN, ↓reduceIte]
    show kappaAiry * (d.width k / kappaAiry) = d.width k
    field_simp
  · simp only [hkN, ↓reduceIte]
    rw [d.width_of_gt (by omega)]
    show kappaAiry * (1 / 4 * (phiWKB (k + 1) - phiWKB k)) = 1 / 4 * gapWKB k
    unfold gapWKB uWKB
    ring

lemma toModified_sigmaFLim (d : TwoZeroDesign n) : -kappaAiry * d.toModified.sigmaFLim = d.q := by
  have hκ := kappaAiry_pos
  show -kappaAiry * (-d.q / kappaAiry) = d.q
  field_simp

/-- The Airy window of the zero/sites/widths of a design. -/
noncomputable def P (d : TwoZeroDesign n) (u : ℂ) : ℂ := airyWindowProd 2 d.q d.site d.width u

/-- The Airy product of the dictionary data equals `W^{(2)} = airyWindowProd 2 q (site) (width)`. -/
lemma airyWindowProd_toModified (d : TwoZeroDesign n) (u : ℂ) :
    airyWindowProd 2 (-kappaAiry * d.toModified.sigmaFLim) (fun k => -kappaAiry * d.toModified.allSigmaLim k)
      (fun k => kappaAiry * d.toModified.allEpsLim k) u = d.P u := by
  rw [d.toModified_sigmaFLim]
  exact airyWindowProd_congr (fun k hk => d.toModified_allSigmaLim hk) (fun k hk => d.toModified_allEpsLim hk) u

/-- **`ut:ID` at `f = 2` for the design comb** (`ut:T2`, Region I): `W̃^{±(2)}(σ) = C_*^{(2)} κ Re W^{(2)}(-κσ)`,
`C_*^{(2)} = C_* κ²`, `W^{(2)}(u) = airyWindowProd 2 q (u_k) (ε_k)`. -/
theorem tildeW_toModified (d : TwoZeroDesign n) (σ : ℝ) :
    tildeW 2 d.toModified.sigmaFLim d.toModified.allSigmaLim d.toModified.allEpsLim σ =
      CStarF 2 * kappaAiry * (d.P ((-kappaAiry * σ : ℝ) : ℂ)).re := by
  rw [lemma_ID_modified 2 (n + 2) (by norm_num) (by omega) d.toModified d.toModified_eta0_nonneg
    d.toModified_eta0_le σ, airyWindowProd_toModified]

lemma CStarF_two : CStarF 2 = CStar * kappaAiry ^ 2 := by
  unfold CStarF
  have : (2 * (((2 : ℕ) : ℤ) - 1)) = 2 := by norm_num
  rw [this]; rfl

/-- `W_2(u) = -(u - p) W^{(2)}(u)` for real `u`, on real parts. -/
lemma Wr_eq_neg_mul_re (d : TwoZeroDesign n) (u : ℝ) : d.Wr u = -(u - d.p) * (d.P (u : ℂ)).re := by
  unfold Wr W P
  have : (-((u : ℂ) - (d.p : ℂ))) = ((-(u - d.p) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.re_ofReal_mul]

/-- The window of the comb `T_{χ(p)} B₁` (`ut:T2`, Region I): `W̃^{±(2)}(σ) (σ - σ_p) = C_* κ² W_2(-κσ)`,
`σ_p = -p/κ`, `W_2 = -(u - p) W^{(2)}` (the zero factor `T_{χ(p)} ≈ (πλ/(2√2))(σ - σ_p)`). -/
theorem tildeW_toModified_Wr (d : TwoZeroDesign n) (σ : ℝ) :
    tildeW 2 d.toModified.sigmaFLim d.toModified.allSigmaLim d.toModified.allEpsLim σ *
        (σ - (-d.p / kappaAiry)) = CStar * kappaAiry ^ 2 * d.Wr (-kappaAiry * σ) := by
  have hκ := kappaAiry_pos
  rw [tildeW_toModified, Wr_eq_neg_mul_re, CStarF_two]
  have : σ - (-d.p / kappaAiry) = -(-kappaAiry * σ - d.p) / kappaAiry := by
    field_simp; ring
  rw [this]; field_simp

/-! ### Uniform bounds on a compact family -/

lemma site_mem (d : TwoZeroDesign n) {k : ℕ} (h3 : 3 ≤ k) (hk : k ≤ n + 2) :
    ∃ i, d.site k = d.s i ∧ d.width k = d.e i := by
  refine ⟨⟨k - 3, by omega⟩, ?_, ?_⟩
  · unfold site; simp only [show 3 ≤ k ∧ k ≤ n + 2 from ⟨h3, hk⟩, and_self, dite_true]
  · unfold width; simp only [show 3 ≤ k ∧ k ≤ n + 2 from ⟨h3, hk⟩, and_self, dite_true]

/-- A compact family of designs has uniformly bounded parameters. -/
lemma IsCompactFamily.exists_bound {𝒦 : Set (TwoZeroDesign n)} (h : IsCompactFamily 𝒦) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ d ∈ 𝒦, |d.p| ≤ R ∧ |d.q| ≤ R ∧ ∀ i, |d.s i| ≤ R ∧ |d.e i| ≤ R := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 h.isBounded
  refine ⟨max C 0, le_max_right _ _, fun d hd => ?_⟩
  have h1 : ‖toTuple d‖ ≤ C := hC _ ⟨d, hd, rfl⟩
  have h2 : C ≤ max C 0 := le_max_left _ _
  have ht : toTuple d = (d.p, d.q, d.s, d.e) := rfl
  rw [ht] at h1
  have hp : ‖d.p‖ ≤ ‖(d.p, d.q, d.s, d.e)‖ := by
    simp
  have hq : ‖d.q‖ ≤ ‖(d.p, d.q, d.s, d.e)‖ :=
    (norm_fst_le (d.q, d.s, d.e)).trans (norm_snd_le (d.p, d.q, d.s, d.e))
  have hs : ∀ i, ‖d.s i‖ ≤ ‖(d.p, d.q, d.s, d.e)‖ := fun i =>
    (norm_le_pi_norm d.s i).trans ((norm_fst_le (d.s, d.e)).trans
      ((norm_snd_le (d.q, d.s, d.e)).trans (norm_snd_le (d.p, d.q, d.s, d.e))))
  have he : ∀ i, ‖d.e i‖ ≤ ‖(d.p, d.q, d.s, d.e)‖ := fun i =>
    (norm_le_pi_norm d.e i).trans ((norm_snd_le (d.s, d.e)).trans
      ((norm_snd_le (d.q, d.s, d.e)).trans (norm_snd_le (d.p, d.q, d.s, d.e))))
  refine ⟨?_, ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [← Real.norm_eq_abs]; linarith
  · rw [← Real.norm_eq_abs]; linarith
  · rw [← Real.norm_eq_abs]; linarith [hs i]
  · rw [← Real.norm_eq_abs]; linarith [he i]

/-- A compact family of admissible designs has uniform margins: `p - q`, `-q`, `-s_i`, `e_i ≥ c₀ > 0`. -/
lemma IsCompactFamily.exists_margins {𝒦 : Set (TwoZeroDesign n)} (h : IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ d ∈ 𝒦, c₀ ≤ d.p - d.q ∧ c₀ ≤ -d.q ∧ ∀ i, c₀ ≤ -d.s i ∧ c₀ ≤ d.e i := by
  set H : ℝ × ℝ × (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun t =>
    (t.1 - t.2.1)⁻¹ + (-t.2.1)⁻¹ + ∑ i, (-t.2.2.1 i)⁻¹ + ∑ i, (t.2.2.2 i)⁻¹ with hH
  have hS : ∀ t ∈ toTuple '' 𝒦, 0 < t.1 - t.2.1 ∧ 0 < -t.2.1 ∧ (∀ i, 0 < -t.2.2.1 i) ∧ ∀ i, 0 < t.2.2.2 i := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨h1, h2, h3, _, h5⟩ := hA d hd
    exact ⟨by simp only [toTuple]; linarith, by simp only [toTuple]; linarith,
      fun i => by simp only [toTuple]; linarith [h3 i], h5⟩
  have hcont : ContinuousOn H (toTuple '' 𝒦) := by
    refine ((((ContinuousOn.inv₀ (by fun_prop) fun t ht => (hS t ht).1.ne').add
      (ContinuousOn.inv₀ (by fun_prop) fun t ht => (hS t ht).2.1.ne')).add
      (continuousOn_finsetSum _ fun i _ => ContinuousOn.inv₀ (by fun_prop)
        fun t ht => (hS t ht).2.2.1 i |>.ne')).add
      (continuousOn_finsetSum _ fun i _ => ContinuousOn.inv₀ (by fun_prop)
        fun t ht => (hS t ht).2.2.2 i |>.ne'))
  obtain ⟨B, hB⟩ := h.exists_bound_of_continuousOn hcont
  have hB1 : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨1 / max B 1, by positivity, fun d hd => ?_⟩
  have hmem : toTuple d ∈ toTuple '' 𝒦 := ⟨d, hd, rfl⟩
  obtain ⟨p1, p2, p3, p4⟩ := hS _ hmem
  have hHle : H (toTuple d) ≤ max B 1 := (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB _ hmem).trans (le_max_left _ _))
  have t1 : 0 ≤ (toTuple d).1 - (toTuple d).2.1 := p1.le
  have hsum1 : 0 ≤ ∑ i, (-(toTuple d).2.2.1 i)⁻¹ := Finset.sum_nonneg fun i _ => inv_nonneg.2 (p3 i).le
  have hsum2 : 0 ≤ ∑ i, ((toTuple d).2.2.2 i)⁻¹ := Finset.sum_nonneg fun i _ => inv_nonneg.2 (p4 i).le
  have hinv : ∀ x : ℝ, 0 < x → x⁻¹ ≤ max B 1 → 1 / max B 1 ≤ x := fun x hx hle => by
    rw [div_le_iff₀ hB1]
    have := mul_le_mul_of_nonneg_left hle hx.le
    rw [mul_inv_cancel₀ hx.ne'] at this
    linarith
  have a1 : ((toTuple d).1 - (toTuple d).2.1)⁻¹ ≤ max B 1 := by
    have : 0 ≤ (-(toTuple d).2.1)⁻¹ := inv_nonneg.2 p2.le
    simp only [hH] at hHle; linarith
  have a2 : (-(toTuple d).2.1)⁻¹ ≤ max B 1 := by
    have : 0 ≤ ((toTuple d).1 - (toTuple d).2.1)⁻¹ := inv_nonneg.2 p1.le
    simp only [hH] at hHle; linarith
  refine ⟨hinv _ p1 a1, hinv _ p2 a2, fun i => ⟨?_, ?_⟩⟩
  · refine hinv _ (p3 i) ?_
    show (-(toTuple d).2.2.1 i)⁻¹ ≤ _
    have h1 := Finset.single_le_sum (f := fun i => (-(toTuple d).2.2.1 i)⁻¹)
      (fun i _ => inv_nonneg.2 (p3 i).le) (Finset.mem_univ i)
    have : 0 ≤ ((toTuple d).1 - (toTuple d).2.1)⁻¹ := inv_nonneg.2 p1.le
    have : 0 ≤ (-(toTuple d).2.1)⁻¹ := inv_nonneg.2 p2.le
    simp only [hH] at hHle; linarith
  · refine hinv _ (p4 i) ?_
    show ((toTuple d).2.2.2 i)⁻¹ ≤ _
    have h1 := Finset.single_le_sum (f := fun i => ((toTuple d).2.2.2 i)⁻¹)
      (fun i _ => inv_nonneg.2 (p4 i).le) (Finset.mem_univ i)
    have : 0 ≤ ((toTuple d).1 - (toTuple d).2.1)⁻¹ := inv_nonneg.2 p1.le
    have : 0 ≤ (-(toTuple d).2.1)⁻¹ := inv_nonneg.2 p2.le
    simp only [hH] at hHle; linarith

end TwoZeroDesign

/-! ### The compact family -/

/-- The finite and limit bounds of `CompactCombFamily` for one admissible design with parameters bounded by `R`. -/
lemma TwoZeroDesign.toModified_bounds {n : ℕ} (d : TwoZeroDesign n) (hd : d.Adm) {R : ℝ}
    (hq : |d.q| ≤ R) (hse : ∀ i, |d.s i| ≤ R ∧ |d.e i| ≤ R) :
    |d.sigmaF| ≤ R / kappaAiry + 1 ∧ ∀ k ∈ Finset.Icc (2 + 1) (n + 2),
      |d.sigmaSite k| ≤ R / kappaAiry + 1 ∧ 0 ≤ d.epsHatSite k ∧ d.epsHatSite k ≤ R / kappaAiry + 1 := by
  have hκ := kappaAiry_pos
  have hdiv : ∀ x : ℝ, |x| ≤ R → |x| / kappaAiry ≤ R / kappaAiry + 1 := fun x hx =>
    (div_le_div_of_nonneg_right hx hκ.le).trans (by linarith)
  refine ⟨?_, fun k hk => ?_⟩
  · show |-d.q / kappaAiry| ≤ _
    rw [abs_div, abs_neg, abs_of_pos hκ]
    exact hdiv _ hq
  · obtain ⟨h3, hkN⟩ := Finset.mem_Icc.1 hk
    obtain ⟨i, hi1, hi2⟩ := d.site_mem h3 hkN
    refine ⟨?_, ?_, ?_⟩
    · show |-d.site k / kappaAiry| ≤ _
      rw [abs_div, abs_neg, abs_of_pos hκ, hi1]
      exact hdiv _ (hse i).1
    · show 0 ≤ d.width k / kappaAiry
      rw [hi2]; exact (div_pos (hd.2.2.2.2 i) hκ).le
    · show d.width k / kappaAiry ≤ _
      rw [hi2]
      have := hdiv _ (hse i).2
      rwa [abs_of_pos (hd.2.2.2.2 i)] at this

/-- A compact family of admissible two-simple-zero designs as a `CompactCombFamily 2 (n + 2)`
(`ut:W`/`ut:P(b)` hypotheses): all data are constant in `c'`, bounded by `R/κ + 1`. -/
noncomputable def TwoZeroDesign.toModifiedFamily {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : TwoZeroDesign.IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) : CompactCombFamily 2 (n + 2) where
  members := TwoZeroDesign.toModified '' 𝒦
  hf := by norm_num
  hN := by omega
  M := (TwoZeroDesign.IsCompactFamily.exists_bound hK).choose / kappaAiry + 1
  hM := by
    have := (TwoZeroDesign.IsCompactFamily.exists_bound hK).choose_spec.1
    have := kappaAiry_pos
    positivity
  eta0_bounds := by
    rintro _ ⟨d, _, rfl⟩
    exact ⟨d.toModified_eta0_nonneg, d.toModified_eta0_le⟩
  finite_bounds := by
    rintro _ ⟨d, hd, rfl⟩ c' _
    obtain ⟨hp, hq, hse⟩ := (TwoZeroDesign.IsCompactFamily.exists_bound hK).choose_spec.2 d hd
    exact d.toModified_bounds (hA d hd) hq hse
  lim_bounds := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨hp, hq, hse⟩ := (TwoZeroDesign.IsCompactFamily.exists_bound hK).choose_spec.2 d hd
    exact d.toModified_bounds (hA d hd) hq hse
  uniform_tendsto := by
    intro ε hε
    refine ⟨1, one_pos, fun _ d hd => ?_⟩
    rcases hd with ⟨d, _, rfl⟩
    simp [TwoZeroDesign.toModified, hε.le]

lemma TwoZeroDesign.toModifiedFamily_mem {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : TwoZeroDesign.IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) {d : TwoZeroDesign n} (hd : d ∈ 𝒦) :
    d.toModified ∈ (TwoZeroDesign.toModifiedFamily hK hA).members := ⟨d, hd, rfl⟩

/-! ### The comb itself -/

/-- The design comb `B₁` of `ut:T2`, `designComb c' 2 (n+2) (1/4)` with sites `χ(u_k) = ξ_* + λ σ_k` and
half-widths `λ ε̂_k = λ ε_k/κ` (the TeX's `λ ε_k/κ`). -/
noncomputable def TwoZeroDesign.comb {n : ℕ} (d : TwoZeroDesign n) (c' : ℝ) (b : ℂ) : ℂ :=
  designComb c' 2 (n + 2) (1 / 4) d.sigmaSeq (fun k => lambdaComb c' * d.epsHatSite k) b

/-- `B₁ = modifiedCombB 2 (n+2) (toModified d)` for every `c'`: the design comb is the `f = 2` finite modification
of the reference comb. -/
theorem TwoZeroDesign.comb_eq_modifiedCombB {n : ℕ} (d : TwoZeroDesign n) (c' : ℝ) (z : ℂ) :
    d.comb c' z = modifiedCombB 2 (n + 2) d.toModified c' z := by
  unfold TwoZeroDesign.comb designComb modifiedCombB
  have hprod : (∏ i ∈ Finset.range (n + 2 - 2), pairT (designSite c' d.sigmaSeq (2 + 1 + i))
        (lambdaComb c' * d.epsHatSite (2 + 1 + i)) z) =
      ∏ k ∈ Finset.Icc (2 + 1) (n + 2),
        blaschkeT (((xiStar + lambdaComb c' * d.toModified.sigmaK c' k : ℝ) : ℂ) +
          ((lambdaComb c' * d.toModified.epsHat c' k : ℝ) : ℂ) * Complex.I) z *
        blaschkeT (((xiStar + lambdaComb c' * d.toModified.sigmaK c' k : ℝ) : ℂ) -
          ((lambdaComb c' * d.toModified.epsHat c' k : ℝ) : ℂ) * Complex.I) z := by
    have hIcc : Finset.Icc (2 + 1) (n + 2) = Finset.Ico (2 + 1) (n + 2 + 1) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIcc, Finset.prod_Ico_eq_prod_range]
    have hlen : n + 2 + 1 - (2 + 1) = n + 2 - 2 := by omega
    rw [hlen]
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold pairT designSite sigmaSeq
    simp only [show 2 + 1 + i ≠ 2 by omega, ↓reduceIte]
    rfl
  rw [hprod]
  rfl

/-! ### Admissibility transported -/

/-- Admissible designs have non-zero limit widths (`ε̂_k^* ≠ 0`, `k > 2`) in the dictionary. -/
lemma TwoZeroDesign.toModified_posLimitWidths {n : ℕ} (d : TwoZeroDesign n) (hd : d.Adm) :
    PosLimitWidths d.toModified := fun k hk h0 => by
  have h := d.toModified_allEpsLim hk
  rw [h0, mul_zero] at h
  exact d.width_ne_zero hd hk h.symm

/-- **Lemma R at `f = 2`** (`ut:R`, used for `ut:T2` Region I, `(σ - σ_q)` divided out): for every admissible design
of a compact family there are `w₀ > 0` and `C₀` with `h₀ e^{c'L} ≥ K̃_c^{(2)} w₀ (σ - σ_q)` for `c' ≥ C₀`,
`σ_q < σ ≤ Σ₀`, `x = ξ_* + λσ`, for the comb `B₁` without the factor `T_{χ(p)}`. -/
theorem TwoZeroDesign.lemma_R_lower_two {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : TwoZeroDesign.IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) {d : TwoZeroDesign n} (hd : d ∈ 𝒦)
    (Sg0 : ℝ) :
    ∃ w0 : ℝ, 0 < w0 ∧ ∃ C₀ : ℝ, ∀ {c' : ℝ}, C₀ ≤ c' → ∀ σ : ℝ, d.sigmaF < σ → σ ≤ Sg0 →
      windowNormKTilde 2 c' * w0 * (σ - d.sigmaF) ≤
        modifiedH0 2 (n + 2) d.toModified c' (xiStar + lambdaComb c' * σ) *
          Real.exp (c' * slitL (xiStar + lambdaComb c' * σ)) :=
  lemma_R_lower (TwoZeroDesign.toModifiedFamily hK hA) (TwoZeroDesign.toModifiedFamily_mem hK hA hd)
    (d.toModified_posLimitWidths (hA d hd)) Sg0

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.lemma_ID_modified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_ID_modified

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDesign.tildeW_toModified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoZeroDesign.tildeW_toModified

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDesign.tildeW_toModified_Wr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoZeroDesign.tildeW_toModified_Wr

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDesign.comb_eq_modifiedCombB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoZeroDesign.comb_eq_modifiedCombB

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDesign.toModifiedFamily_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoZeroDesign.toModifiedFamily_mem

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDesign.IsCompactFamily.exists_margins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoZeroDesign.IsCompactFamily.exists_margins

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDesign.lemma_R_lower_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoZeroDesign.lemma_R_lower_two

end FormalResearch.ModularBootstrap.TwoLevel
