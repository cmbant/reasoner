module

public import FormalResearch.ModularBootstrap.LP.Moments
public import FormalResearch.Measure.PolyGrowthExtension
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Lemma LP-P (`dsl:poly-compact`): shared polynomial moment compactness

`CFT/modular_bootstrap/paper/dual_spectrum_limit.tex`, Lemma LP-P, for an abstract odd family.  Let `X`
be a locally compact Hausdorff space, `t : X → [T₀, ∞)` continuous and proper, `p_j` a family with the
bounds of `ds:mom` (`OddFam C p`), `V_1 ⊂ V_3 ⊂ ⋯` spaces of continuous functions with
`|q| ≤ C_q (1 + t)^N` on `V_N`, containing `p_j ∘ t` for odd `j ≤ N`, and a function `p₀ ∈ V_{N₀}`
with `p₀ ≥ η > 0`.  If `L` is a linear functional on `V = ⋃ V_N`, positive on `X`, with
`L(p_j ∘ t) = ∫ p_j dμ₀` for all odd `j`, where `∫ e^{π t} dμ₀ < ∞`, then
`L = ∫ · dμ` for a positive Radon measure `μ` on `X` with `∫ e^{ε t} dμ < ∞` for some `ε > 0`; if a
finite group acts continuously on `X` preserving `t`, every `V_N` and `L`, `μ` may be taken invariant.

The monic Laguerre family is the instance `lagP_oddFam`.  Proof as in the paper: coercive majorants
`h_N = p_N ∘ t + ((B_N + 1)/η) p₀` (`exists_coercive`, from the lower growth bound), the
positive extension and Riesz-Markov packaging of `FormalResearch.Measure.PolyGrowthExtension`, and
`ds:mom` (`LP.Moments`) for the exponential moment.  The chain is indexed by `ℕ` and only its odd
indices are used.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open FormalResearch.Measure

namespace FormalResearch.ModularBootstrap.LP

variable {X : Type*} [TopologicalSpace X]

/-- `p_j ∘ t` as a continuous function on `X`. -/
def pc (p : ℕ → C(ℝ, ℝ)) (j : ℕ) (t : C(X, ℝ)) : C(X, ℝ) := (p j).comp t

@[simp] lemma pc_apply (p : ℕ → C(ℝ, ℝ)) (j : ℕ) (t : C(X, ℝ)) (x : X) : pc p j t x = p j (t x) := rfl

/-- The union `⋃_{N odd} V_N` of the chain, as a submodule. -/
def polyUnion (V : ℕ → Submodule ℝ C(X, ℝ)) : Submodule ℝ C(X, ℝ) :=
  ⨆ N : {N : ℕ // Odd N}, V N.1

lemma mem_polyUnion {V : ℕ → Submodule ℝ C(X, ℝ)}
    (hmono : ∀ M N, Odd M → Odd N → M ≤ N → V M ≤ V N) {q : C(X, ℝ)} :
    q ∈ polyUnion V ↔ ∃ N, Odd N ∧ q ∈ V N := by
  unfold polyUnion
  have : Nonempty {N : ℕ // Odd N} := ⟨⟨1, odd_one⟩⟩
  rw [Submodule.mem_iSup_of_directed]
  · constructor
    · rintro ⟨⟨N, hN⟩, hq⟩; exact ⟨N, hN, hq⟩
    · rintro ⟨N, hN, hq⟩; exact ⟨⟨N, hN⟩, hq⟩
  · intro a b
    rcases le_total a.1 b.1 with h | h
    · exact ⟨b, hmono _ _ a.2 b.2 h, le_rfl⟩
    · exact ⟨a, le_rfl, hmono _ _ b.2 a.2 h⟩

lemma le_polyUnion {V : ℕ → Submodule ℝ C(X, ℝ)} {N : ℕ} (hN : Odd N) : V N ≤ polyUnion V :=
  le_iSup (fun N : {N : ℕ // Odd N} => V N.1) ⟨N, hN⟩

/-- Hypotheses (i)-(iii) of `dsl:poly-compact`, for the family `p` with constant `C`, the bound `T₀`,
the coordinate `t` and the chain `V` (indexed by `ℕ`; only odd indices are used). -/
structure PolyCompactHyp (C : ℝ) (p : ℕ → C(ℝ, ℝ)) (T₀ : ℝ) (t : C(X, ℝ))
    (V : ℕ → Submodule ℝ C(X, ℝ)) : Prop where
  fam : OddFam C p
  T₀_nonneg : 0 ≤ T₀
  t_ge : ∀ x, T₀ ≤ t x
  t_proper : IsProperMap t
  mono : ∀ M N, Odd M → Odd N → M ≤ N → V M ≤ V N
  /-- (i) polynomial growth `|q| ≤ C_q (1 + t)^N` on `V_N`. -/
  growth : ∀ N, Odd N → ∀ q ∈ V N, ∃ C : ℝ, ∀ x, |q x| ≤ C * (1 + t x) ^ N
  /-- (ii) `V_N ∋ p_j ∘ t` for odd `j ≤ N`. -/
  contains : ∀ N, Odd N → ∀ j, Odd j → j ≤ N → pc p j t ∈ V N
  /-- (iii) a positive majorant `p₀ ∈ V_{N₀}` with `p₀ ≥ η > 0` on `X`. -/
  majorant : ∃ (N₀ : ℕ) (p₀ : C(X, ℝ)) (η : ℝ), Odd N₀ ∧ p₀ ∈ V N₀ ∧ 0 < η ∧ ∀ x, η ≤ p₀ x

namespace PolyCompactHyp

variable {C T₀ : ℝ} {p : ℕ → C(ℝ, ℝ)} {t : C(X, ℝ)} {V : ℕ → Submodule ℝ C(X, ℝ)}

lemma t_nonneg (h : PolyCompactHyp C p T₀ t V) (x : X) : 0 ≤ t x := h.T₀_nonneg.trans (h.t_ge x)

lemma compact_le (h : PolyCompactHyp C p T₀ t V) (R : ℝ) : IsCompact {x | |t x| ≤ R} := by
  have := h.t_proper.isCompact_preimage (isCompact_Icc : IsCompact (Icc (-R) R))
  convert this using 1
  ext x; simp [abs_le]

lemma pc_mem (h : PolyCompactHyp C p T₀ t V) {j : ℕ} (hj : Odd j) :
    pc p j t ∈ polyUnion V :=
  le_polyUnion hj (h.contains j hj j hj le_rfl)

lemma union_le_polyGrowth (h : PolyCompactHyp C p T₀ t V) : polyUnion V ≤ polyGrowth t := by
  intro q hq
  obtain ⟨N, hN, hqN⟩ := (mem_polyUnion h.mono).1 hq
  obtain ⟨C, hC⟩ := h.growth N hN q hqN
  exact ⟨C, N, fun x => by rw [abs_of_nonneg (h.t_nonneg x)]; exact hC x⟩

end PolyCompactHyp

/-- Lower bound for an odd family on the whole ray `[0, ∞)`: `p_N ≥ -(3CN)^N`. -/
lemma OddFam.ge_neg {C : ℝ} {p : ℕ → C(ℝ, ℝ)} (hF : OddFam C p) {N : ℕ} (hN : Odd N) {s : ℝ}
    (hs : 0 ≤ s) : -((3 * C * N) ^ N) ≤ p N s := by
  have hC := hF.C_pos
  have hBnn : 0 ≤ (3 * C * N) ^ N := by positivity
  rcases le_total (2 * C * N) s with h | h
  · have := hF.lower N hN s h
    have : 0 ≤ (s / 2) ^ N := by positivity
    linarith only [this, ‹(s / 2) ^ N ≤ p N s›, hBnn]
  · have h1 := hF.upper N hN s hs
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN.pos
    have h2 : (s + C * N) ^ N ≤ (3 * C * N) ^ N := by
      gcongr; nlinarith only [h, hC, hN1]
    have := neg_abs_le (p N s)
    linarith only [h1, h2, this]

namespace PolyCompactHyp

variable {C T₀ : ℝ} {p : ℕ → C(ℝ, ℝ)} {t : C(X, ℝ)} {V : ℕ → Submodule ℝ C(X, ℝ)}

/-- Coercive majorants: for every `k` there is `h ∈ ⋃ V_N` with `(1 + |t|)^k ≤ h`
(`h_N = p_N ∘ t + ((B_N + 1)/η) p₀`, up to a constant; the lower growth bound of `OddFam`). -/
lemma exists_coercive (h : PolyCompactHyp C p T₀ t V) (k : ℕ) :
    ∃ q ∈ polyUnion V, ∀ x, (1 + |t x|) ^ k ≤ q x := by
  obtain ⟨N₀, p₀, η, hN₀, hp₀, hη, hp₀η⟩ := h.majorant
  have hF := h.fam
  have hC := hF.C_pos
  set N : ℕ := 2 * max k N₀ + 1 with hN
  have hNodd : Odd N := ⟨max k N₀, by rw [hN]⟩
  have hkN : k ≤ N := by have := le_max_left k N₀; omega
  have hN₀N : N₀ ≤ N := by have := le_max_right k N₀; omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNodd.pos
  set s₀ : ℝ := 2 * C * N with hs₀
  set B : ℝ := (3 * C * N) ^ N with hB
  have hs₀pos : 0 < s₀ := by rw [hs₀]; positivity
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  set Cc : ℝ := (1 + s₀) ^ N + (2 * (1 + 1 / s₀)) ^ N with hCc
  have hCcpos : 0 < Cc := by rw [hCc]; positivity
  have hPN : pc p N t ∈ V N := h.contains N hNodd N hNodd le_rfl
  have hp₀N : p₀ ∈ V N := h.mono N₀ N hN₀ hNodd hN₀N hp₀
  refine ⟨Cc • (pc p N t + ((B + 1) / η) • p₀), ?_, fun x => ?_⟩
  · exact Submodule.smul_mem _ _ (Submodule.add_mem _ (le_polyUnion hNodd hPN)
      (Submodule.smul_mem _ _ (le_polyUnion hNodd hp₀N)))
  · have htx := h.t_nonneg x
    rw [abs_of_nonneg htx]
    have hge1 : (1 : ℝ) ≤ p N (t x) + (B + 1) / η * p₀ x := by
      have h1 := hF.ge_neg hNodd htx
      have h2 : B + 1 ≤ (B + 1) / η * p₀ x := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hη]
        nlinarith only [hp₀η x, hBnn]
      linarith only [h1, h2]
    have hk1 : (1 + t x) ^ k ≤ (1 + t x) ^ N :=
      pow_le_pow_right₀ (by linarith only [htx]) hkN
    show (1 + t x) ^ k ≤ Cc * (p N (t x) + (B + 1) / η * p₀ x)
    rcases le_total s₀ (t x) with hs | hs
    · have hl := hF.lower N hNodd (t x) hs
      have hpos : 0 < t x := lt_of_lt_of_le hs₀pos hs
      have h3 : 1 + t x ≤ 2 * (1 + 1 / s₀) * (t x / 2) := by
        have : 1 / s₀ * t x ≥ 1 := by
          rw [one_div, inv_mul_eq_div, ge_iff_le, le_div_iff₀ hs₀pos]; linarith only [hs]
        nlinarith only [this]
      have h4 : (1 + t x) ^ N ≤ (2 * (1 + 1 / s₀)) ^ N * (t x / 2) ^ N := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h3 N
      have hp : 0 ≤ (B + 1) / η * p₀ x := by
        have : 0 < p₀ x := lt_of_lt_of_le hη (hp₀η x); positivity
      have h5 : (2 * (1 + 1 / s₀)) ^ N * (t x / 2) ^ N ≤
          (2 * (1 + 1 / s₀)) ^ N * (p N (t x) + (B + 1) / η * p₀ x) := by
        gcongr; linarith only [hl, hp]
      have h6 : (2 * (1 + 1 / s₀)) ^ N * (p N (t x) + (B + 1) / η * p₀ x) ≤
          Cc * (p N (t x) + (B + 1) / η * p₀ x) := by
        have h7 : 0 ≤ p N (t x) + (B + 1) / η * p₀ x := by linarith only [hge1]
        have : 0 ≤ (1 + s₀) ^ N := by positivity
        nlinarith only [h7, this, hCc]
      linarith only [hk1, h4, h5, h6]
    · have h3 : (1 + t x) ^ N ≤ (1 + s₀) ^ N :=
        pow_le_pow_left₀ (by linarith only [htx]) (by linarith only [hs]) N
      have h6 : (1 + s₀) ^ N ≤ Cc * (p N (t x) + (B + 1) / η * p₀ x) := by
        have : 0 ≤ (2 * (1 + 1 / s₀)) ^ N := by positivity
        have : (1 + s₀) ^ N * 1 ≤ Cc * (p N (t x) + (B + 1) / η * p₀ x) := by
          nlinarith only [hge1, hCc, this, (by positivity : (0 : ℝ) ≤ (1 + s₀) ^ N)]
        linarith only [this]
      linarith only [hk1, h3, h6]

end PolyCompactHyp

section Main

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {C T₀ : ℝ} {p : ℕ → C(ℝ, ℝ)} {t : C(X, ℝ)} {V : ℕ → Submodule ℝ C(X, ℝ)}

omit [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma pow_mem_polyGrowth (t : C(X, ℝ)) (k : ℕ) :
    t ^ k ∈ FormalResearch.Measure.polyGrowth (t : X → ℝ) :=
  ⟨1, k, fun x => by
    rw [ContinuousMap.pow_apply, abs_pow, one_mul]
    exact pow_le_pow_left₀ (abs_nonneg _) (by linarith only [abs_nonneg (t x)]) k⟩

/-- The reference-measure equations on `⋃ V_N`: `L(p_j ∘ t) = ∫ p_j dμ₀` for odd `j`. -/
def RefOdd (p : ℕ → C(ℝ, ℝ)) (t : C(X, ℝ)) (V : ℕ → Submodule ℝ C(X, ℝ)) (μ₀ : Measure ℝ)
    (L : polyUnion V →ₗ[ℝ] ℝ) : Prop :=
  ∀ (v : polyUnion V) (j : ℕ), Odd j → (v : C(X, ℝ)) = pc p j t → L v = ∫ s, p j s ∂μ₀

omit [T2Space X] [LocallyCompactSpace X] in
/-- Exponential moment of any representing measure (the `ds:mom` half of the proof). -/
lemma exists_exp_moment (h : PolyCompactHyp C p T₀ t V) (μ₀ : Measure ℝ) (hμ₀ : μ₀ (Iio 0) = 0)
    (hint : Integrable (fun s => Real.exp (π * s)) μ₀)
    (L : polyUnion V →ₗ[ℝ] ℝ) (hL : ∀ v : polyUnion V, (∀ x, 0 ≤ v.1 x) → 0 ≤ L v)
    (hodd : RefOdd p t V μ₀ L) (μ : Measure X)
    (hpoly : ∀ f ∈ FormalResearch.Measure.polyGrowth t, Integrable f μ)
    (hrep : ∀ v : polyUnion V, ∫ x, v.1 x ∂μ = L v) :
    ∃ ε : ℝ, 0 < ε ∧ Integrable (fun x => Real.exp (ε * t x)) μ := by
  obtain ⟨N₀, p₀, η, hN₀, hp₀, hη, hp₀η⟩ := h.majorant
  have hp₀U : p₀ ∈ polyUnion V := le_polyUnion hN₀ hp₀
  have hLp₀ : 0 ≤ L ⟨p₀, hp₀U⟩ := hL _ fun x => (hη.trans_le (hp₀η x)).le
  set M : ℝ := L ⟨p₀, hp₀U⟩ / η with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  obtain ⟨C₁, hC₁, hbound, hexp⟩ := ds_mom h.fam μ₀ hμ₀ hint hM0
  have htm : Measurable t := t.continuous.measurable
  set ν : Measure ℝ := Measure.map t μ with hν
  have hνIio : ν (Iio 0) = 0 := by
    rw [hν, Measure.map_apply htm measurableSet_Iio]
    have : t ⁻¹' Iio 0 = ∅ := by
      ext x; simp [not_lt.2 (h.t_nonneg x)]
    rw [this, measure_empty]
  have hνmass : ν univ ≤ ENNReal.ofReal M := by
    rw [hν, Measure.map_apply htm MeasurableSet.univ, preimage_univ]
    have hp₀int : Integrable p₀ μ :=
      hpoly p₀ (h.union_le_polyGrowth hp₀U)
    have h1 : ENNReal.ofReal (L ⟨p₀, hp₀U⟩) = ∫⁻ x, ENNReal.ofReal (p₀ x) ∂μ := by
      rw [← hrep ⟨p₀, hp₀U⟩]
      exact ofReal_integral_eq_lintegral_ofReal hp₀int
        (Eventually.of_forall fun x => (hη.trans_le (hp₀η x)).le)
    have h2 : ENNReal.ofReal η * μ univ ≤ ENNReal.ofReal (L ⟨p₀, hp₀U⟩) := by
      rw [h1, ← lintegral_const]
      exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hp₀η x)
    rw [hM, ENNReal.ofReal_div_of_pos hη, ENNReal.le_div_iff_mul_le
      (Or.inl (by simpa using hη)) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact h2
  have hpow : ∀ k : ℕ, Integrable (fun s : ℝ => s ^ k) ν := by
    intro k
    rw [hν, integrable_map_measure (by fun_prop) htm.aemeasurable]
    exact hpoly (t ^ k) (pow_mem_polyGrowth t k)
  have hodd' : ∀ k : ℕ, Odd k → ∫ s, p k s ∂ν = ∫ s, p k s ∂μ₀ := by
    intro k hk
    rw [hν, integral_map htm.aemeasurable (p k).continuous.aestronglyMeasurable]
    have := hrep ⟨pc p k t, h.pc_mem hk⟩
    rw [hodd ⟨pc p k t, h.pc_mem hk⟩ k hk rfl] at this
    exact this
  obtain ⟨hI, -⟩ := hexp ν hνIio hνmass hpow hodd'
  refine ⟨1 / (2 * Real.exp 1 * C₁), by positivity, ?_⟩
  rw [hν, integrable_map_measure (by fun_prop) htm.aemeasurable] at hI
  refine hI.congr (Eventually.of_forall fun x => ?_)
  simp [div_eq_inv_mul]

/-- **Lemma LP-P** (`dsl:poly-compact`).  Under the hypotheses `PolyCompactHyp` (items (i)-(iii)),
let `L` be a linear functional on `V = ⋃ V_N`, nonnegative on every `q ∈ V` with `q ≥ 0` on `X`, with
`L(p_j ∘ t) = ∫ p_j dμ₀` for all odd `j`, where `μ₀` is supported on `[0, ∞)` and
`∫ e^{π t} dμ₀ < ∞`.  Then there is a positive Radon measure `μ` on `X` representing `L` on `V`
(every continuous function of polynomial growth in `t` is `μ`-integrable) with
`∫ e^{ε t} dμ < ∞` for some `ε > 0`.  `X` is any locally compact Hausdorff space (a closed subset
of one is again one). -/
theorem poly_compact (h : PolyCompactHyp C p T₀ t V) (μ₀ : Measure ℝ) (hμ₀ : μ₀ (Iio 0) = 0)
    (hint : Integrable (fun s => Real.exp (π * s)) μ₀)
    (L : polyUnion V →ₗ[ℝ] ℝ) (hL : ∀ v : polyUnion V, (∀ x, 0 ≤ v.1 x) → 0 ≤ L v)
    (hodd : RefOdd p t V μ₀ L) :
    ∃ μ : Measure X, μ.Regular ∧
      (∀ f ∈ FormalResearch.Measure.polyGrowth t, Integrable f μ) ∧
      (∀ v : polyUnion V, ∫ x, v.1 x ∂μ = L v) ∧
      ∃ ε : ℝ, 0 < ε ∧ Integrable (fun x => Real.exp (ε * t x)) μ := by
  obtain ⟨μ, hreg, hpoly, hrep⟩ := FormalResearch.Measure.exists_measure_of_positive_polyGrowth
    t.continuous h.compact_le (polyUnion V) h.union_le_polyGrowth h.exists_coercive L hL
  exact ⟨μ, hreg, hpoly, hrep, exists_exp_moment h μ₀ hμ₀ hint L hL hodd μ hpoly hrep⟩

/-- **Lemma LP-P, finite-group clause**: if a finite group `G` acts continuously on `X`, preserving
`t`, every `V_N` and `L`, the representing measure may be chosen `G`-invariant. -/
theorem poly_compact_invariant {G : Type*} [Group G] [Finite G] [MulAction G X]
    [ContinuousConstSMul G X]
    (h : PolyCompactHyp C p T₀ t V) (μ₀ : Measure ℝ) (hμ₀ : μ₀ (Iio 0) = 0)
    (hint : Integrable (fun s => Real.exp (π * s)) μ₀)
    (L : polyUnion V →ₗ[ℝ] ℝ) (hL : ∀ v : polyUnion V, (∀ x, 0 ≤ v.1 x) → 0 ≤ L v)
    (hodd : RefOdd p t V μ₀ L)
    (htg : ∀ (g : G) (x : X), t (g • x) = t x)
    (hVg : ∀ (g : G) (N : ℕ), Odd N → ∀ v ∈ V N, FormalResearch.Measure.actComp g v ∈ V N)
    (hLg : ∀ (g : G) (v v' : polyUnion V),
      (v' : C(X, ℝ)) = FormalResearch.Measure.actComp g v → L v' = L v) :
    ∃ μ : Measure X, μ.Regular ∧
      (∀ f ∈ FormalResearch.Measure.polyGrowth t, Integrable f μ) ∧
      (∀ v : polyUnion V, ∫ x, v.1 x ∂μ = L v) ∧
      (∃ ε : ℝ, 0 < ε ∧ Integrable (fun x => Real.exp (ε * t x)) μ) ∧
      ∀ g : G, Measure.map (fun x => g • x) μ = μ := by
  have hVg' : ∀ (g : G) (v : C(X, ℝ)), v ∈ polyUnion V →
      FormalResearch.Measure.actComp g v ∈ polyUnion V := by
    intro g v hv
    obtain ⟨N, hN, hvN⟩ := (mem_polyUnion h.mono).1 hv
    exact le_polyUnion hN (hVg g N hN v hvN)
  obtain ⟨μ, hreg, hpoly, hrep, hinv⟩ :=
    FormalResearch.Measure.exists_invariant_measure_of_positive_polyGrowth
      t.continuous h.compact_le htg (polyUnion V) h.union_le_polyGrowth h.exists_coercive
      (fun g v hv => hVg' g v hv) L hL
      (fun g v => hLg g v _ rfl)
  exact ⟨μ, hreg, hpoly, hrep, exists_exp_moment h μ₀ hμ₀ hint L hL hodd μ hpoly hrep, hinv⟩

/-- info: 'FormalResearch.ModularBootstrap.LP.poly_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms poly_compact

/-- info: 'FormalResearch.ModularBootstrap.LP.poly_compact_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms poly_compact_invariant

end Main

end FormalResearch.ModularBootstrap.LP
