module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Compactness

/-!
# Theorem `Σ`, Steps 3--4: concentration on the Airy zeros and the atomic inequality

* `concentration` (Step 3, `sr:Sigma`): every vague limit `ν` of the `μ_j` satisfies
  `ν(ℝ ∖ {a_n}) = 0`.  Proof: with `d = κ = d₀/2`, the designs `𝔄_d`, `𝔅_κ` have the same `G_k`
  and `W_A = G (x - d)`, `W_B = G (x + κ)`, `x = a₁ - u`; the basic inequality for both gives
  `∫ χ G x dν ≤ V_A + V_B ≤ (2 + d/g) E_k → 0`, while `G_k x ≥ (1/2) Ai²/(a₁ - u)` on a compact `K`
  below `a₁` for `k` large.
* `atomic_inequality` (Step 4): for `ν` carried by the zeros, `Σ_n x_n Π_n ≤ V_𝔇` for every design
  test (`sr:e2`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.Special

/-- **Step 3** (`sr:Sigma`): concentration of a vague limit on the zeros of `Ai`. -/
theorem concentration (S : SpectralData) {𝒟 : Set Window} (hP : DesignPropertyP S.μ 𝒟)
    (F : SameSiteFamily 𝒟) (hbd : LocallyBounded S.μ) {𝒰 : Ultrafilter ℕ}
    (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) {ν : Measure ℝ} [IsLocallyFiniteMeasure ν]
    (hν : IsVagueLimit 𝒰 S.μ ν) : ν (Set.range airyNode)ᶜ = 0 := by
  have hsupp := vagueLimit_supp S h𝒰 hν
  have hae : ∀ᵐ u ∂ν, u ≤ airyNode 0 := by
    rw [airyNode_zero]; exact ae_le_of_supp hsupp
  set O : Set ℝ := {u | u < airyZero 1 ∧ airyAi u ≠ 0} with hOdef
  have hO : IsOpen O :=
    (isOpen_Iio (a := airyZero 1)).inter
      (isOpen_ne_fun differentiable_airyAi.continuous continuous_const)
  have hsub : (Set.range airyNode)ᶜ ⊆ O ∪ Ioi (airyZero 1) := by
    intro u hu
    by_cases h1 : airyZero 1 < u
    · exact Or.inr h1
    · push Not at h1
      refine Or.inl ⟨?_, ?_⟩
      · refine lt_of_le_of_ne h1 fun h => hu ⟨0, h.symm⟩
      · intro hAi
        obtain ⟨i, hi⟩ := exists_airyNode_eq hAi (h1.trans (airyZero_neg 1).le)
        exact hu ⟨i, hi.symm⟩
  have hOnull : ν O = 0 := by
    rw [hO.measurableSet.measure_eq_iSup_isCompact]
    refine le_antisymm (iSup_le fun K => iSup_le fun hKO => iSup_le fun hK => ?_) bot_le
    -- compact `K ⊆ O` is null
    have hr := designRadius_pos
    have hr2 := designRadius_lt_two
    set d₁ : ℝ := designRadius / 2 with hd₁
    have hd₁0 : 0 < d₁ := by positivity
    have hd₁2 : d₁ < 1 := by rw [hd₁]; linarith
    have hAabs : |d₁| < designRadius := by rw [abs_of_pos hd₁0]; linarith
    have hBabs : |-d₁| < designRadius := by rw [abs_neg, abs_of_pos hd₁0]; linarith
    obtain ⟨L, hL⟩ := hK.bddBelow
    set A0 : ℝ := min L (airyZero 1 - 3) with hA0
    set B0 : ℝ := airyZero 1 + 1 with hB0
    by_cases hne : K.Nonempty
    swap
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp
    set h : ℝ → ℝ := fun u => (airyAi u) ^ 2 / (airyZero 1 - u) with hh
    have hKlt : ∀ u ∈ K, u < airyZero 1 := fun u hu => (hKO hu).1
    have hhc : ContinuousOn h K := by
      refine ContinuousOn.div ((differentiable_airyAi.continuous.pow 2).continuousOn)
        (continuousOn_const.sub continuousOn_id) fun u hu => ?_
      have := hKlt u hu
      linarith
    obtain ⟨u₀, hu₀, hmin⟩ := hK.exists_isMinOn hne hhc
    have hm : 0 < h u₀ := by
      have h1 := hKO hu₀
      have h2 : 0 < airyAi u₀ ^ 2 := by
        have := h1.2
        positivity
      have h3 : 0 < airyZero 1 - u₀ := by linarith [h1.1]
      exact div_pos h2 h3
    set m := h u₀ with hmdef
    obtain ⟨k₀, hk₀⟩ := F.G_lower K hK
    have hbound : ∀ k, k₀ ≤ k → m / 2 * (ν K).toReal ≤
        (2 + d₁ / SameSiteFamily.gap1) * (F.win k 0).V := by
      intro k hk
      obtain ⟨TA⟩ := hP _ (F.mem k d₁ hAabs)
      obtain ⟨TB⟩ := hP _ (F.mem k (-d₁) hBabs)
      have huA : (F.win k d₁).uF = airyNode 0 - d₁ := F.uF_eq k d₁
      have huB : (F.win k (-d₁)).uF = airyNode 0 + d₁ := by rw [F.uF_eq]; ring
      have hI_A := basic_inequality S hbd h𝒰 hν TA (A := A0) (B := B0)
        (by rw [huA, hA0]; refine (min_le_right _ _).trans ?_; rw [← airyNode_zero]; linarith)
        (by rw [hB0])
      have hI_B := basic_inequality S hbd h𝒰 hν TB (A := A0) (B := B0)
        (by rw [huB, hA0]; refine (min_le_right _ _).trans ?_; rw [← airyNode_zero]; linarith)
        (by rw [hB0])
      set χ := cutoff A0 B0 with hχ
      set G := F.G k with hG
      have hGc : Continuous G := F.G_cont k
      have hcs : ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport (fun u => χ u * g u) :=
        fun g _ => HasCompactSupport.mul_cutoff A0 B0
      have hint : ∀ g : ℝ → ℝ, Continuous g → Integrable (fun u => χ u * g u) ν :=
        fun g hg => integrable_of_cs ((cutoff_continuous A0 B0).mul hg) (hcs g hg)
      have hcGx : Continuous fun u => G u * (airyNode 0 - u) := hGc.mul (continuous_const.sub continuous_id)
      have hcGA : Continuous fun u => G u * (airyNode 0 - d₁ - u) :=
        hGc.mul ((continuous_const.sub continuous_const).sub continuous_id)
      have hcGB : Continuous fun u => G u * (airyNode 0 - -d₁ - u) :=
        hGc.mul ((continuous_const.sub continuous_const).sub continuous_id)
      have hWA : ∀ u, (F.win k d₁).W u = G u * (airyNode 0 - d₁ - u) := F.W_eq k d₁
      have hWB : ∀ u, (F.win k (-d₁)).W u = G u * (airyNode 0 - -d₁ - u) := F.W_eq k (-d₁)
      have hI_A' : ∫ u, χ u * (G u * (airyNode 0 - d₁ - u)) ∂ν ≤ (F.win k d₁).V := by
        simpa [hWA] using hI_A
      have hI_B' : ∫ u, χ u * (G u * (airyNode 0 - -d₁ - u)) ∂ν ≤ (F.win k (-d₁)).V := by
        simpa [hWB] using hI_B
      -- split `χ G x = χ W_A + d₁ χ G` and `d₁ χ G ≤ χ W_B`
      have hsplit : ∫ u, χ u * (G u * (airyNode 0 - u)) ∂ν =
          ∫ u, χ u * (G u * (airyNode 0 - d₁ - u)) ∂ν + d₁ * ∫ u, χ u * G u ∂ν := by
        rw [← integral_const_mul, ← integral_add (hint _ hcGA) ((hint G hGc).const_mul d₁)]
        exact integral_congr_ae (Eventually.of_forall fun u => by ring)
      have hGB : d₁ * ∫ u, χ u * G u ∂ν ≤ ∫ u, χ u * (G u * (airyNode 0 - -d₁ - u)) ∂ν := by
        rw [← integral_const_mul]
        refine integral_mono_ae ((hint G hGc).const_mul d₁) (hint _ hcGB) ?_
        filter_upwards [hae] with u hu
        have h1 := cutoff_nonneg A0 B0 u
        have h2 : 0 ≤ G u := F.G_nonneg k (by linarith [hu, designRadius_pos])
        have h3 : 0 ≤ airyNode 0 - u := by linarith
        nlinarith [mul_nonneg (mul_nonneg h1 h2) h3]
      have hup : ∫ u, χ u * (G u * (airyNode 0 - u)) ∂ν ≤
          (F.win k d₁).V + (F.win k (-d₁)).V := by linarith
      have hVA := F.V_le_of_nonneg k hd₁0.le
      have hVB := F.V_le_of_neg k hd₁0.le
      -- lower bound on the compact `K`
      have hlow : ∀ u ∈ K, m / 2 ≤ χ u * (G u * (airyNode 0 - u)) := by
        intro u hu
        have hχ1 : χ u = 1 := by
          refine cutoff_eq_one ?_ ?_
          · exact (min_le_left _ _).trans (hL hu)
          · rw [hB0, ← airyNode_zero]; linarith [hKlt u hu, airyNode_zero]
        rw [hχ1, one_mul]
        have hlt : airyNode 0 - u > 0 := by
          have := hKlt u hu; rw [airyNode_zero]; linarith
        have h1 := hk₀ k hk u hu (by rw [airyNode_zero]; exact hKlt u hu)
        have h2 : h u₀ ≤ h u := hmin hu
        have h3 : (1 / 2) * (airyAi u) ^ 2 / (u - airyNode 0) ^ 2 * (airyNode 0 - u) =
            (1 / 2) * h u := by
          rw [hh]; simp only
          rw [show (u - airyNode 0) ^ 2 = (airyNode 0 - u) ^ 2 by ring, airyNode_zero]
          rw [airyNode_zero] at hlt
          field_simp
        have h4 := mul_le_mul_of_nonneg_right h1 hlt.le
        nlinarith
      have hoff : ∀ᵐ u ∂ν, u ∉ K → 0 ≤ χ u * (G u * (airyNode 0 - u)) := by
        filter_upwards [hae] with u hu _
        have h1 := cutoff_nonneg A0 B0 u
        have h2 : 0 ≤ G u := F.G_nonneg k (by linarith [hu, designRadius_pos])
        have h3 : 0 ≤ airyNode 0 - u := by linarith
        positivity
      have hmain := const_mul_measure_le_integral (hint _ hcGx) hK.measurableSet
        hK.measure_lt_top hlow hoff
      have hgap := SameSiteFamily.gap1_pos
      have hE0 := F.V_zero_eq k
      calc m / 2 * (ν K).toReal ≤ _ := hmain
        _ ≤ (F.win k d₁).V + (F.win k (-d₁)).V := hup
        _ ≤ (2 + d₁ / SameSiteFamily.gap1) * (F.win k 0).V := by nlinarith
    have hlim : Tendsto (fun k => (2 + d₁ / SameSiteFamily.gap1) * (F.win k 0).V) atTop (𝓝 0) := by
      simpa using F.E_small.const_mul (2 + d₁ / SameSiteFamily.gap1)
    have hle : m / 2 * (ν K).toReal ≤ 0 :=
      ge_of_tendsto hlim ((eventually_ge_atTop k₀).mono fun k hk => hbound k hk)
    have hfin : ν K ≠ ∞ := hK.measure_lt_top.ne
    have h0 : (ν K).toReal ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have : 0 < m / 2 * (ν K).toReal := by positivity
      linarith
    have : ν K = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm h0 ENNReal.toReal_nonneg) with h | h
      · exact h
      · exact absurd h hfin
    rw [this]
  exact measure_mono_null hsub (measure_union_null hOnull hsupp)

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.concentration

end FormalResearch.ModularBootstrap.Upper.Rigidity
