module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDict

/-!
# Lemma R at `f = 2`, uniformly on a compact family of two-simple-zero designs (`upper_transfer.tex`, `ut:R`, `ut:T2`)

`lemma_R_lower` (`Upper.Window.LemmaR`) is a statement about one member of a `CompactCombFamily`: its constants
`w₀`, `C₀` depend on the member.  `ut:T2` needs them uniform on the compact parameter set `𝒦` of the designs
(Region I: "uniformly positive and continuous on `{(σ, 𝔇) : 𝔇 ∈ 𝒦, σ_q ≤ σ ≤ Σ₀}`").  This module derives the uniform
form from the pointwise one by a diagonal argument: if the uniform bound failed, the failing designs `𝔇_m` (with
`c'_m` strictly increasing) have a convergent subsequence in the compact set `𝒦`, and the comb with
`c'`-dependent data `𝔇_{m(c')}` is a single member of a `CompactCombFamily` whose limit data are the limit design,
for which `lemma_R_lower` contradicts the failure.

* `TwoZeroDesign.lemma_R_lower_two_unif`: `∃ w₀ > 0, ∃ C₀, ∀ c' ≥ C₀, ∀ d ∈ 𝒦, ∀ σ ∈ (σ_q, Σ₀]`,
  `K̃_c^{(2)} w₀ (σ - σ_q) ≤ h₀ e^{c'L}` (`h₀ = sech² B₁`, `modifiedH0`).

All results are proved unconditionally.
-/

@[expose] public section

open Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design

namespace TwoZeroDesign

variable {n : ℕ}

lemma site_eq (d : TwoZeroDesign n) {k : ℕ} (h : 3 ≤ k ∧ k ≤ n + 2) :
    d.site k = d.s ⟨k - 3, by omega⟩ := by
  unfold site; simp only [h, and_self, dite_true]

lemma width_eq (d : TwoZeroDesign n) {k : ℕ} (h : 3 ≤ k ∧ k ≤ n + 2) :
    d.width k = d.e ⟨k - 3, by omega⟩ := by
  unfold width; simp only [h, and_self, dite_true]

/-- The data of the diagonal member: the design `D c'` at each `c'`, limit data of the design `d*`. -/
noncomputable def diagData (D : ℝ → TwoZeroDesign n) (d₀ : TwoZeroDesign n) : ModifiedCombData 2 (n + 2) where
  sigmaF c' := (D c').sigmaF
  sigmaK c' k := (D c').sigmaSite k
  epsHat c' k := (D c').epsHatSite k
  eta0 := 1 / 4
  sigmaFLim := d₀.sigmaF
  sigmaKLim k := d₀.sigmaSite k
  epsHatLim k := d₀.epsHatSite k

lemma modifiedH0_diagData (D : ℝ → TwoZeroDesign n) (d₀ : TwoZeroDesign n) (c' x : ℝ) :
    modifiedH0 2 (n + 2) (diagData D d₀) c' x = modifiedH0 2 (n + 2) (D c').toModified c' x := rfl

/-- If the designs `D c'` converge (in parameters) to `d₀ ∈ 𝒦` and all lie in `𝒦`, then `diagData D d₀` is a
single-member `CompactCombFamily`. -/
noncomputable def diagFamily {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm)
    (D : ℝ → TwoZeroDesign n) (hD : ∀ c', D c' ∈ 𝒦) (d₀ : TwoZeroDesign n) (hd₀ : d₀ ∈ 𝒦)
    (hlim : Tendsto (fun c' => toTuple (D c')) atTop (𝓝 (toTuple d₀))) : CompactCombFamily 2 (n + 2) where
  members := {diagData D d₀}
  hf := by norm_num
  hN := by omega
  M := (IsCompactFamily.exists_bound hK).choose / kappaAiry + 1
  hM := by
    have := (IsCompactFamily.exists_bound hK).choose_spec.1
    have := kappaAiry_pos
    positivity
  eta0_bounds := by
    rintro _ rfl
    exact ⟨by show (0 : ℝ) ≤ 1 / 4; norm_num, by show (1 / 4 : ℝ) ≤ 1 / 4; exact le_rfl⟩
  finite_bounds := by
    rintro _ rfl c' _
    obtain ⟨hp, hq, hse⟩ := (IsCompactFamily.exists_bound hK).choose_spec.2 (D c') (hD c')
    exact (D c').toModified_bounds (hA _ (hD c')) hq hse
  lim_bounds := by
    rintro _ rfl
    obtain ⟨hp, hq, hse⟩ := (IsCompactFamily.exists_bound hK).choose_spec.2 d₀ hd₀
    exact d₀.toModified_bounds (hA _ hd₀) hq hse
  uniform_tendsto := by
    intro ε hε
    have hκ := kappaAiry_pos
    have hq : Tendsto (fun c' => (D c').q) atTop (𝓝 d₀.q) :=
      ((continuous_fst.comp continuous_snd).continuousAt.tendsto).comp hlim
    have hs : ∀ i, Tendsto (fun c' => (D c').s i) atTop (𝓝 (d₀.s i)) := fun i =>
      ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).continuousAt.tendsto.comp hlim
    have he : ∀ i, Tendsto (fun c' => (D c').e i) atTop (𝓝 (d₀.e i)) := fun i =>
      ((continuous_apply i).comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).continuousAt.tendsto.comp hlim
    have hnear : ∀ (g : ℝ → ℝ) (a : ℝ), Tendsto g atTop (𝓝 a) →
        ∀ᶠ c' in atTop, |(-g c') / kappaAiry - (-a) / kappaAiry| ≤ ε := by
      intro g a hg
      have := (hg.const_sub 0 |>.div_const kappaAiry).eventually (Metric.closedBall_mem_nhds ((0 - a) / kappaAiry) hε)
      filter_upwards [this] with c' hc'
      simpa [Real.dist_eq, zero_sub] using hc'
    have hF : ∀ᶠ c' in atTop, |(D c').sigmaF - d₀.sigmaF| ≤ ε := hnear _ _ hq
    have hK3 : ∀ᶠ c' in atTop, ∀ k ∈ Finset.Icc (2 + 1) (n + 2),
        |(D c').sigmaSite k - d₀.sigmaSite k| ≤ ε ∧ |(D c').epsHatSite k - d₀.epsHatSite k| ≤ ε := by
      rw [Filter.eventually_all_finset]
      intro k hk
      obtain ⟨h3, hkN⟩ := Finset.mem_Icc.1 hk
      have hk' : 3 ≤ k ∧ k ≤ n + 2 := ⟨h3, hkN⟩
      have e1 := hnear _ _ (hs ⟨k - 3, by omega⟩)
      have e2 := (((he ⟨k - 3, by omega⟩).div_const kappaAiry).eventually
        (Metric.closedBall_mem_nhds (d₀.e ⟨k - 3, by omega⟩ / kappaAiry) hε))
      filter_upwards [e1, e2] with c' h1 h2
      refine ⟨?_, ?_⟩
      · unfold sigmaSite; rw [site_eq _ hk', site_eq _ hk']; exact h1
      · unfold epsHatSite; rw [width_eq _ hk', width_eq _ hk']
        simpa [Real.dist_eq] using h2
    obtain ⟨C, hC⟩ := eventually_atTop.1 (hF.and hK3)
    refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun {c'} hc' d hd => ?_⟩
    rw [Set.mem_singleton_iff.1 hd]
    exact hC c' ((le_max_left _ _).trans hc')

/-- **Lemma R at `f = 2`, uniform on a compact family** (`ut:R`, `ut:T2` Region I): `w₀ > 0` and `C₀` with
`K̃_c^{(2)} w₀ (σ - σ_q) ≤ h₀ e^{c'L}` for all `c' ≥ C₀`, `d ∈ 𝒦`, `σ_q(d) < σ ≤ Σ₀`, `x = ξ_* + λσ`
(`h₀ = sech² B₁`, the comb without the factor `T_{χ(p)}`). -/
theorem lemma_R_lower_two_unif {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm)
    (Sg0 : ℝ) :
    ∃ w0 : ℝ, 0 < w0 ∧ ∃ C₀ : ℝ, ∀ {c' : ℝ}, C₀ ≤ c' → ∀ d ∈ 𝒦, ∀ σ : ℝ, d.sigmaF < σ → σ ≤ Sg0 →
      windowNormKTilde 2 c' * w0 * (σ - d.sigmaF) ≤
        modifiedH0 2 (n + 2) d.toModified c' (xiStar + lambdaComb c' * σ) *
          Real.exp (c' * slitL (xiStar + lambdaComb c' * σ)) := by
  by_contra hneg
  push Not at hneg
  have hbad : ∀ (m : ℕ) (C : ℝ), ∃ (c' : ℝ) (d : TwoZeroDesign n) (σ : ℝ), C ≤ c' ∧ d ∈ 𝒦 ∧
      d.sigmaF < σ ∧ σ ≤ Sg0 ∧
      modifiedH0 2 (n + 2) d.toModified c' (xiStar + lambdaComb c' * σ) *
          Real.exp (c' * slitL (xiStar + lambdaComb c' * σ)) <
        windowNormKTilde 2 c' * (1 / ((m : ℝ) + 1)) * (σ - d.sigmaF) := by
    intro m C
    obtain ⟨c', hc', d, hd, σ, h1, h2, h3⟩ := hneg (1 / ((m : ℝ) + 1)) (by positivity) C
    exact ⟨c', d, σ, hc', hd, h1, h2, h3⟩
  choose cB dB σB hB using hbad
  let thr : ℕ → ℝ := fun m => Nat.rec 0 (fun m ih => cB m ih + 1) m
  have hthr : ∀ m, thr (m + 1) = cB m (thr m) + 1 := fun m => rfl
  let cs : ℕ → ℝ := fun m => cB m (thr m)
  let ds : ℕ → TwoZeroDesign n := fun m => dB m (thr m)
  let σs : ℕ → ℝ := fun m => σB m (thr m)
  have hcs_ge : ∀ m, thr m ≤ cs m := fun m => (hB m (thr m)).1
  have hcs_succ : ∀ m, cs m + 1 ≤ cs (m + 1) := fun m => by
    have := hcs_ge (m + 1); rw [hthr] at this; exact this
  have hcs_mono : StrictMono cs := strictMono_nat_of_lt_succ fun m => by linarith [hcs_succ m]
  have hcs0 : 0 ≤ cs 0 := hcs_ge 0
  have hcs_idx : ∀ m : ℕ, (m : ℝ) ≤ cs m := by
    intro m
    induction m with
    | zero => simpa using hcs0
    | succ m ih => push_cast; linarith [hcs_succ m]
  obtain ⟨t, ht, φ, hφ, hlimφ⟩ := hK.tendsto_subseq (x := fun m => toTuple (ds m))
    (fun m => ⟨ds m, (hB m (thr m)).2.1, rfl⟩)
  obtain ⟨d₀, hd₀, rfl⟩ := ht
  -- the index function `J`
  let P : ℝ → ℕ → Prop := fun c' j => cs (φ j) ≤ c'
  classical
  let J : ℝ → ℕ := fun c' => Nat.findGreatest (P c') ⌈c'⌉₊
  have hφcs : ∀ j : ℕ, (j : ℝ) ≤ cs (φ j) := fun j =>
    (Nat.cast_le.2 (hφ.id_le j)).trans (hcs_idx (φ j))
  have hJeq : ∀ j, J (cs (φ j)) = j := by
    intro j
    show Nat.findGreatest (P (cs (φ j))) ⌈cs (φ j)⌉₊ = j
    rw [Nat.findGreatest_eq_iff]
    refine ⟨?_, fun _ => le_rfl, fun m hjm hmN hPm => ?_⟩
    · exact Nat.cast_le.1 ((hφcs j).trans (Nat.le_ceil _))
    · have := hcs_mono (hφ hjm)
      exact absurd hPm (not_le.2 this)
  have hJtend : Tendsto J atTop atTop := by
    refine tendsto_atTop.2 fun N => ?_
    filter_upwards [eventually_ge_atTop (cs (φ N))] with c' hc'
    exact Nat.le_findGreatest (Nat.cast_le.1 ((hφcs N).trans hc' |>.trans (Nat.le_ceil c')))
      (show cs (φ N) ≤ c' from hc')
  let D : ℝ → TwoZeroDesign n := fun c' => ds (φ (J c'))
  have hD : ∀ c', D c' ∈ 𝒦 := fun c' => (hB (φ (J c')) (thr (φ (J c')))).2.1
  have hDlim : Tendsto (fun c' => toTuple (D c')) atTop (𝓝 (toTuple d₀)) := hlimφ.comp hJtend
  let 𝒦' := diagFamily hK hA D hD d₀ hd₀ hDlim
  have hmem : diagData D d₀ ∈ 𝒦'.members := rfl
  have hpos : PosLimitWidths (diagData D d₀) := by
    have h := d₀.toModified_posLimitWidths (hA d₀ hd₀)
    exact h
  obtain ⟨w0, hw0, C₀, hlow⟩ := lemma_R_lower 𝒦' hmem hpos Sg0
  obtain ⟨m, hm1, hm2, hm3⟩ : ∃ m : ℕ, 1 / w0 ≤ (m : ℝ) ∧ C₀ ≤ (m : ℝ) ∧ 1 ≤ (m : ℝ) := by
    obtain ⟨m, hm⟩ := exists_nat_ge (max (max (1 / w0) C₀) 1)
    exact ⟨m, (le_max_left _ _).trans ((le_max_left _ _).trans hm),
      (le_max_right _ _).trans ((le_max_left _ _).trans hm), (le_max_right _ _).trans hm⟩
  obtain ⟨hc, -, hσ1, hσ2, hlt⟩ := hB (φ m) (thr (φ m))
  have hφm : (m : ℝ) ≤ cs (φ m) := (Nat.cast_le.2 (hφ.id_le m)).trans (hcs_idx (φ m))
  have hc' : C₀ ≤ cs (φ m) := hm2.trans hφm
  have hcpos : 0 < cs (φ m) := lt_of_lt_of_le one_pos (hm3.trans hφm)
  have hDm : D (cs (φ m)) = ds (φ m) := by
    show ds (φ (J (cs (φ m)))) = ds (φ m)
    rw [hJeq]
  have hσF : (diagData D d₀).sigmaF (cs (φ m)) = (ds (φ m)).sigmaF := by
    show (D (cs (φ m))).sigmaF = _
    rw [hDm]
  have hlow' := hlow hc' (σs (φ m)) (by rw [hσF]; exact hσ1) hσ2
  rw [modifiedH0_diagData, hDm, hσF] at hlow'
  have hK := windowNormKTilde_pos 2 hcpos
  have hs : 0 < σs (φ m) - (ds (φ m)).sigmaF := sub_pos.2 hσ1
  have hw : 1 / (((φ m : ℕ) : ℝ) + 1) ≤ w0 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (m : ℝ) ≤ ((φ m : ℕ) : ℝ) := Nat.cast_le.2 (hφ.id_le m)
    have h2 : 1 ≤ w0 * (m : ℝ) := by
      have := mul_le_mul_of_nonneg_left hm1 hw0.le
      rwa [mul_one_div_cancel hw0.ne'] at this
    nlinarith
  have hcmp : windowNormKTilde 2 (cs (φ m)) * (1 / (((φ m : ℕ) : ℝ) + 1)) * (σs (φ m) - (ds (φ m)).sigmaF) ≤
      windowNormKTilde 2 (cs (φ m)) * w0 * (σs (φ m) - (ds (φ m)).sigmaF) := by
    have := mul_le_mul_of_nonneg_left hw hK.le
    exact mul_le_mul_of_nonneg_right this hs.le
  have hlt' : modifiedH0 2 (n + 2) (ds (φ m)).toModified (cs (φ m))
        (xiStar + lambdaComb (cs (φ m)) * σs (φ m)) *
      Real.exp (cs (φ m) * slitL (xiStar + lambdaComb (cs (φ m)) * σs (φ m))) <
      windowNormKTilde 2 (cs (φ m)) * (1 / (((φ m : ℕ) : ℝ) + 1)) * (σs (φ m) - (ds (φ m)).sigmaF) := hlt
  linarith

end TwoZeroDesign

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDesign.lemma_R_lower_two_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoZeroDesign.lemma_R_lower_two_unif

end FormalResearch.ModularBootstrap.TwoLevel
