module

public import FormalResearch.ModularBootstrap.Upper.Holes.HoleProduct
public import FormalResearch.ModularBootstrap.Upper.Holes.HoleGeometry

/-!
# The hole pairs of a modified ramped comb (`rem:thmU` Step (3))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (3), bullets "The pair at `k₀`" and
"The other seven hole pairs".

For an abstract modified comb (sites `χ'_k = ξ_* + λσ_k`, widths `ε_k = η_k ℓ_k` on `f < k ≤ N`,
`ℓ_k = siteGap c' k`) the hypotheses that the construction of the ramped comb verifies are collected in
`RampedHoleHyp`:

* heights `η_k ∈ [0, 1/4]`, nondecreasing, `σ_k ≥ 0`;
* the hole sites are displaced by at most `κ ℓ_n` (the paper's `|Δ_k| ≤ Cλk^{-4/3}` and `ℓ_n ≍ λ n^{-1/3}`
  give `κ = C/n`);
* if the pair `k₀ ∈ {n, n+1}` is displaced, its height satisfies `η² ≤ 1/32` (it lies below `N_Ai`).

`rampedHole_prod_lower` is the displayed lower bound for `∏_{k ∈ H} ρ_k`, `ρ_k = q'_k/q⁰_k`: the pair at `k₀`
contributes `(1 - 16ℓ_n) min(1, 16η_n²)(1 - 128κ²)` and the seven other pairs contribute the finite product
`(1 - δ)⁷ · (16647192576/23591176505) · (1 - 3500/n)` with `δ = 10κ + ℓ_n²`, valid for `n ≥ 10⁵`.
`rampedHoleHyp_ref` is the non-vacuity theorem (the reference comb satisfies the hypotheses with `κ = 0`).
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Holes
  FormalResearch.ModularBootstrap.Upper.Design

/-- The hypotheses on a modified ramped comb used in the hole comparison. -/
structure RampedHoleHyp (c' : ℝ) (f N n : ℕ) (σ η : ℕ → ℝ) (κ : ℝ) : Prop where
  eta_mem : ∀ k, f < k → k ≤ N → 0 ≤ η k ∧ η k ≤ 1 / 4
  eta_mono : ∀ k, f < k → k < N → η k ≤ η (k + 1)
  sigma_nonneg : ∀ k, f ≤ k → k ≤ N → 0 ≤ σ k
  hole_shift : ∀ k, f < k → k ≤ N → k ∈ holeSet n 4 →
    |designSite c' σ k - chiQuantile c' k| ≤ κ * siteGap c' n
  mid_case : ∀ k, f < k → k ≤ N → (k = n ∨ k = n + 1) →
    designSite c' σ k = chiQuantile c' k ∨ η k ^ 2 ≤ 1 / 32

lemma lambdaComb_pos_R {c' : ℝ} (hc' : 0 < c') : 0 < lambdaComb c' := by
  unfold lambdaComb
  have := kTip_pos
  positivity

lemma designSite_ge_xiStar {c' : ℝ} (hc' : 0 < c') {σ : ℕ → ℝ} {k : ℕ} (h : 0 ≤ σ k) :
    xiStar ≤ designSite c' σ k := by
  unfold designSite
  have := lambdaComb_pos_R hc'
  nlinarith

lemma xiStar_le_chiQuantile_nat {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : 1 ≤ k) :
    xiStar ≤ chiQuantile c' (k : ℝ) :=
  (chiQuantile_spec hc' (by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith)).1

/-- **Non-vacuity**: the reference comb itself (`σ_k = r_k/λ`, so `χ'_k = χ_k`; `η_k ≡ 1/4`; `κ = 0`)
satisfies `RampedHoleHyp`. -/
theorem rampedHoleHyp_ref {c' : ℝ} (hc' : 0 < c') {f : ℕ} (hf : 1 ≤ f) (N n : ℕ) :
    RampedHoleHyp c' f N n (fun k => siteRadius c' (k : ℝ) / lambdaComb c') (fun _ => 1 / 4) 0 := by
  have hlam := lambdaComb_pos_R hc'
  have hsite : ∀ k : ℕ, designSite c' (fun k => siteRadius c' (k : ℝ) / lambdaComb c') k =
      chiQuantile c' (k : ℝ) := fun k => by
    unfold designSite siteRadius
    field_simp
    ring
  refine ⟨fun k _ _ => ⟨by norm_num, le_rfl⟩, fun k _ _ => le_rfl, fun k hk _ => ?_, fun k _ _ _ => ?_,
    fun k _ _ _ => Or.inl (hsite k)⟩
  · have := xiStar_le_chiQuantile_nat hc' (hf.trans hk)
    unfold siteRadius
    exact div_nonneg (by linarith) hlam.le
  · rw [hsite]; simp

lemma theta_geom {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 100000) :
    (1 + 20 * t) ^ 2 ≤ (1 + 2000 * t) * (1 - 200 * t) ^ 2 := by
  have h1 : 1 - 400 * t ≤ (1 - 200 * t) ^ 2 := by nlinarith
  have h2 : (1 + 2000 * t) * (1 - 400 * t) ≤ (1 + 2000 * t) * (1 - 200 * t) ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  nlinarith

lemma n_aux {n : ℕ} (hn : 100000 ≤ n) :
    0 < (1 : ℝ) / (n : ℝ) ∧ (1 : ℝ) / (n : ℝ) ≤ 1 / 100000 := by
  have hnr : (100000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith

/-- The gaps in the hole in numeric form: `0 ≤ ℓ_k ≤ 1.0002 ℓ_n` and `ℓ_k ≥ ℓ_n/2`. -/
lemma hole_gap_numeric {c' : ℝ} (hc' : 0 < c') {n : ℕ} (hn : 100000 ≤ n)
    (_hℓ : siteGap c' n ≤ 1 / 16) {k : ℕ} (hkH : k ∈ holeSet n 4) :
    siteGap c' n / 2 ≤ siteGap c' k ∧ siteGap c' k ≤ 1.0002 * siteGap c' n := by
  obtain ⟨hℓpos, hgaps⟩ := hole_gap_bounds hc' (by omega : 20 ≤ n)
  obtain ⟨hgk1, hgk2⟩ := hgaps k hkH
  obtain ⟨ht0, ht1⟩ := n_aux hn
  have e20 : 20 / (n : ℝ) = 20 * (1 / (n : ℝ)) := by ring
  rw [e20] at hgk1 hgk2
  constructor <;> nlinarith

lemma shift_bound_aux {x χ χ' κ ℓ : ℝ} (hxξ : xiStar ≤ x) (hχ : xiStar ≤ χ) (hχ' : xiStar ≤ χ')
    (hℓpos : 0 < ℓ) (hℓ : ℓ ≤ 1 / 16) (hκ : κ ≤ 1 / 98) (hΔ : |χ' - χ| ≤ κ * ℓ)
    (hD3 : 1 / 3 * ℓ ≤ |x - χ|) :
    |realLogT x χ' - realLogT x χ| ≤ 5 * κ ∧ χ' ≠ x := by
  have hξ0 : 0 < xiStar := xiStar_pos
  have hκ0 : 0 ≤ κ := by
    have := abs_nonneg (χ' - χ)
    by_contra hneg
    push Not at hneg
    nlinarith
  have hseg : ∀ y ∈ Set.uIcc χ' χ, ℓ / 4 ≤ |x - y| := by
    intro y hy
    have h1 : |x - χ| - |y - χ| ≤ |x - y| := by
      have := abs_sub_abs_le_abs_sub (x - χ) (y - χ)
      simpa [sub_sub_sub_cancel_right] using this
    have h2 : |y - χ| ≤ |χ' - χ| := by
      rcases Set.mem_uIcc.mp hy with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [abs_le]
        constructor
        · linarith [neg_abs_le (χ' - χ)]
        · linarith [abs_nonneg (χ' - χ)]
      · rw [abs_le]
        constructor
        · linarith [abs_nonneg (χ' - χ)]
        · linarith [le_abs_self (χ' - χ)]
    have hκℓ : κ * ℓ ≤ 1 / 98 * ℓ := mul_le_mul_of_nonneg_right hκ hℓpos.le
    linarith
  constructor
  · have h := abs_realLogT_sub_le hxξ (hξ0.le.trans hχ') (hξ0.le.trans hχ)
      (by positivity : 0 < ℓ / 4) hseg
    refine h.trans ?_
    have hmul : (1 / (ℓ / 4) + π) * |χ' - χ| ≤ (1 / (ℓ / 4) + π) * (κ * ℓ) :=
      mul_le_mul_of_nonneg_left hΔ (by positivity)
    have hexp : (1 / (ℓ / 4) + π) * (κ * ℓ) = 4 * κ + π * ℓ * κ := by
      field_simp
    have hpi := Real.pi_lt_d2
    have hπℓ : π * ℓ ≤ 1 := by nlinarith [Real.pi_pos]
    nlinarith
  · intro h
    have := hseg χ' Set.left_mem_uIcc
    rw [h, sub_self, abs_zero] at this
    linarith

lemma delta_bound_aux {κ ℓ : ℝ} (hκ0 : 0 ≤ κ) (hℓpos : 0 < ℓ) (_hℓ : ℓ ≤ 1 / 16) :
    1 - (10 * κ + ℓ ^ 2) ≤ Real.exp (-2 * (5 * κ)) / (1 + 8 * (ℓ / 3) ^ 2) := by
  rw [le_div_iff₀ (by positivity)]
  have hexp := Real.add_one_le_exp (-2 * (5 * κ))
  nlinarith [mul_nonneg hκ0 (sq_nonneg ℓ), sq_nonneg ℓ, sq_nonneg (ℓ ^ 2)]

lemma geom_bound_aux {a ℓ ℓk t D : ℝ} (ha : 0 ≤ a) (ht0 : 0 < t) (ht1 : t ≤ 1 / 100000) (hℓpos : 0 < ℓ)
    (hgk : ℓk ≤ (1 + 20 * t) * ℓ) (hgk0 : 0 ≤ ℓk) (hD : (1 - 200 * t) * (a * ℓ) ≤ D) (_hD0 : 0 ≤ D) :
    16 * a ^ 2 * (1 / 4 * ℓk) ^ 2 ≤ (1 + 2000 * t) * D ^ 2 := by
  have hth := theta_geom ht0 ht1
  have hD1 : 0 ≤ (1 - 200 * t) * (a * ℓ) := by
    have : 0 ≤ 1 - 200 * t := by linarith
    positivity
  have hDsq : ((1 - 200 * t) * (a * ℓ)) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hD1 hD 2
  have hk2 : ℓk ^ 2 ≤ ((1 + 20 * t) * ℓ) ^ 2 := pow_le_pow_left₀ hgk0 hgk 2
  have hlhs : 16 * a ^ 2 * (1 / 4 * ℓk) ^ 2 = a ^ 2 * ℓk ^ 2 := by ring
  rw [hlhs]
  calc a ^ 2 * ℓk ^ 2 ≤ a ^ 2 * ((1 + 20 * t) * ℓ) ^ 2 :=
        mul_le_mul_of_nonneg_left hk2 (sq_nonneg a)
    _ = ((1 + 20 * t) ^ 2) * (a * ℓ) ^ 2 := by ring
    _ ≤ ((1 + 2000 * t) * (1 - 200 * t) ^ 2) * (a * ℓ) ^ 2 :=
        mul_le_mul_of_nonneg_right hth (sq_nonneg _)
    _ = (1 + 2000 * t) * ((1 - 200 * t) * (a * ℓ)) ^ 2 := by ring
    _ ≤ (1 + 2000 * t) * D ^ 2 :=
        mul_le_mul_of_nonneg_left hDsq (by linarith)

/-- **One of the seven other hole pairs of a modified comb** (`rem:thmU` Step (3)): for `k ∈ H` modified, at
distance `≥ (1 - 200/n) a ℓ_n` from `x`, `ρ_k = q'_k/q⁰_k ≥ (1 - δ)(1 + θ/(16a²))⁻¹` with `δ = 10κ + ℓ_n²`,
`θ = 1 + 2000/n`. -/
theorem other_pair_bound {c' x κ : ℝ} (hc' : 0 < c') {n : ℕ} (hn : 100000 ≤ n)
    (hxξ : xiStar ≤ x) {f N : ℕ} {σ η : ℕ → ℝ} (H : RampedHoleHyp c' f N n σ η κ)
    {k : ℕ} (hkH : k ∈ holeSet n 4) (hkf : f < k) (hkN : k ≤ N) {a : ℝ} (ha : 1 / 2 ≤ a)
    (hdist : (1 - 200 / (n : ℝ)) * (a * siteGap c' n) ≤ |x - chiQuantile c' (k : ℝ)|)
    (hℓ : siteGap c' n ≤ 1 / 16) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 98) :
    (1 - (10 * κ + siteGap c' n ^ 2)) * (1 + (1 + 2000 / (n : ℝ)) / (16 * a ^ 2))⁻¹ ≤
      blaschkePairQ (designSite c' σ k) (η k * siteGap c' k) x / pairModQ c' (1 / 4) x k := by
  obtain ⟨hℓpos, -⟩ := hole_gap_bounds hc' (by omega : 20 ≤ n)
  obtain ⟨hgk1, hgk2⟩ := hole_gap_numeric hc' hn hℓ hkH
  obtain ⟨ht0, ht1⟩ := n_aux hn
  have e200 : 200 / (n : ℝ) = 200 * (1 / (n : ℝ)) := by ring
  have e2000 : 2000 / (n : ℝ) = 2000 * (1 / (n : ℝ)) := by ring
  have hgk2' : siteGap c' k ≤ (1 + 20 * (1 / (n : ℝ))) * siteGap c' n := by
    obtain ⟨-, hgaps⟩ := hole_gap_bounds hc' (by omega : 20 ≤ n)
    have := (hgaps k hkH).2
    have e20 : 20 / (n : ℝ) = 20 * (1 / (n : ℝ)) := by ring
    rwa [e20] at this
  rw [e200] at hdist
  rw [e2000]
  have hk1 : 1 ≤ k := by
    have := (Finset.mem_Icc.mp hkH).1
    omega
  have hχ : xiStar ≤ chiQuantile c' (k : ℝ) := xiStar_le_chiQuantile_nat hc' hk1
  have hη := H.eta_mem k hkf hkN
  have hσk := H.sigma_nonneg k hkf.le hkN
  have hχ' : xiStar ≤ designSite c' σ k := designSite_ge_xiStar hc' hσk
  have hΔ := H.hole_shift k hkf hkN hkH
  have hξ0 : 0 < xiStar := xiStar_pos
  have hD3 : 1 / 3 * siteGap c' n ≤ |x - chiQuantile c' (k : ℝ)| := by
    have hc : 1 / 3 ≤ (1 - 200 * (1 / (n : ℝ))) * a := by nlinarith
    have : 1 / 3 * siteGap c' n ≤ ((1 - 200 * (1 / (n : ℝ))) * a) * siteGap c' n :=
      mul_le_mul_of_nonneg_right hc hℓpos.le
    nlinarith
  obtain ⟨hs, hne'⟩ := shift_bound_aux hxξ hχ hχ' hℓpos hℓ hκ hΔ hD3
  have hne : x ≠ chiQuantile c' (k : ℝ) := by
    intro h
    rw [h, sub_self, abs_zero] at hD3
    linarith
  have hgkpos : 0 ≤ siteGap c' k := by linarith
  have hε' : 0 ≤ η k * siteGap c' k ∧ η k * siteGap c' k ≤ 1 / 2 := by
    constructor
    · exact mul_nonneg hη.1 hgkpos
    · nlinarith [hη.2, hη.1]
  have hε₀ : 0 ≤ 1 / 4 * siteGap c' k ∧ 1 / 4 * siteGap c' k ≤ 1 / 16 := by
    constructor
    · linarith
    · nlinarith
  have hε₀e : 1 / 4 * siteGap c' k ≤ siteGap c' n / 3 := by nlinarith
  have hδ1 : 10 * κ + siteGap c' n ^ 2 ≤ 1 := by nlinarith
  have hδ := delta_bound_aux hκ0 hℓpos hℓ
  have hD0 : 0 ≤ |x - chiQuantile c' (k : ℝ)| := abs_nonneg _
  have hgeom : 16 * a ^ 2 * (1 / 4 * siteGap c' k) ^ 2 ≤
      (1 + 2000 * (1 / (n : ℝ))) * (x - chiQuantile c' (k : ℝ)) ^ 2 := by
    have := geom_bound_aux (by linarith) ht0 ht1 hℓpos hgk2' hgkpos hdist hD0
    rwa [sq_abs] at this
  have h := otherPair_factor_lower (χ := chiQuantile c' (k : ℝ)) (χ' := designSite c' σ k)
    (ε' := η k * siteGap c' k) (ε₀ := 1 / 4 * siteGap c' k) (x := x) (s := 5 * κ)
    (e1 := siteGap c' n / 3) (δ := 10 * κ + siteGap c' n ^ 2)
    (θ := 1 + 2000 * (1 / (n : ℝ))) (a := a) hχ (hξ0.le.trans hχ') hxξ hne hne' hε' hε₀ hs hε₀e hδ1
    hδ (by linarith) hgeom
  have hpm : pairModQ c' (1 / 4) x k = blaschkePairQ (chiQuantile c' (k : ℝ)) (1 / 4 * siteGap c' k) x :=
    rfl
  rw [hpm]
  exact h

/-- **The pair at `k₀` of a modified comb** (`rem:thmU` Step (3), "The pair at `k₀`"):
`ρ_{k₀} ≥ (1 - 16ℓ_n) min(1, 16η_n²)(1 - 128κ²)` when `|x - χ_{k₀}| ≤ ℓ_n/2`, `η_n ≤ η_{k₀}`. -/
theorem k0_pair_bound {c' x κ : ℝ} (hc' : 0 < c') {n : ℕ} (hn : 100000 ≤ n)
    (hxξ : xiStar ≤ x) {f N : ℕ} {σ η : ℕ → ℝ} (H : RampedHoleHyp c' f N n σ η κ)
    {k0 : ℕ} (hk0H : k0 ∈ holeSet n 4) (hk0f : f < k0) (hk0N : k0 ≤ N) (hk0mid : k0 = n ∨ k0 = n + 1)
    (hdist : |x - chiQuantile c' (k0 : ℝ)| ≤ siteGap c' n / 2) (hηn : 0 ≤ η n ∧ η n ≤ η k0)
    (hℓ : siteGap c' n ≤ 1 / 16) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 98) :
    (1 - 16 * siteGap c' n) * (min 1 (16 * η n ^ 2) * (1 - 128 * κ ^ 2)) ≤
      blaschkePairQ (designSite c' σ k0) (η k0 * siteGap c' k0) x / pairModQ c' (1 / 4) x k0 := by
  obtain ⟨hℓpos, -⟩ := hole_gap_bounds hc' (by omega : 20 ≤ n)
  obtain ⟨hgk1, hgk2⟩ := hole_gap_numeric hc' hn hℓ hk0H
  have hk1 : 1 ≤ k0 := by
    have := (Finset.mem_Icc.mp hk0H).1
    omega
  have hχ : xiStar ≤ chiQuantile c' (k0 : ℝ) := xiStar_le_chiQuantile_nat hc' hk1
  have hη := H.eta_mem k0 hk0f hk0N
  have hσk := H.sigma_nonneg k0 hk0f.le hk0N
  have hχ' : xiStar ≤ designSite c' σ k0 := designSite_ge_xiStar hc' hσk
  have hΔ := H.hole_shift k0 hk0f hk0N hk0H
  have hsum : chiQuantile c' (k0 : ℝ) + (designSite c' σ k0 - chiQuantile c' (k0 : ℝ)) =
      designSite c' σ k0 := by ring
  have hκℓ : κ * siteGap c' n ≤ 1 / 98 * siteGap c' n := mul_le_mul_of_nonneg_right hκ hℓpos.le
  have hcase : designSite c' σ k0 - chiQuantile c' (k0 : ℝ) = 0 ∨ η k0 ^ 2 ≤ 1 / 32 := by
    rcases H.mid_case k0 hk0f hk0N hk0mid with h | h
    · exact Or.inl (sub_eq_zero.mpr h)
    · exact Or.inr h
  have hpair := pairK0_factor_lower (χ := chiQuantile c' (k0 : ℝ))
    (Δ := designSite c' σ k0 - chiQuantile c' (k0 : ℝ)) (η := η k0) (ℓ := siteGap c' k0)
    (x := x) (w := siteGap c' n) hχ (by rw [hsum]; exact hχ') hxξ hℓpos hℓ
    (by
      rw [hsum]
      have : x - designSite c' σ k0 = (x - chiQuantile c' (k0 : ℝ)) -
          (designSite c' σ k0 - chiQuantile c' (k0 : ℝ)) := by ring
      rw [this]
      refine (abs_sub _ _).trans ?_
      have h2 := abs_nonneg (x - chiQuantile c' (k0 : ℝ))
      linarith)
    (by linarith) hη.1 (by linarith) (by nlinarith [hη.1, hη.2]) (by nlinarith) hcase
  rw [hsum] at hpair
  have hpm : pairModQ c' (1 / 4) x k0 =
      blaschkePairQ (chiQuantile c' (k0 : ℝ)) (1 / 4 * siteGap c' k0) x := rfl
  rw [hpm]
  refine le_trans ?_ hpair
  have hM : min 1 (16 * η n ^ 2) ≤ min 1 (16 * η k0 ^ 2) :=
    min_le_min le_rfl (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hηn.1 hηn.2 2) (by norm_num))
  have hθ : 1 - 128 * κ ^ 2 ≤ 1 - 32 * (designSite c' σ k0 - chiQuantile c' (k0 : ℝ)) ^ 2 /
      siteGap c' k0 ^ 2 := by
    have hlk : 0 < siteGap c' k0 := by linarith
    have h1 : 32 * (designSite c' σ k0 - chiQuantile c' (k0 : ℝ)) ^ 2 / siteGap c' k0 ^ 2 ≤
        128 * κ ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have hsq : (designSite c' σ k0 - chiQuantile c' (k0 : ℝ)) ^ 2 ≤ (κ * siteGap c' n) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hΔ 2
      have hlsq : (siteGap c' n / 2) ^ 2 ≤ siteGap c' k0 ^ 2 := pow_le_pow_left₀ (by positivity) hgk1 2
      nlinarith [sq_nonneg κ, mul_le_mul_of_nonneg_left hlsq (sq_nonneg κ)]
    linarith
  have hκsq : 128 * κ ^ 2 ≤ 1 := by nlinarith
  have hMnn : 0 ≤ min 1 (16 * η k0 ^ 2) := le_min zero_le_one (by positivity)
  have h16 : 0 ≤ 1 - 16 * siteGap c' n := by linarith
  exact mul_le_mul_of_nonneg_left (mul_le_mul hM hθ (by linarith) hMnn) h16

/-- The modified hole pairs. -/
abbrev holeModSet (f N n : ℕ) : Finset ℕ := (Finset.Icc (f + 1) N).filter (fun k => k ∈ holeSet n 4)

/-- The ratio `ρ_k = q'_k/q⁰_k` of the modified pair `k` to the reference pair. -/
noncomputable def holeRho (c' x : ℝ) (σ η : ℕ → ℝ) (k : ℕ) : ℝ :=
  blaschkePairQ (designSite c' σ k) (η k * siteGap c' k) x / pairModQ c' (1 / 4) x k

lemma holeRho_nonneg (c' x : ℝ) (σ η : ℕ → ℝ) (k : ℕ) : 0 ≤ holeRho c' x σ η k :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The hole product for an arbitrary layout `(k₀, kN, kF)` of the hole. -/
theorem rampedHole_prod_layout {c' x κ : ℝ} (hc' : 0 < c') {n : ℕ} (hn : 100000 ≤ n)
    (hxξ : xiStar ≤ x) {f N : ℕ} {σ η : ℕ → ℝ} (H : RampedHoleHyp c' f N n σ η κ)
    (hfn : f + 4 ≤ n) {k0 : ℕ} {kN kF : ℕ → ℕ}
    (hS : holeSet n 4 = insert k0 (Finset.image kN (Finset.range 4) ∪ Finset.image kF (Finset.range 3)))
    (h0N : ∀ i, i < 4 → kN i ≠ k0) (h0F : ∀ i, i < 3 → kF i ≠ k0)
    (hNF : ∀ i, i < 4 → ∀ j, j < 3 → kN i ≠ kF j)
    (hNi : ∀ i, i < 4 → ∀ j, j < 4 → kN i = kN j → i = j)
    (hFi : ∀ i, i < 3 → ∀ j, j < 3 → kF i = kF j → i = j)
    (hk0mid : k0 = n ∨ k0 = n + 1)
    (hdist0 : |x - chiQuantile c' (k0 : ℝ)| ≤ siteGap c' n / 2)
    (hηk0 : k0 ≤ N → 0 ≤ η n ∧ η n ≤ η k0)
    (hdN : ∀ i : ℕ, i < 4 → (1 - 200 / (n : ℝ)) * (((i : ℝ) + 1 / 2) * siteGap c' n) ≤
      |x - chiQuantile c' ((kN i : ℕ) : ℝ)|)
    (hdF : ∀ i : ℕ, i < 3 → (1 - 200 / (n : ℝ)) * (((i : ℝ) + 1) * siteGap c' n) ≤
      |x - chiQuantile c' ((kF i : ℕ) : ℝ)|)
    (hℓ : siteGap c' n ≤ 1 / 16) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 98) :
    ((1 - 16 * siteGap c' n) * (min 1 (16 * η n ^ 2) * (1 - 128 * κ ^ 2))) *
        ((1 - (10 * κ + siteGap c' n ^ 2)) ^ 7 * holeProdConst *
          (1 - 7 / 4 * ((1 + 2000 / (n : ℝ)) - 1))) ≤
      ∏ k ∈ holeModSet f N n, holeRho c' x σ η k := by
  obtain ⟨hℓpos, -⟩ := hole_gap_bounds hc' (by omega : 20 ≤ n)
  obtain ⟨ht0, ht1⟩ := n_aux hn
  have e2000 : 2000 / (n : ℝ) = 2000 * (1 / (n : ℝ)) := by ring
  have hθ1 : 1 ≤ 1 + 2000 / (n : ℝ) := by
    have : 0 ≤ 2000 / (n : ℝ) := by rw [e2000]; positivity
    linarith
  have hθ2 : 1 + 2000 / (n : ℝ) ≤ 8 / 7 := by rw [e2000]; linarith
  have hδ0 : 0 ≤ 10 * κ + siteGap c' n ^ 2 := by positivity
  have hδ1 : 10 * κ + siteGap c' n ^ 2 ≤ 1 := by nlinarith
  have hκsq : 128 * κ ^ 2 ≤ 1 := by nlinarith
  have hMnn : 0 ≤ min 1 (16 * η n ^ 2) := le_min zero_le_one (by positivity)
  have hM1 : min 1 (16 * η n ^ 2) ≤ 1 := min_le_left _ _
  have h16 : 0 ≤ 1 - 16 * siteGap c' n := by linarith
  have hκ2 : 0 ≤ 1 - 128 * κ ^ 2 := by linarith
  have hb0 : 0 ≤ (1 - 16 * siteGap c' n) * (min 1 (16 * η n ^ 2) * (1 - 128 * κ ^ 2)) :=
    mul_nonneg h16 (mul_nonneg hMnn hκ2)
  have hb01 : (1 - 16 * siteGap c' n) * (min 1 (16 * η n ^ 2) * (1 - 128 * κ ^ 2)) ≤ 1 := by
    have h1 : 1 - 16 * siteGap c' n ≤ 1 := by linarith [hℓpos]
    have h2 : min 1 (16 * η n ^ 2) * (1 - 128 * κ ^ 2) ≤ 1 := by
      calc min 1 (16 * η n ^ 2) * (1 - 128 * κ ^ 2) ≤ 1 * 1 :=
            mul_le_mul hM1 (by nlinarith [sq_nonneg κ]) hκ2 zero_le_one
        _ = 1 := one_mul 1
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (mul_nonneg hMnn hκ2) zero_le_one
      _ = 1 := one_mul 1
  have hmemH : ∀ k, k ∈ holeModSet f N n → f < k ∧ k ≤ N ∧ k ∈ holeSet n 4 := fun k hk => by
    have := Finset.mem_filter.mp hk
    have h2 := Finset.mem_Icc.mp this.1
    exact ⟨by omega, h2.2, this.2⟩
  have hHmem : ∀ k, k ∈ holeSet n 4 → f < k := fun k hk => by
    have := (Finset.mem_Icc.mp hk).1
    omega
  refine holeProduct_lower (H := holeSet n 4) (T := holeModSet f N n) (k0 := k0) (kN := kN) (kF := kF)
    hS h0N h0F hNF hNi hFi (fun k hk => (hmemH k hk).2.2) (holeRho c' x σ η)
    (fun k _ => holeRho_nonneg c' x σ η k) hθ1 (by linarith) hδ0 hδ1 hb0 hb01 ?_ ?_ ?_
  · intro hk0T
    obtain ⟨hf0, hN0, hH0⟩ := hmemH k0 hk0T
    exact k0_pair_bound hc' hn hxξ H hH0 hf0 hN0 hk0mid hdist0 (hηk0 hN0) hℓ hκ0 hκ
  · intro i hi hkT
    obtain ⟨hf0, hN0, hH0⟩ := hmemH _ hkT
    exact other_pair_bound hc' hn hxξ H hH0 hf0 hN0 (a := (i : ℝ) + 1 / 2)
      (by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith) (hdN i hi) hℓ hκ0 hκ
  · intro i hi hkT
    obtain ⟨hf0, hN0, hH0⟩ := hmemH _ hkT
    exact other_pair_bound hc' hn hxξ H hH0 hf0 hN0 (a := (i : ℝ) + 1)
      (by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith) (hdF i hi) hℓ hκ0 hκ

/-- **The hole product of a modified ramped comb** (`rem:thmU` Step (3), "The pair at `k₀`" and "The other
seven hole pairs"): for `x` in the reference cell `n ≥ 10⁵` and a modified comb with `RampedHoleHyp`,
`∏_{k∈H∩(f,N]} ρ_k ≥ (1 - 16ℓ_n) min(1, 16η_n²)(1 - 128κ²) · (1 - δ)⁷ · (16647192576/23591176505) ·
(1 - 3500/n)`, `δ = 10κ + ℓ_n²`. -/
theorem rampedHole_prod_lower {c' x κ : ℝ} (hc' : 0 < c') {n : ℕ} (hn : 100000 ≤ n)
    (hx : inCell c' n x) {f N : ℕ} {σ η : ℕ → ℝ} (H : RampedHoleHyp c' f N n σ η κ)
    (hfn : f + 4 ≤ n) (hℓ : siteGap c' n ≤ 1 / 16) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 98) :
    ((1 - 16 * siteGap c' n) * (min 1 (16 * η n ^ 2) * (1 - 128 * κ ^ 2))) *
        ((1 - (10 * κ + siteGap c' n ^ 2)) ^ 7 * holeProdConst *
          (1 - 7 / 4 * ((1 + 2000 / (n : ℝ)) - 1))) ≤
      ∏ k ∈ holeModSet f N n, holeRho c' x σ η k := by
  have hn4 : 4 ≤ n := by omega
  have hn400 : 400 ≤ n := by omega
  have hxξ : xiStar ≤ x := by
    have := xiStar_le_chiQuantile_nat hc' (by omega : 1 ≤ n)
    exact this.trans hx.1
  have hgap : siteGap c' n = chiQuantile c' ((n + 1 : ℕ) : ℝ) - chiQuantile c' (n : ℝ) := by
    unfold siteGap; push_cast; ring
  have hx2 := hx.2
  have hx1 := hx.1
  rcases le_total (x - chiQuantile c' (n : ℝ)) (siteGap c' n / 2) with hA | hB
  · obtain ⟨gN, gF⟩ := hole_geometry_A hc' hn400 hx1 hA
    refine rampedHole_prod_layout hc' hn hxξ H hfn (k0 := n) (kN := fun i => n + 1 + i)
      (kF := fun i => n - 1 - i) (holeSet_caseA hn4) (by intro i hi; omega) (by intro i hi; omega)
      (by intro i hi j hj; omega) (by intro i hi j hj; omega) (by intro i hi j hj; omega)
      (Or.inl rfl) ?_ ?_ gN gF hℓ hκ0 hκ
    · rw [abs_of_nonneg (by linarith)]; exact hA
    · intro hnN
      exact ⟨(H.eta_mem n (by omega) hnN).1, le_rfl⟩
  · have hB' : chiQuantile c' ((n + 1 : ℕ) : ℝ) - x ≤ siteGap c' n / 2 := by
      have : chiQuantile c' ((n + 1 : ℕ) : ℝ) - x = siteGap c' n - (x - chiQuantile c' (n : ℝ)) := by
        rw [hgap]; ring
      rw [this]; linarith
    obtain ⟨gN, gF⟩ := hole_geometry_B hc' hn400 hx2.le hB'
    refine rampedHole_prod_layout hc' hn hxξ H hfn (k0 := n + 1) (kN := fun i => n - i)
      (kF := fun i => n + 2 + i) (holeSet_caseB hn4) (by intro i hi; omega) (by intro i hi; omega)
      (by intro i hi j hj; omega) (by intro i hi j hj; omega) (by intro i hi j hj; omega)
      (Or.inr rfl) ?_ ?_ gN gF hℓ hκ0 hκ
    · rw [abs_of_nonpos (by linarith)]; linarith
    · intro hnN
      exact ⟨(H.eta_mem n (by omega) (by omega)).1, H.eta_mono n (by omega) (by omega)⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedHoleHyp_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.rampedHoleHyp_ref

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.other_pair_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.other_pair_bound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.k0_pair_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.k0_pair_bound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedHole_prod_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.rampedHole_prod_lower

end FormalResearch.ModularBootstrap.Upper.Ramped
