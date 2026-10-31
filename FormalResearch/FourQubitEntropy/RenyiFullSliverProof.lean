import FormalResearch.FourQubitEntropy.RenyiFullSliverEnt
import FormalResearch.FourQubitEntropy.RenyiFullSliverCore
import FormalResearch.FourQubitEntropy.RenyiFullProps

/-!
# `lem:fqe-cluster-sliver` (SL): proved

Paper E, `sup_renyi.tex`, `lem:fqe-cluster-sliver`.  `ClusterSliver` (`RenyiFullProps.lean`) is proved here
without hypothesis, following the paper's proof:

1. coordinates `(u, δ)` of the two charts `S = ((1-u+δ)/2,(1-u-δ)/2,u/2,u/2)` and
   `B = ((1-u)/2,(1-u)/2,(u+δ)/2,(u-δ)/2)`, `v = δ²`, and the domain reductions (`domain_S`, `domain_B`);
2. entropy estimates (SE),(SH) (`entS`, `entB`, `RenyiFullSliverEnt.lean`);
3. polynomial lower bounds (SP) with the four rows of (ST) (`slA_*`, `RenyiFullSliverCells.lean`);
4. removing `ε`, concavity in `v`, and the one-variable endpoint signs (`core_*`, `end_*`,
   `RenyiFullSliverCore.lean`).
-/

set_option exponentiation.threshold 5000

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

theorem kappa_bounds : 13856 / 10000 ≤ kappaSL ∧ kappaSL ≤ 13857 / 10000 ∧ kappaSL ^ 2 = 48 / 25 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  unfold kappaSL
  refine ⟨?_, ?_, ?_⟩
  · have : (1732 / 1000 : ℝ) ≤ Real.sqrt 3 := by
      apply Real.le_sqrt_of_sq_le; norm_num
    linarith
  · have : Real.sqrt 3 ≤ 1732125 / 1000000 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  · nlinarith [h3]

/-- The polynomial lower bound of `G_±` from the entropy estimate. -/
theorem G_ge {μ : Fin 4 → ℝ} {τ s h₂ u v y ε : ℝ} (hp : pur μ = slp u v) (ht : cub μ = slt τ u v)
    (hH : renyiSpec qS μ ≤ 1 + 39005 / 10000 * u - 5 / 2 * y + 12 / 5 * u ^ 2 - h₂) :
    slG τ s h₂ u v ε kappaSL + 5 / 2 * y ≤ Gsl s ε μ := by
  have hq0 : 0 < qS := by unfold qS; norm_num
  have hq1 : qS ≠ 1 := by unfold qS; norm_num
  have e : Gsl s ε μ = slG τ s h₂ u v ε kappaSL +
      ((1 + 39005 / 10000 * u + 12 / 5 * u ^ 2 - h₂) - renyiSpec qS μ) := by
    unfold Gsl Lam ell Fc Xs slG
    rw [renyiSpec_c1 hq0 hq1, pur_c1, cub_c1, hp, ht]
    unfold aH bH gH
    ring
  rw [e]
  linarith

/-- Domain reductions, chart `S`. -/
theorem domain_S {u v ε κ : ℝ} (hu0 : 0 ≤ u) (hu2 : 2 * u ≤ 1) (_hv0 : 0 ≤ v) (hv2 : v ≤ (1 - 2 * u) ^ 2)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 7 / 5)
    (hp : 47 / 100 ≤ 1 / 2 - u + u ^ 2 + v / 2) (hX : 0 ≤ u - u ^ 2 - v / 2 + ε)
    (hF : 11 / 25 ≤ 1 / 2 + 8 * ε - 9 / 2 * (1 - 2 * u) * v + κ * (u - u ^ 2 - v / 2 + ε)) :
    u ≤ 1 / 16 ∧ v ≤ 1 / 20 ∧ v ≤ 2 * (u - u ^ 2) + 2 * ε ∧
      v * (26 / 5 - 9 * u) ≤ 3 / 50 + 7 / 5 * (u - u ^ 2) + 21 / 10 * (26 / 5 - 9 * u) * ε := by
  have hX1 : u - u ^ 2 - v / 2 + ε ≤ 1 / 25 := by linarith
  have hw : 9 / 2 * (1 - 2 * u) * v ≤ 49 / 250 := by
    have := mul_le_mul_of_nonneg_left hX1 hκ0
    nlinarith [mul_nonneg hκ0 hX, mul_nonneg (sub_nonneg.2 hκ1) hX]
  have hu4 : u < 1 / 4 := by nlinarith
  have hv1 : v < 9 / 100 := by nlinarith
  have hu10 : u < 1 / 10 := by nlinarith
  have hv2' : v < 11 / 200 := by nlinarith
  have hu16 : u < 1 / 16 := by nlinarith
  have hv20 : v < 1 / 20 := by nlinarith
  refine ⟨hu16.le, hv20.le, by nlinarith, ?_⟩
  have hD : 0 < 26 / 5 - 9 * u := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 hκ1) hX]

/-- Domain reduction, chart `B`. -/
theorem domain_B {u v : ℝ} (hu0 : 0 ≤ u) (hu2 : 2 * u ≤ 1) (hv0 : 0 ≤ v) (hvu : v ≤ u ^ 2)
    (hp : 47 / 100 ≤ 1 / 2 - u + u ^ 2 + v / 2) : u ≤ 1 / 30 := by
  nlinarith

/-! ### The final logic -/

theorem sliver_logic {G Z c e u : ℝ} (hc : 0 < c) (he : 0 ≤ e) (hG : Z + c * e ≤ G) (hZ : 0 ≤ Z)
    (hZs : 0 < u → 0 < Z) (hu : 0 ≤ u) : 0 ≤ G ∧ (G = 0 → e = 0 ∧ u = 0) := by
  have h1 : 0 ≤ c * e := mul_nonneg hc.le he
  refine ⟨by linarith, fun h0 => ?_⟩
  have he0 : e = 0 := by
    by_contra hne
    have : 0 < e := lt_of_le_of_ne he (Ne.symm hne)
    have := mul_pos hc this
    linarith
  refine ⟨he0, ?_⟩
  by_contra hne
  have hpos : 0 < u := lt_of_le_of_ne hu (Ne.symm hne)
  have := hZs hpos
  rw [he0] at hG
  linarith

/-! ### Chart `S` -/

/-- The chart-`S` spectrum. -/
noncomputable def muS (u δ : ℝ) : Fin 4 → ℝ := ![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2]

/-- The chart-`B` spectrum. -/
noncomputable def muB (u δ : ℝ) : Fin 4 → ℝ := ![(1 - u) / 2, (1 - u) / 2, (u + δ) / 2, (u - δ) / 2]

theorem pur_muS (u δ : ℝ) : pur (muS u δ) = slp u (δ ^ 2) := by
  unfold pur muS slp; simp [Fin.sum_univ_four]; ring

theorem cub_muS (u δ : ℝ) : cub (muS u δ) = slt (1 - u) u (δ ^ 2) := by
  unfold cub muS slt; simp [Fin.sum_univ_four]; ring

theorem pur_muB (u δ : ℝ) : pur (muB u δ) = slp u (δ ^ 2) := by
  unfold pur muB slp; simp [Fin.sum_univ_four]; ring

theorem cub_muB (u δ : ℝ) : cub (muB u δ) = slt u u (δ ^ 2) := by
  unfold cub muB slt; simp [Fin.sum_univ_four]; ring

theorem muS_zero : muS 0 0 = c1 := by
  funext i; fin_cases i <;> simp [muS, c1]

theorem muB_zero : muB 0 0 = c1 := by
  funext i; fin_cases i <;> simp [muB, c1]

theorem Fc_slp (ε u v : ℝ) (τ : ℝ) :
    Fc ε (slp u v) (slt τ u v) = -1 + 8 * ε + 9 * slp u v - 12 * slt τ u v := rfl

theorem sliver_S_gen {s A B : ℝ} {P : ℝ → ℝ → ℝ}
    (rowA : ∀ u v e k : ℝ, 0 ≤ u → u ≤ 1 / 16 → 0 ≤ v → v ≤ 1 / 20 → 0 ≤ e → e ≤ 1 / 100 →
      13856 / 10000 ≤ k → k ≤ 13857 / 10000 → k ^ 2 = 48 / 25 →
      P u v + e * (A + B * v) ≤ slG (1 - u) s (113 / 100 * v + 3 / 2 * u * v - 3 / 8 * v ^ 2) u v e k)
    (rowEnd : ∀ u v y : ℝ, 0 ≤ u → u ≤ 1 / 16 → 0 ≤ v → v ≤ 2 * (u - u ^ 2) → v ≤ slV u →
      12 / 5 * u ^ 2 ≤ y → (u ≤ 1 / 140 → 357 / 50 * u ^ 2 ≤ y) → (1 / 140 ≤ u → slQ u ≤ y) →
      0 ≤ P u v + 5 / 2 * y ∧ (0 < u → 0 < P u v + 5 / 2 * y))
    (rowCore : ∀ u v v0 e : ℝ, 0 ≤ u → u ≤ 1 / 16 → 0 ≤ v0 → v0 ≤ v → v ≤ 1 / 20 → 0 ≤ e →
      v - v0 ≤ 21 / 10 * e → P u v0 + 9 / 10 * e ≤ P u v + e * (A + B * v))
    {u δ ε : ℝ} (hu0 : 0 ≤ u) (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ 1 - 2 * u) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100)
    (hp : 47 / 100 ≤ slp u (δ ^ 2)) (hX : 0 ≤ Xs ε (slp u (δ ^ 2)))
    (hF : 11 / 25 ≤ Fc ε (slp u (δ ^ 2)) (slt (1 - u) u (δ ^ 2)) + kappaSL * Xs ε (slp u (δ ^ 2))) :
    0 ≤ Gsl s ε (muS u δ) ∧ (Gsl s ε (muS u δ) = 0 → muS u δ = c1 ∧ ε = 0) := by
  obtain ⟨hk0, hk1, hk2⟩ := kappa_bounds
  have hκ0 : 0 ≤ kappaSL := by linarith
  have hv0 : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hv2 : δ ^ 2 ≤ (1 - 2 * u) ^ 2 := pow_le_pow_left₀ hδ0 hδ2 2
  have hFc : Fc ε (slp u (δ ^ 2)) (slt (1 - u) u (δ ^ 2)) =
      1 / 2 + 8 * ε - 9 / 2 * (1 - 2 * u) * δ ^ 2 := by
    unfold Fc slp slt; ring
  have hXs : Xs ε (slp u (δ ^ 2)) = u - u ^ 2 - δ ^ 2 / 2 + ε := by unfold Xs slp; ring
  rw [hFc, hXs] at hF
  rw [hXs] at hX
  obtain ⟨hu1, hv1, hva, hvb⟩ := domain_S (v := δ ^ 2) hu0 (by linarith) hv0 hv2 hε0 hε1 hκ0
    (by linarith) (by unfold slp at hp; exact hp) hX hF
  set v := δ ^ 2 with hv
  have hD : 0 < 26 / 5 - 9 * u := by linarith
  have hvV : v ≤ slV u + 21 / 10 * ε := by
    have hV : slV u * (26 / 5 - 9 * u) = 3 / 50 + 7 / 5 * (u - u ^ 2) := by
      unfold slV; exact div_mul_cancel₀ _ hD.ne'
    by_contra hlt
    push Not at hlt
    have := mul_lt_mul_of_pos_right hlt hD
    nlinarith [hV]
  have hw : 0 ≤ u - u ^ 2 := by nlinarith
  have hVn : 0 ≤ slV u := by
    unfold slV; apply div_nonneg (by nlinarith) hD.le
  set v0 := min v (min (2 * (u - u ^ 2)) (slV u)) with hv0def
  have hv0a : 0 ≤ v0 := le_min hv0 (le_min (by linarith) hVn)
  have hv0b : v0 ≤ v := min_le_left _ _
  have hv0c : v0 ≤ 2 * (u - u ^ 2) := (min_le_right _ _).trans (min_le_left _ _)
  have hv0d : v0 ≤ slV u := (min_le_right _ _).trans (min_le_right _ _)
  have hd : v - v0 ≤ 21 / 10 * ε := by
    rcases min_choice v (min (2 * (u - u ^ 2)) (slV u)) with h | h
    · rw [hv0def, h]; linarith
    · rw [hv0def, h]
      rcases min_choice (2 * (u - u ^ 2)) (slV u) with h' | h'
      · rw [h']; linarith
      · rw [h']; linarith
  have hpu := pur_muS u δ
  have hcu := cub_muS u δ
  have hH := entS hu0 hu1 hδ0 hv hv1
  have hG := G_ge (s := s) (ε := ε) hpu hcu hH
  have hy1 := yL1 hu0 hu1
  have hy2 : u ≤ 1 / 140 → 357 / 50 * u ^ 2 ≤ u ^ (8 / 5 : ℝ) := fun h => yL2 hu0 h
  have hy3 : 1 / 140 ≤ u → slQ u ≤ u ^ (8 / 5 : ℝ) := fun _ => yL3 hu0 (by linarith)
  have hA := rowA u v ε kappaSL hu0 hu1 hv0 hv1 hε0 hε1 hk0 hk1 hk2
  have hC := rowCore u v v0 ε hu0 hu1 hv0a hv0b hv1 hε0 hd
  obtain ⟨hE0, hEs⟩ := rowEnd u v0 (u ^ (8 / 5 : ℝ)) hu0 hu1 hv0a hv0c hv0d hy1 hy2 hy3
  obtain ⟨h1, h2⟩ := sliver_logic (G := Gsl s ε (muS u δ)) (Z := P u v0 + 5 / 2 * u ^ (8 / 5 : ℝ))
    (c := 9 / 10) (e := ε) (u := u) (by norm_num) hε0 (by linarith only [hG, hA, hC]) hE0 hEs hu0
  refine ⟨h1, fun h0 => ?_⟩
  obtain ⟨he, hu⟩ := h2 h0
  refine ⟨?_, he⟩
  subst hu
  have hv00 : v ≤ 0 := by rw [he] at hva; nlinarith
  have hδ : δ = 0 := by
    have h : δ ^ 2 = 0 := le_antisymm hv00 (sq_nonneg δ)
    exact (pow_eq_zero_iff two_ne_zero).1 h
  rw [hδ]; exact muS_zero

/-! ### Chart `B` -/

theorem sliver_B_gen {s A B : ℝ} {P : ℝ → ℝ → ℝ}
    (rowA : ∀ u v e k : ℝ, 0 ≤ u → u ≤ 1 / 16 → 0 ≤ v → v ≤ 1 / 20 → 0 ≤ e → e ≤ 1 / 100 →
      13856 / 10000 ≤ k → k ≤ 13857 / 10000 → k ^ 2 = 48 / 25 →
      P u v + e * (A + B * v) ≤ slG u s (3 * v) u v e k)
    (hAB : ∀ v : ℝ, 0 ≤ v → v ≤ 1 / 20 → 1 / 2 ≤ A + B * v)
    (rowEnd : ∀ u v y : ℝ, 0 ≤ u → u ≤ 1 / 30 → 0 ≤ v → v ≤ u ^ 2 → 12 / 5 * u ^ 2 ≤ y →
      0 ≤ P u v + 5 / 2 * y ∧ (0 < u → 0 < P u v + 5 / 2 * y))
    {u δ ε : ℝ} (hu0 : 0 ≤ u) (hδ0 : 0 ≤ δ) (hδu : δ ≤ u) (hu2 : 2 * u ≤ 1) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 100) (hp : 47 / 100 ≤ slp u (δ ^ 2)) :
    0 ≤ Gsl s ε (muB u δ) ∧ (Gsl s ε (muB u δ) = 0 → muB u δ = c1 ∧ ε = 0) := by
  obtain ⟨hk0, hk1, hk2⟩ := kappa_bounds
  have hv0 : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hvu : δ ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hδ0 hδu 2
  have hu30 : u ≤ 1 / 30 := domain_B hu0 hu2 hv0 hvu (by unfold slp at hp; exact hp)
  set v := δ ^ 2 with hv
  have hv1 : v ≤ 1 / 20 := by nlinarith
  have hpu := pur_muB u δ
  have hcu := cub_muB u δ
  have hH := entB hu0 hu30 hδ0 hδu hv
  have hG := G_ge (s := s) (ε := ε) hpu hcu hH
  have hy1 := yL1 hu0 (by linarith)
  have hA := rowA u v ε kappaSL hu0 (by linarith) hv0 hv1 hε0 hε1 hk0 hk1 hk2
  obtain ⟨hE0, hEs⟩ := rowEnd u v (u ^ (8 / 5 : ℝ)) hu0 hu30 hv0 hvu hy1
  have hab := hAB v hv0 hv1
  have hεab : ε / 2 ≤ ε * (A + B * v) := by nlinarith
  obtain ⟨h1, h2⟩ := sliver_logic (G := Gsl s ε (muB u δ)) (Z := P u v + 5 / 2 * u ^ (8 / 5 : ℝ))
    (c := 1 / 2) (e := ε) (u := u) (by norm_num) hε0 (by linarith only [hG, hA, hεab]) hE0 hEs hu0
  refine ⟨h1, fun h0 => ?_⟩
  obtain ⟨he, hu⟩ := h2 h0
  refine ⟨?_, he⟩
  subst hu
  have hδ : δ = 0 := le_antisymm hδu hδ0
  rw [hδ]; exact muB_zero

/-! ### `ClusterSliver` -/

theorem sliver_S_sign {s : ℝ} (hs : s = 1 ∨ s = -1) {u δ ε : ℝ} (hu0 : 0 ≤ u) (hδ0 : 0 ≤ δ)
    (hδ2 : δ ≤ 1 - 2 * u) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hp : 47 / 100 ≤ slp u (δ ^ 2))
    (hX : 0 ≤ Xs ε (slp u (δ ^ 2)))
    (hF : 11 / 25 ≤ Fc ε (slp u (δ ^ 2)) (slt (1 - u) u (δ ^ 2)) + kappaSL * Xs ε (slp u (δ ^ 2))) :
    0 ≤ Gsl s ε (muS u δ) ∧ (Gsl s ε (muS u δ) = 0 → muS u δ = c1 ∧ ε = 0) := by
  rcases hs with rfl | rfl
  · exact sliver_S_gen (A := 147 / 100) (B := 16)
      (P := fun u v => slP (2 / 125) (7 / 500) (-6) (69 / 50) (-(103 / 20)) 0 u v)
      (fun u v e k a b c d e' f g h i => slA_Sp a b c d e' f g h i)
      (fun u v y a b c d e f g => end_Sp a b c d e f g)
      (fun u v v0 e a b c d f g h => core_Sp a b c d f g h)
      hu0 hδ0 hδ2 hε0 hε1 hp hX hF
  · exact sliver_S_gen (A := 37 / 20) (B := 8)
      (P := fun u v => slP (2 / 125) (7 / 500) (-(571 / 100)) (-(33 / 10)) (-(281 / 100)) 6 u v)
      (fun u v e k a b c d e' f g h i => slA_Sm a b c d e' f g h i)
      (fun u v y a b c d e f g => end_Sm a b c d e f g)
      (fun u v v0 e a b c d f g h => core_Sm a b c d f g h)
      hu0 hδ0 hδ2 hε0 hε1 hp hX hF

theorem sliver_B_sign {s : ℝ} (hs : s = 1 ∨ s = -1) {u δ ε : ℝ} (hu0 : 0 ≤ u) (hδ0 : 0 ≤ δ)
    (hδu : δ ≤ u) (hu2 : 2 * u ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100)
    (hp : 47 / 100 ≤ slp u (δ ^ 2)) :
    0 ≤ Gsl s ε (muB u δ) ∧ (Gsl s ε (muB u δ) = 0 → muB u δ = c1 ∧ ε = 0) := by
  rcases hs with rfl | rfl
  · exact sliver_B_gen (A := 1 / 2) (B := 0)
      (P := fun u v => slP (2 / 125) (19 / 100) (-(571 / 100)) (-(3 / 2)) (-(5 / 2)) 0 u v)
      (fun u v e k a b c d e' f g h i => slA_Bp a b c d e' f g h i)
      (fun v hv _ => by nlinarith)
      (fun u v y a b c d e => coreB_Bp a b c d e)
      hu0 hδ0 hδu hu2 hε0 hε1 hp
  · exact sliver_B_gen (A := 1 / 2) (B := 0)
      (P := fun u v => slP (2 / 125) (19 / 100) (-6) 3 (-5) 0 u v)
      (fun u v e k a b c d e' f g h i => slA_Bm a b c d e' f g h i)
      (fun v hv _ => by nlinarith)
      (fun u v y a b c d e => coreB_Bm a b c d e)
      hu0 hδ0 hδu hu2 hε0 hε1 hp

/-- **`lem:fqe-cluster-sliver` (SL), proved.** -/
theorem clusterSliver : ClusterSliver := by
  intro μ hμ ε hε0 hε1 hp hX hwin s hs
  obtain ⟨⟨hnn, hsum⟩, a, b, c, hc0, hcb, hba, hform⟩ := hμ
  simp only [Fin.sum_univ_four] at hsum
  obtain ⟨F, hF1, hF2, hF3, hF4⟩ := hwin
  rcases hform with rfl | rfl
  · -- chart S:  μ = (a, b, c, c)
    have hsum' : a + b + c + c = 1 := by simpa using hsum
    have hμ : (![a, b, c, c] : Fin 4 → ℝ) = muS (2 * c) (a - b) := by
      funext i; fin_cases i <;> simp [muS] <;> linarith
    rw [hμ] at hp hX hF2 ⊢
    rw [cub_muS, pur_muS] at hF2
    rw [pur_muS] at hp hX
    exact sliver_S_sign hs (by linarith) (by linarith) (by linarith) hε0 hε1 hp hX (by linarith)
  · -- chart B:  μ = (a, a, b, c)
    have hsum' : a + a + b + c = 1 := by simpa using hsum
    have hμ : (![a, a, b, c] : Fin 4 → ℝ) = muB (1 - 2 * a) (b - c) := by
      funext i; fin_cases i <;> simp [muB] <;> linarith
    rw [hμ] at hp ⊢
    rw [pur_muB] at hp
    exact sliver_B_sign hs (by linarith) (by linarith) (by linarith) (by linarith) hε0 hε1 hp

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.clusterSliver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clusterSliver

end FormalResearch.FourQubitEntropy.RenyiFull
