module

public import FormalResearch.ModularBootstrap.Upper.Assembly.Families

/-!
# Lower bound for the same-site factor `Q_k` on compacta below `a_1`

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` (`sr:Sigma`, Step 3, the estimate `Q ≥ 1/2` on
`K`), `upper_transfer.tex` (`ut:G`, `ut:E`).

For the design `D(N, η, ·)` and a real `u` that is not an Airy zero, the real factors
`designFac N η u j = ((u - u_j)² + ε_j²)/(u - a_j)²` (`j ≥ 2`) have a convergent product `T = Q(u)`, and
`G_k(u) = Ai(u)²/(u - a_1)² · Q(u)` (`Gd_eq_mul_prod`).

* `exists_designFac_lower`: for `-r ≤ u` there is `J` with `Q(u) ≥ 1/2` for every design with `N ≥ J`
  (and every height `η`): the factors with `j ≤ N` are `≥ 1`, those with `j > N` are
  `≥ (1 - C_Z/(2 j²))² ≥ exp(-2 C_Z/j²)`, using `|a_j - u_j^W| ≤ C_Z j^{-4/3}` and `|a_j| ≥ 2.5 j^{2/3}`.
* `Gd_lower`: the lower bound field `G_lower` of `SameSiteTailBounds (Gd N₀)`, for every `N₀`.

Everything is proved.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Positivity

/-- The real factor `((u - u_j)² + ε_j²)/(u - a_j)²` of `Q` for the design `D(N, η, ·)`. -/
noncomputable def designFac (N : ℕ) (η u : ℝ) (j : ℕ) : ℝ :=
  ((u - designSiteU N j) ^ 2 + (designWidthU N η j) ^ 2) / (u - airyZero j) ^ 2

lemma ofReal_designFac (N : ℕ) (η u : ℝ) (j : ℕ) :
    (designFac N η u j : ℂ) =
      airyProdFactor (designSiteU N) (designWidthU N η) j (u : ℂ) := by
  unfold designFac airyProdFactor
  push_cast; rfl

private lemma hasProd_real_of_complex' {f : ℕ → ℝ} {z : ℂ}
    (hf : HasProd (fun m => (f m : ℂ)) z) :
    HasProd f z.re ∧ z = (z.re : ℂ) := by
  have hre : Tendsto (fun s : Finset ℕ => ∏ m ∈ s, f m) atTop (𝓝 z.re) := by
    have h1 := Complex.continuous_re.continuousAt.tendsto.comp hf
    refine h1.congr fun s => ?_
    dsimp only [Function.comp_def]
    have : ∏ m ∈ s, (f m : ℂ) = ((∏ m ∈ s, f m : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
  have him : z.im = 0 := by
    have h1 := Complex.continuous_im.continuousAt.tendsto.comp hf
    have h0 : ∀ s : Finset ℕ, (∏ m ∈ s, (f m : ℂ)).im = 0 := fun s => by
      have : ∏ m ∈ s, (f m : ℂ) = ((∏ m ∈ s, f m : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.ofReal_im]
    have h1' : Tendsto (fun _ : Finset ℕ => (0 : ℝ)) atTop (𝓝 z.im) := by
      refine h1.congr fun s => ?_; dsimp only [Function.comp_def]; rw [h0 s]
    exact (tendsto_const_nhds_iff.mp h1').symm
  exact ⟨hre, Complex.ext rfl him⟩

/-- At a real point away from the Airy zeros the tail product is the real product of `designFac`. -/
lemma designFac_hasProd (N : ℕ) (η : ℝ) {u : ℝ} (hu : ∀ n : ℕ, 1 ≤ n → u ≠ airyZero n) :
    ∃ T : ℝ, HasProd (fun m : ℕ => designFac N η u (m + 2)) T ∧
      airyProdTail 1 (designSiteU N) (designWidthU N η) (u : ℂ) = (T : ℂ) := by
  have hH := design_tail_hypothesis N η
  have hne : ∀ k : ℕ, 1 < k → (u : ℂ) ≠ (airyZero k : ℂ) := fun k hk h =>
    hu k (by omega) (Complex.ofReal_injective h)
  have hp := hasProd_airyProdTail hH hne
  have hp' : HasProd (fun m : ℕ => (designFac N η u (m + 2) : ℂ))
      (airyProdTail 1 (designSiteU N) (designWidthU N η) (u : ℂ)) := by
    refine hp.congr_fun fun m => ?_
    rw [show 1 + 1 + m = m + 2 by ring, ofReal_designFac]
  obtain ⟨hre, hcm⟩ := hasProd_real_of_complex' hp'
  exact ⟨_, hre, hcm⟩

/-- `G_k(u) = Ai(u)²/(u - a_1)² · Q(u)` away from the Airy zeros. -/
lemma Gd_eq_mul_prod (N₀ k : ℕ) {u : ℝ} (hu : ∀ n : ℕ, 1 ≤ n → u ≠ airyZero n) :
    ∃ T : ℝ, HasProd (fun m : ℕ => designFac (N₀ + k) (1 / ((k : ℝ) + 4)) u (m + 2)) T ∧
      Gd N₀ k u = airyAi u ^ 2 / (u - airyZero 1) ^ 2 * T := by
  obtain ⟨T, hT, htail⟩ := designFac_hasProd (N₀ + k) (1 / ((k : ℝ) + 4)) hu
  refine ⟨T, hT, ?_⟩
  have h1 : u ≠ airyZero 1 := hu 1 le_rfl
  rw [Gd_of_ne N₀ k h1]
  have hz : ∀ n : ℕ, 1 ≤ n → (u : ℂ) ≠ (airyZero n : ℂ) := fun n hn h =>
    hu n hn (Complex.ofReal_injective h)
  have hne : u - airyZero 1 ≠ 0 := sub_ne_zero.mpr h1
  have hne' : airyZero 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  unfold designWinW designWindowW
  rw [airyWindowProd_eq_of_ne 1 _ _ _ hz, htail, airyAiC_ofReal]
  have hc : (-(airyAi u : ℂ) ^ 2 * ((u : ℂ) - ((airyZero 1 - 0 : ℝ) : ℂ)) /
      (∏ k ∈ Finset.Icc 1 1, ((u : ℂ) - (airyZero k : ℂ)) ^ 2) * (T : ℂ)) =
      ((-(airyAi u) ^ 2 * (u - airyZero 1) / (u - airyZero 1) ^ 2 * T : ℝ) : ℂ) := by
    simp only [Finset.Icc_self, Finset.prod_singleton, sub_zero]
    push_cast
    ring
  rw [hc, Complex.ofReal_re]
  field_simp
  ring

lemma Gd_pos_of_ne (N₀ k : ℕ) {u : ℝ} (hu : u ≠ airyZero 1) : 0 < Gd N₀ k u := by
  rw [Gd_of_ne N₀ k hu]
  obtain ⟨S, hS, h⟩ := designWinW_zero_eq_neg_mul_pos (N₀ + k) (eta_pos k) u
  rw [h]
  have hne : airyZero 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  rw [show -(u - airyZero 1) * S / (airyZero 1 - u) = S by field_simp; ring]
  exact hS

private lemma exp_neg_two_mul_le_one_sub' {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.exp (-2 * t) ≤ 1 - t := by
  have h1 : 1 ≤ (1 - t) * (1 + 2 * t) := by nlinarith
  have h2 : 1 + 2 * t ≤ Real.exp (2 * t) := by linarith [Real.add_one_le_exp (2 * t)]
  have hpos1 : 0 < 1 + 2 * t := by linarith
  have hpos2 : 0 < Real.exp (2 * t) := Real.exp_pos _
  rw [show (-2 * t : ℝ) = -(2 * t) by ring, Real.exp_neg]
  calc (Real.exp (2 * t))⁻¹ ≤ (1 + 2 * t)⁻¹ := inv_anti₀ hpos1 h2
    _ ≤ 1 - t := by rw [← one_div, div_le_iff₀ hpos1]; linarith

private lemma sum_inv_sq_le (N : ℕ) (hN : 1 ≤ N) (s : Finset ℕ) (hs : ∀ m ∈ s, N < m + 2) :
    ∑ m ∈ s, 1 / ((m + 2 : ℕ) : ℝ) ^ 2 ≤ 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set g : ℕ → ℝ := fun m => if N < m + 2 then 1 / ((m + 2 : ℕ) : ℝ) ^ 2 else 0 with hg
  have hg0 : ∀ m, 0 ≤ g m := fun m => by
    simp only [hg]; split_ifs <;> positivity
  have hind : ∀ M : ℕ, ∑ m ∈ Finset.range M, g m ≤ 1 / (N : ℝ) - 1 / ((max N (M + 1) : ℕ) : ℝ) := by
    intro M
    induction M with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, max_eq_left hN, sub_self, le_refl]
    | succ M ih =>
      rw [Finset.sum_range_succ]
      by_cases h : N < M + 2
      · have hmax1 : max N (M + 1) = M + 1 := max_eq_right (by omega)
        have hmax2 : max N (M + 1 + 1) = M + 2 := max_eq_right (by omega)
        rw [hmax1] at ih
        rw [hmax2]
        have hgM : g M = 1 / ((M + 2 : ℕ) : ℝ) ^ 2 := by simp [hg, h]
        rw [hgM]
        have hM1 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
        have hM2 : (0 : ℝ) < ((M + 2 : ℕ) : ℝ) := by positivity
        have hstep : 1 / ((M + 2 : ℕ) : ℝ) ^ 2 ≤ 1 / ((M + 1 : ℕ) : ℝ) - 1 / ((M + 2 : ℕ) : ℝ) := by
          have hc : ((M + 2 : ℕ) : ℝ) = ((M + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
          rw [div_sub_div _ _ hM1.ne' hM2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
          rw [hc]; nlinarith
        linarith
      · have hmax1 : max N (M + 1) = N := max_eq_left (by omega)
        have hmax2 : max N (M + 1 + 1) = N := max_eq_left (by omega)
        rw [hmax1] at ih
        rw [hmax2]
        have hgM : g M = 0 := by simp [hg, h]
        rw [hgM]; linarith
  have hsub : ∀ m ∈ s, m < s.sup id + 1 := fun m hm =>
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)
  calc ∑ m ∈ s, 1 / ((m + 2 : ℕ) : ℝ) ^ 2 = ∑ m ∈ s, g m :=
        Finset.sum_congr rfl fun m hm => by simp [hg, hs m hm]
    _ ≤ ∑ m ∈ Finset.range (s.sup id + 1), g m :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun m hm => Finset.mem_range.mpr (hsub m hm)) (fun m _ _ => hg0 m)
    _ ≤ 1 / (N : ℝ) - 1 / ((max N (s.sup id + 1 + 1) : ℕ) : ℝ) := hind _
    _ ≤ 1 / (N : ℝ) := by
        have : (0 : ℝ) ≤ 1 / ((max N (s.sup id + 1 + 1) : ℕ) : ℝ) := by positivity
        linarith

/-- The factors `j > N` are `≥ exp(-4 x_j)`, `x_j = (C_Z/2)/j²`. -/
lemma designFac_tail_lower {C_Z : ℝ} (hC_Z : 0 < C_Z)
    (hZ : ∀ k : ℕ, 1 ≤ k → |deltaWKB k| ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ)))
    {r : ℝ} {N j : ℕ} (hj : N < j) (hN2 : 2 ≤ N) (hNC : 4 * C_Z ≤ N) (hNr : (2 * r) ^ 3 ≤ N)
    (η u : ℝ) (hur : -r ≤ u) :
    Real.exp (-4 * ((C_Z / 2) / (j : ℝ) ^ 2)) ≤ designFac N η u j := by
  have hj2 : 2 ≤ j := by omega
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
  set p : ℝ := (j : ℝ) ^ (2 / 3 : ℝ) with hp
  have hp0 : 0 < p := Real.rpow_pos_of_pos hjpos _
  have hp3 : p ^ 3 = (j : ℝ) ^ 2 := by
    rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul hjpos.le]; norm_num
  have hNj : (N : ℝ) < j := by exact_mod_cast hj
  have hr : 2 * r ≤ p := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hp0.le ?_
    rw [hp3]; nlinarith
  obtain ⟨h25, -⟩ := airyZero_abs_bounds hj2
  have ht : 2 * p ≤ u - airyZero j := by norm_num at h25; linarith
  set t : ℝ := u - airyZero j with htdef
  have htpos : 0 < t := by linarith
  have hδ := hZ j (by omega)
  have hrp : (j : ℝ) ^ (-(4 / 3 : ℝ)) = p * ((j : ℝ) ^ 2)⁻¹ := by
    rw [hp, show (-(4 / 3 : ℝ)) = 2 / 3 + (-(2 : ℝ)) by norm_num, Real.rpow_add hjpos,
      Real.rpow_neg hjpos.le, Real.rpow_two]
  have hj2sq : (0 : ℝ) < (j : ℝ) ^ 2 := by positivity
  set x : ℝ := (C_Z / 2) / (j : ℝ) ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by
    rw [hx, div_le_iff₀ hj2sq]
    nlinarith
  have hratio : |deltaWKB j| / t ≤ x := by
    rw [div_le_iff₀ htpos]
    have h1 : x * (2 * p) ≤ x * t := mul_le_mul_of_nonneg_left ht hx0
    have h2 : x * (2 * p) = C_Z * (p * ((j : ℝ) ^ 2)⁻¹) := by
      rw [hx]; field_simp
    rw [hrp] at hδ
    linarith
  have hs : designSiteU N j = uWKB j := by
    simp [designSiteU, not_le.mpr hj]
  have hdel : u - uWKB j = t + deltaWKB j := by
    unfold deltaWKB; rw [htdef]; ring
  have hneg : -(|deltaWKB j| / t) ≤ deltaWKB j / t := by
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (neg_abs_le _) htpos.le
  have hbase : 1 - x ≤ 1 + deltaWKB j / t := by linarith
  have hsq : (1 - x) ^ 2 ≤ (1 + deltaWKB j / t) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hbase 2
  have hexp : Real.exp (-4 * x) ≤ (1 - x) ^ 2 := by
    have h1 := exp_neg_two_mul_le_one_sub' hx0 hx1
    have h2 : Real.exp (-4 * x) = (Real.exp (-2 * x)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h2]
    exact pow_le_pow_left₀ (Real.exp_pos _).le h1 2
  have hfac : ((u - uWKB j) ^ 2) / t ^ 2 ≤ designFac N η u j := by
    unfold designFac
    rw [hs]
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (designWidthU N η j)]) (sq_nonneg _)
  have heq : ((u - uWKB j) ^ 2) / t ^ 2 = (1 + deltaWKB j / t) ^ 2 := by
    rw [hdel]; field_simp
  rw [← heq] at hsq
  linarith

/-- **Product lower bound.**  If `HasProd g T` and the factor `g m` is at least `1` for `m + 2 ≤ N` and at least
`exp(-4 (C_Z/2)/(m+2)²)` beyond, with `4 C_Z ≤ N`, then `T ≥ 1/2` (the summation step of
`exists_designFac_lower`, for an arbitrary factor sequence). -/
lemma hasProd_ge_half_of_tail_lower {C_Z : ℝ} (hC_Z : 0 < C_Z) {N : ℕ} (hN2 : 2 ≤ N)
    (hNC : 4 * C_Z ≤ N) {g : ℕ → ℝ} {T : ℝ} (hT : HasProd g T)
    (hfac : ∀ m : ℕ, (if m + 2 ≤ N then (1 : ℝ)
      else Real.exp (-4 * ((C_Z / 2) / ((m + 2 : ℕ) : ℝ) ^ 2))) ≤ g m) :
    1 / 2 ≤ T := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hge : ∀ s : Finset ℕ, 1 / 2 ≤ ∏ m ∈ s, g m := by
    intro s
    have h1 : ∏ m ∈ s, (if m + 2 ≤ N then (1 : ℝ)
          else Real.exp (-4 * ((C_Z / 2) / ((m + 2 : ℕ) : ℝ) ^ 2))) ≤
        ∏ m ∈ s, g m :=
      Finset.prod_le_prod₀ (fun m _ => by split_ifs; exact zero_le_one; exact (Real.exp_pos _).le)
        (fun m _ => hfac m)
    refine le_trans ?_ h1
    have h2 : ∏ m ∈ s, (if m + 2 ≤ N then (1 : ℝ)
          else Real.exp (-4 * ((C_Z / 2) / ((m + 2 : ℕ) : ℝ) ^ 2))) =
        Real.exp (∑ m ∈ s, if m + 2 ≤ N then (0 : ℝ)
          else -4 * ((C_Z / 2) / ((m + 2 : ℕ) : ℝ) ^ 2)) := by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl fun m _ => by split_ifs <;> simp
    rw [h2]
    set s' := s.filter (fun m => ¬(m + 2 ≤ N)) with hs'
    have h3 : (∑ m ∈ s, if m + 2 ≤ N then (0 : ℝ)
          else -4 * ((C_Z / 2) / ((m + 2 : ℕ) : ℝ) ^ 2)) =
        -(2 * C_Z) * ∑ m ∈ s', 1 / ((m + 2 : ℕ) : ℝ) ^ 2 := by
      rw [hs', Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> ring
    have h4 := sum_inv_sq_le N (by omega) s' (fun m hm => by
      have := (Finset.mem_filter.mp hm).2
      omega)
    have h5 : -(2 * C_Z) * ∑ m ∈ s', 1 / ((m + 2 : ℕ) : ℝ) ^ 2 ≥ -(1 / 2) := by
      have h6 : 2 * C_Z * ∑ m ∈ s', 1 / ((m + 2 : ℕ) : ℝ) ^ 2 ≤ 2 * C_Z * (1 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      have h7 : 2 * C_Z * (1 / (N : ℝ)) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ hNpos]; linarith
      linarith
    calc (1 : ℝ) / 2 ≤ Real.exp (-(1 / 2)) := by
          have := Real.add_one_le_exp (-(1 / 2) : ℝ); linarith
      _ ≤ _ := Real.exp_le_exp.mpr (by rw [h3]; linarith)
  exact ge_of_tendsto hT (Eventually.of_forall hge)

/-- For `-r ≤ u` away from the Airy zeros, `Q(u) ≥ 1/2` for every design with `N ≥ J(r)`. -/
lemma exists_designFac_lower (r : ℝ) :
    ∃ J : ℕ, ∀ N : ℕ, J ≤ N → ∀ (η u : ℝ), -r ≤ u → (∀ n : ℕ, 1 ≤ n → u ≠ airyZero n) →
      ∀ T : ℝ, HasProd (fun m : ℕ => designFac N η u (m + 2)) T → 1 / 2 ≤ T := by
  obtain ⟨C_Z, hC_Z, hZ⟩ := deltaWKB_le_exists
  refine ⟨⌈max (max (4 * C_Z) ((2 * r) ^ 3)) 2⌉₊, fun N hN η u hur hu T hT => ?_⟩
  have hNge : max (max (4 * C_Z) ((2 * r) ^ 3)) 2 ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hNC : 4 * C_Z ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hNge)
  have hNr : (2 * r) ^ 3 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hNge)
  have hN2' : (2 : ℝ) ≤ N := (le_max_right _ _).trans hNge
  have hN2 : 2 ≤ N := by exact_mod_cast hN2'
  have hfac : ∀ m : ℕ, (if m + 2 ≤ N then (1 : ℝ)
      else Real.exp (-4 * ((C_Z / 2) / ((m + 2 : ℕ) : ℝ) ^ 2))) ≤ designFac N η u (m + 2) := by
    intro m
    split_ifs with h
    · unfold designFac
      have hs : designSiteU N (m + 2) = airyZero (m + 2) := by simp [designSiteU, h]
      rw [hs]
      have hne : 0 < (u - airyZero (m + 2)) ^ 2 := by
        have := sub_ne_zero.mpr (hu (m + 2) (by omega))
        positivity
      rw [le_div_iff₀ hne]
      nlinarith [sq_nonneg (designWidthU N η (m + 2))]
    · exact designFac_tail_lower hC_Z hZ (by omega) hN2 hNC hNr η u hur
  exact hasProd_ge_half_of_tail_lower hC_Z hN2 hNC hT hfac

/-- **The lower bound field of `SameSiteTailBounds (Gd N₀)`**: `Q_k ≥ 1/2` on compacta below `a_1` for
large `k`, for every `N₀`. -/
theorem Gd_lower (N₀ : ℕ) (K : Set ℝ) (hK : IsCompact K) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ u ∈ K, u < airyNode 0 →
      (1 / 2) * (airyAi u) ^ 2 / (u - airyNode 0) ^ 2 ≤ Gd N₀ k u := by
  obtain ⟨m, hm⟩ := hK.bddBelow
  obtain ⟨J, hJ⟩ := exists_designFac_lower (-m)
  refine ⟨J, fun k hk u huK hua => ?_⟩
  rw [airyNode_zero] at hua ⊢
  have hum : -(-m) ≤ u := by rw [neg_neg]; exact hm huK
  have hJk : J ≤ N₀ + k := le_trans hk (Nat.le_add_left k N₀)
  by_cases hz : ∀ n : ℕ, 1 ≤ n → u ≠ airyZero n
  · obtain ⟨T, hT, hG⟩ := Gd_eq_mul_prod N₀ k hz
    have hT2 : 1 / 2 ≤ T := hJ (N₀ + k) hJk _ u hum hz T hT
    rw [hG]
    have hF : 0 ≤ airyAi u ^ 2 / (u - airyZero 1) ^ 2 := by positivity
    calc (1 / 2) * airyAi u ^ 2 / (u - airyZero 1) ^ 2
        = (1 / 2) * (airyAi u ^ 2 / (u - airyZero 1) ^ 2) := by ring
      _ ≤ airyAi u ^ 2 / (u - airyZero 1) ^ 2 * T := by nlinarith
  · push Not at hz
    obtain ⟨n, hn, hun⟩ := hz
    have hAi : airyAi u = 0 := by rw [hun]; exact airyAi_airyZero n
    rw [hAi]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div]
    exact (Gd_pos_of_ne N₀ k hua.ne).le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.Gd_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Gd_lower

end FormalResearch.ModularBootstrap.Upper.Assembly
