module

public import FormalResearch.Special.DiscreteAiryKappaChart2
public import FormalResearch.Special.DiscreteAiryKappaMass
public import FormalResearch.Special.DiscreteAiryKappaOrderSetup

/-!
# Order-sharp `|κ| ≍ N^{1/6}` for the actual `3j` chain (plan K1, assembly)

Fix integers `M, σ` and a rational `x ∈ (0,1)`; `h = 1/N = δ³`.  `hahn_chain_kappa_order` extends `hahn_chain_kappa`
(`DiscreteAiryKappaMain`) with two-sided bounds, uniform in `N` at the lattice nodes:

`c_lo ≤ κ² δ ≤ c_up`, i.e. `c_lo N^{1/3} ≤ κ² ≤ c_up N^{1/3}` (`δ = N^{-1/3}`).

* **upper** (`kk_ub_final`): the lattice sum `Σ Ai(X_k)²` over `-δ^{-2}s₀² ≤ X_k ≤ -1` is `≳ δ^{-2}` (`kai_sum_lower`, from the antiderivative
  `x Ai² - Ai'²` and `airyKer_diag_neg`), so `N = ΣŶ² ≥ Σ_{window} Ŷ² ≳ κ² δ^{-2}`;
* **lower** (`kk_lb_final`): `N = ΣŶ²` is bounded by the left bound `kl_hahn_left` (`Ai(X_J)² ≲ δ`), the window lattice sum (`kai_sum_upper_bound`), the
  `Ai` envelope up to `X ≈ 1/δ`, and the monotone decay `kr_chain_mono` beyond: `N ≤ Q κ² δ^{-2}`.

The chart constants `g_min, g_max, c₁, c₂` come from `kc2_hahn_full` (`DiscreteAiryKappaChart2`); the pointwise matching of `Ŷ = κ g Ai + μ g Bi`
is that of `hahn_chain_airy_full`, with `|μ|` exponentially small (`kk_mu_small`).

**Claim class: proved**, all constants existential (depending on `M, σ, x`); not sharp.  The *sharp* constant `κ² = 2N^{1/3}(1 + o(1))`
(numerics) is **not** proved here: it needs the amplitude relation between the chart's `g` and the Ermakov profile (`DiscreteAiryKappaBand3j`)
through the whole oscillatory region, i.e. the Airy matching `I = κ² h^{1/3}/π`.
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **Order-sharp `|κ|` for the actual `3j` chain at a lattice node** (see the module docstring): the conclusion of `hahn_chain_kappa`
with `|κ| ≥ κ_min` replaced by `c_lo ≤ κ² δ ≤ c_up` (`δ³ = 1/N`), i.e. `|κ| ≍ N^{1/6}`. -/
theorem hahn_chain_kappa_order (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ (r ε0 C Cmu ξ0 clo cup : ℝ), 0 < r ∧ 0 < ε0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < clo ∧ 0 < cup ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N → (n : ℤ) < N - max |M| |σ| →
        xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x → 1 / (N : ℝ) ≤ ε0 →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = 1 / (N : ℝ) ∧ ∃ J m Nw : ℤ, 1 ≤ J ∧ J < Nw ∧ J ≤ m ∧ m < Nw ∧
          (∀ k ∈ Finset.Icc J (Nw + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - Real.sqrt (1 - (x : ℝ) ^ 2)| ≤ r) ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) - r ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((J : ℝ) + 1 / 2) * δ ^ 3 < Real.sqrt (1 - (x : ℝ) ^ 2) - r + δ ^ 3 ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((m : ℝ) + 1 / 2) * δ ^ 3 < Real.sqrt (1 - (x : ℝ) ^ 2) + δ ^ 3 ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) + r / 4 ≤ ((Nw : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((Nw : ℝ) + 1 + 1 / 2) * δ ^ 3 ≤ Real.sqrt (1 - (x : ℝ) ^ 2) + r / 2 ∧
          DaiFull (hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) (δ ^ 3))
            (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ)
            (fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2)) (dalQ (δ ^ 3 / 2) δ k))
            J m Nw δ C Cmu ξ0 ∧
          ∃ κ μ : ℝ, clo ≤ κ ^ 2 * δ ∧ κ ^ 2 * δ ≤ cup ∧
            |μ| ≤ Cmu * Real.sqrt (N : ℝ) * Real.exp (-ξ0 / δ ^ 3) / δ ∧
            ∀ k ∈ Finset.Icc J (Nw + 1),
              |hahn3jY M σ N x k -
                  (κ * daoPhi (fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2))
                      (dalQ (δ ^ 3 / 2) δ k))
                    (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ) k +
                   μ * daoPsi (fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2))
                      (dalQ (δ ^ 3 / 2) δ k))
                    (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ) k)| ≤
                C * δ ^ 3 * (|κ| * airyWt (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k) +
                  |μ| * airyBiWt (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k)) := by
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hx1' : (x : ℝ) < 1 := by exact_mod_cast hx1
  have hq2 : Real.sqrt (1 - (x : ℝ) ^ 2) ^ 2 = 1 - (x : ℝ) ^ 2 := Real.sq_sqrt (by nlinarith)
  have hqs : 0 < Real.sqrt (1 - (x : ℝ) ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hturn : Phi 1 0 1 (x : ℝ) (Real.sqrt (1 - (x : ℝ) ^ 2) ^ 2) = 0 := by
    unfold Phi etilde
    rw [hq2]
    have : (1 - 1 * (1 - (x : ℝ) ^ 2)) * (1 - 0 * (1 - (x : ℝ) ^ 2)) = (x : ℝ) ^ 2 := by ring
    rw [this, Real.sqrt_sq hx0'.le]
    simp
  obtain ⟨r, δ0, C, Cmu, ξ0, gmax, gmin, c1, c2, hr, hrq, hδ0, -, hC, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, H⟩ :=
    kc2_hahn_full (P := 1) (Q := 0) (by norm_num) (by norm_num) (M : ℝ) (σ : ℝ) 1 (x : ℝ)
      (Real.sqrt (1 - (x : ℝ) ^ 2)) hqs (by norm_num) (by linarith) (by rw [hq2]; nlinarith) (by simp) hturn
  set qs := Real.sqrt (1 - (x : ℝ) ^ 2) with hqsdef
  have hq1 : qs < 1 := by nlinarith
  have hqr : 0 < qs - r / 2 := by linarith
  set e : ℝ := Real.sqrt (1 - (qs - r / 2) ^ 2) with hedef
  have he2 : e ^ 2 = 1 - (qs - r / 2) ^ 2 := Real.sq_sqrt (by nlinarith)
  have hxe : (x : ℝ) < e := by
    by_contra hcon
    push Not at hcon
    have h1 : e ^ 2 ≤ (x : ℝ) ^ 2 := by nlinarith [Real.sqrt_nonneg (1 - (qs - r / 2) ^ 2)]
    nlinarith
  have he1 : e ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
  set K0 : ℕ := ⌈kl_K0real (M : ℝ) (σ : ℝ) (x : ℝ) e⌉₊ with hK0def
  have hK0 : kl_K0real (M : ℝ) (σ : ℝ) (x : ℝ) e ≤ (K0 : ℝ) := Nat.le_ceil _
  set Cl : ℝ := ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 with hCldef
  have hCl : 1 ≤ Cl := ke_C_ge_one K0 hx0' hxe he1
  set Aκ : ℝ := 3 * gmax + C with hAκ
  set Aμ : ℝ := 3600 * gmax + 8 * C with hAμ
  have hAκ0 : 0 < Aκ := by positivity
  have hAμ0 : 0 < Aμ := by positivity
  obtain ⟨ε1, hε1, Hε⟩ := kf_small (x := (x : ℝ)) (qs := qs) (r := r) (δ0 := δ0) (Cmu := Cmu) (Aμ := Aμ)
    (ξ0 := ξ0) (μ0 := |(M : ℝ) * σ|) (m0 := |(M : ℝ)| + |(σ : ℝ)|) K0 hx0' hqs hr hδ0 hCmu hAμ0 hξ0
    (abs_nonneg _) (by positivity) (by linarith)
  have h8Cl : 0 < 8 * Cl := by linarith
  have hc2 : 0 < c2 := lt_of_lt_of_le hc1 hc12
  set κmin : ℝ := 1 / (Aκ * Real.sqrt (8 * Cl)) with hκmindef
  have hκmin : 0 < κmin := by positivity
  set σ0 : ℝ := min (√(3 * c1 * r / 4)) (1 / (20 * c2)) with hσ0
  have hσ0p : 0 < σ0 := lt_min (Real.sqrt_pos.2 (by positivity)) (by positivity)
  set B0 : ℝ := (450 * gmax + C) * Cmu with hB0def
  have hB0 : 0 ≤ B0 := by positivity
  set δ1 : ℝ := min (1 / 2) (min (c1 * r / (8 * (c2 + 1))) (min (σ0 / 100) (min (gmin ^ 2 * c1 / (80 * c2 * σ0 * (C + 1) ^ 2))
    (min (σ0 ^ 2 / 2) (min (ξ0 / 14) (κmin * ξ0 ^ 3 / (48 * (B0 + 1)))))))) with hδ1def
  have hδ1p : 0 < δ1 := by
    refine lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity))))))
  set Rc : ℝ := r + 3 with hRc
  set R0 : ℝ := c2 * (r + 1) with hR0
  set Qc : ℝ := kkQ c1 c2 gmax C σ0 R0 Rc Cl with hQc
  have hQpos : 0 < Qc := by
    rw [hQc]; unfold kkQ
    have : 0 < (1 / c1 + 1) * (3 * gmax + C + 1) ^ 2 := by positivity
    have h2 : 0 ≤ Cl * (20 * gmax ^ 2 / σ0 + 8 * (C + 1) ^ 2) := by positivity
    have h3 : 0 ≤ 2 * gmax ^ 2 * ((√R0 / Real.pi + 1 + 2 * c2 * R0) / c1 + 9 * (5 / (4 * c1) + 2)) + 2 * (C + 1) ^ 2 * Rc := by
      positivity
    have h4 : 0 ≤ 18 * gmax ^ 2 + 2 * (C + 1) ^ 2 := by positivity
    linarith
  refine ⟨r, min ε1 (δ1 ^ 3), C, Cmu, ξ0, 1 / Qc, 80 * c2 / (gmin ^ 2 * σ0), hr, lt_min hε1 (by positivity), hC, hCmu, hξ0,
    by positivity, by positivity, ?_⟩
  intro N n hN hn hxn hNε
  have hN0 : (0 : ℤ) < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hh0 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  obtain ⟨hNε1, hNε2⟩ := le_min_iff.1 hNε
  obtain ⟨⟨δ, hδp, hδ3, hδle, hδsq⟩, hhr, hK3, hc4, hc5, hc6⟩ := Hε _ hh0 hNε1
  have hδδ1 : δ ≤ δ1 := by
    have : δ ^ 3 ≤ δ1 ^ 3 := by rw [hδ3]; exact hNε2
    exact le_of_pow_le_pow_left₀ (by norm_num) hδ1p.le this
  obtain ⟨hδhalf, hδrest⟩ := le_min_iff.1 hδδ1
  obtain ⟨hδc, hδrest⟩ := le_min_iff.1 hδrest
  obtain ⟨hδσ, hδrest⟩ := le_min_iff.1 hδrest
  obtain ⟨hδ5, hδrest⟩ := le_min_iff.1 hδrest
  obtain ⟨hδs, hδrest⟩ := le_min_iff.1 hδrest
  obtain ⟨hδξ, hδμ⟩ := le_min_iff.1 hδrest
  have hδ1' : δ ≤ 1 := by linarith
  obtain ⟨J, m, Nw, hJ, hJN, hJm, hmN, hwin, h1, h2, h3, h4, h5, h6, hg, hXm, hgl, hgap, hX0m, hXN, Hc⟩ :=
    H δ hδp hδle
  have hδ31 : δ ^ 3 ≤ 1 := pow_le_one₀ hδp.le hδ1'
  have hδ3r : δ ^ 3 ≤ r / 8 := by rw [hδ3]; exact hhr
  have hδ3pos : 0 < δ ^ 3 := pow_pos hδp 3
  have hm1 : m + 1 ≤ Nw := kf_idx_lt hδ3pos hδ3r h4 h5
  set X : ℤ → ℝ := turnX (hrU 1 0 1 (x : ℝ)) qs (δ ^ 3 / 2) δ with hXdef
  set g : ℤ → ℝ := fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) qs (dalQ (δ ^ 3 / 2) δ k) with hgdef
  have hrows' : ∀ k ∈ Finset.Icc (J + 1) Nw,
      jac (hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) (δ ^ 3)) (hahn3jY M σ N x) k = 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [hδ3]
    exact hahn_class_chain M σ N x hN0 k (by omega)
  have hmono := kr_chain_mono M σ N m x hN0 hx0' hq2 hqs (by rw [← hδ3]; exact h3) hc4
    (kf_hh2 hh0 (by linarith) (abs_nonneg _) hc5) hc6
  have hYN : |hahn3jY M σ N x Nw| ≤ |hahn3jY M σ N x (m + 1)| := sq_le_sq.1 (hmono Nw hm1)
  have hYN1 : |hahn3jY M σ N x (Nw + 1)| ≤ |hahn3jY M σ N x (m + 1)| := sq_le_sq.1 (hmono (Nw + 1) (by omega))
  obtain ⟨κ, μ, hμ, hpt⟩ := Hc.pointwise (hahn3jY M σ N x) _ hrows' hYN hYN1
  have hμ' := kf_mu_bound hδp hCmu.le (abs_nonneg _) hμ Hc.1
  have hε := kf_eps_half hδp hξ0 hAμ0 hCmu hδsq
  have hwin2 := kf_window_abs (Y := hahn3jY M σ N x) (hJm) hm1 hC.le hδ31 hAκ hAμ hg hXm hpt hμ' hε
  have hleft := kf_left (M := M) (σ := σ) (N := N) (J := J) (x := x) (qs := qs) (r := r) (e := e) (K0 := K0) hN0 hx0'
    hxe he1 he2 hqr hK0 hK3 hhr (by rw [← hδ3]; exact h1) (by rw [← hδ3]; exact h2)
  have hall := kf_assemble (Y := hahn3jY M σ N x) (Aκ := Aκ) (κ := κ) (Cl := Cl) hJm hCl hwin2 hleft
    (fun k hk => hmono k hk)
  have hmass := kf_mass_le M σ N hN n hn (B := 8 * Cl * Aκ ^ 2 * κ ^ 2) (by rw [hxn]; exact hall)
  have hB1 : 1 ≤ 8 * Cl * Aκ ^ 2 * κ ^ 2 := by
    by_contra hcon
    push Not at hcon
    have : (N : ℝ) * (8 * Cl * Aκ ^ 2 * κ ^ 2) < N * 1 := mul_lt_mul_of_pos_left hcon hNr
    linarith
  have hYs : |hahn3jY M σ N x (m + 1)| ≤ Real.sqrt (N : ℝ) := by
    have := hahn_chain_abs_le M σ N hN n hn (m + 1)
    rwa [hxn] at this
  have hμ2 : |μ| ≤ Cmu * Real.sqrt (N : ℝ) * Real.exp (-ξ0 / δ ^ 3) / δ := by
    refine hμ'.trans ?_
    have h0 : 0 ≤ Real.exp (-ξ0 / δ ^ 3) / δ := by positivity
    calc Cmu * |hahn3jY M σ N x (m + 1)| * (Real.exp (-ξ0 / δ ^ 3) / δ)
        ≤ Cmu * Real.sqrt (N : ℝ) * (Real.exp (-ξ0 / δ ^ 3) / δ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYs hCmu.le) h0
      _ = _ := by ring
  have hκ : κmin ≤ |κ| := kf_kappa_ge hAκ0 h8Cl hB1
  -- exponential smallness of μ on the extended window
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : (1 : ℤ) ≤ N)
  have hNδ : 1 / δ ^ 3 = (N : ℝ) := by rw [hδ3]; field_simp
  have hμb : |μ| ≤ Cmu * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ) := by
    have hsq : Real.sqrt (N : ℝ) ≤ 1 / δ ^ 3 := by
      rw [hNδ]; exact Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
    refine hμ2.trans ?_
    have h0 : 0 ≤ Real.exp (-ξ0 / δ ^ 3) / δ := by positivity
    calc Cmu * Real.sqrt (N : ℝ) * Real.exp (-ξ0 / δ ^ 3) / δ = Cmu * Real.sqrt (N : ℝ) * (Real.exp (-ξ0 / δ ^ 3) / δ) := by ring
      _ ≤ Cmu * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hCmu.le) h0
  have hμE : (450 * gmax + C) * |μ| * Real.exp (7 / δ ^ 2) ≤ δ ^ 3 * |κ| := by
    have hsm := kk_mu_small hδp hδ1' hξ0 hB0 hδξ hδμ
    have h1' : (450 * gmax + C) * |μ| * Real.exp (7 / δ ^ 2) ≤
        (450 * gmax + C) * (Cmu * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ)) * Real.exp (7 / δ ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hμb (by positivity)) (Real.exp_pos _).le
    have e1 : (450 * gmax + C) * (Cmu * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ)) * Real.exp (7 / δ ^ 2) =
        B0 * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ) * Real.exp (7 / δ ^ 2) := by rw [hB0def]; ring
    rw [e1] at h1'
    nlinarith [mul_le_mul_of_nonneg_left hκ hδ3pos.le]
  -- the position data
  have hgapZ : ∀ k : ℤ, J ≤ k → k < Nw → c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ :=
    fun k h1 h2 => hgap k (Finset.mem_Icc.2 ⟨h1, by omega⟩)
  have hX1m : X (m + 1) ≤ 1 / 4 := hXm (m + 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)
  have h1δ : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδp]; linarith
  have hc2δ : c2 * δ ≤ 1 / 2000 := by
    have h1 : c2 * δ ≤ c2 * (σ0 / 100) := mul_le_mul_of_nonneg_left hδσ hc2.le
    have h2 : σ0 ≤ 1 / (20 * c2) := min_le_right _ _
    have h3 : c2 * σ0 ≤ 1 / 20 := by
      calc c2 * σ0 ≤ c2 * (1 / (20 * c2)) := mul_le_mul_of_nonneg_left h2 hc2.le
        _ = 1 / 20 := by field_simp
    nlinarith
  have hδc4 : δ < c1 * r / 4 := by
    have h1 : c1 * r / (8 * (c2 + 1)) ≤ c1 * r / 8 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    have h2 : 0 < c1 * r / 8 := by positivity
    linarith
  have hXNge : 1 / δ < X Nw := by
    have h1 : 1 / δ = δ / δ ^ 2 := by field_simp
    have h2 : c1 * (r / 4) / δ ^ 2 = (c1 * r / 4) / δ ^ 2 := by ring
    have h3 : δ / δ ^ 2 < (c1 * r / 4) / δ ^ 2 := div_lt_div_of_pos_right hδc4 (by positivity)
    have := hXN
    linarith
  obtain ⟨k1, hk11, hk12, hk13, hk14⟩ := kk_ivt (X := X) (J := m + 1) (b := Nw) (t := 1 / δ)
    (by linarith) hXNge hm1
  have hmonoX : ∀ k ∈ Finset.Icc J Nw, X k ≤ X (k + 1) := fun k hk => by
    have := (hgap k hk).1
    have : 0 ≤ c1 * δ := by positivity
    linarith [(hgap k hk).1]
  have hXk1 : X (k1 + 1) ≤ 1 / δ + 1 / 2 := by
    have := (hgapZ k1 (by omega) (by omega)).2
    linarith
  have hXle : ∀ k : ℤ, J ≤ k → k ≤ k1 + 1 → X k ≤ 2 / δ := by
    intro k hk1' hk2'
    have := kc_mono hmonoX k (k1 + 1) hk1' hk2' (by omega)
    have e : 2 / δ = 1 / δ + 1 / δ := by ring
    linarith
  -- pointwise remainder bound
  have hrest : ∀ k : ℤ, J ≤ k → k ≤ k1 + 1 →
      |hahn3jY M σ N x k - κ * (g k * airyAi (X k))| ≤ (C + 1) * δ ^ 3 * |κ| := by
    intro k hk1' hk2'
    have hkmem : k ∈ Finset.Icc J (Nw + 1) := Finset.mem_Icc.2 ⟨hk1', by omega⟩
    have hp := hpt k hkmem
    simp only [daoPhi, daoPsi] at hp
    exact kk_rest hC.le hδp hδ1' hgmax.le hp (hg k hkmem) (airyWt_le_one _) (kk_biwt_le hδp hδ1' (hXle k hk1' hk2'))
      (airyBiWt_pos _).le (apx_airyBi_global (X k)).1 hμE
  have hglow : ∀ k : ℤ, J ≤ k → k ≤ k1 + 1 → gmin ≤ g k := fun k hk1' hk2' =>
    hgl k (Finset.mem_Icc.2 ⟨hk1', by omega⟩)
  have hgup : ∀ k : ℤ, J ≤ k → k ≤ k1 + 1 → |g k| ≤ gmax := fun k hk1' hk2' =>
    hg k (Finset.mem_Icc.2 ⟨hk1', by omega⟩)
  -- positions
  have hpos : r - δ ^ 3 ≤ ((m - J : ℤ) : ℝ) * δ ^ 3 := by
    have e : ((m - J : ℤ) : ℝ) * δ ^ 3 = ((m : ℝ) + 1 / 2) * δ ^ 3 - ((J : ℝ) + 1 / 2) * δ ^ 3 := by push_cast; ring
    rw [e]; linarith
  have hposU : ((m - J : ℤ) : ℝ) * δ ^ 3 < r + δ ^ 3 := by
    have e : ((m - J : ℤ) : ℝ) * δ ^ 3 = ((m : ℝ) + 1 / 2) * δ ^ 3 - ((J : ℝ) + 1 / 2) * δ ^ 3 := by push_cast; ring
    rw [e]; linarith
  have hsum : ∀ (ka : ℤ) (n' : ℕ), ∑ i ∈ range n', hahn3jY M σ N x (ka + (i : ℤ)) ^ 2 ≤ 1 / δ ^ 3 := by
    intro ka n'
    have := kk_sum_le M σ N hN n hn ((Finset.range n').image (fun i : ℕ => ka + (i : ℤ)))
    rw [hxn, Finset.sum_image (by intro i _ j _ hij; simpa using hij), ← hNδ] at this
    exact this
  have hgapLow : ∀ k : ℤ, J ≤ k → k < m → c1 * δ ≤ X (k + 1) - X k := fun k h1 h2 =>
    (hgapZ k h1 (by omega)).1
  have hgapUp : ∀ k : ℤ, J ≤ k → k < m → X (k + 1) - X k ≤ c2 * δ := fun k h1 h2 =>
    (hgapZ k h1 (by omega)).2
  have hδc' : c2 * δ ^ 3 ≤ c1 * r / 8 := by
    have h0 : δ ^ 3 ≤ δ := by nlinarith [sq_nonneg δ, pow_pos hδp 2]
    have h1 : c2 * δ ^ 3 ≤ c2 * δ := mul_le_mul_of_nonneg_left h0 hc2.le
    have h2 : c2 * δ ≤ c2 * (c1 * r / (8 * (c2 + 1))) := mul_le_mul_of_nonneg_left hδc hc2.le
    have h3 : c2 * (c1 * r / (8 * (c2 + 1))) ≤ c1 * r / 8 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_pos hc1 hr]
    linarith
  have hσ2 : σ0 ^ 2 ≤ 3 * c1 * r / 4 := by
    have h := min_le_left (√(3 * c1 * r / 4)) (1 / (20 * c2))
    calc σ0 ^ 2 ≤ √(3 * c1 * r / 4) ^ 2 := pow_le_pow_left₀ hσ0p.le h 2
      _ = 3 * c1 * r / 4 := Real.sq_sqrt (by positivity)
  have hδ5' : δ ^ 5 ≤ gmin ^ 2 * c1 / (80 * c2 * σ0 * (C + 1) ^ 2) := by
    have h0 : δ ^ 5 ≤ δ := by
      have : δ ^ 4 ≤ 1 := pow_le_one₀ hδp.le hδ1'
      nlinarith [pow_pos hδp 4]
    linarith
  have hUB := kk_ub_final (X := X) (Y := hahn3jY M σ N x) (g := g) (J := J) (m := m) (δ := δ) (c1 := c1) (c2 := c2)
    (r := r) (gmin := gmin) (C := C) (κ := κ) (σ0 := σ0) hJm hδp hc1 hc12 hr hgmin hC hσ0 hδ3r hδc' (by linarith)
    hδ5' (fun k h1 h2 => hgapZ k h1 (by omega)) hX0m hpos (fun k h1 h2 => hglow k h1 (by omega))
    (fun k h1 h2 => hrest k h1 (by omega)) hsum
  -- the lower bound
  have hXJ := kk_xJ (X := X) (J := J) (m := m) (δ := δ) (c1 := c1) (c2 := c2) (r := r) (σ0 := σ0) hJm hδp hc1 hσ2 hδ3r hδc'
    hgapLow hX0m.2 hpos
  have hs : 2 * δ ^ 2 ≤ σ0 ^ 2 := by
    have : δ ^ 2 ≤ δ := by nlinarith
    linarith
  have hXJlow : -X J ≤ R0 / δ ^ 2 := by
    have hsp := kk_span_up (X := X) (ε' := c2 * δ) hJm hgapUp
    have h1 : ((m - J : ℤ) : ℝ) * (c2 * δ) ≤ c2 * (r + 1) / δ ^ 2 := by
      have h2 : ((m - J : ℤ) : ℝ) ≤ (r + δ ^ 3) / δ ^ 3 := by
        rw [le_div_iff₀ hδ3pos]; linarith
      have h3 : ((m - J : ℤ) : ℝ) * (c2 * δ) ≤ (r + δ ^ 3) / δ ^ 3 * (c2 * δ) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      have h4 : (r + δ ^ 3) / δ ^ 3 * (c2 * δ) = c2 * (r + δ ^ 3) / δ ^ 2 := by field_simp
      rw [h4] at h3
      refine h3.trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    have := hX0m.1
    rw [hR0]
    linarith
  have hkT : X (k1 + 1 - 1) ≤ 1 / δ ∧ 1 / δ ≤ X (k1 + 1) := ⟨by simpa using hk13, hk14.le⟩
  have hmonoT := kr_chain_mono M σ N (k1 + 1 - 1) x hN0 hx0' hq2 hqs
    (by
      rw [← hδ3]
      have : (m : ℝ) ≤ ((k1 + 1 - 1 : ℤ) : ℝ) := by exact_mod_cast (by omega : m ≤ k1 + 1 - 1)
      nlinarith [h3, hδ3pos])
    hc4 (kf_hh2 hh0 (by linarith) (abs_nonneg _) hc5) hc6
  have hmonoT' : ∀ k : ℤ, k1 + 1 ≤ k → hahn3jY M σ N x k ^ 2 ≤ hahn3jY M σ N x (k1 + 1) ^ 2 := by
    intro k hk
    have := hmonoT k (by omega)
    simpa using this
  have hleft' : ∀ k : ℤ, k ≤ J + 1 → hahn3jY M σ N x k ^ 2 ≤
      Cl * (hahn3jY M σ N x (J + 1) ^ 2 + hahn3jY M σ N x J ^ 2) := by
    intro k hk
    have := hleft k hk
    rwa [show J + 1 - 1 = J by ring] at this
  have hmassLB : 1 / δ ^ 3 ≤ ∑ k ∈ Finset.Ico 0 (k1 + 1 + N), hahn3jY M σ N x k ^ 2 := by
    have := kk_le_sum M σ N hN n hn (Finset.Ico 0 (k1 + 1 + N)) (fun k hk1' hk2' =>
      Finset.mem_Ico.2 ⟨le_trans (le_trans (abs_nonneg M) (le_max_left _ _)) hk1', by omega⟩)
    rw [hxn] at this
    rw [hNδ]; exact this
  have hJcnt : ((J + 2 : ℤ) : ℝ) ≤ 2 / δ ^ 3 := by
    have h8 : δ ^ 3 ≤ 1 / 8 := by
      have : δ ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hδp.le hδhalf 3
      norm_num at this; exact this
    have e : ((J + 2 : ℤ) : ℝ) * δ ^ 3 = ((J : ℝ) + 1 / 2) * δ ^ 3 + 3 / 2 * δ ^ 3 := by push_cast; ring
    rw [le_div_iff₀ hδ3pos, e]
    nlinarith
  have hmcnt : ((m + 2 - J : ℤ) : ℝ) ≤ Rc / δ ^ 3 := by
    rw [le_div_iff₀ hδ3pos]
    have e : ((m + 2 - J : ℤ) : ℝ) * δ ^ 3 = ((m - J : ℤ) : ℝ) * δ ^ 3 + 2 * δ ^ 3 := by push_cast; ring
    rw [e, hRc]; nlinarith
  have hLB := kk_lb_final (X := X) (Y := hahn3jY M σ N x) (g := g) (J := J) (m := m) (kT := k1 + 1) (NN := N) (δ := δ)
    (c1 := c1) (c2 := c2) (G := gmax) (C := C) (κ := κ) (s0 := σ0) (R0 := R0) (Rc := Rc) (Cl := Cl) hδp hδ1' hc1 hc2.le hσ0p
    hgmax.le hC.le (by positivity) (by positivity) (by linarith) (by omega) hJm (by omega) (by omega) (by linarith)
    (fun k h1' h2' => hgapZ k h1' (by omega)) hXJ hs hXJlow hX0m.1 hX1m hkT
    (fun k h1' h2' => hrest k h1' h2') (fun k h1' h2' => hgup k h1' h2') hleft' hmonoT' hmassLB (by rw [hNδ]) hJcnt hmcnt
  have hlo : 1 / Qc ≤ κ ^ 2 * δ := by
    rw [div_le_iff₀ hQpos]; linarith
  exact ⟨δ, hδp, hδ3, J, m, Nw, hJ, hJN, hJm, hm1, hwin, h1, h2, h3, h4, h5, h6, Hc, κ, μ, hlo, hUB, hμ2, hpt⟩

/-- info: 'FormalResearch.Special.hahn_chain_kappa_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_kappa_order

end FormalResearch.Special
