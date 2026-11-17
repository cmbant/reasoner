module

public import FormalResearch.Special.BulkKappaSharp
public import FormalResearch.Special.RacahKappaFam
public import FormalResearch.Special.DiscreteAiryKappaMass
public import FormalResearch.Special.DiscreteAiryLimitChains2Twist

/-!
# The `3j` chain as a family for the abstract sharp theorem (integer data, both turn types)

`bk_hahn_int`: for integers `M, σ` and a rational node shape `x ∈ (-1,1)`, `x ≠ 0` (`τ = +1` for `x > 0`, `τ = -1` for `x < 0` with the twisted chain `(-1)^k Ŷ_k`), the family of the actual `3j` chains
`Ŷ = hahn3jY M σ N x` at the lattice nodes `xLat M σ N n = x` (`h = 1/N`, Gauss weight `N`) satisfies the hypotheses of `bk_sharp_abs` (`P = 1, Q = 0, a = M, b = σ`, `s = rkS 1 0 x = 1`, `q_* = √(1-x²)`):

* rows: `hahn_class_chain`, `hahn_class_chain_neg`;
* Gauss weight: `kk_sum_le`, `kk_le_sum` (`DiscreteAiryKappaMass`); `Ŷ_k² ≤ N`: `hahn_chain_abs_le`; support in `[max(|M|,|σ|), N-1]`;
* monotone tail beyond `q_* + h`: `hr_hardedge_decay` at the hard edge `ẽ((N h)²) = ẽ(1) = 0`;
* left a priori bound: `rl_left` (`RacahKappaLeft`).

**Claim class: proved.**  The family is `bkFamHahn`; the node-level statements are in `BulkKappaHahnInst`.
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The family of (twisted) integer `3j` chains of shape `x` at the lattice nodes, with `h ≤ hm`. -/
def bkFamHahn (M σ : ℤ) (x : ℚ) (u : ℤ → ℝ) (hm : ℝ) : ℝ → (ℤ → ℝ) → ℝ → Prop := fun h Y Mm =>
  0 < h ∧ h ≤ hm ∧ ∃ (N : ℤ) (n : ℕ), max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧
    xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x ∧ h = 1 / (N : ℝ) ∧ Y = (fun j => u j * hahn3jY M σ N x j) ∧ Mm = (N : ℝ)

/-- The geometry of the Hahn turn `(P, Q) = (1, 0)`: `q_* = √(1-x²)`, `Φ_τ(q_*²) = 0`. -/
lemma bkh_geom {τ x : ℝ} (hxτ : (τ = 1 ∧ 0 < x) ∨ (τ = -1 ∧ x < 0)) (hx1 : |x| < 1) :
    0 < √(1 - x ^ 2) ∧ τ ^ 2 = 1 ∧ 0 < 1 - τ * x ∧ 0 < 1 - 1 * √(1 - x ^ 2) ^ 2 ∧ 0 < 1 - 0 * √(1 - x ^ 2) ^ 2 ∧
      Phi 1 0 τ x (√(1 - x ^ 2) ^ 2) = 0 := by
  have hx : -1 < x ∧ x < 1 := abs_lt.1 hx1
  have h1 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hq2 : √(1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt h1.le
  rcases hxτ with ⟨rfl, hx0⟩ | ⟨rfl, hx0⟩
  · refine ⟨Real.sqrt_pos.2 h1, by norm_num, by linarith, by rw [hq2]; nlinarith, by simp, ?_⟩
    unfold Phi etilde
    rw [hq2]
    have : (1 - 1 * (1 - x ^ 2)) * (1 - 0 * (1 - x ^ 2)) = x ^ 2 := by ring
    rw [this, Real.sqrt_sq hx0.le]
    simp
  · refine ⟨Real.sqrt_pos.2 h1, by norm_num, by linarith, by rw [hq2]; nlinarith, by simp, ?_⟩
    exact hahn_turn_neg hx0 hx.1

/-- Gauss weight: the sum of squares of the chain over `[0, END)` is `N` once the chain vanishes from `END` on. -/
lemma bkh_meq (M σ N : ℤ) (hN : max |M| |σ| < N) (n : ℕ) (hn : (n : ℤ) < N - max |M| |σ|) (u : ℤ → ℝ) (hu : ∀ k, u k ^ 2 = 1)
    (END : ℤ) (hEND : ∀ k : ℤ, END ≤ k → u k * hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) k = 0) :
    ∑ k ∈ Finset.Ico 0 END, (u k * hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) k) ^ 2 = N := by
  have hsq : ∀ j : ℤ, (u j * hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) j) ^ 2 =
      hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) j ^ 2 := by
    intro j; rw [mul_pow, hu j, one_mul]
  simp only [hsq]
  have hL0 : 0 ≤ max |M| |σ| := le_trans (abs_nonneg M) (le_max_left _ _)
  have hzero : ∀ k : ℤ, END ≤ k → hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) k = 0 := by
    intro k hk
    have := hEND k hk
    rcases mul_eq_zero.1 this with h1 | h1
    · have := hu k; rw [h1] at this; norm_num at this
    · exact h1
  have e1 : ∑ k ∈ Finset.Ico 0 (max END N), hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) k ^ 2 =
      ∑ k ∈ Finset.Ico 0 END, hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) k ^ 2 := by
    symm
    apply Finset.sum_subset
    · intro k hk; rw [Finset.mem_Ico] at hk ⊢; have := le_max_left END N; omega
    · intro k hk hk'
      rw [Finset.mem_Ico] at hk hk'
      have : END ≤ k := by by_contra hh; exact hk' ⟨hk.1, by omega⟩
      rw [hzero k this]; simp
  rw [← e1]
  apply le_antisymm (kk_sum_le M σ N hN n hn _)
  apply kk_le_sum M σ N hN n hn
  intro k hk1 hk2
  rw [Finset.mem_Ico]
  have := le_max_right END N
  omega

/-- Hard-edge monotone tail of the (twisted) integer `3j` chain beyond `q_* + h` (`h = 1/N`, hard edge `ẽ(1) = 0`). -/
lemma bkh_mono {τ x qs : ℝ} (hqs : 0 < qs) (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x) (hturn : Phi 1 0 τ x (qs ^ 2) = 0)
    (M σ N : ℤ) (hN : 0 < N) (Y0 u : ℤ → ℝ) (hu : ∀ k, u k ^ 2 = 1)
    (hsupp0 : ∀ k : ℤ, ¬ (|M| ≤ k ∧ |σ| ≤ k ∧ k ≤ N - 1) → Y0 k = 0)
    (hhM : 1 / (N : ℝ) * (2 * hrM (M : ℝ) (σ : ℝ)) ≤ qs)
    (hhC : 1 / (N : ℝ) * hrRho 1 0 (M : ℝ) (σ : ℝ) qs ≤ 2 * ((1 - τ * x) / qs ^ 2) * qs)
    (hrows : ∀ k : ℤ, 1 ≤ k → jac (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (hrCk 1 0 τ x (M : ℝ) (σ : ℝ) (1 / (N : ℝ)))
      (fun j => u j * Y0 j) k = 0) :
    ∀ k' k : ℤ, qs + 1 / (N : ℝ) ≤ ((k' : ℝ) + 1 / 2) * (1 / (N : ℝ)) → k' ≤ k →
      (u k * Y0 k) ^ 2 ≤ (u k' * Y0 k') ^ 2 := by
  intro k' k hk' hkk
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hsq : ∀ j : ℤ, (u j * Y0 j) ^ 2 = Y0 j ^ 2 := by
    intro j; rw [mul_pow, hu j, one_mul]
  have hk'0 : 0 ≤ k' := by
    have h1 : (0 : ℝ) < ((k' : ℝ) + 1 / 2) * (1 / (N : ℝ)) := by nlinarith only [hk', hqs, hh]
    have h2 : (-1 : ℝ) < k' := by
      by_contra hc; push Not at hc; nlinarith only [h1, hc, hh]
    have : (-1 : ℤ) < k' := by exact_mod_cast h2
    omega
  rw [hsq, hsq]
  by_cases hbig : N - 1 < k'
  · rw [hsupp0 k (fun h => by omega)]
    simpa using sq_nonneg (Y0 k')
  push Not at hbig
  by_cases hbig2 : N - 1 < k
  · rw [hsupp0 k (fun h => by omega)]
    simpa using sq_nonneg (Y0 k')
  push Not at hbig2
  obtain ⟨kmax, hkmax⟩ : ∃ kmax : ℕ, (kmax : ℤ) = N - 1 := ⟨(N - 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hNk : ((kmax : ℝ) + 1) * (1 / (N : ℝ)) = 1 := by
    have : ((kmax : ℝ) + 1) = (N : ℝ) := by
      have : ((kmax : ℤ) : ℝ) = ((N - 1 : ℤ) : ℝ) := by rw [hkmax]
      push_cast at this; linarith
    rw [this]; field_simp
  have hedge : (((kmax : ℝ) + 1) * (1 / (N : ℝ))) ^ 2 ∈ Dom 1 0 := by
    rw [hNk]; refine ⟨by norm_num, by norm_num, by norm_num⟩
  have hedge0 : etilde 1 0 ((((kmax : ℝ) + 1) * (1 / (N : ℝ))) ^ 2) = 0 := by
    rw [hNk, etilde_hahn]; simp
  have key := hr_hardedge_decay (P := 1) (Q := 0) zero_le_one le_rfl (M : ℝ) (σ : ℝ) τ x qs (1 / (N : ℝ)) hqs hh hτ hκ hturn hhM hhC
    kmax k'.toNat hedge hedge0
    (by
      have : ((k'.toNat : ℕ) : ℝ) = (k' : ℝ) := by
        have : ((k'.toNat : ℕ) : ℤ) = k' := Int.toNat_of_nonneg hk'0
        exact_mod_cast this
      rw [this]; nlinarith only [hk', hh])
    (by omega)
    (fun j => u j * Y0 j)
    (fun k hk => hrows k (by rw [Finset.mem_Icc] at hk; omega))
  have := key k (by omega) (by omega)
  have h2 : (|u k * Y0 k|) ^ 2 ≤ (|u (k'.toNat : ℤ) * Y0 (k'.toNat : ℤ)|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) this 2
  have e : ((k'.toNat : ℕ) : ℤ) = k' := Int.toNat_of_nonneg hk'0
  rw [e, sq_abs, sq_abs, hsq, hsq] at h2
  exact h2

/-- **The integer `3j` chain satisfies the hypotheses of the abstract sharp theorem** (see the module docstring): the constants and the three conclusions
`BkOut` (window, sharp amplitude, bulk form) for the family `bkFamHahn` (`h ≤ h_m`). -/
theorem bk_hahn_int (M σ : ℤ) (x : ℚ) (τ : ℝ) (u : ℤ → ℝ) (hxτ : (τ = 1 ∧ 0 < (x : ℝ)) ∨ (τ = -1 ∧ (x : ℝ) < 0))
    (hx1 : |(x : ℝ)| < 1) (hu : ∀ k, u k ^ 2 = 1)
    (hrowsAll : ∀ N : ℤ, 0 < N → ∀ k : ℤ, 1 ≤ k →
      jac (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (hrCk 1 0 τ (x : ℝ) (M : ℝ) (σ : ℝ) (1 / (N : ℝ)))
        (fun j => u j * hahn3jY M σ N x j) k = 0) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA δA hm : ℝ), 0 < r ∧ r ≤ √(1 - (x : ℝ) ^ 2) / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧ 0 < δA ∧ 0 < hm ∧
      BkOut (1 / 2) (fun δ => δ ^ 3 / 2) 1 0 τ (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bkFamHahn M σ x u hm) r Cmu ξ0 gmax gmin c1 c2 CA δA := by
  obtain ⟨hqs, hτ, hκ, hα, hβ, hturn⟩ := bkh_geom hxτ hx1
  set qs : ℝ := √(1 - (x : ℝ) ^ 2) with hqsdef
  have hP : (0 : ℝ) ≤ 1 := zero_le_one
  have hQ : (0 : ℝ) ≤ 0 := le_rfl
  have hs := rk_turn_id hP hQ hτ hα hβ hturn
  have hS : rkS 1 0 (x : ℝ) = 1 := by simp [rkS]
  have hspos : 0 < rkS 1 0 (x : ℝ) := by rw [hS]; norm_num
  set ρ : ℝ := hrRho 1 0 (M : ℝ) (σ : ℝ) qs with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; unfold hrRho; positivity
  have hM1 : 1 ≤ hrM (M : ℝ) (σ : ℝ) := le_max_left _ _
  have hκq : 0 ≤ 2 * ((1 - τ * (x : ℝ)) / qs ^ 2) * qs := by positivity
  set hm : ℝ := min (qs / (2 * hrM (M : ℝ) (σ : ℝ))) ((2 * ((1 - τ * (x : ℝ)) / qs ^ 2) * qs) / (ρ + 1)) with hhm
  have hmpos : 0 < hm := lt_min (by positivity) (by
    apply div_pos _ (by positivity)
    have : 0 < (1 - τ * (x : ℝ)) / qs ^ 2 := by positivity
    positivity)
  set kmin : ℤ := max |M| |σ| with hkmin
  have hkmin0 : 0 ≤ kmin := le_trans (abs_nonneg M) (le_max_left _ _)
  have hka : |(M : ℝ)| ≤ (kmin : ℝ) := by
    have : |M| ≤ kmin := le_max_left _ _
    exact_mod_cast this
  have hkb : |(σ : ℝ)| ≤ (kmin : ℝ) := by
    have : |σ| ≤ kmin := le_max_right _ _
    exact_mod_cast this
  have hsqY : ∀ (N : ℤ) (j : ℤ), (u j * hahn3jY M σ N x j) ^ 2 = hahn3jY M σ N x j ^ 2 := by
    intro N j; rw [mul_pow, hu j, one_mul]
  have hzero : ∀ (N : ℤ) (j : ℤ), u j * hahn3jY M σ N x j = 0 → hahn3jY M σ N x j = 0 := by
    intro N j h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · have := hu j; rw [h1] at this; norm_num at this
    · exact h1
  set Fam := bkFamHahn M σ x u hm with hFam
  have hrowsF : ∀ h Y Mm, Fam h Y Mm → ∀ k : ℤ, 1 ≤ k → jac (hrAk 1 0 (M : ℝ) (σ : ℝ) h) (hrCk 1 0 τ (x : ℝ) (M : ℝ) (σ : ℝ) h) Y k = 0 := by
    rintro h Y Mm ⟨hh, hhm, N, n, hN, hn, hxn, rfl, rfl, rfl⟩ k hk
    have hN0 : 0 < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
    exact hrowsAll N hN0 k hk
  have hmassF : ∀ h Y Mm, Fam h Y Mm → 0 < h → Mm * h * Real.sqrt (rkS 1 0 (x : ℝ)) = 1 := by
    rintro h Y Mm ⟨hh, hhm, N, n, hN, hn, hxn, rfl, rfl, rfl⟩ -
    have hN0 : (0 : ℝ) < N := by exact_mod_cast lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
    rw [hS, Real.sqrt_one]; field_simp
  have hYleF : ∀ h Y Mm, Fam h Y Mm → ∀ k : ℤ, Y k ^ 2 ≤ Mm := by
    rintro h Y Mm ⟨hh, hhm, N, n, hN, hn, hxn, rfl, rfl, rfl⟩ k
    show (u k * hahn3jY M σ N x k) ^ 2 ≤ N
    rw [hsqY]
    have h1 := hahn_chain_abs_le M σ N hN n hn k
    rw [hxn] at h1
    have h2 : (0 : ℝ) ≤ N := by exact_mod_cast (lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN).le
    calc hahn3jY M σ N x k ^ 2 = |hahn3jY M σ N x k| ^ 2 := (sq_abs _).symm
      _ ≤ Real.sqrt (N : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = N := Real.sq_sqrt h2
  have hsuppF : ∀ h Y Mm, Fam h Y Mm → ∀ k : ℤ, 1 < ((k : ℝ) + 1 / 2) * h → Y k = 0 := by
    rintro h Y Mm ⟨hh, hhm, N, n, hN, hn, hxn, rfl, rfl, rfl⟩ k hk
    have hN0 : (0 : ℝ) < N := by exact_mod_cast lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
    have h1 : (N : ℝ) < (k : ℝ) + 1 / 2 := by
      rw [← div_eq_mul_one_div, lt_div_iff₀ hN0] at hk; linarith
    have h2 : N ≤ k := by
      by_contra hc; push Not at hc
      have : (k : ℝ) + 1 ≤ N := by exact_mod_cast (by omega : k + 1 ≤ N)
      linarith
    show u k * hahn3jY M σ N x k = 0
    rw [hahn_chain_support M σ N x k (fun h => by omega), mul_zero]
  have hMeqF : ∀ h Y Mm, Fam h Y Mm → ∀ END : ℤ, (∀ k : ℤ, END ≤ k → Y k = 0) → ∑ k ∈ Finset.Ico 0 END, Y k ^ 2 = Mm := by
    rintro h Y Mm ⟨hh, hhm, N, n, hN, hn, rfl, rfl, rfl, rfl⟩ END hEND
    exact bkh_meq M σ N hN n hn u hu END hEND
  have hmonoF : ∀ h Y Mm, Fam h Y Mm → ∀ k' k : ℤ, qs + h ≤ ((k' : ℝ) + 1 / 2) * h → k' ≤ k → Y k ^ 2 ≤ Y k' ^ 2 := by
    rintro h Y Mm ⟨hh, hhm, N, n, hN, hn, hxn, rfl, rfl, rfl⟩ k' k hk' hkk
    have hN0 : 0 < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
    have h1 : 1 / (N : ℝ) ≤ qs / (2 * hrM (M : ℝ) (σ : ℝ)) := hhm.trans (min_le_left _ _)
    have h2 : 1 / (N : ℝ) ≤ (2 * ((1 - τ * (x : ℝ)) / qs ^ 2) * qs) / (ρ + 1) := hhm.trans (min_le_right _ _)
    have hhM : 1 / (N : ℝ) * (2 * hrM (M : ℝ) (σ : ℝ)) ≤ qs := by
      rw [le_div_iff₀ (by positivity)] at h1; linarith only [h1]
    have hhC : 1 / (N : ℝ) * ρ ≤ 2 * ((1 - τ * (x : ℝ)) / qs ^ 2) * qs := by
      rw [le_div_iff₀ (by positivity)] at h2
      nlinarith only [h2, hρ0, hκq, hh]
    exact bkh_mono hqs hτ hκ hturn M σ N hN0 (hahn3jY M σ N x) u hu
      (fun k hk => hahn_chain_support M σ N x k hk) hhM hhC (fun k hk => hrowsAll N hN0 k hk) k' k hk' hkk
  have hlowF : ∀ h Y Mm, Fam h Y Mm → ∀ k : ℤ, k < kmin → Y k = 0 := by
    rintro h Y Mm ⟨hh, hhm, N, n, hN, hn, hxn, rfl, rfl, rfl⟩ k hk
    show u k * hahn3jY M σ N x k = 0
    rw [hahn_chain_support M σ N x k (fun h => by
      have : max |M| |σ| ≤ k := max_le h.1 h.2.1
      omega), mul_zero]
  have hLeftF := rl_left (a := (M : ℝ)) (b := (σ : ℝ)) (kmin := kmin) hP hQ hτ hs hspos hqs hα hβ hka hkb hkmin0 Fam hrowsF hlowF
    (rk_mle hsuppF hMeqF)
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, H⟩ :=
    bk_sharp_abs hP hQ (M : ℝ) (σ : ℝ) τ (x : ℝ) qs hqs hτ hκ hα hβ hturn (rk_hosc0 hP hQ hτ hqs hκ hα hβ hturn) 1 zero_le_one Fam hrowsF
      hmassF hYleF hsuppF hMeqF hmonoF (fun ε hε => by
        obtain ⟨cL, hL, hcL, hhL, HL⟩ := hLeftF ε hε
        exact ⟨cL, hL, hcL, hhL, HL⟩)
  exact ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hmpos, H⟩

/-- info: 'FormalResearch.Special.bk_hahn_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bk_hahn_int

end FormalResearch.Special
