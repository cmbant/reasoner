module

public import FormalResearch.Special.RacahKappaHLeftBand
public import FormalResearch.Special.RacahKappaHLeftEdge
public import FormalResearch.Special.RacahKappaLeft

/-!
# The a priori bound on the left part of the half-integer Racah chain

`rl_leftH`: twin of `rl_left` (`RacahKappaLeft`) for the shifted closed forms `hrAkH`, `hrCkH` (parameters `a = m + ½`, `b = n + ½`, `kl = halfLo m n`, `|a|, |b| ≤ kl + ½`): the mass of the chain to the left of a
fixed `q_c < q_*/2` is at most `ε M` as `h → 0`.  It combines the band comparison `rl_bandH`, the edge facts `rl_edgeT` (at the real rank `t = j + ½`) and the generic left-mass lemma `rl_left_mass`.

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- Real arithmetic of the final ratio. -/
lemma rl_ratioH {qs h cL ε W : ℝ} {n kmid : ℤ} (hqs : 0 < qs) (hh : 0 < h) (hhq : h ≤ qs / 44) (hcL : cL ≤ qs / 8) (hW : 0 < W)
    (hε : 0 < ε) (hcLε : cL ≤ ε * qs / (8 * W)) (hhε : h ≤ ε * qs / (4 * W)) (hn : (n : ℝ) * h ≤ cL + h / 2)
    (hkmid : qs / 2 - 5 * h < (kmid : ℝ) * h) :
    n < kmid ∧ (n : ℝ) * W ≤ ε * ((kmid - n : ℤ) : ℝ) := by
  have h1 : (kmid : ℝ) * h - (n : ℝ) * h ≥ qs / 4 := by nlinarith only [hkmid, hn, hhq, hcL]
  have hlt : (n : ℝ) < kmid := by
    by_contra hc
    push Not at hc
    nlinarith only [h1, hh, hc, hqs]
  refine ⟨by exact_mod_cast hlt, ?_⟩
  push_cast
  have e1 : cL * W ≤ ε * qs / 8 := by
    rw [le_div_iff₀ (by positivity)] at hcLε; linarith only [hcLε]
  have e2 : h * W ≤ ε * qs / 4 := by
    rw [le_div_iff₀ (by positivity)] at hhε; linarith only [hhε]
  have e3 : ((n : ℝ) * h) * W ≤ (cL + h / 2) * W := mul_le_mul_of_nonneg_right hn hW.le
  have e4 : ε * (qs / 4) ≤ ε * ((kmid : ℝ) * h - (n : ℝ) * h) := mul_le_mul_of_nonneg_left h1 hε.le
  have : h * ((n : ℝ) * W) ≤ h * (ε * ((kmid : ℝ) - n)) := by nlinarith only [e1, e2, e3, e4]
  exact le_of_mul_le_mul_left this hh

/-- **The a priori bound on the left part** (see the module docstring). -/
theorem rl_leftH {P Q a b τ x qs : ℝ} {kl : ℤ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1)
    (hs : 1 - x ^ 2 = rkS P Q x * qs ^ 2) (hspos : 0 < rkS P Q x) (hqs : 0 < qs) (hα : 0 < 1 - P * qs ^ 2)
    (hβ : 0 < 1 - Q * qs ^ 2) (hka : |a| ≤ (kl : ℝ) + 1 / 2) (hkb : |b| ≤ (kl : ℝ) + 1 / 2) (hkl0 : 0 ≤ kl)
    (Fam : ℝ → (ℤ → ℝ) → ℝ → Prop)
    (hrows : ∀ h Y M, Fam h Y M → ∀ k : ℤ, 1 ≤ k → jac (hrAkH P Q a b h) (hrCkH P Q τ x a b h) Y k = 0)
    (hlow : ∀ h Y M, Fam h Y M → ∀ k : ℤ, k < kl → Y k = 0)
    (hMle : ∀ h Y M, Fam h Y M → 0 < h → ∀ k0 k1 : ℤ, 0 ≤ k0 → ∑ k ∈ Finset.Ico k0 k1, Y k ^ 2 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ cL hL : ℝ, 0 < cL ∧ 0 < hL ∧ ∀ h Y M, Fam h Y M → 0 < h → h ≤ hL →
      ∀ kc : ℤ, (kc : ℝ) * h ≤ cL → ∑ k ∈ Finset.Ico 0 kc, Y k ^ 2 ≤ ε * M := by
  obtain ⟨K0b, h0b, Cb, hK0b2, hh0b, hh0b1, hCb, hKa, hKb, band⟩ :=
    rl_bandH (a := a) (b := b) (τ := τ) hP hQ hτ hs hspos hqs hα hβ
  set K0 : ℤ := max (K0b : ℤ) (kl + 1) with hK0
  have hK0b : (K0b : ℤ) ≤ K0 := le_max_left _ _
  have hK0min : kl + 1 ≤ K0 := le_max_right _ _
  have hK02 : (2 : ℤ) ≤ K0 := by
    have : (2 : ℤ) ≤ K0b := by exact_mod_cast hK0b2
    omega
  have hK0R : (2 : ℝ) ≤ (K0 : ℝ) := by exact_mod_cast hK02
  obtain ⟨D, hD, edge⟩ := rl_edgeT (a := a) (b := b) (τ := τ) (x := x) (kmin := (kl : ℝ) + 1 / 2) (Kr := (K0 : ℝ) + 1) hP hQ hτ hqs hα hβ
    hka hkb (by have : (0 : ℝ) ≤ kl := by exact_mod_cast hkl0
                linarith) (by have : (kl : ℝ) + 1 ≤ K0 := by exact_mod_cast hK0min
                              linarith)
  set W : ℝ := 2 * Cb * ((1 + D) ^ K0.toNat * Cb) with hW
  have hWp : 0 < W := by
    have : 0 < Cb := by linarith
    rw [hW]; positivity
  intro ε hε
  set cL : ℝ := min (qs / 8) (ε * qs / (8 * W)) with hcL
  have hcLp : 0 < cL := lt_min (by positivity) (by positivity)
  set hL : ℝ := min (min h0b (qs / 44)) (min (min (ε * qs / (4 * W)) (qs / (2 * ((K0 : ℝ) + 1)))) (cL / K0)) with hhL
  have hhLp : 0 < hL := lt_min (lt_min hh0b (by positivity)) (lt_min (lt_min (by positivity) (by positivity)) (by positivity))
  refine ⟨cL, hL, hcLp, hhLp, ?_⟩
  intro h Y M hF hh hhL' kc hkc
  have hMnn : 0 ≤ M := by simpa using hMle h Y M hF hh 0 0 le_rfl
  have hh0 : h ≤ h0b := hhL'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhq : h ≤ qs / 44 := hhL'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhε : h ≤ ε * qs / (4 * W) := hhL'.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hhK : h ≤ qs / (2 * ((K0 : ℝ) + 1)) := hhL'.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hhc : h ≤ cL / K0 := hhL'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hKh : ((K0 : ℝ) + 1) * h ≤ qs / 2 := by
    rw [le_div_iff₀ (by positivity)] at hhK; linarith only [hhK]
  have hKc : (K0 : ℝ) * h ≤ cL := by
    rw [le_div_iff₀ (by positivity)] at hhc; linarith only [hhc]
  set n : ℤ := max kc K0 with hn
  have hKn : K0 ≤ n := le_max_right _ _
  have hn0 : 0 ≤ n := by omega
  have hnh : (n : ℝ) * h ≤ cL + h / 2 := by
    rcases le_total kc K0 with hc | hc
    · rw [hn, max_eq_right hc]; linarith only [hKc, hh]
    · rw [hn, max_eq_left hc]; linarith only [hkc, hh]
  -- the right end of the band
  set kmid : ℤ := ⌊qs / (2 * h)⌋ - 4 with hkm
  have hfl1 : (⌊qs / (2 * h)⌋ : ℝ) ≤ qs / (2 * h) := Int.floor_le _
  have hfl2 : qs / (2 * h) < (⌊qs / (2 * h)⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hkm1 : ((kmid : ℝ) + 4) * h ≤ qs / 2 := by
    have : (kmid : ℝ) + 4 = (⌊qs / (2 * h)⌋ : ℝ) := by rw [hkm]; push_cast; ring
    rw [this]
    rw [le_div_iff₀ (by positivity)] at hfl1
    linarith only [hfl1]
  have hkm2 : qs / 2 - 5 * h < (kmid : ℝ) * h := by
    rw [div_lt_iff₀ (by positivity)] at hfl2
    have : (kmid : ℝ) = (⌊qs / (2 * h)⌋ : ℝ) - 4 := by rw [hkm]; push_cast; ring
    rw [this]
    nlinarith only [hfl2, hh]
  obtain ⟨hlt, hrat⟩ := rl_ratioH (qs := qs) (h := h) (cL := cL) (ε := ε) (W := W) (n := n) (kmid := kmid) hqs hh hhq
    (min_le_left _ _) hWp hε (min_le_right _ _) hhε hnh hkm2
  have hh1 : h ≤ 1 := hh0.trans hh0b1
  have hcomp : ∀ i j : ℤ, K0 ≤ i → i ≤ j → j ≤ kmid → Y j ^ 2 + Y (j - 1) ^ 2 ≤ Cb * (Y i ^ 2 + Y (i - 1) ^ 2) ∧
      Y i ^ 2 + Y (i - 1) ^ 2 ≤ Cb * (Y j ^ 2 + Y (j - 1) ^ 2) := by
    intro i j hi hij hj
    refine band h Y hh hh0 i j (by omega) hij ?_ (fun k hk => hrows h Y M hF k (by rw [Finset.mem_Ico] at hk; omega))
    have : (j : ℝ) ≤ (kmid : ℝ) := by exact_mod_cast hj
    nlinarith only [this, hkm1, hh]
  have hback : ∀ j ∈ Finset.Icc (kl + 1) (K0 - 1), jac (hrAkH P Q a b h) (hrCkH P Q τ x a b h) Y j = 0 ∧
      0 < hrAkH P Q a b h j ∧ hrCkH P Q τ x a b h j ^ 2 + hrAkH P Q a b h (j + 1) ^ 2 ≤ D * hrAkH P Q a b h j ^ 2 := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj1 : (kl : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hj2 : (j : ℝ) + 1 ≤ (K0 : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ K0)
    obtain ⟨e1, e2⟩ := edge h hh hh1 hKh ((j : ℝ) + 1 / 2) (by linarith) (by linarith)
    refine ⟨hrows h Y M hF j (by omega), ?_, ?_⟩
    · rw [hrAkH_eq]; exact e1
    · rw [hrAkH_succ, hrAkH_eq, hrCkH_eq]; exact e2
  have hM := hMle h Y M hF hh n (kmid + 1) hn0
  have hmass := rl_left_mass (a := hrAkH P Q a b h) (c := hrCkH P Q τ x a b h) (Y := Y) (kmin := kl) (K0 := K0) (kc := n)
    (kmid := kmid) (D := D) (Cb := Cb) (M := M) hD hCb (by omega) hkl0 hK0min hKn hlt (hlow h Y M hF) hback hcomp hM
  have hsub : ∑ k ∈ Finset.Ico 0 kc, Y k ^ 2 ≤ ∑ k ∈ Finset.Ico 0 n, Y k ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (le_max_left _ _)) (fun k _ _ => by positivity)
  refine hsub.trans (hmass.trans ?_)
  have hκ : (0 : ℝ) < ((kmid - n : ℤ) : ℝ) := by
    have : (0 : ℤ) < kmid - n := by omega
    exact_mod_cast this
  have e1 : (n : ℝ) * ((1 + D) ^ K0.toNat * Cb) * (2 * Cb * M / ((kmid - n : ℤ) : ℝ)) =
      ((n : ℝ) * W) * M / ((kmid - n : ℤ) : ℝ) := by
    rw [hW]; field_simp
  rw [e1, div_le_iff₀ hκ]
  nlinarith only [hrat, hMnn]


end FormalResearch.Special
