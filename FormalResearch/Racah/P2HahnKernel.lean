module

public import FormalResearch.Racah.P2HahnRec
public import FormalResearch.Racah.P2HahnL1
public import FormalResearch.Racah.P2ThreeJSystem

/-!
# Explicit Hahn realization of the finite kernel, general degree (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `sec:explicitHahn`, `eq:ExactHahnKernel`.

## What is proved

* `Phi3j_hahn`: **`eq:ExactHahnKernel` for every degree `0 ≤ n ≤ D`** in the chamber `M ≥ |σ|`
  (`α = M-σ`, `β = M+σ`, `D = N-M-1` natural numbers, `u = j_++m_+ ∈ {0,…,D}`):
  `Φ_{M+n}^{M,σ}(x_u) = (-1)^α √(N/(2(M+n)+1)) √(w_H(u)/h_{H,n}) Q_n(u)`.

Proof (no `₃F₂` transformation is needed): both sides satisfy the rank recurrence.  The kernel
satisfies `Phi3j_rank_recurrence` (`kernel_rec`, in Hahn variables); the Hahn polynomials satisfy
the three-term recurrence in the degree (`hahnQ_rec`, `P2HahnRec`).  The recurrence coefficients
match after renormalisation by constants `c_n` (`hahnc`, `c_{n+1} = c_n P_n/T_{n+1}`), which gives
`Φ_{M+n} = c_n (-1)^α √(w_H) Q_n` by induction from `n = 0` (`Phi3j_hahn_zero`; for `M = σ = 0`
the recurrence is degenerate at `L = 0` and the row `L = 1` is supplied by `Phi3j_L1_M0`, from
Racah's two-term sum).  The constant is then fixed, up to the (positive) square root, by the
discrete orthogonality `Phi_discorth` (`kernel_norm`): `c_n² h_{H,n} = N/(2L+1)`, which also
identifies the Hahn norm.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

/-- `P_n = (n+α+β+1)(n+α+1)(D-n) = 2(L+1)(2L+1) A_n` with `L = (α+β)/2 + n`. -/
def hahnP (α β D n : ℕ) : ℝ := ((n : ℝ) + α + β + 1) * ((n : ℝ) + α + 1) * ((D : ℝ) - n)

/-- `T_n = N R_L √(1-L²/N²)` for `L = M+n`, in Hahn variables. -/
noncomputable def hahnT (α β D n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * ((n : ℝ) + α + β) * ((n : ℝ) + α) * ((n : ℝ) + β) *
    ((D : ℝ) + 1 - n) * ((D : ℝ) + n + α + β + 1))

lemma hahnT_sq (α β D n : ℕ) (hn : n ≤ D + 1) :
    hahnT α β D n ^ 2 = (n : ℝ) * ((n : ℝ) + α + β) * ((n : ℝ) + α) * ((n : ℝ) + β) *
      ((D : ℝ) + 1 - n) * ((D : ℝ) + n + α + β + 1) := by
  unfold hahnT
  apply Real.sq_sqrt
  have h : (n : ℝ) ≤ D + 1 := by exact_mod_cast hn
  have : 0 ≤ (D : ℝ) + 1 - n := by linarith
  positivity

lemma hahnT_pos (α β D n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ D) : 0 < hahnT α β D n := by
  unfold hahnT
  apply Real.sqrt_pos.mpr
  have h : (n : ℝ) ≤ D := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have : 0 < (D : ℝ) + 1 - n := by linarith
  positivity

lemma hahnP_pos (α β D n : ℕ) (hn : n + 1 ≤ D) : 0 < hahnP α β D n := by
  unfold hahnP
  have h : (n : ℝ) + 1 ≤ D := by exact_mod_cast hn
  have : 0 < (D : ℝ) - n := by linarith
  positivity

lemma hahnP_eq (α β D n : ℕ) :
    hahnP α β D n = 2 * (((α + β : ℝ) / 2 + n) + 1) * (2 * ((α + β : ℝ) / 2 + n) + 1) *
      hahnA α β D n := by
  unfold hahnP hahnA
  have h1 : (2 * (n : ℝ) + α + β + 1) ≠ 0 := by positivity
  have h2 : (2 * (n : ℝ) + α + β + 2) ≠ 0 := by positivity
  field_simp
  ring

lemma hahnT_rel (α β D n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ D) :
    hahnT α β D n ^ 2 =
      2 * ((α + β : ℝ) / 2 + n) * (2 * ((α + β : ℝ) / 2 + n) + 1) * hahnC α β D n *
        hahnP α β D (n - 1) := by
  rw [hahnT_sq α β D n (by omega)]
  unfold hahnC hahnP
  have h1 : (2 * (n : ℝ) + α + β) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    positivity
  have h2 : (2 * (n : ℝ) + α + β + 1) ≠ 0 := by positivity
  rw [Nat.cast_sub hn1]
  push_cast
  field_simp
  ring

/-- The pure algebra of the induction step: the rank recurrence for `Φ` against the Hahn recurrence
for `Q`.  Here `x = 1 - (α+1+2u)/N`, `N = D+(α+β)/2+1`, `M = (α+β)/2`, `σ = (β-α)/2`,
`L = M+n`. -/
lemma step_alg (α β D n u : ℕ) (hn : n + 1 ≤ D) (hL : 0 < (α : ℝ) + β + n)
    (cn cm cp q0 qm qp sw Phi1 : ℝ)
    (hq : -(u : ℝ) * q0 = hahnA α β D n * qp - (hahnA α β D n + hahnC α β D n) * q0 +
      hahnC α β D n * qm)
    (hqc : (((α + β : ℝ) / 2 + n) + 1) * (hahnT α β D n / ((D : ℝ) + (α + β) / 2 + 1)) * cm =
      cn * (2 * ((α + β : ℝ) / 2 + n) * (((α + β : ℝ) / 2 + n) + 1) *
        (2 * ((α + β : ℝ) / 2 + n) + 1) / ((D : ℝ) + (α + β) / 2 + 1)) * hahnC α β D n)
    (hcp : cp * hahnT α β D (n + 1) = cn * hahnP α β D n)
    (H : (2 * ((α + β : ℝ) / 2 + n) + 1) *
        (((α + β : ℝ) / 2 + n) * (((α + β : ℝ) / 2 + n) + 1) *
            (1 - ((α : ℝ) + 1 + 2 * u) / ((D : ℝ) + (α + β) / 2 + 1)) -
          (α + β : ℝ) / 2 * ((β - α : ℝ) / 2)) * (cn * sw * q0) =
      (((α + β : ℝ) / 2 + n) + 1) * (hahnT α β D n / ((D : ℝ) + (α + β) / 2 + 1)) *
          (cm * sw * qm) +
        ((α + β : ℝ) / 2 + n) * (hahnT α β D (n + 1) / ((D : ℝ) + (α + β) / 2 + 1)) * Phi1) :
    Phi1 = cp * sw * qp := by
  have hT1 : 0 < hahnT α β D (n + 1) := hahnT_pos α β D (n + 1) (by omega) hn
  have hNp : (0 : ℝ) < (D : ℝ) + (α + β) / 2 + 1 := by positivity
  have hLp : 0 < (α + β : ℝ) / 2 + n := by linarith
  have hne : ((α + β : ℝ) / 2 + n) * (hahnT α β D (n + 1) / ((D : ℝ) + (α + β) / 2 + 1)) ≠ 0 :=
    by positivity
  apply mul_left_cancel₀ hne
  have hPA := hahnP_eq α β D n
  have hqq : (2 * ((α + β : ℝ) / 2 + n) + 1) *
        (((α + β : ℝ) / 2 + n) * (((α + β : ℝ) / 2 + n) + 1) *
            (1 - ((α : ℝ) + 1 + 2 * u) / ((D : ℝ) + (α + β) / 2 + 1)) -
          (α + β : ℝ) / 2 * ((β - α : ℝ) / 2)) =
      (2 * ((α + β : ℝ) / 2 + n) * (((α + β : ℝ) / 2 + n) + 1) *
        (2 * ((α + β : ℝ) / 2 + n) + 1) / ((D : ℝ) + (α + β) / 2 + 1)) *
        (-(u : ℝ) + hahnA α β D n + hahnC α β D n) := by
    unfold hahnA hahnC
    have h1 : (2 * (n : ℝ) + α + β + 1) ≠ 0 := by positivity
    have h2 : (2 * (n : ℝ) + α + β + 2) ≠ 0 := by positivity
    have h3 : (2 * (n : ℝ) + α + β) ≠ 0 := by
      have : (0 : ℝ) ≤ n := by positivity
      linarith [hL.ne', (by linarith : (0 : ℝ) < 2 * n + α + β)]
    have h4 : (2 * (n : ℝ) + α + β + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [hqq] at H
  set Lr : ℝ := (α + β : ℝ) / 2 + n with hLr
  set Nr : ℝ := (D : ℝ) + (α + β) / 2 + 1 with hNr
  set Kr : ℝ := 2 * Lr * (Lr + 1) * (2 * Lr + 1) / Nr with hKr
  have hLN : Lr / Nr * (2 * (Lr + 1) * (2 * Lr + 1)) = Kr := by
    rw [hKr]; field_simp
  linear_combination (-1 : ℝ) * H + (-(sw * qm)) * hqc + (-(Lr / Nr * sw * qp)) * hcp +
    (-(Lr / Nr * sw * qp * cn)) * hPA + (cn * sw * Kr) * hq + (cn * sw * qp * hahnA α β D n) * hLN

/-- Real-number form of the chamber data `M = (α+β)/2`, `σ = (β-α)/2`, `N = D+M+1`. -/
lemma chamber_real {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) :
    (M : ℝ) = ((α : ℝ) + β) / 2 ∧ (σ : ℝ) = ((β : ℝ) - α) / 2 ∧
      (N : ℝ) = (D : ℝ) + ((α : ℝ) + β) / 2 + 1 := by
  have h1 : (M : ℝ) - σ = α := by exact_mod_cast hα
  have h2 : (M : ℝ) + σ = β := by exact_mod_cast hβ
  have h3 : (N : ℝ) - M - 1 = D := by exact_mod_cast hD
  refine ⟨by linarith, by linarith, by linarith⟩

/-- `N R_L √(1-L²/N²) = T_k` for `L = M+k`. -/
lemma RkS {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β) (hD : N - M - 1 = D)
    (Lq : ℚ) (k : ℕ) (hLq : Lq = M + k) (hk : k ≤ D + 1) :
    Rk M σ Lq * Real.sqrt (1 - (Lq : ℝ) ^ 2 / (N : ℝ) ^ 2) = hahnT α β D k / (N : ℝ) := by
  obtain ⟨hM, hs, hN⟩ := chamber_real hα hβ hD
  have hL : (Lq : ℝ) = ((α : ℝ) + β) / 2 + k := by rw [hLq]; push_cast; rw [hM]
  have hNp : (0 : ℝ) < N := by rw [hN]; positivity
  have hkk : (k : ℝ) ≤ D + 1 := by exact_mod_cast hk
  have ha : ((Lq : ℝ) ^ 2 - (M : ℝ) ^ 2) * ((Lq : ℝ) ^ 2 - (σ : ℝ) ^ 2) =
      (k : ℝ) * ((k : ℝ) + α + β) * ((k : ℝ) + α) * ((k : ℝ) + β) := by
    rw [hL, hM, hs]; ring
  have hb : 1 - (Lq : ℝ) ^ 2 / (N : ℝ) ^ 2 =
      ((D : ℝ) + 1 - k) * ((D : ℝ) + k + α + β + 1) / (N : ℝ) ^ 2 := by
    field_simp
    rw [hL, hN]; ring
  have hpoly : 0 ≤ (k : ℝ) * ((k : ℝ) + α + β) * ((k : ℝ) + α) * ((k : ℝ) + β) := by positivity
  have hpoly2 : 0 ≤ ((D : ℝ) + 1 - k) * ((D : ℝ) + k + α + β + 1) := by
    have : 0 ≤ (D : ℝ) + 1 - k := by linarith
    positivity
  unfold Rk
  rw [ha, hb, ← Real.sqrt_mul hpoly, hahnT, ← Real.sqrt_sq hNp.le,
    ← Real.sqrt_div (by positivity), Real.sqrt_sq hNp.le]
  congr 1
  ring

lemma PhiX_eq_Phi3j (L M σ N μ : ℚ) (hN : N ≠ 0) :
    PhiX L M σ N (2 * μ / N) = Phi3j L M σ N μ := by
  unfold PhiX
  congr 1
  field_simp

/-- The rank recurrence in Hahn variables (`eq:3jrank` at `L = M+n`, `x = x_u`). -/
lemma kernel_rec {M σ N μ : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) (n u : ℕ) (hn : n ≤ D) (hu : jPlus N σ + mPlus M μ = u) :
    (2 * ((α + β : ℝ) / 2 + n) + 1) *
        (((α + β : ℝ) / 2 + n) * (((α + β : ℝ) / 2 + n) + 1) *
            (1 - ((α : ℝ) + 1 + 2 * u) / ((D : ℝ) + (α + β) / 2 + 1)) -
          (α + β : ℝ) / 2 * ((β - α : ℝ) / 2)) * Phi3j (M + n) M σ N μ =
      (((α + β : ℝ) / 2 + n) + 1) * (hahnT α β D n / ((D : ℝ) + (α + β) / 2 + 1)) *
          Phi3j (M + n - 1) M σ N μ +
        ((α + β : ℝ) / 2 + n) * (hahnT α β D (n + 1) / ((D : ℝ) + (α + β) / 2 + 1)) *
          Phi3j (M + n + 1) M σ N μ := by
  obtain ⟨hM, hs, hN⟩ := chamber_real hα hβ hD
  have hNq : 0 < N := by
    have : (0 : ℝ) < N := by rw [hN]; positivity
    exact_mod_cast this
  have hT : IsTri (M + n) (jMinus N σ) (jPlus N σ) := by
    refine ⟨⟨α + n, ?_⟩, ⟨β + n, ?_⟩, ⟨D - n, ?_⟩⟩
    · unfold jMinus jPlus; push_cast; linarith
    · unfold jMinus jPlus; push_cast; linarith
    · unfold jMinus jPlus; rw [Nat.cast_sub hn]; push_cast; linarith
  have h1 : IsNat (M + n + M) := ⟨α + β + n, by push_cast; linarith⟩
  have h2 : IsNat (M + n - M) := ⟨n, by push_cast; ring⟩
  have hrec := Phi3j_rank_recurrence (M + n) M σ N (2 * μ / N) hNq hT h1 h2
  have hx : (((2 * μ / N : ℚ)) : ℝ) = 1 - ((α : ℝ) + 1 + 2 * u) / ((D : ℝ) + (α + β) / 2 + 1) := by
    have h := hahn_x_of_u M σ N μ u hNq.ne' hu
    rw [hα] at h
    have h' := congrArg (fun q : ℚ => (q : ℝ)) h
    simp only [Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_one,
      Rat.cast_natCast, Rat.cast_ofNat] at h'
    push_cast
    rw [h', hN]
  rw [PhiX_eq_Phi3j _ _ _ _ _ hNq.ne', PhiX_eq_Phi3j _ _ _ _ _ hNq.ne',
    PhiX_eq_Phi3j _ _ _ _ _ hNq.ne'] at hrec
  have e0 := RkS hα hβ hD (M + n) n rfl (by omega)
  have e1 := RkS hα hβ hD (M + n + 1) (n + 1) (by push_cast; ring) (by omega)
  rw [hx, e0] at hrec
  push_cast at hrec e1
  rw [e1, hM, hs] at hrec
  rw [hN] at hrec
  exact hrec

/-- The constants `c_n` of the Hahn form of `Φ`: `c_{n+1} = c_n P_n / T_{n+1}`. -/
noncomputable def hahnc (α β D : ℕ) (c0 : ℝ) : ℕ → ℝ
  | 0 => c0
  | n + 1 => hahnc α β D c0 n * hahnP α β D n / hahnT α β D (n + 1)

lemma hahnc_succ (α β D : ℕ) (c0 : ℝ) (n : ℕ) (hn : n + 1 ≤ D) :
    hahnc α β D c0 (n + 1) * hahnT α β D (n + 1) = hahnc α β D c0 n * hahnP α β D n := by
  have := (hahnT_pos α β D (n + 1) (by omega) hn).ne'
  simp only [hahnc]
  field_simp

lemma hahnT_zero (α β D : ℕ) : hahnT α β D 0 = 0 := by simp [hahnT]

/-- The induction of `eq:ExactHahnKernel` in the degree: for `M > 0`, if the extremal row is
`c₀ √w Q_0`, then every row is `c_n √w Q_n`. -/
lemma kernel_ind {M σ N μ : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β) (hD : N - M - 1 = D)
    (u : ℕ) (hu : jPlus N σ + mPlus M μ = u) (c0 sw : ℝ)
    (h0 : Phi3j M M σ N μ = c0 * sw * hahnQ α β D 0 u)
    (h1 : α + β = 0 → 1 ≤ D →
      Phi3j (M + 1) M σ N μ = hahnc α β D c0 1 * sw * hahnQ α β D 1 u) :
    ∀ n : ℕ, n ≤ D → Phi3j (M + n) M σ N μ = hahnc α β D c0 n * sw * hahnQ α β D n u := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases n with _ | k
  · simpa [hahnc] using h0
  · have hkD : k + 1 ≤ D := hn
    by_cases hdeg : α + β = 0 ∧ k = 0
    · obtain ⟨hab, rfl⟩ := hdeg
      simpa using h1 hab hkD
    have IHk := ih k (by omega) (by omega)
    have hrec := kernel_rec hα hβ hD k u (by omega) hu
    have hq := hahnQ_rec α β D k u hkD
    have hL : 0 < (α : ℝ) + β + k := by
      have : 0 < α + β + k := by omega
      exact_mod_cast this
    have hqc : (((α + β : ℝ) / 2 + k) + 1) * (hahnT α β D k / ((D : ℝ) + (α + β) / 2 + 1)) *
          hahnc α β D c0 (k - 1) =
        hahnc α β D c0 k * (2 * ((α + β : ℝ) / 2 + k) * (((α + β : ℝ) / 2 + k) + 1) *
          (2 * ((α + β : ℝ) / 2 + k) + 1) / ((D : ℝ) + (α + β) / 2 + 1)) * hahnC α β D k := by
      rcases k with _ | j
      · simp [hahnT_zero, hahnC]
      · have hTk := hahnT_pos α β D (j + 1) (by omega) (by omega)
        have hck := hahnc_succ α β D c0 j (by omega)
        have hrel := hahnT_rel α β D (j + 1) (by omega) (by omega)
        have hNp : (0 : ℝ) < (D : ℝ) + (α + β) / 2 + 1 := by positivity
        apply mul_left_cancel₀ hTk.ne'
        simp only [Nat.add_sub_cancel] at hrel ⊢
        push_cast at hrel ⊢
        field_simp
        apply mul_left_cancel₀ hTk.ne'
        linear_combination (hahnc α β D c0 j) * hrel -
          ((α + β + 2 * ((j : ℝ) + 1)) * (α + β + 2 * ((j : ℝ) + 1) + 1) * hahnC α β D (j + 1)) *
            hck
    have hH : (((α + β : ℝ) / 2 + k) + 1) * (hahnT α β D k / ((D : ℝ) + (α + β) / 2 + 1)) *
          Phi3j (M + k - 1) M σ N μ =
        (((α + β : ℝ) / 2 + k) + 1) * (hahnT α β D k / ((D : ℝ) + (α + β) / 2 + 1)) *
          (hahnc α β D c0 (k - 1) * sw * hahnQ α β D (k - 1) u) := by
      rcases k with _ | j
      · simp [hahnT_zero]
      · have := ih j (by omega) (by omega)
        rw [show M + ((j + 1 : ℕ) : ℚ) - 1 = M + (j : ℚ) by push_cast; ring]
        rw [this]; simp
    rw [IHk, hH] at hrec
    have hcp := hahnc_succ α β D c0 k hkD
    have hstep := step_alg α β D k u hkD hL (hahnc α β D c0 k) (hahnc α β D c0 (k - 1))
      (hahnc α β D c0 (k + 1)) (hahnQ α β D k u) (hahnQ α β D (k - 1) u)
      (hahnQ α β D (k + 1) u) sw (Phi3j (M + k + 1) M σ N μ) hq hqc hcp hrec
    rw [show M + ((k + 1 : ℕ) : ℚ) = M + k + 1 by push_cast; ring]
    exact hstep

/-- `M ≥ |σ|` and `max(|M|,|σ|) = M` in the Hahn chamber. -/
lemma chamber_max {M σ : ℚ} {α β : ℕ} (hα : M - σ = α) (hβ : M + σ = β) :
    max |M| |σ| = M := by
  have h1 : (0 : ℚ) ≤ α := Nat.cast_nonneg α
  have h2 : (0 : ℚ) ≤ β := Nat.cast_nonneg β
  have hM0 : 0 ≤ M := by linarith
  rw [abs_of_nonneg hM0]
  exact max_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- Admissibility data of the Hahn chamber. -/
lemma chamber_specAdm {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) : SpecAdm M σ N := by
  rw [SpecAdm, chamber_max hα hβ]
  refine ⟨⟨⟨α, ?_⟩, ⟨β, ?_⟩, ⟨D, ?_⟩⟩, ⟨α + β, ?_⟩, ⟨0, ?_⟩⟩
  · unfold jMinus jPlus; push_cast; linarith
  · unfold jMinus jPlus; push_cast; linarith
  · unfold jMinus jPlus; push_cast; linarith
  · push_cast; linarith
  · push_cast; ring

lemma lat_u {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) (n' : ℕ) (hn' : n' ≤ D) :
    jPlus N σ + mPlus M ((-N + 1 + |M + σ|) / 2 + n') = ((D - n' : ℕ) : ℚ) := by
  rw [abs_of_nonneg (by rw [hβ]; exact Nat.cast_nonneg β), Nat.cast_sub hn']
  unfold jPlus mPlus
  linarith

/-- Normalization: if `Φ_{M+n} = c √w Q_n` on the whole lattice, then `c² h_n = N/(2L+1)`. -/
lemma kernel_norm {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) (n : ℕ) (hn : n ≤ D) (c : ℝ)
    (H : ∀ (μ : ℚ) (u : ℕ), u ≤ D → jPlus N σ + mPlus M μ = u →
      Phi3j (M + n) M σ N μ = c * Real.sqrt (hahnW α β D u : ℝ) * hahnQ α β D n u) :
    c ^ 2 * hahnNorm α β D n = (N : ℝ) / (2 * ((M : ℝ) + n) + 1) := by
  obtain ⟨hMr, hsr, hNr⟩ := chamber_real hα hβ hD
  have hNp : (0 : ℝ) < N := by rw [hNr]; positivity
  have hNq : 0 < N := by exact_mod_cast hNp
  have hA := chamber_specAdm hα hβ hD
  have hK : ((D + 1 : ℕ) : ℚ) = N - max |M| |σ| := by
    rw [chamber_max hα hβ]; push_cast; linarith
  have hT : IsTri (M + n) (jMinus N σ) (jPlus N σ) := by
    refine ⟨⟨α + n, ?_⟩, ⟨β + n, ?_⟩, ⟨D - n, ?_⟩⟩
    · unfold jMinus jPlus; push_cast; linarith
    · unfold jMinus jPlus; push_cast; linarith
    · unfold jMinus jPlus; rw [Nat.cast_sub hn]; push_cast; linarith
  have h1 : IsNat (M + n + M) := ⟨α + β + n, by push_cast; linarith⟩
  have h2 : IsNat (M + n - M) := ⟨n, by push_cast; ring⟩
  have hdo := Phi_discorth hA hNq hK hT h1 h2 hT h1 h2
  rw [if_pos rfl] at hdo
  have hterm : ∀ n' ∈ Finset.range (D + 1),
      PhiX (M + n) M σ N (xLat M σ N n') * PhiX (M + n) M σ N (xLat M σ N n') =
        c ^ 2 * ((hahnW α β D (D - n') : ℝ) * hahnQ α β D n (D - n') ^ 2) := by
    intro n' hn'
    have hn'D : n' ≤ D := by simp only [Finset.mem_range] at hn'; omega
    have hx : PhiX (M + n) M σ N (xLat M σ N n') =
        Phi3j (M + n) M σ N ((-N + 1 + |M + σ|) / 2 + n') := by
      unfold PhiX; rw [mu_lat M σ N hNq.ne']
    rw [hx, H _ (D - n') (by omega) (lat_u hα hβ hD n' hn'D)]
    have : (Real.sqrt (hahnW α β D (D - n') : ℝ)) ^ 2 = hahnW α β D (D - n') :=
      Real.sq_sqrt (by positivity)
    linear_combination (c ^ 2 * hahnQ α β D n (D - n') ^ 2) * this
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hdo
  have hrefl : ∑ n' ∈ Finset.range (D + 1),
      ((hahnW α β D (D - n') : ℝ) * hahnQ α β D n (D - n') ^ 2) = hahnNorm α β D n := by
    unfold hahnNorm
    exact Finset.sum_range_reflect (fun u => (hahnW α β D u : ℝ) * hahnQ α β D n u ^ 2) (D + 1)
  rw [hrefl] at hdo
  have hL : 0 < 2 * ((M : ℝ) + n) + 1 := by
    have : (0 : ℝ) ≤ M := by rw [hMr]; positivity
    positivity
  push_cast at hdo
  field_simp at hdo ⊢
  linarith

lemma hahnc_mul (α β D : ℕ) (a c0 : ℝ) (n : ℕ) :
    hahnc α β D (a * c0) n = a * hahnc α β D c0 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [hahnc, ih]; ring

lemma hahnc_pos (α β D : ℕ) (r0 : ℝ) (hr : 0 < r0) (n : ℕ) (hn : n ≤ D) :
    0 < hahnc α β D r0 n := by
  induction n with
  | zero => simpa [hahnc] using hr
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 := hahnP_pos α β D n hn
    have h3 := hahnT_pos α β D (n + 1) (by omega) hn
    simp only [hahnc]
    positivity

lemma hahnNorm_nonneg (α β D n : ℕ) : 0 ≤ hahnNorm α β D n := by
  unfold hahnNorm
  apply Finset.sum_nonneg
  intro u _
  positivity

/-- The general-degree kernel, assuming the extra base row for `M = σ = 0`. -/
lemma Phi3j_hahn_aux {M σ N μ : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) (n u : ℕ) (hn : n ≤ D) (hu : jPlus N σ + mPlus M μ = u) (huD : u ≤ D)
    (hbase : ∀ (μ : ℚ) (u : ℕ), u ≤ D → jPlus N σ + mPlus M μ = u → α + β = 0 → 1 ≤ D →
      Phi3j (M + 1) M σ N μ =
        hahnc α β D ((-1 : ℝ) ^ α * (Real.sqrt ((N : ℝ) / (2 * (M : ℝ) + 1)) /
          Real.sqrt (hahnNorm α β D 0))) 1 * Real.sqrt (hahnW α β D u : ℝ) * hahnQ α β D 1 u) :
    Phi3j (M + n) M σ N μ =
      (-1 : ℝ) ^ α * Real.sqrt ((N : ℝ) / (2 * ((M : ℝ) + n) + 1)) *
        Real.sqrt ((hahnW α β D u : ℝ) / hahnNorm α β D n) * hahnQ α β D n u := by
  obtain ⟨hMr, hsr, hNr⟩ := chamber_real hα hβ hD
  set r0 : ℝ := Real.sqrt ((N : ℝ) / (2 * (M : ℝ) + 1)) / Real.sqrt (hahnNorm α β D 0) with hr0
  set c0 : ℝ := (-1 : ℝ) ^ α * r0 with hc0
  have hNp : (0 : ℝ) < N := by rw [hNr]; positivity
  have hM0 : (0 : ℝ) ≤ M := by rw [hMr]; positivity
  have hh0 : 0 < hahnNorm α β D 0 := by
    rw [hahnNorm_zero]; exact_mod_cast Nat.choose_pos (by omega)
  have hr0pos : 0 < r0 := by
    rw [hr0]; positivity
  have hbaseall : ∀ (μ : ℚ) (u : ℕ), u ≤ D → jPlus N σ + mPlus M μ = u →
      Phi3j M M σ N μ = c0 * Real.sqrt (hahnW α β D u : ℝ) * hahnQ α β D 0 u := by
    intro μ u huD hu
    have := Phi3j_hahn_zero M σ N μ α β D u hα hβ hD hu huD
    rw [this, Real.sqrt_div (Nat.cast_nonneg _) (hahnNorm α β D 0), hahnQ_zero, hc0, hr0]
    ring
  have hind : ∀ (μ : ℚ) (u : ℕ), u ≤ D → jPlus N σ + mPlus M μ = u →
      ∀ n : ℕ, n ≤ D → Phi3j (M + n) M σ N μ =
        hahnc α β D c0 n * Real.sqrt (hahnW α β D u : ℝ) * hahnQ α β D n u := by
    intro μ u huD hu
    exact kernel_ind hα hβ hD u hu c0 _ (hbaseall μ u huD hu)
      (fun hab hD1 => hbase μ u huD hu hab hD1)
  have hnorm := kernel_norm hα hβ hD n hn (hahnc α β D c0 n)
    (fun μ u huD hu => hind μ u huD hu n hn)
  have hcn : hahnc α β D c0 n = (-1 : ℝ) ^ α * hahnc α β D r0 n := by
    rw [hc0, hahnc_mul]
  have hrn := hahnc_pos α β D r0 hr0pos n hn
  set rn := hahnc α β D r0 n with hrn_def
  have hsq : (-1 : ℝ) ^ α * (-1 : ℝ) ^ α = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have hL : 0 < 2 * ((M : ℝ) + n) + 1 := by positivity
  have hrn2 : rn ^ 2 * hahnNorm α β D n = (N : ℝ) / (2 * ((M : ℝ) + n) + 1) := by
    rw [hcn] at hnorm
    have : ((-1 : ℝ) ^ α * rn) ^ 2 = rn ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm α 2, pow_mul]; simp
    rw [this] at hnorm
    exact hnorm
  have hhn : 0 ≤ hahnNorm α β D n := hahnNorm_nonneg α β D n
  have hkey : Real.sqrt ((N : ℝ) / (2 * ((M : ℝ) + n) + 1)) = rn * Real.sqrt (hahnNorm α β D n) := by
    rw [← hrn2, show rn ^ 2 * hahnNorm α β D n = (rn * Real.sqrt (hahnNorm α β D n)) ^ 2 by
      rw [mul_pow, Real.sq_sqrt hhn]]
    exact Real.sqrt_sq (by positivity)
  have hhnpos : 0 < hahnNorm α β D n := by
    rcases hhn.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hrn2
      have : (N : ℝ) / (2 * ((M : ℝ) + n) + 1) = 0 := by rw [← hrn2]; ring
      have : 0 < (N : ℝ) / (2 * ((M : ℝ) + n) + 1) := by positivity
      linarith
  rw [hind μ u huD hu n hn, hcn, Real.sqrt_div (Nat.cast_nonneg _) (hahnNorm α β D n), hkey]
  have : Real.sqrt (hahnNorm α β D n) ≠ 0 := (Real.sqrt_pos.mpr hhnpos).ne'
  field_simp

lemma hahnQ_one (α β D u : ℕ) :
    hahnQ α β D 1 u = 1 + (-1) * (1 + α + β + 1) * (-(u : ℝ)) / (((α : ℝ) + 1) * (-(D : ℝ)) * 1) := by
  simp [hahnQ, Finset.sum_range_succ, ascPochhammer_one]

/-- The extra base row (`M = σ = 0`, `L = 1`) in the Hahn form. -/
lemma hbase_zero {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) (μ : ℚ) (u : ℕ) (huD : u ≤ D)
    (hu : jPlus N σ + mPlus M μ = u) (hab : α + β = 0) (hD1 : 1 ≤ D) :
    Phi3j (M + 1) M σ N μ =
      hahnc α β D ((-1 : ℝ) ^ α * (Real.sqrt ((N : ℝ) / (2 * (M : ℝ) + 1)) /
        Real.sqrt (hahnNorm α β D 0))) 1 * Real.sqrt (hahnW α β D u : ℝ) * hahnQ α β D 1 u := by
  have ha0 : α = 0 := by omega
  have hb0 : β = 0 := by omega
  subst ha0 hb0
  have hM : M = 0 := by push_cast at hα hβ; linarith
  have hσ : σ = 0 := by push_cast at hα hβ; linarith
  subst hM hσ
  have hD' : N - 1 = D := by linarith
  have hN : (N : ℝ) = (D : ℝ) + 1 := by
    have : N = (D : ℚ) + 1 := by linarith
    rw [this]; push_cast; ring
  rw [zero_add, Phi3j_L1_M0 N μ D u hD' hu huD hD1]
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD1
  have hn0 : hahnNorm 0 0 D 0 = (D : ℝ) + 1 := by
    rw [hahnNorm_zero, show 0 + 0 + 1 + D = D + 1 by ring]
    simp [Nat.choose_one_right]
  have hP : hahnP 0 0 D 0 = D := by simp [hahnP]
  have hT : hahnT 0 0 D 1 = Real.sqrt ((D : ℝ) * (D + 2)) := by
    unfold hahnT; congr 1; push_cast; ring
  have hc0 : ((-1 : ℝ) ^ 0 * (Real.sqrt ((N : ℝ) / (2 * ((0 : ℚ) : ℝ) + 1)) /
      Real.sqrt (hahnNorm 0 0 D 0))) = 1 := by
    rw [hn0, hN]; push_cast
    have : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    simp [Real.sqrt_pos.mpr this |>.ne']
  have hw : (hahnW 0 0 D u : ℝ) = 1 := by simp [hahnW]
  rw [hc0, hw, hahnQ_one]
  simp only [hahnc, hP, hT]
  have hq : 0 < Real.sqrt ((D : ℝ) * (D + 2)) := Real.sqrt_pos.mpr (by positivity)
  simp
  field_simp
  ring

/-- **`eq:ExactHahnKernel`** (explicit Hahn realization of the finite kernel), every degree.
In the chamber `M ≥ |σ|`, with `α = M-σ`, `β = M+σ`, `D = N-M-1` natural numbers, `n = L-M ≤ D`
and the lattice index `u = j_++m_+ ∈ {0,…,D}` (`x_u = 1-(α+1+2u)/N`, `hahn_x_of_u`):
`Φ_{M+n}^{M,σ}(x_u) = (-1)^α √(N/(2(M+n)+1)) √(w_H(u)/h_{H,n}) Q_n(u;α,β,D)`,
with `Q_n = hahnQ`, `w_H = hahnW`, `h_{H,n} = hahnNorm`.  Exactly the paper's boxed statement. -/
theorem Phi3j_hahn {M σ N μ : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) (n u : ℕ) (hn : n ≤ D) (hu : jPlus N σ + mPlus M μ = u) (huD : u ≤ D) :
    Phi3j (M + n) M σ N μ =
      (-1 : ℝ) ^ α * Real.sqrt ((N : ℝ) / (2 * ((M : ℝ) + n) + 1)) *
        Real.sqrt ((hahnW α β D u : ℝ) / hahnNorm α β D n) * hahnQ α β D n u :=
  Phi3j_hahn_aux hα hβ hD n u hn hu huD (fun μ u huD hu hab hD1 =>
    hbase_zero hα hβ hD μ u huD hu hab hD1)

/-- info: 'FormalResearch.Racah.Phi3j_hahn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_hahn

end FormalResearch.Racah
