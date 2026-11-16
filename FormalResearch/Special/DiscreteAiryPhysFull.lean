module

public import FormalResearch.Special.DiscreteAiryOscMain
public import FormalResearch.Special.DiscreteAiryOscAssemble
public import FormalResearch.Special.DiscreteJacobiCalculus

/-!
# The unified discrete-to-Airy conclusion `DaiFull` (abstract lattice form)

`DaoConclusion` (`DiscreteAiryOscMain`) and `DalConclusion` (`DiscreteAiryLimit`) are two statements about the same object: the
exact recessive solution `f` of a three-term recurrence on the rows `J+1..N`, normalised by `f = g Ai(X)` at the **two sites
`N, N+1`**.  This module makes the identification explicit and produces one statement, `DaiFull`, which

* characterises `f` as **the unique** solution of the rows with `f_N = φ_N`, `f_{N+1} = φ_{N+1}` (`φ = g Ai(X)`), and `F₂` as
  the unique solution of the rows with `F₂ = ψ`, `ψ = g Bi(X)`, at two adjacent sites `m, m+1` (uniqueness of the three-term
  recurrence solution from two consecutive values and `a_k ≠ 0`: `eq_of_final_values`, `eq_zero_of_two_values`);
* gives `|f - φ| ≤ C δ³ airyWt(X)` and `|F₂ - ψ| ≤ C δ³ airyBiWt(X)` on **all of `[J, N+1]`** (the `DaoConclusion` statements
  stop at `N`; at `N+1` the recessive one is exact, and the dominant one is obtained by one more row, `dap_one_step`);
* gives the two-sided decomposition `Y = κ f + μ F₂` of every exact solution with `|Y_N|, |Y_{N+1}| ≤ Y_max` on `[J, N+1]`,
  `|μ| ≤ Cmu Y_max e^{-ξ(X_N)}/δ`, and `ξ₀/δ³ ≤ ξ(X_N)` (so `μ` is exponentially small in `1/δ³`).

Consequently (`DaiFull.pointwise`) `Y_k = κ g Ai(X_k) + μ g Bi(X_k)` up to `C δ³ (|κ| airyWt + |μ| airyBiWt)` on all of `[J, N+1]`.

* `dap_one_step`: one row transports an error bound at `N-1, N` and a defect bound at the row `N` to `N+1`;
* `dai_extend`: `DaoConclusion` + the data of a `DaoPair` + `a_N ≤ A_a`, `|c_N| ≤ C_c`  ⟹  `DaiFull` with the explicit constant
  `C' = C + C_n (C_c C + A_a C C_n + K)/c_a`, `C_n = (6/5) e^{c₂ √(1+M)}`;
* `dap_recessive_eq`: two exact solutions with the same two final values agree on the common rows (this is the identification of
  the recessive `f` of `discrete_airy_limit`/`discrete_airy_window` with that of `DaoConclusion`, *when both are normalised at the
  same `N`*).

**Claim class: proved** (abstract lattice form; the smooth-data corollary is `discrete_airy_full`, `DiscreteAiryPhysTurn`).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **The unified conclusion** (see the module docstring). -/
def DaiFull (a c X g : ℤ → ℝ) (J m N : ℤ) (δ C Cmu ξ0 : ℝ) : Prop :=
  ξ0 / δ ^ 3 ≤ airyXi (X N) ∧ (∀ k ∈ Icc (J + 1) (N + 1), 0 < a k) ∧
  ∃ f F₂ : ℤ → ℝ,
    ((∀ k ∈ Icc (J + 1) N, jac a c f k = 0) ∧ f N = daoPhi g X N ∧ f (N + 1) = daoPhi g X (N + 1) ∧
      (∀ f' : ℤ → ℝ, (∀ k ∈ Icc (J + 1) N, jac a c f' k = 0) → f' N = daoPhi g X N →
        f' (N + 1) = daoPhi g X (N + 1) → ∀ k ∈ Icc J (N + 1), f' k = f k) ∧
      (∀ k ∈ Icc J (N + 1), |f k - daoPhi g X k| ≤ C * δ ^ 3 * airyWt (X k))) ∧
    ((∀ k ∈ Icc (J + 1) N, jac a c F₂ k = 0) ∧ F₂ m = daoPsi g X m ∧ F₂ (m + 1) = daoPsi g X (m + 1) ∧
      (∀ F' : ℤ → ℝ, (∀ k ∈ Icc (J + 1) N, jac a c F' k = 0) → F' m = daoPsi g X m →
        F' (m + 1) = daoPsi g X (m + 1) → ∀ k ∈ Icc J (N + 1), F' k = F₂ k) ∧
      (∀ k ∈ Icc J (N + 1), |F₂ k - daoPsi g X k| ≤ C * δ ^ 3 * airyBiWt (X k))) ∧
    δ / C ≤ cas a f F₂ N ∧ (∀ k ∈ Icc J N, cas a f F₂ k = cas a f F₂ N) ∧
    ∀ (Y : ℤ → ℝ) (Ymax : ℝ), (∀ k ∈ Icc (J + 1) N, jac a c Y k = 0) → |Y N| ≤ Ymax → |Y (N + 1)| ≤ Ymax →
      ∃ κ μ : ℝ, (∀ k ∈ Icc J (N + 1), Y k = κ * f k + μ * F₂ k) ∧
        |μ| ≤ Cmu * Ymax * Real.exp (-airyXi (X N)) / δ

/-- **Pointwise form of `DaiFull`.**  Every exact solution `Y` with `|Y_N|, |Y_{N+1}| ≤ Y_max` is
`κ g Ai(X) + μ g Bi(X)` up to `C δ³ (|κ| airyWt + |μ| airyBiWt)` on all of `[J, N+1]`. -/
theorem DaiFull.pointwise {a c X g : ℤ → ℝ} {J m N : ℤ} {δ C Cmu ξ0 : ℝ} (h : DaiFull a c X g J m N δ C Cmu ξ0)
    (Y : ℤ → ℝ) (Ymax : ℝ) (hY : ∀ k ∈ Icc (J + 1) N, jac a c Y k = 0) (hYN : |Y N| ≤ Ymax)
    (hYN1 : |Y (N + 1)| ≤ Ymax) :
    ∃ κ μ : ℝ, |μ| ≤ Cmu * Ymax * Real.exp (-airyXi (X N)) / δ ∧
      ∀ k ∈ Icc J (N + 1), |Y k - (κ * daoPhi g X k + μ * daoPsi g X k)| ≤
        C * δ ^ 3 * (|κ| * airyWt (X k) + |μ| * airyBiWt (X k)) := by
  obtain ⟨-, -, f, F₂, ⟨-, -, -, -, hf⟩, ⟨-, -, -, -, hF⟩, -, -, hYd⟩ := h
  obtain ⟨κ, μ, hYeq, hμ⟩ := hYd Y Ymax hY hYN hYN1
  refine ⟨κ, μ, hμ, fun k hk => ?_⟩
  have e : Y k - (κ * daoPhi g X k + μ * daoPsi g X k) =
      κ * (f k - daoPhi g X k) + μ * (F₂ k - daoPsi g X k) := by rw [hYeq k hk]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h1 := mul_le_mul_of_nonneg_left (hf k hk) (abs_nonneg κ)
  have h2 := mul_le_mul_of_nonneg_left (hF k hk) (abs_nonneg μ)
  nlinarith

/-- **One more row.**  If `y` solves the row `N`, `p` has row defect `≤ D` there, and `y - p` is bounded at `N-1, N`, then
`y - p` is bounded at `N+1` (`a_{N+1} ≥ c_a > 0`, `a_N ≤ A_a`, `|c_N| ≤ C_c`). -/
lemma dap_one_step {a c y p : ℤ → ℝ} {N : ℤ} {E0 E1 D Cc Aa ca : ℝ}
    (hy : jac a c y N = 0) (hp : |jac a c p N| ≤ D)
    (h1 : |y N - p N| ≤ E1) (h0 : |y (N - 1) - p (N - 1)| ≤ E0)
    (hc : |c N| ≤ Cc) (haN : 0 ≤ a N) (haN' : a N ≤ Aa) (hca : 0 < ca) (ha1 : ca ≤ a (N + 1)) :
    |y (N + 1) - p (N + 1)| ≤ (Cc * E1 + Aa * E0 + D) / ca := by
  have e : a (N + 1) * (y (N + 1) - p (N + 1)) =
      c N * (y N - p N) - a N * (y (N - 1) - p (N - 1)) - jac a c p N := by
    simp only [jac] at hy ⊢
    linear_combination hy
  have ha0 : 0 < a (N + 1) := hca.trans_le ha1
  have t1 : |c N * (y N - p N)| ≤ Cc * E1 := by
    rw [abs_mul]; exact mul_le_mul hc h1 (abs_nonneg _) ((abs_nonneg _).trans hc)
  have t2 : |a N * (y (N - 1) - p (N - 1))| ≤ Aa * E0 := by
    rw [abs_mul, abs_of_nonneg haN]; exact mul_le_mul haN' h0 (abs_nonneg _) (haN.trans haN')
  have h2 : a (N + 1) * |y (N + 1) - p (N + 1)| ≤ Cc * E1 + Aa * E0 + D := by
    have : |a (N + 1) * (y (N + 1) - p (N + 1))| = a (N + 1) * |y (N + 1) - p (N + 1)| := by
      rw [abs_mul, abs_of_pos ha0]
    rw [← this, e]
    calc |c N * (y N - p N) - a N * (y (N - 1) - p (N - 1)) - jac a c p N|
        ≤ |c N * (y N - p N) - a N * (y (N - 1) - p (N - 1))| + |jac a c p N| := abs_sub _ _
      _ ≤ (|c N * (y N - p N)| + |a N * (y (N - 1) - p (N - 1))|) + |jac a c p N| := by
          gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  rw [le_div_iff₀ hca]
  have := mul_le_mul_of_nonneg_right ha1 (abs_nonneg (y (N + 1) - p (N + 1)))
  linarith

/-- **Identification of the recessive solutions.**  Two exact solutions of the rows with the same values at the two final sites
`N, N+1` agree on the common rows (`a_k ≠ 0`): the exact recessive `f` of `discrete_airy_limit` (rows `J'+1..N`,
`f = ψ` at `N, N+1`) is the restriction to `[J', N+1]` of the exact `f` of `DaoConclusion` (rows `J+1..N`, `J ≤ J'`) when both are
normalised by the same two values at the same `N`. -/
theorem dap_recessive_eq {a c f f' : ℤ → ℝ} {J J' N : ℤ} (hJJ : J ≤ J') (hJ'N : J' + 1 ≤ N)
    (ha : ∀ k ∈ Icc (J + 1) (N + 1), a k ≠ 0)
    (hf : ∀ k ∈ Icc (J + 1) N, jac a c f k = 0) (hf' : ∀ k ∈ Icc (J' + 1) N, jac a c f' k = 0)
    (hN : f N = f' N) (hN1 : f (N + 1) = f' (N + 1)) : ∀ k ∈ Icc J' (N + 1), f k = f' k := by
  have h := eq_of_final_values a c f f' (fun _ => 0) (J' + 1) N hJ'N
    (fun k hk => by rw [hf k (by rw [mem_Icc] at hk ⊢; omega)])
    (fun k hk => hf' k hk)
    (fun k hk => ha k (by rw [mem_Icc] at hk ⊢; omega)) hN hN1
  intro k hk
  exact h k (by rw [mem_Icc] at hk ⊢; omega)

/-- **Extension of `DaoConclusion` to the site `N+1` and uniqueness.**  Given the lattice data `DaoPair`, `J < N`,
`a_N ≤ A_a`, `|c_N| ≤ C_c`, and `ξ₀/δ³ ≤ ξ(X_N)`, a `DaoConclusion` with constant `C` yields `DaiFull` with the constant
`C' = C + C_n (C_c C + A_a C C_n + K)/c_a`, `C_n = (6/5) e^{c₂ √(1+M)}`. -/
theorem dai_extend {X g a c : ℤ → ℝ} {J m N : ℤ} {δ c1 c2 gmin gmax ca K M Aa Cc C Cmu ξ0 : ℝ}
    (hP : DaoPair X g a c J N δ c1 c2 gmin gmax ca K M) (hJN : J < N) (hJm : J ≤ m) (hmN : m ≤ N)
    (hc2 : 0 ≤ c2) (hM : 0 ≤ M) (haN : a N ≤ Aa) (hcN : |c N| ≤ Cc) (hC : 0 < C) (hxi : ξ0 / δ ^ 3 ≤ airyXi (X N))
    (h : DaoConclusion a c X g J m N δ C Cmu) :
    DaiFull a c X g J m N δ
      (C + 6 / 5 * Real.exp (c2 * √(1 + M)) * (Cc * C + Aa * C * (6 / 5 * Real.exp (c2 * √(1 + M))) + K) / ca)
      Cmu ξ0 := by
  obtain ⟨f, F₂, hf, hfN, hfN1, hfd, hF, hFm, hFm1, hFd, hcas, hcc, hY⟩ := h
  have hδ := hP.δ_pos
  have hδ1 := hP.δ_le
  have hca := hP.ca_pos
  have hK := hP.K_nonneg
  set Cn : ℝ := 6 / 5 * Real.exp (c2 * √(1 + M)) with hCn
  have hCn0 : 0 < Cn := by positivity
  have hCc : 0 ≤ Cc := (abs_nonneg _).trans hcN
  have haNpos : ca ≤ a N := hP.alow N (by rw [mem_Icc]; omega)
  have hAa : 0 ≤ Aa := hca.le.trans (haNpos.trans haN)
  have hδ3 : 0 ≤ δ ^ 3 := by positivity
  have hδ63 : δ ^ 6 ≤ δ ^ 3 := by
    have : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
    nlinarith
  set C' : ℝ := C + Cn * (Cc * C + Aa * C * Cn + K) / ca with hC'
  have hC'0 : 0 ≤ Cn * (Cc * C + Aa * C * Cn + K) / ca := by positivity
  have hCC' : C ≤ C' := by rw [hC']; linarith
  have hC'p : 0 < C' := hC.trans_le hCC'
  have halow : ∀ k ∈ Icc (J + 1) (N + 1), 0 < a k := fun k hk => hca.trans_le (hP.alow k hk)
  have hane : ∀ k ∈ Icc (J + 1) (N + 1), a k ≠ 0 := fun k hk => (halow k hk).ne'
  -- the step at N+1 for `F₂`
  have hNJ : N ∈ Icc (J + 1) N := by rw [mem_Icc]; omega
  have hNm1 : N - 1 ∈ Icc J N := by rw [mem_Icc]; omega
  have hNJ' : N ∈ Icc J N := by rw [mem_Icc]; omega
  have hgapN := hP.gap N hNJ'
  have hgapN1 := hP.gap (N - 1) hNm1
  rw [show N - 1 + 1 = N by ring] at hgapN1
  have hd1 : |X N - X (N + 1)| ≤ c2 * δ := by
    rw [abs_le]; constructor <;> nlinarith [hgapN.1, hgapN.2, hP.c1_pos, hδ]
  have hd2 : |X (N - 1) - X N| ≤ c2 * δ := by
    rw [abs_le]; constructor <;> nlinarith [hgapN1.1, hgapN1.2, hP.c1_pos, hδ]
  have hw1 : airyBiWt (X N) ≤ Cn * airyBiWt (X (N + 1)) :=
    dao_airyBiWt_nbr hδ hδ1 hc2 hP.c2δ (hP.Xabs (N + 1) (by rw [mem_Icc]; omega)) hM hd1
  have hw2 : airyBiWt (X (N - 1)) ≤ Cn * airyBiWt (X N) :=
    dao_airyBiWt_nbr hδ hδ1 hc2 hP.c2δ (hP.Xabs N (by rw [mem_Icc]; omega)) hM hd2
  have hstep := dap_one_step (a := a) (c := c) (y := F₂) (p := daoPsi g X) (N := N)
    (E0 := C * δ ^ 3 * airyBiWt (X (N - 1))) (E1 := C * δ ^ 3 * airyBiWt (X N))
    (D := K * δ ^ 6 * airyBiWt (X N)) (Cc := Cc) (Aa := Aa) (ca := ca)
    (hF N hNJ) (hP.defB N hNJ) (hFd N hNJ') (hFd (N - 1) hNm1) hcN (hca.le.trans haNpos) haN hca
    (hP.alow (N + 1) (by rw [mem_Icc]; omega))
  have hwb0 := airyBiWt_pos (X (N + 1))
  have hwbN := airyBiWt_pos (X N)
  have hFN1 : |F₂ (N + 1) - daoPsi g X (N + 1)| ≤ C' * δ ^ 3 * airyBiWt (X (N + 1)) := by
    refine hstep.trans ?_
    rw [div_le_iff₀ hca]
    have e1 : C * δ ^ 3 * airyBiWt (X (N - 1)) ≤ C * δ ^ 3 * (Cn * (Cn * airyBiWt (X (N + 1)))) :=
      mul_le_mul_of_nonneg_left (hw2.trans (mul_le_mul_of_nonneg_left hw1 hCn0.le)) (by positivity)
    have e2 : K * δ ^ 6 * airyBiWt (X N) ≤ K * δ ^ 3 * (Cn * airyBiWt (X (N + 1))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hδ63 hK) hw1 hwbN.le (by positivity)
    have e3 : C * δ ^ 3 * airyBiWt (X N) ≤ C * δ ^ 3 * (Cn * airyBiWt (X (N + 1))) :=
      mul_le_mul_of_nonneg_left hw1 (by positivity)
    have e4 : Cc * (C * δ ^ 3 * airyBiWt (X N)) + Aa * (C * δ ^ 3 * airyBiWt (X (N - 1))) +
        K * δ ^ 6 * airyBiWt (X N) ≤
        Cc * (C * δ ^ 3 * (Cn * airyBiWt (X (N + 1)))) +
          Aa * (C * δ ^ 3 * (Cn * (Cn * airyBiWt (X (N + 1))))) + K * δ ^ 3 * (Cn * airyBiWt (X (N + 1))) := by
      have := mul_le_mul_of_nonneg_left e3 hCc
      have := mul_le_mul_of_nonneg_left e1 hAa
      linarith
    refine e4.trans ?_
    rw [hC']
    have e5 : (C + Cn * (Cc * C + Aa * C * Cn + K) / ca) * δ ^ 3 * airyBiWt (X (N + 1)) * ca =
        C * δ ^ 3 * airyBiWt (X (N + 1)) * ca + Cn * (Cc * C + Aa * C * Cn + K) * δ ^ 3 * airyBiWt (X (N + 1)) := by
      field_simp
    rw [e5]
    have h0 : 0 ≤ C * δ ^ 3 * airyBiWt (X (N + 1)) * ca := by positivity
    have eA : Cc * (C * δ ^ 3 * (Cn * airyBiWt (X (N + 1)))) +
        Aa * (C * δ ^ 3 * (Cn * (Cn * airyBiWt (X (N + 1))))) + K * δ ^ 3 * (Cn * airyBiWt (X (N + 1))) =
        Cn * (Cc * C + Aa * C * Cn + K) * δ ^ 3 * airyBiWt (X (N + 1)) := by ring
    rw [eA]
    linarith
  -- assemble
  refine ⟨hxi, halow, f, F₂, ⟨hf, hfN, hfN1, ?_, ?_⟩, ⟨hF, hFm, hFm1, ?_, ?_⟩, ?_, hcc, ?_⟩
  · intro f' hf' hN hN1 k hk
    have := eq_of_final_values a c f' f (fun _ => 0) (J + 1) N (by omega)
      (fun k hk => hf' k hk) (fun k hk => hf k hk) (fun k hk => hane k hk) (by rw [hN, hfN]) (by rw [hN1, hfN1])
    exact this k (by rw [mem_Icc] at hk ⊢; omega)
  · intro k hk
    rw [mem_Icc] at hk
    rcases eq_or_lt_of_le hk.2 with h1 | h1
    · rw [h1, hfN1, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hC'p.le hδ3) (airyWt_pos _).le
    · exact (hfd k (by rw [mem_Icc]; omega)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC' hδ3) (airyWt_pos _).le)
  · intro F' hF' h0 h1 k hk
    have hsub : ∀ k ∈ Icc (J + 1) N, jac a c (fun i => F' i - F₂ i) k = 0 := by
      intro k hk
      have := hF' k hk; have := hF k hk
      simp only [jac] at *; linarith
    have := eq_zero_of_two_values a c (fun i => F' i - F₂ i) (J + 1) N m hsub hane
      (by rw [mem_Icc]; omega) (by simp [h0, hFm]) (by simp [h1, hFm1])
    have h2 := this k (by rw [mem_Icc] at hk ⊢; omega)
    simpa [sub_eq_zero] using h2
  · intro k hk
    rw [mem_Icc] at hk
    rcases eq_or_lt_of_le hk.2 with h1 | h1
    · rw [h1]; exact hFN1
    · exact (hFd k (by rw [mem_Icc]; omega)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC' hδ3) (airyBiWt_pos _).le)
  · exact (div_le_div_of_nonneg_left hδ.le hC hCC').trans hcas
  · intro Y Ymax hYex hYN hYN1
    exact hY Y Ymax hYex hYN hYN1

/-- info: 'FormalResearch.Special.dai_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dai_extend

/-- info: 'FormalResearch.Special.dap_recessive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dap_recessive_eq

/-- info: 'FormalResearch.Special.DaiFull.pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.DaiFull.pointwise

end FormalResearch.Special
