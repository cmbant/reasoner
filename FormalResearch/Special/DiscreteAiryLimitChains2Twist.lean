module

public import FormalResearch.Special.DiscreteAiryLimitChainsHahnAiry
public import FormalResearch.Special.DiscreteAiryLimitChains2Nodes
public import FormalResearch.Special.DiscreteAiryLimitChainsRacahAiry

/-!
# The `(-1)^k` twist: the `τ = -1` branch of the actual `3j` / `6j` chains (Weyl P3, `eq:racahTurnType`, `prop:hahn-class`)

The closed-form recurrence of `discrete_airy_hahn_racah` carries a turn type `τ = ±1`, `c_k = τ(x - B_k)`.  The actual
natural-gauge chains `Ŷ_k` solve the `τ = +1` recurrence `jac (hrAk …) (hrCk … 1 …) Ŷ = 0`
(`hahn_class_chain`, `racah_class_chain`).  The `τ = -1` recurrence is obtained by the sign twist `Ŷ_k ↦ (-1)^k Ŷ_k`.

## Results (proved)

* `jac_twist`: `jac a (-c) ((-1)^· y) k = -(-1)^k jac a c y k` (the off-diagonal `a_k` flips sign under `Ŷ_k ↦ (-1)^k Ŷ_k`,
  equivalently the diagonal `c_k` flips sign).
* `hahn_class_chain_neg`, `racah_class_chain_neg`: the twisted actual chains solve every row `k ≥ 1` of the `τ = -1`
  recurrence `jac (hrAk …) (hrCk … (-1) …) ((-1)^· Ŷ) = 0` with the same closed forms.
* `airy_chain_compose`: the abstract composition (any `τ² = 1`): `discrete_airy_hahn_racah` for a sequence `Y` that solves
  every row `k ≥ 1` of the closed-form recurrence at a scale `h ≤ δ₀³` and is bounded by `Y_max`; the conclusion is `AiryOutAt`
  (the window positions, `κ, μ`, and the two-sided approximation by `κ ψ_k`).
* `hahn_chain_airy_neg`: the Airy limit for the actual `3j` chain at lattice nodes `x_n = x` with `x ∈ (-1, 0)`
  (`τ = sgn x = -1`; the twisted chain `(-1)^k Ŷ_k`; the turn `Φ_{-1}(q_*²) = 0` is derived: `-x - |x| = 0`).  This is
  the negative-`x` half of `thm:hahnAiryConnection` ("compact subset of `(0,1)` or of `(-1,0)`").
* `hahn_chain_airy_neg_infinite`: the same along an infinite sequence of `N` (`hahn_node_exists` with `p < 0`).

Claim class: **proved**.

## Not formalised

`κ` (unidentified), `κ ≠ 0`; the non-recessive `Ai`/`Bi` pair (`hahn_chain_airy_full_neg`, `DiscreteAiryPhysChains`); uniformity over compact families of `x`; half-integer data (the shifted-lattice versions are in
`DiscreteAiryLimitChains2Half*`; there the Hahn Airy limit is for `x ∈ (0,1)` only, the `x < 0` twist is not done).
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner
  FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **Sign-flip lemma.**  Under `y ↦ (-1)^k y_k` the row `a_{k+1}y_{k+1} + a_k y_{k-1} - c_k y_k` is multiplied by `-(-1)^k`
and `c` is replaced by `-c`. -/
theorem jac_twist (a c y : ℤ → ℝ) (k : ℤ) :
    jac a (fun j => -c j) (fun j => (-1 : ℝ) ^ j * y j) k = -((-1 : ℝ) ^ k) * jac a c y k := by
  unfold jac
  have h1 : (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) := by rw [zpow_add_one₀ (by norm_num)]; ring
  have h2 : (-1 : ℝ) ^ (k - 1) = -((-1 : ℝ) ^ k) := by
    rw [zpow_sub_one₀ (by norm_num)]; ring
  simp only [h1, h2]
  ring

/-- The twist of a solution of the `τ = +1` rows solves the `τ = -1` rows. -/
theorem jac_twist_zero {a c y : ℤ → ℝ} {k : ℤ} (h : jac a c y k = 0) :
    jac a (fun j => -c j) (fun j => (-1 : ℝ) ^ j * y j) k = 0 := by
  rw [jac_twist, h]; ring

lemma hrCk_neg (P Q x a b h : ℝ) (k : ℤ) : hrCk P Q (-1) x a b h k = -hrCk P Q 1 x a b h k := by
  unfold hrCk; ring

/-- **`τ = -1` branch of `prop:hahn-class`.**  The twisted natural-gauge `3j` chain `(-1)^k Ŷ_k` solves every row `k ≥ 1`
of the closed-form recurrence with `τ = -1` (`c_k = -(x - Mσ/(k(k+1)))`). -/
theorem hahn_class_chain_neg (M σ N : ℤ) (x : ℚ) (hN : 0 < N) (k : ℤ) (hk : 1 ≤ k) :
    jac (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (hrCk 1 0 (-1) (x : ℝ) (M : ℝ) (σ : ℝ) (1 / (N : ℝ)))
      (fun j => (-1 : ℝ) ^ j * hahn3jY M σ N x j) k = 0 := by
  have h := jac_twist_zero (hahn_class_chain M σ N x hN k hk)
  convert h using 2
  ext j
  exact hrCk_neg _ _ _ _ _ _ _

/-- **`τ = -1` branch of `prop:racah-class`** (same hypotheses as `racah_class_chain`). -/
theorem racah_class_chain_neg (a b c m n : ℤ) (h : ℝ) (hh : 0 < h) (hA : 0 < wA (a : ℚ) (n : ℚ))
    (hB : 0 < wB (b : ℚ) (m : ℚ)) (k : ℤ) (hk : 1 ≤ k) :
    jac (hrAk (1 / (4 * (wA (a : ℚ) (n : ℚ) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) (m : ℚ) * h) ^ 2)) (m : ℝ) (n : ℝ) h)
      (hrCk (1 / (4 * (wA (a : ℚ) (n : ℚ) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) (m : ℚ) * h) ^ 2)) (-1)
        (cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ))) (m : ℝ) (n : ℝ) h)
      (fun j => (-1 : ℝ) ^ j * racah6jY a b c m n j) k = 0 := by
  have hh' := jac_twist_zero (racah_class_chain a b c m n h hh hA hB k hk)
  convert hh' using 2
  ext j
  exact hrCk_neg _ _ _ _ _ _ _

/-- The conclusion of `discrete_airy_hahn_racah` for a sequence `Y` (window positions, and `κ, μ` with the two-sided
approximation by `κ ψ_k`), at scale `h = δ³`. -/
def AiryOutAt (P Q τ x qs : ℝ) (Y : ℤ → ℝ) (Ymax A0 r δ0 C Cosc Ctop W Cmu ξ0 D h : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ^ 3 = h ∧ ∃ J m Nw : ℤ, 1 ≤ J ∧ J ≤ m ∧ m ≤ Nw ∧
    (∀ k ∈ Finset.Icc J (Nw + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - qs| ≤ r) ∧
    qs - D * δ ^ 2 ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧ ((J : ℝ) + 1 / 2) * δ ^ 3 ≤ qs ∧
    qs ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧ ((m : ℝ) + 1 / 2) * δ ^ 3 < qs + δ ^ 3 ∧
    turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ J ≤ -A0 ∧
    ξ0 / δ ^ 3 ≤ airyXi (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ Nw) ∧
    ∃ κ μ : ℝ, |μ| ≤ Cmu * Ymax * Real.exp (-airyXi (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ Nw)) ∧
      (∀ k ∈ Finset.Icc J m, |Y k - κ * turnPsi (hrU P Q τ x) (hrA1 P Q) qs (δ ^ 3 / 2) δ k| ≤
        C * δ ^ 3 * |κ| * W + Cosc * (|μ| / δ)) ∧
      (∀ k ∈ Finset.Icc m (Nw + 1), |Y k - κ * turnPsi (hrU P Q τ x) (hrA1 P Q) qs (δ ^ 3 / 2) δ k| ≤
        C * δ ^ 3 * |κ| * turnPsi (hrU P Q τ x) (hrA1 P Q) qs (δ ^ 3 / 2) δ k +
          Ctop * |μ| / δ / airyWt (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k))

/-- **Composition lemma.**  Under the simple-turn hypotheses of `discrete_airy_hahn_racah`, the constants are independent
of `Y`, `h`: any `Y` that solves every row `k ≥ 1` of `jac (hrAk P Q a b h) (hrCk P Q τ x a b h) Y = 0` at a scale
`0 < h ≤ δ₀³` and is bounded by `Y_max` satisfies `AiryOutAt` (`δ = h^{1/3}`). -/
theorem airy_chain_compose {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hturn : Phi P Q τ x (qs ^ 2) = 0) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧ ∀ (h : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < h → h ≤ δ0 ^ 3 →
        (∀ k : ℤ, 1 ≤ k → jac (hrAk P Q a b h) (hrCk P Q τ x a b h) Y k = 0) → (∀ k, |Y k| ≤ Ymax) →
        AiryOutAt P Q τ x qs Y Ymax A0 r δ0 C Cosc Ctop W Cmu ξ0 D h := by
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, -, hδ0, -, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    discrete_airy_hahn_racah hP hQ a b τ x qs hqs hτ hκ hα hβ hturn A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro h Y Ymax hh hhδ hrows hbd
  obtain ⟨δ, hδ0', hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h := by
    refine ⟨h ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos hh _, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    norm_num
  have hδle : δ ≤ δ0 := by
    by_contra hcon
    push Not at hcon
    have : δ0 ^ 3 < δ ^ 3 := by gcongr
    linarith
  obtain ⟨J, m, Nw, hJ, hJm, hmN, hwin, h1, h2, h3, h4, h5, Hc⟩ := H δ hδ0' hδle
  obtain ⟨hxi, -, -, -, HY⟩ := Hc
  have hrows' : ∀ k ∈ Finset.Icc (J + 1) Nw,
      jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0 := by
    intro k hk
    have hk1 : 1 ≤ k := by rw [Finset.mem_Icc] at hk; omega
    rw [hδ3]
    exact hrows k hk1
  obtain ⟨κ, μ, hμ, hlow, hup⟩ := HY Y Ymax hrows' (hbd _) (hbd _)
  exact ⟨δ, hδ0', hδle, hδ3, J, m, Nw, hJ, hJm, hmN, hwin, h1, h2, h3, h4, h5, hxi, κ, μ, hμ, hlow, hup⟩

/-- `Φ_{-1}(q_*²) = 0` for the Hahn data `P = 1, Q = 0`, `x ∈ (-1,0)`, `q_*² = 1 - x²`. -/
lemma hahn_turn_neg {x : ℝ} (hx0 : x < 0) (hx1 : -1 < x) :
    Phi 1 0 (-1) x (Real.sqrt (1 - x ^ 2) ^ 2) = 0 := by
  have hq2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith)
  unfold Phi etilde
  rw [hq2]
  have : (1 - 1 * (1 - x ^ 2)) * (1 - 0 * (1 - x ^ 2)) = (-x) ^ 2 := by ring
  rw [this, Real.sqrt_sq (by linarith)]
  simp

/-- **Airy limit for the actual `3j` chain at lattice nodes `x_n = x ∈ (-1, 0)`** (`thm:hahnAiryConnection`, negative `x`,
`τ = -1`): for the twisted natural-gauge chain `(-1)^k Ŷ_k`, with `Y_max = √N` from `hahn_chain_abs_le`. -/
theorem hahn_chain_airy_neg (M σ : ℤ) (x : ℚ) (hx0 : x < 0) (hx1 : -1 < x) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧ ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N → (n : ℤ) < N - max |M| |σ| →
        xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x → 1 / (N : ℝ) ≤ δ0 ^ 3 →
        AiryOutAt 1 0 (-1) (x : ℝ) (Real.sqrt (1 - (x : ℝ) ^ 2))
          (fun j => (-1 : ℝ) ^ j * hahn3jY M σ N x j) (Real.sqrt (N : ℝ)) A0 r δ0 C Cosc Ctop W Cmu ξ0 D (1 / (N : ℝ)) := by
  have hx0' : (x : ℝ) < 0 := by exact_mod_cast hx0
  have hx1' : (-1 : ℝ) < x := by exact_mod_cast hx1
  have hq2 : Real.sqrt (1 - (x : ℝ) ^ 2) ^ 2 = 1 - (x : ℝ) ^ 2 := Real.sq_sqrt (by nlinarith)
  have hqs : 0 < Real.sqrt (1 - (x : ℝ) ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    airy_chain_compose (P := 1) (Q := 0) (by norm_num) (by norm_num) (M : ℝ) (σ : ℝ) (-1) (x : ℝ)
      (Real.sqrt (1 - (x : ℝ) ^ 2)) hqs (by norm_num) (by linarith) (by rw [hq2]; nlinarith) (by simp)
      (hahn_turn_neg hx0' hx1') A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro N n hN hn hxn hNδ
  have hN0 : (0 : ℤ) < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  refine H (1 / (N : ℝ)) _ _ (by positivity) hNδ (fun k hk => hahn_class_chain_neg M σ N x hN0 k hk) ?_
  intro k
  have h1 : |(-1 : ℝ) ^ k| = 1 := by simp [abs_zpow]
  rw [abs_mul, h1, one_mul, ← hxn]
  exact hahn_chain_abs_le M σ N hN n hn k

/-- info: 'FormalResearch.Special.jac_twist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jac_twist

/-- info: 'FormalResearch.Special.hahn_class_chain_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_class_chain_neg

/-- info: 'FormalResearch.Special.racah_class_chain_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_class_chain_neg

/-- info: 'FormalResearch.Special.airy_chain_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_chain_compose

/-- info: 'FormalResearch.Special.hahn_chain_airy_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_chain_airy_neg

/-- **Negative-`x` Airy asymptotics along an infinite sequence `N → ∞`** (`hahn_chain_airy_neg` + `hahn_node_exists`). -/
theorem hahn_chain_airy_neg_infinite (M σ : ℤ) (x : ℚ) (hx0 : x < 0) (hx1 : -1 < x)
    (hpar : Odd (x.num + (x.den : ℤ)) ∨ Even (1 + |M + σ|)) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧ ∀ N0 : ℕ, ∃ (N : ℤ) (n : ℕ), (N0 : ℤ) < N ∧ max |M| |σ| < N ∧
        (n : ℤ) < N - max |M| |σ| ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x ∧ 1 / (N : ℝ) ≤ δ0 ^ 3 ∧
        AiryOutAt 1 0 (-1) (x : ℝ) (Real.sqrt (1 - (x : ℝ) ^ 2))
          (fun j => (-1 : ℝ) ^ j * hahn3jY M σ N x j) (Real.sqrt (N : ℝ)) A0 r δ0 C Cosc Ctop W Cmu ξ0 D (1 / (N : ℝ)) := by
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    hahn_chain_airy_neg M σ x hx0 hx1 A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro N0
  have hnum : x.num < 0 := Rat.num_neg.2 hx0
  have hlt : -(x.den : ℤ) < x.num := by
    have h1 : -1 < (x.num : ℚ) / (x.den : ℚ) := by rwa [Rat.num_div_den]
    have hd : (0 : ℚ) < (x.den : ℚ) := by exact_mod_cast x.den_pos
    have h2 : -(x.den : ℚ) < (x.num : ℚ) := by
      rw [lt_div_iff₀ hd] at h1; linarith
    exact_mod_cast h2
  obtain ⟨T, hT⟩ := exists_nat_gt (1 / δ0 ^ 3)
  obtain ⟨N, n, hN0, hN1, hN2, hxn⟩ :=
    hahn_node_exists M σ x.num x.den hlt (by omega) hpar (max N0 T)
  have hxn' : xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x := by
    rw [hxn]; exact_mod_cast Rat.num_div_den x
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℤ) < N := by have := le_max_left N0 T; omega
    exact_mod_cast this
  have hNT : (T : ℝ) < N := by
    have : (T : ℤ) < N := by have := le_max_right N0 T; omega
    exact_mod_cast this
  have hδ : 1 / (N : ℝ) ≤ δ0 ^ 3 := by
    have h3 : 0 < δ0 ^ 3 := by positivity
    rw [div_le_iff₀ hNpos]
    have := (div_lt_iff₀ h3).1 hT
    nlinarith
  exact ⟨N, n, by have := le_max_left N0 T; omega, hN1, hN2, hxn', hδ, H N n hN1 hN2 hxn' hδ⟩

/-- info: 'FormalResearch.Special.hahn_chain_airy_neg_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_chain_airy_neg_infinite

end FormalResearch.Special
