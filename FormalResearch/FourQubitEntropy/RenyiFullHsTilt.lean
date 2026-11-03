module

public import FormalResearch.FourQubitEntropy.RenyiFullLowTilt

/-!
# `lem:fqe-hs-tilt`: from `(a,b,c,c)` to the one-large spectrum

Paper E, `renyi_hs_analytic.tex`.  At `q = 8/5` and for purity `p ≤ 9/16`, among spectra
`(a,b,c,c)`, `a ≥ b ≥ c ≥ 0`, of a fixed purity `H_q - t` is maximised only by the one-large
spectrum.  The path is `(1/4+u+d, 1/4+u-d, 1/4-u, 1/4-u)`, `d = √((x-4u²)/2)`, decreasing `u` from
`u₁ = 1/4 - c` to `u₀ = √(x/12)`; `dt/du = 3x - 36u² ≤ 0` and `dH/dt = η > 1`
(`path_strictAntiOn` with `hsTilt_slope_numeric`).
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

noncomputable def uE1 (x u : ℝ) : ℝ := 1 / 4 + u + ddF x u
noncomputable def uE2 (x u : ℝ) : ℝ := 1 / 4 + u - ddF x u
noncomputable def uE3 (u : ℝ) : ℝ := 1 / 4 - u
noncomputable def uT (x u : ℝ) : ℝ := 1 * uE1 x u ^ 3 + 1 * uE2 x u ^ 3 + 2 * uE3 u ^ 3

/-- The context of the upper-chart path: `u₁ = 1/4 - c`, `d₁ = (a-b)/2`, `x = 4u₁²+2d₁²`,
`u₀ = √(x/12)` (`12u₀² = x`); `b > c` means `d₁ < 2u₁`. -/
structure UpCtx (u1 d1 x u0 : ℝ) : Prop where
  hc : 0 ≤ 1 / 4 - u1
  hd1 : 0 ≤ d1
  hd1u : d1 < 2 * u1
  hx : x = 4 * u1 ^ 2 + 2 * d1 ^ 2
  hu0 : 12 * u0 ^ 2 = x
  hu00 : 0 ≤ u0

theorem UpCtx.u1_pos {u1 d1 x u0 : ℝ} (C : UpCtx u1 d1 x u0) : 0 < u1 := by
  have := C.hd1; have := C.hd1u; linarith

theorem UpCtx.x_lt {u1 d1 x u0 : ℝ} (C : UpCtx u1 d1 x u0) : x < 12 * u1 ^ 2 := by
  have := C.hd1; have := C.hd1u; have := C.hx
  nlinarith

theorem UpCtx.lt {u1 d1 x u0 : ℝ} (C : UpCtx u1 d1 x u0) : u0 < u1 := by
  by_contra hle
  push Not at hle
  have := C.x_lt; have := C.hu0; have := C.u1_pos
  nlinarith

theorem UpCtx.x_ge {u1 d1 x u0 : ℝ} (C : UpCtx u1 d1 x u0) : 4 * u1 ^ 2 ≤ x := by
  have := C.hx; nlinarith [sq_nonneg d1]

theorem UpCtx.mem {u1 d1 x u0 : ℝ} (C : UpCtx u1 d1 x u0) {u : ℝ} (hu : u ∈ Icc u0 u1) :
    4 * u ^ 2 ≤ x ∧ x ≤ 12 * u ^ 2 := by
  have h0 : 0 ≤ u := C.hu00.trans hu.1
  have := C.x_ge; have := C.hu0
  have h5 := mul_self_le_mul_self C.hu00 hu.1
  constructor <;> nlinarith [hu.1, hu.2]

theorem UpCtx.dd_u1 {u1 d1 x u0 : ℝ} (C : UpCtx u1 d1 x u0) : ddF x u1 = d1 := by
  unfold ddF
  rw [show (x - 4 * u1 ^ 2) / 2 = d1 ^ 2 by rw [C.hx]; ring, Real.sqrt_sq C.hd1]

theorem UpCtx.dd_u0 {u1 d1 x u0 : ℝ} (C : UpCtx u1 d1 x u0) : ddF x u0 = 2 * u0 := by
  unfold ddF
  have : (x - 4 * u0 ^ 2) / 2 = (2 * u0) ^ 2 := by rw [← C.hu0]; ring
  rw [this, Real.sqrt_sq (by linarith [C.hu00])]

theorem UpCtx.E3_nonneg {u1 d1 x u0 : ℝ} (C : UpCtx u1 d1 x u0) {u : ℝ} (hu : u ∈ Icc u0 u1) :
    0 ≤ uE3 u := by
  unfold uE3; linarith [C.hc, hu.2]

theorem UpCtx.dd_le {u1 d1 x u0 : ℝ} (C : UpCtx u1 d1 x u0) {u : ℝ} (hu : u ∈ Icc u0 u1) :
    ddF x u ≤ 2 * u := by
  have h0 : 0 ≤ u := C.hu00.trans hu.1
  have h2 := ddF_sq (C.mem hu).1
  have h3 : ddF x u ^ 2 ≤ (2 * u) ^ 2 := by
    rw [h2]; nlinarith [(C.mem hu).2]
  exact (abs_le_of_sq_le_sq' h3 (by linarith)).2

theorem UpCtx.E3_le_E2 {u1 d1 x u0 : ℝ} (C : UpCtx u1 d1 x u0) {u : ℝ} (hu : u ∈ Icc u0 u1) :
    uE3 u ≤ uE2 x u := by
  have := C.dd_le hu
  unfold uE3 uE2; linarith

theorem UpCtx.E2_le_E1 {u1 d1 x u0 : ℝ} (_C : UpCtx u1 d1 x u0) (u : ℝ) :
    uE2 x u ≤ uE1 x u := by
  unfold uE2 uE1; linarith [ddF_nonneg x u]

theorem UpCtx.interior {u1 d1 x u0 : ℝ} (C : UpCtx u1 d1 x u0) {u : ℝ} (hu : u ∈ Ioo u0 u1) :
    4 * u ^ 2 < x ∧ 0 < ddF x u ∧ ddF x u < 2 * u := by
  have h0 : 0 ≤ u := C.hu00.trans hu.1.le
  have hu2 : u ^ 2 < u1 ^ 2 := by nlinarith [hu.2]
  have hx := C.x_ge
  have h1 : 4 * u ^ 2 < x := by nlinarith
  have h2 := ddF_sq h1.le
  have hp : 0 < ddF x u := Real.sqrt_pos.2 (by linarith)
  refine ⟨h1, hp, ?_⟩
  have hu0 := C.hu0
  have h3 : ddF x u ^ 2 < (2 * u) ^ 2 := by
    rw [h2]
    have : u0 ^ 2 < u ^ 2 := by nlinarith [mul_self_lt_mul_self C.hu00 hu.1]
    nlinarith
  exact (abs_lt_of_sq_lt_sq' h3 (by linarith [hu.1])).2

theorem uE1_deriv {x u : ℝ} (h : 4 * u ^ 2 < x) :
    HasDerivAt (uE1 x) (1 + (-2 * u / ddF x u)) u := by
  have h1 := sqrtPath_hasDerivAt h
  have := ((hasDerivAt_id u).const_add (1 / 4 : ℝ)).add h1
  unfold uE1 ddF
  exact this

theorem uE2_deriv {x u : ℝ} (h : 4 * u ^ 2 < x) :
    HasDerivAt (uE2 x) (1 - (-2 * u / ddF x u)) u := by
  have h1 := sqrtPath_hasDerivAt h
  have := ((hasDerivAt_id u).const_add (1 / 4 : ℝ)).sub h1
  unfold uE2 ddF
  exact this

theorem uE3_deriv (u : ℝ) : HasDerivAt uE3 (-1) u := by
  unfold uE3
  simpa using (hasDerivAt_id u).const_sub (1 / 4 : ℝ)

theorem uT_deriv {x u : ℝ} (h : 4 * u ^ 2 < x) :
    HasDerivAt (uT x) (3 * (1 * (1 + (-2 * u / ddF x u)) * uE1 x u ^ 2 +
      1 * (1 - (-2 * u / ddF x u)) * uE2 x u ^ 2 + 2 * (-1) * uE3 u ^ 2)) u := by
  have h1 := (uE1_deriv h).pow 3
  have h2 := (uE2_deriv h).pow 3
  have h3 := (uE3_deriv u).pow 3
  have := ((h1.const_mul 1).add (h2.const_mul 1)).add (h3.const_mul 2)
  unfold uT
  convert this using 1
  simp
  ring

theorem upKappa {x u : ℝ} (h : 4 * u ^ 2 < x) :
    1 * (1 + (-2 * u / ddF x u)) * uE1 x u ^ 2 + 1 * (1 - (-2 * u / ddF x u)) * uE2 x u ^ 2 +
      2 * (-1) * uE3 u ^ 2 = x - 12 * u ^ 2 := by
  have h2 := ddF_sq h.le
  have hp : 0 < ddF x u := Real.sqrt_pos.2 (by linarith)
  unfold uE1 uE2 uE3
  field_simp
  nlinarith [h2]

theorem uE1_cont (x : ℝ) : Continuous (uE1 x) := by
  unfold uE1; have := ddF_cont x; fun_prop
theorem uE2_cont (x : ℝ) : Continuous (uE2 x) := by
  unfold uE2; have := ddF_cont x; fun_prop
theorem uE3_cont : Continuous uE3 := by unfold uE3; fun_prop
theorem uT_cont (x : ℝ) : Continuous (uT x) := by
  unfold uT; have := uE1_cont x; have := uE2_cont x; have := uE3_cont; fun_prop

/-- The functional on `(a,b,c,c)` at `q = 8/5`: `H_q - t`. -/
noncomputable def upF (q a b c : ℝ) : ℝ :=
  Real.logb 2 (a ^ q + b ^ q + 2 * c ^ q) / (1 - q) - (a ^ 3 + b ^ 3 + 2 * c ^ 3)

/-- The functional on `(a,b,b,b)`: `H_q - t`. -/
noncomputable def oneF (q a b : ℝ) : ℝ :=
  Real.logb 2 (a ^ q + 3 * b ^ q) / (1 - q) - (a ^ 3 + 3 * b ^ 3)

/-- **`lem:fqe-hs-tilt`, strict form** (`q = 8/5`, `ω = 1`, `p ≤ 9/16`). -/
theorem hsTilt_chart_strict {a b c : ℝ} (hc : 0 ≤ c) (hcb : c < b) (hba : b ≤ a)
    (hs : a + b + 2 * c = 1) (hp : a ^ 2 + b ^ 2 + 2 * c ^ 2 ≤ 9 / 16) :
    ∃ a' b' : ℝ, 0 ≤ b' ∧ b' ≤ a' ∧ a' + 3 * b' = 1 ∧
      a' ^ 2 + 3 * b' ^ 2 = a ^ 2 + b ^ 2 + 2 * c ^ 2 ∧
      upF (8 / 5) a b c < oneF (8 / 5) a' b' := by
  have hq : 1 < (8 / 5 : ℝ) := by norm_num
  obtain ⟨u1, hu1⟩ : ∃ u1 : ℝ, u1 = 1 / 4 - c := ⟨_, rfl⟩
  obtain ⟨d1, hd1⟩ : ∃ d1 : ℝ, d1 = (a - b) / 2 := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 4 * u1 ^ 2 + 2 * d1 ^ 2 := ⟨_, rfl⟩
  have hu1pos : 0 < u1 := by rw [hu1]; linarith
  have hxpos : 0 < x := by rw [hx]; positivity
  obtain ⟨u0, hu0⟩ : ∃ u0 : ℝ, u0 = Real.sqrt (x / 12) := ⟨_, rfl⟩
  have hu02 : 12 * u0 ^ 2 = x := by
    rw [hu0, Real.sq_sqrt (by positivity)]; ring
  have hu00 : 0 ≤ u0 := by rw [hu0]; exact Real.sqrt_nonneg _
  have had : a = 1 / 4 + u1 + d1 := by rw [hu1, hd1]; linarith
  have hbd : b = 1 / 4 + u1 - d1 := by rw [hu1, hd1]; linarith
  have hcd : c = 1 / 4 - u1 := by rw [hu1]; ring
  have C : UpCtx u1 d1 x u0 :=
    ⟨by rw [hu1]; linarith, by rw [hd1]; linarith, by rw [hd1, hu1]; linarith, hx, hu02, hu00⟩
  have hx516 : x ≤ 5 / 16 := by
    have : a ^ 2 + b ^ 2 + 2 * c ^ 2 = 1 / 4 + x := by
      rw [had, hbd, hcd, hx]; ring
    linarith
  have hlt := C.lt
  have E1pos : ∀ u ∈ Icc u0 u1, 0 < uE1 x u := fun u hu => by
    unfold uE1; linarith [C.hu00.trans hu.1, ddF_nonneg x u]
  have hZpos : ∀ u ∈ Icc u0 u1, 0 < Zp (8 / 5) 1 1 2 (uE1 x) (uE2 x) uE3 u := fun u hu => by
    unfold Zp
    have a1 : 0 < uE1 x u ^ (8 / 5 : ℝ) := Real.rpow_pos_of_pos (E1pos u hu) _
    have a2 : 0 ≤ uE2 x u ^ (8 / 5 : ℝ) :=
      Real.rpow_nonneg ((C.E3_nonneg hu).trans (C.E3_le_E2 hu)) _
    have a3 : 0 ≤ uE3 u ^ (8 / 5 : ℝ) := Real.rpow_nonneg (C.E3_nonneg hu) _
    linarith
  have hmono := path_strictAntiOn (q := 8 / 5) (ω := 1) (n1 := 1) (n2 := 1) (n3 := 2)
    (E1 := uE1 x) (E2 := uE2 x) (E3 := uE3) (T := uT x) (u0 := u0) (u1 := u1) hq
    (uE1_cont x).continuousOn (uE2_cont x).continuousOn uE3_cont.continuousOn
    (uT_cont x).continuousOn hZpos
    (w1 := fun u => 1 + (-2 * u / ddF x u)) (w2 := fun u => 1 - (-2 * u / ddF x u))
    (w3 := fun _ => -1)
    (fun u hu => uE1_deriv (C.interior hu).1) (fun u hu => uE2_deriv (C.interior hu).1)
    (fun u _ => uE3_deriv u) (fun u hu => uT_deriv (C.interior hu).1)
    (fun u hu => by ring)
    (fun u hu => by
      obtain ⟨-, hp, -⟩ := C.interior hu
      unfold uE1 uE2 uE3
      field_simp
      ring)
    (fun u hu => by
      obtain ⟨-, hp, hlt2⟩ := C.interior hu
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [uE1, uE2, uE3] at h <;> linarith)
    (fun u hu => by
      have := upKappa (C.interior hu).1
      show 1 * (1 + (-2 * u / ddF x u)) * uE1 x u ^ 2 + 1 * (1 - (-2 * u / ddF x u)) * uE2 x u ^ 2 +
        2 * (-1) * uE3 u ^ 2 < 0
      rw [this]
      have := C.mem (Ioo_subset_Icc_self hu)
      have h1 := hu.1
      have h2 := C.hu0
      nlinarith)
    (fun u hu => by
      obtain ⟨h4, hpd, hlt2⟩ := C.interior hu
      have hume : u ∈ Icc u0 u1 := Ioo_subset_Icc_self hu
      have hE3 := C.E3_nonneg hume
      have e32 : uE3 u < uE2 x u := by unfold uE3 uE2; linarith
      have e21 : uE2 x u < uE1 x u := by unfold uE2 uE1; linarith
      have hD := neg_dd2_ge (r := 8 / 5 - 1) (a := uE1 x u) (b := uE2 x u) (c := uE3 u)
        (by norm_num) (by norm_num) hE3 e32 e21
      have hmean : (uE1 x u + uE2 x u + uE3 u) / 3 = (1 - uE3 u) / 3 := by
        unfold uE1 uE2 uE3; ring
      rw [hmean] at hD
      have hZ := hZpos u hume
      have hsum : 1 * uE1 x u + 1 * uE2 x u + 2 * uE3 u = 1 := by
        unfold uE1 uE2 uE3; ring
      have hpur : 1 * uE1 x u ^ 2 + 1 * uE2 x u ^ 2 + 2 * uE3 u ^ 2 = 1 / 4 + x := by
        unfold uE1 uE2 uE3
        have := ddF_sq h4.le
        nlinarith
      have hZa : Zp (8 / 5) 1 1 2 (uE1 x) (uE2 x) uE3 u ≤ (1 / 4 + x) ^ ((8 / 5 : ℝ) - 1) := by
        unfold Zp
        exact Z_le_pur (n1 := 1) (n2 := 1) (n3 := 2) hq (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (E1pos u hume).le ((C.E3_nonneg hume).trans (C.E3_le_E2 hume))
          (C.E3_nonneg hume) hsum hpur.symm
      have hm0 : 0 < (1 - uE3 u) / 3 := by unfold uE3; linarith [hume.1, hume.2, C.hu00]
      have hm1 : (1 - uE3 u) / 3 ≤ 1 / 3 := by linarith
      have hnum := hsTilt_slope_numeric (p := 1 / 4 + x) (by linarith) (by linarith) hZ hZa hm0 hm1
      unfold slope3
      refine slope_of_bound hq (Real.log_pos (by norm_num)) hZ hD ?_
      have hpos : 0 < (8 / 5 - 1 : ℝ) / 2 := by norm_num
      calc 3 * 1 * ((8 / 5 - 1) * Real.log 2 * Zp (8 / 5) 1 1 2 (uE1 x) (uE2 x) uE3 u)
          = (8 / 5 - 1) / 2 * (6 * 1 * Real.log 2 * Zp (8 / 5) 1 1 2 (uE1 x) (uE2 x) uE3 u) := by
            ring
        _ < (8 / 5 - 1) / 2 * (8 / 5 * (1 - (8 / 5 - 1)) * ((1 - uE3 u) / 3) ^ (8 / 5 - 1 - 2 : ℝ)) :=
            mul_lt_mul_of_pos_left hnum hpos
        _ = 8 / 5 * ((8 / 5 - 1) * (1 - (8 / 5 - 1)) / 2 * ((1 - uE3 u) / 3) ^ (8 / 5 - 1 - 2 : ℝ)) := by
            ring)
  -- endpoint values
  have e1 : uE1 x u1 = a := by unfold uE1; rw [C.dd_u1]; linarith
  have e2 : uE2 x u1 = b := by unfold uE2; rw [C.dd_u1]; linarith
  have e3 : uE3 u1 = c := by unfold uE3; linarith
  have f1 : uE1 x u0 = 1 / 4 + 3 * u0 := by unfold uE1; rw [C.dd_u0]; ring
  have f2 : uE2 x u0 = 1 / 4 - u0 := by unfold uE2; rw [C.dd_u0]; ring
  have f3 : uE3 u0 = 1 / 4 - u0 := rfl
  have hlt' := hmono ⟨le_refl _, hlt.le⟩ ⟨hlt.le, le_refl _⟩ hlt
  have g1 : pathF (8 / 5) 1 1 1 2 (uE1 x) (uE2 x) uE3 (uT x) u1 = upF (8 / 5) a b c := by
    unfold pathF Zp uT upF
    rw [e1, e2, e3]
    simp only [one_mul]
  have g0 : pathF (8 / 5) 1 1 1 2 (uE1 x) (uE2 x) uE3 (uT x) u0 =
      oneF (8 / 5) (1 / 4 + 3 * u0) (1 / 4 - u0) := by
    unfold pathF Zp uT oneF
    rw [f1, f2, f3]
    have h2 : 1 * (1 / 4 + 3 * u0) ^ (8 / 5 : ℝ) + 1 * (1 / 4 - u0) ^ (8 / 5 : ℝ) +
        2 * (1 / 4 - u0) ^ (8 / 5 : ℝ) = (1 / 4 + 3 * u0) ^ (8 / 5 : ℝ) +
        3 * (1 / 4 - u0) ^ (8 / 5 : ℝ) := by ring
    rw [h2]
    ring
  rw [g1, g0] at hlt'
  have hb' : 0 ≤ 1 / 4 - u0 := by
    have := C.E3_nonneg ⟨le_refl _, hlt.le⟩
    unfold uE3 at this
    exact this
  refine ⟨1 / 4 + 3 * u0, 1 / 4 - u0, hb', by linarith, by ring, ?_, hlt'⟩
  have : a ^ 2 + b ^ 2 + 2 * c ^ 2 = 1 / 4 + x := by
    rw [had, hbd, hcd, hx]; ring
  rw [this]
  linear_combination hu02

theorem renyi_abcc (q a b c : ℝ) :
    renyiSpec q ![a, b, c, c] - 1 * cub ![a, b, c, c] = upF q a b c := by
  unfold renyiSpec cub upF
  simp only [Fin.sum_univ_four]
  simp
  ring_nf

theorem renyi_abbb (q a b : ℝ) :
    renyiSpec q ![a, b, b, b] - 1 * cub ![a, b, b, b] = oneF q a b := by
  unfold renyiSpec cub oneF
  simp only [Fin.sum_univ_four]
  simp
  ring_nf

theorem pur_abbb (a b : ℝ) : pur ![a, b, b, b] = a ^ 2 + 3 * b ^ 2 := by
  unfold pur; simp [Fin.sum_univ_four]; ring

theorem cub_abbb (a b : ℝ) : cub ![a, b, b, b] = a ^ 3 + 3 * b ^ 3 := by
  unfold cub; simp [Fin.sum_univ_four]; ring

/-- **`lem:fqe-hs-tilt`** (supporting-function form, `q = 8/5`, `β = 1/12`): a spectrum
`(a,b,c,c)` of purity `≤ 9/16` has a one-large spectrum `(a',b',b',b')` of the same purity with at
least as large `Λ_{(α,1/12,γ)}`, equal only if it is the spectrum itself. -/
theorem hsTilt_reduce (α γ : ℝ) {a b c : ℝ} (hc : 0 ≤ c) (hcb : c ≤ b) (hba : b ≤ a)
    (hs : a + b + 2 * c = 1) (hp : a ^ 2 + b ^ 2 + 2 * c ^ 2 ≤ 9 / 16) :
    ∃ a' b' : ℝ, 0 ≤ b' ∧ b' ≤ a' ∧ a' + 3 * b' = 1 ∧
      pur ![a', b', b', b'] = pur ![a, b, c, c] ∧
      Lam (8 / 5) α (1 / 12) γ ![a, b, c, c] ≤ Lam (8 / 5) α (1 / 12) γ ![a', b', b', b'] ∧
      (![a, b, c, c] = ![a', b', b', b'] ∨
        Lam (8 / 5) α (1 / 12) γ ![a, b, c, c] < Lam (8 / 5) α (1 / 12) γ ![a', b', b', b']) := by
  rcases hcb.eq_or_lt with hbc | hbc
  · subst hbc
    exact ⟨a, c, hc, hba, by linarith, rfl, le_refl _, Or.inl rfl⟩
  · obtain ⟨a', b', hb', hab', hs', hpur, hlt⟩ := hsTilt_chart_strict hc hbc hba hs hp
    have hpp : pur ![a', b', b', b'] = pur ![a, b, c, c] := by
      rw [pur_abbb, pur_abcc]; exact hpur
    have hd := Lam_diff (8 / 5) α (1 / 12) γ hpp
    have e12 : (12 : ℝ) * (1 / 12) = 1 := by norm_num
    rw [e12, renyi_abbb, renyi_abcc] at hd
    refine ⟨a', b', hb', hab', hs', hpp, ?_, Or.inr ?_⟩ <;> linarith

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.hsTilt_chart_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hsTilt_chart_strict

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.hsTilt_reduce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hsTilt_reduce

end FormalResearch.FourQubitEntropy.RenyiFull
