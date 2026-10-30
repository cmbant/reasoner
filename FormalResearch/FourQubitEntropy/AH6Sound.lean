import FormalResearch.FourQubitEntropy.AH6Cert

/-!
# Soundness of the AH-6 certificate for the real parameters

For a real `x` in the bracket `[XLO/10^45, (XLO+1)/10^45]`, the parameters `parR x = (x, ln 2, ln 3, ln c, ln a, ln d)`
(`c = 4u`, `a = 3u + x`, `d = u + x`, `u = (1-2x)/30`) are enclosed by `parB`, hence the real computation
`stageA .. stageD3` satisfies the facts of `CertFacts` (positivity of the constants, distinct nodes, and
`Π(e) > 0` for all `e ≥ 0`).
-/

namespace FormalResearch.FourQubitEntropy.AH6

@[simp] theorem rat_real (p q : ℤ) : (rat p q : ℝ) = (p : ℝ) / (q : ℝ) := by
  simp [rat, div_eq_mul_inv]

/-- The real parameters of the computation. -/
noncomputable def parR (x : ℝ) : Par ℝ :=
  { x := x, l2 := Real.log 2, l3 := Real.log 3,
    lc := Real.log (ic 4 * uOf x), la := Real.log (ic 3 * uOf x + x), ld := Real.log (uOf x + x) }

theorem zFor_log {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    Real.log ((1 + zFor r c) / (1 - zFor r c)) = Real.log (r * c) := by
  have h1 : 0 < r * c := mul_pos hr hc
  have h2 : r * c + 1 ≠ 0 := by positivity
  have h3 : (1 + zFor r c) / (1 - zFor r c) = r * c := by
    unfold zFor
    simp only [ic_real, Int.cast_one]
    field_simp
    ring
  rw [h3]

/-- The bracket of `x_*`. -/
def InBracket (x : ℝ) : Prop := (XLO : ℝ) / 10 ^ 45 ≤ x ∧ x ≤ ((XLO : ℝ) + 1) / 10 ^ 45

theorem bracket_aux {x S N XL m Q : ℝ} (hS : 0 < S) (hN : 0 < N) (h1 : XL ≤ x * N)
    (h2 : x * N ≤ XL + 1) (hm1 : m * (2 * N) ≤ (2 * XL + 1) * S)
    (hm2 : (2 * XL + 1) * S < (m + 1) * (2 * N)) (hr : S < (Q + 1) * (2 * N)) :
    |x * S - m| ≤ Q + 2 := by
  have e1 := mul_le_mul_of_nonneg_left h1 hS.le
  have e2 := mul_le_mul_of_nonneg_left h2 hS.le
  rw [abs_le]
  constructor
  · by_contra hcon
    push Not at hcon
    have : (x * S - m) * (2 * N) < (-(Q + 2)) * (2 * N) := mul_lt_mul_of_pos_right hcon (by linarith)
    nlinarith
  · by_contra hcon
    push Not at hcon
    have : (Q + 2) * (2 * N) < (x * S - m) * (2 * N) := mul_lt_mul_of_pos_right hcon (by linarith)
    nlinarith

theorem xB_enc {x : ℝ} (hx : InBracket x) : Enc x xB := by
  intro _
  obtain ⟨h1, h2⟩ := hx
  have hSC := SC_real_pos
  have hN : (0 : ℝ) < 10 ^ 45 := by positivity
  unfold xB
  show |x * (SC : ℝ) - (((((2 * XLO + 1) * (SC : ℤ)) / (2 * 10 ^ 45) : ℤ)) : ℝ)| ≤
    ((SC / (2 * 10 ^ 45) + 2 : ℕ) : ℝ)
  have hpos : (0 : ℤ) < 2 * 10 ^ 45 := by norm_num
  have hm1 : ((((2 * XLO + 1) * (SC : ℤ)) / (2 * 10 ^ 45) : ℤ) : ℝ) * (2 * 10 ^ 45) ≤
      (2 * (XLO : ℝ) + 1) * SC := by
    have := Int.ediv_mul_le ((2 * XLO + 1) * (SC : ℤ)) hpos.ne'
    exact_mod_cast this
  have hm2 : (2 * (XLO : ℝ) + 1) * SC <
      (((((2 * XLO + 1) * (SC : ℤ)) / (2 * 10 ^ 45) : ℤ) : ℝ) + 1) * (2 * 10 ^ 45) := by
    have := Int.lt_ediv_add_one_mul_self ((2 * XLO + 1) * (SC : ℤ)) hpos
    exact_mod_cast this
  have hr1 : (SC : ℝ) < (((SC / (2 * 10 ^ 45) : ℕ) : ℝ) + 1) * (2 * 10 ^ 45) := by
    have h3 := Nat.lt_mul_div_succ SC (by norm_num : 0 < 2 * 10 ^ 45)
    have h4 : SC < (SC / (2 * 10 ^ 45) + 1) * (2 * 10 ^ 45) := by rw [mul_comm]; exact h3
    exact_mod_cast h4
  have hxN1 : (XLO : ℝ) ≤ x * 10 ^ 45 := by rwa [div_le_iff₀ hN] at h1
  have hxN2 : x * 10 ^ 45 ≤ (XLO : ℝ) + 1 := by rwa [le_div_iff₀ hN] at h2
  have := bracket_aux hSC hN hxN1 hxN2 hm1 hm2 hr1
  push_cast
  exact this


theorem InBracket.bounds {x : ℝ} (hx : InBracket x) : 1 / 20 < x ∧ x < 1 / 10 := by
  obtain ⟨h1, h2⟩ := hx
  constructor
  · have : (1 / 20 : ℝ) < (XLO : ℝ) / 10 ^ 45 := by norm_num [XLO]
    linarith
  · have : ((XLO : ℝ) + 1) / 10 ^ 45 < 1 / 10 := by norm_num [XLO]
    linarith

theorem uOf_pos {x : ℝ} (hx : InBracket x) : 0 < uOf x := by
  have := hx.bounds
  unfold uOf; simp only [ic_real]; norm_num; linarith

theorem log_two_enc : Enc (Real.log 2) l2B := by
  have h := lnB_enc (Enc.rat 1 3) 60
  have e : (1 + (rat 1 3 : ℝ)) / (1 - (rat 1 3 : ℝ)) = 2 := by simp; norm_num
  rw [e] at h; exact h

theorem log_three_enc : Enc (Real.log 3) l3B := by
  have h := lnB_enc (Enc.rat 1 5) 40
  have e : (1 + (rat 1 5 : ℝ)) / (1 - (rat 1 5 : ℝ)) = 3 / 2 := by simp; norm_num
  rw [e] at h
  have h2 := Enc.add log_two_enc h
  have e2 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [← e2] at h2; exact h2

theorem log_shift {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    Real.log c = Real.log (r * c) - Real.log r := by
  rw [Real.log_mul hr.ne' hc.ne']; ring

theorem parR_enc {x : ℝ} (hx : InBracket x) : ParEnc (parR x) parB := by
  have hxe := xB_enc hx
  have hb := hx.bounds
  have hu := uOf_pos hx
  have hxpos : 0 < x := by linarith [hb.1]
  have hl2 := log_two_enc
  have hl3 := log_three_enc
  have hUe : Enc (uOf x) (uOf xB) := by unfold uOf; enc
  have r9 : (rat 9 1 : ℝ) = 9 := by simp [rat_real]
  have r6 : (rat 6 1 : ℝ) = 6 := by simp [rat_real]
  have r32 : (rat 32 3 : ℝ) = 32 / 3 := by simp [rat_real]
  have l9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l32 : Real.log (32 / 3 : ℝ) = 5 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  refine ⟨hxe, hl2, hl3, ?_, ?_, ?_⟩
  · have hc : 0 < ic 4 * uOf x := by simp only [ic_real]; positivity
    have hz : Enc (zFor (rat 9 1 : ℝ) (ic 4 * uOf x)) (zFor (rat 9 1) (ic 4 * uOf xB)) := by
      unfold zFor; enc
    have h := Enc.add (Enc.mul (Enc.ic (-2)) hl3) (lnB_enc hz 24)
    rw [zFor_log (by rw [r9]; norm_num) hc] at h
    have e : Real.log (ic 4 * uOf x) =
        ((-2 : ℤ) : ℝ) * Real.log 3 + Real.log (rat 9 1 * (ic 4 * uOf x)) := by
      have := log_shift (r := (rat 9 1 : ℝ)) (by rw [r9]; norm_num) hc
      rw [this, r9, l9]; push_cast; ring_nf
    show Enc (Real.log (ic 4 * uOf x)) _
    rw [e]; exact h
  · have hc : 0 < ic 3 * uOf x + x := by simp only [ic_real]; positivity
    have hz : Enc (zFor (rat 6 1 : ℝ) (ic 3 * uOf x + x)) (zFor (rat 6 1) (ic 3 * uOf xB + xB)) := by
      unfold zFor; enc
    have h := Enc.add (Enc.neg (Enc.add hl2 hl3)) (lnB_enc hz 24)
    rw [zFor_log (by rw [r6]; norm_num) hc] at h
    have e : Real.log (ic 3 * uOf x + x) =
        -(Real.log 2 + Real.log 3) + Real.log (rat 6 1 * (ic 3 * uOf x + x)) := by
      have := log_shift (r := (rat 6 1 : ℝ)) (by rw [r6]; norm_num) hc
      rw [this, r6, l6]; ring_nf
    show Enc (Real.log (ic 3 * uOf x + x)) _
    rw [e]; exact h
  · have hc : 0 < uOf x + x := by positivity
    have hz : Enc (zFor (rat 32 3 : ℝ) (uOf x + x)) (zFor (rat 32 3) (uOf xB + xB)) := by
      unfold zFor; enc
    have h := Enc.add (Enc.add hl3 (Enc.mul (Enc.ic (-5)) hl2)) (lnB_enc hz 24)
    rw [zFor_log (by rw [r32]; norm_num) hc] at h
    have e : Real.log (uOf x + x) =
        Real.log 3 + ((-5 : ℤ) : ℝ) * Real.log 2 + Real.log (rat 32 3 * (uOf x + x)) := by
      have := log_shift (r := (rat 32 3 : ℝ)) (by rw [r32]; norm_num) hc
      rw [this, r32, l32]; push_cast; ring_nf
    show Enc (Real.log (uOf x + x)) _
    rw [e]; exact h


/-! ### The real computation -/

noncomputable section

/-- The stages of the real computation at the parameters `p`. -/
def rA (p : Par ℝ) : StA ℝ := stageA p
def rB (p : Par ℝ) : StB ℝ := stageB (rA p)
def rC1 (p : Par ℝ) : StC1 ℝ := stageC1 p (rA p) (rB p)
def rC2 (p : Par ℝ) : StC2 ℝ := stageC2 (rC1 p)
def rD1 (p : Par ℝ) : StD1 ℝ := stageD1 (rB p) (rC1 p) (rC2 p)
def rR (p : Par ℝ) : List ℝ := stageD2 (rC1 p) (rD1 p)
def rD3 (p : Par ℝ) : StD3 ℝ := stageD3 (rC1 p) (rR p)

end

/-- Consequences of the certificate. -/
structure CertFacts (p : Par ℝ) : Prop where
  x_pos : 0 < p.x
  u_pos : 0 < (rA p).u
  c_pos : 0 < (rA p).c
  a_pos : 0 < (rA p).a
  d_pos : 0 < (rA p).d
  n21 : (rA p).n2 + -(rA p).n1 ≠ 0
  n31 : (rA p).n3 + -(rA p).n1 ≠ 0
  n32 : (rA p).n3 + -(rA p).n2 ≠ 0
  q0_ne : (rC1 p).q0 ≠ 0
  k0_pos : 0 < (rC2 p).k0
  gam_pos : 0 < (rC2 p).gam
  gam_e0 : 0 < 1 + -((rC2 p).gam * (rC1 p).e0)
  eta3_pos : 0 < (rC1 p).eta3
  Pi_pos : ∀ e : ℝ, 0 ≤ e → 0 < evalL (rD3 p).Pi e

theorem rD3_cA (p : Par ℝ) : (rD3 p).cA = certA (rD3 p).Pi := stageD3_cA _ _
theorem rD3_cB (p : Par ℝ) : (rD3 p).cB = certB (rD3 p).Pi := stageD3_cB _ _
theorem rD3_cC (p : Par ℝ) : (rD3 p).cC = certC (rD3 p).Pi := stageD3_cC _ _
theorem rD3_tail (p : Par ℝ) : (rD3 p).tail = certT (rD3 p).Pi := stageD3_tail _ _

theorem posL_of_enc {p : List ℝ} {P : List Ball} (hp : EncL p P) (h : allPos19 P = true) :
    (∀ a ∈ p, 0 < a) ∧ p ≠ [] := by
  have h' : allPos P = true ∧ (P.length == 19) = true := Bool.and_eq_true_iff.mp h
  refine ⟨allPos_enc hp h'.1, ?_⟩
  intro hnil
  have hl := List.Forall₂.length_eq hp
  have h19 : P.length = 19 := by simpa using h'.2
  rw [hnil] at hl
  simp at hl
  omega

theorem cert_sound (p : Par ℝ) (hp : ParEnc p parB) : CertFacts p := by
  have h := cert_ok
  simp only [finalCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hu, hc⟩, ha⟩, hd⟩, hx⟩, hn21⟩, hn31⟩, hn32⟩, hq0⟩, hk0⟩, hg⟩, hge⟩, he3⟩,
    hcA⟩, hcB⟩, hcC⟩, htail⟩ := h
  have eA := stageA_enc hp
  have eB := stageB_enc eA
  have eC1 := stageC1_enc hp eA eB
  have eC2 := stageC2_enc eC1
  have eD1 := stageD1_enc eB eC1 eC2
  have eR := stageD2_enc eC1 eD1
  have eD3 := stageD3_enc eC1 eR
  refine ⟨Enc.pos hp.x hx, Enc.pos eA.u hu, Enc.pos eA.c hc, Enc.pos eA.a ha, Enc.pos eA.d hd,
    Enc.ne_zero (Enc.add eA.n2 (Enc.neg eA.n1)) hn21,
    Enc.ne_zero (Enc.add eA.n3 (Enc.neg eA.n1)) hn31,
    Enc.ne_zero (Enc.add eA.n3 (Enc.neg eA.n2)) hn32,
    Enc.ne_zero eC1.q0 hq0, Enc.pos eC2.k0 hk0, Enc.pos eC2.gam hg,
    Enc.pos (Enc.add enc_one (Enc.neg (Enc.mul eC2.gam eC1.e0))) hge,
    Enc.pos eC1.eta3 he3, ?_⟩
  have fA : (∀ a ∈ (rD3 p).cA, 0 < a) ∧ (rD3 p).cA ≠ [] := posL_of_enc eD3.cA hcA
  have fB : (∀ a ∈ (rD3 p).cB, 0 < a) ∧ (rD3 p).cB ≠ [] := posL_of_enc eD3.cB hcB
  have fC : (∀ a ∈ (rD3 p).cC, 0 < a) ∧ (rD3 p).cC ≠ [] := posL_of_enc eD3.cC hcC
  have fT : (∀ a ∈ (rD3 p).tail, 0 < a) ∧ (rD3 p).tail ≠ [] := posL_of_enc eD3.tail htail
  obtain ⟨pA, nA⟩ := fA
  obtain ⟨pB, nB⟩ := fB
  obtain ⟨pC, nC⟩ := fC
  obtain ⟨pT, nT⟩ := fT
  have r34 : (rat 3 4 : ℝ) = 3 / 4 := by simp [rat_real]
  have r54 : (rat 5 4 : ℝ) = 5 / 4 := by simp [rat_real]
  intro e he
  rw [rD3_cA] at pA nA
  rw [rD3_cB] at pB nB
  rw [rD3_cC] at pC nC
  rw [rD3_tail] at pT nT
  unfold certA at pA nA
  unfold certB at pB nB
  unfold certC at pC nC
  unfold certT at pT nT
  rcases lt_or_ge e (3 / 4) with h1 | h1
  · refine pos_on_interval' (rD3 p).Pi (l := ic 0) (h := rat 3 4) (d := rat 3 4 + -(ic 0)) ?_ ?_ pA nA e ?_ ?_
    · simp [r34]
    · exact (sub_eq_add_neg _ _).symm
    · simpa using he
    · rwa [r34]
  rcases lt_or_ge e 1 with h2 | h2
  · refine pos_on_interval' (rD3 p).Pi (l := rat 3 4) (h := ic 1) (d := ic 1 + -(rat 3 4)) ?_ ?_ pB nB e ?_ ?_
    · simp only [ic_real, r34]; norm_num
    · exact (sub_eq_add_neg _ _).symm
    · rwa [r34]
    · simpa using h2
  rcases lt_or_ge e (5 / 4) with h3 | h3
  · refine pos_on_interval' (rD3 p).Pi (l := ic 1) (h := rat 5 4) (d := rat 5 4 + -(ic 1)) ?_ ?_ pC nC e ?_ ?_
    · simp only [ic_real, r54]; norm_num
    · exact (sub_eq_add_neg _ _).symm
    · simpa using h2
    · rwa [r54]
  · exact pos_on_tail (rD3 p).Pi (rat 5 4) pT nT e (by rwa [r54])

end FormalResearch.FourQubitEntropy.AH6
