import FormalResearch.FourQubitEntropy.SevenQubitIcoZeroFocus

/-!
# A cut-free cubic formula for the reduced-matrix action `(R_S ⊗ I) ψ`

For a real seven-qubit vector `ψ`, a bijective cut with `k`-side `S` (mask `m`), and `z` a basis string,
```
((R_S ⊗ I) ψ)(z) = ∑_{d ⊆ S} ∑_{e ⊆ Sᶜ} ψ(z ⊕ e) ψ(z ⊕ d) ψ(z ⊕ d ⊕ e),
```
where `⊕` is the bitwise xor on `Fin 7 → Bool` and `d`, `e` range over the subsets of `S`, `Sᶜ`
(`redApply_mask`). Summing over the masks of weight `r` this gives `zfV r ψ z` as a mask sum of cubic
monomials in `ψ` (`zfV_cubic`), and, transferring from `Fin 7 → Bool` to `n < 128` via the bit
pattern `maskOfNat`, a purely numerical form (`cubicMaskSum_nat`). This file is generic (no property of
the icosahedral state is used); the icosahedral evaluation is in `SevenQubitIcoCubicSwap` and the class files `SevenQubitIcoCubicC2/C30/C31`.
The trilinear version `redApplyT` (Gram slots `f`, `h`, acted vector `g`) is used for the contraction identities of
`SevenQubitIcoContraction`.
-/

open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-! ### Xor on bit patterns and on cut assignments -/

/-- Pointwise xor of two bit patterns. -/
def cfXor {ι : Type*} (a b : ι → Bool) : ι → Bool := fun i => xor (a i) (b i)

/-- The all-`false` pattern. -/
def cfZero {ι : Type*} : ι → Bool := fun _ => false

theorem cfXor_cfXor {ι : Type*} (s a : ι → Bool) : cfXor s (cfXor s a) = a := by
  funext j; simp only [cfXor]; cases s j <;> cases a j <;> rfl

theorem cfXor_zero_right {ι : Type*} (a : ι → Bool) : cfXor a cfZero = a := by
  funext j; simp [cfXor, cfZero]

/-- `b ↦ s ⊕ b` as a permutation (an involution). -/
def cfXorEquiv {ι : Type*} (s : ι → Bool) : Equiv.Perm (ι → Bool) :=
  Function.Involutive.toPerm (cfXor s) (cfXor_cfXor s)

theorem cfXorEquiv_apply {ι : Type*} (s a : ι → Bool) : cfXorEquiv s a = cfXor s a := rfl

theorem encode_split {k l : ℕ} (c : Cut k l) (b : Fin k → Bool) (r : Fin l → Bool) :
    encode c b r = cfXor (encode c b cfZero) (encode c cfZero r) := by
  funext i; rcases h : c i with j | j <;> simp [encode, cfXor, cfZero, h]

theorem encode_xor_right {k l : ℕ} (c : Cut k l) (a : Fin k → Bool) (r0 r' : Fin l → Bool) :
    encode c a (cfXor r0 r') = cfXor (encode c a r0) (encode c cfZero r') := by
  funext i; rcases h : c i with j | j <;> simp [encode, cfXor, cfZero, h]

theorem encode_xor_left {k l : ℕ} (c : Cut k l) (a0 b' : Fin k → Bool) (r0 : Fin l → Bool) :
    encode c (cfXor a0 b') r0 = cfXor (encode c a0 r0) (encode c b' cfZero) := by
  funext i; rcases h : c i with j | j <;> simp [encode, cfXor, cfZero, h]

theorem encode_xor_both {k l : ℕ} (c : Cut k l) (a0 b' : Fin k → Bool) (r0 r' : Fin l → Bool) :
    encode c (cfXor a0 b') (cfXor r0 r') = cfXor (encode c a0 r0) (encode c b' r') := by
  funext i; rcases h : c i with j | j <;> simp [encode, cfXor, cfZero, h]

/-! ### The cubic formula for one bijective cut -/

/-- `(G ⊗ I) g` for the Gram matrix of the cut built from two vectors `f`, `h`:
`∑_{a,r} [encode a r = z] ∑_b (∑_{r'} f(a,r') h(b,r')) g(b,r)`. For `f = g = h = ψ` this is `redApply`. -/
def redApplyT {k l : ℕ} (c : Cut k l) (f g h : BitString → ℝ) (z : BitString) : ℝ :=
  ∑ a : Fin k → Bool, ∑ r : Fin l → Bool,
    if encode c a r = z then
      ∑ b, (∑ r' : Fin l → Bool, f (encode c a r') * h (encode c b r')) * g (encode c b r) else 0

theorem redApply_eq_redApplyT {k l : ℕ} (c : Cut k l) (ψ : BitString → ℝ) (z : BitString) :
    redApply c ψ z = redApplyT c ψ ψ ψ z := rfl

theorem redApplyT_cubic {k l : ℕ} (c : Cut k l) (hc : Function.Bijective c) (f g h : BitString → ℝ)
    (z : BitString) :
    redApplyT c f g h z = ∑ b : Fin k → Bool, ∑ r : Fin l → Bool,
      f (cfXor z (encode c cfZero r)) * g (cfXor z (encode c b cfZero)) *
        h (cfXor z (cfXor (encode c b cfZero) (encode c cfZero r))) := by
  have hf := FormalResearch.FourQubitEntropy.SevenQubitConseq.encode_bijective c hc
  obtain ⟨⟨a0, r0⟩, rfl⟩ := hf.surjective z
  have hinj := hf.injective
  have h1 : ∀ (G : (Fin k → Bool) → (Fin l → Bool) → ℝ),
      ∑ a, ∑ r, (if encode c a r = encode c a0 r0 then G a r else 0) = G a0 r0 := by
    intro G
    rw [← Fintype.sum_prod_type'
      (f := fun a r => if encode c a r = encode c a0 r0 then G a r else 0)]
    rw [Finset.sum_eq_single (a0, r0)]
    · simp
    · intro p _ hp
      have : encode c p.1 p.2 ≠ encode c a0 r0 := fun h => hp (hinj (by simpa using h))
      simp [this]
    · simp
  unfold redApplyT
  rw [h1 (fun a r => ∑ b, (∑ r' : Fin l → Bool, f (encode c a r') * h (encode c b r')) *
    g (encode c b r))]
  simp only [Finset.sum_mul]
  refine (Fintype.sum_equiv (cfXorEquiv a0) _ _ fun b' => ?_).symm
  refine Fintype.sum_equiv (cfXorEquiv r0) _ _ fun r' => ?_
  rw [cfXorEquiv_apply, cfXorEquiv_apply, encode_xor_right, encode_xor_both, encode_xor_left,
    ← encode_split]
  ring

/-! ### Reparametrisation of the sums over the two sides of a cut -/

theorem sum_encode_left {k l : ℕ} (c : Cut k l) (hc : Function.Bijective c) (F : BitString → ℝ) :
    ∑ b : Fin k → Bool, F (encode c b cfZero) =
      ∑ d : BitString, if (∀ i, d i = true → (c i).isLeft = true) then F d else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun b _ => encode c b cfZero) ?_ ?_ ?_ ?_
  · intro b _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi
    cases h : c i with
    | inl j => rfl
    | inr j => simp [encode, h, cfZero] at hi
  · intro b _ b' _ h
    funext j
    obtain ⟨i, hi⟩ := hc.surjective (Sum.inl j)
    have := congrFun h i
    simpa [encode, hi] using this
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    refine ⟨fun j => d (Function.surjInv hc.surjective (Sum.inl j)), Finset.mem_univ _, ?_⟩
    funext i
    simp only [encode]
    cases h : c i with
    | inl j =>
      have : i = Function.surjInv hc.surjective (Sum.inl j) :=
        hc.injective (by rw [h]; exact (Function.surjInv_eq hc.surjective _).symm)
      simp [← this]
    | inr j =>
      by_contra hne
      have hd' : d i = true := by
        cases hdi : d i
        · exfalso; apply hne; simp [cfZero, hdi]
        · rfl
      have := hd i hd'
      rw [h] at this
      simp at this
  · intros; rfl

theorem sum_encode_right {k l : ℕ} (c : Cut k l) (hc : Function.Bijective c) (F : BitString → ℝ) :
    ∑ r : Fin l → Bool, F (encode c cfZero r) =
      ∑ e : BitString, if (∀ i, e i = true → (c i).isLeft = false) then F e else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun r _ => encode c cfZero r) ?_ ?_ ?_ ?_
  · intro r _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi
    cases h : c i with
    | inl j => simp [encode, h, cfZero] at hi
    | inr j => rfl
  · intro r _ r' _ h
    funext j
    obtain ⟨i, hi⟩ := hc.surjective (Sum.inr j)
    have := congrFun h i
    simpa [encode, hi] using this
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    refine ⟨fun j => d (Function.surjInv hc.surjective (Sum.inr j)), Finset.mem_univ _, ?_⟩
    funext i
    simp only [encode]
    cases h : c i with
    | inr j =>
      have : i = Function.surjInv hc.surjective (Sum.inr j) :=
        hc.injective (by rw [h]; exact (Function.surjInv_eq hc.surjective _).symm)
      simp [← this]
    | inl j =>
      by_contra hne
      have hd' : d i = true := by
        cases hdi : d i
        · exfalso; apply hne; simp [cfZero, hdi]
        · rfl
      have := hd i hd'
      rw [h] at this
      simp at this
  · intros; rfl

theorem isLeft_maskCut (k l : ℕ) [NeZero k] [NeZero l] (m : Fin 7 → Bool) (i : Fin 7) :
    (maskCut k l m i).isLeft = m i := by
  unfold maskCut
  cases h : m i <;> simp [h]

/-- **The cubic formula** for one bijective mask cut. -/
theorem redApplyT_mask {k l : ℕ} [NeZero k] [NeZero l] (m : Fin 7 → Bool)
    (hc : Function.Bijective (maskCut k l m)) (f g h : BitString → ℝ) (z : BitString) :
    redApplyT (maskCut k l m) f g h z =
      ∑ d : BitString, if (∀ i, d i = true → m i = true) then
        ∑ e : BitString, if (∀ i, e i = true → m i = false) then
          f (cfXor z e) * g (cfXor z d) * h (cfXor z (cfXor d e)) else 0 else 0 := by
  rw [redApplyT_cubic _ hc]
  have h1 : ∀ b : Fin k → Bool, ∑ r : Fin l → Bool,
      f (cfXor z (encode (maskCut k l m) cfZero r)) *
        g (cfXor z (encode (maskCut k l m) b cfZero)) *
        h (cfXor z (cfXor (encode (maskCut k l m) b cfZero) (encode (maskCut k l m) cfZero r))) =
      ∑ e : BitString, if (∀ i, e i = true → m i = false) then
        f (cfXor z e) * g (cfXor z (encode (maskCut k l m) b cfZero)) *
          h (cfXor z (cfXor (encode (maskCut k l m) b cfZero) e)) else 0 := by
    intro b
    rw [sum_encode_right (maskCut k l m) hc
      (fun e => f (cfXor z e) * g (cfXor z (encode (maskCut k l m) b cfZero)) *
          h (cfXor z (cfXor (encode (maskCut k l m) b cfZero) e)))]
    simp only [isLeft_maskCut]
  simp only [h1]
  rw [sum_encode_left (maskCut k l m) hc (fun d => ∑ e : BitString,
    if (∀ i, e i = true → m i = false) then
      f (cfXor z e) * g (cfXor z d) * h (cfXor z (cfXor d e)) else 0)]
  simp only [isLeft_maskCut]

theorem redApply_mask {k l : ℕ} [NeZero k] [NeZero l] (m : Fin 7 → Bool)
    (hc : Function.Bijective (maskCut k l m)) (ψ : BitString → ℝ) (z : BitString) :
    redApply (maskCut k l m) ψ z =
      ∑ d : BitString, if (∀ i, d i = true → m i = true) then
        ∑ e : BitString, if (∀ i, e i = true → m i = false) then
          ψ (cfXor z e) * ψ (cfXor z d) * ψ (cfXor z (cfXor d e)) else 0 else 0 :=
  redApplyT_mask m hc ψ ψ ψ z

/-- `V_r(ψ)` for `r = 1, 2, 3` as a sum over the masks of weight `r` of cubic monomials. -/
theorem zfV_cubic (r : ℕ) (hr : r = 1 ∨ r = 2 ∨ r = 3) (ψ : BitString → ℝ) (z : BitString) :
    zfV r ψ z = ∑ m : Fin 7 → Bool, if weight m = r then
      ∑ d : BitString, if (∀ i, d i = true → m i = true) then
        ∑ e : BitString, if (∀ i, e i = true → m i = false) then
          ψ (cfXor z e) * ψ (cfXor z d) * ψ (cfXor z (cfXor d e)) else 0 else 0 else 0 := by
  rcases hr with rfl | rfl | rfl
  · simp only [zfV, oneMasks, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · exact redApply_mask m (maskCut_bijective_one m h) ψ z
    · rfl
  · simp only [zfV, pairMasks, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · exact redApply_mask m (maskCut_bijective_two m h) ψ z
    · rfl
  · simp only [zfV, tripleMasks, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · exact redApply_mask m (maskCut_bijective_three m h) ψ z
    · rfl

/-! ### Masks restricted by a predicate -/

/-- The trilinear mask sum over the masks satisfying `P` (no weight condition built in). -/
def cubicMaskSumT (f g h : BitString → ℝ) (z : BitString) (P : (Fin 7 → Bool) → Prop)
    [DecidablePred P] : ℝ :=
  ∑ m : Fin 7 → Bool, if P m then
    ∑ d : BitString, if (∀ i, d i = true → m i = true) then
      ∑ e : BitString, if (∀ i, e i = true → m i = false) then
        f (cfXor z e) * g (cfXor z d) * h (cfXor z (cfXor d e)) else 0 else 0 else 0

/-- The cubic mask sum (`f = g = h = ψ`). -/
def cubicMaskSum (ψ : BitString → ℝ) (z : BitString) (P : (Fin 7 → Bool) → Prop)
    [DecidablePred P] : ℝ := cubicMaskSumT ψ ψ ψ z P

theorem sum_masks_cubicT {k l : ℕ} [NeZero k] [NeZero l] (r : ℕ)
    (hbij : ∀ m : Fin 7 → Bool, weight m = r → Function.Bijective (maskCut k l m))
    (q : (Fin 7 → Bool) → Prop) [DecidablePred q] (f g h : BitString → ℝ) (z : BitString) :
    ∑ m ∈ Finset.univ.filter (fun m : Fin 7 → Bool => weight m = r ∧ q m),
        redApplyT (maskCut k l m) f g h z =
      cubicMaskSumT f g h z (fun m => weight m = r ∧ q m) := by
  unfold cubicMaskSumT
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs with hm
  · exact redApplyT_mask m (hbij m hm.1) f g h z
  · rfl

theorem sum_masks_cubic {k l : ℕ} [NeZero k] [NeZero l] (r : ℕ)
    (hbij : ∀ m : Fin 7 → Bool, weight m = r → Function.Bijective (maskCut k l m))
    (q : (Fin 7 → Bool) → Prop) [DecidablePred q] (ψ : BitString → ℝ) (z : BitString) :
    ∑ m ∈ Finset.univ.filter (fun m : Fin 7 → Bool => weight m = r ∧ q m),
        redApply (maskCut k l m) ψ z =
      cubicMaskSum ψ z (fun m => weight m = r ∧ q m) :=
  sum_masks_cubicT r hbij q ψ ψ ψ z

theorem zfV_eq_cubicMaskSum (r : ℕ) (hr : r = 1 ∨ r = 2 ∨ r = 3) (ψ : BitString → ℝ)
    (z : BitString) :
    zfV r ψ z = cubicMaskSum ψ z (fun m => weight m = r) := by
  rw [zfV_cubic r hr]
  rfl

/-! ### Transfer to numbers `n < 128` -/

theorem maskOfNat_xor (a b : ℕ) : maskOfNat (a ^^^ b) = cfXor (maskOfNat a) (maskOfNat b) := by
  funext i; simp [maskOfNat, cfXor, Nat.testBit_xor]

theorem lt_two_pow_of_lt_128 {a i : ℕ} (ha : a < 128) (hi : ¬ i < 7) : a < 2 ^ i :=
  lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega) : 2 ^ 7 ≤ 2 ^ i)

theorem maskOfNat_injOn {a b : ℕ} (ha : a < 128) (hb : b < 128) (h : maskOfNat a = maskOfNat b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 7
  · exact congrFun h ⟨i, hi⟩
  · rw [Nat.testBit_lt_two_pow (lt_two_pow_of_lt_128 ha hi),
      Nat.testBit_lt_two_pow (lt_two_pow_of_lt_128 hb hi)]

theorem sum_maskOfNat {M : Type*} [AddCommMonoid M] (F : BitString → M) :
    ∑ x : BitString, F x = ∑ n ∈ Finset.range 128, F (maskOfNat n) := by
  symm
  refine Finset.sum_bij (fun n _ => maskOfNat n) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro a ha b hb h
    exact maskOfNat_injOn (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) h
  · intro x _
    obtain ⟨n, hn, rfl⟩ := maskOfNat_surjective x
    exact ⟨n, Finset.mem_range.2 hn, rfl⟩

/-- Packed popcount table: 3-bit fields. -/
def cfPcTab : ℕ := 38688605477795291639177638255174619524745213742638081737860757693208305674782301095493395244431646846014899907793992

/-- Popcount of `n < 128`, by table lookup. -/
def cfPc (n : ℕ) : ℕ := (cfPcTab >>> (3 * n)) % 8

theorem weight_maskOfNat : ∀ n < 128, weight (maskOfNat n) = cfPc n := by decide +kernel

theorem sub_maskOfNat {D M : ℕ} (hD : D < 128) (hM : M < 128) :
    (∀ i, maskOfNat D i = true → maskOfNat M i = true) ↔ D &&& M = D := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases hi : i < 7
    · have := h ⟨i, hi⟩
      simp only [maskOfNat] at this
      cases hd : D.testBit i
      · simp
      · simp [this hd]
    · simp [Nat.testBit_lt_two_pow (lt_two_pow_of_lt_128 hD hi)]
  · intro h i hi
    have := congrArg (fun x => x.testBit i.val) h
    simp only [Nat.testBit_and] at this
    simp only [maskOfNat] at hi ⊢
    rw [hi] at this
    simpa using this

theorem disj_maskOfNat {E M : ℕ} (hE : E < 128) (hM : M < 128) :
    (∀ i, maskOfNat E i = true → maskOfNat M i = false) ↔ E &&& M = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases hi : i < 7
    · have := h ⟨i, hi⟩
      simp only [maskOfNat] at this
      cases hd : E.testBit i
      · simp
      · simp [this hd]
    · simp [Nat.testBit_lt_two_pow (lt_two_pow_of_lt_128 hE hi)]
  · intro h i hi
    have := congrArg (fun x => x.testBit i.val) h
    simp only [Nat.testBit_and] at this
    simp only [maskOfNat] at hi ⊢
    rw [hi] at this
    simpa using this

/-- The numerical form of the trilinear mask sum. -/
def cubNatT (pN : ℕ → Prop) [DecidablePred pN] (f g h : ℕ → ℝ) (z : ℕ) : ℝ :=
  ∑ M ∈ Finset.range 128, if pN M then
    ∑ D ∈ Finset.range 128, if D &&& M = D then
      ∑ E ∈ Finset.range 128, if E &&& M = 0 then
        f (z ^^^ E) * g (z ^^^ D) * h (z ^^^ (D ^^^ E)) else 0 else 0 else 0

/-- The numerical form of the cubic mask sum. -/
def cubNat (pN : ℕ → Prop) [DecidablePred pN] (ψ : ℕ → ℝ) (z : ℕ) : ℝ := cubNatT pN ψ ψ ψ z

theorem cubicMaskSumT_nat (P : (Fin 7 → Bool) → Prop) [DecidablePred P]
    (pN : ℕ → Prop) [DecidablePred pN] (hP : ∀ M < 128, P (maskOfNat M) ↔ pN M)
    (f g h : BitString → ℝ) (z : ℕ) (hz : z < 128) :
    cubicMaskSumT f g h (maskOfNat z) P =
      cubNatT pN (fun n => f (maskOfNat n)) (fun n => g (maskOfNat n)) (fun n => h (maskOfNat n)) z := by
  unfold cubicMaskSumT cubNatT
  rw [sum_maskOfNat]
  refine Finset.sum_congr rfl fun M hM => ?_
  have hM' := Finset.mem_range.1 hM
  by_cases hpN : pN M
  · rw [if_pos ((hP M hM').2 hpN), if_pos hpN, sum_maskOfNat]
    refine Finset.sum_congr rfl fun D hD => ?_
    have hD' := Finset.mem_range.1 hD
    by_cases hsub : D &&& M = D
    · rw [if_pos ((sub_maskOfNat hD' hM').2 hsub), if_pos hsub, sum_maskOfNat]
      refine Finset.sum_congr rfl fun E hE => ?_
      have hE' := Finset.mem_range.1 hE
      by_cases hdis : E &&& M = 0
      · rw [if_pos ((disj_maskOfNat hE' hM').2 hdis), if_pos hdis, ← maskOfNat_xor, ← maskOfNat_xor,
          ← maskOfNat_xor, ← maskOfNat_xor]
      · rw [if_neg (fun h => hdis ((disj_maskOfNat hE' hM').1 h)), if_neg hdis]
    · rw [if_neg (fun h => hsub ((sub_maskOfNat hD' hM').1 h)), if_neg hsub]
  · rw [if_neg (fun h => hpN ((hP M hM').1 h)), if_neg hpN]

theorem cubicMaskSum_nat (P : (Fin 7 → Bool) → Prop) [DecidablePred P]
    (pN : ℕ → Prop) [DecidablePred pN] (hP : ∀ M < 128, P (maskOfNat M) ↔ pN M)
    (ψ : BitString → ℝ) (z : ℕ) (hz : z < 128) :
    cubicMaskSum ψ (maskOfNat z) P = cubNat pN (fun n => ψ (maskOfNat n)) z :=
  cubicMaskSumT_nat P pN hP ψ ψ ψ z hz

end FormalResearch.FourQubitEntropy.SevenQubitIco
